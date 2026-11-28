#!/usr/bin/env bash
# Guard against unannounced changes to what the formalization assumes.
#
# 1. Every `axiom` lives in GSpinGGP/Literature/ (cited literature results only), and there is no
#    `opaque` declaration (definitions are never left opaque). Checked on the sources and, for the
#    axioms, also on the compiled project (step 3).
# 2. The axioms used by the main theorem `local_ggp` are exactly those listed in
#    scripts/main-axioms.txt (update that file, and the README, when a citation is added or removed),
#    together with Lean's standard axioms and `sorryAx` only (so no `native_decide`).
# 2b. scripts/derived-axioms.txt lists the *derived* axioms: short combinations of published
#    statements, or published statements whose hypotheses are checked in the docstring only. Every
#    other axiom is a published statement as printed. Each listed name must be an axiom, and the
#    README must give their number.
# 3. The README's status numbers match: total Literature axioms, axioms used by `local_ggp`, the
#    number of declarations with `sorry` that `local_ggp` depends on, and the total number of
#    declarations using `sorry`. Both `sorry` counts are read from the compiled environment
#    (scripts/PathSorries.lean), so they are the same after an incremental build as after a clean one.
#
# Usage: scripts/check-assumptions.sh [build.log]
# If a build log is given, it must come from a clean build (one that compiled every module of the
# project, as CI does on `main`): the number of `sorry` warnings in it is then compared with the
# count from the environment, as a cross-check of the latter.
set -euo pipefail
cd "$(dirname "$0")/.."
export LC_ALL=C   # the sort order of scripts/main-axioms.txt
LAKE="${LAKE:-lake}"
fail=0

# 1. Axioms outside Literature/.
# A declaration keyword at the start of a line, after optional indentation, attributes and modifiers.
decl='^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable|unsafe|partial|nonrec)[[:space:]]+)*'
outside=$(grep -rnE "${decl}axiom[[:space:]]" GSpinGGP GSpinGGP.lean --include='*.lean' \
  | grep -v '^GSpinGGP/Literature/' || true)
if [ -n "$outside" ]; then
  echo "ERROR: axioms outside GSpinGGP/Literature/:"; echo "$outside"; fail=1
fi
opaques=$(grep -rnE "${decl}opaque[[:space:]]" GSpinGGP GSpinGGP.lean --include='*.lean' || true)
if [ -n "$opaques" ]; then
  echo "ERROR: opaque declarations:"; echo "$opaques"; fail=1
fi
total=$(grep -rhE "${decl}axiom[[:space:]]" GSpinGGP/Literature --include='*.lean' | wc -l | tr -d ' ')

# 2. Axioms of the main theorem.
tmp=$(mktemp -d)
printf 'import GSpinGGP\n#print axioms GSpinGGP.local_ggp\n' > "$tmp/Axioms.lean"
"$LAKE" env lean "$tmp/Axioms.lean" > "$tmp/out.txt" 2>&1 || { cat "$tmp/out.txt"; exit 1; }
tr ',[]' '\n\n\n' < "$tmp/out.txt" | sed 's/^ *//; s/ *$//' | grep -v '^$' > "$tmp/names.txt"
grep -q 'depends on axioms' "$tmp/names.txt" || { echo "ERROR: unexpected output of #print axioms:"; cat "$tmp/out.txt"; exit 1; }
grep -E '^GSpinGGP\.' "$tmp/names.txt" | sort -u > "$tmp/used.txt" || true
other=$(grep -vE '^GSpinGGP\.|depends on axioms|^(propext|Classical\.choice|Quot\.sound|sorryAx)$' "$tmp/names.txt" || true)
if [ -n "$other" ]; then
  echo "ERROR: local_ggp depends on axioms that are neither the project's nor Lean's standard ones:"
  echo "$other"; fail=1
fi
if ! diff -u scripts/main-axioms.txt "$tmp/used.txt"; then
  echo "ERROR: local_ggp's literature axioms differ from scripts/main-axioms.txt (diff above)."; fail=1
fi
used=$(wc -l < "$tmp/used.txt" | tr -d ' ')

# 2b. Derived axioms.
derived=0
while read -r name; do
  [ -z "$name" ] && continue
  derived=$((derived + 1))
  short="${name##*.}"
  if ! grep -rqE "${decl}axiom[[:space:]]+${short}([[:space:]]|\$)" GSpinGGP/Literature --include='*.lean'; then
    echo "ERROR: scripts/derived-axioms.txt lists $name, which is not an axiom in GSpinGGP/Literature/"; fail=1
  fi
done < scripts/derived-axioms.txt
if ! grep -q "$derived of the $total are derived" README.md; then
  echo "ERROR: README should say \"$derived of the $total are derived\""; fail=1
fi

# 3. README status numbers.
if ! grep -q "\`local_ggp\` uses $used of the $total\." README.md; then
  echo "ERROR: README should say \"\`local_ggp\` uses $used of the $total.\""; fail=1
fi
"$LAKE" env lean scripts/PathSorries.lean > "$tmp/path.txt" 2>&1 || { cat "$tmp/path.txt"; exit 1; }
# The axioms the compiled environment contains, against the textual search of step 1.
envoutside=$(sed -n 's/.*ENV_AXIOM //p' "$tmp/path.txt" | grep -v ' GSpinGGP\.Literature\.[A-Za-z0-9_.]*$' || true)
if [ -n "$envoutside" ]; then
  echo "ERROR: axioms declared outside GSpinGGP/Literature/ (name, module):"; echo "$envoutside"; fail=1
fi
envtotal=$(grep -c 'ENV_AXIOM' "$tmp/path.txt" || true)
if [ "$envtotal" != "$total" ]; then
  echo "ERROR: $total axiom declarations found in the sources of GSpinGGP/Literature/, $envtotal axioms in the compiled project"; fail=1
fi
pathsorries=$(grep -c 'PATH_SORRY' "$tmp/path.txt" || true)
if ! grep -q "depends on $pathsorries of them" README.md; then
  echo "ERROR: README should say \"depends on $pathsorries of them\"; local_ggp depends on:"
  sed -n 's/.*PATH_SORRY //p' "$tmp/path.txt"; fail=1
fi
sorries=$(grep -c 'ALL_SORRY' "$tmp/path.txt" || true)
if ! grep -q "builds with $sorries declarations containing \`sorry\`" README.md; then
  echo "ERROR: README should say \"builds with $sorries declarations containing \`sorry\`\""; fail=1
fi
if [ "$pathsorries" -gt "$sorries" ]; then
  echo "ERROR: $pathsorries sorry declarations on the path of local_ggp but only $sorries in total"; fail=1
fi
if [ $# -ge 1 ]; then
  logsorries=$(grep 'declaration uses `sorry`' "$1" | sed 's/.*warning: //' | sort -u | wc -l | tr -d ' ')
  if [ "$logsorries" != "$sorries" ]; then
    echo "ERROR: the build log has $logsorries \`sorry\` warnings, the environment has $sorries declarations containing \`sorry\`:"
    sed -n 's/.*ALL_SORRY //p' "$tmp/path.txt"; fail=1
  fi
fi

rm -rf "$tmp"
[ "$fail" -eq 0 ] && echo "Assumptions check passed: $used of $total literature axioms and $pathsorries sorry declarations used by local_ggp."
exit "$fail"
