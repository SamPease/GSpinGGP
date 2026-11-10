#!/usr/bin/env bash
# Guard against unannounced changes to what the formalization assumes.
#
# 1. Every `axiom` lives in GSpinGGP/Literature/ (cited literature results only), and there is no
#    `opaque` declaration (definitions are never left opaque).
# 2. The axioms used by the main theorem `local_ggp` are exactly those listed in
#    scripts/main-axioms.txt (update that file, and the README, when a citation is added or removed),
#    together with Lean's standard axioms and `sorryAx` only (so no `native_decide`).
# 3. The README's status numbers match: total Literature axioms, axioms used by `local_ggp`, the
#    number of declarations with `sorry` that `local_ggp` depends on, and (if a build log is given)
#    the total number of declarations using `sorry`.
#
# Usage: scripts/check-assumptions.sh [build.log]
# The build log must come from a build that compiled the project's own modules (as in CI), since
# Lake does not replay warnings of modules that are already up to date.
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

# 3. README status numbers.
if ! grep -q "\`local_ggp\` uses $used of the $total\." README.md; then
  echo "ERROR: README should say \"\`local_ggp\` uses $used of the $total.\""; fail=1
fi
"$LAKE" env lean scripts/PathSorries.lean > "$tmp/path.txt" 2>&1 || { cat "$tmp/path.txt"; exit 1; }
pathsorries=$(grep -c 'PATH_SORRY' "$tmp/path.txt" || true)
if ! grep -q "depends on $pathsorries of them" README.md; then
  echo "ERROR: README should say \"depends on $pathsorries of them\"; local_ggp depends on:"
  sed -n 's/.*PATH_SORRY //p' "$tmp/path.txt"; fail=1
fi
if [ $# -ge 1 ]; then
  sorries=$(grep 'declaration uses `sorry`' "$1" | sed 's/.*warning: //' | sort -u | wc -l | tr -d ' ')
  if ! grep -q "builds with $sorries declarations containing \`sorry\`" README.md; then
    echo "ERROR: README should say \"builds with $sorries declarations containing \`sorry\`\""; fail=1
  fi
fi

rm -rf "$tmp"
[ "$fail" -eq 0 ] && echo "Assumptions check passed: $used of $total literature axioms and $pathsorries sorry declarations used by local_ggp."
exit "$fail"
