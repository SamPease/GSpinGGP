#!/usr/bin/env bash
# Guard against unannounced changes to what the formalization assumes.
#
# 1. Every `axiom` lives in GSpinGGP/Literature/ (cited literature results only).
# 2. The axioms used by the main theorem `local_ggp` are exactly those listed in
#    scripts/main-axioms.txt (update that file, and the README, when a citation is added or removed).
# 3. The README's status numbers match: total Literature axioms, axioms used by `local_ggp`, and
#    (if a build log is given) the number of declarations using `sorry`.
#
# Usage: scripts/check-assumptions.sh [build.log]
# The build log must come from a build that compiled the project's own modules (as in CI), since
# Lake does not replay warnings of modules that are already up to date.
set -euo pipefail
cd "$(dirname "$0")/.."
LAKE="${LAKE:-lake}"
fail=0

# 1. Axioms outside Literature/.
outside=$(grep -rnE '^(private |protected |noncomputable )*axiom [A-Za-z_]' GSpinGGP --include='*.lean' \
  | grep -v '^GSpinGGP/Literature/' || true)
if [ -n "$outside" ]; then
  echo "ERROR: axioms outside GSpinGGP/Literature/:"; echo "$outside"; fail=1
fi
total=$(grep -rhE '^(private |protected |noncomputable )*axiom [A-Za-z_]' GSpinGGP/Literature --include='*.lean' | wc -l | tr -d ' ')

# 2. Axioms of the main theorem.
tmp=$(mktemp -d)
printf 'import GSpinGGP\n#print axioms GSpinGGP.local_ggp\n' > "$tmp/Axioms.lean"
"$LAKE" env lean "$tmp/Axioms.lean" > "$tmp/out.txt" 2>&1 || { cat "$tmp/out.txt"; exit 1; }
tr ',[]' '\n\n\n' < "$tmp/out.txt" | sed 's/^ *//; s/ *$//' | grep -E '^GSpinGGP\.' | sort -u > "$tmp/used.txt"
if ! diff -u scripts/main-axioms.txt "$tmp/used.txt"; then
  echo "ERROR: local_ggp's literature axioms differ from scripts/main-axioms.txt (diff above)."; fail=1
fi
used=$(wc -l < "$tmp/used.txt" | tr -d ' ')

# 3. README status numbers.
if ! grep -q "\`local_ggp\` uses $used of the $total\." README.md; then
  echo "ERROR: README should say \"\`local_ggp\` uses $used of the $total.\""; fail=1
fi
if [ $# -ge 1 ]; then
  sorries=$(grep 'declaration uses `sorry`' "$1" | sed 's/.*warning: //' | sort -u | wc -l | tr -d ' ')
  if ! grep -q "builds with $sorries declarations containing \`sorry\`" README.md; then
    echo "ERROR: README should say \"builds with $sorries declarations containing \`sorry\`\""; fail=1
  fi
fi

rm -rf "$tmp"
[ "$fail" -eq 0 ] && echo "Assumptions check passed: $used of $total literature axioms used by local_ggp."
exit "$fail"
