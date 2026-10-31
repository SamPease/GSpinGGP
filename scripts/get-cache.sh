#!/usr/bin/env bash
# Download prebuilt Mathlib and Tau Ceti build outputs, so that `lake build` only compiles this
# project. Run from the project root after `lake update` / checkout.
set -euo pipefail
cd "$(dirname "$0")/.."

lake exe cache get

# Tau Ceti publishes its build outputs in a public Lake cache (see Tau Ceti's README).
cfg="$(mktemp)"
cat > "$cfg" <<'TOML'
cache.defaultService = "tauceti-public"
[[cache.service]]
name = "tauceti-public"
kind = "s3"
artifactEndpoint = "https://cache.taucetiproject.org/artifacts"
revisionEndpoint = "https://cache.taucetiproject.org/revisions"
TOML
LAKE_CONFIG="$cfg" lake cache get --service tauceti-public --package=TauCeti \
  --repo TauCetiProject/TauCeti --max-revs=150
rm -f "$cfg"
