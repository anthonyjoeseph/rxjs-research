#!/usr/bin/env bash
# Run the flatten differential (src/flatten-diff.ts) leaving NOTHING behind.
# The source uses NodeNext .js import specifiers, so it can't run under node
# directly — it must be compiled first. tsconfig stays noEmit:true; we emit to
# a throwaway dir one level under typescript/ (so `node` still finds
# node_modules) and delete it on ANY exit. Args pass straight through, e.g.
#   scripts/run-flatten-diff.sh 500
#   scripts/run-flatten-diff.sh --selftest
set -euo pipefail
cd "$(dirname "$0")/.."                 # → typescript/
out=".flatten-tmp"
trap 'rm -rf "$out"' EXIT
./node_modules/.bin/tsc --outDir "$out" --rootDir src --noEmit false
node "$out/flatten-diff.js" "$@"
