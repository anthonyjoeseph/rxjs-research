#!/usr/bin/env bash
# Run the differential-test "main" (src/prop-test.ts) leaving NOTHING behind.
# The source uses NodeNext .js import specifiers, so it can't run under node
# directly — it must be compiled first. tsconfig stays noEmit:true; we emit to
# a throwaway dir one level under typescript/ (so `node` still finds
# node_modules, and agda-bridge's default ../../agda/_cli/Main path resolves)
# and delete it on ANY exit. Args pass straight through to prop-test, e.g.
#   scripts/run-oracle.sh --seed 1
#   scripts/run-oracle.sh --operator mergeAll
set -euo pipefail
cd "$(dirname "$0")/.."                 # → typescript/
out=".oracle-tmp"
trap 'rm -rf "$out"' EXIT
./node_modules/.bin/tsc --outDir "$out" --rootDir src --noEmit false
node "$out/prop-test.js" "$@"
