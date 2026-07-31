#!/usr/bin/env bash
# measure.sh LOG EXPR...  -- print the normal form of each ℕ-valued EXPR from
# probe/Mint-Loop-Shapes by asking Agda to check a deliberate mismatch.  The
# deep rungs of family G′ take tens of minutes and gigabytes each, so the
# expressions run sequentially into one LOG that a single poll can watch.
set -u
export PATH="$PATH:$HOME/.cabal/bin:/root/.cabal/bin" LC_ALL=C.UTF-8 LANG=C.UTF-8
cd "$(dirname "$0")/../agda"
LOG="$1"; shift
: > "$LOG"
for E in "$@"; do
  cat > probe/G-Probe.agda <<AGDA
module G-Probe where
open import Data.Nat using (ℕ; _*_; _^_; _≤ᵇ_)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mint-Loop-Shapes
_ : $E ≡ 987654
_ = refl
AGDA
  echo "=== $E" >> "$LOG"
  agda -i src -i probe probe/G-Probe.agda 2>&1 | grep -A2 '!=' | head -4 >> "$LOG"
done
echo "EXIT=0" >> "$LOG"
