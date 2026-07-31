#!/usr/bin/env bash
# measure.sh "EXPR" LOG -- print the normal form of a ℕ-valued EXPR from
# probe/Mint-Loop-Probe by asking Agda to check a deliberate mismatch.  Writes
# to LOG and appends EXIT=, so a long run can be kicked off and polled:
# family G′'s deeper rungs take tens of minutes and gigabytes.
set -u
export PATH="$PATH:/root/.cabal/bin" LC_ALL=C.UTF-8 LANG=C.UTF-8
cd "$(dirname "$0")/../agda"
LOG="$2"
: > "$LOG"
cat > probe/G-Probe.agda <<AGDA
module G-Probe where
open import Data.Nat using (ℕ; _*_; _^_; _≤ᵇ_)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mint-Loop-Probe
_ : $1 ≡ 987654
_ = refl
AGDA
agda -i src -i probe probe/G-Probe.agda >> "$LOG" 2>&1
echo "EXIT=$?" >> "$LOG"
