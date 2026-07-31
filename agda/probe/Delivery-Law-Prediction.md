# The delivery law's sealed L=5 prediction (2026-07-31)

Committed BEFORE any L=5 measurement exists, so the binomial law is tested
out-of-sample rather than fitted. Standing ruling: L=5 stays unmeasured until
this file is in history. The measurement that tests it comes after, and the
comparison is exact-match, not order-of-magnitude.

## The law (derived from structure, validated on all 21 measured rows, L ≤ 4)

For the lean mint ladders `pLᴸ k` (slots `insGᴸ`, entry cReg = 2L+1):

- fires of shared slot i = `2^(L−i)`, invariant in k — minted registrations on
  these families are pure consumers (their chains end at `root`), so the whole
  k-dependence is fan-out width, not fire count.
- mint generation g (mint-edges from the entry registry) holds exactly
  `C(2^L, g)` registrations.
- slot-0 deliveries at nesting depth k = `Σ_{g=1}^{k+2} C(2^L, g)`.
- per-rung delivery increment: `D(L, k+1) − D(L, k) = C(2^L, k+3)`.
  (Verified exactly: L=3 increments 56, 70, 56, 28, 8, 1 = C(8, 3..8);
  L=4 increments 560, 1820, 4368, 8008, 11440 = C(16, 3..7).)
- saturated slot-0 deliveries: `2^(2^L) − 1 − 2^L` beyond generation 0,
  i.e. D_∞(L) − D(L,0) = `Σ_{g=3}^{2^L} C(2^L, g)`.

## The L=5 prediction (2^L = 32, cReg = 11, bound 4^11 = 4194304)

Exact claims, falsifiable row by row:

1. `ΔD(5, k→k+1) = C(32, k+3)`:
   k=0→1: **4960**, 1→2: **35960**, 2→3: **201376**, 3→4: **906192**,
   4→5: **3365856**.
2. Fires: slot i fires `2^(5−i)` = 32, 16, 8, 4, 2 at every k.
3. Generation counts at any k: gen g has exactly `C(32, g)` registrations
   for g ≤ k (gen 1 = 32, gen 2 = 496, gen 3 = 4960, ...).
4. cReg = 11 at every k; cSize = 8k+2 for k ≥ 1 (same as L=3, L=4 rung for
   rung); mPre invariant in k.
5. **The delivery bound `D ≤ 4^cReg` breaks at k = 5**: the cumulative
   increments alone (4960 + 35960 + 201376 + 906192 + 3365856 = 4514344)
   exceed 4194304 regardless of the k=0 base. If rows past k=2 are not
   measurable (memory died at D ≈ 46k on L=4), the breach follows from
   exact-matching the measurable rows plus the increment law — the
   Fold-Count arithmetic economy.

## What this means for the count (design ruling, W3)

`D ≤ 2^cReg · 2^cReg` is false in general — the true growth is
`2^(2^L)`-shaped: doubly exponential in ladder depth, hence a 2-tower over
cReg, not any single exponential. The proof-route that fits the structure:
each minted registration's ancestry is a SUBSET of the slot-0 fire schedule
(generation g ↦ g-subsets — the binomial counts are subset counts), so the
injection lands in subsets of fires, and fires are bounded by the pre-state
DAG (the inverted-pair leg, applied where it belongs).

## The caveat that decides the general form (next probe family)

"Fires never move" is a property of THESE families: their minting scan sits
in the root program, so minted chains end at `root`. A minting scan INSIDE a
shared def extends that def's chain, whose sink is the share itself — minted
registrations would then be one-shot FIRES of that share, and fires would
beget registrations beget fires. The general count must either bound that
amplifier family (plausibly a tower of height ≤ slot count, which dispatch
gas already caps at n) or the family must be shown structurally tame. That
family — the "amplifier ladder" — is the next measurement target after L=5
validates or refutes the law above. Its k=0 row and small-k rows come first;
no claims from shallow rows (see Mint-Loop-Probe's standing warning).
