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

------------------------------------------------------------------

## RESULTS — the L = 5 measurement (2026-07-31, appended after the fact)

Shapes `Γˢ⁵ / insG⁵ / mintOnly⁵ / pL⁵` added to `probe/Mint-Loop-Shapes.agda`
(five shares, entry cReg = 11, scripted input carrying TWO emissions — the
non-completing form, which is what makes slot 0's fire count a full
`2 ^ 5 = 32` and therefore what claims 1 and 3 were written against).

All rows off the COMPILED harness (`probe/Measure-Main.agda`, indices
122–153), so every one is **measured-not-rechecked**.  The harness's
calibration index 0 reproduced the `refl`-pinned 2546 before and after each
recompile.

### The rows

    k   D       ΔD       mints   fires (slots 0..4)   DELIV (slots 0..4, input)     GEN g=1,2,3      cReg  cSize  mPre
    0     590      —         32   32 16 8 4 2          528  32 16 8 4 2              32   —    —       11     3    94
    1    5550   4960        528   32 16 8 4 2         5488  32 16 8 4 2              32  496   —       11    10    94
    2   41510  35960       5488   32 16 8 4 2        41448  32 16 8 4 2              32  496 4960      11    18     —
    3      —      —          —      —                    —                              —              —      —     —

k = 3 is **NOT MEASURED**: `mFolds 0 (pL⁵ 3) insG⁵` died `out of memory`
under a 12 GB address-space cap and again under a 14.2 GB one (the box has
15 GB).  Predicted D there is 242886.

The pure share-DAG control at this ladder, `pS⁵` (no scan, no minting):
fires `32 16 8 4 2`, deliveries `64 32 16 8 4 2`, D = 126 = `2 ^ 7 ∸ 2`.

### Claim by claim

1. **`ΔD(5, k→k+1) = C(32, k+3)` — MATCH on both measurable rungs.**
   0→1 measured 4960, predicted `C(32,3) = 4960`.
   1→2 measured 35960, predicted `C(32,4) = 35960`.
   2→3 predicted 201376, not measurable.
   (And the base is exact too: D(5,0) = 590 = `C(32,1) + C(32,2) + 2 ^ 6 ∸ 2`.)

2. **Fires = `2 ^ (5 ∸ i)` at every k — MATCH.**  `32 16 8 4 2` at k = 0, 1
   and 2, identical to the `pS⁵` control's, i.e. invariant in k exactly as on
   L ≤ 4.

3. **Generation g holds `C(32, g)` — MATCH on every generation that exists.**
   32, 496, 4960 against `C(32,1) = 32`, `C(32,2) = 496`, `C(32,3) = 4960`.
   ONE DISCREPANCY, AND IT IS IN THE PREDICTION'S WORDING, NOT ITS VALUES:
   claim 3 says "for g ≤ k", and the measured range is g ≤ k + 1 — k = 0 has
   generation 1, k = 2 has generations 1..3.  The L ≤ 4 table in
   Mint-Loop-Shapes already records "the deepest generation is k + 1 on every
   row", so the prediction understated its own range by one.  No measured
   count differs from `C(32, g)`.

4. **cReg = 11 at every k, cSize = 8k + 2 for k ≥ 1, mPre invariant — MATCH.**
   cReg 11 at k = 0, 1, 2; cSize 3, 10, 18; mPre 94 at k = 0 and k = 1.
   (cSize = 3 at k = 0 rather than 2, the same off-form base as L = 3 and
   L = 4.)

5. **The breach at k = 5 — FOLLOWS BY ARITHMETIC, not measured.**  D(5,0) is
   measured at 590 and the increment law is exact on both measurable rungs,
   so
   `D(5,5) = 590 + 4960 + 35960 + 201376 + 906192 + 3365856 = 4514934`
   against `4 ^ cReg = 4 ^ 11 = 4194304`.  The first breaching rung is
   k = 5: D(5,4) = 1149078 is still under.  Nothing at or past k = 3 was
   run, and nothing needs to be — this is the Fold-Count arithmetic economy,
   the same move that put the `2 ^ k` vs `12k + 6` crossover at k = 7 without
   normalising it.

### Verdict

Five claims, four fully checkable at the depths this container reaches, and
every measurable row matches EXACTLY — 3 D values, 2 increments, 3 fire
vectors, 3 delivery splits, 6 generation counts, 3 cReg, 3 cSize, 2 mPre.
The only deviation anywhere is claim 3's range being written one short of
the range its own values occupy.  The law was fitted on L ≤ 4 and holds
out-of-sample at L = 5.

`D ≤ 2 ^ cReg * 2 ^ cReg` is therefore FALSE, at k = 5 on this ladder.
