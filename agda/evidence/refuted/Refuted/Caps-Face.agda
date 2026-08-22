-- ══════════════════════════════════════════════════════════════════
-- CAPS-FACE: two impossible frame bounds
--
-- REFUTATIONS: machine-checked `… → ⊥`.  Each theorem here says a route
-- CANNOT work, and says it in a form the typechecker rechecks — unlike a
-- prose note, which decays silently.
--
-- THIS TREE IS OUTSIDE `agda/src` ON PURPOSE (Anthony).
-- Keeping a dead route in `src` forces `src` to keep whatever machinery
-- makes the route STATE-able, and that machinery is otherwise deletable:
-- these two files held seven definitions alive in Measures for no other
-- reason.  So refutations live here, are checked by `make refuted`, and
-- are NOT subject to the wiring law — nothing in `src` may import them.
-- They do not change, so `src` refers to them in COMMENTS (`-- REFUTED:`).
-- ══════════════════════════════════════════════════════════════════
module Refuted.Caps-Face where

open import Data.Nat     using (ℕ; suc; _+_; _*_; _^_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤⇒≤ᵇ; ≤-trans; <-≤-trans; +-identityʳ; +-monoʳ-<; *-suc; m≤m+n; *-mono-≤; <-irrefl)
open import Data.Empty   using (⊥)
open import Data.Fin     using (Fin)
import Data.Fin as Fin
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Relation.Binary.PropositionalEquality
  using (refl; sym; subst)
open import Rx.Prim      using (_at_from_as_)
open import Rx.Evaluator using (sizeStep)
open import Verify-Budget-Sufficient.Measures using
  (n<2^n)
open import Verify-Budget-Sufficient.Caps using
  (Caps; caps; frameStep)


------------------------------------------------------------------
--
-- (1) THE BOUNDARY FOLD.  caps-frame's hypothesis admits a state
-- satisfying capsOK? with ZERO slack and a `b` whose size is exactly the
-- level's cSize, and demands capsOK? at the SAME level afterwards.  But
-- the subscribe frame itself folds: subscribeE's scanᵉ clause
-- (Rx/Evaluator.agda:958) installs `scan-st (evalTm seed)` and runs the
-- source's sync burst through pushBurst with the scan-f frame, and
-- dispatch updates that node once per synchronous payload.  A cap-sized
-- `b` with one duplicating fold therefore lands at sizeStep C C, above
-- C — and the arithmetic below is uniform in C, so specialising C to
-- capsAt's own tower does not escape it.
--
-- State-Blowup-Probe's framePreserves-absurd is the concrete witness:
-- pRs, whose size is 19 and whose initial state is bounded by 19, leaves
-- a size-30 node after its own root subscribe.  (The root subscribe is
-- one of caps-frame's own instances: κ = root, id = 0, level 0.)
--
-- (2) THE MID-CASCADE HYPOTHESIS, an independent defect.  caps-tick says
-- a whole cascade moves the state from level id to level suc id, so
-- mid-drain states live strictly BETWEEN the two levels.  A proof of
-- caps-tick must apply caps-frame at every inner subscribe inside that
-- cascade, and there are exactly two such call sites:
--
--  · subscribeInner   (Rx/Evaluator.agda:531) — a *All consuming an
--    obs payload mid-cascade, reached from stepFrame
--  · sharedConnect    (Rx/Evaluator.agda:871) — a shared slot's lazy
--    connect, which subscribes the def mid-cascade
--
-- At both, earlier chains in the SAME cascade have already grown the
-- store, so the level-id hypothesis is simply unavailable.  Even had (1)
-- survived, the face could not feed the induction it exists for.
--
-- THE REPAIR SHAPE UNDER EVALUATION (not yet taken on faith — it owes
-- its own probe): make the mid-instant states explicit with a
-- CONSUMED-ITERATION index.  One parametric face against level suc id
-- whose pre-state is bounded by frameBlowup partially applied — k of the
-- 2 ^ cReg * cSize iterations still unspent — and a subscribeE with fold
-- count j consuming j of k.  caps-frame and caps-tick then become the
-- two ENDPOINTS (k = full, k = 0) of a single face rather than siblings,
-- and (2) dissolves because a mid-cascade state is just a smaller k.
--
-- AND THE THING TO CHECK BEFORE BUILDING IT: this is structurally the
-- same bookkeeping the walk face's E′ receipt already does.  Two
-- parallel accounting mechanisms for one growth is a smell; if E′ can
-- carry the iteration count, caps preservation falls out of the walk
-- face instead of standing beside it as a second ledger.
------------------------------------------------------------------
--
-- caps-frame AS STATED IS FALSE, TWICE OVER.  Both halves are
-- statement-level — the face is uninstantiable, not merely unproven —
--  and the same disease class as the original vacuity.

-- the arithmetic obstruction behind (1), UNIFORM IN C: one fold from a
-- cap-sized value on a cap-sized step function always overflows the cap,
-- whatever the cap is.  This is why no choice of level rescues
-- same-level preservation
caps-frame-boundary-absurd : ∀ (C : ℕ) → 1 ≤ C → sizeStep C C ≤ C → ⊥
caps-frame-boundary-absurd C hC h = <-irrefl refl (<-≤-trans C<step h)
  where
  1≤2C : 1 ≤ 2 * C
  1≤2C = ≤-trans hC (m≤m+n C (C + 0))

  0<prod : 0 < C * (2 * C)
  0<prod = *-mono-≤ hC 1≤2C

  C<step : C < sizeStep C C
  C<step = subst (C <_) (sym (*-suc C (2 * C)))
                 (subst (_< C + C * (2 * C)) (+-identityʳ C)
                        (+-monoʳ-< C 0<prod))

------------------------------------------------------------------
-- WHAT WAS HERE, AND WHY IT IS GONE.  regsSz?-subscribeE,
-- "the chain half of ANY repaired face" — a fixed cap C, a registry
-- bounded by it, an expression of size ≤ C subscribed under a κ with
-- `pathSz? C κ` and `suc (pathLen κ) ≤ C`, concluding the registry is
-- still bounded by C.
--
-- IT IS FALSE, and `git show 94a5a3c^:agda/probe/Chain-Half-Probe.agda` computes the
-- counterexample: at C = 5, a κ of four map-f frames (both hypotheses
-- TIGHT) and `mapᵉ f (mapᵉ f (input 0))` (sizeᵉ exactly 5) register a
-- chain of length SIX.  subscribeE pushes one frame per shell of what
-- it walks, and `suc (pathLen κ) ≤ C` buys room for exactly one.
--
-- The defect is the FIXED cap, not the descent.  subscribeE-caps
-- carries the identical two hypotheses and is GROUND, because it
-- reports at `frameStep (j + j′) c` and one j at least doubles cSize
-- (frameStep-size-suc) — so the frame a hop pushes is paid for by the
-- j that hop spends.  A statement with no j has nothing to pay with,
-- and no repair of its hypotheses helps: the joint form
-- `pathLen κ + sizeᵉ b ≤ C` that would make it inductive is the one
-- Joint-Probe refuted at the tight admissible cSize, and it would in
-- any case not survive an *All hop, where the chain grows by the
-- SHELLS OF A PAYLOAD rather than of the syntax.
--
-- AND IT WAS REDUNDANT.  `capsOK?`'s second conjunct IS `regsSz?`, so
-- the ground subscribeE-caps already hands the chain half back at the
-- level it reports.  The postulate had no consumer in the tree.
------------------------------------------------------------------

------------------------------------------------------------------
-- WHAT WAS HERE, AND WHY IT IS GONE.  A fixed-height reach cap —
-- foldBudget, reachCap, reach-covers — built on the measured claim that
-- a reachable observable's tower has its HEIGHT fixed by the syntax and
-- only its BASE growing with the instant count.
--
-- deepScan refuted it: a scan whose step function contains a scan over
-- the accumulator towers ONCE PER FOLD, and folds grow one per instant,
-- so the height grows with `id`.  The machine-checked account, with the
-- recurrence and the payload counts, is the deepScan section of
-- `git show 94a5a3c^:agda/probe/Frame-Work-Probe.agda`.  The Caps recurrence above is the
-- replacement; git history is the archive for the rest.
------------------------------------------------------------------

-- WHY cSize AND cWid ARE SEPARATE FIELDS, machine-checked so that nobody
-- collapses them.  The tempting move is to carry size only and derive
-- width from it — the way hopD-sizeᵉ derives hop depth from szB of size,
-- which is exactly why cHop is NOT a field.  THAT ROUTE IS CIRCULAR for
-- width.  outW is not polynomial in size: pWᵉ (mergeAllᵉ e)
-- is pWᵉ e * innWᵉ e and innWᵉ towers at a scanᵉ, so any size-to-width
-- bound is at least exponential, and the cap would have to dominate an
-- exponential of itself.
--
-- The non-circular route is to iterate them TOGETHER, which is what the
-- Caps recurrence does: one instant's folds are counted by the current
-- width and each fold costs one foldStep, so the next width comes from
-- the current width and the current cascade count — never from the size.
--
-- This is the fourth time this loop has been available in this proof
-- (walk-hyps-absurd, hop-anchor-absurd, round3b-ledger-reset-absurd, and
-- now here), so it gets a witness rather than a warning
reach-via-size-absurd : ∀ (C : ℕ) → 2 ^ C ≤ C → ⊥
reach-via-size-absurd C h = <-irrefl refl (<-≤-trans (n<2^n C) h)

-- ══════════════════════════════════════════════════════════════════
-- WALK-SCAN'S APPLICATION COUNT IS NOT FUNDED BY THE SIZE CEILING
--
-- `hopDᵉ`'s scan clause (Rx.Hop-Depth) bounds a scan's output at
-- `(2 + pmᵗ V 0 f) ^ V * B`, and the fold invariant that clause is
-- evidently sized for — `Aₖ ≤ (1 + (pmᵗ V 0 f ⊔ 1)) ^ k * B`, over
-- PROVEN hopD-applyFn — closes when `k ≤ V`.  With P = pmᵗ V 0 f ⊔ 1
-- that demand is real only for AMPLIFYING folds: at P = 1 the recurrence
-- is additive and `1 + k ≤ 2 ^ V` suffices, while at P ≥ 2 the need is
-- `k ≤ V * log(2+P)/log(1+P)`, i.e. `k ≤ V` up to a constant (1.26 at
-- P = 2).  So this witness bounds the P ≥ 2 region, which is the one the
-- clause is actually exposed on.
--
-- `k` is the number of source values one scan node folds inside a single
-- subscribe burst, and the only thing bounding it is `burstCount?`
-- (.Caps-Face/Part1), which caps INSTANTS and PER-INSTANT VALUES
-- separately, each by `suc (Caps.cWid c)` — so `k` is bounded by a
-- WIDTH SQUARED and by nothing smaller.  The only lower bound the walk
-- face states on `V = Ŝ` is `Caps.cSize (frameStep L̂ c) ≤ Ŝ`: a SIZE.
--
-- The two axes diverge, and that is what this pins.  A level step
-- EXPONENTIATES the width (`foldStep S w = S ^ suc w`, so `cWid
-- (frameStep j c)` is a tower of height j) and merely SCALES the size
-- (`sizeStep S s = S * suc (2 * s)`, geometric in j).  At the smallest
-- admissible caps the squared width passes the size at j = 2 (81 vs 42)
-- and the bare width passes it at j = 3 (512 vs 170).
--
-- AND THERE IS NO LEVEL OFFSET TO SPEND, which is what makes this a
-- refutation rather than an off-by-one: the ceiling requires only
-- `opIterD … ≤ L̂`, while the walk's own exit level is bounded by that
-- same `opIterD …` — so `L̂ := opIterD …` is admissible and the width
-- and the size are then read at the SAME level.
--
-- `ops ≥ 1` (WalkTail's `suc (sizeᵉ b) ≤ ops`) does not rescue it — it
-- constrains opIterD's iteration count, not the relation between the two
-- axes at a level.
--
-- ⚠ SCOPE, ADDED AFTER THIS WAS READ TOO WIDELY.  What is
-- refuted is bounding the fold's exponent FROM THE CEILING PINS.  It is
-- NOT a blocker on walk-scan, and it does NOT show a width ceiling is the
-- missing hypothesis — an earlier draft of this note said exactly that
-- and cost the row a spurious SHAPE classification plus a detour through
-- three candidate ceilings.  The exponent is bounded from the STORE
-- INVARIANT instead: `boundedNode B (scan-st v) = sizeᵛ v ≤ᵇ B`, supplied
-- by WalkTail's own `INV?` hypothesis and carried to `Ŝ` by `ceil`.  That
-- was worked out and is recorded in Keeps-Ring's header.
-- This witness stays because the ceiling route is genuinely dead and
-- someone will propose it again; it decides nothing else.
-- ══════════════════════════════════════════════════════════════════
scan-count-under-ceiling-absurd :
  (∀ (c : Caps) (j : ℕ) → 2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
     Caps.cReg c ≤ Caps.cSize c →
     suc (Caps.cWid (frameStep j c)) * suc (Caps.cWid (frameStep j c))
       ≤ Caps.cSize (frameStep j c)) → ⊥
scan-count-under-ceiling-absurd h =
  ≤⇒≤ᵇ (h (caps 2 0 1) 2 (s≤s (s≤s z≤n)) (s≤s z≤n) (s≤s z≤n))

-- the bare width passes the size one level later — the same divergence
-- without the squaring.  Kept because it is the form any future route
-- through `cWid ≤ cSize` reaches for, and because it is what kills the
-- obvious repair to walk-scan: `capsAt e sl (suc id)` IS a `frameStep N`
-- (Caps: `capsAt e sl (suc id) = frameBlowup (capsAt e sl id) …`), and
-- `sizeCapAt e sl id ≡ Caps.cSize (capsAt e sl id)` (.Wet/Part6), so
-- adding a WIDTH ceiling stated against Ŝ asks for the width and the size
-- of the same caps to be ordered the wrong way.  Unsatisfiable at the one
-- instantiation that matters, for N ≥ 3.
wid≤size-absurd :
  (∀ (c : Caps) (j : ℕ) → 2 ≤ Caps.cSize c →
     Caps.cWid (frameStep j c) ≤ Caps.cSize (frameStep j c)) → ⊥
wid≤size-absurd h = ≤⇒≤ᵇ (h (caps 2 0 1) 3 (s≤s (s≤s z≤n)))
