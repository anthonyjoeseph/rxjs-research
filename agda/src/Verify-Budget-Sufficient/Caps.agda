-- STRATUM 1c of Verify-Budget-Sufficient: THE CAPS RECURRENCE ITSELF.
--
-- The Caps triple, the per-fold step functions (sizeStep / foldStep and
-- their iterates), frameStep, frameBlowup, the recurrence capsAt, the
-- j-monotonicity toolkit, and the supply lemmas that read a level off
-- the recurrence (2≤capsAt-size, 1≤capsAt-reg, cSize≤frameBlowup,
-- capsAt-base-size, cWid≤frameBlowup, capsAt-base-wid) — and the TOWER
-- BOUND capsAt-tower, which says how fast the recurrence can climb.  It
-- is no longer a CLOSED height: the count reads cWid and the width axis
-- pays two tower stories per fold, so the height is `blowH` iterated per
-- instant, the very function `budgetAt` is defined from.
--
-- WHY IT IS ITS OWN MODULE — the .Keeps-Ring precedent, applied a second
-- time.  .Wet reads the caps recurrence (its store bound and its reset
-- caps are `Caps.cSize (capsAt e sl id)`), but it reads NOTHING ELSE from
-- the caps face: not capsOK?, not subscribeE-caps, not caps-tick.  With
-- the recurrence inside .Caps-Face, every edit to a caps-face PROOF
-- re-checked .Wet and thence Verify-Well-Formed — the two most expensive
-- modules in the build — for no reason.  Extracted here, .Caps-Face and
-- .Wet are again siblings over a shared prerequisite, and a caps-face
-- grind costs one module.
--
-- Nothing in here mentions the evaluator's dynamics: capsAt is a
-- recurrence on the syntax and the slot telescope alone, which is what
-- makes it entry-computable.  The ROUND-5 GATE lives here too — frameStep
-- and frameBlowup take a Caps and a depth fuel, so they cannot read the
-- ledger, and round3b-ledger-reset-absurd stays unavailable.
module Verify-Budget-Sufficient.Caps where

open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤-trans; ≤-refl; ≤-reflexive; +-assoc; +-comm; *-suc; *-assoc; *-monoˡ-≤; *-monoʳ-≤;
  *-mono-≤; +-monoˡ-≤; +-monoʳ-≤; +-mono-≤; +-identityʳ; +-suc; m≤m+n; m≤n+m; n≤1+n; m≤m*n; m≤m⊔n;
  ^-monoʳ-≤; ^-monoˡ-≤; <⇒≤; ^-*-assoc; *-comm; *-distribˡ-+; *-identityʳ; *-identityˡ)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂; module ≡-Reasoning)

open import Rx.Exp       using (Ctx; Closed; sizeᵉ)
open import Rx.Frame-Width using (entryCeil; ceilᵉ; dWᵉ; dW≤ceil)
open import Rx.Evaluator using (blowH; capsHgo; capsBase;
                                foldStep; iterFold; sizeStep; iterSize;
                                sizeAt; widAt; regAt; fCharge; fLvl; iterL;
                                dLvl; lvls; dCapᶜ; dWalkᶜ;
                                poolBody; poolCount; blowH-body;
                                fLvlD; sIterD; sLvlD; opIterD; fIterD;
                                fLvlD-0; fLvlD-suc; sIterD-0; sIterD-suc;
                                sLvlD-0; sLvlD-suc; opIterD-0; opIterD-suc;
                                fIterD-0; fIterD-suc)
open import Rx.Slots using (Slots; slotsSize)
open import Rx.Slot-Clos using (slotsClos)

-- for n<2^n (foldStep's inflationary proof) and the whole stratum below,
-- which .Caps-Face and .Wet both re-export through this module
open import Verify-Budget-Sufficient.Measures using
  (2X≡X+X; k≤towerℕ; n<2^n; sizeᵉ-pos; sq≤2^; towerℕ-mono; one≤3^)
open import Rx.Prim using (towerℕ)

------------------------------------------------------------------
-- ROUND 4: PER-INSTANT CAPS, BY RECURRENCE ON THE INSTANT.
--
-- deepScan killed the fixed-height cap (see the refutation below).  What
-- replaces it is NOT a bigger closed formula — it is a recurrence:
--
--     Caps 0        = the entry measure (program + slot telescope)
--     Caps (suc id) = frameBlowup (Caps id) (capsH id)
--
-- with frameBlowup the worst one instant's cascades can do to a state
-- already inside a given cap.  deepScan itself says what that has to
-- cover: within a frame, fold counts are bounded by current WIDTHS, and
-- each fold adds a tower level, so frameBlowup is a tower of height ~its
-- argument and Caps is Ackermann-flavoured in id.  That is acceptable —
-- it is computable, and it is entry-determined GIVEN id, which was
-- always a budget parameter (sizeBudgetAt already takes it).
--
-- WHY THE OLD PRESERVABILITY OBJECTION DOES NOT APPLY.  The fixed-height
-- shape was justified by "an invariant whose height climbs per instant
-- cannot be preserved by a per-frame induction".  That conflated frame
-- crossings with TICK crossings.  Within one frame `id` is FROZEN: every
-- hop, connect and μ edge of a single walk happens at one instant, so
-- the walk face takes its caps as ordinary fixed numbers however they
-- depend on id.  The height climbs only at tick boundaries — which is
-- exactly where the top-level per-instant induction hands over anyway.
-- That is why the face below has TWO halves and only one of them moves.
--
-- THE ROUND-5 GATE IS THE TYPE.  `frameBlowup : Caps → ℕ → Caps` cannot read
-- the ledger, the receipt, or E, because they are not arguments.  If any
-- within-frame quantity turns out to be boundable ONLY by the ledger,
-- round3b-ledger-reset-absurd fires again and that is a stop-and-report,
-- not a signature to widen.
--
-- THE TUPLE, and why hop rank is not in it: cSize and cWid are
-- independent — reach-via-size-absurd shows width cannot be derived from
-- size — and cReg counts the cascades whose blowups compose within one
-- instant.  Hop rank IS derivable, from cSize by hopD-cap, which is what
-- reach-resets proves; carrying it would be a synonym.
------------------------------------------------------------------

record Caps : Set where
  constructor caps
  field
    cSize : ℕ      -- every reachable value's size
    cWid  : ℕ      -- every reachable observable's FRAME width
    cReg  : ℕ      -- live registrations, hence cascades, in one instant


-- THE WORST ONE INSTANT CAN DO, and a function of Caps ALONE — the
-- signature is the round-5 gate, not a comment about one.
--
-- All three components share ONE iteration count, `j`, and this
-- function does not name it: `frameStep` is parametric in the count and
-- every lemma about it below is too, so replacing the count (which has
-- now happened twice) touches `frameBlowup` and nothing else.
--
-- regBlowup is ADDITIVE in the sources, not multiplicative: pR2's two
-- live inputs take the registry 1 ↦ 3, one new registration per
-- referenced source, because a fold subscribes each reference once.  Its
-- cSize factor is exactly that reference count — a fold can subscribe no
-- more references than its step function mentions — and pR2 is why it is
-- there: with `cReg * suc cWid` alone the measured 1 ↦ 3 does not fit
-- j FOLDS' WORTH, so a frame's PROGRESS is explicit rather than
-- all-or-nothing.  This is the repair caps-frame's refutation forces:
-- same-level preservation is false, so the face must report growth, and
-- the honest index of growth inside a frame is the fold count.
--
-- The two endpoints are exactly what caps-frame and caps-tick were each
-- trying to be on their own — j = 0 is frame entry, j = the full count is
-- the tick boundary — so they stop being siblings and become the ends of
-- one measure.  A mid-cascade state, which had no level at all before,
-- is just a smaller j
frameStep : ℕ → Caps → Caps
frameStep j c =
  caps (iterSize (Caps.cSize c) j (Caps.cSize c))
       (iterFold (Caps.cSize c) j (Caps.cWid c))
       (Caps.cReg c * suc (j * Caps.cSize c))

-- THE COUNT, and it is EXPONENTIAL in cReg — the second correction this
-- number has taken, each from a probe rather than from the proof.
--
--   · `cWid * cReg` was refuted by J-Budget-Probe: its pM family fixes
--     the whole triple at (7, 1, 1) and still stores 15 … 4371 in one
--     cascade, so no count read off the triple can work until the triple
--     bounds the CHAIN LENGTH — which pathSz?'s pathLen conjunct does.
--   · `cWid * cReg * cSize` was then refuted by Fold-Count-Probe, and
--     not by a factor: nested shares make ONE cascade's delivery count
--     exponential in the number of shared slots (2 ^ (k+2) - 2) while
--     every component of the triple stays linear (registrations 2k + 2,
--     cSize and cWid constant).  2 ^ k passes 12k + 6 for good at k = 7.

-- THE SHAPE THAT SURVIVES, derived from the share DAG rather than
-- guessed, and REPAIRED once since: the first derivation had a false
-- middle step and Mint-Loop-Probe caught it.
--
-- A delivery is a path r₁ → r₂ → … through the registration DAG —
-- `foldPath` walks a chain without branching and `dispatchShare` fans out
-- to every registration `shareAdmit` returns — and the path is simple,
-- since a repeat would be a cycle in the slot graph, which the slot defs
-- fix at entry.  A DAG on R nodes carries at most `2 ^ R - 1` paths, one
-- per subset.  The step that FAILS is reading R as cReg:
--
--     deliveries ≤ 2 ^ cReg          -- FALSE, and measured false

-- The R of that count is the registry AT THE END of the cascade, not at
-- entry, because `shareAdmit` reads the live registry; a fold that mints
-- on a shared slot adds a node mid-traversal.  Mint-Loop-Probe's
-- three-level lean ladder at k = 2 delivers 176 times out of an ENTRY
-- registry of 7, and 2 ^ 7 = 128.  So the excess is real, `D * cSize`
-- is itself over `2 ^ cReg * cSize`, and the whole paths-times-frames
-- route through that middle step is gone.

-- WHAT SURVIVES IS THE SAME INJECTION WITH A SECOND COORDINATE.  A
-- delivery is sent not to the set of registrations it visits but to the
-- PAIR (the pre-state registrations it visits, an index for which minted
-- registrations it went through).  The first coordinate ranges over
-- subsets of the entry registry — `2 ^ cReg` of them.

-- THE SECOND COORDINATE IS NOT BOUNDED BY cSize, and that was the second
-- thing measured false here.  It was first stated so, on the reasoning
-- that a mint is born of a subscribe inside ONE frame and a frame's step
-- function can name no more sources than its own syntax holds.
-- Mint-Loop-Probe's MEASUREMENT 6 computes the coordinate directly — the
-- fibre of a pre-state class — and gets 4 against a cSize of 3 on the
-- lean two-level ladder and 8 against 3 on the lean three-level one.
-- The lean families exist for exactly this: they keep the delivery
-- structure and shrink the syntax the cap is read off.

-- AND THAT SQUARE IS FALSE TOO — the third correction, and the first
-- one predicted before it was measured.  The pair story gave
--
--     deliveries ≤ 2 ^ cReg * 2 ^ cReg    frames per delivery ≤ cSize
--
-- and the L = 5 mint ladder breaks it.  Delivery-Law-Prediction.md
-- committed the delivery law BEFORE any L = 5 row existed — fires of
-- shared slot i are 2 ^ (L ∸ i), mint generation g holds C(2 ^ L, g)
-- registrations, so the per-rung increment is C(2 ^ L, k + 3) — and the
-- measurement matched every checkable row exactly (3 D values, 2
-- increments, 3 fire vectors, 6 generation counts).  The law then puts
-- D(5,5) at 4514934 against `4 ^ cReg = 4 ^ 11 = 4194304`.  The true
-- growth is `2 ^ (2 ^ L)`-shaped — DOUBLY exponential in the ladder
-- depth, hence a 2-TOWER over cReg, not any single exponential and not
-- a square of one.

-- AND THE 2-TOWER `2 ^ (2 ^ cReg)` IS GONE TOO — not because a row
-- breached it (none does) but because NOTHING CAN PROVE IT.  Every
-- route to a bound that reads cReg alone needs two facts, and the two
-- together are vacuous:
--
--     R ≤ cReg + Q · D          (the registry grows only by mints, and
--                                a mint is a charged step, so the mints
--                                are at most Q per delivery)
--     D ≤ (1 + R) ^ (1 + n)     (a delivery is named by its path through
--                                the registration DAG; the dispatch gas
--                                caps the depth at n and the share
--                                telescope orders the shares strictly)
--
-- which is `D ≤ (1 + cReg + Q · D) ^ (1 + n)` — the right-hand side
-- outgrows the left at EVERY D, so the pair bounds nothing whatever the
-- constants are.  That is Worker 24's self-reference, and it is not
-- repaired by making the bound bigger: any closed form F would have to
-- satisfy `F ≥ (1 + cReg + Q · F) ^ (1 + n)`, and no natural number
-- does.

-- SO THE BOUND STOPS BEING A FORMULA AND BECOMES A RECURSION, `cDel`,
-- exactly as the caps themselves did.  `dCap` (Rx.Evaluator) is the
-- SEQUENTIAL reading of the very same two facts: the walk is done one
-- chain at a time, and the registry a chain sees is the entry registry
-- plus the mints of the deliveries ALREADY MADE.  That is the ordering
-- fact the mint loop natively obeys — a minted registration is
-- reachable only by dispatches that come AFTER it — and recursion on
-- (dispatch gas, walk position) is well-founded where the closed form
-- was circular.  The refuted routes are recorded at
-- cascadeGo-deliveries in .Caps-Face; this is what replaces them.

-- IT IS ACKERMANN-FLAVOURED IN THE GAS, and the height pays for that by
-- READING it: `blowH` is `6 + m + 2 · poolCount (towerℕ m)`, and
-- poolCount IS this count with every field pooled.  The per-instant
-- story increment is then a MONOTONICITY fact rather than a tower
-- estimate — which is strictly cheaper than the old four-story
-- accounting it replaces.
--
-- cWid IS GONE, and it was never a factor of this count — it bounds how
-- WIDE one emitted observable is, not how many times a cascade iterates.
-- Fold-Count-Probe's diamond makes that concrete: `mWid` there is ZERO
-- while the cascade really delivers eight times, so the old product was
-- identically 0 on a program with real work to do.  The duty cWid was
-- carrying (pR vs pRs, 3 ↦ 12 against 3 ↦ 30) belongs to the per-fold
-- `foldStep` / `sizeStep` gates, which is where State-Blowup-Probe
-- checks it.

-- AND cWid MAY NEVER COME BACK INTO THE COUNT.  Width-Count-Probe
-- proves the reason: `iterFold` EXPONENTIATES per fold, so j folds put
-- the width above towerℕ j, and a count that reads cWid would iterate
-- the tower function once per instant — capsAt-tower's linear height,
-- and with it caps-fuel-root, would be gone (17 stories demanded
-- against 13 available at the smallest program there is).  That is why
-- the charge below is `D * cSize` and not `D * (a polynomial in cWid)`,
-- even though the frame receipt scanFrame-caps actually pays is
-- `suc (length vals * suc (sizeᵗ fn))` and `length vals` is a burst
-- width.  Where that width is paid for is the open question the charge
-- face carries.

-- The cSize factor still reads cSize because that is where the length
-- conjunct puts it, not because a length is a size: `pathLen p ≤ᵇ cSize`
-- is a separate conjunct of the same field, and at pM 6 the two
-- genuinely differ (a 9-frame chain in a state whose largest term
-- measures 7).

-- STILL INSIDE THE ROUND-5 GATE: the count reads the Caps triple and
-- nothing else, so round3b-ledger-reset-absurd stays unavailable

-- ONE CASCADE's DELIVERY BOUND, BY RECURRENCE.  The dispatch gas is the
-- decreasing potential (it caps the depth at the slot count, hence at
-- cSize), the walk starts at LEVEL 0 — the entry caps themselves,
-- `frameStep 0 c ≡ c` — and every registry length, chain cap and
-- per-frame receipt the walk reads is read off the level it has climbed
-- to.  Nothing is charged at the entry caps, and charging there is
-- machine-refuted.
--
-- ABSTRACT, and it is a NORMALISATION contract rather than an
-- abstraction one.  `iterSize` and `iterFold` pattern-match on the
-- COUNT, so `capsAt`'s own cSize is `iterSize S (sizeCount c d) S` — and
-- whether that reduces is decided by whether sizeCount does.  The
-- 2-tower it replaces never did (`2 ^ (2 ^ suc X)` is stuck at a
-- variable X), but the walk peels a suc off its GAS and re-enters at a
-- larger level, so every consumer of `sizeCapAt` pays for it.  .Wet ran
-- past an hour on that (measured twice) and finishes in minutes with the
-- count opaque
abstract
  cDel : Caps → ℕ → ℕ
  cDel c d = dCapᶜ (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d
                   (suc (Caps.cSize c)) 0

  cDel-body : ∀ (c : Caps) (d : ℕ) →
    cDel c d ≡ dCapᶜ (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d
                     (suc (Caps.cSize c)) 0
  cDel-body c d = refl

-- and it is POSITIVE once there is a chain to walk, which is what the
-- count's own `1 ≤ J` side conditions read: the walk's first position
-- is the entry registry, and `regAt S R 0` is `R`
1≤dWalkᶜ : ∀ (S W R d g J i : ℕ) → 1 ≤ i → 1 ≤ dWalkᶜ S W R d g J i
1≤dWalkᶜ S W R d g J (suc i) hi =
  ≤-trans (s≤s z≤n)
          (m≤n+m (suc (dCapᶜ S W R d g
                        (lvls S W d J (suc (dWalkᶜ S W R d g J i)))))
                 (dWalkᶜ S W R d g J i))

1≤regAt : ∀ (S R J : ℕ) → 1 ≤ R → 1 ≤ regAt S R J
1≤regAt S R J hR =
  ≤-trans hR (≤-trans (≤-reflexive (sym (*-identityʳ R)))
                      (*-monoʳ-≤ R (s≤s z≤n)))

1≤dCapᶜ : ∀ (S W R d g J : ℕ) → 1 ≤ R → 1 ≤ dCapᶜ S W R d (suc g) J
1≤dCapᶜ S W R d g J hR =
  1≤dWalkᶜ S W R d g J (regAt S R J) (1≤regAt S R J hR)

-- and `poolCount` IS `poolBody` wherever there is anything to count:
-- the match in front of it (Rx.Evaluator) is a normalisation guard, not
-- a definition by cases
poolBody≤poolCount : ∀ (M d : ℕ) → 1 ≤ M → poolBody M d ≤ poolCount M d
poolBody≤poolCount (suc M) d _ = ≤-refl

-- ONE INSTANT's FOLD COUNT, AND IT IS THE WALK'S OWN LANDING LEVEL.
-- The receipt `scanFrame-caps` actually pays is
-- `suc (length vals * suc (sizeᵗ fn))` — one fold per node of the step
-- function PER PAYLOAD — so the count reads cWid; that much was already
-- measured (Charge-Probe: `j ≤ D * cSize` breaches at 47 against 40).
-- What changed is the SHAPE.  The product
--
--     cDel c * cSize c * suc (suc cWid * suc cSize)
--
-- charges every delivery's frames at the level the CASCADE entered at,
-- and that is the same entry-charging one stratum down that
-- Entry-Caps-Refuted machine-refutes: what the walk proves
-- (`cascadeGo-level`, .Caps-Face) is that a cascade LANDS at
-- `lvls S W 0 D`, an ITERATION — each delivery charged at the level the
-- one before it LEFT, each frame at the level the one before IT left.
-- So the count is that landing level, and the per-instant charge stops
-- being a postulate: `cascadeGo-caps` is `cascadeGo-level` composed with
-- `cascadeGo-deliveries` and nothing else.
--
-- IT DOMINATES THE PRODUCT IT REPLACES, so no measured row moves:
-- a linearity step at J = 0 gives `D * chargeAt S W 0 ≤ lvls S W 0 D`, and
-- `chargeAt S W 0` IS `cSize * suc (suc cWid * suc cSize)`
-- (measured by a probe module since DELETED; git history has the rows).
--
-- READING cWid WAS FORBIDDEN AND IS NO LONGER.  Width-Count-Probe's
-- objection was that a count reading cWid iterates the tower function
-- once per instant, which destroys a `towerℕ`-of-LINEAR-height bracket.
-- That bracket is gone by construction now — the budget's own height
-- (`capsHgo` over `capsBase`, Rx.Evaluator) is a recurrence, not a
-- closed form, and it climbs by exactly what the inequalities below
-- demand.  The price is that the height is
-- tower-VALUED; the price of a lazy Gas tower's height being large is
-- nothing at all
--
-- ABSTRACT, for `cDel`'s reason and with `cDel`'s discipline: `lvls`
-- matches on the delivery count, `iterSize` and `iterFold` match on
-- this one, and `capsAt`'s own fields are those iterates — so whether
-- .Wet normalises or runs for an hour is decided by whether this symbol
-- stays stuck.  `sizeCount-body` hands the body back where the
-- recurrence's own arithmetic needs it, which is three places
abstract
  sizeCount : Caps → ℕ → ℕ
  sizeCount c d = lvls (Caps.cSize c) (Caps.cWid c) d 0 (cDel c d)

  sizeCount-body : ∀ (c : Caps) (d : ℕ) →
    sizeCount c d ≡ lvls (Caps.cSize c) (Caps.cWid c) d 0 (cDel c d)
  sizeCount-body c d = refl

frameBlowup : Caps → ℕ → Caps
frameBlowup c d = frameStep (sizeCount c d) c

-- the entry endpoint, by computation
frameStep-0 : ∀ (c : Caps) → frameStep 0 c ≡ c
frameStep-0 (caps s w r) = cong (λ x → caps s w x) (*-identityʳ r)

------------------------------------------------------------------
-- THE ARITHMETIC CORE OF THE REPAIR, proven ahead of subscribeE-caps
-- because it is the piece that would kill the shape if it failed: does
-- frameStep's per-j increment DOMINATE one fold applied to frameStep j?
-- The induction consumes exactly this at every clause.  All three
-- dimensions reduce to "iterating a fixed step commutes", iter-f (suc j)
-- = f (iter-f j), because sizeStep S / foldStep S apply the SAME S each
-- time — the whole reason S is read off cSize once rather than per fold.
------------------------------------------------------------------

-- SIZE.  iterSize S j is the j-fold composition of (sizeStep S), so one
-- more step at the OUTSIDE equals one more at the inside
iterSize-suc : ∀ (S j s : ℕ) → iterSize S (suc j) s ≡ sizeStep S (iterSize S j s)
iterSize-suc S zero    s = refl
iterSize-suc S (suc j) s = iterSize-suc S j (sizeStep S s)

-- so a size-step on the state at frameStep j lands within frameStep (suc j)
frameStep-size-suc : ∀ (c : Caps) (j : ℕ) →
  Caps.cSize (frameStep (suc j) c) ≡ sizeStep (Caps.cSize c) (Caps.cSize (frameStep j c))
frameStep-size-suc c j = iterSize-suc (Caps.cSize c) j (Caps.cSize c)

-- WIDTH.  identically for foldStep
iterFold-suc : ∀ (S j w : ℕ) → iterFold S (suc j) w ≡ foldStep S (iterFold S j w)
iterFold-suc S zero    w = refl
iterFold-suc S (suc j) w = iterFold-suc S j (foldStep S w)

frameStep-wid-suc : ∀ (c : Caps) (j : ℕ) →
  Caps.cWid (frameStep (suc j) c) ≡ foldStep (Caps.cSize c) (Caps.cWid (frameStep j c))
frameStep-wid-suc c j = iterFold-suc (Caps.cSize c) j (Caps.cWid c)

-- REGISTRATIONS.  the cReg dimension is linear in j, so one more j buys
-- exactly cReg * cSize more headroom — enough for the registrations one
-- fold mints, which is at most the step function's reference count ≤ cSize
frameStep-reg-suc : ∀ (c : Caps) (j : ℕ) →
  Caps.cReg (frameStep j c) + Caps.cReg c * Caps.cSize c
    ≡ Caps.cReg (frameStep (suc j) c)
frameStep-reg-suc (caps s w r) j =
  begin
    r * suc (j * s) + r * s
  ≡⟨ cong (_+ r * s) (*-suc r (j * s)) ⟩
    (r + r * (j * s)) + r * s
  ≡⟨ +-assoc r (r * (j * s)) (r * s) ⟩
    r + (r * (j * s) + r * s)
  ≡⟨ cong (r +_) (sym (*-distribˡ-+ r (j * s) s)) ⟩
    r + r * (j * s + s)
  ≡⟨ cong (λ x → r + r * x) (+-comm (j * s) s) ⟩
    r + r * (suc j * s)
  ≡⟨ sym (*-suc r (suc j * s)) ⟩
    r * suc (suc j * s)
  ∎
  where open ≡-Reasoning

-- BY RECURRENCE, never in closed form.
--
-- THE BASE CASE PAYS FOR ITS OWN FRAME.  The root subscribe IS a frame:
-- a synchronous source folds inside it, so the state handed to instant 0
-- has already grown.  pRs ends its root frame at size 30 where the bare
-- syntactic measure allows 25 (State-Blowup-Probe), so the base is one
-- frameBlowup above the syntax — exactly what caps-frame already says
-- about every other frame
-- THE HEIGHT OF THE RECURRENCE, and it is read BEFORE `capsAt` because
-- `capsAt` spends it: instant id's blowup runs at the depth fuel
-- `capsH e sl id`, the story index the SAME recurrence has reached
-- there.  `blowH` makes the identical reading one level down
-- (`poolCount (towerℕ m) m`, Rx.Evaluator), which is what lets
-- `blowup-tower` compare the two counts at one fuel
capsH : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → ℕ → ℕ
capsH e sl id = capsHgo (capsBase e sl) id

-- A CAP DOES NOT EVALUATE, SO NOTHING PRICED IN ONE CAN BE PUT TO A
-- ROW.  `frameBlowup c d` is `frameStep` at the count `sizeCount c d`,
-- and that count is `lvls` iterating `dLvl` as many times as `cDel c d`
-- says -- so `exp≤dLvl` makes one iteration at least an exponential and
-- the count at least a tower of twos of that height.  The sealing
-- already shut the typechecker; what this shuts is the COMPILED route,
-- which is otherwise the standing answer to a sealed family, since the
-- backend ignores `abstract` and runs the real body.  It does not help
-- here, and shrinking the program does not either: `2 ≤ cSize` holds of
-- every cap a program can reach, which is all `exp≤dLvl` asks for.
--
-- DEAD ROUTE: pricing any caps-denominated bound by a harness row.
--   The base fields and `capsBase` print at once at a corpus program,
--   and `cDel` at that same base does not return -- so the wall stands
--   BELOW the recurrence, at the count feeding it, and no smaller
--   program moves it.  Assembling a small cap by hand instead is the
--   hand-built-state trap: it is not one `capsAt` reaches, so a row
--   over it is evidence about nothing.

capsAt : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → (id : ℕ) → Caps
capsAt {n = n} e sl zero =
  frameBlowup (caps (2 + sizeᵉ e + slotsSize sl + slotsClos sl)
                    (suc (entryCeil n sl e))
                    (suc (sizeᵉ e + slotsSize sl)))
              (capsBase e sl)
capsAt e sl (suc id) = frameBlowup (capsAt e sl id) (capsH e sl id)

-- caps ordering: pointwise on the three fields
_⊑ᶜ_ : Caps → Caps → Set
c ⊑ᶜ c′ = (Caps.cSize c ≤ Caps.cSize c′)
        × (Caps.cWid  c ≤ Caps.cWid  c′)
        × (Caps.cReg  c ≤ Caps.cReg  c′)

------------------------------------------------------------------
-- frameStep IS MONOTONE IN j — the last toolkit piece.  The induction
-- lifts a sub-result at frameStep (j + a) to frameStep (j + b) for
-- a ≤ b (via capsOK?-mono), which needs frameStep j c ⊑ᶜ frameStep j′ c
-- for j ≤ j′.  Each iterated component is inflationary because its step
-- is: sizeStep needs 1 ≤ S, foldStep needs 2 ≤ S — and cSize (which is
-- S) is ≥ 2 for every real cap (the base is 2 + sizeᵉ + …).
------------------------------------------------------------------

-- SIZE: sizeStep is inflationary for S ≥ 1, and iterating it only grows
s≤2s : ∀ (s : ℕ) → s ≤ 2 * s
s≤2s s = m≤m+n s (s + 0)

sizeStep-infl : ∀ (S s : ℕ) → 1 ≤ S → s ≤ sizeStep S s
sizeStep-infl S s hS =
  ≤-trans (≤-trans (s≤2s s) (n≤1+n (2 * s)))
          (≤-trans (≤-reflexive (sym (*-identityˡ (suc (2 * s)))))
                   (*-monoˡ-≤ (suc (2 * s)) hS))
  -- 1 * suc(2s) is definitionally suc(2s), so *-identityˡ closes the gap

iterSize-infl : ∀ (S : ℕ) → 1 ≤ S → ∀ (k s : ℕ) → s ≤ iterSize S k s
iterSize-infl S hS zero    s = ≤-refl
iterSize-infl S hS (suc k) s =
  ≤-trans (sizeStep-infl S s hS) (iterSize-infl S hS k (sizeStep S s))

iterSize-mono-count : ∀ (S s : ℕ) → 1 ≤ S → ∀ {j j′ : ℕ} → j ≤ j′ →
  iterSize S j s ≤ iterSize S j′ s
iterSize-mono-count S s hS {j′ = j′} z≤n      = iterSize-infl S hS j′ s
iterSize-mono-count S s hS           (s≤s le)  = iterSize-mono-count S (sizeStep S s) hS le


-- WIDTH: foldStep is inflationary for S ≥ 2 (w < 2^w ≤ 2^(1+w) ≤ S^(1+w))
foldStep-infl : ∀ (S w : ℕ) → 2 ≤ S → w ≤ foldStep S w
foldStep-infl S w hS =
  ≤-trans (<⇒≤ (n<2^n w))
          (≤-trans (^-monoʳ-≤ 2 (n≤1+n w))    -- 2^w ≤ 2^(suc w)
                   (^-monoˡ-≤ (suc w) hS))     -- 2^(suc w) ≤ S^(suc w)

iterFold-infl : ∀ (S : ℕ) → 2 ≤ S → ∀ (k w : ℕ) → w ≤ iterFold S k w
iterFold-infl S hS zero    w = ≤-refl
iterFold-infl S hS (suc k) w =
  ≤-trans (foldStep-infl S w hS) (iterFold-infl S hS k (foldStep S w))

iterFold-mono-count : ∀ (S w : ℕ) → 2 ≤ S → ∀ {j j′ : ℕ} → j ≤ j′ →
  iterFold S j w ≤ iterFold S j′ w
iterFold-mono-count S w hS {j′ = j′} z≤n      = iterFold-infl S hS j′ w
iterFold-mono-count S w hS           (s≤s le)  = iterFold-mono-count S (foldStep S w) hS le


------------------------------------------------------------------
-- THE LEVEL WALK'S OWN ARITHMETIC.  The recursion itself is in
-- Rx.Evaluator (the pooled count `poolBody` reads it, and that is where
-- the budget's height function lives); everything it needs proven about
-- itself is here.
------------------------------------------------------------------

-- THE LEVEL COMPOSES, which is what makes the walk decompose from the
-- FRONT — an equality, so the change of direction the head-first
-- evaluator forces costs nothing
lvls-add : ∀ (S W d J a b : ℕ) →
  lvls S W d J (a + b) ≡ lvls S W d (lvls S W d J a) b
lvls-add S W d J a zero    = cong (lvls S W d J) (+-identityʳ a)
lvls-add S W d J a (suc b) =
  trans (cong (lvls S W d J) (+-suc a b))
        (cong (dLvl S W d) (lvls-add S W d J a b))

dWalkᶜ-front : ∀ (S W R d g J i : ℕ) →
  dWalkᶜ S W R d g J (suc i)
    ≡ suc (dCapᶜ S W R d g (lvls S W d J 1))
      + dWalkᶜ S W R d g (lvls S W d J (suc (dCapᶜ S W R d g (lvls S W d J 1)))) i
dWalkᶜ-front S W R d g J zero =
  sym (+-identityʳ (suc (dCapᶜ S W R d g (lvls S W d J 1))))
dWalkᶜ-front S W R d g J (suc i) =
  trans (cong (λ x → x + suc (dCapᶜ S W R d g (lvls S W d J (suc x))))
              (dWalkᶜ-front S W R d g J i))
    (trans (+-assoc (suc A) W′ (suc (dCapᶜ S W R d g (lvls S W d J (suc (suc A + W′))))))
           (cong (λ x → suc A + (W′ + suc (dCapᶜ S W R d g x))) (sym re)))
  where
  A  = dCapᶜ S W R d g (lvls S W d J 1)
  J′ = lvls S W d J (suc A)
  W′ = dWalkᶜ S W R d g J′ i
  re : lvls S W d J′ (suc W′) ≡ lvls S W d J (suc (suc A + W′))
  re = trans (sym (lvls-add S W d J (suc A) (suc W′)))
             (cong (lvls S W d J) (+-suc (suc A) W′))

------------------------------------------------------------------
-- AND IT IS MONOTONE IN EVERY ARGUMENT, THE LEVEL INCLUDED — the same
-- toolkit `dCap-mono` is, plus the two base monotonicities the level
-- reading needs (the old walk never varied S or W inside itself)
------------------------------------------------------------------

sizeStep-mono : ∀ {S S′ s s′} → S ≤ S′ → s ≤ s′ → sizeStep S s ≤ sizeStep S′ s′
sizeStep-mono hS hb = *-mono-≤ hS (s≤s (*-monoʳ-≤ 2 hb))

foldStep-mono : ∀ {S S′ w w′} → 2 ≤ S → S ≤ S′ → w ≤ w′ →
  foldStep S w ≤ foldStep S′ w′
foldStep-mono {zero}        ()
foldStep-mono {suc zero}    (s≤s ())
foldStep-mono {suc (suc n)} {w′ = w′} 2≤S hS hw =
  ≤-trans (^-monoʳ-≤ (suc (suc n)) (s≤s hw)) (^-monoˡ-≤ (suc w′) hS)

iterSize-mono-base : ∀ (k : ℕ) {S S′ s s′} → S ≤ S′ → s ≤ s′ →
  iterSize S k s ≤ iterSize S′ k s′
iterSize-mono-base zero    hS hb = hb
iterSize-mono-base (suc k) hS hb = iterSize-mono-base k hS (sizeStep-mono hS hb)

iterFold-mono-base : ∀ (k : ℕ) {S S′ w w′} → 2 ≤ S → S ≤ S′ → w ≤ w′ →
  iterFold S k w ≤ iterFold S′ k w′
iterFold-mono-base zero    2≤S hS hw = hw
iterFold-mono-base (suc k) 2≤S hS hw =
  iterFold-mono-base k 2≤S hS (foldStep-mono 2≤S hS hw)

sizeAt-mono : ∀ {S S′ J J′} → 1 ≤ S → S ≤ S′ → J ≤ J′ → sizeAt S J ≤ sizeAt S′ J′
sizeAt-mono {S} {S′} {J} 1≤S hS hJ =
  ≤-trans (iterSize-mono-base J hS hS) (iterSize-mono-count S′ S′ (≤-trans 1≤S hS) hJ)

widAt-mono : ∀ {S S′ W W′ J J′} → 2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ →
  widAt S W J ≤ widAt S′ W′ J′
widAt-mono {S} {S′} {W} {W′} {J} 2≤S hS hW hJ =
  ≤-trans (iterFold-mono-base J 2≤S hS hW) (iterFold-mono-count S′ W′ (≤-trans 2≤S hS) hJ)

regAt-mono : ∀ {S S′ R R′ J J′} → S ≤ S′ → R ≤ R′ → J ≤ J′ →
  regAt S R J ≤ regAt S′ R′ J′
regAt-mono hS hR hJ = *-mono-≤ hR (s≤s (*-mono-≤ hJ hS))

fCharge-mono : ∀ {S S′ W W′ J J′} → 2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ →
  fCharge S W J ≤ fCharge S′ W′ J′
fCharge-mono 2≤S hS hW hJ =
  s≤s (*-mono-≤ (s≤s (widAt-mono 2≤S hS hW hJ))
                (s≤s (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) hS hJ)))

fLvl-mono : ∀ {S S′ W W′ J J′} → 2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ →
  fLvl S W J ≤ fLvl S′ W′ J′
fLvl-mono 2≤S hS hW hJ = +-mono-≤ hJ (fCharge-mono 2≤S hS hW hJ)

------------------------------------------------------------------
-- THE NESTING-BUDGETED FRAME LEVEL, and everything the walk needs of
-- it.  The family itself is in Rx.Evaluator (opaque, for the
-- normalisation reason written there); this reads its clauses back
-- through the `-body` equations and proves the three properties every
-- consumer above `fLvlD` is built out of.
--
-- EVERY TRANSFORMER IS INFLATIONARY, which is the whole content of the
-- gate below: a level never goes down, so the old per-frame receipt
-- survives inside the new one as its own first step.
------------------------------------------------------------------

fLvlD-infl  : ∀ (S W d J : ℕ) → J ≤ fLvlD S W d J
sIterD-infl : ∀ (S W d k m J : ℕ) → J ≤ sIterD S W d k m J
sLvlD-infl  : ∀ (S W d k J : ℕ) → J ≤ sLvlD S W d k J
opIterD-infl : ∀ (S W d k m J : ℕ) → J ≤ opIterD S W d k m J
fIterD-infl : ∀ (S W d k m J : ℕ) → J ≤ fIterD S W d k m J

fLvlD-infl S W zero    J =
  ≤-trans (≤-trans (m≤m+n J (fCharge S W J))
                   (m≤m+n (fLvl S W J) (suc (widAt S W J))))
          (≤-reflexive (sym (fLvlD-0 S W J)))
fLvlD-infl S W (suc d) J =
  ≤-trans (≤-trans (m≤m+n J (fCharge S W J))
                   (sIterD-infl S W d (suc (sizeAt S (suc J))) (suc (widAt S W J))
                                (fLvl S W J)))
          (≤-reflexive (sym (fLvlD-suc S W d J)))

sIterD-infl S W d k zero    J = ≤-reflexive (sym (sIterD-0 S W d k J))
sIterD-infl S W d k (suc m) J =
  ≤-trans (≤-trans (≤-trans (n≤1+n J) (sLvlD-infl S W d k (suc J)))
                   (sIterD-infl S W d k m (sLvlD S W d k (suc J))))
          (≤-reflexive (sym (sIterD-suc S W d k m J)))

sLvlD-infl S W d zero    J = ≤-reflexive (sym (sLvlD-0 S W d J))
sLvlD-infl S W d (suc k) J =
  ≤-trans (opIterD-infl S W d k (suc (sizeAt S J)) J)
          (≤-reflexive (sym (sLvlD-suc S W d k J)))

opIterD-infl S W d k zero    J = ≤-reflexive (sym (opIterD-0 S W d k J))
opIterD-infl S W d k (suc m) J =
  let J₀ = suc (J + suc (sizeAt S J) * suc (sizeAt S J))
      J₂ = opIterD S W d k m (sLvlD S W d k J₀)
  in ≤-trans (≤-trans (≤-trans (≤-trans (n≤1+n J)
                                 (s≤s (m≤m+n J (suc (sizeAt S J) * suc (sizeAt S J)))))
                               (≤-trans (sLvlD-infl S W d k J₀)
                                        (opIterD-infl S W d k m (sLvlD S W d k J₀))))
                      (fIterD-infl S W d k (suc (widAt S W J₂)) J₂))
             (≤-reflexive (sym (opIterD-suc S W d k m J)))

fIterD-infl S W d k zero    J = ≤-reflexive (sym (fIterD-0 S W d k J))
fIterD-infl S W d k (suc m) J =
  ≤-trans (≤-trans (fLvlD-infl S W d J)
                   (fIterD-infl S W d k m (fLvlD S W d J)))
          (≤-reflexive (sym (fIterD-suc S W d k m J)))

-- the d = 0 clause is UNDER the general one: `J + m` is what `sIterD`
-- does when its budget is empty, and its budget is never emptier than
-- that.  This is what makes the fuel-exhausted clause a BOUND rather
-- than a hole — the refresh dominates the inherited family at every
-- budget including the empty one
sIterD-zero≤ : ∀ (S W d k m J : ℕ) → J + m ≤ sIterD S W d k m J
sIterD-zero≤ S W d k zero    J =
  ≤-trans (≤-reflexive (+-identityʳ J)) (≤-reflexive (sym (sIterD-0 S W d k J)))
sIterD-zero≤ S W d k (suc m) J =
  ≤-trans (≤-trans (≤-reflexive (+-suc J m))
                   (≤-trans (+-monoˡ-≤ m (sLvlD-infl S W d k (suc J)))
                            (sIterD-zero≤ S W d k m (sLvlD S W d k (suc J)))))
          (≤-reflexive (sym (sIterD-suc S W d k m J)))

------------------------------------------------------------------
-- AND MONOTONE IN ALL FIVE ARGUMENTS, THE DEPTH FUEL INCLUDED.  This
-- is what makes the rewiring `fLvl := fLvlD` cheap: `iterL-mono`,
-- `dLvl-mono` and `lvls-mono` are built from the per-frame
-- monotonicity and nothing else, so the whole ladder above the frame
-- moves up with this one lemma and no re-derivation.
------------------------------------------------------------------

fLvlD-mono : ∀ {S S′ W W′ J J′} (d d′ : ℕ) → 2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ →
  d ≤ d′ → fLvlD S W d J ≤ fLvlD S′ W′ d′ J′
sIterD-mono : ∀ {S S′ W W′ J J′} (m m′ d d′ k k′ : ℕ) →
  2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ → d ≤ d′ → k ≤ k′ → m ≤ m′ →
  sIterD S W d k m J ≤ sIterD S′ W′ d′ k′ m′ J′
sLvlD-mono : ∀ {S S′ W W′ J J′} (d d′ k k′ : ℕ) →
  2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ → d ≤ d′ → k ≤ k′ →
  sLvlD S W d k J ≤ sLvlD S′ W′ d′ k′ J′
opIterD-mono : ∀ {S S′ W W′ J J′} (m m′ d d′ k k′ : ℕ) →
  2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ → d ≤ d′ → k ≤ k′ → m ≤ m′ →
  opIterD S W d k m J ≤ opIterD S′ W′ d′ k′ m′ J′
fIterD-mono : ∀ {S S′ W W′ J J′} (m m′ d d′ k k′ : ℕ) →
  2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ → d ≤ d′ → k ≤ k′ → m ≤ m′ →
  fIterD S W d k m J ≤ fIterD S′ W′ d′ k′ m′ J′

fLvlD-mono {S} {S′} {W} {W′} {J} {J′} zero zero 2≤S hS hW hJ hd =
  ≤-trans (≤-trans (≤-reflexive (fLvlD-0 S W J))
                   (+-mono-≤ (fLvl-mono 2≤S hS hW hJ)
                             (s≤s (widAt-mono 2≤S hS hW hJ))))
          (≤-reflexive (sym (fLvlD-0 S′ W′ J′)))
fLvlD-mono {S} {S′} {W} {W′} {J} {J′} zero (suc d′) 2≤S hS hW hJ hd =
  ≤-trans (≤-trans (≤-trans (≤-reflexive (fLvlD-0 S W J))
                            (+-mono-≤ (fLvl-mono 2≤S hS hW hJ)
                                      (s≤s (widAt-mono 2≤S hS hW hJ))))
                   (sIterD-zero≤ S′ W′ d′ (suc (sizeAt S′ (suc J′)))
                                 (suc (widAt S′ W′ J′)) (fLvl S′ W′ J′)))
          (≤-reflexive (sym (fLvlD-suc S′ W′ d′ J′)))
fLvlD-mono (suc d) zero 2≤S hS hW hJ ()
fLvlD-mono {S} {S′} {W} {W′} {J} {J′} (suc d) (suc d′) 2≤S hS hW hJ (s≤s hd) =
  ≤-trans (≤-trans (≤-reflexive (fLvlD-suc S W d J))
                   (sIterD-mono (suc (widAt S W J)) (suc (widAt S′ W′ J′)) d d′
                      (suc (sizeAt S (suc J))) (suc (sizeAt S′ (suc J′))) 2≤S hS hW
                      (fLvl-mono 2≤S hS hW hJ) hd
                      (s≤s (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) hS (s≤s hJ)))
                      (s≤s (widAt-mono 2≤S hS hW hJ))))
          (≤-reflexive (sym (fLvlD-suc S′ W′ d′ J′)))

sIterD-mono {S} {S′} {W} {W′} {J} {J′} zero m′ d d′ k k′ 2≤S hS hW hJ hd hk hm =
  ≤-trans (≤-trans (≤-reflexive (sIterD-0 S W d k J)) hJ)
          (sIterD-infl S′ W′ d′ k′ m′ J′)
sIterD-mono (suc m) zero    d d′ k k′ 2≤S hS hW hJ hd hk ()
sIterD-mono {S} {S′} {W} {W′} {J} {J′} (suc m) (suc m′) d d′ k k′
            2≤S hS hW hJ hd hk (s≤s hm) =
  ≤-trans (≤-trans (≤-reflexive (sIterD-suc S W d k m J))
                   (sIterD-mono m m′ d d′ k k′ 2≤S hS hW
                      (sLvlD-mono d d′ k k′ 2≤S hS hW (s≤s hJ) hd hk) hd hk hm))
          (≤-reflexive (sym (sIterD-suc S′ W′ d′ k′ m′ J′)))

sLvlD-mono {S} {S′} {W} {W′} {J} {J′} d d′ zero k′ 2≤S hS hW hJ hd hk =
  ≤-trans (≤-trans (≤-reflexive (sLvlD-0 S W d J)) hJ)
          (sLvlD-infl S′ W′ d′ k′ J′)
sLvlD-mono d d′ (suc k) zero 2≤S hS hW hJ hd ()
sLvlD-mono {S} {S′} {W} {W′} {J} {J′} d d′ (suc k) (suc k′)
           2≤S hS hW hJ hd (s≤s hk) =
  ≤-trans (≤-trans (≤-reflexive (sLvlD-suc S W d k J))
                   (opIterD-mono (suc (sizeAt S J)) (suc (sizeAt S′ J′)) d d′ k k′
                      2≤S hS hW hJ hd hk
                      (s≤s (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) hS hJ))))
          (≤-reflexive (sym (sLvlD-suc S′ W′ d′ k′ J′)))

opIterD-mono {S} {S′} {W} {W′} {J} {J′} zero m′ d d′ k k′ 2≤S hS hW hJ hd hk hm =
  ≤-trans (≤-trans (≤-reflexive (opIterD-0 S W d k J)) hJ)
          (opIterD-infl S′ W′ d′ k′ m′ J′)
opIterD-mono (suc m) zero    d d′ k k′ 2≤S hS hW hJ hd hk ()
opIterD-mono {S} {S′} {W} {W′} {J} {J′} (suc m) (suc m′) d d′ k k′
             2≤S hS hW hJ hd hk (s≤s hm) =
  let sz≤ = sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) hS hJ
      J₀≤ = s≤s (+-mono-≤ hJ (*-mono-≤ (s≤s sz≤) (s≤s sz≤)))
      X   = opIterD S W d k m
              (sLvlD S W d k (suc (J + suc (sizeAt S J) * suc (sizeAt S J))))
      X′  = opIterD S′ W′ d′ k′ m′
              (sLvlD S′ W′ d′ k′ (suc (J′ + suc (sizeAt S′ J′) * suc (sizeAt S′ J′))))
      inner : X ≤ X′
      inner = opIterD-mono m m′ d d′ k k′ 2≤S hS hW
                (sLvlD-mono d d′ k k′ 2≤S hS hW J₀≤ hd hk) hd hk hm
  in ≤-trans (≤-trans (≤-reflexive (opIterD-suc S W d k m J))
                      (fIterD-mono (suc (widAt S W X)) (suc (widAt S′ W′ X′)) d d′ k k′
                         2≤S hS hW inner hd hk
                         (s≤s (widAt-mono 2≤S hS hW inner))))
             (≤-reflexive (sym (opIterD-suc S′ W′ d′ k′ m′ J′)))

fIterD-mono {S} {S′} {W} {W′} {J} {J′} zero m′ d d′ k k′ 2≤S hS hW hJ hd hk hm =
  ≤-trans (≤-trans (≤-reflexive (fIterD-0 S W d k J)) hJ)
          (fIterD-infl S′ W′ d′ k′ m′ J′)
fIterD-mono (suc m) zero    d d′ k k′ 2≤S hS hW hJ hd hk ()
fIterD-mono {S} {S′} {W} {W′} {J} {J′} (suc m) (suc m′) d d′ k k′
            2≤S hS hW hJ hd hk (s≤s hm) =
  ≤-trans (≤-trans (≤-reflexive (fIterD-suc S W d k m J))
                   (fIterD-mono m m′ d d′ k k′ 2≤S hS hW
                      (fLvlD-mono d d′ 2≤S hS hW hJ hd) hd hk hm))
          (≤-reflexive (sym (fIterD-suc S′ W′ d′ k′ m′ J′)))

-- THE GATE: the new per-frame level DOMINATES the old receipt
-- pointwise, AT EVERY DEPTH FUEL — the old receipt is literally the
-- seed of the new iteration, so this needs no arithmetic at all.  It is
-- what keeps every consumer above the frame (`iterL`, `dLvl`, `lvls`,
-- `sizeCount`, the pooled count, and the gate against the product the
-- count replaced) true with no row re-measured
fLvl≤fLvlD : ∀ (S W d J : ℕ) → fLvl S W J ≤ fLvlD S W d J
fLvl≤fLvlD S W zero    J =
  ≤-trans (m≤m+n (fLvl S W J) (suc (widAt S W J)))
          (≤-reflexive (sym (fLvlD-0 S W J)))
fLvl≤fLvlD S W (suc d) J =
  ≤-trans (sIterD-infl S W d (suc (sizeAt S (suc J))) (suc (widAt S W J)) (fLvl S W J))
          (≤-reflexive (sym (fLvlD-suc S W d J)))

iterL-infl : ∀ (S W d k J : ℕ) → J ≤ iterL S W d k J
iterL-infl S W d zero    J = ≤-refl
iterL-infl S W d (suc k) J =
  ≤-trans (fLvlD-infl S W d J) (iterL-infl S W d k (fLvlD S W d J))

-- MONOTONE AT A FIXED DEPTH FUEL, and the fuel is implicit for exactly
-- that reason: nothing on this ladder ever varies it — it is threaded
-- from the one instantiation at the top (`capsAt`, `poolBody`) down to
-- the frame unchanged, so every consumer compares two levels at the
-- SAME d and no call site mentions it
iterL-mono : ∀ {S S′ W W′ J J′ d} (k k′ : ℕ) →
  2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ →
  k ≤ k′ → iterL S W d k J ≤ iterL S′ W′ d k′ J′
iterL-mono {S′ = S′} {W′ = W′} {J′ = J′} {d = d} zero k′ 2≤S hS hW hJ hk =
  ≤-trans hJ (iterL-infl S′ W′ d k′ J′)
iterL-mono (suc k) zero     2≤S hS hW hJ ()
iterL-mono (suc k) (suc k′) 2≤S hS hW hJ (s≤s hk) =
  iterL-mono k k′ 2≤S hS hW (fLvlD-mono _ _ 2≤S hS hW hJ ≤-refl) hk

dLvl-infl : ∀ (S W d J : ℕ) → J ≤ dLvl S W d J
dLvl-infl S W d J = iterL-infl S W d (suc (sizeAt S J)) J

dLvl-mono : ∀ {S S′ W W′ J J′ d} → 2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ →
  dLvl S W d J ≤ dLvl S′ W′ d J′
dLvl-mono {S} {S′} {J = J} {J′ = J′} 2≤S hS hW hJ =
  iterL-mono (suc (sizeAt S J)) (suc (sizeAt S′ J′)) 2≤S hS hW hJ
             (s≤s (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) hS hJ))

lvls-infl : ∀ (S W d J n : ℕ) → J ≤ lvls S W d J n
lvls-infl S W d J zero    = ≤-refl
lvls-infl S W d J (suc n) =
  ≤-trans (lvls-infl S W d J n) (dLvl-infl S W d (lvls S W d J n))

lvls-mono : ∀ {S S′ W W′ J J′ d} (n n′ : ℕ) → 2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ →
  n ≤ n′ → lvls S W d J n ≤ lvls S′ W′ d J′ n′
lvls-mono {S′ = S′} {W′ = W′} {J′ = J′} {d = d} zero n′ 2≤S hS hW hJ hn =
  ≤-trans hJ (lvls-infl S′ W′ d J′ n′)
lvls-mono (suc n) zero     2≤S hS hW hJ ()
lvls-mono (suc n) (suc n′) 2≤S hS hW hJ (s≤s hn) =
  dLvl-mono 2≤S hS hW (lvls-mono n n′ 2≤S hS hW hJ hn)

-- AND ONE DELIVERY ALWAYS COSTS TWO: a chain has at least one frame,
-- a frame's receipt `fCharge` is a `suc` of a product of two `suc`s,
-- and `dLvl` iterates that at least once.  This is what `sizeCount`'s
-- own positivity is read off, now that the count is a LEVEL rather than
-- a product with a visible factor to read it off of
2≤dLvl : ∀ (S W d J : ℕ) → 2 ≤ dLvl S W d J
2≤dLvl S W d J =
  ≤-trans (≤-trans (≤-trans (s≤s (≤-trans (s≤s z≤n)
                                          (m≤m*n (suc (widAt S W J)) (suc (sizeAt S J)))))
                            (m≤n+m (fCharge S W J) J))
                   (fLvl≤fLvlD S W d J))
          (iterL-infl S W d (sizeAt S J) (fLvlD S W d J))

dCapᶜ-mono : ∀ {S S′ W W′ R R′ J J′ d} (g g′ : ℕ) →
  2 ≤ S → S ≤ S′ → W ≤ W′ → R ≤ R′ → g ≤ g′ → J ≤ J′ →
  dCapᶜ S W R d g J ≤ dCapᶜ S′ W′ R′ d g′ J′
dWalkᶜ-mono : ∀ {S S′ W W′ R R′ J J′ d} (g g′ i i′ : ℕ) →
  2 ≤ S → S ≤ S′ → W ≤ W′ → R ≤ R′ → g ≤ g′ → J ≤ J′ → i ≤ i′ →
  dWalkᶜ S W R d g J i ≤ dWalkᶜ S′ W′ R′ d g′ J′ i′

dCapᶜ-mono zero    g′       2≤S hS hW hR hg       hJ = z≤n
dCapᶜ-mono (suc g) zero     2≤S hS hW hR ()       hJ
dCapᶜ-mono (suc g) (suc g′) 2≤S hS hW hR (s≤s hg) hJ =
  dWalkᶜ-mono g g′ _ _ 2≤S hS hW hR hg hJ (regAt-mono hS hR hJ)

dWalkᶜ-mono g g′ zero    i′       2≤S hS hW hR hg hJ hi       = z≤n
dWalkᶜ-mono g g′ (suc i) zero     2≤S hS hW hR hg hJ ()
dWalkᶜ-mono g g′ (suc i) (suc i′) 2≤S hS hW hR hg hJ (s≤s hi) =
  +-mono-≤ ih (s≤s (dCapᶜ-mono g g′ 2≤S hS hW hR hg
                      (lvls-mono (suc _) (suc _) 2≤S hS hW hJ (s≤s ih))))
  where
  ih = dWalkᶜ-mono g g′ i i′ 2≤S hS hW hR hg hJ hi

-- SO THE COUNT IS POSITIVE, once there is one registration to walk:
-- one delivery is one `dLvl`, and `lvls S W d 0 1` IS `dLvl S W d 0`
2≤sizeCount : ∀ (c : Caps) (d : ℕ) → 2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  2 ≤ sizeCount c d
2≤sizeCount c d 2≤S 1≤R =
  ≤-trans (≤-trans (2≤dLvl (Caps.cSize c) (Caps.cWid c) d 0)
                   (lvls-mono 1 (cDel c d) 2≤S ≤-refl ≤-refl ≤-refl 1≤D))
          (≤-reflexive (sym (sizeCount-body c d)))
  where
  1≤D : 1 ≤ cDel c d
  1≤D = ≤-trans (1≤dCapᶜ (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d
                         (Caps.cSize c) 0 1≤R)
                (≤-reflexive (sym (cDel-body c d)))

-- REG: linear, monotone in j always
frameStep-reg-mono : ∀ (c : Caps) {j j′ : ℕ} → j ≤ j′ →
  Caps.cReg (frameStep j c) ≤ Caps.cReg (frameStep j′ c)
frameStep-reg-mono (caps s w r) le =
  *-monoʳ-≤ r (s≤s (*-monoˡ-≤ s le))

frameStep-mono-j : ∀ (c : Caps) → 2 ≤ Caps.cSize c → ∀ {j j′ : ℕ} → j ≤ j′ →
  frameStep j c ⊑ᶜ frameStep j′ c
frameStep-mono-j c hS le =
    iterSize-mono-count (Caps.cSize c) (Caps.cSize c) (≤-trans (s≤s z≤n) hS) le
  , iterFold-mono-count (Caps.cSize c) (Caps.cWid c) hS le
  , frameStep-reg-mono c le

-- and the recurrence's own step, so capsAt (suc id) IS the full endpoint
capsAt-suc-full : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  capsAt e sl (suc id)
    ≡ frameStep (sizeCount (capsAt e sl id) (capsH e sl id)) (capsAt e sl id)
capsAt-suc-full e sl id = refl

------------------------------------------------------------------
-- 2 ≤ cSize AT EVERY LEVEL — frameStep-mono-j's side condition, which
-- the recurrence supplies rather than assumes.  The base is `2 + …` and
-- iterSize only grows it (sizeStep is inflationary for S ≥ 1), so the
-- property is inherited by every frameBlowup
------------------------------------------------------------------

2≤frameBlowup-size : ∀ (c : Caps) (d : ℕ) → 2 ≤ Caps.cSize c →
  2 ≤ Caps.cSize (frameBlowup c d)
2≤frameBlowup-size c d h =
  ≤-trans h (iterSize-infl (Caps.cSize c) (≤-trans (s≤s z≤n) h)
               (sizeCount c d) (Caps.cSize c))

2≤capsAt-size : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  2 ≤ Caps.cSize (capsAt e sl id)
2≤capsAt-size {n = n} e sl zero =
  2≤frameBlowup-size (caps (2 + sizeᵉ e + slotsSize sl + slotsClos sl)
                           (suc (entryCeil n sl e))
                           (suc (sizeᵉ e + slotsSize sl)))
    (capsBase e sl)
    (s≤s (s≤s z≤n))
2≤capsAt-size e sl (suc id) =
  2≤frameBlowup-size (capsAt e sl id) (capsH e sl id) (2≤capsAt-size e sl id)

-- THE RECURRENCE ONLY EVER WIDENS, which is the one fact every face
-- needs to read a quantity taken at one instant against the next
-- instant's cap.  It is the j = 0 end of `frameStep-mono-j` transported
-- along the two definitional equations that pin the endpoints, and the
-- count is pinned by hand because `iterSize`/`iterFold` match on it, so
-- unification cannot invert `frameStep _ c` to recover it from the ⊑ᶜ
-- endpoints.  Sealed for the reason the whole caps axis is: no consumer
-- ever unfolds a ⊑ᶜ proof, and an unfoldable body hands the conversion
-- checker the entire mono tower underneath it.
abstract
  capsAt-⊑-suc : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) → capsAt e sl id ⊑ᶜ capsAt e sl (suc id)
  capsAt-⊑-suc e sl id =
    subst₂ _⊑ᶜ_ (frameStep-0 (capsAt e sl id))
                (sym (capsAt-suc-full e sl id))
                (frameStep-mono-j (capsAt e sl id) (2≤capsAt-size e sl id)
                   (z≤n {n = sizeCount (capsAt e sl id) (capsH e sl id)}))

-- 1 ≤ cReg AT EVERY LEVEL, the registering companions' side condition,
-- and the recurrence proves it the same way: the base's cReg is a `suc`,
-- and frameBlowup's cReg is `cReg c * suc (…)`, which never drops below
-- cReg c
1≤frameBlowup-reg : ∀ (c : Caps) (d : ℕ) → 1 ≤ Caps.cReg c →
  1 ≤ Caps.cReg (frameBlowup c d)
1≤frameBlowup-reg c d h = ≤-trans h (m≤m*n (Caps.cReg c) _)

1≤capsAt-reg : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  1 ≤ Caps.cReg (capsAt e sl id)
1≤capsAt-reg {n = n} e sl zero =
  1≤frameBlowup-reg (caps (2 + sizeᵉ e + slotsSize sl + slotsClos sl)
                          (suc (entryCeil n sl e))
                          (suc (sizeᵉ e + slotsSize sl)))
    (capsBase e sl)
    (s≤s z≤n)
1≤capsAt-reg e sl (suc id) =
  1≤frameBlowup-reg (capsAt e sl id) (capsH e sl id) (1≤capsAt-reg e sl id)

------------------------------------------------------------------
-- AND THE SLOT SIDE CONDITION AT EVERY LEVEL, supplied by the
-- recurrence rather than assumed.  This is what ties `c` to `sl`: the
-- base cSize CONTAINS slotsSize as a summand, iterSize only grows it,
-- so every slot's payloads sit under every level's cSize.
------------------------------------------------------------------

cSize≤frameBlowup : ∀ (c : Caps) (d : ℕ) → 1 ≤ Caps.cSize c →
  Caps.cSize c ≤ Caps.cSize (frameBlowup c d)
cSize≤frameBlowup c d h =
  iterSize-infl (Caps.cSize c) h (sizeCount c d) (Caps.cSize c)

capsAt-base-size : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  2 + sizeᵉ e + slotsSize sl ≤ Caps.cSize (capsAt e sl id)
capsAt-base-size {n = n} e sl zero =
  ≤-trans (m≤m+n (2 + sizeᵉ e + slotsSize sl) (slotsClos sl))
    (cSize≤frameBlowup (caps (2 + sizeᵉ e + slotsSize sl + slotsClos sl)
                            (suc (entryCeil n sl e))
                            (suc (sizeᵉ e + slotsSize sl)))
      (capsBase e sl)
      (s≤s z≤n))
capsAt-base-size e sl (suc id) =
  ≤-trans (capsAt-base-size e sl id)
          (cSize≤frameBlowup (capsAt e sl id) (capsH e sl id)
             (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)))

-- AND THE TELESCOPE'S STAGED READING SITS UNDER THE SAME CAP.  This is
-- the summand the base cap grew for: a slot's flat size is what the
-- width face needs, and the closure face needs the slot read THROUGH
-- the telescope, which is a different and larger number.  Carrying it
-- in the base is what lets the slot pricing predicate hold it, and the
-- pricing predicate is what every walk statement already threads.
-- REFUTED: `Refuted.Nest-Clos-Stratified`, which is why the reading
--   cannot instead be recovered from the flat size at any fixed number
--   of frame levels.
capsAt-base-clos : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  slotsClos sl ≤ Caps.cSize (capsAt e sl id)
capsAt-base-clos {n = n} e sl zero =
  ≤-trans (m≤n+m (slotsClos sl) (2 + sizeᵉ e + slotsSize sl))
    (cSize≤frameBlowup (caps (2 + sizeᵉ e + slotsSize sl + slotsClos sl)
                            (suc (entryCeil n sl e))
                            (suc (sizeᵉ e + slotsSize sl)))
      (capsBase e sl)
      (s≤s z≤n))
capsAt-base-clos e sl (suc id) =
  ≤-trans (capsAt-base-clos e sl id)
          (cSize≤frameBlowup (capsAt e sl id) (capsH e sl id)
             (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)))

-- THE TOP-LEVEL SUPPLY, the counterpart of 2≤capsAt-size and
-- 1≤capsAt-reg.  It is what the cascade face hands the tree once
-- cascadeGo-level carries the side condition too; the companions below
-- thread it from there down to subscribeE-input-caps unchanged
-- THE WIDTH AXIS OF THE SAME SUPPLY, and the reason capsAt's base pays
-- for the WHOLE ENTRY CEILING rather than for the program's own width:
-- the static width measures TOWER in the syntax, and no per-frame
-- receipt buys a tower, so every SUBTERM's five measures — the
-- program's and every shared slot def's alike, a connect subscribes a
-- def whole — are paid for once, here.  The ⊔-collect costs no tower
-- stories over the old three-term base (same two-per-node rate,
-- Mult-Width-Probe §3), so `budgetAt` does not move.  iterFold only
-- grows a width (for S ≥ 2), so every level inherits the base's
cWid≤frameBlowup : ∀ (c : Caps) (d : ℕ) → 2 ≤ Caps.cSize c →
  Caps.cWid c ≤ Caps.cWid (frameBlowup c d)
cWid≤frameBlowup c d h =
  iterFold-infl (Caps.cSize c) h (sizeCount c d) (Caps.cWid c)

capsAt-base-wid : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  suc (entryCeil n sl e) ≤ Caps.cWid (capsAt e sl id)
capsAt-base-wid {n = n} e sl zero =
  cWid≤frameBlowup (caps (2 + sizeᵉ e + slotsSize sl + slotsClos sl)
                         (suc (entryCeil n sl e))
                         (suc (sizeᵉ e + slotsSize sl)))
    (capsBase e sl)
    (s≤s (s≤s z≤n))
capsAt-base-wid e sl (suc id) =
  ≤-trans (capsAt-base-wid e sl id)
          (cWid≤frameBlowup (capsAt e sl id) (capsH e sl id)
             (2≤capsAt-size e sl id))

-- AND THE ARRIVALS' OWN WIDTH KEY FALLS OUT OF IT, at every instant
-- rather than only the first.  This is the one premise of the proven
-- subscribe face that reads the SOURCE instead of the state, so it is
-- the one a door into that face cannot get from a slots bundle -- and
-- it is free here, because the instant's cap is built over a ceiling
-- that already dominates every width the term can deliver.  It lives at
-- this level so both faces reach it; the bridge is not the only caller
-- any more.
dWᵉ≤capsAt-wid : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  dWᵉ n sl e ≤ Caps.cWid (capsAt e sl id)
dWᵉ≤capsAt-wid {n = n} e sl id =
  ≤-trans (dW≤ceil n sl e)
  (≤-trans (m≤m⊔n (ceilᵉ n sl e) _)
  (≤-trans (n≤1+n _)
           (capsAt-base-wid e sl id)))

------------------------------------------------------------------
-- B2 : THE REGISTRATION COUNT NEVER OUTRUNS THE SIZE CAP.
-- (Moved here from Caps-Bridge.agda so Walk-Level can import it
-- without creating a cycle through Burst-Walk.)
------------------------------------------------------------------

sizeStep-eqn : ∀ (S X : ℕ) → sizeStep S X ≡ S + (S * X + S * X)
sizeStep-eqn S X =
  begin
    S * suc (2 * X)
  ≡⟨ *-distribˡ-+ S 1 (2 * X) ⟩
    S * 1 + S * (2 * X)
  ≡⟨ cong (_+ S * (2 * X)) (*-identityʳ S) ⟩
    S + S * (2 * X)
  ≡⟨ cong (λ y → S + S * y) (2X≡X+X X) ⟩
    S + S * (X + X)
  ≡⟨ cong (S +_) (*-distribˡ-+ S X X) ⟩
    S + (S * X + S * X)
  ∎
  where open ≡-Reasoning

frameStep-reg≤size : ∀ (c : Caps) (j : ℕ) → 1 ≤ Caps.cSize c →
  Caps.cReg c ≤ Caps.cSize c →
  Caps.cReg (frameStep j c) ≤ Caps.cSize (frameStep j c)
frameStep-reg≤size c zero hS h =
  subst (λ x → Caps.cReg x ≤ Caps.cSize x) (sym (frameStep-0 c)) h
frameStep-reg≤size c (suc j) hS h = final
  where
  S  = Caps.cSize c
  X  = Caps.cSize (frameStep j c)
  R  = Caps.cReg (frameStep j c)
  Rc = Caps.cReg c
  IH : R ≤ X
  IH = frameStep-reg≤size c j hS h
  S≤X : S ≤ X
  S≤X = iterSize-infl S hS j S
  Rc*S≤S*X : Rc * S ≤ S * X
  Rc*S≤S*X = ≤-trans (*-mono-≤ h ≤-refl) (*-monoʳ-≤ S S≤X)
  step1 : R + Rc * S ≤ X + S * X
  step1 = +-mono-≤ IH Rc*S≤S*X
  X≤S*X : X ≤ S * X
  X≤S*X =
    ≤-trans (≤-reflexive (sym (*-identityʳ X)))
            (≤-trans (*-monoʳ-≤ X hS) (≤-reflexive (*-comm X S)))
  step2 : X + S * X ≤ S * X + S * X
  step2 = +-mono-≤ X≤S*X ≤-refl
  step3 : S * X + S * X ≤ S + (S * X + S * X)
  step3 = m≤n+m (S * X + S * X) S
  chain : R + Rc * S ≤ S + (S * X + S * X)
  chain = ≤-trans step1 (≤-trans step2 step3)
  result : R + Rc * S ≤ sizeStep S X
  result = subst (λ y → R + Rc * S ≤ y) (sym (sizeStep-eqn S X)) chain
  final : Caps.cReg (frameStep (suc j) c) ≤ Caps.cSize (frameStep (suc j) c)
  final = subst₂ _≤_ (frameStep-reg-suc c j) (sym (frameStep-size-suc c j)) result

B2-cReg≤cSize : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) → Caps.cReg (capsAt e sl id) ≤ Caps.cSize (capsAt e sl id)
B2-cReg≤cSize {n = n} e sl zero =
  frameStep-reg≤size c₀ (sizeCount c₀ (capsBase e sl)) 1≤S₀ hReg₀
  where
  c₀ = caps (2 + sizeᵉ e + slotsSize sl + slotsClos sl) (suc (entryCeil n sl e))
            (suc (sizeᵉ e + slotsSize sl))
  1≤S₀ : 1 ≤ Caps.cSize c₀
  1≤S₀ = ≤-trans (s≤s z≤n) (s≤s (s≤s z≤n))
  hReg₀ : Caps.cReg c₀ ≤ Caps.cSize c₀
  hReg₀ = s≤s (≤-trans (m≤m+n (sizeᵉ e + slotsSize sl) (slotsClos sl))
                       (n≤1+n (sizeᵉ e + slotsSize sl + slotsClos sl)))
B2-cReg≤cSize e sl (suc id) =
  frameStep-reg≤size (capsAt e sl id) (sizeCount (capsAt e sl id) (capsH e sl id))
                     (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id))
                     (B2-cReg≤cSize e sl id)

------------------------------------------------------------------
-- THE RECURRENCE UNDER A TOWER — the last supply lemma, and the one
-- the ROOT'S FUEL needs.  capsAt is Ackermann-flavoured in `id`, but
-- only barely: every level sits under a tower of 2s whose HEIGHT is
-- LINEAR in the instant, slope four, and the whole seed inequality is
-- then a height comparison against budgetAt's own (7+sz)(id+2).
--
-- THE LEVEL-COST ACCOUNTING, per instant (one frameBlowup), against a
-- level T = towerℕ m with cSize, cReg ≤ T and m ≥ 3 (so T ≥ 16):
--
--   THE COUNT      J = D̂ · cSize = 2^(2^cReg) · cSize ≤ 2^(2^R + S)
--                    ≤ 2^(2^T) = towerℕ (2+m)              TWO stories
--                  (the delivery bound IS the two stories; the cSize
--                   factor rides beside it in the exponent, which is
--                   what the STRICT registry hypothesis buys)
--   THE ITERATION  iterSize cSize J cSize ≤ (3T)^J · T ≤ 2^(T·(J+1))
--                  and T·(J+1) ≤ (2T)·J ≤ towerℕ (3+m)     TWO stories
--                  (one for the product T·J landing above the count,
--                   one for the outer exponential)
--   THE REGISTRY   cReg · suc (J · cSize) ≤ (2T) · towerℕ (3+m)
--                                        ≤ towerℕ (4+m)    rides along
--
-- so FOUR, and that is the slope.  It is a fixed constant — no
-- dependence on the program, the slot telescope, or the instant — which
-- is exactly what a linear-slope tower needs to dominate; had the count
-- itself needed a story per fold there would be no such bound and
-- budgetAt's slope would be the design session's problem, not this
-- module's.
------------------------------------------------------------------

-- one iteration is available once the count is nonzero
iterSize-step≤ : ∀ (S s j : ℕ) → 1 ≤ S → 1 ≤ j →
  sizeStep S s ≤ iterSize S j s
iterSize-step≤ S s (suc j) hS _ = iterSize-infl S hS j (sizeStep S s)

3≤capsAt-size : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  3 ≤ Caps.cSize (capsAt e sl id)
3≤capsAt-size e sl id =
  ≤-trans (≤-trans (+-monoʳ-≤ 2 (sizeᵉ-pos e))
                   (m≤m+n (2 + sizeᵉ e) (slotsSize sl)))
          (capsAt-base-size e sl id)

21≤frameBlowup-size : ∀ (c : Caps) (d : ℕ) → 1 ≤ Caps.cReg c → 3 ≤ Caps.cSize c →
  21 ≤ Caps.cSize (frameBlowup c d)
21≤frameBlowup-size c d 1≤R 3≤S =
  ≤-trans (*-mono-≤ 3≤S 7≤suc2S) (iterSize-step≤ S S J 1≤S 1≤J)
  where
  S = Caps.cSize c
  J = sizeCount c d
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) 3≤S
  -- the second factor is read at THREE rather than at one, which is
  -- where the whole raise comes from: one `sizeStep` at the minimum cap
  -- is already three sevens, and nothing about the recurrence changes.
  7≤suc2S : 7 ≤ suc (2 * S)
  7≤suc2S = s≤s (*-monoʳ-≤ 2 3≤S)
  1≤J : 1 ≤ J
  1≤J = ≤-trans (s≤s z≤n)
                (2≤sizeCount c d (≤-trans (s≤s (s≤s z≤n)) 3≤S) 1≤R)

-- AND THE FLOOR IS UNIFORM IN THE INSTANT, base included, because the
-- base cap is a `frameBlowup` too -- of a record whose size already
-- reads the program and whose registry is a successor.  Twenty-one is
-- where the nesting side's CUBE overtakes its exponential, which is
-- what a cascade's level range costs once the range is read as a width
-- times a cap rather than as one chain's frames.
21≤capsAt-size : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  21 ≤ Caps.cSize (capsAt e sl id)
21≤capsAt-size {n = n} e sl zero =
  21≤frameBlowup-size
    (caps (2 + sizeᵉ e + slotsSize sl + slotsClos sl) (suc (entryCeil n sl e))
          (suc (sizeᵉ e + slotsSize sl)))
    (capsBase e sl)
    (s≤s z≤n)
    (≤-trans (≤-trans (+-monoʳ-≤ 2 (sizeᵉ-pos e)) (m≤m+n (2 + sizeᵉ e) (slotsSize sl)))
             (m≤m+n (2 + sizeᵉ e + slotsSize sl) (slotsClos sl)))
21≤capsAt-size e sl (suc id) =
  21≤frameBlowup-size (capsAt e sl id) (capsH e sl id)
    (1≤capsAt-reg e sl id) (3≤capsAt-size e sl id)

8≤capsAt-size : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  8 ≤ Caps.cSize (capsAt e sl id)
8≤capsAt-size e sl id =
  ≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
          (21≤capsAt-size e sl id)

6≤capsAt-size : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  6 ≤ Caps.cSize (capsAt e sl (suc id))
6≤capsAt-size e sl id =
  ≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
          (8≤capsAt-size e sl (suc id))

------------------------------------------------------------------
-- THE TOWER BOUND ON THE RECURRENCE.  Every level of capsAt sits under
-- a tower of 2s whose HEIGHT is linear in the instant — slope FOUR,
-- which is what one frameBlowup costs, counted below.
------------------------------------------------------------------

-- two quantities under one tower level multiply within the NEXT level:
-- T² ≤ (2+T)² ≤ 2^T for T ≥ 6, and a tower level from 3 up is ≥ 16
tower-mul : ∀ (m a b : ℕ) → 3 ≤ m → a ≤ towerℕ m → b ≤ towerℕ m →
  a * b ≤ towerℕ (suc m)
tower-mul m a b 3≤m ha hb =
  ≤-trans (*-mono-≤ (≤-trans ha (m≤n+m (towerℕ m) 2))
                    (≤-trans hb (m≤n+m (towerℕ m) 2)))
          (sq≤2^ (towerℕ m) 6≤T)
  where
  6≤T : 6 ≤ towerℕ m
  6≤T = ≤-trans (≤ᵇ⇒≤ 6 16 _) (towerℕ-mono {3} {m} 3≤m)

k≤tower : ∀ (m k : ℕ) → 3 ≤ m → k ≤ 6 → k ≤ towerℕ m
k≤tower m k 3≤m k≤6 =
  ≤-trans k≤6 (≤-trans (≤ᵇ⇒≤ 6 16 _) (towerℕ-mono {3} {m} 3≤m))

-- the linear multiple the size axis needs, within one level
3T≤ : ∀ (m : ℕ) → 3 ≤ m → 3 * towerℕ m ≤ towerℕ (suc m)
3T≤ m 3≤m = tower-mul m 3 (towerℕ m) 3≤m (k≤tower m 3 3≤m (≤ᵇ⇒≤ 3 6 _)) ≤-refl

-- 1 ≤ x^k for 1 ≤ x
1≤pow≤ : ∀ (x k : ℕ) → 1 ≤ x → 1 ≤ x ^ k
1≤pow≤ x zero    h = ≤-refl
1≤pow≤ x (suc k) h = *-mono-≤ h (1≤pow≤ x k h)

-- ONE FOLD's SIZE STEP, iterated: j steps under a uniform cap M cost a
-- FACTOR (3M) each — sizeStep S s = S(1+2s) ≤ M·3s once s ≥ 1
iterSize-pow : ∀ (S M j s : ℕ) → 1 ≤ M → S ≤ M → s ≤ M →
  iterSize S j s ≤ (3 * M) ^ j * M
iterSize-pow S M zero    s 1≤M hS hsz = ≤-trans hsz (m≤m+n M 0)
iterSize-pow S M (suc j) s 1≤M hS hsz =
  ≤-trans (≤-reflexive (iterSize-suc S j s))
  (≤-trans (*-mono-≤ hS (s≤s (*-monoʳ-≤ 2 ih)))
  (≤-trans (*-monoʳ-≤ M sucY)
           (≤-reflexive shape)))
  where
  Y = (3 * M) ^ j * M
  ih : iterSize S j s ≤ Y
  ih = iterSize-pow S M j s 1≤M hS hsz
  1≤Y : 1 ≤ Y
  1≤Y = *-mono-≤ (1≤pow≤ (3 * M) j (*-mono-≤ (≤ᵇ⇒≤ 1 3 _) 1≤M)) 1≤M
  sucY : suc (2 * Y) ≤ 3 * Y
  sucY = ≤-trans (+-monoˡ-≤ (2 * Y) 1≤Y) (≤-reflexive (solve 1 idY refl Y))
    where idY = λ y → y :+ (y :+ (y :+ con 0)) := con 3 :* y
  shape : M * (3 * Y) ≡ (3 * M) ^ suc j * M
  shape = trans (solve 2 (λ m y → m :* (con 3 :* y) := (con 3 :* m) :* y)
                       refl M Y)
                (sym (*-assoc (3 * M) ((3 * M) ^ j) M))

-- suc (a * b) STILL FITS, and it is tower-mul's own slack that pays:
-- the bound goes through (2+T)·(2+T), which exceeds T·T by 4T+4.  The
-- strict form is what the REGISTRY axis now has to report, because the
-- count's arithmetic below consumes a strict registry bound
tower-mul-suc : ∀ (m a b : ℕ) → 3 ≤ m → a ≤ towerℕ m → b ≤ towerℕ m →
  suc (a * b) ≤ towerℕ (suc m)
tower-mul-suc m a b 3≤m ha hb =
  ≤-trans (≤-trans (s≤s (*-mono-≤ ha hb)) grow) (sq≤2^ (towerℕ m) 6≤T)
  where
  Tw = towerℕ m
  6≤T : 6 ≤ Tw
  6≤T = ≤-trans (≤ᵇ⇒≤ 6 16 _) (towerℕ-mono {3} {m} 3≤m)
  grow : suc (Tw * Tw) ≤ (2 + Tw) * (2 + Tw)
  grow =
    ≤-trans (≤-reflexive (solve 1 (λ x → con 1 :+ x :* x := x :* x :+ con 1)
                                refl Tw))
    (≤-trans (+-monoʳ-≤ (Tw * Tw) (s≤s (z≤n {3 + 4 * Tw})))
             (≤-reflexive (solve 1 (λ x → x :* x :+ (con 4 :+ con 4 :* x)
                                            := (con 2 :+ x) :* (con 2 :+ x))
                                 refl Tw)))

-- THE COUNT'S ARITHMETIC IS GONE, and its absence is the point: the
-- count no longer has any.  `sum-fits` used to land `2^(2^R)·S` under
-- `2^(2^T)` — the one place a STRICT registry bound was consumed — and
-- with the delivery bound a recursion rather than a 2-tower, the count
-- fits under the POOLED count by monotonicity in each field
-- (`J≤P` inside blowup-tower) and nothing is exponentiated at all.

-- ONE FOLD's WIDTH STEP, UNDER A TOWER: TWO stories.  `foldStep S w`
-- is S ^ suc w with both S and w under towerℕ k, so it is at most
-- (2 ^ T) ^ suc T = 2 ^ (T · suc T), and T · suc T ≤ (2 + T)² ≤ 2 ^ T —
-- tower-mul's own slack, spent on the width axis this time
foldStep-tower : ∀ (k S w : ℕ) → 3 ≤ k → S ≤ towerℕ k → w ≤ towerℕ k →
  foldStep S w ≤ towerℕ (2 + k)
foldStep-tower k S w 3≤k hS hw =
  ≤-trans (^-monoˡ-≤ (suc w) (≤-trans hS (<⇒≤ (n<2^n Tk))))
  (≤-trans (≤-reflexive (^-*-assoc 2 Tk (suc w)))
           (^-monoʳ-≤ 2 expo))
  where
  Tk = towerℕ k
  6≤T : 6 ≤ Tk
  6≤T = ≤-trans (≤ᵇ⇒≤ 6 16 _) (towerℕ-mono {3} {k} 3≤k)
  grow : Tk * suc Tk ≤ (2 + Tk) * (2 + Tk)
  grow = *-mono-≤ (m≤n+m Tk 2) (n≤1+n (suc Tk))
  expo : Tk * suc w ≤ towerℕ (suc k)
  expo = ≤-trans (*-monoʳ-≤ Tk (s≤s hw)) (≤-trans grow (sq≤2^ Tk 6≤T))

-- so j folds are 2·j stories, and THAT is why the height stopped being
-- linear: j is the instant's fold count, which is itself tower-sized
iterFold-tower : ∀ (k S w j : ℕ) → 3 ≤ k → S ≤ towerℕ k → w ≤ towerℕ k →
  iterFold S j w ≤ towerℕ (k + 2 * j)
iterFold-tower k S w zero 3≤k hS hw =
  subst (λ x → w ≤ towerℕ x) (sym (+-identityʳ k)) hw
iterFold-tower k S w (suc j) 3≤k hS hw =
  subst (λ x → iterFold S j (foldStep S w) ≤ towerℕ x) shape
    (iterFold-tower (2 + k) S (foldStep S w) j
       (≤-trans 3≤k (m≤n+m k 2))
       (≤-trans hS (towerℕ-mono (m≤n+m k 2)))
       (foldStep-tower k S w 3≤k hS hw))
  where
  shape : (2 + k) + 2 * j ≡ k + 2 * suc j
  shape = solve 2 (λ a b → (con 2 :+ a) :+ con 2 :* b
                             := a :+ con 2 :* (con 1 :+ b))
                refl k j

-- ONE INSTANT'S COST, ALL THREE AXES, and it is `blowH` by construction
-- rather than by arithmetic: the height function was WRITTEN to be what
-- these inequalities demand plus visible margin.
--
--   THE COUNT      sizeCount c ≤ poolCount Tw, by MONOTONICITY in each
--                  field and nothing else — `poolCount` IS this count
--                  with every field replaced by the pooled bound.  The
--                  old two-stories-for-the-delivery-tower accounting
--                  (and with it `sum-fits`, the one consumer of a
--                  STRICT registry bound) is gone: the delivery bound
--                  is a recursion now, so there is no exponent to fit.
--   THE SIZE       a factor (3T) per fold, sizeCount folds, and one
--                  story to land the product: two stories over the
--                  meeting level L = 4 + m + 2·P.
--   THE REGISTRY   linear in the count, and reported STRICTLY, which is
--                  what the next level's `hR` consumes.
--   THE WIDTH      TWO stories PER FOLD: m + 2 · sizeCount, which
--                  dominates the other three by an exponential and is
--                  the whole reason a closed-form height is gone.
--
-- EVERYTHING MEETS AT ONE LEVEL, `L = 4 + m + 2 · P` with
-- P = poolCount (towerℕ m), and `blowH m` is `suc (suc L)`.  That is
-- the whole accounting: two stories above L is where the size and the
-- registry land, and the width's `m + 2 · J` is under `6 + m + 2 · P`
-- as soon as J ≤ P.
--
-- THE WIDTH HYPOTHESIS IS NEW, and it is what reading cWid costs: the
-- old bound carried only (cSize, cReg) because the count could not see
-- a width.  It now can, so the induction has to feed the width back to
-- itself, and `capsAt`'s base has to pay the ENTRY CEILING under a
-- tower — which `capsBase` does by reading it, not by bracketing it
blowup-tower : ∀ (m : ℕ) (c : Caps) → 3 ≤ m →
  2 ≤ Caps.cSize c →
  Caps.cSize c ≤ towerℕ m → suc (Caps.cReg c) ≤ towerℕ m →
  Caps.cWid c ≤ towerℕ m →
  (Caps.cSize (frameBlowup c m) ≤ towerℕ (blowH m))
  × (suc (Caps.cReg (frameBlowup c m)) ≤ towerℕ (blowH m))
  × (Caps.cWid (frameBlowup c m) ≤ towerℕ (blowH m))
blowup-tower m c 3≤m 2≤S hS hR hW = sizeGoal , regGoal , widGoal
  where
  1≤S : 1 ≤ Caps.cSize c
  1≤S = ≤-trans (s≤s z≤n) 2≤S
  S = Caps.cSize c
  R = Caps.cReg c
  W = Caps.cWid c
  Tw = towerℕ m
  J = sizeCount c m
  P = poolCount Tw m
  L = 4 + m + 2 * P          -- the level the three axes meet at

  -- `blowH` is opaque (a normalisation guard, Rx.Evaluator); this is
  -- the one place its body is needed, and it is needed three times
  hgt : towerℕ (suc (suc L)) ≤ towerℕ (blowH m)
  hgt = ≤-reflexive (cong towerℕ (sym (blowH-body m)))

  hR′ : R ≤ Tw
  hR′ = ≤-trans (n≤1+n R) hR

  1≤Tw : 1 ≤ Tw
  1≤Tw = ≤-trans 1≤S hS

  -- THE COUNT, and it is monotonicity in each field and nothing else —
  -- `poolBody` IS this count with every field pooled, level walk and all
  J≤P : J ≤ P
  J≤P = ≤-trans (≤-trans (≤-reflexive (sizeCount-body c m))
                   (lvls-mono (cDel c m) (dCapᶜ Tw Tw Tw m (suc Tw) 0)
                      2≤S hS hW ≤-refl
                      (≤-trans (≤-reflexive (cDel-body c m))
                         (dCapᶜ-mono (suc S) (suc Tw)
                            2≤S hS hW hR′ (s≤s hS) ≤-refl))))
                (poolBody≤poolCount Tw m 1≤Tw)

  3≤L : 3 ≤ L
  3≤L = ≤-trans (≤-trans (≤ᵇ⇒≤ 3 4 _) (m≤m+n 4 m)) (m≤m+n (4 + m) (2 * P))

  m≤L : m ≤ L
  m≤L = ≤-trans (m≤n+m m 4) (m≤m+n (4 + m) (2 * P))

  Tw≤L : Tw ≤ towerℕ L
  Tw≤L = towerℕ-mono m≤L

  sucP≤L : suc P ≤ L
  sucP≤L = ≤-trans (s≤s (m≤m+n P (P + 0)))
                   (+-monoˡ-≤ (2 * P) (s≤s (z≤n {3 + m})))

  sucJ≤ : suc J ≤ towerℕ L
  sucJ≤ = ≤-trans (≤-trans (s≤s J≤P) sucP≤L) (k≤towerℕ L)

  J≤L : J ≤ towerℕ L
  J≤L = ≤-trans (n≤1+n J) sucJ≤

  -- SIZE: (3T) per fold, J folds, and one story to land the product
  sizeGoal : Caps.cSize (frameBlowup c m) ≤ towerℕ (blowH m)
  sizeGoal =
    ≤-trans (iterSize-pow S Tw J S 1≤Tw hS hS)
    (≤-trans (*-monoʳ-≤ ((3 * Tw) ^ J) (m≤m+n Tw (Tw + (Tw + 0))))
    (≤-trans (≤-reflexive (*-comm ((3 * Tw) ^ J) (3 * Tw)))
    (≤-trans (^-monoˡ-≤ (suc J) (3T≤ m 3≤m))
    (≤-trans (≤-reflexive (^-*-assoc 2 Tw (suc J)))
    (≤-trans (^-monoʳ-≤ 2 (tower-mul L Tw (suc J) 3≤L Tw≤L sucJ≤))
             hgt)))))

  -- REGISTRATIONS: linear in the count, and reported STRICTLY
  regGoal : suc (Caps.cReg (frameBlowup c m)) ≤ towerℕ (blowH m)
  regGoal =
    ≤-trans (tower-mul-suc (suc L) R (suc (J * S)) (≤-trans 3≤L (n≤1+n L))
               (≤-trans hR′ (≤-trans Tw≤L (towerℕ-mono (n≤1+n L))))
               (tower-mul-suc L J S 3≤L J≤L (≤-trans hS Tw≤L)))
            hgt

  -- WIDTH: two stories a fold, and the fold count is J
  widGoal : Caps.cWid (frameBlowup c m) ≤ towerℕ (blowH m)
  widGoal =
    ≤-trans (≤-trans (iterFold-tower m S W J 3≤m hS hW) (towerℕ-mono climb))
            hgt
    where
    climb : m + 2 * J ≤ suc (suc L)
    climb = ≤-trans (+-monoˡ-≤ (2 * J) (m≤n+m m 6))
                    (+-monoʳ-≤ (6 + m) (*-monoʳ-≤ 2 J≤P))

-- THE TOWER HEIGHT of a caps level — BY RECURRENCE, exactly as the caps
-- themselves are, and IT IS THE SAME FUNCTION `budgetAt` IS DEFINED
-- FROM.  There is no closed form and there cannot be one: the width axis
-- climbs 2·sizeCount stories an instant and sizeCount reads the width,
-- so the height iterates the tower FUNCTION.  The base is `capsBase`,
-- which reads the ENTRY CEILING directly rather than bracketing it by
-- some function of the syntax size — the five static width measures
-- tower in the syntax, and `k ≤ towerℕ k` is a complete and free answer
-- to "under what tower does this number sit".  That is why the width
-- conjunct below costs no new postulate.
3≤blowH : ∀ (m : ℕ) → 3 ≤ blowH m
3≤blowH m =
  ≤-trans (≤-trans (≤-trans (≤ᵇ⇒≤ 3 6 _) (m≤m+n 6 m))
                   (m≤m+n (6 + m) (2 * poolCount (towerℕ m) m)))
          (≤-reflexive (sym (blowH-body m)))

3≤capsH : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  3 ≤ capsH e sl id
3≤capsH e sl zero    = 3≤blowH (capsBase e sl)
3≤capsH e sl (suc id) = 3≤blowH (capsH e sl id)

capsAt-tower : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  (Caps.cSize (capsAt e sl id) ≤ towerℕ (capsH e sl id))
  × (suc (Caps.cReg (capsAt e sl id)) ≤ towerℕ (capsH e sl id))
  × (Caps.cWid (capsAt e sl id) ≤ towerℕ (capsH e sl id))
capsAt-tower {n = n} e sl zero =
  blowup-tower (capsBase e sl)
    (caps (2 + sizeᵉ e + slotsSize sl + slotsClos sl)
          (suc (entryCeil n sl e))
          (suc sz))
    (m≤m+n 3 _) (s≤s (s≤s z≤n))
    (≤-trans base≤ K)
    (≤-trans suc≤ K)
    (≤-trans (m≤n+m (suc (entryCeil n sl e)) (3 + szc)) K)
  where
  sz = sizeᵉ e + slotsSize sl
  szc = sz + slotsClos sl
  K : capsBase e sl ≤ towerℕ (capsBase e sl)
  K = k≤towerℕ (capsBase e sl)
  szc≤ : 2 + szc ≤ capsBase e sl
  szc≤ = ≤-trans (n≤1+n (2 + szc)) (m≤m+n (3 + szc) (suc (entryCeil n sl e)))
  suc≤ : 2 + sz ≤ capsBase e sl
  suc≤ = ≤-trans (+-monoʳ-≤ 2 (m≤m+n sz (slotsClos sl))) szc≤
  base≤ : 2 + sizeᵉ e + slotsSize sl + slotsClos sl ≤ capsBase e sl
  base≤ = ≤-trans (≤-reflexive
                    (trans (cong (_+ slotsClos sl) (+-assoc 2 (sizeᵉ e) (slotsSize sl)))
                           (+-assoc 2 (sizeᵉ e + slotsSize sl) (slotsClos sl))))
                  szc≤
capsAt-tower e sl (suc id) =
  blowup-tower (capsH e sl id) (capsAt e sl id)
    (3≤capsH e sl id)
    (2≤capsAt-size e sl id)
    (proj₁ (capsAt-tower e sl id))
    (proj₁ (proj₂ (capsAt-tower e sl id)))
    (proj₂ (proj₂ (capsAt-tower e sl id)))

-- three stories on top of a tower height is three more levels
tower-3 : ∀ (h x : ℕ) → x ≤ towerℕ h → 2 ^ (2 ^ (2 ^ x)) ≤ towerℕ (3 + h)
tower-3 h x le = ^-monoʳ-≤ 2 (^-monoʳ-≤ 2 (^-monoʳ-≤ 2 le))

-- THE LEAF: one level step at least exponentiates.  `dLvl` runs `fLvlD`
-- `suc (sizeAt S J)` times from `J`, and `fLvlD` is inflationary by at
-- least one, so the step clears `sizeAt S J` — which is `iterSize S J S`,
-- and `sizeStep S s = S * suc (2 * s)` at least doubles.  Both halves are
-- ordinary inductions; the `iterL` half mirrors the deleted `J+n≤lvls`
-- with `fLvlD` in place of `dLvl`.
-- (1) suc J ≤ fLvlD S W d J.  This is not where the growth comes from:
-- it is what carries the iteration COUNT down into the level the
-- iteration lands at, which is what makes the count buy stories.
sucJ≤fLvlD : ∀ (S W d J : ℕ) → suc J ≤ fLvlD S W d J
sucJ≤fLvlD S W d J =
  ≤-trans
    (≤-trans (s≤s (m≤m+n J (suc (widAt S W J) * suc (sizeAt S J))))
             (≤-reflexive (sym (+-suc J (suc (widAt S W J) * suc (sizeAt S J))))))
    (fLvl≤fLvlD S W d J)

-- (2) n steps of the level ladder are worth at least n levels
J+n≤iterL : ∀ (S W d n J : ℕ) → J + n ≤ iterL S W d n J
J+n≤iterL S W d zero    J = ≤-reflexive (+-identityʳ J)
J+n≤iterL S W d (suc n) J =
  ≤-trans (≤-reflexive (+-suc J n))
  (≤-trans (+-monoˡ-≤ n (sucJ≤fLvlD S W d J))
           (J+n≤iterL S W d n (fLvlD S W d J)))

-- AND THE COUNT DOMINATES THE SIZE FIELD ITSELF, which is what lets a
-- descent's own written size be spent as a LEVEL.  One delivery's
-- ladder starts at `sizeAt S 0`, and that IS `S`; `iterL` never goes
-- down, and one registration is enough to reach the first delivery --
-- so the entry cap's size is already inside the count, at every depth.
size≤sizeCount : ∀ (c : Caps) (d : ℕ) → 2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Caps.cSize c ≤ sizeCount c d
size≤sizeCount c d 2≤S 1≤R =
  ≤-trans (≤-trans (≤-trans (n≤1+n (Caps.cSize c))
                            (J+n≤iterL (Caps.cSize c) (Caps.cWid c) d
                               (suc (sizeAt (Caps.cSize c) 0)) 0))
                   (lvls-mono 1 (cDel c d) 2≤S ≤-refl ≤-refl ≤-refl 1≤D))
          (≤-reflexive (sym (sizeCount-body c d)))
  where
  1≤D : 1 ≤ cDel c d
  1≤D = ≤-trans (1≤dCapᶜ (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d
                         (Caps.cSize c) 0 1≤R)
                (≤-reflexive (sym (cDel-body c d)))

-- AND THE FUEL AT AN INSTANT IS TWO EXPONENTIALS ABOVE THE SIZE AT
-- THAT SAME INSTANT, which is the comparison the height side has been
-- reaching for and the one `blowup-tower` cannot give, since it
-- brackets by `towerℕ` of the height and that is the wrong side.  Two
-- and not one, because the currencies that have to fit under the fuel
-- read the size through a POLYNOMIAL before exponentiating it, and a
-- single exponential of the size is already spent by the polynomial.
--
-- ONE DELIVERY'S CLIMB PASSES THE SIZE IT STARTS FROM.  A delivery is
-- one `dLvl`, and `dLvl` iterates the frame level `suc (sizeAt S J)`
-- times from `J`, each turn strictly increasing -- so the level after
-- a delivery is above the SIZE read at the level before it.  That one
-- step is the whole content: the blown-up size is `sizeAt` read at the
-- count, and the count plus one delivery is already past it.
sizeAt≤lvls-suc : ∀ (S W d J n : ℕ) →
  sizeAt S (lvls S W d J n) ≤ lvls S W d J (suc n)
sizeAt≤lvls-suc S W d J n =
  ≤-trans (≤-trans (n≤1+n (sizeAt S L)) (m≤n+m (suc (sizeAt S L)) L))
          (J+n≤iterL S W d (suc (sizeAt S L)) L)
  where L = lvls S W d J n

-- EACH FOLD AT LEAST DOUBLES, so a size read at level `k` carries a
-- factor of two per fold.  This is stated here rather than beside the
-- clause work that also spends it, because that face imports this
-- module and the level ladder is where the exponent is collected.
iterSize-2^ : ∀ (S k s : ℕ) → 1 ≤ S → 2 ^ k * s ≤ iterSize S k s
iterSize-2^ S zero    s hS = ≤-reflexive (*-identityˡ s)
iterSize-2^ S (suc k) s hS =
  ≤-trans (≤-reflexive shape)
          (≤-trans (*-monoʳ-≤ (2 ^ k) 2s≤step)
                   (iterSize-2^ S k (sizeStep S s) hS))
  where
  shape : 2 ^ suc k * s ≡ 2 ^ k * (2 * s)
  shape = solve 2 (λ a b → (con 2 :* a) :* b := a :* (con 2 :* b))
                refl (2 ^ k) s
  2s≤step : 2 * s ≤ sizeStep S s
  2s≤step = ≤-trans (n≤1+n (2 * s))
                    (≤-trans (≤-reflexive (sym (*-identityˡ (suc (2 * s)))))
                             (*-monoˡ-≤ (suc (2 * s)) hS))

-- SO ONE LEVEL OF THE LADDER EXPONENTIATES.  The size read at a level
-- is `iterSize` run that many times off the entry size, and each run
-- doubles -- so the next level is above two to the current one, and
-- two levels are above two to the two.
exp-lvls : ∀ (S W d J n : ℕ) → 1 ≤ S →
  2 ^ lvls S W d J n ≤ lvls S W d J (suc n)
exp-lvls S W d J n 1≤S =
  ≤-trans (≤-trans (≤-reflexive (sym (*-identityʳ (2 ^ L))))
                   (≤-trans (*-monoʳ-≤ (2 ^ L) 1≤S) (iterSize-2^ S L S 1≤S)))
          (sizeAt≤lvls-suc S W d J n)
  where L = lvls S W d J n

exp2-lvls : ∀ (S W d J n : ℕ) → 1 ≤ S →
  2 ^ (2 ^ lvls S W d J n) ≤ lvls S W d J (suc (suc n))
exp2-lvls S W d J n 1≤S =
  ≤-trans (^-monoʳ-≤ 2 (exp-lvls S W d J n 1≤S))
          (exp-lvls S W d J (suc n) 1≤S)

-- AND THE POOLED COUNT HAS THE SPARE DELIVERIES TO PAY FOR THEM.  Its
-- walk runs the pooled registry rather than this caps' one, and the
-- caps carry a STRICT registry bound under the tower -- so the pooled
-- walk is at least one position longer.  One position is not one
-- level: the position pays `suc` of a whole delivery cap, and that cap
-- is at least two once the fuel has two stories, so the single spare
-- registration buys the three levels the two exponentials cost.
2≤dCapᶜ : ∀ (S W R d g J : ℕ) → 2 ≤ S → 1 ≤ R →
  2 ≤ dCapᶜ S W R d (2 + g) J
2≤dCapᶜ S W R d g J 2≤S 1≤R =
  ≤-trans (s≤s (1≤dCapᶜ S W R d g (lvls S W d J 1) 1≤R))
          (dWalkᶜ-mono {d = d} (suc g) (suc g) 1 (regAt S R J)
                       2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl
                       (1≤regAt S R J 1≤R))

3+dWalkᶜ : ∀ (S W R d g J i : ℕ) → 2 ≤ S → 1 ≤ R → 2 ≤ g →
  3 + dWalkᶜ S W R d g J i ≤ dWalkᶜ S W R d g J (suc i)
3+dWalkᶜ S W R d (suc (suc g)) J i 2≤S 1≤R (s≤s (s≤s _)) =
  ≤-trans (≤-reflexive (+-comm 3 w))
          (+-monoʳ-≤ w (s≤s (2≤dCapᶜ S W R d g (lvls S W d J (suc w)) 2≤S 1≤R)))
  where w = dWalkᶜ S W R d (suc (suc g)) J i

cDel+3≤pooled : ∀ (m : ℕ) (c : Caps) →
  3 ≤ m → 2 ≤ Caps.cSize c →
  Caps.cSize c ≤ towerℕ m → suc (Caps.cReg c) ≤ towerℕ m →
  Caps.cWid c ≤ towerℕ m →
  3 + cDel c m ≤ dCapᶜ (towerℕ m) (towerℕ m) (towerℕ m) m (suc (towerℕ m)) 0
cDel+3≤pooled m c 3≤m 2≤S hS hR hW =
  ≤-trans (≤-reflexive (cong (3 +_)
            (trans (cDel-body c m)
                   (cong (dWalkᶜ S W R m S 0) (*-identityʳ R)))))
  (≤-trans (+-monoʳ-≤ 3 (dWalkᶜ-mono {d = m} S T R R 2≤S hS hW R≤T hS ≤-refl ≤-refl))
  (≤-trans (3+dWalkᶜ T T T m T 0 R 2≤T 1≤T 2≤T)
  (≤-trans (dWalkᶜ-mono {d = m} T T (suc R) T 2≤T ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl hR)
           (≤-reflexive (cong (dWalkᶜ T T T m T 0) (sym (*-identityʳ T)))))))
  where
  S = Caps.cSize c
  W = Caps.cWid c
  R = Caps.cReg c
  T = towerℕ m
  R≤T : R ≤ T
  R≤T = ≤-trans (n≤1+n R) hR
  3≤T : 3 ≤ T
  3≤T = ≤-trans 3≤m (k≤towerℕ m)
  2≤T : 2 ≤ T
  2≤T = ≤-trans (s≤s (s≤s z≤n)) 3≤T
  1≤T : 1 ≤ T
  1≤T = ≤-trans (s≤s z≤n) 2≤T

-- THE EXPONENTIAL LANDS UNDER THE POOLED COUNT, WHICH IS THE HALF THE
-- FUEL CARRIES TWICE.  `blowH` is `6 + m + 2 · poolCount`, so a
-- consumer wanting the exponential once takes this and pays the
-- doubling away, and a consumer wanting it TWICE takes it at both
-- summands.  The split is here rather than at the two consumers
-- because the climb -- size into a level, level into the pooled walk --
-- is the whole content and neither reading may re-derive it.
blowup-exp≤pool : ∀ (m : ℕ) (c : Caps) →
  3 ≤ m → 2 ≤ Caps.cSize c →
  Caps.cSize c ≤ towerℕ m → suc (Caps.cReg c) ≤ towerℕ m →
  Caps.cWid c ≤ towerℕ m →
  2 ^ (2 ^ Caps.cSize (frameBlowup c m)) ≤ poolCount (towerℕ m) m
blowup-exp≤pool m c 3≤m 2≤S hS hR hW =
  ≤-trans (^-monoʳ-≤ 2 (^-monoʳ-≤ 2 size≤L₁))
  (≤-trans (exp2-lvls S W m 0 (suc (cDel c m)) 1≤S)
  (≤-trans (lvls-mono {d = m} (3 + cDel c m) N 2≤S hS hW ≤-refl
                      (cDel+3≤pooled m c 3≤m 2≤S hS hR hW))
           (poolBody≤poolCount T m 1≤T)))
  where
  S = Caps.cSize c
  W = Caps.cWid c
  T = towerℕ m
  N = dCapᶜ T T T m (suc T) 0
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) 2≤S
  1≤T : 1 ≤ T
  1≤T = ≤-trans 1≤S hS
  size≤L₁ : Caps.cSize (frameBlowup c m) ≤ lvls S W m 0 (suc (cDel c m))
  size≤L₁ = ≤-trans (≤-reflexive (cong (sizeAt S) (sizeCount-body c m)))
                    (sizeAt≤lvls-suc S W m 0 (cDel c m))

pool2≤blowH : ∀ (m : ℕ) →
  poolCount (towerℕ m) m + poolCount (towerℕ m) m ≤ blowH m
pool2≤blowH m =
  ≤-trans (≤-reflexive (sym (2X≡X+X (poolCount (towerℕ m) m))))
  (≤-trans (m≤n+m (2 * poolCount (towerℕ m) m) (6 + m))
           (≤-reflexive (sym (blowH-body m))))

blowup-exp2≤blowH : ∀ (m : ℕ) (c : Caps) →
  3 ≤ m → 2 ≤ Caps.cSize c →
  Caps.cSize c ≤ towerℕ m → suc (Caps.cReg c) ≤ towerℕ m →
  Caps.cWid c ≤ towerℕ m →
  2 ^ (2 ^ Caps.cSize (frameBlowup c m)) + 2 ^ (2 ^ Caps.cSize (frameBlowup c m))
    ≤ blowH m
blowup-exp2≤blowH m c 3≤m 2≤S hS hR hW =
  ≤-trans (+-mono-≤ ex ex) (pool2≤blowH m)
  where
  ex = blowup-exp≤pool m c 3≤m 2≤S hS hR hW

blowup-exp≤blowH : ∀ (m : ℕ) (c : Caps) →
  3 ≤ m → 2 ≤ Caps.cSize c →
  Caps.cSize c ≤ towerℕ m → suc (Caps.cReg c) ≤ towerℕ m →
  Caps.cWid c ≤ towerℕ m →
  2 ^ (2 ^ Caps.cSize (frameBlowup c m)) ≤ blowH m
blowup-exp≤blowH m c 3≤m 2≤S hS hR hW =
  ≤-trans (m≤n+m P P) (blowup-exp2≤blowH m c 3≤m 2≤S hS hR hW)
  where
  P = 2 ^ (2 ^ Caps.cSize (frameBlowup c m))

-- THE BASE INSTANT'S BLOWUP PREMISES, packaged once.  `capsAt`'s base
-- is a `frameBlowup` like every later instant's, but its caps and its
-- story index are written out rather than named, so the five side
-- conditions have to be re-derived from the base arithmetic -- and two
-- readings of that same blowup would otherwise re-derive them twice.
capsBase-blow-prem : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) →
  let c = caps (2 + sizeᵉ e + slotsSize sl + slotsClos sl)
               (suc (entryCeil _ sl e))
               (suc (sizeᵉ e + slotsSize sl))
      m = capsBase e sl
  in (3 ≤ m) × (2 ≤ Caps.cSize c) × (Caps.cSize c ≤ towerℕ m)
     × (suc (Caps.cReg c) ≤ towerℕ m) × (Caps.cWid c ≤ towerℕ m)
capsBase-blow-prem {n = n} e sl =
  m≤m+n 3 _ , s≤s (s≤s z≤n) , ≤-trans base≤ K , ≤-trans suc≤ K
  , ≤-trans (m≤n+m (suc (entryCeil n sl e)) (3 + szc)) K
  where
  sz = sizeᵉ e + slotsSize sl
  szc = sz + slotsClos sl
  K : capsBase e sl ≤ towerℕ (capsBase e sl)
  K = k≤towerℕ (capsBase e sl)
  szc≤ : 2 + szc ≤ capsBase e sl
  szc≤ = ≤-trans (n≤1+n (2 + szc)) (m≤m+n (3 + szc) (suc (entryCeil n sl e)))
  suc≤ : 2 + sz ≤ capsBase e sl
  suc≤ = ≤-trans (+-monoʳ-≤ 2 (m≤m+n sz (slotsClos sl))) szc≤
  base≤ : 2 + sizeᵉ e + slotsSize sl + slotsClos sl ≤ capsBase e sl
  base≤ = ≤-trans (≤-reflexive
                    (trans (cong (_+ slotsClos sl) (+-assoc 2 (sizeᵉ e) (slotsSize sl)))
                           (+-assoc 2 (sizeᵉ e + slotsSize sl) (slotsClos sl))))
                  szc≤

-- SO THE FUEL AT AN INSTANT IS TWO EXPONENTIALS ABOVE THE SIZE AT THAT
-- SAME INSTANT, at every instant including the base.  The blowup is
-- driven by the fuel the previous story reached and `blowH` is what
-- the fuel climbs by, so the two are one quantity read once each --
-- and the base is no exception, since the height already starts one
-- `blowH` up.  What was missing was only that the pooled walk outruns
-- this caps' own delivery count, and the STRICT registry bracket
-- supplies it.
capsAt-exp≤capsH : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  2 ^ (2 ^ Caps.cSize (capsAt e sl id)) ≤ capsH e sl id
capsAt-exp≤capsH e sl zero =
  blowup-exp≤blowH _ _
    (proj₁ (capsBase-blow-prem e sl))
    (proj₁ (proj₂ (capsBase-blow-prem e sl)))
    (proj₁ (proj₂ (proj₂ (capsBase-blow-prem e sl))))
    (proj₁ (proj₂ (proj₂ (proj₂ (capsBase-blow-prem e sl)))))
    (proj₂ (proj₂ (proj₂ (proj₂ (capsBase-blow-prem e sl)))))
capsAt-exp≤capsH e sl (suc id) =
  blowup-exp≤blowH (capsH e sl id) (capsAt e sl id)
    (3≤capsH e sl id)
    (2≤capsAt-size e sl id)
    (proj₁ (capsAt-tower e sl id))
    (proj₁ (proj₂ (capsAt-tower e sl id)))
    (proj₂ (proj₂ (capsAt-tower e sl id)))

-- THE SAME READING, WITH THE FUEL'S SECOND COPY SPENT.  The round's
-- ceiling is a cap PLUS an increment and each half is priced by its own
-- exponential, so the consumer needs the pair rather than the single
-- reading -- and the pair costs nothing extra, since the fuel carries
-- the pooled count twice and the single reading was already throwing
-- one copy away.
capsAt-exp2≤capsH : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  2 ^ (2 ^ Caps.cSize (capsAt e sl id)) + 2 ^ (2 ^ Caps.cSize (capsAt e sl id))
    ≤ capsH e sl id
capsAt-exp2≤capsH e sl zero =
  blowup-exp2≤blowH _ _
    (proj₁ (capsBase-blow-prem e sl))
    (proj₁ (proj₂ (capsBase-blow-prem e sl)))
    (proj₁ (proj₂ (proj₂ (capsBase-blow-prem e sl))))
    (proj₁ (proj₂ (proj₂ (proj₂ (capsBase-blow-prem e sl)))))
    (proj₂ (proj₂ (proj₂ (proj₂ (capsBase-blow-prem e sl)))))
capsAt-exp2≤capsH e sl (suc id) =
  blowup-exp2≤blowH (capsH e sl id) (capsAt e sl id)
    (3≤capsH e sl id)
    (2≤capsAt-size e sl id)
    (proj₁ (capsAt-tower e sl id))
    (proj₁ (proj₂ (capsAt-tower e sl id)))
    (proj₂ (proj₂ (capsAt-tower e sl id)))

-- THE WIDTH IS UNDER THE NEXT INSTANT'S SIZE, and the route is the
-- level ladder rather than any comparison of the two recurrences.  The
-- width only enters the count through `fCharge`, which is a `suc` of a
-- product one of whose factors is `suc (widAt S W J)` -- and at level
-- zero `widAt S W 0` IS `W`, so no fold has run yet and the bound needs
-- nothing about `S`.  One delivery is one `dLvl`, so the count already
-- clears that charge.
wid≤dLvl : ∀ (S W d : ℕ) → W ≤ dLvl S W d 0
wid≤dLvl S W d =
  ≤-trans (≤-trans W≤fLvl (fLvl≤fLvlD S W d 0))
          (iterL-infl S W d (sizeAt S 0) (fLvlD S W d 0))
  where
  W≤fLvl : W ≤ fLvl S W 0
  W≤fLvl = ≤-trans (n≤1+n W)
                   (≤-trans (m≤m*n (suc W) (suc (sizeAt S 0))) (n≤1+n _))

wid≤sizeCount : ∀ (c : Caps) (d : ℕ) → 2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Caps.cWid c ≤ sizeCount c d
wid≤sizeCount c d 2≤S 1≤R =
  ≤-trans (≤-trans (wid≤dLvl (Caps.cSize c) (Caps.cWid c) d)
                   (lvls-mono 1 (cDel c d) 2≤S ≤-refl ≤-refl ≤-refl 1≤D))
          (≤-reflexive (sym (sizeCount-body c d)))
  where
  1≤D : 1 ≤ cDel c d
  1≤D = ≤-trans (1≤dCapᶜ (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d
                         (Caps.cSize c) 0 1≤R)
                (≤-reflexive (sym (cDel-body c d)))

capsAt-size-mono : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  Caps.cSize (capsAt e sl id) ≤ Caps.cSize (capsAt e sl (suc id))
capsAt-size-mono e sl id =
  cSize≤frameBlowup (capsAt e sl id) (capsH e sl id)
    (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id))

-- AND THE SIZE GAIN IS EXPONENTIAL IN THE SIZE ITSELF, which is the
-- room every ceiling on this face is eventually paid out of.  The
-- count is above the size, every size step at least doubles, and the
-- step is taken count-many times -- so the next size is above two to
-- the current one, times it.  Stated with the factor still attached
-- because a consumer wanting only the exponential drops it in one
-- step and a consumer wanting both cannot recover it.
exp-size-gain : ∀ (c : Caps) (d : ℕ) → 2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  2 ^ Caps.cSize c * Caps.cSize c ≤ Caps.cSize (frameBlowup c d)
exp-size-gain c d 2≤S 1≤R =
  ≤-trans (*-monoˡ-≤ S (^-monoʳ-≤ 2 (size≤sizeCount c d 2≤S 1≤R)))
          (iterSize-2^ S J S (≤-trans (s≤s z≤n) 2≤S))
  where
  S = Caps.cSize c
  J = sizeCount c d

capsAt-exp-gain : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  2 ^ Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id)
    ≤ Caps.cSize (capsAt e sl (suc id))
capsAt-exp-gain e sl id =
  exp-size-gain (capsAt e sl id) (capsH e sl id)
    (2≤capsAt-size e sl id) (1≤capsAt-reg e sl id)

-- AND THE OTHER SIDE OF THE SAME STEP: every size step at least
-- MULTIPLIES BY THE SIZE, so the count-many steps put a whole power of
-- the size under the next one.  That floor is far above the doubling
-- one and it is the half a logarithm has to be read against -- an
-- upper bound on the next size is what makes its bit length nameable,
-- and only a lower bound this strong leaves room to pay for it.
pow≤iterSize : ∀ (S k s : ℕ) → 1 ≤ S → S ^ k * s ≤ iterSize S k s
pow≤iterSize S zero    s hS = ≤-reflexive (*-identityˡ s)
pow≤iterSize S (suc k) s hS =
  ≤-trans (≤-reflexive shape)
          (≤-trans (*-monoʳ-≤ (S ^ k) Ss≤step)
                   (pow≤iterSize S k (sizeStep S s) hS))
  where
  shape : S ^ suc k * s ≡ S ^ k * (S * s)
  shape = solve 3 (λ x a b → (x :* a) :* b := a :* (x :* b))
                  refl S (S ^ k) s
  Ss≤step : S * s ≤ sizeStep S s
  Ss≤step = *-monoʳ-≤ S (≤-trans (m≤m+n s (s + 0)) (n≤1+n (s + (s + 0))))

-- THE FLOOR IN THE FORM THE ROOM WANTS IT: the next size is above a
-- whole power of this one, the exponent being the count and one more
-- for the seed.  A ceiling on the next size is what makes its bit
-- length nameable, and a floor this strong is what leaves room to pay
-- for that length.
size-lower : ∀ (c : Caps) (d : ℕ) → 1 ≤ Caps.cSize c →
  Caps.cSize c ^ suc (sizeCount c d) ≤ Caps.cSize (frameBlowup c d)
size-lower c d 1≤S =
  ≤-trans (≤-reflexive (*-comm S (S ^ J))) (pow≤iterSize S J S 1≤S)
  where
  S = Caps.cSize c
  J = sizeCount c d

-- A LINEAR READING UNDER A POWER OF THREE, which is the one shape the
-- room argument below needs and the doubling lemmas beside it cannot
-- give: three summands are wanted, not two, and a base of three is
-- what the size floor already supplies.
lin3≤pow3 : ∀ (J : ℕ) → 1 ≤ J → 4 + 3 * J ≤ 3 ^ J * 3
lin3≤pow3 (suc zero)    _ = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
lin3≤pow3 (suc (suc k)) _ =
  ≤-trans (≤-reflexive shape)
          (≤-trans (+-mono-≤ (lin3≤pow3 (suc k) (s≤s z≤n)) 3≤P)
                   (≤-trans grow (≤-reflexive (sym assoc))))
  where
  P = 3 ^ suc k * 3
  3≤P : 3 ≤ P
  3≤P = ≤-trans (≤-reflexive (sym (*-identityˡ 3)))
                (*-monoˡ-≤ 3 (one≤3^ (suc k)))
  shape : 4 + 3 * suc (suc k) ≡ (4 + 3 * suc k) + 3
  shape = solve 1 (λ x → con 4 :+ con 3 :* (con 1 :+ x)
                           := (con 4 :+ con 3 :* x) :+ con 3)
                refl (suc k)
  dbl : 2 * P ≡ P + P
  dbl = solve 1 (λ x → con 2 :* x := x :+ x) refl P
  grow : P + P ≤ 3 * P
  grow = ≤-trans (≤-reflexive (sym dbl))
                 (*-monoˡ-≤ P {2} {3} (s≤s (s≤s z≤n)))
  assoc : 3 ^ suc (suc k) * 3 ≡ 3 * (3 ^ suc k * 3)
  assoc = solve 1 (λ x → (con 3 :* x) :* con 3 := con 3 :* (x :* con 3))
                refl (3 ^ suc k)

-- AN UPPER READING OF THE WIDTH, WHICH THIS FACE HAS NEVER HAD.  Every
-- earlier bound on a blowup ran the other way: the width is the number
-- the base cap is BUILT from, so it read as an input with nothing above
-- it.  But the count a blowup iterates is itself above the width -- the
-- level ladder clears one fold charge, and one fold charge is where the
-- width enters -- while every size step at least multiplies by the
-- size.  So the size a blowup lands on is above a whole power of the
-- entry size with the count as exponent, and the count is above both
-- coordinates at once.  The three summands are exactly what an entry
-- exponent is assembled from: two readings of the base size and one of
-- the base width, all under the single size the blowup produced.
room-frameBlowup : ∀ (c : Caps) (d : ℕ) → 3 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  4 + (Caps.cSize c + Caps.cSize c) + Caps.cWid c
    ≤ Caps.cSize (frameBlowup c d)
room-frameBlowup c d 3≤S 1≤R =
  ≤-trans (≤-trans (+-mono-≤ (+-monoʳ-≤ 4 (+-mono-≤ S≤J S≤J)) W≤J)
                   (≤-reflexive shape))
          (≤-trans (lin3≤pow3 J 1≤J) pow≤)
  where
  S = Caps.cSize c
  J = sizeCount c d
  2≤S : 2 ≤ S
  2≤S = ≤-trans (s≤s (s≤s z≤n)) 3≤S
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) 2≤S
  S≤J : S ≤ J
  S≤J = size≤sizeCount c d 2≤S 1≤R
  W≤J : Caps.cWid c ≤ J
  W≤J = wid≤sizeCount c d 2≤S 1≤R
  1≤J : 1 ≤ J
  1≤J = ≤-trans 1≤S S≤J
  shape : 4 + (J + J) + J ≡ 4 + 3 * J
  shape = solve 1 (λ j → con 4 :+ (j :+ j) :+ j := con 4 :+ con 3 :* j)
                refl J
  pow≤ : 3 ^ J * 3 ≤ Caps.cSize (frameBlowup c d)
  pow≤ = ≤-trans (*-mono-≤ (^-monoˡ-≤ J 3≤S) 3≤S) (pow≤iterSize S J S 1≤S)

capsAt-entry-room : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) →
  4 + ((2 + sizeᵉ e + slotsSize sl + slotsClos sl)
     + (2 + sizeᵉ e + slotsSize sl + slotsClos sl))
    + suc (entryCeil n sl e)
    ≤ Caps.cSize (capsAt e sl 0)
capsAt-entry-room {n = n} e sl =
  room-frameBlowup
    (caps (2 + sizeᵉ e + slotsSize sl + slotsClos sl) (suc (entryCeil n sl e))
          (suc (sizeᵉ e + slotsSize sl)))
    (capsBase e sl)
    3≤Z (s≤s z≤n)
  where
  3≤Z : 3 ≤ 2 + sizeᵉ e + slotsSize sl + slotsClos sl
  3≤Z = ≤-trans (≤-trans (+-monoʳ-≤ 2 (sizeᵉ-pos e))
                         (m≤m+n (2 + sizeᵉ e) (slotsSize sl)))
                (m≤m+n (2 + sizeᵉ e + slotsSize sl) (slotsClos sl))
