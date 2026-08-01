-- STRATUM 1c of Verify-Budget-Sufficient: THE CAPS RECURRENCE ITSELF.
--
-- The Caps triple, the per-fold step functions (sizeStep / foldStep and
-- their iterates), frameStep, frameBlowup, the recurrence capsAt, the
-- j-monotonicity toolkit, and the supply lemmas that read a level off
-- the recurrence (2≤capsAt-size, 1≤capsAt-reg, cSize≤frameBlowup,
-- capsAt-base-size, cWid≤frameBlowup, capsAt-base-wid).
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
-- and frameBlowup take a Caps and nothing else, so they cannot read the
-- ledger, and round3b-ledger-reset-absurd stays unavailable.
module Verify-Budget-Sufficient.Caps where

open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _^_; _≤_;
                                _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive;
                                       +-assoc; +-comm; *-suc;
                                       *-monoˡ-≤; *-monoʳ-≤;
                                       m≤m+n; m≤n+m; n≤1+n; m≤m*n;
                                       ^-monoʳ-≤; ^-monoˡ-≤; <⇒≤;
                                       *-distribˡ-+; *-identityʳ;
                                       *-identityˡ; m≤m⊔n; m≤n⊔m)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; module ≡-Reasoning)

open import Rx.Exp       using (Ctx; Closed; sizeᵉ)
open import Rx.Frame-Width using (pWᵉ; slotsPW; slotsIW)
open import Rx.Evaluator using (Slots; slotsSize)

-- for n<2^n (foldStep's inflationary proof) and the whole stratum below,
-- which .Caps-Face and .Wet both re-export through this module
open import Verify-Budget-Sufficient.Keeps-Ring public

------------------------------------------------------------------
-- ROUND 4: PER-INSTANT CAPS, BY RECURRENCE ON THE INSTANT.
--
-- deepScan killed the fixed-height cap (see the refutation below).  What
-- replaces it is NOT a bigger closed formula — it is a recurrence:
--
--     Caps 0        = the entry measure (program + slot telescope)
--     Caps (suc id) = frameBlowup (Caps id)
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
-- THE ROUND-5 GATE IS THE TYPE.  `frameBlowup : Caps → Caps` cannot read
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


-- ONE FOLD's worst case on a width — AND WHY IT READS THE SIZE.
--
-- The earlier `2 ^ suc w` was gated against deepScan's PAYLOAD count and
-- is refuted against the quantity capsOK? actually bounds: one fold
-- takes deepScan's stored width 1 ↦ 6 where it allowed 4
-- (State-Blowup-Probe).  The reason is structural — `innWᵉ (scanᵉ f z e)`
-- puts the source's width in an EXPONENT whose base is read off the step
-- function's syntax — so the per-fold multiplier is a property of `f`,
-- and cSize is the only thing in Caps that bounds a step function.
--
-- Note this is a strict GENERALISATION: at S = 2 it is exactly the old
-- step, so Frame-Work-Probe's 2 / 6 / 126 gates still read as before
foldStep : ℕ → ℕ → ℕ
foldStep S w = S ^ suc w

iterFold : ℕ → ℕ → ℕ → ℕ
iterFold S zero    w = w
iterFold S (suc k) w = iterFold S k (foldStep S w)

-- ONE FOLD's worst case on a SIZE, straight off size-subΘᵉ: a fold
-- substitutes the accumulator into the step function, and
-- size-subΘᵉ bounds that by `sizeᵉ f * suc (2 * V)` with V the env cap.
-- Both `sizeᵉ f` and V are ≤ cSize, hence S in both positions
sizeStep : ℕ → ℕ → ℕ
sizeStep S s = S * suc (2 * s)

iterSize : ℕ → ℕ → ℕ → ℕ
iterSize S zero    s = s
iterSize S (suc k) s = iterSize S k (sizeStep S s)

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
--
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
--
-- The R of that count is the registry AT THE END of the cascade, not at
-- entry, because `shareAdmit` reads the live registry; a fold that mints
-- on a shared slot adds a node mid-traversal.  Mint-Loop-Probe's
-- three-level lean ladder at k = 2 delivers 176 times out of an ENTRY
-- registry of 7, and 2 ^ 7 = 128.  So the excess is real, `D * cSize`
-- is itself over `2 ^ cReg * cSize`, and the whole paths-times-frames
-- route through that middle step is gone.
--
-- WHAT SURVIVES IS THE SAME INJECTION WITH A SECOND COORDINATE.  A
-- delivery is sent not to the set of registrations it visits but to the
-- PAIR (the pre-state registrations it visits, an index for which minted
-- registrations it went through).  The first coordinate ranges over
-- subsets of the entry registry — `2 ^ cReg` of them.
--
-- THE SECOND COORDINATE IS NOT BOUNDED BY cSize, and that was the second
-- thing measured false here.  It was first stated so, on the reasoning
-- that a mint is born of a subscribe inside ONE frame and a frame's step
-- function can name no more sources than its own syntax holds.
-- Mint-Loop-Probe's MEASUREMENT 6 computes the coordinate directly — the
-- fibre of a pre-state class — and gets 4 against a cSize of 3 on the
-- lean two-level ladder and 8 against 3 on the lean three-level one.
-- The lean families exist for exactly this: they keep the delivery
-- structure and shrink the syntax the cap is read off.
--
-- SO BOTH COORDINATES RANGE OVER SUBSETS OF THE ENTRY REGISTRY.  A
-- delivery is determined by the pre-state registrations it visits
-- together with the pre-state registrations whose dispatches minted the
-- ones it visits — every mint happens during some delivery and every
-- delivery bottoms out at a pre-state chain, so the second coordinate is
-- pre-state data too.  That is a story and not yet a proof: it does not
-- on its own show the recursion bottoms out.  It gives
--
--     deliveries ≤ 2 ^ cReg * 2 ^ cReg    frames per delivery ≤ cSize
--
-- and the count is their product: `2 ^ cReg * 2 ^ cReg * cSize`.
-- MEASUREMENT 6 gates both coordinates (22 against 128, 13 against 32)
-- and MEASUREMENT 5 gates the product against j itself.
--
-- The bound is over SUBSETS of registrations, not over branchings, so
-- m-ary fan-in does not beat it: extra fan-in only adds edges, and the
-- transitive tournament already has them all.
--
-- WHEN THE FIRST COORDINATE IS PROVEN RATHER THAN GATED, the lemma to
-- reach for is the INVERTED PAIR, not "one per subset" — the latter is
-- the corollary.  The injection is `paths ↪ subsets`, sending a path to
-- the SET of registrations it visits, and what has to be shown is that
-- the map is injective: two distinct traversals of the SAME set would
-- have to disagree on the order of some pair, and a pair inverted between
-- two reachability-respecting orders is a cycle, which the DAG forbids.
-- Note the nodes are the REGISTRATIONS, not the slots — `merge(s1, s1)`
-- registers twice on one slot and so contributes two nodes — which is
-- why parallel fan-in never collapses into a shared node and the
-- one-per-subset count survives it.
--
-- The SECOND coordinate is the damper, and it is the one without a
-- formal counterpart, and splitting it off as its own coordinate was
-- tried and abandoned: see `cascadeGo-deliveries` below, which now
-- states the delivery bound whole.
--
-- cWid IS GONE, and it was never a factor of this count — it bounds how
-- WIDE one emitted observable is, not how many times a cascade iterates.
-- Fold-Count-Probe's diamond makes that concrete: `mWid` there is ZERO
-- while the cascade really delivers eight times, so the old product was
-- identically 0 on a program with real work to do.  The duty cWid was
-- carrying (pR vs pRs, 3 ↦ 12 against 3 ↦ 30) belongs to the per-fold
-- `foldStep` / `sizeStep` gates, which is where State-Blowup-Probe
-- checks it.
--
-- The cSize factor still reads cSize because that is where the length
-- conjunct puts it, not because a length is a size: `pathLen p ≤ᵇ cSize`
-- is a separate conjunct of the same field, and at pM 6 the two
-- genuinely differ (a 9-frame chain in a state whose largest term
-- measures 7).
--
-- STILL INSIDE THE ROUND-5 GATE: the count reads the Caps triple and
-- nothing else, so round3b-ledger-reset-absurd stays unavailable
frameBlowup : Caps → Caps
frameBlowup c = frameStep (2 ^ Caps.cReg c * 2 ^ Caps.cReg c * Caps.cSize c) c

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
capsAt : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → (id : ℕ) → Caps
capsAt {n = n} e sl zero =
  frameBlowup (caps (2 + sizeᵉ e + slotsSize sl)
                    (suc (pWᵉ n sl e ⊔ slotsPW n sl ⊔ slotsIW n sl))
                    (suc (sizeᵉ e + slotsSize sl)))
capsAt e sl (suc id) = frameBlowup (capsAt e sl id)

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

-- the tick endpoint, by definition rather than by arithmetic: this is
-- what makes caps-tick the j = full case of (a) rather than a
-- separate claim
frameStep-full : ∀ (c : Caps) →
  frameStep (2 ^ Caps.cReg c * 2 ^ Caps.cReg c * Caps.cSize c) c ≡ frameBlowup c
frameStep-full c = refl

-- and the recurrence's own step, so capsAt (suc id) IS the full endpoint
capsAt-suc-full : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  capsAt e sl (suc id)
    ≡ frameStep (2 ^ Caps.cReg (capsAt e sl id) * 2 ^ Caps.cReg (capsAt e sl id)
                   * Caps.cSize (capsAt e sl id))
                (capsAt e sl id)
capsAt-suc-full e sl id = refl

------------------------------------------------------------------
-- 2 ≤ cSize AT EVERY LEVEL — frameStep-mono-j's side condition, which
-- the recurrence supplies rather than assumes.  The base is `2 + …` and
-- iterSize only grows it (sizeStep is inflationary for S ≥ 1), so the
-- property is inherited by every frameBlowup
------------------------------------------------------------------

2≤frameBlowup-size : ∀ (c : Caps) → 2 ≤ Caps.cSize c → 2 ≤ Caps.cSize (frameBlowup c)
2≤frameBlowup-size c h =
  ≤-trans h (iterSize-infl (Caps.cSize c) (≤-trans (s≤s z≤n) h)
               (2 ^ Caps.cReg c * 2 ^ Caps.cReg c * Caps.cSize c) (Caps.cSize c))

2≤capsAt-size : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  2 ≤ Caps.cSize (capsAt e sl id)
2≤capsAt-size {n = n} e sl zero =
  2≤frameBlowup-size (caps (2 + sizeᵉ e + slotsSize sl) (suc (pWᵉ n sl e ⊔ slotsPW n sl))
                           (suc (sizeᵉ e + slotsSize sl)))
    (≤-trans (m≤m+n 2 (sizeᵉ e)) (m≤m+n (2 + sizeᵉ e) (slotsSize sl)))
2≤capsAt-size e sl (suc id) =
  2≤frameBlowup-size (capsAt e sl id) (2≤capsAt-size e sl id)

-- 1 ≤ cReg AT EVERY LEVEL, the registering companions' side condition,
-- and the recurrence proves it the same way: the base's cReg is a `suc`,
-- and frameBlowup's cReg is `cReg c * suc (…)`, which never drops below
-- cReg c
1≤frameBlowup-reg : ∀ (c : Caps) → 1 ≤ Caps.cReg c → 1 ≤ Caps.cReg (frameBlowup c)
1≤frameBlowup-reg c h = ≤-trans h (m≤m*n (Caps.cReg c) _)

1≤capsAt-reg : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  1 ≤ Caps.cReg (capsAt e sl id)
1≤capsAt-reg {n = n} e sl zero =
  1≤frameBlowup-reg (caps (2 + sizeᵉ e + slotsSize sl) (suc (pWᵉ n sl e ⊔ slotsPW n sl))
                          (suc (sizeᵉ e + slotsSize sl)))
    (s≤s z≤n)
1≤capsAt-reg e sl (suc id) =
  1≤frameBlowup-reg (capsAt e sl id) (1≤capsAt-reg e sl id)

------------------------------------------------------------------
-- AND THE SLOT SIDE CONDITION AT EVERY LEVEL, supplied by the
-- recurrence rather than assumed.  This is what ties `c` to `sl`: the
-- base cSize CONTAINS slotsSize as a summand, iterSize only grows it,
-- so every slot's payloads sit under every level's cSize.
------------------------------------------------------------------

cSize≤frameBlowup : ∀ (c : Caps) → 1 ≤ Caps.cSize c →
  Caps.cSize c ≤ Caps.cSize (frameBlowup c)
cSize≤frameBlowup c h =
  iterSize-infl (Caps.cSize c) h
    (2 ^ Caps.cReg c * 2 ^ Caps.cReg c * Caps.cSize c) (Caps.cSize c)

capsAt-base-size : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  2 + sizeᵉ e + slotsSize sl ≤ Caps.cSize (capsAt e sl id)
capsAt-base-size {n = n} e sl zero =
  cSize≤frameBlowup (caps (2 + sizeᵉ e + slotsSize sl)
                          (suc (pWᵉ n sl e ⊔ slotsPW n sl ⊔ slotsIW n sl))
                          (suc (sizeᵉ e + slotsSize sl)))
    (≤-trans (s≤s z≤n) (≤-trans (m≤m+n 2 (sizeᵉ e)) (m≤m+n (2 + sizeᵉ e) (slotsSize sl))))
capsAt-base-size e sl (suc id) =
  ≤-trans (capsAt-base-size e sl id)
          (cSize≤frameBlowup (capsAt e sl id)
             (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)))

-- THE TOP-LEVEL SUPPLY, the counterpart of 2≤capsAt-size and
-- 1≤capsAt-reg.  It is what the cascade face hands the tree once
-- cascadeGo-charge carries the side condition too; the companions below
-- thread it from there down to subscribeE-input-caps unchanged
-- THE WIDTH AXIS OF THE SAME SUPPLY, and the reason capsAt's base pays
-- for `slotsPW` at all: a shared slot's def is entry syntax that a
-- connect subscribes whole, so its parked bodies are as much a base
-- quantity as its size is.  iterFold only grows a width (for S ≥ 2), so
-- every level inherits the base's
cWid≤frameBlowup : ∀ (c : Caps) → 2 ≤ Caps.cSize c →
  Caps.cWid c ≤ Caps.cWid (frameBlowup c)
cWid≤frameBlowup c h =
  iterFold-infl (Caps.cSize c) h
    (2 ^ Caps.cReg c * 2 ^ Caps.cReg c * Caps.cSize c) (Caps.cWid c)

capsAt-base-wid : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  suc (pWᵉ n sl e ⊔ slotsPW n sl ⊔ slotsIW n sl) ≤ Caps.cWid (capsAt e sl id)
capsAt-base-wid {n = n} e sl zero =
  cWid≤frameBlowup (caps (2 + sizeᵉ e + slotsSize sl)
                         (suc (pWᵉ n sl e ⊔ slotsPW n sl ⊔ slotsIW n sl))
                         (suc (sizeᵉ e + slotsSize sl)))
    (≤-trans (m≤m+n 2 (sizeᵉ e)) (m≤m+n (2 + sizeᵉ e) (slotsSize sl)))
capsAt-base-wid e sl (suc id) =
  ≤-trans (capsAt-base-wid e sl id)
          (cWid≤frameBlowup (capsAt e sl id) (2≤capsAt-size e sl id))
