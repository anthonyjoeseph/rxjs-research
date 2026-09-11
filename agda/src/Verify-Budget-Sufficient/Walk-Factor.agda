-- THE WALK'S OWN FACTOR, kept apart from the delivery face's.  Both
-- price a path by what its frames can do to a value and they agree at
-- every frame but one, so the temptation is to share the definition --
-- and the reason not to is that the delivery face sits UNDER the
-- widest module in this tower, which would then rebuild whenever the
-- walk's currency moved.  A separate module is what keeps the walk's
-- repairs cheap.
module Verify-Budget-Sufficient.Walk-Factor where

open import Data.Bool using (Bool; true; _∧_)
open import Data.Nat using (ℕ; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s; _≤ᵇ_)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; ≤ᵇ⇒≤; ≤⇒≤ᵇ; +-mono-≤; +-monoˡ-≤; +-assoc; *-monoˡ-≤;
  *-identityˡ; *-distribʳ-+; m≤m+n; m≤n+m; m^n>0; ^-distribˡ-+-*; ^-monoʳ-≤; ^-*-assoc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Rx.Exp using (Ctx; sizeᵗ)
open import Rx.Nest-Depth using (nestDᵗ)
open import Verify-Budget-Sufficient.Nest-Depth-Size using (nestDᵗ≤sizeᵗ)
open import Rx.Evaluator using
  (Frame; map-f; scan-f; take-f; from-inner; thru-outer; Path; root; share-sink; _↠_)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (frameSz?; pathSz?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using (pathSz?-len)
open import Verify-Budget-Sufficient.Measures using (pathLen; ∧-true)
open import Decide using (T-to; T⇒≡true; ∧-intro; ∧-trueˡ; ∧-trueʳ)

-- AND THE WALK NEEDS A LARGER ONE AT EXACTLY TWO FRAMES.  `frameNestF`
-- prices a frame by the term IT carries, which is right for delivery
-- and wrong for the walk: a `thru-outer` carries no term and yet
-- SUBSCRIBES what it is handed, so the value that comes back has been
-- evaluated and substitution is multiplicative.  The factor that pays
-- for it cannot come from the frame's own syntax, so it comes from the
-- instant's SIZE CAP -- which is the one quantity bounding the arrival
-- whose term the subscription runs, and which the walk's `pathSz?`
-- premise already carries.
--
-- REFUTED: `Refuted.Thru-Subscribe-Nest` is why the extra factor is
--   here at all -- eighty against forty-one at the unindexed reading,
--   with the arrival's depth a free parameter of the witness.

-- AND THE SECOND IS THE FOLD, WHICH IS PRICED PER VALUE IN THE BURST
-- RATHER THAN ONCE.  A map frame substitutes into what it is handed,
-- so one power of its step function pays for the whole burst; a scan
-- frame THREADS, so its k-th output is the step function applied k
-- times in sequence and the charge is a POWER in the count.  Pricing
-- it once left the premise constant in a count the conclusion is
-- exponential in, and the count is bounded by nothing the frame's own
-- syntax says -- so the exponent comes from the same place the outer
-- frame's does, the instant's size cap, which is the one quantity
-- bounding how wide a burst the invariant admits.  The successor is
-- what pays the burst's own additive share of the step function's
-- nesting, one summand per value folded in.
frameΦF : ∀ {n} {Γ : Ctx n} {s u} (B : ℕ) → Frame Γ s u → ℕ
frameΦF B (map-f f)          = 2 ^ sizeᵗ f
frameΦF B (scan-f f _)       = (2 ^ suc (sizeᵗ f)) ^ B
frameΦF B (take-f _)         = 1
frameΦF B (from-inner _ _ _) = 1
frameΦF B (thru-outer _ _)   = 2 ^ B

frameΦSz : ∀ {n} {Γ : Ctx n} {s u} (B : ℕ) → Frame Γ s u → ℕ
frameΦSz B (map-f f)          = sizeᵗ f
frameΦSz B (scan-f f _)       = suc (sizeᵗ f) * B
frameΦSz B (take-f _)         = 0
frameΦSz B (from-inner _ _ _) = 0
frameΦSz B (thru-outer _ _)   = B

-- AND A SINK LEAF CARRIES THE WORST ADMITTED CHAIN, which is the one
-- clause here that is not a reading of a frame.  A sink is where the
-- walk hands its values to paths held in the registry, and the receipt
-- it spends has to be one those paths can be charged against: at a
-- factor of one it says only that the values are shallow, while an
-- admitted chain is owed its own factor and its own depth.  Both are
-- bounded where the hand-over stands -- a chain's factor by the cap
-- below and its depth by the size legality the registry carries -- so
-- the leaf is priced at those bounds rather than at nothing, and the
-- fan-out becomes a monotonicity step instead of a missing relation.

-- AND THE BOUNDS IT IS PRICED AT ARE THE WALK'S, NEVER THE REGISTRY'S,
-- WHICH IS WHAT MAKES A FAN-OUT'S RECEIPT UNSPENDABLE RATHER THAN
-- MISSING.  A registered chain does not fit the cap the walk carries:
-- a subscribing frame swaps its head for a `from-inner` and pushes one
-- frame per operator of the inner, so what lands in the registry is
-- LONGER than what was walked and no fixed cap prices it --
-- `Refuted.Chain-Step-Regs-Cap` kills that reading outright.  What the
-- registry does carry instead is a receipt at the STEPPED cap, and
-- reading this leaf there is unavailable in both directions the
-- pricing can move.

-- MOVING THE WHOLE FACE to the stepped instant trades the depth budget
-- for one nothing supplies: every frame arm spends the tie between the
-- potential and `capsH` at the instant being WALKED, and the descent's
-- depth readings are that instant's.  MOVING THE LEAF ALONE asks this
-- charge -- two to a cube of what it reads -- to fit under a budget
-- that same tie holds beneath that instant's own `capsH`, while the
-- stepped cap is `frameBlowup` OF that very `capsH`.  So the caps
-- recurrence forbids it by construction rather than by a margin: the
-- quantity the leaf would read is built by iterating on the quantity
-- it must fit under, and no program makes that ordering the other way.

-- AND THE ONE PARAMETER IS SERVING TWO DIFFERENT OBJECTS, WHICH IS
-- WHERE THE DEAD CAP READINGS COME FROM.  Two of the clauses here are
-- priced at a cap because the thing they charge for is the ARRIVAL --
-- the subscribing frame runs a term the walk was handed, and the sink
-- leaf carries a chain the walk hands values to.  The arrival is
-- instant-constant: the descent's premise bounds it by the cap at the
-- instant's ENTRY and nothing in the climb moves it.  The remaining
-- clauses are not charges for an arrival at all; they read a cap only
-- because a registry entry's legality is stated at whichever cap that
-- entry was admitted under, and THAT one climbs with the walk.  So a
-- single parameter is asked to be the entry cap and the climbed cap at
-- once, and every reading of it is chosen for both jobs -- which is
-- the shape the four dead readings share, stated at the pricing rather
-- than at any endpoint.
--
-- AND THE DEPTH DIMENSION IS THE WORKED INSTANCE OF THE SPLIT, WHICH
-- IS WHY IT NEVER HAD THIS PROBLEM.  Its registry potential is a fold
-- of a cap-free per-path measure, and its receipt is one conjunct
-- indexed by the instant alone; there is no cap in the potential for a
-- climb to move.  The map clause here is already that shape -- priced
-- by its own operator's syntax and cap-free -- so the split to test is
-- not a better cap but TWO parameters: an arrival charge, constant at
-- the entry cap for the whole instant, and a frame receipt free to
-- climb with the entry it is stated over.  What the split may NOT do
-- is re-denominate the subscribing frame by its own syntax, which is
-- refuted above; the arrival is what that refutation leaves standing,
-- and it is a different quantity from the cap the receipt names.

-- SO THIS LEAF'S CAP IS A WALK QUANTITY PERMANENTLY, and a chain the
-- fan-out hands values to is priced by this clause or by a mechanism
-- that does not price it at a cap at all.  That is the obligation
-- `pathSz?`'s own header states over its two callers, arriving at the
-- potential rather than at the size predicate.

-- AND THE LEAF'S PRICE IS FLAT IN THE REMAINING SHARE DEPTH, WHICH IS
-- A DEFECT NO CHOICE OF CAP REPAIRS.  The number it charges is exactly
-- one chain-length of frame factor -- the longest frame factor the
-- size predicate admits, raised to the length that predicate admits --
-- so it dominates a registered chain whose own terminal is ROOT and
-- nothing more.  A chain terminating at a SECOND sink carries that
-- same leaf price UNDER its own frames, so dominating it asks a
-- constant to exceed itself times a frame product, which no constant
-- does.  That is the structural reading of `Refuted.Sink-Phi-Leaf`,
-- whose witness quantifies the budget rather than exhibiting a deep
-- share: the leaf fails at one generation of nesting, not at some
-- adversarial arithmetic.
--
-- AND ENLARGING IT IS SELF-DEFEATING RATHER THAN MERELY EXPENSIVE,
-- because the ceiling that reads this price is stated as a power of
-- the same exponent: raising the leaf raises the length bound every
-- consumer spends by the identical amount, so the gap between a chain
-- and the price meant to cover it is invariant under the move.  The
-- repair the two together leave standing is to index the charge by
-- the CLIMB -- the share depth still ahead of the walk -- so that a
-- sink's price strictly exceeds what its own registered chains cost
-- by construction, in the way a decreasing measure does and a
-- constant cannot.
pathΦF : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) → Path Γ s t → ℕ
pathΦF B root           = 1
pathΦF B (share-sink _) = 2 ^ ((B + B) * (suc B * B))
pathΦF B (f ↠ p)        = frameΦF B f * pathΦF B p

pathΦSz : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) → Path Γ s t → ℕ
pathΦSz B root           = 0
pathΦSz B (share-sink _) = (B + B) * (suc B * B)
pathΦSz B (f ↠ p)        = frameΦSz B f + pathΦSz B p

-- THE DEPTH HALF, AND IT IS SEPARATE FROM THE STORE FACE'S BECAUSE ONLY
-- THIS ONE READS A CAP.  `pathNestD` prices the syntax a path installs
-- and needs no cap to do it; the sink leaf's charge is a BOUND on
-- something else's syntax, so it cannot be stated there.  Every other
-- clause is the same step, which is what makes the walk's proofs carry
-- over unchanged -- they use the frame equation and treat the tail as
-- opaque.
pathΦD : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) → Path Γ s t → ℕ
pathΦD B root                    = 0
pathΦD B (share-sink _)          = (B + B) * B
pathΦD B (map-f f ↠ p)           = nestDᵗ f + pathΦD B p
pathΦD B (scan-f f _ ↠ p)        = nestDᵗ f + pathΦD B p
pathΦD B (take-f _ ↠ p)          = pathΦD B p
pathΦD B (from-inner _ _ _ ↠ p)  = pathΦD B p
pathΦD B (thru-outer _ _ ↠ p)    = suc (pathΦD B p)

pathΦF≡ : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  pathΦF B p ≡ 2 ^ pathΦSz B p
pathΦF≡ B root           = refl
pathΦF≡ B (share-sink _) = refl
pathΦF≡ B (map-f f ↠ p) =
  trans (cong (2 ^ sizeᵗ f *_) (pathΦF≡ B p))
        (sym (^-distribˡ-+-* 2 (sizeᵗ f) (pathΦSz B p)))
pathΦF≡ B (scan-f f _ ↠ p) =
  trans (cong ((2 ^ suc (sizeᵗ f)) ^ B *_) (pathΦF≡ B p))
        (trans (cong (_* (2 ^ pathΦSz B p)) (^-*-assoc 2 (suc (sizeᵗ f)) B))
               (sym (^-distribˡ-+-* 2 (suc (sizeᵗ f) * B) (pathΦSz B p))))
pathΦF≡ B (take-f _ ↠ p)         = trans (*-identityˡ (pathΦF B p)) (pathΦF≡ B p)
pathΦF≡ B (from-inner _ _ _ ↠ p) = trans (*-identityˡ (pathΦF B p)) (pathΦF≡ B p)
pathΦF≡ B (thru-outer _ _ ↠ p) =
  trans (cong (2 ^ B *_) (pathΦF≡ B p))
        (sym (^-distribˡ-+-* 2 B (pathΦSz B p)))

-- AND THE FACTOR IS NEVER ZERO, which is what lets a bound stated at a
-- frame's own arithmetic be read against the potential the path is
-- charged in: the potential is that arithmetic TIMES this factor, so a
-- consumer holding the unfactored quantity needs the factor to be at
-- least one before it may spend the premise.  It is a corollary of the
-- equation above rather than an induction of its own -- every clause is
-- a power of two, and the root's `1` is the same reading at exponent
-- zero.
pathΦF-pos : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  1 ≤ pathΦF B p
pathΦF-pos B p =
  ≤-trans (m^n>0 2 (pathΦSz B p)) (≤-reflexive (sym (pathΦF≡ B p)))

-- THE HALF OF A SIZE RECEIPT THE PRICING ACTUALLY SPENDS, SPLIT OFF
-- FROM THE HALF IT CANNOT HAVE.  A size receipt bundles two unrelated
-- obligations: every frame's own syntax under the cap, and the whole
-- chain's LENGTH under it too.  The pricing below needs both, and only
-- the first is true of a chain the registry holds -- a subscribing
-- frame swaps its head for a `from-inner` and pushes one frame per
-- operator of the inner, so each new frame's syntax is a piece of an
-- inner the arrival premise already bounds by the cap, while the COUNT
-- of them is the inner's operator count added to what was walked.
-- Splitting the reading is what lets the length be paid somewhere
-- else; nothing here decides where.
--
-- REFUTED: `Refuted.Chain-Step-Regs-Cap`, which is the length half and
--   not this one -- a registered chain runs to nearly twice the cap it
--   entered on, and the frame half survives that witness untouched.
pathFrameSz? : ∀ {n} {Γ : Ctx n} {s t} → ℕ → Path Γ s t → Bool
pathFrameSz? B root           = true
pathFrameSz? B (share-sink _) = true
pathFrameSz? B (f ↠ p)        = frameSz? B f ∧ pathFrameSz? B p

pathSz?-frames : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  pathSz? B p ≡ true → pathFrameSz? B p ≡ true
pathSz?-frames B root           h = refl
pathSz?-frames B (share-sink _) h = refl
pathSz?-frames B (f ↠ p) h
  with ∧-true (frameSz? B f) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) h
... | hf , hr with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) hr
...   | _ , hp = ∧-intro hf (pathSz?-frames B p hp)

-- THE READING THE Φ FACE TAKES, WHICH IS THE SPLIT ABOVE PACKED BACK
-- INTO ONE PREDICATE AT A BUDGET THAT IS NOT THE CAP.  Splitting the
-- size receipt buys the pricing a length it can pay somewhere else;
-- packing the two back together at a FIXED budget is what keeps that
-- purchase from costing every statement in the face an extra index.
-- The budget is twice the cap because that is what the walk's own
-- charge affords.  It is NOT a length a registered chain is known to
-- stay under: `Refuted.Fan-Regs-Packed-Len` mints one at fifteen
-- frames against a doubled budget of twelve, by pushing one frame per
-- operator of an inner that the receipt in hand prices at the STEPPED
-- cap.  So the budget is a figure about what can be PAID, and any
-- statement asking for it at the ENTRY cap is asking for something the
-- mint does not supply -- which is a fact about where such a reading
-- may be taken, not about this predicate.
--
-- AND THE WALKED READING IMPLIES IT, so nothing that already holds a
-- size receipt has to acquire anything: a chain the walk priced is
-- under the cap once, which is under the cap twice.  That is what
-- makes this a widening of the premise rather than a new obligation,
-- and it is why the face may take it without any producer changing.
pathSzL? : ∀ {n} {Γ : Ctx n} {s t} → ℕ → Path Γ s t → Bool
pathSzL? B p = pathFrameSz? B p ∧ (pathLen p ≤ᵇ B + B)

pathSzL?-frames : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  pathSzL? B p ≡ true → pathFrameSz? B p ≡ true
pathSzL?-frames B p h = ∧-trueˡ h

pathSzL?-len : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  pathSzL? B p ≡ true → pathLen p ≤ B + B
pathSzL?-len B p h = ≤ᵇ⇒≤ (pathLen p) (B + B) (T-to (∧-trueʳ {a = pathFrameSz? B p} h))

pathSz?-szL : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  pathSz? B p ≡ true → pathSzL? B p ≡ true
pathSz?-szL B p h =
  ∧-intro (pathSz?-frames B p h)
          (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (pathSz?-len B p h) (m≤m+n B B))))

-- AND EVERY FRAME'S EXPONENT IS UNDER THE FOLD'S, which is what keeps
-- the whole path under a single power: the burst factor is the largest
-- a frame can surrender, so a path of legal length pays at most its
-- length times that one reading and the cap below is a cube rather
-- than a square.
frameΦSz≤ : ∀ {n} {Γ : Ctx n} {s u} (B : ℕ) (f : Frame Γ s u) →
  frameSz? B f ≡ true → frameΦSz B f ≤ suc B * B
frameΦSz≤ B (map-f fn)         h = ≤-trans (≤ᵇ⇒≤ (sizeᵗ fn) B (T-to h))
                                           (m≤m+n B (B * B))
frameΦSz≤ B (scan-f fn _)      h = *-monoˡ-≤ B (s≤s (≤ᵇ⇒≤ (sizeᵗ fn) B (T-to h)))
frameΦSz≤ B (take-f _)         h = z≤n
frameΦSz≤ B (from-inner _ _ _) h = z≤n
frameΦSz≤ B (thru-outer _ _)   h = m≤m+n B (B * B)

-- AND THE CAP IS NOW TWO OF THEM, which is what a sink leaf costs: a
-- path pays its own length in frame readings and, if it ends at a
-- hand-over rather than at the root, one more whole cap for the chain
-- it hands to.  Nothing else moves -- the length half is the same sum
-- it always was, and the leaf's share is a constant the recursion never
-- touches.
--
-- AND THE PREMISE IS THE FRAME HALF ALONE, WHICH IS THE WHOLE POINT OF
-- SPLITTING IT.  The length appears in the CONCLUSION here, as the
-- chain's own `pathLen`, so nothing is owed about it -- what the
-- induction spends at each frame is that frame's syntax and nothing
-- else.  Collapsing the length to the cap is a separate step, and the
-- caps below are where it happens.
pathΦSz-len : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  pathFrameSz? B p ≡ true →
  pathΦSz B p ≤ pathLen p * (suc B * B) + (B + B) * (suc B * B)
pathΦSz-len B root           h = z≤n
pathΦSz-len B (share-sink _) h = ≤-refl
pathΦSz-len B (f ↠ p) h
  with ∧-true (frameSz? B f) (pathFrameSz? B p) h
... | hf , hp =
        ≤-trans (+-mono-≤ (frameΦSz≤ B f hf) (pathΦSz-len B p hp))
                (≤-reflexive (sym (+-assoc (suc B * B)
                                           (pathLen p * (suc B * B))
                                           ((B + B) * (suc B * B)))))

-- AND THE LENGTH IS A SEPARATE BUDGET FROM THE CAP, which is the only
-- thing a registered chain can be held to: the frame half is a piece
-- of an inner the arrival premise already bounds, while the count of
-- frames is whatever the subscription pushed on top.  So the cap `B`
-- prices each frame and a second budget `L` counts them, and the two
-- coincide only where the chain was never stepped through.  Whoever
-- can pay a length says so here; nothing in this module can.
--
-- AND THE LEAF'S SHARE DOES NOT MOVE WITH THE LENGTH, which is what
-- makes a length budget affordable at all.  The `B` in the second
-- summand is the sink leaf's own charge, a constant the recursion
-- never touches, so a chain held to a length of `k` caps rather than
-- one pays `2 ^ ((k + 1) * B * (suc B * B))` -- the entry cap raised
-- to a power of `k + 1`, and not an exponential in a stepped cap,
-- which is what a size receipt taken after a step would have cost.
-- At the near-twice-the-cap the registry actually admits that is a
-- cube.  Whether the budget affords a cube is the consumer's
-- question, and it is a question about a fixed power.
pathΦF-cap-atLen : ∀ {n} {Γ : Ctx n} {s t} (B L : ℕ) (p : Path Γ s t) →
  pathFrameSz? B p ≡ true → pathLen p ≤ L →
  pathΦF B p ≤ 2 ^ ((L + (B + B)) * (suc B * B))
pathΦF-cap-atLen B L p h hl =
  ≤-trans (≤-reflexive (pathΦF≡ B p))
          (^-monoʳ-≤ 2
            (≤-trans (pathΦSz-len B p h)
              (≤-trans (+-monoˡ-≤ ((B + B) * (suc B * B))
                         (*-monoˡ-≤ (suc B * B) hl))
                       (≤-reflexive
                         (sym (*-distribʳ-+ (suc B * B) L (B + B)))))))

-- THE DEPTH HALF'S OWN CAP, and it is a square rather than a cube: a
-- frame installs a step function's nesting and a `thru-outer` one unit,
-- both under the size cap, so a legal path's depth is its length times
-- that cap -- plus, at a hand-over, the square the chain it hands to is
-- owed.
pathΦD-len : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  1 ≤ B → pathFrameSz? B p ≡ true → pathΦD B p ≤ pathLen p * B + (B + B) * B
pathΦD-len B root           _  h = z≤n
pathΦD-len B (share-sink _) _  h = ≤-refl
pathΦD-len B (map-f fn ↠ p) 1B h
  with ∧-true (frameSz? B (map-f fn)) (pathFrameSz? B p) h
... | hf , hp =
        ≤-trans (+-mono-≤ (≤-trans (nestDᵗ≤sizeᵗ fn) (≤ᵇ⇒≤ (sizeᵗ fn) B (T-to hf)))
                          (pathΦD-len B p 1B hp))
                (≤-reflexive (sym (+-assoc B (pathLen p * B) ((B + B) * B))))
pathΦD-len B (scan-f fn z ↠ p) 1B h
  with ∧-true (frameSz? B (scan-f fn z)) (pathFrameSz? B p) h
... | hf , hp =
        ≤-trans (+-mono-≤ (≤-trans (nestDᵗ≤sizeᵗ fn) (≤ᵇ⇒≤ (sizeᵗ fn) B (T-to hf)))
                          (pathΦD-len B p 1B hp))
                (≤-reflexive (sym (+-assoc B (pathLen p * B) ((B + B) * B))))
pathΦD-len B (take-f _ ↠ p) 1B h
  with ∧-true true (pathFrameSz? B p) h
... | _ , hp =
      ≤-trans (pathΦD-len B p 1B hp)
              (+-monoˡ-≤ ((B + B) * B) (m≤n+m (pathLen p * B) B))
pathΦD-len B (from-inner _ _ _ ↠ p) 1B h
  with ∧-true true (pathFrameSz? B p) h
... | _ , hp =
      ≤-trans (pathΦD-len B p 1B hp)
              (+-monoˡ-≤ ((B + B) * B) (m≤n+m (pathLen p * B) B))
pathΦD-len B (thru-outer _ _ ↠ p) 1B h
  with ∧-true true (pathFrameSz? B p) h
... | _ , hp =
      ≤-trans (+-mono-≤ 1B (pathΦD-len B p 1B hp))
              (≤-reflexive (sym (+-assoc B (pathLen p * B) ((B + B) * B))))
