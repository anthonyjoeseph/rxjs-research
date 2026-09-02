-- THE WALK'S OWN FACTOR, kept apart from the delivery face's.  Both
-- price a path by what its frames can do to a value and they agree at
-- every frame but one, so the temptation is to share the definition --
-- and the reason not to is that the delivery face sits UNDER the
-- widest module in this tower, which would then rebuild whenever the
-- walk's currency moved.  A separate module is what keeps the walk's
-- repairs cheap.
module Verify-Budget-Sufficient.Walk-Factor where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s; _≤ᵇ_)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; ≤ᵇ⇒≤; +-mono-≤; +-monoˡ-≤; +-assoc; *-monoˡ-≤;
   *-identityˡ; *-distribʳ-+; m≤m+n; m≤n+m; ^-distribˡ-+-*; ^-monoʳ-≤; ^-*-assoc)
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
open import Decide using (T-to)

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
pathΦF : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) → Path Γ s t → ℕ
pathΦF B root           = 1
pathΦF B (share-sink _) = 2 ^ (B * (suc B * B))
pathΦF B (f ↠ p)        = frameΦF B f * pathΦF B p

pathΦSz : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) → Path Γ s t → ℕ
pathΦSz B root           = 0
pathΦSz B (share-sink _) = B * (suc B * B)
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
pathΦD B (share-sink _)          = B * B
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
pathΦSz-len : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  pathSz? B p ≡ true →
  pathΦSz B p ≤ pathLen p * (suc B * B) + B * (suc B * B)
pathΦSz-len B root           h = z≤n
pathΦSz-len B (share-sink _) h = ≤-refl
pathΦSz-len B (f ↠ p) h
  with ∧-true (frameSz? B f) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) h
... | hf , hr with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) hr
...   | _ , hp =
        ≤-trans (+-mono-≤ (frameΦSz≤ B f hf) (pathΦSz-len B p hp))
                (≤-reflexive (sym (+-assoc (suc B * B)
                                           (pathLen p * (suc B * B))
                                           (B * (suc B * B)))))

pathΦF-cap : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  pathSz? B p ≡ true → pathΦF B p ≤ 2 ^ ((B + B) * (suc B * B))
pathΦF-cap B p h =
  ≤-trans (≤-reflexive (pathΦF≡ B p))
          (^-monoʳ-≤ 2
            (≤-trans (pathΦSz-len B p h)
              (≤-trans (+-monoˡ-≤ (B * (suc B * B))
                         (*-monoˡ-≤ (suc B * B) (pathSz?-len B p h)))
                       (≤-reflexive
                         (sym (*-distribʳ-+ (suc B * B) B B))))))

-- THE DEPTH HALF'S OWN CAP, and it is a square rather than a cube: a
-- frame installs a step function's nesting and a `thru-outer` one unit,
-- both under the size cap, so a legal path's depth is its length times
-- that cap -- plus, at a hand-over, the square the chain it hands to is
-- owed.
pathΦD-len : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  1 ≤ B → pathSz? B p ≡ true → pathΦD B p ≤ pathLen p * B + B * B
pathΦD-len B root           _  h = z≤n
pathΦD-len B (share-sink _) _  h = ≤-refl
pathΦD-len B (map-f fn ↠ p) 1B h
  with ∧-true (frameSz? B (map-f fn)) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) h
... | hf , hr with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) hr
...   | _ , hp =
        ≤-trans (+-mono-≤ (≤-trans (nestDᵗ≤sizeᵗ fn) (≤ᵇ⇒≤ (sizeᵗ fn) B (T-to hf)))
                          (pathΦD-len B p 1B hp))
                (≤-reflexive (sym (+-assoc B (pathLen p * B) (B * B))))
pathΦD-len B (scan-f fn z ↠ p) 1B h
  with ∧-true (frameSz? B (scan-f fn z)) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) h
... | hf , hr with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) hr
...   | _ , hp =
        ≤-trans (+-mono-≤ (≤-trans (nestDᵗ≤sizeᵗ fn) (≤ᵇ⇒≤ (sizeᵗ fn) B (T-to hf)))
                          (pathΦD-len B p 1B hp))
                (≤-reflexive (sym (+-assoc B (pathLen p * B) (B * B))))
pathΦD-len B (take-f _ ↠ p) 1B h
  with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) h
... | _ , hp =
      ≤-trans (pathΦD-len B p 1B hp)
              (+-monoˡ-≤ (B * B) (m≤n+m (pathLen p * B) B))
pathΦD-len B (from-inner _ _ _ ↠ p) 1B h
  with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) h
... | _ , hp =
      ≤-trans (pathΦD-len B p 1B hp)
              (+-monoˡ-≤ (B * B) (m≤n+m (pathLen p * B) B))
pathΦD-len B (thru-outer _ _ ↠ p) 1B h
  with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) h
... | _ , hp =
      ≤-trans (+-mono-≤ 1B (pathΦD-len B p 1B hp))
              (≤-reflexive (sym (+-assoc B (pathLen p * B) (B * B))))

-- AND A CHAIN THAT ENDS AT THE ROOT PAYS ONLY THE LENGTH HALF, which is
-- what lets a hand-over's price cover it.  A path carries exactly one
-- leaf, so this decides which of the two shares above is present -- and
-- where it answers root, both caps shed the leaf's constant and land on
-- exactly the two quantities a sink is charged.
pathRoots : ∀ {n} {Γ : Ctx n} {s t} → Path Γ s t → Bool
pathRoots root           = true
pathRoots (share-sink _) = false
pathRoots (_ ↠ p)        = pathRoots p

pathΦSz-root : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  pathRoots p ≡ true → pathSz? B p ≡ true →
  pathΦSz B p ≤ pathLen p * (suc B * B)
pathΦSz-root B root           _  _ = z≤n
pathΦSz-root B (share-sink _) () _
pathΦSz-root B (f ↠ p) hr h
  with ∧-true (frameSz? B f) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) h
... | hf , hrr with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) hrr
...   | _ , hp = +-mono-≤ (frameΦSz≤ B f hf) (pathΦSz-root B p hr hp)

pathΦF-cap-root : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  pathRoots p ≡ true → pathSz? B p ≡ true →
  pathΦF B p ≤ 2 ^ (B * (suc B * B))
pathΦF-cap-root B p hr h =
  ≤-trans (≤-reflexive (pathΦF≡ B p))
          (^-monoʳ-≤ 2 (≤-trans (pathΦSz-root B p hr h)
                                (*-monoˡ-≤ (suc B * B) (pathSz?-len B p h))))

pathΦD-root : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  1 ≤ B → pathRoots p ≡ true → pathSz? B p ≡ true →
  pathΦD B p ≤ pathLen p * B
pathΦD-root B root           _  _  _ = z≤n
pathΦD-root B (share-sink _) _  () _
pathΦD-root B (map-f fn ↠ p) 1B hr h
  with ∧-true (frameSz? B (map-f fn)) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) h
... | hf , hrr with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) hrr
...   | _ , hp = +-mono-≤ (≤-trans (nestDᵗ≤sizeᵗ fn) (≤ᵇ⇒≤ (sizeᵗ fn) B (T-to hf)))
                          (pathΦD-root B p 1B hr hp)
pathΦD-root B (scan-f fn z ↠ p) 1B hr h
  with ∧-true (frameSz? B (scan-f fn z)) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) h
... | hf , hrr with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) hrr
...   | _ , hp = +-mono-≤ (≤-trans (nestDᵗ≤sizeᵗ fn) (≤ᵇ⇒≤ (sizeᵗ fn) B (T-to hf)))
                          (pathΦD-root B p 1B hr hp)
pathΦD-root B (take-f _ ↠ p) 1B hr h
  with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) h
... | _ , hp = ≤-trans (pathΦD-root B p 1B hr hp) (m≤n+m (pathLen p * B) B)
pathΦD-root B (from-inner _ _ _ ↠ p) 1B hr h
  with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) h
... | _ , hp = ≤-trans (pathΦD-root B p 1B hr hp) (m≤n+m (pathLen p * B) B)
pathΦD-root B (thru-outer _ _ ↠ p) 1B hr h
  with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) h
... | _ , hp = +-mono-≤ 1B (pathΦD-root B p 1B hr hp)

pathΦD-cap-root : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  1 ≤ B → pathRoots p ≡ true → pathSz? B p ≡ true → pathΦD B p ≤ B * B
pathΦD-cap-root B p 1B hr h =
  ≤-trans (pathΦD-root B p 1B hr h) (*-monoˡ-≤ B (pathSz?-len B p h))
