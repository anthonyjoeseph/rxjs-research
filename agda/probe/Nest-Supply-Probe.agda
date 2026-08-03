------------------------------------------------------------------
-- THE NEST-SUPPLY PROBE: can every member of the subscribe clique be
-- HANDED the nesting hypothesis it is about to carry?
--
-- .Caps-Nest settled the measure `M` and its steps.  The signature pass
-- now threads `M … ≤ k` through seventeen heads, and before sixty-odd
-- clause bodies are rewritten it is worth checking the thing that
-- decides whether the interface is even statable: the FRAME-SIDE
-- members do not subscribe a term the caller named.  They subscribe
-- PAYLOADS — values out of `valsCaps?`, observables out of a concat
-- queue's `obsCaps?` — so their hypothesis cannot be an argument the
-- caller supplies pointwise.  It has to be DERIVED from the caps
-- receipt those payloads already carry.
--
-- § 1  IT IS.  `valCaps?` bounds a payload's `sizeᵛ (obs u) o`, which is
--   `sizeᵉ o` definitionally, by `Caps.cSize (frameStep j c)`, which is
--   `sizeAt S j` definitionally — exactly the left summand of
--   `refresh-supplies-M`.  The right summand is the clique's own `slSz`.
--   So a payload admitted at the frame's level j has M under the k the
--   refresh installs, `suc (sizeAt S (suc j))`, with no new premise.
--
-- § 2  THE QUEUE IS THE SAME ROW through `obsCaps?`, which is
--   `valCaps?` for a bare observable.
--
-- § 3  BUT IT MUST BE DERIVED ONCE, AT THE FRAME, AND CARRIED — not
--   re-derived along the walk.  Read off `thruWalk-caps`'s recursive
--   clause rather than assumed: the tail's payload receipt is passed
--   WIDENED, `valsCaps?-widen sl (obs u) os (frameStep-⊑-+ c 2≤S j j₁)`,
--   so the level the receipt is read at GROWS down the walk.  § 1 turns
--   a receipt at level j into a bound at `suc (sizeAt S (suc j))`, so
--   re-deriving per payload would hand each one a LARGER k — while the
--   walk transformer `sIterD S W d k m J` has exactly one.  The
--   hypothesis therefore travels as `mvals?`, a bound at a FIXED k,
--   which the recursion passes through untouched.
--
--   The one thing that does drift under it is `connectedShares`, since
--   `sharedConnect` may fire between two payloads.  That is harmless in
--   the right direction: the connected set only grows, so the residue
--   only falls, and `mvals?-cons` carries the bound across.
--
-- WHAT THIS FIXES about the pass.  The hypothesis has TWO shapes, and
-- which head gets which is not a matter of taste:
--
--   · the FOUR term-subscribing heads — subscribeE, subscribeE-input,
--     sharedSlot, sharedConnect — take `M b sl cs ≤ k` on the term they
--     were handed, and step it with .Caps-Nest's edge lemmas;
--   · the WALK-CARRYING heads take `mvals?` (or its queue twin) at the
--     same fixed k and thread it unchanged;
--   · and NOBODY takes it as a premise at the frame itself.  There § 1
--     and § 2 derive it outright from `valsCaps?` / `obsCaps?` at the
--     frame's own level, against exactly the k the refresh installs,
--     with no premise beyond the `slSz` every head already carries.
--
-- That is the shape the signature pass should be written to.
------------------------------------------------------------------
module Nest-Supply-Probe where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat  using (ℕ; suc; _+_; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤ᵇ⇒≤)
open import Data.List using (List; []; _∷_; all)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Source)
open import Rx.Exp  using (Ctx; Closed; Val; Ty; obs; sizeᵉ; sizeᵛ)
open import Rx.Evaluator using (Slots; sizeAt; slotsSize)

open import Verify-Budget-Sufficient.Measures using (∧-true; ∧-intro; T-to)
open import Verify-Well-Formed using (≤ᵇ-true)
open import Verify-Budget-Sufficient.Caps using (Caps; frameStep)
open import Verify-Budget-Sufficient.Caps-Face
  using (valCaps?; valsCaps?; obsCaps?; valCaps?-size)
open import Verify-Budget-Sufficient.Caps-Nest
  using (M; refresh-supplies-M; M-cons)

------------------------------------------------------------------
-- § 1.  A PAYLOAD VALUE, ADMITTED AT THE FRAME'S LEVEL, HAS M UNDER
-- THE REFRESH'S k.  Note both reductions are definitional:
-- `sizeᵛ (obs u) o ≡ sizeᵉ o` and
-- `Caps.cSize (frameStep j c) ≡ sizeAt (Caps.cSize c) j`
------------------------------------------------------------------

size-obs : ∀ {n} {Γ : Ctx n} {u} (o : Val Γ (obs u)) → sizeᵛ (obs u) o ≡ sizeᵉ o
size-obs o = refl

frameStep-size : ∀ (c : Caps) (j : ℕ) →
  Caps.cSize (frameStep j c) ≡ sizeAt (Caps.cSize c) j
frameStep-size c j = refl

valCaps→M : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (cs : List Source) (o : Val Γ (obs u)) →
  1 ≤ Caps.cSize c →
  slotsSize sl ≤ Caps.cSize c →
  valCaps? (frameStep j c) sl (obs u) o ≡ true →
  M o sl cs ≤ suc (sizeAt (Caps.cSize c) (suc j))
valCaps→M {u = u} c j sl cs o 1≤S hsl hv =
  refresh-supplies-M (Caps.cSize c) j o sl cs 1≤S
    (≤ᵇ⇒≤ (sizeᵉ o) (sizeAt (Caps.cSize c) j)
          (T-to (valCaps?-size (frameStep j c) sl (obs u) o hv)))
    hsl

------------------------------------------------------------------
-- § 2.  A QUEUED OBSERVABLE, through the predicate concatDrain reads
------------------------------------------------------------------

obsCaps→M : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (cs : List Source) (o : Closed Γ s) →
  1 ≤ Caps.cSize c →
  slotsSize sl ≤ Caps.cSize c →
  obsCaps? (frameStep j c) sl o ≡ true →
  M o sl cs ≤ suc (sizeAt (Caps.cSize c) (suc j))
obsCaps→M {n = n} c j sl cs o 1≤S hsl ho =
  refresh-supplies-M (Caps.cSize c) j o sl cs 1≤S
    (≤ᵇ⇒≤ (sizeᵉ o) (sizeAt (Caps.cSize c) j)
          (T-to (proj₁ (∧-true (sizeᵉ o ≤ᵇ Caps.cSize (frameStep j c)) _ ho))))
    hsl

------------------------------------------------------------------
-- § 3.  AND A WHOLE PAYLOAD LIST, which is the shape a walk carries.
-- `mOK?` / `mvals?` below are the predicate the signature pass adds;
-- stated here in the `all` style the rest of the face uses so a walk's
-- premise is one Bool, not a quantified family
------------------------------------------------------------------

mOK? : ∀ {n} {Γ : Ctx n} {u} → ℕ → Slots Γ → List Source → Val Γ (obs u) → Bool
mOK? k sl cs o = M o sl cs ≤ᵇ k

mvals? : ∀ {n} {Γ : Ctx n} {u} →
  ℕ → Slots Γ → List Source → List (Val Γ (obs u)) → Bool
mvals? k sl cs vs = all (mOK? k sl cs) vs

-- and the carry: a connect during the walk only lowers the residue, so
-- a bound established at frame entry survives it
mvals?-cons : ∀ {n} {Γ : Ctx n} {u} (k : ℕ) (sl : Slots Γ) (cs : List Source)
  (s : Source) (vs : List (Val Γ (obs u))) →
  mvals? k sl cs vs ≡ true → mvals? k sl (s ∷ cs) vs ≡ true
mvals?-cons k sl cs s []       h = refl
mvals?-cons k sl cs s (o ∷ vs) h with ∧-true (mOK? k sl cs o) (mvals? k sl cs vs) h
... | h₁ , h₂ =
  ∧-intro (≤ᵇ-true (M o sl (s ∷ cs)) k
            (M-cons o sl cs s k (≤ᵇ⇒≤ (M o sl cs) k (T-to h₁))))
          (mvals?-cons k sl cs s vs h₂)
