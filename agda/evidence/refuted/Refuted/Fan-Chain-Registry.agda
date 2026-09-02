-- ══════════════════════════════════════════════════════════════════
-- WHAT A SHARE'S FAN-OUT MAY ASSUME ABOUT THE CHAINS IT IS HANDED,
-- and the answer is NOTHING, because it is handed whatever the
-- registry holds and the registry is a field of an arbitrary state.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE TWO STATEMENTS SAY.  The fan-out walks `shareAdmit`'s
-- snapshot and needs two receipts per admitted chain: that it is
-- SIZE-LEGAL at the program's cap, and that its NESTING is under the
-- syntactic unit.  Both were stated over a universally quantified
-- state with no premise on its registry at all, so both quantify over
-- registries that no run could produce alongside ones that every run
-- does.  That is what makes them refutable rather than merely hard.
-- ══════════════════════════════════════════════════════════════════

-- AND THE FILTER IS NOT WHERE THE CONTENT IS, which is the part worth
-- carrying away: `shareAdmit` selects on the source and the element
-- type and never reads a path, so it can only pass a receipt along,
-- never establish one.  Both liftings across it are already proven in
-- `src` -- a size one from the registry's own size receipt and a
-- depth one from the registry's depth maximum -- so what these two
-- statements were carrying was never the fan-out's obligation.  It is
-- the REGISTRY's, and it belongs at whatever mints a registration.

-- SO THE WITNESSES REGISTER, RATHER THAN CONSTRUCTING A STATE.  Each
-- one is `register` applied to `st-init`, which is the only way into
-- the registry the evaluator has, and the chain each registers is an
-- ordinary path built from ordinary frames.  Nothing here is a
-- hand-built record, so neither refutation turns on a state shape the
-- interface would not admit.
module Refuted.Fan-Chain-Registry where

open import Data.Bool using (true)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤ᵇ_)
open import Data.Nat.Properties using (1+n≰n; ⊔-identityʳ)
open import Data.Product using (proj₂; _,_)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; subst)

open import Rx.Prim using (hot)
open import Rx.Exp using (Ctx; Closed; Exp; Fn; natᵗ; obs; emptyᵉ; mergeAllᵉ;
  ofᵉ; strmᵗ)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (Path; _↠_; root; map-f; take-f; thru-outer;
  mergeAllᵒ; EvalSt; register; st-init; shareAdmit)
open import Verify-Budget-Sufficient.Measures using (pathLen)
open import Verify-Budget-Sufficient.Nest-Store using (pathNestD; nestUnit)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (pathSz?; regsSz?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using (pathSz?-len)
open import Verify-Budget-Sufficient.Caps using (Caps; capsAt)
open import Verify-Budget-Sufficient.Delivery-Walk using (regP?)
open import Decide using (∧-trueˡ)

----------------------------------------------------------------------
-- THE STATEMENTS, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulates would prove the tower inconsistent instead of refuting
-- anything.  The depth one is transcribed exactly, since every
-- quantity in its conclusion computes at a concrete program; the size
-- one has its cap replaced by an ABSTRACT bound, because `capsAt`
-- returns at no program, and the refutation below is then stronger
-- than the original rather than weaker -- it crosses at every bound,
-- so whatever the cap is, a registration outruns it.
----------------------------------------------------------------------
FanChainSz : Set
FanChainSz = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (B : ℕ) (i : Fin n) (st : EvalSt e) →
  all (λ rp → pathSz? B (proj₂ rp))
      (shareAdmit {t = t} i (EvalSt.registry st)) ≡ true

FanChainNestD : Set
FanChainNestD = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (i : Fin n) (st : EvalSt e) →
  all (λ rp → pathNestD (proj₂ rp) ≤ᵇ nestUnit e sl)
      (shareAdmit {t = t} i (EvalSt.registry st)) ≡ true

----------------------------------------------------------------------
-- THE SMALLEST PROGRAM THAT HAS A SHARE TO FAN OUT FROM: one slot,
-- scripted, and an empty definition.  Both measures bottom out here
-- -- the unit is one and the slot sum is zero -- so every figure
-- below is the chain's own and none of it is context.
----------------------------------------------------------------------
Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

sl₁ : Slots Γ₁
sl₁ fzero = scripted (hot [])

e₀ : Closed Γ₁ natᵗ
e₀ = emptyᵉ

unit≡ : nestUnit e₀ sl₁ ≡ 1
unit≡ = refl

----------------------------------------------------------------------
-- THE SIZE WITNESS: a chain of `take` frames one longer than the
-- bound.  `take-f` is size-free, so no frame of it is ever the thing
-- that fails -- what fails is the LENGTH conjunct, which is the
-- quantity `shareAdmit` cannot see and the registry does not carry.
----------------------------------------------------------------------
takes : ℕ → Path Γ₁ natᵗ natᵗ
takes zero    = root
takes (suc k) = take-f 0 ↠ takes k

takesLen : ∀ k → pathLen (takes k) ≡ k
takesLen zero    = refl
takesLen (suc k) = cong suc (takesLen k)

stLong : ℕ → EvalSt e₀
stLong B = register 0 (takes (suc B)) (st-init e₀)

-- the registration is admitted: same source, same element type
admitLong : ∀ (B : ℕ) →
  shareAdmit {t = natᵗ} fzero (EvalSt.registry (stLong B))
    ≡ (0 , takes (suc B)) ∷ []
admitLong _ = refl

-- THE CROSSING, PINNED UNDER THE BINDER so that it is a fact about
-- the legality predicate and not about the bound this file runs at.
crosses : ∀ (B : ℕ) → pathSz? B (takes (suc B)) ≡ true → ⊥
crosses B h =
  1+n≰n (subst (_≤ B) (takesLen (suc B)) (pathSz?-len B (takes (suc B)) h))

-- at the floor the tower discharges from, so the crossing is not an
-- artifact of a bound chosen small
fan-chain-sz-absurd : FanChainSz → ⊥
fan-chain-sz-absurd pr = crosses 8 row
  where
  row : pathSz? 8 (takes 9) ≡ true
  row = pr {Γ = Γ₁} {t = natᵗ} {e = e₀} 8 fzero (stLong 8)

-- AND THE PREMISE THAT REPLACES IT IS UNCONDITIONALLY FALSE TOO, at
-- the cap the tower actually runs at rather than at a stand-in: the
-- registration is built one longer than whatever that cap is, so the
-- crossing does not need the number to return.  What this leaves is a
-- fact owed at the MINT and nowhere else.
FanRegsSz : Set
FanRegsSz = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (st : EvalSt e) →
  regsSz? (Caps.cSize (capsAt e sl id)) (EvalSt.registry st) ≡ true

fan-regsSz-absurd : FanRegsSz → ⊥
fan-regsSz-absurd pr = crosses B row
  where
  B : ℕ
  B = Caps.cSize (capsAt e₀ sl₁ 0)
  row : pathSz? B (takes (suc B)) ≡ true
  row = ∧-trueˡ (pr sl₁ 0 (stLong B))

----------------------------------------------------------------------
-- THE DEPTH WITNESS: one map into an observable whose body carries
-- two `*All` layers, handed on through the outer frame that reads
-- them.  The map's own function is where the nesting lives, so the
-- path is three deep against a unit of one -- and it is three deep
-- because of syntax the PROGRAM does not contain, which is the whole
-- point: the unit is read off `e₀` and the chain was minted from a
-- term the registry never had to agree with.
----------------------------------------------------------------------
deep : ℕ → Exp Γ₁ [] [] (natᵗ ∷ []) natᵗ
deep zero    = emptyᵉ
deep (suc k) = mergeAllᵉ nothing (ofᵉ (strmᵗ (deep k) ∷ []))

deepFn : ℕ → Fn Γ₁ [] [] [] natᵗ (obs natᵗ)
deepFn k = strmᵗ (deep k)

nested : ℕ → Path Γ₁ natᵗ natᵗ
nested k = map-f (deepFn k) ↠ (thru-outer mergeAllᵒ 0 ↠ root)

-- the ladder is genuinely unbounded: one layer of nesting per rung
deepNest : ∀ (k : ℕ) → nestDᵉ (deep k) ≡ k
deepNest zero    = refl
deepNest (suc k) =
  cong suc (trans (⊔-identityʳ (nestDᵉ (deep k))) (deepNest k))

nestD≡ : pathNestD (nested 2) ≡ 3
nestD≡ = refl

stDeep : ℕ → EvalSt e₀
stDeep k = register 0 (nested k) (st-init e₀)

admitDeep : ∀ (k : ℕ) →
  shareAdmit {t = natᵗ} fzero (EvalSt.registry (stDeep k))
    ≡ (0 , nested k) ∷ []
admitDeep _ = refl

fan-chain-nestD-absurd : FanChainNestD → ⊥
fan-chain-nestD-absurd pr
  with pr {Γ = Γ₁} {t = natᵗ} {e = e₀} sl₁ fzero (stDeep 2)
... | ()

-- and the same for the premise standing in its place, at the same
-- registration
FanRegsNest : Set
FanRegsNest = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (st : EvalSt e) →
  regP? (λ {u} (p : Path Γ u t) → pathNestD p ≤ᵇ nestUnit e sl)
        (EvalSt.registry st) ≡ true

fan-regsNest-absurd : FanRegsNest → ⊥
fan-regsNest-absurd pr with pr {Γ = Γ₁} {t = natᵗ} {e = e₀} sl₁ (stDeep 2)
... | ()
