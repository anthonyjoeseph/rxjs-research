------------------------------------------------------------------
-- TRANSPORTING A TELESCOPE THROUGH A CONSTRUCTOR.
------------------------------------------------------------------

-- WHY THIS IS ITS OWN SHELF.  Two facts about the substituter are
-- proven by walking the syntax while the LOCAL TELESCOPE is
-- rearranged -- dropping an empty tail, and reassociating a split --
-- and in both the equation is between two lists rather than between
-- two expressions, so every congruence arm has to carry the same
-- transport past the constructor it is under.  That is one shelf and
-- not two: nothing below mentions which rearrangement it is serving,
-- and each entry holds by matching the equation.
module Rx.Subst-Transport where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Vec using (lookup)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.Sum using (inj₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)

open import Rx.Exp
  using ( Ty; Ctx; Exp; Tm
        ; input; ofᵉ; emptyᵉ; takeᵉ; batchSyncᵉ; liftᵉ; mergeAllᵉ
        ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; mintᵉ
        ; varᵗ; unit̂; bool̂; nat̂; uniq̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ
        ; caseᵗ; ifᵗ; primᵗ; strmᵗ; PrimOp
        ; nilᵗ; consᵗ; foldᵗ
        ; unitᵗ; boolᵗ; natᵗ; uniqᵗ; obs; listᵗ; _×ᵗ_; _+ᵗ_ )

private
  variable
    n     : ℕ
    Γ     : Ctx n
    Δᵍ Δ  : List Ty
    Θ Θ'  : List Ty
    s t u : Ty

-- THREE-ARGUMENT CONGRUENCE, which the standard library stops at two.
-- It sits here rather than beside either walk because both of them
-- have a three-field constructor and the fact is the same one.
cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x y : A} {u v : B} {p q : C}
      → x ≡ y → u ≡ v → p ≡ q → f x u p ≡ f y v q
cong₃ f refl refl refl = refl

------------------------------------------------------------------
-- THE TRANSPORTS.  Each says a constructor commutes with the
-- telescope transport, and each holds by matching the equation.
------------------------------------------------------------------

Cᵉ : ∀ {n} (Γ : Ctx n) (Δᵍ Δ : List Ty) (t : Ty) → List Ty → Set
Cᵉ Γ Δᵍ Δ t Θ = Exp Γ Δᵍ Δ Θ t

Cᵗ : ∀ {n} (Γ : Ctx n) (Δᵍ Δ : List Ty) (t : Ty) → List Ty → Set
Cᵗ Γ Δᵍ Δ t Θ = Tm Γ Δᵍ Δ Θ t

Cˢ : ∀ {n} (Γ : Ctx n) (Δᵍ Δ : List Ty) (t : Ty) → List Ty → Set
Cˢ Γ Δᵍ Δ t Θ = List (Tm Γ Δᵍ Δ Θ t)

-- A BINDER'S TRANSPORT, which is the one place the equation itself
-- has to be taken apart: the inductive call reports at the extended
-- telescope, and `++-identityʳ` at a cons IS the congruence of its
-- own tail, so the two forms agree by matching.
shift : (eq : Θ ≡ Θ') (f : Tm Γ Δᵍ Δ (s ∷ Θ) t)
      → subst (Cᵗ Γ Δᵍ Δ t) (cong (s ∷_) eq) f
          ≡ subst (λ z → Tm Γ Δᵍ Δ (s ∷ z) t) eq f
shift refl f = refl

pushInput : (eq : Θ ≡ Θ') (i : Fin n)
          → input {Γ = Γ} {Δᵍ} {Δ} {Θ'} i
              ≡ subst (Cᵉ Γ Δᵍ Δ (lookup Γ i)) eq (input i)
pushInput refl i = refl

pushEmpty : (eq : Θ ≡ Θ')
          → emptyᵉ {Γ = Γ} {Δᵍ} {Δ} {Θ'} {t}
              ≡ subst (Cᵉ Γ Δᵍ Δ t) eq emptyᵉ
pushEmpty refl = refl

pushVarᵉ : (eq : Θ ≡ Θ') (x : t ∈ Δ)
         → varᵉ {Γ = Γ} {Δᵍ} {Δ} {Θ'} x ≡ subst (Cᵉ Γ Δᵍ Δ t) eq (varᵉ x)
pushVarᵉ refl x = refl

pushOf : (eq : Θ ≡ Θ') (ts : List (Tm Γ Δᵍ Δ Θ t))
       → ofᵉ (subst (Cˢ Γ Δᵍ Δ t) eq ts) ≡ subst (Cᵉ Γ Δᵍ Δ t) eq (ofᵉ ts)
pushOf refl ts = refl


pushTake : (eq : Θ ≡ Θ') (m : Tm Γ Δᵍ Δ Θ natᵗ) (e : Exp Γ Δᵍ Δ Θ t)
         → takeᵉ (subst (Cᵗ Γ Δᵍ Δ natᵗ) eq m) (subst (Cᵉ Γ Δᵍ Δ t) eq e)
             ≡ subst (Cᵉ Γ Δᵍ Δ t) eq (takeᵉ m e)
pushTake refl m e = refl


pushLift : (eq : Θ ≡ Θ') (f : Tm Γ Δᵍ Δ ((u ×ᵗ s) ∷ Θ) (u ×ᵗ listᵗ t))
           (i : Tm Γ Δᵍ Δ Θ u) (e : Exp Γ Δᵍ Δ Θ s)
         → liftᵉ (subst (λ z → Tm Γ Δᵍ Δ ((u ×ᵗ s) ∷ z) (u ×ᵗ listᵗ t)) eq f)
                 (subst (Cᵗ Γ Δᵍ Δ u) eq i) (subst (Cᵉ Γ Δᵍ Δ s) eq e)
             ≡ subst (Cᵉ Γ Δᵍ Δ t) eq (liftᵉ f i e)
pushLift refl f i e = refl

pushMerge : (eq : Θ ≡ Θ') (lim : Maybe ℕ) (e : Exp Γ Δᵍ Δ Θ (obs t))
          → mergeAllᵉ lim (subst (Cᵉ Γ Δᵍ Δ (obs t)) eq e)
              ≡ subst (Cᵉ Γ Δᵍ Δ t) eq (mergeAllᵉ lim e)
pushMerge refl lim e = refl

pushSwitch : (eq : Θ ≡ Θ') (e : Exp Γ Δᵍ Δ Θ (obs t))
           → switchAllᵉ (subst (Cᵉ Γ Δᵍ Δ (obs t)) eq e)
               ≡ subst (Cᵉ Γ Δᵍ Δ t) eq (switchAllᵉ e)
pushSwitch refl e = refl

pushBatchSync : (eq : Θ ≡ Θ') (e : Exp Γ Δᵍ Δ Θ t)
              → batchSyncᵉ (subst (Cᵉ Γ Δᵍ Δ t) eq e)
                  ≡ subst (Cᵉ Γ Δᵍ Δ (t ×ᵗ listᵗ t)) eq (batchSyncᵉ e)
pushBatchSync refl e = refl

pushExhaust : (eq : Θ ≡ Θ') (e : Exp Γ Δᵍ Δ Θ (obs t))
            → exhaustAllᵉ (subst (Cᵉ Γ Δᵍ Δ (obs t)) eq e)
                ≡ subst (Cᵉ Γ Δᵍ Δ t) eq (exhaustAllᵉ e)
pushExhaust refl e = refl

pushMu : (eq : Θ ≡ Θ') (e : Exp Γ (t ∷ Δᵍ) Δ Θ t)
       → μᵉ (subst (Cᵉ Γ (t ∷ Δᵍ) Δ t) eq e)
           ≡ subst (Cᵉ Γ Δᵍ Δ t) eq (μᵉ e)
pushMu refl e = refl

pushDefer : (eq : Θ ≡ Θ') (e : Exp Γ [] (Δᵍ ++ Δ) Θ t)
          → deferᵉ (subst (Cᵉ Γ [] (Δᵍ ++ Δ) t) eq e)
              ≡ subst (Cᵉ Γ Δᵍ Δ t) eq (deferᵉ e)
pushDefer refl e = refl

shiftᵉ : (eq : Θ ≡ Θ') (e : Exp Γ Δᵍ Δ (s ∷ Θ) t)
       → subst (Cᵉ Γ Δᵍ Δ t) (cong (s ∷_) eq) e
           ≡ subst (λ z → Exp Γ Δᵍ Δ (s ∷ z) t) eq e
shiftᵉ refl e = refl

pushMint : (eq : Θ ≡ Θ') (e : Exp Γ Δᵍ Δ (uniqᵗ ∷ Θ) t)
         → mintᵉ (subst (λ z → Exp Γ Δᵍ Δ (uniqᵗ ∷ z) t) eq e)
             ≡ subst (Cᵉ Γ Δᵍ Δ t) eq (mintᵉ e)
pushMint refl e = refl

pushVarᵗ : (eq : Θ ≡ Θ') (x : t ∈ Θ)
         → varᵗ {Γ = Γ} {Δᵍ} {Δ} (subst (t ∈_) eq x)
             ≡ subst (Cᵗ Γ Δᵍ Δ t) eq (varᵗ x)
pushVarᵗ refl x = refl

pushUnit : (eq : Θ ≡ Θ')
         → unit̂ {Γ = Γ} {Δᵍ} {Δ} {Θ'} ≡ subst (Cᵗ Γ Δᵍ Δ unitᵗ) eq unit̂
pushUnit refl = refl

pushBool : (eq : Θ ≡ Θ') (b : Bool)
         → bool̂ {Γ = Γ} {Δᵍ} {Δ} {Θ'} b ≡ subst (Cᵗ Γ Δᵍ Δ boolᵗ) eq (bool̂ b)
pushBool refl b = refl

pushNat : (eq : Θ ≡ Θ') (m : ℕ)
        → nat̂ {Γ = Γ} {Δᵍ} {Δ} {Θ'} m ≡ subst (Cᵗ Γ Δᵍ Δ natᵗ) eq (nat̂ m)
pushNat refl m = refl

pushUniq : (eq : Θ ≡ Θ') (m : ℕ)
         → uniq̂ {Γ = Γ} {Δᵍ} {Δ} {Θ'} m ≡ subst (Cᵗ Γ Δᵍ Δ uniqᵗ) eq (uniq̂ m)
pushUniq refl m = refl

pushPair : (eq : Θ ≡ Θ') (a : Tm Γ Δᵍ Δ Θ s) (b : Tm Γ Δᵍ Δ Θ t)
         → pairᵗ (subst (Cᵗ Γ Δᵍ Δ s) eq a) (subst (Cᵗ Γ Δᵍ Δ t) eq b)
             ≡ subst (Cᵗ Γ Δᵍ Δ (s ×ᵗ t)) eq (pairᵗ a b)
pushPair refl a b = refl

pushFst : (eq : Θ ≡ Θ') (p : Tm Γ Δᵍ Δ Θ (s ×ᵗ t))
        → fstᵗ (subst (Cᵗ Γ Δᵍ Δ (s ×ᵗ t)) eq p)
            ≡ subst (Cᵗ Γ Δᵍ Δ s) eq (fstᵗ p)
pushFst refl p = refl

pushSnd : (eq : Θ ≡ Θ') (p : Tm Γ Δᵍ Δ Θ (s ×ᵗ t))
        → sndᵗ (subst (Cᵗ Γ Δᵍ Δ (s ×ᵗ t)) eq p)
            ≡ subst (Cᵗ Γ Δᵍ Δ t) eq (sndᵗ p)
pushSnd refl p = refl

pushInl : (eq : Θ ≡ Θ') (a : Tm Γ Δᵍ Δ Θ s)
        → inlᵗ {t = t} (subst (Cᵗ Γ Δᵍ Δ s) eq a)
            ≡ subst (Cᵗ Γ Δᵍ Δ (s +ᵗ t)) eq (inlᵗ a)
pushInl refl a = refl

pushInr : (eq : Θ ≡ Θ') (a : Tm Γ Δᵍ Δ Θ t)
        → inrᵗ {s = s} (subst (Cᵗ Γ Δᵍ Δ t) eq a)
            ≡ subst (Cᵗ Γ Δᵍ Δ (s +ᵗ t)) eq (inrᵗ a)
pushInr refl a = refl

pushCase : (eq : Θ ≡ Θ') (sc : Tm Γ Δᵍ Δ Θ (s +ᵗ t))
           (l : Tm Γ Δᵍ Δ (s ∷ Θ) u) (r : Tm Γ Δᵍ Δ (t ∷ Θ) u)
         → caseᵗ (subst (Cᵗ Γ Δᵍ Δ (s +ᵗ t)) eq sc)
                 (subst (λ z → Tm Γ Δᵍ Δ (s ∷ z) u) eq l)
                 (subst (λ z → Tm Γ Δᵍ Δ (t ∷ z) u) eq r)
             ≡ subst (Cᵗ Γ Δᵍ Δ u) eq (caseᵗ sc l r)
pushCase refl sc l r = refl

pushIf : (eq : Θ ≡ Θ') (c : Tm Γ Δᵍ Δ Θ boolᵗ)
         (a b : Tm Γ Δᵍ Δ Θ t)
       → ifᵗ (subst (Cᵗ Γ Δᵍ Δ boolᵗ) eq c) (subst (Cᵗ Γ Δᵍ Δ t) eq a)
             (subst (Cᵗ Γ Δᵍ Δ t) eq b)
           ≡ subst (Cᵗ Γ Δᵍ Δ t) eq (ifᵗ c a b)
pushIf refl c a b = refl

pushPrim : (eq : Θ ≡ Θ') (op : PrimOp s t) (a : Tm Γ Δᵍ Δ Θ s)
         → primᵗ op (subst (Cᵗ Γ Δᵍ Δ s) eq a)
             ≡ subst (Cᵗ Γ Δᵍ Δ t) eq (primᵗ op a)
pushPrim refl op a = refl

pushStrm : (eq : Θ ≡ Θ') (e : Exp Γ Δᵍ Δ Θ t)
         → strmᵗ (subst (Cᵉ Γ Δᵍ Δ t) eq e)
             ≡ subst (Cᵗ Γ Δᵍ Δ (obs t)) eq (strmᵗ e)
pushStrm refl e = refl

pushNilᵗ : (eq : Θ ≡ Θ')
         → nilᵗ {Γ = Γ} {Δᵍ} {Δ} {Θ'} {t} ≡ subst (Cᵗ Γ Δᵍ Δ (listᵗ t)) eq nilᵗ
pushNilᵗ refl = refl

pushConsᵗ : (eq : Θ ≡ Θ') (a : Tm Γ Δᵍ Δ Θ t) (as : Tm Γ Δᵍ Δ Θ (listᵗ t))
          → consᵗ (subst (Cᵗ Γ Δᵍ Δ t) eq a)
                  (subst (Cᵗ Γ Δᵍ Δ (listᵗ t)) eq as)
              ≡ subst (Cᵗ Γ Δᵍ Δ (listᵗ t)) eq (consᵗ a as)
pushConsᵗ refl a as = refl

pushFoldᵗ : (eq : Θ ≡ Θ') (l : Tm Γ Δᵍ Δ Θ (listᵗ s)) (z : Tm Γ Δᵍ Δ Θ u)
            (f : Tm Γ Δᵍ Δ (s ∷ u ∷ Θ) u)
          → foldᵗ (subst (Cᵗ Γ Δᵍ Δ (listᵗ s)) eq l)
                  (subst (Cᵗ Γ Δᵍ Δ u) eq z)
                  (subst (λ z′ → Tm Γ Δᵍ Δ (s ∷ u ∷ z′) u) eq f)
              ≡ subst (Cᵗ Γ Δᵍ Δ u) eq (foldᵗ l z f)
pushFoldᵗ refl l z f = refl

-- THE TWO-BINDER TRANSPORT.  `foldᵗ`'s step arm binds the element and
-- the accumulator at once, so the one-binder form cannot report it: the
-- inductive call arrives at a telescope extended twice.
shift2 : (eq : Θ ≡ Θ') (f : Tm Γ Δᵍ Δ (s ∷ u ∷ Θ) t)
       → subst (Cᵗ Γ Δᵍ Δ t) (cong (s ∷_) (cong (u ∷_) eq)) f
           ≡ subst (λ z → Tm Γ Δᵍ Δ (s ∷ u ∷ z) t) eq f
shift2 refl f = refl

pushNilˢ : (eq : Θ ≡ Θ')
         → [] ≡ subst (Cˢ Γ Δᵍ Δ t) eq []
pushNilˢ refl = refl

pushConsˢ : (eq : Θ ≡ Θ') (x : Tm Γ Δᵍ Δ Θ t) (xs : List (Tm Γ Δᵍ Δ Θ t))
          → subst (Cᵗ Γ Δᵍ Δ t) eq x ∷ subst (Cˢ Γ Δᵍ Δ t) eq xs
              ≡ subst (Cˢ Γ Δᵍ Δ t) eq (x ∷ xs)
pushConsˢ refl x xs = refl

pushHere : ∀ {a : Ty} (eq : Θ ≡ Θ') (p : t ≡ a)
         → subst (t ∈_) (cong (a ∷_) eq) (here p) ≡ here p
pushHere refl p = refl

pushThere : ∀ {a : Ty} (eq : Θ ≡ Θ') (x : t ∈ Θ)
          → subst (t ∈_) (cong (a ∷_) eq) (there x)
              ≡ there {x = a} (subst (t ∈_) eq x)
pushThere refl x = refl

------------------------------------------------------------------
-- THE SPLITTER AT AN EMPTY RIGHT HALF, which is where the identity's
-- whole content sits: with nothing to the right, every variable goes
-- left, and its left image is the transported variable itself.
------------------------------------------------------------------

∈-id : (Θ : List Ty) (x : t ∈ (Θ ++ []))
     → ∈-++⁻ Θ x ≡ inj₁ (subst (t ∈_) (++-identityʳ Θ) x)
∈-id []      ()
∈-id (a ∷ Θ) (here p)  = sym (cong inj₁ (pushHere (++-identityʳ Θ) p))
∈-id (a ∷ Θ) (there x) rewrite ∈-id Θ x =
  sym (cong inj₁ (pushThere (++-identityʳ Θ) x))
