------------------------------------------------------------------
-- PEELING A FIXPOINT AND CLOSING AGAINST AN ENVIRONMENT COMMUTE.
------------------------------------------------------------------

-- WHY THE GENERAL FORM IS THE ONLY ONE THAT CAN BE PROVEN.  The peel
-- is `elimGExp` at the empty local telescope, and that is where the
-- consumer wants it -- but the eliminator walks under binders by
-- EXTENDING the local telescope, so a statement pinned at the empty
-- one cannot be its own induction hypothesis.  Generalising it
-- immediately costs a transport, because the eliminator's target
-- telescope is `Θloc ++ Θsub` and substituting away `Θsub` leaves the
-- RIGHT side at `Θloc ++ []` while the LEFT is already at `Θloc`.  A
-- list append with a variable on the left does not reduce, so that
-- gap cannot be closed by computation and the equation cannot be
-- STATED without moving one side.  At the consumer's instance the
-- transport is `refl` and both `subst`s vanish definitionally, which
-- is what makes the peel fall out of the general statement rather
-- than out of a second one.
--
-- THE CLOSED COPY IS SUBSTITUTED TOO, and that is the part that has
-- to be said rather than assumed: the eliminator inserts `cl` renamed
-- into the substituted half, so the copy the left side closes is the
-- copy the right side has already closed, and the statement carries
-- `subΘExp [] σ cl` on the right rather than `cl`.
module Rx.Subst-Elim where

open import Data.Bool using (Bool)
open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (there)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Rx.Exp
  using (Ty; Ctx; Val; Exp; Tm; PrimOp; subΘExp; subΘTm; subΘTms; elimGExp; elimGTm; elimGTms;
  elimDExp; elimDTm; elimDTms; _⊟_; ⊟-++ˡ; ⊟-++ʳ; compare∈; renExp; wkTm; reify; lookupEnv;
  natᵗ; boolᵗ; obs; _×ᵗ_; _+ᵗ_; input; ofᵉ; emptyᵉ; takeᵉ; liftᵉ; mergeAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; varᵗ; unit̂; bool̂; nat̂; uniq̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ;
  inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ; nilᵗ; consᵗ; foldᵗ; listᵗ)
open import Rx.Subst-Transport using (Cᵉ; Cᵗ; Cˢ; cong₃; pushVarᵉ)
open import Rx.Subst-Elim-Weak using (elimG-avᵗ; elimD-avᵗ)
open import Rx.Subst-Ren-Fuse using (sub-fixᵉ; ren-wk-Θ; noRen)

private
  variable
    n            : ℕ
    Γ            : Ctx n
    Δᵍ Δ Δᵍ′ Δ′  : List Ty
    Θ Θsub       : List Ty
    s t u v w    : Ty

------------------------------------------------------------------
-- THE TRANSPORT AS A PARAMETER.
------------------------------------------------------------------

-- WHY THE EQUATION IS AN ARGUMENT AND NOT A FIXED `++-identityʳ`.
-- Every one of the commutation lemmas below has to say how the
-- eliminator meets one constructor once its telescope has been moved,
-- and with the equation FIXED each of them is a `subst` shuffle
-- needing its own transport lemma.  Taken as a parameter it can be
-- matched against `refl`, and the wrapper then IS the eliminator, so
-- the lemma is its own defining clause and holds by `refl`.  The
-- consumer pays nothing for this: at the empty local telescope the
-- equation is `refl` on the nose, so the wrapper reduces away.

Gᵉ : (Θl : List Ty) → Θl ++ [] ≡ Θ → (x : t ∈ Δᵍ)
   → Exp Γ [] [] [] t → Exp Γ Δᵍ Δ Θ u → Exp Γ (Δᵍ ⊟ x) Δ Θ u
Gᵉ Θl eq x cl e =
  subst (Cᵉ _ _ _ _) eq (elimGExp Θl x cl (subst (Cᵉ _ _ _ _) (sym eq) e))

Gᵗ : (Θl : List Ty) → Θl ++ [] ≡ Θ → (x : t ∈ Δᵍ)
   → Exp Γ [] [] [] t → Tm Γ Δᵍ Δ Θ u → Tm Γ (Δᵍ ⊟ x) Δ Θ u
Gᵗ Θl eq x cl m =
  subst (Cᵗ _ _ _ _) eq (elimGTm Θl x cl (subst (Cᵗ _ _ _ _) (sym eq) m))

Gˢ : (Θl : List Ty) → Θl ++ [] ≡ Θ → (x : t ∈ Δᵍ)
   → Exp Γ [] [] [] t → List (Tm Γ Δᵍ Δ Θ u) → List (Tm Γ (Δᵍ ⊟ x) Δ Θ u)
Gˢ Θl eq x cl ts =
  subst (Cˢ _ _ _ _) eq (elimGTms Θl x cl (subst (Cˢ _ _ _ _) (sym eq) ts))

Dᵉ : (Θl : List Ty) → Θl ++ [] ≡ Θ → (x : t ∈ Δ)
   → Exp Γ [] [] [] t → Exp Γ Δᵍ Δ Θ u → Exp Γ Δᵍ (Δ ⊟ x) Θ u
Dᵉ Θl eq x cl e =
  subst (Cᵉ _ _ _ _) eq (elimDExp Θl x cl (subst (Cᵉ _ _ _ _) (sym eq) e))

Dᵗ : (Θl : List Ty) → Θl ++ [] ≡ Θ → (x : t ∈ Δ)
   → Exp Γ [] [] [] t → Tm Γ Δᵍ Δ Θ u → Tm Γ Δᵍ (Δ ⊟ x) Θ u
Dᵗ Θl eq x cl m =
  subst (Cᵗ _ _ _ _) eq (elimDTm Θl x cl (subst (Cᵗ _ _ _ _) (sym eq) m))

Dˢ : (Θl : List Ty) → Θl ++ [] ≡ Θ → (x : t ∈ Δ)
   → Exp Γ [] [] [] t → List (Tm Γ Δᵍ Δ Θ u) → List (Tm Γ Δᵍ (Δ ⊟ x) Θ u)
Dˢ Θl eq x cl ts =
  subst (Cˢ _ _ _ _) eq (elimDTms Θl x cl (subst (Cˢ _ _ _ _) (sym eq) ts))

------------------------------------------------------------------
-- THE CONSTRUCTOR COMMUTATIONS.
------------------------------------------------------------------

gInput : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (i : Fin n)
       → Gᵉ {Δ = Δ} Θl eq x cl (input i) ≡ input i
gInput Θl refl x cl i = refl

gEmpty : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
       → Gᵉ {Δ = Δ} Θl eq x cl (emptyᵉ {t = u}) ≡ emptyᵉ
gEmpty Θl refl x cl = refl

gVarE : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (y : u ∈ Δ)
       → Gᵉ Θl eq x cl (varᵉ y) ≡ varᵉ y
gVarE Θl refl x cl y = refl

gOf : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (ts : List (Tm Γ Δᵍ Δ Θ u))
       → Gᵉ Θl eq x cl (ofᵉ ts) ≡ ofᵉ (Gˢ Θl eq x cl ts)
gOf Θl refl x cl ts = refl


gTake : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (m : Tm Γ Δᵍ Δ Θ natᵗ) (e : Exp Γ Δᵍ Δ Θ u)
       → Gᵉ Θl eq x cl (takeᵉ m e) ≡ takeᵉ (Gᵗ Θl eq x cl m) (Gᵉ Θl eq x cl e)
gTake Θl refl x cl m e = refl


gLift : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (f : Tm Γ Δᵍ Δ ((v ×ᵗ listᵗ s) ∷ Θ) (v ×ᵗ listᵗ u)) (i : Tm Γ Δᵍ Δ Θ v)
           (e : Exp Γ Δᵍ Δ Θ s)
       → Gᵉ Θl eq x cl (liftᵉ f i e)
           ≡ liftᵉ (Gᵗ ((v ×ᵗ listᵗ s) ∷ Θl) (cong ((v ×ᵗ listᵗ s) ∷_) eq) x cl f)
                   (Gᵗ Θl eq x cl i) (Gᵉ Θl eq x cl e)
gLift Θl refl x cl f i e = refl

gMerge : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (lim : Maybe ℕ) (e : Exp Γ Δᵍ Δ Θ (obs u))
       → Gᵉ Θl eq x cl (mergeAllᵉ lim e) ≡ mergeAllᵉ lim (Gᵉ Θl eq x cl e)
gMerge Θl refl x cl lim e = refl

gSwitch : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (e : Exp Γ Δᵍ Δ Θ (obs u))
       → Gᵉ Θl eq x cl (switchAllᵉ e) ≡ switchAllᵉ (Gᵉ Θl eq x cl e)
gSwitch Θl refl x cl e = refl

gExhaust : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (e : Exp Γ Δᵍ Δ Θ (obs u))
       → Gᵉ Θl eq x cl (exhaustAllᵉ e) ≡ exhaustAllᵉ (Gᵉ Θl eq x cl e)
gExhaust Θl refl x cl e = refl

gMu : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (e : Exp Γ (u ∷ Δᵍ) Δ Θ u)
       → Gᵉ Θl eq x cl (μᵉ e) ≡ μᵉ (Gᵉ Θl eq (there x) cl e)
gMu Θl refl x cl e = refl

gDefer : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (e : Exp Γ [] (Δᵍ ++ Δ) Θ u)
       → Gᵉ Θl eq x cl (deferᵉ e) ≡ deferᵉ (subst (λ ζ → Exp Γ [] ζ Θ u) (⊟-++ˡ x)
                       (Dᵉ Θl eq (∈-++⁺ˡ x) cl e))
gDefer Θl refl x cl e = refl

gVarT : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (y : u ∈ Θ)
       → Gᵗ {Δ = Δ} Θl eq x cl (varᵗ y) ≡ varᵗ y
gVarT Θl refl x cl y = refl

gUnit : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
       → Gᵗ Θl eq x cl (unit̂ {Γ = Γ} {Δᵍ} {Δ} {Θ}) ≡ unit̂
gUnit Θl refl x cl = refl

gBool : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (b : Bool)
       → Gᵗ Θl eq x cl (bool̂ {Γ = Γ} {Δᵍ} {Δ} {Θ} b) ≡ bool̂ b
gBool Θl refl x cl b = refl

gNat : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (m : ℕ)
       → Gᵗ Θl eq x cl (nat̂ {Γ = Γ} {Δᵍ} {Δ} {Θ} m) ≡ nat̂ m
gNat Θl refl x cl m = refl

gUniq : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (m : ℕ)
       → Gᵗ Θl eq x cl (uniq̂ {Γ = Γ} {Δᵍ} {Δ} {Θ} m) ≡ uniq̂ m
gUniq Θl refl x cl m = refl

gPair : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (a : Tm Γ Δᵍ Δ Θ s) (b : Tm Γ Δᵍ Δ Θ u)
       → Gᵗ Θl eq x cl (pairᵗ a b) ≡ pairᵗ (Gᵗ Θl eq x cl a) (Gᵗ Θl eq x cl b)
gPair Θl refl x cl a b = refl

gFst : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (q : Tm Γ Δᵍ Δ Θ (u ×ᵗ s))
       → Gᵗ Θl eq x cl (fstᵗ q) ≡ fstᵗ (Gᵗ Θl eq x cl q)
gFst Θl refl x cl q = refl

gSnd : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (q : Tm Γ Δᵍ Δ Θ (s ×ᵗ u))
       → Gᵗ Θl eq x cl (sndᵗ q) ≡ sndᵗ (Gᵗ Θl eq x cl q)
gSnd Θl refl x cl q = refl

gInl : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (a : Tm Γ Δᵍ Δ Θ v)
       → Gᵗ Θl eq x cl (inlᵗ {t = w} a) ≡ inlᵗ (Gᵗ Θl eq x cl a)
gInl Θl refl x cl a = refl

gInr : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (a : Tm Γ Δᵍ Δ Θ w)
       → Gᵗ Θl eq x cl (inrᵗ {s = v} a) ≡ inrᵗ (Gᵗ Θl eq x cl a)
gInr Θl refl x cl a = refl

gCase : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (sc : Tm Γ Δᵍ Δ Θ (v +ᵗ w)) (l : Tm Γ Δᵍ Δ (v ∷ Θ) u)
           (r : Tm Γ Δᵍ Δ (w ∷ Θ) u)
       → Gᵗ Θl eq x cl (caseᵗ sc l r) ≡ caseᵗ (Gᵗ Θl eq x cl sc) (Gᵗ (v ∷ Θl) (cong (v ∷_) eq) x cl l)
               (Gᵗ (w ∷ Θl) (cong (w ∷_) eq) x cl r)
gCase Θl refl x cl sc l r = refl

gIf : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (c : Tm Γ Δᵍ Δ Θ boolᵗ) (a b : Tm Γ Δᵍ Δ Θ u)
       → Gᵗ Θl eq x cl (ifᵗ c a b) ≡ ifᵗ (Gᵗ Θl eq x cl c) (Gᵗ Θl eq x cl a) (Gᵗ Θl eq x cl b)
gIf Θl refl x cl c a b = refl

gPrim : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (op : PrimOp v u) (a : Tm Γ Δᵍ Δ Θ v)
       → Gᵗ Θl eq x cl (primᵗ op a) ≡ primᵗ op (Gᵗ Θl eq x cl a)
gPrim Θl refl x cl op a = refl

gStrm : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (e : Exp Γ Δᵍ Δ Θ v)
       → Gᵗ Θl eq x cl (strmᵗ e) ≡ strmᵗ (Gᵉ Θl eq x cl e)
gStrm Θl refl x cl e = refl

gNilᵗ : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
      → Gᵗ Θl eq x cl (nilᵗ {Γ = Γ} {Δᵍ} {Δ} {Θ} {u}) ≡ nilᵗ
gNilᵗ Θl refl x cl = refl

gConsᵗ : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (a : Tm Γ Δᵍ Δ Θ u) (as : Tm Γ Δᵍ Δ Θ (listᵗ u))
       → Gᵗ Θl eq x cl (consᵗ a as) ≡ consᵗ (Gᵗ Θl eq x cl a) (Gᵗ Θl eq x cl as)
gConsᵗ Θl refl x cl a as = refl

gFoldᵗ : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
           (l : Tm Γ Δᵍ Δ Θ (listᵗ v)) (z : Tm Γ Δᵍ Δ Θ u)
           (f : Tm Γ Δᵍ Δ (v ∷ u ∷ Θ) u)
       → Gᵗ Θl eq x cl (foldᵗ l z f)
           ≡ foldᵗ (Gᵗ Θl eq x cl l) (Gᵗ Θl eq x cl z)
               (Gᵗ (v ∷ u ∷ Θl) (cong (v ∷_) (cong (u ∷_) eq)) x cl f)
gFoldᵗ Θl refl x cl l z f = refl

gNil : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
      → Gˢ {Δ = Δ} {u = u} Θl eq x cl [] ≡ []
gNil Θl refl x cl = refl

gCons : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
          (y : Tm Γ Δᵍ Δ Θ u) (ys : List (Tm Γ Δᵍ Δ Θ u))
        → Gˢ Θl eq x cl (y ∷ ys) ≡ Gᵗ Θl eq x cl y ∷ Gˢ Θl eq x cl ys
gCons Θl refl x cl y ys = refl

dInput : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (i : Fin n)
       → Dᵉ {Δᵍ = Δᵍ} Θl eq x cl (input i) ≡ input i
dInput Θl refl x cl i = refl

dEmpty : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
       → Dᵉ {Δᵍ = Δᵍ} Θl eq x cl (emptyᵉ {t = u}) ≡ emptyᵉ
dEmpty Θl refl x cl = refl

dOf : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (ts : List (Tm Γ Δᵍ Δ Θ u))
       → Dᵉ Θl eq x cl (ofᵉ ts) ≡ ofᵉ (Dˢ Θl eq x cl ts)
dOf Θl refl x cl ts = refl


dTake : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (m : Tm Γ Δᵍ Δ Θ natᵗ) (e : Exp Γ Δᵍ Δ Θ u)
       → Dᵉ Θl eq x cl (takeᵉ m e) ≡ takeᵉ (Dᵗ Θl eq x cl m) (Dᵉ Θl eq x cl e)
dTake Θl refl x cl m e = refl


dLift : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (f : Tm Γ Δᵍ Δ ((v ×ᵗ listᵗ s) ∷ Θ) (v ×ᵗ listᵗ u)) (i : Tm Γ Δᵍ Δ Θ v)
           (e : Exp Γ Δᵍ Δ Θ s)
       → Dᵉ Θl eq x cl (liftᵉ f i e)
           ≡ liftᵉ (Dᵗ ((v ×ᵗ listᵗ s) ∷ Θl) (cong ((v ×ᵗ listᵗ s) ∷_) eq) x cl f)
                   (Dᵗ Θl eq x cl i) (Dᵉ Θl eq x cl e)
dLift Θl refl x cl f i e = refl

dMerge : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (lim : Maybe ℕ) (e : Exp Γ Δᵍ Δ Θ (obs u))
       → Dᵉ Θl eq x cl (mergeAllᵉ lim e) ≡ mergeAllᵉ lim (Dᵉ Θl eq x cl e)
dMerge Θl refl x cl lim e = refl

dSwitch : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (e : Exp Γ Δᵍ Δ Θ (obs u))
       → Dᵉ Θl eq x cl (switchAllᵉ e) ≡ switchAllᵉ (Dᵉ Θl eq x cl e)
dSwitch Θl refl x cl e = refl

dExhaust : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (e : Exp Γ Δᵍ Δ Θ (obs u))
       → Dᵉ Θl eq x cl (exhaustAllᵉ e) ≡ exhaustAllᵉ (Dᵉ Θl eq x cl e)
dExhaust Θl refl x cl e = refl

dMu : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (e : Exp Γ (u ∷ Δᵍ) Δ Θ u)
       → Dᵉ Θl eq x cl (μᵉ e) ≡ μᵉ (Dᵉ Θl eq x cl e)
dMu Θl refl x cl e = refl

dDefer : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (e : Exp Γ [] (Δᵍ ++ Δ) Θ u)
       → Dᵉ Θl eq x cl (deferᵉ e) ≡ deferᵉ (subst (λ ζ → Exp Γ [] ζ Θ u) (⊟-++ʳ x)
                       (Dᵉ Θl eq (∈-++⁺ʳ Δᵍ x) cl e))
dDefer Θl refl x cl e = refl

dVarT : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (y : u ∈ Θ)
       → Dᵗ {Δᵍ = Δᵍ} Θl eq x cl (varᵗ y) ≡ varᵗ y
dVarT Θl refl x cl y = refl

dUnit : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
       → Dᵗ Θl eq x cl (unit̂ {Γ = Γ} {Δᵍ} {Δ} {Θ}) ≡ unit̂
dUnit Θl refl x cl = refl

dBool : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (b : Bool)
       → Dᵗ Θl eq x cl (bool̂ {Γ = Γ} {Δᵍ} {Δ} {Θ} b) ≡ bool̂ b
dBool Θl refl x cl b = refl

dNat : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (m : ℕ)
       → Dᵗ Θl eq x cl (nat̂ {Γ = Γ} {Δᵍ} {Δ} {Θ} m) ≡ nat̂ m
dNat Θl refl x cl m = refl

dUniq : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (m : ℕ)
       → Dᵗ Θl eq x cl (uniq̂ {Γ = Γ} {Δᵍ} {Δ} {Θ} m) ≡ uniq̂ m
dUniq Θl refl x cl m = refl

dPair : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (a : Tm Γ Δᵍ Δ Θ s) (b : Tm Γ Δᵍ Δ Θ u)
       → Dᵗ Θl eq x cl (pairᵗ a b) ≡ pairᵗ (Dᵗ Θl eq x cl a) (Dᵗ Θl eq x cl b)
dPair Θl refl x cl a b = refl

dFst : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (q : Tm Γ Δᵍ Δ Θ (u ×ᵗ s))
       → Dᵗ Θl eq x cl (fstᵗ q) ≡ fstᵗ (Dᵗ Θl eq x cl q)
dFst Θl refl x cl q = refl

dSnd : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (q : Tm Γ Δᵍ Δ Θ (s ×ᵗ u))
       → Dᵗ Θl eq x cl (sndᵗ q) ≡ sndᵗ (Dᵗ Θl eq x cl q)
dSnd Θl refl x cl q = refl

dInl : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (a : Tm Γ Δᵍ Δ Θ v)
       → Dᵗ Θl eq x cl (inlᵗ {t = w} a) ≡ inlᵗ (Dᵗ Θl eq x cl a)
dInl Θl refl x cl a = refl

dInr : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (a : Tm Γ Δᵍ Δ Θ w)
       → Dᵗ Θl eq x cl (inrᵗ {s = v} a) ≡ inrᵗ (Dᵗ Θl eq x cl a)
dInr Θl refl x cl a = refl

dCase : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (sc : Tm Γ Δᵍ Δ Θ (v +ᵗ w)) (l : Tm Γ Δᵍ Δ (v ∷ Θ) u)
           (r : Tm Γ Δᵍ Δ (w ∷ Θ) u)
       → Dᵗ Θl eq x cl (caseᵗ sc l r) ≡ caseᵗ (Dᵗ Θl eq x cl sc) (Dᵗ (v ∷ Θl) (cong (v ∷_) eq) x cl l)
               (Dᵗ (w ∷ Θl) (cong (w ∷_) eq) x cl r)
dCase Θl refl x cl sc l r = refl

dIf : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (c : Tm Γ Δᵍ Δ Θ boolᵗ) (a b : Tm Γ Δᵍ Δ Θ u)
       → Dᵗ Θl eq x cl (ifᵗ c a b) ≡ ifᵗ (Dᵗ Θl eq x cl c) (Dᵗ Θl eq x cl a) (Dᵗ Θl eq x cl b)
dIf Θl refl x cl c a b = refl

dPrim : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (op : PrimOp v u) (a : Tm Γ Δᵍ Δ Θ v)
       → Dᵗ Θl eq x cl (primᵗ op a) ≡ primᵗ op (Dᵗ Θl eq x cl a)
dPrim Θl refl x cl op a = refl

dStrm : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (e : Exp Γ Δᵍ Δ Θ v)
       → Dᵗ Θl eq x cl (strmᵗ e) ≡ strmᵗ (Dᵉ Θl eq x cl e)
dStrm Θl refl x cl e = refl

dNilᵗ : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
      → Dᵗ Θl eq x cl (nilᵗ {Γ = Γ} {Δᵍ} {Δ} {Θ} {u}) ≡ nilᵗ
dNilᵗ Θl refl x cl = refl

dConsᵗ : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (a : Tm Γ Δᵍ Δ Θ u) (as : Tm Γ Δᵍ Δ Θ (listᵗ u))
       → Dᵗ Θl eq x cl (consᵗ a as) ≡ consᵗ (Dᵗ Θl eq x cl a) (Dᵗ Θl eq x cl as)
dConsᵗ Θl refl x cl a as = refl

dFoldᵗ : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
           (l : Tm Γ Δᵍ Δ Θ (listᵗ v)) (z : Tm Γ Δᵍ Δ Θ u)
           (f : Tm Γ Δᵍ Δ (v ∷ u ∷ Θ) u)
       → Dᵗ Θl eq x cl (foldᵗ l z f)
           ≡ foldᵗ (Dᵗ Θl eq x cl l) (Dᵗ Θl eq x cl z)
               (Dᵗ (v ∷ u ∷ Θl) (cong (v ∷_) (cong (u ∷_) eq)) x cl f)
dFoldᵗ Θl refl x cl l z f = refl

dNil : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
      → Dˢ {Δ = Δ} {Δᵍ = Δᵍ} {u = u} Θl eq x cl [] ≡ []
dNil Θl refl x cl = refl

dCons : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
          (y : Tm Γ Δᵍ Δ Θ u) (ys : List (Tm Γ Δᵍ Δ Θ u))
        → Dˢ Θl eq x cl (y ∷ ys) ≡ Dᵗ Θl eq x cl y ∷ Dˢ Θl eq x cl ys
dCons Θl refl x cl y ys = refl

-- THE DEFERRED FACE'S VARIABLE ARM HAS NO CONSTRUCTOR FORM, because it
-- is where the eliminator STOPS: it compares the two positions and
-- either inserts the closed copy or renumbers.  So its commutation
-- says only that the wrapper is the eliminator under a transport, and
-- the comparison is taken apart where the induction meets it.
dVarE : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
        (y : u ∈ Δ)
      → Dᵉ Θl eq x cl (varᵉ y)
          ≡ subst (Cᵉ Γ Δᵍ (Δ ⊟ x) u) eq (elimDExp Θl x cl (varᵉ y))
dVarE Θl refl x cl y = refl

------------------------------------------------------------------
-- THE DEFERRED CONTEXT'S OWN TRANSPORT.
------------------------------------------------------------------

-- Crossing a gate re-splits the two μ-variable halves, so the
-- eliminator carries a `subst` on the Δ index there.  The substituter
-- never reads that index, so it passes straight through.
subΔᵉ : (Θloc : List Ty) (σ : All (Val Γ) Θsub) (p : Δ ≡ Δ′)
        (E : Exp Γ [] Δ (Θloc ++ Θsub) u)
      → subΘExp Θloc σ (subst (λ ζ → Exp Γ [] ζ (Θloc ++ Θsub) u) p E)
          ≡ subst (λ ζ → Exp Γ [] ζ Θloc u) p (subΘExp Θloc σ E)
subΔᵉ Θloc σ refl E = refl

------------------------------------------------------------------
-- THE LEAVES.
------------------------------------------------------------------

-- A CLOSED TERM WEAKENED INTO THE WALK IS UNTOUCHED BY EITHER
-- ELIMINATOR, which is what the environment arm needs: the value the
-- substituter drops in is a literal with no variable of any kind in
-- it, so there is nothing for the eliminator to renumber.  Both faces
-- are the instance of `Rx.Subst-Elim-Weak`'s avoidance theorem at the
-- EMPTY source contexts, where the avoidance premise is vacuous and
-- the renamings are the weakening's own absurd maps -- left implicit
-- here so that unification takes them from `wkTm` itself rather than
-- pairing two separately elaborated absurd lambdas.
gWk : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
      (m : Tm Γ [] [] [] u)
    → Gᵗ {Δ = Δ} Θl eq x cl (wkTm m) ≡ wkTm m
gWk Θl refl x cl m = elimG-avᵗ Θl x cl (λ ()) m

dWk : (Θl : List Ty) (eq : Θl ++ [] ≡ Θ) (x : t ∈ Δ) (cl : Exp Γ [] [] [] t)
      (m : Tm Γ [] [] [] u)
    → Dᵗ {Δᵍ = Δᵍ} Θl eq x cl (wkTm m) ≡ wkTm m
dWk Θl refl x cl m = elimD-avᵗ Θl x refl cl (λ ()) m

-- AND THE INSERTED COPY IS CLOSED BY THE SAME ENVIRONMENT IT IS
-- WEAKENED PAST.  The eliminator renames `cl` into the RIGHT half of
-- the walk's telescope -- the half the substituter is about to
-- consume -- so closing after the rename agrees with renaming the
-- already-closed copy.  This is the only place in the development
-- where a renaming and this substituter meet on the same expression.
-- It is `Rx.Subst-Ren-Fuse`'s fix-past-a-renaming theorem at an EMPTY
-- local telescope, where the left premise is vacuous and the right one
-- is reflexivity; what is left over is the transport the telescope's
-- right identity leaves behind, and that falls to the empty source
-- context admitting exactly one renaming.
sub-ren-gate : (Θl : List Ty) (cl : Exp Γ [] [] Θsub t)
               (σ : All (Val Γ) Θsub)
             → subΘExp Θl σ (renExp {Δᵍ′ = Δᵍ′} {Δ′ = Δ′} (λ ()) (λ ()) (∈-++⁺ʳ Θl) cl)
                 ≡ subst (Cᵉ Γ Δᵍ′ Δ′ t) (++-identityʳ Θl)
                     (renExp (λ ()) (λ ()) (∈-++⁺ʳ Θl) (subΘExp [] σ cl))
sub-ren-gate Θl cl σ =
  trans (sub-fixᵉ [] Θl {ρa = noRen} σ (λ ()) (λ _ → refl) cl)
        (sym (ren-wk-Θ (∈-++⁺ʳ Θl) noRen (++-identityʳ Θl) (subΘExp [] σ cl)))

------------------------------------------------------------------
-- THE ARMS WHERE A WALK STOPS.
------------------------------------------------------------------

-- Each of these takes the same comparison apart on BOTH sides at once
-- -- the substituter's telescope split, or the eliminator's position
-- comparison -- which is why they sit outside the induction: there is
-- no recursive call in any of them.

private
  sub-elimG-varᵗ : {Δ : List Ty} (Θloc : List Ty) (x : t ∈ Δᵍ)
                   (cl : Exp Γ [] [] Θsub t)
                   (σ : All (Val Γ) Θsub) (y : u ∈ (Θloc ++ Θsub))
                 → subΘTm Θloc σ (elimGTm {Δ = Δ} Θloc x cl (varᵗ y))
                     ≡ Gᵗ Θloc (++-identityʳ Θloc) x (subΘExp [] σ cl)
                         (subΘTm Θloc σ (varᵗ y))
  sub-elimG-varᵗ Θloc x cl σ y with ∈-++⁻ Θloc y
  ... | inj₁ a = sym (gVarT Θloc (++-identityʳ Θloc) x _ a)
  ... | inj₂ b = sym (gWk Θloc (++-identityʳ Θloc) x _ (reify (lookupEnv σ b)))

  sub-elimD-varᵗ : {Δᵍ : List Ty} (Θloc : List Ty) (x : t ∈ Δ)
                   (cl : Exp Γ [] [] Θsub t)
                   (σ : All (Val Γ) Θsub) (y : u ∈ (Θloc ++ Θsub))
                 → subΘTm Θloc σ (elimDTm {Δᵍ = Δᵍ} Θloc x cl (varᵗ y))
                     ≡ Dᵗ Θloc (++-identityʳ Θloc) x (subΘExp [] σ cl)
                         (subΘTm Θloc σ (varᵗ y))
  sub-elimD-varᵗ Θloc x cl σ y with ∈-++⁻ Θloc y
  ... | inj₁ a = sym (dVarT Θloc (++-identityʳ Θloc) x _ a)
  ... | inj₂ b = sym (dWk Θloc (++-identityʳ Θloc) x _ (reify (lookupEnv σ b)))

  sub-elimD-varᵉ : (Θloc : List Ty) (x : t ∈ Δ) (cl : Exp Γ [] [] Θsub t)
                   (σ : All (Val Γ) Θsub) (y : u ∈ Δ)
                 → subΘExp Θloc σ (elimDExp Θloc x cl (varᵉ y))
                     ≡ subst (Cᵉ Γ Δᵍ (Δ ⊟ x) u) (++-identityʳ Θloc)
                         (elimDExp Θloc x (subΘExp [] σ cl) (varᵉ y))
  sub-elimD-varᵉ Θloc x cl σ y with compare∈ x y
  ... | inj₁ refl = sub-ren-gate Θloc cl σ
  ... | inj₂ y′   = pushVarᵉ (++-identityʳ Θloc) y′

------------------------------------------------------------------
-- THE INDUCTION.
------------------------------------------------------------------

mutual
  sub-elimGᵉ : (Θloc : List Ty) (x : t ∈ Δᵍ)
       (cl : Exp Γ [] [] Θsub t) (σ : All (Val Γ) Θsub)
       (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) u)
     → subΘExp Θloc σ (elimGExp Θloc x cl e)
         ≡ Gᵉ Θloc (++-identityʳ Θloc) x (subΘExp [] σ cl) (subΘExp Θloc σ e)
  sub-elimGᵉ Θloc x cl σ (input i) =
    sym (gInput Θloc (++-identityʳ Θloc) x _ i)
  sub-elimGᵉ Θloc x cl σ emptyᵉ =
    sym (gEmpty Θloc (++-identityʳ Θloc) x _)
  sub-elimGᵉ Θloc x cl σ (varᵉ y) =
    sym (gVarE Θloc (++-identityʳ Θloc) x _ y)
  sub-elimGᵉ Θloc x cl σ (ofᵉ ts) =
    trans (cong ofᵉ (sub-elimGᵗˢ Θloc x cl σ ts))
          (sym (gOf Θloc (++-identityʳ Θloc) x _ _))
  sub-elimGᵉ Θloc x cl σ (takeᵉ m e) =
    trans (cong₂ takeᵉ (sub-elimGᵗ Θloc x cl σ m) (sub-elimGᵉ Θloc x cl σ e))
          (sym (gTake Θloc (++-identityʳ Θloc) x _ _ _))
  sub-elimGᵉ Θloc x cl σ (liftᵉ {s = s} {u = a} f i e) =
    trans (cong₃ liftᵉ (sub-elimGᵗ ((a ×ᵗ listᵗ s) ∷ Θloc) x cl σ f)
                   (sub-elimGᵗ Θloc x cl σ i) (sub-elimGᵉ Θloc x cl σ e))
          (sym (gLift Θloc (++-identityʳ Θloc) x _ _ _ _))
  sub-elimGᵉ Θloc x cl σ (mergeAllᵉ lim e) =
    trans (cong (mergeAllᵉ lim) (sub-elimGᵉ Θloc x cl σ e))
          (sym (gMerge Θloc (++-identityʳ Θloc) x _ lim _))
  sub-elimGᵉ Θloc x cl σ (switchAllᵉ e) =
    trans (cong switchAllᵉ (sub-elimGᵉ Θloc x cl σ e))
          (sym (gSwitch Θloc (++-identityʳ Θloc) x _ _))
  sub-elimGᵉ Θloc x cl σ (exhaustAllᵉ e) =
    trans (cong exhaustAllᵉ (sub-elimGᵉ Θloc x cl σ e))
          (sym (gExhaust Θloc (++-identityʳ Θloc) x _ _))
  sub-elimGᵉ Θloc x cl σ (μᵉ e) =
    trans (cong μᵉ (sub-elimGᵉ Θloc (there x) cl σ e))
          (sym (gMu Θloc (++-identityʳ Θloc) x _ _))
  sub-elimGᵉ Θloc x cl σ (deferᵉ e) =
    trans (cong deferᵉ
            (trans (subΔᵉ Θloc σ (⊟-++ˡ x) _)
                   (cong (subst (λ ζ → Exp _ [] ζ _ _) (⊟-++ˡ x))
                         (sub-elimDᵉ Θloc (∈-++⁺ˡ x) cl σ e))))
          (sym (gDefer Θloc (++-identityʳ Θloc) x _ _))

  sub-elimGᵗ : (Θloc : List Ty) (x : t ∈ Δᵍ)
       (cl : Exp Γ [] [] Θsub t) (σ : All (Val Γ) Θsub)
       (m : Tm Γ Δᵍ Δ (Θloc ++ Θsub) u)
     → subΘTm Θloc σ (elimGTm Θloc x cl m)
         ≡ Gᵗ Θloc (++-identityʳ Θloc) x (subΘExp [] σ cl) (subΘTm Θloc σ m)
  sub-elimGᵗ Θloc x cl σ (varᵗ y) = sub-elimG-varᵗ Θloc x cl σ y
  sub-elimGᵗ Θloc x cl σ unit̂ =
    sym (gUnit Θloc (++-identityʳ Θloc) x _)
  sub-elimGᵗ Θloc x cl σ (bool̂ b) =
    sym (gBool Θloc (++-identityʳ Θloc) x _ b)
  sub-elimGᵗ Θloc x cl σ (nat̂ m) =
    sym (gNat Θloc (++-identityʳ Θloc) x _ m)
  sub-elimGᵗ Θloc x cl σ (uniq̂ m) =
    sym (gUniq Θloc (++-identityʳ Θloc) x _ m)
  sub-elimGᵗ Θloc x cl σ (pairᵗ a b) =
    trans (cong₂ pairᵗ (sub-elimGᵗ Θloc x cl σ a) (sub-elimGᵗ Θloc x cl σ b))
          (sym (gPair Θloc (++-identityʳ Θloc) x _ _ _))
  sub-elimGᵗ Θloc x cl σ (fstᵗ q) =
    trans (cong fstᵗ (sub-elimGᵗ Θloc x cl σ q))
          (sym (gFst Θloc (++-identityʳ Θloc) x _ _))
  sub-elimGᵗ Θloc x cl σ (sndᵗ q) =
    trans (cong sndᵗ (sub-elimGᵗ Θloc x cl σ q))
          (sym (gSnd Θloc (++-identityʳ Θloc) x _ _))
  sub-elimGᵗ Θloc x cl σ (inlᵗ a) =
    trans (cong inlᵗ (sub-elimGᵗ Θloc x cl σ a))
          (sym (gInl Θloc (++-identityʳ Θloc) x _ _))
  sub-elimGᵗ Θloc x cl σ (inrᵗ a) =
    trans (cong inrᵗ (sub-elimGᵗ Θloc x cl σ a))
          (sym (gInr Θloc (++-identityʳ Θloc) x _ _))
  sub-elimGᵗ Θloc x cl σ (caseᵗ {s = a} {t = b} sc l r) =
    trans (cong₃ caseᵗ (sub-elimGᵗ Θloc x cl σ sc) (sub-elimGᵗ (a ∷ Θloc) x cl σ l)
                   (sub-elimGᵗ (b ∷ Θloc) x cl σ r))
          (sym (gCase Θloc (++-identityʳ Θloc) x _ _ _ _))
  sub-elimGᵗ Θloc x cl σ (ifᵗ c a b) =
    trans (cong₃ ifᵗ (sub-elimGᵗ Θloc x cl σ c) (sub-elimGᵗ Θloc x cl σ a)
                   (sub-elimGᵗ Θloc x cl σ b))
          (sym (gIf Θloc (++-identityʳ Θloc) x _ _ _ _))
  sub-elimGᵗ Θloc x cl σ (primᵗ op a) =
    trans (cong (primᵗ op) (sub-elimGᵗ Θloc x cl σ a))
          (sym (gPrim Θloc (++-identityʳ Θloc) x _ op _))
  sub-elimGᵗ Θloc x cl σ nilᵗ =
    sym (gNilᵗ Θloc (++-identityʳ Θloc) x _)
  sub-elimGᵗ Θloc x cl σ (consᵗ a as) =
    trans (cong₂ consᵗ (sub-elimGᵗ Θloc x cl σ a) (sub-elimGᵗ Θloc x cl σ as))
          (sym (gConsᵗ Θloc (++-identityʳ Θloc) x _ _ _))
  sub-elimGᵗ Θloc x cl σ (foldᵗ {s = a} {u = b} l z f) =
    trans (cong₃ foldᵗ (sub-elimGᵗ Θloc x cl σ l) (sub-elimGᵗ Θloc x cl σ z)
                   (sub-elimGᵗ (a ∷ b ∷ Θloc) x cl σ f))
          (sym (gFoldᵗ Θloc (++-identityʳ Θloc) x _ _ _ _))
  sub-elimGᵗ Θloc x cl σ (strmᵗ e) =
    trans (cong strmᵗ (sub-elimGᵉ Θloc x cl σ e))
          (sym (gStrm Θloc (++-identityʳ Θloc) x _ _))

  sub-elimGᵗˢ : (Θloc : List Ty) (x : t ∈ Δᵍ)
        (cl : Exp Γ [] [] Θsub t) (σ : All (Val Γ) Θsub)
        (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) u))
      → subΘTms Θloc σ (elimGTms Θloc x cl ts)
          ≡ Gˢ Θloc (++-identityʳ Θloc) x (subΘExp [] σ cl) (subΘTms Θloc σ ts)
  sub-elimGᵗˢ Θloc x cl σ [] = sym (gNil Θloc (++-identityʳ Θloc) x _)
  sub-elimGᵗˢ Θloc x cl σ (y ∷ ys) =
    trans (cong₂ _∷_ (sub-elimGᵗ Θloc x cl σ y) (sub-elimGᵗˢ Θloc x cl σ ys))
          (sym (gCons Θloc (++-identityʳ Θloc) x _ _ _))

  sub-elimDᵉ : (Θloc : List Ty) (x : t ∈ Δ)
       (cl : Exp Γ [] [] Θsub t) (σ : All (Val Γ) Θsub)
       (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) u)
     → subΘExp Θloc σ (elimDExp Θloc x cl e)
         ≡ Dᵉ Θloc (++-identityʳ Θloc) x (subΘExp [] σ cl) (subΘExp Θloc σ e)
  sub-elimDᵉ Θloc x cl σ (input i) =
    sym (dInput Θloc (++-identityʳ Θloc) x _ i)
  sub-elimDᵉ Θloc x cl σ emptyᵉ =
    sym (dEmpty Θloc (++-identityʳ Θloc) x _)
  sub-elimDᵉ Θloc x cl σ (ofᵉ ts) =
    trans (cong ofᵉ (sub-elimDᵗˢ Θloc x cl σ ts))
          (sym (dOf Θloc (++-identityʳ Θloc) x _ _))
  sub-elimDᵉ Θloc x cl σ (takeᵉ m e) =
    trans (cong₂ takeᵉ (sub-elimDᵗ Θloc x cl σ m) (sub-elimDᵉ Θloc x cl σ e))
          (sym (dTake Θloc (++-identityʳ Θloc) x _ _ _))
  sub-elimDᵉ Θloc x cl σ (liftᵉ {s = s} {u = a} f i e) =
    trans (cong₃ liftᵉ (sub-elimDᵗ ((a ×ᵗ listᵗ s) ∷ Θloc) x cl σ f)
                   (sub-elimDᵗ Θloc x cl σ i) (sub-elimDᵉ Θloc x cl σ e))
          (sym (dLift Θloc (++-identityʳ Θloc) x _ _ _ _))
  sub-elimDᵉ Θloc x cl σ (mergeAllᵉ lim e) =
    trans (cong (mergeAllᵉ lim) (sub-elimDᵉ Θloc x cl σ e))
          (sym (dMerge Θloc (++-identityʳ Θloc) x _ lim _))
  sub-elimDᵉ Θloc x cl σ (switchAllᵉ e) =
    trans (cong switchAllᵉ (sub-elimDᵉ Θloc x cl σ e))
          (sym (dSwitch Θloc (++-identityʳ Θloc) x _ _))
  sub-elimDᵉ Θloc x cl σ (exhaustAllᵉ e) =
    trans (cong exhaustAllᵉ (sub-elimDᵉ Θloc x cl σ e))
          (sym (dExhaust Θloc (++-identityʳ Θloc) x _ _))
  sub-elimDᵉ Θloc x cl σ (μᵉ e) =
    trans (cong μᵉ (sub-elimDᵉ Θloc x cl σ e))
          (sym (dMu Θloc (++-identityʳ Θloc) x _ _))
  sub-elimDᵉ Θloc x cl σ (deferᵉ e) =
    trans (cong deferᵉ
            (trans (subΔᵉ Θloc σ (⊟-++ʳ x) _)
                   (cong (subst (λ ζ → Exp _ [] ζ _ _) (⊟-++ʳ x))
                         (sub-elimDᵉ Θloc (∈-++⁺ʳ _ x) cl σ e))))
          (sym (dDefer Θloc (++-identityʳ Θloc) x _ _))
  sub-elimDᵉ Θloc x cl σ (varᵉ y) =
    trans (sub-elimD-varᵉ Θloc x cl σ y)
          (sym (dVarE Θloc (++-identityʳ Θloc) x _ y))

  sub-elimDᵗ : (Θloc : List Ty) (x : t ∈ Δ)
       (cl : Exp Γ [] [] Θsub t) (σ : All (Val Γ) Θsub)
       (m : Tm Γ Δᵍ Δ (Θloc ++ Θsub) u)
     → subΘTm Θloc σ (elimDTm Θloc x cl m)
         ≡ Dᵗ Θloc (++-identityʳ Θloc) x (subΘExp [] σ cl) (subΘTm Θloc σ m)
  sub-elimDᵗ Θloc x cl σ (varᵗ y) = sub-elimD-varᵗ Θloc x cl σ y
  sub-elimDᵗ Θloc x cl σ unit̂ =
    sym (dUnit Θloc (++-identityʳ Θloc) x _)
  sub-elimDᵗ Θloc x cl σ (bool̂ b) =
    sym (dBool Θloc (++-identityʳ Θloc) x _ b)
  sub-elimDᵗ Θloc x cl σ (nat̂ m) =
    sym (dNat Θloc (++-identityʳ Θloc) x _ m)
  sub-elimDᵗ Θloc x cl σ (uniq̂ m) =
    sym (dUniq Θloc (++-identityʳ Θloc) x _ m)
  sub-elimDᵗ Θloc x cl σ (pairᵗ a b) =
    trans (cong₂ pairᵗ (sub-elimDᵗ Θloc x cl σ a) (sub-elimDᵗ Θloc x cl σ b))
          (sym (dPair Θloc (++-identityʳ Θloc) x _ _ _))
  sub-elimDᵗ Θloc x cl σ (fstᵗ q) =
    trans (cong fstᵗ (sub-elimDᵗ Θloc x cl σ q))
          (sym (dFst Θloc (++-identityʳ Θloc) x _ _))
  sub-elimDᵗ Θloc x cl σ (sndᵗ q) =
    trans (cong sndᵗ (sub-elimDᵗ Θloc x cl σ q))
          (sym (dSnd Θloc (++-identityʳ Θloc) x _ _))
  sub-elimDᵗ Θloc x cl σ (inlᵗ a) =
    trans (cong inlᵗ (sub-elimDᵗ Θloc x cl σ a))
          (sym (dInl Θloc (++-identityʳ Θloc) x _ _))
  sub-elimDᵗ Θloc x cl σ (inrᵗ a) =
    trans (cong inrᵗ (sub-elimDᵗ Θloc x cl σ a))
          (sym (dInr Θloc (++-identityʳ Θloc) x _ _))
  sub-elimDᵗ Θloc x cl σ (caseᵗ {s = a} {t = b} sc l r) =
    trans (cong₃ caseᵗ (sub-elimDᵗ Θloc x cl σ sc) (sub-elimDᵗ (a ∷ Θloc) x cl σ l)
                   (sub-elimDᵗ (b ∷ Θloc) x cl σ r))
          (sym (dCase Θloc (++-identityʳ Θloc) x _ _ _ _))
  sub-elimDᵗ Θloc x cl σ (ifᵗ c a b) =
    trans (cong₃ ifᵗ (sub-elimDᵗ Θloc x cl σ c) (sub-elimDᵗ Θloc x cl σ a)
                   (sub-elimDᵗ Θloc x cl σ b))
          (sym (dIf Θloc (++-identityʳ Θloc) x _ _ _ _))
  sub-elimDᵗ Θloc x cl σ (primᵗ op a) =
    trans (cong (primᵗ op) (sub-elimDᵗ Θloc x cl σ a))
          (sym (dPrim Θloc (++-identityʳ Θloc) x _ op _))
  sub-elimDᵗ Θloc x cl σ nilᵗ =
    sym (dNilᵗ Θloc (++-identityʳ Θloc) x _)
  sub-elimDᵗ Θloc x cl σ (consᵗ a as) =
    trans (cong₂ consᵗ (sub-elimDᵗ Θloc x cl σ a) (sub-elimDᵗ Θloc x cl σ as))
          (sym (dConsᵗ Θloc (++-identityʳ Θloc) x _ _ _))
  sub-elimDᵗ Θloc x cl σ (foldᵗ {s = a} {u = b} l z f) =
    trans (cong₃ foldᵗ (sub-elimDᵗ Θloc x cl σ l) (sub-elimDᵗ Θloc x cl σ z)
                   (sub-elimDᵗ (a ∷ b ∷ Θloc) x cl σ f))
          (sym (dFoldᵗ Θloc (++-identityʳ Θloc) x _ _ _ _))
  sub-elimDᵗ Θloc x cl σ (strmᵗ e) =
    trans (cong strmᵗ (sub-elimDᵉ Θloc x cl σ e))
          (sym (dStrm Θloc (++-identityʳ Θloc) x _ _))

  sub-elimDᵗˢ : (Θloc : List Ty) (x : t ∈ Δ)
        (cl : Exp Γ [] [] Θsub t) (σ : All (Val Γ) Θsub)
        (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) u))
      → subΘTms Θloc σ (elimDTms Θloc x cl ts)
          ≡ Dˢ Θloc (++-identityʳ Θloc) x (subΘExp [] σ cl) (subΘTms Θloc σ ts)
  sub-elimDᵗˢ Θloc x cl σ [] = sym (dNil Θloc (++-identityʳ Θloc) x _)
  sub-elimDᵗˢ Θloc x cl σ (y ∷ ys) =
    trans (cong₂ _∷_ (sub-elimDᵗ Θloc x cl σ y) (sub-elimDᵗˢ Θloc x cl σ ys))
          (sym (dCons Θloc (++-identityʳ Θloc) x _ _ _))
