------------------------------------------------------------------
-- CLOSING AGAINST NOTHING IS THE IDENTITY.
------------------------------------------------------------------

-- WHY THIS IS A MODULE AND NOT A ONE-LINE `refl`.  The consumer wants
-- the statement at the EMPTY local telescope, where it is degenerate;
-- the induction cannot stay there, because every binder the
-- substituter walks under EXTENDS the local telescope, so the general
-- statement is about an arbitrary `Θloc` with an empty environment.
-- There the two sides sit at DIFFERENT telescopes -- one at `Θloc`,
-- one at `Θloc ++ []` -- and a list append with a variable on the left
-- does not reduce, so the equation cannot even be STATED without a
-- transport.  That transport is what the bulk of this file pushes
-- through constructors: each arm is a congruence whose two sides carry
-- the same `subst` at different indices, and the whole of the content
-- is in the variable arm, where the splitter is shown to send every
-- variable to the left half because the right half is empty.
module Rx.Subst-Identity where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.All using ([])
open import Relation.Binary.PropositionalEquality
  using (_≡_; trans; cong; cong₂; subst)

open import Rx.Exp
  using (Ty; Ctx; Exp; Tm; subΘExp; subΘTm; subΘTms; input; ofᵉ; emptyᵉ; takeᵉ; liftᵉ;
  mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; varᵗ; unit̂; bool̂; nat̂; uniq̂; pairᵗ; fstᵗ;
  sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ; _×ᵗ_; listᵗ; nilᵗ; consᵗ; foldᵗ)
open import Rx.Subst-Transport
  using ( Cᵉ; Cᵗ; Cˢ; shift; ∈-id; cong₃
        ; pushInput; pushEmpty; pushVarᵉ; pushOf; pushTake; pushLift
        ; pushMerge; pushSwitch; pushExhaust; pushMu; pushDefer
        ; pushVarᵗ; pushUnit; pushBool; pushNat; pushUniq; pushPair; pushFst; pushSnd
        ; pushInl; pushInr; pushCase; pushIf; pushPrim; pushStrm
        ; pushNilˢ; pushConsˢ
        ; pushNilᵗ; pushConsᵗ; pushFoldᵗ; shift2 )

private
  variable
    n     : ℕ
    Γ     : Ctx n
    Δᵍ Δ  : List Ty
    Θ Θ'  : List Ty
    s t u : Ty

------------------------------------------------------------------
-- THE INDUCTION.
------------------------------------------------------------------

mutual
  subΘ-idᵉ : (Θloc : List Ty) (e : Exp Γ Δᵍ Δ (Θloc ++ []) t)
           → subΘExp Θloc [] e ≡ subst (Cᵉ Γ Δᵍ Δ t) (++-identityʳ Θloc) e
  subΘ-idᵉ Θloc (input i)  = pushInput (++-identityʳ Θloc) i
  subΘ-idᵉ Θloc emptyᵉ     = pushEmpty (++-identityʳ Θloc)
  subΘ-idᵉ Θloc (varᵉ x)   = pushVarᵉ (++-identityʳ Θloc) x
  subΘ-idᵉ Θloc (ofᵉ ts)   =
    trans (cong ofᵉ (subΘ-idᵗˢ Θloc ts)) (pushOf (++-identityʳ Θloc) ts)
  subΘ-idᵉ Θloc (takeᵉ m e) =
    trans (cong₂ takeᵉ (subΘ-idᵗ Θloc m) (subΘ-idᵉ Θloc e))
          (pushTake (++-identityʳ Θloc) m e)
  subΘ-idᵉ Θloc (liftᵉ {s = s} {u = u} f i e) =
    trans (cong₃ liftᵉ
            (trans (subΘ-idᵗ ((u ×ᵗ listᵗ s) ∷ Θloc) f) (shift (++-identityʳ Θloc) f))
            (subΘ-idᵗ Θloc i) (subΘ-idᵉ Θloc e))
          (pushLift (++-identityʳ Θloc) f i e)
  subΘ-idᵉ Θloc (mergeAllᵉ lim e) =
    trans (cong (mergeAllᵉ lim) (subΘ-idᵉ Θloc e))
          (pushMerge (++-identityʳ Θloc) lim e)
  subΘ-idᵉ Θloc (switchAllᵉ e) =
    trans (cong switchAllᵉ (subΘ-idᵉ Θloc e)) (pushSwitch (++-identityʳ Θloc) e)
  subΘ-idᵉ Θloc (exhaustAllᵉ e) =
    trans (cong exhaustAllᵉ (subΘ-idᵉ Θloc e)) (pushExhaust (++-identityʳ Θloc) e)
  subΘ-idᵉ Θloc (μᵉ e) =
    trans (cong μᵉ (subΘ-idᵉ Θloc e)) (pushMu (++-identityʳ Θloc) e)
  subΘ-idᵉ Θloc (deferᵉ e) =
    trans (cong deferᵉ (subΘ-idᵉ Θloc e)) (pushDefer (++-identityʳ Θloc) e)

  subΘ-idᵗ : (Θloc : List Ty) (m : Tm Γ Δᵍ Δ (Θloc ++ []) t)
           → subΘTm Θloc [] m ≡ subst (Cᵗ Γ Δᵍ Δ t) (++-identityʳ Θloc) m
  subΘ-idᵗ Θloc (varᵗ x) rewrite ∈-id Θloc x = pushVarᵗ (++-identityʳ Θloc) x
  subΘ-idᵗ Θloc unit̂     = pushUnit (++-identityʳ Θloc)
  subΘ-idᵗ Θloc (bool̂ b) = pushBool (++-identityʳ Θloc) b
  subΘ-idᵗ Θloc (nat̂ m)  = pushNat (++-identityʳ Θloc) m
  subΘ-idᵗ Θloc (uniq̂ m) = pushUniq (++-identityʳ Θloc) m
  subΘ-idᵗ Θloc (pairᵗ a b) =
    trans (cong₂ pairᵗ (subΘ-idᵗ Θloc a) (subΘ-idᵗ Θloc b))
          (pushPair (++-identityʳ Θloc) a b)
  subΘ-idᵗ Θloc (fstᵗ p) =
    trans (cong fstᵗ (subΘ-idᵗ Θloc p)) (pushFst (++-identityʳ Θloc) p)
  subΘ-idᵗ Θloc (sndᵗ p) =
    trans (cong sndᵗ (subΘ-idᵗ Θloc p)) (pushSnd (++-identityʳ Θloc) p)
  subΘ-idᵗ Θloc (inlᵗ a) =
    trans (cong inlᵗ (subΘ-idᵗ Θloc a)) (pushInl (++-identityʳ Θloc) a)
  subΘ-idᵗ Θloc (inrᵗ a) =
    trans (cong inrᵗ (subΘ-idᵗ Θloc a)) (pushInr (++-identityʳ Θloc) a)
  subΘ-idᵗ Θloc (caseᵗ {s = s} {t = t} sc l r) =
    trans (cong₃ caseᵗ (subΘ-idᵗ Θloc sc)
            (trans (subΘ-idᵗ (s ∷ Θloc) l) (shift (++-identityʳ Θloc) l))
            (trans (subΘ-idᵗ (t ∷ Θloc) r) (shift (++-identityʳ Θloc) r)))
          (pushCase (++-identityʳ Θloc) sc l r)
  subΘ-idᵗ Θloc (ifᵗ c a b) =
    trans (cong₃ ifᵗ (subΘ-idᵗ Θloc c) (subΘ-idᵗ Θloc a) (subΘ-idᵗ Θloc b))
          (pushIf (++-identityʳ Θloc) c a b)
  subΘ-idᵗ Θloc (primᵗ op a) =
    trans (cong (primᵗ op) (subΘ-idᵗ Θloc a)) (pushPrim (++-identityʳ Θloc) op a)
  subΘ-idᵗ Θloc nilᵗ =
    pushNilᵗ (++-identityʳ Θloc)
  subΘ-idᵗ Θloc (consᵗ a as) =
    trans (cong₂ consᵗ (subΘ-idᵗ Θloc a) (subΘ-idᵗ Θloc as))
          (pushConsᵗ (++-identityʳ Θloc) a as)
  subΘ-idᵗ Θloc (foldᵗ {s = s} {u = u} l z f) =
    trans (cong₃ foldᵗ (subΘ-idᵗ Θloc l) (subΘ-idᵗ Θloc z)
            (trans (subΘ-idᵗ (s ∷ u ∷ Θloc) f)
                   (shift2 (++-identityʳ Θloc) f)))
          (pushFoldᵗ (++-identityʳ Θloc) l z f)
  subΘ-idᵗ Θloc (strmᵗ e) =
    trans (cong strmᵗ (subΘ-idᵉ Θloc e)) (pushStrm (++-identityʳ Θloc) e)

  subΘ-idᵗˢ : (Θloc : List Ty) (ts : List (Tm Γ Δᵍ Δ (Θloc ++ []) t))
            → subΘTms Θloc [] ts ≡ subst (Cˢ Γ Δᵍ Δ t) (++-identityʳ Θloc) ts
  subΘ-idᵗˢ Θloc []       = pushNilˢ (++-identityʳ Θloc)
  subΘ-idᵗˢ Θloc (x ∷ xs) =
    trans (cong₂ _∷_ (subΘ-idᵗ Θloc x) (subΘ-idᵗˢ Θloc xs))
          (pushConsˢ (++-identityʳ Θloc) x xs)

------------------------------------------------------------------
-- THE CONSUMER'S INSTANCE, where the transport is `refl`.
------------------------------------------------------------------

subΘ-id-exp : (e : Exp Γ Δᵍ Δ [] t) → subΘExp [] [] e ≡ e
subΘ-id-exp e = subΘ-idᵉ [] e
