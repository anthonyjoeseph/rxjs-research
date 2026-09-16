------------------------------------------------------------------
-- SUBSTITUTING TWICE IS SUBSTITUTING ONCE WITH THE CONCATENATION.
------------------------------------------------------------------

-- WHAT THE EMBEDDING ARM ACTUALLY OWES.  Reading a stream literal
-- does not descend into it -- it CLOSES the expression against the
-- ambient environment -- so the arm where the term face hands back
-- to the expression face is not an induction hypothesis about terms
-- at all.  It is a claim about two substitutions in sequence.  The
-- degenerate end of it, where the ambient environment is EMPTY and
-- the outer substitution must do nothing, is already proven on the
-- identity face; what is left is the composition proper.
--
-- WHY IT LIVES IN A MODULE OF ITS OWN rather than beside the
-- identity walk it mirrors or the renaming shelf it will spend.  It
-- is a walk over the whole expression grammar, so discharging it
-- grows a mutual block that every consumer of either would then be
-- rebuilt behind; nothing but the evaluation agreement needs it, and
-- this is the shallowest module that reaches it.
module Rx.Subst-Compose where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; [])
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Rx.Exp
  using ( Ty; Ctx; Exp; Tm; Val; subΘExp; subΘTm; subΘTms
        ; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ
        ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ
        ; varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ
        ; caseᵗ; ifᵗ; primᵗ; strmᵗ; _×ᵗ_; nilᵗ; consᵗ; foldᵗ; listᵗ
        ; renTm; wkTm; reify; lookupEnv )
open import Rx.Subst-Transport
  using ( Cᵉ; Cᵗ; Cˢ; shift; cong₃
        ; pushInput; pushEmpty; pushVarᵉ; pushOf; pushMap; pushTake; pushScan
        ; pushMerge; pushSwitch; pushExhaust; pushMu; pushDefer
        ; pushUnit; pushBool; pushNat; pushPair; pushFst; pushSnd
        ; pushInl; pushInr; pushCase; pushIf; pushPrim; pushStrm
        ; pushNilˢ; pushConsˢ; pushVarᵗ; pushHere; pushThere
        ; pushNilᵗ; pushConsᵗ; pushFoldᵗ; shift2 )
open import Rx.Subst-Split
  using (split; isˡ; isʳ; sub-left; sub-right; lookup-left; lookup-right)
open import Rx.Subst-Renaming using (sub-renᵗ)
open import Rx.Subst-Ren-Fuse using (sub-fixᵗ)

private
  variable
    n           : ℕ
    Γ           : Ctx n
    Δᵍ Δ        : List Ty
    Θloc Θsub   : List Ty
    s t         : Ty

------------------------------------------------------------------
-- THE VARIABLE ARM, WHICH IS THE WHOLE OF THE CONTENT.  Every other
-- arm is a congruence carrying the same cast through a constructor;
-- here the two substituters each split the telescope at a different
-- point, and the claim is that the two splits agree.  A variable the
-- OUTER telescope covers is read by neither; one the inner half
-- covers is taken by the inner substituter and must then survive the
-- outer one; and one the substituted tail covers is taken by
-- whichever of the two owns it, which on the right is the
-- concatenated environment.  The induction is on the outer telescope,
-- and its step needs no walk of its own: a `there` is a RENAMING that
-- fixes the substituted half, so the fusion face already says both
-- substituters commute with it.
------------------------------------------------------------------

comp-var : (Θout : List Ty) (ρ : All (Val Γ) Θloc) (σ : All (Val Γ) Θsub)
           (x : t ∈ ((Θout ++ Θloc) ++ Θsub))
         → subΘTm {Δᵍ = Δᵍ} {Δ} Θout ρ (subΘTm (Θout ++ Θloc) σ (varᵗ x))
             ≡ subΘTm Θout (++⁺ ρ σ)
                 (varᵗ (subst (_ ∈_) (++-assoc Θout Θloc Θsub) x))
comp-var {Θloc = Θl} {Θsub = Θs} [] ρ σ x with split Θl Θs x
... | isˡ y e =
  trans (cong (subΘTm [] ρ) (sub-left Θl σ x y e))
        (cong (λ v → wkTm (reify v)) (sym (lookup-left Θl ρ σ x y e)))
... | isʳ z e =
  trans (cong (subΘTm [] ρ) (sub-right Θl σ x z e))
        (trans (sub-renᵗ {Θloc = []} {ρt = λ ()} ρ (λ ())
                  (reify (lookupEnv σ z)))
               (cong (λ v → wkTm (reify v)) (sym (lookup-right Θl ρ σ x z e))))
comp-var {Θloc = Θl} {Θsub = Θs} (a ∷ Θo) ρ σ (here refl) =
  sym (cong (λ q → subΘTm (a ∷ Θo) (++⁺ ρ σ) (varᵗ q))
            (pushHere (++-assoc Θo Θl Θs) refl))
comp-var {Θloc = Θl} {Θsub = Θs} (a ∷ Θo) ρ σ (there p) =
  trans (cong (subΘTm (a ∷ Θo) ρ)
          (sub-fixᵗ (Θo ++ Θl) (a ∷ (Θo ++ Θl))
            {ρg = λ w → w} {ρd = λ w → w} {ρ⁺ = there} {ρa = there}
            σ (λ _ → refl) (λ _ → refl) (varᵗ p)))
  (trans (sub-fixᵗ Θo (a ∷ Θo)
            {ρg = λ w → w} {ρd = λ w → w} {ρ⁺ = there} {ρa = there}
            ρ (λ _ → refl) (λ _ → refl) (subΘTm (Θo ++ Θl) σ (varᵗ p)))
  (trans (cong (renTm (λ w → w) (λ w → w) there) (comp-var Θo ρ σ p))
  (trans (sym (sub-fixᵗ Θo (a ∷ Θo)
                {ρg = λ w → w} {ρd = λ w → w} {ρ⁺ = there} {ρa = there}
                (++⁺ ρ σ) (λ _ → refl) (λ _ → refl)
                (varᵗ (subst (_ ∈_) (++-assoc Θo Θl Θs) p))))
         (sym (cong (λ q → subΘTm (a ∷ Θo) (++⁺ ρ σ) (varᵗ q))
                    (pushThere (++-assoc Θo Θl Θs) p))))))

subΘ-comp-var : (Θout : List Ty) (ρ : All (Val Γ) Θloc)
                (σ : All (Val Γ) Θsub)
                (x : t ∈ ((Θout ++ Θloc) ++ Θsub))
              → subΘTm {Δᵍ = Δᵍ} {Δ} Θout ρ
                  (subΘTm (Θout ++ Θloc) σ (varᵗ x))
                  ≡ subΘTm Θout (++⁺ ρ σ)
                      (subst (Cᵗ Γ Δᵍ Δ t) (++-assoc Θout Θloc Θsub) (varᵗ x))
subΘ-comp-var {Θloc = Θl} {Θsub = Θs} Θo ρ σ x =
  trans (comp-var Θo ρ σ x)
        (cong (subΘTm Θo (++⁺ ρ σ)) (pushVarᵗ (++-assoc Θo Θl Θs) x))

------------------------------------------------------------------
-- THE WALK, AT THREE TELESCOPES.  The statement the consumer wants
-- sits at an empty OUTER telescope, and the induction cannot stay
-- there: every binding arm extends the telescope both substituters
-- are standing at, and it extends it on the LEFT of both halves.  So
-- the general form carries an outer telescope they share, the two
-- sides then sit at differently-bracketed appends, and the cast
-- between them is pushed through every constructor -- exactly as the
-- identity face pays one for the empty append it cannot reduce.
------------------------------------------------------------------

mutual
  subΘ-compᵍᵉ : (Θout : List Ty) (ρ : All (Val Γ) Θloc)
                (σ : All (Val Γ) Θsub)
                (e : Exp Γ Δᵍ Δ ((Θout ++ Θloc) ++ Θsub) t)
              → subΘExp Θout ρ (subΘExp (Θout ++ Θloc) σ e)
                  ≡ subΘExp Θout (++⁺ ρ σ)
                      (subst (Cᵉ Γ Δᵍ Δ t) (++-assoc Θout Θloc Θsub) e)
  subΘ-compᵍᵉ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (input i) =
    cong (subΘExp Θo (++⁺ ρ σ)) (pushInput (++-assoc Θo Θl Θs) i)
  subΘ-compᵍᵉ {Θloc = Θl} {Θsub = Θs} Θo ρ σ emptyᵉ =
    cong (subΘExp Θo (++⁺ ρ σ)) (pushEmpty (++-assoc Θo Θl Θs))
  subΘ-compᵍᵉ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (varᵉ x) =
    cong (subΘExp Θo (++⁺ ρ σ)) (pushVarᵉ (++-assoc Θo Θl Θs) x)
  subΘ-compᵍᵉ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (ofᵉ ts) =
    trans (cong ofᵉ (subΘ-compᵍᵗˢ Θo ρ σ ts))
          (cong (subΘExp Θo (++⁺ ρ σ)) (pushOf (++-assoc Θo Θl Θs) ts))
  subΘ-compᵍᵉ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (mapᵉ {s = s} f e) =
    trans (cong₂ mapᵉ
            (trans (subΘ-compᵍᵗ (s ∷ Θo) ρ σ f)
                   (cong (subΘTm (s ∷ Θo) (++⁺ ρ σ)) (shift (++-assoc Θo Θl Θs) f)))
            (subΘ-compᵍᵉ Θo ρ σ e))
          (cong (subΘExp Θo (++⁺ ρ σ)) (pushMap (++-assoc Θo Θl Θs) f e))
  subΘ-compᵍᵉ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (takeᵉ m e) =
    trans (cong₂ takeᵉ (subΘ-compᵍᵗ Θo ρ σ m) (subΘ-compᵍᵉ Θo ρ σ e))
          (cong (subΘExp Θo (++⁺ ρ σ)) (pushTake (++-assoc Θo Θl Θs) m e))
  subΘ-compᵍᵉ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (scanᵉ {s = s} {t = t} f i e) =
    trans (cong₃ scanᵉ
            (trans (subΘ-compᵍᵗ ((t ×ᵗ s) ∷ Θo) ρ σ f)
                   (cong (subΘTm ((t ×ᵗ s) ∷ Θo) (++⁺ ρ σ))
                         (shift (++-assoc Θo Θl Θs) f)))
            (subΘ-compᵍᵗ Θo ρ σ i) (subΘ-compᵍᵉ Θo ρ σ e))
          (cong (subΘExp Θo (++⁺ ρ σ)) (pushScan (++-assoc Θo Θl Θs) f i e))
  subΘ-compᵍᵉ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (mergeAllᵉ lim e) =
    trans (cong (mergeAllᵉ lim) (subΘ-compᵍᵉ Θo ρ σ e))
          (cong (subΘExp Θo (++⁺ ρ σ)) (pushMerge (++-assoc Θo Θl Θs) lim e))
  subΘ-compᵍᵉ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (switchAllᵉ e) =
    trans (cong switchAllᵉ (subΘ-compᵍᵉ Θo ρ σ e))
          (cong (subΘExp Θo (++⁺ ρ σ)) (pushSwitch (++-assoc Θo Θl Θs) e))
  subΘ-compᵍᵉ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (exhaustAllᵉ e) =
    trans (cong exhaustAllᵉ (subΘ-compᵍᵉ Θo ρ σ e))
          (cong (subΘExp Θo (++⁺ ρ σ)) (pushExhaust (++-assoc Θo Θl Θs) e))
  subΘ-compᵍᵉ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (μᵉ e) =
    trans (cong μᵉ (subΘ-compᵍᵉ Θo ρ σ e))
          (cong (subΘExp Θo (++⁺ ρ σ)) (pushMu (++-assoc Θo Θl Θs) e))
  subΘ-compᵍᵉ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (deferᵉ e) =
    trans (cong deferᵉ (subΘ-compᵍᵉ Θo ρ σ e))
          (cong (subΘExp Θo (++⁺ ρ σ)) (pushDefer (++-assoc Θo Θl Θs) e))

  subΘ-compᵍᵗ : (Θout : List Ty) (ρ : All (Val Γ) Θloc)
                (σ : All (Val Γ) Θsub)
                (m : Tm Γ Δᵍ Δ ((Θout ++ Θloc) ++ Θsub) t)
              → subΘTm Θout ρ (subΘTm (Θout ++ Θloc) σ m)
                  ≡ subΘTm Θout (++⁺ ρ σ)
                      (subst (Cᵗ Γ Δᵍ Δ t) (++-assoc Θout Θloc Θsub) m)
  subΘ-compᵍᵗ Θo ρ σ (varᵗ x) = subΘ-comp-var Θo ρ σ x
  subΘ-compᵍᵗ {Θloc = Θl} {Θsub = Θs} Θo ρ σ unit̂ =
    cong (subΘTm Θo (++⁺ ρ σ)) (pushUnit (++-assoc Θo Θl Θs))
  subΘ-compᵍᵗ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (bool̂ b) =
    cong (subΘTm Θo (++⁺ ρ σ)) (pushBool (++-assoc Θo Θl Θs) b)
  subΘ-compᵍᵗ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (nat̂ m) =
    cong (subΘTm Θo (++⁺ ρ σ)) (pushNat (++-assoc Θo Θl Θs) m)
  subΘ-compᵍᵗ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (pairᵗ a b) =
    trans (cong₂ pairᵗ (subΘ-compᵍᵗ Θo ρ σ a) (subΘ-compᵍᵗ Θo ρ σ b))
          (cong (subΘTm Θo (++⁺ ρ σ)) (pushPair (++-assoc Θo Θl Θs) a b))
  subΘ-compᵍᵗ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (fstᵗ p) =
    trans (cong fstᵗ (subΘ-compᵍᵗ Θo ρ σ p))
          (cong (subΘTm Θo (++⁺ ρ σ)) (pushFst (++-assoc Θo Θl Θs) p))
  subΘ-compᵍᵗ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (sndᵗ p) =
    trans (cong sndᵗ (subΘ-compᵍᵗ Θo ρ σ p))
          (cong (subΘTm Θo (++⁺ ρ σ)) (pushSnd (++-assoc Θo Θl Θs) p))
  subΘ-compᵍᵗ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (inlᵗ a) =
    trans (cong inlᵗ (subΘ-compᵍᵗ Θo ρ σ a))
          (cong (subΘTm Θo (++⁺ ρ σ)) (pushInl (++-assoc Θo Θl Θs) a))
  subΘ-compᵍᵗ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (inrᵗ a) =
    trans (cong inrᵗ (subΘ-compᵍᵗ Θo ρ σ a))
          (cong (subΘTm Θo (++⁺ ρ σ)) (pushInr (++-assoc Θo Θl Θs) a))
  subΘ-compᵍᵗ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (caseᵗ {s = s} {t = t} sc l r) =
    trans (cong₃ caseᵗ (subΘ-compᵍᵗ Θo ρ σ sc)
            (trans (subΘ-compᵍᵗ (s ∷ Θo) ρ σ l)
                   (cong (subΘTm (s ∷ Θo) (++⁺ ρ σ)) (shift (++-assoc Θo Θl Θs) l)))
            (trans (subΘ-compᵍᵗ (t ∷ Θo) ρ σ r)
                   (cong (subΘTm (t ∷ Θo) (++⁺ ρ σ)) (shift (++-assoc Θo Θl Θs) r))))
          (cong (subΘTm Θo (++⁺ ρ σ)) (pushCase (++-assoc Θo Θl Θs) sc l r))
  subΘ-compᵍᵗ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (ifᵗ c a b) =
    trans (cong₃ ifᵗ (subΘ-compᵍᵗ Θo ρ σ c) (subΘ-compᵍᵗ Θo ρ σ a)
                     (subΘ-compᵍᵗ Θo ρ σ b))
          (cong (subΘTm Θo (++⁺ ρ σ)) (pushIf (++-assoc Θo Θl Θs) c a b))
  subΘ-compᵍᵗ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (primᵗ op a) =
    trans (cong (primᵗ op) (subΘ-compᵍᵗ Θo ρ σ a))
          (cong (subΘTm Θo (++⁺ ρ σ)) (pushPrim (++-assoc Θo Θl Θs) op a))
  subΘ-compᵍᵗ {Θloc = Θl} {Θsub = Θs} Θo ρ σ nilᵗ =
    cong (subΘTm Θo (++⁺ ρ σ)) (pushNilᵗ (++-assoc Θo Θl Θs))
  subΘ-compᵍᵗ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (consᵗ a as) =
    trans (cong₂ consᵗ (subΘ-compᵍᵗ Θo ρ σ a) (subΘ-compᵍᵗ Θo ρ σ as))
          (cong (subΘTm Θo (++⁺ ρ σ)) (pushConsᵗ (++-assoc Θo Θl Θs) a as))
  subΘ-compᵍᵗ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (foldᵗ {s = s} {u = u} l z f) =
    trans (cong₃ foldᵗ (subΘ-compᵍᵗ Θo ρ σ l) (subΘ-compᵍᵗ Θo ρ σ z)
            (trans (subΘ-compᵍᵗ (s ∷ u ∷ Θo) ρ σ f)
                   (cong (subΘTm (s ∷ u ∷ Θo) (++⁺ ρ σ))
                         (shift2 (++-assoc Θo Θl Θs) f))))
          (cong (subΘTm Θo (++⁺ ρ σ)) (pushFoldᵗ (++-assoc Θo Θl Θs) l z f))
  subΘ-compᵍᵗ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (strmᵗ e) =
    trans (cong strmᵗ (subΘ-compᵍᵉ Θo ρ σ e))
          (cong (subΘTm Θo (++⁺ ρ σ)) (pushStrm (++-assoc Θo Θl Θs) e))

  subΘ-compᵍᵗˢ : (Θout : List Ty) (ρ : All (Val Γ) Θloc)
                 (σ : All (Val Γ) Θsub)
                 (ts : List (Tm Γ Δᵍ Δ ((Θout ++ Θloc) ++ Θsub) t))
               → subΘTms Θout ρ (subΘTms (Θout ++ Θloc) σ ts)
                   ≡ subΘTms Θout (++⁺ ρ σ)
                       (subst (Cˢ Γ Δᵍ Δ t) (++-assoc Θout Θloc Θsub) ts)
  subΘ-compᵍᵗˢ {Θloc = Θl} {Θsub = Θs} Θo ρ σ [] =
    cong (subΘTms Θo (++⁺ ρ σ)) (pushNilˢ (++-assoc Θo Θl Θs))
  subΘ-compᵍᵗˢ {Θloc = Θl} {Θsub = Θs} Θo ρ σ (x ∷ xs) =
    trans (cong₂ _∷_ (subΘ-compᵍᵗ Θo ρ σ x) (subΘ-compᵍᵗˢ Θo ρ σ xs))
          (cong (subΘTms Θo (++⁺ ρ σ)) (pushConsˢ (++-assoc Θo Θl Θs) x xs))

------------------------------------------------------------------
-- THE CONSUMER'S INSTANCE, where both bracketings are the same list
-- and the transport is `refl`.
------------------------------------------------------------------

-- TWO SUBSTITUTIONS COMPOSE.  The inner one owns the tail of the
-- telescope and reifies what it takes; the outer one owns what is
-- left and must leave those reified copies alone.
subΘ-compᵉ : (ρ : All (Val Γ) Θloc) (σ : All (Val Γ) Θsub)
             (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t)
           → subΘExp [] ρ (subΘExp Θloc σ e) ≡ subΘExp [] (++⁺ ρ σ) e
subΘ-compᵉ ρ σ e = subΘ-compᵍᵉ [] ρ σ e
