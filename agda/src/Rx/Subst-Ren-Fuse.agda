------------------------------------------------------------------
-- TWO RENAMINGS IN SEQUENCE, AND THE ENVIRONMENT SURVIVING ONE.
------------------------------------------------------------------

-- WHAT THE SUBSTITUTER NEEDS FROM A RENAMING IT MEETS.  When a
-- renaming is carried past the environment substituter, the two
-- halves of the telescope are treated differently and each needs its
-- own premise: on the LOCAL half the renaming may do whatever it
-- likes, since the substituter merely relabels there, while on the
-- SUBSTITUTED half it must be the identity, since the substituter is
-- about to replace those variables by closed values that carry no
-- position to relabel.  Both premises are POINTWISE, so nothing here
-- needs extensionality and the closure lemmas are two lines each.
--
-- AND THE VALUE THE SUBSTITUTER DROPS IN IS WHY FUSION COMES FIRST.
-- At a variable it owns, the substituter emits a reified value
-- WEAKENED from the empty contexts, and the renaming on the other
-- side of the equation then has to be shown inert on it.  That is a
-- statement about two renamings in sequence rather than about
-- substitution, so it is proven here on its own: a renaming composed
-- after a weakening is a weakening, because both are the unique map
-- out of an empty context.
module Rx.Subst-Ren-Fuse where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁻∘++⁺)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Rx.Exp
  using ( Ty; Ctx; Exp; Tm; Val; Ren∈; ext∈; ++Ren; renExp; renTm; renTms
        ; subΘExp; subΘTm; subΘTms; wkTm; reify; lookupEnv; _×ᵗ_; listᵗ
        ; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; liftᵉ; mergeAllᵉ; switchAllᵉ
        ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ
        ; varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ
        ; ifᵗ; primᵗ; strmᵗ; nilᵗ; consᵗ; foldᵗ )
open import Rx.Subst-Transport using (Cᵉ; cong₃)
open import Rx.Subst-Renaming using (Idᵖ; ren-idᵉ)
open import Rx.Subst-Split
  using (isˡ; isʳ; split; left-back; right-back; sub-left; sub-right
        ; ++Ren-l; ++Ren-r)

private
  variable
    n                  : ℕ
    Γ                  : Ctx n
    Δᵍ Δᵍ′ Δᵍ″ Δ Δ′ Δ″ : List Ty
    Θ Θ′ Θ″ Θsub       : List Ty
    s t u              : Ty

------------------------------------------------------------------
-- COMPOSITION, POINTWISE, AND THE TWO WAYS A RENAMING GROWS.
------------------------------------------------------------------

Comp : {A B C : List Ty} → Ren∈ A B → Ren∈ B C → Ren∈ A C → Set
Comp {A = A} ρ σ τ = ∀ {u} (x : u ∈ A) → σ (ρ x) ≡ τ x

comp-ext : {A B C : List Ty} {ρ : Ren∈ A B} {σ : Ren∈ B C} {τ : Ren∈ A C}
         → Comp ρ σ τ → Comp (ext∈ {s = s} ρ) (ext∈ σ) (ext∈ τ)
comp-ext c (here refl) = refl
comp-ext c (there x)   = cong there (c x)

comp-++ : {A A′ A″ B B′ B″ : List Ty}
          {ρa : Ren∈ A A′} {σa : Ren∈ A′ A″} {τa : Ren∈ A A″}
          {ρb : Ren∈ B B′} {σb : Ren∈ B′ B″} {τb : Ren∈ B B″}
        → Comp ρa σa τa → Comp ρb σb τb
        → Comp (++Ren ρa ρb) (++Ren σa σb) (++Ren τa τb)
comp-++ {A = A} {A′ = A′} {A″ = A″} {ρa = ρa} {σa = σa} {τa = τa}
        {ρb = ρb} {σb = σb} {τb = τb} ca cb x with split A _ x
... | isˡ a eq =
  trans (cong (++Ren σa σb) (++Ren-l ρa ρb x a eq))
    (trans (++Ren-l σa σb (∈-++⁺ˡ (ρa a)) (ρa a) (++⁻∘++⁺ A′ (inj₁ (ρa a))))
      (trans (cong ∈-++⁺ˡ (ca a)) (sym (++Ren-l τa τb x a eq))))
... | isʳ b eq =
  trans (cong (++Ren σa σb) (++Ren-r ρa ρb x b eq))
    (trans (++Ren-r σa σb (∈-++⁺ʳ A′ (ρb b)) (ρb b) (++⁻∘++⁺ A′ (inj₂ (ρb b))))
      (trans (cong (∈-++⁺ʳ A″) (cb b)) (sym (++Ren-r τa τb x b eq))))

------------------------------------------------------------------
-- RENAMING TWICE IS RENAMING ONCE.
------------------------------------------------------------------

mutual
  ren-∘ᵉ : {ρg : Ren∈ Δᵍ Δᵍ′} {σg : Ren∈ Δᵍ′ Δᵍ″} {τg : Ren∈ Δᵍ Δᵍ″}
           {ρd : Ren∈ Δ Δ′} {σd : Ren∈ Δ′ Δ″} {τd : Ren∈ Δ Δ″}
           {ρt : Ren∈ Θ Θ′} {σt : Ren∈ Θ′ Θ″} {τt : Ren∈ Θ Θ″}
         → Comp ρg σg τg → Comp ρd σd τd → Comp ρt σt τt
         → (e : Exp Γ Δᵍ Δ Θ t)
         → renExp σg σd σt (renExp ρg ρd ρt e) ≡ renExp τg τd τt e
  ren-∘ᵉ cg cd ct (input i)  = refl
  ren-∘ᵉ cg cd ct emptyᵉ     = refl
  ren-∘ᵉ cg cd ct (varᵉ x)   = cong varᵉ (cd x)
  ren-∘ᵉ cg cd ct (ofᵉ ts)   = cong ofᵉ (ren-∘ᵗˢ cg cd ct ts)
  ren-∘ᵉ cg cd ct (mapᵉ f e) =
    cong₂ mapᵉ (ren-∘ᵗ cg cd (comp-ext ct) f) (ren-∘ᵉ cg cd ct e)
  ren-∘ᵉ cg cd ct (takeᵉ m e) =
    cong₂ takeᵉ (ren-∘ᵗ cg cd ct m) (ren-∘ᵉ cg cd ct e)
  ren-∘ᵉ cg cd ct (scanᵉ f i e) =
    cong₃ scanᵉ (ren-∘ᵗ cg cd (comp-ext ct) f) (ren-∘ᵗ cg cd ct i)
                (ren-∘ᵉ cg cd ct e)
  ren-∘ᵉ cg cd ct (liftᵉ f i e) =
    cong₃ liftᵉ (ren-∘ᵗ cg cd (comp-ext ct) f) (ren-∘ᵗ cg cd ct i)
                (ren-∘ᵉ cg cd ct e)
  ren-∘ᵉ cg cd ct (mergeAllᵉ lim e) = cong (mergeAllᵉ lim) (ren-∘ᵉ cg cd ct e)
  ren-∘ᵉ cg cd ct (switchAllᵉ e)    = cong switchAllᵉ (ren-∘ᵉ cg cd ct e)
  ren-∘ᵉ cg cd ct (exhaustAllᵉ e)   = cong exhaustAllᵉ (ren-∘ᵉ cg cd ct e)
  ren-∘ᵉ cg cd ct (μᵉ e)     = cong μᵉ (ren-∘ᵉ (comp-ext cg) cd ct e)
  ren-∘ᵉ {ρg = ρg} {σg = σg} {τg = τg} {ρd = ρd} {σd = σd} {τd = τd}
         cg cd ct (deferᵉ e) =
    cong deferᵉ (ren-∘ᵉ (λ ())
      (comp-++ {ρa = ρg} {σa = σg} {τa = τg} {ρb = ρd} {σb = σd} {τb = τd}
               cg cd) ct e)

  ren-∘ᵗ : {ρg : Ren∈ Δᵍ Δᵍ′} {σg : Ren∈ Δᵍ′ Δᵍ″} {τg : Ren∈ Δᵍ Δᵍ″}
           {ρd : Ren∈ Δ Δ′} {σd : Ren∈ Δ′ Δ″} {τd : Ren∈ Δ Δ″}
           {ρt : Ren∈ Θ Θ′} {σt : Ren∈ Θ′ Θ″} {τt : Ren∈ Θ Θ″}
         → Comp ρg σg τg → Comp ρd σd τd → Comp ρt σt τt
         → (m : Tm Γ Δᵍ Δ Θ t)
         → renTm σg σd σt (renTm ρg ρd ρt m) ≡ renTm τg τd τt m
  ren-∘ᵗ cg cd ct (varᵗ x)    = cong varᵗ (ct x)
  ren-∘ᵗ cg cd ct unit̂        = refl
  ren-∘ᵗ cg cd ct (bool̂ b)    = refl
  ren-∘ᵗ cg cd ct (nat̂ m)     = refl
  ren-∘ᵗ cg cd ct (pairᵗ a b) =
    cong₂ pairᵗ (ren-∘ᵗ cg cd ct a) (ren-∘ᵗ cg cd ct b)
  ren-∘ᵗ cg cd ct (fstᵗ p) = cong fstᵗ (ren-∘ᵗ cg cd ct p)
  ren-∘ᵗ cg cd ct (sndᵗ p) = cong sndᵗ (ren-∘ᵗ cg cd ct p)
  ren-∘ᵗ cg cd ct (inlᵗ a) = cong inlᵗ (ren-∘ᵗ cg cd ct a)
  ren-∘ᵗ cg cd ct (inrᵗ a) = cong inrᵗ (ren-∘ᵗ cg cd ct a)
  ren-∘ᵗ cg cd ct (caseᵗ sc l r) =
    cong₃ caseᵗ (ren-∘ᵗ cg cd ct sc) (ren-∘ᵗ cg cd (comp-ext ct) l)
                (ren-∘ᵗ cg cd (comp-ext ct) r)
  ren-∘ᵗ cg cd ct (ifᵗ c a b) =
    cong₃ ifᵗ (ren-∘ᵗ cg cd ct c) (ren-∘ᵗ cg cd ct a) (ren-∘ᵗ cg cd ct b)
  ren-∘ᵗ cg cd ct (primᵗ op a) = cong (primᵗ op) (ren-∘ᵗ cg cd ct a)
  ren-∘ᵗ cg cd ct nilᵗ          = refl
  ren-∘ᵗ cg cd ct (consᵗ a as)  =
    cong₂ consᵗ (ren-∘ᵗ cg cd ct a) (ren-∘ᵗ cg cd ct as)
  ren-∘ᵗ cg cd ct (foldᵗ l z f) =
    cong₃ foldᵗ (ren-∘ᵗ cg cd ct l) (ren-∘ᵗ cg cd ct z)
                (ren-∘ᵗ cg cd (comp-ext (comp-ext ct)) f)
  ren-∘ᵗ cg cd ct (strmᵗ e)    = cong strmᵗ (ren-∘ᵉ cg cd ct e)

  ren-∘ᵗˢ : {ρg : Ren∈ Δᵍ Δᵍ′} {σg : Ren∈ Δᵍ′ Δᵍ″} {τg : Ren∈ Δᵍ Δᵍ″}
            {ρd : Ren∈ Δ Δ′} {σd : Ren∈ Δ′ Δ″} {τd : Ren∈ Δ Δ″}
            {ρt : Ren∈ Θ Θ′} {σt : Ren∈ Θ′ Θ″} {τt : Ren∈ Θ Θ″}
          → Comp ρg σg τg → Comp ρd σd τd → Comp ρt σt τt
          → (ts : List (Tm Γ Δᵍ Δ Θ t))
          → renTms σg σd σt (renTms ρg ρd ρt ts) ≡ renTms τg τd τt ts
  ren-∘ᵗˢ cg cd ct []       = refl
  ren-∘ᵗˢ cg cd ct (x ∷ xs) =
    cong₂ _∷_ (ren-∘ᵗ cg cd ct x) (ren-∘ᵗˢ cg cd ct xs)

------------------------------------------------------------------
-- THE UNIQUE MAP OUT OF NOTHING, AND THE TWO FACTS IT BUYS.
------------------------------------------------------------------

noRen : {A : List Ty} → Ren∈ [] A
noRen ()

-- A RENAMING AFTER A WEAKENING IS THE WEAKENING.
ren-wkᵗ : {ρg : Ren∈ Δᵍ Δᵍ′} {ρd : Ren∈ Δ Δ′} {ρt : Ren∈ Θ Θ′}
          (m : Tm Γ [] [] [] u)
        → renTm ρg ρd ρt (wkTm m) ≡ wkTm m
ren-wkᵗ m = ren-∘ᵗ (λ ()) (λ ()) (λ ()) m

private
  idᵖ : {A : List Ty} → Idᵖ {A = A} (λ x → x)
  idᵖ _ = refl

-- AND THE TELESCOPE MAP OF A Θ-CLOSED EXPRESSION IS IMMATERIAL,
-- EVEN ACROSS A TRANSPORT OF THE TARGET: there is nothing for either
-- map to be applied to, so the two renamings agree pointwise and the
-- transport is the one the target's equation names.
ren-wk-Θ : {ρg : Ren∈ Δᵍ Δᵍ′} {ρd : Ren∈ Δ Δ′}
           (ρt : Ren∈ [] Θ′) (ρt′ : Ren∈ [] Θ″) (p : Θ′ ≡ Θ″)
           (e : Exp Γ Δᵍ Δ [] t)
         → subst (Cᵉ Γ Δᵍ′ Δ′ t) p (renExp ρg ρd ρt e) ≡ renExp ρg ρd ρt′ e
ren-wk-Θ {ρg = ρg} {ρd = ρd} ρt ρt′ refl e =
  trans (sym (ren-idᵉ idᵖ idᵖ idᵖ (renExp ρg ρd ρt e)))
        (ren-∘ᵉ {σg = λ x → x} {σd = λ x → x} {σt = λ x → x}
                (λ _ → refl) (λ _ → refl) (λ ()) e)

------------------------------------------------------------------
-- SUBSTITUTING PAST A RENAMING THAT FIXES THE SUBSTITUTED HALF.
------------------------------------------------------------------

FixL : (Θa Θb : List Ty) {Θsub : List Ty}
     → Ren∈ (Θa ++ Θsub) (Θb ++ Θsub) → Ren∈ Θa Θb → Set
FixL Θa Θb ρ⁺ ρa = ∀ {u} (y : u ∈ Θa) → ρ⁺ (∈-++⁺ˡ y) ≡ ∈-++⁺ˡ (ρa y)

FixR : (Θa Θb : List Ty) {Θsub : List Ty}
     → Ren∈ (Θa ++ Θsub) (Θb ++ Θsub) → Set
FixR Θa Θb {Θsub} ρ⁺ = ∀ {u} (z : u ∈ Θsub) → ρ⁺ (∈-++⁺ʳ Θa z) ≡ ∈-++⁺ʳ Θb z

fixL-ext : {Θa Θb : List Ty} {ρ⁺ : Ren∈ (Θa ++ Θsub) (Θb ++ Θsub)}
           {ρa : Ren∈ Θa Θb}
         → FixL Θa Θb ρ⁺ ρa → FixL (s ∷ Θa) (s ∷ Θb) (ext∈ ρ⁺) (ext∈ ρa)
fixL-ext fl (here refl) = refl
fixL-ext fl (there y)   = cong there (fl y)

fixR-ext : {Θa Θb : List Ty} {ρ⁺ : Ren∈ (Θa ++ Θsub) (Θb ++ Θsub)}
         → FixR Θa Θb ρ⁺ → FixR (s ∷ Θa) (s ∷ Θb) (ext∈ {s = s} ρ⁺)
fixR-ext fr z = cong there (fr z)

mutual
  sub-fixᵉ : (Θa Θb : List Ty) {ρg : Ren∈ Δᵍ Δᵍ′} {ρd : Ren∈ Δ Δ′}
             {ρ⁺ : Ren∈ (Θa ++ Θsub) (Θb ++ Θsub)} {ρa : Ren∈ Θa Θb}
             (σ : All (Val Γ) Θsub)
           → FixL Θa Θb ρ⁺ ρa → FixR Θa Θb ρ⁺
           → (e : Exp Γ Δᵍ Δ (Θa ++ Θsub) t)
           → subΘExp Θb σ (renExp ρg ρd ρ⁺ e)
               ≡ renExp ρg ρd ρa (subΘExp Θa σ e)
  sub-fixᵉ Θa Θb σ fl fr (input i) = refl
  sub-fixᵉ Θa Θb σ fl fr emptyᵉ    = refl
  sub-fixᵉ Θa Θb σ fl fr (varᵉ x)  = refl
  sub-fixᵉ Θa Θb σ fl fr (ofᵉ ts)  = cong ofᵉ (sub-fixᵗˢ Θa Θb σ fl fr ts)
  sub-fixᵉ Θa Θb {ρ⁺ = ρ⁺} σ fl fr (mapᵉ {s = s} f e) =
    cong₂ mapᵉ (sub-fixᵗ (s ∷ Θa) (s ∷ Θb) σ (fixL-ext fl) (fixR-ext {Θa = Θa} {Θb = Θb} {ρ⁺ = ρ⁺} fr) f)
               (sub-fixᵉ Θa Θb σ fl fr e)
  sub-fixᵉ Θa Θb σ fl fr (takeᵉ m e) =
    cong₂ takeᵉ (sub-fixᵗ Θa Θb σ fl fr m) (sub-fixᵉ Θa Θb σ fl fr e)
  sub-fixᵉ Θa Θb {ρ⁺ = ρ⁺} σ fl fr (scanᵉ {s = s} {t = w} f i e) =
    cong₃ scanᵉ
      (sub-fixᵗ ((w ×ᵗ s) ∷ Θa) ((w ×ᵗ s) ∷ Θb) σ (fixL-ext fl) (fixR-ext {Θa = Θa} {Θb = Θb} {ρ⁺ = ρ⁺} fr) f)
      (sub-fixᵗ Θa Θb σ fl fr i) (sub-fixᵉ Θa Θb σ fl fr e)
  sub-fixᵉ Θa Θb {ρ⁺ = ρ⁺} σ fl fr (liftᵉ {s = s} {u = w} f i e) =
    cong₃ liftᵉ
      (sub-fixᵗ ((w ×ᵗ listᵗ s) ∷ Θa) ((w ×ᵗ listᵗ s) ∷ Θb) σ (fixL-ext fl) (fixR-ext {Θa = Θa} {Θb = Θb} {ρ⁺ = ρ⁺} fr) f)
      (sub-fixᵗ Θa Θb σ fl fr i) (sub-fixᵉ Θa Θb σ fl fr e)
  sub-fixᵉ Θa Θb σ fl fr (mergeAllᵉ lim e) =
    cong (mergeAllᵉ lim) (sub-fixᵉ Θa Θb σ fl fr e)
  sub-fixᵉ Θa Θb σ fl fr (switchAllᵉ e)  =
    cong switchAllᵉ (sub-fixᵉ Θa Θb σ fl fr e)
  sub-fixᵉ Θa Θb σ fl fr (exhaustAllᵉ e) =
    cong exhaustAllᵉ (sub-fixᵉ Θa Θb σ fl fr e)
  sub-fixᵉ Θa Θb σ fl fr (μᵉ e)     = cong μᵉ (sub-fixᵉ Θa Θb σ fl fr e)
  sub-fixᵉ Θa Θb σ fl fr (deferᵉ e) = cong deferᵉ (sub-fixᵉ Θa Θb σ fl fr e)

  sub-fixᵗ : (Θa Θb : List Ty) {ρg : Ren∈ Δᵍ Δᵍ′} {ρd : Ren∈ Δ Δ′}
             {ρ⁺ : Ren∈ (Θa ++ Θsub) (Θb ++ Θsub)} {ρa : Ren∈ Θa Θb}
             (σ : All (Val Γ) Θsub)
           → FixL Θa Θb ρ⁺ ρa → FixR Θa Θb ρ⁺
           → (m : Tm Γ Δᵍ Δ (Θa ++ Θsub) t)
           → subΘTm Θb σ (renTm ρg ρd ρ⁺ m)
               ≡ renTm ρg ρd ρa (subΘTm Θa σ m)
  sub-fixᵗ Θa Θb {ρg = ρg} {ρd = ρd} {ρ⁺ = ρ⁺} {ρa = ρa} σ fl fr (varᵗ x)
    with split Θa _ x
  ... | isˡ y eq =
    trans (cong (λ w → subΘTm Θb σ (varᵗ w))
                (trans (cong ρ⁺ (sym (left-back x y eq))) (fl y)))
      (trans (sub-left Θb σ (∈-++⁺ˡ (ρa y)) (ρa y) (++⁻∘++⁺ Θb (inj₁ (ρa y))))
             (cong (renTm ρg ρd ρa) (sym (sub-left Θa σ x y eq))))
  ... | isʳ z eq =
    trans (cong (λ w → subΘTm Θb σ (varᵗ w))
                (trans (cong ρ⁺ (sym (right-back x z eq))) (fr z)))
      (trans (sub-right Θb σ (∈-++⁺ʳ Θb z) z (++⁻∘++⁺ Θb (inj₂ z)))
        (trans (sym (ren-wkᵗ (reify (lookupEnv σ z))))
               (cong (renTm ρg ρd ρa) (sym (sub-right Θa σ x z eq)))))
  sub-fixᵗ Θa Θb σ fl fr unit̂        = refl
  sub-fixᵗ Θa Θb σ fl fr (bool̂ b)    = refl
  sub-fixᵗ Θa Θb σ fl fr (nat̂ m)     = refl
  sub-fixᵗ Θa Θb σ fl fr (pairᵗ a b) =
    cong₂ pairᵗ (sub-fixᵗ Θa Θb σ fl fr a) (sub-fixᵗ Θa Θb σ fl fr b)
  sub-fixᵗ Θa Θb σ fl fr (fstᵗ p) = cong fstᵗ (sub-fixᵗ Θa Θb σ fl fr p)
  sub-fixᵗ Θa Θb σ fl fr (sndᵗ p) = cong sndᵗ (sub-fixᵗ Θa Θb σ fl fr p)
  sub-fixᵗ Θa Θb σ fl fr (inlᵗ a) = cong inlᵗ (sub-fixᵗ Θa Θb σ fl fr a)
  sub-fixᵗ Θa Θb σ fl fr (inrᵗ a) = cong inrᵗ (sub-fixᵗ Θa Θb σ fl fr a)
  sub-fixᵗ Θa Θb {ρ⁺ = ρ⁺} σ fl fr (caseᵗ {s = v} {t = w} sc l r) =
    cong₃ caseᵗ (sub-fixᵗ Θa Θb σ fl fr sc)
      (sub-fixᵗ (v ∷ Θa) (v ∷ Θb) σ (fixL-ext fl) (fixR-ext {Θa = Θa} {Θb = Θb} {ρ⁺ = ρ⁺} fr) l)
      (sub-fixᵗ (w ∷ Θa) (w ∷ Θb) σ (fixL-ext fl) (fixR-ext {Θa = Θa} {Θb = Θb} {ρ⁺ = ρ⁺} fr) r)
  sub-fixᵗ Θa Θb σ fl fr (ifᵗ c a b) =
    cong₃ ifᵗ (sub-fixᵗ Θa Θb σ fl fr c) (sub-fixᵗ Θa Θb σ fl fr a)
              (sub-fixᵗ Θa Θb σ fl fr b)
  sub-fixᵗ Θa Θb σ fl fr (primᵗ op a) =
    cong (primᵗ op) (sub-fixᵗ Θa Θb σ fl fr a)
  sub-fixᵗ Θa Θb σ fl fr nilᵗ         = refl
  sub-fixᵗ Θa Θb σ fl fr (consᵗ a as) =
    cong₂ consᵗ (sub-fixᵗ Θa Θb σ fl fr a) (sub-fixᵗ Θa Θb σ fl fr as)
  sub-fixᵗ Θa Θb {ρ⁺ = ρ⁺} σ fl fr (foldᵗ {s = v} {u = w} l z f) =
    cong₃ foldᵗ
      (sub-fixᵗ Θa Θb σ fl fr l)
      (sub-fixᵗ Θa Θb σ fl fr z)
      (sub-fixᵗ (v ∷ w ∷ Θa) (v ∷ w ∷ Θb) σ
         (fixL-ext (fixL-ext fl))
         (fixR-ext {Θa = w ∷ Θa} {Θb = w ∷ Θb} {ρ⁺ = ext∈ ρ⁺}
           (fixR-ext {Θa = Θa} {Θb = Θb} {ρ⁺ = ρ⁺} fr))
         f)
  sub-fixᵗ Θa Θb σ fl fr (strmᵗ e) = cong strmᵗ (sub-fixᵉ Θa Θb σ fl fr e)

  sub-fixᵗˢ : (Θa Θb : List Ty) {ρg : Ren∈ Δᵍ Δᵍ′} {ρd : Ren∈ Δ Δ′}
              {ρ⁺ : Ren∈ (Θa ++ Θsub) (Θb ++ Θsub)} {ρa : Ren∈ Θa Θb}
              (σ : All (Val Γ) Θsub)
            → FixL Θa Θb ρ⁺ ρa → FixR Θa Θb ρ⁺
            → (ts : List (Tm Γ Δᵍ Δ (Θa ++ Θsub) t))
            → subΘTms Θb σ (renTms ρg ρd ρ⁺ ts)
                ≡ renTms ρg ρd ρa (subΘTms Θa σ ts)
  sub-fixᵗˢ Θa Θb σ fl fr []       = refl
  sub-fixᵗˢ Θa Θb σ fl fr (x ∷ xs) =
    cong₂ _∷_ (sub-fixᵗ Θa Θb σ fl fr x) (sub-fixᵗˢ Θa Θb σ fl fr xs)
