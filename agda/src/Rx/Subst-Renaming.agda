------------------------------------------------------------------
-- A WEAKENED-FROM-CLOSED TERM IS INERT.
------------------------------------------------------------------

-- THE ONE FACT THREE LEAVES WERE WAITING ON.  Wherever the
-- substituter meets a variable it does not own, it emits the
-- environment value REIFIED and WEAKENED, and every statement about
-- carrying an environment past something then has to say that the
-- weakened copy is not touched again: reading a reified value back
-- ignores the ambient environment, two substitutions in sequence
-- agree with their concatenation, and the fixpoint peel commutes with
-- the environment.  All three are that one claim at different
-- call sites.  It is stated here over an arbitrary RENAMING into the
-- left half rather than over `wkTm`, because the induction walks
-- under binders and a closed subterm stops being closed the moment
-- it does -- what survives is that the renaming's image avoids the
-- half being substituted.  The maps are compared POINTWISE and never
-- as functions, so nothing here needs extensionality.
module Rx.Subst-Renaming where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁻∘++⁺)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; cong₂)

open import Rx.Exp
  using (Ty; Ctx; Exp; Tm; Val; Ren∈; ext∈; ++Ren; renExp; renTm; renTms; subΘExp; subΘTm; subΘTms;
  input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; liftᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
  varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
  nilᵗ; consᵗ; foldᵗ)
open import Rx.Subst-Transport using (cong₃)
open import Rx.Subst-Split using (left-back; right-back; sub-left)

private
  variable
    n          : ℕ
    Γ          : Ctx n
    Δᵍ Δᵍ′ Δ Δ′ : List Ty
    Θ Θloc Θsub : List Ty
    s t        : Ty

------------------------------------------------------------------
-- POINTWISE IDENTITY SURVIVES EVERY EXTENSION A RENAMING MAKES.
------------------------------------------------------------------

Idᵖ : ∀ {A : List Ty} → Ren∈ A A → Set
Idᵖ {A = A} ρ = ∀ {u} (x : u ∈ A) → ρ x ≡ x

ext-id : ∀ {A : List Ty} {ρ : Ren∈ A A} → Idᵖ ρ → Idᵖ (ext∈ {s = s} ρ)
ext-id i (here refl) = refl
ext-id i (there x)   = cong there (i x)

++Ren-id : ∀ {A B : List Ty} {ρa : Ren∈ A A} {ρb : Ren∈ B B}
         → Idᵖ ρa → Idᵖ ρb → Idᵖ (++Ren {A} {A} {B} {B} ρa ρb)
++Ren-id {A = A} {ρa = ρa} {ρb} ia ib x with ∈-++⁻ A x in eq
... | inj₁ y = trans (cong ∈-++⁺ˡ (ia y)) (left-back x y eq)
... | inj₂ z = trans (cong (∈-++⁺ʳ A) (ib z)) (right-back x z eq)

------------------------------------------------------------------
-- RENAMING BY POINTWISE-IDENTITY MAPS CHANGES NOTHING.  This is what
-- says a closed expression weakened into empty contexts is itself.
------------------------------------------------------------------

mutual
  ren-idᵉ : {ρg : Ren∈ Δᵍ Δᵍ} {ρd : Ren∈ Δ Δ} {ρt : Ren∈ Θ Θ}
          → Idᵖ ρg → Idᵖ ρd → Idᵖ ρt
          → (e : Exp Γ Δᵍ Δ Θ t) → renExp ρg ρd ρt e ≡ e
  ren-idᵉ ig id it (input i)  = refl
  ren-idᵉ ig id it emptyᵉ     = refl
  ren-idᵉ ig id it (varᵉ x)   = cong varᵉ (id x)
  ren-idᵉ ig id it (ofᵉ ts)   = cong ofᵉ (ren-idᵗˢ ig id it ts)
  ren-idᵉ ig id it (mapᵉ f e) =
    cong₂ mapᵉ (ren-idᵗ ig id (ext-id it) f) (ren-idᵉ ig id it e)
  ren-idᵉ ig id it (takeᵉ m e) =
    cong₂ takeᵉ (ren-idᵗ ig id it m) (ren-idᵉ ig id it e)
  ren-idᵉ ig id it (scanᵉ f i e) =
    cong₃ scanᵉ (ren-idᵗ ig id (ext-id it) f) (ren-idᵗ ig id it i)
                (ren-idᵉ ig id it e)
  ren-idᵉ ig id it (liftᵉ f i e) =
    cong₃ liftᵉ (ren-idᵗ ig id (ext-id it) f) (ren-idᵗ ig id it i)
                (ren-idᵉ ig id it e)
  ren-idᵉ ig id it (mergeAllᵉ lim e) =
    cong (mergeAllᵉ lim) (ren-idᵉ ig id it e)
  ren-idᵉ ig id it (switchAllᵉ e)  = cong switchAllᵉ (ren-idᵉ ig id it e)
  ren-idᵉ ig id it (exhaustAllᵉ e) = cong exhaustAllᵉ (ren-idᵉ ig id it e)
  ren-idᵉ ig id it (μᵉ e)     = cong μᵉ (ren-idᵉ (ext-id ig) id it e)
  ren-idᵉ ig id it (deferᵉ e) =
    cong deferᵉ (ren-idᵉ (λ ()) (++Ren-id ig id) it e)

  ren-idᵗ : {ρg : Ren∈ Δᵍ Δᵍ} {ρd : Ren∈ Δ Δ} {ρt : Ren∈ Θ Θ}
          → Idᵖ ρg → Idᵖ ρd → Idᵖ ρt
          → (m : Tm Γ Δᵍ Δ Θ t) → renTm ρg ρd ρt m ≡ m
  ren-idᵗ ig id it (varᵗ x)    = cong varᵗ (it x)
  ren-idᵗ ig id it unit̂        = refl
  ren-idᵗ ig id it (bool̂ b)    = refl
  ren-idᵗ ig id it (nat̂ m)     = refl
  ren-idᵗ ig id it (pairᵗ a b) =
    cong₂ pairᵗ (ren-idᵗ ig id it a) (ren-idᵗ ig id it b)
  ren-idᵗ ig id it (fstᵗ p)  = cong fstᵗ (ren-idᵗ ig id it p)
  ren-idᵗ ig id it (sndᵗ p)  = cong sndᵗ (ren-idᵗ ig id it p)
  ren-idᵗ ig id it (inlᵗ a)  = cong inlᵗ (ren-idᵗ ig id it a)
  ren-idᵗ ig id it (inrᵗ a)  = cong inrᵗ (ren-idᵗ ig id it a)
  ren-idᵗ ig id it (caseᵗ sc l r) =
    cong₃ caseᵗ (ren-idᵗ ig id it sc) (ren-idᵗ ig id (ext-id it) l)
                (ren-idᵗ ig id (ext-id it) r)
  ren-idᵗ ig id it (ifᵗ c a b) =
    cong₃ ifᵗ (ren-idᵗ ig id it c) (ren-idᵗ ig id it a) (ren-idᵗ ig id it b)
  ren-idᵗ ig id it (primᵗ op a) = cong (primᵗ op) (ren-idᵗ ig id it a)
  ren-idᵗ ig id it nilᵗ          = refl
  ren-idᵗ ig id it (consᵗ a as)  =
    cong₂ consᵗ (ren-idᵗ ig id it a) (ren-idᵗ ig id it as)
  ren-idᵗ ig id it (foldᵗ l z f) =
    cong₃ foldᵗ (ren-idᵗ ig id it l) (ren-idᵗ ig id it z)
                (ren-idᵗ ig id (ext-id (ext-id it)) f)
  ren-idᵗ ig id it (strmᵗ e)    = cong strmᵗ (ren-idᵉ ig id it e)

  ren-idᵗˢ : {ρg : Ren∈ Δᵍ Δᵍ} {ρd : Ren∈ Δ Δ} {ρt : Ren∈ Θ Θ}
           → Idᵖ ρg → Idᵖ ρd → Idᵖ ρt
           → (ts : List (Tm Γ Δᵍ Δ Θ t)) → renTms ρg ρd ρt ts ≡ ts
  ren-idᵗˢ ig id it []       = refl
  ren-idᵗˢ ig id it (x ∷ xs) =
    cong₂ _∷_ (ren-idᵗ ig id it x) (ren-idᵗˢ ig id it xs)

------------------------------------------------------------------
-- SUBSTITUTING PAST A RENAMING THAT LANDS LEFT.  The environment
-- owns the right half of the telescope, the renaming's image is
-- entirely in the left, so the substituter never meets a variable it
-- owns and the renaming comes back unchanged.
------------------------------------------------------------------

Lands : ∀ {Θ Θloc Θsub} → Ren∈ Θ (Θloc ++ Θsub) → Ren∈ Θ Θloc → Set
Lands {Θ = Θ} {Θloc} ρ⁺ ρt = ∀ {u} (x : u ∈ Θ) → ρ⁺ x ≡ ∈-++⁺ˡ (ρt x)

lands-ext : {ρ⁺ : Ren∈ Θ (Θloc ++ Θsub)} {ρt : Ren∈ Θ Θloc}
          → Lands ρ⁺ ρt → Lands (ext∈ {s = s} ρ⁺) (ext∈ ρt)
lands-ext ag (here refl) = refl
lands-ext ag (there x)   = cong there (ag x)

mutual
  sub-renᵉ : {ρg : Ren∈ Δᵍ Δᵍ′} {ρd : Ren∈ Δ Δ′}
             {ρt : Ren∈ Θ Θloc} {ρ⁺ : Ren∈ Θ (Θloc ++ Θsub)}
             (σ : All (Val Γ) Θsub) → Lands ρ⁺ ρt
           → (e : Exp Γ Δᵍ Δ Θ t)
           → subΘExp Θloc σ (renExp ρg ρd ρ⁺ e) ≡ renExp ρg ρd ρt e
  sub-renᵉ σ ag (input i)  = refl
  sub-renᵉ σ ag emptyᵉ     = refl
  sub-renᵉ σ ag (varᵉ x)   = refl
  sub-renᵉ σ ag (ofᵉ ts)   = cong ofᵉ (sub-renᵗˢ σ ag ts)
  sub-renᵉ σ ag (mapᵉ f e) =
    cong₂ mapᵉ (sub-renᵗ σ (lands-ext ag) f) (sub-renᵉ σ ag e)
  sub-renᵉ σ ag (takeᵉ m e) =
    cong₂ takeᵉ (sub-renᵗ σ ag m) (sub-renᵉ σ ag e)
  sub-renᵉ σ ag (scanᵉ f i e) =
    cong₃ scanᵉ (sub-renᵗ σ (lands-ext ag) f) (sub-renᵗ σ ag i)
                (sub-renᵉ σ ag e)
  sub-renᵉ σ ag (liftᵉ f i e) =
    cong₃ liftᵉ (sub-renᵗ σ (lands-ext ag) f) (sub-renᵗ σ ag i)
                (sub-renᵉ σ ag e)
  sub-renᵉ σ ag (mergeAllᵉ lim e) = cong (mergeAllᵉ lim) (sub-renᵉ σ ag e)
  sub-renᵉ σ ag (switchAllᵉ e)    = cong switchAllᵉ (sub-renᵉ σ ag e)
  sub-renᵉ σ ag (exhaustAllᵉ e)   = cong exhaustAllᵉ (sub-renᵉ σ ag e)
  sub-renᵉ σ ag (μᵉ e)     = cong μᵉ (sub-renᵉ σ ag e)
  sub-renᵉ σ ag (deferᵉ e) = cong deferᵉ (sub-renᵉ σ ag e)

  sub-renᵗ : {ρg : Ren∈ Δᵍ Δᵍ′} {ρd : Ren∈ Δ Δ′}
             {ρt : Ren∈ Θ Θloc} {ρ⁺ : Ren∈ Θ (Θloc ++ Θsub)}
             (σ : All (Val Γ) Θsub) → Lands ρ⁺ ρt
           → (m : Tm Γ Δᵍ Δ Θ t)
           → subΘTm Θloc σ (renTm ρg ρd ρ⁺ m) ≡ renTm ρg ρd ρt m
  sub-renᵗ {Θloc = Θloc} {ρt = ρt} σ ag (varᵗ x) =
    trans (cong (λ z → subΘTm Θloc σ (varᵗ z)) (ag x))
          (sub-left Θloc σ (∈-++⁺ˡ (ρt x)) (ρt x) (++⁻∘++⁺ Θloc (inj₁ (ρt x))))
  sub-renᵗ σ ag unit̂        = refl
  sub-renᵗ σ ag (bool̂ b)    = refl
  sub-renᵗ σ ag (nat̂ m)     = refl
  sub-renᵗ σ ag (pairᵗ a b) =
    cong₂ pairᵗ (sub-renᵗ σ ag a) (sub-renᵗ σ ag b)
  sub-renᵗ σ ag (fstᵗ p) = cong fstᵗ (sub-renᵗ σ ag p)
  sub-renᵗ σ ag (sndᵗ p) = cong sndᵗ (sub-renᵗ σ ag p)
  sub-renᵗ σ ag (inlᵗ a) = cong inlᵗ (sub-renᵗ σ ag a)
  sub-renᵗ σ ag (inrᵗ a) = cong inrᵗ (sub-renᵗ σ ag a)
  sub-renᵗ σ ag (caseᵗ sc l r) =
    cong₃ caseᵗ (sub-renᵗ σ ag sc) (sub-renᵗ σ (lands-ext ag) l)
                (sub-renᵗ σ (lands-ext ag) r)
  sub-renᵗ σ ag (ifᵗ c a b) =
    cong₃ ifᵗ (sub-renᵗ σ ag c) (sub-renᵗ σ ag a) (sub-renᵗ σ ag b)
  sub-renᵗ σ ag (primᵗ op a) = cong (primᵗ op) (sub-renᵗ σ ag a)
  sub-renᵗ σ ag nilᵗ          = refl
  sub-renᵗ σ ag (consᵗ a as)  =
    cong₂ consᵗ (sub-renᵗ σ ag a) (sub-renᵗ σ ag as)
  sub-renᵗ σ ag (foldᵗ l z f) =
    cong₃ foldᵗ (sub-renᵗ σ ag l) (sub-renᵗ σ ag z)
                (sub-renᵗ σ (lands-ext (lands-ext ag)) f)
  sub-renᵗ σ ag (strmᵗ e)    = cong strmᵗ (sub-renᵉ σ ag e)

  sub-renᵗˢ : {ρg : Ren∈ Δᵍ Δᵍ′} {ρd : Ren∈ Δ Δ′}
              {ρt : Ren∈ Θ Θloc} {ρ⁺ : Ren∈ Θ (Θloc ++ Θsub)}
              (σ : All (Val Γ) Θsub) → Lands ρ⁺ ρt
            → (ts : List (Tm Γ Δᵍ Δ Θ t))
            → subΘTms Θloc σ (renTms ρg ρd ρ⁺ ts) ≡ renTms ρg ρd ρt ts
  sub-renᵗˢ σ ag []       = refl
  sub-renᵗˢ σ ag (x ∷ xs) =
    cong₂ _∷_ (sub-renᵗ σ ag x) (sub-renᵗˢ σ ag xs)
