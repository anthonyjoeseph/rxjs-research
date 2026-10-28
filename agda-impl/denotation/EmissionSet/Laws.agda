{-# OPTIONS --guardedness #-}

-- THE EMISSION SET'S LAWS: the meaning of a node is its operator applied to its
-- children's meanings, so proofs over it go one operator at a time; and
-- `map` fuses.
module denotation.EmissionSet.Laws where

open import Data.Bool using (Bool)
open import Data.List using (List; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (_∷_; lookup)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Function using (_∘_)

open import Tree using (Obs; Later; FlatOp; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (Timeline)
open import denotation.EmissionSet
  using (Ev; EmissionSet; Few; Truncate; Den; enter; DenEnv; Lim; from; ⟦_⟧ᵀ; coldᵀ; emptyᵀ; ofᵀ; mapᵀ; scanᵀ; takeWhileᵀ; flatMapᵀ; connectᵀ; deferᵀ;
         MapT; map-out; map-skip; map-end)

-- The same rows at every subscription.
_≅_ : ∀ {A} → Den A → Den A → Set
d ≅ d′ = ∀ p {q e} → (enter d p q e → enter d′ p q e) × (enter d′ p q e → enter d p q e)

-- A row of every approximant is a row of the limit, and back.
private
  constant : ∀ {A} (d : Den A) p {q e} → (Lim (λ _ → enter d p) q e → enter d p q e) × (enter d p q e → Lim (λ _ → enter d p) q e)
  constant d p = (λ { (from N h) → h N ≤-refl }) , λ x → from 0 λ _ _ → x

record Compositionalᵀ : Set₁ where
  field
    coldᶜ      : ∀ {Γ A} (c : Timeline A) (ρ : DenEnv Γ) → ⟦ cold c ⟧ᵀ ρ ≅ coldᵀ c
    emptyᶜ     : ∀ {Γ A} (ρ : DenEnv Γ) → ⟦ empty {Γ = Γ} {A = A} ⟧ᵀ ρ ≅ emptyᵀ
    ofᶜ        : ∀ {Γ A} (xs : List A) (ρ : DenEnv Γ) → ⟦ of {Γ = Γ} xs ⟧ᵀ ρ ≅ ofᵀ xs
    mapᶜ       : ∀ {Γ A B} (f : A → B) (s : Obs Timeline Γ A) (ρ : DenEnv Γ) → ⟦ map f s ⟧ᵀ ρ ≅ mapᵀ f (⟦ s ⟧ᵀ ρ)
    scanᶜ      : ∀ {Γ A B} (f : B → A → B) z (s : Obs Timeline Γ A) (ρ : DenEnv Γ) → ⟦ scan f z s ⟧ᵀ ρ ≅ scanᵀ f z (⟦ s ⟧ᵀ ρ)
    takeWhileᶜ : ∀ {Γ A} (i : Bool) (k : A → Bool) (s : Obs Timeline Γ A) (ρ : DenEnv Γ) → ⟦ takeWhile i k s ⟧ᵀ ρ ≅ takeWhileᵀ i k (⟦ s ⟧ᵀ ρ)
    flatMapᶜ   : ∀ {Γ A B} (op : FlatOp) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) (ρ : DenEnv Γ)
               → ⟦ flatMap op f s ⟧ᵀ ρ ≅ flatMapᵀ op (λ a → ⟦ f a ⟧ᵀ ρ) (⟦ s ⟧ᵀ ρ)
    connectᶜ   : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) (ρ : DenEnv Γ)
               → ⟦ connect s b ⟧ᵀ ρ ≅ connectᵀ (⟦ s ⟧ᵀ ρ) (λ h → ⟦ b ⟧ᵀ (h ∷ ρ))
    connectedᶜ : ∀ {Γ A} (i : A ∈ Γ) (ρ : DenEnv Γ) → ⟦ connected i ⟧ᵀ ρ ≅ lookup ρ i
    deferᶜ     : ∀ {Γ A} (l : Later Timeline Γ A) (ρ : DenEnv Γ) → ⟦ defer l ⟧ᵀ ρ ≅ deferᵀ (⟦ Later.force l ⟧ᵀ ρ)

-- An operator's meaning, through the limit: each approximant applies the
-- operator to its children's approximants, and the limit commutes with it.
postulate
  map-lim       : ∀ {Γ A B} (f : A → B) (s : Obs Timeline Γ A) (ρ : DenEnv Γ) → ⟦ map f s ⟧ᵀ ρ ≅ mapᵀ f (⟦ s ⟧ᵀ ρ)
  scan-lim      : ∀ {Γ A B} (f : B → A → B) z (s : Obs Timeline Γ A) (ρ : DenEnv Γ) → ⟦ scan f z s ⟧ᵀ ρ ≅ scanᵀ f z (⟦ s ⟧ᵀ ρ)
  takeWhile-lim : ∀ {Γ A} (i : Bool) (k : A → Bool) (s : Obs Timeline Γ A) (ρ : DenEnv Γ) → ⟦ takeWhile i k s ⟧ᵀ ρ ≅ takeWhileᵀ i k (⟦ s ⟧ᵀ ρ)
  flatMap-lim   : ∀ {Γ A B} (op : FlatOp) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) (ρ : DenEnv Γ)
                → ⟦ flatMap op f s ⟧ᵀ ρ ≅ flatMapᵀ op (λ a → ⟦ f a ⟧ᵀ ρ) (⟦ s ⟧ᵀ ρ)
  connect-lim   : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) (ρ : DenEnv Γ)
                → ⟦ connect s b ⟧ᵀ ρ ≅ connectᵀ (⟦ s ⟧ᵀ ρ) (λ h → ⟦ b ⟧ᵀ (h ∷ ρ))
  defer-lim     : ∀ {Γ A} (l : Later Timeline Γ A) (ρ : DenEnv Γ) → ⟦ defer l ⟧ᵀ ρ ≅ deferᵀ (⟦ Later.force l ⟧ᵀ ρ)

-- THE MEANING IS COMPOSITIONAL.
compositionalᵀ : Compositionalᵀ
compositionalᵀ = record
  { coldᶜ      = λ c ρ → constant (coldᵀ c)
  ; emptyᶜ     = λ ρ → constant emptyᵀ
  ; ofᶜ        = λ xs ρ → constant (ofᵀ xs)
  ; mapᶜ       = map-lim
  ; scanᶜ      = scan-lim
  ; takeWhileᶜ = takeWhile-lim
  ; flatMapᶜ   = flatMap-lim
  ; connectᶜ   = connect-lim
  ; connectedᶜ = λ i ρ → constant (lookup ρ i)
  ; deferᶜ     = defer-lim
  }

-- MAP FUSES: `map (f ∘ g)` and `map f ∘ map g` have the same rows.
map-fusionᵀ : ∀ {Γ A B C} (f : B → C) (g : A → B) (s : Obs Timeline Γ A) (ρ : DenEnv Γ)
            → ⟦ map (f ∘ g) s ⟧ᵀ ρ ≅ ⟦ map f (map g s) ⟧ᵀ ρ
map-fusionᵀ f g s ρ p = (λ { (from N h) → from N λ n le → fuse (h n le) }) , λ { (from N h) → from N λ n le → split (h n le) }
  where
    few-via : ∀ {A B} {t : EmissionSet A} {t′ : EmissionSet B} {q} → (∀ {k e} → t′ k e → Σ (Ev A) (t k)) → Few t q → Few t′ q
    few-via back (ks , h) = ks , λ x lt → h (proj₂ (back x)) lt

    down : ∀ {t k e} → MapT (f ∘ g) t k e → Σ (Ev _) (MapT g t k)
    down (map-out x)  = _ , map-out x
    down (map-skip x) = _ , map-skip x
    down (map-end x)  = _ , map-end x

    up : ∀ {t k e} → MapT g t k e → Σ (Ev _) (MapT (f ∘ g) t k)
    up (map-out x)  = _ , map-out x
    up (map-skip x) = _ , map-skip x
    up (map-end x)  = _ , map-end x

    across : ∀ {t k e} → MapT f (Truncate (MapT g t)) k e → Σ (Ev _) (MapT (f ∘ g) t k)
    across (map-out (map-out x , _))   = _ , map-out x
    across (map-skip (map-skip x , _)) = _ , map-skip x
    across (map-end (map-end x , _))   = _ , map-end x

    fuse : ∀ {t q e} → Truncate (MapT (f ∘ g) t) q e → Truncate (MapT f (Truncate (MapT g t))) q e
    fuse (map-out x , F)  = map-out (map-out x , few-via up F) , few-via across F
    fuse (map-skip x , F) = map-skip (map-skip x , few-via up F) , few-via across F
    fuse (map-end x , F)  = map-end (map-end x , few-via up F) , few-via across F

    split : ∀ {t q e} → Truncate (MapT f (Truncate (MapT g t))) q e → Truncate (MapT (f ∘ g) t) q e
    split (map-out (map-out x , G) , _)   = map-out x , few-via down G
    split (map-skip (map-skip x , G) , _) = map-skip x , few-via down G
    split (map-end (map-end x , G) , _)   = map-end x , few-via down G
