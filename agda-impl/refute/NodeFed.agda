{-# OPTIONS --guardedness #-}

-- node-fed over any node and any source refuted: a source whose value
-- comes before the skip it follows, merged beside a lane that leads, has
-- its skip neither leading nor erasable.
module refute.NodeFed where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import denotation.MonotonicList.Events using (Events; Events∞; Pos; out; skip; end; hush; ix; idle)
open import denotation.MonotonicList using (Agree; agree-refl)
open import Tree using (mergeᶠ)
open import denotation.Unfold using (stateᴺ; NEnv)
import denotation.Unfold as U
open import adequacy.Engine.Meaning using (same)
open import adequacy.Engine.Erase using (Erase; outᵉ; skipᵉ; erased; nowᵉ)
open import adequacy.Engine.Drop using (Dropsˢ; dropˢ; dropsˢ; Fed; ≋-⊒)
open import adequacy.Engine.Shown using (Sought; Caught; Flat)

open Events∞

NodeFed : Set₁
NodeFed = ∀ {Γ X B} v q {P} (n : U.Node (X ∷ Γ) B) (ρ : NEnv Γ) {h h′ : Events∞ X}
        → Sought v q P → Caught (here refl) q n → (∀ m → Flat m (force h)) → Dropsˢ P h h′
        → Fed P (stateᴺ n (force h ∷ᴬ ρ)) (stateᴺ n (force h′ ∷ᴬ ρ))

h : Events∞ ℕ
h′ : Events∞ ℕ
h .force = skip (ix 5 ∷ []) h′
h .cut = idle
h′ .force = out (ix 3 ∷ []) 1 λ where
  .force → end (ix 9 ∷ [])
  .cut → idle
h′ .cut = idle

n : U.Node (ℕ ∷ []) ℕ
n = U.flatMapᶜ {A = ℕ} (mergeᶠ nothing) (λ _ _ → U.idleᶜ) nothing (U.ofᶜ (ix 0 ∷ []) 0 (1 ∷ 2 ∷ []) ∷ U.joinᶜ (here refl) (ix 1 ∷ []) [] nothing ∷ []) [] U.idleᶜ

fl′ : ∀ m → Flat m (force h′)
fl′ zero = tt
fl′ (suc zero) = tt
fl′ (suc (suc m)) = tt

fl : ∀ m → Flat m (force h)
fl zero = tt
fl (suc m) = refl , fl′ m

β β′ : Events∞ ℕ
β = stateᴺ n (force h ∷ᴬ []ᴬ)
β′ = stateᴺ n (force h′ ∷ᴬ []ᴬ)

unerased : ∀ {t} → Erase 5 (force β) t (force β′) → ⊥
unerased (outᵉ _ (outᵉ _ (skipᵉ _ (erased () _ _))))
unerased (outᵉ _ (outᵉ _ (erased _ _ (erased () _ _))))

unled : ∀ {k r} → Agree 1 (force β) (skip k r) → ⊥
unled ()

refuted : ¬ NodeFed
refuted nf with nf false (ix 5 ∷ []) {λ k → k ≡ ix 5 ∷ []} n []ᴬ {h} {h′} (λ k e → e)
                   (tt , (refl , ((inj₂ refl , refl) , tt)) , tt) fl (dropˢ refl (λ m → agree-refl m _) (≋-⊒ (λ m → same m h′)))
... | inj₁ (_ , _ , e) = unerased (nowᵉ (e 5))
... | inj₂ (dropˢ _ ag _) = unled (ag 1)
... | inj₂ (dropsˢ _ ag _) = unled (ag 1)
