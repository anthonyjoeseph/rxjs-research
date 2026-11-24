{-# OPTIONS --guardedness #-}

-- AN APPROXIMANT FINITE IN AN INSTANT IS THE MEANING THERE.  A cut spins
-- endlessly many rows in its own instant.  So past a shown row with few
-- before it, an approximant with finitely many rows left in that row's
-- instant has no cut there, and agrees with the next approximant up to any
-- position of that instant; the next keeps the same few, so down the
-- approximants it agrees with the meaning there (`inst-meaning`).
module simultaneous.InstantTruth where

open import Data.List using (List; _∷_; _++_; [_]; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (≤-refl; m≤m+n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Nullary using (¬_)

open import Tree using (Obs)
open import denotation.Position using (Pos; ix; last; instant; _⊕_)
open import denotation.Events using (Timeline)
open import denotation.EmissionSet using (EmissionSet; DenEnv; Few; _≺_; _≼_; enter; approx; ⟦_⟧)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; AgreeTo-sym; AgreeTo-trans; ≺→≼; ≼-refl; ≼-trans; ≼-or-≻; ≼-split; ≺-trans; ≺-≼-≺)
open import denotation.Laws.Count using (ag-cnt)
open import denotation.Laws.Worlds using (Ok; Hots; GoodEnv; ⊑-refl)
open import denotation.Laws using (from)
open import denotation.Laws.Truth using (Truth; Safe; Lie; Placed; safe-ag; spin-few; below-next; past; instant-⊑; instant-⊕; clear)
open import denotation.Laws.Truthful using (truth)
open import simultaneous.Instants using (btw)

module _ {A : Set} {t : EmissionSet A} {w : Pos} (ks₀ ks : List Pos)
         (h₀ : ∀ {k e} → t k e → k ≺ w → k ∈ ks₀)
         (h : ∀ {k e} → t k e → w ≺ k → instant k ≡ instant w → k ∈ ks) where

  -- Past `w` and no later than a position of its instant: in its instant.
  in-inst : ∀ {k x} → w ≺ k → k ≼ x → instant x ≡ instant w → instant k ≡ instant w
  in-inst {k} {x} wk kx iw with ≼-split {k} {x} kx
  ... | inj₁ kx′ = btw w k x wk kx′ (sym iw)
  ... | inj₂ refl = iw

  -- Before a position of `w`'s instant: before `w`, `w`, or left in it.
  few-in : ∀ {x} → instant x ≡ instant w → ∀ {k e} → t k e → k ≺ x → k ∈ w ∷ ks₀ ++ ks
  few-in {x} iw {k} tk kx with ≼-or-≻ k w
  ... | inj₂ wk = there (∈-++⁺ʳ ks₀ (h tk wk (in-inst {k} {x} wk (≺→≼ {k} {x} kx) iw)))
  ... | inj₁ kw with ≼-split {k} {w} kw
  ...   | inj₁ lt   = there (∈-++⁺ˡ (h₀ tk lt))
  ...   | inj₂ refl = here refl

  module _ {t′ : EmissionSet A} (tr : Truth t t′) (sf : Safe t w) where
    open Truth tr

    -- No cut in `w`'s instant: its spin would leave endlessly many there.
    uncut : ∀ {s} → Cut s → ¬ (instant s ≡ instant w)
    uncut {s} c is = spin-few {s = s} {x = s ⊕ [ last ]}
      (λ i → let (z , e , sz , tz) = shows c i (w ∷ ks₀ ++ ks , λ {k} {e′} → few-in {s ⊕ [ ix (suc i) ]} (trans (instant-⊕ s [ ix (suc i) ]) is) {k} {e′})
             in z , e , sz , tz , ≺-trans {z} {s ⊕ [ ix (suc i) ]} {s ⊕ [ last ]} (below-next s sz ≤-refl) (past s (suc i)))
      (w ∷ ks₀ ++ ks , λ {k} {e′} → few-in {s ⊕ [ last ]} (trans (instant-⊕ s [ last ]) is) {k} {e′})

    -- Nothing up to a position of `w`'s instant lies past a cut's first.
    clean-in : ∀ {k x} → k ≼ x → instant x ≡ instant w → ¬ Lie Cut k
    clean-in {k} {x} kx iw with ≼-or-≻ k w
    ... | inj₁ kw = clear tr (ks₀ , h₀) sf kw
    ... | inj₂ wk = λ { (s , c , i , l) → uncut c (trans (sym (trans (instant-⊑ l) (instant-⊕ s [ ix (suc i) ]))) (in-inst {k} {x} wk kx iw)) }

    -- UP TO A POSITION OF `w`'s INSTANT, THE NEXT.
    inst-lies : ∀ {x} → instant x ≡ instant w → AgreeTo x t t′
    inst-lies {x} iw = ⟨ (λ {y} {e} yx → agree y e (clean-in {y} {x} yx iw , w ∷ ks₀ ++ ks ,
      λ {k} tk ky _ → inj₂ (Any.map (λ { refl → ⊑-refl _ }) (few-in {x} iw tk (≺-≼-≺ {k} {y} {x} ky yx))) ,
                      clean-in {k} {x} (≼-trans {k} {y} {x} (≺→≼ {k} {y} ky) yx) iw)) ⟩

module _ {Γ A} (o : Obs Timeline Γ A) (ρ : DenEnv Γ) (g : GoodEnv ρ) (p : Pos) (ok : Ok (Hots ρ) p) where
  private
    T : ℕ → EmissionSet A
    T n = enter (approx n o ρ) p

    M : EmissionSet A
    M = enter (⟦ o ⟧ ρ) p

    -- The same few before `w`, the same left in its instant, and safe.
    Kept : ℕ → Pos → List Pos → List Pos → Set
    Kept n w ks₀ ks = (∀ {k e} → T n k e → k ≺ w → k ∈ ks₀) × (∀ {k e} → T n k e → w ≺ k → instant k ≡ instant w → k ∈ ks) × Safe (T n) w

    -- Kept down the approximants, each agreeing with the first in the instant.
    down : ∀ n {w ks₀ ks} → Kept n w ks₀ ks → ∀ {x} → instant x ≡ instant w → ∀ k → Kept (k + n) w ks₀ ks × AgreeTo x (T n) (T (k + n))
    down n kp iw zero = kp , ⟨ (λ _ → (λ a → a) , (λ a → a)) ⟩
    down n {w} {ks₀} {ks} kp {x} iw (suc k) =
      let ((h₀ , h , sf) , ag) = down n kp iw k
          ag′ : ∀ {y} → instant y ≡ instant w → AgreeTo y (T (k + n)) (T (suc k + n))
          ag′ = inst-lies ks₀ ks h₀ h (Placed.tr (truth (k + n) o ρ g p ok)) sf
      in ( (λ {j} tj jw → h₀ (proj₂ (upto (ag′ {w} refl) {j} (≺→≼ {j} {w} jw)) tj) jw)
         , (λ {j} tj wj ij → h (proj₂ (upto (ag′ {j} ij) {j} (≼-refl {j})) tj) wj ij)
         , safe-ag (ag′ {w} refl) sf )
       , AgreeTo-trans ag (ag′ {x} iw)

  -- FINITE IN AN INSTANT PAST A SHOWN ROW, THE MEANING THERE.
  inst-meaning : ∀ n {w} → Few (T n) w → Safe (T n) w
               → Σ (List Pos) (λ ks → ∀ {k e} → T n k e → w ≺ k → instant k ≡ instant w → k ∈ ks)
               → ∀ {x} → instant x ≡ instant w → AgreeTo x (T n) M
  inst-meaning n {w} (ks₀ , h₀) sf (ks , h) {x} iw =
    let L = w ∷ ks₀ ++ ks
        ((h₀′ , h′ , _) , ag) = down n (h₀ , h , sf) iw (length L)
    in AgreeTo-trans ag (AgreeTo-sym (ag-cnt (from (length L + n) o ρ g p ok) x
         (inj₂ (L , m≤m+n (length L) n , λ {k} {e′} y kq → inj₂ (Any.map (λ { refl → ⊑-refl _ }) (few-in ks₀ ks (λ {k′} {e″} → h₀′ {k′} {e″}) (λ {k′} {e″} → h′ {k′} {e″}) {x} iw {k} {e′} y kq))))))
