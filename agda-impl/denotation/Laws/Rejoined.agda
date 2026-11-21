{-# OPTIONS --guardedness #-}

-- A LAWFUL HOT, REJOINED: its rows shown a label down keep their order,
-- since none lies under another, so a rejoined row has as few rows
-- before it as the hot's row it shows.
module denotation.Laws.Rejoined where

open import Data.Bool using (true; false)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥-elim)
open import Data.List using ([_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (subst; refl)

open import denotation.Position using (sub; _<ᵖ_; _⊕_)
open import denotation.Events using (<ᵖ-split; <ᵖ-down)
open import denotation.EmissionSet using (EmissionSet; Few; Reach; Dep; Rejoin; shown; heard; ended; late; _≺_)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≼-trans)
open import denotation.Laws.Worlds using (Lawful)

-- Two rows of a lawful hot, a label down in order: in order.
lower : ∀ {A} {t : EmissionSet A} → Lawful t → ∀ {q k e e′ s} → t q e → t k e′ → (k ⊕ [ s ]) ≺ (q ⊕ [ s ]) → k ≺ q
lower {t = t} Lw {q} {k} {e} {e′} {s} x y lt with q <ᵖ k in qk
... | true  = ⊥-elim (≺-absurd {k ⊕ [ s ]} {q ⊕ [ s ]} lt
                (Equivalence.from T-≡ (<ᵖ-down q k s s qk (λ l ls eq → Lawful.flat Lw x (subst (λ z → t z e′) eq y)))))
... | false with <ᵖ-split k q qk
...   | inj₁ kq   = Equivalence.from T-≡ kq
...   | inj₂ refl = ⊥-elim (≺-irrefl {k ⊕ [ s ]} lt)

-- A row rejoined from the hot's row at `q`: the hot's rows before `q`.
row-reach : ∀ {A} {t : EmissionSet A} {j} → Lawful t → ∀ {q e₀} → t q e₀ → Few t q → j ≺ q → ∀ {e} → Reach (Rejoin j t) (q ⊕ [ sub j ]) e
row-reach {t = t} {j} Lw {q} x (ks , h) jq {e} = L.map (_⊕ [ sub j ]) ks , pick
  where
    pick : ∀ {k e′} → Rejoin j t k e′ → k ≺ (q ⊕ [ sub j ]) → Dep (q ⊕ [ sub j ]) e k e′ → k ∈ L.map (_⊕ [ sub j ]) ks
    pick (shown y _ _)   l _ = ∈-map⁺ (_⊕ [ sub j ]) (h y (lower Lw x y l))
    pick (heard y _)     l _ = ∈-map⁺ (_⊕ [ sub j ]) (h y (lower Lw x y l))
    pick (ended y _)     l _ = ∈-map⁺ (_⊕ [ sub j ]) (h y (lower Lw x y l))
    pick (late {c} y cj) _ _ = ⊥-elim (≼-trans {q} {c} {j} (Lawful.proper Lw y x) cj jq)
