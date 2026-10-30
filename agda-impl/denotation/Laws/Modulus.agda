{-# OPTIONS --guardedness #-}

-- THE ORDER ON ROWS, AND AGREEMENT UP TO A CUT: two emission sets agree
-- at `q` with the same rows at and below it.  How far two observables
-- agree, and how that bounds the unfolding, is `Laws.Count`.
module denotation.Laws.Modulus where

open import Data.Bool using (T; true; false)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_; [_]; length; filter)
open import Data.List.Properties using (filter-notAll)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁺)
import Data.List.Relation.Unary.Any as Any
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-pred)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_∘_; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary.Decidable.Core using (T?)

open import denotation.Events using (Pos; ix; _<ᵖ_; <ᵖ-trans; <ᵖ-irrefl; <ᵖ-asym; <ᵖ-split; <ᵖ-part; <ᵖ-below)
open import denotation.EmissionSet
  using (Ev; EmissionSet; _≺_; _≼_; Few; Dep; Reach; Truncate; Den; hot; coldAt; enter; Lim; from)

------------------------------------------------------------------------
-- The order on positions

≺-trans : ∀ {x y z} → x ≺ y → y ≺ z → x ≺ z
≺-trans {x} {y} {z} a b = Equivalence.from T-≡ (<ᵖ-trans x y z (Equivalence.to T-≡ a) (Equivalence.to T-≡ b))

≺-irrefl : ∀ {x} → x ≺ x → ⊥
≺-irrefl {x} a = subst T (<ᵖ-irrefl x) a

≺-absurd : ∀ {x y} → x ≺ y → y ≺ x → ⊥
≺-absurd {x} {y} a b = ≺-irrefl {x} (≺-trans {x} {y} {x} a b)

≼-refl : ∀ {x} → x ≼ x
≼-refl {x} = ≺-irrefl {x}

≺→≼ : ∀ {x y} → x ≺ y → x ≼ y
≺→≼ {x} {y} a b = subst T (<ᵖ-asym x y (Equivalence.to T-≡ a)) b

≼-false : ∀ {y q} → y ≼ q → q <ᵖ y ≡ false
≼-false {y} {q} h with q <ᵖ y
... | true  = ⊥-elim (h tt)
... | false = refl

-- Before what is at or before `q`: before `q`.
≺-≼-≺ : ∀ {w y q} → w ≺ y → y ≼ q → w ≺ q
≺-≼-≺ {w} {y} {q} wy yq with <ᵖ-split y q (≼-false {y} {q} yq)
... | inj₁ lt   = ≺-trans {w} {y} {q} wy (Equivalence.from T-≡ lt)
... | inj₂ refl = wy

-- Before what is after what is at or before: before.
≼-≺-≺ : ∀ {x y z} → x ≼ y → y ≺ z → x ≺ z
≼-≺-≺ {x} {y} {z} xy yz with <ᵖ-split x y (≼-false {x} {y} xy)
... | inj₁ lt   = ≺-trans {x} {y} {z} (Equivalence.from T-≡ lt) yz
... | inj₂ refl = yz

≼-antisym : ∀ {x y} → x ≼ y → y ≼ x → x ≡ y
≼-antisym {x} {y} xy yx with <ᵖ-split x y (≼-false {x} {y} xy)
... | inj₁ lt = ⊥-elim (yx (Equivalence.from T-≡ lt))
... | inj₂ eq = eq

≼-trans : ∀ {x y z} → x ≼ y → y ≼ z → x ≼ z
≼-trans {x} {y} {z} xy yz zx = yz (≺-≼-≺ {z} {x} {y} zx xy)

-- At or before, or after.
≼-or-≻ : ∀ x q → x ≼ q ⊎ q ≺ x
≼-or-≻ x q with q <ᵖ x
... | true  = inj₂ tt
... | false = inj₁ (λ ())

-- A position comes before its extensions.
≺-ext : ∀ x {l} ys → x ≺ (x ++ l ∷ ys)
≺-ext x ys = Equivalence.from T-≡ (<ᵖ-below x ys)

------------------------------------------------------------------------
-- Few

-- Rows of `t′` are rows of `t`, so as few.
few-via : ∀ {A B} {t : EmissionSet A} {t′ : EmissionSet B} {q} → (∀ {k e} → t′ k e → Σ (Ev A) (t k)) → Few t q → Few t′ q
few-via back (ks , h) = ks , λ x lt → h (proj₂ (back x)) lt

-- Fewer before an earlier position.
few-down : ∀ {A} {t : EmissionSet A} {y w} → Few t y → w ≺ y → Few t w
few-down {y = y} {w} (ks , h) wy = ks , λ {k} x kw → h x (≺-trans {k} {w} {y} kw wy)

-- Few before `q`: whatever a row there waits on is few.
few-reach : ∀ {A} {t : EmissionSet A} {q e} → Few t q → Reach t q e
few-reach (ks , h) = ks , λ x lt _ → h x lt

-- A row waiting on everything before it is reached by few.
reach-few : ∀ {A} {t : EmissionSet A} {q e} → (∀ {k e′} → Dep q e k e′) → Reach t q e → Few t q
reach-few all (ks , h) = ks , λ x lt → h x lt all

-- Rows of `t′` a row waits on are rows of `t` it waits on, so as few.
reach-via : ∀ {A B} {t : EmissionSet A} {t′ : EmissionSet B} {q e e₀}
          → (∀ {k e′} → t′ k e′ → k ≺ q → Dep q e k e′ → Σ (Ev A) λ e″ → t k e″ × Dep q e₀ k e″)
          → Reach t q e₀ → Reach t′ q e
reach-via back (ks , h) = ks , λ x lt d → h (proj₁ (proj₂ (back x lt d))) lt (proj₂ (proj₂ (back x lt d)))

-- A row read through `enter` has finitely many rows it waits on.
entered-reach : ∀ {A} (d : Den A) p {q e} → enter d p q e → Reach (enter d p) q e
entered-reach (hot t)  p (_ , F) = reach-via (λ y _ d → _ , proj₁ y , d) F
entered-reach (coldAt f) p (_ , F) = reach-via (λ y _ d → _ , proj₁ y , d) F

-- A row of no pin read through `enter` has finitely many rows before it.
entered-few : ∀ {A} (d : Den A) p {q e} → (∀ {k e′} → Dep q e k e′) → enter d p q e → Few (enter d p) q
entered-few d p all x = reach-few all (entered-reach d p x)

-- INDUCTION ON THE ROWS BEFORE: a property that holds of a row once it
-- holds of every row before it holds of every row with few before it.
few-ind : ∀ {A} {t : EmissionSet A} (P : Pos → Set)
        → (∀ {w} → Few t w → (∀ {v e} → t v e → v ≺ w → P v) → P w)
        → ∀ {w} → Few t w → P w
few-ind {t = t} P step F = go (length (proj₁ F)) F ≤-refl
  where
    go : ∀ n {w} (F : Few t w) → length (proj₁ F) ≤ n → P w
    go zero    ([] , h)    le = step ([] , h) λ x vw → ⊥-elim (none (h x vw))
      where none : ∀ {v : Pos} → v ∈ [] → ⊥
            none ()
    go (suc n) {w} (ks , h) le = step (ks , h) λ {v} x vw →
      go n (filter (λ k → T? (k <ᵖ v)) ks , λ {k} y kv → ∈-filter⁺ (λ k → T? (k <ᵖ v)) (h y (≺-trans {k} {v} {w} kv vw)) kv)
        (≤-pred (≤-trans (filter-notAll (λ k → T? (k <ᵖ v)) ks (Any.map (λ { refl → ≺-irrefl {v} }) (h x vw))) le))

------------------------------------------------------------------------
-- Agreement

-- At and below `q`, the same rows.
record AgreeTo {A} (q : Pos) (t t′ : EmissionSet A) : Set where
  constructor ⟨_⟩
  field upto : ∀ {y e} → y ≼ q → (t y e → t′ y e) × (t′ y e → t y e)

open AgreeTo public

AgreeTo-sym : ∀ {A} {t t′ : EmissionSet A} {q} → AgreeTo q t t′ → AgreeTo q t′ t
AgreeTo-sym ⟨ a ⟩ = ⟨ (λ {y} {e} yq → proj₂ (a {y} {e} yq) , proj₁ (a {y} {e} yq)) ⟩

AgreeTo-trans : ∀ {A} {t u v : EmissionSet A} {q} → AgreeTo q t u → AgreeTo q u v → AgreeTo q t v
AgreeTo-trans ⟨ a ⟩ ⟨ b ⟩ = ⟨ (λ {y} {e} yq → proj₁ (b {y} {e} yq) ∘ proj₁ (a {y} {e} yq) , proj₂ (a {y} {e} yq) ∘ proj₂ (b {y} {e} yq)) ⟩

-- Agreeing at and below `q`, rows before `q` are as few.
few-agree : ∀ {A} {t t′ : EmissionSet A} {q} → AgreeTo q t t′ → Few t q → Few t′ q
few-agree {q = q} a (ks , h) = ks , λ {k} {e′} x kq → h (proj₂ (upto a {k} {e′} (≺→≼ {k} {q} kq)) x) kq

reach-agree : ∀ {A} {t t′ : EmissionSet A} {q e} → AgreeTo q t t′ → Reach t q e → Reach t′ q e
reach-agree {q = q} a = reach-via λ {k} {e′} x kq d → e′ , proj₂ (upto a {k} {e′} (≺→≼ {k} {q} kq)) x , d

------------------------------------------------------------------------
-- Observables

-- The same rows at every subscription `R` admits.
Same : ∀ {A} → (Pos → Set) → Den A → Den A → Set
Same R d d′ = ∀ p → R p → ∀ {q e} → (enter d p q e → enter d′ p q e) × (enter d′ p q e → enter d p q e)

-- A row every member has from some index on, read where reached.
LimD : ∀ {A} → (ℕ → Den A) → Den A
LimD c = coldAt λ p → Lim λ n → enter (c n) p

-- The guard comes before the body.
ticks : ∀ p j → (p ++ [ ix 0 ]) ≺ (p ++ [ ix (suc j) ])
ticks p j = Equivalence.from T-≡ (<ᵖ-part p [] [] refl)

------------------------------------------------------------------------
-- Causality

-- At and below `q`, the same rows at every subscription.
_~⟨_⟩_ : ∀ {A} → Den A → Pos → Den A → Set
d ~⟨ q ⟩ d′ = ∀ p → AgreeTo q (enter d p) (enter d′ p)

-- Agreeing at and below `q` agrees below what is at or before it.
ag-down : ∀ {A} {t t′ : EmissionSet A} {q y} → y ≼ q → AgreeTo q t t′ → AgreeTo y t t′
ag-down {q = q} {y} yq a = ⟨ (λ {v} vy → upto a {v} (≼-trans {v} {y} {q} vy yq)) ⟩

-- TRUNCATION KEEPS AGREEMENT at and below `q`: a row there has its
-- predecessors there too.
trunc-to : ∀ {A} {t t′ : EmissionSet A} {q} → AgreeTo q t t′ → AgreeTo q (Truncate t) (Truncate t′)
trunc-to {q = q} a = ⟨ (λ {y} yq →
    (λ { (x , F) → proj₁ (upto a {y} yq) x , reach-agree (ag-down {q = q} {y} yq a) F })
  , (λ { (x , F) → proj₂ (upto a {y} yq) x , reach-agree (AgreeTo-sym (ag-down {q = q} {y} yq a)) F })) ⟩

-- A cold agreeing at every subscription.
~-cold : ∀ {A q} {f f′ : Pos → EmissionSet A} → (∀ p → AgreeTo q (f p) (f′ p)) → coldAt f ~⟨ q ⟩ coldAt f′
~-cold a p = trunc-to (a p)

~-refl : ∀ {A q} (d : Den A) → d ~⟨ q ⟩ d
~-refl d p = ⟨ (λ yq → (λ x → x) , (λ x → x)) ⟩
