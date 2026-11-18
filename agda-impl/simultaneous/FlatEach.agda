{-# OPTIONS --guardedness #-}

-- THE ELABORATION'S `each`, FLAT.  `each f s` is a merge over `of (f x)`
-- lanes; its rows are stated here as one operator on its source's rows
-- (`EachT`), and the merge's rows are exactly those, for any source
-- (`each-rows`), so at every subscription (`each-flat`).  No cut and no
-- listing: both sides are the same stream, so a row's derivation on one
-- side holds everything its derivation on the other needs.
--
-- A lane's own truncation falls away: an `of` has finitely many rows,
-- listed outright (`of-list`).
module simultaneous.FlatEach where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; mergeᶠ; flatMap; of)
open import Data.Maybe using (nothing)
open import denotation.Position using (Pos; ix; last; _⊕_)
open import denotation.Events using (Timeline; ofᴱ)
open import denotation.EmissionSet
  using (Ev; out; skip; end; pin; EmissionSet; _≺_; _≼_; InE; at-out; at-end; on-out; Truncate; Ended; enter; Den; DenEnv; ⟦_⟧;
         module Op; module Merge)
open import denotation.Laws.Modulus using (≺-ext)

------------------------------------------------------------------------
-- An `of`'s rows

-- A row of an `of` is a value, or its end at `last`.
of-inv : ∀ {A : Set} s i (xs : List A) {k e} → InE (ofᴱ s i xs) k e → (Σ A λ y → e ≡ out y) ⊎ (e ≡ end × k ≡ s ⊕ [ last ])
of-inv s i []       at-end     = inj₂ (refl , refl)
of-inv s i (x ∷ xs) at-out     = inj₁ (x , refl)
of-inv s i (x ∷ xs) (on-out r) = of-inv s (suc i) xs r

of-end : ∀ {A : Set} s i (xs : List A) → InE (ofᴱ s i xs) (s ⊕ [ last ]) end
of-end s i []       = at-end
of-end s i (x ∷ xs) = on-out (of-end s (suc i) xs)

-- Every row lies past the subscription.
of-after : ∀ {A : Set} s i (xs : List A) {k e} → InE (ofᴱ s i xs) k e → s ≺ k
of-after s i []       at-end     = ≺-ext s []
of-after s i (x ∷ xs) at-out     = ≺-ext s []
of-after s i (x ∷ xs) (on-out r) = of-after s (suc i) xs r

-- Its rows, listed.
of-list : ∀ {A : Set} s i (xs : List A) → Σ (List Pos) λ ks → ∀ {k e} → InE (ofᴱ s i xs) k e → k ∈ ks
of-list s i []       = [ s ⊕ [ last ] ] , λ { at-end → here refl }
of-list s i (x ∷ xs) = (s ⊕ [ ix i ]) ∷ proj₁ (of-list s (suc i) xs) , λ { at-out → here refl ; (on-out r) → there (proj₂ (of-list s (suc i) xs) r) }

-- So a row of an `of` is a row of its reading.
of-enter : ∀ {A : Set} s (xs : List A) {k e} → InE (ofᴱ s 0 xs) k e → enter (Op.of xs) s k e
of-enter s xs r = r , proj₁ (of-list s 0 xs) , λ x _ _ → proj₂ (of-list s 0 xs) x

------------------------------------------------------------------------
-- The flat operator

module Each {X Y : Set} (f : X → List Y) (t : EmissionSet X) where

  -- Where the lane of the value at `q` ends.
  lastOf : Pos → Pos
  lastOf q = q ⊕ [ ix 1 ] ⊕ [ last ]

  -- The source has ended by `c`, and every lane begun before it.
  Doneᶠ : Pos → Set
  Doneᶠ c = Ended t c × (∀ {q a} → t q (out a) → q ≺ c → lastOf q ≼ c)

  data EachT : EmissionSet Y where
    e-val   : ∀ {q a} → t q (out a) → EachT (q ⊕ [ ix 0 ]) skip
    e-step  : ∀ {q} → t q skip → EachT q skip
    e-pin   : ∀ {q r} → t q (pin r) → EachT q (pin r)
    e-oend  : ∀ {c} → t c end → Doneᶠ c → EachT c end
    e-opass : ∀ {c} → t c end → ¬ Doneᶠ c → EachT c skip
    e-item  : ∀ {q a k y} → t q (out a) → InE (ofᴱ (q ⊕ [ ix 1 ]) 0 (f a)) k (out y) → EachT k (out y)
    e-lend  : ∀ {q a} → t q (out a) → Doneᶠ (lastOf q) → EachT (lastOf q) end
    e-lpass : ∀ {q a} → t q (out a) → ¬ Doneᶠ (lastOf q) → EachT (lastOf q) skip

  open Merge (λ x → Op.of (f x)) t

  private
    done→ : ∀ {c} → Done c → Doneᶠ c
    done→ {c} (ov , h) = ov , go
      where
        go : ∀ {q a} → t q (out a) → q ≺ c → lastOf q ≼ c
        go {q} {a} x lt with h x tt lt (λ ())
        ... | c₀ , (ln , _) , le with of-inv (q ⊕ [ ix 1 ]) 0 (f a) (proj₁ ln)
        ...   | inj₁ (_ , ())
        ...   | inj₂ (_ , refl) = le

    done← : ∀ {c} → Doneᶠ c → Done c
    done← (ov , h) = ov , λ {q} {a} x _ lt _ →
      lastOf q , (of-enter (q ⊕ [ ix 1 ]) (f a) (of-end (q ⊕ [ ix 1 ]) 0 (f a)) , ≺-ext (q ⊕ [ ix 1 ]) []) , h x lt

  -- THE MERGE'S ROWS ARE THE FLAT OPERATOR'S.
  to : ∀ {k e} → JoinT k e → EachT k e
  to (val x)      = e-val x
  to (step x)     = e-step x
  to (opin x)     = e-pin x
  to (oend x d)   = e-oend x (done→ d)
  to (opass x nd) = e-opass x (λ d → nd (done← d))
  to (lane {q} {a} x _ (ln , _) _ w) with of-inv (q ⊕ [ ix 1 ]) 0 (f a) (proj₁ ln)
  ... | inj₁ (y , refl) = e-item x (proj₁ ln)
  ... | inj₂ (refl , _) = ⊥-elim w
  to (lend {q} {a} x _ (ln , _) _ _ d) with of-inv (q ⊕ [ ix 1 ]) 0 (f a) (proj₁ ln)
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , refl) = e-lend x (done→ d)
  to (lpass {q} {a} x _ (ln , _) _ _ nd) with of-inv (q ⊕ [ ix 1 ]) 0 (f a) (proj₁ ln)
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , refl) = e-lpass x (λ d → nd (done← d))
  to (hand _ _ _ _ ())
  to (left {q} {a} x _ (ln , _) _ _) with of-inv (q ⊕ [ ix 1 ]) 0 (f a) (proj₁ ln)
  ... | inj₁ (_ , ())
  ... | inj₂ (() , _)
  to (run () _)
  to (rend () _ _)
  to (rpass () _ _)
  to (rhand () _)

  from : ∀ {k e} → EachT k e → JoinT k e
  from (e-val x)      = val x
  from (e-step x)     = step x
  from (e-pin x)      = opin x
  from (e-oend x d)   = oend x (done← d)
  from (e-opass x nd) = opass x (λ d → nd (done→ d))
  from (e-item {q} {a} x r) = lane x tt (of-enter (q ⊕ [ ix 1 ]) (f a) r , of-after (q ⊕ [ ix 1 ]) 0 (f a) r) (λ ()) tt
  from (e-lend {q} {a} x d) =
    lend x tt (of-enter (q ⊕ [ ix 1 ]) (f a) (of-end (q ⊕ [ ix 1 ]) 0 (f a)) , ≺-ext (q ⊕ [ ix 1 ]) []) (λ ()) (λ ()) (done← d)
  from (e-lpass {q} {a} x nd) =
    lpass x tt (of-enter (q ⊕ [ ix 1 ]) (f a) (of-end (q ⊕ [ ix 1 ]) 0 (f a)) , ≺-ext (q ⊕ [ ix 1 ]) []) (λ ()) (λ ()) (λ d → nd (done→ d))

open Each using (EachT)

------------------------------------------------------------------------
-- At every subscription

-- Sets with the same rows are truncated alike.
trunc-≃ : ∀ {A : Set} {t t′ : EmissionSet A} → (∀ {k e} → t k e → t′ k e) → (∀ {k e} → t′ k e → t k e)
        → ∀ {q e} → Truncate t q e → Truncate t′ q e
trunc-≃ a b (x , ks , h) = a x , ks , λ y lt d → h (b y) lt d

-- The flat operator, as an observable.
eachᶠ : ∀ {X Y : Set} → (X → List Y) → Den X → Den Y
eachᶠ f s = Den.coldAt λ p → EachT f (enter s p)

-- `each` over any source reads as the flat operator over it.
each-rows : ∀ {X Y : Set} (f : X → List Y) (s : Den X) p {q e}
          → (enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (f x)) s) p q e → enter (eachᶠ f s) p q e)
          × (enter (eachᶠ f s) p q e → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (f x)) s) p q e)
each-rows f s p = trunc-≃ (Each.to f (enter s p)) (Each.from f (enter s p)) , trunc-≃ (Each.from f (enter s p)) (Each.to f (enter s p))

-- So a program's `each`, whatever its source means.
each-flat : ∀ {Γ X Y} (f : X → List Y) (s : Obs Timeline Γ X) (ρ : DenEnv Γ) p {q e}
          → (enter (⟦ flatMap (mergeᶠ nothing) (λ x → of (f x)) s ⟧ ρ) p q e → enter (eachᶠ f (⟦ s ⟧ ρ)) p q e)
          × (enter (eachᶠ f (⟦ s ⟧ ρ)) p q e → enter (⟦ flatMap (mergeᶠ nothing) (λ x → of (f x)) s ⟧ ρ) p q e)
each-flat f s ρ = each-rows f (⟦ s ⟧ ρ)
