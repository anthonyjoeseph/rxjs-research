{-# OPTIONS --guardedness #-}

-- A LISTING READ AS ITS OWN TABLE (`TR`).  Each former's listing is its
-- operator applied to its parts' listings, each read the same way, so a
-- composite's rows are the operator's rows over its parts' (`map-tr`,
-- `scan-tr`, `merge-tr`, `bounded-tr`), down to the leaves (`cold-tr`,
-- `of1`, `of2`).
--
-- A finite exact table orders its values: each has an index (`nth-any`),
-- so a scan folds up to each (`acc-of`).
module simultaneous.ListTR where

open import Data.Bool using (true; false; T)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
open import Data.Nat.Properties using (≤-refl; <-≤-trans; ≤-pred)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Tree using (Obs; mergeᶠ; flatMap; cold; of; map; scan)
open import denotation.Position using (Pos; _<ᵖ_; ix; last; _⊕_)
open import denotation.Events using (Timeline; From; fixed; start)
open import denotation.EmissionSet using (Ev; out; end; EmissionSet; Den; coldAt; enter; After; Reach; Truncate; MapT; _≺_; _≼_;
  module Merge; module Bounded; module Values; module Scan)
open import denotation.Laws.Modulus using (≼-refl; ≺→≼; ≼-trans; ≼-or-≻)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (rows; afterL; values)
open import quickcheck.Tabled.Exact using (map-exact; merge-exact; truncate-exact)
open import quickcheck.Tabled.Exact.Scan using (scan-exact)
open import quickcheck.Tabled.Exact.Bounded using (bounded-exact)
open import quickcheck.Tabled.Exact.Base using (Exact; Exactly; sound; complete; bind⁻; lanes-from; lanes-to; afterL-exact;
  values⁺; values⁻; cnt; cnt-lt)
open import simultaneous.Listing using (walkN; listC; listC-ok; UncutEnv)
open import simultaneous.TableCorr using (TR)

------------------------------------------------------------------------
-- A listing is exact for its own table

tr-at : ∀ {X : Set} {m : Maybe (Tb.Listed X)} {L k e} → m ≡ just L → TR m k e → (k , e) ∈ rows L
tr-at refl (_ , refl , x) = x

at-tr : ∀ {X : Set} {m : Maybe (Tb.Listed X)} {L k e} → m ≡ just L → (k , e) ∈ rows L → TR m k e
at-tr {L = L} eq x = L , eq , x

self-exact : ∀ {X : Set} {m : Maybe (Tb.Listed X)} {L} → m ≡ just L → Exactly L (TR m)
self-exact eq _ = record { sound = at-tr eq ; complete = tr-at eq }

-- Every row of a listed table waits on finitely many: the listing's.
reach-tr : ∀ {X : Set} {m : Maybe (Tb.Listed X)} {L k e} → m ≡ just L → Reach (TR m) k e
reach-tr {L = L} eq = mapL proj₁ (rows L) , λ x _ _ → ∈-map⁺ proj₁ (tr-at eq x)

-- A listed row is entered.
ent : ∀ {Γ} {X : Set} K n (o : Obs Timeline Γ X) {ρ : All Tb.Listed Γ} → UncutEnv ρ → ∀ s {k e}
  → TR (listC K n o ρ s) k e → Truncate (TR (listC K n o ρ s)) k e
ent K n o uρ s x with listC-ok K n o uρ s
... | L , eq , _ = x , reach-tr eq

------------------------------------------------------------------------
-- The leaves

cold-tr : ∀ {Γ} {X : Set} K n (m : From X 0) {ρ : All Tb.Listed Γ} p {k e}
  → TR (listC K n (cold (fixed m)) ρ p) k e ⇔ ((k , e) ∈ walkN K (start p m))
cold-tr K n m p = mk⇔ (λ { (_ , refl , x) → x }) (λ x → _ , refl , x)

data Of1 {X : Set} (p : Pos) (x : X) : Pos → Ev X → Set where
  o₀ : Of1 p x (p ⊕ [ ix 0 ]) (out x)
  oₑ : Of1 p x (p ⊕ [ last ]) end

of1 : ∀ {Γ} {X : Set} K n (x : X) {ρ : All Tb.Listed Γ} p {k e}
  → TR (listC K n (of (x ∷ [])) ρ p) k e ⇔ Of1 p x k e
of1 K n x p = mk⇔ (λ { (_ , refl , here refl) → o₀ ; (_ , refl , there (here refl)) → oₑ ; (_ , refl , there (there ())) })
                  (λ { o₀ → _ , refl , here refl ; oₑ → _ , refl , there (here refl) })

data Of2 {X : Set} (p : Pos) (x y : X) : Pos → Ev X → Set where
  o₀ : Of2 p x y (p ⊕ [ ix 0 ]) (out x)
  o₁ : Of2 p x y (p ⊕ [ ix 1 ]) (out y)
  oₑ : Of2 p x y (p ⊕ [ last ]) end

of2 : ∀ {Γ} {X : Set} K n (x y : X) {ρ : All Tb.Listed Γ} p {k e}
  → TR (listC K n (of (x ∷ y ∷ [])) ρ p) k e ⇔ Of2 p x y k e
of2 K n x y p = mk⇔ (λ { (_ , refl , here refl) → o₀ ; (_ , refl , there (here refl)) → o₁
                       ; (_ , refl , there (there (here refl))) → oₑ ; (_ , refl , there (there (there ()))) })
                    (λ { o₀ → _ , refl , here refl ; o₁ → _ , refl , there (here refl)
                       ; oₑ → _ , refl , there (there (here refl)) })

------------------------------------------------------------------------
-- One input

map-tr : ∀ {Γ} {X Y : Set} K n (g : X → Y) (s : Obs Timeline Γ X) {ρ : All Tb.Listed Γ} → UncutEnv ρ → ∀ p {k e}
  → TR (listC K n (map g s) ρ p) k e ⇔ MapT g (TR (listC K n s ρ p)) k e
map-tr K n g s {ρ} uρ p with listC-ok K n (map g s) uρ p
... | L , eq , u with bind⁻ {m = listC K n s ρ p} eq
... | o , eo , refl = mk⇔ (λ x → sound ex (tr-at eq x)) (λ x → at-tr eq (complete ex x))
  where
    ex : Exact (Tb.mapRows g o) (MapT g (TR (listC K n s ρ p)))
    ex = map-exact g (self-exact eo) u

scan-tr : ∀ {Γ} {X Y : Set} K n (f : Y → X → Y) (z : Y) (s : Obs Timeline Γ X) {ρ : All Tb.Listed Γ} → UncutEnv ρ → ∀ p {k e}
  → TR (listC K n (scan f z s) ρ p) k e ⇔ Scan.ScanT f z (TR (listC K n s ρ p)) k e
scan-tr K n f z s {ρ} uρ p with listC-ok K n (scan f z s) uρ p
... | L , eq , u with bind⁻ {m = listC K n s ρ p} eq
... | o , eo , refl = mk⇔ (λ x → sound ex (tr-at eq x)) (λ x → at-tr eq (complete ex x))
  where
    ex : Exact (Tb.scanRows f z o) (Scan.ScanT f z (TR (listC K n s ρ p)))
    ex = scan-exact f z o (self-exact eo) u

------------------------------------------------------------------------
-- Joiners

-- Each lane read off its own listing, wherever it is subscribed.
laneD : ∀ {Γ} {X Y : Set} → ℕ → ℕ → (X → Obs Timeline Γ Y) → All Tb.Listed Γ → X → Den Y
laneD K n f ρ x = coldAt (λ s → TR (listC K n (f x) ρ s))

merge-tr : ∀ {Γ} {X Y : Set} K n (f : X → Obs Timeline Γ Y) (s : Obs Timeline Γ X) {ρ : All Tb.Listed Γ} → UncutEnv ρ → ∀ p {k e}
  → TR (listC K n (flatMap (mergeᶠ nothing) f s) ρ p) k e ⇔ Merge.JoinT (laneD K n f ρ) (TR (listC K n s ρ p)) k e
merge-tr K n f s {ρ} uρ p with listC-ok K n (flatMap (mergeᶠ nothing) f s) uρ p
... | L , eq , u with bind⁻ {m = listC K n s ρ p} eq
... | o , eo , e₁ with bind⁻ {m = Tb.lanes (afterL (λ a → listC K n (f a) ρ)) (values (rows o))} e₁
... | ls , els , refl = mk⇔ (λ x → sound ex (tr-at eq x)) (λ x → at-tr eq (complete ex x))
  where
    ex : Exact L (Merge.JoinT (laneD K n f ρ) (TR (listC K n s ρ p)))
    ex = merge-exact (laneD K n f ρ) o ls (self-exact eo)
      (lanes-from {ln = afterL (λ a → listC K n (f a) ρ)} {D = λ a → After (laneD K n f ρ a)}
        (afterL-exact {ln = λ a → listC K n (f a) ρ} {D = λ a → enter (laneD K n f ρ a)} (λ el → truncate-exact (self-exact el))) els)
      (lanes-to {ln = afterL (λ a → listC K n (f a) ρ)} els) u

bounded-tr : ∀ {Γ} {X Y : Set} K n j (f : X → Obs Timeline Γ Y) (s : Obs Timeline Γ X) {ρ : All Tb.Listed Γ} → UncutEnv ρ → ∀ p {k e}
  → TR (listC K n (flatMap (mergeᶠ (just j)) f s) ρ p) k e ⇔ Bounded.JoinT j (laneD K n f ρ) (TR (listC K n s ρ p)) k e
bounded-tr K n j f s {ρ} uρ p with listC-ok K n (flatMap (mergeᶠ (just j)) f s) uρ p
... | L , eq , u with bind⁻ {m = listC K n s ρ p} eq
... | o , eo , e₁ = mk⇔ (λ x → sound ex (tr-at eq x)) (λ x → at-tr eq (complete ex x))
  where
    ex : Exact L (Bounded.JoinT j (laneD K n f ρ) (TR (listC K n s ρ p)))
    ex = bounded-exact j (laneD K n f ρ) (TR (listC K n s ρ p)) (afterL (λ a → listC K n (f a) ρ)) o (self-exact eo)
      (afterL-exact {ln = λ a → listC K n (f a) ρ} {D = λ a → enter (laneD K n f ρ a)} (λ el → truncate-exact (self-exact el))) e₁ u

------------------------------------------------------------------------
-- A finite exact table's values, in order

private
  T-of : ∀ {x y} → x <ᵖ y ≡ true → x ≺ y
  T-of = Equivalence.from T-≡

  ≺-false : ∀ {x y} → x ≺ y → x <ᵖ y ≡ false → ⊥
  ≺-false lt e with () ← subst T e lt

module NthAny {X : Set} {t : EmissionSet X} {o : Tb.Listed X} (ex : Exact o t) where
  open Values t using (Nth; first; next)

  -- The latest of `xs` before `q`, or none is.
  below : ∀ (xs : List (Pos × X)) q → (∀ {k b} → (k , b) ∈ xs → k ≺ q → ⊥)
        ⊎ (Σ Pos λ k → Σ X λ b → (k , b) ∈ xs × k ≺ q × (∀ {k′ b′} → (k′ , b′) ∈ xs → k′ ≺ q → k′ ≼ k))
  below [] q = inj₁ λ ()
  below ((k , b) ∷ xs) q with k <ᵖ q in e | below xs q
  ... | false | inj₁ n = inj₁ λ { (here refl) lt → ≺-false {k} {q} lt e ; (there m) lt → n m lt }
  ... | false | inj₂ (k₀ , b₀ , m , lt , mx) =
    inj₂ (k₀ , b₀ , there m , lt , λ { (here refl) lt′ → ⊥-elim (≺-false {k} {q} lt′ e) ; (there m′) lt′ → mx m′ lt′ })
  ... | true | inj₁ n =
    inj₂ (k , b , here refl , T-of {k} {q} e , λ { (here refl) _ → ≼-refl {k} ; (there m′) lt′ → ⊥-elim (n m′ lt′) })
  ... | true | inj₂ (k₀ , b₀ , m , lt , mx) with ≼-or-≻ k₀ k
  ...   | inj₁ le = inj₂ (k , b , here refl , T-of {k} {q} e , λ { (here refl) _ → ≼-refl {k} ; {k′} (there m′) lt′ → ≼-trans {k′} {k₀} {k} (mx m′ lt′) le })
  ...   | inj₂ gt = inj₂ (k₀ , b₀ , there m , lt , λ { (here refl) _ → ≺→≼ {k} {k₀} gt ; (there m′) lt′ → mx m′ lt′ })

  private
    nth-fuel : ∀ N {q a} → cnt q (values (rows o)) < N → t q (out a) → Σ ℕ λ i → Nth i q a
    nth-fuel zero () _
    nth-fuel (suc N) {q} c x with below (values (rows o)) q
    ... | inj₁ n = 0 , first x (λ y lt → n (values⁺ (complete ex y)) lt)
    ... | inj₂ (k , b , m , lt , mx) with nth-fuel N (<-≤-trans (cnt-lt m (Equivalence.to (T-≡ {k <ᵖ q}) lt)) (≤-pred c)) (sound ex (values⁻ m))
    ...   | i , N′ = suc i , next N′ x lt (λ y kk′ k′q → mx (values⁺ (complete ex y)) k′q kk′)

  -- Every value has an index.
  nth-any : ∀ {q a} → t q (out a) → Σ ℕ λ i → Nth i q a
  nth-any x = nth-fuel _ ≤-refl x

-- A scan folds up to every indexed value, that value last.
module AccOf {X Y : Set} (f : Y → X → Y) (z : Y) (t : EmissionSet X) where
  open Values t using (Nth; first; next)
  open Scan f z t using (Acc; acc₀; acc)

  acc-of : ∀ {i q a} → Nth i q a → Σ Y λ b → Acc q (f b a)
  acc-of (first x mn) = z , acc₀ x mn
  acc-of (next {a = a₀} N x lt nx) with acc-of N
  ... | b , A = f b a₀ , acc A x lt nx
