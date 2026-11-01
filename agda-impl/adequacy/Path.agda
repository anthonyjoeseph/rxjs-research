{-# OPTIONS --guardedness #-}

-- A RUN, STEP BY STEP: the steps a run takes from one conf to another,
-- what it shows next, and a step whose clock passes no listed position.
module adequacy.Path where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import denotation.Events using (Pos)
open import denotation.EmissionSet using (Ev; out; end)
open import operation.PureObservable using (module Machine; module Driver)
open Machine using (Conf; nx; cp) renaming (Shown to Shownᴹ)
open import operation.Key using (Key; at; _<ᴷ_; ≮ᴷ-trans)
open import adequacy.Rows using (Steps; tau; val)
open import adequacy.Weight using (Clock)

-- `a` no later than `b`.
record _⊑_ (a b : Key) : Set where
  constructor ⊑i
  field un : b <ᴷ a ≡ false

⊑-trans : ∀ {a b c} → a ⊑ b → b ⊑ c → a ⊑ c
⊑-trans {a} {b} {c} ab bc = ⊑i (≮ᴷ-trans c b a (_⊑_.un bc) (_⊑_.un ab))

-- A run from `k` to `k′` showing `rs`.
data Path {R : Set} : Conf R → Shownᴹ R → Conf R → Set₁ where
  []  : ∀ {k} → Path k [] k
  tau : ∀ {k k′ k″ t rs} → Driver.step R k ≡ Driver.silent t k′ → Path k′ rs k″ → Path k rs k″
  val : ∀ {k k′ k″ t p a rs} → Driver.step R k ≡ Driver.value t p a k′ → Path k′ rs k″ → Path k ((p , nx a) ∷ rs) k″

_▸_ : ∀ {R} {k k′ k″ : Conf R} {rs rs′} → Path k rs k′ → Path k′ rs′ k″ → Path k (rs ++ rs′) k″
[]        ▸ q = q
tau e pth ▸ q = tau e (pth ▸ q)
val e pth ▸ q = val e (pth ▸ q)

then : ∀ {R} {k k′ : Conf R} {rs rs′} → Path k rs k′ → Steps k′ rs′ → Steps k (rs ++ rs′)
then []        st = st
then (tau e p) st = tau e (then p st)
then (val e p) st = val e (then p st)

-- What a run shows next.
data Next {R : Set} (k : Conf R) (p : Pos) : Ev R → Set₁ where
  more : ∀ {a k′} → Path k [ (p , nx a) ] k′ → Next k p (out a)
  done : Steps k [ (p , cp) ] → Next k p end

-- `k′` a silent step on from `k`.
_⇜_ : ∀ {R} → Conf R → Conf R → Set₁
_⇜_ {R} k′ k = Σ _ λ τ → Driver.step R k ≡ Driver.silent τ k′

_▸τ_ : ∀ {R} {k k′ k″ : Conf R} {rs} → Path k rs k′ → k″ ⇜ k′ → Path k rs k″
[]        ▸τ (_ , e) = tau e []
tau e pth ▸τ st      = tau e (pth ▸τ st)
val e pth ▸τ st      = val e (pth ▸τ st)

-- `k′` a silent step on from `k`, its clock passing no listed position.
Still : ∀ {R} → List Pos → Conf R → Conf R → Set₁
Still ks k′ k = k′ ⇜ k × (∀ {q} → q ∈ ks → Clock k <ᴷ at q ≡ true → Clock k′ <ᴷ at q ≡ true)

