{-# OPTIONS --guardedness #-}

-- A merge over an outer whose row lies under a timer rooted below one of
-- its own values' first children: the lane subscribed there places a row
-- at that same position, and the merge shows the outer's value just under
-- it.  Every input keeps the invariant; the merge is not flat.
module denotation.EmissionSet.Laws.Refute where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Properties using (≤-refl; 1+n≢n)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import denotation.MonotonicList.Events using (Pos; ix; sub; tick; <ᵖ-part; ix-<)
open import denotation.EmissionSet using (Ev; out; skip; end; EmissionSet; _≺_; Den; cold; enter; flatMapᵀ; module Merge)
open import Tree using (mergeᶠ)
open import denotation.EmissionSet.Laws.Worlds using (Plain; plain-ix; W; W⁼; step; timer; here; inW; Real; real-snoc; Ok; InvAt; InvD; ext≢)

H₀ : Pos → Set
H₀ _ = ⊥

tick-ext : ∀ p ys → Real p → tick (p ++ ys) ≡ tick p
tick-ext (ix _ ∷ _) ys _ = refl

before : ∀ x ys → Real x → x ≺ (ix (suc (tick x)) ∷ ys)
before (ix a ∷ xs) ys _ = Equivalence.from T-≡ (<ᵖ-part [] {ix a} {ix (suc a)} xs ys (ix-< {a} {suc a} ≤-refl))

-- Rows at `p ++ [ ix 0 ]` and under a timer rooted at `anchor p`.
module Two (ex hx : Ev Bool) (ne : ex ≡ end → ⊥) (nh : hx ≡ end → ⊥) (anchor : Pos → Pos)
           (aw : ∀ p → W⁼ H₀ p (anchor p)) (ar : ∀ p → Real p → Real (anchor p)) (at : ∀ p → Real p → tick (anchor p) ≡ tick p) where

  hi : Pos → Pos
  hi p = ix (suc (tick p)) ∷ sub (anchor p) ∷ ix 0 ∷ []

  data R (p : Pos) : EmissionSet Bool where
    lo : R p (p ++ [ ix 0 ]) ex
    up : R p (hi p) hx

  D : Den Bool
  D = cold R

  module _ (p : Pos) (ok : Ok H₀ p) where
    rp = proj₁ ok

    apart : ∀ ys → p ++ ix 0 ∷ ys ≡ hi p → ⊥
    apart ys eq = 1+n≢n (trans (sym (cong tick eq)) (tick-ext p (ix 0 ∷ ys) rp))

    apart′ : ∀ ys → hi p ++ ys ≡ p ++ [ ix 0 ] → ⊥
    assoc0 : ∀ p → (p ++ [ ix 0 ]) ≡ p ++ ix 0 ∷ []
    assoc0 _ = refl

    ++-identityʳ′ : ∀ (x : Pos) → x ≡ x ++ []
    ++-identityʳ′ x = sym (++-identityʳ x)

    apart′ ys eq = 1+n≢n (trans (cong tick eq) (tick-ext p [ ix 0 ] rp))

    wo : ∀ {y e} → R p y e → W H₀ p y
    wo lo = step here plain-ix
    wo up = step (inW (timer (suc (tick p)) (aw p))) plain-ix

    re : ∀ {y e} → R p y e → Real y
    re lo = real-snoc p plain-ix rp
    re up = ar p rp , lt , tt
      where lt : anchor p ≺ (ix (suc (tick p)) ∷ sub (anchor p) ∷ [])
            lt with before (anchor p) (sub (anchor p) ∷ []) (ar p rp)
            ... | b rewrite at p rp = b

    fu : ∀ {y y′ e e′} → R p y e → R p y′ e′ → y ≡ y′ → e ≡ e′
    fu lo lo _  = refl
    fu up up _  = refl
    fu lo up eq = ⊥-elim (apart [] (trans (sym (assoc0 p)) eq))
    fu up lo eq = ⊥-elim (apart′ [] (trans (++-identityʳ′ (hi p)) eq))

    fl : ∀ {y y′ e e′ l ys} → R p y e → R p y′ e′ → y′ ≡ y ++ l ∷ ys → ⊥
    fl {l = l} {ys} lo lo eq = ext≢ (p ++ [ ix 0 ]) ys (sym eq)
    fl {l = l} {ys} lo up eq = apart (l ∷ ys) (sym (trans eq (++-assoc p [ ix 0 ] (l ∷ ys))))
    fl {l = l} {ys} up lo eq = apart′ (l ∷ ys) (sym eq)
    fl {l = l} {ys} up up eq = ext≢ (hi p) ys (sym eq)

    noend : ∀ {y} → R p y end → ⊥
    noend lo = ne refl
    noend up = nh refl

    inv : InvAt H₀ p (enter D p)
    inv = record
      { world = λ x → wo (proj₁ x)
      ; real  = λ x → re (proj₁ x)
      ; func  = λ x x′ → fu (proj₁ x) (proj₁ x′) refl
      ; flat  = λ x x′ → fl (proj₁ x) (proj₁ x′) refl
      ; burst = λ c _ _ → ⊥-elim (noend (proj₁ c))
      }

  invD : InvD H₀ D
  invD = inv

  few : ∀ p q → Σ (List Pos) λ ks → ∀ {k e′} → R p k e′ → k ≺ q → k ∈ ks
  few p q = (p ++ [ ix 0 ]) ∷ hi p ∷ [] , λ { lo _ → here refl ; up _ → there (here refl) }

module O = Two (out true) (out false) (λ ()) (λ ()) (λ p → ((p ++ [ ix 0 ]) ++ [ ix 1 ]) ++ [ ix 0 ])
  (λ p → inW (step {x = (p ++ [ ix 0 ]) ++ [ ix 1 ]} (inW (step {x = p ++ [ ix 0 ]} (inW (step {x = p} here (plain-ix {0}))) (plain-ix {1}))) (plain-ix {0})))
  (λ p r → real-snoc ((p ++ [ ix 0 ]) ++ [ ix 1 ]) {ix 0} plain-ix (real-snoc (p ++ [ ix 0 ]) {ix 1} plain-ix (real-snoc p {ix 0} plain-ix r)))
  (λ { (ix _ ∷ _) _ → refl })

module L = Two skip (out true) (λ ()) (λ ()) (λ s → s ++ [ ix 0 ])
  (λ s → inW (step {x = s} here (plain-ix {0})))
  (λ s r → real-snoc s {ix 0} plain-ix r)
  (λ { (ix _ ∷ _) _ → refl })

None : Den Bool
None = cold λ _ _ _ → ⊥

f : Bool → Den Bool
f true  = L.D
f false = None

f-inv : ∀ a → InvD H₀ (f a)
f-inv true  = L.invD
f-inv false = λ p ok → record
  { world = λ x → ⊥-elim (proj₁ x) ; real = λ x → ⊥-elim (proj₁ x) ; func = λ x _ → ⊥-elim (proj₁ x)
  ; flat = λ x _ → ⊥-elim (proj₁ x) ; burst = λ x _ _ → ⊥-elim (proj₁ x) }

p₀ : Pos
p₀ = ix 0 ∷ []

open Merge f (enter O.D p₀)

rows : List Pos
rows = ((p₀ ++ [ ix 0 ]) ++ [ ix 0 ]) ∷ (O.hi p₀ ++ [ ix 0 ]) ∷ (((p₀ ++ [ ix 0 ]) ++ [ ix 1 ]) ++ [ ix 0 ]) ∷ L.hi ((p₀ ++ [ ix 0 ]) ++ [ ix 1 ]) ∷ []

fewM : ∀ q → Σ (List Pos) λ ks → ∀ {k e′} → MergeT k e′ → k ≺ q → k ∈ ks
fewM q = rows , mem
  where
    mem : ∀ {k e′} → MergeT k e′ → k ≺ q → k ∈ rows
    mem (val (O.lo , _)) _ = here refl
    mem (val (O.up , _)) _ = there (here refl)
    mem (step (() , _)) _
    mem (oend (() , _) _) _
    mem (opass (() , _) _) _
    mem (lane (O.lo , _) ((L.lo , _) , _) _) _ = there (there (here refl))
    mem (lane (O.lo , _) ((L.up , _) , _) _) _ = there (there (there (here refl)))
    mem (lane (O.up , _) ((() , _) , _) _) _
    mem (lend (O.lo , _) ((() , _) , _) _) _
    mem (lend (O.up , _) ((() , _) , _) _) _
    mem (lpass (O.lo , _) ((() , _) , _) _) _
    mem (lpass (O.up , _) ((() , _) , _) _) _

-- The merge's lane row at the outer's timer row, and its value just under.
refuted : (∀ {A B H} op {f : A → Den B} {s : Den A} → InvD H s → (∀ a → InvD H (f a)) → InvD H (flatMapᵀ op f s)) → ⊥
refuted fi = InvAt.flat (fi (mergeᶠ nothing) {f} {O.D} O.invD f-inv p₀ (tt , λ ()))
  (lane (O.lo , O.few p₀ _) ((L.up , L.few _ _) , tt) tt , fewM _)
  (val (O.up , O.few p₀ _) , fewM _)
