{-# OPTIONS --guardedness #-}

-- WHAT A JOINER'S FLAGS READ: the engine's done-flags agree with its
-- rows.  Over where its outer's next row is its end, every lane past it,
-- it runs no lane; over where a lane's end is, every part no earlier,
-- it is done and runs at most that lane; with a value queued, over at no
-- outer end at all, since every queued lane ends past a running one.
module adequacy.Flags where

open import Data.Bool using (Bool; true; T; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length; [_])
open import Data.Nat using (ℕ; zero; suc; pred; _≡ᵇ_; _+_; _≤_)
open import Data.Nat.Properties using (+-identityʳ; +-suc; m+n≮m; <⇒≤; ≤-refl)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import denotation.Events using (Pos; ix)
open import denotation.EmissionSet using (EmissionSet; Ended; out; end; _≺_; _≼_)
open import denotation.Laws.Modulus using (≼-antisym; ≺-trans; ≺-ext)
open import operation.Key using (at)
open import adequacy.Rows using (Lanes; Each; Kth; AllEnd; EndsOf; module Flat; module SwitchF; module ExhaustF; module BoundedF) renaming (sub to subᴿ)
open import adequacy.Bound using (Apart; From; Parts; Spread; _⊑_; above-any; ⊑→≼)
open import adequacy.Skip using (After)
open import adequacy.LaneEnd using (kth-less; kth-lanes; after-lanes)
open import adequacy.Search using (bounded-unqueued)

-- What a race's flags owe its rows.  Nothing queued: a lane's end hands
-- off to none, and the joiner over at a lane's or the outer's end says
-- so in the flag.  A value queued: never over at the outer's end.
Flags : ∀ {A B : Set} → EmissionSet A → List (EmissionSet B) → (Over Hand : Pos → Set) → Bool → ℕ → List A → Set
Flags O Ls Over Hand d n []      = (∀ {Q} → Apart O (Lanes Ls) → From (at Q) O → Lanes Ls Q end → ¬ Hand Q)
                                 × (∀ {Q} → Parts O Ls → From (at Q) O → Each (From (at Q)) Ls → Lanes Ls Q end → Over Q → T (d ∧ (pred n ≡ᵇ 0)))
                                 × (∀ {Q} → From (at Q) O → Each (After Q) Ls → Over Q → T (n ≡ᵇ 0))
Flags O Ls Over Hand d n (_ ∷ _) = ∀ {Q} → From (at Q) O → Each (After Q) Ls → Over Q → ⊥

∧-both : ∀ {a b} → T a → T b → T (a ∧ b)
∧-both {true} _ y = y

-- Every lane past `Q`: none has ended by it.
none-ended : ∀ {B} n (Ls : List (EmissionSet B)) {Q} → Each (After Q) Ls → AllEnd (_≼ Q) n (EndsOf Ls) → T (n ≡ᵇ 0)
none-ended zero    Ls al _ = tt
none-ended (suc k) Ls {Q} al x with kth-lanes {P = _≼ Q} Ls k x
... | _ , l , cq = ⊥-elim (after-lanes {p = Q} Ls al l cq)

-- Lanes from `Q`, apart: no two end by it.
two-ends : ∀ {B} (Ls : List (EmissionSet B)) k {Q} → Spread Ls → Each (From (at Q)) Ls → ¬ Kth (_≼ Q) (EndsOf Ls) (suc k)
two-ends (t ∷ Ls) k {Q} (ap , _) (f , fs) (inj₁ ((c , r , cq) , x)) with kth-lanes Ls k x
... | c′ , l , cq′ with ≼-antisym {c} {Q} cq (⊑→≼ (f r)) | ≼-antisym {c′} {Q} cq′ (⊑→≼ (above-any {P = at Q ⊑_} Ls fs l))
...   | refl | refl = ap r l
two-ends (t ∷ Ls) k (_ , sp) (_ , fs) (inj₂ x) = two-ends Ls k sp fs x

one-ended : ∀ {B} n (Ls : List (EmissionSet B)) {Q} → Spread Ls → Each (From (at Q)) Ls → AllEnd (_≼ Q) n (EndsOf Ls) → T (pred n ≡ᵇ 0)
one-ended zero          Ls sp fs _ = tt
one-ended (suc zero)    Ls sp fs _ = tt
one-ended (suc (suc k)) Ls sp fs x = ⊥-elim (two-ends Ls k sp fs x)

-- The outer from `Q`, apart from a lane's end there: done by its flag.
outer-on : ∀ {A B} {O : EmissionSet A} {Ls : List (EmissionSet B)} {Q d} → Apart O (Lanes Ls) → From (at Q) O → Lanes Ls Q end → T d ⊎ Ended O Q → T d
outer-on ap fo x (inj₁ td)              = td
outer-on {Q = Q} ap fo x (inj₂ (c₀ , r , cq)) with ≼-antisym {c₀} {Q} cq (⊑→≼ (fo r))
... | refl = ⊥-elim (ap r x)

-- The outer from `Q`: no value of it before.
unkilled : ∀ {A} {O : EmissionSet A} {Q} → From (at Q) O → ¬ (Σ Pos λ q′ → Σ A λ a′ → O q′ (out a′) × q′ ≺ Q)
unkilled fo (_ , _ , r , lt) = ⊑→≼ (fo r) lt

flat-flags : ∀ {A B} (L : A → Pos → EmissionSet B) O d n Ls → Flags O Ls (Flat.Over L O d n Ls) (λ _ → ⊥) d n []
flat-flags L O d n Ls =
  (λ _ _ _ ()) ,
  (λ { {Q} (ap , sp) fo fl x (Flat.over-at oo lo) → ∧-both (outer-on {Q = Q} (λ {q} {e} {e′} → ap {q} {e} {e′}) (λ {q} {e} → fo {q} {e}) x oo) (one-ended n Ls {Q} sp fl lo) }) ,
  (λ { {Q} fo al (Flat.over-at _ lo) → none-ended n Ls {Q} al lo })

switch-flags : ∀ {A B} (L : A → Pos → EmissionSet B) O d n Ls → Flags O Ls (SwitchF.Over L O d n Ls) (λ _ → ⊥) d n []
switch-flags L O d n Ls =
  (λ _ _ _ ()) ,
  (λ { {Q} (ap , sp) fo fl x (oo , inj₁ lo) → ∧-both (outer-on {Q = Q} (λ {q} {e} {e′} → ap {q} {e} {e′}) (λ {q} {e} → fo {q} {e}) x oo) (one-ended n Ls {Q} sp fl lo)
     ; {Q} (ap , sp) fo fl x (oo , inj₂ k)  → ⊥-elim (unkilled {Q = Q} (λ {q} {e} → fo {q} {e}) k) }) ,
  (λ { {Q} fo al (_ , inj₁ lo) → none-ended n Ls {Q} al lo
     ; {Q} fo al (_ , inj₂ k)  → ⊥-elim (unkilled {Q = Q} (λ {q} {e} → fo {q} {e}) k) })

exhaust-flags : ∀ {A B} (L : A → Pos → EmissionSet B) O d n Ls → Flags O Ls (ExhaustF.Over L O d n Ls) (λ _ → ⊥) d n []
exhaust-flags L O d n Ls =
  (λ _ _ _ ()) ,
  (λ { {Q} (ap , sp) fo fl x (oo , lo) → ∧-both (outer-on {Q = Q} (λ {q} {e} {e′} → ap {q} {e} {e′}) (λ {q} {e} → fo {q} {e}) x oo) (one-ended n Ls {Q} sp fl lo) }) ,
  (λ { {Q} fo al (_ , lo) → none-ended n Ls {Q} al lo })

bounded-flags : ∀ {A B} m (L : A → Pos → EmissionSet B) O d n Ls → Flags O Ls (BoundedF.Over m L O d n [] Ls) (BoundedF.Queued m L O d n [] Ls) d n []
bounded-flags m L O d n Ls =
  (λ {Q} ap fo x → bounded-unqueued m L O Ls d n {Q} (λ {q} {e} {e′} → ap {q} {e} {e′}) (λ {q} {e} → fo {q} {e}) x) ,
  (λ { {Q} (ap , sp) fo fl x (oo , lo) → ∧-both (outer-on {Q = Q} (λ {q} {e} {e′} → ap {q} {e} {e′}) (λ {q} {e} → fo {q} {e}) x oo) (one-ended n Ls {Q} sp fl (counted lo)) }) ,
  (λ { {Q} fo al (_ , lo) → none-ended n Ls {Q} al (counted lo) })
  where
    counted : ∀ {P} → AllEnd P (n + 0) (EndsOf Ls) → AllEnd P n (EndsOf Ls)
    counted {P} = subst (λ k → AllEnd P k (EndsOf Ls)) (+-identityʳ n)

kth-zero : ∀ {P} ls k → Kth P ls k → Kth P ls 0
kth-zero ls zero    x = x
kth-zero ls (suc k) x = kth-zero ls k (kth-less ls k x)

kth-pick : ∀ {Q} ls → Kth (_≼ Q) ls 0 → Σ Pos λ c → Kth (_≡ c) ls 0 × c ≼ Q
kth-pick {Q} (l ∷ ls) (inj₁ (c , lc , cq)) = c , inj₁ (c , lc , refl) , cq
kth-pick {Q} (l ∷ ls) (inj₂ x) with kth-pick {Q} ls x
... | c , y , cq = c , inj₂ y , cq

-- Every lane past `Q`: every end the schedule reads before the outer's
-- own lanes lies past it, a queued lane starting past an end before it.
module Queue {A B : Set} (m : ℕ) (L : A → Pos → EmissionSet B) (O : EmissionSet A) (d : Bool) (n : ℕ) (Qu : List A) (Ls : List (EmissionSet B))
             {Q} (al : Each (After Q) Ls) where
  open BoundedF m L O d n Qu Ls

  begun-past : ∀ (Ls′ : List (EmissionSet B)) → Each (After Q) Ls′ → ∀ {c} → Kth (_≡ c) (EndsOf Ls′) 0 → Q ≺ c
  begun-past (_ ∷ _)   (a , _)  (inj₁ (_ , r , refl)) = a r
  begun-past (_ ∷ Ls′) (_ , as) (inj₂ x)             = begun-past Ls′ as x

  mutual
    sched-past : ∀ i → i ≤ length Qu → ∀ {c} → Kth (_≡ c) (Sched i) 0 → Q ≺ c
    sched-past zero    _  x                                                  = begun-past Ls al x
    sched-past (suc i) le (inj₁ (_ , (_ , _ , _ , it , st , subᴿ _ ps) , refl)) = start-past i le it st ps
    sched-past (suc i) le (inj₂ x)                                           = sched-past i (<⇒≤ le) x

    start-past : ∀ i {w a s c} → suc i ≤ length Qu → Item i w a → Starts i (Sched i) w s → s ≺ c → Q ≺ c
    start-past .(length Qu + _) le (Item.outer _) _ _ = ⊥-elim (m+n≮m (length Qu) _ le)
    start-past i {c = c} le (Item.queued _) (Starts.queued {c = c″} _ _ x _ _) ps =
      ≺-trans {Q} {c″} {c} (sched-past i (<⇒≤ le) x) (≺-trans {c″} {c″ ++ [ ix 1 ]} {c} (≺-ext c″ []) ps)

queued-flags : ∀ {A B} m (L : A → Pos → EmissionSet B) O d n (a : A) q Ls → Flags O Ls (BoundedF.Over m L O d n (a ∷ q) Ls) (BoundedF.Queued m L O d n (a ∷ q) Ls) d n (a ∷ q)
queued-flags m L O d n a q Ls {Q} fo al (_ , lo) = none (kth-pick {Q} S (kth-zero S (n + length q) (subst (λ k → AllEnd (_≼ Q) k S) (+-suc n (length q)) lo)))
  where
    S = BoundedF.Sched m L O d n (a ∷ q) Ls (suc (length q))
    none : ¬ (Σ Pos λ c → Kth (_≡ c) S 0 × c ≼ Q)
    none (c , x , cq) = cq (Queue.sched-past m L O d n (a ∷ q) Ls {Q} al (suc (length q)) ≤-refl x)
