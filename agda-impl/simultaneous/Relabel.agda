{-# OPTIONS --guardedness #-}

-- A STREAM THAT RELABELS ITS SOURCE HOLDS WHAT ITS SOURCE HOLDS.  When
-- every run met of `t′` is a run met of `t`, row for row at the same
-- positions, each mark kept and each value still a value of the same
-- name, the count reads the same marks in the same order: a route held
-- under one is held under the other, a begin stays a begin, and a dead
-- instant's values are the same rows.
module simultaneous.Relabel where

open import Data.List using (List; []; _∷_; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there; any?)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
open import Relation.Nullary using (¬_; does)
open import Relation.Nullary.Decidable using (decidable-stable)
open import Data.Maybe using (Maybe)

open import denotation.Events using (Pos; Timeline; root; fresh; _≟ᵖ_)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; Few; _≺_)
open import denotation.Read using (Visible; After; cursor)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; stop; over; outerOpen; outerClose; laneStart; carry; laneDone;
  burstEnd; outerDone; subscribed; completed)
open import simultaneous.SObs using (module Elaborate)
open import simultaneous.Relations using (Met; values)
open import simultaneous.Shut using (Shut; r₀)
open import simultaneous.Routed using (Held; Idle; Carried; c-value; c-stop; c-over; c-end; cnt; Ex; nameOf; Routing; Early; Valued; opos)
open import simultaneous.Readings using (instantOf)
open import denotation.Laws.Worlds using (_⊑_)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (IE; Routes; count)

------------------------------------------------------------------------
-- Same marks

-- `x′` is `x` with at most its value changed.
data Same {A B : Set} : IE B → IE A → Set where
  same-mark  : ∀ {m n} → Same (instEmit (mark m) n) (instEmit (mark m) n)
  same-value : ∀ {a b n} → Same (instEmit (value b) n) (instEmit (value a) n)

data EvSame {A B : Set} : Ev (IE B) → Ev (IE A) → Set where
  ev-out : ∀ {x′ x} → Same x′ x → EvSame (out x′) (out x)
  ev-end : EvSame end end

data Rows≈ {A B : Set} : List (Pos × Ev (IE B)) → List (Pos × Ev (IE A)) → Set where
  []  : Rows≈ [] []
  _∷_ : ∀ {q e′ e rs′ rs} → EvSame e′ e → Rows≈ rs′ rs → Rows≈ ((q , e′) ∷ rs′) ((q , e) ∷ rs)

------------------------------------------------------------------------
-- The count reads the same marks

count-same : ∀ {A B : Set} r {x′ : IE B} {x : IE A} → Same x′ x → count r x′ ≡ count r x
count-same r                        (same-value)                   = refl
count-same (m , k) {instEmit (mark begin) n} same-mark with does (n ≟ᵖ m)
... | true  = refl
... | false = refl
count-same r {instEmit (mark stop) _}       same-mark = refl
count-same r {instEmit (mark over) _}       same-mark = refl
count-same r {instEmit (mark outerOpen) _}  same-mark = refl
count-same r {instEmit (mark outerClose) _} same-mark = refl
count-same r {instEmit (mark laneStart) _}  same-mark = refl
count-same r {instEmit (mark carry) _}      same-mark = refl
count-same r {instEmit (mark laneDone) _}   same-mark = refl
count-same r {instEmit (mark burstEnd) _}   same-mark = refl
count-same r {instEmit (mark outerDone) _}  same-mark = refl
count-same r {instEmit (mark subscribed) _} same-mark = refl
count-same r {instEmit (mark completed) _}  same-mark = refl

fold-same : ∀ {A B : Set} r {rs′ : List (Pos × Ev (IE B))} {rs : List (Pos × Ev (IE A))} → Rows≈ rs′ rs
          → L.foldl count r (values rs′) ≡ L.foldl count r (values rs)
fold-same r []                    = refl
fold-same r (ev-out s ∷ eq) rewrite count-same r s = fold-same _ eq
fold-same r (ev-end ∷ eq)         = fold-same r eq

cnt-same : ∀ {A B : Set} {rs′ : List (Pos × Ev (IE B))} {rs : List (Pos × Ev (IE A))} → Rows≈ rs′ rs → cnt rs′ ≡ cnt rs
cnt-same = fold-same r₀

------------------------------------------------------------------------
-- Rows

split≈ : ∀ {A B : Set} {rs′ : List (Pos × Ev (IE B))} {rs : List (Pos × Ev (IE A))} → Rows≈ rs′ rs
       → ∀ r₁′ r₂′ → rs′ ≡ r₁′ ++ r₂′
       → Σ _ λ r₁ → Σ _ λ r₂ → rs ≡ r₁ ++ r₂ × Rows≈ r₁′ r₁ × Rows≈ r₂′ r₂
split≈ eq         []        r₂′ refl = [] , _ , refl , [] , eq
split≈ (s ∷ eq)   (_ ∷ r₁′) r₂′ refl with split≈ eq r₁′ r₂′ refl
... | r₁ , r₂ , refl , e₁ , e₂ = _ ∷ r₁ , r₂ , refl , s ∷ e₁ , e₂

head≈ : ∀ {A B : Set} {y e′ r₂′} {r₂ : List (Pos × Ev (IE A))} → Rows≈ {B = B} ((y , e′) ∷ r₂′) r₂
      → Σ _ λ e → Σ _ λ r₂₀ → r₂ ≡ (y , e) ∷ r₂₀ × EvSame e′ e
head≈ (s ∷ eq) = _ , _ , refl , s

mem≈ : ∀ {A B : Set} {rs′ : List (Pos × Ev (IE B))} {rs : List (Pos × Ev (IE A))} → Rows≈ rs′ rs
     → ∀ {q x′} → (q , out x′) ∈ rs′ → Σ (IE A) λ x → (q , out x) ∈ rs × Same x′ x
mem≈ (ev-out s ∷ _) (here refl) = _ , here refl , s
mem≈ (_ ∷ eq)       (there m)   with mem≈ eq m
... | x , m′ , s = x , there m′ , s

cursor≈ : ∀ {A B : Set} {rs′ : List (Pos × Ev (IE B))} {rs : List (Pos × Ev (IE A))} → Rows≈ rs′ rs
        → ∀ (c : Maybe Pos) → cursor c rs′ ≡ cursor c rs
cursor≈ []       c = refl
cursor≈ (_ ∷ eq) c = cursor≈ eq _

end≈ : ∀ {A B : Set} {rs′ : List (Pos × Ev (IE B))} {rs : List (Pos × Ev (IE A))} → Rows≈ rs′ rs
     → ∀ {c} → (c , end) ∈ rs → (c , end) ∈ rs′
end≈ (ev-end ∷ _) (here refl) = here refl
end≈ (_ ∷ eq)     (there m)   = there (end≈ eq m)

carried-same : ∀ {A B : Set} {e′ : Ev (IE B)} {e : Ev (IE A)} → EvSame e′ e → Carried e′ → Carried e
carried-same (ev-out same-value) c-value = c-value
carried-same (ev-out same-mark)  c-stop  = c-stop
carried-same (ev-out same-mark)  c-over  = c-over
carried-same ev-end              c-end   = c-end

------------------------------------------------------------------------
-- Held carries over

held-same : ∀ {A B : Set} {t : EmissionSet (IE A)} {t′ : EmissionSet (IE B)} {cs}
          → (∀ {y x′} → t′ y (out x′) → Σ (IE A) λ x → t y (out x) × Same x′ x)
          → (∀ {y} → t′ y end → t y end)
          → (∀ {rs′} → Met t′ rs′ → Σ _ λ rs → Met t rs × Rows≈ rs′ rs)
          → (∀ {w} → Few t′ w → ∀ {k e} → t k e → k ≺ w → ¬ ¬ Σ _ λ e′ → t′ k e′ × (Visible e → Visible e′))
          → Held t cs → Held t′ cs
held-same {t = t} {t′} {cs} row end-row back fwd H = record
  { named = named ; covered = covered ; exact = exact ; routing = routing ; shut = shut
  ; early = early ; ends = λ x → Held.ends H (end-row x) ; late = late ; idle = idle }
  where
    early : ∀ {y a n} → t′ y (out (instEmit (value a) n)) → Early y
    early x with row x
    ... | _ , y , same-value = Held.early H y

    late : ∀ {y n} → t′ y (out (instEmit (mark over) n)) → Valued (instantOf y) × opos (instantOf y) ⊑ y
    late x with row x
    ... | _ , y , same-mark = Held.late H y

    named : ∀ {y n} → t′ y (out (instEmit (mark begin) n)) → n ≡ nameOf y
    named x with row x
    ... | _ , y , same-mark = Held.named H y

    covered : ∀ {rs′} → Met t′ rs′ → ∀ r₁′ {y e′} r₂′ → rs′ ≡ r₁′ ++ (y , e′) ∷ r₂′ → Carried e′ → ¬ Ex cs y
            → Σ ℕ λ k → cnt r₁′ ≡ (nameOf y , suc k)
    covered m r₁′ r₂′ e c nx with back m
    ... | rs , run , eq with split≈ eq r₁′ _ e
    ...   | r₁ , r₂ , refl , e₁ , e₂ with head≈ e₂
    ...     | _ , r₂₀ , refl , s =
      subst (λ r → Σ _ λ k → r ≡ _) (sym (cnt-same e₁)) (Held.covered H run r₁ r₂₀ refl (carried-same s c) nx)

    exact : ∀ {rs′} → Met t′ rs′ → ∀ r₁′ {y n} r₂′ → rs′ ≡ r₁′ ++ (y , out (instEmit (mark stop) n)) ∷ r₂′
          → Σ ℕ λ k → proj₂ (cnt r₁′) ≡ suc k
    exact m r₁′ r₂′ e with back m
    ... | rs , run , eq with split≈ eq r₁′ _ e
    ...   | r₁ , r₂ , refl , e₁ , e₂ with head≈ e₂
    ...     | _ , r₂₀ , refl , ev-out same-mark =
      subst (λ r → Σ _ λ k → proj₂ r ≡ _) (sym (cnt-same e₁)) (Held.exact H run r₁ r₂₀ refl)

    idle : Idle t′
    idle m ne {w} F aw later with back m
    ... | rs , run , eq =
      subst (λ r → proj₂ r ≡ 0 ⊎ proj₁ r ≡ nameOf w) (sym (cnt-same eq))
        (Held.idle H run (λ ce → ne (end≈ eq ce)) few (subst (λ c → After c w) (cursor≈ eq _) aw)
          λ ty vy ay yw → fwd F ty yw λ (_ , t′y , vv) → later t′y (vv vy) (subst (λ c → After c _) (sym (cursor≈ eq _)) ay) yw)
      where
        few : Few t w
        few = proj₁ F , λ {k} tk kw → decidable-stable (any? (k ≟ᵖ_) (proj₁ F)) λ nm → fwd F tk kw λ (_ , t′k , _) → nm (proj₂ F t′k kw)

    routing : ∀ {y m n} → t′ y (out (instEmit (mark m) n)) → Routing m
    routing x with row x
    ... | _ , y , same-mark = Held.routing H y

    shut : Shut t′
    shut m r₁′ r₂′ e z bq vy iq with back m
    ... | rs , run , eq with split≈ eq r₁′ r₂′ e
    ...   | r₁ , r₂ , refl , e₁ , e₂ with mem≈ e₁ bq | mem≈ e₂ vy
    ...     | _ , bq′ , same-mark | _ , vy′ , same-value =
      Held.shut H run r₁ r₂ refl (subst (λ r → proj₂ r ≡ 0) (cnt-same e₁) z)
        (subst (λ n → (_ , out (instEmit (mark begin) n)) ∈ r₁) (cong proj₁ (cnt-same e₁)) bq′) vy′ iq
