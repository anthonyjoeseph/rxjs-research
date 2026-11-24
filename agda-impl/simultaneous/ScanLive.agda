{-# OPTIONS --guardedness #-}

-- WHAT THE SCAN HOLDS OF A CONNECT IN SCOPE IS THAT CONNECT'S LAST REPORT:
-- only a tracker's row moves `live`, setting its own index, and a padded
-- index holds nothing.
module simultaneous.ScanLive where

open import Data.Bool using (true; false; _∧_; _∨_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (yes; no; does)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; end; skip; pin)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; stop; over; outerOpen; outerClose; laneStart; laneDone;
  burstEnd; outerDone; subscribed; completed)
open import simultaneous.SObs using (Flat; isZero; lone; module Elaborate; outerB; laneB; closeB)
open import simultaneous.HeldComb using (past; init)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (Routes; Out; Input; react; onMark; begun; entered;
  bump; share; stopped; overed; cut; unpark; arrive; ended; burstOver; left; anyHolds; holds; setAt; anew)

Row : Set → Set
Row B = Pos × Ev (Maybe (Input B))

-- The routes at an index of what the scan holds.
data _[_]≔_ : List Routes → ℕ → Routes → Set where
  at-here  : ∀ {r l} → (r ∷ l) [ 0 ]≔ r
  at-there : ∀ {x l i r} → l [ i ]≔ r → (x ∷ l) [ suc i ]≔ r

-- No tracker row of index `j`.
NoJ : ∀ {B} → ℕ → List (Row B) → Set
NoJ j rx = ∀ {z r} → (z , out (just (inj₂ (j , r)))) ∈ rx → ⊥

-- The last tracker row of index `i` reports `r`.
LastIn : ∀ {B} → ℕ → Routes → List (Row B) → Set
LastIn i r rx = Σ _ λ xs → Σ _ λ ys → Σ Pos λ y → rx ≡ xs ++ (y , out (just (inj₂ (i , r)))) ∷ ys × NoJ i ys

------------------------------------------------------------------------
-- Holding

holds-at : ∀ {n r} → holds n r ≡ true → proj₁ r ≡ n × (proj₂ r ≡ 0 → ⊥)
holds-at {n} {m , zero} h with m ≟ᵖ n
holds-at {n} {m , zero} () | yes _
holds-at {n} {m , zero} () | no _
holds-at {n} {m , suc k} h with m ≟ᵖ n
holds-at {n} {m , suc k} h  | yes eq = eq , λ ()
holds-at {n} {m , suc k} () | no _

any-at : ∀ {n} l → anyHolds n l ≡ true → Σ ℕ λ i → Σ Routes λ r → l [ i ]≔ r × holds n r ≡ true
any-at {n} (r ∷ σ) h with holds n r in hr
... | true  = 0 , r , at-here , hr
... | false with any-at σ h
...   | i , r′ , a , h′ = suc i , r′ , at-there a , h′

-- A padded index holds nothing.
pad-none : ∀ {n} i {r} → setAt i r [] [ i ]≔ r × (∀ {j r′} → setAt i r [] [ j ]≔ r′ → holds n r′ ≡ true → j ≡ i × r′ ≡ r)
pad-none zero    = at-here , λ { at-here _ → refl , refl ; (at-there ()) _ }
pad-none {n} (suc i) {r} = at-there (proj₁ (pad-none {n} i)) , go
  where
    go : ∀ {j r′} → setAt (suc i) r [] [ j ]≔ r′ → holds n r′ ≡ true → j ≡ suc i × r′ ≡ r
    go at-here      h = ⊥-elim (proj₂ (holds-at {n} {root , 0} h) refl)
    go (at-there a) h with proj₂ (pad-none {n} i) a h
    ... | refl , refl = refl , refl

-- An index `setAt` writes holds what it writes; any other what it held.
set-at : ∀ {n} i r l {j r′} → setAt i r l [ j ]≔ r′ → holds n r′ ≡ true → (j ≡ i × r′ ≡ r) ⊎ ((j ≡ i → ⊥) × l [ j ]≔ r′)
set-at {n} i r [] a h = inj₁ (proj₂ (pad-none {n} i) a h)
set-at zero    r (x ∷ σ) at-here       h = inj₁ (refl , refl)
set-at zero    r (x ∷ σ) (at-there a)  h = inj₂ ((λ ()) , at-there a)
set-at (suc i) r (x ∷ σ) at-here       h = inj₂ ((λ ()) , at-here)
set-at {n} (suc i) r (x ∷ σ) (at-there a) h with set-at {n} i r σ a h
... | inj₁ (refl , refl) = inj₁ (refl , refl)
... | inj₂ (ne , a′)     = inj₂ ((λ { refl → ne refl }) , at-there a′)

------------------------------------------------------------------------
-- Only a tracker's row moves what the scan holds

Live : ∀ {B} → Flat Pos → Out B → Set
Live s o = Flat.live (proj₁ o) ≡ Flat.live s

cut-live : ∀ {B} k n s → Live s (cut {B} k n s)
cut-live k n s with Flat.spent s | anyHolds (Flat.at s) (Flat.live s)
... | true  | _     = refl
... | false | true  = refl
... | false | false = refl

unpark-live : ∀ {B} n s → Live s (unpark {B} n s)
unpark-live n s with anyHolds (Flat.at s) (Flat.live s)
... | true  = refl
... | false = refl

arrive-live : ∀ {B} op n s → Live s (arrive {B} op n s)
arrive-live (mergeᶠ (just _)) n s = refl
arrive-live (mergeᶠ nothing)  n s = refl
arrive-live switchᶠ           n s = cut-live (Flat.lanes s) n (record s { active = 0 ; lanes = 0 })
arrive-live exhaustᶠ          n s = refl

ended-live : ∀ {B} k n s → Live s (ended {B} k n s)
ended-live k n s with isZero (Flat.queue s)
... | false = refl
... | true with Flat.finished s ∧ isZero (Flat.active s)
...   | true  = refl
...   | false = cut-live (k + Flat.held s) n (record s { held = 0 })

burst-live : ∀ {B} h n s → Live s (burstOver {B} h n s)
burst-live true  n s = refl
burst-live false n s = cut-live (Flat.held s) n (record s { held = 0 })

left-live : ∀ {B} n s → Live s (left {B} n s)
left-live n s with isZero (Flat.active s) ∧ isZero (Flat.queue s)
... | true  = refl
... | false = cut-live (Flat.outer s) n (record s { outer = 0 })

bump-live : ∀ b f s → Flat.live (bump b f s) ≡ Flat.live s
bump-live outerB f s = refl
bump-live laneB  f s = refl
bump-live closeB f s = refl

entered-live : ∀ b n s → Flat.live (entered b n s) ≡ Flat.live s
entered-live b n s with does (n ≟ᵖ Flat.at s)
... | true  = bump-live b suc s
... | false = bump-live b suc (anew n s)

begun-live : ∀ {B} b n s → Live s (begun {B} b n s)
begun-live b n s with does (n ≟ᵖ Flat.at s) ∧ Flat.spent s
... | true  = refl
... | false = entered-live b n s

stopped-live : ∀ {B} b n s k → Live s (stopped {B} b n s k)
stopped-live b n s zero    = refl
stopped-live b n s (suc _) = bump-live b _ s

overed-live : ∀ {B} n s → Live s (overed {B} n s)
overed-live n s with Flat.spent s
... | true  = refl
... | false = refl

mark-live : ∀ {B} op b s m n → Live s (onMark {B} op b s m n)
mark-live op b s begin         n = begun-live b n s
mark-live op b s stop          n = stopped-live b n s (if Flat.spent s then 0 else share b s)
mark-live op b s over          n = overed-live n s
mark-live op b s outerOpen     n = arrive-live op n s
mark-live op b s outerClose    n = refl
mark-live op b s laneStart     n = refl
mark-live op b s (laneDone k)  n = ended-live _ n (record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ k ; dead = true })
mark-live op b s burstEnd      n = burst-live (isZero (Flat.held s) ∨ Flat.dead s) n s
mark-live op b s outerDone     n = left-live n (record s { finished = true })
mark-live op b s subscribed    n = refl
mark-live op b s completed     n = refl

react-live : ∀ {B} op (o : Out B) x → (∀ {i r} → x ≡ just (inj₂ (i , r)) → ⊥) → Live (proj₁ o) (react op o x)
react-live op o (just (inj₁ (b , instEmit (value v) n))) _ = refl
react-live op o (just (inj₁ (b , instEmit (mark m) n)))  _ = mark-live op b (proj₁ o) m n
react-live op o (just (inj₂ _))                          nt = ⊥-elim (nt refl)
react-live op o nothing                                  _ = refl

------------------------------------------------------------------------
-- The last report

last-from : ∀ {B} op (o : Out B) rx → (∀ {c} → (c , end) ∈ rx → ⊥) → ∀ {n j r′}
          → Flat.live (proj₁ (past op o rx)) [ j ]≔ r′ → holds n r′ ≡ true
          → (Flat.live (proj₁ o) [ j ]≔ r′ × NoJ j rx) ⊎ LastIn j r′ rx
last-from op o []                 ne a h = inj₁ (a , λ ())
last-from op o ((k , end) ∷ rx)   ne a h = ⊥-elim (ne (here refl))
last-from op o ((k , skip) ∷ rx)  ne a h with last-from op o rx (λ i → ne (there i)) a h
... | inj₁ (a′ , nj)                 = inj₁ (a′ , λ { (here ()) ; (there i) → nj i })
... | inj₂ (xs , ys , y , refl , nj) = inj₂ ((k , skip) ∷ xs , ys , y , refl , nj)
last-from op o ((k , pin s) ∷ rx) ne a h with last-from op o rx (λ i → ne (there i)) a h
... | inj₁ (a′ , nj)                 = inj₁ (a′ , λ { (here ()) ; (there i) → nj i })
last-from op o ((k , pin s) ∷ rx) ne a h | inj₂ (xs , ys , y , refl , nj) = inj₂ ((k , pin s) ∷ xs , ys , y , refl , nj)
last-from op o ((k , out (just (inj₂ (i , r)))) ∷ rx) ne {j = j} {r′} a h with last-from op (react op o (just (inj₂ (i , r)))) rx (λ c → ne (there c)) a h
... | inj₂ (xs , ys , y , refl , nj) = inj₂ ((k , out (just (inj₂ (i , r)))) ∷ xs , ys , y , refl , nj)
... | inj₁ (a′ , nj) with set-at i r (Flat.live (proj₁ o)) (subst (_[ j ]≔ r′) (unpark-live root (record (proj₁ o) { live = setAt i r (Flat.live (proj₁ o)) })) a′) h
...   | inj₁ (refl , refl) = inj₂ ([] , rx , k , refl , nj)
...   | inj₂ (ne′ , a″)    = inj₁ (a″ , λ { (here refl) → ne′ refl ; (there c) → nj c })
last-from op o ((k , out (just (inj₁ v))) ∷ rx) ne a h with last-from op (react op o (just (inj₁ v))) rx (λ c → ne (there c)) a h
... | inj₂ (xs , ys , y , refl , nj) = inj₂ ((k , out (just (inj₁ v))) ∷ xs , ys , y , refl , nj)
... | inj₁ (a′ , nj) = inj₁ (subst (_[ _ ]≔ _) (react-live op o (just (inj₁ v)) (λ ())) a′ , λ { (here ()) ; (there c) → nj c })
last-from op o ((k , out nothing) ∷ rx) ne a h with last-from op (react op o nothing) rx (λ c → ne (there c)) a h
... | inj₂ (xs , ys , y , refl , nj) = inj₂ ((k , out nothing) ∷ xs , ys , y , refl , nj)
... | inj₁ (a′ , nj) = inj₁ (a′ , λ { (here ()) ; (there c) → nj c })

-- WHAT THE SCAN HOLDS AN INSTANT BY: some connect's last report.
live-last : ∀ {B} op (rx : List (Row B)) → (∀ {c} → (c , end) ∈ rx → ⊥) → ∀ {n}
          → anyHolds n (Flat.live (proj₁ (past op init rx))) ≡ true → Σ ℕ λ i → Σ Routes λ r → holds n r ≡ true × LastIn i r rx
live-last op rx ne h with any-at _ h
... | i , r , a , hr with last-from op init rx ne a hr
...   | inj₁ (() , _)
...   | inj₂ l = i , r , hr , l
