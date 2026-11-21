{-# OPTIONS --guardedness #-}

-- A STREAM THAT RELABELS ITS SOURCE HOLDS WHAT ITS SOURCE HOLDS.  When
-- every run met of `t′` is a run met of `t`, row for row at the same
-- positions, each mark kept, a begin under its own name, and each value
-- still a value, the count reads the same marks in the same order: a route held
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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst; subst₂; trans)
open import Relation.Nullary using (¬_; does)
open import Relation.Nullary.Decidable using (decidable-stable)
open import Data.Maybe using (Maybe)

open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; Few; _≺_)
open import denotation.Read using (Visible; After; cursor)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; stop; over; outerOpen; outerClose; laneStart; carry; laneDone;
  burstEnd; outerDone; subscribed; completed)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Relations using (Met; values)
open import simultaneous.Shut using (Shut; r₀)
open import simultaneous.Routed using (Held; Idle; Rest; Carried; c-value; c-stop; c-over; c-done; c-end; cnt; Ex; nameOf; nm; Routing; Early; Valued; opos)
open import simultaneous.Readings using (rootOf)
open import denotation.Laws.Worlds using (_⊑_)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Routes; count)

------------------------------------------------------------------------
-- Same marks

-- `x′` is `x` with at most its value, or a name no count reads, changed.
data Same {A B : Set} : IE B → IE A → Set where
  same-mark  : ∀ {m n n′} → (m ≡ begin → n′ ≡ n) → Same (instEmit (mark m) n′) (instEmit (mark m) n)
  same-value : ∀ {a b n n′} → Same (instEmit (value b) n′) (instEmit (value a) n)

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
count-same (m , k) {instEmit (mark begin) n} (same-mark e) with e refl
... | refl with does (n ≟ᵖ m)
...   | true  = refl
...   | false = refl
count-same r {instEmit (mark stop) _}       (same-mark _) = refl
count-same r {instEmit (mark over) _}       (same-mark _) = refl
count-same r {instEmit (mark outerOpen) _}  (same-mark _) = refl
count-same r {instEmit (mark outerClose) _} (same-mark _) = refl
count-same r {instEmit (mark laneStart) _}  (same-mark _) = refl
count-same r {instEmit (mark carry) _}      (same-mark _) = refl
count-same r {instEmit (mark laneDone) _}   (same-mark _) = refl
count-same r {instEmit (mark burstEnd) _}   (same-mark _) = refl
count-same r {instEmit (mark outerDone) _}  (same-mark _) = refl
count-same r {instEmit (mark subscribed) _} (same-mark _) = refl
count-same r {instEmit (mark completed) _}  (same-mark _) = refl

fold-same : ∀ {A B : Set} r {rs′ : List (Pos × Ev (IE B))} {rs : List (Pos × Ev (IE A))} → Rows≈ rs′ rs
          → L.foldl count r (values rs′) ≡ L.foldl count r (values rs)
fold-same r []                    = refl
fold-same r (ev-out s ∷ eq) rewrite count-same r s = fold-same _ eq
fold-same r (ev-end ∷ eq)         = fold-same r eq

cnt-same : ∀ {A B : Set} {rs′ : List (Pos × Ev (IE B))} {rs : List (Pos × Ev (IE A))} → Rows≈ rs′ rs → cnt rs′ ≡ cnt rs
cnt-same = fold-same r₀

------------------------------------------------------------------------
-- Rows

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
carried-same (ev-out (same-mark _)) c-stop = c-stop
carried-same (ev-out (same-mark _)) c-over = c-over
carried-same (ev-out (same-mark _)) c-done = c-done
carried-same ev-end              c-end   = c-end

------------------------------------------------------------------------
-- Held carries over

-- A relabelling whose every row lies where one of its source's does
-- finishes its instants where its source does.
rest-same : ∀ {A B : Set} {t : EmissionSet (IE A)} {t′ : EmissionSet (IE B)}
          → (∀ {y e′} → t′ y e′ → Σ _ (t y))
          → (∀ {rs′} → Met t′ rs′ → Σ _ λ rs → Met t rs × Rows≈ rs′ rs)
          → Rest t → Rest t′
rest-same every back R m z bq with back m
... | rs , run , eq with mem≈ eq bq
...   | _ , bq′ , same-mark e with R run (subst (λ r → proj₂ r ≡ 0) (cnt-same eq) z)
                                      (subst (λ n → (_ , out (instEmit (mark begin) n)) ∈ rs) (trans (sym (e refl)) (cong proj₁ (cnt-same eq))) bq′)
...     | ks , h = ks , λ ty ay iq → h (proj₂ (every ty)) (subst (λ c → After c _) (cursor≈ eq _) ay) iq

------------------------------------------------------------------------
-- Rows at related positions

-- Row for row, each at a position `R` relates to its source's.
data RowsAt {A B : Set} (R : Pos → Pos → Set) : List (Pos × Ev (IE B)) → List (Pos × Ev (IE A)) → Set where
  []ᵃ  : RowsAt R [] []
  _∷ᵃ_ : ∀ {q′ q e′ e rs′ rs} → R q′ q × EvSame e′ e → RowsAt R rs′ rs → RowsAt R ((q′ , e′) ∷ rs′) ((q , e) ∷ rs)

at≈ : ∀ {A B : Set} {rs′ : List (Pos × Ev (IE B))} {rs : List (Pos × Ev (IE A))} → Rows≈ rs′ rs → RowsAt _≡_ rs′ rs
at≈ []       = []ᵃ
at≈ (s ∷ eq) = (refl , s) ∷ᵃ at≈ eq

foldAt : ∀ {A B : Set} {R} r {rs′ : List (Pos × Ev (IE B))} {rs : List (Pos × Ev (IE A))} → RowsAt R rs′ rs
       → L.foldl count r (values rs′) ≡ L.foldl count r (values rs)
foldAt r []ᵃ                     = refl
foldAt r ((_ , ev-out s) ∷ᵃ eq) rewrite count-same r s = foldAt _ eq
foldAt r ((_ , ev-end) ∷ᵃ eq)   = foldAt r eq

cntAt : ∀ {A B : Set} {R} {rs′ : List (Pos × Ev (IE B))} {rs : List (Pos × Ev (IE A))} → RowsAt R rs′ rs → cnt rs′ ≡ cnt rs
cntAt = foldAt r₀

splitAt : ∀ {A B : Set} {R} {rs′ : List (Pos × Ev (IE B))} {rs : List (Pos × Ev (IE A))} → RowsAt R rs′ rs
        → ∀ r₁′ r₂′ → rs′ ≡ r₁′ ++ r₂′
        → Σ _ λ r₁ → Σ _ λ r₂ → rs ≡ r₁ ++ r₂ × RowsAt R r₁′ r₁ × RowsAt R r₂′ r₂
splitAt eq         []        r₂′ refl = [] , _ , refl , []ᵃ , eq
splitAt (s ∷ᵃ eq)  (_ ∷ r₁′) r₂′ refl with splitAt eq r₁′ r₂′ refl
... | r₁ , r₂ , refl , e₁ , e₂ = _ ∷ r₁ , r₂ , refl , s ∷ᵃ e₁ , e₂

headAt : ∀ {A B : Set} {R} {y′ e′ r₂′} {r₂ : List (Pos × Ev (IE A))} → RowsAt {B = B} R ((y′ , e′) ∷ r₂′) r₂
       → Σ Pos λ y → Σ _ λ e → Σ _ λ r₂₀ → r₂ ≡ (y , e) ∷ r₂₀ × R y′ y × EvSame e′ e
headAt ((r , s) ∷ᵃ eq) = _ , _ , _ , refl , r , s

memAt : ∀ {A B : Set} {R} {rs′ : List (Pos × Ev (IE B))} {rs : List (Pos × Ev (IE A))} → RowsAt R rs′ rs
      → ∀ {q′ x′} → (q′ , out x′) ∈ rs′ → Σ Pos λ q → Σ (IE A) λ x → (q , out x) ∈ rs × R q′ q × Same x′ x
memAt ((r , ev-out s) ∷ᵃ _) (here refl) = _ , _ , here refl , r , s
memAt (_ ∷ᵃ eq)             (there m)   with memAt eq m
... | q , x , m′ , r , s = q , x , there m′ , r , s

-- An end met of the source is met of the stream.
endAt : ∀ {A B : Set} {R} {rs′ : List (Pos × Ev (IE B))} {rs : List (Pos × Ev (IE A))} → RowsAt R rs′ rs
      → ∀ {c} → (c , end) ∈ rs → Σ Pos λ c′ → (c′ , end) ∈ rs′ × R c′ c
endAt ((r , ev-end) ∷ᵃ _) (here refl) = _ , here refl , r
endAt (_ ∷ᵃ eq)           (there m)   with endAt eq m
... | c′ , m′ , r = c′ , there m′ , r

------------------------------------------------------------------------
-- Held carries over

-- A STREAM WHOSE ROWS ARE ITS SOURCE'S, MOVED, holds what its source
-- holds: each row lies where `R` relates it to one of its source's, in
-- the same instant, exempt, early and late wherever that one is.
held-move : ∀ {A B : Set} {t : EmissionSet (IE A)} {t′ : EmissionSet (IE B)} {cs cs′} (R : Pos → Pos → Set)
          → (∀ {y′ y} → R y′ y → rootOf y′ ≡ rootOf y)
          → (∀ {y′ y} → R y′ y → Ex cs y → Ex cs′ y′)
          → (∀ {y′ y} → R y′ y → Early y → Early y′)
          → (∀ {y′ y} → R y′ y → opos (rootOf y) ⊑ y → opos (rootOf y′) ⊑ y′)
          → (∀ {y′ x′} → t′ y′ (out x′) → Σ Pos λ y → Σ (IE A) λ x → R y′ y × t y (out x) × Same x′ x)
          → (∀ {y′} → t′ y′ end → Σ Pos λ y → R y′ y × t y end)
          → (∀ {rs′} → Met t′ rs′ → Σ _ λ rs → Met t rs × RowsAt R rs′ rs)
          → (Idle t → Idle t′) → (Rest t → Rest t′)
          → Held t cs → Held t′ cs′
held-move {A} {t = t} {t′} {cs} {cs′} R rt exR eaR laR row end-row back idle rest H = record
  { named = named ; covered = covered ; exact = exact ; routing = routing ; shut = shut
  ; early = early ; ends = ends ; done = done ; late = late ; idle = idle (Held.idle H) ; rest = rest (Held.rest H) }
  where
    nm-R : ∀ {y′ y} → R y′ y → nameOf y′ ≡ nameOf y
    nm-R r = cong nm (rt r)

    early : ∀ {y a n} → t′ y (out (instEmit (value a) n)) → Early y
    early x with row x
    ... | _ , _ , r , y , same-value = eaR r (Held.early H y)

    ends : ∀ {y} → t′ y end → Early y
    ends x with end-row x
    ... | _ , r , y = eaR r (Held.ends H y)

    done : ∀ {y n} → t′ y (out (instEmit (mark completed) n)) → Early y
    done x with row x
    ... | _ , _ , r , y , same-mark _ = eaR r (Held.done H y)

    late : ∀ {y n} → t′ y (out (instEmit (mark over) n)) → Valued (rootOf y) × opos (rootOf y) ⊑ y
    late x with row x
    ... | _ , _ , r , y , same-mark _ = subst Valued (sym (rt r)) (proj₁ (Held.late H y)) , laR r (proj₂ (Held.late H y))

    named : ∀ {y n} → t′ y (out (instEmit (mark begin) n)) → n ≡ nameOf y
    named x with row x
    ... | _ , _ , r , y , same-mark e = trans (e refl) (trans (Held.named H y) (sym (nm-R r)))

    routing : ∀ {y m n} → t′ y (out (instEmit (mark m) n)) → Routing m
    routing x with row x
    ... | _ , _ , _ , y , same-mark _ = Held.routing H y

    covered : ∀ {rs′} → Met t′ rs′ → ∀ r₁′ {y e′} r₂′ → rs′ ≡ r₁′ ++ (y , e′) ∷ r₂′ → Carried e′ → ¬ Ex cs′ y
            → Σ ℕ λ k → cnt r₁′ ≡ (nameOf y , suc k)
    covered m r₁′ r₂′ e c nx with back m
    ... | rs , run , eq with splitAt eq r₁′ _ e
    ...   | r₁ , r₂ , refl , e₁ , e₂ with headAt e₂
    ...     | _ , _ , r₂₀ , refl , r , s =
      subst₂ (λ a b → Σ ℕ λ k → a ≡ (b , suc k)) (sym (cntAt e₁)) (sym (nm-R r))
        (Held.covered H run r₁ r₂₀ refl (carried-same s c) λ ex → nx (exR r ex))

    exact : ∀ {rs′} → Met t′ rs′ → ∀ r₁′ {y n} r₂′ → rs′ ≡ r₁′ ++ (y , out (instEmit (mark stop) n)) ∷ r₂′
          → Σ ℕ λ k → proj₂ (cnt r₁′) ≡ suc k
    exact m r₁′ r₂′ e with back m
    ... | rs , run , eq with splitAt eq r₁′ _ e
    ...   | r₁ , r₂ , refl , e₁ , e₂ with headAt e₂
    ...     | _ , _ , r₂₀ , refl , _ , ev-out (same-mark _) =
      subst (λ r → Σ _ λ k → proj₂ r ≡ _) (sym (cntAt e₁)) (Held.exact H run r₁ r₂₀ refl)

    shut : Shut t′
    shut m r₁′ r₂′ e z bq vy iq with back m
    ... | rs , run , eq with splitAt eq r₁′ r₂′ e
    ...   | r₁ , r₂ , refl , e₁ , e₂ with memAt e₁ bq | memAt e₂ vy
    ...     | _ , _ , bq′ , rq , same-mark e | _ , _ , vy′ , ry , same-value =
      Held.shut H run r₁ r₂ refl (subst (λ r → proj₂ r ≡ 0) (cntAt e₁) z)
        (subst (λ n → (_ , out (instEmit (mark begin) n)) ∈ r₁) (trans (sym (e refl)) (cong proj₁ (cntAt e₁))) bq′) vy′
        (trans (sym (rt ry)) (trans iq (rt rq)))

-- A relabelling that every row of its source a reader could wait on
-- shows waits where its source does.
idle-same : ∀ {A B : Set} {t : EmissionSet (IE A)} {t′ : EmissionSet (IE B)}
          → (∀ {rs′} → Met t′ rs′ → Σ _ λ rs → Met t rs × Rows≈ rs′ rs)
          → (∀ {w} → Few t′ w → ∀ {k e} → t k e → k ≺ w → ¬ ¬ Σ _ λ e′ → t′ k e′ × (Visible e → Visible e′))
          → Idle t → Idle t′
idle-same {t = t} back fwd I m ne {w} F aw later with back m
... | rs , run , eq =
  subst (λ r → proj₂ r ≡ 0 ⊎ proj₁ r ≡ nameOf w) (sym (cnt-same eq))
    (I run (λ ce → ne (end≈ eq ce)) few (subst (λ c → After c w) (cursor≈ eq _) aw)
      λ ty vy ay yw → fwd F ty yw λ (_ , t′y , vv) → later t′y (vv vy) (subst (λ c → After c _) (sym (cursor≈ eq _)) ay) yw)
  where
    few : Few t w
    few = proj₁ F , λ {k} tk kw → decidable-stable (any? (k ≟ᵖ_) (proj₁ F)) λ nm′ → fwd F tk kw λ (_ , t′k , _) → nm′ (proj₂ F t′k kw)

held-same : ∀ {A B : Set} {t : EmissionSet (IE A)} {t′ : EmissionSet (IE B)} {cs}
          → (∀ {y x′} → t′ y (out x′) → Σ (IE A) λ x → t y (out x) × Same x′ x)
          → (∀ {y} → t′ y end → t y end)
          → (∀ {rs′} → Met t′ rs′ → Σ _ λ rs → Met t rs × Rows≈ rs′ rs)
          → (∀ {w} → Few t′ w → ∀ {k e} → t k e → k ≺ w → ¬ ¬ Σ _ λ e′ → t′ k e′ × (Visible e → Visible e′))
          → (Rest t → Rest t′)
          → Held t cs → Held t′ cs
held-same row end-row back fwd rest =
  held-move _≡_ (λ { refl → refl }) (λ { refl x → x }) (λ { refl x → x }) (λ { refl x → x })
    (λ x → let (x₀ , y , s) = row x in _ , x₀ , refl , y , s) (λ x → _ , refl , end-row x)
    (λ m → let (rs , run , eq) = back m in rs , run , at≈ eq) (idle-same back fwd) rest
