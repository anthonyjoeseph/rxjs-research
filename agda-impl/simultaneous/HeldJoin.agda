{-# OPTIONS --guardedness #-}

-- A READER THAT JOINS LATE COUNTS WHAT ITS SOURCE COUNTS.  A reader
-- subscribed to a hot partway through meets the source's rows from some
-- row on, and before that row a `begin` for each route the source held
-- there (`joins`).  So a run it meets is a run of the source with the
-- prefix it missed traded for those begins (`Joined`), and from the row
-- it first meets the two counts agree, or both hold nothing and the
-- reader has begun nothing (`Sim`).  A route held under a row is held
-- under it in both, a stop finds a route in both, and a dead instant is
-- dead in both.
module simultaneous.HeldJoin where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; replicate)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Properties using (foldl-++; ++-assoc; ++-identityʳ; ∷-injective)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; yes; no)

open import denotation.Position using (Pos; root; frame; cascade; ix; sub; last; _∙_; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; skip; pin)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; stop; over; outerOpen; outerClose; laneStart; laneDone;
  burstEnd; outerDone; subscribed; completed)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Relations using (Met; values; values-++)
open import simultaneous.Shut using (Shut; r₀)
open import simultaneous.Routed using (Held; Carried; c-value; c-stop; c-over; c-done; c-end; cnt; Ex; nameOf; nm)
open import simultaneous.Readings using (rootOf; instantOf)
open import simultaneous.Relabel using (Same; same-mark; same-value; EvSame; ev-out; ev-end; RowsAt; []ᵃ; _∷ᵃ_; count-same;
  splitAt; headAt; memAt; carried-same)
open import simultaneous.HeldIn using (++-split)
open import simultaneous.Layers using (run-row)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Routes; count; joins)

------------------------------------------------------------------------
-- Begins

data IsBegin {A : Set} : IE A → Set where
  is-begin : ∀ {n} → IsBegin (instEmit (mark begin) n)

begin? : ∀ {A} (x : IE A) → IsBegin x ⊎ ¬ IsBegin x
begin? (instEmit (value _) _)        = inj₂ λ ()
begin? (instEmit (mark begin) _)      = inj₁ is-begin
begin? (instEmit (mark stop) _)       = inj₂ λ ()
begin? (instEmit (mark over) _)       = inj₂ λ ()
begin? (instEmit (mark outerOpen) _)  = inj₂ λ ()
begin? (instEmit (mark outerClose) _) = inj₂ λ ()
begin? (instEmit (mark laneStart) _)  = inj₂ λ ()
begin? (instEmit (mark (laneDone _)) _)   = inj₂ λ ()
begin? (instEmit (mark burstEnd) _)   = inj₂ λ ()
begin? (instEmit (mark outerDone) _)  = inj₂ λ ()
begin? (instEmit (mark subscribed) _) = inj₂ λ ()
begin? (instEmit (mark completed) _)  = inj₂ λ ()

-- A begin of the routes' name, for each route held.
held-begins : ∀ {A} → Routes → List (IE A)
held-begins r = replicate (proj₂ r) (instEmit (mark begin) (proj₁ r))

-- The begins a reader sends before the first row it meets.
jl : ∀ {A} → Routes → Ev (IE A) → List (IE A)
jl r (out x) = joins r x
jl r _       = held-begins r

joins-nb : ∀ {A} r (x : IE A) → ¬ IsBegin x → joins r x ≡ held-begins r
joins-nb (m , k) (instEmit (value _) _)        _  = refl
joins-nb (m , k) (instEmit (mark begin) _)      nb = ⊥-elim (nb is-begin)
joins-nb (m , k) (instEmit (mark stop) _)       _  = refl
joins-nb (m , k) (instEmit (mark over) _)       _  = refl
joins-nb (m , k) (instEmit (mark outerOpen) _)  _  = refl
joins-nb (m , k) (instEmit (mark outerClose) _) _  = refl
joins-nb (m , k) (instEmit (mark laneStart) _)  _  = refl
joins-nb (m , k) (instEmit (mark (laneDone _)) _)   _  = refl
joins-nb (m , k) (instEmit (mark burstEnd) _)   _  = refl
joins-nb (m , k) (instEmit (mark outerDone) _)  _  = refl
joins-nb (m , k) (instEmit (mark subscribed) _) _  = refl
joins-nb (m , k) (instEmit (mark completed) _)  _  = refl

-- The first row met is not a begin: the joins are the routes held.
NoBegin : ∀ {A} → Ev (IE A) → Set
NoBegin e = ∀ {x} → e ≡ out x → ¬ IsBegin x

jl-nb : ∀ {A} r (e : Ev (IE A)) → NoBegin e → jl r e ≡ held-begins r
jl-nb r (out x) nb = joins-nb r x (nb refl)
jl-nb r skip    _  = refl
jl-nb r (pin _) _  = refl
jl-nb r end     _  = refl

-- The joins are the routes held, or none.
jl-rep : ∀ {A} r (e : Ev (IE A)) → jl r e ≡ [] ⊎ jl r e ≡ held-begins r
jl-rep (m , k) (out x) with begin? x
jl-rep (m , k) (out (instEmit (mark begin) n)) | inj₁ is-begin with n ≟ᵖ m
... | yes _ = inj₂ refl
... | no _  = inj₁ refl
jl-rep r (out x) | inj₂ nb = inj₂ (joins-nb r x nb)
jl-rep r skip    = inj₂ refl
jl-rep r (pin _) = inj₂ refl
jl-rep r end     = inj₂ refl

rep-in : ∀ {A} {x : IE A} {y} k → y ∈ replicate k x → y ≡ x × Σ ℕ λ j → k ≡ suc j
rep-in (suc k) (here refl) = refl , k , refl
rep-in (suc k) (there y)   = proj₁ (rep-in k y) , k , refl

-- A join is a begin of the routes' name, and some route is held.
jl-in : ∀ {A} r (e : Ev (IE A)) {x} → x ∈ jl r e → x ≡ instEmit (mark begin) (proj₁ r) × Σ ℕ λ j → proj₂ r ≡ suc j
jl-in r e {x} i with jl-rep r e
... | inj₁ eq = case-nil (subst (x ∈_) eq i)
  where case-nil : x ∈ [] → _
        case-nil ()
... | inj₂ eq = rep-in (proj₂ r) (subst (x ∈_) eq i)

------------------------------------------------------------------------
-- The count over begins

begin-zero : ∀ {A} m n → count (m , 0) (instEmit {A = A} (mark begin) n) ≡ (n , 1)
begin-zero m n with n ≟ᵖ m
... | yes refl = refl
... | no _     = refl

begin-same : ∀ {A} m k → count (m , k) (instEmit {A = A} (mark begin) m) ≡ (m , suc k)
begin-same m k with m ≟ᵖ m
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

begin-suc : ∀ {A} c n → Σ ℕ λ k → proj₂ (count c (instEmit {A = A} (mark begin) n)) ≡ suc k
begin-suc (m , k) n with n ≟ᵖ m
... | yes _ = k , refl
... | no _  = 0 , refl

begin-name : ∀ {A} c n → proj₁ (count c (instEmit {A = A} (mark begin) n)) ≡ n
begin-name (m , k) n with n ≟ᵖ m
... | yes refl = refl
... | no _     = refl

-- Past a mark no reader routes by, a count holding nothing still does,
nb-zero : ∀ {A} (x : IE A) c → proj₂ c ≡ 0 → ¬ IsBegin x → proj₂ (count c x) ≡ 0
nb-zero (instEmit (value _) _)        (m , .0) refl _  = refl
nb-zero (instEmit (mark begin) _)      _        _    nb = ⊥-elim (nb is-begin)
nb-zero (instEmit (mark stop) _)       (m , .0) refl _  = refl
nb-zero (instEmit (mark over) _)       (m , .0) refl _  = refl
nb-zero (instEmit (mark outerOpen) _)  (m , .0) refl _  = refl
nb-zero (instEmit (mark outerClose) _) (m , .0) refl _  = refl
nb-zero (instEmit (mark laneStart) _)  (m , .0) refl _  = refl
nb-zero (instEmit (mark (laneDone _)) _)   (m , .0) refl _  = refl
nb-zero (instEmit (mark burstEnd) _)   (m , .0) refl _  = refl
nb-zero (instEmit (mark outerDone) _)  (m , .0) refl _  = refl
nb-zero (instEmit (mark subscribed) _) (m , .0) refl _  = refl
nb-zero (instEmit (mark completed) _)  (m , .0) refl _  = refl

-- keeps its name, and holds a route only where it held one before.
nb-back : ∀ {A} (x : IE A) c {j} → ¬ IsBegin x → proj₂ (count c x) ≡ suc j
        → proj₁ (count c x) ≡ proj₁ c × Σ ℕ λ i → proj₂ c ≡ suc i
nb-back (instEmit (value _) _)        (m , k)           nb e = refl , _ , e
nb-back (instEmit (mark begin) _)      _                 nb e = ⊥-elim (nb is-begin)
nb-back (instEmit (mark stop) _)       (m , suc (suc k)) nb e = refl , suc k , refl
nb-back (instEmit (mark stop) _)       (m , suc zero)    nb ()
nb-back (instEmit (mark stop) _)       (m , zero)        nb ()
nb-back (instEmit (mark over) _)       (m , k)           nb ()
nb-back (instEmit (mark outerOpen) _)  (m , k)           nb e = refl , _ , e
nb-back (instEmit (mark outerClose) _) (m , k)           nb e = refl , _ , e
nb-back (instEmit (mark laneStart) _)  (m , k)           nb e = refl , _ , e
nb-back (instEmit (mark (laneDone _)) _)   (m , k)           nb e = refl , _ , e
nb-back (instEmit (mark burstEnd) _)   (m , k)           nb e = refl , _ , e
nb-back (instEmit (mark outerDone) _)  (m , k)           nb e = refl , _ , e
nb-back (instEmit (mark subscribed) _) (m , k)           nb e = refl , _ , e
nb-back (instEmit (mark completed) _)  (m , k)           nb e = refl , _ , e

-- Begins of one name, counted on from that name.
rep-from : ∀ {A} m j k → L.foldl count (m , j) (replicate {A = IE A} k (instEmit (mark begin) m)) ≡ (m , j + k)
rep-from m j zero    = cong (m ,_) (sym (+-identityʳ j))
rep-from {A} m j (suc k) =
  trans (cong (λ c → L.foldl count c (replicate k _)) (begin-same {A} m j))
        (trans (rep-from m (suc j) k) (cong (m ,_) (sym (+-suc j k))))

-- WHERE A ROUTE IS HELD, SOME BEGIN OF ITS NAME WAS MET: the count's name
-- is the last begin's, or the start's with a route held from the start.
cnt-begin : ∀ {A} c (rs : List (Pos × Ev (IE A))) {k} → proj₂ (L.foldl count c (values rs)) ≡ suc k
          → (Σ Pos λ q → (q , out (instEmit (mark begin) (proj₁ (L.foldl count c (values rs))))) ∈ rs)
          ⊎ (proj₁ (L.foldl count c (values rs)) ≡ proj₁ c × Σ ℕ λ i → proj₂ c ≡ suc i)
cnt-begin c []                    e = inj₂ (refl , _ , e)
cnt-begin c ((q , skip) ∷ rs)     e with cnt-begin c rs e
... | inj₁ (q′ , i) = inj₁ (q′ , there i)
... | inj₂ h        = inj₂ h
cnt-begin c ((q , pin _) ∷ rs)    e with cnt-begin c rs e
... | inj₁ (q′ , i) = inj₁ (q′ , there i)
... | inj₂ h        = inj₂ h
cnt-begin c ((q , end) ∷ rs)      e with cnt-begin c rs e
... | inj₁ (q′ , i) = inj₁ (q′ , there i)
... | inj₂ h        = inj₂ h
cnt-begin {A} c ((q , out x) ∷ rs)    e with cnt-begin (count c x) rs e
... | inj₁ (q′ , i) = inj₁ (q′ , there i)
... | inj₂ (n≡ , i , e′) with begin? x
...   | inj₁ (is-begin {n}) =
  inj₁ (q , subst (λ n′ → (q , out (instEmit (mark begin) n′)) ∈ ((q , out x) ∷ rs)) (sym (trans n≡ (begin-name {A} c n))) (here refl))
...   | inj₂ nb = let (n₁ , j) = nb-back x c nb e′ in inj₂ (trans n≡ n₁ , j)

-- A run of begins holds a route.
Begins : ∀ {A} → List (Pos × Ev (IE A)) → Set
Begins rs = ∀ {y e} → (y , e) ∈ rs → Σ Pos λ n → e ≡ out (instEmit (mark begin) n)

begins-pos : ∀ {A} c y (e : Ev (IE A)) rs → Begins ((y , e) ∷ rs) → Σ ℕ λ k → proj₂ (L.foldl count c (values ((y , e) ∷ rs))) ≡ suc k
begins-pos {A} c y e rs bs with bs (here refl)
... | n , refl with rs
...   | []             = begin-suc {A} c n
...   | (y′ , e′) ∷ rs′ = begins-pos {A} (count c (instEmit {A = A} (mark begin) n)) y′ e′ rs′ (λ i → bs (there i))

begins-held : ∀ {A} {rs : List (Pos × Ev (IE A))} {q e} → Begins rs → (q , e) ∈ rs → Σ ℕ λ k → proj₂ (cnt rs) ≡ suc k
begins-held {rs = (y , e) ∷ rs} bs _ = begins-pos r₀ y e rs bs

------------------------------------------------------------------------
-- Counting alike

-- Two counts agree, or both hold nothing and no begin has been met.
Sim : ∀ {A} → Routes → Routes → List (IE A) → Set
Sim c′ c vs = c′ ≡ c ⊎ (proj₂ c′ ≡ 0 × proj₂ c ≡ 0 × All (λ x → ¬ IsBegin x) vs)

zero-begin : ∀ {A} c n → proj₂ c ≡ 0 → count c (instEmit {A = A} (mark begin) n) ≡ (n , 1)
zero-begin {A} (m , .0) n refl = begin-zero {A} m n

sim-step : ∀ {A} {c′ c} {vs : List (IE A)} (x′ x : IE A) → Same x′ x → Sim c′ c vs → Sim (count c′ x′) (count c x) (vs ++ [ x′ ])
sim-step {c′ = c′} x′ x s (inj₁ refl) = inj₁ (count-same c′ s)
sim-step {A} {c′ = c′} {c} x′ x s (inj₂ (z′ , z , nb)) with begin? x′
... | inj₁ (is-begin {n}) = inj₁ (trans (zero-begin {A} c′ n z′) (trans (sym (zero-begin {A} c n z)) (count-same c s)))
... | inj₂ nb′ = inj₂ (nb-zero x′ c′ z′ nb′ , subst (λ d → proj₂ d ≡ 0) (count-same c s) (nb-zero x′ c z nb′) , ++⁺ nb (nb′ All.∷ All.[]))

-- Counting on over rows a run's rows relate to.
sim-at : ∀ {A} {R : Pos → Pos → Set} {c′ c} {vs : List (IE A)} {rs′ rs : List (Pos × Ev (IE A))} → RowsAt R rs′ rs → Sim c′ c vs
       → Sim (L.foldl count c′ (values rs′)) (L.foldl count c (values rs)) (vs ++ values rs′)
sim-at {A} {vs = vs} []ᵃ s = subst (Sim {A} _ _) (sym (++-identityʳ vs)) s
sim-at {A} {vs = vs} {rs′ = _ ∷ rsᵗ′} ((_ , ev-out {x′} {x} sm) ∷ᵃ ra) s = subst (Sim {A} _ _) (++-assoc vs [ x′ ] (values rsᵗ′)) (sim-at ra (sim-step x′ x sm s))
sim-at ((_ , ev-end) ∷ᵃ ra) s = sim-at ra s

-- The routes held, joined from nothing.
rep-sim : ∀ {A} r → Sim (L.foldl count r₀ (held-begins {A} r)) r (held-begins {A} r)
rep-sim {A} (m , zero)  = inj₂ (refl , refl , All.[])
rep-sim {A} (m , suc k) = inj₁ (trans (cong (λ c → L.foldl count c (replicate k _)) (begin-zero {A} root m)) (rep-from {A} m 1 k))

-- The joins and the first row met, against the routes held and that row.
sim-head : ∀ {A} r (x′ x : IE A) → Same x′ x → Sim (L.foldl count r₀ (joins r x ++ [ x′ ])) (count r x) (joins r x ++ [ x′ ])
sim-head r x′ x s with begin? x
sim-head {A} (m , k) x′ (instEmit (mark begin) n) s | inj₁ is-begin with n ≟ᵖ m
... | yes refl =
  subst (λ d → Sim d (n , suc k) (held-begins {A} (n , k) ++ [ x′ ])) (sym (foldl-++ count r₀ (held-begins (n , k)) [ x′ ]))
    (subst (λ d → Sim (count (L.foldl count r₀ (held-begins {A} (n , k))) x′) d (held-begins (n , k) ++ [ x′ ])) (begin-same {A} n k)
      (sim-step x′ (instEmit (mark begin) n) s (rep-sim {A} (n , k))))
sim-head {A} (m , k) (instEmit (mark begin) n′) (instEmit (mark begin) n) (same-mark e) | inj₁ is-begin | no ne with e refl
... | refl = inj₁ (begin-zero {A} root n′)
sim-head {A} r x′ x s | inj₂ nb rewrite joins-nb r x nb =
  subst (λ d → Sim d (count r x) (held-begins {A} r ++ [ x′ ])) (sym (foldl-++ count r₀ (held-begins r) [ x′ ])) (sim-step x′ x s (rep-sim {A} r))

------------------------------------------------------------------------
-- Runs

cnt-++ : ∀ {A} (xs ys : List (Pos × Ev (IE A))) → cnt (xs ++ ys) ≡ L.foldl count (cnt xs) (values ys)
cnt-++ xs ys = trans (cong (L.foldl count r₀) (values-++ xs ys)) (foldl-++ count r₀ (values xs) (values ys))

values-of : ∀ {A} {js : List (Pos × Ev (IE A))} {xs} → L.map proj₂ js ≡ L.map out xs → values js ≡ xs
values-of {js = []}               {[]}     refl = refl
values-of {js = (_ , out _) ∷ js} {_ ∷ xs} eq   with ∷-injective eq
... | refl , eq′ = cong (_ ∷_) (values-of eq′)

mem-of : ∀ {A} {js : List (Pos × Ev (IE A))} {xs} → L.map proj₂ js ≡ L.map out xs → ∀ {y e} → (y , e) ∈ js → Σ (IE A) λ x → e ≡ out x × x ∈ xs
mem-of {js = (_ , out _) ∷ js} {_ ∷ xs} eq (here refl) with ∷-injective eq
... | refl , _ = _ , refl , here refl
mem-of {js = (_ , _) ∷ js}     {_ ∷ xs} eq (there i)   with mem-of (proj₂ (∷-injective eq)) i
... | x , e , xi = x , e , there xi

out-in : ∀ {A} {rs : List (Pos × Ev (IE A))} {q x} → (q , out x) ∈ rs → x ∈ values rs
out-in {rs = (_ , out _) ∷ _} (here refl) = here refl
out-in {rs = (_ , out _) ∷ _} (there i)   = there (out-in i)
out-in {rs = (_ , skip) ∷ _}  (there i)   = out-in i
out-in {rs = (_ , pin _) ∷ _} (there i)   = out-in i
out-in {rs = (_ , end) ∷ _}   (there i)   = out-in i

-- A RUN A LATE READER MEETS: rows past its subscription that are none of
-- the source's, each an end it is exempt for; begins alone, the first
-- rows of joins; or the joins for the routes the source held before a
-- row, then the source's rows from that row on, each moved by `R`.
data Joined {A : Set} (t : EmissionSet (IE A)) (R : Pos → Pos → Set) (cs′ : List Pos) : List (Pos × Ev (IE A)) → Set where
  j-late : ∀ {rs′} → (∀ {y e} → (y , e) ∈ rs′ → e ≡ end × Ex cs′ y) → Joined t R cs′ rs′
  j-part : ∀ {rs′} → Begins rs′ → Joined t R cs′ rs′
  j-read : ∀ {pre y e rs js rs₁′} → Met t (pre ++ (y , e) ∷ rs) → L.map proj₂ js ≡ L.map out (jl (cnt pre) e)
         → RowsAt R rs₁′ ((y , e) ∷ rs) → Joined t R cs′ (js ++ rs₁′)

-- The rows past the joins.
split-begins : ∀ {A} (js rs₁′ r₁′ : List (Pos × Ev (IE A))) {y e′} r₂′ → Begins js → (∀ {n} → e′ ≡ out (instEmit (mark begin) n) → ⊥)
             → js ++ rs₁′ ≡ r₁′ ++ (y , e′) ∷ r₂′ → Σ _ λ r₁″ → r₁′ ≡ js ++ r₁″ × rs₁′ ≡ r₁″ ++ (y , e′) ∷ r₂′
split-begins []       rs₁′ r₁′       r₂′ _  _  eq = r₁′ , refl , eq
split-begins (j ∷ js) rs₁′ []        r₂′ bs nb eq with ∷-injective eq
... | refl , _ = ⊥-elim (nb (proj₂ (bs (here refl))))
split-begins (j ∷ js) rs₁′ (x ∷ r₁′) r₂′ bs nb eq with ∷-injective eq
... | refl , eq′ with split-begins js rs₁′ r₁′ r₂′ (λ i → bs (there i)) nb eq′
...   | r₁″ , refl , e₂ = r₁″ , refl , e₂


zero-suc : ∀ {j} → 0 ≡ suc j → ⊥
zero-suc ()

-- Past the joins, the counts agree, or hold nothing with nothing begun:
-- with no row of the source met yet,
sim-nil : ∀ {A} r {e₀ : Ev (IE A)} (js : List (Pos × Ev (IE A))) → L.map proj₂ js ≡ L.map out (jl r e₀) → NoBegin e₀
        → Sim (cnt js) r (values js)
sim-nil r {e₀} js jeq nb =
  subst (λ l → Sim (L.foldl count r₀ l) r l) (sym (trans (values-of jeq) (jl-nb r e₀ nb))) (rep-sim r)

-- or with some.
sim-cons : ∀ {A} {R : Pos → Pos → Set} r {y₀ e₀ r₁ᵗ y′ e′ r₁ᵗ′} (js : List (Pos × Ev (IE A))) → L.map proj₂ js ≡ L.map out (jl r e₀)
         → RowsAt R ((y′ , e′) ∷ r₁ᵗ′) ((y₀ , e₀) ∷ r₁ᵗ)
         → Sim (cnt (js ++ (y′ , e′) ∷ r₁ᵗ′)) (L.foldl count r (values ((y₀ , e₀) ∷ r₁ᵗ))) (values (js ++ (y′ , e′) ∷ r₁ᵗ′))
sim-cons r {r₁ᵗ = r₁ᵗ} {y′ = y′} {r₁ᵗ′ = r₁ᵗ′} js jeq ((_ , ev-out {x′} {x} sm) ∷ᵃ ra) =
  subst (λ l → Sim (L.foldl count r₀ l) _ l) (sym vq)
    (subst (λ l → Sim (L.foldl count r₀ l) _ l) (++-assoc (joins r x) [ x′ ] (values r₁ᵗ′))
      (subst (λ d → Sim d (L.foldl count (count r x) (values r₁ᵗ)) ((joins r x ++ [ x′ ]) ++ values r₁ᵗ′)) (sym (foldl-++ count r₀ (joins r x ++ [ x′ ]) (values r₁ᵗ′))) (sim-at ra (sim-head r x′ x sm))))
  where
    vq : values (js ++ (y′ , out x′) ∷ r₁ᵗ′) ≡ joins r x ++ x′ ∷ values r₁ᵗ′
    vq = trans (values-++ js ((y′ , out x′) ∷ r₁ᵗ′)) (cong (_++ (x′ ∷ values r₁ᵗ′)) (values-of jeq))
sim-cons r {r₁ᵗ = r₁ᵗ} {y′ = y′} {r₁ᵗ′ = r₁ᵗ′} js jeq ((_ , ev-end) ∷ᵃ ra) =
  subst (λ l → Sim (L.foldl count r₀ l) _ l) (sym vq)
    (subst (λ d → Sim d (L.foldl count r (values r₁ᵗ)) (held-begins r ++ values r₁ᵗ′)) (sym (foldl-++ count r₀ (held-begins r) (values r₁ᵗ′))) (sim-at ra (rep-sim r)))
  where
    vq : values (js ++ (y′ , end) ∷ r₁ᵗ′) ≡ held-begins r ++ values r₁ᵗ′
    vq = trans (values-++ js ((y′ , end) ∷ r₁ᵗ′)) (cong (_++ values r₁ᵗ′) (values-of jeq))

------------------------------------------------------------------------
-- Instants by name

-- An instant's name tells it apart.
inst-inj : ∀ i j → nm (i ∙ []) ≡ nm (j ∙ []) → i ≡ j
inst-inj frame                 frame                 _    = refl
inst-inj frame                 (cascade _ _ last)    ()
inst-inj frame                 (cascade _ _ (ix _))  ()
inst-inj frame                 (cascade _ _ (sub _)) ()
inst-inj (cascade _ _ last)    frame                 ()
inst-inj (cascade _ _ (ix _))  frame                 ()
inst-inj (cascade _ _ (sub _)) frame                 ()
inst-inj (cascade _ _ last)    (cascade _ _ last)    refl = refl
inst-inj (cascade _ _ last)    (cascade _ _ (ix _))  ()
inst-inj (cascade _ _ last)    (cascade _ _ (sub _)) ()
inst-inj (cascade _ _ (ix _))  (cascade _ _ last)    ()
inst-inj (cascade _ _ (ix _))  (cascade _ _ (ix _))  refl = refl
inst-inj (cascade _ _ (ix _))  (cascade _ _ (sub _)) ()
inst-inj (cascade _ _ (sub _)) (cascade _ _ last)    ()
inst-inj (cascade _ _ (sub _)) (cascade _ _ (ix _))  ()
inst-inj (cascade _ _ (sub _)) (cascade _ _ (sub _)) refl = refl

root-inj : ∀ {a b} → nameOf a ≡ nameOf b → rootOf a ≡ rootOf b
root-inj {a} {b} eq = cong (_∙ []) (inst-inj (instantOf a) (instantOf b) eq)

------------------------------------------------------------------------
-- What the reader holds

carried-nb : ∀ {A} {e : Ev (IE A)} → Carried e → ∀ {n} → e ≡ out (instEmit (mark begin) n) → ⊥
carried-nb c-value ()
carried-nb c-stop  ()
carried-nb c-over  ()
carried-nb c-done  ()
carried-nb c-end   ()

carried-nob : ∀ {A} {e : Ev (IE A)} → Carried e → NoBegin e
carried-nob c-value refl ()
carried-nob c-stop  refl ()
carried-nob c-over  refl ()
carried-nob c-done  refl ()

js-begins : ∀ {A} {r} {e : Ev (IE A)} {js : List (Pos × Ev (IE A))} → L.map proj₂ js ≡ L.map out (jl r e) → Begins js
js-begins {r = r} {e} jeq i with mem-of jeq i
... | x , refl , xi = _ , cong out (proj₁ (jl-in r e xi))

same-nob : ∀ {A} {e′ e : Ev (IE A)} → EvSame e′ e → NoBegin e′ → NoBegin e
same-nob (ev-out (same-mark _)) nb refl is-begin = nb refl is-begin
same-nob (ev-out same-value)    nb refl ()

head-eq : ∀ {A} {y₀ y′ : Pos} {e₀ e″ : Ev (IE A)} {rs rr r₂ : List (Pos × Ev (IE A))} → (y₀ , e₀) ∷ rs ≡ ((y′ , e″) ∷ rr) ++ r₂ → y′ ≡ y₀ × e″ ≡ e₀
head-eq refl = refl , refl

-- Past the joins, a run splits at a row of the source's, and the counts
-- before it agree.
module Past {A : Set} (R : Pos → Pos → Set) (t : EmissionSet (IE A)) {pre y₀ e₀ rs} {js : List (Pos × Ev (IE A))}
            (jeq : L.map proj₂ js ≡ L.map out (jl (cnt pre) e₀)) where

  sim-split : ∀ {r₁″ r₁ r₂} → (y₀ , e₀) ∷ rs ≡ r₁ ++ r₂ → RowsAt R r₁″ r₁ → (r₁ ≡ [] → NoBegin e₀)
            → Sim (cnt (js ++ r₁″)) (cnt (pre ++ r₁)) (values (js ++ r₁″))
  sim-split {[]} {[]} _ []ᵃ nil =
    subst (λ l → Sim (cnt l) _ (values l)) (sym (++-identityʳ js))
      (subst (λ d → Sim _ d _) (sym (trans (cnt-++ pre []) refl)) (sim-nil (cnt pre) js jeq (nil refl)))
  sim-split {(y′ , e′) ∷ r₁ᵗ′} {(y , e) ∷ r₁ᵗ} eq ra _ with head-eq {rr = r₁ᵗ} eq
  ... | refl , refl = subst (λ d → Sim _ d _) (sym (cnt-++ pre ((y₀ , e₀) ∷ r₁ᵗ))) (sim-cons (cnt pre) js jeq ra)

  -- The row a carried or stopping row of the reader is, past the joins.
  at-row : ∀ {r₁″ rs₁′ y e′ r₂′} → RowsAt R rs₁′ ((y₀ , e₀) ∷ rs) → rs₁′ ≡ r₁″ ++ (y , e′) ∷ r₂′ → NoBegin e′
         → Σ Pos λ y₁ → Σ _ λ e₁ → Σ _ λ r₁ → Σ _ λ r₂₀ → ((y₀ , e₀) ∷ rs ≡ r₁ ++ (y₁ , e₁) ∷ r₂₀)
           × R y y₁ × EvSame e′ e₁ × RowsAt R r₂′ r₂₀ × Sim (cnt (js ++ r₁″)) (cnt (pre ++ r₁)) (values (js ++ r₁″))
  at-row {r₁″} {y = y} {e′} {r₂′} ra e₂ nb′ with splitAt ra r₁″ ((y , e′) ∷ r₂′) e₂
  ... | r₁ , r₂ , eq , ra₁ , ra₂ with headAt ra₂
  ...   | y₁ , e₁ , r₂₀ , refl , r , s =
    y₁ , e₁ , r₁ , r₂₀ , eq , r , s , tl ra₂ , sim-split eq ra₁ (λ { refl → nob eq })
    where
      tl : ∀ {a b c d} → RowsAt R ((a , b) ∷ c) ((y₁ , e₁) ∷ d) → RowsAt R c d
      tl (_ ∷ᵃ x) = x
      nob : (y₀ , e₀) ∷ rs ≡ [] ++ (y₁ , e₁) ∷ r₂₀ → NoBegin e₀
      nob refl = same-nob s nb′

-- A count holding a route of a named instant is decided: not refuting it
-- proves it.
named-stable : ∀ {c : Pos × ℕ} {n} → ¬ ¬ (Σ ℕ λ k → c ≡ (n , suc k)) → Σ ℕ λ k → c ≡ (n , suc k)
named-stable {a , zero}  nn = ⊥-elim (nn λ { (_ , ()) })
named-stable {a , suc k} {n} nn with a ≟ᵖ n
... | yes refl = k , refl
... | no ne    = ⊥-elim (nn λ { (_ , refl) → ne refl })

suc-stable : ∀ {m : ℕ} → ¬ ¬ (Σ ℕ λ k → m ≡ suc k) → Σ ℕ λ k → m ≡ suc k
suc-stable {zero}  nn = ⊥-elim (nn λ { (_ , ()) })
suc-stable {suc k} _  = k , refl

module Join {A : Set} {t t′ : EmissionSet (IE A)} {cs cs′ : List Pos} (R : Pos → Pos → Set)
            (rt  : ∀ {y′ y} → R y′ y → rootOf y′ ≡ rootOf y)
            (exR : ∀ {y′ y} → R y′ y → Ex cs y → Ex cs′ y′)
            (named′ : ∀ {y n} → t′ y (out (instEmit (mark begin) n)) → n ≡ nameOf y)
            (back : ∀ {rs′} → Met t′ rs′ → ¬ ¬ Joined t R cs′ rs′)
            (H : Held t cs) where

  covered-j : ∀ {rs′} → Joined t R cs′ rs′ → ∀ r₁′ {y e′} r₂′ → rs′ ≡ r₁′ ++ (y , e′) ∷ r₂′ → Carried e′ → ¬ Ex cs′ y
            → Σ ℕ λ k → cnt r₁′ ≡ (nameOf y , suc k)
  covered-j j r₁′ {y} {e′} r₂′ eq c nx with j
  ... | j-late h = ⊥-elim (nx (proj₂ (h (subst ((y , e′) ∈_) (sym eq) (∈-++⁺ʳ r₁′ (here refl))))))
  ... | j-part h = ⊥-elim (carried-nb c (proj₂ (h (subst ((y , e′) ∈_) (sym eq) (∈-++⁺ʳ r₁′ (here refl))))))
  ... | j-read {pre} {e = e₀} {js = js} {rs₁′} run jeq ra with split-begins js rs₁′ r₁′ r₂′ (js-begins {r = cnt pre} {e₀} jeq) (carried-nb c) eq
  ...   | r₁″ , refl , e₂ with Past.at-row R t {pre} jeq ra e₂ (carried-nob c)
  ...     | y₁ , e₁ , r₁ , r₂₀ , eq₁ , r , s , _ , sim
    with Held.covered H run (pre ++ r₁) r₂₀ (trans (cong (pre ++_) eq₁) (sym (++-assoc pre r₁ _))) (carried-same s c) (λ ex → nx (exR r ex))
  ...       | k , ck with sim
  ...         | inj₁ ceq = k , trans ceq (trans ck (cong (λ n → n , suc k) (sym (cong nm (rt r)))))
  ...         | inj₂ (_ , z , _) = ⊥-elim (zero-suc (trans (sym z) (cong proj₂ ck)))

  -- A count read back is decided, so not refuting it is enough.
  covered′ : ∀ {rs′} → Met t′ rs′ → ∀ r₁′ {y e′} r₂′ → rs′ ≡ r₁′ ++ (y , e′) ∷ r₂′ → Carried e′ → ¬ Ex cs′ y
           → Σ ℕ λ k → cnt r₁′ ≡ (nameOf y , suc k)
  covered′ m r₁′ r₂′ eq c nx = named-stable λ h → back m λ j → h (covered-j j r₁′ r₂′ eq c nx)

  exact-j : ∀ {rs′} → Joined t R cs′ rs′ → ∀ r₁′ {y n} r₂′ → rs′ ≡ r₁′ ++ (y , out (instEmit (mark stop) n)) ∷ r₂′
          → Σ ℕ λ k → proj₂ (cnt r₁′) ≡ suc k
  exact-j j r₁′ {y} {n} r₂′ eq with j
  ... | j-late h = ⊥-elim (out-end (proj₁ (h (subst ((y , _) ∈_) (sym eq) (∈-++⁺ʳ r₁′ (here refl))))))
    where out-end : out (instEmit {A = A} (mark stop) n) ≡ end → ⊥
          out-end ()
  ... | j-part h = ⊥-elim (carried-nb c-stop (proj₂ (h (subst ((y , _) ∈_) (sym eq) (∈-++⁺ʳ r₁′ (here refl))))))
  ... | j-read {pre} {e = e₀} {js = js} {rs₁′} run jeq ra with split-begins js rs₁′ r₁′ r₂′ (js-begins {r = cnt pre} {e₀} jeq) (carried-nb c-stop) eq
  ...   | r₁″ , refl , e₂ with Past.at-row R t {pre} jeq ra e₂ (carried-nob c-stop)
  ...     | y₁ , _ , r₁ , r₂₀ , eq₁ , r , ev-out (same-mark _) , _ , sim
    with Held.exact H run (pre ++ r₁) r₂₀ (trans (cong (pre ++_) eq₁) (sym (++-assoc pre r₁ _)))
  ...       | k , ck with sim
  ...         | inj₁ ceq = k , trans (cong proj₂ ceq) ck
  ...         | inj₂ (_ , z , _) = ⊥-elim (zero-suc (trans (sym z) ck))

  -- A begin met past the joins is one of the source's of its instant.
  src-begin : ∀ {pre y₀ e₀ rs js rs′ r₁″ r₁ q} → Met t (pre ++ (y₀ , e₀) ∷ rs) → L.map proj₂ js ≡ L.map out (jl (cnt pre) e₀)
            → RowsAt R r₁″ r₁ → Met t′ rs′ → (∀ {z} → z ∈ js ++ r₁″ → z ∈ rs′)
            → (q , out (instEmit (mark begin) (proj₁ (cnt (js ++ r₁″))))) ∈ js ++ r₁″
            → proj₁ (cnt (js ++ r₁″)) ≡ proj₁ (cnt (pre ++ r₁))
            → Σ Pos λ q₀ → (q₀ , out (instEmit (mark begin) (proj₁ (cnt (pre ++ r₁))))) ∈ (pre ++ r₁) × rootOf q₀ ≡ rootOf q
  src-begin {pre} {e₀ = e₀} {js = js} {r₁″ = r₁″} {r₁} {q} run jeq ra₁ m incl bq neq with ∈-++⁻ js bq
  ... | inj₂ i with memAt ra₁ i
  ...   | q₀ , instEmit (mark begin) n₀ , i₀ , rq , same-mark e with e refl
  ...     | refl = q₀ , ∈-++⁺ʳ pre (subst (λ n → (q₀ , out (instEmit (mark begin) n)) ∈ r₁) neq i₀) , sym (rt rq)
  src-begin {pre} {e₀ = e₀} {js = js} {r₁″ = r₁″} {r₁} {q} run jeq ra₁ m incl bq neq | inj₁ i with mem-of jeq i
  ...   | x , refl , xi with jl-in (cnt pre) e₀ xi
  ...     | x≡ , k , ck with cnt-begin r₀ pre ck
  ...       | inj₂ (_ , _ , ())
  ...       | inj₁ (q₀ , i₀) =
    q₀ , ∈-++⁺ˡ (subst (λ n → (q₀ , out (instEmit (mark begin) n)) ∈ pre) (trans (sym N≡) neq) i₀) ,
    root-inj {q₀} {q} (trans (sym (Held.named H (proj₁ (run-row run (∈-++⁺ˡ i₀)))))
                    (trans (sym N≡) (named′ (proj₁ (run-row m (incl bq))))))
    where
      begin-inj : ∀ {n n′} → instEmit {A = A} (mark begin) n ≡ instEmit (mark begin) n′ → n ≡ n′
      begin-inj refl = refl
      N≡ : proj₁ (cnt (js ++ r₁″)) ≡ proj₁ (cnt pre)
      N≡ = begin-inj x≡

  -- A dead instant of the reader's, past the joins, is dead in the source.
  shut-read : ∀ {pre y₀ e₀ rs js rs₁′} → Met t′ (js ++ rs₁′) → Met t (pre ++ (y₀ , e₀) ∷ rs)
            → L.map proj₂ js ≡ L.map out (jl (cnt pre) e₀) → RowsAt R rs₁′ ((y₀ , e₀) ∷ rs)
            → ∀ r₁′ r₂′ → js ++ rs₁′ ≡ r₁′ ++ r₂′ → proj₂ (cnt r₁′) ≡ 0
            → ∀ {q} → (q , out (instEmit (mark begin) (proj₁ (cnt r₁′)))) ∈ r₁′
            → ∀ {y a j} → (y , out (instEmit (value a) j)) ∈ r₂′ → rootOf y ≡ rootOf q → ⊥
  shut-read {pre} {y₀} {e₀} {rs} {js} {rs₁′} m run jeq ra r₁′ r₂′ eq z bq vy iq with ++-split js rs₁′ r₁′ r₂′ eq
  ... | inj₂ (mm , js≡ , _) =
    zero-suc (trans (sym z) (proj₂ (begins-held (λ i → js-begins {r = cnt pre} {e₀} jeq (subst (_ ∈_) (sym js≡) (∈-++⁺ˡ i))) bq)))
  ... | inj₁ (r₁″ , refl , e₂) with splitAt ra r₁″ r₂′ e₂
  ...   | [] , r₂ , eq₂ , []ᵃ , ra₂ =
    zero-suc (trans (sym z) (proj₂ (begins-held {rs = js ++ []} (λ i → js-begins {r = cnt pre} {e₀} jeq (subst (_ ∈_) (++-identityʳ js) i)) bq)))
  ...   | (y₁ , e₁) ∷ r₁ᵗ , r₂ , eq₂ , ra₁ , ra₂ with Past.sim-split R t {pre} jeq eq₂ ra₁ (λ ())
  ...     | inj₂ (_ , _ , nb) = All.lookup nb (out-in bq) is-begin
  ...     | inj₁ ceq with memAt ra₂ vy
  ...       | y₂ , _ , vy₂ , ry , same-value
    with src-begin run jeq ra₁ m (λ i → subst (_ ∈_) (trans (++-assoc js r₁″ r₂′) (cong (js ++_) (sym e₂))) (∈-++⁺ˡ i)) bq (cong proj₁ ceq)
  ...         | q₀ , bq₀ , iq₀ =
    Held.shut H run (pre ++ (y₁ , e₁) ∷ r₁ᵗ) r₂ (trans (cong (pre ++_) eq₂) (sym (++-assoc pre ((y₁ , e₁) ∷ r₁ᵗ) r₂)))
      (trans (sym (cong proj₂ ceq)) z) bq₀ vy₂ (trans (sym (rt ry)) (trans iq (sym iq₀)))

  exact′ : ∀ {rs′} → Met t′ rs′ → ∀ r₁′ {y n} r₂′ → rs′ ≡ r₁′ ++ (y , out (instEmit (mark stop) n)) ∷ r₂′
         → Σ ℕ λ k → proj₂ (cnt r₁′) ≡ suc k
  exact′ m r₁′ r₂′ eq = suc-stable λ h → back m λ j → h (exact-j j r₁′ r₂′ eq)

  shut-j : ∀ {rs′} → Met t′ rs′ → Joined t R cs′ rs′ → ∀ r₁′ r₂′ → rs′ ≡ r₁′ ++ r₂′ → proj₂ (cnt r₁′) ≡ 0
         → ∀ {q} → (q , out (instEmit (mark begin) (proj₁ (cnt r₁′)))) ∈ r₁′
         → ∀ {y a j} → (y , out (instEmit (value a) j)) ∈ r₂′ → rootOf y ≡ rootOf q → ⊥
  shut-j m jd r₁′ r₂′ eq z {q} bq {y} {a} {j} vy iq with jd
  ... | j-late h = out-end (proj₁ (h (subst ((y , _) ∈_) (sym eq) (∈-++⁺ʳ r₁′ vy))))
    where out-end : out (instEmit {A = A} (value a) j) ≡ end → ⊥
          out-end ()
  ... | j-part h = val-begin (proj₂ (h (subst ((y , _) ∈_) (sym eq) (∈-++⁺ʳ r₁′ vy))))
    where val-begin : ∀ {n} → out (instEmit {A = A} (value a) j) ≡ out (instEmit (mark begin) n) → ⊥
          val-begin ()
  ... | j-read run jeq ra = shut-read m run jeq ra r₁′ r₂′ eq z bq vy iq

  shut′ : Shut t′
  shut′ m r₁′ r₂′ eq z bq vy iq = back m λ jd → shut-j m jd r₁′ r₂′ eq z bq vy iq
