{-# OPTIONS --guardedness #-}

-- THE COLD'S RUNS COUNT ITS ROUTES.  A step's begin is met before its
-- other rows, and every row met between them is of its instant and no
-- mark (`opened`), so each carried row of a step is met with its route
-- open (`cold-covered`).  A count shut on a begun instant stays shut: a
-- later value of that instant would find its route open again, and only
-- a second begin of it could have opened it (`cold-shut`).
module simultaneous.ColdRuns where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Properties using (foldl-++; ++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-∃++)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
import Data.Product as P
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (decidable-stable)

open import denotation.Position using (Pos; Instant; cascade; ix; last; _∙_; _⊕_; _≟ᵖ_; instant; root)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; DenEnv; enter; Ev; out; skip; pin; end; _≺_; _≼_)
open import denotation.Read using (Run; []; _∷_; Visible; After; cursor)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≺→≼; ≼-split)
open import denotation.Laws.Worlds using (⊑-inside)
open import denotation.Laws.Truth using (instant-⊑)
open import simultaneous.HeldComb using (ev; ShutRun)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.InstEmit using (instEmit; mark; value; begin; over; stop; outerOpen; outerClose; laneStart; laneDone;
  burstEnd; outerDone; subscribed; completed)
open import simultaneous.Routed using (nm; nameOf; cnt; Carried; Ex; c-value; nm-inst)
open import simultaneous.Relations using (Met; values; values-++)
open import simultaneous.Shut using (r₀)
open import simultaneous.Readings using (rootOf)
open import simultaneous.HeldConnect using (rootOf-ext)
open import simultaneous.Instants using (btw)
open import simultaneous.Layers using (run-tail; run-after; run-row)
open import simultaneous.ColdFew using (Fresh; fresh-self)
open import simultaneous.ColdShape using (ColdRow; now-value; now-end; step-begin; step-value; step-over; step-end; cold-rows)
open import simultaneous.ColdBegin using (same-≺; same-≺⁻; cold-vb; cold-ob; cold-eb)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Routes; count; coldˢ)

------------------------------------------------------------------------
-- Runs and counts

-- A visible row before one met is met, with some row.
run-has-ex : ∀ {A} {t : EmissionSet A} {c rs v e k ek} → Run t c rs → t v e → Visible e → After c v → v ≼ k → (k , ek) ∈ rs
           → Σ (Ev A) λ e′ → (v , e′) ∈ rs
run-has-ex {rs = (q , e₁) ∷ _} {v} ((_ , _ , _ , lst) ∷ run) x vi av vk m with ≼-split {q} {v} (lst x vi av)
... | inj₂ refl = e₁ , here refl
... | inj₁ qv with m
...   | here refl = ⊥-elim (vk qv)
...   | there m′  = P.map₂ there (run-has-ex run x vi qv vk m′)

-- A row met earlier lies earlier.
run-order : ∀ {A} {t : EmissionSet A} {c} xs {ys k e y e′} → Run t c (xs ++ ys) → (k , e) ∈ xs → (y , e′) ∈ ys → k ≺ y
run-order (_ ∷ xs) (_ ∷ run) (here refl) m = run-after run (∈-++⁺ʳ xs m)
run-order (_ ∷ xs) (_ ∷ run) (there i)   m = run-order xs run i m

after-in : ∀ {A} {t : EmissionSet A} {c} xs {y e ys k e′} → Run t c (xs ++ (y , e) ∷ ys) → (k , e′) ∈ ys → y ≺ k
after-in xs run m with run-tail xs run
... | _ ∷ run′ = run-after run′ m

values-∈ : ∀ {A} {x : A} rs → x ∈ values rs → Σ Pos λ q → (q , out x) ∈ rs
values-∈ ((q , out _) ∷ rs) (here refl) = q , here refl
values-∈ ((q , out _) ∷ rs) (there m)   = P.map₂ there (values-∈ rs m)
values-∈ ((q , skip) ∷ rs)  m           = P.map₂ there (values-∈ rs m)
values-∈ ((q , pin _) ∷ rs) m           = P.map₂ there (values-∈ rs m)
values-∈ ((q , end) ∷ rs)   m           = P.map₂ there (values-∈ rs m)

-- Rows with no mark leave the count as it was.
quiet-fold : ∀ {A} c (rs : List (Pos × Ev (IE A))) → (∀ {y m n} → (y , out (instEmit (mark m) n)) ∈ rs → ⊥)
           → L.foldl count c (values rs) ≡ c
quiet-fold c []                                      h = refl
quiet-fold c ((y , out (instEmit (value a) n)) ∷ rs) h = quiet-fold c rs (λ i → h (there i))
quiet-fold c ((y , out (instEmit (mark m) n)) ∷ rs)  h = ⊥-elim (h (here refl))
quiet-fold c ((y , end) ∷ rs)                        h = quiet-fold c rs (λ i → h (there i))
quiet-fold c ((y , skip) ∷ rs)                       h = quiet-fold c rs (λ i → h (there i))
quiet-fold c ((y , pin _) ∷ rs)                      h = quiet-fold c rs (λ i → h (there i))

-- A begin opens its route.
beg-open : ∀ {A} c n → Σ ℕ λ k → count {A} c (instEmit (mark begin) n) ≡ (n , suc k)
beg-open (m , k) n with n ≟ᵖ m
... | yes refl = k , refl
... | no _     = 0 , refl

-- An open route was opened by a begin of it, or was open already.
rise-step : ∀ {A} c (x : IE A) {n} → proj₁ (count c x) ≡ n → 0 < proj₂ (count c x)
          → x ≡ instEmit (mark begin) n ⊎ (proj₁ c ≡ n × 0 < proj₂ c)
rise-step (m , k) (instEmit (mark begin) n′) e lt with n′ ≟ᵖ m
... | yes refl = inj₁ (cong (λ z → instEmit (mark begin) z) e)
... | no _     = inj₁ (cong (λ z → instEmit (mark begin) z) e)
rise-step (m , zero)  (instEmit (mark stop) _) e ()
rise-step (m , suc k) (instEmit (mark stop) _) e lt = inj₂ (e , s≤s z≤n)
rise-step (m , k) (instEmit (mark over) _)       e ()
rise-step (m , k) (instEmit (mark outerOpen) _)  e lt = inj₂ (e , lt)
rise-step (m , k) (instEmit (mark outerClose) _) e lt = inj₂ (e , lt)
rise-step (m , k) (instEmit (mark laneStart) _)  e lt = inj₂ (e , lt)
rise-step (m , k) (instEmit (mark (laneDone _)) _)   e lt = inj₂ (e , lt)
rise-step (m , k) (instEmit (mark burstEnd) _)   e lt = inj₂ (e , lt)
rise-step (m , k) (instEmit (mark outerDone) _)  e lt = inj₂ (e , lt)
rise-step (m , k) (instEmit (mark subscribed) _) e lt = inj₂ (e , lt)
rise-step (m , k) (instEmit (mark completed) _)  e lt = inj₂ (e , lt)
rise-step (m , k) (instEmit (value _) _)         e lt = inj₂ (e , lt)

rise : ∀ {A} c (xs : List (IE A)) {n k} → L.foldl count c xs ≡ (n , suc k)
     → instEmit (mark begin) n ∈ xs ⊎ (proj₁ c ≡ n × 0 < proj₂ c)
rise c []       refl = inj₂ (refl , s≤s z≤n)
rise c (x ∷ xs) eq with rise (count c x) xs eq
... | inj₁ i        = inj₁ (there i)
... | inj₂ (e , lt) with rise-step c x e lt
...   | inj₁ refl = inj₁ (here refl)
...   | inj₂ r    = inj₂ r

dec-open : ∀ (c : Routes) n → Dec (Σ ℕ λ k → c ≡ (n , suc k))
dec-open (m , zero)  n = no λ { (_ , ()) }
dec-open (m , suc k) n with m ≟ᵖ n
... | yes refl = yes (k , refl)
... | no ne    = no λ { (_ , refl) → ne refl }

------------------------------------------------------------------------
-- A cold's runs

-- Where a step at `J` begins, and its begin.
B⁰ : Instant → Pos
B⁰ J = J ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ [])

-- No over of a value step at `J` lies before `y`.
NoOv : Instant → Pos → Set
NoOv J y = ∀ {T e i} → cascade T e (ix i) ≡ J → (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ [])) ≺ y → ⊥

noov-v : ∀ {T e i} → NoOv (cascade T e (ix i)) (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ []))
noov-v {T} {e} {i} refl h = same-≺⁻ (cascade T e (ix i)) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ []) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ []) h

noov-o : ∀ {T e i} → NoOv (cascade T e (ix i)) (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ []))
noov-o {T} {e} {i} refl h = same-≺⁻ (cascade T e (ix i)) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ []) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ []) h

noov-e : ∀ {T e} → NoOv (cascade T e last) (cascade T e last ∙ (ix 1 ∷ last ∷ []))
noov-e () _

inr : ∀ {X : Set} {rs zs} {x : X} → rs ≡ zs → x ∈ zs → x ∈ rs
inr refl m = m

-- No row of the subscribe burst lies in a fresh instant.
not-now : ∀ {p J zs ws} → p ⊕ zs ≡ (J ∙ ws) → Fresh p J → ⊥
not-now {p} {J} {zs} eq f = fresh-self (subst (Fresh p) (trans (cong instant (sym eq)) (instant-⊑ {p} {p ⊕ zs} (zs , refl))) f)

-- A begin, and the step it opens.
beg-name : ∀ {A p q n} → ColdRow {A} p q (out (instEmit (mark begin) n)) → Σ Instant λ K → q ≡ B⁰ K × n ≡ nm (K ∙ []) × Fresh p K
beg-name (step-begin f) = _ , refl , refl , f

module Runs {A : Set} (p : Pos) (t : EmissionSet (IE A)) (row : ∀ {y e} → t y e → Visible e → ColdRow p y e)
  (vb : ∀ {T e i a} → t (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ [])) (out (instEmit (value a) (cascade T e (ix i) ∙ [ ix 1 ])))
      → t (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ [])) (out (instEmit (mark begin) (cascade T e (ix i) ∙ [ ix 1 ]))))
  (ob : ∀ {T e i} → t (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ [])) (out (instEmit (mark over) (cascade T e (ix i) ∙ [ ix 1 ])))
      → t (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ [])) (out (instEmit (mark begin) (cascade T e (ix i) ∙ [ ix 1 ]))))
  (eb : ∀ {T e} → Fresh p (cascade T e last) → t (cascade T e last ∙ (ix 1 ∷ last ∷ [])) end
      → ¬ ¬ t (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ [])) (out (instEmit (mark begin) (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ [])))))
  where

  lt0 : ∀ {n} → n ≡ 0 → 0 < n → ⊥
  lt0 refl ()

  Bg : Instant → Ev (IE A)
  Bg J = out (instEmit (mark begin) (nm (J ∙ [])))

  -- The row where a fresh step begins is its begin.
  at-beg : ∀ {J k e} → ColdRow p k e → k ≡ B⁰ J → Fresh p J → e ≡ Bg J
  at-beg (now-value zs) eq f = ⊥-elim (not-now eq f)
  at-beg (now-end zs)   eq f = ⊥-elim (not-now eq f)
  at-beg (step-begin _) refl f = refl
  at-beg (step-value _) ()
  at-beg (step-over _)  ()
  at-beg (step-end _)   ()

  -- A value of a fresh instant is its step's.
  val-at : ∀ {K y a j} → ColdRow {A} p y (out (instEmit (value a) j)) → rootOf y ≡ (K ∙ []) → Fresh p K
         → y ≡ (K ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ [])) × j ≡ nm (K ∙ [])
  val-at (now-value zs) ro f =
    ⊥-elim (fresh-self (subst (Fresh p) (trans (sym (cong instant ro)) (cong instant (rootOf-ext p zs))) f))
  val-at (step-value _) refl f = refl , refl

  -- Rows between a step's begin and its later rows hold no mark.
  mid-mark : ∀ {k mk n J y} → ColdRow {A} p k (out (instEmit (mark mk) n)) → instant k ≡ J → B⁰ J ≺ k → k ≺ y → NoOv J y → ⊥
  mid-mark (step-begin {t′} {e′} {l} _) refl bk _ _ = ≺-irrefl {B⁰ (cascade t′ e′ l)} bk
  mid-mark (step-over _) eq _ ky noov = noov eq ky

  -- The begin is met before the row.
  beg-in : ∀ {rs r₁ y e r₂ J} → Met t rs → rs ≡ r₁ ++ (y , e) ∷ r₂ → Fresh p J → t (B⁰ J) (Bg J) → B⁰ J ≺ y → (B⁰ J , Bg J) ∈ r₁
  beg-in {r₁ = r₁} {y} {e} {r₂} {J} mt refl f x lt with run-has-ex mt x tt tt (≺→≼ {B⁰ J} {y} lt) (∈-++⁺ʳ r₁ (here refl))
  ... | e′ , m with ∈-++⁻ r₁ m
  ...   | inj₁ m₁         = subst (λ z → (B⁰ J , z) ∈ r₁) (at-beg (row (proj₁ (run-row mt m)) (proj₂ (run-row mt m))) refl f) m₁
  ...   | inj₂ (here eq)  = ⊥-elim (≺-irrefl {y} (subst (_≺ y) (cong proj₁ eq) lt))
  ...   | inj₂ (there m₂) = ⊥-elim (≺-absurd {B⁰ J} {y} lt (after-in r₁ mt m₂))

  -- So the route is open at a step's row.
  opened : ∀ {rs r₁ y e r₂ J} → Met t rs → rs ≡ r₁ ++ (y , e) ∷ r₂ → instant y ≡ J → Fresh p J → t (B⁰ J) (Bg J) → B⁰ J ≺ y
         → NoOv J y → Σ ℕ λ k → cnt r₁ ≡ (nm (J ∙ []) , suc k)
  opened {r₁ = r₁} {y} {e} {r₂} {J} mt refl iy f x by noov with ∈-∃++ (beg-in mt refl f x by)
  ... | a , m , refl with beg-open {A} (cnt a) (nm (J ∙ []))
  ...   | k , ek = k , trans (trans (cong (L.foldl count r₀) (values-++ a ((B⁰ J , Bg J) ∷ m))) (foldl-++ count r₀ (values a) _))
                         (trans (quiet-fold _ m quiet) ek)
    where
      run′ : Run t (cursor nothing a) ((B⁰ J , Bg J) ∷ (m ++ (y , e) ∷ r₂))
      run′ = run-tail a (subst (Run t nothing) (++-assoc a ((B⁰ J , Bg J) ∷ m) ((y , e) ∷ r₂)) mt)

      quiet : ∀ {k mk n} → (k , out (instEmit (mark mk) n)) ∈ m → ⊥
      quiet {k} i with run′
      ... | _ ∷ run =
        let bk = run-after run (∈-++⁺ˡ i)
            ky = run-order m run i (here refl)
        in mid-mark (row (proj₁ (run-row run (∈-++⁺ˡ i))) tt)
                    (trans (btw (B⁰ J) k y bk ky (sym iy)) refl) bk ky noov

  covered : ∀ {rs} → Met t rs → ∀ r₁ {y e} r₂ → rs ≡ r₁ ++ (y , e) ∷ r₂ → Carried e → ¬ Ex [ p ] y
          → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
  covered mt r₁ {y} {e} r₂ eq cr ne with run-row mt (subst ((y , e) ∈_) (sym eq) (∈-++⁺ʳ r₁ (here refl)))
  ... | x , v with row x v
  ...   | now-value zs = ⊥-elim (ne (here (⊑-inside {p} {p ⊕ zs} (zs , refl) , rootOf-ext p zs)))
  ...   | now-end zs   = ⊥-elim (ne (here (⊑-inside {p} {p ⊕ zs} (zs , refl) , rootOf-ext p zs)))
  ...   | step-begin _ with cr
  ...     | ()
  covered mt r₁ r₂ eq cr ne | x , v | step-value {T} {e′} {i} f =
    opened mt eq refl f (vb x) (same-≺ (cascade T e′ (ix i)) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ []) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ []) tt) noov-v
  covered mt r₁ r₂ eq cr ne | x , v | step-over {T} {e′} {i} f =
    opened mt eq refl f (ob x) (same-≺ (cascade T e′ (ix i)) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ []) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ []) tt) noov-o
  covered mt r₁ r₂ eq cr ne | x , v | step-end {T} {e′} f =
    decidable-stable (dec-open (cnt r₁) _) λ ¬o → eb f x λ xb →
      ¬o (opened mt eq refl f xb (same-≺ (cascade T e′ last) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ []) (ix 1 ∷ last ∷ []) tt) noov-e)

  fresh-ex : ∀ {K zs} → Fresh p K → ¬ Ex [ p ] (K ∙ zs)
  fresh-ex fK (here (_ , r)) = fresh-self (subst (Fresh p) (cong instant r) fK)
  fresh-ex fK (there ())

  shut : ∀ {rs} → Met t rs → ShutRun rs
  shut {rs} mt r₁ r₂ eq z {q} bq {y} {a} {j} yv ro with beg-name (row (proj₁ (run-row mt (inr eq (∈-++⁺ˡ bq)))) tt)
  ... | K , refl , eqn , fK with ∈-∃++ yv
  ...   | r₂a , r₂b , refl with val-at (row (proj₁ (run-row mt (inr eq (∈-++⁺ʳ r₁ yv)))) tt) ro fK
  ...     | refl , refl with covered mt (r₁ ++ r₂a) r₂b (trans eq (sym (++-assoc r₁ r₂a _))) c-value (fresh-ex fK)
  ...       | k , ek with rise (cnt r₁) (values r₂a)
                         (trans (sym (trans (cong (L.foldl count r₀) (values-++ r₁ r₂a)) (foldl-++ count r₀ (values r₁) (values r₂a)))) ek)
  ...         | inj₂ (_ , lt) = lt0 z lt
  ...         | inj₁ m with values-∈ r₂a m
  ...           | q′ , m′ with beg-name (row (proj₁ (run-row mt (inr eq (∈-++⁺ʳ r₁ (∈-++⁺ˡ {ys = (y , out (instEmit (value a) j)) ∷ r₂b} m′))))) tt)
  ...             | K′ , refl , eqK , _ =
    ≺-irrefl {B⁰ K} (subst (λ z → B⁰ K ≺ B⁰ z) (sym (trans (sym (nm-inst K)) (trans (cong instant eqK) (nm-inst K′))))
                      (run-order r₁ (subst (Met t) eq mt) bq (∈-++⁺ˡ m′)))

------------------------------------------------------------------------
-- The cold

cold-covered : ∀ m {Δ A} (c : Timeline A) (env : DenEnv Δ) p {rs} → Met (enter (ev m (coldˢ c) env) p) rs
             → ∀ r₁ {y e} r₂ → rs ≡ r₁ ++ (y , e) ∷ r₂ → Carried e → ¬ Ex [ p ] y
             → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
cold-covered m c env p = Runs.covered p (enter (ev m (coldˢ c) env) p) (cold-rows m c env p)
  (λ {T} {e} {i} {a} → cold-vb m c env p {T} {e} {i} {a}) (λ {T} {e} {i} → cold-ob m c env p {T} {e} {i})
  (λ {T} {e} → cold-eb m c env p {T} {e})

cold-shut : ∀ m {Δ A} (c : Timeline A) (env : DenEnv Δ) p {rs} → Met (enter (ev m (coldˢ c) env) p) rs → ShutRun rs
cold-shut m c env p = Runs.shut p (enter (ev m (coldˢ c) env) p) (cold-rows m c env p)
  (λ {T} {e} {i} {a} → cold-vb m c env p {T} {e} {i} {a}) (λ {T} {e} {i} → cold-ob m c env p {T} {e} {i})
  (λ {T} {e} → cold-eb m c env p {T} {e})
