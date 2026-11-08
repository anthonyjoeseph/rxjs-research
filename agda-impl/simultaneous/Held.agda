{-# OPTIONS --guardedness #-}

-- EVERY ELABORATED STREAM HOLDS (`simultaneous.Routed.Held`), former by
-- former, and so the batcher's source keeps its dead instants dead.
--
-- A `defer` is reached through its approximants: each is a finite tree,
-- so the formers' leaves hold of it by induction on the bound, and the
-- meaning is their limit.
module simultaneous.Held where

open import Data.List using (List; []; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (lookup; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Obs; Later; FlatOp; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Events using (Pos; Timeline; root; fresh; _≟ᵖ_; ix)
open import denotation.EmissionSet using (EmissionSet; Den; hot; enter; Proper; ⟦_⟧; DenEnv; approx)
open import simultaneous.SObs using (SObs; module Elaborate)
open import simultaneous.Relations using (elaborated)
open import simultaneous.Shut using (Shut)
open import simultaneous.Routed using (Held; HeldD; Early)
open import denotation.Laws.Worlds using (Hots; GoodEnv)
open import simultaneous.HeldMap using (held-map-den)
open import simultaneous.HeldScan using (held-scan-den)
open import simultaneous.HeldConnect using (held-conn; early-snoc)
open import denotation.Laws using (inv-⟦⟧; inv-approx; good-cons)
open import denotation.Laws.Worlds using (Ok; InvD; Lawful; TimerRoot; _⊕_; plain-untimed; plain-ix)
open import denotation.Laws.Connect using () renaming (lawful to src-lawful; ok₀ to body-ok)
open import Data.Empty using (⊥)
open import Data.List.Relation.Unary.Any using (here; there)
open import simultaneous.InstEmit using (begin; valuesOf)
open import Data.Product using (_×_; _,_; proj₁)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (IE; AIE; Routes; elab; annotate; marked; trackers; closer; combined; laneˢ; each;
  Input; react; going; fed; opening)
open import simultaneous.HeldComb using (ev; CombIn; RunHeld; ShutRun; outRows; comb-held; init; from; past; lay; Local; Locals;
  locals-runs; local-end; run-row; walk; inv-past; step-local)
open import simultaneous.Shut using (r₀)
open import simultaneous.SObs using (Flat)
open import simultaneous.Routed using (Ex)
open import Data.List.Properties using (++-assoc)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; proj₂)
open import simultaneous.SObs using (outerB; laneB; closeB)
open import simultaneous.InstEmit using (instEmit; value; mark; over; outerOpen; outerClose; outerDone)
open import simultaneous.Routed using (nameOf; nm; Valued; opos; Before)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Relations using (Met)
open import simultaneous.HeldConnect using (inst-snoc; before-ext)
open import denotation.Read using (Visible)
open import denotation.EmissionSet using (Ev; out; end)
open import denotation.Events using (sub; last)
open import denotation.Laws.Worlds using (InvAt; ok-step; _⊑_; ⊑-trans; ⊑-snoc⁺; real-snoc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (trans; sym; cong; subst)
open import Tree using (mergeᶠ)
open import Data.Bool using (true; false)

------------------------------------------------------------------------
-- Programs and their binders

-- A connect's binder: its source annotated, read hot past the connect
-- at `at`, the source holding, and every burst it is exempt for one the
-- reader is exempt for too.
record Bound {X : Set} (d : Den (AIE X)) (cs : List Pos) : Set₁ where
  field
    {Θ}   : List Set
    m     : Maybe ℕ
    src   : Obs Timeline Θ (IE X)
    env   : DenEnv Θ
    at    : Pos
    outer : List Pos
    held  : HeldD (Hots env) (ev m src env) outer
    under : ∀ {c} → c ∈ at ∷ outer → c ∈ cs
    is    : d ≡ hot (Proper (enter (ev m (annotate src) env) (at ++ [ ix 1 ])))

EnvHeld : ∀ {Γ Δ} → (∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → DenEnv Δ → List Pos → Set₁
EnvHeld {Γ} ρ env cs = ∀ {X} (i : X ∈ Γ) → Bound (lookup env (ρ (∈-map⁺ AIE i))) cs

-- Held under every environment of held binders.  A record, so that a
-- statement about a former is compared by its arguments, never by the
-- elaborated tree its meaning unfolds to.
record IH (m : Maybe ℕ) {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) : Set₁ where
  constructor ih
  field holds : ∀ (env : DenEnv Δ) cs → GoodEnv env → EnvHeld ρ env cs → HeldD (Hots env) (ev m (elab ρ o) env) cs

------------------------------------------------------------------------
-- The formers

-- EACH ELABORATED FORMER HOLDS when its children do, under the meaning
-- and under every approximant alike.
postulate
  held-cold      : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (c : Timeline A) → IH m ρ (cold c)
  held-empty     : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → IH m ρ (empty {A = A})
  held-of        : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (xs : L.List A) → IH m ρ (of xs)
  held-takeWhile : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) i (p : A → _) s → IH m ρ s → IH m ρ (takeWhile i p s)
  held-connected : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) → IH m ρ (connected i)

held-map : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : A → B) s → IH m ρ s → IH m ρ (map f s)
held-map nothing  ρ f s (ih h) = ih λ env cs g eh → held-map-den f (⟦ elab ρ s ⟧ env) cs (h env cs g eh)
held-map (just n) ρ f s (ih h) = ih λ env cs g eh → held-map-den f (approx n (elab ρ s) env) cs (h env cs g eh)

held-scan : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : B → A → B) z s → IH m ρ s → IH m ρ (scan f z s)
held-scan nothing  ρ f z s (ih h) = ih λ env cs g eh → held-scan-den f (z , marked begin) (⟦ elab ρ s ⟧ env) cs (h env cs g eh)
held-scan (just n) ρ f z s (ih h) = ih λ env cs g eh → held-scan-den f (z , marked begin) (approx n (elab ρ s) env) cs (h env cs g eh)

-- A binder held under `cs` is held under more.
widen : ∀ {X} {d : Den (AIE X)} {c cs} → Bound d cs → Bound d (c ∷ cs)
widen b = record
  { m = Bound.m b ; src = Bound.src b ; env = Bound.env b ; at = Bound.at b ; outer = Bound.outer b
  ; held = Bound.held b ; under = λ i → there (Bound.under b i) ; is = Bound.is b }

-- A connect shows its body, read over its source made hot.
conn-ev : ∀ m {Δ X B} (A′ : Obs Timeline Δ X) (B′ : Obs Timeline (X ∷ Δ) (IE B)) (env : DenEnv Δ) cs → GoodEnv env
        → ∀ p → Ok (Hots env) p → (TimerRoot p → ⊥) → Early p
        → (Lawful (Proper (enter (ev m A′ env) (p ++ [ ix 1 ])))
           → Ok (Hots env ⊕ Proper (enter (ev m A′ env) (p ++ [ ix 1 ]))) (p ++ [ ix 0 ]) → Early (p ++ [ ix 0 ])
           → Held (enter (ev m B′ (hot (Proper (enter (ev m A′ env) (p ++ [ ix 1 ]))) ∷ env)) (p ++ [ ix 0 ])) ((p ++ [ ix 0 ]) ∷ p ∷ cs))
        → Held (enter (ev m (connect A′ B′) env) p) (p ∷ cs)
conn-ev nothing A′ B′ env cs g p ok nt ep k =
  held-conn (⟦ A′ ⟧ env) (λ h → ⟦ B′ ⟧ (h ∷ env)) Is IF p ok nt cs
    (k (src-lawful {s = ⟦ A′ ⟧ env} {F = λ h → ⟦ B′ ⟧ (h ∷ env)} Is IF p ok) (body-ok {s = ⟦ A′ ⟧ env} {F = λ h → ⟦ B′ ⟧ (h ∷ env)} Is IF p ok)
       (early-snoc (ix 0) (proj₁ ok) nt ep))
  where
    Is = inv-⟦⟧ A′ env g
    IF : ∀ {t} → Lawful t → InvD (Hots env ⊕ t) (⟦ B′ ⟧ (hot t ∷ env))
    IF L = inv-⟦⟧ B′ (hot _ ∷ env) (good-cons L g)
conn-ev (just n) A′ B′ env cs g p ok nt ep k =
  held-conn (approx n A′ env) (λ h → approx n B′ (h ∷ env)) Is IF p ok nt cs
    (k (src-lawful {s = approx n A′ env} {F = λ h → approx n B′ (h ∷ env)} Is IF p ok)
       (body-ok {s = approx n A′ env} {F = λ h → approx n B′ (h ∷ env)} Is IF p ok)
       (early-snoc (ix 0) (proj₁ ok) nt ep))
  where
    Is = inv-approx n A′ env g
    IF : ∀ {t} → Lawful t → InvD (Hots env ⊕ t) (approx n B′ (hot t ∷ env))
    IF L = inv-approx n B′ (hot _ ∷ env) (good-cons L g)

held-connect : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B)
             → IH m ρ s → (∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE (A ∷ Γ) → X ∈ Δ′) → IH m ρ′ b) → IH m ρ (connect s b)
held-connect m ρ s b (ih hs) hb = ih λ env cs g eh p ok nt ep →
  conn-ev m (annotate (elab ρ s)) _ env cs g p ok nt ep λ L ok₀ ep₀ →
    IH.holds (hb _) _ (p ∷ cs) (good-cons L g)
      (λ { (here refl) → record { m = m ; src = elab ρ s ; env = env ; at = p ; outer = cs ; held = hs env cs g eh
                                ; under = λ i → i ; is = refl }
         ; (there i)   → widen (eh i) })
      (p ++ [ ix 0 ]) ok₀ (plain-untimed p plain-ix) ep₀

-- A FLATMAP'S SCAN HOLDS, read past the three connects that share its
-- outer: the outer at `p ++ [ ix 1 ]`, the closer, then the real
-- flatMap, each made hot.  What it reads: the connects in scope, the
-- outer, the lanes and the closer.
module FlatHots (m : Maybe ℕ) {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (op : FlatOp) (f : A → Obs Timeline Γ B)
                (s : Obs Timeline Γ A) (env : DenEnv Δ) (p : Pos) where

  g : A → Obs Timeline (IE B ∷ IE A ∷ Δ) (IE B)
  g a = elab (λ i → there (there (ρ i))) (f a)

  tk : Obs Timeline (IE B ∷ IE B ∷ IE A ∷ Δ) (ℕ × Routes)
  tk = trackers Γ 0 (λ i → there (there (there (ρ i))))

  real : Obs Timeline (IE B ∷ IE A ∷ Δ) (IE B)
  real = flatMap op (λ a → laneˢ (g a)) (each valuesOf (connected (there (here refl))))

  p₀ p₀₀ : Pos
  p₀  = p ++ [ ix 0 ]
  p₀₀ = p₀ ++ [ ix 0 ]

  σ₁ : EmissionSet (IE A)
  σ₁ = Proper (enter (ev m (elab ρ s) env) (p ++ [ ix 1 ]))

  σ₂ : EmissionSet (IE B)
  σ₂ = Proper (enter (ev m closer (hot σ₁ ∷ env)) (p₀ ++ [ ix 1 ]))

  σ₃ : EmissionSet (IE B)
  σ₃ = Proper (enter (ev m real (hot σ₂ ∷ hot σ₁ ∷ env)) (p₀₀ ++ [ ix 1 ]))

  env′ : DenEnv (IE B ∷ IE B ∷ IE A ∷ Δ)
  env′ = hot σ₃ ∷ hot σ₂ ∷ hot σ₁ ∷ env

  P : Pos
  P = p₀₀ ++ [ ix 0 ]

  -- What the scan reads: the connects in scope, then its own branches.
  src : Obs Timeline (IE B ∷ IE B ∷ IE A ∷ Δ) (Maybe (Input B))
  src = takeWhile false going (flatMap (mergeᶠ nothing) (fed tk) (of (true ∷ false ∷ [])))

  scanned : EmissionSet (IE B)
  scanned = enter (ev m (combined op tk) env′) P

  M : EmissionSet (Maybe (Input B))
  M = enter (ev m src env′) P

-- Either reading is lawful.
inv-ev : ∀ m {Γ A} (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → InvD (Hots ρ) (ev m o ρ)
inv-ev nothing  o ρ g = inv-⟦⟧ o ρ g
inv-ev (just n) o ρ g = inv-approx n o ρ g

-- What a hot reader re-keys keeps its instant.
inst-sub : ∀ {A H p} {X : EmissionSet A} → InvAt H p X → ∀ {q e} → X q e → ∀ w → instantOf (q ++ [ sub w ]) ≡ instantOf q
inst-sub I x w = inst-snoc _ (sub w) (InvAt.real I x) (InvAt.untimed I x)

-- Four labels deep, a position's instant is fixed.
inst-P : ∀ p zs → instantOf ((((p ++ [ ix 0 ]) ++ [ ix 0 ]) ++ [ ix 0 ]) ++ zs) ≡ instantOf (((p ++ [ ix 0 ]) ++ [ ix 0 ]) ++ [ ix 0 ])
inst-P []                      zs = refl
inst-P (ix _ ∷ [])             zs = refl
inst-P (ix _ ∷ ix _ ∷ _)       zs = refl
inst-P (ix _ ∷ last ∷ _)       zs = refl
inst-P (ix _ ∷ sub _ ∷ [])     zs = refl
inst-P (ix _ ∷ sub _ ∷ _ ∷ _)  zs = refl
inst-P (sub _ ∷ _)             zs = refl
inst-P (last ∷ _)              zs = refl

-- Under a position of the same instant, a step is as early.
early-inst : ∀ {y} zs → instantOf (y ++ zs) ≡ instantOf y → Early y → Early (y ++ zs)
early-inst {y} zs eq ey = subst (λ I → Valued I → Before (y ++ zs) (opos I)) (sym eq) (λ v → before-ext zs (ey v))

-- Over a re-keyed row, an over keeps its place.
late-sub : ∀ {q} w → instantOf (q ++ [ sub w ]) ≡ instantOf q → Valued (instantOf q) × opos (instantOf q) ⊑ q
         → Valued (instantOf (q ++ [ sub w ])) × opos (instantOf (q ++ [ sub w ])) ⊑ (q ++ [ sub w ])
late-sub {q} w eq (v , o) = subst (λ I → Valued I × opos I ⊑ (q ++ [ sub w ])) (sym eq) (v , ⊑-trans o (⊑-snoc⁺ q))

-- An opened outer row is a mark it was, unless it opens.
open-mark : ∀ {A B} {x : IE A} {m n} → opening {B = B} x ≡ instEmit (mark m) n → (m ≡ outerOpen → ⊥) → x ≡ instEmit (mark m) n
open-mark {x = instEmit (value _) _} refl no = ⊥-elim (no refl)
open-mark {x = instEmit (mark _) _}  refl _  = refl

open-value : ∀ {A B} {x : IE A} {a n} → opening {B = B} x ≡ instEmit (value a) n → ⊥
open-value {x = instEmit (value _) _} ()
open-value {x = instEmit (mark _) _}  ()

-- What the closer sends: a bracket's close, then the outer's end.
data Closing {B : Set} : IE B → Set where
  c-close : ∀ {n} → Closing (instEmit (mark outerClose) n)
  c-done  : ∀ {n} → Closing (instEmit (mark outerDone) n)

closing-mark : ∀ {B} {m n} → Closing {B} (instEmit (mark m) n) → (m ≡ outerClose → ⊥) → (m ≡ outerDone → ⊥) → ⊥
closing-mark c-close a _ = a refl
closing-mark c-done  _ b = b refl

closing-value : ∀ {B} {a n} → Closing {B} (instEmit (value a) n) → ⊥
closing-value ()

-- WHAT THE SCAN'S SOURCE MEETS, read past the three connects: a
-- tracker's report, a branch's row re-keyed where the branch's reader
-- subscribed it, or the end, under the scan's own subscription.
module CombSrc (m : Maybe ℕ) {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (op : FlatOp) (f : A → Obs Timeline Γ B)
               (s : Obs Timeline Γ A) (env : DenEnv Δ) (cs : List Pos) (gd : GoodEnv env) (eh : EnvHeld ρ env cs)
               (hs : HeldD (Hots env) (ev m (elab ρ s) env) cs) (hf : ∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ (f a))
               (p : Pos) (ok : Ok (Hots env) p) (nt : TimerRoot p → ⊥) (ep : Early p)
               (L₁ : Lawful (FlatHots.σ₁ m ρ op f s env p)) (L₂ : Lawful (FlatHots.σ₂ m ρ op f s env p))
               (L₃ : Lawful (FlatHots.σ₃ m ρ op f s env p))
               (ok₂ : Ok (Hots (hot (FlatHots.σ₂ m ρ op f s env p) ∷ hot (FlatHots.σ₁ m ρ op f s env p) ∷ env)) (FlatHots.p₀₀ m ρ op f s env p))
               (ok₃ : Ok (Hots (FlatHots.env′ m ρ op f s env p)) (FlatHots.P m ρ op f s env p))
               (ep₃ : Early (FlatHots.P m ρ op f s env p)) where
  open FlatHots m ρ op f s env p

  data MRow : Pos → Ev (Maybe (Input B)) → Set where
    tracker : ∀ {q x} → MRow q (out (just (inj₂ x)))
    outer   : ∀ {q w x y} → σ₁ q (out x) → opening x ≡ y → MRow (q ++ [ sub w ]) (out (just (inj₁ (outerB , y))))
    lane    : ∀ {q w x} → σ₃ q (out x) → MRow (q ++ [ sub w ]) (out (just (inj₁ (laneB , x))))
    close   : ∀ {q w x} → σ₂ q (out x) → MRow (q ++ [ sub w ]) (out (just (inj₁ (closeB , x))))
    done    : ∀ {zs} → MRow (P ++ zs) end

  postulate
    -- Every row the scan's source meets is one of these.
    m-rows      : ∀ {q e} → M q e → Visible e → MRow q e
    -- The lanes' rows: begins named for their instants, values before
    -- their over, overs at it.
    lane-named  : ∀ {q n} → σ₃ q (out (instEmit (mark begin) n)) → n ≡ nameOf q
    lane-early  : ∀ {q a n} → σ₃ q (out (instEmit (value a) n)) → Early q
    lane-late   : ∀ {q n} → σ₃ q (out (instEmit (mark over) n)) → Valued (instantOf q) × opos (instantOf q) ⊑ q
    close-marks : ∀ {q x} → σ₂ q (out x) → Closing x

  cs′ : List Pos
  cs′ = P ∷ p₀₀ ∷ p₀ ∷ p ∷ cs

  -- THE SCAN'S COUNTERS TRACK THE BRANCHES, row by row of a run met:
  -- the routes open at a row are of its instant; a value read, a live
  -- over read, and the end find one open unless exempt; and a dead
  -- instant stays dead.
  postulate
    start-current : ∀ rx₁ {q e rx₂} → Met M (rx₁ ++ (q , e) ∷ rx₂) → Visible e
                  → proj₂ (from r₀ (outRows op init rx₁)) ≡ 0 ⊎ proj₁ (from r₀ (outRows op init rx₁)) ≡ nameOf q
    value-open    : ∀ rx₁ {q b a n rx₂} → Met M (rx₁ ++ (q , out (just (inj₁ (b , instEmit (value a) n)))) ∷ rx₂) → ¬ Ex cs′ q
                  → Σ ℕ λ k → proj₂ (from r₀ (outRows op init rx₁)) ≡ suc k
    over-open     : ∀ rx₁ {q b n rx₂} → Met M (rx₁ ++ (q , out (just (inj₁ (b , instEmit (mark over) n)))) ∷ rx₂)
                  → Flat.spent (proj₁ (past op init rx₁)) ≡ false → ¬ Ex cs′ q
                  → Σ ℕ λ k → proj₂ (from r₀ (outRows op init rx₁)) ≡ suc k
    end-open      : ∀ rx₁ {q rx₂} → Met M (rx₁ ++ (q , end) ∷ rx₂) → ¬ Ex cs′ q
                  → Σ ℕ λ k → from r₀ (outRows op init rx₁) ≡ (nameOf q , suc k)
    comb-shut     : ∀ {rx} → Met M rx → ShutRun (outRows op init rx)

  I₁ : InvAt (Hots env) (p ++ [ ix 1 ]) (enter (ev m (elab ρ s) env) (p ++ [ ix 1 ]))
  I₁ = inv-ev m (elab ρ s) env gd (p ++ [ ix 1 ]) (ok-step p ok)

  I₃ : InvAt (Hots (hot σ₂ ∷ hot σ₁ ∷ env)) (p₀₀ ++ [ ix 1 ]) (enter (ev m real (hot σ₂ ∷ hot σ₁ ∷ env)) (p₀₀ ++ [ ix 1 ]))
  I₃ = inv-ev m real (hot σ₂ ∷ hot σ₁ ∷ env) (good-cons L₂ (good-cons L₁ gd)) (p₀₀ ++ [ ix 1 ]) (ok-step p₀₀ ok₂)

  H₁ : Held (enter (ev m (elab ρ s) env) (p ++ [ ix 1 ])) ((p ++ [ ix 1 ]) ∷ cs)
  H₁ = hs (p ++ [ ix 1 ]) (ok-step p ok) (plain-untimed p plain-ix) (early-snoc (ix 1) (proj₁ ok) nt ep)

  named : ∀ {q b n} → M q (out (just (inj₁ (b , instEmit (mark begin) n)))) → n ≡ nameOf q
  named x with m-rows x tt
  ... | outer {w = w} y eq with refl ← open-mark eq (λ ()) =
    trans (Held.named H₁ (proj₁ y)) (cong nm (sym (inst-sub I₁ (proj₁ y) w)))
  ... | lane {w = w} y  = trans (lane-named y) (cong nm (sym (inst-sub I₃ (proj₁ y) w)))
  ... | close y = ⊥-elim (closing-mark (close-marks y) (λ ()) (λ ()))

  early : ∀ {q b a n} → M q (out (just (inj₁ (b , instEmit (value a) n)))) → Early q
  early x with m-rows x tt
  ... | outer y eq = ⊥-elim (open-value eq)
  ... | lane {w = w} y = early-inst [ sub w ] (inst-sub I₃ (proj₁ y) w) (lane-early y)
  ... | close y = ⊥-elim (closing-value (close-marks y))

  ends : ∀ {q} → M q end → Early q
  ends x with m-rows x tt
  ... | done {zs} = early-inst zs (inst-P p zs) ep₃

  late : ∀ {q b n} → M q (out (just (inj₁ (b , instEmit (mark over) n)))) → Valued (instantOf q) × opos (instantOf q) ⊑ q
  late x with m-rows x tt
  ... | outer {w = w} y eq with refl ← open-mark eq (λ ()) = late-sub w (inst-sub I₁ (proj₁ y) w) (Held.late H₁ (proj₁ y))
  ... | lane {w = w} y = late-sub w (inst-sub I₃ (proj₁ y) w) (lane-late y)
  ... | close y = ⊥-elim (closing-mark (close-marks y) (λ ()) (λ ()))

  IM : InvAt (Hots env′) P M
  IM = inv-ev m src env′ (good-cons L₃ (good-cons L₂ (good-cons L₁ gd))) P ok₃

  -- An output laid under a row is of the row's instant.
  inst-lay : ∀ {q e} → M q e → ∀ j → instantOf (q ++ ix 1 ∷ ix j ∷ []) ≡ instantOf q
  inst-lay {q} x j =
    trans (cong instantOf (sym (++-assoc q [ ix 1 ] [ ix j ])))
      (trans (inst-snoc (q ++ [ ix 1 ]) (ix j) (real-snoc q plain-ix (InvAt.real IM x)) (plain-untimed q plain-ix))
             (inst-snoc q (ix 1) (InvAt.real IM x) (InvAt.untimed IM x)))

  comb-runs : ∀ {rx} → Met M rx → RunHeld cs′ (outRows op init rx)
  comb-runs {rx} mt = locals-runs (walk op cs′ init r₀ rx step fin) (comb-shut mt)
    where
      step : ∀ rx₁ {q x} rx₂ → rx ≡ rx₁ ++ (q , out x) ∷ rx₂
           → Locals cs′ (from r₀ (outRows op init rx₁)) (lay q 0 (proj₂ (react op (past op init rx₁) x)))
      step rx₁ {q} {x} rx₂ refl =
        step-local op cs′ (past op init rx₁) (from r₀ (outRows op init rx₁)) q x (inv-past op rx₁) (start-current rx₁ mt tt)
          (λ { refl → named (proj₁ (run-row rx₁ mt)) })
          (λ { refl ne → value-open rx₁ mt ne })
          (λ { refl sp ne → over-open rx₁ mt sp ne })
          (inst-lay (proj₁ (run-row rx₁ mt)))

      fin : ∀ rx₁ {q} rx₂ → rx ≡ rx₁ ++ (q , end) ∷ rx₂ → Local cs′ (from r₀ (outRows op init rx₁)) q end
      fin rx₁ rx₂ refl = local-end (end-open rx₁ mt) (start-current rx₁ mt tt)

  comb : CombIn op M (P ∷ p₀₀ ∷ p₀ ∷ p ∷ cs)
  comb = record { named = named ; early = early ; ends = ends ; late = late ; runs = comb-runs }

held-comb : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) s
            (env : DenEnv Δ) cs → GoodEnv env → EnvHeld ρ env cs → HeldD (Hots env) (ev m (elab ρ s) env) cs
          → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ (f a))
          → ∀ p → Ok (Hots env) p → (TimerRoot p → ⊥) → Early p
          → let open FlatHots m ρ op f s env p in
            Lawful σ₁ → Lawful σ₂ → Lawful σ₃ → Ok (Hots (hot σ₂ ∷ hot σ₁ ∷ env)) p₀₀ → Ok (Hots env′) P → Early P
          → Held scanned (P ∷ p₀₀ ∷ p₀ ∷ p ∷ cs)
held-comb m ρ op f s env cs gd eh hs hf p ok nt ep L₁ L₂ L₃ ok₂ ok₃ ep₃ =
  comb-held m op src env′ P _ (good-cons L₃ (good-cons L₂ (good-cons L₁ gd))) ok₃
    (CombSrc.comb m ρ op f s env cs gd eh hs hf p ok nt ep L₁ L₂ L₃ ok₂ ok₃ ep₃)
  where open FlatHots m ρ op f s env p using (src; env′; P)

held-flatMap : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) s → IH m ρ s
             → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ (f a)) → IH m ρ (flatMap op f s)
held-flatMap m ρ op f s (ih hs) hf = ih λ env cs g eh p ok nt ep →
  conn-ev m (elab ρ s) _ env cs g p ok nt ep λ L₁ ok₁ ep₁ →
    conn-ev m closer _ _ (p ∷ cs) (good-cons L₁ g) (p ++ [ ix 0 ]) ok₁ (plain-untimed p plain-ix) ep₁ λ L₂ ok₂ ep₂ →
      conn-ev m (FlatHots.real m ρ op f s env p) _ _ ((p ++ [ ix 0 ]) ∷ p ∷ cs) (good-cons L₂ (good-cons L₁ g))
        ((p ++ [ ix 0 ]) ++ [ ix 0 ]) ok₂ (plain-untimed (p ++ [ ix 0 ]) plain-ix) ep₂ λ L₃ ok₃ ep₃ →
        held-comb m ρ op f s env cs g eh (hs env cs g eh) hf p ok nt ep L₁ L₂ L₃ ok₂ ok₃ ep₃

-- THE BOTTOM APPROXIMANT shows only skips; each further one is the body
-- under a `defer`'s guard; the meaning is the approximants' limit.
postulate
  held-⊥    : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A) → IH (just zero) ρ (defer l)
  held-next : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A)
            → IH (just n) ρ (Later.force l) → IH (just (suc n)) ρ (defer l)
  held-lim  : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A)
            → (∀ n → IH (just n) ρ (defer l)) → IH nothing ρ (defer l)

held-approx : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) → IH (just n) ρ o
held-approx n       ρ (cold c)          = held-cold (just n) ρ c
held-approx n       ρ empty             = held-empty (just n) ρ
held-approx n       ρ (of xs)           = held-of (just n) ρ xs
held-approx n       ρ (map f s)         = held-map (just n) ρ f s (held-approx n ρ s)
held-approx n       ρ (scan f z s)      = held-scan (just n) ρ f z s (held-approx n ρ s)
held-approx n       ρ (takeWhile i p s) = held-takeWhile (just n) ρ i p s (held-approx n ρ s)
held-approx n       ρ (flatMap op f s)  = held-flatMap (just n) ρ op f s (held-approx n ρ s) λ a ρ′ → held-approx n ρ′ (f a)
held-approx n       ρ (connect s b)     = held-connect (just n) ρ s b (held-approx n ρ s) λ ρ′ → held-approx n ρ′ b
held-approx n       ρ (connected i)     = held-connected (just n) ρ i
held-approx zero    ρ (defer l)         = held-⊥ ρ l
held-approx (suc n) ρ (defer l)         = held-next n ρ l (held-approx n ρ (Later.force l))

held-⟦⟧ : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) → IH nothing ρ o
held-⟦⟧ ρ (cold c)          = held-cold nothing ρ c
held-⟦⟧ ρ empty             = held-empty nothing ρ
held-⟦⟧ ρ (of xs)           = held-of nothing ρ xs
held-⟦⟧ ρ (map f s)         = held-map nothing ρ f s (held-⟦⟧ ρ s)
held-⟦⟧ ρ (scan f z s)      = held-scan nothing ρ f z s (held-⟦⟧ ρ s)
held-⟦⟧ ρ (takeWhile i p s) = held-takeWhile nothing ρ i p s (held-⟦⟧ ρ s)
held-⟦⟧ ρ (flatMap op f s)  = held-flatMap nothing ρ op f s (held-⟦⟧ ρ s) λ a ρ′ → held-⟦⟧ ρ′ (f a)
held-⟦⟧ ρ (connect s b)     = held-connect nothing ρ s b (held-⟦⟧ ρ s) λ ρ′ → held-⟦⟧ ρ′ b
held-⟦⟧ ρ (connected i)     = held-connected nothing ρ i
held-⟦⟧ ρ (defer l)         = held-lim ρ l λ n → held-approx n ρ (defer l)

------------------------------------------------------------------------
-- The top

-- THE BATCHER'S SOURCE HOLDS: the elaborated program, restamped, beside
-- the subscribe and completion marks, exempt for the subscribe burst.
postulate
  held-top : ∀ {A} (o : SObs [] A) → IH nothing (λ i → i) o → Held (elaborated o) (root ∷ [])

held : ∀ {A} (o : SObs [] A) → Held (elaborated o) (root ∷ [])
held o = held-top o (held-⟦⟧ (λ i → i) o)

-- The elaborated program's instants stay dead.
shut : ∀ {A : Set} (o : SObs [] A) → Shut (elaborated o)
shut o = Held.shut (held o)
