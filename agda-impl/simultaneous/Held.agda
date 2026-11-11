{-# OPTIONS --guardedness #-}

-- EVERY ELABORATED STREAM HOLDS (`simultaneous.Routed.Held`), former by
-- former, and so the batcher's source keeps its dead instants dead.
--
-- A `defer` is reached through its approximants: each is a finite tree,
-- so the formers' leaves hold of it by induction on the bound, and the
-- meaning is their limit.
module simultaneous.Held where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (lookup; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Obs; Later; FlatOp; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; sub; last; _⊕_; _∙_; frame; cascade)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Den; hot; enter; Proper; ⟦_⟧; DenEnv; approx)
open import simultaneous.SObs using (SObs; plain; module Elaborate)
open import simultaneous.Relations using (elaborated)
open import simultaneous.Shut using (Shut)
open import simultaneous.Routed using (Held; HeldD; Early)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Shows)
open import simultaneous.HeldMap using (held-map-den)
open import simultaneous.HeldScan using (held-scan-den)
open import simultaneous.HeldConnect using (held-conn; early-inst)
open import denotation.Laws using (inv-⟦⟧; inv-approx; good-cons)
open import denotation.Laws.Worlds using (Ok; InvD; Lawful; _∪ʰ_)
open import denotation.Laws.Connect using () renaming (lawful to src-lawful; ok₀ to body-ok)
open import denotation.Laws.Shows using (k-shows)
open import denotation.Laws.ShowsEv using (sk-⟦⟧; sk-approx)
open import Data.Empty using (⊥)
open import Data.List.Relation.Unary.Any using (here; there)
open import simultaneous.InstEmit using (begin; valuesOf)
open import Data.Product using (_×_; _,_; proj₁)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) using (IE; AIE; Routes; elab; annotate; marked; trackers; closer; combined; laneˢ; each; coldˢ;
  Input; react; going; fed; opening; anyHolds)
open import simultaneous.HeldComb using (ev; CombIn; RunHeld; ShutRun; outRows; init; from; past; lay; Local; Locals;
  locals-runs; local-end; run-row; walk; inv-past; step-local; Laid; laid; ended; laid-in; runs-prefix; held-runs)
open import simultaneous.FlatSim using (react-sent; passed; routed; minted; NoCB; tot)
open import simultaneous.HeldComb using (exact-past; inv-at)
open import simultaneous.Reach using (module Reached)
open import simultaneous.Routed using (valued; Idle; Rest; Routing; r-begin; r-stop; r-over; r-subscribed; r-completed)
open import Relation.Nullary.Decidable using (decidable-stable)
open import Data.Bool.Properties using (T?)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import denotation.Laws.Worlds using (inside-⊑; ⊑-inside)
open import simultaneous.InstEmit using (stop; subscribed; completed; laneStart; carry; laneDone; burstEnd)
open import simultaneous.Shut using (r₀)
open import simultaneous.SObs using (Flat)
open import simultaneous.Routed using (Ex)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; proj₂)
open import simultaneous.SObs using (outerB; laneB; closeB)
open import simultaneous.InstEmit using (instEmit; value; mark; over; outerOpen; outerClose; outerDone)
open import simultaneous.Routed using (nameOf; nm; Valued; opos)
open import simultaneous.Readings using (rootOf)
open import simultaneous.Relations using (Met)
open import simultaneous.HeldConnect using (rootOf-ext)
open import denotation.Read using (Visible)
open import denotation.EmissionSet using (Ev; out; end)
open import denotation.Laws.Worlds using (InvAt; ok-step; _⊑_; ⊑-trans)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (trans; sym; cong; subst)
open import Tree using (mergeᶠ)
open import Data.Bool using (true; false)
open import simultaneous.Project using (Proj; proj-outs; run-prefix)
open import denotation.EmissionSet using (skip; pin; Few; _≼_; module TakeWhile)
open import denotation.Read using (After; cursor)
open import Data.Nat.Properties using (0≢1+n)
open import Data.Bool using (T)
open import denotation.Position using (isLt; cmpPath)
open import denotation.Simultaneity using (reflⁱ)
open import denotation.EmissionSet using (_≺_)
open import simultaneous.Routed using (cnt; Carried)
open import simultaneous.HeldComb using (ShutRun)

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
    is    : d ≡ hot (Proper (enter (ev m (annotate src) env) (at ⊕ [ ix 1 ])))

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
  held-empty     : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → IH m ρ (empty {A = A})
  held-of        : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (xs : L.List A) → IH m ρ (of xs)
  held-takeWhile : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) i (p : A → _) s → IH m ρ s → IH m ρ (takeWhile i p s)
  held-connected : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) → IH m ρ (connected i)

-- THE COLD'S ROWS, subscribed at `p`: its synchronous values and end lie
-- in the subscribe burst, named `root`.  Each async step at `I` renders
-- under its lane at `I ∙ [ ix 1 ]`: a value step's `of` sends begin,
-- value and over beneath `nm I ⊕ [ ix 0 ]`, the over at `opos I`.  A
-- completion is an instant of its own, even straight after a value: its
-- begin lies where a value step's does, under the name one queued lane
-- further down, and the cold's end carries that route
-- (`simultaneous.Routed.Carried`) from where the step's lane completes.
data ColdRow {A : Set} (p : Pos) : Pos → Ev (IE A) → Set where
  now-value  : ∀ zs {a} → ColdRow p (p ⊕ zs) (out (instEmit (value a) root))
  now-end    : ∀ zs → ColdRow p (p ⊕ zs) end
  step-begin : ∀ {t e l} → ColdRow p (cascade t e l ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ []))
                                     (out (instEmit (mark begin) (nm (cascade t e l ∙ []))))
  step-value : ∀ {t e i a} → ColdRow p (cascade t e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ []))
                                       (out (instEmit (value a) (nm (cascade t e (ix i) ∙ []))))
  step-over  : ∀ {t e i} → ColdRow p (cascade t e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ []))
                                     (out (instEmit (mark over) (nm (cascade t e (ix i) ∙ []))))
  step-end   : ∀ {t e} → ColdRow p (cascade t e last ∙ (ix 1 ∷ last ∷ [])) end

-- A step's route opens at its begin and nothing comes between: what the
-- cold's runs ask needs the order of its rows, which `ColdRow` does not
-- carry.
postulate
  cold-rows    : ∀ m {Δ A} (c : Timeline A) (env : DenEnv Δ) p {y e}
               → enter (ev m (coldˢ c) env) p y e → Visible e → ColdRow p y e
  cold-covered : ∀ m {Δ A} (c : Timeline A) (env : DenEnv Δ) p {rs} → Met (enter (ev m (coldˢ c) env) p) rs
               → ∀ r₁ {y e} r₂ → rs ≡ r₁ ++ (y , e) ∷ r₂ → Carried e → ¬ Ex [ p ] y
               → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
  cold-shut    : ∀ m {Δ A} (c : Timeline A) (env : DenEnv Δ) p {rs} → Met (enter (ev m (coldˢ c) env) p) rs → ShutRun rs
  cold-idle    : ∀ m {Δ A} (c : Timeline A) (env : DenEnv Δ) p → Idle (enter (ev m (coldˢ c) env) p)
  -- A cold step's rows past its over are finitely many.
  cold-rest    : ∀ m {Δ A} (c : Timeline A) (env : DenEnv Δ) p → Rest (enter (ev m (coldˢ c) env) p)

private
  same-≺ : ∀ i x y → T (isLt (cmpPath x y)) → (i ∙ x) ≺ (i ∙ y)
  same-≺ i x y h rewrite reflⁱ i = h

-- WHAT EACH ROW OF THE COLD HOLDS, read off its shape.
module ColdHeld {A : Set} (p : Pos) (t : EmissionSet (IE A)) (row : ∀ {y e} → t y e → Visible e → ColdRow p y e) where

  named : ∀ {y n} → t y (out (instEmit (mark begin) n)) → n ≡ nameOf y
  named x with row x tt
  ... | step-begin = refl

  routing : ∀ {y m n} → t y (out (instEmit (mark m) n)) → Routing m
  routing x with row x tt
  ... | step-begin = r-begin
  ... | step-over  = r-over

  early : Early p → ∀ {y a n} → t y (out (instEmit (value a) n)) → Early y
  early ep x with row x tt
  ... | now-value zs = early-inst zs ep
  ... | step-value {t} {e} {i} = λ _ → same-≺ (cascade t e (ix i)) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ []) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ []) tt , λ { (_ , ()) }

  ends : Early p → ∀ {y} → t y end → Early y
  ends ep x with row x tt
  ... | now-end zs = early-inst zs ep
  ... | step-end   = λ ()

  late : ∀ {y n} → t y (out (instEmit (mark over) n)) → Valued (rootOf y) × opos (rootOf y) ⊑ y
  late x with row x tt
  ... | step-over = valued , [] , refl

  no-stop : ∀ {y n} → t y (out (instEmit (mark stop) n)) → ⊥
  no-stop x with row x tt
  ... | ()

held-cold : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (c : Timeline A) → IH m ρ (cold c)
held-cold m ρ c = ih λ env cs g eh p ok ep →
  let open ColdHeld p (enter (ev m (elab ρ (cold c)) env) p) (cold-rows m c env p) in
  held-runs named routing (early ep) (ends ep) late (cold-idle m c env p) (cold-rest m c env p) λ mt → record
    { covered = λ r₁ r₂ eq cr ne → cold-covered m c env p mt r₁ r₂ eq cr λ { (here s) → ne (here s) ; (there ()) }
    ; exact   = λ r₁ r₂ eq → ⊥-elim (no-stop (proj₁ (run-row r₁ (subst (Met _) eq mt))))
    ; shut    = cold-shut m c env p mt }

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

-- EVERY HANG SHOWS: past a position, a reader reaching few rows before
-- it finds few rows there, for every size of the reach.
shows-ev : ∀ m {Δ X} (A′ : Obs Timeline Δ X) (env : DenEnv Δ) → GoodEnv env → ∀ p → Ok (Hots env) p
         → Shows (enter (ev m A′ env) p)
shows-ev nothing  A′ env g p ok = k-shows λ n → sk-⟦⟧ n A′ env g p ok
shows-ev (just k) A′ env g p ok = k-shows λ n → sk-approx n k A′ env g p ok

-- A connect shows its body, read over its source made hot.
conn-ev : ∀ m {Δ X B} (A′ : Obs Timeline Δ X) (B′ : Obs Timeline (X ∷ Δ) (IE B)) (env : DenEnv Δ) cs → GoodEnv env
        → ∀ p → Ok (Hots env) p → Early p
        → (Lawful (Proper (enter (ev m A′ env) (p ⊕ [ ix 1 ])))
           → Ok (Hots env ∪ʰ Proper (enter (ev m A′ env) (p ⊕ [ ix 1 ]))) (p ⊕ [ ix 0 ]) → Early (p ⊕ [ ix 0 ])
           → Held (enter (ev m B′ (hot (Proper (enter (ev m A′ env) (p ⊕ [ ix 1 ]))) ∷ env)) (p ⊕ [ ix 0 ])) ((p ⊕ [ ix 0 ]) ∷ p ∷ cs))
        → Held (enter (ev m (connect A′ B′) env) p) (p ∷ cs)
conn-ev nothing A′ B′ env cs g p ok ep k =
  held-conn (⟦ A′ ⟧ env) (λ h → ⟦ B′ ⟧ (h ∷ env)) Is IF p ok cs (shows-ev nothing A′ env g (p ⊕ [ ix 1 ]) (ok-step p ok))
    (k (src-lawful {s = ⟦ A′ ⟧ env} {F = λ h → ⟦ B′ ⟧ (h ∷ env)} Is IF p ok) (body-ok {s = ⟦ A′ ⟧ env} {F = λ h → ⟦ B′ ⟧ (h ∷ env)} Is IF p ok)
       (early-inst [ ix 0 ] ep))
  where
    Is = inv-⟦⟧ A′ env g
    IF : ∀ {t} → Lawful t → InvD (Hots env ∪ʰ t) (⟦ B′ ⟧ (hot t ∷ env))
    IF L = inv-⟦⟧ B′ (hot _ ∷ env) (good-cons L g)
conn-ev (just n) A′ B′ env cs g p ok ep k =
  held-conn (approx n A′ env) (λ h → approx n B′ (h ∷ env)) Is IF p ok cs (shows-ev (just n) A′ env g (p ⊕ [ ix 1 ]) (ok-step p ok))
    (k (src-lawful {s = approx n A′ env} {F = λ h → approx n B′ (h ∷ env)} Is IF p ok)
       (body-ok {s = approx n A′ env} {F = λ h → approx n B′ (h ∷ env)} Is IF p ok)
       (early-inst [ ix 0 ] ep))
  where
    Is = inv-approx n A′ env g
    IF : ∀ {t} → Lawful t → InvD (Hots env ∪ʰ t) (approx n B′ (hot t ∷ env))
    IF L = inv-approx n B′ (hot _ ∷ env) (good-cons L g)

held-connect : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B)
             → IH m ρ s → (∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE (A ∷ Γ) → X ∈ Δ′) → IH m ρ′ b) → IH m ρ (connect s b)
held-connect m ρ s b (ih hs) hb = ih λ env cs g eh p ok ep →
  conn-ev m (annotate (elab ρ s)) _ env cs g p ok ep λ L ok₀ ep₀ →
    IH.holds (hb _) _ (p ∷ cs) (good-cons L g)
      (λ { (here refl) → record { m = m ; src = elab ρ s ; env = env ; at = p ; outer = cs ; held = hs env cs g eh
                                ; under = λ i → i ; is = refl }
         ; (there i)   → widen (eh i) })
      (p ⊕ [ ix 0 ]) ok₀ ep₀

-- A FLATMAP'S SCAN HOLDS, read past the three connects that share its
-- outer: the outer at `p ⊕ [ ix 1 ]`, the closer, then the real
-- flatMap, each made hot.  What it reads: the connects in scope, the
-- outer, the lanes and the closer.
-- A source read while its items go on passes no `nothing`, under the
-- meaning and every approximant.
ev-none : ∀ m {Γ X} (s : Obs Timeline Γ (Maybe X)) (env : DenEnv Γ) P {q}
        → enter (ev m (takeWhile false going s) env) P q (out nothing) → ⊥
ev-none nothing  s env P (TakeWhile.pass _ () _ , _)
ev-none nothing  s env P (TakeWhile.fail _ _ _ () , _)
ev-none (just n) s env P (TakeWhile.pass _ () _ , _)
ev-none (just n) s env P (TakeWhile.fail _ _ _ () , _)

module FlatHots (m : Maybe ℕ) {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (op : FlatOp) (f : A → Obs Timeline Γ B)
                (s : Obs Timeline Γ A) (env : DenEnv Δ) (p : Pos) where

  g : A → Obs Timeline (IE B ∷ IE A ∷ Δ) (IE B)
  g a = elab (λ i → there (there (ρ i))) (f a)

  tk : Obs Timeline (IE B ∷ IE B ∷ IE A ∷ Δ) (ℕ × Routes)
  tk = trackers Γ 0 (λ i → there (there (there (ρ i))))

  real : Obs Timeline (IE B ∷ IE A ∷ Δ) (IE B)
  real = flatMap op (λ a → laneˢ (g a)) (each valuesOf (connected (there (here refl))))

  p₀ p₀₀ : Pos
  p₀  = p ⊕ [ ix 0 ]
  p₀₀ = p₀ ⊕ [ ix 0 ]

  σ₁ : EmissionSet (IE A)
  σ₁ = Proper (enter (ev m (elab ρ s) env) (p ⊕ [ ix 1 ]))

  σ₂ : EmissionSet (IE B)
  σ₂ = Proper (enter (ev m closer (hot σ₁ ∷ env)) (p₀ ⊕ [ ix 1 ]))

  σ₃ : EmissionSet (IE B)
  σ₃ = Proper (enter (ev m real (hot σ₂ ∷ hot σ₁ ∷ env)) (p₀₀ ⊕ [ ix 1 ]))

  env′ : DenEnv (IE B ∷ IE B ∷ IE A ∷ Δ)
  env′ = hot σ₃ ∷ hot σ₂ ∷ hot σ₁ ∷ env

  P : Pos
  P = p₀₀ ⊕ [ ix 0 ]

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

-- Past its over, a step is as late.
late-ext : ∀ {q} zs → Valued (rootOf q) × opos (rootOf q) ⊑ q
         → Valued (rootOf (q ⊕ zs)) × opos (rootOf (q ⊕ zs)) ⊑ (q ⊕ zs)
late-ext {q} zs (v , o) = subst (λ I → Valued I × opos I ⊑ (q ⊕ zs)) (sym (rootOf-ext q zs)) (v , ⊑-trans o (zs , refl))

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
               (p : Pos) (ok : Ok (Hots env) p) (ep : Early p)
               (L₁ : Lawful (FlatHots.σ₁ m ρ op f s env p)) (L₂ : Lawful (FlatHots.σ₂ m ρ op f s env p))
               (L₃ : Lawful (FlatHots.σ₃ m ρ op f s env p))
               (ok₁ : Ok (Hots (hot (FlatHots.σ₁ m ρ op f s env p) ∷ env)) (FlatHots.p₀ m ρ op f s env p))
               (ok₂ : Ok (Hots (hot (FlatHots.σ₂ m ρ op f s env p) ∷ hot (FlatHots.σ₁ m ρ op f s env p) ∷ env)) (FlatHots.p₀₀ m ρ op f s env p))
               (ok₃ : Ok (Hots (FlatHots.env′ m ρ op f s env p)) (FlatHots.P m ρ op f s env p))
               (ep₃ : Early (FlatHots.P m ρ op f s env p)) where
  open FlatHots m ρ op f s env p

  -- Where a branch's reader ends: past its source's end.
  data BEnd : Pos → Set where
    b-outer : ∀ {c w} → σ₁ c end → BEnd (c ⊕ [ sub w ])
    b-lane  : ∀ {c w} → σ₃ c end → BEnd (c ⊕ [ sub w ])
    b-close : ∀ {c w} → σ₂ c end → BEnd (c ⊕ [ sub w ])

  data MRow : Pos → Ev (Maybe (Input B)) → Set where
    tracker : ∀ {q x} → MRow q (out (just (inj₂ x)))
    outer   : ∀ {q w x y} → σ₁ q (out x) → opening x ≡ y → MRow (q ⊕ [ sub w ]) (out (just (inj₁ (outerB , y))))
    lane    : ∀ {q w x} → σ₃ q (out x) → MRow (q ⊕ [ sub w ]) (out (just (inj₁ (laneB , x))))
    close   : ∀ {q w x} → σ₂ q (out x) → MRow (q ⊕ [ sub w ]) (out (just (inj₁ (closeB , x))))
    under   : ∀ {zs} → MRow (P ⊕ zs) end
    done    : ∀ {c zs} → BEnd c → MRow (c ⊕ zs) end

  postulate
    -- WHAT EACH BRANCH SENT, row by row: a row of the outer, the closer or
    -- the lanes, one `sub` below where that branch shows it.
    outer-sent : ∀ {q y} → M q (out (just (inj₁ (outerB , y))))
               → Σ Pos λ c → Σ Pos λ w → Σ (IE A) λ x → σ₁ c (out x) × opening x ≡ y × q ≡ c ⊕ [ sub w ]
    lane-sent  : ∀ {q x} → M q (out (just (inj₁ (laneB , x)))) → Σ Pos λ c → Σ Pos λ w → σ₃ c (out x) × q ≡ c ⊕ [ sub w ]
    close-sent : ∀ {q x} → M q (out (just (inj₁ (closeB , x)))) → Σ Pos λ c → Σ Pos λ w → σ₂ c (out x) × q ≡ c ⊕ [ sub w ]
    -- The source ends under its own subscription, or past a branch's end.
    m-ends     : ∀ {q} → M q end → (Σ _ λ zs → q ≡ P ⊕ zs) ⊎ (Σ Pos λ c → Σ _ λ zs → BEnd c × q ≡ c ⊕ zs)

  -- Every row the scan's source meets is one of these.
  m-rows : ∀ {q e} → M q e → Visible e → MRow q e
  m-rows {e = out (just (inj₂ _))} _ _ = tracker
  m-rows {e = out (just (inj₁ (outerB , _)))} x _ with outer-sent x
  ... | _ , _ , _ , y , o , refl = outer y o
  m-rows {e = out (just (inj₁ (laneB , _)))} x _ with lane-sent x
  ... | _ , _ , y , refl = lane y
  m-rows {e = out (just (inj₁ (closeB , _)))} x _ with close-sent x
  ... | _ , _ , y , refl = close y
  m-rows {e = out nothing} x _ = ⊥-elim (ev-none m _ env′ P x)
  m-rows {e = end} x _ with m-ends x
  ... | inj₁ (_ , refl)     = under
  ... | inj₂ (_ , _ , b , refl) = done b

  postulate
    -- The lanes' rows: begins named for their instants, values before
    -- their over, overs at it.
    lane-named  : ∀ {q n} → σ₃ q (out (instEmit (mark begin) n)) → n ≡ nameOf q
    lane-early  : ∀ {q a n} → σ₃ q (out (instEmit (value a) n)) → Early q
    lane-late   : ∀ {q n} → σ₃ q (out (instEmit (mark over) n)) → Valued (rootOf q) × opos (rootOf q) ⊑ q
    close-marks : ∀ {q x} → σ₂ q (out x) → Closing x
    -- A lane's and the closer's ends lie before their step's over.
    lane-ends   : ∀ {q} → σ₃ q end → Early q
    close-ends  : ∀ {q} → σ₂ q end → Early q

  cs′ : List Pos
  cs′ = P ∷ p₀₀ ∷ p₀ ∷ p ∷ cs

  -- THE SCAN'S COUNTERS TRACK THE BRANCHES, row by row of a run met:
  -- the routes open at a row are of its instant; a value read, a live
  -- over read, and the end find one open unless exempt; and a dead
  -- instant stays dead.
  postulate
    -- THE SCAN'S COUNTERS ARE OF THE ROW'S INSTANT, OR NONE, counter by
    -- counter: the outer's routes, the lanes', those an ended lane hands
    -- a queued lane's burst, and those parked on a connect in scope.
    outer-current  : ∀ rx₁ {q e rx₂} → Met M (rx₁ ++ (q , e) ∷ rx₂) → Visible e
                   → Flat.outer (proj₁ (past op init rx₁)) ≡ 0 ⊎ Flat.at (proj₁ (past op init rx₁)) ≡ nameOf q
    held-current   : ∀ rx₁ {q e rx₂} → Met M (rx₁ ++ (q , e) ∷ rx₂) → Visible e
                   → Flat.held (proj₁ (past op init rx₁)) ≡ 0 ⊎ Flat.at (proj₁ (past op init rx₁)) ≡ nameOf q
    value-open    : ∀ rx₁ {q b a n rx₂} → Met M (rx₁ ++ (q , out (just (inj₁ (b , instEmit (value a) n)))) ∷ rx₂) → ¬ Ex cs′ q
                  → Σ ℕ λ k → proj₂ (from r₀ (outRows op init rx₁)) ≡ suc k
    over-open     : ∀ rx₁ {q b n rx₂} → Met M (rx₁ ++ (q , out (just (inj₁ (b , instEmit (mark over) n)))) ∷ rx₂)
                  → Flat.spent (proj₁ (past op init rx₁)) ≡ false → ¬ Ex cs′ q
                  → Σ ℕ λ k → proj₂ (from r₀ (outRows op init rx₁)) ≡ suc k
    end-open      : ∀ rx₁ {q rx₂} → Met M (rx₁ ++ (q , end) ∷ rx₂) → ¬ Ex cs′ q
                  → Σ ℕ λ k → from r₀ (outRows op init rx₁) ≡ (nameOf q , suc k)
    comb-shut     : ∀ {rx} → Met M rx → ShutRun (outRows op init rx)
    -- IDLE BETWEEN ROWS: where a reader of the scan waits on nothing before
    -- a position few rows precede, the routes it counts are of that
    -- position's instant, or none.
    scan-idle     : Idle scanned
    -- PAST A ZERO COUNT THE SCAN FINISHES THE INSTANT: once its count holds
    -- no route of the instant last begun, finitely many rows of it follow,
    -- outer, branches and trackers together.
    scan-rest     : Rest scanned

  -- THE LANES' BRANCH OF THE SCAN'S SOURCE: a lane's row, where the lanes
  -- show it.
  laneTag : Ev (Maybe (Input B)) → Maybe (Ev (IE B))
  laneTag (out (just (inj₁ (laneB , x)))) = just (out x)
  laneTag _                              = nothing

  lane-vals : ∀ {e e′} → laneTag e ≡ just e′ → Σ (IE B) λ x → e′ ≡ out x
  lane-vals {out (just (inj₁ (laneB , x)))}  refl = x , refl
  lane-vals {out (just (inj₁ (outerB , _)))} ()
  lane-vals {out (just (inj₁ (closeB , _)))} ()
  lane-vals {out (just (inj₂ _))}            ()
  lane-vals {out nothing}                    ()
  lane-vals {skip}                           ()
  lane-vals {pin _}                          ()
  lane-vals {end}                            ()

  postulate
    -- The lanes' rows a run of the source met are a run of the lanes.
    lane-run    : ∀ {rx} → Met M rx → Σ _ λ rs → Proj laneTag rx rs × Met σ₃ rs
    -- What the lanes tell of past those rows lies no earlier than the
    -- source's next row: no source row lies under a lane's row.
    lane-next   : ∀ rx₁ {q e rx₂ rs} → Met M (rx₁ ++ (q , e) ∷ rx₂) → Visible e → Proj laneTag rx₁ rs
                → Few σ₃ q × After (cursor nothing rs) q
                × (∀ {y e′} → σ₃ y e′ → Visible e′ → After (cursor nothing rs) y → q ≼ y)
    -- The lanes keep no route past its instant.
    lane-idle   : Idle σ₃
    -- THE LANES' COUNTER IS THE LANES' COUNT: none, or of the name the
    -- lanes last began, with a route of it open.  A begin past the
    -- instant's over counts there and not here, and a lane's end hands
    -- its routes on, so the counter is at most the count.
    lanes-count : ∀ {rx rs} → Met M rx → Proj laneTag rx rs
                → Flat.lanes (proj₁ (past op init rx)) ≡ 0
                ⊎ Flat.at (proj₁ (past op init rx)) ≡ proj₁ (cnt rs) × Σ ℕ λ k → proj₂ (cnt rs) ≡ suc k

  lanes-current : ∀ rx₁ {q e rx₂} → Met M (rx₁ ++ (q , e) ∷ rx₂) → Visible e
                → Flat.lanes (proj₁ (past op init rx₁)) ≡ 0 ⊎ Flat.at (proj₁ (past op init rx₁)) ≡ nameOf q
  lanes-current rx₁ mt v with lane-run (run-prefix rx₁ mt)
  ... | rs , pr , mr with lanes-count (run-prefix rx₁ mt) pr
  ...   | inj₁ z = inj₁ z
  ...   | inj₂ (at≡ , k , open≡) with lane-next rx₁ mt v pr
  ...     | fw , af , least with lane-idle mr (proj-outs lane-vals pr) fw af least
  ...       | inj₁ none = ⊥-elim (0≢1+n (trans (sym none) open≡))
  ...       | inj₂ nm≡  = inj₂ (trans at≡ nm≡)

  postulate
    -- ROUTES PARK ONLY ON A CONNECT HOLDING ONE: a cut parks while a
    -- connect in scope holds a route of the instant, a tracker's row that
    -- leaves none holding stops them, and a new instant starts none.
    parked-live  : ∀ {rx} → Met M rx
                 → Flat.parked (proj₁ (past op init rx)) ≡ 0
                 ⊎ anyHolds (Flat.at (proj₁ (past op init rx))) (Flat.live (proj₁ (past op init rx))) ≡ true
    -- A CONNECT IN SCOPE KEEPS NO ROUTE PAST ITS INSTANT, read at the
    -- scan's rows.  Owed: the run split onto that connect's tracker, and
    -- the binder's own `idle` (`Bound.held`) read through `annotate`.
    live-current : ∀ rx₁ {q e rx₂} → Met M (rx₁ ++ (q , e) ∷ rx₂) → Visible e
                 → anyHolds (Flat.at (proj₁ (past op init rx₁))) (Flat.live (proj₁ (past op init rx₁))) ≡ true
                 → Flat.at (proj₁ (past op init rx₁)) ≡ nameOf q

  parked-current : ∀ rx₁ {q e rx₂} → Met M (rx₁ ++ (q , e) ∷ rx₂) → Visible e
                 → Flat.parked (proj₁ (past op init rx₁)) ≡ 0 ⊎ Flat.at (proj₁ (past op init rx₁)) ≡ nameOf q
  parked-current rx₁ mt v with parked-live (run-prefix rx₁ mt)
  ... | inj₁ z = inj₁ z
  ... | inj₂ h = inj₂ (live-current rx₁ mt v h)

  -- No closer's row begins a route.
  no-cb : ∀ {q n} → MRow q (out (just (inj₁ (closeB , instEmit (mark begin) n)))) → ⊥
  no-cb (close y) = closing-mark (close-marks y) (λ ()) (λ ())

  nocb : ∀ rx₁ {q e rx₂} → Met M (rx₁ ++ (q , e) ∷ rx₂) → ∀ r₁ {q′ x} r₂ → rx₁ ≡ r₁ ++ (q′ , out x) ∷ r₂ → NoCB x
  nocb rx₁ {q} {e} {rx₂} mt r₁ {q′} r₂ refl refl =
    no-cb (m-rows (proj₁ (run-row r₁ (subst (Met M) (++-assoc r₁ ((q′ , _) ∷ r₂) ((q , e) ∷ rx₂)) mt))) tt)

  -- Four counters each of the instant or none: their sum is.
  sum-current : ∀ {X : Set} (a b c d : ℕ) → (a ≡ 0 ⊎ X) → (b ≡ 0 ⊎ X) → (c ≡ 0 ⊎ X) → (d ≡ 0 ⊎ X) → a + b + c + d ≡ 0 ⊎ X
  sum-current .0 .0 .0 .0 (inj₁ refl) (inj₁ refl) (inj₁ refl) (inj₁ refl) = inj₁ refl
  sum-current _ _ _ _ (inj₂ x) _ _ _ = inj₂ x
  sum-current _ _ _ _ (inj₁ _) (inj₂ x) _ _ = inj₂ x
  sum-current _ _ _ _ (inj₁ _) (inj₁ _) (inj₂ x) _ = inj₂ x
  sum-current _ _ _ _ (inj₁ _) (inj₁ _) (inj₁ _) (inj₂ x) = inj₂ x

  flat-current : ∀ rx₁ {q e rx₂} → Met M (rx₁ ++ (q , e) ∷ rx₂) → Visible e
               → tot (proj₁ (past op init rx₁)) ≡ 0 ⊎ Flat.at (proj₁ (past op init rx₁)) ≡ nameOf q
  flat-current rx₁ mt v = sum-current (Flat.outer st) (Flat.lanes st) (Flat.held st) (Flat.parked st)
    (outer-current rx₁ mt v) (lanes-current rx₁ mt v) (held-current rx₁ mt v) (parked-current rx₁ mt v)
    where st = proj₁ (past op init rx₁)

  start-current : ∀ rx₁ {q e rx₂} → Met M (rx₁ ++ (q , e) ∷ rx₂) → Visible e
                → proj₂ (from r₀ (outRows op init rx₁)) ≡ 0 ⊎ proj₁ (from r₀ (outRows op init rx₁)) ≡ nameOf q
  start-current rx₁ mt v with flat-current rx₁ mt v
  ... | inj₁ z = inj₁ (trans (exact-past op rx₁ (nocb rx₁ mt)) z)
  ... | inj₂ a = inj₂ (trans (inv-at (inv-past op rx₁)) a)

  H₁ : Held (enter (ev m (elab ρ s) env) (p ⊕ [ ix 1 ])) ((p ⊕ [ ix 1 ]) ∷ cs)
  H₁ = hs (p ⊕ [ ix 1 ]) (ok-step p ok) (early-inst [ ix 1 ] ep)

  named : ∀ {q b n} → M q (out (just (inj₁ (b , instEmit (mark begin) n)))) → n ≡ nameOf q
  named x with m-rows x tt
  ... | outer {q = c} {w = w} y eq with refl ← open-mark eq (λ ()) =
    trans (Held.named H₁ (proj₁ y)) (cong nm (sym (rootOf-ext c [ sub w ])))
  ... | lane {q = c} {w = w} y  = trans (lane-named y) (cong nm (sym (rootOf-ext c [ sub w ])))
  ... | close y = ⊥-elim (closing-mark (close-marks y) (λ ()) (λ ()))

  early : ∀ {q b a n} → M q (out (just (inj₁ (b , instEmit (value a) n)))) → Early q
  early x with m-rows x tt
  ... | outer y eq = ⊥-elim (open-value eq)
  ... | lane {w = w} y = early-inst [ sub w ] (lane-early y)
  ... | close y = ⊥-elim (closing-value (close-marks y))

  ends : ∀ {q} → M q end → Early q
  ends x with m-rows x tt
  ... | under {zs} = early-inst zs ep₃
  ... | done {zs = zs} b = early-inst zs (bend b)
    where
      bend : ∀ {c} → BEnd c → Early c
      bend (b-outer {w = w} y) = early-inst [ sub w ] (Held.ends H₁ (proj₁ y))
      bend (b-lane {w = w} y)  = early-inst [ sub w ] (lane-ends y)
      bend (b-close {w = w} y) = early-inst [ sub w ] (close-ends y)

  late : ∀ {q b n} → M q (out (just (inj₁ (b , instEmit (mark over) n)))) → Valued (rootOf q) × opos (rootOf q) ⊑ q
  late x with m-rows x tt
  ... | outer {w = w} y eq with refl ← open-mark eq (λ ()) = late-ext [ sub w ] (Held.late H₁ (proj₁ y))
  ... | lane {w = w} y = late-ext [ sub w ] (lane-late y)
  ... | close y = ⊥-elim (closing-mark (close-marks y) (λ ()) (λ ()))

  IM : InvAt (Hots env′) P M
  IM = inv-ev m src env′ (good-cons L₃ (good-cons L₂ (good-cons L₁ gd))) P ok₃

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
          (λ j → rootOf-ext q (ix 1 ∷ ix j ∷ []))

      fin : ∀ rx₁ {q} rx₂ → rx ≡ rx₁ ++ (q , end) ∷ rx₂ → Local cs′ (from r₀ (outRows op init rx₁)) q end
      fin rx₁ rx₂ refl = local-end (end-open rx₁ mt)

  comb : CombIn op M (P ∷ p₀₀ ∷ p₀ ∷ p ∷ cs)
  comb = record { named = named ; early = early ; ends = ends ; late = late ; runs = comb-runs }

------------------------------------------------------------------------
-- The scanned stream

-- WHAT THE SCANNED STREAM MEETS IS LAID OUT FROM WHAT ITS SOURCE MEETS: a
-- run met of it is a prefix of what a run met of the source lays out.
postulate
  comb-run : ∀ m {Γ B} op (s : Obs Timeline Γ (Maybe (Input B))) (ρ : DenEnv Γ) P → GoodEnv ρ → Ok (Hots ρ) P
           → ∀ {rs} → Met (enter (ev m (each proj₂ (scan (react op) init s)) ρ) P) rs
           → Σ _ λ rx → Met (enter (ev m s ρ) P) rx × Σ _ λ ext → rs ++ ext ≡ outRows op init rx

-- What a row shows, it shows whether or not a run is found to meet it.
early-stable : ∀ {y} → ¬ ¬ Early y → Early y
early-stable h v = decidable-stable (T? _) (λ k → h λ e → k (proj₁ (e v))) , λ s → h λ e → proj₂ (e v) s

valued-stable : ∀ {I} → ¬ ¬ Valued I → Valued I
valued-stable {cascade _ _ (ix _) ∙ []}      h = valued
valued-stable {frame ∙ _}                    h = ⊥-elim (h λ ())
valued-stable {cascade _ _ (ix _) ∙ (_ ∷ _)} h = ⊥-elim (h λ ())
valued-stable {cascade _ _ (sub _) ∙ _}      h = ⊥-elim (h λ ())
valued-stable {cascade _ _ last ∙ _}         h = ⊥-elim (h λ ())

late-stable : ∀ {y} → ¬ ¬ (Valued (rootOf y) × opos (rootOf y) ⊑ y) → Valued (rootOf y) × opos (rootOf y) ⊑ y
late-stable {y} h =
  valued-stable (λ k → h λ l → k (proj₁ l)) , inside-⊑ _ y (decidable-stable (T? _) λ k → h λ l → k (⊑-inside (proj₂ l)))

routing-stable : ∀ {m} → ¬ ¬ Routing m → Routing m
routing-stable {begin}      _ = r-begin
routing-stable {stop}       _ = r-stop
routing-stable {over}       _ = r-over
routing-stable {subscribed} _ = r-subscribed
routing-stable {completed}  _ = r-completed
routing-stable {outerOpen}  h = ⊥-elim (h λ ())
routing-stable {outerClose} h = ⊥-elim (h λ ())
routing-stable {laneStart}  h = ⊥-elim (h λ ())
routing-stable {carry}      h = ⊥-elim (h λ ())
routing-stable {laneDone}   h = ⊥-elim (h λ ())
routing-stable {burstEnd}   h = ⊥-elim (h λ ())
routing-stable {outerDone}  h = ⊥-elim (h λ ())

-- THE SCANNED STREAM HOLDS WHAT ITS SOURCE PROMISES: a row it shows is
-- one a run met of the source lays out, a step's output, which is what
-- the step read or a stop, or the source's end.
module Scanned (m : Maybe ℕ) {Γ B} op (s : Obs Timeline Γ (Maybe (Input B))) (ρ : DenEnv Γ) P cs (g : GoodEnv ρ) (ok : Ok (Hots ρ) P)
               (ci : CombIn op (enter (ev m s ρ) P) cs) where
  M = enter (ev m s ρ) P
  S = enter (ev m (each proj₂ (scan (react op) init s)) ρ) P

  IM : InvAt (Hots ρ) P M
  IM = inv-ev m s ρ g P ok

  open Reached (ev m (each proj₂ (scan (react op) init s)) ρ) P (inv-ev m (each proj₂ (scan (react op) init s)) ρ g P ok) using (reach)

  -- A row shown is laid out by a run met of the source, classically.
  met-laid : ∀ {y e} → S y e → Visible e → ¬ ¬ Σ _ λ rx → Met M rx × Laid op init rx y e
  met-laid {y} {e} x vi k = reach x vi λ (rs , mt) → let (rx , mx , ext , eq) = comb-run m op s ρ P g ok mt in
    k (rx , mx , laid-in op init rx (subst ((y , e) ∈_) eq (∈-++⁺ˡ (∈-++⁺ʳ rs (here refl)))))

  named-laid : ∀ {rx y n} → Met M rx → Laid op init rx y (out (instEmit (mark begin) n)) → n ≡ nameOf y
  named-laid mx (laid rx₁ {q = c} {x = x} rx₂ {j = j} refl vi) with react-sent op (past op init rx₁) x vi
  ... | routed _ refl = trans (CombIn.named ci mq) (cong nm (sym (rootOf-ext c (ix 1 ∷ ix j ∷ []))))
    where mq = proj₁ (run-row rx₁ mx)

  routing-laid : ∀ {rx y m n} → Met M rx → Laid op init rx y (out (instEmit (mark m) n)) → Routing m
  routing-laid mx (laid rx₁ {x = x} rx₂ refl vi) with react-sent op (past op init rx₁) x vi
  ... | routed r refl = r
  ... | minted        = r-stop

  early-laid : ∀ {rx y a n} → Met M rx → Laid op init rx y (out (instEmit (value a) n)) → Early y
  early-laid mx (laid rx₁ {x = x} rx₂ {j = j} refl vi) with react-sent op (past op init rx₁) x vi
  ... | passed refl = early-inst (ix 1 ∷ ix j ∷ []) (CombIn.early ci mq)
    where mq = proj₁ (run-row rx₁ mx)

  ends-laid : ∀ {rx y} → Met M rx → Laid op init rx y end → Early y
  ends-laid mx (ended rx₁ rx₂ refl) = CombIn.ends ci (proj₁ (run-row rx₁ mx))

  late-laid : ∀ {rx y n} → Met M rx → Laid op init rx y (out (instEmit (mark over) n)) → Valued (rootOf y) × opos (rootOf y) ⊑ y
  late-laid mx (laid rx₁ {x = x} rx₂ {j = j} refl vi) with react-sent op (past op init rx₁) x vi
  ... | routed _ refl = late-ext (ix 1 ∷ ix j ∷ []) (CombIn.late ci mq)
    where mq = proj₁ (run-row rx₁ mx)

  named : ∀ {y n} → S y (out (instEmit (mark begin) n)) → n ≡ nameOf y
  named x = decidable-stable (_ ≟ᵖ _) λ ng → met-laid x tt λ (_ , mx , l) → ng (named-laid mx l)

  routing : ∀ {y m n} → S y (out (instEmit (mark m) n)) → Routing m
  routing x = routing-stable λ ng → met-laid x tt λ (_ , mx , l) → ng (routing-laid mx l)

  early : ∀ {y a n} → S y (out (instEmit (value a) n)) → Early y
  early x = early-stable λ ng → met-laid x tt λ (_ , mx , l) → ng (early-laid mx l)

  ends : ∀ {y} → S y end → Early y
  ends x = early-stable λ ng → met-laid x tt λ (_ , mx , l) → ng (ends-laid mx l)

  late : ∀ {y n} → S y (out (instEmit (mark over) n)) → Valued (rootOf y) × opos (rootOf y) ⊑ y
  late x = late-stable λ ng → met-laid x tt λ (_ , mx , l) → ng (late-laid mx l)

  runs : ∀ {rs} → Met S rs → RunHeld cs rs
  runs mt with comb-run m op s ρ P g ok mt
  ... | rx , mx , ext , eq = runs-prefix ext (subst (RunHeld cs) (sym eq) (CombIn.runs ci mx))

comb-held : ∀ m {Γ B} op (s : Obs Timeline Γ (Maybe (Input B))) (ρ : DenEnv Γ) P cs → GoodEnv ρ → Ok (Hots ρ) P
          → CombIn op (enter (ev m s ρ) P) cs → Idle (enter (ev m (each proj₂ (scan (react op) init s)) ρ) P)
          → Rest (enter (ev m (each proj₂ (scan (react op) init s)) ρ) P)
          → Held (enter (ev m (each proj₂ (scan (react op) init s)) ρ) P) cs
comb-held m op s ρ P cs g ok ci id re = held-runs named routing early ends late id re runs
  where open Scanned m op s ρ P cs g ok ci

held-comb : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) s
            (env : DenEnv Δ) cs → GoodEnv env → EnvHeld ρ env cs → HeldD (Hots env) (ev m (elab ρ s) env) cs
          → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ (f a))
          → ∀ p → Ok (Hots env) p → Early p
          → let open FlatHots m ρ op f s env p in
            Lawful σ₁ → Lawful σ₂ → Lawful σ₃ → Ok (Hots (hot σ₁ ∷ env)) p₀ → Ok (Hots (hot σ₂ ∷ hot σ₁ ∷ env)) p₀₀ → Ok (Hots env′) P → Early P
          → Held scanned (P ∷ p₀₀ ∷ p₀ ∷ p ∷ cs)
held-comb m ρ op f s env cs gd eh hs hf p ok ep L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃ =
  comb-held m op src env′ P _ (good-cons L₃ (good-cons L₂ (good-cons L₁ gd))) ok₃
    (CombSrc.comb m ρ op f s env cs gd eh hs hf p ok ep L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃)
    (CombSrc.scan-idle m ρ op f s env cs gd eh hs hf p ok ep L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃)
    (CombSrc.scan-rest m ρ op f s env cs gd eh hs hf p ok ep L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃)
  where open FlatHots m ρ op f s env p using (src; env′; P)

held-flatMap : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) s → IH m ρ s
             → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ (f a)) → IH m ρ (flatMap op f s)
held-flatMap m ρ op f s (ih hs) hf = ih λ env cs g eh p ok ep →
  conn-ev m (elab ρ s) _ env cs g p ok ep λ L₁ ok₁ ep₁ →
    conn-ev m closer _ _ (p ∷ cs) (good-cons L₁ g) (p ⊕ [ ix 0 ]) ok₁ ep₁ λ L₂ ok₂ ep₂ →
      conn-ev m (FlatHots.real m ρ op f s env p) _ _ ((p ⊕ [ ix 0 ]) ∷ p ∷ cs) (good-cons L₂ (good-cons L₁ g))
        ((p ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ok₂ ep₂ λ L₃ ok₃ ep₃ →
        held-comb m ρ op f s env cs g eh (hs env cs g eh) hf p ok ep L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃

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
  held-top : ∀ {A} (o : SObs [] A) → IH nothing (λ i → i) (plain o) → Held (elaborated o) (root ∷ [])

held : ∀ {A} (o : SObs [] A) → Held (elaborated o) (root ∷ [])
held o = held-top o (held-⟦⟧ (λ i → i) (plain o))

-- The elaborated program's instants stay dead.
shut : ∀ {A : Set} (o : SObs [] A) → Shut (elaborated o)
shut o = Held.shut (held o)
