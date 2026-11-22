{-# OPTIONS --guardedness #-}

-- THE HELD INDUCTION'S PARTS: its hypothesis, the leaves, the one-input
-- operators, the connects, and the hots a flatMap's scan reads past.
module simultaneous.HeldBase where

open import Data.List using (List; []; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (lookup; _∷_) renaming ([] to []ᵉ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Obs; FlatOp; mergeᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; last; _⊕_; cascade)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Den; hot; enter; Proper; ⟦_⟧; DenEnv; approx; Few)
open import simultaneous.SObs using (lone; Part; ext; module Elaborate)
open import simultaneous.Routed using (Held; HeldD; Early)
open import simultaneous.HeldIn using (HeldIn; held-in)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Shows)
open import simultaneous.HeldMap using (held-map-den)
open import simultaneous.HeldScan using (held-scan-den)
open import simultaneous.HeldTake using (held-take-den)
open import simultaneous.CombSent using (src-op; own-op; cat-op; tag-op; no-track; no-close; tag-branch; Cat-of; Tag; sent-branch; Closing; closing-mark; closing-value; closer-marks; closer-good; src-where; Where) renaming (under to w-under; past to w-past)
open import denotation.EmissionSet using (map-end) renaming (ended to r-ended; late to r-late; shown to r-shown)
open import simultaneous.HeldConnect using (held-conn; early-inst; Tracks)
open import denotation.Laws using (inv-⟦⟧; inv-approx; good-cons)
open import denotation.Laws.Worlds using (Ok; InvD; Lawful; _∪ʰ_)
open import denotation.Laws.Connect using () renaming (lawful to src-lawful; ok₀ to body-ok)
open import denotation.Laws.Shows using (k-shows)
open import denotation.Laws.ShowsEv using (sk-⟦⟧; sk-approx)
open import Data.Empty using (⊥)
open import Data.List.Relation.Unary.Any using (here; there)
open import simultaneous.InstEmit using (begin; valuesOf)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; count; elab; srcLane; laneSrc; annotate; marked; trackers; closer; combined; laneˢ; each; coldˢ;
  Input; react; going; fed; opening; anyHolds; branch; restamp; wrapped)
open import simultaneous.HeldComb using (ev; RunHeld; run-row; held-runs)
open import simultaneous.Routed using (valued; Rest; Routing; r-begin; r-over)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ)
open import denotation.Laws.Worlds using (⊑-inside)
open import simultaneous.InstEmit using (stop; completed)
open import simultaneous.Shut using (r₀)
open import simultaneous.Routed using (Ex)
import Relation.Nullary as Nl
open import Data.Product using (Σ; proj₂)
open import simultaneous.InstEmit using (instEmit; value; mark; over)
open import simultaneous.Routed using (nameOf; Valued; opos)
open import simultaneous.Layers using (run-tail) renaming (run-row to run-row∈)
open import simultaneous.Readings using (rootOf)
open import simultaneous.ColdFew using (cold-step-few; of-below)
open import simultaneous.Relations using (Met)
open import simultaneous.HeldConnect using (rootOf-ext)
open import denotation.Read using (Visible)
open import denotation.EmissionSet using (out; end)
open import denotation.Laws.Worlds using (ok-step; _⊑_)
open import Data.Sum using (inj₁)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (sym; cong; subst)
open import Tree using (mergeᶠ)
open import Data.Bool using (true; false)
open import denotation.EmissionSet using (module TakeWhile)
open import denotation.Read using (Run)
import denotation.Read as Run
open import Data.Bool using (Bool)
open import denotation.Position using (Path)
open import denotation.EmissionSet using (InE; at-end; at-out; on-out)
open import denotation.Events using (ofᴱ)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import simultaneous.HeldComb using (RunHeld)
open import simultaneous.ColdShape using (ColdRow; now-value; now-end; step-begin; step-value; step-over; step-end; cold-rows)
open import simultaneous.ColdBegin using (same-≺)
open import simultaneous.ColdRuns using (quiet-fold; cold-covered; cold-shut)
open import simultaneous.ColdIdle using (cold-idle)

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
    good  : GoodEnv env
    ok    : Ok (Hots env) at
    ep    : Early at
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

-- A STREAM OF ITS SUBSCRIBE BURST ALONE HOLDS: every row it shows lies
-- below its subscription, in its instant, and none is a mark.
module Quiet {A : Set} (t : EmissionSet (IE A)) (p : Pos) (cs : List Pos) (ep : Early p)
             (below : ∀ {y e} → t y e → Visible e → Σ Path λ zs → y ≡ p ⊕ zs)
             (no-mark : ∀ {y m n} → t y (out (instEmit (mark m) n)) → ⊥) where

  in-burst : ∀ {y e} → t y e → Visible e → Ex (p ∷ cs) y
  in-burst x v with below x v
  ... | zs , refl = here (⊑-inside {p} {p ⊕ zs} (zs , refl) , rootOf-ext p zs)

  runs : ∀ {rs} → Met t rs → RunHeld (p ∷ cs) rs
  runs {rs} mt = record
    { covered = λ r₁ r₂ eq _ ne → let (x , v) = run-row r₁ (subst (Met t) eq mt) in ⊥-elim (ne (in-burst x v))
    ; exact   = λ r₁ r₂ eq → ⊥-elim (no-mark (proj₁ (run-row r₁ (subst (Met t) eq mt))))
    ; shut    = λ r₁ r₂ eq _ bq _ _ → ⊥-elim (no-mark (proj₁ (run-row∈ mt (subst (_ ∈_) (sym eq) (∈-++⁺ˡ bq))))) }

  held : Held t (p ∷ cs)
  held = held-runs (λ x → ⊥-elim (no-mark x)) (λ x → ⊥-elim (no-mark x)) early ends (λ x → ⊥-elim (no-mark x)) (λ x → ⊥-elim (no-mark x))
    (λ mt _ _ _ _ → inj₁ (cong proj₂ (quiet-fold {A} r₀ _ (λ i → no-mark (proj₁ (run-row∈ mt i))))))
    (λ mt _ bq → ⊥-elim (no-mark (proj₁ (run-row∈ mt bq))))
    runs
    where
      early : ∀ {y a n} → t y (out (instEmit (value a) n)) → Early y
      early x with below x tt
      ... | zs , refl = early-inst zs ep
      ends : ∀ {y} → t y end → Early y
      ends x with below x tt
      ... | zs , refl = early-inst zs ep

-- The rows of `of` and of `empty`.
of-vals : ∀ {X} p i (ys : List X) {y v} → InE (ofᴱ p i ys) y (out v) → v ∈ ys
of-vals p i (_ ∷ ys) at-out     = here refl
of-vals p i (_ ∷ ys) (on-out r) = there (of-vals p (suc i) ys r)

of-mark : ∀ {X} p (xs : List X) {y m n} → InE (ofᴱ p 0 (L.map (λ x → instEmit (value x) root) xs)) y (out (instEmit (mark m) n)) → ⊥
of-mark p xs r with ∈-map⁻ (λ x → instEmit (value x) root) (of-vals p 0 _ r)
... | _ , _ , ()

-- An `empty` makes one row.
empty-few : ∀ m {Δ} (env : DenEnv Δ) q → Σ (List Pos) λ ks → ∀ {k e} → enter (ev m (empty {A = ⊤}) env) q k e → k ∈ ks
empty-few nothing  env q = [ q ⊕ [ last ] ] , λ { (at-end , _) → here refl }
empty-few (just n) env q = [ q ⊕ [ last ] ] , λ { (at-end , _) → here refl }

held-empty : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → IH m ρ (empty {A = A})
held-empty nothing  ρ = ih λ env cs g eh p ok ep → Quiet.held _ p cs ep (λ { (at-end , _) _ → [ last ] , refl }) λ { (() , _) }
held-empty (just n) ρ = ih λ env cs g eh p ok ep → Quiet.held _ p cs ep (λ { (at-end , _) _ → [ last ] , refl }) λ { (() , _) }

held-of : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (xs : L.List A) → IH m ρ (of xs)
held-of nothing  ρ xs = ih λ env cs g eh p ok ep →
  Quiet.held _ p cs ep (λ (x , _) _ → of-below p 0 _ x) λ (x , _) → of-mark p xs x
held-of (just n) ρ xs = ih λ env cs g eh p ok ep →
  Quiet.held _ p cs ep (λ (x , _) _ → of-below p 0 _ x) λ (x , _) → of-mark p xs x

-- So past a zero count, the instant last begun has finitely many rows left.
cold-rest : ∀ m {Δ A} (c : Timeline A) (env : DenEnv Δ) p → Rest (enter (ev m (coldˢ c) env) p)
cold-rest m c env p mt _ bq with cold-step-few m c env p (proj₁ (run-row∈ mt bq))
... | ks , h = ks , λ xy _ ry → h xy ry

-- WHAT EACH ROW OF THE COLD HOLDS, read off its shape.
module ColdHeld {A : Set} (p : Pos) (t : EmissionSet (IE A)) (row : ∀ {y e} → t y e → Visible e → ColdRow p y e) where

  named : ∀ {y n} → t y (out (instEmit (mark begin) n)) → n ≡ nameOf y
  named x with row x tt
  ... | step-begin _ = refl

  routing : ∀ {y m n} → t y (out (instEmit (mark m) n)) → Routing m
  routing x with row x tt
  ... | step-begin _ = r-begin
  ... | step-over _  = r-over

  early : Early p → ∀ {y a n} → t y (out (instEmit (value a) n)) → Early y
  early ep x with row x tt
  ... | now-value zs = early-inst zs ep
  ... | step-value {t} {e} {i} _ = λ _ → same-≺ (cascade t e (ix i)) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ []) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ []) tt , λ { (_ , ()) }

  ends : Early p → ∀ {y} → t y end → Early y
  ends ep x with row x tt
  ... | now-end zs = early-inst zs ep
  ... | step-end _   = λ ()

  late : ∀ {y n} → t y (out (instEmit (mark over) n)) → Valued (rootOf y) × opos (rootOf y) ⊑ y
  late x with row x tt
  ... | step-over _ = valued , [] , refl

  no-stop : ∀ {y n} → t y (out (instEmit (mark stop) n)) → ⊥
  no-stop x with row x tt
  ... | ()

  done : ∀ {y n} → t y (out (instEmit (mark completed) n)) → Early y
  done x with row x tt
  ... | ()

held-cold : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (c : Timeline A) → IH m ρ (cold c)
held-cold m ρ c = ih λ env cs g eh p ok ep →
  let open ColdHeld p (enter (ev m (elab ρ (cold c)) env) p) (cold-rows m c env p) in
  held-runs named routing (early ep) (ends ep) done late (cold-idle m c env p) (cold-rest m c env p) λ mt → record
    { covered = λ r₁ r₂ eq cr ne → cold-covered m c env p mt r₁ r₂ eq cr λ { (here s) → ne (here s) ; (there ()) }
    ; exact   = λ r₁ r₂ eq → ⊥-elim (no-stop (proj₁ (run-row r₁ (subst (Met _) eq mt))))
    ; shut    = cold-shut m c env p mt }

held-map : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : A → B) s → IH m ρ s → IH m ρ (map f s)
held-map nothing  ρ f s (ih h) = ih λ env cs g eh → held-map-den f (⟦ elab ρ s ⟧ env) cs (h env cs g eh)
held-map (just n) ρ f s (ih h) = ih λ env cs g eh → held-map-den f (approx n (elab ρ s) env) cs (h env cs g eh)

held-takeWhile : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) i (p : A → _) s → IH m ρ s → IH m ρ (takeWhile i p s)
held-takeWhile nothing  ρ i p s (ih h) = ih λ env cs g eh →
  held-take-den i p (⟦ elab ρ s ⟧ env) cs (h env cs g eh) (inv-⟦⟧ (elab ρ s) env g)
held-takeWhile (just n) ρ i p s (ih h) = ih λ env cs g eh →
  held-take-den i p (approx n (elab ρ s) env) cs (h env cs g eh) (inv-approx n (elab ρ s) env g)

held-scan : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : B → A → B) z s → IH m ρ s → IH m ρ (scan f z s)
held-scan nothing  ρ f z s (ih h) = ih λ env cs g eh → held-scan-den f (z , marked begin) (⟦ elab ρ s ⟧ env) cs (h env cs g eh)
held-scan (just n) ρ f z s (ih h) = ih λ env cs g eh → held-scan-den f (z , marked begin) (approx n (elab ρ s) env) cs (h env cs g eh)

-- A binder held under `cs` is held under more.
widen : ∀ {X} {d : Den (AIE X)} {c cs} → Bound d cs → Bound d (c ∷ cs)
widen b = record
  { m = Bound.m b ; src = Bound.src b ; env = Bound.env b ; at = Bound.at b ; outer = Bound.outer b
  ; held = Bound.held b ; good = Bound.good b ; ok = Bound.ok b ; ep = Bound.ep b ; under = λ i → there (Bound.under b i) ; is = Bound.is b }

-- EVERY HANG SHOWS: past a position, a reader reaching few rows before
-- it finds few rows there, for every size of the reach.
shows-ev : ∀ m {Δ X} (A′ : Obs Timeline Δ X) (env : DenEnv Δ) → GoodEnv env → ∀ p → Ok (Hots env) p
         → Shows (enter (ev m A′ env) p)
shows-ev nothing  A′ env g p ok = k-shows λ n → sk-⟦⟧ n A′ env g p ok
shows-ev (just k) A′ env g p ok = k-shows λ n → sk-approx n k A′ env g p ok

-- A connect shows its body, read over its source made hot.
conn-ev : ∀ m {Δ X B} (A′ : Obs Timeline Δ X) (B′ : Obs Timeline (X ∷ Δ) (IE B)) (env : DenEnv Δ) cs → GoodEnv env
        → ∀ p → Ok (Hots env) p → Early p
        → Tracks (Few (enter (ev m A′ env) (p ⊕ [ ix 1 ]))) (enter (ev m A′ env) (p ⊕ [ ix 1 ]))
                 (enter (ev m B′ (hot (Proper (enter (ev m A′ env) (p ⊕ [ ix 1 ]))) ∷ env)) (p ⊕ [ ix 0 ]))
        → (Lawful (Proper (enter (ev m A′ env) (p ⊕ [ ix 1 ])))
           → Ok (Hots env ∪ʰ Proper (enter (ev m A′ env) (p ⊕ [ ix 1 ]))) (p ⊕ [ ix 0 ]) → Early (p ⊕ [ ix 0 ])
           → HeldIn (Few (enter (ev m A′ env) (p ⊕ [ ix 1 ])))
                    (enter (ev m B′ (hot (Proper (enter (ev m A′ env) (p ⊕ [ ix 1 ]))) ∷ env)) (p ⊕ [ ix 0 ])) ((p ⊕ [ ix 0 ]) ∷ p ∷ cs))
        → Held (enter (ev m (connect A′ B′) env) p) (p ∷ cs)
conn-ev nothing A′ B′ env cs g p ok ep tr k =
  held-conn (⟦ A′ ⟧ env) (λ h → ⟦ B′ ⟧ (h ∷ env)) Is IF p ok cs (shows-ev nothing A′ env g (p ⊕ [ ix 1 ]) (ok-step p ok))
    (k (src-lawful {s = ⟦ A′ ⟧ env} {F = λ h → ⟦ B′ ⟧ (h ∷ env)} Is IF p ok) (body-ok {s = ⟦ A′ ⟧ env} {F = λ h → ⟦ B′ ⟧ (h ∷ env)} Is IF p ok)
       (early-inst [ ix 0 ] ep)) tr
  where
    Is = inv-⟦⟧ A′ env g
    IF : ∀ {t} → Lawful t → InvD (Hots env ∪ʰ t) (⟦ B′ ⟧ (hot t ∷ env))
    IF L = inv-⟦⟧ B′ (hot _ ∷ env) (good-cons L g)
conn-ev (just n) A′ B′ env cs g p ok ep tr k =
  held-conn (approx n A′ env) (λ h → approx n B′ (h ∷ env)) Is IF p ok cs (shows-ev (just n) A′ env g (p ⊕ [ ix 1 ]) (ok-step p ok))
    (k (src-lawful {s = approx n A′ env} {F = λ h → approx n B′ (h ∷ env)} Is IF p ok)
       (body-ok {s = approx n A′ env} {F = λ h → approx n B′ (h ∷ env)} Is IF p ok)
       (early-inst [ ix 0 ] ep)) tr
  where
    Is = inv-approx n A′ env g
    IF : ∀ {t} → Lawful t → InvD (Hots env ∪ʰ t) (approx n B′ (hot t ∷ env))
    IF L = inv-approx n B′ (hot _ ∷ env) (good-cons L g)

-- AN ELABORATED BODY EMPTIES ONLY ONCE ITS SOURCE LETS GO OF THE
-- INSTANT: each flatMap of the body watches the connect, parking a route
-- it cuts while the connect's source holds one of the instant.
postulate
  connect-tracks : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B)
                   (env : DenEnv Δ) cs → GoodEnv env → EnvHeld ρ env cs → ∀ p → Ok (Hots env) p → Early p
                 → ∀ {D} → Tracks D (enter (ev m (annotate (elab ρ s)) env) (p ⊕ [ ix 1 ]))
                          (enter (ev m (elab (ext ρ) b) (hot (Proper (enter (ev m (annotate (elab ρ s)) env) (p ⊕ [ ix 1 ]))) ∷ env)) (p ⊕ [ ix 0 ]))

held-connect : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B)
             → IH m ρ s → (∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE (A ∷ Γ) → X ∈ Δ′) → IH m ρ′ b) → IH m ρ (connect s b)
held-connect m ρ s b (ih hs) hb = ih λ env cs g eh p ok ep →
  conn-ev m (annotate (elab ρ s)) _ env cs g p ok ep (connect-tracks m ρ s b env cs g eh p ok ep) λ L ok₀ ep₀ →
    held-in (IH.holds (hb _) _ (p ∷ cs) (good-cons L g)
      (λ { (here refl) → record { m = m ; src = elab ρ s ; env = env ; at = p ; outer = cs ; held = hs env cs g eh
                                ; good = g ; ok = ok ; ep = ep ; under = λ i → i ; is = refl }
         ; (there i)   → widen (eh i) })
      (p ⊕ [ ix 0 ]) ok₀ ep₀)

-- A FLATMAP'S SCAN HOLDS, read past the connects that share its outer:
-- the trigger at `p ⊕ [ ix 1 ]`, the outer as its lane, the closer,
-- then the real flatMap, each made hot.  What it reads: the connects in
-- scope, the outer, the lanes and the closer.
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

  g : A → Part → Bool → Obs Timeline (⊤ ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ) (IE B)
  g a k c = laneSrc (λ i → there (there (there (there (ρ i))))) (f a) k c

  tk : Obs Timeline (IE B ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ) (ℕ × Routes)
  tk = trackers Γ 0 (λ i → there (there (there (there (ρ i)))))

  real : Obs Timeline (IE B ∷ IE A ∷ ⊤ ∷ Δ) (IE B)
  real = flatMap op (λ a → laneˢ (g a)) (each valuesOf (connected (there (here refl))))

  -- The outer, queued past the trigger's lane.
  trig : Obs Timeline (⊤ ∷ Δ) (IE A)
  trig = flatMap (mergeᶠ (just 1)) (λ c → srcLane ρ s c) (of (true ∷ false ∷ []))

  c p₀ p₀₀ : Pos
  c   = p ⊕ [ ix 0 ]
  p₀  = c ⊕ [ ix 0 ]
  p₀₀ = p₀ ⊕ [ ix 0 ]

  σ₀ : EmissionSet ⊤
  σ₀ = Proper (enter (ev m empty env) (p ⊕ [ ix 1 ]))

  env₀ : DenEnv (⊤ ∷ Δ)
  env₀ = hot σ₀ ∷ env

  σ₁ : EmissionSet (IE A)
  σ₁ = Proper (enter (ev m trig env₀) (c ⊕ [ ix 1 ]))

  σ₂ : EmissionSet (IE B)
  σ₂ = Proper (enter (ev m closer (hot σ₁ ∷ env₀)) (p₀ ⊕ [ ix 1 ]))

  -- The real flatMap, read at its connect.
  R : EmissionSet (IE B)
  R = enter (ev m real (hot σ₂ ∷ hot σ₁ ∷ env₀)) (p₀₀ ⊕ [ ix 1 ])

  σ₃ : EmissionSet (IE B)
  σ₃ = Proper R

  env′ : DenEnv (IE B ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ)
  env′ = hot σ₃ ∷ hot σ₂ ∷ hot σ₁ ∷ env₀

  P : Pos
  P = p₀₀ ⊕ [ ix 0 ]

  -- What the scan reads: the connects in scope, then its own branches.
  src : Obs Timeline (IE B ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ) (Maybe (Input B))
  src = takeWhile false going (flatMap (mergeᶠ nothing) (fed tk) (of (true ∷ false ∷ [])))

  scanned : EmissionSet (IE B)
  scanned = enter (ev m (combined op tk) env′) P

  M : EmissionSet (Maybe (Input B))
  M = enter (ev m src env′) P

  -- EACH CONNECT OF THE FLATMAP LETS ITS BODY EMPTY ONLY ONCE ITS SOURCE
  -- IS DONE WITH THE INSTANT: the outer read through the closer and the
  -- real flatMap, the real flatMap's rows read by the scan, which parks
  -- what it cuts while a connect in scope holds a route.
  postulate
    tracks-trig   : ∀ {D} → Tracks D (enter (ev m trig env₀) (c ⊕ [ ix 1 ]))
                           (enter (ev m (connect (closer {B = B}) (connect real (combined op tk))) (hot σ₁ ∷ env₀)) p₀)
    tracks-closer : ∀ {D} → Tracks D (enter (ev m (closer {B = B}) (hot σ₁ ∷ env₀)) (p₀ ⊕ [ ix 1 ]))
                           (enter (ev m (connect real (combined op tk)) (hot σ₂ ∷ hot σ₁ ∷ env₀)) p₀₀)

  -- The scan, read only where the real flatMap has few rows before.
  --
  -- REFUTED: 9e244736 `tracks-real` unrestricted, by a switch whose cut lane loops: the real flatMap never gets past the loop, while the scan reads on in the clairvoyant hot outer, meets an `outerDone` with the completion's route kept, and empties in an instant the real flatMap's rows still fill
  postulate
    tracks-real   : Tracks (Few R) R scanned
