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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import simultaneous.ElabUndone using (Undone; AUndone; EnvU; hot-u; ann-u⟦⟧; ann-uᵃ; elab-undone⟦⟧; elab-undoneᵃ)

open import Tree using (Obs; FlatOp; mergeᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; last; _⊕_; cascade)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Den; hot; enter; Proper; ⟦_⟧; DenEnv; approx; Few)
open import simultaneous.SObs using (lone; Part; ext; module Elaborate)
open import simultaneous.Routed using (Held; HeldD; Early; Placed; PlacedD; Adm; Shown; s-value; s-done; s-end)
open import simultaneous.LaneLocal using (inv-ev; emptyE; of-outer; shown-vis; Fit)
open import simultaneous.CombSent using (hots-at)
open import simultaneous.Layers using (pinby-vis)
open import denotation.Laws.Worlds using (InvAt; W; step; here; inW; plain-ix; plain-last; Plain; ⊑-snoc; ⊑-snoc⁺; ⊑-trans; ⊕-injˡ;
  ⊕-injʳ; ⊕-identityʳ; W⁼; w-up; ⊕-assoc; ∙-inj; ⊑-refl; ⊑-cmp)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All.Properties as AllP
open import denotation.Position using (_∙_)
open import simultaneous.ColdFew using (fresh-past)
open import denotation.EmissionSet using (Ev; module Op; module Connecting)
open import Data.Sum using (_⊎_; inj₂)
open import simultaneous.HeldIn using (HeldIn)
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
open import denotation.Laws.Modulus using (≺-trans; ≺-ext)
open import denotation.EmissionSet using (_≺_)
open import Data.Unit using (⊤; tt)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; count; elab; srcLane; laneSrc; annotate; marked; trackers; closer; combined; laneˢ; each; coldˢ;
  Input; react; going; fed; opening; anyHolds; branch; restamp; wrapped; mapIE; scanIE; passes)
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
open import denotation.Read using (Visible)
open import Data.Sum using (inj₁)
open import Data.Sum using (inj₁)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (sym; cong; subst)
open import Tree using (mergeᶠ)
open import Data.Bool using (true; false)
open import denotation.EmissionSet using (module TakeWhile; module Scan; map-out; map-end)
open import simultaneous.DenRows using (scan-out)
open import Data.Bool using (T; not)
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
-- at `at`, the source holding, every burst it is exempt for one the
-- reader is exempt for too, and the source ending no lane: a binder
-- whose source showed a `laneDone` would put one in a lane's rows that
-- no frame piece sent, so a lane's rows would not be its program's.
record Bound {X : Set} (d : Den (AIE X)) (cs : List Pos) : Set₁ where
  field
    {Θ}   : List Set
    m     : Maybe ℕ
    src   : Obs Timeline Θ (IE X)
    env   : DenEnv Θ
    at    : Pos
    outer : List Pos
    held  : Held (enter (ev m src env) ((at ⊕ [ ix 1 ]) ⊕ [ ix 1 ])) (((at ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ∷ outer)
    good  : GoodEnv env
    undone : Undone (ev m src env)
    ok    : Ok (Hots env) at
    ep    : Early at
    under : ∀ {c} → c ∈ at ∷ outer → c ∈ cs
    is    : d ≡ hot (Proper (enter (ev m (annotate src) env) (at ⊕ [ ix 1 ])))

-- The binder's annotated source, as the connect's source shows it.
Ann : ∀ {X} {d : Den (AIE X)} {cs} → Bound d cs → EmissionSet (AIE X)
Ann b = enter (ev (Bound.m b) (annotate (Bound.src b)) (Bound.env b)) (Bound.at b ⊕ [ ix 1 ])

-- AN ANNOTATED HOT'S LAST GAP: under the queued lane that tells its
-- `nothing`, short of that lane's end.  A reader joined there meets a
-- lone end.
GapIn : ∀ {X} → EmissionSet (AIE X) → Pos → Set
GapIn t y = Σ Pos λ c → Σ Routes λ r → t ((c ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) (out (r , nothing))
          × (c ⊕ [ ix 1 ]) ⊑ y × Nl.¬ (((c ⊕ [ ix 1 ]) ⊕ [ last ]) ⊑ y)

Gap : ∀ {X} {d : Den (AIE X)} {cs} → Bound d cs → Pos → Set
Gap b = GapIn (Ann b)

-- An annotated row a reader's lane can hang on: a value, or the end.
data AShown {X : Set} : Ev (AIE X) → Set where
  a-value : ∀ {r a n} → AShown (out (r , just (instEmit (value a) n)))
  a-end   : AShown end

-- EVERY BINDER IN SCOPE HELD, and no row a reader of one can hang a lane
-- on in any binder's last gap.
record EnvHeld {Γ Δ} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (env : DenEnv Δ) (cs : List Pos) : Set₁ where
  field
    bound : ∀ {X} (i : X ∈ Γ) → Bound (lookup env (ρ (∈-map⁺ AIE i))) cs
    apart : ∀ {X Y} (i : X ∈ Γ) (j : Y ∈ Γ) {y e} → Ann (bound i) y e → AShown e → Nl.¬ Gap (bound j) y

-- An elaborated program ends no lane where its binders end none.
ev-undone : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) (env : DenEnv Δ) → EnvU ρ env → Undone (ev m (elab ρ o) env)
ev-undone nothing  ρ o env eu = elab-undone⟦⟧ ρ o env eu
ev-undone (just n) ρ o env eu = elab-undoneᵃ n ρ o env eu

-- An annotated source ends no lane where the source ends none.
ann-ev : ∀ m {Θ X} (src : Obs Timeline Θ (IE X)) (env : DenEnv Θ) → Undone (ev m src env) → AUndone (ev m (annotate src) env)
ann-ev nothing  src env u = ann-u⟦⟧ src env u
ann-ev (just n) src env u = ann-uᵃ n src env u

-- No binder in scope ends a lane: each annotates a source that ends none.
eh-u : ∀ {Γ Δ} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {env : DenEnv Δ} {cs} → EnvHeld ρ env cs → EnvU ρ env
eh-u eh i = subst AUndone (sym (Bound.is b)) (hot-u (ev (Bound.m b) (annotate (Bound.src b)) (Bound.env b)) (ann-ev (Bound.m b) (Bound.src b) (Bound.env b) (Bound.undone b)))
  where b = EnvHeld.bound eh i

-- Outside every gap of a scope, one binder at a time.
Apart : ∀ (Γ : List Set) → (∀ {X} → X ∈ Γ → Pos → Set) → Pos → Set
Apart []      G y = ⊤
Apart (_ ∷ Γ) G y = Nl.¬ G (here refl) y × Apart Γ (λ {X} i → G {X} (there i)) y

apart-at : ∀ {Γ} {G : ∀ {X} → X ∈ Γ → Pos → Set} {y} → Apart Γ G y → ∀ {X} (i : X ∈ Γ) → Nl.¬ G i y
apart-at (n , _) (here refl) = n
apart-at (_ , a) (there i)   = apart-at a i

apart-all : ∀ {Γ} {G : ∀ {X} → X ∈ Γ → Pos → Set} {y} → (∀ {X} (i : X ∈ Γ) → Nl.¬ G i y) → Apart Γ G y
apart-all {[]}    f = tt
apart-all {_ ∷ Γ} f = f (here refl) , apart-all {Γ} (λ {X} i → f {X} (there i))

-- ADMISSIBLE UNDER THE BINDERS: in no binder's last gap, and past every
-- subscription the binders list.
Fresh : ∀ {Γ Δ} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {env cs} → EnvHeld ρ env cs → Pos → Set
Fresh {Γ} {cs = cs} eh p = Apart Γ (λ {X} i → Gap (EnvHeld.bound eh {X} i)) p × (∀ {c} → c ∈ cs → c ≺ p)

-- A binder's `nothing` row is a hot row: its hot is read past it.
gap-hot : ∀ {Γ Δ} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {env : DenEnv Δ} {cs} (eh : EnvHeld ρ env cs) {X} (i : X ∈ Γ) {n r}
        → Ann (EnvHeld.bound eh i) n (out (r , nothing)) → Hots env n
gap-hot {ρ = ρ} {env} eh i a =
  hots-at env (ρ (∈-map⁺ AIE i)) (Bound.is b) (a , λ ce cq → pinby-vis tt (InvAt.quiet IA ce a cq))
  where
    b  = EnvHeld.bound eh i
    IA = inv-ev (Bound.m b) (annotate (Bound.src b)) (Bound.env b) (Bound.good b) (Bound.at b ⊕ [ ix 1 ]) (ok-step (Bound.at b) (Bound.ok b))

-- A gap is entered at its own second child alone.
gap-bare : ∀ {X} (t : EmissionSet (AIE X)) {q l} → GapIn t (q ⊕ [ l ]) → (l ≡ ix 1 → ⊥) → GapIn t q
gap-bare t {q} (c , r , a , h , ne) nl with ⊑-snoc q h
... | inj₁ h′ = c , r , a , h′ , λ e → ne (⊑-trans e (⊑-snoc⁺ q))
... | inj₂ eq = ⊥-elim (nl (sym (⊕-injʳ c q eq)))

-- A GAP'S OWN SECOND CHILD IS NO ADMISSIBLE POSITION: the `nothing` row
-- below it is a hot row in its world.
fresh-step : ∀ {Γ Δ} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {env : DenEnv Δ} {cs} (eh : EnvHeld ρ env cs) {q}
           → Ok (Hots env) q → Fresh eh q → Fresh eh (q ⊕ [ ix 1 ])
fresh-step eh {q} (_ , dj) (fq , bq) = apart-all (λ i → go i) , λ {c} ci → ≺-trans {c} {q} {q ⊕ [ ix 1 ]} (bq ci) (≺-ext q [])
  where
    go : ∀ {X} (i : X ∈ _) → Nl.¬ Gap (EnvHeld.bound eh i) (q ⊕ [ ix 1 ])
    go i (c , r , a , h , ne) with ⊑-snoc q h
    ... | inj₁ h′ = apart-at fq i (c , r , a , h′ , λ e → ne (⊑-trans e (⊑-snoc⁺ q)))
    ... | inj₂ eq with ⊕-injˡ c q eq
    ...   | refl = dj (gap-hot eh i a) (step (inW (step here plain-ix)) plain-ix) (⊑-inside {(q ⊕ [ ix 1 ]) ⊕ [ ix 0 ]} ([] , sym (⊕-identityʳ _)))

-- Formers keep admissibility under the binders.
fresh-adm : ∀ {Γ Δ} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {env : DenEnv Δ} {cs} (eh : EnvHeld ρ env cs) → Adm (Hots env) (Fresh eh)
fresh-adm eh = record { step = st ; bare = bare ; copy = λ fq → bare fq λ () }
  where
    bare : ∀ {q l} → Fresh eh q → (l ≡ ix 1 → ⊥) → Fresh eh (q ⊕ [ l ])
    bare {q} {l} (fq , bq) nl = apart-all (λ i g → apart-at fq i (gap-bare (Ann (EnvHeld.bound eh i)) g nl))
                              , λ {c} ci → ≺-trans {c} {q} {q ⊕ [ l ]} (bq ci) (≺-ext q [])
    st : ∀ {q l} → Ok _ q → Fresh eh q → Plain l → Fresh eh (q ⊕ [ l ])
    st ok fq (plain-ix {1})             = fresh-step eh ok fq
    st ok fq (plain-ix {0})             = bare fq λ ()
    st ok fq (plain-ix {suc (suc _)})   = bare fq λ ()
    st ok fq plain-last                 = bare fq λ ()

-- Held under every environment of held binders, at every position
-- admissible under them, with every row a lane can hang on admissible.
-- A record, so that a statement about a former is compared by its
-- arguments, never by the elaborated tree its meaning unfolds to.
record IH (m : Maybe ℕ) {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) : Set₁ where
  constructor ih
  field
    holds  : ∀ (env : DenEnv Δ) cs → GoodEnv env → (eh : EnvHeld ρ env cs) → HeldD (Hots env) (Fresh eh) (ev m (elab ρ o) env) cs
    placed : ∀ (env : DenEnv Δ) cs → GoodEnv env → (eh : EnvHeld ρ env cs) → PlacedD (Hots env) (Fresh eh) (ev m (elab ρ o) env)

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
held-empty nothing  ρ = ih (λ env cs g eh p ok fr ep → Quiet.held _ p cs ep (λ { (at-end , _) _ → [ last ] , refl }) λ { (() , _) })
                          λ env cs g eh p ok fr ep → Fit.placed (emptyE nothing env (fresh-adm eh) p ok fr ep)
held-empty (just n) ρ = ih (λ env cs g eh p ok fr ep → Quiet.held _ p cs ep (λ { (at-end , _) _ → [ last ] , refl }) λ { (() , _) })
                          λ env cs g eh p ok fr ep → Fit.placed (emptyE (just n) env (fresh-adm eh) p ok fr ep)

held-of : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (xs : L.List A) → IH m ρ (of xs)
held-of nothing  ρ xs = ih
  (λ env cs g eh p ok fr ep → Quiet.held _ p cs ep (λ (x , _) _ → of-below p 0 _ x) λ (x , _) → of-mark p xs x)
  λ env cs g eh p ok fr ep r sh → proj₂ (proj₂ (of-outer nothing _ env (fresh-adm eh) p ok fr ep)) r (shown-vis sh)
held-of (just n) ρ xs = ih
  (λ env cs g eh p ok fr ep → Quiet.held _ p cs ep (λ (x , _) _ → of-below p 0 _ x) λ (x , _) → of-mark p xs x)
  λ env cs g eh p ok fr ep r sh → proj₂ (proj₂ (of-outer (just n) _ env (fresh-adm eh) p ok fr ep)) r (shown-vis sh)

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
  ... | now-value {l} _ zs = early-inst (l ∷ zs) ep
  ... | step-value {t} {e} {i} _ = λ _ → same-≺ (cascade t e (ix i)) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ []) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ []) tt , λ { (_ , ()) }

  ends : Early p → ∀ {y} → t y end → Early y
  ends ep x with row x tt
  ... | now-end {l} _ zs = early-inst (l ∷ zs) ep
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

-- Down plain steps from a position, the world holds every position or
-- the subscription lies on the way.
w-pre : ∀ {H a} x zs → All Plain zs → W⁼ H a (x ⊕ zs) → W⁼ H a x ⊎ (x ⊑ a × a ⊑ (x ⊕ zs))
w-pre x []       _          w = inj₁ (subst (W⁼ _ _) (⊕-identityʳ x) w)
w-pre x (l ∷ zs) (pl ∷ ps) w with w-pre (x ⊕ [ l ]) zs ps (subst (W⁼ _ _) (sym (⊕-assoc x [ l ] zs)) w)
... | inj₂ (xa , ay) = inj₂ (⊑-trans (⊑-snoc⁺ x) xa , subst (_ ⊑_) (⊕-assoc x [ l ] zs) ay)
... | inj₁ w′ with w-up pl w′
...   | inj₁ eq = inj₂ (subst (x ⊑_) (sym eq) (⊑-snoc⁺ x) , subst (_⊑ (x ⊕ (l ∷ zs))) (sym eq) (zs , sym (⊕-assoc x [ l ] zs)))
...   | inj₂ w″ = inj₁ w″

-- What follows a position on an all-plain path is all plain.
plain-tail : ∀ {i ws} q zs → All Plain ws → (i ∙ ws) ≡ q ⊕ zs → All Plain zs
plain-tail (k ∙ b) zs ps eq = AllP.++⁻ʳ b (subst (All Plain) (proj₂ (∙-inj eq)) ps)

-- WHAT A LANE CAN HANG ON, as each one-input former and a cold show it:
-- a cold's rows and its steps' lie below its subscription or in a timer
-- it creates, in its world; a map, a scan and a takeWhile keep their
-- source's positions, a takeWhile's own end one step below a value.
--
-- A cold's synchronous row lies one plain step into the world, and a
-- step's row plain steps below a timer the world holds, so a gap there
-- would hang its `nothing`, a hot row, in the world.
module ColdPlaced {Γ Δ} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {env : DenEnv Δ} {cs} (eh : EnvHeld ρ env cs)
                  {p} (ok : Ok (Hots env) p) (fr : Fresh eh p) where

  gap-off : ∀ {X} (j : X ∈ Γ) {c r} → Ann (EnvHeld.bound eh j) ((c ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) (out (r , nothing))
          → W⁼ (Hots env) p (c ⊕ [ ix 1 ]) → ⊥
  gap-off j {c} a w = proj₂ ok (gap-hot eh j a) (step w (plain-ix {0})) (⊑-inside {(c ⊕ [ ix 1 ]) ⊕ [ ix 0 ]} (⊑-refl _))

  now-apart : ∀ {l} → Plain l → ∀ zs {X} (j : X ∈ Γ) → Nl.¬ Gap (EnvHeld.bound eh j) (p ⊕ (l ∷ zs))
  now-apart {l} pl zs j (c , r , a , h , nl) with ⊑-cmp (c ⊕ [ ix 1 ]) (p ⊕ [ l ]) h (zs , sym (⊕-assoc p [ l ] zs))
  ... | inj₂ pc = proj₂ ok (gap-hot eh j a) (step here pl) (⊑-inside (⊑-trans pc (⊑-snoc⁺ _)))
  ... | inj₁ cp with ⊑-snoc p cp
  ...   | inj₁ cp′ = apart-at (proj₁ fr) j (c , r , a , cp′ , λ lp → nl (⊑-trans lp ((l ∷ zs) , refl)))
  ...   | inj₂ eq  = gap-off j a (subst (W⁼ _ _) (sym eq) (inW (step here pl)))

  step-apart : ∀ {i ws} → All Plain ws → W⁼ (Hots env) p (i ∙ ws) → ∀ {X} (j : X ∈ Γ) → Nl.¬ Gap (EnvHeld.bound eh j) (i ∙ ws)
  step-apart ps w j (c , r , a , (zs , eq) , nl) with w-pre (c ⊕ [ ix 1 ]) zs (plain-tail (c ⊕ [ ix 1 ]) zs ps eq) (subst (W⁼ _ _) eq w)
  ... | inj₁ wc        = gap-off j a wc
  ... | inj₂ (cp , py) = apart-at (proj₁ fr) j (c , r , a , cp , λ lp → nl (⊑-trans lp (subst (p ⊑_) (sym eq) py)))

  now-fresh : ∀ {l} → Plain l → ∀ zs → Fresh eh (p ⊕ (l ∷ zs))
  now-fresh pl zs = apart-all (λ j → now-apart pl zs j) , λ {c} ci → ≺-trans {c} {p} {p ⊕ (_ ∷ zs)} (proj₂ fr ci) (≺-ext p zs)

  step-fresh : ∀ {i ws} → All Plain ws → W⁼ (Hots env) p (i ∙ ws) → p ≺ (i ∙ ws) → Fresh eh (i ∙ ws)
  step-fresh {i} {ws} ps w lt = apart-all (λ j → step-apart ps w j) , λ {c} ci → ≺-trans {c} {p} {i ∙ ws} (proj₂ fr ci) lt

no-begin : ∀ {A n} → Shown {A} (out (instEmit (mark begin) n)) → ⊥
no-begin ()

no-over : ∀ {A n} → Shown {A} (out (instEmit (mark over) n)) → ⊥
no-over ()

placed-cold : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (c : Timeline A) (env : DenEnv Δ) cs → GoodEnv env
            → (eh : EnvHeld ρ env cs) → PlacedD (Hots env) (Fresh eh) (ev m (elab ρ (cold c)) env)
placed-cold m ρ c env cs g eh p ok fr ep x sh with cold-rows m c env p x (shown-vis sh)
... | now-value pl zs = ColdPlaced.now-fresh eh ok fr pl zs
... | now-end pl zs   = ColdPlaced.now-fresh eh ok fr pl zs
... | step-begin _    = ⊥-elim (no-begin sh)
... | step-over _     = ⊥-elim (no-over sh)
... | step-value f    = ColdPlaced.step-fresh eh ok fr (plain-ix ∷ plain-ix ∷ plain-ix ∷ plain-ix ∷ []ᵉ)
                          (inW (InvAt.world (inv-ev m (elab ρ (cold c)) env g p ok) x)) (fresh-past (⊑-refl p) f)
... | step-end f      = ColdPlaced.step-fresh eh ok fr (plain-ix ∷ plain-last ∷ []ᵉ)
                          (inW (InvAt.world (inv-ev m (elab ρ (cold c)) env g p ok) x)) (fresh-past (⊑-refl p) f)

shown-map : ∀ {A B} (f : A → B) (x : IE A) → Shown (out (mapIE f x)) → Shown {A} (out x)
shown-map f (instEmit (value _) _) _      = s-value
shown-map f (instEmit (mark _) _)  s-done = s-done

shown-scan : ∀ {A B} (f : B → A → B) st (x : IE A) → Shown (out (proj₂ (scanIE f st x))) → Shown {A} (out x)
shown-scan f st (instEmit (value _) _) _      = s-value
shown-scan f st (instEmit (mark _) _)  s-done = s-done

-- A value a takeWhile stops on is a value: marks pass.
fails-shown : ∀ {X} (kp : X → Bool) {x : IE X} → T (not (passes kp x)) → Shown (out x)
fails-shown kp {instEmit (value _) _} _ = s-value
fails-shown kp {instEmit (mark _) _} ()

placed-map-den : ∀ {A B : Set} (f : A → B) (d : Den (IE A)) {W F} → PlacedD W F d → PlacedD W F (Op.map (mapIE f) d)
placed-map-den f d pl p ok fp ep (map-out {a = x} t , _) sh = pl p ok fp ep t (shown-map f x sh)
placed-map-den f d pl p ok fp ep (map-end t , _)      s-end = pl p ok fp ep t s-end

placed-scan-den : ∀ {A B : Set} (f : B → A → B) (z : B × IE B) (d : Den (IE A)) {W F} → PlacedD W F d
                → PlacedD W F (Op.map proj₂ (Op.scan (scanIE f) z d))
placed-scan-den f z d pl p ok fp ep (map-out t , _) sh with scan-out (scanIE f) z d p t
... | st , x , r , refl = pl p ok fp ep r (shown-scan f st x sh)
placed-scan-den f z d pl p ok fp ep (map-end (Scan.send r , _) , _) s-end = pl p ok fp ep r s-end

placed-take-den : ∀ {X : Set} incl (kp : X → Bool) (d : Den (IE X)) {H F} → Adm H F → PlacedD H F d
                → PlacedD H F (Op.takeWhile incl (passes kp) d)
placed-take-den incl kp d ad pl p ok fp ep (TakeWhile.pass t _ _ , _)    sh    = pl p ok fp ep t sh
placed-take-den incl kp d ad pl p ok fp ep (TakeWhile.fail t nk _ _ , _) _     = Adm.bare ad (pl p ok fp ep t (fails-shown kp nk)) λ ()
placed-take-den incl kp d ad pl p ok fp ep (TakeWhile.stop t nk _ , _)   s-end = Adm.bare ad (pl p ok fp ep t (fails-shown kp nk)) λ ()
placed-take-den incl kp d ad pl p ok fp ep (TakeWhile.tend t _ , _)      s-end = pl p ok fp ep t s-end

held-cold : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (c : Timeline A) → IH m ρ (cold c)
held-cold m ρ c = ih (λ env cs g eh p ok fr ep →
  let open ColdHeld p (enter (ev m (elab ρ (cold c)) env) p) (cold-rows m c env p) in
  held-runs named routing (early ep) (ends ep) done late (cold-idle m c env p) (cold-rest m c env p) λ mt → record
    { covered = λ r₁ r₂ eq cr ne → cold-covered m c env p mt r₁ r₂ eq cr λ { (here s) → ne (here s) ; (there ()) }
    ; exact   = λ r₁ r₂ eq → ⊥-elim (no-stop (proj₁ (run-row r₁ (subst (Met _) eq mt))))
    ; shut    = cold-shut m c env p mt })
  (placed-cold m ρ c)

held-map : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : A → B) s → IH m ρ s → IH m ρ (map f s)
held-map nothing  ρ f s (ih h pl) = ih (λ env cs g eh → held-map-den f (⟦ elab ρ s ⟧ env) cs (h env cs g eh))
                                        λ env cs g eh → placed-map-den f (⟦ elab ρ s ⟧ env) (pl env cs g eh)
held-map (just n) ρ f s (ih h pl) = ih (λ env cs g eh → held-map-den f (approx n (elab ρ s) env) cs (h env cs g eh))
                                        λ env cs g eh → placed-map-den f (approx n (elab ρ s) env) (pl env cs g eh)

held-takeWhile : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) i (p : A → _) s → IH m ρ s → IH m ρ (takeWhile i p s)
held-takeWhile nothing  ρ i p s (ih h pl) = ih
  (λ env cs g eh → held-take-den i p (⟦ elab ρ s ⟧ env) cs (h env cs g eh) (inv-⟦⟧ (elab ρ s) env g))
  λ env cs g eh → placed-take-den i p (⟦ elab ρ s ⟧ env) (fresh-adm eh) (pl env cs g eh)
held-takeWhile (just n) ρ i p s (ih h pl) = ih
  (λ env cs g eh → held-take-den i p (approx n (elab ρ s) env) cs (h env cs g eh) (inv-approx n (elab ρ s) env g))
  λ env cs g eh → placed-take-den i p (approx n (elab ρ s) env) (fresh-adm eh) (pl env cs g eh)

held-scan : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : B → A → B) z s → IH m ρ s → IH m ρ (scan f z s)
held-scan nothing  ρ f z s (ih h pl) = ih (λ env cs g eh → held-scan-den f (z , marked begin) (⟦ elab ρ s ⟧ env) cs (h env cs g eh))
                                           λ env cs g eh → placed-scan-den f (z , marked begin) (⟦ elab ρ s ⟧ env) (pl env cs g eh)
held-scan (just n) ρ f z s (ih h pl) = ih (λ env cs g eh → held-scan-den f (z , marked begin) (approx n (elab ρ s) env) cs (h env cs g eh))
                                           λ env cs g eh → placed-scan-den f (z , marked begin) (approx n (elab ρ s) env) (pl env cs g eh)

-- A binder held under `cs` is held under more.
widen : ∀ {X} {d : Den (AIE X)} {c cs} → Bound d cs → Bound d (c ∷ cs)
widen b = record
  { m = Bound.m b ; src = Bound.src b ; env = Bound.env b ; at = Bound.at b ; outer = Bound.outer b
  ; held = Bound.held b ; good = Bound.good b ; undone = Bound.undone b ; ok = Bound.ok b ; ep = Bound.ep b ; under = λ i → there (Bound.under b i) ; is = Bound.is b }

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

-- A connect's rows are its body's, read past the source made hot.
placed-conn : ∀ m {Δ X B} (A′ : Obs Timeline Δ X) (B′ : Obs Timeline (X ∷ Δ) (IE B)) (env : DenEnv Δ) → GoodEnv env
            → ∀ {F G : Pos → Set} → (∀ {y} → G y → F y) → ∀ p → Ok (Hots env) p
            → (Lawful (Proper (enter (ev m A′ env) (p ⊕ [ ix 1 ])))
               → Ok (Hots env ∪ʰ Proper (enter (ev m A′ env) (p ⊕ [ ix 1 ]))) (p ⊕ [ ix 0 ])
               → Placed G (enter (ev m B′ (hot (Proper (enter (ev m A′ env) (p ⊕ [ ix 1 ]))) ∷ env)) (p ⊕ [ ix 0 ])))
            → Placed F (enter (ev m (connect A′ B′) env) p)
placed-conn nothing A′ B′ env g gf p ok k (Connecting.body x , _) sh =
  gf (k (src-lawful {s = ⟦ A′ ⟧ env} {F = λ h → ⟦ B′ ⟧ (h ∷ env)} Is IF p ok) (body-ok {s = ⟦ A′ ⟧ env} {F = λ h → ⟦ B′ ⟧ (h ∷ env)} Is IF p ok) x sh)
  where
    Is = inv-⟦⟧ A′ env g
    IF : ∀ {t} → Lawful t → InvD (Hots env ∪ʰ t) (⟦ B′ ⟧ (hot t ∷ env))
    IF L = inv-⟦⟧ B′ (hot _ ∷ env) (good-cons L g)
placed-conn (just n) A′ B′ env g gf p ok k (Connecting.body x , _) sh =
  gf (k (src-lawful {s = approx n A′ env} {F = λ h → approx n B′ (h ∷ env)} Is IF p ok)
        (body-ok {s = approx n A′ env} {F = λ h → approx n B′ (h ∷ env)} Is IF p ok) x sh)
  where
    Is = inv-approx n A′ env g
    IF : ∀ {t} → Lawful t → InvD (Hots env ∪ʰ t) (approx n B′ (hot t ∷ env))
    IF L = inv-approx n B′ (hot _ ∷ env) (good-cons L g)

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
