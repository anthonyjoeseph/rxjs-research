{-# OPTIONS --guardedness #-}

-- THE LINK.  The pure runtime and the denotation agree: the limit of the
-- pure run's approximants is the denotation's limit, observed at the
-- root, with positions forgotten down to ticks.
--
-- Both sides are chains of approximants built the same way — approximant
-- n compiles n nested `defer`s, and past that shows nothing — so the
-- fundamental lemma compares approximant n with approximant n, by
-- induction on (n , tree), one operator at a time: each kernel preserves
-- a logical relation between a `Subscribe` and a timeline.  Nothing is
-- coinductive except the last step, from approximants to limits.
--
-- The relation is APPROXIMATION, not equality: `Rel s d` says everything
-- `d` shows, running `s` shows too, given budget enough.  No lemma ever
-- mentions a heap address belonging to another operator.
--
-- The IO runtime has no theorem of its own, and needs none: it is the
-- same engine over a different monad, with its recursion closed by `fix`
-- rather than by unfolding.  The oracle compares it to the TypeScript.
module Adequacy where

open import Data.List using (List; _∷_; [])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using ([]; _∷_; lookup)
open import Data.Nat using (zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Level using (lower)

open import Tree using (cold; empty; of; map; scan; takeWhile; flatten; connect; connected; defer; Later)
open import operation.AbstractObservable using (module Run)
open import operation.PureObservable using (Pureᴾ; PureObs; deferredᴺ; compileᴺ; runPure; toArray) renaming (_⊑_ to _≤ʷ_)
open import denotation.MonotonicList using (ML; MonotonicList; coldᴰ; observe; root; ticks; Timeline; emptyᴰ; ofᴰ; mapᴰ; scanᴰ; takeWhileᴰ; flattenᴰ; deferᴰ; connectᴰ; ⊥ᴰ; _⊑_; ⊑-trans; _≃_; limit)
open import denotation.Denote using (DenEnv; flatOp; laneᴰ; ⟦_⟧[_]; ⟦_⟧)
open Run Pureᴾ

-- The pure run: the limit of its approximants.
run : ∀ {A} → PureObs [] A → ML A
run o = limit λ n → toArray n o

postulate
  -- "Subscribing with `s` at any position p, in any heap, on an engine
  -- with budget enough, shows at least what `d` shows a subscriber
  -- arriving at p, ticks for ticks."
  Rel   : ∀ {A w} → Subscribe A w → MonotonicList A → Set₁
  -- A subject and the handle `connectᴰ` passed its body agree: joining
  -- one shows at least what the other shows, at any join time.
  RelSubj : ∀ {A w} → Subject A w → MonotonicList A → Set₁
  -- A subject made in one world is the same subject in every later one.
  RelSubj-wk : ∀ {A w v} {st : Subject A w} {x} (σ : w ≤ʷ v) → RelSubj st x → RelSubj (wkSubject σ st) x

data RelEnv {w} : ∀ {Γ} → Env Γ w → DenEnv Γ → Set₁ where
  []  : RelEnv [] []
  _∷_ : ∀ {Γ A} {st : Subject A w} {x : MonotonicList A} {ρ : Env Γ w} {δ : DenEnv Γ}
      → RelSubj st x → RelEnv ρ δ → RelEnv (st ∷ ρ) (x ∷ δ)

wkRelEnv : ∀ {Γ w v} {ρ : Env Γ w} {δ : DenEnv Γ} (σ : w ≤ʷ v) → RelEnv ρ δ → RelEnv (wkEnv σ ρ) δ
wkRelEnv σ []      = []
wkRelEnv σ (r ∷ e) = RelSubj-wk σ r ∷ wkRelEnv σ e

-- An element's echo is the same on both sides; its lane, if any, is related.
data RelLane {B : Set} {w} : Lane B w → Maybe B × Maybe (MonotonicList B) → Set₁ where
  none : ∀ {e}     → RelLane (e , nothing) (e , nothing)
  some : ∀ {e} {s : Subscribe B w} {d} → Rel s d → RelLane (e , just s) (e , just d)

postulate
  -- One per operator: the kernel and its denotation agree.
  empty-rel     : ∀ {A w} → Rel {A} {w} emptyᴷ emptyᴰ
  of-rel        : ∀ {A w} (xs : List A) → Rel {w = w} (ofᴷ xs) (ofᴰ xs)
  map-rel       : ∀ {A B w} {s : Subscribe A w} {d} (f : A → B) → Rel s d → Rel (mapᴷ f s) (mapᴰ f d)
  scan-rel      : ∀ {A B w} {s : Subscribe A w} {d} (f : B → A → B) z → Rel s d → Rel (scanᴷ f z s) (scanᴰ f z d)
  takeWhile-rel : ∀ {A w} {s : Subscribe A w} {d} p → Rel s d → Rel (takeWhileᴷ p s) (takeWhileᴰ p d)
  flatten-rel   : ∀ {A B w} {s : Subscribe A w} {d} op {f : A → Lane B w} {g}
                → (∀ a → RelLane (f a) (g a)) → Rel s d → Rel (flattenᴷ op f s) (flattenᴰ (flatOp op) (mapᴰ g d))
  cold-rel      : ∀ {A w} (c : Timeline A) → Rel {w = w} (via (startCold c)) (coldᴰ (lower c))
  connected-rel : ∀ {Γ A w} {ρ : Env Γ w} {δ} (i : A ∈ Γ) → RelEnv ρ δ
                → Rel (joinᴷ (lookup ρ i)) (lookup δ i)
  -- The subject `connectᴷ` allocates, fed by the source after the body
  -- has subscribed, agrees with the hot handle `connectᴰ` passes; then
  -- the body runs under both.
  connect-rel   : ∀ {A B w} {s : Subscribe A w} {d} {b : ∀ {v} → w ≤ʷ v → Subject A v → Subscribe B v}
                    {e : MonotonicList A → MonotonicList B}
                → Rel s d → (∀ {v} (σ : w ≤ʷ v) {st r} → RelSubj st r → Rel (b σ st) (e r))
                → Rel (connectᴷ s b) (connectᴰ d e)
  -- `deferᴰ` adds one `skip`, a `stall` once reported, invisible to `_⊑_`.
  defer-rel     : ∀ {A w} {s : Subscribe A w} {d} → Rel s d → Rel s (deferᴰ d)
  -- A cut-off `defer` on both sides: ⊥ᴰ shows nothing.
  bot-rel       : ∀ {A w} → Rel {A} {w} ⊥ᴷ ⊥ᴰ

  -- THE ENGINE'S FACT: running a related subscription at the root shows
  -- at least what the denotation shows there, in the limit of the run's
  -- budget.
  run-rel : ∀ {A} {s : Subscribe A []} {d}
          → Rel s d → ticks (observe d root) ⊑ limit (λ m → runPure m s)

  -- More `defer`s compiled shows more, so running approximant n of the
  -- compiler is below the run, whose approximants compile ever more.
  diagonal : ∀ {A} n (o : PureObs [] A) → limit (λ m → runPure m (compileᴺ n o [])) ⊑ run o

  -- Every finite prefix of the run is reached at some finite budget, so
  -- some approximant of the denotation already shows it; with
  -- soundness, the two limits agree.  The one argument about limits.
  exhaust : ∀ {A} (o : PureObs [] A) → (∀ n → ticks (observe (⟦ o ⟧[ n ] []) root) ⊑ run o)
          → run o ≃ ticks (observe (⟦ o ⟧ []) root)

mutual
  -- THE FUNDAMENTAL LEMMA.  Approximant n against approximant n, by the
  -- recursion both share: lexicographic on (n , tree), so inductive.
  fundamental : ∀ n {Γ A w} (o : PureObs Γ A) {ρ : Env Γ w} {δ : DenEnv Γ}
              → RelEnv ρ δ → Rel (compileᴺ n o ρ) (⟦ o ⟧[ n ] δ)
  fundamental n       (cold c)         e = cold-rel c
  fundamental n       empty            e = empty-rel
  fundamental n       (of xs)          e = of-rel xs
  fundamental n       (map f s)        e = map-rel f (fundamental n s e)
  fundamental n       (scan f z s)     e = scan-rel f z (fundamental n s e)
  fundamental n       (takeWhile p s)  e = takeWhile-rel p (fundamental n s e)
  fundamental n       (flatten op f s) e = flatten-rel op (λ a → lane-rel n (f a) e) (fundamental n s e)
  fundamental n       (connect s b)    e = connect-rel (fundamental n s e) (λ σ r → fundamental n b (r ∷ wkRelEnv σ e))
  fundamental n       (connected i)    e = connected-rel i e
  fundamental zero    (defer l)        e = bot-rel
  fundamental (suc n) (defer l)        e = defer-rel (fundamental n (Later.force l) e)

  lane-rel : ∀ n {Γ B w} (x : Maybe B × Maybe (PureObs Γ B)) {ρ : Env Γ w} {δ : DenEnv Γ}
           → RelEnv ρ δ → RelLane (lane (deferredᴺ n) x ρ) (laneᴰ n x δ)
  lane-rel n (b , nothing) e = none
  lane-rel n (b , just l)  e = some (fundamental n l e)

-- Each approximant of the denotation is sound for the run.
sound : ∀ {A} (o : PureObs [] A) n → ticks (observe (⟦ o ⟧[ n ] []) root) ⊑ run o
sound o n = ⊑-trans (run-rel (fundamental n o [])) (diagonal n o)

adequacy : ∀ {A} (o : PureObs [] A) → run o ≃ ticks (observe (⟦ o ⟧ []) root)
adequacy o = exhaust o (sound o)
