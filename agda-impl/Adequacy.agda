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
-- The relation is TWO-SIDED.  `Rel s d`: with budget enough, running `s`
-- shows everything `d` shows; on any budget, it shows nothing `d` does
-- not.  The second half is what makes the limits meet: run n is below
-- approximant n, which is below the run.  No lemma ever mentions a heap
-- address belonging to another operator.
--
-- The IO runtime has no theorem of its own, and needs none: it is the
-- same engine over a different monad, with its recursion closed by `fix`
-- rather than by unfolding.  The oracle compares it to the TypeScript.
module Adequacy where

open import Data.List using (List; _∷_; [])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using ([]; _∷_; lookup)
open import Data.Nat using (ℕ; zero; suc)
open import Level using (lower)

open import Tree using (cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer; Later)
open import operation.AbstractObservable using (module Run)
open import operation.PureObservable using (Pureᴾ; PureObs; deferredᴺ; compileᴺ; runPure; toArray) renaming (_⊑_ to _≤ʷ_)
open import denotation.MonotonicList using (ML; MonotonicList; coldᴰ; observe; root; ticks; Timeline; emptyᴰ; ofᴰ; mapᴰ; scanᴰ; takeWhileᴰ; flatMapᴰ; deferᴰ; connectᴰ; ⊥ᴰ; _⊑_; ⊑-trans; _≃_; ≃-trans; limit; Chain; squeeze)
open import denotation.Denote using (DenEnv; flatOp; ⟦_⟧[_]; ⟦_⟧)
open Run Pureᴾ

-- The pure run: the limit of its approximants.
run : ∀ {A} → PureObs [] A → ML A
run o = limit λ n → toArray n o

-- Approximant n of the denotation, as the run reports one.
approxAt : ∀ {A} → PureObs [] A → ℕ → ML A
approxAt o n = ticks (observe (⟦ o ⟧[ n ] []) root)

postulate
  -- "Subscribing with `s` at any position p, in any heap, shows what `d`
  -- shows a subscriber arriving at p, ticks for ticks: on an engine with
  -- budget enough, at least that; on any budget, no more."
  Rel   : ∀ {A w} → Subscribe A w → MonotonicList A → Set₁
  -- A subject and the handle `connectᴰ` passed its body agree: joining
  -- one shows what joining the other shows, at any join time, both ways
  -- as `Rel`.
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

postulate
  -- One per operator: the kernel and its denotation agree.
  empty-rel     : ∀ {A w} → Rel {A} {w} emptyᴷ emptyᴰ
  of-rel        : ∀ {A w} (xs : List A) → Rel {w = w} (ofᴷ xs) (ofᴰ xs)
  map-rel       : ∀ {A B w} {s : Subscribe A w} {d} (f : A → B) → Rel s d → Rel (mapᴷ f s) (mapᴰ f d)
  scan-rel      : ∀ {A B w} {s : Subscribe A w} {d} (f : B → A → B) z → Rel s d → Rel (scanᴷ f z s) (scanᴰ f z d)
  takeWhile-rel : ∀ {A w} {s : Subscribe A w} {d} i p → Rel s d → Rel (takeWhileᴷ i p s) (takeWhileᴰ i p d)
  flatMap-rel   : ∀ {A B w} {s : Subscribe A w} {d} op {f : A → Subscribe B w} {g}
                → (∀ a → Rel (f a) (g a)) → Rel s d → Rel (flatMapᴷ op f s) (flatMapᴰ (flatOp op) g d)
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
  -- `deferᴰ` adds one `skip`, a `stall` once reported, invisible either way.
  defer-rel     : ∀ {A w} {s : Subscribe A w} {d} → Rel s d → Rel s (deferᴰ d)
  -- A cut-off `defer` on both sides: each shows nothing.
  bot-rel       : ∀ {A w} → Rel {A} {w} ⊥ᴷ ⊥ᴰ

  -- THE ENGINE'S FACTS, `Rel`'s two halves at the root: in the limit of
  -- its budget, a related run shows at least what the denotation shows
  -- there; on any budget, no more.
  run-rel : ∀ {A} {s : Subscribe A []} {d}
          → Rel s d → ticks (observe d root) ⊑ limit (λ m → runPure m s)
  run-bound : ∀ {A} {s : Subscribe A []} {d}
            → Rel s d → ∀ m → runPure m s ⊑ ticks (observe d root)

  -- More `defer`s compiled shows more, so running approximant n of the
  -- compiler is below the run, whose approximants compile ever more.
  diagonal : ∀ {A} n (o : PureObs [] A) → limit (λ m → runPure m (compileᴺ n o [])) ⊑ run o

  -- Both sides are chains: a bigger budget, or a deeper approximant,
  -- shows more.
  toArray-chain : ∀ {A} (o : PureObs [] A) → Chain (λ n → toArray n o)
  approx-chain  : ∀ {A} (o : PureObs [] A) → Chain (approxAt o)

  -- Observing at the root, then forgetting positions, commutes with the
  -- limit that `⟦_⟧` takes.
  ⟦⟧-limit : ∀ {A} (o : PureObs [] A) → limit (approxAt o) ≃ ticks (observe (⟦ o ⟧ []) root)

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
  fundamental n       (takeWhile i p s) e = takeWhile-rel i p (fundamental n s e)
  fundamental n       (flatMap op f s) e = flatMap-rel op (λ a → fundamental n (f a) e) (fundamental n s e)
  fundamental n       (connect s b)    e = connect-rel (fundamental n s e) (λ σ r → fundamental n b (r ∷ wkRelEnv σ e))
  fundamental n       (connected i)    e = connected-rel i e
  fundamental zero    (defer l)        e = bot-rel
  fundamental (suc n) (defer l)        e = defer-rel (fundamental n (Later.force l) e)

-- Each approximant of the denotation is below the run.
sound : ∀ {A} (o : PureObs [] A) n → approxAt o n ⊑ run o
sound o n = ⊑-trans (run-rel (fundamental n o [])) (diagonal n o)

-- Each approximant of the run is below the denotation's.
complete : ∀ {A} (o : PureObs [] A) n → toArray n o ⊑ approxAt o n
complete o n = run-bound (fundamental n o []) n

adequacy : ∀ {A} (o : PureObs [] A) → run o ≃ ticks (observe (⟦ o ⟧ []) root)
adequacy o = ≃-trans (squeeze (toArray-chain o) (approx-chain o) (sound o) (complete o)) (⟦⟧-limit o)
