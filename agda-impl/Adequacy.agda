{-# OPTIONS --guardedness #-}

-- THE LINK.  The pure runtime and the denotation agree: the limit of the
-- pure run's approximants is the denotation's limit, observed at time 0.
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
open import operation.PureObservable using (Pureᴾ; PureObs; deferredᴺ; compileᴺ; runPure; toArray)
open import denotation.MonotonicList using (MonotonicList; cold; observe; Timeline; emptyᴰ; ofᴰ; mapᴰ; scanᴰ; takeWhileᴰ; flattenᴰ; deferᴰ; connectᴰ; ⊥ᴰ; _⊑_; ⊑-trans; _≈_; lub)
open import denotation.Denote using (DenEnv; flatOp; laneᴰ; ⟦_⟧[_]; ⟦_⟧)
open Run Pureᴾ

-- The pure run: the limit of its approximants, the root subscribed at 0.
run : ∀ {A} → PureObs [] A → MonotonicList A
run o = lub λ n → cold (toArray n o)

postulate
  -- "Subscribing with `s` at any time t, in any heap, on an engine with
  -- budget enough, shows at least what `d` shows a subscriber arriving
  -- at t."
  Rel   : ∀ {A} → Subscribe A → MonotonicList A → Set₁
  -- A subject and the handle `connectᴰ` passed its body agree: joining
  -- one shows at least what the other shows, at any join time.
  RelSubj : ∀ {A} → Subject A → MonotonicList A → Set₁

data RelEnv : ∀ {Γ} → Env Γ → DenEnv Γ → Set₁ where
  []  : RelEnv [] []
  _∷_ : ∀ {Γ A} {st : Subject A} {x : MonotonicList A} {ρ : Env Γ} {δ : DenEnv Γ}
      → RelSubj st x → RelEnv ρ δ → RelEnv (st ∷ ρ) (x ∷ δ)

-- An element's echo is the same on both sides; its lane, if any, is related.
data RelLane {B : Set} : Maybe B × Maybe (Subscribe B) → Maybe B × Maybe (MonotonicList B) → Set₁ where
  none : ∀ {e}     → RelLane (e , nothing) (e , nothing)
  some : ∀ {e s d} → Rel s d → RelLane (e , just s) (e , just d)

postulate
  -- One per operator: the kernel and its denotation agree.
  empty-rel     : ∀ {A} → Rel {A} emptyᴷ emptyᴰ
  of-rel        : ∀ {A} (xs : List A) → Rel (ofᴷ xs) (ofᴰ xs)
  map-rel       : ∀ {A B s d} (f : A → B) → Rel s d → Rel (mapᴷ f s) (mapᴰ f d)
  scan-rel      : ∀ {A B s d} (f : B → A → B) z → Rel s d → Rel (scanᴷ f z s) (scanᴰ f z d)
  takeWhile-rel : ∀ {A s d} p → Rel {A} s d → Rel (takeWhileᴷ p s) (takeWhileᴰ p d)
  flatten-rel   : ∀ {A B s d} op {f : A → Maybe B × Maybe (Subscribe B)} {g}
                → (∀ a → RelLane (f a) (g a)) → Rel s d → Rel (flattenᴷ op f s) (flattenᴰ (flatOp op) (mapᴰ g d))
  cold-rel      : ∀ {A} (c : Timeline A) → Rel (via (startCold c)) (cold (lower c))
  connected-rel : ∀ {Γ A ρ δ} (i : A ∈ Γ) → RelEnv ρ δ
                → Rel (joinᴷ (lookup ρ i)) (lookup δ i)
  -- The subject `connectᴷ` allocates, fed by the source after the body
  -- has subscribed, agrees with the hot handle `connectᴰ` passes; then
  -- the body runs under both.
  connect-rel   : ∀ {A B} {s : Subscribe A} {d} {b : Subject A → Subscribe B}
                    {e : MonotonicList A → MonotonicList B}
                → Rel s d → (∀ {st r} → RelSubj st r → Rel (b st) (e r))
                → Rel (connectᴷ s b) (connectᴰ d e)
  -- `deferᴰ` adds one `stall`, invisible to `_⊑_`.
  defer-rel     : ∀ {A} {s : Subscribe A} {d} → Rel s d → Rel s (deferᴰ d)
  -- A cut-off `defer` on both sides: ⊥ᴰ shows nothing.
  bot-rel       : ∀ {A} → Rel {A} ⊥ᴷ ⊥ᴰ

  -- THE ENGINE'S FACT: running a related subscription at time 0 shows at
  -- least what the timeline shows, in the limit of the run's budget.
  run-rel : ∀ {A} {s : Subscribe A} {d}
          → Rel s d → cold (observe d 0) ⊑ lub (λ m → cold (runPure m s))

  -- More `defer`s compiled shows more, so running approximant n of the
  -- compiler is below the run, whose approximants compile ever more.
  diagonal : ∀ {A} n (o : PureObs [] A) → lub (λ m → cold (runPure m (compileᴺ n o []))) ⊑ run o

  -- Every finite prefix of the run is reached at some finite budget, so
  -- some approximant of the denotation already shows it; with
  -- soundness, the two limits agree.  The one argument about limits.
  exhaust : ∀ {A} (o : PureObs [] A) → (∀ n → cold (observe (⟦ o ⟧[ n ] []) 0) ⊑ run o)
          → run o ≈ cold (observe (⟦ o ⟧ []) 0)

mutual
  -- THE FUNDAMENTAL LEMMA.  Approximant n against approximant n, by the
  -- recursion both share: lexicographic on (n , tree), so inductive.
  fundamental : ∀ n {Γ A} (o : PureObs Γ A) {ρ : Env Γ} {δ : DenEnv Γ}
              → RelEnv ρ δ → Rel (compileᴺ n o ρ) (⟦ o ⟧[ n ] δ)
  fundamental n       (cold c)         e = cold-rel c
  fundamental n       empty            e = empty-rel
  fundamental n       (of xs)          e = of-rel xs
  fundamental n       (map f s)        e = map-rel f (fundamental n s e)
  fundamental n       (scan f z s)     e = scan-rel f z (fundamental n s e)
  fundamental n       (takeWhile p s)  e = takeWhile-rel p (fundamental n s e)
  fundamental n       (flatten op f s) e = flatten-rel op (λ a → lane-rel n (f a) e) (fundamental n s e)
  fundamental n       (connect s b)    e = connect-rel (fundamental n s e) (λ r → fundamental n b (r ∷ e))
  fundamental n       (connected i)    e = connected-rel i e
  fundamental zero    (defer l)        e = bot-rel
  fundamental (suc n) (defer l)        e = defer-rel (fundamental n (Later.force l) e)

  lane-rel : ∀ n {Γ B} (x : Maybe B × Maybe (PureObs Γ B)) {ρ : Env Γ} {δ : DenEnv Γ}
           → RelEnv ρ δ → RelLane (lane (deferredᴺ n) x ρ) (laneᴰ n x δ)
  lane-rel n (b , nothing) e = none
  lane-rel n (b , just l)  e = some (fundamental n l e)

-- Each approximant of the denotation is sound for the run.
sound : ∀ {A} (o : PureObs [] A) n → cold (observe (⟦ o ⟧[ n ] []) 0) ⊑ run o
sound o n = ⊑-trans (run-rel (fundamental n o [])) (diagonal n o)

adequacy : ∀ {A} (o : PureObs [] A) → run o ≈ cold (observe (⟦ o ⟧ []) 0)
adequacy o = exhaust o (sound o)
