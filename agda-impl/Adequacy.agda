{-# OPTIONS --guardedness #-}

-- THE LINK.  Running a program in the pure semantics yields exactly its
-- denotation, observed at time 0.
--
-- The route is a logical relation between a `Subscribe` and a timeline,
-- proven one operator at a time: each kernel preserves it.  The
-- fundamental lemma is then the same recursion as `⟦_⟧[_]`, and adequacy
-- is that lemma plus two facts about the loop.  No lemma ever mentions a
-- heap address belonging to another operator.
--
-- The relation is APPROXIMATION, not equality: `Rel s d` says everything
-- `d` shows, running `s` shows too.  That is what lets the fundamental
-- lemma be inductive — at index zero a `defer` means ⊥ᴰ, which every
-- subscription approximates — and leaves all coinduction to the loop,
-- the one place it is productive.
--
-- The IO runtime has no theorem: it runs the same `subscribe`, and the
-- oracle compares it to the TypeScript through `Observable.toIO`.
module Adequacy where

open import Data.List using (List; _∷_; [])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; map₂)
open import Data.Unit using (tt)
open import Level using (lower)

open import AbstractObservable hiding (ones; merge; flatMap)
open import MonotonicList hiding (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import Denote
open import PureObservable
open Run Pureᴾ

-- The pure run, as a timeline: the root is subscribed at time 0.
run : ∀ {A} → PureObs [] A → MonotonicList A
run o = cold (runPure o)

postulate
  -- "Subscribing with `s` at any time t, in any heap, with its `child`
  -- requests unfolded by the loop, shows at least what `d` shows a
  -- subscriber arriving at t."
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

  -- THE LOOP'S TWO FACTS.  Unfolding `child` is a `stall` and then the
  -- subtree's own subscribe, and `stall`s are invisible to `_⊑_`.
  child-rel : ∀ {Γ A} {s : Obs Timeline Γ A} {ρ d} → Rel (subscribe s ρ) d → Rel (sub s ρ) d
  -- ⊥ᴰ shows nothing, so anything approximates it.
  bot-rel   : ∀ {A} {s : Subscribe A} → Rel s ⊥ᴰ

  -- The loop turns a related subscription into a run at time 0.
  loop-rel : ∀ {A} {s : Subscribe A} {d}
           → Rel s d → cold (observe d 0) ⊑ cold (loop (λ sink → s (sinkObserver sink) λ _ → done tt))

  -- Every finite prefix of a run unfolds finitely many `child`s, so some
  -- approximant already shows it; with soundness, the run is the lub.
  -- The one coinductive argument in the development.
  exhaust : ∀ {A} (o : PureObs [] A) → (∀ n → cold (observe (⟦ o ⟧[ n ] []) 0) ⊑ run o)
          → run o ≈ cold (observe (⟦ o ⟧ []) 0)

mutual
  -- THE FUNDAMENTAL LEMMA.  The recursion of `⟦_⟧[_]`: lexicographic on
  -- (n , tree), so inductive — nothing here is guarded.
  fundamental : ∀ n {Γ A} (o : PureObs Γ A) {ρ : Env Γ} {δ : DenEnv Γ}
              → RelEnv ρ δ → Rel (subscribe o ρ) (⟦ o ⟧[ n ] δ)
  fundamental n       (cold c)         e = cold-rel c
  fundamental n       empty            e = empty-rel
  fundamental n       (of xs)          e = of-rel xs
  fundamental n       (map f s)        e = map-rel f (child-rel (fundamental n s e))
  fundamental n       (scan f z s)     e = scan-rel f z (child-rel (fundamental n s e))
  fundamental n       (takeWhile p s)  e = takeWhile-rel p (child-rel (fundamental n s e))
  fundamental n       (flatten op f s) e = flatten-rel op (λ a → lane-rel n (f a) e) (child-rel (fundamental n s e))
  fundamental n       (connect s b)    e = connect-rel (child-rel (fundamental n s e))
                                                       (λ r → child-rel (fundamental n b (r ∷ e)))
  fundamental n       (connected i)    e = connected-rel i e
  fundamental zero    (defer l)        e = bot-rel
  fundamental (suc n) (defer l)        e = defer-rel (child-rel (fundamental n (Later.force l) e))

  lane-rel : ∀ n {Γ B} (x : Maybe B × Maybe (PureObs Γ B)) {ρ : Env Γ} {δ : DenEnv Γ}
           → RelEnv ρ δ → RelLane (map₂ (Maybe.map λ l → sub l ρ) x) (laneᴰ n x δ)
  lane-rel n (b , nothing) e = none
  lane-rel n (b , just l)  e = some (child-rel (fundamental n l e))

-- Each approximant is sound for the run.
sound : ∀ {A} (o : PureObs [] A) n → cold (observe (⟦ o ⟧[ n ] []) 0) ⊑ run o
sound o n = loop-rel (fundamental n o [])

adequacy : ∀ {A} (o : PureObs [] A) → run o ≈ cold (observe (⟦ o ⟧ []) 0)
adequacy o = exhaust o (sound o)
