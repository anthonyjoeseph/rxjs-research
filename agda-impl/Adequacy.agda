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
open import Data.Unit using (tt)
open import Level using (lower)

open import AbstractObservable
open import MonotonicList
open import PureObservable
open Run Pureᴾ

postulate
  -- Equal frames at equal times, ignoring finitely many `stall`s.
  _≈_ : ∀ {A} → ML A → ML A → Set

  -- "Subscribing with `s` at any time t, in any heap, with its `child`
  -- requests unfolded by the loop, shows at least what `d` shows a
  -- subscriber arriving at t."
  Rel   : ∀ {A} → Subscribe A → MonotonicList A → Set₁
  -- The share's state and its denotation agree: joining one shows at
  -- least what reading the other does, at any join time.
  RelSh : ∀ {A} → ShareSt A → Shared A → Set₁

data RelEnv : ∀ {Γ} → Env Γ → DenEnv Γ → Set₁ where
  []  : RelEnv [] []
  _∷_ : ∀ {Γ A} {st : ShareSt A} {x : Shared A} {ρ : Env Γ} {δ : DenEnv Γ}
      → RelSh st x → RelEnv ρ δ → RelEnv (st ∷ ρ) (x ∷ δ)

postulate
  -- One per operator: the kernel and its denotation agree.
  of-rel        : ∀ {A} (xs : List A) → Rel (ofᴷ xs) (ofᴰ xs)
  map-rel       : ∀ {A B s d} (f : A → B) → Rel s d → Rel (mapᴷ f s) (mapᴰ f d)
  scan-rel      : ∀ {A B s d} (f : B → A → B) z → Rel s d → Rel (scanᴷ f z s) (scanᴰ f z d)
  takeWhile-rel : ∀ {A s d} p → Rel {A} s d → Rel (takeWhileᴷ p s) (takeWhileᴰ p d)
  merge-rel     : ∀ {A s d t e} → Rel {A} s d → Rel t e → Rel (mergeᴷ s t) (mergeᴰ d e)
  flatMap-rel   : ∀ {A B s d} op {f : A → Subscribe B} {g}
                → (∀ a → Rel (f a) (g a)) → Rel s d → Rel (flatMapᴷ op f s) (flatMapᴰ op g d)
  cold-rel      : ∀ {A} (c : Timeline A) → Rel (via (startCold c)) (cold (lower c))
  shared-rel    : ∀ {Γ A ρ δ} (i : A ∈ Γ) → RelEnv ρ δ
                → Rel (joinᴷ (lookup ρ i)) (readShared (lookup δ i))
  -- The state `newShareᴷ` allocates agrees with `shareᴰ`; then the body
  -- runs under both.  The open design question lives here and in
  -- `shared-rel`: `RelSh` must say what a ref-counted join shows.
  share-rel     : ∀ {Γ A B} {s : Obs Timeline Γ A} {ρ δ d} {b : ShareSt A → Subscribe B} {e}
                → RelEnv ρ δ → Rel (subscribe s ρ) d
                → (∀ {st} → RelSh st (shareᴰ d) → Rel (b st) e)
                → Rel (λ o k → newShareᴷ s ρ λ st → b st o k) e

  -- THE LOOP'S TWO FACTS.  Unfolding `child` is a `stall` and then the
  -- subtree's own subscribe, and `stall`s are invisible to `_⊑_`.
  child-rel : ∀ {Γ A} {s : Obs Timeline Γ A} {ρ d} → Rel (subscribe s ρ) d → Rel (sub s ρ) d
  -- ⊥ᴰ shows nothing, so anything approximates it.
  bot-rel   : ∀ {A} {s : Subscribe A} → Rel s ⊥ᴰ

  -- The loop turns a related subscription into a run at time 0.
  loop-rel : ∀ {A} {s : Subscribe A} {d}
           → Rel s d → observe d 0 ⊑ loop (λ sink → s (sinkObserver sink) λ _ → done tt)

  -- Every finite prefix of a run unfolds finitely many `child`s, so some
  -- approximant already shows it; with soundness, the run is the lub.
  -- The one coinductive argument in the development.
  exhaust : ∀ {A} (o : PureObs [] A) → (∀ n → observe (⟦ o ⟧[ n ] []) 0 ⊑ runPure o)
          → runPure o ≈ observe (⟦ o ⟧ []) 0

-- THE FUNDAMENTAL LEMMA.  The recursion of `⟦_⟧[_]`: lexicographic on
-- (n , tree), so inductive — nothing here is guarded.
fundamental : ∀ n {Γ A} (o : PureObs Γ A) {ρ : Env Γ} {δ : DenEnv Γ}
            → RelEnv ρ δ → Rel (subscribe o ρ) (⟦ o ⟧[ n ] δ)
fundamental n       (cold c)         e = cold-rel c
fundamental n       (of xs)          e = of-rel xs
fundamental n       (map f s)        e = map-rel f (child-rel (fundamental n s e))
fundamental n       (scan f z s)     e = scan-rel f z (child-rel (fundamental n s e))
fundamental n       (takeWhile p s)  e = takeWhile-rel p (child-rel (fundamental n s e))
fundamental n       (merge s t)      e = merge-rel (child-rel (fundamental n s e))
                                                   (child-rel (fundamental n t e))
fundamental n       (flatMap op f s) e = flatMap-rel op (λ a → child-rel (fundamental n (f a) e))
                                                        (child-rel (fundamental n s e))
fundamental n       (share s b)      e = share-rel e (fundamental n s e)
                                                   (λ r → child-rel (fundamental n b (r ∷ e)))
fundamental n       (shared i)       e = shared-rel i e
fundamental zero    (defer l)        e = bot-rel
fundamental (suc n) (defer l)        e = child-rel (fundamental n (Later.force l) e)

-- Each approximant is sound for the run.
sound : ∀ {A} (o : PureObs [] A) n → observe (⟦ o ⟧[ n ] []) 0 ⊑ runPure o
sound o n = loop-rel (fundamental n o [])

adequacy : ∀ {A} (o : PureObs [] A) → runPure o ≈ observe (⟦ o ⟧ []) 0
adequacy o = exhaust o (sound o)
