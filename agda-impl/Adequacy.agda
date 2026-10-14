{-# OPTIONS --guardedness #-}

-- THE LINK.  The pure runtime and the denotation agree: the limit of the
-- pure run's approximants is the denotation's limit, observed at the
-- root, with positions forgotten down to ticks.
--
-- Both sides are chains of approximants built the same way — approximant
-- n compiles n nested `defer`s, and past that shows nothing — so each
-- half compares approximant n with approximant n.  Run n is below
-- approximant n, which is below the run, and `squeeze` meets the limits.
--
-- BELOW: the run's record, ghost positions and all, is placed against
-- the events the root is shown (`operation.Placed`), so it shows nothing
-- they do not.  ABOVE: a logical relation between a `Subscribe` and a
-- timeline, by induction on (n , tree), one operator at a time: with
-- budget enough, the kernel shows everything its timeline does.  Nothing
-- is coinductive except the last step, from approximants to limits.
--
-- The IO runtime has no theorem of its own, and needs none: it is the
-- same engine over a different monad, with its recursion closed by `fix`
-- rather than by unfolding.  The oracle compares it to the TypeScript.
module Adequacy where

open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using ([]; _∷_; lookup)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_)
open import Data.Nat.Properties using (≤-refl; n≤1+n; m≤m⊔n; m≤n⊔m)
open import Level using (lower)

open import Tree using (cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer; Later)
open import operation.Placed using (Up; module Ran)
open import operation.AbstractObservable using (module Run)
open import operation.Budget using (module Approx)
open import operation.PureObservable using (Pureᴾ; PureObs; module Pure; toArray) renaming (_⊑_ to _≤ʷ_)
open import denotation.MonotonicList using (ML; Burst; Burst∞; ML∞; done; quiet; at; emit; stall; close; Time; MonotonicList; coldᴰ; observe; root; ticks; Timeline; emptyᴰ; ofᴰ; mapᴰ; scanᴰ; takeWhileᴰ; flatMapᴰ; deferᴰ; connectᴰ; ⊥ᴰ)
open import denotation.Order using (_⊑_; ⊑-trans; _≃_; ≃-trans; limit; Chain; squeeze; limit-ub; limit-least)
open import denotation.Denote using (DenEnv; flatOp; ⟦_⟧[_]; ⟦_⟧)

-- The pure run: the limit of its approximants.
run : ∀ {A} → PureObs [] A → ML A
run o = limit λ n → toArray n o

-- Approximant n of the denotation, as the run reports one.
approxAt : ∀ {A} → PureObs [] A → ℕ → ML A
approxAt o n = ticks (observe (⟦ o ⟧[ n ] []) root)

-- A place along a cold's timeline: a frame to come, or inside one.
data Along (A : Set) : Set where
  ahead  : ML A → Along A
  inside : Burst A → Along A

-- A TIMELINE THAT RISES: no frame before tick t, each after the last.
mutual
  record Rises {A : Set} (t : Time) (x : Along A) : Set where
    coinductive
    field rises : Rise t x

  Rise : ∀ {A} → Time → Along A → Set
  Rise t (ahead done)              = ⊤
  Rise t (ahead quiet)             = ⊤
  Rise t (ahead (at t′ b))         = t ≤ t′ × Rises (suc t′) (inside b)
  Rise t (inside (emit _ k))       = Rises t (inside (Burst∞.force k))
  Rise t (inside (stall k))        = Rises t (inside (Burst∞.force k))
  Rise t (inside (close k))        = Rises t (ahead (ML∞.force k))

-- Every cold a program reaches within n `defer`s rises.
Rising : ∀ {Γ A} → ℕ → PureObs Γ A → Set
Rising n       (cold c)          = Rises 0 (ahead (lower c))
Rising n       empty             = ⊤
Rising n       (of xs)           = ⊤
Rising n       (map f s)         = Rising n s
Rising n       (scan f z s)      = Rising n s
Rising n       (takeWhile i p s) = Rising n s
Rising n       (flatMap op f s)  = (∀ a → Rising n (f a)) × Rising n s
Rising n       (connect s b)     = Rising n s × Rising n b
Rising n       (connected i)     = ⊤
Rising zero    (defer l)         = ⊤
Rising (suc n) (defer l)         = Rising n (Later.force l)

-- The fundamental lemma, for a run whose root observes `R`.
module Link (R : Set) where
  open Run (Pureᴾ R)
  open Pure R using (runPure; compileᴺ)
  open Approx R using (runPure-mono)
  open Ran R using (ran; Recorded; recorded-⊑)

  postulate
    -- THE EDGE where `adequacy` meets a cold whose ticks fall.  `ML` says
    -- its ticks increase and does not carry it, so this is false: the
    -- denotation places a frame at its own tick, ahead of a sibling's
    -- frame at the tick already reached; the engine sets its timer for
    -- now, behind every timer already due.  Whether `ML` carries it,
    -- `adequacy` assumes it, or the denotation clamps a late frame to now
    -- is Anthony's call.
    -- REFUTED: `git show 26f0a574` derives `⊥` from `rising`.
    rising : ∀ n (o : PureObs [] R) → Rising n o

    -- An approximant's ticks never fall, its colds' rising.
    ticks-up : ∀ n (o : PureObs [] R) → Rising n o → Up 0 (observe (⟦ o ⟧[ n ] []) root)

    -- "Subscribing with `s` at any position p, in any heap, shows at least
    -- what `d` shows a subscriber arriving at p, ticks for ticks, on an
    -- engine with budget enough."
    Rel   : ∀ {A w} → Subscribe A w → MonotonicList A → Set₁
    -- A subject and the handle `connectᴰ` passed its body agree: joining
    -- one shows what joining the other shows, at any join time, both ways
    -- as `Rel`.
    RelSubj : ∀ {A w} → Subject A w → MonotonicList A → Set₁
    -- A subject made in one world is the same subject in every later one.
    RelSubj-wk : ∀ {A w v} {st : Subject A w} {x} (σ : w ≤ʷ v) → RelSubj st x → RelSubj (wkSubject σ st) x

  postulate
    -- "Subscribing with `s` at any position p, in any heap, delivers its
    -- observer each value at its own event of what `d` shows a subscriber
    -- at p, in order, and its completion at the end; never anything past
    -- them; and once nothing it set is left to run, nothing more."  The
    -- bound half, positionally.  Not at-most alone: a run that goes dry
    -- must meet a denotation that falls silent there, `Placed`'s `quiets`.
    Below     : ∀ {A w} → Subscribe A w → MonotonicList A → Set₁
    -- A subject and the handle `connectᴰ` passed its body agree as `Below`
    -- for every join.
    BelowSubj : ∀ {A w} → Subject A w → MonotonicList A → Set₁
    BelowSubj-wk : ∀ {A w v} {st : Subject A w} {x} (σ : w ≤ʷ v) → BelowSubj st x → BelowSubj (wkSubject σ st) x

  data BelowEnv {w} : ∀ {Γ} → Env Γ w → DenEnv Γ → Set₁ where
    []  : BelowEnv [] []
    _∷_ : ∀ {Γ A} {st : Subject A w} {x : MonotonicList A} {ρ : Env Γ w} {δ : DenEnv Γ}
        → BelowSubj st x → BelowEnv ρ δ → BelowEnv (st ∷ ρ) (x ∷ δ)

  wkBelowEnv : ∀ {Γ w v} {ρ : Env Γ w} {δ : DenEnv Γ} (σ : w ≤ʷ v) → BelowEnv ρ δ → BelowEnv (wkEnv σ ρ) δ
  wkBelowEnv σ []      = []
  wkBelowEnv σ (r ∷ e) = BelowSubj-wk σ r ∷ wkBelowEnv σ e

  postulate
    -- One per operator, each kernel's bound against its denotation.
    empty-below     : ∀ {A w} → Below {A} {w} emptyᴷ emptyᴰ
    of-below        : ∀ {A w} (xs : List A) → Below {w = w} (ofᴷ xs) (ofᴰ xs)
    map-below       : ∀ {A B w} {s : Subscribe A w} {d} (f : A → B) → Below s d → Below (mapᴷ f s) (mapᴰ f d)
    scan-below      : ∀ {A B w} {s : Subscribe A w} {d} (f : B → A → B) z → Below s d → Below (scanᴷ f z s) (scanᴰ f z d)
    takeWhile-below : ∀ {A w} {s : Subscribe A w} {d} i p → Below s d → Below (takeWhileᴷ i p s) (takeWhileᴰ i p d)
    flatMap-below   : ∀ {A B w} {s : Subscribe A w} {d} op {f : A → Subscribe B w} {g}
                    → (∀ a → Below (f a) (g a)) → Below s d → Below (flatMapᴷ op f s) (flatMapᴰ (flatOp op) g d)
    connected-below : ∀ {Γ A w} {ρ : Env Γ w} {δ} (i : A ∈ Γ) → BelowEnv ρ δ
                    → Below (joinᴷ (lookup ρ i)) (lookup δ i)
    -- A frame falling behind the clock is placed at the clock's tick by
    -- the engine and at its own by the denotation: `rising`'s edge.
    cold-below      : ∀ {A w} (c : Timeline A) → Rises 0 (ahead (lower c)) → Below {w = w} (via (startCold c)) (coldᴰ (lower c))
    -- Every joiner of the allocated subject is held to the hot handle.
    connect-below   : ∀ {A B w} {s : Subscribe A w} {d} {b : ∀ {v} → w ≤ʷ v → Subject A v → Subscribe B v}
                        {e : MonotonicList A → MonotonicList B}
                    → Below s d → (∀ {v} (σ : w ≤ʷ v) {st r} → BelowSubj st r → Below (b σ st) (e r))
                    → Below (connectᴷ s b) (connectᴰ d e)
    defer-below     : ∀ {A w} {s : Subscribe A w} {d} → Below s d → Below (deeper s) (deferᴰ d)
    bot-below       : ∀ {A w} → Below {A} {w} ⊥ᴷ ⊥ᴰ

    -- `Below` at the root, on every budget: the record the run leaves.
    run-below : ∀ {s : Subscribe R []} {d} → Below s d → ∀ m → Recorded (ran m s) (observe d root)

  -- THE BOUND HALF'S FUNDAMENTAL LEMMA, by the recursion `fundamental`
  -- shares.
  below : ∀ n {Γ A w} (o : PureObs Γ A) → Rising n o → {ρ : Env Γ w} {δ : DenEnv Γ}
        → BelowEnv ρ δ → Below (compileᴺ n o ρ) (⟦ o ⟧[ n ] δ)
  below n       (cold c)          u        e = cold-below c u
  below n       empty             u        e = empty-below
  below n       (of xs)           u        e = of-below xs
  below n       (map f s)         u        e = map-below f (below n s u e)
  below n       (scan f z s)      u        e = scan-below f z (below n s u e)
  below n       (takeWhile i p s) u        e = takeWhile-below i p (below n s u e)
  below n       (flatMap op f s)  (v , u)  e = flatMap-below op (λ a → below n (f a) (v a) e) (below n s u e)
  below n       (connect s b)     (u , v)  e = connect-below (below n s u e) (λ σ r → below n b v (r ∷ wkBelowEnv σ e))
  below n       (connected i)     u        e = connected-below i e
  below zero    (defer l)         u        e = bot-below
  below (suc n) (defer l)         u        e = defer-below (below n (Later.force l) u e)

  -- THE BOUND HALF, where the run can see it: approximant m of the
  -- engine leaves its record placed against the events approximant n of
  -- the denotation shows the root, each value at its own event.
  places : ∀ n (o : PureObs [] R) → Rising n o → ∀ m → Recorded (ran m (compileᴺ n o [])) (observe (⟦ o ⟧[ n ] []) root)
  places n o u = run-below (below n o u [])

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
    connected-rel : ∀ {Γ A w} {ρ : Env Γ w} {δ} (i : A ∈ Γ) → RelEnv ρ δ
                  → Rel (joinᴷ (lookup ρ i)) (lookup δ i)
    -- Only for a timeline that rises: one that falls is `rising`'s edge.
    cold-rel      : ∀ {A w} (c : Timeline A) → Rises 0 (ahead (lower c)) → Rel {w = w} (via (startCold c)) (coldᴰ (lower c))
    -- The subject `connectᴷ` allocates, fed by the source after the body
    -- has subscribed, agrees with the hot handle `connectᴰ` passes; then
    -- the body runs under both.
    --
    -- False wherever the source outlives what the body shows of it:
    -- `connectᴰ` drops the source's events.  A body that does not consume
    -- them shows past a source that spins, where the engine — and rxjs, by
    -- overflowing — stops the whole run; and shows silence over a source
    -- that runs forever, which the engine, still firing its timers, can
    -- never report.  Cutting the run at a spin repairs only the first.
    -- Keeping the source's events as `skip`s repairs both, but rxjs runs a
    -- source's subscribe burst to its end even after the body has ended.
    -- Which, or `adequacy` assuming neither, is Anthony's call.
    -- REFUTED: `git show f5256988` derives `⊥` from `run-rel`.
    -- REFUTED: `git show e6c9d03a` derives `⊥` from `run-rel`.
    connect-rel   : ∀ {A B w} {s : Subscribe A w} {d} {b : ∀ {v} → w ≤ʷ v → Subject A v → Subscribe B v}
                      {e : MonotonicList A → MonotonicList B}
                  → Rel s d → (∀ {v} (σ : w ≤ʷ v) {st r} → RelSubj st r → Rel (b σ st) (e r))
                  → Rel (connectᴷ s b) (connectᴰ d e)
    -- `deferᴰ` adds one `skip`, a `stall` once reported, invisible either
    -- way, and subscribes its body one level down, as `deeper` does.
    defer-rel     : ∀ {A w} {s : Subscribe A w} {d} → Rel s d → Rel (deeper s) (deferᴰ d)
    -- A cut-off `defer` on both sides: each shows nothing.
    bot-rel       : ∀ {A w} → Rel {A} {w} ⊥ᴷ ⊥ᴰ

    -- THE ENGINE'S FACT, `Rel` at the root: in the limit of its budget, a
    -- related run shows at least what the denotation shows there.
    run-rel : ∀ {s : Subscribe R []} {d}
            → Rel s d → ticks (observe d root) ⊑ limit (λ m → runPure m s)

    -- A deeper approximant of the denotation shows more.
    approx-chain  : (o : PureObs [] R) → Chain (approxAt o)

    -- Observing at the root, then forgetting positions, commutes with the
    -- limit that `⟦_⟧` takes.
    ⟦⟧-limit : (o : PureObs [] R) → limit (approxAt o) ≃ ticks (observe (⟦ o ⟧ []) root)

  -- The run's approximants are a chain.
  toArray-chain : (o : PureObs [] R) → Chain (λ n → toArray n o)
  toArray-chain o n = runPure-mono o (n≤1+n n) (n≤1+n n)

  -- Running approximant n of the compiler is below the run, whose
  -- approximants compile ever more.
  diagonal : ∀ n (o : PureObs [] R) → limit (λ m → runPure m (compileᴺ n o [])) ⊑ run o
  diagonal n o = limit-least (λ m → runPure-mono {n = n} o (n≤1+n m) ≤-refl)
                   (λ m → ⊑-trans (runPure-mono {n = n} o (m≤m⊔n m n) (m≤n⊔m m n)) (limit-ub (toArray-chain o) (m ⊔ n)))

  mutual
    -- THE FUNDAMENTAL LEMMA.  Approximant n against approximant n, by the
    -- recursion both share: lexicographic on (n , tree), so inductive.
    fundamental : ∀ n {Γ A w} (o : PureObs Γ A) → Rising n o → {ρ : Env Γ w} {δ : DenEnv Γ}
                → RelEnv ρ δ → Rel (compileᴺ n o ρ) (⟦ o ⟧[ n ] δ)
    fundamental n       (cold c)          u        e = cold-rel c u
    fundamental n       empty             u        e = empty-rel
    fundamental n       (of xs)           u        e = of-rel xs
    fundamental n       (map f s)         u        e = map-rel f (fundamental n s u e)
    fundamental n       (scan f z s)      u        e = scan-rel f z (fundamental n s u e)
    fundamental n       (takeWhile i p s) u        e = takeWhile-rel i p (fundamental n s u e)
    fundamental n       (flatMap op f s)  (v , u)  e = flatMap-rel op (λ a → fundamental n (f a) (v a) e) (fundamental n s u e)
    fundamental n       (connect s b)     (u , v)  e = connect-rel (fundamental n s u e) (λ σ r → fundamental n b v (r ∷ wkRelEnv σ e))
    fundamental n       (connected i)     u        e = connected-rel i e
    fundamental zero    (defer l)         u        e = bot-rel
    fundamental (suc n) (defer l)         u        e = defer-rel (fundamental n (Later.force l) u e)

  -- Each approximant of the denotation is below the run.
  sound : (o : PureObs [] R) (n : ℕ) → approxAt o n ⊑ run o
  sound o n = ⊑-trans (run-rel (fundamental n o (rising n o) [])) (diagonal n o)

  -- Each approximant of the run is below the denotation's.
  complete : (o : PureObs [] R) (n : ℕ) → toArray n o ⊑ approxAt o n
  complete o n = recorded-⊑ (ran n (compileᴺ n o [])) (ticks-up n o (rising n o)) (places n o (rising n o) n)

adequacy : ∀ {A} (o : PureObs [] A) → run o ≃ ticks (observe (⟦ o ⟧ []) root)
adequacy {A} o = ≃-trans (squeeze (toArray-chain o) (approx-chain o) (sound o) (complete o)) (⟦⟧-limit o)
  where open Link A
