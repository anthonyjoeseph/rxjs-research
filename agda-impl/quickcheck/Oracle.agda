{-# OPTIONS --guardedness #-}

-- ONE PROGRAM, THREE SEMANTICS.  A `Prog` is handed to the denotation
-- (its emission set, listed by `quickcheck.Tabled`), the pure
-- operational semantics or the IO one, each through its one entry point,
-- the same `toObs` and the same unfolding budget, and the result is
-- rendered as JSON for whoever is comparing — `Quickcheck` here, the
-- TypeScript oracle through `Oracle-CLI`.
--
-- Each engine gives a `quickcheck.Trace`.  The IO engine's trace is its
-- log, read once nothing is left to wait for — a program that never
-- finishes never returns.
module quickcheck.Oracle where

open import Agda.Builtin.IO using (IO)
open import Data.List using (List; []; _∷_; reverse)
open import Data.List.Relation.Unary.All using ([])
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _*_; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import IO.Primitive.Core using (pure; _>>=_)
open import IO.Primitive.Finite using (putStrLn)

import denotation.Events as Events
open import denotation.Events using (Time; root)
open import operation.PureObservable using () renaming (run to runᴾ)
open import operation.Observable using (IORef; IOCold; Emit; Observable; subscribe; forkIO; Signal; newSignal; raise; await; newIORef; readIORef; writeIORef)
open import quickcheck.Clock using (Clock; newClock; fire; fromTimeline)
import Tree as T
open import quickcheck.Ty using (⟦_⟧ᵀ)
open import quickcheck.Code using (Leaf; Prog; toObs; timeline)
open import quickcheck.Trace using (Event; tick; val; Trace; _▸_; completed; silent; cut; traceML; depth; showTrace)
open import quickcheck.Tabled using (listT; traceT)

-- The emission set's listing, `u` bounding each `μ`'s unfolding and the
-- approximant deep enough that no `defer` is cut; `cut` if it lists
-- nothing.
denoteTrace : ∀ {t} → ℕ → Prog t → Trace ⟦ t ⟧ᵀ
denoteTrace u p with listT (depth u p) (toObs timeline u p [] [] []) [] root
... | just l  = traceT l
... | nothing = [] ▸ cut

-- The tick a pure run is read up to.  A looping program works forever,
-- so it is read up to a time, as the rxjs side reads it; every finite
-- program is done well before.  A shorter read is only ever cut.
horizon : Time
horizon = 100

-- The pure semantics run for many more steps than the trace's budget:
-- each value or stall of a frame is several steps of work.
pureTrace : ∀ {t} → ℕ → ℕ → Prog t → Trace ⟦ t ⟧ᵀ
pureTrace u n p = traceML n (runᴾ (200 * n) horizon (toObs timeline u p [] [] []))

------------------------------------------------------------------------
-- The IO engine, logged

private
  logged : ∀ {A} → Maybe Time → List (Time × A) → List (Event A)
  logged _        []             = []
  logged nothing  ((t , a) ∷ xs) = tick t ∷ val a ∷ logged (just t) xs
  logged (just s) ((t , a) ∷ xs) = if s ≡ᵇ t then val a ∷ logged (just t) xs else tick t ∷ val a ∷ logged (just t) xs

-- The program, run through the bare `subscribe` as any program is, with
-- the harness's clock behind its inputs.  Around it, three colds of the
-- harness's own: one per value, logging it with the clock's time; a
-- probe merged beside it, which forks the thread that fires the timers;
-- and a marker concatenated after it, recording its completion.  The
-- forked thread first asks the probe's `closed`, which waits out the
-- subscribe burst on the engine's lock; it then fires every timer, and
-- once none is left the log is read, newest first.  Never `cut`: a
-- program that never finishes never returns.
ioTraceWith : ∀ {t} → (∀ {A} → Observable A → IO ⊤) → ℕ → Prog t → IO (Trace ⟦ t ⟧ᵀ)
ioTraceWith {t} sub u p =
  newClock >>= λ ck → newIORef false >>= λ fin → newIORef [] >>= λ log → newIORef 0 >>= λ names → newSignal >>= λ over →
  forkIO (sub (wrapped ck fin log over (toObs (leaf ck names) u p [] [] []))) >>= λ _ →
  await over >>= λ _ →
  readIORef log >>= λ xs → readIORef fin >>= λ c →
  pure (logged nothing (reverse xs) ▸ (if c then completed else silent))
  where
    -- the leaves, each name drawn from the run's supply
    leaf : Clock → IORef ℕ → Leaf IOCold
    leaf ck names .Leaf.scripted s = fromTimeline ck names (Leaf.scripted timeline s)
    leaf ck names .Leaf.named      = fromTimeline ck names Events.fresh

    doing : ∀ {A} → IO ⊤ → IOCold A
    doing m = record { Internal = ⊤ ; create = λ e → record
      { subscription = m >>= λ _ → Emit.complete e ; teardown = λ _ → pure tt } }

    wrapped : Clock → IORef Bool → IORef (List (Time × ⟦ t ⟧ᵀ)) → Signal → Observable ⟦ t ⟧ᵀ → Observable ⊤
    wrapped ck fin log over o = T.flatMap (T.mergeᶠ (just 1)) (λ b → if b then body else T.cold (doing (writeIORef fin true)))
                                  (T.of (true ∷ false ∷ []))
      where
        tap : ⟦ t ⟧ᵀ → IOCold ⊤
        tap a = doing (readIORef (Clock.now ck) >>= λ s → readIORef log >>= λ xs → writeIORef log ((s , a) ∷ xs))

        probe : IOCold ⊤
        probe = record { Internal = ⊤ ; create = λ e → record
          { subscription = forkIO (Emit.closed e >>= λ _ → fire ck >>= λ _ → raise over) >>= λ _ → Emit.complete e
          ; teardown = λ _ → pure tt } }

        body : Observable ⊤
        body = T.merge (T.flatMap (T.mergeᶠ nothing) (λ a → T.cold (tap a)) o) (T.cold probe)

------------------------------------------------------------------------
-- One engine's trace, printed

ioTrace : ∀ {t} → ℕ → Prog t → IO (Trace ⟦ t ⟧ᵀ)
ioTrace = ioTraceWith subscribe

data Engine : Set where
  denotational pureOp ioOp : Engine

-- `u` bounds each `μ`'s unfolding; `n` bounds a pure trace.
oracle : ∀ {t} → Engine → ℕ → ℕ → Prog t → IO ⊤
oracle {t} denotational u n p = putStrLn (showTrace t (denoteTrace u p))
oracle {t} pureOp       u n p = putStrLn (showTrace t (pureTrace u n p))
oracle {t} ioOp         u n p = ioTrace u p >>= λ tr → putStrLn (showTrace t tr)
