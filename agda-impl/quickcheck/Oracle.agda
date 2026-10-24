{-# OPTIONS --guardedness #-}

-- ONE PROGRAM, THREE SEMANTICS.  A `Prog` is handed to the denotation,
-- the pure operational semantics or the IO one, each through its one
-- entry point, the same `toObs` and the same unfolding budget, and the result is rendered as JSON for whoever is
-- comparing — `Quickcheck` here, the TypeScript oracle through
-- `Oracle-CLI`.
--
-- Each engine gives a TRACE: frame times and values in order, then how
-- it ended.  A timeline can be infinite, even inside one frame, so a pure
-- trace is read under a step budget and may end `cut`.  The IO engine's
-- trace is its log, read once nothing is left to wait for — a program
-- that never finishes never returns.
module quickcheck.Oracle where

open import Agda.Builtin.IO using (IO)
open import Data.List using (List; []; _∷_; reverse) renaming (map to mapL)
open import Data.List.Relation.Unary.All using ([])
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≡ᵇ_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String using (String; _++_; intersperse)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import IO.Primitive.Core using (pure; _>>=_)
open import IO.Primitive.Finite using (putStrLn)

import denotation.MonotonicList.Events as Events
open import denotation.MonotonicList.Events using (ML; Burst; Burst∞; ML∞; done; quiet; at; emit; stall; close; Time; root)
open import denotation.MonotonicList using (observe; ticks)
open import denotation.Denote using (⟦_⟧[_])
open import operation.PureObservable using () renaming (run to runᴾ)
open import port.operation.PureObservable using () renaming (run to runᴹ)
open import port.operation.Observable using () renaming (subscribe to subscribeᴹ)
open import operation.Observable using (IORef; IOCold; Emit; Observable; subscribe; forkIO; Signal; newSignal; raise; await; newIORef; readIORef; writeIORef)
open import quickcheck.Clock using (Clock; newClock; fire; fromTimeline)
import Tree as T
open import quickcheck.Ty using (⟦_⟧ᵀ; showᵀ)
open import quickcheck.Code using (Code; Leaf; cold; fresh; empty; of; map; scan; takeWhile; flatMap; connect; connected; μ; var; defer; Prog; toObs; timeline)

------------------------------------------------------------------------
-- Traces

data Event (A : Set) : Set where
  tick : Time → Event A     -- a frame begins
  val  : A → Event A        -- a value, in the current frame

data End : Set where
  completed silent cut : End

record Trace (A : Set) : Set where
  constructor _▸_
  field
    events : List (Event A)
    end    : End

-- One step of budget per frame, value or `stall`: a burst that spins
-- forever is cut, not hung.  A frame that emits nothing is not printed:
-- rxjs cannot show one.
mutual
  traceML : ∀ {A} → ℕ → ML A → Trace A
  traceML zero    _        = [] ▸ cut
  traceML (suc n) done     = [] ▸ completed
  traceML (suc n) quiet    = [] ▸ silent
  traceML (suc n) (at t b) = opening t (traceBurst n b)

  traceBurst : ∀ {A} → ℕ → Burst A → Trace A
  traceBurst zero    _          = [] ▸ cut
  traceBurst (suc n) (emit a k) = cons (val a) (traceBurst n (Burst∞.force k))
  traceBurst (suc n) (stall k)  = traceBurst n (Burst∞.force k)
  traceBurst (suc n) (close k)  = traceML n (ML∞.force k)

  cons : ∀ {A} → Event A → Trace A → Trace A
  cons e (es ▸ x) = (e ∷ es) ▸ x

  opening : ∀ {A} → Time → Trace A → Trace A
  opening t ((val a ∷ es) ▸ x) = cons (tick t) ((val a ∷ es) ▸ x)
  opening t tr                 = tr

------------------------------------------------------------------------
-- Running

-- Every `defer` on any path of the unfolded tree, so the approximant at
-- this index never reaches `⊥ᴰ`: on a cut tree the denotation is exact.
defers : ∀ {Γ Δᵍ Δ Θ t} → Code Γ Δᵍ Δ Θ t → ℕ
defers (cold _)              = 0
defers fresh                 = 0
defers empty                 = 0
defers (of _)                = 0
defers (map _ s)             = defers s
defers (scan _ _ s)          = defers s
defers (takeWhile _ _ s)     = defers s
defers (flatMap _ l s)       = defers l + defers s
defers (connect s b)         = defers s + defers b
defers (connected _)         = 0
defers (μ c)                 = defers c
defers (var _)               = 0
defers (defer c)             = suc (defers c)

depth : ∀ {t} → ℕ → Prog t → ℕ
depth u p = suc u * suc (defers p)

-- `u` bounds each `μ`'s unfolding; `n` bounds the trace.
denoteTrace : ∀ {t} → ℕ → ℕ → Prog t → Trace ⟦ t ⟧ᵀ
denoteTrace u n p = traceML n (ticks (observe (⟦ toObs timeline u p [] [] [] ⟧[ depth u p ] []) root))

-- The tick a pure run is read up to.  A looping program works forever,
-- so it is read up to a time, as the rxjs side reads it; every finite
-- program is done well before.  A shorter read is only ever cut.
horizon : Time
horizon = 100

-- The pure semantics run for many more steps than the trace's budget:
-- each value or stall of a frame is several steps of work.
pureTrace : ∀ {t} → ℕ → ℕ → Prog t → Trace ⟦ t ⟧ᵀ
pureTrace u n p = traceML n (runᴾ (200 * n) horizon (toObs timeline u p [] [] []))

-- The pointer-free engine's pure semantics (`port.operation.PureObservable`), under the same budget.
marksTrace : ∀ {t} → ℕ → ℕ → Prog t → Trace ⟦ t ⟧ᵀ
marksTrace u n p = traceML n (runᴹ (200 * n) horizon (toObs timeline u p [] [] []))

------------------------------------------------------------------------
-- JSON

showEvent : ∀ t → Event ⟦ t ⟧ᵀ → String
showEvent t (tick k) = "{\"tick\":" ++ showℕ k ++ "}"
showEvent t (val a)  = "{\"val\":" ++ showᵀ t a ++ "}"

showEnd : End → String
showEnd completed = "\"completed\""
showEnd silent    = "\"silent\""
showEnd cut       = "\"cut\""

showTrace : ∀ t → Trace ⟦ t ⟧ᵀ → String
showTrace t (es ▸ x) = "{\"events\":[" ++ intersperse "," (mapL (showEvent t) es) ++ "],\"end\":" ++ showEnd x ++ "}"

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

-- The same, through the pointer-free engine's IO runtime (`port.operation.Observable`).
marksIoTrace : ∀ {t} → ℕ → Prog t → IO (Trace ⟦ t ⟧ᵀ)
marksIoTrace = ioTraceWith subscribeᴹ

data Engine : Set where
  denotational pureOp ioOp marksIoOp : Engine

-- `u` bounds each `μ`'s unfolding; `n` bounds a pure trace.
oracle : ∀ {t} → Engine → ℕ → ℕ → Prog t → IO ⊤
oracle {t} denotational u n p = putStrLn (showTrace t (denoteTrace u n p))
oracle {t} pureOp       u n p = putStrLn (showTrace t (pureTrace u n p))
oracle {t} ioOp         u n p = ioTrace u p >>= λ tr → putStrLn (showTrace t tr)
oracle {t} marksIoOp    u n p = marksIoTrace u p >>= λ tr → putStrLn (showTrace t tr)
