{-# OPTIONS --guardedness #-}

-- ONE PROGRAM, THREE RUNTIMES.  A `Prog` is handed to the denotation, the
-- pure event loop or the IO runtime, through the same `toObs` and the same
-- unfolding budget, and the result is rendered as JSON for whoever is
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
open import Data.Bool using (true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≡ᵇ_; _<ᵇ_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String using (String; _++_; intersperse)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import IO.Primitive.Core using (pure; _>>=_)
open import IO.Primitive.Finite using (putStrLn)

open import denotation.MonotonicList.Events using (ML; Burst; Burst∞; ML∞; done; quiet; at; emit; stall; close; Time; root)
open import denotation.MonotonicList using (observe; ticks)
open import denotation.Denote using (⟦_⟧[_])
open import operation.Machine using (module Machine)
open import operation.Observable using (subscribe; fromTimeline; newIORef; readIORef; writeIORef)
open import quickcheck.Ty using (⟦_⟧ᵀ; showᵀ)
open import quickcheck.Code using (Code; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; μ; var; defer; Prog; toObs; timeline)

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

-- How many of a run's first n steps come by tick `horizon`.  A looping
-- program works forever, and its machine slows as its heap grows, so it is
-- read up to a time, as the rxjs side reads it; every finite program is
-- done well before.  A shorter read is only ever cut.
horizon : Time
horizon = 100

module _ {R : Set} where
  open Machine R using (tau; out; end; idle)

  until : ℕ → Machine.Trace R → ℕ
  until zero    _             = zero
  until (suc n) (tau t k)     = if horizon <ᵇ t then zero else suc (until n (Machine.Trace∞.force k))
  until (suc n) (out t _ _ k) = if horizon <ᵇ t then zero else suc (until n (Machine.Trace∞.force k))
  until (suc n) (end _)       = 1
  until (suc n) idle          = 1

-- The machine read for many more steps than the trace's budget: each
-- value or stall of a frame is several steps of work.
pureTrace : ∀ {t} → ℕ → ℕ → Prog t → Trace ⟦ t ⟧ᵀ
pureTrace {t} u n p = traceML n (Machine.prefix ⟦ t ⟧ᵀ (until (200 * n) (Machine.trace ⟦ t ⟧ᵀ (Machine.begin ⟦ t ⟧ᵀ o))) o)
  where o = toObs timeline u p [] [] []

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

-- Values are logged as they arrive, newest first, and read into a trace
-- once nothing is left to wait for.  Never `cut`: a program that never
-- finishes never returns.
ioTrace : ∀ {t} → ℕ → Prog t → IO (Trace ⟦ t ⟧ᵀ)
ioTrace u p = newIORef false >>= λ fin → newIORef [] >>= λ log → newIORef 0 >>= λ names → subscribe
  (toObs (λ s → fromTimeline names (timeline s)) u p [] [] [])
  (λ t a → readIORef log >>= λ xs → writeIORef log ((t , a) ∷ xs))
  (writeIORef fin true) >>= λ _ →
  readIORef log >>= λ xs → readIORef fin >>= λ c →
  pure (logged nothing (reverse xs) ▸ (if c then completed else silent))

------------------------------------------------------------------------
-- One engine's trace, printed

data Engine : Set where
  denotational pureOp ioOp : Engine

-- `u` bounds each `μ`'s unfolding; `n` bounds a pure trace.
oracle : ∀ {t} → Engine → ℕ → ℕ → Prog t → IO ⊤
oracle {t} denotational u n p = putStrLn (showTrace t (denoteTrace u n p))
oracle {t} pureOp       u n p = putStrLn (showTrace t (pureTrace u n p))
oracle {t} ioOp         u n p = ioTrace u p >>= λ tr → putStrLn (showTrace t tr)
