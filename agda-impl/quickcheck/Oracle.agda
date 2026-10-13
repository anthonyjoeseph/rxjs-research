{-# OPTIONS --guardedness #-}

-- ONE PROGRAM, THREE RUNTIMES.  A `Prog` is handed to the denotation, the
-- pure event loop or the IO runtime, through the same `toObs` and the same
-- unfolding budget, and the result is rendered as JSON for whoever is
-- comparing — `Quickcheck` here, the TypeScript oracle eventually.
--
-- The two pure engines give a TRACE: frame times and values in order,
-- then how it ended.  A timeline can be infinite, even inside one frame,
-- so a trace is read under a step budget and may end `cut`.  The IO
-- engine gives what `toArray` gives — the values, once the program
-- completes; a program that never completes never returns.
module quickcheck.Oracle where

open import Agda.Builtin.IO using (IO)
open import Data.List using (List; []; _∷_) renaming (map to mapL)
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String using (String; _++_; intersperse)
open import IO.Primitive.Core using (pure; _>>=_)

open import MonotonicList using (ML; Burst; Burst∞; ML∞; done; quiet; at; emit; stall; close; Time; observe)
open import Denote using (⟦_⟧[_])
open import PureObservable using (runPure)
open import Observable using (toArray; fromTimeline)
open import quickcheck.Ty
open import quickcheck.Code

data Engine : Set where
  denotational pureOp ioOp : Engine

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
-- forever is cut, not hung.
mutual
  traceML : ∀ {A} → ℕ → ML A → Trace A
  traceML zero    _        = [] ▸ cut
  traceML (suc n) done     = [] ▸ completed
  traceML (suc n) quiet    = [] ▸ silent
  traceML (suc n) (at t b) = cons (tick t) (traceBurst n b)

  traceBurst : ∀ {A} → ℕ → Burst A → Trace A
  traceBurst zero    _          = [] ▸ cut
  traceBurst (suc n) (emit a k) = cons (val a) (traceBurst n (Burst∞.force k))
  traceBurst (suc n) (stall k)  = traceBurst n (Burst∞.force k)
  traceBurst (suc n) (close k)  = traceML n (ML∞.force k)

  cons : ∀ {A} → Event A → Trace A → Trace A
  cons e (es ▸ x) = (e ∷ es) ▸ x

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
defers (takeWhile _ s)       = defers s
defers (flatten _ _ _ l s)   = defers l + defers s
defers (connect s b)         = defers s + defers b
defers (connected _)         = 0
defers (μ c)                 = defers c
defers (var _)               = 0
defers (defer c)             = suc (defers c)

depth : ∀ {t} → ℕ → Prog t → ℕ
depth u p = suc u * suc (defers p)

-- `u` bounds each `μ`'s unfolding; `n` bounds the trace.
denoteTrace : ∀ {t} → ℕ → ℕ → Prog t → Trace ⟦ t ⟧ᵀ
denoteTrace u n p = traceML n (observe (⟦ toObs timeline u p [] [] [] ⟧[ depth u p ] []) 0)

pureTrace : ∀ {t} → ℕ → ℕ → Prog t → Trace ⟦ t ⟧ᵀ
pureTrace u n p = traceML n (runPure (toObs timeline u p [] [] []))

ioValues : ∀ {t} → ℕ → Prog t → IO (List ⟦ t ⟧ᵀ)
ioValues u p = toArray (toObs (λ s → fromTimeline (timeline s)) u p [] [] [])

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

oracle : ∀ {t} → Engine → ℕ → ℕ → Prog t → IO String
oracle {t} denotational u n p = pure (showTrace t (denoteTrace u n p))
oracle {t} pureOp       u n p = pure (showTrace t (pureTrace u n p))
oracle {t} ioOp         u n p = ioValues u p >>= λ xs → pure ("{\"values\":" ++ showᵀ (listᵗ t) xs ++ "}")
