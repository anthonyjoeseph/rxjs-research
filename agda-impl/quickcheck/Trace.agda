{-# OPTIONS --guardedness #-}

-- A TRACE: frame times and values in order, then how it ended — what
-- each runtime is read as for comparing (`quickcheck.Oracle`).  A
-- timeline can be infinite, even inside one frame, so a trace is read
-- under a step budget and may end `cut`.
module quickcheck.Trace where

open import Data.List using (List; []; _∷_) renaming (map to mapL)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String using (String; _++_; intersperse)

open import denotation.Events using (ML; Burst; Burst∞; ML∞; done; quiet; at; emit; stall; close; Time)
open import quickcheck.Ty using (⟦_⟧ᵀ; showᵀ)
open import quickcheck.Code using (Code; cold; fresh; empty; of; map; scan; takeWhile; flatMap; connect; connected; μ; var; defer; Prog)

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
-- Unfolding

-- Every `defer` on any path of the unfolded tree, so the approximant at
-- this index never reaches `Op.⊥`: on a cut tree the denotation is exact.
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
