{-# OPTIONS --guardedness --large-indices #-}

-- THE FOCUS: a firing cold's step, lifted through the subscriptions
-- around it to the meaning's next step.  At each level the cold's step
-- comes first when every sibling's next event comes later (`Clear`): a
-- flatMap's other lanes and its outer, a connect's body beside its
-- source, its source beside its body.  A connect shows its source's
-- step below the source's own position, at `ix 0`.
module Focus where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; Σ)
open import Data.Bool using (true; false)
open import Data.Unit using (⊤)
open import Level using (Lift; lower; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import denotation.MonotonicList using (Pos; Frame; ix; _<ᵖ_)
import denotation.Unfold as U
open import denotation.Unfold using (Srcs)
open import operation.AbstractObservable using (module Run)
open import operation.PureObservable using (Pureᴾ; World; Sink; module Pure)
open import Realize using (module Realizing)

module Focusing (R : Set) where
  open Run (Pureᴾ R) using (Env)
  open Realizing R using (Sub; Lane; Phase; nodeOf; Holding; firing; Spot; SpotLanes; cold-here; in-map; in-scan; in-take; in-outer
                         ; in-lanes; in-source; in-body; in-defer; this-lane; next-lane; spot-of; phaseAt; module At)
  open Pure R using (State; get)

  -- A next event, if any, after `q`.
  After : Pos → Maybe Pos → Set
  After q nothing  = ⊤
  After q (just k) = q <ᵖ k ≡ true

  Later : ∀ {A} → Pos → U.Node A → Set
  Later q n = After q (U.headˢ (U.step n))

  Up : Set → Set₁
  Up = Lift (suc zero)

  Open : ∀ {A} → Pos → Maybe (U.Node A) → Set
  Open q nothing  = ⊤
  Open q (just n) = Later q n

  -- Where the cold's step at `q` is shown at the root.
  mutual
    lift : ∀ {h Δ A B} {t : Sub h Δ A} {s : Sink h B} {hd} → Spot t s hd → Pos → Pos
    lift cold-here     q = q
    lift (in-map p)    q = lift p q
    lift (in-scan p)   q = lift p q
    lift (in-take p)   q = lift p q
    lift (in-outer p)  q = lift p q
    lift (in-lanes p)  q = liftLanes p q
    lift (in-source p) q = lift p q ++ [ ix 0 ]
    lift (in-body p)   q = lift p q
    lift (in-defer p)  q = lift p q

    liftLanes : ∀ {h Δ B C} {ls : List (Lane h Δ B)} {s : Sink h C} {hd} → SpotLanes ls s hd → Pos → Pos
    liftLanes (this-lane p) q = lift p q
    liftLanes (next-lane p) q = liftLanes p q

  module On {h : World} (H : All (Pure.Val R h) h) where
    open At H

    -- Every sibling on the way up next steps after the cold's step there.
    mutual
      Clear : ∀ {Δ A B} {t : Sub h Δ A} {s : Sink h B} {hd} → Spot t s hd → Env Δ h → Srcs Δ → Pos → Set₁
      Clear cold-here                                  E ρ q = Up ⊤
      Clear (in-map p)                                 E ρ q = Clear p E ρ q
      Clear (in-scan p)                                E ρ q = Clear p E ρ q
      Clear (in-take p)                                E ρ q = Clear p E ρ q
      Clear (in-outer {ls = ls} p)                     E ρ q = Clear p E ρ q × All (Later (lift p q)) (partLanes ls E ρ)
      Clear (in-lanes {t = so} p)                      E ρ q = ClearLanes p E ρ q × Up (Open (liftLanes p q) (part so E ρ))
      Clear (in-source {S = S} {s₀ = s₀} {u = u} p)    E ρ q =
        Clear p E ρ q × Up (Open (lift p q ++ [ ix 0 ]) (part u (S ∷ E) (s₀ ∷ ρ)))
      Clear (in-body {S = S} {s₀ = s₀} {m = m} p)      E ρ q = Clear p (S ∷ E) (s₀ ∷ ρ) q × Up (Open (lift p q) m)
      Clear (in-defer p)                               E ρ q = Clear p E ρ q

      ClearLanes : ∀ {Δ B C} {ls : List (Lane h Δ B)} {s : Sink h C} {hd} → SpotLanes ls s hd → Env Δ h → Srcs Δ → Pos → Set₁
      ClearLanes (this-lane {ls = ls} p) E ρ q = Clear p E ρ q × All (Later (lift p q)) (partLanes ls E ρ)
      ClearLanes (next-lane {l = l} p)   E ρ q = ClearLanes p E ρ q × All (Later (liftLanes p q)) (partLanes (l ∷ []) E ρ)

    postulate
      -- A live cold's silent step, every sibling above it clear, is the
      -- step of what is open around it, lifted, to the witness with its
      -- phase moved: no gate above a live cold is closed (`Gated`).
      lift-skip : ∀ {Δ A B} {t : Sub h Δ A} {s : Sink h B} {hd} (sp : Spot t s hd) {E ρ q} {ph : Phase B}
                → spentʰ hd ≡ false → Gated t E ρ → Clear sp E ρ q
                → U.step (nodeOf (phaseAt sp)) ≡ U.skipˢ q (nodeOf ph)
                → Σ (U.Node A) λ n → Σ (U.Node A) λ n₁ → part t E ρ ≡ just n × U.step n ≡ U.skipˢ (lift sp q) n₁
                                                       × part (stepAt sp ph E ρ) E ρ ≡ just n₁

  postulate
    -- At a burst boundary every other node's next event comes after the
    -- firing cold's step: another cold's is a queued timer's, past the
    -- run's position (`Ordered`, `Timed`) and so past every step of a
    -- frame the run is short of (`behind`); a joiner's copy is its
    -- source's (`caught`), shown below its own join point (`past`).
    clear : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {b : Frame A u}
          → (H : Holding (firing s hd τ r i b ∷ []) c st) → lower (get (State.heap st) hd) ≡ false
          → ∀ {q} {ph : Phase A} → U.burstˢ τ r i b ≡ U.skipˢ q (nodeOf ph)
          → On.Clear (State.heap st) (spot-of (Holding.tree H) (Holding.firing≡ H)) [] [] q
