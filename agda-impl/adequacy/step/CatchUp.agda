{-# OPTIONS --guardedness --large-indices #-}

-- THE CATCH-UP: after a firing cold's step at `F`, every joiner's copy
-- of a source the step moved takes that source's steps, each shown
-- below its join point, and a connect shows its source's below the
-- source's own, at `ix 0`.  Every such step lies under `F` and every
-- other next event past all of them (`Beyond F`), so the meaning takes
-- exactly these, silently, in whatever order their positions give.
module adequacy.step.CatchUp where

open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using (All; head)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc; _+_)
open import Data.Nat.Properties using (n<1+n; +-monoʳ-<)
open import Data.Product using (_×_; Σ; _,_)
open import Data.Bool using (true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Level using (Lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import denotation.MonotonicList using (Pos; Frame; Frame∞; From; From∞; ix; sub; last; emit; stall; close; done; quiet; at; _<ᵖ_; <ᵖ-ix-lt; <ᵖ-ix-last)
import denotation.Unfold as U
open import operation.AbstractObservable using (module Run)
open import operation.PureObservable using (Pureᴾ; Sink; module Pure)
open import adequacy.Realize using (module Realizing)
open import adequacy.step.Focus using (Beyond; burst-head; module Shape)

-- Silent steps under `F`, to a node `P` holds of.
data Settle {A : Set} (F : Pos) (P : U.Node A → Set) : U.Node A → U.Node A → Set₁ where
  stop : ∀ {c} → P c → Settle F P c c
  go   : ∀ {c c₁ c′} Y → U.step c ≡ U.skipˢ (F ++ Y) c₁ → Settle F P c₁ c′ → Settle F P c c′

private
  skip-inj : ∀ {A} {a b : Pos} {x y : U.Node A} → U.skipˢ a x ≡ U.skipˢ b y → a ≡ b × x ≡ y
  skip-inj refl = refl , refl

module Catching (R : Set) where
  open Run (Pureᴾ R) using (Env)
  open Realizing R using (Sub; Phase; nodeOf; Holding; Firing; firing; spot-of; phaseAt; firings; pendings; joiners; Joiner; forget; module At)
  open Pure R using (State; Timer; cascade)

  -- The cold's own next event past every step under the one it takes:
  -- its frame's next step, its close, or its next frame, a later tick
  -- than this one's (`rooted`).
  cold-next : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {b : Frame A u}
            → Holding (firing s hd τ r i b ∷ []) c st → ∀ {q} {ph : Phase A} → U.burstˢ τ r i b ≡ U.skipˢ q (nodeOf ph)
            → Shape.Next (State.pos st) (Beyond q) (nodeOf ph)
  cold-next {st = st} {u = u} {τ} {i = i} {b} H {q} {ph} eq with head (Holding.rooted H)
  ... | e , refl = next b eq
    where open Shape (State.pos st) (Beyond q)
          r = ix (τ + u) ∷ sub e ∷ []
          next : (b : Frame _ u) → U.burstˢ τ r i b ≡ U.skipˢ q (nodeOf ph) → Next (nodeOf ph)
          next (emit _ _) ()
          next (stall k)  eq with skip-inj eq
          ... | refl , n≡ = subst Next n≡ (subst OkM (sym (burst-head′ (suc i))) λ Y → <ᵖ-ix-lt r i (suc i) Y [] (n<1+n i))
            where burst-head′ = λ j → burst-head τ r j (Frame∞.force k)
          next (close k)  eq with skip-inj eq
          ... | refl , n≡ = subst Next n≡ (frames (From∞.force k))
            where frames : (m : From _ (suc u)) → Next (U.framesᶜ τ (r ++ [ last ]) m)
                  frames done         = λ Y → <ᵖ-ix-last r i Y []
                  frames quiet        = tt
                  frames (at t le b′) =
                    subst OkM (sym (burst-head τ (ix (τ + t) ∷ sub (r ++ [ last ]) ∷ []) 0 b′))
                          λ Y → <ᵖ-ix-lt [] (τ + u) (τ + t) (((sub e ∷ []) ++ [ ix i ]) ++ Y) ((sub (r ++ [ last ]) ∷ []) ++ [ ix 0 ]) (+-monoʳ-< τ le)

  module Under {h} (H : All (Pure.Val R h) h) (pos F : Pos) (pF : pos <ᵖ F ≡ true) where
    open At {h} H
    open Shape pos (Beyond F)

    RunM : ∀ {A} → Maybe (U.Node A) → Maybe (U.Node A) → Set₁
    RunM nothing  nothing   = Lift _ ⊤
    RunM (just c) (just c′) = Settle F Next c c′
    RunM _        _         = Lift _ ⊥

    runM-just : ∀ {A} {c : U.Node A} m → RunM (just c) m → Σ (U.Node A) λ c′ → m ≡ just c′ × Settle F Next c c′
    runM-just (just c′) rn = c′ , refl , rn
    runM-just nothing   ()

    postulate
      -- The cold's spot, every joiner on the way to it copying a source
      -- the step did not move: the witness with its phase moved settles,
      -- up to the sources the meaning holds, to one whose every copy is
      -- caught up.
      settle-at : ∀ {Δ A} (t : Sub h Δ A) {f} (e : firings t ≡ f ∷ []) {E : Env Δ h} {ρ} {ν : Now Δ} {ph : Phase (Firing.A f)}
                → spentʰ (Firing.handle f) ≡ false → unended ph ≡ true → Next (nodeOf ph)
                → Gated t E ρ → Caught t E ρ ν → Fine ν
                → All (λ tm → spentʰ (Timer.handle tm) ≡ false → Beyond F (cascade tm)) (pendings t)
                → All (λ j → pos <ᵖ Joiner.at′ j ≡ false) (joiners t E)
                → U.step (nodeOf (phaseAt (spot-of t e))) ≡ U.skipˢ F (nodeOf ph)
                → Σ (Sub h Δ A) λ t′ → forget t′ ≡ forget (stepAt (spot-of t e) ph E ρ)
                    × Caught t′ E ρ ν × Gated t′ E ρ × RunM (part (stepAt (spot-of t e) ph E ρ) E ρ) (part t′ E ρ)
