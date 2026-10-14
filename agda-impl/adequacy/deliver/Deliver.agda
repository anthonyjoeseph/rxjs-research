{-# OPTIONS --guardedness --large-indices #-}

-- A FRAME'S STEP, DELIVERED.  An emit or a completion runs the observer
-- chain the cold's slot holds, in continuation-passing style: whatever
-- the run does after the delivery returns, given what holds then, the
-- segment from the delivery's start is what the run does.  A delivery
-- the run never returns from — a synchronous recursion through a lane's
-- subscription — calls its continuation never, so nothing here asks a
-- delivery to finish.
--
-- What holds on return is the invariant again, at the frame's next step
-- or, the cold cut on the way, with no frame being burst: the meaning has
-- taken every step under the one the frame took.  The frame's slot runs
-- at least that one step, so a guard is passed before the continuation
-- runs, and the continuation is unbounded.
module adequacy.deliver.Deliver where

open import Data.List using ([]; _∷_; _++_; [_])
open import Data.Nat using (ℕ; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false)
open import Data.Maybe using (nothing)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import denotation.MonotonicList using (Time; Pos; Frame; Frame∞; From∞; ix; last; done; emit; close)
import denotation.Unfold as U
open import operation.Machine using (module Machine)
open import operation.PureObservable using (Sink; Handle; same; grow; _⨾_; wk∋; module Pure) renaming (_⊑_ to _⊑ʷ_)
open import adequacy.Realize using (module Realizing)
open import adequacy.Segment using (module Seg)

-- Growing a world from where it stands.
same-⨾ : ∀ {u v} (τ : u ⊑ʷ v) → same ⨾ τ ≡ τ
same-⨾ same     = refl
same-⨾ (grow τ) = cong grow (same-⨾ τ)

module Delivering (R : Set) where
  open Machine R using (⟨_,_⟩; turn; burst; run; ret; loop; push; sent; Stack; cbs; silent; shown; trace)
  open Realizing R using (Calm; calm; bursting; Holding; firing)
  open Pure R using (State; Callbacks; get; put)
  open Seg R

  -- On an emit's return: the cold live at its frame's next step, or cut
  -- on the way.
  Sent : ∀ {h v} {A u} → Sink h A → Handle h → Time → Pos → ℕ → Frame A u → h ⊑ʷ v → U.Node R → State v → Set₁
  Sent s hd τ r i b τ′ c′ st′ = (lower (get (State.heap st′) (wk∋ τ′ hd)) ≡ false × Holding (firing (wk∋ τ′ s) (wk∋ τ′ hd) τ r i b ∷ []) c′ st′)
                              ⊎ (lower (get (State.heap st′) (wk∋ τ′ hd)) ≡ true × Holding [] c′ st′)

  postulate
    -- An emit delivered down the observer chain the cold's slot holds.
    --
    -- RECOVERY: `git show a2e0bb8b:agda-impl/Realize.agda` restores `obsAt`
    --   — the observer a spot's slot holds — over the fuel engine's witness.
    deliver-next : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {a : A} {k′ : Frame∞ A u}
                 → Holding (firing s hd τ r i (emit a k′) ∷ []) c st → lower (get (State.heap st) hd) ≡ false
                 → ∀ {w} {σ : w ⊑ʷ h} {K : Stack w ⊤}
                 → (∀ {v} (τ′ : h ⊑ʷ v) {st′ : State v} {c′} → Sent s hd τ r (suc i) (Frame∞.force k′) τ′ c′ st′
                    → Seg nothing (trace ⟨ st′ , ret tt (σ ⨾ τ′) K ⟩) (U.unfold c′))
                 → ∀ {bd} → Seg bd (trace ⟨ record st { pos = r ++ [ ix i ] } , run (Callbacks.onNext (cbs st s) a) σ K ⟩) (U.unfold c)

    -- A frame closing on its timeline's end: the cold spent, its
    -- completion delivered down the chain, and nothing left firing.
    deliver-done : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {k′ : From∞ A (suc u)}
                 → Holding (firing s hd τ r i (close k′) ∷ []) c st → lower (get (State.heap st) hd) ≡ false → From∞.force k′ ≡ done
                 → ∀ {w} {σ : w ⊑ʷ h} {K : Stack w ⊤}
                 → (∀ {v} (τ′ : h ⊑ʷ v) {st′ : State v} {c′} → Holding [] c′ st′
                    → Seg nothing (trace ⟨ st′ , ret tt (σ ⨾ τ′) K ⟩) (U.unfold c′))
                 → ∀ {bd} → Seg bd (trace ⟨ record st { heap = put (State.heap st) hd (lift true) ; pos = r ++ [ last ] }
                                          , run (Callbacks.onComplete (cbs st s)) σ K ⟩)
                                   (U.unfold c)

  -- An emit's step: delivered, then the frame resumes at its next step,
  -- or the loop is calm again.
  emit-seg : ∀ {w h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {a : A} {k′ : Frame∞ A u} {σ : w ⊑ʷ h}
           → Holding (firing s hd τ r i (emit a k′) ∷ []) c st → lower (get (State.heap st) hd) ≡ false
           → ∀ {bd} → Seg bd (shown (silent ⟨ record st { pos = r ++ [ ix i ] }
                                            , run (Callbacks.onNext (cbs st s) a) same (push (sent s hd u r (suc i) (Frame∞.force k′)) σ loop) ⟩))
                              (U.unfold c)
  emit-seg {u = u} {r = r} {i} {k′ = k′} {σ} H lv = tauˡ (deliver-next H lv resume)
    where
      resume : ∀ {v} (τ′ : _ ⊑ʷ v) {st′ : State v} {c′} → Sent _ _ _ r (suc i) (Frame∞.force k′) τ′ c′ st′
             → Seg nothing (trace ⟨ st′ , ret tt (same ⨾ τ′) (push (sent _ _ u r (suc i) (Frame∞.force k′)) σ loop) ⟩) (U.unfold c′)
      resume τ′ p rewrite same-⨾ τ′ with p
      ... | inj₁ (lv′ , H′) = tauˡ (calm~ (bursting H′ lv′) tt)
      ... | inj₂ (sp , H′)  = tauˡ (if-true (λ m → Seg _ (shown (silent m)) _) sp (tauˡ (tauˡ (calm~ (calm H′) tt))))

  -- A frame closing on its timeline's end: its completion delivered, and
  -- the loop is calm again.
  done-seg : ∀ {w h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {k′ : From∞ A (suc u)} {σ : w ⊑ʷ h}
           → Holding (firing s hd τ r i (close k′) ∷ []) c st → lower (get (State.heap st) hd) ≡ false → From∞.force k′ ≡ done
           → ∀ {bd} → Seg bd (shown (silent ⟨ record st { heap = put (State.heap st) hd (lift true) ; pos = r ++ [ last ] }
                                            , run (Callbacks.onComplete (cbs st s)) σ loop ⟩))
                              (U.unfold c)
  done-seg H lv fk = tauˡ (deliver-done H lv fk λ τ′ H′ → tauˡ (calm~ (calm H′) tt))
