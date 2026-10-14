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

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Nat using (ℕ; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.MonotonicList using (Time; Pos; Frame; Frame∞; From∞; ix; last; done; emit; close)
import denotation.Unfold as U
open import operation.Machine using (module Machine)
open import operation.AbstractObservable using (module Run)
open import operation.PureObservable using (Pureᴾ; Sink; Handle; same; grow; _⨾_; wk∋; module Pure) renaming (_⊑_ to _⊑ʷ_)
open import adequacy.Realize using (module Realizing)
open import adequacy.Segment using (module Seg)
open import adequacy.deliver.Context using (module Contexts)
open import adequacy.deliver.Mid using (module Middles)
open import adequacy.deliver.Climb using (same-⨾; module Climbing)

module Delivering (R : Set) where
  open Machine R using (⟨_,_⟩; turn; burst; run; ret; loop; push; sent; Stack; cbs; silent; shown; trace)
  open Realizing R using (Holding; firing; coldˢ; playing; waiting; _≗_)
  open Contexts R using (Ctx; obsC)
  open Middles R using (Mid; Back; module AtC)
  open Climbing R using (NextAt; DoneAt; delivers)
  open Run (Pureᴾ R) using (Observer)
  open Pure R using (State; Callbacks; get; put)
  open Seg R

  -- On an emit's return: the cold live at its frame's next step, or cut
  -- on the way.
  Sent : ∀ {h v} {A u} → Sink h A → Handle h → Time → Pos → ℕ → Frame A u → h ⊑ʷ v → U.Node R → State v → Set₁
  Sent s hd τ r i b τ′ c′ st′ = (lower (get (State.heap st′) (wk∋ τ′ hd)) ≡ false × Holding (firing (wk∋ τ′ s) (wk∋ τ′ hd) τ r i b ∷ []) c′ st′)
                              ⊎ (lower (get (State.heap st′) (wk∋ τ′ hd)) ≡ true × Holding [] c′ st′)

  ------------------------------------------------------------------------
  -- A delivery from where the cold's slot is, to where it returns

  -- A frame's emit about to run its cold's slot: the hole the cold, its
  -- phase at the frame's next step, its meaning still before the emit.
  record Start {h} {A u} (s : Sink h A) (hd : Handle h) (τ : Time) (r : Pos) (i : ℕ) (a : A) (k′ : Frame∞ A u)
               (c : U.Node R) (st : State h) : Set₁ where
    field
      {Δ}  : List Set
      ctx  : Ctx h Δ A
      mid  : Mid [] ctx (coldˢ s hd (playing τ r (suc i) (Frame∞.force k′))) (just (U.burstᶜ τ r i (emit a k′)))
                 (firing s hd τ r (suc i) (Frame∞.force k′) ∷ []) c (record st { pos = r ++ [ ix i ] })
      fore : AtC.Fore (State.heap st) ctx (r ++ [ ix i ])
      slot : Callbacks.onNext (cbs st s) a ≗ Observer.next (obsC ctx) a

  -- A frame's close about to run its cold's completion: the meaning past
  -- the frame's last step, at its timeline's end; the cold spent.
  record StartDone {h} {A} (u : Time) (s : Sink h A) (hd : Handle h) (τ : Time) (r : Pos) (c : U.Node R) (st : State h) : Set₁ where
    field
      {Δ}   : List Set
      {c₁}  : U.Node R
      ctx   : Ctx h Δ A
      skips : Skips c c₁
      mid   : Mid [] ctx (coldˢ s hd (waiting {u = u} τ (r ++ [ last ]) done)) (just (U.framesᶜ {t = u} τ (r ++ [ last ]) done)) [] c₁
                  (record st { heap = put (State.heap st) hd (lift true) ; pos = r ++ [ last ] })
      fore  : AtC.Fore (put (State.heap st) hd (lift true)) ctx (r ++ [ last ])
      slot  : Callbacks.onComplete (cbs st s) ≗ Observer.complete (obsC ctx)

  postulate
    -- A firing cold opened as the hole: its slot holds the observer the
    -- frames above it build.
    --
    -- RECOVERY: `git show a2e0bb8b:agda-impl/Realize.agda` restores `obsAt`
    --   — the observer a spot's slot holds — over the fuel engine's witness.
    mid-start : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {a : A} {k′ : Frame∞ A u}
              → Holding (firing s hd τ r i (emit a k′) ∷ []) c st → lower (get (State.heap st) hd) ≡ false
              → Start s hd τ r i a k′ c st

    -- A closing frame's last step taken by the meaning, a skip under the
    -- frames above, and the cold opened as the hole at its end.
    mid-start-done : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {k′ : From∞ A (suc u)}
                   → Holding (firing s hd τ r i (close k′) ∷ []) c st → lower (get (State.heap st) hd) ≡ false → From∞.force k′ ≡ done
                   → StartDone (suc u) s hd τ r c st

    -- The emit returned to the cold's frame: the cold live at its next
    -- step, or cut on the way and its phase forgotten.
    back-sent : ∀ {h v Δ} {A u τ₀} {s : Sink h A} {hd r i} {b : Frame A u} {k : Ctx h Δ A} {τ : h ⊑ʷ v} {c′} {st′ : State v}
              → Back [] τ k (coldˢ s hd (playing τ₀ r (suc i) b)) (r ++ [ ix i ]) (just (U.burstᶜ τ₀ r (suc i) b))
                     (firing s hd τ₀ r (suc i) b ∷ []) c′ st′
              → Sent s hd τ₀ r (suc i) b τ c′ st′

    back-done : ∀ {h v Δ} {A u τ₀} {s : Sink h A} {hd e} {k : Ctx h Δ A} {τ : h ⊑ʷ v} {c′} {st′ : State v}
              → Back [] τ k (coldˢ s hd (waiting {u = u} τ₀ e done)) e nothing [] c′ st′
              → Holding [] c′ st′

  -- AN EMIT AT A HOLE, delivered to the hole's observer: the run up to
  -- its return is the meaning's, and on return the invariant is back at
  -- the hole, every sibling past the emit.
  next-at : ∀ {h Δ A} {k : Ctx h Δ A} → NextAt k
  next-at {k = k} = proj₁ (delivers k)

  -- AN END AT A HOLE, delivered as a completion.
  done-at : ∀ {h Δ A} {k : Ctx h Δ A} → DoneAt k
  done-at {k = k} = proj₂ (delivers k)

  -- An emit delivered down the observer chain the cold's slot holds.
  deliver-next : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {a : A} {k′ : Frame∞ A u}
               → Holding (firing s hd τ r i (emit a k′) ∷ []) c st → lower (get (State.heap st) hd) ≡ false
               → ∀ {w} {σ : w ⊑ʷ h} {K : Stack w ⊤}
               → (∀ {v} (τ′ : h ⊑ʷ v) {st′ : State v} {c′} → Sent s hd τ r (suc i) (Frame∞.force k′) τ′ c′ st′
                  → Seg nothing (trace ⟨ st′ , ret tt (σ ⨾ τ′) K ⟩) (U.unfold c′))
               → ∀ {bd} → Seg bd (trace ⟨ record st { pos = r ++ [ ix i ] } , run (Callbacks.onNext (cbs st s) a) σ K ⟩) (U.unfold c)
  deliver-next H lv κ = next-at (Start.mid S) refl refl (Start.fore S) (Start.slot S) λ τ B → κ τ (back-sent B)
    where S = mid-start H lv

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
  deliver-done H lv fk κ =
    skipping (StartDone.skips S) (done-at (StartDone.mid S) refl refl (StartDone.fore S) (StartDone.slot S) λ τ B → κ τ (back-done B))
    where S = mid-start-done H lv fk

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
