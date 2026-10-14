{-# OPTIONS --guardedness --large-indices #-}

-- WHAT HOLDS MID-DELIVERY: the invariant at the subscription a delivery
-- has reached, against a heap the delivery has partly written.
--
-- The meaning and the run disagree there.  The run writes on the way up —
-- a scan its accumulator, a feeder each joiner in turn — while the
-- meaning steps the whole configuration at once.  So the hole carries the
-- meaning's node `m` apart from its witness `t`, and the configuration is
-- the frames' meaning around `m` (`plugN`), not the witness's open part.
-- Below the hole the witness is the run's, exactly.
--
-- A feeder's joiners are fed one at a time, so a joiner not yet fed holds
-- its copy one step behind its source, at a position `L` names and the
-- run has not reached (`Lagging`).  Before a delivery every sibling's next
-- event is past every step under it (`Fore`); a connect's body is the
-- exception, its joiners about to be shown the source's event.  After,
-- every sibling's is (`Quiet`).
module adequacy.deliver.Mid where

open import Data.Bool using (true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_+_)
open import Data.Product using (_×_; Σ)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Level using (Lift)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import denotation.MonotonicList using (Pos; ix; _<ᵖ_) renaming (sub to subᴾ)
import denotation.Unfold as U
open import denotation.Unfold using (Srcs)
open import operation.AbstractObservable using (module Run)
open import operation.PureObservable using (Pureᴾ; World; _⊑_; module Pure)
open import adequacy.Realize using (module Realizing)
open import adequacy.step.Focus using (Beyond; Open)
open import adequacy.deliver.Context using (module Contexts)

module Middles (R : Set) where
  open Run (Pureᴾ R)
  open Kit
  open FlatKit
  open Realizing R
  open Contexts R
  open Pure R using (State)

  -- A next event, if any, past every step under `q`.
  Clears : Pos → Maybe Pos → Set
  Clears q nothing  = ⊤
  Clears q (just k) = Beyond q k

  Past : ∀ {A} → Pos → Maybe (U.Node A) → Set
  Past q nothing  = ⊤
  Past q (just n) = Clears q (U.headˢ (U.step n))

  module AtC {h : World} (H : All (Pure.Val R h) h) where
    open At H

    ----------------------------------------------------------------------
    -- The meaning around the hole

    nodeF : ∀ {Δ A Δ′ B} → Fr h Δ A Δ′ B → Env Δ′ h → Srcs Δ′ → Maybe (U.Node A) → Maybe (U.Node B)
    nodeF (mapF f)                            E ρ m = mapᴹ (U.mapᶜ f) m
    nodeF (scanF f r)                         E ρ m = mapᴹ (U.scanᶜ f (val r)) m
    nodeF (takeF i p c u)                     E ρ m = if val (Kit.live c) then mapᴹ (U.takeWhileᶜ i p) m else nothing
    nodeF (outerF op f fl oc u r ls)          E ρ m = merged op (λ a q → U.subscribe (f a) ρ q) m (partLanes ls E ρ) (val (Flat.queue fl))
    nodeF (laneF op f fl oc u r so bs c d as) E ρ m =
      merged op (λ a q → U.subscribe (f a) ρ q) (part so E ρ)
             (partLanes bs E ρ ++ (if val (Kit.live c) then consᴹ m (partLanes as E ρ) else partLanes as E ρ)) (val (Flat.queue fl))
    nodeF (sourceF S c u s₀ mm body)          E ρ m = connected mm (part body (S ∷ E) (s₀ ∷ ρ))
    nodeF (bodyF S c u s₀ mm src)             E ρ m = connected mm m
    nodeF (deferF u)                          E ρ m = m

    plugN : ∀ {Δ A} → Ctx h Δ A → Maybe (U.Node A) → Maybe (U.Node R)
    plugN top     m = m
    plugN (f ◂ k) m = plugN k (nodeF f (envC k) (srcsC k) m)

    -- Each connect in scope at the hole, its source as the run holds it.
    nowF : ∀ {Δ A Δ′ B} → Fr h Δ A Δ′ B → Env Δ′ h → Srcs Δ′ → Now Δ′ → Now Δ
    nowF (bodyF S c u s₀ mm src)        E ρ ν = part src E ρ ∷ ν
    nowF (mapF _)                       E ρ ν = ν
    nowF (scanF _ _)                    E ρ ν = ν
    nowF (takeF _ _ _ _)                E ρ ν = ν
    nowF (outerF _ _ _ _ _ _ _)         E ρ ν = ν
    nowF (laneF _ _ _ _ _ _ _ _ _ _ _)  E ρ ν = ν
    nowF (sourceF _ _ _ _ _ _)          E ρ ν = ν
    nowF (deferF _)                     E ρ ν = ν

    nowC : ∀ {Δ A} → Ctx h Δ A → Now Δ
    nowC top     = []
    nowC (f ◂ k) = nowF f (envC k) (srcsC k) (nowC k)

    ----------------------------------------------------------------------
    -- The joiners' copies, a feeder part way through its joiners

    module Lagging (L : Pos → Set) (pos : Pos) where
      -- A copy one step behind its source `s`, that step at `q`.
      Behind : ∀ {A} → U.Node A → Pos → Maybe (U.Node A) → Set₁
      Behind {A} cp q (just s) = Σ A λ a → U.step cp ≡ U.outˢ q a s
      Behind     cp q nothing  = U.step cp ≡ U.endˢ q

      -- Caught up, or behind by the step a feeder has yet to show it.
      Lag : ∀ {A} → Pos → Maybe (U.Node A) → U.Node A → Set₁
      Lag j s cp = s ≡ just cp ⊎ Σ Pos λ q → L (q ++ [ subᴾ j ]) × pos <ᵖ (q ++ [ subᴾ j ]) ≡ true × Behind cp q s

      open Catching Lag public renaming (Caught to CaughtL; CaughtLanes to CaughtLanesL)

      -- A frame's siblings, the hole's source as the meaning holds it.
      CaughtF : ∀ {Δ A Δ′ B} → Fr h Δ A Δ′ B → Env Δ′ h → Srcs Δ′ → Now Δ′ → Maybe (U.Node A) → Set₁
      CaughtF (outerF op f fl oc u r ls)          E ρ ν m = CaughtLanesL ls E ρ ν
      CaughtF (laneF op f fl oc u r so bs c d as) E ρ ν m = CaughtL so E ρ ν × CaughtLanesL bs E ρ ν × CaughtLanesL as E ρ ν
      CaughtF (sourceF S c u s₀ mm body)          E ρ ν m = CaughtL body (S ∷ E) (s₀ ∷ ρ) (m ∷ ν)
      CaughtF (bodyF S c u s₀ mm src)             E ρ ν m = CaughtL src E ρ ν
      CaughtF (mapF _)                            E ρ ν m = Lift _ ⊤
      CaughtF (scanF _ _)                         E ρ ν m = Lift _ ⊤
      CaughtF (takeF _ _ _ _)                     E ρ ν m = Lift _ ⊤
      CaughtF (deferF _)                          E ρ ν m = Lift _ ⊤

      CaughtC : ∀ {Δ A} → Ctx h Δ A → Maybe (U.Node A) → Set₁
      CaughtC top     m = Lift _ ⊤
      CaughtC (f ◂ k) m = CaughtF f (envC k) (srcsC k) (nowC k) m × CaughtC k (nodeF f (envC k) (srcsC k) m)

    ----------------------------------------------------------------------
    -- The gates around the hole

    GatedF : ∀ {Δ A Δ′ B} → Fr h Δ A Δ′ B → Env Δ′ h → Srcs Δ′ → Sub h Δ A → Maybe (U.Node A) → Set₁
    GatedF (takeF i p c u)                     E ρ t m = val (Kit.live c) ≡ false → Dead t
    GatedF (outerF op f fl oc u r ls)          E ρ t m = GatedLanes ls E ρ
    GatedF (laneF op f fl oc u r so bs c d as) E ρ t m =
      Gated so E ρ × GatedLanes bs E ρ × (val (Kit.live c) ≡ false → Dead t) × GatedLanes as E ρ
    GatedF (sourceF S c u s₀ mm body)          E ρ t m =
      Kept mm m × (part body (S ∷ E) (s₀ ∷ ρ) ≡ nothing → Dead t) × Gated body (S ∷ E) (s₀ ∷ ρ)
    GatedF (bodyF S c u s₀ mm src)             E ρ t m = Kept mm (part src E ρ) × (m ≡ nothing → Dead src) × Gated src E ρ
    GatedF (mapF _)                            E ρ t m = Lift _ ⊤
    GatedF (scanF _ _)                         E ρ t m = Lift _ ⊤
    GatedF (deferF _)                          E ρ t m = Lift _ ⊤

    GatedC : ∀ {Δ A} → Ctx h Δ A → Sub h Δ A → Maybe (U.Node A) → Set₁
    GatedC top     t m = Lift _ ⊤
    GatedC (f ◂ k) t m = GatedF f (envC k) (srcsC k) t m × GatedC k (plugF f t) (nodeF f (envC k) (srcsC k) m)

    ----------------------------------------------------------------------
    -- The siblings' next events, against a delivery at `q`

    -- Before it: every sibling past it, a connect's body short of the
    -- source's event as its joiners are shown it.
    ForeF : ∀ {Δ A Δ′ B} → Fr h Δ A Δ′ B → Env Δ′ h → Srcs Δ′ → Pos → Set₁
    ForeF (outerF op f fl oc u r ls)          E ρ q = All (λ n → Past q (just n)) (partLanes ls E ρ)
    ForeF (laneF op f fl oc u r so bs c d as) E ρ q =
      Past q (part so E ρ) × All (λ n → Past q (just n)) (partLanes bs E ρ) × All (λ n → Past q (just n)) (partLanes as E ρ)
    ForeF (sourceF S c u s₀ mm body)          E ρ q = Lift _ (Open (q ++ [ ix 0 ]) (part body (S ∷ E) (s₀ ∷ ρ)))
    ForeF (bodyF S c u s₀ mm src)             E ρ q = Lift _ (Past q mm)
    ForeF (mapF _)                            E ρ q = Lift _ ⊤
    ForeF (scanF _ _)                         E ρ q = Lift _ ⊤
    ForeF (takeF _ _ _ _)                     E ρ q = Lift _ ⊤
    ForeF (deferF _)                          E ρ q = Lift _ ⊤

    Fore : ∀ {Δ A} → Ctx h Δ A → Pos → Set₁
    Fore top     q = Lift _ ⊤
    Fore (f ◂ k) q = ForeF f (envC k) (srcsC k) q × Fore k q

    -- After it: every sibling past it.
    QuietF : ∀ {Δ A Δ′ B} → Fr h Δ A Δ′ B → Env Δ′ h → Srcs Δ′ → Pos → Set₁
    QuietF (sourceF S c u s₀ mm body)          E ρ q = Lift _ (Past q (part body (S ∷ E) (s₀ ∷ ρ)))
    QuietF (outerF op f fl oc u r ls)          E ρ q = ForeF (outerF op f fl oc u r ls) E ρ q
    QuietF (laneF op f fl oc u r so bs c d as) E ρ q = ForeF (laneF op f fl oc u r so bs c d as) E ρ q
    QuietF (bodyF S c u s₀ mm src)             E ρ q = Lift _ (Past q mm)
    QuietF (mapF _)                            E ρ q = Lift _ ⊤
    QuietF (scanF _ _)                         E ρ q = Lift _ ⊤
    QuietF (takeF _ _ _ _)                     E ρ q = Lift _ ⊤
    QuietF (deferF _)                          E ρ q = Lift _ ⊤

    Quiet : ∀ {Δ A} → Ctx h Δ A → Pos → Set₁
    Quiet top     q = Lift _ ⊤
    Quiet (f ◂ k) q = QuietF f (envC k) (srcsC k) q × Quiet k q

  ------------------------------------------------------------------------
  -- THE INVARIANT MID-DELIVERY: `Holding`'s, at a hole `k`, the witness
  -- there `t`, its meaning `m`.

  record Mid {h Δ A} (L : Pos → Set) (k : Ctx h Δ A) (t : Sub h Δ A) (m : Maybe (U.Node A))
             (fs : List (Firing h)) (c : U.Node R) (st : State h) : Set₁ where
    open At (State.heap st)
    open AtC (State.heap st)
    open Lagging L (State.pos st)
    field
      holds   : Holds (plug k t) [] rootObs
      open≡   : plugN k m ≡ just c
      caughtC : CaughtC k m
      caught  : CaughtL t (envC k) (srcsC k) (nowC k)
      gatedC  : GatedC k t m
      gated   : Gated t (envC k) (srcsC k)
      past    : All (λ j → State.pos st <ᵖ Joiner.at′ j ≡ false) (joiners (plug k t) [])
      firing≡ : firings (plug k t) ≡ fs
      clocked : All (λ f → Firing.since f + Firing.u f ≡ State.clock st) fs
      behind  : All (λ f → Σ Pos (λ d → State.pos st ≡ Firing.at′ f ++ d)
                         × State.pos st <ᵖ (Firing.at′ f ++ [ ix (Firing.index f) ]) ≡ true) fs
      rooted  : All (λ f → Σ Pos λ e → Firing.at′ f ≡ ix (Firing.since f + Firing.u f) ∷ subᴾ e ∷ []) fs
      timed   : Timed (State.timers st) (pendings (plug k t))
      joined  : Joined (subjects (plug k t)) (joiners (plug k t) [])
      ordered : Ordered st
      fresh   : AllPairs _≢_ (names (plug k t))
      running : State.ended st ≡ false

  -- ON A DELIVERY'S RETURN at `q`, in a world grown by `τ`: the frames
  -- and the hole moved as a delivery moves them, the invariant at the
  -- hole with its meaning `m′`, every sibling past `q`.
  record Back {h v Δ A} (L : Pos → Set) (τ : h ⊑ v) (k : Ctx h Δ A) (t : Sub h Δ A) (q : Pos)
              (m′ : Maybe (U.Node A)) (fs : List (Firing h)) (c′ : U.Node R) (st′ : State v) : Set₁ where
    constructor back
    field
      {k′}    : Ctx v Δ A
      {t′}    : Sub v Δ A
      grown   : Grown τ k k′
      evolves : Evolves τ t t′
      mid     : Mid L k′ t′ m′ (map (wkFiring τ) fs) c′ st′
      quiet   : AtC.Quiet (State.heap st′) k′ q
