------------------------------------------------------------------
-- THE BURST CEILING: the frame width read along the descent a
-- SUBSCRIBE actually takes, which is not the one the full ceiling
-- collects.
--
-- `ceilᵉ` joins every measure at every node of the syntax, defers
-- included, because it is what a caps predicate has to satisfy: a
-- parked observable is delivered LATER and something must have priced
-- it.  A subscribe frame's descent is narrower on both counts.  It
-- reads one measure -- how many payloads this frame delivers, which is
-- `outWⱽ` and nothing else -- and it STOPS at a defer, because a defer
-- crosses a tick and the frame under it is a different frame.  It also
-- never enters a template: a `mapᵉ`'s function is applied to what the
-- source delivers, it is not subscribed.
--
-- SO THE TWO CEILINGS ARE NOT INTERCHANGEABLE, and the narrow one is
-- what a descent statement can be proven against.  Cutting at the
-- defer is the whole of the difference that matters: a μ's variable is
-- reachable only from under a defer, so a ceiling that cuts there
-- cannot see the plug an unfolding substitutes, and is unmoved by it --
-- the mechanism `hopD-unfoldμ` already runs on.  The joined ceiling
-- does see it, once per occurrence, and `Refuted.Ceil-Unfold-Mu` is
-- what that costs.
--
-- AND IT IS STILL UNDER THE JOINED ONE, which is what keeps the caps
-- base paying for it: every node's reading is one of the five the join
-- takes at that node, and every child it descends into is one the join
-- descends into too.
------------------------------------------------------------------
module Rx.Burst-Ceil where

open import Data.Nat  using (ℕ; _⊔_; _≤_; z≤n)
open import Data.Nat.Properties using (≤-trans; ⊔-lub; ⊔-mono-≤; m≤n⊔m)
open import Data.Fin  using (Fin)
open import Data.List using (List; []; _∷_; tabulate)

open import Rx.Exp using (Ctx; Exp; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ;
                          scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ;
                          varᵉ; deferᵉ)
open import Rx.Slots using (Slots; Slot; scripted; shared)
open import Rx.Frame-Width
  using (outWⱽ; ceilᵉ; ownᵉ; kidsᵉ; ceilᵗ; slotCeil; slotsCeilgo; slotsCeil;
         outW≤ceil)

mutual
  bCeilᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) → Exp Γ Δᵍ Δ Θ t → ℕ
  bCeilᵉ j sl e = outWⱽ j [] sl e ⊔ bKidsᵉ j sl e

  -- ONE CHILD PER CLAUSE, and exactly the child the descent takes.
  -- The slot head is absent on purpose: a connect re-enters the walk on
  -- the DEFINITION, so it is the telescope's ceiling that pays for it
  -- and not this node's.
  bKidsᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) → Exp Γ Δᵍ Δ Θ t → ℕ
  bKidsᵉ j sl (input i)         = 0
  bKidsᵉ j sl (ofᵉ ts)          = 0
  bKidsᵉ j sl emptyᵉ            = 0
  bKidsᵉ j sl (mapᵉ f e)        = bCeilᵉ j sl e
  bKidsᵉ j sl (takeᵉ c e)       = bCeilᵉ j sl e
  bKidsᵉ j sl (scanᵉ f z e)     = bCeilᵉ j sl e
  bKidsᵉ j sl (mergeAllᵉ lim e) = bCeilᵉ j sl e
  bKidsᵉ j sl (switchAllᵉ e)    = bCeilᵉ j sl e
  bKidsᵉ j sl (exhaustAllᵉ e)   = bCeilᵉ j sl e
  bKidsᵉ j sl (μᵉ e)            = bCeilᵉ j sl e
  bKidsᵉ j sl (varᵉ x)          = 0
  bKidsᵉ j sl (deferᵉ e)        = 0

slotBCeil : ∀ {n} {Γ : Ctx n} {k u} (j : ℕ) (sl : Slots Γ) → Slot Γ k u → ℕ
slotBCeil j sl (scripted _) = 0
slotBCeil j sl (shared d)   = bCeilᵉ j sl d

slotsBCeilgo : ∀ {n} {Γ : Ctx n} (j : ℕ) (sl : Slots Γ) → List (Fin n) → ℕ
slotsBCeilgo j sl []       = 0
slotsBCeilgo j sl (i ∷ is) = slotBCeil j sl (sl i) ⊔ slotsBCeilgo j sl is

slotsBCeil : ∀ {n} {Γ : Ctx n} (j : ℕ) (sl : Slots Γ) → ℕ
slotsBCeil {n = n} j sl = slotsBCeilgo j sl (tabulate {n = n} (λ i → i))

------------------------------------------------------------------
-- AND IT IS UNDER THE JOINED CEILING, node for node and child for
-- child.  This is what lets a descent statement proven against the
-- narrow reading be spent where the caps base's own width coordinate
-- is what is on offer.
------------------------------------------------------------------
mutual
  bCeil≤ceil : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ)
    (e : Exp Γ Δᵍ Δ Θ t) → bCeilᵉ j sl e ≤ ceilᵉ j sl e
  bCeil≤ceil j sl e = ⊔-lub (outW≤ceil j sl e) (bKids≤ceil j sl e)

  bKids≤ceil : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ)
    (e : Exp Γ Δᵍ Δ Θ t) → bKidsᵉ j sl e ≤ ceilᵉ j sl e
  bKids≤ceil j sl (input i)         = z≤n
  bKids≤ceil j sl (ofᵉ ts)          = z≤n
  bKids≤ceil j sl emptyᵉ            = z≤n
  bKids≤ceil j sl (mapᵉ f e)        =
    ≤-trans (≤-trans (bCeil≤ceil j sl e) (m≤n⊔m (ceilᵗ j sl f) (ceilᵉ j sl e)))
            (m≤n⊔m (ownᵉ j sl (mapᵉ f e)) (kidsᵉ j sl (mapᵉ f e)))
  bKids≤ceil j sl (takeᵉ c e)       =
    ≤-trans (≤-trans (bCeil≤ceil j sl e) (m≤n⊔m (ceilᵗ j sl c) (ceilᵉ j sl e)))
            (m≤n⊔m (ownᵉ j sl (takeᵉ c e)) (kidsᵉ j sl (takeᵉ c e)))
  bKids≤ceil j sl (scanᵉ f z e)     =
    ≤-trans (≤-trans (bCeil≤ceil j sl e)
                     (m≤n⊔m (ceilᵗ j sl f ⊔ ceilᵗ j sl z) (ceilᵉ j sl e)))
            (m≤n⊔m (ownᵉ j sl (scanᵉ f z e)) (kidsᵉ j sl (scanᵉ f z e)))
  bKids≤ceil j sl (mergeAllᵉ lim e) =
    ≤-trans (bCeil≤ceil j sl e)
            (m≤n⊔m (ownᵉ j sl (mergeAllᵉ lim e)) (kidsᵉ j sl (mergeAllᵉ lim e)))
  bKids≤ceil j sl (switchAllᵉ e)    =
    ≤-trans (bCeil≤ceil j sl e)
            (m≤n⊔m (ownᵉ j sl (switchAllᵉ e)) (kidsᵉ j sl (switchAllᵉ e)))
  bKids≤ceil j sl (exhaustAllᵉ e)   =
    ≤-trans (bCeil≤ceil j sl e)
            (m≤n⊔m (ownᵉ j sl (exhaustAllᵉ e)) (kidsᵉ j sl (exhaustAllᵉ e)))
  bKids≤ceil j sl (μᵉ e)            =
    ≤-trans (bCeil≤ceil j sl e)
            (m≤n⊔m (ownᵉ j sl (μᵉ e)) (kidsᵉ j sl (μᵉ e)))
  bKids≤ceil j sl (varᵉ x)          = z≤n
  bKids≤ceil j sl (deferᵉ e)        = z≤n

slotB≤slotCeil : ∀ {n} {Γ : Ctx n} {k u} (j : ℕ) (sl : Slots Γ)
  (s : Slot Γ k u) → slotBCeil j sl s ≤ slotCeil j sl s
slotB≤slotCeil j sl (scripted _) = z≤n
slotB≤slotCeil j sl (shared d)   = bCeil≤ceil j sl d

slotsBgo≤go : ∀ {n} {Γ : Ctx n} (j : ℕ) (sl : Slots Γ) (is : List (Fin n)) →
  slotsBCeilgo j sl is ≤ slotsCeilgo j sl is
slotsBgo≤go j sl []       = z≤n
slotsBgo≤go j sl (i ∷ is) =
  ⊔-mono-≤ (slotB≤slotCeil j sl (sl i)) (slotsBgo≤go j sl is)

slotsB≤slotsCeil : ∀ {n} {Γ : Ctx n} (j : ℕ) (sl : Slots Γ) →
  slotsBCeil j sl ≤ slotsCeil j sl
slotsB≤slotsCeil {n = n} j sl = slotsBgo≤go j sl (tabulate {n = n} (λ i → i))
