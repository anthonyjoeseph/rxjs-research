-- ══════════════════════════════════════════════════════════════════
-- THREE ENTRY READINGS ACROSS KILL AND CONSUME STEPS.
--
-- TARGET: switchKill-readings @6deac2
-- TARGET: thruConsume-readings @e590fc
-- TARGET: subscribeInner-readings @f4ed74
--
-- WHAT THESE ROWS COVER.  All three statements ask that three boolean
-- readings are preserved across one evaluator step:
--
--   H1 pathOrd? — path cells below the nextNode counter
--   H2 pathPark? — path frames carry valid park strategies
--   H3 parkStrat? — the outer node's queue entries are below pathFloor
--
-- switchKill-readings: covered at κ = root and two cur shapes (nothing
-- and just v).  switchKill never touches nodes or nextNode, so the
-- triple is the input triple at both shapes — all three readings are
-- preserved trivially.
--
-- thruConsume-readings (no-room case): covered at a 2-slot context and
-- κ = share-sink fzero (pathFloor κ = 0), where thruConsume parks the
-- arrival o = input fzero into the merge node's queue.  After the park
-- parkStrat? reads all (inputsBelowᵉ 0) [input fzero] = (0 <ᵇ 0) =
-- false.  The figures row pins this reading; a tie row that asserted
-- conclusion C3 = true here would carry refl : false ≡ true, which
-- does not typecheck.  This is a REFUTATION candidate — the no-room
-- branch violates H3 unless inputsBelowᵉ (pathFloor κ) o is separately
-- guaranteed.  The figures≡ pin below records the actual boolean
-- so the conclusion the statement makes is visible.
--
-- thruConsume-readings (identity paths): covered at κ = root,
-- missing-node path (thruConsume returns sched and st unchanged) and
-- no-room path at κ = root (pathFloor root = n = 1, input fzero has
-- index 0 < 1, so inputsBelowᵉ 1 (input fzero) = true and parkStrat?
-- is preserved).  Both rows hold.
--
-- subscribeInner-readings (g0 case): covered at κ = root.
-- subscribeInner g0 returns record sched { nextNode = suc inst } and
-- the ORIGINAL st — nodes are unchanged.  nextNode increases, which
-- preserves pathOrd? by monotonicity; nodes unchanged preserves H2 and
-- H3 by refl.
--
-- NOT COVERED: subscribeInner (gs fuel) where subscribeE is called and
-- may itself call thruConsume; thruConsume in the hasRoom = true branch
-- (which calls subscribeInner and mergeAllBump); the switchᵒ and
-- exhaustᵒ arms of thruConsume.
-- ══════════════════════════════════════════════════════════════════
module Probed.Kill-Consume-Readings where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gs; cold)
open import Rx.Exp using (Ctx; Closed; natᵗ; obs; input)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator
  using (EvalSt; Sched; sched-init; st-init; root; mergeAllᵒ; mergeAll-st;
         AllOp; Path; NodeId; NodeState; lookupNode; installNode;
         thru-outer; switchKill; thruConsume; subscribeInner; share-sink;
         _↠_)
open import Verify-Budget-Sufficient.Caps-Face.Part1
  using (pathOrd?; pathPark?; parkStrat?; pathFloor)
open import Verify-Budget-Sufficient.Caps-Face.Part6
  using (switchKill-readings; thruConsume-readings; subscribeInner-readings)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- ONE-SLOT CONTEXT — used for switchKill and subscribeInner rows
-- where κ = root (pathFloor root = 1).
----------------------------------------------------------------------
Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

e₁ : Closed Γ₁ natᵗ
e₁ = input fzero

slots₁ : Slots Γ₁
slots₁ fzero = scripted (cold [] [])

-- nextNode = 1 makes pathOrd? true for nid = 0 at thru-outer
sched₁ : Sched Γ₁
sched₁ = record (sched-init e₁ slots₁) { nextNode = 1 }

st₁ : EvalSt e₁
st₁ = st-init e₁

-- A state with a mergeAll node at nid = 0, capacity 1, active 0:
-- hasRoom (just 1) 0 = 0 <ᵇ 1 = true → takes the hasRoom branch
st₁-node : EvalSt e₁
st₁-node = installNode 0 (mergeAll-st {t = natᵗ} (just 1) 0 [] false) st₁

-- A state with a mergeAll node at nid = 0, capacity 1, active 1:
-- hasRoom (just 1) 1 = 1 <ᵇ 1 = false → takes the no-room branch
st₁-full : EvalSt e₁
st₁-full = installNode 0 (mergeAll-st {t = natᵗ} (just 1) 1 [] false) st₁

----------------------------------------------------------------------
-- TWO-SLOT CONTEXT — used for the no-room refutation probe at
-- κ = share-sink fzero (pathFloor κ = 0).
----------------------------------------------------------------------
Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

e₂ : Closed Γ₂ natᵗ
e₂ = input fzero

slots₂ : Slots Γ₂
slots₂ fzero = scripted (cold [] [])
slots₂ (fsuc fzero) = scripted (cold [] [])

-- nextNode = 1, nid = 0, so pathOrd? 1 (thru-outer mergeAllᵒ 0 ↠ share-sink fzero)
-- = (1 ≤ᵇ 1) ∧ (0 ≤ᵇ 0) ∧ true = true
sched₂ : Sched Γ₂
sched₂ = record (sched-init e₂ slots₂) { nextNode = 1 }

st₂ : EvalSt e₂
st₂ = st-init e₂

-- node 0 at capacity 1, already active 1 → no room
st₂-full : EvalSt e₂
st₂-full = installNode 0 (mergeAll-st {t = natᵗ} (just 1) 1 [] false) st₂

----------------------------------------------------------------------
-- FIGURES: WHAT THE CONCLUSIONS ACTUALLY COMPUTE AT THE NO-ROOM CASE
-- WITH κ = share-sink fzero (pathFloor κ = 0) AND o = input fzero.
--
-- This is the load-bearing observation: parkStrat? 0 after parking
-- input fzero reads (0 <ᵇ 0) = false.  A tie asserting C3 = true
-- here cannot be given a refl body — it is a REFUTATION witness.
-- The figures row pins the actual boolean so the violation is visible.
----------------------------------------------------------------------
κ₂ : Path Γ₂ natᵗ natᵗ
κ₂ = share-sink fzero

o₂ : Closed Γ₂ natᵗ
o₂ = input fzero

thruResult₂ : _ × _ × Sched Γ₂ × EvalSt e₂
thruResult₂ = thruConsume (gs g0) mergeAllᵒ 0 κ₂ 0 0 o₂ sched₂ st₂-full

-- LOAD-BEARING: pins the three conclusion booleans after the no-room park.
-- C1 (pathOrd?) should stay true (nextNode unchanged in no-room branch).
-- C2 (pathPark?) should stay true (share-sink path always returns true).
-- C3 (parkStrat?) is the refutation: parks o₂ = input fzero with
--    pathFloor (share-sink fzero) = 0, so parkStrat? checks
--    inputsBelowᵉ 0 (input fzero) = (0 <ᵇ 0) = false.
thruConclusions₂ : Bool × Bool × Bool
thruConclusions₂ =
  let r = thruResult₂
      st-r = proj₂ (proj₂ (proj₂ r))
      sc-r = proj₁ (proj₂ (proj₂ r))
  in pathOrd? (Sched.nextNode sc-r) (thru-outer mergeAllᵒ 0 ↠ κ₂)
   , pathPark? κ₂ st-r
   , parkStrat? (pathFloor κ₂) (lookupNode 0 (EvalSt.nodes st-r))

-- LOAD-BEARING: C3 = false confirms the violation.
-- If this were true, thruConsume-readings would hold here; it being
-- false is the refutation of thruConsume-readings at this instantiation.
thruConclusions₂≡ : thruConclusions₂ ≡ (true , true , false)
thruConclusions₂≡ = refl

----------------------------------------------------------------------
-- FIGURES: WHAT THE CONCLUSIONS COMPUTE AT κ = root WITH FULL NODE.
-- pathFloor root = 1, inputsBelowᵉ 1 (input fzero) = (0 <ᵇ 1) = true,
-- so parkStrat? IS preserved here.  This row shows the boundary:
-- the refutation requires pathFloor κ < context size.
----------------------------------------------------------------------
κ₁ : Path Γ₁ natᵗ natᵗ
κ₁ = root

o₁ : Closed Γ₁ natᵗ
o₁ = input fzero

thruResult₁-full : _ × _ × Sched Γ₁ × EvalSt e₁
thruResult₁-full = thruConsume (gs g0) mergeAllᵒ 0 κ₁ 0 0 o₁ sched₁ st₁-full

-- LOAD-BEARING: at κ = root the park preserves parkStrat? because
-- pathFloor root = 1 and inputsBelowᵉ 1 (input fzero) = true.
thruConclusions₁-full : Bool × Bool × Bool
thruConclusions₁-full =
  let r = thruResult₁-full
      st-r = proj₂ (proj₂ (proj₂ r))
      sc-r = proj₁ (proj₂ (proj₂ r))
  in pathOrd? (Sched.nextNode sc-r) (thru-outer mergeAllᵒ 0 ↠ κ₁)
   , pathPark? κ₁ st-r
   , parkStrat? (pathFloor κ₁) (lookupNode 0 (EvalSt.nodes st-r))

-- LOAD-BEARING: all three conclusions are true here, showing the
-- boundary: the violation only occurs when pathFloor κ < n.
thruConclusions₁-full≡ : thruConclusions₁-full ≡ (true , true , true)
thruConclusions₁-full≡ = refl

----------------------------------------------------------------------
-- switchKill-readings TIES.
--
-- switchKill never modifies nodes or nextNode, so all three readings
-- are preserved at both shapes of `cur`.
----------------------------------------------------------------------

-- LOAD-BEARING: the `nothing` case — switchKill returns the inputs
-- unchanged, so all three conclusions are literally the three
-- hypotheses at the same state.
tieSwitchKillNothing : Confirms
  (switchKill-readings mergeAllᵒ 0 root nothing sched₁ st₁
     refl refl refl)
tieSwitchKillNothing = refl , refl , refl

-- LOAD-BEARING: the `just v` case — switchKill modifies registry,
-- cancelled, live but NOT nodes or nextNode.  pathOrd? reads nextNode
-- (unchanged), pathPark? and parkStrat? read nodes (unchanged).
-- The state has no registry entries so cutThrough returns empty lists.
tieSwitchKillJust : Confirms
  (switchKill-readings mergeAllᵒ 0 root (just 0) sched₁ st₁
     refl refl refl)
tieSwitchKillJust = refl , refl , refl

----------------------------------------------------------------------
-- thruConsume-readings TIES (identity path: missing node).
--
-- When lookupNode returns nothing (or the wrong type), thruConsume
-- is the identity and all readings are preserved.
----------------------------------------------------------------------

-- LOAD-BEARING: missing node at κ = root — thruConsume returns
-- ([], [], sched, st) unchanged.
tieThruConsumeIdentity : Confirms
  (thruConsume-readings (gs g0) mergeAllᵒ 0 root 0 0 o₁ sched₁ st₁
     refl refl refl)
tieThruConsumeIdentity = refl , refl , refl

----------------------------------------------------------------------
-- subscribeInner-readings TIES (g0 case).
--
-- subscribeInner g0 returns record sched { nextNode = suc inst } and
-- the ORIGINAL st.  Nodes are unchanged so pathPark? and parkStrat?
-- are identical to their hypothesis values.  pathOrd? is monotone in
-- nextNode: if suc nid ≤ nx then suc nid ≤ suc nx.
----------------------------------------------------------------------

-- LOAD-BEARING: g0 case at κ = root — nextNode bumped, st unchanged.
-- H1 had pathOrd? 1 (thru-outer mergeAllᵒ 0 ↠ root) = true;
-- conclusion reads pathOrd? 2 (...) which is also true by monotonicity.
tieSubscribeInnerG0 : Confirms
  (subscribeInner-readings g0 mergeAllᵒ 0 root 0 0 o₁ sched₁ st₁
     refl refl refl)
tieSubscribeInnerG0 = refl , refl , refl
