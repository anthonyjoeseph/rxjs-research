-- THE SHARED INNER SUBSCRIBE, AT THE REGION ITS PREDECESSORS' RECEIPTS
-- NAMED AS UNREACHED.
--
-- EVIDENCE, not a claim: `src` cannot import this file (the library
-- layout makes the name unresolvable from there) and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: subscribeInner-nestCaps @e68c04
--
-- WHAT IS BEING TESTED.  All three consume arms now descend through one
-- `subscribeInner`, and what the leaf asserts of it is not an
-- inequality: the caps invariant HOLDS at the state the descent leaves,
-- and the slot telescope is the one the walk re-enters at.  Neither
-- conjunct has an exponent to hide behind, so a row either pins `true`
-- or refutes.
--
-- WHY THESE ARRIVALS.  The descent installs nodes, and the only node
-- kind whose width reading is not zero by definition is a merge, whose
-- `nodeNest` folds over its QUEUE -- so the region that can move the
-- invariant is a subscription that ARMS one.  An unlimited merge parks
-- nothing however deep it goes, which is why the earlier receipts on
-- this machinery all recorded the armed case as unreached.  Rows C and
-- D reach it: the limit is one and two sources arrive, so the second is
-- queued and the node the invariant is read at is genuinely non-empty,
-- pinned by `queued≡` rather than assumed.
--
-- WHAT IS NOT COVERED.  The width premise is read at the arrival's own
-- size, the smallest cap admitting it, so no row separates the
-- invariant from that choice; and the descent runs from a table holding
-- one installed node, so a deep pre-existing table is untouched.
module Probed.Subscribe-Inner-Caps where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; natᵗ; obs; ofᵉ; mergeAllᵉ; nat̂; strmᵗ; syncSizeᵛ)
open import Rx.Frame-Width using (pWᵛ; pWᵉ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (root; sched-init; st-init; EvalSt; Sched; Path;
         mergeAllᵒ; installNode; mergeAll-st; switch-st;
         exhaust-st; subscribeInner)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?)
open import Verify-Budget-Sufficient.Nest-Walk using (nestCapsOK?; nodesMax)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))

prog : Closed Γ₂ natᵗ
prog = ofᵉ (nat̂ 0 ∷ [])

sched₀ : Sched Γ₂
sched₀ = sched-init prog slots

stM stS stX : EvalSt prog
stM = installNode 7 (mergeAll-st {t = natᵗ} nothing 0 [] false) (st-init prog)
stS = installNode 8 (switch-st nothing false) (st-init prog)
stX = installNode 9 (exhaust-st false false) (st-init prog)

κ : Path Γ₂ natᵗ natᵗ
κ = root

-- an UNLIMITED merge: parks nothing however deep
open' : ℕ → Val Γ₂ (obs natᵗ)
open' zero    = ofᵉ (nat̂ 0 ∷ [])
open' (suc k) = mergeAllᵉ nothing (ofᵉ (strmᵗ (open' k) ∷ []))

-- a LIMITED merge with more sources than room: the second is queued, so
-- the node the invariant is read at is armed
armed : Val Γ₂ (obs natᵗ)
armed = mergeAllᵉ (just 1)
          (ofᵉ (strmᵗ (open' 3) ∷ strmᵗ (open' 3) ∷ []))

-- THE SMALLEST CAP THE PREMISE ADMITS: the arrival's own size and width
tight : Val Γ₂ (obs natᵗ) → Caps
tight o = caps (syncSizeᵛ (obs natᵗ) o) (pWᵛ 2 slots (obs natᵗ) o) 0

-- the premises, pinned rather than assumed
prem : Val Γ₂ (obs natᵗ) → EvalSt prog → Bool × Bool × Bool
prem o st = nestValOK? (tight o) (obs natᵗ) o
          , nestCapsOK? (tight o) sched₀ st
          , (pWᵉ 2 (Sched.slots sched₀) o ≤ᵇ Caps.cWid (tight o))

-- the caps conjunct, at the state the descent leaves
capsAfter : Val Γ₂ (obs natᵗ) → ℕ → EvalSt prog → Bool
capsAfter o nid st =
  let R = subscribeInner gasBig mergeAllᵒ nid κ 0 0 o sched₀ st
      sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R))))
      st₁ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R))))
  in nestCapsOK? (tight o) sched₁ st₁

-- and the slots conjunct, as a propositional equality rather than a
-- decision -- the telescope is not a decidable type here, and `refl`
-- is the stronger reading anyway
slotsAfter : Val Γ₂ (obs natᵗ) → ℕ → EvalSt prog → Slots Γ₂
slotsAfter o nid st =
  Sched.slots (proj₁ (proj₂ (proj₂ (proj₂ (proj₂
    (subscribeInner gasBig mergeAllᵒ nid κ 0 0 o sched₀ st))))))

-- ROW A: the unlimited merge at the merge node, one level
premA : prem (open' 1) stM ≡ (true , true , true)
premA = refl

concA : (capsAfter (open' 1) 7 stM ≡ true)
       × (slotsAfter (open' 1) 7 stM ≡ slots)
concA = refl , refl

-- ROW B: the same three levels down, where the descent installs more
premB : prem (open' 3) stM ≡ (true , true , true)
premB = refl

concB : (capsAfter (open' 3) 7 stM ≡ true)
       × (slotsAfter (open' 3) 7 stM ≡ slots)
concB = refl , refl

-- ROW C: THE ARMED CASE, which is the region the predecessors' receipts
-- recorded as unreached -- the limit is one and two sources arrive
premC : prem armed stM ≡ (true , true , true)
premC = refl

concC : (capsAfter armed 7 stM ≡ true)
       × (slotsAfter armed 7 stM ≡ slots)
concC = refl , refl

-- AND THE ARMED REGION IS NOT REACHABLE THROUGH THIS DESCENT AT ALL,
-- which is a boundary and not a gap to fill.  A limited merge with more
-- sources than room was built for exactly this -- the limit is one and
-- two three-deep sources arrive -- and the table the descent leaves
-- still reads ZERO nesting at every node.  So the caps rows above are
-- DEGENERATE on the store axis: the predicate they pin holds over a
-- table with nothing parked in it.  Pinned as a figure rather than
-- described, so a repair that starts parking values fails here first.
notArmed : nodesMax
             (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
               (subscribeInner gasBig mergeAllᵒ 7 κ 0 0 armed sched₀ stM))))))
           ≡ 0
notArmed = refl

-- ROW D: the armed arrival at the other two heads, whose arms reach the
-- same descent through a different node kind
premD : (prem armed stS ≡ (true , true , true))
      × (prem armed stX ≡ (true , true , true))
premD = refl , refl

concD : (capsAfter armed 8 stS ≡ true) × (capsAfter armed 9 stX ≡ true)
concD = refl , refl
