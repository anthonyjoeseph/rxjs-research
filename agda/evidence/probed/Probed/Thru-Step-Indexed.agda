-- ══════════════════════════════════════════════════════════════════
-- THE CONSUME STEP AT TWO GRANT INDICES, instantiated at the very
-- witness that killed the one-index form -- so the repair is measured
-- against the thing it was made for rather than against fresh programs
-- chosen to suit it.
--
-- PROBES: `refl` receipts at concrete programs.  See EVIDENCE.md.
--
-- WHAT IS LOAD-BEARING HERE IS NOT THE DOUBLING.  The delivered figure
-- is twice the arrival, and one step of the key buys a factor of
-- `(2 ^ S) ^ suc W`, which at any cap this statement admits is already
-- far above two -- so every row reading the VALUE conjunct is
-- DEGENERATE on the exponent and could not have failed.  That is worth
-- pinning exactly once, because it is the finding: the axis the
-- one-index form died on cannot reach the indexed one at all.
--
-- WHAT CAN FAIL is everything else, and one of them did.  The STORE
-- halves are taken at the arm that PARKS -- a merge whose limit is
-- already spent writes the arrival into its own queue, which is the one
-- place a step's store reading is the arrival's depth rather than the
-- table's, and the node goes from three to six against an incoming
-- three.  The two conjuncts that are not inequalities at all are taken
-- there too: the caps invariant the next step runs under and the slots
-- equation the walk re-enters at.
--
-- AND THE CAPS ONE HAD TO BE PAID FOR, which is why the field here is
-- two and not the arrival's own one: the node conjunct COUNTS the queue
-- as well as measuring it, so the parking arm overflows a field the
-- arrival fits in exactly.  Two is the smallest field the statement's
-- room premise admits at this node, so the rows are not bought by
-- widening.
--
-- AND THE VALUE CONJUNCT IS NOT REACHABLE BY THIS AXIS AT ALL, which
-- the tight rows at the bottom pin as arithmetic rather than as a
-- failed attempt: the cap bounds the arrival and the key's factor is
-- two to that cap, so a step delivering twice its arrival fits at
-- every program.  AND IT IS NOT THE DRAIN EITHER, which is the reading
-- this file used to carry: every arm of `thruConsume` subscribes the
-- arrival or parks it, and no arm reads a queue back, so the parked
-- figure is never a delivery.  The region left is the arrival's own
-- term, where nesting a duplicating substitution to depth `d` doubles
-- once per level against a `syncSizeᵛ` that grows by a constant per
-- level.  The rows below do not reach it.
--
-- TARGET: thruStep-merge
-- TARGET: thruStep-switch
-- TARGET: thruStep-exhaust
-- REFUTED: Refuted.Thru-Step-Caps
-- ══════════════════════════════════════════════════════════════════
module Probed.Thru-Step-Indexed where

open import Data.Bool using (Bool; true; false)
open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.List using ([]; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤ᵇ_; _^_; _*_; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; nat̂; strmᵗ; varᵗ; caseᵗ; inlᵗ; syncSizeᵛ; deferᵉ)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵛ)
open import Rx.Evaluator
  using (root; sched-init; st-init; EvalSt; Sched; Path; _↠_; thru-outer;
         mergeAllᵒ; switchᵒ; exhaustᵒ; installNode; mergeAll-st; switch-st;
         exhaust-st; thruConsume)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nestDᵛˢ; nestCapsOK?; nodesMax; nodeNestAt; nestStB?; nodeWidᴺ?)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

-- the duplicating step, verbatim from the witness that refuted the
-- one-index form: the payload lands in the map's step function and in
-- the source it maps over
dup : Fn Γ₂ [] [] [] (obs natᵗ) (obs natᵗ)
dup = strmᵗ (mapᵉ
        (caseᵗ (inlᵗ (varᵗ (there (here refl)))) (nat̂ 0) (varᵗ (here refl)))
        (ofᵉ (varᵗ (here refl) ∷ [])))

E : ℕ → Val Γ₂ (obs natᵗ)
E zero    = ofᵉ (nat̂ 0 ∷ [])
E (suc k) = mergeAllᵉ nothing (ofᵉ (strmᵗ (E k) ∷ []))

prog : Closed Γ₂ natᵗ
prog = ofᵉ (nat̂ 0 ∷ [])

arr : ℕ → Val Γ₂ (obs (obs natᵗ))
arr k = mapᵉ dup (ofᵉ (strmᵗ (E k) ∷ []))

κ : Path Γ₂ (obs natᵗ) natᵗ
κ = thru-outer mergeAllᵒ 0 ↠ root

sched₀ : Sched Γ₂
sched₀ = sched-init prog slots

stM stS stX : EvalSt prog
stM = installNode 7 (mergeAll-st {t = obs natᵗ} nothing 0 [] false)
                 (st-init prog)
stS = installNode 8 (switch-st nothing false) (st-init prog)
stX = installNode 9 (exhaust-st false false) (st-init prog)

cap : Caps
cap = caps (syncSizeᵛ (obs (obs natᵗ)) (arr 6))
           (pWᵛ 2 slots (obs (obs natᵗ)) (arr 6)) 0

-- the grant, written out because `nestB` is sealed, at `W = 0` -- the
-- smallest the statement can be read at
G : ℕ → ℕ → ℕ
G B m = (2 ^ Caps.cSize cap) ^ m * (B + suc m * nestUnit prog slots)

-- ── the value conjunct, and why it is degenerate ──────────────────

arrival : ℕ
arrival = nestDᵛ (obs (obs natᵗ)) (arr 6)

deliveredM deliveredS deliveredX : ℕ
deliveredM = nestDᵛˢ (proj₁ (thruConsume gasBig mergeAllᵒ 7 κ 0 0 (arr 6) sched₀ stM))
deliveredS = nestDᵛˢ (proj₁ (thruConsume gasBig switchᵒ 8 κ 0 0 (arr 6) sched₀ stS))
deliveredX = nestDᵛˢ (proj₁ (thruConsume gasBig exhaustᵒ 9 κ 0 0 (arr 6) sched₀ stX))

-- NON-VACUITY: a delivered reading over an empty burst measures nothing
burstLen : ℕ
burstLen = length (proj₁ (thruConsume gasBig mergeAllᵒ 7 κ 0 0 (arr 6) sched₀ stM))

burstLen≡1 : burstLen ≡ 1
burstLen≡1 = refl

figures : ℕ
figures = arrival + 100 * deliveredM + 10000 * deliveredS + 1000000 * deliveredX

figures≡ : figures ≡ 12121206
figures≡ = refl

-- the hypothesis at the TIGHTEST base the statement's own premise
-- admits: `B` chosen so the incoming grant at key zero is exactly the
-- arrival, so nothing is given away on the way in
Bmin : ℕ
Bmin = arrival

hypAtZero : (arrival ≤ᵇ G Bmin 0) ≡ true
hypAtZero = refl

-- DEGENERATE, and pinned as such: one step of the key clears a doubling
-- with room to spare that no arrival can consume, the factor being a
-- power of the same cap the arrival's own size is bounded by
valAtOne : ((deliveredM ≤ᵇ G Bmin 1) ≡ true)
         × ((deliveredS ≤ᵇ G Bmin 1) ≡ true)
         × ((deliveredX ≤ᵇ G Bmin 1) ≡ true)
valAtOne = refl , refl , refl

-- and the margin, so the degeneracy is a number rather than a claim
marginM : ℕ
marginM = G Bmin 1

marginM≡ : marginM ≡ 21990232555520
marginM≡ = refl

-- ── the conjuncts that can fail ───────────────────────────────────

-- the caps invariant the NEXT step runs under, and the slots equation
-- the walk re-enters at: neither is an inequality, so neither has an
-- exponent to hide behind
after : ∀ (o : Val Γ₂ (obs (obs natᵗ))) → Bool
after o = nestCapsOK? cap
            (proj₁ (proj₂ (proj₂ (thruConsume gasBig mergeAllᵒ 7 κ 0 0 o sched₀ stM))))
            (proj₂ (proj₂ (proj₂ (thruConsume gasBig mergeAllᵒ 7 κ 0 0 o sched₀ stM))))

prems : Bool × Bool
prems = nestValOK? cap (obs (obs natᵗ)) (arr 6)
      , nestCapsOK? cap sched₀ stM

prems≡ : prems ≡ (true , true)
prems≡ = refl

capsAfter≡ : after (arr 6) ≡ true
capsAfter≡ = refl

-- ── the store halves at the arm that SUBSCRIBES ───────────────────

-- the parking rows below reach the arm that writes a queue; this is
-- the other one, where the limit has room and the step runs the
-- `subscribeInner` all three heads share -- so what the store reads is
-- what the descent INSTALLED rather than what the caller handed in
rM : _
rM = thruConsume gasBig mergeAllᵒ 7 κ 0 0 (arr 6) sched₀ stM

-- AND THE STORE CANNOT BE ARMED HERE AT ALL, which is a boundary and
-- not a gap to fill.  A merge node's `nodeNest` is a fold over its
-- QUEUE, and the admit arm is the one with room, so it queues nothing;
-- every other node kind the descent installs reads zero by definition.
-- Deferring the inner does not move it either -- its body being unrun
-- leaves the node in the table, but an unlimited merge still parks
-- nothing -- so both readings are zero at both, pinned below rather
-- than dressed up as a fit.  The region where a subscribe DOES arm the
-- store is a LIMITED merge under the frame, and `Probed.Wrap-Nest-Frame`
-- is where it is taken.
arrD : ℕ → Val Γ₂ (obs (obs natᵗ))
arrD k = mapᵉ dup (ofᵉ (strmᵗ (deferᵉ (E k)) ∷ []))

rD : _
rD = thruConsume gasBig mergeAllᵒ 7 κ 0 0 (arrD 6) sched₀ stM

storeM : ℕ
storeM = nodesMax (proj₂ (proj₂ (proj₂ rM)))
       + 100 * nodeNestAt 7 (proj₂ (proj₂ (proj₂ rM)))
       + 10000 * nodesMax (proj₂ (proj₂ (proj₂ rD)))
       + 1000000 * nodeNestAt 7 (proj₂ (proj₂ (proj₂ rD)))

storeM≡ : storeM ≡ 0
storeM≡ = refl

-- ── the store halves, at the arm that PARKS ──────────────────────

-- a merge whose limit is already spent takes the arm that writes the
-- arrival into the node's own queue -- the one place a step's store
-- reading is the arrival's depth rather than the table's, and the only
-- arm where the conjunct is not `0 ≤ _` at these programs
stFull : EvalSt prog
stFull = installNode 7 (mergeAll-st {t = obs natᵗ} (just 1) 1 (arr 3 ∷ []) false)
                    (st-init prog)

-- the width field is TWO here, not the arrival's own one: the node
-- conjunct counts the queue as well as measuring it, and at a field of
-- one the parking arm overflows -- which is `Refuted.Thru-Step-Caps`
-- and is why the statement carries a room premise.  Two is the
-- smallest field the premise admits at this node, so nothing is given
-- away by widening it
capF : Caps
capF = caps (syncSizeᵛ (obs (obs natᵗ)) (arr 6)) 2 0

premF : (nestValOK? capF (obs (obs natᵗ)) (arr 6) ≡ true)
      × (nestCapsOK? capF sched₀ stFull ≡ true)
premF = refl , refl

rF : _
rF = thruConsume gasBig mergeAllᵒ 7 κ 0 0 (arr 6) sched₀ stFull

armed : ℕ
armed = nodeNestAt 7 stFull

storeF : ℕ
storeF = armed
       + 100 * nodeNestAt 7 (proj₂ (proj₂ (proj₂ rF)))
       + 10000 * nodesMax (proj₂ (proj₂ (proj₂ rF)))

storeF≡ : storeF ≡ 60603
storeF≡ = refl

-- the conjuncts themselves at that arm, where what the node ends up
-- holding is the arrival and the grant is what has to cover it
fitsF : ((nodeNestAt 7 (proj₂ (proj₂ (proj₂ rF))) ≤ᵇ armed ⊔ G Bmin 1) ≡ true)
      × ((nodesMax (proj₂ (proj₂ (proj₂ rF))) ≤ᵇ nodesMax stFull ⊔ G Bmin 1) ≡ true)
      × (nestCapsOK? capF (proj₁ (proj₂ (proj₂ rF))) (proj₂ (proj₂ (proj₂ rF))) ≡ true)
fitsF = refl , refl , refl

-- both halves of the node conjunct, at the arm that writes the queue
parts : Bool × Bool
parts =
  nestStB? (Caps.cSize capF) (proj₁ (proj₂ (proj₂ rF))) (proj₂ (proj₂ (proj₂ rF)))
  , all (λ kv → nodeWidᴺ? (Caps.cWid capF) (Sched.slots (proj₁ (proj₂ (proj₂ rF)))) (proj₂ kv))
        (EvalSt.nodes (proj₂ (proj₂ (proj₂ rF))))

parts≡ : parts ≡ (true , true)
parts≡ = refl

-- ── the value conjunct where the two sides are COMPARABLE ─────────

-- the rows above are degenerate for a reason that is about the CAP and
-- not about the program's depth: the key's factor is a power of
-- `cSize`, `cSize` is read off the arrival's own size, and the step
-- only doubles.  So the way to bring the two sides together is a
-- SHALLOWER arrival, not a deeper program -- which is the cheap
-- direction, since the harness cost is geometric in depth
capT : Caps
capT = caps (syncSizeᵛ (obs (obs natᵗ)) (arr 1))
            (pWᵛ 2 slots (obs (obs natᵗ)) (arr 1)) 0

GT : ℕ → ℕ → ℕ
GT B m = (2 ^ Caps.cSize capT) ^ m * (B + suc m * nestUnit prog slots)

arrivalT deliveredT : ℕ
arrivalT = nestDᵛ (obs (obs natᵗ)) (arr 1)
deliveredT =
  nestDᵛˢ (proj₁ (thruConsume gasBig mergeAllᵒ 7 κ 0 0 (arr 1) sched₀ stM))

tightFigures : ℕ
tightFigures = arrivalT + 100 * deliveredT + 10000 * Caps.cSize capT
             + 1000000 * nestUnit prog slots

tightFigures≡ : tightFigures ≡ 2210201
tightFigures≡ = refl

-- the conjunct itself at those caps, DEGENERATE like every other row
-- on this axis and kept because it makes the gap a number: two against
-- ten million, at the shallowest arrival there is
valTight : (deliveredT ≤ᵇ GT arrivalT 1) ≡ true
valTight = refl

-- AND THE AXIS CANNOT REFUTE, WHICH IS THE FINDING RATHER THAN THE
-- FAILED ATTEMPT.  The reading above is arrival 1, delivered 2, unit 2
-- and `cSize` TWENTY-ONE -- at the shallowest arrival the harness has.
-- `cSize` is the arrival's `syncSizeᵛ`, which measures the TERM, and a
-- step that duplicates needs a term big enough to do it, so shrinking
-- the arrival's depth does not shrink the cap.
--
-- Worse for the sweep, and this is what closes it: the same `cSize`
-- bounds the arrival, through the very `nestValOK?` premise the
-- statement carries.  So for any step delivering at most twice its
-- arrival, the conjunct at one key reads `2 * arrival ≤ (2 ^ cSize) * _`
-- with `arrival ≤ cSize` -- and `2 * k ≤ 2 ^ k` at every `k`, with
-- equality only at one and two.  No program refutes that, so no sweep
-- over arrivals is worth running: the axis moves the bound side faster
-- than the measure side by construction.
--
-- WHERE THE RISK ACTUALLY LIVES is a step whose delivery is NOT linear
-- in its arrival -- the merge DRAIN, which hands over a queue parked by
-- earlier arrivals and so is bounded by the node's width rather than by
-- the value in hand.  That is the region an instantiation would have to
-- reach, and these rows do not reach it.

-- ── THE NESTED DUPLICATOR, which is the axis the receipt names ────

-- `arr` applies the substituting step ONCE; this nests it, so the
-- arrival's delivery compounds per level instead of doubling once
Dn : ℕ → Val Γ₂ (obs (obs natᵗ))
Dn zero    = ofᵉ (strmᵗ (mergeAllᵉ nothing
               (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))) ∷ [])
Dn (suc k) = mapᵉ dup (mergeAllᵉ nothing (ofᵉ (strmᵗ (Dn k) ∷ [])))

capN : ℕ → Caps
capN k = caps (syncSizeᵛ (obs (obs natᵗ)) (Dn k))
              (pWᵛ 2 slots (obs (obs natᵗ)) (Dn k)) 0

GN : ℕ → ℕ → ℕ → ℕ
GN k B m = (2 ^ Caps.cSize (capN k)) ^ m * (B + suc m * nestUnit prog slots)

arrN delN : ℕ → ℕ
arrN k = nestDᵛ (obs (obs natᵗ)) (Dn k)
delN k = nestDᵛˢ (proj₁ (thruConsume gasBig mergeAllᵒ 7 κ 0 0 (Dn k) sched₀ stM))

nestedFigures : ℕ
nestedFigures = arrN 1 + 10 * delN 1 + 100 * arrN 2 + 1000 * delN 2
              + 10000 * arrN 3 + 100000 * delN 3

nestedFigures≡ : nestedFigures ≡ 844322
nestedFigures≡ = refl

premN : Bool × Bool
premN = nestValOK? (capN 3) (obs (obs natᵗ)) (Dn 3)
      , nestCapsOK? (capN 3) sched₀ stM

premN≡ : premN ≡ (true , true)
premN≡ = refl

fitN1 : (delN 1 ≤ᵇ GN 1 (arrN 1) 1) ≡ true
fitN1 = refl

fitN2 : (delN 2 ≤ᵇ GN 2 (arrN 2) 1) ≡ true
fitN2 = refl

fitN3 : (delN 3 ≤ᵇ GN 3 (arrN 3) 1) ≡ true
fitN3 = refl
