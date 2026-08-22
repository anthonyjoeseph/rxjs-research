-- THE DEPTH FACE'S NEW CURRENCY, INSTANTIATED AT THE FOUR PROGRAMS
-- THAT KILLED THE OLD ONE.
-- TARGET: depth-hop-all-burst
--
-- EVIDENCE, not a claim: `src` cannot import this file (the library
-- layout makes `Probed.Depth-Hop` unresolvable from there) and nothing
-- in the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHY THESE FOUR PROGRAMS AND NOT EASIER ONES.  They are the witnesses
-- that refuted `depth-hop`'s predecessor `depth-compositional` and its
-- cap (Depth-Compositional's header carries the refutation; the
-- refutation files went with the statement they refuted).  § 1 and § 2
-- put a payload variable in a scan's SOURCE and re-wrap the
-- accumulator in the step, so the old cap's product term charged
-- nothing and the depth ran to 4 and 8 against a cap of 3.  § 3 and
-- § 4 are the quadratic gadget: a scan whose step merges its
-- accumulator with a constant emitter, whose emission count is
-- quadratic in the tick count while every term of a syntactic sum is
-- linear — depth 35 at four ticks and 70 at six.  So this is a probe
-- reaching the RISKY region rather than a degenerate one: these four
-- programs ARE the region.
--
-- EVERY ROW IS LOAD-BEARING, and the way it could fail is the point.
-- `hopDᵉ`'s scan clause is `(2 + pmᵗ V 0 f) ^ V * (…)`, an EXPONENTIAL
-- in the refold bound `V`, so a row is a real test only at a `V` small
-- enough that the exponential has not swallowed the question.  The
-- depths are pinned by `refl` beside each domination row, so a row
-- cannot pass by the left-hand side collapsing to 0.
--
-- ⚠ AND THE COVERAGE IS `V ∈ {1, 4}`, WHICH IS THE BOUNDARY THAT
-- MATTERS MOST HERE — `V = 1` only on the two small programs, since the
-- gadget needs the exponential.  Monotonicity of `hopDᵉ` in `V` is not
-- proven anywhere, so NO row transfers to another `V`; and `V` is chosen
-- adequate for the whole program in every section below, so a def large
-- against a small `V` is a region this file does not reach at all —
-- `Refuted.Depth-Hop` is what stands there.  The non-root path, both
-- `Slot` constructors and a mid-run store are reached, in § 5 to § 7 and
-- § 11.
-- WHAT THIS FILE IS EVIDENCE FOR, AND WHICH ROWS CARRY IT.  `depth-hop`
-- is a real body over ONE leaf — `depth-hop-all-burst`, the `thru-outer`
-- walk arm — and that leaf carries the same three conditions every row
-- below instantiates.  So a row whose program contains a `*All`
-- constructor runs through the leaf and is LOAD-BEARING for it: § 5,
-- § 10, § 11 and § 12's refold.  The scan, slot and parking rows —
-- § 1 to § 4 and § 6 to § 9 — are DEGENERATE for the leaf, since the
-- clauses they exercise close without it; they are kept as coverage of
-- the currency, which is what the conditions are stated over.

module Probed.Depth-Hop where

open import Data.Bool using (true; false)
open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Vec using (_∷_) renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Product using (proj₁; proj₂; _×_)

open import Rx.Prim using (Gas; g0; gs; cold)
open import Rx.Exp using (Ctx; Closed; Exp; Fn; natᵗ; obs; _×ᵗ_; nat̂; strmᵗ; varᵗ;
  ofᵉ; emptyᵉ; mapᵉ; scanᵉ; mergeAllᵉ; fstᵗ; input; deferᵉ; μᵉ; varᵉ; takeᵉ;
  concatAllᵉ; switchAllᵉ; exhaustAllᵉ; sizeᵉ; syncSizeᵉ; unfoldμ)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Evaluator using (Sched; EvalSt; root; share-sink; _↠_;
  from-inner; thru-outer; mergeᵒ; sched-init; st-init; subscribeE; Stream)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)
open import Verify-Budget-Sufficient.Depth-Compositional using (pathNestD)

gN : ℕ → Gas
gN zero    = g0
gN (suc n) = gs (gN n)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

slots₀ : Slots Γ₀
slots₀ ()

-- the step RE-WRAPS its accumulator: one `*All` layer per delivered payload
gA : Fn Γ₀ [] [] (obs natᵗ ∷ []) (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
gA = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

-- and the payload variable sits in the scan's SOURCE, so the count the
-- old cap's product term read was the variable's own width — zero
fA : Fn Γ₀ [] [] [] (obs natᵗ) (obs (obs natᵗ))
fA = strmᵗ (scanᵉ gA (strmᵗ emptyᵉ) (mergeAllᵉ (ofᵉ (varᵗ (here refl) ∷ []))))

------------------------------------------------------------------
-- § 1  three payloads — the depth the old cap read 3 against
------------------------------------------------------------------

progA : Closed Γ₀ natᵗ
progA = mergeAllᵉ (mergeAllᵉ (mapᵉ fA (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])) ∷ []))))

schedA : Sched Γ₀
schedA = sched-init progA slots₀

stA : EvalSt progA
stA = st-init progA

_ : depthE (gN 20) progA root 0 0 schedA stA ≡ 4
_ = refl

_ : (depthE (gN 20) progA root 0 0 schedA stA
       ≤ᵇ hopDᵉ 1 (slotHop 1 slots₀) progA + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

_ : (depthE (gN 20) progA root 0 0 schedA stA
       ≤ᵇ hopDᵉ 4 (slotHop 4 slots₀) progA + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

------------------------------------------------------------------
-- § 2  seven payloads — the gap is the PAYLOAD COUNT, so this row is
-- what says no constant repair reaches the old cap: the depth doubles
-- while a syntactic measure of this program does not.
--
-- ⚠ AND THIS PROGRAM IS WHERE THE REFOLD FACTOR IS THE WHOLE MARGIN.
-- Its widening lives in a LITERAL LIST, which `hopDᵉ` charges 0 for at
-- every `V` (`hopDᵗ (nat̂ _) = 0`), so nothing but the scan's
-- `(2 + pmᵗ V 0 f) ^ V` grows when the source goes three literals to
-- seven — while `depthE` doubles to 8.  The `V = 1` row below therefore
-- holds with NO ROOM AT ALL, which is the strongest form a green row
-- comes in and the reason it is worth re-running after anything touches
-- the refold clause.  One step down, at `V = 0`, the factor is 1 and
-- this program REFUTES the bound: that is `Refuted.Depth-Hop`, and it is
-- why the statement conditions `V` at all.
------------------------------------------------------------------

progB : Closed Γ₀ natᵗ
progB = mergeAllᵉ (mergeAllᵉ (mapᵉ fA
          (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ nat̂ 5 ∷ nat̂ 6 ∷ [])) ∷ []))))

schedB : Sched Γ₀
schedB = sched-init progB slots₀

stB : EvalSt progB
stB = st-init progB

_ : depthE (gN 20) progB root 0 0 schedB stB ≡ 8
_ = refl

_ : (depthE (gN 20) progB root 0 0 schedB stB
       ≤ᵇ hopDᵉ 1 (slotHop 1 slots₀) progB + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

_ : (depthE (gN 20) progB root 0 0 schedB stB
       ≤ᵇ hopDᵉ 4 (slotHop 4 slots₀) progB + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

------------------------------------------------------------------
-- § 3 and § 4  THE QUADRATIC GADGET.  The step merges the accumulator
-- with a CONSTANT emitter, so emissions grow by a constant per tick
-- and the `*All` over the scan runs over every accumulator emitted.
-- The step is ADDITIVE and not duplicating on purpose: doubling the
-- accumulator doubles its SYNTAX per tick too, and normalising that
-- costs minutes where this costs seconds.
------------------------------------------------------------------

dupF : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
dupF = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl))
         ∷ strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])) ∷ [])))

vD : Closed Γ₀ natᵗ
vD = mergeAllᵉ (scanᵉ dupF (strmᵗ (ofᵉ (nat̂ 0 ∷ []))) (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])))

progD : Closed Γ₀ natᵗ
progD = mergeAllᵉ (mergeAllᵉ (mapᵉ fA (ofᵉ (strmᵗ vD ∷ []))))

schedD : Sched Γ₀
schedD = sched-init progD slots₀

stD : EvalSt progD
stD = st-init progD

_ : depthE (gN 200) progD root 0 0 schedD stD ≡ 35
_ = refl

_ : (depthE (gN 200) progD root 0 0 schedD stD
       ≤ᵇ hopDᵉ 4 (slotHop 4 slots₀) progD + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

vC : Closed Γ₀ natᵗ
vC = mergeAllᵉ (scanᵉ dupF (strmᵗ (ofᵉ (nat̂ 0 ∷ [])))
       (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ nat̂ 5 ∷ [])))

progC : Closed Γ₀ natᵗ
progC = mergeAllᵉ (mergeAllᵉ (mapᵉ fA (ofᵉ (strmᵗ vC ∷ []))))

schedC : Sched Γ₀
schedC = sched-init progC slots₀

stC : EvalSt progC
stC = st-init progC

-- the row the old cap lost by: 70 against a syntactic sum of 56
_ : depthE (gN 200) progC root 0 0 schedC stC ≡ 70
_ = refl

_ : (depthE (gN 200) progC root 0 0 schedC stC
       ≤ᵇ hopDᵉ 4 (slotHop 4 slots₀) progC + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

------------------------------------------------------------------
-- § 5  THE SLOT TELESCOPE — the `input` clause, which every row
--      above leaves untouched (they all run at `Γ₀`, where `Slots`
--      is the empty function and `η` is never read).
--
-- This is the region the PREDECESSOR was refuted in: its measure
-- charged an `input` nothing, and `input-wet` exhibited an obs-typed
-- shared slot whose def emits values of positive hop.  `hopDᵉ` takes
-- an `η` for exactly that reason, and `slotHop` is the honest one.
-- So these rows test the repair, not the measure's arithmetic.
--
-- ⚠ AND THEY REACH THE STRATIFICATION, WHICH IS THE POINT.  Slot 1's
-- def READS slot 0, so `slotHop` must resolve slot 1 at stage 1 —
-- `ηAt`'s `suc k` branch, whose `k = 0` case is vacuous and which
-- Demand-Probe series W therefore never exercised (recorded in
-- `Rx.Slot-Hop`'s own header).  A one-slot telescope would have been
-- a degenerate row here; a chain of two is not.
------------------------------------------------------------------

Γ₂ : Ctx 2
Γ₂ = obs natᵗ ∷ obs natᵗ ∷ []ⱽ

-- slot 0: no inputs at all (stratification forbids them at index 0),
-- and a `*All` layer so its hop is positive rather than 0
d₀ : Closed Γ₂ (obs natᵗ)
d₀ = ofᵉ (strmᵗ (mergeAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 7 ∷ [])) ∷ []))) ∷ [])

-- slot 1: READS SLOT 0, which is what makes stage 1 load-bearing
d₁ : Closed Γ₂ (obs natᵗ)
d₁ = ofᵉ (strmᵗ (mergeAllᵉ (input zero)) ∷ [])

slots₂ : Slots Γ₂
slots₂ zero          = shared d₀
slots₂ (suc zero)     = shared d₁
slots₂ (suc (suc ()))

-- the program is the input itself, wrapped once so it is `natᵗ`-typed
progE : Closed Γ₂ natᵗ
progE = mergeAllᵉ (input (suc zero))

schedE : Sched Γ₂
schedE = sched-init progE slots₂

stE : EvalSt progE
stE = st-init progE

-- LOAD-BEARING, and tight: 3 against 3, with 2 of the 3 units coming
-- out of the η chain rather than the program's own syntax
_ : depthE (gN 20) progE root 0 0 schedE stE ≡ 3
_ = refl

_ : (depthE (gN 20) progE root 0 0 schedE stE
       ≤ᵇ hopDᵉ 4 (slotHop 4 slots₂) progE + pathNestD (root {Γ = Γ₂} {t = natᵗ}))
      ≡ true
_ = refl

_ : (depthE (gN 20) progE root 0 0 schedE stE
       ≤ᵇ hopDᵉ 1 (slotHop 1 slots₂) progE + pathNestD (root {Γ = Γ₂} {t = natᵗ}))
      ≡ true
_ = refl

------------------------------------------------------------------
-- § 6  A SCRIPTED SLOT IS CHARGED 0 — the other `Slot` constructor,
-- and the one where the charge could be too small by construction.
-- `slotHopD (scripted _) = 0` rests on the data-only side condition
-- (`T (isData t)`): no emission of a scripted slot can hold an
-- observable, so nothing it delivers is ever subscribed.
--
-- ⚠ SO THE PROGRAM HAS TO PUT THE SUBSCRIPTION SOMEWHERE ELSE, or the
-- row is not a row.  Reading a scripted slot and stopping gives depth
-- 0 against a bound of 0 — measured, and unfalsifiable, since a
-- data-only pipeline cannot have positive depth by construction.  So
-- the map's FUNCTION mints the observable and `mergeAllᵉ` subscribes
-- it: the depth is then positive and paid for entirely by `hopDᵗ f`,
-- and the row fails if `depthE` charges anything at all for the trip
-- through the slot.
------------------------------------------------------------------

Γ₃ : Ctx 1
Γ₃ = natᵗ ∷ []ⱽ

slots₃ : Slots Γ₃
slots₃ zero     = scripted (cold (3 ∷ 4 ∷ []) [])
slots₃ (suc ())

-- the payload becomes a one-element observable, so the subscription is
-- the FUNCTION's and not the slot's
fS : Fn Γ₃ [] [] [] natᵗ (obs natᵗ)
fS = strmᵗ (ofᵉ (varᵗ (here refl) ∷ []))

progF : Closed Γ₃ natᵗ
progF = mergeAllᵉ (mapᵉ fS (input zero))

schedF : Sched Γ₃
schedF = sched-init progF slots₃

stF : EvalSt progF
stF = st-init progF

-- LOAD-BEARING, and tight: 1 against 1
_ : depthE (gN 20) progF root 0 0 schedF stF ≡ 1
_ = refl

_ : (depthE (gN 20) progF root 0 0 schedF stF
       ≤ᵇ hopDᵉ 4 (slotHop 4 slots₃) progF + pathNestD (root {Γ = Γ₃} {t = natᵗ}))
      ≡ true
_ = refl

_ : (depthE (gN 20) progF root 0 0 schedF stF
       ≤ᵇ hopDᵉ 1 (slotHop 1 slots₃) progF + pathNestD (root {Γ = Γ₃} {t = natᵗ}))
      ≡ true
_ = refl

------------------------------------------------------------------
-- § 7  OFF THE ROOT PATH — `pathNestD κ` is the whole of the
-- statement's path term, and it charges NOTHING for four of the five
-- frames.  Only `thru-outer` is a `suc`.  So the sharp question is
-- whether `depthE` grows along a path built entirely out of the free
-- ones; if it does, the statement is false with no repair available
-- in `hopDᵉ`, since `hopDᵉ` never sees `κ` at all.
--
-- ⚠ THE PAIRINGS BELOW ARE NOT CLAIMED REACHABLE, and they do not
-- need to be: `depth-hop` quantifies over `b` and `κ` INDEPENDENTLY,
-- so any well-typed pair is a legitimate instantiation of the
-- statement as written.  The states are still reached honestly —
-- `sched-init`/`st-init`, never a record update.  A FAILING row here
-- would make reachability the next question rather than the finding.
--
-- ⚠⚠ AND THE ANSWER MEASURED IS 0 AT EVERY PATH TRIED — 0 against
-- bounds of 0, 2 and 1.  `depthE` does not read `κ` at the call it is
-- given; the path only starts costing anything when a clause EXTENDS
-- it, descending into a subscribed inner.  So the first row below is
-- the load-bearing one (0 against 0: it fails if a single frame is
-- charged anything), and the two after it are SLACK — genuine, since a
-- charge of 3 for a share sink would have shown up, but they pin
-- nothing tight.
--
-- ⚠⚠ WHICH MEANS `pathNestD κ` IS STILL UNEXERCISED, and that is the
-- coverage boundary to carry into the grind: no row here needs the
-- term to be there at all.  A statement with a slack term is weaker
-- rather than wrong, so this is not a refutation — but whoever grinds
-- the `thru-outer` clause should find out whether the term is
-- load-bearing in the INDUCTION before assuming it must be carried.
------------------------------------------------------------------

-- hop 0, so the bound is `pathNestD κ` alone and nothing hides in it
bFlat : Closed Γ₀ natᵗ
bFlat = ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ [])

-- hop 1, an inner observable waiting to be subscribed
bObs : Closed Γ₀ (obs natᵗ)
bObs = ofᵉ (strmᵗ (mergeAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ [])) ∷ []))) ∷ [])

-- TWO `from-inner` FRAMES AND A `take`-shaped map: `pathNestD` is 0 on
-- all of them, so this row demands `depthE` be 0 outright
-- LOAD-BEARING: both sides are 0, so any charge at all breaks it
_ : depthE (gN 20) bFlat
      (from-inner mergeᵒ 1 2 ↠ (from-inner mergeᵒ 3 4 ↠ root)) 0 0 schedA stA
      ≡ 0
_ = refl

_ : (depthE (gN 20) bFlat
       (from-inner mergeᵒ 1 2 ↠ (from-inner mergeᵒ 3 4 ↠ root)) 0 0 schedA stA
       ≤ᵇ hopDᵉ 4 (slotHop 4 slots₀) bFlat
           + pathNestD (from-inner mergeᵒ 1 2
                         ↠ (from-inner mergeᵒ 3 4 ↠ root {Γ = Γ₀} {t = natᵗ})))
      ≡ true
_ = refl

-- and one `thru-outer`, the only frame that pays: 0 against 1 + 1, so
-- SLACK — it would have caught a charge of 3, and nothing smaller
_ : (depthE (gN 20) bObs (thru-outer mergeᵒ 5 ↠ root) 0 0 schedA stA
       ≤ᵇ hopDᵉ 4 (slotHop 4 slots₀) bObs
           + pathNestD (thru-outer mergeᵒ 5 ↠ root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

-- A SHARE SINK, the third `Path` constructor, which `pathNestD` also
-- charges 0 for.  Its slot is the shared chain of § 5, so the values
-- landing in the subject are the ones with positive hop — 0 against 1,
-- SLACK in the same way.
bIn : Closed Γ₂ (obs natᵗ)
bIn = input zero

_ : (depthE (gN 20) bIn (share-sink zero) 0 0 schedE stE
       ≤ᵇ hopDᵉ 4 (slotHop 4 slots₂) bIn
           + pathNestD (share-sink {Γ = Γ₂} {t = natᵗ} zero))
      ≡ true
_ = refl

------------------------------------------------------------------
-- § 8  THE OTHER CONSTANT-ZERO CLAUSE — `hopDᵉ V η (deferᵉ e) = 0`,
-- which charges NOTHING for an arbitrarily deep body.  That is the
-- same shape as the `input` clause the predecessor died on, so it is
-- the sharpest thing left to instantiate: wrap the deepest program in
-- this file and the bound goes to 0 while the body's own depth is 4.
--
-- It survives, and the reason is the one the clause is named for: a
-- `deferᵉ` subscribes its body at the NEXT tick, so nothing of the
-- body's depth is spent in the frame `depthE` is asked about.  Note
-- that `inputsBelowᵉ` deliberately does NOT cut at `deferᵉ` (recorded
-- in `Rx.Exp`) while `hopDᵉ` does — the two answer different
-- questions, and this row is why the second cut is sound.
------------------------------------------------------------------

progG : Closed Γ₀ natᵗ
progG = deferᵉ progA

schedG : Sched Γ₀
schedG = sched-init progG slots₀

stG : EvalSt progG
stG = st-init progG

-- LOAD-BEARING at its sharpest: the bound is 0 and the body's own
-- depth is 4, so the row fails unless the defer really does cost
-- nothing in this frame
_ : hopDᵉ 4 (slotHop 4 slots₀) progG ≡ 0
_ = refl

_ : (depthE (gN 20) progG root 0 0 schedG stG
       ≤ᵇ hopDᵉ 4 (slotHop 4 slots₀) progG + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

-- and once more with the defer INSIDE a subscribing layer, so the
-- frame that would pay for it is a `*All` rather than the root
progH : Closed Γ₀ natᵗ
progH = mergeAllᵉ (ofᵉ (strmᵗ (deferᵉ progA) ∷ []))

schedH : Sched Γ₀
schedH = sched-init progH slots₀

stH : EvalSt progH
stH = st-init progH

-- LOAD-BEARING, and tight: 1 against 1
_ : hopDᵉ 4 (slotHop 4 slots₀) progH ≡ 1
_ = refl

_ : depthE (gN 20) progH root 0 0 schedH stH ≡ 1
_ = refl

_ : (depthE (gN 20) progH root 0 0 schedH stH
       ≤ᵇ hopDᵉ 4 (slotHop 4 slots₀) progH + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

------------------------------------------------------------------
-- § 9  THE FIXPOINT AND THE TAKE — the two remaining clauses that
-- pass their subject's hop straight through: `hopDᵉ (μᵉ e) = hopDᵉ e`
-- and `hopDᵉ (takeᵉ c e) = hopDᵉ e`.  The μ one is the sharp case,
-- because a μ RE-SUBSCRIBES: the program below unfolds once per tick
-- for as long as the gas lasts, and the bound does not grow with it.
-- What makes that sound is that the recursive reference is reachable
-- only through a `deferᵉ` (synchronous self-reference is a type
-- error), so each unfolding lands in a LATER frame than the one
-- `depthE` is asked about — the § 8 fact, spent recursively.
------------------------------------------------------------------

progI : Closed Γ₀ natᵗ
progI = μᵉ (mergeAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ []))
                        ∷ strmᵗ (deferᵉ (varᵉ (here refl))) ∷ [])))

schedI : Sched Γ₀
schedI = sched-init progI slots₀

stI : EvalSt progI
stI = st-init progI

-- LOAD-BEARING, and tight: 1 against 1, with the μ unfolding for as
-- long as twenty units of gas last
_ : hopDᵉ 4 (slotHop 4 slots₀) progI ≡ 1
_ = refl

_ : depthE (gN 20) progI root 0 0 schedI stI ≡ 1
_ = refl

_ : (depthE (gN 20) progI root 0 0 schedI stI
       ≤ᵇ hopDᵉ 4 (slotHop 4 slots₀) progI + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

-- a `takeᵉ` over the deepest program: the count is a term, evaluated
-- once at subscription, so it adds no layer and the bound is progA's —
-- LOAD-BEARING, and tight: 4 against 4
progJ : Closed Γ₀ natᵗ
progJ = takeᵉ (nat̂ 2) progA

schedJ : Sched Γ₀
schedJ = sched-init progJ slots₀

stJ : EvalSt progJ
stJ = st-init progJ

_ : depthE (gN 20) progJ root 0 0 schedJ stJ ≡ 4
_ = refl

_ : (depthE (gN 20) progJ root 0 0 schedJ stJ
       ≤ᵇ hopDᵉ 4 (slotHop 4 slots₀) progJ + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

------------------------------------------------------------------
-- § 10  THE OTHER THREE `*All` OPERATORS.  `hopDᵉ` charges all four
-- the same `suc`, which is the obvious thing to distrust: `switchAllᵉ`
-- CANCELS a live inner when the next arrives and `exhaustAllᵉ` DROPS
-- one, so their evaluators do work `mergeAllᵉ`'s does not, and every
-- row above this section is a merge.  A uniform clause over four
-- operators with three of them uninstantiated is exactly the coverage
-- claim that reads as wider than it is.
--
-- The nesting is § 1's, so the comparison is against a KNOWN answer:
-- the merge version has depth 4 and bound 4.  ALL THREE COME OUT AT 4
-- AS WELL — every row here is LOAD-BEARING and tight, and the uniform
-- clause is uniform for a reason: cancelling and dropping change WHICH
-- inners are live, never how many layers deep a live one sits.
------------------------------------------------------------------

progK progL progM : Closed Γ₀ natᵗ
progK = concatAllᵉ  (concatAllᵉ  (mapᵉ fA (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])) ∷ []))))
progL = switchAllᵉ  (switchAllᵉ  (mapᵉ fA (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])) ∷ []))))
progM = exhaustAllᵉ (exhaustAllᵉ (mapᵉ fA (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])) ∷ []))))

_ : depthE (gN 20) progK root 0 0 (sched-init progK slots₀) (st-init progK) ≡ 4
_ = refl

_ : depthE (gN 20) progL root 0 0 (sched-init progL slots₀) (st-init progL) ≡ 4
_ = refl

_ : depthE (gN 20) progM root 0 0 (sched-init progM slots₀) (st-init progM) ≡ 4
_ = refl

_ : (depthE (gN 20) progK root 0 0 (sched-init progK slots₀) (st-init progK)
       ≤ᵇ hopDᵉ 4 (slotHop 4 slots₀) progK + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

_ : (depthE (gN 20) progL root 0 0 (sched-init progL slots₀) (st-init progL)
       ≤ᵇ hopDᵉ 4 (slotHop 4 slots₀) progL + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

_ : (depthE (gN 20) progM root 0 0 (sched-init progM slots₀) (st-init progM)
       ≤ᵇ hopDᵉ 4 (slotHop 4 slots₀) progM + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

------------------------------------------------------------------
-- § 11  A MID-RUN STATE, REACHED BY RUNNING — the one region § 5–§ 10
-- leave open, and the one the postulate's own header names as what is
-- left of its risk.  Every row above starts from `st-init`, where the
-- node store is empty; these start from the state the ROOT SUBSCRIBE
-- returns, so the registry, the node table and the delivered set are
-- all populated by the evaluator rather than by hand.
--
-- ⚠ THE STATE IS PROJECTED OUT OF `subscribeE`, NOT WRITTEN DOWN.
-- That is the whole point: a `record (st-init e) { … }` is not a state
-- the evaluator can reach, and a row over one says nothing.  The gas
-- is a concrete numeral rather than `budgetAt`, whose value is a tower
-- and would not normalise as a unary `Gas` — gas only bounds the
-- recursion, so a run that completes under 20 is the real run.
------------------------------------------------------------------

runA : Stream Γ₀ natᵗ × Sched Γ₀ × EvalSt progA
runA = subscribeE (gN 20) progA root 0 0 schedA stA

schedA′ : Sched Γ₀
schedA′ = proj₁ (proj₂ runA)

stA′ : EvalSt progA
stA′ = proj₂ (proj₂ runA)

-- LOAD-BEARING, and tight: 4 against 4 — the same answer as from
-- `st-init`, which is the finding, not a coincidence
_ : depthE (gN 20) progA root 0 1 schedA′ stA′ ≡ 4
_ = refl

_ : (depthE (gN 20) progA root 0 1 schedA′ stA′
       ≤ᵇ hopDᵉ 4 (slotHop 4 (Sched.slots schedA′)) progA
           + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

-- ⚠ AND THE GADGET'S MID-RUN STATE DOES NOT NORMALISE — a BOUNDARY,
-- recorded so nobody pays for it twice.  `subscribeE (gN 200) progC`
-- projected into `depthE` reached 7.9 GB of resident memory in six
-- minutes and was killed; progC runs six ticks with a chain registered
-- per tick, and the state term it returns is shared across both sides
-- of the comparison rather than being reduced away.  So the mid-run
-- coverage here is progA's store and nothing deeper.  The lever, if it
-- is ever wanted, is the compiled harness (`make harness`), which runs
-- real bodies and would report a number — `measured-not-rechecked`,
-- and so useless for THIS purpose, which is a `refl`.

------------------------------------------------------------------
-- § 12  THE REGION THE SIZE CONDITION OPENS — `syncSizeᵉ b ≤ V` where
-- `sizeᵉ b ≤ V` once stood.  The two measures part company at exactly
-- one constructor: `sizeᵉ (deferᵉ e) = suc (sizeᵉ e)` while `syncSizeᵉ
-- (deferᵉ e) = 1`.  So the whole region the weaker hypothesis admits is
-- programs with a large `deferᵉ` body, and this section is that region
-- at the smallest `V` each program admits — which is the sharp
-- direction, since `V` also drives the bound.
--
-- WHY IT IS WORTH INSTANTIATING RATHER THAN ARGUING.  `depthE` and
-- `hopDᵉ` both charge a defer body ZERO, so the condition looks safe
-- from the clause list alone; what the clause list does not settle is
-- that the burst arm re-subscribes an EMITTED inner at full `sizeᵛ`,
-- and an emitted inner can be a defer whose body the store still has
-- to serve.  Rows, not reasoning.
--
-- ⚠ AND THE THIRD CONDITION IS TRIVIAL HERE — every program below runs
-- over `slots₀`, the empty store, so `slotsSize ≤ V` costs nothing and
-- these rows say nothing about it.  The slot side is
-- `Refuted.Depth-Hop`'s, and it is a refutation rather than a receipt.
------------------------------------------------------------------

-- twenty literals: `sizeᵉ` and `syncSizeᵉ` agree on this one, so all of
-- the divergence below comes from the `deferᵉ` wrapping it
lits20 : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} → Exp Γ Δᵍ Δ Θ natᵗ
lits20 = ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ nat̂ 5 ∷ nat̂ 6
            ∷ nat̂ 7 ∷ nat̂ 8 ∷ nat̂ 9 ∷ nat̂ 10 ∷ nat̂ 11 ∷ nat̂ 12 ∷ nat̂ 13
            ∷ nat̂ 14 ∷ nat̂ 15 ∷ nat̂ 16 ∷ nat̂ 17 ∷ nat̂ 18 ∷ nat̂ 19 ∷ [])

-- § 8's `deferᵉ progA` AT THE FLOOR OF `V`.  The size condition put this
-- program out of reach at any `V` below its size; the sync one admits
-- it at `V = 2`, where the bound is 0 and the body's own depth is 4.
-- LOAD-BEARING at its sharpest: a bound of 0 fails on any charge at all
_ : syncSizeᵉ progG ≡ 1
_ = refl

_ : (sizeᵉ progG ≤ᵇ 2) ≡ false
_ = refl

_ : hopDᵉ 2 (slotHop 2 slots₀) progG ≡ 0
_ = refl

_ : (depthE (gN 20) progG root 0 0 schedG stG
       ≤ᵇ hopDᵉ 2 (slotHop 2 slots₀) progG + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

-- and § 8's defer INSIDE a subscribing layer, so the frame that would
-- pay for the body is a `*All` rather than the root.  LOAD-BEARING, and
-- tight: 1 against 1, at a `V` the old condition excluded
_ : syncSizeᵉ progH ≡ 5
_ = refl

_ : (sizeᵉ progH ≤ᵇ 5) ≡ false
_ = refl

_ : hopDᵉ 5 (slotHop 5 slots₀) progH ≡ 1
_ = refl

_ : (depthE (gN 20) progH root 0 0 schedH stH
       ≤ᵇ hopDᵉ 5 (slotHop 5 slots₀) progH + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

-- THE `μᵉ` RE-ENTRY, which is the clause the condition exists for: the
-- guarded body carries the twenty literals behind a defer, so
-- `syncSizeᵉ` is 8 and `sizeᵉ` is not.
bodyR : Exp Γ₀ (natᵗ ∷ []) [] [] natᵗ
bodyR = mergeAllᵉ (ofᵉ (strmᵗ (deferᵉ lits20)
                     ∷ strmᵗ (deferᵉ (varᵉ (here refl))) ∷ []))

progR : Closed Γ₀ natᵗ
progR = μᵉ bodyR

schedR : Sched Γ₀
schedR = sched-init progR slots₀

stR : EvalSt progR
stR = st-init progR

_ : syncSizeᵉ progR ≡ 8
_ = refl

-- THE ROW THE WHOLE CONDITION TURNS ON: one unfolding puts `sizeᵉ` out
-- of reach of the `V` the subject was admitted at, so the old condition
-- is not merely unbounded in the abstract — it is destroyed at a
-- concrete program, in the step `depthE` takes at `gs`
_ : (sizeᵉ (unfoldμ bodyR) ≤ᵇ 8) ≡ false
_ = refl

-- LOAD-BEARING, and tight: 1 against 1, with the μ unfolding for as
-- long as twenty units of gas last and the bound not growing with it
_ : hopDᵉ 8 (slotHop 8 slots₀) progR ≡ 1
_ = refl

_ : depthE (gN 20) progR root 0 0 schedR stR ≡ 1
_ = refl

_ : (depthE (gN 20) progR root 0 0 schedR stR
       ≤ᵇ hopDᵉ 8 (slotHop 8 slots₀) progR + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl
