-- THE RANK THE MACHINE ENTERS AT NOW MOVES WITH SOURCE LENGTH, AND IT
-- OUTRUNS THE DEPTH THE CASCADE REACHES.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHY THIS FAMILY.  Every row ever taken against the operator leaf sat
-- at a root the leaf does not answer for, so the region carrying its
-- risk had no coverage at all.  A row there needs a FLATTENING root —
-- that is what `opShape` admits — and it is worth having only if the
-- program underneath it grows the one quantity the rank is denominated
-- in.  The family below is built to do exactly that and nothing else.
--
-- HOW A RUN DEEPENS WHAT IT SUBSCRIBES.  Two folds, and each does one
-- job.  The inner one re-wraps its accumulator THREE times per source
-- value, so flattening its output delivers a tree: one literal buys
-- three deliveries, two buy twelve, and the count triples with the
-- source.  The outer one wraps its own accumulator ONCE per delivery it
-- sees, which turns that count into a DEPTH — so the values the family
-- hands out read as deep as the inner fold delivers wide, and the root
-- flattener subscribes every one of them.
--
-- BOTH RATES MOVE, AND THE READING'S IS THE FASTER — WHICH IS THE
-- FINDING.  Four programs differing in literals alone give an entry
-- reading of 5, 21, 85, 329 against a carried depth of 3, 12, 39, 120.
-- The reading dominates at every length and the margin WIDENS with the
-- source, from a factor under two at one literal to nearly three at
-- four.  Every row is load-bearing in both directions: a reading that
-- stalled would say the clause is still blind to what it folds over,
-- and a carried depth overtaking it at any length would refute the
-- entry conjunct outright at the one root shape the leaf answers for.
--
-- IT IS THE SAME FAMILY THAT EXHIBITED THE CROSSING, WHICH IS WHY THE
-- COVERAGE COUNTS.  These four programs used to read a FLAT 532899 —
-- a function of the store bound and the templates, with source length
-- among the inputs of neither — so the two rates met at twelve literals
-- and the conjunct was false beyond it.  The iterating clause takes its
-- refold count off the source's own delivery component, so what was a
-- constant is now the faster of two exponentials: the crossing is not
-- pushed out, it is the wrong way round.

-- THE COVERAGE BOUNDARY, and it is an infrastructure limit rather than
-- a choice.  MEASURING a burst and SUBSCRIBING one cost differently, so
-- the leaf row below sits at the ONE literal root while the rate rows
-- reach four; a leaf row at two literals stalled for eleven minutes
-- with the resident set FLAT, against a whole probe root that checks in
-- seconds.  So what is instantiated is the rate at four lengths and the
-- subscribe at one, and no row here reaches the twelve literals the old
-- crossing sat at.
--
-- WHAT THE LEAF ROW BUYS BESIDE THE RATE: the first coverage this leaf
-- has ever had at a root it answers for.  The run really does reach
-- `subscribeInner`, really does peel the rank, and really does come
-- back without a dry close.
--
-- TARGET: dry-operator @27b615
module Probed.Operator-Root where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; _⊔_)
open import Data.Product using (proj₁)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEvent; value; InstEmit)
open import Rx.Exp using (Ctx; Closed; Fn; Tm; natᵗ; obs; _×ᵗ_;
  ofᵉ; emptyᵉ; scanᵉ; mergeAllᵉ; strmᵗ; nat̂; fstᵗ; varᵗ)
open import Rx.Slots using (Slots)
open import Rx.Hop-Depth using (Rd₃; depthᵉ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Stream; subscribeE; rootWitness; root;
  sched-init; st-init)
open import Verify-Rank-Sufficient.Dry using (dry-operator)
open import Verify-Rank-Sufficient.Entry using (rootTri-reads)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- HOW DEEP THE VALUES A RUN HANDS OUT READ, IN THE RANK'S OWN
-- CURRENCY.  The payloads it reads are exactly the ones the root
-- flattener goes on to subscribe, so a depth here is comparable with
-- the rank rows below rather than merely alongside them — which a
-- reading in NESTING was not, since the two orders disagree at the
-- `deferᵉ` gate.
----------------------------------------------------------------------

evHop : ∀ {n} {Γ : Ctx n} {u} (ψ : Fin n → Rd₃) →
        List (InstEvent (Closed Γ u)) → ℕ
evHop ψ []             = 0
evHop ψ (value v ∷ es) = depthᵉ ψ v ⊔ evHop ψ es
evHop ψ (_ ∷ es)       = evHop ψ es

carried : ∀ {n} {Γ : Ctx n} {u} (ψ : Fin n → Rd₃) →
          Stream Γ (obs u) → ℕ
carried ψ []         = 0
carried ψ (em ∷ ems) = evHop ψ (InstEmit.events em) ⊔ carried ψ ems

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

burstOf : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) → Stream Γ t
burstOf e ins =
  proj₁ (subscribeE (rootWitness e ins) e root 0 0 (sched-init e ins)
           (st-init e))

----------------------------------------------------------------------
-- THE TWO FOLDS.  `spread` re-wraps its accumulator three times, so its
-- output flattens to a tree that triples with the source; `deepen`
-- wraps once per delivery it sees, which is what converts that width
-- into depth.  The inner fold's seed is LIVE — one value — because a
-- tree with nothing at its leaves delivers nothing and so moves neither
-- quantity.
----------------------------------------------------------------------

spread : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
spread = strmᵗ (mergeAllᵉ nothing
                 (ofᵉ (fstᵗ (varᵗ (here refl)) ∷
                       fstᵗ (varᵗ (here refl)) ∷
                       fstᵗ (varᵗ (here refl)) ∷ [])))

deepen : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

liveSeed : Tm Γ₀ [] [] [] (obs natᵗ)
liveSeed = strmᵗ (ofᵉ (nat̂ 0 ∷ []))

emitter : List (Tm Γ₀ [] [] [] natᵗ) → Closed Γ₀ (obs natᵗ)
emitter src = scanᵉ deepen (strmᵗ emptyᵉ)
  (mergeAllᵉ nothing (scanᵉ spread liveSeed (ofᵉ src)))

e1 e2 e3 e4 : Closed Γ₀ (obs natᵗ)
e1 = emitter (nat̂ 0 ∷ [])
e2 = emitter (nat̂ 0 ∷ nat̂ 1 ∷ [])
e3 = emitter (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])
e4 = emitter (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])

----------------------------------------------------------------------
-- THE RANK THE MACHINE ACTUALLY ENTERS AT, AND IT MOVES.  The entry
-- reads `depthᵉ` off the slot telescope; the four programs differ in
-- source length alone and every one reads higher than the last.  Each
-- row is LOAD-BEARING and could have failed in either direction — a
-- reading flat across the four would say the clause is still blind to
-- what it folds over, which is the defect that refuted every earlier
-- form of this conjunct, and one that shrank would say a literal costs
-- the measure something.
----------------------------------------------------------------------

ψ₀ : Fin 0 → Rd₃
ψ₀ = slotRd ins₀

_ : depthᵉ ψ₀ e1 ≡ 5                                   -- LOAD-BEARING
_ = refl

_ : depthᵉ ψ₀ e2 ≡ 21                                  -- LOAD-BEARING
_ = refl

_ : depthᵉ ψ₀ e3 ≡ 85                                  -- LOAD-BEARING
_ = refl

_ : depthᵉ ψ₀ e4 ≡ 329                                 -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE RATE IT HAS TO DOMINATE, row for row against the four above.
-- Each is LOAD-BEARING and each could have failed in either direction:
-- a depth that stalled would say the outer fold does not see the
-- flattened tree, and a depth OVERTAKING its row above would refute the
-- entry conjunct at the one root shape this leaf answers for.  It does
-- neither — three against five, twelve against twenty-one, thirty-nine
-- against eighty-five, a hundred and twenty against three hundred and
-- twenty-nine — so the gap widens rather than closing.
----------------------------------------------------------------------

_ : carried ψ₀ (burstOf e1 ins₀) ≡ 3                   -- LOAD-BEARING
_ = refl

_ : carried ψ₀ (burstOf e2 ins₀) ≡ 12                  -- LOAD-BEARING
_ = refl

_ : carried ψ₀ (burstOf e3 ins₀) ≡ 39                  -- LOAD-BEARING
_ = refl

_ : carried ψ₀ (burstOf e4 ins₀) ≡ 120                 -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE LEAF, AT A ROOT IT ANSWERS FOR.  The flattener subscribes the
-- layers the one-literal row above measures, so the rank really is
-- peeled — and this is the first row the statement has ever had inside
-- the region `opShape` admits.
----------------------------------------------------------------------

flat1 : Closed Γ₀ natᵗ
flat1 = mergeAllᵉ nothing e1

opRoot : Confirms (dry-operator (rootWitness flat1 ins₀) flat1 root 0 0
  (sched-init flat1 ins₀) (st-init flat1) refl
  (rootTri-reads flat1 ins₀))
opRoot = refl
