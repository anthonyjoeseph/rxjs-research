-- THE DEPTH MIRROR IS NOT TRUE FOR EVERY REFOLD BOUND.
--
-- `depth-hop` (Depth-Compositional) bounds `depthE` by
-- `hopDᵉ V (slotHop V (Sched.slots sched)) b + pathNestD κ`.  Stated
-- with `V` universally quantified it is FALSE, and the reason is
-- structural rather than incidental: `hopDᵉ`'s scan clause is
-- `(2 + pmᵗ V 0 f) ^ V * (…)`, an EXPONENTIAL IN `V`, so at `V = 0` the
-- factor is 1 and a scan is charged its step, seed and source and
-- nothing for refolding at all.  A program whose depth comes from
-- refolding then outruns the bound.
--
-- WHICH IS WHY THE STATEMENT CARRIES `2 ≤ V` AND `sizeᵉ b ≤ V`.  That
-- is a RESTATEMENT and this file is its justification: the
-- unconditional form is refuted, so the conditioned form replaces a
-- false statement rather than weakening a true one.
--
-- ⚠ WHAT THIS FILE PINS IS THAT *SOME* CONDITION ON `V` IS NEEDED, NOT
-- THAT THESE TWO ARE THE WEAKEST ONES.  It kills `V = 0` and says
-- nothing against `V = 1`, which was MEASURED to hold on this same
-- program (the green row is in `Probed.Depth-Hop`, and it holds there
-- with no margin at all).  So do not read the pair as tight: it is the
-- shape every other hop consumer in this tree already uses —
-- `thruOuter-face-core-go` takes `2 ≤ C` with `sizeᵉ o ≤ C`, and
-- `subscribeE-wet-via-caps` reads `hopDᵉ Ŝ (slotHop Ŝ sl) b` at
-- `Ŝ = sizeCapAt e sl (suc id)`, where `2≤sizeCapAt` and
-- `size≤sizeCapAt` are both proven.
--
-- THE WITNESS IS THE CHEAPEST ONE IN THE FAMILY, and it is cheap for a
-- reason worth stating: its widening lives in a LITERAL LIST, which
-- `hopDᵉ` charges 0 for at every `V` (`hopDᵗ (nat̂ _) = 0`).  So
-- widening the map's source from three literals to seven leaves the hop
-- depth EXACTLY WHERE IT WAS while doubling `depthE` to 8.  Only the
-- refold factor `(2 + pmᵗ V 0 f) ^ V` can pay for that program, and at
-- `V = 0` that factor is 1 — the scan is charged its step, its seed and
-- its source, and nothing for refolding.  Twenty units of gas and a
-- program of constant size settle it; no quadratic gadget is needed.
module Refuted.Depth-Hop where

open import Data.Empty using (⊥)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Unit using (tt)
open import Data.Fin using (zero; suc)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n; _≤ᵇ_)

open import Rx.Prim using (Gas; g0; gs; Id; Tick)
open import Rx.Exp using (Ctx; Closed; Tm; Fn; natᵗ; obs; _×ᵗ_; nat̂; strmᵗ; varᵗ;
  ofᵉ; emptyᵉ; mapᵉ; scanᵉ; mergeAllᵉ; fstᵗ; input; sizeᵉ)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; sched-init; st-init)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Decide using (≤ᵇ-true)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)
open import Verify-Budget-Sufficient.Depth-Compositional using (pathNestD)

gN : ℕ → Gas
gN zero    = g0
gN (suc n) = gs (gN n)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

slots₀ : Slots Γ₀
slots₀ ()

gA : Fn Γ₀ [] [] (obs natᵗ ∷ []) (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
gA = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

fA : Fn Γ₀ [] [] [] (obs natᵗ) (obs (obs natᵗ))
fA = strmᵗ (scanᵉ gA (strmᵗ emptyᵉ) (mergeAllᵉ (ofᵉ (varᵗ (here refl) ∷ []))))

progB : Closed Γ₀ natᵗ
progB = mergeAllᵉ (mergeAllᵉ (mapᵉ fA
          (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ nat̂ 5 ∷ nat̂ 6 ∷ [])) ∷ []))))

schedB : Sched Γ₀
schedB = sched-init progB slots₀

stB : EvalSt progB
stB = st-init progB

theDepth : depthE (gN 20) progB root 0 0 schedB stB ≡ 8
theDepth = refl

-- THE ROW, stated as a DIRECTION rather than a pair of values: the
-- refutation needs only that the comparison comes out `false`, so it
-- does not have to be re-read every time either side's arithmetic
-- moves.
theRow : (depthE (gN 20) progB root 0 0 schedB stB
           ≤ᵇ hopDᵉ 0 (slotHop 0 slots₀) progB
               + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
         ≡ false
theRow = refl

-- and the statement itself, taken as a hypothesis, so this file says
-- the STATEMENT is false rather than reporting on whatever `src`
-- currently proves it through
depth-hop-∀V-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
     (V : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (bid : Id) (now : Tick)
     (sched : Sched Γ) (st : EvalSt e) →
     depthE g b κ bid now sched st
       ≤ hopDᵉ V (slotHop V (Sched.slots sched)) b + pathNestD κ) → ⊥
depth-hop-∀V-absurd h =
  bad (trans (sym (≤ᵇ-true _ _ (h 0 (gN 20) progB root 0 0 schedB stB))) theRow)
  where
  bad : true ≡ false → ⊥
  bad ()

------------------------------------------------------------------
-- AND THE CONDITIONED FORM IS FALSE TOO — THE SLOT DESCENT.
--
-- `2 ≤ V` and `sizeᵉ b ≤ V` are inherited at every STRUCTURAL descent,
-- because `b` shrinks there and `V` does not move.  The `input` clause
-- is not a structural descent: `depthE` reads the slot and recurses
-- into the shared DEF, and the subject's own `sizeᵉ (input i) ≡ 1`
-- says nothing whatever about that def's size.  So `V` can be pinned
-- at its floor of 2 while the def is arbitrarily large, and the def
-- then outruns the bound its own slot reports.
--
-- WHICH MAKES THE WITNESS THE SAME PROGRAM AS ABOVE, MOVED INTO A
-- SLOT.  The refold factor `(2 + pmᵗ V 0 f) ^ V` is the only term that
-- can pay for a payload-count-driven depth, and at a FIXED `V` it is a
-- constant while `depthE` grows one per literal — literals being
-- exactly what `hopDᵉ` charges nothing for.  The two figures below say
-- it in one line: widening the source from 7 literals to 20 takes the
-- depth 8 → 21 and leaves the bound at 20 in both.
--
-- SO THE REPAIR IS THE SLOT HYPOTHESIS THE MIRROR ALREADY CARRIES.
-- `subscribeE-caps` (.Subscribe-Face) takes `slotsSize sl ≤
-- Caps.cSize c` beside its size condition, and `slotDef-size`
-- (.Measures) turns it into `sizeᵉ d ≤ V` at exactly this clause.  It
-- is a RESTATEMENT and this section is its justification: the form
-- with two conditions is false, so the form with three replaces a
-- false statement rather than weakening a true one.  The consumer pays
-- nothing new — `capsBase e sl` is `2 + sizeᵉ e + slotsSize sl`, which
-- is where `size≤sizeCapAt` already comes from.
--
-- ⚠ AND WHAT THIS DOES NOT SAY is that three conditions SUFFICE.  It
-- reaches one clause: the slot descent.  The `μᵉ` re-entry breaks the
-- size condition a second way — `size-unfoldμ` (.Keeps-Ring) bounds an
-- unfold only by `sizeᵉ (μᵉ body) * sizeᵉ (μᵉ body)`, so a fixed `V`
-- cannot survive repeated unfolding either — and that one is a route
-- failure rather than a falsity, since `hopD-unfoldμ` holds the bound
-- itself fixed across an unfold.  No witness here bears on it.
------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

-- the widening lives in a literal list, which `hopDᵉ` charges 0 for at
-- every `V` (`hopDᵗ (nat̂ _) = 0`), and which `depthE` charges one
-- nesting level per element because the scan re-wraps its accumulator
litsUpto : ℕ → List (Tm Γ₁ [] [] [] natᵗ)
litsUpto zero    = []
litsUpto (suc k) = nat̂ k ∷ litsUpto k

gS : Fn Γ₁ [] [] (obs natᵗ ∷ []) (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
gS = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

fS : Fn Γ₁ [] [] [] (obs natᵗ) (obs (obs natᵗ))
fS = strmᵗ (scanᵉ gS (strmᵗ emptyᵉ) (mergeAllᵉ (ofᵉ (varᵗ (here refl) ∷ []))))

progS : Closed Γ₁ natᵗ
progS = mergeAllᵉ (mergeAllᵉ (mapᵉ fS
          (ofᵉ (strmᵗ (ofᵉ (litsUpto 20)) ∷ []))))

-- the def sits in slot 0, where stratification forbids inputs anyway,
-- so `inputsBelowᵉ 0 progS` holds by having no `input` in it at all
slots₁ : Slots Γ₁
slots₁ zero    = shared progS {ok = tt}
slots₁ (suc ())

-- and the SUBJECT is the input, whose own size is 1
subjS : Closed Γ₁ natᵗ
subjS = input zero

schedS : Sched Γ₁
schedS = sched-init subjS slots₁

stS : EvalSt subjS
stS = st-init subjS

-- the three figures, pinned, so that a repair moving either side fails
-- here by NAMING THE NUMBER rather than by quietly closing the gap
slotSubjSize : sizeᵉ subjS ≡ 1
slotSubjSize = refl

slotBound : hopDᵉ 2 (slotHop 2 slots₁) subjS
              + pathNestD (root {Γ = Γ₁} {t = natᵗ}) ≡ 20
slotBound = refl

slotDepth : depthE (gN 30) subjS root 0 0 schedS stS ≡ 21
slotDepth = refl

slotRow : (depthE (gN 30) subjS root 0 0 schedS stS
            ≤ᵇ hopDᵉ 2 (slotHop 2 slots₁) subjS
                + pathNestD (root {Γ = Γ₁} {t = natᵗ}))
          ≡ false
slotRow = refl

depth-hop-slot-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
     (V : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (bid : Id) (now : Tick)
     (sched : Sched Γ) (st : EvalSt e) →
     2 ≤ V → sizeᵉ b ≤ V →
     depthE g b κ bid now sched st
       ≤ hopDᵉ V (slotHop V (Sched.slots sched)) b + pathNestD κ) → ⊥
depth-hop-slot-absurd h =
  bad (trans (sym (≤ᵇ-true _ _
                    (h 2 (gN 30) subjS root 0 0 schedS stS
                       (s≤s (s≤s z≤n)) (s≤s z≤n))))
             slotRow)
  where
  bad : true ≡ false → ⊥
  bad ()
