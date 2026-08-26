-- THE MULTI-LEVEL DESCENT, which every receipt on the `*All` heads
-- names as the region nothing had reached: deep observable values
-- crossing a genuine `*All` boundary per level, DOUBLED by a
-- payload-duplicating step function between crossings, so the
-- delivered nesting grows exponentially in the level count while the
-- program's own spine grows linearly.  Every earlier row at these
-- heads moved the depth axis alone, and delivered nesting there was
-- exactly `k` -- the compounding this family exists to reach was
-- structurally absent.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: subscribeE-nest-merge
-- TARGET: subscribeE-nest-switch
-- TARGET: subscribeE-nest-exhaust
--
-- THE FAMILY.  `dup` names its observable payload twice at the one
-- additive slot the measure has, so one application doubles the
-- value's nesting reading without moving its type; a level wraps the previous program in a `mergeAllᵉ` (a real
-- boundary the deep values must cross) and then applies `dup` to what
-- comes through.  The head under test wraps the whole stack once more,
-- so each row instantiates a `*All` head whose descent contains `k`
-- further boundaries with substitution between them.
--
-- LOAD-BEARING, and on the axis that can refute: the delivered figures
-- below DOUBLE per level while the grant's exponent grows linearly in
-- the spine, so the two sides genuinely race -- a family whose
-- delivered nesting outran `(2^S)^m` at any level would cross, and the
-- rows would have caught it.  W is read at ZERO exactly as
-- `Probed.Subscribe-Nest-Wrap` reads it, and for the same reason: the
-- rows clear a SMALLER grant than any the width premise would permit,
-- and `nestB` only rises with `W`.
--
-- NOT COVERED: the store halves move here only through the descent's
-- transient nodes (the final tables are small and pinned), so the
-- drain-under-a-queue region stays with `Probed.Wrap-Nest-Frame`; and
-- no row reaches a `switch`/`exhaust` boundary DEEP in the stack --
-- the inner levels are all `mergeAllᵉ`, the outermost head is where
-- the three operators vary.
module Probed.Nest-Multi-Level where

open import Data.Bool using (Bool; true)
open import Data.List using ([]; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; switchAllᵉ;
         exhaustAllᵉ; nat̂; strmᵗ; varᵗ; caseᵗ; inlᵗ; syncSizeᵛ; syncSizeᵉ)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Evaluator
  using (subscribeE; splitBurst; root; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nodesMax; nestDᵛˢ; nestCapsOK?)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

-- the duplicating step: the payload lands once in the map's own step
-- function (through a case SCRUTINEE, the one additive slot a `Tm`
-- has) and once in the source it maps over, and the measure charges a
-- map's two halves by SUM -- so one application doubles the value's
-- nesting without moving its type
dup : Fn Γ₂ [] [] [] (obs natᵗ) (obs natᵗ)
dup = strmᵗ (mapᵉ
        (caseᵗ (inlᵗ (varᵗ (there (here refl)))) (nat̂ 0) (varᵗ (here refl)))
        (ofᵉ (varᵗ (here refl) ∷ [])))

-- a seed the doubling has something to double
v0 : Val Γ₂ (obs natᵗ)
v0 = mergeAllᵉ nothing (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))

-- k levels: cross a fresh `mergeAllᵉ` boundary, then double
D : ℕ → Closed Γ₂ (obs natᵗ)
D zero    = ofᵉ (strmᵗ v0 ∷ [])
D (suc k) = mapᵉ dup (mergeAllᵉ nothing (ofᵉ (strmᵗ (D k) ∷ [])))

pM pS pX : ℕ → Closed Γ₂ (obs natᵗ)
pM k = mergeAllᵉ nothing (ofᵉ (strmᵗ (D k) ∷ []))
pS k = switchAllᵉ (ofᵉ (strmᵗ (D k) ∷ []))
pX k = exhaustAllᵉ (ofᵉ (strmᵗ (D k) ∷ []))

tight : ∀ {u} → Val Γ₂ u → Caps
tight {u} v = caps (syncSizeᵛ u v) (pWᵛ 2 slots u v) 0

lhs : ∀ {t} (e : Closed Γ₂ t) → ℕ
lhs {t} e =
  let r = subscribeE gasBig e root 0 0 (sched-init e slots) (st-init e)
  in nodesMax (proj₂ (proj₂ r))
       ⊔ nestDᵛˢ (proj₁ (splitBurst {A = Val Γ₂ t} (proj₁ r)))

-- the grant at `W = 0`, `nestB` written out because it is sealed
rhs : ∀ {t} (e : Closed Γ₂ t) → ℕ
rhs {t} e =
  let S = Caps.cSize (tight {obs t} e)
      m = syncSizeᵉ e
  in (2 ^ S) ^ m * (nestDᵉ e + suc m * nestUnit e slots)

-- the premise the statement actually names, pinned where the rows run
nestPrems : Bool × Bool × Bool
nestPrems = nestCapsOK? (tight {obs (obs natᵗ)} (pM 3)) (sched-init (pM 3) slots) (st-init (pM 3))
          , nestCapsOK? (tight {obs (obs natᵗ)} (pS 2)) (sched-init (pS 2) slots) (st-init (pS 2))
          , nestCapsOK? (tight {obs (obs natᵗ)} (pX 2)) (sched-init (pX 2) slots) (st-init (pX 2))

nestPrems≡ : nestPrems ≡ (true , true , true)
nestPrems≡ = refl

valPrems : Bool × Bool × Bool
valPrems = nestValOK? (tight {obs (obs natᵗ)} (pM 3)) (obs (obs natᵗ)) (pM 3)
         , nestValOK? (tight {obs (obs natᵗ)} (pS 2)) (obs (obs natᵗ)) (pS 2)
         , nestValOK? (tight {obs (obs natᵗ)} (pX 2)) (obs (obs natᵗ)) (pX 2)

valPrems≡ : valPrems ≡ (true , true , true)
valPrems≡ = refl

-- THE COMPOUNDING, measured: delivered nesting per level, doubling --
-- the first rows at these heads whose delivered figure is not linear
burstAt : ∀ {t} (e : Closed Γ₂ t) → ℕ
burstAt {t} e =
  length (proj₁ (splitBurst {A = Val Γ₂ t}
    (proj₁ (subscribeE gasBig e root 0 0 (sched-init e slots) (st-init e)))))

-- NON-VACUITY: a delivered figure over an empty burst measures nothing
lens : ℕ × ℕ × ℕ × ℕ
lens = burstAt (pM 0) , burstAt (pM 1) , burstAt (pM 2) , burstAt (pM 3)

lens≡ : lens ≡ (1 , 1 , 1 , 1)
lens≡ = refl

delivered : ℕ × ℕ × ℕ × ℕ
delivered = lhs (pM 0) , lhs (pM 1) , lhs (pM 2) , lhs (pM 3)

delivered≡ : delivered ≡ (1 , 2 , 4 , 8)
delivered≡ = refl

-- the race: the head's own grant, at every level the family reaches
fitsM0 : (lhs (pM 0) ≤ᵇ rhs (pM 0)) ≡ true
fitsM0 = refl

fitsM1 : (lhs (pM 1) ≤ᵇ rhs (pM 1)) ≡ true
fitsM1 = refl

fitsM2 : (lhs (pM 2) ≤ᵇ rhs (pM 2)) ≡ true
fitsM2 = refl

fitsM3 : (lhs (pM 3) ≤ᵇ rhs (pM 3)) ≡ true
fitsM3 = refl

fitsS2 : (lhs (pS 2) ≤ᵇ rhs (pS 2)) ≡ true
fitsS2 = refl

fitsX2 : (lhs (pX 2) ≤ᵇ rhs (pX 2)) ≡ true
fitsX2 = refl
