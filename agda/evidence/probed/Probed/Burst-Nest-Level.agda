-- THE ARRIVALS' CAP AT THE LEVEL, READ AT THE WITNESS THAT KILLED THE
-- FLAT ONE.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: subscribeE-burst-nest @d2c32b
--
-- WHAT IS BEING TESTED.  A step function naming its payload twice
-- returns about twice the payload while contributing a constant to the
-- head it is read against, so the arrival crosses any key stated in the
-- head's own written size.  That crossing is machine-refuted at a flat
-- cap.  The statement as it now reads keys the arrivals at a LEVEL
-- instead -- the entry cap stepped once per unit of its own size -- and
-- the question this file answers is whether the level outruns the
-- substitution at the very program that produced the crossing.
--
-- THE ROWS: the same duplicating map, the same eight-value payload and
-- the same slots the refutation uses, with the payload doubled on a
-- second family so a reading that merely happened to fit is separated
-- from one the level actually covers.  Each row carries the flat key,
-- the levelled key, the largest value the burst emits, and BOTH
-- verdicts -- so a green row is a crossing that has been closed rather
-- than a boolean, and the flat verdict beside it is what says the row
-- could have failed.
--
-- NOT COVERED: the width leaf refuted beside the admissibility one,
-- which reads a second key; a payload large enough to test the level's
-- own growth rate against a substitution deeper than one frame; and
-- every premise about a SEALED cap, since the target is stated over a
-- quantified `Caps` and these rows pick a concrete one.
module Probed.Burst-Nest-Level where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_; foldr)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs; InstEmit)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; nat̂; strmᵗ; varᵗ;
         syncSizeᵛ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (splitEvents; root; sched-init; st-init; subscribeE; mintNode; Stream; _↠_; thru-outer;
  mergeAllᵒ; installNode)
open import Verify-Budget-Sufficient.Caps using (Caps; caps; arrCapAt)
open import Verify-Budget-Sufficient.Caps-Face.Part1
  using (nestValOK?; capsOK?; nestClosOK?)
open import Verify-Budget-Sufficient.Nest-Walk
  using (burstNest?; allWrap; allFresh)
open import Refuted.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))

dupFn : Fn Γ₂ [] [] [] (obs natᵗ) (obs natᵗ)
dupFn = strmᵗ (mergeAllᵉ nothing
                 (ofᵉ (varᵗ (here refl) ∷ varᵗ (here refl) ∷ [])))

payload8 : Val Γ₂ (obs natᵗ)
payload8 = ofᵉ (nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷
                nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ [])

payload16 : Val Γ₂ (obs natᵗ)
payload16 = ofᵉ (nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷
                 nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷
                 nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷
                 nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ [])

bodyOf : Val Γ₂ (obs natᵗ) → Closed Γ₂ (obs natᵗ)
bodyOf v = mapᵉ dupFn (ofᵉ (strmᵗ v ∷ []))

headOf : Val Γ₂ (obs natᵗ) → Closed Γ₂ natᵗ
headOf v = allWrap mergeAllᵒ nothing (bodyOf v)

-- the entry cap is the head's own written size, which is what the size
-- premises ask for and all they ask for; the other two fields are set
-- wide so nothing but the size half can be doing the work
capOf : Val Γ₂ (obs natᵗ) → Caps
capOf v = caps (syncSizeᵛ (obs natᵗ) (headOf v)) 99 99

biggest : Stream Γ₂ (obs natᵗ) → ℕ
biggest [] = 0
biggest (em ∷ ems) =
  foldr (λ o acc → syncSizeᵛ (obs natᵗ) o ⊔ acc) 0
    (proj₁ (splitEvents {A = ℕ} (InstEmit.events em)))
  ⊔ biggest ems

-- one row: the premises the target reads, the flat key the refutation
-- crossed, the levelled key the statement actually uses, the largest
-- emitted value, and the verdict
row : Val Γ₂ (obs natᵗ) →
      (Bool × Bool × Bool) × (ℕ × ℕ × ℕ) × Bool × Bool
row v =
  let hd    = headOf v
      bd    = bodyOf v
      c     = capOf v
      sch₀  = sched-init hd slots
      nid   = proj₁ (mintNode sch₀)
      sch   = proj₂ (mintNode sch₀)
      st    = installNode nid (allFresh natᵗ mergeAllᵒ nothing) (st-init hd)
      res   = subscribeE gasBig bd (thru-outer mergeAllᵒ nid ↠ root) 0 0 sch st
      arrC  = arrCapAt (Caps.cSize c) c
  in ( capsOK? c sch st
     , nestValOK? c (obs (obs natᵗ)) bd
     , nestClosOK? c slots bd )
   , ( Caps.cSize c , Caps.cSize arrC , biggest (proj₁ res) )
   , burstNest? c slots (proj₁ res)
   , burstNest? arrC slots (proj₁ res)

row8 : (Bool × Bool × Bool) × (ℕ × ℕ × ℕ) × Bool × Bool
row8 = row payload8

row16 : (Bool × Bool × Bool) × (ℕ × ℕ × ℕ) × Bool × Bool
row16 = row payload16

row8≡ : row8 ≡ ((true , true , true) , (21 , 263584474897314644261250991132258803 , 25) , false , true)
row8≡ = refl

row16≡ : row16 ≡ ((true , true , true) , (29 , 40678314445607703830446247298919538279736746158459131 , 41) , false , true)
row16≡ = refl
