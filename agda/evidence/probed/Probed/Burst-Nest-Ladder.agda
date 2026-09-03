-- THE LEVEL THE ARRIVALS ACTUALLY NEED, AT A SUBSTITUTION DEEPER THAN
-- ONE FRAME.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: subscribeE-burst-nestL @2bcf96
--
-- WHAT IS BEING TESTED, AND IT IS A DENOMINATION AND NOT A BOOLEAN.
-- This statement answers at the cap it was asked at stepped that cap's
-- own SIZE many times, which is what refuses every attempt to enter it
-- one level up.  The repair on the table is the discipline the caps
-- face beside it is proven in: report an INCREMENT and let the carried
-- ceiling convert it.  That is worth nothing if the increment the
-- arrivals actually need grows with the term, so the rows measure it
-- directly -- the LEAST level at which the burst is admitted -- along
-- the one axis the sibling probe names as uncovered.
--
-- THE LADDER IS THAT AXIS.  The same duplicating map, with each rung's
-- whole merged head substituted in as the next rung's payload, so the
-- depth moves and the payload does not.  A rung raises both the entry
-- size and the largest emitted value by better than half again, so a
-- needed level that does not move with depth is a reading about the
-- RATE and not an artifact of a cap that happened to be roomy.
--
-- EVERY ROW IS LOAD-BEARING, and the control is what makes the rest of
-- them so: at every depth the largest emitted value is strictly over
-- the entry size, so the entry cap genuinely refuses the burst, and
-- the control -- the same shape with a step function naming its
-- payload ONCE, which substitutes without growing -- is admitted at
-- the entry cap and returns ZERO.  So the search can return zero, and
-- a one is a level that was needed.
--
-- NOT COVERED: any head but `mergeAllᵒ`; the SWEEP the increment must
-- fit inside, and the ceiling that converts it, both of which are
-- sealed and so cannot be instantiated at any input -- these rows
-- reach the increment and stop where the arithmetic that must pay for
-- it begins; and every premise about a cap this face quantifies over,
-- since the rows pick concrete ones.
module Probed.Burst-Nest-Ladder where

open import Data.Bool using (Bool; true; if_then_else_)
open import Data.List using ([]; _∷_; foldr)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _⊔_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤ᵇ⇒≤)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs; InstEmit)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; nat̂; strmᵗ; varᵗ;
         syncSizeᵛ; sizeᵉ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (splitEvents; root; sched-init; st-init; subscribeE; mintNode; Stream;
         _↠_; thru-outer; mergeAllᵒ; installNode; NodeId; Sched; EvalSt; Path)
open import Verify-Budget-Sufficient.Caps using (Caps; caps; frameStep)
open import Verify-Budget-Sufficient.Caps-Face.Part1
  using (nestValOK?; capsOK?; nestClosOK?)
open import Verify-Budget-Sufficient.Nest-Store using (allFresh)
open import Verify-Budget-Sufficient.Nest-Walk
  using (burstNest?; allWrap; FaceOK; faceOK; subscribeE-burst-nestL)
open import Verify-Budget-Sufficient.Nest-Burst using (descW)
open import Probed.Apparatus using (Confirms)
open import Refuted.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))

dupFn : Fn Γ₂ [] [] [] (obs natᵗ) (obs natᵗ)
dupFn = strmᵗ (mergeAllᵉ nothing
                 (ofᵉ (varᵗ (here refl) ∷ varᵗ (here refl) ∷ [])))

payload : Val Γ₂ (obs natᵗ)
payload = ofᵉ (nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ [])

bodyOf : Val Γ₂ (obs natᵗ) → Closed Γ₂ (obs natᵗ)
bodyOf v = mapᵉ dupFn (ofᵉ (strmᵗ v ∷ []))

headOf : Val Γ₂ (obs natᵗ) → Closed Γ₂ natᵗ
headOf v = allWrap mergeAllᵒ nothing (bodyOf v)

-- THE LADDER: each rung substitutes the rung below it, whole, as the
-- payload of the next duplicating map, so `rung k` is a substitution k
-- frames deep and the payload is the same at every depth
rung : ℕ → Val Γ₂ (obs natᵗ)
rung zero    = payload
rung (suc k) = headOf (rung k)

capOf : Val Γ₂ (obs natᵗ) → Caps
capOf v = caps (syncSizeᵛ (obs natᵗ) (headOf v)) 99 99

biggest : Stream Γ₂ (obs natᵗ) → ℕ
biggest [] = 0
biggest (em ∷ ems) =
  foldr (λ o acc → syncSizeᵛ (obs natᵗ) o ⊔ acc) 0
    (proj₁ (splitEvents {A = ℕ} (InstEmit.events em)))
  ⊔ biggest ems

-- the LEAST level at which the burst is admitted, searched upward from
-- the entry cap; the fuel is reported back when nothing under it works,
-- so a row that ran out is visible as the fuel itself
leastL : ℕ → Caps → Stream Γ₂ (obs natᵗ) → ℕ → ℕ
leastL zero    c str acc = acc
leastL (suc f) c str acc =
  if burstNest? (frameStep acc c) slots str then acc
  else leastL f c str (suc acc)

-- one row: the premises the target reads, the entry size, the operator
-- count the sweep is indexed by, the least level the burst needs, and
-- the largest emitted value
LadderRow : Set
LadderRow = (Bool × Bool × Bool) × ℕ × ℕ × ℕ × ℕ

row : ℕ → LadderRow
row k =
  let v     = rung k
      hd    = headOf v
      bd    = bodyOf v
      c     = capOf v
      sch₀  = sched-init hd slots
      nid   = proj₁ (mintNode sch₀)
      sch   = proj₂ (mintNode sch₀)
      st    = installNode nid (allFresh natᵗ mergeAllᵒ nothing) (st-init hd)
      κ     = thru-outer mergeAllᵒ nid ↠ root
      res   = subscribeE gasBig bd κ 0 0 sch st
  in ( capsOK? c sch st
     , nestValOK? c (obs (obs natᵗ)) bd
     , nestClosOK? c slots bd )
   , Caps.cSize c
   , suc (sizeᵉ bd)
   , leastL 8 c (proj₁ res) 0
   , biggest (proj₁ res)

ladder1 : LadderRow
ladder1 = row 1

ladder2 : LadderRow
ladder2 = row 2

ladder3 : LadderRow
ladder3 = row 3

-- THE CONTROL, and it is what says a needed level of one is a reading
-- and not the search's floor: the same shape with a step function that
-- names its payload ONCE substitutes without growing, so the entry cap
-- admits the burst and the search returns zero
oneFn : Fn Γ₂ [] [] [] (obs natᵗ) (obs natᵗ)
oneFn = strmᵗ (mergeAllᵉ nothing (ofᵉ (varᵗ (here refl) ∷ [])))

-- the control's pieces are NAMED rather than let-bound, because the
-- tie at the end of this file instantiates the target at exactly them
-- and a `let` cannot be pointed at from a type
flatBd : Closed Γ₂ (obs natᵗ)
flatBd = mapᵉ oneFn (ofᵉ (strmᵗ payload ∷ []))

flatHd : Closed Γ₂ natᵗ
flatHd = allWrap mergeAllᵒ nothing flatBd

flatC : Caps
flatC = caps (syncSizeᵛ (obs natᵗ) flatHd) 99 99

flatNid : NodeId
flatNid = proj₁ (mintNode (sched-init flatHd slots))

flatSch : Sched Γ₂
flatSch = proj₂ (mintNode (sched-init flatHd slots))

flatSt : EvalSt flatHd
flatSt = installNode flatNid (allFresh natᵗ mergeAllᵒ nothing) (st-init flatHd)

flatκ : Path Γ₂ (obs natᵗ) natᵗ
flatκ = thru-outer mergeAllᵒ flatNid ↠ root

ladderFlat : LadderRow
ladderFlat =
  let res = subscribeE gasBig flatBd flatκ 0 0 flatSch flatSt
  in ( capsOK? flatC flatSch flatSt
     , nestValOK? flatC (obs (obs natᵗ)) flatBd
     , nestClosOK? flatC slots flatBd )
   , Caps.cSize flatC
   , suc (sizeᵉ flatBd)
   , leastL 8 flatC (proj₁ res) 0
   , biggest (proj₁ res)

ladder1≡ : ladder1 ≡ ((true , true , true) , 28 , 28 , 1 , 39)
ladder1≡ = refl

ladder2≡ : ladder2 ≡ ((true , true , true) , 39 , 39 , 1 , 61)
ladder2≡ = refl

ladder3≡ : ladder3 ≡ ((true , true , true) , 50 , 50 , 1 , 83)
ladder3≡ = refl

ladderFlat≡ : ladderFlat ≡ ((true , true , true) , 16 , 16 , 0 , 10)
ladderFlat≡ = refl

----------------------------------------------------------------------
-- AND THE TIE TO THE STATEMENT, AT THE CONTROL AND ONLY THERE.  Every
-- row above is a READING — `leastL`, a search this file wrote, run
-- over a stream the evaluator produced — and nothing in it is held to
-- `subscribeE-burst-nestL` as it reads.  The row below is: Agda
-- generates its type from the statement, so this file supplies only
-- the point and the witness, and a restatement of the target breaks
-- here rather than leaving a green search about text that is gone.
--
-- WHY THE CONTROL IS THE ONLY POINT, and this is the finding rather
-- than a shortfall of effort.  The target's first conjunct is
-- denominated in `opIterD`, which this tower SEALS for cost, so it
-- reduces at no input whatever.  At the control the needed increment
-- is ZERO — the row above measures exactly that — and the conjunct
-- becomes `0 ≤ _`, which holds without reading the sealed family at
-- all.  At every RUNG the increment is one, and `1 ≤ opIterD …` is a
-- fact about the sealed arithmetic and cannot be written here.  So the
-- ladder's whole reading — that the needed level does not grow with
-- depth — stays a reading, and what is tied is the boundary case it is
-- measured against.
--
-- THE ROW IS LOAD-BEARING ON ITS SECOND CONJUNCT AND DEGENERATE ON ITS
-- FIRST.  `z≤n` could not have failed; `refl` could, and does at every
-- rung above, which is the whole content of `leastL` returning one
-- there.  The premises are discharged at the tightest value each
-- admits: the slots equation at the schedule's own slots, the width
-- premise at the descent's own `descW`.
----------------------------------------------------------------------

flatFace : FaceOK flatC slots
flatFace = faceOK (≤ᵇ⇒≤ _ _ tt) (≤ᵇ⇒≤ _ _ tt) refl (≤ᵇ⇒≤ _ _ tt)

flatRow : Confirms
  (subscribeE-burst-nestL flatC 0 slots
     (descW gasBig flatBd flatκ 0 0 flatSch flatSt)
     gasBig flatBd flatκ 0 0 flatSch flatSt ⦃ flatFace ⦄
     refl refl refl refl (≤ᵇ⇒≤ _ _ tt) (≤ᵇ⇒≤ _ _ tt) refl (≤ᵇ⇒≤ _ _ tt)
     ≤-refl)
flatRow = 0 , z≤n , refl
