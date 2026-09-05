-- ══════════════════════════════════════════════════════════════════
-- THE SUMMAND AT A TELESCOPE OF SEVERAL SLOTS, AND WHY IT IS A SUM.
--
-- TARGET: subscribeInner-sz @e1520e
--
-- WHAT WAS UNTESTED.  Every reading of this leaf so far stands at a
-- telescope of ONE, so the summand's shape was never asked a question:
-- a sum over one slot and a max over one slot are the same number.
-- What a several-slot telescope decides is the JOIN.  A `shared` def
-- may name the slots below it, so ONE subscription can thread through
-- the whole telescope, running each definition once -- and layers that
-- run in series COMPOUND, which is what a sum buys and a max does not.
--
-- THE ROWS.  Eleven slots, each `shared`: a singleton at the bottom
-- and ten definitions above it, each naming the one below and doubling
-- what it carries.  Subscribing the top reference runs all eleven, and
-- the arrival's own layers are ZERO -- a bare reference -- so the
-- entire charge is the telescope and nothing else is standing in.  The
-- conclusion is read against the rival max reading and then against
-- the summand as it is stated, and reports `false` then `true`.
--
-- SO THE SEPARATION IS AT THE CONCLUSION, not merely between two
-- numbers.  The two readings are five and fifty-three, and at the
-- smallest rungs the statement admits the max reading buys seventeen
-- hundred against a delivered value of two thousand and forty-seven.
-- A max over the telescope is a FALSE reading of this leaf, and it is
-- the reading the arrival join would suggest.
--
-- WHAT THE ROWS DO NOT BUY.  Every slot here is `shared`, so nothing
-- about a `scripted` slot, whose definition a subscription does not
-- run and whose size the sum charges anyway; the telescope is a CHAIN,
-- so nothing about the JOIN a diamond asks for, which
-- `Probed.Slot-Named-Twice` reads; the door is `mergeAllᵒ`; and
-- the sum's generosity is untested from the other side -- it charges
-- slots the run never names, which no row here can fail on.
-- ══════════════════════════════════════════════════════════════════
module Probed.Slot-Telescope-Sum where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map; foldr; tabulate)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fz; suc to fs)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Exp using (Ctx; Ty; Closed; Val; Fn; natᵗ; obs; _×ᵗ_;
  emptyᵉ; ofᵉ; mapᵉ; input; nat̂; varᵗ; pairᵗ; sizeᵛ)
open import Rx.Layer-Count using (layᵉ)
open import Rx.Slots using (Slots; shared; slotSize; slotsSize)
open import Rx.Evaluator using (EvalSt; root; mergeAllᵒ; mergeAll-st;
  installNode; st-init; sched-init; iterSize; subscribeInner)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (valsSz?; subscribeInner-sz)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE RIVAL READING, WRITTEN OUT.  It is the same walk of the same
-- telescope with the join swapped, so the pair below differs in
-- exactly the thing under test.
----------------------------------------------------------------------
slotsMax : ∀ {n} {Γ : Ctx n} → Slots Γ → ℕ
slotsMax sl = foldr _⊔_ 0 (tabulate λ i → slotSize (sl i))

----------------------------------------------------------------------
-- THE PROGRAM FAMILY.  `Pw k` is the balanced product of `2 ^ k`
-- naturals and `dupG` writes its payload into both arms -- the family
-- the slot refutations are built on, here cut into one rung per slot
-- rather than stacked inside one definition.
----------------------------------------------------------------------
Pw : ℕ → Ty
Pw zero    = natᵗ
Pw (suc k) = Pw k ×ᵗ Pw k

dupG : ∀ {n} {Γ : Ctx n} {k} → Fn Γ [] [] [] (Pw k) (Pw (suc k))
dupG = pairᵗ (varᵗ (here refl)) (varᵗ (here refl))

----------------------------------------------------------------------
-- THE TELESCOPE.  Slot `k` carries `Pw k`, and every slot above the
-- bottom names the one below it: the stratification the telescope is
-- declared under is exactly what makes such a chain legal, and running
-- the top reference is what makes the chain a single subscription.
----------------------------------------------------------------------
Γᵀ : Ctx 11
Γᵀ = Pw 0 ∷ⱽ Pw 1 ∷ⱽ Pw 2 ∷ⱽ Pw 3 ∷ⱽ Pw 4 ∷ⱽ Pw 5 ∷ⱽ Pw 6 ∷ⱽ Pw 7
   ∷ⱽ Pw 8 ∷ⱽ Pw 9 ∷ⱽ Pw 10 ∷ⱽ []ⱽ

slᵀ : Slots Γᵀ
slᵀ fz                                         = shared (ofᵉ (nat̂ 0 ∷ []))
slᵀ (fs fz)                                    = shared (mapᵉ dupG (input fz))
slᵀ (fs (fs fz))                               = shared (mapᵉ dupG (input (fs fz)))
slᵀ (fs (fs (fs fz)))                          = shared (mapᵉ dupG (input (fs (fs fz))))
slᵀ (fs (fs (fs (fs fz))))                     = shared (mapᵉ dupG (input (fs (fs (fs fz)))))
slᵀ (fs (fs (fs (fs (fs fz)))))                = shared (mapᵉ dupG (input (fs (fs (fs (fs fz))))))
slᵀ (fs (fs (fs (fs (fs (fs fz))))))           = shared (mapᵉ dupG (input (fs (fs (fs (fs (fs fz)))))))
slᵀ (fs (fs (fs (fs (fs (fs (fs fz)))))))      = shared (mapᵉ dupG (input (fs (fs (fs (fs (fs (fs fz))))))))
slᵀ (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))) = shared (mapᵉ dupG (input (fs (fs (fs (fs (fs (fs (fs fz)))))))))
slᵀ (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))) =
  shared (mapᵉ dupG (input (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))))
slᵀ (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))) =
  shared (mapᵉ dupG (input (fs (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))))

eᵀ : Closed Γᵀ (Pw 10)
eᵀ = emptyᵉ

stᵀ : EvalSt eᵀ
stᵀ = installNode 0 (mergeAll-st {Γ = Γᵀ} {t = Pw 10} nothing 0 [] false)
        (st-init eᵀ)

-- the arrival is a bare reference, so its own layers are zero and the
-- whole charge is the telescope standing behind it
oᵀ : Val Γᵀ (obs (Pw 10))
oᵀ = input (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))))

outᵀ : List (Val Γᵀ (Pw 10))
outᵀ = proj₁ (proj₂ (subscribeInner {e = eᵀ} (gasPad 64 g0) mergeAllᵒ 0 root 0 0
                       oᵀ (sched-init eᵀ slᵀ) stᵀ))

----------------------------------------------------------------------
-- THE TWO READINGS AND WHAT THE RUN DELIVERS.
----------------------------------------------------------------------

-- LOAD-BEARING: the first entry says the arrival contributes nothing,
-- so neither reading is being carried by the program's own layers; the
-- next two are the rival and the stated summand, which a telescope of
-- one would report equal.
figures : List ℕ
figures = layᵉ oᵀ ∷ slotsMax slᵀ ∷ slotsSize slᵀ ∷ []

figures≡ : figures ≡ 0 ∷ 5 ∷ 53 ∷ []
figures≡ = refl

-- LOAD-BEARING: one value carrying two thousand and forty-seven nodes
-- is the chain having run END TO END.  A subscription that had stopped
-- at the slot it names would report three.
delivered≡ : map (sizeᵛ {Γ = Γᵀ} (Pw 10)) outᵀ ≡ 2047 ∷ []
delivered≡ = refl

----------------------------------------------------------------------
-- THE CONCLUSION AT THE TWO JOINS, at the smallest rungs the statement
-- admits: two is the least ladder and one bounds the arrival's syntax.
----------------------------------------------------------------------

-- LOAD-BEARING, and it is this file's product: the max reading FAILS
-- here.  Ten definitions of five units each compound in series, so a
-- join that keeps the largest of them prices one rung of a chain of
-- ten -- seventeen hundred against a delivered two thousand.
telescopeRows : List Bool
telescopeRows = valsSz? {Γ = Γᵀ} {s = Pw 10}
                  (iterSize 2 (layᵉ oᵀ + slotsMax slᵀ) 1) outᵀ
              ∷ valsSz? {Γ = Γᵀ} {s = Pw 10}
                  (iterSize 2 (layᵉ oᵀ + slotsSize slᵀ) 1) outᵀ
              ∷ []

telescopeRows≡ : telescopeRows ≡ false ∷ true ∷ []
telescopeRows≡ = refl

----------------------------------------------------------------------
-- THE TIE.  The type is generated from the statement as it reads, so a
-- restatement changes it rather than leaving the rungs above copied out
-- beside a claim.  The premises are left as arguments: the row asserts
-- the conclusion with them unasked.
----------------------------------------------------------------------

-- LOAD-BEARING: it is read at the same rungs the rows are, so a charge
-- the chained telescope outran would fail it exactly as the max
-- reading beside it does.
tieTelescope : Confirms
  (subscribeInner-sz {e = eᵀ} (gasPad 64 g0) mergeAllᵒ 0 root 0 0 oᵀ
     (sched-init eᵀ slᵀ) stᵀ 2 1)
tieTelescope = λ _ _ → refl
