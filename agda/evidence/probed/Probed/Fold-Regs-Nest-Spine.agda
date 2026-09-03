-- THE NESTING SPINE, AND THE READING TAKEN OVER IT.  This module is
-- the harness only; the rows that spend it are its two siblings,
-- `Probed.Fold-Regs-Nest-Grid` below the crossover and
-- `Probed.Fold-Regs-Nest-Cross` above it.  They are separate modules
-- because a row is one whole run of the evaluator at a program whose
-- cost climbs steeply with the height, and a harness shared by import
-- is checked once instead of once per row.

-- THE FAMILY.  A nesting frame wrapping `d` flatten levels around its
-- argument pushes about `d` frames of its own when it subscribes, and
-- `k` such frames composed down ONE spine register about `k * d`.
-- That PRODUCT is what outran a grant of twice a MAXIMUM, so it is
-- the shape to take to the grant that replaced the doubling -- a
-- frame step of two caps that are no longer tied to each other.

-- WHY HEIGHT IS THE AXIS AND DEPTH IS HELD.  Depth raises the frame's
-- own SYNTAX, and the cap is a maximum over that syntax and the
-- walked path's length, so a deeper frame BUYS the room it costs and
-- cannot refute.  Height lengthens the spine, and it moves the cap
-- only once the path outgrows the frame's syntax; below that the two
-- caps sit pinned at the syntax while the exit grows, which is the
-- one stretch in which the grant is momentarily constant in the
-- height and so the only one where a crossing could hide.

-- WHAT WOULD REFUTE.  Only the exit column.  Raising either cap
-- enlarges `sizeStep S B` and weakens the premise it gates at the
-- same time, so every instantiation above the least is strictly
-- easier and the rows are read at each cap's own least.  An exit that
-- outruns one frame step at any height is a witness against the
-- restated leaf exactly as this family was against the doubling, and
-- it would say the currency is wrong rather than the constant.

-- HOW A ROW IS PACKED.  One scalar carries the three caps, the
-- verdict and the stage the run reached, and the subscribe and the
-- chain list are matched on rather than projected, so one run of the
-- evaluator serves every column.  A separate accessor per column
-- would pay for the whole evaluation once per column, which is the
-- difference between a row that fits a dev check and one that does
-- not.

-- TARGET: foldPath-regsLen @d58775
module Probed.Fold-Regs-Nest-Spine where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp using (Ctx; Closed; Exp; Fn; natᵗ; obs; ofᵉ; mapᵉ;
  mergeAllᵉ; strmᵗ; varᵗ; input; syncSizeᵉ)
open import Rx.Prim using (gasPad; g0; cold; after_,_)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next; cascadeLatch; chainsOf;
  foldPath; Arrival; Path; RegId; arrTy; arrVal; arrTick; arrSource; budgetAt; sizeStep)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (pathSz?; regsSz?)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?)

open import Verify-Budget-Sufficient.Regs-Fold-Len using (foldPath-regsLen)

open import Probed.Apparatus using (Confirms)
open import Probed.Fold-Regs-Row using (e₀; gp; pth; vls; evs₀; fin₀; sd₀; st₀;
  le1; le2; pv; pp; pr; foldRow)

Γ₃ : Ctx 3
Γ₃ = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

outer : Closed Γ₃ natᵗ
outer = input fzero

inner : ∀ {Δᵍ Δ Θ} → Exp Γ₃ Δᵍ Δ Θ natᵗ
inner = input (fsuc fzero)

-- the nesting frame's body: `d` flatten levels wrapped around the
-- incoming observable, each one a `mergeAllᵉ` over a singleton.  This
-- is the family that refuted the doubling, taken here at the two caps
-- that replaced it
nest : ℕ → Exp Γ₃ [] [] (obs natᵗ ∷ []) natᵗ
nest zero    = mergeAllᵉ nothing (ofᵉ (varᵗ (here refl) ∷ []))
nest (suc d) = mergeAllᵉ nothing (ofᵉ (strmᵗ (nest d) ∷ []))

deep : ℕ → Fn Γ₃ [] [] [] (obs natᵗ) (obs natᵗ)
deep d = strmᵗ (nest d)

lifted : Closed Γ₃ (obs natᵗ)
lifted = mapᵉ (strmᵗ inner) outer

dstack : ℕ → ℕ → Closed Γ₃ (obs natᵗ) → Closed Γ₃ (obs natᵗ)
dstack d zero    s = s
dstack d (suc k) s = mapᵉ (deep d) (dstack d k s)

prog : ℕ → ℕ → Closed Γ₃ natᵗ
prog d k = mergeAllᵉ nothing (dstack d k lifted)

slots : Slots Γ₃
slots fzero               = scripted (cold [] ((after 0 , 7) ∷ (after 2 , 8) ∷ (after 0 , 9) ∷ []))
slots (fsuc fzero)        = scripted (cold [] ((after 9 , 1) ∷ []))
slots (fsuc (fsuc fzero)) = scripted (cold [] ((after 9 , 2) ∷ []))

sucG : Closed Γ₃ natᵗ → ℕ
sucG e = suc (syncSizeᵉ e + hopDᵉ 0 (slotHop 0 slots) e)

sub : (e : Closed Γ₃ natᵗ) → Sched Γ₃ × EvalSt e
sub e = let r = subscribeE (gasPad (sucG e) g0) e root 0 0
                           (sched-init e slots) (st-init e)
        in proj₁ (proj₂ r) , proj₂ (proj₂ r)

-- the least budget at which a Boolean reading holds, searched upward
-- from zero.  Running off the fuel reports zero, which a satisfied
-- search can never return here, so an exhausted search is visible in
-- the figures rather than silent
least : (ℕ → Bool) → ℕ → ℕ → ℕ
least p zero    b = 0
least p (suc f) b = if p b then b else least p f (suc b)

fuel : ℕ
fuel = 400

-- one chain whose exit outruns its own frame step turns the verdict
-- red, so the conjunction is what carries the reading and the three
-- maxima are only there to be pinned
scan : (e : Closed Γ₃ natᵗ) (a : Arrival Γ₃) (s : Sched Γ₃) (st : EvalSt e)
     → List (RegId × Path Γ₃ (arrTy a) natᵗ) → ℕ × ℕ × ℕ × Bool
scan e a s st [] = 0 , 0 , 0 , true
scan e a s st ((rid , c) ∷ rest) =
  let st₀ = record st { delivered = rid ∷ [] }
      r   = foldPath (budgetAt e (Sched.slots s) 1) 3 1
              (arrTick a) (arrSource a) c (arrVal a ∷ [])
              [] false s st₀
      sV  = least (λ b → pathSz? b c) fuel 0
      bV  = least (λ b → valsSz? b (arrVal a ∷ [])
                       ∧ regsSz? b (EvalSt.registry st₀)) fuel 0
      eV  = least (λ b → regsSz? b
                       (EvalSt.registry (proj₂ (proj₂ r)))) fuel 0
      rec = scan e a s st rest
  in (sV ⊔ proj₁ rec)
   , (bV ⊔ proj₁ (proj₂ rec))
   , (eV ⊔ proj₁ (proj₂ (proj₂ rec)))
   , ((eV ≤ᵇ sizeStep sV bV) ∧ proj₂ (proj₂ (proj₂ rec)))

read : (e : Closed Γ₃ natᵗ) → Sched Γ₃ × EvalSt e → ℕ × ℕ × ℕ × Bool × ℕ
read e (sd , st) with sched-next sd
... | inj₁ _       = 0 , 0 , 0 , false , 1
... | inj₂ (a , s) with chainsOf a st
...   | []         = 0 , 0 , 0 , false , 2
...   | c ∷ cs     with scan e a s (cascadeLatch a st) (c ∷ cs)
...     | sV , bV , eV , f = sV , bV , eV , f , 3

pack : ℕ × ℕ × ℕ × Bool × ℕ → ℕ
pack (s , b , e , f , g) =
  s + 100 * b + 10000 * e + 1000000 * (if f then 1 else 0) + 10000000 * g

rowOf : Closed Γ₃ natᵗ → ℕ
rowOf e = pack (read e (sub e))

-- AND THE TIE TO THE STATEMENT, held at the point this family shares.
-- The rows above are the READING; `foldTie` is what holds them to
-- `foldPath-regsLen` as it now reads, so a restatement of the target
-- breaks here rather than leaving the reading green about text that is
-- gone.  What the point covers, and what it does not, is stated where
-- it is paid for: `Probed.Fold-Regs-Row`.
foldTie : Confirms
  (foldPath-regsLen {e = e₀} gp 3 1 0 0 pth vls evs₀ fin₀ sd₀ st₀ 1 2
     le1 le2 pv pp pr)
foldTie = foldRow
