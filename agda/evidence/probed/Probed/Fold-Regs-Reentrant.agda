-- THE WALK THAT RE-ENTERS THE STRUCTURE PRICING `B`, WHICH IS THE
-- HOLE THE SEPARATION LEFT.  The separated reading stood a heavy
-- branch beside a light one and fired the light source, so the walked
-- path was DISJOINT from the entries setting `B`: the fold carried
-- the standing registry forward untouched and added nothing bigger,
-- and the whole frame step read as spare.  That is the easy half.
-- The consumer's walk is not disjoint -- it climbs frames of the same
-- kind as the ones it is registered under, and every frame it climbs
-- SUBSCRIBES, so the entries it adds are built from walked syntax and
-- land in a registry already standing at `B`.

-- SO THE TWO DEPTHS ARE SWEPT INDEPENDENTLY.  The heavy branch
-- carries `k` duplicator frames and its source is due late, so it
-- sets `B` without ever being walked.  The walked branch carries `j`
-- of the SAME frames and its source fires at once, so the fold's own
-- registrations are cut from the same cloth as the standing ones.
-- That is the configuration neither earlier reading covers: the
-- duplicator sweep had `j = k` and collapsed the columns, the
-- separated sweep had `j = 0` and stood the walk beside the
-- structure instead of inside it.

-- AND THE READING IS TAKEN OVER EVERY CHAIN THE ARRIVAL MATCHES.
-- The leaf is stated per chain, so reading the head of the registry's
-- list is legitimate and weak -- it reports whichever chain happened
-- to be listed first.  Each column here is the worst over the list
-- and the verdict is the conjunction across it.

-- WHAT WOULD REFUTE, AND IT IS THE EXIT COLUMN ALONE.  Neither cap
-- can refute by moving up -- raising either enlarges `sizeStep S B`
-- and weakens the premise it gates at once -- so the rows are read at
-- each cap's own least and the only falsifiable reading is `E ≤ᵇ
-- sizeStep S B`.  An `E` that outruns one frame step is a witness
-- against the leaf exactly as the nesting spine was against the
-- doubling it replaced; an `E` that tracks `B` says the walk's own
-- registrations stay under the standing ones even when they are the
-- same shape.

-- WHAT THE SWEEP FOUND, INCLUDING THE PART THAT DID NOT WORK.  The
-- caps do stay apart with the walk inside the structure -- the path
-- column holds at six while the registry column moves with `k` -- and
-- the exit column equals the registry column at every row, so the
-- fold's own registrations stay under the standing ones even when
-- they are the same shape, and the frame step is spare by the same
-- wide margin the disjoint reading showed.  But `j` MOVED NO COLUMN:
-- three walked frames read identically to one, so this construction
-- does not in fact lengthen the walked chain.  What it covers is a
-- walk whose frames share the SHAPE of the standing ones, not a walk
-- that is longer, and the depth axis is still unread at this door.

-- WHICH ROWS BEAR WEIGHT.  `fits` is LOAD-BEARING and is the reading.
-- `separates` is LOAD-BEARING for a narrower claim than its namesake
-- carries in the disjoint file: here it says the caps stay apart
-- while the walk is inside the structure, which is what makes the
-- `fits` row a new region rather than a re-run.  `figures` is
-- LOAD-BEARING because it pins all three columns, so a `fits` that
-- passed on a least-budget search running off its fuel shows up as a
-- wrong number rather than a green -- and it is what makes the dead
-- `j` axis visible instead of hiding inside a green.  `reaches` is
-- DEGENERATE and guards against reading any of it over a run that
-- never got to the door.

-- TARGET: foldPath-regsLen @d58775
module Probed.Fold-Regs-Reentrant where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_; _≤ᵇ_; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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

third : Closed Γ₃ natᵗ
third = input (fsuc (fsuc fzero))

inner : ∀ {Δᵍ Δ Θ} → Exp Γ₃ Δᵍ Δ Θ natᵗ
inner = input (fsuc fzero)

-- the frame both branches are built from: its body merges its own
-- argument with itself, so it SUBSCRIBES when walked and the entries
-- it adds are cut from the same syntax the standing entries are
dup : Fn Γ₃ [] [] [] (obs natᵗ) (obs natᵗ)
dup = strmᵗ (mergeAllᵉ nothing
       (ofᵉ (varᵗ (here refl) ∷ varᵗ (here refl) ∷ [])))

lifted : Closed Γ₃ (obs natᵗ)
lifted = mapᵉ (strmᵗ inner) outer

light : Closed Γ₃ (obs natᵗ)
light = mapᵉ (strmᵗ inner) third

stack : ℕ → Closed Γ₃ (obs natᵗ) → Closed Γ₃ (obs natᵗ)
stack zero    s = s
stack (suc k) s = mapᵉ dup (stack k s)

-- `k` frames nothing walks, `j` frames the first arrival climbs
heavyN : ℕ → Closed Γ₃ natᵗ
heavyN k = mergeAllᵉ nothing (stack k lifted)

walkedN : ℕ → Closed Γ₃ natᵗ
walkedN j = mergeAllᵉ nothing (stack j light)

prog : ℕ → ℕ → Closed Γ₃ natᵗ
prog j k = mergeAllᵉ nothing
             (ofᵉ (strmᵗ (heavyN k) ∷ strmᵗ (walkedN j) ∷ []))

-- the walked branch's source fires at once and everything feeding the
-- heavy branch is due past it
slots : Slots Γ₃
slots fzero               = scripted (cold [] ((after 9 , 7) ∷ []))
slots (fsuc fzero)        = scripted (cold [] ((after 9 , 1) ∷ []))
slots (fsuc (fsuc fzero)) = scripted (cold [] ((after 0 , 2) ∷ (after 2 , 3) ∷ []))

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

-- a single chain whose exit outruns its own frame step turns the
-- verdict red, so the conjunction is what carries the reading and the
-- three maxima are only there to be pinned
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

capsOf : (e : Closed Γ₃ natᵗ) → ℕ × ℕ × ℕ × Bool
capsOf e with sched-next (proj₁ (sub e))
... | inj₁ _        = 0 , 0 , 0 , false
... | inj₂ (a , s)  =
      scan e a s (cascadeLatch a (proj₂ (sub e)))
        (chainsOf a (proj₂ (sub e)))

Sof Bof Eof : Closed Γ₃ natᵗ → ℕ
Sof e = proj₁ (capsOf e)
Bof e = proj₁ (proj₂ (capsOf e))
Eof e = proj₁ (proj₂ (proj₂ (capsOf e)))

Fof : Closed Γ₃ natᵗ → Bool
Fof e = proj₂ (proj₂ (proj₂ (capsOf e)))

stage : Closed Γ₃ natᵗ → ℕ
stage e with sched-next (proj₁ (sub e))
... | inj₁ _        = 1
... | inj₂ (a , _) with chainsOf a (proj₂ (sub e))
...   | []          = 2
...   | _ ∷ _       = 3

q0 q1 q2 : Closed Γ₃ natᵗ
q0 = prog 1 4
q1 = prog 1 7
q2 = prog 3 7

reaches : stage q0 + stage q1 + stage q2 ≡ 9
reaches = refl

figures : Sof q0 + 100 * Bof q0 + 10000 * Eof q0
        + 1000000 * Sof q2 + 100000000 * Bof q2 + 10000000000 * Eof q2
        ≡ 101006070706
figures = refl

figures′ : Sof q1 + 100 * Bof q1 + 10000 * Eof q1 ≡ 101006
figures′ = refl

separates : (Sof q0 <ᵇ Bof q0) ∧ (Sof q1 <ᵇ Bof q1) ∧ (Sof q2 <ᵇ Bof q2)
          ≡ true
separates = refl

fits : Fof q0 ∧ Fof q1 ∧ Fof q2 ≡ true
fits = refl

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
