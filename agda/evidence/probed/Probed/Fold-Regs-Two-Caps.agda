-- THE TWO CAPS PULLED APART, WHICH IS THE ONE THING NO EARLIER ROW
-- DID.  The fold's leaf prices the walked path at `S` and the
-- standing registry and arriving values at `B ≥ S`, and concludes at
-- one frame step `sizeStep S B`.  Every row taken against it reads a
-- SINGLE number: the duplicator sweep searches one joint budget
-- covering all three premises, and the nesting witness's repair row
-- is read at `S = B`.  So the grant has never been read where the two
-- differ, and `sizeStep S B` is strictly smaller than the
-- `sizeStep B B` those rows effectively bought.

-- WHICH AXIS COULD REFUTE, DECIDED BEFORE SWEEPING ANYTHING.  Neither
-- cap can, by moving up.  Raising `B` enlarges the grant AND weakens
-- the two premises it gates, and raising `S` does the same for the
-- path premise, so every instantiation above the least is strictly
-- easier than the least.  For a fixed reached door the binding
-- instantiation is therefore unique: each cap at the smallest value
-- its own premise admits.  A sweep over either cap is unfalsifiable
-- by construction, however many rows it has -- so separation is a
-- property of the PROGRAM, and the only question is which programs
-- have it.

-- AND THE TWO OBVIOUS FAMILIES DO NOT, WHICH IS WHY THE PROGRAM BELOW
-- IS SHAPED AS IT IS.  Growing the registry by applying the fold
-- again saturates at once -- the cap stands still from the first step
-- on, so the iterate is not a source of separation.  And on the
-- DUPLICATOR the two caps are pinned together by construction:
-- `pathSz?` charges every frame's OWN syntax as well as the path's
-- length, so a value the frames on the walked path built is priced by
-- the very cap that prices them, and the path column tracks the value
-- column exactly.  Both were read before this program was written.

-- SO THE BIG SYNTAX HAS TO STAND OFF THE WALKED PATH.  Two branches
-- are merged: a heavy one carrying the duplicator stack, and a light
-- one that is a single map.  Both are registered when the program is
-- subscribed, so the standing registry is priced by the heavy branch;
-- the scheduler is then scripted so the FIRST arrival comes on the
-- light branch, whose walked path is three frames of small syntax.
-- That is the shape the consumer stands in -- a registry carrying
-- everything the program registered, against a walk that touches one
-- corner of it.

-- AND THE WALK DOES NOT CHARGE THE REGISTRY AT ALL.  The path column
-- stands at three across the sweep while the registry column climbs
-- six, nine, fourteen with the branch nothing walks -- so the caps
-- separate, and by a gap that widens on demand.  The exit column
-- equals the registry column on every row: what the fold leaves
-- behind is priced by the entries it CARRIED FORWARD and by nothing
-- the walk added, so the whole frame step is spare and the margin
-- widens with the separation rather than closing.  That is the
-- opposite of the nesting family, where the walked spine is the thing
-- that grows, and it is why the two shapes have to be read
-- separately.

-- WHICH ROWS BEAR WEIGHT.  `separates` is LOAD-BEARING and is what
-- makes the rest a new reading rather than a re-run: it says the
-- standing registry strictly outprices the walked path, so the grant
-- below really is the smaller of the two the joint rows bought.
-- `fits` is LOAD-BEARING and is the reading -- a `≤ᵇ` between two
-- independently searched numbers, so a door whose exit outran one
-- frame step of its own two caps would read false.  `figures` is
-- LOAD-BEARING for a third reason: it pins all three columns, so a
-- `fits` that passed because a least-budget search ran off its fuel
-- and reported zero shows up as a wrong number rather than a green.
-- `reaches` is DEGENERATE and guards against reading any of it over a
-- run that never got to the door.

-- TARGET: foldPath-regsLen @d58775
module Probed.Fold-Regs-Two-Caps where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤ᵇ_; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; Exp; Fn; natᵗ; obs; ofᵉ; mapᵉ;
  mergeAllᵉ; strmᵗ; varᵗ; input; syncSizeᵉ)
open import Rx.Prim using (gasPad; g0; cold; after_,_)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next; cascadeLatch; chainsOf;
  foldPath; arrVal; arrTick; arrSource; budgetAt; sizeStep)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (pathSz?; regsSz?)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?)

Γ₃ : Ctx 3
Γ₃ = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

outer : Closed Γ₃ natᵗ
outer = input fzero

third : Closed Γ₃ natᵗ
third = input (fsuc (fsuc fzero))

inner : ∀ {Δᵍ Δ Θ} → Exp Γ₃ Δᵍ Δ Θ natᵗ
inner = input (fsuc fzero)

-- THE DUPLICATOR: its body merges its own argument with itself, so
-- the returned value mentions the incoming syntax twice while the
-- type is unchanged -- which is what lets the frames stack without
-- the program's type growing with them, and what makes the heavy
-- branch expensive to register.
dup : Fn Γ₃ [] [] [] (obs natᵗ) (obs natᵗ)
dup = strmᵗ (mergeAllᵉ nothing
       (ofᵉ (varᵗ (here refl) ∷ varᵗ (here refl) ∷ [])))

lifted : Closed Γ₃ (obs natᵗ)
lifted = mapᵉ (strmᵗ inner) outer

stack : ℕ → Closed Γ₃ (obs natᵗ) → Closed Γ₃ (obs natᵗ)
stack zero    s = s
stack (suc k) s = mapᵉ dup (stack k s)

heavy : ℕ → Closed Γ₃ (obs natᵗ)
heavy k = stack k lifted

-- the light branch: one map, and the source that drives it is the one
-- the scheduler fires first
light : Closed Γ₃ (obs natᵗ)
light = mapᵉ (strmᵗ inner) third

-- each branch is flattened to a value stream first, so `strmᵗ` can
-- wrap it as a term and the two can stand side by side in one `ofᵉ`
heavyN : ℕ → Closed Γ₃ natᵗ
heavyN k = mergeAllᵉ nothing (heavy k)

lightN : Closed Γ₃ natᵗ
lightN = mergeAllᵉ nothing light

prog : ℕ → Closed Γ₃ natᵗ
prog k = mergeAllᵉ nothing
           (ofᵉ (strmᵗ (heavyN k) ∷ strmᵗ lightN ∷ []))

-- the light branch's source fires immediately and everything feeding
-- the heavy branch is due past it, so the first arrival the scheduler
-- hands out walks the short path while the registry already carries
-- the whole program
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

-- THE READING, all three columns at the SAME reached door.  `S`
-- prices ONLY the walked path; `B` prices the arriving value together
-- with the standing registry, which is the leaf's other side; `E` is
-- the least the output registry satisfies.
capsOf : (e : Closed Γ₃ natᵗ) → ℕ × ℕ × ℕ
capsOf e with sched-next (proj₁ (sub e))
... | inj₁ _        = 0 , 0 , 0
... | inj₂ (a , s) with chainsOf a (proj₂ (sub e))
...   | []            = 0 , 0 , 0
...   | (rid , c) ∷ _ =
        let st₀ = record (cascadeLatch a (proj₂ (sub e))) { delivered = rid ∷ [] }
            r   = foldPath (budgetAt e (Sched.slots s) 1) 3 1
                    (arrTick a) (arrSource a) c (arrVal a ∷ [])
                    [] false s st₀
            sP  = λ b → pathSz? b c
            bP  = λ b → valsSz? b (arrVal a ∷ [])
                      ∧ regsSz? b (EvalSt.registry st₀)
            eP  = λ b → regsSz? b (EvalSt.registry (proj₂ (proj₂ r)))
        in least sP fuel 0 , least bP fuel 0 , least eP fuel 0

Sof Bof Eof : Closed Γ₃ natᵗ → ℕ
Sof e = proj₁ (capsOf e)
Bof e = proj₁ (proj₂ (capsOf e))
Eof e = proj₂ (proj₂ (capsOf e))

stage : Closed Γ₃ natᵗ → ℕ
stage e with sched-next (proj₁ (sub e))
... | inj₁ _        = 1
... | inj₂ (a , _) with chainsOf a (proj₂ (sub e))
...   | []          = 2
...   | _ ∷ _       = 3

p0 p1 p2 : Closed Γ₃ natᵗ
p0 = prog 1
p1 = prog 6
p2 = prog 11

reaches : stage p0 + stage p1 + stage p2 ≡ 9
reaches = refl

figures : Sof p0 + 100 * Bof p0 + 10000 * Eof p0
        + 1000000 * Sof p1 + 100000000 * Bof p1 + 10000000000 * Eof p1
        ≡ 90903060603
figures = refl

figures′ : Sof p2 + 100 * Bof p2 + 10000 * Eof p2 ≡ 141403
figures′ = refl

-- THE CAPS REALLY CAME APART.  On every height the standing registry
-- costs strictly more than the walked path, so the grant read below
-- is the smaller `sizeStep S B` and not the `sizeStep B B` a joint
-- search would have bought.
separates : (Sof p0 <ᵇ Bof p0) ∧ (Sof p1 <ᵇ Bof p1) ∧ (Sof p2 <ᵇ Bof p2)
          ≡ true
separates = refl

-- THE SWEEP.  At three heights of the branch the walk never touches,
-- the output registry sits inside ONE FRAME STEP of the door's own
-- two caps, taken separately.  The heavy branch is what moves between
-- rows, so a grant that had been paying for the registry out of the
-- path's cap would come apart as the two columns spread -- and it
-- does not: the margin widens row by row.
fits : (Eof p0 ≤ᵇ sizeStep (Sof p0) (Bof p0))
     ∧ (Eof p1 ≤ᵇ sizeStep (Sof p1) (Bof p1))
     ∧ (Eof p2 ≤ᵇ sizeStep (Sof p2) (Bof p2))
     ≡ true
fits = refl
