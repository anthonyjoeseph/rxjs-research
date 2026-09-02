-- AN ARRIVAL THAT COMES FROM AN INNER, WHICH IS THE RE-ENTRY SHAPE NO
-- SWEEP HAS STEPPED.  Every row of every chain-door sweep so far steps
-- an arrival from the OUTER source.  An inner registered by a flatten
-- is a registry entry like any other, so an arrival from it re-enters
-- `foldPath` at a frame that is already mid-flight -- carrying the
-- sighted path the outer built rather than a fresh one -- and nothing
-- has read what the chain door does there.

-- WHY THE SECOND-ARRIVAL SWEEP COULD NOT READ IT, and it is one line
-- of its script.  That sweep needed an inner still LIVE when the next
-- arrival landed, so it timed the inner past every outer value; an
-- inner that never fires never delivers, so no arrival there ever came
-- from one.  The change here is the timing alone -- the arms, the
-- context, the measurement and the guard are that sweep's.

-- WHAT IS UNDER TEST.  The statement prices a registry by `pathSz?`,
-- whose only unbounded conjunct is a length at every frame, so what
-- could refute is a registered path left LONGER by a step taken at an
-- inner's arrival than by the same program stepped at an outer's.  The
-- inner's own chain is the one carrying the outer's frames, so if any
-- arrival lengthens a registration past its flatten control this is
-- the one.

-- WHICH ROWS BEAR WEIGHT.  The provenance pair is LOAD-BEARING and is
-- what the sweep turns on: the stepped arrival's source differs from
-- the first arrival's under the retiming and EQUALS it under the
-- sibling's, so the two readings together say the re-entry moved to an
-- inner rather than that the numbers happen to differ.  Without the
-- second half it would not be a row at all -- the three flatten arms
-- read identically here, exactly as they do on a first arrival, so
-- nothing else in the file distinguishes a retimed run from an
-- unretimed one.  The length comparison is LOAD-BEARING: it is a
-- maximum registered length against the same program's flatten
-- control at the same step, and a cut leaving a longer entry behind
-- fails it.  The registry COUNTS and the emit count are DEGENERATE
-- here -- they are carried so a step that changed shape shows up as a
-- wrong total rather than silently, and no ordering is read off them.

-- WHAT THESE ROWS DO NOT BUY.  One inner value per subscribe and one
-- level of nesting, so an arrival from an inner OF an inner is not
-- reached; and the inner is a bare slot read, so nothing here carries
-- operators of its own into the registered chain -- which is the
-- quantity `Refuted.Chain-Step-Regs-Cap` moves, and it stays flat
-- across every row below.  The stepped arrival is the SECOND overall
-- in each arm, so a chain door met after several inner deliveries have
-- already landed is unmeasured.

-- TARGET: foldPath-regsLen @68fc23
module Probed.Chain-Step-Regs-Inner where

open import Data.Bool using (true; _∧_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_; map; foldr; length)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _+_; _*_; _⊔_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; Exp; natᵗ; ofᵉ; mapᵉ; mergeAllᵉ;
  switchAllᵉ; exhaustAllᵉ; strmᵗ; input; syncSizeᵉ)
open import Rx.Prim using (gasPad; g0; cold; after_,_)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Evaluator using (Sched; EvalSt; subscribeE; sched-init;
  st-init; root; sched-next; cascade; cascadeLatch; chainStep; chainsOf;
  arrSource)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Measures using (pathLen)

Γ₃ : Ctx 3
Γ₃ = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

outer : Closed Γ₃ natᵗ
outer = input fzero

-- polymorphic in the local contexts for the same reason the sibling
-- sweep's is: it sits under a `mapᵉ` and is checked in the function's
-- own value context
inner : ∀ {Δᵍ Δ Θ} → Exp Γ₃ Δᵍ Δ Θ natᵗ
inner = input (fsuc fzero)

mrg swi exh : Closed Γ₃ natᵗ → Closed Γ₃ natᵗ
mrg src = mergeAllᵉ nothing (mapᵉ (strmᵗ inner) src)
swi src = switchAllᵉ        (mapᵉ (strmᵗ inner) src)
exh src = exhaustAllᵉ       (mapᵉ (strmᵗ inner) src)

slots : Slots Γ₃
-- THE ONE CHANGE.  `resolve` is cumulative and `after 0` is the next
-- tick, so the outer now fires at 1, 4 and 5 while the inner
-- subscribed at the first of those is due at 2 -- BETWEEN two outer
-- values.  The second arrival the schedule hands out is therefore the
-- inner's, and the source is not spent when it lands, so what is
-- measured is a chain door and not `cascadeFinish` dropping a registry.
slots fzero               = scripted (cold [] ((after 0 , 7) ∷ (after 2 , 8) ∷ (after 0 , 9) ∷ []))
slots (fsuc fzero)        = scripted (cold [] ((after 0 , 1) ∷ []))
slots (fsuc (fsuc fzero)) = shared (swi outer)

-- THE SAME PROGRAM UNDER THE SIBLING SWEEP'S TIMING, which is the
-- control that makes the provenance row load-bearing: the inner is
-- due past every outer value, so it never fires and the second
-- arrival can only be the outer's own next one.
slotsLate : Slots Γ₃
slotsLate fzero               = scripted (cold [] ((after 0 , 7) ∷ (after 2 , 8) ∷ (after 0 , 9) ∷ []))
slotsLate (fsuc fzero)        = scripted (cold [] ((after 9 , 1) ∷ []))
slotsLate (fsuc (fsuc fzero)) = shared (swi outer)

sucG : Slots Γ₃ → Closed Γ₃ natᵗ → ℕ
sucG sl e = suc (syncSizeᵉ e + hopDᵉ 0 (slotHop 0 sl) e)

sub : Slots Γ₃ → (e : Closed Γ₃ natᵗ) → Sched Γ₃ × EvalSt e
sub sl e = let r = subscribeE (gasPad (sucG sl e) g0) e root 0 0
                              (sched-init e sl) (st-init e)
           in proj₁ (proj₂ r) , proj₂ (proj₂ r)

maxLenOf : (e : Closed Γ₃ natᵗ) → EvalSt e → ℕ
maxLenOf e st = foldr _⊔_ 0
  (map (λ en → pathLen (proj₂ (proj₂ (proj₂ en)))) (EvalSt.registry st))

-- the first arrival is RUN, not constructed, and the second step
-- mirrors `cascadeGo`'s own call, exactly as the sibling sweep does it
row : (e : Closed Γ₃ natᵗ) → ℕ × ℕ × ℕ × ℕ × ℕ
row e with sched-next (proj₁ (sub slots e))
... | inj₁ _         = 0 , 0 , 0 , 0 , 0
... | inj₂ (a₁ , s₁) with cascade a₁ 1 s₁ (proj₂ (sub slots e))
...   | (_ , s₂ , st₁) with sched-next s₂
...     | inj₁ _         = 0 , 0 , 0 , 0 , 0
...     | inj₂ (a₂ , s₃) with chainsOf a₂ st₁
...       | []            = 0 , 0 , 0 , 0 , 0
...       | (rid , c) ∷ _ =
            let st₀ = record (cascadeLatch a₂ st₁) { delivered = rid ∷ [] }
                r   = chainStep 2 a₂ c s₃ st₀
            in maxLenOf e st₀ , maxLenOf e (proj₂ (proj₂ r))
             , length (EvalSt.registry st₀)
             , length (EvalSt.registry (proj₂ (proj₂ r)))
             , length (proj₁ r)

-- WHICH SOURCE THE STEPPED ARRIVAL CAME FROM, and this row is what
-- makes the sweep non-degenerate.  Every figure below reads the same
-- across the three arms, exactly as the second-arrival sweep's did on
-- a FIRST arrival -- so without this the rows would be consistent with
-- the retiming having changed nothing.  The outer occupies slot zero
-- and the inner slot one, and each subscribe of the inner mints its
-- own source, so a reading above zero is an arrival no earlier sweep
-- has stepped.
arrSrc : Slots Γ₃ → Closed Γ₃ natᵗ → ℕ
arrSrc sl e with sched-next (proj₁ (sub sl e))
... | inj₁ _         = 0
... | inj₂ (a₁ , s₁) with cascade a₁ 1 s₁ (proj₂ (sub sl e))
...   | (_ , s₂ , st₁) with sched-next s₂
...     | inj₁ _          = 0
...     | inj₂ (a₂ , _)   = suc (arrSource a₂)

-- and the FIRST arrival's source, so the reading above is a contrast
-- rather than a bare number
arrSrc₁ : Slots Γ₃ → Closed Γ₃ natᵗ → ℕ
arrSrc₁ sl e with sched-next (proj₁ (sub sl e))
... | inj₁ _        = 0
... | inj₂ (a₁ , _) = suc (arrSource a₁)

-- HOW FAR EACH ROW GOT, so a row cannot read as covered while the
-- program never reached a second `chainStep`
stage : Closed Γ₃ natᵗ → ℕ
stage e with sched-next (proj₁ (sub slots e))
... | inj₁ _         = 1
... | inj₂ (a₁ , s₁) with cascade a₁ 1 s₁ (proj₂ (sub slots e))
...   | (_ , s₂ , st₁) with sched-next s₂
...     | inj₁ _         = 2
...     | inj₂ (a₂ , _) with chainsOf a₂ st₁
...       | []          = 3
...       | _ ∷ _       = 4

lenBefore : Closed Γ₃ natᵗ → ℕ
lenBefore e = proj₁ (row e)
lenAfter : Closed Γ₃ natᵗ → ℕ
lenAfter e = proj₁ (proj₂ (row e))
regsBefore : Closed Γ₃ natᵗ → ℕ
regsBefore e = proj₁ (proj₂ (proj₂ (row e)))
regsAfter : Closed Γ₃ natᵗ → ℕ
regsAfter e = proj₁ (proj₂ (proj₂ (proj₂ (row e))))
emits : Closed Γ₃ natᵗ → ℕ
emits e = proj₂ (proj₂ (proj₂ (proj₂ (row e))))

sh₂ : Closed Γ₃ natᵗ
sh₂ = input (fsuc (fsuc fzero))

ctl swiP exhP : Closed Γ₃ natᵗ
ctl  = mrg outer
swiP = swi outer
exhP = exh outer

deepP : Closed Γ₃ natᵗ
deepP = mergeAllᵉ nothing (ofᵉ (strmᵗ sh₂ ∷ strmᵗ sh₂ ∷ []))

packed : Closed Γ₃ natᵗ → ℕ
packed e = lenBefore e + 100 * lenAfter e + 10000 * regsBefore e
         + 1000000 * regsAfter e + 100000000 * emits e

reaches : stage ctl + stage swiP + stage exhP + stage deepP ≡ 16
reaches = refl

-- THE NON-DEGENERACY ROW.  Read as a pair per arm so a change in
-- either half is visible: the first arrival's source against the
-- stepped one's.
pack4 : (Closed Γ₃ natᵗ → ℕ) → ℕ
pack4 f = f ctl + 100 * f swiP + 10000 * f exhP + 1000000 * f deepP

-- the stepped arrival's source, and the first arrival's, under the
-- retiming …
sources≡ : pack4 (arrSrc slots) ≡ 6050505
sources≡ = refl

sources₁≡ : pack4 (arrSrc₁ slots) ≡ 5040404
sources₁≡ = refl

-- … and under the sibling sweep's timing, where the two must agree
-- because the inner never fires
lateSources≡ : pack4 (arrSrc slotsLate) ≡ 5040404
lateSources≡ = refl

lateSources₁≡ : pack4 (arrSrc₁ slotsLate) ≡ 5040404
lateSources₁≡ = refl

figuresC : packed ctl ≡ 102020202
figuresC = refl

figuresSw : packed swiP ≡ 102020202
figuresSw = refl

figuresEx : packed exhP ≡ 102020202
figuresEx = refl

figuresDp : packed deepP ≡ 304040202
figuresDp = refl

no-longer-than-control : (lenAfter swiP ≤ᵇ lenAfter ctl)
                       ∧ (lenAfter exhP ≤ᵇ lenAfter ctl)
                       ∧ (lenAfter deepP ≤ᵇ lenAfter ctl) ≡ true
no-longer-than-control = refl
