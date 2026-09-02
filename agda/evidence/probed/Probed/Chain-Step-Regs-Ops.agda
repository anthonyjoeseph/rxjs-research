-- AN INNER THAT CARRIES OPERATORS, WHICH IS THE ONE AXIS KNOWN TO
-- BREAK THIS STATEMENT'S PREDECESSOR.  Six chain-door sweeps now cover
-- the door's re-entries -- depth, share telescope, fan width, both
-- cutting arms, the second arrival and the arrival that comes from an
-- inner -- and every one of them registers an inner that is a BARE
-- SLOT READ.  So no registered chain in any of them ever gained a
-- frame of the inner's own, and the length conjunct reads flat
-- throughout.  `Refuted.Chain-Step-Regs-Cap` moves exactly that
-- quantity to break the fixed-cap form of this statement: a
-- subscribing frame swaps its head for a `from-inner` and pushes one
-- frame per operator of the inner, so what lands in the registry is
-- longer than what was walked.

-- WHAT IS UNDER TEST, and it is the flatness rather than the bound.
-- The flatness on record is a property of the programs swept, not yet
-- of the door, and nothing in the tree says which.  These rows vary
-- the inner's operator count with everything else held at the second
-- arrival sweep's program, so a registered length that tracks the
-- count says the refuting axis is live in a RUN and not only in a
-- constructed state -- and a length that stays flat would say the
-- evaluator does not push those frames along this route at all.

-- AND THE READING IS TAKEN AS A SUM RATHER THAN A MAXIMUM, which is
-- the one measurement choice here and it is forced.  A step registers
-- ONE new entry, and the entry it registers is shorter than the
-- longest one already standing at every count below three -- so the
-- maximum is flat across the step in five of six rows while the
-- registry is genuinely gaining frames.  A maximum answers what
-- `regsSz?` charges; a sum is what shows the charge MOVING, and a
-- sweep whose whole question is whether an axis is live needs the
-- second.

-- WHICH ROWS BEAR WEIGHT.  The growth row is LOAD-BEARING and is the
-- sweep: the merge arm's registered total grows by exactly one more
-- than the inner's operator count at each of three counts, against a
-- switch arm that grows by nothing at any of them.  Either half alone
-- would be consistent with the numbers being about something else --
-- the switch abandons and re-registers, so its zero is a cancellation
-- and not an absence -- and the two together say the frames pushed are
-- the inner's.  The fit row is LOAD-BEARING too: it reads that growth
-- against the inner's own syntax, which is the quantity the arrival's
-- size premise bounds, so it is the one row that speaks to whether a
-- LEVEL pays.  The maximum lengths and the syntax sizes are
-- DEGENERATE -- carried so an arm that changed shape shows up as a
-- wrong total rather than silently.

-- WHAT THESE ROWS DO NOT BUY.  Three operator counts and one nesting
-- level, and the operators are identity maps, so a frame that reads
-- its argument's syntax rather than merely occupying a node is
-- unmeasured.  The step registers one entry in every row, so nothing
-- here says what several subscribes inside a single step do to the
-- total -- which is the shape the cascade fold spends this statement
-- at, and it is the one the sum would have to be read cumulatively
-- against.

-- TARGET: chainStep-regsSz @a3d8b7
module Probed.Chain-Step-Regs-Ops where

open import Data.Bool using (true; _∧_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_; map; foldr)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _+_; _*_; _∸_; _⊔_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; Exp; natᵗ; mapᵉ; mergeAllᵉ; switchAllᵉ; strmᵗ; varᵗ; input; syncSizeᵉ; sizeᵉ)
open import Rx.Prim using (gasPad; g0; cold; after_,_)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Evaluator using (Sched; EvalSt; subscribeE; sched-init;
  st-init; root; sched-next; cascade; cascadeLatch; chainStep; chainsOf)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Measures using (pathLen)

Γ₃ : Ctx 3
Γ₃ = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

outer : Closed Γ₃ natᵗ
outer = input fzero

-- the inner at three operator counts.  `varᵗ (here refl)` is the
-- identity on the mapped value, so each wrapper adds an operator and
-- nothing else -- the same one-node-per-frame shape the refutation
-- uses, and the reason the arms below differ in one number only
inner0 inner1 inner2 : ∀ {Δᵍ Δ Θ} → Exp Γ₃ Δᵍ Δ Θ natᵗ
inner0 = input (fsuc fzero)
inner1 = mapᵉ (varᵗ (here refl)) inner0
inner2 = mapᵉ (varᵗ (here refl)) inner1

-- the same three at the closed contexts, so `sizeᵉ` below has
-- something to read: the polymorphic form leaves its contexts open
i0 i1 i2 : Closed Γ₃ natᵗ
i0 = inner0
i1 = inner1
i2 = inner2

swi0 swi1 swi2 : Closed Γ₃ natᵗ → Closed Γ₃ natᵗ
swi0 src = switchAllᵉ (mapᵉ (strmᵗ inner0) src)
swi1 src = switchAllᵉ (mapᵉ (strmᵗ inner1) src)
swi2 src = switchAllᵉ (mapᵉ (strmᵗ inner2) src)

mrg0 mrg1 mrg2 : Closed Γ₃ natᵗ → Closed Γ₃ natᵗ
mrg0 src = mergeAllᵉ nothing (mapᵉ (strmᵗ inner0) src)
mrg1 src = mergeAllᵉ nothing (mapᵉ (strmᵗ inner1) src)
mrg2 src = mergeAllᵉ nothing (mapᵉ (strmᵗ inner2) src)

-- the inner-arrival sweep's timing: the outer fires at 1, 4 and 5 and
-- the inner subscribed at the first of those is due at 2, so the
-- stepped arrival comes from an inner
slots : Slots Γ₃
slots fzero               = scripted (cold [] ((after 0 , 7) ∷ (after 2 , 8) ∷ (after 0 , 9) ∷ []))
slots (fsuc fzero)        = scripted (cold [] ((after 9 , 1) ∷ []))
slots (fsuc (fsuc fzero)) = shared (swi0 outer)

sucG : Closed Γ₃ natᵗ → ℕ
sucG e = suc (syncSizeᵉ e + hopDᵉ 0 (slotHop 0 slots) e)

sub : (e : Closed Γ₃ natᵗ) → Sched Γ₃ × EvalSt e
sub e = let r = subscribeE (gasPad (sucG e) g0) e root 0 0
                           (sched-init e slots) (st-init e)
        in proj₁ (proj₂ r) , proj₂ (proj₂ r)

maxLenOf sumLenOf : (e : Closed Γ₃ natᵗ) → EvalSt e → ℕ
maxLenOf e st = foldr _⊔_ 0
  (map (λ en → pathLen (proj₂ (proj₂ (proj₂ en)))) (EvalSt.registry st))
sumLenOf e st = foldr _+_ 0
  (map (λ en → pathLen (proj₂ (proj₂ (proj₂ en)))) (EvalSt.registry st))

row : (e : Closed Γ₃ natᵗ) → ℕ × ℕ × ℕ × ℕ
row e with sched-next (proj₁ (sub e))
... | inj₁ _         = 0 , 0 , 0 , 0
... | inj₂ (a₁ , s₁) with cascade a₁ 1 s₁ (proj₂ (sub e))
...   | (_ , s₂ , st₁) with sched-next s₂
...     | inj₁ _         = 0 , 0 , 0 , 0
...     | inj₂ (a₂ , s₃) with chainsOf a₂ st₁
...       | []            = 0 , 0 , 0 , 0
...       | (rid , c) ∷ _ =
            let st₀ = record (cascadeLatch a₂ st₁) { delivered = rid ∷ [] }
                r   = chainStep 2 a₂ c s₃ st₀
            in maxLenOf e st₀ , maxLenOf e (proj₂ (proj₂ r))
             , sumLenOf e st₀ , sumLenOf e (proj₂ (proj₂ r))

stage : Closed Γ₃ natᵗ → ℕ
stage e with sched-next (proj₁ (sub e))
... | inj₁ _         = 1
... | inj₂ (a₁ , s₁) with cascade a₁ 1 s₁ (proj₂ (sub e))
...   | (_ , s₂ , st₁) with sched-next s₂
...     | inj₁ _         = 2
...     | inj₂ (a₂ , _) with chainsOf a₂ st₁
...       | []          = 3
...       | _ ∷ _       = 4

lenBefore lenAfter sumBefore sumAfter : Closed Γ₃ natᵗ → ℕ
lenBefore e = proj₁ (row e)
lenAfter  e = proj₁ (proj₂ (row e))
sumBefore e = proj₁ (proj₂ (proj₂ (row e)))
sumAfter  e = proj₂ (proj₂ (proj₂ (row e)))

packed : Closed Γ₃ natᵗ → ℕ
packed e = lenBefore e + 100 * lenAfter e + 10000 * sumBefore e
         + 1000000 * sumAfter e

s0 s1 s2 : Closed Γ₃ natᵗ
s0 = swi0 outer
s1 = swi1 outer
s2 = swi2 outer

m0 m1 m2 : Closed Γ₃ natᵗ
m0 = mrg0 outer
m1 = mrg1 outer
m2 = mrg2 outer

reaches : stage s0 + stage s1 + stage s2 + stage m0 + stage m1 + stage m2 ≡ 24
reaches = refl

-- the inners differ in operator count alone: one `mapᵉ` node and its
-- identity function per step, so two of syntax each
syntaxes : sizeᵉ i0 + 100 * sizeᵉ i1 + 10000 * sizeᵉ i2 ≡ 50301
syntaxes = refl

figS0 : packed s0 ≡ 3030202
figS0 = refl
figS1 : packed s1 ≡ 4040202
figS1 = refl
figS2 : packed s2 ≡ 5050303
figS2 = refl
figM0 : packed m0 ≡ 4030202
figM0 = refl
figM1 : packed m1 ≡ 6040202
figM1 = refl
figM2 : packed m2 ≡ 8050303
figM2 = refl

grew : Closed Γ₃ natᵗ → ℕ
grew e = sumAfter e ∸ sumBefore e

-- THE SWEEP.  One `from-inner` plus one frame per operator, at each of
-- three counts …
mergeGrowth : grew m0 + 100 * grew m1 + 10000 * grew m2 ≡ 30201
mergeGrowth = refl

-- … against the arm that abandons, where the same three counts cost
-- nothing at all, so the reading above is the inner's frames and not
-- the step's own bookkeeping
switchGrowth : grew s0 + 100 * grew s1 + 10000 * grew s2 ≡ 0
switchGrowth = refl

-- and the growth sits under the inner's own syntax, which is what the
-- arrival's size premise bounds -- so a level, which multiplies the
-- reading, covers what a fixed cap could not
fits : (grew m0 ≤ᵇ sizeᵉ i0) ∧ (grew m1 ≤ᵇ sizeᵉ i1)
     ∧ (grew m2 ≤ᵇ sizeᵉ i2) ≡ true
fits = refl
