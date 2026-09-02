-- THE DIAMOND, WHICH IS THE SHAPE A SHARE EXISTS FOR AND THE ONE
-- NEITHER RE-ENTRY SWEEP HAD.  `Probed.Chain-Step-Regs-Level` walks
-- the rootward stack and `Probed.Chain-Step-Regs-Share` the share
-- telescope, and in both of them every share fans out to exactly ONE
-- registered chain -- so both measure a share as a relay.  A share
-- with one subscriber is not a share.  `shareGo` folds the
-- registrations of share `i` one after another, threading the state
-- through, and each of those chains may sink again; that is the only
-- place in `chainStep` where one arrival becomes many, and it is the
-- axis with no row at all.

-- WIDTH IS A ROOT-SIDE CHOICE, NOT A TELESCOPE ONE, which is what
-- makes this cheap.  A share's registrations are its SUBSCRIBERS, so
-- `w` chains on one share is `w` branches of the root reading the same
-- `input` -- `mergeAllᵉ` over an `ofᵉ` of `w` copies, the merge every
-- rxjs diamond is written as.  The slot telescope does not move at
-- all: three slots, a scripted driver at zero and shares at one and
-- two, with the width varied in the PROGRAM.

-- AND ONE ROW WHERE WIDTH MEETS DEPTH, because the compounding case is
-- the product and not either factor.  Slot two's own def is a two-way
-- fan on slot one, so a program fanning `w` ways onto slot two puts a
-- share of width two UNDER a share of width `w`: one arrival crosses
-- the first sink into two chains, each of which crosses the second
-- into `w`.  A relay reading of a share predicts `w` deliveries there
-- and a fan reading predicts `2·w`, so the emit count separates them
-- outright.

-- WHAT COULD REFUTE, and it is the registered length alone.  The
-- statement prices a registry by `pathSz?`, whose only unbounded
-- conjunct is `suc (pathLen p) ≤ B` at every frame, and one level step
-- takes B to `S * suc (2 * B)`.  Width moves the registry's LENGTH
-- (how many entries) and the emit count for free; whether it moves the
-- longest entry is the question, and a `w` that lengthens the maximum
-- registered path is what a refutation looks like.

-- TARGET: chainStep-regsSz @a3d8b7
module Probed.Chain-Step-Regs-Fan where

open import Data.Bool using (true; _∧_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; map; foldr; length; replicate)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _+_; _*_; _⊔_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; natᵗ; ofᵉ; mapᵉ; mergeAllᵉ; strmᵗ;
  nat̂; input; syncSizeᵉ)
open import Rx.Prim using (gasPad; g0; cold; after_,_)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Evaluator using (Sched; EvalSt; subscribeE; sched-init;
  st-init; root; sched-next; cascadeLatch; chainStep; chainsOf)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Measures using (pathLen)

Γ₃ : Ctx 3
Γ₃ = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

-- one `mergeAllᵉ` over the source: the flatten is what makes a hop
-- REGISTER, so a branch writes to the registry rather than merely
-- passing a value along
feed : Closed Γ₃ natᵗ → Closed Γ₃ natᵗ
feed src = mergeAllᵉ nothing (mapᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ []))) src)

-- `w` independent subscriptions of the same source, merged.  `ofᵉ`
-- emits its terms inside the subscribe frame, so all `w` branches are
-- registered before any arrival is scheduled.
fan : ℕ → Closed Γ₃ natᵗ → Closed Γ₃ natᵗ
fan w src = mergeAllᵉ nothing (ofᵉ (replicate w (strmᵗ (feed src))))

slots : Slots Γ₃
-- ASYNC and TWO VALUES, for the reasons the telescope probe records:
-- a sync emission never becomes a scheduled arrival, and on a source's
-- LAST value `shareFinish` sweeps the share's registrations so the
-- registry shrinks and a growth bound holds whatever the fan did.
slots fzero               = scripted (cold [] ((after 0 , 7) ∷ (after 0 , 8) ∷ []))
slots (fsuc fzero)        = shared (feed (input fzero))
slots (fsuc (fsuc fzero)) = shared (fan 2 (input (fsuc fzero)))

sucG : Closed Γ₃ natᵗ → ℕ
sucG e = suc (syncSizeᵉ e + hopDᵉ 0 (slotHop 0 slots) e)

sub : (e : Closed Γ₃ natᵗ) → Sched Γ₃ × EvalSt e
sub e = let r = subscribeE (gasPad (sucG e) g0) e root 0 0
                           (sched-init e slots) (st-init e)
        in proj₁ (proj₂ r) , proj₂ (proj₂ r)

maxLenOf : (e : Closed Γ₃ natᵗ) → EvalSt e → ℕ
maxLenOf e st = foldr _⊔_ 0
  (map (λ en → pathLen (proj₂ (proj₂ (proj₂ en)))) (EvalSt.registry st))

-- the program is the PARAMETER here rather than an index into a family,
-- which is what lets one row function serve both the width sweep and
-- the width-meets-depth row without a transport
row : (e : Closed Γ₃ natᵗ) → ℕ × ℕ × ℕ × ℕ × ℕ
row e with sched-next (proj₁ (sub e))
... | inj₁ _        = 0 , 0 , 0 , 0 , 0
... | inj₂ (a , sd) with chainsOf a (proj₂ (sub e))
...   | []            = 0 , 0 , 0 , 0 , 0
...   | (rid , c) ∷ _ =
        let st₀ = cascadeLatch a (proj₂ (sub e))
            r   = chainStep 1 a c sd st₀
        in maxLenOf e st₀ , maxLenOf e (proj₂ (proj₂ r))
         , length (EvalSt.registry st₀)
         , length (EvalSt.registry (proj₂ (proj₂ r)))
         , length (proj₁ r)

-- WHICH ARM EACH ROW IS TAKEN ON, so a row cannot read as covered
-- while the program never reached a real `chainStep`
stage : Closed Γ₃ natᵗ → ℕ
stage e with sched-next (proj₁ (sub e))
... | inj₁ _        = 1
... | inj₂ (a , sd) with chainsOf a (proj₂ (sub e))
...   | []          = 2
...   | _ ∷ _       = 3

lenBefore : Closed Γ₃ natᵗ → ℕ
lenBefore e = proj₁ (row e)
lenAfter : Closed Γ₃ natᵗ → ℕ
lenAfter e = proj₁ (proj₂ (row e))
regsBefore : Closed Γ₃ natᵗ → ℕ
regsBefore e = proj₁ (proj₂ (proj₂ (row e)))
regsAfter : Closed Γ₃ natᵗ → ℕ
regsAfter e = proj₁ (proj₂ (proj₂ (proj₂ (row e))))

-- one emit per share boundary crossed plus one per chain bottomed out,
-- so this is what says the fan was FANNED rather than merely built
emits : Closed Γ₃ natᵗ → ℕ
emits e = proj₂ (proj₂ (proj₂ (proj₂ (row e))))

-- `w₁` is the relay case the two earlier sweeps already measure, kept
-- as the control the width reading is taken against
w₁ w₂ w₃ w₄ : Closed Γ₃ natᵗ
w₁ = fan 1 (input (fsuc fzero))
w₂ = fan 2 (input (fsuc fzero))
w₃ = fan 3 (input (fsuc fzero))
w₄ = fan 4 (input (fsuc fzero))

-- width `w` over a share whose own def is a two-way fan
d₂ d₃ : Closed Γ₃ natᵗ
d₂ = fan 2 (input (fsuc (fsuc fzero)))
d₃ = fan 3 (input (fsuc (fsuc fzero)))

packed : Closed Γ₃ natᵗ → ℕ
packed e = lenBefore e + 100 * lenAfter e + 10000 * regsBefore e
         + 1000000 * regsAfter e + 100000000 * emits e

-- EVERY ROW ON THE CHAIN ARM: a plain sum, so no row can be carried by
-- another and a program that never reached `chainStep` shows up as a
-- wrong total rather than as a silent zero
reaches : stage w₁ + stage w₂ + stage w₃ + stage w₄
        + stage d₂ + stage d₃ ≡ 18
reaches = refl

figures₁ : packed w₁ ≡ 202020303
figures₁ = refl

figures₂ : packed w₂ ≡ 303030303
figures₂ = refl

figures₃ : packed w₃ ≡ 404040303
figures₃ = refl

figures₄ : packed w₄ ≡ 505050303
figures₄ = refl

figuresD₂ : packed d₂ ≡ 705050303
figuresD₂ = refl

figuresD₃ : packed d₃ ≡ 906060303
figuresD₃ = refl

-- WIDTH DOES NOT LENGTHEN A REGISTERED PATH, the claim the sweep is
-- here to test: the fan multiplies entries, and a bound priced on the
-- longest of them is only threatened if it multiplies their LENGTH.
flat-in-width : (lenAfter w₂ ≤ᵇ lenAfter w₁)
              ∧ (lenAfter w₃ ≤ᵇ lenAfter w₁)
              ∧ (lenAfter w₄ ≤ᵇ lenAfter w₁)
              ∧ (lenAfter d₃ ≤ᵇ lenAfter d₂) ≡ true
flat-in-width = refl
