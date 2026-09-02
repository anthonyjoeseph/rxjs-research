-- THE SIDEWAYS RE-ENTRY, WHICH THE ROOTWARD SWEEP COULD NOT SEE.
-- `foldPath` bottoms out two ways.  Rootward, through `f ↠ path′`, it
-- steps one frame at a time and `Probed.Chain-Step-Regs-Level` walks
-- that stack out to depth eight.  Sideways, at a `share-sink i`, it
-- calls `dispatchShare`, which folds every chain registered on share
-- `i` -- and those chains may themselves sink into a LATER share.  So
-- one `chainStep` can cross the whole telescope, while the statement
-- it is evidence about licenses ONE level step for the whole call.

-- THE TELESCOPE IS THE DEPTH, NOT THE SYNTAX, which is why a program
-- over the two-slot context cannot reach this at all.  A share's def
-- may name only inputs strictly below its own index, so a chain
-- sinking into share `i` and out through share `i′` needs `i < i′`
-- and a share nesting of depth d needs d+1 slots.  The family here is
-- ONE five-slot context whose slot zero is scripted and whose slots
-- one to four are each a `mergeAllᵉ` over the slot below; the four
-- programs root at slots one to four, so a single scripted arrival
-- crosses one, two, three and four share boundaries inside one
-- `chainStep`.  Slots above the root simply never connect.

-- AND THE ARRANGEMENT IS FORCED, NOT CHOSEN.  A share at index zero
-- has a def nothing can arrive into, so its fan-out happens once
-- inside the connect burst and no DELIVERY ever reaches its sink --
-- which is why every family built over the two-slot context is silent
-- here whatever it sweeps.  `Refuted.Share-Sink-Nodes` established
-- that, on the nest measure, and it is the same vocabulary fact.  So
-- the scripted driver goes at index zero and every share above it.

-- WHAT COULD REFUTE, and it is the registered length alone.  The
-- statement prices a registry by `pathSz?`, whose only unbounded
-- conjunct is `suc (pathLen p) ≤ B` at every frame, and one level
-- step takes B to `S * suc (2 * B)`.  So a refutation needs the max
-- registered length after the step to outrun that, and the axis that
-- could deliver it is the number of share hops -- the one axis this
-- family moves and the rootward sweep held at zero.

-- TARGET: foldPath-regsLen @68fc23
module Probed.Chain-Step-Regs-Share where

open import Data.Bool using (true; _∧_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_; map; foldr; length)
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

-- FIVE SLOTS, ONE SCRIPTED DRIVER AND FOUR SHARES IN A STRICT CHAIN.
-- Every slot is `natᵗ`, so `lookup` reduces at every concrete index
-- and the stratification side condition discharges by unification.
Γ₅ : Ctx 5
Γ₅ = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

-- one `mergeAllᵉ` over the source below: the flatten is what makes the
-- hop REGISTER, so each crossing writes to the registry rather than
-- merely passing a value along.  It takes the SOURCE rather than its
-- index because `lookup Γ₅ i` does not reduce under a variable `i`.
feed : Closed Γ₅ natᵗ → Closed Γ₅ natᵗ
feed src = mergeAllᵉ nothing (mapᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ []))) src)

slots : Slots Γ₅
-- ASYNC, not sync: a sync emission is delivered inside the subscribe
-- frame and never appears as a scheduled arrival, so the rows would
-- be taken on the no-arrival arm.
--
-- AND TWO VALUES, NOT ONE, WHICH IS WHAT MAKES THE ROWS ABLE TO FAIL.
-- On a source's LAST value the fan-out latches the share and
-- `shareFinish` sweeps every registration it owned, so the registry
-- after the step is SMALLER than before and a growth bound holds
-- whatever the hops did.  Measured at one value: the count went two
-- to one across the step.  A second value keeps `isLast` false, so
-- the step is a live fan-out and the bound is being asked something.
slots fzero = scripted (cold [] ((after 0 , 7) ∷ (after 0 , 8) ∷ []))
slots (fsuc fzero)                      = shared (feed (input fzero))
slots (fsuc (fsuc fzero))               = shared (feed (input (fsuc fzero)))
slots (fsuc (fsuc (fsuc fzero)))        = shared (feed (input (fsuc (fsuc fzero))))
slots (fsuc (fsuc (fsuc (fsuc fzero)))) =
  shared (feed (input (fsuc (fsuc (fsuc fzero)))))

-- the root reads share `d`, so an arrival at slot zero crosses
-- exactly `d` share boundaries on its way out
progS : Fin 5 → Closed Γ₅ natᵗ
progS fzero                             = feed (input fzero)
progS (fsuc fzero)                      = feed (input (fsuc fzero))
progS (fsuc (fsuc fzero))               = feed (input (fsuc (fsuc fzero)))
progS (fsuc (fsuc (fsuc fzero)))        = feed (input (fsuc (fsuc (fsuc fzero))))
progS (fsuc (fsuc (fsuc (fsuc fzero)))) =
  feed (input (fsuc (fsuc (fsuc (fsuc fzero)))))

sucGS : Fin 5 → ℕ
sucGS d = suc (syncSizeᵉ (progS d) + hopDᵉ 0 (slotHop 0 slots) (progS d))

sub : (d : Fin 5) → Sched Γ₅ × EvalSt (progS d)
sub d = let r = subscribeE (gasPad (sucGS d) g0) (progS d) root 0 0
                           (sched-init (progS d) slots) (st-init (progS d))
        in proj₁ (proj₂ r) , proj₂ (proj₂ r)

-- `d` is EXPLICIT for the same reason `k` was in the rootward probe:
-- `progS` is not injective as far as the unifier is concerned, so an
-- implicit here has nothing to solve it from.
maxLen : ∀ (d : Fin 5) → EvalSt (progS d) → ℕ
maxLen d st = foldr _⊔_ 0
  (map (λ en → pathLen (proj₂ (proj₂ (proj₂ en)))) (EvalSt.registry st))

regCount : ∀ (d : Fin 5) → EvalSt (progS d) → ℕ
regCount d st = length (EvalSt.registry st)

row : (d : Fin 5) → ℕ × ℕ × ℕ × ℕ × ℕ
row d with sched-next (proj₁ (sub d))
... | inj₁ _        = 0 , 0 , 0 , 0 , 0
... | inj₂ (a , sd) with chainsOf a (proj₂ (sub d))
...   | []            = 0 , 0 , 0 , 0 , 0
...   | (rid , c) ∷ _ =
        let st₀ = cascadeLatch a (proj₂ (sub d))
            r   = chainStep 1 a c sd st₀
        in maxLen d st₀ , maxLen d (proj₂ (proj₂ r))
         , regCount d st₀ , regCount d (proj₂ (proj₂ r))
         , length (proj₁ r)

-- WHICH ARM EACH ROW IS TAKEN ON, so a row cannot read as covered
-- while the program never reached a real `chainStep`
stage : Fin 5 → ℕ
stage d with sched-next (proj₁ (sub d))
... | inj₁ _        = 1
... | inj₂ (a , sd) with chainsOf a (proj₂ (sub d))
...   | []          = 2
...   | _ ∷ _       = 3

lenBefore : Fin 5 → ℕ
lenBefore d = proj₁ (row d)
lenAfter : Fin 5 → ℕ
lenAfter d = proj₁ (proj₂ (row d))
regsBefore : Fin 5 → ℕ
regsBefore d = proj₁ (proj₂ (proj₂ (row d)))
regsAfter : Fin 5 → ℕ
regsAfter d = proj₁ (proj₂ (proj₂ (proj₂ (row d))))

-- WHAT SAYS THE STEP WENT SIDEWAYS AT ALL, and without it the length
-- rows below cannot be read.  `foldPath` writes one `handoff` emit at
-- every `share-sink` it reaches and one delivery envelope where it
-- bottoms out, so with one chain registered per share the emit count
-- of a single `chainStep` is the crossings plus one -- a direct count
-- of the boundaries that step went through.  A count that did not
-- move with `d` would mean the telescope was built and never entered,
-- and every flat length reading below would be about nothing.
emits : Fin 5 → ℕ
emits d = proj₂ (proj₂ (proj₂ (proj₂ (row d))))

-- `d₀` roots at the SCRIPTED slot, so its delivery crosses no share
-- at all: it is the control the per-hop reading is measured against,
-- and without it "one per hop" has no zero to start from.
d₀ d₁ d₂ d₃ d₄ : Fin 5
d₀ = fzero
d₁ = fsuc fzero
d₂ = fsuc (fsuc fzero)
d₃ = fsuc (fsuc (fsuc fzero))
d₄ = fsuc (fsuc (fsuc (fsuc fzero)))

packed : Fin 5 → ℕ
packed d = lenBefore d + 100 * lenAfter d + 10000 * regsBefore d
         + 1000000 * regsAfter d + 100000000 * emits d

-- EVERY ROW ON THE CHAIN ARM: a plain sum, so no row can be carried
-- by another and a program that never reached `chainStep` shows up
-- as a wrong total rather than as a silent zero
reaches : stage d₀ + stage d₁ + stage d₂ + stage d₃ + stage d₄ ≡ 15
reaches = refl

figures₀ : packed d₀ ≡ 101010202
figures₀ = refl

figures₁ : packed d₁ ≡ 202020202
figures₁ = refl

figures₂ : packed d₂ ≡ 303030202
figures₂ = refl

figures₃ : packed d₃ ≡ 404040202
figures₃ = refl

figures₄ : packed d₄ ≡ 505050202
figures₄ = refl

-- ONE REGISTERED FRAME PER CROSSING, the claim the sweep is here to
-- test: the depth axis is the only one moving, so a failure is a
-- refutation of per-hop linearity and nothing else.
one-per-hop : (lenAfter d₀ ≤ᵇ lenBefore d₀ + 0)
            ∧ (lenAfter d₁ ≤ᵇ lenBefore d₁ + 1)
            ∧ (lenAfter d₂ ≤ᵇ lenBefore d₂ + 2)
            ∧ (lenAfter d₃ ≤ᵇ lenBefore d₃ + 3)
            ∧ (lenAfter d₄ ≤ᵇ lenBefore d₄ + 4) ≡ true
one-per-hop = refl
