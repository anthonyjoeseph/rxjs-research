-- ══════════════════════════════════════════════════════════════════
-- ONE FRAME'S SIZE STEP DOES NOT COST ONE LEVEL, and the second
-- witness is the expensive half: it kills the repair, not the
-- statement.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAID.  The values a frame EMITS are priced at one
-- `iterSize` level above the values it RECEIVED, whatever the frame
-- does.  It is the size sibling of the registry face, and a walk
-- threading both was to spend one level per frame rather than one
-- each.
--
-- WHERE THE FIRST ONE BREAKS, and it is the shape CLAUDE.md calls
-- almost always wrong: the conclusion needs information NO hypothesis
-- carries.  A `map-f` emits `applyFn fn v`, and nothing in the
-- statement bounds `fn` -- not the arriving values' reading, which is
-- about `v`, and not the path, which is not a premise at all.  So the
-- frame is free and one level is beaten by inspection.
--
-- WHERE THE SECOND ONE BREAKS, WHICH IS THE FINDING.  Add every bound
-- the fold has to hand -- the frame's own `frameSz?`, the path's, the
-- values' -- and the statement is STILL false, because `applyFn`
-- DUPLICATES.  `evalWith (pairᵗ a b) env` evaluates `env` into both
-- arms, so a pair tree of `k` leaves at size `2k-1` takes a value of
-- size `V` to `(k-1) + k·V`.  With both `k` and `V` capped at the
-- level `L`, the emission is quadratic in `L`; one level buys
-- `sizeStep S L = S·(1+2L)`, which is LINEAR in `L`.  Quadratic beats
-- linear as soon as `L` outruns the cap it was iterated from, which is
-- at `j = 1` for every `S ≥ 2`.
--
-- WHAT THIS LEAVES.  Not "one level is too few" -- no FIXED number of
-- levels is enough, since the crossing moves with `j`.  What survives
-- is the shape the proven caps face already uses: report an
-- EXISTENTIAL growth index and land the post-state at `j + j′`
-- (`stepFrame-caps` in `.Subscribe-Face`, which reports exactly that
-- and is ground).  The registry sibling can ride that level unchanged,
-- since `regsSz?` widens with the cap and `iterSize` is monotone in
-- the count.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Frame-Step-Size-Level where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc; _≤_; s≤s; z≤n)
open import Data.Product using (proj₁; _,_)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Gas; g0; hot; Tick; Id)
open import Rx.Exp using (Ctx; Ty; Closed; Val; Fn; natᵗ; _×ᵗ_; emptyᵉ;
  varᵗ; pairᵗ; sizeᵗ; sizeᵛ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (Sched; EvalSt; Frame; map-f; Path; root;
  stepFrame; sched-init; st-init; iterSize)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (pathSz?; frameSz?)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?)

----------------------------------------------------------------------
-- THE TWO STATEMENTS, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulate would prove the tower inconsistent instead of refuting
-- anything.  The second is the first plus every bound the fold that
-- consumes it actually holds.
----------------------------------------------------------------------
StepFrameSz : Set
StepFrameSz = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (path : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
  (S j : ℕ) →
  valsSz? (iterSize S j S) vals ≡ true →
  valsSz? (iterSize S (suc j) S)
    (proj₁ (stepFrame sf id now f path vals fin sched st)) ≡ true

StepFrameSzFramed : Set
StepFrameSzFramed = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (path : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
  (S j : ℕ) →
  1 ≤ S →
  frameSz? (iterSize S j S) f ≡ true →
  pathSz? (iterSize S j S) path ≡ true →
  valsSz? (iterSize S j S) vals ≡ true →
  valsSz? (iterSize S (suc j) S)
    (proj₁ (stepFrame sf id now f path vals fin sched st)) ≡ true

f≡t : false ≡ true → ⊥
f≡t ()

----------------------------------------------------------------------
-- ONE SLOT, and it is never consulted: a `map-f` frame reads no state
-- and returns the state it was handed, so the whole witness is the
-- FUNCTION and the value it is applied to.
----------------------------------------------------------------------
Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

sl₁ : Slots Γ₁
sl₁ fzero = scripted (hot [])

----------------------------------------------------------------------
-- WITNESS ONE — the frame is unbounded, so the level is beaten by
-- inspection.  `S = 1`, `j = 0`: the level in hand is `1` and one step
-- buys `sizeStep 1 1 = 3`.  A three-leaf duplicator takes the arriving
-- `0` (size 1, so the premise holds) to `(0 , (0 , 0))` at size 5.
----------------------------------------------------------------------
U₃ : Ty
U₃ = natᵗ ×ᵗ (natᵗ ×ᵗ natᵗ)

fnA : Fn Γ₁ [] [] [] natᵗ U₃
fnA = pairᵗ (varᵗ (here refl)) (pairᵗ (varᵗ (here refl)) (varᵗ (here refl)))

eA : Closed Γ₁ U₃
eA = emptyᵉ

valsA : List (Val Γ₁ natᵗ)
valsA = 0 ∷ []

outA : List (Val Γ₁ U₃)
outA = proj₁ (stepFrame {e = eA} g0 0 0 (map-f fnA) root valsA false
                        (sched-init eA sl₁) (st-init eA))

-- LOAD-BEARING FIGURES.  The premise's level, the level one step buys,
-- and the size the emission actually reaches.  Any of the three moving
-- fails this line by name.
figuresA : List ℕ
figuresA = iterSize 1 0 1 ∷ iterSize 1 1 1 ∷ sizeᵗ fnA ∷ sizeᵛ {Γ = Γ₁} U₃ (0 , (0 , 0)) ∷ []

figuresA≡ : figuresA ≡ 1 ∷ 3 ∷ 5 ∷ 5 ∷ []
figuresA≡ = refl

rowA : Bool
rowA = valsSz? {Γ = Γ₁} {s = U₃} (iterSize 1 1 1) outA

rowA≡false : rowA ≡ false
rowA≡false = refl

stepFrame-sz-absurd : StepFrameSz → ⊥
stepFrame-sz-absurd pr =
  f≡t (trans (sym rowA≡false)
             (pr {e = eA} g0 0 0 (map-f fnA) root valsA false
                 (sched-init eA sl₁) (st-init eA) 1 0 refl))

----------------------------------------------------------------------
-- WITNESS TWO — every bound the fold holds is supplied and the
-- statement still fails, because the duplication is a PRODUCT of two
-- quantities the level caps separately.  `S = 2`, `j = 1`: the level
-- in hand is `10` and one step buys `sizeStep 2 10 = 42`.  A five-leaf
-- duplicator has size 9, inside the frame's own cap of 10; the
-- arriving value has size 9, inside the values' cap of 10; and the
-- emission is `4 + 5·9 = 49`.
----------------------------------------------------------------------
P₅ : Ty
P₅ = natᵗ ×ᵗ (natᵗ ×ᵗ (natᵗ ×ᵗ (natᵗ ×ᵗ natᵗ)))

U₅ : Ty
U₅ = P₅ ×ᵗ (P₅ ×ᵗ (P₅ ×ᵗ (P₅ ×ᵗ P₅)))

fnB : Fn Γ₁ [] [] [] P₅ U₅
fnB = pairᵗ (varᵗ (here refl))
        (pairᵗ (varᵗ (here refl))
          (pairᵗ (varᵗ (here refl))
            (pairᵗ (varᵗ (here refl)) (varᵗ (here refl)))))

vB : Val Γ₁ P₅
vB = 0 , (0 , (0 , (0 , 0)))

eB : Closed Γ₁ U₅
eB = emptyᵉ

valsB : List (Val Γ₁ P₅)
valsB = vB ∷ []

outB : List (Val Γ₁ U₅)
outB = proj₁ (stepFrame {e = eB} g0 0 0 (map-f fnB) root valsB false
                        (sched-init eB sl₁) (st-init eB))

-- LOAD-BEARING FIGURES.  Both caps are read at the SAME level and both
-- are respected with room; the emission is what crosses.
figuresB : List ℕ
figuresB = iterSize 2 1 2 ∷ iterSize 2 2 2 ∷ sizeᵗ fnB ∷ sizeᵛ {Γ = Γ₁} P₅ vB ∷ []

figuresB≡ : figuresB ≡ 10 ∷ 42 ∷ 9 ∷ 9 ∷ []
figuresB≡ = refl

-- THE PREMISES HOLD, spelled out so the witness cannot be read as one
-- that merely fails to satisfy them.
premA : frameSz? {Γ = Γ₁} (iterSize 2 1 2) (map-f fnB) ≡ true
premA = refl

premB : pathSz? (iterSize 2 1 2) (root {Γ = Γ₁} {t = U₅}) ≡ true
premB = refl

premC : valsSz? {Γ = Γ₁} {s = P₅} (iterSize 2 1 2) valsB ≡ true
premC = refl

rowB : Bool
rowB = valsSz? {Γ = Γ₁} {s = U₅} (iterSize 2 2 2) outB

rowB≡false : rowB ≡ false
rowB≡false = refl

stepFrame-sz-framed-absurd : StepFrameSzFramed → ⊥
stepFrame-sz-framed-absurd pr =
  f≡t (trans (sym rowB≡false)
             (pr {e = eB} g0 0 0 (map-f fnB) root valsB false
                 (sched-init eB sl₁) (st-init eB) 2 1
                 (s≤s z≤n) premA premB premC))
