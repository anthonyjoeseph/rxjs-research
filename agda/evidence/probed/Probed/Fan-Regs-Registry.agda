-- WHAT A RUN ACTUALLY REGISTERS, which is the question the statement
-- was stated over an arbitrary state to avoid asking.
-- `Refuted.Fan-Chain-Registry` kills the unconditional form at a
-- single `register` onto the initial state, so what is left open is
-- whether it holds of a registry a RUN produced -- and that is a
-- different question, because a run only ever registers chains built
-- out of the program's own frames, while the refutation's witness was
-- minted from a term the program does not contain.
--
-- TARGET: fan-regsNest @232560

-- TWO AXES, BECAUSE THE STATEMENT HAS TWO SIDES THAT COULD MOVE.  The
-- conclusion compares a registered chain's `pathNestD` against
-- `nestUnit e sl`, which reads the ROOT program's nesting and every
-- slot's.  So a family that deepens the SHARES moves both sides at
-- once and says little; a family that deepens the program ABOVE the
-- share moves the chain's reading against a unit that grows for a
-- different reason, and that is where the margin can close.  Both are
-- swept here, five rungs each.

-- THE SHARE TELESCOPE IS THE COUNT AXIS.  One five-slot context: slot
-- zero scripted, slots one to four each a `mergeAllᵉ` over the slot
-- below, and the roots read shares zero to four -- so a run at `d`
-- connects `d` shares and writes one registration per crossing.  A
-- share's def may name only inputs strictly below its index, so depth
-- `d` needs `d+1` slots and the arrangement is forced rather than
-- chosen.  What it moves is how MANY chains the fan-out is handed.

-- THE NESTING LADDER IS THE TIGHT AXIS, AND IT IS THE ONE THAT COULD
-- HAVE FAILED.  Two slots, one share, and a root that wraps the share
-- in `k` further flatten layers.  Each rung adds one `thru-outer` to
-- the registered chain and one layer to the program, so the chain's
-- depth and the syntactic unit climb together -- measured at `k+1`
-- against `k+3`, a CONSTANT margin of two that neither closes nor
-- opens across the sweep.  A mint that attributed one frame to the
-- wrong side would have shown up as that margin shrinking rung by
-- rung, which is exactly what a five-rung ladder is for.

-- AND THE LENGTH READING IS A FINDING ABOUT THE SIZE SIDE, NOT A ROW
-- ABOUT IT.  The registered chain's LENGTH climbs two per rung, so a
-- registry is size-legal only against a cap that grows with the
-- program's own syntax; a fixed bound is outrun by the fourth rung.
-- That constrains where a size receipt can come from, and it is
-- recorded at the statement it constrains rather than claimed here.

-- NOT COVERED: a share whose def nests more deeply than its consumer,
-- which would move the unit's slot summand against a flat chain and
-- is the mirror of the ladder swept here; and the size conjunct at
-- its real cap, since `capsAt` returns at no program -- the boundary
-- `Refuted.Fan-Chain-Registry` already records.
module Probed.Fan-Regs-Registry where

open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_; map; foldr; length)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; natᵗ; ofᵉ; mapᵉ; mergeAllᵉ; strmᵗ;
  nat̂; input; syncSizeᵉ)
open import Rx.Prim using (gasPad; g0; cold; after_,_)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Evaluator using (Sched; EvalSt; subscribeE; sched-init;
  st-init; root)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Measures using (pathLen)
open import Verify-Budget-Sufficient.Nest-Store using (pathNestD; nestUnit)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Depth-Fit using (fan-regsNest)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- AXIS ONE: THE SHARE TELESCOPE
----------------------------------------------------------------------
Γ₅ : Ctx 5
Γ₅ = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

-- one `mergeAllᵉ` over the source below: the flatten is what makes the
-- hop REGISTER, so each crossing writes to the registry rather than
-- merely passing a value along
feed : Closed Γ₅ natᵗ → Closed Γ₅ natᵗ
feed src = mergeAllᵉ nothing (mapᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ []))) src)

-- ASYNC, and two values rather than one: a sync emission is delivered
-- inside the subscribe frame, and on a source's LAST value the
-- fan-out latches the share and sweeps its registrations away
slots : Slots Γ₅
slots fzero = scripted (cold [] ((after 0 , 7) ∷ (after 0 , 8) ∷ []))
slots (fsuc fzero)                      = shared (feed (input fzero))
slots (fsuc (fsuc fzero))               = shared (feed (input (fsuc fzero)))
slots (fsuc (fsuc (fsuc fzero)))        = shared (feed (input (fsuc (fsuc fzero))))
slots (fsuc (fsuc (fsuc (fsuc fzero)))) =
  shared (feed (input (fsuc (fsuc (fsuc fzero)))))

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

-- `d` is EXPLICIT because `progS` is not injective as far as the
-- unifier is concerned, so an implicit has nothing to solve it from
regCount : ∀ (d : Fin 5) → EvalSt (progS d) → ℕ
regCount d st = length (EvalSt.registry st)

d₀ d₁ d₂ d₃ d₄ : Fin 5
d₀ = fzero
d₁ = fsuc fzero
d₂ = fsuc (fsuc fzero)
d₃ = fsuc (fsuc (fsuc fzero))
d₄ = fsuc (fsuc (fsuc (fsuc fzero)))

-- WHAT SAYS THE TELESCOPE WAS ENTERED AT ALL, and without it every
-- `held` row below would be `all` over a list that never grew.  One
-- registration per crossing plus the root's own, read as a ladder so
-- a run that connected nothing shows up as a wrong total rather than
-- as a silently satisfied quantifier.
counts : regCount d₀ (proj₂ (sub d₀)) + 10 * regCount d₁ (proj₂ (sub d₁))
       + 100 * regCount d₂ (proj₂ (sub d₂)) + 1000 * regCount d₃ (proj₂ (sub d₃))
       + 10000 * regCount d₄ (proj₂ (sub d₄)) ≡ 54321
counts = refl

-- LOAD-BEARING, on the count axis: five distinct reachable registries,
-- the largest holding five chains, every one of them under the unit.
-- It fails the moment a crossing mints a chain the program's own
-- nesting does not bound.  The claim is the statement's own, at each
-- rung -- `Confirms` returns the applied postulate's type, so this
-- file chooses the point and nothing else.
regsS : (d : Fin 5) → Confirms (fan-regsNest slots (proj₂ (sub d)))
regsS fzero                             = refl
regsS (fsuc fzero)                      = refl
regsS (fsuc (fsuc fzero))               = refl
regsS (fsuc (fsuc (fsuc fzero)))        = refl
regsS (fsuc (fsuc (fsuc (fsuc fzero)))) = refl

----------------------------------------------------------------------
-- AXIS TWO: NESTING ABOVE THE SHARE
----------------------------------------------------------------------
Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

feed₂ : Closed Γ₂ natᵗ → Closed Γ₂ natᵗ
feed₂ src = mergeAllᵉ nothing (mapᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ []))) src)

slots₂ : Slots Γ₂
slots₂ fzero        = scripted (cold [] ((after 0 , 7) ∷ (after 0 , 8) ∷ []))
slots₂ (fsuc fzero) = shared (feed₂ (input fzero))

-- `k` flatten layers ABOVE the share, so each rung adds one frame to
-- the registered chain and one layer to the program
progK : ℕ → Closed Γ₂ natᵗ
progK zero    = feed₂ (input (fsuc fzero))
progK (suc k) = feed₂ (progK k)

sucGK : ℕ → ℕ
sucGK k = suc (syncSizeᵉ (progK k) + hopDᵉ 0 (slotHop 0 slots₂) (progK k))

subK : (k : ℕ) → Sched Γ₂ × EvalSt (progK k)
subK k = let r = subscribeE (gasPad (sucGK k) g0) (progK k) root 0 0
                            (sched-init (progK k) slots₂) (st-init (progK k))
         in proj₁ (proj₂ r) , proj₂ (proj₂ r)

maxNestK : ∀ (k : ℕ) → EvalSt (progK k) → ℕ
maxNestK k st = foldr _⊔_ 0
  (map (λ en → pathNestD (proj₂ (proj₂ (proj₂ en)))) (EvalSt.registry st))

maxLenK : ∀ (k : ℕ) → EvalSt (progK k) → ℕ
maxLenK k st = foldr _⊔_ 0
  (map (λ en → pathLen (proj₂ (proj₂ (proj₂ en)))) (EvalSt.registry st))

unitK : ℕ → ℕ
unitK k = nestUnit (progK k) slots₂

-- LOAD-BEARING, AND THE MARGIN IS THE ROW.  Reading the two sides as
-- exact numerals rather than as an inequality is what makes a closing
-- margin visible: `heldK` alone would stay green all the way to the
-- rung where it flips, and by then the ladder is over.  Measured
-- `k+1` against `k+3` at every rung -- so the gap is constant, and a
-- frame attributed to the chain but not to the unit would show here
-- as the second column failing to keep up.
marginK : maxNestK 0 (proj₂ (subK 0)) + 100 * unitK 0
        + 10000 * maxNestK 1 (proj₂ (subK 1)) + 1000000 * unitK 1
        + 100000000 * maxNestK 2 (proj₂ (subK 2)) + 10000000000 * unitK 2
        ≡ 50304020301
marginK = refl

marginK′ : maxNestK 3 (proj₂ (subK 3)) + 100 * unitK 3
         + 10000 * maxNestK 4 (proj₂ (subK 4)) + 1000000 * unitK 4
         ≡ 7050604
marginK′ = refl

-- LOAD-BEARING, on the axis the two sides actually race on
regsK : (k : Fin 5) → Confirms (fan-regsNest slots₂ (proj₂ (subK (toℕ k))))
regsK fzero                             = refl
regsK (fsuc fzero)                      = refl
regsK (fsuc (fsuc fzero))               = refl
regsK (fsuc (fsuc (fsuc fzero)))        = refl
regsK (fsuc (fsuc (fsuc (fsuc fzero)))) = refl

-- THE SIZE SIDE, READ AND NOT CLAIMED.  Two frames per rung, against
-- a unit that climbs by one -- so the length is the quantity a cap
-- has to grow with, and the finding is recorded at the statement that
-- owes it rather than as a receipt here.
lensK : maxLenK 0 (proj₂ (subK 0)) + 100 * maxLenK 1 (proj₂ (subK 1))
      + 10000 * maxLenK 2 (proj₂ (subK 2)) + 1000000 * maxLenK 3 (proj₂ (subK 3))
      + 100000000 * maxLenK 4 (proj₂ (subK 4)) ≡ 1008060402
lensK = refl
