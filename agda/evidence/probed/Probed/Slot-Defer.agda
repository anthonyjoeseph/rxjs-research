-- THE TWO SHAPES A DELIVERY COUNT READS COARSELY: A SLOT AND A DEFER.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHAT IS LEFT TO DECIDE.  `Probed.Delivery-Count` settles that a
-- synchronous delivery count is readable off the term over a fold
-- family, and leaves exactly two clauses standing on nothing.  An
-- `input` does not read the term at all — it reports an ENVIRONMENT, so
-- the reading is only as good as the environment is, and the constant
-- zero is always available to a caller.  A `deferᵉ` reads ZERO, which is
-- the one clause that lets the count survive an unfolding, and is
-- therefore also the one clause a recursion could leak through.
--
-- THE SEPARATION AND THE DOMINATION ARE THE SAME PROGRAM HERE, which is
-- what makes the fork load-bearing rather than decorative.  A single
-- reference to a shared def delivers what the def delivers: the honest
-- telescope reading says two and the run hands out two, so the row is
-- TIGHT, and the constant-zero candidate says zero at the same point and
-- is refuted by it.  For hop this was recorded as false rather than
-- coarse; a delivery count inherits the finding by the same route.
--
-- THE DEFER ROW IS MAXIMALLY TIGHT BY CONSTRUCTION.  Its program's only
-- arm is the recursive one, so the reading is zero and the row asserts
-- the subscribe burst delivers NOTHING.  Any value reaching the frame
-- through the gate fails it outright — there is no slack to absorb one —
-- which is the only way to instantiate a clause whose whole content is
-- an absence.
--
-- THE BOUNDARY.  A hot scripted input is read as zero here and no row
-- reaches one, since a hot source anchors at tick zero and a row at a
-- subscribe frame cannot tell that reading from a cold one whose script
-- is empty.  Nothing below instantiates the staged recursion past one
-- slot either: the telescope is stratified, so a second stage is the
-- same clause again, and the rows pick the stage rather than exercise
-- it.
--
-- FORK: dry-operator
module Probed.Slot-Defer where

open import Data.Bool using (true; if_then_else_)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_; _≤ᵇ_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEvent; value; InstEmit; ObservableInput;
  hot; cold)
open import Rx.Exp using (Ctx; Closed; input; ofᵉ; mergeAllᵉ; μᵉ;
  varᵉ; deferᵉ; strmᵗ; natᵗ)
open import Rx.Slots using (Slot; Slots; scripted; shared)
open import Rx.Evaluator using (Stream; subscribeE; rootWitness; root;
  sched-init; st-init)

open import Probed.Apparatus using (Separates; separates-at)
open import Probed.Delivery-Count using (dlvᵉ)
open import Probed.Descent using (Γ₀; ins₀; Γ₁; insShared; progP1; progP7)

----------------------------------------------------------------------
-- THE ENVIRONMENT THE `input` CLAUSE WAS PARAMETERISED FOR, built the
-- way `Rx.Slot-Hop` builds the hop one: a scripted slot reports what its
-- script delivers INSIDE the subscribe frame, which is a cold source's
-- sync prefix and nothing at a hot one, and a shared slot reports its
-- def's own reading at the def's own stage.  The staging is what
-- stratification buys — slot k's def reads only slots below k — and it
-- is the same recursion, so it is written the same way.
----------------------------------------------------------------------

syncOf : ∀ {A : Set} → ObservableInput A → ℕ
syncOf (hot _)       = 0
syncOf (cold sync _) = length sync

slotDlvD : ∀ {n} {Γ : Ctx n} {k t} (ν : Fin n → ℕ) → Slot Γ k t → ℕ
slotDlvD ν (scripted src) = syncOf src
slotDlvD ν (shared d)     = dlvᵉ ν d

νAt : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (k : ℕ) → Fin n → ℕ
νAt sl zero    i = 0
νAt sl (suc k) i =
  if toℕ i ≡ᵇ k then slotDlvD (νAt sl k) (sl i)
                else νAt sl k i

slotDlv : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) → Fin n → ℕ
slotDlv sl i = slotDlvD (νAt sl (toℕ i)) (sl i)

-- the candidate this replaces, and the one a caller is always free to
-- pick: zero at every slot
νZero : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) → Fin n → ℕ
νZero sl i = 0

----------------------------------------------------------------------
-- WHAT A RUN ACTUALLY HANDS OUT IN ITS SUBSCRIBE FRAME.  The reading
-- above is a claim about exactly this number, so the rows compare the
-- two directly rather than through a depth — which is what a `≤` row
-- can be tight at.
----------------------------------------------------------------------

vals : ∀ {A : Set} → List (InstEvent A) → ℕ
vals []             = 0
vals (value _ ∷ es) = 1 + vals es
vals (_ ∷ es)       = vals es

-- the element type is taken as the parameter rather than the context
-- and the type, because `Stream` unfolds through `Val`, which is not
-- injective — an inference failure and not a design choice
delivered : ∀ {A : Set} → List (InstEmit A) → ℕ
delivered []         = 0
delivered (em ∷ ems) = vals (InstEmit.events em) + delivered ems

-- the store bound the schedule and the witness are both taken at, so a
-- row is about a RUN rather than about a pair of readings
SB : ℕ
SB = 30

burstOf : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) → Stream Γ t
burstOf e ins =
  proj₁ (subscribeE (rootWitness SB e ins) e root 0 0 (sched-init SB e ins)
           (st-init e))

----------------------------------------------------------------------
-- THE SLOT.  One reference to a shared def whose own source is two
-- literals, so the def's reading is what the reference has to report.
----------------------------------------------------------------------

progS : Closed Γ₁ natᵗ
progS = mergeAllᵉ nothing (ofᵉ (strmᵗ (input fzero) ∷ []))

readAt : Slots Γ₁ → ℕ
readAt sl = dlvᵉ (slotDlv sl) progS

readZero : Slots Γ₁ → ℕ
readZero sl = dlvᵉ (νZero sl) progS

-- LOAD-BEARING: the honest reading either reaches through the telescope
-- to the def or it does not, and the constant-zero candidate is what it
-- has to differ from for the parameterisation to be buying anything.
_ : readAt insShared ≡ 2                                  -- LOAD-BEARING
_ = refl

_ : readZero insShared ≡ 0                                -- LOAD-BEARING
_ = refl

slot-fork : Separates readAt readZero
slot-fork = separates-at insShared (λ ())

-- LOAD-BEARING AND TIGHT: the run delivers exactly what the reading
-- says, so a reading one smaller would be refuted by this very row.
_ : delivered (burstOf progS insShared) ≡ 2               -- LOAD-BEARING
_ = refl

_ : (delivered (burstOf progS insShared) ≤ᵇ readAt insShared) ≡ true
_ = refl

----------------------------------------------------------------------
-- THE DEFER.  The recursive arm is the ONLY arm, so the reading is zero
-- and the row says the subscribe frame delivers nothing at all.  There
-- is no slack in it: one value through the gate fails it.
----------------------------------------------------------------------

progD : Closed Γ₀ natᵗ
progD = μᵉ (mergeAllᵉ nothing (ofᵉ (strmᵗ (deferᵉ (varᵉ (here refl))) ∷ [])))

_ : dlvᵉ (λ ()) progD ≡ 0                                 -- LOAD-BEARING
_ = refl

_ : delivered (burstOf progD ins₀) ≡ 0                    -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE TWO TOGETHER, on the programs `Probed.Descent` already runs: a
-- recursion beside a literal source, and a recursion beside a slot
-- reference.  Neither is tight, and each could still have failed — a
-- gate that leaked would put the whole unfolding's output in the frame,
-- which no margin of this size absorbs.
----------------------------------------------------------------------

_ : (delivered (burstOf progP1 ins₀) ≤ᵇ dlvᵉ (λ ()) progP1) ≡ true
_ = refl

_ : (delivered (burstOf progP7 insShared) ≤ᵇ dlvᵉ (slotDlv insShared) progP7)
      ≡ true
_ = refl
