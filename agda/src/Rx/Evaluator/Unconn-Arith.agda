------------------------------------------------------------------
-- THE UNCONNECTED COUNT, AND NOTHING ELSE.
------------------------------------------------------------------

-- WHAT LIVES HERE AND WHY IT IS ITS OWN MODULE.  The count reads no
-- program: it tabulates the slot table and adds one for every SHARED
-- slot whose index the connected set does not hold, so every fact
-- about it is a fact about a list gaining an element.  It sits above
-- `Rx.Evaluator` rather than in it because its only consumer is the
-- reducibility candidate, and a four-line arithmetic fact placed at
-- the bottom would invalidate the evaluator's whole cone to buy
-- nothing.

-- WHAT IT IS FOR.  The fan-out's cycle closes through a connect, and
-- this is the quantity that cycle descends on: the connect is the one
-- edge that moves it, it moves it strictly DOWN, and nothing anywhere
-- moves it up.

-- AND THE STRICT FORM CARRIES THE SLOT'S OWN SHAPE, WHICH IS WHAT THE
-- MEMBERSHIP PREMISE ALONE COULD NOT SAY.  Only a `shared` slot ever
-- reads one, and it reads one only while the set is without it, so
-- both branches have to be in hand before the index can be said to
-- fall.  Stated with membership alone the claim is FALSE, and a table
-- of one scripted slot is the witness.

-- THE ANTITONE FORM TAKES MEMBERSHIP-PRESERVATION RATHER THAN A CONS,
-- WHICH IS WHAT MAKES IT USABLE ACROSS A WHOLE SUB-RUN.  A step of the
-- evaluator does not cons once; it hands back a set reached by some
-- number of connects, and what the step's own induction can carry is
-- that whatever was a member still is.  That premise is exactly this
-- one, and the cons form is the special case.

-- REFUTED: `Refuted.Scripted-Connect`, deleted at 104d61de and read
--   with `git show 104d61de^:agda/evidence/refuted/Refuted/Scripted-Connect.agda`
--   -- the membership-only form, at the smallest table there is.

-- RECOVERY: git show 2f40824d:agda/src/Verify-Budget-Sufficient/Measures.agda
--   is where every statement below but the last was proven before, and
--   `git show 2f40824d:agda/src/Verify-Budget-Sufficient/Keeps-Ring.agda`
--   is the state relation that feeds the antitone one.
-- RECOVERY: git show 3abdafa1:agda/src/Rx/Evaluator/Unconn-Arith.agda
--   holds the strict fall at a connect (`unconn-insert`, over
--   `sum-tab-strict` and `unconnAt-cons-≤`), which the connect arm
--   spends.
module Rx.Evaluator.Unconn-Arith where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; _∷_; tabulate)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-<-trans; +-mono-≤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx)
open import Rx.Prim using (Source)
open import Rx.Slots using (Slots; shared; scripted)
open import Rx.Evaluator using (memberSource; sameSource)

-- ONE SLOT'S CONTRIBUTION.  A scripted slot has no definition to
-- subscribe, so connecting it is not an operation and it never counts;
-- a shared one counts until its own index joins the set.
unconnAt : ∀ {n} {Γ : Ctx n} → Slots Γ → List Source → Fin n → ℕ
unconnAt sl cs i with sl i
... | shared _   = if memberSource (toℕ i) cs then 0 else 1
... | scripted _ = 0

unconn : ∀ {n} {Γ : Ctx n} → Slots Γ → List Source → ℕ
unconn sl cs = sum (tabulate (unconnAt sl cs))

-- pointwise sums over the telescope
sum-tab-mono : ∀ {m} (f g : Fin m → ℕ) → (∀ i → f i ≤ g i) →
  sum (tabulate f) ≤ sum (tabulate g)
sum-tab-mono {zero}  f g h = z≤n
sum-tab-mono {suc m} f g h =
  +-mono-≤ (h fzero) (sum-tab-mono _ _ (λ i → h (fsuc i)))

-- KEEPING A MEMBER NEVER RAISES A SLOT'S CONTRIBUTION EITHER, and this
-- is the form a sub-run's induction can hand over.
unconnAt-antitone : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs cs′ : List Source)
  (i : Fin n) →
  (memberSource (toℕ i) cs ≡ true → memberSource (toℕ i) cs′ ≡ true) →
  unconnAt sl cs′ i ≤ unconnAt sl cs i
unconnAt-antitone sl cs cs′ i h with sl i
... | scripted _ = z≤n
... | shared _ with memberSource (toℕ i) cs′ | memberSource (toℕ i) cs | h
...   | true  | _     | _  = z≤n
...   | false | false | _  = ≤-refl
...   | false | true  | h′ with h′ refl
...     | ()

unconn-antitone : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs cs′ : List Source) →
  (∀ s → memberSource s cs ≡ true → memberSource s cs′ ≡ true) →
  unconn sl cs′ ≤ unconn sl cs
unconn-antitone sl cs cs′ mono =
  sum-tab-mono (unconnAt sl cs′) (unconnAt sl cs)
    (λ i → unconnAt-antitone sl cs cs′ i (mono (toℕ i)))

-- WHAT A STEP OF THE EVALUATOR IS ALLOWED TO DO TO THE TWO FIELDS THE
-- COUNT READS, STATED OVER THE FIELDS AND NOT OVER THE STATES.  A
-- schedule reached by a record update is not definitionally the one it
-- came from, so a relation indexed by states would need a transport at
-- every arm that rebuilds one; indexed by the fields it does not,
-- because the projection out of a record update reduces.
--
-- AND IT IS A RECORD RATHER THAN THE PAIR IT WRAPS, because the set
-- appears in that pair only under `memberSource`.  A transparent alias
-- leaves a reflexivity whose two sides are the same state asking Agda
-- to solve the set by INVERTING a fold, which it refuses at depth; the
-- record keeps the type rigid, so the same clause matches structurally.
record KeepsC {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
              (sl′ : Slots Γ) (cs′ : List Source) : Set where
  constructor keepsC
  field table : sl′ ≡ sl
        mem   : ∀ s → memberSource s cs ≡ true → memberSource s cs′ ≡ true

keeps-refl : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) → KeepsC sl cs sl cs
keeps-refl sl cs = keepsC refl λ _ h → h

keeps-trans : ∀ {n} {Γ : Ctx n} {sl sl′ sl″ : Slots Γ} {cs cs′ cs″ : List Source}
            → KeepsC sl cs sl′ cs′ → KeepsC sl′ cs′ sl″ cs″ → KeepsC sl cs sl″ cs″
keeps-trans (keepsC refl f) (keepsC refl g) = keepsC refl λ s h → g s (f s h)

-- the connect's own step: one index joins the set and the table is untouched
keeps-cons : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) (s : Source)
           → KeepsC sl cs sl (s ∷ cs)
keeps-cons sl cs s = keepsC refl mem-cons
  where
  mem-cons : ∀ r → memberSource r cs ≡ true → memberSource r (s ∷ cs) ≡ true
  mem-cons r h rewrite h = ∨-zeroʳ (sameSource r s)

-- a room under the ceiling stays under it through any step that keeps
-- the two fields, and the strict form says the same of a fallen one
room-keeps : ∀ {n} {Γ : Ctx n} {sl sl′ : Slots Γ} {cs cs′ : List Source} {m}
           → KeepsC sl cs sl′ cs′ → unconn sl cs ≤ m → unconn sl′ cs′ ≤ m
room-keeps {sl = sl} {cs = cs} {cs′ = cs′} (keepsC refl mono) le =
  ≤-trans (unconn-antitone sl cs cs′ mono) le

fell-keeps : ∀ {n} {Γ : Ctx n} {sl sl′ : Slots Γ} {cs cs′ : List Source} {m}
           → KeepsC sl cs sl′ cs′ → unconn sl cs < m → unconn sl′ cs′ < m
fell-keeps {sl = sl} {cs = cs} {cs′ = cs′} (keepsC refl mono) lt =
  ≤-<-trans (unconn-antitone sl cs cs′ mono) lt
