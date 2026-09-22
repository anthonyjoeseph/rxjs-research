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
module Rx.Evaluator.Unconn-Arith where

open import Data.Bool using (T; true; false; if_then_else_; _∨_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; _∷_; tabulate)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; +-mono-≤; +-mono-<-≤; +-mono-≤-<)
open import Data.Vec using (lookup)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Decide using (≡ᵇ-refl)
open import Rx.Exp using (Ctx; Closed; inputsBelowᵉ)
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

-- and the same with one index moving strictly, which is the only way
-- a sum of naturals falls at all
sum-tab-strict : ∀ {m} (f g : Fin m → ℕ) → (∀ j → f j ≤ g j) →
  (i : Fin m) → f i < g i → sum (tabulate f) < sum (tabulate g)
sum-tab-strict {suc m} f g h fzero    fi<gi =
  +-mono-<-≤ fi<gi (sum-tab-mono _ _ (λ j → h (fsuc j)))
sum-tab-strict {suc m} f g h (fsuc i) fi<gi =
  +-mono-≤-< (h fzero) (sum-tab-strict _ _ (λ j → h (fsuc j)) i fi<gi)

-- adding a member never raises any slot's contribution
unconnAt-cons-≤ : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
  (s : Source) (i : Fin n) → unconnAt sl (s ∷ cs) i ≤ unconnAt sl cs i
unconnAt-cons-≤ sl cs s i with sl i
... | scripted _ = z≤n
... | shared _ with memberSource (toℕ i) cs
...   | true  rewrite ∨-zeroʳ (sameSource (toℕ i) s) = z≤n
...   | false with sameSource (toℕ i) s ∨ false
...     | true  = z≤n
...     | false = ≤-refl

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

-- THE CONNECT EDGE'S OWN FACT, STATED IN THE CURRENCY THE ARM HOLDS.
-- The connect clause reaches its body down two branches -- the slot
-- matched `shared`, and membership read `false` -- and that pair is
-- exactly what makes its index fall from one to nought while no other
-- index rises.  Keeping the two separate at the edge and joining them
-- here is what stops the shape being lost again: the refuted statement
-- is the one that carries only the second.
unconn-insert : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
  (i : Fin n) {d : Closed Γ (lookup Γ i)}
  {ok : T (inputsBelowᵉ (toℕ i) d)} → sl i ≡ shared d {ok = ok} →
  memberSource (toℕ i) cs ≡ false →
  unconn sl (toℕ i ∷ cs) < unconn sl cs
unconn-insert sl cs i eqi fresh =
  sum-tab-strict _ _ (unconnAt-cons-≤ sl cs (toℕ i)) i strict
  where
  strict : unconnAt sl (toℕ i ∷ cs) i < unconnAt sl cs i
  strict rewrite eqi | fresh | ≡ᵇ-refl (toℕ i) = s≤s z≤n

-- WHAT A STEP OF THE EVALUATOR IS ALLOWED TO DO TO THE TWO FIELDS THE
-- COUNT READS, STATED OVER THE FIELDS AND NOT OVER THE STATES.  A
-- schedule reached by a record update is not definitionally the one it
-- came from, so a relation indexed by states would need a transport at
-- every arm that rebuilds one; indexed by the fields it does not,
-- because the projection out of a record update reduces.
KeepsC : ∀ {n} {Γ : Ctx n} → Slots Γ → List Source → Slots Γ → List Source → Set
KeepsC sl cs sl′ cs′ =
  (sl′ ≡ sl) × (∀ s → memberSource s cs ≡ true → memberSource s cs′ ≡ true)

keeps-refl : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) → KeepsC sl cs sl cs
keeps-refl sl cs = refl , λ _ h → h

keeps-trans : ∀ {n} {Γ : Ctx n} {sl sl′ sl″ : Slots Γ} {cs cs′ cs″ : List Source}
            → KeepsC sl cs sl′ cs′ → KeepsC sl′ cs′ sl″ cs″ → KeepsC sl cs sl″ cs″
keeps-trans (refl , f) (refl , g) = refl , λ s h → g s (f s h)

-- the connect's own step: one index joins the set and the table is untouched
keeps-cons : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) (s : Source)
           → KeepsC sl cs sl (s ∷ cs)
keeps-cons sl cs s = refl , mem-cons
  where
  mem-cons : ∀ r → memberSource r cs ≡ true → memberSource r (s ∷ cs) ≡ true
  mem-cons r h rewrite h = ∨-zeroʳ (sameSource r s)

-- AND THE LINE THE WHOLE RING IS FOR, WHICH MOVES A BOUND AND NEVER AN
-- ACCESSIBILITY.  The descent is carried as a CEILING with the witness
-- beside it rather than as an accessibility at the count itself, and
-- that is the difference between a proof that terminates and one that
-- only typechecks: a step that leaves the count alone hands the SAME
-- witness on, untouched, and re-proves the bound instead -- so the
-- termination checker sees a variable where transporting an
-- accessibility would hand it a function call.  Only the connect peels
-- the witness, which is the one edge that may.
room-keeps : ∀ {n} {Γ : Ctx n} {sl sl′ : Slots Γ} {cs cs′ : List Source} {m}
           → KeepsC sl cs sl′ cs′ → unconn sl cs ≤ m → unconn sl′ cs′ ≤ m
room-keeps {sl = sl} {cs = cs} {cs′ = cs′} (refl , mono) le =
  ≤-trans (unconn-antitone sl cs cs′ mono) le
