-- DECIDER↔PROPOSITION ADAPTERS: the little facts that move between a
-- `Bool`-valued decision procedure and a proposition about it — `≡ true`,
-- `T b`, `_≡ᵇ_`, `_≤ᵇ_`, `if_then_else_`, `Maybe` injectivity, and the
-- eliminations of an absurd equation.  Nothing here mentions a type of the
-- rxjs model or of the proof; it imports the standard library and nothing
-- else, which is what lets it sit below every tree.
--
-- WHY IT EXISTS, and it is a wiring finding rather than a tidy-up.  This
-- class had no home, so it accreted A COPY PER TREE: at the time this
-- module was created the repo held FOUR names for `true ≢ false` and TWO
-- byte-identical `∧-intro`s, one on each side of the tier boundary.  The
-- duplicate pair was invisible to `make dup-check`, whose normalisation
-- covers binder spelling and type synonyms but not redundant parentheses
-- (`a ∧ b ≡ true` against `(a ∧ b) ≡ true`), so the compiler could not
-- see it either — neither copy was ever in scope with the other.
--
-- AND IT IS WHAT CLOSES THE TIER-2 DOOR.  `The-Proof` used to reach into
-- `Verify-Well-Formed.Part12`, `.Part4` and `Verify-Budget-Sufficient`'s
-- `Node-Table` for five of these, so utility lemmas crossed two tier
-- boundaries and a reader counting the doors into either tree counted
-- them as claims on the tier.  They are not claims on anything; they are
-- arithmetic.  With one home below both trees, `The-Proof` names this
-- module and the tier exports exactly the statements it proves.
--
-- ONE MODULE, DELIBERATELY, AND NOT A `utils/` DIRECTORY (Anthony's
-- proposal, narrowed here).  The standing rule is ONE naming convention
-- per class of fact, because two conventions are the machine that
-- generates duplicates — and a directory named for its ROLE re-admits as
-- many conventions as it has files.  One module named for its CONTENT
-- makes "does this already exist?" a grep of one file.  Nothing here is
-- mutual with anything, so there is no SCC reason to split it, and the
-- cost of checking it is nil.
--
-- THE NAMES ARE NOT NORMALISED, AND THAT IS A RULING, NOT AN OVERSIGHT.
-- The class arrived with several conventions at once (`∧-trueˡ`, `T-to`,
-- `T⇒≡true`, `f≡t-absurd`, `true≢false`, `≡ᵇ→≡`, `≢ᵇ-from-<`, `not-out`,
-- `ifNeq`), and renaming to one of them would have rewritten roughly 1900
-- call sites for no proof content.  The duplicate-generating mechanism is
-- LOCALITY, not spelling: with every such fact in one file, the check
-- before adding one is reading this file.  Match a neighbour's convention
-- when you add to it; do not launch a rename.
module Decide where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_;
                            if_then_else_; T)
open import Data.Bool.Properties using (∨-assoc; ∨-comm)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _≡ᵇ_; _≤ᵇ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤⇒≤ᵇ; ≤ᵇ⇒≤;
                                       ≡ᵇ⇒≡; ≡⇒≡ᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst)

------------------------------------------------------------------
-- eliminating an absurd equation.  Both directions land in an arbitrary
-- `Set` rather than in `⊥`, which is strictly stronger: a consumer
-- wanting `⊥` gets it by instantiation, and the two `→ ⊥` variants this
-- module replaced were exactly that instantiation written out.
------------------------------------------------------------------

true≢false : {A : Set} → true ≡ false → A
true≢false ()

f≡t-absurd : ∀ {A : Set} → false ≡ true → A
f≡t-absurd ()

------------------------------------------------------------------
-- Bool: ∧, ∨, not, if
------------------------------------------------------------------

∧-trueˡ : ∀ {a b : Bool} → (a ∧ b) ≡ true → a ≡ true
∧-trueˡ {true} _ = refl

∧-trueʳ : ∀ {a b : Bool} → (a ∧ b) ≡ true → b ≡ true
∧-trueʳ {true} h = h

∧-intro : ∀ {a b : Bool} → a ≡ true → b ≡ true → (a ∧ b) ≡ true
∧-intro refl refl = refl

∧ˡ : ∀ (a b : Bool) → T (a ∧ b) → T a
∧ˡ true  b _  = tt
∧ˡ false b ()

∧ʳ : ∀ (a b : Bool) → T (a ∧ b) → T b
∧ʳ true  b h = h
∧ʳ false b ()

∨-fˡ : ∀ (b c : Bool) → (b ∨ c) ≡ false → b ≡ false
∨-fˡ false c h = refl
∨-fˡ true  c h = h

∨-fʳ : ∀ (b c : Bool) → (b ∨ c) ≡ false → c ≡ false
∨-fʳ false c h = h
∨-fʳ true  c ()

∨-trueʳ : ∀ (x : Bool) → (x ∨ true) ≡ true
∨-trueʳ false = refl
∨-trueʳ true  = refl

∨-swap : ∀ (a b c : Bool) → (a ∨ (b ∨ c)) ≡ (b ∨ (a ∨ c))
∨-swap a b c = trans (sym (∨-assoc a b c))
                     (trans (cong (_∨ c) (∨-comm a b)) (∨-assoc b a c))

-- `not x ≡ true → x ≡ false` and its converse.  The implicit-`x` form is
-- the one kept; an explicit-argument twin (`not-true b h`) stood in
-- Verify-Well-Formed and its call sites now pass nothing.
not-out : ∀ {x : Bool} → not x ≡ true → x ≡ false
not-out {false} _ = refl

not-in : ∀ {x : Bool} → x ≡ false → not x ≡ true
not-in refl = refl

force-false : (b : Bool) → (b ≡ true → false ≡ true) → b ≡ false
force-false false _ = refl
force-false true  d with d refl
... | ()

if-false : ∀ {A : Set} {x y : A} (b : Bool) → b ≡ false → (if b then x else y) ≡ y
if-false b eq rewrite eq = refl

if-true : ∀ {A : Set} {x y : A} (b : Bool) → b ≡ true → (if b then x else y) ≡ x
if-true b eq rewrite eq = refl

------------------------------------------------------------------
-- T and `≡ true`, in both directions
------------------------------------------------------------------

T-to : ∀ {b : Bool} → b ≡ true → T b
T-to refl = tt

T⇒≡true : ∀ b → T b → b ≡ true
T⇒≡true true _ = refl

------------------------------------------------------------------
-- ℕ's Bool-valued equality and order
------------------------------------------------------------------

≡ᵇ-refl : ∀ (m : ℕ) → (m ≡ᵇ m) ≡ true
≡ᵇ-refl zero    = refl
≡ᵇ-refl (suc m) = ≡ᵇ-refl m

≡ᵇ-sym : ∀ (a b : ℕ) → (a ≡ᵇ b) ≡ (b ≡ᵇ a)
≡ᵇ-sym zero    zero    = refl
≡ᵇ-sym zero    (suc b) = refl
≡ᵇ-sym (suc a) zero    = refl
≡ᵇ-sym (suc a) (suc b) = ≡ᵇ-sym a b

≡ᵇ→≡ : ∀ (m k : ℕ) → (m ≡ᵇ k) ≡ true → m ≡ k
≡ᵇ→≡ zero    zero    _ = refl
≡ᵇ→≡ (suc m) (suc k) h = cong suc (≡ᵇ→≡ m k h)

≢ᵇ-from-< : ∀ {j i : ℕ} → j ≤ i → (suc i ≡ᵇ j) ≡ false
≢ᵇ-from-< z≤n     = refl
≢ᵇ-from-< (s≤s q) = ≢ᵇ-from-< q

sucle→≢ᵇ : ∀ {j nextId : ℕ} → suc j ≤ nextId → (nextId ≡ᵇ j) ≡ false
sucle→≢ᵇ (s≤s q) = ≢ᵇ-from-< q

≤ᵇ-true : ∀ (a b : ℕ) → a ≤ b → (a ≤ᵇ b) ≡ true
≤ᵇ-true a b p with a ≤ᵇ b | ≤⇒≤ᵇ p
... | true | _ = refl

-- the `where`-local inverse this proof used to carry was a third copy of
-- `T⇒≡true`; it spends the sibling instead.
≤ᵇ-widen : ∀ (v : ℕ) {B B′ : ℕ} → B ≤ B′ → (v ≤ᵇ B) ≡ true → (v ≤ᵇ B′) ≡ true
≤ᵇ-widen v {B} {B′} le h with ≤⇒≤ᵇ (≤-trans (≤ᵇ⇒≤ v B (T-to h)) le)
... | w = T⇒≡true (v ≤ᵇ B′) w

------------------------------------------------------------------
-- the 0/1 indicator `if a ≡ᵇ b then 1 else 0`
------------------------------------------------------------------

ite≤ : ∀ (b : Bool) {N : ℕ} → 1 ≤ N → (if b then 1 else 0) ≤ N
ite≤ true  h = h
ite≤ false h = z≤n

ifLe1 : ∀ (a b : ℕ) → (if a ≡ᵇ b then 1 else 0) ≤ 1
ifLe1 a b with a ≡ᵇ b
... | true  = ≤-refl
... | false = z≤n

ifNeq : ∀ (a b : ℕ) → (a ≡ b → ⊥) → (if a ≡ᵇ b then 1 else 0) ≡ 0
ifNeq a b ne with a ≡ᵇ b in eq
... | false = refl
... | true  = ⊥-elim (ne (≡ᵇ⇒≡ a b (subst T (sym eq) tt)))

ifEq : ∀ (a b : ℕ) → a ≡ b → 1 ≤ (if a ≡ᵇ b then 1 else 0)
ifEq a b e with a ≡ᵇ b in q
... | true  = s≤s z≤n
... | false = ⊥-elim (subst T q (≡⇒≡ᵇ a b e))

------------------------------------------------------------------
-- Maybe
------------------------------------------------------------------

just-injᵂ : ∀ {A : Set} {x y : A} → _≡_ {A = Maybe A} (just x) (just y) → x ≡ y
just-injᵂ refl = refl

n≢jᵂ : ∀ {A : Set} {x : A} → _≡_ {A = Maybe A} nothing (just x) → ⊥
n≢jᵂ ()
