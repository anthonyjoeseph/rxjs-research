{-# OPTIONS --guardedness #-}

-- THE CONSUMPTION: the elaborated program reads what its plain program
-- reads.  Each plain row has an elaborated row of its kind (`Sim.fwd`);
-- each value, end and pin the elaborated run shows is a plain row's
-- (`Sim.val←`, `Sim.end←`, `Sim.pin←`); and every elaborated row is
-- owned, by the subscription, a plain row or an environment row, each
-- owning finitely many (`Sim.cover`).  So a finite plain run has a
-- finite elaborated run (`sim-whole`).
--
-- AN EXACT SIMULATION, BOTH WAYS.  Every operator above decides from
-- values, ends and their order across streams (a take's failure, a
-- switch's next outer value, an exhaust's busy lane, a concat's
-- hand-off), and a reading keeps a row only with finitely many before
-- it, so neither side's rows are bounded by the other's unless each
-- decision transfers both ways.
--
-- ORDER ACROSS STREAMS IS ONE EMBEDDING (`Emb`): a plain row maps to the
-- ANCHOR its elaborated rows lie under, the anchors keep the plain
-- order, and an anchor under another is a row under another.  Plain rows
-- lie apart, so anchors do, and every elaborated row of one owner lies
-- before every elaborated row of a later one.
module simultaneous.Consume where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; concat) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-concat⁺′)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_)
open import Data.List.Relation.Unary.All using ([])
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; _≺_; enter; approx)
open import denotation.Laws.Worlds using (_⊑_)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.SObs using (SObs; plain; lone; module Elaborate)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; elaborate)

------------------------------------------------------------------------
-- Maps of positions

PMap : Set₁
PMap = Pos → Pos → Set

-- AN ORDER EMBEDDING: one image each, the order kept, leading reflected.
record Emb (M : PMap) : Set where
  field
    fun     : ∀ {x y y′} → M x y → M x y′ → y ≡ y′
    mono    : ∀ {x x′ y y′} → M x y → M x′ y′ → x ≺ x′ → y ≺ y′
    reflect : ∀ {x x′ y y′} → M x y → M x′ y′ → y ⊑ y′ → x ⊑ x′

------------------------------------------------------------------------
-- The simulation

-- A plain event and an elaborated one of its kind: a value and a value
-- showing it, a skip and a skip or a value showing nothing, an end and an
-- end, a pin and a pin of its connect's image.
data Mt {A B : Set} (V : A → B → Set) (Sh : B → Set) (M : PMap) : Ev A → Ev B → Set where
  m-out  : ∀ {a b} → V a b → Mt V Sh M (out a) (out b)
  m-skip : Mt V Sh M skip skip
  m-mark : ∀ {b} → ¬ Sh b → Mt V Sh M skip (out b)
  m-end  : Mt V Sh M end end
  m-pin  : ∀ {r r′} → M r r′ → Mt V Sh M (pin r) (pin r′)

-- The elaborated rows `U`, subscribed at `p′`, simulate the plain rows
-- `T`, subscribed at `p`, along `M`, under the environment's plain rows
-- `HP`: each row under its owner's anchor.
record Sim {A B : Set} (V : A → B → Set) (Sh : B → Set) (M : PMap) (HP : Pos → Set) (p : Pos)
           (T : EmissionSet A) (U : EmissionSet B) : Set where
  field
    fwd   : ∀ {k e} → T k e → Σ Pos λ y → M k y × Σ Pos λ l → y ⊑ l × Σ (Ev B) λ e′ → U l e′ × Mt V Sh M e e′
    val←  : ∀ {l b} → U l (out b) → Sh b → Σ Pos λ k → Σ Pos λ y → M k y × y ⊑ l × Σ A λ a → T k (out a) × V a b
    end←  : ∀ {l} → U l end → Σ Pos λ k → Σ Pos λ y → M k y × y ⊑ l × T k end
    pin←  : ∀ {l r r′} → U l (pin r′) → M r r′ → Σ Pos λ k → Σ Pos λ y → M k y × y ⊑ l × T k (pin r)
    fib   : Pos → List Pos
    cover : ∀ {l e′} → U l e′ → Σ Pos λ k → (k ≡ p ⊎ Σ (Ev A) (T k) ⊎ HP k) × l ∈ fib k × Σ Pos λ y → M k y × y ⊑ l

-- A FINITE PLAIN RUN HAS A FINITE ELABORATED RUN: each elaborated row is
-- among its owner's, and the owners are the subscription and the plain
-- rows.
sim-whole : ∀ {A B} {V : A → B → Set} {Sh M HP p T U} → Sim V Sh M HP p T U → (∀ {k} → HP k → ⊥)
          → (ks : List Pos) → (∀ {k e} → T k e → k ∈ ks) → Σ (List Pos) λ ls → ∀ {l e} → U l e → l ∈ ls
sim-whole {p = p} {U = U} S nh ks every = concat (mapL (Sim.fib S) (p ∷ ks)) , owned
  where
  owned : ∀ {l e} → U l e → l ∈ concat (mapL (Sim.fib S) (p ∷ ks))
  owned y with Sim.cover S y
  ... | k , inj₁ refl , m , _              = ∈-concat⁺′ {xss = mapL (Sim.fib S) (p ∷ ks)} m (here refl)
  ... | k , inj₂ (inj₁ (_ , x)) , m , _    = ∈-concat⁺′ {xss = mapL (Sim.fib S) (p ∷ ks)} m (∈-map⁺ (Sim.fib S) (there (every x)))
  ... | k , inj₂ (inj₂ h) , _ , _          = ⊥-elim (nh h)

------------------------------------------------------------------------
-- The elaboration simulates its program

-- A value shown is the plain value; a mark shows none.
Shows : ∀ {A} → A → IE A → Set
Shows a b = valuesOf b ≡ a ∷ []

Shown : ∀ {A} → IE A → Set
Shown b = ¬ (valuesOf b ≡ [])

postulate
  -- THE CLOSED PROGRAM, simulated at every approximant from the root.
  sim-root : ∀ n {A} (o : SObs [] A) → Σ PMap λ M → Emb M
           × Sim Shows Shown M (λ _ → ⊥) root (enter (approx n (plain o) []) root) (enter (approx n (elaborate (plain o)) []) root)
