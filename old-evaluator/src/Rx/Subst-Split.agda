------------------------------------------------------------------
-- TAKING A CONCATENATED TELESCOPE APART, WHERE THE GOAL CANNOT SEE IT.
------------------------------------------------------------------

-- EVERY STATEMENT ABOUT CARRYING AN ENVIRONMENT PAST A RENAMING HAS
-- TO SPLIT A MEMBERSHIP, AND BOTH SIDES HIDE THEIR SPLIT.  The
-- renaming's ++-congruence and the substituter's variable arm each
-- scrutinise the splitter inside their own `with`, so a caller that
-- scrutinises it directly does not merely learn which half the
-- variable came from: the abstraction reaches into the NORMALISED
-- goal and rewrites those buried calls too, leaving an equation whose
-- sides mention a with-auxiliary the caller cannot name.  Packaging
-- the split into a datatype the goal never mentions stops that, and
-- each consumer's step is then restated here as an ordinary lemma
-- taking the equation -- which is what makes it usable from a clause
-- that has already committed to a branch.
module Rx.Subst-Split where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺∘++⁻)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Rx.Exp
  using (Ty; Ctx; Val; Ren∈; ++Ren; subΘTm; varᵗ; wkTm; reify; lookupEnv)

private
  variable
    n           : ℕ
    Γ           : Ctx n
    Δᵍ Δ Θloc Θsub : List Ty
    u           : Ty

------------------------------------------------------------------
-- THE SPLIT, AS A VALUE THE GOAL DOES NOT MENTION.
------------------------------------------------------------------

data Split (A B : List Ty) {u : Ty} (y : u ∈ (A ++ B)) : Set where
  isˡ : (a : u ∈ A) → ∈-++⁻ A y ≡ inj₁ a → Split A B y
  isʳ : (b : u ∈ B) → ∈-++⁻ A y ≡ inj₂ b → Split A B y

split : (A B : List Ty) {u : Ty} (y : u ∈ (A ++ B)) → Split A B y
split A B y with ∈-++⁻ A y in eq
... | inj₁ a = isˡ a eq
... | inj₂ b = isʳ b eq

------------------------------------------------------------------
-- THE SPLITTER'S ROUND TRIP, READ BACKWARDS: a membership the
-- splitter sends one way came from that injection.
------------------------------------------------------------------

left-back : {A B : List Ty} (x : u ∈ (A ++ B)) (y : u ∈ A)
          → ∈-++⁻ A x ≡ inj₁ y → ∈-++⁺ˡ {xs = A} {ys = B} y ≡ x
left-back {A = A} x y eq =
  trans (sym (cong [ ∈-++⁺ˡ , ∈-++⁺ʳ A ]′ eq)) (++⁺∘++⁻ A x)

right-back : {A B : List Ty} (x : u ∈ (A ++ B)) (z : u ∈ B)
           → ∈-++⁻ A x ≡ inj₂ z → ∈-++⁺ʳ A z ≡ x
right-back {A = A} x z eq =
  trans (sym (cong [ ∈-++⁺ˡ , ∈-++⁺ʳ A ]′ eq)) (++⁺∘++⁻ A x)

------------------------------------------------------------------
-- THE TWO CONSUMERS, EACH STEPPED ONCE FROM A KNOWN SPLIT.
------------------------------------------------------------------

++Ren-l : {A A′ B B′ : List Ty} (ρa : Ren∈ A A′) (ρb : Ren∈ B B′)
          (y : u ∈ (A ++ B)) (a : u ∈ A)
        → ∈-++⁻ A y ≡ inj₁ a → ++Ren {A} {A′} {B} {B′} ρa ρb y ≡ ∈-++⁺ˡ (ρa a)
++Ren-l {A = A} ρa ρb y a eq with ∈-++⁻ A y | eq
... | inj₁ _ | refl = refl

++Ren-r : {A A′ B B′ : List Ty} (ρa : Ren∈ A A′) (ρb : Ren∈ B B′)
          (y : u ∈ (A ++ B)) (b : u ∈ B)
        → ∈-++⁻ A y ≡ inj₂ b → ++Ren {A} {A′} {B} {B′} ρa ρb y ≡ ∈-++⁺ʳ A′ (ρb b)
++Ren-r {A = A} ρa ρb y b eq with ∈-++⁻ A y | eq
... | inj₂ _ | refl = refl

sub-left : (Θloc : List Ty) (σ : All (Val Γ) Θsub)
           (x : u ∈ (Θloc ++ Θsub)) (y : u ∈ Θloc)
         → ∈-++⁻ Θloc x ≡ inj₁ y
         → subΘTm {Δᵍ = Δᵍ} {Δ} Θloc σ (varᵗ x) ≡ varᵗ y
sub-left Θloc σ x y eq with ∈-++⁻ Θloc x | eq
... | inj₁ _ | refl = refl

sub-right : (Θloc : List Ty) (σ : All (Val Γ) Θsub)
            (x : u ∈ (Θloc ++ Θsub)) (z : u ∈ Θsub)
          → ∈-++⁻ Θloc x ≡ inj₂ z
          → subΘTm {Δᵍ = Δᵍ} {Δ} Θloc σ (varᵗ x) ≡ wkTm (reify (lookupEnv σ z))
sub-right Θloc σ x z eq with ∈-++⁻ Θloc x | eq
... | inj₂ _ | refl = refl

------------------------------------------------------------------
-- READING A CONCATENATED ENVIRONMENT, at the same split.  The two
-- substituter lemmas above say which TERM a variable becomes; this
-- says which VALUE it is looked up as, and the two are what a
-- composition of substitutions has to reconcile: the inner walk takes
-- what its half owns and the outer takes the rest, while a single
-- walk over the concatenation takes both from one environment.
------------------------------------------------------------------

lookup-++ : (Θloc : List Ty) (ρ : All (Val Γ) Θloc) (σ : All (Val Γ) Θsub)
            (x : u ∈ (Θloc ++ Θsub))
          → lookupEnv (++⁺ ρ σ) x
              ≡ [ lookupEnv ρ , lookupEnv σ ]′ (∈-++⁻ Θloc x)
lookup-++ []      []      σ x          = refl
lookup-++ (a ∷ Θ) (w ∷ ρ) σ (here refl) = refl
lookup-++ (a ∷ Θ) (w ∷ ρ) σ (there p)
  with ∈-++⁻ Θ p | lookup-++ Θ ρ σ p
... | inj₁ y | ih = ih
... | inj₂ z | ih = ih

lookup-left : (Θloc : List Ty) (ρ : All (Val Γ) Θloc) (σ : All (Val Γ) Θsub)
              (x : u ∈ (Θloc ++ Θsub)) (y : u ∈ Θloc)
            → ∈-++⁻ Θloc x ≡ inj₁ y
            → lookupEnv (++⁺ ρ σ) x ≡ lookupEnv ρ y
lookup-left Θloc ρ σ x y eq =
  trans (lookup-++ Θloc ρ σ x) (cong [ lookupEnv ρ , lookupEnv σ ]′ eq)

lookup-right : (Θloc : List Ty) (ρ : All (Val Γ) Θloc) (σ : All (Val Γ) Θsub)
               (x : u ∈ (Θloc ++ Θsub)) (z : u ∈ Θsub)
             → ∈-++⁻ Θloc x ≡ inj₂ z
             → lookupEnv (++⁺ ρ σ) x ≡ lookupEnv σ z
lookup-right Θloc ρ σ x z eq =
  trans (lookup-++ Θloc ρ σ x) (cong [ lookupEnv ρ , lookupEnv σ ]′ eq)
