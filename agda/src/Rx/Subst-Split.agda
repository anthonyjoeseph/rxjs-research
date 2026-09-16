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
open import Data.List using (List; _++_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
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
    Δᵍ Δ Θsub   : List Ty
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
