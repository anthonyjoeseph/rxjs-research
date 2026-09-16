------------------------------------------------------------------
-- CLOSING A TERM AGAINST AN ENVIRONMENT, AND THEN READING IT, IS
-- READING IT UNDER THAT ENVIRONMENT.
--
-- The reducibility walk carries its environment rather than applying
-- it, so every clause that finally reads a term owes the agreement
-- between the two.  It reaches one at exactly two telescopes: a
-- one-shot's element, where nothing is bound, and a frame's function
-- at an arriving value, where one thing is.  `evalTm` and `applyFn`
-- are both `evalWith` at a fixed environment, so those are not two
-- obligations -- they are one statement at `Θloc = []` and at a
-- singleton, and the general form is what is stated here.
--
-- WHY THE LOCAL TELESCOPE IS A PARAMETER AND THE ENVIRONMENT SPLITS.
-- `subΘTm` walks under binders by EXTENDING `Θloc`, so a statement
-- pinned at the empty telescope cannot be its own induction
-- hypothesis -- the `mapᵉ`, `scanᵉ` and `caseᵗ` arms all recurse at a
-- longer one.  Quantifying over `Θloc` and supplying the values for
-- it separately is what closes that, and it is the same shape the
-- measure face's own substitution walks already take.
module Rx.Subst-Eval where

open import Data.Bool using (if_then_else_; not)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Nat using (_+_; _∸_; _*_; _≡ᵇ_; _<ᵇ_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Rx.Exp using (Ctx; Val; Exp; Tm; Fn; evalTm; evalWith; applyFn; subΘTm; subΘExp; lookupEnv; wkTm; reify;
  varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ; add; sub;
  mul; eqᵖ; ltᵖ; notᵖ)

postulate
  -- THE VARIABLE ARM, WHICH IS THE WHOLE OF WHAT A LEAF CAN BE HERE.
  -- `subΘTm` dispatches a variable on which half of the telescope it
  -- lands in: a local one is renamed and read from `ρ`, a substituted
  -- one is REIFIED to a closed literal and weakened back in, so the
  -- two sides agree for different reasons and neither has a subterm to
  -- recurse on.
  -- REIFYING A VALUE AND READING IT BACK IS THE IDENTITY, in any
  -- environment at all.  The environment cannot matter because the
  -- literal `reify` produces is CLOSED and weakened in, so nothing in
  -- it is a variable -- but saying so needs the expression face at the
  -- observable arm, where the literal carries a whole expression and
  -- the reading closes it against an environment it does not mention.
  -- PROBED: `Probed.Substitution-Leaves`, at an OBSERVABLE against a
  --   non-empty environment, which is the one arm whose literal is not
  --   already a value; and at a numeral, which is degenerate.  Not
  --   reached: the product and sum arms, and a literal carrying an
  --   expression with a real local telescope.
  evalWith-wkReify : ∀ {n} {Γ : Ctx n} {Θ t} (v : Val Γ t) (ρ : All (Val Γ) Θ)
                   → evalWith (wkTm (reify v)) ρ ≡ v

  -- THE EMBEDDING ARM, WHERE THE TERM FACE HANDS BACK TO THE
  -- EXPRESSION FACE AND THE STATEMENT STOPS BEING ABOUT TERMS.
  -- `evalWith` at a stream literal does not read the expression, it
  -- CLOSES it against the environment, so this arm is substitution
  -- COMPOSITION rather than an induction hypothesis -- the term walk
  -- has no subterm of its own type here.
  -- PROBED: `Probed.Substitution-Leaves`, at a one-entry local
  --   telescope whose embedded expression reads BOTH halves of the
  --   split.  Not reached: a longer local telescope, and any former
  --   sitting between the embedding and the variables.
  sub-evalStrm : ∀ {n} {Γ : Ctx n} {Θloc Θsub t} (e : Exp Γ [] [] (Θloc ++ Θsub) t)
                 (σ : All (Val Γ) Θsub) (ρ : All (Val Γ) Θloc)
               → evalWith (strmᵗ (subΘExp Θloc σ e)) ρ
                   ≡ evalWith (strmᵗ e) (++⁺ ρ σ)

-- THE VARIABLE ARM, BY INDUCTION ON THE LOCAL TELESCOPE.  A variable
-- the telescope still covers is read straight out of `ρ`; one it has
-- walked past is the substitution's, and is reified.  The step case
-- has to split the SAME dispatch the definition splits, which is why
-- the hypothesis is brought under the `with` rather than applied
-- after it.
sub-evalVar : ∀ {n} {Γ : Ctx n} {Θloc Θsub t} (x : t ∈ (Θloc ++ Θsub))
              (σ : All (Val Γ) Θsub) (ρ : All (Val Γ) Θloc)
            → evalWith (subΘTm Θloc σ (varᵗ x)) ρ ≡ lookupEnv (++⁺ ρ σ) x
sub-evalVar {Θloc = []}      x           σ []      =
  evalWith-wkReify (lookupEnv σ x) []
sub-evalVar {Θloc = a ∷ Θl} (here refl)  σ (w ∷ ρ) = refl
sub-evalVar {Θloc = a ∷ Θl} (there p)    σ (w ∷ ρ)
  with ∈-++⁻ Θl p | sub-evalVar p σ ρ
... | inj₁ y | ih = ih
... | inj₂ z | ih =
  trans (evalWith-wkReify (lookupEnv σ z) (w ∷ ρ))
        (trans (sym (evalWith-wkReify (lookupEnv σ z) ρ)) ih)

-- THE GENERAL AGREEMENT.  Every arm but the two above is a congruence,
-- and every binder extends the local telescope rather than the
-- substituted one -- which is why the statement had to be general in
-- `Θloc` before any of it could be written.
sub-evalWith : ∀ {n} {Γ : Ctx n} {Θloc Θsub t} (tm : Tm Γ [] [] (Θloc ++ Θsub) t)
               (σ : All (Val Γ) Θsub) (ρ : All (Val Γ) Θloc)
             → evalWith (subΘTm Θloc σ tm) ρ ≡ evalWith tm (++⁺ ρ σ)
sub-evalWith (varᵗ x)    σ ρ = sub-evalVar x σ ρ
sub-evalWith unit̂        σ ρ = refl
sub-evalWith (bool̂ b)    σ ρ = refl
sub-evalWith (nat̂ n)     σ ρ = refl
sub-evalWith (pairᵗ a b) σ ρ = cong₂ _,_ (sub-evalWith a σ ρ) (sub-evalWith b σ ρ)
sub-evalWith (fstᵗ p)    σ ρ = cong (λ w → let (a , _) = w in a) (sub-evalWith p σ ρ)
sub-evalWith (sndᵗ p)    σ ρ = cong (λ w → let (_ , b) = w in b) (sub-evalWith p σ ρ)
sub-evalWith (inlᵗ a)    σ ρ = cong inj₁ (sub-evalWith a σ ρ)
sub-evalWith (inrᵗ a)    σ ρ = cong inj₂ (sub-evalWith a σ ρ)
sub-evalWith (ifᵗ c a b) σ ρ =
  cong₃ if_then_else_ (sub-evalWith c σ ρ) (sub-evalWith a σ ρ) (sub-evalWith b σ ρ)
  where
  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x y u v p q}
        → x ≡ y → u ≡ v → p ≡ q → f x u p ≡ f y v q
  cong₃ f refl refl refl = refl
sub-evalWith (primᵗ add  a) σ ρ =
  cong (λ w → let (x , y) = w in x + y) (sub-evalWith a σ ρ)
sub-evalWith (primᵗ sub  a) σ ρ =
  cong (λ w → let (x , y) = w in x ∸ y) (sub-evalWith a σ ρ)
sub-evalWith (primᵗ mul  a) σ ρ =
  cong (λ w → let (x , y) = w in x * y) (sub-evalWith a σ ρ)
sub-evalWith (primᵗ eqᵖ  a) σ ρ =
  cong (λ w → let (x , y) = w in x ≡ᵇ y) (sub-evalWith a σ ρ)
sub-evalWith (primᵗ ltᵖ  a) σ ρ =
  cong (λ w → let (x , y) = w in x <ᵇ y) (sub-evalWith a σ ρ)
sub-evalWith (primᵗ notᵖ a) σ ρ = cong not (sub-evalWith a σ ρ)
sub-evalWith (strmᵗ e)   σ ρ = sub-evalStrm e σ ρ
sub-evalWith (caseᵗ sc l r) σ ρ
  rewrite sub-evalWith sc σ ρ with evalWith sc (++⁺ ρ σ)
... | inj₁ x = sub-evalWith l σ (x ∷ ρ)
... | inj₂ y = sub-evalWith r σ (y ∷ ρ)

-- A ONE-SHOT'S ELEMENT binds nothing, so the local telescope is empty
-- and the environment is the substitution's own.
sub-evalTm : ∀ {n} {Γ : Ctx n} {Θ u} (tm : Tm Γ [] [] Θ u) (σ : All (Val Γ) Θ)
           → evalTm (subΘTm [] σ tm) ≡ evalWith tm σ
sub-evalTm tm σ = sub-evalWith tm σ []

-- A FRAME'S FUNCTION binds exactly its argument, so the local
-- telescope is a singleton and the arriving value is what fills it.
sub-applyFn : ∀ {n} {Γ : Ctx n} {Θ s u} (f : Fn Γ [] [] Θ s u)
              (σ : All (Val Γ) Θ) (v : Val Γ s)
            → applyFn (subΘTm (s ∷ []) σ f) v ≡ evalWith f (v ∷ σ)
sub-applyFn f σ v = sub-evalWith f σ (v ∷ [])
