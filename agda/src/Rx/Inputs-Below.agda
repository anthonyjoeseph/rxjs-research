-- THE DESCENT SHELF FOR THE INPUT BOUND, and it is a shelf rather than
-- a lemma because the predicate is a fold of `_∧_` over a term's
-- children.  Every subscription step walks into a subexpression, so
-- every step owes the same projection, and writing them once here keeps
-- the evaluator's clauses reading as the machine rather than as a proof.
--
-- AND THE BOUND TRAVELS AS AN IMPLICIT, WHICH IS WHY NONE OF THIS
-- REACHES A CALL SITE.  `T b` is `⊤` when `b` computes to `true`, and
-- Agda's eta for the unit record solves such an implicit with no
-- argument written — so at a concrete program the whole shelf is
-- invisible and only a statement quantifying over the expression has to
-- carry the premise at all.  That is the same device the slot
-- telescope's own constructor already uses to store this bound.

module Rx.Inputs-Below where

open import Data.Bool using (Bool; T)
open import Data.Bool.Properties using (T-∧)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Properties using (<ᵇ⇒<; <⇒<ᵇ)
open import Data.Product using (_,_; proj₂)
open import Data.Unit using (tt)
open import Function using (Equivalence)

open import Rx.Exp using (Ctx; Exp; Tm; Fn; Val; obs; natᵗ; _×ᵗ_; inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ; unfoldμ;
  input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
  varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ)

private
  variable
    n : ℕ
    Γ : Ctx n
    k : ℕ

-- THE SPLIT, ONCE.  Everything below is this applied at one clause's
-- own conjunction, so the equivalence is spent here and nowhere else.
-- Only the RIGHT projection is ever wanted: a clause's own terms sit
-- left of the conjunction and a subscription steps into the expression.
∧ʳ : ∀ {a b : Bool} → T (a Data.Bool.∧ b) → T b
∧ʳ {a} {b} p = proj₂ (Equivalence.to (T-∧ {a} {b}) p)

-- THE ONE ARM THAT SAYS SOMETHING, and it is the whole point of the
-- bound: a subscription reading slot `i` under floor `k` learns that
-- `i` is strictly below the floor, which is exactly what lets the
-- caller's continuation be registered at a floor above `i`.
-- AND EVERY ARM TAKES ITS FLOOR AND ITS SUBTERM EXPLICITLY, which is
-- not a style choice: `T` is defined by matching on a Bool, so `T x`
-- against `T y` cannot be decomposed while both sides are stuck, and an
-- implicit floor is a meta the caller's expected type can never solve.
-- Written out, every arm's result COMPUTES to the type the clause wants
-- and nothing is left to guess.  The binders go the same way for the
-- one arm whose conclusion mentions neither of them.
below-input : ∀ (k : ℕ) (i : Fin n)
            → T (inputsBelowᵉ {Γ = Γ} {[]} {[]} {[]} k (input i)) → toℕ i < k
below-input k i p = <ᵇ⇒< (toℕ i) k p

-- and the descent arms, one per clause of the predicate that has a
-- subexpression a subscription steps into
below-map : ∀ {Δᵍ Δ Θ s t} (k : ℕ) (f : Fn Γ Δᵍ Δ Θ s t) (b : Exp Γ Δᵍ Δ Θ s)
          → T (inputsBelowᵉ k (mapᵉ f b)) → T (inputsBelowᵉ k b)
below-map k f b = ∧ʳ {inputsBelowᵗ k f}

below-take : ∀ {Δᵍ Δ Θ t} (k : ℕ) (c : Tm Γ Δᵍ Δ Θ natᵗ) (b : Exp Γ Δᵍ Δ Θ t)
           → T (inputsBelowᵉ k (takeᵉ c b)) → T (inputsBelowᵉ k b)
below-take k c b = ∧ʳ {inputsBelowᵗ k c}

below-scan : ∀ {Δᵍ Δ Θ s t} (k : ℕ) (f : Fn Γ Δᵍ Δ Θ (t ×ᵗ s) t)
               (z : Tm Γ Δᵍ Δ Θ t) (b : Exp Γ Δᵍ Δ Θ s)
           → T (inputsBelowᵉ k (scanᵉ f z b)) → T (inputsBelowᵉ k b)
below-scan k f z b p = ∧ʳ {inputsBelowᵗ k z} (∧ʳ {inputsBelowᵗ k f} p)

-- the three flatteners and the two binders carry the bound through
-- unchanged, so they are definitional and exist only to be nameable
below-mergeAll : ∀ {Δᵍ Δ Θ t} (k : ℕ) (lim : Maybe ℕ) (b : Exp Γ Δᵍ Δ Θ (obs t))
               → T (inputsBelowᵉ k (mergeAllᵉ lim b))
               → T (inputsBelowᵉ k b)
below-mergeAll k lim b p = p

below-switchAll : ∀ {Δᵍ Δ Θ t} (k : ℕ) (b : Exp Γ Δᵍ Δ Θ (obs t))
                → T (inputsBelowᵉ k (switchAllᵉ b))
                → T (inputsBelowᵉ k b)
below-switchAll k b p = p

below-exhaustAll : ∀ {Δᵍ Δ Θ t} (k : ℕ) (b : Exp Γ Δᵍ Δ Θ (obs t))
                 → T (inputsBelowᵉ k (exhaustAllᵉ b))
                 → T (inputsBelowᵉ k b)
below-exhaustAll k b p = p

below-μ : ∀ {Δᵍ Δ Θ t} (k : ℕ) (b : Exp Γ (t ∷ Δᵍ) Δ Θ t)
        → T (inputsBelowᵉ k (μᵉ b)) → T (inputsBelowᵉ k b)
below-μ k b p = p

-- THE ROOT'S OWN WITNESS, and it is true of EVERY closed term because
-- the syntax cannot state otherwise: an `input` names a `Fin n`, and
-- `toℕ` of a `Fin n` is below `n`.  Every other constructor either
-- carries no input at all or hands the bound down unchanged, so the
-- whole body is the `Fin` fact at one clause and the conjunction
-- introduction everywhere else.
--
-- THE FLOOR IS THE CONTEXT SIZE AND CANNOT BE GENERALISED, which is
-- what makes this the ROOT's witness rather than a lemma about terms:
-- at any smaller floor the `input` clause is exactly the statement the
-- runtime arm below is refuted at.
∧ᵢ : ∀ {a b : Bool} → T a → T b → T (a Data.Bool.∧ b)
∧ᵢ {a} {b} x y = Equivalence.from (T-∧ {a} {b}) (x , y)

mutual
  below-ctx : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (b : Exp Γ Δᵍ Δ Θ t)
            → T (inputsBelowᵉ n b)
  below-ctx (input i)               = <⇒<ᵇ (toℕ<n i)
  below-ctx (ofᵉ ts)                = below-ctxᵗˢ ts
  below-ctx emptyᵉ                  = tt
  below-ctx (mapᵉ f b)              = ∧ᵢ (below-ctxᵗ f) (below-ctx b)
  below-ctx (takeᵉ c b)             = ∧ᵢ (below-ctxᵗ c) (below-ctx b)
  below-ctx (scanᵉ f z b)           =
    ∧ᵢ (below-ctxᵗ f) (∧ᵢ (below-ctxᵗ z) (below-ctx b))
  below-ctx (mergeAllᵉ lim b)       = below-ctx b
  below-ctx (switchAllᵉ b)          = below-ctx b
  below-ctx (exhaustAllᵉ b)         = below-ctx b
  below-ctx (μᵉ b)                  = below-ctx b
  below-ctx (varᵉ x)                = tt
  below-ctx (deferᵉ b)              = below-ctx b

  below-ctxᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (c : Tm Γ Δᵍ Δ Θ t)
             → T (inputsBelowᵗ n c)
  below-ctxᵗ (varᵗ x)      = tt
  below-ctxᵗ unit̂          = tt
  below-ctxᵗ (bool̂ _)      = tt
  below-ctxᵗ (nat̂ _)       = tt
  below-ctxᵗ (pairᵗ a b)   = ∧ᵢ (below-ctxᵗ a) (below-ctxᵗ b)
  below-ctxᵗ (fstᵗ p)      = below-ctxᵗ p
  below-ctxᵗ (sndᵗ p)      = below-ctxᵗ p
  below-ctxᵗ (inlᵗ a)      = below-ctxᵗ a
  below-ctxᵗ (inrᵗ a)      = below-ctxᵗ a
  below-ctxᵗ (caseᵗ s l r) =
    ∧ᵢ (below-ctxᵗ s) (∧ᵢ (below-ctxᵗ l) (below-ctxᵗ r))
  below-ctxᵗ (ifᵗ c a b)   =
    ∧ᵢ (below-ctxᵗ c) (∧ᵢ (below-ctxᵗ a) (below-ctxᵗ b))
  below-ctxᵗ (primᵗ _ a)   = below-ctxᵗ a
  below-ctxᵗ (strmᵗ b)     = below-ctx b

  below-ctxᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t))
              → T (inputsBelowᵗˢ n ts)
  below-ctxᵗˢ []       = tt
  below-ctxᵗˢ (y ∷ ys) = ∧ᵢ (below-ctxᵗ y) (below-ctxᵗˢ ys)

-- THE UNFOLD SUBSTITUTES THE BINDING INTO ITS OWN BODY, so the only
-- thing entering is a term already at the bound, and the bound is
-- closed under that.  One induction over the substitution, and the
-- statement is the one shape where a self-substitution is the whole
-- content rather than a step of a larger walk.
--
-- PROBED: `Probed.Unfold-Bound` — two floors, each strictly inside a
--   context of three, so the conclusion is not the free one the root's
--   own witness already gives; a negative control at floor zero fixes
--   the same unfolded term with the predicate computing to `false`, so
--   the empty type is reachable along this conclusion and a green row
--   is a reading.  NOT covered: a NESTED μ, where the graft index is
--   `there` and the elimination walks under a second binder — every row
--   is one binder deep.
postulate
  below-unfoldμ : ∀ {t} (k : ℕ) (b : Exp Γ (t ∷ []) [] [] t)
                → T (inputsBelowᵉ k b) → T (inputsBelowᵉ k (unfoldμ b))

-- THE ARM THE SYNTAX CANNOT REACH.  A value of observable type IS a
-- closed expression, manufactured by applying a function rather than
-- sitting anywhere in the program, so the bound on it is a fact about
-- the RUN and not about the term the subscription is walking.  What
-- makes it true where the evaluator uses it: a value carried on a chain
-- registered at slot `i` was emitted by that slot, whose definition
-- names only inputs below `i`, while the chain's own floor is `suc i` —
-- so the bound arrives with a unit of slack, and substitution is
-- monotone in the floor, so every hop rootward only weakens it.
--
-- AND STATED OVER AN ARBITRARY FLOOR IT IS FALSE, SO THIS IS A HOLE AND
-- NOT A GAP.  ⊥ follows from it directly, which means every statement
-- proven anywhere above it currently stands on a false hypothesis — the
-- one shape of debt this development treats as outranking the work it
-- was incurred for.  The sound form carries the bound on the VALUE and
-- relates it to the chain the value arrived on, which is a proof field
-- on the run state; that is the same per-emission cost the batching
-- design declined once, and the reason the restatement is a design
-- question rather than a signature edit.
--
-- AND DELETING IT IS NOT THE REPAIR, because the EVALUATOR consumes it:
-- the inner-subscription clause needs an inhabitant to hand the walk it
-- re-enters, so the leaf is load-bearing for the machine to be
-- well-typed and not merely for a proof above it.  The floors a run
-- actually produces are the ones the claim wants — the root enters at
-- the context size and the only descent is to `suc i`, so the bound
-- arrives with a unit of slack — and nothing in the type says so.
--
-- REFUTED: `Refuted.Inner-Floor` — a floor of zero against a context
--   that has a slot, at the value `input 0`.  The predicate computes to
--   `false`, so the statement returns an inhabitant of the empty type
--   with no crossing to pin and no figure a repair could leave intact.
  below-inner : ∀ {t} (k : ℕ) (o : Val Γ (obs t)) → T (inputsBelowᵉ k o)
