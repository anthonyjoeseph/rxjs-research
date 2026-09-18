-- A BOVE-CAPRETTA DOMAIN PREDICATE OVER THIS SYNTAX, AND WHY THE
-- STRUCTURAL ONE ASSERTS NOTHING.  The evaluator's hop subscribes an
-- observable that ARRIVED rather than one it can see, so the obvious
-- repair for a refuted numeric rank is to carry a domain predicate and
-- descend on it instead.  A predicate over the term's own formers is
-- the only one of the candidate shapes that is both strictly positive
-- and invertible at a term head -- which is what the evaluator needs,
-- since it cases on the term and must hand the recursive call a proof
-- for that term's child.  This file shows it is `⊤`: every closed term
-- inhabits it, by plain structural recursion, so descending on it is
-- descending on a copy of the term and the hop is no better off.
--
-- AND THE THREE STRONGER SHAPES ARE NOT AVAILABLE, EACH FOR A REASON
-- THE COMPILER GIVES RATHER THAN A REASON ANYONE ARGUED.  Asking the
-- fold's template to preserve the predicate as a premise
-- (`∀ acc → Sub acc → Sub (applyFn f (acc , v))`) puts the predicate
-- left of an arrow and is rejected `NotStrictlyPositive`.  The same
-- premise as a recursive predicate into `Set` instead of a datatype
-- escapes positivity and is rejected `TerminationIssue`, because
-- `applyFn f (acc , v)` is larger than `acc`.  Minting instead -- a
-- constructor `Sub acc → Sub (applyFn f (acc , v))`, no quantifier in
-- front, so the producing frame hands back the successor -- IS
-- strictly positive and DOES terminate, and dies at the third
-- condition: `SplitError.UnificationStuck` on
-- `applyFn f (acc , v) ≟ mergeAllᵉ lim b`, since substitution is not a
-- constructor and nothing about the produced term inverts.
--
-- WHAT THE FOUR HAVE IN COMMON IS THE FINDING.  A fold's output is
-- built by SUBSTITUTION into a template, and substitution is neither a
-- constructor nor size-reducing -- so the arriving observable is
-- related to nothing in hand, structurally or numerically.  A
-- predicate strong enough to carry the hop is one that quantifies over
-- produced values and cannot be defined; one weak enough to be defined
-- is one that reads the term and buys nothing.  The gap is not in how
-- the descent is DENOMINATED, which is what a rank and a domain
-- predicate disagree about; it is that a value carries no trace of
-- what produced it.
module Refuted.Domain-Predicate where

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Product using (Σ; _,_)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Nullary using (¬_)

open import Rx.Exp using (Ctx; Tm; Fn; Closed; obs; natᵗ; _×ᵗ_; input; ofᵉ; emptyᵉ; takeᵉ; batchSyncᵉ;
  mapᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; mintᵉ)

-- the structural domain predicate: one constructor per former, each
-- taking the predicate at the Exp children a subscribe actually walks.
-- `input`, `ofᵉ`, `emptyᵉ`, `deferᵉ`, `μᵉ` and `mintᵉ` are leaves here
-- -- the first is the share connect, whose descent is the unconnected
-- count, and the μ peel's is `syncSize`.  A mint is a leaf for a
-- sharper reason than choice: it BINDS, so its child sits under a
-- longer token telescope and is not closed, and this predicate is
-- indexed by closed terms alone.  None of them is the hop, and none is
-- in question.
data Sub {n} {Γ : Ctx n} : ∀ {t} → Closed Γ t → Set where
  s-input : ∀ {i} → Sub (input {Γ = Γ} i)
  s-of    : ∀ {t ts} → Sub (ofᵉ {Γ = Γ} {t = t} ts)
  s-empty : ∀ {t} → Sub (emptyᵉ {Γ = Γ} {t = t})
  s-defer : ∀ {t body} → Sub (deferᵉ {Γ = Γ} {t = t} body)
  s-μ     : ∀ {t body} → Sub (μᵉ {Γ = Γ} {t = t} body)
  s-mint  : ∀ {t body} → Sub (mintᵉ {Γ = Γ} {t = t} body)
  s-take  : ∀ {t} {c : Tm Γ [] [] [] _} {b} → Sub b → Sub (takeᵉ {t = t} c b)
  s-map   : ∀ {s t} {f : Fn Γ [] [] [] s t} {b : Closed Γ s}
          → Sub b → Sub (mapᵉ f b)
  s-scan  : ∀ {s t} {f : Fn Γ [] [] [] (t ×ᵗ s) t}
              {z : Tm Γ [] [] [] t} {b : Closed Γ s}
          → Sub b → Sub (scanᵉ f z b)
  s-merge : ∀ {t lim} {b : Closed Γ (obs t)} → Sub b → Sub (mergeAllᵉ lim b)
  s-switch : ∀ {t} {b : Closed Γ (obs t)} → Sub b → Sub (switchAllᵉ b)
  s-batchSync : ∀ {t} {b : Closed Γ t} → Sub b → Sub (batchSyncᵉ b)
  s-exhaust : ∀ {t} {b : Closed Γ (obs t)} → Sub b → Sub (exhaustAllᵉ b)

sub-total : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) → Sub e
sub-total (input i)         = s-input
sub-total (ofᵉ ts)          = s-of
sub-total emptyᵉ            = s-empty
sub-total (deferᵉ body)     = s-defer
sub-total (μᵉ body)         = s-μ
sub-total (mintᵉ body)      = s-mint
sub-total (takeᵉ c b)       = s-take (sub-total b)
sub-total (mapᵉ f b)        = s-map (sub-total b)
sub-total (scanᵉ f z b)     = s-scan (sub-total b)
sub-total (mergeAllᵉ l b)   = s-merge (sub-total b)
sub-total (switchAllᵉ b)    = s-switch (sub-total b)
sub-total (batchSyncᵉ b)    = s-batchSync (sub-total b)
sub-total (exhaustAllᵉ b)   = s-exhaust (sub-total b)
sub-total (varᵉ ())

-- the claim that the structural domain predicate is worth carrying:
-- that SOME closed term fails it, so that holding one is information.
StructuralDomainHasContent : Set
StructuralDomainHasContent =
  ∀ {n} {Γ : Ctx n} {t} → Σ (Closed Γ t) (λ e → ¬ Sub e)

structural-domain-has-content-false : StructuralDomainHasContent → ⊥
structural-domain-has-content-false w with w {0} {[]ⱽ} {natᵗ}
... | (e , ¬s) = ¬s (sub-total e)
