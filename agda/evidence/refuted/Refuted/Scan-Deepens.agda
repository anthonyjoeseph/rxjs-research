-- A FRAME'S OUTPUTS ARE NOT BOUNDED BY ANY FIGURE READ OFF THE FRAME AND
-- THE INCOMING BOUND.  A fold whose template re-wraps its accumulator
-- deepens it by exactly one per delivery, so the outputs of ONE frame,
-- entered under ONE bound, climb with the length of the burst.

-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make refuted`, claimed by
-- `Refuted.Main`.

-- WHY IT IS STATED HERE RATHER THAN QUOTED FROM `src`.  The statement
-- refuted is the strengthened return type a frame shelf is about to be
-- written against, and it is not in the tree yet — which is the whole
-- value of taking the witness first.  `ScanBounded` is deliberately
-- WEAKER than the shape it kills: it asks only that SOME bound exist,
-- and lets that bound depend on the seed as well as on the template, so
-- a refutation of it refutes every figure computed from less.

-- WHAT DEEPENS, AND IT IS SUBSTITUTION RATHER THAN EMISSION.  A value of
-- observable type is a closed expression, and substituting one for a
-- variable REIFIES it under `strmᵗ` — the one head the measure counts.
-- So a template mentioning its accumulator under a `strmᵗ` hands back an
-- accumulator one deeper, and the fold feeds that back in.  The climb is
-- in the ITERATION and not in the template, whose own reading is a
-- constant — and that constant is exactly what the dead shape reads.

-- AND THE CURRENCY CHANGE DID NOT RETIRE IT.  The tower this replaces
-- recorded the same dead route against the reading that priced what a
-- subtree would EMIT, and attributed it to that currency: a payload
-- admitted by its depth alone is one whose delivery count is
-- unconstrained.  A syntactic count removes the emission axis and leaves
-- this one standing, because the accumulator is a value the fold writes
-- BACK rather than a stream it prices.

-- THE BOUNDARY.  The rows are over `scanVals`, which is exactly the
-- second premise of the domain relation's `step-scan`, so the rows below
-- reach the frame step through that constructor and no other.  What it
-- does NOT establish is that a reachable store holds a shallow
-- accumulator beside a burst this long — a separate question, answered
-- elsewhere and in the affirmative, so the escape it left open is shut.
--
-- REFUTED: `Refuted.Scan-Reachable` — the same template RUN, reaching
--   the configuration this one only constructs.
module Refuted.Scan-Deepens where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; _⊔_; z≤n)
open import Data.Nat.Properties using (+-suc; +-identityʳ; n≮n)
-- the Σ is written APPLIED rather than through `Σ[ _ ∈ _ ]`, because
-- that form is a `syntax` declaration whose use site never mentions the
-- name it desugars to, and the import checker reads names textually
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂;
  trans; subst)

open import Rx.Exp using (Ty; Ctx; Exp; Tm; Val; Fn; Ren∈; ext∈; renExp; renTm; renTms;
  natᵗ; obs; _×ᵗ_; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ;
  inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ; applyFn)
open import Refuted.Apparatus using (obsDepthᵉ; obsDepthᵗ; obsDepthᵗˢ; obsDepthᵛ)
open import Rx.Evaluator using (scanVals)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

-- The measure's context implicit is not inferable from a value: at a
-- data type `Val Γ t` mentions no Γ at all, so every application below
-- pins it once through this alias rather than nine times inline.
depth : (t : Ty) → Val Γ₀ t → ℕ
depth t v = obsDepthᵛ {Γ = Γ₀} t v

----------------------------------------------------------------------
-- THE STATEMENT.  A bound on a fold's outputs that knows the template,
-- the seed and the bound the payloads came in under — everything except
-- how many of them there are.
----------------------------------------------------------------------

ScanBounded : Set
ScanBounded =
  ∀ {u s} (fn : Fn Γ₀ [] [] [] (u ×ᵗ s) u) (ac : Val Γ₀ u) (m : ℕ) →
    Σ ℕ (λ b → (vals : List (Val Γ₀ s)) →
      All (λ v → depth s v ≤ m) vals →
      All (λ v → depth u v ≤ b) (proj₁ (scanVals fn ac vals)))

----------------------------------------------------------------------
-- THE TEMPLATE THAT RE-WRAPS, AND THE SEED IT STARTS FROM.
----------------------------------------------------------------------

bump : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
bump = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

seed : Val Γ₀ (obs natᵗ)
seed = emptyᵉ

----------------------------------------------------------------------
-- APPARATUS: THE MEASURE DOES NOT SEE A RENAMING.
--
-- Substituting a value for a variable WEAKENS it into the binder's
-- contexts, so the accumulator handed back is wrapped in a renaming
-- rather than returned bare, and the row below cannot be `refl` without
-- this.  The measure reads Γ and the syntax and nothing the renaming
-- moves — a recursion variable and a deferred body both read nought —
-- so every clause is structural.  The same induction is written for
-- three other measures in the attic tower this replaces, which is where
-- the shape is from.
--
-- RECOVERY: git show 919f115:agda/src/Rx/Inputs-Below.agda carries it
--   for the guard's own reading, the clause-for-clause precedent.

mutual
  ren-depthᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (e : Exp Γ Δᵍ Δ Θ t) → obsDepthᵉ (renExp ρg ρd ρt e) ≡ obsDepthᵉ e
  ren-depthᵉ ρg ρd ρt (input i)       = refl
  ren-depthᵉ ρg ρd ρt (ofᵉ ts)        = ren-depthᵗˢ ρg ρd ρt ts
  ren-depthᵉ ρg ρd ρt emptyᵉ          = refl
  ren-depthᵉ ρg ρd ρt (mapᵉ f e)      =
    cong₂ _⊔_ (ren-depthᵗ ρg ρd (ext∈ ρt) f) (ren-depthᵉ ρg ρd ρt e)
  ren-depthᵉ ρg ρd ρt (takeᵉ c e)     =
    cong₂ _⊔_ (ren-depthᵗ ρg ρd ρt c) (ren-depthᵉ ρg ρd ρt e)
  ren-depthᵉ ρg ρd ρt (scanᵉ f z e)   =
    cong₂ _⊔_ (cong₂ _⊔_ (ren-depthᵗ ρg ρd (ext∈ ρt) f)
                         (ren-depthᵗ ρg ρd ρt z))
              (ren-depthᵉ ρg ρd ρt e)
  ren-depthᵉ ρg ρd ρt (mergeAllᵉ _ e) = ren-depthᵉ ρg ρd ρt e
  ren-depthᵉ ρg ρd ρt (switchAllᵉ e)  = ren-depthᵉ ρg ρd ρt e
  ren-depthᵉ ρg ρd ρt (exhaustAllᵉ e) = ren-depthᵉ ρg ρd ρt e
  ren-depthᵉ ρg ρd ρt (μᵉ e)          = ren-depthᵉ (ext∈ ρg) ρd ρt e
  ren-depthᵉ ρg ρd ρt (varᵉ x)        = refl
  ren-depthᵉ ρg ρd ρt (deferᵉ e)      = refl

  ren-depthᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (tm : Tm Γ Δᵍ Δ Θ t) → obsDepthᵗ (renTm ρg ρd ρt tm) ≡ obsDepthᵗ tm
  ren-depthᵗ ρg ρd ρt (varᵗ x)      = refl
  ren-depthᵗ ρg ρd ρt unit̂          = refl
  ren-depthᵗ ρg ρd ρt (bool̂ _)      = refl
  ren-depthᵗ ρg ρd ρt (nat̂ _)       = refl
  ren-depthᵗ ρg ρd ρt (pairᵗ a b)   =
    cong₂ _⊔_ (ren-depthᵗ ρg ρd ρt a) (ren-depthᵗ ρg ρd ρt b)
  ren-depthᵗ ρg ρd ρt (fstᵗ p)      = ren-depthᵗ ρg ρd ρt p
  ren-depthᵗ ρg ρd ρt (sndᵗ p)      = ren-depthᵗ ρg ρd ρt p
  ren-depthᵗ ρg ρd ρt (inlᵗ a)      = ren-depthᵗ ρg ρd ρt a
  ren-depthᵗ ρg ρd ρt (inrᵗ a)      = ren-depthᵗ ρg ρd ρt a
  ren-depthᵗ ρg ρd ρt (caseᵗ s l r) =
    cong suc (cong₂ _+_ (ren-depthᵗ ρg ρd ρt s)
                        (cong₂ _⊔_ (ren-depthᵗ ρg ρd (ext∈ ρt) l)
                                   (ren-depthᵗ ρg ρd (ext∈ ρt) r)))
  ren-depthᵗ ρg ρd ρt (ifᵗ c a b)   =
    cong₂ _⊔_ (cong₂ _⊔_ (ren-depthᵗ ρg ρd ρt c)
                         (ren-depthᵗ ρg ρd ρt a))
              (ren-depthᵗ ρg ρd ρt b)
  ren-depthᵗ ρg ρd ρt (primᵗ _ a)   = ren-depthᵗ ρg ρd ρt a
  ren-depthᵗ ρg ρd ρt (strmᵗ e)     = cong suc (ren-depthᵉ ρg ρd ρt e)

  ren-depthᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    obsDepthᵗˢ (renTms ρg ρd ρt ts) ≡ obsDepthᵗˢ ts
  ren-depthᵗˢ ρg ρd ρt []       = refl
  ren-depthᵗˢ ρg ρd ρt (y ∷ ys) =
    cong₂ _⊔_ (ren-depthᵗ ρg ρd ρt y) (ren-depthᵗˢ ρg ρd ρt ys)

-- LOAD-BEARING, AND IT IS THE WHOLE MECHANISM: one application, one
-- layer.  The row fails the moment substitution stops reifying an
-- observable under `strmᵗ`, which is the only reason the climb exists
step-deepens : ∀ (a : Val Γ₀ (obs natᵗ)) (v : Val Γ₀ natᵗ) →
  depth (obs natᵗ) (applyFn bump (a , v)) ≡ suc (depth (obs natᵗ) a)
step-deepens a v = cong suc (ren-depthᵉ (λ ()) (λ ()) (λ ()) a)

----------------------------------------------------------------------
-- THE BURST, AND WHERE THE DEEPEST OUTPUT SITS IN IT.
----------------------------------------------------------------------

rep : ℕ → List (Val Γ₀ natᵗ)
rep zero    = []
rep (suc k) = 0 ∷ rep k

-- DEGENERATE by design: every payload is data, so the incoming bound is
-- nought and the climb below cannot be read as depth the caller supplied
flat : ∀ (k : ℕ) → All (λ v → depth natᵗ v ≤ 0) (rep k)
flat zero    = []
flat (suc k) = z≤n ∷ flat k

-- LOAD-BEARING: the fold's final accumulator reads exactly the burst's
-- length above the seed's.  A template whose reading did not enter the
-- accumulator would leave this constant in k
final-deep : ∀ (k : ℕ) (a : Val Γ₀ (obs natᵗ)) →
  depth (obs natᵗ) (proj₂ (scanVals bump a (rep k)))
    ≡ k + depth (obs natᵗ) a
final-deep zero    a = refl
final-deep (suc k) a
  rewrite final-deep k (applyFn bump (a , 0))
        | step-deepens a 0
  = +-suc k (depth (obs natᵗ) a)

final-deep-seed : ∀ (k : ℕ) →
  depth (obs natᵗ) (proj₂ (scanVals bump seed (rep k))) ≡ k
final-deep-seed k = trans (final-deep k seed) (+-identityʳ k)

-- LOAD-BEARING: and that deepest accumulator IS one of the outputs, so a
-- bound on the output list is a bound on it.  Without this row the
-- crossing below would be about a quantity the statement never mentions
final-among : ∀ (k : ℕ) (a : Val Γ₀ (obs natᵗ)) →
  proj₂ (scanVals bump a (rep (suc k))) ∈ proj₁ (scanVals bump a (rep (suc k)))
final-among zero    a = here refl
final-among (suc k) a = there (final-among k (applyFn bump (a , 0)))

----------------------------------------------------------------------
-- THE CROSSING.  Whatever bound the statement offers, a burst one
-- longer than it carries an output deeper than it.
----------------------------------------------------------------------

scan-bounded-false : ScanBounded → ⊥
scan-bounded-false h with h bump seed 0
... | b , k =
  n≮n b (subst (λ d → d ≤ b) (final-deep-seed (suc b))
           (lookup (k (rep (suc b)) (flat (suc b))) (final-among b seed)))
