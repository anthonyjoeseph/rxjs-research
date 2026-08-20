------------------------------------------------------------------
-- THE STEP: `valHopSpn?` PRESERVED BY ONE APPLICATION OF A TEMPLATE.
--
-- Split out of `.Hop-Spine-Face` because it is a new family and not
-- mutual with anything there — the burst predicates consume this
-- module's `scanVals-hopSpn` as a finished fact, which is an import
-- rather than mutuality.  Keeping it here also stops every consumer of
-- `valHopSpn?` (`.Demand-Probe`'s wall of `refl` pins, in particular)
-- from paying for an induction over `Tm` that it never mentions.
--
-- WHAT IT PROVES.  One `applyFn` preserves the hereditary spine bound,
-- and the fold therefore preserves it across a whole burst.  The
-- induction is over the TERM, with the type as an index; the hereditary
-- conclusion is what makes the projections work, and `EnvPlug`'s
-- per-position disjunction is what makes `caseᵗ` statable.  Both
-- findings are recorded at their own declarations below.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Hop-Spine-Step where

open import Data.Bool using (Bool; true; false; T; _∧_)
open import Data.Bool.ListAction using (all)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; s≤s; z≤n)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-refl; ≤-reflexive;
                                       ^-monoʳ-≤; ^-monoˡ-≤; *-monoˡ-≤;
                                       ⊔-lub; m≤m⊔n; m≤n⊔m; n≤1+n;
                                       m≤m+n; *-identityˡ; +-identityʳ;
                                       +-monoʳ-≤)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Fin  using (Fin)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Rx.Exp   using (Ty; Ctx; Val; Fn; Tm; Exp; applyFn; evalWith; subΘExp;
                            varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                            inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
                            add; sub; mul; eqᵖ; ltᵖ; notᵖ; varIx; lookupEnv;
                            unitᵗ; boolᵗ; natᵗ; obs; _×ᵗ_; _+ᵗ_)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵛ; pmᵗ; pmᵉ)
open import Rx.Hop-Spine using (spnᵉ; spnᵛ)
open import Rx.Evaluator using (scanVals)
open import Verify-Budget-Sufficient.Measures using
  (∧-true; ∧-intro; T⇒≡true; T-to; hopD-evalWith; ifEq)
open import Verify-Budget-Sufficient.Hop-Spine-Face using
  (valHopSpn?; valHopSpn?-intro; valHopSpn?-hopD; B≤powB)
open import Verify-Budget-Sufficient.Hop-Spine-Sub using
  (EnvPlug; EnvPlug-mono; hopD-sub-spnᵉ)

------------------------------------------------------------------
-- THE STEP, AND IT IS ONE LEMMA OVER THE TERM.
--
-- A type-directed front end was tried first and it cannot reach this:
-- at `fstᵗ q` the result is `proj₁ (evalWith q env)`, whose spine is
-- STRICTLY SMALLER than the pair's, so a headline bound on the pair is
-- the wrong direction and only the HEREDITARY predicate at the pair
-- supplies the component.  So the induction is over the TERM with the
-- hereditary predicate as its conclusion, and the type follows as an
-- index.  Doing it this way subsumes the pair arm, the sum arm and the
-- zero-slope `obs` case, which were three separate obligations before.
--
-- WHY THE CONCLUSION LANDS BACK AT `B`, which is the whole difficulty.
-- Two earlier shapes concluded at a DERIVED coefficient and decayed by
-- a factor per fold step with nothing to recover it (the record is in
-- `EnvPlug`'s header).  The repair is that the drag is spent AT THE
-- LEAF, not at the top: an `obs` leaf of the result is `subΘExp []
-- env e` for a `strmᵗ e` in the term, `hopD-subΘᵉ` (.Measures, PROVEN)
-- prices it as `hopDᵉ e + Σⱼ pmⱼ(e) · hopDᵛ σⱼ`, and every plugged
-- value's own spine sits at least ONE BELOW the leaf's — the reified
-- value lands under an `Exp` node, and that node's own `suc` is the
-- unit.  So `Σⱼ pmⱼ(e) · B · Q ^ spnᵛ σⱼ ≤ P · B · Q ^ (spn − 1)`, the
-- leading `hopDᵉ e ≤ B` rides along, and `1 + P ≤ 2 + P = Q` closes it
-- exactly.  Nothing decays, so `caseᵗ` can extend the environment with
-- a value carried at the SAME `B` as the outer ones.
------------------------------------------------------------------

-- THE LOOKUP.  A position the term actually MENTIONS hands back the
-- hereditary receipt under either disjunct: the first carries it
-- outright, and the second gives `hopDᵛ v ≤ B` once the slope is at
-- least one, which `valHopSpn?-intro` lifts.  So the disjunction costs
-- the copied leaves nothing.
envPlug-lookup : ∀ {n} {Γ : Ctx n} {Θ t} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (Ps : ℕ → ℕ) (σ : All (Val Γ) Θ) → EnvPlug V η P B σ Ps → (z : t ∈ Θ) →
  1 ≤ Ps (varIx z) →
  valHopSpn? V η P B t (lookupEnv σ z) ≡ true
envPlug-lookup V η P B Ps (v ∷ᵃ σ) (inl (_ , hv) , _) (here refl) hit = hv
envPlug-lookup V η P B Ps (_∷ᵃ_ {x = t} v σ) (inr hprod , _) (here refl) hit =
  valHopSpn?-intro V η P B t v
    (≤-trans (≤-trans (≤-reflexive (sym (*-identityˡ (hopDᵛ V η t v))))
                      (*-monoˡ-≤ (hopDᵛ V η t v) hit))
             hprod)
envPlug-lookup V η P B Ps (v ∷ᵃ σ) (_ , hσ) (there z) hit =
  envPlug-lookup V η P B (λ j → Ps (suc j)) σ hσ z hit

postulate
  -- THE CLAUSE THAT EXTENDS THE ENVIRONMENT, and the one residue of the
  -- whole family.  What it needs is `EnvPlug` at the branch's own
  -- environment `x ∷ᵃ env`, where `x` is the scrutinee's evaluated
  -- payload — so, at position 0, one of the two disjuncts for the slope
  -- `pmᵗ V 0 l`.  The receipt half is FREE: the recursive call on `sc`
  -- hands back `valHopSpn?` of its value directly, which is what making
  -- the conclusion hereditary bought.  What is open is the slope.
  --
  -- THE TWO EXTREMES EACH CLOSE, AND BY DIFFERENT DISJUNCTS.
  --   * `sc` MENTIONS an environment position j.  Then `pmᵗ V j (caseᵗ
  --     sc l r)` contains `(pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1) * pmᵗ V j sc`, so
  --     the PARENT's slope at j already dominates `pmᵗ V 0 l`, and the
  --     parent's own condition bounds it.  Disjunct (a).
  --   * `sc` is CLOSED.  Then `hopDᵛ x ≤ hopDᵗ sc` with nothing added,
  --     and `hopDᵗ (caseᵗ sc l r)`'s second summand already paid
  --     `(pmᵗ V 0 l ⊔ … ⊔ 1) * hopDᵗ sc ≤ B`.  Disjunct (b).
  --
  -- WHAT IS OPEN is the MIXED case: `sc` mentioning several positions,
  -- some of them held under disjunct (a).  Pricing `x` through
  -- `hopD-evalWith` (.Measures) then leaves `Σⱼ pmᵗ V j sc * hopDᵛ envⱼ`,
  -- and a disjunct-(a) position bounds `hopDᵛ envⱼ` only by `Q ^ spnᵛ *
  -- B`, so the sum runs to M * B and disjunct (b) fails at M ≥ 2 exactly
  -- as it does upstream.  The mechanism that fixes it is a PER-POSITION
  -- BUDGET in `EnvPlug` — the closed-scrutinee arm wants `x` carried at
  -- `B / (c * C)` rather than at `B` — and that is a restatement of the
  -- environment condition, not a grind, which is why this row is
  -- DIFFICULTY and not GRINDABLE.
  --
  -- x DEAD ROUTE 2026-08-20: the four-piece `maxW`/`EnvSpn` plan that
  -- stood here.  `maxW` is refuted one clause into the substitution
  -- induction (`mapᵉ` needs a sum of maxes under a max of sums; the
  -- record is at `hopD-sub-spnᵉ` in .Hop-Spine-Sub), and with it goes the
  -- claim that `EnvPlug`'s disjunction "could not be spent".  It CAN:
  -- `envPlug-plug` spends it at every plug site, and `hopD-sub-spnᵉ`
  -- discharged the sibling `strmᵗ` leaf outright with `EnvPlug`
  -- unchanged.  The two leaves did NOT want the same apparatus.
  --
  -- x SUPERSEDED 2026-08-20 — "M positions need `1 + M * P ≤ Q`" is a
  -- real obstruction, but only for a bound that SUMS over positions.
  -- The coefficient-carrying induction never forms that sum, so the
  -- environment's LENGTH does not enter it; the M-dependence survives
  -- only in this clause, and only through `hopD-evalWith`.
  evalWith-hopSpn-case : ∀ {n} {Γ : Ctx n} {Θ a b u} (V : ℕ) (η : Fin n → ℕ)
    (P B : ℕ) (sc : Tm Γ [] [] Θ (a +ᵗ b))
    (l : Tm Γ [] [] (a ∷ Θ) u) (r : Tm Γ [] [] (b ∷ Θ) u)
    (env : All (Val Γ) Θ) →
    hopDᵗ V η (caseᵗ sc l r) ≤ B →
    EnvPlug V η P B env (λ j → pmᵗ V j (caseᵗ sc l r)) →
    valHopSpn? V η P B u (evalWith (caseᵗ sc l r) env) ≡ true

------------------------------------------------------------------
-- THE STEP, AS A REAL BODY.  Eleven of the thirteen clauses are
-- structure: the copied leaves read the environment through
-- `envPlug-lookup`, the projections take a conjunct of the pair's own
-- receipt — which is the whole reason the conclusion is hereditary —
-- and every recursive call reuses the parent's environment condition
-- through `EnvPlug-mono`, since a subterm's slope is under its
-- parent's at every index.  `hopDᵗ`'s own clauses supply the recursive
-- bound the same way.
------------------------------------------------------------------

evalWith-hopSpn : ∀ {n} {Γ : Ctx n} {Θ u} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (tm : Tm Γ [] [] Θ u) (env : All (Val Γ) Θ) →
  hopDᵗ V η tm ≤ B →
  EnvPlug V η P B env (λ j → pmᵗ V j tm) →
  valHopSpn? V η P B u (evalWith tm env) ≡ true
evalWith-hopSpn {Γ = Γ} V η P B (varᵗ x) env hB hσ =
  envPlug-lookup V η P B
    (λ j → pmᵗ {Γ = Γ} {Δᵍ = []} {Δ = []} V j (varᵗ x)) env hσ x
    (ifEq (varIx x) (varIx x) refl)
evalWith-hopSpn V η P B unit̂     env hB hσ = refl
evalWith-hopSpn V η P B (bool̂ _) env hB hσ = refl
evalWith-hopSpn V η P B (nat̂ _)  env hB hσ = refl
evalWith-hopSpn V η P B (pairᵗ a b) env hB hσ =
  ∧-intro (evalWith-hopSpn V η P B a env
             (≤-trans (m≤m⊔n (hopDᵗ V η a) (hopDᵗ V η b)) hB)
             (EnvPlug-mono V η P B env (λ j → pmᵗ V j (pairᵗ a b))
                           (λ j → pmᵗ V j a)
                           (λ j → m≤m⊔n (pmᵗ V j a) (pmᵗ V j b)) hσ))
          (evalWith-hopSpn V η P B b env
             (≤-trans (m≤n⊔m (hopDᵗ V η a) (hopDᵗ V η b)) hB)
             (EnvPlug-mono V η P B env (λ j → pmᵗ V j (pairᵗ a b))
                           (λ j → pmᵗ V j b)
                           (λ j → m≤n⊔m (pmᵗ V j a) (pmᵗ V j b)) hσ))
evalWith-hopSpn V η P B (fstᵗ q) env hB hσ =
  proj₁ (∧-true _ _ (evalWith-hopSpn V η P B q env hB hσ))
evalWith-hopSpn V η P B (sndᵗ q) env hB hσ =
  proj₂ (∧-true _ _ (evalWith-hopSpn V η P B q env hB hσ))
evalWith-hopSpn V η P B (inlᵗ a) env hB hσ = evalWith-hopSpn V η P B a env hB hσ
evalWith-hopSpn V η P B (inrᵗ a) env hB hσ = evalWith-hopSpn V η P B a env hB hσ
evalWith-hopSpn V η P B (caseᵗ sc l r) env hB hσ =
  evalWith-hopSpn-case V η P B sc l r env hB hσ
evalWith-hopSpn V η P B (ifᵗ c a b) env hB hσ with evalWith c env
... | true  = evalWith-hopSpn V η P B a env
                (≤-trans (m≤m⊔n (hopDᵗ V η a) (hopDᵗ V η b)) hB)
                (EnvPlug-mono V η P B env (λ j → pmᵗ V j (ifᵗ c a b))
                              (λ j → pmᵗ V j a)
                              (λ j → m≤m⊔n (pmᵗ V j a) (pmᵗ V j b)) hσ)
... | false = evalWith-hopSpn V η P B b env
                (≤-trans (m≤n⊔m (hopDᵗ V η a) (hopDᵗ V η b)) hB)
                (EnvPlug-mono V η P B env (λ j → pmᵗ V j (ifᵗ c a b))
                              (λ j → pmᵗ V j b)
                              (λ j → m≤n⊔m (pmᵗ V j a) (pmᵗ V j b)) hσ)
-- one clause per operator, since the RESULT type is what makes the
-- predicate `true` — every PrimOp lands in natᵗ or boolᵗ
evalWith-hopSpn V η P B (primᵗ add  a) env hB hσ = refl
evalWith-hopSpn V η P B (primᵗ sub  a) env hB hσ = refl
evalWith-hopSpn V η P B (primᵗ mul  a) env hB hσ = refl
evalWith-hopSpn V η P B (primᵗ eqᵖ  a) env hB hσ = refl
evalWith-hopSpn V η P B (primᵗ ltᵖ  a) env hB hσ = refl
evalWith-hopSpn V η P B (primᵗ notᵖ a) env hB hσ = refl
-- a CLOSED template is its own value, so the headline receipt is the
-- whole story and `B≤powB` is the lift
evalWith-hopSpn V η P B (strmᵗ e) []ᵃ hB hσ =
  T⇒≡true _ (≤⇒≤ᵇ (≤-trans hB (B≤powB P B (spnᵉ e))))
-- THE BUILT LEAF, and the only place the drag is actually spent.
-- `closeUnderFn` IS `subΘExp []`, so this is exactly the substitution
-- the induction in .Hop-Spine-Sub prices; the coefficient starts at 1
-- and every clause of that induction hands its own on down.
evalWith-hopSpn V η P B (strmᵗ e) (v ∷ᵃ vs) hB hσ =
  T⇒≡true _ (≤⇒≤ᵇ
    (≤-trans (≤-reflexive (sym (*-identityˡ (hopDᵉ V η (subΘExp [] (v ∷ᵃ vs) e)))))
      (hopD-sub-spnᵉ V η P B 1 [] (v ∷ᵃ vs) e
        (≤-trans (≤-reflexive (*-identityˡ (hopDᵉ V η e))) hB)
        (EnvPlug-mono V η P B (v ∷ᵃ vs) (λ j → pmᵉ V j e)
                      (λ j → 1 * pmᵉ V j e)
                      (λ j → ≤-reflexive (*-identityˡ (pmᵉ V j e))) hσ))))

-- and the scan fold's own shape: the argument is the pair the fold hands
-- in, at the single position the fn binds
applyFn-hopSpn : ∀ {n} {Γ : Ctx n} {s u} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac : Val Γ u) (v : Val Γ s) →
  pmᵗ V 0 fn ≤ P →
  hopDᵗ V η fn ≤ B →
  valHopSpn? V η P B u ac ≡ true →
  valHopSpn? V η P B s v ≡ true →
  valHopSpn? V η P B u (applyFn fn (ac , v)) ≡ true
applyFn-hopSpn V η P B fn ac v hP hB hac hv =
  evalWith-hopSpn V η P B fn ((ac , v) ∷ᵃ []ᵃ) hB
    (inl (hP , ∧-intro hac hv) , tt)

------------------------------------------------------------------
-- THE FOLD.  Mechanical over the list, exactly `scanVals-ofW`'s shape
-- (.Wet/Part3) — the same fold, the same `all`, the same ∧-intro — with
-- the ⊔-shaped invariant replaced by the hereditary one.  Every output
-- IS an accumulator, so the outputs' receipt and the last accumulator's
-- are the same fact collected twice.
------------------------------------------------------------------

scanVals-hopSpn : ∀ {n} {Γ : Ctx n} {s u} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac : Val Γ u) (vs : List (Val Γ s)) →
  pmᵗ V 0 fn ≤ P →
  hopDᵗ V η fn ≤ B →
  valHopSpn? V η P B u ac ≡ true →
  all (valHopSpn? V η P B _) vs ≡ true →
  (valHopSpn? V η P B u (proj₂ (scanVals fn ac vs)) ≡ true)
  × (all (valHopSpn? V η P B u) (proj₁ (scanVals fn ac vs)) ≡ true)
scanVals-hopSpn V η P B fn ac []       hP hB hac _ = hac , refl
scanVals-hopSpn {s = s} V η P B fn ac (v ∷ vs) hP hB hac h =
  proj₁ IH , ∧-intro hac′ (proj₂ IH)
  where
  hv  : valHopSpn? V η P B s v ≡ true
  hv  = proj₁ (∧-true (valHopSpn? V η P B s v) _ h)
  hac′ = applyFn-hopSpn V η P B fn ac v hP hB hac hv
  IH  = scanVals-hopSpn V η P B fn (applyFn fn (ac , v)) vs hP hB hac′
          (proj₂ (∧-true (valHopSpn? V η P B s v) _ h))