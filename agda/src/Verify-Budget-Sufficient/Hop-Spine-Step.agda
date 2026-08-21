------------------------------------------------------------------
-- THE STEP: `valHopSpn?` PRESERVED BY ONE APPLICATION OF A TEMPLATE.
--
-- Split out of `.Hop-Spine-Face` because it is a new family and not
-- mutual with anything there — the burst predicates consume this
-- module's `scanVals-hopSpn` as a finished fact, which is an import
-- rather than mutuality.  Keeping it here also stops every consumer of
-- `valHopSpn?` from paying for an induction over `Tm` that it never
-- mentions.  The consumer that made the cost visible was a probe's wall
-- of `refl` pins; it has since expired with its targets and been deleted,
-- so the saving is now only the ordinary one, but the split is what keeps
-- this family importable without the `Tm` induction.
--
-- WHAT IT PROVES.  One `applyFn` preserves the hereditary spine bound,
-- and the fold therefore preserves it across a whole burst.  Fully
-- discharged: no postulate remains in this family.
--
-- THE INDUCTION IS OVER THE TERM, with the type as an index.  A
-- type-directed front end cannot host it: at `fstᵗ q` the result is
-- `proj₁ (evalWith q env)`, whose spine is STRICTLY SMALLER than the
-- pair's, so a headline bound on the pair points the wrong way and only
-- the HEREDITARY predicate at the pair supplies the component.
--
-- THERE ARE TWO INDUCTIONS, and the split is forced rather than chosen.
-- `evalWith-hopSpn` concludes the plain receipt and takes `EnvPlug`'s
-- per-position DISJUNCTION, which is the only form the fold can supply
-- at the top — an unscaled receipt plus a slope under `P`.
-- `evalWith-hopSpnC` concludes a receipt SCALED by a coefficient and
-- takes `EnvC`, the scaled condition, which is what `caseᵗ` needs for
-- the value it pushes onto the environment: the branch reads that value
-- through `pmᵗ V 0 l`, a template-internal slope no hypothesis bounds.
-- Neither subsumes the other — the first cannot scale a receipt, the
-- second cannot be met at the top — and `case-small`/`case-big` are
-- where the two meet, split on how the branch coefficient compares
-- with `P`.  The reasons are recorded at those declarations.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Hop-Spine-Step where

open import Data.Bool using (true; false)
open import Data.Bool.ListAction using (all)
open import Data.Nat  using (ℕ; suc; _*_; _⊔_; _≤_; _≤?_)
open import Data.Nat.Properties using (≤⇒≤ᵇ; ≰⇒>; ≤-trans; ≤-reflexive; m≤m⊔n; m≤n⊔m; m≤m+n; m≤n+m; *-identityˡ; *-identityʳ;
  *-assoc; *-monoʳ-≤; *-zeroʳ)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Fin  using (Fin)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)

open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Rx.Exp   using (Ctx; Val; Fn; Tm; applyFn; evalWith; subΘExp; varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
  inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ; add; sub; mul; eqᵖ; ltᵖ; notᵖ; varIx; lookupEnv; _×ᵗ_;
  _+ᵗ_)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; pmᵗ; pmᵉ)
open import Rx.Hop-Spine using (spnᵉ)
open import Rx.Evaluator using (scanVals)
open import Verify-Budget-Sufficient.Measures using
  (∧-true)
open import Verify-Budget-Sufficient.Hop-Spine-Face using
  (valHopSpn?; B≤powB)
open import Verify-Budget-Sufficient.Hop-Spine-Sub using
  (EnvPlug; EnvPlug-mono; hopD-sub-spnᵉ; ⊔₁+; ⊔₂+;
   ≤2nd; 1≤C; big-forces-zero; envPlug⇒envC;
   valHopSpnC?; valHopSpnC?-mono; valHopSpnC?-one;
   EnvC; EnvC-mono; envC-lookup; envC⇒envPlug)
open import Decide using (T⇒≡true; ifEq; ∧-intro)

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
-- the SCALED disjunct hands back the unscaled receipt as soon as the
-- slope is at least one, which a MENTIONED position always is
envPlug-lookup V η P B Ps (_∷ᵃ_ {x = t} v σ) (inr hsc , _) (here refl) hit =
  valHopSpnC?-one V η P B t v
    (valHopSpnC?-mono V η P B 1 (Ps 0) t v hit hsc)
envPlug-lookup V η P B Ps (v ∷ᵃ σ) (_ , hσ) (there z) hit =
  envPlug-lookup V η P B (λ j → Ps (suc j)) σ hσ z hit

------------------------------------------------------------------
-- THE SAME INDUCTION, CARRYING A COEFFICIENT.  This is what the outer
-- `caseᵗ` clause spends on its SCRUTINEE, and the reason it exists is
-- that `caseᵗ` pushes the scrutinee's value onto the environment where
-- the branch reads it through `pmᵗ V 0 l` — a template-internal slope
-- that no hypothesis bounds.  Scaling the receipt by the coefficient
-- carries that slope, and every clause hands its own coefficient down:
-- the scrutinee runs at `c * C`, which is exactly the factor `pmᵗ`'s own
-- `caseᵗ` clause applies to it, so the branch's position-0 requirement
-- follows by monotonicity ALONE.  No case analysis, no sum over
-- positions, no dependence on the environment's length.
--
-- Why this cannot simply REPLACE `evalWith-hopSpn`: its `varᵗ` clause
-- copies an environment value into a scaled conclusion, so its
-- environment condition has to be the scaled receipt (`EnvC`) rather
-- than a slope bound plus an unscaled one.  The fold supplies the
-- latter, and at the top the two differ by a factor of `P`.  So the
-- unscaled lemma stays the outer interface and this one is its engine.
------------------------------------------------------------------

evalWith-hopSpnC : ∀ {n} {Γ : Ctx n} {Θ u} (V : ℕ) (η : Fin n → ℕ)
  (P B c : ℕ) (tm : Tm Γ [] [] Θ u) (env : All (Val Γ) Θ) →
  c * hopDᵗ V η tm ≤ B →
  EnvC V η P B env (λ j → c * pmᵗ V j tm) →
  valHopSpnC? V η P B c u (evalWith tm env) ≡ true
evalWith-hopSpnC {Γ = Γ} {u = u} V η P B c (varᵗ x) env hB hσ =
  valHopSpnC?-mono V η P B c
    (c * pmᵗ {Γ = Γ} {Δᵍ = []} {Δ = []} V (varIx x) (varᵗ x))
    u (lookupEnv env x)
    (≤-trans (≤-reflexive (sym (*-identityʳ c)))
             (*-monoʳ-≤ c (ifEq (varIx x) (varIx x) refl)))
    (envC-lookup V η P B
      (λ j → c * pmᵗ {Γ = Γ} {Δᵍ = []} {Δ = []} V j (varᵗ x)) env hσ x)
evalWith-hopSpnC V η P B c unit̂     env hB hσ = refl
evalWith-hopSpnC V η P B c (bool̂ _) env hB hσ = refl
evalWith-hopSpnC V η P B c (nat̂ _)  env hB hσ = refl
evalWith-hopSpnC V η P B c (pairᵗ a b) env hB hσ =
  ∧-intro (evalWith-hopSpnC V η P B c a env
             (≤-trans (*-monoʳ-≤ c (m≤m⊔n (hopDᵗ V η a) (hopDᵗ V η b))) hB)
             (EnvC-mono V η P B env (λ j → c * pmᵗ V j (pairᵗ a b))
                        (λ j → c * pmᵗ V j a)
                        (λ j → *-monoʳ-≤ c (m≤m⊔n (pmᵗ V j a) (pmᵗ V j b))) hσ))
          (evalWith-hopSpnC V η P B c b env
             (≤-trans (*-monoʳ-≤ c (m≤n⊔m (hopDᵗ V η a) (hopDᵗ V η b))) hB)
             (EnvC-mono V η P B env (λ j → c * pmᵗ V j (pairᵗ a b))
                        (λ j → c * pmᵗ V j b)
                        (λ j → *-monoʳ-≤ c (m≤n⊔m (pmᵗ V j a) (pmᵗ V j b))) hσ))
evalWith-hopSpnC V η P B c (fstᵗ q) env hB hσ =
  proj₁ (∧-true _ _ (evalWith-hopSpnC V η P B c q env hB hσ))
evalWith-hopSpnC V η P B c (sndᵗ q) env hB hσ =
  proj₂ (∧-true _ _ (evalWith-hopSpnC V η P B c q env hB hσ))
evalWith-hopSpnC V η P B c (inlᵗ a) env hB hσ = evalWith-hopSpnC V η P B c a env hB hσ
evalWith-hopSpnC V η P B c (inrᵗ a) env hB hσ = evalWith-hopSpnC V η P B c a env hB hσ
-- the scrutinee's value and its SCALED receipt are abstracted together,
-- so the branch sees the receipt already specialised to its injection
evalWith-hopSpnC V η P B c (caseᵗ {s = s} {t = t} sc l r) env hB hσ
  with evalWith sc env
     | evalWith-hopSpnC V η P B (c * (pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1)) sc env
         (≤-trans (≤-reflexive
                    (*-assoc c (pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1) (hopDᵗ V η sc)))
                  (≤-trans (*-monoʳ-≤ c
                             (m≤n+m ((pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1) * hopDᵗ V η sc)
                                    (hopDᵗ V η l ⊔ hopDᵗ V η r))) hB))
         (EnvC-mono V η P B env (λ j → c * pmᵗ V j (caseᵗ sc l r))
                    (λ j → (c * (pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1)) * pmᵗ V j sc)
                    (λ j → ≤-trans (≤-reflexive
                                     (*-assoc c (pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1)
                                                (pmᵗ V j sc)))
                                   (*-monoʳ-≤ c (m≤n+m _ _))) hσ)
... | inl x | ihsc =
  evalWith-hopSpnC V η P B c l (x ∷ᵃ env)
    (≤-trans (*-monoʳ-≤ c (≤-trans (m≤m⊔n (hopDᵗ V η l) (hopDᵗ V η r))
                                   (m≤m+n LR (C * hopDᵗ V η sc)))) hB)
    ( valHopSpnC?-mono V η P B (c * pmᵗ V 0 l) (c * C) s x
        (*-monoʳ-≤ c (≤-trans (m≤m⊔n (pmᵗ V 0 l) (pmᵗ V 0 r))
                              (m≤m⊔n (pmᵗ V 0 l ⊔ pmᵗ V 0 r) 1))) ihsc
    , EnvC-mono V η P B env (λ j → c * pmᵗ V j (caseᵗ sc l r))
                (λ j → c * pmᵗ V (suc j) l)
                (λ j → *-monoʳ-≤ c (⊔₁+ (pmᵗ V (suc j) l) (pmᵗ V (suc j) r)
                                        (C * pmᵗ V j sc))) hσ )
  where
  C  = pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1
  LR = hopDᵗ V η l ⊔ hopDᵗ V η r
... | inr y | ihsc =
  evalWith-hopSpnC V η P B c r (y ∷ᵃ env)
    (≤-trans (*-monoʳ-≤ c (≤-trans (m≤n⊔m (hopDᵗ V η l) (hopDᵗ V η r))
                                   (m≤m+n LR (C * hopDᵗ V η sc)))) hB)
    ( valHopSpnC?-mono V η P B (c * pmᵗ V 0 r) (c * C) t y
        (*-monoʳ-≤ c (≤-trans (m≤n⊔m (pmᵗ V 0 l) (pmᵗ V 0 r))
                              (m≤m⊔n (pmᵗ V 0 l ⊔ pmᵗ V 0 r) 1))) ihsc
    , EnvC-mono V η P B env (λ j → c * pmᵗ V j (caseᵗ sc l r))
                (λ j → c * pmᵗ V (suc j) r)
                (λ j → *-monoʳ-≤ c (⊔₂+ (pmᵗ V (suc j) l) (pmᵗ V (suc j) r)
                                        (C * pmᵗ V j sc))) hσ )
  where
  C  = pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1
  LR = hopDᵗ V η l ⊔ hopDᵗ V η r
evalWith-hopSpnC V η P B c (ifᵗ cnd a b) env hB hσ with evalWith cnd env
... | true  = evalWith-hopSpnC V η P B c a env
                (≤-trans (*-monoʳ-≤ c (m≤m⊔n (hopDᵗ V η a) (hopDᵗ V η b))) hB)
                (EnvC-mono V η P B env (λ j → c * pmᵗ V j (ifᵗ cnd a b))
                           (λ j → c * pmᵗ V j a)
                           (λ j → *-monoʳ-≤ c (m≤m⊔n _ _)) hσ)
... | false = evalWith-hopSpnC V η P B c b env
                (≤-trans (*-monoʳ-≤ c (m≤n⊔m (hopDᵗ V η a) (hopDᵗ V η b))) hB)
                (EnvC-mono V η P B env (λ j → c * pmᵗ V j (ifᵗ cnd a b))
                           (λ j → c * pmᵗ V j b)
                           (λ j → *-monoʳ-≤ c (m≤n⊔m _ _)) hσ)
evalWith-hopSpnC V η P B c (primᵗ add  a) env hB hσ = refl
evalWith-hopSpnC V η P B c (primᵗ sub  a) env hB hσ = refl
evalWith-hopSpnC V η P B c (primᵗ mul  a) env hB hσ = refl
evalWith-hopSpnC V η P B c (primᵗ eqᵖ  a) env hB hσ = refl
evalWith-hopSpnC V η P B c (primᵗ ltᵖ  a) env hB hσ = refl
evalWith-hopSpnC V η P B c (primᵗ notᵖ a) env hB hσ = refl
evalWith-hopSpnC V η P B c (strmᵗ e) []ᵃ hB hσ =
  T⇒≡true _ (≤⇒≤ᵇ (≤-trans hB (B≤powB P B (spnᵉ e))))
evalWith-hopSpnC V η P B c (strmᵗ e) (v ∷ᵃ vs) hB hσ =
  T⇒≡true _ (≤⇒≤ᵇ
    (hopD-sub-spnᵉ V η P B c [] (v ∷ᵃ vs) e hB
      (envC⇒envPlug V η P B (v ∷ᵃ vs) (λ j → c * pmᵉ V j e) hσ)))

------------------------------------------------------------------
-- THE STEP, AS A REAL BODY — every clause.  Most of them are pure
-- structure: the copied leaves read the environment through
-- `envPlug-lookup`, the projections take a conjunct of the pair's own
-- receipt — which is the whole reason the conclusion is hereditary —
-- and every recursive call reuses the parent's environment condition
-- through `EnvPlug-mono`, since a subterm's slope is under its
-- parent's at every index.  `hopDᵗ`'s own clauses supply the recursive
-- bound the same way.
------------------------------------------------------------------

mutual
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
  evalWith-hopSpn V η P B (caseᵗ sc l r) env hB hσ
    with (pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1) ≤? P
  ... | yes hle = case-small V η P B sc l r env hB hσ hle
  ... | no  hgt = case-big   V η P B sc l r env hB hσ (≰⇒> hgt)
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

  ------------------------------------------------------------------
  -- `caseᵗ`, SPLIT ON THE BRANCH COEFFICIENT, and the split is forced.
  -- The branch reads the pushed value through `pmᵗ V 0 l`, so position 0
  -- of its environment needs one of `EnvPlug`'s two disjuncts, and which
  -- one is available depends on how that slope compares with `P`:
  --
  --   * `C ≤ P` — the FIRST disjunct.  `pmᵗ V 0 l ≤ C ≤ P` is the slope
  --     bound outright, and the unscaled receipt on the pushed value is
  --     the plain recursive call on the scrutinee.  Nothing is scaled.
  --   * `P < C` — the SECOND.  No slope bound is available at all, so
  --     the value must arrive already scaled by `C`, which is
  --     `evalWith-hopSpnC`'s conclusion.
  --
  -- The two are genuinely different proofs, not two cases of one, and
  -- neither covers the other: the first cannot scale a receipt and the
  -- second cannot bound a slope.
  ------------------------------------------------------------------

  -- THE SMALL BRANCH.  Everything runs unscaled; `C ≤ P` does all the
  -- work, since it bounds `pmᵗ V 0 l` and `pmᵗ V 0 r` at once.
  case-small : ∀ {n} {Γ : Ctx n} {Θ a b u} (V : ℕ) (η : Fin n → ℕ)
    (P B : ℕ) (sc : Tm Γ [] [] Θ (a +ᵗ b))
    (l : Tm Γ [] [] (a ∷ Θ) u) (r : Tm Γ [] [] (b ∷ Θ) u)
    (env : All (Val Γ) Θ) →
    hopDᵗ V η (caseᵗ sc l r) ≤ B →
    EnvPlug V η P B env (λ j → pmᵗ V j (caseᵗ sc l r)) →
    (pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1) ≤ P →
    valHopSpn? V η P B u (evalWith (caseᵗ sc l r) env) ≡ true
  case-small V η P B sc l r env hB hσ hle
    with evalWith sc env
       | evalWith-hopSpn V η P B sc env
           (≤-trans (≤2nd (hopDᵗ V η l ⊔ hopDᵗ V η r)
                          (pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1) (hopDᵗ V η sc)
                          (1≤C (pmᵗ V 0 l ⊔ pmᵗ V 0 r))) hB)
           (EnvPlug-mono V η P B env (λ j → pmᵗ V j (caseᵗ sc l r))
                         (λ j → pmᵗ V j sc)
                         (λ j → ≤2nd _ (pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1) (pmᵗ V j sc)
                                      (1≤C (pmᵗ V 0 l ⊔ pmᵗ V 0 r))) hσ)
  ... | inl x | ihsc =
    evalWith-hopSpn V η P B l (x ∷ᵃ env)
      (≤-trans (≤-trans (m≤m⊔n (hopDᵗ V η l) (hopDᵗ V η r))
                        (m≤m+n (hopDᵗ V η l ⊔ hopDᵗ V η r) (C * hopDᵗ V η sc))) hB)
      ( inl (≤-trans (≤-trans (m≤m⊔n (pmᵗ V 0 l) (pmᵗ V 0 r))
                              (m≤m⊔n (pmᵗ V 0 l ⊔ pmᵗ V 0 r) 1)) hle
            , ihsc)
      , EnvPlug-mono V η P B env (λ j → pmᵗ V j (caseᵗ sc l r))
                     (λ j → pmᵗ V (suc j) l)
                     (λ j → ⊔₁+ (pmᵗ V (suc j) l) (pmᵗ V (suc j) r)
                                (C * pmᵗ V j sc)) hσ )
    where C = pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1
  ... | inr y | ihsc =
    evalWith-hopSpn V η P B r (y ∷ᵃ env)
      (≤-trans (≤-trans (m≤n⊔m (hopDᵗ V η l) (hopDᵗ V η r))
                        (m≤m+n (hopDᵗ V η l ⊔ hopDᵗ V η r) (C * hopDᵗ V η sc))) hB)
      ( inl (≤-trans (≤-trans (m≤n⊔m (pmᵗ V 0 l) (pmᵗ V 0 r))
                              (m≤m⊔n (pmᵗ V 0 l ⊔ pmᵗ V 0 r) 1)) hle
            , ihsc)
      , EnvPlug-mono V η P B env (λ j → pmᵗ V j (caseᵗ sc l r))
                     (λ j → pmᵗ V (suc j) r)
                     (λ j → ⊔₂+ (pmᵗ V (suc j) l) (pmᵗ V (suc j) r)
                                (C * pmᵗ V j sc)) hσ )
    where C = pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1

  -- THE BIG BRANCH.  `envPlug⇒envC` is where `P < C` is spent: a
  -- position the scrutinee mentions has parent slope at least `C > P`,
  -- so it cannot be held under the unscaled disjunct, and a position it
  -- does not mention arrives at coefficient zero.
  case-big : ∀ {n} {Γ : Ctx n} {Θ a b u} (V : ℕ) (η : Fin n → ℕ)
    (P B : ℕ) (sc : Tm Γ [] [] Θ (a +ᵗ b))
    (l : Tm Γ [] [] (a ∷ Θ) u) (r : Tm Γ [] [] (b ∷ Θ) u)
    (env : All (Val Γ) Θ) →
    hopDᵗ V η (caseᵗ sc l r) ≤ B →
    EnvPlug V η P B env (λ j → pmᵗ V j (caseᵗ sc l r)) →
    suc P ≤ (pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1) →
    valHopSpn? V η P B u (evalWith (caseᵗ sc l r) env) ≡ true
  case-big V η P B sc l r env hB hσ hgt
    with evalWith sc env
       | evalWith-hopSpnC V η P B (pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1) sc env
           (≤-trans (m≤n+m ((pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1) * hopDᵗ V η sc)
                           (hopDᵗ V η l ⊔ hopDᵗ V η r)) hB)
           (envPlug⇒envC V η P B env (λ j → pmᵗ V j (caseᵗ sc l r))
                         (λ j → (pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1) * pmᵗ V j sc)
                         (λ j → m≤n+m _ _)
                         (λ j hp → trans
                           (cong ((pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1) *_)
                             (big-forces-zero P (pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1)
                               (pmᵗ V j sc) hgt (≤-trans (m≤n+m _ _) hp)))
                           (*-zeroʳ (pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1)))
                         hσ)
  ... | inl x | ihsc =
    evalWith-hopSpn V η P B l (x ∷ᵃ env)
      (≤-trans (≤-trans (m≤m⊔n (hopDᵗ V η l) (hopDᵗ V η r))
                        (m≤m+n (hopDᵗ V η l ⊔ hopDᵗ V η r) (C * hopDᵗ V η sc))) hB)
      ( inr (valHopSpnC?-mono V η P B (pmᵗ V 0 l) C _ x
               (≤-trans (m≤m⊔n (pmᵗ V 0 l) (pmᵗ V 0 r))
                        (m≤m⊔n (pmᵗ V 0 l ⊔ pmᵗ V 0 r) 1)) ihsc)
      , EnvPlug-mono V η P B env (λ j → pmᵗ V j (caseᵗ sc l r))
                     (λ j → pmᵗ V (suc j) l)
                     (λ j → ⊔₁+ (pmᵗ V (suc j) l) (pmᵗ V (suc j) r)
                                (C * pmᵗ V j sc)) hσ )
    where C = pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1
  ... | inr y | ihsc =
    evalWith-hopSpn V η P B r (y ∷ᵃ env)
      (≤-trans (≤-trans (m≤n⊔m (hopDᵗ V η l) (hopDᵗ V η r))
                        (m≤m+n (hopDᵗ V η l ⊔ hopDᵗ V η r) (C * hopDᵗ V η sc))) hB)
      ( inr (valHopSpnC?-mono V η P B (pmᵗ V 0 r) C _ y
               (≤-trans (m≤n⊔m (pmᵗ V 0 l) (pmᵗ V 0 r))
                        (m≤m⊔n (pmᵗ V 0 l ⊔ pmᵗ V 0 r) 1)) ihsc)
      , EnvPlug-mono V η P B env (λ j → pmᵗ V j (caseᵗ sc l r))
                     (λ j → pmᵗ V (suc j) r)
                     (λ j → ⊔₂+ (pmᵗ V (suc j) l) (pmᵗ V (suc j) r)
                                (C * pmᵗ V j sc)) hσ )
    where C = pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1

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