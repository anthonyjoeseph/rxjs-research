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
open import Rx.Exp   using (Ty; Ctx; Val; Fn; Tm; Exp; applyFn; evalWith;
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

-- THE ENVIRONMENT CONDITION, PER POSITION, AND THE DISJUNCTION IS THE
-- FINDING (2026-08-19).  Three single-number hypotheses were tried and
-- each died at the opposite end from the one it fixed — a derived
-- bound decays per step, a global `∀ j → pmᵗ V j tm ≤ P` dies at a
-- CLOSED `caseᵗ` scrutinee, and a global product `pmᵗ V j tm * Ds j ≤
-- B` is false at the fold's own call site, where `Ds 0` is the
-- accumulator's hop and exponential in its spine by construction.
--
-- What the three failures say together is that the multiplier
-- condition is NOT one inequality: a leaf of the result is either
-- COPIED out of the environment or BUILT by a `strmᵗ`, and the two
-- need different arithmetic.  A position whose slope is under `P`
-- feeds a value that must carry the hereditary receipt, and the drag
-- pays for it.  A position whose slope is NOT under `P` is reachable
-- only through a PRODUCT the parent's own `hopDᵗ` clause already paid
-- for — `hopDᵗ (caseᵗ s l r)` prices the scrutinee at `pmᵗ V 0 l ⊔
-- pmᵗ V 0 r ⊔ 1`, so the product is under `B` however big the slope
-- is — and then no receipt on the value is needed at all.
--
-- DOWNWARD CLOSED IN THE SLOPE, which is what makes it usable at every
-- recursive call: a subterm's slope is under its parent's at every
-- index, so `EnvPlug-mono` re-uses the parent's condition unchanged.
EnvPlug : ∀ {n} {Γ : Ctx n} {Θ} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ) →
  All (Val Γ) Θ → (ℕ → ℕ) → Set
EnvPlug V η P B []ᵃ                Ps = ⊤
EnvPlug V η P B (_∷ᵃ_ {x = t} v σ) Ps =
  ((Ps 0 ≤ P) × (valHopSpn? V η P B t v ≡ true)
     ⊎ (Ps 0 * hopDᵛ V η t v ≤ B))
  × EnvPlug V η P B σ (λ j → Ps (suc j))

EnvPlug-mono : ∀ {n} {Γ : Ctx n} {Θ} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (σ : All (Val Γ) Θ) (Ps Qs : ℕ → ℕ) → (∀ j → Qs j ≤ Ps j) →
  EnvPlug V η P B σ Ps → EnvPlug V η P B σ Qs
EnvPlug-mono V η P B []ᵃ      Ps Qs le h = tt
EnvPlug-mono V η P B (v ∷ᵃ σ) Ps Qs le (h0 , hσ) =
  head h0 , EnvPlug-mono V η P B σ (λ j → Ps (suc j)) (λ j → Qs (suc j))
                         (λ j → le (suc j)) hσ
  where
  head : ((Ps 0 ≤ P) × (valHopSpn? V η P B _ v ≡ true)
            ⊎ (Ps 0 * hopDᵛ V η _ v ≤ B)) →
         ((Qs 0 ≤ P) × (valHopSpn? V η P B _ v ≡ true)
            ⊎ (Qs 0 * hopDᵛ V η _ v ≤ B))
  head (inl (hp , hv)) = inl (≤-trans (le 0) hp , hv)
  head (inr hprod)     = inr (≤-trans (*-monoˡ-≤ (hopDᵛ V η _ v) (le 0)) hprod)

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
  -- THE CLAUSE THAT EXTENDS THE ENVIRONMENT.  Both remaining leaves want
  -- the SAME apparatus, and the apparatus is now decided; what is left is
  -- to write it.  The design, so the next pass grinds rather than
  -- re-derives:
  --
  --   * `maxW g w m = ⊔ⱼ<m (g j * w j)` — `sumW`'s (.Measures) sibling
  --     with `⊔` in place of `+`, and the `⊔` is the whole point.  Read
  --     it as the SLOPE-WEIGHTED coefficient of a term over an
  --     environment carrying a PER-POSITION bound `Bs`.
  --   * `EnvSpn V η P σ Bs` — position-wise `hopDᵛ σⱼ ≤ Bs j * (2 + P) ^
  --     spnᵛ σⱼ`.  This REPLACES `EnvPlug`'s disjunction: the choice
  --     between "the value carries the receipt" and "the parent already
  --     paid for the product" is not a case analysis inside the proof, it
  --     is which `Bs j` the CALLER picks.  `EnvPlug` was that disjunction
  --     written at a place where it could not be spent.
  --   * the conclusion at a DERIVED coefficient, Q-shifted:
  --     `(2 + P) * hopDᵉ e ≤ C * (2 + P) ^ spnᵉ e` at every `obs` leaf,
  --     with `C = hopDᵗ tm + maxW (λ j → pmᵗ V j tm) Bs (length Θ)`.  The
  --     leading factor is what pays for the drag at the top, where
  --     `C ≤ B + P * B ≤ (2 + P) * B` cancels it exactly.
  --
  -- WHY `caseᵗ` CLOSES, and it is the `⊔` that does it.  The branch runs
  -- at `Cs ∷ Bs` where `Cs` is the scrutinee's own derived coefficient,
  -- so its coefficient is `hopDᵗ l + ((pmᵗ V 0 l * Cs) ⊔ maxW (λ j →
  -- pmᵗ V (suc j) l) Bs M)`.  Expand `pmᵗ V 0 l * Cs` into
  -- `pmᵗ V 0 l * hopDᵗ sc` plus `pmᵗ V 0 l * maxW (pmᵗ V · sc) Bs M`: the
  -- first is under `(pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1) * hopDᵗ sc`, which is
  -- `hopDᵗ (caseᵗ sc l r)`'s own second summand, and the second is under
  -- the parent's `maxW` termwise, because `pmᵗ`'s `caseᵗ` clause carries
  -- that very product.  A `+` in `maxW` would then cost a factor of two
  -- and the invariant would decay per nesting level; the `⊔` absorbs the
  -- third term into the first two and it closes EXACTLY.
  --
  -- x SUPERSEDED 2026-08-19 — "M positions need `1 + M * P ≤ Q`".  That
  -- was read off the one-shot route through `hopD-subΘᵉ` (.Measures),
  -- which SUMS over positions and so pays for every plug even when they
  -- sit on different branches of a `⊔`.  Weighting by `maxW` instead
  -- removes the M-dependence outright: `pm` itself combines by `⊔` at
  -- every `⊔` node and by `+` only where the measure multiplies, and
  -- there the node's own `suc` in `spnᵉ` funds it.  So the environment's
  -- LENGTH does not enter, and neither leaf needs the other settled
  -- first — they need the same four pieces above.
  evalWith-hopSpn-case : ∀ {n} {Γ : Ctx n} {Θ a b u} (V : ℕ) (η : Fin n → ℕ)
    (P B : ℕ) (sc : Tm Γ [] [] Θ (a +ᵗ b))
    (l : Tm Γ [] [] (a ∷ Θ) u) (r : Tm Γ [] [] (b ∷ Θ) u)
    (env : All (Val Γ) Θ) →
    hopDᵗ V η (caseᵗ sc l r) ≤ B →
    EnvPlug V η P B env (λ j → pmᵗ V j (caseᵗ sc l r)) →
    valHopSpn? V η P B u (evalWith (caseᵗ sc l r) env) ≡ true

  -- THE BUILT LEAF, and the only place the drag is actually spent.
  -- `subΘExp` is where an environment value physically enters an
  -- expression, so this is where the spine has to pay: a plugged value
  -- lands as `wkReify σⱼ` UNDER an `Exp` node, that node's own `suc` is
  -- one spine unit, and `spnᵗ (wkReify v)` is itself `suc (spnᵛ v)`
  -- wherever `hopDᵛ v` is non-zero (at a ground leaf both sides of the
  -- inequality are zero and the unit is not needed).  Those two units are
  -- exactly the drag: they turn `1 + P` into a factor of `2 + P`.
  --
  -- SO THE INDUCTION IS OVER THE EXPRESSION, not a call to
  -- `hopD-subΘᵉ` — the one-shot route discards the `⊔` structure the
  -- accounting depends on (see the superseded note above).  It is
  -- `hopD-subΘᵉ`'s own induction, clause for clause, with `sumW` replaced
  -- by `maxW` and the bound scaled by `(2 + P) ^ spnᵉ`.  Its `mapᵉ`,
  -- `scanᵉ` and `caseᵗ` clauses are the multiplying ones and each is
  -- funded by its node's `suc`; `scanᵉ` needs `(2 + P) ^ a + (2 + P) ^ b
  -- + (2 + P) ^ c ≤ (2 + P) ^ (a + b + c)` at `1 ≤ a , b , c`, which is
  -- why no `1 ≤ P` hypothesis is needed anywhere.
  --
  -- The empty-environment case is not here at all — it is `B≤powB` in the
  -- body below — so this leaf is exactly the substituting one.
  evalWith-hopSpn-strm : ∀ {n} {Γ : Ctx n} {Θ t w} (V : ℕ) (η : Fin n → ℕ)
    (P B : ℕ) (e : Exp Γ [] [] (t ∷ Θ) w)
    (v : Val Γ t) (vs : All (Val Γ) Θ) →
    hopDᵉ V η e ≤ B →
    EnvPlug V η P B (v ∷ᵃ vs) (λ j → pmᵉ V j e) →
    valHopSpn? V η P B (obs w) (evalWith (strmᵗ e) (v ∷ᵃ vs)) ≡ true

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
evalWith-hopSpn V η P B (strmᵗ e) (v ∷ᵃ vs) hB hσ =
  evalWith-hopSpn-strm V η P B e v vs hB hσ

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