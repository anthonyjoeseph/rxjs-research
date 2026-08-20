------------------------------------------------------------------
-- THE SPINE-INDEXED BURST BOUND, and the one lemma that spends it.
--
-- `burstHopD? V η r` asks every emitted value to sit under a SINGLE
-- number `r`.  For a scan frame that number is `hopDᵉ V η (scanᵉ f z b)
-- = (2 + pmᵗ V 0 f) ^ V * B`, and the exponent V arrives only through
-- the store bound.  Getting there in one step forces the fold's
-- induction to carry `V` in the exponent from the start, which is what
-- `Refuted.Hop-Drag` refutes: a fold step can DEEPEN the accumulator
-- while shrinking its `sizeᵛ`, so no per-step size comparison funds the
-- exponent.
--
-- So the burst is bounded at each value's OWN SPINE first — a quantity
-- the refuting step does not decrease — and the exponent is raised to V
-- afterwards, here, once, using the size receipt the same walk already
-- proves.  That is the whole content of this module: `burstHopSpn?` is
-- the fold's natural conclusion, `burstHopD?` is the walk's, and
-- `burstHopSpn-cap` is the conversion.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Hop-Spine-Face where

open import Data.Bool using (Bool; true; T; _∧_)
open import Data.Bool.ListAction using (all)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; s≤s; z≤n)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-refl; ≤-reflexive;
                                       ^-monoʳ-≤; ^-monoˡ-≤; *-monoˡ-≤;
                                       ⊔-lub; m≤m⊔n; m≤n⊔m; n≤1+n;
                                       m≤m+n; *-identityˡ; +-identityʳ)
open import Data.List using (List; []; _∷_)
open import Data.Fin  using (Fin)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Rx.Prim  using (InstEmit; InstEvent; init; value; close;
                            handoff; complete)
open import Data.Unit using (tt)
open import Data.List.Relation.Unary.All renaming ([] to []ᵃ) using ()
open import Rx.Exp   using (Ty; Ctx; Val; Fn; Tm; applyFn; evalTm; sizeᵛ;
                            unitᵗ; boolᵗ; natᵗ; obs; _×ᵗ_; _+ᵗ_)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵛ; pmᵗ)
open import Rx.Hop-Spine using (spnᵉ; spnᵛ; spn≤sizeᵛ)
open import Rx.Evaluator using (Stream; scanVals)
open import Verify-Budget-Sufficient.Measures using
  (burstB?; burstHopD?; valB?; eventB?; hopDev?; all-impl;
   ∧-true; ∧-intro; T⇒≡true; T-to; all-zip; 1≤2^;
   hopD-evalWith; sumW)

-- the same event walk as hopDev?, with the bound read off the VALUE
hopSpnev? : ∀ {n} {Γ : Ctx n} {u} → ℕ → (Fin n → ℕ) → ℕ → ℕ →
            InstEvent (Val Γ u) → Bool
hopSpnev? {u = u} V η base B (value v) = hopDᵛ V η u v ≤ᵇ base ^ spnᵛ u v * B
hopSpnev? V η base B (init _)    = true
hopSpnev? V η base B (close _ _) = true
hopSpnev? V η base B (handoff _) = true
hopSpnev? V η base B complete    = true

burstHopSpn? : ∀ {n} {Γ : Ctx n} {u} → ℕ → (Fin n → ℕ) → ℕ → ℕ →
               Stream Γ u → Bool
burstHopSpn? V η base B =
  all (λ em → all (hopSpnev? V η base B) (InstEmit.events em))

------------------------------------------------------------------
-- THE CONVERSION.  `spn≤sizeᵛ` (Rx.Hop-Spine) is what makes the size
-- receipt pay for the hop exponent: the spine is size along the
-- hop-deepest path, so a cap on the whole value caps it too.
------------------------------------------------------------------

burstHopSpn-cap : ∀ {n} {Γ : Ctx n} {u} (V Ψ base B Bsz : ℕ)
  (η : Fin n → ℕ) (str : Stream Γ u) →
  1 ≤ base → Bsz ≤ V →
  burstB? Bsz Ψ str ≡ true →
  burstHopSpn? V η base B str ≡ true →
  burstHopD? V η (base ^ V * B) str ≡ true
-- base ≡ 0 is vacuous, and matching on `suc base` is also what puts the
-- NonZero instance ^-monoʳ-≤ asks for in scope
burstHopSpn-cap V Ψ zero B Bsz η str () hBsz hB hS
burstHopSpn-cap {u = u} V Ψ (suc base) B Bsz η str 1≤b hBsz hB hS =
  all-zip (λ em → all (eventB? Bsz Ψ) (InstEmit.events em))
            (λ em → all (hopSpnev? V η (suc base) B) (InstEmit.events em))
            (λ em → all (hopDev? V η (suc base ^ V * B)) (InstEmit.events em))
            (λ em → all-zip (eventB? Bsz Ψ)
                              (hopSpnev? V η (suc base) B)
                              (hopDev? V η (suc base ^ V * B))
                              ev (InstEmit.events em))
            str hB hS
  where
  ev : (x : InstEvent (Val _ u)) →
       eventB? Bsz Ψ x ≡ true → hopSpnev? V η (suc base) B x ≡ true →
       hopDev? V η (suc base ^ V * B) x ≡ true
  ev (value v) hb hs =
    T⇒≡true _ (≤⇒≤ᵇ
      (≤-trans (≤ᵇ⇒≤ (hopDᵛ V η u v) (suc base ^ spnᵛ u v * B) (T-to hs))
               (*-monoˡ-≤ B (^-monoʳ-≤ (suc base)
                 (≤-trans (spn≤sizeᵛ u v)
                   (≤-trans (≤ᵇ⇒≤ (sizeᵛ u v) Bsz
                              (T-to (proj₁ (∧-true (sizeᵛ u v ≤ᵇ Bsz) _ hb))))
                            hBsz))))))
  ev (init _)    hb hs = refl
  ev (close _ _) hb hs = refl
  ev (handoff _) hb hs = refl
  ev complete    hb hs = refl

------------------------------------------------------------------
-- THE HEREDITARY FORM, and why the headline one is not enough.
--
-- The fold's invariant cannot be `hopDᵛ accᵢ ≤ (2 + P) ^ spnᵛ accᵢ * B`
-- on the accumulator ALONE, because it does not survive `fstᵗ`:
-- projecting a pair yields a component whose SPINE is smaller than the
-- pair's (spnᵛ takes `⊔` and adds one) while its DEPTH may be the whole
-- pair's (hopDᵛ takes the same `⊔`).  The headline bound at the pair
-- therefore says nothing at the component, and `evalWith` projects.
--
-- So the invariant is carried at every component: `valHopSpn?` recurses
-- through pairs and sums and bottoms out at `obs` with the headline
-- inequality.
--
-- IT STOPS AT `obs`, AND THAT IS THE WHOLE DESIGN DECISION (2026-08-19).
-- Hereditary-everywhere would mean recursing into the EXPRESSION a
-- stream value is, which is a second structural induction and a second
-- predicate to preserve.  It is not needed, and the reason is a property
-- of the syntax rather than of this proof: `Tm` HAS NO ELIMINATOR FOR
-- `obs`.  Nothing projects a component out of a stream value — the only
-- eliminating term formers are `fstᵗ`, `sndᵗ` and `caseᵗ`, which take
-- pairs and sums apart and nothing else.  Streams are only ever BUILT
-- (mapᵉ, mergeAllᵉ, …), and a builder needs its argument's headline
-- bound, not its interior.  So pairs and sums are exactly the positions
-- where a bound can be projected away, and exactly the positions the
-- recursion covers.
------------------------------------------------------------------

valHopSpn? : ∀ {n} {Γ : Ctx n} → ℕ → (Fin n → ℕ) → ℕ → ℕ →
             (u : Ty) → Val Γ u → Bool
valHopSpn? V η P B unitᵗ    _        = true
valHopSpn? V η P B boolᵗ    _        = true
valHopSpn? V η P B natᵗ     _        = true
valHopSpn? V η P B (s ×ᵗ t) (a , b)  =
  valHopSpn? V η P B s a ∧ valHopSpn? V η P B t b
valHopSpn? V η P B (s +ᵗ t) (inj₁ a) = valHopSpn? V η P B s a
valHopSpn? V η P B (s +ᵗ t) (inj₂ b) = valHopSpn? V η P B t b
valHopSpn? V η P B (obs t)  e        = hopDᵉ V η e ≤ᵇ (2 + P) ^ spnᵉ e * B

-- the headline follows from the hereditary form, and this is what makes
-- the extra structure free at the consumer: `⊔` of two exponentials is
-- the exponential of the `⊔`, and the pair node's own `suc` pays for it
valHopSpn?-hopD : ∀ {n} {Γ : Ctx n} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (u : Ty) (v : Val Γ u) → valHopSpn? V η P B u v ≡ true →
  hopDᵛ V η u v ≤ (2 + P) ^ spnᵛ u v * B
valHopSpn?-hopD V η P B unitᵗ _ h = z≤n
valHopSpn?-hopD V η P B boolᵗ _ h = z≤n
valHopSpn?-hopD V η P B natᵗ  _ h = z≤n
valHopSpn?-hopD V η P B (s ×ᵗ t) (a , b) h =
  ⊔-lub (≤-trans (valHopSpn?-hopD V η P B s a (proj₁ sp)) (up (m≤m⊔n (spnᵛ s a) (spnᵛ t b))))
        (≤-trans (valHopSpn?-hopD V η P B t b (proj₂ sp)) (up (m≤n⊔m (spnᵛ s a) (spnᵛ t b))))
  where
  sp = ∧-true (valHopSpn? V η P B s a) (valHopSpn? V η P B t b) h
  up : ∀ {k} → k ≤ spnᵛ s a ⊔ spnᵛ t b →
       (2 + P) ^ k * B ≤ (2 + P) ^ suc (spnᵛ s a ⊔ spnᵛ t b) * B
  up le = *-monoˡ-≤ B (^-monoʳ-≤ (2 + P) (≤-trans le (n≤1+n (spnᵛ s a ⊔ spnᵛ t b))))
valHopSpn?-hopD V η P B (s +ᵗ t) (inj₁ a) h =
  ≤-trans (valHopSpn?-hopD V η P B s a h)
          (*-monoˡ-≤ B (^-monoʳ-≤ (2 + P) (n≤1+n (spnᵛ s a))))
valHopSpn?-hopD V η P B (s +ᵗ t) (inj₂ b) h =
  ≤-trans (valHopSpn?-hopD V η P B t b h)
          (*-monoˡ-≤ B (^-monoʳ-≤ (2 + P) (n≤1+n (spnᵛ t b))))
valHopSpn?-hopD V η P B (obs t) e h =
  ≤ᵇ⇒≤ (hopDᵉ V η e) ((2 + P) ^ spnᵉ e * B) (T-to h)

evHopSpnH? : ∀ {n} {Γ : Ctx n} {u} → ℕ → (Fin n → ℕ) → ℕ → ℕ →
             InstEvent (Val Γ u) → Bool
evHopSpnH? {u = u} V η P B (value v) = valHopSpn? V η P B u v
evHopSpnH? V η P B (init _)    = true
evHopSpnH? V η P B (close _ _) = true
evHopSpnH? V η P B (handoff _) = true
evHopSpnH? V η P B complete    = true

burstHopSpnH? : ∀ {n} {Γ : Ctx n} {u} → ℕ → (Fin n → ℕ) → ℕ → ℕ →
                Stream Γ u → Bool
burstHopSpnH? V η P B =
  all (λ em → all (evHopSpnH? V η P B) (InstEmit.events em))

-- and the burst-level projection, which is all the consumer needs
burstHopSpnH-headline : ∀ {n} {Γ : Ctx n} {u} (V P B : ℕ) (η : Fin n → ℕ)
  (str : Stream Γ u) →
  burstHopSpnH? V η P B str ≡ true →
  burstHopSpn? V η (2 + P) B str ≡ true
burstHopSpnH-headline {u = u} V P B η str h =
  all-impl (λ em → all (evHopSpnH? V η P B) (InstEmit.events em))
           (λ em → all (hopSpnev? V η (2 + P) B) (InstEmit.events em))
           (λ em → all-impl (evHopSpnH? V η P B) (hopSpnev? V η (2 + P) B)
                            ev (InstEmit.events em))
           str h
  where
  ev : (x : InstEvent (Val _ u)) →
       evHopSpnH? V η P B x ≡ true → hopSpnev? V η (2 + P) B x ≡ true
  ev (value v) hv = T⇒≡true _ (≤⇒≤ᵇ (valHopSpn?-hopD V η P B _ v hv))
  ev (init _)    _ = refl
  ev (close _ _) _ = refl
  ev (handoff _) _ = refl
  ev complete    _ = refl

------------------------------------------------------------------
-- THE INTRODUCTION, and it is why the walk face does NOT have to be
-- restated hereditarily.
--
-- `hopDᵛ` is a `⊔` over the value's obs-leaves and nothing else — pairs
-- take `⊔`, sums pass through, the ground types are 0 — so a PLAIN
-- headline bound `hopDᵛ v ≤ B` already bounds EVERY leaf by B.  The
-- hereditary predicate asks each leaf for `hopDᵉ e ≤ (2 + P) ^ spnᵉ e *
-- B`, and `1 ≤ (2 + P) ^ k`, so the leaf's own spine is never needed:
-- the exponent is spare room.
--
-- That is the whole reason the source values arrive for free.  The fold
-- consumes `b`'s burst, whose receipt is the ORDINARY `burstHopD?` the
-- walk face already proves at a single number, and the seed's is
-- `hopDᵗ z`.  Both are headlines and both land here.  Only the
-- ACCUMULATOR needs the hereditary form maintained, because only it is
-- fed back through `applyFn` where a projection can strip a pair.
------------------------------------------------------------------

B≤powB : ∀ (P B k : ℕ) → B ≤ (2 + P) ^ k * B
B≤powB P B k =
  ≤-trans (≤-reflexive (sym (*-identityˡ B)))
          (*-monoˡ-≤ B (≤-trans (1≤2^ k) (^-monoˡ-≤ k (m≤m+n 2 P))))

valHopSpn?-intro : ∀ {n} {Γ : Ctx n} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (u : Ty) (v : Val Γ u) → hopDᵛ V η u v ≤ B →
  valHopSpn? V η P B u v ≡ true
valHopSpn?-intro V η P B unitᵗ _ h = refl
valHopSpn?-intro V η P B boolᵗ _ h = refl
valHopSpn?-intro V η P B natᵗ  _ h = refl
valHopSpn?-intro V η P B (s ×ᵗ t) (a , b) h =
  ∧-intro (valHopSpn?-intro V η P B s a
            (≤-trans (m≤m⊔n (hopDᵛ V η s a) (hopDᵛ V η t b)) h))
          (valHopSpn?-intro V η P B t b
            (≤-trans (m≤n⊔m (hopDᵛ V η s a) (hopDᵛ V η t b)) h))
valHopSpn?-intro V η P B (s +ᵗ t) (inj₁ a) h = valHopSpn?-intro V η P B s a h
valHopSpn?-intro V η P B (s +ᵗ t) (inj₂ b) h = valHopSpn?-intro V η P B t b h
valHopSpn?-intro V η P B (obs t) e h =
  T⇒≡true _ (≤⇒≤ᵇ (≤-trans h (B≤powB P B (spnᵉ e))))

------------------------------------------------------------------
-- THE STEP — the one gap the fold has, and the whole content of the
-- scan hop receipt.
--
-- `applyFn fn x = evalWith fn (x ∷ᵃ []ᵃ)`, so this is a structural
-- induction over `Tm` carrying the hereditary predicate.  Every clause
-- but one is bookkeeping: the ground types are trivial, `pairᵗ`/`inj`
-- split the conjunction, `fstᵗ`/`sndᵗ`/`caseᵗ` PROJECT — which is
-- exactly what the hereditary form was chosen to survive, and where a
-- headline-only invariant dies.
--
-- The one clause with content is `strmᵗ e`, where the reified argument
-- is substituted syntactically into `e` and the result's leaf is
-- `subΘᵉ e env`.  That is where the drag lives, and on the SPINE it is
-- true: a plug position contributes its own spine to `spnᵉ (subΘᵉ e
-- env)`, so the exponent grows by at least the plugged value's spine
-- while `hopDᵉ` grows by at most `pmᵗ V 0 fn` times its depth.  The
-- degenerate half is free from `hopD-evalWith`'s TIGHT form: at `pmᵗ V
-- 0 fn ≡ 0` it gives `hopDᵛ (applyFn fn v) ≤ hopDᵗ fn ≤ B` outright, so
-- the arithmetic is only ever asked at `≥ 1`.
--
-- TWINS, both PROVEN and both over this same induction: `hopD-evalWith`
-- (.Measures) is the headline version of this statement, and
-- `evalWith-iterSize` (.Caps-Face/Part1) already carries an env-wise
-- predicate (`EnvSize`) in the shape the hypotheses here need.
--
-- The open bookkeeping question is `caseᵗ`, whose branch evaluates
-- under an EXTENDED env: the parent's `pmᵗ V j (caseᵗ s l r)` does not
-- see `pmᵗ V 0 l` when the scrutinee is closed, while `hopDᵗ` does —
-- `(pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1) * hopDᵗ s` — so it should close through
-- the depth side rather than the slope side.
------------------------------------------------------------------

------------------------------------------------------------------
-- WHAT THIS LEAF NOW OWES, AND WHAT IT NO LONGER DOES (2026-08-19).
--
-- DISCHARGED around it, all REAL BODIES: the fold (`scanVals-hopSpn`,
-- below), the burst walk that spends it (`pushBurst-scan-hopSpn`,
-- .Hop-Spine-Push), the scan clause's own assembly (`walk-scan-hop-spn`,
-- .Walk-Level), and both headline-to-hereditary lifts (`scanSeed-hopSpn`
-- and `burstHopSpnH-intro`, below).  So the ENTIRE scan hop receipt now
-- reduces to this one substitution step plus a frame condition on the
-- node table.
--
-- THE ARITHMETIC IS SETTLED, and that is a receipt rather than a plan.
-- The `strmᵗ` clause needs: the template's own hop `h ≤ B`, the plugged
-- value's receipt at its own spine `k`, the multiplier `P`, and at least
-- ONE template spine node above the plug.  Under those the step closes —
-- the extra factor of `2 + P` bought by that one node pays `2` for the
-- template's hop and `P` for the multiplied value's.  Machine-checked
-- during design as a standalone ℕ lemma and then REMOVED, because its
-- only possible consumer is this postulate's own unwritten clause and
-- the wiring law does not carry code nothing calls.  It is four lines of
-- `≤-trans` over `^-distribˡ-+-*`; the finding is that it CLOSES, not
-- how it is spelled.
--
-- THE ONE REMAINING UNKNOWN, STATED NARROWLY.  It is NOT "does the
-- spine drag" in general — that question is about whole values and is
-- the wrong one, because a projection inside the induction can reach a
-- component at a smaller spine, which is exactly what the hereditary
-- predicate exists to absorb.  What the `strmᵗ` clause actually needs is
-- a claim about the substituted EXPRESSION:
--
--     if variable j is plugged in `e` at all (`1 ≤ pmᵉ V j e`), then
--     `spnᵉ (subΘᵉ e env)` is at least `1 + spnᵛ (envⱼ)`
--
-- — the plugged value's own spine, plus at least one node of the
-- template above it.  That single node is what `pow-binomial-step`'s
-- `1 ≤ sp` hypothesis spends, and it is the whole difference between
-- this and the size measure `Refuted.Hop-Drag` kills: a `caseᵗ` branch
-- discards a SIBLING, and a sibling is never on the hop-deepest path, so
-- `spnᵉ` never counted it.
--
-- AND THAT CLAIM IS NOW EVIDENCED, WHICH IS WHY THIS ROW IS GRINDABLE
-- RATHER THAN DIFFICULTY (2026-08-19).  Three things, and the class rests
-- on all three together:
--
--   · EXHAUSTIVE INSPECTION OF THE MEASURE.  Every non-leaf clause of
--     `spnᵗ` and `spnᵉ` (Rx.Hop-Spine) is `suc (…)`, and not one of them
--     DROPS a subterm — the combining operators are `+`, `⊔` and `suc`,
--     all monotone in every argument.  So a plugged value's spine
--     propagates upward to the root by construction, and any non-variable
--     template contributes at least the one node the arithmetic needs.
--     That is a property of twenty-six lines, checkable by reading them.
--
--   · MACHINE RECEIPTS AT BOTH ADVERSARIAL SHAPES.  `Refuted.Hop-Drag`
--     pins 4 ↦ 7 ↦ 10 ↦ 13 across the very caseᵗ step that drops `sizeᵛ`
--     from 36 to 9 — the projecting discard, the shape that REFUTED the
--     size measure.  Demand-Probe series Ω′ pins 3 ↦ 15 ↦ 27 ↦ 39 on the
--     amplifying `mapᵉ`-plug step, and pins the claim itself rather than
--     the numbers: `suc (spnᵛ accₖ) ≤ᵇ spnᵛ accₖ₊₁` at three steps.
--
--   · THE PRECEDENT FOR THE INDUCTION.  `hopD-evalWith` (.Measures,
--     PROVEN) is this same induction over the same syntax with the same
--     env apparatus; the hereditary version carries a Bool predicate
--     where it carries a number.  Its `EnvHopDs`/`sumW` shape is also the
--     answer to the `caseᵗ` question above, so the generalisation the
--     body needs is already written down and discharged next door.
--
-- WHAT THE EVIDENCE DID NOT REACH, stated so the demotion is auditable:
-- no probe covers `ifᵗ` or nested `caseᵗ` plugs, and nobody has typed the
-- induction, so the bookkeeping could still surprise.  What would REOPEN
-- this as DIFFICULTY is a template that plugs the accumulator and does
-- not advance the spine — the same refutation Hop-Drag ran against
-- `sizeᵛ`, which is exactly what these two series looked for and did not
-- find.
--
-- THE `caseᵗ` BOOKKEEPING QUESTION IS ANSWERED, and the answer changes
-- the induction's SHAPE rather than adding a lemma.  A uniform
-- hypothesis `∀ j → pmᵗ V j tm ≤ P` does not survive `caseᵗ`: the
-- parent's `pmᵗ V k (caseᵗ s l r)` has `pmᵗ V 0 l` only inside a product
-- with `pmᵗ V k s`, so a CLOSED scrutinee makes the branch's own plug
-- multiplier invisible.  But it is also harmless exactly there — when
-- `hopDᵗ s` and every `pmᵗ V k s` vanish, `hopD-evalWith` gives the
-- branch's bound variable a payload of hop ZERO, so any multiplier
-- times it is zero.  What the two facts say together is that the
-- induction must carry a PER-VARIABLE pairing rather than a uniform
-- bound — precisely `hopD-evalWith`'s own `EnvHopDs`/`sumW` shape
-- (.Measures, PROVEN).  State the hereditary version at that shape and
-- the case disappears; state it at a uniform `P` and it cannot be
-- closed.  Do NOT probe this: a `caseᵗ` probe is degenerate for the same
-- reason Demand-Probe series Ω is.
------------------------------------------------------------------
-- THE RESEARCH RECORD FOR THIS LEAF, moved here from the walk face when
-- the scan clause was assembled and this became the only thing it owes.
-- Read it as being about the fold `scanVals` runs, whose per-step
-- substitution is exactly the statement above.
--
-- It is the scan clause that GROWS values within an instant (applyFn-size is the Ŝ-ceiling supplier; the
-- P-series probe receipts in the block header above ran exactly this
-- shape).  Why it is not GRINDABLE beside walk-map: map's emitted value
-- is a function of ONE source value and hopD-map-emit bounds it; scan's
-- is a function of the source value AND the running accumulator, and
-- there is no hopD-scan-emit.  The funding is visible and generous —
-- hopDᵉ's scan clause carries a `(2 + pmᵗ V 0 f) ^ V` factor, room for
-- V applications, against map's single `(pmᵗ V 0 f ⊔ 1)` — but an
-- exponential with room to spare is not an induction, and what has to
-- be decided is what the accumulator's invariant IS across the fold.
-- Decide that before authoring scan-f's push face, not after: the face
-- reports at whatever index the invariant turns out to need.
--
-- THE INVARIANT, DERIVED (2026-08-19) — the fold half is settled and
-- one arithmetic question is all that is left.  Write P = pmᵗ V 0 f ⊔ 1
-- and B = hopDᵗ f + hopDᵗ z + hopDᵉ b, so hopDᵉ's scan clause is
-- `(2 + pmᵗ V 0 f) ^ V * B`.  Let Aₖ be the accumulator's hop after k
-- applications.  Then, with `hopDᵛ (s ×ᵗ t) (a , b) = hopDᵛ a ⊔ hopDᵛ b`
-- (Rx.Hop-Depth — a MAX, not a sum, which is what keeps this linear)
-- and PROVEN hopD-applyFn giving
-- `hopDᵛ (applyFn f w) ≤ hopDᵗ f + P * hopDᵛ w`:
--
--     A₀   = hopDᵗ z                       ≤ B
--     Aₖ₊₁ ≤ hopDᵗ f + P * (Aₖ ⊔ hopDᵉ b)  ≤ B + P * Aₖ
--     ⇒ Aₖ ≤ (1 + P) ^ k * B
--
-- and `1 + P = 1 + (pmᵗ V 0 f ⊔ 1) ≤ 2 + pmᵗ V 0 f` in BOTH cases of
-- the ⊔.  So the induction closes at exactly the base hopDᵉ already
-- carries — the scan clause was evidently sized for this fold, which is
-- the strongest evidence the shape is the intended one.
--
-- SO THE INVARIANT IS `hopDᵛ acc ≤ (2 + pmᵗ V 0 f) ^ k * B after k
-- applications`, established at the seed and preserved by
-- hopD-applyFn.  The one remaining question is the exponent, and the
-- answer is that it is NOT `k` — it is the ACCUMULATOR'S OWN SIZE:
--
-- ⚠ DO NOT BOUND k FROM THE CEILING PINS.  That route is REFUTED
-- (`scan-count-under-ceiling-absurd`, agda/refuted, Refuted.Caps-Face):
-- via the ceiling, `k` is bounded only by burstCount?, which caps
-- instants and per-instant values SEPARATELY, each by `suc (Caps.cWid
-- c)` — a WIDTH SQUARED — while the only lower bound on `V = Ŝ` is
-- `Caps.cSize (frameStep L̂ c) ≤ Ŝ`, a SIZE.  The axes diverge: a level
-- step EXPONENTIATES the width (`foldStep S w = S ^ suc w`, a tower in
-- the level) and merely SCALES the size (`sizeStep S s = S * suc (2 *
-- s)`), so the squared width passes the size at j = 2 and the bare
-- width at j = 3.  No level offset is available either: the ceiling
-- asks `opIterD … ≤ L̂` while the walk's exit level is bounded by that
-- same `opIterD …`, so `L̂ := opIterD …` is admissible and both are read
-- at the SAME level.
--
-- BUT THE CEILING WAS NEVER THE ROUTE, and reading the refutation as a
-- blocker cost this row a SHAPE classification it did not deserve.  The
-- bound comes from the STORE INVARIANT, which this face already carries
-- as a hypothesis — worked out 2026-07-28 and recorded in Keeps-Ring's
-- header, where a search would have found it:
--   · `boundedNode B (scan-st v) = sizeᵛ t v ≤ᵇ B` (.Measures) — the
--     accumulator is a STORED value and stBounded? reads it as a size;
--   · WalkTail's `INV? Ψ (Caps.cSize (frameStep j c)) sched st` supplies
--     that at `B = Caps.cSize (frameStep j c)`;
--   · `ceil` (`Caps.cSize (frameStep L̂ c) ≤ Ŝ`) with `F ≡ Ŝ` carries it
--     to `sizeᵛ accₖ ≤ V`.
-- So the size bound is HYPOTHESIS-SIDE and needs no new premise, no
-- width ceiling, no re-indexing and no gas.  The three-candidate repair
-- space below is therefore MOOT; it is kept only so the two dead
-- candidates are not re-proposed.
--
-- ✗ DEAD ROUTE 2026-08-19 — BOUNDING k AT ALL.  Recorded because it is
-- the obvious first move and it cannot work; it is NOT the row's
-- residue, and an earlier draft of this header wrongly promoted it to
-- one.  Take the inventory of what bounds the fold's step count k:
--
--   · `burstCount?` (.Caps-Face/Part1), which this face carries as a
--     hypothesis, is `length str ≤ᵇ suc (Caps.cWid c)` together with a
--     per-emit `valCountᵉ … ≤ᵇ suc (Caps.cWid c)`.  WIDTH-denominated.
--   · `make find Q='valCount'` returns NO size-denominated bound
--     anywhere in the development — every consumer (countVals, countIn,
--     splitEvents-valsCaps) is against suc (cWid c).
--   · the natural size-denominated candidate is REFUTED, with a
--     machine-checked receipt sitting on the measure itself
--     (Rx/Exp:500): `syncSizeᵉ` does NOT bound emissions per instant —
--     valueCount 30 against syncSizeᵉ 20 at K = 4, with K = 1..3 all
--     holding, which is why it looks true from small cases.
--
-- And hopDᵉ's scan clause targets `(2 + pmᵗ V 0 f) ^ V`, with V the
-- SIZE cap.  So a bound on k and the budget for it are in different
-- currencies, and converting between them is dead route #1 below —
-- width sits ABOVE size at the true instantiation because foldStep
-- towers where sizeStep scales.
--
-- WHY THAT COSTS NOTHING: THE LIVE ROUTE NEVER MENTIONS k.  Rx.Hop-Depth's
-- own header is explicit — "a fold that deepens the accumulator adds at
-- least one constructor, and a fold that does not deepen it does not raise
-- hopD either" — so the exponent is the accumulator's SIZE and the store
-- bound supplies it directly.  k is an artefact of reading the recurrence
-- in steps rather than in the accumulator's own measure.  Do not re-open
-- it, and do not commission the `valCountᵉ ≤ sizeᵉ b` probe an earlier
-- draft of this header asked for: its answer changes nothing here.
--
-- THE OLD FRAMING, kept because its refutation is still load-bearing.
-- `k ≤ sizeᵛ accₖ` is FALSE as literally stated — an identity or
-- constant fold leaves the size alone — so the exponent cannot be the
-- step count.  State the invariant with the size IN the exponent,
-- `hopDᵛ accₖ ≤ (1 + P) ^ sizeᵛ accₖ * B`, which degenerates correctly
-- on the non-deepening folds that break the k-form.  Preserving it
-- wants a sharper hopD-applyFn: one that spends a size INCREASE to pay
-- for each factor of P.
--
-- ✗ DO NOT REACH FOR `hopD-sizeᵗ` / `hopD-sizeᵉ` (.Measures, PROVEN)
-- HERE, despite their being exactly "depth bounded by size".  They land
-- at `szB V (sizeᵉ e)`, and `szB V V = (2+V)^((1+V)^V)` is the GLOBAL
-- hop cap — astronomically above the `(2 + pmᵗ V 0 f) ^ V * B` this
-- conjunct is measured against.  The base has to be the plug
-- multiplier, not the size; that gap is the lemma this row owes.
--
-- THE RISKY REGION IS AMPLIFYING FOLDS ONLY (corrected 2026-08-19; an
-- earlier draft of this header said the slack is nil everywhere, which
-- is wrong and made the region look bigger than it is).  Write
-- P = pmᵗ V 0 f ⊔ 1 and split on it:
--   · P = 1 (pmᵗ ≤ 1) — the recurrence `Aₖ₊₁ ≤ hopDᵗ f + P * (Aₖ ⊔
--     hopDᵉ b)` is ADDITIVE, not geometric, so `Aₖ ≤ (1+k) * B` and the
--     clause's `2 ^ V * B` needs only `1 + k ≤ 2 ^ V`.  Exponentially
--     weaker than `k ≤ V`, and comfortably true.
--   · P ≥ 2 — `Aₖ ≤ (1+P)^k * B` against `(2+P)^V * B` needs
--     `k ≤ V * log(2+P)/log(1+P)`, which at P = 2 is 1.26·V.  That is
--     `k ≤ V` up to a constant, and it is where the row actually lives.
--
-- THE REPAIR SPACE BELOW IS MOOT — kept so the dead candidates are not
-- re-proposed, since each cost a day to kill.  It was written while the
-- ceiling looked like the only source of a bound on the exponent; the
-- store invariant above removes the need for any of it.
--
--   ✗ A WIDTH CEILING AGAINST Ŝ — `suc (cWid (frameStep L̂ c)) ^ 2 ≤ Ŝ`,
--     threaded beside `ceil`.  DEAD: `sizeCapAt e sl id ≡ Caps.cSize
--     (capsAt e sl id)` (.Wet/Part6), so at the true instantiation Ŝ is
--     a size and `cWid (capsAt …)` is the width of the SAME caps —
--     `foldStep` towers where `sizeStep` scales, so the width is already
--     above the size there.  The hypothesis would be unsatisfiable at
--     the only instantiation that matters.
--   ✗ DECOUPLE F FROM Ŝ — carry the hop index separately with its own
--     width ceiling, leaving Ŝ the size cap.  DEAD: the demand side
--     spends `dBound-connect`'s `r′ ≤ R` with `R̂ ≡ hopR Ŝ`, and hopD-cap
--     yields only `hopDᵉ F η e ≤ hopR F`.  For F > Ŝ that needs
--     `hopR F ≤ hopR Ŝ`, and hopR is monotone the other way.  Every
--     consumer wants ONE index; splitting it breaks the connect edge.
--   ⚠ RAISE Ŝ ITSELF to a width-scale cap.  The only live one, and it
--     is monotone-safe everywhere the index appears as an upper bound:
--     `2 ≤ Ŝ`, `cSize (frameStep L̂ c) ≤ Ŝ`, `slotsSize sl ≤ V` and
--     `sizeᵉ b ≤ V` (slotHop-cap) all survive a BIGGER Ŝ, hopR grows
--     with it so hopD-cap still applies, and burstHopD?'s two sides move
--     together so the conclusion only loosens.
--
-- (Had raise-Ŝ been needed it would have raised `dBound Ŝ R̂ …` and hence
-- G, which `g hasAtLeast suc G` must fund — a budget question, and one
-- whose rough shape was discouraging.  It is not asked; the store
-- invariant makes the whole detour unnecessary.)
--
-- `ops ≥ 1` (WalkTail's `suc (sizeᵉ b) ≤ ops`) rescues nothing here — it
-- constrains opIterD's iteration count, not the relation between the two
-- axes at a level.
--
-- IS THE FOLD'S GROWTH REALLY GEOMETRIC?  ANSWERED 2026-08-19: YES.
-- The cheap escape is CLOSED, so the raise-Ŝ repair above is the only
-- one left and the gas question is the live one.  Do not re-open this.
--
-- The hope was that hopD-applyFn's MULTIPLICATIVE factor, `hopDᵛ
-- (applyFn f v) ≤ hopDᵗ f + (pmᵗ V 0 f ⊔ 1) * hopDᵛ v`, is loose for a
-- DEPTH — hopDᵛ reads pairs by ⊔ (Rx.Hop-Depth), so duplicating the
-- accumulator into k positions cannot deepen it.  That observation is
-- TRUE AND IRRELEVANT, which is the trap worth recording: the
-- multiplication never came from duplication.  It comes from plugging
-- the accumulator into the SOURCE position of a `mapᵉ`, the one clause
-- of hopDᵉ that multiplies — `hopDᵗ f + (pmᵗ V 0 f ⊔ 1) * hopDᵉ e` —
-- where the source's WHOLE depth is scaled.  The ⊔ at the pair node
-- never sees that factor and cannot damp it.
--
-- MACHINE-CHECKED: Demand-Probe series X.  A scan step with P = 2
-- iterated four times gives Aₖ = 2^(k+1) − 2, and hopD-applyFn's bound
-- instantiates to `Aₖ₊₁ ≤ 2 + 2 * Aₖ` — MET WITH EQUALITY at every
-- step, so there is no slack to strengthen away.
--
-- AND AMPLIFICATION NEEDS NOTHING EXOTIC, which is what kills the
-- fallback hope that a nested scan could be excluded by the fold's own
-- size budget.  `pmᵗ V 0 g = 2` is reachable in a NAT-TYPED template
-- containing no stream, no map and no scan at all: pmᵗ's caseᵗ clause
-- ADDS the branches' slope to the scrutinee's, and `1 + 1 = 2`.  A
-- step function need only route its accumulator through `ofᵉ` + a *All
-- frame (the only way an obs-typed Θ-var reaches expression position)
-- into such a map.
--
-- The one thing series X does NOT settle: what bounds k.  It says the
-- growth is geometric, not that k exceeds V.
--
-- ═══ THE ROW IS SPLIT (2026-08-19), AND ONLY THE HOP HALF IS HARD ═══
-- `walk-scan` is now a real body (below) pairing the two leaves that
-- follow.  Everything above this line is about the hop
-- half ALONE; the other eight conjuncts never see the fold's arithmetic.
--
-- the eight — GRINDABLE, and it is walk-map's census verbatim at this
-- shape.  scanᵉ mints no subscription mapᵉ does not: subscribeE's scan
-- clause (Evaluator:1453) installs ONE node, subscribes the source with
-- `scan-f f nid ↠ κ`, and pushes the resulting burst — the same
-- install-subscribe-push the other chain frames run, with `scanFrame-caps`
-- (.Caps-Face, PROVEN) paying the frame charge and `subscribeE-caps`
-- delegating the caps half.  So the *budget* really is map-difficulty,
-- which is what the shape of this leaf records.
-- the hop conjunct — DIFFICULTY, and the whole of this row's risk.  What
-- it owes is the ACCUMULATOR INVARIANT, `hopDᵛ accᵢ ≤ (2 + pmᵗ V 0 f) ^
-- sizeᵛ accᵢ * B`, carried along `scanVals`' fold (Evaluator:1279) and
-- closed against the clause's `(2 + pmᵗ V 0 f) ^ V` by the store bound
-- `sizeᵛ accᵢ ≤ V` — which is HYPOTHESIS-SIDE here (INV? + ceil + F ≡ Ŝ,
-- see the store-invariant paragraph above) and needs no new premise.
-- Its one missing ingredient is a SHARPER hopD-applyFn: one that spends a
-- size INCREASE to pay for each factor of the multiplier.  That is exactly
-- what makes the exponent the accumulator's own size rather than the step
-- count k — and it is why `k` need never be bounded at all, which retires
-- the currency question the paragraph above raises against the k-form.
--
-- WHERE EXACTLY THE INVARIANT BREAKS, AND IT IS ONE CASE (derived
-- 2026-08-19; arithmetic, NOT typechecked).  Write P = pmᵗ V 0 f ⊔ 1,
-- B = hopDᵗ f + hopDᵗ z + hopDᵉ b — the clause's own summand — and
-- Aᵢ = hopDᵛ accᵢ, sᵢ = sizeᵛ accᵢ along scanVals' fold.
--   · BASE: `hopD-evalWith` (.Measures, PROVEN) at the empty env, since
--     `evalTm` is `evalWith … []ᵃ` — the same reduction
--     `evalTm-iterSize` (.Caps-Face/Part1) already makes for the size.
--     Gives A₀ ≤ hopDᵗ z ≤ B.
--   · STEP: hopD-applyFn against the pair's ⊔ gives Aᵢ₊₁ ≤ B + P * (Aᵢ ⊔ B).
-- Against the invariant `Aᵢ ≤ (1 + P) ^ sᵢ * B`, that splits two ways:
--   · sᵢ₊₁ ≥ suc sᵢ — CLOSES, on `1 + P * (1+P)^s ≤ (1+P)^(suc s)`, one
--     binomial step, every P and s.
--   · sᵢ₊₁ ≡ sᵢ — DOES NOT close: it asks `1 + P * (1+P)^s ≤ (1+P)^s`,
--     false for every P ≥ 1.
-- So the ENTIRE residue is the SIZE-PRESERVING step — and that step is
-- REACHABLE, which is the next section.
--
-- ═══ THE SIZE-PRESERVING ARM IS NOT EMPTY.  REFUTED 2026-08-19 ═══
-- REFUTED: `Refuted.Hop-Drag.hop-drag-absurd`, which states and kills
-- the arm's whole content — "a step that does not GROW the accumulator
-- cannot DEEPEN it" — in the strongest form (the size hypothesis
-- compares new accumulator against old, not against the step's whole
-- argument).  So the invariant `hopDᵛ accᵢ ≤ (1 + P) ^ sizeᵛ accᵢ * B`
-- is not provable step-by-step, and the paragraph an earlier draft of
-- this header ended on — "what is owed is therefore that lemma, and
-- only that lemma" — was owed a FALSE lemma.
--
-- THE DRAG ARGUMENT HAS A HOLE, AND IT IS `caseᵗ`.  Demand-Probe series
-- Y (below, still standing) established the drag: a step can mention the
-- accumulator inside a `strmᵗ` only by substitution, `subΘ` substitutes
-- the reified argument SYNTACTICALLY, and projections are not reduced
-- away — so a wrapper that deepens the accumulator carries a full copy
-- of it and pays in size.  Series Y ran the sharpest attack available on
-- that (wrap one component of a pair, discard a large shallow sibling)
-- and collected no refund at all: 34 ↦ 51 ↦ 68, monotone.
--
-- What series Y could not reach is a BINDER.  A `caseᵗ` branch binds the
-- SCRUTINEE'S PAYLOAD, and evalWith EVALUATES the scrutinee before the
-- branch is substituted — so the branch's `strmᵗ` drags a copy of that
-- payload alone, not of the argument it was projected out of.
-- Scrutinising the small deep component wraps it while the large shallow
-- sibling is discarded for free.  The refutation's step does exactly
-- that and the first move SHRINKS the accumulator by 27 while DEEPENING
-- it: size 36 ↦ 9 ↦ 13 ↦ 17 against hopD 1 ↦ 2 ↦ 3 ↦ 4.
--
-- ⇒ THE ROW'S RISK CLASS IS UNCHANGED AND ITS RESIDUE HAS MOVED.  The
-- THEOREM is not in doubt — the refutation's own rows show why.  The
-- refund is ONE-SHOT: the sibling slot is spent by the step that
-- discards it, and from there the deep chain pays a flat +4 of size per
-- +1 of depth.  A shrinking step draws on a pool bounded by the
-- accumulator's INITIAL size, which the store invariant caps at V.  What
-- is refuted is the per-step reading, not the bound.
--
-- ═══ THE ROUTE THE REFUTATION LEAVES — TAKEN, AND HALF LANDED ═══
-- The exponent has to be a quantity the fold cannot DECREASE, and
-- `sizeᵛ accᵢ` is not one.  What the refuting step discards is a
-- sibling that was never carrying the depth; the deep component goes
-- on being copied.  So the exponent is the SPINE — size along the
-- hop-deepest path — and `Rx.Hop-Spine` defines it as `sizeᵉ/sizeᵗ/
-- sizeᵛ` with `⊔` at exactly hopD's branch positions (pairs, sums,
-- `ofᵉ` lists, caseᵗ/ifᵗ branches).  On the refutation's own run the
-- spine is 4 ↦ 7 ↦ 10 ↦ 13, strictly monotone across the very step
-- that drops 27 units of total size; pinned there beside it.
--
-- WHAT IS ALREADY PROVEN, and it is why this leaf is stated at the
-- spine rather than at F:
--   · `spn≤sizeᵛ` (Rx.Hop-Spine) — every ⊔ sits where size has a `+`,
--     so the store bound caps the spine too and no second cap is
--     needed anywhere downstream;
--   · `burstHopSpn-cap` (.Hop-Spine-Face) — the conversion, and
--     `walk-scan` below is a real body spending it: it takes this
--     leaf's spine-indexed burst, takes `walk-scan-rest`'s `burstB?`
--     size receipt at `frameStep (j + j′) c`, puts that frame under Ŝ
--     (a₄ then `lb` then `frameStep-mono-j` then `ceil`), and raises
--     the exponent to F once.  `hopDᵉ F η (scanᵉ f z b)` is
--     definitionally `(2 + pmᵗ F 0 f) ^ F * (…)`, so the conclusion
--     lands with no arithmetic at the boundary.
--
-- SO THE RESIDUE IS THE FOLD AT THE SPINE EXPONENT, and nothing else.
-- Two twins govern it, both PROVEN and both at this exact shape:
--   · `scanVals-size` (.Caps-Face/Part5) — the SAME fold over the SAME
--     list, threading a growing bound through `applyFn`; its clause
--     structure is what this leaf's induction copies;
--   · `hopD-evalWith` (.Measures) — the per-step substitution, whose
--     TIGHT form (before `hopD-applyFn` loosens the coefficient to
--     `pmᵗ V 0 f ⊔ 1`) already settles the degenerate half for free:
--     at `pmᵗ V 0 f ≡ 0` it gives `hopDᵛ (applyFn f v) ≤ hopDᵗ f ≤ B`
--     outright, so the arithmetic is only ever asked at `≥ 1`.
--
-- THE INVARIANT IS HEREDITARY, AND THAT DECISION IS LANDED (2026-08-19).
-- This leaf now concludes at `burstHopSpnH?` (.Hop-Spine-Face), whose
-- value predicate `valHopSpn?` recurses through pairs and sums and
-- bottoms out at `obs` with the headline inequality.  Headline-only
-- does not survive `fstᵗ`: projecting a pair yields a component whose
-- SPINE is smaller than the pair's (spnᵛ takes `⊔` and adds one) while
-- its DEPTH may be the pair's whole depth, and `evalWith` projects.
-- `valHopSpn?-hopD` (PROVEN) recovers the headline, and `walk-scan`
-- spends it through `burstHopSpnH-headline`, so the extra structure is
-- free at the consumer.
--
-- IT STOPS AT `obs`, which is the substantive half of the decision:
-- `Tm` HAS NO ELIMINATOR FOR `obs`.  The only eliminating term formers
-- are `fstᵗ`, `sndᵗ` and `caseᵗ` — pairs and sums and nothing else —
-- so those are exactly the positions where a bound can be projected
-- away, and exactly the positions the recursion covers.  Streams are
-- only ever BUILT, and a builder needs its argument's headline bound,
-- not its interior.  Recursing into the expression would be a second
-- structural induction and a second predicate to preserve, for nothing.
--
-- WHAT IS LEFT, all three with named PROVEN twins:
--   · the fold — `scanVals` preserves `valHopSpn?`; twin
--     `scanVals-size` (.Caps-Face/Part5), the same fold over the same
--     list, whose clause structure this copies;
--   · the step — `valHopSpn?` preserved by `evalWith` under an
--     env-wise hypothesis; twins `hopD-evalWith` (.Measures, the same
--     induction over Tm) and `evalWith-iterSize` (.Caps-Face/Part1,
--     which already carries an env predicate, `EnvSize`, in the shape
--     the env-wise hypothesis needs);
--   · the evaluator connection — subscribeE's scan clause emits the
--     fold's accumulators; the same job `walk-map` does for mapᵉ.
--
-- THE RESIDUE IS PROOF LABOUR, NOT A TRUTH QUESTION (Demand-Probe
-- series Ω, 2026-08-19).  Those rows are DEGENERATE and that is the
-- finding: run at the AMPLIFYING step (`pmᵗ V 0 fʸ ≡ 2`, the
-- accumulator plugged into a `mapᵉ` source, the one clause of hopDᵉ
-- that multiplies) the invariant clears by orders of magnitude, and it
-- could not have done otherwise.  Per step the depth multiplies by P
-- while the bound multiplies by `(2 + P) ^ Δspine`, and Δspine ≥ 1
-- whenever the accumulator is plugged at all — the drag, restated on
-- the spine, where it is TRUE.  Nor is a bigger P cheap: `pm-sizeᵗ`
-- (.Measures, PROVEN) bounds the multiplier by the template's own
-- size, and template size is what the step's spine contribution
-- charges for.  A step that multiplies the depth at ZERO spine cost
-- would refute this, and none is constructible — the plug must sit
-- under a `mapᵉ` source and that node is counted.
--
-- STILL DIFFICULTY, and the one open bookkeeping question is `caseᵗ`.
-- Its branch is evaluated under an EXTENDED env, so the step lemma has
-- to bound the branch's own plug slope, and the parent's `pmᵗ V j
-- (caseᵗ s l r)` does NOT see `pmᵗ V 0 l` when the scrutinee is closed
-- (`pmᵗ V j s ≡ 0` makes the coefficient's summand vanish).  `hopDᵗ`
-- does see it — `(pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1) * hopDᵗ s` — so it should
-- close through the depth side rather than the slope side.  Do NOT
-- probe that: a caseᵗ probe is degenerate for the same reason series Ω
-- is, so the only way to settle it is to write the clause.
--
-- ✗ DEAD ROUTE 2026-08-19 — A VALUE-LOCAL BOUND BASED ON `fnCapᵛ`.
-- Recorded because it is the obvious repair and it is one
-- instantiation from being checkable: a sharper twin of
-- `hopD-sizeᵗ`/`pm-sizeᵗ` (.Measures, both PROVEN, both landing at the
-- global `szB V (sizeᵗ tm)`) reading `hopDᵛ w ≤ (2 + fnCapᵛ w) ^
-- sizeᵛ w * <leaf depth>`, with the fold then carrying only ⊔-shaped
-- quantities — immune to the shrink, and `map-Ψ` (.Burst-Walk,
-- PROVEN) is already that step for `caseWᵗ ⊔ fnCapᵗ` under `applyFn`.
-- DEAD because the base comes out wrong by an unbounded margin: the
-- conjunct is measured against `pmᵗ V 0 f`, a SLOPE, and fnCap is a
-- CAP.  Take `f = pairᵗ (fstᵗ var) (strmᵗ (mapᵉ g (ofᵉ (nat̂ 0 ∷ []))))`
-- with `g` carrying a large `caseWᵗ`: the second component ignores the
-- argument, so `pmᵗ V 0 f = 1`, while `fnCapᵛ accᵢ ≥ caseWᵗ g` without
-- bound.  No choice of leaf depth repairs a base already too big, and
-- the same objection kills every measure of the VALUE ALONE — which is
-- why the spine is spent inside the fold rather than instead of it.
--
-- THE ADDITIVE CORNER IS NOT A SEPARATE CASE, correcting the P-split
-- above: at P = 1 the recurrence is Aᵢ₊₁ ≤ B + Aᵢ and the invariant
-- asks `1 + 2^s ≤ 2^(suc s)` — the same split, the same failing arm.
-- It is "comfortably true" only AFTER the size-preserving step is
-- discharged, so it buys no separate route.
postulate
  applyFn-hopSpn : ∀ {n} {Γ : Ctx n} {s u} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
    (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac : Val Γ u) (v : Val Γ s) →
    pmᵗ V 0 fn ≤ P →
    hopDᵗ V η fn ≤ B →
    valHopSpn? V η P B u ac ≡ true →
    valHopSpn? V η P B s v ≡ true →
    valHopSpn? V η P B u (applyFn fn (ac , v)) ≡ true

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


------------------------------------------------------------------
-- WHAT THE INTRODUCTION BUYS AT THE TWO PLACES THE SCAN WALK NEEDS IT.
-- The seed and the source burst both arrive as ORDINARY headline
-- receipts — `hopDᵗ z` and the walk face's own `burstHopD?` — and both
-- become hereditary here at no cost.
------------------------------------------------------------------

-- a closed term's value is no deeper than the term: hopD-evalWith at the
-- empty environment, where the slope sum is empty
hopD-evalTm : ∀ {n} {Γ : Ctx n} {u} (V : ℕ) (η : Fin n → ℕ)
  (z : Tm Γ [] [] [] u) → hopDᵛ V η u (evalTm z) ≤ hopDᵗ V η z
hopD-evalTm V η z =
  ≤-trans (hopD-evalWith V η (λ _ → 0) z []ᵃ tt)
          (≤-reflexive (+-identityʳ (hopDᵗ V η z)))

scanSeed-hopSpn : ∀ {n} {Γ : Ctx n} {u} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (z : Tm Γ [] [] [] u) → hopDᵗ V η z ≤ B →
  valHopSpn? V η P B u (evalTm z) ≡ true
scanSeed-hopSpn V η P B z hz =
  valHopSpn?-intro V η P B _ (evalTm z) (≤-trans (hopD-evalTm V η z) hz)

burstHopSpnH-intro : ∀ {n} {Γ : Ctx n} {u} (V : ℕ) (η : Fin n → ℕ) (P B C : ℕ)
  (str : Stream Γ u) → C ≤ B → burstHopD? V η C str ≡ true →
  burstHopSpnH? V η P B str ≡ true
burstHopSpnH-intro {u = u} V η P B C str hCB h =
  all-impl (λ em → all (hopDev? V η C) (InstEmit.events em))
           (λ em → all (evHopSpnH? V η P B) (InstEmit.events em))
           (λ em → all-impl (hopDev? V η C) (evHopSpnH? V η P B)
                            ev (InstEmit.events em))
           str h
  where
  ev : (x : InstEvent (Val _ u)) →
       hopDev? V η C x ≡ true → evHopSpnH? V η P B x ≡ true
  ev (value v) hx =
    valHopSpn?-intro V η P B u v
      (≤-trans (≤ᵇ⇒≤ (hopDᵛ V η u v) C (T-to hx)) hCB)
  ev (init _)    _ = refl
  ev (close _ _) _ = refl
  ev (handoff _) _ = refl
  ev complete    _ = refl
