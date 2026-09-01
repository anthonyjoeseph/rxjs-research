-- Verify-Budget-Sufficient.Caps-Term
-- evalTms-caps … unfoldμ-caps
module Verify-Budget-Sufficient.Caps-Term where

open import Data.Bool    using (true)
open import Data.Nat     using (ℕ; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤⇒≤ᵇ; ≤-trans; ≤-refl; ≤-reflexive; m≤m+n; m≤n+m; n≤1+n; <⇒≤; *-mono-≤; +-monoʳ-≤)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; map)
open import Data.Bool.ListAction using (all)
open import Data.Fin     using (Fin)
import Data.Fin as Fin
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym)

open import Rx.Prim      using (_at_from_as_; after_,_)
open import Rx.Exp       using (Ctx; sizeᵉ; sizeᵗ; sizeᵗˢ; Exp; Tm; μᵉ; unfoldμ; evalTm)
open import Rx.Frame-Width using (dWᵉ; dWᵗ; dWᵗˢ)
open import Rx.Evaluator using (iterSize)
open import Rx.Slots using (Slots)

-- .Delivery-Walk re-exports BOTH prerequisites of the cascade
-- conjuncts and adds the walk itself:
--
--   · .Caps holds the recurrence (Caps / frameStep / frameBlowup /
--     capsAt and their supply lemmas) and re-exports .Keeps-Ring, hence
--     .Measures.  Extracted so that a grind here no longer
--     re-checks .Wet — see that module's head.
--   · .Deliveries is the ledger stratum: where EvalSt.delivered moves
--     and where it provably does not, plus delivN and its composition
--     laws.  delivN is the currency the cascade conjuncts are stated in.
--   · .Delivery-Walk maps the delivery clique onto the LEVEL walk —
--     foldPath ↦ dCapᶜ, dispatchShare ↦ dCapᶜ, shareGo ↦ dWalkᶜ,
--     cascadeGo ↦ dWalkᶜ — RELATIVE to one frame's face at the level it
--     RUNS at, which it takes as a record of hypotheses rather than
--     postulating.  `walkH` below instantiates that record and
--     `cascadeGo-deliveries` is the theorem it buys.
open import Verify-Budget-Sufficient.Caps using
  (Caps; frameStep; iterFold-infl; iterFold-mono-count; iterSize-2^; iterSize-mono-count)
open import Verify-Budget-Sufficient.Measures using
  (n<2^n)
open import Verify-Budget-Sufficient.Keeps-Ring using
  (size-unfoldμ)
-- the nesting measure the subscribe budget descends on, and the frame
-- row that supplies it.  Re-exported, so the clique names one module
-- the depth mirror: `depthInner` is the fuel `thruOuter-face-core`'s
-- new hypothesis ranges over.  The rest of the family
-- carries THE DEPTH PREMISE down the frame chain, and it threads by
-- IDENTITY because the mirror is definitionally equal at every hop:
--   depthFrame … (from-inner op allNid inst) … fin = depthReact … fin
--   depthReact … true  = depthFin … (lookupNode allNid (EvalSt.nodes st))
--   depthReact … false = 0
-- so each face passes its premise straight to the next and the absorbed
-- branch needs nothing at all
-- arithmetic lemmas consumed by thruOuter-face-core's walk helpers

open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (evalTm-iterSize; iterSize-+; iterSize-mono-s; slotsCaps?; SlotWid; valCaps?)
open import Verify-Budget-Sufficient.Caps-Face.Part3 using
  (evalTm-iterFold; expWid-fromSize; wid-lift)
open import Verify-Budget-Sufficient.Caps-Face.Part2 using
  (slotsCaps?-slotWid; SlotWid-mono)
open import Decide using (T⇒≡true; ∧-intro)

------------------------------------------------------------------
-- THE THREE CLAUSES subscribeE-caps CANNOT DISCHARGE IN PLACE, GROUND
-- BESIDE IT.
--
-- Two of subscribeE's clauses BUILD VALUES BY EVALUATION and one
-- REBUILDS ITS OWN SYNTAX, and all three land exactly where
-- mapFrame-caps / scanFrame-caps already are: `evalTm` is `evalWith`
-- with an empty environment, an EVALUATION rather than a substitution,
-- and evalWith-size is a TOWER in the term's syntax (evalWith-sharp
-- only moves the exponent to `3 ^ caseWᵗ`).  So none of the three is
-- `sizeᵛ ≤ sizeᵗ` and each wants an existential j′ of its own — which
-- is affordable, because iterSize runs away faster than the clause
-- does, and is the same reason the two frame members are true.
--
-- Stated as tightly as the clauses consume them, so the difficulty has
-- a NAME and a boundary — no state, no recursion, no chain, just the
-- evaluator's own arithmetic — instead of being buried in the hub.
--
-- THE μ CLAUSE IS THE ONE THAT IS NOT ABOUT evalTm — and it is the one
-- that cost a refuted draft.  `unfoldμ body` is LARGER than `μᵉ body`
-- on the size axis, and the width axis was assumed stable and is not:
-- see the note on unfoldμ-caps below, and Hop-Descent-Probe's μwide,
-- which measures 0 ↦ 6.  Both halves now come off ONE size receipt:
-- size-unfoldμ (the μ's size squared) for the size, and the width
-- bridge above for the width.
------------------------------------------------------------------

-- `ofᵉ ts` bursts `map evalTm ts`, GROUND AND SYNTAX-COUNTED.  Both
-- halves of valCaps? are owed and each comes off its OWN receipt at the
-- same count: evalTm-iterSize spends one iterSize fold per syntax node
-- from an empty environment, evalTm-iterFold one foldStep per syntax
-- node from the telescope's leaf bound.  j′ = suc (sizeᵗˢ ts)
evalTms-caps : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (ts : List (Tm Γ [] [] [] u)) →
  2 ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  sizeᵗˢ ts ≤ Caps.cSize (frameStep j c) →
  dWᵗˢ n sl ts ≤ Caps.cWid (frameStep j c) →
  Σ ℕ λ j′ → all (valCaps? (frameStep (j + j′) c) sl u)
                 (map (λ tm → evalTm tm) ts) ≡ true
evalTms-caps {n = n} {Γ = Γ} {u = u} c j sl ts 2≤S slC szb wdb =
  suc a , go ts ≤-refl
  where
  S   = Caps.cSize c
  W   = Caps.cWid c
  V   = Caps.cWid (frameStep j c)
  a   = sizeᵗˢ ts
  M   = suc V
  1≤S = ≤-trans (s≤s z≤n) 2≤S
  slW : SlotWid sl M
  slW = SlotWid-mono sl (s≤s (iterFold-infl S 2≤S j W))
                     (slotsCaps?-slotWid S W sl slC)
  one : (tm : Tm Γ [] [] [] u) → sizeᵗ tm ≤ a →
        valCaps? (frameStep (j + suc a) c) sl u (evalTm tm) ≡ true
  one tm h =
    ∧-intro
      (T⇒≡true _ (≤⇒≤ᵇ
        (≤-trans (≤-trans (≤-trans (evalTm-iterSize S 1≤S tm)
                            (≤-trans (iterSize-mono-count S 0 1≤S h)
                                     (iterSize-mono-s S a z≤n)))
                          (≤-reflexive (sym (iterSize-+ S j a S))))
                 (iterSize-mono-count S S 1≤S (+-monoʳ-≤ j (n≤1+n a))))))
      (T⇒≡true _ (≤⇒≤ᵇ
        (wid-lift c j a 2≤S
          (≤-trans (evalTm-iterFold S M 2≤S (s≤s z≤n) sl slW tm)
                   (iterFold-mono-count S M 2≤S h)))))
  go : (vs : List (Tm Γ [] [] [] u)) → sizeᵗˢ vs ≤ a →
       all (valCaps? (frameStep (j + suc a) c) sl u)
           (map (λ tm → evalTm tm) vs) ≡ true
  go []       h = refl
  go (y ∷ ys) h =
    ∧-intro (one y (≤-trans (m≤m+n (sizeᵗ y) (sizeᵗˢ ys)) h))
            (go ys (≤-trans (m≤n+m (sizeᵗˢ ys) (sizeᵗ y)) h))

-- `scanᵉ f seed b` installs `scan-st (evalTm seed)`: the same statement
-- for one term, and the accumulator has to come back bounded on both
-- axes because capsOK? reads it on both.  j′ = suc (sizeᵗ z)
evalSeed-caps : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (z : Tm Γ [] [] [] u) →
  2 ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  sizeᵗ z ≤ Caps.cSize (frameStep j c) →
  dWᵗ n sl z ≤ Caps.cWid (frameStep j c) →
  Σ ℕ λ j′ → valCaps? (frameStep (j + j′) c) sl u (evalTm z) ≡ true
evalSeed-caps {n = n} {u = u} c j sl z 2≤S slC szz wdz =
  suc a
    , ∧-intro
        (T⇒≡true _ (≤⇒≤ᵇ
          (≤-trans (≤-trans (≤-trans (evalTm-iterSize S 1≤S z)
                              (iterSize-mono-s S a z≤n))
                            (≤-reflexive (sym (iterSize-+ S j a S))))
                   (iterSize-mono-count S S 1≤S (+-monoʳ-≤ j (n≤1+n a))))))
        (T⇒≡true _ (≤⇒≤ᵇ
          (wid-lift c j a 2≤S (evalTm-iterFold S M 2≤S (s≤s z≤n) sl slW z))))
  where
  S   = Caps.cSize c
  W   = Caps.cWid c
  V   = Caps.cWid (frameStep j c)
  a   = sizeᵗ z
  M   = suc V
  1≤S = ≤-trans (s≤s z≤n) 2≤S
  slW : SlotWid sl M
  slW = SlotWid-mono sl (s≤s (iterFold-infl S 2≤S j W))
                     (slotsCaps?-slotWid S W sl slC)

-- `μᵉ body` subscribes `unfoldμ body`, and BOTH AXES MOVE.  The size
-- axis was always going to: the unfolding is larger than the μ (only
-- syncSizeᵉ is preserved — syncSize-unfoldμ) by an amount no syntactic
-- measure in the file bounds.
--
-- THE WIDTH AXIS MOVES TOO, and the first draft of this said it did
-- not.  `dWᵉ (unfoldμ body) ≤ dWᵉ (μᵉ body)` reads plausible — the
-- plug lands at `varᵉ` positions and dWᵉ is 0 there — and it is
-- FALSE, refuted by Hop-Descent-Probe's μwide (0 ↦ 6).  hopD survives
-- an unfold because Δᵍ variables are reachable only under deferᵉ and
-- hopD CUTS a defer to 0; dW's whole reason to exist is that it does
-- NOT cut there, so the plug lands exactly where dW is looking and
-- exposes the μ's own outW — which dW does not bound.  Nor is it off
-- by a constant: k copies of the var in the template multiply through
-- innW's slope, so any true bound is affine in the plug's width with
-- the pmO/pmI coefficients, i.e. the hopD-subΘ machinery.
--
-- So the two axes are stated TOGETHER, at ONE existential j′ (which
-- is what the recursive call needs — both hypotheses at the same
-- level), and the width half is derived from the SIZE hypothesis the
-- telescope already carries rather than from the width one.  That is
-- affordable for the same reason the two frame postulates are:
-- iterFold is a tower in the cap and outW of an expression is a tower
-- in its size, so a large enough j′ covers it
unfoldμ-caps : ∀ {n} {Γ : Ctx n} {t} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (body : Exp Γ (t ∷ []) [] [] t) →
  2 ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  sizeᵉ (μᵉ body) ≤ Caps.cSize (frameStep j c) →
  dWᵉ n sl (μᵉ body) ≤ Caps.cWid (frameStep j c) →
  Σ ℕ λ j′ → (sizeᵉ (unfoldμ body) ≤ Caps.cSize (frameStep (j + j′) c))
           × (dWᵉ n sl (unfoldμ body) ≤ Caps.cWid (frameStep (j + j′) c))
unfoldμ-caps c j sl body 2≤S slC szb wdb =
  (m + suc (m * m))
    , ≤-trans SZ (iterSize-mono-count S S 1≤S
                    (+-monoʳ-≤ j (m≤m+n m (suc (m * m)))))
    , expWid-fromSize c j m (m * m) sl 2≤S slC (unfoldμ body)
        (size-unfoldμ body)
  where
  S   = Caps.cSize c
  B   = Caps.cSize (frameStep j c)
  m   = sizeᵉ (μᵉ body)
  1≤S = ≤-trans (s≤s z≤n) 2≤S
  -- QUADRATIC, AND ONE ROUND OF DOUBLING PER NODE CLEARS IT: unfolding
  -- plants the whole μ at each of the body's global-var positions
  -- (size-unfoldμ, the shared prerequisite in .Keeps-Ring), so the
  -- growth is the μ's size SQUARED — and iterSize at least doubles per
  -- fold (iterSize-2^), so the μ's OWN SIZE many folds cover the factor
  -- of m the squaring costs.  Both halves are counted in syntax: the
  -- unfolding IS syntax, so its width needs no cap read either
  quad : m * m ≤ iterSize S m B
  quad = ≤-trans (*-mono-≤ (<⇒≤ (n<2^n m)) szb) (iterSize-2^ S m B 1≤S)
  SZ : sizeᵉ (unfoldμ body) ≤ Caps.cSize (frameStep (j + m) c)
  SZ = ≤-trans (≤-trans (size-unfoldμ body) quad)
               (≤-reflexive (sym (iterSize-+ S j m S)))

