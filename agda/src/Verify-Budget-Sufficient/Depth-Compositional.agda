------------------------------------------------------------------
-- `depth-compositional`, ASSEMBLED — landed from
-- Depth-Compositional-Assembly (DELETED; git history) 2026-08-06, where the
-- shape was typechecked symbolically before paying this recheck.
--
-- THE MEASURE (`storeNestMax` and its four helpers) LIVES HERE, moved
-- from Depth-Bound.agda, because this module both defines the measure
-- and proves the compositional bound over it, while Depth-Bound
-- CONSUMES the bound (depth-capped) — the move is what breaks the
-- import cycle.  The node half is `boundedNode`'s own two live clauses
-- (Measures.agda) turned from a `≤ᵇ B` test into a `⊔`; the slot half
-- charges shared defs, the one channel `stBounded?` deliberately
-- excludes (slot defs are fixed syntax within one run, but `depthSlot`
-- reads them).
--
-- CLAUSE CENSUS (all 16 subscribe-side heads; the census findings from
-- the 2026-08-05 worker sweep are preserved in Depth-Bound's history
-- and the four load-bearing ones here):
--
-- (1) SCOPE IS 16 HEADS, NOT 19.  `depthFold`/`depthDisp`/
--     `depthShareGo`/`depthChain` are the DELIVERY family and are
--     never called from `depthE`'s clique.
-- (2) THE SECOND `suc` ARC IS OUT OF SCOPE.  `depthFinC`'s `yes refl`
--     arm is reached only through a `from-inner` Frame, which reaches
--     `depthFrame` only inside `depthFold` (Caps-Depth:393) — the
--     delivery family.  Taken standalone at `q = []` it computes
--     `suc 0 = 1` against a zero-able RHS, so it is FALSE as its own
--     obligation and must not be given this statement's shape.
-- (3) `depthBurst` calls `depthFrame` at the SAME `κ`, so
--     `thru-outer`'s `suc` is paid by the `*All` constructor's own
--     `sizeᵉ (mergeAllᵉ b) ≡ suc (sizeᵉ b)`, not by `pathLen`.
-- (4) THE REAL WORK: every clause that calls `depthBurst` feeds it the
--     state produced by running the REAL `subscribeE`, while the RHS
--     reads the ENTRY state.  The `storeNestMax`-preservation conjunct
--     is what `depth-all-bound` (below) absorbs; when it is ground it
--     must be proved as a second conjunct of the same induction, not a
--     separate family, and must NOT ride `subscribeE-caps` (circular —
--     that face takes `depthE ≤ dep` as a hypothesis).
--
-- BUCKETS: (a) trivially zero — ofᵉ, emptyᵉ, deferᵉ, g0(μᵉ),
-- takeᵉ(zero), and the g0 connect.  (b) IH + arithmetic — mapᵉ,
-- takeᵉ(suc), scanᵉ, over the burst-zero and installNode lemmas below.
-- (c) THE CONNECT, a real clause: `input` recurses into the slot's own
-- def and pays for it out of the summand admitting slot `i` to the
-- partial sum.  (d) BLOCKED, two named postulates —
-- `depth-all-bound` (needs the preservation conjunct, finding (4)) and
-- `depth-μ-bound` (sizeᵉ (unfoldμ body) > sizeᵉ (μᵉ body) kills the
-- size IH; the honest route is the guarded-context discipline —
-- μ-variable occurrences sit under deferᵉ, and deferᵉ contributes 0
-- to depthE).
--
-- TERMINATION: LEXICOGRAPHIC in (gas, b) — mapᵉ/scanᵉ/takeᵉ recurse on
-- the strict subterm at the same gas, and the connect recurses on a def
-- that is no subterm of anything but peels one gas doing it.  No pragma
-- needed, and it is checked: this module has no multi-member mutual
-- block, so `make agda-dev` emits it verbatim.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Depth-Compositional where

open import Data.Nat
  using (ℕ; zero; suc; _+_; _≤_; _⊔_; z≤n; s≤s; _≡ᵇ_; _<ᵇ_)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; m≤n+m; +-mono-≤; ⊔-lub; n≤1+n; m≤m⊔n; m≤n⊔m; +-suc; ≤-reflexive; ≤ᵇ⇒≤; n≮n;
  +-identityʳ; ⊔-mono-≤)
open import Data.Fin   using (Fin; toℕ)
open import Data.List  using (List; []; _∷_; foldr; tabulate)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)
open import Data.Nat.ListAction using (sum)
open import Data.Bool  using (Bool; false; true; if_then_else_; T; _∧_)
open import Data.Maybe using (nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Rx.Prim using (Gas; g0; gs; Id; Tick; InstEmit)
open import Rx.Exp
  using (natᵗ; _×ᵗ_; Ctx; Closed; Exp; Tm; Fn; Val; obs; evalTm; unfoldμ; elimGExp; sizeᵉ; sizeᵗ;
  input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ;
  varᵉ; deferᵉ; varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ;
  strmᵗ; inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ)
open import Rx.Evaluator
  using (Sched; EvalSt; NodeState; AllOp; NodeId; Path; Stream; scan-st; merge-st; concat-st;
  switch-st; exhaust-st; take-st; mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ; _↠_; map-f; scan-f;
  take-f; mintNode; installNode; subscribeE; splitEvents; stepFrame; setNode;
  share-sink; register)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵗ)
open import Rx.Slots using (scripted; shared; Slot; Slots)

-- pathLen, imported from .Measures where it is defined — the
-- SAME pathLen `depth-capped`'s statement reads, so the landing plugs
-- into its consumer unchanged.
open import Verify-Budget-Sufficient.Measures using
  (pathLen; sum-tab-mono; +-mix4)
open import Verify-Budget-Sufficient.Caps-Nest using (sum-tab-slack)
open import Data.Empty using (⊥-elim)
open import Decide using (force-false; T-to; ≤ᵇ-true; ≤ᵇ-widen; ∧ˡ; ∧ʳ)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthE; depthAll; depthBurst)

------------------------------------------------------------------
-- THE MEASURE — the state's contribution to subscribe-time depth,
-- validated by Depth-Compositional-Probe § A.
------------------------------------------------------------------

-- A NODE IS CHARGED FOR WHAT THE DEPTH FAMILY READS OUT OF IT, and
-- `lookupNode` appears exactly twice in that family: `depthConsumeS`,
-- whose only non-zero arm needs a `switch-st` and spends its `cur`
-- rather than its size, and `depthReact`, which routes to `depthFin`,
-- whose only non-zero arm needs a `concat-st` and WALKS its queue.  So
-- the queue is charged and everything else is 0 — a `scan-st` in
-- particular, whose accumulator no clause of the family ever looks at.
--
-- IT USED TO CHARGE `sizeᵛ t v` FOR A SCAN NODE, mirroring
-- `boundedNode`, and that over-approximation was the whole of one
-- postulate: the scan clause installs its seed before recursing, so the
-- IH ran against a store the entry-state right-hand side did not name,
-- and the gap was exactly the accumulator.  Charging the truth closes
-- it against the same `setNode` induction the take clause already used.
-- `boundedNode` is NOT changed to match — it is the state invariant the
-- caps face maintains, and the accumulator is bounded there for reasons
-- that have nothing to do with subscribe-side depth.
--
-- RECOVERY: the probe `Probed.Install-Scan`, deleted with that
-- postulate, held a four-link shared-slot chain under a scan whose
-- accumulator varied 1 → 41 with the depth flat at 4 — the measured
-- form of what the clause now proves.  `git log -S'Probed.Install-Scan'
-- --all` restores the fixture if a later measure needs one.
nodeNestMax : ∀ {n} {Γ : Ctx n} → NodeState Γ → ℕ
nodeNestMax (scan-st _)           = 0
nodeNestMax (concat-st {t} q _ _) = foldr (λ o acc → sizeᵉ o ⊔ acc) 0 q
nodeNestMax (take-st _)           = 0
nodeNestMax (merge-st _ _)        = 0
nodeNestMax (switch-st _ _)       = 0
nodeNestMax (exhaust-st _ _)      = 0

nodesNestMax : ∀ {n} {Γ : Ctx n} → List (NodeId × NodeState Γ) → ℕ
nodesNestMax = foldr (λ kv acc → nodeNestMax (proj₂ kv) ⊔ acc) 0

-- A SHARED SLOT PAYS ITS DEF'S NESTING TOO, and that is where the
-- refutation's product had to land.  A def reached through `input` is
-- entered by the mirror with the def in hand, so its own scan/`*All`
-- structure deepens exactly as the root program's does; charging only
-- `sizeᵉ d` was the same undercount `depth-all-bound` was refuted for.
--
-- Charging it HERE rather than descending inside `nestDᵉ` is forced:
-- see that module's header — a descending `input` clause is stuck on a
-- variable fuel.  What it costs is `slotNest-≤-slotSize` and the chain
-- above it, which fed the caps-conditioned interface this refutation
-- retires anyway.
slotNest : ∀ {n} {Γ : Ctx n} {k t} → Slots Γ → Slot Γ k t → ℕ
slotNest sl (shared d)   = sizeᵉ d + nestDᵉ sl d
slotNest sl (scripted _) = 0

-- A SUM OVER THE SLOTS, AND THE `foldr _⊔_ 0` IT REPLACES WAS
-- REFUTED — Refuted.Depth-Chain, and the defect was the CURRENCY
-- rather than any statement written over it.  Slots are STRATIFIED, so
-- slot k's def may reference inputs strictly below k and the connects
-- CHAIN; each link is traversed by one `thru-outer` frame and the arcs
-- ADD.  A max over the slots does not grow with the chain at all, so
-- the two sides grew in different variables — the left in the chain
-- LENGTH, the right in one def's SIZE — and a chain longer than its
-- largest def crossed: nine links of size 5 over a base of size 7
-- measured depth 9 against a store of 7, and against the parent's own
-- right-hand side of 8.
--
-- A SUM IS THE RIGHT CURRENCY BECAUSE THE CHAIN CANNOT REVISIT.
-- Stratification makes the connect indices strictly decreasing, so
-- each slot is entered at most once along any path and `Σ slotNest`
-- pays for the whole chain; pointwise `slotNest ≤ slotSize` then keeps
-- it under the caps, which is what `slots-nest-≤-size` and
-- `storeNest-capped` do — and the sum form makes that proof SMALLER,
-- since it is sum monotonicity rather than max-of-tabulate ≤
-- sum-of-tabulate.
--
-- NOT A WEAKENING: the max was false, so this replaces a refuted
-- measure rather than retreating from a true one.  Every statement
-- written over `storeNestMax` keeps its text verbatim, which is why
-- the refutation cost no clause below it.
--
-- THE NODE HALF IS NOT COVERED BY THAT ARGUMENT and is unprobed:
-- `storeNestMax` still joins the two halves with `⊔`, because `+`
-- there would need `slotsSize + nodeCeil ≤ cSize` and the caps supply
-- each side separately.  Whether reads of parked observables chain the
-- way slot defs do wants a state the evaluator actually REACHED, so it
-- is a separate build.
slotsNestSum : ∀ {n} {Γ : Ctx n} → Slots Γ → ℕ
slotsNestSum {n} sl = sum (tabulate {n = n} (λ i → slotNest sl (sl i)))

storeNestMax : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ → EvalSt e → ℕ
storeNestMax sched st =
  slotsNestSum (Sched.slots sched) ⊔ nodesNestMax (EvalSt.nodes st)

------------------------------------------------------------------
-- THE PARTIAL SUM — the same currency restricted to the slots a term
-- can actually reach.  `slotsNestSum` pays for a whole chain, which is
-- what the refutation forced, but it pays for it ALL AT ONCE and so
-- cannot pay again: the assembly's `input` clause recurses on the
-- slot's def and charges that def's size on top of a term that already
-- included it.  Restricting the sum to indices strictly below the term's
-- own reach makes the charge SEPARATE from the payment — the def lives
-- strictly lower than the slot holding it, so the slot's own summand is
-- exactly the room the recursion needs.
--
-- INDEXED BY THE TERM AND NOT BY A HYPOTHESIS, deliberately.  A `k`
-- parameter with `T (inputsBelowᵉ k b)` alongside says the same thing,
-- and costs a projection in every clause plus a lemma saying every
-- closed term over `Ctx n` has its inputs below `n` — which is an
-- induction over the whole syntax, bought only to discharge the
-- top-level instantiation.  Reading the bound OFF the term needs no
-- hypothesis anywhere and no such lemma: the top-level statement is
-- unconditional, and stratification is consulted at the one clause that
-- uses it.
------------------------------------------------------------------

mutual
  maxInputᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → ℕ
  maxInputᵉ (input i)       = suc (toℕ i)
  maxInputᵉ (ofᵉ ts)        = maxInputᵗˢ ts
  maxInputᵉ emptyᵉ          = 0
  maxInputᵉ (mapᵉ f e)      = maxInputᵗ f ⊔ maxInputᵉ e
  maxInputᵉ (takeᵉ c e)     = maxInputᵗ c ⊔ maxInputᵉ e
  maxInputᵉ (scanᵉ f z e)   = maxInputᵗ f ⊔ maxInputᵗ z ⊔ maxInputᵉ e
  maxInputᵉ (mergeAllᵉ e)   = maxInputᵉ e
  maxInputᵉ (concatAllᵉ e)  = maxInputᵉ e
  maxInputᵉ (switchAllᵉ e)  = maxInputᵉ e
  maxInputᵉ (exhaustAllᵉ e) = maxInputᵉ e
  maxInputᵉ (μᵉ e)          = maxInputᵉ e
  maxInputᵉ (varᵉ x)        = 0
  maxInputᵉ (deferᵉ e)      = maxInputᵉ e

  maxInputᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ Δᵍ Δ Θ t → ℕ
  maxInputᵗ (varᵗ x)      = 0
  maxInputᵗ unit̂          = 0
  maxInputᵗ (bool̂ _)      = 0
  maxInputᵗ (nat̂ _)       = 0
  maxInputᵗ (pairᵗ a b)   = maxInputᵗ a ⊔ maxInputᵗ b
  maxInputᵗ (fstᵗ p)      = maxInputᵗ p
  maxInputᵗ (sndᵗ p)      = maxInputᵗ p
  maxInputᵗ (inlᵗ a)      = maxInputᵗ a
  maxInputᵗ (inrᵗ a)      = maxInputᵗ a
  maxInputᵗ (caseᵗ s l r) = maxInputᵗ s ⊔ maxInputᵗ l ⊔ maxInputᵗ r
  maxInputᵗ (ifᵗ c a b)   = maxInputᵗ c ⊔ maxInputᵗ a ⊔ maxInputᵗ b
  maxInputᵗ (primᵗ _ a)   = maxInputᵗ a
  maxInputᵗ (strmᵗ e)     = maxInputᵉ e

  maxInputᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  maxInputᵗˢ []       = 0
  maxInputᵗˢ (t ∷ ts) = maxInputᵗ t ⊔ maxInputᵗˢ ts

-- STRATIFICATION, READ OFF THE SYNTAX.  `shared`'s `ok` field IS
-- `T (inputsBelowᵉ (toℕ i) d)`, so the fact the `input` clause needs is
-- already carried by the slot it reads — this is the one place the
-- restatement consults it, and the induction is a transcription of
-- `inputsBelowᵉ`'s own clauses.
mutual
  inputsBelow⇒maxᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k : ℕ)
    (e : Exp Γ Δᵍ Δ Θ t) → T (inputsBelowᵉ k e) → maxInputᵉ e ≤ k
  inputsBelow⇒maxᵉ k (input i)       h = ≤ᵇ⇒≤ (suc (toℕ i)) k h
  inputsBelow⇒maxᵉ k (ofᵉ ts)        h = inputsBelow⇒maxᵗˢ k ts h
  inputsBelow⇒maxᵉ k emptyᵉ          h = z≤n
  inputsBelow⇒maxᵉ k (mapᵉ f e)      h =
    ⊔-lub (inputsBelow⇒maxᵗ k f (∧ˡ (inputsBelowᵗ k f) (inputsBelowᵉ k e) h))
          (inputsBelow⇒maxᵉ k e (∧ʳ (inputsBelowᵗ k f) (inputsBelowᵉ k e) h))
  inputsBelow⇒maxᵉ k (takeᵉ c e)     h =
    ⊔-lub (inputsBelow⇒maxᵗ k c (∧ˡ (inputsBelowᵗ k c) (inputsBelowᵉ k e) h))
          (inputsBelow⇒maxᵉ k e (∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k e) h))
  inputsBelow⇒maxᵉ k (scanᵉ f z e)   h =
    ⊔-lub (⊔-lub (inputsBelow⇒maxᵗ k f (∧ˡ (inputsBelowᵗ k f) rest h))
                 (inputsBelow⇒maxᵗ k z (∧ˡ (inputsBelowᵗ k z)
                                            (inputsBelowᵉ k e) tl)))
          (inputsBelow⇒maxᵉ k e (∧ʳ (inputsBelowᵗ k z)
                                     (inputsBelowᵉ k e) tl))
    where
    rest : Bool
    rest = inputsBelowᵗ k z ∧ inputsBelowᵉ k e
    tl : T rest
    tl = ∧ʳ (inputsBelowᵗ k f) rest h
  inputsBelow⇒maxᵉ k (mergeAllᵉ e)   h = inputsBelow⇒maxᵉ k e h
  inputsBelow⇒maxᵉ k (concatAllᵉ e)  h = inputsBelow⇒maxᵉ k e h
  inputsBelow⇒maxᵉ k (switchAllᵉ e)  h = inputsBelow⇒maxᵉ k e h
  inputsBelow⇒maxᵉ k (exhaustAllᵉ e) h = inputsBelow⇒maxᵉ k e h
  inputsBelow⇒maxᵉ k (μᵉ e)          h = inputsBelow⇒maxᵉ k e h
  inputsBelow⇒maxᵉ k (varᵉ x)        h = z≤n
  inputsBelow⇒maxᵉ k (deferᵉ e)      h = inputsBelow⇒maxᵉ k e h

  inputsBelow⇒maxᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k : ℕ)
    (m : Tm Γ Δᵍ Δ Θ t) → T (inputsBelowᵗ k m) → maxInputᵗ m ≤ k
  inputsBelow⇒maxᵗ k (varᵗ x)      h = z≤n
  inputsBelow⇒maxᵗ k unit̂          h = z≤n
  inputsBelow⇒maxᵗ k (bool̂ _)      h = z≤n
  inputsBelow⇒maxᵗ k (nat̂ _)       h = z≤n
  inputsBelow⇒maxᵗ k (pairᵗ a b)   h =
    ⊔-lub (inputsBelow⇒maxᵗ k a (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k b) h))
          (inputsBelow⇒maxᵗ k b (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k b) h))
  inputsBelow⇒maxᵗ k (fstᵗ p)      h = inputsBelow⇒maxᵗ k p h
  inputsBelow⇒maxᵗ k (sndᵗ p)      h = inputsBelow⇒maxᵗ k p h
  inputsBelow⇒maxᵗ k (inlᵗ a)      h = inputsBelow⇒maxᵗ k a h
  inputsBelow⇒maxᵗ k (inrᵗ a)      h = inputsBelow⇒maxᵗ k a h
  inputsBelow⇒maxᵗ k (caseᵗ x l r) h =
    ⊔-lub (⊔-lub (inputsBelow⇒maxᵗ k x (∧ˡ (inputsBelowᵗ k x) rest h))
                 (inputsBelow⇒maxᵗ k l (∧ˡ (inputsBelowᵗ k l)
                                            (inputsBelowᵗ k r) tl)))
          (inputsBelow⇒maxᵗ k r (∧ʳ (inputsBelowᵗ k l)
                                     (inputsBelowᵗ k r) tl))
    where
    rest : Bool
    rest = inputsBelowᵗ k l ∧ inputsBelowᵗ k r
    tl : T rest
    tl = ∧ʳ (inputsBelowᵗ k x) rest h
  inputsBelow⇒maxᵗ k (ifᵗ c a b)   h =
    ⊔-lub (⊔-lub (inputsBelow⇒maxᵗ k c (∧ˡ (inputsBelowᵗ k c) rest h))
                 (inputsBelow⇒maxᵗ k a (∧ˡ (inputsBelowᵗ k a)
                                            (inputsBelowᵗ k b) tl)))
          (inputsBelow⇒maxᵗ k b (∧ʳ (inputsBelowᵗ k a)
                                     (inputsBelowᵗ k b) tl))
    where
    rest : Bool
    rest = inputsBelowᵗ k a ∧ inputsBelowᵗ k b
    tl : T rest
    tl = ∧ʳ (inputsBelowᵗ k c) rest h
  inputsBelow⇒maxᵗ k (primᵗ _ a)   h = inputsBelow⇒maxᵗ k a h
  inputsBelow⇒maxᵗ k (strmᵗ e)     h = inputsBelow⇒maxᵉ k e h

  inputsBelow⇒maxᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k : ℕ)
    (ms : List (Tm Γ Δᵍ Δ Θ t)) → T (inputsBelowᵗˢ k ms) →
    maxInputᵗˢ ms ≤ k
  inputsBelow⇒maxᵗˢ k []       h = z≤n
  inputsBelow⇒maxᵗˢ k (m ∷ ms) h =
    ⊔-lub (inputsBelow⇒maxᵗ  k m  (∧ˡ (inputsBelowᵗ k m)
                                      (inputsBelowᵗˢ k ms) h))
          (inputsBelow⇒maxᵗˢ k ms (∧ʳ (inputsBelowᵗ k m)
                                      (inputsBelowᵗˢ k ms) h))

slotNestBelow : ∀ {n} {Γ : Ctx n} → Slots Γ → ℕ → Fin n → ℕ
slotNestBelow sl k i = if toℕ i <ᵇ k then slotNest sl (sl i) else 0

slotsNestBelow : ∀ {n} {Γ : Ctx n} → Slots Γ → ℕ → ℕ
slotsNestBelow {n} sl k = sum (tabulate {n = n} (slotNestBelow sl k))

-- MONOTONE IN THE CUT, pointwise then summed.  Raising the cut can only
-- unmask summands, never change one.  The boolean half is already in
-- `Decide`: `_<ᵇ_` IS `suc _ ≤ᵇ _`, so `≤ᵇ-widen` is exactly the
-- widening and `≤ᵇ-true` exactly the unmasking at `suc (toℕ i)`.
if-mono : ∀ (b b′ : Bool) (x : ℕ) → (b ≡ true → b′ ≡ true) →
  (if b then x else 0) ≤ (if b′ then x else 0)
if-mono false _     x h = z≤n
if-mono true  true  x h = ≤-refl
if-mono true  false x h with h refl
... | ()

slotNestBelow-mono : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (k k′ : ℕ) → k ≤ k′ →
  (i : Fin n) → slotNestBelow sl k i ≤ slotNestBelow sl k′ i
slotNestBelow-mono sl k k′ le i =
  if-mono (toℕ i <ᵇ k) (toℕ i <ᵇ k′) (slotNest sl (sl i))
          (≤ᵇ-widen (suc (toℕ i)) le)

slotsNestBelow-mono : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (k k′ : ℕ) → k ≤ k′ →
  slotsNestBelow sl k ≤ slotsNestBelow sl k′
slotsNestBelow-mono {n} sl k k′ le =
  sum-tab-mono {n} (slotNestBelow sl k) (slotNestBelow sl k′)
    (slotNestBelow-mono sl k k′ le)

-- AND UNDER THE FULL SUM whatever the cut, which is what keeps every
-- statement written over `storeNestMax` and its cap untouched
-- THE CAP `depth-compositional` IS PROVED AGAINST, and the whole
-- reason it is not `storeNestMax`.  The slot half is read at the
-- program's OWN stratification level rather than over every slot,
-- which is what turns the connect from a postulate into a clause.
--
-- ITS PREDECESSORS ARE BOTH REFUTED, and the second refutation is what
-- moved the measure.  A statement over the DEF `d`, quantified over
-- every `Closed Γ (lookup Γ i)` with nothing tying it to `sched`, dies
-- to Refuted.Depth-Conn; reading the slot inside the statement instead
-- fixes that but then dies to Refuted.Depth-Chain over the MAX that
-- `storeNestMax` used to be, 9 depth against a max of 7.  Making the
-- slot half a SUM survives that witness (9 against 47) with a margin
-- that grows down the chain, which is the property the max lacked.
--
-- AND A `⊔` BETWEEN THE PATH AND THE STORE IS DEAD, a fortiori by the
-- same witness: `(sizeᵉ b + pathLen κ) ⊔ storeNestMax` gives `1 ⊔ 7`
-- against 9.  A max cannot pay for a CHAIN of connects.  Recorded
-- because it was the plausible next move.
--
-- DEAD ROUTE 2026-08-21: the RESIDUE currency, which is the obvious
-- candidate because the exact accounting already exists and is
-- PROVEN — `resid sl cs` masks a slot that is in `connectedShares`,
-- `resid-connect` says the residue falls by precisely the connected
-- slot's weight, `depthConn` conses `toℕ i` on before recursing, and
-- the caps face already threads `nest b sl (EvalSt.connectedShares
-- st)` at these very call sites.  The payment is exact and it is
-- still dead: the residue is 0 at a slot already connected, while the
-- MIRROR charges the connect there anyway.  `subscribeSharedSlot`
-- short-circuits on a spent share and `depthShSlot` does not — a
-- sound over-approximation of "does nothing", and exactly the loss
-- the accounting cannot absorb.  Measured at the nine-link chain with
-- `connectedShares` saturated: residue 0, node half 0, depth 9.  So
-- the route reopens only by making the mirror short-circuit too, which
-- is a change to `depthE` and invalidates every statement about it.
--
-- WHAT THE PARTIAL SUM HAS THAT THE RESIDUE LACKED, three things.  It
-- reads STRATIFICATION, already in the syntax, since `shared`'s `ok`
-- field IS `T (inputsBelowᵉ (toℕ i) d)`, so nothing about the mirror
-- moves.  The payment is an EQUALITY rather than a bound, because
-- `slotNest (shared d)` is `sizeᵉ d` on the nose.  And the strict
-- decrease in `i` that pays for the arithmetic is simultaneously the
-- termination measure for a recursion that is not structural in `b`.
--
-- PROBED-HISTORICAL 2026-08-21: the measure was instantiated before
-- being adopted — accumulating chains at 6 and 9 links, partial sum 33
-- and 48 against depth 6 and 9, and an `obs`-ladder chain whose links
-- cost 2 apiece has depth 1 at BOTH lengths, because a bare
-- `mergeAllᵉ (input j)` recurses on the subscribe side where the
-- mirror charges nothing and every `suc` comes from a `thru-outer`
-- burst.  The size a link spends on re-wrapping is what GENERATES the
-- depth, so the ratio is bounded away from 1 by the mechanism rather
-- than by the encoding.  NOT COVERED: a non-empty node store, and a
-- `scripted` slot mixed into a chain.
--
-- ONE THING THE SHAPE FORCES, and it is a real cost: the `⊔` with the
-- node half sits OUTSIDE, so the slot-side arithmetic happens inside
-- the left arm.  With the join where `storeNestMax` puts it, a node
-- half that dominates leaves the connect needing
-- `sizeᵉ d ≤ suc (pathLen κ)`, which no hypothesis offers.  Outward it
-- goes through, and `storeNest-capped`'s `⊔-lub` split survives — which
-- a `+` would NOT, since that needs the SUM of two quantities the caps
-- bound only separately.
depthCapN : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sz mx : ℕ) (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) → ℕ
depthCapN sz mx κ sched st =
  (sz + pathLen κ + slotsNestBelow (Sched.slots sched) mx)
    ⊔ nodesNestMax (EvalSt.nodes st)

depthCap : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {e : Closed Γ t} {u}
  (b : Exp Γ Δᵍ Δ Θ u) (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) → ℕ
depthCap {n = n} b κ sched st =
  depthCapN (sizeᵉ b + nestDᵉ (Sched.slots sched) b) (maxInputᵉ b) κ sched st

slotsNestBelow-≤-sum : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (k : ℕ) →
  slotsNestBelow sl k ≤ slotsNestSum sl
slotsNestBelow-≤-sum {n} sl k =
  sum-tab-mono {n} (slotNestBelow sl k) (λ i → slotNest sl (sl i))
    (λ i → if-mono (toℕ i <ᵇ k) true (slotNest sl (sl i)) (λ _ → refl))

-- and the bridge the export spends: the below-sum is a summand of the
-- whole sum, and the node half is the other arm of `storeNestMax`'s
-- own join, so the exported statement keeps its text verbatim and
-- nothing downstream of this module moves.
cap-≤-store : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {e : Closed Γ t} {u}
  (b : Exp Γ Δᵍ Δ Θ u) (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) →
  depthCap b κ sched st
    ≤ sizeᵉ b + nestDᵉ (Sched.slots sched) b + pathLen κ
        + storeNestMax sched st
cap-≤-store {n = n} b κ sched st = ⊔-lub slotHalf nodeHalf
  where
  SZ : ℕ
  SZ = sizeᵉ b + nestDᵉ (Sched.slots sched) b
  slotHalf : SZ + pathLen κ + slotsNestBelow (Sched.slots sched) (maxInputᵉ b)
               ≤ SZ + pathLen κ + storeNestMax sched st
  slotHalf = +-mono-≤ ≤-refl
               (≤-trans (slotsNestBelow-≤-sum (Sched.slots sched) (maxInputᵉ b))
                        (m≤m⊔n _ _))
  nodes≤store : nodesNestMax (EvalSt.nodes st) ≤ storeNestMax sched st
  nodes≤store = m≤n⊔m _ _
  store≤goal : storeNestMax sched st
                 ≤ SZ + pathLen κ + storeNestMax sched st
  store≤goal = m≤n+m (storeNestMax sched st) (SZ + pathLen κ)
  nodeHalf : nodesNestMax (EvalSt.nodes st)
               ≤ SZ + pathLen κ + storeNestMax sched st
  nodeHalf = ≤-trans nodes≤store store≤goal

-- THE PAYMENT, and it is an EQUALITY at the one index that matters.
-- Slot `i`'s summand is masked out below the cut `toℕ i` and present at
-- `suc (toℕ i)`, so admitting slot `i` to the sum buys exactly
-- `slotNest sl (sl i)` — which is `sizeᵉ d + nestDᵉ sl d` on the nose
-- for the def the assembly is about to recurse on.  That is the whole
-- content of the restatement: the charge and the payment are the same
-- number, and they stayed the same number when the nesting term was
-- added to both sides of it.
<ᵇ-irrefl : ∀ (a : ℕ) → (a <ᵇ a) ≡ false
<ᵇ-irrefl a = force-false (a <ᵇ a)
  (λ h → ⊥-elim (n≮n a (≤ᵇ⇒≤ (suc a) a (T-to h))))

slotsNestBelow-step : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (i : Fin n) →
  slotNest sl (sl i) + slotsNestBelow sl (toℕ i)
    ≤ slotsNestBelow sl (suc (toℕ i))
slotsNestBelow-step sl i =
  sum-tab-slack (slotNestBelow sl (toℕ i)) (slotNestBelow sl (suc (toℕ i)))
    (slotNest sl (sl i))
    (slotNestBelow-mono sl (toℕ i) (suc (toℕ i)) (n≤1+n (toℕ i)))
    i slack
  where
  slack : slotNest sl (sl i) + slotNestBelow sl (toℕ i) i
            ≤ slotNestBelow sl (suc (toℕ i)) i
  slack rewrite <ᵇ-irrefl (toℕ i)
              | ≤ᵇ-true (suc (toℕ i)) (suc (toℕ i)) ≤-refl
        = ≤-reflexive (+-identityʳ (slotNest sl (sl i)))

------------------------------------------------------------------
-- BUCKET (d) — the three hard postulates (schedule-blockers)
------------------------------------------------------------------

postulate
  -- depthAll's burst uses thru-outer (the spending arc).  Bounding the
  -- inner subscribes requires storeNestMax preservation through
  -- subscribeE proved simultaneously (census finding (4)).
  --
  -- PROBED 2026-08-21 (Probed.Depth-All): the burst takes a MAX across
  -- SIBLINGS, not a sum.  A merge over one slot-chain top measures 5;
  -- a merge over two independent 4-link chains measures 5 as well,
  -- with the store held at 51 in both rows by using the same slots.
  -- So the arc that accumulates is the CONNECT — which is what forced
  -- `slotsNestSum` (Refuted.Depth-Chain) — and NOT the sibling entry,
  -- so `suc (sizeᵉ b)` is not being asked to pay for k chains.  This
  -- was the live falsity candidate once the chain finding landed, and
  -- it is the region the rows reached.
  -- Shapes NOT covered: `mergeAllᵉ` only, so no concat/switch/exhaust
  -- burst (different `initSt`, and their queueing is what
  -- `nodesNestMax` charges); no nested burst; no post-cascade state;
  -- and both arms are the same length, so a burst over siblings of
  -- DIFFERENT depths is untested.
  --
  -- RESTATED over `depthCapN` when the connect landed, and the rows were
  -- re-read rather than inherited: the two-chain program measures 5
  -- against a cap of 51, where the `storeNestMax` bound it replaced gave
  -- 58.  The mirror-side findings above are untouched, since nothing
  -- about `depthAll` moved — only the right-hand side, and it got
  -- SMALLER, which is the direction that could have refuted this.
  --
  -- ITS PREDECESSOR IS REFUTED 2026-08-21 (Refuted.Depth-Nest), AND THE
  -- RECEIPT ABOVE IS WHAT AIMED IT: the one shape it names as untested is
  -- a NESTED burst, and that is the shape the predecessor — the same
  -- statement with `depthCapN (suc (sizeᵉ b))` and no nesting term —
  -- dies at.  The statement below adds `suc (nestDᵉ …)` to that first
  -- argument, so it is strictly weaker than the refuted form and the
  -- witness does not reach it; what follows is why.  A `scanᵉ`
  -- whose step function wraps its own accumulator gains `w` nesting
  -- levels PER TICK while the syntax gains `4` per wrap and `1` per
  -- listed source value — so the left side grows in `w · k` and the
  -- right in `w + k`, and at `w = 4, k = 12` the depth is 49 against a
  -- cap of 38.  `depthE` of a `scanᵉ` charges its emissions nothing
  -- (`burst-scf-zero`), which is exactly what makes a scan a free
  -- generator of nesting; the charge lands only here, in the `*All`
  -- that consumes it.
  --
  -- The sibling-max finding above SURVIVES and is not what failed: the
  -- burst does take a max across siblings.  It accumulates down
  -- NESTING, which is a different axis and the one no syntactic term
  -- can pay for.  Restating means conditioning on the caps, whose
  -- `valCaps?` already bounds `sizeᵛ` — and `sizeᵛ (obs t) v` IS
  -- `sizeᵉ v`, so the nesting of a reachable value is bounded there and
  -- nowhere in the program text.
  --
  -- AND THE RESTATEMENT DOES NOT STOP AT `depth-capped`, WHICH THIS
  -- HEADER PREVIOUSLY CLAIMED IT WOULD.  `3 · cSize` has room at THIS
  -- witness (114 against 49) and none in general, because a constant
  -- multiple is still linear: `depth-capped-absurd` walks the same
  -- family out to `w = 7, k = 29` and measures 204 against 201.  The
  -- interface has to move too.
  --
  -- THE CURRENCY TO MOVE IT INTO IS ALREADY IN THE TREE, and it is not
  -- a bigger multiple.  `scanFrame-caps` charges a scan frame
  -- `length vals * suc (sizeᵗ fn)` folds — burst cardinality times step
  -- size, which is `k · w` with the two factors named — and the size
  -- and width faces both read their bound at that count
  -- (`iterSize S (length vals * suc (sizeᵗ fn)) B`,
  -- `iterFold S … M`).  So the product this statement dies on is the
  -- product those faces already pay, and the depth face is the one
  -- reading a linear cap where its siblings read a fold count.
  --
  -- AND THE OBLIGATION ON A NEW CONCLUSION IS WEAK, once the right
  -- consumer is read.  A depth bound spent through `opIterD` does climb
  -- levels tower-ly per unit — `opIterD`'s `d` slot passes to `fLvlD`,
  -- whose `suc d` clause unfolds a whole `sIterD` sweep — but that `dep`
  -- bounds `depthInner`, and it arrives on `sub-charge-capsOK-lift`'s
  -- `depOK` premise rather than from this family.  What this statement
  -- feeds is `depth-capped`, and `depth-capped` has exactly ONE consumer:
  -- `depthE≤capsH-root`, chaining into `capsH e ins 0` through
  -- `three-size-le-blowH`.  So all a restatement owes is to sit under
  -- `blowH (capsBase e ins)`, which carries `2 * poolCount (towerℕ m) m`
  -- and is astronomically above any exponential in `sizeᵉ e`.
  --
  -- PROBED 2026-08-21 (Probed.Nest-Depth), AND THE MEASURE IS DERIVED
  -- RATHER THAN FITTED — which is why the rows ask for EQUALITY and not
  -- domination.  Charge one `suc` per `*All` layer, because that is what
  -- `depthFrame` at `thru-outer` charges, and charge a `scanᵉ` its
  -- SOURCE'S PAYLOAD COUNT times its step function's layers, because the
  -- accumulator is re-wrapped once per delivered payload and the scan's
  -- own frame charges its emissions nothing.  The resulting measure
  -- equals `depthE` on the nose at both crossings the refutation walks:
  -- 49 at four wraps over twelve ticks, 204 at seven over twenty-nine.
  -- Two products, so no constant passes both, and a zero-wrap row pins
  -- the collapse to 1.
  --
  -- AND THE PRODUCT COMPOUNDS, which is the row that settles the
  -- currency rather than merely confirming the measure.  Put a scan
  -- inside the outer scan's STEP FUNCTION, seeded by the incoming
  -- accumulator, and the inner scan's layers are re-applied once per
  -- outer payload: the measure predicts `j · (k · w + 1) + 1`, and
  -- `depthE` returns exactly that (22 at two wraps, three inner, three
  -- outer).  One factor per nested scan, with no bound on how many.
  --
  -- So `depthE` is EXPONENTIAL in the program size — each factor costs a
  -- constant of syntax and multiplies — and every fixed-degree product
  -- of caps fields is dead, `cSize · cSize` included.  That closes the
  -- guess two commits back by measurement rather than by argument, and
  -- it sharpens the one open question to a single arithmetic one: the
  -- depth bound is spent as a LEVEL COUNT through `opIterD`, and levels
  -- exponentiate, so what has to be checked is whether the height
  -- budget absorbs an EXPONENTIAL level count.  A tower it certainly
  -- does not (`Caps`'s own header defends that when it forbids `cWid`
  -- from re-entering the delivery count); an exponential is undecided
  -- and is the next thing to settle.
  --
  -- Shapes NOT covered: `mergeAllᵉ` only, so no concat/switch/exhaust
  -- layer, whose queueing `nodesNestMax` charges separately; no slot
  -- descent, so the connect arc is unmeasured here and `slotsNestBelow`
  -- is the term that would carry it; no post-cascade state; and the
  -- compounding row is degree THREE, so nothing here says the pattern
  -- continues past it — only that it does not stop at two.
  --
  -- AND THE ROUTE INTO `src` HAD ONE DESIGN CHOICE IN IT, WHOSE FIRST
  -- ANSWER WAS WRONG.  Enlarging `depthCap`'s first summand to
  -- `sizeᵉ b + nestDᵉ b` leaves the `input` clause owing the SLOT
  -- definition's nesting, and there were exactly two places to pay it.
  --
  -- DEAD ROUTE 2026-08-21: PAY IT IN THE MEASURE, by descending into
  -- slot definitions on slot fuel with a visited set — `outWⱽ`'s shape,
  -- whose `input` clause is already written that way and whose `j` is
  -- the lexicographic measure a connect spends.  It was chosen first,
  -- and for a good reason: it kept `slots-nest-≤-size`, which held
  -- `slotNest` pointwise under `slotsSize` and kept `storeNest-capped`
  -- under the caps.  It is STRUCTURALLY DEAD.  The consumer fixes the
  -- fuel at the slot count `n`, a VARIABLE, so `nestDⱽ n [] sl (input i)`
  -- never reduces, and the parent has no more fuel than the child it
  -- would recurse into — there is no inequality to prove even in
  -- principle, and no lemma repairs it.  `outWⱽ` gets away with the
  -- shape by threading `j` through its own consumers; a measure read off
  -- a `Sched` cannot.
  --
  -- So it is paid in `slotNest`, which already pays `sizeᵉ d` on the
  -- nose and whose `slotsNestBelow-step` is an equality at exactly the
  -- index the `input` clause needs — the charge and the payment stayed
  -- the same number when the nesting went onto both.  What that cost was
  -- `slots-nest-≤-size`, `storeNest-capped` and `depth-capped`, since an
  -- exponential quantity has no bound by a size: the whole
  -- caps-conditioned interface went, and `depth-compositional` reaches
  -- the root directly now (`nest-store≤capsH`, Caps-Bridge, whose header
  -- carries what the deleted module knew).  That was the right trade
  -- rather than a loss — the interface was refuted anyway, and it was
  -- refuted for reading a level it does not report.
  depth-all-bound : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (op : AllOp) (initSt : NodeState Γ) (b : Closed Γ (obs u))
    (κ : Path Γ u t) (bid : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    depthAll g op initSt b κ bid now sched st
      ≤ depthCapN (suc (sizeᵉ b) + suc (nestDᵉ (Sched.slots sched) b))
                  (maxInputᵉ b) κ sched st

  -- SUBSTITUTION UNDER THE GUARD, which is what `unfoldμ` is: it is
  -- `elimGExp (here refl) (μᵉ body) body`, and `elimGExp` reaches a
  -- `varᵉ` only by descending into a `deferᵉ` — because `μᵉ` puts its
  -- variable in the GUARDED context while `varᵉ` reads the unguarded
  -- one, so the only route from the binder to the variable is the
  -- `deferᵉ` that moves `Δᵍ ++ Δ` into `Δ`.  The guardedness is a
  -- property of the SYNTAX, not a discipline anyone maintains.
  --
  -- So the substituted term appears only in positions `depthE` returns
  -- 0 on without looking inside, and the statement is over an ARBITRARY
  -- `cl`: the induction genuinely does not care what was substituted,
  -- which is the content of the whole route.  The `deferᵉ` clause is
  -- `z≤n`; the rest is the structural recursion `depth-compositional`
  -- already does, on `body` rather than on its unfolding.
  --
  -- STATED OVER `sizeᵉ body`, NOT `sizeᵉ (μᵉ body)`, so the parent's
  -- `suc` is spent in the assembly below rather than smuggled into the
  -- leaf.  The obstacle its predecessor's header named — `unfoldμ body`
  -- is LARGER than `μᵉ body`, so the size IH fails — was a fact about
  -- the route through `sizeᵉ (unfoldμ body)`, never about the
  -- statement, and this leaf is the route that does not take it.
  -- PROBED 2026-08-21 (Probed.Depth-Mu): depth is INDEPENDENT OF GAS,
  -- which is the region the falsity candidate lived in — `unfoldμ`
  -- grows the term once per unfolding and no right-hand side here
  -- mentions gas, so an arc charged inside a `deferᵉ` would cross any
  -- fixed bound.  Measured at two gas values twenty apart: a one-layer
  -- guarded body gives 1 and 1, a two-layer body 2 and 2, with the
  -- store held at 0 by an all-`scripted` slot.  Depth tracks the BODY's
  -- own nesting and nothing else.
  -- THE ROWS PIN THE PARENT, so they instantiate this leaf at
  -- `cl = μᵉ body` and at nothing else — the generality in `cl` is the
  -- part of the route that carries the induction, and it is unprobed by
  -- construction, since only the parent's conclusion computes at a
  -- program.
  -- Shapes NOT covered: `mergeAllᵉ` guards only, so no map/take/scan
  -- frame above the guard; no nested `μᵉ`; no shared slot in the store,
  -- so the interaction with the connect chain is untested; and the
  -- guarded body uses its variable exactly once.
  --
  -- RESTATED over `depthCap` when the connect landed.  Re-read: the two
  -- bodies' caps are 6 and 10, and DEGENERATE on the slot half — this
  -- program has no shared slot, so the partial sum is 0 at every cut and
  -- these figures cannot tell the cap from the bound it replaced.  What
  -- they do is keep the crossing against the depth rows honest.
  depth-subst-guarded : ∀ {n} {Γ : Ctx n} {r u} {e : Closed Γ r}
    (fuel : Gas) (body : Exp Γ (u ∷ []) [] [] u) (cl : Closed Γ u)
    (κ : Path Γ u r) (bid : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    depthE fuel (elimGExp (here refl) cl body) κ bid now sched st
      ≤ depthCap body κ sched st

-- THE RECEIPT FOR THIS ARITHMETIC IS ON `depth-subst-guarded`, NOT
-- HERE, and the reason is a gap in E3's tense model worth naming: a
-- receipt is `-- PROBED` over a live postulate and
-- `-- PROBED-HISTORICAL` over a proven one, and this is NEITHER — a
-- real body over a leaf that is still open.  Marking it HISTORICAL
-- would assert the statement is settled, which is the lying comment E3
-- exists to prevent, arriving from the other side.  So the receipt
-- follows the statement that is still OPEN, downward to the leaf.
depth-μ-bound : ∀ {n} {Γ : Ctx n} {r u} {e : Closed Γ r}
  (fuel : Gas) (body : Exp Γ (u ∷ []) [] [] u) (κ : Path Γ u r)
  (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  depthE fuel (unfoldμ body) κ bid now sched st
    ≤ depthCap (μᵉ body) κ sched st
depth-μ-bound {n = n} fuel body κ bid now sched st =
  ≤-trans (depth-subst-guarded fuel body (μᵉ body) κ bid now sched st)
          (⊔-mono-≤ (+-mono-≤ (+-mono-≤ step ≤-refl) ≤-refl) ≤-refl)
  where
  -- `μᵉ` adds one to the SIZE and nothing to the nesting, so the whole
  -- first summand climbs by exactly the one `suc`
  step : sizeᵉ body + nestDᵉ (Sched.slots sched) body
           ≤ suc (sizeᵉ body) + nestDᵉ (Sched.slots sched) body
  step = n≤1+n (sizeᵉ body + nestDᵉ (Sched.slots sched) body)

------------------------------------------------------------------
-- BUCKET (b) — burst = 0 for non-thru-outer frames (provable by
-- structural induction on the stream; each frame clause in
-- Caps-Depth:361-363 returns 0 definitionally)
------------------------------------------------------------------

-- depthFrame returns 0 definitionally for map-f/scan-f/take-f (Caps-Depth:361-363),
-- so depthBurst over these frames is a fold of (0 ⊔ IH) — provable by list induction.
burst-mapf-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (fuel : Gas) (bid : Id) (now : Tick)
  (f : Fn Γ [] [] [] s u) (κ : Path Γ u t)
  (stream : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  depthBurst fuel bid now (map-f f) κ stream sched st ≤ 0
burst-mapf-zero fuel bid now f κ [] sched st = z≤n
burst-mapf-zero {Γ = Γ} {u = u} fuel bid now f κ (em ∷ ems) sched st =
  ⊔-lub z≤n (burst-mapf-zero fuel bid now f κ ems sched' st')
  where
  sp     = splitEvents {A = Val Γ u} (InstEmit.events em)
  r      = stepFrame fuel bid now (map-f f) κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  sched' = proj₁ (proj₂ (proj₂ (proj₂ r)))
  st'    = proj₂ (proj₂ (proj₂ (proj₂ r)))

burst-scf-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (fuel : Gas) (bid : Id) (now : Tick)
  (f : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId) (κ : Path Γ u t)
  (stream : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  depthBurst fuel bid now (scan-f f nid) κ stream sched st ≤ 0
burst-scf-zero fuel bid now f nid κ [] sched st = z≤n
burst-scf-zero {Γ = Γ} {u = u} fuel bid now f nid κ (em ∷ ems) sched st =
  ⊔-lub z≤n (burst-scf-zero fuel bid now f nid κ ems sched' st')
  where
  sp     = splitEvents {A = Val Γ u} (InstEmit.events em)
  r      = stepFrame fuel bid now (scan-f f nid) κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  sched' = proj₁ (proj₂ (proj₂ (proj₂ r)))
  st'    = proj₂ (proj₂ (proj₂ (proj₂ r)))

burst-takef-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (fuel : Gas) (bid : Id) (now : Tick)
  (nid : NodeId) (κ : Path Γ s t)
  (stream : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  depthBurst fuel bid now (take-f nid) κ stream sched st ≤ 0
burst-takef-zero fuel bid now nid κ [] sched st = z≤n
burst-takef-zero {Γ = Γ} {s = s} fuel bid now nid κ (em ∷ ems) sched st =
  ⊔-lub z≤n (burst-takef-zero fuel bid now nid κ ems sched' st')
  where
  sp     = splitEvents {A = Val Γ s} (InstEmit.events em)
  r      = stepFrame fuel bid now (take-f nid) κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  sched' = proj₁ (proj₂ (proj₂ (proj₂ r)))
  st'    = proj₂ (proj₂ (proj₂ (proj₂ r)))

-- setNode with take-st never increases nodesNestMax: nodeNestMax(take-st _) = 0.
private
  setNode-take-nodesNestMax : ∀ {n} {Γ : Ctx n}
    (nid : NodeId) (k : ℕ)
    (nodes : List (NodeId × NodeState Γ)) →
    nodesNestMax (setNode nid (take-st k) nodes) ≤ nodesNestMax nodes
  setNode-take-nodesNestMax nid k [] = z≤n
  setNode-take-nodesNestMax nid k ((j , ns) ∷ rest) with j ≡ᵇ nid
  ... | true  = ⊔-lub z≤n (m≤n⊔m _ _)
  ... | false = ⊔-lub (m≤m⊔n _ _)
                      (≤-trans (setNode-take-nodesNestMax nid k rest) (m≤n⊔m _ _))

  -- the same induction for a scan node, which is 0-weight for the same
  -- reason: `nodeNestMax` charges only what the family reads.
  setNode-scan-nodesNestMax : ∀ {n} {Γ : Ctx n} {u}
    (nid : NodeId) (v : Val Γ u)
    (nodes : List (NodeId × NodeState Γ)) →
    nodesNestMax (setNode nid (scan-st v) nodes) ≤ nodesNestMax nodes
  setNode-scan-nodesNestMax nid v [] = z≤n
  setNode-scan-nodesNestMax nid v ((j , ns) ∷ rest) with j ≡ᵇ nid
  ... | true  = ⊔-lub z≤n (m≤n⊔m _ _)
  ... | false = ⊔-lub (m≤m⊔n _ _)
                      (≤-trans (setNode-scan-nodesNestMax nid v rest)
                               (m≤n⊔m _ _))

-- After mintNode + installNode(take-st(suc k)), storeNestMax is
-- unchanged: nodeNestMax(take-st _) = 0, and mintNode preserves slots.
-- stated over the CAP rather than over `storeNestMax`, because that is
-- what the take clause's IH now returns.  Only the node half moves:
-- `mintNode` leaves the slots alone, so the whole left arm — the
-- below-sum included — is definitionally unchanged.
depthCap-installTake : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {e : Closed Γ t} {u}
  (b : Exp Γ Δᵍ Δ Θ u) (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e)
  (k : ℕ) →
  depthCap b κ (proj₂ (mintNode sched))
               (installNode (proj₁ (mintNode sched)) (take-st (suc k)) st)
    ≤ depthCap b κ sched st
depthCap-installTake b κ sched st k =
  ⊔-mono-≤ ≤-refl
    (setNode-take-nodesNestMax (Sched.nextNode sched) (suc k)
      (EvalSt.nodes st))

-- and the scan twin, which is now a twin: it was a postulate for as long
-- as the measure charged for the accumulator.
depthCap-installScan : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {e : Closed Γ t} {u s}
  (b : Exp Γ Δᵍ Δ Θ u) (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e)
  (v : Val Γ s) →
  depthCap b κ (proj₂ (mintNode sched))
               (installNode (proj₁ (mintNode sched)) (scan-st v) st)
    ≤ depthCap b κ sched st
depthCap-installScan b κ sched st v =
  ⊔-mono-≤ ≤-refl
    (setNode-scan-nodesNestMax (Sched.nextNode sched) v (EvalSt.nodes st))

------------------------------------------------------------------
-- ARITHMETIC HELPERS — proved here.
------------------------------------------------------------------

-- Core step: a + suc p ≤ suc (c + a) + p.
-- Used by map-size-arith and take-size-arith.
private
  arith-step : ∀ (a p c : ℕ) → a + suc p ≤ suc (c + a) + p
  arith-step a p c =
    ≤-trans (≤-reflexive (+-suc a p))
            (s≤s (+-mono-≤ (m≤n+m a c) ≤-refl))

  -- the two summands of the enlarged cap travel together, so every
  -- `*-size-arith` needs the middle pair swapped: the SIZE the operator
  -- adds sits beside the size below it, and the NESTING it adds beside
  -- the nesting below it, while `arith-step` delivers them grouped the
  -- other way
  arith-step₂ : ∀ (S N p C D : ℕ) → (S + N) + suc p ≤ (suc (C + S) + (D + N)) + p
  arith-step₂ S N p C D =
    ≤-trans (arith-step (S + N) p (C + D))
            (≤-reflexive (cong (_+ p) (cong suc (+-mix4 C D S N))))

-- sizeᵉ b + 1 ≤ 1 + sizeᵗ f + sizeᵉ b = sizeᵉ (mapᵉ f b)
map-size-arith : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (f : Fn Γ [] [] [] s u) (b : Closed Γ s)
  (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) →
  depthCap b (map-f f ↠ κ) sched st ≤ depthCap (mapᵉ f b) κ sched st
map-size-arith {n = n} f b κ sched st =
  ⊔-mono-≤ (+-mono-≤ (arith-step₂ (sizeᵉ b) (nestDᵉ (Sched.slots sched) b)
                        (pathLen κ) (sizeᵗ f) (nestDᵗ (Sched.slots sched) f))
                     (slotsNestBelow-mono (Sched.slots sched)
                        (maxInputᵉ b) (maxInputᵉ (mapᵉ f b)) (m≤n⊔m _ _)))
           ≤-refl

-- same shape as map-size-arith
take-size-arith : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Tm Γ [] [] [] natᵗ) (b : Closed Γ u) (nid : NodeId)
  (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) →
  depthCap b (take-f nid ↠ κ) sched st ≤ depthCap (takeᵉ c b) κ sched st
take-size-arith {n = n} c b nid κ sched st =
  ⊔-mono-≤ (+-mono-≤ (arith-step₂ (sizeᵉ b) (nestDᵉ (Sched.slots sched) b)
                        (pathLen κ) (sizeᵗ c) 0)
                     (slotsNestBelow-mono (Sched.slots sched)
                        (maxInputᵉ b) (maxInputᵉ (takeᵉ c b)) (m≤n⊔m _ _)))
           ≤-refl

-- scan: same shape as map-size-arith, because the install is absorbed
-- BEFORE this arithmetic runs — `depthCap-installScan` returns the IH's
-- post-install cap to the entry cap, so what is left here is the syntax
-- payment alone.
scan-size-arith : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u) (b : Closed Γ s)
  (nid : NodeId) (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) →
  depthCap b (scan-f f nid ↠ κ) sched st
    ≤ depthCap (scanᵉ f seed b) κ sched st
scan-size-arith {n = n} f seed b nid κ sched st =
  ⊔-mono-≤ (+-mono-≤ (arith-step₂ (sizeᵉ b) (nestDᵉ (Sched.slots sched) b)
                        (pathLen κ) (sizeᵗ f + sizeᵗ seed) _)
                     (slotsNestBelow-mono (Sched.slots sched)
                        (maxInputᵉ b) (maxInputᵉ (scanᵉ f seed b))
                        (m≤n⊔m _ _)))
           ≤-refl

------------------------------------------------------------------
-- THE ASSEMBLY — structurally recursive on `b`; dispatch order follows
-- the clause list in Caps-Depth.agda:214-251.
------------------------------------------------------------------

-- The assembly is built PRIVATE and exported through an ABSTRACT
-- alias, for the caps axis's normalization contract (measured
-- 2026-08-07: an unfoldable body on the budget-sufficient spine
-- OOM'd VWF's recheck twice; the morning-green build had a postulate
-- — i.e. exactly this opacity — in this spot).  The alias pattern
-- rather than a plain abstract block because these clauses lean on
-- untyped where-bindings and a with-abstraction, which abstract
-- refuses to infer.
private
  depth-compositional-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (bid : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    depthE g b κ bid now sched st ≤ depthCap b κ sched st

  -- BUCKET (a): returns 0
  depth-compositional-go g (ofᵉ _)    κ bid now sched st = z≤n
  depth-compositional-go g emptyᵉ     κ bid now sched st = z≤n
  depth-compositional-go g (deferᵉ _) κ bid now sched st = z≤n
  depth-compositional-go g0 (μᵉ _)    κ bid now sched st = z≤n
  depth-compositional-go g (varᵉ ())  κ bid now sched st

  -- BUCKET (d): μ with gas — dispatched to depth-μ-bound
  depth-compositional-go (gs fuel) (μᵉ body) κ bid now sched st =
    depth-μ-bound fuel body κ bid now sched st

  -- THE CONNECT, and no longer a postulate.  The slot is read HERE
  -- rather than inside a leaf, which is what the partial sum buys: the
  -- def `d` comes out of the constructor so it cannot be instantiated
  -- against a store that does not hold it (Refuted.Depth-Conn), and
  -- `shared`'s own `ok` field says every input `d` mentions is below
  -- `toℕ i` — so the def's whole below-sum sits under the cut at `i`
  -- and `slotsNestBelow-step` covers it plus `sizeᵉ d` with the one
  -- summand admitting slot `i` buys.  GAS is what decreases, which is
  -- why the recursion needs no measure of its own.
  depth-compositional-go g0 (input i) κ bid now sched st
    with Sched.slots sched i
  ... | scripted _ = z≤n
  ... | shared d   = z≤n
  depth-compositional-go (gs fuel′) (input i) κ bid now sched st
    with Sched.slots sched i in slotEq
  ... | scripted _ = z≤n
  ... | shared d {ok = ok} =
    ≤-trans
      (depth-compositional-go fuel′ d (share-sink i) bid now sched
        (register (toℕ i) κ
          (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })))
      (⊔-mono-≤ (≤-trans slotPay (m≤n+m _ _)) ≤-refl)
    where
    sl = Sched.slots sched
    -- the def's own cut, widened to `toℕ i` by stratification
    below : slotsNestBelow sl (maxInputᵉ d) ≤ slotsNestBelow sl (toℕ i)
    below = slotsNestBelow-mono sl (maxInputᵉ d) (toℕ i)
              (inputsBelow⇒maxᵉ (toℕ i) d ok)
    -- slot `i`'s summand, which IS `sizeᵉ d + nestDᵉ sl d` — the child's
    -- whole charge, size and nesting together, on the nose
    step : sizeᵉ d + nestDᵉ sl d + slotsNestBelow sl (toℕ i)
             ≤ slotsNestBelow sl (suc (toℕ i))
    step = subst (λ s → slotNest sl s + slotsNestBelow sl (toℕ i)
                          ≤ slotsNestBelow sl (suc (toℕ i)))
                 slotEq (slotsNestBelow-step sl i)
    -- `pathLen (share-sink i)` is 0 definitionally: the connect resets
    -- the path, which is why the goal's own `κ` is free room here.
    slotPay : sizeᵉ d + nestDᵉ sl d + 0 + slotsNestBelow sl (maxInputᵉ d)
                ≤ slotsNestBelow sl (suc (toℕ i))
    slotPay = ≤-trans
                (+-mono-≤ (≤-reflexive (+-identityʳ (sizeᵉ d + nestDᵉ sl d)))
                          below)
                step

  -- BUCKET (b): mapᵉ — burst(map-f) = 0 by frame clause; IH on b
  depth-compositional-go fuel (mapᵉ f b) κ bid now sched st =
    ≤-trans
      (⊔-lub
        (depth-compositional-go fuel b (map-f f ↠ κ) bid now sched st)
        (≤-trans (burst-mapf-zero fuel bid now f κ
                    (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
                 z≤n))
      (map-size-arith f b κ sched st)
    where r = subscribeE fuel b (map-f f ↠ κ) bid now sched st

  -- BUCKET (a)/(b): takeᵉ — zero arm trivial; suc arm uses take-f burst = 0
  depth-compositional-go fuel (takeᵉ c b) κ bid now sched st
    with evalTm c
  ... | zero  = z≤n
  ... | suc k =
    ≤-trans
      (⊔-lub
        (≤-trans
          (depth-compositional-go fuel b (take-f nid ↠ κ) bid now sched₁ st₀)
          (depthCap-installTake b (take-f nid ↠ κ) sched st k))
        (≤-trans (burst-takef-zero fuel bid now nid κ
                    (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
                 z≤n))
      (take-size-arith c b nid κ sched st)
    where
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₀    = installNode nid (take-st (suc k)) st
    r      = subscribeE fuel b (take-f nid ↠ κ) bid now sched₁ st₀

  -- BUCKET (b): scanᵉ — burst(scan-f) = 0, and the IH comes back through
  -- the ENTRY store because installing the seed is 0-weight: nothing in
  -- the depth family reads a scan node, so `nodeNestMax` does not charge
  -- for it and this clause is the take clause with a different node.
  depth-compositional-go fuel (scanᵉ f seed b) κ bid now sched st =
    ≤-trans
      (⊔-lub
        (≤-trans
          (depth-compositional-go fuel b (scan-f f nid ↠ κ) bid now sched₁ st₀)
          (depthCap-installScan b (scan-f f nid ↠ κ) sched st (evalTm seed)))
        (≤-trans (burst-scf-zero fuel bid now f nid κ
                    (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
                 z≤n))
      (scan-size-arith f seed b nid κ sched st)
    where
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₀    = installNode nid (scan-st (evalTm seed)) st
    r      = subscribeE fuel b (scan-f f nid ↠ κ) bid now sched₁ st₀

  -- BUCKET (d): *All — all four delegate to depth-all-bound;
  -- suc (sizeᵉ b) IS sizeᵉ (*Allᵉ b) definitionally
  depth-compositional-go fuel (mergeAllᵉ b) κ bid now sched st =
    depth-all-bound fuel mergeᵒ (merge-st 0 false) b κ bid now sched st

  depth-compositional-go {u = u} fuel (concatAllᵉ b) κ bid now sched st =
    depth-all-bound fuel concatᵒ (concat-st {t = u} [] false false) b κ bid now sched st

  depth-compositional-go fuel (switchAllᵉ b) κ bid now sched st =
    depth-all-bound fuel switchᵒ (switch-st nothing false) b κ bid now sched st

  depth-compositional-go fuel (exhaustAllᵉ b) κ bid now sched st =
    depth-all-bound fuel exhaustᵒ (exhaust-st false false) b κ bid now sched st


-- ITS PREDECESSOR IS REFUTED 2026-08-21 (Refuted.Depth-Nest,
-- `depth-compositional-sum-absurd`), AND THE RESTATEMENT HAS LANDED —
-- read the two right-hand sides side by side before believing either.
-- What died was `sizeᵉ b + pathLen κ + storeNestMax`, with no nesting
-- term: a `scanᵉ` that wraps its own accumulator makes `depthE` grow in
-- `wraps × ticks` while `sizeᵉ b` grows in `wraps + ticks`, measured 49
-- against 38.  The statement below carries `nestDᵉ`, which IS the
-- quantity that witness was measuring, so the witness cannot reach it —
-- the currency changed, exactly as the leaf's header said it had to, and
-- the induction did not.
--
-- THE REFUTATION IS KEPT FOR THE ROUTE, NOT FOR THIS STATEMENT.  It is
-- what forbids ever dropping the nesting term again to make an arm close,
-- and a sum whose margin grows down a connect chain is not something a
-- reader recovers from the statement alone.
abstract
  depth-compositional : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (bid : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    depthE g b κ bid now sched st
      ≤ sizeᵉ b + nestDᵉ (Sched.slots sched) b + pathLen κ
          + storeNestMax sched st
  depth-compositional g b κ bid now sched st =
    ≤-trans (depth-compositional-go g b κ bid now sched st)
            (cap-≤-store b κ sched st)