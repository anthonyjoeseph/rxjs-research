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
--     `nestDᵉ (mergeAllᵉ b) ≡ suc (nestDᵉ b)` — the cap's path measure
--     charges that frame and no other, and the constructor grants
--     exactly the one unit it charges.
-- (4) THE REAL WORK: every clause that calls `depthBurst` feeds it the
--     state produced by running the REAL `subscribeE`, while the RHS
--     reads the ENTRY state.  The `storeNestMax`-preservation conjunct
--     is what `depth-all-burst-gs` (below) absorbs; when it is ground it
--     must be proved as a second conjunct of the same induction, not a
--     separate family, and must NOT ride `subscribeE-caps` (circular —
--     that face takes `depthE ≤ dep` as a hypothesis).  Its sibling arm
--     needed the same induction for a different reason and is proven
--     inside it; see that leaf's header.
--
-- BUCKETS: (a) trivially zero — ofᵉ, emptyᵉ, deferᵉ, g0(μᵉ),
-- takeᵉ(zero), and the g0 connect.  (b) IH + arithmetic — mapᵉ,
-- takeᵉ(suc), scanᵉ, over the burst-zero and installNode lemmas below.
-- (c) THE CONNECT, a real clause: `input` recurses into the slot's own
-- def and pays for it out of the summand admitting slot `i` to the
-- partial sum.  (d) BLOCKED, two named postulates —
-- `depth-all-burst-gs` (needs the preservation conjunct, finding (4);
-- it is the burst half of the `*All` clauses at POSITIVE gas — the
-- outer half is proven in the assembly itself and the zero-gas half in
-- bucket (b′)) and
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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.Nat.ListAction using (sum)
open import Data.Bool  using (Bool; false; true; if_then_else_; T; _∧_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Rx.Prim using (Gas; g0; gs; Id; Tick; InstEmit)
open import Rx.Exp
  using (natᵗ; _×ᵗ_; Ctx; Closed; Exp; Tm; Fn; Val; obs; evalTm; unfoldμ; elimGExp; sizeᵉ; input; ofᵉ;
  emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
  varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
  inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ)
open import Rx.Evaluator
  using (Sched; EvalSt; NodeState; AllOp; NodeId; Path; Stream; scan-st; merge-st; concat-st;
  switch-st; exhaust-st; take-st; mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ; _↠_; map-f; scan-f;
  take-f; from-inner; thru-outer; mintNode; installNode; subscribeE; splitEvents; stepFrame;
  setNode; root; share-sink; register; lookupNode; thruConsume)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵗ)
open import Rx.Slots using (scripted; shared; Slot; Slots)

-- pathLen, imported from .Measures where it is defined — the
-- SAME pathLen `depth-capped`'s statement reads, so the landing plugs
-- into its consumer unchanged.
open import Verify-Budget-Sufficient.Measures using
  (pathLen; sum-tab-mono)
open import Verify-Budget-Sufficient.Caps-Nest using (sum-tab-slack)
open import Data.Empty using (⊥-elim)
open import Decide using (force-false; T-to; ≤ᵇ-true; ≤ᵇ-widen; ∧ˡ; ∧ʳ)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthE; depthBurst; depthWalk; depthConsume; depthConsumeS)

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
-- AND IT CHARGES THE QUEUE IN THE NESTING CURRENCY, WHICH IS WHY IT
-- TAKES THE SLOTS.  It read `sizeᵉ o` once, and that was the same
-- mismatch the cap's own size term was: the burst arm has to bound the
-- IH's cap at the state the walk REACHED, and a `concatAllᵉ` that
-- queues an emitted inner puts that inner into this measure — so a
-- size here demands the cap bound an emitted inner's SIZE, which is
-- exactly what an accumulator-wrapping scan refutes.  In this currency
-- the same leaf covers it: an emitted inner's nesting is bounded by its
-- emitter's, and the emitter's is what the `*All` layer's cap already
-- names.
nodeNestMax : ∀ {n} {Γ : Ctx n} → Slots Γ → NodeState Γ → ℕ
nodeNestMax sl (scan-st _)           = 0
nodeNestMax sl (concat-st {t} q _ _) = foldr (λ o acc → nestDᵉ sl o ⊔ acc) 0 q
nodeNestMax sl (take-st _)           = 0
nodeNestMax sl (merge-st _ _)        = 0
nodeNestMax sl (switch-st _ _)       = 0
nodeNestMax sl (exhaust-st _ _)      = 0

nodesNestMax : ∀ {n} {Γ : Ctx n} → Slots Γ →
  List (NodeId × NodeState Γ) → ℕ
nodesNestMax sl = foldr (λ kv acc → nodeNestMax sl (proj₂ kv) ⊔ acc) 0

-- A SHARED SLOT PAYS ITS DEF'S NESTING TOO, and that is where the
-- refutation's product had to land.  A def reached through `input` is
-- entered by the mirror with the def in hand, so its own scan/`*All`
-- structure deepens exactly as the root program's does; charging only
-- `sizeᵉ d` was the same undercount the `*All` face's PREDECESSOR was
-- refuted for — the form with no nesting term, which is what
-- `Refuted.Depth-Nest`'s witness types state.
--
-- Charging it HERE rather than descending inside `nestDᵉ` is forced:
-- see that module's header — a descending `input` clause is stuck on a
-- variable fuel.  What it costs is `slotNest-≤-slotSize` and the chain
-- above it, which fed the caps-conditioned interface this refutation
-- retires anyway.
-- ONE SUMMAND, NOT TWO.  It paid `sizeᵉ d + nestDᵉ sl d` while the cap
-- read both currencies; with the cap read off nesting alone the size
-- half was pure over-payment, and dropping it makes the connect's
-- charge and its payment the SAME NUMBER again — `slotsNestBelow-step`
-- is an equality at exactly the index the `input` clause needs, which
-- is the property the whole partial-sum design rests on.
slotNest : ∀ {n} {Γ : Ctx n} {k t} → Slots Γ → Slot Γ k t → ℕ
slotNest sl (shared d)   = nestDᵉ sl d
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
-- pays for the whole chain.  Nothing bounds it by a SIZE any more, and
-- nothing needs to: the caps-conditioned interface that wanted a
-- pointwise `slotNest ≤ slotSize` was refuted for reading a level it
-- does not report, and `nest-store≤capsH` (Caps-Bridge) reaches the
-- root through the tower instead, where a sum is what `tower-sum-tab`
-- is stated over.
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
  slotsNestSum (Sched.slots sched)
    ⊔ nodesNestMax (Sched.slots sched) (EvalSt.nodes st)

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
-- goes through, and the `⊔-lub` split every consumer of this measure
-- takes survives — which a `+` would NOT, since that needs the SUM of
-- two quantities the tower bounds only separately.

-- THE PATH MEASURE THE CAP READS, AND IT IS NOT `pathLen`.  A frame in
-- the path is charged on DELIVERY by `depthFold`, but only a
-- `thru-outer` frame charges a `suc` on the SUBSCRIBE side, which is
-- the side this face is about — `depthFrame` returns 0 on map-f,
-- scan-f and take-f definitionally.  Counting all frames therefore
-- makes the cap pay for descent steps that cost nothing, and something
-- has to fund that: it was `sizeᵉ`, which is why the cap carried a size
-- term at all.  Charging the spending arc alone is what lets the size
-- term go, and the `*All` clause pays its one unit out of
-- `nestDᵉ (mergeAllᵉ b) ≡ suc (nestDᵉ b)` — the same `suc`, in the
-- currency the depth is actually generated in.
--
-- `from-inner` charges NOTHING here, and it is the one clause worth
-- justifying: the arc it funds (`depthFinC`'s completion `suc`) is
-- reached only through `depthFold`, and its contents are the queued
-- observables the node half already charges.  A unit here would double
-- charge the layer the `thru-outer` above it already bought.
pathNestD : ∀ {n} {Γ : Ctx n} {s t} → Path Γ s t → ℕ
pathNestD root                    = 0
pathNestD (share-sink i)          = 0
pathNestD (map-f _ ↠ p)           = pathNestD p
pathNestD (scan-f _ _ ↠ p)        = pathNestD p
pathNestD (take-f _ ↠ p)          = pathNestD p
pathNestD (from-inner _ _ _ ↠ p)  = pathNestD p
pathNestD (thru-outer _ _ ↠ p)    = suc (pathNestD p)

-- what the exported statement is still stated over, so the tightening
-- is invisible outside this module
pathNestD≤pathLen : ∀ {n} {Γ : Ctx n} {s t} (κ : Path Γ s t) →
  pathNestD κ ≤ pathLen κ
pathNestD≤pathLen root                   = z≤n
pathNestD≤pathLen (share-sink i)         = z≤n
pathNestD≤pathLen (map-f _ ↠ p)          = ≤-trans (pathNestD≤pathLen p) (n≤1+n _)
pathNestD≤pathLen (scan-f _ _ ↠ p)       = ≤-trans (pathNestD≤pathLen p) (n≤1+n _)
pathNestD≤pathLen (take-f _ ↠ p)         = ≤-trans (pathNestD≤pathLen p) (n≤1+n _)
pathNestD≤pathLen (from-inner _ _ _ ↠ p) = ≤-trans (pathNestD≤pathLen p) (n≤1+n _)
pathNestD≤pathLen (thru-outer _ _ ↠ p)   = s≤s (pathNestD≤pathLen p)

depthCapN : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sz mx : ℕ) (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) → ℕ
depthCapN sz mx κ sched st =
  (sz + pathNestD κ + slotsNestBelow (Sched.slots sched) mx)
    ⊔ nodesNestMax (Sched.slots sched) (EvalSt.nodes st)

-- NO SIZE TERM.  The depth this face bounds is generated by the
-- spending arc and by nothing else, so `nestDᵉ` is the currency
-- throughout and `sizeᵉ` was slack — measured slack: at the two μ
-- probe programs the old cap read 7 and 12 where the depth is 1 and 2,
-- and `nestDᵉ` reads 1 and 2 on the nose.  Dropping it is what makes
-- the `*All` burst arm statable: an emitted inner can be arbitrarily
-- LARGER than the source that emitted it (a scan whose step re-wraps
-- its accumulator), but it cannot be more deeply NESTED than the
-- source's own nesting measure, because that measure's product term
-- charges one re-wrap per delivered payload precisely to cover this.
depthCap : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {e : Closed Γ t} {u}
  (b : Exp Γ Δᵍ Δ Θ u) (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) → ℕ
depthCap {n = n} b κ sched st =
  depthCapN (nestDᵉ (Sched.slots sched) b) (maxInputᵉ b) κ sched st

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
  -- three widenings, one per summand: the cap's own currency into the
  -- exported sum, the spending-arc count into the frame count, and the
  -- below-sum into the whole sum
  slotHalf : nestDᵉ (Sched.slots sched) b + pathNestD κ
               + slotsNestBelow (Sched.slots sched) (maxInputᵉ b)
               ≤ SZ + pathLen κ + storeNestMax sched st
  slotHalf = +-mono-≤
               (+-mono-≤ (m≤n+m (nestDᵉ (Sched.slots sched) b) (sizeᵉ b))
                         (pathNestD≤pathLen κ))
               (≤-trans (slotsNestBelow-≤-sum (Sched.slots sched) (maxInputᵉ b))
                        (m≤m⊔n _ _))
  nodes≤store : nodesNestMax (Sched.slots sched) (EvalSt.nodes st)
                  ≤ storeNestMax sched st
  nodes≤store = m≤n⊔m _ _
  store≤goal : storeNestMax sched st
                 ≤ SZ + pathLen κ + storeNestMax sched st
  store≤goal = m≤n+m (storeNestMax sched st) (SZ + pathLen κ)
  nodeHalf : nodesNestMax (Sched.slots sched) (EvalSt.nodes st)
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
  -- with the store held at 9 in both rows by using the same slots.
  -- So the arc that accumulates is the CONNECT — which is what forced
  -- `slotsNestSum` (Refuted.Depth-Chain) — and NOT the sibling entry,
  -- so this arm's own `suc` is not being asked to pay for k chains.
  -- RE-READ 2026-08-22 in the nesting currency: the figures were 5
  -- against a store of 60 and a cap of 53 when the slot measure paid
  -- sizes, and are 5 against 9 and 9 now, so the margin the rows cross
  -- is of the same order as the depth rather than mostly size slack.  This
  -- was the live falsity candidate once the chain finding landed, and
  -- it is the region the rows reached.
  -- Shapes NOT covered: `mergeAllᵉ` only, so no concat/switch/exhaust
  -- burst (different `initSt`, and their queueing is what
  -- `nodesNestMax` charges); no nested burst; no post-cascade state;
  -- and both arms are the same length, so a burst over siblings of
  -- DIFFERENT depths is untested.
  --
  -- RESTATED over `depthCapN` when the connect landed and again when the
  -- cap lost its size term, and the rows were re-read rather than
  -- inherited both times: the two-chain program measures 5 against a cap
  -- of 53, where the `storeNestMax` bound it replaced gave 60.  The
  -- mirror-side findings above are untouched, since nothing about
  -- `depthAll` moved — only the right-hand side, and it got SMALLER each
  -- time, which is the direction that could have refuted this.  Almost
  -- all of what is left is the slot chain: this program's own
  -- contribution to its cap is ONE, its `mergeAllᵉ` layer.
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
  -- ANSWER WAS WRONG.  Putting `nestDᵉ b` into `depthCap`'s first
  -- summand — beside `sizeᵉ b` then, alone there now — leaves the
  -- `input` clause owing the SLOT definition's nesting, and there were
  -- exactly two places to pay it.
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
  -- So it is paid in `slotNest`, whose `slotsNestBelow-step` is an
  -- equality at exactly the index the `input` clause needs.  It paid the
  -- def's SIZE beside its nesting while the cap read both currencies,
  -- and pays the nesting ALONE now, so the charge and the payment are
  -- again the same number.  What either version cost was
  -- `slots-nest-≤-size`, `storeNest-capped` and `depth-capped`, since an
  -- exponential quantity has no bound by a size: the whole
  -- caps-conditioned interface went, and `depth-compositional` reaches
  -- the root directly now (`nest-store≤capsH`, Caps-Bridge, whose header
  -- carries what the deleted module knew).  That was the right trade
  -- rather than a loss — the interface was refuted anyway, and it was
  -- refuted for reading a level it does not report.
  -- THE FACE SPLIT INTO ITS TWO ARMS, AND ONLY THE BURST ONE IS A LEAF.
  -- `depthAll` reduces to `depthE … ⊔ depthBurst …` — Caps-Depth is
  -- deliberately not `abstract`, so both arms are visible from here —
  -- so the four `*All` clauses of the assembly below close with `⊔-lub`
  -- over an OUTER half they prove and this BURST half they assume.
  --
  -- DEAD ROUTE 2026-08-22: STATE THE OUTER ARM AS A LEAF OF ITS OWN.
  -- It was written that way first, alongside this one, and it is
  -- STRUCTURALLY DEAD — not hard, impossible.  The arm's only route is
  -- the take/scan buckets' route step for step: the assembly's own
  -- recursion at the SUB-expression, then the install lemma, then the
  -- `*All` layer's cap arithmetic.  That first step is the induction
  -- hypothesis, and it is available only INSIDE the induction: a
  -- standalone lemma would have to call the assembly at an expression
  -- of the same size as its own argument, so nothing decreases and no
  -- measure repairs it.  The decrease happens at the CALLER, which is
  -- exactly where the proof now lives.
  --
  -- AND THE `initSt` GENERALITY WAS A SYMPTOM OF THE SAME THING, worth
  -- recording because it read as the blocker.  Stated standalone, the
  -- arm quantifies over a free initial node state, the install lemma
  -- needs that state to weigh 0, and the unconditional form is NOT
  -- refuted — `depthE` never reads `nodesNestMax`, only the cap does,
  -- and installing can only raise it — so a hypothesis was not
  -- licensed and the arm looked stuck.  Inline in the clause the
  -- question does not arise: the state is the literal one the evaluator
  -- installs, and its weight is `refl`.  An over-general argument in a
  -- statement is worth suspecting of being a statement that belongs
  -- somewhere else.
  --
  -- WHAT IS LEFT HERE IS THE ARM THAT CANNOT BE INLINED, and finding
  -- (4) above says why: its scheduler and state come out of the REAL
  -- `subscribeE`, while the cap reads the entry state, so it owes a
  -- preservation argument no arithmetic supplies.  The three
  -- projections below are that subscribe's stream, scheduler and state,
  -- in that order.
  --
  -- DEAD ROUTE 2026-08-22: RUN THE ASSEMBLY'S OWN INDUCTION AT THE
  -- EMITTED INNER AND DOMINATE ITS CAP.  It is the obvious route and
  -- the arms line up: the burst reaches `depthE` at each delivered
  -- inner observable one gas lower, and the `*All` layer's two `suc`s
  -- pay exactly the frame's charge and the extra path frame, leaving
  -- the inner's own size-plus-nesting to be covered by the source's.
  -- It is STRUCTURALLY DEAD IN THE SIZE TERM.  Take a scan whose step
  -- re-wraps its own accumulator inside one more `*All` layer per tick:
  -- the accumulator's NESTING grows by one per delivered payload and
  -- the measure pays for precisely that, since the scan clause's
  -- `outWᵉ · nestDᵗ` IS the per-payload re-wrap — but its SIZE grows by
  -- a constant per payload too, and the target's size term is fixed
  -- syntax.  So the child's cap outruns the parent's by the size term
  -- alone, at a program where the depths are fine.
  --
  -- WHICH IS TO SAY THE BLOCKAGE IS SLACK, NOT FALSITY.  At that same
  -- program the depth IS the nesting, so nothing here is refuted and no
  -- hypothesis is licensed; what is wrong is that `depthCap` reads the
  -- size currency at all.  `Probed.Nest-Depth` says so in the strongest
  -- available form: its rows report `depthE` EQUAL to `nestDᵉ`, not
  -- dominated by it, so the `sizeᵉ` summand buys nothing at any row
  -- reached.  Those rows are all at the root with no slot and no node
  -- store, so they do NOT reach the two places the size currency is
  -- load-bearing — the connect, which pays a def's `sizeᵉ` through
  -- `slotNest`, and `nodeNestMax`, which charges a concat queue by its
  -- observables' `sizeᵉ`.  Both of those keep paying under any repair;
  -- the summand in question is the one read off the SUBJECT.
  --
  -- AND THE `pathLen` SUMMAND IS NOT SLACK, WHICH IS THE PART THE ROWS
  -- CANNOT SEE, since `pathLen root` is 0 in every one of them.
  -- Spending arc 2 charges a `suc` for a `from-inner` frame that came
  -- out of the PATH rather than out of the subject, so a cap with no
  -- path term cannot pay for it — dropping the summand is not the
  -- repair, restating it in the nesting currency is.
  --
  -- THAT REPAIR IS DONE, AND IT IS WHY THIS STATEMENT READS AS IT NOW
  -- DOES.  The cap is read off nesting throughout: the subject's
  -- `sizeᵉ` is gone, the below-sum is kept, and `pathLen` became
  -- `pathNestD`, which charges the SPENDING ARC and nothing else.  The
  -- dead route above is what forced it and it stays recorded, because
  -- what was dead was the route THROUGH THE OLD STATEMENT and the
  -- repair was to move the statement — the route it kills is still
  -- dead for anyone who puts a size term back.
  --
  -- WHAT IT COST, and the answer is nothing: every clause of the
  -- assembly got SHORTER.  The three structural descents need no
  -- arithmetic step at all now, since the measure they used to have to
  -- fund is not charged; the `*All` arm's step is `arith-step` at
  -- `c = 0`, an equality in all but association; the μ clause's two
  -- caps became the SAME TERM, so its bridge went entirely; and the
  -- connect's charge and its payment are the same number again.  A
  -- tightening that simplifies every consumer is evidence about the
  -- measure, not about the arithmetic.
  --
  -- AND THE STORE MEASURE HAD TO FOLLOW IT, which the tightening left
  -- owed and THIS ARM is what collects.  The burst has to bound the
  -- IH's cap at the state the walk REACHED, and a `concatAllᵉ` queues
  -- an emitted inner into `nodeNestMax`; while that charged a SIZE the
  -- arm needed the cap to bound an emitted inner's size, which is
  -- exactly what an accumulator-wrapping scan refutes — the same
  -- mismatch one level down, and no cleverer proof reaches it.  Both
  -- halves of the store read `nestDᵉ` now (`nodeNestMax` taking the
  -- `Slots` that costs it), so the ONE leaf below covers the queued
  -- inner and the emitted one together.
  --
  -- SO WHAT IS LEFT ON THIS LEAF IS EXACTLY "an emitted inner's nesting
  -- is bounded by its emitter's nesting", which is the one thing the
  -- measure was derived to pay and which the scan clause pays on the
  -- nose — plus finding (4)'s state-preservation conjunct, which no
  -- restatement removes.  The `*All` layer's `suc` on `nestDᵉ` pays the
  -- frame's charge and `pathNestD` no longer bills the extra path frame
  -- at all, so the arithmetic is finished before the induction starts.
  --
  -- AND THE MEASURE THE ROUTE NEEDS IS ALREADY IN THE SIGNATURE: THE
  -- GAS.  An emitted inner is not a subexpression of its emitter, so
  -- structural recursion on the subject cannot reach it — but the
  -- descent that reaches it PEELS ONE GAS (`depthInner`'s `gs` clause
  -- is what enters the payload, and its zero clause returns 0), and the
  -- gas travels unchanged from `depthAll` down through the burst, the
  -- frame, the walk and the consume to get there.  So the pair is
  -- lexicographic on gas and then on the subject, which is the order
  -- the arguments already sit in, and no fuel parameter and no
  -- well-founded plumbing is owed.  THE SPLIT IS TAKEN: `depth-all-burst`
  -- is a real body over `g0` and `gs fuel`, and the zero half is
  -- discharged in bucket (b′) — which also checks the claim of this
  -- paragraph, since the base case of a gas descent closing is what
  -- says the gas is the thing being descended on.
  --
  -- WHICH MEANS THIS ARM CANNOT STAY A LEAF EITHER, for the reason its
  -- sibling could not: the recursion it needs exists only inside the
  -- induction.  Its route is to mirror the burst-side clique — burst,
  -- frame, walk, consume, inner, and concat's drain — as members of
  -- that induction, each recursing on its own list at a fixed gas and
  -- reaching the subject only one gas lower.  Every cycle in that call
  -- graph then decreases something: the lists on their own edges, the
  -- gas on the edge back to the subject.  What is left over as a true
  -- leaf is the one fact none of it supplies — an emitted inner's
  -- nesting is bounded by its emitter's — together with finding (4)'s
  -- state conjunct.
  -- THE BURST ARM AT POSITIVE GAS, over the stream the outer subscribe
  -- returned.  Its own scheduler and state come out of that subscribe
  -- rather than out of `sched`/`st`, which is why the arm cannot be
  -- stated over arbitrary ones: the three projections are the
  -- subscribe's stream, scheduler and state, in that order.
  --
  -- AND THE GAS SPLIT IS DONE, which is the half of the route above
  -- that needed no new mathematics.  `depth-all-burst` below is a real
  -- body: at `g0` every entry into a payload returns 0 without looking
  -- at it, so the whole burst-side clique collapses to the ONE `suc` a
  -- `thru-outer` frame charges and the cap's `suc` pays it.  What is
  -- left is this leaf, and its gas is the thing the route descends on.
  depth-all-burst-gs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : Gas) (op : AllOp) (initSt : NodeState Γ) (b : Closed Γ (obs u))
    (κ : Path Γ u t) (bid : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    let g   = gs fuel
        nid = proj₁ (mintNode sched)
        r   = subscribeE g b (thru-outer op nid ↠ κ) bid now
                (proj₂ (mintNode sched)) (installNode nid initSt st)
    in depthBurst g bid now (thru-outer op nid) κ
         (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
         ≤ depthCapN (suc (nestDᵉ (Sched.slots sched) b))
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
  -- STATED OVER `body`, NOT OVER `μᵉ body`, so the parent's own step is
  -- spent in the assembly below rather than smuggled into the leaf —
  -- and since the cap lost its size term that step is now the identity,
  -- `μᵉ` moving neither the nesting nor the input cut.  The obstacle its
  -- predecessor's header named — `unfoldμ body` is LARGER than
  -- `μᵉ body`, so the size IH fails — was a fact about the route
  -- through `sizeᵉ (unfoldμ body)`, never about the statement, and this
  -- leaf is the route that does not take it.  There is no size on
  -- either side of it any more.
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
  -- RESTATED over `depthCap` when the connect landed, and RE-READ when
  -- the cap lost its size term — which is what turned these rows from
  -- decoration into evidence.  Still DEGENERATE on the slot half, since
  -- this program has no shared slot and the partial sum is 0 at every
  -- cut; but the two bodies' caps read 6 and 10 before against depths of
  -- 1 and 2, and read 1 and 2 now.  The statement was almost entirely
  -- size slack, so nothing this probe could have measured would have
  -- crossed it; it holds with NO room at all, and any accumulation
  -- whatsoever refutes it.  That is the strongest form a green row
  -- comes in, and it is also the reason the row is worth re-running
  -- after anything touches the guard.
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
-- `μᵉ` adds one to the SIZE and NOTHING to the nesting or the input
-- cut, so with the size term gone the two caps are the SAME TERM and
-- the arithmetic that used to bridge them is not needed at all.
depth-μ-bound {n = n} fuel body κ bid now sched st =
  depth-subst-guarded fuel body (μᵉ body) κ bid now sched st

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

------------------------------------------------------------------
-- BUCKET (b′) — the burst arm AT ZERO GAS, and it is the same list
-- induction one clique wider.  `depthInner`'s zero clause returns 0
-- without entering the payload, and the gas travels UNCHANGED from the
-- burst through the frame, the walk and the consume to reach it — so at
-- `g0` every one of those returns 0 and the only charge left standing
-- is the single `suc` a `thru-outer` frame makes.  A cap whose subject
-- term is `suc _` pays that with nothing else spent.
--
-- WHICH IS ALSO A CHECK ON THE ROUTE rather than only a discharge: the
-- arm's header argues the induction descends on the GAS, and this is
-- that claim's base case, typechecked.  Had the gas not been the thing
-- the descent peels, this clique would not close.
------------------------------------------------------------------

-- switchAll's node read, which is the one place the walk looks at the
-- store before entering.  Every arm returns 0 at zero gas, but the
-- `Maybe` has to be SPLIT for that to reduce — a catch-all over a
-- variable is stuck.
consumeS-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (nid : NodeId) (κ : Path Γ u t) (id : Id) (now : Tick)
  (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e)
  (nd : Maybe (NodeState Γ)) →
  depthConsumeS g0 nid κ id now o sched st nd ≤ 0
consumeS-zero nid κ id now o sched st nothing                  = z≤n
consumeS-zero nid κ id now o sched st (just (scan-st _))       = z≤n
consumeS-zero nid κ id now o sched st (just (concat-st _ _ _)) = z≤n
consumeS-zero nid κ id now o sched st (just (take-st _))       = z≤n
consumeS-zero nid κ id now o sched st (just (merge-st _ _))    = z≤n
consumeS-zero nid κ id now o sched st (just (switch-st _ _))   = z≤n
consumeS-zero nid κ id now o sched st (just (exhaust-st _ _))  = z≤n

consume-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (op : AllOp) (nid : NodeId) (κ : Path Γ u t) (id : Id) (now : Tick)
  (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e) →
  depthConsume g0 op nid κ id now o sched st ≤ 0
consume-zero mergeᵒ   nid κ id now o sched st = z≤n
consume-zero concatᵒ  nid κ id now o sched st = z≤n
consume-zero exhaustᵒ nid κ id now o sched st = z≤n
consume-zero switchᵒ  nid κ id now o sched st =
  consumeS-zero nid κ id now o sched st
    (lookupNode nid (EvalSt.nodes st))

-- the walk threads a state per payload, so the tail's scheduler and
-- state are the consume's outputs — the same `where` shape the three
-- frame-zero lemmas above use, read off `thruConsume` instead of
-- `stepFrame`.
walk-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (op : AllOp) (nid : NodeId) (κ : Path Γ u t) (id : Id) (now : Tick)
  (vals : List (Val Γ (obs u))) (sched : Sched Γ) (st : EvalSt e) →
  depthWalk g0 op nid κ id now vals sched st ≤ 0
walk-zero op nid κ id now []       sched st = z≤n
walk-zero op nid κ id now (o ∷ os) sched st =
  ⊔-lub (consume-zero op nid κ id now o sched st)
        (walk-zero op nid κ id now os sched' st')
  where
  r      = thruConsume g0 op nid κ id now o sched st
  sched' = proj₁ (proj₂ (proj₂ r))
  st'    = proj₂ (proj₂ (proj₂ r))

-- ONE, and the `suc` is the frame's own: `depthFrame` at a
-- `thru-outer` is `suc (depthWalk …)`, so the bound is `s≤s` over the
-- walk and the burst's `⊔` keeps it there across the whole stream.
burst-thru-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (bid : Id) (now : Tick) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (stream : Stream Γ (obs u)) (sched : Sched Γ) (st : EvalSt e) →
  depthBurst g0 bid now (thru-outer op nid) κ stream sched st ≤ 1
burst-thru-zero bid now op nid κ [] sched st = z≤n
burst-thru-zero {Γ = Γ} {u = u} bid now op nid κ (em ∷ ems) sched st =
  ⊔-lub (s≤s (walk-zero op nid κ bid now (proj₁ sp) sched st))
        (burst-thru-zero bid now op nid κ ems sched' st')
  where
  -- `A` is the LEFTOVER event type, pinned to the path's root as
  -- `depthBurst` pins it, so the two `sp`s are the same term
  sp     = splitEvents {A = Val Γ u} (InstEmit.events em)
  r      = stepFrame g0 bid now (thru-outer op nid) κ
             (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  sched' = proj₁ (proj₂ (proj₂ (proj₂ r)))
  st'    = proj₂ (proj₂ (proj₂ (proj₂ r)))

-- the cap's subject term is `suc _` at every `*All` layer, and that is
-- the whole of what the zero-gas arm has to be paid out of
one-≤-capN : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (N mx : ℕ) (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) →
  1 ≤ depthCapN {e = e} (suc N) mx κ sched st
one-≤-capN N mx κ sched st =
  ≤-trans (s≤s z≤n)
          (m≤m⊔n (suc N + pathNestD κ + slotsNestBelow (Sched.slots sched) mx)
                 (nodesNestMax (Sched.slots sched) (EvalSt.nodes st)))

-- THE ARM, split on its gas.  The `g0` clause is the clique above; the
-- `gs` clause is the leaf, and nothing else remains of this face.
depth-all-burst : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (op : AllOp) (initSt : NodeState Γ) (b : Closed Γ (obs u))
  (κ : Path Γ u t) (bid : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let nid = proj₁ (mintNode sched)
      r   = subscribeE g b (thru-outer op nid ↠ κ) bid now
              (proj₂ (mintNode sched)) (installNode nid initSt st)
  in depthBurst g bid now (thru-outer op nid) κ
       (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
       ≤ depthCapN (suc (nestDᵉ (Sched.slots sched) b))
                   (maxInputᵉ b) κ sched st
depth-all-burst g0 op initSt b κ bid now sched st =
  ≤-trans (burst-thru-zero bid now op nid κ
             (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
          (one-≤-capN (nestDᵉ (Sched.slots sched) b) (maxInputᵉ b)
             κ sched st)
  where
  nid = proj₁ (mintNode sched)
  r   = subscribeE g0 b (thru-outer op nid ↠ κ) bid now
          (proj₂ (mintNode sched)) (installNode nid initSt st)
depth-all-burst (gs fuel) op initSt b κ bid now sched st =
  depth-all-burst-gs fuel op initSt b κ bid now sched st

-- INSTALLING A 0-WEIGHT NODE NEVER RAISES `nodesNestMax`, over the
-- HYPOTHESIS rather than over a constructor.  It was two copies of this
-- induction — one for `take-st`, one for `scan-st` — differing only in
-- the state installed, and both closed their `true` arm with `z≤n`
-- because the constructor made the weight literally 0.  Taking the
-- weight's vanishing as a premise buys the other four states at the same
-- price, which is what the `*All` clauses need: `merge-st`, `switch-st`,
-- `exhaust-st` and `concat-st []` all read 0, each by `refl`.
private
  setNode-nodesNestMax-0 : ∀ {n} {Γ : Ctx n} (sl : Slots Γ)
    (nid : NodeId) (s : NodeState Γ) → nodeNestMax sl s ≡ 0 →
    (nodes : List (NodeId × NodeState Γ)) →
    nodesNestMax sl (setNode nid s nodes) ≤ nodesNestMax sl nodes
  setNode-nodesNestMax-0 sl nid s eq [] = ⊔-lub (≤-reflexive eq) z≤n
  setNode-nodesNestMax-0 sl nid s eq ((j , ns) ∷ rest) with j ≡ᵇ nid
  ... | true  = ⊔-lub (≤-trans (≤-reflexive eq) z≤n) (m≤n⊔m _ _)
  ... | false = ⊔-lub (m≤m⊔n _ _)
                      (≤-trans (setNode-nodesNestMax-0 sl nid s eq rest)
                               (m≤n⊔m _ _))

-- After mintNode + installNode(take-st(suc k)), storeNestMax is
-- unchanged: nodeNestMax(take-st _) = 0, and mintNode preserves slots.
-- stated over the CAP rather than over `storeNestMax`, because that is
-- what the take clause's IH now returns.  Only the node half moves:
-- `mintNode` leaves the slots alone, so the whole left arm — the
-- below-sum included — is definitionally unchanged.
depthCap-install0 : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {e : Closed Γ t} {u}
  (b : Exp Γ Δᵍ Δ Θ u) (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e)
  (s : NodeState Γ) → nodeNestMax (Sched.slots sched) s ≡ 0 →
  depthCap b κ (proj₂ (mintNode sched))
               (installNode (proj₁ (mintNode sched)) s st)
    ≤ depthCap b κ sched st
depthCap-install0 b κ sched st s eq =
  ⊔-mono-≤ ≤-refl
    (setNode-nodesNestMax-0 (Sched.slots sched) (Sched.nextNode sched)
       s eq (EvalSt.nodes st))

------------------------------------------------------------------
-- ARITHMETIC HELPERS — proved here.
------------------------------------------------------------------

-- Core step: a + suc p ≤ suc (c + a) + p.  The `*All` arm is the ONLY
-- caller now: it is the only descent that moves the path measure, and
-- the unit it moves it by is the one the `*All` constructor's own
-- `nestDᵉ` grants.  The three structural descents below need no
-- arithmetic step at all, which is the tightening's whole dividend —
-- `pathNestD` does not charge them, so nothing has to fund them.
private
  arith-step : ∀ (a p c : ℕ) → a + suc p ≤ suc (c + a) + p
  arith-step a p c =
    ≤-trans (≤-reflexive (+-suc a p))
            (s≤s (+-mono-≤ (m≤n+m a c) ≤-refl))

-- nestDᵉ b ≤ nestDᵗ f + nestDᵉ b = nestDᵉ (mapᵉ f b), and the path
-- measure is UNCHANGED by the descent
map-size-arith : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (f : Fn Γ [] [] [] s u) (b : Closed Γ s)
  (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) →
  depthCap b (map-f f ↠ κ) sched st ≤ depthCap (mapᵉ f b) κ sched st
map-size-arith {n = n} f b κ sched st =
  ⊔-mono-≤ (+-mono-≤
              (+-mono-≤ (m≤n+m (nestDᵉ (Sched.slots sched) b)
                               (nestDᵗ (Sched.slots sched) f))
                        ≤-refl)
              (slotsNestBelow-mono (Sched.slots sched)
                 (maxInputᵉ b) (maxInputᵉ (mapᵉ f b)) (m≤n⊔m _ _)))
           ≤-refl

-- take adds NOTHING to the nesting, so this is the below-sum widening
-- alone
take-size-arith : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Tm Γ [] [] [] natᵗ) (b : Closed Γ u) (nid : NodeId)
  (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) →
  depthCap b (take-f nid ↠ κ) sched st ≤ depthCap (takeᵉ c b) κ sched st
take-size-arith {n = n} c b nid κ sched st =
  ⊔-mono-≤ (+-mono-≤ (≤-refl {x = nestDᵉ (Sched.slots sched) b + pathNestD κ})
                     (slotsNestBelow-mono (Sched.slots sched)
                        (maxInputᵉ b) (maxInputᵉ (takeᵉ c b)) (m≤n⊔m _ _)))
           ≤-refl

-- scan: the seed's nesting and the PRODUCT term both sit to the left of
-- the source's own nesting, so this is `m≤n+m` at a two-summand
-- constant.  The install is absorbed BEFORE this arithmetic runs —
-- `depthCap-install0` returns the IH's post-install cap to the entry
-- cap, so what is left here is the syntax payment alone.
scan-size-arith : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u) (b : Closed Γ s)
  (nid : NodeId) (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) →
  depthCap b (scan-f f nid ↠ κ) sched st
    ≤ depthCap (scanᵉ f seed b) κ sched st
scan-size-arith {n = n} f seed b nid κ sched st =
  ⊔-mono-≤ (+-mono-≤
              (+-mono-≤ (m≤n+m (nestDᵉ (Sched.slots sched) b) _) ≤-refl)
              (slotsNestBelow-mono (Sched.slots sched)
                 (maxInputᵉ b) (maxInputᵉ (scanᵉ f seed b))
                 (m≤n⊔m _ _)))
           ≤-refl

-- THE `*All` ARM, and it serves all four operators from one statement:
-- `sizeᵉ`, `nestDᵉ` and `maxInputᵉ` treat `mergeAllᵉ`, `concatAllᵉ`,
-- `switchAllᵉ` and `exhaustAllᵉ` identically — `suc` on the first two,
-- unchanged on the third — so the four caps are one term and the
-- conclusion is written at `depthCapN` rather than at any constructor.
-- The install is folded in HERE rather than left to the clause, because
-- unlike take and scan the `*All` clauses have a second arm to state and
-- the node weight is the only thing that differs between the four.
-- `≤-refl` on the below-sum where the siblings need
-- `slotsNestBelow-mono`: a `*All` layer adds no input.
private
  all-outer-arith : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (op : AllOp) (s : NodeState Γ) (b : Closed Γ (obs u))
    (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) →
    nodeNestMax (Sched.slots sched) s ≡ 0 →
    depthCap b (thru-outer op (proj₁ (mintNode sched)) ↠ κ)
               (proj₂ (mintNode sched))
               (installNode (proj₁ (mintNode sched)) s st)
      ≤ depthCapN (suc (nestDᵉ (Sched.slots sched) b))
                  (maxInputᵉ b) κ sched st
  all-outer-arith {n = n} op s b κ sched st eq =
    ≤-trans (depthCap-install0 b (thru-outer op (proj₁ (mintNode sched)) ↠ κ)
               sched st s eq)
            (⊔-mono-≤ (+-mono-≤ (arith-step (nestDᵉ (Sched.slots sched) b)
                                   (pathNestD κ) 0)
                                ≤-refl)
                      ≤-refl)

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
    -- slot `i`'s summand, which IS `nestDᵉ sl d` — the child's whole
    -- charge, on the nose and in the one currency
    step : nestDᵉ sl d + slotsNestBelow sl (toℕ i)
             ≤ slotsNestBelow sl (suc (toℕ i))
    step = subst (λ s → slotNest sl s + slotsNestBelow sl (toℕ i)
                          ≤ slotsNestBelow sl (suc (toℕ i)))
                 slotEq (slotsNestBelow-step sl i)
    -- `pathNestD (share-sink i)` is 0 definitionally: the connect resets
    -- the path, which is why the goal's own `κ` is free room here.  With
    -- both sides in the nesting currency the charge and the payment are
    -- the same number again, so nothing here is slack.
    slotPay : nestDᵉ sl d + 0 + slotsNestBelow sl (maxInputᵉ d)
                ≤ slotsNestBelow sl (suc (toℕ i))
    slotPay = ≤-trans
                (+-mono-≤ (≤-reflexive (+-identityʳ (nestDᵉ sl d))) below)
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
          (depthCap-install0 b (take-f nid ↠ κ) sched st (take-st (suc k)) refl))
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
          (depthCap-install0 b (scan-f f nid ↠ κ) sched st
             (scan-st (evalTm seed)) refl))
        (≤-trans (burst-scf-zero fuel bid now f nid κ
                    (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
                 z≤n))
      (scan-size-arith f seed b nid κ sched st)
    where
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₀    = installNode nid (scan-st (evalTm seed)) st
    r      = subscribeE fuel b (scan-f f nid ↠ κ) bid now sched₁ st₀

  -- BUCKET (b)+(d): *All — the OUTER arm is this induction at `b`, the
  -- BURST arm is the one leaf left.  `suc (sizeᵉ b)` IS `sizeᵉ (*Allᵉ b)`
  -- definitionally, and so is the nesting `suc`, which is why one
  -- `all-outer-arith` covers four constructors.  The `refl` is
  -- `nodeNestMax` of the installed state: nothing in the depth family
  -- reads an outer node, so all four weigh 0 and the IH comes back
  -- through the ENTRY store, exactly as take and scan do.
  depth-compositional-go fuel (mergeAllᵉ b) κ bid now sched st =
    ⊔-lub
      (≤-trans (depth-compositional-go fuel b
                  (thru-outer mergeᵒ nid ↠ κ) bid now sched₁ st₀)
               (all-outer-arith mergeᵒ (merge-st 0 false) b κ sched st refl))
      (depth-all-burst fuel mergeᵒ (merge-st 0 false) b κ bid now sched st)
    where
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₀    = installNode nid (merge-st 0 false) st

  depth-compositional-go {u = u} fuel (concatAllᵉ b) κ bid now sched st =
    ⊔-lub
      (≤-trans (depth-compositional-go fuel b
                  (thru-outer concatᵒ nid ↠ κ) bid now sched₁ st₀)
               (all-outer-arith concatᵒ (concat-st {t = u} [] false false)
                  b κ sched st refl))
      (depth-all-burst fuel concatᵒ (concat-st {t = u} [] false false)
         b κ bid now sched st)
    where
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₀    = installNode nid (concat-st {t = u} [] false false) st

  depth-compositional-go fuel (switchAllᵉ b) κ bid now sched st =
    ⊔-lub
      (≤-trans (depth-compositional-go fuel b
                  (thru-outer switchᵒ nid ↠ κ) bid now sched₁ st₀)
               (all-outer-arith switchᵒ (switch-st nothing false)
                  b κ sched st refl))
      (depth-all-burst fuel switchᵒ (switch-st nothing false)
         b κ bid now sched st)
    where
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₀    = installNode nid (switch-st nothing false) st

  depth-compositional-go fuel (exhaustAllᵉ b) κ bid now sched st =
    ⊔-lub
      (≤-trans (depth-compositional-go fuel b
                  (thru-outer exhaustᵒ nid ↠ κ) bid now sched₁ st₀)
               (all-outer-arith exhaustᵒ (exhaust-st false false)
                  b κ sched st refl))
      (depth-all-burst fuel exhaustᵒ (exhaust-st false false)
         b κ bid now sched st)
    where
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₀    = installNode nid (exhaust-st false false) st


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