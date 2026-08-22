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
-- (4) WAS THE REAL WORK, AND IS DISCHARGED: every clause that calls
--     `depthBurst` feeds it the scheduler the REAL `subscribeE`
--     produced, while the RHS reads the ENTRY one.  With the cap a
--     function of `Sched.slots` alone, the preservation conjunct is
--     exactly `subscribeE-slots` (Keeps-Ring), unconditional and
--     PROVEN, so the `gs` arm substitutes with it and nothing about
--     preservation remains inside a leaf.  It never needed
--     `subscribeE-caps`, which would have been circular — that face
--     takes `depthE ≤ dep` as a hypothesis.
--
-- BUCKETS: (a) trivially zero — ofᵉ, emptyᵉ, deferᵉ, g0(μᵉ),
-- takeᵉ(zero), and the g0 connect.  (b) IH + arithmetic — mapᵉ,
-- takeᵉ(suc), scanᵉ, over the burst-zero and installNode lemmas below.
-- (c) THE CONNECT, a real clause: `input` recurses into the slot's own
-- def and pays for it out of the summand admitting slot `i` to the
-- partial sum.  (d) BLOCKED, two named postulates —
-- `emit-cap` (what a subscribe's burst EMITS is no more deeply nested
-- than the expression that emitted it; every other part of the `*All`
-- face is a real body over it, including the burst walk itself) and
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
  using (ℕ; zero; suc; _+_; _≤_; _⊔_; z≤n; s≤s; _<ᵇ_; _≤ᵇ_)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; m≤n+m; +-mono-≤; ⊔-lub; n≤1+n; m≤m⊔n; m≤n⊔m; +-suc; ≤-reflexive; ≤ᵇ⇒≤; n≮n;
  +-identityʳ; +-monoˡ-≤)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; con)
open import Data.Fin   using (Fin; toℕ)
open import Data.List  using (List; []; _∷_; foldr; tabulate)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans)
open import Data.Nat.ListAction using (sum)
open import Data.Bool  using (Bool; false; true; if_then_else_; T; _∧_)
open import Data.Bool.ListAction using (all)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; proj₁; proj₂)
open import Rx.Prim
  using (Gas; g0; gs; Id; Tick; InstEmit; InstEvent; init; value; close; handoff;
  complete)
open import Rx.Exp
  using (natᵗ; _×ᵗ_; Ctx; Closed; Exp; Tm; Fn; Val; obs; evalTm; unfoldμ; elimGExp; sizeᵉ; input; ofᵉ;
  emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
  varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
  inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ)
open import Rx.Evaluator
  using (Sched; EvalSt; NodeState; AllOp; NodeId; Path; Stream; scan-st; merge-st; concat-st;
  switch-st; exhaust-st; take-st; mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ; _↠_; map-f; scan-f;
  take-f; from-inner; thru-outer; mintNode; installNode; subscribeE; splitEvents; stepFrame;
  root; share-sink; register; lookupNode; thruConsume; switchKill)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵗ)
open import Rx.Slots using (scripted; shared; Slot; Slots)

-- pathLen, imported from .Measures where it is defined — the
-- SAME pathLen `depth-capped`'s statement reads, so the landing plugs
-- into its consumer unchanged.
open import Verify-Budget-Sufficient.Measures using
  (pathLen; sum-tab-mono)
open import Verify-Budget-Sufficient.Caps-Nest using (sum-tab-slack)
open import Verify-Budget-Sufficient.Keeps-Ring
  using (subscribeE-slots; KeepsC; thruConsume-keeps; stepFrame-keeps;
  switchKill-keeps)
open import Data.Empty using (⊥-elim)
open import Decide
  using (force-false; T-to; ≤ᵇ-true; ≤ᵇ-widen; ∧ˡ; ∧ʳ; ∧-intro; ∧-trueˡ; ∧-trueʳ)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthE; depthBurst; depthWalk; depthConsume; depthConsumeS; depthInner)

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
-- TAKES THE SLOTS — but the argument that FORCED the change is not the
-- one that holds it, and the difference is worth recording.  The change
-- was made for the burst arm: a `concatAllᵉ` queues an emitted inner
-- into this measure, so while it charged `sizeᵉ o` the arm looked to
-- need the cap to bound an emitted inner's SIZE, which is exactly what
-- an accumulator-wrapping scan refutes.  Working that arm's arithmetic
-- said otherwise — the cap does not read the node store at all
-- (`depthCapN`'s header) — so the arm never collects.
--
-- WHAT THE CURRENCY BUYS INSTEAD is that `storeNestMax`, the EXPORTED
-- bound's own right-hand side, got strictly smaller: every statement
-- over it stayed true and `nest-store≤capsH` (Caps-Bridge) has less to
-- bound.  That is a strengthening rather than a repair.
--
-- AND IT IS KEPT FOR THE DELIVERY FACE, whose consumer is nameable
-- rather than hypothetical.  The queue-walking clause is `depthFin`'s,
-- reached only through `depthFold`, and that is the face the delivery
-- postulate in Caps-Face/Part7 covers; when that side is bounded it
-- will read a concat queue exactly as this measure does, and it will
-- want the nesting currency for the reason the subscribe side wanted
-- it.  The subscribe face is what stopped spending it, not the depth
-- family.
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
--
-- AND THE SUBSCRIBE FACE NO LONGER SPENDS IT AT ALL: `cap-≤-store`
-- widens into the slot half alone, so `depth-compositional` would hold
-- verbatim with this arm deleted, and hold STRONGER.  It stays because
-- the face that reads a queue is the delivery one (`nodeNestMax`'s
-- header), and an export that over-states its own right-hand side costs
-- its consumers nothing.
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

-- NO NODE ARM, AND THAT IS A REACHABILITY FACT ABOUT THE DEPTH FAMILY
-- RATHER THAN A CHOICE.  This cap joined a `nodesNestMax` term until the
-- `*All` burst arm was worked and could not close over it: `depthFrame`
-- at a `thru-outer` is `suc (depthWalk …)`, and `suc (A ⊔ L)` is
-- `suc A ⊔ suc L`, while a goal carrying a bare node arm offers only
-- `L` — the frame's own `suc` had nowhere to land, at any program.
--
-- THE ARM IS UNREACHABLE FROM `depthE`.  `depthDrain` is the only clause
-- in the family that reads a node's queue CONTENT, and it hangs off
-- `depthFrame`'s `from-inner` arm, which only `depthFold` ever supplies
-- — the DELIVERY family.  `depthE` passes `map-f`, `scan-f`, `take-f`
-- and `thru-outer`, and nothing else.  So dropping the arm STRENGTHENS
-- every statement below it and lands the frame's `suc` exactly, since
-- `suc N + p + bel` is the subject term the `*All` cap already names.
--
-- WHAT IT COST, and again the answer is that it paid: `cap-≤-store` lost
-- a half, the three structural arithmetic lemmas and the connect clause
-- each lost a join layer, and `depthCap-install0` with its `setNode`
-- induction went entirely — the cap is invariant under
-- `mintNode`/`installNode` by REDUCTION now, so take, scan and all four
-- `*All` clauses hand their IH straight in.  A cap that reads only the
-- scheduler is also what makes the burst arm's remaining obligation
-- nameable: slot preservation across `subscribeE`, and nothing about the
-- node store.
depthCapN : ∀ {n} {Γ : Ctx n} {t} {u}
  (sz mx : ℕ) (κ : Path Γ u t) (sched : Sched Γ) → ℕ
depthCapN sz mx κ sched =
  sz + pathNestD κ + slotsNestBelow (Sched.slots sched) mx

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
depthCap : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {u}
  (b : Exp Γ Δᵍ Δ Θ u) (κ : Path Γ u t) (sched : Sched Γ) → ℕ
depthCap {n = n} b κ sched =
  depthCapN (nestDᵉ (Sched.slots sched) b) (maxInputᵉ b) κ sched

slotsNestBelow-≤-sum : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (k : ℕ) →
  slotsNestBelow sl k ≤ slotsNestSum sl
slotsNestBelow-≤-sum {n} sl k =
  sum-tab-mono {n} (slotNestBelow sl k) (λ i → slotNest sl (sl i))
    (λ i → if-mono (toℕ i <ᵇ k) true (slotNest sl (sl i)) (λ _ → refl))

-- and the bridge the export spends, now a single chain of three
-- widenings: the cap is one sum rather than a join, so the exported
-- statement keeps its text verbatim while everything above this line
-- got smaller, and nothing downstream of this module moves.
cap-≤-store : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {e : Closed Γ t} {u}
  (b : Exp Γ Δᵍ Δ Θ u) (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) →
  depthCap b κ sched
    ≤ sizeᵉ b + nestDᵉ (Sched.slots sched) b + pathLen κ
        + storeNestMax sched st
cap-≤-store {n = n} b κ sched st = slotHalf
  where
  SZ : ℕ
  SZ = sizeᵉ b + nestDᵉ (Sched.slots sched) b
  -- one widening per summand: the cap's own currency into the exported
  -- sum, the spending-arc count into the frame count, and the below-sum
  -- into the whole sum
  slotHalf : nestDᵉ (Sched.slots sched) b + pathNestD κ
               + slotsNestBelow (Sched.slots sched) (maxInputᵉ b)
               ≤ SZ + pathLen κ + storeNestMax sched st
  slotHalf = +-mono-≤
               (+-mono-≤ (m≤n+m (nestDᵉ (Sched.slots sched) b) (sizeᵉ b))
                         (pathNestD≤pathLen κ))
               (≤-trans (slotsNestBelow-≤-sum (Sched.slots sched) (maxInputᵉ b))
                        (m≤m⊔n _ _))

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
      ≤ depthCap body κ sched

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
    ≤ depthCap (μᵉ body) κ sched
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
one-≤-capN : ∀ {n} {Γ : Ctx n} {t} {u}
  (N mx : ℕ) (κ : Path Γ u t) (sched : Sched Γ) →
  1 ≤ depthCapN (suc N) mx κ sched
one-≤-capN N mx κ sched = s≤s z≤n

------------------------------------------------------------------
-- BUCKET (d′) — THE BURST ARM AT POSITIVE GAS, and it is bucket (b′)'s
-- clique one currency up.  Where the zero-gas clique reported 0 at every
-- entry, this one ENTERS, so each member carries two things the zero
-- version needed neither of: the induction hypothesis, to bound what it
-- finds inside a payload, and the fact that the slots have not moved, so
-- that the bound it carries still names the same number.
--
-- THE IH IS AN EXPLICIT PARAMETER, NOT A MUTUAL SIBLING, and that is a
-- cost decision rather than a style one.  Made mutual with the assembly,
-- this clique would give the module its FIRST multi-member mutual block,
-- and `make agda-dev` STUBS those — the file's dev check would stop being
-- a real check, termination included, for the sake of a recursion that is
-- not actually mutual.  It is not: every edge here descends either its own
-- list argument or the gas, and the gas edge is the one that reaches the
-- subject, because `depthInner`'s `gs` clause is the only entry into a
-- payload and it peels one.  So the hypothesis is taken at `fuel` and the
-- conclusion drawn at `gs fuel`, which is the same lexicographic order on
-- (gas, subject) the connect clause has always run on.
------------------------------------------------------------------

DepthIH : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Gas → Set
DepthIH {Γ = Γ} {t = t} e g = ∀ {u} (b : Closed Γ u) (κ : Path Γ u t)
  (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  depthE g b κ bid now sched st ≤ depthCap b κ sched

-- THE SUBJECT HALF OF THE CAP, which is the half that travels.  A burst
-- walk holds its path fixed and changes the subject at every payload, so
-- what has to be carried across the clique is `depthCapN`'s two subject
-- terms rather than the cap itself.
innerNest : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ w} → Slots Γ → Exp Γ Δᵍ Δ Θ w → ℕ
innerNest sl x = nestDᵉ sl x + slotsNestBelow sl (maxInputᵉ x)

-- THE SUM AND NOT THE TWO CONJUNCTS, and the `input` shape is why: at
-- `b = input i` the emitter's own nesting is 0 while what it emits comes
-- out of the slot's def, so the nesting conjunct alone is false there and
-- the below-sum's step at `suc (toℕ i)` is what pays — the same equality
-- the connect clause spends.  A predicate that split them would be
-- refuted by the connect and could not be repaired by tightening either.
valND? : ∀ {n} {Γ : Ctx n} {u} → Slots Γ → ℕ → Val Γ (obs u) → Bool
valND? sl C o = innerNest sl o ≤ᵇ C

valsND? : ∀ {n} {Γ : Ctx n} {u} → Slots Γ → ℕ → List (Val Γ (obs u)) → Bool
valsND? sl C = all (valND? sl C)

eventND? : ∀ {n} {Γ : Ctx n} {u} → Slots Γ → ℕ →
  InstEvent (Val Γ (obs u)) → Bool
eventND? sl C (value o)   = valND? sl C o
eventND? sl C (init _)    = true
eventND? sl C (close _ _) = true
eventND? sl C (handoff _) = true
eventND? sl C complete    = true

burstND? : ∀ {n} {Γ : Ctx n} {u} → Slots Γ → ℕ → Stream Γ (obs u) → Bool
burstND? sl C = all (λ em → all (eventND? sl C) (InstEmit.events em))

-- the walk reads the VALUES out of a burst's events, so the predicate has
-- to come apart the same way `splitEvents` does.  Its `Ψ` and `caps`
-- twins are in .Psi-Split and .Caps-Face.Part4; this is the same
-- induction over the five event shapes, four of which carry no value.
splitEvents-vals-ND : ∀ {n} {Γ : Ctx n} {u} {A : Set}
  (sl : Slots Γ) (C : ℕ) (es : List (InstEvent (Val Γ (obs u)))) →
  all (eventND? sl C) es ≡ true →
  valsND? sl C (proj₁ (splitEvents {A = A} es)) ≡ true
splitEvents-vals-ND sl C [] h = refl
splitEvents-vals-ND {A = A} sl C (value o ∷ es) h =
  ∧-intro (∧-trueˡ h) (splitEvents-vals-ND {A = A} sl C es (∧-trueʳ h))
splitEvents-vals-ND {A = A} sl C (init _ ∷ es) h =
  splitEvents-vals-ND {A = A} sl C es (∧-trueʳ h)
splitEvents-vals-ND {A = A} sl C (close _ _ ∷ es) h =
  splitEvents-vals-ND {A = A} sl C es (∧-trueʳ h)
splitEvents-vals-ND {A = A} sl C (handoff _ ∷ es) h =
  splitEvents-vals-ND {A = A} sl C es (∧-trueʳ h)
splitEvents-vals-ND {A = A} sl C (complete ∷ es) h =
  splitEvents-vals-ND {A = A} sl C es (∧-trueʳ h)

-- the one arithmetic move the clique makes, and it makes it once: the
-- path term sits BETWEEN the cap's two subject terms, so spending a
-- bound on their SUM means commuting it past the path
private
  nest-shuffle : ∀ (a p b c : ℕ) → a + b ≤ c → a + p + b ≤ c + p
  nest-shuffle a p b c h =
    ≤-trans (≤-reflexive (solve 3 (λ x y z →
               (x :+ y) :+ z := (x :+ z) :+ y) refl a p b))
            (+-monoˡ-≤ p h)

  cap-shuffle : ∀ (a p b : ℕ) → suc (a + b + p) ≡ suc a + p + b
  cap-shuffle a p b =
    solve 3 (λ x y z → con 1 :+ ((x :+ z) :+ y) := ((con 1 :+ x) :+ y) :+ z)
      refl a p b

-- ONE PAYLOAD, and the only place the gas peels.  What comes back is the
-- IH's cap at the payload, whose path term is `κ`'s again because
-- `pathNestD` charges a `from-inner` nothing — the frame that installed
-- the inner was already charged for it, by the `suc` the walk sits under.
inner-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (fuel : Gas) (ih : DepthIH e fuel) (sl : Slots Γ) (C : ℕ)
  (op : AllOp) (nid : NodeId) (κ : Path Γ u t) (bid : Id) (now : Tick)
  (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → valND? sl C o ≡ true →
  depthInner (gs fuel) op nid κ bid now o sched st ≤ C + pathNestD κ
inner-nest fuel ih sl C op nid κ bid now o sched st refl hv =
  ≤-trans (ih o (from-inner op nid (Sched.nextNode sched) ↠ κ) bid now
              (record sched { nextNode = suc (Sched.nextNode sched) }) st)
          (nest-shuffle (nestDᵉ (Sched.slots sched) o) (pathNestD κ)
             (slotsNestBelow (Sched.slots sched) (maxInputᵉ o)) C
             (≤ᵇ⇒≤ _ C (T-to hv)))

-- switchAll's node read, split for the same reason `consumeS-zero` is:
-- a catch-all over a variable `Maybe` is stuck, so every constructor
-- appears.  Only the live-inner arm subscribes, and it subscribes at the
-- state the CUT left — which is why its slot equation is a `trans`
-- through `switchKill-keeps` rather than the caller's own.
consumeS-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (fuel : Gas) (ih : DepthIH e fuel) (sl : Slots Γ) (C : ℕ)
  (nid : NodeId) (κ : Path Γ u t) (bid : Id) (now : Tick)
  (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e)
  (nd : Maybe (NodeState Γ)) →
  Sched.slots sched ≡ sl → valND? sl C o ≡ true →
  depthConsumeS (gs fuel) nid κ bid now o sched st nd ≤ C + pathNestD κ
consumeS-nest fuel ih sl C nid κ bid now o sched st
  (just (switch-st cur od)) hs hv =
  inner-nest fuel ih sl C switchᵒ nid κ bid now o
    (proj₁ (proj₂ (switchKill cur sched st)))
    (proj₂ (proj₂ (switchKill cur sched st)))
    (trans (KeepsC.slotsEq (switchKill-keeps cur sched st)) hs) hv
consumeS-nest fuel ih sl C nid κ bid now o sched st
  nothing                  hs hv = z≤n
consumeS-nest fuel ih sl C nid κ bid now o sched st
  (just (scan-st _))       hs hv = z≤n
consumeS-nest fuel ih sl C nid κ bid now o sched st
  (just (concat-st _ _ _)) hs hv = z≤n
consumeS-nest fuel ih sl C nid κ bid now o sched st
  (just (take-st _))       hs hv = z≤n
consumeS-nest fuel ih sl C nid κ bid now o sched st
  (just (merge-st _ _))    hs hv = z≤n
consumeS-nest fuel ih sl C nid κ bid now o sched st
  (just (exhaust-st _ _))  hs hv = z≤n

consume-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (fuel : Gas) (ih : DepthIH e fuel) (sl : Slots Γ) (C : ℕ)
  (op : AllOp) (nid : NodeId) (κ : Path Γ u t) (bid : Id) (now : Tick)
  (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → valND? sl C o ≡ true →
  depthConsume (gs fuel) op nid κ bid now o sched st ≤ C + pathNestD κ
consume-nest fuel ih sl C mergeᵒ nid κ bid now o sched st hs hv =
  inner-nest fuel ih sl C mergeᵒ nid κ bid now o sched st hs hv
consume-nest fuel ih sl C concatᵒ nid κ bid now o sched st hs hv =
  inner-nest fuel ih sl C concatᵒ nid κ bid now o sched st hs hv
consume-nest fuel ih sl C exhaustᵒ nid κ bid now o sched st hs hv =
  inner-nest fuel ih sl C exhaustᵒ nid κ bid now o sched st hs hv
consume-nest fuel ih sl C switchᵒ nid κ bid now o sched st hs hv =
  consumeS-nest fuel ih sl C nid κ bid now o sched st
    (lookupNode nid (EvalSt.nodes st)) hs hv

-- the walk threads a state per payload, so the tail runs at the consume's
-- outputs and its slot equation chains through `thruConsume-keeps`.  The
-- predicate comes apart the same way the list does.
walk-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (fuel : Gas) (ih : DepthIH e fuel) (sl : Slots Γ) (C : ℕ)
  (op : AllOp) (nid : NodeId) (κ : Path Γ u t) (bid : Id) (now : Tick)
  (vals : List (Val Γ (obs u))) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → valsND? sl C vals ≡ true →
  depthWalk (gs fuel) op nid κ bid now vals sched st ≤ C + pathNestD κ
walk-nest fuel ih sl C op nid κ bid now [] sched st hs hvs = z≤n
walk-nest fuel ih sl C op nid κ bid now (o ∷ os) sched st hs hvs =
  ⊔-lub (consume-nest fuel ih sl C op nid κ bid now o sched st hs
           (∧-trueˡ hvs))
        (walk-nest fuel ih sl C op nid κ bid now os sched' st'
           (trans (KeepsC.slotsEq (thruConsume-keeps (gs fuel) op nid κ bid now o
                              sched st)) hs)
           (∧-trueʳ hvs))
  where
  r      = thruConsume (gs fuel) op nid κ bid now o sched st
  sched' = proj₁ (proj₂ (proj₂ r))
  st'    = proj₂ (proj₂ (proj₂ r))

-- ONE, and it is the frame's own: `depthFrame` at a `thru-outer` is
-- `suc (depthWalk …)`, exactly as at zero gas.  The `⊔` keeps the bound
-- across the stream and `stepFrame-keeps` keeps the slots.
burst-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (fuel : Gas) (ih : DepthIH e fuel) (sl : Slots Γ) (C : ℕ)
  (op : AllOp) (nid : NodeId) (κ : Path Γ u t) (bid : Id) (now : Tick)
  (stream : Stream Γ (obs u)) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → burstND? sl C stream ≡ true →
  depthBurst (gs fuel) bid now (thru-outer op nid) κ stream sched st
    ≤ suc (C + pathNestD κ)
burst-nest fuel ih sl C op nid κ bid now [] sched st hs hb = z≤n
burst-nest {Γ = Γ} {u = u} fuel ih sl C op nid κ bid now (em ∷ ems) sched st
  hs hb =
  ⊔-lub (s≤s (walk-nest fuel ih sl C op nid κ bid now (proj₁ sp) sched st hs
                (splitEvents-vals-ND {A = Val Γ u} sl C
                   (InstEmit.events em) (∧-trueˡ hb))))
        (burst-nest fuel ih sl C op nid κ bid now ems sched' st'
           (trans (KeepsC.slotsEq (stepFrame-keeps (gs fuel) bid now
                              (thru-outer op nid) κ (proj₁ sp)
                              (proj₂ (proj₂ sp)) sched st)) hs)
           (∧-trueʳ hb))
  where
  -- `A` is the LEFTOVER event type, pinned as `depthBurst` pins it, so
  -- the two `sp`s are the same term
  sp     = splitEvents {A = Val Γ u} (InstEmit.events em)
  r      = stepFrame (gs fuel) bid now (thru-outer op nid) κ
             (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  sched' = proj₁ (proj₂ (proj₂ (proj₂ r)))
  st'    = proj₂ (proj₂ (proj₂ (proj₂ r)))

-- depthAll's burst uses thru-outer (the spending arc).  Census finding
-- (4) read this as owing `storeNestMax` preservation through
-- `subscribeE`, proved simultaneously; it owes neither.  The cap does not
-- read the store at all, and the slots half is PROVEN separately
-- (`subscribeE-slots`) — so the whole of that finding is discharged by a
-- single `subst` in the arm below, and it is recorded here as read
-- because a route that turned out unnecessary is the kind a later reader
-- would otherwise re-schedule.
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
-- burst (different `initSt`, and their queueing is charged by the
-- store's node half, which this cap does not read); no nested burst;
-- no post-cascade state;
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
-- recording because it read as the blocker and because the way it
-- dissolved is the lesson.  Stated standalone, the arm quantifies over
-- a free initial node state, the install lemma needed that state to
-- weigh 0, and the unconditional form was NOT refuted — installing can
-- only raise a node measure — so a hypothesis was not licensed and the
-- arm looked stuck.  What settled it was neither a proof nor a
-- hypothesis: the cap stopped reading the node store at all
-- (`depthCapN`'s header), the install lemma went with it, and there is
-- nothing left for a free `initSt` to threaten.  An over-general
-- argument in a statement is worth suspecting of being a statement
-- that belongs somewhere else.
--
-- WHAT IS LEFT HERE IS THE ARM THAT CANNOT BE INLINED, and finding
-- (4) above says why: its scheduler and state come out of the REAL
-- `subscribeE`, while the cap reads the entry scheduler, so it owes a
-- preservation argument no arithmetic supplies.  That obligation is
-- one conjunct lighter than it was — the cap reads the SLOTS and
-- nothing else, so the state half of it went with the node arm.  The
-- three projections below are that subscribe's stream, scheduler and
-- state, in that order.
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
-- AND THE STORE MEASURE FOLLOWED IT, THOUGH NOT FOR THE REASON GIVEN
-- WHEN IT DID — worth recording, because the wrong reason is the one
-- this arm supplied.  The expectation was that the burst has to bound
-- the IH's cap at the state the walk REACHED, and a `concatAllᵉ`
-- queues an emitted inner into `nodeNestMax`, so while that charged a
-- SIZE the arm looked to need the cap to bound an emitted inner's size
-- — exactly what an accumulator-wrapping scan refutes.  Working the
-- arithmetic said otherwise: the cap does not read the node store at
-- all, so this arm never collects.  Both halves of the store read
-- `nestDᵉ` anyway, which shrank the EXPORT rather than this leaf, and
-- the leaf below is one conjunct lighter for the same finding.
--
-- AND THE ROUTE IS RUN.  Everything the paragraphs above scheduled is
-- below as real bodies: the gas split, the burst-side clique, and the
-- entry into the payload.  One thing came out differently from how it was
-- scheduled, and it is worth recording because the route took it for
-- granted: THE CLIQUE DID NOT HAVE TO JOIN THE ASSEMBLY'S MUTUAL BLOCK.
-- The recursion is not mutual — the induction hypothesis travels as an
-- ARGUMENT at strictly lower gas (`DepthIH e fuel`, concluding at
-- `gs fuel`) — so this module still has NO multi-member mutual block and
-- its `make agda-dev` run is still a real check, termination included,
-- which is exactly what a stubbed block would have stopped checking.
--
-- WHAT WAS RIGHT is the half that mattered: the gas is the measure, and
-- what is left over is one fact about what a burst emits.
postulate
  -- WHAT A SUBSCRIBE'S BURST EMITS IS NO MORE DEEPLY NESTED THAN THE
  -- EXPRESSION THAT EMITTED IT, and this is all that is left of the
  -- `*All` face: the burst arm, the walk, the consume and the payload
  -- entry are real bodies over it, and so is the arm's gas split.
  --
  -- IT IS THE SUM AND NOT THE TWO CONJUNCTS, and the `input` shape is
  -- why.  At `b = input i` the emitter's own nesting is 0 while what it
  -- emits comes out of the slot's def, so a nesting-only conjunct is
  -- FALSE there; the below-sum's step at `suc (toℕ i)` is what pays,
  -- which is the same equality the connect clause spends.  A predicate
  -- splitting them would be refuted by the connect and no tightening
  -- would repair it.
  --
  -- ITS PREDECESSOR — the same statement over a SUMMING `nestDᵗˢ` — IS
  -- REFUTED, and the refutation is why `Rx.Nest-Depth` reads an `ofᵉ`
  -- list with a `⊔`.  A step function may hand its input observable to
  -- an `ofᵉ` list twice; under the sum, the emitted inner then measured
  -- 3 where its emitter measured 2, while its own DEPTH was 2 — the
  -- measure was over the depth by exactly the duplication.  Measured at
  -- that program (Probed.Nest-Depth §3), which is now the row that keeps
  -- the sum from coming back.
  --
  -- WHAT IT IS NOT ASKED FOR: slot preservation.  The consumer moves its
  -- own cap between the entry scheduler and the reached one with the
  -- PROVEN `subscribeE-slots` (Keeps-Ring), off a `KeepsC` family
  -- covering `stepFrame`, `thruConsume`, `thruWalk`, `thruWrap`,
  -- `switchKill` and `concatDrain` besides — so the statement below is
  -- read at the reached scheduler and never sees the question.
  emit-cap : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ (obs u)) (κ : Path Γ (obs u) t)
    (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    let r  = subscribeE g b κ bid now sched st
        sl = Sched.slots (proj₁ (proj₂ r))
    in burstND? sl (innerNest sl b) (proj₁ r) ≡ true

-- THE ARM AT ZERO GAS.  Unchanged in content from the clause it was
-- split out of; it is a separate name now only because its sibling
-- takes an induction hypothesis and it does not.
depth-all-burst-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (op : AllOp) (initSt : NodeState Γ) (b : Closed Γ (obs u))
  (κ : Path Γ u t) (bid : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let nid = proj₁ (mintNode sched)
      r   = subscribeE g0 b (thru-outer op nid ↠ κ) bid now
              (proj₂ (mintNode sched)) (installNode nid initSt st)
  in depthBurst g0 bid now (thru-outer op nid) κ
       (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
       ≤ depthCapN (suc (nestDᵉ (Sched.slots sched) b))
                   (maxInputᵉ b) κ sched
depth-all-burst-zero op initSt b κ bid now sched st =
  ≤-trans (burst-thru-zero bid now op nid κ
             (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
          (one-≤-capN (nestDᵉ (Sched.slots sched) b) (maxInputᵉ b) κ sched)
  where
  nid = proj₁ (mintNode sched)
  r   = subscribeE g0 b (thru-outer op nid ↠ κ) bid now
          (proj₂ (mintNode sched)) (installNode nid initSt st)

-- THE ARM AT POSITIVE GAS, and it is now a real body over ONE leaf.
-- Two things are spent here and neither is owed: `subscribeE-slots`,
-- which is PROVEN in .Keeps-Ring and moves the burst's own cap back to
-- the entry cap under a single `subst` — the cap reads a scheduler
-- through `Sched.slots` and nothing else, which is the dividend of its
-- having lost its node arm — and the clique above, which walks the burst
-- the subscribe returned.  What the leaf supplies is the one fact the
-- walk cannot derive: that what came out is no more deeply nested than
-- what emitted it.
depth-all-burst : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (fuel : Gas) (ih : DepthIH e fuel)
  (op : AllOp) (initSt : NodeState Γ) (b : Closed Γ (obs u))
  (κ : Path Γ u t) (bid : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let nid = proj₁ (mintNode sched)
      r   = subscribeE (gs fuel) b (thru-outer op nid ↠ κ) bid now
              (proj₂ (mintNode sched)) (installNode nid initSt st)
  in depthBurst (gs fuel) bid now (thru-outer op nid) κ
       (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
       ≤ depthCapN (suc (nestDᵉ (Sched.slots sched) b))
                   (maxInputᵉ b) κ sched
depth-all-burst fuel ih op initSt b κ bid now sched st =
  subst (λ sl → depthBurst (gs fuel) bid now (thru-outer op nid) κ
                  (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                  ≤ suc (nestDᵉ sl b) + pathNestD κ
                      + slotsNestBelow sl (maxInputᵉ b))
        (subscribeE-slots (gs fuel) b (thru-outer op nid ↠ κ) bid now
           (proj₂ (mintNode sched)) (installNode nid initSt st))
        reached
  where
  nid = proj₁ (mintNode sched)
  r   = subscribeE (gs fuel) b (thru-outer op nid ↠ κ) bid now
          (proj₂ (mintNode sched)) (installNode nid initSt st)
  sl′ = Sched.slots (proj₁ (proj₂ r))
  reached : depthBurst (gs fuel) bid now (thru-outer op nid) κ
              (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
            ≤ suc (nestDᵉ sl′ b) + pathNestD κ
                + slotsNestBelow sl′ (maxInputᵉ b)
  reached =
    ≤-trans (burst-nest fuel ih sl′ (innerNest sl′ b) op nid κ bid now
               (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) refl
               (emit-cap (gs fuel) b (thru-outer op nid ↠ κ) bid now
                  (proj₂ (mintNode sched)) (installNode nid initSt st)))
            (≤-reflexive (cap-shuffle (nestDᵉ sl′ b) (pathNestD κ)
                            (slotsNestBelow sl′ (maxInputᵉ b))))

-- NOTHING IS OWED FOR AN INSTALL ANY MORE, and the two lemmas that
-- used to pay for one are gone with the node arm.  `mintNode` leaves the
-- slots alone and the cap reads nothing else, so the IH comes back at a
-- cap that is the ENTRY cap definitionally — the take, scan and `*All`
-- clauses each dropped a `≤-trans` and a `refl` witnessing a node
-- weight.  RECOVERY: git show HEAD restores `setNode-nodesNestMax-0`
-- (a `setNode` induction over the hypothesis `nodeNestMax sl s ≡ 0`)
-- and `depthCap-install0`, should any measure ever read the store again.

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
map-size-arith : ∀ {n} {Γ : Ctx n} {t} {s u}
  (f : Fn Γ [] [] [] s u) (b : Closed Γ s)
  (κ : Path Γ u t) (sched : Sched Γ) →
  depthCap b (map-f f ↠ κ) sched ≤ depthCap (mapᵉ f b) κ sched
map-size-arith {n = n} f b κ sched =
  +-mono-≤ (+-mono-≤ (m≤n+m (nestDᵉ (Sched.slots sched) b)
                            (nestDᵗ (Sched.slots sched) f))
                     ≤-refl)
           (slotsNestBelow-mono (Sched.slots sched)
              (maxInputᵉ b) (maxInputᵉ (mapᵉ f b)) (m≤n⊔m _ _))

-- take adds NOTHING to the nesting, so this is the below-sum widening
-- alone
take-size-arith : ∀ {n} {Γ : Ctx n} {t} {u}
  (c : Tm Γ [] [] [] natᵗ) (b : Closed Γ u) (nid : NodeId)
  (κ : Path Γ u t) (sched : Sched Γ) →
  depthCap b (take-f nid ↠ κ) sched ≤ depthCap (takeᵉ c b) κ sched
take-size-arith {n = n} c b nid κ sched =
  +-mono-≤ (≤-refl {x = nestDᵉ (Sched.slots sched) b + pathNestD κ})
           (slotsNestBelow-mono (Sched.slots sched)
              (maxInputᵉ b) (maxInputᵉ (takeᵉ c b)) (m≤n⊔m _ _))

-- scan: the seed's nesting and the PRODUCT term both sit to the left of
-- the source's own nesting, so this is `m≤n+m` at a two-summand
-- constant.  The install is absorbed BEFORE this arithmetic runs —
-- `depthCap-install0` returns the IH's post-install cap to the entry
-- cap, so what is left here is the syntax payment alone.
scan-size-arith : ∀ {n} {Γ : Ctx n} {t} {s u}
  (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u) (b : Closed Γ s)
  (nid : NodeId) (κ : Path Γ u t) (sched : Sched Γ) →
  depthCap b (scan-f f nid ↠ κ) sched
    ≤ depthCap (scanᵉ f seed b) κ sched
scan-size-arith {n = n} f seed b nid κ sched =
  +-mono-≤ (+-mono-≤ (m≤n+m (nestDᵉ (Sched.slots sched) b) _) ≤-refl)
           (slotsNestBelow-mono (Sched.slots sched)
              (maxInputᵉ b) (maxInputᵉ (scanᵉ f seed b))
              (m≤n⊔m _ _))

-- THE `*All` ARM, and it serves all four operators from one statement:
-- `sizeᵉ`, `nestDᵉ` and `maxInputᵉ` treat `mergeAllᵉ`, `concatAllᵉ`,
-- `switchAllᵉ` and `exhaustAllᵉ` identically — `suc` on the first two,
-- unchanged on the third — so the four caps are one term and the
-- conclusion is written at `depthCapN` rather than at any constructor.
-- The minted scheduler is carried rather than discharged: `mintNode`
-- touches `nextNode` alone, so the cap at it IS the cap at `sched` and
-- the four clauses hand their IH straight in.  `≤-refl` on the below-sum
-- where the siblings need `slotsNestBelow-mono`: a `*All` layer adds no
-- input.
private
  all-outer-arith : ∀ {n} {Γ : Ctx n} {t} {u}
    (op : AllOp) (b : Closed Γ (obs u))
    (κ : Path Γ u t) (sched : Sched Γ) →
    depthCap b (thru-outer op (proj₁ (mintNode sched)) ↠ κ)
               (proj₂ (mintNode sched))
      ≤ depthCapN (suc (nestDᵉ (Sched.slots sched) b))
                  (maxInputᵉ b) κ sched
  all-outer-arith {n = n} op b κ sched =
    +-mono-≤ (arith-step (nestDᵉ (Sched.slots sched) b) (pathNestD κ) 0)
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
    depthE g b κ bid now sched st ≤ depthCap b κ sched

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
      (≤-trans slotPay (m≤n+m _ _))
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
      (map-size-arith f b κ sched)
    where r = subscribeE fuel b (map-f f ↠ κ) bid now sched st

  -- BUCKET (a)/(b): takeᵉ — zero arm trivial; suc arm uses take-f burst = 0
  depth-compositional-go fuel (takeᵉ c b) κ bid now sched st
    with evalTm c
  ... | zero  = z≤n
  ... | suc k =
    ≤-trans
      (⊔-lub
        (depth-compositional-go fuel b (take-f nid ↠ κ) bid now sched₁ st₀)
        (≤-trans (burst-takef-zero fuel bid now nid κ
                    (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
                 z≤n))
      (take-size-arith c b nid κ sched)
    where
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₀    = installNode nid (take-st (suc k)) st
    r      = subscribeE fuel b (take-f nid ↠ κ) bid now sched₁ st₀

  -- BUCKET (b): scanᵉ — burst(scan-f) = 0, and the IH comes back at the
  -- ENTRY cap by reduction: the cap reads the scheduler's slots and
  -- `mintNode` does not touch them, so installing the seed is invisible
  -- to it and this clause is the take clause with a different node.
  depth-compositional-go fuel (scanᵉ f seed b) κ bid now sched st =
    ≤-trans
      (⊔-lub
        (depth-compositional-go fuel b (scan-f f nid ↠ κ) bid now sched₁ st₀)
        (≤-trans (burst-scf-zero fuel bid now f nid κ
                    (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
                 z≤n))
      (scan-size-arith f seed b nid κ sched)
    where
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₀    = installNode nid (scan-st (evalTm seed)) st
    r      = subscribeE fuel b (scan-f f nid ↠ κ) bid now sched₁ st₀

  -- BUCKET (b)+(d): *All — the OUTER arm is this induction at `b`, the
  -- BURST arm is the one leaf left.  `suc (sizeᵉ b)` IS `sizeᵉ (*Allᵉ b)`
  -- definitionally, and so is the nesting `suc`, which is why one
  -- `all-outer-arith` covers four constructors.  The installed state is
  -- not an argument to that arithmetic at all: the cap reads the
  -- scheduler's slots, so the IH comes back at the ENTRY cap by
  -- reduction, exactly as take and scan do.
  depth-compositional-go g0 (mergeAllᵉ b) κ bid now sched st =
    ⊔-lub
      (≤-trans (depth-compositional-go g0 b
                  (thru-outer mergeᵒ nid ↠ κ) bid now sched₁ st₀)
               (all-outer-arith mergeᵒ b κ sched))
      (depth-all-burst-zero mergeᵒ (merge-st 0 false) b κ bid now sched st)
    where
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₀    = installNode nid (merge-st 0 false) st

  depth-compositional-go (gs fuel) (mergeAllᵉ b) κ bid now sched st =
    ⊔-lub
      (≤-trans (depth-compositional-go (gs fuel) b
                  (thru-outer mergeᵒ nid ↠ κ) bid now sched₁ st₀)
               (all-outer-arith mergeᵒ b κ sched))
      (depth-all-burst fuel
         (λ {w} c ν cid tick sch stt →
            depth-compositional-go {u = w} fuel c ν cid tick sch stt)
         mergeᵒ (merge-st 0 false) b κ bid now sched st)
    where
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₀    = installNode nid (merge-st 0 false) st

  depth-compositional-go {u = u} g0 (concatAllᵉ b) κ bid now sched st =
    ⊔-lub
      (≤-trans (depth-compositional-go g0 b
                  (thru-outer concatᵒ nid ↠ κ) bid now sched₁ st₀)
               (all-outer-arith concatᵒ b κ sched))
      (depth-all-burst-zero concatᵒ (concat-st {t = u} [] false false) b κ bid now sched st)
    where
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₀    = installNode nid (concat-st {t = u} [] false false) st

  depth-compositional-go {u = u} (gs fuel) (concatAllᵉ b) κ bid now sched st =
    ⊔-lub
      (≤-trans (depth-compositional-go (gs fuel) b
                  (thru-outer concatᵒ nid ↠ κ) bid now sched₁ st₀)
               (all-outer-arith concatᵒ b κ sched))
      (depth-all-burst fuel
         (λ {w} c ν cid tick sch stt →
            depth-compositional-go {u = w} fuel c ν cid tick sch stt)
         concatᵒ (concat-st {t = u} [] false false) b κ bid now sched st)
    where
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₀    = installNode nid (concat-st {t = u} [] false false) st

  depth-compositional-go g0 (switchAllᵉ b) κ bid now sched st =
    ⊔-lub
      (≤-trans (depth-compositional-go g0 b
                  (thru-outer switchᵒ nid ↠ κ) bid now sched₁ st₀)
               (all-outer-arith switchᵒ b κ sched))
      (depth-all-burst-zero switchᵒ (switch-st nothing false) b κ bid now sched st)
    where
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₀    = installNode nid (switch-st nothing false) st

  depth-compositional-go (gs fuel) (switchAllᵉ b) κ bid now sched st =
    ⊔-lub
      (≤-trans (depth-compositional-go (gs fuel) b
                  (thru-outer switchᵒ nid ↠ κ) bid now sched₁ st₀)
               (all-outer-arith switchᵒ b κ sched))
      (depth-all-burst fuel
         (λ {w} c ν cid tick sch stt →
            depth-compositional-go {u = w} fuel c ν cid tick sch stt)
         switchᵒ (switch-st nothing false) b κ bid now sched st)
    where
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₀    = installNode nid (switch-st nothing false) st

  depth-compositional-go g0 (exhaustAllᵉ b) κ bid now sched st =
    ⊔-lub
      (≤-trans (depth-compositional-go g0 b
                  (thru-outer exhaustᵒ nid ↠ κ) bid now sched₁ st₀)
               (all-outer-arith exhaustᵒ b κ sched))
      (depth-all-burst-zero exhaustᵒ (exhaust-st false false) b κ bid now sched st)
    where
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₀    = installNode nid (exhaust-st false false) st

  depth-compositional-go (gs fuel) (exhaustAllᵉ b) κ bid now sched st =
    ⊔-lub
      (≤-trans (depth-compositional-go (gs fuel) b
                  (thru-outer exhaustᵒ nid ↠ κ) bid now sched₁ st₀)
               (all-outer-arith exhaustᵒ b κ sched))
      (depth-all-burst fuel
         (λ {w} c ν cid tick sch stt →
            depth-compositional-go {u = w} fuel c ν cid tick sch stt)
         exhaustᵒ (exhaust-st false false) b κ bid now sched st)
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