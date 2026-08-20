-- THE SCAN NODE'S SURVIVAL — the computable face of
-- `subscribeE-nodes-below` (.Node-Fresh), instantiated at the consumer that
-- commissioned it.  These rows were written against a conjunct of
-- `walk-scan-source-frame`; that postulate has since been split, its node
-- half discharged from the .Node-Fresh leaf, and the rows retargeted at the
-- leaf without changing a line — they were always testing this fact.
--
-- MODULE_ROOT (see scripts/check-wiring.py): not imported by Main, not
-- compiled; checked by `make bug-cache`.  The receipt lives in that
-- postulate's own header.
--
-- WHAT IS BEING TESTED.  The fact says that subscribing a scan's SOURCE
-- under `scan-f f nid ↠ κ` leaves node `nid` holding exactly the seed it was
-- installed with:
--
--     lookupNode nid (nodes (proj₂ (proj₂ (subscribeE g b (scan-f f nid ↠ κ)
--                       bid now sched₁ (installNode nid (scan-st (evalTm z)) st)))))
--       ≡ just (scan-st (evalTm z))
--
-- Every symbol in that is a real evaluator function, so at concrete `b` it
-- COMPUTES, and each row below either refutes the conjunct or is a receipt at
-- that shape.  Note which SIDE is being tested: the postulate's twenty-odd
-- caps/level hypotheses are NOT discharged here — the conclusion is probed at
-- reachable states and the hypotheses are simply not needed to evaluate it,
-- which is the point of probing a conclusion.
--
-- THE STATE IS REACHED, NOT BUILT.  `sched`/`st` are the initial pair the
-- top-level subscribe of `scanᵉ f z b` actually starts in, and `nid`/`sched₁`
-- come from `mintNode` — so every row instantiates the evaluator's own scan
-- clause (Evaluator:1453) verbatim rather than a state written by hand.
--
-- EVERY ROW IS LABELLED, and the calibration row is what makes the rest
-- load-bearing: `b := emptyᵉ` mints nothing and writes nothing, so it could
-- not have failed.  A row is LOAD-BEARING when subscribing `b` itself writes
-- the node table — which is what the `nodeCount` pins beside each row
-- establish, by naming how many nodes the source's subscribe leaves behind.
-- A row whose count is 1 has only the scan's own node and tests nothing about
-- interference; the ones that matter are the counts above 1.
module Verify-Budget-Sufficient.Scan-Node-Probe where

open import Data.Bool using (Bool; true; false)
open import Data.Nat  using (ℕ; zero; suc; _≤ᵇ_)
open import Data.List using (List; []; _∷_; length)
open import Data.Fin  using (Fin; zero; suc)
open import Data.Vec  using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Product using (proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Unit using (tt)
open import Rx.Exp using (Ctx; Closed; Tm; Fn; natᵗ; _×ᵗ_;
                          input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                          mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          nat̂; primᵗ; pairᵗ; fstᵗ; sndᵗ; strmᵗ; varᵗ;
                          add; evalTm)
open import Rx.Evaluator using (subscribeE; sched-init; st-init; budgetAt;
                                Slots; Sched; EvalSt; NodeId; NodeState;
                                Path; root; scan-f; scan-st; _↠_;
                                Slot; shared; mintNode; installNode; lookupNode)

------------------------------------------------------------------
-- The fixed shell: an empty context, so `Slots` is the empty function
-- and no `input` leaf can appear in any program below.
------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

-- the QuickCheck's own accumulator function and seed
ADD : Fn Γ₀ [] [] [] (natᵗ ×ᵗ natᵗ) natᵗ
ADD = primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))

SEED : Tm Γ₀ [] [] [] natᵗ
SEED = nat̂ 7

------------------------------------------------------------------
-- The runner: the evaluator's scan clause, opened up.  `PROG b` is the
-- whole program, so `budgetAt`, `sched-init` and `st-init` are read off
-- the same term the walk face is stated about.
------------------------------------------------------------------

PROG : Closed Γ₀ natᵗ → Closed Γ₀ natᵗ
PROG b = scanᵉ ADD SEED b

NID : Closed Γ₀ natᵗ → NodeId
NID b = proj₁ (mintNode (sched-init (PROG b) ins₀))

SCH₁ : Closed Γ₀ natᵗ → Sched Γ₀
SCH₁ b = proj₂ (mintNode (sched-init (PROG b) ins₀))

-- the SOURCE subscribe, exactly as Evaluator:1453 writes it
SRC : (b : Closed Γ₀ natᵗ) → EvalSt (PROG b)
SRC b =
  proj₂ (proj₂ (subscribeE (budgetAt (PROG b) ins₀ 0) b
                  (scan-f ADD (NID b) ↠ root) 0 0 (SCH₁ b)
                  (installNode (NID b) (scan-st (evalTm SEED)) (st-init (PROG b)))))

-- THE CONJUNCT ITSELF
KEPT : Closed Γ₀ natᵗ → Set
KEPT b = lookupNode (NID b) (EvalSt.nodes (SRC b)) ≡ just (scan-st {t = natᵗ} (evalTm SEED))

-- DID THE SOURCE'S SUBSCRIBE TOUCH THE NODE TABLE AT ALL?  `true` means it
-- left more behind than the scan's own installed node, so a subscribe that
-- wrote a node it had not minted would have had the chance to.  Stated as a
-- threshold rather than a count on purpose: the exact number is an artifact of
-- the program, the threshold is the non-degeneracy claim.
MINTED? : Closed Γ₀ natᵗ → Bool
MINTED? b = 2 ≤ᵇ length (EvalSt.nodes (SRC b))

------------------------------------------------------------------
-- § 1  CALIBRATION — could not have failed, and says so.
------------------------------------------------------------------

-- emptyᵉ closes at once: nothing is minted, nothing is written.
_ : MINTED? emptyᵉ ≡ false
_ = refl
_ : KEPT emptyᵉ
_ = refl

-- ofᵉ emits synchronously but the burst is RETURNED, not pushed, so the
-- node table is still the scan's own singleton.  DEGENERATE for the same
-- reason as the row above.
_ : MINTED? (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ [])) ≡ false
_ = refl
_ : KEPT (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ []))
_ = refl

------------------------------------------------------------------
-- § 2  LOAD-BEARING — the source's own subscribe mints and writes nodes,
-- so a subscribe that touched a node it did not mint would show here.
------------------------------------------------------------------

-- a NESTED SCAN: the source installs a second scan node and pushes its
-- source's burst through its OWN scan-f frame, which is the one write in
-- the evaluator that a `scan-st` can suffer.  The outer node must not be
-- the one that moves.
NESTED : Closed Γ₀ natᵗ
NESTED = scanᵉ ADD (nat̂ 3) (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ []))

_ : MINTED? NESTED ≡ true
_ = refl
_ : KEPT NESTED
_ = refl

-- a take under a scan: `take-st` counts down as values pass, so the
-- source subscribe demonstrably WRITES a node during the subscribe.
COUNTED : Closed Γ₀ natᵗ
COUNTED = takeᵉ (nat̂ 2) (scanᵉ ADD (nat̂ 3) (ofᵉ (nat̂ 4 ∷ nat̂ 5 ∷ nat̂ 6 ∷ [])))

_ : MINTED? COUNTED ≡ true
_ = refl
_ : KEPT COUNTED
_ = refl

-- the *All operators: a subscribeAll mints its own node and then drives
-- inner subscriptions, which is the deepest the source's subscribe goes.
MERGED : Closed Γ₀ natᵗ
MERGED = mergeAllᵉ (ofᵉ (strmᵗ (scanᵉ ADD (nat̂ 1) (ofᵉ (nat̂ 2 ∷ []))) ∷
                         strmᵗ (ofᵉ (nat̂ 9 ∷ [])) ∷ []))

_ : MINTED? MERGED ≡ true
_ = refl
_ : KEPT MERGED
_ = refl

CONCATTED : Closed Γ₀ natᵗ
CONCATTED = concatAllᵉ (ofᵉ (strmᵗ (scanᵉ ADD (nat̂ 1) (ofᵉ (nat̂ 2 ∷ nat̂ 4 ∷ []))) ∷
                             strmᵗ (takeᵉ (nat̂ 1) (ofᵉ (nat̂ 9 ∷ []))) ∷ []))

_ : MINTED? CONCATTED ≡ true
_ = refl
_ : KEPT CONCATTED
_ = refl

SWITCHED : Closed Γ₀ natᵗ
SWITCHED = switchAllᵉ (ofᵉ (strmᵗ (scanᵉ ADD (nat̂ 1) (ofᵉ (nat̂ 2 ∷ []))) ∷
                            strmᵗ (scanᵉ ADD (nat̂ 5) (ofᵉ (nat̂ 3 ∷ []))) ∷ []))

_ : MINTED? SWITCHED ≡ true
_ = refl
_ : KEPT SWITCHED
_ = refl

EXHAUSTED : Closed Γ₀ natᵗ
EXHAUSTED = exhaustAllᵉ (ofᵉ (strmᵗ (mapᵉ (varᵗ (here refl)) (ofᵉ (nat̂ 2 ∷ []))) ∷
                              strmᵗ (scanᵉ ADD (nat̂ 5) (ofᵉ (nat̂ 3 ∷ []))) ∷ []))

_ : MINTED? EXHAUSTED ≡ true
_ = refl
_ : KEPT EXHAUSTED
_ = refl

------------------------------------------------------------------
-- § 3  THE SHARE BOUNDARY — the one region §§ 1-2 cannot reach.
--
-- Everything above runs in the EMPTY context, so no program there has an
-- `input` leaf, no path ends in `share-sink`, and no delivery to a
-- second registered chain ever happens.  That matters, because a share
-- CONNECT is the only place a subscribe drives a source whose values fan
-- out to chains it did not itself create — and those chains carry frames
-- of nodes minted long before, which is the one way a subscribe could
-- write a node it did not mint.
--
-- So this section runs the same conjunct over a context with a SHARED
-- slot, with `b` subscribing that slot twice: the second subscription
-- finds the share already connected, and the first is what connects it.
------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

DEF : Closed Γ₁ natᵗ
DEF = ofᵉ (nat̂ 5 ∷ nat̂ 6 ∷ [])

ins₁ : Slots Γ₁
ins₁ zero = shared DEF {ok = tt}

ADD₁ : Fn Γ₁ [] [] [] (natᵗ ×ᵗ natᵗ) natᵗ
ADD₁ = primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))

SEED₁ : Tm Γ₁ [] [] [] natᵗ
SEED₁ = nat̂ 7

PROG₁ : Closed Γ₁ natᵗ → Closed Γ₁ natᵗ
PROG₁ b = scanᵉ ADD₁ SEED₁ b

NID₁ : Closed Γ₁ natᵗ → NodeId
NID₁ b = proj₁ (mintNode (sched-init (PROG₁ b) ins₁))

SCH₁′ : Closed Γ₁ natᵗ → Sched Γ₁
SCH₁′ b = proj₂ (mintNode (sched-init (PROG₁ b) ins₁))

SRC₁ : (b : Closed Γ₁ natᵗ) → EvalSt (PROG₁ b)
SRC₁ b =
  proj₂ (proj₂ (subscribeE (budgetAt (PROG₁ b) ins₁ 0) b
                  (scan-f ADD₁ (NID₁ b) ↠ root) 0 0 (SCH₁′ b)
                  (installNode (NID₁ b) (scan-st (evalTm SEED₁)) (st-init (PROG₁ b)))))

MINTED?₁ : Closed Γ₁ natᵗ → Bool
MINTED?₁ b = 2 ≤ᵇ length (EvalSt.nodes (SRC₁ b))

KEPT₁ : Closed Γ₁ natᵗ → Set
KEPT₁ b = lookupNode (NID₁ b) (EvalSt.nodes (SRC₁ b))
            ≡ just (scan-st {t = natᵗ} (evalTm SEED₁))

-- did the share actually connect during this subscribe?  `true` is what
-- makes the row load-bearing: an unconnected share delivers nothing and
-- the row would be testing §1 again.
CONNECTED? : Closed Γ₁ natᵗ → Bool
CONNECTED? b = 1 ≤ᵇ length (EvalSt.connectedShares (SRC₁ b))

-- TWO SUBSCRIBERS ON ONE SHARED SLOT, one of them behind its own scan
-- node: the merge subscribes both inners in the same frame, so the second
-- finds the slot connected and the first's connect drives DEF through a
-- chain the second registered.
FANOUT : Closed Γ₁ natᵗ
FANOUT = mergeAllᵉ (ofᵉ (strmᵗ (scanᵉ ADD₁ (nat̂ 1) (input zero)) ∷
                         strmᵗ (input zero) ∷ []))

_ : CONNECTED? FANOUT ≡ true
_ = refl
_ : MINTED?₁ FANOUT ≡ true
_ = refl
_ : KEPT₁ FANOUT
_ = refl

-- the same fan-out with the two subscribers in a CONCAT, so the second
-- registration happens in a later instant than the connect
FANOUT-SEQ : Closed Γ₁ natᵗ
FANOUT-SEQ = concatAllᵉ (ofᵉ (strmᵗ (input zero) ∷
                              strmᵗ (scanᵉ ADD₁ (nat̂ 1) (input zero)) ∷ []))

_ : CONNECTED? FANOUT-SEQ ≡ true
_ = refl
_ : MINTED?₁ FANOUT-SEQ ≡ true
_ = refl
_ : KEPT₁ FANOUT-SEQ
_ = refl

-- a bare shared input as the source: the connect happens with the outer
-- scan node already installed and the outer chain already the only sink.
BARE : Closed Γ₁ natᵗ
BARE = input zero

_ : CONNECTED? BARE ≡ true
_ = refl
_ : KEPT₁ BARE
_ = refl
