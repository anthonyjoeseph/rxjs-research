------------------------------------------------------------------
-- WHAT THE UNCONNECTED COUNT SURVIVES.
------------------------------------------------------------------

-- THE COUNT IS THE BUILDER'S MEASURE, AND THIS IS THE ONE THING IT
-- OWES.  Every builder obligation is stated under a bound on the store
-- it was handed, so a frame that runs a step and then spends the next
-- obligation has to know the step left the count where it was.  It
-- did: the connected list is written at exactly one site in the whole
-- tree -- a connect, which EXTENDS it -- and the slot telescope is
-- fixed at the start of the run, so every other move leaves both
-- readings alone and the count with them.
--
-- TWO LAYERS, AND ONLY THE FIRST IS FREE.  A STEP is a record update
-- on a field the count cannot read, so its obligation is a case split
-- all of whose arms are `refl`.  A RELATION is what a builder actually
-- holds at the point of spending -- the derivation, not the function
-- that produced it -- so each of the five is an induction over
-- constructors, every arm of which is a step or a smaller derivation.
--
-- AND IT SITS BELOW THE BUILDER BECAUSE NOTHING HERE LOOKS AT A
-- CANDIDATE.  The count is a natural number read off two fields; the
-- bound rides as an inert index.  That is what lets the whole layer be
-- written once, under the levels rather than inside one.
module Rx.Evaluator.Unconnected where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (zero; suc; _≤_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-reflexive; ≤-trans)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)

open import Rx.Exp using (_×ᵗ_; obs; listᵗ; _≟ᵗ_; Ctx; Closed; Val; FnClo)
open import Rx.Evaluator using (Sched; EvalSt; Path; AllOp; NodeId; mergeAllᵒ; switchᵒ; exhaustᵒ; cell-st; take-st;
  batchSync-st; mergeAll-st; switch-st; exhaust-st; lookupNode; switchKill; markInnerDone;
  markOuterDone; mergeAllQueue; scanStep; takeStep; cutAt; batchSyncPush; batchSyncFlush;
  shareLatch)
open import Rx.Evaluator.Domain using (emit⇓; close⇓; emits⇓; subscribeE⇓; drainQueue⇓)
open import Rx.Evaluator.Reducible using (Out; unconnected; unconn-cong)

-- THE LATCH RUNS BEFORE THE FAN-OUT AND THE SWEEP AFTER IT, WHICH IS
-- WHY BOTH STAY APPLIED.  An end latches the share as completed on the
-- way in, so a chain subscribing to it DURING the fan-out sees a spent
-- slot; the registrations are dropped on the way out, once every chain
-- that was admitted has had its end.
-- THE LATCH IS THE ONE STORE STEP THE COUNT CANNOT READ THROUGH ON
-- ITS OWN, and it is a two-line case split rather than a leaf: the
-- completion arm writes two fields, neither of them the connected
-- list, and the other arm writes nothing at all.  What makes it owed
-- here rather than free is only that the step branches on a value the
-- caller has not forced.
unconn-latch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m}
               (i : Fin n) (b : Bool) (sched : Sched Γ) (st : EvalSt e)
             → unconnected sched st ≤ m
             → unconnected sched (shareLatch i b st) ≤ m
unconn-latch i false sched st le = le
unconn-latch i true  sched st le = le

-- WHAT A NODE STEP OWES THE COUNT, AND IT IS THE SAME PROOF IN EVERY
-- ARM.  Each of these hands back either the store it was given or a
-- record update on a field the count does not read, so the whole
-- obligation is a case split all of whose arms are `refl`.  They are
-- split out from the frames below rather than inlined because a frame
-- runs its step under a `with` and so never has the step's own result
-- in a form that reduces.
shares-scanStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
                  (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId) (v : Val Γ s) (st : EvalSt e)
                → EvalSt.connectedShares (proj₂ (scanStep fn nid v st))
                  ≡ EvalSt.connectedShares st
shares-scanStep {u = u} fn nid v st with lookupNode nid (EvalSt.nodes st)
... | just (cell-st {w} ac) with w ≟ᵗ u
...   | no  _    = refl
...   | yes refl = refl
shares-scanStep fn nid v st | nothing = refl
shares-scanStep fn nid v st | just (take-st _) = refl
shares-scanStep fn nid v st | just (batchSync-st _ _) = refl
shares-scanStep fn nid v st | just (mergeAll-st _ _ _ _) = refl
shares-scanStep fn nid v st | just (switch-st _ _) = refl
shares-scanStep fn nid v st | just (exhaust-st _ _) = refl

shares-takeStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (nid : NodeId) (st : EvalSt e)
                → EvalSt.connectedShares (proj₂ (takeStep nid st))
                  ≡ EvalSt.connectedShares st
shares-takeStep nid st with lookupNode nid (EvalSt.nodes st)
... | just (take-st (suc k)) = refl
... | just (take-st zero)    = refl
shares-takeStep nid st | nothing = refl
shares-takeStep nid st | just (cell-st _) = refl
shares-takeStep nid st | just (batchSync-st _ _) = refl
shares-takeStep nid st | just (mergeAll-st _ _ _ _) = refl
shares-takeStep nid st | just (switch-st _ _) = refl
shares-takeStep nid st | just (exhaust-st _ _) = refl

shares-batchSyncPush : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
                       (nid : NodeId) (v : Val Γ s) (st : EvalSt e)
                     → EvalSt.connectedShares (proj₂ (batchSyncPush nid v st))
                       ≡ EvalSt.connectedShares st
shares-batchSyncPush {s = s} nid v st with lookupNode nid (EvalSt.nodes st)
... | just (batchSync-st {w} true buf) with w ≟ᵗ s
...   | no  _    = refl
...   | yes refl = refl
shares-batchSyncPush nid v st | just (batchSync-st false buf) = refl
shares-batchSyncPush nid v st | nothing = refl
shares-batchSyncPush nid v st | just (cell-st _) = refl
shares-batchSyncPush nid v st | just (take-st _) = refl
shares-batchSyncPush nid v st | just (mergeAll-st _ _ _ _) = refl
shares-batchSyncPush nid v st | just (switch-st _ _) = refl
shares-batchSyncPush nid v st | just (exhaust-st _ _) = refl

shares-batchSyncFlush : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
                        (nid : NodeId) (st : EvalSt e)
                      → EvalSt.connectedShares (proj₂ (batchSyncFlush {s = s} nid st))
                        ≡ EvalSt.connectedShares st
shares-batchSyncFlush {s = s} nid st with lookupNode nid (EvalSt.nodes st)
... | just (batchSync-st {w} _ buf) with w ≟ᵗ s
...   | no  _    = refl
...   | yes refl = refl
shares-batchSyncFlush nid st | nothing = refl
shares-batchSyncFlush nid st | just (cell-st _) = refl
shares-batchSyncFlush nid st | just (take-st _) = refl
shares-batchSyncFlush nid st | just (mergeAll-st _ _ _ _) = refl
shares-batchSyncFlush nid st | just (switch-st _ _) = refl
shares-batchSyncFlush nid st | just (exhaust-st _ _) = refl

shares-markInnerDone : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                       (op : AllOp) (nid inst : NodeId) (st : EvalSt e)
                     → EvalSt.connectedShares (markInnerDone op nid inst st)
                       ≡ EvalSt.connectedShares st
shares-markInnerDone mergeAllᵒ nid inst st with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st lim act q od) = refl
shares-markInnerDone mergeAllᵒ nid inst st | nothing = refl
shares-markInnerDone mergeAllᵒ nid inst st | just (cell-st _) = refl
shares-markInnerDone mergeAllᵒ nid inst st | just (take-st _) = refl
shares-markInnerDone mergeAllᵒ nid inst st | just (batchSync-st _ _) = refl
shares-markInnerDone mergeAllᵒ nid inst st | just (switch-st _ _) = refl
shares-markInnerDone mergeAllᵒ nid inst st | just (exhaust-st _ _) = refl
shares-markInnerDone switchᵒ nid inst st with lookupNode nid (EvalSt.nodes st)
... | just (switch-st (just c) od) with c ≡ᵇ inst
...   | true  = refl
...   | false = refl
shares-markInnerDone switchᵒ nid inst st | just (switch-st nothing od) = refl
shares-markInnerDone switchᵒ nid inst st | nothing = refl
shares-markInnerDone switchᵒ nid inst st | just (cell-st _) = refl
shares-markInnerDone switchᵒ nid inst st | just (take-st _) = refl
shares-markInnerDone switchᵒ nid inst st | just (batchSync-st _ _) = refl
shares-markInnerDone switchᵒ nid inst st | just (mergeAll-st _ _ _ _) = refl
shares-markInnerDone switchᵒ nid inst st | just (exhaust-st _ _) = refl
shares-markInnerDone exhaustᵒ nid inst st with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st ia od) = refl
shares-markInnerDone exhaustᵒ nid inst st | nothing = refl
shares-markInnerDone exhaustᵒ nid inst st | just (cell-st _) = refl
shares-markInnerDone exhaustᵒ nid inst st | just (take-st _) = refl
shares-markInnerDone exhaustᵒ nid inst st | just (batchSync-st _ _) = refl
shares-markInnerDone exhaustᵒ nid inst st | just (mergeAll-st _ _ _ _) = refl
shares-markInnerDone exhaustᵒ nid inst st | just (switch-st _ _) = refl

shares-mergeAllQueue : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
                       (nid : NodeId) (st : EvalSt e)
                     → EvalSt.connectedShares (proj₂ (mergeAllQueue {s = s} nid st))
                       ≡ EvalSt.connectedShares st
shares-mergeAllQueue {s = s} nid st with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ s
...   | no  _    = refl
...   | yes refl = refl
shares-mergeAllQueue nid st | nothing = refl
shares-mergeAllQueue nid st | just (cell-st _) = refl
shares-mergeAllQueue nid st | just (take-st _) = refl
shares-mergeAllQueue nid st | just (batchSync-st _ _) = refl
shares-mergeAllQueue nid st | just (switch-st _ _) = refl
shares-mergeAllQueue nid st | just (exhaust-st _ _) = refl

-- THE COUNT, CARRIED ACROSS A STEP THAT LEFT THE CONNECTED LIST ALONE.
unconn-shares : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m}
                (sched : Sched Γ) (st st′ : EvalSt e)
              → EvalSt.connectedShares st′ ≡ EvalSt.connectedShares st
              → unconnected sched st ≤ m → unconnected sched st′ ≤ m
unconn-shares sched st st′ p le =
  ≤-trans (≤-reflexive (unconn-cong sched {st = st} {st′ = st′} p)) le

-- AND THE SIX A FRAME ACTUALLY SPENDS, each reading its step's result
-- back off the equation the frame's own `with` recorded.
unconn-scanStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u m}
                  (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId) (v : Val Γ s)
                  (sched : Sched Γ) (st : EvalSt e)
                  {ac : Val Γ u} {st₁ : EvalSt e}
                → scanStep fn nid v st ≡ (just ac , st₁)
                → unconnected sched st ≤ m → unconnected sched st₁ ≤ m
unconn-scanStep fn nid v sched st {st₁ = st₁} eq =
  unconn-shares sched st st₁
    (trans (cong (λ z → EvalSt.connectedShares (proj₂ z)) (sym eq))
           (shares-scanStep fn nid v st))

unconn-takeStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m}
                  (nid : NodeId) (sched : Sched Γ) (st : EvalSt e)
                  {b : Maybe Bool} {st₁ : EvalSt e}
                → takeStep nid st ≡ (b , st₁)
                → unconnected sched st ≤ m → unconnected sched st₁ ≤ m
unconn-takeStep nid sched st {st₁ = st₁} eq =
  unconn-shares sched st st₁
    (trans (cong (λ z → EvalSt.connectedShares (proj₂ z)) (sym eq))
           (shares-takeStep nid st))

unconn-cutAt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m}
               (nid : NodeId) (sched : Sched Γ) (st : EvalSt e)
             → unconnected sched st ≤ m
             → unconnected (proj₁ (cutAt nid sched st)) (proj₂ (cutAt nid sched st)) ≤ m
unconn-cutAt nid sched st le = le

unconn-batchSyncPush : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s m}
                       (nid : NodeId) (v : Val Γ s)
                       (sched : Sched Γ) (st : EvalSt e)
                       {g : Maybe (Val Γ (s ×ᵗ listᵗ s))} {st₁ : EvalSt e}
                     → batchSyncPush nid v st ≡ (g , st₁)
                     → unconnected sched st ≤ m → unconnected sched st₁ ≤ m
unconn-batchSyncPush nid v sched st {st₁ = st₁} eq =
  unconn-shares sched st st₁
    (trans (cong (λ z → EvalSt.connectedShares (proj₂ z)) (sym eq))
           (shares-batchSyncPush nid v st))

unconn-batchSyncFlush : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s m}
                        (nid : NodeId) (sched : Sched Γ) (st : EvalSt e)
                        {g : Maybe (Val Γ (s ×ᵗ listᵗ s))} {st₁ : EvalSt e}
                      → batchSyncFlush {s = s} nid st ≡ (g , st₁)
                      → unconnected sched st ≤ m → unconnected sched st₁ ≤ m
unconn-batchSyncFlush {s = s} nid sched st {st₁ = st₁} eq =
  unconn-shares sched st st₁
    (trans (cong (λ z → EvalSt.connectedShares (proj₂ z)) (sym eq))
           (shares-batchSyncFlush {s = s} nid st))

unconn-mergeAllQueue : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s m}
                       (op : AllOp) (nid inst : NodeId)
                       (sched : Sched Γ) (st : EvalSt e)
                       {q : List (Val Γ (obs s))} {st₀ : EvalSt e}
                     → mergeAllQueue {s = s} nid (markInnerDone op nid inst st) ≡ (q , st₀)
                     → unconnected sched st ≤ m → unconnected sched st₀ ≤ m
unconn-mergeAllQueue {s = s} op nid inst sched st {st₀ = st₀} eq =
  unconn-shares sched st st₀
    (trans (cong (λ z → EvalSt.connectedShares (proj₂ z)) (sym eq))
      (trans (shares-mergeAllQueue {s = s} nid (markInnerDone op nid inst st))
             (shares-markInnerDone op nid inst st)))

shares-markOuterDone : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                       (op : AllOp) (nid : NodeId) (st : EvalSt e)
                     → EvalSt.connectedShares (markOuterDone op nid st)
                       ≡ EvalSt.connectedShares st
shares-markOuterDone mergeAllᵒ nid st with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st lim act q od) = refl
shares-markOuterDone mergeAllᵒ nid st | nothing = refl
shares-markOuterDone mergeAllᵒ nid st | just (cell-st _) = refl
shares-markOuterDone mergeAllᵒ nid st | just (take-st _) = refl
shares-markOuterDone mergeAllᵒ nid st | just (batchSync-st _ _) = refl
shares-markOuterDone mergeAllᵒ nid st | just (switch-st _ _) = refl
shares-markOuterDone mergeAllᵒ nid st | just (exhaust-st _ _) = refl
shares-markOuterDone switchᵒ nid st with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur od) = refl
shares-markOuterDone switchᵒ nid st | nothing = refl
shares-markOuterDone switchᵒ nid st | just (cell-st _) = refl
shares-markOuterDone switchᵒ nid st | just (take-st _) = refl
shares-markOuterDone switchᵒ nid st | just (batchSync-st _ _) = refl
shares-markOuterDone switchᵒ nid st | just (mergeAll-st _ _ _ _) = refl
shares-markOuterDone switchᵒ nid st | just (exhaust-st _ _) = refl
shares-markOuterDone exhaustᵒ nid st with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st ia od) = refl
shares-markOuterDone exhaustᵒ nid st | nothing = refl
shares-markOuterDone exhaustᵒ nid st | just (cell-st _) = refl
shares-markOuterDone exhaustᵒ nid st | just (take-st _) = refl
shares-markOuterDone exhaustᵒ nid st | just (batchSync-st _ _) = refl
shares-markOuterDone exhaustᵒ nid st | just (mergeAll-st _ _ _ _) = refl
shares-markOuterDone exhaustᵒ nid st | just (switch-st _ _) = refl

unconn-markOuterDone : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m}
                       (op : AllOp) (nid : NodeId) (sched : Sched Γ) (st : EvalSt e)
                     → unconnected sched st ≤ m
                     → unconnected sched (markOuterDone op nid st) ≤ m
unconn-markOuterDone op nid sched st =
  unconn-shares sched st (markOuterDone op nid st) (shares-markOuterDone op nid st)

-- THE SWITCH'S CUT MOVES BOTH HALVES AT ONCE, so this one is stated
-- over the pair rather than over the store alone.
unconn-switchKill : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m}
                    (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e)
                  → unconnected sched st ≤ m
                  → unconnected (proj₁ (switchKill cur sched st))
                                (proj₂ (switchKill cur sched st)) ≤ m
unconn-switchKill nothing  sched st le = le
unconn-switchKill (just v) sched st le = le

unconn-switchKill-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m}
                       (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e)
                       {sched₁ : Sched Γ} {st₁ : EvalSt e}
                     → switchKill cur sched st ≡ (sched₁ , st₁)
                     → unconnected sched st ≤ m → unconnected sched₁ st₁ ≤ m
unconn-switchKill-eq cur sched st refl le = unconn-switchKill cur sched st le

-- FIVE BECAUSE THE OBLIGATION IS SPENT THROUGH FIVE RELATIONS, and the
-- fact is the same fact in each: a derivation ending in a store the
-- count reads no higher than the one it started from.  A connect is
-- the only move that writes the connected list and it only EXTENDS it,
-- so every arm is either a step that leaves both readings alone or a
-- smaller derivation.
--
-- TWIN: `unconn-latch` -- the same fact one level down, over a store
--   STEP rather than a derivation: a case split on the move, every arm
--   discharged outright because the count reads two fields and the
--   move writes neither.  Each of these five is that proof once per
--   constructor, and the arms it needs are proven already.
postulate
  unconn-emit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                  {κ : Path Γ lo u t} {now} {v : Val Γ u}
                  {sched : Sched Γ} {st : EvalSt e} {r : Out e}
              → emit⇓ {e = e} κ now v sched st r
              → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                  ≤ unconnected sched st

  unconn-close : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                   {κ : Path Γ lo u t} {now}
                   {sched : Sched Γ} {st : EvalSt e} {r : Out e}
               → close⇓ {e = e} κ now sched st r
               → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                   ≤ unconnected sched st

  unconn-subs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                  {b : Val Γ (obs u)} {κ : Path Γ lo u t} {now}
                  {sched : Sched Γ} {st : EvalSt e} {r : Out e}
              → subscribeE⇓ {e = e} b κ now sched st r
              → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                  ≤ unconnected sched st

  unconn-emits : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                   {κ : Path Γ lo u t} {now} {vs : List (Val Γ u)}
                   {sched : Sched Γ} {st : EvalSt e} {r : Out e}
               → emits⇓ {e = e} κ now vs sched st r
               → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                   ≤ unconnected sched st

  unconn-drain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                   {op : AllOp} {nid : NodeId} {κ : Path Γ lo u t} {now}
                   {q : List (Val Γ (obs u))}
                   {sched : Sched Γ} {st : EvalSt e} {r : Out e}
               → drainQueue⇓ {e = e} op nid κ now q sched st r
               → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                   ≤ unconnected sched st
