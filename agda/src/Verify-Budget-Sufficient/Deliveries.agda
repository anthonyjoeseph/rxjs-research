-- STRATUM 0 of Verify-Budget-Sufficient: THE DELIVERY LEDGER.
--
-- Where `EvalSt.delivered` moves, and where it provably does not.  The
-- evaluator conses onto that field at exactly TWO sites in the whole
-- machine — shareGo's uncancelled clause and cascadeGo's — and every
-- other function that threads a state either returns the field
-- untouched or is a composition of ones that do.  This module proves
-- that, function by function, over the entire stepFrame clique, and
-- then characterises the two consing walks as monotone EXTENSIONS of
-- the ledger they were handed.
--
-- WHY IT EXISTS.  `delivN st st′ = length (delivered st′) ∸ length
-- (delivered st)` is the currency both cascade conjuncts are stated in
-- (cascadeGo-level's D and cascadeGo-deliveries' bound).  A subtraction
-- of lengths composes only if the ledger GROWS — otherwise
-- `delivN st st″` and `delivN st st′ + delivN st′ st″` are unrelated
-- numbers.  Growth is exactly what is established here, so the delivery
-- recurrence
--
--     D(cascadeGo)     = Σ over uncancelled chains of (1 + Dfp n)
--     Dfp g root       = 0
--     Dfp g (f ↠ p)    = Dfp g p            -- stepFrame delivers nothing
--     Dfp g (sink i)   = Dds g
--     Dds 0            = 0
--     Dds (suc g)      = Σ over shareAdmit i (registry AS OF NOW) of (1 + Dfp g)
--
-- becomes a set of PROVEN equations (§ D) rather than a reading of the
-- source.  The `↠` line is the one that needed the grind: it is an
-- equality and not an inequality precisely because the whole stepFrame
-- clique preserves the field, and that clique is fifteen mutually
-- recursive functions.  § E closes the level above: `cascadeLatch`
-- CLEARS the ledger (the one write that is not a cons), which is why
-- every count here is read between a latch and the next one, and why
-- one cascade's D is a plain length rather than a difference.
--
-- It imports Rx.Evaluator and the standard library and NOTHING else —
-- no Caps, no measure, no invariant — so it sits under every stratum
-- and an edit here cannot invalidate a bound.  .Caps-Face re-exports it
-- (delivN is stated here and read there).
module Verify-Budget-Sufficient.Deliveries where

open import Data.Bool    using (Bool; true; false; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_)
open import Data.Nat.Properties using (m+n∸n≡m; n∸n≡0; +-suc; +-comm)
open import Data.List    using (List; []; _∷_; _++_; length)
open import Data.Bool.ListAction using (any)
open import Data.List.Properties using (++-assoc; length-++)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Fin     using (Fin; toℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec     using (lookup)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Rx.Prim      using (Tick; Id; Source; InstEmit; InstEvent; close; exhausted; Gas; g0; gs; hot; cold)
open import Rx.Exp       using (Ctx; Closed; Val; _≟ᵗ_; obs; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; concatAllᵉ;
  switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; evalTm; unfoldμ)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; RegId; NodeId; NodeState; scan-st; take-st; merge-st; concat-st;
  switch-st; exhaust-st; lookupNode; installNode; register; mintNode; root; share-sink; _↠_;
  Path; Frame; AllOp; map-f; scan-f; take-f; from-inner; thru-outer; mergeᵒ; concatᵒ; switchᵒ;
  exhaustᵒ; Stream; splitEvents; memberSource; burstCompleted; aliveThroughᶠ; takeVals;
  takeDispatch; switchKill; thruConsume; thruWalk; thruWrap; concatDrain; innerFinish;
  innerReact; stepFrame; pushBurst; subscribeAll; subscribeE; subscribeInner; sharedConnect;
  subscribeSharedSlot; shareLatch; shareAdmit; shareFinish; foldPath; dispatchShare; shareGo;
  chainStep; cascadeGo; budgetAt; arrTy; arrTick; arrSource; arrVal)
open import Rx.Slots using (scripted; shared)

------------------------------------------------------------------
-- § A.  THE LEDGER ORDER AND ITS ARITHMETIC.
--
-- `st ⊑ᵈ st′` says st′'s delivery ledger is st's with a block of new
-- ids in front — which is the only shape the evaluator ever produces,
-- since `delivered` is written by `rid ∷_` and by nothing else inside a
-- cascade (cascadeLatch's reset opens a cascade; it is not part of one).
-- Everything downstream counts with `delivN` and never with the witness
-- list, so the composition laws are stated at the ℕ level.
------------------------------------------------------------------

infix 4 _⊑ᵈ_

-- A DATA type, not a Σ: the two states are PARAMETERS, so a witness
-- determines them.  Stated as a Σ over `EvalSt.delivered` alone, the
-- states are only ever mentioned under a projection and Agda cannot
-- invert one, so every composition would leave the middle state a
-- blocked meta.
data _⊑ᵈ_ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (st st′ : EvalSt e) : Set where
  ext : (ds : List RegId) →
        EvalSt.delivered st′ ≡ ds ++ EvalSt.delivered st → st ⊑ᵈ st′

-- the deliveries a call makes, off the evaluator's own ledger.  Stated
-- here rather than in the caps face because it is the ledger's measure,
-- not a cap
delivN : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → EvalSt e → EvalSt e → ℕ
delivN st st′ = length (EvalSt.delivered st′) ∸ length (EvalSt.delivered st)

-- the cons site, named: what shareGo and cascadeGo write
consᵈ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → RegId → EvalSt e → EvalSt e
consᵈ rid st = record st { delivered = rid ∷ EvalSt.delivered st }

abstract

  ⊑ᵈ-refl : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (st : EvalSt e) → st ⊑ᵈ st
  ⊑ᵈ-refl st = ext [] refl

  -- st′ is EXPLICIT: it is the middle state at every composition site,
  -- and a preservation equation mentions it only under `delivered`
  ⊑ᵈ-of-≡ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (st st′ : EvalSt e) →
    EvalSt.delivered st′ ≡ EvalSt.delivered st → st ⊑ᵈ st′
  ⊑ᵈ-of-≡ st st′ h = ext [] h

  ⊑ᵈ-trans : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {st st′ st″ : EvalSt e} →
    st ⊑ᵈ st′ → st′ ⊑ᵈ st″ → st ⊑ᵈ st″
  ⊑ᵈ-trans {st = st} (ext ds p) (ext es q) =
    ext (es ++ ds)
      (trans q (trans (cong (es ++_) p) (sym (++-assoc es ds (EvalSt.delivered st)))))

  ⊑ᵈ-cons : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (rid : RegId) (st : EvalSt e) →
    st ⊑ᵈ consᵈ rid st
  ⊑ᵈ-cons rid st = ext (rid ∷ []) refl

  -- the ledger measure of an extension IS the block's length
  delivN-ext : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (st st′ : EvalSt e) (ds : List RegId) →
    EvalSt.delivered st′ ≡ ds ++ EvalSt.delivered st → delivN st st′ ≡ length ds
  delivN-ext st st′ ds p =
    trans (cong (λ l → length l ∸ length (EvalSt.delivered st)) p)
          (trans (cong (_∸ length (EvalSt.delivered st)) (length-++ ds))
                 (m+n∸n≡m (length ds) (length (EvalSt.delivered st))))

  -- a preserving call contributes nothing
  delivN-≡ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (st st′ : EvalSt e) →
    EvalSt.delivered st′ ≡ EvalSt.delivered st → delivN st st′ ≡ 0
  delivN-≡ st st′ h =
    trans (cong (λ l → length l ∸ length (EvalSt.delivered st)) h)
          (n∸n≡0 (length (EvalSt.delivered st)))

  -- THE COMPOSITION LAW.  Two calls in sequence add their ledgers —
  -- true only because both are extensions, which is what § B and § C
  -- establish
  delivN-split : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {st st′ st″ : EvalSt e} →
    st ⊑ᵈ st′ → st′ ⊑ᵈ st″ → delivN st st″ ≡ delivN st st′ + delivN st′ st″
  delivN-split {st = st} {st′ = st′} {st″ = st″} (ext ds p) (ext es q) =
    trans (delivN-ext st st″ (es ++ ds)
            (trans q (trans (cong (es ++_) p)
                            (sym (++-assoc es ds (EvalSt.delivered st))))))
      (trans (length-++ es)
        (trans (+-comm (length es) (length ds))
          (cong₂ _+_ (sym (delivN-ext st st′ ds p))
                     (sym (delivN-ext st′ st″ es q)))))

  -- THE CONS LAW.  A delivery in front of an extension is one more
  -- delivery: this is the `1 +` in `Σ over chains of (1 + Dfp)`
  delivN-cons : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (rid : RegId) (st st′ : EvalSt e) → consᵈ rid st ⊑ᵈ st′ →
    delivN st st′ ≡ suc (delivN (consᵈ rid st) st′)
  delivN-cons rid st st′ (ext ds p) =
    trans (cong (λ l → length l ∸ length (EvalSt.delivered st)) p)
      (trans (cong (_∸ length (EvalSt.delivered st))
                   (trans (length-++ ds)
                          (+-suc (length ds) (length (EvalSt.delivered st)))))
        (trans (m+n∸n≡m (suc (length ds)) (length (EvalSt.delivered st)))
               (cong suc (sym (delivN-ext (consᵈ rid st) st′ ds p)))))

------------------------------------------------------------------
-- § B.  THE stepFrame CLIQUE PRESERVES THE LEDGER.
--
-- Fifteen mutually recursive functions, one lemma each, all with the
-- same conclusion: the output state's `delivered` IS the input's.  The
-- proofs are congruence and nothing else — every clause either returns
-- its input state, returns a record update on a field other than
-- `delivered` (which reduces), or composes sub-calls.  The clause
-- structure mirrors the evaluator's exactly, including the catch-alls,
-- because a catch-all does not reduce under a variable pattern.
--
-- THE CONTENT IS THE ABSENCE: no clause here conses.  That is what
-- makes `Dfp g (f ↠ p) = Dfp g p` an equality.
------------------------------------------------------------------

abstract

  -- forward declarations: the clique, in the evaluator's own order
  subscribeE-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    EvalSt.delivered (proj₂ (proj₂ (subscribeE g b κ id now sched st)))
      ≡ EvalSt.delivered st

  subscribeInner-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (op : AllOp) (allNid : NodeId) (κ : Path Γ u t)
    (id : Id) (now : Tick) (o : Val Γ (obs u))
    (sched : Sched Γ) (st : EvalSt e) →
    EvalSt.delivered
      (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
        (subscribeInner g op allNid κ id now o sched st))))))
      ≡ EvalSt.delivered st

  sharedConnect-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    EvalSt.delivered (proj₂ (proj₂ (sharedConnect g i d κ id now sched st)))
      ≡ EvalSt.delivered st

  sharedSlot-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    EvalSt.delivered
      (proj₂ (proj₂ (subscribeSharedSlot g i d κ id now sched st)))
      ≡ EvalSt.delivered st

  thruConsume-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
    (id : Id) (now : Tick) (o : Val Γ (obs u))
    (sched : Sched Γ) (st : EvalSt e) →
    EvalSt.delivered
      (proj₂ (proj₂ (proj₂ (thruConsume g op nid κ id now o sched st))))
      ≡ EvalSt.delivered st

  thruWalk-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
    (id : Id) (now : Tick) (vals : List (Val Γ (obs u)))
    (sched : Sched Γ) (st : EvalSt e) →
    EvalSt.delivered
      (proj₂ (proj₂ (proj₂ (thruWalk g op nid κ id now vals sched st))))
      ≡ EvalSt.delivered st

  concatDrain-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (g : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
    (q : List (Closed Γ s)) (sched : Sched Γ) (st : EvalSt e) →
    EvalSt.delivered
      (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
        (concatDrain g allNid κ id now q sched st))))))
      ≡ EvalSt.delivered st

  innerFinish-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (g : Gas) (op : AllOp) (allNid inst : NodeId) (κ : Path Γ s t)
    (id : Id) (now : Tick) (vals : List (Val Γ s))
    (sched : Sched Γ) (st : EvalSt e) (ns : Maybe (NodeState Γ)) →
    EvalSt.delivered
      (proj₂ (proj₂ (proj₂ (proj₂
        (innerFinish g op allNid inst κ id now vals sched st ns)))))
      ≡ EvalSt.delivered st

  innerReact-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (g : Gas) (op : AllOp) (allNid inst : NodeId) (κ : Path Γ s t)
    (id : Id) (now : Tick) (vals : List (Val Γ s))
    (sched : Sched Γ) (st : EvalSt e) (fin : Bool) →
    EvalSt.delivered
      (proj₂ (proj₂ (proj₂ (proj₂
        (innerReact g op allNid inst κ id now vals sched st fin)))))
      ≡ EvalSt.delivered st

  stepFrame-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (g : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    EvalSt.delivered
      (proj₂ (proj₂ (proj₂ (proj₂
        (stepFrame g id now f κ vals fin sched st)))))
      ≡ EvalSt.delivered st

  pushBurst-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (g : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t)
    (str : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
    EvalSt.delivered (proj₂ (proj₂ (pushBurst g id now f κ str sched st)))
      ≡ EvalSt.delivered st

  subscribeAll-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (op : AllOp) (ns : NodeState Γ) (b : Closed Γ (obs u))
    (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    EvalSt.delivered
      (proj₂ (proj₂ (subscribeAll g op ns b κ id now sched st)))
      ≡ EvalSt.delivered st

  ----------------------------------------------------------------
  -- the two leaves: no re-entry, only a registry/node rewrite
  ----------------------------------------------------------------

  takeDispatch-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (ns : Maybe (NodeState Γ)) →
    EvalSt.delivered
      (proj₂ (proj₂ (proj₂ (proj₂
        (takeDispatch {t = t} nid vals fin sched st ns)))))
      ≡ EvalSt.delivered st
  takeDispatch-deliv nid vals fin sched st (just (take-st k))
    with proj₂ (proj₂ (takeVals k vals))
  ... | true  = refl
  ... | false = refl
  takeDispatch-deliv nid vals fin sched st nothing                = refl
  takeDispatch-deliv nid vals fin sched st (just (scan-st _))     = refl
  takeDispatch-deliv nid vals fin sched st (just (flatten-st _ _ _ _))  = refl
  takeDispatch-deliv nid vals fin sched st (just (switch-st _ _)) = refl
  takeDispatch-deliv nid vals fin sched st (just (exhaust-st _ _)) = refl

  switchKill-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) →
    EvalSt.delivered (proj₂ (proj₂ (switchKill {t = t} cur sched st)))
      ≡ EvalSt.delivered st
  switchKill-deliv nothing  sched st = refl
  switchKill-deliv (just v) sched st = refl

  thruWrap-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (op : AllOp) (nid : NodeId) (fin : Bool)
    (vs : List (Val Γ u)) (bs : List (InstEvent (Val Γ t)))
    (sched : Sched Γ) (st : EvalSt e) →
    EvalSt.delivered
      (proj₂ (proj₂ (proj₂ (proj₂ (thruWrap op nid fin (vs , bs , sched , st))))))
      ≡ EvalSt.delivered st
  thruWrap-deliv op nid false vs bs sched st = refl
  thruWrap-deliv mergeᵒ nid true vs bs sched st
    with lookupNode nid (EvalSt.nodes st)
  ... | just (merge-st k _)    = refl
  ... | nothing                = refl
  ... | just (scan-st _)       = refl
  ... | just (take-st _)       = refl
  ... | just (concat-st _ _ _) = refl
  ... | just (switch-st _ _)   = refl
  ... | just (exhaust-st _ _)  = refl
  thruWrap-deliv concatᵒ nid true vs bs sched st
    with lookupNode nid (EvalSt.nodes st)
  ... | just (concat-st q act _) = refl
  ... | nothing                = refl
  ... | just (scan-st _)       = refl
  ... | just (take-st _)       = refl
  ... | just (merge-st _ _)    = refl
  ... | just (switch-st _ _)   = refl
  ... | just (exhaust-st _ _)  = refl
  thruWrap-deliv switchᵒ nid true vs bs sched st
    with lookupNode nid (EvalSt.nodes st)
  ... | just (switch-st cur _) = refl
  ... | nothing                = refl
  ... | just (scan-st _)       = refl
  ... | just (take-st _)       = refl
  ... | just (flatten-st _ _ _ _)    = refl
  ... | just (exhaust-st _ _)  = refl
  thruWrap-deliv exhaustᵒ nid true vs bs sched st
    with lookupNode nid (EvalSt.nodes st)
  ... | just (exhaust-st act _) = refl
  ... | nothing                = refl
  ... | just (scan-st _)       = refl
  ... | just (take-st _)       = refl
  ... | just (flatten-st _ _ _ _)    = refl
  ... | just (switch-st _ _)   = refl

  ----------------------------------------------------------------
  -- the outer *All frame
  ----------------------------------------------------------------

  thruConsume-deliv g mergeᵒ nid κ id now o sched st =
    subscribeInner-deliv g mergeᵒ nid κ id now o sched st
  thruConsume-deliv {u = u} g concatᵒ nid κ id now o sched st
    with lookupNode nid (EvalSt.nodes st)
  ... | just (concat-st {w} q true od) with w ≟ᵗ u
  ...   | yes refl = refl
  ...   | no _     = refl
  thruConsume-deliv {u = u} g concatᵒ nid κ id now o sched st
      | just (concat-st q false od) =
    subscribeInner-deliv g concatᵒ nid κ id now o sched st
  thruConsume-deliv g concatᵒ nid κ id now o sched st | nothing = refl
  thruConsume-deliv g concatᵒ nid κ id now o sched st | just (scan-st _) = refl
  thruConsume-deliv g concatᵒ nid κ id now o sched st | just (take-st _) = refl
  thruConsume-deliv g concatᵒ nid κ id now o sched st | just (merge-st _ _) = refl
  thruConsume-deliv g concatᵒ nid κ id now o sched st | just (switch-st _ _) = refl
  thruConsume-deliv g concatᵒ nid κ id now o sched st | just (exhaust-st _ _) = refl
  thruConsume-deliv g switchᵒ nid κ id now o sched st
    with lookupNode nid (EvalSt.nodes st)
  ... | just (switch-st cur od) =
        trans (subscribeInner-deliv g switchᵒ nid κ id now o
                 (proj₁ (proj₂ (switchKill cur sched st)))
                 (proj₂ (proj₂ (switchKill cur sched st))))
              (switchKill-deliv cur sched st)
  ... | nothing                = refl
  ... | just (scan-st _)       = refl
  ... | just (take-st _)       = refl
  ... | just (flatten-st _ _ _ _)    = refl
  ... | just (exhaust-st _ _)  = refl
  thruConsume-deliv g exhaustᵒ nid κ id now o sched st
    with lookupNode nid (EvalSt.nodes st)
  ... | just (exhaust-st true od)  = refl
  ... | just (exhaust-st false od) =
        subscribeInner-deliv g exhaustᵒ nid κ id now o sched st
  ... | nothing                = refl
  ... | just (scan-st _)       = refl
  ... | just (take-st _)       = refl
  ... | just (flatten-st _ _ _ _)    = refl
  ... | just (switch-st _ _)   = refl

  thruWalk-deliv g op nid κ id now []       sched st = refl
  thruWalk-deliv g op nid κ id now (o ∷ os) sched st =
    let cr = thruConsume g op nid κ id now o sched st in
    trans (thruWalk-deliv g op nid κ id now os
             (proj₁ (proj₂ (proj₂ cr))) (proj₂ (proj₂ (proj₂ cr))))
          (thruConsume-deliv g op nid κ id now o sched st)

  ----------------------------------------------------------------
  -- the inner *All frame
  ----------------------------------------------------------------

  concatDrain-deliv g allNid κ id now []      sched st = refl
  concatDrain-deliv g allNid κ id now (o ∷ q) sched st
    with subscribeInner g concatᵒ allNid κ id now o sched st
       | subscribeInner-deliv g concatᵒ allNid κ id now o sched st
  ... | (_ , vs , bs , false , sched₁ , st₁) | si = si
  ... | (_ , vs , bs , true  , sched₁ , st₁) | si =
        trans (concatDrain-deliv g allNid κ id now q sched₁ st₁) si

  innerFinish-deliv g mergeᵒ allNid inst κ id now vals sched st
                    (just (merge-st k od)) = refl
  innerFinish-deliv {s = s} g concatᵒ allNid inst κ id now vals sched st
                    (just (concat-st {w} q act od)) with w ≟ᵗ s
  ... | yes refl = concatDrain-deliv g allNid κ id now q sched st
  ... | no _     = refl
  innerFinish-deliv g switchᵒ allNid inst κ id now vals sched st
                    (just (switch-st (just c) od))
    with _≡ᵇ_ c inst
  ... | true  = refl
  ... | false = refl
  innerFinish-deliv g exhaustᵒ allNid inst κ id now vals sched st
                    (just (exhaust-st act od)) = refl
  -- the catch-all, enumerated: a variable pattern would not reduce
  innerFinish-deliv g mergeᵒ allNid inst κ id now vals sched st nothing = refl
  innerFinish-deliv g mergeᵒ allNid inst κ id now vals sched st (just (scan-st _)) = refl
  innerFinish-deliv g mergeᵒ allNid inst κ id now vals sched st (just (take-st _)) = refl
  innerFinish-deliv g mergeᵒ allNid inst κ id now vals sched st (just (concat-st _ _ _)) = refl
  innerFinish-deliv g mergeᵒ allNid inst κ id now vals sched st (just (switch-st _ _)) = refl
  innerFinish-deliv g mergeᵒ allNid inst κ id now vals sched st (just (exhaust-st _ _)) = refl
  innerFinish-deliv g concatᵒ allNid inst κ id now vals sched st nothing = refl
  innerFinish-deliv g concatᵒ allNid inst κ id now vals sched st (just (scan-st _)) = refl
  innerFinish-deliv g concatᵒ allNid inst κ id now vals sched st (just (take-st _)) = refl
  innerFinish-deliv g concatᵒ allNid inst κ id now vals sched st (just (merge-st _ _)) = refl
  innerFinish-deliv g concatᵒ allNid inst κ id now vals sched st (just (switch-st _ _)) = refl
  innerFinish-deliv g concatᵒ allNid inst κ id now vals sched st (just (exhaust-st _ _)) = refl
  innerFinish-deliv g switchᵒ allNid inst κ id now vals sched st nothing = refl
  innerFinish-deliv g switchᵒ allNid inst κ id now vals sched st (just (scan-st _)) = refl
  innerFinish-deliv g switchᵒ allNid inst κ id now vals sched st (just (take-st _)) = refl
  innerFinish-deliv g switchᵒ allNid inst κ id now vals sched st (just (flatten-st _ _ _ _)) = refl
  innerFinish-deliv g switchᵒ allNid inst κ id now vals sched st (just (switch-st nothing _)) = refl
  innerFinish-deliv g switchᵒ allNid inst κ id now vals sched st (just (exhaust-st _ _)) = refl
  innerFinish-deliv g exhaustᵒ allNid inst κ id now vals sched st nothing = refl
  innerFinish-deliv g exhaustᵒ allNid inst κ id now vals sched st (just (scan-st _)) = refl
  innerFinish-deliv g exhaustᵒ allNid inst κ id now vals sched st (just (take-st _)) = refl
  innerFinish-deliv g exhaustᵒ allNid inst κ id now vals sched st (just (flatten-st _ _ _ _)) = refl
  innerFinish-deliv g exhaustᵒ allNid inst κ id now vals sched st (just (switch-st _ _)) = refl

  innerReact-deliv g op allNid inst κ id now vals sched st false = refl
  innerReact-deliv g op allNid inst κ id now vals sched st true
    with any (aliveThroughᶠ inst st) (EvalSt.registry st)
  ... | true  = refl
  ... | false = innerFinish-deliv g op allNid inst κ id now vals sched st
                  (lookupNode allNid (EvalSt.nodes st))

  ----------------------------------------------------------------
  -- the frame step and the burst push
  ----------------------------------------------------------------

  stepFrame-deliv g id now (map-f fn) κ vals fin sched st = refl
  stepFrame-deliv {u = u} g id now (scan-f fn nid) κ vals fin sched st
    with lookupNode nid (EvalSt.nodes st)
  ... | nothing                = refl
  ... | just (take-st _)       = refl
  ... | just (flatten-st _ _ _ _)    = refl
  ... | just (switch-st _ _)   = refl
  ... | just (exhaust-st _ _)  = refl
  ... | just (scan-st {w} ac) with w ≟ᵗ u
  ...   | yes refl = refl
  ...   | no _     = refl
  stepFrame-deliv g id now (take-f nid) κ vals fin sched st =
    takeDispatch-deliv nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
  stepFrame-deliv g id now (from-inner op allNid inst) κ vals fin sched st =
    innerReact-deliv g op allNid inst κ id now vals sched st fin
  stepFrame-deliv g id now (thru-outer op nid) κ vals fin sched st =
    let wk = thruWalk g op nid κ id now vals sched st in
    trans (thruWrap-deliv op nid fin (proj₁ wk) (proj₁ (proj₂ wk))
             (proj₁ (proj₂ (proj₂ wk))) (proj₂ (proj₂ (proj₂ wk))))
          (thruWalk-deliv g op nid κ id now vals sched st)

  pushBurst-deliv g id now f κ []         sched st = refl
  pushBurst-deliv {Γ = Γ} {t = t} {s = s} {u = u} g id now f κ (em ∷ ems) sched st =
    let sp = splitEvents {A = Val Γ u} (InstEmit.events em)
        r  = stepFrame g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st in
    trans (pushBurst-deliv g id now f κ ems
             (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r)))))
          (stepFrame-deliv g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st)

  ----------------------------------------------------------------
  -- the subscription walk
  ----------------------------------------------------------------

  subscribeAll-deliv g op ns b κ id now sched st =
    let sE = subscribeE g b (thru-outer op (proj₁ (mintNode sched)) ↠ κ) id now
               (proj₂ (mintNode sched)) (installNode (proj₁ (mintNode sched)) ns st) in
    trans (pushBurst-deliv g id now (thru-outer op (proj₁ (mintNode sched))) κ
             (proj₁ sE) (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)))
          (subscribeE-deliv g b (thru-outer op (proj₁ (mintNode sched)) ↠ κ) id now
             (proj₂ (mintNode sched)) (installNode (proj₁ (mintNode sched)) ns st))

  sharedConnect-deliv g0 i d κ id now sched st = refl
  sharedConnect-deliv (gs fuel) i d κ id now sched st
    with burstCompleted (proj₁ (subscribeE fuel d (share-sink i) id now sched
                                 (register (toℕ i) κ
                                   (record st { connectedShares =
                                                  toℕ i ∷ EvalSt.connectedShares st }))))
  ... | true  = subscribeE-deliv fuel d (share-sink i) id now sched
                  (register (toℕ i) κ
                    (record st { connectedShares =
                                   toℕ i ∷ EvalSt.connectedShares st }))
  ... | false = subscribeE-deliv fuel d (share-sink i) id now sched
                  (register (toℕ i) κ
                    (record st { connectedShares =
                                   toℕ i ∷ EvalSt.connectedShares st }))

  sharedSlot-deliv g i d κ id now sched st
    with memberSource (toℕ i) (EvalSt.completedSources st)
  ... | true  = refl
  ... | false with memberSource (toℕ i) (EvalSt.connectedShares st)
  ...   | true  = refl
  ...   | false = sharedConnect-deliv g i d κ id now sched st

  subscribeE-deliv g (input i) κ id now sched st with Sched.slots sched i
  ... | shared d = sharedSlot-deliv g i d κ id now sched st
  ... | scripted (hot h) with memberSource (toℕ i) (EvalSt.completedSources st)
  ...   | true  = refl
  ...   | false = refl
  subscribeE-deliv g (input i) κ id now sched st
      | scripted (cold sync [])       = refl
  subscribeE-deliv g (input i) κ id now sched st
      | scripted (cold sync (d ∷ ds)) = refl

  subscribeE-deliv g (ofᵉ ts) κ id now sched st = refl
  subscribeE-deliv g emptyᵉ   κ id now sched st = refl

  subscribeE-deliv g (mapᵉ f b) κ id now sched st =
    let sE = subscribeE g b (map-f f ↠ κ) id now sched st in
    trans (pushBurst-deliv g id now (map-f f) κ
             (proj₁ sE) (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)))
          (subscribeE-deliv g b (map-f f ↠ κ) id now sched st)

  subscribeE-deliv g (takeᵉ count b) κ id now sched st with evalTm count
  ... | zero  = refl
  ... | suc k =
        let sE = subscribeE g b (take-f (proj₁ (mintNode sched)) ↠ κ) id now
                   (proj₂ (mintNode sched))
                   (installNode (proj₁ (mintNode sched)) (take-st (suc k)) st) in
        trans (pushBurst-deliv g id now (take-f (proj₁ (mintNode sched))) κ
                 (proj₁ sE) (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)))
              (subscribeE-deliv g b (take-f (proj₁ (mintNode sched)) ↠ κ) id now
                 (proj₂ (mintNode sched))
                 (installNode (proj₁ (mintNode sched)) (take-st (suc k)) st))

  subscribeE-deliv g (scanᵉ f seed b) κ id now sched st =
    let sE = subscribeE g b (scan-f f (proj₁ (mintNode sched)) ↠ κ) id now
               (proj₂ (mintNode sched))
               (installNode (proj₁ (mintNode sched)) (scan-st (evalTm seed)) st) in
    trans (pushBurst-deliv g id now (scan-f f (proj₁ (mintNode sched))) κ
             (proj₁ sE) (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)))
          (subscribeE-deliv g b (scan-f f (proj₁ (mintNode sched)) ↠ κ) id now
             (proj₂ (mintNode sched))
             (installNode (proj₁ (mintNode sched)) (scan-st (evalTm seed)) st))

  subscribeE-deliv g (mergeAllᵉ b) κ id now sched st =
    subscribeAll-deliv g mergeᵒ (merge-st 0 false) b κ id now sched st
  subscribeE-deliv {u = u} g (concatAllᵉ b) κ id now sched st =
    subscribeAll-deliv g concatᵒ (concat-st {t = u} [] false false) b κ id now sched st
  subscribeE-deliv g (switchAllᵉ b) κ id now sched st =
    subscribeAll-deliv g switchᵒ (switch-st nothing false) b κ id now sched st
  subscribeE-deliv g (exhaustAllᵉ b) κ id now sched st =
    subscribeAll-deliv g exhaustᵒ (exhaust-st false false) b κ id now sched st

  subscribeE-deliv g0        (μᵉ body) κ id now sched st = refl
  subscribeE-deliv (gs fuel) (μᵉ body) κ id now sched st =
    subscribeE-deliv fuel (unfoldμ body) κ id now sched st

  subscribeE-deliv g (varᵉ ()) κ id now sched st

  subscribeE-deliv g (deferᵉ body) κ id now sched st = refl

  subscribeInner-deliv g0 op allNid κ id now o sched st = refl
  subscribeInner-deliv (gs fuel) op allNid κ id now o sched st =
    subscribeE-deliv fuel o
      (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
      (record sched { nextNode = suc (Sched.nextNode sched) }) st

------------------------------------------------------------------
-- § C.  THE DELIVERY WALK EXTENDS THE LEDGER.
--
-- foldPath / dispatchShare / shareGo are the only functions that can
-- move `delivered`, and they move it in exactly one direction: shareGo
-- conses one rid per uncancelled admitted registration and hands the
-- extended ledger onward.  chainStep and cascadeGo sit above them
-- (cascadeGo is the second cons site).
--
-- The recursion is lexicographic on (dispatch gas, path), exactly as
-- the evaluator's: a frame hop shortens the path at constant gas, the
-- share hop peels one gas.
------------------------------------------------------------------

abstract

  -- the two share-boundary bookkeeping steps: the latch writes
  -- completedSources and dying, the finish drops the share's registry
  -- entries.  Neither touches the ledger
  shareLatch-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (i : Fin n) (fin : Bool) (st : EvalSt e) →
    EvalSt.delivered (shareLatch {e = e} i fin st) ≡ EvalSt.delivered st
  shareLatch-deliv i false st = refl
  shareLatch-deliv i true  st = refl

  shareFinish-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (i : Fin n) (fin : Bool) (out : Stream Γ t × Sched Γ × EvalSt e) →
    EvalSt.delivered (proj₂ (proj₂ (shareFinish i fin out)))
      ≡ EvalSt.delivered (proj₂ (proj₂ out))
  shareFinish-deliv i false out = refl
  shareFinish-deliv i true  out = refl

  foldPath-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    (path : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    st ⊑ᵈ proj₂ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st))

  dispatchShare-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    st ⊑ᵈ proj₂ (proj₂ (dispatchShare {t = t} sf gas id now i vals fin sched st))

  shareGo-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) →
    st ⊑ᵈ proj₂ (proj₂ (shareGo sf gas id now i vals fin ps sched st))

  foldPath-deliv sf gas id now envSrc root vals evs fin sched st = ⊑ᵈ-refl st
  foldPath-deliv sf gas id now envSrc (share-sink i) vals evs fin sched st =
    dispatchShare-deliv sf gas id now i vals fin sched st
  foldPath-deliv sf gas id now envSrc (f ↠ path′) vals evs fin sched st =
    let r = stepFrame sf id now f path′ vals fin sched st in
    ⊑ᵈ-trans (⊑ᵈ-of-≡ st (proj₂ (proj₂ (proj₂ (proj₂ r))))
                (stepFrame-deliv sf id now f path′ vals fin sched st))
             (foldPath-deliv sf gas id now envSrc path′ (proj₁ r)
                (evs ++ proj₁ (proj₂ r)) (proj₁ (proj₂ (proj₂ r)))
                (proj₁ (proj₂ (proj₂ (proj₂ r))))
                (proj₂ (proj₂ (proj₂ (proj₂ r)))))

  dispatchShare-deliv sf zero id now i vals fin sched st = ⊑ᵈ-refl st
  dispatchShare-deliv sf (suc gas) id now i vals fin sched st =
    ⊑ᵈ-trans (⊑ᵈ-of-≡ st (shareLatch i fin st) (shareLatch-deliv i fin st))
      (⊑ᵈ-trans
        (shareGo-deliv sf gas id now i vals fin
          (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st))
        (⊑ᵈ-of-≡
          (proj₂ (proj₂ (shareGo sf gas id now i vals fin
            (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st))))
          (proj₂ (proj₂ (shareFinish i fin
            (shareGo sf gas id now i vals fin
              (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st)))))
          (shareFinish-deliv i fin
            (shareGo sf gas id now i vals fin
              (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st)))))

  shareGo-deliv sf gas id now i vals fin []              sched st = ⊑ᵈ-refl st
  shareGo-deliv sf gas id now i vals fin ((rid , p) ∷ ps) sched st
    with any (_≡ᵇ rid) (EvalSt.cancelled st)
  ... | true  = shareGo-deliv sf gas id now i vals fin ps sched st
  ... | false =
        let fp = foldPath sf gas id now (toℕ i) p vals
                   (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched
                   (consᵈ rid st) in
        ⊑ᵈ-trans (⊑ᵈ-cons rid st)
          (⊑ᵈ-trans
            (foldPath-deliv sf gas id now (toℕ i) p vals
               (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched
               (consᵈ rid st))
            (shareGo-deliv sf gas id now i vals fin ps
               (proj₁ (proj₂ fp)) (proj₂ (proj₂ fp))))

  chainStep-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
    (sched : Sched Γ) (st : EvalSt e) →
    st ⊑ᵈ proj₂ (proj₂ (chainStep id a path sched st))
  chainStep-deliv {n = n} {e = e} id a path sched st =
    foldPath-deliv (budgetAt e (Sched.slots sched) id) n id (arrTick a)
      (arrSource a) path (arrVal a ∷ [])
      (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
      (Arrival.isLast a) sched st

  cascadeGo-deliv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (a : Arrival Γ) (id : Id)
    (chains : List (RegId × Path Γ (arrTy a) t))
    (sched : Sched Γ) (st : EvalSt e) →
    st ⊑ᵈ proj₂ (proj₂ (cascadeGo a id chains sched st))
  cascadeGo-deliv a id []                   sched st = ⊑ᵈ-refl st
  cascadeGo-deliv a id ((rid , c) ∷ chains) sched st
    with any (_≡ᵇ rid) (EvalSt.cancelled st)
  ... | true  = cascadeGo-deliv a id chains sched st
  ... | false =
        let cs = chainStep id a c sched (consᵈ rid st) in
        ⊑ᵈ-trans (⊑ᵈ-cons rid st)
          (⊑ᵈ-trans (chainStep-deliv id a c sched (consᵈ rid st))
                    (cascadeGo-deliv a id chains
                       (proj₁ (proj₂ cs)) (proj₂ (proj₂ cs))))

------------------------------------------------------------------
-- § D.  THE DELIVERY RECURRENCE, AS PROVEN EQUATIONS.
--
-- What a consumer reads off: "the deliveries this call added are
-- these, counted so-and-so".  Each equation is the corresponding line
-- of the recurrence at the head of this module, discharged from § B
-- and § C.  Composition is by delivN-split; the `1 +` is delivN-cons.
------------------------------------------------------------------

abstract

  -- Dfp g root = 0
  foldPath-root-N : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    (vals : List (Val Γ t)) (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    delivN st (proj₂ (proj₂ (foldPath sf gas id now envSrc root vals evs fin sched st)))
      ≡ 0
  foldPath-root-N sf gas id now envSrc vals evs fin sched st = delivN-≡ st st refl

  -- Dfp g (f ↠ p) = Dfp g p, at the frame's own post-state.  The
  -- equality (not an inequality) is § B's whole content
  foldPath-frame-N : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    (f : Frame Γ s u) (path′ : Path Γ u t) (vals : List (Val Γ s))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    let r    = stepFrame sf id now f path′ vals fin sched st
        st₁   = proj₂ (proj₂ (proj₂ (proj₂ r)))
        sched₁ = proj₁ (proj₂ (proj₂ (proj₂ r))) in
    delivN st (proj₂ (proj₂ (foldPath sf gas id now envSrc (f ↠ path′)
                               vals evs fin sched st)))
      ≡ delivN st₁ (proj₂ (proj₂ (foldPath sf gas id now envSrc path′
                                    (proj₁ r) (evs ++ proj₁ (proj₂ r))
                                    (proj₁ (proj₂ (proj₂ r))) sched₁ st₁)))
  foldPath-frame-N sf gas id now envSrc f path′ vals evs fin sched st =
    let r   = stepFrame sf id now f path′ vals fin sched st
        sfp = stepFrame-deliv sf id now f path′ vals fin sched st in
    trans (delivN-split (⊑ᵈ-of-≡ st (proj₂ (proj₂ (proj₂ (proj₂ r)))) sfp)
             (foldPath-deliv sf gas id now envSrc path′ (proj₁ r)
                (evs ++ proj₁ (proj₂ r)) (proj₁ (proj₂ (proj₂ r)))
                (proj₁ (proj₂ (proj₂ (proj₂ r))))
                (proj₂ (proj₂ (proj₂ (proj₂ r))))))
          (cong (_+ delivN (proj₂ (proj₂ (proj₂ (proj₂ r))))
                    (proj₂ (proj₂ (foldPath sf gas id now envSrc path′ (proj₁ r)
                       (evs ++ proj₁ (proj₂ r)) (proj₁ (proj₂ (proj₂ r)))
                       (proj₁ (proj₂ (proj₂ (proj₂ r))))
                       (proj₂ (proj₂ (proj₂ (proj₂ r))))))))
                (delivN-≡ st (proj₂ (proj₂ (proj₂ (proj₂ r)))) sfp))

  -- Dfp g (sink i) = Dds g
  foldPath-sink-N : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (evs : List (InstEvent (Val Γ t)))
    (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    delivN st (proj₂ (proj₂ (foldPath sf gas id now envSrc (share-sink i)
                               vals evs fin sched st)))
      ≡ delivN st (proj₂ (proj₂ (dispatchShare sf gas id now i vals fin sched st)))
  foldPath-sink-N sf gas id now envSrc i vals evs fin sched st = refl

  -- Dds 0 = 0
  dispatchShare-zero-N : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    delivN st (proj₂ (proj₂ (dispatchShare {t = t} sf zero id now i vals fin sched st)))
      ≡ 0
  dispatchShare-zero-N sf id now i vals fin sched st = delivN-≡ st st refl

  -- Dds (suc g) = the fan-out walk over the registry AS OF NOW.  The
  -- latch and the finish are both ledger-free, so the whole step is the
  -- shareGo walk
  dispatchShare-suc-N : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    delivN st (proj₂ (proj₂ (dispatchShare {t = t} sf (suc gas) id now i vals fin sched st)))
      ≡ delivN (shareLatch i fin st)
               (proj₂ (proj₂ (shareGo sf gas id now i vals fin
                 (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st))))
  dispatchShare-suc-N sf gas id now i vals fin sched st =
    cong₂ _∸_
      (cong length (shareFinish-deliv i fin
        (shareGo sf gas id now i vals fin
          (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st))))
      (cong length (sym (shareLatch-deliv i fin st)))

  -- a cancelled chain delivers nothing: the walk skips it whole
  shareGo-skip-N : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool) (rid : RegId)
    (p : Path Γ (lookup Γ i) t) (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) →
    any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true →
    delivN st (proj₂ (proj₂ (shareGo sf gas id now i vals fin ((rid , p) ∷ ps) sched st)))
      ≡ delivN st (proj₂ (proj₂ (shareGo sf gas id now i vals fin ps sched st)))
  shareGo-skip-N sf gas id now i vals fin rid p ps sched st h
    with any (_≡ᵇ rid) (EvalSt.cancelled st) | h
  ... | true | refl = refl

  -- AND THE ONE THAT CARRIES THE `1 +`: an uncancelled chain costs one
  -- delivery, plus what its fold does, plus what the rest of the walk
  -- does — the `Σ over uncancelled chains of (1 + Dfp g)` line, one
  -- summand at a time
  shareGo-cons-N : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool) (rid : RegId)
    (p : Path Γ (lookup Γ i) t) (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) →
    any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false →
    let st₀ = consᵈ rid st
        fp  = foldPath sf gas id now (toℕ i) p vals
                (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀
        st₁ = proj₂ (proj₂ fp) in
    delivN st (proj₂ (proj₂ (shareGo sf gas id now i vals fin ((rid , p) ∷ ps) sched st)))
      ≡ suc (delivN st₀ st₁
             + delivN st₁ (proj₂ (proj₂ (shareGo sf gas id now i vals fin ps
                                          (proj₁ (proj₂ fp)) st₁))))
  shareGo-cons-N sf gas id now i vals fin rid p ps sched st h
    with any (_≡ᵇ rid) (EvalSt.cancelled st) | h
  ... | false | refl =
        let st₀ = consᵈ rid st
            fp  = foldPath sf gas id now (toℕ i) p vals
                    (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀
            FP  = foldPath-deliv sf gas id now (toℕ i) p vals
                    (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀
            GO  = shareGo-deliv sf gas id now i vals fin ps
                    (proj₁ (proj₂ fp)) (proj₂ (proj₂ fp)) in
        trans (delivN-cons rid st _ (⊑ᵈ-trans FP GO))
              (cong suc (delivN-split FP GO))

-- (DELETED) § E held `cascadeLatch-deliv`, `cascadeFinish-deliv`
-- and `cascade-delivN` — one cascade's deliveries are its final ledger,
-- counted flat, because the latch clears `delivered` and cascadeFinish
-- touches it not at all.  Together with `cascadeGo-skip-N` / `cascadeGo-cons-N`
-- (the cascade's own two ledger lines, also deleted) they existed for ONE
-- consumer, `dry-tick-core`'s argument list, and that list is wrong about
-- itself: the dry half is `cascadeGo`'s stream verbatim (cascadeFinish
-- emits nothing), so no ledger fact can enter it.
--
-- RECOVERY: git show fa9692d:agda/src/Verify-Budget-Sufficient/Deliveries.agda
--   restores all five.  `delivN` itself is LIVE (.Delivery-Walk reads it all
--   through the walk), so the cascade-level counts are the natural thing to
--   want back the moment a delivery-count obligation is actually stated.
------------------------------------------------------------------
