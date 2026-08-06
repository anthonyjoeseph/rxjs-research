-- Battery-Done-Thread.agda  (2026-08-06)
--
-- PURPOSE: verify that threading `ProtocolSt.done S ≡ false` through
-- `subscribeE-wf` is type-correct — the proposed repair for the refuted
-- `burst-done-false` postulate.
--
-- Three specific claims this probe checks by typechecking:
--
--   (A) ofᵉ / emptyᵉ clauses: `deq : ProtocolSt.done S ≡ false` passed
--       directly to `oneShotBurst-wf` instead of the false `burst-done-false`.
--
--   (B) mapᵉ / scanᵉ / μᵉ (gs fuel) clauses: `deq` forwarded unchanged to
--       the recursive call, since S itself is forwarded unchanged (SPINE).
--
--   (C) External caller `subscribe-wf′`: supplies `refl` at `S = protocol-init`
--       because `ProtocolSt.done protocol-init = false` by definition (reduces
--       definitionally, so `refl` typechecks).
--
-- WHAT THIS PROBE DOES **NOT** ESTABLISH — read before trusting the repair.
-- The spine argument is VERIFIED only for the clauses whose recursion is
-- VISIBLE CODE: mapᵉ, scanᵉ, takeᵉ (via its receipt), μᵉ (gs), and the two
-- bases.  The FOUR `*All` clauses and `input`/`deferᵉ` do NOT recurse in
-- source — they delegate to postulates.  So for those, threading `deq` does
-- not PROVE the spine; it RELOCATES the obligation into those postulates,
-- which now carry `done ≡ false` as a premise they must honour when they
-- eventually subscribe anything.  Four of them (`*All-wf`) are additionally
-- blocked on MERGE-CERT, so the honest status is: the repair is type-correct
-- everywhere and semantically verified on the visible spine only.
--
-- The claim that would BREAK it, for whoever proves an `*All` receipt: if one
-- subscribe walk can reach TWO base bursts in sequence, the second needs
-- `done ≡ false` against `oneShotBurst-run`'s latched `done ≡ true` (VWF:860)
-- and the threaded premise is FALSE at that call.  VWF:3823's topology note
-- (no binary static merge; inners subscribe in later cascades) is why this is
-- believed impossible — it is the load-bearing fact, not an aside.
--
-- BUILD: cd agda && agda -i src -i probe probe/Battery-Done-Thread.agda
-- (VWF.agdai is the heavy interface; this file deserialises it, ~10 s.)
------------------------------------------------------------------------
module Battery-Done-Thread where

open import Data.Bool    using (Bool; true; false)
open import Data.Empty   using (⊥-elim)
open import Data.Fin     using (Fin)
open import Data.List    using (List; []; _∷_; map)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Nat     using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Vec     using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs; Id; Tick)
open import Rx.Exp  using (Ctx; Ty; Closed; Val; Fn; Tm; obs; _×ᵗ_; natᵗ;
                           input; ofᵉ; emptyᵉ; mapᵉ; scanᵉ; takeᵉ; μᵉ; varᵉ;
                           deferᵉ; mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                           unfoldμ; evalTm)
open import Rx.Evaluator using (Sched; EvalSt; Path; Stream; NodeId; Slots;
                                AllOp; NodeState;
                                subscribeE; hasDry;
                                installNode; mintNode; scan-st; take-st;
                                map-f; scan-f; take-f; root; _↠_;
                                sched-init; st-init; budgetAt;
                                memberSource)
open import Rx.Protocol  using (ProtocolSt; runProtocol; valsLast?; protocol-init)

-- Real proven lemmas from Verify-Well-Formed.
-- subscribeE-wf is NOT listed — we define our own amended version.
-- burst-done-false is NOT listed — it is FALSE and this probe deletes it.
open import Verify-Well-Formed using
  ( BurstInv
  ; oneShotBurst-wf
  ; subscribeE-map-wf
  ; subscribeE-scan-wf
  ; burst-init
  )

------------------------------------------------------------------------
-- Local helper
------------------------------------------------------------------------

private
  true≢false : ∀ {A : Set} → true ≡ false → A
  true≢false ()

------------------------------------------------------------------------
-- Gap postulates — shape-identical to the ones in VWF (unchanged)
------------------------------------------------------------------------

postulate
  -- hasDry propagates inward through the map push (VWF:1114)
  map-nodry-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (f : Fn Γ [] [] [] s u) (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    hasDry (proj₁ (subscribeE fuel (mapᵉ f b) κ id now sched st)) ≡ false →
    hasDry (proj₁ (subscribeE fuel b (map-f f ↠ κ) id now sched st)) ≡ false

  -- map-frame preserves valsLast? (VWF:1121)
  map-valsLast-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (f : Fn Γ [] [] [] s u) (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    valsLast? (proj₁ (subscribeE fuel b (map-f f ↠ κ) id now sched st)) ≡ true →
    valsLast? (proj₁ (subscribeE fuel (mapᵉ f b) κ id now sched st)) ≡ true

  -- hasDry propagates inward through the scan push (VWF:1130)
  scan-nodry-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u)
    (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    hasDry (proj₁ (subscribeE fuel (scanᵉ f seed b) κ id now sched st)) ≡ false →
    hasDry (proj₁ (subscribeE fuel b
                    (scan-f f (proj₁ (mintNode sched)) ↠ κ) id now
                    (proj₂ (mintNode sched))
                    (installNode (proj₁ (mintNode sched)) (scan-st (evalTm seed)) st)))
           ≡ false

  -- fresh scan node survives subscribeE b (VWF:1143)
  scan-nodeP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u)
    (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    let nid = proj₁ (mintNode sched)
        r₀  = subscribeE fuel b (scan-f f nid ↠ κ) id now (proj₂ (mintNode sched))
                (installNode nid (scan-st (evalTm seed)) st)
    in Σ (Val Γ u) λ acc →
         Rx.Evaluator.lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r₀)))
           ≡ just (scan-st acc)

  -- scan-frame preserves valsLast? (VWF:1157)
  scan-valsLast-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u)
    (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    valsLast? (proj₁ (subscribeE fuel b
                       (scan-f f (proj₁ (mintNode sched)) ↠ κ) id now
                       (proj₂ (mintNode sched))
                       (installNode (proj₁ (mintNode sched)) (scan-st (evalTm seed)) st)))
              ≡ true →
    valsLast? (proj₁ (subscribeE fuel (scanᵉ f seed b) κ id now sched st)) ≡ true

  -- BurstInv adaptation for scan's mintNode/installNode (VWF:1166)
  scan-binv-adapt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u)
    (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    BurstInv id (proj₂ (mintNode sched))
               (installNode (proj₁ (mintNode sched)) (scan-st (evalTm seed)) st) S

------------------------------------------------------------------------
-- Per-clause postulates WITH the new `done S ≡ false` premise.
-- These are the new signatures the patch produces.
------------------------------------------------------------------------

postulate
  -- input clause (VWF:1195) — new signature includes deq
  subscribeE-input-wf′ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (fuel : Gas) (i : Fin n) (κ : Path Γ (lookup Γ i) t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    ProtocolSt.done S ≡ false →
    hasDry (proj₁ (subscribeE fuel (input i) κ id now sched st)) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = subscribeE fuel (input i) κ id now sched st
      in (runProtocol S (proj₁ r) ≡ just S′)
         × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
         × (valsLast? (proj₁ r) ≡ true)

  -- deferᵉ clause (VWF:1218) — new signature includes deq
  subscribeE-defer-wf′ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : Gas) (body : Closed Γ u) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    ProtocolSt.done S ≡ false →
    hasDry (proj₁ (subscribeE fuel (deferᵉ body) κ id now sched st)) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = subscribeE fuel (deferᵉ body) κ id now sched st
      in (runProtocol S (proj₁ r) ≡ just S′)
         × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
         × (valsLast? (proj₁ r) ≡ true)

  -- *All clauses (VWF:1235–1277) — new signature includes deq
  subscribeE-mergeAll-wf′ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    ProtocolSt.done S ≡ false →
    hasDry (proj₁ (subscribeE fuel (mergeAllᵉ b) κ id now sched st)) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = subscribeE fuel (mergeAllᵉ b) κ id now sched st
      in (runProtocol S (proj₁ r) ≡ just S′)
         × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
         × (valsLast? (proj₁ r) ≡ true)

  subscribeE-concatAll-wf′ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    ProtocolSt.done S ≡ false →
    hasDry (proj₁ (subscribeE fuel (concatAllᵉ b) κ id now sched st)) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = subscribeE fuel (concatAllᵉ b) κ id now sched st
      in (runProtocol S (proj₁ r) ≡ just S′)
         × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
         × (valsLast? (proj₁ r) ≡ true)

  subscribeE-switchAll-wf′ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    ProtocolSt.done S ≡ false →
    hasDry (proj₁ (subscribeE fuel (switchAllᵉ b) κ id now sched st)) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = subscribeE fuel (switchAllᵉ b) κ id now sched st
      in (runProtocol S (proj₁ r) ≡ just S′)
         × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
         × (valsLast? (proj₁ r) ≡ true)

  subscribeE-exhaustAll-wf′ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    ProtocolSt.done S ≡ false →
    hasDry (proj₁ (subscribeE fuel (exhaustAllᵉ b) κ id now sched st)) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = subscribeE fuel (exhaustAllᵉ b) κ id now sched st
      in (runProtocol S (proj₁ r) ≡ just S′)
         × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
         × (valsLast? (proj₁ r) ≡ true)

  -- takeᵉ whole case (VWF:1294 outer) — new signature includes deq
  subscribeE-takeᵉ-wf′ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (fuel : Gas) (count : Tm Γ [] [] [] natᵗ) (b : Closed Γ s) (κ : Path Γ s t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    ProtocolSt.done S ≡ false →
    hasDry (proj₁ (subscribeE fuel (takeᵉ count b) κ id now sched st)) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = subscribeE fuel (takeᵉ count b) κ id now sched st
      in (runProtocol S (proj₁ r) ≡ just S′)
         × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
         × (valsLast? (proj₁ r) ≡ true)

------------------------------------------------------------------------
-- THE AMENDED subscribeE-wf′ SIGNATURE
-- New parameter: `deq : ProtocolSt.done S ≡ false` after `binv`.
------------------------------------------------------------------------

subscribeE-wf′ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (fuel : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  BurstInv id sched st S →
  ProtocolSt.done S ≡ false →           -- ← NEW (replaces burst-done-false)
  hasDry (proj₁ (subscribeE fuel b κ id now sched st)) ≡ false →
  Σ ProtocolSt λ S′ →
    let r = subscribeE fuel b κ id now sched st
    in (runProtocol S (proj₁ r) ≡ just S′)
       × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
       × (valsLast? (proj₁ r) ≡ true)

------------------------------------------------------------------------
-- CLAIM A: base clauses use `deq` directly — no burst-done-false
------------------------------------------------------------------------

-- ofᵉ: `deq` handed directly to oneShotBurst-wf (its 6th argument)
subscribeE-wf′ fuel (ofᵉ ts) κ id now sched st S binv deq nodry =
  let vals = map evalTm ts
      (S′ , run , binv′) = oneShotBurst-wf vals id sched st S binv deq
  in S′ , run , binv′ , refl

-- emptyᵉ: same shape
subscribeE-wf′ fuel emptyᵉ κ id now sched st S binv deq nodry =
  let (S′ , run , binv′) = oneShotBurst-wf [] id sched st S binv deq
  in S′ , run , binv′ , refl

------------------------------------------------------------------------
-- CLAIM B: spine clauses forward `deq` — S unchanged throughout
------------------------------------------------------------------------

-- mapᵉ: deq forwarded to recursive call (same S)
subscribeE-wf′ fuel (mapᵉ f b) κ id now sched st S binv deq nodry =
  let (S′ , run₀ , binv₀ , vl₀) =
        subscribeE-wf′ fuel b (map-f f ↠ κ) id now sched st S binv deq
          (map-nodry-push fuel f b κ id now sched st nodry)
      (S″ , run , binv″) =
        subscribeE-map-wf fuel f b κ id now sched st S binv (S′ , run₀ , binv₀)
  in S″ , run , binv″ , map-valsLast-push fuel f b κ id now sched st vl₀

-- scanᵉ: deq forwarded (S unchanged; sched/st change but not S)
subscribeE-wf′ fuel (scanᵉ f seed b) κ id now sched st S binv deq nodry =
  let nid    = proj₁ (mintNode sched)
      sched₁ = proj₂ (mintNode sched)
      st₁    = installNode nid (scan-st (evalTm seed)) st
      (S′ , run₀ , binv₀ , vl₀) =
        subscribeE-wf′ fuel b (scan-f f nid ↠ κ) id now sched₁ st₁ S
          (scan-binv-adapt fuel f seed b κ id now sched st S binv)
          deq   -- ← same S, so deq still valid
          (scan-nodry-push fuel f seed b κ id now sched st nodry)
      (S″ , run , binv″) =
        subscribeE-scan-wf fuel f seed b κ id now sched st S binv
          (S′ , run₀ , binv₀ , scan-nodeP fuel f seed b κ id now sched st)
  in S″ , run , binv″ , scan-valsLast-push fuel f seed b κ id now sched st vl₀

-- input: forward deq to per-clause helper
subscribeE-wf′ fuel (input i) κ id now sched st S binv deq nodry =
  subscribeE-input-wf′ fuel i κ id now sched st S binv deq nodry

-- deferᵉ: forward deq to per-clause helper
subscribeE-wf′ fuel (deferᵉ body) κ id now sched st S binv deq nodry =
  subscribeE-defer-wf′ fuel body κ id now sched st S binv deq nodry

-- takeᵉ: forward deq to per-clause helper
subscribeE-wf′ fuel (takeᵉ count b) κ id now sched st S binv deq nodry =
  subscribeE-takeᵉ-wf′ fuel count b κ id now sched st S binv deq nodry

-- *All: forward deq to per-clause helpers
subscribeE-wf′ fuel (mergeAllᵉ b)   κ id now sched st S binv deq nodry =
  subscribeE-mergeAll-wf′  fuel b κ id now sched st S binv deq nodry
subscribeE-wf′ fuel (concatAllᵉ b)  κ id now sched st S binv deq nodry =
  subscribeE-concatAll-wf′ fuel b κ id now sched st S binv deq nodry
subscribeE-wf′ fuel (switchAllᵉ b)  κ id now sched st S binv deq nodry =
  subscribeE-switchAll-wf′ fuel b κ id now sched st S binv deq nodry
subscribeE-wf′ fuel (exhaustAllᵉ b) κ id now sched st S binv deq nodry =
  subscribeE-exhaustAll-wf′ fuel b κ id now sched st S binv deq nodry

-- μᵉ g0: dryBurst fires hasDry = true, contradicts nodry (≡ false)
subscribeE-wf′ g0 (μᵉ body) κ id now sched st S binv deq nodry =
  ⊥-elim (true≢false nodry)

-- μᵉ (gs fuel): fuel decreases; unfoldμ reduces definitionally; deq forwarded
subscribeE-wf′ (gs fuel) (μᵉ body) κ id now sched st S binv deq nodry =
  subscribeE-wf′ fuel (unfoldμ body) κ id now sched st S binv deq nodry

-- varᵉ (): absurd
subscribeE-wf′ fuel (varᵉ ()) κ id now sched st S binv deq nodry

------------------------------------------------------------------------
-- CLAIM C: external caller supplies `refl` — protocol-init.done = false
-- by definition, so `refl : ProtocolSt.done protocol-init ≡ false`
-- reduces definitionally.
------------------------------------------------------------------------

-- We use `_` for the result body; only the CALL typechecking matters here.
subscribe-wf′-entry-ok :
  ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  hasDry (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                            (sched-init e ins) (st-init e))) ≡ false →
  Σ ProtocolSt λ S →
    let r = subscribeE (budgetAt e ins 0) e root 0 0 (sched-init e ins) (st-init e)
    in (runProtocol protocol-init (proj₁ r) ≡ just S)
       × BurstInv 0 (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S
       × (valsLast? (proj₁ r) ≡ true)
subscribe-wf′-entry-ok e ins nodry =
  subscribeE-wf′ (budgetAt e ins 0) e root 0 0
                 (sched-init e ins) (st-init e)
                 protocol-init
                 (burst-init e ins)
                 refl    -- ← ProtocolSt.done protocol-init ≡ false (definitional)
                 nodry
