-- ROADMAP: tier-1 #1 — per-clause census for `subscribeE-walk-core` sub-postulates.
-- DELETE WHEN: `subscribeE-walk-core` is assembled into src and this file's content
--   is superseded by the src landing.  [T2]
-- Mirrored in PROOF-STATE.md § "PROBE ROADMAP TIES".  If you change one,
-- change the other — the duplication is deliberate cross-checking.
--
-- Walk-Core-Census-Probe.agda  (2026-08-11)
--
-- CLAUSE CENSUS for `subscribeE-walk-core` (Measures.agda:5733).
-- One census lemma per subscribeE clause.  Each lemma takes the full
-- hypothesis block of subscribeE-walk-core with b fixed, fills easy
-- conjuncts by computation/refl/hypothesis, and names a postulate for
-- every goal that requires real mathematics.
--
-- The LEDGER at the bottom of this file lists every census postulate
-- with its classification.
--
-- PROBE CLASSIFICATION: EVIDENCE
-- This probe is a census, not a landing candidate.
-- It compiles against the current src tree but its content is the
-- LEDGER of sub-postulates, not a theorem to land.
--
-- BUILD:
--   cd /Users/flipside-anthony/Developer/personal/rxjs-research/agda &&
--   ls probe/Walk-Core-Census-Probe.agda &&
--   agda -i src -i probe probe/Walk-Core-Census-Probe.agda

module Walk-Core-Census-Probe where

open import Data.Bool    using (Bool; true; false)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _<_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; n≤1+n)
open import Data.List.Properties using (length-map)
open import Data.List    using (List; []; _∷_; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Fin     using (Fin)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import Rx.Prim using (Gas; g0; gs; Id; Tick)
open import Rx.Exp
  using (Ty; Ctx; Closed; Val; Tm; Exp; Fn;
         natᵗ; obs; _×ᵗ_; _+ᵗ_;
         emptyᵉ; ofᵉ; mapᵉ; takeᵉ; scanᵉ;
         mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
         μᵉ; varᵉ; deferᵉ; input;
         nat̂; syncSizeᵉ; sizeᵉ; unfoldμ)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Evaluator
  using (Slots; Path; root; share-sink; _↠_;
         Stream; Sched; EvalSt;
         hasDry; subscribeE; pushBurst; subscribeAll;
         mintNode; mintSource; mintOrdinal;
         oneShotBurst; register; map-f; scan-f; take-f;
         thru-outer; AllOp; mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ;
         merge-st; concat-st; switch-st; exhaust-st; take-st;
         dryBurst;
         NodeState; installNode)

-- Wet opens Caps → Keeps-Ring → Measures all public, so INV?, capᴱ,
-- walkCap, dBound, mintCount, burstLen, burstB?, burstHopD?, regsLen?,
-- ofWᵉ, pathB?, pathΩ?, pathLen, widthOK?, unconn, _hasAtLeast_,
-- E≤E*3^, subscribeE-walk, hasAtLeast-mono etc. come in here.
open import Verify-Budget-Sufficient.Wet
  using (INV?; capᴱ; walkCap; dBound; mintCount; burstLen;
         burstB?; burstHopD?; regsLen?; pathB?; pathΩ?; pathLen;
         widthOK?; ofWᵉ; unconn;
         _hasAtLeast_; hz; hs; hasAtLeast-mono;
         E≤E*3^; subscribeE-walk; INV?-widen; capᴱ-mono;
         slotsOfW; ΩAt; fnCapᵉ;
         dBound-struct; dBound-hop)

----------------------------------------------------------------------
-- § 0  NOTATION
--
-- The 9-conjunct result type of subscribeE-walk-core at a fixed b:
--
--  WalkResult g b κ id now sched st E Ψ W Ω ℓ F G =
--    let r = subscribeE g b κ id now sched st
--    in Σ ℕ λ E′ →
--         (E ≤ E′)
--       × (E′ ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ G))          -- ceiling
--       × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
--       × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
--       × (burstHopD? F (hopDᵉ F b) (proj₁ r) ≡ true)
--       × (hasDry (proj₁ r) ≡ false)
--       × (mintCount (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
--             ≤ mintCount sched st + walkCap Ω ℓ G)
--       × (burstLen (proj₁ r) ≤ walkCap Ω ℓ G)
--       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
--
-- Abbreviations used in census postulate types (from dBound):
--   U = unconn (slots sched) (connectedShares st)
----------------------------------------------------------------------

----------------------------------------------------------------------
-- § 1  SHARED ARITHMETIC CENSUS POSTULATES
----------------------------------------------------------------------

postulate
  ------------------------------------------------------------------
  -- CENS-MINTS: mintSource bumps mintCount by exactly 1 ≤ walkCap.
  -- Proof sketch:
  --   mintCount (record sched { nextSource = suc _ }) st
  --     = nextOrdinal + suc nextSource + nextNode + nextReg
  --     = suc (mintCount sched st)           [by +-suc]
  --   suc (mintCount sched st) ≤ mintCount sched st + walkCap Ω ℓ G
  --     ↔ 1 ≤ walkCap Ω ℓ G                 [by m+1≤m+n ↔ 1≤n]
  --   walkCap Ω ℓ G = ((3+Ω)*suc ℓ)^(3^G) ≥ 3 ≥ 1   [pos]
  -- Classification: arithmetic / walkCap positivity — PROVABLE
  ------------------------------------------------------------------
  walk-core-mintSource-mintCount :
    ∀ {n} {Γ : Ctx n} (Ω ℓ G : ℕ) (sched : Sched Γ)
      {t} {e : Closed Γ t} (st : EvalSt e) →
    mintCount (proj₂ (mintSource sched)) st
      ≤ mintCount sched st + walkCap Ω ℓ G

  ------------------------------------------------------------------
  -- CENS-MINTS2: TWO mintSource calls (mintSource + mintOrdinal,
  -- or mintNode + mintSource) bump mintCount by ≤ 2 ≤ walkCap.
  -- Classification: arithmetic — PROVABLE (same sketch as above)
  ------------------------------------------------------------------
  walk-core-2mints-mintCount :
    ∀ {n} {Γ : Ctx n} (Ω ℓ G : ℕ) (sched : Sched Γ)
      {t} {e : Closed Γ t} (st : EvalSt e) →
    mintCount (proj₂ (mintSource (proj₂ (mintNode sched)))) st
      ≤ mintCount sched st + walkCap Ω ℓ G

  ------------------------------------------------------------------
  -- CENS-MINTS3: THREE mints (mintNode + mintSource + mintOrdinal)
  -- bump mintCount by ≤ 3 ≤ walkCap (G ≥ 1).
  -- Classification: arithmetic — PROVABLE
  ------------------------------------------------------------------
  walk-core-3mints-mintCount :
    ∀ {n} {Γ : Ctx n} (Ω ℓ G : ℕ) (sched : Sched Γ)
      {t} {e : Closed Γ t} (st : EvalSt e) →
    1 ≤ G →
    mintCount (proj₂ (mintOrdinal (proj₂ (mintSource (proj₂ (mintNode sched)))))) st
      ≤ mintCount sched st + walkCap Ω ℓ G

  ------------------------------------------------------------------
  -- CENS-BLEN-EMPTY: burstLen of oneShotBurst [] = 4 ≤ walkCap.
  -- Proof sketch:
  --   burstLen [(init s ∷ close s exhausted ∷ complete ∷ []) at ...]
  --     = suc (length [init s, close s exhausted, complete]) = suc 3 = 4
  --   walkCap Ω ℓ G ≥ walkCap 0 1 1 = (3*2)^3 = 216 ≥ 4  [when G≥1, ℓ≥1]
  -- Classification: arithmetic + walkCap positivity — PROVABLE
  ------------------------------------------------------------------
  walk-core-burstLen-empty :
    ∀ {n} {Γ : Ctx n} (Ω ℓ G : ℕ)
      (id : Id) (sched : Sched Γ) {u} →
    1 ≤ G → 1 ≤ ℓ →
    burstLen {u = u} (proj₁ (oneShotBurst [] id sched)) ≤ walkCap Ω ℓ G

  ------------------------------------------------------------------
  -- CENS-BLEN-OF: burstLen of oneShotBurst vs = suc(2 + |vs|) ≤ walkCap.
  -- Needs sizeᵉ (ofᵉ ts) ≤ capᴱ W E to bound |ts|.
  -- Classification: arithmetic + size bound — PROVABLE (with length ts ≤ capᴱ)
  ------------------------------------------------------------------
  walk-core-burstLen-of :
    ∀ {n} {Γ : Ctx n} {u} (Ω ℓ G : ℕ) (B : ℕ) (id : Id) (sched : Sched Γ)
      (vs : List (Val Γ u)) →
    1 ≤ G → 1 ≤ ℓ → length vs ≤ B → 4 ≤ B →
    burstLen (proj₁ (oneShotBurst vs id sched)) ≤ walkCap Ω ℓ G

  ------------------------------------------------------------------
  -- CENS-BLEN-DEFER: burstLen of deferᵉ burst ≤ walkCap.
  -- deferᵉ emits [(init src ∷ []) at id from src] — burstLen = 2.
  -- Classification: arithmetic — PROVABLE
  ------------------------------------------------------------------
  walk-core-burstLen-defer :
    ∀ {n} {Γ : Ctx n} (Ω ℓ G : ℕ) (id : Id) (sched : Sched Γ) {u} →
    1 ≤ G → 1 ≤ ℓ →
    burstLen {u = u} (proj₁ (oneShotBurst [] id sched)) ≤ walkCap Ω ℓ G

  ------------------------------------------------------------------
  -- CENS-OF-BURSTB: burstB? holds for oneShotBurst (map evalTm ts).
  -- Requires that each evalTm tm has sizeᵛ ≤ capᴱ W E and fnCapᵛ ≤ Ψ.
  -- Classification: evaluated-value size bound — PROVABLE (existing
  -- lemma ofVals-B in Wet.agda proves this for the store face)
  ------------------------------------------------------------------
  walk-core-of-burstB :
    ∀ {n} {Γ : Ctx n} {u} (Ψ W E : ℕ) (id : Id) (sched : Sched Γ)
      (ts : List (Tm Γ [] [] [] u)) →
    3 ≤ E →
    sizeᵉ (ofᵉ ts) ≤ capᴱ W E →
    fnCapᵉ (ofᵉ ts) ≤ Ψ →
    burstB? (capᴱ W E) Ψ (proj₁ (oneShotBurst (Data.List.map (λ tm → Rx.Exp.evalTm tm) ts) id sched)) ≡ true

  ------------------------------------------------------------------
  -- CENS-OF-BHOPD: burstHopD? F (hopDᵉ F (ofᵉ ts)) holds.
  -- hopDᵉ F (ofᵉ ts) = hopDᵗˢ F ts.
  -- Values of ofᵉ are closed terms so hopDᵛ = 0 ≤ hopDᵗˢ F ts.
  -- Classification: hop-depth of evaluated terms — PROVABLE (by
  -- existing hop-depth apparatus in Hop-Depth.agda)
  ------------------------------------------------------------------
  walk-core-of-burstHopD :
    ∀ {n} {Γ : Ctx n} {u} (W E F : ℕ) (id : Id) (sched : Sched Γ)
      (ts : List (Tm Γ [] [] [] u)) →
    burstHopD? F (hopDᵉ F (ofᵉ ts))
      (proj₁ (oneShotBurst (Data.List.map (λ tm → Rx.Exp.evalTm tm) ts) id sched)) ≡ true

  ------------------------------------------------------------------
  -- CENS-OF-REGSLEN: regsLen? grows by 1 for scripted (cold _ (d∷ds))
  -- and for deferᵉ (both register a chain).
  -- Classification: registry length bound — PROVABLE (register adds
  -- at most one entry; regsLen? checks ≤ᵇ ℓ; pathLen ≤ ℓ from hyp)
  ------------------------------------------------------------------
  walk-core-register-regsLen :
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
      (ℓ src : ℕ) (κ : Path Γ u t) (st : EvalSt e) →
    pathLen κ ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    regsLen? ℓ (EvalSt.registry (register src κ st)) ≡ true

  ------------------------------------------------------------------
  -- CENS-SIZE-OF: length ts ≤ sizeᵉ (ofᵉ ts) (used in burstLen bound)
  -- Proof sketch: sizeᵉ (ofᵉ ts) = suc (length ts + ...) ≥ length ts
  -- Classification: arithmetic — PROVABLE
  ------------------------------------------------------------------
  sizeᵗˢ≤sizeᵉ :
    ∀ {n} {Γ : Ctx n} {u} (ts : List (Tm Γ [] [] [] u)) →
    length ts ≤ sizeᵉ (ofᵉ ts)

  ------------------------------------------------------------------
  -- CENS-G-POS: 1 ≤ G when dBound ≥ 1. For emptyᵉ/takeᵉ-zero,
  -- dBound Ŝ R̂ U r (syncSizeᵉ e) where syncSizeᵉ e ≥ 1 gives dBound ≥ 1.
  -- Classification: arithmetic — PROVABLE (n≤m+n)
  ------------------------------------------------------------------
  walk-core-G-pos :
    ∀ {Ŝ R̂ U r s G : ℕ} →
    dBound Ŝ R̂ U r s ≤ G → 1 ≤ G

  ------------------------------------------------------------------
  -- CENS-ℓ-POS: 1 ≤ ℓ when pathLen κ + G ≤ ℓ and 1 ≤ G.
  -- Classification: arithmetic — PROVABLE (≤-trans)
  ------------------------------------------------------------------
  walk-core-ℓ-pos :
    ∀ {G ℓ κlen : ℕ} →
    1 ≤ G → κlen + G ≤ ℓ → 1 ≤ ℓ

  ------------------------------------------------------------------
  -- CENS-HASDRY: hasDry of a oneShotBurst (structural events only)
  -- is always false.  Proof: structural events are init/close/complete,
  -- none of which are dried.
  -- Classification: enumeration — PROVABLE
  ------------------------------------------------------------------
  walk-core-oneShotBurst-hasDry :
    ∀ {n} {Γ : Ctx n} {u} (vs : List (Val Γ u)) (id : Id) (sched : Sched Γ) →
    hasDry (proj₁ (oneShotBurst vs id sched)) ≡ false

  ------------------------------------------------------------------
  -- CENS-CAPE-4: capᴱ W E ≥ 4 when E ≥ 3.
  -- capᴱ W 3 = (2+2W)^3 ≥ 2^3 = 8 ≥ 4.
  -- Classification: arithmetic — PROVABLE
  ------------------------------------------------------------------
  walk-core-capᴱ-lb4 :
    ∀ (W E : ℕ) → 3 ≤ E → 4 ≤ capᴱ W E

----------------------------------------------------------------------
-- § 2  PER-CLAUSE CENSUS POSTULATES (for structurally complex cases)
----------------------------------------------------------------------

postulate
  ------------------------------------------------------------------
  -- CENS-INPUT: the input clause covers 5 shapes (shared completed,
  -- shared live, hot completed, hot live, cold[]).  Each shape is
  -- either a one-shot or a registration.  The full 9-conjunct result
  -- requires tracking which slot case fires (depends on sched at
  -- runtime) so a single all-cases postulate is used here.
  --
  -- Sub-obligations broken out below as commentary:
  --   (a) completed-shared / completed-hot: E′=E; INV unchanged;
  --       burstB/hasDry/burstHopD by computation; mintCount+1≤walkCap;
  --       burstLen=4≤walkCap; regsLen unchanged.
  --   (b) live-shared / live-hot: E′=2E (register-INV pays ×2);
  --       INV from register-INV; burstB/hasDry/burstHopD by computation;
  --       mintCount unchanged; burstLen=2≤walkCap; regsLen+1≤walkCap.
  --   (c) cold-sync []: same as emptyᵉ case (1 mint, burstLen=4).
  --   (d) cold-sync (d∷ds): 2 mints + burst + register; regsLen+1.
  --   (e) shared d → sharedConnect: delegates to the connect walk
  --       (a recursive call on d via dBound-connect edge; postulated).
  -- Classification: COMPLEX — each shape is provable individually;
  -- sharedConnect needs the connect edge from round3b.
  ------------------------------------------------------------------
  walk-core-input :
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (h-split : ∀ Ψ W Ω ℓ E B₀ R U r s →
        Σ ℕ λ V → Σ ℕ λ d →
          (dBound B₀ R U r s ≤ d) × (capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ d)) ≤ V))
    (h-r3b : ∀ p Ŝ R̂ U r s →
        Σ ℕ λ G →
            (dBound Ŝ R̂ U r s ≤ G)
          × (p + G ≤ p + G)
          × (∀ r″ s″ → r″ < r → s″ ≤ Ŝ → suc (dBound Ŝ R̂ U r″ s″) ≤ G)
          × (∀ U″ r″ s″ → U″ < U → r″ ≤ R̂ → s″ ≤ Ŝ → suc (dBound Ŝ R̂ U″ r″ s″) ≤ G)
          × (∀ s″ → s″ < s → suc (dBound Ŝ R̂ U r s″) ≤ G)
          × (∀ q G′ → q + suc G′ ≤ p + G → suc q + G′ ≤ p + G))
    (Ψ W Ω ℓ F Ŝ R̂ G : ℕ) (g : Gas) (i : Fin n)
    (b : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
    3 ≤ E →
    INV? Ψ (capᴱ W E) sched st ≡ true →
    sizeᵉ b ≤ capᴱ W E → fnCapᵉ b ≤ Ψ →
    pathB? (capᴱ W E) Ψ κ ≡ true →
    widthOK? Ω sched st ≡ true → ofWᵉ b ≤ Ω → pathΩ? Ω κ ≡ true →
    dBound Ŝ R̂ (unconn (Sched.slots sched) (EvalSt.connectedShares st))
           (hopDᵉ F b) (syncSizeᵉ b) ≤ G →
    g hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let r = subscribeE g b κ id now sched st
    in Σ ℕ λ E′ → (E ≤ E′)
       × (E′ ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ G))
       × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
       × (burstHopD? F (hopDᵉ F b) (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)
       × (mintCount (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
            ≤ mintCount sched st + walkCap Ω ℓ G)
       × (burstLen (proj₁ r) ≤ walkCap Ω ℓ G)
       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)

  ------------------------------------------------------------------
  -- CENS-PUSHBURST-WALK: after applying the IH (subscribeE-walk) to
  -- the inner call, pushBurst maps the walk-result across the frame.
  --
  -- Given:
  --   IH result at G_inner ≤ G (from hop/frame-crossing edges):
  --     E₀ , (E ≤ E₀) , (E₀ ≤ E*3^(Ψ*walkCap Ω ℓ G_inner)) ,
  --     (INV? Ψ (capᴱ W E₀) sched₁ st₁) ,
  --     (burstB? (capᴱ W E₀) Ψ burst₀) ,
  --     (burstHopD? F hopD_b burst₀) ,
  --     (hasDry burst₀ = false) ,
  --     (mintCount sched₁ st₁ ≤ mintCount_init + walkCap Ω ℓ G_inner) ,
  --     (burstLen burst₀ ≤ walkCap Ω ℓ G_inner) ,
  --     (regsLen? ℓ (registry st₁))
  --
  -- Then pushBurst g id now frame κ burst₀ sched₁ st₁ produces:
  --   E′ ≥ E₀, ceiling at G (not G_inner), all 9 conjuncts.
  --
  -- This postulate covers all three hop cases (mapᵉ, takeᵉ suc, scanᵉ).
  -- Classification: HARD — requires analysis of pushBurst's effect on
  -- each conjunct: INV (pushBurst-wet), ceiling monotonicity in G,
  -- burstHopD propagation, hasDry preservation, mintCount/burstLen
  -- recursion closed by walkCap's recurrence.
  ------------------------------------------------------------------
  walk-core-pushBurst-walk :
    ∀ {n} {Γ : Ctx n} {s t u} {e : Closed Γ t}
    (Ψ W Ω ℓ F G_inner G : ℕ) (g : Gas)
    (frame : Rx.Evaluator.Frame Γ s u)
    (κ : Path Γ u t) (id : Id) (now : Tick)
    (burst₀ : Stream Γ s) (sched₁ : Sched Γ) (st₁ : EvalSt e) (E E₀ : ℕ)
    (hopD_b : ℕ) →
    G_inner ≤ G →
    E ≤ E₀ →
    E₀ ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ G_inner) →
    INV? Ψ (capᴱ W E₀) sched₁ st₁ ≡ true →
    burstB? (capᴱ W E₀) Ψ burst₀ ≡ true →
    burstHopD? F hopD_b burst₀ ≡ true →
    hasDry burst₀ ≡ false →
    mintCount sched₁ st₁ ≤ mintCount sched₁ st₁ + walkCap Ω ℓ G_inner →
    burstLen burst₀ ≤ walkCap Ω ℓ G_inner →
    regsLen? ℓ (EvalSt.registry st₁) ≡ true →
    let r = pushBurst g id now frame κ burst₀ sched₁ st₁
    in Σ ℕ λ E′ → (E₀ ≤ E′)
       × (E′ ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ G))
       × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
       × (burstHopD? F hopD_b (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)
       × (mintCount (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
            ≤ mintCount sched₁ st₁ + walkCap Ω ℓ G)
       × (burstLen (proj₁ r) ≤ walkCap Ω ℓ G)
       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)

  ------------------------------------------------------------------
  -- CENS-SUBWALL: subscribeAll produces the 9-conjunct result.
  -- All four *All operators (merge/concat/switch/exhaust) share this.
  --
  -- Sub-obligations:
  --   • subscribeAll mints one node (mintNode → mintCount + 1)
  --   • applies subscribeE-walk to the *All source (hop edge fires:
  --     hopDᵉ F (mergeAllᵉ b) = suc (hopDᵉ F b) > hopDᵉ F b,
  --     so dBound-hop gives G_inner < G)
  --   • applies pushBurst-walk (frame = thru-outer op nid)
  --   • hasDry: pushBurst-hasDry preservation
  --   • burstHopD: the inner carries hopDᵉ F b, one level lower
  --     than hopDᵉ F (mergeAllᵉ b) — conjunct 5 holds at the outer
  --     hop depth by ≤ transitivity
  -- Classification: HARD — same category as pushBurst-walk above.
  ------------------------------------------------------------------
  walk-core-subscribeAll-walk :
    ∀ {n} {Γ : Ctx n} {t u} {e : Closed Γ t}
    (Ψ W Ω ℓ F Ŝ R̂ G : ℕ) (g : Gas) (op : AllOp)
    (b : Closed Γ (obs u))
    (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
    3 ≤ E →
    INV? Ψ (capᴱ W E) sched st ≡ true →
    sizeᵉ b ≤ capᴱ W E → fnCapᵉ b ≤ Ψ →
    pathB? (capᴱ W E) Ψ κ ≡ true →
    widthOK? Ω sched st ≡ true → ofWᵉ b ≤ Ω → pathΩ? Ω κ ≡ true →
    dBound Ŝ R̂ (unconn (Sched.slots sched) (EvalSt.connectedShares st))
           (hopDᵉ F b) (syncSizeᵉ b) ≤ G →
    g hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    -- IH: subscribeE-walk is available for the inner call on b
    -- (used inside the postulate's proof body; listed for the ledger)
    let r = subscribeAll g op (merge-st 0 false) b κ id now sched st
    in Σ ℕ λ E′ → (E ≤ E′)
       × (E′ ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ G))
       × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
       × (burstHopD? F (suc (hopDᵉ F b)) (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)
       × (mintCount (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
            ≤ mintCount sched st + walkCap Ω ℓ G)
       × (burstLen (proj₁ r) ≤ walkCap Ω ℓ G)
       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)

  ------------------------------------------------------------------
  -- CENS-MU-MONO: walkCap and mintCount bounds are monotone in G
  -- (needed to go from G_inner < G to G).
  --   walkCap Ω ℓ G_inner ≤ walkCap Ω ℓ G  when G_inner ≤ G.
  -- Classification: arithmetic / walkCap monotonicity — PROVABLE
  ------------------------------------------------------------------
  walkCap-mono-d : ∀ Ω ℓ {G_inner G : ℕ} →
    G_inner ≤ G → walkCap Ω ℓ G_inner ≤ walkCap Ω ℓ G

  ------------------------------------------------------------------
  -- CENS-DEFER: deferᵉ mints 3 counters, registers a chain, emits
  -- one burst.  The full 9-conjunct result requires:
  --   (a) INV after mintNode + mintSource + mintOrdinal + register
  --   (b) burstB for [(init src ∷ []) at id from src] — trivial
  --   (c) burstHopD for init event — trivial (init always true)
  --   (d) hasDry for this burst — trivial (no dried close)
  --   (e) mintCount + 3 ≤ walkCap (G ≥ 1)
  --   (f) burstLen = 2 ≤ walkCap (G ≥ 1)
  --   (g) regsLen after one registration ≤ ℓ (pathLen (thru-outer ↠ κ))
  -- Classification: MODERATE — (a) needs INV-mint chain; (g) needs
  -- walk-core-register-regsLen with pathLen computation.
  ------------------------------------------------------------------
  -- walk-core-deferᵉ-INV: caller passes db = deferᵉ body : Closed Γ u
  walk-core-deferᵉ-INV :
    ∀ {n} {Γ : Ctx n} {t u} {e : Closed Γ t}
    (Ψ W Ω ℓ F Ŝ R̂ G : ℕ) (g : Gas) (db : Closed Γ u)
    (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
    3 ≤ E →
    INV? Ψ (capᴱ W E) sched st ≡ true →
    sizeᵉ db ≤ capᴱ W E →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    1 ≤ G →
    let sched₁ = proj₁ (proj₂ (subscribeE g db κ id now sched st))
        st₁    = proj₂ (proj₂ (subscribeE g db κ id now sched st))
    in INV? Ψ (capᴱ W E) sched₁ st₁ ≡ true
       × regsLen? ℓ (EvalSt.registry st₁) ≡ true

----------------------------------------------------------------------
-- § 3  CENSUS LEMMAS — one per subscribeE clause
----------------------------------------------------------------------

----------------------------------------------------------------------
-- CLAUSE: emptyᵉ
-- subscribeE g emptyᵉ κ id now sched st = oneShotBurst [] id sched , st
--
-- Easy (by computation/refl): conjuncts 1, 3, 4, 5, 6, 9
-- Postulated:  conjunct 2 (E≤E*3^, provable), 7 (mintCount, provable),
--              8 (burstLen ≤ walkCap, provable)
----------------------------------------------------------------------
walk-core-emptyᵉ :
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W Ω ℓ F Ŝ R̂ G : ℕ) (g : Gas) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  1 ≤ capᴱ W E →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  widthOK? Ω sched st ≡ true → pathΩ? Ω κ ≡ true →
  dBound Ŝ R̂ (unconn (Sched.slots sched) (EvalSt.connectedShares st)) 0 1 ≤ G →
  g hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = subscribeE g emptyᵉ κ id now sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (E′ ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ G))
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
     × (burstHopD? F 0 (proj₁ r) ≡ true)
     × (hasDry (proj₁ r) ≡ false)
     × (mintCount (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
          ≤ mintCount sched st + walkCap Ω ℓ G)
     × (burstLen (proj₁ r) ≤ walkCap Ω ℓ G)
     × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
walk-core-emptyᵉ {u = u} Ψ W Ω ℓ F Ŝ R̂ G g κ id now sched st E
    h3≤E h-INV h-sz h-pB h-wOK h-pΩ h-dB h-hA h-pL h-rL =
  -- E′ = E  (emptyᵉ does not enlarge the store)
  E
  -- (1) E ≤ E  [≤-refl]
  , ≤-refl
  -- (2) E ≤ E * 3^(suc Ψ * walkCap Ω ℓ G)  [arithmetic: E≤E*3^]
  , E≤E*3^ E (suc Ψ * walkCap Ω ℓ G)
  -- (3) INV? at (sched₁, st)  [sched₁ = record sched { nextSource = _ };
  --     INV? does not use nextSource — definitional equality]
  , h-INV
  -- (4) burstB? for emptyᵉ burst  [all structural events → true; refl]
  , refl
  -- (5) burstHopD? F 0 for emptyᵉ  [hopDᵉ F emptyᵉ = 0; all events structural → true; refl]
  , refl
  -- (6) hasDry = false  [close src exhausted, not dried; refl]
  , refl
  -- (7) mintCount ≤ mintCount₀ + walkCap  [mintSource bumps by 1 ≤ walkCap; postulate]
  , walk-core-mintSource-mintCount Ω ℓ G sched st
  -- (8) burstLen ≤ walkCap  [burstLen=4; walkCap≥4 when G≥1,ℓ≥1; postulate]
  , walk-core-burstLen-empty Ω ℓ G id sched {u}
      (walk-core-G-pos {Ŝ = Ŝ} {R̂ = R̂} {U = unconn (Sched.slots sched) (EvalSt.connectedShares st)} {r = 0} {s = 1} h-dB)
      (walk-core-ℓ-pos (walk-core-G-pos {Ŝ = Ŝ} {R̂ = R̂} {U = unconn (Sched.slots sched) (EvalSt.connectedShares st)} {r = 0} {s = 1} h-dB) h-pL)
  -- (9) regsLen? from hypothesis  [st unchanged]
  , h-rL

----------------------------------------------------------------------
-- CLAUSE: ofᵉ ts
-- subscribeE g (ofᵉ ts) κ id now sched st =
--   oneShotBurst (map evalTm ts) id sched , st
--
-- Easy: conjuncts 1, 3, 6, 9
-- Postulated: 2 (E≤E*3^), 4 (burstB? for values), 5 (burstHopD?),
--             7 (mintSource-mintCount), 8 (burstLen with length ts ≤ capᴱ)
----------------------------------------------------------------------
walk-core-ofᵉ :
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W Ω ℓ F Ŝ R̂ G : ℕ) (g : Gas)
  (ts : List (Tm Γ [] [] [] u))
  (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  sizeᵉ (ofᵉ ts) ≤ capᴱ W E → fnCapᵉ (ofᵉ ts) ≤ Ψ →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  widthOK? Ω sched st ≡ true → ofWᵉ (ofᵉ ts) ≤ Ω → pathΩ? Ω κ ≡ true →
  dBound Ŝ R̂ (unconn (Sched.slots sched) (EvalSt.connectedShares st))
         (hopDᵉ F (ofᵉ ts)) (syncSizeᵉ (ofᵉ ts)) ≤ G →
  g hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = subscribeE g (ofᵉ ts) κ id now sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (E′ ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ G))
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
     × (burstHopD? F (hopDᵉ F (ofᵉ ts)) (proj₁ r) ≡ true)
     × (hasDry (proj₁ r) ≡ false)
     × (mintCount (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
          ≤ mintCount sched st + walkCap Ω ℓ G)
     × (burstLen (proj₁ r) ≤ walkCap Ω ℓ G)
     × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
walk-core-ofᵉ Ψ W Ω ℓ F Ŝ R̂ G g ts κ id now sched st E
    h3≤E h-INV h-sz h-fc h-pB h-wOK h-ofW h-pΩ h-dB h-hA h-pL h-rL =
  E
  , ≤-refl
  , E≤E*3^ E (suc Ψ * walkCap Ω ℓ G)
  , h-INV
  , walk-core-of-burstB Ψ W E id sched ts h3≤E h-sz h-fc
  , walk-core-of-burstHopD W E F id sched ts
  , walk-core-oneShotBurst-hasDry (Data.List.map Rx.Exp.evalTm ts) id sched
  , walk-core-mintSource-mintCount Ω ℓ G sched st
  , walk-core-burstLen-of Ω ℓ G (capᴱ W E) id sched
      (Data.List.map (λ tm → Rx.Exp.evalTm tm) ts)
      (walk-core-G-pos {Ŝ = Ŝ} {R̂ = R̂} {U = unconn (Sched.slots sched) (EvalSt.connectedShares st)} {r = hopDᵉ F (ofᵉ ts)} {s = syncSizeᵉ (ofᵉ ts)} h-dB)
      (walk-core-ℓ-pos (walk-core-G-pos {Ŝ = Ŝ} {R̂ = R̂} {U = unconn (Sched.slots sched) (EvalSt.connectedShares st)} {r = hopDᵉ F (ofᵉ ts)} {s = syncSizeᵉ (ofᵉ ts)} h-dB) h-pL)
      (≤-trans (≤-trans (≤-reflexive (length-map _ ts)) (sizeᵗˢ≤sizeᵉ ts)) h-sz)
      (walk-core-capᴱ-lb4 W E h3≤E)
  , h-rL

----------------------------------------------------------------------
-- CLAUSE: takeᵉ count b | evalTm count = zero
-- subscribeE g (takeᵉ count b) κ ... with evalTm count | zero =
--   oneShotBurst [] id sched , st
--
-- Easy: same as emptyᵉ case.  Classified as trivial.
----------------------------------------------------------------------
walk-core-takeᵉ-zero :
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W Ω ℓ F Ŝ R̂ G : ℕ) (g : Gas)
  (count : Tm Γ [] [] [] natᵗ) (b : Closed Γ u)
  (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  Rx.Exp.evalTm count ≡ zero →   -- branch condition
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  sizeᵉ (takeᵉ count b) ≤ capᴱ W E → fnCapᵉ (takeᵉ count b) ≤ Ψ →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  widthOK? Ω sched st ≡ true → ofWᵉ (takeᵉ count b) ≤ Ω → pathΩ? Ω κ ≡ true →
  dBound Ŝ R̂ (unconn (Sched.slots sched) (EvalSt.connectedShares st))
         (hopDᵉ F (takeᵉ count b)) (syncSizeᵉ (takeᵉ count b)) ≤ G →
  g hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = subscribeE g (takeᵉ count b) κ id now sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (E′ ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ G))
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
     × (burstHopD? F (hopDᵉ F (takeᵉ count b)) (proj₁ r) ≡ true)
     × (hasDry (proj₁ r) ≡ false)
     × (mintCount (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
          ≤ mintCount sched st + walkCap Ω ℓ G)
     × (burstLen (proj₁ r) ≤ walkCap Ω ℓ G)
     × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
walk-core-takeᵉ-zero {u = u} Ψ W Ω ℓ F Ŝ R̂ G g count b κ id now sched st E
    h-zero h3≤E h-INV h-sz h-fc h-pB h-wOK h-ofW h-pΩ h-dB h-hA h-pL h-rL
  rewrite h-zero =
  E , ≤-refl , E≤E*3^ E (suc Ψ * walkCap Ω ℓ G) , h-INV , refl , refl , refl
  , walk-core-mintSource-mintCount Ω ℓ G sched st
  , walk-core-burstLen-empty Ω ℓ G id sched {u}
      (walk-core-G-pos {Ŝ = Ŝ} {R̂ = R̂} {U = unconn (Sched.slots sched) (EvalSt.connectedShares st)} {r = hopDᵉ F (takeᵉ count b)} {s = syncSizeᵉ (takeᵉ count b)} h-dB)
      (walk-core-ℓ-pos (walk-core-G-pos {Ŝ = Ŝ} {R̂ = R̂} {U = unconn (Sched.slots sched) (EvalSt.connectedShares st)} {r = hopDᵉ F (takeᵉ count b)} {s = syncSizeᵉ (takeᵉ count b)} h-dB) h-pL)
  , h-rL

----------------------------------------------------------------------
-- CLAUSE: μᵉ body | g0
-- subscribeE g0 (μᵉ body) κ id now sched st = dryBurst id , sched , st
--
-- The hypothesis g0 hasAtLeast suc G is absurd (no constructor
-- for g0 hasAtLeast (suc _)).  All conjuncts follow by ⊥-elim.
----------------------------------------------------------------------

g0-hasAtLeast-absurd : ∀ {G} → g0 hasAtLeast suc G → ⊥
g0-hasAtLeast-absurd ()

walk-core-μᵉ-g0 :
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W Ω ℓ F Ŝ R̂ G : ℕ)
  (body : Rx.Exp.Exp Γ (u ∷ []) [] [] u)
  (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  sizeᵉ (μᵉ body) ≤ capᴱ W E → fnCapᵉ (μᵉ body) ≤ Ψ →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  widthOK? Ω sched st ≡ true → ofWᵉ (μᵉ body) ≤ Ω → pathΩ? Ω κ ≡ true →
  dBound Ŝ R̂ (unconn (Sched.slots sched) (EvalSt.connectedShares st))
         (hopDᵉ F (μᵉ body)) (syncSizeᵉ (μᵉ body)) ≤ G →
  g0 hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = subscribeE g0 (μᵉ body) κ id now sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (E′ ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ G))
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
     × (burstHopD? F (hopDᵉ F (μᵉ body)) (proj₁ r) ≡ true)
     × (hasDry (proj₁ r) ≡ false)
     × (mintCount (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
          ≤ mintCount sched st + walkCap Ω ℓ G)
     × (burstLen (proj₁ r) ≤ walkCap Ω ℓ G)
     × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
walk-core-μᵉ-g0 _ _ _ _ _ _ _ _ body _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h-hA _ _ =
  ⊥-elim (g0-hasAtLeast-absurd h-hA)

----------------------------------------------------------------------
-- CLAUSE: μᵉ body | gs fuel
-- subscribeE (gs fuel) (μᵉ body) κ id now sched st
--   = subscribeE fuel (unfoldμ body) κ id now sched st
--
-- The IH (subscribeE-walk) is applied to unfoldμ body with a smaller G:
--   G′ = dBound Ŝ R̂ U (hopDᵉ F body) (syncSizeᵉ (unfoldμ body))
--   suc G′ ≤ G  [from round3b's μ-edge: s′ = syncSizeᵉ (unfoldμ body) < syncSizeᵉ (μᵉ body) = s]
--
-- After IH, ceiling at G′ → ceiling at G by walkCap-mono-d.
-- mintCount and burstLen bounds at G′ → G by walkCap-mono-d.
--
-- Sub-postulates:
--   walk-core-μ-dBound-inner  — derives G′ and G′ < G from μ-edge
--   walk-core-μ-hasAtLeast    — from gs fuel hasAtLeast suc G to fuel hasAtLeast suc G′
--   walkCap-mono-d            — [already postulated above]
--
-- Classification: MODERATE — requires μ-edge from round3b plus
-- hasAtLeast monotonicity.
----------------------------------------------------------------------

postulate
  walk-core-μ-dBound-inner :
    ∀ {n} {Γ : Ctx n} {t u} (F Ŝ R̂ G : ℕ)
    (body : Rx.Exp.Exp Γ (u ∷ []) [] [] u)
    (sched : Sched Γ) {e : Closed Γ t} (st : EvalSt e) →
    dBound Ŝ R̂ (unconn (Sched.slots sched) (EvalSt.connectedShares st))
           (hopDᵉ F (μᵉ body)) (syncSizeᵉ (μᵉ body)) ≤ G →
    Σ ℕ λ G′ →
        suc G′ ≤ G
      × dBound Ŝ R̂ (unconn (Sched.slots sched) (EvalSt.connectedShares st))
               (hopDᵉ F (unfoldμ body)) (syncSizeᵉ (unfoldμ body)) ≤ G′

  walk-core-μ-hasAtLeast :
    ∀ {fuel : Gas} {G G′ : ℕ} →
    gs fuel hasAtLeast suc G →
    suc G′ ≤ G →
    fuel hasAtLeast suc G′

  -- unfoldμ body: size bounded by capᴱ W E (via size-unfoldμ + h-sz)
  walk-core-μ-sz :
    ∀ {n} {Γ : Ctx n} {t u} {e : Closed Γ t}
    (Ψ W E : ℕ) (body : Rx.Exp.Exp Γ (u ∷ []) [] [] u)
    (sched : Sched Γ) (st : EvalSt e) →
    sizeᵉ (μᵉ body) ≤ capᴱ W E →
    INV? Ψ (capᴱ W E) sched st ≡ true →
    sizeᵉ (unfoldμ body) ≤ capᴱ W E

  -- unfoldμ body: fnCap bounded (via fnCap-elimG)
  walk-core-μ-fc :
    ∀ {n} {Γ : Ctx n} {u} (Ψ E : ℕ)
    (body : Rx.Exp.Exp Γ (u ∷ []) [] [] u) →
    fnCapᵉ (μᵉ body) ≤ Ψ →
    fnCapᵉ (unfoldμ body) ≤ Ψ

  -- unfoldμ body: ofWᵉ = ofWᵉ body = ofWᵉ (μᵉ body)
  walk-core-μ-ofW :
    ∀ {n} {Γ : Ctx n} {u} (Ω : ℕ)
    (body : Rx.Exp.Exp Γ (u ∷ []) [] [] u) →
    ofWᵉ (μᵉ body) ≤ Ω →
    ofWᵉ (unfoldμ body) ≤ Ω

  -- hopDᵉ of unfoldμ body equals hopDᵉ of body itself
  -- (substituting a closed term doesn't change hop depth)
  -- Classification: structural/substitution lemma — PROVABLE
  walk-core-μ-hopD :
    ∀ {n} {Γ : Ctx n} {u} (F : ℕ)
    (body : Rx.Exp.Exp Γ (u ∷ []) [] [] u) →
    hopDᵉ F (unfoldμ body) ≡ hopDᵉ F body

walk-core-μᵉ-gs :
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W Ω ℓ F Ŝ R̂ G : ℕ) (fuel : Gas)
  (body : Rx.Exp.Exp Γ (u ∷ []) [] [] u)
  (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  sizeᵉ (μᵉ body) ≤ capᴱ W E → fnCapᵉ (μᵉ body) ≤ Ψ →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  widthOK? Ω sched st ≡ true → ofWᵉ (μᵉ body) ≤ Ω → pathΩ? Ω κ ≡ true →
  dBound Ŝ R̂ (unconn (Sched.slots sched) (EvalSt.connectedShares st))
         (hopDᵉ F (μᵉ body)) (syncSizeᵉ (μᵉ body)) ≤ G →
  gs fuel hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = subscribeE (gs fuel) (μᵉ body) κ id now sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (E′ ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ G))
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
     × (burstHopD? F (hopDᵉ F (μᵉ body)) (proj₁ r) ≡ true)
     × (hasDry (proj₁ r) ≡ false)
     × (mintCount (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
          ≤ mintCount sched st + walkCap Ω ℓ G)
     × (burstLen (proj₁ r) ≤ walkCap Ω ℓ G)
     × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
walk-core-μᵉ-gs {n = n} {Γ = Γ} {t = t} {e = e} {u = u}
    Ψ W Ω ℓ F Ŝ R̂ G fuel body κ id now sched st E
    h3≤E h-INV h-sz h-fc h-pB h-wOK h-ofW h-pΩ h-dB h-hA h-pL h-rL =
  -- Step 1: extract G′ from the μ-edge
  let G′    = proj₁ (walk-core-μ-dBound-inner F Ŝ R̂ G body sched st h-dB)
      sucG′≤G = proj₁ (proj₂ (walk-core-μ-dBound-inner F Ŝ R̂ G body sched st h-dB))
      h-dB′  = proj₂ (proj₂ (walk-core-μ-dBound-inner F Ŝ R̂ G body sched st h-dB))
      h-hA′  = walk-core-μ-hasAtLeast h-hA sucG′≤G
      -- pathLen κ + G′ ≤ ℓ: G′ < G and outer gives pathLen κ + G ≤ ℓ
      h-pL′  : pathLen κ + G′ ≤ ℓ
      h-pL′  = ≤-trans (Data.Nat.Properties.+-monoʳ-≤ (pathLen κ) (≤-trans (n≤1+n G′) sucG′≤G)) h-pL
      -- IH: apply subscribeE-walk to unfoldμ body at G′
      -- Note: subscribeE (gs fuel) (μᵉ body) = subscribeE fuel (unfoldμ body) definitionally
      -- Additional hypotheses needed for unfoldμ body:
      --   sizeᵉ (unfoldμ body) ≤ capᴱ W E  [from size-unfoldμ + h-sz]
      --   fnCapᵉ (unfoldμ body) ≤ Ψ        [from fnCap-elimG + h-fc]
      --   ofWᵉ (unfoldμ body) ≤ Ω           [from ofWᵉ (μᵉ body) = ofWᵉ body]
      -- These are postulated via walk-core-μ-sz/fc/ofW
      IH    = subscribeE-walk Ψ W Ω ℓ F Ŝ R̂ G′ fuel (unfoldμ body) κ id now sched st E
                h3≤E h-INV
                (walk-core-μ-sz Ψ W E body sched st h-sz h-INV)
                (walk-core-μ-fc Ψ E body h-fc)
                h-pB h-wOK
                (walk-core-μ-ofW Ω body h-ofW)
                h-pΩ h-dB′ h-hA′ h-pL′ h-rL
      E₀    = proj₁ IH
      h1    = proj₁ (proj₂ IH)
      h2    = proj₁ (proj₂ (proj₂ IH))
      h3    = proj₁ (proj₂ (proj₂ (proj₂ IH)))
      h4    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))
      h5    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
      h6    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))
      h7    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))))
      h8    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))))
      h9    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))))
      -- definitionally: subscribeE (gs fuel) (μᵉ body) ... = subscribeE fuel (unfoldμ body) ...
      stream = proj₁ (subscribeE (gs fuel) (μᵉ body) κ id now sched st)
  in E₀ , h1
  -- conjunct 2: ceiling at G′ → ceiling at G by walkCap-mono-d
  , ≤-trans h2 (Data.Nat.Properties.*-monoʳ-≤ E
      (Data.Nat.Properties.^-monoʳ-≤ 3
        (Data.Nat.Properties.*-monoʳ-≤ (suc Ψ) (walkCap-mono-d Ω ℓ (≤-trans (n≤1+n G′) sucG′≤G)))))
  , h3 , h4
  -- conjunct 5: rewrite hopDᵉ F (unfoldμ body) to hopDᵉ F body = hopDᵉ F (μᵉ body) (definitional)
  , subst (λ d → burstHopD? F d stream ≡ true) (walk-core-μ-hopD F body) h5
  , h6
  -- conjunct 7: mintCount at G′ → G by walkCap-mono-d + ≤-trans
  , ≤-trans h7 (Data.Nat.Properties.+-monoʳ-≤ (mintCount sched st) (walkCap-mono-d Ω ℓ (≤-trans (n≤1+n G′) sucG′≤G)))
  -- conjunct 8: burstLen at G′ → G
  , ≤-trans h8 (walkCap-mono-d Ω ℓ (≤-trans (n≤1+n G′) sucG′≤G))
  , h9

----------------------------------------------------------------------
-- CLAUSE: mapᵉ f b
-- subscribeE g (mapᵉ f b) κ id now sched st =
--   pushBurst g id now (map-f f) κ (subscribeE g b (map-f f ↠ κ) ...) ...
--
-- IH applied to b at G_inner (frame-crossing: G_inner = G-1 from pathLen+1 side,
-- OR same G if dBound of b < dBound of mapᵉ f b).
-- Then walk-core-pushBurst-walk closes the result.
--
-- Sub-postulates beyond walk-core-pushBurst-walk:
--   walk-core-mapᵉ-dBound-inner  — derives dBound for b ≤ G (or G-1)
--   walk-core-mapᵉ-pathLen       — derives pathLen (map-f f ↠ κ) + G_inner ≤ ℓ
--   walk-core-mapᵉ-sz/fc         — size/fnCap of b from mapᵉ f b
--   walk-core-mapᵉ-ofW           — ofWᵉ b from ofWᵉ (mapᵉ f b)
--
-- Classification: HARD (IH setup + pushBurst-walk)
----------------------------------------------------------------------

postulate
  walk-core-mapᵉ-all :
    ∀ {n} {Γ : Ctx n} {t s u} {e : Closed Γ t}
    (Ψ W Ω ℓ F Ŝ R̂ G : ℕ) (g : Gas)
    (f : Fn Γ [] [] [] (obs s) u) (b : Closed Γ (obs s))
    (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
    3 ≤ E →
    INV? Ψ (capᴱ W E) sched st ≡ true →
    sizeᵉ (mapᵉ f b) ≤ capᴱ W E → fnCapᵉ (mapᵉ f b) ≤ Ψ →
    pathB? (capᴱ W E) Ψ κ ≡ true →
    widthOK? Ω sched st ≡ true → ofWᵉ (mapᵉ f b) ≤ Ω → pathΩ? Ω κ ≡ true →
    dBound Ŝ R̂ (unconn (Sched.slots sched) (EvalSt.connectedShares st))
           (hopDᵉ F (mapᵉ f b)) (syncSizeᵉ (mapᵉ f b)) ≤ G →
    g hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let r = subscribeE g (mapᵉ f b) κ id now sched st
    in Σ ℕ λ E′ → (E ≤ E′)
       × (E′ ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ G))
       × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
       × (burstHopD? F (hopDᵉ F (mapᵉ f b)) (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)
       × (mintCount (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
            ≤ mintCount sched st + walkCap Ω ℓ G)
       × (burstLen (proj₁ r) ≤ walkCap Ω ℓ G)
       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)

  walk-core-takeᵉ-suc-all :
    ∀ {n} {Γ : Ctx n} {t u} {e : Closed Γ t}
    (Ψ W Ω ℓ F Ŝ R̂ G k : ℕ) (g : Gas)
    (count : Tm Γ [] [] [] natᵗ) (b : Closed Γ u)
    (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
    Rx.Exp.evalTm count ≡ suc k →
    3 ≤ E →
    INV? Ψ (capᴱ W E) sched st ≡ true →
    sizeᵉ (takeᵉ count b) ≤ capᴱ W E → fnCapᵉ (takeᵉ count b) ≤ Ψ →
    pathB? (capᴱ W E) Ψ κ ≡ true →
    widthOK? Ω sched st ≡ true → ofWᵉ (takeᵉ count b) ≤ Ω → pathΩ? Ω κ ≡ true →
    dBound Ŝ R̂ (unconn (Sched.slots sched) (EvalSt.connectedShares st))
           (hopDᵉ F (takeᵉ count b)) (syncSizeᵉ (takeᵉ count b)) ≤ G →
    g hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let r = subscribeE g (takeᵉ count b) κ id now sched st
    in Σ ℕ λ E′ → (E ≤ E′)
       × (E′ ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ G))
       × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
       × (burstHopD? F (hopDᵉ F (takeᵉ count b)) (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)
       × (mintCount (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
            ≤ mintCount sched st + walkCap Ω ℓ G)
       × (burstLen (proj₁ r) ≤ walkCap Ω ℓ G)
       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)

  walk-core-scanᵉ-all :
    ∀ {n} {Γ : Ctx n} {t u} {e : Closed Γ t}
    (Ψ W Ω ℓ F Ŝ R̂ G : ℕ) (g : Gas)
    (f : Fn Γ [] [] [] (u ×ᵗ u) u) (seed : Tm Γ [] [] [] u) (b : Closed Γ u)
    (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
    3 ≤ E →
    INV? Ψ (capᴱ W E) sched st ≡ true →
    sizeᵉ (scanᵉ f seed b) ≤ capᴱ W E → fnCapᵉ (scanᵉ f seed b) ≤ Ψ →
    pathB? (capᴱ W E) Ψ κ ≡ true →
    widthOK? Ω sched st ≡ true → ofWᵉ (scanᵉ f seed b) ≤ Ω → pathΩ? Ω κ ≡ true →
    dBound Ŝ R̂ (unconn (Sched.slots sched) (EvalSt.connectedShares st))
           (hopDᵉ F (scanᵉ f seed b)) (syncSizeᵉ (scanᵉ f seed b)) ≤ G →
    g hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let r = subscribeE g (scanᵉ f seed b) κ id now sched st
    in Σ ℕ λ E′ → (E ≤ E′)
       × (E′ ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ G))
       × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
       × (burstHopD? F (hopDᵉ F (scanᵉ f seed b)) (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)
       × (mintCount (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
            ≤ mintCount sched st + walkCap Ω ℓ G)
       × (burstLen (proj₁ r) ≤ walkCap Ω ℓ G)
       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)

  -- walk-core-deferᵉ-all: caller passes db = deferᵉ body : Closed Γ u
  walk-core-deferᵉ-all :
    ∀ {n} {Γ : Ctx n} {t u} {e : Closed Γ t}
    (Ψ W Ω ℓ F Ŝ R̂ G : ℕ) (g : Gas)
    (db : Closed Γ u)
    (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
    3 ≤ E →
    INV? Ψ (capᴱ W E) sched st ≡ true →
    sizeᵉ db ≤ capᴱ W E → fnCapᵉ db ≤ Ψ →
    pathB? (capᴱ W E) Ψ κ ≡ true →
    widthOK? Ω sched st ≡ true → ofWᵉ db ≤ Ω → pathΩ? Ω κ ≡ true →
    dBound Ŝ R̂ (unconn (Sched.slots sched) (EvalSt.connectedShares st))
           (hopDᵉ F db) (syncSizeᵉ db) ≤ G →
    g hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let r = subscribeE g db κ id now sched st
    in Σ ℕ λ E′ → (E ≤ E′)
       × (E′ ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ G))
       × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
       × (burstHopD? F (hopDᵉ F db) (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)
       × (mintCount (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
            ≤ mintCount sched st + walkCap Ω ℓ G)
       × (burstLen (proj₁ r) ≤ walkCap Ω ℓ G)
       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)

----------------------------------------------------------------------
-- CLAUSE: *All cases (merge/concat/switch/exhaust)
-- All four share the same shape: subscribeAll g op ns b κ ...
-- Delegated entirely to walk-core-subscribeAll-walk.
-- (Each op may have different op-specific postulates inside the
-- subscribeAll analysis, but the outer census lemma is the same.)
--
-- The *All census lemmas are simply projections of the postulate
-- walk-core-subscribeAll-walk specialised to the specific op and ns.
----------------------------------------------------------------------

-- mergeAllᵉ
walk-core-mergeAllᵉ :
  ∀ {n} {Γ : Ctx n} {t u} {e : Closed Γ t}
  (Ψ W Ω ℓ F Ŝ R̂ G : ℕ) (g : Gas)
  (b : Closed Γ (obs u))
  (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  sizeᵉ (mergeAllᵉ b) ≤ capᴱ W E → fnCapᵉ (mergeAllᵉ b) ≤ Ψ →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  widthOK? Ω sched st ≡ true → ofWᵉ (mergeAllᵉ b) ≤ Ω → pathΩ? Ω κ ≡ true →
  dBound Ŝ R̂ (unconn (Sched.slots sched) (EvalSt.connectedShares st))
         (hopDᵉ F (mergeAllᵉ b)) (syncSizeᵉ (mergeAllᵉ b)) ≤ G →
  g hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = subscribeE g (mergeAllᵉ b) κ id now sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (E′ ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ G))
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
     × (burstHopD? F (hopDᵉ F (mergeAllᵉ b)) (proj₁ r) ≡ true)
     × (hasDry (proj₁ r) ≡ false)
     × (mintCount (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
          ≤ mintCount sched st + walkCap Ω ℓ G)
     × (burstLen (proj₁ r) ≤ walkCap Ω ℓ G)
     × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
walk-core-mergeAllᵉ Ψ W Ω ℓ F Ŝ R̂ G g b κ id now sched st E
    h3≤E h-INV h-sz h-fc h-pB h-wOK h-ofW h-pΩ h-dB h-hA h-pL h-rL =
  let IH = walk-core-subscribeAll-walk Ψ W Ω ℓ F Ŝ R̂ G g mergeᵒ b κ id now sched st E
             h3≤E h-INV
             (≤-trans (n≤1+n (sizeᵉ b)) h-sz)
             h-fc
             h-pB h-wOK h-ofW h-pΩ
             (≤-trans (n≤1+n _) (≤-trans (dBound-struct Ŝ R̂ (unconn (Sched.slots sched) (EvalSt.connectedShares st)) (n≤1+n (hopDᵉ F b)) ≤-refl) h-dB))
             h-hA h-pL h-rL
  in proj₁ IH , proj₁ (proj₂ IH) , proj₁ (proj₂ (proj₂ IH))
     , proj₁ (proj₂ (proj₂ (proj₂ IH)))
     , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))
     , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
     , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))
     , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))))
     , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))))
     , proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))))

----------------------------------------------------------------------
-- § 6  CENSUS LEDGER
--
-- SUMMARY of all census postulates and their classifications:
--
-- PROVABLE ARITHMETIC (no new mathematical content needed):
--   walk-core-mintSource-mintCount   — mintCount + 1 ≤ mintCount₀ + walkCap
--   walk-core-2mints-mintCount       — mintCount + 2 ≤ mintCount₀ + walkCap
--   walk-core-3mints-mintCount       — mintCount + 3 ≤ mintCount₀ + walkCap (G≥1)
--   walk-core-burstLen-empty         — 4 ≤ walkCap (G≥1, ℓ≥1)
--   walk-core-burstLen-of            — suc(2+|vs|) ≤ walkCap (|vs| ≤ B)
--   walk-core-burstLen-defer         — 2 ≤ walkCap (G≥1, ℓ≥1)
--   walkCap-mono-d                   — walkCap monotone in G
--   walk-core-μ-dBound-inner         — μ-edge: G′ from syncSizeᵉ(unfoldμ) < syncSizeᵉ(μ)
--   walk-core-μ-hasAtLeast           — hasAtLeast-mono for μ case
--
-- PROVABLE BY EXISTING LEMMAS (references to existing src theorems):
--   walk-core-of-burstB             — ofVals-B (already in Wet.agda)
--   walk-core-of-burstHopD          — hop-depth of closed terms = 0
--   walk-core-register-regsLen      — register adds one entry; pathLen ≤ ℓ
--   walk-core-μ-sz                  — size-unfoldμ + capᴱ-square (in Measures)
--   walk-core-μ-fc                  — fnCap-elimG (in Wet.agda)
--   walk-core-μ-ofW                 — ofWᵉ (unfoldμ) = ofWᵉ body = ofWᵉ (μᵉ) (trivial)
--
-- HARD (new proof work required):
--   walk-core-pushBurst-walk        — pushBurst preserves all 9 conjuncts after IH;
--                                     closes the walkCap recurrence per clause
--   walk-core-subscribeAll-walk     — subscribeAll walk: hop-edge + IH + pushBurst
--
-- COMPLEX (covers multiple sub-cases with runtime branches):
--   walk-core-input                 — 5 slot shapes, one of which is recursive
--   walk-core-deferᵉ-INV            — INV after 3 mints + register
--
-- ENTIRE-CLAUSE POSTULATES (used directly as census lemmas):
--   walk-core-mapᵉ-all             — mapᵉ: IH + pushBurst-walk
--   walk-core-takeᵉ-suc-all        — takeᵉ suc k: mintNode + IH + pushBurst-walk
--   walk-core-scanᵉ-all            — scanᵉ: mintNode + scan-seed + IH + pushBurst-walk
--   walk-core-deferᵉ-all           — deferᵉ: 3 mints + register + burst
----------------------------------------------------------------------
