-- THE WALK FACE AS A TYPE — every statement the collapsed walk is
-- written over, and nothing that proves anything about them.  The face
-- itself, its clause leaves and its dispatch live one module up.
--
-- WHY IT IS SEPARATE, and it is a checking-cost argument rather than a
-- taste one.  The walk's dispatch is one genuine mutual cycle, and a
-- mutual block is an indivisible checking unit: every focused check of
-- any member re-pays for whatever else shares the module.  These
-- telescopes are large, they are pure Set-valued abbreviation, and
-- nothing in the cycle needs them RE-CHECKED to check itself — an
-- import is enough.  Moving them out is therefore free to the proof and
-- takes the per-member iteration loop back under its budget, which is
-- the difference between grinding a clause in seconds and in a minute.
--
-- WHAT BELONGS HERE: a definition that mentions no lemma — the shared
-- telescopes, the record of proven edges the dispatch is narrowed over,
-- the gas peel, and the clause leaves, which are postulates and so
-- cannot be part of any cycle by construction.  Anything with a proof
-- body that the cycle consumes belongs in the shelf module beside this
-- one; anything IN the cycle belongs with the dispatch.
--
-- Re-exported `public` all the way up, so no consumer downstream can
-- tell these moved.

module Verify-Budget-Sufficient.Walk-Level.Statement where

open import Data.Bool    using (Bool; T; true; false; _∨_; _∧_; not; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _<_;
                                _≤ᵇ_; _<ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.List    using (List; []; _∷_; _++_; length; map)
open import Data.Unit    using (⊤; tt)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; ≤-pred;
                                       m≤m+n; m≤n+m; n≤1+n;
                                       +-suc; +-assoc; +-comm;
                                       +-mono-≤; +-monoʳ-≤; +-monoˡ-≤;
                                       *-mono-≤; *-monoʳ-≤;
                                       +-identityʳ;
                                       m≤m⊔n; m≤n⊔m; ≤⇒≤ᵇ; ≤ᵇ⇒≤)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Bool.ListAction using (all; any)
open import Data.Fin     using (Fin; toℕ)
open import Data.Vec     using (Vec; lookup)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (yes; no)

open import Rx.Prim      using (Tick; Id; Source; init; value; close;
                                complete; handoff; exhausted; dried;
                                cut; cutPending; subscribe;
                                InstEmit; InstEvent; _at_from_as_;
                                Gas; g0; gs; gasPad; ObservableInput; hot; cold)
open import Rx.Exp       using (Ty; obs; natᵗ; _×ᵗ_; Ctx; Closed; Val; Exp; Tm; Fn;
                                inputsBelowᵉ; isData;
                                _≟ᵗ_;
                                sizeᵉ; sizeᵗ; sizeᵛ; syncSizeᵉ;
                                shellSizeᵉ; innerᵉ;
                                input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                                mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                                μᵉ; varᵉ; deferᵉ; unfoldμ; applyFn; evalTm)
open import Rx.Frame-Width using (dWᵉ; pWᵉ; pWᵛ)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵛ; pmᵗ; hopD-unfoldμ)
open import Rx.Slot-Hop  using (slotHop; slotHop-fix)
open import Rx.Evaluator using (Sched; EvalSt; Slots; Slot; shared; scripted;
                                RegId; Chain;
                                memberSource; Path; root; share-sink; _↠_;
                                Stream; subscribeE; sharedConnect;
                                subscribeAll; AllOp;
                                mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ;
                                NodeState; merge-st; concat-st;
                                switch-st; exhaust-st; scan-st; take-st;
                                scan-f; take-f;
                                splitBurst; hasDry; dryEvent;
                                burstCompleted; sharedPlumb; dropSource;
                                sched-init; st-init; budgetAt; slotsSize;
                                opIterD; fIterD; fLvlD; sLvlD; sIterD; sizeAt;
                                sLvlD-suc; opIterD-suc; sIterD-suc; fLvlD-suc; fLvl; widAt;
                                Frame; thru-outer; from-inner;
                                pushBurst; stepFrame;
                                subscribeInner; splitEvents; retagEvents;
                                thruConsume; thruWalk; thruWrap;
                                mergeBump; switchKill; cutThrough; sweepLive;
                                lookupNode; setNode; pathHasNode; LiveSource;
                                sameSource; installNode; NodeId; register; mintNode)

-- the wet stratum: INV?, dBound, hasAtLeast, regsLen?, pathLen, the gas
-- edges, sizeCapAt, capsAt/capsH/frameStep/Caps (via .Caps), the
-- Keeps ring, and every companion the core is narrowed over
open import Verify-Budget-Sufficient.Wet
-- the caps face: only the five predicates the statement reads there
open import Verify-Budget-Sufficient.Caps-Face
  using (capsOK?; burstCaps?; burstCount?; pathSz?; slotsCaps?; nest;
         widNode; merge-step; concat-step; switch-step; exhaust-step;
         frameSz?; capsOK?-mono; capsOK?-setNode; capsOK?-nextNode;
         pathSz?-⊑; frameStep-chain-suc; frameStep-⊑-+;
         valCaps?; valsCaps?; eventCaps?; valCountᵉ; frameBud;
         mapValue-caps; valsCaps?-widen; finList-caps;
         splitEvents-valsCaps; splitEvents-bk-caps; burstCaps?-widen;
         capsOK?-mergeBump; switchKill-caps; switchKill-closes-caps;
         lookupNode-caps; capsOK?-nodeSz; capsOK?-nodeWid;
         thruWrap-caps; mList?; mList?-head; mList?-tail; mList?-keeps;
         valsCaps→mList-strict; splitBurst-vals-caps; splitBurst-bk-caps;
         widNode-push; valCaps?-size; valCaps?-wid; eventsCaps?-widen;
         frameStep-size-strict-suc;
         capsOK?-regs; pathSz?-len;
         slotsCaps?-capsAt; capsOK?-parts)
open import Verify-Budget-Sufficient.Psi-Split
-- the chain-charge algebra subscribeE-caps' own *All head spends
open import Verify-Budget-Sufficient.Caps-Chain
  using (chain-desc; op-step; burst-index; burst-nil; burst-step;
         op-step-mu; quad-arith;
         op-desc; push-desc; frame-desc; tail-desc;
         walk-desc; inner-desc;
         inner-nil; inner-step; walk-nil;
         frame-step; walk-index; queue-push)
open import Verify-Budget-Sufficient.Caps-Sadd
  using (walk-step-suc)
-- the transformer monotonicity/inflation family, cited directly by the
-- loop faces' ceiling conversions
open import Verify-Budget-Sufficient.Caps
  using (opIterD-mono; sIterD-mono; sLvlD-infl; sIterD-infl;
         sLvlD-mono; opIterD-infl; fIterD-infl;
         B2-cReg≤cSize; frameStep-reg≤size;
         capsAt-base-size)
-- proven projections and per-emit plumbing off the caps push face —
-- pieces, never the face itself (the wet twin re-walks its skeleton
-- so both halves share one witness)
open import Verify-Budget-Sufficient.Subscribe-Face
  using (unfoldμ-caps; subscribeE-caps; countLen; countVals; countIn; valsOf; pushEmit-count;
         pushBurst-len; retagEvents-caps;
         burstCount?-widen; burstCount?-tail;
         thruWrap-vals; splitBurst-len; mul-fits; valsIn; valsLen;
         lenWiden; frameStep-+suc; concat-fits)
open import Verify-Budget-Sufficient.Hop-Spine-Face
  using (burstHopSpn?; burstHopSpn-cap; burstHopSpnH?; burstHopSpnH-headline;
         burstHopSpnH-intro; scanSeed-hopSpn)
open import Verify-Budget-Sufficient.Hop-Spine-Push
  using (scanAccSpn?; nodeAccSpn?; nodeAccSpn?-scan; pushBurst-scan-hopSpn)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthE; depthAll; depthBurst; depthFrame; depthInner;
         depthConsume; depthWalk; depthSlot; depthConn)
open import Verify-Budget-Sufficient.Caps-Nest
  using (nest-keeps; mu-step)
open import Verify-Budget-Sufficient.Op-Budget
  using (opIterD-dominated)

-- `input i` WITH ITS Exp INDICES PINNED.  Written bare in a postulate's
-- type the guarded/value/parked contexts are metavariables — only
-- `Closed` forces them to `[]`, and WalkStmt gets that for free from its
-- own `b : Closed Γ u`.  A postulate has no such binder, so the six
-- conjuncts mentioning the expression each raise an unsolved meta.
inputᶜ : ∀ {n} {Γ : Ctx n} (i : Fin n) → Exp Γ [] [] [] (lookup Γ i)
inputᶜ i = input i


-- THE WALK FACE AND ITS CORE, as types — named once so that neither
-- the face nor the assembly that consumes it has to retype the
-- statement.  All sit above the postulate block because a postulate
-- cannot reference a definition below it.
--
-- WalkStmt ABSTRACTS THE STATEMENT OVER b, so that each clause of the
-- face's dispatch can state its own obligation as `WalkStmt (ctor …)`
-- in two lines instead of retyping the forty-line telescope — the
-- clause postulates below are exactly those instances, and a wrong
-- specialisation is a type error rather than a drifted copy.  b
-- therefore moves to the FRONT of WalkLevel's telescope (the dispatch
-- matches on it); its two application sites pass it first.
-- THE TAIL, SHARED — everything from κ onwards, with the gas and the
-- numeric prefix as PARAMETERS.  Factored out so one statement can be read
-- two ways: with the gas INSIDE the telescope (WalkStmt, whose argument
-- order is unchanged, so its call sites are untouched) and with the gas
-- FIXED UP FRONT (WalkStmtAt).  The second is the only way to name a walk
-- face at a given fuel: WalkStmt's conclusion is gas-indexed — a Σ about
-- `subscribeE g b κ …` — so "walkFace at the peeled fuel" is not a term of
-- type WalkLevel at all, it needs a type of its own.
WalkTail : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} →
  Gas → Closed Γ u → Caps → (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) → Set
WalkTail {n} {Γ} {t} {e} {u} g b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j =
  ∀ (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    -- caps prelims, subscribeE-caps' own
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Caps.cReg c ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ b ≤ Caps.cSize (frameStep j c) →
    dWᵉ n sl b ≤ Caps.cWid (frameStep j c) →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    nest b sl (EvalSt.connectedShares st) ≤ bud →
    suc (sizeᵉ b) ≤ ops →
    depthE g b κ bid now sched st ≤ dep →
    -- the wet half, at the level (the E-into-j collapse: the wet
    -- predicate's B position IS the level's size cap)
    INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
    fnCapᵉ b ≤ Ψ →
    pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
    -- the reset-anchor pins (2026-08-13): the hop measurement index
    -- and rank ARE the reset cap's (refl at the true instantiation,
    -- where F, Ŝ := sizeCapAt e sl (suc id) and R̂ := hopR Ŝ), and the
    -- CEILING — no level this walk can reach outgrows Ŝ, stated as one
    -- frameStep bound at the free ceiling L̂ plus the face's own budget
    -- under it; call edges convert budgets with the Caps-Chain
    -- descents.  This is the hypothesis GAP 2's ruling (.Wet/Part6)
    -- always intended and hop-step-needs proves NECESSARY: without a
    -- syncSize-to-Ŝ link no r-drop can fund an inner walk, and the
    -- level receipts are the only syncSize bound in the telescope.
    2 ≤ Ŝ →
    F ≡ Ŝ →
    R̂ ≡ hopR Ŝ →
    Caps.cSize (frameStep L̂ c) ≤ Ŝ →
    opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j ≤ L̂ →
    -- the dry half, unchanged: demand at the ENTRY-COMPUTABLE reset
    -- caps, never at any ledger
    dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
           (hopDᵉ F (slotHop F sl) b) (syncSizeᵉ b) ≤ G →
    g hasAtLeast suc G →
    -- the length ledger, ℓ FREE (wet-ell-absurd killed the Ŝ pin)
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let r = subscribeE g b κ bid now sched st
    in Σ ℕ λ j′ →
       (capsOK? (frameStep (j + j′) c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
       × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
       × (j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j)
       × (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
               (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
       -- the hop conjunct rides the HONEST environment (Rx.Slot-Hop):
       -- `slotHop F sl i` is slot i's own def's hop, so the bound at
       -- `input i` is the def's hop rather than 0 — which is what the
       -- refutation (Demand-Probe series W) showed it has to be, and
       -- slotHop-fix is the equation the input clause spends.
       × (burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b)
                     (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)
       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)

WalkStmt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} → Closed Γ u → Set
WalkStmt {n} {Γ} {t} {e} {u} b =
  ∀ (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) (g : Gas) →
  WalkTail {e = e} g b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j

-- the same statement with the gas pinned: a walk face AT a fuel
WalkStmtAt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} → Gas → Closed Γ u → Set
WalkStmtAt {n} {Γ} {t} {e} {u} g b =
  ∀ (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) →
  WalkTail {e = e} g b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j

-- WalkStmt WITH THE regsLen? CONJUNCT REMOVED — the shape a clause's leaf
-- takes once its length-ledger conjunct is actually proven, so that the
-- proof plugs into a real body instead of being asserted inside a bigger
-- postulate.  It exists once, here, because every clause that registers
-- splits the same way; walk-defer is the first.  The hypothesis list is
-- WalkTail's verbatim — read the comments there, they are not repeated.
WalkTail⁻ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} →
  Gas → Closed Γ u → Caps → (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) → Set
WalkTail⁻ {n} {Γ} {t} {e} {u} g b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j =
  ∀ (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Caps.cReg c ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ b ≤ Caps.cSize (frameStep j c) →
    dWᵉ n sl b ≤ Caps.cWid (frameStep j c) →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    nest b sl (EvalSt.connectedShares st) ≤ bud →
    suc (sizeᵉ b) ≤ ops →
    depthE g b κ bid now sched st ≤ dep →
    INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
    fnCapᵉ b ≤ Ψ →
    pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
    2 ≤ Ŝ →
    F ≡ Ŝ →
    R̂ ≡ hopR Ŝ →
    Caps.cSize (frameStep L̂ c) ≤ Ŝ →
    opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j ≤ L̂ →
    dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
           (hopDᵉ F (slotHop F sl) b) (syncSizeᵉ b) ≤ G →
    g hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let r = subscribeE g b κ bid now sched st
    in Σ ℕ λ j′ →
       (capsOK? (frameStep (j + j′) c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
       × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
       × (j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j)
       × (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
               (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
       × (burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b)
                     (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)

WalkStmt⁻ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} → Closed Γ u → Set
WalkStmt⁻ {n} {Γ} {t} {e} {u} b =
  ∀ (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) (g : Gas) →
  WalkTail⁻ {e = e} g b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j


------------------------------------------------------------------
-- SPLITTING THE HOP CONJUNCT OFF THE REST.
--
-- The burstHopD? conjunct is the ONE axis on which the chain clauses
-- differ from each other, and it is the only conjunct in the Σ that
-- mentions neither `j′` nor the caps — so it detaches cleanly, and a
-- clause's remaining eight can be stated (and ground) without it.  That
-- matters because the eight are a DELEGATION to `subscribeE-caps` plus
-- the wet predicates, identical in shape across map / take / scan,
-- while the hop conjunct is where each frame's own ledger lives and
-- where scan is genuinely harder than its siblings:
--
--   · takeᵉ transforms no value, so `hopDᵉ (takeᵉ c e) = hopDᵉ e` and
--     the source's receipt IS the receipt;
--   · mapᵉ applies its fn ONCE per value, so one hopD-applyFn step
--     closes it, and hopD-map-emit (.Measures) is that step, PROVEN;
--   · scanᵉ REFOLDS the accumulator, so the fn's multiplier compounds
--     along the burst and the receipt needs an INVARIANT rather than a
--     step.  Nothing else about scan is harder — it mints no
--     subscription the other chain frames do not, and its caps half is
--     the same delegation theirs is.
--
-- So the split is not scan-specific plumbing: it is where the family's
-- one real difference lives, and `walk-scan` below is the assembly that
-- puts scan's clause back together from the two halves.
------------------------------------------------------------------

-- THE HOP CONJUNCT AT THE FOLD'S OWN EXPONENT — scan only.
--
-- `WalkTailᴴ` asks the burst to sit under ONE number, and for a scan
-- frame that number carries the exponent `F` outright.  Reaching it in
-- one step forces the fold to carry `F` in the exponent from the start,
-- which `Refuted.Hop-Drag` refutes: a step can DEEPEN the accumulator
-- while shrinking its `sizeᵛ`.  So the leaf concludes at each emitted
-- value's OWN SPINE — `spnᵛ`, size along the hop-deepest path, which
-- that step does not decrease — and `walk-scan` below raises the
-- exponent to `F` once, by `spn≤sizeᵛ` against the size receipt the
-- other half already proves.  Everything else is `WalkTailᴴ` verbatim
-- at `b := scanᵉ f z b`.
WalkTailᴴˢ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} →
  Gas → Fn Γ [] [] [] (u ×ᵗ s) u → Tm Γ [] [] [] u → Closed Γ s →
  Caps → (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) → Set
WalkTailᴴˢ {n} {Γ} {t} {e} {s} {u} g f z b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j =
  ∀ (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Caps.cReg c ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ (scanᵉ f z b) ≤ Caps.cSize (frameStep j c) →
    dWᵉ n sl (scanᵉ f z b) ≤ Caps.cWid (frameStep j c) →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    nest (scanᵉ f z b) sl (EvalSt.connectedShares st) ≤ bud →
    suc (sizeᵉ (scanᵉ f z b)) ≤ ops →
    depthE g (scanᵉ f z b) κ bid now sched st ≤ dep →
    INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
    fnCapᵉ (scanᵉ f z b) ≤ Ψ →
    pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
    2 ≤ Ŝ →
    F ≡ Ŝ →
    R̂ ≡ hopR Ŝ →
    Caps.cSize (frameStep L̂ c) ≤ Ŝ →
    opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j ≤ L̂ →
    dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
           (hopDᵉ F (slotHop F sl) (scanᵉ f z b))
           (syncSizeᵉ (scanᵉ f z b)) ≤ G →
    g hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    burstHopSpnH? F (slotHop F sl) (pmᵗ F 0 f)
      (hopDᵗ F (slotHop F sl) f + hopDᵗ F (slotHop F sl) z
         + hopDᵉ F (slotHop F sl) b)
      (proj₁ (subscribeE g (scanᵉ f z b) κ bid now sched st)) ≡ true

------------------------------------------------------------------
-- THE SOURCE HALF OF THE SCAN HOP RECEIPT.
--
-- `subscribeE` at a `scanᵉ` does exactly two things: it subscribes the
-- SOURCE under a freshly minted `scan-f` frame, into a state where that
-- frame's node holds `evalTm z`, and then it pushes the resulting burst
-- through the frame.  The second half is now PROVEN — `.Hop-Spine-Push`
-- walks the burst, runs `scanVals` per emit, and carries the node's
-- accumulator across emits — so the leaf is this first half alone.
--
-- Two conjuncts, and the second is the one the push face cannot see:
-- the source subscription may install nodes of its own, and the scan
-- node has to still hold a bounded accumulator when the push begins.
-- `evalTm z` satisfies it by `valHopSpn?-intro` off `hopDᵗ z ≤ BND`;
-- what is owed is that subscribing `b` does not disturb it.
------------------------------------------------------------------
WalkTailᴴˢ⁰ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} →
  Gas → Fn Γ [] [] [] (u ×ᵗ s) u → Tm Γ [] [] [] u → Closed Γ s →
  Caps → (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) → Set
WalkTailᴴˢ⁰ {n} {Γ} {t} {e} {s} {u} g f z b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j =
  ∀ (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Caps.cReg c ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ (scanᵉ f z b) ≤ Caps.cSize (frameStep j c) →
    dWᵉ n sl (scanᵉ f z b) ≤ Caps.cWid (frameStep j c) →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    nest (scanᵉ f z b) sl (EvalSt.connectedShares st) ≤ bud →
    suc (sizeᵉ (scanᵉ f z b)) ≤ ops →
    depthE g (scanᵉ f z b) κ bid now sched st ≤ dep →
    INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
    fnCapᵉ (scanᵉ f z b) ≤ Ψ →
    pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
    2 ≤ Ŝ →
    F ≡ Ŝ →
    R̂ ≡ hopR Ŝ →
    Caps.cSize (frameStep L̂ c) ≤ Ŝ →
    opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j ≤ L̂ →
    dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
           (hopDᵉ F (slotHop F sl) (scanᵉ f z b))
           (syncSizeᵉ (scanᵉ f z b)) ≤ G →
    g hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let (nid , sched₁) = mintNode sched
        r = subscribeE g b (scan-f f nid ↠ κ) bid now sched₁
              (installNode nid (scan-st (evalTm z)) st)
        BND = hopDᵗ F (slotHop F sl) f + hopDᵗ F (slotHop F sl) z
                + hopDᵉ F (slotHop F sl) b
    in (burstHopSpnH? F (slotHop F sl) (pmᵗ F 0 f) BND (proj₁ r) ≡ true)
     × (scanAccSpn? F (slotHop F sl) (pmᵗ F 0 f) BND u nid (proj₂ (proj₂ r)) ≡ true)

------------------------------------------------------------------
-- THE SOURCE BURST'S HOP RECEIPT, and it is all that is left of the
-- source half.
--
-- ORDINARY: the walk face's own `burstHopD?` at the source's headline
-- bound, the shape every sibling clause produces.
--
-- THE NODE-TABLE CONJUNCT USED TO SIT HERE, AND IT WAS THE WHOLE RISK.
-- It asked that subscribing `b` under `scan-f f nid ↠ κ` leave node `nid`
-- holding exactly `scan-st (evalTm z)`.  That is now DISCHARGED at the
-- consumer (`walk-scan-source`, .Parts) off `mint-install-survives`
-- (.Node-Fresh), so the statement no longer carries it — a subscribe
-- writes nothing below the `nextNode` watermark it was handed, and the
-- caller minted `nid` below it.  That watermark fact is itself PROVEN
-- there, so nothing under this conjunct is postulated any more.
--
-- WHAT IT IS NOT, kept because the alignment is what made the route look
-- mechanical: the caps face.  `capsOK?` (.Caps-Face/Part1) BOUNDS every
-- node and IDENTIFIES none, so no strengthening of it reaches a claim
-- that a particular nid holds a particular value.
--
-- Nothing about the SPINE appears here.  `walk-scan-source` converts both
-- of its conjuncts to the hereditary form by `burstHopSpnH-intro` and
-- `scanSeed-hopSpn` (.Hop-Spine-Face, both PROVEN), which cost nothing
-- because `hopDᵛ` is a `⊔` over obs-leaves and the exponent is spare
-- room.
------------------------------------------------------------------
WalkTailᴴˢᶠ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} →
  Gas → Fn Γ [] [] [] (u ×ᵗ s) u → Tm Γ [] [] [] u → Closed Γ s →
  Caps → (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) → Set
WalkTailᴴˢᶠ {n} {Γ} {t} {e} {s} {u} g f z b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j =
  ∀ (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Caps.cReg c ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ (scanᵉ f z b) ≤ Caps.cSize (frameStep j c) →
    dWᵉ n sl (scanᵉ f z b) ≤ Caps.cWid (frameStep j c) →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    nest (scanᵉ f z b) sl (EvalSt.connectedShares st) ≤ bud →
    suc (sizeᵉ (scanᵉ f z b)) ≤ ops →
    depthE g (scanᵉ f z b) κ bid now sched st ≤ dep →
    INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
    fnCapᵉ (scanᵉ f z b) ≤ Ψ →
    pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
    2 ≤ Ŝ →
    F ≡ Ŝ →
    R̂ ≡ hopR Ŝ →
    Caps.cSize (frameStep L̂ c) ≤ Ŝ →
    opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j ≤ L̂ →
    dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
           (hopDᵉ F (slotHop F sl) (scanᵉ f z b))
           (syncSizeᵉ (scanᵉ f z b)) ≤ G →
    g hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let (nid , sched₁) = mintNode sched
        r = subscribeE g b (scan-f f nid ↠ κ) bid now sched₁
              (installNode nid (scan-st (evalTm z)) st)
    in burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b) (proj₁ r) ≡ true

-- THE THREE SCAN HALVES ARE GAS-PINNED, AND THAT IS LOAD-BEARING, NOT
-- COSMETIC.  Their assembly (`walk-scan`, .Parts) receives the walk face
-- AT THE SOURCE — `walkFace b` — so the dispatch has to hand it over at
-- the clause's OWN gas: a gas-polymorphic argument can only be supplied
-- as a lambda whose gas binder is unrelated to the clause's, and the
-- termination checker then reads the recursive call's fuel as UNKNOWN and
-- rejects the whole walk group (measured; it takes walk-mu down with it).
-- Pinned, the call is `walkFace b … g …`: fuel equal, source structurally
-- smaller, which is the shape `subscribeAll-walk` already recurses at.
-- Same lesson as `WalkStmtAt` above, arriving from the other clause.
WalkStmtᴴˢᶠ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} → Gas →
  Fn Γ [] [] [] (u ×ᵗ s) u → Tm Γ [] [] [] u → Closed Γ s → Set
WalkStmtᴴˢᶠ {n} {Γ} {t} {e} {s} {u} g f z b =
  ∀ (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) →
  WalkTailᴴˢᶠ {e = e} g f z b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j

WalkStmtᴴˢ⁰ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} → Gas →
  Fn Γ [] [] [] (u ×ᵗ s) u → Tm Γ [] [] [] u → Closed Γ s → Set
WalkStmtᴴˢ⁰ {n} {Γ} {t} {e} {s} {u} g f z b =
  ∀ (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) →
  WalkTailᴴˢ⁰ {e = e} g f z b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j

WalkStmtᴴˢ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} → Gas →
  Fn Γ [] [] [] (u ×ᵗ s) u → Tm Γ [] [] [] u → Closed Γ s → Set
WalkStmtᴴˢ {n} {Γ} {t} {e} {s} {u} g f z b =
  ∀ (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) →
  WalkTailᴴˢ {e = e} g f z b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j

-- WalkStmt WITH THE burstHopD? CONJUNCT REMOVED — the other eight.
WalkTail⁻ᴴ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} →
  Gas → Closed Γ u → Caps → (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) → Set
WalkTail⁻ᴴ {n} {Γ} {t} {e} {u} g b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j =
  ∀ (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Caps.cReg c ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ b ≤ Caps.cSize (frameStep j c) →
    dWᵉ n sl b ≤ Caps.cWid (frameStep j c) →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    nest b sl (EvalSt.connectedShares st) ≤ bud →
    suc (sizeᵉ b) ≤ ops →
    depthE g b κ bid now sched st ≤ dep →
    INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
    fnCapᵉ b ≤ Ψ →
    pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
    2 ≤ Ŝ →
    F ≡ Ŝ →
    R̂ ≡ hopR Ŝ →
    Caps.cSize (frameStep L̂ c) ≤ Ŝ →
    opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j ≤ L̂ →
    dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
           (hopDᵉ F (slotHop F sl) b) (syncSizeᵉ b) ≤ G →
    g hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let r = subscribeE g b κ bid now sched st
    in Σ ℕ λ j′ →
       (capsOK? (frameStep (j + j′) c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
       × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
       × (j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j)
       × (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
               (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)
       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)

-- RECOVERY: `git show 62fb817` restores `WalkTailᴴ`/`WalkStmtᴴ` (the hop
-- conjunct at WalkTail's telescope, bounded by ONE number) and `walk-join`
-- (the generic re-association of the two halves).  They were scan's assembly
-- until the hop half moved to the SPINE exponent, which is scan-specific;
-- another chain clause needing the SAME split at a single bound would want
-- them back verbatim.
-- GAS-FIXED, because the one clause stated at it needs the walk's own
-- INDUCTION HYPOTHESIS beside it and that hypothesis is stated at a fixed
-- gas (`WalkStmtAt`).  The un-fixed `WalkStmt⁻ᴴ` this replaces had exactly
-- one user and could not have one that closed: see walk-scan-rest.
WalkStmtAt⁻ᴴ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} →
  Gas → Closed Γ u → Set
WalkStmtAt⁻ᴴ {n} {Γ} {t} {e} {u} g b =
  ∀ (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) →
  WalkTail⁻ᴴ {e = e} g b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j

WalkLevel : Set
WalkLevel = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (b : Closed Γ u) → WalkStmt {e = e} b

-- THE WALK FACE AT A FIXED GAS.  `walkFace` partially applied to a fuel
-- inhabits this — no lambda over the tail is needed, since WalkStmtAt is
-- WalkStmt with exactly the gas argument removed.
WalkLevelAt : Gas → Set
WalkLevelAt g = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (b : Closed Γ u) → WalkStmtAt {e = e} g b

-- one gas step down, total.  In the type of input-wet-core below this is
-- what turns the clause's own gas into the fuel its recursive walk runs at;
-- at `gs fuel` it reduces to `fuel`, which is what makes the recursive call
-- STRUCTURALLY smaller and so visible to the termination checker.
peelGas : Gas → Gas
peelGas g0       = g0
peelGas (gs fuel) = fuel

-- THE 19 ROUTE LEMMAS, RE-HOMED (2026-08-13).  They used to hang off
-- `subscribeE-wet-core`'s hypothesis list, from the days when that
-- core walked the gas edges clause by clause.  Assembling the outer
-- face showed it needs NONE of them — it is pure instantiation and
-- lift — while the walk face, which IS the clause-by-clause gas walk,
-- is where every one of them gets spent.  Their ONLY consumer in the
-- repo was that hypothesis list, so re-homing them here is also what
-- keeps them wired.  Set₁ rather than Set: two of them quantify over
-- `{A : Set}` (splitBurst's payload), which lifts the whole core.
WalkLevelCore : Set₁
WalkLevelCore =
    -- mu-edge  (Verify-Budget-Sufficient/Wet/Part6.agda)
    (∀ {n} {Γ : Ctx n} {t} (Ŝ R̂ U : ℕ) (η : Fin n → ℕ)
      (body : Exp Γ (t ∷ []) [] [] t) →
      suc (dBound Ŝ R̂ U (hopDᵉ Ŝ η (unfoldμ body)) (syncSizeᵉ (unfoldμ body)))
        ≤ dBound Ŝ R̂ U (hopDᵉ Ŝ η (μᵉ body)) (syncSizeᵉ (μᵉ body))
     ) →
    -- hop-edge  (Verify-Budget-Sufficient/Wet/Part6.agda)
    (∀ {n} {Γ : Ctx n} {u} (Ŝ U r s : ℕ) (η : Fin n → ℕ) → 2 ≤ Ŝ →
      (o : Val Γ (obs u)) → sizeᵛ (obs u) o ≤ Ŝ → hopDᵛ Ŝ η (obs u) o < r →
      suc (dBound Ŝ (hopR Ŝ) U (hopDᵛ Ŝ η (obs u) o) (syncSizeᵉ o))
        ≤ dBound Ŝ (hopR Ŝ) U r s
     ) →
    -- connect-edge  (Verify-Budget-Sufficient/Wet/Part6.agda)
    (∀ {n} {Γ : Ctx n} (Ŝ r s : ℕ) → 2 ≤ Ŝ →
      (sl : Slots Γ) → slotsSize sl ≤ Ŝ → (cs : List Source) (i : Fin n)
      {d : Closed Γ (lookup Γ i)} {ok : T (inputsBelowᵉ (toℕ i) d)} →
      sl i ≡ shared d {ok = ok} →
      memberSource (toℕ i) cs ≡ false → sizeᵉ d ≤ Ŝ →
      suc (dBound Ŝ (hopR Ŝ) (unconn sl (toℕ i ∷ cs))
                  (hopDᵉ Ŝ (slotHop Ŝ sl) d) (syncSizeᵉ d))
        ≤ dBound Ŝ (hopR Ŝ) (unconn sl cs) r s
     ) →
    -- hop-step-gives  (Verify-Budget-Sufficient/Wet/Part6.agda)
    (∀ (V R U r s s′ : ℕ) → suc s′ ≤ s + suc V →
      suc (dBound V R U r s′) ≤ dBound V R U (suc r) s
     ) →
    -- hop-step-needs  (Verify-Budget-Sufficient/Wet/Part6.agda)
    (∀ (V R U r s s′ : ℕ) →
      suc (dBound V R U r s′) ≤ dBound V R U (suc r) s → suc s′ ≤ s + suc V
     ) →
    -- unconn-keeps  (Verify-Budget-Sufficient/Wet.agda)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      (sched : Sched Γ) (st : EvalSt e) (sched′ : Sched Γ) (st′ : EvalSt e) →
      Keeps sched st sched′ st′ →
      unconn (Sched.slots sched′) (EvalSt.connectedShares st′)
        ≤ unconn (Sched.slots sched) (EvalSt.connectedShares st)
     ) →
    -- sharedConnect-unconn  (Verify-Budget-Sufficient/Keeps-Ring.agda)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      (fuel : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
      (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
      (sched : Sched Γ) (st : EvalSt e) {dd : Closed Γ (lookup Γ i)}
      {okd : T (inputsBelowᵉ (toℕ i) dd)} →
      Sched.slots sched i ≡ shared dd {ok = okd} →
      memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false →
      unconn (Sched.slots (proj₁ (proj₂ (sharedConnect (gs fuel) i d κ id now sched st))))
             (EvalSt.connectedShares
               (proj₂ (proj₂ (sharedConnect (gs fuel) i d κ id now sched st))))
      < unconn (Sched.slots sched) (EvalSt.connectedShares st)
     ) →
    -- obs-slot-shared  (Verify-Budget-Sufficient/Keeps-Ring.agda)
    (∀ {n} {Γ : Ctx n} {k u} (s : Slot Γ k (obs u)) →
      Σ (Closed Γ (obs u)) λ d → Σ (T (inputsBelowᵉ k d)) λ ok →
        s ≡ shared d {ok = ok}
     ) →
    -- share-live-novals  (Verify-Budget-Sufficient/Keeps-Ring.agda)
    (∀ {n} {Γ : Ctx n} {u} {A : Set} (s : Source) (id : Id) →
      proj₁ (splitBurst {Γ = Γ} {u = u} {A = A}
              (((init s ∷ []) at id from s as subscribe) ∷ [])) ≡ []
     ) →
    -- share-spent-novals  (Verify-Budget-Sufficient/Keeps-Ring.agda)
    (∀ {n} {Γ : Ctx n} {u} {A : Set} (s : Source) (id : Id) →
      proj₁ (splitBurst {Γ = Γ} {u = u} {A = A}
              (((init s ∷ close s exhausted ∷ complete ∷ []) at id from s as subscribe) ∷ []))
        ≡ []
     ) →
    -- hasAtLeast-pad  (Verify-Budget-Sufficient/Measures.agda)
    (∀ (m : ℕ) (g : Gas) {n} → n ≤ m → gasPad m g hasAtLeast n
     ) →
    -- hasAtLeast-peel  (Verify-Budget-Sufficient/Measures.agda)
    (∀ {g : Gas} {m : ℕ} → g hasAtLeast suc m →
      Σ Gas (λ g′ → (g ≡ gs g′) × (g′ hasAtLeast m))
     ) →
    -- seed-covers  (Verify-Budget-Sufficient/Measures.agda)
    (∀ (sz U : ℕ) → U ≤ sz →
      let V = towerℕ ((4 + sz) * 1) in
      suc (suc V * suc (hopR V) * suc U)
        ≤ 2 ^ (sz * 1 * 1) + towerℕ ((7 + sz) * 2)
     ) →
    -- budget-covers  (Verify-Budget-Sufficient/Measures.agda)
    (∀ (sz U id : ℕ) → U ≤ sz →
      let V = towerℕ ((4 + sz) * suc (suc id)) in
      suc (suc V * suc (hopR V) * suc U)
        ≤ 2 ^ (sz * suc id * suc id) + towerℕ ((7 + sz) * suc (suc id))
     ) →
    -- oneShot-tail-dry  (Verify-Budget-Sufficient/Measures.agda)
    (∀ {n} {Γ : Ctx n} {u} (vals : List (Val Γ u)) (src : Source) →
      any dryEvent (map value vals ++ close src exhausted ∷ complete ∷ []) ≡ false
     ) →
    -- connect-anchor  (Verify-Budget-Sufficient/Measures.agda)
    (∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
      (id : Id) (i : Fin n) {d : Closed Γ (lookup Γ i)}
      {ok : T (inputsBelowᵉ (toℕ i) d)} → sl i ≡ shared d {ok = ok} →
      let V = sizeBudgetAt e sl id in
      (hopDᵉ V (slotHop V sl) d ≤ hopR V) × (syncSizeᵉ d ≤ V)
     ) →
    -- hopD-map-emit  (Verify-Budget-Sufficient/Measures.agda)
    (∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s u} (V : ℕ) (η : Fin n → ℕ)
      (f : Tm Γ Δᵍ Δ (s ∷ Θ) u) (b : Exp Γ Δᵍ Δ Θ s) (v : Val Γ s) →
      (f₀ : Fn Γ [] [] [] s u) →
      hopDᵗ V η f₀ ≤ hopDᵗ V η f → pmᵗ V 0 f₀ ≤ pmᵗ V 0 f →
      hopDᵛ V η s v ≤ hopDᵉ V η b →
      hopDᵛ V η u (applyFn f₀ v) ≤ hopDᵉ V η (mapᵉ f b)
     ) →
    -- applyFn-size  (Verify-Budget-Sufficient/Measures.agda)
    (∀ {n} {Γ : Ctx n} {s t} (V : ℕ)
      (fn : Fn Γ [] [] [] s t) (v : Val Γ s) → sizeᵛ s v ≤ V →
      sizeᵛ t (applyFn fn v) ≤ (2 + 2 * V) ^ (3 ^ sizeᵗ fn)
     ) →
    -- unconn-cons-≤  (Verify-Budget-Sufficient/Measures.agda)
    (∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
      (s : Source) → unconn sl (s ∷ cs) ≤ unconn sl cs
     ) →
    -- shellSize-unfoldμ  (Verify-Budget-Sufficient/Measures.agda)
    (∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
      shellSizeᵉ (unfoldμ body) ≡ shellSizeᵉ body
     ) →
    -- inner-unfoldμ  (Verify-Budget-Sufficient/Measures.agda)
    (∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
      innerᵉ (unfoldμ body) ≡ innerᵉ body
     ) →
    -- walk-desc  (Verify-Budget-Sufficient/Caps-Chain.agda)
    (∀ (S W d k m j : ℕ) →
      sLvlD S W d k (suc j) ≤ sIterD S W d k (suc m) j
     ) →
    -- inner-desc  (Verify-Budget-Sufficient/Caps-Chain.agda)
    (∀ (S W d bud j m : ℕ) → 2 ≤ S →
      suc m ≤ suc (sizeAt S (suc j)) →
      opIterD S W d bud (suc m) (suc j) ≤ sLvlD S W d (suc bud) (suc j)
     ) →
  WalkLevel

postulate
  -- THE COLLAPSED WALK FACE, CLAUSE BY CLAUSE.  The face's statement:
  -- subscribeE-caps' hypothesis list verbatim (caps prelims, the
  -- level-indexed size/width/path bounds, the three charge indices
  -- dep/bud/ops), then the wet half at the SAME level (INV? / fnCap /
  -- pathB? at cSize (frameStep j c)), then the dry half unchanged
  -- (demand at the reset caps, one spare peel, the free length ledger
  -- ℓ).  Conclusion: subscribeE-caps' Σ with the wet conjuncts riding
  -- the same witness.
  --
  -- THE DISPATCH IS REAL (`walkFace`, below): the face is now split
  -- along subscribeE-caps' own clause structure, one postulate per
  -- constructor of the subscribed expression, each a two-line
  -- `WalkStmt (ctor …)` instance of the face.  What the split has
  -- already PROVEN, because both discharges are structural: the μ DRY
  -- MINT IS UNREACHABLE (at g0 the gas hypothesis `g0 hasAtLeast
  -- suc G` has no constructor — the demand hypothesis excludes the one
  -- dry close subscribeE itself can mint, the walk-face twin of
  -- Burst-Walk's budgetAt-gs finding), and varᵉ is closed-term absurd.
  -- Each remaining clause grinds by riding subscribeE-caps' proven
  -- clause body (same IH calls, same level arithmetic) with the wet
  -- conjuncts threaded through; the *All clauses delegate to
  -- subscribeAll-walk (below, REAL — its body walks the mutual
  -- recursion with this face); the hop edge — hasDry's one live risk —
  -- is paid at subscribeInner-walk, the LEAF of the hop-edge chain
  -- (the WHOLE chain is REAL as of 2026-08-14: leaf, thruConsume,
  -- thruWalk, stepThru, pushThru — the leaf's header has the route).
  --
  -- Σ-CONTENT CHECKED 2026-08-13 (the "a Σ-receipt has content only
  -- through its witness" rule, run before any clause grind).  NOT
  -- VACUOUS, and here is the exact accounting, because five of the nine
  -- conjuncts ARE upward-closed in j′ and would be vacuous alone:
  --   · the capsOK? / burstCaps? / burstCount? / INV? / burstB?
  --     conjuncts all weaken as the level grows (frameStep is monotone
  --     in j and every one of them is a ≤-against-the-caps test), so
  --     each survives enlarging the witness;
  --   · the opIterD LEVEL BOUND (`j + j′ ≤ opIterD …`) is
  --     DOWNWARD-closed — it is the only conjunct that bounds j′ from
  --     above, and it is what gives the other five their content.
  --     Deleting or weakening it makes the whole Σ satisfiable by
  --     taking j′ enormous.  Do not.
  --   · the burstHopD? / hasDry / regsLen? conjuncts do not mention j′
  --     at all: real content at every witness.
  -- This is the SAME shape as `subscribeE-caps` (.Subscribe-Face:937),
  -- which is ground with exactly the caps conjuncts plus that level
  -- bound — so the collapse inherits a witness discipline that is
  -- already proven to close.
  --
  -- WHAT THIS CHECK DOES *NOT* SETTLE, and it is the live risk: whether
  -- the j′ the caps face PRODUCES is large enough for the INV? and
  -- burstB? conjuncts at the same time as the level bound still holds.
  -- Vacuity is ruled out; falsity is not.  The two halves sharing one
  -- witness is the whole content of the collapse, and it is untested —
  -- the caps half cannot be probed (opIterD is in the sealed level
  -- family, Evaluator:746-828, and the can't-probe ruling applies), so
  -- this one is symbolic-or-nothing.  Grind INV? and burstB? FIRST, at
  -- the clause where subscribeE-caps' own witness is largest; if they
  -- need more level than the bound allows, that is the refutation and
  -- it should be stated as a `→ ⊥` here.
  --
  -- The grind order for the clauses, per the containment receipt: the
  -- decrement edges consume one hasAtLeast peel each against
  -- dBound-μ / dBound-hop / dBound-connect (walk-mu, the *All
  -- descendants, walk-input's connect respectively), riding
  -- subscribeE-caps' proven clause skeleton for the level half.
  --
  -- ═══ CONTAINMENT RECEIPT, 2026-08-13 — checked by inspection, and
  -- it says exactly where the FALSITY can and cannot live ═══
  --
  -- This statement is a CONSERVATIVE EXTENSION of a PROVEN theorem.
  -- Against `subscribeE-caps` (.Subscribe-Face:906, GROUND — that
  -- module has no live postulate):
  --   · the thirteen caps prelims below are subscribeE-caps' OWN
  --     hypothesis list, same statements, same ORDER, nothing added
  --     and nothing dropped;
  --   · the capsOK?, burstCaps? and burstCount? conjuncts and the
  --     opIterD level bound are its OWN Σ, verbatim — including the
  --     bound's `j + j′` form.  (The `j′ ≤ …` form seen at
  --     Caps-Bridge:659 is `sub-charge` WEAKENING this one by m≤n+m,
  --     not a competing statement — checked, since a mismatch there
  --     would have meant the collapse silently strengthened the
  --     bound.)
  --
  -- CONSEQUENCE: the four caps conjuncts cannot be the failure point,
  -- and neither can the hypothesis list be too weak for them.  What
  -- this statement ADDS is three wet hypotheses and five wet conjuncts
  -- (INV? / burstB? / burstHopD? / hasDry / regsLen?), asked to hold
  -- AT THE WITNESS THE CAPS FACE ALREADY PICKS.
  --
  -- SO THE RISK IS WITNESS-COINCIDENCE, and nothing else: does the j′
  -- that subscribeE-caps produces also carry INV?, burstB?,
  -- burstHopD?, hasDry ≡ false and regsLen?.  THIS RECEIPT DOES NOT
  -- LOWER THE CLASS — it reached the caps half, which was never the
  -- risky region.  Per the standing rule (CLAUDE.md: a risk class may
  -- only be lowered by evidence that REACHED the risky region), the
  -- row stays FALSITY.  What it buys is aim: any refutation attempt
  -- should target the coincidence, and any grind should ride
  -- subscribeE-caps' clause skeleton rather than re-deriving a level
  -- walk.
  --
  -- ═══ THE COINCIDENCE, CONJUNCT BY CONJUNCT (census 2026-08-13) —
  -- the five wet conjuncts do NOT carry equal risk ═══
  --
  -- · INV? at the landing size cap — ASSEMBLY, not independent risk.
  --     Six sub-conjuncts: stBounded?/regsB?'s size halves come from
  --     the LANDING capsOK? (proven at the same witness); the two Ψ
  --     halves are level-free and mirror the proven wet clique; the
  --     registry-cardinality conjunct needs
  --     `cReg (frameStep …) ≤ cSize (frameStep …)`, which is
  --     `frameStep-reg≤size` — PROVEN, .Caps-Bridge:151, since
  --     2026-08-05 (f306c9e; § 5a's "hand derivation, not yet machine"
  --     note predated finding it); the two slot conjuncts ride the
  --     entry INV? since slots never change and B only widens.  This
  --     is cascade-wet-via-caps' § C recombination, one face down.
  -- · burstB? at the landing cap — the size half is IMPLIED by the
  --     burstCaps? conjunct via `burstB?-halves` (.Burst-Walk,
  --     PROVEN); only the Ψ half (burstΨ?) is new, and it is
  --     level-free.
  -- · burstHopD? — genuinely separate, level-free; the hop-descent
  --     conjunct, refuted once and restated with corpus receipts (the
  --     hop-descent memo, .Measures).  Its risk is documented there.
  -- · hasDry ≡ false — REAL RISK, but the demand ledger CLOSES at
  --     the interface (census 2026-08-13).  The evaluator has EXACTLY
  --     THREE gas-peel sites — the only `g0` matches in Rx/Evaluator —
  --     and each is matched by a PROVEN decrement lemma (.Measures):
  --       · subscribeInner g0 (:1004, the hop)  ↔ dBound-hop
  --       · sharedConnect g0 (:1346, connect)   ↔ dBound-connect,
  --         side conditions PROVEN off the budget's slot summand
  --         (connect-anchor — no state invariant consulted)
  --       · subscribeE g0 (μᵉ …) (:1454, μ)     ↔ dBound-μ
  --     So a hasDry falsity, if present, is a SIDE-CONDITION failure
  --     at one of three named edges, not a missing lemma.  The connect
  --     and μ conditions are structural; the live one is the HOP edge:
  --     r′ < r is funded by the burstHopD? conjunct carried on the
  --     SAME witness (this is why hop-descent and dryness ride one Σ —
  --     hasDry cannot be ground before burstHopD? threads the same
  --     clauses), and s′ ≤ V is funded by the value-size conjuncts via
  --     reach-reset (syncSizeᵉ ≤ C from sizeᵉ ≤ C, .Measures:1783).
  -- · regsLen? ℓ — REAL RISK, and PROBEABLE (unlike hasDry: dBound,
  --     subscribeE, regsLen? all compute).  The scare: a chain minted
  --     from an inner GROWN by within-instant applyFn (not a subterm
  --     of b) adds size-many frames on ONE gas peel, so gas does not
  --     bound minted path lengths.  The answer the statement bets on:
  --     within-instant value sizes fit under Ŝ (lvl-fits +
  --     capsAt-suc-full), and dBound Ŝ R̂ u r s = s + suc Ŝ · (r + …)
  --     carries an Ŝ-PER-HOP term, so minted lengths stay under
  --     pathLen κ + dBound.  If a probe refutes even with a generous
  --     hand-supplied Ŝ ≥ the program's observed sizes, the MECHANISM
  --     is broken, not just an instantiation.
  --
  -- NET: the falsity surface is hasDry and regsLen?, plus the
  -- possibility that one witness cannot serve both flavours at once —
  -- INV? and burstB? cannot fail except through their level-free Ψ
  -- halves.
  --
  -- ═══ AND THE TWO SHARE ONE MECHANISM (the consolidation) ═══
  -- regsLen?'s scare is a within-instant GROWN inner minting size-many
  -- frames; hasDry's live edge is a grown inner whose syncSize escapes
  -- V at the hop.  BOTH are funded by the same fact: values produced
  -- this instant stay under the Ŝ ceiling (mid-walk: the value-size
  -- conjuncts at the landing level; at the seam: lvl-fits +
  -- capsAt-suc-full, `cascadeGo-burst-nodry`'s payoff arithmetic,
  -- .Burst-Walk).  So the whole tier-0 FALSITY
  -- class now rests on ONE question — does within-instant growth stay
  -- under Ŝ — and that question is PROBEABLE (sizeᵉ / syncSizeᵉ /
  -- dBound / subscribeE all compute).
  --
  -- PROBED 2026-08-13 (Demand-Probe, P-series; dual-sided pins) and
  -- extended 2026-08-14 (P-c3/c4, P-COMP2, P-S1).  The mechanism HELD
  -- on every shape run — no refutation of either conjunct.  Coverage,
  -- stated exactly:
  --   · regsLen?: scan-GROWN inners subscribed through mergeAll at
  --     k = 1, 2, 3, and 4 nesting, registry non-empty at exit (deferᵉ
  --     persistence).  Max minted pathLen 2/3/4/5/6 vs dBound
  --     11/1477/1478/1479/1480.  Comparison at Ŝ = 5, BELOW acc₁'s
  --     sizeᵉ = 8: dBound is monotone in Ŝ, so green here implies green
  --     at every faithful (larger) Ŝ.
  --   · hasDry: minimal dry-free pad bisected exactly (h* = 1/2/3/4/5),
  --     h* ≤ suc dBound with margin three orders or more.
  --   · Ŝ-ceiling: grown-inner sizes pinned (sizeᵉ acc₁ ≡ 8), so the
  --     true instantiation needs sizeCapAt ≥ 8 — trivially met by the
  --     tower.
  --   · COMPOUNDING (P-COMP2): outer scan over inner scan; hopDᵉ 5 =
  --     59293 (inner 243, outer 244×); hasDry h* = 4 (SAME depth as
  --     k = 3 B-series — compounding inflates hopDᵉ/dBound but NOT gas
  --     depth); max pathLen = 5; ratio dBound/pathLen ≈ 71000.
  --   · SHARE EDGES (P-S1): shared slot in the growth path; h* = 3
  --     (outer subscribeInner + acc₁ subscribeInner + sharedConnect).
  --     FINDING: sharedConnect writes to connectedShares, NOT to
  --     EvalSt.registry, so regsLen? is vacuously true for share-only
  --     programs.  hasDry conjunct confirmed at h* = 3 ≤ suc dBound.
  --   · RICHER REGISTRIES: P-c3 at k=3 has 3 entries (pathLen 3,4,5);
  --     P-c4 at k=4 has 4 entries (pathLen 3,4,5,6) — both reached by
  --     running, not hand-constructed.
  -- ═══ THE SHAPE OF THE MARGIN (read this before probing further) ═══
  -- The ratio dBound/pathLen FALLS with nesting (≈296 at k=3, ≈247 at
  -- k=4) and that reads alarming, but the ratio is the wrong statistic:
  -- the DIFFERENCE is invariant.  pathLen runs 2/3/4/5/6 against dBound
  -- 11/1477/1478/1479/1480, so from k=1 on both sides increment by
  -- EXACTLY +1 per nesting level and the gap is a flat 1474.  Nesting
  -- moves both sides in lockstep; it does not erode the margin, and
  -- crossover by nesting alone never arrives.
  --
  -- The original scare — "slack observed at small k is exactly what
  -- geometric growth eats" — is now MEASURED, and it runs the other
  -- way.  P-COMP2's compounding drives hopDᵉ to 59293 while h* stays
  -- at 4, the SAME depth as the non-compounding k = 3 run: growth
  -- enters through hopDᵉ, which multiplies the BOUND side, and never
  -- through gas depth.  Compounding FEEDS the margin.
  --
  -- THE LOCKSTEP IS ON THE PROOF PATH (2026-08-14): the +1/+1
  -- arithmetic — one demand unit funds one gas peel AND one from-inner
  -- frame's ℓ extension — is subscribeInner-walk's gs clause below
  -- (`sucG′≤G`, spelled with hop-step-gives and the dBound monos),
  -- consumed by the REAL thruConsume/thruWalk/stepThru tower.  A
  -- standalone ∀-depth statement of it (Lockstep.agda, dry/mint over a
  -- nestN family, plus Demand-Probe ∀-depth pins) existed for one day
  -- off the claim graph and was deleted uncommitted when this clause
  -- landed — the telescope form strictly supersedes it (arbitrary
  -- inner VALUES, not just syntactic nests, and all nine conjuncts).
  -- The load-bearing residue of the P-rows is unchanged: the scanᵉ
  -- clause mints evalTm-EQUAL values through applyFn, so the
  -- obligation AT that clause (walk-scan below) is untouched, and only
  -- the concrete P-rows reach it.
  --
  -- NOT COVERED: μᵉ-recursive programs; programs with both deferᵉ AND
  -- sharedConnect in the same growth chain; and the crossover region
  -- where the sum side (sucG) closes on the product demand, which no
  -- row here reaches and which cost hours to approach by measurement.
  -- (That crossing region is the one Demand-Probe SERIES Q already ran
  -- at, against the OLD unlinked statement — see the series Q note in
  -- subscribeInner-walk's header below.  Spell it "series Q": the
  -- receipt that first cited it wrote "Q-series", which greps as
  -- nothing and cost a review cycle.)
  -- Class stays FALSITY: the nesting dimension is retired by theorem,
  -- but series Q's d·k growth is NOT nesting a fixed base (the outer
  -- program's entry bound is the question there), and share-path
  -- regsLen? coverage is vacuous (see P-S1) rather than real.
  --
  -- ⚠ THIS RULING DOES NOT REACH THE CHAIN FRAMES (2026-08-20), and it
  -- was read as if it did — walk-map, walk-take and walk-scan-rest were
  -- all classed FALSITY by citing it.  Two independent reasons it cannot
  -- carry them, and the first is decisive:
  --
  --   · THE CHAIN FRAMES PEEL NO GAS.  Evaluator:1436-1458: the mapᵉ,
  --     takeᵉ-`suc k` and scanᵉ clauses each pass `fuel` UNCHANGED to
  --     both the recursive `subscribeE` and the following `pushBurst`,
  --     and takeᵉ-`zero` never subscribes at all.  The ONLY clauses that
  --     consume gas are μᵉ (`subscribeE (gs fuel) (μᵉ …)`) and
  --     subscribeAll/subscribeInner.  Series Q's mechanism IS gas
  --     exhaustion — a static sum failing to dominate a runtime product
  --     — so it cannot be sited at a clause that spends no gas.  What
  --     these three owe on the hasDry/regsLen? axis is TRANSPORT across
  --     one frame at the same fuel, not a demand argument.
  --   · IT WOULD REFUTE THE PROVEN ROWS FIRST.  Series Q's own header
  --     says a true row "REFUTES IT — not merely the hop-edge leaf but
  --     WalkStmt itself".  Eight of walkFace's twelve clauses are REAL
  --     BODIES at the full nine-conjunct WalkStmt, the four *All rows
  --     among them, and those four are exactly the gas-peeling ones. A
  --     risk shared with the proven rows cannot be what distinguishes
  --     the open ones.
  --
  -- AND THE REGION IS UNREACHABLE BY MEASUREMENT, so this is not a
  -- ruling awaiting evidence.  Measured 2026-08-20 in the compiled
  -- harness at 26 points: cost is exponential in d·k with base 2.895,
  -- putting the cheapest refuting row at ~2×10¹² years against a
  -- practical ceiling of d·k ≈ 21.  The full curve and what it
  -- supersedes are in series Q's header (.Demand-Probe).
  --
  -- The chain frames' real residue is the PER-FRAME PUSH FACE — the
  -- DEAD ROUTE below, whose refutation is at `burstHopD?` and NOT at
  -- either ruled-FALSITY conjunct — which is labour with a design
  -- decision in it, i.e. DIFFICULTY.
  --
  -- NOTE for the opIterD level bound at the degenerate corner:
  -- `opIterD` is the identity at m = 0 (`opIterD-0`, Evaluator:811)
  -- and `ops` sits in the m position — so `ops = 0` would pin j′ = 0.
  -- It is excluded by the `suc (sizeᵉ b) ≤ ops` hypothesis, i.e. the
  -- positivity is already threaded.  `dep = 0` and `bud = 0` ARE
  -- reachable and are harmless: opIterD's `suc m` clause bumps J
  -- unconditionally (J₀ = suc (J + …)) before any d/k-dependent step
  -- runs.

  -- (walk-input is GROUND — assembled below over subscribeE-caps and
  -- input-wet; the share/connect gas peel is what input-wet still owes)
  --
  -- ═══ THE FAMILY CENSUS (2026-08-19) ═══
  -- These four are what is left of walkFace; the other eight clauses
  -- (walk-mu, walk-input, walk-map, walk-take and the four *All) are
  -- GROUND.  The caps half of every one of them is a DELEGATION, not a
  -- re-derivation — see the
  -- "WHY THE SPLIT IS EXACT" paragraph above — and the proven twin is
  -- `subscribeE-caps` (.Subscribe-Face), whose own header carries a
  -- clause-to-form map matching this family one for one.  So what each
  -- row below owes is the WET FIVE at its shape, and the census is of
  -- those.  Derived by reading the evaluator and the measures, NOT by
  -- typechecking — treat each named ingredient as located, not spent.
  --
  -- THE CHAIN FRAMES DO NOT SHARE A PUSH FACE, and that is the one thing
  -- to internalise before touching scan — the last of the three.  A
  -- frame-generic wet push face is REFUTED — the DEAD ROUTE at the
  -- hop-edge chain section below (`pushBurst-walk`, generic in
  -- `f : Frame Γ s u`) — because caps measures are frame-generic and THE
  -- HOP LEDGER IS NOT.  Each chain frame needs its own face, at its own
  -- output index, and the index is read off hopDᵉ (Rx.Hop-Depth) rather
  -- than chosen:
  --   · takeᵉ  `hopDᵉ V η (takeᵉ c e) = hopDᵉ V η e` — the IDENTITY, so
  --            no growth lemma is owed at all.  SPENT: `pushTake-wet`
  --            ⊗ `stepTake-wet` (.Walk-Level/Parts), both real bodies.
  --   · mapᵉ   `hopDᵗ f + (pmᵗ V 0 f ⊔ 1) * hopDᵉ e`.  SPENT:
  --            `pushMap-wet` (ibid.), whose per-value step is
  --            hopD-map-emit (.Measures) — and whose SIZE half rides
  --            `burstB?-halves` rather than any growth theorem, which
  --            is why applyFn-size never had to be fitted under the
  --            level cap after all.
  --   · scanᵉ  `(2 + pmᵗ V 0 f) ^ V * (hopDᵗ f + hopDᵗ z + hopDᵉ e)` —
  --            EXPONENTIAL in V, which is the room that funds repeated
  --            application, and the only row with no emit lemma yet.
  -- The worked instances for the last one are `pushTake-wet` and
  -- `pushMap-wet`; `pushThru-walk` below (PROVEN, thru-outer) is the
  -- shape when a face has to carry the caps column too.
  --
  -- THE GAS-PEEL FINDING, and it is what took this family off FALSITY.
  -- Evaluator:1436-38 and 1453-58:
  --
  --     subscribeE fuel (mapᵉ f b) κ id now sched st =
  --       let (burst , sched₁ , st₁) = subscribeE fuel b (map-f f ↠ κ) …
  --       in pushBurst fuel id now (map-f f) κ burst sched₁ st₁
  --
  -- `fuel` goes to the recursive call and to `pushBurst` UNCHANGED, and
  -- the scanᵉ clause does the same.  The chain frames spend no gas; only
  -- μᵉ and subscribeAll/subscribeInner do.  The FALSITY once carried by
  -- this family is series Q's, and series Q's mechanism is gas
  -- exhaustion — a static sum (`sucG`) failing to dominate a runtime
  -- product (d·k).  A clause that peels no gas is not a place that
  -- mechanism can bite: `hasDry`/`regsLen?` here are a TRANSPORT across
  -- one frame at the same fuel.  The block header above carries the
  -- argument in full, including why series Q would refute the four
  -- PROVEN *All rows before it touched any of these.
  --
  -- one-shot emitter — GRINDABLE.  oneShotBurst with the state untouched,
  -- the same shape as input-wet-scripted's cold-nil (that census names the
  -- ingredient per conjunct, and they carry over): INV?-widen with the mint
  -- transparent, mapValue-B, mapValue-hop, oneShot-tail-dry, and regsLen?
  -- straight off the hypothesis.  THE ONE DIFFERENCE, and it is the whole
  -- residue: the values here are `map evalTm ts`, not a slot's, so their
  -- size/weight bound comes from an evalTms lemma.
  --
  -- ⚠ "evalTms-caps HAS NO WET TWIN. THAT TWIN IS THIS ROW" WAS WRONG
  -- (corrected 2026-08-20).  `ofVals-B` (.Wet/Part1) IS that twin and is
  -- PROVEN: it gives `all (valB? (capᴱ W (E * 3 ^ suc Ψ)) Ψ u)` over
  -- `map evalTm ts` from a size and a fnCap hypothesis on the terms, i.e.
  -- BOTH halves this row needs.  It is not a drop-in — its bound is
  -- capᴱ-shaped and has to be fitted under the caps ladder's B, which is
  -- the actual residue — but "no twin exists" would send the next reader
  -- to re-derive a proven lemma, which is the one failure the SEARCH FIRST
  -- rule exists to prevent.  Fit it; do not restate it.
  walk-of : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (ts : List (Tm Γ [] [] [] u)) → WalkStmt {e = e} (ofᵉ ts)
  -- spent one-shot — GRINDABLE, and the CHEAPEST row in the family: it is
  -- walk-of at `vals ≡ []`.  `oneShotBurst []`, state untouched, so
  -- oneShot-tail-dry degenerates, the two value conjuncts (burstB?,
  -- burstHopD?) are vacuous over an empty payload, and regsLen? is the
  -- hypothesis.  `hopDᵉ V η emptyᵉ = 0`.  Needs no evalTms twin — there
  -- are no values.
  --
  -- ⚠ "NO RESIDUE AT ALL" WAS OVERSTATED (corrected 2026-08-20): FOUR of
  -- the nine conjuncts are not vacuous over an empty payload.  capsOK? is
  -- about sched₁/st and not the payload at all; burstCount? reduces to
  -- `0 ≤ᵇ cWid` by computation rather than by emptiness; the level bound
  -- needs `+-identityʳ` plus inflationarity; and INV? — which this row
  -- comment omitted entirely — is a STATE conjunct needing that transport
  -- plus mint-transparency (INV? reads the schedule only through
  -- `Sched.live` and `Sched.slots`, while mintSource touches `nextSource`
  -- alone).  The honest statement is "residue is four definitional
  -- transports and no lemma" — still the cheapest row in the family.  And
  -- the better twin for conjuncts 1-4 is the PROVEN `subscribeE-caps`
  -- emptyᵉ clause (.Subscribe-Face), not the open sibling walk-of.
  walk-empty : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} →
    WalkStmt {e = e} (emptyᵉ {t = u})
  -- the eight OTHER conjuncts of the scan clause — SHAPE, and the
  -- restatement has been made: this leaf now takes the walk's own
  -- INDUCTION HYPOTHESIS (`wb : WalkStmtAt g b`) and is stated at a fixed
  -- gas, like every other clause in the family.
  --
  -- ⚠ WHY IT WAS UNPROVABLE AS FIRST STATED (2026-08-20), and it is not a
  -- matter of difficulty.  The old form quantified over an ARBITRARY
  -- `b : Closed Γ s` with no hypothesis about it, while all eight of its
  -- conjuncts are assertions about the result of `subscribeE g (scanᵉ f z b)`
  -- — which unfolds THROUGH b's own subscribe.  Nothing could close that:
  -- this leaf is not recursive (walkFace is), and it cannot be made mutual
  -- with walkFace because it lives BELOW it.  `walkFace` does hand `wb` to
  -- `walk-scan`, and `walk-scan` spends it on `walk-scan-source` and
  -- `walk-scan-hop-spn` — but it was never threaded to this leaf, so the
  -- one hypothesis that makes the clause provable stopped one call short.
  -- The tell was visible in the family without looking at any proof: every
  -- sibling clause (walk-map, walk-take, and both scan halves above) takes
  -- `wb`, and this one did not.
  --
  -- The restatement is NOT a weakening and needs no further justification
  -- than that: `wb` is the induction hypothesis, it is already in scope at
  -- the single call site, and the alternative reading — that the clause is
  -- true without it — is refuted by the shape of the statement rather than
  -- by any fact about scan.
  --
  -- For what the eight then cost, the map clause is the worked instance:
  -- a real body (`walk-map` ⊗ `pushMap-wet`, .Walk-Level/Parts).
  --
  -- THE MIRROR, AND ITS COVERAGE BOUNDARY (2026-08-20).  `subscribeE-walkS`
  -- (.Wet/Part2) is a PROVEN recursive wet walk whose scanᵉ clause mirrors
  -- this one piece for piece, and `subscribeE-caps`' scanᵉ clause mirrors
  -- the caps column.  Between them they FIX this clause's skeleton:
  --   witness       `j₀ + suc (j₁ + j₂)`
  --   seed, size    `evalSeed-caps` — its j₀ is what pays the seed's eval
  --   seed, Ψ       `fnCap-evalWith Ψ z []ᵃ tt` — NO ladder, Ψ does not grow
  --   mint+install  `INV?-install`, with `capsOK?-setNode` /
  --                 `capsOK?-nextNode` on the caps side
  --   recursion     `wb`, at `suc (j + j₀)`
  --   the push      a bespoke Ψ-only face over a `stepScan-wet`
  --
  -- BUT THE MIRROR CANNOT BE CALLED, and the reason is the INDEX SYSTEM
  -- rather than the mathematics: `capᴱ W E = (2 + 2 * W) ^ E` (with E
  -- growing as `E * 3 ^ suc Ψ`) and `frameStep`'s `iterSize` are two
  -- different exponential ladders, and they meet only where .Caps-Bridge
  -- instantiates them together at the TOP (`sizeCapAt` / `capsAt`), never
  -- at an arbitrary mid-walk `frameStep (j + j′) c`.  That is the same
  -- reason map needed its own `pushMap-wet` instead of reusing the
  -- frame-generic `pushBurst-wet`.  So: read the mirror for the
  -- ingredients and their indices; do not try to import it.
  --
  -- A related note, because it reads like a contradiction and is not:
  -- `pushBurst-wet` IS frame-generic and proven, while the DEAD ROUTE
  -- beside `pushBurst-walk` rules a frame-generic wet push face FALSE.
  -- The refutation is about the HOP ledger, which is frame-specific; Ψ and
  -- the capᴱ size index are not.  Different columns.  And the hop column
  -- is the one column THIS row does not owe — `walk-scan` pays conjunct 7
  -- through `walk-scan-hop-spn` ⊗ `burstHopSpn-cap`.
  --
  -- Finally, the accumulator needs NO new invariant field: `INV?` already
  -- covers node states on both axes (`fnCapNode Ψ (scan-st v)` is
  -- `fnCapᵛ v ≤ᵇ Ψ`; `stBounded?` carries `boundedNode`), so the bound
  -- comes in and goes out as a projection of a hypothesis this leaf
  -- already takes.  `INV?-setNode` (.Walk-Level/Parts) is the step.
  --
  -- ⚠ CLASS HISTORY, because this header and the ledger had DRIFTED apart:
  -- this row was moved to FALSITY in PROOF-STATE on 2026-08-20 while this
  -- header still read GRINDABLE, and walk-map/walk-take were then raised
  -- to FALSITY for consistency with the ledger row.  All three raises are
  -- WITHDRAWN (2026-08-20) on the gas-peel finding in the census above:
  -- the scanᵉ clause passes `fuel` unchanged to both the recursive
  -- subscribe and the push (Evaluator:1453-58), so series Q's gas
  -- exhaustion cannot be sited here either.  GRINDABLE was also wrong —
  -- the scan-f push face is unauthored and its frame-generic form is
  -- REFUTED — which leaves DIFFICULTY, agreeing with the two rows this
  -- one is tied to.  scanᵉ mints no subscription
  -- mapᵉ does not: subscribeE's scan clause (Evaluator:1453) installs ONE
  -- node, subscribes the source with `scan-f f nid ↠ κ`, and pushes the
  -- resulting burst — the same install-subscribe-push the other chain
  -- frames run, with `scanFrame-caps` (.Caps-Face, PROVEN) paying the
  -- frame charge and `subscribeE-caps` delegating the caps half.  So the
  -- *budget* really is map-difficulty, which is what this leaf's shape
  -- records; none of these eight ever sees the fold's arithmetic.
  walk-scan-rest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (g : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (z : Tm Γ [] [] [] u)
    (b : Closed Γ s) (wb : WalkStmtAt {e = e} g b) →
    WalkStmtAt⁻ᴴ {e = e} g (scanᵉ f z b)
  -- (walk-mu is GROUND — forward-declared below, body after walkFace)
  -- registration + parked body — GRINDABLE.  The clause that MINTS a
  -- registry entry, so regsLen?'s growth is paid here, and it is the
  -- ONLY row in this family that neither recurses nor pushes: install,
  -- mint, park, register, and the burst is `init src ∷ []` (Evaluator:
  -- 1485-1496).  So four of the wet five are cheap — no values in the
  -- burst at all, hence burstB? and burstHopD? over an empty payload
  -- (`hopDᵉ V η (deferᵉ e) = 0`), hasDry by computation on a lone init,
  -- INV? by INV?-install (below, PROVEN) then addLive-INV (.Wet/Part2,
  -- PROVEN).  The fifth, regsLen?, IS DISCHARGED (2026-08-19): `walk-defer`
  -- below is a real body pairing this leaf with PROVEN register-regsLen,
  -- which is why this leaf is at WalkStmt⁻ rather than WalkStmt.  What the
  -- defer clause registers is `thru-outer mergeᵒ nid ↠ κ` over an
  -- installNode — one longer than κ, and installNode leaves the registry
  -- alone — so the growth is funded by G, which is at least 1 here because
  -- `syncSizeᵉ (deferᵉ e) = 1` sits in dBound's summand position.
  walk-defer-eight : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (body : Closed Γ u) → WalkStmt⁻ {e = e} (deferᵉ body)

-- THE *All BODY'S PIECES — INV?-install (below, after all-setNode) and the
-- push face its assembly (below) consumes.

------------------------------------------------------------------
-- THE μ CLAUSE'S REMAINING MISSING PIECE.  Everything else walk-mu spends
-- is proven and named in its body; this is what the caps twin could NOT
-- donate (`ceil`/`lb` are wet-side reset-anchor pins; subscribeE-caps
-- carries no L̂ ledger).  fnCap-unfoldμ is now proven in .Measures.
------------------------------------------------------------------
-- THE μ LEVEL DESCENT, for the L̂ ceiling.  A μ unfolding is a FRESH
-- ENTRY, not a chain edge: it subscribes a LARGER term at a MINTED
-- index (`suc (sizeAt S (j + j₀))`) while spending one nesting level,
-- which is exactly the shape `op-step-mu` (.Caps-Chain) already opens
-- quadratic room for.  ROUTE: sLvlD-suc converts LHS to sLvlD; sLvlD-mono
-- bounds sLvlD (j+j₀) ≤ sLvlD J₀ under hJ₀; two -infl steps; opIterD-suc
-- closes.  hJ₀ at the call site is j + j₀ ≤ J₀ = suc(j + suc B * suc B)
-- with B = cSize(frameStep j c), derived from szb via quad-arith.
-- SEALED: body on the budget-sufficient spine; consumers need only the type.
abstract
  mu-lvl-desc : ∀ (c : Caps) (d bud m j j₀ : ℕ) → 2 ≤ Caps.cSize c →
    j + j₀ ≤ suc (j + suc (Caps.cSize (frameStep j c)) * suc (Caps.cSize (frameStep j c))) →
    opIterD (Caps.cSize c) (Caps.cWid c) d bud
            (suc (Caps.cSize (frameStep (j + j₀) c))) (j + j₀)
      ≤ opIterD (Caps.cSize c) (Caps.cWid c) d (suc bud) (suc m) j
  mu-lvl-desc c d bud m j j₀ 2≤S hJ₀ =
    let S  = Caps.cSize c
        W  = Caps.cWid c
        J₀ = suc (j + suc (Caps.cSize (frameStep j c)) * suc (Caps.cSize (frameStep j c)))
        J₂ = opIterD S W d (suc bud) m (sLvlD S W d (suc bud) J₀)
    in ≤-trans (≤-reflexive (sym (sLvlD-suc S W d bud (j + j₀))))
       (≤-trans (sLvlD-mono d d (suc bud) (suc bud) 2≤S ≤-refl ≤-refl hJ₀ ≤-refl ≤-refl)
       (≤-trans (opIterD-infl S W d (suc bud) m (sLvlD S W d (suc bud) J₀))
       (≤-trans (fIterD-infl S W d (suc bud) (suc (widAt S W J₂)) J₂)
                (≤-reflexive (sym (opIterD-suc S W d (suc bud) m j))))))
