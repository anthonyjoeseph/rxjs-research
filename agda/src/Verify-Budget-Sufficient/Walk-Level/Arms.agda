-- THE SLOT DISPATCH AND ITS OTHER TWO ARMS — the shared slot's live and
-- fresh branches, the scripted slot, and the `with` that picks between
-- them.  The connect arm is one arrow below, and everything here
-- RECEIVES the walk face as an argument (`wl : WalkLevelAt (peelGas g)`)
-- rather than calling it, so none of it is part of the walk's recursion.
--
-- WHY THAT IS WORTH A MODULE, and it is a measured reason.  Sitting
-- textually among the dispatch's declarations put these INSIDE its
-- mutual block, and a block member in no cycle cannot be stubbed: every
-- focused check of every OTHER member re-proved all of these bodies in
-- full.  That was the whole of the per-member loop's overrun — the
-- statement telescopes and the lemma shelf together were worth a couple
-- of seconds, these were worth the rest.
--
-- Re-exported `public` upward, so no consumer can tell any of this
-- moved.

module Verify-Budget-Sufficient.Walk-Level.Arms where

open import Data.Bool    using (Bool; T; true; false; _∨_; _∧_; not; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _<_;
                                _≤ᵇ_; _<ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; ≤-pred;
                                       m≤m+n; m≤n+m; n≤1+n;
                                       +-suc; +-assoc; +-comm;
                                       +-mono-≤; +-monoʳ-≤; +-monoˡ-≤;
                                       *-mono-≤; *-monoʳ-≤;
                                       +-identityʳ;
                                       m≤m⊔n; m≤n⊔m; ≤⇒≤ᵇ; ≤ᵇ⇒≤)
open import Data.Fin     using (Fin; toℕ)
open import Data.Vec     using (Vec; lookup)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Data.List    using (List; []; _∷_)

open import Rx.Prim      using (Tick; Id; Source; init; value; close;
                                complete; handoff; exhausted; dried;
                                cut; cutPending; subscribe;
                                InstEmit; InstEvent; _at_from_as_;
                                Gas; g0; gs; gasPad; ObservableInput; hot; cold;
                                Timed)
open import Rx.Exp       using (Ty; obs; natᵗ; _×ᵗ_; Ctx; Closed; Val; Exp; Tm; Fn;
                                inputsBelowᵉ; isData;
                                _≟ᵗ_;
                                sizeᵉ; sizeᵗ; sizeᵛ; syncSizeᵉ;
                                shellSizeᵉ; innerᵉ;
                                input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                                mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                                μᵉ; varᵉ; deferᵉ; unfoldμ; applyFn; evalTm)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵛ; pmᵗ; hopD-unfoldμ)
open import Rx.Slot-Hop  using (slotHop; slotHop-fix)
open import Rx.Evaluator using (Sched; EvalSt; Slots; Slot; shared; scripted;
                                RegId; Chain;
                                memberSource; Path; root; share-sink; _↠_;
                                Stream; subscribeE; sharedConnect;
                                subscribeAll; AllOp;
                                mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ;
                                NodeState; merge-st; concat-st;
                                switch-st; exhaust-st; scan-st; take-st; scan-f;
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
-- the transformer monotonicity/inflation family, cited directly by the
-- loop faces' ceiling conversions
-- proven projections and per-emit plumbing off the caps push face —
-- pieces, never the face itself (the wet twin re-walks its skeleton
-- so both halves share one witness)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthE; depthAll; depthBurst; depthFrame; depthInner;
         depthConsume; depthWalk; depthSlot; depthConn)
open import Verify-Budget-Sufficient.Walk-Level.Connect public


-- THE SHARED SLOT, ASSEMBLED (2026-08-19).  Was one opaque postulate over
-- the whole slot; it is now the real three-way dispatch subscribeSharedSlot
-- performs, against the PROVEN clause-for-clause twin `sharedSlot-caps`
-- (.Subscribe-Face), whose three arms are these three at the same
-- scrutinees and in the same order.
--
-- ARM A (spent share) and ARM B (live share) are CLOSED HERE — neither
-- connects, so neither recurses, and between them they account for four of
-- the wet five by computation:
--   · burstB? / burstHopD?  `eventB?` and `hopDev?` are `true` on init,
--     close, handoff and complete alike (.Measures) and these two arms emit
--     no values at all, so both are refl.
--   · hasDry                `dryEvent` fires on `close _ dried` ALONE
--     (Evaluator:370); arm A emits `close _ exhausted`, arm B emits no
--     close.  refl both times.
--   · INV? (arm A)          the state is untouched, so this is INV?-widen
--     across the cap step, and `frameStep-mono-j` supplies the step.
--   · regsLen?              arm A leaves the registry alone (the
--     hypothesis); arm B is PROVEN register-regsLen, spending
--     `pathLen κ ≤ ℓ` out of this statement's own `pathLen κ + G ≤ ℓ`.
-- What is left of arm B is its INV? alone (`shared-live-INV`), and arm C is
-- `sharedConnect-walk`.  Both are stated above with their routes.
input-wet-shared : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ : ℕ)
    (g : Gas) → WalkLevelAt (peelGas g) →
    ∀ (i : Fin n) (b : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e)
    (d : Closed Γ (lookup Γ i)) {ok : T (inputsBelowᵉ (toℕ i) d)} →
    Sched.slots sched i ≡ shared d {ok = ok} →
    -- b is BOUND, not applied: the measures below take a general
    -- `Exp Γ Δᵍ Δ Θ t`, and only a binder pins those three contexts to
    -- `[]` — an alias of type `Closed Γ _` does not, so writing
    -- `sizeᵉ (input i)` here leaves an unsolved meta per measure.
    b ≡ inputᶜ i →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Caps.cReg c ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ b ≤ Caps.cSize (frameStep j c) →
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
    in capsOK? (frameStep (j + j′) c)
               (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
       burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true →
       burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true →
       j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j →
       (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
              (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
       × (burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b)
                     (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)
       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
-- `with … in slotEq2`, NOT `with … | slotEq`.  Both abstract the scrutinee
-- so that subscribeE's own `with Sched.slots sched i` can fire — that much
-- is forced, since subscribeE is stuck on it and the goal does not mention
-- it syntactically, which is why `rewrite` cannot serve here.  But the
-- `| slotEq` form CONSUMES the equation, and arm C has to hand it on to
-- sharedConnect-walk; re-forming it as `refl` afterwards does not typecheck
-- (Agda re-elaborates `Sched.slots sched i` un-reduced).  The `in` form
-- keeps it, at the cost of a scripted branch that slotEq itself refutes.
input-wet-shared c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g wl i b κ bid now sl sched st
  d slotEq refl 2≤S 1≤R hCR slEq slC slSz cOK szb pSz lC nst hidx dpt invW fnC pB
  s2 fS rS ceil lb dmd gas lℓ rgs cOK′ bC bCnt jle
  with Sched.slots sched i in slotEq2
-- the slot cannot be scripted: this face was dispatched on `shared`
... | scripted s with slotEq
...   | ()
input-wet-shared c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g wl i b κ bid now sl sched st
  d slotEq refl 2≤S 1≤R hCR slEq slC slSz cOK szb pSz lC nst hidx dpt invW fnC pB
  s2 fS rS ceil lb dmd gas lℓ rgs cOK′ bC bCnt jle
  | shared d′
  with memberSource (toℕ i) (EvalSt.completedSources st)
-- ARM A — the spent share.  sched and st both untouched, so the only
-- moving part is the cap widening on INV?.
...  | true =
    INV?-widen sched st (proj₁ (frameStep-mono-j c 2≤S (m≤m+n j j′))) invW
  , refl , refl , refl , rgs
...  | false with memberSource (toℕ i) (EvalSt.connectedShares st) in eqM
-- ARM B — the live share joins mid-flight: one `init`, and a registration.
...    | true =
    shared-live-INV c Ψ j j′ (toℕ i) κ sched st 2≤S hCR cOK′ invW pB
  , refl , refl , refl
  , register-regsLen ℓ (toℕ i) κ st (≤-trans (m≤m+n (pathLen κ) G) lℓ) rgs
-- ARM C — the connect, and the only arm that recurses; `wl` goes with it.
...    | false =
  sharedConnect-walk c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g wl i b κ bid now sl
    -- `dpt` needs NO transport: depthE at an input is `depthSlot … (Sched
    -- .slots sched i)` by refl (.Caps-Depth) and depthSlot takes the slot
    -- as its LAST argument, so the with-abstraction of the scrutinee has
    -- already carried this hypothesis' type to depthConn at d′.  That is
    -- the whole reason the leaf is stated at depthConn.
    -- eqM is ARM C's own scrutinee equation, kept by `with … in eqM`
    -- above.  It IS the freshness premise the leaf now takes, and it is
    -- free here precisely because this arm is the not-yet-connected
    -- branch — the same branch `subscribeSharedSlot` guards on.
    sched st d′ slotEq2 refl eqM 2≤S 1≤R hCR slEq slC slSz cOK szb pSz lC nst hidx dpt
    invW fnC pB s2 fS rS ceil lb dmd gas lℓ rgs cOK′ bC bCnt jle

postulate
  -- SHAPE C — cold, no async tail.  oneShotBurst; the schedule takes a
  -- mint and the state is untouched, so the whole clause is the burst's
  -- own three conjuncts plus INV? across the mint.
  --
  -- GRINDABLE, and every ingredient is located and PROVEN: burstB? is
  -- `mapValue-B` (.Measures) under `all-++-intro`, burstHopD? is
  -- `mapValue-hop` (.Walk-Level/Parts), hasDry is `oneShot-tail-dry`
  -- (.Measures) after the leading `init`, and INV? is `INV?-widen`
  -- (.Wet/Part1) across `frameStep-mono-j` — the mint is invisible to
  -- INV?, which reads the schedule only through `live` and `slots`.
  --
  -- WHAT IS ACTUALLY OWED, and it is two value-level bounds on `sync`
  -- rather than anything about the clause.  `mapValue-B` wants
  -- `all (valB? B Ψ u) sync`, whose SIZE half is `slotCaps?`'s first
  -- conjunct at this slot (.Caps-Face/Part1) reached through a
  -- tabulate-lookup projection of `slotsCaps?`; and whose Ψ half is FREE,
  -- because `fnCapᵛ` is nonzero only at `obs` and this slot's element type
  -- is data — that is what the `ok : T (isData …)` binder buys.
  --
  -- THAT SECOND HALF NEEDS ONE NEW LEMMA AND IT DOES NOT EXIST YET:
  -- `T (isData u) → fnCapᵛ u v ≡ 0`, by induction on the type.  Its exact
  -- twin IS proven — `outWᵛ-data` (.Caps-Face/Part5) is the same induction
  -- for `outWᵛ` — so the route is a transcription, not a design.  Searched
  -- for under `make find Q='fnCapᵛ'` and `Q='isData'`: absent.
  scripted-cold-empty-four : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ : ℕ)
    (g : Gas)
    (i : Fin n) (b : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e)
    {ok : T (isData (lookup Γ i))}
    (sync : List (Val Γ (lookup Γ i))) →
    Sched.slots sched i ≡ scripted {ok = ok} (cold sync []) →
    -- b is BOUND, not applied: the measures below take a general
    -- `Exp Γ Δᵍ Δ Θ t`, and only a binder pins those three contexts to
    -- `[]` — an alias of type `Closed Γ _` does not, so writing
    -- `sizeᵉ (input i)` here leaves an unsolved meta per measure.
    b ≡ inputᶜ i →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Caps.cReg c ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ b ≤ Caps.cSize (frameStep j c) →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    nest b sl (EvalSt.connectedShares st) ≤ bud →
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
    in capsOK? (frameStep (j + j′) c)
               (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
       burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true →
       burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true →
       j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j →
       (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
              (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
       × (burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b)
                     (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)

  -- SHAPE D — cold with an async tail.  A fresh source per subscribe: two
  -- mints, one live source prepended, and the state registered.
  --
  -- ⚠ THE CENSUS'S ROUTE FOR THIS SHAPE DOES NOT COMPOSE AS WRITTEN, and
  -- that is this leaf's reason to exist.  It says "register-INV then
  -- addLive-INV", and both lemmas are real: `shared-live-INV` (.Connect,
  -- now PROVEN) moves INV? across the register, and `addLive-INV`
  -- (.Wet/Part2) moves it across exactly this record update.  But they do
  -- not meet.  `shared-live-INV` needs a caps receipt at the schedule it
  -- registers under — the PRE-addLive one — while the receipt this clause
  -- is handed (`cOK′`) is stated at the POST-addLive schedule, and
  -- `capsOK?` genuinely reads `Sched.live`: its widLive conjunct is
  -- `all (widLive (Caps.cWid c) (Sched.slots sched)) (Sched.live sched)`
  -- (see capsOK?-parts, .Caps-Face/Part4).  So a third step is owed that
  -- the census never named: DROP one live entry from a caps receipt.
  --
  -- It looks cheap rather than deep — `all p (l ∷ ls) ≡ true` gives
  -- `all p ls ≡ true`, slots are untouched by the mint, and the other four
  -- capsOK? conjuncts do not read `live` at all — but it is a missing
  -- ingredient and not a slip, so it is recorded here rather than assumed.
  -- Establish it BEFORE grinding the rest of this shape: if the drop is
  -- not available the INV? conjunct needs a different assembly, and the
  -- other three conjuncts are wasted work until that is known.
  --
  -- The other three conjuncts are shape C's, minus the tail: burstB? and
  -- burstHopD? are the same `mapValue-B` / `mapValue-hop` over the same
  -- two bounds on `sync` (so C's owed lemmas serve both), and hasDry is
  -- `mapValue-dry` with `any-dry-++` (both .Walk-Level/Parts) since this
  -- burst carries no close at all.
  scripted-cold-async-four : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ : ℕ)
    (g : Gas)
    (i : Fin n) (b : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e)
    {ok : T (isData (lookup Γ i))}
    (sync : List (Val Γ (lookup Γ i)))
    (d : Timed (Val Γ (lookup Γ i)))
    (ds : List (Timed (Val Γ (lookup Γ i)))) →
    Sched.slots sched i ≡ scripted {ok = ok} (cold sync (d ∷ ds)) →
    -- b is BOUND, not applied: the measures below take a general
    -- `Exp Γ Δᵍ Δ Θ t`, and only a binder pins those three contexts to
    -- `[]` — an alias of type `Closed Γ _` does not, so writing
    -- `sizeᵉ (input i)` here leaves an unsolved meta per measure.
    b ≡ inputᶜ i →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Caps.cReg c ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ b ≤ Caps.cSize (frameStep j c) →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    nest b sl (EvalSt.connectedShares st) ≤ bud →
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
    in capsOK? (frameStep (j + j′) c)
               (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
       burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true →
       burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true →
       j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j →
       (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
              (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
       × (burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b)
                     (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)

-- no connect, so no recursion: a scripted slot replays its own values
--
-- ═══ THE CENSUS (2026-08-19).  FOUR SHAPES × THE WET FIVE ═══
-- GRINDABLE.  The precedent is `subscribeE-input-caps` (.Subscribe-Face,
-- PROVEN), whose scripted side splits into exactly these four branches
-- and whose clauses correspond one-to-one.  Note this postulate takes NO
-- walk face (contrast input-wet-shared) — the scripted slot never
-- connects, so nothing here recurses and no induction has to be designed.
-- The caps receipts arrive as HYPOTHESES, so only the wet five are owed.
--
-- What subscribeE produces (Evaluator:1401-1426), and the ingredient for
-- each conjunct.  Every one named below is PROVEN except where marked:
--
--   A. hot, memberSource ≡ true — burst init/close-exhausted/complete;
--      sched AND st untouched; caps twin returns j′ = 0.
--        INV?       INV?-widen (.Wet/Part1) over +-identityʳ
--        burstB?    no values in the burst — computation
--        burstHopD? no values in the burst — computation
--        hasDry     dryEvent fires on `dried` ALONE (Evaluator:370), and
--                   this burst carries `exhausted` — computation
--        regsLen?   registry untouched — the hypothesis, as-is
--
--   B. hot, memberSource ≡ false — burst `init` only; st = register; j′ = 1.
--        INV?       register-INV (.Wet/Part1)
--        burstB?    no values — computation
--        burstHopD? no values — computation
--        hasDry     `init` only — computation
--        regsLen?   ⚠ register-regsLen — THE ONE GAP, stated below
--
--   C. cold sync [] — oneShotBurst; st untouched; j′ = 1.
--        INV?       INV?-widen; the mint is TRANSPARENT (below)
--        burstB?    mapValue-B (.Measures)
--        burstHopD? mapValue-hop (above, this module)
--        hasDry     oneShot-tail-dry (.Measures)
--        regsLen?   registry untouched — the hypothesis, as-is
--
--   D. cold sync (d ∷ ds) — mint + addLive; st = register; j′ = 1.
--        INV?       register-INV then addLive-INV (.Wet/Part2)
--        burstB?    mapValue-B (.Measures)
--        burstHopD? mapValue-hop (above, this module)
--        hasDry     mapValue-dry + any-dry-++ (above, this module)
--        regsLen?   ⚠ register-regsLen — THE ONE GAP, stated below
--
-- THE MINT IS TRANSPARENT TO INV?, which is why C and D need no lemma for
-- it: INV? reads the schedule ONLY through `Sched.live` and `Sched.slots`
-- (Measures:4438, via stBounded? and fnCapBounded?), while mintSource and
-- mintOrdinal touch `nextSource` / `nextOrdinal` alone (Evaluator:305).
-- The record update reduces, so the mint is invisible to the predicate.
-- Only D's addLive genuinely moves `live`, and that is addLive-INV's job.
--
-- THE regsLen? CONJUNCT IS DISCHARGED (2026-08-19).  `input-wet-scripted`
-- below is a REAL BODY over this leaf: it pairs the four conjuncts owed
-- here with the PROVEN `input-wet-scripted-regs` (above, this module),
-- which closes the fifth for all four shapes off `register-regsLen`.  So
-- the ⚠ rows in A-D are shape B's and shape D's, and they are shut.
--
-- `pathLen κ ≤ ℓ`, which that lemma wants, comes from this statement's own
-- `pathLen κ + G ≤ ℓ` by m≤m+n — nothing new is spent for it.
--
-- PLACEMENT, a real constraint and cheap to get wrong: neither the leaf nor
-- the body takes a walk face, so neither may join the heavy mutual block
-- (block 42, 15 members — `make agda-dev ARGS='--list …'` shows them free).
-- The regs lemma sits ABOVE that block with the dry/hop helpers it spends
-- (retagEvents-dry, mapValue-hop, mapValue-dry, any-dry-++).  The regsLen?
-- helpers do NOT: capsOK⇒regsLen and regsLen?-mono sit ~1200 lines BELOW,
-- after the block, so anything of theirs a future clause wants moves up too.
--
-- ═══ TWO CHORES BEFORE THE GRIND, NEITHER STRUCTURAL ═══
-- Both are bookkeeping, and both are recorded because each reads as
-- already-done from the census above.
--
--   · THE PRECEDENT IS NOT IN SCOPE.  `subscribeE-input-caps` is named
--     as the clause-for-clause twin, and it is PROVEN, but it is absent
--     from this module's `using` list for .Subscribe-Face — so the twin
--     cannot be APPLIED here until it is added.  Deliberately not added
--     ahead of the body: an unapplied name in a `using` list earns no
--     reachability credit and is indistinguishable from clutter.  Add it
--     in the commit that spends it.
--   · EIGHT CONJUNCTS ARE ROUTED "BY COMPUTATION" AND NONE OF THE EIGHT
--     IS TYPECHECKED.  The census discharges them by inspection of the
--     evaluator, which is the same disclaimer the walkFace family carries
--     — located, not spent.  Expect the residue to be larger than four
--     lemmas, and treat any of the eight that does NOT fall out as the
--     finding rather than as a slip in the census.
input-wet-scripted-four : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ : ℕ)
  (g : Gas)
  (i : Fin n) (b : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t)
  (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e)
  {ok : T (isData (lookup Γ i))}
  (src : ObservableInput (Val Γ (lookup Γ i))) →
  Sched.slots sched i ≡ scripted {ok = ok} src →
  -- b is BOUND, not applied: the measures below take a general
  -- `Exp Γ Δᵍ Δ Θ t`, and only a binder pins those three contexts to
  -- `[]` — an alias of type `Closed Γ _` does not, so writing
  -- `sizeᵉ (input i)` here leaves an unsolved meta per measure.
  b ≡ inputᶜ i →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  sizeᵉ b ≤ Caps.cSize (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  nest b sl (EvalSt.connectedShares st) ≤ bud →
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
  in capsOK? (frameStep (j + j′) c)
             (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
     burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true →
     burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true →
     j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j →
     (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
            (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
     × (burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b)
                   (proj₁ r) ≡ true)
     × (hasDry (proj₁ r) ≡ false)
input-wet-scripted-four c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g i b κ bid now sl sched st (hot asy) slotEq refl
  2≤S 1≤R hCR slEq slC slS cOK szb pSz spL nst dpt inv fnc pB 2≤Ŝ FŜ R̂eq Ŝge opL dB gHas pℓ rgs cOK′ bC bCt jle
  with Sched.slots sched i | slotEq
... | .(scripted (hot asy)) | refl
  with memberSource (toℕ i) (EvalSt.completedSources st)
-- A. the spent script: close/complete at once, nothing registered, and
--    neither the schedule nor the state moves — so INV? is pure widening
--    and the burst carries no value to bound.
...   | true  =
        INV?-widen sched st (proj₁ (frameStep-mono-j c 2≤S (m≤m+n j j′))) inv
      , refl , refl , refl
-- B. the live script: one `init`, and the registration this face exists
--    for.  shared-live-INV (.Connect) is exactly it, and its caps receipt
--    is this clause's own cOK′ — the schedule does not move here, which
--    is precisely what shape D loses.
...   | false =
        shared-live-INV c Ψ j j′ (toℕ i) κ sched st 2≤S hCR cOK′ inv pB
      , refl , refl , refl
input-wet-scripted-four c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g i b κ bid now sl sched st (cold sync []) slotEq bEq
  2≤S 1≤R hCR slEq slC slS cOK szb pSz spL nst dpt inv fnc pB 2≤Ŝ FŜ R̂eq Ŝge opL dB gHas pℓ rgs cOK′ bC bCt jle =
  scripted-cold-empty-four c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g i b κ bid now sl sched st sync slotEq bEq
    2≤S 1≤R hCR slEq slC slS cOK szb pSz spL nst dpt inv fnc pB 2≤Ŝ FŜ R̂eq Ŝge opL dB gHas pℓ rgs cOK′ bC bCt jle
input-wet-scripted-four c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g i b κ bid now sl sched st (cold sync (d ∷ ds)) slotEq bEq
  2≤S 1≤R hCR slEq slC slS cOK szb pSz spL nst dpt inv fnc pB 2≤Ŝ FŜ R̂eq Ŝge opL dB gHas pℓ rgs cOK′ bC bCt jle =
  scripted-cold-async-four c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g i b κ bid now sl sched st sync d ds slotEq bEq
    2≤S 1≤R hCR slEq slC slS cOK szb pSz spL nst dpt inv fnc pB 2≤Ŝ FŜ R̂eq Ŝge opL dB gHas pℓ rgs cOK′ bC bCt jle

-- THE SCRIPTED SLOT, ASSEMBLED.  A real body over the four-conjunct leaf and
-- the proven regs lemma — the leaf-only shape, so that when a shape's wet
-- four lands the fit is tested by the typechecker rather than asserted.

input-wet-scripted : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ : ℕ)
  (g : Gas)
  (i : Fin n) (b : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t)
  (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e)
  {ok : T (isData (lookup Γ i))}
  (src : ObservableInput (Val Γ (lookup Γ i))) →
  Sched.slots sched i ≡ scripted {ok = ok} src →
  -- b is BOUND, not applied: the measures below take a general
  -- `Exp Γ Δᵍ Δ Θ t`, and only a binder pins those three contexts to
  -- `[]` — an alias of type `Closed Γ _` does not, so writing
  -- `sizeᵉ (input i)` here leaves an unsolved meta per measure.
  b ≡ inputᶜ i →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  sizeᵉ b ≤ Caps.cSize (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  nest b sl (EvalSt.connectedShares st) ≤ bud →
  -- TAKEN AND DROPPED.  The scripted slot never connects, so nothing here
  -- needs an ops ledger; this is carried only to keep the telescope aligned
  -- with input-wet-core's, which DOES need it for the connect arm.  It is
  -- not passed on, so the postulate above stays at full strength.
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
  in capsOK? (frameStep (j + j′) c)
             (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
     burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true →
     burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true →
     j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j →
     (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
            (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
     × (burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b)
                   (proj₁ r) ≡ true)
     × (hasDry (proj₁ r) ≡ false)
     × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
input-wet-scripted c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g i b κ bid now sl sched st
  src slotEq bEq 2≤S 1≤R hCR slEq slC slSz cOK szb pSz lC nst _ dpt invW fnC pB
  s2 fS rS ceil lb dmd gas lℓ rgs cOK′ bC bCnt jle =
  let (a₁ , a₂ , a₃ , a₄) =
        input-wet-scripted-four c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g i b κ bid
          now sl sched st src slotEq bEq 2≤S 1≤R hCR slEq slC slSz cOK szb pSz
          lC nst dpt invW fnC pB s2 fS rS ceil lb dmd gas lℓ rgs cOK′ bC bCnt jle
  in a₁ , a₂ , a₃ , a₄
   , input-wet-scripted-regs ℓ g i b κ bid now sched st src slotEq bEq
       (≤-trans (m≤m+n (pathLen κ) G) lℓ) rgs

-- the dispatch itself: match the slot, hand each shape its own residue.
input-wet-core : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ : ℕ)
  (g : Gas) → WalkLevelAt (peelGas g) →
  ∀ (i : Fin n) (b : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t)
  (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  -- b is BOUND, not applied: the measures below take a general
  -- `Exp Γ Δᵍ Δ Θ t`, and only a binder pins those three contexts to
  -- `[]` — an alias of type `Closed Γ _` does not, so writing
  -- `sizeᵉ (input i)` here leaves an unsolved meta per measure.
  b ≡ inputᶜ i →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  sizeᵉ b ≤ Caps.cSize (frameStep j c) →
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
  in capsOK? (frameStep (j + j′) c)
             (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
     burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true →
     burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true →
     j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j →
     (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
            (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
     × (burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b)
                   (proj₁ r) ≡ true)
     × (hasDry (proj₁ r) ≡ false)
     × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
input-wet-core c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g wl i b κ bid now sl sched st
  with Sched.slots sched i in slotEq
... | shared d   = input-wet-shared c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g wl i b κ bid now sl sched st d slotEq
... | scripted s = input-wet-scripted c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g i b κ bid now sl sched st s slotEq
