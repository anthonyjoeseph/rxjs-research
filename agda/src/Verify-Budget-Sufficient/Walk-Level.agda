-- THE COLLAPSED WALK — the E-into-j restatement (2026-08-13), executing
-- the ruling in Wet/Part6's GAP 4 header ("THE NESTING BUDGET IS THE
-- GAS").  The wet walk's running position is a caps LEVEL j — frameStep
-- iterated on the entry caps — and the capᴱ W E ledger is RETIRED from
-- the walk face entirely.  This is the only surviving route: the ledger
-- composition is machine-refuted at both ends (`wet-ceiling-absurd`
-- way-out, `wet-ell-absurd` way-in, Wet/Part6), and the two refutations
-- dissolve together under this collapse.
--
-- WHY ITS OWN MODULE.  The wet stratum (.Wet) and the caps face
-- (.Subscribe-Face) are deliberate siblings — neither imports the other
-- — and this statement is the one artifact that reads BOTH vocabularies
-- (INV?/dBound/hasAtLeast from the wet side, capsOK?/frameStep/opIterD
-- from the caps side).  It sits where .Caps-Bridge sits, one arrow
-- above each; .Caps-Bridge consumes it.
--
-- THE STATEMENT IS subscribeE-caps ⊗ THE WET CONTENT, ONE Σ.  The caps
-- half (hypotheses and the first four conclusion conjuncts) is
-- `subscribeE-caps`'s own face VERBATIM (.Subscribe-Face:937, GROUND) —
-- same prelims, same level index, same charge `j + j′ ≤ opIterD S W dep
-- bud ops j`.  That is deliberate: the level-threading pattern is
-- PROVEN through the whole mutual block there, so the grind adds wet
-- conjuncts to a skeleton that already walks, instead of inventing a
-- second walk.  The two halves must share ONE witness j′ — two separate
-- Σs could not be joined — which is why the caps conjuncts are
-- restated here rather than consumed as a black box.
--
-- THE RULING'S "VERIFY FIRST" ITEM, EXECUTED (census 2026-08-13, all
-- consumers of the old walk's conclusion traced): the old mintCount /
-- burstLen conjuncts do NOT reappear in wet flavour.  Their jobs are
-- the level machinery's own conjuncts, already carried here — registry
-- growth is capsOK?'s fifth conjunct (`length registry ≤ cReg
-- (frameStep J c)`), burst size is burstCount? at the same level — and
-- the census verdict is that NO consumer needs them at a caps level or
-- in mint flavour (they fed only the old walk's own induction; the
-- outer lenOK is sourced from caps-tick via capsOK?-count +
-- B2-cReg≤cSize, not from the walk).  The Ω width trio (widthOK? /
-- ofWᵉ ≤ Ω / pathΩ?) is retired WITH the ledger: Ω fed only walkCap's
-- base, and the caps side carries width as dWᵉ ≤ cWid.
--
-- WHAT SURVIVES UNCHANGED: the dry half.  The demand `dBound Ŝ R̂ U
-- (hopDᵉ F b) (syncSizeᵉ b) ≤ G` at the ENTRY-COMPUTABLE reset caps,
-- the gas `g hasAtLeast suc G`, and the length ledger `pathLen κ + G ≤
-- ℓ` / regsLen? — with ℓ now FREE, decoupled from Ŝ exactly as the
-- ruling says (`wet-ell-absurd` killed the ℓ := Ŝ pin, not the
-- ledger; the outer instantiation floats ℓ to pathLen κ + G ⊔ the
-- registry bound).
--
-- THE LANDING.  The outer face needs INV? at Ŝ = sizeCapAt e sl
-- (suc id).  The walk lands INV? at cSize (frameStep (j + j′) c); the
-- charge conjunct bounds j + j′ by opIterD, and the lift to Ŝ is the
-- SAME chain `sub-charge-capsOK-lift` already walks one stratum up
-- (.Caps-Bridge): opIterD-dominated → sizeCount-body → sizeCount-mono-d
-- over depOK → capsAt-suc-full → frameStep-mono-j, plus INV?'s upward
-- monotonicity in B (a lemma the core's grind owes; INV? weakens
-- upward conjunct by conjunct).
--
-- RECOVERY: git show eb11caf:agda/src/Verify-Budget-Sufficient/Measures.agda
-- restores the old ledger walk (subscribeE-walk, subscribeE-walk-core,
-- its 20 sub-postulates and the round-3 DAG) — deleted the day this
-- landed, because its composition with the core was refuted for every
-- parameter choice, not because its clauses were wrong.

module Verify-Budget-Sufficient.Walk-Level where

open import Data.Bool    using (Bool; true; false; _∨_; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _<_;
                                _≤ᵇ_; z≤n; s≤s)
open import Data.List    using (List; []; _∷_; _++_; length; map)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive;
                                       m≤m+n; m≤n+m; n≤1+n;
                                       +-suc; +-assoc; +-monoʳ-≤; +-identityʳ;
                                       m≤m⊔n; m≤n⊔m; ≤⇒≤ᵇ; ≤ᵇ⇒≤)
open import Data.Maybe   using (nothing)
open import Data.Bool.ListAction using (all; any)
open import Data.Fin     using (Fin; toℕ)
open import Data.Vec     using (Vec; lookup)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Rx.Prim      using (Tick; Id; Source; init; value; close;
                                complete; handoff; exhausted; dried;
                                cut; cutPending; subscribe;
                                InstEmit; InstEvent; _at_from_as_;
                                Gas; g0; gs; gasPad)
open import Rx.Exp       using (Ty; obs; natᵗ; _×ᵗ_; Ctx; Closed; Val; Exp; Tm; Fn;
                                sizeᵉ; sizeᵗ; sizeᵛ; syncSizeᵉ;
                                shellSizeᵉ; innerᵉ;
                                input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                                mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                                μᵉ; varᵉ; deferᵉ; unfoldμ; applyFn)
open import Rx.Frame-Width using (dWᵉ)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵛ; pmᵗ)
open import Rx.Evaluator using (Sched; EvalSt; Slots; Slot; shared; RegId; Chain;
                                memberSource; Path; root; share-sink; _↠_;
                                Stream; subscribeE; sharedConnect;
                                subscribeAll; AllOp;
                                mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ;
                                NodeState; merge-st; concat-st;
                                switch-st; exhaust-st;
                                splitBurst; hasDry; dryEvent;
                                sched-init; st-init; budgetAt; slotsSize;
                                opIterD; fIterD; fLvlD; sLvlD; sIterD; sizeAt;
                                Frame; thru-outer; pushBurst; stepFrame;
                                subscribeInner; splitEvents; retagEvents;
                                installNode; NodeId)

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
         splitEvents-valsCaps; splitEvents-bk-caps; burstCaps?-widen)
-- the chain-charge algebra subscribeE-caps' own *All head spends
open import Verify-Budget-Sufficient.Caps-Chain
  using (chain-desc; op-step; burst-index; burst-nil; burst-step;
         op-desc; push-desc; frame-desc; tail-desc;
         walk-desc; inner-desc)
-- proven projections and per-emit plumbing off the caps push face —
-- pieces, never the face itself (the wet twin re-walks its skeleton
-- so both halves share one witness)
open import Verify-Budget-Sufficient.Subscribe-Face
  using (countLen; countVals; countIn; valsOf; pushEmit-count;
         pushBurst-len; retagEvents-caps;
         burstCount?-widen; burstCount?-tail)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthE; depthAll; depthBurst; depthFrame; depthInner)
open import Verify-Budget-Sufficient.Op-Budget
  using (opIterD-dominated)


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
WalkStmt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} → Closed Γ u → Set
WalkStmt {n} {Γ} {t} {e} {u} b =
  ∀ (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ)
    (g : Gas) (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    -- caps prelims, subscribeE-caps' own
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
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
           (hopDᵉ F b) (syncSizeᵉ b) ≤ G →
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
       × (burstHopD? F (hopDᵉ F b) (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)
       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)

WalkLevel : Set
WalkLevel = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (b : Closed Γ u) → WalkStmt {e = e} b

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
    (∀ {n} {Γ : Ctx n} {t} (Ŝ R̂ U : ℕ) (body : Exp Γ (t ∷ []) [] [] t) →
      suc (dBound Ŝ R̂ U (hopDᵉ Ŝ (unfoldμ body)) (syncSizeᵉ (unfoldμ body)))
        ≤ dBound Ŝ R̂ U (hopDᵉ Ŝ (μᵉ body)) (syncSizeᵉ (μᵉ body))
     ) →
    -- hop-edge  (Verify-Budget-Sufficient/Wet/Part6.agda)
    (∀ {n} {Γ : Ctx n} {u} (Ŝ U r s : ℕ) → 2 ≤ Ŝ →
      (o : Val Γ (obs u)) → sizeᵛ (obs u) o ≤ Ŝ → hopDᵛ Ŝ (obs u) o < r →
      suc (dBound Ŝ (hopR Ŝ) U (hopDᵛ Ŝ (obs u) o) (syncSizeᵉ o))
        ≤ dBound Ŝ (hopR Ŝ) U r s
     ) →
    -- connect-edge  (Verify-Budget-Sufficient/Wet/Part6.agda)
    (∀ {n} {Γ : Ctx n} (Ŝ r s : ℕ) → 2 ≤ Ŝ →
      (sl : Slots Γ) (cs : List Source) (i : Fin n)
      {d : Closed Γ (lookup Γ i)} → sl i ≡ shared d →
      memberSource (toℕ i) cs ≡ false → sizeᵉ d ≤ Ŝ →
      suc (dBound Ŝ (hopR Ŝ) (unconn sl (toℕ i ∷ cs)) (hopDᵉ Ŝ d) (syncSizeᵉ d))
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
      (sched : Sched Γ) (st : EvalSt e) {dd : Closed Γ (lookup Γ i)} →
      Sched.slots sched i ≡ shared dd →
      memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false →
      unconn (Sched.slots (proj₁ (proj₂ (sharedConnect (gs fuel) i d κ id now sched st))))
             (EvalSt.connectedShares
               (proj₂ (proj₂ (sharedConnect (gs fuel) i d κ id now sched st))))
      < unconn (Sched.slots sched) (EvalSt.connectedShares st)
     ) →
    -- obs-slot-shared  (Verify-Budget-Sufficient/Keeps-Ring.agda)
    (∀ {n} {Γ : Ctx n} {u} (s : Slot Γ (obs u)) →
      Σ (Closed Γ (obs u)) λ d → s ≡ shared d
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
      (id : Id) (i : Fin n) {d : Closed Γ (lookup Γ i)} → sl i ≡ shared d →
      let V = sizeBudgetAt e sl id in
      (hopDᵉ V d ≤ hopR V) × (syncSizeᵉ d ≤ V)
     ) →
    -- hopD-map-emit  (Verify-Budget-Sufficient/Measures.agda)
    (∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s u} (V : ℕ)
      (f : Tm Γ Δᵍ Δ (s ∷ Θ) u) (b : Exp Γ Δᵍ Δ Θ s) (v : Val Γ s) →
      (f₀ : Fn Γ [] [] [] s u) → hopDᵗ V f₀ ≤ hopDᵗ V f → pmᵗ V 0 f₀ ≤ pmᵗ V 0 f →
      hopDᵛ V s v ≤ hopDᵉ V b →
      hopDᵛ V u (applyFn f₀ v) ≤ hopDᵉ V (mapᵉ f b)
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
  -- (pushThru-walk is REAL, stepThru-walk is an assembly over the
  -- leaf; the leaf's header names the live edge and the probe).
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
  -- NOT COVERED: μᵉ-recursive programs; programs with both deferᵉ AND
  -- sharedConnect in the same growth chain; the Q-series crossover
  -- region (multi-hour cost).  Class stays FALSITY.
  --
  -- NOTE for the opIterD level bound at the degenerate corner:
  -- `opIterD` is the identity at m = 0 (`opIterD-0`, Evaluator:811)
  -- and `ops` sits in the m position — so `ops = 0` would pin j′ = 0.
  -- It is excluded by the `suc (sizeᵉ b) ≤ ops` hypothesis, i.e. the
  -- positivity is already threaded.  `dep = 0` and `bud = 0` ARE
  -- reachable and are harmless: opIterD's `suc m` clause bumps J
  -- unconditionally (J₀ = suc (J + …)) before any d/k-dependent step
  -- runs.

  -- share/connect clause — expects connect-edge, sharedConnect-unconn,
  -- obs-slot-shared, unconn-keeps, unconn-cons-≤, connect-anchor and
  -- the two share-novals lemmas; connect is one of the three gas peels
  walk-input : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (i : Fin n) → WalkStmt {e = e} (input i)
  -- one-shot emitter — expects oneShot-tail-dry for hasDry
  walk-of : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (ts : List (Tm Γ [] [] [] u)) → WalkStmt {e = e} (ofᵉ ts)
  -- spent one-shot — oneShot-tail-dry at vals ≡ []
  walk-empty : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} →
    WalkStmt {e = e} (emptyᵉ {t = u})
  -- chain edge — expects hopD-map-emit and applyFn-size for the
  -- within-instant growth conjuncts
  walk-map : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (f : Fn Γ [] [] [] s u) (b : Closed Γ s) → WalkStmt {e = e} (mapᵉ f b)
  -- node install; takeᵉ 0 is a spent one-shot (oneShot-tail-dry)
  walk-take : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (cnt : Tm Γ [] [] [] natᵗ) (b : Closed Γ u) →
    WalkStmt {e = e} (takeᵉ cnt b)
  -- the accumulator clause — the one that GROWS values within an
  -- instant (applyFn-size is the Ŝ-ceiling supplier; the P-series
  -- probe receipts in the block header above ran exactly this shape)
  walk-scan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (f : Fn Γ [] [] [] (u ×ᵗ s) u) (z : Tm Γ [] [] [] u)
    (b : Closed Γ s) → WalkStmt {e = e} (scanᵉ f z b)
  -- the μ gas peel — expects mu-edge, shellSize-unfoldμ,
  -- inner-unfoldμ, hasAtLeast-peel; stated gas-generic (the g0
  -- instance is vacuously true: its hypotheses are contradictory,
  -- which walkFace's absurd clause proves rather than assumes)
  walk-mu : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (body : Exp Γ (u ∷ []) [] [] u) → WalkStmt {e = e} (μᵉ body)
  -- registration + parked body — the clause that MINTS a registry
  -- entry, so regsLen?'s growth is paid here
  walk-defer : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (body : Closed Γ u) → WalkStmt {e = e} (deferᵉ body)

-- THE *All BODY'S PIECES — the two plumbing lemmas and the push face
-- its assembly (below) consumes.
postulate
  -- INV? across a node install plus a nextNode mint, lifted one level.
  -- Conjunct by conjunct: stBounded?'s new-node entry is the caps
  -- boundedNode hypothesis (both read the same node list), fnCapBounded?'s
  -- is fnCapNode; the registry conjuncts don't see nodes; the slot
  -- conjuncts transport along the slots equality; every B test is ≤ᵇ,
  -- upward in B.  The nextNode field is read by NO conjunct.
  INV?-install : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (Ψ B B′ : ℕ) (nid : NodeId) (ns : NodeState Γ)
    (sched sched′ : Sched Γ) (st : EvalSt e) →
    B ≤ B′ →
    Sched.slots sched′ ≡ Sched.slots sched →
    boundedNode B′ ns ≡ true →
    fnCapNode Ψ ns ≡ true →
    INV? Ψ B sched st ≡ true →
    INV? Ψ B′ sched′ (installNode nid ns st) ≡ true


------------------------------------------------------------------
-- PER-EMIT WET PLUMBING, hop and dryness family — the hopDev?/dryEvent
-- halves of the splitEvents/retagEvents/map-value/terminator algebra
-- the push face's cons clause reassembles.  THE B-FAMILY ALREADY
-- EXISTED, PROVEN (.Measures W7 block: valB?/valsB?/eventB?/burstB?/
-- pathB?/frameB?-widen, splitEvents-vals-B/-bk-B, mapValue-B, and
-- finList-B in .Wet/Part2) — found by the clash, not the grep, which is
-- the wrong order; grep first.  Only the hop/dry twins below are new.
-- They live in THIS module rather than beside their family in
-- .Measures deliberately: a Measures edit invalidates every interface
-- above it (hours), a Walk-Level edit costs seconds.  When the
-- map/take/scan wet push faces need them, THAT is the day they move
-- down — not before.
------------------------------------------------------------------

-- any-p over ++ stays false when both halves are; hasDry-append's
-- event-level sibling
any-++-false : ∀ {A : Set} (p : A → Bool) (xs ys : List A) →
  any p xs ≡ false → any p ys ≡ false → any p (xs ++ ys) ≡ false
any-++-false p []       ys hx hy = hy
any-++-false p (x ∷ xs) ys hx hy with ∨-false (p x) (any p xs) hx
... | px , pxs = cong₂ _∨_ px (any-++-false p xs ys pxs hy)

-- and the hop tests weaken upward in the hop index, F fixed
hopDev?-widen : ∀ {n} {Γ : Ctx n} {u} (F r r′ : ℕ) (ev : InstEvent (Val Γ u)) →
  r ≤ r′ → hopDev? F r ev ≡ true → hopDev? F r′ ev ≡ true
hopDev?-widen {u = u} F r r′ (value v) le h = ≤ᵇ-widen (hopDᵛ F u v) le h
hopDev?-widen F r r′ (init _)    le h = refl
hopDev?-widen F r r′ (close _ _) le h = refl
hopDev?-widen F r r′ (handoff _) le h = refl
hopDev?-widen F r r′ complete    le h = refl

burstHopD?-widen : ∀ {n} {Γ : Ctx n} {u} (F r r′ : ℕ) (str : Stream Γ u) →
  r ≤ r′ → burstHopD? F r str ≡ true → burstHopD? F r′ str ≡ true
burstHopD?-widen F r r′ str le h =
  all-impl (λ em → all (hopDev? F r)  (InstEmit.events em))
           (λ em → all (hopDev? F r′) (InstEmit.events em))
           (λ em hem → all-impl (hopDev? F r) (hopDev? F r′)
                         (λ ev hev → hopDev?-widen F r r′ ev le hev)
                         (InstEmit.events em) hem)
           str h

splitEvents-vals-hop : ∀ {n} {Γ : Ctx n} {s u} (F r : ℕ)
  (es : List (InstEvent (Val Γ s))) →
  all (hopDev? F r) es ≡ true →
  all (λ v → hopDᵛ F s v ≤ᵇ r) (proj₁ (splitEvents {A = Val Γ u} es)) ≡ true
splitEvents-vals-hop F r [] h = refl
splitEvents-vals-hop {s = s} {u = u} F r (value v ∷ es) h
  with ∧-true (hopDᵛ F s v ≤ᵇ r) (all (hopDev? F r) es) h
... | hv , hes = ∧-intro hv (splitEvents-vals-hop {u = u} F r es hes)
splitEvents-vals-hop {u = u} F r (init _ ∷ es) h =
  splitEvents-vals-hop {u = u} F r es (proj₂ (∧-true _ _ h))
splitEvents-vals-hop {u = u} F r (close _ _ ∷ es) h =
  splitEvents-vals-hop {u = u} F r es (proj₂ (∧-true _ _ h))
splitEvents-vals-hop {u = u} F r (handoff _ ∷ es) h =
  splitEvents-vals-hop {u = u} F r es (proj₂ (∧-true _ _ h))
splitEvents-vals-hop {u = u} F r (complete ∷ es) h =
  splitEvents-vals-hop {u = u} F r es (proj₂ (∧-true _ _ h))

splitEvents-bk-hop : ∀ {n} {Γ : Ctx n} {s u} (F r : ℕ)
  (es : List (InstEvent (Val Γ s))) →
  all (hopDev? F r) (proj₁ (proj₂ (splitEvents {A = Val Γ u} es))) ≡ true
splitEvents-bk-hop F r []                    = refl
splitEvents-bk-hop {u = u} F r (value _   ∷ es) = splitEvents-bk-hop {u = u} F r es
splitEvents-bk-hop {u = u} F r (init _    ∷ es) = ∧-intro refl (splitEvents-bk-hop {u = u} F r es)
splitEvents-bk-hop {u = u} F r (close _ _ ∷ es) = ∧-intro refl (splitEvents-bk-hop {u = u} F r es)
splitEvents-bk-hop {u = u} F r (handoff _ ∷ es) = ∧-intro refl (splitEvents-bk-hop {u = u} F r es)
splitEvents-bk-hop {u = u} F r (complete  ∷ es) = splitEvents-bk-hop {u = u} F r es

-- dryness DOES cross the split (close events survive it), so this one
-- is conditional, and the `dried` reason is matched absurd
splitEvents-bk-dry : ∀ {n} {Γ : Ctx n} {s u}
  (es : List (InstEvent (Val Γ s))) →
  any dryEvent es ≡ false →
  any dryEvent (proj₁ (proj₂ (splitEvents {A = Val Γ u} es))) ≡ false
splitEvents-bk-dry []                          h = refl
splitEvents-bk-dry {u = u} (value _          ∷ es) h = splitEvents-bk-dry {u = u} es h
splitEvents-bk-dry {u = u} (init _           ∷ es) h = splitEvents-bk-dry {u = u} es h
splitEvents-bk-dry {u = u} (close _ cut        ∷ es) h = splitEvents-bk-dry {u = u} es h
splitEvents-bk-dry {u = u} (close _ cutPending ∷ es) h = splitEvents-bk-dry {u = u} es h
splitEvents-bk-dry {u = u} (close _ exhausted  ∷ es) h = splitEvents-bk-dry {u = u} es h
splitEvents-bk-dry {u = u} (close _ dried      ∷ es) ()
splitEvents-bk-dry {u = u} (handoff _        ∷ es) h = splitEvents-bk-dry {u = u} es h
splitEvents-bk-dry {u = u} (complete         ∷ es) h = splitEvents-bk-dry {u = u} es h

-- a retagged list is value-free, so the wet tests are unconditional —
-- retagEvents-caps' twins — while dryness again crosses
retagEvents-B : ∀ {n} {Γ : Ctx n} {u} {A : Set} (B Ψ : ℕ)
  (es : List (InstEvent A)) →
  all (eventB? {u = u} B Ψ) (retagEvents {A = A} {B = Val Γ u} es) ≡ true
retagEvents-B B Ψ []               = refl
retagEvents-B B Ψ (value _   ∷ es) = retagEvents-B B Ψ es
retagEvents-B B Ψ (init _    ∷ es) = ∧-intro refl (retagEvents-B B Ψ es)
retagEvents-B B Ψ (close _ _ ∷ es) = ∧-intro refl (retagEvents-B B Ψ es)
retagEvents-B B Ψ (handoff _ ∷ es) = ∧-intro refl (retagEvents-B B Ψ es)
retagEvents-B B Ψ (complete  ∷ es) = ∧-intro refl (retagEvents-B B Ψ es)

retagEvents-hop : ∀ {n} {Γ : Ctx n} {u} {A : Set} (F r : ℕ)
  (es : List (InstEvent A)) →
  all (hopDev? {u = u} F r) (retagEvents {A = A} {B = Val Γ u} es) ≡ true
retagEvents-hop F r []               = refl
retagEvents-hop F r (value _   ∷ es) = retagEvents-hop F r es
retagEvents-hop F r (init _    ∷ es) = ∧-intro refl (retagEvents-hop F r es)
retagEvents-hop F r (close _ _ ∷ es) = ∧-intro refl (retagEvents-hop F r es)
retagEvents-hop F r (handoff _ ∷ es) = ∧-intro refl (retagEvents-hop F r es)
retagEvents-hop F r (complete  ∷ es) = ∧-intro refl (retagEvents-hop F r es)

retagEvents-dry : ∀ {A B : Set} (es : List (InstEvent A)) →
  any dryEvent es ≡ false →
  any dryEvent (retagEvents {A = A} {B = B} es) ≡ false
retagEvents-dry []                          h = refl
retagEvents-dry (value _          ∷ es) h = retagEvents-dry es h
retagEvents-dry (init _           ∷ es) h = retagEvents-dry es h
retagEvents-dry (close _ cut        ∷ es) h = retagEvents-dry es h
retagEvents-dry (close _ cutPending ∷ es) h = retagEvents-dry es h
retagEvents-dry (close _ exhausted  ∷ es) h = retagEvents-dry es h
retagEvents-dry (close _ dried      ∷ es) ()
retagEvents-dry (handoff _        ∷ es) h = retagEvents-dry es h
retagEvents-dry (complete         ∷ es) h = retagEvents-dry es h

mapValue-hop : ∀ {n} {Γ : Ctx n} {u} (F r : ℕ) (vs : List (Val Γ u)) →
  all (λ v → hopDᵛ F u v ≤ᵇ r) vs ≡ true →
  all (hopDev? F r) (map value vs) ≡ true
mapValue-hop F r [] h = refl
mapValue-hop {u = u} F r (v ∷ vs) h
  with ∧-true (hopDᵛ F u v ≤ᵇ r) (all (λ w → hopDᵛ F u w ≤ᵇ r) vs) h
... | hv , hvs = ∧-intro hv (mapValue-hop F r vs hvs)

mapValue-dry : ∀ {n} {Γ : Ctx n} {u} (vs : List (Val Γ u)) →
  any dryEvent (map value vs) ≡ false
mapValue-dry []       = refl
mapValue-dry (v ∷ vs) = mapValue-dry vs

finList-hop : ∀ {n} {Γ : Ctx n} {u} (F r : ℕ) (b : Bool) →
  all (hopDev? {n = n} {Γ = Γ} {u = u} F r)
      (if b then complete ∷ [] else []) ≡ true
finList-hop F r true  = refl
finList-hop F r false = refl

finList-dry : ∀ {A : Set} (b : Bool) →
  any (dryEvent {A = A}) (if b then complete ∷ [] else []) ≡ false
finList-dry true  = refl
finList-dry false = refl

------------------------------------------------------------------
-- THE HOP-EDGE CHAIN, LEAF FIRST — subscribeInner-walk, its one-frame
-- consumer stepThru-walk, and the REAL push face over them.  Each is
-- its caps twin ⊗ the wet content on one witness, the discipline the
-- whole module runs on.
--
-- ⚠ DEAD ROUTE 2026-08-13, and it shaped this whole section: A
-- FRAME-GENERIC WET PUSH FACE IS FALSE.  The first statement of this
-- face (one postulate `pushBurst-walk`, generic in `f : Frame Γ s u`,
-- committed 9fb13d3) carried a uniform hop conjunct — input receipts
-- at r̂, output at suc r̂ — and that is REFUTABLE BY CONSTRUCTION at
-- f := map-f: a step function that wraps its input two mergeAll levels
-- deep sends a value of hop exactly r̂ to hop r̂ + 2 > suc r̂, with every
-- hypothesis satisfiable (frameB? bounds the fn's SIZE and WEIGHT,
-- never its hop growth).  The caps face is frame-generic because caps
-- measures are; THE HOP LEDGER IS FRAME-SPECIFIC.  pushBurst has four
-- call sites (thru-outer, map-f, take-f, scan-f — Rx.Evaluator), so
-- the repair is one wet push face PER FRAME KIND, this one thru-outer's;
-- the chain frames' faces are authored when walk-map/take/scan are
-- ground, funded by hopD-map-emit at their own output indices.
------------------------------------------------------------------

-- THE LEAF — the wet face of subscribeInner, WHERE THE GAS PEEL IS.
-- subscribeInner-caps' hypothesis list and Σ verbatim (.Subscribe-Face,
-- PROVEN both clauses, including the strict sLvlD report), ⊗ the wet
-- content.  Σ-content: the strict level bound is the one downward
-- conjunct; the hop/dry/regsLen? conjuncts are j′-free.
--
-- WHAT IS NAILED DOWN BY THE STATEMENT ALONE: subscribeInner's g0 arm
-- is the evaluator's ONE remaining dry mint under this face
-- (`close drySource dried`, Rx.Evaluator) — and the gas hypothesis
-- `g hasAtLeast suc G` HAS NO CONSTRUCTOR AT g0, so the mint is
-- unreachable by type, exactly as the μ mint is at walkFace's absurd
-- clause.  Both of the machine's dry mints are now excluded by the
-- same one-line shape; what remains everywhere else is PRESERVATION.
--
-- THE gs ROUTE (for the eventual body): hasAtLeast-peel the gas;
-- walkFace o (the mutual walk at the inner — legitimate because the
-- peel descends the gas, the same induction subscribeE-caps'
-- subscribeInner clause runs) at level suc j under
-- κ′ = from-inner op allNid inst ↠ κ; the walk's burst conjuncts feed
-- the vs/bs receipts through the splitBurst square (the caps twins of
-- those two splits are proven in .Subscribe-Face; the dry one is
-- splitBurst-nodry, .Burst-Walk).  The demand: hop-step-gives at the
-- descended index — hopDᵛ F o ≤ r̂ (hypothesis) and dBound monotone in
-- r — funds the inner walk's demand STRICTLY below suc r̂'s.
--
-- THE LIVE EDGE IS CLOSED AT THE STATEMENT (2026-08-13, the
-- reset-anchor pins): the face used to quantify Ŝ freely with NO
-- hypothesis linking the level cap to it, which made the demand
-- funding unprovable and possibly false — hop-step-gives' premise
-- needs suc (syncSizeᵉ o) ≤ ŝ + suc Ŝ, the receipts bound syncSizeᵉ o
-- only by the LEVEL cap (valB?'s size half + reach-reset, .Measures),
-- and hop-step-needs (machine-checked, .Wet/Part6) proves the link is
-- NECESSARY for any r-drop funding, so no cleverer proof could have
-- avoided it.  The repair is the threaded ceiling the old header
-- predicted: `2 ≤ Ŝ`, `F ≡ Ŝ`, `R̂ ≡ hopR Ŝ`, and
-- `cSize (frameStep L̂ c) ≤ Ŝ` at the face's own budget — refl/lemma
-- at the true instantiation (entry-ceiling; GAP 2's ruling and
-- caps-tick supply it), converted between faces by the Caps-Chain
-- descents.  With the link in the telescope the gs body's funding is
-- hop-edge (proven) at the receipt-derived size bound; what remains is
-- assembly against the caps twin, not a coincidence bet.
-- (Demand-Probe series Q probed the OLD unlinked statement: the safe
-- region green, the crossing region multi-hour; a crossing-region
-- refutation would confirm the pin was needed, and its green would
-- not have certified the unlinked face.  Burst-Walk's SiNodry states
-- the DELIVERY-side leaf, hasDry only, PROVEN there by consuming the
-- finished walk face; this statement is the SUBSCRIBE-side leaf the
-- walk face itself consumes.  Same evaluator function, opposite
-- direction of dependency.)
--
-- PAYABILITY (census 2026-08-13): the ceiling conversion the gs body
-- owes the inner walkFace call — its own `sLvlD S W dep (suc bud)
-- (suc j) ≤ L̂` into the inner's `opIterD … (suc j) ≤ L̂` — is
-- DEFINITIONAL.  sLvlD-suc (Rx.Evaluator, refl):
--   sLvlD S W d (suc k) J ≡ opIterD S W d k (suc (sizeAt S J)) J
-- so the leaf's budget IS the inner sweep's budget at ops :=
-- suc (sizeAt S (suc j)); and `Caps.cSize (frameStep j c)` UNFOLDS to
-- `sizeAt (Caps.cSize c) j` (both are iterSize S j S), so the inner's
-- actual ops `suc (sizeᵉ o)` sits under the pinned one by szb +
-- sizeAt-mono (.Caps, proven) over j ≤ suc j.  The tower was built
-- for this edge; nothing new is owed here.
SubscribeInnerWalk : Set
SubscribeInnerWalk = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j : ℕ)
  (g : Gas) (op : AllOp) (allNid : NodeId)
  (κ : Path Γ u t) (bid : Id) (now : Tick) (o : Val Γ (obs u))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  valCaps? (frameStep j c) sl (obs u) o ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  nest o sl (EvalSt.connectedShares st) ≤ bud →
  depthInner g op allNid κ bid now o sched st ≤ dep →
  -- the wet half at the level
  INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
  valB? (Caps.cSize (frameStep j c)) Ψ (obs u) o ≡ true →
  pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
  hopDᵛ F (obs u) o ≤ r̂ →
  -- the reset-anchor pins, at this face's own budget.  THE LIVE EDGE
  -- CLOSES HERE: the ceiling converts o's valB?/valCaps? size receipt
  -- (at cSize (frameStep j c), j under the budget under L̂) into
  -- hop-edge's `sizeᵛ o ≤ Ŝ` premise, which is the exact syncSize
  -- headroom hop-step-needs proves the gas peel REQUIRES.
  2 ≤ Ŝ →
  F ≡ Ŝ →
  R̂ ≡ hopR Ŝ →
  Caps.cSize (frameStep L̂ c) ≤ Ŝ →
  sLvlD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (suc j) ≤ L̂ →
  -- the dry half
  unconn sl (EvalSt.connectedShares st) ≤ U →
  dBound Ŝ R̂ U (suc r̂) ŝ ≤ G →
  g hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = subscribeInner g op allNid κ bid now o sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
              (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ (proj₂ r)) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ (proj₂ r))) ≡ true)
     × (suc (j + j′) ≤ sLvlD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (suc j))
     × (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
             (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
             (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
     × (all (valB? (Caps.cSize (frameStep (j + j′) c)) Ψ u)
            (proj₁ (proj₂ r)) ≡ true)
     × (all (λ v → hopDᵛ F u v ≤ᵇ r̂) (proj₁ (proj₂ r)) ≡ true)
     × (any dryEvent (proj₁ (proj₂ (proj₂ r))) ≡ false)
     × (regsLen? ℓ (EvalSt.registry
          (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r)))))) ≡ true)

-- ONE thru-outer FRAME — stepFrame-caps' Σ at f := thru-outer op nid
-- (its frameSz? hypothesis is definitionally true there and is
-- dropped), ⊗ the wet content.  The vs it emits are inner-burst values,
-- so their hop receipts stay AT r̂ — no growth through this frame; the
-- push face widens once at its consumer.
StepThruWalk : Set
StepThruWalk = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j : ℕ)
  (g : Gas) (bid : Id) (now : Tick) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (vals : List (Val Γ (obs u))) (fin : Bool)
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  valsCaps? (frameStep j c) sl vals ≡ true →
  frameBud c j ≤ bud →
  depthFrame g bid now (thru-outer op nid) κ vals fin sched st ≤ dep →
  -- the wet half at the level
  INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
  pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
  all (valB? (Caps.cSize (frameStep j c)) Ψ (obs u)) vals ≡ true →
  all (λ o → hopDᵛ F (obs u) o ≤ᵇ r̂) vals ≡ true →
  -- the reset-anchor pins, at this face's own budget (the -core owes
  -- each loop element the leaf's sLvlD form, a frame-step descent)
  2 ≤ Ŝ →
  F ≡ Ŝ →
  R̂ ≡ hopR Ŝ →
  Caps.cSize (frameStep L̂ c) ≤ Ŝ →
  fLvlD (Caps.cSize c) (Caps.cWid c) dep j ≤ L̂ →
  -- the dry half
  unconn sl (EvalSt.connectedShares st) ≤ U →
  dBound Ŝ R̂ U (suc r̂) ŝ ≤ G →
  g hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = stepFrame g bid now (thru-outer op nid) κ vals fin sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ r))))
              (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl) (proj₁ (proj₂ r)) ≡ true)
     × (j + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)
     × (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
             (proj₁ (proj₂ (proj₂ (proj₂ r))))
             (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (valB? (Caps.cSize (frameStep (j + j′) c)) Ψ u) (proj₁ r) ≡ true)
     × (all (λ v → hopDᵛ F u v ≤ᵇ r̂) (proj₁ r) ≡ true)
     × (any dryEvent (proj₁ (proj₂ r)) ≡ false)
     × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)

postulate
  subscribeInner-walk : SubscribeInnerWalk
  -- the -core carries the LOOP: thruWalk folds subscribeInner over the
  -- value list (thruWalk-caps/thruWrap-caps are its proven caps twins,
  -- .Subscribe-Face), re-establishing the state-dependent hypotheses
  -- after each element — the same loop shape innerReact-nodry-core's
  -- ruling names (.Burst-Walk) — and funds each element's nest premise
  -- from frameBud, per the caps route (valsCaps→mList-strict).  concatᵒ
  -- additionally queues instead of subscribing; its drain is
  -- innerFinish's job, not this face's.
  --
  -- PAYABILITY (census 2026-08-13): the ceiling conversion this core
  -- owes the leaf per element — its own `fLvlD S W dep j ≤ L̂` into the
  -- leaf's `sLvlD S W dep′ (suc bud′) (suc jᵢ) ≤ L̂` — is PAYABLE from
  -- the existing kit, no new mathematics.  The chain: per element,
  -- `sLvlD S W d k (suc jᵢ) ≤ sIterD S W d k (suc m) jᵢ` is the same
  -- two-line -suc/-infl shape as frame-desc/tail-desc (.Caps-Chain);
  -- prefix positions compose by sIterD-mono (walk-step's spine); and
  -- `fLvlD S W (suc d) j ≡ sIterD S W d (suc (sizeAt S (suc j)))
  -- (suc (widAt S W j)) (fLvl S W j)` (fLvlD-suc, an EQUALITY) lands
  -- it, with the loop's k/m under the pinned ones from its own
  -- count/nest receipts.  THE DEPTH DECREMENTS AT THE FRAME (payload
  -- priced at d from a frame at suc d — fLvlD-0 has no payload budget
  -- at all), so this core hands the leaf the PREDECESSOR depth,
  -- exactly as its proven caps twin already does.
  stepThru-walk-core : SubscribeInnerWalk → StepThruWalk

-- wired per the law: the leaf is consumed the day it is stated
stepThru-walk : StepThruWalk
stepThru-walk = stepThru-walk-core subscribeInner-walk

-- THE PUSH FACE AT thru-outer, REAL — pushBurst-caps' proven proof
-- (.Subscribe-Face) step for step, wet conjuncts threaded through:
-- per emit, split the events, step the values through the one frame
-- (stepThru-walk), recurse on the tail from the stepped state, and
-- reassemble the envelope with the per-segment plumbing above.  The
-- input hop receipts arrive at r̂ and LEAVE at r̂ — the thru frame does
-- not grow hops — so the composite's suc is paid by the consumer's one
-- widening, never here.
pushThru-walk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j : ℕ)
  (g : Gas) (bid : Id) (now : Tick) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (str : Stream Γ (obs u))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  burstCaps? (frameStep j c) sl str ≡ true →
  burstCount? (frameStep j c) str ≡ true →
  depthBurst g bid now (thru-outer op nid) κ str sched st ≤ dep →
  -- the wet half at the level
  INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
  pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
  burstB? (Caps.cSize (frameStep j c)) Ψ str ≡ true →
  burstHopD? F r̂ str ≡ true →
  hasDry str ≡ false →
  -- the reset-anchor pins, at this face's own budget
  2 ≤ Ŝ →
  F ≡ Ŝ →
  R̂ ≡ hopR Ŝ →
  Caps.cSize (frameStep L̂ c) ≤ Ŝ →
  fIterD (Caps.cSize c) (Caps.cWid c) dep bud (length str) j ≤ L̂ →
  -- the dry half
  unconn sl (EvalSt.connectedShares st) ≤ U →
  dBound Ŝ R̂ U (suc r̂) ŝ ≤ G →
  g hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = pushBurst g bid now (thru-outer op nid) κ str sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
     × (j + j′ ≤ fIterD (Caps.cSize c) (Caps.cWid c) dep bud (length str) j)
     × (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
             (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
     × (burstHopD? F r̂ (proj₁ r) ≡ true)
     × (hasDry (proj₁ r) ≡ false)
     × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
pushThru-walk c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j g bid now op nid κ [] sl sched st
  2≤S 1≤R slEq slC slSz inv pS lC bC cC dpt invW pB bB bH hDry s2 fS rS ceil lb hU dmd gas lℓ rgs =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , refl
    , refl
    , burst-nil (Caps.cSize c) (Caps.cWid c) dep bud j
    , subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st ≡ true)
            (sym (+-identityʳ j)) invW
    , refl
    , refl
    , refl
    , rgs
pushThru-walk {n = n} {Γ = Γ} {t = t} {u = u} c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j g bid now op nid κ (em ∷ ems) sl sched st
  2≤S 1≤R slEq slC slSz inv pS lC bC cC dpt invW pB bB bH hDry s2 fS rS ceil lb hU dmd gas lℓ rgs =
  j₁ + j₂
    , subst (λ x → capsOK? (frameStep x c)
                     (proj₁ (proj₂ REST)) (proj₂ (proj₂ REST)) ≡ true) EQA W1
    , subst (λ x → burstCaps? (frameStep x c) sl OUT ≡ true) EQA
            (∧-intro EMIT W2)
    , subst (λ x → burstCount? (frameStep x c) OUT ≡ true) EQA COUNT
    , burst-step (Caps.cSize c) (Caps.cWid c) dep bud (length ems) j j₁ j₂ 2≤S
        S4 W4
    , subst (λ x → INV? Ψ (Caps.cSize (frameStep x c))
                     (proj₁ (proj₂ REST)) (proj₂ (proj₂ REST)) ≡ true) EQA W5
    , subst (λ x → burstB? (Caps.cSize (frameStep x c)) Ψ OUT ≡ true) EQA
            (∧-intro EMITB W6)
    , ∧-intro EMITH W7
    , cong₂ _∨_ EMITD W8
    , W9
  where
  E    = InstEmit.events em
  sp   = splitEvents {A = Val Γ u} E
  step = stepFrame g bid now (thru-outer op nid) κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  sd₁  = proj₁ (proj₂ (proj₂ (proj₂ step)))
  st₁  = proj₂ (proj₂ (proj₂ (proj₂ step)))
  -- caps receipts for this emit, verbatim from the caps proof
  eC   = proj₁ (∧-true _ _ bC)
  cntW = suc (Caps.cWid (frameStep j c))
  cntP : InstEmit (Val Γ (obs u)) → Bool
  cntP em′ = valCountᵉ (InstEmit.events em′) ≤ᵇ cntW
  cCv  = proj₂ (∧-true (length (em ∷ ems) ≤ᵇ cntW) (all cntP (em ∷ ems)) cC)
  cntE = ≤ᵇ⇒≤ (valCountᵉ E) cntW
           (T-to (proj₁ (∧-true (cntP em) (all cntP ems) cCv)))
  -- wet receipts for this emit
  eB   = proj₁ (∧-true _ _ bB)
  eH   = proj₁ (∧-true _ _ bH)
  dSp  = ∨-false (any dryEvent E) (hasDry ems) hDry
  SF   = stepThru-walk c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep (frameBud c j) j g bid now op nid κ
           (proj₁ sp) (proj₂ (proj₂ sp)) sl sched st
           2≤S 1≤R slEq slC slSz inv pS lC
           (splitEvents-valsCaps {u = u} (frameStep j c) sl E eC cntE)
           ≤-refl
           -- both ⊔ arguments spelled out: _⊔_ matches on BOTH sides,
           -- so the tail as a meta is a stuck constraint, not a hole
           -- the unifier can fill
           (≤-trans (m≤m⊔n
              (depthFrame g bid now (thru-outer op nid) κ
                 (proj₁ sp) (proj₂ (proj₂ sp)) sched st)
              (depthBurst g bid now (thru-outer op nid) κ ems sd₁ st₁)) dpt)
           invW pB
           (splitEvents-vals-B {u = u} (Caps.cSize (frameStep j c)) Ψ E eB)
           (splitEvents-vals-hop {u = u} F r̂ E eH)
           s2 fS rS ceil
           (≤-trans (frame-desc (Caps.cSize c) (Caps.cWid c) dep bud (length ems) j) lb)
           hU dmd gas lℓ rgs
  j₁   = proj₁ SF
  S1   = proj₁ (proj₂ SF)
  S2   = proj₁ (proj₂ (proj₂ SF))
  S3   = proj₁ (proj₂ (proj₂ (proj₂ SF)))
  S4   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SF))))
  S5   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SF)))))
  S6   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SF))))))
  S7   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SF)))))))
  S8   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SF))))))))
  S9   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SF))))))))
  ⊑₁   = frameStep-⊑-+ c 2≤S j j₁
  KS   = stepFrame-keeps g bid now (thru-outer op nid) κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  sl₁eq : Sched.slots sd₁ ≡ sl
  sl₁eq = trans (KeepsC.slotsEq KS) slEq
  UK₁ : unconn sl (EvalSt.connectedShares st₁) ≤ U
  UK₁ = ≤-trans
          (subst₂ (λ y z → unconn y (EvalSt.connectedShares st₁)
                             ≤ unconn z (EvalSt.connectedShares st))
                  sl₁eq slEq
                  (unconn-keeps sched st sd₁ st₁ KS))
          hU
  IH   = pushThru-walk c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud (j + j₁) g bid now op nid κ ems sl sd₁ st₁
           2≤S 1≤R sl₁eq slC slSz
           S1
           (pathSz?-⊑ κ ⊑₁ pS)
           (≤-trans lC (proj₁ ⊑₁))
           (burstCaps?-widen sl ems ⊑₁ (proj₂ (∧-true _ _ bC)))
           (burstCount?-widen ems ⊑₁ (burstCount?-tail (frameStep j c) em ems cC))
           (≤-trans (m≤n⊔m _ _) dpt)
           S5
           (pathB?-widen κ (proj₁ ⊑₁) pB)
           (burstB?-widen ems (proj₁ ⊑₁) (proj₂ (∧-true _ _ bB)))
           (proj₂ (∧-true _ _ bH))
           (proj₂ dSp)
           s2 fS rS ceil
           (≤-trans (tail-desc (Caps.cSize c) (Caps.cWid c) dep bud (length ems) j j₁
                       2≤S S4)
                    lb)
           UK₁ dmd gas lℓ
           S9
  j₂   = proj₁ IH
  W1   = proj₁ (proj₂ IH)
  W2   = proj₁ (proj₂ (proj₂ IH))
  W3   = proj₁ (proj₂ (proj₂ (proj₂ IH)))
  W4   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))
  W5   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
  W6   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))
  W7   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))))
  W8   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))))
  W9   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))))
  REST = pushBurst g bid now (thru-outer op nid) κ ems sd₁ st₁
  OUT  = ((proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
             ++ map value (proj₁ step)
             ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
           at InstEmit.instant em from InstEmit.source em as InstEmit.kind em)
          ∷ proj₁ REST
  EQA : (j + j₁) + j₂ ≡ j + (j₁ + j₂)
  EQA = +-assoc j j₁ j₂
  ⊑₂  = frameStep-⊑-+ c 2≤S (j + j₁) j₂
  ⊑ⱼ  = frameStep-mono-j c 2≤S (≤-trans (m≤m+n j j₁) (m≤m+n (j + j₁) j₂))
  B″  = Caps.cSize (frameStep ((j + j₁) + j₂) c)
  EMIT : all (eventCaps? (frameStep ((j + j₁) + j₂) c) sl)
             (proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
                ++ map value (proj₁ step)
                ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
           ≡ true
  EMIT = all-++-intro (eventCaps? (frameStep ((j + j₁) + j₂) c) sl)
           (proj₁ (proj₂ sp)) _
           (splitEvents-bk-caps {u = u} (frameStep ((j + j₁) + j₂) c) sl E)
           (all-++-intro (eventCaps? (frameStep ((j + j₁) + j₂) c) sl)
              (retagEvents (proj₁ (proj₂ step))) _
              (retagEvents-caps {u = u} (frameStep ((j + j₁) + j₂) c) sl
                 (proj₁ (proj₂ step)))
              (all-++-intro (eventCaps? (frameStep ((j + j₁) + j₂) c) sl)
                 (map value (proj₁ step)) _
                 (mapValue-caps (frameStep ((j + j₁) + j₂) c) sl u (proj₁ step)
                    (valsCaps?-widen sl u (proj₁ step) ⊑₂
                       (valsOf (frameStep (j + j₁) c) sl (proj₁ step) S2)))
                 (finList-caps (frameStep ((j + j₁) + j₂) c) sl
                    (proj₁ (proj₂ (proj₂ step))))))
  EMITB : all (eventB? B″ Ψ)
              (proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
                 ++ map value (proj₁ step)
                 ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
            ≡ true
  EMITB = all-++-intro (eventB? B″ Ψ) (proj₁ (proj₂ sp)) _
            (splitEvents-bk-B {u = u} B″ Ψ E)
            (all-++-intro (eventB? B″ Ψ) (retagEvents (proj₁ (proj₂ step))) _
               (retagEvents-B B″ Ψ (proj₁ (proj₂ step)))
               (all-++-intro (eventB? B″ Ψ) (map value (proj₁ step)) _
                  (mapValue-B B″ Ψ u (proj₁ step)
                     (valsB?-widen u (proj₁ step) (proj₁ ⊑₂) S6))
                  (finList-B {u = u} B″ Ψ (proj₁ (proj₂ (proj₂ step))))))
  EMITH : all (hopDev? F r̂)
              (proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
                 ++ map value (proj₁ step)
                 ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
            ≡ true
  EMITH = all-++-intro (hopDev? F r̂) (proj₁ (proj₂ sp)) _
            (splitEvents-bk-hop {u = u} F r̂ E)
            (all-++-intro (hopDev? F r̂) (retagEvents (proj₁ (proj₂ step))) _
               (retagEvents-hop F r̂ (proj₁ (proj₂ step)))
               (all-++-intro (hopDev? F r̂) (map value (proj₁ step)) _
                  (mapValue-hop F r̂ (proj₁ step) S7)
                  (finList-hop {n = n} {Γ = Γ} {u = u} F r̂
                     (proj₁ (proj₂ (proj₂ step))))))
  EMITD : any dryEvent
              (proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
                 ++ map value (proj₁ step)
                 ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
            ≡ false
  EMITD = any-++-false dryEvent (proj₁ (proj₂ sp)) _
            (splitEvents-bk-dry {u = u} E (proj₁ dSp))
            (any-++-false dryEvent (retagEvents (proj₁ (proj₂ step))) _
               (retagEvents-dry (proj₁ (proj₂ step)) S8)
               (any-++-false dryEvent (map value (proj₁ step)) _
                  (mapValue-dry (proj₁ step))
                  (finList-dry {A = Val Γ u} (proj₁ (proj₂ (proj₂ step))))))
  HEADV : valCountᵉ (proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
                       ++ map value (proj₁ step)
                       ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
            ≡ length (proj₁ step)
  HEADV = pushEmit-count {Γ = Γ} {s = obs u} {u = u} {A = Val Γ t}
            E (proj₁ (proj₂ step)) (proj₁ step) (proj₁ (proj₂ (proj₂ step)))
  HEADB : (valCountᵉ (proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
                        ++ map value (proj₁ step)
                        ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
             ≤ᵇ suc (Caps.cWid (frameStep ((j + j₁) + j₂) c))) ≡ true
  HEADB = subst (λ x → (x ≤ᵇ suc (Caps.cWid (frameStep ((j + j₁) + j₂) c))) ≡ true)
                (sym HEADV)
                (≤ᵇ-widen (length (proj₁ step)) (s≤s (proj₁ (proj₂ ⊑₂)))
                   (proj₂ (∧-true
                     (all (valCaps? (frameStep (j + j₁) c) sl u) (proj₁ step))
                     (length (proj₁ step)
                        ≤ᵇ suc (Caps.cWid (frameStep (j + j₁) c)))
                     S2)))
  LEN : length OUT ≤ suc (Caps.cWid (frameStep ((j + j₁) + j₂) c))
  LEN = subst (λ x → suc x ≤ suc (Caps.cWid (frameStep ((j + j₁) + j₂) c)))
              (sym (pushBurst-len g bid now (thru-outer op nid) κ ems sd₁ st₁))
              (≤-trans (countLen (frameStep j c) (em ∷ ems) cC)
                       (s≤s (proj₁ (proj₂ ⊑ⱼ))))
  COUNT : burstCount? (frameStep ((j + j₁) + j₂) c) OUT ≡ true
  COUNT = countIn (frameStep ((j + j₁) + j₂) c) OUT LEN
            (∧-intro HEADB
               (countVals (frameStep ((j + j₁) + j₂) c) (proj₁ REST) W3))

-- THE *All DELEGATE — subscribeAll-caps ⊗ the wet content, one Σ,
-- exactly as WalkStmt is subscribeE-caps ⊗ the same content, and REAL:
-- the body (below walkFace — the two are mutual, the recursion
-- decreasing at walkFace (opᵉ b) → … → walkFace b) mirrors
-- subscribeAll-caps' proven proof step for step.  mint → install
-- (capsOK?-setNode / INV?-install) → the recursive walk on b at
-- κ′ = thru-outer op nid ↠ κ, funded by hop-step-gives (the composite
-- demand at suc/suc measures yields the source's demand STRICTLY
-- smaller, the spent unit paying the ℓ extension exactly — the unit
-- subscribeE-inner-nodry-pLen lacks) → pushThru-walk over the
-- returned burst (REAL, above — its hop receipts return AT hopDᵉ F b,
-- and the composite conjunct's suc is one widening here) → op-step for
-- the level charge.  The residue is the hop-edge chain's two
-- postulates: stepThru-walk-core and subscribeInner-walk, above.
--
-- The hypothesis list is subscribeAll-caps' own, verbatim and in its
-- order, then the wet half with the composite's measures in REDUCED
-- form — suc (hopDᵉ F b), suc (syncSizeᵉ b), fnCapᵉ b,
-- suc (suc (sizeᵉ b)) — because every *All constructor computes to
-- exactly those, so the four heads pass their hypotheses through
-- untouched (the caps precedent: "inherits their index and their
-- hypothesis verbatim").
--
-- ONE wet hypothesis is new, fnCapNode Ψ ns: INV?'s fnCapBounded?
-- conjunct reads EvalSt.nodes, which installNode extends, so the Ψ
-- half of the install must be funded.  (The SIZE half rides the caps
-- boundedNode hypothesis already in the list — stBounded? reads the
-- same node list.)  All four heads supply it by refl: merge-st /
-- switch-st / exhaust-st are `true` outright, concat-st [] is
-- `all _ []`.
subscribeAll-walk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ)
  (g : Gas) (op : AllOp) (ns : NodeState Γ)
  (b : Closed Γ (obs u)) (κ : Path Γ u t)
  (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  boundedNode (Caps.cSize (frameStep (suc j) c)) ns ≡ true →
  widNode (Caps.cWid (frameStep (suc j) c)) sl ns ≡ true →
  sizeᵉ b ≤ Caps.cSize (frameStep j c) →
  dWᵉ n sl b ≤ Caps.cWid (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  nest b sl (EvalSt.connectedShares st) ≤ bud →
  suc (suc (sizeᵉ b)) ≤ ops →
  depthAll g op ns b κ bid now sched st ≤ dep →
  -- the wet half, WalkStmt's own
  INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
  fnCapᵉ b ≤ Ψ →
  fnCapNode Ψ ns ≡ true →
  pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
  -- the reset-anchor pins, WalkStmt's own (the budget is the same
  -- opIterD, so the heads pass all five through verbatim)
  2 ≤ Ŝ →
  F ≡ Ŝ →
  R̂ ≡ hopR Ŝ →
  Caps.cSize (frameStep L̂ c) ≤ Ŝ →
  opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j ≤ L̂ →
  -- the dry half, at the composite's own measures (each *All
  -- constructor computes to exactly this suc/suc form)
  dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
         (suc (hopDᵉ F b)) (suc (syncSizeᵉ b)) ≤ G →
  g hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = subscribeAll g op ns b κ bid now sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
     × (j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j)
     × (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
             (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
     × (burstHopD? F (suc (hopDᵉ F b)) (proj₁ r) ≡ true)
     × (hasDry (proj₁ r) ≡ false)
     × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)

-- THE FOUR *All HEADS, REAL: each delegates its whole body to
-- subscribeAll-walk, exactly as subscribeE-caps' four heads delegate
-- to subscribeAll-caps — the node bounds (caps AND wet) are refl at
-- every initial state, the size hypothesis sheds the constructor's
-- suc, the nest hypothesis steps by the Caps-Nest lemma, and every
-- other hypothesis passes through untouched because the *All measures
-- compute (sizeᵉ/hopDᵉ/syncSizeᵉ to suc, fnCapᵉ/dWᵉ to themselves,
-- depthE to depthAll at this op and state).
walk-mergeAll : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (b : Closed Γ (obs u)) → WalkStmt {e = e} (mergeAllᵉ b)
walk-mergeAll b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
  2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB s2 fS rS ceil lb dmd gas lℓ rgs =
  subscribeAll-walk c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g mergeᵒ (merge-st 0 false)
    b κ bid now sl sched st
    2≤S 1≤R slEq slC slSz inv refl refl
    (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC
    (merge-step _ sl _ bud nst) hidx dpt
    invW fnC refl pB s2 fS rS ceil lb dmd gas lℓ rgs

walk-concatAll : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (b : Closed Γ (obs u)) → WalkStmt {e = e} (concatAllᵉ b)
walk-concatAll {u = u} b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
  2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB s2 fS rS ceil lb dmd gas lℓ rgs =
  subscribeAll-walk c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g concatᵒ
    (concat-st {t = u} [] false false) b κ bid now sl sched st
    2≤S 1≤R slEq slC slSz inv refl refl
    (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC
    (concat-step _ sl _ bud nst) hidx dpt
    invW fnC refl pB s2 fS rS ceil lb dmd gas lℓ rgs

walk-switchAll : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (b : Closed Γ (obs u)) → WalkStmt {e = e} (switchAllᵉ b)
walk-switchAll b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
  2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB s2 fS rS ceil lb dmd gas lℓ rgs =
  subscribeAll-walk c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g switchᵒ
    (switch-st nothing false) b κ bid now sl sched st
    2≤S 1≤R slEq slC slSz inv refl refl
    (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC
    (switch-step _ sl _ bud nst) hidx dpt
    invW fnC refl pB s2 fS rS ceil lb dmd gas lℓ rgs

walk-exhaustAll : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (b : Closed Γ (obs u)) → WalkStmt {e = e} (exhaustAllᵉ b)
walk-exhaustAll b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
  2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB s2 fS rS ceil lb dmd gas lℓ rgs =
  subscribeAll-walk c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g exhaustᵒ
    (exhaust-st false false) b κ bid now sl sched st
    2≤S 1≤R slEq slC slSz inv refl refl
    (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC
    (exhaust-step _ sl _ bud nst) hidx dpt
    invW fnC refl pB s2 fS rS ceil lb dmd gas lℓ rgs

-- THE DISPATCH, real from day one: match the subscribed expression,
-- hand the clause its own obligation.  Two clauses are PROVEN outright:
-- varᵉ (a closed term has no value variables) and μᵉ at g0 — the μ dry
-- mint, subscribeE's ONLY dry emit, is unreachable because
-- `g0 hasAtLeast suc G` has no constructor.  So `hasDry ≡ false` needs
-- no postulate at the one clause of subscribeE that emits dryness:
-- what remains is showing the recursive clauses PRESERVE it.
walkFace : WalkLevel
walkFace (input i)       = walk-input i
walkFace (ofᵉ ts)        = walk-of ts
walkFace emptyᵉ          = walk-empty
walkFace (mapᵉ f b)      = walk-map f b
walkFace (takeᵉ cnt b)   = walk-take cnt b
walkFace (scanᵉ f z b)   = walk-scan f z b
walkFace (mergeAllᵉ b)   = walk-mergeAll b
walkFace (concatAllᵉ b)  = walk-concatAll b
walkFace (switchAllᵉ b)  = walk-switchAll b
walkFace (exhaustAllᵉ b) = walk-exhaustAll b
walkFace (μᵉ body) c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g0 κ bid now sl sched st
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ()
walkFace (μᵉ body) c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j (gs fuel) κ bid now sl sched st =
  walk-mu body c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j (gs fuel) κ bid now sl sched st
walkFace (varᵉ ())
walkFace (deferᵉ body)   = walk-defer body

-- THE *All BODY — subscribeAll-caps' proven proof, step for step, with
-- the wet conjuncts threaded through.  ops splits exactly as there: at
-- zero the index hypothesis `suc (suc (sizeᵉ b)) ≤ zero` is uninhabited,
-- and the successor clause spends op-step's one operator.
subscribeAll-walk c Ψ F Ŝ R̂ G ℓ L̂ dep bud zero j g op ns b κ bid now sl sched st
  2≤S 1≤R slEq slC slSz inv bn wn szb wdb pC lC nst ()
subscribeAll-walk c Ψ F Ŝ R̂ G ℓ L̂ dep bud (suc ops′) j g op ns b κ bid now sl sched st
  2≤S 1≤R slEq slC slSz inv bn wn szb wdb pC lC nst hidx dpt invW fnC fnN pB s2 fS rS ceil lb dmd gas lℓ rgs =
  suc (j₁ + j₂)
    , subst (λ x → capsOK? (frameStep x c)
                     (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) ≡ true) EQ W1
    , subst (λ x → burstCaps? (frameStep x c) sl (proj₁ PB) ≡ true) EQ W2
    , subst (λ x → burstCount? (frameStep x c) (proj₁ PB) ≡ true) EQ W3
    -- ONE OPERATOR, spent exactly as the caps head spends it: the
    -- source's conjunct at the predecessor index, and the push face's
    -- fIterD charge converted once by burst-index
    , op-step (Caps.cSize c) (Caps.cWid c) dep bud ops′ j j₁ j₂ 2≤S S4
        (≤-trans W4 (burst-index (Caps.cSize c) (Caps.cWid c) dep bud
           (length (proj₁ res)) (suc j + j₁) (suc j + j₁) 2≤S
           (countLen (frameStep (suc j + j₁) c) (proj₁ res) S3)))
    , subst (λ x → INV? Ψ (Caps.cSize (frameStep x c))
                     (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) ≡ true) EQ W5
    , subst (λ x → burstB? (Caps.cSize (frameStep x c)) Ψ (proj₁ PB) ≡ true) EQ W6
    -- the push face reports hop receipts AT hopDᵉ F b (the thru frame
    -- does not grow hops); the composite conjunct's suc is one widening
    , burstHopD?-widen F (hopDᵉ F b) (suc (hopDᵉ F b)) (proj₁ PB)
        (n≤1+n (hopDᵉ F b)) W7
    , W8 , W9
  where
  nid    = Sched.nextNode sched
  sched₀ = record sched { nextNode = suc (Sched.nextNode sched) }
  st₀    = installNode nid ns st
  κ′     = thru-outer op nid ↠ κ
  step⊑  = frameStep-mono-j c 2≤S (n≤1+n j)
  B′     = Caps.cSize (frameStep (suc j) c)
  U      = unconn sl (EvalSt.connectedShares st)
  -- the source's demand, one hop-step below the composite's: the spent
  -- unit pays the thru-outer path extension in ℓ exactly
  G′     = dBound Ŝ R̂ U (hopDᵉ F b) (syncSizeᵉ b)
  sucG′≤G : suc G′ ≤ G
  sucG′≤G = ≤-trans (hop-step-gives Ŝ R̂ U (hopDᵉ F b)
                       (suc (syncSizeᵉ b)) (syncSizeᵉ b)
                       (m≤m+n (suc (syncSizeᵉ b)) (suc Ŝ)))
                    dmd
  pC′ : pathSz? B′ κ′ ≡ true
  pC′ = ∧-intro refl
          (∧-intro (T⇒≡true (suc (pathLen κ) ≤ᵇ B′)
                     (≤⇒≤ᵇ (≤-trans lC (proj₁ step⊑))))
                   (pathSz?-⊑ κ step⊑ pC))
  inv₀ : capsOK? (frameStep (suc j) c) sched₀ st₀ ≡ true
  inv₀ = capsOK?-setNode (frameStep (suc j) c) nid ns sched₀ st bn
           (subst (λ y → widNode (Caps.cWid (frameStep (suc j) c)) y ns ≡ true)
                  (sym slEq) wn)
           (capsOK?-mono (frameStep j c) (frameStep (suc j) c) sched₀ st step⊑
              (capsOK?-nextNode (frameStep j c) (suc (Sched.nextNode sched))
                                sched st inv))
  invW′ : INV? Ψ B′ sched₀ st₀ ≡ true
  invW′ = INV?-install Ψ (Caps.cSize (frameStep j c)) B′ nid ns sched sched₀ st
            (proj₁ step⊑) refl bn fnN invW
  SUB = walkFace b c Ψ F Ŝ R̂ G′ ℓ L̂ dep bud ops′ (suc j) g κ′ bid now sl sched₀ st₀
          2≤S 1≤R slEq slC slSz inv₀
          (≤-trans szb (proj₁ step⊑))
          (≤-trans wdb (proj₁ (proj₂ step⊑)))
          pC′
          (frameStep-chain-suc c j (pathLen κ) 2≤S lC)
          nst
          (chain-desc 0 (sizeᵉ b) ops′ hidx)
          (≤-trans (m≤m⊔n _ _) dpt)
          invW′ fnC
          (pathB?-widen κ (proj₁ step⊑) pB)
          s2 fS rS ceil
          (≤-trans (op-desc (Caps.cSize c) (Caps.cWid c) dep bud ops′ j 2≤S) lb)
          ≤-refl
          (hasAtLeast-mono (≤-trans sucG′≤G (n≤1+n G)) gas)
          (≤-trans (≤-reflexive (sym (+-suc (pathLen κ) G′)))
                   (≤-trans (+-monoʳ-≤ (pathLen κ) sucG′≤G) lℓ))
          rgs
  j₁  = proj₁ SUB
  S1  = proj₁ (proj₂ SUB)
  S2  = proj₁ (proj₂ (proj₂ SUB))
  S3  = proj₁ (proj₂ (proj₂ (proj₂ SUB)))
  S4  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SUB))))
  S5  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB)))))
  S6  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB))))))
  S7  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB)))))))
  S8  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB))))))))
  S9  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB))))))))
  res = subscribeE g b κ′ bid now sched₀ st₀
  KP  = subscribeE-keeps g b κ′ bid now sched₀ st₀
  sl₂eq : Sched.slots (proj₁ (proj₂ res)) ≡ sl
  sl₂eq = trans (KeepsC.slotsEq KP) slEq
  -- shares only connect during the walk, so the caller's unconn count
  -- weakens to the post-walk one
  UK : unconn sl (EvalSt.connectedShares (proj₂ (proj₂ res))) ≤ U
  UK = subst₂ (λ y z → unconn y (EvalSt.connectedShares (proj₂ (proj₂ res)))
                         ≤ unconn z (EvalSt.connectedShares st))
              sl₂eq slEq
              (unconn-keeps sched₀ st₀ (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) KP)
  PBW = pushThru-walk c Ψ F Ŝ R̂ G ℓ L̂ U (hopDᵉ F b) (suc (syncSizeᵉ b))
          dep bud (suc j + j₁) g bid now op nid
          κ (proj₁ res) sl (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
          2≤S 1≤R sl₂eq slC slSz
          S1
          (pathSz?-⊑ κ (frameStep-⊑-+ c 2≤S (suc j) j₁) (pathSz?-⊑ κ step⊑ pC))
          (≤-trans (≤-trans lC (proj₁ step⊑))
                   (proj₁ (frameStep-⊑-+ c 2≤S (suc j) j₁)))
          S2 S3
          (≤-trans (m≤n⊔m _ _) dpt)
          S5
          (pathB?-widen κ
             (≤-trans (proj₁ step⊑) (proj₁ (frameStep-⊑-+ c 2≤S (suc j) j₁))) pB)
          S6 S7 S8
          s2 fS rS ceil
          (≤-trans (push-desc (Caps.cSize c) (Caps.cWid c) dep bud ops′
                      (length (proj₁ res)) j j₁ 2≤S S4
                      (countLen (frameStep (suc j + j₁) c) (proj₁ res) S3))
                   lb)
          UK dmd gas lℓ S9
  j₂  = proj₁ PBW
  W1  = proj₁ (proj₂ PBW)
  W2  = proj₁ (proj₂ (proj₂ PBW))
  W3  = proj₁ (proj₂ (proj₂ (proj₂ PBW)))
  W4  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ PBW))))
  W5  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ PBW)))))
  W6  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ PBW))))))
  W7  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ PBW)))))))
  W8  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ PBW))))))))
  W9  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ PBW))))))))
  PB  = pushBurst g bid now (thru-outer op nid) κ (proj₁ res)
          (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
  EQ : (suc j + j₁) + j₂ ≡ j + suc (j₁ + j₂)
  EQ = trans (cong suc (+-assoc j j₁ j₂)) (sym (+-suc j (j₁ + j₂)))

-- EX-POSTULATE (2026-08-13): the core is the dispatch.  Its 21 route
-- hypotheses are bound and awaiting their clauses — each clause
-- postulate's header names the ones expected to pay it, and a clause
-- grind spends them from module scope, shedding nothing here until the
-- family is real.
subscribeE-walk-level-core : WalkLevelCore
subscribeE-walk-level-core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = walkFace

subscribeE-walk-level : WalkLevel
subscribeE-walk-level =
  subscribeE-walk-level-core
    mu-edge hop-edge connect-edge hop-step-gives hop-step-needs unconn-keeps
    sharedConnect-unconn obs-slot-shared
    -- these two must be instantiated EXPLICITLY: `splitBurst` computes on
    -- the literal event list, so the reduced statement no longer mentions
    -- Γ or u and Agda cannot solve those implicits from the expected type.
    (λ {n} {Γ} {u} {A} → share-live-novals {n} {Γ} {u} {A})
    (λ {n} {Γ} {u} {A} → share-spent-novals {n} {Γ} {u} {A})
    hasAtLeast-pad hasAtLeast-peel seed-covers budget-covers oneShot-tail-dry
    connect-anchor hopD-map-emit applyFn-size unconn-cons-≤
    shellSize-unfoldμ inner-unfoldμ walk-desc inner-desc

-- THE OUTER WET FACE, as a type.
WetOuter : Set
WetOuter =
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let sl = Sched.slots sched
      Ψ  = ΨAt e sl
      B  = sizeCapAt e sl id
      Ŝ  = sizeCapAt e sl (suc id)
  in INV? Ψ B sched st ≡ true →
     pathB? B Ψ κ ≡ true →
     pathSz? B κ ≡ true →
     suc (pathLen κ) ≤ B →
     sizeᵉ b ≤ B →
     fnCapᵉ b ≤ Ψ →
     g hasAtLeast
       suc (dBound Ŝ (hopR Ŝ)
                   (unconn sl (EvalSt.connectedShares st))
                   (hopDᵉ Ŝ b) (syncSizeᵉ b)) →
     capsOK? (capsAt e sl id) sched st ≡ true →
     dWᵉ n sl b ≤ Caps.cWid (capsAt e sl id) →
     3 + nest b sl (EvalSt.connectedShares st) ≤ B →       -- nestOK
     suc (sizeᵉ b) ≤ B →                                   -- opsOK
     depthE g b κ id now sched st ≤ capsH e sl id →        -- depOK
     let r = subscribeE g b κ id now sched st
     in (hasDry (proj₁ r) ≡ false)
        × (INV? (ΨAt e (Sched.slots (proj₁ (proj₂ r))))
                (sizeCapAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
                (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)

------------------------------------------------------------------
-- THE OUTER FACE, ASSEMBLED — ex-postulate (2026-08-13).
--
-- `subscribeE-wet-core` used to be a postulate over the walk face and
-- 19 route lemmas.  Writing the assembly showed it is pure PLUMBING:
-- instantiate the walk at the entry caps and lift its landing.  The
-- instantiation is
--
--   c := capsAt e sl id     j := 0        Ψ := ΨAt e sl
--   F , Ŝ := sizeCapAt e sl (suc id)      R̂ := hopR Ŝ
--   G := the demand         dep := capsH e sl id
--   bud := nest b sl …      ops := suc (sizeᵉ b)
--   ℓ := B + (pathLen κ + G)
--
-- and `sizeCapAt e sl id` IS `Caps.cSize (capsAt e sl id)` by
-- definition, so the size-indexed entry hypotheses transport by `refl`
-- and only the whole-Caps one needs `frameStep-0`.
--
-- WHY ℓ CARRIES A `B +`, since the obvious `ℓ := pathLen κ + G` is
-- WRONG and the assembly is what catches it: `dBound Ŝ R̂ U r s`
-- degenerates to `s` when the hop index and the unconnected count are
-- both 0 (a program with no hops and no shares), and `syncSizeᵉ b` is
-- nowhere near the tower `B`.  So the entry registry — bounded by `B`
-- through capsOK? — would not fit under `pathLen κ + G`, and the
-- ledger hypothesis would be unsatisfiable at exactly the shapes the
-- probe series calls degenerate.  Adding `B` is what makes the entry
-- weakening go through, and costs the landing nothing.
------------------------------------------------------------------

postulate
  -- ENTRY, (i): the slot store fits the caps its own recurrence is
  -- built from.  Entry-only and slot-only — no state, no level.
  entry-slotsCaps : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : Id) →
    slotsCaps? (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) sl
      ≡ true

  -- ENTRY, (ii): and its total size does too.  Companion of
  -- `size≤sizeCapAt` (.Wet/Part6, PROVEN) for the slot summand.
  entry-slotsSize : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : Id) → slotsSize sl ≤ Caps.cSize (capsAt e sl id)

  -- ENTRY, (iv): capsOK?'s registry conjunct, read as a LENGTH bound.
  -- capsOK? already carries `regsSz?` (every registered chain's frames
  -- fit the size cap); this is that conjunct with the per-chain path
  -- length read off it.
  capsOK⇒regsLen : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
    capsOK? c sched st ≡ true →
    regsLen? (Caps.cSize c) (EvalSt.registry st) ≡ true

  -- ENTRY, (v): the ledger weakens upward, which is what spends the
  -- `B +` above.
  regsLen?-mono : ∀ {n} {Γ : Ctx n} {t} (m ℓ : ℕ)
    (rs : List (RegId × Source × Chain Γ t)) → m ≤ ℓ →
    regsLen? m rs ≡ true → regsLen? ℓ rs ≡ true

  -- THE LANDING LIFT, and it is the only conjunct of this assembly with
  -- real content.  The walk lands INV? at its own level's size cap,
  -- `cSize (frameStep j′ (capsAt e sl id))`, bounded by the walk's
  -- opIterD conjunct; the outer face wants it at `sizeCapAt e sl
  -- (suc id)`.  This is `sub-charge-capsOK-lift`'s chain (.Caps-Bridge)
  -- — opIterD-dominated → sizeCount-body → sizeCount-mono-d over depOK
  -- → capsAt-suc-full → frameStep-mono-j — plus INV?'s upward
  -- monotonicity in B.  Slots never change across a run, so the Ψ index
  -- transports untouched.
  wet-landing-lift : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (j′ : ℕ) →
    let sl = Sched.slots sched
        r  = subscribeE g b κ id now sched st
    in depthE g b κ id now sched st ≤ capsH e sl id →
       0 + j′ ≤ opIterD (Caps.cSize (capsAt e sl id))
                        (Caps.cWid (capsAt e sl id))
                        (capsH e sl id)
                        (nest b sl (EvalSt.connectedShares st))
                        (suc (sizeᵉ b)) 0 →
       INV? (ΨAt e sl)
            (Caps.cSize (frameStep (0 + j′) (capsAt e sl id)))
            (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
       INV? (ΨAt e (Sched.slots (proj₁ (proj₂ r))))
            (sizeCapAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
            (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true

-- ENTRY, (iii): the reset cap ceils the walk — no level the entry budget can
-- reach outgrows the NEXT instant's size cap.  Discharged 2026-08-13: the
-- chain is opIterD-dominated → sizeCount-body → capsAt-suc-full →
-- frameStep-mono-j (identical to sub-charge-capsOK-lift's route, .Caps-Bridge,
-- without the final capsOK?-mono step — we only need the size projection).
-- WetOuter's nestOK/opsOK supply the two size bounds opIterD-dominated needs.
entry-ceiling : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : Id) {u} (b : Closed Γ u) (cs : List Source) →
  3 + nest b sl cs ≤ Caps.cSize (capsAt e sl id) →     -- nestOK
  suc (sizeᵉ b) ≤ Caps.cSize (capsAt e sl id) →        -- opsOK
  Caps.cSize (frameStep (opIterD (Caps.cSize (capsAt e sl id))
                                 (Caps.cWid (capsAt e sl id))
                                 (capsH e sl id) (nest b sl cs)
                                 (suc (sizeᵉ b)) 0)
                        (capsAt e sl id))
    ≤ sizeCapAt e sl (suc id)
entry-ceiling e sl id b cs nestOK opsOK = proj₁ lift-⊑
  where
  c   = capsAt e sl id
  hS  = 2≤capsAt-size e sl id
  L₀  = opIterD (Caps.cSize c) (Caps.cWid c) (capsH e sl id)
                (nest b sl cs) (suc (sizeᵉ b)) 0
  j≤full : L₀ ≤ sizeCount c (capsH e sl id)
  j≤full =
    ≤-trans (opIterD-dominated (Caps.cSize c) (Caps.cWid c) (capsH e sl id)
                (nest b sl cs) (suc (sizeᵉ b)) (Caps.cReg c)
                hS nestOK opsOK (1≤capsAt-reg e sl id))
            (≤-reflexive (sym (sizeCount-body c (capsH e sl id))))
  lift-⊑ : frameStep L₀ c ⊑ᶜ capsAt e sl (suc id)
  lift-⊑ = subst (λ x → frameStep L₀ c ⊑ᶜ x)
                 (sym (capsAt-suc-full e sl id))
                 (frameStep-mono-j c hS j≤full)

subscribeE-wet-core : WalkLevel → WetOuter
subscribeE-wet-core wl {n} {Γ} {t} {e} {u} g b κ id now sched st
                    inv pB pS pLen szB fcB gas cOK dW nestOK opsOK depOK =
    dry
  , wet-landing-lift g b κ id now sched st j′ depOK lvl invL
  where
  sl = Sched.slots sched
  c  = capsAt e sl id
  Ψ  = ΨAt e sl
  B  = sizeCapAt e sl id
  Ŝ  = sizeCapAt e sl (suc id)
  G  = dBound Ŝ (hopR Ŝ) (unconn sl (EvalSt.connectedShares st))
               (hopDᵉ Ŝ b) (syncSizeᵉ b)
  ℓ  = B + (pathLen κ + G)

  cOK0 : capsOK? (frameStep 0 c) sched st ≡ true
  cOK0 = subst (λ x → capsOK? x sched st ≡ true) (sym (frameStep-0 c)) cOK

  regs : regsLen? ℓ (EvalSt.registry st) ≡ true
  regs = regsLen?-mono B ℓ (EvalSt.registry st) (m≤m+n B (pathLen κ + G))
           (capsOK⇒regsLen c sched st cOK)

  L₀ = opIterD (Caps.cSize c) (Caps.cWid c) (capsH e sl id)
               (nest b sl (EvalSt.connectedShares st)) (suc (sizeᵉ b)) 0

  W = wl b c Ψ Ŝ Ŝ (hopR Ŝ) G ℓ L₀ (capsH e sl id)
         (nest b sl (EvalSt.connectedShares st)) (suc (sizeᵉ b)) 0
         g κ id now sl sched st
         (2≤capsAt-size e sl id) (1≤capsAt-reg e sl id) refl
         (entry-slotsCaps e sl id) (entry-slotsSize e sl id)
         cOK0 szB dW pS pLen ≤-refl ≤-refl depOK
         inv fcB pB
         -- the reset-anchor pins at the entry: the F/R̂ equations are
         -- refl by the instantiation, 2 ≤ Ŝ is the next instant's own
         -- entry floor, and the ceiling is entry-ceiling at L̂ := the
         -- entry budget itself (so the budget pin is ≤-refl)
         (2≤capsAt-size e sl (suc id)) refl refl
         (entry-ceiling e sl id b (EvalSt.connectedShares st) nestOK opsOK) ≤-refl
         ≤-refl gas (m≤n+m (pathLen κ + G) B) regs

  -- the Σ's nine conjuncts, named rather than counted: capsOK?,
  -- burstCaps?, burstCount?, the opIterD level bound, INV?, burstB?,
  -- burstHopD?, hasDry, regsLen?
  j′ = proj₁ W
  p2 = proj₂ W
  p3 = proj₂ p2
  p4 = proj₂ p3
  p5 = proj₂ p4
  p6 = proj₂ p5
  p7 = proj₂ p6
  p8 = proj₂ p7
  p9 = proj₂ p8

  lvl  = proj₁ p5
  invL = proj₁ p6
  dry  = proj₁ p9

subscribeE-wet : WetOuter
subscribeE-wet = subscribeE-wet-core subscribeE-walk-level
