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

open import Data.Bool    using (Bool; true; false)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _<_;
                                _≤ᵇ_; z≤n; s≤s)
open import Data.List    using (List; []; _∷_; _++_; length; map)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive;
                                       m≤m+n; m≤n+m; n≤1+n;
                                       +-suc; +-assoc; +-monoʳ-≤;
                                       m≤m⊔n; m≤n⊔m; ≤⇒≤ᵇ)
open import Data.Maybe   using (nothing)
open import Data.Bool.ListAction using (all; any)
open import Data.Fin     using (Fin; toℕ)
open import Data.Vec     using (Vec; lookup)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import Rx.Prim      using (Tick; Id; Source; init; value; close;
                                complete; exhausted; subscribe;
                                _at_from_as_;
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
                                opIterD; fIterD;
                                Frame; thru-outer; pushBurst;
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
         pathSz?-⊑; frameStep-chain-suc; frameStep-⊑-+)
-- the chain-charge algebra subscribeE-caps' own *All head spends
open import Verify-Budget-Sufficient.Caps-Chain
  using (chain-desc; op-step; burst-index)
-- ONE proven projection, not the face: burstCount? read as a length
open import Verify-Budget-Sufficient.Subscribe-Face using (countLen)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthE; depthAll; depthBurst)


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
  ∀ (c : Caps) (Ψ F Ŝ R̂ G ℓ dep bud ops j : ℕ)
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
  -- is paid below pushBurst-walk (its header names the live edge and
  -- the minimal-gas probe that must precede its grind).
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
  -- PROBED 2026-08-13 (Demand-Probe, P-series; dual-sided pins), and
  -- the mechanism HELD on every shape run — no refutation of either
  -- conjunct.  Coverage, stated exactly:
  --   · regsLen?: scan-GROWN inners subscribed through mergeAll at
  --     k = 1 and k = 2 nesting, registry non-empty at exit (deferᵉ
  --     persistence; the B/D/E series turned out DEGENERATE here —
  --     their registries empty at exit).  Max minted pathLen 2/3/4 vs
  --     dBound 11/1477/1478 — and the comparison ran at Ŝ = 5, BELOW
  --     the grown inner's measured sizeᵉ = 8, which is the STRICT
  --     direction: dBound is monotone in Ŝ, so green here implies
  --     green at every faithful (larger) Ŝ.
  --   · hasDry: minimal dry-free pad bisected exactly (h* = 1/2/3),
  --     h* ≤ suc dBound with three-orders margin; hasAtLeast-pad makes
  --     the padded run a legitimate instance of the conjunct's
  --     hypothesis.
  --   · Ŝ-ceiling: grown-inner sizes pinned (sizeᵉ acc₁ ≡ 8), so the
  --     true instantiation needs sizeCapAt ≥ 8 at that subscription
  --     point — trivially met by the tower.
  -- NOT COVERED, and the class stays FALSITY on account of it: the
  -- COMPOUNDING regime (growth that squares repeatedly within one
  -- instant, k ≥ 3, sizes beyond ~12), programs with shares/connect
  -- edges, and mid-cascade registry states richer than two entries.
  -- The margins (~3 orders) suggest slack, but slack observed at
  -- small k is exactly what geometric growth eats.
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
  -- pathB? weakens upward in B (Ψ fixed): every frameB? B test is a
  -- size ≤ᵇ B, the Ψ tests don't mention B.  pathSz?-⊑'s wet twin.
  pathB?-mono-B : ∀ {n} {Γ : Ctx n} {s t}
    (B B′ Ψ : ℕ) (κ : Path Γ s t) → B ≤ B′ →
    pathB? B Ψ κ ≡ true → pathB? B′ Ψ κ ≡ true

  -- THE PUSH FACE, WET — pushBurst-caps ⊗ the wet content, one Σ,
  -- the same conservative extension subscribeAll-walk was over
  -- subscribeAll-caps, one face down.  The caps half (hypotheses and
  -- the first four conjuncts, including the per-emit fIterD charge) is
  -- pushBurst-caps' own face VERBATIM (.Subscribe-Face:2440, GROUND),
  -- so the risk is again WITNESS-COINCIDENCE, plus the two live edges
  -- below.  Σ-content: same accounting as the walk face's (five
  -- conjuncts upward-closed in j′, given content by the downward
  -- fIterD bound; burstHopD?/hasDry/regsLen? j′-free).
  --
  -- THE HOP PEEL IS PAID BELOW THIS FACE.  pushBurst's per-emit step
  -- is stepFrame, and a thru-outer frame's consume subscribes each
  -- inner value through subscribeInner — the gas-peel edge.  The
  -- burstHopD? F r̂ hypothesis is what makes the peel STRICT with no
  -- arithmetic: an inner drawn from str has hopD ≤ r̂ < suc r̂, and
  -- dBound's per-hop refill (hop-step-gives) funds the inner's demand
  -- at the descended index.  The ŝ DECOUPLING is deliberate: after one
  -- hop the refill resets the sync budget to Ŝ-scale (suc s′ ≤ s +
  -- suc Ŝ), so no hypothesis links ŝ to str's own values.
  --
  -- ⚠ THE LIVE EDGE, named at authoring — THE REFILL IS Ŝ-SCALE BUT
  -- THE VALUE RECEIPTS ARE LEVEL-SCALE.  The inner's post-hop sync
  -- budget is ~Ŝ; the receipts bound the inner's syncSize by the
  -- LEVEL cap (burstB?'s size half + reach-reset, .Measures), and NO
  -- hypothesis here — or anywhere in WalkStmt — links the two.  At
  -- the true instantiation Ŝ IS the landing cap and every level the
  -- walk visits sits under it (sub-charge-capsOK-lift's chain), so
  -- the statement is BELIEVED at the instantiation that matters; but
  -- the face quantifies Ŝ freely, and at a tiny Ŝ with the gas pinned
  -- minimal (g := exactly suc G peels — nothing forbids it) the hop
  -- may run dry.  This is the walk-input header's "does within-instant
  -- growth stay under Ŝ" question surfacing as a POSSIBLE FALSITY OF
  -- THE FACE AS STATED, and unlike the anchor it is PROBEABLE: hasDry
  -- is j′-free, so a single run with all hypotheses satisfied and
  -- hasDry ≡ true refutes the whole Σ with no opIterD evaluation.  If
  -- it refutes, the repair is a threaded ceiling hypothesis (the walk's
  -- maximal level fits under Ŝ), a signature change to the whole face,
  -- NOT a weakening.
  --
  -- PROBE BUILT 2026-08-13 (Demand-Probe, series D) — READ ITS COVERAGE
  -- AND COST RECEIPT BEFORE RE-OPENING THIS.  Ŝ/R̂/F are quantified
  -- FREELY here, so the adversarial instantiation is the smallest, where
  -- the demand collapses to `syncSizeᵉ b + hopDᵉ 0 b` — a SUM, against a
  -- gas demand that tracks within-instant nesting DEPTH, a PRODUCT d·k
  -- for a fold of depth d over k values.  The sum side is pinned at six
  -- points (exactly 5d + k + 12) and the depth model is pinned in the
  -- refuting direction at (3,4).
  --
  -- WHAT IS COVERED: the SAFE region only — margins of three orders at
  -- the small shapes, 18 at (3,4).  WHAT IS NOT: the crossing region,
  -- which the model puts just above (6,8).  That row is a MULTI-HOUR
  -- job, not a pin (`runDry` has no short-circuit in either direction;
  -- cost is quadratic in k, receipt in Demand-Probe), so a green
  -- series D is NOT evidence for this face — it reaches only the region
  -- where the sum still dominates, which is the region that was never
  -- in doubt.  Per the standing rule, this does not lower the class.
  pushBurst-walk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (c : Caps) (Ψ F Ŝ R̂ G ℓ U r̂ ŝ dep bud j : ℕ)
    (g : Gas) (bid : Id) (now : Tick)
    (f : Frame Γ s u) (κ : Path Γ u t) (str : Stream Γ s)
    (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    frameSz? (Caps.cSize (frameStep j c)) f ≡ true →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    burstCaps? (frameStep j c) sl str ≡ true →
    burstCount? (frameStep j c) str ≡ true →
    depthBurst g bid now f κ str sched st ≤ dep →
    -- the wet half, at the same level
    INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
    pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
    frameB? (Caps.cSize (frameStep j c)) Ψ f ≡ true →
    burstB? (Caps.cSize (frameStep j c)) Ψ str ≡ true →
    burstHopD? F r̂ str ≡ true →
    hasDry str ≡ false →
    -- the dry half: U carries the unconn slack (shares only connect
    -- during a walk, so the caller's count weakens to any earlier one)
    unconn sl (EvalSt.connectedShares st) ≤ U →
    dBound Ŝ R̂ U (suc r̂) ŝ ≤ G →
    g hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let r = pushBurst g bid now f κ str sched st
    in Σ ℕ λ j′ →
       (capsOK? (frameStep (j + j′) c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
       × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
       × (j + j′ ≤ fIterD (Caps.cSize c) (Caps.cWid c) dep bud (length str) j)
       × (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
               (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
       × (burstHopD? F (suc r̂) (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)
       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)

-- THE *All DELEGATE — subscribeAll-caps ⊗ the wet content, one Σ,
-- exactly as WalkStmt is subscribeE-caps ⊗ the same content, and REAL:
-- the body (below walkFace — the two are mutual, the recursion
-- decreasing at walkFace (opᵉ b) → … → walkFace b) mirrors
-- subscribeAll-caps' proven proof step for step.  mint → install
-- (capsOK?-setNode / INV?-install) → the recursive walk on b at
-- κ′ = thru-outer op nid ↠ κ, funded by hop-step-gives (the composite
-- demand at suc/suc measures yields the source's demand STRICTLY
-- smaller, the spent unit paying the ℓ extension exactly — the unit
-- subscribeE-inner-nodry-pLen lacks) → pushBurst-walk over the
-- returned burst → op-step for the level charge.  The residue is
-- pushBurst-walk and the two plumbing pieces, above.
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
  (c : Caps) (Ψ F Ŝ R̂ G ℓ dep bud ops j : ℕ)
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
walk-mergeAll b c Ψ F Ŝ R̂ G ℓ dep bud ops j g κ bid now sl sched st
  2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB dmd gas lℓ rgs =
  subscribeAll-walk c Ψ F Ŝ R̂ G ℓ dep bud ops j g mergeᵒ (merge-st 0 false)
    b κ bid now sl sched st
    2≤S 1≤R slEq slC slSz inv refl refl
    (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC
    (merge-step _ sl _ bud nst) hidx dpt
    invW fnC refl pB dmd gas lℓ rgs

walk-concatAll : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (b : Closed Γ (obs u)) → WalkStmt {e = e} (concatAllᵉ b)
walk-concatAll {u = u} b c Ψ F Ŝ R̂ G ℓ dep bud ops j g κ bid now sl sched st
  2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB dmd gas lℓ rgs =
  subscribeAll-walk c Ψ F Ŝ R̂ G ℓ dep bud ops j g concatᵒ
    (concat-st {t = u} [] false false) b κ bid now sl sched st
    2≤S 1≤R slEq slC slSz inv refl refl
    (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC
    (concat-step _ sl _ bud nst) hidx dpt
    invW fnC refl pB dmd gas lℓ rgs

walk-switchAll : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (b : Closed Γ (obs u)) → WalkStmt {e = e} (switchAllᵉ b)
walk-switchAll b c Ψ F Ŝ R̂ G ℓ dep bud ops j g κ bid now sl sched st
  2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB dmd gas lℓ rgs =
  subscribeAll-walk c Ψ F Ŝ R̂ G ℓ dep bud ops j g switchᵒ
    (switch-st nothing false) b κ bid now sl sched st
    2≤S 1≤R slEq slC slSz inv refl refl
    (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC
    (switch-step _ sl _ bud nst) hidx dpt
    invW fnC refl pB dmd gas lℓ rgs

walk-exhaustAll : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (b : Closed Γ (obs u)) → WalkStmt {e = e} (exhaustAllᵉ b)
walk-exhaustAll b c Ψ F Ŝ R̂ G ℓ dep bud ops j g κ bid now sl sched st
  2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB dmd gas lℓ rgs =
  subscribeAll-walk c Ψ F Ŝ R̂ G ℓ dep bud ops j g exhaustᵒ
    (exhaust-st false false) b κ bid now sl sched st
    2≤S 1≤R slEq slC slSz inv refl refl
    (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC
    (exhaust-step _ sl _ bud nst) hidx dpt
    invW fnC refl pB dmd gas lℓ rgs

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
walkFace (μᵉ body) c Ψ F Ŝ R̂ G ℓ dep bud ops j g0 κ bid now sl sched st
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ()
walkFace (μᵉ body) c Ψ F Ŝ R̂ G ℓ dep bud ops j (gs fuel) κ bid now sl sched st =
  walk-mu body c Ψ F Ŝ R̂ G ℓ dep bud ops j (gs fuel) κ bid now sl sched st
walkFace (varᵉ ())
walkFace (deferᵉ body)   = walk-defer body

-- THE *All BODY — subscribeAll-caps' proven proof, step for step, with
-- the wet conjuncts threaded through.  ops splits exactly as there: at
-- zero the index hypothesis `suc (suc (sizeᵉ b)) ≤ zero` is uninhabited,
-- and the successor clause spends op-step's one operator.
subscribeAll-walk c Ψ F Ŝ R̂ G ℓ dep bud zero j g op ns b κ bid now sl sched st
  2≤S 1≤R slEq slC slSz inv bn wn szb wdb pC lC nst ()
subscribeAll-walk c Ψ F Ŝ R̂ G ℓ dep bud (suc ops′) j g op ns b κ bid now sl sched st
  2≤S 1≤R slEq slC slSz inv bn wn szb wdb pC lC nst hidx dpt invW fnC fnN pB dmd gas lℓ rgs =
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
    , W7 , W8 , W9
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
  SUB = walkFace b c Ψ F Ŝ R̂ G′ ℓ dep bud ops′ (suc j) g κ′ bid now sl sched₀ st₀
          2≤S 1≤R slEq slC slSz inv₀
          (≤-trans szb (proj₁ step⊑))
          (≤-trans wdb (proj₁ (proj₂ step⊑)))
          pC′
          (frameStep-chain-suc c j (pathLen κ) 2≤S lC)
          nst
          (chain-desc 0 (sizeᵉ b) ops′ hidx)
          (≤-trans (m≤m⊔n _ _) dpt)
          invW′ fnC
          (pathB?-mono-B (Caps.cSize (frameStep j c)) B′ Ψ κ (proj₁ step⊑) pB)
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
  PBW = pushBurst-walk c Ψ F Ŝ R̂ G ℓ U (hopDᵉ F b) (suc (syncSizeᵉ b))
          dep bud (suc j + j₁) g bid now
          (thru-outer op nid) κ (proj₁ res) sl (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
          2≤S 1≤R sl₂eq slC slSz
          S1 refl
          (pathSz?-⊑ κ (frameStep-⊑-+ c 2≤S (suc j) j₁) (pathSz?-⊑ κ step⊑ pC))
          (≤-trans (≤-trans lC (proj₁ step⊑))
                   (proj₁ (frameStep-⊑-+ c 2≤S (suc j) j₁)))
          S2 S3
          (≤-trans (m≤n⊔m _ _) dpt)
          S5
          (pathB?-mono-B (Caps.cSize (frameStep j c))
             (Caps.cSize (frameStep (suc j + j₁) c)) Ψ κ
             (≤-trans (proj₁ step⊑) (proj₁ (frameStep-⊑-+ c 2≤S (suc j) j₁))) pB)
          refl
          S6 S7 S8
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
subscribeE-walk-level-core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = walkFace

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
    shellSize-unfoldμ inner-unfoldμ

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

  -- ENTRY, (iii): capsOK?'s registry conjunct, read as a LENGTH bound.
  -- capsOK? already carries `regsSz?` (every registered chain's frames
  -- fit the size cap); this is that conjunct with the per-chain path
  -- length read off it.
  capsOK⇒regsLen : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
    capsOK? c sched st ≡ true →
    regsLen? (Caps.cSize c) (EvalSt.registry st) ≡ true

  -- ENTRY, (iv): the ledger weakens upward, which is what spends the
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

  W = wl b c Ψ Ŝ Ŝ (hopR Ŝ) G ℓ (capsH e sl id)
         (nest b sl (EvalSt.connectedShares st)) (suc (sizeᵉ b)) 0
         g κ id now sl sched st
         (2≤capsAt-size e sl id) (1≤capsAt-reg e sl id) refl
         (entry-slotsCaps e sl id) (entry-slotsSize e sl id)
         cOK0 szB dW pS pLen ≤-refl ≤-refl depOK
         inv fcB pB ≤-refl gas (m≤n+m (pathLen κ + G) B) regs

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
