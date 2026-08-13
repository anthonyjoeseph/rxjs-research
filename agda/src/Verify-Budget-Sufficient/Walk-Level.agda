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
open import Data.Nat.Properties using (≤-refl; m≤m+n; m≤n+m)
open import Data.Bool.ListAction using (all; any)
open import Data.Fin     using (Fin; toℕ)
open import Data.Vec     using (Vec; lookup)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Prim      using (Tick; Id; Source; init; value; close;
                                complete; exhausted; subscribe;
                                _at_from_as_;
                                Gas; g0; gs; gasPad)
open import Rx.Exp       using (Ty; obs; Ctx; Closed; Val; Exp; Tm; Fn;
                                sizeᵉ; sizeᵗ; sizeᵛ; syncSizeᵉ;
                                shellSizeᵉ; innerᵉ;
                                mapᵉ; μᵉ; unfoldμ; applyFn)
open import Rx.Frame-Width using (dWᵉ)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵛ; pmᵗ)
open import Rx.Evaluator using (Sched; EvalSt; Slots; Slot; shared; RegId; Chain;
                                memberSource; Path; root; share-sink; _↠_;
                                Stream; subscribeE; sharedConnect;
                                splitBurst; hasDry; dryEvent;
                                sched-init; st-init; budgetAt; slotsSize;
                                opIterD)

-- the wet stratum: INV?, dBound, hasAtLeast, regsLen?, pathLen, the gas
-- edges, sizeCapAt, capsAt/capsH/frameStep/Caps (via .Caps), the
-- Keeps ring, and every companion the core is narrowed over
open import Verify-Budget-Sufficient.Wet
-- the caps face: only the five predicates the statement reads there
open import Verify-Budget-Sufficient.Caps-Face
  using (capsOK?; burstCaps?; burstCount?; pathSz?; slotsCaps?; nest)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)


-- THE WALK FACE AND ITS CORE, as types — named once so that neither
-- the postulate that asserts the face nor the assembly that consumes
-- it has to retype the statement.  Both sit above the postulate block
-- because a postulate cannot reference a definition below it.
WalkLevel : Set
WalkLevel =
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (Ψ F Ŝ R̂ G ℓ dep bud ops j : ℕ)
    (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
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
  -- THE COLLAPSED WALK FACE.  Hypotheses: subscribeE-caps' list
  -- verbatim (caps prelims, the level-indexed size/width/path bounds,
  -- the three charge indices dep/bud/ops), then the wet half at the
  -- SAME level (INV? / fnCap / pathB? at cSize (frameStep j c)), then
  -- the dry half unchanged (demand at the reset caps, one spare peel,
  -- the free length ledger ℓ).  Conclusion: subscribeE-caps' Σ with
  -- the wet conjuncts riding the same witness.
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
  -- To be ground clause by clause through the mutual block
  -- (subscribeE / stepFrame / pushBurst / subscribeAll /
  -- subscribeInner / subscribeSharedSlot), each decrement edge
  -- consuming one hasAtLeast peel against dBound-μ / dBound-hop /
  -- dBound-connect, riding subscribeE-caps' proven clause skeleton for
  -- the level half.
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
  subscribeE-walk-level-core : WalkLevelCore

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

  W = wl c Ψ Ŝ Ŝ (hopR Ŝ) G ℓ (capsH e sl id)
         (nest b sl (EvalSt.connectedShares st)) (suc (sizeᵉ b)) 0
         g b κ id now sl sched st
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
