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
open import Rx.Evaluator using (Sched; EvalSt; Slots; Slot; shared;
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

postulate
  -- THE COLLAPSED WALK FACE.  Hypotheses: subscribeE-caps' list
  -- verbatim (caps prelims, the level-indexed size/width/path bounds,
  -- the three charge indices dep/bud/ops), then the wet half at the
  -- SAME level (INV? / fnCap / pathB? at cSize (frameStep j c)), then
  -- the dry half unchanged (demand at the reset caps, one spare peel,
  -- the free length ledger ℓ).  Conclusion: subscribeE-caps' Σ with
  -- the wet conjuncts riding the same witness.
  --
  -- To be ground clause by clause through the mutual block
  -- (subscribeE / stepFrame / pushBurst / subscribeAll /
  -- subscribeInner / subscribeSharedSlot), each decrement edge
  -- consuming one hasAtLeast peel against dBound-μ / dBound-hop /
  -- dBound-connect, riding subscribeE-caps' proven clause skeleton for
  -- the level half.
  subscribeE-walk-level : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
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

postulate
  -- THE WET CONTRACT's CORE, restated over the collapsed walk
  -- (2026-08-13; the previous form, narrowed over the ledger walk, is
  -- in the RECOVERY commit above — its walk hypothesis was
  -- machine-refuted as unsatisfiable-in-composition, wet-ceiling-absurd).
  --
  -- THE OUTER FACE GAINS THE CAPS-SIDE HYPOTHESES — exactly the list
  -- `subscribeE-wet-via-caps` (.Caps-Bridge) already carries and its
  -- call sites already supply (the root has init-capsOK? /
  -- dWe≤cWid / depthE≤capsH-root; via-caps holds them as its own
  -- hypotheses).  This is the ruling's clause (b) run in reverse: the
  -- conjuncts one face has and the other lacks ride as explicit
  -- hypotheses, free at every call site.
  --
  -- THE INSTANTIATION, so the grind starts aimed: c := capsAt e sl id,
  -- j := 0 (frameStep-0 rewrites the entry hypotheses to the outer
  -- face's own), dep := depthE (≤-refl), bud := nest (≤-refl),
  -- ops := suc (sizeᵉ b) (≤-refl), G := the demand (≤-refl),
  -- ℓ := (sizeCapAt e sl id) + (pathLen κ + G) — regsLen? at entry
  -- weakens up from capsOK?'s regsSz? conjunct (pathSz? carries the
  -- per-entry length bound), and the landing lifts by the
  -- sub-charge-capsOK-lift chain plus INV?'s upward B-monotonicity.
  subscribeE-wet-core :
    -- subscribeE-walk-level  (above)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
      (c : Caps) (Ψ F Ŝ R̂ G ℓ dep bud ops j : ℕ)
      (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
      (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
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
      INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
      fnCapᵉ b ≤ Ψ →
      pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
      dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
             (hopDᵉ F b) (syncSizeᵉ b) ≤ G →
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
         × (burstHopD? F (hopDᵉ F b) (proj₁ r) ≡ true)
         × (hasDry (proj₁ r) ≡ false)
         × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
     ) →
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

-- the wet face, assembled over its core.  The outer statement is
-- subscribeE-wet-via-caps' own hypothesis list (.Caps-Bridge) minus its
-- caps conclusion — every call site already holds every argument.
subscribeE-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
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
     3 + nest b sl (EvalSt.connectedShares st) ≤ B →
     suc (sizeᵉ b) ≤ B →
     depthE g b κ id now sched st ≤ capsH e sl id →
     let r = subscribeE g b κ id now sched st
     in (hasDry (proj₁ r) ≡ false)
        × (INV? (ΨAt e (Sched.slots (proj₁ (proj₂ r))))
                (sizeCapAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
                (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
subscribeE-wet =
  subscribeE-wet-core subscribeE-walk-level
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
