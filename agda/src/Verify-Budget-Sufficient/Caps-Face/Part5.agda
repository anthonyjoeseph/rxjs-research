-- Verify-Budget-Sufficient.Caps-Face.Part5
-- innerFinish-zero … reach-reset
module Verify-Budget-Sufficient.Caps-Face.Part5 where

open import Data.Bool    using (Bool; true; false; T; _∧_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; _⊔_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-reflexive; +-identityʳ; m≤m+n; n≤1+n; +-mono-≤; *-mono-≤; *-monoʳ-≤;
  +-monoʳ-≤; ⊔-lub)
open import Data.Empty   using (⊥-elim)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; length; map)
open import Data.Bool.ListAction using (all)
open import Data.Fin     using (Fin)
import Data.Fin as Fin
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.Maybe   using (Maybe; nothing; just)
open import Relation.Nullary using (yes; no)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; subst)

open import Rx.Prim      using (Tick; Id; _at_from_as_; Gas; Timed; after_,_)
open import Rx.Exp       using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; _≟ᵗ_; isData; Ctx; Closed; Val; sizeᵗ; sizeᵛ; Fn;
  applyFn)
open import Rx.Frame-Width using (pWᵛ; dWᵛ; outWᵛ)
open import Rx.Evaluator using (Sched; EvalSt; LiveSource; resolve; scanVals; NodeState; scan-st; take-st;
  mergeAll-st; switch-st; exhaust-st; lookupNode; NodeId; scan-f; takeVals; takeDispatch; Path;
  stepFrame; fCharge; sizeStep; iterSize; iterFold)
open import Rx.Slots using (Slots)
open import Rx.Slot-Clos using (slotClos)

-- .Delivery-Walk re-exports BOTH prerequisites of the cascade
-- conjuncts and adds the walk itself:
--
--   · .Caps holds the recurrence (Caps / frameStep / frameBlowup /
--     capsAt and their supply lemmas) and re-exports .Keeps-Ring, hence
--     .Measures.  Extracted so that a grind here no longer
--     re-checks .Wet — see that module's head.
--   · .Deliveries is the ledger stratum: where EvalSt.delivered moves
--     and where it provably does not, plus delivN and its composition
--     laws.  delivN is the currency the cascade conjuncts are stated in.
--   · .Delivery-Walk maps the delivery clique onto the LEVEL walk —
--     foldPath ↦ dCapᶜ, dispatchShare ↦ dCapᶜ, shareGo ↦ dWalkᶜ,
--     cascadeGo ↦ dWalkᶜ — RELATIVE to one frame's face at the level it
--     RUNS at, which it takes as a record of hypotheses rather than
--     postulating.  `walkH` below instantiates that record and
--     `cascadeGo-deliveries` is the theorem it buys.
open import Verify-Budget-Sufficient.Measures using
  (all-impl; boundedLive; boundedNode; fnCapᵛ; ∧-true)
open import Verify-Budget-Sufficient.Caps using
  (Caps; frameStep; iterFold-infl; iterFold-mono-count; iterSize-infl;
   iterSize-mono-count; iterSize-suc)
-- the nesting measure the subscribe budget descends on, and the frame
-- row that supplies it.  Re-exported, so the clique names one module
-- the depth mirror: `depthInner` is the fuel `thruOuter-face-core`'s
-- new hypothesis ranges over (see below, ~6307).  The rest of the family
-- carries THE DEPTH PREMISE down the frame chain, and it threads by
-- IDENTITY because the mirror is definitionally equal at every hop:
--   depthFrame … (from-inner op allNid inst) … fin = depthReact … fin
--   depthReact … true  = depthFin … (lookupNode allNid (EvalSt.nodes st))
--   depthReact … false = 0
-- so each face passes its premise straight to the next and the absorbed
-- branch needs nothing at all
-- arithmetic lemmas consumed by thruOuter-face-core's walk helpers

open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (capsOK?-nodeSz; capsOK?-nodeWid; capsOK?-parts; capsOK?-setNode; face-lift;
   FrameFace; lookupNode-caps; valsCaps?)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (applyFn-iterSize; capsOK?; capsOK?-mono; closLive; eventCaps?;
   closSizeᵛ; closSizeᵛ-OK; closSizeᵛ≤mul;
   frameSz?; iterFold-+; iterSize-+; nestClosOK?ᵛ; pair≤sizeStep; pathSz?;
   slotsCaps?; slotsCaps?-clos; SlotWid; valCaps?; widLive; widNode)
open import Verify-Budget-Sufficient.Caps-Face.Part3 using
  (applyFn-iterFold; frameStep-⊑-+; valCaps?-size; valCaps?-wid; wid-lift)
open import Verify-Budget-Sufficient.Caps-Face.Part2 using
  (pWᵛ-pair; slotsCaps?-slotWid; SlotWid-mono)
open import Decide using (T-to; T⇒≡true; ∧-intro; ≤ᵇ-widen)

-- the clauses of innerFinish that neither emit nor step: a mistyped or
-- missing node, and every op/node pair the evaluator's catch-all covers
innerFinish-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (j : ℕ) (sl : Slots Γ) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) →
  capsOK? (frameStep j c) sched st ≡ true →
  all (valCaps? (frameStep j c) sl s) vals ≡ true →
  Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c) sched st ≡ true)
     × (all (valCaps? (frameStep (j + j′) c) sl s) vals ≡ true)
     × (all (eventCaps? {n = n} {Γ = Γ} {u = t} (frameStep (j + j′) c) sl) []
          ≡ true)
innerFinish-zero c j sl vals sched st inv vC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , subst (λ x → all (valCaps? (frameStep x c) sl _) vals ≡ true)
            (sym (+-identityʳ j)) vC
    , refl

------------------------------------------------------------------
-- THE SLOT EDGE, GROUND: subscribeE-input-caps, and both of the two
-- blockages that stopped it are gone.

-- Its four branches:
--
--   scripted (hot _)   A spent script answers with a
--                      one-shot close; a live one registers, which is
--                      register-caps and one j.  Needs nothing new.
--   shared d           needs `sizeᵉ d ≤ cSize` for sharedSlot-caps.
--   scripted (cold …)  oneShotBurst carries the slot's own sync
--                      values, and the async tail becomes a LiveSource
--                      whose pendings capsOK? bounds by cSize and
--                      cWid.  Both are slot data.

-- BLOCKAGE 1 — THE JOINT BOUND — IS RESOLVED, by a design ruling whose
-- evidence is Joint-Probe.  What blocked here (and
-- at thruWalk / mergeAllDrain / innerFinish) was that subscribeE-caps
-- demanded `pathLen κ + sizeᵉ b ≤ cSize` while the delivery side
-- carries the two bounds SEPARATELY.  The natural-looking repair —
-- thread round 3's ℓ ledger through the delivery clique too — was
-- gated first, and the gate came back negative: Joint-Probe measures
-- the joint sum against the TIGHT admissible cSize on seventeen
-- families and it is violated on every one, at adm + 1 EXACTLY on
-- every family carrying a scan.  A subscribed payload that IS the
-- stored accumulator already attains the cap by itself, so any chain
-- on top overshoots and no constant slackening of the ledger survives.
-- So the JOINT FORM went, not the delivery side: subscribeE-caps now
-- asks for `suc (pathLen κ) ≤ cSize` and `sizeᵉ b ≤ cSize` separately,
-- which is exactly what foldPath-caps already splits out of pathSz?.
-- The induction still closes because each *All hop PAYS ONE j for the
-- from-inner frame it adds, and one j at least doubles cSize
-- (frameStep-chain-suc), so a +1 chain extension is absorbed with
-- room.  The extra receipt rides in the same sum the fold receipts do.

-- BLOCKAGE 2 — `c` NOT TIED TO `sl` — IS REPAIRED AT THE TELESCOPE.
-- capsAt's base is `2 + sizeᵉ e + slotsSize sl`, so the connection
-- exists at the top and used to be thrown away by the time a companion
-- was stated at an abstract `c`: nothing bounded a slot def or a
-- scripted value, since `d` is `Sched.slots sched i` and capsOK? never
-- mentions slotsSize.  `slotsCaps? (Caps.cSize c) sl` is that
-- connection as a decidable side condition, threaded unchanged through
-- the whole tree exactly as `2 ≤ Caps.cSize c` and `1 ≤ Caps.cReg c`
-- are (slots never change, so it is a constant), and supplied by
-- slotsCaps?-capsAt.  What is left here is the CLAUSE: the shared
-- branch reads its `d` out of it, and the cold branch its sync values
-- and async pendings.

-- AND THE WIDTH HALF IS FREE, which is why slotsCaps? carries sizes
-- only.  A scripted slot's element type is DATA — the `ok` proof the
-- `scripted` constructor carries is exactly `T (isData t)` — and pWᵛ
-- is identically zero on a data type, since only its `obs` clause reads
-- a width at all.  So a scripted value's width bound is refl and the
-- side condition never has to mention cWid.  A shared slot's def is
-- handed to sharedSlot-caps, which asks for its size and nothing else.
------------------------------------------------------------------
-- THE DELIVERY CLIQUE — foldPath / dispatchShare / shareGo /
-- chainStep — is no longer postulated: it is GROUND, below the block,
-- on stepFrame-caps and the three share-bookkeeping leaves.  Neither
-- is the *All edge: subscribeInner-caps, thruConsume-caps,
-- thruWalk-caps, mergeAllDrain-caps and innerFinish-caps are all ground
-- below, once the joint bound stopped blocking them.

-- a data type has no observable inside it, so it has neither a
-- delivered nor a parked frame width — which is what still makes the
-- scripted half of the slot side condition a size-only predicate.  Both
-- axes need their own induction: pWᵛ is a join of two structural
-- recursions, and at a pair the joins interleave
outWᵛ-data : ∀ {n} {Γ : Ctx n} (k : ℕ) (sl : Slots Γ) (u : Ty) → T (isData u) →
  (v : Val Γ u) → outWᵛ k sl u v ≡ 0
outWᵛ-data k sl unitᵗ ok v = refl
outWᵛ-data k sl boolᵗ ok v = refl
outWᵛ-data k sl natᵗ  ok v = refl
outWᵛ-data k sl (s ×ᵗ u) ok (a , b) with isData s in eqs
... | true  = cong₂ _⊔_ (outWᵛ-data k sl s (subst T (sym eqs) tt) a)
                        (outWᵛ-data k sl u ok b)
... | false = ⊥-elim ok
outWᵛ-data k sl (s +ᵗ u) ok (inj₁ a) with isData s in eqs
... | true  = outWᵛ-data k sl s (subst T (sym eqs) tt) a
... | false = ⊥-elim ok
outWᵛ-data k sl (s +ᵗ u) ok (inj₂ b) with isData s
... | true  = outWᵛ-data k sl u ok b
... | false = ⊥-elim ok
outWᵛ-data k sl (obs u) ok v = ⊥-elim ok

dWᵛ-data : ∀ {n} {Γ : Ctx n} (k : ℕ) (sl : Slots Γ) (u : Ty) → T (isData u) →
  (v : Val Γ u) → dWᵛ k sl u v ≡ 0
dWᵛ-data k sl unitᵗ ok v = refl
dWᵛ-data k sl boolᵗ ok v = refl
dWᵛ-data k sl natᵗ  ok v = refl
dWᵛ-data k sl (s ×ᵗ u) ok (a , b) with isData s in eqs
... | true  = cong₂ _⊔_ (dWᵛ-data k sl s (subst T (sym eqs) tt) a)
                        (dWᵛ-data k sl u ok b)
... | false = ⊥-elim ok
dWᵛ-data k sl (s +ᵗ u) ok (inj₁ a) with isData s in eqs
... | true  = dWᵛ-data k sl s (subst T (sym eqs) tt) a
... | false = ⊥-elim ok
dWᵛ-data k sl (s +ᵗ u) ok (inj₂ b) with isData s
... | true  = dWᵛ-data k sl u ok b
... | false = ⊥-elim ok
dWᵛ-data k sl (obs u) ok v = ⊥-elim ok

pWᵛ-data : ∀ {n} {Γ : Ctx n} (k : ℕ) (sl : Slots Γ) (u : Ty) → T (isData u) →
  (v : Val Γ u) → pWᵛ k sl u v ≡ 0
pWᵛ-data k sl u ok v =
  cong₂ _⊔_ (outWᵛ-data k sl u ok v) (dWᵛ-data k sl u ok v)

-- and the SAME emptiness on the Ψ axis, which is the cheapest of the three:
-- fnCapᵛ is a plain structural recursion with no isData scrutinee of its own
-- and no slots to carry, so where outWᵛ needs the `with` to see that a pair's
-- left half is data, this reads it straight off the conjunction.  fnCapᵛ is
-- nonzero at `obs` ALONE, and isData is exactly the absence of obs.
fnCapᵛ-data : ∀ {n} {Γ : Ctx n} (u : Ty) → T (isData u) →
  (v : Val Γ u) → fnCapᵛ u v ≡ 0
fnCapᵛ-data unitᵗ ok v = refl
fnCapᵛ-data boolᵗ ok v = refl
fnCapᵛ-data natᵗ  ok v = refl
fnCapᵛ-data (s ×ᵗ u) ok (a , b) with isData s in eqs
... | true  = cong₂ _⊔_ (fnCapᵛ-data s (subst T (sym eqs) tt) a)
                        (fnCapᵛ-data u ok b)
... | false = ⊥-elim ok
fnCapᵛ-data (s +ᵗ u) ok (inj₁ a) with isData s in eqs
... | true  = fnCapᵛ-data s (subst T (sym eqs) tt) a
... | false = ⊥-elim ok
fnCapᵛ-data (s +ᵗ u) ok (inj₂ b) with isData s
... | true  = fnCapᵛ-data u ok b
... | false = ⊥-elim ok
fnCapᵛ-data (obs u) ok v = ⊥-elim ok

valCaps?-data : ∀ {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ) (u : Ty) → T (isData u) →
  (v : Val Γ u) → (sizeᵛ u v ≤ᵇ Caps.cSize c) ≡ true → valCaps? c sl u v ≡ true
valCaps?-data {n = n} c sl u ok v h =
  ∧-intro h (subst (λ x → (x ≤ᵇ Caps.cWid c) ≡ true)
                   (sym (pWᵛ-data n sl u ok v)) refl)

valsCaps?-data : ∀ {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ) (u : Ty) → T (isData u) →
  (vs : List (Val Γ u)) → all (λ v → sizeᵛ u v ≤ᵇ Caps.cSize c) vs ≡ true →
  all (valCaps? c sl u) vs ≡ true
valsCaps?-data c sl u ok []       h = refl
valsCaps?-data c sl u ok (v ∷ vs) h
  with ∧-true (sizeᵛ u v ≤ᵇ Caps.cSize c)
              (all (λ x → sizeᵛ u x ≤ᵇ Caps.cSize c) vs) h
... | h1 , h2 = ∧-intro (valCaps?-data c sl u ok v h1)
                        (valsCaps?-data c sl u ok vs h2)

-- resolving a delta-encoded tail against an anchor keeps the values, so
-- it keeps their bounds
resolve-caps : ∀ {n} {Γ : Ctx n} {u} (B : ℕ) (anchor : Tick)
  (ds : List (Timed (Val Γ u))) →
  all (λ tv → sizeᵛ u (Timed.val tv) ≤ᵇ B) ds ≡ true →
  all (λ tv → sizeᵛ u (proj₂ tv) ≤ᵇ B) (resolve anchor ds) ≡ true
resolve-caps B anchor []                  h = refl
resolve-caps {u = u} B anchor ((after w , v) ∷ r) h
  with ∧-true (sizeᵛ u v ≤ᵇ B)
              (all (λ tv → sizeᵛ u (Timed.val tv) ≤ᵇ B) r) h
... | h1 , h2 = ∧-intro h1 (resolve-caps B (anchor + suc w) r h2)

resolve-wid-data : ∀ {n} {Γ : Ctx n} {u} (W : ℕ) (sl : Slots Γ) → T (isData u) →
  (ps : List (Tick × Val Γ u)) →
  all (λ tv → pWᵛ n sl u (proj₂ tv) ≤ᵇ W) ps ≡ true
resolve-wid-data W sl ok []             = refl
resolve-wid-data {n = n} {u = u} W sl ok ((tk , v) ∷ ps) =
  ∧-intro (subst (λ x → (x ≤ᵇ W) ≡ true) (sym (pWᵛ-data n sl u ok v)) refl)
          (resolve-wid-data W sl ok ps)

-- so a data slot's resolved tail is free on the Ψ axis too, exactly as
-- resolve-wid-data gives it free on the width axis -- and that is the whole
-- fnCapLive half of a fresh cold's live entry, which no caps receipt can ever
-- supply because capsOK? has no Ψ conjunct.
resolve-fnCap-data : ∀ {n} {Γ : Ctx n} (Ψ : ℕ) (u : Ty) → T (isData u) →
  (ps : List (Tick × Val Γ u)) →
  all (λ tv → fnCapᵛ u (proj₂ tv) ≤ᵇ Ψ) ps ≡ true
resolve-fnCap-data Ψ u ok []             = refl
resolve-fnCap-data Ψ u ok ((tk , v) ∷ ps) =
  ∧-intro (subst (λ x → (x ≤ᵇ Ψ) ≡ true) (sym (fnCapᵛ-data u ok v)) refl)
          (resolve-fnCap-data Ψ u ok ps)

-- a fresh cold's live entry, bounded on both halves
capsOK?-addLive : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (l : LiveSource Γ) (sched : Sched Γ) (st : EvalSt e) →
  boundedLive (Caps.cSize c) l ≡ true →
  widLive (Caps.cWid c) (Sched.slots sched) l ≡ true →
  closLive c (Sched.slots sched) l ≡ true →
  capsOK? c sched st ≡ true →
  capsOK? c (record sched { live = l ∷ Sched.live sched }) st ≡ true
capsOK?-addLive {Γ = Γ} c l sched st bl wl cl inv =
    ∧-intro (∧-intro (∧-intro bl (proj₁ hL)) (proj₂ hL))
    (∧-intro h1
    (∧-intro (∧-intro wl h2)
    (∧-intro h3 (∧-intro h4
    (∧-intro h5 (∧-intro cl h6))))))
  where
  P  = capsOK?-parts c sched st inv
  h0 = proj₁ P
  hL = ∧-true (all (boundedLive {Γ = Γ} (Caps.cSize c)) (Sched.live sched))
              (all (λ kv → boundedNode (Caps.cSize c) (proj₂ kv)) (EvalSt.nodes st))
              h0
  h1 = proj₁ (proj₂ P)
  h2 = proj₁ (proj₂ (proj₂ P))
  h3 = proj₁ (proj₂ (proj₂ (proj₂ P)))
  h4 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ P))))
  h5 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ P)))))
  h6 = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ P)))))

-- AND THE SAME STEP BACKWARDS, which costs no hypothesis at all: every
-- capsOK? conjunct that reads `live` reads it through an `all`, so the head
-- comes off for free, and `record sched { live = _ }` leaves `Sched.slots`
-- definitionally alone, so the widLive conjunct does not move.
--
-- Owed by a cold scripted subscribe, where the two INV? steps do not meet:
-- the register step wants its caps receipt at the schedule it registers
-- under -- the PRE-addLive one -- while the clause is handed a receipt at the
-- POST-addLive schedule, and capsOK? genuinely reads `Sched.live`.  Its
-- absence is why that shape was split off as its own leaf rather than ground.
capsOK?-dropLive : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (l : LiveSource Γ) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c (record sched { live = l ∷ Sched.live sched }) st ≡ true →
  capsOK? c sched st ≡ true
capsOK?-dropLive {Γ = Γ} c l sched st ok =
    ∧-intro (∧-intro (proj₂ hL) (proj₂ hB))
    (∧-intro h1
    (∧-intro (proj₂ hW)
    (∧-intro h3 (∧-intro h4
    (∧-intro h5 (proj₂ hCL))))))
  where
  sched′ = record sched { live = l ∷ Sched.live sched }
  P  = capsOK?-parts c sched′ st ok
  hB = ∧-true (all (boundedLive {Γ = Γ} (Caps.cSize c)) (l ∷ Sched.live sched))
              (all (λ kv → boundedNode (Caps.cSize c) (proj₂ kv)) (EvalSt.nodes st))
              (proj₁ P)
  hL = ∧-true (boundedLive (Caps.cSize c) l)
              (all (boundedLive {Γ = Γ} (Caps.cSize c)) (Sched.live sched))
              (proj₁ hB)
  hW = ∧-true (widLive (Caps.cWid c) (Sched.slots sched) l)
              (all (widLive (Caps.cWid c) (Sched.slots sched))
                   (Sched.live sched))
              (proj₁ (proj₂ (proj₂ P)))
  h1 = proj₁ (proj₂ P)
  h3 = proj₁ (proj₂ (proj₂ (proj₂ P)))
  h4 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ P))))
  h5 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ P)))))
  h6 = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ P)))))
  hCL = ∧-true (closLive c (Sched.slots sched) l)
               (all (closLive c (Sched.slots sched))
                    (Sched.live sched))
               h6

-- and the head of the same conjunct, which the drop throws away and a fresh
-- cold subscribe then needs: the entry it just prepended is bounded, and the
-- receipt it is handed already says so, so this costs nothing either.
capsOK?-liveHead : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (l : LiveSource Γ) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c (record sched { live = l ∷ Sched.live sched }) st ≡ true →
  boundedLive (Caps.cSize c) l ≡ true
capsOK?-liveHead {Γ = Γ} c l sched st ok =
  proj₁ (∧-true (boundedLive (Caps.cSize c) l)
                (all (boundedLive {Γ = Γ} (Caps.cSize c)) (Sched.live sched))
                (proj₁ (∧-true
                  (all (boundedLive {Γ = Γ} (Caps.cSize c))
                       (l ∷ Sched.live sched))
                  (all (λ kv → boundedNode (Caps.cSize c) (proj₂ kv)) (EvalSt.nodes st))
                  (proj₁ (capsOK?-parts c
                    (record sched { live = l ∷ Sched.live sched }) st ok)))))

-- and cSize only ever grows with j, which is what widens a slot bound
-- stated at `c` to the level a clause reports at
cSize≤frameStep : ∀ (c : Caps) (j : ℕ) → 2 ≤ Caps.cSize c →
  Caps.cSize c ≤ Caps.cSize (frameStep j c)
cSize≤frameStep c j h =
  iterSize-infl (Caps.cSize c) (≤-trans (s≤s z≤n) h) j (Caps.cSize c)

-- and the width axis of the same, which is what widens the slot
-- telescope's parked-width half to the level a clause reports at
cWid≤frameStep : ∀ (c : Caps) (j : ℕ) → 2 ≤ Caps.cSize c →
  Caps.cWid c ≤ Caps.cWid (frameStep j c)
cWid≤frameStep c j h = iterFold-infl (Caps.cSize c) h j (Caps.cWid c)

------------------------------------------------------------------
-- AND THE TWO CLAUSES THAT DO BUILD VALUES, GROUND — over the size
-- receipt and the width bridge above.
--
-- map-f and scan-f are the only clauses of stepFrame that call
-- `applyFn`, and `applyFn fn v` is `evalWith fn (v ∷ [])`: not a
-- substitution but an EVALUATION.  That distinction is the whole
-- content of these two statements, and it is why they are not
-- one-liners off size-subΘᵉ the way `sizeStep`'s comment reads.
--
-- WHAT sizeStep IS READ OFF, AND WHAT applyFn ACTUALLY DOES.  sizeStep
-- S s = S * suc (2 * s) is exactly size-subΘᵉ's bound, `sizeᵉ f * suc
-- (2 * V)` — the cost of PLUGGING an env of size V into a template of
-- size f.  evalWith does more than plug: its `caseᵗ` clause evaluates
-- the scrutinee and extends the environment WITH THE RESULTING VALUE,
-- so the env a later `strmᵗ` closes over is not the caller's env.  The
-- shape that exploits it:
--
--     caseᵗ (inlᵗ (pairᵗ x x)) (caseᵗ (inlᵗ (pairᵗ v₀ v₀)) (… ) _) _
--
-- nested d deep, each level pairing the binding introduced by the level
-- above with itself.  `sizeᵗ fn` is Θ(d); the value it computes from an
-- input of size 1 is Θ(2 ^ d).  So NO j′ = 1 works: one sizeStep is
-- linear in the cap and the clause is exponential in the step
-- function's syntax.  .Measures' own bounds say the same thing without
-- the counterexample — evalWith-size is `(2 + 2 * V) ^ (3 ^ sizeᵗ fn)`,
-- a tower, and evalWith-sharp only moves the exponent to
-- `3 ^ caseWᵗ fn`.
--
-- AND THAT IS WHAT applyFn-iterSize PAYS, PROVEN: the receipt is one
-- fold per node of the STEP FUNCTION, `sizeᵗ fn`, with the payload's
-- own size as the seed — Eval-Growth-Probe §6 gates it at the worst
-- admissible base S = 1 on the very family above.  What is NOT true is
-- that the receipt is one fold per FRAME.
--
-- SO THE COST MOVES, IT DOES NOT VANISH, AND IT LANDS ON THE PER-FRAME
-- RECEIPT `fCharge` the level walk reads.  A single map-f frame over a
-- case-nested step function needs a j′ exponential in cSize, and
-- `fCharge S W J = suc (suc (widAt S W J) * suc (sizeAt S J))` is
-- polynomial in the level's own fields — so on that program the receipt
-- is short by an exponential.  This is flagged rather than patched, but
-- it is no longer a design ruling about a closed count: the count is a
-- WALK now, so a bigger per-frame receipt is a change to `fLvl`
-- (Rx.Evaluator) and everything above it follows by the same
-- monotonicity lemmas.  The two
-- statements below are stated so that the difficulty has a NAME and a
-- boundary — no state, no recursion, no mutual induction, just
-- applyFn — instead of being buried in the hub clause
------------------------------------------------------------------

-- ONE map-f FRAME, GROUND AND SYNTAX-COUNTED.  Every payload is mapped
-- independently, so nothing composes and the whole list costs one
-- clause's worth of folds: applyFn-iterSize reads the SIZE receipt off
-- the step function's syntax with the payload's own size as the seed,
-- and applyFn-iterFold reads the WIDTH receipt off the same syntax with
-- the payload's own WIDTH as the seed.  j′ = suc (sizeᵗ fn) — one fold
-- per node of the step function, and ONE more that absorbs the seed
mapFrame-caps : ∀ {n} {Γ : Ctx n} {s u} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (fn : Fn Γ [] [] [] s u) (vals : List (Val Γ s)) →
  2 ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  (sizeᵗ fn ≤ᵇ Caps.cSize (frameStep j c)) ≡ true →
  all (valCaps? (frameStep j c) sl s) vals ≡ true →
  Σ ℕ λ j′ →
    all (valCaps? (frameStep (j + j′) c) sl u) (map (applyFn fn) vals) ≡ true
mapFrame-caps {Γ = Γ} {s = s} {u = u} c j sl fn vals 2≤S slC fS vC =
  suc a , go vals vC
  where
  S   = Caps.cSize c
  W   = Caps.cWid c
  B   = Caps.cSize (frameStep j c)
  V   = Caps.cWid (frameStep j c)
  a   = sizeᵗ fn
  M   = suc V
  1≤S = ≤-trans (s≤s z≤n) 2≤S
  slW : SlotWid sl M
  slW = SlotWid-mono sl (s≤s (iterFold-infl S 2≤S j W))
                     (slotsCaps?-slotWid S W sl slC)
  sz : (v : Val Γ s) → valCaps? (frameStep j c) sl s v ≡ true →
       sizeᵛ u (applyFn fn v) ≤ Caps.cSize (frameStep (j + suc a) c)
  sz v hv =
    ≤-trans (≤-trans (applyFn-iterSize S B 1≤S fn v
                        (≤ᵇ⇒≤ (sizeᵛ s v) B
                           (T-to (valCaps?-size (frameStep j c) sl s v hv))))
                     (≤-reflexive (sym (iterSize-+ S j a S))))
            (iterSize-mono-count S S 1≤S (+-monoʳ-≤ j (n≤1+n a)))
  wd : (v : Val Γ s) → valCaps? (frameStep j c) sl s v ≡ true →
       pWᵛ _ sl u (applyFn fn v) ≤ Caps.cWid (frameStep (j + suc a) c)
  wd v hv =
    wid-lift c j a 2≤S
      (applyFn-iterFold S M 2≤S (s≤s z≤n) sl slW fn v
        (≤-trans (≤ᵇ⇒≤ (pWᵛ _ sl s v) V
                   (T-to (valCaps?-wid (frameStep j c) sl s v hv)))
                 (n≤1+n V)))
  go : (vs : List (Val Γ s)) → all (valCaps? (frameStep j c) sl s) vs ≡ true →
       all (valCaps? (frameStep (j + suc a) c) sl u)
           (map (applyFn fn) vs) ≡ true
  go []       h = refl
  go (v ∷ vs) h
    with ∧-true (valCaps? (frameStep j c) sl s v)
                (all (valCaps? (frameStep j c) sl s) vs) h
  ... | hd , tl =
    ∧-intro (∧-intro (T⇒≡true _ (≤⇒≤ᵇ (sz v hd))) (T⇒≡true _ (≤⇒≤ᵇ (wd v hd))))
            (go vs tl)

-- THE CLOSURE READING IS THE CAPS READING TIMES THE CAP, AND ONE
-- LEVEL PAYS FOR THAT FACTOR.  A value's key is read THROUGH the slot
-- telescope, the telescope is capped by the slot premise, so the key
-- is at most the size cap times the value's PLAIN size -- and a level
-- multiplies the size field by roughly twice itself.  So any list the
-- caps face has already priced at a level is priced for closure one
-- level up, whatever produced it.
--
-- SO NO HEAD OWES A CLOSURE LAW OF ITS OWN, WHICH IS THE WHOLE REASON
-- THIS IS STATED OVER A LIST AND NOT OVER A FRAME.  A per-head law has
-- to re-derive the rebuilt value from the ARGUMENT's reading, and the
-- two rebuilding heads make that false: both factors are the cap and
-- the rebuild is their product.  Reading the OUTPUT's own size instead
-- needs nothing about how it was made, so the walk spends this once,
-- at whatever level the caps face left the values it is carrying.
--
-- AND THE SLOT PREMISE IS WHAT MAKES IT TRUE.  With no ceiling on the
-- telescope a slot definition is free, the ratio between the two
-- readings is unbounded in the slot COUNT, and no number of levels
-- pays for the rebuild.
-- REFUTED: `Refuted.Nest-Clos-Stratified` -- that ratio, with the
--   ceiling removed.
-- REFUTED: `Refuted.Step-Frame-Clos` -- the per-head form, cap-free,
--   at a frame function no hypothesis bounds.
-- REFUTED: `Refuted.Step-Frame-Clos-Level` -- the per-head form at ONE
--   level with every caller premise discharged: a template of `S²`
--   copies applied to an argument of closure `S²`, both inside the
--   level-one cap, whose product outruns the level-two cap.
-- RECOVERY: `git show 35762e6` restores the two per-head probes, whose
--   harness reaches a PARKED `mergeAll` queue by running a concurrency
--   of one whose first lane stays open on a hot slot -- the expensive
--   half of instantiating anything about a drain.
clos-lift : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (vs : List (Val Γ u)) →
  2 ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  all (λ v → sizeᵛ u v ≤ᵇ Caps.cSize (frameStep j c)) vs ≡ true →
  all (nestClosOK?ᵛ (frameStep (suc j) c) sl u) vs ≡ true
clos-lift {Γ = Γ} {u = u} c j sl vs 2≤S slC vC =
  all-impl (λ v → sizeᵛ u v ≤ᵇ Caps.cSize (frameStep j c))
           (nestClosOK?ᵛ (frameStep (suc j) c) sl u)
           (λ v hv → closSizeᵛ-OK (frameStep (suc j) c) sl u v (sz v hv))
           vs vC
  where
  S   = Caps.cSize c
  B   = Caps.cSize (frameStep j c)
  1≤S = ≤-trans (s≤s z≤n) 2≤S
  σ≤S : ∀ i → slotClos sl i ≤ S
  σ≤S i = slotsCaps?-clos S (Caps.cWid c) sl i slC
  eqStep : Caps.cSize (frameStep (suc j) c) ≡ S * suc (2 * B)
  eqStep = iterSize-suc S j S
  B≤ : B ≤ suc (2 * B)
  B≤ = ≤-trans (m≤m+n B (B + 0)) (n≤1+n (B + (B + 0)))
  sz : (v : Val Γ u) → (sizeᵛ u v ≤ᵇ B) ≡ true →
       closSizeᵛ (slotClos sl) u v ≤ Caps.cSize (frameStep (suc j) c)
  sz v hv =
    ≤-trans (≤-trans (closSizeᵛ≤mul (slotClos sl) S σ≤S 1≤S u v)
                     (*-monoʳ-≤ S (≤-trans (≤ᵇ⇒≤ (sizeᵛ u v) B (T-to hv)) B≤)))
            (≤-reflexive (sym eqStep))

-- ONE scan-f FRAME'S SIZE LADDER.  Here the folds DO compose — scanVals
-- threads the accumulator, so payload i is `applyFn` applied i times —
-- and each rung costs one PAIRING plus one step function: the arriving
-- payload is paired with the stored accumulator before the step runs,
-- which is exactly one sizeStep, so a rung is `suc (sizeᵗ fn)` folds and
-- the whole list is `length vals` of them
scanVals-size : ∀ {n} {Γ : Ctx n} {s u} (S B : ℕ) → 2 ≤ S →
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac0 : Val Γ u) (vals : List (Val Γ s)) →
  sizeᵛ u ac0 ≤ B →
  all (λ v → sizeᵛ s v ≤ᵇ B) vals ≡ true →
  (all (λ w → sizeᵛ u w ≤ᵇ iterSize S (length vals * suc (sizeᵗ fn)) B)
       (proj₁ (scanVals fn ac0 vals)) ≡ true)
  × (sizeᵛ u (proj₂ (scanVals fn ac0 vals))
       ≤ iterSize S (length vals * suc (sizeᵗ fn)) B)
scanVals-size S B hS fn ac0 []       hac0 h = refl , hac0
scanVals-size {s = s} {u = u} S B hS fn ac0 (v ∷ vs) hac0 h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ HEAD)) (proj₁ IH′) , proj₂ IH′
  where
  F    = sizeᵗ fn
  B₁   = iterSize S (suc F) B
  1≤S  = ≤-trans (s≤s z≤n) hS
  split = ∧-true (sizeᵛ s v ≤ᵇ B) (all (λ x → sizeᵛ s x ≤ᵇ B) vs) h
  hv   : sizeᵛ s v ≤ B
  hv   = ≤ᵇ⇒≤ (sizeᵛ s v) B (T-to (proj₁ split))
  hac0′ : sizeᵛ u (applyFn fn (ac0 , v)) ≤ B₁
  hac0′ = applyFn-iterSize S (sizeStep S B) 1≤S fn (ac0 , v)
            (≤-trans (s≤s (+-mono-≤ hac0 hv)) (pair≤sizeStep S B 1≤S))
  hvs  = all-impl (λ x → sizeᵛ s x ≤ᵇ B) (λ x → sizeᵛ s x ≤ᵇ B₁)
           (λ x → ≤ᵇ-widen (sizeᵛ s x) (iterSize-infl S 1≤S (suc F) B))
           vs (proj₂ split)
  IH   = scanVals-size S B₁ hS fn (applyFn fn (ac0 , v)) vs hac0′ hvs
  eq   : iterSize S (length vs * suc F) B₁
           ≡ iterSize S (suc F + length vs * suc F) B
  eq   = sym (iterSize-+ S (suc F) (length vs * suc F) B)
  IH′  = subst (λ X →
                  (all (λ w → sizeᵛ u w ≤ᵇ X)
                       (proj₁ (scanVals fn (applyFn fn (ac0 , v)) vs)) ≡ true)
                  × (sizeᵛ u (proj₂ (scanVals fn (applyFn fn (ac0 , v)) vs)) ≤ X))
               eq IH
  HEAD : sizeᵛ u (applyFn fn (ac0 , v))
           ≤ iterSize S (suc F + length vs * suc F) B
  HEAD = ≤-trans hac0′
           (subst (B₁ ≤_) eq (iterSize-infl S 1≤S (length vs * suc F) B₁))

-- the same ladder ON THE WIDTH AXIS, and at the SAME count: a rung
-- pairs the arriving payload with the stored accumulator (one fold)
-- and steps it (one per node of the step function), with the widths
-- entering as SEEDS
scanVals-wid : ∀ {n} {Γ : Ctx n} {s u} (S M : ℕ) → 2 ≤ S → 1 ≤ M →
  (sl : Slots Γ) → SlotWid sl M →
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac0 : Val Γ u) (vals : List (Val Γ s)) →
  pWᵛ n sl u ac0 ≤ M →
  all (λ v → pWᵛ n sl s v ≤ᵇ M) vals ≡ true →
  (all (λ w → pWᵛ n sl u w ≤ᵇ iterFold S (length vals * suc (sizeᵗ fn)) M)
       (proj₁ (scanVals fn ac0 vals)) ≡ true)
  × (pWᵛ n sl u (proj₂ (scanVals fn ac0 vals))
       ≤ iterFold S (length vals * suc (sizeᵗ fn)) M)
scanVals-wid S M hS hM sl hI fn ac0 []       hac0 h = refl , hac0
scanVals-wid {n = n} {s = s} {u = u} S M hS hM sl hI fn ac0 (v ∷ vs) hac0 h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ HEAD)) (proj₁ IH′) , proj₂ IH′
  where
  F    = sizeᵗ fn
  M₁   = iterFold S (suc F) M
  split = ∧-true (pWᵛ n sl s v ≤ᵇ M) (all (λ x → pWᵛ n sl s x ≤ᵇ M) vs) h
  hv   : pWᵛ n sl s v ≤ M
  hv   = ≤ᵇ⇒≤ (pWᵛ n sl s v) M (T-to (proj₁ split))
  hac0′ : pWᵛ n sl u (applyFn fn (ac0 , v)) ≤ M₁
  hac0′ = ≤-trans (applyFn-iterFold S M hS hM sl hI fn (ac0 , v)
                     (≤-trans (pWᵛ-pair sl u s ac0 v) (⊔-lub hac0 hv)))
                  (iterFold-mono-count S M hS (n≤1+n F))
  hI₁ : SlotWid sl M₁
  hI₁ = SlotWid-mono sl (iterFold-infl S hS (suc F) M) hI
  hvs  = all-impl (λ x → pWᵛ n sl s x ≤ᵇ M) (λ x → pWᵛ n sl s x ≤ᵇ M₁)
           (λ x → ≤ᵇ-widen (pWᵛ n sl s x) (iterFold-infl S hS (suc F) M))
           vs (proj₂ split)
  IH   = scanVals-wid S M₁ hS (≤-trans hM (iterFold-infl S hS (suc F) M))
           sl hI₁ fn (applyFn fn (ac0 , v)) vs hac0′ hvs
  eq   : iterFold S (length vs * suc F) M₁
           ≡ iterFold S (suc F + length vs * suc F) M
  eq   = sym (iterFold-+ S (suc F) (length vs * suc F) M)
  IH′  = subst (λ X →
                  (all (λ w → pWᵛ n sl u w ≤ᵇ X)
                       (proj₁ (scanVals fn (applyFn fn (ac0 , v)) vs)) ≡ true)
                  × (pWᵛ n sl u (proj₂ (scanVals fn (applyFn fn (ac0 , v)) vs)) ≤ X))
               eq IH
  HEAD : pWᵛ n sl u (applyFn fn (ac0 , v))
           ≤ iterFold S (suc F + length vs * suc F) M
  HEAD = ≤-trans hac0′
           (subst (M₁ ≤_) eq (iterFold-infl S hS (length vs * suc F) M₁))

-- the two ladders' conclusions are read off one list, so they are
-- joined before the widening
all-∧ : ∀ {A : Set} (p q : A → Bool) (xs : List A) →
  all p xs ≡ true → all q xs ≡ true → all (λ x → p x ∧ q x) xs ≡ true
all-∧ p q []       hp hq = refl
all-∧ p q (x ∷ xs) hp hq =
  ∧-intro (∧-intro (proj₁ (∧-true (p x) (all p xs) hp))
                   (proj₁ (∧-true (q x) (all q xs) hq)))
          (all-∧ p q xs (proj₂ (∧-true (p x) (all p xs) hp))
                        (proj₂ (∧-true (q x) (all q xs) hq)))

-- ONE scan-f FRAME, GROUND AND SYNTAX-COUNTED.  The accumulator has to
-- come back bounded too, because it is reinstalled.
-- j′ = suc (length vals * suc (sizeᵗ fn))
scanFrame-caps : ∀ {n} {Γ : Ctx n} {s u} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac0 : Val Γ u) (vals : List (Val Γ s)) →
  2 ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  (sizeᵗ fn ≤ᵇ Caps.cSize (frameStep j c)) ≡ true →
  valCaps? (frameStep j c) sl u ac0 ≡ true →
  all (valCaps? (frameStep j c) sl s) vals ≡ true →
  Σ ℕ λ j′ →
    (all (valCaps? (frameStep (j + j′) c) sl u)
         (proj₁ (scanVals fn ac0 vals)) ≡ true)
    × (valCaps? (frameStep (j + j′) c) sl u (proj₂ (scanVals fn ac0 vals)) ≡ true)
scanFrame-caps {n = n} {Γ = Γ} {s = s} {u = u} c j sl fn ac0 vals 2≤S slC fS aC vC =
  suc a
    , all-impl (λ w → (sizeᵛ u w ≤ᵇ iterSize S a B) ∧ (pWᵛ n sl u w ≤ᵇ iterFold S a M))
               (valCaps? (frameStep (j + suc a) c) sl u)
               (λ w hw → mk w (proj₁ (∧-true (sizeᵛ u w ≤ᵇ iterSize S a B)
                                             (pWᵛ n sl u w ≤ᵇ iterFold S a M) hw))
                              (proj₂ (∧-true (sizeᵛ u w ≤ᵇ iterSize S a B)
                                             (pWᵛ n sl u w ≤ᵇ iterFold S a M) hw)))
               (proj₁ (scanVals fn ac0 vals))
               (all-∧ (λ w → sizeᵛ u w ≤ᵇ iterSize S a B)
                      (λ w → pWᵛ n sl u w ≤ᵇ iterFold S a M)
                      (proj₁ (scanVals fn ac0 vals)) (proj₁ SV) (proj₁ SW))
    , mk (proj₂ (scanVals fn ac0 vals))
         (T⇒≡true _ (≤⇒≤ᵇ (proj₂ SV))) (T⇒≡true _ (≤⇒≤ᵇ (proj₂ SW)))
  where
  S   = Caps.cSize c
  W   = Caps.cWid c
  B   = Caps.cSize (frameStep j c)
  V   = Caps.cWid (frameStep j c)
  a   = length vals * suc (sizeᵗ fn)
  M   = suc V
  1≤S = ≤-trans (s≤s z≤n) 2≤S
  slW : SlotWid sl M
  slW = SlotWid-mono sl (s≤s (iterFold-infl S 2≤S j W))
                     (slotsCaps?-slotWid S W sl slC)
  mk : (w : Val Γ u) → (sizeᵛ u w ≤ᵇ iterSize S a B) ≡ true →
       (pWᵛ n sl u w ≤ᵇ iterFold S a M) ≡ true →
       valCaps? (frameStep (j + suc a) c) sl u w ≡ true
  mk w h1 h2 =
    ∧-intro
      (T⇒≡true _ (≤⇒≤ᵇ
        (≤-trans (≤-trans (≤ᵇ⇒≤ (sizeᵛ u w) (iterSize S a B) (T-to h1))
                          (≤-reflexive (sym (iterSize-+ S j a S))))
                 (iterSize-mono-count S S 1≤S (+-monoʳ-≤ j (n≤1+n a))))))
      (T⇒≡true _ (≤⇒≤ᵇ
        (wid-lift c j a 2≤S (≤ᵇ⇒≤ (pWᵛ n sl u w) (iterFold S a M) (T-to h2)))))
  SV = scanVals-size S B 2≤S fn ac0 vals
         (≤ᵇ⇒≤ (sizeᵛ u ac0) B
            (T-to (valCaps?-size (frameStep j c) sl u ac0 aC)))
         (all-impl (valCaps? (frameStep j c) sl s) (λ v → sizeᵛ s v ≤ᵇ B)
            (λ v → valCaps?-size (frameStep j c) sl s v) vals vC)
  SW = scanVals-wid S M 2≤S (s≤s z≤n) sl slW fn ac0 vals
         (≤-trans (≤ᵇ⇒≤ (pWᵛ n sl u ac0) V
                    (T-to (valCaps?-wid (frameStep j c) sl u ac0 aC)))
                  (n≤1+n V))
         (all-impl (valCaps? (frameStep j c) sl s) (λ v → pWᵛ n sl s v ≤ᵇ M)
            (λ v hv → ≤ᵇ-widen (pWᵛ n sl s v) (n≤1+n V)
                        (valCaps?-wid (frameStep j c) sl s v hv))
            vals vC)

------------------------------------------------------------------
-- stepFrame-caps, GROUND.  Five clauses over the four leaves above and
-- the two value postulates; the only arithmetic is widening the entry
-- invariant to the reported level.
--
-- ONE HYPOTHESIS HAD TO BE ADDED, and it was missing rather than
-- optional: `suc (pathLen κ) ≤ cSize (frameStep j c)`.  The thru-outer
-- clause hands κ to thruWalk-caps, which requires exactly that conjunct,
-- and the postulated face carried only `pathSz? … κ` — which says every
-- PROPER SUFFIX of κ is short, and says nothing about κ itself.  The
-- caller already has it: foldPath-caps splits `pathSz? B (f ↠ p)` into
-- `frameSz? B f`, `suc (pathLen p) ≤ᵇ B` and `pathSz? B p`, and was
-- discarding the middle one.  So the repair costs the call site one
-- `≤ᵇ⇒≤` and nothing else — no new obligation anywhere in the tree
------------------------------------------------------------------

-- the six clauses where the node lookup misses or mismatches: the
-- evaluator emits nothing and touches nothing
-- THE RECEIPT ARITHMETIC, and it is one `*-mono-≤`: fCharge's two
-- factors ARE `suc (cWid (frameStep j c))` and `suc (cSize (frameStep
-- j c))` by refl, so the scan row lands exactly and the map row lands
-- with the width factor spare.  It sits HERE, ahead of the frame
-- clauses, because they now report their own receipts and the face
-- below spends the same two lemmas afterwards
face-charge : ∀ (c : Caps) (j w a : ℕ) →
  w ≤ suc (Caps.cWid (frameStep j c)) →
  a ≤ Caps.cSize (frameStep j c) →
  suc (w * suc a) ≤ fCharge (Caps.cSize c) (Caps.cWid c) j
face-charge c j w a hw ha = s≤s (*-mono-≤ hw (s≤s ha))

face-charge1 : ∀ (c : Caps) (j a : ℕ) →
  a ≤ Caps.cSize (frameStep j c) →
  suc a ≤ fCharge (Caps.cSize c) (Caps.cWid c) j
face-charge1 c j a ha =
  ≤-trans (s≤s (≤-trans (n≤1+n a) (m≤m+n (suc a) 0)))
          (face-charge c j 1 a (s≤s z≤n) ha)

stepFrame-zero-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (j : ℕ) (u : Ty) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? (frameStep j c) sched st ≡ true →
  Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c) sched st ≡ true)
     × (all (valCaps? (frameStep (j + j′) c) sl u) [] ≡ true)
     × (all (eventCaps? {n = n} {Γ = Γ} {u = t} (frameStep (j + j′) c) sl) [] ≡ true)
     -- and it charges NOTHING, which the frame face needs stated rather
     -- than re-derived: its consumer reports in `fLvlD` at an abstract
     -- depth, where only a receipt-shaped bound goes through
     × (j′ ≤ fCharge (Caps.cSize c) (Caps.cWid c) j)
stepFrame-zero-caps c j u sl sched st inv =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , refl , refl , z≤n

stepFrame-scan-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (c : Caps) (j : ℕ) (g : Gas) (id : Id) (now : Tick)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  Sched.slots sched ≡ sl →
  capsOK? (frameStep j c) sched st ≡ true →
  frameSz? (Caps.cSize (frameStep j c)) (scan-f fn nid) ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  -- THE PAYLOAD'S CARDINALITY, and it has to be an argument.  A scan's
  -- receipt is a PRODUCT — one fold per payload per node of the step
  -- function — so `fCharge`'s width factor is what pays for the payload
  -- count, and nothing in `all (valCaps? …)` bounds it.  The caller
  -- already computes this fact for its own payload ledger and used to
  -- drop it here
  length vals ≤ suc (Caps.cWid (frameStep j c)) →
  all (valCaps? (frameStep j c) sl s) vals ≡ true →
  let r = stepFrame g id now (scan-f fn nid) κ vals fin sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
                ≡ true)
     × (all (valCaps? (frameStep (j + j′) c) sl u)
            (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ r)) ≡ true)
     -- the receipt, which the eight clauses cannot leave to reduction:
     -- seven of them charge nothing and one charges the product, so the
     -- bound is invisible at the call site unless it is reported
     × (j′ ≤ fCharge (Caps.cSize c) (Caps.cWid c) j)
stepFrame-scan-caps {s = s} {u = u} c j g id now fn nid κ vals fin sl sched st
                    2≤S slC slEq inv fS pS vL vC
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-caps (frameStep j c) (Sched.slots sched) nid (EvalSt.nodes st)
         (capsOK?-nodeSz (frameStep j c) sched st inv)
         (capsOK?-nodeWid (frameStep j c) sched st inv)
... | nothing                | _ = stepFrame-zero-caps c j u sl sched st inv
... | just (take-st _)       | _ = stepFrame-zero-caps c j u sl sched st inv
... | just (mergeAll-st _ _ _ _)    | _ = stepFrame-zero-caps c j u sl sched st inv
... | just (switch-st _ _)   | _ = stepFrame-zero-caps c j u sl sched st inv
... | just (exhaust-st _ _)  | _ = stepFrame-zero-caps c j u sl sched st inv
... | just (scan-st {w} ac)  | nb with w ≟ᵗ u
...   | no _    = stepFrame-zero-caps c j u sl sched st inv
...   | yes refl =
  j′ , capsOK?-setNode (frameStep (j + j′) c) nid
         (scan-st (proj₂ run)) sched st
         (valCaps?-size (frameStep (j + j′) c) sl _ (proj₂ run) (proj₂ (proj₂ SC)))
         refl
         (subst (λ x → widNode (Caps.cWid (frameStep (j + j′) c)) x
                         (scan-st (proj₂ run)) ≡ true)
                (sym slEq)
                (valCaps?-wid (frameStep (j + j′) c) sl _ (proj₂ run)
                   (proj₂ (proj₂ SC))))
         (capsOK?-mono (frameStep j c) (frameStep (j + j′) c) sched st
            (frameStep-⊑-+ c 2≤S j j′) inv)
     , proj₁ (proj₂ SC)
     , refl
     -- ONE FOLD PER PAYLOAD PER NODE of the step function, and that is
     -- exactly `fCharge`'s product: `vL` pays the width factor and
     -- `frameSz?`'s own size conjunct pays the other
     , face-charge c j (length vals) (sizeᵗ fn) vL
         (≤ᵇ⇒≤ (sizeᵗ fn) (Caps.cSize (frameStep j c)) (T-to fS))
  where
  run = scanVals fn ac vals
  SC  = scanFrame-caps c j sl fn ac vals 2≤S slC fS
          (∧-intro (proj₁ nb)
                   (subst (λ x → (pWᵛ _ x u ac ≤ᵇ Caps.cWid (frameStep j c)) ≡ true)
                          slEq (proj₂ nb)))
          vC
  j′  = proj₁ SC

------------------------------------------------------------------
-- THE FRAME FACE, GROUND ON FIVE CLAUSE PIECES — three proven here,
-- two named and postulated.  See the forward declaration above for
-- what the face adds to `stepFrame-caps` and why it cannot be got by
-- strengthening it.
--
-- THE THREE LENGTH REPORTS are the whole of (b) on the value-shaping
-- frames, and each is one line: map emits one payload per input
-- (length-map), scan emits one per input (scanVals-len), take emits a
-- prefix (takeVals-len, lifted over the node dispatch).  Nothing here
-- widens a width — the OUTPUT width is the INPUT width, and the one
-- monotonicity is `cWid (frameStep j c) ≤ cWid (frameStep (j + j′) c)`.
------------------------------------------------------------------

-- scan emits exactly one payload per input
scanVals-len : ∀ {n} {Γ : Ctx n} {s u} (fn : Fn Γ [] [] [] (u ×ᵗ s) u)
  (ac : Val Γ u) (vs : List (Val Γ s)) →
  length (proj₁ (scanVals fn ac vs)) ≡ length vs
scanVals-len fn ac []       = refl
scanVals-len fn ac (v ∷ vs) = cong suc (scanVals-len fn (applyFn fn (ac , v)) vs)

-- take emits a prefix
takeVals-len : ∀ {n} {Γ : Ctx n} {s} (k : ℕ) (vs : List (Val Γ s)) →
  length (proj₁ (takeVals k vs)) ≤ length vs
takeVals-len zero          vs       = z≤n
takeVals-len (suc k)       []       = z≤n
takeVals-len (suc zero)    (v ∷ vs) = s≤s z≤n
takeVals-len (suc (suc k)) (v ∷ vs) = s≤s (takeVals-len (suc k) vs)

-- and the take-f dispatch either passes that prefix or emits nothing,
-- on every node the evaluator's catch-all covers
takeDispatch-len : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (mns : Maybe (NodeState Γ)) →
  length (proj₁ (takeDispatch {t = t} nid vals fin sched st mns)) ≤ length vals
takeDispatch-len nid vals fin sched st (just (take-st k))
  with proj₂ (proj₂ (takeVals k vals))
... | true  = takeVals-len k vals
... | false = takeVals-len k vals
takeDispatch-len nid vals fin sched st nothing                  = z≤n
takeDispatch-len nid vals fin sched st (just (scan-st _))       = z≤n
takeDispatch-len nid vals fin sched st (just (mergeAll-st _ _ _ _))    = z≤n
takeDispatch-len nid vals fin sched st (just (switch-st _ _))   = z≤n
takeDispatch-len nid vals fin sched st (just (exhaust-st _ _))  = z≤n

-- valsCaps?'s two halves, read back out: the payload ledger and the
-- width the receipt bound is charged against
valsCaps?-parts : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ)
  (vs : List (Val Γ u)) → valsCaps? c sl vs ≡ true →
  (all (valCaps? c sl u) vs ≡ true) × (length vs ≤ suc (Caps.cWid c))
valsCaps?-parts {u = u} c sl vs h
  with ∧-true (all (valCaps? c sl u) vs) (length vs ≤ᵇ suc (Caps.cWid c)) h
... | h1 , h2 = h1 , ≤ᵇ⇒≤ (length vs) (suc (Caps.cWid c)) (T-to h2)

-- and back the other way, at the REPORTED level: the payload ledger is
-- the companion's, the width is the input's carried across the level
-- by frameStep's own monotonicity
face-vals : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (j k : ℕ) (sl : Slots Γ)
  (vs : List (Val Γ u)) → 2 ≤ Caps.cSize c →
  all (valCaps? (frameStep (j + k) c) sl u) vs ≡ true →
  length vs ≤ suc (Caps.cWid (frameStep j c)) →
  valsCaps? (frameStep (j + k) c) sl vs ≡ true
face-vals c j k sl vs 2≤S hA hl =
  ∧-intro hA (T⇒≡true _ (≤⇒≤ᵇ
    (≤-trans hl (s≤s (proj₁ (proj₂ (frameStep-⊑-+ c 2≤S j k)))))))

-- the clauses that emit nothing and touch nothing: j′ = 0, and the
-- empty burst is inside every width there is
stepFrame-face-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (d j : ℕ) (u : Ty) (sl : Slots Γ) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  capsOK? (frameStep j c) sched st ≡ true →
  FrameFace {u = u} c d j sl ([] , [] , fin , sched , st)
stepFrame-face-zero c d j u sl fin sched st inv =
  0 , face-lift c d j 0 z≤n
    , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → valsCaps? {s = u} (frameStep x c) sl [] ≡ true)
            (sym (+-identityʳ j)) refl
    , refl

------------------------------------------------------------------
-- THE TWO *All FACES WAIT ON **TWO** NUMBERS, NOT ONE.

-- Both postulates below were flagged as waiting on the burst VALUE
-- COUNT — the (b) conjunct — and that reading is right about (b) and
-- incomplete about (a).  Enumerating what the tree reports:
--
--   (b) THE COUNT.  `subscribeE-caps` returns `burstCaps?`, which is
--       `all (all (eventCaps? …))` — every EVENT under the caps and no
--       cardinality at all.  The number that IS wanted is exactly the
--       entry measure `outWᵉ` (Rx.Frame-Width) already computes:
--       `ofᵉ ts ↦ length ts`, a scripted slot ↦ 1, map/take/scan ↦ the
--       source's, `deferᵉ ↦ 0`, and — the clause that matters — an *All
--       edge ↦ `outWⱽ e * innWⱽ e`, which is precisely "one subscribe
--       per payload, each contributing its own outW".  And `valCaps?`
--       ALREADY bounds it for a payload observable: `pWᵛ = outWᵛ ⊔ dWᵛ`
--       under `cWid`.  So (b) is a standalone induction over the
--       subscribe clique, `count ≤ outWᵉ n sl b`, needing no new
--       hypothesis on `subscribeE-caps` beyond the one it already
--       carries in `dWᵉ` form.
--
--   (a) THE RECEIPT, AND IT HAS NO SUPPLIER AT ALL.  `FrameFace`
--       demands `j′ ≤ fCharge (cSize c) (cWid c) j` — ONE frame's
--       receipt — and `thruWalk-caps` / `mergeAllDrain-caps` produce their
--       j′ by SUMMING `subscribeInner-caps`'s, which comes from
--       `subscribeE-caps`, whose j′ is existential and BOUNDED BY
--       NOTHING.  .Wet's own GAP note says the same thing from the wet
--       side ("NO SUBSCRIBE-LEVEL CHARGE … the missing companion is a
--       subscribeE-level analogue"), so this is one hole seen twice, not
--       two.  The count conjunct does not touch it: knowing how many
--       VALUES a subscribe emits says nothing about how many LEVELS it
--       climbed to emit them.

-- AND (a) DOES NOT FIT `fCharge`, NOR ANY CLOSED FORM IN (S, W, J) —
-- measured, `git show 94a5a3c^:agda/probe/Sub-Charge-Probe.agda`, which reads the receipt
-- table off this file's own GROUND clauses.  The crude reading said one
-- subscribe walks the inner's operator chain paying a frame receipt per
-- operator, `sizeᵉ o ≤ cSize` of them, so ~2·cSize per subscribe and
-- ~2·cWid·cSize per thru-outer frame — a CONSTANT factor over `fCharge
-- = suc (suc widAt * suc sizeAt)`.  That reading is wrong, and not by a
-- constant: a subscribe of `mergeAllᵉ l b` INSTALLS A thru-outer FRAME and
-- pushes b's burst back through it, `thruWalk` subscribes one inner per
-- payload, and that inner's subscribe runs frames of its own.  So
--
--     one FRAME     ⟶ ≤ suc widAt subscribes  (valsCaps?'s length half)
--     one SUBSCRIBE ⟶ ≤ suc sizeAt operators, each ⟶ ≤ suc widAt frames
--
-- and the two charges are MUTUALLY RECURSIVE.  It is the same failure
-- `dCapᶜ` already took one stratum up ("EVERY CLOSED FORM FAILS, AND
-- NOT BY A CONSTANT", Rx.Evaluator), and it takes the same repair: a
-- RECURSION on a nesting budget, every level quantity read at the level
-- the walk has climbed to.

-- THE GAS ESCAPE IS CLOSED BY TYPING, which had to be checked first.  A
-- synchronous fixpoint `μ x. mergeAll (of x)` would re-enter subscribeE
-- once per unfolding, bounded by the GAS and nothing else — and
-- `budgetAt` is a tower THREE STORIES ABOVE `capsAt`, so no reading of
-- the Caps triple could ever pay for it.  It is not writable: `μᵉ` binds
-- into Δᵍ, `varᵉ` reads Δ, and `deferᵉ` is the sole gate moving Δᵍ into
-- scope (Rx.Exp), so a μ's self-reference is reachable only across a
-- TICK.  `unfoldμ body` mentions `μᵉ body` only under a `deferᵉ`, and
-- one subscribe unfolds a μ at most as many times as the syntax nests
-- them — the μ clause's `j₀ = m + suc (m * m)` is a per-operator cost
-- like any other.

-- THE REPLACEMENT IS LANDED, AND SO IS THE RE-RULING ON
-- TOP OF IT.  The per-frame level in Rx.Evaluator is now the REFRESHED
-- hierarchy — `fLvlD` / `sIterD` / `sLvlD` / `opIterD` / `fIterD`, with
-- `k := suc (sizeAt S J)` re-read AT EVERY FRAME ENTRY rather than
-- inherited down the subscribe tree — and `iterL` spends `fLvlD S W d`
-- per frame where it spent `fLvl`.  The inherited family it replaces is
-- gone.  Reading the budget once, where a subscribe BEGAN, is refuted
-- (`git show 1f1730e^:agda/probe/Nest-Budget-Probe.agda` § 3: a `scanᵉ` under an *All mints
-- a payload per fold, the k-th mint nests k deep, the carrier's own
-- nesting stands still — 2 against 43690 at S = 2, W = 1, J = 0).  The
-- refresh's soundness is a theorem (Refresh-Probe § 1: `stepFrame`
-- reaches `subscribeInner` from two clauses only, and both suppliers are
-- bounded at the frame's own entry); its cost is the DEPTH FUEL `d`,
-- which descends where `k` used to.

-- Nothing above the frame had to move: `fLvl ≤ fLvlD` pointwise at every
-- fuel (.Caps), and `iterL`, `dLvl`, `lvls`, `sizeCount` and the count
-- gate are built from the per-frame monotonicity and nothing else.

-- AND THE FUEL IS RULED: it is the budget recurrence's OWN STORY INDEX,
-- threaded explicitly.  `blowH m` hands the pooled count its own m
-- (`poolCount (towerℕ m) m`) and `capsAt` runs instant id's blowup at
-- `capsH e sl id`, so `blowup-tower` compares the two counts at one
-- fuel and the budgetAt ↔ poolCount cycle (Refresh-Probe § 8) is broken
-- by the index rather than by an estimate.  What licenses reading a
-- fuel off the evaluator at all is the gas discipline written out at the
-- family in Rx.Evaluator: a subscribe with no gas installs nothing, the
-- three edges that reach a deeper subscribe each peel one `gs`, and
-- every other route keeps the gas fixed because it stays at ONE nesting
-- level.  What the placement still owes — the story index dominating the
-- depth an instant reaches, where the gas bound sits one blowH story
-- above it — is recorded there as owed.

-- WHAT IS LEFT IS THE PASS THAT SURFACES THE RECEIPTS INTO THE
-- SIGNATURES: `subscribeE-caps`'s Σ gains `j + j′ ≤ sLvlD S W d k j`
-- under a nesting hypothesis on `b`, and the six companions it calls
-- gain the matching conjunct.  The arithmetic each clause SHAPE needs
-- is proven ahead of the grind, and now against the LANDED family
-- rather than a mirror of it (`git show 94a5a3c^:agda/probe/Sub-Charge-Probe.agda` § 5, five
-- steps: `walk-step` a payload of thruWalk / mergeAllDrain, `frame-step`
-- the refresh itself — a frame's payload walk stops taking its nesting
-- hypothesis from the subscribe that installed it and reads its own —
-- `op-step` map / take / the four *All, `op-step-eval` scan, and
-- `op-step-mu`), against the receipts as abstract numbers under exactly
-- the bound the ground clauses hand back.  That gate is also what fixed the shape,
-- since the first draft of the hierarchy admitted none of the four (it
-- ran the frames before the rest of the operator chain, it charged a
-- payload's subscribe at J rather than at `suc J`, and its eval receipt
-- was linear where `unfoldμ-caps` pays `m + suc (m * m)`).

-- THE NESTING HYPOTHESIS IS SETTLED and is not `nestᵉ`.
-- The measure k really counts is `syncSizeᵉ` — the one that stops at
-- `deferᵉ`, the sole gate moving Δᵍ into Δ, and so drops by exactly one
-- across the μ edge, matching k's single descent at
-- `sLvlD S W d (suc k) J ↦ opIterD S W d k …` (Mu-Nest-Probe).
-- Nest-Count-Probe's `nestᵉ` counts scan-nesting and holds `nestᵉ (μᵉ e)
-- ≡ nestᵉ e`, so it is the WRONG measure here — nobody should re-derive
-- it.  The `nest ≤ size` leg the pass was recorded as owing is therefore
-- already in tree, as `syncSize≤sizeᵉ` (.Measures).  What the term
-- measure alone cannot do is the SHARE edge, whose callee is a stored
-- def unrelated to the caller's `input i`; the hypothesis the signatures
-- carry is .Caps-Nest's `M` — syncSize plus the residue owed by the
-- unconnected shares — and the frame supplies it one size level up
-- (`refresh-supplies-M`; the entry level is refuted outright).

-- THE COMPANION SIDE'S OWN FUEL is the gas it is handed: subscribe depth
-- ≤ gas height, by induction on the evaluator's recursion, which is the
-- same bridge the level side reads.  And the two faces below are the
-- first consumers that pass will pay for — `Walk-Hyps.sf-step` already
-- reports the level a frame LEAVES (`J + j′ ≤ fLvlD S W d J`) rather
-- than the receipt alone, so what these two owe is a receipt inside ONE
-- refreshed frame level rather than inside `fCharge`.

-- AND `FrameFace` IS NOW STATED THERE.  It carries the
-- depth fuel `d` and its receipt conjunct IS the landing form, `j + j′ ≤
-- fLvlD (cSize c) (cWid c) d j`.  The five ground construction sites
-- still pay `fCharge` and are lifted one at a time by `face-lift` (which
-- is exactly the composition `walkH.sf-step` used to do at its call
-- site, moved inside the face), so the relaxation cost nothing anywhere
-- else and `sf-step` now just forwards the conjunct.  What these two
-- postulates wait on is therefore ONE thing, not two: the signature pass
-- that gives `subscribeE-caps`'s j′ a bound at all.  With it, (a) is a
-- sum of subscribe receipts inside `sIterD` — which is what `fLvlD S W
-- (suc d) J` spends, one payload at a time, at the level the last one
-- left — and (b) is the width sum the block above prices.

-- BUT (a) IS DOWNSTREAM OF (b), NOT PARALLEL TO IT (read off
-- the two ground clauses below rather than argued).  The block above
-- calls (b) "a standalone induction" and (a) the receipt with no
-- supplier, as if either could be done first.  It cannot: (a)'s own
-- TARGET is counted in units only (b) supplies, at two sites, and both
-- are on the path from `subscribeE-caps` to the faces.
--
--   · ONE FRAME PER EMIT.  `pushBurst-caps` recurses on `em ∷ ems`,
--     summing one `stepFrame-caps` receipt per EMIT.  `op-step`'s
--     pushBurst premise is `… ≤ fIterD S W d k (suc (widAt S W A)) A` —
--     `suc (widAt S W A)` frames — so the clause needs
--     `length str ≤ suc (widAt S W A)`.  Its ONLY hypothesis about the
--     burst is `burstCaps?`, which is `all (all (eventCaps? …))`: every
--     event under the caps and NO cardinality, exactly as the block above
--     says of (b).  So the emit count is not a downstream nicety; it is
--     the index of the iteration that pays (a).
--
--   · AND ONE PAYLOAD PER VALUE INSIDE THE EMIT.  That same clause hands
--     `stepFrame-caps` its values through `splitEvents-vals-caps`, whose
--     conclusion is `all (valCaps? …)` and nothing more.  `frame-step`'s
--     walk premise counts payloads in `suc (widAt S W j)` — which is
--     `valsCaps?`'s length conjunct, i.e. what `FrameFace` carries and
--     what `stepFrame-caps` does not.  This is the same asymmetry the
--     face was SPLIT for (see the FrameFace block: "(a) needs the INPUT
--     width, and the companion's two callers have none to give"), now
--     read from the other end: the split is why the face can be charged
--     at one `fLvlD` and the companion cannot.

-- So the pass is (b) THEN (a), and (b) is two counts rather than one —
-- emits per burst and values per emit.  Both have the same entry
-- measure, `outWᵉ` (Rx.Frame-Width), and the same supplier for a payload
-- observable, `valCaps?`'s `pWᵛ = outWᵛ ⊔ dWᵛ` under `cWid`; what does
-- not exist yet is the predicate that carries them along the subscribe
-- clique the way `burstCaps?` carries the per-event bound
------------------------------------------------------------------

-- THE WIRING, proven rather than postulated: a value inside the cap
-- discharges BOTH of the walk's reset obligations at once.  This is what
-- makes the cluster one object instead of three coincidences, and it is
-- why F needs no separate justification — it is Ŝ
-- DELEGATES to `reach-reset` (.Measures), which is where this pair is
-- now stated once.  Kept as a name because the caps face's prose refers
-- to "the reset cluster" by it; it is a re-export, not a second proof.
-- DECLARED HERE, above the faces, because `thruOuter-face` consumes it
-- and that face is itself consumed further down the file than the hop
-- section this used to sit in.

