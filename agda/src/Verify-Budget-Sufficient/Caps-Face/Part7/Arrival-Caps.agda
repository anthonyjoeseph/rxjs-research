-- Verify-Budget-Sufficient.Caps-Face.Part7.Arrival-Caps
-- arr-chain-caps … arr-chains-caps-all
module Verify-Budget-Sufficient.Caps-Face.Part7.Arrival-Caps where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∨_)
open import Data.Nat     using (ℕ; suc; _+_; _∸_; _⊔_; _≤_; _≤ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (m+[n∸m]≡n; ≤-trans; ≤-refl; ≤-reflexive; m≤m+n; m≤n+m; n≤1+n; *-identityʳ; *-identityˡ;
  *-monoˡ-≤; +-monoʳ-≤; m≤m⊔n; +-suc; ≤ᵇ⇒≤)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; length)
open import Data.Bool.ListAction using (all; any)
open import Data.Fin     using (Fin)
import Data.Fin as Fin
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit    using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst; cong)

open import Rx.Prim      using (Gas; Id; Tick; _at_from_as_; after_,_; close; exhausted)
open import Rx.Exp       using (Ctx; Closed; Val; sizeᵉ; inputsBelowᵛ)
open import Verify-Budget-Sufficient.Nest-Ceiling using
  (Reached; Ent; Pos; ent-step; base; walk)
open import Verify-Budget-Sufficient.Subscribe-Face using (subscribeInner-caps; innerFinish-caps)
open import Verify-Budget-Sufficient.Caps-Depth using
  (depthCascade; depthChain; depthFold; depthFrame; depthDisp; lub3-l; lub3-m; lub3-r)
open import Verify-Budget-Sufficient.Nest-Store using
  (storeSyncMax; realWidAt-def; nestUnit; sightCeil; sightCeil-mono; nestBurstAt)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ)
open import Verify-Budget-Sufficient.Keeps-Ring using (stepFrame-slots)
open import Verify-Budget-Sufficient.Caps-Face.Nest-Arith using (nestΦAt)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Depth-Join using (fold-le; disp-le; latch-sync)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Frame-Vals using (chain-frame-ΦHyp)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using
  (valsΦ?; stepFrame-nest-Φ; Φ-to-bound)
open import Verify-Budget-Sufficient.Walk-Factor using (pathΦF-pos)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; arrVal; RegId; cascadeLatch; arrSource; chainsOf; cascadeGo; Path;
  Frame; stepFrame; foldPath; arrTy; regAt; dCapᶜ; lvls; iterL; chainStep; budgetAt; arrTick)
open import Rx.Slots using (Slots; slotsSize)

open import Verify-Budget-Sufficient.Delivery-Walk using
  (module Walk; chainsGo-chQ)
open import Verify-Budget-Sufficient.Psi-Split using
  (regP?-∧; regStrat?-paths; chP?-∧)
open import Verify-Budget-Sufficient.Deliveries using
  (delivN; delivN-cons; delivN-split; chainStep-deliv; cascadeGo-deliv; ⊑ᵈ-trans)
open import Verify-Budget-Sufficient.Caps using
  (1≤capsAt-reg; 2≤capsAt-size; Caps; capsAt; capsAt-base-size; capsH; cDel; _⊑ᶜ_; dCapᶜ-mono;
  frameStep; frameStep-0; frameStep-mono-j; iterL-mono; lvls-add; lvls-mono; sizeCount;
  sizeCount-body)
open import Verify-Budget-Sufficient.Measures using
  (pathLen; ∧-true; all-impl)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthCascade)

open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (capsAt-round-size; capsOK?; entStrat?; n≤capsAt-size; pathFloor; pathPark?; pathStrat?;
  pathSz?; pathSz?-widen; valCaps?; nestClosOK?ᵛ; nestClosOK?ᵛ-widen; pathOrd?)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Root-Strat using
  (pathStrat-top)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Strat-Leaves using
  (cascade-admit-park; chainStep-park; chainsOf-strat;
   cascade-admit-ord; chainStep-ord)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (capsOK?-count; capsOK?-delivered; capsOK?-regs; chainsStrat?-one; pathPark-delivered; pathsPark-delivered;
  pathSz?-len; registry-entStrat; slotsCaps?-capsAt; valsCaps?; valsCaps?-lvl; foldPath-slots;
  capsOK?-regOrd; capsOK?-regPark)
open import Verify-Budget-Sufficient.Caps-Face.Part3 using
  (valCaps?-widen)
open import Decide using (∧-intro; ∧-trueʳ; T-to)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Caps using
  (cascadeGo-deliveries; cascadeLatch-caps; chainStep-slots; chainsOf-length; walkH)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Chain-Caps-OK using
  (chainBurstOK; chainCapsOK; chainsBurstOK; chainsCapsOK)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Nodes using
  (chains-count-width)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Ring-Vocabulary using
  (WalkHyps; floor-parts)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Walk-Sink using
  (chain-walk-burst; chain-walk-caps)

-- WHAT A CASCADE'S CHAINS ARE STRATIFIED BY, stated over the list the
-- state hands out rather than over a path.  What a dead free form of
-- this needs moved is its SUBJECT and not its receipt, and the subject
-- is here already: `chainsOf a st` is `chainsGo` over
-- `EvalSt.registry`, a FILTER of the registry, so a statement over it
-- is one the store can be asked.  Structurally the ring's own admitted
-- list one face over, which is why the two are stated in the same
-- shape.
--
-- ONLY THE PATH HALF MOVES HERE, and the split is forced rather than
-- chosen.  A chain comes off the state; the VALUE the chain is entered
-- with is `arrVal a`, and `a` is still universally quantified at every
-- statement on this route -- so the value half's witness transfers
-- untouched, and moving it needs the arrival tied to the schedule it
-- was minted from.  That tie exists and is proven five times over, at
-- the drain: each `pop-head-` lemma reads a fact about `arrVal a` off
-- a `capsOK?` conjunct over `Sched.live`, across `sched-next`.  The
-- channel down to here is open too, since two such facts already
-- travel it.  What is missing is the conjunct itself.
--
-- AND IT IS THE SAME OBLIGATION THE MINT ALREADY NAMED, which is what
-- makes it one finding rather than two.  `registry-entStrat`'s dead
-- route enumerates four obligations at a registration and calls its
-- last "a
-- conjunct on the values in flight, a different invariant from this
-- one".  This is that invariant, reached from the delivery end.
--
-- THE SOURCE IS NOT THE INDEX, and that is why the ring's widening
-- does not transfer with its statement.  The sink meets its entry at
-- its own slot and widens up to the path's floor.  A floor is `n` at a
-- root and `toℕ i` at a sink, while `srcFloor?` puts every minted
-- source at or above `n` -- so a source-indexed premise holds with
-- equality exactly when the source is a slot's and fails as soon as
-- one is minted.  The claim is therefore stated AT each entry's own
-- floor, which is also why it cannot be a per-arrival premise.
--

-- AND ONLY THE SINK-FLOORED CHAINS ARE ASKED FOR, because the others
-- are free and `pathStrat-top` says so without spending the receipt.
-- A frame names inputs of `Γ`, so every closure is below `n`; a chain
-- ending at `root` is charged at exactly `n`, and one ending at a
-- `share-sink` at the slot's index.  So the disjunct below is the
-- whole risky region, and it is strictly smaller than the chain set:
-- what a share registered, rather than what the registry holds.
--
-- AND THE REGION ADMITS NO INSTANTIATION ON THE DEMAND CORPUS, which
-- is a coverage boundary rather than an unprobed row.  Running every
-- family of `Demand-Programs` -- fan, unsubscribe, window, chain --
-- across the instants the schedule reaches, and
-- counting registry entries whose chain floors below `n`, gives ZERO
-- at every one of thirteen configurations: the corpus registers
-- root-terminated chains only, so a row taken on it would land in the
-- disjunct's free half and could not have failed.
--
-- AND THE TELESCOPE CLOSES MOST OF THAT REGION, BUT NOT ALL OF IT,
-- WHICH IS WHERE THIS MEETS THE ENTRY LEDGER'S OWN MINT OBLIGATION.  A
-- sink-terminated chain is registered by the CONNECT, which subscribes
-- the slot's def under `share-sink i`, so a frame the DESCENT pushes is
-- a subterm of that def -- and `Rx.Slots.shared` admits a def only with
-- its inputs below the slot's own index, which is definitionally what
-- `frameStrat?` asks at the floor such a chain reports.  That is four
-- of the five registration sites the reading is owed at, enumerated at
-- `regStrat?` itself.  The fifth is NOT telescope induction and the tempting
-- argument that it is, is false: a flatten frame inside the def can
-- subscribe an observable that arrived as a VALUE, and `Val Γ (obs t)`
-- is an arbitrary closed expression, so the syntax the telescope
-- checked never contained the inputs then being registered.  Read off
-- the constructors, not instantiated, so nothing here lowers a class.
--
-- AND WHAT IS LEFT IS ONE LEDGER OVER THE REGISTRY, NOT ONE STATEMENT
-- PER FACE.  `chainsGo` filters the registry by source and type, so a
-- reading held at every entry is inherited by the arrival's chains --
-- and the ORDERING half that reading also carries is dropped here
-- rather than being a second premise, because the cascade's own claim
-- says nothing about where the values are leaving from.  Which is why
-- this face never meets that half's guard: the frame reading it does
-- want is the entry ledger's unguarded conjunct.
--
-- REFUTED: `Refuted.Walk-Entry-Strat.walk-path-strat-absurd` kills the
--   free form this replaces, where the path was quantified after the
--   receipt: one frame over a sink -- a `map` whose template names
--   input one, ending at slot nought, whose floor is nought -- against
--   the receipt taken at the INITIAL state of a two-slot program,
--   where it computes. The telescope's own stratification does not
--   reach it, `shared` constraining a slot's DEF while a path's frames
--   are not any slot's def.  It is also why the disjunct above may not
--   be traded for a premise on a free path: that is the refuted form
--   with a floor hypothesis, and the counterexample's floor is nought.
cascade-admit-sink : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  all (λ rc → (n ≤ᵇ pathFloor (proj₂ rc)) ∨ pathStrat? (proj₂ rc))
      (chainsOf a st) ≡ true
cascade-admit-sink {n = n} {Γ = Γ} {t = t} c a sched st cok =
  all-impl _ _ drop (chainsOf a st)
    (chainsGo-chQ (λ {u} → entStrat? {u = u}) a (EvalSt.registry st)
                  (registry-entStrat c sched st cok))
  where
  drop : ∀ (rc : RegId × Path Γ (arrTy a) t) →
         entStrat? (arrSource a) (proj₂ rc) ≡ true →
         ((n ≤ᵇ pathFloor (proj₂ rc)) ∨ pathStrat? (proj₂ rc)) ≡ true
  drop rc h with n ≤ᵇ pathFloor (proj₂ rc)
  ... | true  = refl
  ... | false = ∧-trueʳ h

cascade-admit-entry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  all (λ rc → pathStrat? (proj₂ rc)) (chainsOf a st) ≡ true
cascade-admit-entry {n = n} {Γ = Γ} {t = t} c a sched st cok =
  all-impl _ _ free (chainsOf a st) (cascade-admit-sink c a sched st cok)
  where
  free : ∀ (rc : RegId × Path Γ (arrTy a) t) →
         ((n ≤ᵇ pathFloor (proj₂ rc)) ∨ pathStrat? (proj₂ rc)) ≡ true →
         pathStrat? (proj₂ rc) ≡ true
  free rc h with n ≤ᵇ pathFloor (proj₂ rc) in eq
  ... | true  = pathStrat-top (proj₂ rc) (≤ᵇ⇒≤ n _ (T-to eq))
  ... | false = h

-- THE TUPLE ONE CHAIN'S WALK IS ENTERED WITH, met once and spent by
-- both ledgers below.  The cascade's round package carries every
-- hypothesis the walk skeleton wants of a chain except the entering
-- level bound, which is the one rewrite: the fold's climb over the
-- path is under the round's level because the path is no longer than
-- the size that bounds it.
arr-chain-hyps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lv : ℕ) (a : Arrival Γ) (nextId : Id)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (frameStep Lv (capsAt e sl id)) sched st ≡ true →
  valsCaps? (frameStep Lv (capsAt e sl id)) sl (arrVal a ∷ []) ≡ true →
  all (nestClosOK?ᵛ (frameStep Lv (capsAt e sl id)) sl (arrTy a)) (arrVal a ∷ []) ≡ true →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) path ≡ true →
  depthChain nextId a path sched st ≤ capsH e sl id →
  pathStrat? path ≡ true →
  inputsBelowᵛ (pathFloor path) (arrTy a) (arrVal a) ≡ true →
  pathPark? path st ≡ true →
  pathOrd? (Sched.nextNode sched) path ≡ true →
  (Σ ℕ λ g → Σ ℕ λ P →
     (4 + (sizeᵉ e + slotsSize sl) + n + n ≤ g)
     × (lvls (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) (capsH e sl id) Lv 1
          ≤ P)
     × Reached (capsAt e sl id) (capsH e sl id) P g) →
  WalkHyps sl id Lv (budgetAt e (Sched.slots sched) nextId) n nextId (arrTick a) (arrSource a)
    path (arrVal a ∷ [])
    (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    (Arrival.isLast a) sched st
arr-chain-hyps {e = e} sl id Lv a nextId path sched st sleq cok hvc hcl hpz hdp hstr hsv hpk hord
  (g , P , hfl , hlvP , hR) =
  sleq , cok , hvc , hcl , hpz , hdp
  , ∧-intro hsv refl
  , hstr
  , hpk
  , hord
  , (g , P , hfl , ENTRY , hR)
  where
  c   = capsAt e sl id
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  ENTRY : iterL (Caps.cSize c) (Caps.cWid c) d (pathLen path) Lv ≤ P
  ENTRY = ≤-trans (iterL-mono (pathLen path) _ 2≤S ≤-refl ≤-refl ≤-refl
                     (≤-trans (pathSz?-len (Caps.cSize (frameStep Lv c)) path hpz)
                              (n≤1+n _)))
            hlvP

arr-chain-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lv : ℕ) (a : Arrival Γ) (nextId : Id)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (frameStep Lv (capsAt e sl id)) sched st ≡ true →
  valsCaps? (frameStep Lv (capsAt e sl id)) sl (arrVal a ∷ []) ≡ true →
  all (nestClosOK?ᵛ (frameStep Lv (capsAt e sl id)) sl (arrTy a)) (arrVal a ∷ []) ≡ true →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) path ≡ true →
  depthChain nextId a path sched st ≤ capsH e sl id →
  pathStrat? path ≡ true →
  inputsBelowᵛ (pathFloor path) (arrTy a) (arrVal a) ≡ true →
  pathPark? path st ≡ true →
  pathOrd? (Sched.nextNode sched) path ≡ true →
  (Σ ℕ λ g → Σ ℕ λ P →
     (4 + (sizeᵉ e + slotsSize sl) + n + n ≤ g)
     × (lvls (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) (capsH e sl id) Lv 1
          ≤ P)
     × Reached (capsAt e sl id) (capsH e sl id) P g) →
  chainCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lv nextId a path sched st
arr-chain-caps {n = n} {e = e} sl id Lv a nextId path sched st sleq cok hvc hcl hpz hdp hstr hsv hpk hord hR =
  chain-walk-caps sl id Lv (budgetAt e (Sched.slots sched) nextId) n nextId
    (arrTick a) (arrSource a) path (arrVal a ∷ [])
    (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    (Arrival.isLast a) sched st
    (arr-chain-hyps sl id Lv a nextId path sched st sleq cok hvc hcl hpz hdp hstr hsv hpk hord hR)

-- AND THE SAME CHAIN'S BURST LEDGER, entered with the same tuple, so
-- that one walk of the cascade's chains yields both.
arr-chain-burst : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lv : ℕ) (a : Arrival Γ) (nextId : Id)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (frameStep Lv (capsAt e sl id)) sched st ≡ true →
  valsCaps? (frameStep Lv (capsAt e sl id)) sl (arrVal a ∷ []) ≡ true →
  all (nestClosOK?ᵛ (frameStep Lv (capsAt e sl id)) sl (arrTy a)) (arrVal a ∷ []) ≡ true →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) path ≡ true →
  depthChain nextId a path sched st ≤ capsH e sl id →
  pathStrat? path ≡ true →
  inputsBelowᵛ (pathFloor path) (arrTy a) (arrVal a) ≡ true →
  pathPark? path st ≡ true →
  pathOrd? (Sched.nextNode sched) path ≡ true →
  (Σ ℕ λ g → Σ ℕ λ P →
     (4 + (sizeᵉ e + slotsSize sl) + n + n ≤ g)
     × (lvls (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) (capsH e sl id) Lv 1
          ≤ P)
     × Reached (capsAt e sl id) (capsH e sl id) P g) →
  chainBurstOK (nestBurstAt e sl id) nextId a path sched st
arr-chain-burst {n = n} {e = e} sl id Lv a nextId path sched st sleq cok hvc hcl hpz hdp hstr hsv hpk hord hR =
  chain-walk-burst sl id Lv (budgetAt e (Sched.slots sched) nextId) n nextId
    (arrTick a) (arrSource a) path (arrVal a ∷ [])
    (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    (Arrival.isLast a) sched st
    (arr-chain-hyps sl id Lv a nextId path sched st sleq cok hvc hcl hpz hdp hstr hsv hpk hord hR)


-- ONE CHAIN'S STEP IS THE PATH FOLD, so the level it lands at is the
-- fold's own theorem and not a leaf.  `chainStep` IS `foldPath` at the
-- minted gas, the walk skeleton is instantiated at exactly the caps
-- hypotheses here, and its receipt reports the three things the
-- statement asks for: the level, that the walk only climbed to it, and
-- the state fact there.  The increment is the difference, which is why
-- the conclusion is stated at `Lv + L'` and proven at the absolute
-- level the walk names.
--
-- TWIN: `stepFrame-caps` -- one frame of this same fold, with the same
--   discipline: invariant at the stepped cap, own increment reported.
chainStep-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lv : ℕ) (a : Arrival Γ) (nextId : Id)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (frameStep Lv (capsAt e sl id)) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) path ≡ true →
  valCaps? (frameStep Lv (capsAt e sl id)) sl (arrTy a) (arrVal a) ≡ true →
  depthChain nextId a path sched st ≤ capsH e sl id →
  -- THE ENTRY READING, BESIDE THE SIZE ONE.  Both of the walk's ledgers
  -- carry a stratification half now, so this direct entry owes both:
  -- the chain is stratified, and the arriving value sits below that
  -- chain's floor.  Neither half mentions the level, so the step's own
  -- climb leaves them untouched
  pathStrat? path ≡ true →
  inputsBelowᵛ (pathFloor path) (arrTy a) (arrVal a) ≡ true →
  -- AND THE CHAIN'S TWO ENTRY READINGS, which the walk's ledger prices
  -- its registry by: neither is derivable from the caps receipt, so
  -- each is carried in from whatever wrote what it reads
  pathPark? path st ≡ true →
  pathOrd? (Sched.nextNode sched) path ≡ true →
  Σ ℕ λ L′ →
    (Lv + L′ ≤ lvls (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) (capsH e sl id)
                 Lv (suc (delivN st (proj₂ (proj₂ (chainStep nextId a path sched st))))))
    × (capsOK? (frameStep (Lv + L′) (capsAt e sl id))
         (proj₁ (proj₂ (chainStep nextId a path sched st)))
         (proj₂ (proj₂ (chainStep nextId a path sched st))) ≡ true)
chainStep-caps {n = n} {e = e} sl id Lv a nextId path sched st sleq cok hpz hvc hdp hstr hsv hpk hord =
  W.Res.lvl FP ∸ Lv
  , subst (_≤ CEIL) (sym EQ) (≤-trans (W.Res.hi FP) STEP)
  , subst (λ x → capsOK? (frameStep x c)
                   (proj₁ (proj₂ (chainStep nextId a path sched st)))
                   (proj₂ (proj₂ (chainStep nextId a path sched st))) ≡ true)
          (sym EQ) (proj₂ (proj₁ (W.Res.good FP)))
  where
  c = capsAt e sl id
  d = capsH e sl id
  2≤S : 2 ≤ Caps.cSize c
  2≤S = 2≤capsAt-size e sl id
  slSz : slotsSize sl ≤ Caps.cSize c
  slSz = ≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl id)
  module W = Walk {e = e} (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d 2≤S
                  (walkH (λ {n′} {Γ′} {t′} {e′} {u′} →
                            subscribeInner-caps {n′} {Γ′} {t′} {e′} {u′})
                         (λ {n′} {Γ′} {t′} {e′} {s′} →
                            innerFinish-caps {n′} {Γ′} {t′} {e′} {s′})
                         c d sl 2≤S (1≤capsAt-reg e sl id)
                         (slotsCaps?-capsAt e sl id) slSz)
  -- THE WALK PRICES ITS REGISTRY BY BOTH READINGS NOW, so the entry
  -- receipt is the caps invariant's two halves recombined: the size one
  -- straight off `capsOK?`, the entry one off the same invariant's
  -- ninth conjunct and lifted from a registry reading to a path one
  regʲ = regP?-∧ (λ {u} pp → pathSz? (Caps.cSize (frameStep Lv c)) pp)
                 (λ {u} pp → pathStrat? pp) (EvalSt.registry st)
           (capsOK?-regs (frameStep Lv c) sched st cok)
           (regStrat?-paths (EvalSt.registry st)
              (registry-entStrat (frameStep Lv c) sched st cok))
  FP = W.foldPath-go Lv (budgetAt e (Sched.slots sched) nextId) n nextId
         (arrTick a) (arrSource a) path (arrVal a ∷ [])
         (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
         (Arrival.isLast a) sched st
         ((sleq , cok) , regʲ)
         (∧-intro hpz hstr)
         (∧-intro (∧-intro (∧-intro hvc refl) refl) (∧-intro hsv refl))
         (W.eb-seed Lv (arrSource a) (Arrival.isLast a)) tt tt hdp
         (∧-intro hord hpk)
  EQ : Lv + (W.Res.lvl FP ∸ Lv) ≡ W.Res.lvl FP
  EQ = m+[n∸m]≡n (W.Res.lo FP)
  D = delivN st (proj₂ (proj₂ (chainStep nextId a path sched st)))
  CEIL = lvls (Caps.cSize c) (Caps.cWid c) d Lv (suc D)
  -- one chain is at most `suc (sizeAt S Lv)` frames, so its whole level
  -- climb is peeled off the front of the walk's own ladder as ONE
  -- delivery's charge — which is what makes the ceiling base-relative
  -- and so composable along the cascade
  chain≤ : iterL (Caps.cSize c) (Caps.cWid c) d (pathLen path) Lv
             ≤ lvls (Caps.cSize c) (Caps.cWid c) d Lv 1
  chain≤ = iterL-mono (pathLen path) _ 2≤S ≤-refl ≤-refl ≤-refl
             (≤-trans (pathSz?-len (Caps.cSize (frameStep Lv c)) path hpz) (n≤1+n _))
  STEP : lvls (Caps.cSize c) (Caps.cWid c) d
           (iterL (Caps.cSize c) (Caps.cWid c) d (pathLen path) Lv) D ≤ CEIL
  STEP = ≤-trans (lvls-mono D D 2≤S ≤-refl ≤-refl chain≤ ≤-refl)
                 (≤-reflexive (sym (lvls-add (Caps.cSize c) (Caps.cWid c) d Lv 1 D)))

-- ONE CHAIN'S DELIVERIES AGAINST THE BUDGET READ AT ITS OWN POSITION,
-- which is the recursive shape of the whole claim rather than a step
-- of it: the cascade's total is what `cascadeGo-deliveries` bounds at
-- entry, and this is the same statement one round down, at the level
-- the round's ledger has climbed to instead of at the entry level.
-- The gas is the term's own operator budget, and it is what stops the
-- statement being vacuous -- at gas zero the cap is zero and no chain
-- delivering anything can fit.
chain-deliv-cap : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) (Lv J g i : ℕ) →
  Sched.slots sched ≡ sl →
  n ≤ g →
  capsOK? (frameStep Lv (capsAt e sl id)) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) path ≡ true →
  valsCaps? (frameStep Lv (capsAt e sl id)) sl (arrVal a ∷ []) ≡ true →
  depthChain nextId a path sched st ≤ capsH e sl id →
  Lv ≤ Ent (capsAt e sl id) (capsH e sl id) J g i →
  -- the same two halves the step above owes, for the same reason and at
  -- the same chain: the position this is read at moves the budget, not
  -- either reading
  pathStrat? path ≡ true →
  inputsBelowᵛ (pathFloor path) (arrTy a) (arrVal a) ≡ true →
  pathPark? path st ≡ true →
  pathOrd? (Sched.nextNode sched) path ≡ true →
  delivN st (proj₂ (proj₂ (chainStep nextId a path sched st)))
    ≤ dCapᶜ (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id))
            (Caps.cReg (capsAt e sl id)) (capsH e sl id) g
            (Pos (capsAt e sl id) (capsH e sl id) J g i)
chain-deliv-cap {n = n} {e = e} sl id a nextId path sched st Lv J g i
  sleq n≤g cok hpz hvc hdp hLv hstr hsv hpk hord =
  ≤-trans (W.Res.cnt (W.foldPath-go Lv (budgetAt e (Sched.slots sched) nextId) n nextId
                        (arrTick a) (arrSource a) path (arrVal a ∷ [])
                        (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
                        (Arrival.isLast a) sched st
                        ((sleq , cok) , regʲ)
                        (∧-intro hpz hstr) (∧-intro hvc (∧-intro hsv refl))
                        refl tt tt hdp (∧-intro hord hpk)))
          (dCapᶜ-mono {S} {S} {Wd} {Wd} {R} {R} {_} {_} {d} n g
             2≤S ≤-refl ≤-refl ≤-refl n≤g CLIMB)
  where
  c   = capsAt e sl id
  S   = Caps.cSize c
  Wd  = Caps.cWid c
  R   = Caps.cReg c
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  regʲ = regP?-∧ (λ {u} pp → pathSz? (Caps.cSize (frameStep Lv c)) pp)
                 (λ {u} pp → pathStrat? pp) (EvalSt.registry st)
           (capsOK?-regs (frameStep Lv c) sched st cok)
           (regStrat?-paths (EvalSt.registry st)
              (registry-entStrat (frameStep Lv c) sched st cok))
  module W = Walk {e = e} S Wd R d 2≤S
    (walkH (λ {n′} {Γ′} {t′} {e′} {u′} → subscribeInner-caps {n′} {Γ′} {t′} {e′} {u′})
           (λ {n′} {Γ′} {t′} {e′} {s′} → innerFinish-caps {n′} {Γ′} {t′} {e′} {s′})
           c d sl 2≤S (1≤capsAt-reg e sl id) (slotsCaps?-capsAt e sl id)
           (≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl id)))
  -- the chain's frames climb at most one restart, which is what
  -- `pathSz?` bounds, and one restart from the round's ledger IS the
  -- position -- so the level the fold reads the budget at dominates
  -- the level the chain's own walk reads it at
  CLIMB : iterL S Wd d (pathLen path) Lv ≤ Pos c d J g i
  CLIMB = ≤-trans (iterL-mono (pathLen path) _ 2≤S ≤-refl ≤-refl ≤-refl
                     (≤-trans (pathSz?-len (Caps.cSize (frameStep Lv c)) path hpz)
                              (n≤1+n _)))
                  (lvls-mono 1 1 2≤S ≤-refl ≤-refl hLv ≤-refl)


-- `R` for the tail, related by `lvls-add`.
arr-chains-caps-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lv : ℕ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  lvls (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) (capsH e sl id) Lv
       (delivN st (proj₂ (proj₂ (cascadeGo a nextId chains sched st))))
    ≤ sizeCount (capsAt e sl id) (capsH e sl id) ⊔ Caps.cSize (capsAt e sl id) →
  capsOK? (frameStep Lv (capsAt e sl id)) sched st ≡ true →
  all (λ rc → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rc)) chains ≡ true →
  all (λ rc → pathStrat? (proj₂ rc)) chains ≡ true →
  all (λ rc → inputsBelowᵛ (pathFloor (proj₂ rc)) (arrTy a) (arrVal a)) chains ≡ true →
  -- the third reading, pointwise like the two above it and unlike them
  -- read AT THE STATE, which is what makes the fold's two recursive arms
  -- ask for it in two different places rather than one
  all (λ rc → pathPark? (proj₂ rc) st) chains ≡ true →
  -- and the chain's own order, which the reading above it is transported
  -- ON and which moves only with the counter
  all (λ rc → pathOrd? (Sched.nextNode sched) (proj₂ rc)) chains ≡ true →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  nestClosOK?ᵛ (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  depthCascade a nextId chains sched st ≤ capsH e sl id →
  (J g i : ℕ) →
  4 + (sizeᵉ e + slotsSize sl) + n + n ≤ g →
  Reached (capsAt e sl id) (capsH e sl id) J (suc g) →
  i + length chains
    ≤ regAt (Caps.cSize (capsAt e sl id)) (Caps.cReg (capsAt e sl id)) J →
  Lv ≤ Ent (capsAt e sl id) (capsH e sl id) J g i →
  chainsCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lv a nextId chains sched st
  × chainsBurstOK (nestBurstAt e sl id) a nextId chains sched st
arr-chains-caps-go sl id Lv a nextId [] sched st sleq hlv cok hpz hstr hsv hpk hord hvc hcl hdp
  J g i hfl hR hlen hLv = tt , tt
arr-chains-caps-go {n = n} {e = e} sl id Lv a nextId ((rid , path) ∷ chains) sched st sleq hlv cok hpz hstr hsv hpk hord hvc hcl hdp
  J g i hfl hR hlen hLv
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = arr-chains-caps-go sl id Lv a nextId chains sched st sleq hlv cok
                (proj₂ (∧-true _ _ hpz)) (proj₂ (∧-true _ _ hstr))
                (proj₂ (∧-true _ _ hsv)) (proj₂ (∧-true _ _ hpk))
                (proj₂ (∧-true _ _ hord)) hvc hcl
                (lub3-l (depthCascade a nextId chains sched st)
                        (depthChain nextId a path sched
                           (record st { delivered = rid ∷ EvalSt.delivered st }))
                        (depthCascade a nextId chains
                           (proj₁ (proj₂ (chainStep nextId a path sched
                              (record st { delivered = rid ∷ EvalSt.delivered st }))))
                           (proj₂ (proj₂ (chainStep nextId a path sched
                              (record st { delivered = rid ∷ EvalSt.delivered st }))))) hdp)
                J g i hfl hR
                (≤-trans (+-monoʳ-≤ i (n≤1+n (length chains))) hlen) hLv
... | false =
      ( arr-chain-caps sl id Lv a nextId path sched st′ sleq COK′ HVC HCL HPZ HDP
          (proj₁ (∧-true _ _ hstr)) (proj₁ (∧-true _ _ hsv)) HPK
          (proj₁ (∧-true _ _ hord))
          (g , Pos c d J g i , hfl , CH≤ , walk J g i HI hR)
      , proj₁ ST
      , FLAT
      , proj₁ GO′ )
    , ( arr-chain-burst sl id Lv a nextId path sched st′ sleq COK′ HVC HCL HPZ HDP
          (proj₁ (∧-true _ _ hstr)) (proj₁ (∧-true _ _ hsv)) HPK
          (proj₁ (∧-true _ _ hord))
          (g , Pos c d J g i , hfl , CH≤ , walk J g i HI hR)
      , proj₂ GO′ )
  where st′ = record st { delivered = rid ∷ EvalSt.delivered st }
        c   = capsAt e sl id
        S   = Caps.cSize c
        W   = Caps.cWid c
        d   = capsH e sl id
        TOP = sizeCount c d ⊔ S
        2≤S = 2≤capsAt-size e sl id
        st₁ = proj₂ (proj₂ (chainStep nextId a path sched st′))
        D   = delivN st′ st₁
        R   = delivN st₁ (proj₂ (proj₂ (cascadeGo a nextId chains
                (proj₁ (proj₂ (chainStep nextId a path sched st′))) st₁)))
        step⊑ = frameStep-mono-j c 2≤S (z≤n {Lv})
        c⊑ : c ⊑ᶜ frameStep Lv c
        c⊑ = subst (_⊑ᶜ frameStep Lv c) (frameStep-0 c) step⊑
        HVC0 : valsCaps? c sl (arrVal a ∷ []) ≡ true
        HVC0 = ∧-intro (∧-intro hvc refl) refl
        HVC : valsCaps? (frameStep Lv c) sl (arrVal a ∷ []) ≡ true
        HVC = valsCaps?-lvl c (frameStep Lv c) sl (arrVal a ∷ []) c⊑ HVC0
        HCL : all (nestClosOK?ᵛ (frameStep Lv c) sl (arrTy a)) (arrVal a ∷ []) ≡ true
        HCL = all-impl _ _
                (λ v h → nestClosOK?ᵛ-widen sl _ v c⊑ h)
                (arrVal a ∷ []) (∧-intro hcl refl)
        COK′ = capsOK?-delivered (frameStep Lv c) rid sched st cok
        ST  = chainStep-caps sl id Lv a nextId path sched st′ sleq COK′
                (pathSz?-widen path (proj₁ c⊑) (proj₁ (∧-true _ _ hpz)))
                (valCaps?-widen sl (arrTy a) (arrVal a) c⊑ hvc)
                (lub3-m (depthCascade a nextId chains sched st)
                        (depthChain nextId a path sched st′)
                        (depthCascade a nextId chains
                           (proj₁ (proj₂ (chainStep nextId a path sched st′)))
                           (proj₂ (proj₂ (chainStep nextId a path sched st′)))) hdp)
                (proj₁ (∧-true _ _ hstr)) (proj₁ (∧-true _ _ hsv))
                (pathPark-delivered path rid st (proj₁ (∧-true _ _ hpk)))
                (proj₁ (∧-true _ _ hord))
        -- THE CASCADE'S OWN LEDGER LINE, at the state this arm has
        -- already reduced to: an uncancelled registration costs one
        -- delivery, plus this chain's fold, plus the tail's.  It is
        -- written here rather than taken from the ledger stratum
        -- because the `with` has replaced the cascade by its reduct,
        -- and a lemma stated over the unreduced application no longer
        -- applies to what this arm holds.
        CS  = chainStep-deliv nextId a path sched st′
        GO  = cascadeGo-deliv a nextId chains
                (proj₁ (proj₂ (chainStep nextId a path sched st′))) st₁
        SPLIT : delivN st (proj₂ (proj₂ (cascadeGo a nextId chains
                  (proj₁ (proj₂ (chainStep nextId a path sched st′))) st₁)))
                  ≡ suc (D + R)
        SPLIT = trans (delivN-cons rid st _ (⊑ᵈ-trans CS GO))
                      (cong suc (delivN-split CS GO))
        hlvC : lvls S W d Lv (suc (D + R)) ≤ TOP
        hlvC = subst (λ x → lvls S W d Lv x ≤ TOP) SPLIT hlv
        -- this chain's own charge, which is what both the leaf below
        -- and the Σ above are bounded by
        FLATC : lvls S W d Lv (suc D) ≤ TOP
        FLATC = ≤-trans (lvls-mono (suc D) (suc (D + R)) 2≤S ≤-refl ≤-refl ≤-refl
                           (s≤s (m≤m+n D R)))
                        hlvC
        FLAT = ≤-trans (proj₁ (proj₂ ST)) FLATC
        -- this chain sits at the round's `i`-th position, and one
        -- restart from there is what its own frames may climb
        HI : suc i ≤ regAt S (Caps.cReg c) J
        HI = ≤-trans (subst (suc i ≤_) (sym (+-suc i (length chains)))
                            (s≤s (m≤m+n i (length chains))))
                     hlen
        CH≤ : lvls S W d Lv 1 ≤ Pos c d J g i
        CH≤ = lvls-mono 1 1 2≤S ≤-refl ≤-refl hLv ≤-refl
        hgn = proj₁ (proj₂ (floor-parts (4 + (sizeᵉ e + slotsSize sl)) n n g hfl))
        -- and the fold's own climb lands on the NEXT position exactly
        -- when this chain's deliveries fit the budget read at this one
        STEP : lvls S W d Lv (suc D) ≤ Ent c d J g (suc i)
        STEP = ≤-trans (lvls-mono (suc D) (suc D) 2≤S ≤-refl ≤-refl hLv ≤-refl)
                       (ent-step c d J g i D 2≤S
                          (chain-deliv-cap sl id a nextId path sched st′ Lv J g i
                             sleq hgn COK′
                             (pathSz?-widen path (proj₁ c⊑) (proj₁ (∧-true _ _ hpz)))
                             HVC
                             (lub3-m (depthCascade a nextId chains sched st)
                                     (depthChain nextId a path sched st′)
                                     (depthCascade a nextId chains
                                        (proj₁ (proj₂ (chainStep nextId a path sched st′)))
                                        (proj₂ (proj₂ (chainStep nextId a path sched st′)))) hdp)
                             hLv (proj₁ (∧-true _ _ hstr))
                             (proj₁ (∧-true _ _ hsv))
                             (pathPark-delivered path rid st (proj₁ (∧-true _ _ hpk)))
                             (proj₁ (∧-true _ _ hord))))
        REC  = ≤-trans (lvls-mono R R 2≤S ≤-refl ≤-refl (proj₁ (proj₂ ST)) ≤-refl)
                 (≤-trans (≤-reflexive (sym (lvls-add S W d Lv (suc D) R))) hlvC)
        HPZ  = pathSz?-widen path (proj₁ c⊑) (proj₁ (∧-true _ _ hpz))
        -- the head chain's park reading, transported to the state this
        -- arm has already marked delivered
        HPK  = pathPark-delivered path rid st (proj₁ (∧-true _ _ hpk))
        HDP  = lub3-m (depthCascade a nextId chains sched st)
                      (depthChain nextId a path sched st′)
                      (depthCascade a nextId chains
                         (proj₁ (proj₂ (chainStep nextId a path sched st′)))
                         (proj₂ (proj₂ (chainStep nextId a path sched st′)))) hdp
        -- the tail, at the state and level this chain's step left
        GO′  = arr-chains-caps-go sl id (Lv + proj₁ ST) a nextId chains
                 (proj₁ (proj₂ (chainStep nextId a path sched st′)))
                 (proj₂ (proj₂ (chainStep nextId a path sched st′)))
                 (trans (chainStep-slots nextId a path sched st′) sleq)
                 REC (proj₂ (proj₂ ST))
                 (proj₂ (∧-true _ _ hpz)) (proj₂ (∧-true _ _ hstr))
                 (proj₂ (∧-true _ _ hsv))
                 -- the tail's chains are read at the state the HEAD's
                 -- step produced, which is the one place the reading is
                 -- re-established rather than rearranged
                 (chainStep-park nextId a path sched st′ chains
                    (pathsPark-delivered chains rid st (proj₂ (∧-true _ _ hpk))))
                 -- and the same at the counter, which the step only
                 -- raised: the tail's chains are the chains they were
                 (chainStep-ord nextId a path sched st′ chains
                    (proj₂ (∧-true _ _ hord)))
                 hvc hcl
                 (lub3-r (depthCascade a nextId chains sched st)
                         (depthChain nextId a path sched st′)
                         (depthCascade a nextId chains
                            (proj₁ (proj₂ (chainStep nextId a path sched st′)))
                            (proj₂ (proj₂ (chainStep nextId a path sched st′)))) hdp)
                 J g (suc i) hfl hR
                 (subst (_≤ regAt S (Caps.cReg c) J) (+-suc i (length chains)) hlen)
                 (≤-trans (proj₁ (proj₂ ST)) STEP)

-- ONE WALK OF THE CHAINS, BOTH LEDGERS.  The caps fold is the one that
-- knows the level each chain is entered at, and the burst ledger is
-- read at exactly that level, so the burst rows fall out of the same
-- recursion instead of a second fold carrying a weaker invariant.
arr-chains-ledgers : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  all (λ rc → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rc))
      (chainsOf a st) ≡ true →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  nestClosOK?ᵛ (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  all (λ rc → inputsBelowᵛ (pathFloor (proj₂ rc)) (arrTy a) (arrVal a))
      (chainsOf a st) ≡ true →
  depthCascade a nextId (chainsOf a st) sched (cascadeLatch a st) ≤ capsH e sl id →
  chainsCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) 0 a nextId (chainsOf a st) sched
    (cascadeLatch a st)
  × chainsBurstOK (nestBurstAt e sl id) a nextId (chainsOf a st) sched (cascadeLatch a st)
arr-chains-ledgers {e = e} sl id a nextId sched st sleq cok hpz hvc hcl hsv hdp =
  arr-chains-caps-go sl id 0 a nextId (chainsOf a st) sched (cascadeLatch a st)
    sleq ENTRY
    (subst (λ x → capsOK? x sched (cascadeLatch a st) ≡ true)
           (sym (frameStep-0 (capsAt e sl id))) LATCH)
    hpz (cascade-admit-entry (capsAt e sl id) a sched st cok) hsv
    (cascade-admit-park a st (capsOK?-regPark (capsAt e sl id) sched st cok))
    (cascade-admit-ord a sched st (capsOK?-regOrd (capsAt e sl id) sched st cok)) hvc hcl hdp
    0 (Caps.cSize (capsAt e sl id)) 0
    (capsAt-round-size e sl id) base REGLEN ≤-refl
  where
  c   = capsAt e sl id
  LATCH = cascadeLatch-caps (capsAt e sl id) a sched st cok
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  slSz : slotsSize sl ≤ Caps.cSize c
  slSz = ≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl id)
  -- the round has as many positions as the registry has entries, and
  -- the cascade walks a sublist of it
  REGLEN : 0 + length (chainsOf a st) ≤ regAt (Caps.cSize c) (Caps.cReg c) 0
  REGLEN = ≤-trans (≤-trans (chainsOf-length a st)
                            (capsOK?-count c sched st cok))
                   (≤-reflexive (sym (*-identityʳ (Caps.cReg c))))
  -- the cascade's own delivery total, which is what the fold's
  -- invariant is stated over
  DEL = cascadeGo-deliveries
          (λ {n′} {Γ′} {t′} {e′} {u′} → subscribeInner-caps {n′} {Γ′} {t′} {e′} {u′})
          (λ {n′} {Γ′} {t′} {e′} {s′} → innerFinish-caps {n′} {Γ′} {t′} {e′} {s′})
          c d a nextId (chainsOf a st) sl sched (cascadeLatch a st)
          2≤S (1≤capsAt-reg e sl id) (slotsCaps?-capsAt e sl id) sleq
          (cascadeLatch-caps c a sched st cok) hvc hpz (n≤capsAt-size e sl id)
          (subst (length (chainsOf a st) ≤_) (realWidAt-def e sl id)
                 (chains-count-width sl id a sched st cok))
          slSz hdp
          -- the entry reading, both halves local to this fold: the chain
          -- half off the registry the arrival's chains are filtered from,
          -- the payload half `hsv` in the list shape the walk reads
          (chainsOf-strat a st (registry-entStrat c sched st cok))
          (chainsStrat?-one (arrVal a) (chainsOf a st) hsv)
          -- and the chain's two entry readings, both filters of the
          -- registry's own.  The order half is state-blind, so the latch
          -- does not move it; the park half is taken AT the latched
          -- state, which is the state this fold enters
          (chP?-∧ (λ {u} κ → pathOrd? (Sched.nextNode sched) κ)
                  (λ {u} κ → pathPark? κ (cascadeLatch a st)) (chainsOf a st)
             (cascade-admit-ord a sched st (capsOK?-regOrd c sched st cok))
             (cascade-admit-park a st (capsOK?-regPark c sched st cok)))
  ENTRY = ≤-trans (lvls-mono (delivN (cascadeLatch a st)
                                (proj₂ (proj₂ (cascadeGo a nextId (chainsOf a st) sched
                                                 (cascadeLatch a st)))))
                             (cDel c d) 2≤S ≤-refl ≤-refl ≤-refl DEL)
                  (≤-trans (≤-reflexive (sym (sizeCount-body c d)))
                           (m≤m⊔n (sizeCount c d) (Caps.cSize c)))

arr-chains-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  all (λ rc → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rc))
      (chainsOf a st) ≡ true →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  nestClosOK?ᵛ (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  all (λ rc → inputsBelowᵛ (pathFloor (proj₂ rc)) (arrTy a) (arrVal a))
      (chainsOf a st) ≡ true →
  depthCascade a nextId (chainsOf a st) sched (cascadeLatch a st) ≤ capsH e sl id →
  chainsCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) 0 a nextId (chainsOf a st) sched
    (cascadeLatch a st)
arr-chains-caps sl id a nextId sched st sleq cok hpz hvc hcl hsv hdp =
  proj₁ (arr-chains-ledgers sl id a nextId sched st sleq cok hpz hvc hcl hsv hdp)

arr-chains-bursts : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  all (λ rc → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rc))
      (chainsOf a st) ≡ true →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  nestClosOK?ᵛ (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  all (λ rc → inputsBelowᵛ (pathFloor (proj₂ rc)) (arrTy a) (arrVal a))
      (chainsOf a st) ≡ true →
  depthCascade a nextId (chainsOf a st) sched (cascadeLatch a st) ≤ capsH e sl id →
  chainsBurstOK (nestBurstAt e sl id) a nextId (chainsOf a st) sched (cascadeLatch a st)
arr-chains-bursts sl id a nextId sched st sleq cok hpz hvc hcl hsv hdp =
  proj₂ (arr-chains-ledgers sl id a nextId sched st sleq cok hpz hvc hcl hsv hdp)

-- ONE ROUND'S DESCENT AGAINST WHAT THE ROUND CAN SEE.  A cascade
-- descends by crossing `thru-outer` frames and by draining a bounded
-- mergeAll, and both crossings are paid for out of structure that is
-- already present when the round starts: the payload it carries, the
-- store it walks, and the program's own wrap unit.  `sightCeil` is
-- that sum scaled by the program's size.
--
-- WHY THE SCALING IS THE WHOLE CONTENT.  Edge by edge a descent
-- TRADES: what a frame takes off the subject it puts on the path, so
-- the bare sum is an equality along the subscribe walk.  The drain is
-- the one level with no edge to come out of -- it runs under a
-- `from-inner`, which the path measure charges nothing for -- and a
-- program whose folds nest spends one per layer.  So the gap grows
-- with a program parameter the sum does not see.
--
-- AND THE SEEN PARAMETER IS A SIZE, WHICH IS WHY THE SUMMANDS COULD
-- NOT BE MADE BIGGER.  All three of them are NESTING depths, so none
-- moves with how many values an instant carries: at two programs
-- differing only in the delivered count, every quantity this statement
-- reads is identical while the descent moves by a third.  The size is
-- the only sighted thing that separates them, and it enters as a
-- FACTOR because as a summand it is outrun -- one per delivered value
-- against the descent's eight.
--
-- AND THE STORE SLOT IS THE CAP, NOT THE READING, WHICH IS WHAT MAKES
-- THE ROUND INDUCIBLE.  A round states its ceiling once and spends it
-- at every chain, and the chains after the first run on states their
-- predecessors moved -- so the slot has to hold across the walk.  The
-- reading does not: a chain subscribes what its delivery reaches and
-- installs the nodes for it, and both the live fold and the node fold
-- are places the measure reads.  The CAP does, and it costs the
-- consumer nothing, because the arithmetic below already collapses all
-- three of the ceiling's summands to that same cap.
--
-- AND THE STORE IT READS IS THE SYNCHRONOUS ONE -- slots, nodes and
-- registry, with the live fold left out -- because the descent never
-- reads a live.  A live's pending payload is a next-instant quantity:
-- nothing within an instant consumes it, and the measure this bounds
-- reads a deferred body as zero at the node and never at the live at
-- all.  Charging the leaf against the four-place store would make the
-- round hold the live fold under THIS instant's ceiling, which is the
-- next instant's entry bound and is not preservable by any charge
-- this instant's fuel affords.  The three-place store is what a chain
-- can be held to, and it is the weaker premise, so this is the
-- stronger statement.

-- AND THE DESCENT IS A JOIN DOWN THE PATH, WHICH IS WHY THE STATEMENT
-- IS A BODY AND NOT A LEAF.  `depthFold` branches at exactly two heads
-- -- a frame's own spend, and a share sink's dispatch -- and threads
-- the values and the state through everything else, so a ceiling on it
-- is an induction over the path whose only content is that an
-- invariant survives one frame step.  The induction is spelled once,
-- at `.Part7.Depth-Join`, apart from any particular ceiling; what is
-- chosen here is the invariant, and the three leaves below are what
-- that choice owes.
--
-- THE INVARIANT IS THE POSITION'S OWN CEILING, NOT THE STATEMENT'S
-- PARAMETERS, and that is what makes the leaves instantiable where the
-- conclusion is not.  Carrying `storeSyncMax ≤ S` down the path would
-- demand that a frame step move the store not at all, which the walk's
-- own growth bound already says it may; carrying the CEILING lets the
-- values and the store trade against each other, and reduces the step
-- obligation to a comparison between two numerals at states one
-- `stepFrame` apart.  Both sides of that comparison compute, which the
-- descent itself does not.
--
-- REFUTED: `Refuted.Chain-Step-Store` is why the reading could not be
--   carried -- nine before one chain and sixteen after, at the instant
--   the round's own rows are read at, with two further families in the
--   same corpus growing at the same instant.  What died is the plan to
--   thread the entry store across the chains; the growth has to be
--   priced, and pricing it against the cap is what the leaves below do.
-- DEAD ROUTE: descending into `depthE` and spending `depthE-sighted`
--   cannot close this.  That ceiling carries the FOLD's grant in its
--   subject place -- a tower over the payload -- where this one
--   carries the arrival's own nesting, and two upper bounds stated in
--   different currencies do not compose.  The delivery side needs its
--   own value-nesting walk, which is what the leaf below states.
-- REFUTED: `Refuted.Cascade-Deliv-Depth` is the delivery-side witness
--   the ceiling is calibrated against -- a limit-one mergeAll over
--   three inners, read at the second cascade, whose descent climbs six
--   per fold layer against the bare sum's four.
-- DEAD ROUTE: re-threading a slacker `S` so that a proven monotonicity
--   carries an entry row forward cannot close the coverage gap above,
--   and the reason is that the gap is on the wrong side of the
--   statement.  The round already threads a cap-denominated `S`
--   unchanged across its chains and already re-establishes the store
--   premise at each stepped state, by `chainStep-store≤`, which is
--   proven.  So the premise was never what the rows could not reach.
--   What they cannot reach is the CONCLUSION, whose subject is the
--   state itself: nothing transports `depthChain` from a state to one
--   a chain has stepped, and every consumer in this family takes the
--   descent bound as a HYPOTHESIS rather than establishing it, so
--   there is no monotonicity to borrow.  Slackening `S` only weakens a
--   premise that is already discharged, and moves no risk off this
--   leaf onto the round.
-- DEAD ROUTE: the compiled harness cannot price this descent at a
--   registry a consumer walks at, and the barrier is not an instrument
--   that is missing.  Its one advantage is running bodies the checker
--   will not unfold, and `Caps-Depth` seals nothing at all; what blocks
--   the descent is a doubling per registered share path, recorded at the
--   clause responsible, and speed is a constant against a `2ⁿ`.  The
--   route is therefore dead in the LENGTH and not in the kind -- a
--   handful of admitted paths prices in an instant, as the sibling
--   below's rows show -- so what no row can reach is the length at
--   which the doubling bites, which is the length every consumer here
--   stands at.

-- ONE FRAME'S OWN SPEND.  `depthFrame` is flatly nought at map, scan
-- and take, so the whole claim is the two arms that charge: the
-- `from-inner` react, and the `thru-outer` walk that sits a successor
-- above it.
-- PROBED: `Probed.Depth-Join` covers BOTH arms that charge.  The
--   `from-inner` one is read at the first chain a round admits, whose
--   path is headed by it over three frames, against the ceiling at the
--   state the cascade hands the chain.  The `thru-outer` one -- the
--   larger, a successor above the react -- is read at an ASSEMBLED
--   frame and state rather than a walked one, at two inner nestings so
--   a pass surviving only a flat arrival is not one.  The residue is
--   therefore the state axis at that arm, not the arm.
postulate
  frame-depth-fit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sl : Slots Γ) (sf : Gas) (bid : Id) (now : Tick)
    (f : Frame Γ s u) (p : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl → sf ≡ budgetAt e sl bid →
    depthFrame sf bid now f p vals fin sched st
      ≤ sightCeil (sizeᵉ e) (nestDᵛˢ vals) (storeSyncMax sched st) (nestUnit e sl)

-- THE FOLD HALF OF WHAT THE SHARE SINK OWES, over the registrations a
-- share admits rather than the frames a path crosses.  It is
-- `depthFold` again, so it inherits the parent's obstruction rather
-- than the sibling's -- which is why the two no longer share a block.
--
-- AND THE BARRIER IS A SIZE, NOT A KIND, which is the correction a
-- measurement made to what this block used to assert.  It said no
-- instrument reached the conclusion, and read that off the parent
-- instead of off a row; both things that would have had to hold for it
-- fail.  `Caps-Depth` seals nothing, so opacity is not the obstruction;
-- and `Gas` is a lazy datatype built to be peeled, so the budget the
-- hypothesis pins `sf` to does not carry the anchor's divergence into
-- this side either.  What is actually there is `depthShareGo`'s two
-- recursive calls per admitted path -- a `2ⁿ` stated at the clause
-- responsible.  So the conclusion computes, and computes fast, at a
-- registry of a handful.

-- AND THAT COST IS THE INSTRUMENT'S, NOT A REGION OF THE STATEMENT,
-- which is what a second measurement corrected.  The length was read as
-- the region this row still rested on; it cannot be, on two counts a
-- reader can check off the type.  The statement is over ONE path, so an
-- admitted LIST is not a parameter of it at all; and both places a
-- length could enter its value -- the share fold over admitted paths,
-- and the frame arm along the path itself -- combine by `⊔`.  A max is
-- raised by a DEEPER member and never by another member, so a count
-- moves the left side only through the state it threads, which moves
-- the right side too by `storeSyncMax`.  An axis that moves both sides
-- cannot refute, and the length was the one every plan here had aimed
-- at.

-- AND THE VALUE AXIS RUNS THE SAME WAY, WHICH IS THE ONE THAT WAS
-- EXPECTED TO BITE.  It is the only axis that moves BOTH sides on
-- purpose -- the ceiling's second argument is exactly the values' nest
-- depth -- so which side moves faster is the whole question, and it is
-- arithmetic rather than a matter of coverage.  A nesting level buys
-- the ceiling `suc (sizeᵉ e)`, since that is the factor `sightCeil`
-- multiplies its summands by, and the factor is at least two at any
-- program with a term in it.  It buys the fold AT MOST one, and only
-- while a frame is left to spend it: the whole family combines by `⊔`
-- but for two `suc` sites, and the one on this arc is `depthFrame`'s
-- `thru-outer`, so a path charges once per FRAME and not once per
-- level nested beneath it.  The fold is therefore capped by the path
-- while the ceiling keeps climbing, and the axis that was the last
-- candidate to refute is the one that cannot.

-- SO THE RESIDUE IS ONE FRAME'S CHARGE AND ONE PATH'S DEPTH, and the
-- first of those is the sibling directly above rather than anything new.
-- The ceiling names no path, which reads as the shape a conclusion takes
-- when no hypothesis carries what it needs -- and the sibling ceiling
-- this development spends for the same currency does carry one, since
-- `fitG` (.Nest-Store) sums `pathNestD κ` into it.  The two are
-- reconciled by where the path CONTRIBUTES: by descent under a `Sight`,
-- where each frame's charge accumulates, and by `⊔` here, where the
-- whole path can charge no more than its heaviest frame.  A path-free
-- ceiling is therefore the right shape for this side, and what it needs
-- is that one frame's charge be bounded by what the values and the store
-- already pay for.

-- AND THE CEILING IS READ AT THE GRANT, NOT AT THE STATE THE FOLD WAS
-- ENTERED AT, which is the correction the assembly forced.  The two
-- axes enter `sightCeil` as a SUM, so a ceiling naming the entry
-- state's own two readings is strictly SMALLER than one naming a grant
-- that covers both -- and every instrument this side has is denominated
-- in the grant.  The statement was therefore stronger than anything
-- available and stronger than anything wanted: its one consumer weakens
-- it to the grant form by `sightCeil-mono` on the line it is spent, out
-- of premises that consumer already holds.  So the grant form costs the
-- consumer nothing and is what the walk's own invariant carries.
--
-- AND THE ASSEMBLY IS THEN THE CHAIN FACE'S, ARM FOR ARM, WITH ONE ARM
-- OWING A WALK RATHER THAN A BOUND.  `fold-le` over `ChainFit sl S` is
-- the induction, and two of its three obligations have routes already
-- walked on the chain side: the frame arm is the sibling above weakened
-- by `sightCeil-mono`, and the step arm is `chain-fit-step` verbatim.
-- The SINK arm owes `disp-depth-fit`, which is proven FROM this
-- statement, so the pair recurs through the fold gas -- and the
-- dispatch asks its own fold premise at a gas STRICTLY BELOW the one it
-- was entered at, which is the ordering that recursion is walked on.
-- What is left is to walk it: an induction on the gas whose step is
-- this statement at every smaller one, the other two arms supplied
-- unchanged.
-- DEAD ROUTE: closing the sink arm by STRUCTURAL mutual recursion is
--   dead however the dispatch is stated, which is a fact about the
--   measure and not about a signature.  The fold reaches its sink at
--   the gas it is holding, so the fold-to-dispatch edge is FLAT: no
--   argument of either statement decreases across it, and the cycle's
--   one decrease is the peel the dispatch performs an edge later.  A
--   pair whose cycle decreases while an edge of it does not is not
--   structural, so the walk has to be an explicit induction on the gas.
-- TWIN: `chain-depth-sighted` -- this statement on the chain face, at
--   the same ceiling in the same currency, proven by exactly the
--   `fold-le` instantiation described above.
postulate
  share-fold-fit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (bid : Id) (now : Tick)
    (S : ℕ) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (rid : RegId) (p : Path Γ (lookup Γ i) t)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl → sf ≡ budgetAt e sl bid →
    nestΦAt e sl id ≤ S →
    nestDᵛˢ vals ≤ S →
    storeSyncMax sched st ≤ S →
    depthFold sf gas bid now (Fin.toℕ i) p vals
      (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched
      (record st { delivered = rid ∷ EvalSt.delivered st })
      ≤ sightCeil (sizeᵉ e) S S (nestUnit e sl)

-- AND THE STEP HALF, WHICH IS REACHED.  Its `rid` and `p` are exactly a
-- `shareAdmit` entry, so a point is whatever the shared slot has
-- registered where the row stands -- and what decides whether it has
-- registered anything is the DEF.  A share whose def COMPLETES leaves
-- none: `sharedConnect` subscribes the def, asks whether the burst came
-- back completed, and on yes drops every registration on that source
-- before it returns, so the entry is written and does not survive the
-- call that writes it.  A def built from one-shots can therefore never
-- leave one, which is why the corpus this face is otherwise
-- instantiated at admits nothing at either connect timing -- both its
-- families share the def that decides it, and neither wrapper alters
-- that.
--
-- WHAT CLEARS IT IS A DEF THAT OUTLIVES ITS OWN CONNECT, and the
-- telescope invariant is what puts that outside that corpus rather than
-- outside reach: a slot's def may name only strictly earlier slots, so
-- a nought-indexed share reaches no scripted source and every def open
-- to it is synchronous.  A share at a LATER index over a scripted slot
-- below it is the shape that clears this, and the rows below stand at
-- one -- a share over an empty hot, a source that never fires and so
-- never completes.
--
-- AN OBSERVABLE-TYPED SLOT IS WHAT PUTS THE SUBSCRIBING ARM UNDER A
-- SHARE.  `p` is the registered chain, so its head decides what
-- `foldPath` does, and a `thru-outer` head is written only by
-- `subscribeAll`, which subscribes its OUTER under one -- so the share
-- must BE the outer, and an outer is typed `obs u`.  `Rx.Slots` permits
-- exactly one way to carry that type: `scripted` is barred at a
-- non-data type, `shared` is not, which is the shape wanted anyway
-- since only a shared slot has an admit list.  One slot further and the
-- chain sinks into a LATER share rather than the root, which is
-- `foldPath`'s recursive arm.

-- AND `scan-f` IS THE ARM THAT KILLS IT.  `storeSyncMax` maximises over
-- slots, nodes and registry.  Of the three arms the rows below miss,
-- `map-f` returns the schedule and store it was handed, and `take-f`
-- only ever shrinks them -- it drops registrations, sweeps the live set
-- and stores a numeral.  `scan-f` writes a node back with a fresh
-- ACCUMULATOR, and at an observable-typed accumulator that value
-- carries nesting of its own, so `nodeNest` grows across the very step
-- the conclusion says cannot grow.  A step function wrapping the
-- previous accumulator once per delivered value takes the store from
-- two to three and the ceiling up with it, on a chain a share whose def
-- never completes actually admits.
--
-- SO PRESERVATION IS THE WRONG SHAPE FOR THIS OBLIGATION, and what
-- stands in its place is a PRICE denominated in the round's own grant:
-- the fold leaves the store under whatever ceiling the walk entered
-- under, PROVIDED that ceiling already covers what one instant of this
-- program can add.  A price of that form chains where a repaired
-- preservation could not have: the grant is ONE number for the whole
-- round and the bound is a join against it, so a fan-out of any width
-- climbs no further than a single registration does, and the count the
-- dispatch would otherwise have had to carry never enters the bound.
--
-- AND IT IS SEALED ON BOTH SIDES, WHICH IS WHAT STATING IT COSTS.  The
-- grant belongs to the nesting tower's abstract block, so it reduces at
-- no program: the premise cannot be discharged at a numeral and the
-- conclusion compares against a symbol.  Anything smaller that WOULD
-- reduce is too small to pay -- the wrap unit is fixed by the program
-- text, while a scan wrapping its accumulator once per delivered value
-- is not -- so the region this leaf is risky in is closed to
-- instantiation exactly as the fold obligation above it is, and it
-- moves only by proof.
-- REFUTED: `Refuted.Share-Step-Scan` is why the conclusion is a price
--   rather than a preservation.  It crosses the old second conjunct at
--   a `scan-f` head over an `obs`-typed accumulator, taking `rid` and
--   `p` off `shareAdmit` at the state the subscribe returned; the
--   ceiling goes 78 to 91 across the fold.
-- TWIN: `chainStep-store≤` prices a whole chain's step in this same
--   currency and is proven, which is what says the shape is right.  It
--   is also what says the route is not mechanical: that proof spends
--   the round's caps package, and a fold standing inside one chain does
--   not hold one.
postulate
  share-fold-store≤ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (bid : Id) (now : Tick)
    (S : ℕ) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (rid : RegId) (p : Path Γ (lookup Γ i) t)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl → sf ≡ budgetAt e sl bid →
    nestΦAt e sl id ≤ S →
    storeSyncMax sched st ≤ S →
    storeSyncMax
      (proj₁ (proj₂ (foldPath sf gas bid now (Fin.toℕ i) p vals
         (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched
         (record st { delivered = rid ∷ EvalSt.delivered st }))))
      (proj₂ (proj₂ (foldPath sf gas bid now (Fin.toℕ i) p vals
         (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched
         (record st { delivered = rid ∷ EvalSt.delivered st }))))
      ≤ S

-- AND THE PAIR THE DISPATCH ACTUALLY WALKS WITH, which is that price
-- beside the vocabulary fact -- and the vocabulary half is not a gap at
-- all: a fold threads the slots untouched, and that is proven.
share-step-fit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (bid : Id) (now : Tick)
  (S : ℕ) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (rid : RegId) (p : Path Γ (lookup Γ i) t)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → sf ≡ budgetAt e sl bid →
  nestΦAt e sl id ≤ S →
  storeSyncMax sched st ≤ S →
  (Sched.slots (proj₁ (proj₂ (foldPath sf gas bid now (Fin.toℕ i) p vals
     (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched
     (record st { delivered = rid ∷ EvalSt.delivered st })))) ≡ sl)
  × (storeSyncMax
       (proj₁ (proj₂ (foldPath sf gas bid now (Fin.toℕ i) p vals
          (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched
          (record st { delivered = rid ∷ EvalSt.delivered st }))))
       (proj₂ (proj₂ (foldPath sf gas bid now (Fin.toℕ i) p vals
          (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched
          (record st { delivered = rid ∷ EvalSt.delivered st }))))
     ≤ S)
share-step-fit sl id sf gas bid now S i vals fin rid p sched st hsl hsf hΦ hS =
  trans (foldPath-slots sf gas bid now (Fin.toℕ i) p vals
           (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched
           (record st { delivered = rid ∷ EvalSt.delivered st }))
        hsl
  , share-fold-store≤ sl id sf gas bid now S i vals fin rid p sched st
      hsl hsf hΦ hS

-- THE SHARE SINK IS THE SAME INDUCTION ONE LEVEL DOWN, over the
-- registrations the share admits rather than over the path -- and the
-- invariant is the same shape, so the weakening down the list is the
-- identity and only the two state-moving obligations are owed.  What
-- the fan-out costs is therefore stated at ONE registration, which is
-- the smallest unit anything here can be instantiated at.
--
-- AND ITS CEILING IS READ OFF THE GRANT RATHER THAN OFF THE STATE IT
-- WAS ENTERED AT, which is what the priced step forces and is no loss:
-- the walk's own invariant is now the two ingredient bounds separately
-- -- the payload under the grant and the store under the ceiling's
-- store slot -- so each position recovers its ceiling by monotonicity
-- and the one number the dispatch states is spent unchanged at every
-- registration.
disp-depth-fit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (bid : Id) (now : Tick)
  (S : ℕ) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → sf ≡ budgetAt e sl bid →
  nestΦAt e sl id ≤ S →
  nestDᵛˢ vals ≤ S →
  storeSyncMax sched st ≤ S →
  depthDisp sf gas bid now i vals fin sched st
    ≤ sightCeil (sizeᵉ e) S S (nestUnit e sl)
disp-depth-fit {e = e} sl id sf gas bid now S i vals fin sched st hsl hsf hΦ hval hS =
  disp-le D sf gas bid now i vals fin
    (λ _ sch sto → (Sched.slots sch ≡ sl) × (storeSyncMax sch sto ≤ S))
    (λ g _ rid p ps sch sto q →
       share-fold-fit sl id sf g bid now S i vals fin rid p sch sto
         (proj₁ q) hsf hΦ hval (proj₂ q))
    (λ rid p ps sch sto q → q)
    (λ g _ rid p ps sch sto q →
       share-step-fit sl id sf g bid now S i vals fin rid p sch sto
         (proj₁ q) hsf hΦ (proj₂ q))
    sched st
    (hsl , ≤-trans (≤-reflexive (latch-sync i fin sched st)) hS)
  where
  D : ℕ
  D = sightCeil (sizeᵉ e) S S (nestUnit e sl)

-- AND THE STEP THAT FRAME MAKES IS PRICED THE SAME WAY, on both axes
-- the ceiling reads: what the frame EMITS stays under the round's
-- grant, and the state it leaves stays under the walk's ceiling.  The
-- two are one obligation split, because one arm moves both -- a scan's
-- emitted values ARE the accumulator it writes back into the nodes, so
-- an `obs`-typed accumulator deepens the payload axis and the store
-- axis together and there is no trade between them to be had.
--
-- WHICH IS WHY THE WALK CARRIES THE INGREDIENTS AND NOT THE CEILING.
-- Holding a combination lets a position pay for a deeper payload out of
-- a shallower store, and that is exactly the exchange the arm that
-- charges refuses; holding the two bounds separately asks each axis for
-- what it can actually supply, and the ceiling is then recovered at
-- each position by monotonicity rather than transported across a step.
-- REFUTED: `Refuted.Share-Step-Scan` at the chain's own frame rather
--   than at the fold around it: under the old combined form the ceiling
--   goes 78 to 130 across one `stepFrame`, which is further than the
--   fold half moves at the same point.
-- TWIN: `chainStep-store≤` -- the store axis of this, priced in the
--   same currency at the granularity of a whole chain, and proven.
postulate
  step-frame-store≤ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (bid : Id) (now : Tick) (S : ℕ)
    (f : Frame Γ s u) (p : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl → sf ≡ budgetAt e sl bid →
    nestΦAt e sl id ≤ S →
    nestDᵛˢ vals ≤ S →
    storeSyncMax sched st ≤ S →
    storeSyncMax (proj₁ (proj₂ (proj₂ (proj₂
                    (stepFrame sf bid now f p vals fin sched st)))))
                 (proj₂ (proj₂ (proj₂ (proj₂
                    (stepFrame sf bid now f p vals fin sched st)))))
      ≤ S

-- READING A GRANT BACK OUT OF THE POTENTIAL, which is what lets the
-- two leaf obligations below go on being stated against one number
-- while the invariant that reaches them steps.  The potential charges
-- a value at the factor of the path still to be walked, and that
-- factor is at least one, so the values' own maximum is under the
-- potential's ceiling with the path's share left unspent.
Φ-vals≤ : ∀ {n} {Γ : Ctx n} {u t} (B U S : ℕ) (p : Path Γ u t)
  (vals : List (Val Γ u)) → valsΦ? B U p vals ≡ true → U ≤ S →
  nestDᵛˢ vals ≤ S
Φ-vals≤ B U S p vals hΦ hUS =
  ≤-trans (≤-trans (≤-trans (≤-reflexive (sym (*-identityˡ (nestDᵛˢ vals))))
                            (*-monoˡ-≤ (nestDᵛˢ vals) (pathΦF-pos B p)))
                   (Φ-to-bound B U p vals hΦ))
          hUS

-- the three things a position is entered with: the vocabulary, the
-- payload's POTENTIAL at the path still ahead of it, and the store
-- under the ceiling's own store slot.
--
-- AND THE MIDDLE ONE IS NOT A NUMBER, WHICH IS THE WHOLE CORRECTION.
-- A fixed grant on what a frame emits dies at the arms that
-- substitute: the frame is quantified over, so its step function's
-- body is chosen after the grant is, and one layer deeper than any of
-- them admits.  The potential reads the payload at the factor and
-- summand of what remains to be walked, so a position's reading
-- changes as the path shortens -- which is what a term minted at the
-- position can be charged against.
-- REFUTED: `Refuted.Step-Frame-Vals-Map` -- the grant form this
--   replaces, at a step function one layer deeper than whatever the
--   numeric hypotheses admit.
ChainFit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (sl : Slots Γ) (id : ℕ)
  (S : ℕ)
  {v} → Path Γ v t → List (Val Γ v) → Bool → Sched Γ → EvalSt e → Set
ChainFit {e = e} sl id S p vals _ sch sto =
  (Sched.slots sch ≡ sl)
  × (valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id) p vals ≡ true)
  × (storeSyncMax sch sto ≤ S)

-- AND THE FRAME'S OWN STEP RE-ESTABLISHES ALL THREE, the vocabulary
-- half out of the proven fact that a frame threads the slots untouched,
-- the payload half out of the walk face's own transport, and the store
-- half out of the priced leaf above.
chain-fit-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (bid : Id) (now : Tick) (S : ℕ)
  (f : Frame Γ s u) (p : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → sf ≡ budgetAt e sl bid →
  nestΦAt e sl id ≤ S →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id) (f ↠ p) vals ≡ true →
  storeSyncMax sched st ≤ S →
  ChainFit sl id S p
    (proj₁ (stepFrame sf bid now f p vals fin sched st))
    (proj₁ (proj₂ (proj₂ (stepFrame sf bid now f p vals fin sched st))))
    (proj₁ (proj₂ (proj₂ (proj₂ (stepFrame sf bid now f p vals fin sched st)))))
    (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf bid now f p vals fin sched st)))))
chain-fit-step {e = e} sl id sf bid now S f p vals fin sched st hsl hsf hΦ hval hS =
  trans (stepFrame-slots sf bid now f p vals fin sched st) hsl
  , stepFrame-nest-Φ sf bid now f p vals fin sched st
      (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id) hval
      (chain-frame-ΦHyp sl id sf bid now S f p vals fin sched st hsl hsf hval hS)
  , step-frame-store≤ sl id sf bid now S f p vals fin sched st hsl hsf hΦ
      (Φ-vals≤ (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id) S (f ↠ p) vals
         hval hΦ)
      hS

chain-depth-sighted : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id) (S : ℕ)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  nestΦAt e sl id ≤ S →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id) path
         (arrVal a ∷ []) ≡ true →
  storeSyncMax sched st ≤ S →
  depthChain nextId a path sched st
    ≤ sightCeil (sizeᵉ e) S S (nestUnit e sl)
chain-depth-sighted {n = n} {e = e} sl id a nextId S path sched st hsl hΦ hval hS =
  fold-le C sf n nextId (arrTick a) (arrSource a)
    (λ {v} → ChainFit sl id S {v})
    (λ f p′ vals fin sch sto h →
       ≤-trans (frame-depth-fit sl sf nextId (arrTick a) f p′ vals fin sch sto
                  (proj₁ h) hsf)
               (sightCeil-mono (sizeᵉ e) (nestUnit e sl)
                  (Φ-vals≤ B (nestΦAt e sl id) S (f ↠ p′) vals
                     (proj₁ (proj₂ h)) hΦ)
                  (proj₂ (proj₂ h))))
    (λ i vals fin sch sto h →
       disp-depth-fit sl id sf n nextId (arrTick a) S i vals fin sch sto
         (proj₁ h) hsf hΦ
         (Φ-vals≤ B (nestΦAt e sl id) S (share-sink i) vals
            (proj₁ (proj₂ h)) hΦ)
         (proj₂ (proj₂ h)))
    (λ f p′ vals fin sch sto h →
       chain-fit-step sl id sf nextId (arrTick a) S f p′ vals fin sch sto
         (proj₁ h) hsf hΦ (proj₁ (proj₂ h)) (proj₂ (proj₂ h)))
    path (arrVal a ∷ [])
    (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    (Arrival.isLast a) sched st
    (hsl , hval , hS)
  where
  B : ℕ
  B = Caps.cSize (capsAt e sl id)
  C : ℕ
  C = sightCeil (sizeᵉ e) S S (nestUnit e sl)
  sf : Gas
  sf = budgetAt e (Sched.slots sched) nextId
  hsf : sf ≡ budgetAt e sl nextId
  hsf = cong (λ z → budgetAt e z nextId) hsl

-- AND THE BOUND SURVIVES A CHAIN, which is the other half of the same
-- design: the round states its ceiling once and spends it at every
-- later chain, so what a chain may do to the store is exactly what the
-- bound has to absorb.
--
-- AND IT IS NOT A COROLLARY OF THE GROWTH BOUND THIS TREE ALREADY HAS,
-- WHICH IS THE WHOLE OF WHY IT IS A LEAF.  The walk's own store bound
-- lands at the SUCCESSOR cap -- a factor times the cap plus an
-- increment, which is by definition the next instant's -- and the tick
-- statement above it spends exactly that to close an instant.  So the
-- discipline says a round STARTS under its own cap and ENDS under the
-- next one, and says nothing about the states between.  What this leaf
-- claims is that the growth an instant actually performs stays under
-- the instant's own cap, which is the design's intent and is not
-- anywhere derived.  Neither side of it can be instantiated: the cap
-- sits on the caps recurrence, which does not terminate even natively.
-- AND THE STORE IS FOUR PLACES UNDER ONE `⊔`, SO THIS SPLITS FOUR WAYS
-- RATHER THAN INDUCTING ONCE, which is the same split the round's
-- growth statement takes and for the same reason: the four arms are
-- nowhere near equally hard.  The slot arm needs no leaf at all -- a
-- chain threads the vocabulary untouched, so its sum is the one the
-- entry cap already covers -- and the three that survive are each a
-- statement about one thing a delivery writes.
-- THE THREE ARMS PRICE THE GROWTH AGAINST THE PROGRAM AND NOT AGAINST
-- THE STORE THEY START FROM, and that shape is forced rather than
-- chosen.  A growth priced against the entry store COMPOUNDS: each
-- chain's bound is the previous chain's, so no ceiling stated once
-- survives a walk of unknown length.  Charging the increment instead
-- makes preservation a condition on the BOUND -- it holds as soon as
-- the bound already covers one instant's increment -- which is a
-- condition the round discharges once, at its entry, rather than a
-- condition the walk has to re-establish per chain.
--
-- AND THE CHARGE IS THE SAME ONE THE FIRST SUBSCRIPTION PAYS.  The
-- floor rows for a program's own subscribe frame are stated at exactly
-- this quantity, so the three arms are that statement moved from the
-- opening frame to an arbitrary chain, and the two are refutable
-- together at any program where a chain outgrows a first subscription.
--
-- THE UNCONDITIONAL GROWTH BOUND BESIDE THEM CANNOT SUPPLY IT, AND
-- THAT IS WORTH KNOWING BEFORE ANYONE TRIES.  Two of that bound's
-- three disjuncts are places the store measure reads, so the entry
-- bound covers them outright; the third is the chain's own PATH factor
-- times the arrival's size, and the path factor is a PRODUCT over the
-- path's frames while the increment is linear in the caps at the
-- instant.  The product outruns it, and no premise the round can
-- supply changes that -- a legal path of length the size cap already
-- carries a factor exponential in that cap.

-- AND THE CHARGE MAY NOT BE DEPTH-DENOMINATED, WHICH IS WHY IT IS THE
-- INCREMENT AND NOT SOMETHING SMALLER.  The cheap repair replaces the
-- path PRODUCT by the path's additive depth, which holds at every
-- family the corpus reaches -- exactly, four against four, at the
-- transforming frame.  It fails one step further along that same
-- family: both nesting-depth measures read ZERO into a `deferᵉ` body,
-- so a `map-f` whose function is a deferred constant hands the frame a
-- value as deep as the constant while the charge does not move at all.
-- Whatever pays for these arms has to see inside a deferred body, and
-- only a SIZE measure does -- which the size cap carries and no
-- depth-built quantity does.
--
-- AND THE SIZE CAP IS THE LARGEST CHARGE THE FUEL CAN AFFORD, WHICH IS
-- WHY IT IS THAT AND NOT THE INSTANT'S INCREMENT.  A bound covering
-- one chain's growth is not the cap, so the round's ceiling reads the
-- cap PLUS the charge and each half is priced by its own copy of the
-- exponential -- and the fuel carries exactly two.  The size cap fits
-- under one with room, being a quadratic under a double exponential of
-- itself.  Everything about this is index-aligned by construction: the
-- exponential room this face runs on prices no summand at the cap
-- after the one being bounded, so a charge naming the next instant is
-- unaffordable however true it is, and reading the ceiling at the
-- SUCCESSOR cap instead is dead for the same reason.
--
-- AND THE PATH PREMISE IS NOT A CONVENIENCE.  A charge naming the
-- program alone cannot hold against a path built by hand: the path is
-- universally quantified, a frame carries its own function, and a
-- frame whose function wraps twenty times installs a node twenty deep
-- against a program that never mentions it.  So the unconditional form
-- is FALSE and the conditioned one replaces it rather than weakening
-- it.  The premise costs the consumer nothing -- the walk's own caller
-- derives it from the caps invariant it already holds, one
-- application, so it is a fact the round has rather than a fact the
-- round must acquire.
--

-- AND THIS ONE CARRIES THE CHAIN'S OWN DEPTH, which the two arms above
-- do not.  A registration this chain mints sits at the frames of the
-- subscribed value over the REMAINING path, so its depth is the
-- arrival's nesting plus the path's -- and neither of the other
-- premises reaches that quantity: the size premise is about the
-- payload's syntax and `pathSz?` bounds each frame's SIZE and the
-- path's LENGTH, which together allow a nesting quadratic in the cap.
-- The premise is the tree's own cascade-level reading taken one chain
-- at a time, so it is derived where the arm is spent rather than
-- assumed: the selection comes from the registry, and the registry's
-- join is already under the unit there.
--
-- THE BODY IS THE WALK, and the charge it spends is the unit under the
-- path's own FACTOR.  Substitution is multiplicative in this currency,
-- so a walk that survives a map frame carries the factor the frames can
-- still apply -- and the size premise is what bounds it without reading
-- the run: each frame's size is under the cap and the path's length is
-- too, so the factor is two to the cap SQUARED and no more.
-- THE PATH'S OWN DEPTH ONLY GROWS ROOTWARD, which is what lets a
-- premise taken at the chain's entry be spent at every frame the walk
-- reaches: four clauses add a term's depth or nothing, and the outer
-- frame adds one.
