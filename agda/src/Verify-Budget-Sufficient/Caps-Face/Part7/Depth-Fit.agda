-- Verify-Budget-Sufficient.Caps-Face.Part7.Depth-Fit
-- pathNestD-step … caps-tick
module Verify-Budget-Sufficient.Caps-Face.Part7.Depth-Fit where

open import Data.Bool    using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (*-assoc; ≤ᵇ⇒≤; ≤⇒≤ᵇ; ^-monoʳ-≤; *-monoˡ-≤; *-cancelˡ-≤; ≤-trans; ≤-refl; ≤-reflexive; m≤m+n;
  m≤n+m; n≤1+n; *-identityʳ; *-mono-≤; *-monoʳ-≤; +-monoʳ-≤; +-monoˡ-≤; ⊔-lub; m≤m⊔n; m≤n⊔m;
  +-mono-≤; +-suc; +-assoc; *-distribʳ-+)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; _++_; length; foldr)
open import Data.Bool.ListAction using (all; any)
open import Data.Fin     using (Fin; toℕ)
import Data.Fin as Fin
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Empty   using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Data.Unit    using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; subst; cong)

open import Rx.Prim      using (Tick; Id; _at_from_as_; Gas; after_,_; close; exhausted;
                                Source; InstEvent)
open import Rx.Exp       using (obs; Ctx; Closed; Val; Fn; _×ᵗ_; _≟ᵗ_; sizeᵉ; sizeᵛ;
  inputsBelowᵛ)
open import Rx.Nest-Depth using (nestDᵛ; nestDᵗ)
open import Verify-Budget-Sufficient.Depth-Sighted using (ValsFit; valsFit-of-max)
open import Verify-Budget-Sufficient.Nest-Walk using
  (nestDᵛˢ; nodeNestAt; capsDrainOK; FaceOK; faceOK; frameDrainOK; capsWalkOK; dispatchCapsOK;
  shareCapsOK; capsWalkOK-strat)
open import Verify-Budget-Sufficient.Nest-Burst using (drainW)
open import Verify-Budget-Sufficient.Nest-Cap using (nestFac; nestU)
open import Verify-Budget-Sufficient.Deliveries using
  (delivN)
open import Verify-Budget-Sufficient.Walk-Factor using
  (pathΦF; pathΦF-cap-atLen; pathFrameSz?; pathSz?-frames; pathΦD; pathΦD-len; pathSzL?;
  pathSzL?-frames; pathSzL?-len; pathSz?-szL)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using
  (foldPath-nest-regs; PathΦHyp; DispatchΦHyp; ShareGoΦHyp; FrameΦHyp; InnerΦBody; valsΦ?;
  stepFrame-nest-Φ; Φ-to-bound)
open import Verify-Budget-Sufficient.Nodes-Nest-Walk using (foldPath-nest-nodes)
open import Verify-Budget-Sufficient.Nest-Ceiling using
  (Reached; Ent; Pos; base; walk; ent-step)
open import Verify-Budget-Sufficient.Nest-Store using
  (chainsNestD; pathNestD; storeSyncMax; storeSyncMax≤storeNestMax; storeSyncMax-lub;
  storeSync-slots≤; storeSync-nodes≤; storeSync-regs≤; nestCapAt; nestOK?; nestUnit;
  slotsNestSum; nodeNest; regsNestMax; sightCeil; slotWrapSum; nestCapAt-0; nestCap-mono₀;
  nestOK?-latch; nestOK?-store; shareAdmit-nest; storeNest-regs≤)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; arrVal; RegId; lookupNode; NodeId; _↠_; Frame; AllOp; map-f; scan-f;
  take-f; from-inner; thru-outer; cascadeLatch; chainsOf; cascadeGo; Path; arrTy; stepFrame;
  cascade; share-sink; root; chainStep; budgetAt; arrSource; arrTick; shareAdmit; shareLatch;
  foldPath; NodeState; mergeAll-st; scan-st; take-st; switch-st; exhaust-st; regAt; lvls)
open import Rx.Slots using (Slots; slotsSize)

open import Verify-Budget-Sufficient.Caps using
  (1≤capsAt-reg; 2≤capsAt-size; 8≤capsAt-size; Caps; capsAt; capsAt-base-size; capsH; frameStep;
  frameStep-0; sizeCount; iterSize-infl; iterSize-mono-count; frameStep-mono-j; _⊑ᶜ_;
  lvls-mono)
open import Verify-Budget-Sufficient.Measures using
  (pathLen; ∧-true; 2X≡X+X; all-impl)
open import Verify-Budget-Sufficient.Keeps-Ring using
  (KeepsC; stepFrame-keeps)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthCascade; depthReact; depthFrame; depthFold; depthDisp; depthShareGo; depthChain; lub3-l;
  lub3-m; lub3-r)

open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (capsAt-round-size; capsOK?; capsOK?-mono; frameSz?; n≤capsAt-size; pathFloor; pathPark?;
  pathStrat?; pathSz?; pathSz?-widen; regsSz?; valCaps?; nestClosOK?ᵛ; parkStrat?; framePark?;
  framePark?-own; regOwn?; nestClosOK?ᵛ-widen; pathOrd?; pathOrd?-outer)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (capsOK?-count; capsOK?-regs; chainsStrat?-one; pathPark-delivered; pathsPark-delivered; pathSz?-len;
  registry-entStrat; slotsCaps?-capsAt; valsCaps?; valsCaps?-lvl; foldPath-slots;
  shareAdmit-caps; capsOK?-delivered; capsOK?-regOrd; capsOK?-regPark)
open import Verify-Budget-Sufficient.Delivery-Walk using
  (shareAdmit-chP)
open import Verify-Budget-Sufficient.Psi-Split using
  (chP?-∧)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Strat-Leaves using
  (cascade-admit-park; chainStep-park; chainsOf-strat;
   cascade-admit-ord; chainStep-ord)
open import Verify-Budget-Sufficient.Caps-Face.Part6 using
  (SiCType; IfcType)
open import Verify-Budget-Sufficient.Caps-Face.Part3 using
  (valCaps?-size; valCaps?-widen)
open import Decide using (T-to; T⇒≡true; ∧-intro; ∧-trueˡ; ∧-trueʳ; ≡ᵇ-refl; ≤ᵇ-true)
open import Verify-Budget-Sufficient.Caps-Face.Nest-Arith using
  (nestWalkAt-def; nestΦAt; nestΦ-sight≤capsH; nestCapAt≤nestΦAt; nestWalkAt≤nestΦAt;
  walkExpL-widen; nestΦ-frame-charge)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Caps using
  (cascadeFinish-caps; cascadeGo-caps; cascadeLatch-caps; chainStep-slots; chainsOf-caps; chainsOf-length)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Ring-Vocabulary using
  (floor-parts)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Nest using
  (arr-chains-nest-syn)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Arrival-Caps using
  (cascade-admit-entry; chain-depth-sighted; arr-chain-caps; chainStep-caps;
   chain-deliv-cap)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Chain-Caps-OK using
  (chainCapsOK; chainsCapsAll)

pathNestD-step : ∀ {n} {Γ : Ctx n} {s u t} (f : Frame Γ s u) (p : Path Γ u t) →
  pathNestD p ≤ pathNestD (f ↠ p)
pathNestD-step (map-f fn)         p = m≤n+m (pathNestD p) (nestDᵗ fn)
pathNestD-step (scan-f fn _)      p = m≤n+m (pathNestD p) (nestDᵗ fn)
pathNestD-step (take-f _)         p = ≤-refl
pathNestD-step (from-inner _ _ _) p = ≤-refl
pathNestD-step (thru-outer _ _)   p = n≤1+n (pathNestD p)

-- AND THE WALK'S DEPTH IS THE STORE'S PLUS ONE SQUARE, which is the
-- whole difference between the two ledgers: they step identically at
-- every frame and part company only at the leaf, where the walk's
-- prices the chain a hand-over passes its values to and the store's
-- prices nothing.  A path carries exactly one leaf, so the gap is a
-- constant and not a recursion.
pathΦD≤nestD : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  pathΦD B p ≤ pathNestD p + (B + B) * B
pathΦD≤nestD B root                   = z≤n
pathΦD≤nestD B (share-sink _)         = ≤-refl
pathΦD≤nestD B (map-f fn ↠ p)         =
  ≤-trans (+-monoʳ-≤ (nestDᵗ fn) (pathΦD≤nestD B p))
          (≤-reflexive (sym (+-assoc (nestDᵗ fn) (pathNestD p) ((B + B) * B))))
pathΦD≤nestD B (scan-f fn _ ↠ p)      =
  ≤-trans (+-monoʳ-≤ (nestDᵗ fn) (pathΦD≤nestD B p))
          (≤-reflexive (sym (+-assoc (nestDᵗ fn) (pathNestD p) ((B + B) * B))))
pathΦD≤nestD B (take-f _ ↠ p)         = pathΦD≤nestD B p
pathΦD≤nestD B (from-inner _ _ _ ↠ p) = pathΦD≤nestD B p
pathΦD≤nestD B (thru-outer _ _ ↠ p)   = s≤s (pathΦD≤nestD B p)

-- AND IT DOMINATES IT, from the same reading: the leaf is the only
-- clause where they differ and the walk's is the larger one there.
nestD≤pathΦD : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  pathNestD p ≤ pathΦD B p
nestD≤pathΦD B root                   = z≤n
nestD≤pathΦD B (share-sink _)         = z≤n
nestD≤pathΦD B (map-f fn ↠ p)         = +-monoʳ-≤ (nestDᵗ fn) (nestD≤pathΦD B p)
nestD≤pathΦD B (scan-f fn _ ↠ p)      = +-monoʳ-≤ (nestDᵗ fn) (nestD≤pathΦD B p)
nestD≤pathΦD B (take-f _ ↠ p)         = nestD≤pathΦD B p
nestD≤pathΦD B (from-inner _ _ _ ↠ p) = nestD≤pathΦD B p
nestD≤pathΦD B (thru-outer _ _ ↠ p)   = s≤s (nestD≤pathΦD B p)

-- THE PACKED READING SURVIVES A STEP, which is what lets it travel
-- down the walk beside the strict one rather than being re-derived at
-- every frame.  Both halves step for their own reason and neither
-- needs the cap to move: the frame half is a pairing, so the tail's is
-- one projection; and the length half is a BUDGET rather than a
-- per-frame ledger, so dropping a frame can only spend less of it.
-- That is the asymmetry the strict reading does not have -- it re-mints
-- its length conjunct at every frame against the cap itself, which is
-- why it is a descent invariant and this is not.
pathSzL?-tail : ∀ {n} {Γ : Ctx n} {s u t} (B : ℕ)
  (f : Frame Γ s u) (p : Path Γ u t) →
  pathSzL? B (f ↠ p) ≡ true → pathSzL? B p ≡ true
pathSzL?-tail B f p h =
  ∧-intro (∧-trueʳ {a = frameSz? B f} {b = pathFrameSz? B p}
             (∧-trueˡ {a = pathFrameSz? B (f ↠ p)}
                      {b = pathLen (f ↠ p) ≤ᵇ B + B} h))
          (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (n≤1+n (pathLen p))
            (≤ᵇ⇒≤ (suc (pathLen p)) (B + B)
              (T-to (∧-trueʳ {a = pathFrameSz? B (f ↠ p)} h))))))

-- THE GRANT AT ONE OUTER FRAME, which was the whole of what the walk
-- still owed: the four other frame kinds owe nothing, so a path with
-- no `thru-outer` in it needs none of this.  What is owed is a SIGHTED
-- grant covering the values that reach this frame -- a ceiling on each
-- one's depth plus the store's per-slot wrap, which the delivery
-- face's fit demands and the potential does not carry.
--
-- THE GRANT IS NAMED, NOT SEARCHED FOR: the path's remaining depth,
-- plus the maximum depth in flight, plus the wrap the whole context
-- can charge.  The first two come off the premises directly and the
-- input guard is free once the context is read whole, so the only
-- content is that the charge affords it -- and it does, in three
-- pieces that land on the potential's two halves.  The maximum in
-- flight is paid by the outer frame's OWN factor, which is two to the
-- cap and so at least two; the path's depth splits at the premise's
-- own denomination, the cap piece landing on the cap's charge and the
-- leaf's square beside the wrap on the walk's.  The doubling in the
-- charge is what lets the first piece sit beside the other two rather
-- than competing with them.

-- AND IT ASKS FOR THE PACKED SIZE READING, WHICH IS THE ONLY ONE THIS
-- ARM EVER SPENDS.  The grant is priced by `pathΦF-cap-atLen` at the
-- entry cap against a length budget of twice it, so a frame syntax and
-- a doubled length is the currency exactly -- the strict per-frame
-- ledger was being weakened to this on arrival.  Asking for what is
-- spent is what frees the walk to carry the strict reading at its OWN
-- level rather than at the entry, where minting it was refuted.

-- AND THE CAP IT SPENDS AT IS THE ONE THE CAPS RECURRENCE ISSUES NO
-- RECEIPT AT, WHICH IS THE FINDING ABOVE THE ROW.  That recurrence's
-- own contract is that the walk starts at level zero and climbs, and
-- that every registry length, chain cap and per-frame receipt is read
-- off the level it has reached -- nothing is charged at the entry
-- caps.  This arm charges there, and so does the terminal leaf's
-- re-pricing beside it; between them they are the whole of what
-- spends the entry-cap reading, and each names that cap only because
-- the potential handed to it is indexed by the INSTANT rather than by
-- the level.  So minting that reading was refuted rather than merely
-- hard: the face asks the registry for a receipt at the one cap no
-- receipt is issued at.  Moving the demand to the other endpoint does
-- not help either, since the next instant's caps are a blowup of THIS
-- instant's height, so a potential denominated there exceeds the
-- budget the descent is held under.  What is left is the climb
-- itself, and whether a potential exponential in the cap can be
-- indexed by it is a question about the caps mechanism rather than
-- about any statement underneath it.
-- AND THE ARM READS THE CAPS RECURRENCE IN EXACTLY THREE PLACES,
-- WHICH IS WHAT MAKES THE DENOMINATION QUESTION ANSWERABLE RATHER
-- THAN OPEN.  Everything else it applies is already stated over an
-- arbitrary cap and potential: both path re-pricings, the value
-- bound, and the fit of the values against the slots.  What it
-- genuinely takes from the instant is that the cap admits the
-- context, that the cap is at least two, and the grant itself.  So
-- the generic arm carries those three as hypotheses and the
-- specialisation supplies today's.  A re-denomination is then one
-- restated grant rather than a rebuilt arm -- and the grant is the
-- only thing left on this whole face that names the entry cap,
-- since the fan's root arm needs nothing but positivity.
walk-thru-fit-gen : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (S NC Φ : ℕ) (sf : Gas) (eid : Id) (now : Tick)
  (op : AllOp) (nid : NodeId)
  (p : Path Γ u t) (vals : List (Val Γ (obs u))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ S →
  n ≤ S →
  4 * (2 ^ ((S + S + (S + S)) * (suc S * S)) * (NC + (S + S) * S))
    + 2 * (2 ^ ((S + S + (S + S)) * (suc S * S)) * (S * slotWrapSum sl))
    ≤ Φ →
  Sched.slots sched ≡ sl →
  pathSzL? S (thru-outer op nid ↠ p) ≡ true →
  pathNestD (thru-outer op nid ↠ p) ≤ NC →
  valsΦ? S Φ (thru-outer op nid ↠ p) vals ≡ true →
  FrameΦHyp sf eid now S Φ (thru-outer op nid) p vals fin sched st
walk-thru-fit-gen {n = n} sl S NC Φ sf eid now op nid p vals fin sched st
                  2≤S n≤S hch hsl hpz hnd hΦ =
  n , G
  , subst (λ z → ValsFit n z G p vals) (sym hsl)
      (valsFit-of-max sl p vals M ≤-refl)
  , *-cancelˡ-≤ 2
      (≤-trans (*-monoʳ-≤ 2 (*-monoʳ-≤ (pathΦF S p)
                 (+-monoˡ-≤ (pathΦD S p)
                   (+-monoˡ-≤ (n * slotWrapSum sl)
                     (+-monoˡ-≤ (nestDᵛˢ vals) (nestD≤pathΦD S p))))))
      (≤-trans (≤-reflexive spread)
        (≤-trans (+-mono-≤ hA2 hBC2)
                 (≤-reflexive (sym (2X≡X+X Φ))))))
  where
  Q    = pathΦF S p
  Dn   = pathNestD p
  D    = pathΦD S p
  M    = nestDᵛˢ vals
  W    = slotWrapSum sl
  G    = Dn + M + n * W
  hpp  : pathSzL? S p ≡ true
  hpp  = pathSzL?-tail S (thru-outer op nid) p hpz
  1≤S  = ≤-trans (s≤s z≤n) 2≤S
  EXP  : ℕ
  EXP  = (S + S + (S + S)) * (suc S * S)
  Q≤   : Q ≤ 2 ^ EXP
  Q≤   = pathΦF-cap-atLen S (S + S) p (pathSzL?-frames S p hpp)
                          (pathSzL?-len S p hpp)
  D≤   : D ≤ NC + (S + S) * S
  D≤   = ≤-trans (pathΦD≤nestD S p)
                 (+-monoˡ-≤ ((S + S) * S)
                            (≤-trans (n≤1+n (pathNestD p)) hnd))
  2≤2^S : 2 ≤ 2 ^ S
  2≤2^S = ≤-trans (≤-reflexive (sym (*-identityʳ 2))) (^-monoʳ-≤ 2 1≤S)
  -- the values in flight, paid by the outer frame's own factor
  hA   : 2 ^ S * (Q * M) ≤ Φ
  hA   = ≤-trans (≤-reflexive (sym (*-assoc (2 ^ S) Q M)))
                 (Φ-to-bound S Φ (thru-outer op nid ↠ p) vals hΦ)
  hA2  : 2 * (Q * M) ≤ Φ
  hA2  = ≤-trans (*-monoˡ-≤ (Q * M) 2≤2^S) hA
  -- the path's own depth, and the wrap, against the charge a frame arm
  -- is granted: the depth's cap piece against the cap's half and its
  -- leaf square beside the wrap against the walk's
  reshape : ∀ q d w → 2 * (2 * (q * d) + q * w)
                        ≡ 4 * (q * d) + 2 * (q * w)
  reshape q d w = solve 3 (λ q′ d′ w′ →
                    con 2 :* (con 2 :* (q′ :* d′) :+ q′ :* w′)
                      := con 4 :* (q′ :* d′) :+ con 2 :* (q′ :* w′))
                  refl q d w
  hBC2 : 2 * (2 * (Q * D) + Q * (n * W)) ≤ Φ
  hBC2 =
    ≤-trans (≤-reflexive (reshape Q D (n * W)))
    (≤-trans (+-mono-≤ (*-monoʳ-≤ 4 (*-mono-≤ Q≤ D≤))
                       (*-monoʳ-≤ 2 (*-mono-≤ Q≤ (*-monoˡ-≤ W n≤S))))
             hch)
  spread : 2 * (Q * (D + M + n * W + D))
             ≡ 2 * (Q * M) + 2 * (2 * (Q * D) + Q * (n * W))
  spread =
    solve 4 (λ q d m w →
               con 2 :* (q :* (d :+ m :+ w :+ d))
                 := con 2 :* (q :* m)
                    :+ con 2 :* (con 2 :* (q :* d) :+ q :* w))
          refl Q D M (n * W)

walk-thru-fit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick)
  (op : AllOp) (nid : NodeId)
  (p : Path Γ u t) (vals : List (Val Γ (obs u))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  pathSzL? (Caps.cSize (capsAt e sl id)) (thru-outer op nid ↠ p) ≡ true →
  pathNestD (thru-outer op nid ↠ p) ≤ nestCapAt e sl id →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
         (thru-outer op nid ↠ p) vals ≡ true →
  FrameΦHyp sf eid now (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
            (thru-outer op nid) p vals fin sched st
walk-thru-fit {e = e} sl id sf eid now op nid p vals fin sched st
              hsl hpz hnd hΦ =
  walk-thru-fit-gen sl (Caps.cSize (capsAt e sl id)) (nestCapAt e sl id)
    (nestΦAt e sl id) sf eid now op nid p vals fin sched st
    (2≤capsAt-size e sl id) (n≤capsAt-size e sl id)
    (nestΦ-frame-charge e sl id) hsl hpz hnd hΦ

postulate
  -- THE FOLD'S GRANT HAS NOWHERE TO COME FROM ON THIS SIDE, and that
  -- is the finding rather than the size of the proof.  The consuming
  -- face now asks a scan frame for a ceiling on what its NODE holds --
  -- it has to, since the value a fold emits is its accumulator and no
  -- statement about the arriving values reaches it.  Every premise
  -- here is about the schedule, the path or the values; not one of
  -- them mentions `EvalSt.nodes`, so the store's depth is a free
  -- parameter of this statement and its conclusion is not derivable
  -- from its hypotheses.
  --
  -- SO WHAT IS OWED IS AN INVARIANT AND NOT A LEMMA -- AND NOT ONE IN
  -- THIS BUDGET'S CURRENCY EITHER.  A ceiling on the table is a fact
  -- every writer of a node must establish and every reader may spend,
  -- which is a field on the record the walk already carries; the
  -- ambient bundle this face runs under is about caps and slots
  -- alone, so there is no field to hang it on today, and the block
  -- below says why minting one would not help.  Threading it in here
  -- instead would launder the debt out of the
  -- ledger and into a signature that only today's one caller happens
  -- to satisfy, so the statement is left at full strength and the gap
  -- is left where a reader will meet it.  The width half is not part
  -- of the gap: `length vals` is a parameter, and the factors are the
  -- ones the iteration face is already proven at.

  -- AND THE FIELD IS NOT MERELY UN-THREADED -- THE CEILING THAT DOES
  -- EXIST IS AT THE WRONG DENOMINATION, which is worth knowing before
  -- a leg is spent relocating it.  The round above genuinely holds
  -- the node table under a ceiling: `chainStep-store≤` takes
  -- `storeNestMax sched st ≤ S` as a premise and `storeNest-nodes≤`
  -- reads the fold straight out of it, so the instinct that the fact
  -- is present and simply undelivered is half right.  But the ceiling
  -- is `S`, and that same caller carries `nestΦAt e sl id ≤ S`, so
  -- the two run the wrong way past each other.  This arm has to fit
  -- an EXPONENTIAL in `nodesMax st` under `nestΦAt` itself: the
  -- witness is pinned above the fold and then raised to the burst's
  -- length, so a bound sitting ABOVE `nestΦAt` is not a weak bound
  -- here, it is no bound at all.

  -- AND THE STORE SUMMAND IS THE WHOLE SEPARATION FROM A PROVEN ARM,
  -- which is what makes the residue small rather than structural.
  -- The fourth arm closes from these very four premises --
  -- `walk-thru-fit` builds its grant out of the path's depth, the
  -- depth in flight and the context's wrap, and reads the store
  -- nowhere at all -- so what stands between this arm and that one is
  -- one term and not a shape.  That term is read at the entry the
  -- step names: the scan clause does a single lookup and a single
  -- write at its own `nid` and never consults another, and
  -- `stepFrame-emit-scan` bounds what LEAVES the frame from that
  -- accumulator alone.  The table's own max is the honest reading for
  -- the table the step RETURNS and for nothing else.  So the ceiling
  -- owed here is one accumulator's depth, and it is the values folded
  -- into it that should pay for it.

  -- AND THE CEILING AT THE RIGHT DENOMINATION NOW FITS, WHICH TURNS
  -- THE RESIDUE FROM ARITHMETIC INTO ROUTING.  `nestOK?` is
  -- `storeNestMax` under `nestCapAt`, and `cascadeGo-nest-nodes` -- a
  -- sibling on this same face -- already takes it as a premise, so
  -- the routing half costs no producer anything it does not owe
  -- already.  What used to stop it was the arithmetic: the cap and
  -- the walk are separate recurrences in the instant index and the
  -- cap is the faster one AT THE SAME INDEX, so a `nestCapAt` ceiling
  -- sat above the walk's whole budget, and minting a fresh field in
  -- the walk's currency failed for the same reason at the writers'
  -- end.  The budget now CARRIES the cap rather than racing it:
  -- `nestΦAt`'s first summand is `nestCapAt` times two to the size
  -- cap cubed, which is above the path factor times the burst power
  -- this arm reads its `G` under.  So what is left here is that no
  -- premise names the table at all, and the fact that would is an
  -- ambient one this face does not carry.
  -- REFUTED: `Refuted.Cap-Walk-Cross`, at every floor this
  --   development proves at once -- the size cap at the REACHABLE one
  --   rather than the weakest one proven, the burst and the register
  --   width at one, the deletion size at the cap and the wrap sum at
  --   its bound -- and no axis moves the gap the other way.  It kills
  --   the walk-currency reading this statement used to be stated in,
  --   which is what the budget above it moved for.

  -- AND THE BURST'S COUNT IS A FREE PARAMETER WHILE THE CHARGE IS AN
  -- EXPONENTIAL IN IT, which is a second and independent defect: not
  -- about what this arm cannot see, but about what its own premises
  -- do not say.  Three of the four are about the PATH, and the
  -- fourth, `valsΦ?`, is an `all` -- it constrains each value and
  -- never how many there are -- while the conclusion charges
  -- `(2 ^ sizeᵗ fn) ^ length vals`.  A budget affording one value is
  -- beaten by the same value repeated.
  --
  -- AND THE LEDGER LOOKS LIKE THE REPAIR AND IS NOT, WHICH IS THE
  -- FINDING.  The caps face's own value ledger `valsCaps?` is a
  -- CONJUNCTION -- the per-value predicate together with a bound on
  -- `length vs` -- and `stepFrame-scan-caps`, proven about this very
  -- frame, takes that second conjunct as a premise.  `valsΦ?` carries
  -- only the first, so the obvious move is to put the width back.  A
  -- width the ledger is free to choose closes nothing: the number that
  -- has to bound the count is the instant's SIZE CAP, and a conjunct on
  -- the values names no instant.
  --
  -- WHAT SEPARATES THE TWO FACES IS THAT ONE CURRENCY STEPS.  The
  -- mirror's conclusion is a receipt at a cap the fold has already
  -- advanced, and the width axis EXPONENTIATES per step, so the caps
  -- face never fits a burst's charge under a quantity fixed before
  -- the walk began.  The potential does: `nestΦAt` is indexed by the
  -- INSTANT and reads nothing of how far into a chain the frame sits.
  -- So what has to move is where this arm's charge is denominated,
  -- and no conjunct on the values reaches that.
  -- REFUTED: `Refuted.Scan-Phi-Width`, twice.  Once as written, at the
  --   reachable size floor with the frame at the ROOT -- so the path
  --   contributes neither factor nor depth and the crossing is the
  --   fold's alone -- and at a budget taken at exactly what one value
  --   costs, the burst being the least count that crosses there.  Once
  --   again with the width premise added and the width left under its
  --   binder, which is what says the ledger is not the repair rather
  --   than that some width is too small.

  -- AND NEITHER THE COUNT NOR ITS FACTOR IS MISSING FROM THE
  -- DEVELOPMENT, which is what narrows this to one question.  The
  -- factor is the store face's `nestFac S W`, `((2 ^ S) ^ suc W) ^ S`
  -- -- the burst power written INTO the factor instead of fitted under
  -- it -- and `nestFac≤exp` with `nestFacLog≤pow` take the whole power
  -- down to a polynomial in a size cap.  The fold is proven in that
  -- currency: `scanVals-nest` and `stepFrame-emit-scan` state this very
  -- step under `length vals ≤ W` and conclude at `(2 ^ sizeᵗ fn) ^ W`.
  -- The count hypothesis is proven too, and walk-shaped: `burstsOK`
  -- carries a bound along a path exactly as this walk carries its size
  -- receipt, `burstsHead` projects the head, `burstsDrain` the frame's
  -- own obligation, and `chainBurstOK` packages one chain's worth.  So
  -- the residue is not a fact to prove but a place to read: WHERE this
  -- arm's factor is denominated.

  -- AND IT CANNOT BE READ AT THIS INSTANT'S SIZE CAP, WHICH IS WHAT
  -- THIS ARM'S FACTOR IS PRICED AT.  The quantity bounding a burst is
  -- the WIDTH -- `nestBurstAt` is `suc` of it -- and the width and the
  -- size of one caps triple are ordered the wrong way from the first
  -- fold on, a fold taking the width through `S ^ suc w` and the size
  -- through `S * suc (2 * s)`.  `burst≤size′` does put the burst under
  -- a size cap, and the cap it names is the NEXT instant's.  So a count
  -- premise at this instant's cap is not one the development can
  -- supply, however the ledger is shaped, and no conjunct on the values
  -- reaches the difference.
  -- REFUTED: `Refuted.Caps-Face`, whose `wid≤size-absurd` orders the two
  --   axes at one triple and whose `scan-count-under-ceiling-absurd`
  --   kills the squared form beside it.
  -- DEAD ROUTE: denominating this arm at `frameStep j` of the instant's
  --   caps instead, so the receipt is read at a cap the fold has
  --   already advanced.  The width axis exponentiates per fold, so j
  --   folds put it above `towerℕ j`, and a count that reads it gives up
  --   the linear height `capsAt-tower` proves.

  -- AND THE COUNT CANNOT BE CARRIED AS ITS OWN PARAMETER EITHER, WHICH
  -- CLOSES THE LAST DENOMINATION ON OFFER.  Taking the burst's count as
  -- a second parameter is what the store face does -- `nestFac S W`
  -- takes both -- and it reads as what the two findings above point at,
  -- since premise and conclusion would then move together and a free
  -- count would finance itself.  What decides it is AFFORDABILITY, and
  -- the ceiling is proven rather than open: `nestΦ-sight≤capsH` routes
  -- through `capsAt-exp≤capsH`, so a budget denominated at an instant
  -- may carry an exponent as large as two to that instant's size cap
  -- and no larger.  A factor read at a count W costs the path's length
  -- times `suc S * W`, so the exponent is quadratic in the cap and
  -- LINEAR in the count, and affording it asks the count under `2 ^ S`.
  -- The caps face's width is not under it: the width folds through
  -- `S ^ suc w` against the size's `S * suc (2 * s)`, so it is a tower
  -- in the fold count where the size is geometric.
  -- REFUTED: `Refuted.Caps-Face.wid≤exp-size-absurd`, whose base triple
  --   starts with its width EQUAL to its size -- so nothing is smuggled
  --   in by starting wide -- and crosses at three folds, `wid₃≡` and
  --   `size₃≡` pinning five hundred and thirteen doublings of width
  --   against a ceiling of one hundred and seventy.

  -- AND THE STORE FACE'S RECURRENCE DOES NOT TRANSFER, WHICH IS THE
  -- FOURTH DENOMINATION AND THE ONE THAT SAYS WHERE TO LOOK NEXT.  It
  -- is the obvious reading of the three findings above: `nestCapAt` is
  -- a recurrence rather than a formula, each instant multiplying the
  -- previous cap by `nestFacAt`, so a burst power rides as a factor
  -- and never has to fit inside an exponent -- and that budget is
  -- affordable, proven, and already a summand of this one through
  -- `capΦAt`.  What the two faces do not share is WHICH instant's
  -- burst each has to price.  `nestCapAt` at an instant charges the
  -- PREVIOUS instant's folds, whose width sits under THIS instant's
  -- size, so the charge is polynomial against a
  -- ceiling that is two to the size.  This ledger is spent DURING its
  -- own instant -- `cascade-depth-capsH` is what spends it, against
  -- the fuel that instant runs at -- so its folds' width is only under
  -- the NEXT instant's size.  One index, and it is the whole
  -- difference: the width folds through a power tower where the size
  -- steps geometrically, so a width read one instant late is above
  -- every exponential this instant's fuel affords.

  -- AND THE BURST IS DECIDED AFTER ALL -- BY THE PROVEN CAPS FACE, AND
  -- AGAINST THIS ARM.  `burstsOK` carries its bound as a free parameter
  -- and no consumer instantiates it, which reads as an open choice; the
  -- mirror has already made it.  `valsCaps?` is the per-value predicate
  -- CONJOINED with `length vs` under `suc` of the width, and the walk
  -- reads it at the cap the walk has advanced to, so a mid-walk count is
  -- bounded by the width there and by nothing smaller.  The uniform
  -- reading `burstsOK` needs is the walk's endpoint, which is this
  -- instant's exit cap by monotonicity in the hop count -- one number
  -- covering every hop, and NOT the one `nestBurstAt` takes, which is
  -- the entry width: the count between two `thru` frames is already
  -- over it.

  -- AND NO STORY BUYS THE ROOM, WHICH IS WHAT MAKES THIS A MECHANISM
  -- FINDING RATHER THAN AN INDEX ONE.  The instinct once the numbers are
  -- side by side is that the charge is spent one story too low -- the gas
  -- an instant runs under is denominated a `blowH` story above the index
  -- the depth ledger reads, and the shortfall looks like exactly that
  -- gap.  It is not.  Within an instant the size cap steps geometrically
  -- per fold and the width cap steps through a power tower, so the width
  -- at ANY instant is above two-to-two-to the size at that SAME instant,
  -- and the ceiling a story supplies is that double exponential whichever
  -- story is chosen.  Moving up one moves both sides.
  --
  -- WHAT DOMINATES A WIDTH IS THE NEXT INSTANT'S SIZE AND NOTHING
  -- EARLIER, and the store face affords its own burst charge by being
  -- checked exactly there: its factor is two to a square of the burst,
  -- read against the ceiling at the instant AFTER the one that produced
  -- it. The depth ledger is spent DURING its own instant, so the same
  -- charge has no such ceiling to reach for.  That is the whole
  -- asymmetry, and it is a property of where the two faces are checked
  -- rather than of what either one charges -- so the repair is not a
  -- restatement of this arm but a decision about whether the depth face
  -- prices a threading frame at all.

  -- AND THE REASON NO STORY BUYS IT IS A CIRCLE, NOT A SHORTFALL.  The
  -- depth an instant's arcs may spend is ONE NUMBER fixed before the
  -- instant runs, and the delivery count the caps face affords is
  -- computed FROM that number, towering in it.  A fold's width is under
  -- that count; a fold with a step function of positive nesting builds
  -- nesting that is at least linear in its width; and a nested value
  -- subscribed at a hand-over spends depth per layer.  So the depth the
  -- instant needs is at least the count taken at the depth it was given,
  -- and a number that dominates a tower in itself does not exist.  That
  -- is the same region producing the same refutation at every
  -- denomination tried -- size, level, count as parameter, the story
  -- above -- which is the convergence test's own stop condition, and it
  -- names the mechanism: a depth parameter chosen BEFORE the count it
  -- must dominate.  Two repairs suggest themselves and neither is one.
  -- Counting STORIES instead of depth -- one per scan hop, since the
  -- fuel is a tower whose height `blowH` keeps -- is the caps face's
  -- own currency already, affordable there because it is read at the
  -- EXIT index; what this face owes is the story-index NUMBER at the
  -- ENTRY index, since the count axis instantiates its level function
  -- at that nesting depth and every frame of the instant must nest
  -- under it.  And a join rather than a sum in the `caseᵗ` clause of
  -- `nestDᵗ` is what that clause already takes.

  -- AND THE RESIDUE CANNOT BE SETTLED BY INSTANTIATION, WHICH IS A
  -- FACT ABOUT THE OBLIGATION AND NOT ABOUT ANY HARNESS.  What is left
  -- here is that no premise names the node table, so the natural next
  -- move is to read the two sides at a state a run reached and see
  -- which one has room.  Only one of them can be read.  The store side
  -- computes: driven through later frames off its own subscribe, the
  -- table reads one less than two to the burst length and DOUBLES on
  -- the first later value, so the side that CAN be measured grows
  -- exponentially in a count these premises never bound -- the
  -- `valsΦ?` defect above, arriving from the store rather than from
  -- the charge.  The charge side computes nowhere: `nestΦAt` and both
  -- its summands are sealed, the `-def` equations hand the body back
  -- in terms of `capsAt`, and `capsAt` is stuck at its own ENTRY,
  -- since even there it is `frameBlowup` of the sealed `sizeCount`.
  -- Compiled, which ignores every seal, the entry size cap and both
  -- Φ summands were each killed at 180 s with no value at the smallest
  -- program reaching this arm, while `nestCapAt` at the entry returns
  -- at once because it IS `nestUnit`.  The rows are `Harness.Main`'s,
  -- and are measured-not-rechecked by construction.

  -- SO THE ARM IS NOT MIS-SHAPED, IT IS UNAFFORDABLE, and that is a
  -- class and not a repair.  The count is under the exit cap's width and
  -- under nothing smaller, the fold charges a power in the count, and
  -- the fuel this instant runs at affords an exponent of two to its own
  -- size.  A count at least the size is all that is known, and that
  -- already leaves the room.  No ledger, no field and no recurrence
  -- changes the two numbers being compared.

  -- AND THE BINARY IS ANSWERED, IN NEITHER OF THE TWO WAYS IT WAS PUT.
  -- What was asked is whether the count the recurrence ADMITS at a
  -- level is reachable by a run at all, since a count no run reaches is
  -- a premise this arm may simply carry.  It is not that count: driven
  -- at one layer, the widest instant a run reaches is a CUBE of the
  -- synchronous burst its slot script delivers, and at the smallest
  -- dials the layer axis is flat where the recurrence towers.  But the
  -- premise unreachability was to license cannot be carried either, and
  -- the same rows say why: the burst length takes the widest instant
  -- from one to three hundred and forty-three while every
  -- program-denominated quantity beside it -- the size, the level, and
  -- the proven entry ceiling -- stands still, and a slot script is
  -- carried by no part of the program.  So the two numbers are not
  -- merely far apart, they are in different CURRENCIES, and this arm
  -- waits on a ceiling that does not exist rather than on a number that
  -- is too big.  The rows are `Harness.Main`'s and are
  -- measured-not-rechecked by construction.
  -- REFUTED: `Refuted.Walk-Phi-Room`, whose `walk-fold-room-absurd`
  --   states the affordability as the product it is and kills it at the
  --   floor of twenty-one, with `size₄` pinning that four folds already
  --   carry the next cap past two to that floor -- so the count it
  --   spends is one the recurrence admits rather than one invented.
  -- DEAD ROUTE: re-reading the ceiling with the ENTRY width in the
  --   exponent -- two to two to the entry size times the entry width is
  --   under the story index at the same instant, by the pooled walk's
  --   last-position slack -- affords only the levels whose width is
  --   under that ceiling, about two to the previous instant's size
  --   count of them, while the instant runs a level count that towers
  --   in the story index.  Provable, and it buys a prefix.
  -- DEAD ROUTE: the WIDTH-FIELD half of the binary above -- carrying a
  --   tighter width as a field of the invariant record on the reading
  --   that a program fans out per hop by at most its size.  The field
  --   would have to be denominated in the measure the frame face
  --   already uses, and that measure carries the source's payload count
  --   into an EXPONENT -- on its INNER reading, which the outer one
  --   multiplies by exactly when a FLATTEN consumes it, so a bare fold
  --   is flat there and one refold is not.  It therefore towers in the
  --   layer count with no cap anywhere in its definition: a three-layer
  --   refold crosses the linear ceiling at the linear reading's own
  --   most generous setting, its own size at each level.  So there is
  --   no field to thread, and the arm sits on the other branch.  The
  --   separation is proven in `Probed.Fold-Width-Reach`, where a RUN
  --   of the same family -- driven through later frames off the state
  --   its own subscribe produced -- crosses the linear reading at the
  --   FIRST hop, so the field is refuted by a measurement and not only
  --   by a measure.  What the run does NOT reach is the count the
  --   recurrence ADMITS, which is the binary above and stands where it
  --   stood: two layers outran the evidence loop outright.  And the
  --   field is named HERE and nowhere else in the development, so
  --   killing it moved this arm alone -- no sibling was parked on it,
  --   and none of them can be reclassified off this route.
  -- DEAD ROUTE: asking for the same field as a burst LENGTH rather
  --   than as a width, on the reading that a COUNT and a MEASURE are
  --   different currencies and only the second was killed above.  They
  --   are not different, and the descent ceiling is what says so: the
  --   only proven ceiling on the values a frame is handed is
  --   `burst-out`, which puts that length under `outWⱽ` -- the frame
  --   face's own measure, read at the entry form -- and nothing here
  --   bounds it by anything smaller.  So a length field is the width
  --   field wearing a count's name, and the separation above kills it
  --   unchanged, since `outWⱽ` takes a source's payload count into an
  --   exponent exactly when a flatten consumes it and so towers in the
  --   layer count.  What that closes is the RETRY: both halves of the
  --   binary stand where they stood, and this route reaches neither.
  -- DEAD ROUTE: carrying the delivery count as a PREMISE of this arm,
  --   on the reading that a count no run reaches may be assumed away.
  --   The count is reachable in the only sense a premise cares about --
  --   it moves with the slot script and with nothing the program names
  --   -- so the premise would have to be discharged at the call site
  --   out of a ceiling on a LATER frame's values, and the development
  --   has none.  `burst-out` is its only syntax-to-values tie and it
  --   prices the SUBSCRIBE frame, which for the one family that can
  --   tower a width emits nothing at all at every burst length
  --   measured, so it constrains none of the instants that carry the
  --   width.  The premise is undischargeable for the same reason the
  --   field was unthreadable, one frame further on.
  -- DEAD ROUTE: taking the tie off the REGISTRY face instead, on the
  --   reading that a fanned chain's price and this arm's are one
  --   missing relation owed at two sites.  That face turned out to
  --   need no new relation at all -- a chain legal at the cap climbs
  --   at most a cap's worth of levels, and that is proven -- so what
  --   closed there was a LEVEL ledger, a quantity that COMPOUNDS
  --   along a walk and is paid for by a term per hop.  The potential
  --   does not compound: a fanned chain owes what the sink was handed
  --   and nothing accumulated on the way in.  There is no shared
  --   statement to state once, so this arm is not waiting on that
  --   face.

  -- AND THE MECHANISM UNDER ALL FIVE IS WHAT IS DEAD, NOT A SIXTH
  -- DENOMINATION.  The routes above share one shape: a potential fixed
  -- per instant and read at the entry cap is asked to dominate a term
  -- carrying the burst count in an EXPONENT.  That count is not
  -- independent of the potential -- a scan's burst is at most the
  -- flattened width of what reaches it, which is exponential in the
  -- nesting the potential bounds, and the fold's output nesting is
  -- again exponential in the count -- so a flat potential is asked to
  -- be a fixed point of a loop that has none.  The one ceiling in the
  -- development that DOES afford this fold is the store face's, and it
  -- is read at the EXIT index: the nesting cap at the next instant is
  -- this instant's cap times a factor towering in the burst
  -- (`nestFacAt`), discharged by no premise of any frame but by the
  -- walk's own count ledger -- `burstsOK` at every hop, closed at the
  -- top by `arr-chains-bursts` -- and that closure is FLAT, which
  -- `Refuted.Chains-Burst-Flat` kills: two `thru` frames square a
  -- burst, so the factor is itself priced in a refuted width and the
  -- re-denomination it once promised is not available as it stands.
  -- This arm cannot read that ceiling,
  -- because the depth door `cascade-depth-capsH` is sighted at THIS
  -- instant's fuel: it lands the potential under `capsH` at the entry
  -- index, and the caps recurrence puts the next instant's factor two
  -- exponentials above what that fuel can see.  So the repair is not
  -- inside this statement, and the row is SHAPE rather than FALSITY:
  -- either the depth face is re-denominated to carry the walk's count
  -- ledger and be sighted one instant later -- which moves what the
  -- evaluator's budget must afford, a question and not an edit -- or a
  -- dynamics argument puts the same-instant burst under this instant's
  -- fuel, and `Harness.Main`'s rows (measured-not-rechecked) say a
  -- run's count is script-denominated, so no premise here carries it.
  -- DEAD ROUTE: a sixth local denomination of the scan arm -- an
  --   existential width in place of the burst count, threaded from
  --   `burstsOK` the way the store face threads it.  The threading is
  --   available, and the fit it lands is exactly the product
  --   `Refuted.Walk-Phi-Room` kills: the width so threaded is the
  --   walk's, which the store affords only through its exit-index
  --   factor, and no potential sighted at `capsH` at this instant
  --   carries that factor.  The three subdivisions that reached the
  --   spiral stop were all inside this potential, so a fourth is the
  --   same route under a new name.
  scanΦ-fit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick) (Lv : ℕ)
    (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId)
    (p : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ)
    (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id)))
            (scan-f fn nid ↠ p) ≡ true →
    pathSzL? (Caps.cSize (capsAt e sl id)) (scan-f fn nid ↠ p) ≡ true →
    pathNestD (scan-f fn nid ↠ p) ≤ nestCapAt e sl id →
    valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
           (scan-f fn nid ↠ p) vals ≡ true →
    FrameΦHyp sf eid now (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
              (scan-f fn nid) p vals fin sched st

-- AND THE DRAIN'S GRANT IS OWED THREE THINGS, AND THE STORE HALF OF
-- IT IS THE FOLD'S.  A `from-inner` hands on what the inner run
-- produced, so like the fold it reaches past its own values -- but
-- the payload it reaches is the merge node's QUEUE, and what a
-- subscription does to a queued term is substitute into it.  So the
-- grant carries the iteration face's factors rather than a summand.
-- Its store ceiling is read at the ONE entry `innerFinish` looks up:
-- the drain consumes that node's queue and reaches no other cell, so
-- a ⊔ over the table is a widening of this reading rather than a
-- second source, and the residue is the queued terms' own depth.

-- AND THE STRICT LENGTH CONJUNCT IS A DESCENT INVARIANT, WHICH IS WHY
-- NO WEAKENING OF IT IS LOCAL.  It is not carried to the bottom and
-- spent there: `path-step` consumes it at EVERY frame and re-mints it
-- one level up, off the chain device that grows the size cap by
-- exactly one per level -- so this conjunct is what CARRIES the
-- descent, and a length known only at twice the cap cannot enter it
-- at level zero, where the caps step is the identity.  Nor may the
-- size predicate's two halves travel as separate premises: the length
-- half is the inductively load-bearing one and the frame half rides
-- on it.  The pair runs from `stepFrame-nodes-inner` through
-- `innerFinish-nest` and `mergeAllDrain-nest` to `subscribeInner-nest`,
-- and a census finds it in ninety-odd signatures across a dozen
-- modules, `Nest-Walk` and `Walk-Level` among them -- the two the dev
-- loop can no longer hold.  What the walk DOES follow is a WIDENING to
-- the level it is standing at, which is the surviving route and the
-- one `fan-regsSz`'s own header names.
InnerΦCore : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sf : Gas) (eid : Id) (now : Tick) (B U W : ℕ)
  (op : AllOp) (allNid inst : NodeId) (p : Path Γ s t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
  (c : Caps) (d Lv G : ℕ) → Set
InnerΦCore {e = e} sf eid now B U W op allNid inst p vals fin sched st c d Lv G =
    FaceOK c (Sched.slots sched)
  × (depthReact sf op allNid inst p eid now vals sched st fin ≤ d)
  × (pathSz? (Caps.cSize (frameStep Lv c)) p ≡ true)
  × (suc (pathLen p) ≤ Caps.cSize (frameStep Lv c))
  × (nodeNestAt allNid st ⊔ nestDᵛˢ vals ≤ G)
  × (∀ (j : ℕ) → j ≤ sizeCount c d ⊔ Caps.cSize c →
       pathΦF B p
         * (nestFac (Caps.cSize (frameStep j c)) W
              * (G + nestU (Caps.cSize (frameStep j c))
                       (nestUnit e (Sched.slots sched)))
            + pathΦD B p) ≤ U)

-- AND THE TABLE IS NOT A FREE PARAMETER, which is what dissolves the
-- routing the two drain ledgers used to pose.  Both are quantified
-- over whatever queue the lookup returns, and that reads as a fact
-- some other statement has to hand over -- but `lookupNode allNid` is
-- a determinate value of the state this statement is ALREADY given, so
-- the two conjuncts are about ONE queue rather than about every queue
-- a table might hold.  Reading it costs no hypothesis, and it is what
-- the two arms below do.
NotMergeAt : ∀ {n} {Γ : Ctx n} {s} → Maybe (NodeState Γ) → Set
NotMergeAt {Γ = Γ} {s = s} ns =
  ∀ (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
    ns ≢ just (mergeAll-st lim act q od)

notMerge-none : ∀ {n} {Γ : Ctx n} {s} {ns : Maybe (NodeState Γ)} →
  ns ≡ nothing → NotMergeAt {Γ = Γ} {s = s} ns
notMerge-none refl _ _ _ _ ()

notMerge-scan : ∀ {n} {Γ : Ctx n} {s u} {ns : Maybe (NodeState Γ)} (v : Val Γ u) →
  ns ≡ just (scan-st v) → NotMergeAt {Γ = Γ} {s = s} ns
notMerge-scan _ refl _ _ _ _ ()

notMerge-take : ∀ {n} {Γ : Ctx n} {s} {ns : Maybe (NodeState Γ)} (k : ℕ) →
  ns ≡ just (take-st k) → NotMergeAt {Γ = Γ} {s = s} ns
notMerge-take _ refl _ _ _ _ ()

notMerge-switch : ∀ {n} {Γ : Ctx n} {s} {ns : Maybe (NodeState Γ)}
  (cur : Maybe NodeId) (od : Bool) →
  ns ≡ just (switch-st cur od) → NotMergeAt {Γ = Γ} {s = s} ns
notMerge-switch _ _ refl _ _ _ _ ()

notMerge-exhaust : ∀ {n} {Γ : Ctx n} {s} {ns : Maybe (NodeState Γ)} (ia od : Bool) →
  ns ≡ just (exhaust-st ia od) → NotMergeAt {Γ = Γ} {s = s} ns
notMerge-exhaust _ _ refl _ _ _ _ ()

-- AND A MERGE AT ANOTHER TYPE IS NOT ONE EITHER, which is the arm the
-- constructor alone cannot refute: the queue carries its element type
-- existentially, so a stored merge is a merge at SOME type and this
-- frame reads one at its own.  The evaluator's every read of the cell
-- pays the same decision, and this is that decision on the proof side.
notMerge-other : ∀ {n} {Γ : Ctx n} {s w} {ns : Maybe (NodeState Γ)}
  (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ w)) (od : Bool) →
  ns ≡ just (mergeAll-st lim act q od) → w ≢ s → NotMergeAt {Γ = Γ} {s = s} ns
notMerge-other lim act q od refl ne _ _ _ _ refl = ne refl

-- THE FACE AT THE PROGRAM'S OWN CAP, and none of its four fields is
-- something a walk has to carry: the size floor, the register floor,
-- the slot legality and the slot budget are each already proven of
-- `capsAt` itself.  So the arms below can REPORT this cap instead of
-- choosing one, and that is what takes the upward-closure question off
-- their existential -- a witness read off the program cannot be
-- enlarged to make a conjunct true.
faceOK-capsAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  FaceOK (capsAt e sl id) sl
faceOK-capsAt {n = n} e sl id =
  faceOK (2≤capsAt-size e sl id) (1≤capsAt-reg e sl id) (slotsCaps?-capsAt e sl id)
    (≤-trans (m≤n+m (slotsSize sl) (sizeᵉ e))
      (≤-trans (m≤n+m (sizeᵉ e + slotsSize sl) 4)
        (≤-trans (m≤m+n (4 + (sizeᵉ e + slotsSize sl)) n)
          (≤-trans (m≤m+n (4 + (sizeᵉ e + slotsSize sl) + n) n)
                   (capsAt-round-size e sl id)))))

-- AND THREE OF THE ARM'S FOUR EXISTENTIALS WERE NEVER CHOICES, which
-- is what writing the body settled.  The face is the program's own
-- cap, the descent count is the reaction's own depth, and the store
-- residue is the node's nesting joined with the values' -- each is
-- named by a premise the arm already takes, so each is supplied here
-- and its conjunct closes on reflexivity.  The path's two receipts
-- follow by widening the entry's, since a level only inflates the
-- size it is read at.  What is left is two quantities nothing in the
-- premises names, and they are the two leaves below.
postulate
  -- THE CHARGE, WITH NO QUEUE TO DRAIN, and the width is zero there
  -- because a drain that finds no cell subscribes nothing.  This is
  -- the whole of the quiet arm once the reported quantities are taken
  -- out of it: one inequality, at every level within the descent's own
  -- count.
  --
  -- AND IT CHARGES THE NODE TABLE WHILE NO PREMISE OF IT BOUNDS THE
  -- TABLE, which is the first of the two shapes that are almost always
  -- wrong: `nodeNestAt` reads one accumulator out of a state this
  -- quantifies over, and the four premises speak about the schedule,
  -- the path and the values in flight.  At an empty burst the potential
  -- premise is an `all` over nothing, the depth premise is met because a
  -- `from-inner` is charged no depth, and the level is met at zero -- so
  -- a fixed number is asked to dominate the depth of whatever cell the
  -- frame happens to name.  The gap is a MISSING INVARIANT and not a
  -- missing lemma: what is owed is the ambient store predicate every
  -- cascade door already takes, carried down the walk, which is
  -- `walk-share-nestOK`'s gap read at this arm.  Whether the grant is
  -- AFFORDABLE once it has that is a separate question, and the factor
  -- being read at the walk's level is why it stays open.
  -- REFUTED: `Refuted.Inner-Phi-Store`, at one installed scan cell whose
  --   accumulator is deeper than the instant's potential.
  -- REFUTED: `Refuted.Cap-Walk-Cross`, which settles the ordering the
  --   charge is read under -- the store ceiling sits under the budget,
  --   so the fold arm's settlement binds this one too.
  innerΦ-quiet-fit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick) (Lv : ℕ)
    (op : AllOp) (allNid inst : NodeId)
    (p : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ)
    (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id)))
            (from-inner op allNid inst ↠ p) ≡ true →
    pathSzL? (Caps.cSize (capsAt e sl id)) (from-inner op allNid inst ↠ p) ≡ true →
    pathNestD (from-inner op allNid inst ↠ p) ≤ nestCapAt e sl id →
    valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
           (from-inner op allNid inst ↠ p) vals ≡ true →
    ∀ (j : ℕ) →
      j ≤ sizeCount (capsAt e sl id)
                    (depthReact sf op allNid inst p eid now vals sched st fin)
          ⊔ Caps.cSize (capsAt e sl id) →
      pathΦF (Caps.cSize (capsAt e sl id)) p
        * (nestFac (Caps.cSize (frameStep j (capsAt e sl id))) 0
             * ((nodeNestAt allNid st ⊔ nestDᵛˢ vals)
                + nestU (Caps.cSize (frameStep j (capsAt e sl id)))
                        (nestUnit e (Sched.slots sched)))
           + pathΦD (Caps.cSize (capsAt e sl id)) p)
      ≤ nestΦAt e sl id

  -- AND THE SAME CHARGE WITH ONE, at the queue the state names rather
  -- than at any the table might hold.  The width is no longer chosen:
  -- it is that queue's own `drainW`, so the charge is read against the
  -- number the drain actually spends.
  --
  -- AND ITS LEVEL RANGE IS THE ROUND'S COUNT AND NOT THE REACTION'S,
  -- WHICH IS WHAT SHARING A LEDGER WITH THE CAPS FACE COSTS.  The
  -- drain ledger this arm now takes rather than mints is denominated
  -- at the walk's own descent count, so the record's count has to be
  -- that one -- and the range every level is read over is the count's,
  -- which widens here from the reaction's depth to the round's.  The
  -- statement is strictly stronger for it, and it is the honest one:
  -- the levels a drain can reach are the levels the ROUND affords, not
  -- the ones this one reaction descends through.
  --
  -- AND ITS ONE EXTRA PREMISE PINS THE CELL'S CONSTRUCTOR AND NOT ITS
  -- DEPTH, so the store term runs away here exactly as it does in the
  -- quiet arm beside it.  The lookup says the cell IS a merge at this
  -- frame's type; what that cell has PARKED is then read by the same
  -- `nodeNestAt`, and a queue holding one deep program sends its depth
  -- through a conclusion whose right side is fixed by the program, the
  -- slots and the instant.  So the arm owes the ambient store predicate
  -- carried down the walk before the width question is even reached,
  -- and the two inner arms owe it as one thing.
  -- REFUTED: `Refuted.Inner-Phi-Store`, at one parked program deeper
  --   than the instant's potential.
  -- REFUTED: `Refuted.Cap-Walk-Cross`.

  -- AND ITS OBSTACLE IS THE SCAN ARM'S, ONE ARM OVER.  The charge here
  -- multiplies a flat potential by a factor carrying the drain width in
  -- an exponent, and that width is the same walk count the scan arm's
  -- burst is: bounded by nothing at this instant's fuel and afforded
  -- only by the store's exit-index factor.  The finding is one and its
  -- argument sits in `scanΦ-fit`'s header; what it means for this
  -- statement is that no repair inside the arm exists, so the row is
  -- SHAPE and the restatement comes with the face's, not alone.
  -- DEAD ROUTE: repairing the drain arm by itself, by reading its width
  --   off the queue the state names rather than off the table.  That
  --   is what the statement already does, and it moves the width from
  --   chosen to actual without moving its CURRENCY: the actual drain
  --   width is walk-denominated, so a potential sighted at this
  --   instant's fuel cannot dominate the factor, for the reason the
  --   scan arm's mechanism route records.
  innerΦ-drain-fit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick) (Lv : ℕ)
    (op : AllOp) (allNid inst : NodeId)
    (p : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ)
    (st : EvalSt e) (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
    lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
    Sched.slots sched ≡ sl →
    pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id)))
            (from-inner op allNid inst ↠ p) ≡ true →
    pathSzL? (Caps.cSize (capsAt e sl id)) (from-inner op allNid inst ↠ p) ≡ true →
    pathNestD (from-inner op allNid inst ↠ p) ≤ nestCapAt e sl id →
    valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
           (from-inner op allNid inst ↠ p) vals ≡ true →
    ∀ (j : ℕ) →
      j ≤ sizeCount (capsAt e sl id) (capsH e sl id)
          ⊔ Caps.cSize (capsAt e sl id) →
      pathΦF (Caps.cSize (capsAt e sl id)) p
        * (nestFac (Caps.cSize (frameStep j (capsAt e sl id)))
                   (drainW sf allNid p eid now q sched st)
             * ((nodeNestAt allNid st ⊔ nestDᵛˢ vals)
                + nestU (Caps.cSize (frameStep j (capsAt e sl id)))
                        (nestUnit e (Sched.slots sched)))
           + pathΦD (Caps.cSize (capsAt e sl id)) p)
      ≤ nestΦAt e sl id

-- THE QUIET ARM, ASSEMBLED, and the level it reports is the WALK'S
-- because that is the level its size receipt is read at.  Nothing here
-- descends, so the arm is free to report any level the receipt covers;
-- reporting the walk's is what lets the receipt arrive un-widened, and
-- the two path conjuncts are then projections.
innerΦ-fit-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick) (Lv : ℕ)
  (op : AllOp) (allNid inst : NodeId)
  (p : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ)
  (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id)))
          (from-inner op allNid inst ↠ p) ≡ true →
  pathSzL? (Caps.cSize (capsAt e sl id)) (from-inner op allNid inst ↠ p) ≡ true →
  pathNestD (from-inner op allNid inst ↠ p) ≤ nestCapAt e sl id →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
         (from-inner op allNid inst ↠ p) vals ≡ true →
  Σ Caps λ c → Σ ℕ λ d → Σ ℕ λ Lv′ → Σ ℕ λ G →
    InnerΦCore sf eid now (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id) 0
      op allNid inst p vals fin sched st c d Lv′ G
innerΦ-fit-quiet {e = e} sl id sf eid now Lv op allNid inst p vals fin sched st
                 hsl hpz hpl hnd hΦ =
  capsAt e sl id
  , depthReact sf op allNid inst p eid now vals sched st fin
  , Lv
  , (nodeNestAt allNid st ⊔ nestDᵛˢ vals)
  , subst (λ z → FaceOK (capsAt e sl id) z) (sym hsl) (faceOK-capsAt e sl id)
  , ≤-refl
  , ∧-trueʳ hpz
  , ≤ᵇ⇒≤ _ _ (T-to (∧-trueˡ hpz))
  , ≤-refl
  , innerΦ-quiet-fit sl id sf eid now Lv op allNid inst p vals fin sched st
      hsl hpz hpl hnd hΦ

-- AND THE DRAIN ARM, WHOSE LEDGER IS CARRIED IN RATHER THAN MINTED.
-- The queue's caps receipt is the caps face's own product, delivered
-- along the walk this arm sits on, so the level it is read at is the
-- walk's -- and the record's count is the ROUND's, since that is the
-- count the carried ledger is denominated at.  The two path conjuncts
-- arrive at the walk's level already, so the arm still never has to
-- know how far the descent climbed and nothing is widened here.
innerΦ-fit-drain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick) (Lv : ℕ)
  (op : AllOp) (allNid inst : NodeId)
  (p : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ)
  (st : EvalSt e) (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
  lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id)))
          (from-inner op allNid inst ↠ p) ≡ true →
  pathSzL? (Caps.cSize (capsAt e sl id)) (from-inner op allNid inst ↠ p) ≡ true →
  pathNestD (from-inner op allNid inst ↠ p) ≤ nestCapAt e sl id →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
         (from-inner op allNid inst ↠ p) vals ≡ true →
  capsDrainOK (capsAt e sl id) sl (capsH e sl id) Lv
    sf allNid p eid now lim (pred act) q sched st →
  depthReact sf op allNid inst p eid now vals sched st fin ≤ capsH e sl id →
  Σ Caps λ c → Σ ℕ λ d → Σ ℕ λ Lv′ → Σ ℕ λ G →
    capsDrainOK c (Sched.slots sched) d Lv′ sf allNid p eid now lim (pred act) q sched st
    × InnerΦCore sf eid now (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
        (drainW sf allNid p eid now q sched st)
        op allNid inst p vals fin sched st c d Lv′ G
innerΦ-fit-drain {e = e} sl id sf eid now Lv op allNid inst p vals fin sched st
                 lim act q od eqn hsl hpz hpl hnd hΦ hdrain hdep =
  capsAt e sl id
  , capsH e sl id
  , Lv
  , (nodeNestAt allNid st ⊔ nestDᵛˢ vals)
  , subst (λ z → capsDrainOK (capsAt e sl id) z (capsH e sl id) Lv
                   sf allNid p eid now lim (pred act) q sched st)
          (sym hsl) hdrain
  , subst (λ z → FaceOK (capsAt e sl id) z) (sym hsl) (faceOK-capsAt e sl id)
  , hdep
  , ∧-trueʳ hpz
  , ≤ᵇ⇒≤ _ _ (T-to (∧-trueˡ hpz))
  , ≤-refl
  , innerΦ-drain-fit sl id sf eid now Lv op allNid inst p vals fin sched st
      lim act q od eqn hsl hpz hpl hnd hΦ

-- THE QUIET ASSEMBLY, and the two ledgers are discharged rather than
-- carried: a lookup that is not a merge at this type cannot satisfy
-- either premise, so both are functions out of an impossibility.
innerΦ-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick) (Lv : ℕ)
  (op : AllOp) (allNid inst : NodeId)
  (p : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ)
  (st : EvalSt e) →
  NotMergeAt {s = s} (lookupNode allNid (EvalSt.nodes st)) →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id)))
          (from-inner op allNid inst ↠ p) ≡ true →
  pathSzL? (Caps.cSize (capsAt e sl id)) (from-inner op allNid inst ↠ p) ≡ true →
  pathNestD (from-inner op allNid inst ↠ p) ≤ nestCapAt e sl id →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
         (from-inner op allNid inst ↠ p) vals ≡ true →
  pathStrat? p ≡ true →
  parkStrat? (pathFloor p) (lookupNode allNid (EvalSt.nodes st)) ≡ true →
  InnerΦBody sf eid now (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
             op allNid inst p vals fin sched st
innerΦ-quiet sl id sf eid now Lv op allNid inst p vals fin sched st ¬m hsl hpz hpl hnd hΦ stP stQ
  with innerΦ-fit-quiet sl id sf eid now Lv op allNid inst p vals fin sched st
         hsl hpz hpl hnd hΦ
... | c , d , Lv′ , G , fok , hdr , hsz , hlen , hG , hnum =
  c , d , 0 , Lv′ , G , fok
  , (λ lim act q od h → ⊥-elim (¬m lim act q od h))
  , (λ lim act q od h → ⊥-elim (¬m lim act q od h))
  , hdr , hsz , hlen , stP , stQ , hG , hnum

-- AND THE DRAIN ASSEMBLY, where the two ledgers are read at the one
-- queue and transported to any the premise names -- which is the same
-- queue, since a lookup has one answer.
innerΦ-drain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick) (Lv : ℕ)
  (op : AllOp) (allNid inst : NodeId)
  (p : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ)
  (st : EvalSt e) (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
  lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id)))
          (from-inner op allNid inst ↠ p) ≡ true →
  pathSzL? (Caps.cSize (capsAt e sl id)) (from-inner op allNid inst ↠ p) ≡ true →
  pathNestD (from-inner op allNid inst ↠ p) ≤ nestCapAt e sl id →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
         (from-inner op allNid inst ↠ p) vals ≡ true →
  frameDrainOK (capsAt e sl id) sl (capsH e sl id) Lv sf eid now
    (from-inner op allNid inst) p vals sched st →
  depthReact sf op allNid inst p eid now vals sched st fin ≤ capsH e sl id →
  pathStrat? p ≡ true →
  parkStrat? (pathFloor p) (lookupNode allNid (EvalSt.nodes st)) ≡ true →
  InnerΦBody sf eid now (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
             op allNid inst p vals fin sched st
innerΦ-drain sl id sf eid now Lv op allNid inst p vals fin sched st lim act q od
             eqn hsl hpz hpl hnd hΦ hfd hdep stP stQ
  with innerΦ-fit-drain sl id sf eid now Lv op allNid inst p vals fin sched st
         lim act q od eqn hsl hpz hpl hnd hΦ (hfd lim act q od eqn) hdep
... | c , d , Lv′ , G , hdrain , fok , hdr , hsz , hlen , hG , hnum =
  c , d , drainW sf allNid p eid now q sched st , Lv′ , G , fok
  , (λ { _ _ _ _ h → transport h hdrain })
  , (λ { _ _ _ _ h →
          transport {P = λ _ _ q′ _ → drainW sf allNid p eid now q′ sched st
                                        ≤ drainW sf allNid p eid now q sched st}
            h ≤-refl })
  , hdr , hsz , hlen , stP , stQ , hG , hnum
  where
  transport : ∀ {ℓ} {lim′ : Maybe ℕ} {act′ : ℕ} {q′ : List (Closed _ _)}
    {od′ : Bool} {P : Maybe ℕ → ℕ → List (Closed _ _) → Bool → Set ℓ} →
    lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim′ act′ q′ od′) →
    P lim act q od → P lim′ act′ q′ od′
  transport h r with trans (sym eqn) h
  ... | refl = r

-- SO THE FIT READS THE TABLE, and every arm but one is quiet.  The
-- five node shapes that are not a merge and the merge stored at
-- another type all reach the same assembly, and only the cell this
-- frame actually drains reaches the other.  The cell is passed as an
-- ARGUMENT beside its own equation rather than abstracted out of the
-- goal, because the goal names the lookup and a `with` would rewrite
-- it out from under both assemblies.
innerΦ-fit-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick) (Lv : ℕ)
  (op : AllOp) (allNid inst : NodeId)
  (p : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ)
  (st : EvalSt e) (ns : Maybe (NodeState Γ)) →
  lookupNode allNid (EvalSt.nodes st) ≡ ns →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id)))
          (from-inner op allNid inst ↠ p) ≡ true →
  pathSzL? (Caps.cSize (capsAt e sl id)) (from-inner op allNid inst ↠ p) ≡ true →
  pathNestD (from-inner op allNid inst ↠ p) ≤ nestCapAt e sl id →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
         (from-inner op allNid inst ↠ p) vals ≡ true →
  frameDrainOK (capsAt e sl id) sl (capsH e sl id) Lv sf eid now
    (from-inner op allNid inst) p vals sched st →
  depthReact sf op allNid inst p eid now vals sched st fin ≤ capsH e sl id →
  pathStrat? p ≡ true →
  parkStrat? (pathFloor p) (lookupNode allNid (EvalSt.nodes st)) ≡ true →
  InnerΦBody sf eid now (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
             op allNid inst p vals fin sched st
innerΦ-fit-go sl id sf eid now Lv op allNid inst p vals fin sched st
              nothing eqn hsl hpz hpl hnd hΦ hfd hdep stP stQ =
  innerΦ-quiet sl id sf eid now Lv op allNid inst p vals fin sched st
    (notMerge-none eqn) hsl hpz hpl hnd hΦ stP stQ
innerΦ-fit-go sl id sf eid now Lv op allNid inst p vals fin sched st
              (just (scan-st v)) eqn hsl hpz hpl hnd hΦ hfd hdep stP stQ =
  innerΦ-quiet sl id sf eid now Lv op allNid inst p vals fin sched st
    (notMerge-scan v eqn) hsl hpz hpl hnd hΦ stP stQ
innerΦ-fit-go sl id sf eid now Lv op allNid inst p vals fin sched st
              (just (take-st k)) eqn hsl hpz hpl hnd hΦ hfd hdep stP stQ =
  innerΦ-quiet sl id sf eid now Lv op allNid inst p vals fin sched st
    (notMerge-take k eqn) hsl hpz hpl hnd hΦ stP stQ
innerΦ-fit-go sl id sf eid now Lv op allNid inst p vals fin sched st
              (just (switch-st cur od)) eqn hsl hpz hpl hnd hΦ hfd hdep stP stQ =
  innerΦ-quiet sl id sf eid now Lv op allNid inst p vals fin sched st
    (notMerge-switch cur od eqn) hsl hpz hpl hnd hΦ stP stQ
innerΦ-fit-go sl id sf eid now Lv op allNid inst p vals fin sched st
              (just (exhaust-st ia od)) eqn hsl hpz hpl hnd hΦ hfd hdep stP stQ =
  innerΦ-quiet sl id sf eid now Lv op allNid inst p vals fin sched st
    (notMerge-exhaust ia od eqn) hsl hpz hpl hnd hΦ stP stQ
innerΦ-fit-go {s = s} sl id sf eid now Lv op allNid inst p vals fin sched st
              (just (mergeAll-st {w} lim act q od)) eqn hsl hpz hpl hnd hΦ hfd hdep stP stQ
  with w ≟ᵗ s
... | no ne =
  innerΦ-quiet sl id sf eid now Lv op allNid inst p vals fin sched st
    (notMerge-other lim act q od eqn ne) hsl hpz hpl hnd hΦ stP stQ
... | yes refl =
  innerΦ-drain sl id sf eid now Lv op allNid inst p vals fin sched st
    lim act q od eqn hsl hpz hpl hnd hΦ hfd hdep stP stQ

innerΦ-fit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick) (Lv : ℕ)
  (op : AllOp) (allNid inst : NodeId)
  (p : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ)
  (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id)))
          (from-inner op allNid inst ↠ p) ≡ true →
  pathSzL? (Caps.cSize (capsAt e sl id)) (from-inner op allNid inst ↠ p) ≡ true →
  pathNestD (from-inner op allNid inst ↠ p) ≤ nestCapAt e sl id →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
         (from-inner op allNid inst ↠ p) vals ≡ true →
  frameDrainOK (capsAt e sl id) sl (capsH e sl id) Lv sf eid now
    (from-inner op allNid inst) p vals sched st →
  depthReact sf op allNid inst p eid now vals sched st fin ≤ capsH e sl id →
  pathStrat? p ≡ true →
  parkStrat? (pathFloor p) (lookupNode allNid (EvalSt.nodes st)) ≡ true →
  -- AND THE THREE REGISTRY READINGS, WHICH THIS FIT ONLY FORWARDS.  They
  -- sit outside the fit's existential precisely so that nothing between
  -- the walk that holds them and the descent that spends them has to
  -- carry them, so the assembly here is a pairing.  The owner of the
  -- outer's cell is one of them because the descent subscribes under a
  -- frame naming that cell, and a caps receipt cannot pay for it.
  pathOrd? (Sched.nextNode sched) (thru-outer op allNid ↠ p) ≡ true →
  pathPark? p st ≡ true →
  regOwn? allNid (pathFloor p) (EvalSt.registry st) ≡ true →
  FrameΦHyp sf eid now (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
            (from-inner op allNid inst) p vals fin sched st
innerΦ-fit sl id sf eid now Lv op allNid inst p vals fin sched st
           hsl hpz hpl hnd hΦ hfd hdep stP stQ stR stK stW =
  stR , stK , stW ,
  innerΦ-fit-go sl id sf eid now Lv op allNid inst p vals fin sched st
    (lookupNode allNid (EvalSt.nodes st)) refl hsl hpz hpl hnd hΦ hfd hdep stP stQ

-- AND THE FRAME'S SIDE-CONDITION IS A CASE SPLIT AND NOTHING ELSE,
-- which is the point of separating it from the walk below: the silent
-- kinds are units, so the walk's recursion never mentions them.
--
-- AND THE ONE ARM THAT DRAINS TAKES ITS LEDGER FROM THE CAPS WALK
-- RATHER THAN MINTING ONE.  The caps face's per-frame product is a
-- `frameDrainOK`, which is `⊤` at the four frames that forward and the
-- queue's whole ledger at the one that re-enters -- so the same
-- premise discharges every arm here, and the drain arm's ledger is the
-- caps face's own rather than a second statement of it.
frameΦ-fit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick) (Lv : ℕ)
  (f : Frame Γ s u) (p : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) (f ↠ p) ≡ true →
  pathSzL? (Caps.cSize (capsAt e sl id)) (f ↠ p) ≡ true →
  pathNestD (f ↠ p) ≤ nestCapAt e sl id →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id) (f ↠ p) vals ≡ true →
  frameDrainOK (capsAt e sl id) sl (capsH e sl id) Lv sf eid now f p vals sched st →
  depthFrame sf eid now f p vals fin sched st ≤ capsH e sl id →
  pathStrat? (f ↠ p) ≡ true →
  framePark? (pathFloor p) f st ≡ true →
  -- AND THE CHAIN'S OWN TWO READINGS, which only the inner descent
  -- spends: it re-reads the outer's frame beneath itself, and neither
  -- half is derivable from the caps receipt this fit already holds.
  pathOrd? (Sched.nextNode sched) (f ↠ p) ≡ true →
  pathPark? (f ↠ p) st ≡ true →
  FrameΦHyp sf eid now (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
            f p vals fin sched st
frameΦ-fit sl id sf eid now Lv (map-f _)  p vals fin sched st _ _ _ _ _ _ _ _ _ _ _ = tt
frameΦ-fit sl id sf eid now Lv (take-f _) p vals fin sched st _ _ _ _ _ _ _ _ _ _ _ = tt
frameΦ-fit sl id sf eid now Lv (scan-f fn nid) p vals fin sched st hsl hpz hpl hnd hΦ _ _ _ _ _ _ =
  scanΦ-fit sl id sf eid now Lv fn nid p vals fin sched st hsl hpz hpl hnd hΦ
frameΦ-fit {s = s} sl id sf eid now Lv (from-inner op allNid inst) p vals fin sched st
           hsl hpz hpl hnd hΦ hfd hdep stP stQ stR stK =
  innerΦ-fit sl id sf eid now Lv op allNid inst p vals fin sched st
    hsl hpz hpl hnd hΦ hfd hdep stP (∧-trueˡ stQ)
    (pathOrd?-outer (Sched.nextNode sched) allNid inst op p stR)
    (proj₂ (∧-true _ _ stK))
    -- and the owner of the outer's cell, off the SAME frame reading the
    -- strat half came from: a `from-inner` names two cells and the outer
    -- is the first, so the membership side is a `≡ᵇ` reflexivity.  The
    -- frame's two source indices are SPELLED because neither the helper's
    -- conclusion nor the node list mentions them, so unification has
    -- nothing to solve them from
    (framePark?-own {s = s} {u = s} (pathFloor p) (from-inner op allNid inst)
       allNid st stQ
       (cong (_∨ ((inst ≡ᵇ allNid) ∨ false)) (≡ᵇ-refl allNid)))
frameΦ-fit sl id sf eid now Lv (thru-outer op nid) p vals fin sched st hsl _ hpl hnd hΦ _ _ _ _ _ _ =
  walk-thru-fit sl id sf eid now op nid p vals fin sched st hsl hpl hnd hΦ

-- THE WALK ITSELF, and it is the fold's own recursion with the grant
-- hung off each frame.  Nothing here is arithmetic: the potential is
-- stepped by the frame law, the size receipt and the depth premise are
-- read off the path's head, and the slot equality survives a frame
-- because a frame never rewrites the schedule's slots.
-- THE REGISTRY-SIDE GRANT FOR THE POTENTIAL, and it is the same gap the
-- live arm's is: a sink hands the values to chains whose paths are in
-- the registry, and the potential is a statement about a PATH, so the
-- one the walk carries says nothing about theirs.
--
-- BUT IT IS NOT THE LIVE ARM'S CROSSING, AND THAT IS THE READING THIS
-- HEADER USED TO CARRY.  The level ledger COMPOUNDS: a hop prices the
-- registry at the level the walk has reached, the next hop at that plus
-- the admitted path's own length, and the hop count is capped by nothing
-- but the dispatch gas -- so no exponential this fuel affords pays for
-- it, and that is why every reading of the live arm closed.  The
-- potential does not compound at all.  `ShareGoΦHyp` and `PathΦHyp`
-- recurse at the very SAME budget, so what a fanned-into chain owes is
-- read against the number the sink was handed and against nothing
-- accumulated on the way in.  The witnesses that closed the level arm
-- are therefore silent about this one, and it has to be read on its own.

-- AND READ ON ITS OWN IT IS NOT A CAP QUESTION AT ALL, WHICH IS WHAT
-- SPLITTING BY THE ADMITTED CHAIN'S TERMINAL HID.  What the fit owes
-- is the chain's own factor times a value's depth plus its own depth,
-- under the instant's nest potential.  Reading that against the LEAF's
-- two numbers closes a root-terminated chain and cannot close any
-- other, since a chain ending at a second hand-over carries the leaf's
-- price MULTIPLIED by its frames' and no leaf price dominates itself
-- times a product.  But the leaf was never the ceiling the fit needs.
-- The budget is; and a chain's factor and depth are both bounded off
-- its size legality at a length budget, with no reference to what its
-- terminal is.  So the split collapses to one arm, and what is left
-- over is an inequality between two arithmetics neither of which
-- mentions a path.
chgF : ℕ → ℕ
chgF B = 2 ^ ((B + B + (B + B)) * (suc B * B))

chgD : ℕ → ℕ
chgD B = (B + B) * B + (B + B) * B

-- the fit read one value at a time, so the list's maximum is never
-- formed and the empty list is not a special case
valsΦ?-ceil : ∀ {n} {Γ : Ctx n} {u t} (B U F D : ℕ) (p q : Path Γ u t)
  (vs : List (Val Γ u)) →
  pathΦF B p ≤ F → pathΦD B p ≤ D →
  (∀ (d : ℕ) → pathΦF B q * (d + pathΦD B q) ≤ U → F * (d + D) ≤ U) →
  valsΦ? B U q vs ≡ true → valsΦ? B U p vs ≡ true
valsΦ?-ceil B U F D p q []       hF hD hh h = refl
valsΦ?-ceil {u = u} B U F D p q (v ∷ vs) hF hD hh h =
  ∧-intro
    (≤ᵇ-true (pathΦF B p * (nestDᵛ u v + pathΦD B p)) U
      (≤-trans (*-mono-≤ hF (+-monoʳ-≤ (nestDᵛ u v) hD))
        (hh (nestDᵛ u v)
          (≤ᵇ⇒≤ (pathΦF B q * (nestDᵛ u v + pathΦD B q)) U
            (T-to (∧-trueˡ h))))))
    (valsΦ?-ceil B U F D p q vs hF hD hh (∧-trueʳ h))

-- WHAT IS LEFT NAMES NO PATH AND NO REGISTRY.  The walk hands the sink
-- its own receipt; what an admitted chain needs is that same shape at
-- the legality ceilings rather than at the leaf's two numbers.  The
-- gap between the two is one exponential in the size cap, against a
-- nest potential carrying a fifth power of it -- so this is headroom
-- in the instant's own arithmetic, and it is what the terminal turned
-- out to be once the leaf stopped being asked to be the ceiling.
-- REFUTED: `Refuted.Sink-Phi-Leaf`, which is why the reading is
--   against the BUDGET and not against the leaf.  That witness
--   quantifies the budget and takes it at the number the sink's own
--   receipt exactly exhausts, so it kills the leaf comparison at an
--   ordinary two-generation share and says nothing whatever about the
--   potential an instant actually carries.
postulate
  sink-fan-headroom : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (i : Fin n) (d : ℕ) →
    pathΦF {Γ = Γ} {s = lookup Γ i} {t = t}
      (Caps.cSize (capsAt e sl id)) (share-sink i)
      * (d + pathΦD {Γ = Γ} {s = lookup Γ i} {t = t}
               (Caps.cSize (capsAt e sl id)) (share-sink i))
      ≤ nestΦAt e sl id →
    chgF (Caps.cSize (capsAt e sl id))
      * (d + chgD (Caps.cSize (capsAt e sl id))) ≤ nestΦAt e sl id

sink-fan-chg : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (i : Fin n) (p : Path Γ (lookup Γ i) t)
  (vals : List (Val Γ (lookup Γ i))) →
  pathSzL? (Caps.cSize (capsAt e sl id)) p ≡ true →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
    (share-sink {t = t} i) vals ≡ true →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id) p vals ≡ true
sink-fan-chg {e = e} sl id i p vals hz hΦ =
  valsΦ?-ceil B (nestΦAt e sl id) (chgF B) (chgD B) p (share-sink i) vals
    (pathΦF-cap-atLen B (B + B) p hf hl)
    (≤-trans (pathΦD-len B p 1≤B hf)
      (+-monoˡ-≤ ((B + B) * B) (*-monoˡ-≤ B hl)))
    (sink-fan-headroom sl id i) hΦ
  where
  B = Caps.cSize (capsAt e sl id)
  1≤B : 1 ≤ B
  1≤B = ≤-trans (s≤s z≤n) (8≤capsAt-size e sl id)
  hf : pathFrameSz? B p ≡ true
  hf = pathSzL?-frames B p hz
  hl : pathLen p ≤ B + B
  hl = pathSzL?-len B p hz

-- THE LEVEL IS WHAT THE FAN WAS MISSING, AND PICKING IT UP COSTS
-- NOTHING.  The walk already stands at a level: `capsWalkOK` reads its
-- caps receipt at `frameStep Lv`, and the sink clause used to hold that
-- receipt and then drop it.  Read at that level the registry's strict
-- size reading is exactly what `capsOK?-regs` returns, so the fan's
-- strict half is a projection rather than a statement -- and the
-- entry-cap reading it used to ask for, the one a registration minted
-- since the instant was entered makes false, is not asked for at all.
--
-- WHAT THE CALLER HAD TO CARRY IS A LEVEL AND NOTHING ELSE, which the
-- caps face already settled and this side had not adopted.  The ring
-- takes its admitted-list receipt at a level of its own under the
-- walk's, spends it after widening, and its depth premise never reads
-- either -- so entering an admitted chain below the top costs the
-- measure nothing, `depthShareGo` being level-free in its own
-- signature.
--
-- THE ONE CONSUMER THAT CANNOT FOLLOW A WIDENING IS THE POTENTIAL
-- PRICING, because what it spends a size receipt on is a LENGTH under
-- the cap its CONCLUSION names.  That is the whole reason the fan
-- reads the registry twice: the walk takes the strict predicate at the
-- level it is standing at, which is free here, and the terminal leaves
-- take the packed pair at the entry cap, which is the statement below.
fan-regsSz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lv : ℕ) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? (frameStep Lv (capsAt e sl id)) sched st ≡ true →
  regsSz? (Caps.cSize (frameStep Lv (capsAt e sl id)))
    (EvalSt.registry st) ≡ true
fan-regsSz {e = e} sl id Lv sched st cok =
  capsOK?-regs (frameStep Lv (capsAt e sl id)) sched st cok

-- THE READING IS FREE OF THE INSTANT'S CAPS EVERYWHERE IT IS SPENT,
-- AND THE ROW IS STILL OPEN.  The frame arm's budget is proven of four
-- bare numbers asking of the cap only that it be at least two, and
-- both spenders of the packed reading are proven cap-generic, so the
-- cap this row names is now a free choice at every site that READS it.
-- That is worth knowing because it settles which end the obstacle sits
-- at: nothing about the supply, the spenders or the grant's arithmetic
-- holds the reading at entry, so a repair does not have to buy any of
-- them, and what remains is the ceiling the chosen cap is priced under.
--
-- AND THE CAP IS PULLED BOTH WAYS BY ONE NUMBER, WHICH IS WHY NO CHOICE
-- OF IT LANDS.  The two obligations the cap answers move in opposite
-- directions and are denominated in the SAME quantity.  A receipt asks
-- the cap to be LARGE: the frame conjunct weakens as it grows, and the
-- entry reading is refuted precisely because an admitted chain carries
-- a frame the entry cap does not cover.  The pricing asks it to be
-- SMALL, and far more steeply: the sink leaf's charge is two to a CUBE
-- of the cap the conclusion names, under a ceiling that affords two to
-- the cap itself.  So the receipt's floor and the pricing's roof are
-- the same variable.  That is a property of the DENOMINATION and not of
-- any endpoint, which is what says the routes below are one route: a
-- cap chosen anywhere -- entry, stepped, climbed, or carried per entry
-- under a ceiling -- is chosen for both jobs at once.
--
-- AND THE GAP BETWEEN FLOOR AND ROOF IS REAL BUT FINITE, WHICH IS THE
-- ONE NUMBER A REPAIR HAS TO BEAT.  The roof is not where it looks: the
-- budget's own exponent is a chosen power of the cap, the ceiling
-- affords two to the cap, and the ladder that fits one under the other
-- is the same lemma at a higher rung -- the tree already carries the
-- square and the fifth power, each at its own threshold, and every
-- threshold on that ladder sits far under the size floor this face
-- proves.  So the roof lifts by several powers for the cost of one
-- arithmetic lemma.  What it does not lift by is unboundedly many: each
-- step of the recurrence roughly squares the cap and so CUBES the
-- degree the charge needs, and the floor admits only a couple of those
-- before the ladder runs past two to the cap.  So the repair a lifted
-- roof would license is exactly one: a receipt at a BOUNDED number of
-- steps.  The walk does not have one -- its level accumulates across
-- the chain list rather than standing still -- which is what turns
-- every cap reading into the same dead end and says the number to beat
-- is not the one to work on.  What is left is not a better cap but a
-- potential that is not a function of one: carried with the entry and
-- re-established where the entry is made.  Read off the pricing, the
-- step function and the ladder's thresholds rather than instantiated.

-- THE LEAVES' HALF OF THE SAME READING, AND THE DOUBLING DOES NOT SAVE
-- IT.  The packed form was adopted because the witness that kills the
-- flat reading satisfies it -- a minted chain of eight frames against
-- an entry size of six, which fails the strict per-frame conjunct
-- while clearing a length side that asks only for twice the cap.  That
-- is a figure about one witness and not a bound the operation
-- respects: a subscribing frame pushes one frame per operator of the
-- INNER, and what bounds the inner is the receipt in hand, taken at
-- the STEPPED cap.  So no multiple of the entry cap is a length bound
-- here, and the row is open on the same ground the flat one died on
-- rather than on a smaller region.
--
-- AND THE PAIR DOES NOT COME APART, WHICH IS WHAT SHUTS THE OBVIOUS
-- ESCAPE.  Keeping the frame conjunct at the entry cap and finding the
-- length elsewhere is the repair a dead length side invites, since
-- AND THE CURRENCY THAT IS NOT A CAP IS ALREADY LEGIBLE IN THE
-- PRICING, WHICH IS WHERE THE NEXT ATTEMPT GOES.  The walk's size
-- charge is LINEAR in the cap it reads, and its coefficients are
-- cap-free: a mapping frame contributes its own operator's syntax and
-- nothing else, a folding frame and a subscribing frame each
-- contribute a fixed weight times the cap, and the sink leaf
-- contributes one fixed cubic in the cap according to whether the
-- chain ends at a sink.  So a chain's charge at EVERY cap is
-- determined by three cap-free numbers read off its syntax -- a syntax
-- sum, a weight, and a sink indicator -- and the cap enters only where
-- the charge is finally spent.
--
-- That is what makes a carried reading stateable at all.  The registry
-- would hold the three numbers, registration would establish them from
-- the walk that minted the entry, and a reader would recover the
-- charge at whatever cap it is spending under -- instead of holding a
-- predicate whose truth depends on which cap happened to be current.
-- It is the depth dimension's shape, whose per-path measure is
-- likewise cap-free and whose receipt is one conjunct indexed by the
-- instant alone.  And nothing recorded below reaches it: every one of
-- those witnesses busts a CAP READING -- a frame wider than the entry
-- cap, a chain longer than twice it -- and none of them bounds the
-- three numbers, which is what says the obstacle was the denomination
-- rather than the registry.  What is left to establish is that the
-- carried numbers survive registration, which is a producer obligation
-- and not an arithmetic one.  Read off the pricing's own clauses
-- rather than instantiated.

-- AND THE TWO READINGS ARE MEASURED APART AT A STATE THE EVALUATOR
-- REACHES, which is what moves this off a reading of the clauses.
-- `Probed.Regs-Charge-Currency` runs a scan that carries syntax as a
-- value under a merge, takes the registry the run actually leaves, and
-- asks both questions of it at a range of caps.  The predicate this
-- statement is written in is false at every cap up to and including
-- forty-eight and turns true at sixty-four; the charge the hand-over
-- actually spends is false at two and true from three upward.  So the
-- gap is more than an order of magnitude wide and it is an interval
-- rather than one awkward cap, and inside it the face's own premise is
-- unavailable while the quantity the face spends is affordable.  What
-- the separation does not buy is the producer obligation: every chain
-- in that registry ends at the root, so the sink leaf's own cubic is
-- never charged, and nothing there says the charge is re-establishable
-- where a registration is made.

-- the frame conjunct is the half the leaves' pricing actually spends.
-- It fails for the same reason at a different witness: the frame a
-- subscribe pushes carries its operator's TRANSFORMER verbatim, and
-- that transformer is legal at the stepped cap, so ONE operator wider
-- than the entry cap registers a short chain that busts the syntax.
-- The two conjuncts therefore fail independently, and the entry cap is
-- not a reading the mint supports in either currency.
--
-- AND THE TOP OF THE INSTANT PAYS FOR ITSELF, which is what makes this
-- a body over one leaf rather than a second monolith.  At level zero
-- the step is the identity, the flat receipt is free from
-- `capsOK?-regs`, and the packed reading is the flat one pointwise --
-- so the mint below carries only the levels above the top, which is
-- where a registration minted since entry can sit.
--
-- REFUTED: `Refuted.Fan-Regs-Packed-Frame`, the same generic form with
--   the packed pair replaced by its FRAME conjunct alone.  Its witness
--   carries ONE operator whose transformer has a syntax size of ten
--   against an entry size of six, so the chain it registers is seven
--   frames -- inside the doubled budget its sibling busts -- and fails
--   the per-frame conjunct instead.  The two halves die at different
--   witnesses, so no split of the pair survives.
-- REFUTED: `Refuted.Fan-Regs-Packed-Len`, which is this statement's
--   own caps-generic form rather than the flat one's.  It is the
--   sibling's witness with nine operators in the arrival's payload
--   instead of two -- same state, node, chain and triple -- and the
--   chain it registers runs to fifteen frames against a doubled entry
--   budget of twelve.  The gap grows with the inner and the inner is
--   priced at the stepped cap, so a larger multiple is refuted by a
--   longer one and the repair is not a bigger budget.
-- REFUTED: `Refuted.Fan-Regs-Entry-Cap`, at the caps-generic form,
--   which is the strongest shape any route may read while `capsAt`'s
--   fields stay sealed.  It discharges every side-condition the walk's
--   doors take, and it is the strict per-frame conjunct it fails.
-- REFUTED: `Refuted.Fan-Chain-Registry`, which is what licenses this
--   being a premise rather than a fact.  Stated over an arbitrary
--   state it fails at a single `register` onto the initial one: a
--   `take` chain one longer than the bound, at EVERY bound rather than
--   at a chosen one, and a mapped ladder of `*All` layers against a
--   unit of one.
-- DEAD ROUTE: serving the LEAVES from a receipt read at the level the
--   fan is standing at, which is what the walk's own half is now
--   restated to take and is therefore free.  The leaves cannot follow
--   it: the potential pricing reads `pathΦF` and `pathΦD` at the cap
--   the budget handed to the terminal is denominated at, and what a
--   size receipt buys that pricing is a LENGTH via `pathSz?-len`
--   landing in an EXPONENT -- a sink's factor is two to the cap times
--   a square of it, and a fanned chain is affordable exactly while its
--   length is under the cap the CONCLUSION is stated at.  A receipt at
--   a larger cap bounds the length by that cap instead and multiplies
--   the exponent by the ratio, which ONE step of `sizeStep` already
--   makes a square: the exponent is cubic in the cap before the step
--   and sixth-power after it.  Nor does weakening only the PREMISE
--   escape it, which is how the caps face repaired its own version --
--   there the conclusions already named the larger cap, and here they
--   cannot.
-- DEAD ROUTE: a FLAT carried field -- one predicate at one cap, added
--   to the walk's bundle -- answering this row together with
--   `walk-share-nestOK`, `sink-fan-chg` and the two inner potential
--   arms, which is what those four sharing an obstacle invites.  Each
--   currency kills it separately and for the same reason: the descent
--   reads a state the instant has STEPPED, every receipt in hand is
--   denominated at or above the cap it stepped to, and each of these
--   predicates WEAKENS as its cap grows -- so a field fixed at one cap
--   is either unavailable at the read or useless at the consumer, and
--   no producer cascade repairs a direction.  The INDEXED form the
--   elimination leaves standing -- a per-entry cap under an absolute
--   ceiling, which `stepFrame-nodes` already shows is not a new
--   mechanism -- dies on the arithmetic directly above, by ONE step of
--   the recurrence rather than at some threshold, so no ceiling is
--   small enough.
-- DEAD ROUTE: DECOUPLING the cap a frame's syntax is known under from
--   the cap the potential is priced at, and spending the stepped-cap
--   receipt -- which is free -- at the smaller pricing cap.  The
--   separation itself is sound and cheap: a map frame's charge is its
--   raw term size and names no cap, every other arm is monotone in the
--   syntax bound, and the sink leaf's share is a constant of the
--   pricing cap alone, so the receipt's cap would appear exactly once,
--   multiplying the length.  It dies on the GRANT rather than on the
--   separation.  `nestΦ-frame-charge` (.Caps-Face.Nest-Arith) hands the
--   frame arm a budget denominated at two to a CUBE of the entry cap,
--   and a stepped-cap receipt prices the same chain at a sixth power,
--   since one `sizeStep` squares the cap and the length is bounded by
--   that same stepped number.  The shortfall is a factor of the cap
--   SQUARED inside the exponent, so it is not a margin to tighten.
--   What this leaves is an obligation with two ends and neither of them
--   the receipt: the grant is fixed at the entry cap and the registry
--   supplies nothing there, so the repair is owed at the pricing's own
--   denomination or at the budget the grant is drawn from.
-- DEAD ROUTE: ENLARGING that budget, which is the second of those two
--   ends and the one that reads affordable.  The headroom is real and
--   it is an entire exponential level: `capsAt-exp2≤capsH` affords two
--   to a DOUBLE exponential of the entry cap while the grant spends two
--   to a cube of it, and the ceiling's own fit already carries a size
--   floor generous enough for any polynomial degree the stepped reading
--   could ask for.  It dies because the stepped cap is not a polynomial
--   in the entry one.  The level a chain is registered at is bounded by
--   the size COUNT of the instant being walked, and a cap stepped that
--   many times is the NEXT instant's entry cap by construction -- which
--   is a blowup OF this instant's height, not a quantity underneath it.
--   So the enlarged budget would have to exceed the ceiling it is
--   fitted under, and the affordable headroom is affordable for the
--   wrong quantity.  Read off the definitions rather than instantiated:
--   the count's own recurrence is sealed for cost, so what is checkable
--   here is the shape of the bound and not a witness at numerals.
-- DEAD ROUTE: moving the pricing's DENOMINATION rather than any
--   receipt, so that the face names the cap the receipt is held at.
--   Both answers die on the pricing rather than on the registry, and
--   `pathΦF`'s sink clause carries the arithmetic: the face cannot
--   follow the cap to the stepped instant, because every frame arm
--   spends a tie between the potential and the depth budget of the
--   instant being WALKED and the descent carries no reading of the
--   next; and the leaf alone cannot follow it either, because the
--   stepped cap is a blowup OF that same depth budget.
-- DEAD ROUTE: retiring the row by dropping the size premise from
--   `sink-fan-chg`, on the reading that an admitted chain arrives
--   carrying the registry's own stratification -- every source
--   strictly under the slot its chain terminates at -- and that a
--   climb up the stratified telescope is bounded by the slot count
--   while naming no cap.  That reading cannot substitute, and the two
--   predicates say so by their own recursion: a terminal-ordering
--   reading walks past every frame and speaks only at the leaf, while
--   the size receipt speaks at each frame it passes.  They are not two
--   readings of one climb -- one counts HOPS and the other counts
--   FRAMES, and no bound on either is a bound on the other.
-- DEAD ROUTE: stating the whole face at the CLIMBED cap -- the one the
--   registry receipt is free at -- now that the grant is denomination-
--   free and neither spender reads the instant.  This is the shape the
--   first two dead routes each left open at one end, and the generic
--   grant closes it rather than opening it.  A pricing exponent is
--   polynomial in the cap it names, and the ceiling the face is fitted
--   under affords an exponent of two to the entry cap; so the climbed
--   cap may exceed the entry one by a power and no more.  It exceeds it
--   by an exponential instead: the walk's level runs to the instant's
--   whole fold count, the cap stepped that far is what the exit door
--   already fits under the NEXT instant's entry cap, and that cap is a
--   blowup of this instant's HEIGHT -- the same height whose logarithm
--   is the entire exponent budget.  So the gap is not a factor at any
--   level and the choice of cap is not where the repair is.  Read off
--   the pricing and the step function rather than instantiated: the
--   fold count is sealed for cost, and what is checkable here is that
--   one endpoint bounds the other.
postulate
  fan-regsSzL-mint : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (Lv : ℕ) (sched : Sched Γ) (st : EvalSt e) →
    capsOK? (frameStep (suc Lv) (capsAt e sl id)) sched st ≡ true →
    all (λ en → pathSzL? (Caps.cSize (capsAt e sl id))
                  (proj₂ (proj₂ (proj₂ en))))
        (EvalSt.registry st) ≡ true

fan-regsSzL : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lv : ℕ) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? (frameStep Lv (capsAt e sl id)) sched st ≡ true →
  all (λ en → pathSzL? (Caps.cSize (capsAt e sl id))
                (proj₂ (proj₂ (proj₂ en))))
      (EvalSt.registry st) ≡ true
fan-regsSzL {e = e} sl id zero sched st cok =
  all-impl _ _
    (λ en h → pathSz?-szL (Caps.cSize (capsAt e sl id))
                (proj₂ (proj₂ (proj₂ en))) h)
    (EvalSt.registry st)
    (capsOK?-regs (capsAt e sl id) sched st
      (subst (λ c → capsOK? c sched st ≡ true) (frameStep-0 (capsAt e sl id)) cok))
fan-regsSzL sl id (suc Lv) sched st cok = fan-regsSzL-mint sl id Lv sched st cok

-- the admitted sublist inherits it, by the generic filter rather than
-- a second copy of the size-shaped one beside it
fan-chain-szL : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (i : Fin n) (st : EvalSt e) →
  all (λ en → pathSzL? (Caps.cSize (capsAt e sl id))
                (proj₂ (proj₂ (proj₂ en))))
      (EvalSt.registry st) ≡ true →
  all (λ rp → pathSzL? (Caps.cSize (capsAt e sl id)) (proj₂ rp))
      (shareAdmit {t = t} i (EvalSt.registry st)) ≡ true
fan-chain-szL {e = e} sl id i st h =
  shareAdmit-chP (λ {u} → pathSzL? {s = u} (Caps.cSize (capsAt e sl id)))
    i (EvalSt.registry st) h

-- ONE CHAIN'S DEPTH OUT OF THE SELECTION'S JOIN.  The cascade-level
-- reading is a ⊔-fold over the whole selection, and the walk spends it
-- one chain at a time, so the fold has to be taken apart before the
-- first `chainStep` sees it.
chainsNest-all : ∀ {n} {Γ : Ctx n} {s t} (D U : ℕ)
  (cs : List (RegId × Path Γ s t)) →
  D + chainsNestD cs ≤ U →
  all (λ rc → D + pathNestD (proj₂ rc) ≤ᵇ U) cs ≡ true
chainsNest-all D U []       h = refl
chainsNest-all D U (c ∷ cs) h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (+-monoʳ-≤ D
                       (m≤m⊔n (pathNestD (proj₂ c)) (chainsNestD cs))) h)))
          (chainsNest-all D U cs
            (≤-trans (+-monoʳ-≤ D (m≤n⊔m (pathNestD (proj₂ c))
                                          (chainsNestD cs))) h))

-- WHAT THE DEPTH IS FOR IS ONE BOUND ON `pathΦD`, and that is a fact
-- about the consumers rather than about this statement.  Every route
-- out of here reaches `frameΦ-fit`, whose three loud arms are the
-- scan charge, the inner fit's pair and the outer frame's -- and the
-- arm that is PROVEN spends the depth on exactly one step, widening
-- the path's Φ-depth to the unit plus a square of the cap.  So the
-- unit is the number the bound is routed THROUGH, not a currency
-- anything downstream is stated in.
--
-- AND THE STORE DENOMINATION BUYS THE FAN-OUT HALF AND STOPS AT THE
-- CHARGE.  Read as the registry's own place in the store measure this
-- is a numeral inequality, so the selection's join is a proven fold
-- and the per-chain receipt follows with no filter lemma between.
-- What it cannot reach is a receipt at the STORE's own maximum: the
-- frame arms are stated at the instant's CAP, so a premise widened to
-- the store has nothing there to be compared against.  The cap
-- reading is the one that lands, the arms already take it, and the
-- store measure delivers it -- which leaves the remaining leaf on
-- where the cap reading's own side-condition comes from.

-- AND THEIR DEPTH AGAINST THE INSTANT'S CAP, which is the second, and
-- which is two proven steps rather than a gap.  The store measure's
-- own decomposition puts `regsNestMax` under `storeNestMax`, and the
-- instant's nest predicate reads that maximum against `nestCapAt`, so
-- the registry's depth under the cap is a composition and no new
-- mathematics.
--
-- AND THE PREMISE IS THE STATEMENT RATHER THAN A CONVENIENCE.  What it
-- buys is the one thing that separates a true reading of this from a
-- false one: the state is an instant's ENTRY state and not an
-- arbitrary one.  Neither denomination survives without it -- the
-- syntactic unit is outrun by a `map-f` frame, which charges the path
-- its function's nesting while the unit is read off the program once,
-- and the cap collapses onto the unit at instant zero -- so what is
-- written here replaces a false statement rather than weakening a true
-- one, and the residue is where the side-condition comes from.
--
-- DEAD ROUTE: spending the cap-side conclusion in the potential's WALK
--   half, which is the half the frame arms visibly charge.  That half
--   multiplies the syntactic UNIT, and it is affordable only because
--   the unit sits under the size cap; `nestCapAt` steps by a factor
--   whose logarithm is already a square of the landing instant's
--   size, so no widening puts it under the same exponential.  The
--   CAP half is where a cap-side receipt lands, and its coefficient
--   carries the path factor's own cap so that a frame arm can spend
--   it there.
-- REFUTED: `Refuted.Reg-Nest-Reached`, at a chain five deep against a
--   unit of four, reached by running, and climbing one per fold.
-- REFUTED: `Refuted.Fan-Chain-Registry`, at a chain three deep
--   against a unit of one, minted by a map whose function carries
--   syntax the program does not.
fan-regsNest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (sched : Sched Γ) (st : EvalSt e) →
  nestOK? e sl id sched st ≡ true →
  regsNestMax (EvalSt.registry st) ≤ nestCapAt e sl id
fan-regsNest {e = e} sl id sched st h =
  ≤-trans (storeNest-regs≤ sched st) (nestOK?-store e sl id sched st h)

-- AND THE SIDE-CONDITION HAS TO COME FROM THE WALK, WHICH IS WHERE IT
-- IS NOT.  The instant's nest predicate is the ambient invariant every
-- cascade door already takes as a hypothesis, so at an instant's ENTRY
-- it is in hand; the fan reads the registry deep inside the descent,
-- at a state the walk has stepped to, and the walk's carried bundle
-- has no nest conjunct of any kind -- only the admitted selection's
-- size, its length against the registration cap, and the share tail.
-- The fact exists one level up and is not carried down, and that gap
-- is the whole of what is asserted here.
--
-- AND WHAT A RUN REGISTERS IS NOT BOUNDED BY A NUMERAL, which is why
-- the missing conjunct cannot be traded for a constant.  A ladder of
-- flatten layers standing above a share deepens the registered chain
-- one rung at a time and lengthens it by two, so both readings climb
-- with the program's own syntax and any bound chosen here is outrun by
-- the fourth layer.
--
-- DEAD ROUTE: threading the predicate down the walk as a premise, so
--   that the door's own hypothesis reaches the read.  It is not
--   preserved: within one instant the store legitimately grows toward
--   the NEXT cap, which is the denomination the frame arms' own nest
--   receipts are stated in, so re-establishing an entry-cap predicate
--   after a frame step asks the step to leave the store where it
--   found it.
-- DEAD ROUTE: deriving the fanned chain's depth receipt from the SIZE
--   receipt the fan already holds, which would need no registry
--   reading at all -- a size-legal path has depth under its length
--   times the size cap and length under that cap, so the cap's square
--   bounds it.  The charge affords the instant's cap plus one square
--   and this asks for two, and the walk half's slack is the unit and
--   the size rather than a square.  It is affordable wherever the cap
--   dominates the square and fails at instant ZERO exactly, the cap
--   being the unit there.
-- DEAD ROUTE: owing this to whatever MINTS a registration, which is
--   where the size analogue directly above sends its own obligation.
--   A mint holds the path it is registering and the program, and the
--   reached counterexample is legal in both: the depth is a fact about
--   the accumulated STORE, which neither the path's frames nor the
--   syntax can report, so no premise threaded to a mint can pay it.
-- DEAD ROUTE: a flat carried field answering this row, the size half
--   and the two inner Φ arms at once, which is where those arms send
--   their own obligation.  `fan-regsSz` carries the elimination across
--   all four currencies, and the indexed shape it leaves standing.
postulate
  walk-share-nestOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
    (Lv : ℕ) (i : Fin n) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    dispatchCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lv
      sf (suc gas) nid now i vals fin sched st →
    Sched.slots sched ≡ sl →
    nestOK? e sl id sched st ≡ true

-- AND THE FAN-OUT HALF IS A PROVEN FOLD RATHER THAN A FILTER LEMMA,
-- which is the whole of what the store denomination bought.  A
-- share's admitted selection is under the registry's own place in the
-- store measure by an induction this tree already had, and the join is
-- taken apart per chain by the one directly above -- so nothing
-- between the postulate and the walk's premise is stated over a
-- boolean predicate.
--
-- AND ITS BOUND IS A PARAMETER, WHICH IS WHAT KEEPS IT OUT OF THE
-- SWAP ABOVE.  Neither step reads the number: the selection is under
-- the registry's maximum whatever that maximum is, and the join comes
-- apart against any ceiling.  So this junction is currency-free and
-- the only thing here denominated in the program's unit is the
-- statement above's own conclusion -- which is where the swap is owed
-- and where it stays.  The bound is EXPLICIT because it stands inside
-- an `all` predicate, where an implicit is a fresh meta per element.
fan-chain-nestD : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (U : ℕ) (i : Fin n) (st : EvalSt e) →
  regsNestMax (EvalSt.registry st) ≤ U →
  all (λ rp → pathNestD (proj₂ rp) ≤ᵇ U)
      (shareAdmit {t = t} i (EvalSt.registry st)) ≡ true
fan-chain-nestD {t = t} U i st h =
  chainsNest-all 0 U (shareAdmit {t = t} i (EvalSt.registry st))
    (≤-trans (shareAdmit-nest i (EvalSt.registry st)) h)

-- AND THE UNIT IS UNDER EVERY CAP, being the cap at instant zero and
-- the recurrence nondecreasing after it.  It stands here because it is
-- the bridge the whole walk crosses on: every producer downstream
-- holds a unit-side receipt and every consumer now asks for a cap-side
-- one, and this is the only step between them -- which is also why it
-- runs one way only, and why the statement above cannot be repaired by
-- reading it back.
unit≤cap : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  nestUnit e sl ≤ nestCapAt e sl id
unit≤cap e sl id =
  ≤-trans (≤-reflexive (sym (nestCapAt-0 e sl))) (nestCap-mono₀ e sl id)

------------------------------------------------------------------
-- THE CONS CLAUSE'S THREE SUMMANDS, NAMED ONCE RATHER THAN AT EVERY
-- CALL.  `lub3-*` must be handed its bounds explicitly -- that is
-- `.Caps-Depth`'s own ruling and it is not negotiable -- and the three
-- bounds of `depthShareGo`'s cons clause are large terms whose
-- `closes`/`st₁`/`r` sub-terms have to be spelled out identically to
-- the clause's own `where`.  Writing them at a call site is how a
-- consumer comes to spell one of them ALMOST right, and an `≤` between
-- two terms that differ under a `foldPath` projection is exactly the
-- failure the explicit-bound rule was introduced to avoid.
--
-- The consuming clause's `with` on the cancellation test is the other
-- half of the reason: it splits the clause into two branches that each
-- need a different projection, and a `where` block reaches only the
-- last of them, so the bounds cannot be named once in the consumer at
-- all.
--
-- AND THEY LIVE HERE AND NOT BESIDE `depthShareGo`, which is where they
-- read as belonging.  The measure sits in a MUTUAL BLOCK, so the dev
-- loop stubs it in its own module and a projection stated there is
-- checked against a postulate that does not reduce -- green on the
-- gate, unverifiable on the loop.  One module out, the measure is an
-- ordinary imported definition and the clause reduces.
------------------------------------------------------------------

depthShareGo-tail : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool) (rid : RegId)
  (p : Path Γ (lookup Γ i) t)
  (ps : List (RegId × Path Γ (lookup Γ i) t))
  (sched : Sched Γ) (st : EvalSt e) {d : ℕ} →
  depthShareGo sf gas id now i vals fin ((rid , p) ∷ ps) sched st ≤ d →
  depthShareGo sf gas id now i vals fin ps sched st ≤ d
depthShareGo-tail sf gas id now i vals fin rid p ps sched st h = lub3-l A B C h
  where
  closes = if fin then close (toℕ i) exhausted ∷ [] else []
  st₁    = record st { delivered = rid ∷ EvalSt.delivered st }
  r      = foldPath sf gas id now (toℕ i) p vals closes fin sched st₁
  A = depthShareGo sf gas id now i vals fin ps sched st
  B = depthFold sf gas id now (toℕ i) p vals closes fin sched st₁
  C = depthShareGo sf gas id now i vals fin ps
        (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

depthShareGo-head : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool) (rid : RegId)
  (p : Path Γ (lookup Γ i) t)
  (ps : List (RegId × Path Γ (lookup Γ i) t))
  (sched : Sched Γ) (st : EvalSt e) {d : ℕ} →
  depthShareGo sf gas id now i vals fin ((rid , p) ∷ ps) sched st ≤ d →
  depthFold sf gas id now (toℕ i) p vals
    (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched
    (record st { delivered = rid ∷ EvalSt.delivered st }) ≤ d
depthShareGo-head sf gas id now i vals fin rid p ps sched st h = lub3-m A B C h
  where
  closes = if fin then close (toℕ i) exhausted ∷ [] else []
  st₁    = record st { delivered = rid ∷ EvalSt.delivered st }
  r      = foldPath sf gas id now (toℕ i) p vals closes fin sched st₁
  A = depthShareGo sf gas id now i vals fin ps sched st
  B = depthFold sf gas id now (toℕ i) p vals closes fin sched st₁
  C = depthShareGo sf gas id now i vals fin ps
        (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

depthShareGo-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool) (rid : RegId)
  (p : Path Γ (lookup Γ i) t)
  (ps : List (RegId × Path Γ (lookup Γ i) t))
  (sched : Sched Γ) (st : EvalSt e) {d : ℕ} →
  depthShareGo sf gas id now i vals fin ((rid , p) ∷ ps) sched st ≤ d →
  depthShareGo sf gas id now i vals fin ps
    (proj₁ (proj₂ (foldPath sf gas id now (toℕ i) p vals
      (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched
      (record st { delivered = rid ∷ EvalSt.delivered st }))))
    (proj₂ (proj₂ (foldPath sf gas id now (toℕ i) p vals
      (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched
      (record st { delivered = rid ∷ EvalSt.delivered st })))) ≤ d
depthShareGo-step sf gas id now i vals fin rid p ps sched st h = lub3-r A B C h
  where
  closes = if fin then close (toℕ i) exhausted ∷ [] else []
  st₁    = record st { delivered = rid ∷ EvalSt.delivered st }
  r      = foldPath sf gas id now (toℕ i) p vals closes fin sched st₁
  A = depthShareGo sf gas id now i vals fin ps sched st
  B = depthFold sf gas id now (toℕ i) p vals closes fin sched st₁
  C = depthShareGo sf gas id now i vals fin ps
        (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

mutual
  walk-ΦHyp-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick) (Lv : ℕ)
    (envSrc : Source) (evs : List (InstEvent (Val Γ t)))
    (path : Path Γ u t) (vals : List (Val Γ u)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    capsWalkOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lv
      sf gas nid now path vals fin sched st →
    depthFold sf gas nid now envSrc path vals evs fin sched st ≤ capsH e sl id →
    Sched.slots sched ≡ sl →
    pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) path ≡ true →
    pathSzL? (Caps.cSize (capsAt e sl id)) path ≡ true →
    pathNestD path ≤ nestCapAt e sl id →
    valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id) path vals ≡ true →
    PathΦHyp sf gas nid now (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
      path vals fin sched st

  -- ONE LEVEL OF THE DISPATCH TELESCOPE, and the two arms it has are
  -- the spent one, which owes nothing, and the latched one, which is
  -- the fan-out fold over the admitted snapshot.  The latch writes the
  -- completed and dying ledgers and never the registry, so the
  -- registry receipt crosses it unchanged -- which is why `fin` is
  -- split here rather than threaded.
  walk-share-ΦHyp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick) (Lv : ℕ)
    (i : Fin n) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    dispatchCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lv
      sf gas nid now i vals fin sched st →
    capsOK? (frameStep Lv (capsAt e sl id)) sched st ≡ true →
    depthDisp sf gas nid now i vals fin sched st ≤ capsH e sl id →
    Sched.slots sched ≡ sl →
    valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
      (share-sink {t = t} i) vals ≡ true →
    DispatchΦHyp sf gas nid now (Caps.cSize (capsAt e sl id))
      (nestΦAt e sl id) i vals fin sched st

  -- THE FAN-OUT FOLD, ENTRY BY ENTRY AND AT THE STATE EACH LEAVES.  A
  -- cancelled entry owes nothing and does not move the state; a
  -- delivered one owes the potential at ITS path -- which is the
  -- terminal split, and the only place the two leaves above are spent
  -- -- and then the whole walk down it, at a level one higher, since
  -- the fold's own registry receipt is the one a chain step reports.
  walk-shareGo-ΦHyp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick) (Lv : ℕ)
    (i : Fin n) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) →
    shareCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lv
      sf gas nid now i vals fin ps sched st →
    depthShareGo sf gas nid now i vals fin ps sched st ≤ capsH e sl id →
    Sched.slots sched ≡ sl →
    all (λ rp → pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) (proj₂ rp))
        ps ≡ true →
    all (λ rp → pathSzL? (Caps.cSize (capsAt e sl id)) (proj₂ rp)) ps ≡ true →
    all (λ rp → pathNestD (proj₂ rp) ≤ᵇ nestCapAt e sl id) ps ≡ true →
    valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
      (share-sink {t = t} i) vals ≡ true →
    ShareGoΦHyp sf gas nid now (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
      i vals fin ps sched st

  walk-share-ΦHyp sl id sf zero nid now Lv i vals fin sched st _ _ _ _ _ = tt
  walk-share-ΦHyp {e = e} sl id sf (suc gas) nid now Lv i vals false sched st
                  hd hck hdd hsl hΦ =
    walk-shareGo-ΦHyp sl id sf gas nid now Lv i vals false
      (shareAdmit i (EvalSt.registry st)) sched st
      (proj₂ (proj₂ hd)) hdd
      hsl (shareAdmit-caps (Caps.cSize (frameStep Lv (capsAt e sl id)))
             i (EvalSt.registry st) (fan-regsSz sl id Lv sched st hck))
          (fan-chain-szL sl id i st (fan-regsSzL sl id Lv sched st hck))
          (fan-chain-nestD (nestCapAt e sl id) i st
             (fan-regsNest sl id sched st
                (walk-share-nestOK sl id sf gas nid now Lv i vals false
                   sched st hd hsl)))
          hΦ
  walk-share-ΦHyp {e = e} sl id sf (suc gas) nid now Lv i vals true sched st
                  hd hck hdd hsl hΦ =
    walk-shareGo-ΦHyp sl id sf gas nid now Lv i vals true
      (shareAdmit i (EvalSt.registry st)) sched (shareLatch i true st)
      (proj₂ (proj₂ hd)) hdd
      hsl (shareAdmit-caps (Caps.cSize (frameStep Lv (capsAt e sl id)))
             i (EvalSt.registry st) (fan-regsSz sl id Lv sched st hck))
          (fan-chain-szL sl id i st (fan-regsSzL sl id Lv sched st hck))
          (fan-chain-nestD (nestCapAt e sl id) i st
             (fan-regsNest sl id sched st
                (walk-share-nestOK sl id sf gas nid now Lv i vals true
                   sched st hd hsl)))
          hΦ

  walk-shareGo-ΦHyp sl id sf gas nid now Lv i vals fin [] sched st
                    _ _ _ _ _ _ _ = tt
  walk-shareGo-ΦHyp {e = e} sl id sf gas nid now Lv i vals fin
                    ((rid , p) ∷ ps) sched st hsg hdsg hsl hpz hpl hnd hΦ
    with any (_≡ᵇ rid) (EvalSt.cancelled st)
  ... | true  = walk-shareGo-ΦHyp sl id sf gas nid now Lv i vals fin ps sched st
                  hsg (depthShareGo-tail sf gas nid now i vals fin rid p ps sched st hdsg)
                  hsl (∧-trueʳ hpz) (∧-trueʳ hpl) (∧-trueʳ hnd) hΦ
  ... | false =
      hΦp
    , walk-ΦHyp-go sl id sf gas nid now Lv (toℕ i) evs p vals fin sched st₀
        (proj₁ hsg)
        (depthShareGo-head sf gas nid now i vals fin rid p ps sched st hdsg)
        hsl hp₀ hpl₀ hndp hΦp
    , walk-shareGo-ΦHyp sl id sf gas nid now (Lv + proj₁ (proj₂ hsg))
        i vals fin ps
        (proj₁ (proj₂ FP)) (proj₂ (proj₂ FP))
        (proj₂ (proj₂ (proj₂ hsg)))
        (depthShareGo-step sf gas nid now i vals fin rid p ps sched st hdsg)
        (trans (foldPath-slots sf gas nid now (toℕ i) p vals evs fin sched st₀) hsl)
        hpzs (∧-trueʳ hpl) (∧-trueʳ hnd)
        hΦ
    where
    B : ℕ
    B = Caps.cSize (capsAt e sl id)
    1≤B : 1 ≤ B
    1≤B = ≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)
    hp₀ : pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) p ≡ true
    hp₀ = ∧-trueˡ hpz
    -- and the rest of the fan is read at the level the fold has climbed
    -- to by the time it reaches them, which the strict reading permits
    hpzs : all (λ rp → pathSz? (Caps.cSize
                   (frameStep (Lv + proj₁ (proj₂ hsg)) (capsAt e sl id)))
                 (proj₂ rp)) ps ≡ true
    hpzs = all-impl _ _
             (λ rp h → pathSz?-widen (proj₂ rp)
                         (iterSize-mono-count B B 1≤B
                            (m≤m+n Lv (proj₁ (proj₂ hsg)))) h)
             ps (∧-trueʳ hpz)
    hpl₀ : pathSzL? B p ≡ true
    hpl₀ = ∧-trueˡ hpl
    hndp : pathNestD p ≤ nestCapAt e sl id
    hndp = ≤ᵇ⇒≤ (pathNestD p) (nestCapAt e sl id) (T-to (∧-trueˡ hnd))
    st₀ : EvalSt e
    st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
    evs = if fin then close (toℕ i) exhausted ∷ [] else []
    FP = foldPath sf gas nid now (toℕ i) p vals evs fin sched st₀
    hΦp : valsΦ? B (nestΦAt e sl id) p vals ≡ true
    hΦp = sink-fan-chg sl id i p vals hpl₀ hΦ

  walk-ΦHyp-go sl id sf gas nid now Lv envSrc evs root vals fin sched st
               _ _ _ _ _ _ _ = tt
  walk-ΦHyp-go sl id sf gas nid now Lv envSrc evs (share-sink i) vals fin sched st
               hcw hdf hsl _ _ _ hΦ =
    walk-share-ΦHyp sl id sf gas nid now Lv i vals fin sched st
      (proj₂ hcw) (proj₁ hcw) hdf hsl hΦ
  walk-ΦHyp-go {e = e} sl id sf gas nid now Lv envSrc evs (f ↠ p) vals fin sched st
               hcw hdf hsl hpz hpl hnd hΦ =
      hF
    , walk-ΦHyp-go sl id sf gas nid now (Lv + proj₁ hL) envSrc
        (evs ++ proj₁ (proj₂ step))
        p (proj₁ step)
        (proj₁ (proj₂ (proj₂ step)))
        (proj₁ (proj₂ (proj₂ (proj₂ step))))
        (proj₂ (proj₂ (proj₂ (proj₂ step))))
        (proj₂ (proj₂ hL))
        (≤-trans (m≤n⊔m (depthFrame sf nid now f p vals fin sched st) _) hdf)
        (trans (KeepsC.slotsEq (stepFrame-keeps sf nid now f p vals fin sched st)) hsl)
        hpz′
        (pathSzL?-tail (Caps.cSize (capsAt e sl id)) f p hpl)
        (≤-trans (pathNestD-step f p) hnd)
        (stepFrame-nest-Φ sf nid now f p vals fin sched st
          (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id) hΦ hF)
    where
    step = stepFrame sf nid now f p vals fin sched st
    hL   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hcw)))))))))
    hord  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hcw))))))))
    hpark = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hcw)))))))))
    -- THE WALK'S OWN FRAME READING, JOINED TO ITS TAIL'S.  The
    -- predicate records the frame's reading at the floor the tail is
    -- read at and the tail's whole reading under it, which is the
    -- recursion `pathStrat?` is defined by -- so the head's reading is
    -- a pairing and mints nothing.  The PARK reading is a pairing too,
    -- and CARRIED rather than derived: deriving it from the caps
    -- receipt is machine-refuted, since a caps-legal state need not be
    -- one the evaluator built.
    stP = ∧-intro (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hcw))))))))
            (capsWalkOK-strat _ _ sl _ _ sf gas nid now p _ _ _ _
               (proj₂ (proj₂ hL)))
    hF = frameΦ-fit sl id sf nid now Lv f p vals fin sched st hsl hpz hpl hnd hΦ
           (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hcw))))))
           (≤-trans (m≤m⊔n (depthFrame sf nid now f p vals fin sched st) _) hdf)
           stP
           (proj₁ (∧-true _ _ hpark))
           hord hpark
    S  = Caps.cSize (capsAt e sl id)
    1≤S : 1 ≤ S
    1≤S = ≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)
    B  = Caps.cSize (frameStep Lv (capsAt e sl id))
    -- THE TAIL'S READING AT THE LEVEL THE TAIL IS WALKED AT.  The head's
    -- comes off the pairing, and the step's own level is then reached by
    -- widening, which the strict reading permits upward.
    hpz₀ : pathSz? B p ≡ true
    hpz₀ = proj₂ (∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p)
                   (proj₂ (∧-true (frameSz? B f)
                            ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) hpz)))
    hpz′ : pathSz? (Caps.cSize (frameStep (Lv + proj₁ hL) (capsAt e sl id))) p
             ≡ true
    hpz′ = pathSz?-widen p (iterSize-mono-count S S 1≤S (m≤m+n Lv (proj₁ hL)))
             hpz₀

-- THE ARRIVAL'S OWN POTENTIAL, READ AGAINST A LENGTH BUDGET RATHER
-- THAN AGAINST THE CAP.  The entry reading is where the walk's
-- side-condition and the fold's own premise are both spent -- one
-- value on the path, so the depth premise the arm was stated with is
-- the whole of it once the path's factor is applied.  What the factor
-- costs is linear in the path's LENGTH, and a chain the registry
-- holds is longer than the cap: a subscribing frame swaps its head
-- for a `from-inner` and pushes one frame per operator of the inner,
-- so the count is the walked one plus an inner the arrival premise
-- bounds by the cap again.  Splitting the length off the frame
-- reading is what lets such a chain enter here at all.
--
-- AND THE ANSWER IS THAT THE CHARGE AFFORDS IT, WHICH IS THE WHOLE
-- POINT OF STATING IT AT A BUDGET.  The premise is the budget the
-- walk's exponent can absorb -- twice the cap -- and it is not a
-- convenience: the walk's charge is three fifth powers beside four
-- squares while a chain of that length prices at four cubes and
-- four squares, so the cubes and the squares each fit inside one
-- fifth power and nothing else moves.  A budget larger than
-- twice the cap is not refuted here, merely unclaimed; twice is what
-- a registered chain is known to need.
entryΦ-atLen : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id L : ℕ) (a : Arrival Γ) (path : Path Γ (arrTy a) t) →
  L ≤ Caps.cSize (capsAt e sl id) + Caps.cSize (capsAt e sl id) →
  pathFrameSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  pathLen path ≤ L →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id) path
         (arrVal a ∷ []) ≡ true
entryΦ-atLen {e = e} sl id L a path hL hf hl hΦ =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ Φfit)) refl
  where
  Sz = Caps.cSize (capsAt e sl id)
  2≤Sz : 2 ≤ Sz
  2≤Sz = 2≤capsAt-size e sl id
  twoSq : (Sz + Sz) * Sz ≤ Sz * Sz + Sz * Sz + (Sz * Sz + Sz * Sz)
  twoSq = ≤-trans (≤-reflexive (*-distribʳ-+ Sz Sz Sz))
                  (m≤m+n (Sz * Sz + Sz * Sz) (Sz * Sz + Sz * Sz))
  dΦ : nestDᵛ (arrTy a) (arrVal a) + pathΦD Sz path
         ≤ nestUnit e sl + (Sz * Sz + Sz * Sz + (Sz * Sz + Sz * Sz)) + Sz
  dΦ =
    ≤-trans (+-monoʳ-≤ (nestDᵛ (arrTy a) (arrVal a)) (pathΦD≤nestD Sz path))
    (≤-trans (≤-reflexive (sym (+-assoc (nestDᵛ (arrTy a) (arrVal a))
                                        (pathNestD path) ((Sz + Sz) * Sz))))
    (≤-trans (+-mono-≤ hΦ twoSq)
             (m≤m+n (nestUnit e sl
                     + (Sz * Sz + Sz * Sz + (Sz * Sz + Sz * Sz))) Sz)))
  Φfit : pathΦF Sz path * (nestDᵛ (arrTy a) (arrVal a) + pathΦD Sz path)
           ≤ nestΦAt e sl id
  Φfit = ≤-trans
    (subst (pathΦF Sz path * (nestDᵛ (arrTy a) (arrVal a) + pathΦD Sz path) ≤_)
           (sym (nestWalkAt-def e sl id))
           (*-mono-≤ (≤-trans (pathΦF-cap-atLen Sz L path hf hl)
                              (^-monoʳ-≤ 2
                                (≤-trans (walkExpL-widen Sz (L + (Sz + Sz))
                                            2≤Sz (+-monoˡ-≤ (Sz + Sz) hL))
                                         (n≤1+n _))))
                     (≤-trans dΦ
                              (m≤m+n (nestUnit e sl
                                      + (Sz * Sz + Sz * Sz
                                         + (Sz * Sz + Sz * Sz))
                                      + Sz)
                                     (Sz * slotWrapSum sl)))))
    (nestWalkAt≤nestΦAt e sl id)

-- AND A CHAIN THE WALK ITSELF PRICED ENTERS AT THE CAP, which is the
-- budget above at the one length a size receipt supplies directly.
entryΦ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (path : Path Γ (arrTy a) t) →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id) path
         (arrVal a ∷ []) ≡ true
entryΦ {e = e} sl id a path hp hΦ =
  entryΦ-atLen sl id (Caps.cSize (capsAt e sl id)) a path
    (m≤m+n (Caps.cSize (capsAt e sl id)) (Caps.cSize (capsAt e sl id)))
    (pathSz?-frames (Caps.cSize (capsAt e sl id)) path hp)
    (pathSz?-len (Caps.cSize (capsAt e sl id)) path hp) hΦ


-- AND THE CHAIN ENTERS THE WALK WITH IT, the path's remaining depth
-- being under the same unit the arrival's is read against.
--
-- AND IT ENTERS CARRYING THE CAPS FACE'S OWN RECEIPT FOR THE SAME
-- WALK, which is what the drain arm inside spends.  The two packages
-- are the same recursion read in two currencies, so the chain door is
-- where they are put beside each other: `chainCapsOK` is the caps walk
-- at exactly this path, values, gas and state, and `depthChain` is the
-- descent measure over exactly that walk.
chain-walk-ΦHyp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lc : ℕ) (a : Arrival Γ) (nextId : Id)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  chainCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lc
    nextId a path sched st →
  depthChain nextId a path sched st ≤ capsH e sl id →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  PathΦHyp (budgetAt e (Sched.slots sched) nextId) n nextId (arrTick a)
    (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
    path (arrVal a ∷ []) (Arrival.isLast a) sched st
chain-walk-ΦHyp {n = n} {e = e} sl id Lc a nextId path sched st hcc hdc hsl hp hΦ =
  walk-ΦHyp-go sl id _ n nextId (arrTick a) Lc (arrSource a)
    (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    path (arrVal a ∷ [])
    (Arrival.isLast a) sched st hcc hdc hsl
    (pathSz?-widen path
      (iterSize-infl (Caps.cSize (capsAt e sl id))
        (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)) Lc
        (Caps.cSize (capsAt e sl id)))
      hp)
    (pathSz?-szL (Caps.cSize (capsAt e sl id)) path hp)
    (≤-trans (≤-trans (m≤n+m (pathNestD path) (nestDᵛ (arrTy a) (arrVal a))) hΦ)
             (unit≤cap e sl id))
    (entryΦ sl id a path hp hΦ)

chainStep-nest-regsC : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lc : ℕ) (a : Arrival Γ) (nextId : Id)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  chainCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lc
    nextId a path sched st →
  depthChain nextId a path sched st ≤ capsH e sl id →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  regsNestMax (EvalSt.registry (proj₂ (proj₂ (chainStep nextId a path sched st))))
    ≤ regsNestMax (EvalSt.registry st)
      ⊔ (nestΦAt e sl id)
chainStep-nest-regsC {e = e} sl id Lc a nextId path sched st hcc hdc hsl hp hΦ =
  foldPath-nest-regs _ _ _ _ _ path (arrVal a ∷ []) _ _ sched st
    (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
    (entryΦ sl id a path hp hΦ)
    (chain-walk-ΦHyp sl id Lc a nextId path sched st hcc hdc hsl hp hΦ)

-- THE NODES ARM IS THE SAME WALK AT THE OTHER PLACE A FRAME STORES,
-- and it is the same three inputs: the entry potential, the walk's
-- per-frame side-condition, and the fold.  What it adds to the
-- registry arm's conclusion is the registry's own join, because a
-- chain that reaches a share fans into paths this one does not walk
-- and stores at their nodes -- the term the path-denominated reading
-- was refuted for missing.  The consumer pays nothing for it: the
-- round already holds the registry under the same ceiling.
--
-- AND IT TAKES THE DEPTH PREMISE THE REGISTRY ARM TAKES.  That is not
-- a convenience of the one call site -- without it the walk has no
-- entry potential, so there is no induction to run at all, and the
-- monolithic form it replaces was asserting the whole walk rather
-- than owing this.
chainStep-nest-nodesC : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lc : ℕ) (a : Arrival Γ) (nextId : Id)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  chainCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lc
    nextId a path sched st →
  depthChain nextId a path sched st ≤ capsH e sl id →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0
        (EvalSt.nodes (proj₂ (proj₂ (chainStep nextId a path sched st))))
    ≤ foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
        ⊔ regsNestMax (EvalSt.registry st)
        ⊔ (nestΦAt e sl id)
chainStep-nest-nodesC {e = e} sl id Lc a nextId path sched st hcc hdc hsl hp hΦ =
  foldPath-nest-nodes _ _ _ _ _ path (arrVal a ∷ []) _ _ sched st
    (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
    (entryΦ sl id a path hp hΦ)
    (chain-walk-ΦHyp sl id Lc a nextId path sched st hcc hdc hsl hp hΦ)

-- AND THAT IS WHAT A WALK CAN CARRY.  A bound the chains preserve has
-- to be one the growth cannot climb past however many chains run, and
-- a growth priced against the ENTRY store is not one -- it compounds.
-- The two arms that write price it against the program instead, so
-- the walk's bound survives a chain exactly when it already covers one
-- instant's increment, which is a condition on the bound and not on
-- the walk.  The slot arm needs no leaf, since a chain threads the
-- vocabulary untouched.
--
-- AND THERE IS NO LIVE ARM, BECAUSE THE STORE THIS PRESERVES HAS NO
-- LIVE PLACE.  What a chain mints into the live list is the next
-- instant's entry -- a payload nothing reads until the schedule
-- advances -- and it is priced at the successor cap by the
-- end-of-instant leaf.  Holding it under THIS instant's ceiling was
-- what the level ledger this fold used to carry was for, and no
-- charge this instant's fuel affords can pay for a mint at a deferred
-- body the depth measure reads as zero; the descent the ceiling
-- serves never reads the live list, so the arm was owed to nothing.
-- REFUTED: Refuted.Chain-Step-Nodes
chainStep-store≤ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lc : ℕ) (a : Arrival Γ) (nextId : Id) (S : ℕ)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  chainCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lc
    nextId a path sched st →
  depthChain nextId a path sched st ≤ capsH e sl id →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  nestΦAt e sl id ≤ S →
  storeSyncMax sched st ≤ S →
  storeSyncMax (proj₁ (proj₂ (chainStep nextId a path sched st)))
               (proj₂ (proj₂ (chainStep nextId a path sched st))) ≤ S
chainStep-store≤ {e = e} sl id Lc a nextId S path sched st
                 hcc hdc hsl hp hΦ hinc hS =
  storeSyncMax-lub sd′ st′ S SL
    (≤-trans (chainStep-nest-nodesC sl id Lc a nextId path sched st
                hcc hdc hsl hp hΦ)
             (⊔-lub (⊔-lub (≤-trans (storeSync-nodes≤ sched st) hS)
                           (≤-trans (storeSync-regs≤ sched st) hS))
                    hinc))
    (≤-trans (chainStep-nest-regsC  sl id Lc a nextId path sched st
                hcc hdc hsl hp hΦ)
             (⊔-lub (≤-trans (storeSync-regs≤  sched st) hS) hinc))
  where
  sd′ = proj₁ (proj₂ (chainStep nextId a path sched st))
  st′ = proj₂ (proj₂ (chainStep nextId a path sched st))
  SL : slotsNestSum (Sched.slots sd′) ≤ S
  SL = ≤-trans (≤-reflexive (cong slotsNestSum
                              (chainStep-slots nextId a path sched st)))
               (≤-trans (storeSync-slots≤ sched st) hS)

-- THE ROUND IS A WALK OVER ITS CHAINS, and the three-callee clause is
-- the one `depthCascade` reports: the tail at the incoming state, the
-- live chain at the delivered-marked one, and the tail again at the
-- state that chain left.
--
-- AND IT CARRIES THE CAPS FACE'S PACKAGE UNPROJECTED, because the
-- measure it bounds is.  Every chain's store step is charged here
-- whatever the cancellation test says, so what pays for it has to be
-- the reading that owes a receipt at every entry rather than at the
-- surviving ones.  The chain leaf supplies each descent bound from the
-- entry store's ceiling, so nothing here needs the round's own bound
-- -- which is what this is proving.
cascade-depth-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lc : ℕ) (a : Arrival Γ) (nextId : Id) (S : ℕ)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  chainsCapsAll (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lc
    a nextId chains sched st →
  sightCeil (sizeᵉ e) S S (nestUnit e sl) ≤ capsH e sl id →
  Sched.slots sched ≡ sl →
  all (λ rc → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rc)) chains ≡ true →
  all (λ rc → nestDᵛ (arrTy a) (arrVal a) + pathNestD (proj₂ rc)
                ≤ᵇ nestUnit e sl) chains ≡ true →
  nestΦAt e sl id ≤ S →
  nestDᵛ (arrTy a) (arrVal a) ≤ S →
  storeSyncMax sched st ≤ S →
  depthCascade a nextId chains sched st
    ≤ sightCeil (sizeᵉ e) S S (nestUnit e sl)
cascade-depth-go sl id Lc a nextId S [] sched st
                 hca hsight hsl hps hΦs hinc hval hS = z≤n
cascade-depth-go {e = e} sl id Lc a nextId S ((rid , c) ∷ cs) sched st
  hca hsight hsl hps hΦs hinc hval hS =
  ⊔-lub (cascade-depth-go sl id Lc a nextId S cs sched st
           (proj₁ hca) hsight hsl hpr hΦr hinc hval hS)
        (⊔-lub (chain-depth-sighted sl id a nextId S c sched st₀ hsl hinc hval hS)
               (cascade-depth-go sl id (Lc + L′) a nextId S cs
                  (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                  (proj₂ (proj₂ (proj₂ (proj₂ hca)))) hsight
                  (trans (chainStep-slots nextId a c sched st₀) hsl)
                  hpr hΦr hinc hval
                  (chainStep-store≤ sl id Lc a nextId S c sched st₀
                     (proj₁ (proj₂ hca)) hdc hsl hpc
                     (≤ᵇ⇒≤ (nestDᵛ (arrTy a) (arrVal a) + pathNestD c)
                           (nestUnit e sl) (T-to hΦc))
                     hinc hS)))
  where
  st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
  hdc = ≤-trans (chain-depth-sighted sl id a nextId S c sched st₀ hsl hinc hval hS)
                hsight
  r   = chainStep nextId a c sched st₀
  hpc = proj₁ (∧-true (pathSz? (Caps.cSize (capsAt e sl id)) c) _ hps)
  hpr = proj₂ (∧-true (pathSz? (Caps.cSize (capsAt e sl id)) c) _ hps)
  hΦc = proj₁ (∧-true (nestDᵛ (arrTy a) (arrVal a) + pathNestD c
                         ≤ᵇ nestUnit e sl) _ hΦs)
  hΦr = proj₂ (∧-true (nestDᵛ (arrTy a) (arrVal a) + pathNestD c
                         ≤ᵇ nestUnit e sl) _ hΦs)
  L′ = proj₁ (proj₂ (proj₂ hca))

-- AND ALL THREE OF THE CEILING'S SUMMANDS ARE THE SAME CAP.  The
-- payload's nesting is held under it by the caller's premise, the
-- store's by the nesting invariant, and the wrap unit IS the cap at
-- instant zero -- so the sighted sum is three readings of one number
-- and the ceiling collapses to a multiple of it.  That collapse is the
-- whole of what the run-side hypotheses buy.
--
-- AND THE PAYLOAD SLOT IS A BARE NUMBER HERE.  A chain's ceiling is
-- stated at the round's grant rather than at the arrival that entered
-- it, because a frame's emitted values are the ones IT built and can be
-- deeper than what arrived; the collapse never read the slot's
-- provenance, only its bound, so it costs nothing to let the caller say
-- which quantity is in it.
sight-collapse : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (V B S : ℕ) →
  V ≤ B →
  S ≤ B →
  nestUnit e sl ≤ B →
  sightCeil (sizeᵉ e) V S (nestUnit e sl) ≤ suc (sizeᵉ e) * suc (3 * B)
sight-collapse {e = e} sl V B S hval hS hu =
  *-monoʳ-≤ (suc (sizeᵉ e)) (s≤s sum≤3B)
  where
  eq : B + B + B ≡ 3 * B
  eq = solve 1 (λ b → b :+ b :+ b := con 3 :* b) refl B
  sum≤3B : V + S + nestUnit e sl ≤ 3 * B
  sum≤3B =
    ≤-trans (+-mono-≤ (+-mono-≤ hval hS) hu) (≤-reflexive eq)


-- AND THE FUEL HAS THAT ROOM, so the comparison the depth face owes
-- the height is assembled rather than asserted.  The caps recurrence
-- steps by a blowup the fuel itself drives and `blowH` is what the
-- fuel climbs by, so the size at an instant and the fuel at that
-- instant are one quantity read once each -- with two exponentials
-- between them, bought by the single spare registration the tower
-- bracket leaves in the pooled walk.
sighted-nest≤capsH : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (V B S : ℕ) →
  V ≤ B →
  S ≤ B →
  nestUnit e sl ≤ B →
  suc (sizeᵉ e) * suc (3 * B) ≤ capsH e sl id →
  sightCeil (sizeᵉ e) V S (nestUnit e sl) ≤ capsH e sl id
sighted-nest≤capsH {e = e} sl id V B S hval hS hu room =
  ≤-trans (sight-collapse {e = e} sl V B S hval hS hu) room

-- THE CASCADE'S CAPS DOOR, STATED WHERE THE STORE CEILING IS.  Every
-- chain of the round gets the caps package, including the ones the
-- evaluator steps over, which is the reading the depth measure needs
-- and the surviving fold does not offer.
--
-- AND IT ASKS FOR THE STORE CEILING BECAUSE ITS THIRD ARM CROSSES A
-- STEP.  The surviving fold takes the round's descent bound as a
-- premise and splits it three ways, and the same split would serve
-- here, since the descent's own recursion is unconditional and
-- three-fold exactly as this reading is.  What closes that route is
-- not the arms but the SUPPLY: the only machine producing that bound
-- for a whole round is the measure this statement is an ingredient
-- of, so taking it here would make the two mutually circular.  The
-- store ceiling is what generates a descent bound at every state the
-- walk reaches rather than at the entry alone, and the package around
-- it is what carries the ceiling across a step -- so the premises are
-- what the third arm costs, not what the caller happens to hold.
--
-- AND THE RECEIPT THE STEP SPENDS IS THIS FOLD'S OWN SECOND ARM, which
-- is why the crossing needs no second walk.  The ceiling moves across
-- a chain step only against that chain's caps reading, and the reading
-- is taken at the state before the step -- so the arm that reports it
-- stands at the state the arm that spends it starts from.
--
-- AND THE Σ'S BOUND IS THE CHAIN LEAF'S OWN, not a share of a round
-- ledger.  The level a crossing climbs by is minted per chain, priced
-- against the deliveries THAT chain makes, so the arm hands back what
-- the leaf handed it and nothing has to be funded across the arms the
-- evaluator steps over.
cascade-caps-all-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lc : ℕ) (a : Arrival Γ) (nextId : Id) (S : ℕ)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (frameStep Lc (capsAt e sl id)) sched st ≡ true →
  sightCeil (sizeᵉ e) S S (nestUnit e sl) ≤ capsH e sl id →
  all (λ rc → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rc)) chains ≡ true →
  all (λ rc → nestDᵛ (arrTy a) (arrVal a) + pathNestD (proj₂ rc)
                ≤ᵇ nestUnit e sl) chains ≡ true →
  all (λ rc → pathStrat? (proj₂ rc)) chains ≡ true →
  all (λ rc → inputsBelowᵛ (pathFloor (proj₂ rc)) (arrTy a) (arrVal a)) chains ≡ true →
  all (λ rc → pathPark? (proj₂ rc) st) chains ≡ true →
  all (λ rc → pathOrd? (Sched.nextNode sched) (proj₂ rc)) chains ≡ true →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  nestClosOK?ᵛ (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  nestΦAt e sl id ≤ S →
  nestDᵛ (arrTy a) (arrVal a) ≤ S →
  storeSyncMax sched st ≤ S →
  (J g i : ℕ) →
  4 + (sizeᵉ e + slotsSize sl) + n + n ≤ g →
  Reached (capsAt e sl id) (capsH e sl id) J (suc g) →
  i + length chains
    ≤ regAt (Caps.cSize (capsAt e sl id)) (Caps.cReg (capsAt e sl id)) J →
  Lc ≤ Ent (capsAt e sl id) (capsH e sl id) J g i →
  chainsCapsAll (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lc
    a nextId chains sched st
cascade-caps-all-go sl id Lc a nextId S [] sched st
  sleq cok hsc hpz hΦs hstr hsv hpk hord hvc hcl hinc hval hS J g i hfl hR hlen hLc = tt
cascade-caps-all-go {n = n} {e = e} sl id Lc a nextId S ((rid , path) ∷ chains) sched st
  sleq cok hsc hpz hΦs hstr hsv hpk hord hvc hcl hinc hval hS J g i hfl hR hlen hLc =
    cascade-caps-all-go sl id Lc a nextId S chains sched st
      sleq cok hsc hpr hΦr hstrr hsvr hpkr hordr hvc hcl hinc hval hS
      J g i hfl hR
      (≤-trans (+-monoʳ-≤ i (n≤1+n (length chains))) hlen) hLc
  , HEAD
  , proj₁ ST
  , proj₁ (proj₂ ST)
  , cascade-caps-all-go sl id (Lc + proj₁ ST) a nextId S chains
      (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
      (trans (chainStep-slots nextId a path sched st′) sleq)
      (proj₂ (proj₂ ST)) hsc hpr hΦr hstrr hsvr
      -- the tail is read at the state the head's step produced
      (chainStep-park nextId a path sched st′ chains
         (pathsPark-delivered chains rid st hpkr))
      (chainStep-ord nextId a path sched st′ chains hordr)
      hvc hcl hinc hval
      (chainStep-store≤ sl id Lc a nextId S path sched st′
         HEAD hdc sleq hpc hΦc hinc hS)
      J g (suc i) hfl hR
      (subst (_≤ regAt B (Caps.cReg c) J) (+-suc i (length chains)) hlen)
      (≤-trans (proj₁ (proj₂ ST)) STEP)
  where
  st′ = record st { delivered = rid ∷ EvalSt.delivered st }
  COK′ = capsOK?-delivered (frameStep Lc (capsAt e sl id)) rid sched st cok
  r   = chainStep nextId a path sched st′
  c   = capsAt e sl id
  B   = Caps.cSize c
  W   = Caps.cWid c
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  D   = delivN st′ (proj₂ (proj₂ r))
  hpc = proj₁ (∧-true (pathSz? B path) _ hpz)
  hpr = proj₂ (∧-true (pathSz? B path) _ hpz)
  hΦc = ≤ᵇ⇒≤ (nestDᵛ (arrTy a) (arrVal a) + pathNestD path) (nestUnit e sl)
          (T-to (proj₁ (∧-true (nestDᵛ (arrTy a) (arrVal a) + pathNestD path
                                 ≤ᵇ nestUnit e sl) _ hΦs)))
  hΦr = proj₂ (∧-true (nestDᵛ (arrTy a) (arrVal a) + pathNestD path
                         ≤ᵇ nestUnit e sl) _ hΦs)
  hstrc = proj₁ (∧-true (pathStrat? path) _ hstr)
  hstrr = proj₂ (∧-true (pathStrat? path) _ hstr)
  hsvc = proj₁ (∧-true (inputsBelowᵛ (pathFloor path) (arrTy a) (arrVal a)) _ hsv)
  hsvr = proj₂ (∧-true (inputsBelowᵛ (pathFloor path) (arrTy a) (arrVal a)) _ hsv)
  hpkc = pathPark-delivered path rid st
           (proj₁ (∧-true (pathPark? path st) _ hpk))
  hpkr = proj₂ (∧-true (pathPark? path st) _ hpk)
  hordc = proj₁ (∧-true (pathOrd? (Sched.nextNode sched) path) _ hord)
  hordr = proj₂ (∧-true (pathOrd? (Sched.nextNode sched) path) _ hord)
  -- this chain's own descent, priced off the store ceiling rather than
  -- off a bound on the round -- which is the premise this door does
  -- not have and the surviving fold does
  hdc = ≤-trans (chain-depth-sighted sl id a nextId S path sched st′
                   sleq hinc hval hS)
                hsc
  step⊑ = frameStep-mono-j c 2≤S (z≤n {Lc})
  c⊑ : c ⊑ᶜ frameStep Lc c
  c⊑ = subst (_⊑ᶜ frameStep Lc c) (frameStep-0 c) step⊑
  HVC : valsCaps? (frameStep Lc c) sl (arrVal a ∷ []) ≡ true
  HVC = valsCaps?-lvl c (frameStep Lc c) sl (arrVal a ∷ []) c⊑
          (∧-intro (∧-intro hvc refl) refl)
  HCL : all (nestClosOK?ᵛ (frameStep Lc c) sl (arrTy a)) (arrVal a ∷ []) ≡ true
  HCL = all-impl _ _
          (λ v h → nestClosOK?ᵛ-widen sl _ v c⊑ h)
          (arrVal a ∷ []) (∧-intro hcl refl)
  hgn = proj₁ (proj₂ (floor-parts (4 + (sizeᵉ e + slotsSize sl)) n n g hfl))
  HI : suc i ≤ regAt B (Caps.cReg c) J
  HI = ≤-trans (subst (suc i ≤_) (sym (+-suc i (length chains)))
                      (s≤s (m≤m+n i (length chains))))
               hlen
  CH≤ : lvls B W d Lc 1 ≤ Pos c d J g i
  CH≤ = lvls-mono 1 1 2≤S ≤-refl ≤-refl hLc ≤-refl
  HEAD = arr-chain-caps sl id Lc a nextId path sched st′ sleq COK′ HVC HCL
           (pathSz?-widen path (proj₁ c⊑) hpc) hdc hstrc hsvc hpkc hordc
           (g , Pos c d J g i , hfl , CH≤ , walk J g i HI hR)
  ST  = chainStep-caps sl id Lc a nextId path sched st′ sleq COK′
          (pathSz?-widen path (proj₁ c⊑) hpc)
          (valCaps?-widen sl (arrTy a) (arrVal a) c⊑ hvc) hdc hstrc hsvc
          hpkc hordc
  -- and the fold's own climb lands on the NEXT position exactly when
  -- this chain's deliveries fit the budget read at this one
  STEP : lvls B W d Lc (suc D) ≤ Ent c d J g (suc i)
  STEP = ≤-trans (lvls-mono (suc D) (suc D) 2≤S ≤-refl ≤-refl hLc ≤-refl)
                 (ent-step c d J g i D 2≤S
                    (chain-deliv-cap sl id a nextId path sched st′ Lc J g i
                       sleq hgn COK′ (pathSz?-widen path (proj₁ c⊑) hpc)
                       HVC hdc hLc hstrc hsvc hpkc hordc))

cascade-caps-all : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id) (S : ℕ)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  sightCeil (sizeᵉ e) S S (nestUnit e sl) ≤ capsH e sl id →
  all (λ rc → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rc))
      (chainsOf a st) ≡ true →
  all (λ rc → nestDᵛ (arrTy a) (arrVal a) + pathNestD (proj₂ rc)
                ≤ᵇ nestUnit e sl) (chainsOf a st) ≡ true →
  all (λ rc → inputsBelowᵛ (pathFloor (proj₂ rc)) (arrTy a) (arrVal a))
      (chainsOf a st) ≡ true →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  nestClosOK?ᵛ (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  nestΦAt e sl id ≤ S →
  nestDᵛ (arrTy a) (arrVal a) ≤ S →
  storeSyncMax sched (cascadeLatch a st) ≤ S →
  chainsCapsAll (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) 0
    a nextId (chainsOf a st) sched (cascadeLatch a st)
cascade-caps-all {e = e} sl id a nextId S sched st sleq cok hsc
                 hpz hΦs hsv hvc hcl hinc hval hsn =
  cascade-caps-all-go sl id 0 a nextId S (chainsOf a st) sched
    (cascadeLatch a st) sleq
    (subst (λ x → capsOK? x sched (cascadeLatch a st) ≡ true)
           (sym (frameStep-0 (capsAt e sl id)))
           (cascadeLatch-caps (capsAt e sl id) a sched st cok))
    hsc hpz hΦs
    (cascade-admit-entry (capsAt e sl id) a sched st cok) hsv
    (cascade-admit-park a st (capsOK?-regPark (capsAt e sl id) sched st cok))
    (cascade-admit-ord a sched st (capsOK?-regOrd (capsAt e sl id) sched st cok))
    hvc hcl hinc hval hsn
    0 (Caps.cSize (capsAt e sl id)) 0
    (capsAt-round-size e sl id) base REGLEN ≤-refl
  where
  c = capsAt e sl id
  -- the round has as many positions as the registry has entries, and
  -- the cascade walks a sublist of it
  REGLEN : 0 + length (chainsOf a st) ≤ regAt (Caps.cSize c) (Caps.cReg c) 0
  REGLEN = ≤-trans (≤-trans (chainsOf-length a st)
                            (capsOK?-count c sched st cok))
                   (≤-reflexive (sym (*-identityʳ (Caps.cReg c))))

-- AND IT ENTERS CARRYING THE ROUND'S CAPS PACKAGE, which is what the
-- store step inside spends.  The two run-side premises the caps
-- reading wants -- the value's own caps and its closures' -- are two
-- of the three the instant loop already prices this arrival by, so the
-- door widens by what the caller was holding anyway.
--
-- AND THE STORE CEILING IT ENTERS UNDER IS THE NESTING INVARIANT'S,
-- read down to the three places a descent can see: the invariant
-- holds all four places under the cap, and the synchronous store is
-- under the four-place one, so the ceiling costs one line.
cascade-depth-sighted : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  nestClosOK?ᵛ (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  all (λ rc → inputsBelowᵛ (pathFloor (proj₂ rc)) (arrTy a) (arrVal a))
      (chainsOf a st) ≡ true →
  depthCascade a nextId (chainsOf a st) sched (cascadeLatch a st)
    ≤ sightCeil (sizeᵉ e) (nestΦAt e sl id) (nestΦAt e sl id) (nestUnit e sl)
cascade-depth-sighted {e = e} sl id a nextId sched st
                      hsl hok hn hval valC closC strC =
  cascade-depth-go sl id 0 a nextId (nestΦAt e sl id)
    (chainsOf a st) sched (cascadeLatch a st)
    (cascade-caps-all sl id a nextId (nestΦAt e sl id) sched st hsl hok
       SIGHT CHAINPZ CHAINΦ strC valC closC ≤-refl VALΦ STORE)
    SIGHT
    hsl
    CHAINPZ
    CHAINΦ
    ≤-refl
    VALΦ
    STORE
  where
  VALΦ = ≤-trans hval (nestCapAt≤nestΦAt e sl id)
  CHAINPZ = chainsOf-caps (Caps.cSize (capsAt e sl id)) a st
              (capsOK?-regs (capsAt e sl id) sched st hok)
  CHAINΦ = chainsNest-all (nestDᵛ (arrTy a) (arrVal a)) (nestUnit e sl)
             (chainsOf a st)
             (arr-chains-nest-syn sl id a sched st hsl hok hn)
  STORE = ≤-trans (storeSyncMax≤storeNestMax sched (cascadeLatch a st))
            (≤-trans (nestOK?-store e sl id sched (cascadeLatch a st)
                       (trans (nestOK?-latch e sl id a sched st) hn))
                     (nestCapAt≤nestΦAt e sl id))
  SIGHT = sighted-nest≤capsH sl id (nestΦAt e sl id) (nestΦAt e sl id)
            (nestΦAt e sl id) ≤-refl ≤-refl
            (≤-trans (unit≤cap e sl id) (nestCapAt≤nestΦAt e sl id))
            (nestΦ-sight≤capsH e sl id)

-- THE ROUND'S DEPTH FITS THE INSTANT'S FUEL, assembled rather than
-- asserted: the descent goes under what the round can see, and what
-- the round can see goes under the fuel.  The split is the point -- the
-- first half is a statement about the evaluator at concrete programs
-- and the second is arithmetic about two currencies, and only the
-- second is where the height comparison lives.
--
-- THE SIZE PREMISE IS CARRIED AND NOT SPENT.  It is the caller's, and
-- it belongs to the statement rather than to this route: a descent
-- bounded through the payload's NESTING says nothing about the
-- payload's size, and the consumers that hand this premise in are
-- pricing the same arrival on the size axis in the same breath.
cascade-depth-capsH : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  nestClosOK?ᵛ (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  all (λ rc → inputsBelowᵛ (pathFloor (proj₂ rc)) (arrTy a) (arrVal a))
      (chainsOf a st) ≡ true →
  depthCascade a nextId (chainsOf a st) sched (cascadeLatch a st)
    ≤ capsH e sl id
cascade-depth-capsH {e = e} sl id a nextId sched st hsl hcaps hnest hval hsz valC closC strC =
  ≤-trans (cascade-depth-sighted sl id a nextId sched st hsl hcaps hnest hval valC closC strC)
          (sighted-nest≤capsH sl id B B B ≤-refl ≤-refl
             (≤-trans (unit≤cap e sl id)
               (nestCapAt≤nestΦAt e sl id))
             (nestΦ-sight≤capsH e sl id))
  where
  B = nestΦAt e sl id

-- THE WALK'S POST-STATE FITS THE INSTANT'S EXIT CAP, which is the caps
-- face's own product read one clause before the instant ends.  The
-- store face needs it at exactly this point: its measure is taken over
-- the walk's post-state, before the finish shortens any list, so a fit
-- stated after the finish is not one it can spend.
caps-go :
  SiCType →
  IfcType →
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  nestClosOK?ᵛ (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  all (λ rc → inputsBelowᵛ (pathFloor (proj₂ rc)) (arrTy a) (arrVal a))
      (chainsOf a st) ≡ true →
  let r = cascadeGo a nextId (chainsOf a st) sched (cascadeLatch a st)
  in capsOK? (capsAt e sl (suc id)) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
caps-go siC ifc {e = e} sl id a nextId sched st slEq pre nok bnd val closV strC =
  capsOK?-mono (frameStep j c) (capsAt e sl (suc id))
               (proj₁ (proj₂ GOr)) (proj₂ (proj₂ GOr))
               (frameStep-mono-j c (2≤capsAt-size e sl id) jFits)
               (proj₂ (proj₂ GO))
  where
  c    = capsAt e sl id
  st₀  = cascadeLatch a st
  GO   = cascadeGo-caps siC ifc c (capsH e sl id) a nextId (chainsOf a st) sl sched st₀
           (2≤capsAt-size e sl id) (1≤capsAt-reg e sl id)
           (slotsCaps?-capsAt e sl id) slEq
           (cascadeLatch-caps c a sched st pre) val
           (chainsOf-caps (Caps.cSize c) a st (capsOK?-regs c sched st pre))
           (n≤capsAt-size e sl id)
           (≤-trans (chainsOf-length a st) (capsOK?-count c sched st pre))
           -- H1 is FREE here: capsAt's base formula already contains the
           -- slot store as a summand
           (≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e))
                    (capsAt-base-size e sl id))
           (cascade-depth-capsH sl id a nextId sched st slEq pre nok bnd
             (≤ᵇ⇒≤ (sizeᵛ (arrTy a) (arrVal a)) (Caps.cSize c)
                   (T-to (valCaps?-size c sl (arrTy a) (arrVal a) val)))
             val closV strC)
           -- the entry reading, both halves local: the chain half is the
           -- registry's own conjunct carried across `chainsOf`, and the
           -- payload half is `strC` in the list shape the walk reads
           (chainsOf-strat a st (registry-entStrat c sched st pre))
           (chainsStrat?-one (arrVal a) (chainsOf a st) strC)
           -- and the chain's two entry readings, both filters of the
           -- registry's own.  The order half is state-blind, so the
           -- latch does not move it; the park half is taken AT the
           -- latched state, which is the state the walk enters
           (chP?-∧ (λ {u} κ → pathOrd? (Sched.nextNode sched) κ)
                   (λ {u} κ → pathPark? κ st₀) (chainsOf a st)
              (cascade-admit-ord a sched st (capsOK?-regOrd c sched st pre))
              (cascade-admit-park a st (capsOK?-regPark c sched st pre)))
  GOr   = cascadeGo a nextId (chainsOf a st) sched st₀
  j     = proj₁ GO
  jFits = proj₁ (proj₂ GO)

-- AND THE WHOLE INSTANT IS THE SAME ROUND ONE STEP ON.  `cascade` is a
-- latch, a walk and a finish; the walk's post-state is already at the
-- exit cap above, and the finish only shortens lists, so the instant's
-- fit is the walk's fit widened by the one clause between them.
caps-tick :
  SiCType →
  IfcType →
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  nestClosOK?ᵛ (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  all (λ rc → inputsBelowᵛ (pathFloor (proj₂ rc)) (arrTy a) (arrVal a))
      (chainsOf a st) ≡ true →
  let r = cascade a nextId sched st
  in capsOK? (capsAt e sl (suc id)) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
caps-tick siC ifc {e = e} sl id a nextId sched st slEq pre nok bnd val closV strC =
  cascadeFinish-caps (capsAt e sl (suc id)) a (proj₁ (proj₂ GOr)) (proj₂ (proj₂ GOr))
    (caps-go siC ifc sl id a nextId sched st slEq pre nok bnd val closV strC)
  where
  GOr = cascadeGo a nextId (chainsOf a st) sched (cascadeLatch a st)

-- REFUTED: `caps-frame-boundary-absurd`
--   (sizeStep C C ≤ C is impossible for 1 ≤ C) and `reach-via-size-absurd`
--   (2 ^ C ≤ C is impossible) now live in `refuted/Refuted/Caps-Face.agda`,
--   checked by `make refuted`.  Do not re-attempt either bound here.


-- (`reach-resets`, the reset cluster this section's prose names, is
-- declared ABOVE the face postulate block — `thruOuter-face` consumes
-- it and is itself consumed before this point in the file.)

------------------------------------------------------------------
-- HOP DESCENT, the *All clause's missing edge — AND THE OPEN HOLE.

