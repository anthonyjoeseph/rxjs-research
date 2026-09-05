-- Verify-Budget-Sufficient.Caps-Face.Part7.Depth-Fit
-- pathNestD-step … caps-tick
module Verify-Budget-Sufficient.Caps-Face.Part7.Depth-Fit where

open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (*-assoc; ≤ᵇ⇒≤; ≤⇒≤ᵇ; ^-monoʳ-≤; *-monoˡ-≤; *-cancelˡ-≤; ≤-trans; ≤-refl; ≤-reflexive; m≤m+n;
  m≤n+m; n≤1+n; *-identityʳ; *-identityˡ; *-mono-≤; *-monoʳ-≤; +-monoʳ-≤; +-monoˡ-≤; ⊔-lub;
  m≤m⊔n; m≤n⊔m; +-mono-≤; *-distribʳ-+; +-suc; +-assoc)
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
  using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂)

open import Rx.Prim      using (Tick; Id; _at_from_as_; Gas; after_,_; close; exhausted;
                                Source; InstEvent)
open import Rx.Exp       using (obs; Ctx; Closed; Val; Fn; _×ᵗ_; _≟ᵗ_; sizeᵉ; sizeᵛ)
open import Rx.Nest-Depth using (nestDᵛ; nestDᵗ)
open import Verify-Budget-Sufficient.Depth-Sighted using (ValsFit; valsFit-of-max)
open import Verify-Budget-Sufficient.Nest-Walk using
  (nestDᵛˢ; nodeNestAt; capsDrainOK; FaceOK; faceOK;
   frameDrainOK; capsWalkOK; dispatchCapsOK; shareCapsOK)
open import Verify-Budget-Sufficient.Nest-Burst using (drainW)
open import Verify-Budget-Sufficient.Nest-Cap using (nestFac; nestU)
open import Verify-Budget-Sufficient.Deliveries using
  (delivN)
open import Verify-Budget-Sufficient.Deliver-Measure using
  (chainsLenSum)
open import Verify-Budget-Sufficient.Walk-Factor using
  (pathΦF; pathΦF-cap; pathΦD; pathRoots; pathΦF-cap-root; pathΦD-cap-root)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using
  (foldPath-nest-regs; PathΦHyp; DispatchΦHyp; ShareGoΦHyp; FrameΦHyp; valsΦ?; valsSz?;
  valsΦ?-mono; valsSz?-mono; stepFrame-nest-Φ; stepFrame-sz; stepFrame-sz-store; szCount;
  frameCh; walkSzOK; dispatchSzOK; shareGoSzOK; Φ-to-bound)
open import Verify-Budget-Sufficient.Nodes-Nest-Walk using (foldPath-nest-nodes)
open import Verify-Budget-Sufficient.Nest-Ceiling using
  (Reached; Ent; Pos; base; walk; ent-step)
open import Verify-Budget-Sufficient.Live-Nest-Walk using
  (foldPath-nest-live; PathLiveHyp; DispatchLiveHyp; ShareGoLiveHyp; FrameLiveHyp;
  frameLive-of-sz)
open import Verify-Budget-Sufficient.Nest-Store using
  (chainsNestD; pathNestD; storeNestMax; nestCapAt; nestOK?; realWidAt-def; nestUnit;
  slotsNestSum; liveNest; nodeNest; regsNestMax; sightCeil; slotWrapSum; nestCapAt-0;
  nestCap-mono₀; nestOK?-latch; nestOK?-store; shareAdmit-nest; storeNestMax-lub; storeNest-slots≤;
  storeNest-live≤; storeNest-nodes≤; storeNest-regs≤)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; arrVal; RegId; lookupNode; NodeId; _↠_; Frame; AllOp; map-f; scan-f;
  take-f; from-inner; thru-outer; cascadeLatch; chainsOf; cascadeGo; Path; arrTy; stepFrame;
  subscribeInner; innerFinish; cascade; share-sink; root; fLvlD; sLvlD; chainStep; budgetAt;
  arrSource; arrTick; iterSize; shareAdmit; shareLatch; foldPath; NodeState; mergeAll-st; scan-st; take-st;
  switch-st; exhaust-st; regAt; lvls)
open import Rx.Slots using (Slots; slotsSize)

open import Verify-Budget-Sufficient.Caps using
  (1≤capsAt-reg; 2≤capsAt-size; 8≤capsAt-size; B2-cReg≤cSize; Caps; capsAt; capsAt-base-size;
  capsH; frameStep; frameStep-0; sizeCount; iterSize-infl; iterSize-mono-count;
  frameStep-mono-j; _⊑ᶜ_; lvls-mono)
open import Verify-Budget-Sufficient.Measures using
  (pathLen; ∧-true; 2X≡X+X; all-impl; boundedNode)
open import Verify-Budget-Sufficient.Keeps-Ring using
  (KeepsC; stepFrame-keeps)
open import Verify-Budget-Sufficient.Caps-Nest using
  (nest)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthInner; depthFin; depthCascade; depthReact;
         depthFrame; depthFold; depthDisp; depthShareGo; depthChain;
         lub3-l; lub3-m; lub3-r)

open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (capsAt-round-size; capsOK?; capsOK?-mono; eventCaps?; frameSz?; n≤capsAt-size; pathSz?;
  pathSz?-widen; regsSz?; slotsCaps?; valCaps?; nestClosOK?ᵛ; nestClosOK?ᵛ-widen; iterSize-+)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (capsOK?-count; capsOK?-nodeSz; capsOK?-regs; frameBud; slotsCaps?-capsAt; valsCaps?;
  valsCaps?-lvl; foldPath-slots; shareAdmit-caps)
open import Verify-Budget-Sufficient.Caps-Face.Part3 using
  (valCaps?-size; valCaps?-widen)
open import Decide using (T-to; T⇒≡true; ∧-intro; ∧-trueˡ; ∧-trueʳ)
open import Verify-Budget-Sufficient.Caps-Face.Nest-Arith using
  (nestWalkAt-def; nestΦAt; nestΦ-sight≤capsH; nestCapAt≤nestΦAt; nestWalkAt≤nestΦAt;
  iterSize≤2^; walkExp-widen; nestΦ-frame-charge)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Caps using
  (cascadeFinish-caps; cascadeGo-caps; cascadeLatch-caps; chainStep-slots; chainsOf-caps; chainsOf-length)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Ring-Vocabulary using
  (floor-parts)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Nodes using
  (chains-count-width)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Nest using
  (arr-chains-nest-syn)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Arrival-Ledger using
  (chainsGo-sz; chainsLenSum-bound)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Arrival-Caps using
  (chain-depth-sighted; arr-chain-caps; chainStep-caps; chain-deliv-cap)
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
  pathΦD B p ≤ pathNestD p + B * B
pathΦD≤nestD B root                   = z≤n
pathΦD≤nestD B (share-sink _)         = ≤-refl
pathΦD≤nestD B (map-f fn ↠ p)         =
  ≤-trans (+-monoʳ-≤ (nestDᵗ fn) (pathΦD≤nestD B p))
          (≤-reflexive (sym (+-assoc (nestDᵗ fn) (pathNestD p) (B * B))))
pathΦD≤nestD B (scan-f fn _ ↠ p)      =
  ≤-trans (+-monoʳ-≤ (nestDᵗ fn) (pathΦD≤nestD B p))
          (≤-reflexive (sym (+-assoc (nestDᵗ fn) (pathNestD p) (B * B))))
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
walk-thru-fit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick)
  (op : AllOp) (nid : NodeId)
  (p : Path Γ u t) (vals : List (Val Γ (obs u))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (capsAt e sl id)) (thru-outer op nid ↠ p) ≡ true →
  pathNestD (thru-outer op nid ↠ p) ≤ nestCapAt e sl id →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
         (thru-outer op nid ↠ p) vals ≡ true →
  FrameΦHyp sf eid now (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
            (thru-outer op nid) p vals fin sched st
walk-thru-fit {n = n} {e = e} sl id sf eid now op nid p vals fin sched st
              hsl hpz hnd hΦ =
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
                 (≤-reflexive (sym (2X≡X+X (nestΦAt e sl id)))))))
  where
  S    = Caps.cSize (capsAt e sl id)
  Q    = pathΦF S p
  Dn   = pathNestD p
  D    = pathΦD S p
  M    = nestDᵛˢ vals
  W    = slotWrapSum sl
  G    = Dn + M + n * W
  hpp  : pathSz? S p ≡ true
  hpp  = ∧-trueʳ hpz
  2≤S  = 2≤capsAt-size e sl id
  1≤S  = ≤-trans (s≤s z≤n) 2≤S
  EXP  : ℕ
  EXP  = (S + S) * (suc S * S)
  Q≤   : Q ≤ 2 ^ EXP
  Q≤   = pathΦF-cap S p hpp
  D≤   : D ≤ nestCapAt e sl id + S * S
  D≤   = ≤-trans (pathΦD≤nestD S p)
                 (+-monoˡ-≤ (S * S) (≤-trans (n≤1+n (pathNestD p)) hnd))
  n≤S  : n ≤ S
  n≤S  = n≤capsAt-size e sl id
  2≤2^S : 2 ≤ 2 ^ S
  2≤2^S = ≤-trans (≤-reflexive (sym (*-identityʳ 2))) (^-monoʳ-≤ 2 1≤S)
  -- the values in flight, paid by the outer frame's own factor
  hA   : 2 ^ S * (Q * M) ≤ nestΦAt e sl id
  hA   = ≤-trans (≤-reflexive (sym (*-assoc (2 ^ S) Q M)))
                 (Φ-to-bound S (nestΦAt e sl id) (thru-outer op nid ↠ p)
                             vals hΦ)
  hA2  : 2 * (Q * M) ≤ nestΦAt e sl id
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
  hBC2 : 2 * (2 * (Q * D) + Q * (n * W)) ≤ nestΦAt e sl id
  hBC2 =
    ≤-trans (≤-reflexive (reshape Q D (n * W)))
    (≤-trans (+-mono-≤ (*-monoʳ-≤ 4 (*-mono-≤ Q≤ D≤))
                       (*-monoʳ-≤ 2 (*-mono-≤ Q≤ (*-monoˡ-≤ W n≤S))))
             (nestΦ-frame-charge e sl id))
  spread : 2 * (Q * (D + M + n * W + D))
             ≡ 2 * (Q * M) + 2 * (2 * (Q * D) + Q * (n * W))
  spread =
    solve 4 (λ q d m w →
               con 2 :* (q :* (d :+ m :+ w :+ d))
                 := con 2 :* (q :* m)
                    :+ con 2 :* (con 2 :* (q :* d) :+ q :* w))
          refl Q D M (n * W)

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
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick)
    (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId)
    (p : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ)
    (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    pathSz? (Caps.cSize (capsAt e sl id)) (scan-f fn nid ↠ p) ≡ true →
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
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick)
    (op : AllOp) (allNid inst : NodeId)
    (p : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ)
    (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    pathSz? (Caps.cSize (capsAt e sl id)) (from-inner op allNid inst ↠ p) ≡ true →
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
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick)
    (op : AllOp) (allNid inst : NodeId)
    (p : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ)
    (st : EvalSt e) (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
    lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
    Sched.slots sched ≡ sl →
    pathSz? (Caps.cSize (capsAt e sl id)) (from-inner op allNid inst ↠ p) ≡ true →
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

-- THE QUIET ARM, ASSEMBLED, and the level it reports is zero because
-- nothing here descends: no queue, no subscribe, so the entry's own
-- receipts are already the ones the arm owes.
innerΦ-fit-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick)
  (op : AllOp) (allNid inst : NodeId)
  (p : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ)
  (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (capsAt e sl id)) (from-inner op allNid inst ↠ p) ≡ true →
  pathNestD (from-inner op allNid inst ↠ p) ≤ nestCapAt e sl id →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
         (from-inner op allNid inst ↠ p) vals ≡ true →
  Σ Caps λ c → Σ ℕ λ d → Σ ℕ λ Lv → Σ ℕ λ G →
    InnerΦCore sf eid now (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id) 0
      op allNid inst p vals fin sched st c d Lv G
innerΦ-fit-quiet {e = e} sl id sf eid now op allNid inst p vals fin sched st
                 hsl hpz hnd hΦ =
  capsAt e sl id
  , depthReact sf op allNid inst p eid now vals sched st fin
  , 0
  , (nodeNestAt allNid st ⊔ nestDᵛˢ vals)
  , subst (λ z → FaceOK (capsAt e sl id) z) (sym hsl) (faceOK-capsAt e sl id)
  , ≤-refl
  , pathSz?-widen p (iterSize-infl B 1≤B 0 B) (∧-trueʳ hpz)
  , ≤-trans (≤ᵇ⇒≤ _ _ (T-to (∧-trueˡ hpz))) (iterSize-infl B 1≤B 0 B)
  , ≤-refl
  , innerΦ-quiet-fit sl id sf eid now op allNid inst p vals fin sched st
      hsl hpz hnd hΦ
  where
  B   = Caps.cSize (capsAt e sl id)
  1≤B : 1 ≤ B
  1≤B = ≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)

-- AND THE DRAIN ARM, WHOSE LEDGER IS CARRIED IN RATHER THAN MINTED.
-- The queue's caps receipt is the caps face's own product, delivered
-- along the walk this arm sits on, so the level it is read at is the
-- walk's -- and the record's count is the ROUND's, since that is the
-- count the carried ledger is denominated at.  The two path conjuncts
-- are read at the walk's level by widening, so the arm still never has
-- to know how far the descent climbed.
innerΦ-fit-drain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick) (Lv : ℕ)
  (op : AllOp) (allNid inst : NodeId)
  (p : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ)
  (st : EvalSt e) (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
  lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (capsAt e sl id)) (from-inner op allNid inst ↠ p) ≡ true →
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
                 lim act q od eqn hsl hpz hnd hΦ hdrain hdep =
  capsAt e sl id
  , capsH e sl id
  , Lv
  , (nodeNestAt allNid st ⊔ nestDᵛˢ vals)
  , subst (λ z → capsDrainOK (capsAt e sl id) z (capsH e sl id) Lv
                   sf allNid p eid now lim (pred act) q sched st)
          (sym hsl) hdrain
  , subst (λ z → FaceOK (capsAt e sl id) z) (sym hsl) (faceOK-capsAt e sl id)
  , hdep
  , pathSz?-widen p (iterSize-infl B 1≤B Lv B) (∧-trueʳ hpz)
  , ≤-trans (≤ᵇ⇒≤ _ _ (T-to (∧-trueˡ hpz))) (iterSize-infl B 1≤B Lv B)
  , ≤-refl
  , innerΦ-drain-fit sl id sf eid now op allNid inst p vals fin sched st
      lim act q od eqn hsl hpz hnd hΦ
  where
  B   = Caps.cSize (capsAt e sl id)
  1≤B : 1 ≤ B
  1≤B = ≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)

-- THE QUIET ASSEMBLY, and the two ledgers are discharged rather than
-- carried: a lookup that is not a merge at this type cannot satisfy
-- either premise, so both are functions out of an impossibility.
innerΦ-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick)
  (op : AllOp) (allNid inst : NodeId)
  (p : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ)
  (st : EvalSt e) →
  NotMergeAt {s = s} (lookupNode allNid (EvalSt.nodes st)) →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (capsAt e sl id)) (from-inner op allNid inst ↠ p) ≡ true →
  pathNestD (from-inner op allNid inst ↠ p) ≤ nestCapAt e sl id →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
         (from-inner op allNid inst ↠ p) vals ≡ true →
  FrameΦHyp sf eid now (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
            (from-inner op allNid inst) p vals fin sched st
innerΦ-quiet sl id sf eid now op allNid inst p vals fin sched st ¬m hsl hpz hnd hΦ
  with innerΦ-fit-quiet sl id sf eid now op allNid inst p vals fin sched st
         hsl hpz hnd hΦ
... | c , d , Lv , G , fok , hdr , hsz , hlen , hG , hnum =
  c , d , 0 , Lv , G , fok
  , (λ lim act q od h → ⊥-elim (¬m lim act q od h))
  , (λ lim act q od h → ⊥-elim (¬m lim act q od h))
  , hdr , hsz , hlen , hG , hnum

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
  pathSz? (Caps.cSize (capsAt e sl id)) (from-inner op allNid inst ↠ p) ≡ true →
  pathNestD (from-inner op allNid inst ↠ p) ≤ nestCapAt e sl id →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
         (from-inner op allNid inst ↠ p) vals ≡ true →
  frameDrainOK (capsAt e sl id) sl (capsH e sl id) Lv sf eid now
    (from-inner op allNid inst) p vals sched st →
  depthReact sf op allNid inst p eid now vals sched st fin ≤ capsH e sl id →
  FrameΦHyp sf eid now (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
            (from-inner op allNid inst) p vals fin sched st
innerΦ-drain sl id sf eid now Lv op allNid inst p vals fin sched st lim act q od
             eqn hsl hpz hnd hΦ hfd hdep
  with innerΦ-fit-drain sl id sf eid now Lv op allNid inst p vals fin sched st
         lim act q od eqn hsl hpz hnd hΦ (hfd lim act q od eqn) hdep
... | c , d , Lv , G , hdrain , fok , hdr , hsz , hlen , hG , hnum =
  c , d , drainW sf allNid p eid now q sched st , Lv , G , fok
  , (λ { _ _ _ _ h → transport h hdrain })
  , (λ { _ _ _ _ h →
          transport {P = λ _ _ q′ _ → drainW sf allNid p eid now q′ sched st
                                        ≤ drainW sf allNid p eid now q sched st}
            h ≤-refl })
  , hdr , hsz , hlen , hG , hnum
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
  pathSz? (Caps.cSize (capsAt e sl id)) (from-inner op allNid inst ↠ p) ≡ true →
  pathNestD (from-inner op allNid inst ↠ p) ≤ nestCapAt e sl id →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
         (from-inner op allNid inst ↠ p) vals ≡ true →
  frameDrainOK (capsAt e sl id) sl (capsH e sl id) Lv sf eid now
    (from-inner op allNid inst) p vals sched st →
  depthReact sf op allNid inst p eid now vals sched st fin ≤ capsH e sl id →
  FrameΦHyp sf eid now (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
            (from-inner op allNid inst) p vals fin sched st
innerΦ-fit-go sl id sf eid now Lv op allNid inst p vals fin sched st
              nothing eqn hsl hpz hnd hΦ hfd hdep =
  innerΦ-quiet sl id sf eid now op allNid inst p vals fin sched st
    (notMerge-none eqn) hsl hpz hnd hΦ
innerΦ-fit-go sl id sf eid now Lv op allNid inst p vals fin sched st
              (just (scan-st v)) eqn hsl hpz hnd hΦ hfd hdep =
  innerΦ-quiet sl id sf eid now op allNid inst p vals fin sched st
    (notMerge-scan v eqn) hsl hpz hnd hΦ
innerΦ-fit-go sl id sf eid now Lv op allNid inst p vals fin sched st
              (just (take-st k)) eqn hsl hpz hnd hΦ hfd hdep =
  innerΦ-quiet sl id sf eid now op allNid inst p vals fin sched st
    (notMerge-take k eqn) hsl hpz hnd hΦ
innerΦ-fit-go sl id sf eid now Lv op allNid inst p vals fin sched st
              (just (switch-st cur od)) eqn hsl hpz hnd hΦ hfd hdep =
  innerΦ-quiet sl id sf eid now op allNid inst p vals fin sched st
    (notMerge-switch cur od eqn) hsl hpz hnd hΦ
innerΦ-fit-go sl id sf eid now Lv op allNid inst p vals fin sched st
              (just (exhaust-st ia od)) eqn hsl hpz hnd hΦ hfd hdep =
  innerΦ-quiet sl id sf eid now op allNid inst p vals fin sched st
    (notMerge-exhaust ia od eqn) hsl hpz hnd hΦ
innerΦ-fit-go {s = s} sl id sf eid now Lv op allNid inst p vals fin sched st
              (just (mergeAll-st {w} lim act q od)) eqn hsl hpz hnd hΦ hfd hdep
  with w ≟ᵗ s
... | no ne =
  innerΦ-quiet sl id sf eid now op allNid inst p vals fin sched st
    (notMerge-other lim act q od eqn ne) hsl hpz hnd hΦ
... | yes refl =
  innerΦ-drain sl id sf eid now Lv op allNid inst p vals fin sched st
    lim act q od eqn hsl hpz hnd hΦ hfd hdep

innerΦ-fit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (eid : Id) (now : Tick) (Lv : ℕ)
  (op : AllOp) (allNid inst : NodeId)
  (p : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ)
  (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (capsAt e sl id)) (from-inner op allNid inst ↠ p) ≡ true →
  pathNestD (from-inner op allNid inst ↠ p) ≤ nestCapAt e sl id →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
         (from-inner op allNid inst ↠ p) vals ≡ true →
  frameDrainOK (capsAt e sl id) sl (capsH e sl id) Lv sf eid now
    (from-inner op allNid inst) p vals sched st →
  depthReact sf op allNid inst p eid now vals sched st fin ≤ capsH e sl id →
  FrameΦHyp sf eid now (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
            (from-inner op allNid inst) p vals fin sched st
innerΦ-fit sl id sf eid now Lv op allNid inst p vals fin sched st hsl hpz hnd hΦ hfd hdep =
  innerΦ-fit-go sl id sf eid now Lv op allNid inst p vals fin sched st
    (lookupNode allNid (EvalSt.nodes st)) refl hsl hpz hnd hΦ hfd hdep

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
  pathSz? (Caps.cSize (capsAt e sl id)) (f ↠ p) ≡ true →
  pathNestD (f ↠ p) ≤ nestCapAt e sl id →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id) (f ↠ p) vals ≡ true →
  frameDrainOK (capsAt e sl id) sl (capsH e sl id) Lv sf eid now f p vals sched st →
  depthFrame sf eid now f p vals fin sched st ≤ capsH e sl id →
  FrameΦHyp sf eid now (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
            f p vals fin sched st
frameΦ-fit sl id sf eid now Lv (map-f _)  p vals fin sched st _ _ _ _ _ _ = tt
frameΦ-fit sl id sf eid now Lv (take-f _) p vals fin sched st _ _ _ _ _ _ = tt
frameΦ-fit sl id sf eid now Lv (scan-f fn nid) p vals fin sched st hsl hpz hnd hΦ _ _ =
  scanΦ-fit sl id sf eid now fn nid p vals fin sched st hsl hpz hnd hΦ
frameΦ-fit sl id sf eid now Lv (from-inner op allNid inst) p vals fin sched st
           hsl hpz hnd hΦ hfd hdep =
  innerΦ-fit sl id sf eid now Lv op allNid inst p vals fin sched st
    hsl hpz hnd hΦ hfd hdep
frameΦ-fit sl id sf eid now Lv (thru-outer op nid) p vals fin sched st hsl hpz hnd hΦ _ _ =
  walk-thru-fit sl id sf eid now op nid p vals fin sched st hsl hpz hnd hΦ

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

-- AND READ ON ITS OWN THE DEFICIT SPLITS BY THE ADMITTED CHAIN'S
-- TERMINAL, which is what pricing the leaf bought.  A sink now carries
-- a factor and a depth of its own rather than one and zero, and a path
-- holds exactly one leaf -- so a chain ending at `root` spends its
-- whole factor on frames, legality caps that count by the size cap,
-- and the leaf is priced at exactly that exponent.  Its depth is
-- capped in the same currency by the same premise.  That half closes
-- off `pathΦF-cap-root`, `pathΦD-cap-root` and monotonicity, with no
-- new fact -- and this is the assembly that spends the three.
sink-fan-root : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (i : Fin n) (p : Path Γ (lookup Γ i) t)
  (vals : List (Val Γ (lookup Γ i))) →
  pathRoots p ≡ true →
  pathSz? (Caps.cSize (capsAt e sl id)) p ≡ true →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
    (share-sink {t = t} i) vals ≡ true →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id) p vals ≡ true
sink-fan-root {e = e} sl id i p vals hr hz hΦ =
  valsΦ?-mono B (nestΦAt e sl id) p (share-sink i) vals
    (pathΦF-cap-root B p hr hz) (pathΦD-cap-root B p 1≤B hr hz) hΦ
  where
  B : ℕ
  B = Caps.cSize (capsAt e sl id)
  1≤B : 1 ≤ B
  1≤B = ≤-trans (s≤s z≤n) (8≤capsAt-size e sl id)

-- WHAT IS LEFT IS THE CHAIN THAT ENDS AT A SECOND HAND-OVER.  Its
-- factor is the leaf's own multiplied by its frames', so the leaf
-- would have to dominate itself times a frame product -- which no
-- function of the cap does at an ARBITRARY chain, and arbitrary is
-- what this statement gets: `pathRoots p ≡ false` is the whole of
-- what it knows about the path it is handed.  An ordinary program
-- does put a hand-over there, since a registration minted while a
-- share's definition is being subscribed carries that share's sink as
-- its continuation.  So the residue is the sink-terminated arm and
-- nothing else.

-- AND THE ESCALATION IS BOUNDED BY THE PROGRAM, WHICH IS WHAT THIS
-- HEADER USED TO DENY.  The reading it carried -- that the hop count
-- is capped by nothing but the dispatch gas, since admission filters
-- on the source and the element type and never on whether a chain has
-- been delivered to -- is a fact about ADMISSION, and admission is not
-- what bounds it.  The slot telescope is STRATIFIED: a shared slot's
-- def may name only inputs below its own index, so a registration
-- whose continuation ends at some slot's sink was minted subscribing
-- an input that slot's def contains, and its source is strictly below
-- that slot.  Sink hops therefore climb the telescope, no chain can be
-- re-entered through its own sink, and the count is capped by the slot
-- count.  Instantiated in `Harness.Main` over a run of two shared
-- slots stacked on a hot source: every registration carrying a sink
-- terminal has its source strictly under that sink, none re-enters its
-- own, and the hop depth saturates at the telescope's own bound while
-- the walking fuel is taken to four times the slot count.  Those rows
-- are measured-not-rechecked, as everything in that module is.

-- SO THE RESIDUE IS THE ARBITRARY CHAIN, NOT A MISSING NUMBER, and
-- that relocates the row rather than shrinking it.  A price
-- denominated in the slot count is available the moment the chain is
-- read out of the REGISTRY -- and the registry is what the walk holds
-- at an arbitrary state, which is the wall `fan-regsSz` stands at one
-- statement over.  Stratification is therefore owed as a CARRIED
-- conjunct of the invariant, where every producer re-establishes it,
-- and not as a hypothesis here, where only today's caller supplies it.
-- REFUTED: `Refuted.Sink-Phi-Leaf`, at the size floor this arm
--   discharges from and at the budget the sink's own receipt exactly
--   exhausts, so the crossing is not an artifact of a small budget.
-- DEAD ROUTE: asserting the stratification receipt AT THE READ, as its
--   own postulate over the same arbitrary state `fan-regsSz` stands
--   at, is structurally dead rather than merely unproven --
--   `Refuted.Fan-Chain-Registry` kills that shape at a single
--   `register` onto the initial state, and the stratification reading
--   falls to the same witness family with a zero source handed a zero
--   sink.  So the fact is owed at the MINT, and the mint is FOUR
--   obligations rather than the one the carried conjunct reads as: a
--   slot-sourced registration wants the telescope carried down the
--   subscribe descent, since the continuation's terminal and the
--   expression's inputs meet only at the enclosing share's own
--   `inputsBelowᵉ` field; a minted-sourced one wants a FLOOR on the
--   sched's next source, which starts at the slot count and only
--   climbs and which nothing carries today, and gets the receipt for
--   free once it has one; and an inner subscribe of a DELIVERED
--   observable reaches the input arm under syntax the telescope never
--   saw, so it registers a slot source against a continuation nothing
--   local relates it to -- a conjunct on the values in flight, which
--   is a different invariant from this one.
postulate
  sink-fan-sink : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (i : Fin n) (p : Path Γ (lookup Γ i) t)
    (vals : List (Val Γ (lookup Γ i))) →
    pathRoots p ≡ false →
    pathSz? (Caps.cSize (capsAt e sl id)) p ≡ true →
    valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
      (share-sink {t = t} i) vals ≡ true →
    valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id) p vals ≡ true

-- AND WRITING THE BODY FOUND TWO MORE, BOTH ABOUT WHAT THE REGISTRY
-- MAY HOLD RATHER THAN ABOUT THE POTENTIAL.  A chain the fan-out
-- re-enters is walked FROM THE TOP, so it needs its size receipt at
-- the program's own cap -- and the walk carries no registry reading of
-- its own to narrow down to it, the level ledger having turned out to
-- pay for the fan-out on its own.  Only the registration side supplies
-- this one.

-- AND WHAT A SIZE RECEIPT HAS TO PRICE IS THE REGISTERED LENGTH, which
-- does not sit at a constant.  The reachable maximum is two frames per
-- flatten layer standing above a share -- so it climbs with the
-- program's own syntax, and a receipt
-- stated at any numeral is outrun by the fourth layer.  That is why the
-- mint-side fact cannot be a bound chosen here: it has to read the
-- program, which is what the cap does, and which is equally why this
-- row admits no instantiation of its own -- the cap returns at no
-- program, so only the conjunct underneath it is reachable.

-- AND THE FIELD IT WANTS ALREADY EXISTS -- WHAT IS MISSING IS A
-- DIRECTION, NOT AN INVARIANT.  Asking whether the registry belongs to
-- the invariant record as a CARRIED field rather than a measured one
-- answers itself: `capsOK?` carries the registry's size receipt as a
-- conjunct already, the sink's own predicate carries the same receipt
-- over the ADMITTED sublist, and the walk's sink clause holds a third
-- at the stepped cap.  So there is no producer that fails to
-- re-establish it, because there is nothing to add.
--
-- EVERY ONE OF THE THREE IS READ AT A CAP ABOVE THE ONE THE FANNED
-- WALK DEMANDS, AND THE RECEIPT WEAKENS UPWARD.  The sink's conjunct
-- is denominated in the round's EXIT cap and the walk's clause in the
-- STEPPED one, while the chains a sink fans into are walked at the
-- round's ENTRY cap -- and entry is under both, provably.  A receipt
-- at a larger cap does not deliver one at a smaller, so all three are
-- in hand and none can be spent.  That is why this row survived the
-- field question: the residue is that the fanned chain's walk is
-- denominated in the entry cap at all, which is a restatement of the
-- walk rather than a fact about the registry.

-- AND NEITHER IS THE ADMISSION FILTER'S TO CARRY, which is what the
-- pair being stated over the fan-out was hiding.  `shareAdmit`
-- selects on the source and the element type and never reads a path,
-- so it can only pass a receipt along, never establish one -- and
-- both passings are already proven, a size one and a generic one over
-- an arbitrary path predicate.  So the residue is the REGISTRY read
-- at the program's own cap, and it is owed at whatever mints a
-- registration.
--
-- REFUTED: `Refuted.Fan-Chain-Registry`, which is what licenses the
--   two premises below being premises rather than facts.  Stated over
--   an arbitrary state each fails at a single `register` onto the
--   initial one: a `take` chain one longer than the bound, at EVERY
--   bound rather than at a chosen one, and a mapped ladder of `*All`
--   layers against a unit of one.
-- DEAD ROUTE: restating the fanned walk at whichever of the three caps
--   is in hand, so that the receipt is spent rather than re-derived.
--   The entry cap is load-bearing for exactly one thing and it is not
--   a bookkeeping one: the Φ PRICING reads `pathΦF` and `pathΦD` at
--   the cap the walk's own budget is denominated at, so a receipt
--   taken higher moves the leaf's exponent and the budget under it --
--   which is the share ring's fold budget, the quantity the sink
--   predicate's own dead route records as unmovable, arriving here
--   from the registry's side rather than the caps face's.  Nothing
--   else in the walk reads the cap, the size and registry receipts it
--   used to thread having reached no obligation at all.
-- DEAD ROUTE: a FLAT carried field -- one predicate at one cap, added
--   to the walk's bundle -- answering this row together with
--   `walk-share-nestOK`, `sink-fan-sink` and the two inner Φ arms,
--   which is what those four sharing an obstacle invites.  Each
--   currency kills it separately and for the same reason: the descent
--   reads a state the instant has STEPPED, every receipt in hand is
--   denominated at or above the cap it stepped to, and each of these
--   predicates WEAKENS as its cap grows -- so a field fixed at one cap
--   is either unavailable at the read or useless at the consumer, and
--   no producer cascade repairs a direction.  What the elimination
--   leaves standing is the INDEXED form, a per-entry cap under an
--   absolute ceiling rather than one cap for the whole fold; and that
--   is not a new mechanism, `stepFrame-nodes` already proving a
--   per-frame advance under exactly such a ceiling.  The residue is
--   whether the Φ pricing affords a leaf exponent read at a stepped
--   cap, which the route directly above prices at a FLAT raise and
--   therefore does not answer for an indexed one.
-- DEAD ROUTE: that INDEXED form itself, and it dies on the same
--   arithmetic as the flat raise -- by ONE step of the recurrence
--   rather than at some threshold, so no ceiling is small enough.
--   What a size receipt actually buys the Φ pricing is a LENGTH, via
--   `pathSz?-len`, and the length lands in an EXPONENT: a sink's own
--   factor is two to the cap times a square of it, and a fanned chain
--   is affordable exactly while its length is under the cap the
--   CONCLUSION is stated at.  A receipt at any larger cap bounds the
--   length by that cap instead and multiplies the exponent by the
--   ratio, which one step already makes a square.  Nor does weakening
--   only the PREMISE escape it, which is how the caps face repaired
--   its own version: there the conclusions already named the larger
--   cap, and here they cannot, so the premise's cap reaches the
--   conclusion through the factor lemmas either way.
-- DEAD ROUTE: moving the Φ face's DENOMINATION rather than any
--   receipt, which is the one shape the routes above leave standing --
--   the receipt in hand names the stepped cap and the conclusion names
--   the entry one, so the remaining question is which instant's
--   numbers the whole pricing is stated at.  Both answers die on the
--   pricing rather than on the registry, and `pathΦF`'s sink clause
--   carries the arithmetic: the face cannot follow the cap to the
--   stepped instant, because every frame arm spends a tie between the
--   potential and the depth budget of the instant being WALKED and the
--   descent carries no reading of the next; and the leaf alone cannot
--   follow it either, because the stepped cap is a blowup OF that same
--   depth budget.  What that leaves is not a further denomination but
--   the obligation `pathSz?`'s header already states over its two
--   callers: a chain the fan-out hands values to has to be priced by
--   something that is not a cap.
postulate
  fan-regsSz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (st : EvalSt e) →
    regsSz? (Caps.cSize (capsAt e sl id)) (EvalSt.registry st) ≡ true

fan-chain-sz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (i : Fin n) (st : EvalSt e) →
  regsSz? (Caps.cSize (capsAt e sl id)) (EvalSt.registry st) ≡ true →
  all (λ rp → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rp))
      (shareAdmit {t = t} i (EvalSt.registry st)) ≡ true
fan-chain-sz {e = e} sl id i st h =
  shareAdmit-caps (Caps.cSize (capsAt e sl id)) i (EvalSt.registry st) h

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
    pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
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
    all (λ rp → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rp)) ps ≡ true →
    all (λ rp → pathNestD (proj₂ rp) ≤ᵇ nestCapAt e sl id) ps ≡ true →
    valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
      (share-sink {t = t} i) vals ≡ true →
    ShareGoΦHyp sf gas nid now (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
      i vals fin ps sched st

  walk-share-ΦHyp sl id sf zero nid now Lv i vals fin sched st _ _ _ _ = tt
  walk-share-ΦHyp {e = e} sl id sf (suc gas) nid now Lv i vals false sched st
                  hd hdd hsl hΦ =
    walk-shareGo-ΦHyp sl id sf gas nid now Lv i vals false
      (shareAdmit i (EvalSt.registry st)) sched st
      (proj₂ (proj₂ hd)) hdd
      hsl (fan-chain-sz sl id i st (fan-regsSz sl id st))
          (fan-chain-nestD (nestCapAt e sl id) i st
             (fan-regsNest sl id sched st
                (walk-share-nestOK sl id sf gas nid now Lv i vals false
                   sched st hd hsl))) hΦ
  walk-share-ΦHyp {e = e} sl id sf (suc gas) nid now Lv i vals true sched st
                  hd hdd hsl hΦ =
    walk-shareGo-ΦHyp sl id sf gas nid now Lv i vals true
      (shareAdmit i (EvalSt.registry st)) sched (shareLatch i true st)
      (proj₂ (proj₂ hd)) hdd
      hsl (fan-chain-sz sl id i st (fan-regsSz sl id st))
          (fan-chain-nestD (nestCapAt e sl id) i st
             (fan-regsNest sl id sched st
                (walk-share-nestOK sl id sf gas nid now Lv i vals true
                   sched st hd hsl))) hΦ

  walk-shareGo-ΦHyp sl id sf gas nid now Lv i vals fin [] sched st
                    _ _ _ _ _ _ = tt
  walk-shareGo-ΦHyp {e = e} sl id sf gas nid now Lv i vals fin
                    ((rid , p) ∷ ps) sched st hsg hdsg hsl hpz hnd hΦ
    with any (_≡ᵇ rid) (EvalSt.cancelled st)
  ... | true  = walk-shareGo-ΦHyp sl id sf gas nid now Lv i vals fin ps sched st
                  hsg (depthShareGo-tail sf gas nid now i vals fin rid p ps sched st hdsg)
                  hsl (∧-trueʳ hpz) (∧-trueʳ hnd) hΦ
  ... | false =
      hΦp
    , walk-ΦHyp-go sl id sf gas nid now Lv (toℕ i) evs p vals fin sched st₀
        (proj₁ hsg)
        (depthShareGo-head sf gas nid now i vals fin rid p ps sched st hdsg)
        hsl hp₀ hndp hΦp
    , walk-shareGo-ΦHyp sl id sf gas nid now (Lv + proj₁ (proj₂ hsg))
        i vals fin ps
        (proj₁ (proj₂ FP)) (proj₂ (proj₂ FP))
        (proj₂ (proj₂ (proj₂ hsg)))
        (depthShareGo-step sf gas nid now i vals fin rid p ps sched st hdsg)
        (trans (foldPath-slots sf gas nid now (toℕ i) p vals evs fin sched st₀) hsl)
        (∧-trueʳ hpz) (∧-trueʳ hnd)
        hΦ
    where
    B : ℕ
    B = Caps.cSize (capsAt e sl id)
    hp₀ : pathSz? B p ≡ true
    hp₀ = ∧-trueˡ hpz
    hndp : pathNestD p ≤ nestCapAt e sl id
    hndp = ≤ᵇ⇒≤ (pathNestD p) (nestCapAt e sl id) (T-to (∧-trueˡ hnd))
    st₀ : EvalSt e
    st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
    evs = if fin then close (toℕ i) exhausted ∷ [] else []
    FP = foldPath sf gas nid now (toℕ i) p vals evs fin sched st₀
    hΦp : valsΦ? B (nestΦAt e sl id) p vals ≡ true
    hΦp with pathRoots p in eqr
    ... | true  = sink-fan-root sl id i p vals eqr hp₀ hΦ
    ... | false = sink-fan-sink sl id i p vals eqr hp₀ hΦ

  walk-ΦHyp-go sl id sf gas nid now Lv envSrc evs root vals fin sched st
               _ _ _ _ _ _ = tt
  walk-ΦHyp-go sl id sf gas nid now Lv envSrc evs (share-sink i) vals fin sched st
               hcw hdf hsl _ _ hΦ =
    walk-share-ΦHyp sl id sf gas nid now Lv i vals fin sched st
      (proj₂ hcw) hdf hsl hΦ
  walk-ΦHyp-go {e = e} sl id sf gas nid now Lv envSrc evs (f ↠ p) vals fin sched st
               hcw hdf hsl hpz hnd hΦ =
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
        (≤-trans (pathNestD-step f p) hnd)
        (stepFrame-nest-Φ sf nid now f p vals fin sched st
          (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id) hΦ hF)
    where
    step = stepFrame sf nid now f p vals fin sched st
    hL   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hcw)))))
    hF = frameΦ-fit sl id sf nid now Lv f p vals fin sched st hsl hpz hnd hΦ
           (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hcw))))))
           (≤-trans (m≤m⊔n (depthFrame sf nid now f p vals fin sched st) _) hdf)
    B  = Caps.cSize (capsAt e sl id)
    hpz′ : pathSz? B p ≡ true
    hpz′ = proj₂ (∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p)
                   (proj₂ (∧-true (frameSz? B f)
                            ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) hpz)))

-- THE ARRIVAL'S OWN POTENTIAL, which is the entry reading BOTH the
-- walk's side-condition and the fold's own premise are spent at: one
-- value on the path, so the depth premise the arm was stated with is
-- the whole of it once the path's factor is applied.
entryΦ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (path : Path Γ (arrTy a) t) →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id) path
         (arrVal a ∷ []) ≡ true
entryΦ {e = e} sl id a path hp hΦ = ∧-intro (T⇒≡true _ (≤⇒≤ᵇ Φfit)) refl
  where
  Sz = Caps.cSize (capsAt e sl id)
  1≤Sz : 1 ≤ Sz
  1≤Sz = ≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)
  dΦ : nestDᵛ (arrTy a) (arrVal a) + pathΦD Sz path
         ≤ nestUnit e sl + (Sz * Sz + Sz * Sz) + Sz
  dΦ =
    ≤-trans (+-monoʳ-≤ (nestDᵛ (arrTy a) (arrVal a)) (pathΦD≤nestD Sz path))
    (≤-trans (≤-reflexive (sym (+-assoc (nestDᵛ (arrTy a) (arrVal a))
                                        (pathNestD path) (Sz * Sz))))
    (≤-trans (+-monoˡ-≤ (Sz * Sz) hΦ)
    (≤-trans (+-monoʳ-≤ (nestUnit e sl) (m≤m+n (Sz * Sz) (Sz * Sz)))
             (m≤m+n (nestUnit e sl + (Sz * Sz + Sz * Sz)) Sz))))
  Φfit : pathΦF Sz path * (nestDᵛ (arrTy a) (arrVal a) + pathΦD Sz path)
           ≤ nestΦAt e sl id
  Φfit = ≤-trans
    (subst (pathΦF Sz path * (nestDᵛ (arrTy a) (arrVal a) + pathΦD Sz path) ≤_)
           (sym (nestWalkAt-def e sl id))
           (*-mono-≤ (≤-trans (pathΦF-cap Sz path hp)
                              (^-monoʳ-≤ 2
                                (≤-trans (walkExp-widen Sz 1≤Sz) (n≤1+n _))))
                     (≤-trans dΦ
                              (m≤m+n (nestUnit e sl + (Sz * Sz + Sz * Sz) + Sz)
                                     (Sz * slotWrapSum sl)))))
    (nestWalkAt≤nestΦAt e sl id)

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
    (Arrival.isLast a) sched st hcc hdc hsl hp
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

-- THE LIVE WALK AND THE FAN-OUT IT RE-ENTERS, AS ONE MUTUAL BODY, and
-- it stands here rather than beside its own statements because this is
-- where the registry's reading is a FACT.  The monolithic form it
-- replaces was owed a premise relating the registry's price to the
-- values its chains produce; `fan-regsSz` is that reading, taken at
-- the program's cap over an ARBITRARY state, so the fold re-derives
-- chain legality at every state `foldPath` leaves instead of carrying
-- a receipt that degrades as it goes.
--
-- AND THE RELATION IS THE LENGTH CONJUNCT, WHICH WAS ALREADY PROVEN.
-- Legality prices a chain's syntax, the conclusion prices the values
-- that syntax emits, and `pathSz?-len` is the bridge: a chain the
-- registry admits at the cap climbs at most a cap's worth of levels,
-- so a fanned-into chain entered at level `j` finishes under `j + S`.
-- That is what the level ledger below buys with its `S` per hop, and
-- the dispatch gas is what bounds the hops.
--
-- REFUTED: `Refuted.Share-Live-Afford`, `Refuted.Share-Live-Level`
-- REFUTED: `Refuted.Sink-Level-Range`

-- WHAT ONE FRAME OF A LEGAL CHAIN CHARGES THE SIZE LADDER, at this
-- instant's caps.  A frame applies its function once per arriving
-- value and every application costs a rung, so the charge is a burst
-- width's worth of a cap and not one -- which is the whole content of
-- the two refutations `Verify-Budget-Sufficient.Regs-Nest-Walk`
-- carries.
--
-- AND THE WIDTH IT IS READ AT IS THE SIZE CAP, WHICH IS THE ONLY
-- CURRENCY THIS CHARGE CAN BE PAID IN.  The charge lands in an
-- EXPONENT -- a count of rungs, and a rung multiplies -- so whatever
-- number stands here is spent against `2^S` and nothing larger.  The
-- cap-side WIDTH coordinate is not a candidate at any threshold: it
-- steps by `foldStep S w = S ^ suc w` where the size steps by
-- `sizeStep S s = S * suc (2 * s)`, so a width read at the same count
-- is a tower where the size is geometric, and the two cross a few
-- folds in and never come back.  The size cap is the ceiling this
-- development already prices real burst widths against -- `nestBurstAt`
-- is a size coordinate, not a width one -- so reading the walk's
-- bursts there is the existing denomination rather than a new one.
-- DEAD ROUTE: denominating the charge in `Caps.cWid` -- one above it,
--   to dodge the width's missing positivity floor.  It buys the floor
--   and loses the exponent: the ledger's rungs times a width put a
--   power tower inside `2^S`, and no threshold on the size repairs
--   that, since the gap grows with the fold count rather than shrinking.
--   Recorded already at `walk-sight≤exp` and at `scanΦ-fit`.
chAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) → ℕ
chAt e sl id =
  frameCh (Caps.cSize (capsAt e sl id)) (Caps.cSize (capsAt e sl id))

-- THE WALK IS UNIFORM IN THE FRAME KIND, AND THE CEILING IS WHAT
-- BOUGHT THAT.  Every clause below reads the head at the concluding
-- level and recurses at the level the frame climbed to, so the only
-- thing a frame contributes is that its climb stays under the ceiling
-- -- which the walk predicate now ASSERTS at each frame rather than
-- leaving to a consumer's arithmetic.  Three of the five frame kinds
-- charge a count a per-frame product dominates and the two crossings
-- charge what the program they subscribe would cost to RUN, but that
-- distinction is no longer visible here: it is a fact about whether
-- the ceiling conjunct can be SUPPLIED, and it is owed where the walk
-- is produced.
mutual
  walk-LiveHyp-goC : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
    (Lv k : ℕ) (path : Path Γ u t) (vals : List (Val Γ u)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    valsSz? (iterSize (Caps.cSize (capsAt e sl id)) k
              (Caps.cSize (capsAt e sl id))) vals ≡ true →
    all (λ kv → boundedNode (iterSize (Caps.cSize (capsAt e sl id)) k
                              (Caps.cSize (capsAt e sl id))) (proj₂ kv))
        (EvalSt.nodes st) ≡ true →
    walkSzOK (Caps.cSize (capsAt e sl id))
             (Caps.cSize (capsAt e sl id)) Lv k sf gas nid now
             path vals fin sched st →
    pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
    k ≤ Lv →
    PathLiveHyp sf gas nid now
      (iterSize (Caps.cSize (capsAt e sl id)) Lv (Caps.cSize (capsAt e sl id)))
      path vals fin sched st

  -- ONE LEVEL OF THE DISPATCH TELESCOPE.  The spent arm owes nothing;
  -- the latched one is the fan-out fold over the admitted snapshot,
  -- and the snapshot is read off the state BEFORE the latch, which is
  -- the state `fan-regsSz` is spent at.
  walk-share-LiveHypC : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
    (Lv k : ℕ) (i : Fin n) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    valsSz? (iterSize (Caps.cSize (capsAt e sl id)) k
              (Caps.cSize (capsAt e sl id))) vals ≡ true →
    dispatchSzOK (Caps.cSize (capsAt e sl id))
                 (Caps.cSize (capsAt e sl id)) Lv k sf gas nid now
                 i vals fin sched st →
    k ≤ Lv →
    DispatchLiveHyp sf gas nid now
      (iterSize (Caps.cSize (capsAt e sl id)) Lv (Caps.cSize (capsAt e sl id)))
      i vals fin sched st

  -- THE FAN-OUT FOLD, ENTRY BY ENTRY AND AT THE STATE EACH LEAVES.  A
  -- cancelled entry owes nothing and moves neither state nor level; a
  -- delivered one is walked at the level the fold has reached, and the
  -- fold then advances by what that entry's own run left behind.  The
  -- values are re-read at the advanced level rather than re-derived,
  -- since the fan hands every chain the same arrivals and the ladder
  -- only grows.
  walk-shareGo-LiveHypC : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
    (Lv k : ℕ) (i : Fin n) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) →
    valsSz? (iterSize (Caps.cSize (capsAt e sl id)) k
              (Caps.cSize (capsAt e sl id))) vals ≡ true →
    shareGoSzOK (Caps.cSize (capsAt e sl id))
                (Caps.cSize (capsAt e sl id)) Lv k sf gas nid now
                i vals fin ps sched st →
    all (λ rp → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rp)) ps ≡ true →
    k ≤ Lv →
    ShareGoLiveHyp sf gas nid now
      (iterSize (Caps.cSize (capsAt e sl id)) Lv (Caps.cSize (capsAt e sl id)))
      i vals fin ps sched st

  walk-share-LiveHypC sl id sf zero nid now Lv k i vals fin sched st _ _ _ = tt
  walk-share-LiveHypC sl id sf (suc gas) nid now Lv k i vals fin sched st
                      hsz hw hk =
    walk-shareGo-LiveHypC sl id sf gas nid now Lv k i vals fin
      (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st)
      hsz hw (fan-chain-sz sl id i st (fan-regsSz sl id st)) hk

  walk-shareGo-LiveHypC sl id sf gas nid now Lv k i vals fin [] sched st
                        _ _ _ _ = tt
  walk-shareGo-LiveHypC {e = e} sl id sf gas nid now Lv k i vals fin
                        ((rid , p) ∷ ps) sched st hsz hsg hpz hk
    with any (_≡ᵇ rid) (EvalSt.cancelled st) | hsg
  ... | true  | h = walk-shareGo-LiveHypC sl id sf gas nid now Lv k i vals fin ps
                      sched st hsz h (∧-trueʳ hpz) hk
  ... | false | (hns , hwk , k′ , hk′ , htl) =
      walk-LiveHyp-goC sl id sf gas nid now Lv k p vals fin sched st₀
        hsz hns hwk hp₀ hk
    , walk-shareGo-LiveHypC sl id sf gas nid now Lv (k + k′) i vals fin ps
        (proj₁ (proj₂ FP)) (proj₂ (proj₂ FP))
        hszTail htl (∧-trueʳ hpz) hk′
    where
    S : ℕ
    S = Caps.cSize (capsAt e sl id)
    1≤S : 1 ≤ S
    1≤S = ≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)
    hp₀ : pathSz? S p ≡ true
    hp₀ = ∧-trueˡ hpz
    st₀ : EvalSt e
    st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
    evs = if fin then close (toℕ i) exhausted ∷ [] else []
    FP  = foldPath sf gas nid now (toℕ i) p vals evs fin sched st₀
    hszTail : valsSz? (iterSize S (k + k′) S) vals ≡ true
    hszTail = valsSz?-mono (iterSize S k S) (iterSize S (k + k′) S) vals
                (iterSize-mono-count S S 1≤S (m≤m+n k k′)) hsz

  walk-LiveHyp-goC sl id sf gas nid now Lv k root vals fin sched st
                   _ _ _ _ _ = tt
  walk-LiveHyp-goC sl id sf gas nid now Lv k (share-sink i) vals fin
                   sched st hsz _ hw _ hk =
    walk-share-LiveHypC sl id sf gas nid now Lv k i vals fin sched st hsz hw hk
  walk-LiveHyp-goC {e = e} sl id sf gas nid now Lv k (f ↠ p) vals fin sched st
                   hsz hns hw hpz hk =
      hHead
    , walk-LiveHyp-goC sl id sf gas nid now Lv (k + szCount sls A f vals) p
        (proj₁ step)
        (proj₁ (proj₂ (proj₂ step)))
        (proj₁ (proj₂ (proj₂ (proj₂ step))))
        (proj₂ (proj₂ (proj₂ (proj₂ step))))
        hszTail hnsTail (proj₂ (proj₂ hw)) hpTail (proj₁ (proj₂ hw))
    where
    S : ℕ
    S = Caps.cSize (capsAt e sl id)
    sls = Sched.slots sched
    step = stepFrame sf nid now f p vals fin sched st
    2≤S : 2 ≤ S
    2≤S = 2≤capsAt-size e sl id
    1≤S : 1 ≤ S
    1≤S = ≤-trans (s≤s z≤n) 2≤S
    A : ℕ
    A = iterSize S k S
    atV : valsSz? (iterSize S Lv S) vals ≡ true
    atV = valsSz?-mono (iterSize S k S) (iterSize S Lv S) vals
            (iterSize-mono-count S S 1≤S hk) hsz
    hHead : FrameLiveHyp (iterSize S Lv S) f p vals
    hHead = frameLive-of-sz (iterSize S Lv S) f p vals atV
    hpTail : pathSz? S p ≡ true
    hpTail = proj₂ (∧-true (suc (pathLen p) ≤ᵇ S) (pathSz? S p)
                      (proj₂ (∧-true (frameSz? S f)
                               ((suc (pathLen p) ≤ᵇ S) ∧ pathSz? S p) hpz)))
    eqSplit : iterSize S (k + szCount sls A f vals) S
                ≡ iterSize S (szCount sls A f vals) A
    eqSplit = iterSize-+ S k (szCount sls A f vals) S
    hszTail : valsSz? (iterSize S (k + szCount sls A f vals) S) (proj₁ step) ≡ true
    hszTail = subst (λ z → valsSz? z (proj₁ step) ≡ true) (sym eqSplit)
                (stepFrame-sz sf nid now f p vals fin sched st S A 2≤S hns hsz)
    hnsTail : all (λ kv → boundedNode (iterSize S (k + szCount sls A f vals) S)
                            (proj₂ kv))
                  (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂ step))))) ≡ true
    hnsTail = subst (λ z → all (λ kv → boundedNode z (proj₂ kv))
                            (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂ step)))))
                              ≡ true)
                (sym eqSplit)
                (stepFrame-sz-store sf nid now f p vals fin sched st S A 2≤S
                   hns hsz)

-- THE SIZE-SIDE SIDE CONDITION, DISCHARGED, AND IN THE LADDER'S OWN
-- CURRENCY.  The walk reads the bound at the level it has reached and
-- each frame moves the level by one, so what the caller owes is the
-- entry reading -- which is the size premise it already carries -- and
-- the budget the walk concludes at is the top of the ladder it climbs
-- rather than the round's ceiling.
--
-- AND THAT IS WHY NO AFFORDABILITY IS ASKED FOR HERE.  With the walk's
-- budget being the ladder's own top, every frame's reading is
-- monotonicity of the ladder and nothing else, so the ceiling is met
-- ONCE, at the consumer below, on one number -- instead of at every
-- frame of every chain.  A cascade still enters its k-th chain at
-- whatever the first k-1 left, and that range is still a property of
-- the SELECTION; what changed is that it is now the consumer's
-- question and not a premise the walk carries through its own arms.
--
-- AND THE LEDGER NOW PAYS FOR THE FAN-OUT TOO, which is what the
-- registry reading stopped being a premise in exchange for.  A chain
-- reaching a sink leaves for the registry's own chains, each of which
-- climbs by at most a cap; the dispatch gas bounds how many such hops
-- follow, so the level the walk can reach is its own frames plus a cap
-- per hop -- and that is one term rather than a receipt threaded
-- through the arms.
-- THE WALK'S OWN HEAD READING, PROJECTED.  Every clause of the caps
-- walk opens with the levelled `capsOK?`, so a consumer that wants it
-- at the head of an arbitrary path takes it here rather than casing on
-- the path itself.
capsWalkOK-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c ac : Caps) (sl : Slots Γ) (d Lv : ℕ) (sf : Gas) (gas : ℕ)
  (id : Id) (now : Tick) (p : Path Γ u t) (vals : List (Val Γ u))
  (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  capsWalkOK c ac sl d Lv sf gas id now p vals fin sched st →
  capsOK? (frameStep Lv c) sched st ≡ true
capsWalkOK-caps c ac sl d Lv sf gas id now root           vals fin sched st h = h
capsWalkOK-caps c ac sl d Lv sf gas id now (share-sink _) vals fin sched st h = proj₁ h
capsWalkOK-caps c ac sl d Lv sf gas id now (_ ↠ _)        vals fin sched st h = proj₁ h

-- THE ENTRY READING IS NOT OWED AT ALL, AND WHAT BOUGHT THAT IS THE
-- INDEX.  `Caps.cSize (frameStep Lv c)` IS `iterSize (Caps.cSize c) Lv
-- (Caps.cSize c)` -- the size walk's own ladder, read at the level the
-- caps walk has reached rather than at the bottom of it.  So what the
-- door needs is the head projection above and `capsOK?-nodeSz`, once
-- it stops asking for the reading FLAT.  It asked flat only because
-- the consumer instantiated the walk's level at zero, and nothing
-- about a chain required that; what the level costs instead is that
-- `Lc` be paid for out of the ledger the cascade already carries.
chain-entry-nodesSz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lc : ℕ) (a : Arrival Γ) (nextId : Id)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  chainCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lc
    nextId a path sched st →
  all (λ kv → boundedNode (iterSize (Caps.cSize (capsAt e sl id)) Lc
                            (Caps.cSize (capsAt e sl id))) (proj₂ kv))
      (EvalSt.nodes st) ≡ true
chain-entry-nodesSz {e = e} sl id Lc a nextId path sched st hcc =
  capsOK?-nodeSz (frameStep Lc (capsAt e sl id)) sched st
    (capsWalkOK-caps (capsAt e sl id) (capsAt e sl (suc id)) sl
       (capsH e sl id) Lc _ _ nextId (arrTick a) path
       (arrVal a ∷ []) (Arrival.isLast a) sched st hcc)

-- THE WHOLE SIZE WALK ALONG ONE CHAIN, CEILING INCLUDED, and the
-- ceiling is what this row now owes over and above the readings.  The
-- walk asserts at every frame that its climb stays under `C` and at
-- every fan-out entry that the advance that entry's run left behind
-- does too; the premise is the cascade's own per-chain ledger, which
-- is what the consumer can actually supply.  So the arithmetic that
-- used to sit in a consumer's hypothesis is stated here instead --
-- tracked, at full strength, and against the two obligations below
-- rather than spread across the walk's arms.
--
-- THE FAN-OUT ADVANCE IS ONE OF THE TWO, and it is where a LEDGER
-- cannot be what is owed.  A sink hands its admitted chains a table
-- the chains ahead of them in the same fan have written -- a chain
-- reaching a drain door subscribes what the `*All` node parked, and
-- the subscription installs a node of its own, so one parked
-- duplication chain puts the table over the level the fan was entered
-- at.  The advance is therefore real and per entry.  What it may not
-- be is SUMMED: an entry's own walk reaches a sink of its own, so a
-- ledger charging a cap per entry recurs through the dispatch gas and
-- is exponential in it, while a ceiling is not a sum and has no such
-- recurrence.  Which is why the walk takes one.

-- THE CROSSING FRAME IS THE OTHER, AND IT IS DEAD ON AFFORDABILITY.
-- Put the numbers beside each other.  What the walk may SPEND is a
-- rung count polynomial in the cap: `walkFac-ch` affords `L * chAt`
-- rungs for `L` under a quadratic, and it affords that because
-- `nestWalkAt` is two to a polynomial in the cap, singly exponential
-- and no more.  What a crossing frame NEEDS is a rung count linear in
-- the size of the observable it subscribes, because bounding a
-- subscribed program's output means climbing once per operator it can
-- chain.  And the only bound the walk carries on that observable is
-- its own level reading, which is ladder-shaped in the level.  So the
-- need is two to a ladder where the ceiling is two to a polynomial,
-- and the gap opens with the level rather than closing.  A ceiling
-- and a ledger are both ways of SPENDING a budget already too small
-- by an exponential.
--
-- AND THE EVALUATOR ALREADY SAYS NO CLOSED FORM CAN CLOSE IT, which is
-- why the two spendings fail together rather than one being the
-- repair for the other.  A crossing emits inside the instant it runs
-- in -- it subscribes one inner per payload and the source's burst is
-- pushed straight back through the frame -- so a frame's cost and a
-- subscribe's cost are MUTUALLY RECURSIVE: a frame runs a width's
-- worth of subscribes, a subscribe installs a size's worth of frames.
-- `fCharge`'s own header records that no closed form in the cap, the
-- width and the level closes that loop, and a ceiling and a ledger are
-- both closed forms in exactly those three.  What answers the shape one
-- stratum up is a recursion on a DEPTH FUEL with every quantity read at
-- the level the walk has CLIMBED to, which is what `dCapᶜ` is.

-- AND THE FACTOR DOES NOT AFFORD THAT SHAPE, WHICH SETTLES THE OTHER
-- SIDE THE SAME WAY.  Written out -- fuel outside, rungs threaded, the
-- charge at each frame read at the level that frame stands at -- the
-- climb passes what `walkFac-ch` allows at its SECOND crossing frame,
-- at every cap this development admits.  The factor's whole ledger
-- sits below THREE rungs of the size ladder while one crossing frame
-- climbs a cap's worth of them, and the row is two-sided: one frame is
-- affordable and two are not.  So the gap is a ladder against a
-- polynomial, and widening the polynomial buys a rung of the ladder.
-- What makes the same shape work one face over is therefore not the
-- shape: the caps ceiling is DEFINED by reading its own climb and is
-- affordable by construction, while this level must fit under a
-- nesting budget that is a fixed exponential in a polynomial and reads
-- nothing.

-- AND NO ADVANCE RULE REPAIRS IT, WHICH CLOSES THE LEVEL SIDE
-- ENTIRELY.  The one thing the climb leaves free is HOW the rung count
-- moves when a frame's charge arrives, and every reading of that sits
-- between a JOIN and a SUM -- an advance may fall below neither the
-- count in hand, which is monotone, nor the charge, which is owed, and
-- need not exceed their sum.  The whole bracket is refuted at once,
-- with both endpoints exhibited rather than assumed.  A join buys
-- nothing over a sum because the two quantities it chooses between are
-- of the SAME ORDER: a frame's charge is read at the level its rung
-- stands at, so what a max discards is the lower-order term.

-- SO THE CHARGE MAY NOT READ THE WALK'S OWN LEVEL, AND THAT IS THE
-- MECHANISM RATHER THAN A NUMBER.  Moving the ceiling instead is the
-- remaining direction and it is closed one stratum up: affording a
-- rung count of the level's own order means affording the size ladder
-- iterated at itself, and the nesting budget's header records that no
-- exponent this instant's fuel affords is a tower.

-- AND ONE ARM IS THE WHOLE OF IT, WHICH IS WHAT MAKES THAT ACTIONABLE.
-- The rung count a frame adds is level-free at four of the five frame
-- kinds -- three read the program's own syntax and the crossing reads
-- the arrivals plus the telescope -- and the drain arm charges the
-- LEVEL ITSELF, flatly, with no value in it.  That single clause is
-- what turns the count into a ladder: it is the one place where what a
-- rung costs is what the rungs so far bought.  So the restatement owed
-- is per-arm rather than to the walk, and the shape to state it in is
-- the one the live face's outer arm is PROVEN in, where the conclusion
-- joins a budget passed in and there is no level to index at all.

-- AND THE PROVEN MIRROR DOES NOT TRANSFER, which is the natural next
-- move and the reason to say so here.  The potential face prices its
-- own crossing frame outright and is discharged, so the shape looks
-- portable.  It is not: that face is denominated in DEPTH, and depth
-- TRUNCATES at the defer a crossing mints across while size counts
-- straight through it.  The two faces agree at every other frame kind
-- and part company exactly here, which is why the crossing arms are
-- the ones this face cannot borrow.
--
-- REFUTED: `Refuted.Frame-Step-Size-Cross-Count` -- the crossing
--   count against the cap-side ceiling, which is what a per-frame
--   discharge of the ceiling conjunct would have to beat.
-- REFUTED: `Refuted.Walk-Ceil-Ledger` -- the same crossing against the
--   WHOLE ledger this premise supplies, at the longest path the size
--   predicate's own length conjunct admits and with the level in hand
--   held under the ledger it has been spending.  It is what says which
--   side breaks: TWO rungs of the walk put the level past every
--   allowance the path has, so no reading of this premise fixes a
--   ceiling a crossing frame fits under, and one rung lower the
--   crossing is affordable -- the gap opens with the walk rather than
--   with the program.
-- REFUTED: `Refuted.Size-Climb-Afford` -- the same premise restated as
--   a recursion on a depth fuel, the charge at each frame read at the
--   level that frame stands at, against what `walkFac-ch` affords, and
--   quantified over every ADVANCE RULE between a join and a sum with
--   both endpoints exhibited.  Two crossing frames of that climb outrun
--   the factor's whole ledger at every admissible cap under every rule
--   in the bracket, and one crossing frame does not.
-- DEAD ROUTE: a fan-out fold that does not advance at all, reading
--   every admitted entry's node table at the level the fan was
--   ENTERED at.  Killed at a two-entry fan whose first entry is a
--   drain door over a parked duplication chain: the subscription
--   stores an accumulator exponential in a program of size sixty-three
--   against the rung one level of the ladder buys, so the table is
--   under the rung when the fan is entered and over it at the state
--   that entry's own run leaves.  No longer machine-stateable, the
--   predicate it concluded in having taken the advance.
-- DEAD ROUTE: charging the fan-out advance to a per-entry LEDGER
--   instead of holding it under the ceiling.  The advance is a cap's
--   worth per entry, the fan is as wide as the registry, and an
--   entry's own walk fans again, so the ledger is exponential in the
--   dispatch gas and no exponent the walk factor can carry covers it.
-- DEAD ROUTE: instantiating the ceiling with the caps face's own --
--   `sizeCount c d ⊔ cSize c`, which its fan-out fold uses.  Dead on
--   AFFORDABILITY rather than on the shape: the size walk's level is
--   what `walkFac-ch` must afford under `nestΦAt`, which caps it at a
--   cubic in the cap, while one rung of the caps ladder already
--   exceeds every polynomial in it.  Recorded at `chain-climb-ch`
--   from the other end.
-- RECOVERY: git show 216332b:agda/src/Verify-Budget-Sufficient/Regs-Nest-Walk.agda
--   restores `szCount≤ch` and the `crossFrame?` predicate it excluded
--   the two crossings by -- a per-frame discharge of the three
--   program-reading arms against `frameCh`, which is the shelf a
--   `pathLen path * chAt` reading of the premise above would spend.
postulate
  chain-walk-szOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (Lc C : ℕ) (a : Arrival Γ) (nextId : Id)
    (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    chainCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lc
      nextId a path sched st →
    pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
    Lc + pathLen path * chAt e sl id
      + n * (Caps.cSize (capsAt e sl id) * chAt e sl id) ≤ C →
    walkSzOK (Caps.cSize (capsAt e sl id))
             (Caps.cSize (capsAt e sl id)) C Lc
             (budgetAt e (Sched.slots sched) nextId) n nextId (arrTick a)
             path (arrVal a ∷ []) (Arrival.isLast a) sched st

-- THE LEVEL ONE CHAIN CLIMBS, IN THE WALK'S OWN CURRENCY, and it is
-- exactly what the cascade's ledger already sets aside per chain: a
-- rung for the chain itself and one per frame of it, each at the
-- per-frame charge.  What the caps package reports instead is a
-- delivery-shaped ceiling every chain's step is held under, and an
-- absolute ceiling is not a per-chain increment.
--
-- AND IT IS STATED AT THE CLIMB THE STEP ACTUALLY MINTS, NOT AT A FREE
-- NUMBER STANDING FOR IT.  The caps package hands its increment back
-- inside a Σ, and a row taking that component as an unconstrained `L′`
-- has only the package's own upper bound to work from -- two ceilings
-- in the same direction, which derive nothing from one another and
-- leave the row true exactly when the caps ladder is already under the
-- per-frame product.  It is not: a PROVEN lower bound on that ladder
-- puts one rung past the product at the floor of every parameter the
-- package can pin, since a fold storey squares while the charge is
-- quadratic in the cap and linear in the path.  So the subject here is
-- the value `chainStep-caps` returns, under the hypotheses that
-- determine it -- the same law a Σ-receipt obeys, arriving at a
-- component detached from its record.
--
-- AND THE RECEIPT THAT READS LIKE A ROUTE IS NOT ONE.  The climb is
-- not the outer chain's frames: a `thru-outer` frame SUBSCRIBES an
-- inner per payload, and the only receipt on that subscribe's own
-- climb, `subscribeInner-caps`, reports it at `sLvlD` -- a LADDER
-- rung, which is an upper bound and so funds nothing.
--
-- AND NOTHING IN REACH SOURCES THE CONCLUSION, IN TWO SEPARATE WAYS,
-- OF WHICH ONLY ONE IS REPAIRABLE.  The climb is the sum of the walk's
-- per-frame witnesses, and the record supplying them bounds each ONLY
-- by a REFRESHED ladder rung: the per-frame charge this ledger counts
-- in is not a conjunct of that Σ at all, so there is nothing to sum --
-- and one level away from the entry that rung is two orders past what
-- this ledger hands a whole chain, so a chain of ONE frame is already
-- over.  The second gap is that the sum is over the wrong set: a chain
-- ending in a SHARE SINK adds no frames to `pathLen`, while the walk
-- there runs a delivery per admitted registration, each a fold of its
-- own.  That one HAS an answer -- the delivery face already proves a
-- sink-aware measure, a bridge from it to the flat length, and an
-- aggregate bridge over a round's chains, and a sibling face already
-- prices a chain list in it -- so it wanted a search and not a
-- restatement.  The first has none, and it is the binding one: no
-- count reaches a gap that is already there at one frame.
--
-- REFUTED: `Refuted.Frame-Charge-Arith` -- the per-frame conjunct the
--   walk record carries, held under the per-frame charge this ledger
--   buys, at two caps and at every depth fuel.  It is what puts the gap
--   at one frame rather than at the count.
-- REFUTED: `Refuted.Chain-Climb-Arith` -- the free-number form of this
--   row, with the state predicate dropped and the path replaced by its
--   length, at the floor of the cap, the width, the depth fuel and the
--   delivery count.  It is what forces the subject to be the step's
--   own witness, and it stands as long as the detached shape is a
--   shape anyone could reach for.
-- REFUTED: `Refuted.Caps-Face.caps-frame-boundary-absurd` -- charging
--   the climb at the ENTRY cap, which is what `chAt` reads.
-- DEAD ROUTE: restating the increment as the ABSOLUTE ceiling the caps
--   package hands back -- `sizeCount c d ⊔ cSize c`, which is what the
--   proven chains fold composes across a round.  It is dead on the
--   AFFORDABILITY side rather than on the composition: the size walk's
--   level is what `walkFac-ch` must afford under `nestΦAt`, and that
--   caps the level at a CUBIC in the cap, while one rung of the caps
--   ladder already exceeds every polynomial in it (`dLvl-gain-sizeAt`
--   puts a size cap under a single `dLvl`).  So the two ledgers agree
--   on dimension only in the INCREMENT form, and a ceiling denominated
--   in the caps ladder cannot be spent by the size walk at all.
-- DEAD ROUTE: re-denominating the conclusion in the sink-aware count,
--   which is what the fan-out gap asks for.  Dead twice over.  On
--   AFFORDABILITY: the arrival ledger bounds a round's sink-aware count
--   by the real width times the delivery size, whose fan term recurs
--   through the dispatch gas, while `walkFac-ch` affords a quadratic in
--   the cap -- so `cascade-afford` breaks where it holds today.  And on
--   SOURCING: the gap is already at one frame, so a count that is
--   larger everywhere cannot close it.
postulate
  chain-climb-ch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (Lc : ℕ) (a : Arrival Γ) (nextId : Id)
    (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e)
    (sleq : Sched.slots sched ≡ sl)
    (cok : capsOK? (frameStep Lc (capsAt e sl id)) sched st ≡ true)
    (hpz : pathSz? (Caps.cSize (frameStep Lc (capsAt e sl id))) path ≡ true)
    (hvc : valCaps? (frameStep Lc (capsAt e sl id)) sl (arrTy a) (arrVal a) ≡ true)
    (hdp : depthChain nextId a path sched st ≤ capsH e sl id) →
    proj₁ (chainStep-caps sl id Lc a nextId path sched st sleq cok hpz hvc hdp)
      ≤ suc (pathLen path) * chAt e sl id

chain-walk-LiveHyp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lc : ℕ) (a : Arrival Γ) (nextId : Id) (Lv j : ℕ)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  chainCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lc
    nextId a path sched st →
  Sched.slots sched ≡ sl →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  j + pathLen path + n * Caps.cSize (capsAt e sl id) ≤ Lv →
  Lc ≤ j * chAt e sl id →
  PathLiveHyp (budgetAt e (Sched.slots sched) nextId) n nextId (arrTick a)
    (iterSize (Caps.cSize (capsAt e sl id)) (Lv * chAt e sl id)
              (Caps.cSize (capsAt e sl id)))
    path (arrVal a ∷ []) (Arrival.isLast a) sched st
chain-walk-LiveHyp {n = n} {e = e} sl id Lc a nextId Lv j path sched st
                   hcc hsl hsz hp hj hLc =
  walk-LiveHyp-goC sl id _ n nextId (arrTick a) (Lv * Ch) Lc path
    (arrVal a ∷ []) (Arrival.isLast a) sched st entrySz entryNs entryW hp Lc≤
  where
  S = Caps.cSize (capsAt e sl id)
  Ch = chAt e sl id
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) (8≤capsAt-size e sl id)
  entrySz : valsSz? (iterSize S Lc S) (arrVal a ∷ []) ≡ true
  entrySz = ∧-intro (T⇒≡true _ (≤⇒≤ᵇ
              (≤-trans hsz (iterSize-infl S 1≤S Lc S)))) refl
  entryNs = chain-entry-nodesSz sl id Lc a nextId path sched st hcc
  step≡ : (j + pathLen path + n * S) * Ch
            ≡ j * Ch + pathLen path * Ch + n * (S * Ch)
  step≡ = trans (*-distribʳ-+ Ch (j + pathLen path) (n * S))
                (cong₂ _+_ (*-distribʳ-+ Ch j (pathLen path))
                           (*-assoc n S Ch))
  hj′ : Lc + pathLen path * Ch + n * (S * Ch) ≤ Lv * Ch
  hj′ = ≤-trans (+-monoˡ-≤ (n * (S * Ch))
                  (+-monoˡ-≤ (pathLen path * Ch) hLc))
                (≤-trans (≤-reflexive (sym step≡)) (*-monoˡ-≤ Ch hj))
  entryW  = chain-walk-szOK sl id Lc (Lv * Ch) a nextId path sched st hsl hcc hp hj′
  Lc≤ : Lc ≤ Lv * Ch
  Lc≤ = ≤-trans (m≤m+n Lc (pathLen path * Ch))
                (≤-trans (m≤m+n (Lc + pathLen path * Ch) (n * (S * Ch))) hj′)

-- THE LIVE ARM, the third and last of the chain's arms to become the
-- walk rather than an assertion about it.  Two extra terms over the
-- registry arm's conclusion: the slots, because a scripted slot's
-- subscribe mints out of script data, and the registry's join, because
-- a share fans into chains that mint out of their own.  The round
-- holds all three under the same ceiling, so the consumer pays for
-- neither.
chainStep-nest-liveC : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lc : ℕ) (a : Arrival Γ) (nextId : Id) (Lv j : ℕ)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  chainCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lc
    nextId a path sched st →
  depthChain nextId a path sched st ≤ capsH e sl id →
  Sched.slots sched ≡ sl →
  iterSize (Caps.cSize (capsAt e sl id)) (Lv * chAt e sl id)
           (Caps.cSize (capsAt e sl id))
    ≤ nestΦAt e sl id →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  j + pathLen path + n * Caps.cSize (capsAt e sl id) ≤ Lv →
  Lc ≤ j * chAt e sl id →
  foldr (λ l acc → liveNest l ⊔ acc) 0
        (Sched.live (proj₁ (proj₂ (chainStep nextId a path sched st))))
    ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
        ⊔ slotsNestSum (Sched.slots sched)
        ⊔ regsNestMax (EvalSt.registry st)
        ⊔ (nestΦAt e sl id)
chainStep-nest-liveC {e = e} sl id Lc a nextId Lv j path sched st
                     hcc hdc hsl afford hsz hp hΦ hj hLc =
  ≤-trans
    (foldPath-nest-live _ _ _ _ _ path (arrVal a ∷ []) _ _ sched st
      (Caps.cSize (capsAt e sl id)) (nestΦAt e sl id)
      (iterSize (Caps.cSize (capsAt e sl id)) (Lv * chAt e sl id)
                (Caps.cSize (capsAt e sl id)))
      (entryΦ sl id a path hp hΦ)
      (chain-walk-ΦHyp sl id Lc a nextId path sched st hcc hdc hsl hp hΦ)
      (chain-walk-LiveHyp sl id Lc a nextId Lv j path sched st
         hcc hsl hsz hp hj hLc))
    (⊔-lub ≤-refl (≤-trans afford (m≤n⊔m _ (nestΦAt e sl id))))

-- AND THAT IS WHAT A WALK CAN CARRY.  A bound the chains preserve has
-- to be one the growth cannot climb past however many chains run, and
-- a growth priced against the ENTRY store is not one -- it compounds.
-- These three price it against the program instead, so the walk's
-- bound survives a chain exactly when it already covers one instant's
-- increment, which is a condition on the bound and not on the walk.
-- REFUTED: Refuted.Chain-Step-Nodes
-- REFUTED: Refuted.Chain-Step-Live-Additive
-- DEAD ROUTE: spending the unconditional live-growth bound and
--   discharging its three disjuncts against the entry cap.  Two go;
--   the third is the path factor above, and it is not repairable by a
--   premise, only by a tighter growth statement.
-- DEAD ROUTE: restating the whole walk one instant up, so the arms
--   preserve the successor cap and the round's ceiling is read there.
--   The entry lifts and the arms carry over, but the consumer does
--   not: its fuel is the exponential at THIS instant, which the caps
--   recurrence pins to this instant's cap.
-- DEAD ROUTE: charging the arms the instant's INCREMENT, which is what
--   they carried while they mirrored the entry burst.  The increment's
--   own exponent reads the delivery at the NEXT instant, and the size
--   there is already a blowup story above the fuel available here, so
--   no reading of it fits under this instant's exponential.
chainStep-store≤ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lc : ℕ) (a : Arrival Γ) (nextId : Id) (S : ℕ) (Lv j : ℕ)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  chainCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lc
    nextId a path sched st →
  depthChain nextId a path sched st ≤ capsH e sl id →
  Sched.slots sched ≡ sl →
  iterSize (Caps.cSize (capsAt e sl id)) (Lv * chAt e sl id)
           (Caps.cSize (capsAt e sl id))
    ≤ nestΦAt e sl id →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  j + pathLen path + n * Caps.cSize (capsAt e sl id) ≤ Lv →
  Lc ≤ j * chAt e sl id →
  nestΦAt e sl id ≤ S →
  storeNestMax sched st ≤ S →
  storeNestMax (proj₁ (proj₂ (chainStep nextId a path sched st)))
               (proj₂ (proj₂ (chainStep nextId a path sched st))) ≤ S
chainStep-store≤ {e = e} sl id Lc a nextId S Lv j path sched st
                 hcc hdc hsl afford hsz hp hΦ hj hLc hinc hS =
  storeNestMax-lub sd′ st′ S SL
    (≤-trans (chainStep-nest-liveC  sl id Lc a nextId Lv j path sched st
                hcc hdc hsl afford hsz hp hΦ hj hLc)
             (⊔-lub (⊔-lub (⊔-lub (≤-trans (storeNest-live≤  sched st) hS)
                                  (≤-trans (storeNest-slots≤ sched st) hS))
                           (≤-trans (storeNest-regs≤ sched st) hS))
                    hinc))
    (≤-trans (chainStep-nest-nodesC sl id Lc a nextId path sched st
                hcc hdc hsl hp hΦ)
             (⊔-lub (⊔-lub (≤-trans (storeNest-nodes≤ sched st) hS)
                           (≤-trans (storeNest-regs≤ sched st) hS))
                    hinc))
    (≤-trans (chainStep-nest-regsC  sl id Lc a nextId path sched st
                hcc hdc hsl hp hΦ)
             (⊔-lub (≤-trans (storeNest-regs≤  sched st) hS) hinc))
  where
  sd′ = proj₁ (proj₂ (chainStep nextId a path sched st))
  st′ = proj₂ (proj₂ (chainStep nextId a path sched st))
  SL : slotsNestSum (Sched.slots sd′) ≤ S
  SL = ≤-trans (≤-reflexive (cong slotsNestSum
                              (chainStep-slots nextId a path sched st)))
               (≤-trans (storeNest-slots≤ sched st) hS)

-- THE ROUND IS A WALK OVER ITS CHAINS, and the three-callee clause is
-- the one `depthCascade` reports: the tail at the incoming state, the
-- live chain at the delivered-marked one, and the tail again at the
-- state that chain left.

-- AND THE SELECTION'S LEVEL BUDGET IS ONE NUMBER, PEELED THREE WAYS
-- PER CHAIN.  The head chain walks at the level reached so far, so it
-- owes its own frames; the tail is re-entered twice, once at that same
-- level and once one above it, and both times with one fewer chain in
-- hand.  `chainsLenSum + length` is what makes those three fit under
-- one premise: the sum pays the frames and the count pays the levels.
--
-- AND THE BUDGET IS NOT THE SIZE CAP, WHICH IS THE WHOLE FINDING HERE.
-- A cap admits chains of a cap's length and a selection as wide as the
-- registry, so its own `chainsLenSum` already outruns it -- there is no
-- arrangement of the arithmetic under which a cascade's levels fit
-- under the number one chain's frames fit under.  So the budget rides
-- as a parameter with the affordability that pays for it, and the
-- caller carries a ledger it can actually meet.
--
-- AND IT CARRIES THE CAPS FACE'S PACKAGE UNPROJECTED, because the
-- measure it bounds is.  Every chain's store step is charged here
-- whatever the cancellation test says, so what pays for it has to be
-- the reading that owes a receipt at every entry rather than at the
-- surviving ones.  The chain leaf supplies each descent bound from the
-- entry store's ceiling, so nothing here needs the round's own bound
-- -- which is what this is proving.
cascade-depth-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lc : ℕ) (a : Arrival Γ) (nextId : Id) (S : ℕ) (Lv j : ℕ)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  chainsCapsAll (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lc
    a nextId chains sched st →
  sightCeil (sizeᵉ e) (nestDᵛ (arrTy a) (arrVal a)) S (nestUnit e sl)
    ≤ capsH e sl id →
  Sched.slots sched ≡ sl →
  iterSize (Caps.cSize (capsAt e sl id)) (Lv * chAt e sl id)
           (Caps.cSize (capsAt e sl id))
    ≤ nestΦAt e sl id →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  all (λ rc → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rc)) chains ≡ true →
  all (λ rc → nestDᵛ (arrTy a) (arrVal a) + pathNestD (proj₂ rc)
                ≤ᵇ nestUnit e sl) chains ≡ true →
  j + chainsLenSum chains + length chains
    + n * Caps.cSize (capsAt e sl id) ≤ Lv →
  Lc ≤ j * chAt e sl id →
  nestΦAt e sl id ≤ S →
  storeNestMax sched st ≤ S →
  depthCascade a nextId chains sched st
    ≤ sightCeil (sizeᵉ e) (nestDᵛ (arrTy a) (arrVal a)) S (nestUnit e sl)
cascade-depth-go sl id Lc a nextId S Lv j [] sched st
                 hca hsight hsl afford hsz hps hΦs hbud hLc hinc hS = z≤n
cascade-depth-go {n = n} {e = e} sl id Lc a nextId S Lv j ((rid , c) ∷ cs) sched st
  hca hsight hsl afford hsz hps hΦs hbud hLc hinc hS =
  ⊔-lub (cascade-depth-go sl id Lc a nextId S Lv j cs sched st
           (proj₁ hca) hsight hsl afford hsz hpr hΦr hbud-tail hLc hinc hS)
        (⊔-lub (chain-depth-sighted sl a nextId S c sched st₀ hsl hS)
               (cascade-depth-go sl id (Lc + L′)
                  a nextId S Lv (j + suc (pathLen c)) cs
                  (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                  (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hca))))) hsight
                  (trans (chainStep-slots nextId a c sched st₀) hsl)
                  afford hsz hpr hΦr
                  hbud-next
                  hLc-next
                  hinc
                  (chainStep-store≤ sl id Lc a nextId S Lv j c sched st₀
                     (proj₁ (proj₂ hca)) hdc
                     hsl afford hsz hpc
                     (≤ᵇ⇒≤ (nestDᵛ (arrTy a) (arrVal a) + pathNestD c)
                           (nestUnit e sl) (T-to hΦc))
                     hbud-head hLc hinc hS)))
  where
  st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
  hdc = ≤-trans (chain-depth-sighted sl a nextId S c sched st₀ hsl hS) hsight
  r   = chainStep nextId a c sched st₀
  hpc = proj₁ (∧-true (pathSz? (Caps.cSize (capsAt e sl id)) c) _ hps)
  hpr = proj₂ (∧-true (pathSz? (Caps.cSize (capsAt e sl id)) c) _ hps)
  hΦc = proj₁ (∧-true (nestDᵛ (arrTy a) (arrVal a) + pathNestD c
                         ≤ᵇ nestUnit e sl) _ hΦs)
  hΦr = proj₂ (∧-true (nestDᵛ (arrTy a) (arrVal a) + pathNestD c
                         ≤ᵇ nestUnit e sl) _ hΦs)
  N   = n * Caps.cSize (capsAt e sl id)
  hbud-head : j + pathLen c + N ≤ Lv
  hbud-head =
    ≤-trans (+-monoˡ-≤ N
              (≤-trans (+-monoʳ-≤ j (m≤m+n (pathLen c) (chainsLenSum cs)))
                       (m≤m+n (j + (pathLen c + chainsLenSum cs))
                              (suc (length cs)))))
            hbud
  hbud-tail : j + chainsLenSum cs + length cs + N ≤ Lv
  hbud-tail =
    ≤-trans (+-monoˡ-≤ N
              (+-mono-≤ (+-monoʳ-≤ j (m≤n+m (chainsLenSum cs) (pathLen c)))
                        (n≤1+n (length cs))))
            hbud
  hbud-next : j + suc (pathLen c) + chainsLenSum cs + length cs + N ≤ Lv
  hbud-next =
    ≤-trans (+-monoˡ-≤ N (≤-reflexive
              (solve 4 (λ x p s l → x :+ (con 1 :+ p) :+ s :+ l
                                 := x :+ (p :+ s) :+ (con 1 :+ l))
                     refl j (pathLen c) (chainsLenSum cs) (length cs))))
            hbud
  L′ = proj₁ (proj₂ (proj₂ hca))
  -- the package's own second conjunct IS this ledger's rung: the
  -- descent never converts a caps ceiling, it reads the increment in
  -- the per-frame charge the position ledger counts in
  hLc-next : Lc + L′ ≤ (j + suc (pathLen c)) * chAt e sl id
  hLc-next =
    ≤-trans (+-mono-≤ hLc (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ hca))))))
            (≤-reflexive
              (sym (*-distribʳ-+ (chAt e sl id) j (suc (pathLen c)))))

-- THE LADDER IS CLIMBED A FRAME-CHARGE AT A TIME, which is what the
-- per-frame count being a WIDTH times a cap costs this arithmetic.
-- The cascade's ledger is unchanged -- a cap squared plus a cap plus a
-- cap squared, which is what the selection can reach -- and every rung
-- of it is now `chAt` rungs of the size ladder.
--
-- AND IT COSTS EXACTLY TWO POWERS OF THE CAP, which is what
-- `nestWalkAt`'s exponent was grown by.  `iterSize≤2^` carries a count
-- `j` into exponent `S*j`, so the ledger's `S*S + S + S*S` rungs at a
-- per-frame charge of `S * suc S` reach `2S⁵ + 3S⁴ + S³`, where the old
-- one-rung-per-frame reading reached `2S³ + S²`.  Three fifth powers
-- cover that -- `3S⁴ + S³ ≤ 4S⁴ ≤ S⁵` off the cap's own floor -- and
-- `walk-sight≤exp` pays for the grown exponent with the quintic
-- threshold rather than the cubic one.
-- DEAD ROUTE: keeping the old count and charging one rung per frame.
--   Refuted twice in `Verify-Budget-Sufficient.Regs-Nest-Walk`'s own
--   header -- unconditionally, and again with the store premise added.
walkFacCh≤nestΦAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) →
  2 ^ (Caps.cSize (capsAt e sl id)
         * ((Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id)
             + Caps.cSize (capsAt e sl id)
             + Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id))
            * chAt e sl id))
    * Caps.cSize (capsAt e sl id)
    ≤ nestΦAt e sl id
walkFacCh≤nestΦAt e sl id =
  ≤-trans (≤-trans (*-mono-≤ (^-monoʳ-≤ 2 expLE) tail≥)
                   (≤-reflexive (sym (nestWalkAt-def e sl id))))
          (nestWalkAt≤nestΦAt e sl id)
  where
  S  = Caps.cSize (capsAt e sl id)
  P2 = S * S
  P3 = S * P2
  P4 = S * P3
  Q  = S * P4
  8≤S : 8 ≤ S
  8≤S = 8≤capsAt-size e sl id
  1≤S : 1 ≤ S
  1≤S = ≤-trans (≤ᵇ⇒≤ 1 8 tt) 8≤S
  4≤S : 4 ≤ S
  4≤S = ≤-trans (≤ᵇ⇒≤ 4 8 tt) 8≤S
  P3≤P4 : P3 ≤ P4
  P3≤P4 = ≤-trans (≤-reflexive (sym (*-identityˡ P3))) (*-monoˡ-≤ P3 1≤S)
  eq4 : 3 * P4 + P4 ≡ 4 * P4
  eq4 = solve 1 (λ a → con 3 :* a :+ a := con 4 :* a) refl P4
  -- THE QUARTIC RESIDUE FITS UNDER ONE MORE FACTOR OF THE CAP, which is
  -- the whole reason three fifth powers suffice rather than four.
  quartic≤Q : 3 * P4 + P3 ≤ Q
  quartic≤Q =
    ≤-trans (+-monoʳ-≤ (3 * P4) P3≤P4)
            (≤-trans (≤-reflexive eq4) (*-monoˡ-≤ P4 4≤S))
  shape : S * ((P2 + S + P2) * (S * suc S)) ≡ Q + Q + (3 * P4 + P3)
  shape =
    solve 1 (λ a → a :* ((a :* a :+ a :+ a :* a) :* (a :* (con 1 :+ a)))
                   := a :* (a :* (a :* (a :* a)))
                      :+ a :* (a :* (a :* (a :* a)))
                      :+ (con 3 :* (a :* (a :* (a :* a))) :+ a :* (a :* a)))
            refl S
  expLE : S * ((P2 + S + P2) * (S * suc S)) ≤ suc (Q + Q + Q + (P2 + P2))
  expLE =
    ≤-trans (≤-reflexive shape)
            (≤-trans (+-monoʳ-≤ (Q + Q) quartic≤Q)
                     (≤-trans (m≤m+n (Q + Q + Q) (P2 + P2)) (n≤1+n _)))
  tail≥ : S ≤ nestUnit e sl + (P2 + P2) + S + S * slotWrapSum sl
  tail≥ =
    ≤-trans (m≤n+m S (nestUnit e sl + (P2 + P2)))
            (m≤m+n (nestUnit e sl + (P2 + P2) + S) (S * slotWrapSum sl))

walkFac-ch : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) (L : ℕ) →
  L ≤ Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id)
      + Caps.cSize (capsAt e sl id)
      + Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id) →
  iterSize (Caps.cSize (capsAt e sl id)) (L * chAt e sl id)
           (Caps.cSize (capsAt e sl id))
    ≤ nestΦAt e sl id
walkFac-ch e sl id L hL =
  ≤-trans (iterSize≤2^ S (L * Ch) S (8≤capsAt-size e sl id) ≤-refl)
          (≤-trans (*-monoˡ-≤ S
                      (^-monoʳ-≤ 2 (*-monoʳ-≤ S (*-monoˡ-≤ Ch hL))))
                   (walkFacCh≤nestΦAt e sl id))
  where
  S  = Caps.cSize (capsAt e sl id)
  Ch = chAt e sl id

-- EVERY LEVEL A WHOLE CASCADE REACHES IS AFFORDABLE, and this is the
-- one place the level ledger has to meet the walk's ceiling.  The
-- selection enters its k-th chain at the level the first k-1 left and
-- climbs one per frame inside it, so the levels it reaches run to the
-- chains' total length plus their count -- and that ledger is what
-- `cascade-depth-go` carries, precisely so this obligation can be
-- stated once for the whole selection rather than re-derived per chain.
--
-- AND THE INVARIANT IS PART OF THE STATEMENT, not a convenience the
-- caller happens to offer.  Without it the two sides are not
-- comparable quantities at all: the charge reads the program, the slot
-- vocabulary and the instant and never the state, while the ledger
-- reads the state and nothing else -- so a registry longer than the
-- charge satisfies every hypothesis and lands a level above the
-- conclusion.  With it the registry is a width and each chain is legal
-- at a cap's length, so the ledger is a cap SQUARED plus a cap, which
-- is the range the frame charge above is read over.
--
-- REFUTED: Refuted.Cascade-Afford-Wide
-- TWIN: `arr-chains-len-sum`
-- DEAD ROUTE: keying the cascade's budget to the size cap, so that a
--   one-chain affordability discharges it unchanged.  The cap admits
--   chains of a cap's length and the registry admits a selection as
--   wide as itself, so the selection's own `chainsLenSum` already
--   outruns the cap -- the premise is unsatisfiable at the caller
--   rather than merely hard to prove there.
cascade-afford : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? (capsAt e sl id) sched st ≡ true →
  iterSize (Caps.cSize (capsAt e sl id))
    ((chainsLenSum (chainsOf a st) + length (chainsOf a st)
      + n * Caps.cSize (capsAt e sl id)) * chAt e sl id)
    (Caps.cSize (capsAt e sl id))
    ≤ nestΦAt e sl id
cascade-afford {n = n} {e = e} sl id a sched st hok =
  walkFac-ch e sl id _ ledger
  where
  S = Caps.cSize (capsAt e sl id)
  wid : length (chainsOf a st) ≤ S
  wid = ≤-trans (chains-count-width sl id a sched st hok)
                (≤-trans (≤-reflexive (realWidAt-def e sl id))
                         (B2-cReg≤cSize e sl id))
  ledger : chainsLenSum (chainsOf a st) + length (chainsOf a st) + n * S
             ≤ S * S + S + S * S
  ledger =
    +-mono-≤ (+-mono-≤ (≤-trans (chainsLenSum-bound S (chainsOf a st)
                                   (chainsGo-sz S a (EvalSt.registry st)
                                     (capsOK?-regs (capsAt e sl id) sched st hok)))
                                (*-monoˡ-≤ S wid))
                       wid)
             (*-monoˡ-≤ S (n≤capsAt-size e sl id))

-- AND ALL THREE OF THE CEILING'S SUMMANDS ARE THE SAME CAP.  The
-- arrival's nesting is held under it by the caller's premise, the
-- store's by the nesting invariant, and the wrap unit IS the cap at
-- instant zero -- so the sighted sum is three readings of one number
-- and the ceiling collapses to a multiple of it.  That collapse is the
-- whole of what the run-side hypotheses buy.
sight-collapse : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (a : Arrival Γ) (B S : ℕ) →
  S ≤ B →
  nestDᵛ (arrTy a) (arrVal a) ≤ B →
  nestUnit e sl ≤ B →
  sightCeil (sizeᵉ e) (nestDᵛ (arrTy a) (arrVal a)) S (nestUnit e sl)
    ≤ suc (sizeᵉ e) * suc (3 * B)
sight-collapse {e = e} sl a B S hS hval hu =
  *-monoʳ-≤ (suc (sizeᵉ e)) (s≤s sum≤3B)
  where
  eq : B + B + B ≡ 3 * B
  eq = solve 1 (λ b → b :+ b :+ b := con 3 :* b) refl B
  sum≤3B : nestDᵛ (arrTy a) (arrVal a) + S + nestUnit e sl ≤ 3 * B
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
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (B S : ℕ) →
  S ≤ B →
  nestDᵛ (arrTy a) (arrVal a) ≤ B →
  nestUnit e sl ≤ B →
  suc (sizeᵉ e) * suc (3 * B) ≤ capsH e sl id →
  sightCeil (sizeᵉ e) (nestDᵛ (arrTy a) (arrVal a)) S (nestUnit e sl)
    ≤ capsH e sl id
sighted-nest≤capsH {e = e} sl id a B S hS hval hu room =
  ≤-trans (sight-collapse {e = e} sl a B S hS hval hu) room

-- THE CASCADE'S CAPS DOOR, STATED WHERE THE STORE CEILING IS.  Every
-- chain of the round gets the caps package, including the ones the
-- evaluator steps over, which is the reading the depth measure needs
-- and the surviving fold does not offer.
--
-- AND IT ASKS FOR AFFORDABILITY BECAUSE ITS THIRD ARM CROSSES A STEP.
-- The surviving fold takes the round's descent bound as a premise and
-- splits it three ways, and the same split would serve here, since the
-- descent's own recursion is unconditional and three-fold exactly as
-- this reading is.  What closes that route is not the arms but the
-- SUPPLY: the only machine producing that bound for a whole round is
-- the measure this statement is an ingredient of, so taking it here
-- would make the two mutually circular.  The store ceiling is what
-- generates a descent bound at every state the walk reaches rather
-- than at the entry alone, and the package around it is what carries
-- the ceiling across a step -- so the premises are what the third arm
-- costs, not what the caller happens to hold.
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
-- evaluator steps over.  The position ledger is what carries the
-- climbed level to the next entry.
cascade-caps-all-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lc : ℕ) (a : Arrival Γ) (nextId : Id) (S : ℕ) (Lv j : ℕ)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (frameStep Lc (capsAt e sl id)) sched st ≡ true →
  sightCeil (sizeᵉ e) (nestDᵛ (arrTy a) (arrVal a)) S (nestUnit e sl)
    ≤ capsH e sl id →
  iterSize (Caps.cSize (capsAt e sl id)) (Lv * chAt e sl id)
           (Caps.cSize (capsAt e sl id))
    ≤ nestΦAt e sl id →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  all (λ rc → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rc)) chains ≡ true →
  all (λ rc → nestDᵛ (arrTy a) (arrVal a) + pathNestD (proj₂ rc)
                ≤ᵇ nestUnit e sl) chains ≡ true →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  nestClosOK?ᵛ (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  j + chainsLenSum chains + length chains
    + n * Caps.cSize (capsAt e sl id) ≤ Lv →
  Lc ≤ j * chAt e sl id →
  nestΦAt e sl id ≤ S →
  storeNestMax sched st ≤ S →
  (J g i : ℕ) →
  4 + (sizeᵉ e + slotsSize sl) + n + n ≤ g →
  Reached (capsAt e sl id) (capsH e sl id) J (suc g) →
  i + length chains
    ≤ regAt (Caps.cSize (capsAt e sl id)) (Caps.cReg (capsAt e sl id)) J →
  Lc ≤ Ent (capsAt e sl id) (capsH e sl id) J g i →
  chainsCapsAll (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lc
    a nextId chains sched st
cascade-caps-all-go sl id Lc a nextId S Lv j [] sched st
  sleq cok hsc afford hsz hpz hΦs hvc hcl hbud hLcCh hinc hS J g i hfl hR hlen hLc = tt
cascade-caps-all-go {n = n} {e = e} sl id Lc a nextId S Lv j ((rid , path) ∷ chains) sched st
  sleq cok hsc afford hsz hpz hΦs hvc hcl hbud hLcCh hinc hS J g i hfl hR hlen hLc =
    cascade-caps-all-go sl id Lc a nextId S Lv j chains sched st
      sleq cok hsc afford hsz hpr hΦr hvc hcl hbud-tail hLcCh hinc hS
      J g i hfl hR
      (≤-trans (+-monoʳ-≤ i (n≤1+n (length chains))) hlen) hLc
  , HEAD
  , proj₁ ST
  , proj₁ (proj₂ ST)
  , CLIMB
  , cascade-caps-all-go sl id (Lc + proj₁ ST) a nextId S Lv
      (j + suc (pathLen path)) chains
      (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
      (trans (chainStep-slots nextId a path sched st′) sleq)
      (proj₂ (proj₂ ST)) hsc afford hsz hpr hΦr hvc hcl
      hbud-next hLcCh-next hinc
      (chainStep-store≤ sl id Lc a nextId S Lv j path sched st′
         HEAD hdc sleq afford hsz hpc hΦc hbud-head hLcCh hinc hS)
      J g (suc i) hfl hR
      (subst (_≤ regAt B (Caps.cReg c) J) (+-suc i (length chains)) hlen)
      (≤-trans (proj₁ (proj₂ ST)) STEP)
  where
  st′ = record st { delivered = rid ∷ EvalSt.delivered st }
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
  -- this chain's own descent, priced off the store ceiling rather than
  -- off a bound on the round -- which is the premise this door does
  -- not have and the surviving fold does
  hdc = ≤-trans (chain-depth-sighted sl a nextId S path sched st′ sleq hS) hsc
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
  HEAD = arr-chain-caps sl id Lc a nextId path sched st′ sleq cok HVC HCL
           (pathSz?-widen path (proj₁ c⊑) hpc) hdc
           (g , Pos c d J g i , hfl , CH≤ , walk J g i HI hR)
  ST  = chainStep-caps sl id Lc a nextId path sched st′ sleq cok
          (pathSz?-widen path (proj₁ c⊑) hpc)
          (valCaps?-widen sl (arrTy a) (arrVal a) c⊑ hvc) hdc
  CLIMB : proj₁ ST ≤ suc (pathLen path) * chAt e sl id
  CLIMB = chain-climb-ch sl id Lc a nextId path sched st′ sleq cok
            (pathSz?-widen path (proj₁ c⊑) hpc)
            (valCaps?-widen sl (arrTy a) (arrVal a) c⊑ hvc) hdc
  -- and the fold's own climb lands on the NEXT position exactly when
  -- this chain's deliveries fit the budget read at this one
  STEP : lvls B W d Lc (suc D) ≤ Ent c d J g (suc i)
  STEP = ≤-trans (lvls-mono (suc D) (suc D) 2≤S ≤-refl ≤-refl hLc ≤-refl)
                 (ent-step c d J g i D 2≤S
                    (chain-deliv-cap sl id a nextId path sched st′ Lc J g i
                       sleq hgn cok (pathSz?-widen path (proj₁ c⊑) hpc)
                       HVC hdc hLc))
  N   = n * B
  hbud-head : j + pathLen path + N ≤ Lv
  hbud-head =
    ≤-trans (+-monoˡ-≤ N
              (≤-trans (+-monoʳ-≤ j (m≤m+n (pathLen path) (chainsLenSum chains)))
                       (m≤m+n (j + (pathLen path + chainsLenSum chains))
                              (suc (length chains)))))
            hbud
  hbud-tail : j + chainsLenSum chains + length chains + N ≤ Lv
  hbud-tail =
    ≤-trans (+-monoˡ-≤ N
              (+-mono-≤ (+-monoʳ-≤ j (m≤n+m (chainsLenSum chains) (pathLen path)))
                        (n≤1+n (length chains))))
            hbud
  hbud-next : j + suc (pathLen path) + chainsLenSum chains + length chains + N ≤ Lv
  hbud-next =
    ≤-trans (+-monoˡ-≤ N (≤-reflexive
              (solve 4 (λ x p s l → x :+ (con 1 :+ p) :+ s :+ l
                                 := x :+ (p :+ s) :+ (con 1 :+ l))
                     refl j (pathLen path) (chainsLenSum chains)
                     (length chains))))
            hbud
  -- and the level the chain climbs is paid for out of the same rungs:
  -- one for the chain and one per frame of it, at the per-frame charge
  hLcCh-next : Lc + proj₁ ST ≤ (j + suc (pathLen path)) * chAt e sl id
  hLcCh-next =
    ≤-trans (+-mono-≤ hLcCh CLIMB)
            (≤-reflexive
              (sym (*-distribʳ-+ (chAt e sl id) j (suc (pathLen path)))))

cascade-caps-all : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id) (S : ℕ) (Lv : ℕ)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  sightCeil (sizeᵉ e) (nestDᵛ (arrTy a) (arrVal a)) S (nestUnit e sl)
    ≤ capsH e sl id →
  iterSize (Caps.cSize (capsAt e sl id)) (Lv * chAt e sl id)
           (Caps.cSize (capsAt e sl id))
    ≤ nestΦAt e sl id →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  all (λ rc → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rc))
      (chainsOf a st) ≡ true →
  all (λ rc → nestDᵛ (arrTy a) (arrVal a) + pathNestD (proj₂ rc)
                ≤ᵇ nestUnit e sl) (chainsOf a st) ≡ true →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  nestClosOK?ᵛ (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  chainsLenSum (chainsOf a st) + length (chainsOf a st)
    + n * Caps.cSize (capsAt e sl id) ≤ Lv →
  nestΦAt e sl id ≤ S →
  storeNestMax sched (cascadeLatch a st) ≤ S →
  chainsCapsAll (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) 0
    a nextId (chainsOf a st) sched (cascadeLatch a st)
cascade-caps-all {e = e} sl id a nextId S Lv sched st sleq cok hsc afford hsz
                 hpz hΦs hvc hcl hbud hinc hsn =
  cascade-caps-all-go sl id 0 a nextId S Lv 0 (chainsOf a st) sched
    (cascadeLatch a st) sleq
    (subst (λ x → capsOK? x sched (cascadeLatch a st) ≡ true)
           (sym (frameStep-0 (capsAt e sl id)))
           (cascadeLatch-caps (capsAt e sl id) a sched st cok))
    hsc afford hsz hpz hΦs hvc hcl hbud z≤n hinc hsn
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
-- store step inside spends.  The three run-side premises the caps
-- reading wants -- the value's own caps, its closures', and the
-- arrival's nesting under the cap -- are the same three the instant
-- loop already prices this arrival by, so the door widens by what the
-- caller was holding anyway.
cascade-depth-sighted : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  nestClosOK?ᵛ (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  depthCascade a nextId (chainsOf a st) sched (cascadeLatch a st)
    ≤ sightCeil (sizeᵉ e) (nestDᵛ (arrTy a) (arrVal a))
                (nestΦAt e sl id)
                (nestUnit e sl)
cascade-depth-sighted {n = n} {e = e} sl id a nextId sched st
                      hsl hok hn hval hsz valC closC =
  cascade-depth-go sl id 0 a nextId (nestΦAt e sl id) LV 0
    (chainsOf a st) sched (cascadeLatch a st)
    (cascade-caps-all sl id a nextId (nestΦAt e sl id) LV sched st hsl hok
       SIGHT (cascade-afford sl id a sched st hok) hsz CHAINPZ CHAINΦ valC closC
       ≤-refl ≤-refl STORE)
    SIGHT
    hsl
    (cascade-afford sl id a sched st hok) hsz
    CHAINPZ
    CHAINΦ
    ≤-refl
    z≤n
    ≤-refl
    STORE
  where
  LV = chainsLenSum (chainsOf a st) + length (chainsOf a st)
         + n * Caps.cSize (capsAt e sl id)
  CHAINPZ = chainsOf-caps (Caps.cSize (capsAt e sl id)) a st
              (capsOK?-regs (capsAt e sl id) sched st hok)
  CHAINΦ = chainsNest-all (nestDᵛ (arrTy a) (arrVal a)) (nestUnit e sl)
             (chainsOf a st)
             (arr-chains-nest-syn sl id a sched st hsl hok hn)
  STORE = ≤-trans (nestOK?-store e sl id sched (cascadeLatch a st)
                    (trans (nestOK?-latch e sl id a sched st) hn))
                  (nestCapAt≤nestΦAt e sl id)
  SIGHT = sighted-nest≤capsH sl id a (nestΦAt e sl id) (nestΦAt e sl id) ≤-refl
            (≤-trans hval (nestCapAt≤nestΦAt e sl id))
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
  depthCascade a nextId (chainsOf a st) sched (cascadeLatch a st)
    ≤ capsH e sl id
cascade-depth-capsH {e = e} sl id a nextId sched st hsl hcaps hnest hval hsz valC closC =
  ≤-trans (cascade-depth-sighted sl id a nextId sched st hsl hcaps hnest hval hsz valC closC)
          (sighted-nest≤capsH sl id a B B ≤-refl
             (≤-trans hval (nestCapAt≤nestΦAt e sl id))
             (≤-trans (unit≤cap e sl id)
               (nestCapAt≤nestΦAt e sl id))
             (nestΦ-sight≤capsH e sl id))
  where
  B = nestΦAt e sl id

caps-tick :
  (∀ {n′} {Γ′ : Ctx n′} {t′} {e′ : Closed Γ′ t′} {u′}
    (c′ : Caps) (dep bud j′ : ℕ) (g′ : Gas) (op′ : AllOp) (allNid′ : NodeId)
    (κ′ : Path Γ′ u′ t′) (id′ : Id) (now′ : Tick) (o′ : Val Γ′ (obs u′))
    (sl′ : Slots Γ′) (sched′ : Sched Γ′) (st′ : EvalSt e′) →
    2 ≤ Caps.cSize c′ →
    1 ≤ Caps.cReg c′ →
    Sched.slots sched′ ≡ sl′ →
    slotsCaps? (Caps.cSize c′) (Caps.cWid c′) sl′ ≡ true →
    slotsSize sl′ ≤ Caps.cSize c′ →
    capsOK? (frameStep j′ c′) sched′ st′ ≡ true →
    valCaps? (frameStep j′ c′) sl′ (obs u′) o′ ≡ true →
    pathSz? (Caps.cSize (frameStep j′ c′)) κ′ ≡ true →
    suc (pathLen κ′) ≤ Caps.cSize (frameStep j′ c′) →
    nest o′ sl′ (EvalSt.connectedShares st′) ≤ bud →
    depthInner g′ op′ allNid′ κ′ id′ now′ o′ sched′ st′ ≤ dep →
    let r′ = subscribeInner g′ op′ allNid′ κ′ id′ now′ o′ sched′ st′
    in Σ ℕ λ j₂ →
       (capsOK? (frameStep (j′ + j₂) c′)
                (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r′)))))
                (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r′))))) ≡ true)
       × (valsCaps? (frameStep (j′ + j₂) c′) sl′ (proj₁ (proj₂ r′)) ≡ true)
       × (all (eventCaps? (frameStep (j′ + j₂) c′) sl′)
              (proj₁ (proj₂ (proj₂ r′))) ≡ true)
       × (suc (j′ + j₂) ≤ sLvlD (Caps.cSize c′) (Caps.cWid c′) dep (suc bud) (suc j′))
   ) →
  -- ifc  (innerFinish-caps, .Subscribe-Face)
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (dep bud j : ℕ) (g : Gas) (op : AllOp) (allNid inst : NodeId)
    (κ : Path Γ s t) (id : Id) (now : Tick) (vals : List (Val Γ s))
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
    depthFin g op allNid inst κ id now vals sched st
      (lookupNode allNid (EvalSt.nodes st)) ≤ dep →
    let r = innerFinish g op allNid inst κ id now vals sched st
              (lookupNode allNid (EvalSt.nodes st))
    in Σ ℕ λ j′ →
       (capsOK? (frameStep (j + j′) c)
                (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
                  ≡ true)
       × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
       × (all (eventCaps? (frameStep (j + j′) c) sl)
              (proj₁ (proj₂ r)) ≡ true)
       × (suc (j + j′) ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  nestClosOK?ᵛ (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  let r = cascade a nextId sched st
  in capsOK? (capsAt e sl (suc id)) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
caps-tick siC ifc {e = e} sl id a nextId sched st slEq pre nok bnd val closV =
  cascadeFinish-caps (capsAt e sl (suc id)) a (proj₁ (proj₂ GOr)) (proj₂ (proj₂ GOr))
    (capsOK?-mono (frameStep j c) (capsAt e sl (suc id))
                  (proj₁ (proj₂ GOr)) (proj₂ (proj₂ GOr))
                  (frameStep-mono-j c (2≤capsAt-size e sl id) jFits)
                  (proj₂ (proj₂ GO)))
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
             val closV)
  GOr   = cascadeGo a nextId (chainsOf a st) sched st₀
  j     = proj₁ GO
  jFits = proj₁ (proj₂ GO)

-- REFUTED: `caps-frame-boundary-absurd`
--   (sizeStep C C ≤ C is impossible for 1 ≤ C) and `reach-via-size-absurd`
--   (2 ^ C ≤ C is impossible) now live in `refuted/Refuted/Caps-Face.agda`,
--   checked by `make refuted`.  Do not re-attempt either bound here.


-- (`reach-resets`, the reset cluster this section's prose names, is
-- declared ABOVE the face postulate block — `thruOuter-face` consumes
-- it and is itself consumed before this point in the file.)

------------------------------------------------------------------
-- HOP DESCENT, the *All clause's missing edge — AND THE OPEN HOLE.

