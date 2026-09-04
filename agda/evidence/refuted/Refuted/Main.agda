-- THE REFUTATION ROOT.  `make refuted` checks this module, and nothing
-- else reaches it: `make gate-heavy` compiles `src/Main.agda`, which cannot
-- import this tree, and `make wiring` scans `agda/src` only.
--
-- Naming each witness here is what keeps this tree honest: a refutation
-- that is not listed is not checked, exactly as in src/Main.agda.
module Refuted.Main where

open import Refuted.Caps-Face
  using (caps-frame-boundary-absurd; reach-via-size-absurd;
         scan-count-under-ceiling-absurd; wid≤size-absurd;
         wid≤exp-size-absurd; wid₃≡; size₃≡)
open import Refuted.Anchor
  using (g0-hasAtLeast-absurd; walk-hyps-absurd; hop-anchor-absurd;
         round3b-ledger-reset-absurd; round3-old-ell-absurd;
         round3-anchor-indexed-absurd)
open import Refuted.Wet
  using (wet-ceiling-absurd; wet-ell-absurd)
open import Refuted.Hop-Drag
  using (hop-drag-absurd)
open import Refuted.Cut-Through
  using (cutThrough-close-bound-dying-absurd; cutThrough-live-dying-absurd)
open import Refuted.MergeAll-Drain
  using (mergeAllDrain-nodry-nestBud-absurd; thruConsume-nodry-nestBud-absurd)
open import Refuted.Thru-Loop
  using (thruConsume-nodry-loop-absurd)
open import Refuted.Inner-Nodry
  using (inner-nodry-inv-regLen-absurd)
open import Refuted.Nest-Depth-One
  using (descent≡81; oneSyn≡74; nest-one-syn-absurd)
open import Refuted.Nest-Depth-Live-Reg
  using (liveDescent≡81; liveReg≡24; nest-live-reg-absurd)
open import Refuted.Cascade-Deliv-Depth
  using (descent≡49; perDeliv≡44; val-hyp; cascade-deliv-depth-absurd)
open import Refuted.Cascade-Nest-PerDeliv
  using (grown≡48; perDeliv≡35; store-val-hyp; cascade-nest-perDeliv-absurd)
open import Refuted.Chain-Step-Store
  using (before≡9; after≡16; chain-step-store-absurd)
open import Refuted.Chain-Step-Live-Additive
  using (tight≡; cross≡; chain-step-live-additive-absurd)
open import Refuted.Chain-Level-Unbounded
  using (prog; slots; cp; ceil; lvl; arr; pth; widen; fits;
         chain-level-unbounded-absurd)
open import Refuted.Chain-Step-Live-Nest
  using (grown≡3; charge≡1; grown₅≡5; chainStep-nest-live-absurd)
open import Refuted.Chain-Step-Nodes
  using (grown≡22; charge≡15; chainStep-nodes-absurd)
open import Refuted.Share-Sink-Nodes
  using (grown≡3; charge≡1; share-sink-nodes-absurd)
open import Refuted.Apply-Fn-Nest
  using (subbed≡2; oneWrap≡1; applyFn-nest-absurd)
open import Refuted.Eval-Seed-Nest
  using (evald≡3; syntactic≡2; eval-seed-nest-absurd)
open import Refuted.Step-Frame-Nest-Dup
  using (dup≡80; perFrame≡40; stepFrame-nest-dup-absurd)
open import Refuted.Ceil-Unfold-Mu
  using (parked≡6; unfolded≡18; ceil-unfoldμ-absurd;
         parked₂≡6; unfolded₂≡12)
open import Refuted.Thru-Subscribe-Nest
  using (emitted≡80; perValue≡41; stepFrame-nodes-thru-absurd;
         parent≡41; stepFrame-nodes-at-thru-absurd;
         capsZeroThru; capsCharge≡41; stepFrame-nodes-thru-caps-absurd; valCapsFails;
         walkBefore≡41; walkAfter≡80; thruΦ-grantless-absurd)
open import Refuted.Scan-Burst-Nest
  using (premises; burst≡14; delivered≡16383; charged≡12288;
         delivered₁₃≡8191; charged₁₃≡12288; subscribeE-nest-burst-absurd)
open import Refuted.Scan-Arr-Nest
  using (premises; burst≡14; delivered≡; charged≡;
         delivered₁₃≡; charged₁₃≡; closKeys≡; subscribeE-nest-arr-scan-absurd)
open import Refuted.Thru-Scan-Burst-Nest
  using (charged≡8192; charged₁₃≡8192; stepFrame-nodes-thru-burst-absurd)
  renaming (premises to thruBurstPremises;
            burst≡14 to thruBurst≡14;
            delivered≡16383 to thruDelivered≡16383;
            delivered₁₃≡8191 to thruDelivered₁₃≡8191)
open import Refuted.Scan-Fold-Burst
  using (fold≡65; charge≡64; scan-fold-burst-absurd)
open import Refuted.Scan-Phi-Burst
  using (Φ-hyp-burst; scan-Φ-burst-absurd; live-factor; refuted-factor)
open import Refuted.Walk-Phi-Room
  using (walk-fold-room-absurd; room₂₁; size₄; charge₂₁)
open import Refuted.Scan-Nodes-Burst
  using (before≡0; after≡65; budget≡64; stepFrame-nest-nodes-burst-absurd)
open import Refuted.Subscribe-Caps-Nest
  using (capsZero; capsZero₂; delivered≡16; charged≡6;
         delivered₂≡8; charged₂≡6;
         subscribeE-nest-absurd; subscribeE-nest-two-absurd; valCapsFails₃; valCapsFails₂)
open import Refuted.Thru-Fit-Frame-Slot
  using (arrival-nest≡0; store≡0; G≡4; premises; delivered≡;
         delivered₃≡8; thruFit-frame-slot-absurd; len₃≡1; grown₃≡8;
         stepFrame-nodes-thru-slot-absurd; unit₇≡9; parentGrant≡76;
         len₇≡1; grown₇≡128; grown₆≡64; parentGrant₆≡68;
         stepFrame-nodes-slot-absurd; telescope₇≡115; telescope₃≡55;
         parent-premise-absurd; fit-premise-absurd)
open import Refuted.Sight-All-Fit-Slot
  using (okb; G≡16; delivered≡; delivered₆≡64; repaired-holds;
         sight-all-fit-slot-absurd; Gv≡0; sight-thru-val-slot-absurd)
open import Refuted.Sight-All-Stream-Dup
  using (figs≡; sides≡; sight-all-stream-dup-absurd;
         payload≡; emitted≡; sight-all-stream-nest-absurd)
open import Refuted.Shared-Slot-Nest-Arr
  using (arrival≡0; capsPin; contained≡; substituted≡; delivered≡8;
         granted≡5; sharedSlot-nest-arr-absurd; headValPin; packHead≡;
         headGrant≡5; nest-arr-at-slot-absurd; sizes≡)
open import Refuted.Inner-Drain-Share-Nest
  using (delivered≡40; charged≡0; capsPin;
         stepFrame-nodes-inner-share-absurd; unit≡41)
open import Refuted.Inner-Drain-Nest
  using (drained≡80; queued≡40; stepFrame-nodes-inner-absurd;
         parent≡40; stepFrame-nodes-at-inner-absurd;
         drainedΦ≡80; Φ-hyp; stepFrame-nest-Φ-inner-absurd;
         drainedΦ₃≡120; stepFrame-nest-Φ-inner-trip-absurd;
         drained₃≡120; queued₃≡40; unitCharge≡82;
         stepFrame-nodes-inner-unit-absurd)
open import Refuted.Drain-Regs-Nest
  using (before≡0; after≡1; Φ-hyp-drain; stepFrame-nest-regs-drain-absurd)
open import Refuted.Scan-Acc-Nest
  using (drainedΦˢ≡40; Φ-hyp-scan; stepFrame-nest-Φ-scan-absurd;
         drainedΦˢ≡80; stepFrame-nest-Φ-scan-wide-absurd)
open import Refuted.Scan-Seed-Caps
  using (syn≡39; val≡45; capsBefore; valOK; capsAfter; scan-seed-caps-absurd)
open import Refuted.Thru-Step-Nest
  using (burstLen≡1; prems≡; arrival≡6;
         deliveredM≡12; deliveredS≡12; deliveredX≡12;
         thru-step-merge-absurd; thru-step-switch-absurd;
         thru-step-exhaust-absurd)
open import Refuted.Thru-Step-Caps
  using (capsPrems≡; slots≡; after≡false; thru-step-caps-absurd; widths≡)
open import Refuted.Share-Go-Path
  using (grown≡; charge≡; share-go-path-absurd)
open import Refuted.Share-Go-Registry
  using (priced; slots-fixed; grown≡; charge≡; share-go-registry-absurd)
open import Refuted.Share-Go-Stack
  using (priced; reg-priced; slots-fixed; grown≡; charge≡; share-go-stack-absurd)
open import Refuted.Share-Live-Afford
  using (entering≡; produced≡; hU; hR; share-live-afford-absurd)
open import Refuted.Share-Live-Level
  using (frame₁≡; frame₂≡; after₁≡; after₂≡; afford; 1≤S; hV; hR; j≤Lv;
  share-live-level-absurd)
open import Refuted.Sink-Level-Range
  using (reading≡; range≡; len≡; 8≤S; j≤range; legal; sink-level-range-absurd)
open import Refuted.Sink-Phi-Leaf
  using (escalates; deepens; leafFac≡; leafDep≡; legal; handed; 8≤B;
  sink-phi-leaf-absurd)
open import Refuted.Defer-Park-Size
  using (Stmt; prog; defer-park-size-absurd)
open import Refuted.Defer-Park-Width
  using (StmtW; progW; defer-park-width-absurd)
open import Refuted.Subscribe-Burst-Width
  using (Stmt; prems≡; burst-width-absurd; figs≡; keyFig≡;
         StmtWalk; premsP≡; walk-absurd)
open import Refuted.Nest-Size-Currency
  using (valKey; closKey; size-defers; size-from-nest-absurd)
open import Refuted.Nest-Caps-Keys
  using (Stmt; long-len; nest-caps-keys-absurd)
open import Refuted.PushVals-Adm-Map
  using (AdmStmt; WidStmt; prems-map≡; adm-absurd; wid-absurd; figs-map≡;
  AdmStmtZ; WidStmtZ; prems-z≡; adm-absurd-z; wid-absurd-z; regs≡)
open import Refuted.Nest-Cap-Height
  using (fLvlD-depth; d≤dLvl; d≤lvls; d≤sizeCount; suc≤sizeStep; add≤iterSize;
         fuel≤blowup; capsH≤levels; capsH≤size; size<fac; fac≤cap; capsH<inc; inc≤cap; level-step; level-crosses;
         NestCapCapsH; nestCap-3≤capsH-absurd; nestCap-3≤capsH-absurd-inc;
  NestLevelKeyed; nestCap-level-absurd)
open import Refuted.Chain-Step-Flat
  using (cap; row; latched≡true; pre≡true; post≡false; chain-step-flat-absurd)
open import Refuted.Subscribe-Inner-Regs-Base
  using (subscribeInner-regs-base-absurd)
open import Refuted.Step-Frame-Clos using (step-frame-clos-absurd)
open import Refuted.Step-Frame-Clos-Level
  using (StepFrameClosMap; step-frame-clos-map-absurd)
open import Refuted.Drain-Reach-Gas
  using (reached-gas; gasValUp₈; nest₈; room₈; stepSize₈; baseGas₈;
         drain-reach-gas-absurd; drain-reach-gas-base)
open import Refuted.Drain-Queue-Flat
  using (valUp₂; valFlat₂; valUp₄; valFlat₄; valUp₈; valFlat₈;
         closUp₈; closFlat₈; roomUp₈; roomFlat₈;
         flatSizes≡; stepSizes≡;
         drain-spine-flat-absurd; drain-clos-flat-absurd;
         drain-room-flat-absurd)
open import Refuted.Frame-Step-Compose
  using (c₀; FrameStepCompose; frameStep-compose-absurd)
open import Refuted.Frame-Step-Size-Level
  using (StepFrameSz; StepFrameSzFramed; figuresA≡; figuresB≡;
         rowA≡false; rowB≡false; premA; premB; premC;
         stepFrame-sz-absurd; stepFrame-sz-framed-absurd)
open import Refuted.Frame-Step-Size-Store
  using (P; vP; fnS; stS; figures≡; premFrame; premVals; rowS≡false;
         storeReading; stepFrame-sz-store-absurd)
open import Refuted.Frame-Step-Size-Fold
  using (StepFrameSzFold; figuresFold≡; premFrameFold; premStoreFold;
         premValsFold; deliveredFold≡false; stepFrame-sz-fold-absurd)
open import Refuted.Frame-Step-Size-Cross
  using (StepFrameSzOuter; StepFrameSzInner; growth≡; figures₁≡; figures₂≡;
         nodes₁; prem₁; row₁≡false; nodes₂; prem₂; nodesQ; premQ;
         stepFrame-sz-outer-absurd; stepFrame-sz-inner-absurd)
open import Refuted.Frame-Step-Size-Cross-Store
  using (StepFrameSzStoreOuter; StepFrameSzStoreInner; figures≡;
         nodes₀; prem₀; nodesQ; premQ;
         stepFrame-sz-store-outer-absurd; stepFrame-sz-store-inner-absurd)
open import Refuted.Frame-Step-Size-Cross-Count
  using (CrossCountCh; figures≡; prem; count≡; cross-count-ch-absurd)
open import Refuted.Chain-Step-Regs-Cap
  using (ChainStepRegsSz; figures≡; regLens≡; premSz; premPath; premReg;
         row≡false; chain-step-regs-cap-absurd)
open import Refuted.Cascade-Afford-Wide
  using (CascadeAffordWide; suc≤sizeStep; iterSize-lb; selLen; S≤N; hK;
         cascade-afford-wide-absurd)
open import Refuted.Arr-Cap-Step
  using (cA; ArrCapStep; arr-cap-step-absurd; arr-cap-step-wide-absurd)
open import Refuted.Nest-Clos-Flat
  using (syntaxes≡; closures≡; premise; broken; nest-clos-flat-absurd)
open import Refuted.Clos-Wrap-Sum
  using (wrapSum≡; ownNest≡; closRead≡; traded≡; clos-wrap-sum-absurd)
open import Refuted.Nest-Clos-Cap-Free
  using (size≡; clos≡; wid≡; third-lo; third-hi; NestClosCaps; nest-clos-cap-free-absurd)
open import Refuted.Nest-Clos-Stratified
  using (flat-priced; size≡1; lvl≡105; read-fails; staged-rejects; DeferParkClos;
         nest-clos-stratified-absurd)

open import Refuted.Thru-Park-Free
  using (opIterD-strict; ParkOne; park-absurd; ceil-absurd-at)

-- THE CUT AND WRAP FAMILIES ARE CLAIMED HERE AND CONSUMED BY THE PROBE
-- TREE.  A program family is infrastructure rather than a witness, and
-- the probe tree cannot hold it: every file under `probed/` must name a
-- live target, which a family of programs has none of.  So it lives out
-- here, and the claim root says so rather than letting reachability
-- report it as dead weight.
open import Refuted.Demand-Programs
  using (progC; sucGC; sucGW)
open import Refuted.Sight-Fit-Scan using (figs≡; ok₂; scan-fit-absurd)
open import Refuted.Fold-Path-Regs-Len
  using (FoldPathRegsLen; reached; entryVals; entryPath; entryRegs;
         figures; exitRow≡false; fold-path-regs-len-absurd;
         repairFigs; repairFits)
open import Refuted.Drain-Live-Defer
  using (before≡0; after≡3; charge≡1; parkedNest≡0; Φ-hyp-drain;
         stepFrame-nest-live-drain-absurd)
open import Refuted.Cap-Walk-Cross
  using (CapUnderWalk; capExp≡; walkExp≡; walkFac≡; cap-walk-cross-absurd;
         FieldStepFits; field-step-absurd)
open import Refuted.Scan-Phi-Width
  using (ScanΦFits; size≡; nestD≡; depth≡; rootFac≡; legal; unit-ok; premΦ;
         bound; scan-phi-width-absurd;
         ScanΦFitsWide; wide; scan-phi-wide-absurd)
open import Refuted.Fan-Chain-Registry
  using (FanChainSz; FanChainNestD; unit≡; takesLen; admitLong; crosses;
         fan-chain-sz-absurd; FanRegsSz; fan-regsSz-absurd;
         deepNest; nestD≡; admitDeep; fan-chain-nestD-absurd;
         FanRegsNest; fan-regsNest-absurd)
open import Refuted.Reg-Nest-Reached
  using (RegsNestReached; regs-nest-reached-absurd; unit≡4;
         deepest₁≡1; deepest₃≡3; deepest₅≡5; regsLen₅≡5)
open import Refuted.Chains-Burst-Flat
  using (reached; chain≡; prems≡; chains-burst-flat-absurd; widths≡; hops≡)
open import Refuted.Drain-Root-Ceil
  using (InnerUnderRootCeil; emitted₂; emitted₃; ceil₂≡2; ceil₃≡3;
         mapBurst₂≡4; mapBurst₃≡6; drain-root-ceil-absurd)
