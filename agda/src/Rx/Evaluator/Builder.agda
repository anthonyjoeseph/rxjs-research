------------------------------------------------------------------
-- THE BUILDER: THE RUN, CONSTRUCTED RATHER THAN TESTED.
------------------------------------------------------------------

-- WHAT A BUILDER IS.  Every family in `Rx.Evaluator.Domain` is a graph
-- relation, so a member of it is a complete run; this module inhabits
-- the ones the reducibility candidate does not.  The result is not
-- fixed by a machine -- the builder RETURNS the pair, so it CHOOSES
-- which clause ran, and a clause it does not write is a run that does
-- not exist.  That is why no arm here tests a rank and no arm answers
-- a negative case: there is no negative case to answer.
--
-- AND THE SUBSCRIBE CYCLE IS NOT HERE, BECAUSE IT IS ALREADY PROVEN
-- NEXT DOOR.  `Rx.Evaluator.Reducible` builds every subscribe, push,
-- frame step and flattening walk a SUBSCRIPTION reaches, carrying the
-- candidate through each; re-deriving them here would be a second copy
-- of the same induction with the satisfaction column thrown away.
-- What is left for this module is what a subscription never enters:
-- the completion side, the share fan-out, and the arrival spine.
--
-- AND THE ONE THING THAT USED TO BE A LEAF IS NOW A CALL.  A merge's
-- parked lane hands back a value the store kept, and a store keeps
-- values rather than premises -- so the drain used to be short of the
-- candidate that value arrived with.  With a value at observable type
-- being a body paired with an environment, and the claim at an
-- environment's entries being the whole of the claim at the pair, the
-- fundamental theorem at VALUES is total and the drain simply calls
-- it.
--
-- SO THE EVALUATOR IS A PROJECTION.  `evaluate↓` is `proj₁` of
-- `evaluate!`, and a projection computes only as far as the thing
-- projected is a real body.
module Rx.Evaluator.Builder where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; _<_; _∸_; s≤s; _≡ᵇ_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (∸-monoʳ-<)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (refl; cong)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Rx.Prim using (Fuel; Tick)
open import Rx.Exp using (Ty; obs; _≟ᵗ_; Ctx; Closed; Val; []ᵉ)
open import Rx.Mint using (nodeᵏ; freshId; setAt)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Stream; VSegs; Sched; EvalSt; Path; root; share-sink; _↠_;
  Frame; map-f; scan-f; take-f; batchSync-f; from-inner; thru-outer;
  AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ; NodeId; NodeState;
  cell-st; take-st; batchSync-st; mergeAll-st; switch-st; exhaust-st;
  lookupNode; setNode; hasRoom; aliveThroughᶠ;
  Arrival; arrTick; arrTy; arrVal; AtFloor; RegId; chainsOf; cascadeLatch;
  sched-next; sched-init; st-init; shareAdmit; shareDying)
open import Rx.Evaluator.Domain using (subscribeInner⇓; mergeAllDrain⇓; innerFinish⇓; innerReact⇓; stepFrame⇓; foldPath⇓;
  foldVSegs⇓; segs-nil; segs-last; segs-more;
  dispatchShare⇓; shareWalk⇓; shareGo⇓; chainStep⇓; cascadeGo⇓; cascade⇓; drain⇓; evaluate⇓; inner;
  drain-nil; drain-no-room; drain-room; finish-all-drain; finish-switch-clear;
  finish-exhaust-clear; finish-nil; react-false; react-alive; react-dead; step-map; step-scan;
  step-take; step-batchSync; step-from-inner; step-thru-outer; fold-root; fold-sink; fold-step;
  disp; walk-nil; walk-last; walk-more; go-nil; go-cut; go-live; chain-step; casc-nil; casc-cut; casc-live; casc-run;
  drain-done; drain-empty; drain-step; eval-run)
open import Rx.Evaluator.Reducible using (Red; red-val; red-walk; reducible)

------------------------------------------------------------------
-- WHAT EVERY ARRIVING VALUE IS.
------------------------------------------------------------------

-- THE CANDIDATE AT A LIST, WHICH IS THE ONLY THING THE ARRIVAL SIDE
-- EVER ASKS FOR.  A cascade walks values it read out of a schedule and
-- a flattening frame walks observables it read out of a burst; neither
-- carries a premise, and neither needs one, because the claim at a
-- value is re-established from the value itself.
allRed : ∀ {n} {Γ : Ctx n} (u : Ty) (vs : List (Val Γ u)) → All (Red u) vs
allRed u []       = []ᵃ
allRed u (v ∷ vs) = red-val u v ∷ᵃ allRed u vs

------------------------------------------------------------------
-- THE COMPLETION SIDE, WHICH NO SUBSCRIBE REACHES.
------------------------------------------------------------------

-- ONE INNER SUBSCRIPTION, OPENED AT A FRESHLY COUNTED INSTANCE.  The
-- subscribe itself is the candidate at the arriving observable, which
-- quantifies over every schedule and every state -- so the advanced
-- mint this arm builds is one of them by construction and nothing is
-- threaded.
inner! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
         (op : AllOp) (allNid : NodeId) (κ : Path Γ lo s t) (now : Tick)
         (o : Val Γ (obs s)) (sched : Sched Γ) (st : EvalSt e)
       → Σ (NodeId × VSegs Γ s t × Bool × Sched Γ × EvalSt e) λ r →
           subscribeInner⇓ {e = e} op allNid κ now o sched st r
inner! op allNid κ now o sched st =
  let inst = freshId nodeᵏ (Sched.mint sched)
      ((burst , _ , sched′ , st′) , d , _) =
        red-val (obs _) o (from-inner op allNid inst ↠ κ) now
          (record sched { mint = setAt nodeᵏ (suc inst) (Sched.mint sched) }) st
  in _ , inner refl d refl

-- THE PARKED LANE, HANDED BACK ITS QUEUE.  A flattener that could not
-- subscribe when a value arrived kept it; this is the walk that spends
-- the backlog once a lane frees, one carried value at a time.  The
-- recursion peels the popped queue, so nothing here needs a measure.
mergeAllDrain! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
                 (allNid : NodeId) (κ : Path Γ lo s t) (now : Tick)
                 (lim : Maybe ℕ) (act : ℕ) (od : Bool)
                 (q : List (Val Γ (obs s))) (sched : Sched Γ) (st : EvalSt e)
               → Σ (VSegs Γ s t × ℕ × List (Val Γ (obs s)) × Sched Γ × EvalSt e) λ r →
                   mergeAllDrain⇓ {e = e} allNid κ now lim act od q sched st r
mergeAllDrain! allNid κ now lim act od []      sched st = _ , drain-nil
mergeAllDrain! allNid κ now lim act od (o ∷ q) sched st
  with hasRoom lim act in eqr
... | false = _ , drain-no-room eqr
... | true  =
      let ((inst , segs , done , sched₁ , st₁) , s) =
            inner! mergeAllᵒ allNid κ now o sched
              (record st
                 { nodes = setNode allNid (mergeAll-st lim act q od)
                     (EvalSt.nodes st) })
          (_ , d) = mergeAllDrain! allNid κ now lim
                      (if done then act else suc act) od q sched₁ st₁
      in _ , drain-room eqr s d

-- A FIN COMPLETES AN INNER ONLY ONCE NOTHING UNDER ITS EXIT FRAME CAN
-- DELIVER AGAIN, and only a merge's finish subscribes anything -- it
-- drains the queue the lane limit had held back, which is the second
-- place a value becomes a subscription and the one no subscribe
-- reaches.
--
-- EVERY OTHER READING IS THE COLLAPSE, AND IT IS SPELT OUT RATHER THAN
-- CAUGHT, because the fallback carries a side condition and a
-- condition on two variables does not reduce.  One clause per operator
-- per shape the store can be in, each handing back the same `refl`.
innerFinish! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
               (op : AllOp) (allNid inst : NodeId) (κ : Path Γ lo s t)
               (now : Tick) (vals : List (Val Γ s))
               (sched : Sched Γ) (st : EvalSt e) (ns : Maybe (NodeState Γ))
             → Σ (VSegs Γ s t × Bool × Sched Γ × EvalSt e) λ r →
                 innerFinish⇓ {e = e} op allNid inst κ now vals sched st ns r

innerFinish! {s = s} mergeAllᵒ allNid inst κ now vals sched st
             (just (mergeAll-st {w} lim act q od)) with w ≟ᵗ s in eqw
... | no  _    = _ , finish-nil (cong ⌊_⌋ eqw)
... | yes refl =
      let (_ , d) = mergeAllDrain! allNid κ now lim (pred act) od q sched st
      in _ , finish-all-drain d
innerFinish! switchᵒ allNid inst κ now vals sched st
             (just (switch-st (just c) od)) with (c ≡ᵇ inst) in eqc
... | true  = _ , finish-switch-clear eqc
... | false = _ , finish-nil eqc
innerFinish! exhaustᵒ allNid inst κ now vals sched st
             (just (exhaust-st act od)) = _ , finish-exhaust-clear

innerFinish! mergeAllᵒ allNid inst κ now vals sched st nothing = _ , finish-nil refl
innerFinish! mergeAllᵒ allNid inst κ now vals sched st (just (cell-st _)) = _ , finish-nil refl
innerFinish! mergeAllᵒ allNid inst κ now vals sched st (just (take-st _)) = _ , finish-nil refl
innerFinish! mergeAllᵒ allNid inst κ now vals sched st (just (batchSync-st _)) = _ , finish-nil refl
innerFinish! mergeAllᵒ allNid inst κ now vals sched st (just (switch-st _ _)) = _ , finish-nil refl
innerFinish! mergeAllᵒ allNid inst κ now vals sched st (just (exhaust-st _ _)) = _ , finish-nil refl
innerFinish! switchᵒ allNid inst κ now vals sched st nothing = _ , finish-nil refl
innerFinish! switchᵒ allNid inst κ now vals sched st (just (cell-st _)) = _ , finish-nil refl
innerFinish! switchᵒ allNid inst κ now vals sched st (just (take-st _)) = _ , finish-nil refl
innerFinish! switchᵒ allNid inst κ now vals sched st (just (batchSync-st _)) = _ , finish-nil refl
innerFinish! switchᵒ allNid inst κ now vals sched st (just (mergeAll-st _ _ _ _)) = _ , finish-nil refl
innerFinish! switchᵒ allNid inst κ now vals sched st (just (exhaust-st _ _)) = _ , finish-nil refl
innerFinish! switchᵒ allNid inst κ now vals sched st (just (switch-st nothing _)) = _ , finish-nil refl
innerFinish! exhaustᵒ allNid inst κ now vals sched st nothing = _ , finish-nil refl
innerFinish! exhaustᵒ allNid inst κ now vals sched st (just (cell-st _)) = _ , finish-nil refl
innerFinish! exhaustᵒ allNid inst κ now vals sched st (just (take-st _)) = _ , finish-nil refl
innerFinish! exhaustᵒ allNid inst κ now vals sched st (just (batchSync-st _)) = _ , finish-nil refl
innerFinish! exhaustᵒ allNid inst κ now vals sched st (just (mergeAll-st _ _ _ _)) = _ , finish-nil refl
innerFinish! exhaustᵒ allNid inst κ now vals sched st (just (switch-st _ _)) = _ , finish-nil refl

innerReact! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
              (op : AllOp) (allNid inst : NodeId) (κ : Path Γ lo s t)
              (now : Tick) (vals : List (Val Γ s))
              (sched : Sched Γ) (st : EvalSt e) (fin : Bool)
            → Σ (VSegs Γ s t × Bool × Sched Γ × EvalSt e) λ r →
                innerReact⇓ {e = e} op allNid inst κ now vals sched st fin r
innerReact! op allNid inst κ now vals sched st false = _ , react-false
innerReact! op allNid inst κ now vals sched st true
  with any (aliveThroughᶠ inst st) (EvalSt.registry st) in eqa
... | true  = _ , react-alive eqa
... | false =
      let (_ , f) = innerFinish! op allNid inst κ now vals sched st
                      (lookupNode allNid (EvalSt.nodes st))
      in _ , react-dead eqa f

-- THE FRAME STEP OVER EVERY FRAME, WHICH IS THE CANDIDATE'S OWN PLUS
-- THE ONE IT REFUSES.  The arrival spine walks a path it read out of
-- the registry, so it meets `from-inner` and nothing restricts what it
-- meets; a subscribe meets the other five and never this one.  The
-- split is checked rather than asserted -- `srcFrame`'s `()` next door
-- is Agda refusing the frame, not a convention about callers.
stepFrameAny! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
                (now : Tick) (fr : Frame Γ s u) (κ : Path Γ lo u t)
                (vals : List (Val Γ s)) (fin : Bool)
                (sched : Sched Γ) (st : EvalSt e)
              → Σ (VSegs Γ u t × Bool × Sched Γ × EvalSt e) λ r →
                  stepFrame⇓ {e = e} now fr κ vals fin sched st r
stepFrameAny! now (map-f fn)       κ vals fin sched st = _ , step-map
stepFrameAny! now (scan-f fn nid)  κ vals fin sched st = _ , step-scan
stepFrameAny! now (take-f nid)     κ vals fin sched st = _ , step-take
stepFrameAny! now (batchSync-f nid) κ vals fin sched st = _ , step-batchSync
stepFrameAny! now (from-inner op allNid inst) κ vals fin sched st =
  let (_ , r) = innerReact! op allNid inst κ now vals sched st fin
  in _ , step-from-inner r
stepFrameAny! {u = u} now (thru-outer op nid) κ vals fin sched st =
  let (_ , w , _) = red-walk op nid κ now (allRed (obs u) vals) sched st
  in _ , step-thru-outer w

------------------------------------------------------------------
-- THE SHARE FAN-OUT, WHOSE DESCENT IS THE FLOOR.
------------------------------------------------------------------

-- A chain registered on a share sinks STRICTLY above that share, so
-- the room left above the floor is what shrinks at every fan-out and
-- the path itself never has to.
monus-sink : ∀ {n lo} (i : Fin n) → lo ≤ toℕ i → n ∸ suc (toℕ i) < n ∸ lo
monus-sink i below = ∸-monoʳ-< (s≤s below) (toℕ<n i)

mutual

  foldPath! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
              (ac : Acc _<_ (n ∸ lo)) (now : Tick) (κ : Path Γ lo u t)
              (vals : List (Val Γ u)) (fin : Bool)
              (sched : Sched Γ) (st : EvalSt e)
            → Σ (Stream Γ t × Sched Γ × EvalSt e) λ r →
                foldPath⇓ {e = e} now κ vals fin sched st r

  foldVSegs! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
               (ac : Acc _<_ (n ∸ lo)) (now : Tick) (κ : Path Γ lo u t)
               (segs : VSegs Γ u t) (fin : Bool)
               (sched : Sched Γ) (st : EvalSt e)
             → Σ (Stream Γ t × Sched Γ × EvalSt e) λ r →
                 foldVSegs⇓ {e = e} now κ segs fin sched st r

  dispatchShare! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo} {i : Fin n}
                   (ac : Acc _<_ (n ∸ suc (toℕ i))) (below : lo ≤ toℕ i)
                   (now : Tick) (vals : List (Val Γ _)) (fin : Bool)
                   (sched : Sched Γ) (st : EvalSt e)
                 → Σ (Stream Γ t × Sched Γ × EvalSt e) λ r →
                     dispatchShare⇓ {e = e} now i below vals fin sched st r

  shareWalk! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {i : Fin n}
               (ac : Acc _<_ (n ∸ suc (toℕ i))) (now : Tick)
               (vals : List (Val Γ _)) (fin : Bool)
               (sched : Sched Γ) (st : EvalSt e)
             → Σ (Stream Γ t × Sched Γ × EvalSt e) λ r →
                 shareWalk⇓ {e = e} now i vals fin sched st r

  shareGo! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {i : Fin n}
             (ac : Acc _<_ (n ∸ suc (toℕ i))) (now : Tick)
             (v : Val Γ _) (fin : Bool)
             (ps : List (RegId × Path Γ (suc (toℕ i)) _ t))
             (sched : Sched Γ) (st : EvalSt e)
           → Σ (Stream Γ t × Sched Γ × EvalSt e) λ r →
               shareGo⇓ {e = e} now i v fin ps sched st r

  foldPath! ac now root vals fin sched st = _ , fold-root
  foldPath! (acc rec) now (share-sink i below) vals fin sched st =
    let (_ , d) = dispatchShare! (rec (monus-sink i below)) below
                    now vals fin sched st
    in _ , fold-sink d
  foldPath! ac now (fr ↠ κ) vals fin sched st =
    let ((segs , fin′ , sched₁ , st₁) , sf) =
          stepFrameAny! now fr κ vals fin sched st
        (_ , rest) = foldVSegs! ac now κ segs fin′ sched₁ st₁
    in _ , fold-step sf rest

  -- THE MEASURE IS THE PAIR (PATH, SEGMENT LIST), LEXICOGRAPHIC.
  -- `foldPath!` reaches here only at a strictly smaller path, this
  -- reaches `foldPath!` at an equal one, and it reaches itself at an
  -- equal path with a shorter list -- so the accessibility argument
  -- crosses untouched, exactly as the frame clause already passed it.
  foldVSegs! ac now κ [] fin sched st =
    let (_ , f) = foldPath! ac now κ [] fin sched st
    in _ , segs-nil f
  foldVSegs! ac now κ ((vs , rts) ∷ []) fin sched st =
    let (_ , f) = foldPath! ac now κ vs fin sched st
    in _ , segs-last f
  foldVSegs! ac now κ ((vs , rts) ∷ s ∷ ss) fin sched st =
    let ((emits , sched₁ , st₁) , f) = foldPath! ac now κ vs false sched st
        (_ , r) = foldVSegs! ac now κ (s ∷ ss) fin sched₁ st₁
    in _ , segs-more f r

  dispatchShare! {i = i} ac below now vals fin sched st =
    let (_ , w) = shareWalk! ac now vals fin sched (shareDying i fin st)
    in _ , disp w

  shareWalk! ac now [] fin sched st = _ , walk-nil
  shareWalk! {i = i} ac now (v ∷ []) fin sched st =
    let (_ , g) = shareGo! ac now v fin
                    (shareAdmit i (EvalSt.registry st)) sched st
    in _ , walk-last g
  shareWalk! {i = i} ac now (v ∷ w ∷ vs) fin sched₀ st₀ =
    let ((emits , sched₁ , st₁) , g) =
          shareGo! ac now v false
            (shareAdmit i (EvalSt.registry st₀)) sched₀ st₀
        (_ , r) = shareWalk! ac now (w ∷ vs) fin sched₁ st₁
    in _ , walk-more g r

  shareGo! ac now v fin [] sched st = _ , go-nil
  shareGo! {i = i} ac now v fin ((rid , p) ∷ ps) sched st
    with any (_≡ᵇ rid) (EvalSt.cancelled st) in eqc
  ... | true  = let (_ , g) = shareGo! ac now v fin ps sched st
                in _ , go-cut eqc g
  ... | false =
        let ((emits , sched₁ , st₁) , f) =
              foldPath! ac now p (v ∷ []) fin sched
                (record st { delivered = rid ∷ EvalSt.delivered st })
            (_ , g) = shareGo! ac now v fin ps sched₁ st₁
        in _ , go-live eqc f g

------------------------------------------------------------------
-- THE ARRIVAL SPINE.
------------------------------------------------------------------

chainStep! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             (a : Arrival Γ) (c : AtFloor Γ (arrTy a) t)
             (sched : Sched Γ) (st : EvalSt e)
           → Σ (Stream Γ t × Sched Γ × EvalSt e) λ r →
               chainStep⇓ {e = e} a c sched st r
chainStep! {n = n} a (lo , path) sched st =
  let (_ , f) = foldPath! (<-wellFounded (n ∸ lo)) (arrTick a) path
                  (arrVal a ∷ []) (Arrival.isLast a) sched st
  in _ , chain-step f

cascadeGo! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             (a : Arrival Γ) (chains : List (RegId × AtFloor Γ (arrTy a) t))
             (sched : Sched Γ) (st : EvalSt e)
           → Σ (Stream Γ t × Sched Γ × EvalSt e) λ r →
               cascadeGo⇓ {e = e} a chains sched st r
cascadeGo! a []               sched st = _ , casc-nil
cascadeGo! a ((rid , c) ∷ cs) sched st
  with any (_≡ᵇ rid) (EvalSt.cancelled st) in eqc
... | true  = let (_ , g) = cascadeGo! a cs sched st in _ , casc-cut eqc g
... | false =
      let ((emits , sched₁ , st₁) , s) =
            chainStep! a c sched
              (record st { delivered = rid ∷ EvalSt.delivered st })
          (_ , g) = cascadeGo! a cs sched₁ st₁
      in _ , casc-live eqc s g

cascade! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e)
         → Σ (Stream Γ t × Sched Γ × EvalSt e) λ r →
             cascade⇓ {e = e} a sched st r
cascade! a sched st =
  let (_ , g) = cascadeGo! a (chainsOf a st) sched (cascadeLatch a sched st)
  in _ , casc-run g

drain! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
         (fuel : Fuel) (sched : Sched Γ) (st : EvalSt e)
       → Σ (Stream Γ t) λ s → drain⇓ {e = e} fuel sched st s
drain! zero    sched st = _ , drain-done
drain! (suc k) sched st with sched-next sched in eqn
... | inj₁ _            = _ , drain-empty eqn
... | inj₂ (a , sched′) =
      let ((out , sched″ , st′) , c) = cascade! a sched′ st
          (_ , d)                    = drain! k sched″ st′
      in _ , drain-step eqn c d

------------------------------------------------------------------
-- THE TOP LINE.
------------------------------------------------------------------

-- A RUN IS ITS ROOT SUBSCRIBE FOLLOWED BY ITS DRAIN, and the relation
-- says so in one constructor -- so this is the assembly and the two
-- builders are its leaves.
evaluate! : ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ)
          → Σ (Stream Γ t) λ s → evaluate⇓ fuel e ins s
evaluate! {n = n} fuel e ins =
  let ((burst , roots , sched₀ , st₀) , s , _) =
        reducible e []ᵉ tt (root {lo = n}) 0 (sched-init e ins) (st-init e)
      (rest , d) = drain! fuel sched₀ st₀
  in _ , eval-run s d

-- AND THE EVALUATOR IS THE PROJECTION.  Not a new machine -- the same
-- machine reached through the builder rather than through a witness it
-- seeds itself.
evaluate↓ : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
          → Stream Γ t
evaluate↓ fuel e ins = proj₁ (evaluate! fuel e ins)
