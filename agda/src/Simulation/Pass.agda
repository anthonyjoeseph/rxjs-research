------------------------------------------------------------------
-- A CASCADE'S VALUE PASS, ONE PATH CONSTRUCTOR AT A TIME.  A related
-- chain hands its values down two related paths, and the fold reads
-- both derivations together: one `PathRel` constructor's frames per
-- step, the stores kept related, the values each sends rootward
-- related, and the chains the pass has not reached kept paired.
--
-- A STEP'S ARM SEES THE PLAIN FRAME'S STEP AND THE IMPL'S WHOLE FOLD.
-- The impl runs a former's frames where the plain run steps once, so an
-- arm takes the impl fold from the top of that run and hands back what
-- is left of it below the run: the tail the plain path continues on,
-- related again, and the group that reaches it.  The plain fold is the
-- descent; an impl-only lane is the one step that moves the impl alone.
------------------------------------------------------------------
module Simulation.Pass where

open import Data.Bool    using (true; false)
open import Data.Fin     using (Fin; toℕ; _↑ʳ_; _↑ˡ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty   using (⊥-elim)
open import Data.List    using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; ++⁺) renaming (map to pw-map)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Bool.ListAction using (any)
open import Data.Fin.Properties using (toℕ<n; toℕ-↑ˡ; toℕ-↑ʳ; ↑ʳ-injective) renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe   using (nothing; just)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Nullary using (yes; no)
open import Data.Nat     using (suc; _≤_)
open import Data.Nat.Properties using (≤-refl; n<1+n)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂; [_,_])
open import Data.Vec     using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Rx.Exp       using (Ctx; Closed; Val; Ty; _≟ᵗ_; uniqᵗ; unitᵗ; _×ᵗ_; _+ᵗ_; obs; listᵗ; applyClo; varᵗ; unit̂; pairᵗ; inlᵗ;
  inrᵗ)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Arrival; arrVal; arrTy; arrTick; arrSource; skipᵇ; cascadeClose; shareSpend; shareDying;
  memberSource; Path; share-sink; _↠[_]_; map-f; batchSync-f; thru-outer; from-inner;
  mergeAllᵒ; lookupNode; mergeAll-st; echoᵗ; thruEvents; thruWrap; RegId; RegRow; AtFloor;
  atDyn; atSlot; chainsOf; aliveThroughᶠ; batchSync-st; batchVals; setNode)
open import Rx.Evaluator.Domain using (foldPath⇓; fold-step; stepFrame⇓; step-map; step-thru-outer; step-from-inner; react-false;
  react-alive; react-dead; innerFinish⇓; thruWalk⇓; chainStep⇓; cascadeGo⇓; casc-nil; casc-cut;
  casc-live; shareGo⇓; go-nil; go-cut; go-live; dispatchShare⇓; step-batchSync; fold-sink; disp; walk-nil;
  chain-step)
open import SExp.Syntax  using (Kinds; plainᵏ; plainᵗ; emitᵗ; hotᵏ)
open import SExp.Elaborate using (inputStampᵖ)
open import Simulation.Stores using (srcCount; SrcPair; Src; PathRel; InputBlock; block; hotEq; RowRel; cold~; defer~; []; _∷_;
  partner-row; Store)
open import Simulation.After using (module Kept; readᴵ; skip-cut)
open import Simulation.Take using (module Takes)
open import Simulation.Scan using (module Scans)
open import Simulation.Arm using (Clear; unthru; adv; Out; out-++; out-quiet; quiet-fold; NoBatch; rel-unbatched)
open import Rx.Mint using (counter; sourceᵏ)
open import SExp.InstEmit using (instEmitᵗ)
open import Simulation.Sweep using (t≢f)
open import Simulation.Schedules using (HeadOf)
open import Rx.Evaluator.Reducible.Support using (Sound; drop-ot; sub-ot; Agree)
open import Rx.Evaluator.Reducible.Rule-Kept using (step-kept; fold-kept)
open import Simulation.Pass.Path using (module PassP)
open import Simulation.Walk using (walker)
open import Simulation.Pass.Quiet using (SlotPair; delivered; slotpair; unchain)

-- AN OPEN BRACKET FLUSHES WHAT IT IS HANDED, each value its own group,
-- and rewrites its own node as it was
batch-flush : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {lo s now nid} {p : Path Δ lo (s ×ᵗ listᵗ s) u}
                {vals fin sched} {st : EvalSt e} {r}
            → stepFrame⇓ now (batchSync-f nid) p vals fin sched st r
            → lookupNode nid (EvalSt.nodes st) ≡ just (batchSync-st {s = s} false [] false)
            → r ≡ ([] , batchVals false vals , fin , sched
                  , record st { nodes = setNode nid (batchSync-st {s = s} false [] false) (EvalSt.nodes st) })
batch-flush {s = s} {nid = nid} {st = st} step-batchSync e with lookupNode nid (EvalSt.nodes st) | e
... | _ | refl with s ≟ᵗ s
...   | yes refl = refl
...   | no ne    = ⊥-elim (ne refl)

sink-at : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {ℓ now} {k : Fin m} {h : ℓ ≤ toℕ k} {w} (eq : lookup Δ k ≡ w) {fin sched st r}
        → foldPath⇓ {e = e} now (subst (λ w → Path Δ ℓ w u) eq (share-sink k h)) [] fin sched st r
        → dispatchShare⇓ now k h [] fin sched st r
sink-at refl (fold-sink d) = d

-- the share handed nothing, and no end, does nothing
disp-quiet : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {ℓ now} {k : Fin m} {h : ℓ ≤ toℕ k} {sched st r}
           → dispatchShare⇓ {e = e} now k h [] false sched st r → r ≡ ([] , sched , st)
disp-quiet (disp walk-nil) = refl

-- a merge's wrap with no end hands its tail none, which sends nothing
quiet-wrap : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ (instEmitᵗ uniqᵗ t)} {ℓ u} {q : Path Δ ℓ u (instEmitᵗ uniqᵗ t)}
               {now r} op nid {f} sW stW
           → f ≡ false → NoBatch q
           → foldPath⇓ {e = e} now q [] (proj₁ (thruWrap op nid f (sW , stW)))
               (proj₁ (proj₂ (thruWrap op nid f (sW , stW)))) (proj₂ (proj₂ (thruWrap op nid f (sW , stW)))) r
           → readᴵ (proj₁ r) ≡ []
quiet-wrap _ _ _ _ refl b d = proj₁ (quiet-fold b d)

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  open PassP {Γ = Γ} κ public
  open Takes {Γ = Γ} κ using (module While)
  open Scans {Γ = Γ} κ using (module Cells)

  module _ {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

    open InP {t} {ep} {ei} public
    open Kept {Γ = Γ} κ {t} {ep} {ei}
    open While {t} {ep} {ei} using (takeWhile-arm)
    open Cells {t} {ep} {ei} using (scan-arm)

    -- THE TWO ROWS A MINTED SOURCE'S CHAINS CAN BE, each a walk and an
    -- end.  A cold read's impl chain runs its input block alone into a
    -- merge whose walk folds the path its partner runs; a deferred hop's
    -- walks the hop's merge on both sides.
    postulate
      -- A COLD READ'S BLOCK WALKED WITH ITS INNER OPEN: the impl's merge
      -- hands the marked values on untouched, and its merge's walk folds
      -- the tail over what the plain path folds the group into
      --
      -- EVERY EMIT IT SENDS STANDS AT THE COUNTER THE CHAIN ENTERED WITH:
      -- the merge's subscribe of the stamp draws that instant in the
      -- stamp's `mintᵉ`, nothing before it draws, and the tail carries it.
      -- Below the block every emit's instant is copied (`mapStepᵖ`'s
      -- reassemble, a scan's and a cutter's alike), or restamped by
      -- `flatStepᵛ` with the last instant the flattener put out, which the
      -- echo leaving ahead of its lane has just set; a subscribe burst
      -- inside a cascade is subscribe-kind throughout.
      --
      -- A LANE'S END IS ITSELF AN EMIT THROUGH THE FLATTENER, so a bounded
      -- merge's queued inner, drained when a lane ends, meets a cell this
      -- arrival has already set.  Read off the bug cache's rows "a bounded
      -- merge's lane cut valueless by a takeWhile, then drained", hot and
      -- cold, whose `sides` print the drained burst at the cut's instant.
      -- PROBED: make qc-store QC='52 150 3' QC_BUDGET=900 QC_DRAW='{"exp":[2,2,1,1,1,1,2,1,0,0,0,0,1],"leaf":[3,0,1],"slot":[2,0,1,1],"script":[0,0,1,1,1]}'
      --   decided by `CLI.Store-Check`'s `store?`: 150 agree, 0 fail.
      --   Case 71 merges a cold read with a switch whose first cold read it
      --   switched past at subscribe, so one script's arrivals and end walk
      --   an open block and a dead one.
      block-open : ∀ {sP stP sI stI} (S : St sP stP sI stI) {src src′ s} {vs : List (Val Γ s)} {vs′ : List (Val (plainᵏ Γ κ) (plainᵗ s))}
                 → Head src src′ {s} {plainᵗ s} vs vs′ → SrcPair κ (Sched.live sP) (Sched.live sI) src src′ s (plainᵗ s)
                 → ∀ {lo ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ m1 j1 b m2 Θ₀ ρ₀ Θ₃ fr ρ₃ Θ₄ ρ₄}
                     {h₁ : lo ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                     {p : Path Γ ℓ s t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ s) (emitᵗ t)}
                 → InputBlock κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (plainᵗ s) (map-f (Θ₀ , inrᵗ (varᵗ (here refl)) , ρ₀) ↠[ h₁ ] (from-inner mergeAllᵒ m1 j1 ↠[ h₂ ] (batchSync-f b ↠[ h₃ ] (map-f (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃) ↠[ h₄ ] (map-f (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄) ↠[ h₅ ] (thru-outer mergeAllᵒ m2 ↠[ h₆ ] q)))))) q
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                 → Sound p sP stP → Sound (map-f (Θ₀ , inrᵗ (varᵗ (here refl)) , ρ₀) ↠[ h₁ ] (from-inner mergeAllᵒ m1 j1 ↠[ h₂ ] (batchSync-f b ↠[ h₃ ] (map-f (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃) ↠[ h₄ ] (map-f (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄) ↠[ h₅ ] (thru-outer mergeAllᵒ m2 ↠[ h₆ ] q)))))) sI stI
                 → ∀ {now rP o₂ v₂ f₂ s₂ st₂ oW sW stW}
                 → foldPath⇓ now p vs false sP stP rP
                 → stepFrame⇓ now (batchSync-f b) (map-f (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃) ↠[ h₄ ] (map-f (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄) ↠[ h₅ ] (thru-outer mergeAllᵒ m2 ↠[ h₆ ] q))) (map (applyClo {s = plainᵗ s} {t = unitᵗ +ᵗ plainᵗ s} (Θ₀ , inrᵗ (varᵗ (here refl)) , ρ₀)) vs′) false sI stI (o₂ , v₂ , f₂ , s₂ , st₂)
                 → thruWalk⇓ mergeAllᵒ m2 q now
                     (thruEvents (map (applyClo {s = obs (emitᵗ s)} {t = echoᵗ (emitᵗ s)} (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄))
                                   (map (applyClo {s = (unitᵗ +ᵗ plainᵗ s) ×ᵗ listᵗ (unitᵗ +ᵗ plainᵗ s)} {t = obs (emitᵗ s)} (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃)) v₂)))
                     s₂ st₂ (oW , sW , stW)
                 → After S rP (o₂ ++ oW , sW , stW) × Out (counter (Sched.mint sI) sourceᵏ) (o₂ ++ oW)
      -- the same at the plain end, the impl's inner still registered
      -- PROBED: make qc-store QC='52 150 3' QC_BUDGET=900 QC_DRAW='{"exp":[2,2,1,1,1,1,2,1,0,0,0,0,1],"leaf":[3,0,1],"slot":[2,0,1,1],"script":[0,0,1,1,1]}'
      --   decided by `CLI.Store-Check`'s `store?`: 150 agree, 0 fail.
      --   Case 71 merges a cold read with a switch whose first cold read it
      --   switched past at subscribe, so one script's arrivals and end walk
      --   an open block and a dead one.
      block-alive : ∀ {sP stP sI stI} (S : St sP stP sI stI) {src src′ s} {vs : List (Val Γ s)} {vs′ : List (Val (plainᵏ Γ κ) (plainᵗ s))}
                 → Head src src′ {s} {plainᵗ s} vs vs′ → SrcPair κ (Sched.live sP) (Sched.live sI) src src′ s (plainᵗ s)
                 → ∀ {lo ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ m1 j1 b m2 Θ₀ ρ₀ Θ₃ fr ρ₃ Θ₄ ρ₄}
                     {h₁ : lo ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                     {p : Path Γ ℓ s t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ s) (emitᵗ t)}
                 → InputBlock κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (plainᵗ s) (map-f (Θ₀ , inrᵗ (varᵗ (here refl)) , ρ₀) ↠[ h₁ ] (from-inner mergeAllᵒ m1 j1 ↠[ h₂ ] (batchSync-f b ↠[ h₃ ] (map-f (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃) ↠[ h₄ ] (map-f (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄) ↠[ h₅ ] (thru-outer mergeAllᵒ m2 ↠[ h₆ ] q)))))) q
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                 → Sound p sP stP → Sound (map-f (Θ₀ , inrᵗ (varᵗ (here refl)) , ρ₀) ↠[ h₁ ] (from-inner mergeAllᵒ m1 j1 ↠[ h₂ ] (batchSync-f b ↠[ h₃ ] (map-f (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃) ↠[ h₄ ] (map-f (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄) ↠[ h₅ ] (thru-outer mergeAllᵒ m2 ↠[ h₆ ] q)))))) sI stI
                 → ∀ {now rP o₂ v₂ f₂ s₂ st₂ oW sW stW}
                 → foldPath⇓ now p vs true sP stP rP
                 → any (aliveThroughᶠ j1 stI) (EvalSt.registry stI) ≡ true
                 → stepFrame⇓ now (batchSync-f b) (map-f (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃) ↠[ h₄ ] (map-f (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄) ↠[ h₅ ] (thru-outer mergeAllᵒ m2 ↠[ h₆ ] q))) (map (applyClo {s = plainᵗ s} {t = unitᵗ +ᵗ plainᵗ s} (Θ₀ , inrᵗ (varᵗ (here refl)) , ρ₀)) vs′) false sI stI (o₂ , v₂ , f₂ , s₂ , st₂)
                 → thruWalk⇓ mergeAllᵒ m2 q now
                     (thruEvents (map (applyClo {s = obs (emitᵗ s)} {t = echoᵗ (emitᵗ s)} (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄))
                                   (map (applyClo {s = (unitᵗ +ᵗ plainᵗ s) ×ᵗ listᵗ (unitᵗ +ᵗ plainᵗ s)} {t = obs (emitᵗ s)} (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃)) v₂)))
                     s₂ st₂ (oW , sW , stW)
                 → After S rP (o₂ ++ oW , sW , stW)
      -- AND WITH ITS INNER DEAD: the impl's merge finishes the inner at the
      -- end, and what the finish hands on is walked the same way
      -- PROBED: make qc-store QC='52 150 3' QC_BUDGET=900 QC_DRAW='{"exp":[2,2,1,1,1,1,2,1,0,0,0,0,1],"leaf":[3,0,1],"slot":[2,0,1,1],"script":[0,0,1,1,1]}'
      --   decided by `CLI.Store-Check`'s `store?`: 150 agree, 0 fail.
      --   Case 71 merges a cold read with a switch whose first cold read it
      --   switched past at subscribe, so one script's arrivals and end walk
      --   an open block and a dead one.
      block-dead : ∀ {sP stP sI stI} (S : St sP stP sI stI) {src src′ s} {vs : List (Val Γ s)} {vs′ : List (Val (plainᵏ Γ κ) (plainᵗ s))}
                 → Head src src′ {s} {plainᵗ s} vs vs′ → SrcPair κ (Sched.live sP) (Sched.live sI) src src′ s (plainᵗ s)
                 → ∀ {lo ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ m1 j1 b m2 Θ₀ ρ₀ Θ₃ fr ρ₃ Θ₄ ρ₄}
                     {h₁ : lo ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                     {p : Path Γ ℓ s t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ s) (emitᵗ t)}
                 → InputBlock κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (plainᵗ s) (map-f (Θ₀ , inrᵗ (varᵗ (here refl)) , ρ₀) ↠[ h₁ ] (from-inner mergeAllᵒ m1 j1 ↠[ h₂ ] (batchSync-f b ↠[ h₃ ] (map-f (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃) ↠[ h₄ ] (map-f (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄) ↠[ h₅ ] (thru-outer mergeAllᵒ m2 ↠[ h₆ ] q)))))) q
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                 → Sound p sP stP → Sound (map-f (Θ₀ , inrᵗ (varᵗ (here refl)) , ρ₀) ↠[ h₁ ] (from-inner mergeAllᵒ m1 j1 ↠[ h₂ ] (batchSync-f b ↠[ h₃ ] (map-f (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃) ↠[ h₄ ] (map-f (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄) ↠[ h₅ ] (thru-outer mergeAllᵒ m2 ↠[ h₆ ] q)))))) sI stI
                 → ∀ {now rP o₁ v₁ f₁ s₁ st₁ o₂ v₂ f₂ s₂ st₂ oW sW stW}
                 → foldPath⇓ now p vs true sP stP rP
                 → any (aliveThroughᶠ j1 stI) (EvalSt.registry stI) ≡ false
                 → innerFinish⇓ mergeAllᵒ m1 j1 (batchSync-f b ↠[ h₃ ] (map-f (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃) ↠[ h₄ ] (map-f (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄) ↠[ h₅ ] (thru-outer mergeAllᵒ m2 ↠[ h₆ ] q)))) now (map (applyClo {s = plainᵗ s} {t = unitᵗ +ᵗ plainᵗ s} (Θ₀ , inrᵗ (varᵗ (here refl)) , ρ₀)) vs′) sI stI
                     (lookupNode m1 (EvalSt.nodes stI)) (o₁ , v₁ , f₁ , s₁ , st₁)
                 → stepFrame⇓ now (batchSync-f b) (map-f (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃) ↠[ h₄ ] (map-f (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄) ↠[ h₅ ] (thru-outer mergeAllᵒ m2 ↠[ h₆ ] q))) v₁ f₁ s₁ st₁ (o₂ , v₂ , f₂ , s₂ , st₂)
                 → thruWalk⇓ mergeAllᵒ m2 q now
                     (thruEvents (map (applyClo {s = obs (emitᵗ s)} {t = echoᵗ (emitᵗ s)} (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄))
                                   (map (applyClo {s = (unitᵗ +ᵗ plainᵗ s) ×ᵗ listᵗ (unitᵗ +ᵗ plainᵗ s)} {t = obs (emitᵗ s)} (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃)) v₂)))
                     s₂ st₂ (oW , sW , stW)
                 → After S rP (o₁ ++ (o₂ ++ oW) , sW , stW)
      -- THE BLOCK'S END: the merge wraps up and the impl's tail folds what
      -- the wrap hands on, the plain path having ended already
      -- PROBED: make qc-store QC='52 150 3' QC_BUDGET=900 QC_DRAW='{"exp":[2,2,1,1,1,1,2,1,0,0,0,0,1],"leaf":[3,0,1],"slot":[2,0,1,1],"script":[0,0,1,1,1]}'
      --   decided by `CLI.Store-Check`'s `store?`: 150 agree, 0 fail.
      --   Case 71's script ends through an open block and a dead one.
      block-end  : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now m2 ℓ s} {q : Path (plainᵏ Γ κ) ℓ (emitᵗ s) (emitᵗ t)}
                     {rP o₁ o₂ oW sW stW fin r}
                 → After S rP (o₁ ++ (o₂ ++ oW) , sW , stW)
                 → Sound q (proj₁ (proj₂ (thruWrap mergeAllᵒ m2 fin (sW , stW)))) (proj₂ (proj₂ (thruWrap mergeAllᵒ m2 fin (sW , stW))))
                 → foldPath⇓ now q [] (proj₁ (thruWrap mergeAllᵒ m2 fin (sW , stW)))
                     (proj₁ (proj₂ (thruWrap mergeAllᵒ m2 fin (sW , stW)))) (proj₂ (proj₂ (thruWrap mergeAllᵒ m2 fin (sW , stW)))) r
                 → After S rP (o₁ ++ (o₂ ++ (oW ++ proj₁ r)) , proj₂ r)
      -- A DEFERRED HOP'S WALK OVER ITS ONE POPPED VALUE: the body the emit
      -- carries is subscribed through the hop's merge on both sides, the
      -- tails staying related
      --
      -- EVERY EMIT IT SENDS STANDS AT THE HOP'S TOKEN, the counter the
      -- chain entered with: what leaves `deferBodyᵖ`'s restamp map is at
      -- the token, a subscribe burst restamped there and the begin marker
      -- minted there, and the merge's inner frame and tail carry it.
      --
      -- `make qc-same-clock` with a defer in every program decides this
      -- body's instants on each hop arrival: seed 27 at depth 3, fuel 12, μ
      -- off, 74 agree and 26 undecided; seed 26 with μ on agreed on 42
      -- before a μ ran the binary out of memory.  The bug-cache rows "a
      -- deferred read of a cold with a synchronous value", "… of a share
      -- its hop connects, over a cold" and "a deferred cold read merged
      -- beside a read of the share it feeds" print each body's synchronous
      -- burst, a share's connect included, at the hop's own instant.
      --
      -- DEAD ROUTE: split at `deferBodyᵖ`'s restamp, the body's subscribe
      --   owing subscribe-kind or token-stamped emits to a tail that keeps a
      --   token-stamped delivery at the token.  The tail folds at every state
      --   the body's subscribe reaches, so its claim quantifies them: over
      --   `Sound` states it is false at a planted queue (a drained inner
      --   minting its own token) or a lowered batch buffer, and over
      --   `Storeʳ`-related ones it needs the stores the values walk's `After`
      --   hands out between folds, which an impl-only chain does not hold.
      hop-one   : ∀ {sP stP sI stI} (S : St sP stP sI stI) {src src′ u} {v : Val Γ (echoᵗ u)} {v′ : Val (plainᵏ Γ κ) (echoᵗ (emitᵗ u))}
                → ∀ {l l′ a a′} → Src κ l l′ → HeadOf l a → HeadOf l′ a′ → Arrival.source a ≡ src → Arrival.source a′ ≡ src′
                → _≡_ {A = Σ Ty (Val Γ)} (arrTy a , arrVal a) (echoᵗ u , v)
                → _≡_ {A = Σ Ty (Val (plainᵏ Γ κ))} (arrTy a′ , arrVal a′) (echoᵗ (emitᵗ u) , v′)
                → SrcPair κ (Sched.live sP) (Sched.live sI) src src′ (echoᵗ u) (echoᵗ (emitᵗ u))
                → ∀ {nid nid′} → (nid , nid′ ∷ []) ∈ Store.π S
                → lookupNode nid (EvalSt.nodes stP) ≡ just (mergeAll-st {t = u} nothing 0 [] false)
                → lookupNode nid′ (EvalSt.nodes stI) ≡ just (mergeAll-st {t = emitᵗ u} nothing 0 [] false)
                → ∀ {ℓ ℓ′} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)}
                → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                → Clear nid′ q sI stI
                → ∀ {now rP rI}
                → thruWalk⇓ mergeAllᵒ nid p now (thruEvents (v ∷ [])) sP stP rP
                → thruWalk⇓ mergeAllᵒ nid′ q now (thruEvents (v′ ∷ [])) sI stI rI
                → Σ (After S rP rI) λ A
                    → PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
                    × Out (counter (Sched.mint sI) sourceᵏ) (proj₁ rI)
      -- THE HOP'S END: the hop's merge wraps up on both sides and the
      -- impl's tail folds what its wrap hands on
      hop-end   : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now nid nid′ ℓ ℓ′ u}
                    {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)} {oP sP′ stP′ oI sI′ stI′ fin r}
                → (A : After S (oP , sP′ , stP′) (oI , sI′ , stI′))
                → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP′) (EvalSt.nodes stI′) p q
                → Sound q (proj₁ (proj₂ (thruWrap mergeAllᵒ nid′ fin (sI′ , stI′)))) (proj₂ (proj₂ (thruWrap mergeAllᵒ nid′ fin (sI′ , stI′))))
                → foldPath⇓ now q [] (proj₁ (thruWrap mergeAllᵒ nid′ fin (sI′ , stI′)))
                    (proj₁ (proj₂ (thruWrap mergeAllᵒ nid′ fin (sI′ , stI′)))) (proj₂ (proj₂ (thruWrap mergeAllᵒ nid′ fin (sI′ , stI′)))) r
                → Arm S now oP (proj₁ (proj₂ (thruWrap mergeAllᵒ nid fin (sP′ , stP′)))) (proj₂ (proj₂ (thruWrap mergeAllᵒ nid fin (sP′ , stP′))))
                    p [] (proj₁ (thruWrap mergeAllᵒ nid fin (sP′ , stP′))) none Never (oI ++ proj₁ r , proj₂ r)


    -- A COLD READ'S BLOCK WALKED: the impl alone runs the inner, the
    -- bracket and the stamp, by how its merge reacts to the group
    block-walk : ∀ {sP stP sI stI} (S : St sP stP sI stI) {src src′ s} {vs : List (Val Γ s)} {vs′ : List (Val (plainᵏ Γ κ) (plainᵗ s))}
               → Head src src′ {s} {plainᵗ s} vs vs′ → SrcPair κ (Sched.live sP) (Sched.live sI) src src′ s (plainᵗ s)
               → ∀ {lo ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ m1 j1 b m2 Θ₀ ρ₀ Θ₃ fr ρ₃ Θ₄ ρ₄}
                   {h₁ : lo ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                   {p : Path Γ ℓ s t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ s) (emitᵗ t)}
               → InputBlock κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (plainᵗ s) (map-f (Θ₀ , inrᵗ (varᵗ (here refl)) , ρ₀) ↠[ h₁ ] (from-inner mergeAllᵒ m1 j1 ↠[ h₂ ] (batchSync-f b ↠[ h₃ ] (map-f (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃) ↠[ h₄ ] (map-f (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄) ↠[ h₅ ] (thru-outer mergeAllᵒ m2 ↠[ h₆ ] q)))))) q
               → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
               → Sound p sP stP → Sound (map-f (Θ₀ , inrᵗ (varᵗ (here refl)) , ρ₀) ↠[ h₁ ] (from-inner mergeAllᵒ m1 j1 ↠[ h₂ ] (batchSync-f b ↠[ h₃ ] (map-f (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃) ↠[ h₄ ] (map-f (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄) ↠[ h₅ ] (thru-outer mergeAllᵒ m2 ↠[ h₆ ] q)))))) sI stI
               → lookupNode b (EvalSt.nodes stI) ≡ just (batchSync-st {s = unitᵗ +ᵗ plainᵗ s} false [] false)
               → ∀ {now fin rP o₁ v₁ f₁ s₁ st₁ o₂ v₂ f₂ s₂ st₂ oW sW stW}
               → foldPath⇓ now p vs fin sP stP rP
               → stepFrame⇓ now (from-inner mergeAllᵒ m1 j1) (batchSync-f b ↠[ h₃ ] (map-f (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃) ↠[ h₄ ] (map-f (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄) ↠[ h₅ ] (thru-outer mergeAllᵒ m2 ↠[ h₆ ] q)))) (map (applyClo {s = plainᵗ s} {t = unitᵗ +ᵗ plainᵗ s} (Θ₀ , inrᵗ (varᵗ (here refl)) , ρ₀)) vs′)
                   fin sI stI (o₁ , v₁ , f₁ , s₁ , st₁)
               → stepFrame⇓ now (batchSync-f b) (map-f (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃) ↠[ h₄ ] (map-f (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄) ↠[ h₅ ] (thru-outer mergeAllᵒ m2 ↠[ h₆ ] q))) v₁ f₁ s₁ st₁ (o₂ , v₂ , f₂ , s₂ , st₂)
               → thruWalk⇓ mergeAllᵒ m2 q now
                   (thruEvents (map (applyClo {s = obs (emitᵗ s)} {t = echoᵗ (emitᵗ s)} (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄))
                                 (map (applyClo {s = (unitᵗ +ᵗ plainᵗ s) ×ᵗ listᵗ (unitᵗ +ᵗ plainᵗ s)} {t = obs (emitᵗ s)} (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃)) v₂)))
                   s₂ st₂ (oW , sW , stW)
               → After S rP (o₁ ++ (o₂ ++ oW) , sW , stW)
               × (fin ≡ false → Out (counter (Sched.mint sI) sourceᵏ) (o₁ ++ (o₂ ++ oW)) × f₂ ≡ false)
    block-walk S hd sp ib r soP si eb dP (step-from-inner react-false) d₂ W =
      proj₁ X , λ _ → proj₂ X , cong (λ z → proj₁ (proj₂ (proj₂ z))) (batch-flush d₂ eb)
      where X = block-open S hd sp ib r soP si dP d₂ W
    block-walk S hd sp ib r soP si _ dP (step-from-inner (react-alive al)) d₂ W = block-alive S hd sp ib r soP si dP al d₂ W , λ ()
    block-walk S hd sp ib r soP si _ dP (step-from-inner (react-dead dd F)) d₂ W = block-dead S hd sp ib r soP si dP dd F d₂ W , λ ()

    -- a cold read's input block: the impl walks it alone into its
    -- merge, whose walk folds the tail, then ends it
    block-arm : ∀ {sP stP sI stI} (S : St sP stP sI stI) {src src′ s} {vs : List (Val Γ s)} {vs′ : List (Val (plainᵏ Γ κ) (plainᵗ s))}
              → Head src src′ {s} {plainᵗ s} vs vs′ → SrcPair κ (Sched.live sP) (Sched.live sI) src src′ s (plainᵗ s)
              → ∀ {lo′ ℓ ℓ′} {p : Path Γ ℓ s t} {full : Path (plainᵏ Γ κ) lo′ (plainᵗ s) (emitᵗ t)}
                  {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ s) (emitᵗ t)}
              → InputBlock κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (plainᵗ s) full q
              → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
              → Sound p sP stP → Sound full sI stI
              → ∀ {now fin rP rI} → foldPath⇓ now p vs fin sP stP rP → foldPath⇓ now full vs′ fin sI stI rI
              → After S rP rI × (fin ≡ false → Out (counter (Sched.mint sI) sourceᵏ) (proj₁ rI))
    block-arm S hd sp blk@(block {m2 = m2} _ _ eb _ _ _ _ _) r soP si dP
              (fold-step step-map (fold-step {out₁ = o₁} d₁ (fold-step {out₁ = o₂} {fin′ = f₂} d₂ (fold-step step-map (fold-step step-map
                (fold-step {out₁ = oW} {out₂ = oR} dW@(step-thru-outer {sched′ = sW} {st′ = stW} W) dR)))))) =
      let s₁ = drop-ot _ _ _ (step-kept _ d₁ (drop-ot _ _ _ si))
          s₃ = drop-ot _ _ _ (drop-ot _ _ _ (drop-ot _ _ _ (step-kept _ d₂ s₁)))
          X  = block-walk S hd sp blk r soP si eb dP d₁ d₂ W
      in block-end {m2 = m2} {o₁ = o₁} {o₂ = o₂} {oW = oW} {fin = f₂} (proj₁ X) (drop-ot _ _ _ (step-kept _ dW s₃)) dR ,
         λ e → subst (Out _) (trans (++-assoc o₁ (o₂ ++ oW) oR) (cong (o₁ ++_) (++-assoc o₂ oW oR)))
                 (out-++ (o₁ ++ (o₂ ++ oW)) oR (proj₁ (proj₂ X e)) (out-quiet oR (quiet-wrap mergeAllᵒ m2 sW stW (proj₂ (proj₂ X e)) (rel-unbatched r) dR)))

    -- A DEFERRED HOP'S WALK: the body each emit carries is subscribed
    -- through the hop's merge on both sides, the tails staying related.
    -- A source with nothing popped walks nothing
    hop-walk  : ∀ {sP stP sI stI} (S : St sP stP sI stI) {src src′ u} {vs : List (Val Γ (echoᵗ u))} {vs′ : List (Val (plainᵏ Γ κ) (echoᵗ (emitᵗ u)))}
              → Head src src′ {echoᵗ u} {echoᵗ (emitᵗ u)} vs vs′ → SrcPair κ (Sched.live sP) (Sched.live sI) src src′ (echoᵗ u) (echoᵗ (emitᵗ u))
              → ∀ {nid nid′} → (nid , nid′ ∷ []) ∈ Store.π S
              → lookupNode nid (EvalSt.nodes stP) ≡ just (mergeAll-st {t = u} nothing 0 [] false)
              → lookupNode nid′ (EvalSt.nodes stI) ≡ just (mergeAll-st {t = emitᵗ u} nothing 0 [] false)
              → ∀ {ℓ ℓ′} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)}
              → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
              → Clear nid′ q sI stI
              → ∀ {now rP rI}
              → thruWalk⇓ mergeAllᵒ nid p now (thruEvents vs) sP stP rP
              → thruWalk⇓ mergeAllᵒ nid′ q now (thruEvents vs′) sI stI rI
              → Σ (After S rP rI) λ A
                  → PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
                  × Out (counter (Sched.mint sI) sourceᵏ) (proj₁ rI)
    hop-walk S nohead sp k nP nI r cl walk-nil walk-nil = after S (λ x → x) (λ x → x) [] (λ x → x) , r , []
    hop-walk S (head s h h′ e e′) sp k nP nI r cl W W′ = hop-one S s h h′ e e′ refl refl sp k nP nI r cl W W′

    -- a deferred hop subscribes its body on both sides
    hop-arm   : ∀ {sP stP sI stI} (S : St sP stP sI stI) {src src′ u} {vs : List (Val Γ (echoᵗ u))} {vs′ : List (Val (plainᵏ Γ κ) (echoᵗ (emitᵗ u)))}
              → Head src src′ {echoᵗ u} {echoᵗ (emitᵗ u)} vs vs′ → SrcPair κ (Sched.live sP) (Sched.live sI) src src′ (echoᵗ u) (echoᵗ (emitᵗ u))
              → ∀ {nid nid′} → (nid , nid′ ∷ []) ∈ Store.π S
              → lookupNode nid (EvalSt.nodes stP) ≡ just (mergeAll-st {t = u} nothing 0 [] false)
              → lookupNode nid′ (EvalSt.nodes stI) ≡ just (mergeAll-st {t = emitᵗ u} nothing 0 [] false)
              → ∀ {ℓ ℓ′ lo′} {h′ : lo′ ≤ ℓ′} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)}
              → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
              → Sound (thru-outer mergeAllᵒ nid′ ↠[ h′ ] q) sI stI
              → ∀ {now fin oP vs₁ fin₁ sP₁ stP₁ rI}
              → stepFrame⇓ now (thru-outer mergeAllᵒ nid) p vs fin sP stP (oP , vs₁ , fin₁ , sP₁ , stP₁)
              → foldPath⇓ now (thru-outer mergeAllᵒ nid′ ↠[ h′ ] q) vs′ fin sI stI rI
              → Arm S now oP sP₁ stP₁ p vs₁ fin₁ none Never rI
    hop-arm S hd sp k nP nI r si {fin = fin} dW@(step-thru-outer W) (fold-step dW′@(step-thru-outer W′) dR) =
      let X = hop-walk S hd sp k nP nI r (unthru si) W W′
      in hop-end {fin = fin} (proj₁ X) (proj₁ (proj₂ X)) (drop-ot _ _ _ (step-kept _ dW′ si)) dR


    -- A SHARE'S FAN-OUT AGAINST THE PLAIN CASCADE OVER THE SAME READERS,
    -- one reader at a time: the plain chain and the admitted row it is
    -- partnered with, a cut one on both sides skipped
    fan-go : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n} {a : Arrival Γ}
               (εI : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (arrTy a)) {es now vs fin}
           → CarriesU εI es vs → arrTick a ≡ now → arrSource a ≡ toℕ i
           → ∀ {chs adm}
           → Pointwise (SlotPair (Store.rows S) (EvalSt.cancelled stP) (EvalSt.cancelled stI) i) chs adm
           → (∀ {x} → x ∈ chs → Sound (proj₂ (proj₂ x)) sP stP)
           → (∀ {x y} → x ∈ chs → y ∈ chs → Agree (proj₂ (proj₂ x)) (proj₂ (proj₂ y)))
           → (∀ {x} → x ∈ adm → Sound (proj₂ x) sI stI)
           → (∀ {x y} → x ∈ adm → y ∈ adm → Agree (proj₂ x) (proj₂ y))
           → ∀ {oP sP₁ stP₁ oI sI₁ stI₁}
           → cascadeGo⇓ a vs fin chs sP stP (oP , sP₁ , stP₁)
           → shareGo⇓ now (n ↑ʳ i) es fin adm sI stI (oI , sI₁ , stI₁)
           → After S (oP , sP₁ , stP₁) (oI , sI₁ , stI₁)
           × (fin ≡ false → ∀ {I} → DelU εI I es → Out I oI)
    fan-go S εI c ta sa [] _ _ _ _ casc-nil go-nil = after S (λ x → x) (λ x → x) [] (λ x → x) , λ _ _ → []
    fan-go S εI c ta sa (slotpair _ ∷ ps) hP aP hI aI (casc-cut _ g) (go-cut _ g′) =
      fan-go S εI c ta sa ps (λ m → hP (there m)) (λ m m′ → aP (there m) (there m′)) (λ m → hI (there m)) (λ m m′ → aI (there m) (there m′)) g g′
    fan-go S εI c ta sa (slotpair q ∷ _) _ _ _ _ (casc-cut y _) (go-live y′ _ _) =
      ⊥-elim (t≢f (trans (sym y) (trans (cong (λ s → skipᵇ s _ _) sa) (trans (skip-alike S q) y′))))
    fan-go S εI c ta sa (slotpair q ∷ _) _ _ _ _ (casc-live y _ _) (go-cut y′ _) =
      ⊥-elim (t≢f (trans (sym y′) (trans (sym (trans (cong (λ s → skipᵇ s _ _) sa) (skip-alike S q))) y)))
    fan-go S εI c ta sa (slotpair (inj₁ (x , _)) ∷ _) _ _ _ _ (casc-live {a = a₀} {rid = rid} {st₀ = st₀} y _ _) (go-live _ _ _) =
      ⊥-elim (t≢f (trans (sym (skip-cut {s = arrSource a₀} {rid} {st₀} x)) y))
    fan-go S εI {fin = fin} c refl sa (slotpair (inj₂ (_ , _ , pr)) ∷ ps) hP aP hI aI (casc-live _ dP g) (go-live {emits = eI} _ dI g′) =
      rebase {fin = fin} (A ⨾ proj₁ R) , λ { refl d → out-++ eI _ (proj₂ X refl d) (proj₂ R refl d) }
      where
        sP₀ = sub-ot (λ r∈ → r∈) ≤-refl (hP (here refl))
        sI₀ = sub-ot (λ r∈ → r∈) ≤-refl (hI (here refl))
        X = slot-pass (walker κ) (delivered S {fin} pr) εI (partner-row κ _ _ _ _ _ (Store.rows S) pr) c sP₀ sI₀ (unchain dP) dI (n<1+n _)
        A = proj₁ X
        map-slot : ∀ {sP stP sI stI sP₁ stP₁ sI₁ stI₁} {S₀ : St sP stP sI stI} {S₁ : St sP₁ stP₁ sI₁ stI₁} {i : Fin n} {u}
                     {cs : List (RegId × AtFloor Γ u t)} {ds}
                 → Keeps S₀ S₁
                 → Pointwise (SlotPair (Store.rows S₀) (EvalSt.cancelled stP) (EvalSt.cancelled stI) i) cs ds
                 → Pointwise (SlotPair (Store.rows S₁) (EvalSt.cancelled stP₁) (EvalSt.cancelled stI₁) i) cs ds
        map-slot K []       = []
        map-slot {S₀ = S₀} {S₁ = S₁} K (r ∷ rs) = slot-keeps {S = S₀} {S₁ = S₁} K r ∷ map-slot {S₀ = S₀} {S₁ = S₁} K rs
        R = fan-go (After.store A) εI c refl sa (map-slot {S₀ = S} {S₁ = After.store A} (After.keeps A) ps)
              (λ m → fold-kept (unchain dP) sP₀ _ (sub-ot (λ r∈ → r∈) ≤-refl (hP (there m))) (aP (here refl) (there m)))
              (λ m m′ → aP (there m) (there m′))
              (λ m → fold-kept dI sI₀ _ (sub-ot (λ r∈ → r∈) ≤-refl (hI (there m))) (aI (here refl) (there m)))
              (λ m m′ → aI (there m) (there m′)) g g′

    -- WHAT A HOT ARRIVAL'S IMPL CHAIN DOES BEFORE THE SHARE: its input block
    -- runs alone, the plain side not moving, and hands the share the one emit
    -- that carries the arrival's value
    data HotStart {sP stP sI stI} (S : St sP stP sI stI) (a : Arrival Γ) (a′ : Arrival (plainᵏ Γ κ)) (i : Fin n)
                  (oI : Stream (plainᵏ Γ κ) (emitᵗ t)) (sI₁ : Sched (plainᵏ Γ κ)) (stI₁ : EvalSt ei) : Set where
      hot-start-at : ∀ {oB sI₂ stI₂ e lo rD} {below : lo ≤ toℕ (n ↑ʳ i)}
                       {εI : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (arrTy a)} {ty : arrTy a ≡ lookup Γ i}
                   → (A : After S ([] , sP , stP) (oB , sI₂ , stI₂))
                   → CarriesU εI (e ∷ []) (arrVal a ∷ [])
                   → Out (counter (Sched.mint sI) sourceᵏ) oB × DelU εI (counter (Sched.mint sI) sourceᵏ) (e ∷ [])
                   → dispatchShare⇓ (arrTick a′) (n ↑ʳ i) below (e ∷ []) false sI₂ stI₂ rD
                   → (oI , sI₁ , stI₁) ≡ (oB ++ proj₁ rD , proj₂ rD)
                   → HotStart S a a′ i oI sI₁ stI₁
      -- or no reader on either side, and the impl not moving
      hot-idle : chainsOf a stP ≡ [] → (oI , sI₁ , stI₁) ≡ ([] , sI , stI)
               → HotStart S a a′ i oI sI₁ stI₁

    -- WHAT A HOT ARRIVAL'S IMPL CHAIN DOES AT THE END: the same block runs
    -- alone, the share is spent, and the end it hands the share is
    -- dispatched.  The plain side has latched the slot and the impl the share,
    -- which is where the latches meet again
    data HotEnd {sP stP sI stI} (S : St sP stP sI stI) (a : Arrival Γ) (a′ : Arrival (plainᵏ Γ κ)) (i : Fin n)
                (eI : Stream (plainᵏ Γ κ) (emitᵗ t)) (sI₃ : Sched (plainᵏ Γ κ)) (stI₃ : EvalSt ei) : Set where
      hot-end-at : ∀ {oB sI₂ stI₂ lo rD} {below : lo ≤ toℕ (n ↑ʳ i)}
                     {εI : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (arrTy a)} {ty : arrTy a ≡ lookup Γ i}
                 → (A : After S ([] , sP , cascadeClose a stP)
                              (oB , sI₂ , shareSpend (n ↑ʳ i) (shareDying (n ↑ʳ i) true stI₂)))
                 → CarriesU εI [] []
                 → dispatchShare⇓ (arrTick a′) (n ↑ʳ i) below [] true sI₂ stI₂ rD
                 → (eI , sI₃ , stI₃) ≡ (oB ++ proj₁ rD , proj₂ rD)
                 → HotEnd S a a′ i eI sI₃ stI₃
      -- or no row at the raw slot or the share, no plain reader, and the
      -- impl only latching the raw slot; a share that connected is spent
      hot-end-idle : chainsOf a stP ≡ []
                   → srcCount (toℕ (i ↑ˡ n)) (EvalSt.registry stI) ≡ 0 → srcCount (toℕ (n ↑ʳ i)) (EvalSt.registry stI) ≡ 0
                   → (memberSource (toℕ (n ↑ʳ i)) (EvalSt.connectedShares stI) ≡ true
                      → memberSource (toℕ (i ↑ˡ n)) (EvalSt.completedSources stI) ≡ true)
                   → (eI , sI₃ , stI₃) ≡ ([] , sI , cascadeClose a′ stI)
                   → HotEnd S a a′ i eI sI₃ stI₃

    postulate
      -- THE HOT BLOCK PAST ITS BRACKET: the stamp the bracket's one group
      -- makes is subscribed through the block's merge, and its value
      -- reaches the share.  What it owes is the start's: the block's run
      -- related, the one stamped emit carrying the value at the counter the
      -- chain entered with, the plain side not moving
      -- PROBED: make qc-store QC='51 150 3' QC_BUDGET=900 QC_DRAW='{"exp":[1,1,1,2,1,0,1,1,0,0,0,0,2],"leaf":[2,0,1],"script":[1,1,1,1,1],"reach":["scan","flatten"]}'
      --   decided by `CLI.Store-Check`'s `store?`: 150 agree, 0 fail.
      --   Case 28's two hot arrivals reach a switch's last inner, a read
      --   of the hot input connected at subscribe.
      hot-walk : ∀ {sP stP sI stI} (S : St sP stP sI stI) {a : Arrival Γ} {a′ : Arrival (plainᵏ Γ κ)} {i : Fin n}
               → (hot : lookup κ i ≡ hotᵏ)
               → Head (toℕ i) (toℕ (i ↑ˡ n)) {arrTy a} {arrTy a′} (arrVal a ∷ []) (arrVal a′ ∷ [])
               → arrTy a ≡ lookup Γ i
               → ∀ {v} → _≡_ {A = Σ Ty (Val (plainᵏ Γ κ))} (arrTy a′ , arrVal a′) (plainᵗ (lookup Γ i) , v)
               → ∀ {ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ m1 j1 b m2 Θ₀ ρ₀ Θ₃ fr ρ₃ Θ₄ ρ₄}
                   {h₁ : suc (toℕ (i ↑ˡ n)) ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ}
                   {h : ℓ ≤ toℕ (n ↑ʳ i)}
               → InputBlock κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (plainᵗ (lookup Γ i))
                   (map-f (Θ₀ , inrᵗ (varᵗ (here refl)) , ρ₀) ↠[ h₁ ] (from-inner mergeAllᵒ m1 j1 ↠[ h₂ ] (batchSync-f b ↠[ h₃ ] (map-f (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃) ↠[ h₄ ] (map-f (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄) ↠[ h₅ ] (thru-outer mergeAllᵒ m2 ↠[ h₆ ] subst (λ u → Path (plainᵏ Γ κ) ℓ u (emitᵗ t)) (hotEq {Γ = Γ} κ i hot) (share-sink (n ↑ʳ i) h)))))))
                   (subst (λ u → Path (plainᵏ Γ κ) ℓ u (emitᵗ t)) (hotEq {Γ = Γ} κ i hot) (share-sink (n ↑ʳ i) h))
               → ∀ {oW sW stW}
               → thruWalk⇓ mergeAllᵒ m2 (subst (λ u → Path (plainᵏ Γ κ) ℓ u (emitᵗ t)) (hotEq {Γ = Γ} κ i hot) (share-sink (n ↑ʳ i) h)) (arrTick a′)
                   (thruEvents (map (applyClo {s = obs (emitᵗ (lookup Γ i))} {t = echoᵗ (emitᵗ (lookup Γ i))} (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄))
                                 (map (applyClo {s = (unitᵗ +ᵗ plainᵗ (lookup Γ i)) ×ᵗ listᵗ (unitᵗ +ᵗ plainᵗ (lookup Γ i))} {t = obs (emitᵗ (lookup Γ i))} (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃))
                                   (batchVals false (map (applyClo {s = plainᵗ (lookup Γ i)} {t = unitᵗ +ᵗ plainᵗ (lookup Γ i)} (Θ₀ , inrᵗ (varᵗ (here refl)) , ρ₀)) (v ∷ []))))))
                   sI (record stI
                         { nodes = setNode b (batchSync-st {s = unitᵗ +ᵗ plainᵗ (lookup Γ i)} false [] false) (EvalSt.nodes stI) })
                   (oW , sW , stW)
               → HotStart S a a′ i oW sW stW

    -- THE IMPL'S ONE CHAIN AT A HOT ARRIVAL'S RAW SLOT, ONCE ITS SHARE HAS
    -- CONNECTED: the raw row's step over the arrival's value, its input
    -- block run alone into the share.  With no end the inner reacts to
    -- nothing, the bracket flushes the one value, and the tail below the
    -- merge is handed nothing
    hot-block : ∀ {sP stP sI stI} (S : St sP stP sI stI) {a : Arrival Γ} {a′ : Arrival (plainᵏ Γ κ)} {i : Fin n}
              → (hot : lookup κ i ≡ hotᵏ)
              → Head (toℕ i) (toℕ (i ↑ˡ n)) {arrTy a} {arrTy a′} (arrVal a ∷ []) (arrVal a′ ∷ [])
              → arrTy a ≡ lookup Γ i
              → ∀ {rid q ℓ full} {h : ℓ ≤ toℕ (n ↑ʳ i)}
              → _≡_ {A = RegRow (plainᵏ Γ κ) (emitᵗ t)} (rid , atSlot (i ↑ˡ n) , (arrTy a′ , q)) (rid , atSlot (i ↑ˡ n) , (plainᵗ (lookup Γ i) , full))
              → InputBlock κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (plainᵗ (lookup Γ i)) full
                  (subst (λ u → Path (plainᵏ Γ κ) ℓ u (emitᵗ t)) (hotEq {Γ = Γ} κ i hot) (share-sink (n ↑ʳ i) h))
              → ∀ {oI sI₁ stI₁}
              → chainStep⇓ a′ (arrVal a′ ∷ []) false (suc (toℕ (i ↑ˡ n)) , q) sI
                  stI (oI , sI₁ , stI₁)
              → HotStart S a a′ i oI sI₁ stI₁
    hot-block S {a′ = record { elemTy = _ ; payload = v }} {i = i} hot hd ty refl ib@(block _ _ eb _ _ _ _ _)
      (chain-step (fold-step step-map (fold-step (step-from-inner react-false)
        (fold-step SB (fold-step step-map (fold-step step-map (fold-step (step-thru-outer W) fq)))))))
      with batch-flush SB eb
    ... | refl with disp-quiet (sink-at (hotEq {Γ = Γ} κ i hot) fq)
    ...   | refl = subst (λ o → HotStart S _ _ i o _ _) (sym (++-identityʳ _)) (hot-walk S hot hd ty refl ib W)

    -- a minted source's partnered chain, by the row the store pairs it with
    row-pass : ∀ {sP stP sI stI} (S : St sP stP sI stI) {src src′ u u′} {vs : List (Val Γ u)} {vs′ : List (Val (plainᵏ Γ κ) u′)}
             → Head src src′ {u} {u′} vs vs′
             → ∀ {rid rid′ lo lo′} {p : Path Γ lo u t} {p′ : Path (plainᵏ Γ κ) lo′ u′ (emitᵗ t)}
             → RowRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI)
                 (rid , atDyn src lo , (u , p)) (rid′ , atDyn src′ lo′ , (u′ , p′))
             → Sound p sP stP → Sound p′ sI stI
             → ∀ {now fin rP rI} → foldPath⇓ now p vs fin sP stP rP → foldPath⇓ now p′ vs′ fin sI stI rI
             → After S rP rI × (fin ≡ false → Out (counter (Sched.mint sI) sourceᵏ) (proj₁ rI))
    row-pass S hd (cold~ sp blk r refl) soP soI dP dI = block-arm S hd sp blk r soP soI dP dI
    row-pass S hd (defer~ sp k nP nI r refl) soP soI (fold-step d@(step-thru-outer W) dP) dI@(fold-step {out₁ = oH} {out₂ = oR} (step-thru-outer {op = op} {nid = nid} {sched′ = sW} {st′ = stW} W′) dR) =
      proj₁ (resume (walker κ) (hop-arm S hd sp k nP nI r soI d dI) (adv d soP) dP (n<1+n _)) ,
      λ e → out-++ oH oR (proj₂ (proj₂ (hop-walk S hd sp k nP nI r (unthru soI) W W′))) (out-quiet oR (quiet-wrap op nid sW stW e (rel-unbatched r) dR))
