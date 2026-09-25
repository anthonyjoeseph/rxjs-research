------------------------------------------------------------------
-- THE CALLS A FRAME MAKES ABOVE IT, AS THE CANDIDATE'S MUTUAL BLOCK
-- CONSUMES THEM: each carries the rule across the run it wraps, which
-- is what `Rx.Evaluator.Reducible.Rule-Kept` proves, so they sit
-- downstream of it and of `Rx.Evaluator.Reducible.Support`.
------------------------------------------------------------------

module Rx.Evaluator.Reducible.Calls where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Bool.ListAction using (any)
open import Data.Fin.Properties using (toℕ<n) renaming (_≟_ to _≟ᶠ_)
open import Data.List using (List; []; _∷_; null)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᵃ)
open import Data.Maybe using (Maybe; just; nothing; _<∣>_) renaming (map to mapᵐ)
open import Data.Nat using (ℕ; pred; _≤_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using ([_,_]; [_,_]′)
open import Data.Unit.Polymorphic using (tt)
open import Data.Unit using () renaming (tt to tt₀)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)

open import Rx.Prim using (Tick)
open import Rx.Exp using (obs; Ctx; Closed; Val)
open import Rx.Evaluator.Freshness using (nodeCt; lookup-set)
open import Rx.Evaluator using (Sched; EvalSt; Path; _↠[_]_; Frame; from-inner; NodeState; mergeAll-st; mergeAllᵒ; AllOp;
  NodeId; switch-st; exhaust-st; setNode; finishUsable; aliveThroughᶠ)
open import Rx.Evaluator.Unconn-Arith using (fell-keeps; room-keeps)
open import Rx.Evaluator.Keeps using (foldPath-keeps; stepFrame-keeps; innerFinish-keeps)
open import Rx.Evaluator.Domain using (subscribeE⇓; mergeAllDrain⇓; foldPath⇓; fold-step; drain-spent; innerFinish⇓;
  finish-all-drain; finish-switch-clear; finish-exhaust-clear; finish-nil; innerReact⇓;
  react-false; react-alive; react-dead; step-from-inner)
open import Rx.Evaluator.Reducible.Support using (_∷ᵗ_; Ans; Call; Column; FrameStep; HeldF; NodeOn; Pre; PreFs; PreHolds; QEmpty; RP; Red;
  Room; Sound; Stage; SubStep; []ᵗ; apply; bumpNode; call; deadBy; der; drop-ot; endPre; endRP;
  endS; f-exhaust; f-merge; f-switch; fallen; finishing; fin″; fold; fresh-inner; grounded;
  head-off; headHolds; headKept; headPre; holdsFs-step; inner-back; kept; ofColumn; out; outs;
  sched″; stage; stage-map; stage-nil; stage-seq; standing; step; step-ct; step-off; step-red;
  step-⇓; st″; writeStage)
open import Rx.Evaluator.Reducible.Rule-Kept using (step-kept; subscribe-kept; fold-kept)

-- THE CALL A LIVE FRAME MAKES ABOVE IT, FOR THE CALL MADE TO IT: the
-- step's group with the candidates through the step, at the step's
-- state, on the ground the step carried up.  One function, because
-- the fold makes this call and the arm's translation re-makes it, and
-- the two have to be the same term.
headCall : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo ℓ s u} {f : Frame Γ s u}
           {P : Val Γ s → Set₁} {P′ : Val Γ u → Set₁} {Held : HeldF f → Set₁} {le : lo ≤ ℓ}
           (fs : FrameStep {e = e} f P P′ Held) (h : HeldF f) → Held h
         → (κ : Path Γ ℓ u t) (pfs : PreFs κ)
         → Call {e = e} m P (f ↠[ le ] κ) (standing (h , pfs))
         → Call {e = e} m P′ κ (standing pfs)
headCall {f = f} {le = le} fs h rh κ pfs (call now vals col fin sched st rm (grounded ((c , fr) , ap , hs) so)) =
  let r = step fs h vals fin sched st
  in call now (outs r) (ofColumn κ (standing pfs) (proj₁ (step-red fs col rh))) (fin″ r) (sched″ r) (st″ r)
       (room-keeps (stepFrame-keeps (step-⇓ fs {κ = κ} {now = now} h vals fin sched st c)) rm)
       (grounded
         (holdsFs-step κ pfs
           (λ k on k< → step-off fs h vals fin sched st k (λ onF → ap k onF on))
           (subst (nodeCt sched ≤_) (sym (step-ct fs h vals fin sched st)) ≤-refl) hs)
         (drop-ot f le κ (step-kept le (step-⇓ fs {κ = κ} {now = now} h vals fin sched st c) so)))

-- ONE CALL ABOVE THE FRAME, AS A STAGE: on standing ground it is the
-- fold applied once and the frame's ground carried over it; on fallen
-- ground the fold reads the store and the fall stands.
callStage : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {S : Set} {lo ℓ s u}
            (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (h : HeldF f)
            (q : Pre κ) (rp : RP {e = e} m (Red m u) S κ q) (s₀ : S)
            (now : Tick) (vals : List (Val Γ u)) → Column κ (Red m u) q vals → (fin : Bool)
          → {sched : Sched Γ} {st : EvalSt e} → Room m sched st
          → PreHolds m (f ↠[ le ] κ) (headPre h q) sched st
          → Stage m f le κ (λ o sc s′ → foldPath⇓ {e = e} now κ vals fin sched st (o , sc , s′)) q rp s₀ sched st
callStage f le κ h (standing pfs) rp s₀ now vals col fin {sched} {st} rm (grounded (hf , ap , hs) so) =
  let c  = call now vals col fin sched st rm (grounded hs (drop-ot f le κ so))
      an = apply rp s₀ c
  in stage (out an) (Ans.sched′ an) (Ans.st′ an) (der an) (c ∷ᵗ []ᵗ) refl h
       (headHolds f le κ h hf ap so (Ans.pre′ an) (Ans.holds′ an) (kept an)
          (fold-kept (der an) (drop-ot f le κ so) (f ↠[ le ] κ) so (λ _ _ _ → refl)))
       (headKept f le κ (λ _ _ → refl) refl (λ _ _ _ ea → ea) (Ans.pre′ an) (kept an) h)
callStage f le κ h fallen rp s₀ now vals col fin {sched} {st} rm (grounded fell so) =
  let an = fold rp s₀ now vals col fin sched st rm (grounded fell (drop-ot f le κ so))
  in stage (out an) (Ans.sched′ an) (Ans.st′ an) (der an) []ᵗ refl h
       (grounded (fell-keeps (foldPath-keeps (der an)) fell)
          (fold-kept (der an) (drop-ot f le κ so) (f ↠[ le ] κ) so (λ _ _ _ → refl)))
       tt

-- and the frame holds what it held
callStage-hd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {S : Set} {lo ℓ s u}
               (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (h : HeldF f)
               (q : Pre κ) (rp : RP {e = e} m (Red m u) S κ q) (s₀ : S)
               (now : Tick) (vals : List (Val Γ u)) (col : Column κ (Red m u) q vals) (fin : Bool)
               {sched : Sched Γ} {st : EvalSt e} (rm : Room m sched st)
               (hs : PreHolds m (f ↠[ le ] κ) (headPre h q) sched st)
             → Stage.hd (callStage f le κ h q rp s₀ now vals col fin rm hs) ≡ h
callStage-hd f le κ h (standing pfs) rp s₀ now vals col fin rm hs = refl
callStage-hd f le κ h fallen         rp s₀ now vals col fin rm hs = refl

-- so an inner subscribed raw leaves the rule standing on both
inner-after : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} (op : AllOp) (nid : NodeId)
                (κ : Path Γ lo u t) {now} {o : Val Γ (obs u)} (sched : Sched Γ) {st : EvalSt e} {r}
            → subscribeE⇓ {e = e} o (from-inner op nid (nodeCt sched) ↠[ ≤-refl ] κ) now (bumpNode sched) st r
            → Sound κ sched st → NodeOn nid κ sched st
            → Sound κ (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) × NodeOn nid κ (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
inner-after {u = u} op nid κ sched {st} d so nd =
  let so₀ = fresh-inner op nid κ sched {st} so nd
  in inner-back op nid (nodeCt sched) κ (subscribe-kept d so₀ _ so₀ (λ _ _ _ → refl))

-- THE INNER FRAME'S STEP.  Values pass; an end passes while a chain
-- under this instance is still registered; otherwise the finish runs
-- at the node, and the merge's drain there has nothing to subscribe.
fiStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u} (op : AllOp) (allNid inst : NodeId)
       → SubStep {e = e} (from-inner {s = u} op allNid inst) QEmpty m

pass : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u} (op : AllOp) (allNid inst : NodeId) {S : Set} {lo ℓ}
       (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (pfs : PreFs κ)
       (rp : RP {e = e} m (Red m u) S κ (standing pfs)) (s₀ : S) (h : Maybe (NodeState Γ))
       (now : Tick) (vals : List (Val Γ u)) → All (Red m u) vals → (fin : Bool)
     → {sched : Sched Γ} {st : EvalSt e} → Room m sched st
     → PreHolds m (from-inner {s = u} op allNid inst ↠[ le ] κ) (standing (h , pfs)) sched st
     → innerReact⇓ {e = e} op allNid inst κ now vals sched st fin ([] , vals , false , sched , st)
     → Stage m (from-inner op allNid inst) le κ
         (λ o sc s′ → foldPath⇓ {e = e} now (from-inner op allNid inst ↠[ le ] κ) vals fin sched st (o , sc , s′))
         (standing pfs) rp s₀ sched st
pass op allNid inst le κ pfs rp s₀ h now vals col fin rm hs d =
  stage-map (λ d′ → fold-step (step-from-inner d) d′)
    (callStage (from-inner op allNid inst) le κ h (standing pfs) rp s₀ now vals (ofColumn κ (standing pfs) col) false rm hs)

-- the finish, once no chain under the instance is registered
fiDead : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u} (op : AllOp) (allNid inst : NodeId) {S : Set} {lo ℓ}
         (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (pfs : PreFs κ)
         (rp : RP {e = e} m (Red m u) S κ (standing pfs)) (s₀ : S) (h : Maybe (NodeState Γ)) → QEmpty h
       → (now : Tick) (vals : List (Val Γ u)) → All (Red m u) vals
       → {sched : Sched Γ} {st : EvalSt e} → Room m sched st
       → PreHolds m (from-inner {s = u} op allNid inst ↠[ le ] κ) (standing (h , pfs)) sched st
       → any (aliveThroughᶠ inst st) (EvalSt.registry st) ≡ false
       → Σ (Stage m (from-inner op allNid inst) le κ
             (λ o sc s′ → foldPath⇓ {e = e} now (from-inner op allNid inst ↠[ le ] κ) vals true sched st (o , sc , s′))
             (standing pfs) rp s₀ sched st)
           (λ r → QEmpty (Stage.hd r))
fiDead {Γ = Γ} {e = e} {u = u} op allNid inst le κ pfs rp s₀ h g now vals col {sched} {st} rm hs@(grounded ((c , lts) , ap , hsκ) _) eqa
  with finishUsable op u inst h in equ
... | false = stage-map (λ d′ → fold-step (step-from-inner (react-dead eqa (finish-nil (trans (cong (finishUsable op u inst) c) equ)))) d′)
                (callStage (from-inner op allNid inst) le κ h (standing pfs) rp s₀ now vals (ofColumn κ (standing pfs) col) false rm hs)
            , g
... | true with finishing op u inst h equ
...   | f-switch c′ od eqc =
        let w  = writeStage (from-inner op allNid inst) le κ (standing pfs) rp s₀ allNid (switch-st nothing od)
                   (λ k ne → head-off allNid (inst ∷ []) k ne) (just (switch-st nothing od)) (lookup-set allNid (switch-st nothing od) (EvalSt.nodes st)) h hs
            cs = callStage (from-inner op allNid inst) le κ (just (switch-st nothing od)) (standing pfs) rp s₀ now vals
                   (ofColumn κ (standing pfs) col) od rm (Stage.hl w)
        in stage-map (λ d′ → fold-step (step-from-inner (deadBy eqa c (finish-switch-clear eqc))) d′)
             (stage-seq w cs (λ d → d))
           , tt
...   | f-exhaust act od =
        let w  = writeStage (from-inner op allNid inst) le κ (standing pfs) rp s₀ allNid (exhaust-st false od)
                   (λ k ne → head-off allNid (inst ∷ []) k ne) (just (exhaust-st false od)) (lookup-set allNid (exhaust-st false od) (EvalSt.nodes st)) h hs
            cs = callStage (from-inner op allNid inst) le κ (just (exhaust-st false od)) (standing pfs) rp s₀ now vals
                   (ofColumn κ (standing pfs) col) od rm (Stage.hl w)
        in stage-map (λ d′ → fold-step (step-from-inner (deadBy eqa c finish-exhaust-clear)) d′)
             (stage-seq w cs (λ d → d))
           , tt
...   | f-merge lim act q od with g
...     | refl =
        let fi = from-inner {s = u} op allNid inst
            s₁ = callStage fi le κ h (standing pfs) rp s₀ now vals (ofColumn κ (standing pfs) col) false rm hs
            s₂ : Stage _ fi le κ
                   (λ o sc s′ → Σ ℕ (λ act′ → Σ (List (Val Γ (obs u))) (λ q′ →
                      mergeAllDrain⇓ {e = e} allNid κ now [] lim (pred act) od [] (Stage.sc s₁) (Stage.st′ s₁)
                        (o , act′ , q′ , sc , s′))))
                   (endPre (Stage.tr s₁)) (endRP (Stage.tr s₁)) (endS (Stage.tr s₁)) (Stage.sc s₁) (Stage.st′ s₁)
            s₂ = stage-nil fi le κ (endPre (Stage.tr s₁)) (endRP (Stage.tr s₁)) (endS (Stage.tr s₁)) []
                   (pred act , [] , drain-spent) (Stage.hd s₁) (Stage.hl s₁)
            s₁₂ : Stage _ fi le κ
                    (λ o sc s′ → Σ ℕ (λ act′ → Σ (List (Val Γ (obs u))) (λ q′ →
                       innerFinish⇓ {e = e} mergeAllᵒ allNid inst κ now vals sched st (just (mergeAll-st lim act q od))
                         (o , [] , null q ∧ od ∧ (act′ ≡ᵇ 0) , sc
                         , record s′ { nodes = setNode allNid (mergeAll-st lim act′ q′ od) (EvalSt.nodes s′) }))))
                    (standing pfs) rp s₀ sched st
            s₁₂ = stage-seq s₁ s₂ (λ { (act′ , q′ , d₂) → act′ , q′ , finish-all-drain {act = act} (Stage.dv s₁) d₂ })
            act′ = proj₁ (Stage.dv s₁₂)
            q′   = proj₁ (proj₂ (Stage.dv s₁₂))
            dfin = proj₂ (proj₂ (Stage.dv s₁₂))
            fin′ = null q ∧ od ∧ (act′ ≡ᵇ 0)
            w  = writeStage fi le κ (endPre (Stage.tr s₁₂)) (endRP (Stage.tr s₁₂)) (endS (Stage.tr s₁₂)) allNid
                   (mergeAll-st lim act′ q′ od) (λ k ne → head-off allNid (inst ∷ []) k ne)
                   (just (mergeAll-st lim act′ q′ od)) (lookup-set allNid (mergeAll-st lim act′ q′ od) (EvalSt.nodes (Stage.st′ s₁₂))) (Stage.hd s₁₂) (Stage.hl s₁₂)
            cs = callStage fi le κ (just (mergeAll-st lim act′ q′ od)) (endPre (Stage.tr s₁₂)) (endRP (Stage.tr s₁₂)) (endS (Stage.tr s₁₂))
                   now [] (ofColumn κ _ []ᵃ) fin′ (room-keeps (innerFinish-keeps dfin) rm) (Stage.hl w)
            cs-hd = callStage-hd fi le κ (just (mergeAll-st lim act′ q′ od)) (endPre (Stage.tr s₁₂)) (endRP (Stage.tr s₁₂))
                      (endS (Stage.tr s₁₂)) now [] (ofColumn κ _ []ᵃ) fin′ (room-keeps (innerFinish-keeps dfin) rm) (Stage.hl w)
            s₃ : Stage _ fi le κ
                   (λ o sc s′ → foldPath⇓ {e = e} now κ [] fin′ (Stage.sc s₁₂)
                                  (record (Stage.st′ s₁₂) { nodes = setNode allNid (mergeAll-st lim act′ q′ od) (EvalSt.nodes (Stage.st′ s₁₂)) })
                                  (o , sc , s′))
                   (endPre (Stage.tr s₁₂)) (endRP (Stage.tr s₁₂)) (endS (Stage.tr s₁₂)) (Stage.sc s₁₂) (Stage.st′ s₁₂)
            s₃ = stage-seq w cs (λ d → d)
        in stage-seq s₁₂ s₃ (λ d₃ → fold-step (step-from-inner (deadBy eqa c dfin)) d₃)
           , subst QEmpty (sym cs-hd) refl

fiStep op allNid inst le κ pfs rp s₀ h g now vals col false sched st rm hs =
  pass op allNid inst le κ pfs rp s₀ h now vals col false rm hs react-false , g
fiStep op allNid inst le κ pfs rp s₀ h g now vals col true sched st rm hs
  with any (aliveThroughᶠ inst st) (EvalSt.registry st) in eqa
... | true  = pass op allNid inst le κ pfs rp s₀ h now vals col true rm hs (react-alive eqa) , g
... | false = fiDead op allNid inst le κ pfs rp s₀ h g now vals col rm hs eqa
