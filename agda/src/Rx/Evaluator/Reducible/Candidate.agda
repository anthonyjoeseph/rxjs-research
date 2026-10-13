------------------------------------------------------------------
-- THE CANDIDATE AND EVERYTHING STATED OVER A TRACE: the reducibility
-- predicate, the stage a frame arm answers with, and the per-frame
-- arms the candidate's mutual block consumes.  Nothing here calls
-- into that block either (`Rx.Evaluator.Reducible`).
------------------------------------------------------------------

module Rx.Evaluator.Reducible.Candidate where

-- THE ORACLE BUILDS THIS MODULE'S DATA STRICT.  A lazy field of a
-- record an answer is built from is a thunk over the state it was
-- computed from, so a compiled run that keeps one answer keeps every
-- state before it -- measured on the bug-cache row switching to two
-- ofs, where collecting them was most of the run
-- (`typecheck-performance-numbers.md`).  The pragma is per module and
-- the proof never sees it; the one family that must stay lazy is
-- `Rx.Evaluator.Reducible.Trace`, which is why it is a module of its
-- own.
{-# FOREIGN GHC {-# LANGUAGE StrictData #-} #-}

open import Data.Bool using (Bool; true; false; T)
open import Data.Bool.ListAction using (any)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n) renaming (_≟_ to _≟ᶠ_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᵃ)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing; _<∣>_) renaming (map to mapᵐ)
open import Data.Nat using (ℕ; suc; _≤_; _<_; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Level using () renaming (_⊔_ to _⊔ˡ_)
open import Data.Sum using (inj₁; inj₂; [_,_]; [_,_]′)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc)
open import Relation.Nullary using (yes; no)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans)

open import Rx.Prim using (Tick; ObservableInput; hot; cold)
open import Rx.Slots using (scripted)
open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; listᵗ; obs; Ctx; Closed; Val; Exp; Tm; Env; []ᵉ;
  _∷ᵉ_; evalWith; foldVals; lookupEnv; input; isData; inputsBelowᵉ; FnClo; applyClo; _≟ᵗ_)
open import Rx.Exp.Guarded using (gsizeᵉ)
open import Rx.Mint using (sourceᵏ; regᵏ; ordinalᵏ; freshId; setAt)
open import Rx.Evaluator.Freshness using (nodeCt; pres; below; set-above)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; _↠[_]_; Frame; batchSync-f; NodeState; lookupNode; frameNodes;
  register; atDyn; atSlot; lowerFloor; memberSource; mergeAll-st; NodeId; cell-st; take-st;
  switch-st; exhaust-st; batchSync-st; setNode; scanVals; scanDispatch; batchVals;
  batchDispatch; batchDown; resolve)
open import Rx.Evaluator.Unconn-Arith using (fell-keeps)
open import Rx.Evaluator.Keeps using (Keeps)
open import Rx.Evaluator.Domain using (subscribeE⇓; subs-hot-done; subs-hot-live; subs-cold-sync; subs-cold-async; foldPath⇓;
  stepFrame⇓; injectRoot; step-batchSync)
open import Rx.Evaluator.Reducible.Support using (Room; Fell; HeldF; PreFs; Pre; standing; fallen; ConsistentF;
  EndsKept; Sound; PreHolds; grounded; ofColumn; ∨-Tˡ; sub-ot; lower-nodes; lower-end; lower-distinct; register-sound;
  ends-register; holdsFs-step; holds-step; Kept; kept-step; call; RP; Ans; Answered; answer; joinPre; _⁰×_; Σ⁰; _|>⁰_;
  FrameStep; headPre; head-off; kept-refl; join-idem; join-chain; kept-join; kept-shift; kept-before; cell-inj;
  scanHeld; batchHeld; batchCons; batchOff; batchCt; batchReg; batchStepped; _,_; step-⇓; out; step-ct; step-off;
  kept; der; step-reg; step; step-red; step-cons; distinct)
open import Rx.Evaluator.Reducible.Trace using (Trace; []ᵗ; _∷ᵗ_; endPre; endRP; endS; _++ᵗ_; end-++)

-- THE CANDIDATE.  At a data type it is trivial, because nothing about
-- a number can fail to be reducible; at an observable it is the
-- statement the whole argument turns on -- given any continuation
-- above and any state under the ceiling, a subscription derivation
-- exists whose answer is at the root, and the calls made to the
-- continuation come back as a trace whose end stands on the ground it
-- claims and kept what a frame beneath needs kept.
--
-- IT LIVES IN `Set₁` BECAUSE THE OBSERVABLE ARM QUANTIFIES OVER THE
-- CONTINUATION'S STATE TYPE, and nothing else about it moved: the
-- data arms are the polymorphic unit, the product and sum arms are
-- products and sums of candidates, and the list arm is `All`.
--
-- THE RECURSIVE OCCURRENCE IS THE CONTINUATION'S PARAMETER.  `Red m u`
-- appears once in the observable arm, as the predicate `RP` is
-- indexed by, at a strictly smaller type.  That is the Girard-Tait
-- descent, unchanged; what changed is that the answer no longer
-- carries it, so the answer can be at `t`.
--
-- THE CEILING IS AN INDEX AND THE PREDICATE GROWS WITH IT -- a larger
-- ceiling admits more states, so it quantifies over more -- while a
-- connect descends to a SMALLER one.  It is met here by never asking
-- the lower ceiling's candidates to come back UP: they go down the raw
-- continuation at the ceiling the connect peeled to, and a
-- continuation built at the higher ceiling that has to cross to the
-- lower one is dropped to it, its candidates forgotten.  What comes
-- back up is not a candidate but a `fallen` successor, which is what
-- the caller's own ceiling can hold: it stands on the room having
-- fallen, and re-vouches from the store at the peeled accessibility
-- on every later call.  Weakening only ever runs from the higher
-- ceiling to the lower, which is the direction it is sound in.
--
-- DEAD ROUTE: re-indexing the candidate by the room WHILE THE ANSWER
--   STILL CARRIES A SATISFACTION COLUMN.  The connect's def comes back
--   proven at the inner ceiling and the arm owes the column at the
--   outer; weakening runs the other way and no instance of it closes
--   the gap.  Bypassed rather than reopened: nothing here comes back
--   proven, because nothing comes back at the element type at all.
Red : ∀ {n} {Γ : Ctx n} (m : ℕ) (t : Ty) → Val Γ t → Set₁
Red m unitᵗ     _        = ⊤
Red m boolᵗ     _        = ⊤
Red m natᵗ      _        = ⊤
Red m uniqᵗ     _        = ⊤
Red m (s ×ᵗ t)  (a , b)  = Red m s a × Red m t b
Red m (s +ᵗ t)  (inj₁ a) = Red m s a
Red m (s +ᵗ t)  (inj₂ b) = Red m t b
Red m (listᵗ t) vs       = All (Red m t) vs
Red {Γ = Γ} m (obs u) b =
  ∀ {S : Set} {t} {e : Closed Γ t} {lo} (κ : Path Γ lo u t) (pre : Pre κ)
  → (rp : RP {e = e} m (Red m u) S κ pre) (s : S)
  → (now : Tick) (sched : Sched Γ) (st : EvalSt e) → {-@0-}Room m sched st
  → {-@0-}PreHolds m κ pre sched st
  → Σ (Stream Γ t × Sched Γ × EvalSt e)
      (λ r → subscribeE⇓ {e = e} b κ now sched st r
           ⁰× Σ⁰ (Trace {e = e} m (Red m u) S κ pre rp s)
               (λ tr → PreHolds m κ (endPre tr) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                     × Kept κ (endPre tr) sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))))

-- A VALUE ENVIRONMENT IS REDUCIBLE WHEN EVERY ENTRY IS.  Terms are
-- open in a Θ telescope and a frame's closure pairs a term with one
-- such environment, so the fundamental theorem at terms has to be
-- stated under an environment rather than at closed terms alone.
RedEnv : ∀ {n} {Γ : Ctx n} (m : ℕ) {Θ : List Ty} → Env Γ Θ → Set₁
RedEnv m []ᵉ                  = ⊤
RedEnv m (_∷ᵉ_ {s = t} v vs)  = Red m t v × RedEnv m vs

-- an entry of a reducible environment is reducible
redLookup : ∀ {n} {Γ : Ctx n} {m Θ t} (ρ : Env Γ Θ) → RedEnv m ρ
          → (x : t ∈ Θ) → Red m t (lookupEnv ρ x)
redLookup (v ∷ᵉ vs) (p , ps) (here refl) = p
redLookup (v ∷ᵉ vs) (p , ps) (there x)   = redLookup vs ps x

-- THE LIST FOLD'S ACCUMULATOR LOOP, WITH THE STEP TAKEN AS A
-- HYPOTHESIS.  The step is one instance of the term face at an
-- environment two entries longer, and it does not vary along the list,
-- so the walk over the list is an ordinary recursion outside the
-- theorem's own cycle.
redFoldVals : ∀ {n} {Γ : Ctx n} {m Θ s u} (f : Tm Γ [] [] (s ∷ u ∷ Θ) u)
              (ρ : Env Γ Θ)
            → (∀ {x : Val Γ s} {ac : Val Γ u} → Red m s x → Red m u ac
                 → Red m u (evalWith f (x ∷ᵉ ac ∷ᵉ ρ)))
            → {vs : List (Val Γ s)} → All (Red m s) vs
            → {ac : Val Γ u} → Red m u ac
            → Red m u (foldVals f ρ vs ac)
redFoldVals f ρ step []       rac = rac
redFoldVals f ρ step (p ∷ ps) rac = redFoldVals f ρ step ps (step p rac)

-- THE STAGE.  One run of the frame's step, or a piece of one: what
-- it sent to the root and the state it left, with the derivation the
-- caller wants of it; the calls it made above, as a trace whose end
-- never stands where the stage began fallen; and the frame's ground
-- over the trace's end at the state it left, with what the frame kept
-- for the frame beneath.
record Stage {n} {Γ : Ctx n} {t} {e : Closed Γ t} (m : ℕ) {S : Set} {lo ℓ s u}
             (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t)
             (D : Stream Γ t → Sched Γ → EvalSt e → Set)
             (q : Pre κ) (rp : RP {e = e} m (Red m u) S κ q) (s₀ : S)
             (sched : Sched Γ) (st : EvalSt e) : Set₁ where
  constructor stage
  field
    out   : Stream Γ t
    sc    : Sched Γ
    st′   : EvalSt e
  field {-@0-}dv    : D out sc st′
  field tr    : Trace {e = e} m (Red m u) S κ q rp s₀
  field {-@0-}endOk : joinPre q (endPre tr) ≡ endPre tr
  field hd    : HeldF f
  field {-@0-}hl    : PreHolds m (f ↠[ le ] κ) (headPre hd (endPre tr)) sc st′
  field {-@0-}kp    : Kept (f ↠[ le ] κ) (headPre hd (endPre tr)) sched st sc st′

-- a stage that calls nothing and moves nothing
stage-nil : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {S : Set} {lo ℓ s u}
            (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t)
            {D : Stream Γ t → Sched Γ → EvalSt e → Set}
            (q : Pre κ) (rp : RP {e = e} m (Red m u) S κ q) (s₀ : S)
            {sched : Sched Γ} {st : EvalSt e}
            (out : Stream Γ t) → {-@0-}D out sched st
          → (h : HeldF f) → {-@0-}PreHolds m (f ↠[ le ] κ) (headPre h q) sched st
          → Stage m f le κ D q rp s₀ sched st
stage-nil f le κ q rp s₀ out d h hs = stage out _ _ d []ᵗ (join-idem q) h hs (kept-refl _ _)

-- a stage on fallen ground: whatever ran kept the two fields the room
-- reads, so the fall stands
fallenStage : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {S : Set} {lo ℓ s u}
              (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t)
              {D : Stream Γ t → Sched Γ → EvalSt e → Set}
              (rp : RP {e = e} m (Red m u) S κ fallen) (s₀ : S)
              {sched : Sched Γ} {st : EvalSt e}
              (out : Stream Γ t) (sc : Sched Γ) (st′ : EvalSt e) → {-@0-}D out sc st′
            → {-@0-}Keeps {e = e} sched st sc st′ → {-@0-}Fell m sched st → {-@0-}Sound (f ↠[ le ] κ) sc st′ → (h : HeldF f)
            → Stage m f le κ D fallen rp s₀ sched st
fallenStage f le κ rp s₀ out sc st′ d ks fell so h =
  stage out sc st′ d []ᵗ refl h (grounded (fell-keeps ks fell) so) tt

-- the derivation re-read
stage-map : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {S : Set} {lo ℓ s u}
            {f : Frame Γ s u} {le : lo ≤ ℓ} {κ : Path Γ ℓ u t}
            {D₁ D₂ : Stream Γ t → Sched Γ → EvalSt e → Set}
            {q : Pre κ} {rp : RP {e = e} m (Red m u) S κ q} {s₀ : S}
            {sched : Sched Γ} {st : EvalSt e}
          → {-@0-}(∀ {o sc s′} → D₁ o sc s′ → D₂ o sc s′)
          → Stage m f le κ D₁ q rp s₀ sched st → Stage m f le κ D₂ q rp s₀ sched st
stage-map g (stage out sc st′ d tr e h hl kp) = stage out sc st′ (g d) tr e h hl kp

-- the stage read from an earlier state that differs only at the
-- frame's own nodes
stage-rebase : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {S : Set} {lo ℓ s u}
               (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t)
               {D : Stream Γ t → Sched Γ → EvalSt e → Set}
               {q : Pre κ} {rp : RP {e = e} m (Red m u) S κ q} {s₀ : S}
               {sched₀ sched : Sched Γ} {st₀ st : EvalSt e}
             → {-@0-}nodeCt sched₀ ≤ nodeCt sched
             → {-@0-}(∀ k → k < nodeCt sched₀ → (T (any (_≡ᵇ k) (frameNodes f)) → ⊥)
                    → lookupNode k (EvalSt.nodes st) ≡ lookupNode k (EvalSt.nodes st₀))
             → {-@0-}EndsKept (f ↠[ le ] κ) sched₀ st₀ st
             → Stage m f le κ D q rp s₀ sched st → Stage m f le κ D q rp s₀ sched₀ st₀
stage-rebase f le κ ct off eks (stage out sc st′ d tr e h hl kp) =
  stage out sc st′ d tr e h hl (kept-shift f f le le κ h h (endPre tr) ct (λ _ _ ne → ne) off eks kp)

-- ONE STAGE AFTER ANOTHER.  The second begins where the first's trace
-- ended, on the first's ground; the traces append, the ground is the
-- second's, and what was kept composes.
stage-seq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {S : Set} {lo ℓ s u}
            {f : Frame Γ s u} {le : lo ≤ ℓ} {κ : Path Γ ℓ u t}
            {D₁ D₂ D₃ : Stream Γ t → Sched Γ → EvalSt e → Set}
            {q : Pre κ} {rp : RP {e = e} m (Red m u) S κ q} {s₀ : S}
            {sched : Sched Γ} {st : EvalSt e}
            (a : Stage m f le κ D₁ q rp s₀ sched st)
          → Stage m f le κ D₂ (endPre (Stage.tr a)) (endRP (Stage.tr a)) (endS (Stage.tr a))
                  (Stage.sc a) (Stage.st′ a)
          → {-@0-}(∀ {o sc s′} → D₂ o sc s′ → D₃ (Stage.out a ++ o) sc s′)
          → Stage m f le κ D₃ q rp s₀ sched st
stage-seq {f = f} {le} {κ} {q = q} a b glue =
  trans (end-++ (Stage.tr a) (Stage.tr b)) (Stage.endOk b) |>⁰ λ eqE →
  stage (Stage.out a ++ Stage.out b) (Stage.sc b) (Stage.st′ b) (glue (Stage.dv b))
       (Stage.tr a ++ᵗ Stage.tr b)
       (subst (λ p → joinPre q p ≡ p) (sym eqE) (join-chain q _ _ (Stage.endOk a) (Stage.endOk b)))
       (Stage.hd b)
       (subst (λ p → PreHolds _ (f ↠[ le ] κ) (headPre (Stage.hd b) p) _ _) (sym eqE) (Stage.hl b))
       (subst (λ p → Kept (f ↠[ le ] κ) (headPre (Stage.hd b) p) _ _ _ _) (sym eqE)
              (kept-join f le κ (Stage.hd a) (Stage.hd b) _ _ (Stage.endOk b) (Stage.kp a) (Stage.kp b)))

-- THE FRAME'S OWN WRITE, AS A STAGE: no call, no output, and the
-- frame's ground re-established at what it now holds, given that the
-- node written is one of the frame's own.
writeStage : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {S : Set} {lo ℓ s u}
             (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t)
             (p : Pre κ) (rp : RP {e = e} m (Red m u) S κ p) (s₀ : S)
             (nid : NodeId) (ns : NodeState Γ)
           → {-@0-}(∀ k → (T (any (_≡ᵇ k) (frameNodes f)) → ⊥) → (nid ≡ᵇ k) ≡ false)
           → (h′ : HeldF f) {sched : Sched Γ} {st : EvalSt e}
           → {-@0-}ConsistentF f h′ (record st { nodes = setNode nid ns (EvalSt.nodes st) })
           → (h : HeldF f) → {-@0-}PreHolds m (f ↠[ le ] κ) (headPre h p) sched st
           → Stage m f le κ (λ o sc s′ → (o ≡ []) × (sc ≡ sched)
                                       × (s′ ≡ record st { nodes = setNode nid ns (EvalSt.nodes st) }))
                   p rp s₀ sched st
writeStage f le κ p rp s₀ nid ns ownOff h′ {sched} {st} con h hs =
  stage [] sched (record st { nodes = setNode nid ns (EvalSt.nodes st) }) (refl , refl , refl) []ᵗ (join-idem p) h′
    (writeHolds f le κ p nid ns ownOff h′ con h hs) (writeKept f le κ p nid ns ownOff h′ h hs)
  where
  writeHolds : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {lo ℓ s u}
               (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (p : Pre κ)
               (nid : NodeId) (ns : NodeState Γ)
             → (∀ k → (T (any (_≡ᵇ k) (frameNodes f)) → ⊥) → (nid ≡ᵇ k) ≡ false)
             → (h′ : HeldF f) {sched : Sched Γ} {st : EvalSt e}
             → ConsistentF f h′ (record st { nodes = setNode nid ns (EvalSt.nodes st) })
             → (h : HeldF f) → PreHolds m (f ↠[ le ] κ) (headPre h p) sched st
             → PreHolds m (f ↠[ le ] κ) (headPre h′ p) sched (record st { nodes = setNode nid ns (EvalSt.nodes st) })
  writeHolds f le κ (standing pfs) nid ns ownOff h′ {sched} {st} con h (grounded ((_ , fr) , ap , hs) so) =
    grounded
      ( (con , fr) , ap
      , holdsFs-step κ pfs (λ k on _ → set-above nid k ns (EvalSt.nodes st) (ownOff k (λ onF → ap k onF on))) ≤-refl hs )
      (sub-ot (λ r∈ → r∈) ≤-refl so)
  writeHolds f le κ fallen nid ns ownOff h′ con h (grounded fell so) = grounded fell (sub-ot (λ r∈ → r∈) ≤-refl so)
  writeKept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {lo ℓ s u}
              (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (p : Pre κ)
              (nid : NodeId) (ns : NodeState Γ)
            → (∀ k → (T (any (_≡ᵇ k) (frameNodes f)) → ⊥) → (nid ≡ᵇ k) ≡ false)
            → (h′ : HeldF f) {sched : Sched Γ} {st : EvalSt e}
            → (h : HeldF f) → PreHolds m (f ↠[ le ] κ) (headPre h p) sched st
            → Kept (f ↠[ le ] κ) (headPre h′ p) sched st sched (record st { nodes = setNode nid ns (EvalSt.nodes st) })
  writeKept f le κ (standing pfs) nid ns ownOff h′ {sched} {st} h (grounded (_ , ap , _) _) =
    ≤-refl , (λ k _ ne _ → set-above nid k ns (EvalSt.nodes st) (ownOff k (λ onF → ne (∨-Tˡ onF)))) , λ _ _ _ ea → ea
  writeKept f le κ fallen nid ns ownOff h′ h fell = tt

-- WHAT A SUBSCRIBING FRAME'S STEP IS: given the frame's ground over a
-- standing path, a call, and a state under the ceiling, a stage whose
-- derivation is the fold of the frame's own path at that call.
--
-- AND A GUARD ON THE COLUMN, WHICH THE STEP IS HANDED AND HANDS BACK.
-- On standing ground the store agrees with the column, so a fact about
-- the column that every step of the frame re-establishes is a fact
-- about the store at every call -- carried by the continuation, with
-- nothing global to thread.
SubStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} (f : Frame Γ s u) → (HeldF f → Set) → ℕ → Set₁
SubStep {Γ = Γ} {t} {e} {s} {u} f G m =
  ∀ {S : Set} {lo ℓ} (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (pfs : PreFs κ)
    (rp : RP {e = e} m (Red m u) S κ (standing pfs)) (s₀ : S) (h : HeldF f) → G h
  → (now : Tick) (vals : List (Val Γ s)) → All (Red m s) vals → (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) → {-@0-}Room m sched st
  → {-@0-}PreHolds m (f ↠[ le ] κ) (standing (h , pfs)) sched st
  → Σ (Stage m f le κ (λ o sc s′ → foldPath⇓ {e = e} now (f ↠[ le ] κ) vals fin sched st (o , sc , s′))
             (standing pfs) rp s₀ sched st)
      (λ r → G (Stage.hd r))

-- THE INNER'S BASE: ITS EXIT FRAME OVER THE REST OF THE PATH, FOLDED
-- RAW.  It is the one continuation an inner subscribed from the raw
-- fold is handed, so the frames the inner stacks step live above it and
-- no arm's extension re-enters the raw fold.  It holds no candidates,
-- so its column is what the store holds, and its successor stands there
-- again -- or on `fallen`, where the fold connected.

-- IT IS BUDGETED BY THE QUEUE ITS OWN COLUMN PINS.  It is the only place
-- a merge's queue is nonempty at an inner's finish: on standing ground
-- the column guards keep it empty, but a share's fan-out reaches the
-- outer while the lane is busy, and a raw finish meets what it queued.
-- Standing ground makes the store read back the column at every fold, so
-- the finish drains exactly the queue the base was built over; each
-- drained inner's base is built over the queue with that inner popped,
-- and a drain reading its queue back longer than it left it has spent
-- room and peels it.  The accessibility is the column's, so no fold
-- transports it.

-- DEAD ROUTE: the base folded raw at the same room, unbudgeted.  The
--   base reaches the drain's inner as an argument to its candidate, and
--   a call there is not guarded by the `fold` copattern: nothing on the
--   cycle through `rawInner` is smaller.

-- THE STATEMENT EVERY ARM MAKES: the candidate for one closure over a
-- reducible environment, funded by three accessibilities.  The room's
-- is outermost and only a share's connect peels it; under it the input
-- bound and the term size fall at every former.  Every member of the
-- candidate's cycle carries all three, so the checker reads the whole
-- order off the call sites.
Arm : ∀ {n} {Γ : Ctx n} {Θ t} → Exp Γ [] [] Θ t → Set₁
Arm {Γ = Γ} {Θ = Θ} {t = t} b =
  ∀ (ρ : Env Γ Θ) {m} → RedEnv m ρ
  → (k : ℕ) → T (inputsBelowᵉ k b) → {-@0-}Acc _<_ k
  → {-@0-}Acc _<_ (gsizeᵉ b) → {-@0-}Acc _<_ m → Red {Γ = Γ} m (obs t) (Θ , b , ρ)

-- A VALUE OF A DATA TYPE IS A CANDIDATE AT EVERY CEILING, AND ASKS
-- NOTHING OF IT: no observable sits anywhere inside it, so nothing is
-- subscribed and no accessibility is spent.
red-data : ∀ {n} {Γ : Ctx n} {m} (t : Ty) → T (isData t) → (v : Val Γ t) → Red m t v
red-data unitᵗ     _  _        = tt
red-data boolᵗ     _  _        = tt
red-data natᵗ      _  _        = tt
red-data uniqᵗ     _  _        = tt
red-data (s ×ᵗ u)  ok (a , b)  with isData s in es
... | true  = red-data s (subst T (sym es) tt₀) a , red-data u ok b
... | false = ⊥-elim ok
red-data (s +ᵗ u)  ok (inj₁ a) with isData s in es
... | true  = red-data s (subst T (sym es) tt₀) a
... | false = ⊥-elim ok
red-data (s +ᵗ u)  ok (inj₂ b) with isData s in es
... | true  = red-data u ok b
... | false = ⊥-elim ok
red-data (listᵗ u) ok []       = []ᵃ
red-data (listᵗ u) ok (x ∷ xs) = red-data u ok x ∷ᵃ red-data (listᵗ u) ok xs
red-data (obs _)   ()

-- THE SCRIPTED SLOT.  Folds what the slot script says through the
-- continuation with a data candidate beside every value; the live hot
-- slot registers and folds nothing; the cold slot with a tail registers
-- FIRST and then folds its prefix, since a synchronous value can cut
-- this very chain and a cut severs registrations.
red-scripted : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo Θ S}
    (i : Fin n) (ρ : Env Γ Θ) (k : ℕ) → T (toℕ i <ᵇ k) → {-@0-}Acc _<_ k
  → (κ : Path Γ lo (lookup Γ i) t) (below : toℕ i < lo) (pre : Pre κ)
  → ∀ {m} (rp : RP {e = e} m (Red m (lookup Γ i)) S κ pre) (s : S)
  → (now : Tick) (sched : Sched Γ)
  → (sc : ObservableInput (Val Γ (lookup Γ i))) {oks : T (isData (lookup Γ i))}
  → Sched.slots sched i ≡ scripted {ok = oks} sc
  → ∀ (st : EvalSt e) → {-@0-}Acc _<_ m → {-@0-}Room m sched st → {-@0-}PreHolds m κ pre sched st
  → Σ (Stream Γ t × Sched Γ × EvalSt e)
      (λ r → subscribeE⇓ {e = e} (Θ , input i , ρ) κ now sched st r
           ⁰× Σ⁰ (Trace {e = e} m (Red m (lookup Γ i)) S κ pre rp s)
               (λ tr → PreHolds m κ (endPre tr) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                     × Kept κ (endPre tr) sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))))
red-scripted i ρ k ok aK κ below pre rp s now sched (hot async) slEq st aM rm h
  with memberSource (toℕ i) (EvalSt.completedSources st) in doneEq
... | true =
      answer rp s (call now [] (ofColumn κ pre []ᵃ) true sched st rm h) λ a →
      let an = Answered.an a
      in _ , subs-hot-done below slEq doneEq (der an) , a ∷ᵗ []ᵗ , Ans.holds′ an , kept an
... | false =
      _ , subs-hot-live below slEq doneEq refl , []ᵗ
    , holds-step κ pre (λ _ _ _ → refl) ≤-refl (λ x → x)
        (register-sound {sched = sched} {st = st} (freshId regᵏ (Sched.mint sched)) (atSlot i) (lowerFloor below κ)
           ≤-refl (lower-end below κ) (λ k′ on → inj₁ (subst T (lower-nodes below κ k′) on))
           (λ so′ → lower-distinct below κ (distinct so′)))
        h
    , kept-step κ pre (pres (λ _ _ → refl)) ≤-refl
        (ends-register {κ = κ} {sched = sched} {st = st} (freshId regᵏ (Sched.mint sched)) (atSlot i) (lowerFloor below κ)
           (λ k′ on → inj₁ (subst T (lower-nodes below κ k′) on)))
red-scripted i ρ k ok aK κ below pre rp s now sched (cold sync []) {oks} slEq st aM rm h =
  answer rp s (call now sync (ofColumn κ pre (red-data (listᵗ _) oks sync)) true sched st rm h) λ a →
  let an = Answered.an a
  in _ , subs-cold-sync below slEq (der an) , a ∷ᵗ []ᵗ , Ans.holds′ an , kept an
red-scripted {Γ = Γ} {lo = lo} i ρ k ok aK κ below pre rp s now sched (cold sync (d ∷ ds)) {oks} slEq st aM rm h =
  let src    = freshId sourceᵏ (Sched.mint sched)
      ord    = freshId ordinalᵏ (Sched.mint sched)
      rid    = freshId regᵏ (Sched.mint sched)
      sched₁ = record sched
                 { mint = setAt regᵏ (suc rid) (setAt sourceᵏ (suc src) (setAt ordinalᵏ (suc ord) (Sched.mint sched)))
                 ; live = record { source = src ; ordinal = ord ; elemTy = lookup Γ i
                                 ; pending = resolve now (d ∷ ds) }
                          ∷ Sched.live sched }
      st₁    = register rid (atDyn src lo) κ st
  in answer rp s (call now sync (ofColumn κ pre (red-data (listᵗ _) oks sync)) false sched₁ st₁ rm
                   (holds-step κ pre {sched′ = sched₁} {st′ = st₁} (λ _ _ _ → refl) ≤-refl (λ x → x)
                      (register-sound {sched = sched} {sched′ = sched₁} {st = st} rid (atDyn src lo) κ ≤-refl refl (λ k′ on → inj₁ on) (λ so′ → distinct so′))
                      h)) λ a →
  let an = Answered.an a
  in _ , subs-cold-async below slEq refl refl refl (der an) , a ∷ᵗ []ᵗ , Ans.holds′ an
   , kept-before κ (pres (λ _ _ → refl)) ≤-refl
       (ends-register {κ = κ} {sched = sched} {st = st} rid (atDyn src lo) κ (λ k′ on → inj₁ on)) (Ans.pre′ an) (kept an)

-- A FOLD IS ITS ACCUMULATOR THREADED ALONG THE BATCH, and so is the
-- claim about it: each output IS the next accumulator, so one walk
-- delivers both the candidate at every emitted value and the candidate
-- at what gets written back.
redScanVals : ∀ {n} {Γ : Ctx n} {m s u} (fn : FnClo Γ (u ×ᵗ s) u)
            → (∀ {v} → Red m (u ×ᵗ s) v → Red m u (applyClo fn v))
            → {a : Val Γ u} → Red m u a
            → {vals : List (Val Γ s)} → All (Red m s) vals
            → All (Red m u) (proj₁ (scanVals fn a vals)) × Red m u (proj₂ (scanVals fn a vals))
redScanVals fn rf ra []ᵃ       = []ᵃ , ra
redScanVals fn rf ra (p ∷ᵃ ps) =
  let q = rf (ra , p)
  in q ∷ᵃ proj₁ (redScanVals fn rf q ps) , proj₂ (redScanVals fn rf q ps)

-- WHAT THE SCAN FRAME HOLDS A CANDIDATE FOR: the accumulator its cell
-- holds, whenever it holds one of the frame's own type
ScanHeld : ∀ {n} {Γ : Ctx n} (m : ℕ) (u : Ty) → Maybe (NodeState Γ) → Set₁
ScanHeld {Γ = Γ} m u h = ∀ {a : Val Γ u} → h ≡ just (cell-st a) → Red m u a

scanRed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s u} (fn : FnClo Γ (u ×ᵗ s) u)
            (rf : ∀ {v} → Red m (u ×ᵗ s) v → Red m u (applyClo fn v))
            (nid : NodeId) {vals : List (Val Γ s)} (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
            (h : Maybe (NodeState Γ))
        → All (Red m s) vals → ScanHeld m u h
        → All (Red m u) (proj₁ (scanDispatch {e = e} fn nid vals fin sched st h)) × ScanHeld m u (scanHeld fn vals h)
scanRed {u = u} fn rf nid fin sched st (just (cell-st {w} a)) ps rh with w ≟ᵗ u
... | no  _    = []ᵃ , rh
... | yes refl =
      proj₁ (redScanVals fn rf (rh refl) ps)
    , λ eq → subst (Red _ u) (cell-inj eq) (proj₂ (redScanVals fn rf (rh refl) ps))
scanRed fn rf nid fin sched st (just (take-st _))           ps rh = []ᵃ , rh
scanRed fn rf nid fin sched st (just (batchSync-st _ _ _))  ps rh = []ᵃ , rh
scanRed fn rf nid fin sched st (just (mergeAll-st _ _ _ _)) ps rh = []ᵃ , rh
scanRed fn rf nid fin sched st (just (switch-st _ _))       ps rh = []ᵃ , rh
scanRed fn rf nid fin sched st (just (exhaust-st _ _))      ps rh = []ᵃ , rh
scanRed fn rf nid fin sched st nothing                      ps rh = []ᵃ , rh

-- WHAT THE BATCH FRAME HOLDS A CANDIDATE FOR: the buffer its bracket
-- holds, whenever it holds one of the frame's own element type.  The
-- buffer is only ever a concatenation of arrivals, so the candidates
-- are the arrivals' own.
BatchHeld : ∀ {n} {Γ : Ctx n} (m : ℕ) (u : Ty) → Maybe (NodeState Γ) → Set₁
BatchHeld {Γ = Γ} m u h =
  ∀ {sync} {bur : List (Val Γ u)} {done} → h ≡ just (batchSync-st {s = u} sync bur done) → All (Red m u) bur

-- the bracket the install opens holds nothing
batch₀ : ∀ {n} {Γ : Ctx n} {m u} → BatchHeld {Γ = Γ} m u (just (batchSync-st {s = u} true [] false))
batch₀ refl = []ᵃ

-- a regrouping of candidates is candidates for the groups
redBatch : ∀ {n} {Γ : Ctx n} {m s} (sync : Bool) {vals : List (Val Γ s)}
         → All (Red m s) vals → All (Red m (s ×ᵗ listᵗ s)) (batchVals sync vals)
redBatch _     []ᵃ       = []ᵃ
redBatch true  (p ∷ᵃ ps) = (p , ps) ∷ᵃ []ᵃ
redBatch false (p ∷ᵃ ps) = (p , []ᵃ) ∷ᵃ redBatch false ps

batchRed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s} (nid : NodeId) {vals : List (Val Γ s)} (fin : Bool)
             (sched : Sched Γ) (st : EvalSt e) (h : Maybe (NodeState Γ))
         → All (Red m s) vals → BatchHeld m s h
         → All (Red m (s ×ᵗ listᵗ s)) (proj₁ (batchDispatch {e = e} nid vals fin sched st h))
         × BatchHeld m s (batchHeld vals fin h)
batchRed {s = s} nid fin sched st (just (batchSync-st {w} true bur done)) ps rh with w ≟ᵗ s
... | no  _    = []ᵃ , rh
... | yes refl = []ᵃ , λ { refl → ++⁺ (rh refl) ps }
batchRed {s = s} nid fin sched st (just (batchSync-st {w} false bur done)) ps rh with w ≟ᵗ s
... | no  _    = redBatch false ps , rh
... | yes refl = ++⁺ (redBatch true (rh refl)) (redBatch false ps) , λ { refl → []ᵃ }
batchRed nid fin sched st (just (cell-st _))           ps rh = []ᵃ , rh
batchRed nid fin sched st (just (take-st _))           ps rh = []ᵃ , rh
batchRed nid fin sched st (just (mergeAll-st _ _ _ _)) ps rh = []ᵃ , rh
batchRed nid fin sched st (just (switch-st _ _))       ps rh = []ᵃ , rh
batchRed nid fin sched st (just (exhaust-st _ _))      ps rh = []ᵃ , rh
batchRed nid fin sched st nothing                      ps rh = []ᵃ , rh

batchStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s} (nid : NodeId)
          → FrameStep {e = e} (batchSync-f {s = s} nid) (Red m s) (Red m (s ×ᵗ listᵗ s)) (BatchHeld m s)
batchStep {s = s} nid = record
  { step      = batchStepped nid
  ; step-⇓    = λ {_} {κ} {now} h vals fin sched st c →
                  subst (λ x → stepFrame⇓ now (batchSync-f nid) κ vals fin sched st
                                 (injectRoot {u = s ×ᵗ listᵗ s} (batchDispatch nid vals fin sched st x)))
                        c step-batchSync
  ; step-red  = λ {h} {vals} {fin} {sched} {st} ps rh → batchRed nid fin sched st h ps rh
  ; step-cons = λ h vals fin sched st c → batchCons nid vals fin sched st h c
  ; step-off  = λ h vals fin sched st k ne → batchOff nid vals fin sched st h k (head-off nid [] k ne)
  ; step-ct   = λ h vals fin sched st → batchCt nid vals fin sched st h
  ; step-reg  = λ h vals fin sched st r∈ → subst (_ ∈_) (batchReg nid vals fin sched st h) r∈ }

-- lowering the bit keeps the buffer, so it keeps the buffer's
-- candidates; a bracket of another type is emptied
downHeld : ∀ {n} {Γ : Ctx n} {m} (u : Ty) (x : Maybe (NodeState Γ))
         → BatchHeld m u x → BatchHeld m u (just (batchDown u x))
downHeld u (just (batchSync-st {w} sync bur done)) rh with w ≟ᵗ u
... | no  _    = λ { refl → []ᵃ }
... | yes refl = λ { refl → rh refl }
downHeld u (just (cell-st _))           rh = λ { refl → []ᵃ }
downHeld u (just (take-st _))           rh = λ { refl → []ᵃ }
downHeld u (just (mergeAll-st _ _ _ _)) rh = λ { refl → []ᵃ }
downHeld u (just (switch-st _ _))       rh = λ { refl → []ᵃ }
downHeld u (just (exhaust-st _ _))      rh = λ { refl → []ᵃ }
downHeld u nothing                      rh = λ { refl → []ᵃ }
