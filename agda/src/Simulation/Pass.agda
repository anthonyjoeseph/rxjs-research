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

open import Data.Bool    using (Bool; true; false; if_then_else_)
open import Data.Fin     using (Fin; toℕ; _↑ʳ_; _↑ˡ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (tt)
open import Data.List    using (List; []; _∷_; _++_; map; concatMap)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; ++⁺) renaming (map to pw-map)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.Bool.ListAction using (any)
open import Data.Fin.Properties using (toℕ<n; toℕ-↑ˡ; toℕ-↑ʳ; ↑ʳ-injective) renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Nat     using (ℕ; suc; _≤_; _<_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl; <⇒≢; <-≤-trans; m≤m+n)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Vec     using (lookup)
open import Data.List.Properties using (++-assoc; ++-identityʳ; map-id)
open import Relation.Nullary using (yes; no)
open import Function using (case_of_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Rx.Prim      using (Tick; valueᵖ; completeᵖ)
open import Rx.Exp       using (Ty; Ctx; Closed; Val; Env; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; _≟ᵗ_; uniqᵗ; unitᵗ; _×ᵗ_; _+ᵗ_; obs; listᵗ; FnClo; applyClo; Tm; varᵗ; unit̂; pairᵗ; inlᵗ; inrᵗ; sndᵗ)
open import Rx.Evaluator using (Stream; Sched; EvalSt; NodeId; NodeState; Arrival; arrVal; arrTy; arrTick; cascadeClose;
  shareSpend; shareDying; memberSource; Path; share-sink; _↠[_]_; scan-f; take-f; map-f; batchSync-f;
  thru-outer; from-inner; mergeAllᵒ; lookupNode; mergeAll-st; echoᵗ; thruEvents; thruWrap;
  setNode; exhaust-st; switch-st; switchKill; hasRoom; consumeUsable; switchᵒ; exhaustᵒ; RegId;
  RegRow; AtFloor; atDyn; atSlot; chainsOf; shareAdmit; shareFinish; aliveThroughᶠ)
open import Rx.Evaluator.Domain using (flatOp; foldPath⇓; fold-root; fold-step; stepFrame⇓; step-map; step-thru-outer; step-from-inner; react-false; react-alive; react-dead; innerFinish⇓; finish-switch-clear; finish-exhaust-clear; finish-nil; thruWalk⇓; walk-nil; walk-echo; walk-cons;
  thruConsume⇓; inner; consume-all-sub; consume-all-enqueue; consume-all-nil; consume-exhaust-sub; consume-exhaust-nil; consume-switch-sub; consume-switch-nil; subscribeInner⇓; subscribeE⇓; chainStep⇓; chain-step;
  cascadeGo⇓; casc-nil; casc-cut; casc-live; shareGo⇓; go-nil; go-cut; go-live; dispatchShare⇓; disp; shareWalk⇓; walk-end; walk-more; fold-sink)
open import SExp.Syntax  using (Kinds; plainᵏ; plainᵗ; emitᵗ; hotᵏ; sharedᵏ)
open import SExp.Elaborate using (inputStampᵖ; restampᵛ; subscribeᵛ; deliveryᵛ; flatStepᵛ; elemᵛ; explodeᵛ; FlatSᵗ)
open import Simulation.Schedules using (HeadOf)
open import Simulation.Stores using (srcCount; V; EmitRel; ObsRel; Flattener; FlatNodes; CurRel; merge~; switch~; exhaust~; Src;
  SrcPair; sharedEq; PathRel; root~; sink~; map~; scan~; take~; takeWhile~; spent~;
  spentWhile~; outerElem~; outerExplode~; inner~; lane~; elab; deferInner~; InputBlock; block; hotEq;
  RowRel; read~; cold~; defer~; RegRel; []; _∷_; mach; MachRow; hot~; partner-row; Store; Arr)
open import Simulation.After using (readᴾ; readᴵ; PairedR; module Kept)
open import Simulation.Cut using (cut-kill)
open import Simulation.Take using (module Takes)
open import Simulation.Scan using (module Scans)
open import Simulation.Arm using (module Arms; Unmoved; unmoved; Clear; ClearI; missed; fold-unmoved; on-drop; unthru; step-clear; fold-clear; consume-clear; adv)
open import Simulation.Sweep using (t≢f)
open import Decide using (≡ᵇ-refl; ≡ᵇ→≡)
open import Simulation.Write using (module Write; key-same; vals-same)
open import Simulation.Walk using (walk)
open import Simulation.Grow using (nodes-grow; flatG; pathG; fresh-off)
open import Rx.Evaluator.Freshness using (nodeCt)
open import Simulation.Elem using (pw-one; pw-none; paysOf; values-decode; echoList; elem-run; quiet-run)
open import Rx.Evaluator.Reducible.Support using (Sound; fresh-path; FreshPath; switchKill-ct; sub-rule; switchKill-nodes; drop-ot; head-on;
  self-node; sub-ot; Agree; Rule; sink-sound; admit-ot; admit-agree; termini)
open import Rx.Evaluator.Reducible.Rule-Kept using (step-kept; fold-kept)

-- a minted source's chain, as the registration it was read from
dynRow : ∀ {n} {Γ : Ctx n} {t} (a : Arrival Γ) → RegId × AtFloor Γ (arrTy a) t → RegRow Γ t
dynRow a (rid , lo , p) = rid , atDyn (Arrival.source a) lo , (arrTy a , p)

-- a minted source's chains, paired as `PairedR` pairs rows
Paired : ∀ {n} {Γ : Ctx n} {t} {κ : Kinds n} {π NP NI LP LI rs rs′}
       → RegRel κ π {t} NP NI LP LI rs rs′ → List RegId → List RegId → (a : Arrival Γ) (a′ : Arrival (plainᵏ Γ κ))
       → RegId × AtFloor Γ (arrTy a) t → RegId × AtFloor (plainᵏ Γ κ) (arrTy a′) (emitᵗ t) → Set
Paired rr CP CI a a′ c c′ = PairedR rr CP CI (dynRow a c) (dynRow a′ c′)

-- a node a consume can use, read as one it cannot
unusable : ∀ {n} {Γ : Ctx n} op w {N N′ : Maybe (NodeState Γ)}
         → N ≡ N′ → consumeUsable op w N ≡ false → consumeUsable op w N′ ≡ true → ⊥
unusable _ _ refl f u = t≢f (trans (sym u) f)

usable-self : ∀ u → ⌊ u ≟ᵗ u ⌋ ≡ true
usable-self u with u ≟ᵗ u
... | yes _ = refl
... | no ¬e = ⊥-elim (¬e refl)

-- the fold a chain step runs
unchain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {a : Arrival Γ} {vs fin x sched st r}
        → chainStep⇓ {e = e} a vs fin x sched st r → foldPath⇓ (arrTick a) (proj₂ x) vs fin sched st r
unchain (chain-step d) = d

-- a chain step marks its row delivered, which no relation reads
delivered : ∀ {n} {Γ : Ctx n} {t} {κ : Kinds n} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
              {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
          → Store κ sP stP sI stI → ∀ {x y}
          → Store κ sP (record stP { delivered = x }) sI (record stI { delivered = y })
delivered s = record
  { π = π ; π-keys = π-keys ; π-vals = π-vals ; pairs-below = pairs-below ; sources = sources ; numbers = numbers ; distinct = distinct
  ; sync = sync ; rows = rows ; latches = latches ; bounded = bounded ; swept = swept ; uncut = uncut ; rids = rids ; fresh-ids = fresh-ids ; above = above ; census = census ; owned = owned
  ; ruleP = sub-rule (λ r∈ → r∈) ≤-refl ruleP ; ruleI = sub-rule (λ r∈ → r∈) ≤-refl ruleI }
  where open Store s

-- the arrival's pair against the rows is as it was, since the rows are
delivered-arr : ∀ {n} {Γ : Ctx n} {t} {κ : Kinds n} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
                  {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
                  {S : Store κ sP stP sI stI} {x y s s′ u u′}
              → Arr S s s′ u u′ → Arr (delivered S {x} {y}) s s′ u u′
delivered-arr ar = record { boundP = boundP ; boundI = boundI ; rows = rows ; lists = lists } where open Arr ar

-- a share marked dying on both sides, which no relation reads
dying : ∀ {n} {Γ : Ctx n} {t} {κ : Kinds n} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
          {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
      → Store κ sP stP sI stI → ∀ {x y}
      → Store κ sP (record stP { dying = x }) sI (record stI { dying = y })
dying s = record
  { π = π ; π-keys = π-keys ; π-vals = π-vals ; pairs-below = pairs-below ; sources = sources ; numbers = numbers ; distinct = distinct
  ; sync = sync ; rows = rows ; latches = latches ; bounded = bounded ; swept = swept ; uncut = uncut ; rids = rids ; fresh-ids = fresh-ids ; above = above ; census = census ; owned = owned
  ; ruleP = sub-rule (λ r∈ → r∈) ≤-refl ruleP ; ruleI = sub-rule (λ r∈ → r∈) ≤-refl ruleI }
  where open Store s

dying-arr : ∀ {n} {Γ : Ctx n} {t} {κ : Kinds n} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
              {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
              {S : Store κ sP stP sI stI} {x y s s′ u u′}
          → Arr S s s′ u u′ → Arr (dying S {x} {y}) s s′ u u′
dying-arr ar = record { boundP = boundP ; boundI = boundI ; rows = rows ; lists = lists } where open Arr ar

module _ {m} {Δ : Ctx m} {t} {lo} {j : Fin m} {h : lo ≤ toℕ j} where

  -- A STAMPED SHARE'S SINK, its fold read at the type the share holds
  sink-inv : ∀ {e : Closed Δ t} {now u} (ε : lookup Δ j ≡ u) {es : List (Val Δ u)} {fin sched st r}
           → foldPath⇓ {e = e} now (subst (λ u → Path Δ lo u t) ε (share-sink j h)) es fin sched st r
           → dispatchShare⇓ now j h (map (subst (Val Δ) (sym ε)) es) fin sched st r
  sink-inv refl {es} (fold-sink d) = subst (λ xs → dispatchShare⇓ _ j h xs _ _ _ _) (sym (map-id es)) d

  sink-intro : ∀ {e : Closed Δ t} {now u} (ε : lookup Δ j ≡ u) {es : List (Val Δ u)} {fin sched st r}
             → foldPath⇓ {e = e} now (share-sink j h) (map (subst (Val Δ) (sym ε)) es) fin sched st r
             → foldPath⇓ now (subst (λ u → Path Δ lo u t) ε (share-sink j h)) es fin sched st r
  sink-intro refl {es} d = subst (λ xs → foldPath⇓ _ (share-sink j h) xs _ _ _ _) (map-id es) d

  sink-ok : ∀ {e : Closed Δ t} {u} (ε : lookup Δ j ≡ u) {sched st}
          → Rule {e = e} sched st → Sound (subst (λ u → Path Δ lo u t) ε (share-sink j h)) sched st
  sink-ok refl ru = sink-sound j h ru

-- a share's admitted rows agree, by the rule's termini
admit-agrees : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} (i : Fin m) {sched : Sched Δ} {st : EvalSt e} → Rule sched st
             → ∀ {a b} → a ∈ shareAdmit i (EvalSt.registry st) → b ∈ shareAdmit i (EvalSt.registry st)
             → Agree (proj₂ a) (proj₂ b)
admit-agrees i {st = st} ru = admit-agree i st (termini ru)

-- A PLAIN CHAIN AT A SLOT AND THE REGISTRATION THE ELABORATION READ IT THROUGH:
-- the stamped slot's share fans out to exactly the rows the plain run walks
data SlotPair {n} {Γ : Ctx n} {t} {κ : Kinds n} {π NP NI LP LI rs rs′}
              (rr : RegRel κ π {t} NP NI LP LI rs rs′) (CP CI : List RegId) (i : Fin n) {u : Ty}
            : RegId × AtFloor Γ u t
            → RegId × Path (plainᵏ Γ κ) (suc (toℕ (n ↑ʳ i))) (lookup (plainᵏ Γ κ) (n ↑ʳ i)) (emitᵗ t) → Set where
  slotpair : ∀ {rid rid′ p p′}
           → PairedR rr CP CI (rid , atSlot i , (u , p)) (rid′ , atSlot (n ↑ʳ i) , (lookup (plainᵏ Γ κ) (n ↑ʳ i) , p′))
           → SlotPair rr CP CI i (rid , suc (toℕ i) , p) (rid′ , p′)

-- a share's admitted reader, at the floor its slot puts it
ShareSlot : ∀ {n} {Γ : Ctx n} {t} {κ : Kinds n} {π NP NI LP LI rs rs′}
          → RegRel κ π {t} NP NI LP LI rs rs′ → List RegId → List RegId → (i : Fin n)
          → RegId × Path Γ (suc (toℕ i)) (lookup Γ i) t
          → RegId × Path (plainᵏ Γ κ) (suc (toℕ (n ↑ʳ i))) (lookup (plainᵏ Γ κ) (n ↑ʳ i)) (emitᵗ t) → Set
ShareSlot rr CP CI i c d = SlotPair rr CP CI i (proj₁ c , suc (toℕ i) , proj₂ c) d

-- the impl's tail below a restamp, read off the restamp's path
tail-of : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {ℓ₂ ℓ₃ ℓ₄ s u w} {C : FnClo Γ (u ×ᵗ s) u} {D : FnClo Γ u w} {ks k}
            {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {q : Path Γ ℓ₄ w t} {sched} {st : EvalSt e}
        → Clear k (scan-f C ks ↠[ h₃ ] (map-f D ↠[ h₄ ] q)) sched st → ClearI k ks q sched st
tail-of {ks = ks} (on , so) =
  (on-drop (on-drop on) , drop-ot _ _ _ (drop-ot _ _ _ so)) , on-drop (head-on _ _ _ ks (self-node ks []) so)

-- two pointwise lists, one pair apart from a common tail
cons-skip : ∀ {A B : Set} {P : A → B → Set} {xs ys xs′ ys′} → xs ≡ xs′ → ys ≡ ys′ → Pointwise P xs′ ys′ → Pointwise P xs ys
cons-skip refl refl pw = pw

-- the same, for a pair that does contribute one chain on each side
cons-take : ∀ {A B : Set} {P : A → B → Set} {xs ys x y xs₁ ys₁} → xs ≡ x ∷ xs₁ → ys ≡ y ∷ ys₁ → P x y → Pointwise P xs₁ ys₁ → Pointwise P xs ys
cons-take refl refl p pw = p ∷ pw

-- a row at the share's own slot and type is admitted next
admit-slot : ∀ {m} {Δ : Ctx m} {t} {k : Fin m} {rid u} {p : Path Δ (suc (toℕ k)) u t} {rest}
           → (e′ : u ≡ lookup Δ k)
           → Σ _ λ q → shareAdmit k ((rid , atSlot k , (u , p)) ∷ rest) ≡ (rid , q) ∷ shareAdmit k rest
                       × _≡_ {A = RegRow Δ t} (rid , atSlot k , (lookup Δ k , q)) (rid , atSlot k , (u , p))
admit-slot {Δ = Δ} {k = k} {rid} {p = p} refl with k ≟ᶠ k | lookup Δ k ≟ᵗ lookup Δ k
... | yes refl | yes refl = p , refl , refl
... | yes refl | no ¬p    = ⊥-elim (¬p refl)
... | no ¬e    | _        = ⊥-elim (¬e refl)

-- a row at another slot is not admitted
admit-skip : ∀ {m} {Δ : Ctx m} {t} {k j : Fin m} {rid u} {p : Path Δ (suc (toℕ j)) u t} {rest}
           → k ≢ j → shareAdmit k ((rid , atSlot j , (u , p)) ∷ rest) ≡ shareAdmit k rest
admit-skip {Δ = Δ} {k = k} {j} {u = u} ne with k ≟ᶠ j | u ≟ᵗ lookup Δ k
... | no _  | _ = refl
... | yes e | _ = ⊥-elim (ne e)

-- A SWITCH'S CURRENT INNER, ONE PAIRING: the dying one on one side is
-- the dying one on the other
cur-here : ∀ {π : List (NodeId × List NodeId)} {c c′ j j′} → Unique (map proj₁ π) → (c , c′ ∷ []) ∈ π → (j , j′ ∷ []) ∈ π
         → (c ≡ᵇ j) ≡ true → (c′ ≡ᵇ j′) ≡ true
cur-here {c = c} {c′} {j} keys pc pj e with ≡ᵇ→≡ c j e
... | refl with key-same keys pc pj
...   | refl = ≡ᵇ-refl c′

cur-there : ∀ {π : List (NodeId × List NodeId)} {c c′ j j′} → Unique (concatMap proj₂ π) → (c , c′ ∷ []) ∈ π → (j , j′ ∷ []) ∈ π
          → (c′ ≡ᵇ j′) ≡ true → (c ≡ᵇ j) ≡ true
cur-there {c = c} {c′} {j′ = j′} vals pc pj e with ≡ᵇ→≡ c′ j′ e
... | refl with vals-same vals pc pj (here refl) (here refl)
...   | refl = ≡ᵇ-refl c

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  open Arms {Γ = Γ} κ public
  open Takes {Γ = Γ} κ using (module Count)
  open Scans {Γ = Γ} κ using (module Cells)

  -- a pair the tail of a relation partners, the whole relation does
  slot-there : ∀ {t π NP NI LP LI r r′ rs rs′} (x : RowRel {Γ = Γ} κ π {t} NP NI LP LI r r′) {q : RegRel {Γ = Γ} κ π NP NI LP LI rs rs′}
                 {CP CI i u c d}
             → SlotPair q CP CI i {u} c d → SlotPair (x ∷ q) CP CI i c d
  slot-there x (slotpair (inj₁ c))           = slotpair (inj₁ c)
  slot-there x (slotpair (inj₂ (a , b , p))) = slotpair (inj₂ (a , b , inj₂ p))

  slot-mach : ∀ {t π NP NI LP LI r′ rs rs′} (x : MachRow {Γ = Γ} κ π {t} NP NI LP LI r′) {q : RegRel {Γ = Γ} κ π NP NI LP LI rs rs′}
                {CP CI i u c d}
            → SlotPair q CP CI i {u} c d → SlotPair (mach x q) CP CI i c d
  slot-mach x (slotpair p) = slotpair p

  -- A SHARE'S READERS PAIR UP, in order, with the rows its stamped share
  -- admits: a minted source's row is admitted by neither, and the impl's
  -- raw slot is below every stamped one
  share-rows′ : ∀ {t π NP NI LP LI rg rg′} {i : Fin n} {CP CI}
              → (rr : RegRel {Γ = Γ} κ π {t} NP NI LP LI rg rg′)
              → All (λ r → any (_≡ᵇ proj₁ r) CP ≡ false) rg → All (λ r → any (_≡ᵇ proj₁ r) CI ≡ false) rg′
              → Pointwise (ShareSlot rr CP CI i) (shareAdmit i rg) (shareAdmit (n ↑ʳ i) rg′)
  share-rows′ [] _ _ = []
  share-rows′ {i = i} (read~ {i = j} hk pr refl ∷ q) (uP ∷ usP) (uI ∷ usI) = case i ≟ᶠ j of λ where
    (no ne) →
      cons-skip (admit-skip ne) (admit-skip (λ x → ne (↑ʳ-injective n i j x)))
                (pw-map (slot-there _) (share-rows′ q usP usI))
    (yes refl) →
      let (_ , h , d)   = admit-slot {k = i} refl
          (_ , h′ , d′) = admit-slot {k = n ↑ʳ i} (sym ([ hotEq {Γ = Γ} κ i , sharedEq {Γ = Γ} κ i ] hk))
      in cons-take h h′ (slotpair (inj₂ (uP , uI , inj₁ (d , d′)))) (pw-map (slot-there _) (share-rows′ q usP usI))
  share-rows′ (cold~ sp ib pr refl ∷ q) (_ ∷ usP) (_ ∷ usI) = pw-map (slot-there _) (share-rows′ q usP usI)
  share-rows′ (defer~ sp pi lnP lnI pr refl ∷ q) (_ ∷ usP) (_ ∷ usI) = pw-map (slot-there _) (share-rows′ q usP usI)
  share-rows′ {i = i} (mach x@(hot~ {i = j} hot ib refl) q) usP (_ ∷ usI) =
    cons-skip refl
              (admit-skip (λ y → <⇒≢ (<-≤-trans (toℕ<n j) (m≤m+n n (toℕ i)))
                                     (sym (trans (sym (toℕ-↑ʳ n i)) (trans (cong toℕ y) (toℕ-↑ˡ j n))))))
              (pw-map (slot-mach x) (share-rows′ q usP usI))

  -- WHAT `elemᵛ` MAKES OF AN OUTER EMIT CARRYING ONE ELEMENT: an echo
  -- always, carrying the element's echoed value if it has one, beside
  -- the element's inner as the lane if it has one
  echoOf : ∀ {u} → Val Γ (unitᵗ +ᵗ u) → List (Val Γ u)
  echoOf (inj₁ _) = []
  echoOf (inj₂ v) = v ∷ []

  data LaneRel {u} : Val (plainᵏ Γ κ) (unitᵗ +ᵗ obs (emitᵗ u)) → Val Γ (unitᵗ +ᵗ obs u) → Set where
    no-lane : ∀ {a b} → LaneRel (inj₁ a) (inj₁ b)
    a-lane  : ∀ {o′ o} → ObsRel κ u o′ o → LaneRel (inj₂ o′) (inj₂ o)

  data Elem {u} : Val Γ (echoᵗ u) → Val (plainᵏ Γ κ) (echoᵗ (emitᵗ u)) → Set where
    elem : ∀ {w l x l′} → EmitRel κ u x (echoOf w) → LaneRel l′ l → Elem (w , l) (inj₂ x , l′)

  -- and of one carrying none: an echo carrying nothing, and no lane
  data QuietElem {u} : Val (plainᵏ Γ κ) (echoᵗ (emitᵗ u)) → Set where
    quiet-elem : ∀ {x a} → Bare {u} x → QuietElem (inj₂ x , inj₁ a)

  echo-rel : ∀ {u} {i : ℕ} e′ e → V κ (unitᵗ +ᵗ u) e′ e
           → Pointwise (λ x w → V κ u (proj₂ x) w) (map (i ,_) (echoList e′)) (echoOf e)
  echo-rel (inj₁ _) (inj₁ _) _ = []
  echo-rel (inj₂ _) (inj₂ _) r = r ∷ []
  echo-rel (inj₁ _) (inj₂ _) ()
  echo-rel (inj₂ _) (inj₁ _) ()

  lane-rel : ∀ {u} l′ l → V κ (unitᵗ +ᵗ obs u) l′ l → LaneRel l′ l
  lane-rel (inj₁ _) (inj₁ _) _ = no-lane
  lane-rel (inj₂ _) (inj₂ _) r = a-lane r
  lane-rel (inj₁ _) (inj₂ _) ()
  lane-rel (inj₂ _) (inj₁ _) ()

  elem-one : ∀ {u Θ ρ} e′ {w} → EmitRel κ (echoᵗ u) e′ (w ∷ []) → Elem w (applyClo (Θ , elemᵛ , ρ) e′)
  elem-one {u} {ρ = ρ} e′ {w} r =
    subst (Elem w) (sym (proj₁ (proj₂ run)))
          (elem (subst (λ l → Pointwise (λ x v → V κ u (proj₂ x) v) l (echoOf (proj₁ w))) (sym (proj₂ (proj₂ run)))
                       (echo-rel {i = proj₁ (proj₂ e′)} (proj₁ (proj₁ pw)) (proj₁ w) (proj₁ (proj₂ (proj₂ pw)))))
                (lane-rel (proj₂ (proj₁ pw)) (proj₂ w) (proj₂ (proj₂ (proj₂ pw)))))
    where
    pw = pw-one (paysOf {Γ = plainᵏ Γ κ} {a = plainᵗ (echoᵗ u)} (proj₁ e′))
                (subst (λ l → Pointwise (λ x v → V κ (echoᵗ u) (proj₂ x) v) l (w ∷ []))
                       (values-decode {Γ = plainᵏ Γ κ} {a = plainᵗ (echoᵗ u)} (proj₁ e′) (proj₁ (proj₂ e′)) (proj₁ (proj₂ (proj₂ e′))) (proj₂ (proj₂ (proj₂ e′)))) r)
    run = elem-run {t = u} ρ e′ (proj₁ (proj₁ pw)) (proj₂ (proj₁ pw)) (proj₁ (proj₂ pw))

  elem-quiet : ∀ {u Θ ρ} e′ → Bare {echoᵗ u} e′ → QuietElem {u} (applyClo (Θ , elemᵛ , ρ) e′)
  elem-quiet {u} {ρ = ρ} e′ b =
    subst (QuietElem {u}) (sym (proj₁ (proj₂ run)))
          (quiet-elem (subst (λ l → Pointwise (λ x v → V κ u (proj₂ x) v) l []) (sym (proj₂ (proj₂ run))) []))
    where
    run = quiet-run {t = u} ρ e′
            (pw-none (paysOf {Γ = plainᵏ Γ κ} {a = plainᵗ (echoᵗ u)} (proj₁ e′))
                     (subst (λ l → Pointwise (λ x v → V κ (echoᵗ u) (proj₂ x) v) l [])
                            (values-decode {Γ = plainᵏ Γ κ} {a = plainᵗ (echoᵗ u)} (proj₁ e′) (proj₁ (proj₂ e′)) (proj₁ (proj₂ (proj₂ e′))) (proj₂ (proj₂ (proj₂ e′)))) b))

  -- THE VALUE A POPPED SOURCE HANDS ITS CHAINS, on both sides: the head
  -- of each partnered source's pending list, at the row's source
  data Head (src src′ : ℕ) : ∀ {u u′} → List (Val Γ u) → List (Val (plainᵏ Γ κ) u′) → Set where
    head : ∀ {l l′ a a′} → Src κ l l′ → HeadOf l a → HeadOf l′ a′
         → Arrival.source a ≡ src → Arrival.source a′ ≡ src′
         → Head src src′ (arrVal a ∷ []) (arrVal a′ ∷ [])
    nohead : ∀ {u u′} → Head src src′ {u} {u′} [] []

  -- the related values at the root: the emits' payloads in order
  postulate
    root-values : ∀ {t es vs} → Carries {t} es vs → ∀ fin
      → Pointwise (λ x w → V κ t (proj₂ x) w)
          (readᴵ ((map valueᵖ es ++ (if fin then completeᵖ ∷ [] else [])) ∷ []))
          (readᴾ ((map valueᵖ vs ++ (if fin then completeᵖ ∷ [] else [])) ∷ []))

  module _ {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

    open Kept {Γ = Γ} κ {t} {ep} {ei}
    open Run {t} {ep} {ei} public
    open Count {t} {ep} {ei} using (take-arm; takeWhile-arm)
    open Cells {t} {ep} {ei} using (scan-arm)

    -- a share's readers, as registrations the store partners
    share-rows : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n}
               → Pointwise (ShareSlot (Store.rows S) (EvalSt.cancelled stP) (EvalSt.cancelled stI) i)
                   (shareAdmit i (EvalSt.registry stP)) (shareAdmit (n ↑ʳ i) (EvalSt.registry stI))
    share-rows S = share-rows′ (Store.rows S) (proj₁ (Store.uncut S)) (proj₂ (Store.uncut S))


    ----------------------------------------------------------------
    -- AN OUTER'S WALK
    ----------------------------------------------------------------

    -- the impl's tail below a flattener: the restamp's scan and projection
    Restamp : ∀ {ℓ₂ ℓ₃ ℓ₄ u} Θ₁ → Env (plainᵏ Γ κ) Θ₁ → NodeId → ∀ Θ₂ → Env (plainᵏ Γ κ) Θ₂ → ℓ₂ ≤ ℓ₃ → ℓ₃ ≤ ℓ₄
            → Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t) → Path (plainᵏ Γ κ) ℓ₂ (emitᵗ u) (emitᵗ t)
    Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q =
      scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₃ ] (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₄ ] q)

    -- where the walk has got to: the flattener, and the tails it hands to
    Walked : ∀ {ℓ ℓ₄ u} → FlatOp → NodeId → NodeId → NodeId
           → Path Γ ℓ u t → Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t) → Goal
    Walked {u = u} op m m′ ks p q π NP NI = Flattener {Γ = Γ} κ π {t = t} NP NI u op m m′ ks [] × PathRel {Γ = Γ} κ π NP NI p q

    -- a flattener stays one where its nodes do and the pairing grows
    flat-move : ∀ {π π′ u op m m′ ks xs} (NP : List (NodeId × NodeState Γ)) (NI : List (NodeId × NodeState (plainᵏ Γ κ)))
                  (NP′ : List (NodeId × NodeState Γ)) (NI′ : List (NodeId × NodeState (plainᵏ Γ κ)))
              → (∀ {x} → x ∈ π → x ∈ π′) → Unmoved m NP′ NP → Unmoved m′ NI′ NI → Unmoved ks NI′ NI
              → Flattener {Γ = Γ} κ π {t = t} NP NI u op m m′ ks xs → Flattener {Γ = Γ} κ π′ {t = t} NP′ NI′ u op m m′ ks xs
    flat-move _ _ _ _ g (unmoved eP) (unmoved eI) (unmoved eK) (pm , x , x′ , lP , lI , fn , c , lk) =
      g pm , x , x′ , trans eP lP , trans eI lI , nodes-grow {Γ = Γ} κ g fn , c , trans eK lk

    -- an echo through the restamp's scan, on the impl side alone: the
    -- flattener kept, and the group the scan hands its projection
    data Restamped {sP stP sI stI} (S : St sP stP sI stI) {ℓ ℓ₄ u} (op : FlatOp) (m m′ ks : NodeId)
                   (p : Path Γ ℓ u t) (q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)) (ws : List (Val Γ u))
                   (es : List (Val (plainᵏ Γ κ) (emitᵗ u))) (fin : Bool)
                   (oI : Stream (plainᵏ Γ κ) (emitᵗ t)) (sI₁ : Sched (plainᵏ Γ κ)) (stI₁ : EvalSt ei) : Set where
      restamped : (A : After S ([] , sP , stP) (oI , sI₁ , stI₁))
                → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes stI₁)
                → Carries es ws → fin ≡ false
                → Restamped S op m m′ ks p q ws es fin oI sI₁ stI₁

    -- the outer's end on both sides, as far as the impl's tail
    data Wrapped {sP stP sI stI} (S : St sP stP sI stI) {ℓ ℓ₄ u} (op : FlatOp) (m m′ ks : NodeId)
                 (p : Path Γ ℓ u t) (q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)) (fin : Bool) (now : Tick)
               : Stream (plainᵏ Γ κ) (emitᵗ t) × Sched (plainᵏ Γ κ) × EvalSt ei → Set where
      wrapped : ∀ {sI₁ stI₁ r} (A : After S ([] , proj₂ (thruWrap (flatOp op) m fin (sP , stP))) ([] , sI₁ , stI₁))
              → Walked op m m′ ks p q (Store.π (After.store A))
                  (EvalSt.nodes (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP , stP))))) (EvalSt.nodes stI₁)
              → ClearI m′ ks q sI₁ stI₁
              → foldPath⇓ now q [] (proj₁ (thruWrap (flatOp op) m fin (sP , stP))) sI₁ stI₁ r
              → Wrapped S op m m′ ks p q fin now r

    -- A FLATTENER'S NODE PAIR WRITTEN ALIKE: the stores and the walk
    -- stay related with the two nodes moved to states that pair again
    flat-write : ∀ {sP stP sI stI} (S : St sP stP sI stI) {ℓ ℓ₄ u op m m′ ks xs}
                   {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {y y′}
               → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks xs
                 × PathRel {Γ = Γ} κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
               → FlatNodes {Γ = Γ} κ (Store.π S) u op y y′
               → Σ (After S ([] , sP , record stP { nodes = setNode m y (EvalSt.nodes stP) })
                            ([] , sI , record stI { nodes = setNode m′ y′ (EvalSt.nodes stI) })) λ A
                   → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (setNode m y (EvalSt.nodes stP)) (setNode m′ y′ (EvalSt.nodes stI)) u op m m′ ks xs
                     × PathRel {Γ = Γ} κ (Store.π (After.store A)) (setNode m y (EvalSt.nodes stP)) (setNode m′ y′ (EvalSt.nodes stI)) p q
    flat-write {sP} {stP} {sI} {stI} S {m = m} {m′} {y = y} {y′} (f@(pm , _ , _ , lP , lI , fn , _ , lk) , r) fn′ =
      after S′ (λ { (inj₁ c) → inj₁ c ; (inj₂ (a , b , pr)) → inj₂ (a , b , W.partW (Store.rows S) pr) })
               (λ ar → record { boundP = Arr.boundP ar ; boundI = Arr.boundI ar
                               ; rows = W.arrW (Store.rows S) (Arr.rows ar) ; lists = Arr.lists ar })
               [] (λ x → x)
      , W.flatW f , W.pathW r
      where
      module W = Write κ (Store.π-keys S) (Store.π-vals S) {t = t} {NP = EvalSt.nodes stP} {NI = EvalSt.nodes stI} pm lP lI fn lk fn′
      open Store S
      S′ : St sP (record stP { nodes = setNode m y (EvalSt.nodes stP) }) sI (record stI { nodes = setNode m′ y′ (EvalSt.nodes stI) })
      S′ = record
        { π = π ; π-keys = π-keys ; π-vals = π-vals ; pairs-below = pairs-below ; sources = sources ; numbers = numbers ; distinct = distinct
        ; sync = sync ; rows = W.regW rows ; latches = latches ; bounded = bounded ; swept = swept ; uncut = uncut ; rids = rids ; fresh-ids = fresh-ids ; above = above
        ; census = census ; owned = owned
        ; ruleP = sub-rule (λ r∈ → r∈) ≤-refl ruleP ; ruleI = sub-rule (λ r∈ → r∈) ≤-refl ruleI }

    -- a flattener fact read at the frame's operator is one at the former's
    reop : ∀ {π u op op₀ x x′} → flatOp op ≡ flatOp op₀ → FlatNodes {Γ = Γ} κ π u op₀ x x′ → FlatNodes {Γ = Γ} κ π u op x x′
    reop {op = mergeᶠ _} _ (merge~ ps) = merge~ ps
    reop {op = switchᶠ}  _ (switch~ c) = switch~ c
    reop {op = exhaustᶠ} _ exhaust~    = exhaust~
    reop {op = mergeᶠ _} () (switch~ _)
    reop {op = mergeᶠ _} () exhaust~
    reop {op = switchᶠ}  () (merge~ _)
    reop {op = switchᶠ}  () exhaust~
    reop {op = exhaustᶠ} () (merge~ _)
    reop {op = exhaustᶠ} () (switch~ _)

    -- no inner's frame is related to a restamp's scan
    no-scan : ∀ {π NP NI ℓ ℓ′ lo lo′ u s a m j k F} {h : lo ≤ ℓ} {h′ : lo′ ≤ ℓ′} {p : Path Γ ℓ u t} {Q : Path (plainᵏ Γ κ) ℓ′ s (emitᵗ t)}
            → PathRel κ π {t} NP NI (from-inner a m j ↠[ h ] p) (scan-f F k ↠[ h′ ] Q) → ⊥
    no-scan ()

    -- AN INNER'S SUBSCRIBE LEFT AGAIN: the lane's frames taken apart,
    -- the flattener as the walk left it, and the tails
    leave : ∀ {π NP NI lo lo′ ℓ ℓ₂ ℓ₃ ℓ₄ u} op {m m′ ks j j′ Θ₁ ρ₁ Θ₂ ρ₂} {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₂}
              {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)}
          → PathRel κ π {t} NP NI (from-inner (flatOp op) m j ↠[ h ] p)
              (from-inner (flatOp op) m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q)
          → Σ (List NodeId) (λ xs → Flattener {Γ = Γ} κ π {t} NP NI u op m m′ ks xs) × (j , j′ ∷ []) ∈ π × PathRel κ π NP NI p q
    leave (mergeᶠ _) (inner~ e (pm , x , x′ , lP , lI , fn , c , lk) ip pr) = (_ , pm , x , x′ , lP , lI , reop e fn , c , lk) , ip , pr
    leave (mergeᶠ _) (lane~ _ _ _ pr) = ⊥-elim (no-scan pr)
    leave switchᶠ    (inner~ e (pm , x , x′ , lP , lI , fn , c , lk) ip pr) = (_ , pm , x , x′ , lP , lI , reop e fn , c , lk) , ip , pr
    leave exhaustᶠ   (inner~ e (pm , x , x′ , lP , lI , fn , c , lk) ip pr) = (_ , pm , x , x′ , lP , lI , reop e fn , c , lk) , ip , pr

    -- the one row `π` keys by the flattener's node
    only : ∀ {π NP NI u op m m′ ks xs} → Unique (map proj₁ π) → (m , m′ ∷ ks ∷ []) ∈ π
         → Flattener {Γ = Γ} κ π {t} NP NI u op m m′ ks xs → Flattener {Γ = Γ} κ π {t} NP NI u op m m′ ks []
    only keys pm₀ f@(pm , _) with key-same keys pm pm₀
    ... | refl = f

    -- AN INNER'S WALK FROM STORES ALREADY MINTED: the walk of its
    -- elaboration, left again at the lane's frames
    inner-walk : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₁ ρ₁ Θ₂ ρ₂}
                   {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {o o′ j j′ rP rI}
               → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
               → (j , j′ ∷ []) ∈ Store.π S
               → ObsRel κ u o′ o
               → subscribeE⇓ o (from-inner (flatOp op) m j ↠[ ≤-refl ] p) now sP stP rP
               → subscribeE⇓ o′ (from-inner (flatOp op) m′ j′ ↠[ ≤-refl ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now sI stI rI
               → Σ (After S rP rI) λ A
                   → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
    inner-walk S {op = op} {rP = rP} {rI} (f@(pm , _) , pr) ip (elab s w r) dP dI =
      proj₁ B , only {NP = EvalSt.nodes (proj₂ (proj₂ rP))} {NI = EvalSt.nodes (proj₂ (proj₂ rI))} (Store.π-keys (After.store (proj₁ B))) (After.grows (proj₁ B) pm) (proj₂ (proj₁ L)) , proj₂ (proj₂ L)
      where
      B = walk κ s w r S (inner~ refl f ip pr) dP dI
      L = leave {NP = EvalSt.nodes (proj₂ (proj₂ rP))} {NI = EvalSt.nodes (proj₂ (proj₂ rI))} op (proj₂ B)

    postulate
      -- AN ECHO THROUGH THE RESTAMP: the scan's cell restamps it and
      -- keeps its payloads, and writes nothing but the cell, so the
      -- flattener and the tails stay related with the cell moved on; the
      -- group it hands on keeps its end
      restamp-echo : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ u op m m′ ks xs Θ₁ ρ₁ Θ₂ ρ₂}
                       {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {es ws fin o₁ fin₁ sI₁ stI₁}
                       {ys : List (Val (plainᵏ Γ κ) (FlatSᵗ u))}
                   → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks xs
                   → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                   → Carries es ws
                   → stepFrame⇓ now (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks) (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₄ ] q)
                       es fin sI stI (o₁ , ys , fin₁ , sI₁ , stI₁)
                   → Σ (After S ([] , sP , stP) (o₁ , sI₁ , stI₁)) λ A
                       → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI₁) u op m m′ ks xs
                       × PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes stI₁) p q
                       × Carries (map (applyClo {s = FlatSᵗ u} (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂)) ys) ws × fin₁ ≡ fin

      -- THE OUTER'S END ON BOTH SIDES: a flattener completes once its
      -- outer has and no lane is open or queued, read off related nodes,
      -- so the two ends agree; the restamp passes the empty group on
      outer-wrap : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₁ ρ₁ Θ₂ ρ₂}
                     {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {fin r}
                 → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                 → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) (proj₁ (proj₂ (thruWrap (flatOp op) m′ fin (sI , stI))))
                     (proj₂ (proj₂ (thruWrap (flatOp op) m′ fin (sI , stI))))
                 → foldPath⇓ now (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) []
                     (proj₁ (thruWrap (flatOp op) m′ fin (sI , stI)))
                     (proj₁ (proj₂ (thruWrap (flatOp op) m′ fin (sI , stI))))
                     (proj₂ (proj₂ (thruWrap (flatOp op) m′ fin (sI , stI)))) r
                 → Wrapped S op m m′ ks p q fin now r

    -- the same, at a walk
    flat-echo : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ u op m m′ ks Θ₁ ρ₁ Θ₂ ρ₂}
                  {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {xs ws o₁ fin₁ sI₁ stI₁}
                  {ys : List (Val (plainᵏ Γ κ) (FlatSᵗ u))}
              → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
              → Carries xs ws
              → stepFrame⇓ now (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks) (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₄ ] q)
                  xs false sI stI (o₁ , ys , fin₁ , sI₁ , stI₁)
              → Restamped S op m m′ ks p q ws (map (applyClo {s = FlatSᵗ u} (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂)) ys) fin₁ o₁ sI₁ stI₁
    flat-echo S (f , r) c d = let (A , f′ , r′ , c′ , e) = restamp-echo S f r c d in restamped A (f′ , r′) c′ e


    -- A SWITCH'S RUNNING INNER CUT ON BOTH SIDES: the rows through the
    -- two inners `CurRel` pairs leave together, and the walk is kept
    switch-kill : ∀ {sP stP sI stI} (S : St sP stP sI stI) {ℓ ℓ₄ u m m′ ks cur cur′ od od′ sP₁ stP₁ sI₁ stI₁}
                    {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)}
                → Walked switchᶠ m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                → lookupNode m (EvalSt.nodes stP) ≡ just (switch-st cur od)
                → lookupNode m′ (EvalSt.nodes stI) ≡ just (switch-st cur′ od′)
                → switchKill cur sP stP ≡ (sP₁ , stP₁) → switchKill cur′ sI stI ≡ (sI₁ , stI₁)
                → Σ (After S ([] , sP₁ , stP₁) ([] , sI₁ , stI₁)) λ A
                    → Walked switchᶠ m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes stP₁) (EvalSt.nodes stI₁)
    switch-kill {sP} {stP} {sI} {stI} S {m = m} {m′} {ks} {p = p} {q} W@((_ , _ , _ , lP , lI , fn , _) , _) eP eI kP kI =
      kill (kill-cur fn (trans (sym lP) eP) (trans (sym lI) eI)) kP kI
      where
        kill-cur : ∀ {π u x x′ cur cur′ od od′} → FlatNodes {Γ = Γ} κ π u switchᶠ x x′
                 → just x ≡ just (switch-st cur od) → just x′ ≡ just (switch-st cur′ od′) → CurRel {Γ = Γ} κ π cur cur′
        kill-cur (switch~ c) refl refl = c
        kill : ∀ {cur cur′ sP₁ stP₁ sI₁ stI₁} → CurRel {Γ = Γ} κ (Store.π S) cur cur′
             → switchKill cur sP stP ≡ (sP₁ , stP₁) → switchKill cur′ sI stI ≡ (sI₁ , stI₁)
             → Σ (After S ([] , sP₁ , stP₁) ([] , sI₁ , stI₁)) λ A
                 → Walked switchᶠ m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes stP₁) (EvalSt.nodes stI₁)
        kill {nothing} {nothing} _ refl refl = after S (λ x → x) (λ x → x) [] (λ x → x) , W
        kill {just c}  {just c′} ce refl refl =
          let K = cut-kill κ S ce (here refl)
          in proj₁ K , subst (λ π → Walked switchᶠ m m′ ks p q π (EvalSt.nodes stP) (EvalSt.nodes stI)) (sym (proj₂ K)) W
        kill {nothing} {just _}  () _ _
        kill {just _}  {nothing} () _ _

    -- a switch's node pair has one outer bit
    same-od : ∀ {π u x x′ cur cur′ od od′} → FlatNodes {Γ = Γ} κ π u switchᶠ x x′
            → just x ≡ just (switch-st cur od) → just x′ ≡ just (switch-st cur′ od′) → od ≡ od′
    same-od (switch~ _) refl refl = refl

    -- A FLATTENER NAMING ITS NEXT INNER AND SUBSCRIBING IT ON BOTH
    -- SIDES: each names the node its counter hands out next, and the
    -- subscribe mints it.  The pair joins `π` first, since `pairs-below`
    -- holds of it only once the counters have passed it; then the node is
    -- written, and the inner walks from there
    --
    -- The impl's tail is below its counter: without that, a tail naming
    -- the counter's next node as an impl-only merge would hold the node
    -- unpaired while the flattener pairs it
    flat-mint : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₁ ρ₁ Θ₂ ρ₂ y y′}
                  {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {o o′ j j′ rP rI}
              → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
              → FreshPath (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI
              → FlatNodes {Γ = Γ} κ (Minted S) u op y y′
              → ObsRel κ u o′ o
              → subscribeInner⇓ (flatOp op) m p now o sP (record stP { nodes = setNode m y (EvalSt.nodes stP) }) (j , rP)
              → subscribeInner⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now o′ sI
                  (record stI { nodes = setNode m′ y′ (EvalSt.nodes stI) }) (j′ , rI)
              → Σ (After S rP rI) λ A
                  → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
    flat-mint {sP} {stP} {sI} {stI} S {op = op} {m = m} {m′ = m′} {ks = ks} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂}
              {h₃ = h₃} {h₄ = h₄} {p = p} {q = q} (f , pr) fp fn ob (inner refl dP) (inner refl dI) =
      unmint (proj₁ Wr ⨾ proj₁ B) , proj₂ B
      where
      W₁ : Walked op m m′ ks p q (Store.π (mint-pair S)) (EvalSt.nodes stP) (EvalSt.nodes stI)
      W₁ = flatG {Γ = Γ} κ {π = Store.π S} {π′ = Store.π (mint-pair S)} there {t = t} {NP = EvalSt.nodes stP} {NI = EvalSt.nodes stI} f
         , pathG {Γ = Γ} κ there {t = t} {NP = EvalSt.nodes stP} {NI = EvalSt.nodes stI} (proj₂ (proj₂ (fresh-off {Γ = Γ} {κ = κ} {π = Store.π S} {j = nodeCt sP} (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) fp))) pr
      Wr = flat-write (mint-pair S) W₁ fn
      B = inner-walk (After.store (proj₁ Wr)) (proj₂ Wr) (After.grows (proj₁ Wr) (here refl)) ob dP dI

    -- a switch's: the node names the inner it subscribes
    switch-subscribe : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ u m m′ ks Θ₁ ρ₁ Θ₂ ρ₂ cur cur′ od od′}
                         {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {o o′ rP rI}
                     → Walked switchᶠ m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                     → lookupNode m (EvalSt.nodes stP) ≡ just (switch-st cur od)
                     → lookupNode m′ (EvalSt.nodes stI) ≡ just (switch-st cur′ od′)
                     → FreshPath (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI
                     → ObsRel κ u o′ o
                     → subscribeInner⇓ switchᵒ m p now o sP
                         (record stP { nodes = setNode m (switch-st (just (nodeCt sP)) od) (EvalSt.nodes stP) }) (nodeCt sP , rP)
                     → subscribeInner⇓ switchᵒ m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now o′ sI
                         (record stI { nodes = setNode m′ (switch-st (just (nodeCt sI)) od′) (EvalSt.nodes stI) }) (nodeCt sI , rI)
                     → Σ (After S rP rI) λ A
                         → Walked switchᶠ m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
    switch-subscribe {sP} {sI = sI} S {od = od} W@((_ , _ , _ , lP , lI , fn , _) , _) eP eI fp ob dP dI =
      flat-mint S W fp
        (subst (λ d → FlatNodes {Γ = Γ} κ (Minted S) _ switchᶠ (switch-st (just (nodeCt sP)) od) (switch-st (just (nodeCt sI)) d))
               (same-od fn (trans (sym lP) eP) (trans (sym lI) eI)) (switch~ (here refl)))
        ob dP dI

    -- A MERGE'S NODE PAIR AS EACH CONSUME READS IT: one count, one bound
    -- and the queues paired, so the two decide room alike, and a lane
    -- taken or an element queued pairs again
    room-agree : ∀ {π u lim x x′ l₁ a₁ q₁ d₁ l₂ a₂ q₂ d₂ b b′}
               → FlatNodes {Γ = Γ} κ π u (mergeᶠ lim) x x′
               → just x ≡ just (mergeAll-st {t = u} l₁ a₁ q₁ d₁) → just x′ ≡ just (mergeAll-st {t = emitᵗ u} l₂ a₂ q₂ d₂)
               → hasRoom l₁ a₁ ≡ b → hasRoom l₂ a₂ ≡ b′ → b ≡ b′
    room-agree (merge~ _) refl refl e e′ = trans (sym e) e′

    lane-nodes : ∀ {π u lim x x′ l₁ a₁ q₁ d₁ l₂ a₂ q₂ d₂}
               → FlatNodes {Γ = Γ} κ π u (mergeᶠ lim) x x′
               → just x ≡ just (mergeAll-st {t = u} l₁ a₁ q₁ d₁) → just x′ ≡ just (mergeAll-st {t = emitᵗ u} l₂ a₂ q₂ d₂)
               → FlatNodes {Γ = Γ} κ π u (mergeᶠ lim) (mergeAll-st {t = u} l₁ (suc a₁) q₁ d₁) (mergeAll-st {t = emitᵗ u} l₂ (suc a₂) q₂ d₂)
    lane-nodes (merge~ ps) refl refl = merge~ ps

    queue-nodes : ∀ {π u lim x x′ l₁ a₁ q₁ d₁ l₂ a₂ q₂ d₂ o o′}
                → FlatNodes {Γ = Γ} κ π u (mergeᶠ lim) x x′
                → just x ≡ just (mergeAll-st {t = u} l₁ a₁ q₁ d₁) → just x′ ≡ just (mergeAll-st {t = emitᵗ u} l₂ a₂ q₂ d₂)
                → ObsRel κ u o′ o
                → FlatNodes {Γ = Γ} κ π u (mergeᶠ lim) (mergeAll-st {t = u} l₁ a₁ (q₁ ++ o ∷ []) d₁)
                                                       (mergeAll-st {t = emitᵗ u} l₂ a₂ (q₂ ++ o′ ∷ []) d₂)
    queue-nodes (merge~ ps) refl refl r = merge~ (++⁺ ps (r ∷ []))

    merge-usable : ∀ {π u lim x x′} → FlatNodes {Γ = Γ} κ π u (mergeᶠ lim) x x′
                 → consumeUsable mergeAllᵒ u (just x) ≡ true × consumeUsable mergeAllᵒ (emitᵗ u) (just x′) ≡ true
    merge-usable {u = u} (merge~ _) = usable-self u , usable-self (emitᵗ u)

    -- an exhaust's pair is one flag and one end, read alike
    idle-nodes : ∀ {π u x x′ d₁ d₂}
               → FlatNodes {Γ = Γ} κ π u exhaustᶠ x x′
               → just x ≡ just (exhaust-st false d₁) → just x′ ≡ just (exhaust-st false d₂)
               → FlatNodes {Γ = Γ} κ π u exhaustᶠ (exhaust-st true d₁) (exhaust-st true d₂)
    idle-nodes exhaust~ refl refl = exhaust~

    idle-plain : ∀ {π u w x x′ d} → FlatNodes {Γ = Γ} κ π u exhaustᶠ x x′
               → just x ≡ just (exhaust-st false d) → consumeUsable exhaustᵒ w (just x′) ≡ true
    idle-plain exhaust~ refl = refl

    idle-impl : ∀ {π u w x x′ d} → FlatNodes {Γ = Γ} κ π u exhaustᶠ x x′
              → just x′ ≡ just (exhaust-st false d) → consumeUsable exhaustᵒ w (just x) ≡ true
    idle-impl exhaust~ refl = refl

    -- A SWITCH'S CONSUME ON BOTH SIDES: a switch can always be used, so
    -- both cut the running inner and then name and subscribe the next
    consume-switch : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ u m m′ ks Θ₁ ρ₁ Θ₂ ρ₂}
                       {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {o o′ rP rI}
                   → Walked switchᶠ m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                   → ObsRel κ u o′ o
                   → FreshPath (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI
                   → thruConsume⇓ switchᵒ m p now o sP stP rP
                   → thruConsume⇓ switchᵒ m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now o′ sI stI rI
                   → Σ (After S rP rI) λ A
                       → Walked switchᶠ m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
    consume-switch {sP} {stP} {sI} {stI} S {m = m} {m′} W ob fp (consume-switch-sub {cur = cur} eP kP refl dP) (consume-switch-sub {cur = cur′} eI kI refl dI) =
      let K = switch-kill S W eP eI kP kI
          B = switch-subscribe (After.store (proj₁ K)) (proj₂ K) (cut-kept m cur sP stP kP eP) (cut-kept m′ cur′ sI stI kI eI) (λ k h → subst (k <_) (cut-ct cur′ sI stI kI) (fp k h)) ob dP dI
      in proj₁ K ⨾ proj₁ B , proj₂ B
      where
      cut-kept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} k (c : Maybe NodeId) (s : Sched Γ) (st : EvalSt e) {s₁ st₁ x}
               → switchKill c s st ≡ (s₁ , st₁) → lookupNode k (EvalSt.nodes st) ≡ x → lookupNode k (EvalSt.nodes st₁) ≡ x
      cut-kept k c s st refl e = trans (cong (lookupNode k) (switchKill-nodes c s st)) e
      cut-ct : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (c : Maybe NodeId) (s : Sched Γ) (st : EvalSt e) {s₁ st₁}
             → switchKill c s st ≡ (s₁ , st₁) → nodeCt s ≡ nodeCt s₁
      cut-ct c s st refl = sym (switchKill-ct c s st)
    consume-switch S W ob _ (consume-switch-nil _) (consume-switch-nil _) = after S (λ x → x) (λ x → x) [] (λ x → x) , W
    consume-switch S {u = u} ((_ , _ , _ , _ , lI , switch~ _ , _) , _) ob _ (consume-switch-sub _ _ _ _) (consume-switch-nil n) =
      ⊥-elim (unusable switchᵒ (emitᵗ u) lI n refl)
    consume-switch S {u = u} ((_ , _ , _ , lP , _ , switch~ _ , _) , _) ob _ (consume-switch-nil n) _ =
      ⊥-elim (unusable switchᵒ u lP n refl)

    -- AN OUTER'S INNER HANDED THE FLATTENER ON BOTH SIDES, its lane on
    -- the impl's: the policy reads related nodes and decides alike.  A
    -- lane taken is a related write and then the inner's subscribe; an
    -- element queued is the write alone; a node neither can use is no
    -- step at all
    consume-pair : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₁ ρ₁ Θ₂ ρ₂}
                     {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {o o′ rP rI}
                 → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                 → ObsRel κ u o′ o
                 → FreshPath (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI
                 → thruConsume⇓ (flatOp op) m p now o sP stP rP
                 → thruConsume⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now o′ sI stI rI
                 → Σ (After S rP rI) λ A
                     → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
    consume-pair S {op = switchᶠ} W ob fp dP dI = consume-switch S W ob fp dP dI
    consume-pair S {op = mergeᶠ _} W@((_ , _ , _ , lP , lI , fn , _) , _) ob fp (consume-all-sub eP _ dP) (consume-all-sub eI _ dI) =
      flat-mint S W fp (lane-nodes (nodes-grow {Γ = Γ} κ there fn) (trans (sym lP) eP) (trans (sym lI) eI)) ob dP dI
    consume-pair S {op = mergeᶠ _} W@((_ , _ , _ , lP , lI , fn , _) , _) ob _ (consume-all-enqueue eP _) (consume-all-enqueue eI _) =
      flat-write S W (queue-nodes fn (trans (sym lP) eP) (trans (sym lI) eI) ob)
    consume-pair S {op = mergeᶠ _} W ob _ (consume-all-nil _) (consume-all-nil _) = after S (λ x → x) (λ x → x) [] (λ x → x) , W
    consume-pair S {op = mergeᶠ _} ((_ , _ , _ , lP , lI , fn , _) , _) ob _ (consume-all-sub eP hP _) (consume-all-enqueue eI hI) =
      ⊥-elim (t≢f (room-agree fn (trans (sym lP) eP) (trans (sym lI) eI) hP hI))
    consume-pair S {op = mergeᶠ _} ((_ , _ , _ , lP , lI , fn , _) , _) ob _ (consume-all-enqueue eP hP) (consume-all-sub eI hI _) =
      ⊥-elim (t≢f (sym (room-agree fn (trans (sym lP) eP) (trans (sym lI) eI) hP hI)))
    consume-pair S {u = u} {op = mergeᶠ _} ((_ , _ , _ , _ , lI , fn , _) , _) ob _ _ (consume-all-nil n) = ⊥-elim (unusable mergeAllᵒ (emitᵗ u) lI n (proj₂ (merge-usable fn)))
    consume-pair S {u = u} {op = mergeᶠ _} ((_ , _ , _ , lP , _ , fn , _) , _) ob _ (consume-all-nil n) _ = ⊥-elim (unusable mergeAllᵒ u lP n (proj₁ (merge-usable fn)))
    consume-pair S {op = exhaustᶠ} W@((_ , _ , _ , lP , lI , fn , _) , _) ob fp (consume-exhaust-sub eP dP) (consume-exhaust-sub eI dI) =
      flat-mint S W fp (idle-nodes (nodes-grow {Γ = Γ} κ there fn) (trans (sym lP) eP) (trans (sym lI) eI)) ob dP dI
    consume-pair S {op = exhaustᶠ} W ob _ (consume-exhaust-nil _) (consume-exhaust-nil _) = after S (λ x → x) (λ x → x) [] (λ x → x) , W
    consume-pair S {u = u} {op = exhaustᶠ} ((_ , _ , _ , lP , lI , fn , _) , _) ob _ (consume-exhaust-sub eP _) (consume-exhaust-nil n) =
      ⊥-elim (unusable exhaustᵒ (emitᵗ u) lI n (idle-plain fn (trans (sym lP) eP)))
    consume-pair S {u = u} {op = exhaustᶠ} ((_ , _ , _ , lP , lI , fn , _) , _) ob _ (consume-exhaust-nil n) (consume-exhaust-sub eI _) =
      ⊥-elim (unusable exhaustᵒ u lP n (idle-impl fn (trans (sym lI) eI)))

    ----------------------------------------------------------------
    -- A VALUELESS GROUP, ON THE IMPL SIDE ALONE.  An outer's emit whose
    -- element echoes nothing is restamped and folded rootward by the
    -- impl, and the plain run has nothing to fold.  The impl's frames
    -- step on it one constructor at a time, the plain side still, and
    -- the descent is the impl's fold.
    ----------------------------------------------------------------

    -- a pass's impl output, regrouped as the fold lays it down
    after-out : ∀ {sP stP sI stI} {S : St sP stP sI stI} {rP o o′} {x : Sched (plainᵏ Γ κ) × EvalSt ei}
              → o ≡ o′ → After S rP (o , x) → After S rP (o′ , x)
    after-out {rP = rP} e A =
      after (After.store A) (After.keeps A) (After.persists A)
        (subst (λ o → Pointwise (λ x w → V κ t (proj₂ x) w) (readᴵ o) (readᴾ (proj₁ rP))) e (After.values A))
        (After.grows A)

    regroup₂ : (o₁ o₂ y : Stream (plainᵏ Γ κ) (emitᵗ t)) → (o₁ ++ o₂) ++ y ≡ o₁ ++ (o₂ ++ y)
    regroup₂ o₁ o₂ y = ++-assoc o₁ o₂ y

    regroup₃ : (o₁ o₂ o₃ y : Stream (plainᵏ Γ κ) (emitᵗ t)) → (o₁ ++ (o₂ ++ o₃)) ++ y ≡ o₁ ++ (o₂ ++ (o₃ ++ y))
    regroup₃ o₁ o₂ o₃ y = trans (++-assoc o₁ (o₂ ++ o₃) y) (cong (o₁ ++_) (++-assoc o₂ o₃ y))

    -- A VALUELESS GROUP KEEPS THE PASS WITH THE PLAIN SIDE STILL, and
    -- the two paths related where the impl's fold leaves them
    Quiet : ∀ {lo lo′ s} → Path Γ lo s t → Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t) → Set
    Quiet p q =
      ∀ {now es fin sP stP sI stI rI} (S : St sP stP sI stI)
      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q → Carries es [] → fin ≡ false
      → Sound q sI stI
      → foldPath⇓ now q es fin sI stI rI
      → Σ (After S ([] , sP , stP) rI) λ A
          → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI))) p q

    -- WHAT A QUIET ARM HANDS BACK: the impl's run for one constructor
    -- stepped, the plain side still, the group reaching the tail still
    -- valueless and open, and the whole related again once the tail has
    -- folded
    data QArm {sP stP sI stI} (S : St sP stP sI stI) (now : Tick) {ℓ u} (p : Path Γ ℓ u t) (G : Goal)
              {ℓ′} (q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)) (es : List (Val (plainᵏ Γ κ) (emitᵗ u))) (fin : Bool)
              (oI : Stream (plainᵏ Γ κ) (emitᵗ t)) (sI₁ : Sched (plainᵏ Γ κ)) (stI₁ : EvalSt ei) : Set where
      qarm : (A : After S ([] , sP , stP) (oI , sI₁ , stI₁))
           → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes stI₁) p q
           → Carries es [] → fin ≡ false
           → (∀ {rI} → foldPath⇓ now q es fin sI₁ stI₁ rI → (B : After (After.store A) ([] , sP , stP) rI)
              → PathRel κ (Store.π (After.store B)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
              → G (Store.π (After.store B)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI))))
           → QArm S now p G q es fin oI sI₁ stI₁

    -- ONE LEAF PER CONSTRUCTOR, OVER THE IMPL'S OWN STEPS.  Each is
    -- handed the steps of its constructor's run and not the tail's fold,
    -- which its caller keeps, so the descent stays on the impl's fold.
    postulate
      -- A SHARE'S SUBJECT FANS A VALUELESS GROUP OUT TO EVERY READER, and
      -- every reader's chain folds it on the impl side alone
      quiet-sink : ∀ {lo lo′} {i : Fin n} {h : lo ≤ toℕ i} {h′ : lo′ ≤ toℕ (n ↑ʳ i)} (sh : lookup κ i ≡ sharedᵏ)
                 → Quiet (share-sink i h)
                     (subst (λ u → Path (plainᵏ Γ κ) lo′ u (emitᵗ t)) (sharedEq {Γ = Γ} κ i sh) (share-sink (n ↑ʳ i) h′))

      -- A SCAN'S CELL STEPPED ON EMITS CARRYING NOTHING stays related to
      -- the plain cell, which the plain scan's empty step leaves alone
      quiet-scan : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ s u C k k′}
                     {F : FnClo Γ (u ×ᵗ s) u} {F′ : FnClo (plainᵏ Γ κ) (C ×ᵗ emitᵗ s) C} {G : FnClo (plainᵏ Γ κ) C (emitᵗ u)}
                     {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₂ (emitᵗ u) (emitᵗ t)}
                     {es fin o₁ y₁ f₁ s₁ st₁}
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (scan-f F k ↠[ h ] p) (scan-f F′ k′ ↠[ h₁ ] (map-f G ↠[ h₂ ] q))
                 → Carries es [] → fin ≡ false
                 → stepFrame⇓ now (scan-f F′ k′) (map-f G ↠[ h₂ ] q) es fin sI stI (o₁ , y₁ , f₁ , s₁ , st₁)
                 → QArm S now p (λ π NP NI → PathRel κ π NP NI (scan-f F k ↠[ h ] p) (scan-f F′ k′ ↠[ h₁ ] (map-f G ↠[ h₂ ] q)))
                     q (map (applyClo G) y₁) f₁ o₁ s₁ st₁

      -- A COUNT'S CUT NEVER FIRES ON NOTHING: the cut's scan, its test,
      -- its projection and the one-lane merge all pass the group on open
      quiet-take : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ s C k k₁ k₂ m j w}
                     {F₁ : FnClo (plainᵏ Γ κ) (C ×ᵗ emitᵗ s) C} {G : FnClo (plainᵏ Γ κ) C (emitᵗ s)}
                     {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                     {p : Path Γ ℓ s t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ s) (emitᵗ t)}
                     {es fin o₁ y₁ f₁ s₁ st₁ o₂ y₂ f₂ s₂ st₂ o₄ y₄ f₄ s₄ st₄}
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (take-f nothing k ↠[ h ] p)
                     (scan-f F₁ k₁ ↠[ h₁ ] (take-f w k₂ ↠[ h₂ ] (map-f G ↠[ h₃ ] (from-inner mergeAllᵒ m j ↠[ h₄ ] q))))
                 → Carries es [] → fin ≡ false
                 → stepFrame⇓ now (scan-f F₁ k₁) (take-f w k₂ ↠[ h₂ ] (map-f G ↠[ h₃ ] (from-inner mergeAllᵒ m j ↠[ h₄ ] q)))
                     es fin sI stI (o₁ , y₁ , f₁ , s₁ , st₁)
                 → stepFrame⇓ now (take-f w k₂) (map-f G ↠[ h₃ ] (from-inner mergeAllᵒ m j ↠[ h₄ ] q)) y₁ f₁ s₁ st₁ (o₂ , y₂ , f₂ , s₂ , st₂)
                 → stepFrame⇓ now (from-inner mergeAllᵒ m j) q (map (applyClo G) y₂) f₂ s₂ st₂ (o₄ , y₄ , f₄ , s₄ , st₄)
                 → QArm S now p (λ π NP NI → PathRel κ π NP NI (take-f nothing k ↠[ h ] p)
                       (scan-f F₁ k₁ ↠[ h₁ ] (take-f w k₂ ↠[ h₂ ] (map-f G ↠[ h₃ ] (from-inner mergeAllᵒ m j ↠[ h₄ ] q)))))
                     q y₄ f₄ (o₁ ++ (o₂ ++ o₄)) s₄ st₄

      -- A TEST'S CUT NEVER FIRES ON NOTHING: no value to test
      quiet-takeWhile : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ s C P k k₁ k₂ w}
                          {F₁ : FnClo (plainᵏ Γ κ) (C ×ᵗ emitᵗ s) C} {G : FnClo (plainᵏ Γ κ) C (emitᵗ s)}
                          {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                          {p : Path Γ ℓ s t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ s) (emitᵗ t)}
                          {es fin o₁ y₁ f₁ s₁ st₁ o₂ y₂ f₂ s₂ st₂}
                      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (take-f (just P) k ↠[ h ] p)
                          (scan-f F₁ k₁ ↠[ h₁ ] (take-f w k₂ ↠[ h₂ ] (map-f G ↠[ h₃ ] q)))
                      → Carries es [] → fin ≡ false
                      → stepFrame⇓ now (scan-f F₁ k₁) (take-f w k₂ ↠[ h₂ ] (map-f G ↠[ h₃ ] q)) es fin sI stI (o₁ , y₁ , f₁ , s₁ , st₁)
                      → stepFrame⇓ now (take-f w k₂) (map-f G ↠[ h₃ ] q) y₁ f₁ s₁ st₁ (o₂ , y₂ , f₂ , s₂ , st₂)
                      → QArm S now p (λ π NP NI → PathRel κ π NP NI (take-f (just P) k ↠[ h ] p)
                            (scan-f F₁ k₁ ↠[ h₁ ] (take-f w k₂ ↠[ h₂ ] (map-f G ↠[ h₃ ] q))))
                          q (map (applyClo G) y₂) f₂ (o₁ ++ o₂) s₂ st₂

      -- AN EXPLODED OUTER'S EMIT CARRYING NOTHING explodes into no
      -- inner, and its echo is restamped on the impl side alone
      quiet-explode : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₅ ρ₅ Θ₁ ρ₁ Θ₂ ρ₂}
                        {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                        {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                        {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                    → Quiet (thru-outer (flatOp op) m ↠[ h ] p)
                        (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                         (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                          (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                           (thru-outer (flatOp op) m′ ↠[ h₄ ]
                            (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₅ ]
                             (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₆ ] q))))))

      -- AN INNER'S EMITS CARRYING NOTHING leave its lane as they came,
      -- the flattener's node unwritten, and are restamped
      quiet-inner : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u C op m m′ j j′ k}
                      {F : FnClo (plainᵏ Γ κ) (C ×ᵗ emitᵗ u) C} {G : FnClo (plainᵏ Γ κ) C (emitᵗ u)}
                      {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                      {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                      {es fin o₁ y₁ f₁ s₁ st₁ o₂ y₂ f₂ s₂ st₂}
                  → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (from-inner (flatOp op) m j ↠[ h ] p)
                      (from-inner (flatOp op) m′ j′ ↠[ h₁ ] (scan-f F k ↠[ h₂ ] (map-f G ↠[ h₃ ] q)))
                  → Carries es [] → fin ≡ false
                  → stepFrame⇓ now (from-inner (flatOp op) m′ j′) (scan-f F k ↠[ h₂ ] (map-f G ↠[ h₃ ] q)) es fin sI stI (o₁ , y₁ , f₁ , s₁ , st₁)
                  → stepFrame⇓ now (scan-f F k) (map-f G ↠[ h₃ ] q) y₁ f₁ s₁ st₁ (o₂ , y₂ , f₂ , s₂ , st₂)
                  → QArm S now p (λ π NP NI → PathRel κ π NP NI (from-inner (flatOp op) m j ↠[ h ] p)
                        (from-inner (flatOp op) m′ j′ ↠[ h₁ ] (scan-f F k ↠[ h₂ ] (map-f G ↠[ h₃ ] q))))
                      q (map (applyClo G) y₂) f₂ (o₁ ++ o₂) s₂ st₂

      -- THE IMPL-ONLY MERGE IN FRONT OF A LANE passes emits carrying
      -- nothing on as they came
      quiet-lane : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ′ u a m j mL jL}
                     {h : lo ≤ ℓ} {h′ : lo′ ≤ ℓ′} {p : Path Γ ℓ u t} {Q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)}
                     {es fin o₁ y₁ f₁ s₁ st₁}
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (from-inner a m j ↠[ h ] p)
                     (from-inner mergeAllᵒ mL jL ↠[ h′ ] Q)
                 → Carries es [] → fin ≡ false
                 → stepFrame⇓ now (from-inner mergeAllᵒ mL jL) Q es fin sI stI (o₁ , y₁ , f₁ , s₁ , st₁)
                 → QArm S now (from-inner a m j ↠[ h ] p)
                     (λ π NP NI → PathRel κ π NP NI (from-inner a m j ↠[ h ] p) (from-inner mergeAllᵒ mL jL ↠[ h′ ] Q))
                     Q y₁ f₁ o₁ s₁ st₁

      -- A DEFERRED BODY'S EMITS CARRYING NOTHING pass the hop's marker
      -- merge, its restamp and the hop's node as they came
      quiet-deferInner : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u nid nid′ j j′ m2 j2}
                           {G : FnClo (plainᵏ Γ κ) (emitᵗ u) (emitᵗ u)}
                           {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                           {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                           {es fin o₁ y₁ f₁ s₁ st₁ o₃ y₃ f₃ s₃ st₃}
                       → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (from-inner mergeAllᵒ nid j ↠[ h ] p)
                           (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ] (map-f G ↠[ h₂ ] (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))
                       → Carries es [] → fin ≡ false
                       → stepFrame⇓ now (from-inner mergeAllᵒ m2 j2) (map-f G ↠[ h₂ ] (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))
                           es fin sI stI (o₁ , y₁ , f₁ , s₁ , st₁)
                       → stepFrame⇓ now (from-inner mergeAllᵒ nid′ j′) q (map (applyClo G) y₁) f₁ s₁ st₁ (o₃ , y₃ , f₃ , s₃ , st₃)
                       → QArm S now p (λ π NP NI → PathRel κ π NP NI (from-inner mergeAllᵒ nid j ↠[ h ] p)
                             (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ] (map-f G ↠[ h₂ ] (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))))
                           q y₃ f₃ (o₁ ++ o₃) s₃ st₃

    mutual
      quiet-pass : ∀ {lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)} → Quiet p q
      quiet-pass S root~ b refl _ fold-root = after S (λ x → x) (λ x → x) (root-values b false) (λ x → x) , root~
      quiet-pass S r@(sink~ sh) b e si dI = quiet-sink sh S r b e si dI
      quiet-pass S (map~ L r) b e si (fold-step step-map dI) =
        let X = quiet-pass S r (carries-map L b) e (drop-ot _ _ _ si) dI in proj₁ X , map~ L (proj₂ X)
      quiet-pass S r@(scan~ _ _ _ _ _ _) b e si (fold-step d₁ (fold-step step-map dq)) =
        quiet-resume (quiet-scan S r b e d₁) (drop-ot _ _ _ (adv d₁ si)) dq
      quiet-pass S r@(take~ _ _ _ _ _ _ _ _ _) b e si
                 (fold-step {out₁ = o₁} d₁ (fold-step {out₁ = o₂} d₂ (fold-step step-map (fold-step {out₁ = o₄} d₄ dq)))) =
        let X = quiet-resume (quiet-take S r b e d₁ d₂ d₄) (adv d₄ (drop-ot _ _ _ (adv d₂ (adv d₁ si)))) dq
        in after-out (regroup₃ o₁ o₂ o₄ _) (proj₁ X) , proj₂ X
      quiet-pass S r@(takeWhile~ _ _ _ _ _ _) b e si (fold-step {out₁ = o₁} d₁ (fold-step {out₁ = o₂} d₂ (fold-step step-map dq))) =
        let X = quiet-resume (quiet-takeWhile S r b e d₁ d₂) (drop-ot _ _ _ (adv d₂ (adv d₁ si))) dq
        in after-out (regroup₂ o₁ o₂ _) (proj₁ X) , proj₂ X
      quiet-pass S r@(spent~ _ _ _ _) b e si
                 (fold-step {out₁ = o₁} d₁ (fold-step {out₁ = o₂} d₂ (fold-step step-map (fold-step {out₁ = o₄} d₄ dq)))) =
        let X = quiet-resume (quiet-take S r b e d₁ d₂ d₄) (adv d₄ (drop-ot _ _ _ (adv d₂ (adv d₁ si)))) dq
        in after-out (regroup₃ o₁ o₂ o₄ _) (proj₁ X) , proj₂ X
      quiet-pass S r@(spentWhile~ _ _ _ _) b e si (fold-step {out₁ = o₁} d₁ (fold-step {out₁ = o₂} d₂ (fold-step step-map dq))) =
        let X = quiet-resume (quiet-takeWhile S r b e d₁ d₂) (drop-ot _ _ _ (adv d₂ (adv d₁ si))) dq
        in after-out (regroup₂ o₁ o₂ _) (proj₁ X) , proj₂ X
      quiet-pass S (outerElem~ fl r) b e si dI = quiet-outer S (fl , r) b e si dI
      quiet-pass S r@(outerExplode~ _ _) b e si dI = quiet-explode S r b e si dI
      quiet-pass S r@(inner~ refl _ _ _) b e si (fold-step {out₁ = o₁} d₁ (fold-step {out₁ = o₂} d₂ (fold-step step-map dq))) =
        let X = quiet-resume (quiet-inner S r b e d₁ d₂) (drop-ot _ _ _ (adv d₂ (adv d₁ si))) dq
        in after-out (regroup₂ o₁ o₂ _) (proj₁ X) , proj₂ X
      quiet-pass S r@(lane~ _ _ _ _) b e si (fold-step d₁ dq) = quiet-resume (quiet-lane S r b e d₁) (adv d₁ si) dq
      quiet-pass S r@(deferInner~ _ _ _ _ _ _ _) b e si (fold-step {out₁ = o₁} d₁ (fold-step step-map (fold-step {out₁ = o₃} d₃ dq))) =
        let X = quiet-resume (quiet-deferInner S r b e d₁ d₃) (adv d₃ (drop-ot _ _ _ (adv d₁ si))) dq
        in after-out (regroup₂ o₁ o₃ _) (proj₁ X) , proj₂ X

      quiet-resume : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now ℓ ℓ′ u} {p : Path Γ ℓ u t} {G : Goal}
                       {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)} {es fin oI sI₁ stI₁ rI}
                   → QArm S now p G q es fin oI sI₁ stI₁ → Sound q sI₁ stI₁ → foldPath⇓ now q es fin sI₁ stI₁ rI
                   → Σ (After S ([] , sP , stP) (oI ++ proj₁ rI , proj₂ rI)) λ A
                       → G (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI)))
      quiet-resume (qarm A r b e rb) si dq = let X = quiet-pass (After.store A) r b e si dq in A ⨾ proj₁ X , rb dq (proj₁ X) (proj₂ X)

      -- AN OUTER'S EMITS CARRYING NOTHING, HANDED THE FLATTENER: every
      -- element a bare echo, restamped, then the open end restamped too
      quiet-outer : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                      {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                      {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {es fin rI}
                  → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) → Carries es [] → fin ≡ false
                  → Sound (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q)) sI stI
                  → foldPath⇓ now (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q))
                      es fin sI stI rI
                  → Σ (After S ([] , sP , stP) rI) λ A
                      → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI)))
                          (thru-outer (flatOp op) m ↠[ h ] p)
                          (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q))
      quiet-outer S {op = op} {Θ₀ = Θ₀} {ρ₀} w b refl si
                  (fold-step step-map (fold-step dW@(step-thru-outer W) (fold-step d₁ (fold-step step-map dq)))) =
        let si′ = drop-ot _ _ _ si
            X  = quiet-walk S {op = op} {Θ₀ = Θ₀} {ρ₀} (unthru si′) w b W
            c₁ = step-clear d₁ (unthru (step-kept _ dW si′))
            T  = quiet-tail (flat-echo (After.store (proj₁ X)) (proj₂ X) [] d₁) (tail-of c₁) dq
        in proj₁ X ⨾ proj₁ T , outerElem~ (proj₁ (proj₂ T)) (proj₂ (proj₂ T))

      -- THE OUTER'S WALK, every element a bare echo
      quiet-walk : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                     {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {es rI}
                 → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
                 → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                 → Carries {echoᵗ u} es []
                 → thruWalk⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now
                     (thruEvents (map (applyClo (Θ₀ , elemᵛ , ρ₀)) es)) sI stI rI
                 → Σ (After S ([] , sP , stP) rI) λ A
                     → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI)))
      quiet-walk S cI w [] walk-nil = after S (λ x → x) (λ x → x) [] (λ x → x) , w
      quiet-walk S {Θ₀ = Θ₀} {ρ₀} cI w (quiet e′ bq b) W = quiet-elem-step S cI w (elem-quiet {Θ = Θ₀} {ρ₀} e′ bq) b W

      quiet-elem-step : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                          {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {z es rI}
                      → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
                      → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                      → QuietElem {u} z → Carries {echoᵗ u} es []
                      → thruWalk⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now
                          (thruEvents (z ∷ map (applyClo (Θ₀ , elemᵛ , ρ₀)) es)) sI stI rI
                      → Σ (After S ([] , sP , stP) rI) λ A
                          → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI)))
      quiet-elem-step S cI w (quiet-elem bx) b (walk-echo (fold-step d₁ (fold-step step-map dq)) W′) =
        let c₁ = step-clear d₁ cI
            E  = quiet-tail (flat-echo S w (quiet _ bx []) d₁) (tail-of c₁) dq
            X  = quiet-walk (After.store (proj₁ E)) (fold-clear dq (proj₂ (proj₁ (tail-of c₁))) refl c₁) (proj₂ E) b W′
        in proj₁ E ⨾ proj₁ X , proj₂ X

      -- a bare echo, restamped: down the impl's tail alone
      quiet-tail : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now ℓ ℓ₄ u op m m′ ks}
                     {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {es fin oI sI₁ stI₁ r}
                 → Restamped S op m m′ ks p q [] es fin oI sI₁ stI₁ → ClearI m′ ks q sI₁ stI₁ → foldPath⇓ now q es fin sI₁ stI₁ r
                 → Σ (After S ([] , sP , stP) (oI ++ proj₁ r , proj₂ r)) λ A
                     → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ r)))
      quiet-tail {stP = stP} {stI₁ = stI₁} {r = r} (restamped A (fl , rel) c e) cI dq =
        let X  = quiet-pass (After.store A) rel c e (proj₂ (proj₁ cI)) dq
            F  = flat-move (EvalSt.nodes stP) (EvalSt.nodes stI₁) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ r)))
                   (After.grows (proj₁ X)) (unmoved refl) (missed dq (proj₁ cI)) (missed dq (proj₂ cI , proj₂ (proj₁ cI))) fl
        in A ⨾ proj₁ X , F , proj₂ X

    -- THE OUTER'S END, AS THE ARM ITS TAIL RESUMES: the flattener's
    -- nodes are below the tail, so its fold leaves them where they were
    wrap-arm : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                 {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                 {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {oP sP′ stP′ oI sI′ stI′ fin r}
             → (A : After S (oP , sP′ , stP′) (oI , sI′ , stI′))
             → Clear m p (proj₁ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′)))) (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
             → Wrapped (After.store A) op m m′ ks p q fin now r
             → Arm S now oP (proj₁ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                 (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                 p [] (proj₁ (thruWrap (flatOp op) m fin (sP′ , stP′)))
                 (λ π NP NI → PathRel κ π NP NI (thru-outer (flatOp op) m ↠[ h ] p)
                    (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q)))
                 (oI ++ proj₁ r , proj₂ r)
    wrap-arm {op = op} {m = m} {sP′ = sP′} {stP′ = stP′} {fin = fin} {r = r} A cP (wrapped {stI₁ = stI₁} A′ (fl , rel) cI dq) =
      arm (A ⨾∅ A′) rel [] (proj₂ (proj₁ cI)) dq λ {rP} dP B rel′ →
        let F  = flat-move (EvalSt.nodes (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))) (EvalSt.nodes stI₁)
                   (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ r)))
                   (After.grows B) (missed dP cP) (missed dq (proj₁ cI)) (missed dq (proj₂ cI , proj₂ (proj₁ cI))) fl
        in outerElem~ F rel′

    -- TWO RELATED PATHS KEEP THE PASS, AND ARE RELATED AGAIN WHERE IT
    -- LEAVES THEM: a flattener's outer folds its tail once per emit
    Pass : ∀ {lo lo′ s} → Path Γ lo s t → Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t) → Set
    Pass p q =
      ∀ {now vs es fin sP stP sI stI rP rI} (S : St sP stP sI stI)
      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q → Carries es vs
      → Sound p sP stP → Sound q sI stI
      → foldPath⇓ now p vs fin sP stP rP → foldPath⇓ now q es fin sI stI rI
      → Σ (After S rP rI) λ A
          → PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q


    -- ONE LEAF PER PLAIN FRAME A CONSTRUCTOR STARTS WITH.  An outer's
    -- two constructors and an inner's three are split once their arm is
    -- the riskiest.
    postulate
      -- A SHARE CLOSED ON BOTH SIDES, before its end is delivered
      share-spend  : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n} → lookup κ i ≡ sharedᵏ
                   → After S ([] , sP , shareSpend i stP) ([] , sI , shareSpend (n ↑ʳ i) stI)
      -- A SHARE'S READERS DROPPED ON BOTH SIDES, once its end is delivered
      share-finish : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n} → lookup κ i ≡ sharedᵏ
                   → After S ([] , proj₂ (shareFinish i true ([] , sP , stP))) ([] , proj₂ (shareFinish (n ↑ʳ i) true ([] , sI , stI)))
      -- AN OUTER'S ELEMENTS EXPLODED: each emit's run of elements is an
      -- inner the impl's merge subscribes, and its elements walk into the
      -- flattener where the plain outer's walk hands them on
      explode-walk : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₅ ρ₅ Θ₁ ρ₁ Θ₂ ρ₂}
                       {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                       {es vs rP rI}
                   → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                   → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                   → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                   → Carries {echoᵗ u} es vs
                   → thruWalk⇓ (flatOp op) m p now (thruEvents vs) sP stP rP
                   → thruWalk⇓ mergeAllᵒ mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) now
                       (thruEvents (map (applyClo {s = obs (echoᵗ (emitᵗ u))} {t = echoᵗ (echoᵗ (emitᵗ u))}
                                                  (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅))
                                        (map (applyClo {s = emitᵗ (echoᵗ u)} {t = obs (echoᵗ (emitᵗ u))} (Θ₀ , explodeᵛ , ρ₀)) es))) sI stI rI
                   → Σ (After S rP rI) λ A
                       → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
                           u op m m′ ks (mX ∷ [])
                         × PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
      -- THE EXPLODED OUTER'S END: the impl's merge ends where the plain
      -- outer does, and the flattener's end follows on both sides
      explode-end : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₅ ρ₅ Θ₁ ρ₁ Θ₂ ρ₂}
                      {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                      {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)} {oP sP′ stP′ oI sI′ stI′ fin r}
                  → (A : After S (oP , sP′ , stP′) (oI , sI′ , stI′))
                  → Clear m p (proj₁ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′)))) (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                  → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes stP′) (EvalSt.nodes stI′) u op m m′ ks (mX ∷ [])
                    × PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP′) (EvalSt.nodes stI′) p q
                  → Sound (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)
                      (proj₁ (proj₂ (thruWrap mergeAllᵒ mX fin (sI′ , stI′)))) (proj₂ (proj₂ (thruWrap mergeAllᵒ mX fin (sI′ , stI′))))
                  → foldPath⇓ now (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) []
                      (proj₁ (thruWrap mergeAllᵒ mX fin (sI′ , stI′)))
                      (proj₁ (proj₂ (thruWrap mergeAllᵒ mX fin (sI′ , stI′)))) (proj₂ (proj₂ (thruWrap mergeAllᵒ mX fin (sI′ , stI′)))) r
                  → Arm S now oP (proj₁ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                      (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                      p [] (proj₁ (thruWrap (flatOp op) m fin (sP′ , stP′)))
                      (λ π NP NI → PathRel κ π NP NI (thru-outer (flatOp op) m ↠[ h ] p)
                         (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                          (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                           (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                            (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)))))
                      (oI ++ proj₁ r , proj₂ r)
      -- AN INNER HAS A CHAIN RUNNING THROUGH IT ON THE PLAIN SIDE EXACTLY
      -- WHEN ITS PAIR DOES ON THE IMPL'S
      inner-alive : ∀ {sP stP sI stI} (S : St sP stP sI stI) {j j′}
                  → (j , j′ ∷ []) ∈ Store.π S
                  → any (aliveThroughᶠ j stP) (EvalSt.registry stP) ≡ any (aliveThroughᶠ j′ stI) (EvalSt.registry stI)
      -- A MERGE'S INNER ENDED ON BOTH SIDES: each finish folds the group
      -- down its tail, then drains the queue its node holds, and the
      -- related nodes hold related queues
      merge-finish : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u lim m m′ ks xs j j′ Θ₁ ρ₁ Θ₂ ρ₂}
                       {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                       {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                       {vs es oP vs₁ fin₁ sP₁ stP₁ o₁ es₁ f₁ sI₁ stI₁ rI}
                   → Flattener {Γ = Γ} κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) u (mergeᶠ lim) m m′ ks xs
                   → (j , j′ ∷ []) ∈ Store.π S → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                   → Carries es vs
                   → Sound (from-inner mergeAllᵒ m j ↠[ h ] p) sP stP
                   → Sound (from-inner mergeAllᵒ m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) sI stI
                   → innerFinish⇓ mergeAllᵒ m j p now vs sP stP (lookupNode m (EvalSt.nodes stP)) (oP , vs₁ , fin₁ , sP₁ , stP₁)
                   → innerFinish⇓ mergeAllᵒ m′ j′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) now es sI stI (lookupNode m′ (EvalSt.nodes stI))
                       (o₁ , es₁ , f₁ , sI₁ , stI₁)
                   → foldPath⇓ now (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) es₁ f₁ sI₁ stI₁ rI
                   → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                       (λ π NP NI → PathRel κ π NP NI (from-inner mergeAllᵒ m j ↠[ h ] p)
                          (from-inner mergeAllᵒ m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q)) (o₁ ++ proj₁ rI , proj₂ rI)
      -- A LANE'S INNER IS LIVE EXACTLY WHERE ITS PLAIN INNER IS: the lane merge
      -- sits in front of every impl chain the inner's pair runs
      lane-alive : ∀ {sP stP sI stI} (S : St sP stP sI stI) {lo lo′ ℓ ℓ′ u a m j mL jL} {h : lo ≤ ℓ} {h′ : lo′ ≤ ℓ′}
                     {p : Path Γ ℓ u t} {Q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)}
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (from-inner a m j ↠[ h ] p) (from-inner mergeAllᵒ mL jL ↠[ h′ ] Q)
                 → any (aliveThroughᶠ j stP) (EvalSt.registry stP) ≡ any (aliveThroughᶠ jL stI) (EvalSt.registry stI)
      -- A LANE MERGE OVER AN INNER'S ARM STAYS ONE: impl only, idle, and
      -- off every tail the arm folds
      lane-wrap : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now lo lo′ ℓ ℓ′ u a m j mL jL vs rI} {h : lo ≤ ℓ} {h′ : lo′ ≤ ℓ′}
                    {p : Path Γ ℓ u t} {Q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)}
                → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (from-inner a m j ↠[ h ] p) (from-inner mergeAllᵒ mL jL ↠[ h′ ] Q)
                → Sound (from-inner mergeAllᵒ mL jL ↠[ h′ ] Q) sI stI
                → Arm S now [] sP stP p vs false (λ π NP NI → PathRel κ π NP NI (from-inner a m j ↠[ h ] p) Q) rI
                → Arm S now [] sP stP p vs false
                    (λ π NP NI → PathRel κ π NP NI (from-inner a m j ↠[ h ] p) (from-inner mergeAllᵒ mL jL ↠[ h′ ] Q)) rI
      -- A DEAD INNER BEHIND A LANE MERGE FINISHES ON BOTH SIDES: the
      -- plain flattener's finish, against the lane merge's and the inner
      -- below it the group then reaches
      lane-finish : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ′ u a m j mL jL}
                      {h : lo ≤ ℓ} {h′ : lo′ ≤ ℓ′} {p : Path Γ ℓ u t} {Q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)}
                      {vs es oP vs₁ fin₁ sP₁ stP₁ o₁ es₁ f₁ sI₁ stI₁ rI}
                  → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (from-inner a m j ↠[ h ] p) (from-inner mergeAllᵒ mL jL ↠[ h′ ] Q)
                  → Carries es vs
                  → Sound (from-inner a m j ↠[ h ] p) sP stP → Sound (from-inner mergeAllᵒ mL jL ↠[ h′ ] Q) sI stI
                  → any (aliveThroughᶠ j stP) (EvalSt.registry stP) ≡ false
                  → innerFinish⇓ a m j p now vs sP stP (lookupNode m (EvalSt.nodes stP)) (oP , vs₁ , fin₁ , sP₁ , stP₁)
                  → innerFinish⇓ mergeAllᵒ mL jL Q now es sI stI (lookupNode mL (EvalSt.nodes stI)) (o₁ , es₁ , f₁ , sI₁ , stI₁)
                  → foldPath⇓ now Q es₁ f₁ sI₁ stI₁ rI
                  → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                      (λ π NP NI → PathRel κ π NP NI (from-inner a m j ↠[ h ] p) (from-inner mergeAllᵒ mL jL ↠[ h′ ] Q))
                      (o₁ ++ proj₁ rI , proj₂ rI)
      -- A DEFERRED BODY'S INNER IS LIVE ON THE PLAIN SIDE EXACTLY WHEN
      -- THE HOP'S MARKER MERGE'S INNER IS ON THE IMPL'S
      defer-alive : ∀ {sP stP sI stI} (S : St sP stP sI stI) {j j′ m2 j2}
                  → (j , j′ ∷ m2 ∷ j2 ∷ []) ∈ Store.π S
                  → any (aliveThroughᶠ j stP) (EvalSt.registry stP) ≡ any (aliveThroughᶠ j2 stI) (EvalSt.registry stI)
      -- A DELIVERED EMIT CARRIES WHAT IT CARRIED: the hop's restamp
      -- retags a subscribe as a delivery over its own events
      delivery-rel : ∀ {u Θx ρ₀} e′ {ws}
                   → EmitRel {Γ = Γ} κ u e′ ws
                   → EmitRel {Γ = Γ} κ u (applyClo (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) e′) ws
      -- A DEAD DEFERRED BODY FINISHES ON BOTH SIDES: the plain merge's
      -- finish, against the hop's marker merge's and the restamp and hop
      -- node the group then reaches
      defer-finish : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u nid nid′ j j′ m2 j2 Θx ρ₀}
                       {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                       {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                       {vs es oP vs₁ fin₁ sP₁ stP₁ o₁ es₁ f₁ sI₁ stI₁ rI}
                   → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (from-inner mergeAllᵒ nid j ↠[ h ] p)
                       (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                        (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                         (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))
                   → Carries es vs
                   → Sound (from-inner mergeAllᵒ nid j ↠[ h ] p) sP stP
                   → Sound (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                            (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                             (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))) sI stI
                   → any (aliveThroughᶠ j stP) (EvalSt.registry stP) ≡ false
                   → innerFinish⇓ mergeAllᵒ nid j p now vs sP stP (lookupNode nid (EvalSt.nodes stP)) (oP , vs₁ , fin₁ , sP₁ , stP₁)
                   → innerFinish⇓ mergeAllᵒ m2 j2
                       (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                        (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)) now es sI stI (lookupNode m2 (EvalSt.nodes stI)) (o₁ , es₁ , f₁ , sI₁ , stI₁)
                   → foldPath⇓ now (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                       (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)) es₁ f₁ sI₁ stI₁ rI
                   → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                       (λ π NP NI → PathRel κ π NP NI (from-inner mergeAllᵒ nid j ↠[ h ] p)
                          (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                           (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                            (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))) (o₁ ++ proj₁ rI , proj₂ rI)

    -- AN INNER LEFT OPEN: the impl's lets the group past as the plain one
    -- does, its restamp moves the cell alone, and the tails are related
    inner-on : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u op m m′ ks j j′ Θ₁ ρ₁ Θ₂ ρ₂}
                 {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                 {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)} {stP₁ stI₁ vs es fin rI}
             → (A₀ : After S ([] , sP , stP₁) ([] , sI , stI₁))
             → Σ (List NodeId) (λ xs → Flattener {Γ = Γ} κ (Store.π (After.store A₀)) {t} (EvalSt.nodes stP₁) (EvalSt.nodes stI₁) u op m m′ ks xs)
               × (j , j′ ∷ []) ∈ Store.π (After.store A₀) × PathRel κ (Store.π (After.store A₀)) (EvalSt.nodes stP₁) (EvalSt.nodes stI₁) p q
             → Carries es vs
             → Sound (from-inner (flatOp op) m j ↠[ h ] p) sP stP₁
             → Sound (from-inner (flatOp op) m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) sI stI₁
             → foldPath⇓ now (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) es fin sI stI₁ rI
             → Arm S now [] sP stP₁ p vs fin
                 (λ π NP NI → PathRel κ π NP NI (from-inner (flatOp op) m j ↠[ h ] p)
                    (from-inner (flatOp op) m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q)) rI
    inner-on {m = m} {m′} {j = j} {j′} {stP₁ = stP₁} A₀ ((_ , f) , ip , pr) b sp si (fold-step d₁ (fold-step step-map dq))
      with restamp-echo (After.store A₀) f pr b d₁
    ... | A , f′ , pr′ , c′ , refl =
      arm (A₀ ⨾ A) pr′ c′ (proj₂ (proj₁ cI)) dq λ {rP} dP B rel′ →
        inner~ refl (flat-move (EvalSt.nodes stP₁) _ (EvalSt.nodes (proj₂ (proj₂ rP))) _ (After.grows B)
                       (missed dP (head-on _ _ _ m (self-node m (j ∷ [])) sp , drop-ot _ _ _ sp))
                       (missed dq (proj₁ cI)) (missed dq (proj₂ cI , proj₂ (proj₁ cI))) f′)
               (After.grows B (After.grows A ip)) rel′
      where
      cI = tail-of (step-clear d₁ (head-on _ _ _ m′ (self-node m′ (j′ ∷ [])) si , drop-ot _ _ _ si))

    -- leaving an inner: the flattener's lane, then its restamp
    inner-pass : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u op m m′ ks j j′ Θ₁ ρ₁ Θ₂ ρ₂}
                   {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                   {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
               → InnerPasses (flatOp op) m j h p
                   (from-inner (flatOp op) m′ j′ ↠[ h₁ ]
                    (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₂ ]
                     (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₃ ] q)))
    inner-pass {op = op} S R b sp si _ (fold-step (step-from-inner react-false) dR) = inner-on (after S (λ x → x) (λ x → x) [] (λ x → x)) (leave op R) b sp si dR
    inner-pass {op = op} S R b sp si _ (fold-step (step-from-inner (react-alive _)) dR) = inner-on (after S (λ x → x) (λ x → x) [] (λ x → x)) (leave op R) b sp si dR
    inner-pass S R b sp si (inj₁ ()) (fold-step (step-from-inner (react-dead _ _)) _)
    inner-pass {op = op} S R b sp si (inj₂ al) (fold-step (step-from-inner (react-dead dd _)) _) =
      ⊥-elim (t≢f (trans (sym (trans (sym (inner-alive S (proj₁ (proj₂ (leave op R))))) al)) dd))

    -- A SWITCH'S INNER ENDED: both sides clear their current inner and let
    -- the group on, or neither does -- `CurRel` pairs the two currents,
    -- so the dying inner is current on both sides or on neither
    switch-finish : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u m m′ ks xs j j′ Θ₁ ρ₁ Θ₂ ρ₂ x x′}
                   {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                   {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                   {vs es oP vs₁ fin₁ sP₁ stP₁ o₁ es₁ f₁ sI₁ stI₁ rI}
               → Flattener {Γ = Γ} κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) u switchᶠ m m′ ks xs
               → (j , j′ ∷ []) ∈ Store.π S → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
               → FlatNodes {Γ = Γ} κ (Store.π S) u switchᶠ x x′
               → Carries es vs
               → Sound (from-inner switchᵒ m j ↠[ h ] p) sP₁ stP₁
               → Sound (from-inner switchᵒ m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) sI₁ stI₁
               → innerFinish⇓ switchᵒ m j p now vs sP stP (just x) (oP , vs₁ , fin₁ , sP₁ , stP₁)
               → innerFinish⇓ switchᵒ m′ j′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) now es sI stI (just x′) (o₁ , es₁ , f₁ , sI₁ , stI₁)
               → foldPath⇓ now (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) es₁ f₁ sI₁ stI₁ rI
               → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                   (λ π NP NI → PathRel κ π NP NI (from-inner switchᵒ m j ↠[ h ] p)
                     (from-inner switchᵒ m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q)) (o₁ ++ proj₁ rI , proj₂ rI)
    switch-finish S f ip pr (switch~ _) b sp si (finish-switch-clear _) (finish-switch-clear _) dR =
      let W = flat-write S (f , pr) (switch~ tt) in inner-on (proj₁ W) ((_ , proj₁ (proj₂ W)) , ip , proj₂ (proj₂ W)) b sp si dR
    switch-finish S f ip pr (switch~ {cur′ = nothing} ()) b sp si (finish-switch-clear _) (finish-nil _) dR
    switch-finish S f ip pr (switch~ {cur′ = just _} c) b sp si (finish-switch-clear e) (finish-nil e′) dR =
      ⊥-elim (t≢f (trans (sym (cur-here (Store.π-keys S) c ip e)) e′))
    switch-finish S f ip pr (switch~ {cur = nothing} ()) b sp si (finish-nil _) (finish-switch-clear _) dR
    switch-finish S f ip pr (switch~ {cur = just _} c) b sp si (finish-nil e) (finish-switch-clear e′) dR =
      ⊥-elim (t≢f (trans (sym (cur-there (Store.π-vals S) c ip e′)) e))
    switch-finish S f ip pr (switch~ _) b sp si (finish-nil _) (finish-nil _) dR =
      inner-on (after S (λ x → x) (λ x → x) [] (λ x → x)) ((_ , f) , ip , pr) b sp si dR

    -- AN EXHAUST'S INNER ENDED: both sides clear their lane and let the
    -- group on
    exhaust-finish : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u m m′ ks xs j j′ Θ₁ ρ₁ Θ₂ ρ₂ x x′}
                   {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                   {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                   {vs es oP vs₁ fin₁ sP₁ stP₁ o₁ es₁ f₁ sI₁ stI₁ rI}
               → Flattener {Γ = Γ} κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) u exhaustᶠ m m′ ks xs
               → (j , j′ ∷ []) ∈ Store.π S → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
               → FlatNodes {Γ = Γ} κ (Store.π S) u exhaustᶠ x x′
               → Carries es vs
               → Sound (from-inner exhaustᵒ m j ↠[ h ] p) sP₁ stP₁
               → Sound (from-inner exhaustᵒ m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) sI₁ stI₁
               → innerFinish⇓ exhaustᵒ m j p now vs sP stP (just x) (oP , vs₁ , fin₁ , sP₁ , stP₁)
               → innerFinish⇓ exhaustᵒ m′ j′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) now es sI stI (just x′) (o₁ , es₁ , f₁ , sI₁ , stI₁)
               → foldPath⇓ now (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) es₁ f₁ sI₁ stI₁ rI
               → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                   (λ π NP NI → PathRel κ π NP NI (from-inner exhaustᵒ m j ↠[ h ] p)
                     (from-inner exhaustᵒ m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q)) (o₁ ++ proj₁ rI , proj₂ rI)
    exhaust-finish S f ip pr exhaust~ b sp si finish-exhaust-clear finish-exhaust-clear dR =
      let W = flat-write S (f , pr) (exhaust~ {ia = false}) in inner-on (proj₁ W) ((_ , proj₁ (proj₂ W)) , ip , proj₂ (proj₂ W)) b sp si dR
    exhaust-finish S f ip pr exhaust~ b sp si (finish-nil ()) _ dR
    exhaust-finish S f ip pr exhaust~ b sp si finish-exhaust-clear (finish-nil ()) dR

    -- AN INNER ENDED ON BOTH SIDES, by its flattener's operator
    finish-by : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u op m m′ ks j j′ Θ₁ ρ₁ Θ₂ ρ₂}
                  {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                  {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                  {vs es oP vs₁ fin₁ sP₁ stP₁ o₁ es₁ f₁ sI₁ stI₁ rI}
              → Σ (List NodeId) (λ xs → Flattener {Γ = Γ} κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks xs)
                × (j , j′ ∷ []) ∈ Store.π S × PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
              → Carries es vs
              → Sound (from-inner (flatOp op) m j ↠[ h ] p) sP stP
              → Sound (from-inner (flatOp op) m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) sI stI
              → Sound (from-inner (flatOp op) m j ↠[ h ] p) sP₁ stP₁
              → Sound (from-inner (flatOp op) m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) sI₁ stI₁
              → innerFinish⇓ (flatOp op) m j p now vs sP stP (lookupNode m (EvalSt.nodes stP)) (oP , vs₁ , fin₁ , sP₁ , stP₁)
              → innerFinish⇓ (flatOp op) m′ j′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) now es sI stI (lookupNode m′ (EvalSt.nodes stI))
                  (o₁ , es₁ , f₁ , sI₁ , stI₁)
              → foldPath⇓ now (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) es₁ f₁ sI₁ stI₁ rI
              → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                  (λ π NP NI → PathRel κ π NP NI (from-inner (flatOp op) m j ↠[ h ] p)
                     (from-inner (flatOp op) m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q)) (o₁ ++ proj₁ rI , proj₂ rI)
    finish-by S {op = mergeᶠ _} ((_ , f) , ip , pr) b sp si _ _ F F′ dR = merge-finish S f ip pr b sp si F F′ dR
    finish-by S {op = switchᶠ} ((_ , f@(_ , _ , _ , lP , lI , fn , _)) , ip , pr) b _ _ sp si F F′ dR =
      switch-finish S f ip pr fn b sp si (subst (λ ns → innerFinish⇓ _ _ _ _ _ _ _ _ ns _) lP F)
        (subst (λ ns → innerFinish⇓ _ _ _ _ _ _ _ _ ns _) lI F′) dR
    finish-by S {op = exhaustᶠ} ((_ , f@(_ , _ , _ , lP , lI , fn , _)) , ip , pr) b _ _ sp si F F′ dR =
      exhaust-finish S f ip pr fn b sp si (subst (λ ns → innerFinish⇓ _ _ _ _ _ _ _ _ ns _) lP F)
        (subst (λ ns → innerFinish⇓ _ _ _ _ _ _ _ _ ns _) lI F′) dR

    -- AN INNER NO LIVE CHAIN RUNS THROUGH: its pair is dead too, and
    -- both sides finish it
    inner-dies : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u op m m′ ks j j′ Θ₁ ρ₁ Θ₂ ρ₂}
                   {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                   {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
               → InnerDies (flatOp op) m j h p
                   (from-inner (flatOp op) m′ j′ ↠[ h₁ ]
                    (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₂ ]
                     (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₃ ] q)))
    inner-dies {op = op} S R b sp si dd F (fold-step (step-from-inner (react-alive al′)) _) =
      ⊥-elim (t≢f (trans (sym al′) (trans (sym (inner-alive S (proj₁ (proj₂ (leave op R))))) dd)))
    inner-dies {op = op} S R b sp si dd F (fold-step d′@(step-from-inner (react-dead _ F′)) dR) =
      finish-by S (leave op R) b sp si (step-kept _ (step-from-inner (react-dead dd F)) sp) (step-kept _ d′ si) F F′ dR

    -- AN INNER NO LIVE CHAIN RUNS THROUGH, BEHIND A LANE MERGE: the lane's
    -- inner is dead too, and both sides finish it
    lane-dies : ∀ {lo lo′ ℓ ℓ′ u a m j mL jL} {h : lo ≤ ℓ} {h′ : lo′ ≤ ℓ′}
                  {p : Path Γ ℓ u t} {Q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)}
              → InnerDies a m j h p (from-inner mergeAllᵒ mL jL ↠[ h′ ] Q)
    lane-dies S R b sp si dd F (fold-step (step-from-inner (react-alive al′)) _) =
      ⊥-elim (t≢f (trans (sym al′) (trans (sym (lane-alive S R)) dd)))
    lane-dies S R b sp si dd F (fold-step (step-from-inner (react-dead _ F′)) dR) = lane-finish S R b sp si dd F F′ dR

    -- A DEFERRED BODY NO LIVE CHAIN RUNS THROUGH: the hop's marker
    -- merge's inner is dead too, and both sides finish it
    deferInner-dies : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u nid nid′ j j′ m2 j2 Θx ρ₀}
                        {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                        {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                    → InnerDies mergeAllᵒ nid j h p
                        (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                         (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                          (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))
    deferInner-dies S R@(deferInner~ _ ip₂ _ _ _ _ _) b sp si dd F (fold-step (step-from-inner (react-alive al′)) _) =
      ⊥-elim (t≢f (trans (sym al′) (trans (sym (defer-alive S ip₂)) dd)))
    deferInner-dies S R b sp si dd F (fold-step (step-from-inner (react-dead _ F′)) dR) = defer-finish S R b sp si dd F F′ dR

    delivery-carries : ∀ {u Θx ρ₀} {es vs}
                     → Carries {s = u} es vs
                     → Carries (map (applyClo (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀)) es) vs
    delivery-carries []              = []
    delivery-carries (quiet e′ r bs) = quiet _ (delivery-rel e′ r) (delivery-carries bs)
    delivery-carries (one e′ r bs)   = one _ (delivery-rel e′ r) (delivery-carries bs)

    -- A DEFERRED BODY'S INNER LEFT OPEN: the hop's marker merge and its
    -- node let the group past, and the restamp between moves no node
    defer-on : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u nid nid′ j j′ m2 j2 Θx ρ₀}
                 {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                 {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)} {vs es rI}
             → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (from-inner mergeAllᵒ nid j ↠[ h ] p)
                 (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                  (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                   (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))
             → Carries es vs
             → Sound (from-inner mergeAllᵒ nid j ↠[ h ] p) sP stP
             → Sound (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                      (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                       (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))) sI stI
             → foldPath⇓ now q (map (applyClo (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀)) es)
                 false sI stI rI
             → Arm S now [] sP stP p vs false
                 (λ π NP NI → PathRel κ π NP NI (from-inner mergeAllᵒ nid j ↠[ h ] p)
                    (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                     (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                      (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))) rI
    defer-on S {nid = nid} {nid′} {j} {j′} {m2} {j2} (deferInner~ ip₁ ip₂ lP lI l2 a1 pr) b sp si dq =
      arm (after S (λ x → x) (λ x → x) [] (λ x → x)) pr (delivery-carries b) s3 dq λ {rP} dP B rel′ →
        deferInner~ (After.grows B ip₁) (After.grows B ip₂) (trans (fold-unmoved dP cP) lP)
                    (trans (fold-unmoved dq c′) lI) (trans (fold-unmoved dq c2) l2) a1 rel′
      where
      s2 = drop-ot _ _ _ (drop-ot _ _ _ si)
      s3 = drop-ot _ _ _ s2
      cP = head-on _ _ _ nid (self-node nid (j ∷ [])) sp , drop-ot _ _ _ sp
      c′ = head-on _ _ _ nid′ (self-node nid′ (j′ ∷ [])) s2 , s3
      c2 = on-drop (on-drop (head-on _ _ _ m2 (self-node m2 (j2 ∷ [])) si)) , s3

    -- a deferred body: the hop's marker merge, its restamp, the hop's node
    deferInner-pass : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u nid nid′ j j′ m2 j2 Θx ρ₀}
                        {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                        {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                    → InnerPasses mergeAllᵒ nid j h p
                        (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                         (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                          (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))
    deferInner-pass S R b sp si _
      (fold-step (step-from-inner react-false) (fold-step step-map (fold-step (step-from-inner react-false) dq))) =
      defer-on S R b sp si dq
    deferInner-pass S R b sp si _
      (fold-step (step-from-inner (react-alive _)) (fold-step step-map (fold-step (step-from-inner react-false) dq))) =
      defer-on S R b sp si dq
    deferInner-pass S R b sp si (inj₁ ()) (fold-step (step-from-inner (react-dead _ _)) _)
    deferInner-pass S R@(deferInner~ _ ip₂ _ _ _ _ _) b sp si (inj₂ al) (fold-step (step-from-inner (react-dead dd _)) _) =
      ⊥-elim (t≢f (trans (sym (trans (sym (defer-alive S ip₂)) al)) dd))

    -- AN INNER LEFT OPEN, BY HOW ITS ELABORATION LED IT: a lane merge in
    -- front lets the group past as the inner below it does
    inner-any : ∀ {lo lo′ ℓ u a m j} {h : lo ≤ ℓ} {p : Path Γ ℓ u t} {Q : Path (plainᵏ Γ κ) lo′ (emitᵗ u) (emitᵗ t)}
              → InnerPasses a m j h p Q
    inner-any S R@(inner~ refl _ _ _) b sp si alv dI = inner-pass S R b sp si alv dI
    inner-any S R@(deferInner~ _ _ _ _ _ _ _) b sp si alv dI = deferInner-pass S R b sp si alv dI
    inner-any S R@(lane~ _ _ _ R′) b sp si _ (fold-step (step-from-inner react-false) dR) =
      lane-wrap R si (inner-any S R′ b sp (drop-ot _ _ _ si) (inj₁ refl) dR)
    inner-any S R@(lane~ _ _ _ R′) b sp si _ (fold-step (step-from-inner (react-alive _)) dR) =
      lane-wrap R si (inner-any S R′ b sp (drop-ot _ _ _ si) (inj₁ refl) dR)
    inner-any S (lane~ _ _ _ _) b sp si (inj₁ ()) (fold-step (step-from-inner (react-dead _ _)) _)
    inner-any S R@(lane~ _ _ _ _) b sp si (inj₂ al) (fold-step (step-from-inner (react-dead dd _)) _) =
      ⊥-elim (t≢f (trans (sym (trans (sym (lane-alive S R)) al)) dd))

    -- an outer's elements, each inner a sync outer hands the flattener
    -- subscribed before the step returns: the explode and its merge
    outerExplode-arm : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₅ ρ₅ Θ₁ ρ₁ Θ₂ ρ₂}
                         {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                         {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                         {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                         {vs es fin oP vs₁ fin₁ sP₁ stP₁ rI}
                     → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                       × PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                     → Carries {echoᵗ u} es vs
                     → Sound (thru-outer (flatOp op) m ↠[ h ] p) sP stP
                     → Sound (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                               (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                                (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                                 (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)))) sI stI
                     → stepFrame⇓ now (thru-outer (flatOp op) m) p vs fin sP stP (oP , vs₁ , fin₁ , sP₁ , stP₁)
                     → foldPath⇓ now (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                               (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                                (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                                 (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)))) es fin sI stI rI
                     → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                         (λ π NP NI → PathRel κ π NP NI (thru-outer (flatOp op) m ↠[ h ] p)
                            (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                             (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                              (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                               (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q))))) rI
    outerExplode-arm S {op = op} {Θ₀ = Θ₀} {ρ₀} {Θ₅ = Θ₅} {ρ₅} {fin = fin} (fl , r) b sp si dW@(step-thru-outer W)
                     (fold-step step-map (fold-step step-map (fold-step dW′@(step-thru-outer W′) dR))) =
      let si′ = drop-ot _ _ _ (drop-ot _ _ _ si)
          X   = explode-walk S {op = op} {Θ₀ = Θ₀} {ρ₀} {Θ₅ = Θ₅} {ρ₅} (unthru sp) (unthru si′) fl r b W W′
      in explode-end {op = op} {Θ₀ = Θ₀} {ρ₀} {Θ₅ = Θ₅} {ρ₅} {fin = fin} (proj₁ X) (unthru (step-kept _ dW sp)) (proj₂ X)
           (drop-ot _ _ _ (step-kept _ dW′ si′)) dR

    -- AN INNER'S STEP, by the rule its react takes: open or alive, it
    -- passes the group on; dead, it finishes
    inner-arm     : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u op m m′ ks j j′ Θ₁ ρ₁ Θ₂ ρ₂}
                      {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                      {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                  → Steps (from-inner (flatOp op) m j) h p
                      (from-inner (flatOp op) m′ j′ ↠[ h₁ ]
                       (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₂ ]
                        (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₃ ] q)))
    inner-arm {op = op} S R b sp si (step-from-inner react-false)        dI = inner-pass {op = op} S R b sp si (inj₁ refl) dI
    inner-arm {op = op} S R b sp si (step-from-inner (react-alive al))   dI = inner-pass {op = op} S R b sp si (inj₂ al) dI
    inner-arm {op = op} S R b sp si (step-from-inner (react-dead dd fz)) dI = inner-dies {op = op} S R b sp si dd fz dI

    lane-arm      : ∀ {lo lo′ ℓ ℓ′ u a m j mL jL} {h : lo ≤ ℓ} {h′ : lo′ ≤ ℓ′}
                      {p : Path Γ ℓ u t} {Q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)}
                  → Steps (from-inner a m j) h p (from-inner mergeAllᵒ mL jL ↠[ h′ ] Q)
    lane-arm S R b sp si (step-from-inner react-false)        dI = inner-any S R b sp si (inj₁ refl) dI
    lane-arm S R b sp si (step-from-inner (react-alive al))   dI = inner-any S R b sp si (inj₂ al) dI
    lane-arm S R b sp si (step-from-inner (react-dead dd fz)) dI = lane-dies S R b sp si dd fz dI

    deferInner-arm : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u nid nid′ j j′ m2 j2 Θx ρ₀}
                       {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                       {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                   → Steps (from-inner mergeAllᵒ nid j) h p
                       (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                        (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                         (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))
    deferInner-arm S R b sp si (step-from-inner react-false)        dI = deferInner-pass S R b sp si (inj₁ refl) dI
    deferInner-arm S R b sp si (step-from-inner (react-alive al))   dI = deferInner-pass S R b sp si (inj₂ al) dI
    deferInner-arm S R b sp si (step-from-inner (react-dead dd fz)) dI = deferInner-dies S R b sp si dd fz dI

    postulate
      -- A RESTAMPED EMIT CARRIES WHAT IT CARRIED: the restamp rebuilds the
      -- emit over its own events, so the values it holds are the ones
      restamp-rel : ∀ {i : Fin n} {Θ₀ ρ₀} {X : Tm (plainᵏ Γ κ) [] [] (emitᵗ (lookup Γ i) ∷ Θ₀) uniqᵗ} e′ {ws}
                  → EmitRel {Γ = Γ} κ (lookup Γ i) e′ ws
                  → EmitRel {Γ = Γ} κ (lookup Γ i) (applyClo (Θ₀ , restampᵛ X subscribeᵛ (varᵗ (here refl)) , ρ₀) e′) ws

    restamp-carries : ∀ {i : Fin n} {Θ₀ ρ₀} {X : Tm (plainᵏ Γ κ) [] [] (emitᵗ (lookup Γ i) ∷ Θ₀) uniqᵗ} {es vs}
                    → Carries {s = lookup Γ i} es vs
                    → Carries (map (applyClo (Θ₀ , restampᵛ X subscribeᵛ (varᵗ (here refl)) , ρ₀)) es) vs
    restamp-carries []             = []
    restamp-carries {i = i} {X = X} (quiet e′ r bs) = quiet _ (restamp-rel {i = i} {X = X} e′ r) (restamp-carries {i = i} {X = X} bs)
    restamp-carries {i = i} {X = X} (one e′ r bs)   = one _ (restamp-rel {i = i} {X = X} e′ r) (restamp-carries {i = i} {X = X} bs)

    -- A SLOT'S READER: the impl runs the restamp where the plain path runs
    -- on, so the arm is the one frame the impl moves alone, and the plain
    -- side has not moved
    read-arm : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n} {Θ₀ ρ₀ ℓ′}
                   {X : Tm (plainᵏ Γ κ) [] [] (emitᵗ (lookup Γ i) ∷ Θ₀) uniqᵗ} {h : suc (toℕ (n ↑ʳ i)) ≤ ℓ′}
                   {p : Path Γ (suc (toℕ i)) (lookup Γ i) t} {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ (lookup Γ i)) (emitᵗ t)}
                 → lookup κ i ≡ hotᵏ ⊎ lookup κ i ≡ sharedᵏ
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                 → ∀ {now vs es fin rI} → Carries es vs
                 → Sound (map-f (Θ₀ , restampᵛ X subscribeᵛ (varᵗ (here refl)) , ρ₀) ↠[ h ] q) sI stI
                 → foldPath⇓ now (map-f (Θ₀ , restampᵛ X subscribeᵛ (varᵗ (here refl)) , ρ₀) ↠[ h ] q) es fin sI stI rI
                 → Arm S now [] sP stP p vs fin none rI
    read-arm S {i = i} {X = X} _ r c si (fold-step step-map dq) =
      arm (after S (λ x → x) (λ x → x) [] (λ x → x)) r (restamp-carries {i = i} {X = X} c) (drop-ot _ _ _ si) dq (λ _ _ _ → tt)

    -- the emits of a stamped slot against the plain values, at types the
    -- share's own is only propositionally the emit of
    CarriesU : ∀ {u u′} → u′ ≡ emitᵗ u → List (Val (plainᵏ Γ κ) u′) → List (Val Γ u) → Set
    CarriesU refl = Carries

    carriesU-nil : ∀ {u u′} (e : u′ ≡ emitᵗ u) → CarriesU e [] []
    carriesU-nil refl = []

    -- a partnered pair stays partnered once the store moves
    slot-keeps : ∀ {sP stP sI stI sP₁ stP₁ sI₁ stI₁} {S : St sP stP sI stI} {S₁ : St sP₁ stP₁ sI₁ stI₁} {i : Fin n} {u}
                   {c : RegId × AtFloor Γ u t} {d}
               → Keeps S S₁
               → SlotPair (Store.rows S) (EvalSt.cancelled stP) (EvalSt.cancelled stI) i c d
               → SlotPair (Store.rows S₁) (EvalSt.cancelled stP₁) (EvalSt.cancelled stI₁) i c d
    slot-keeps K (slotpair x) = slotpair (K x)

    -- the same pass, started from the store as it stood before the row was marked
    rebase : ∀ {sP stP sI stI x y rP rI} {S : St sP stP sI stI}
           → After (delivered S {x} {y}) rP rI → After S rP rI
    rebase (after s k q v g) = after s k (λ ar → q (delivered-arr ar)) v g

    -- a fan-out's pairs stay paired once the store moves
    share-keeps : ∀ {sP stP sI stI sP₁ stP₁ sI₁ stI₁} {S₀ : St sP stP sI stI} {S₁ : St sP₁ stP₁ sI₁ stI₁} {i : Fin n} {cs ds}
                → Keeps S₀ S₁
                → Pointwise (ShareSlot (Store.rows S₀) (EvalSt.cancelled stP) (EvalSt.cancelled stI) i) cs ds
                → Pointwise (ShareSlot (Store.rows S₁) (EvalSt.cancelled stP₁) (EvalSt.cancelled stI₁) i) cs ds
    share-keeps K []       = []
    share-keeps {S₀ = S₀} {S₁ = S₁} K (r ∷ rs) = slot-keeps {S = S₀} {S₁ = S₁} K r ∷ share-keeps {S₀ = S₀} {S₁ = S₁} K rs

    -- the share's emits at the type its stamped slot holds them
    slot-cast : ∀ {i : Fin n} → lookup κ i ≡ sharedᵏ → Val (plainᵏ Γ κ) (emitᵗ (lookup Γ i)) → Val (plainᵏ Γ κ) (lookup (plainᵏ Γ κ) (n ↑ʳ i))
    slot-cast {i} sh = subst (Val (plainᵏ Γ κ)) (sym (sharedEq {Γ = Γ} κ i sh))

    carries-cast : ∀ {u u′} (ε : u′ ≡ emitᵗ u) {es : List (Val (plainᵏ Γ κ) (emitᵗ u))} {vs}
                 → Carries es vs → CarriesU ε (map (subst (Val (plainᵏ Γ κ)) (sym ε)) es) vs
    carries-cast refl {es} c = subst (λ xs → Carries xs _) (sym (map-id es)) c

    -- a share marked dying on both sides
    dying-after : ∀ {sP stP sI stI} (S : St sP stP sI stI) (i : Fin n)
                → After S ([] , sP , shareDying i true stP) ([] , sI , shareDying (n ↑ʳ i) true stI)
    dying-after S i = after (dying S) (λ x → x) dying-arr [] (λ x → x)

    mutual
      path-pass : ∀ {lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)} → Pass p q
      path-pass S root~ b _ _ (fold-root {fin = fin}) fold-root = after S (λ x → x) (λ x → x) (root-values b fin) (λ x → x) , root~
      path-pass S r@(sink~ sh) b sp si dP dI = sink-pass sh S r b sp si dP dI
      path-pass S (map~ L r) b sp si (fold-step step-map dP) (fold-step step-map dI) =
        let X = path-pass S r (carries-map L b) (drop-ot _ _ _ sp) (drop-ot _ _ _ si) dP dI in proj₁ X , map~ L (proj₂ X)
      path-pass S r@(scan~ _ _ _ _ _ _) b sp si (fold-step d dP) dI = resume (scan-arm S r b sp si d dI) (adv d sp) dP
      path-pass S r@(take~ _ _ _ _ _ _ _ _ _) b sp si (fold-step d dP) dI = resume (take-arm S r b sp si d dI) (adv d sp) dP
      path-pass S r@(takeWhile~ _ _ _ _ _ _) b sp si (fold-step d dP) dI = resume (takeWhile-arm S r b sp si d dI) (adv d sp) dP
      path-pass S r@(spent~ _ _ _ _) b sp si (fold-step d dP) dI = resume (take-arm S r b sp si d dI) (adv d sp) dP
      path-pass S r@(spentWhile~ _ _ _ _) b sp si (fold-step d dP) dI = resume (takeWhile-arm S r b sp si d dI) (adv d sp) dP
      path-pass S (outerElem~ fl r) b sp si (fold-step d dP) dI = resume (outerElem-arm S (fl , r) b sp si d dI) (adv d sp) dP
      path-pass S (outerExplode~ fl r) b sp si (fold-step d dP) dI = resume (outerExplode-arm S (fl , r) b sp si d dI) (adv d sp) dP
      path-pass S r@(inner~ refl _ _ _) b sp si (fold-step d dP) dI = resume (inner-arm S r b sp si d dI) (adv d sp) dP
      path-pass S r@(lane~ _ _ _ _) b sp si (fold-step d dP) dI = resume (lane-arm S r b sp si d dI) (adv d sp) dP
      path-pass S r@(deferInner~ _ _ _ _ _ _ _) b sp si (fold-step d dP) dI = resume (deferInner-arm S r b sp si d dI) (adv d sp) dP

      resume : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now oP sP₁ stP₁ ℓ u} {p : Path Γ ℓ u t} {vs fin G rP rI}
             → Arm S now oP sP₁ stP₁ p vs fin G rI → Sound p sP₁ stP₁ → foldPath⇓ now p vs fin sP₁ stP₁ rP
             → Σ (After S (oP ++ proj₁ rP , proj₂ rP) rI) λ A
                 → G (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
      resume (arm A r b si dI rb) sp dP = let X = path-pass (After.store A) r b sp si dP dI in A ⨾ proj₁ X , rb dP (proj₁ X) (proj₂ X)

      -- a slot's partnered reader, by the row the store pairs it with
      slot-pass : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n} {u u′ rid rid′}
                    {p : Path Γ (suc (toℕ i)) u t} {p′ : Path (plainᵏ Γ κ) (suc (toℕ (n ↑ʳ i))) u′ (emitᵗ t)}
                    {vs es} (εI : u′ ≡ emitᵗ u)
                → RowRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI)
                    (rid , atSlot i , (u , p)) (rid′ , atSlot (n ↑ʳ i) , (u′ , p′))
                → CarriesU εI es vs
                → Sound p sP stP → Sound p′ sI stI
                → ∀ {now fin rP rI} → foldPath⇓ now p vs fin sP stP rP → foldPath⇓ now p′ es fin sI stI rI
                → After S rP rI
      slot-pass S refl (read~ hk r refl) c sp si dP dI = proj₁ (resume (read-arm S hk r c si dI) sp dP)

      -- A SHARE'S FAN-OUT ON BOTH SIDES, one partnered reader at a time,
      -- a cut one on both sides skipped
      share-go : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n}
                   (εI : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (lookup Γ i)) {es now vs fin}
               → CarriesU εI es vs
               → ∀ {chs adm}
               → Pointwise (ShareSlot (Store.rows S) (EvalSt.cancelled stP) (EvalSt.cancelled stI) i) chs adm
               → (∀ {x} → x ∈ chs → Sound (proj₂ x) sP stP)
               → (∀ {x y} → x ∈ chs → y ∈ chs → Agree (proj₂ x) (proj₂ y))
               → (∀ {x} → x ∈ adm → Sound (proj₂ x) sI stI)
               → (∀ {x y} → x ∈ adm → y ∈ adm → Agree (proj₂ x) (proj₂ y))
               → ∀ {oP sP₁ stP₁ oI sI₁ stI₁}
               → shareGo⇓ now i vs fin chs sP stP (oP , sP₁ , stP₁)
               → shareGo⇓ now (n ↑ʳ i) es fin adm sI stI (oI , sI₁ , stI₁)
               → After S (oP , sP₁ , stP₁) (oI , sI₁ , stI₁)
      share-go S εI c [] _ _ _ _ go-nil go-nil = after S (λ x → x) (λ x → x) [] (λ x → x)
      share-go S εI c (slotpair (inj₁ _) ∷ ps) hP aP hI aI (go-cut _ g) (go-cut _ g′) =
        share-go S εI c ps (λ m → hP (there m)) (λ m m′ → aP (there m) (there m′)) (λ m → hI (there m)) (λ m m′ → aI (there m) (there m′)) g g′
      share-go S εI c (slotpair (inj₁ (x , _)) ∷ _) _ _ _ _ (go-live y _ _) _ = ⊥-elim (t≢f (trans (sym x) y))
      share-go S εI c (slotpair (inj₁ (_ , x)) ∷ _) _ _ _ _ (go-cut _ _) (go-live y _ _) = ⊥-elim (t≢f (trans (sym x) y))
      share-go S εI c (slotpair (inj₂ (x , _)) ∷ _) _ _ _ _ (go-cut y _) _ = ⊥-elim (t≢f (trans (sym y) x))
      share-go S εI c (slotpair (inj₂ (_ , x , _)) ∷ _) _ _ _ _ (go-live _ _ _) (go-cut y _) = ⊥-elim (t≢f (trans (sym y) x))
      share-go S {i = i} εI c (slotpair (inj₂ (_ , _ , pr)) ∷ ps) hP aP hI aI (go-live _ dP g) (go-live _ dI g′) =
        rebase (A ⨾ share-go (After.store A) εI c (share-keeps {S₀ = S} {S₁ = After.store A} {i = i} (After.keeps A) ps)
                  (λ m → fold-kept dP sP₀ _ (sub-ot (λ r∈ → r∈) ≤-refl (hP (there m))) (aP (here refl) (there m)))
                  (λ m m′ → aP (there m) (there m′))
                  (λ m → fold-kept dI sI₀ _ (sub-ot (λ r∈ → r∈) ≤-refl (hI (there m))) (aI (here refl) (there m)))
                  (λ m m′ → aI (there m) (there m′)) g g′)
        where
          sP₀ = sub-ot (λ r∈ → r∈) ≤-refl (hP (here refl))
          sI₀ = sub-ot (λ r∈ → r∈) ≤-refl (hI (here refl))
          A = slot-pass (delivered S) εI (partner-row κ _ _ _ _ _ (Store.rows S) pr) c sP₀ sI₀ dP dI

      -- A SHARE'S WALK ON BOTH SIDES, one emit at a time: a value every
      -- reader takes on both sides, an emit carrying none the impl's
      -- readers take alone, and the end over the share closed
      share-walk : ∀ {sP stP sI stI} (S : St sP stP sI stI) {lo lo′} {i : Fin n} {h : lo ≤ toℕ i} {h′ : lo′ ≤ toℕ (n ↑ʳ i)}
                     (sh : lookup κ i ≡ sharedᵏ) {now es vs fin rP rI}
                 → Carries es vs
                 → shareWalk⇓ now i vs fin sP stP rP
                 → shareWalk⇓ now (n ↑ʳ i) (map (slot-cast sh) es) fin sI stI rI
                 → After S rP rI
      share-walk S sh [] walk-nil walk-nil = after S (λ x → x) (λ x → x) [] (λ x → x)
      share-walk S {i = i} sh [] (walk-end gP) (walk-end gI) = D ⨾ fan (After.store D) (carries-cast ε []) gP gI
        where
          ε = sharedEq {Γ = Γ} κ i sh
          D = share-spend S sh
          fan = λ S′ c → share-go S′ ε c (share-rows S′) (admit-ot i _ _ (Store.ruleP S′)) (admit-agrees i (Store.ruleP S′))
                           (admit-ot (n ↑ʳ i) _ _ (Store.ruleI S′)) (admit-agrees (n ↑ʳ i) (Store.ruleI S′))
      share-walk S {i = i} {h = h} {h′ = h′} sh (quiet x b c) wP (walk-more gI wI) =
        Q ⨾ share-walk (After.store Q) {h = h} {h′ = h′} sh c wP wI
        where
          ε = sharedEq {Γ = Γ} κ i sh
          Q = after-out (++-identityʳ _)
                (proj₁ (quiet-sink {h = h} {h′ = h′} sh S (sink~ sh) (quiet x b []) refl (sink-ok ε (Store.ruleI S))
                          (sink-intro ε (fold-sink (disp (walk-more gI walk-nil))))))
      share-walk S {i = i} {h = h} {h′ = h′} sh (one x r c) (walk-more gP wP) (walk-more gI wI) =
        A ⨾ share-walk (After.store A) {h = h} {h′ = h′} sh c wP wI
        where
          ε = sharedEq {Γ = Γ} κ i sh
          A = share-go S ε (carries-cast ε (one x r [])) (share-rows S)
                (admit-ot i _ _ (Store.ruleP S)) (admit-agrees i (Store.ruleP S))
                (admit-ot (n ↑ʳ i) _ _ (Store.ruleI S)) (admit-agrees (n ↑ʳ i) (Store.ruleI S)) gP gI

      -- A SHARE'S DISPATCH: the walk, between the share marked dying and
      -- its readers dropped when the group ends it
      share-dispatch : ∀ {sP stP sI stI} (S : St sP stP sI stI) {lo lo′} {i : Fin n} {h : lo ≤ toℕ i} {h′ : lo′ ≤ toℕ (n ↑ʳ i)}
                         (sh : lookup κ i ≡ sharedᵏ) {now es vs fin rP rI}
                     → Carries es vs
                     → dispatchShare⇓ now i h vs fin sP stP rP
                     → dispatchShare⇓ now (n ↑ʳ i) h′ (map (slot-cast sh) es) fin sI stI rI
                     → After S rP rI
      share-dispatch S {h = h} {h′ = h′} sh c (disp {fin = false} wP) (disp wI) = share-walk S {h = h} {h′ = h′} sh c wP wI
      share-dispatch S {i = i} {h = h} {h′ = h′} sh c (disp {fin = true} wP) (disp wI) = W ⨾∅ share-finish (After.store W) sh
        where
          D = dying-after S i
          W = D ⨾ share-walk (After.store D) {h = h} {h′ = h′} sh c wP wI

      -- a share's subject, fanning the group out to every reader
      sink-pass : ∀ {lo lo′} {i : Fin n} {h : lo ≤ toℕ i} {h′ : lo′ ≤ toℕ (n ↑ʳ i)} (sh : lookup κ i ≡ sharedᵏ)
                → Pass (share-sink i h)
                       (subst (λ u → Path (plainᵏ Γ κ) lo′ u (emitᵗ t)) (sharedEq {Γ = Γ} κ i sh) (share-sink (n ↑ʳ i) h′))
      sink-pass {i = i} {h = h} {h′ = h′} sh S _ b _ _ (fold-sink dP) dI =
        share-dispatch S {h = h} {h′ = h′} sh b dP (sink-inv (sharedEq {Γ = Γ} κ i sh) dI) , sink~ sh

      -- AN OUTER'S ELEMENT, ONE PER EMIT, HANDED THE FLATTENER: the
      -- walk, then the outer's end, then the tail resumed on the empty
      -- group.  Handed the flattener and the tails apart, since the frame's
      -- relation does not invert at a variable policy.
      outerElem-arm : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                        {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                        {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)}
                        {vs es fin oP vs₁ fin₁ sP₁ stP₁ rI}
                    → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) → Carries es vs
                    → Sound (thru-outer (flatOp op) m ↠[ h ] p) sP stP
                    → Sound (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q)) sI stI
                    → stepFrame⇓ now (thru-outer (flatOp op) m) p vs fin sP stP (oP , vs₁ , fin₁ , sP₁ , stP₁)
                    → foldPath⇓ now (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q))
                        es fin sI stI rI
                    → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                        (λ π NP NI → PathRel κ π NP NI (thru-outer (flatOp op) m ↠[ h ] p)
                           (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q))) rI
      outerElem-arm S {op = op} {Θ₀ = Θ₀} {ρ₀} {fin = fin} w b sp si dW@(step-thru-outer W) (fold-step step-map (fold-step dW′@(step-thru-outer W′) dR)) =
        let si′ = drop-ot _ _ _ si
            X   = elem-walk S {op = op} {Θ₀ = Θ₀} {ρ₀} (unthru sp) (unthru si′) w b W W′
        in wrap-arm (proj₁ X) (unthru (step-kept _ dW sp))
             (outer-wrap (After.store (proj₁ X)) {op = op} {fin = fin} (proj₂ X) (unthru (step-kept _ dW′ si′)) dR)

      -- THE OUTER'S WALK, an element at a time
      elem-walk : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                    {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {es vs rP rI}
                → Clear m p sP stP → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
                → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                → Carries {echoᵗ u} es vs
                → thruWalk⇓ (flatOp op) m p now (thruEvents vs) sP stP rP
                → thruWalk⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now
                    (thruEvents (map (applyClo (Θ₀ , elemᵛ , ρ₀)) es)) sI stI rI
                → Σ (After S rP rI) λ A
                    → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
      elem-walk S cP cI w [] walk-nil walk-nil = after S (λ x → x) (λ x → x) [] (λ x → x) , w
      elem-walk S {Θ₀ = Θ₀} {ρ₀} cP cI w (quiet e′ bq b) W W′ = quiet-step S cP cI w (elem-quiet {Θ = Θ₀} {ρ₀} e′ bq) b W W′
      elem-walk S {Θ₀ = Θ₀} {ρ₀} cP cI w (one e′ r b) W W′ = one-step S cP cI w (elem-one {Θ = Θ₀} {ρ₀} e′ r) b W W′

      -- an emit with no element: its bare echo, on the impl side alone
      quiet-step : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                     {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {z es vs rP rI}
                 → Clear m p sP stP → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
                 → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                 → QuietElem {u} z → Carries {echoᵗ u} es vs
                 → thruWalk⇓ (flatOp op) m p now (thruEvents vs) sP stP rP
                 → thruWalk⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now
                     (thruEvents (z ∷ map (applyClo (Θ₀ , elemᵛ , ρ₀)) es)) sI stI rI
                 → Σ (After S rP rI) λ A
                     → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
      quiet-step S cP cI w (quiet-elem bx) b W (walk-echo (fold-step d₁ (fold-step step-map dq)) W′) =
        let c₁ = step-clear d₁ cI
            E  = quiet-tail (flat-echo S w (quiet _ bx []) d₁) (tail-of c₁) dq
            X  = elem-walk (After.store (proj₁ E)) cP (fold-clear dq (proj₂ (proj₁ (tail-of c₁))) refl c₁) (proj₂ E) b W W′
        in proj₁ E ⨾ proj₁ X , proj₂ X

      -- an emit with one element: its echo, then its lane
      one-step : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                   {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {w z es vs rP rI}
               → Clear m p sP stP → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
               → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
               → Elem {u} w z → Carries {echoᵗ u} es vs
               → thruWalk⇓ (flatOp op) m p now (thruEvents (w ∷ vs)) sP stP rP
               → thruWalk⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now
                   (thruEvents (z ∷ map (applyClo (Θ₀ , elemᵛ , ρ₀)) es)) sI stI rI
               → Σ (After S rP rI) λ A
                   → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
      one-step S cP cI w (elem {w = inj₁ _} r no-lane) b W (walk-echo (fold-step d₁ (fold-step step-map dq)) W′) =
        let c₁ = step-clear d₁ cI
            E  = quiet-tail (flat-echo S w (quiet _ r []) d₁) (tail-of c₁) dq
            X  = elem-walk (After.store (proj₁ E)) cP (fold-clear dq (proj₂ (proj₁ (tail-of c₁))) refl c₁) (proj₂ E) b W W′
        in proj₁ E ⨾ proj₁ X , proj₂ X
      one-step S cP cI w (elem {w = inj₁ _} r (a-lane ob)) b (walk-cons c W) (walk-echo (fold-step d₁ (fold-step step-map dq)) (walk-cons c′ W′)) =
        let c₁ = step-clear d₁ cI
            E  = quiet-tail (flat-echo S w (quiet _ r []) d₁) (tail-of c₁) dq
            c₂ = fold-clear dq (proj₂ (proj₁ (tail-of c₁))) refl c₁
            C  = consume-pair (After.store (proj₁ E)) (proj₂ E) ob (fresh-path (proj₂ c₂)) c c′
            X  = elem-walk (After.store (proj₁ C)) (consume-clear c cP)
                   (consume-clear c′ c₂) (proj₂ C) b W W′
        in proj₁ E ⨾ (proj₁ C ⨾ proj₁ X) , proj₂ X
      one-step S cP cI w (elem {w = inj₂ _} r no-lane) b (walk-echo dv W) (walk-echo (fold-step d₁ (fold-step step-map dq)) W′) =
        let c₁ = step-clear d₁ cI
            E  = echo-go dv cP (flat-echo S w (one _ r []) d₁) (tail-of c₁) dq
            X  = elem-walk (After.store (proj₁ E)) (fold-clear dv (proj₂ cP) refl cP)
                   (fold-clear dq (proj₂ (proj₁ (tail-of c₁))) refl c₁) (proj₂ E) b W W′
        in proj₁ E ⨾ proj₁ X , proj₂ X
      one-step S cP cI w (elem {w = inj₂ _} r (a-lane ob)) b (walk-echo dv (walk-cons c W)) (walk-echo (fold-step d₁ (fold-step step-map dq)) (walk-cons c′ W′)) =
        let c₁  = step-clear d₁ cI
            E   = echo-go dv cP (flat-echo S w (one _ r []) d₁) (tail-of c₁) dq
            cP₂ = fold-clear dv (proj₂ cP) refl cP
            c₂  = fold-clear dq (proj₂ (proj₁ (tail-of c₁))) refl c₁
            C   = consume-pair (After.store (proj₁ E)) (proj₂ E) ob (fresh-path (proj₂ c₂)) c c′
            X   = elem-walk (After.store (proj₁ C)) (consume-clear c cP₂)
                    (consume-clear c′ c₂) (proj₂ C) b W W′
        in proj₁ E ⨾ (proj₁ C ⨾ proj₁ X) , proj₂ X

      -- a valued echo, restamped: down both tails
      echo-go : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now ℓ ℓ₄ u op m m′ ks}
                  {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {v rP es fin oI sI₁ stI₁ r}
              → foldPath⇓ now p (v ∷ []) false sP stP rP → Clear m p sP stP
              → Restamped S op m m′ ks p q (v ∷ []) es fin oI sI₁ stI₁ → ClearI m′ ks q sI₁ stI₁ → foldPath⇓ now q es fin sI₁ stI₁ r
              → Σ (After S rP (oI ++ proj₁ r , proj₂ r)) λ A
                  → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ r)))
      echo-go {stP = stP} {rP = rP} {stI₁ = stI₁} {r = r} dv cP (restamped A (fl , rel) c refl) cI dq =
        let X  = path-pass (After.store A) rel c (proj₂ cP) (proj₂ (proj₁ cI)) dv dq
            F  = flat-move (EvalSt.nodes stP) (EvalSt.nodes stI₁) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ r)))
                   (After.grows (proj₁ X)) (missed dv cP) (missed dq (proj₁ cI)) (missed dq (proj₂ cI , proj₂ (proj₁ cI))) fl
        in A ⨾ proj₁ X , F , proj₂ X

    -- THE TWO ROWS A MINTED SOURCE'S CHAINS CAN BE, each a walk and an
    -- end.  A cold read's impl chain runs its input block alone into a
    -- merge whose walk folds the path its partner runs; a deferred hop's
    -- walks the hop's merge on both sides.
    postulate
      -- A COLD READ'S BLOCK WALKED: the impl alone runs the inner, the
      -- bracket and the stamp, and its merge's walk folds the tail over
      -- what the plain path folds the group into
      block-walk : ∀ {sP stP sI stI} (S : St sP stP sI stI) {src src′ s} {vs : List (Val Γ s)} {vs′ : List (Val (plainᵏ Γ κ) (plainᵗ s))}
                 → Head src src′ {s} {plainᵗ s} vs vs′ → SrcPair κ (Sched.live sP) (Sched.live sI) src src′ s (plainᵗ s)
                 → ∀ {lo ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ m1 j1 b m2 Θ₀ ρ₀ Θ₃ fr ρ₃ Θ₄ ρ₄}
                     {h₁ : lo ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                     {p : Path Γ ℓ s t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ s) (emitᵗ t)}
                 → InputBlock κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (plainᵗ s) (map-f (Θ₀ , inrᵗ (varᵗ (here refl)) , ρ₀) ↠[ h₁ ] (from-inner mergeAllᵒ m1 j1 ↠[ h₂ ] (batchSync-f b ↠[ h₃ ] (map-f (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃) ↠[ h₄ ] (map-f (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄) ↠[ h₅ ] (thru-outer mergeAllᵒ m2 ↠[ h₆ ] q)))))) q
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                 → Sound p sP stP → Sound (map-f (Θ₀ , inrᵗ (varᵗ (here refl)) , ρ₀) ↠[ h₁ ] (from-inner mergeAllᵒ m1 j1 ↠[ h₂ ] (batchSync-f b ↠[ h₃ ] (map-f (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃) ↠[ h₄ ] (map-f (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄) ↠[ h₅ ] (thru-outer mergeAllᵒ m2 ↠[ h₆ ] q)))))) sI stI
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
      -- THE BLOCK'S END: the merge wraps up and the impl's tail folds what
      -- the wrap hands on, the plain path having ended already
      block-end  : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now m2 ℓ s} {q : Path (plainᵏ Γ κ) ℓ (emitᵗ s) (emitᵗ t)}
                     {rP o₁ o₂ oW sW stW fin r}
                 → After S rP (o₁ ++ (o₂ ++ oW) , sW , stW)
                 → Sound q (proj₁ (proj₂ (thruWrap mergeAllᵒ m2 fin (sW , stW)))) (proj₂ (proj₂ (thruWrap mergeAllᵒ m2 fin (sW , stW))))
                 → foldPath⇓ now q [] (proj₁ (thruWrap mergeAllᵒ m2 fin (sW , stW)))
                     (proj₁ (proj₂ (thruWrap mergeAllᵒ m2 fin (sW , stW)))) (proj₂ (proj₂ (thruWrap mergeAllᵒ m2 fin (sW , stW)))) r
                 → After S rP (o₁ ++ (o₂ ++ (oW ++ proj₁ r)) , proj₂ r)
      -- A DEFERRED HOP'S WALK: the body each emit carries is subscribed
      -- through the hop's merge on both sides, the tails staying related
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
                    p [] (proj₁ (thruWrap mergeAllᵒ nid fin (sP′ , stP′))) none (oI ++ proj₁ r , proj₂ r)


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
              → After S rP rI
    block-arm S hd sp blk@(block {m2 = m2} _ _ _ _ _ _ _ _) r soP si dP
              (fold-step step-map (fold-step {out₁ = o₁} d₁ (fold-step {out₁ = o₂} {fin′ = f₂} d₂ (fold-step step-map (fold-step step-map
                (fold-step {out₁ = oW} dW@(step-thru-outer W) dR)))))) =
      let s₁ = drop-ot _ _ _ (step-kept _ d₁ (drop-ot _ _ _ si))
          s₃ = drop-ot _ _ _ (drop-ot _ _ _ (drop-ot _ _ _ (step-kept _ d₂ s₁)))
      in block-end {m2 = m2} {o₁ = o₁} {o₂ = o₂} {oW = oW} {fin = f₂}
           (block-walk S hd sp blk r soP si dP d₁ d₂ W) (drop-ot _ _ _ (step-kept _ dW s₃)) dR

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
              → Arm S now oP sP₁ stP₁ p vs₁ fin₁ none rI
    hop-arm S hd sp k nP nI r si {fin = fin} dW@(step-thru-outer W) (fold-step dW′@(step-thru-outer W′) dR) =
      let X = hop-walk S hd sp k nP nI r (unthru si) W W′
      in hop-end {fin = fin} (proj₁ X) (proj₂ X) (drop-ot _ _ _ (step-kept _ dW′ si)) dR


    -- A SHARE'S FAN-OUT AGAINST THE PLAIN CASCADE OVER THE SAME READERS,
    -- one reader at a time: the plain chain and the admitted row it is
    -- partnered with, a cut one on both sides skipped
    fan-go : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n} {a : Arrival Γ}
               (εI : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (arrTy a)) {es now vs fin}
           → CarriesU εI es vs → arrTick a ≡ now
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
    fan-go S εI c ta [] _ _ _ _ casc-nil go-nil = after S (λ x → x) (λ x → x) [] (λ x → x)
    fan-go S εI c ta (slotpair (inj₁ _) ∷ ps) hP aP hI aI (casc-cut _ g) (go-cut _ g′) =
      fan-go S εI c ta ps (λ m → hP (there m)) (λ m m′ → aP (there m) (there m′)) (λ m → hI (there m)) (λ m m′ → aI (there m) (there m′)) g g′
    fan-go S εI c ta (slotpair (inj₁ (x , _)) ∷ _) _ _ _ _ (casc-live y _ _) _ = ⊥-elim (t≢f (trans (sym x) y))
    fan-go S εI c ta (slotpair (inj₁ (_ , x)) ∷ _) _ _ _ _ (casc-cut _ _) (go-live y _ _) = ⊥-elim (t≢f (trans (sym x) y))
    fan-go S εI c ta (slotpair (inj₂ (x , _)) ∷ _) _ _ _ _ (casc-cut y _) _ = ⊥-elim (t≢f (trans (sym y) x))
    fan-go S εI c ta (slotpair (inj₂ (_ , x , _)) ∷ _) _ _ _ _ (casc-live _ _ _) (go-cut y _) = ⊥-elim (t≢f (trans (sym y) x))
    fan-go S εI c refl (slotpair (inj₂ (_ , _ , pr)) ∷ ps) hP aP hI aI (casc-live _ dP g) (go-live _ dI g′) =
      rebase (A ⨾ fan-go (After.store A) εI c refl (map-slot {S₀ = S} {S₁ = After.store A} (After.keeps A) ps)
                (λ m → fold-kept (unchain dP) sP₀ _ (sub-ot (λ r∈ → r∈) ≤-refl (hP (there m))) (aP (here refl) (there m)))
                (λ m m′ → aP (there m) (there m′))
                (λ m → fold-kept dI sI₀ _ (sub-ot (λ r∈ → r∈) ≤-refl (hI (there m))) (aI (here refl) (there m)))
                (λ m m′ → aI (there m) (there m′)) g g′)
      where
        sP₀ = sub-ot (λ r∈ → r∈) ≤-refl (hP (here refl))
        sI₀ = sub-ot (λ r∈ → r∈) ≤-refl (hI (here refl))
        A = slot-pass (delivered S) εI (partner-row κ _ _ _ _ _ (Store.rows S) pr) c sP₀ sI₀ (unchain dP) dI

        map-slot : ∀ {sP stP sI stI sP₁ stP₁ sI₁ stI₁} {S₀ : St sP stP sI stI} {S₁ : St sP₁ stP₁ sI₁ stI₁} {i : Fin n} {u}
                     {cs : List (RegId × AtFloor Γ u t)} {ds}
                 → Keeps S₀ S₁
                 → Pointwise (SlotPair (Store.rows S₀) (EvalSt.cancelled stP) (EvalSt.cancelled stI) i) cs ds
                 → Pointwise (SlotPair (Store.rows S₁) (EvalSt.cancelled stP₁) (EvalSt.cancelled stI₁) i) cs ds
        map-slot K []       = []
        map-slot {S₀ = S₀} {S₁ = S₁} K (r ∷ rs) = slot-keeps {S = S₀} {S₁ = S₁} K r ∷ map-slot {S₀ = S₀} {S₁ = S₁} K rs

    -- WHAT A HOT ARRIVAL'S IMPL CHAIN DOES BEFORE THE SHARE: its input block
    -- runs alone, the plain side not moving, and hands the share the one emit
    -- that carries the arrival's value
    data HotStart {sP stP sI stI} (S : St sP stP sI stI) (a : Arrival Γ) (a′ : Arrival (plainᵏ Γ κ)) (i : Fin n)
                  (oI : Stream (plainᵏ Γ κ) (emitᵗ t)) (sI₁ : Sched (plainᵏ Γ κ)) (stI₁ : EvalSt ei) : Set where
      hot-start-at : ∀ {oB sI₂ stI₂ e lo rD} {below : lo ≤ toℕ (n ↑ʳ i)}
                       {εI : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (arrTy a)} {ty : arrTy a ≡ lookup Γ i}
                   → (A : After S ([] , sP , stP) (oB , sI₂ , stI₂))
                   → CarriesU εI (e ∷ []) (arrVal a ∷ [])
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
      -- THE IMPL'S ONE CHAIN AT A HOT ARRIVAL'S RAW SLOT, ONCE ITS SHARE HAS
      -- CONNECTED: the raw row's step over the arrival's value, its input
      -- block run alone into the share.  What it owes is the block's run:
      -- the one stamped emit carrying the value, the plain side not moving
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
                    (record stI { delivered = rid ∷ EvalSt.delivered stI }) (oI , sI₁ , stI₁)
                → HotStart S a a′ i oI sI₁ stI₁

    -- a minted source's partnered chain, by the row the store pairs it with
    row-pass : ∀ {sP stP sI stI} (S : St sP stP sI stI) {src src′ u u′} {vs : List (Val Γ u)} {vs′ : List (Val (plainᵏ Γ κ) u′)}
             → Head src src′ {u} {u′} vs vs′
             → ∀ {rid rid′ lo lo′} {p : Path Γ lo u t} {p′ : Path (plainᵏ Γ κ) lo′ u′ (emitᵗ t)}
             → RowRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI)
                 (rid , atDyn src lo , (u , p)) (rid′ , atDyn src′ lo′ , (u′ , p′))
             → Sound p sP stP → Sound p′ sI stI
             → ∀ {now fin rP rI} → foldPath⇓ now p vs fin sP stP rP → foldPath⇓ now p′ vs′ fin sI stI rI
             → After S rP rI
    row-pass S hd (cold~ sp blk r refl) soP soI dP dI = block-arm S hd sp blk r soP soI dP dI
    row-pass S hd (defer~ sp k nP nI r refl) soP soI (fold-step d dP) dI = proj₁ (resume (hop-arm S hd sp k nP nI r soI d dI) (adv d soP) dP)
