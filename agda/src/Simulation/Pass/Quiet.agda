------------------------------------------------------------------
-- THE PASS'S VOCABULARY AND ITS QUIET ARMS: the relations a pass
-- reads, a flattener's outer walked, and the frames that hand on
-- nothing.  `Simulation.Pass` is the pass itself, over this.
------------------------------------------------------------------
module Simulation.Pass.Quiet where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∨_; _∧_)
open import Data.Fin     using (Fin; toℕ; _↑ʳ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.List    using (List; []; _∷_; _++_; map; concatMap; null)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; ++⁺) renaming (map to pw-map)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (lookup to lookupᵃ; map to mapᵃ)
open import Data.Bool.ListAction using (any)
open import Data.Fin.Properties using (toℕ<n; toℕ-↑ˡ; toℕ-↑ʳ; ↑ʳ-injective; toℕ-injective) renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe   using (Maybe; nothing; just; is-nothing)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _<_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; <⇒≢; <-≤-trans; <-trans; m≤m+n; n≤1+n; m<n⇒m<1+n; <-irrefl)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit    using (tt)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Vec     using (lookup)
open import Data.List.Properties using (++-assoc; ++-identityʳ; map-id)
open import Relation.Nullary using (yes; no; ¬_)
open import Decide       using (≡ᵇ→≡)
open import Function using (case_of_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)

open import Rx.Prim      using (Tick; valueᵖ; completeᵖ)
open import Rx.Exp       using (Ty; Ctx; Closed; Val; Env; Tm; ofᵉ; evalWith; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; _≟ᵗ_; unitᵗ; _×ᵗ_; _+ᵗ_; obs;
  FnClo; applyClo; varᵗ; unit̂; pairᵗ; inlᵗ; inrᵗ; sndᵗ; uniqᵗ)
open import Rx.Evaluator using (Stream; Sched; EvalSt; NodeId; markDlv; NodeState; Arrival; arrVal; arrTy; arrTick; Path;
  root; share-sink; _↠[_]_; scan-f; take-f; map-f; batchSync-f; thru-outer; from-inner; mergeAllᵒ; lookupNode;
  mergeAll-st; echoᵗ; thruEvents; thruWrap; setNode; cell-st; batchSync-st; scanVals; take-st; spentAt;
  takeVals; exhaust-st; switch-st; switchKill; hasRoom; consumeUsable; switchᵒ; exhaustᵒ;
  RegId; RegRow; AtFloor; atDyn; atSlot; shareAdmit; shareDying; memberSource; skipᵇ;
  regSource; aliveThroughᶠ)
open import Rx.Evaluator.Domain using (flatOp; foldPath⇓; fold-root; fold-step; stepFrame⇓; step-map; step-scan; step-from-inner; react-false; step-thru-outer; thruWalk⇓;
  walk-nil; walk-echo; walk-cons; thruConsume⇓; inner; consume-all-sub; consume-all-enqueue;
  consume-all-nil; consume-exhaust-sub; consume-exhaust-nil; consume-switch-sub;
  consume-switch-nil; subscribeInner⇓; subscribeE⇓; chainStep⇓; chain-step; dispatchShare⇓;
  fold-sink; disp; walk-more; shareWalk⇓; shareGo⇓; go-nil; go-cut; go-live; subs-of; react-alive; react-dead;
  innerFinish⇓; finish-all-drain; finish-nil; drain-spent)
open import SExp.Syntax  using (Kinds; plainᵏ; plainᵗ; emitᵗ; sharedᵏ; hotᵏ)
open import SExp.Elaborate using (restampᵛ; subscribeᵛ; deliveryᵛ; flatStepᵛ; elemᵛ; explodeᵛ; FlatSᵗ; ScanAᵗ; CutS; cutOpenᵛ; cutOutᵛ)
open import Simulation.Schedules using (HeadOf)
open import Simulation.Stores using (V; Spent; dlvᵇ; EmitRel; ObsRel; Flattener; FlatNodes; CurRel; merge~; switch~; exhaust~;
  Src; sharedEq; PathRel; root~; sink~; map~; scan~; takeWhile~; spentWhile~; outerElem~;
  outerExplode~; inner~; elab; deferInner~; hotEq; RowRel; read~; cold~; defer~; RegRel; [];
  _∷_; mach; MachRow; hot~; Store; Arr; Partners; pair-ids; spent-zip; partner-row;
  partner-mem; Named; named-node; MergeAt; LiveRows; live; Inv; inv-dlv; inv-dying; live-quiet;
  live-keep; live-write; outerDoneᵇ; LiveIf; live-if; LiveOn; thruNodes; live-if-set; live-if-cons; live-if-drop; live-if-under; live-if-take; LiveFor; live-for)
open import Simulation.After using (readᴾ; readᴵ; PairedR; skip-cut; module Kept)
open import SExp.Plain   using (plainValues)
open import SExp.InstEmit.Decode using (decodeEmits)
open import Batchable.Inst-Extract using (instExtract)
open import Simulation.Cut using (cut-kill)
open import Simulation.Take using (module Takes; scan-at; take-open-at; cell-take)
open import Simulation.Scan using (module Scans)
open import Simulation.Arm using (module Arms; Unmoved; unmoved; Clear; ClearI; missed; on-drop; unthru; step-clear;
  fold-clear; adv; fold-unmoved; consume-clear; Out; Gone; gone-nodes; Passes; headKey; scan-c)
open import Simulation.Sweep using (t≢f; stamp-rows; stamped<; sameSource-no)
open import Rx.Mint using (counter; sourceᵏ; regᵏ; nodeᵏ; setAt)
open import Decide using (≡ᵇ-refl; ≡ᵇ→≡)
open import Simulation.Write using (module Write; module CellWrite; module FlatCellWrite; module MergeDone; key-same; vals-same; apart)
open import Simulation.Walks using (module Walkers)
open import Simulation.Size using (sz-subscribeE; sz-subscribeInner; sz-thruConsume; sz-1)
open import Simulation.Grow using (nodes-grow; flatG; pathG; fresh-off)
open import Rx.Evaluator.Freshness using (nodeCt; lookup-set; set-above)
open import Simulation.Elem using (pw-one; pw-none; paysOf; values-decode; echoList; elem-run; quiet-run)
open import Rx.Evaluator.Reducible.Support using (Sound; fresh-path; fresh-inner; sub-ot; sub-on; kill-sub; switchKill-ct; sub-rule;
  switchKill-nodes; drop-ot; head-on; self-node; Agree; Rule; admit-agree; termini; admit-ot; fresh-rows)
open import Rx.Evaluator.Reducible.Dead-Kept using (alive-dead)
open import Rx.Evaluator.Reducible.Rule-Kept using (step-kept; fold-kept)

-- AN EMIT'S RELATION NEVER READS ITS INSTANT: retagging every value's
-- instant keeps the values related
retag : ∀ {I A B : Set} {R : I × A → B → Set} {i j : I} {xs : List A} {ws : List B}
      → (∀ {x w} → R (i , x) w → R (j , x) w)
      → Pointwise R (map (i ,_) xs) ws → Pointwise R (map (j ,_) xs) ws
retag {xs = []}     f []       = []
retag {xs = _ ∷ _} f (r ∷ rs) = f r ∷ retag f rs

-- a node written what it already holds leaves the table as it was
set-same : ∀ {m} {Δ : Ctx m} (nid : NodeId) (ns : NodeState Δ) (ts : List (NodeId × NodeState Δ))
         → lookupNode nid ts ≡ just ns → setNode nid ns ts ≡ ts
set-same nid ns []            ()
set-same nid ns ((k , s) ∷ r) e with k ≡ᵇ nid in eq
... | true with ≡ᵇ→≡ k nid eq | e
...   | refl | refl = refl
set-same nid ns ((k , s) ∷ r) e | false = cong ((k , s) ∷_) (set-same nid ns r e)

-- A SCAN'S STEP AT A NODE HOLDING NO ACCUMULATOR OF ITS OWN TYPE
-- passes nothing and writes nothing; at one that does, it is `scan-at`'s
scan-any : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {s u lo} {fn : FnClo Δ (u ×ᵗ s) u} {k} {κ′ : Path Δ lo u t}
             {now vals fin sc} {st : EvalSt e} {r}
         → stepFrame⇓ now (scan-f fn k) κ′ vals fin sc st r
         → r ≡ ([] , [] , fin , sc , st)
           ⊎ Σ (Val Δ u) λ a → lookupNode k (EvalSt.nodes st) ≡ just (cell-st a)
               × r ≡ ([] , proj₁ (scanVals fn a vals) , fin , sc
                     , record st { nodes = setNode k (cell-st (proj₂ (scanVals fn a vals))) (EvalSt.nodes st) })
scan-any {u = u} {k = k} {st = st} step-scan with lookupNode k (EvalSt.nodes st)
... | nothing                      = inj₁ refl
... | just (take-st _)             = inj₁ refl
... | just (mergeAll-st _ _ _ _)   = inj₁ refl
... | just (switch-st _ _)         = inj₁ refl
... | just (exhaust-st _ _)        = inj₁ refl
... | just (batchSync-st _ _ _)    = inj₁ refl
... | just (cell-st {w} a) with w ≟ᵗ u
...   | yes refl = inj₂ (a , refl , refl)
...   | no _     = inj₁ refl

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

-- nothing related to nothing
nil-all : ∀ {A B : Set} {R : A → B → Set} {P : A → Set} {xs} → Pointwise R xs [] → All P xs
nil-all [] = []

-- AN INNER THE COUNTER HANDS OUT NEXT IS DEAD: no row threads a node
-- the counter has not passed
fresh-dead : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {sched : Sched Δ} {st : EvalSt e}
           → Rule sched st → any (aliveThroughᶠ (nodeCt sched) st) (EvalSt.registry st) ≡ false
fresh-dead {e = e} {sched = sched} {st = st} ru = alive-dead {e = e} (nodeCt sched) {st = st} (λ r∈ th → ⊥-elim (<-irrefl refl (fresh-rows ru r∈ _ th)))

-- an unbounded merge never queues
no-queue : ∀ {n} {Γ : Ctx n} {w a q od lim act q′ od′}
         → just (mergeAll-st {Γ = Γ} {t = w} nothing a q od) ≡ just (mergeAll-st {t = w} lim act q′ od′)
         → hasRoom lim act ≡ false → ⊥
no-queue refl h = t≢f h

-- a delivery or a dying share names what the run already had
dlv-named : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {f} {sched : Sched Γ} {st : EvalSt e} {rid} fin
          → Named f sched st → rid < counter (Sched.mint sched) regᵏ → Named f sched (markDlv fin rid st)
dlv-named false N _ = N
dlv-named true  N b = record { slots-below = Named.slots-below N ; ords-below = Named.ords-below N ; srcs-below = Named.srcs-below N
                             ; cut-below = Named.cut-below N ; dlv-below = b ∷ Named.dlv-below N ; dying-below = Named.dying-below N }

dying-named : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {f} {sched : Sched Γ} {st : EvalSt e} (i : Fin n)
            → Named f sched st → toℕ i < counter (Sched.mint sched) sourceᵏ → Named f sched (shareDying i true st)
dying-named i N b = record { slots-below = Named.slots-below N ; ords-below = Named.ords-below N ; srcs-below = Named.srcs-below N
                           ; cut-below = Named.cut-below N ; dlv-below = Named.dlv-below N ; dying-below = b ∷ Named.dying-below N }

-- the fold a chain step runs
unchain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {a : Arrival Γ} {vs fin x sched st r}
        → chainStep⇓ {e = e} a vs fin x sched st r → foldPath⇓ (arrTick a) (proj₂ x) vs fin sched st r
unchain (chain-step d) = d

-- a chain step marks its partnered pair of rows delivered, alike
delivered : ∀ {n} {Γ : Ctx n} {t} {κ : Kinds n} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
              {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
          → (S : Store κ sP stP sI stI) → ∀ {fin x x′} → Partners κ _ _ _ _ _ (Store.rows S) x x′
          → Store κ sP (markDlv fin (proj₁ x) stP) sI (markDlv fin (proj₁ x′) stI)
delivered {κ = κ} {sP = sP} {stP} {sI} {stI} s {fin} {x} {x′} pr = record
  { π = π ; π-keys = π-keys ; π-vals = π-vals ; pairs-below = pairs-below ; sources = sources ; numbers = numbers ; distinct = distinct
  ; sync = sync ; rows = rows ; latches = latches ; dying-done = dying-done
  ; dlv-alike = dlv fin ; dying-alike = dying-alike ; bounded = bounded ; swept = swept ; uncut = uncut
  ; named = dlv-named fin (proj₁ named) (lookupᵃ (proj₁ fresh-ids) (proj₁ mx)) , dlv-named fin (proj₂ named) (lookupᵃ (proj₂ fresh-ids) (proj₂ mx)) ; rids = rids ; fresh-ids = fresh-ids ; above = above ; census = census ; owned = owned
  ; ruleP = sub-rule (λ r∈ → r∈) ≤-refl ruleP ; ruleI = sub-rule (λ r∈ → r∈) ≤-refl ruleI
  ; scripts = scripts ; inv = inv-dlv fin (proj₁ x′) inv }
  where
    open Store s
    mx = partner-mem κ _ _ _ _ _ rows pr
    dlv : (f : Bool) → Spent κ π (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI) rows
                         (dlvᵇ (markDlv f (proj₁ x) stP)) (dlvᵇ (markDlv f (proj₁ x′) stI))
    dlv false = dlv-alike
    dlv true  = spent-zip κ _ _ _ _ _ rows _∨_ (pair-ids κ _ _ _ _ _ rows (proj₁ rids) (proj₂ rids) {x} {x′} pr) dlv-alike

-- the arrival's pair against the rows is as it was, since the rows are
delivered-arr : ∀ {n} {Γ : Ctx n} {t} {κ : Kinds n} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
                  {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
                  {S : Store κ sP stP sI stI} {fin x x′} {pr : Partners κ _ _ _ _ _ (Store.rows S) x x′} {s s′ u u′}
              → Arr S s s′ u u′ → Arr (delivered S {fin} pr) s s′ u u′
delivered-arr ar = record { boundP = boundP ; boundI = boundI ; rows = rows ; lists = lists } where open Arr ar

-- a shared slot's share marked dying on both sides, a pair of rows at
-- the slot and its stamp alike
dying : ∀ {n} {Γ : Ctx n} {t} {κ : Kinds n} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
          {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
      → Store κ sP stP sI stI → (i : Fin n) → lookup κ i ≡ sharedᵏ
      → Store κ sP (shareDying i true stP) sI (shareDying (n ↑ʳ i) true stI)
dying {n} {κ = κ} {stP = stP} {stI = stI} s i sk = record
  { π = π ; π-keys = π-keys ; π-vals = π-vals ; pairs-below = pairs-below ; sources = sources ; numbers = numbers ; distinct = distinct
  ; sync = sync ; rows = rows ; latches = latches
  ; dying-done = λ j hj → (λ m → proj₁ (dying-done j hj) (trans (sym (mn (EvalSt.dying stP) (neP j hj))) m))
                        , (λ m → proj₂ (dying-done j hj) (trans (sym (mn (EvalSt.dying stI) (λ e → neP j hj (cong toℕ (↑ʳ-injective n j i (toℕ-injective e)))))) m))
  ; dlv-alike = dlv-alike ; dying-alike = spent-zip κ _ _ _ _ _ rows _∨_ (stamp-rows κ i rows (proj₁ above) (proj₂ above)) dying-alike ; bounded = bounded ; swept = swept ; uncut = uncut
  ; named = dying-named i (proj₁ named) (<-trans (toℕ<n i) (Named.slots-below (proj₁ named)))
          , dying-named (n ↑ʳ i) (proj₂ named) (<-trans (stamped< i) (Named.slots-below (proj₂ named))) ; rids = rids ; fresh-ids = fresh-ids ; above = above ; census = census ; owned = owned
  ; ruleP = sub-rule (λ r∈ → r∈) ≤-refl ruleP ; ruleI = sub-rule (λ r∈ → r∈) ≤-refl ruleI
  ; scripts = scripts ; inv = inv-dying (n ↑ʳ i) inv }
  where
  open Store s
  mn : ∀ {x k : ℕ} xs → x ≢ k → memberSource x (k ∷ xs) ≡ memberSource x xs
  mn {x} xs ne = cong (_∨ memberSource x xs) (sameSource-no ne)
  neP : ∀ j → lookup κ j ≡ hotᵏ → toℕ j ≢ toℕ i
  neP j hj e with toℕ-injective e
  ... | refl with trans (sym hj) sk
  ... | ()

dying-arr : ∀ {n} {Γ : Ctx n} {t} {κ : Kinds n} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
              {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
              {S : Store κ sP stP sI stI} {i : Fin n} {sh : lookup κ i ≡ sharedᵏ} {s s′ u u′}
          → Arr S s s′ u u′ → Arr (dying S i sh) s s′ u u′
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

-- related queues are empty together
pw-null : ∀ {A B : Set} {R : A → B → Set} {xs ys} → Pointwise R xs ys → null xs ≡ null ys
pw-null []      = refl
pw-null (_ ∷ _) = refl

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

-- AN OUTER'S END NOT YET COME leaves its flattener open
wrap-false : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {op nid fin} {sc : Sched Δ} {st : EvalSt e}
           → fin ≡ false → proj₁ (thruWrap op nid fin (sc , st)) ≡ false
wrap-false refl = refl

module PassQ {n} {Γ : Ctx n} (κ : Kinds n) where

  open Arms {Γ = Γ} κ public
  open Walkers {Γ = Γ} κ using (Walker)
  open Takes {Γ = Γ} κ using (module While; cut-group)
  open Scans {Γ = Γ} κ using (module Cells; scan-group)

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

  postulate
    -- AN EMIT CARRYING NOTHING, EXPLODED: one element, the echo carrying
    -- nothing and no lane, as an `of` of that element alone
    --
    -- TWIN: `quiet-run` -- the same split read through `explodeᵛ`'s fold
    --   over no payloads, whose run is the bare element.
    explode-run : ∀ {u Θ ρ} e′ → Bare {echoᵗ u} e′
                → Σ (List Ty) λ Θ′ → Σ (Tm (plainᵏ Γ κ) [] [] Θ′ (echoᵗ (emitᵗ u))) λ tm → Σ (Env (plainᵏ Γ κ) Θ′) λ ρ′
                    → applyClo {s = emitᵗ (echoᵗ u)} {t = obs (echoᵗ (emitᵗ u))} (Θ , explodeᵛ , ρ) e′ ≡ (Θ′ , ofᵉ (tm ∷ []) , ρ′)
                      × QuietElem {u} (evalWith tm ρ′)

  -- THE VALUE A POPPED SOURCE HANDS ITS CHAINS, on both sides: the head
  -- of each partnered source's pending list, at the row's source
  data Head (src src′ : ℕ) : ∀ {u u′} → List (Val Γ u) → List (Val (plainᵏ Γ κ) u′) → Set where
    head : ∀ {l l′ a a′} → Src κ l l′ → HeadOf l a → HeadOf l′ a′
         → Arrival.source a ≡ src → Arrival.source a′ ≡ src′
         → Head src src′ (arrVal a ∷ []) (arrVal a′ ∷ [])
    nohead : ∀ {u u′} → Head src src′ {u} {u′} [] []

  -- the related values at the root: the emits' payloads in order, a
  -- valueless emit decoding to none and the end to nothing on either side
  carried : ∀ {t es vs} → Carries {t} es vs → ∀ fin
    → Pointwise (λ x w → V κ t (proj₂ x) w)
        (instExtract (decodeEmits (map valueᵖ es ++ (if fin then completeᵖ ∷ [] else []))))
        (plainValues (map valueᵖ vs ++ (if fin then completeᵖ ∷ [] else [])))
  carried []             false = []
  carried []             true  = []
  carried (quiet _ b c)  fin   = ++⁺ b (carried c fin)
  carried (one _ r c)    fin   = ++⁺ r (carried c fin)

  root-values : ∀ {t es vs} → Carries {t} es vs → ∀ fin
    → Pointwise (λ x w → V κ t (proj₂ x) w)
        (readᴵ ((map valueᵖ es ++ (if fin then completeᵖ ∷ [] else [])) ∷ []))
        (readᴾ ((map valueᵖ vs ++ (if fin then completeᵖ ∷ [] else [])) ∷ []))
  root-values {t} {es} {vs} c fin =
    subst₂ (Pointwise (λ x w → V κ t (proj₂ x) w))
      (cong (λ z → instExtract (decodeEmits z)) (sym (++-identityʳ (map valueᵖ es ++ (if fin then completeᵖ ∷ [] else [])))))
      (cong plainValues (sym (++-identityʳ (map valueᵖ vs ++ (if fin then completeᵖ ∷ [] else [])))))
      (carried c fin)

  module InQ {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

    open Kept {Γ = Γ} κ {t} {ep} {ei}
    open Run {t} {ep} {ei} public
    open While {t} {ep} {ei} using (takeWhile-arm; while-write)
    open Cells {t} {ep} {ei} using (scan-arm; scan-write)

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

    -- the restamp's scan is a cell, and its projection is transparent
    gone-restamp : ∀ {sP stP sI stI} (S : St sP stP sI stI) {ℓ₂ ℓ₃ ℓ₄ u Θ₁ ρ₁ ks Θ₂ ρ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                   {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)}
                 → Gone (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) stI → Gone q stI
    gone-restamp S {u = u} {Θ₁} {ρ₁} {ks} {Θ₂} {ρ₂} {h₃} {h₄} {q} =
      gone-cell S {s = emitᵗ u} {u = FlatSᵗ u} {f = scan-f (Θ₁ , flatStepᵛ , ρ₁) ks} {h = h₃}
        {q = map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₄ ] q} scan-c

    -- where the walk has got to: the flattener, and the tails it hands to
    Walkedˣ : ∀ {ℓ ℓ₄ u} → List NodeId → FlatOp → NodeId → NodeId → NodeId
            → Path Γ ℓ u t → Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t) → Goal
    Walkedˣ {u = u} xs op m m′ ks p q π NP NI = Flattener {Γ = Γ} κ π {t = t} NP NI u op m m′ ks xs × PathRel {Γ = Γ} κ π NP NI p q

    -- one no outer explodes into: its row names nothing past the cell
    Walked : ∀ {ℓ ℓ₄ u} → FlatOp → NodeId → NodeId → NodeId
           → Path Γ ℓ u t → Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t) → Goal
    Walked = Walkedˣ []

    -- a flattener stays one where its nodes do and the pairing grows
    flat-move : ∀ {π π′ u op m m′ ks xs} (NP : List (NodeId × NodeState Γ)) (NI : List (NodeId × NodeState (plainᵏ Γ κ)))
                  (NP′ : List (NodeId × NodeState Γ)) (NI′ : List (NodeId × NodeState (plainᵏ Γ κ)))
              → (∀ {x} → x ∈ π → x ∈ π′) → Unmoved m NP′ NP → Unmoved m′ NI′ NI → Unmoved ks NI′ NI
              → Flattener {Γ = Γ} κ π {t = t} NP NI u op m m′ ks xs → Flattener {Γ = Γ} κ π′ {t = t} NP′ NI′ u op m m′ ks xs
    flat-move _ _ _ _ g (unmoved eP) (unmoved eI) (unmoved eK) (pm , x , x′ , lP , lI , fn , c , lk) =
      g pm , x , x′ , trans eP lP , trans eI lI , nodes-grow {Γ = Γ} κ g fn , c , trans eK lk

    -- an echo through the restamp's scan, on the impl side alone: the
    -- flattener kept, and the group the scan hands its projection
    data Restamped {sP stP sI stI} (S : St sP stP sI stI) {ℓ ℓ₄ u} (ns : List NodeId) (op : FlatOp) (m m′ ks : NodeId)
                   (p : Path Γ ℓ u t) (q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)) (ws : List (Val Γ u))
                   (es : List (Val (plainᵏ Γ κ) (emitᵗ u))) (fin : Bool)
                   (oI : Stream (plainᵏ Γ κ) (emitᵗ t)) (sI₁ : Sched (plainᵏ Γ κ)) (stI₁ : EvalSt ei) : Set where
      restamped : (A : After S ([] , sP , stP) (oI , sI₁ , stI₁))
                → Walkedˣ ns op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes stI₁)
                → Carries es ws → fin ≡ false
                → Restamped S ns op m m′ ks p q ws es fin oI sI₁ stI₁

    -- the outer's end on both sides, as far as the impl's tail
    data Wrapped {sP stP sI stI} (S : St sP stP sI stI) {ℓ ℓ₄ u} (xs : List NodeId) (op : FlatOp) (m m′ ks : NodeId)
                 (p : Path Γ ℓ u t) (q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)) (fin : Bool) (now : Tick)
               : Stream (plainᵏ Γ κ) (emitᵗ t) × Sched (plainᵏ Γ κ) × EvalSt ei → Set where
      wrapped : ∀ {sI₁ stI₁ r} (A : After S ([] , proj₂ (thruWrap (flatOp op) m fin (sP , stP))) ([] , sI₁ , stI₁))
              → Walkedˣ xs op m m′ ks p q (Store.π (After.store A))
                  (EvalSt.nodes (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP , stP))))) (EvalSt.nodes stI₁)
              → ClearI m′ ks q sI₁ stI₁
              → (proj₁ (thruWrap (flatOp op) m fin (sP , stP)) ≡ true → Gone q stI₁)
              → foldPath⇓ now q [] (proj₁ (thruWrap (flatOp op) m fin (sP , stP))) sI₁ stI₁ r
              → Wrapped S xs op m m′ ks p q fin now r

    -- an impl node written keeps the rows live, read off the store
    keep-live : ∀ {sP stP sI stI} (S : St sP stP sI stI) (k : NodeId) {x y}
              → lookupNode k (EvalSt.nodes stI) ≡ just x → outerDoneᵇ (just y) ≡ outerDoneᵇ (just x)
              → LiveRows (record stI { nodes = setNode k y (EvalSt.nodes stI) })
    keep-live {stI = stI} S k l e = live-keep {st = stI} k l e (Inv.live-outer (Store.inv S))

    -- and keeps a path live unless spent, a flattener's state never spent
    flat-live-if : ∀ {lo s u} (q : Path (plainᵏ Γ κ) lo s u) (k : NodeId) {N x y}
                 → lookupNode k N ≡ just x → outerDoneᵇ (just y) ≡ outerDoneᵇ (just x) → spentAt (just x) ≡ false
                 → LiveIf q N → LiveIf q (setNode k y N)
    flat-live-if q k {N} {y = y} l e s =
      live-if-set q k y N (λ h → trans e (subst (λ z → outerDoneᵇ z ≡ false) l h)) (λ _ → trans (cong spentAt l) s)

    write-live : ∀ {sP stP sI stI} (S : St sP stP sI stI) (k : NodeId) {y}
               → (outerDoneᵇ (lookupNode k (EvalSt.nodes stI)) ≡ false → outerDoneᵇ (just y) ≡ false)
               → LiveRows (record stI { nodes = setNode k y (EvalSt.nodes stI) })
    write-live {stI = stI} S k w = live-write {st = stI} k w (Inv.live-outer (Store.inv S))

    -- A FLATTENER'S NODE PAIR WRITTEN ALIKE: the stores and the walk
    -- stay related with the two nodes moved to states that pair again
    flat-write : ∀ {sP stP sI stI} (S : St sP stP sI stI) {ℓ ℓ₄ u op m m′ ks xs}
                   {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {y y′}
               → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks xs
                 × PathRel {Γ = Γ} κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
               → FlatNodes {Γ = Γ} κ (Store.π S) u op y y′
               → LiveRows (record stI { nodes = setNode m′ y′ (EvalSt.nodes stI) })
               → Σ (After S ([] , sP , record stP { nodes = setNode m y (EvalSt.nodes stP) })
                            ([] , sI , record stI { nodes = setNode m′ y′ (EvalSt.nodes stI) })) λ A
                   → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (setNode m y (EvalSt.nodes stP)) (setNode m′ y′ (EvalSt.nodes stI)) u op m m′ ks xs
                     × PathRel {Γ = Γ} κ (Store.π (After.store A)) (setNode m y (EvalSt.nodes stP)) (setNode m′ y′ (EvalSt.nodes stI)) p q
    flat-write {sP} {stP} {sI} {stI} S {m = m} {m′} {y = y} {y′} (f@(pm , _ , _ , lP , lI , fn , _ , lk) , r) fn′ lv =
      node-write S W.moved lv
      , W.flatW f , W.pathW r
      where
      module W = Write κ (Store.π-keys S) (Store.π-vals S) {t = t} {NP = EvalSt.nodes stP} {NI = EvalSt.nodes stI} pm lP lI fn lk fn′

    -- AN IMPL CELL WRITTEN UNDER A SPENT TEST: the stores and the tails
    -- stay related, the plain side unmoved
    spent-write : ∀ {sP stP sI stI} (S : St sP stP sI stI) {ℓ ℓ′ s k k₁ k₂ w} {a c : Val (plainᵏ Γ κ) w}
                    {p : Path Γ ℓ s t} {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ s) (emitᵗ t)}
                → (k , k₁ ∷ k₂ ∷ []) ∈ Store.π S → lookupNode k (EvalSt.nodes stP) ≡ just (take-st 0)
                → lookupNode k₁ (EvalSt.nodes stI) ≡ just (cell-st a)
                → PathRel {Γ = Γ} κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                → Σ (After S ([] , sP , stP) ([] , sI , record stI { nodes = setNode k₁ (cell-st c) (EvalSt.nodes stI) })) λ A
                    → PathRel {Γ = Γ} κ (Store.π (After.store A)) (EvalSt.nodes stP) (setNode k₁ (cell-st c) (EvalSt.nodes stI)) p q
    spent-write {sP} {stP} {sI} {stI} S {k₁ = k₁} {c = c} e lP l₁ r =
      node-write S W.M.moved (live-quiet k₁ refl (Inv.live-outer (Store.inv S)))
      , W.M.pathW r
      where
      module W = CellWrite κ (Store.π-vals S) {t = t} {NP = EvalSt.nodes stP} {NI = EvalSt.nodes stI} {c = c} e lP l₁

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

    -- AN INNER'S SUBSCRIBE LEFT AGAIN: the lane's frames taken apart,
    -- the flattener as the walk left it, and the tails
    leave : ∀ {π NP NI lo lo′ ℓ ℓ₂ ℓ₃ ℓ₄ u} op {m m′ ks j j′ Θ₁ ρ₁ Θ₂ ρ₂} {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₂}
              {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)}
          → PathRel κ π {t} NP NI (from-inner (flatOp op) m j ↠[ h ] p)
              (from-inner (flatOp op) m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q)
          → Σ (List NodeId) (λ xs → Flattener {Γ = Γ} κ π {t} NP NI u op m m′ ks xs) × (j , j′ ∷ []) ∈ π × PathRel κ π NP NI p q
    leave (mergeᶠ _) (inner~ e (pm , x , x′ , lP , lI , fn , c , lk) ip pr) = (_ , pm , x , x′ , lP , lI , reop e fn , c , lk) , ip , pr
    leave switchᶠ    (inner~ e (pm , x , x′ , lP , lI , fn , c , lk) ip pr) = (_ , pm , x , x′ , lP , lI , reop e fn , c , lk) , ip , pr
    leave exhaustᶠ   (inner~ e (pm , x , x′ , lP , lI , fn , c , lk) ip pr) = (_ , pm , x , x′ , lP , lI , reop e fn , c , lk) , ip , pr

    -- the one row `π` keys by the flattener's node
    only : ∀ {π NP NI u op m m′ ks xs xs₀} → Unique (map proj₁ π) → (m , m′ ∷ ks ∷ xs₀) ∈ π
         → Flattener {Γ = Γ} κ π {t} NP NI u op m m′ ks xs → Flattener {Γ = Γ} κ π {t} NP NI u op m m′ ks xs₀
    only keys pm₀ f@(pm , _) with key-same keys pm pm₀
    ... | refl = f

    -- AN INNER'S WALK FROM STORES ALREADY MINTED: the walk of its
    -- elaboration, left again at the lane's frames
    inner-walk : ∀ {N} (wk : Walker ep ei N) {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ u op m m′ ks xs Θ₁ ρ₁ Θ₂ ρ₂}
                   {h₃ : n + ℓ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {o o′ j j′ rP rI}
               → Walkedˣ xs op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
               → (j , j′ ∷ []) ∈ Store.π S
               → LiveIf (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) (EvalSt.nodes stI)
               → ObsRel κ u o′ o
               → Sound (from-inner (flatOp op) m j ↠[ ≤-refl ] p) sP stP
               → Sound (from-inner (flatOp op) m′ j′ ↠[ ≤-refl ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
               → (dP : subscribeE⇓ o (from-inner (flatOp op) m j ↠[ ≤-refl ] p) now sP stP rP)
               → subscribeE⇓ o′ (from-inner (flatOp op) m′ j′ ↠[ ≤-refl ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now sI stI rI
               → sz-subscribeE dP < N
               → Σ (After S rP rI) λ A
                   → Walkedˣ xs op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
    inner-walk wk S {op = op} {m′ = m′} {ks = ks} {Θ₁ = Θ₁} {ρ₁} {Θ₂} {ρ₂} {h₃} {h₄} {q = q} {j′ = j′} {rP = rP} {rI} (f@(pm , _) , pr) ip lq (elab s w r) oP oI dP dI lt =
      proj₁ B , only {NP = EvalSt.nodes (proj₂ (proj₂ rP))} {NI = EvalSt.nodes (proj₂ (proj₂ rI))} (Store.π-keys (After.store (proj₁ B))) (After.grows (proj₁ B) pm) (proj₂ (proj₁ L)) , proj₂ (proj₂ L)
      where
      B = wk s w r S (inner~ refl f ip pr) oP oI (live-if-cons (from-inner (flatOp op) m′ j′) ≤-refl (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) refl lq) dP dI lt
      L = leave {NP = EvalSt.nodes (proj₂ (proj₂ rP))} {NI = EvalSt.nodes (proj₂ (proj₂ rI))} op (proj₁ (proj₂ B))

    -- A FLATTENER'S RESTAMP CELL WRITTEN: the stores and the tails stay
    -- related, the plain side unmoved
    restamp-write : ∀ {sP stP sI stI} (S : St sP stP sI stI) {u op m m′ ks xs} {c′ : Val (plainᵏ Γ κ) (FlatSᵗ u)} {ℓ ℓ′ s}
                      {p : Path Γ ℓ s t} {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ s) (emitᵗ t)}
                  → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks xs
                  → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                  → Σ (After S ([] , sP , stP) ([] , sI , record stI { nodes = setNode ks (cell-st {t = FlatSᵗ u} c′) (EvalSt.nodes stI) })) λ A
                      → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes stP) (setNode ks (cell-st {t = FlatSᵗ u} c′) (EvalSt.nodes stI)) u op m m′ ks xs
                      × PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) (setNode ks (cell-st {t = FlatSᵗ u} c′) (EvalSt.nodes stI)) p q
    restamp-write {sP} {stP} {sI} {stI} S {u = u} {ks = ks} {c′ = c′} f@(pm , _ , _ , _ , lI , fn , _ , lk) r =
      node-write S W.M.moved (live-quiet ks refl (Inv.live-outer (Store.inv S)))
      , W.flatW f , W.M.pathW r
      where
      module W = FlatCellWrite κ (Store.π-vals S) {t = t} {NP = EvalSt.nodes stP} {NI = EvalSt.nodes stI} pm lI fn lk c′

    -- A RESTAMP KEEPS AN EMIT'S EVENTS, so its values, and moves only a
    -- subscribe's stamp
    flat-rel : ∀ {u Θ₁ ρ₁ Θ₂ ρ₂} (ac : Val (plainᵏ Γ κ) (FlatSᵗ u)) e′ {ws}
             → EmitRel {Γ = Γ} κ u e′ ws
             → EmitRel {Γ = Γ} κ u (applyClo {s = FlatSᵗ u} (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) (applyClo (Θ₁ , flatStepᵛ , ρ₁) (ac , e′))) ws
    flat-rel _ (evs , i , s , inj₁ k) r = retag (λ q → q) r
    flat-rel _ (evs , i , s , inj₂ k) r = r

    flat-carries : ∀ {u Θ₁ ρ₁ Θ₂ ρ₂} (ac : Val (plainᵏ Γ κ) (FlatSᵗ u)) {es ws} → Carries es ws
                 → Carries (map (applyClo {s = FlatSᵗ u} (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂)) (proj₁ (scanVals (Θ₁ , flatStepᵛ , ρ₁) ac es))) ws
    flat-carries _ [] = []
    flat-carries {Θ₁ = Θ₁} {ρ₁} {Θ₂} {ρ₂} ac (quiet e′ r bs) =
      quiet _ (flat-rel {Θ₁ = Θ₁} {ρ₁} {Θ₂} {ρ₂} ac e′ r) (flat-carries {Θ₁ = Θ₁} {ρ₁} {Θ₂} {ρ₂} _ bs)
    flat-carries {Θ₁ = Θ₁} {ρ₁} {Θ₂} {ρ₂} ac (one e′ r bs) =
      one _ (flat-rel {Θ₁ = Θ₁} {ρ₁} {Θ₂} {ρ₂} ac e′ r) (flat-carries {Θ₁ = Θ₁} {ρ₁} {Θ₂} {ρ₂} _ bs)

    flat-del : ∀ {u Θ₁ ρ₁ Θ₂ ρ₂} {I} (ac : Val (plainᵏ Γ κ) (FlatSᵗ u)) {es : List (Val (plainᵏ Γ κ) (emitᵗ u))} → All (DelAt I) es
             → All (DelAt I) (map (applyClo {s = FlatSᵗ u} (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂)) (proj₁ (scanVals (Θ₁ , flatStepᵛ , ρ₁) ac es)))
    flat-del _ {es = []} [] = []
    flat-del _ {es = (_ , _ , _ , inj₁ _) ∷ _} (() ∷ _)
    flat-del {Θ₁ = Θ₁} {ρ₁} {Θ₂} {ρ₂} _ {es = (_ , _ , _ , inj₂ _) ∷ _} (d ∷ ds) = d ∷ flat-del {Θ₁ = Θ₁} {ρ₁} {Θ₂} {ρ₂} _ ds

    -- AN ECHO THROUGH THE RESTAMP: the scan's cell restamps it and
    -- keeps its payloads, and writes nothing but the cell, so the
    -- flattener and the tails stay related with the cell moved on; the
    -- group it hands on keeps its end, and every delivery's stamp
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
                     × (∀ {I} → All (DelAt I) es → All (DelAt I) (map (applyClo {s = FlatSᵗ u} (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂)) ys))
    restamp-echo {sP} {stP} {sI} {stI} S {u = u} {op} {m} {m′} {ks} {xs} {Θ₁} {ρ₁} {Θ₂} {ρ₂} {p = p} {q} {es} {ws} {fin}
                 f@(_ , _ , _ , _ , _ , _ , c , lk) r cs d = at (scan-at lk d)
      where
      G = applyClo {s = FlatSᵗ u} (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂)
      at : ∀ {o₁ ys fin₁ sI₁ stI₁}
         → (o₁ , ys , fin₁ , sI₁ , stI₁) ≡ ([] , proj₁ (scanVals (Θ₁ , flatStepᵛ , ρ₁) c es) , fin , sI
                                           , record stI { nodes = setNode ks (cell-st (proj₂ (scanVals (Θ₁ , flatStepᵛ , ρ₁) c es))) (EvalSt.nodes stI) })
         → Σ (After S ([] , sP , stP) (o₁ , sI₁ , stI₁)) λ A
             → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI₁) u op m m′ ks xs
             × PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes stI₁) p q
             × Carries (map G ys) ws × fin₁ ≡ fin × (∀ {I} → All (DelAt I) es → All (DelAt I) (map G ys))
      at refl =
        let (A , f′ , r′) = restamp-write S f r
        in A , f′ , r′ , flat-carries {Θ₁ = Θ₁} {ρ₁} {Θ₂} {ρ₂} c cs , refl , flat-del {Θ₁ = Θ₁} {ρ₁} {Θ₂} {ρ₂} c

    -- THE ECHO'S SCAN WRITES ONLY ITS CELL, which no row's skip reads,
    -- so a tail gone before it stays gone
    gone-echo : ∀ {π NP} {now ℓ₃ ℓ₄ u op m m′ ks xs Θ₁ ρ₁ Θ₂ ρ₂} {h₄ : ℓ₃ ≤ ℓ₄}
                  {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {es fin sI} {stI : EvalSt ei} {o₁ ys fin₁ sI₁ stI₁}
              → Flattener {Γ = Γ} κ π {t = t} NP (EvalSt.nodes stI) u op m m′ ks xs
              → stepFrame⇓ now (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks) (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₄ ] q)
                  es fin sI stI (o₁ , ys , fin₁ , sI₁ , stI₁)
              → Gone q stI → Gone q stI₁
    gone-echo {q = q} {stI = stI} (_ , _ , _ , _ , _ , _ , _ , lk) d g with scan-at lk d
    ... | refl = gone-nodes {q = q} {st = stI} g

    -- the restamp walks no outer and spends nothing, so its tail is as
    -- live as it
    restamp-unlive : ∀ {ℓ₂ ℓ₃ ℓ₄ u Θ₁ ρ₁ ks Θ₂ ρ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {N}
                   → LiveIf (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) N → LiveIf q N
    restamp-unlive {Θ₁ = Θ₁} {ρ₁} {ks} {Θ₂} {ρ₂} {h₃} {h₄} {q} l =
      live-if-drop (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂)) h₄ q refl refl (live-if-drop (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks) h₃ _ refl refl l)

    -- and its cell is no outer and no take, so a path live unless spent
    -- before the echo is after it
    live-echo-if : ∀ {π NP} {now ℓ₃ ℓ₄ u op m m′ ks xs Θ₁ ρ₁ Θ₂ ρ₂} {h₄ : ℓ₃ ≤ ℓ₄} {lo s} {Q : Path (plainᵏ Γ κ) lo s (emitᵗ t)}
                     {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {es fin sI} {stI : EvalSt ei} {o₁ ys fin₁ sI₁ stI₁}
                 → Flattener {Γ = Γ} κ π {t = t} NP (EvalSt.nodes stI) u op m m′ ks xs
                 → stepFrame⇓ now (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks) (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₄ ] q)
                     es fin sI stI (o₁ , ys , fin₁ , sI₁ , stI₁)
                 → LiveIf Q (EvalSt.nodes stI) → LiveIf Q (EvalSt.nodes stI₁)
    live-echo-if {Q = Q} {stI = stI} (_ , _ , _ , _ , _ , _ , _ , lk) d l with scan-at lk d
    ... | refl = live-if-set Q _ _ (EvalSt.nodes stI) (λ _ → refl) (λ _ → cong spentAt lk) l

    live-echo : ∀ {π NP} {now ℓ₂ ℓ₃ ℓ₄ u op m m′ ks xs Θ₁ ρ₁ Θ₂ ρ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                  {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {es fin sI} {stI : EvalSt ei} {o₁ ys fin₁ sI₁ stI₁}
              → Flattener {Γ = Γ} κ π {t = t} NP (EvalSt.nodes stI) u op m m′ ks xs
              → stepFrame⇓ now (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks) (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₄ ] q)
                  es fin sI stI (o₁ , ys , fin₁ , sI₁ , stI₁)
              → LiveFor es (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) (EvalSt.nodes stI)
              → LiveFor (map (applyClo {s = FlatSᵗ u} (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂)) ys) q (EvalSt.nodes stI₁)
    live-echo (_ , _ , _ , _ , _ , _ , _ , lk) d (inj₁ refl) with scan-at lk d
    ... | refl = inj₁ refl
    live-echo {π = π} {NP} {h₃ = h₃} {h₄} {q} {stI = stI} f d (inj₂ l) = inj₂ (live-echo-if {π = π} {NP} {h₄ = h₄} {Q = q} {q = q} {stI = stI} f d (restamp-unlive {h₃ = h₃} {h₄} {q} l))

    -- a flattener's node is never a spent take
    flat-unspent : ∀ {π NP NI u op m m′ ks xs} → Flattener {Γ = Γ} κ π {t = t} NP NI u op m m′ ks xs → spentAt (lookupNode m′ NI) ≡ false
    flat-unspent (_ , _ , _ , _ , lI , merge~ _ , _)  = cong spentAt lI
    flat-unspent (_ , _ , _ , _ , lI , switch~ _ , _) = cong spentAt lI
    flat-unspent (_ , _ , _ , _ , lI , exhaust~ , _)  = cong spentAt lI


    cur-none : ∀ {π cur cur′} → CurRel {Γ = Γ} κ π cur cur′ → is-nothing cur ≡ is-nothing cur′
    cur-none {cur = nothing} {nothing} _ = refl
    cur-none {cur = just _}  {just _}  _ = refl

    -- A FLATTENER'S PAIR WRAPPED ALIKE: the outer's end marks both
    -- nodes, and each reads its own state's end the same way
    wrap-at : ∀ {π u op x x′ m m′ sP sI} {stP : EvalSt ep} {stI : EvalSt ei}
            → FlatNodes {Γ = Γ} κ π u op x x′
            → lookupNode m (EvalSt.nodes stP) ≡ just x → lookupNode m′ (EvalSt.nodes stI) ≡ just x′
            → Σ Bool λ b → Σ (NodeState Γ) λ y → Σ (NodeState (plainᵏ Γ κ)) λ y′ → FlatNodes {Γ = Γ} κ π u op y y′
                × thruWrap (flatOp op) m true (sP , stP) ≡ (b , sP , record stP { nodes = setNode m y (EvalSt.nodes stP) })
                × thruWrap (flatOp op) m′ true (sI , stI) ≡ (b , sI , record stI { nodes = setNode m′ y′ (EvalSt.nodes stI) })
    wrap-at {m′ = m′} {sI = sI} {stI = stI} (merge~ {lim′ = lim′} {a} {q} {q′} ps) lP lI rewrite lP | lI =
      _ , _ , _ , merge~ ps , refl
      , cong (λ z → (a ≡ᵇ 0) ∧ z , sI , record stI { nodes = setNode m′ (mergeAll-st lim′ a q′ true) (EvalSt.nodes stI) }) (pw-null ps)
    wrap-at {m′ = m′} {sI = sI} {stI = stI} (switch~ {cur′ = cur′} c) lP lI rewrite lP | lI =
      _ , _ , _ , switch~ c , refl
      , cong (λ z → z , sI , record stI { nodes = setNode m′ (switch-st cur′ true) (EvalSt.nodes stI) }) (sym (cur-none c))
    wrap-at exhaust~ lP lI rewrite lP | lI = _ , _ , _ , exhaust~ , refl , refl

    wrapped′ : ∀ {sP stP sI stI} {S : St sP stP sI stI} {ℓ ℓ₄ u xs op m m′ ks} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)}
                 {fin now sI₁ stI₁ r T}
             → thruWrap (flatOp op) m fin (sP , stP) ≡ T
             → (A : After S ([] , proj₂ T) ([] , sI₁ , stI₁))
             → Walkedˣ xs op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ T))) (EvalSt.nodes stI₁)
             → ClearI m′ ks q sI₁ stI₁ → (proj₁ T ≡ true → Gone q stI₁) → foldPath⇓ now q [] (proj₁ T) sI₁ stI₁ r
             → Wrapped S xs op m m′ ks p q fin now r
    wrapped′ refl = wrapped

    -- AN EMPTY GROUP THROUGH THE RESTAMP: the cell written as it was,
    -- the tail handed nothing at the same end
    wrap-tail : ∀ {sP stP sI stI} (S : St sP stP sI stI) {sP′ stP′ sI′ stI′} (A₀ : After S ([] , sP′ , stP′) ([] , sI′ , stI′))
                  {now ℓ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₁ ρ₁ Θ₂ ρ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                  {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {b r xs}
              → Walkedˣ xs op m m′ ks p q (Store.π (After.store A₀)) (EvalSt.nodes stP′) (EvalSt.nodes stI′)
              → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI′ stI′
              → (b ≡ true → Gone q stI′)
              → foldPath⇓ now (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) [] b sI′ stI′ r
              → Σ (Sched (plainᵏ Γ κ)) λ sI₁ → Σ (EvalSt ei) λ stI₁ → Σ (After S ([] , sP′ , stP′) ([] , sI₁ , stI₁)) λ A
                  → Walkedˣ xs op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes stP′) (EvalSt.nodes stI₁)
                  × ClearI m′ ks q sI₁ stI₁ × (b ≡ true → Gone q stI₁) × foldPath⇓ now q [] b sI₁ stI₁ r
    wrap-tail S {sP′} {stP′} {sI′} {stI′} A₀ {now} {u = u} {op} {m} {m′} {ks} {Θ₁} {ρ₁} {Θ₂} {ρ₂} {h₃} {h₄} {p} {q} {b} {xs = xs}
              (f@(_ , _ , _ , _ , _ , _ , c , lk) , pr) cl gq (fold-step d₁ (fold-step step-map dq)) =
      go (scan-at lk d₁) dq (step-clear d₁ cl)
      where
      go : ∀ {o vs f′ s₁ st₁ out₂ s₂ st₂}
         → (o , vs , f′ , s₁ , st₁) ≡ ([] , [] , b , sI′ , record stI′ { nodes = setNode ks (cell-st {t = FlatSᵗ u} c) (EvalSt.nodes stI′) })
         → foldPath⇓ now q (map (applyClo {s = FlatSᵗ u} (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂)) vs) f′ s₁ st₁ (out₂ , s₂ , st₂)
         → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) s₁ st₁
         → Σ (Sched (plainᵏ Γ κ)) λ sI₁ → Σ (EvalSt ei) λ stI₁ → Σ (After S ([] , sP′ , stP′) ([] , sI₁ , stI₁)) λ A
             → Walkedˣ xs op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes stP′) (EvalSt.nodes stI₁)
             × ClearI m′ ks q sI₁ stI₁ × (b ≡ true → Gone q stI₁) × foldPath⇓ now q [] b sI₁ stI₁ (o ++ ([] ++ out₂) , s₂ , st₂)
      go refl dq cl₁ =
        let (A₁ , f₁ , r₁) = restamp-write (After.store A₀) {c′ = c} f pr
        in _ , _ , A₀ ⨾ A₁ , (f₁ , r₁) , tail-of cl₁ , (λ e → gone-nodes {q = q} {st = stI′} (gq e)) , dq

    -- NO ROW A DISPATCH WOULD WALK RUNS THROUGH `k`'S OUTER
    OuterSpent : NodeId → EvalSt ei → Set
    OuterSpent k st = ∀ {r} → r ∈ EvalSt.registry st → skipᵇ (regSource (proj₁ (proj₂ r))) (proj₁ r) st ≡ false
                    → All (λ j → (k ≡ᵇ j) ≡ false) (thruNodes (proj₂ (proj₂ (proj₂ r))))

    -- AN OUTER'S END KEEPS THE ROWS LIVE when none walks that outer:
    -- every other outer a row walks reads back as it did
    live-spent : ∀ {st : EvalSt ei} (k : NodeId) (y : NodeState (plainᵏ Γ κ))
               → OuterSpent k st → LiveRows st → LiveRows (record st { nodes = setNode k y (EvalSt.nodes st) })
    live-spent {st} k y sp (live L) = live λ r∈ sk → go (sp r∈ sk) (L r∈ sk)
      where
      go : ∀ {js} → All (λ j → (k ≡ᵇ j) ≡ false) js → All (λ j → outerDoneᵇ (lookupNode j (EvalSt.nodes st)) ≡ false) js
         → All (λ j → outerDoneᵇ (lookupNode j (setNode k y (EvalSt.nodes st))) ≡ false) js
      go []               []       = []
      go {j ∷ _} (a ∷ as) (h ∷ hs) = trans (cong outerDoneᵇ (set-above k j y (EvalSt.nodes st) a)) h ∷ go as hs

    -- AN END THAT LEFT A FLATTENER'S OUTER LEFT EVERY ROW OFF IT
    gone-thru : ∀ {st : EvalSt ei} {ℓ s k} {q : Path (plainᵏ Γ κ) ℓ s (emitᵗ t)}
              → headKey q ≡ 2 ∷ k ∷ [] → Gone q st → OuterSpent k st
    gone-thru {k = k} e (g , _) r∈ sk = go (λ ps → g r∈ sk (subst (λ x → Passes x _) (sym e) ps))
      where
      go : ∀ {lo s′} {p : Path (plainᵏ Γ κ) lo s′ (emitᵗ t)} → ¬ Passes (2 ∷ k ∷ []) p → All (λ j → (k ≡ᵇ j) ≡ false) (thruNodes p)
      go {p = root}                     _  = []
      go {p = share-sink _ _}           _  = []
      go {p = thru-outer _ j ↠[ _ ] p} np with k ≡ᵇ j in kj
      ... | true  = ⊥-elim (np (inj₁ (cong (λ x → 2 ∷ x ∷ []) (sym (≡ᵇ→≡ k j kj)))))
      ... | false = kj ∷ go (λ ps → np (inj₂ ps))
      go {p = map-f _ ↠[ _ ] p}         np = go (λ ps → np (inj₂ ps))
      go {p = scan-f _ _ ↠[ _ ] p}      np = go (λ ps → np (inj₂ ps))
      go {p = take-f _ _ ↠[ _ ] p}      np = go (λ ps → np (inj₂ ps))
      go {p = batchSync-f _ ↠[ _ ] p}   np = go (λ ps → np (inj₂ ps))
      go {p = from-inner _ _ _ ↠[ _ ] p} np = go (λ ps → np (inj₂ ps))

    -- THE OUTER'S END ON BOTH SIDES: a flattener completes once its
    -- outer has and no lane is open or queued, read off related nodes,
    -- so the two ends agree; the restamp passes the empty group on
    outer-wrap : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₁ ρ₁ Θ₂ ρ₂}
                   {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {fin r xs}
               → Walkedˣ xs op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
               → (fin ≡ true → Gone (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) stI)
               → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) (proj₁ (proj₂ (thruWrap (flatOp op) m′ fin (sI , stI))))
                   (proj₂ (proj₂ (thruWrap (flatOp op) m′ fin (sI , stI))))
               → foldPath⇓ now (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) []
                   (proj₁ (thruWrap (flatOp op) m′ fin (sI , stI)))
                   (proj₁ (proj₂ (thruWrap (flatOp op) m′ fin (sI , stI))))
                   (proj₂ (proj₂ (thruWrap (flatOp op) m′ fin (sI , stI)))) r
               → Wrapped S xs op m m′ ks p q fin now r
    outer-wrap S {fin = false} W _ cl dR =
      let (_ , _ , A , W′ , c , g , d) = wrap-tail S (after S (λ x → x) (λ x → x) [] (λ x → x)) W cl (λ ()) dR in wrapped A W′ c g d
    outer-wrap {sP} {stP} {sI} {stI} S {now} {op = op} {m′ = m′} {ks} {Θ₁} {ρ₁} {Θ₂} {ρ₂} {h₂} {h₃} {h₄} {q = q} {fin = true} {r}
               W@((_ , _ , _ , lP , lI , fn , _) , _) gw cl dR =
      let (b , y , y′ , fn′ , eP , eI) = wrap-at {sP = sP} {sI} {stP} {stI} fn lP lI
          (A₀ , f₀ , r₀) = flat-write S W fn′ (live-spent m′ y′ (gone-thru {st = stI} {q = thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q} refl (gw refl)) (Inv.live-outer (Store.inv S)))
          (_ , _ , A , W′ , c , g , d) = wrap-tail S A₀ (f₀ , r₀)
            (subst (λ T → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) (proj₁ (proj₂ T)) (proj₂ (proj₂ T))) eI cl)
            (λ e → gone-nodes {q = q} {st = stI} (gone-restamp S {Θ₁ = Θ₁} {ρ₁} {ks} {Θ₂} {ρ₂} {h₃} {h₄} {q} (gone-wrap S {o = flatOp op} {k = m′} {h = h₂} {q = Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q} (gw refl) (trans (cong proj₁ eI) e))))
            (subst (λ T → foldPath⇓ now (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) [] (proj₁ T) (proj₁ (proj₂ T)) (proj₂ (proj₂ T)) r) eI dR)
      in wrapped′ eP A W′ c g d

    -- AN EXPLODE'S MERGE TOLD ITS OUTER HAS ENDED: idle, so it reads the
    -- end as it came and marks itself done
    merge-wrap : ∀ {s} {st : EvalSt ei} {u mX od}
               → lookupNode mX (EvalSt.nodes st) ≡ just (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] od)
               → thruWrap mergeAllᵒ mX true (s , st)
                 ≡ (true , s , record st { nodes = setNode mX (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] true) (EvalSt.nodes st) })
    merge-wrap l rewrite l = refl

    -- and the stores and the walk stay related across the mark
    merge-done : ∀ {sP stP sI stI} (S : St sP stP sI stI) {ℓ ℓ′ u op m m′ ks mX od}
                   {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)}
               → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
               → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
               → lookupNode mX (EvalSt.nodes stI) ≡ just (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] od)
               → LiveRows (record stI { nodes = setNode mX (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] true) (EvalSt.nodes stI) })
               → Σ (After S ([] , sP , stP)
                      ([] , sI , record stI { nodes = setNode mX (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] true) (EvalSt.nodes stI) })) λ A
                   → Walkedˣ (mX ∷ []) op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes stP)
                       (setNode mX (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] true) (EvalSt.nodes stI))
                     × MergeAt {Γ = Γ} κ (setNode mX (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] true) (EvalSt.nodes stI)) u mX
    merge-done {sP} {stP} {sI} {stI} S {u = u} {mX = mX} f@(pm , _) r lX lv =
      node-write S W.M.moved lv
      , (W.flatW f , W.M.pathW r) , W.mergeX
      where
      module W = MergeDone κ (Store.π-vals S) {t = t} {NP = EvalSt.nodes stP} {NI = EvalSt.nodes stI} pm lX

    -- the same, at a walk
    flat-echo : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ u op m m′ ks Θ₁ ρ₁ Θ₂ ρ₂}
                  {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {ns xs ws o₁ fin₁ sI₁ stI₁}
                  {ys : List (Val (plainᵏ Γ κ) (FlatSᵗ u))}
              → Walkedˣ ns op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
              → Carries xs ws
              → stepFrame⇓ now (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks) (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₄ ] q)
                  xs false sI stI (o₁ , ys , fin₁ , sI₁ , stI₁)
              → Restamped S ns op m m′ ks p q ws (map (applyClo {s = FlatSᵗ u} (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂)) ys) fin₁ o₁ sI₁ stI₁
    flat-echo S (f , r) c d = let (A , f′ , r′ , c′ , e , _) = restamp-echo S f r c d in restamped A (f′ , r′) c′ e


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
    flat-mint : ∀ {N} (wk : Walker ep ei N) {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ u op m m′ ks xs Θ₁ ρ₁ Θ₂ ρ₂ y y′}
                  {h₃ : n + ℓ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {o o′ j j′ rP rI}
              → Walkedˣ xs op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
              → Clear m p sP stP → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
              → FlatNodes {Γ = Γ} κ (Minted S) u op y y′
              → LiveRows (record stI { nodes = setNode m′ y′ (EvalSt.nodes stI) })
              → LiveIf (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) (setNode m′ y′ (EvalSt.nodes stI))
              → ObsRel κ u o′ o
              → (dP : subscribeInner⇓ (flatOp op) m p now o sP (record stP { nodes = setNode m y (EvalSt.nodes stP) }) (j , rP))
              → subscribeInner⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now o′ sI
                  (record stI { nodes = setNode m′ y′ (EvalSt.nodes stI) }) (j′ , rI)
              → sz-subscribeInner dP < N
              → Σ (After S rP rI) λ A
                  → Walkedˣ xs op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
    flat-mint wk {sP} {stP} {sI} {stI} S {op = op} {m = m} {m′ = m′} {ks = ks} {xs = xs} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂}
              {h₃ = h₃} {h₄ = h₄} {p = p} {q = q} (f , pr) cP cI fn lv lq ob (inner refl dP) (inner refl dI) lt =
      unmint (proj₁ Wr ⨾ proj₁ B) , proj₂ B
      where
      W₁ : Walkedˣ xs op m m′ ks p q (Store.π (mint-pair S)) (EvalSt.nodes stP) (EvalSt.nodes stI)
      W₁ = flatG {Γ = Γ} κ {π = Store.π S} {π′ = Store.π (mint-pair S)} there {t = t} {NP = EvalSt.nodes stP} {NI = EvalSt.nodes stI} f
         , pathG {Γ = Γ} κ there {t = t} {NP = EvalSt.nodes stP} {NI = EvalSt.nodes stI} (proj₂ (proj₂ (fresh-off {Γ = Γ} {κ = κ} {π = Store.π S} {j = nodeCt sP} (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) (fresh-path (proj₂ cI))))) pr
      Wr = flat-write (mint-pair S) W₁ fn lv
      B = inner-walk wk (After.store (proj₁ Wr)) (proj₂ Wr) (After.grows (proj₁ Wr) (here refl)) lq ob
            (sub-ot (λ r∈ → r∈) ≤-refl (fresh-inner (flatOp op) m p sP (proj₂ cP) (proj₁ cP)))
            (sub-ot (λ r∈ → r∈) ≤-refl (fresh-inner (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI (proj₂ cI) (proj₁ cI)))
            dP dI (sz-1 lt)

    -- a switch's: the node names the inner it subscribes
    switch-subscribe : ∀ {N} (wk : Walker ep ei N) {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ u m m′ ks Θ₁ ρ₁ Θ₂ ρ₂ cur cur′ od od′}
                         {h₃ : n + ℓ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {o o′ rP rI}
                     → Walked switchᶠ m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                     → lookupNode m (EvalSt.nodes stP) ≡ just (switch-st cur od)
                     → lookupNode m′ (EvalSt.nodes stI) ≡ just (switch-st cur′ od′)
                     → Clear m p sP stP → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
                     → LiveIf (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) (EvalSt.nodes stI)
                     → ObsRel κ u o′ o
                     → (dP : subscribeInner⇓ switchᵒ m p now o sP
                         (record stP { nodes = setNode m (switch-st (just (nodeCt sP)) od) (EvalSt.nodes stP) }) (nodeCt sP , rP))
                     → subscribeInner⇓ switchᵒ m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now o′ sI
                         (record stI { nodes = setNode m′ (switch-st (just (nodeCt sI)) od′) (EvalSt.nodes stI) }) (nodeCt sI , rI)
                     → sz-subscribeInner dP < N
                     → Σ (After S rP rI) λ A
                         → Walked switchᶠ m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
    switch-subscribe wk {sP} {sI = sI} S {m′ = m′} {od = od} W@((_ , _ , _ , lP , lI , fn , _) , _) eP eI cP cI lq ob dP dI lt =
      flat-mint wk S W cP cI
        (subst (λ d → FlatNodes {Γ = Γ} κ (Minted S) _ switchᶠ (switch-st (just (nodeCt sP)) od) (switch-st (just (nodeCt sI)) d))
               (same-od fn (trans (sym lP) eP) (trans (sym lI) eI)) (switch~ (here refl)))
        (keep-live S m′ eI refl) (flat-live-if _ m′ eI refl refl lq) ob dP dI lt

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
    consume-switch : ∀ {N} (wk : Walker ep ei N) {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ u m m′ ks Θ₁ ρ₁ Θ₂ ρ₂}
                       {h₃ : n + ℓ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {o o′ rP rI}
                   → Walked switchᶠ m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                   → ObsRel κ u o′ o
                   → Clear m p sP stP → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
                   → LiveIf (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) (EvalSt.nodes stI)
                   → (dP : thruConsume⇓ switchᵒ m p now o sP stP rP)
                   → thruConsume⇓ switchᵒ m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now o′ sI stI rI
                   → sz-thruConsume dP < N
                   → Σ (After S rP rI) λ A
                       → Walked switchᶠ m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
    consume-switch wk {sP} {stP} {sI} {stI} S {m = m} {m′} W ob cP cI lq (consume-switch-sub {cur = cur} eP kP refl dP) (consume-switch-sub {cur = cur′} eI kI refl dI) lt =
      let K = switch-kill S W eP eI kP kI
          B = switch-subscribe wk (After.store (proj₁ K)) (proj₂ K) (cut-kept m cur sP stP kP eP) (cut-kept m′ cur′ sI stI kI eI) (kill-clear cur sP stP kP cP) (kill-clear cur′ sI stI kI cI)
                (subst (LiveIf _) (cut-nodes cur′ sI stI kI) lq) ob dP dI (sz-1 lt)
      in proj₁ K ⨾ proj₁ B , proj₂ B
      where
      cut-kept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} k (c : Maybe NodeId) (s : Sched Γ) (st : EvalSt e) {s₁ st₁ x}
               → switchKill c s st ≡ (s₁ , st₁) → lookupNode k (EvalSt.nodes st) ≡ x → lookupNode k (EvalSt.nodes st₁) ≡ x
      cut-kept k c s st refl e = trans (cong (lookupNode k) (switchKill-nodes c s st)) e
      cut-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (c : Maybe NodeId) (s : Sched Γ) (st : EvalSt e) {s₁ st₁}
                → switchKill c s st ≡ (s₁ , st₁) → EvalSt.nodes st ≡ EvalSt.nodes st₁
      cut-nodes c s st refl = sym (switchKill-nodes c s st)
      kill-clear : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo s′} {k} {π : Path Γ lo s′ t} (c : Maybe NodeId) (s : Sched Γ) (st : EvalSt e) {s₁ st₁}
                 → switchKill c s st ≡ (s₁ , st₁) → Clear k π s st → Clear k π s₁ st₁
      kill-clear c s st refl (on , so) =
        sub-on (kill-sub c s st) (≤-reflexive (sym (switchKill-ct c s st))) on , sub-ot (kill-sub c s st) (≤-reflexive (sym (switchKill-ct c s st))) so
    consume-switch _ S W ob _ _ _ (consume-switch-nil _) (consume-switch-nil _) _ = after S (λ x → x) (λ x → x) [] (λ x → x) , W
    consume-switch _ S {u = u} ((_ , _ , _ , _ , lI , switch~ _ , _) , _) ob _ _ _ (consume-switch-sub _ _ _ _) (consume-switch-nil n) _ =
      ⊥-elim (unusable switchᵒ (emitᵗ u) lI n refl)
    consume-switch _ S {u = u} ((_ , _ , _ , lP , _ , switch~ _ , _) , _) ob _ _ _ (consume-switch-nil n) _ _ =
      ⊥-elim (unusable switchᵒ u lP n refl)

    -- AN OUTER'S INNER HANDED THE FLATTENER ON BOTH SIDES, its lane on
    -- the impl's: the policy reads related nodes and decides alike.  A
    -- lane taken is a related write and then the inner's subscribe; an
    -- element queued is the write alone; a node neither can use is no
    -- step at all
    consume-pair : ∀ {N} (wk : Walker ep ei N) {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ u op m m′ ks Θ₁ ρ₁ Θ₂ ρ₂}
                     {h₃ : n + ℓ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {o o′ rP rI}
                 → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                 → ObsRel κ u o′ o
                 → Clear m p sP stP → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
                 → LiveIf (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) (EvalSt.nodes stI)
                 → (dP : thruConsume⇓ (flatOp op) m p now o sP stP rP)
                 → thruConsume⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now o′ sI stI rI
                 → sz-thruConsume dP < N
                 → Σ (After S rP rI) λ A
                     → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
    consume-pair wk S {op = switchᶠ} W ob cP cI lq dP dI lt = consume-switch wk S W ob cP cI lq dP dI lt
    consume-pair wk S {op = mergeᶠ _} W@((_ , _ , _ , lP , lI , fn , _) , _) ob cP cI lq (consume-all-sub eP _ dP) (consume-all-sub eI _ dI) lt =
      flat-mint wk S W cP cI (lane-nodes (nodes-grow {Γ = Γ} κ there fn) (trans (sym lP) eP) (trans (sym lI) eI))
        (keep-live S _ eI refl) (flat-live-if _ _ eI refl refl lq) ob dP dI (sz-1 lt)
    consume-pair _ S {op = mergeᶠ _} W@((_ , _ , _ , lP , lI , fn , _) , _) ob _ _ _ (consume-all-enqueue eP _) (consume-all-enqueue eI _) _ =
      flat-write S W (queue-nodes fn (trans (sym lP) eP) (trans (sym lI) eI) ob) (keep-live S _ eI refl)
    consume-pair _ S {op = mergeᶠ _} W ob _ _ _ (consume-all-nil _) (consume-all-nil _) _ = after S (λ x → x) (λ x → x) [] (λ x → x) , W
    consume-pair _ S {op = mergeᶠ _} ((_ , _ , _ , lP , lI , fn , _) , _) ob _ _ _ (consume-all-sub eP hP _) (consume-all-enqueue eI hI) _ =
      ⊥-elim (t≢f (room-agree fn (trans (sym lP) eP) (trans (sym lI) eI) hP hI))
    consume-pair _ S {op = mergeᶠ _} ((_ , _ , _ , lP , lI , fn , _) , _) ob _ _ _ (consume-all-enqueue eP hP) (consume-all-sub eI hI _) _ =
      ⊥-elim (t≢f (sym (room-agree fn (trans (sym lP) eP) (trans (sym lI) eI) hP hI)))
    consume-pair _ S {u = u} {op = mergeᶠ _} ((_ , _ , _ , _ , lI , fn , _) , _) ob _ _ _ _ (consume-all-nil n) _ = ⊥-elim (unusable mergeAllᵒ (emitᵗ u) lI n (proj₂ (merge-usable fn)))
    consume-pair _ S {u = u} {op = mergeᶠ _} ((_ , _ , _ , lP , _ , fn , _) , _) ob _ _ _ (consume-all-nil n) _ _ = ⊥-elim (unusable mergeAllᵒ u lP n (proj₁ (merge-usable fn)))
    consume-pair wk S {op = exhaustᶠ} W@((_ , _ , _ , lP , lI , fn , _) , _) ob cP cI lq (consume-exhaust-sub eP dP) (consume-exhaust-sub eI dI) lt =
      flat-mint wk S W cP cI (idle-nodes (nodes-grow {Γ = Γ} κ there fn) (trans (sym lP) eP) (trans (sym lI) eI))
        (keep-live S _ eI refl) (flat-live-if _ _ eI refl refl lq) ob dP dI (sz-1 lt)
    consume-pair _ S {op = exhaustᶠ} W ob _ _ _ (consume-exhaust-nil _) (consume-exhaust-nil _) _ = after S (λ x → x) (λ x → x) [] (λ x → x) , W
    consume-pair _ S {u = u} {op = exhaustᶠ} ((_ , _ , _ , lP , lI , fn , _) , _) ob _ _ _ (consume-exhaust-sub eP _) (consume-exhaust-nil n) _ =
      ⊥-elim (unusable exhaustᵒ (emitᵗ u) lI n (idle-plain fn (trans (sym lP) eP)))
    consume-pair _ S {u = u} {op = exhaustᶠ} ((_ , _ , _ , lP , lI , fn , _) , _) ob _ _ _ (consume-exhaust-nil n) (consume-exhaust-sub eI _) _ =
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

    postulate
      -- AN UNENDED FOLD ENDS NO STANDING OUTER UNLESS IT SPENDS ITS PATH:
      -- an end reaches a flattener's outer only down a path a take on it
      -- sent, and everything else the fold sets running is minted fresh
      fold-spares : ∀ {now lo ℓ s o k x} {h : lo ≤ ℓ} {q : Path (plainᵏ Γ κ) ℓ s (emitᵗ t)} {es sched} {st : EvalSt ei} {r}
                  → foldPath⇓ now q es false sched st r
                  → lookupNode k (EvalSt.nodes st) ≡ just x
                  → LiveIf (thru-outer {u = s} o k ↠[ h ] q) (EvalSt.nodes st)
                  → LiveIf (thru-outer o k ↠[ h ] q) (EvalSt.nodes (proj₂ (proj₂ r)))

      -- AN INNER SUBSCRIBED UNDER A FLATTENER ENDS NO STANDING OUTER
      -- UNLESS IT SPENDS ITS PATH: its end finds the flattener's outer
      -- live, so it frees a lane and ends nothing
      inner-spares : ∀ {now lo ℓ s op k o′} {h : lo ≤ ℓ} {q : Path (plainᵏ Γ κ) ℓ s (emitᵗ t)} {o sched} {st : EvalSt ei} {r}
                   → subscribeInner⇓ op k q now o sched st r
                   → LiveIf (thru-outer {u = s} o′ k ↠[ h ] q) (EvalSt.nodes st)
                   → LiveIf (thru-outer o′ k ↠[ h ] q) (EvalSt.nodes (proj₂ (proj₂ (proj₂ r))))

    -- an echo's restamp, then its tail, keep the path live unless spent
    echo-on : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now ℓ ℓ₁ ℓ₃ ℓ₄ u op m m′ ks Θ₁ ρ₁ Θ₂ ρ₂}
                {h₂ : ℓ₁ ≤ n + ℓ} {h₃ : n + ℓ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)}
                {ns ws es fin oI sI₁ stI₁ r}
            → Restamped S ns op m m′ ks p q ws es fin oI sI₁ stI₁ → foldPath⇓ now q es fin sI₁ stI₁ r
            → LiveIf (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) (EvalSt.nodes stI₁)
            → LiveIf (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) (EvalSt.nodes (proj₂ (proj₂ r)))
    echo-on {op = op} {h₂ = h₂} {h₃ = h₃} {h₄ = h₄} (restamped A w _ refl) dq l =
      live-if (LiveIf.run (fold-spares {o = flatOp op} {h = ≤-trans h₂ (≤-trans h₃ h₄)} dq
        (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₁ w)))))) (live-if (LiveIf.run l))))

    -- a consume takes its lane, ending nothing, then subscribes the inner
    consume-spares : ∀ {now lo ℓ s op k o′} {h : lo ≤ ℓ} {q : Path (plainᵏ Γ κ) ℓ s (emitᵗ t)} {o sched} {st : EvalSt ei} {r}
                   → thruConsume⇓ op k q now o sched st r
                   → LiveIf (thru-outer {u = s} o′ k ↠[ h ] q) (EvalSt.nodes st)
                   → LiveIf (thru-outer o′ k ↠[ h ] q) (EvalSt.nodes (proj₂ (proj₂ r)))
    consume-spares {k = k} {st = st} (consume-all-sub e _ d) l =
      inner-spares d (live-if-set _ k _ (EvalSt.nodes st) (λ z → trans (sym (cong outerDoneᵇ e)) z) (λ _ → cong spentAt e) l)
    consume-spares {k = k} {st = st} (consume-all-enqueue e _) l =
      live-if-set _ k _ (EvalSt.nodes st) (λ z → trans (sym (cong outerDoneᵇ e)) z) (λ _ → cong spentAt e) l
    consume-spares (consume-all-nil _) l = l
    consume-spares {k = k} {st = st} (consume-switch-sub {sched₀ = s₀} {cur = cur} e refl _ d) l =
      inner-spares d (live-if-set _ k _ _ (λ z → trans (sym (cong outerDoneᵇ e′)) z) (λ _ → cong spentAt e′)
        (subst (LiveIf _) (sym (switchKill-nodes cur s₀ st)) l))
      where e′ = trans (cong (lookupNode k) (switchKill-nodes cur s₀ st)) e
    consume-spares (consume-switch-nil _) l = l
    consume-spares {k = k} {st = st} (consume-exhaust-sub e d) l =
      inner-spares d (live-if-set _ k _ (EvalSt.nodes st) (λ z → trans (sym (cong outerDoneᵇ e)) z) (λ _ → cong spentAt e) l)
    consume-spares (consume-exhaust-nil _) l = l

    -- a run that carries something finds its path live unless spent
    live-cons : ∀ {A : Set} {e : A} {es lo s u} {q : Path (plainᵏ Γ κ) lo s u} {N} → LiveFor (e ∷ es) q N → LiveIf q N
    live-cons (inj₁ ())
    live-cons (inj₂ l) = l

    -- A VALUELESS GROUP KEEPS THE PASS WITH THE PLAIN SIDE STILL, and
    -- the two paths related where the impl's fold leaves them
    Quiet : ∀ {lo lo′ s} → Path Γ lo s t → Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t) → Set
    Quiet p q =
      ∀ {now es fin sP stP sI stI rI} (S : St sP stP sI stI)
      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q → Carries es [] → fin ≡ false
      → Sound p sP stP → Sound q sI stI
      → LiveFor es q (EvalSt.nodes stI)
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
           → LiveFor es q (EvalSt.nodes stI₁)
           → (∀ {rI} → foldPath⇓ now q es fin sI₁ stI₁ rI → (B : After (After.store A) ([] , sP , stP) rI)
              → PathRel κ (Store.π (After.store B)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
              → G (Store.π (After.store B)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI))))
           → QArm S now p G q es fin oI sI₁ stI₁

    -- A RESTAMPED EMIT CARRIES WHAT IT CARRIED: the restamp rebuilds the
    -- emit over its own events, so the values it holds are the ones
    restamp-rel : ∀ {i : Fin n} {Θ₀ ρ₀} {X : Tm (plainᵏ Γ κ) [] [] (emitᵗ (lookup Γ i) ∷ Θ₀) uniqᵗ} e′ {ws}
                → EmitRel {Γ = Γ} κ (lookup Γ i) e′ ws
                → EmitRel {Γ = Γ} κ (lookup Γ i) (applyClo (Θ₀ , restampᵛ X subscribeᵛ (varᵗ (here refl)) , ρ₀) e′) ws
    restamp-rel (evs , i , s , inj₁ k) r = retag (λ q → q) r
    restamp-rel (evs , i , s , inj₂ k) r = r

    restamp-carries : ∀ {i : Fin n} {Θ₀ ρ₀} {X : Tm (plainᵏ Γ κ) [] [] (emitᵗ (lookup Γ i) ∷ Θ₀) uniqᵗ} {es vs}
                    → Carries {s = lookup Γ i} es vs
                    → Carries (map (applyClo (Θ₀ , restampᵛ X subscribeᵛ (varᵗ (here refl)) , ρ₀)) es) vs
    restamp-carries []             = []
    restamp-carries {i = i} {X = X} (quiet e′ r bs) = quiet _ (restamp-rel {i = i} {X = X} e′ r) (restamp-carries {i = i} {X = X} bs)
    restamp-carries {i = i} {X = X} (one e′ r bs)   = one _ (restamp-rel {i = i} {X = X} e′ r) (restamp-carries {i = i} {X = X} bs)

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

    -- one emit of a valueless group, and the rest
    cu-head : ∀ {u u′} (F : u′ ≡ emitᵗ u) {e es} → CarriesU F (e ∷ es) [] → CarriesU F (e ∷ []) []
    cu-head refl (quiet _ b _) = quiet _ b []

    cu-tail : ∀ {u u′} (F : u′ ≡ emitᵗ u) {e es} → CarriesU F (e ∷ es) [] → CarriesU F es []
    cu-tail refl (quiet _ _ c) = c

    -- a merge a run left alone stays where it was
    merge-moved : ∀ {N N′ u k} → Unmoved k N′ N → MergeAt {Γ = Γ} κ N u k → MergeAt {Γ = Γ} κ N′ u k
    merge-moved (unmoved e) (od , l) = od , trans e l

    -- A NODE THE IMPL'S COUNTER PASSES ALONE: the pairs stay as they
    -- were, every one still below both counters
    mint-impl : ∀ {sP stP sI stI} (S : St sP stP sI stI)
              → St sP stP (record sI { mint = setAt nodeᵏ (suc (nodeCt sI)) (Sched.mint sI) }) stI
    mint-impl {sI = sI} S = record
      { π = π ; π-keys = π-keys ; π-vals = π-vals
      ; pairs-below = proj₁ pairs-below , mapᵃ (mapᵃ m<n⇒m<1+n) (proj₂ pairs-below)
      ; sources = sources ; numbers = numbers ; distinct = distinct ; sync = sync
      ; rows = rows ; dlv-alike = dlv-alike ; dying-alike = dying-alike
      ; latches = latches ; dying-done = dying-done ; bounded = bounded ; swept = swept ; uncut = uncut
      ; named = proj₁ named , named-node (proj₂ named) ; rids = rids ; fresh-ids = fresh-ids ; above = above
      ; census = census ; owned = owned
      ; ruleP = ruleP ; ruleI = sub-rule (λ r∈ → r∈) (n≤1+n (nodeCt sI)) ruleI
      ; scripts = scripts ; inv = inv
      }
      where open Store S

    unmintI : ∀ {sP stP sI stI} {S : St sP stP sI stI} {rP rI} → After (mint-impl S) rP rI → After S rP rI
    unmintI A =
      after (After.store A) (After.keeps A)
            (λ ar → After.persists A (record { boundP = Arr.boundP ar ; boundI = Arr.boundI ar ; rows = Arr.rows ar ; lists = Arr.lists ar }))
            (After.values A) (After.grows A)

    -- an impl finish at an index known otherwise
    finish-at : ∀ {lo s op m j} {q : Path (plainᵏ Γ κ) lo s (emitᵗ t)} {now vals sched} {st : EvalSt ei} {mx my r}
              → mx ≡ my → innerFinish⇓ op m j q now vals sched st mx r → innerFinish⇓ op m j q now vals sched st my r
    finish-at refl F = F

    postulate
      -- AN EXPLODE'S QUIET ELEMENT WALKED WHILE ITS MERGE COUNTS IT: the
      -- flattener's fold of the one element runs over the merge's node
      -- holding the inner in flight, and with that node set back to what
      -- it held, the stores and the walk are related where the fold
      -- leaves them, the plain side still
      --
      -- DEAD ROUTE: walking it where the merge counts the inner needs a
      --   `Store` there, and every row through the outer reads `MergeAt`
      --   at count zero; the store holds only between steps.
      -- DEAD ROUTE: re-basing the fold off the written node by a frame
      --   lemma, then walking it by `quiet-elem-step`, does not descend:
      --   the walk recurses on the impl's derivation, and one a lemma
      --   hands back is no subterm of the explode's.
      inner-over : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₁ ρ₁ Θ₂ ρ₂ x₀ y z}
                     {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)} {r}
                 → Sound p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                 → Walkedˣ (mX ∷ []) op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                 → lookupNode mX (EvalSt.nodes stI) ≡ just x₀
                 → LiveIf (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) (EvalSt.nodes stI)
                 → QuietElem {u} z
                 → foldPath⇓ now (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) (z ∷ []) false sI (record stI { nodes = setNode mX y (EvalSt.nodes stI) }) r
                 → Σ (After S ([] , sP , stP)
                        (proj₁ r , proj₁ (proj₂ r) , record (proj₂ (proj₂ r)) { nodes = setNode mX x₀ (EvalSt.nodes (proj₂ (proj₂ r))) })) λ A
                     → Walkedˣ (mX ∷ []) op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes stP)
                         (setNode mX x₀ (EvalSt.nodes (proj₂ (proj₂ r))))

      -- AN OUTER'S EMIT CARRYING NOTHING, EXPLODED AND SUBSCRIBED AT A
      -- MERGE WHOSE OUTER HAS ENDED: as `explode-quiet-sub`, at a merge
      -- marked done, which the pass's liveness does not rule out on a
      -- spent path.  The inner's finish ends the merge again and that end
      -- reaches the flattener's wrap, which `explode-one-ended` records open
      explode-quiet-ended : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                            {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                            {inst out sched₁ st₁}
                        → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                        → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                        → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                        → LiveIf (thru-outer mergeAllᵒ mX ↠[ h₃ ] (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)) (EvalSt.nodes stI)
                        → lookupNode mX (EvalSt.nodes stI) ≡ just (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] true)
                        → ∀ e′ → Bare {echoᵗ u} e′
                        → subscribeInner⇓ mergeAllᵒ mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) now
                            (applyClo {s = emitᵗ (echoᵗ u)} {t = obs (echoᵗ (emitᵗ u))} (Θ₀ , explodeᵛ , ρ₀) e′) sI
                            (record stI { nodes = setNode mX (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 1 [] true) (EvalSt.nodes stI) })
                            (inst , out , sched₁ , st₁)
                        → Σ (After S ([] , sP , stP) (out , sched₁ , st₁)) λ A
                            → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes stP) (EvalSt.nodes st₁) u op m m′ ks (mX ∷ [])
                              × PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes st₁) p q
                              × MergeAt {Γ = Γ} κ (EvalSt.nodes st₁) u mX
                              × (∀ {I} → DelAt {echoᵗ u} I e′ → Out I out)

    -- A DELIVERED EMIT CARRIES WHAT IT CARRIED: the hop's restamp
    -- retags a subscribe as a delivery over its own events
    delivery-rel : ∀ {u Θx ρ₀} e′ {ws}
                 → EmitRel {Γ = Γ} κ u e′ ws
                 → EmitRel {Γ = Γ} κ u (applyClo (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) e′) ws
    delivery-rel (evs , i , s , inj₁ k) r = retag (λ q → q) r
    delivery-rel (evs , i , s , inj₂ k) r = r

    delivery-carries : ∀ {u Θx ρ₀} {es vs}
                     → Carries {s = u} es vs
                     → Carries (map (applyClo (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀)) es) vs
    delivery-carries []              = []
    delivery-carries (quiet e′ r bs) = quiet _ (delivery-rel e′ r) (delivery-carries bs)
    delivery-carries (one e′ r bs)   = one _ (delivery-rel e′ r) (delivery-carries bs)

    -- A DEFERRED BODY'S EMITS CARRYING NOTHING pass the hop's marker
    -- merge, its restamp and the hop's node as they came; the tail's
    -- fold runs below the hop's node and the marker merge, so both
    -- survive it
    --
    -- REFUTED: `Refuted.Of-Fold-Sound`, read with
    --   `git show c2e60cb8:agda/evidence/refuted/Refuted/Of-Fold-Sound.agda`
    --   -- a tail related frame by frame
    --   may pass one merge twice, so what survives the tail's fold is
    --   owed only of a distinct impl path.
    quiet-deferInner : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₂ ℓ₃ u nid nid′ j j′ m2 j2}
                         {G : FnClo (plainᵏ Γ κ) (emitᵗ u) (emitᵗ u)}
                         {h : lo ≤ ℓ} {h₁ : lo′ ≤ n + ℓ} {h₂ : n + ℓ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                         {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                         {es fin o₁ y₁ f₁ s₁ st₁ o₃ y₃ f₃ s₃ st₃}
                     → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (from-inner mergeAllᵒ nid j ↠[ h ] p)
                         (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ] (map-f G ↠[ h₂ ] (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))
                     → Carries es [] → fin ≡ false
                     → Sound (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ] (map-f G ↠[ h₂ ] (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))) sI stI
                     → LiveFor es (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ] (map-f G ↠[ h₂ ] (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))) (EvalSt.nodes stI)
                     → stepFrame⇓ now (from-inner mergeAllᵒ m2 j2) (map-f G ↠[ h₂ ] (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))
                         es fin sI stI (o₁ , y₁ , f₁ , s₁ , st₁)
                     → stepFrame⇓ now (from-inner mergeAllᵒ nid′ j′) q (map (applyClo G) y₁) f₁ s₁ st₁ (o₃ , y₃ , f₃ , s₃ , st₃)
                     → QArm S now p (λ π NP NI → PathRel κ π NP NI (from-inner mergeAllᵒ nid j ↠[ h ] p)
                           (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ] (map-f G ↠[ h₂ ] (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))))
                         q y₃ f₃ (o₁ ++ o₃) s₃ st₃
    quiet-deferInner S {nid′ = nid′} {j′ = j′} {m2 = m2} {j2 = j2} (deferInner~ ip₁ ip₂ lP lI l2 a1 b1 pr) b refl si lv
                     (step-from-inner react-false) (step-from-inner react-false) =
      qarm (after S (λ x → x) (λ x → x) [] (λ x → x)) pr (delivery-carries b) refl
        (live-for (λ { refl → refl }) (λ l → inj₂ (live-if-drop _ _ _ refl refl (live-if-drop _ _ _ refl refl (live-if-drop _ _ _ refl refl l)))) lv)
        λ dq B rel′ →
        deferInner~ (After.grows B ip₁) (After.grows B ip₂) lP (trans (fold-unmoved dq c′) lI) (trans (fold-unmoved dq c2) l2) a1 b1 rel′
      where
      s2 = drop-ot _ _ _ (drop-ot _ _ _ si)
      s3 = drop-ot _ _ _ s2
      c′ = head-on _ _ _ nid′ (self-node nid′ (j′ ∷ [])) s2 , s3
      c2 = on-drop (on-drop (head-on _ _ _ m2 (self-node m2 (j2 ∷ [])) si)) , s3

    -- A SCAN'S CELL STEPPED ON EMITS CARRYING NOTHING stays related to
    -- the plain cell, which the plain scan's empty step leaves alone: the
    -- cell written on both sides, the plain one with what it holds
    quiet-scan : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ s u C k k′}
                   {F : FnClo Γ (u ×ᵗ s) u} {F′ : FnClo (plainᵏ Γ κ) (C ×ᵗ emitᵗ s) C} {G : FnClo (plainᵏ Γ κ) C (emitᵗ u)}
                   {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₂ (emitᵗ u) (emitᵗ t)}
                   {es fin o₁ y₁ f₁ s₁ st₁}
               → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (scan-f F k ↠[ h ] p) (scan-f F′ k′ ↠[ h₁ ] (map-f G ↠[ h₂ ] q))
               → Carries es [] → fin ≡ false
               → Sound (scan-f F k ↠[ h ] p) sP stP → Sound (scan-f F′ k′ ↠[ h₁ ] (map-f G ↠[ h₂ ] q)) sI stI
               → LiveFor es (scan-f F′ k′ ↠[ h₁ ] (map-f G ↠[ h₂ ] q)) (EvalSt.nodes stI)
               → stepFrame⇓ now (scan-f F′ k′) (map-f G ↠[ h₂ ] q) es fin sI stI (o₁ , y₁ , f₁ , s₁ , st₁)
               → QArm S now p (λ π NP NI → PathRel κ π NP NI (scan-f F k ↠[ h ] p) (scan-f F′ k′ ↠[ h₁ ] (map-f G ↠[ h₂ ] q)))
                   q (map (applyClo G) y₁) f₁ o₁ s₁ st₁
    quiet-scan {sP = sP} {stP} {sI} {stI} S {es = es}
               R@(scan~ {u = u} {k = k} {k′ = k′} {a = a} {a′ = a′} {em = em} {Θ₀ = Θ₀} {ρ₀ = ρ₀}
                        {h₁ = h₁} {F′ = F′} {p = p} {q = q} e lk lk′ v L _)
               bs refl sp si lv d₁
      with scan-at lk′ d₁
    ... | refl = qarm (proj₁ X) (proj₂ X) (proj₁ G₀) refl LV λ dq B rel′ →
                   scan~ (After.grows B (After.grows (proj₁ X) e)) lk (trans (fold-unmoved dq c′) lkI) (proj₂ G₀) L rel′
      where
      G₀ = scan-group {Θ₀ = Θ₀} {ρ₀ = ρ₀} L bs a′ em a v
      aI = proj₂ (scanVals F′ (a′ , em) es)
      NI = setNode k′ (cell-st {t = ScanAᵗ u} aI) (EvalSt.nodes stI)
      X : Σ (After S ([] , sP , stP) ([] , sI , record stI { nodes = NI })) λ A
            → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) NI p q
      X = subst (λ N → Σ (After S ([] , sP , record stP { nodes = N }) ([] , sI , record stI { nodes = NI })) λ A
                         → PathRel κ (Store.π (After.store A)) N NI p q)
                (set-same k (cell-st {t = u} a) (EvalSt.nodes stP) lk) (scan-write S R sp si a aI)
      lkI : lookupNode k′ NI ≡ just (cell-st {t = ScanAᵗ u} (proj₁ aI , proj₂ aI))
      lkI = lookup-set k′ (cell-st {t = ScanAᵗ u} aI) (EvalSt.nodes stI)
      -- the cell's write ends no outer and spends nothing
      LV = live-for (λ { refl → refl })
             (λ l → inj₂ (live-if-drop _ _ q refl refl
                           (live-if-set (_ ↠[ _ ] q) k′ (cell-st {t = ScanAᵗ u} aI) (EvalSt.nodes stI)
                              (λ _ → refl) (λ _ → cong spentAt lk′)
                              (live-if-drop (scan-f F′ k′) h₁ _ refl refl l))))
             lv
      so₁ = step-kept h₁ d₁ si
      c′ : Clear k′ q sI (record stI { nodes = NI })
      c′ = on-drop (head-on (scan-f F′ k′) h₁ _ k′ (self-node k′ []) so₁) , drop-ot _ _ _ (drop-ot _ _ _ so₁)

    -- AN INNER'S EMITS CARRYING NOTHING leave its lane as they came,
    -- the flattener's node unwritten, and are restamped; the tail's fold
    -- runs below the flattener's node and its cell, so both survive it
    --
    -- REFUTED: `Refuted.Of-Fold-Sound`, read with
    --   `git show c2e60cb8:agda/evidence/refuted/Refuted/Of-Fold-Sound.agda`
    --   -- a tail related frame by frame
    --   may pass one flattener twice, so what survives the tail's fold
    --   is owed only of a distinct impl path.
    quiet-inner : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₂ ℓ₃ u C a m m′ j j′ k}
                    {F : FnClo (plainᵏ Γ κ) (C ×ᵗ emitᵗ u) C} {G : FnClo (plainᵏ Γ κ) C (emitᵗ u)}
                    {h : lo ≤ ℓ} {h₁ : lo′ ≤ n + ℓ} {h₂ : n + ℓ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                    {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                    {es fin o₁ y₁ f₁ s₁ st₁ o₂ y₂ f₂ s₂ st₂}
                → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (from-inner a m j ↠[ h ] p)
                    (from-inner a m′ j′ ↠[ h₁ ] (scan-f F k ↠[ h₂ ] (map-f G ↠[ h₃ ] q)))
                → Carries es [] → fin ≡ false
                → Sound (from-inner a m′ j′ ↠[ h₁ ] (scan-f F k ↠[ h₂ ] (map-f G ↠[ h₃ ] q))) sI stI
                → LiveFor es (from-inner a m′ j′ ↠[ h₁ ] (scan-f F k ↠[ h₂ ] (map-f G ↠[ h₃ ] q))) (EvalSt.nodes stI)
                → stepFrame⇓ now (from-inner a m′ j′) (scan-f F k ↠[ h₂ ] (map-f G ↠[ h₃ ] q)) es fin sI stI (o₁ , y₁ , f₁ , s₁ , st₁)
                → stepFrame⇓ now (scan-f F k) (map-f G ↠[ h₃ ] q) y₁ f₁ s₁ st₁ (o₂ , y₂ , f₂ , s₂ , st₂)
                → QArm S now p (λ π NP NI → PathRel κ π NP NI (from-inner a m j ↠[ h ] p)
                      (from-inner a m′ j′ ↠[ h₁ ] (scan-f F k ↠[ h₂ ] (map-f G ↠[ h₃ ] q))))
                    q (map (applyClo G) y₂) f₂ (o₁ ++ o₂) s₂ st₂
    quiet-inner {stP = stP} S {m′ = m′} {j′ = j′} {h₂ = h₂} {h₃ = h₃} {q = q} (inner~ e f ip pr) b refl si lv (step-from-inner react-false) d₂ =
      let (A , f′ , pr′ , c′ , e′ , _) = restamp-echo S f pr b d₂
      in qarm A pr′ c′ e′ (live-echo {π = Store.π S} {NP = EvalSt.nodes stP} {h₃ = h₂} {h₄ = h₃} {q = q} f d₂ (live-for (λ x → x) (λ l → inj₂ (live-if-drop _ _ _ refl refl l)) lv)) λ {rI} dq B rel′ →
           inner~ e (flat-move (EvalSt.nodes stP) _ (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI))) (After.grows B)
                          (unmoved refl) (missed dq (proj₁ cI)) (missed dq (proj₂ cI , proj₂ (proj₁ cI))) f′)
                  (After.grows B (After.grows A ip)) rel′
      where
      cI = tail-of (step-clear d₂ (head-on _ _ _ m′ (self-node m′ (j′ ∷ [])) si , drop-ot _ _ _ si))

    -- A TEST'S CUT NEVER FIRES ON NOTHING: no value to test, so an open
    -- test's nodes are written open on both sides, the plain one with
    -- the one it holds
    quiet-takeWhile : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ s C P k k₁ k₂ w}
                        {F₁ : FnClo (plainᵏ Γ κ) (C ×ᵗ emitᵗ s) C} {G : FnClo (plainᵏ Γ κ) C (emitᵗ s)}
                        {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                        {p : Path Γ ℓ s t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ s) (emitᵗ t)}
                        {es fin o₁ y₁ f₁ s₁ st₁ o₂ y₂ f₂ s₂ st₂}
                    → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (take-f (just P) k ↠[ h ] p)
                        (scan-f F₁ k₁ ↠[ h₁ ] (take-f w k₂ ↠[ h₂ ] (map-f G ↠[ h₃ ] q)))
                    → Carries es [] → fin ≡ false
                    → Sound (take-f (just P) k ↠[ h ] p) sP stP
                    → Sound (scan-f F₁ k₁ ↠[ h₁ ] (take-f w k₂ ↠[ h₂ ] (map-f G ↠[ h₃ ] q))) sI stI
                    → LiveFor es (scan-f F₁ k₁ ↠[ h₁ ] (take-f w k₂ ↠[ h₂ ] (map-f G ↠[ h₃ ] q))) (EvalSt.nodes stI)
                    → stepFrame⇓ now (scan-f F₁ k₁) (take-f w k₂ ↠[ h₂ ] (map-f G ↠[ h₃ ] q)) es fin sI stI (o₁ , y₁ , f₁ , s₁ , st₁)
                    → stepFrame⇓ now (take-f w k₂) (map-f G ↠[ h₃ ] q) y₁ f₁ s₁ st₁ (o₂ , y₂ , f₂ , s₂ , st₂)
                    → QArm S now p (λ π NP NI → PathRel κ π NP NI (take-f (just P) k ↠[ h ] p)
                          (scan-f F₁ k₁ ↠[ h₁ ] (take-f w k₂ ↠[ h₂ ] (map-f G ↠[ h₃ ] q))))
                        q (map (applyClo G) y₂) f₂ (o₁ ++ o₂) s₂ st₂
    quiet-takeWhile {sP = sP} {stP} {sI} {stI} S {es = es}
                    (spentWhile~ {k = k} {k₁ = k₁} {k₂ = k₂} {h₁ = h₁} {h₂ = h₂} {F₁ = F₁} {p = p} {q = q} e lk lk₂ r)
                    bs refl sp si _ d₁ d₂
      with scan-any d₁
    ... | inj₁ refl with take-open-at lk₂ refl d₂
    ...   | refl = qarm (proj₁ X) (proj₂ X) [] refl (inj₁ refl) λ dq B rel′ →
                     spentWhile~ (After.grows B (After.grows (proj₁ X) e)) lk (trans (fold-unmoved dq c₂) lk₂′) rel′
      where
      N₂ = setNode k₂ (take-st 0) (EvalSt.nodes stI)
      X : Σ (After S ([] , sP , stP) ([] , sI , record stI { nodes = N₂ })) λ A
            → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) N₂ p q
      X = subst (λ N → Σ (After S ([] , sP , stP) ([] , sI , record stI { nodes = N })) λ A
                         → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) N p q)
                (sym (set-same k₂ (take-st 0) (EvalSt.nodes stI) lk₂)) (after S (λ x → x) (λ x → x) [] (λ x → x) , r)
      lk₂′ : lookupNode k₂ N₂ ≡ just (take-st 0)
      lk₂′ = lookup-set k₂ (take-st 0) (EvalSt.nodes stI)
      so₂ = step-kept h₂ d₂ (drop-ot _ _ _ (step-kept h₁ d₁ si))
      c₂ : Clear k₂ q sI _
      c₂ = on-drop (head-on _ h₂ _ k₂ (self-node k₂ []) so₂) , drop-ot _ _ _ (drop-ot _ _ _ so₂)
    quiet-takeWhile {sP = sP} {stP} {sI} {stI} S {es = es}
                    (spentWhile~ {k = k} {k₁ = k₁} {k₂ = k₂} {h₁ = h₁} {h₂ = h₂} {F₁ = F₁} {p = p} {q = q} e lk lk₂ r)
                    bs refl sp si _ d₁ d₂ | inj₂ (a , l₁ , refl)
      with take-open-at (trans (set-above k₁ k₂ (cell-st (proj₂ (scanVals F₁ a es))) (EvalSt.nodes stI)
                                 (apart k₁ k₂ (cell-take {N = EvalSt.nodes stI} {k = k₁} {k′ = k₂} l₁ lk₂))) lk₂) refl d₂
    ...   | refl = qarm (proj₁ X) (proj₂ X) [] refl (inj₁ refl) λ dq B rel′ →
                     spentWhile~ (After.grows B (After.grows (proj₁ X) e)) lk (trans (fold-unmoved dq c₂) lk₂′) rel′
      where
      N₁ = setNode k₁ (cell-st (proj₂ (scanVals F₁ a es))) (EvalSt.nodes stI)
      N₂ = setNode k₂ (take-st 0) N₁
      lk₂₁ : lookupNode k₂ N₁ ≡ just (take-st 0)
      lk₂₁ = trans (set-above k₁ k₂ (cell-st (proj₂ (scanVals F₁ a es))) (EvalSt.nodes stI)
                     (apart k₁ k₂ (cell-take {N = EvalSt.nodes stI} {k = k₁} {k′ = k₂} l₁ lk₂))) lk₂
      X : Σ (After S ([] , sP , stP) ([] , sI , record stI { nodes = N₂ })) λ A
            → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) N₂ p q
      X = subst (λ N → Σ (After S ([] , sP , stP) ([] , sI , record stI { nodes = N })) λ A
                         → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) N p q)
                (sym (set-same k₂ (take-st 0) N₁ lk₂₁)) (spent-write S e lk l₁ r)
      lk₂′ : lookupNode k₂ N₂ ≡ just (take-st 0)
      lk₂′ = lookup-set k₂ (take-st 0) N₁
      so₂ = step-kept h₂ d₂ (drop-ot _ _ _ (step-kept h₁ d₁ si))
      c₂ : Clear k₂ q sI _
      c₂ = on-drop (head-on _ h₂ _ k₂ (self-node k₂ []) so₂) , drop-ot _ _ _ (drop-ot _ _ _ so₂)
    quiet-takeWhile {sP = sP} {stP} {sI} {stI} S {es = es}
                    R@(takeWhile~ {s = s} {k = k} {k₁ = k₁} {k₂ = k₂} {os = os} {em = em} {Θ₂ = Θ₂} {ρ₂ = ρ₂} {Θ₃ = Θ₃} {ρ₃ = ρ₃}
                                  {h₁ = h₁} {h₂ = h₂} {P = P} {F₁ = F₁} {p = p} {q = q} e lk lk₁ lk₂ CL _)
                    bs refl sp si lv d₁ d₂
      with cut-group {Bud = λ _ b → b ≡ 1} {F′ = F₁} {P = just P} {Θ₂ = Θ₂} {ρ₂ = ρ₂} {Θ₃ = Θ₃} {ρ₃ = ρ₃} CL bs (tt , false , os , em) 1 refl refl
         | scan-at lk₁ d₁
    ... | cs , fe , rest , _ | refl
      with rest refl
         | take-open-at (trans (set-above k₁ k₂ (cell-st {t = CutS unitᵗ s} (proj₂ (scanVals F₁ (tt , false , os , em) es))) (EvalSt.nodes stI)
                                          (apart k₁ k₂ (cell-take {N = EvalSt.nodes stI} {k = k₁} {k′ = k₂} lk₁ lk₂))) lk₂)
                        fe d₂
    ... | r1 , fl , _ | refl =
      qarm (proj₁ X) (proj₂ X) cs refl LV λ dq B rel′ →
        takeWhile~ (After.grows B (After.grows (proj₁ X) e)) lk (trans (fold-unmoved dq c₁) lk₁′) (trans (fold-unmoved dq c₂) lk₂′) CL rel′
      where
      fc : Val (plainᵏ Γ κ) (CutS unitᵗ s)
      fc = proj₂ (scanVals F₁ (tt , false , os , em) es)
      r₂ = proj₁ (proj₂ (takeVals {s = CutS unitᵗ s} (just (Θ₂ , cutOpenᵛ , ρ₂)) 1 (proj₁ (scanVals F₁ (tt , false , os , em) es))))
      N₁ = setNode k₁ (cell-st {t = CutS unitᵗ s} fc) (EvalSt.nodes stI)
      N₂ = setNode k₂ (take-st r₂) N₁
      X : Σ (After S ([] , sP , stP) ([] , sI , record stI { nodes = N₂ })) λ A
            → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) N₂ p q
      X = subst (λ N → Σ (After S ([] , sP , record stP { nodes = N }) ([] , sI , record stI { nodes = N₂ })) λ A
                         → PathRel κ (Store.π (After.store A)) N N₂ p q)
                (set-same k (take-st 1) (EvalSt.nodes stP) lk) (while-write S R sp si 1 fc r₂ fl refl r1)
      lk₁′ : lookupNode k₁ N₂ ≡ just (cell-st {t = CutS unitᵗ s} (tt , false , proj₂ (proj₂ fc)))
      lk₁′ = trans (set-above k₂ k₁ (take-st r₂) N₁ (apart k₂ k₁ (λ x → cell-take {N = EvalSt.nodes stI} {k = k₁} {k′ = k₂} lk₁ lk₂ (sym x))))
                   (subst (λ f → lookupNode k₁ N₁ ≡ just (cell-st {t = CutS unitᵗ s} (tt , f , proj₂ (proj₂ fc))))
                          fl (lookup-set k₁ (cell-st {t = CutS unitᵗ s} fc) (EvalSt.nodes stI)))
      lk₂′ : lookupNode k₂ N₂ ≡ just (take-st 1)
      lk₂′ = subst (λ x → lookupNode k₂ N₂ ≡ just (take-st x)) r1 (lookup-set k₂ (take-st r₂) N₁)
      -- the test stays open, so the writes end no outer and spend nothing
      LV = live-for (λ { refl → refl })
             (λ l → inj₂ (live-if-drop (map-f (Θ₃ , cutOutᵛ , ρ₃)) _ q refl refl
                           (live-if-set (map-f (Θ₃ , cutOutᵛ , ρ₃) ↠[ _ ] q) k₂ (take-st r₂) N₁
                              (λ _ → refl)
                              (λ _ → cong spentAt (trans (set-above k₁ k₂ (cell-st {t = CutS unitᵗ s} fc) (EvalSt.nodes stI)
                                                            (apart k₁ k₂ (cell-take {N = EvalSt.nodes stI} {k = k₁} {k′ = k₂} lk₁ lk₂))) lk₂))
                              (live-if-set (map-f (Θ₃ , cutOutᵛ , ρ₃) ↠[ _ ] q) k₁ (cell-st {t = CutS unitᵗ s} fc) (EvalSt.nodes stI)
                                 (λ _ → refl) (λ _ → cong spentAt lk₁)
                                 (live-if-take h₂ (map-f (Θ₃ , cutOutᵛ , ρ₃) ↠[ _ ] q) (cong spentAt lk₂)
                                    (live-if-drop (scan-f F₁ k₁) h₁ _ refl refl l))))))
             lv
      so₁ = step-kept h₁ d₁ si
      so₂ = step-kept h₂ d₂ (drop-ot _ _ _ so₁)
      soq = drop-ot _ _ _ (drop-ot _ _ _ so₂)
      c₁ : Clear k₁ q sI _
      c₁ = on-drop (on-drop (proj₁ (step-clear d₂ (head-on (scan-f F₁ k₁) h₁ _ k₁ (self-node k₁ []) so₁ , drop-ot _ _ _ so₁)))) , soq
      c₂ : Clear k₂ q sI _
      c₂ = on-drop (head-on _ h₂ _ k₂ (self-node k₂ []) so₂) , soq

    mutual
      quiet-pass : ∀ {lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)} → Quiet p q
      quiet-pass S root~ b refl _ _ _ fold-root = after S (λ x → x) (λ x → x) (root-values b false) (λ x → x) , root~
      quiet-pass S r@(sink~ sh) b e sp si lv dI = quiet-sink sh S r b e sp si lv dI
      quiet-pass S (map~ L r) b e sp si lv (fold-step step-map dI) =
        let X = quiet-pass S r (carries-map L b) e (drop-ot _ _ _ sp) (drop-ot _ _ _ si)
                  (live-for (λ { refl → refl }) (λ l → inj₂ (live-if-drop _ _ _ refl refl l)) lv) dI in proj₁ X , map~ L (proj₂ X)
      quiet-pass S r@(scan~ _ _ _ _ _ _) b e sp si lv (fold-step d₁ (fold-step step-map dq)) =
        quiet-resume (quiet-scan S r b e sp si lv d₁) (drop-ot _ _ _ sp) (drop-ot _ _ _ (adv d₁ si)) dq
      quiet-pass S r@(takeWhile~ _ _ _ _ _ _) b e sp si lv (fold-step {out₁ = o₁} d₁ (fold-step {out₁ = o₂} d₂ (fold-step step-map dq))) =
        let X = quiet-resume (quiet-takeWhile S r b e sp si lv d₁ d₂) (drop-ot _ _ _ sp) (drop-ot _ _ _ (adv d₂ (adv d₁ si))) dq
        in after-out (regroup₂ o₁ o₂ _) (proj₁ X) , proj₂ X
      quiet-pass S r@(spentWhile~ _ _ _ _) b e sp si lv (fold-step {out₁ = o₁} d₁ (fold-step {out₁ = o₂} d₂ (fold-step step-map dq))) =
        let X = quiet-resume (quiet-takeWhile S r b e sp si lv d₁ d₂) (drop-ot _ _ _ sp) (drop-ot _ _ _ (adv d₂ (adv d₁ si))) dq
        in after-out (regroup₂ o₁ o₂ _) (proj₁ X) , proj₂ X
      quiet-pass S (outerElem~ fl r) b e sp si lv dI = quiet-outer S (fl , r) b e sp si lv dI
      quiet-pass S (outerExplode~ fl x r) b e sp si lv dI = quiet-explode S fl x r b e sp si lv dI
      quiet-pass S r@(inner~ refl _ _ _) b e sp si lv (fold-step {out₁ = o₁} d₁ (fold-step {out₁ = o₂} d₂ (fold-step step-map dq))) =
        let X = quiet-resume (quiet-inner S r b e si lv d₁ d₂) (drop-ot _ _ _ sp) (drop-ot _ _ _ (adv d₂ (adv d₁ si))) dq
        in after-out (regroup₂ o₁ o₂ _) (proj₁ X) , proj₂ X
      quiet-pass S r@(deferInner~ _ _ _ _ _ _ _ _) b e sp si lv (fold-step {out₁ = o₁} d₁ (fold-step step-map (fold-step {out₁ = o₃} d₃ dq))) =
        let X = quiet-resume (quiet-deferInner S r b e si lv d₁ d₃) (drop-ot _ _ _ sp) (adv d₃ (drop-ot _ _ _ (adv d₁ si))) dq
        in after-out (regroup₂ o₁ o₃ _) (proj₁ X) , proj₂ X

      -- A SHARE'S SUBJECT FANS A VALUELESS GROUP OUT TO EVERY READER, and
      -- every reader's chain folds it on the impl side alone.  The walk
      -- marks no reader delivered, since the group carries no end
      quiet-sink : ∀ {lo lo′} {i : Fin n} {h : lo ≤ toℕ i} {h′ : lo′ ≤ toℕ (n ↑ʳ i)} (sh : lookup κ i ≡ sharedᵏ)
                 → Quiet (share-sink i h)
                     (subst (λ u → Path (plainᵏ Γ κ) lo′ u (emitᵗ t)) (sharedEq {Γ = Γ} κ i sh) (share-sink (n ↑ʳ i) h′))
      quiet-sink {i = i} sh S _ b refl _ _ _ dI = sink-quiet S (sharedEq {Γ = Γ} κ i sh) refl b dI , sink~ sh

      -- the subject's fold, read at the type the share holds: the cast
      -- left as an equation the fold is matched under, so the walk is the
      -- fold's own premise
      sink-quiet : ∀ {sP stP sI stI} (S : St sP stP sI stI) {lo′} {i : Fin n} {h′ : lo′ ≤ toℕ (n ↑ʳ i)} {w}
                     (E : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ w) (F : w ≡ emitᵗ (lookup Γ i)) {now es rI}
                 → CarriesU F es []
                 → foldPath⇓ now (subst (λ u → Path (plainᵏ Γ κ) lo′ u (emitᵗ t)) E (share-sink (n ↑ʳ i) h′)) es false sI stI rI
                 → After S ([] , sP , stP) rI
      sink-quiet S refl F c (fold-sink (disp w)) = quiet-share S F c w

      -- the walk, one emit at a time, each fanned out to the readers the
      -- registry then admits
      quiet-share : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n} (F : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (lookup Γ i))
                      {now es rI}
                  → CarriesU F es [] → shareWalk⇓ now (n ↑ʳ i) es false sI stI rI → After S ([] , sP , stP) rI
      quiet-share S F c walk-nil = after S (λ x → x) (λ x → x) [] (λ x → x)
      quiet-share S {i = i} F c (walk-more g w) = A ⨾ quiet-share (After.store A) F (cu-tail F c) w
        where
          A = quiet-go S F (cu-head F c) (share-rows S) (admit-ot i _ _ (Store.ruleP S))
                (admit-ot (n ↑ʳ i) _ _ (Store.ruleI S)) (admit-agrees (n ↑ʳ i) (Store.ruleI S)) g

      -- ONE EMIT TO EVERY ADMITTED READER, the impl's alone: a cut pair
      -- skipped, a live one folded down its reader's tail
      quiet-go : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n}
                   (F : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (lookup Γ i)) {es now}
               → CarriesU F es []
               → ∀ {chs adm}
               → Pointwise (ShareSlot (Store.rows S) (EvalSt.cancelled stP) (EvalSt.cancelled stI) i) chs adm
               → (∀ {x} → x ∈ chs → Sound (proj₂ x) sP stP)
               → (∀ {x} → x ∈ adm → Sound (proj₂ x) sI stI)
               → (∀ {x y} → x ∈ adm → y ∈ adm → Agree (proj₂ x) (proj₂ y))
               → ∀ {rI} → shareGo⇓ now (n ↑ʳ i) es false adm sI stI rI
               → After S ([] , sP , stP) rI
      quiet-go S F c [] _ _ _ go-nil = after S (λ x → x) (λ x → x) [] (λ x → x)
      quiet-go S F c (slotpair _ ∷ ps) hP hI aI (go-cut _ g) =
        quiet-go S F c ps (λ m → hP (there m)) (λ m → hI (there m)) (λ m m′ → aI (there m) (there m′)) g
      quiet-go S F c (slotpair (inj₁ (_ , x)) ∷ _) _ _ _ (go-live {i = i₀} {rid = rid} {st₀ = st₀} y _ _) =
        ⊥-elim (t≢f (trans (sym (skip-cut {s = toℕ i₀} {rid} {st₀} x)) y))
      quiet-go S {i = i} F c (slotpair (inj₂ (_ , _ , pr)) ∷ ps) hP hI aI (go-live y dI g) =
        A ⨾ quiet-go (After.store A) F c (share-keeps {S₀ = S} {S₁ = After.store A} {i = i} (After.keeps A) ps)
              (λ m → hP (there m))
              (λ m → fold-kept dI (hI (here refl)) _ (hI (there m)) (aI (here refl) (there m)))
              (λ m m′ → aI (there m) (there m′)) g
        where
          A = slot-quiet S F (partner-row κ _ _ _ _ _ (Store.rows S) pr) c (hP (here refl)) (hI (here refl))
                (LiveRows.rows-live (Inv.live-outer (Store.inv S)) (proj₂ (partner-mem κ _ _ _ _ _ (Store.rows S) pr)) y) dI

      -- a slot's partnered reader: the restamp on the impl side alone,
      -- then the tail the store relates to the plain reader
      slot-quiet : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n} {u u′ rid rid′}
                     {p : Path Γ (suc (toℕ i)) u t} {p′ : Path (plainᵏ Γ κ) (suc (toℕ (n ↑ʳ i))) u′ (emitᵗ t)}
                     {es} (F : u′ ≡ emitᵗ u)
                 → RowRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI)
                     (rid , atSlot i , (u , p)) (rid′ , atSlot (n ↑ʳ i) , (u′ , p′))
                 → CarriesU F es []
                 → Sound p sP stP → Sound p′ sI stI → LiveOn p′ (EvalSt.nodes stI)
                 → ∀ {now rI} → foldPath⇓ now p′ es false sI stI rI
                 → After S ([] , sP , stP) rI
      slot-quiet S {i = i} {p′ = p′} refl (read~ {X = X} _ r refl) c sp si L (fold-step step-map dq) =
        proj₁ (quiet-pass S r (restamp-carries {i = i} {X = X} c) refl sp (drop-ot _ _ _ si)
                 (inj₂ (live-if-drop _ _ _ refl refl (live-if {q = p′} (λ _ → L)))) dq)

      -- AN EXPLODED OUTER'S EMITS CARRYING NOTHING explode into no
      -- inner, the merge's walk subscribing each empty run, and its
      -- echo is restamped on the impl side alone
      quiet-explode : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₅ ρ₅ Θ₁ ρ₁ Θ₂ ρ₂}
                        {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ n + ℓ}
                        {h₅ : n + ℓ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                        {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)} {es fin rI}
                    → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                    → MergeAt {Γ = Γ} κ (EvalSt.nodes stI) u mX
                    → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                    → Carries es [] → fin ≡ false
                    → Sound (thru-outer (flatOp op) m ↠[ h ] p) sP stP
                    → Sound (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                             (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                              (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                               (thru-outer (flatOp op) m′ ↠[ h₄ ]
                                (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₅ ]
                                 (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₆ ] q)))))) sI stI
                    → LiveFor es (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                             (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                              (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                               (thru-outer (flatOp op) m′ ↠[ h₄ ]
                                (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₅ ]
                                 (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₆ ] q)))))) (EvalSt.nodes stI)
                    → foldPath⇓ now (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                                     (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                                      (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                                       (thru-outer (flatOp op) m′ ↠[ h₄ ]
                                        (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₅ ]
                                         (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₆ ] q))))))
                        es fin sI stI rI
                    → Σ (After S ([] , sP , stP) rI) λ A
                        → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI)))
                            (thru-outer (flatOp op) m ↠[ h ] p)
                            (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                             (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                              (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                               (thru-outer (flatOp op) m′ ↠[ h₄ ]
                                (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₅ ]
                                 (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₆ ] q))))))
      quiet-explode S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₅ = Θ₅} {ρ₅ = ρ₅} fl x r b refl sp si lv
                    (fold-step step-map (fold-step step-map (fold-step dW@(step-thru-outer W) dR))) =
        let si′ = drop-ot _ _ _ (drop-ot _ _ _ si)
            (X , fl′ , r′ , x′) = explode-none S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₅ = Θ₅} {ρ₅ = ρ₅} (unthru sp) (unthru si′) fl r x
                                    (live-for (λ e → e) (λ l → inj₂ (live-if-drop _ _ _ refl refl (live-if-drop _ _ _ refl refl l))) lv) b W
            (T , fl″ , r″ , x″) = explode-tail (After.store X) {op = op} (proj₂ (unthru sp)) (unthru (step-kept _ dW si′)) fl′ r′ x′ dR
        in X ⨾ T , outerExplode~ fl″ x″ r″

      -- THE EXPLODED OUTER'S TAIL, handed the walk's empty group: the
      -- flattener steps over it and the restamp echoes nothing
      explode-tail : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₁ ρ₁ Θ₂ ρ₂}
                       {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)} {rI}
                   → Sound p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                   → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                   → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                   → MergeAt {Γ = Γ} κ (EvalSt.nodes stI) u mX
                   → foldPath⇓ now (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) [] false sI stI rI
                   → Σ (After S ([] , sP , stP) rI) λ A
                       → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI)))
                           u op m m′ ks (mX ∷ [])
                         × PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
                         × MergeAt {Γ = Γ} κ (EvalSt.nodes (proj₂ (proj₂ rI))) u mX
      explode-tail {stP = stP} S {h₅ = h₅} sp ci fl r x d@(fold-step dW@(step-thru-outer walk-nil) (fold-step d₁ (fold-step step-map dq))) =
        let cI = tail-of (step-clear d₁ (unthru (step-kept _ dW (proj₂ ci))))
            (A , f′ , r′ , c′ , e′ , _) = restamp-echo S fl r [] d₁
            B  = quiet-pass (After.store A) r′ c′ e′ sp (proj₂ (proj₁ cI)) (live-echo {π = Store.π S} {NP = EvalSt.nodes stP} {h₃ = h₅} fl d₁ (inj₁ refl)) dq
        in A ⨾ proj₁ B ,
           flat-move (EvalSt.nodes stP) _ (EvalSt.nodes stP) _ (After.grows (proj₁ B)) (unmoved refl)
                     (missed dq (proj₁ cI)) (missed dq (proj₂ cI , proj₂ (proj₁ cI))) f′ ,
           proj₂ B , merge-moved (missed d ci) x

      -- THE EXPLODED OUTER'S WALK, every emit carrying nothing
      explode-none : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₅ ρ₅ Θ₁ ρ₁ Θ₂ ρ₂}
                       {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                       {es rI}
                   → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                   → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                   → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                   → MergeAt {Γ = Γ} κ (EvalSt.nodes stI) u mX
                   → LiveFor es (thru-outer mergeAllᵒ mX ↠[ h₃ ] (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)) (EvalSt.nodes stI)
                   → Carries {echoᵗ u} es []
                   → thruWalk⇓ mergeAllᵒ mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) now
                       (thruEvents (map (applyClo {s = obs (echoᵗ (emitᵗ u))} {t = echoᵗ (echoᵗ (emitᵗ u))}
                                                  (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅))
                                        (map (applyClo {s = emitᵗ (echoᵗ u)} {t = obs (echoᵗ (emitᵗ u))} (Θ₀ , explodeᵛ , ρ₀)) es))) sI stI rI
                   → Σ (After S ([] , sP , stP) rI) λ A
                       → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI)))
                           u op m m′ ks (mX ∷ [])
                         × PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
                         × MergeAt {Γ = Γ} κ (EvalSt.nodes (proj₂ (proj₂ rI))) u mX
      explode-none S cp ci fl r x _ [] walk-nil = after S (λ y → y) (λ y → y) [] (λ y → y) , fl , r , x
      explode-none S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₅ = Θ₅} {ρ₅ = ρ₅} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂}
                   cp ci fl r x lv (quiet e′ bare b) (walk-cons C W′) =
        let l = live-cons lv
            (X , fl′ , r′ , x′ , _) = explode-quiet S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} cp ci fl r x l e′ bare C
            (Y , rest) = explode-none (After.store X) {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₅ = Θ₅} {ρ₅ = ρ₅} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂}
                                      cp (consume-clear C ci) fl′ r′ x′ (inj₂ (consume-spares C l)) b W′
        in (X ⨾ Y) , rest

      -- AN OUTER'S EMIT CARRYING NOTHING, EXPLODED: the merge is unbounded,
      -- so its consume neither queues nor finds the node unusable, and
      -- subscribes
      explode-quiet : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                      {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                      {rI}
                  → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                  → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                  → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                  → MergeAt {Γ = Γ} κ (EvalSt.nodes stI) u mX
                  → LiveIf (thru-outer mergeAllᵒ mX ↠[ h₃ ] (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)) (EvalSt.nodes stI)
                  → ∀ e′ → Bare {echoᵗ u} e′
                  → thruConsume⇓ mergeAllᵒ mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) now
                      (applyClo {s = emitᵗ (echoᵗ u)} {t = obs (echoᵗ (emitᵗ u))} (Θ₀ , explodeᵛ , ρ₀) e′) sI stI rI
                  → Σ (After S ([] , sP , stP) rI) λ A
                      → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI)))
                          u op m m′ ks (mX ∷ [])
                        × PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
                        × MergeAt {Γ = Γ} κ (EvalSt.nodes (proj₂ (proj₂ rI))) u mX
                        × (∀ {I} → DelAt {echoᵗ u} I e′ → Out I (proj₁ rI))
      explode-quiet S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} cp ci fl r x lv e′ b
                    (consume-all-sub l _ c) =
        explode-quiet-sub S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} cp ci fl r x lv (trans (sym (proj₂ x)) l) e′ b c
      explode-quiet S cp ci fl r (_ , lX) _ e′ b (consume-all-enqueue l h) = ⊥-elim (no-queue (trans (sym lX) l) h)
      explode-quiet S {u = u} cp ci fl r (_ , lX) _ e′ b (consume-all-nil e) =
        ⊥-elim (unusable mergeAllᵒ (echoᵗ (emitᵗ u)) lX e (usable-self (echoᵗ (emitᵗ u))))

      -- AN OUTER'S EMIT CARRYING NOTHING, EXPLODED, SUBSCRIBED: the impl's
      -- merge takes its one quiet element as an inner, the plain side
      -- does not move, and the merge stays unbounded at the echo's type;
      -- what it sends, it sends at the emit's own delivery.  The inner is
      -- the counter's next node, so no row keeps it alive and it finishes
      -- at once: its element walks the flattener, the merge's count falls
      -- back, and the empty group the finish leaves folds the tail
      explode-quiet-sub : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                          {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                          {lim a qs od inst out sched₁ st₁}
                      → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                      → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                      → (mg : MergeAt {Γ = Γ} κ (EvalSt.nodes stI) u mX)
                      → LiveIf (thru-outer mergeAllᵒ mX ↠[ h₃ ] (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)) (EvalSt.nodes stI)
                      → just (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] (proj₁ mg)) ≡ just (mergeAll-st lim a qs od)
                      → ∀ e′ → Bare {echoᵗ u} e′
                      → subscribeInner⇓ mergeAllᵒ mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) now
                          (applyClo {s = emitᵗ (echoᵗ u)} {t = obs (echoᵗ (emitᵗ u))} (Θ₀ , explodeᵛ , ρ₀) e′) sI
                          (record stI { nodes = setNode mX (mergeAll-st {t = echoᵗ (emitᵗ u)} lim (suc a) qs od) (EvalSt.nodes stI) })
                          (inst , out , sched₁ , st₁)
                      → Σ (After S ([] , sP , stP) (out , sched₁ , st₁)) λ A
                          → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes stP) (EvalSt.nodes st₁) u op m m′ ks (mX ∷ [])
                            × PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes st₁) p q
                            × MergeAt {Γ = Γ} κ (EvalSt.nodes st₁) u mX
                            × (∀ {I} → DelAt {echoᵗ u} I e′ → Out I out)
      explode-quiet-sub S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} cp ci fl r (true , lX) lv refl e′ b c =
        explode-quiet-ended S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} cp ci fl r lv lX e′ b c
      explode-quiet-sub S {op = op} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} cp ci fl r (false , lX) lv refl e′ b (inner refl sub) =
        let (_ , _ , _ , eq , qz) = explode-run e′ b
            (A , f , pr , x) = explode-fresh S {op = op} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} cp ci fl r lX lv qz eq sub
        in A , f , pr , x , λ _ → nil-all (After.values A)

      -- THE EXPLODE'S INNER, ITS ONE QUIET ELEMENT IN HAND: the counter's
      -- next node, so no row keeps it alive and it finishes at once; its
      -- element walks the flattener, the merge's count falls back, and the
      -- empty group the finish leaves folds the tail
      explode-fresh : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₁ ρ₁ Θ₂ ρ₂}
                        {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                        {Θ′ ρ′} {tm : Tm (plainᵏ Γ κ) [] [] Θ′ (echoᵗ (emitᵗ u))} {o out sched₁ st₁}
                    → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                    → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                    → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                    → lookupNode mX (EvalSt.nodes stI) ≡ just (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] false)
                    → LiveIf (thru-outer mergeAllᵒ mX ↠[ h₃ ] (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)) (EvalSt.nodes stI)
                    → QuietElem {u} (evalWith tm ρ′)
                    → o ≡ (Θ′ , ofᵉ (tm ∷ []) , ρ′)
                    → subscribeE⇓ o (from-inner mergeAllᵒ mX (nodeCt sI) ↠[ ≤-refl ] (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)) now
                        (record sI { mint = setAt nodeᵏ (suc (nodeCt sI)) (Sched.mint sI) })
                        (record stI { nodes = setNode mX (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 1 [] false) (EvalSt.nodes stI) })
                        (out , sched₁ , st₁)
                    → Σ (After S ([] , sP , stP) (out , sched₁ , st₁)) λ A
                        → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes stP) (EvalSt.nodes st₁) u op m m′ ks (mX ∷ [])
                          × PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes st₁) p q
                          × MergeAt {Γ = Γ} κ (EvalSt.nodes st₁) u mX
      explode-fresh S cp ci fl r lX lv qz refl (subs-of (fold-step (step-from-inner (react-alive al)) _)) =
        ⊥-elim (t≢f (trans (sym al) (fresh-dead (Store.ruleI S))))
      explode-fresh {sI = sI} {stI = stI} S {op = op} {mX = mX} {Θ′ = Θ′} {ρ′ = ρ′} {tm = tm} cp ci fl r lX lv qz refl
                    (subs-of (fold-step (step-from-inner (react-dead _ F′)) F₂)) =
        explode-drain S {op = op} {mX = mX} {Θ′ = Θ′} {ρ′ = ρ′} {tm = tm} cp ci fl r lX lv qz
          (finish-at (lookup-set mX _ (EvalSt.nodes stI)) F′) F₂

      -- the inner's finish read at the node it set, so its arms match
      -- with no with-abstraction over the subscribe's context
      explode-drain : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₁ ρ₁ Θ₂ ρ₂}
                        {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                        {Θ′ ρ′} {tm : Tm (plainᵏ Γ κ) [] [] Θ′ (echoᵗ (emitᵗ u))} {r₁ out₂ sched₂ st₂}
                    → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                    → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                    → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                    → lookupNode mX (EvalSt.nodes stI) ≡ just (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] false)
                    → LiveIf (thru-outer mergeAllᵒ mX ↠[ h₃ ] (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)) (EvalSt.nodes stI)
                    → QuietElem {u} (evalWith tm ρ′)
                    → innerFinish⇓ mergeAllᵒ mX (nodeCt sI) (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) now (evalWith tm ρ′ ∷ [])
                        (record sI { mint = setAt nodeᵏ (suc (nodeCt sI)) (Sched.mint sI) })
                        (record stI { nodes = setNode mX (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 1 [] false) (EvalSt.nodes stI) })
                        (just (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 1 [] false)) r₁
                    → foldPath⇓ now (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) (proj₁ (proj₂ r₁)) (proj₁ (proj₂ (proj₂ r₁)))
                        (proj₁ (proj₂ (proj₂ (proj₂ r₁)))) (proj₂ (proj₂ (proj₂ (proj₂ r₁)))) (out₂ , sched₂ , st₂)
                    → Σ (After S ([] , sP , stP) (proj₁ r₁ ++ out₂ , sched₂ , st₂)) λ A
                        → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes stP) (EvalSt.nodes st₂) u op m m′ ks (mX ∷ [])
                          × PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes st₂) p q
                          × MergeAt {Γ = Γ} κ (EvalSt.nodes st₂) u mX
      explode-drain S cp ci fl r lX lv qz (finish-nil e) _ = ⊥-elim (t≢f (trans (sym (usable-self _)) e))
      explode-drain {sI = sI} {stI = stI} S {op = op} {mX = mX} cp ci fl r lX lv qz (finish-all-drain {outV = outV} {st₁ = st₁′} fd drain-spent) F₂ =
        let ci′ = sub-on (λ r∈ → r∈) (n≤1+n (nodeCt sI)) (proj₁ ci) , sub-ot (λ r∈ → r∈) (n≤1+n (nodeCt sI)) (proj₂ ci)
            (A₁ , W₁) = inner-over (mint-impl S) (proj₂ cp) ci′ (fl , r) lX (live-if-under _ _ lv) qz fd
            c₁ = fold-clear fd (sub-ot (λ r∈ → r∈) (n≤1+n (nodeCt sI)) (proj₂ ci)) refl
                   (sub-on (λ r∈ → r∈) (n≤1+n (nodeCt sI)) (proj₁ ci) , sub-ot (λ r∈ → r∈) (n≤1+n (nodeCt sI)) (proj₂ ci))
            (T , fl₂ , r₂ , x₂) = explode-tail (After.store A₁) {op = op} (proj₂ cp)
                                    (sub-on (λ r∈ → r∈) ≤-refl (proj₁ c₁) , sub-ot (λ r∈ → r∈) ≤-refl (proj₂ c₁))
                                    (proj₁ W₁) (proj₂ W₁) (false , lookup-set mX _ (EvalSt.nodes st₁′)) F₂
        in after-out (cong (_++ _) (sym (++-identityʳ outV))) (unmintI A₁ ⨾ T) , fl₂ , r₂ , x₂

      quiet-resume : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now ℓ ℓ′ u} {p : Path Γ ℓ u t} {G : Goal}
                       {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)} {es fin oI sI₁ stI₁ rI}
                   → QArm S now p G q es fin oI sI₁ stI₁ → Sound p sP stP → Sound q sI₁ stI₁ → foldPath⇓ now q es fin sI₁ stI₁ rI
                   → Σ (After S ([] , sP , stP) (oI ++ proj₁ rI , proj₂ rI)) λ A
                       → G (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI)))
      quiet-resume (qarm A r b e lv rb) sp si dq = let X = quiet-pass (After.store A) r b e sp si lv dq in A ⨾ proj₁ X , rb dq (proj₁ X) (proj₂ X)

      -- AN OUTER'S EMITS CARRYING NOTHING, HANDED THE FLATTENER: every
      -- element a bare echo, restamped, then the open end restamped too
      quiet-outer : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                      {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ n + ℓ} {h₃ : n + ℓ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                      {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {es fin rI}
                  → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) → Carries es [] → fin ≡ false
                  → Sound (thru-outer (flatOp op) m ↠[ h ] p) sP stP
                  → Sound (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q)) sI stI
                  → LiveFor es (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q)) (EvalSt.nodes stI)
                  → foldPath⇓ now (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q))
                      es fin sI stI rI
                  → Σ (After S ([] , sP , stP) rI) λ A
                      → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI)))
                          (thru-outer (flatOp op) m ↠[ h ] p)
                          (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q))
      quiet-outer {stP = stP} S {op = op} {Θ₀ = Θ₀} {ρ₀} {h₃ = h₃} w b refl sp si lv
                  (fold-step step-map (fold-step dW@(step-thru-outer W) (fold-step d₁ (fold-step step-map dq)))) =
        let si′ = drop-ot _ _ _ si
            sp′ = proj₂ (unthru sp)
            X  = quiet-walk S {op = op} {Θ₀ = Θ₀} {ρ₀} sp′ (unthru si′) w b
                   (live-for (λ x → x) (λ l → inj₂ (live-if-drop _ _ _ refl refl l)) lv) W
            c₁ = step-clear d₁ (unthru (step-kept _ dW si′))
            T  = quiet-tail (flat-echo (After.store (proj₁ X)) (proj₂ X) [] d₁) sp′ (tail-of c₁) (live-echo {π = Store.π (After.store (proj₁ X))} {NP = EvalSt.nodes stP} {h₃ = h₃} (proj₁ (proj₂ X)) d₁ (inj₁ refl)) dq
        in proj₁ X ⨾ proj₁ T , outerElem~ (proj₁ (proj₂ T)) (proj₂ (proj₂ T))

      -- THE OUTER'S WALK, every element a bare echo
      quiet-walk : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₁ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                     {h₂ : ℓ₁ ≤ n + ℓ} {h₃ : n + ℓ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {ns es rI}
                 → Sound p sP stP → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
                 → Walkedˣ ns op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                 → Carries {echoᵗ u} es []
                 → LiveFor es (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) (EvalSt.nodes stI)
                 → thruWalk⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now
                     (thruEvents (map (applyClo (Θ₀ , elemᵛ , ρ₀)) es)) sI stI rI
                 → Σ (After S ([] , sP , stP) rI) λ A
                     → Walkedˣ ns op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI)))
      quiet-walk S sp cI w [] _ walk-nil = after S (λ x → x) (λ x → x) [] (λ x → x) , w
      quiet-walk S {Θ₀ = Θ₀} {ρ₀} sp cI w (quiet e′ bq b) lv W = quiet-elem-step S sp cI w (elem-quiet {Θ = Θ₀} {ρ₀} e′ bq) b (live-cons lv) W

      quiet-elem-step : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₁ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                          {h₂ : ℓ₁ ≤ n + ℓ} {h₃ : n + ℓ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {ns z es rI}
                      → Sound p sP stP → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
                      → Walkedˣ ns op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                      → QuietElem {u} z → Carries {echoᵗ u} es []
                      → LiveIf (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) (EvalSt.nodes stI)
                      → thruWalk⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now
                          (thruEvents (z ∷ map (applyClo (Θ₀ , elemᵛ , ρ₀)) es)) sI stI rI
                      → Σ (After S ([] , sP , stP) rI) λ A
                          → Walkedˣ ns op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI)))
      quiet-elem-step {stP = stP} S sp cI w (quiet-elem bx) b l (walk-echo (fold-step d₁ (fold-step step-map dq)) W′) =
        let c₁ = step-clear d₁ cI
            R  = flat-echo S w (quiet _ bx []) d₁
            L₁ = live-echo-if {π = Store.π S} {NP = EvalSt.nodes stP} (proj₁ w) d₁ l
            E  = quiet-tail R sp (tail-of c₁) (inj₂ (restamp-unlive (live-if-under _ _ L₁))) dq
            X  = quiet-walk (After.store (proj₁ E)) sp (fold-clear dq (proj₂ (proj₁ (tail-of c₁))) refl c₁) (proj₂ E) b (inj₂ (echo-on R dq L₁)) W′
        in proj₁ E ⨾ proj₁ X , proj₂ X

      -- a bare echo, restamped: down the impl's tail alone
      quiet-tail : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now ℓ ℓ₄ u op m m′ ks}
                     {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {ns es fin oI sI₁ stI₁ r}
                 → Restamped S ns op m m′ ks p q [] es fin oI sI₁ stI₁ → Sound p sP stP → ClearI m′ ks q sI₁ stI₁
                 → LiveFor es q (EvalSt.nodes stI₁)
                 → foldPath⇓ now q es fin sI₁ stI₁ r
                 → Σ (After S ([] , sP , stP) (oI ++ proj₁ r , proj₂ r)) λ A
                     → Walkedˣ ns op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ r)))
      quiet-tail {stP = stP} {stI₁ = stI₁} {r = r} (restamped A (fl , rel) c e) sp cI lv dq =
        let X  = quiet-pass (After.store A) rel c e sp (proj₂ (proj₁ cI)) lv dq
            F  = flat-move (EvalSt.nodes stP) (EvalSt.nodes stI₁) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ r)))
                   (After.grows (proj₁ X)) (unmoved refl) (missed dq (proj₁ cI)) (missed dq (proj₂ cI , proj₂ (proj₁ cI))) fl
        in A ⨾ proj₁ X , F , proj₂ X

    -- THE OUTER'S END, AS THE ARM ITS TAIL RESUMES: the flattener's
    -- nodes are below the tail, so its fold leaves them where they were
    wrap-arm : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now lo lo′ ℓ ℓ₁ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                 {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ n + ℓ} {h₃ : n + ℓ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                 {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {oP sP′ stP′ oI sI′ stI′ fin r} {H : ℕ → Set}
             → (A : After S (oP , sP′ , stP′) (oI , sI′ , stI′))
             → Clear m p (proj₁ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′)))) (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
             → Wrapped (After.store A) [] op m m′ ks p q fin now r
             → (∀ {I} → H I → Out I oI × fin ≡ false)
             → Arm S now oP (proj₁ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                 (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                 p [] (proj₁ (thruWrap (flatOp op) m fin (sP′ , stP′)))
                 (λ π NP NI → PathRel κ π NP NI (thru-outer (flatOp op) m ↠[ h ] p)
                    (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q)))
                 H (oI ++ proj₁ r , proj₂ r)
    wrap-arm {op = op} {m = m} {sP′ = sP′} {stP′ = stP′} {fin = fin} {r = r} A cP (wrapped {stI₁ = stI₁} A′ (fl , rel) cI gq dq) g =
      arm (A ⨾∅ A′) rel [] (proj₂ (proj₁ cI)) gq (inj₁ refl) dq (λ {rP} dP B rel′ →
        let F  = flat-move (EvalSt.nodes (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))) (EvalSt.nodes stI₁)
                   (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ r)))
                   (After.grows B) (missed dP cP) (missed dq (proj₁ cI)) (missed dq (proj₂ cI , proj₂ (proj₁ cI))) fl
        in outerElem~ F rel′)
        λ h → proj₁ (g h) , inj₂ (wrap-false (proj₂ (g h)) , [])

    -- THE EXPLODED OUTER'S END, AS THE ARM ITS TAIL RESUMES: the
    -- flattener's nodes are below the tail, and the explode's merge is
    -- where the tail's fold left it
    explode-arm : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₅ ρ₅ Θ₁ ρ₁ Θ₂ ρ₂}
                    {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ n + ℓ} {h₅ : n + ℓ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                    {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)} {oP sP′ stP′ oI sI′ stI′ fin r} {H : ℕ → Set}
                → (A : After S (oP , sP′ , stP′) (oI , sI′ , stI′))
                → Clear m p (proj₁ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′)))) (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                → Wrapped (After.store A) (mX ∷ []) op m m′ ks p q fin now r
                → MergeAt {Γ = Γ} κ (EvalSt.nodes (proj₂ (proj₂ r))) u mX
                → (∀ {I} → H I → Out I oI × fin ≡ false)
                → Arm S now oP (proj₁ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                    (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                    p [] (proj₁ (thruWrap (flatOp op) m fin (sP′ , stP′)))
                    (λ π NP NI → PathRel κ π NP NI (thru-outer (flatOp op) m ↠[ h ] p)
                       (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                        (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                         (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                          (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q))))) H
                    (oI ++ proj₁ r , proj₂ r)
    explode-arm {op = op} {m = m} {sP′ = sP′} {stP′ = stP′} {fin = fin} {r = r} A cP (wrapped {stI₁ = stI₁} A′ (fl , rel) cI gq dq) x g =
      arm (A ⨾∅ A′) rel [] (proj₂ (proj₁ cI)) gq (inj₁ refl) dq (λ {rP} dP B rel′ →
        let F  = flat-move (EvalSt.nodes (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))) (EvalSt.nodes stI₁)
                   (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ r)))
                   (After.grows B) (missed dP cP) (missed dq (proj₁ cI)) (missed dq (proj₂ cI , proj₂ (proj₁ cI))) fl
        in outerExplode~ F x rel′)
        λ h → proj₁ (g h) , inj₂ (wrap-false (proj₂ (g h)) , [])
