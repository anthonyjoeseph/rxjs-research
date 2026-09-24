------------------------------------------------------------------
-- EVERY RUN KEEPS THE RULE.  A run's new rows are its continuation
-- with frames pushed at nodes the counter hands out, or the path it was
-- walking with its floor lowered; a fan-out folds each admitted row
-- down its own path, which the registry already ties to its end; a cut
-- only removes rows; and nothing else a run writes is read by the rule.
-- So the rule is kept not only for the path being walked but for every
-- path that agrees with it where they meet, and that is the form that
-- carries through the induction: a row a run registers runs through the
-- walked path's nodes and the fresh ones, and a path the rule held for
-- before the run is below the counter, so it meets the row only where
-- it meets the walked path.
------------------------------------------------------------------

module Rx.Evaluator.Reducible.Rule-Kept where

open import Data.Bool using (Bool; true; false; T; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; toℕ)
open import Data.Maybe using (Maybe; nothing)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; suc; _≤_; _<_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; n≤1+n; <-≤-trans; <-irrefl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans)

open import Rx.Exp using (Ctx; Closed; Val; obs)
open import Rx.Evaluator using (Sched; EvalSt; Path; _↠[_]_; Frame; map-f; scan-f; take-f; batchSync-f; from-inner;
  thru-outer; NodeId; RegId; RegSrc; regFloor; register; lookupNode; frameNodes; pathHasNode;
  atSlot; atDyn; lowerFloor; mergeAllᵒ; mergeAll-st; AllOp; shareAdmit; shareDying;
  shareFinish; switchKill)
open import Rx.Mint using (freshId; setAt; regᵏ; sourceᵏ)
open import Rx.Evaluator.Freshness using (nodeCt)
open import Rx.Evaluator.Domain using (subscribeE⇓; subscribeInner⇓; thruConsume⇓; thruWalk⇓; mergeAllDrain⇓;
  innerFinish⇓; innerReact⇓; stepFrame⇓; subscribeAll⇓; subscribeSharedSlot⇓; foldPath⇓; dispatchShare⇓;
  shareWalk⇓; shareGo⇓;
  subs-floor; subs-shared; subs-hot-done; subs-hot-live; subs-cold-sync; subs-cold-async; subs-of; subs-empty;
  subs-take-zero; subs-take-suc; subs-batchSync; subs-map; subs-scan; subs-merge-all; subs-switch-all;
  subs-exhaust-all; subs-μ; subs-defer; subs-mint; inner; consume-all-sub; consume-all-enqueue; consume-all-nil;
  consume-switch-sub; consume-switch-nil; consume-exhaust-sub; consume-exhaust-nil; walk-nil; walk-cons;
  drain-spent; drain-nil; drain-no-room; drain-room; finish-all-drain; finish-switch-clear; finish-exhaust-clear;
  finish-nil; react-false; react-alive; react-dead; step-map; step-scan; step-take; step-batchSync;
  step-from-inner; step-thru-outer; sub-all; connect; slot-spent; slot-join; slot-connect; disp; walk-end;
  walk-more; go-nil; go-cut; go-live; fold-root; fold-sink; fold-step)
open import Rx.Evaluator.Reducible.Support using (Sound; sound; ruled; ends; fresh-path; distinct; termini; Agree; rowThrough; rowEnd;
  push-sound; Distinct; endOf; ∨-T; ∨-Tˡ; ∨-Tʳ; node-one; node-in₁; node-eq; node-cases;
  self-node; drop-ot; head-on; sub-ot; sink-sound; lower-nodes; lower-end; lower-distinct;
  register-sound; admit-row; admit-ot; admit-agree; kill-sub; switchKill-ct; wrap-ot;
  fresh-inner; fresh-sound; scanCt; scanReg; takeCt; takeReg; batchCt; batchReg)
open import Rx.Evaluator.Reducible.Floor using (drop-sub)

module _ {n} {Γ : Ctx n} {t} {e : Closed Γ t} where

  -- A RUN KEEPS THE RULE FOR EVERY PATH THAT AGREES WITH `π`: the
  -- invariant each member carries, at the path it walks.
  RuleKept : ∀ {lo s} → Path Γ lo s t → Sched Γ → EvalSt e → Sched Γ → EvalSt e → Set
  RuleKept π sched st sched′ st′ =
    ∀ {lo′ s′} (κ₂ : Path Γ lo′ s′ t) → Sound κ₂ sched st → Agree π κ₂ → Sound κ₂ sched′ st′

  -- A FLATTENER'S NODE STANDING ON THE PATH BELOW IT, as one path: its
  -- nodes are the flattener's and the path's, and it ends where the path
  -- does.  Every member walking a flattener's inners carries this.
  Thru : ∀ {lo u} → NodeId → Path Γ lo u t → Path Γ lo (obs u) t
  Thru {u = u} a κ = thru-outer {u = u} mergeAllᵒ a ↠[ ≤-refl ] κ

  -- a flattener's node is among its inner's exit frame's
  widen : ∀ {lo u} {a j k : ℕ} (κ : Path Γ lo u t)
        → T (any (_≡ᵇ k) (a ∷ []) ∨ pathHasNode k κ) → T (any (_≡ᵇ k) (a ∷ j ∷ []) ∨ pathHasNode k κ)
  widen {a = a} {j} {k} κ h =
    [ (λ h₁ → ∨-Tˡ {b = pathHasNode k κ} (node-in₁ {a} {k} (j ∷ []) (node-one {a} {k} h₁)))
    , ∨-Tʳ {a = any (_≡ᵇ k) (a ∷ j ∷ [])} ]′ (∨-T {a = any (_≡ᵇ k) (a ∷ [])} h)

  -- so the rule for an inner's exit path is the rule for its flattener's
  fi-thru : ∀ {lo ℓ u} {op : AllOp} {a inst : NodeId} {le : lo ≤ ℓ} {κ : Path Γ ℓ u t} {sched : Sched Γ} {st : EvalSt e}
          → Sound (from-inner {s = u} op a inst ↠[ le ] κ) sched st → Sound (Thru a κ) sched st
  fi-thru {a = a} {inst = inst} {κ = κ} (sound ru ea fp (ap , ds)) =
    sound ru (λ k h → ea k (widen {a = a} {inst} {k} κ h)) (λ k h → fp k (widen {a = a} {inst} {k} κ h))
             ((λ k h → ap k (node-in₁ {a} {k} (inst ∷ []) (node-one {a} {k} h))) , ds)

  fi-agree : ∀ {lo ℓ u lo′ s′} {op : AllOp} {a inst : NodeId} {le : lo ≤ ℓ} {κ : Path Γ ℓ u t} {κ₂ : Path Γ lo′ s′ t}
           → Agree (from-inner {s = u} op a inst ↠[ le ] κ) κ₂ → Agree (Thru a κ) κ₂
  fi-agree {a = a} {inst = inst} {κ = κ} ag k h h₂ = ag k (widen {a = a} {inst} {k} κ h) h₂

  -- and the outer frame's rule is the flattener's, whichever flattener
  outer-thru : ∀ {lo ℓ u} {op : AllOp} {a : NodeId} {le : lo ≤ ℓ} {κ : Path Γ ℓ u t} {sched : Sched Γ} {st : EvalSt e}
             → Sound (thru-outer {u = u} op a ↠[ le ] κ) sched st → Sound (Thru a κ) sched st
  outer-thru (sound ru ea fp ds) = sound ru ea fp ds

  -- A FRAME AT THE COUNTER MEETS NO PATH BELOW IT, so a path agreeing
  -- with the one below agrees with the pushed one
  fresh-agree : ∀ {s u lo ℓ lo′ s′} (f : Frame Γ s u) {le : lo ≤ ℓ} {κ : Path Γ ℓ u t} {κ₂ : Path Γ lo′ s′ t} {c : ℕ}
              → (∀ k → T (any (_≡ᵇ k) (frameNodes f)) → c ≡ k) → (∀ k → T (pathHasNode k κ₂) → k < c)
              → Agree κ κ₂ → Agree (f ↠[ le ] κ) κ₂
  fresh-agree f {κ = κ} one fp ag k h h₂ =
    [ (λ hf → ⊥-elim (<-irrefl (sym (one k hf)) (fp k h₂))) , (λ hκ → ag k hκ h₂) ]′
      (∨-T {a = any (_≡ᵇ k) (frameNodes f)} {b = pathHasNode k κ} h)

  -- and an inner's exit frame, whose instance is the counter, meets it
  -- only at the flattener's node
  inner-agree : ∀ {lo u lo′ s′} {op : AllOp} {a c : NodeId} {le : lo ≤ lo} {κ : Path Γ lo u t} {κ₂ : Path Γ lo′ s′ t}
              → (∀ k → T (pathHasNode k κ₂) → k < c)
              → Agree (Thru a κ) κ₂ → Agree (from-inner {s = u} op a c ↠[ le ] κ) κ₂
  inner-agree {a = a} {c} {κ = κ} fp ag k h h₂ =
    [ (λ hf → node-cases {x = a} {y = c} {k = k} hf
                (λ eq → ag k (∨-Tˡ {b = pathHasNode k κ} (subst (λ j → T (any (_≡ᵇ k) (j ∷ []))) (sym eq) (self-node k []))) h₂)
                (λ eq → ⊥-elim (<-irrefl (sym eq) (fp k h₂))))
    , (λ hκ → ag k (∨-Tʳ {a = any (_≡ᵇ k) (a ∷ [])} hκ) h₂) ]′
      (∨-T {a = any (_≡ᵇ k) (a ∷ c ∷ [])} {b = pathHasNode k κ} h)

  -- A ROW WHOSE PATH RUNS THROUGH `π`'S NODES AND ENDS WHERE `π` DOES
  -- keeps the rule for every path agreeing with `π`
  register-kept : ∀ {lo s u} {π : Path Γ lo s t} {sched sched′ : Sched Γ} {st : EvalSt e}
                    (rid : RegId) (rs : RegSrc Γ) (p : Path Γ (regFloor rs) u t)
                → nodeCt sched ≤ nodeCt sched′ → endOf p ≡ endOf π
                → (∀ k → T (pathHasNode k p) → T (pathHasNode k π)) → Distinct p
                → Sound π sched st → RuleKept π sched st sched′ (register rid rs p st)
  register-kept {π = π} {sched} {sched′} {st} rid rs p ct ee nk dp so κ₂ so₂ ag =
    sound (ruled (register-sound {κ = π} {sched′ = sched′} rid rs p ct ee (λ k h → inj₁ (nk k h)) (λ _ → dp) so))
          ea′ (λ k h → <-≤-trans (fresh-path so₂ k h) ct) (distinct so₂)
    where
    ea′ : ∀ k → T (pathHasNode k κ₂) → ∀ {r} → r ∈ EvalSt.registry (register rid rs p st)
        → T (rowThrough k r) → rowEnd r ≡ endOf κ₂
    ea′ k h₂ a th with ∈-++⁻ (EvalSt.registry st) a
    ... | inj₁ a′          = ends so₂ k h₂ a′ th
    ... | inj₂ (here refl) = trans ee (ag k (nk k th) h₂)

  -- a slot's row: the walked path with its floor lowered
  slot-kept : ∀ {lo} (i : Fin n) (below : toℕ i < lo) {κ : Path Γ lo (lookup Γ i) t} {sched sched′ : Sched Γ} {st : EvalSt e}
            → nodeCt sched ≤ nodeCt sched′ → Sound κ sched st
            → RuleKept κ sched st sched′ (register (freshId regᵏ (Sched.mint sched)) (atSlot i) (lowerFloor below κ) st)
  slot-kept i below {κ} {sched} ct so =
    register-kept (freshId regᵏ (Sched.mint sched)) (atSlot i) (lowerFloor below κ) ct (lower-end below κ)
      (λ k h → subst T (lower-nodes below κ k) h) (lower-distinct below κ (distinct so)) so

  -- an admitted row agrees with every path the rule holds for
  admit-agree₂ : ∀ (i : Fin n) {lo′ s′} {κ₂ : Path Γ lo′ s′ t} {sched : Sched Γ} {st : EvalSt e}
               → Sound κ₂ sched st → ∀ {a} → a ∈ shareAdmit i (EvalSt.registry st) → Agree (proj₂ a) κ₂
  admit-agree₂ i {st = st} so₂ a∈ k ha h₂ =
    let (r₀ , m , ek , ee) = admit-row i (EvalSt.registry st) a∈
    in trans (sym ee) (ends so₂ k h₂ m (subst T (sym (ek k)) ha))

  -- the switch's cut, the share's marks and its retirement only drop rows
  kill-ot : ∀ {lo s} {κ : Path Γ lo s t} (cur : Maybe NodeId) {sched sched₁ : Sched Γ} {st st₁ : EvalSt e}
          → switchKill {e = e} cur sched st ≡ (sched₁ , st₁) → Sound κ sched st → Sound κ sched₁ st₁
  kill-ot {κ = κ} cur {sched} {st = st} kl so =
    subst (λ p → Sound κ (proj₁ p) (proj₂ p)) kl
      (sub-ot (kill-sub cur sched st) (≤-reflexive (sym (switchKill-ct cur sched st))) so)

  dying-ot : ∀ {lo s} {κ : Path Γ lo s t} (i : Fin n) (fin : Bool) {sched : Sched Γ} {st : EvalSt e}
           → Sound κ sched st → Sound κ sched (shareDying i fin st)
  dying-ot i false so = so
  dying-ot i true  so = sub-ot (λ r∈ → r∈) ≤-refl so

  finish-ot : ∀ {lo s} {κ : Path Γ lo s t} (i : Fin n) (fin : Bool) r
            → Sound κ (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
            → Sound κ (proj₁ (proj₂ (shareFinish {e = e} i fin r))) (proj₂ (proj₂ (shareFinish i fin r)))
  finish-ot i false r                 so = so
  finish-ot i true  (emits , sc , st) so = sub-ot (drop-sub (toℕ i) (EvalSt.registry st)) ≤-refl so

  -- THE FOURTEEN-MEMBER INDUCTION, in the shape of the floor's: every
  -- clause matches a constructor and recurses on its sub-derivations.
  -- The connect is folded into the slot's member, as there.
  -- STRUCTURAL SCC: subscribeE-rule subscribeSharedSlot-rule subscribeAll-rule subscribeInner-rule stepFrame-rule thruWalk-rule thruConsume-rule innerReact-rule innerFinish-rule mergeAllDrain-rule foldPath-rule dispatchShare-rule shareWalk-rule shareGo-rule
  subscribeE-rule : ∀ {u lo} {b : Val Γ (obs u)} {κ : Path Γ lo u t} {now}
                      {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out}
                  → subscribeE⇓ {e = e} b κ now sched st (out , sched′ , st′)
                  → Sound κ sched st → RuleKept κ sched st sched′ st′

  subscribeSharedSlot-rule : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t} {below} {now}
                               {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out}
                           → subscribeSharedSlot⇓ {e = e} i d κ below now sched st (out , sched′ , st′)
                           → Sound κ sched st → RuleKept κ sched st sched′ st′

  subscribeAll-rule : ∀ {u lo} {op} {ns} {b : Val Γ (obs (obs u))} {κ : Path Γ lo u t} {now}
                        {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out}
                    → subscribeAll⇓ {e = e} op ns b κ now sched st (out , sched′ , st′)
                    → Sound κ sched st → RuleKept κ sched st sched′ st′

  subscribeInner-rule : ∀ {u lo} {op a} {κ : Path Γ lo u t} {now} {o : Val Γ (obs u)}
                          {sched sched′ : Sched Γ} {st st′ : EvalSt e} {inst out}
                      → subscribeInner⇓ {e = e} op a κ now o sched st (inst , out , sched′ , st′)
                      → Sound (Thru a κ) sched st → RuleKept (Thru a κ) sched st sched′ st′

  stepFrame-rule : ∀ {s u lo ℓ} {f : Frame Γ s u} (le : lo ≤ ℓ) {κ : Path Γ ℓ u t} {now vals fin}
                     {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out vals′ fin′}
                 → stepFrame⇓ {e = e} now f κ vals fin sched st (out , vals′ , fin′ , sched′ , st′)
                 → Sound (f ↠[ le ] κ) sched st → RuleKept (f ↠[ le ] κ) sched st sched′ st′

  thruWalk-rule : ∀ {u lo} {op a} {κ : Path Γ lo u t} {now} {vals : List (Val Γ (obs u))}
                    {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out}
                → thruWalk⇓ {e = e} op a κ now vals sched st (out , sched′ , st′)
                → Sound (Thru a κ) sched st → RuleKept (Thru a κ) sched st sched′ st′

  thruConsume-rule : ∀ {u lo} {op a} {κ : Path Γ lo u t} {now} {o : Val Γ (obs u)}
                       {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out}
                   → thruConsume⇓ {e = e} op a κ now o sched st (out , sched′ , st′)
                   → Sound (Thru a κ) sched st → RuleKept (Thru a κ) sched st sched′ st′

  innerReact-rule : ∀ {s lo} {op a inst} {κ : Path Γ lo s t} {now} {vals : List (Val Γ s)}
                      {sched sched′ : Sched Γ} {st st′ : EvalSt e} {alive} {out vals′ fin}
                  → innerReact⇓ {e = e} op a inst κ now vals sched st alive (out , vals′ , fin , sched′ , st′)
                  → Sound (Thru a κ) sched st → RuleKept (Thru a κ) sched st sched′ st′

  innerFinish-rule : ∀ {s lo} {op a inst} {κ : Path Γ lo s t} {now} {vals : List (Val Γ s)}
                       {sched sched′ : Sched Γ} {st st′ : EvalSt e} {m} {out vals′ fin}
                   → innerFinish⇓ {e = e} op a inst κ now vals sched st m (out , vals′ , fin , sched′ , st′)
                   → Sound (Thru a κ) sched st → RuleKept (Thru a κ) sched st sched′ st′

  mergeAllDrain-rule : ∀ {s lo} {a} {κ : Path Γ lo s t} {now} {fuel lim act od} {q : List (Val Γ (obs s))}
                         {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out act′} {q′ : List (Val Γ (obs s))}
                     → mergeAllDrain⇓ {e = e} a κ now fuel lim act od q sched st (out , act′ , q′ , sched′ , st′)
                     → Sound (Thru a κ) sched st → RuleKept (Thru a κ) sched st sched′ st′

  foldPath-rule : ∀ {u lo} {κ : Path Γ lo u t} {now vals fin}
                    {sched sched′ : Sched Γ} {st st′ : EvalSt e} {emits}
                → foldPath⇓ {e = e} now κ vals fin sched st (emits , sched′ , st′)
                → Sound κ sched st → RuleKept κ sched st sched′ st′

  -- the fan-out folds rows the registry holds, which agree with every
  -- path the rule holds for, so it keeps the rule for all of them
  dispatchShare-rule : ∀ {lo} {i : Fin n} {below} {now vals fin} {sched : Sched Γ} {st : EvalSt e} {r}
                     → dispatchShare⇓ {e = e} {lo = lo} now i below vals fin sched st r
                     → ∀ {lo′ s′} (κ₂ : Path Γ lo′ s′ t) → Sound κ₂ sched st
                     → Sound κ₂ (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

  shareWalk-rule : ∀ {i : Fin n} {now vals fin} {sched : Sched Γ} {st : EvalSt e} {r}
                 → shareWalk⇓ {e = e} now i vals fin sched st r
                 → ∀ {lo′ s′} (κ₂ : Path Γ lo′ s′ t) → Sound κ₂ sched st
                 → Sound κ₂ (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

  shareGo-rule : ∀ {lo} {i : Fin n} {now vals fin} {ps : List (RegId × Path Γ lo (lookup Γ i) t)}
                   {sched : Sched Γ} {st : EvalSt e} {r}
               → shareGo⇓ {e = e} {lo = lo} now i vals fin ps sched st r
               → (∀ {a} → a ∈ ps → Sound (proj₂ a) sched st)
               → (∀ {a b} → a ∈ ps → b ∈ ps → Agree (proj₂ a) (proj₂ b))
               → ∀ {lo′ s′} (κ₂ : Path Γ lo′ s′ t) → Sound κ₂ sched st → (∀ {a} → a ∈ ps → Agree (proj₂ a) κ₂)
               → Sound κ₂ (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

  subscribeE-rule (subs-floor _ f)        so = foldPath-rule f so
  subscribeE-rule (subs-shared _ slot)    so = subscribeSharedSlot-rule slot so
  subscribeE-rule (subs-hot-done _ _ _ f) so = foldPath-rule f so
  subscribeE-rule {κ = κ} (subs-hot-live {i = i} below _ _ refl) so = slot-kept i below ≤-refl so
  subscribeE-rule (subs-cold-sync _ _ f)  so = foldPath-rule f so
  subscribeE-rule {lo = lo} {κ = κ} {sched = sched} (subs-cold-async _ _ refl refl refl f) so κ₂ so₂ ag =
    foldPath-rule f (register-kept {π = κ} rid rs κ ≤-refl refl (λ k h → h) (distinct so) so κ so (λ _ _ _ → refl))
      κ₂ (register-kept {π = κ} rid rs κ ≤-refl refl (λ k h → h) (distinct so) so κ₂ so₂ ag) ag
    where
    rid = freshId regᵏ (Sched.mint sched)
    rs  = atDyn (freshId sourceᵏ (Sched.mint sched)) lo
  subscribeE-rule (subs-of f)             so = foldPath-rule f so
  subscribeE-rule (subs-empty f)          so = foldPath-rule f so
  subscribeE-rule (subs-take-zero _ f)    so = foldPath-rule f so
  subscribeE-rule {κ = κ} {sched = sched} (subs-take-suc _ refl sub) so κ₂ so₂ ag =
    subscribeE-rule sub (fresh-sound (take-f (nodeCt sched)) κ _ (λ k a → node-eq a) so) κ₂
      (sub-ot {κ = κ₂} (λ r∈ → r∈) (n≤1+n _) so₂)
      (fresh-agree (take-f (nodeCt sched)) {le = ≤-refl} {κ = κ} {κ₂ = κ₂} {c = nodeCt sched} (λ k a → node-eq a) (fresh-path so₂) ag)
  subscribeE-rule {κ = κ} {sched = sched} (subs-batchSync refl sub f) so κ₂ so₂ ag =
    foldPath-rule f (sub-ot (λ r∈ → r∈) ≤-refl (subscribeE-rule sub soπ _ soπ (λ _ _ _ → refl))) κ₂
      (sub-ot (λ r∈ → r∈) ≤-refl (subscribeE-rule sub soπ κ₂ (sub-ot (λ r∈ → r∈) (n≤1+n _) so₂) ag′)) ag′
    where
    soπ = fresh-sound (batchSync-f (nodeCt sched)) κ _ (λ k a → node-eq a) so
    ag′ = fresh-agree (batchSync-f (nodeCt sched)) {le = ≤-refl} {κ = κ} {κ₂ = κ₂} {c = nodeCt sched} (λ k a → node-eq a) (fresh-path so₂) ag
  subscribeE-rule {κ = κ} (subs-map sub)  so =
    subscribeE-rule sub (push-sound (map-f _) ≤-refl κ so (λ k ()))
  subscribeE-rule {κ = κ} {sched = sched} (subs-scan {Θ = Θ} {ρ = ρ} {f = fn} refl sub) so κ₂ so₂ ag =
    subscribeE-rule sub (fresh-sound (scan-f (Θ , fn , ρ) (nodeCt sched)) κ _ (λ k a → node-eq a) so) κ₂
      (sub-ot {κ = κ₂} (λ r∈ → r∈) (n≤1+n _) so₂)
      (fresh-agree (scan-f (Θ , fn , ρ) (nodeCt sched)) {le = ≤-refl} {κ = κ} {κ₂ = κ₂} {c = nodeCt sched} (λ k a → node-eq a) (fresh-path so₂) ag)
  subscribeE-rule (subs-merge-all sa)     so = subscribeAll-rule sa so
  subscribeE-rule (subs-switch-all sa)    so = subscribeAll-rule sa so
  subscribeE-rule (subs-exhaust-all sa)   so = subscribeAll-rule sa so
  subscribeE-rule (subs-μ sub)            so = subscribeE-rule sub so
  subscribeE-rule {u = u} {lo = lo} {κ = κ} {sched = sched} (subs-defer refl refl refl refl) so κ₂ so₂ ag =
    register-kept {π = π} (freshId regᵏ (Sched.mint sched)) (atDyn (freshId sourceᵏ (Sched.mint sched)) lo) π
      ≤-refl refl (λ k h → h) (distinct soπ) soπ κ₂ (sub-ot (λ r∈ → r∈) (n≤1+n _) so₂)
      (fresh-agree (thru-outer {u = u} mergeAllᵒ (nodeCt sched)) {le = ≤-refl} {κ = κ} {κ₂ = κ₂} {c = nodeCt sched} (λ k a → node-eq a) (fresh-path so₂) ag)
    where
    π   = thru-outer mergeAllᵒ (nodeCt sched) ↠[ ≤-refl ] κ
    soπ = fresh-sound (thru-outer mergeAllᵒ (nodeCt sched)) κ (mergeAll-st {t = u} nothing 0 [] false) (λ k a → node-eq a) so
  subscribeE-rule (subs-mint refl sub)    so κ₂ so₂ ag =
    subscribeE-rule sub (sub-ot (λ r∈ → r∈) ≤-refl so) κ₂ (sub-ot (λ r∈ → r∈) ≤-refl so₂) ag

  subscribeSharedSlot-rule (slot-spent _ f) so = foldPath-rule f so
  subscribeSharedSlot-rule {i = i} {below = below} (slot-join _ _ refl) so = slot-kept i below ≤-refl so
  subscribeSharedSlot-rule {i = i} {κ = κ} {below = below} {sched = sched} {st = st} (slot-connect _ _ (connect refl sub)) so κ₂ so₂ ag =
    subscribeE-rule sub (sink-sound i ≤-refl (ruled (slot-kept i below {κ = κ} {sched} {sched₁} {st₁} ≤-refl so₁ κ so₁ (λ _ _ _ → refl))))
      κ₂ (slot-kept i below {κ = κ} {sched} {sched₁} {st₁} ≤-refl so₁ κ₂ (sub-ot {κ = κ₂} {st′ = st₁} (λ r∈ → r∈) ≤-refl so₂) ag) (λ k ())
    where
    sched₁ : Sched Γ
    sched₁ = record sched { mint = setAt regᵏ (suc (freshId regᵏ (Sched.mint sched))) (Sched.mint sched) }
    st₁ : EvalSt e
    st₁ = record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }
    so₁ : Sound κ sched st₁
    so₁ = sub-ot {st′ = st₁} (λ r∈ → r∈) ≤-refl so

  subscribeAll-rule {u = u} {op = op} {κ = κ} {sched = sched} (sub-all refl sub) so κ₂ so₂ ag =
    subscribeE-rule sub (fresh-sound (thru-outer {u = u} op (nodeCt sched)) κ _ (λ k a → node-eq a) so) κ₂
      (sub-ot {κ = κ₂} (λ r∈ → r∈) (n≤1+n _) so₂)
      (fresh-agree (thru-outer {u = u} op (nodeCt sched)) {le = ≤-refl} {κ = κ} {κ₂ = κ₂} {c = nodeCt sched} (λ k a → node-eq a) (fresh-path so₂) ag)

  subscribeInner-rule {op = op} {a = a} {κ = κ} {sched = sched} (inner refl sub) so κ₂ so₂ ag =
    subscribeE-rule sub
      (fresh-inner op a κ sched (drop-ot (thru-outer mergeAllᵒ a) ≤-refl κ so)
        (head-on (thru-outer mergeAllᵒ a) ≤-refl κ a (self-node a []) so))
      κ₂ (sub-ot {κ = κ₂} (λ r∈ → r∈) (n≤1+n _) so₂)
      (inner-agree {op = op} {a = a} {c = nodeCt sched} {le = ≤-refl} {κ = κ} {κ₂ = κ₂} (fresh-path so₂) ag)

  stepFrame-rule le step-map so κ₂ so₂ ag = so₂
  stepFrame-rule le (step-scan {fn = fn} {nid = c} {vals = vals} {fin} {sched} {st}) so κ₂ so₂ ag =
    sub-ot (λ r∈ → subst (_ ∈_) (scanReg fn c vals fin sched st (lookupNode c (EvalSt.nodes st))) r∈)
           (≤-reflexive (sym (scanCt fn c vals fin sched st (lookupNode c (EvalSt.nodes st))))) so₂
  stepFrame-rule le (step-take {nid = c} {vals = vals} {fin} {sched} {st}) so κ₂ so₂ ag =
    sub-ot (takeReg c (lookupNode c (EvalSt.nodes st)) vals fin sched st)
           (≤-reflexive (sym (takeCt c (lookupNode c (EvalSt.nodes st)) vals fin sched st))) so₂
  stepFrame-rule le (step-batchSync {nid = c} {vals = vals} {fin} {sched} {st}) so κ₂ so₂ ag =
    sub-ot (λ r∈ → subst (_ ∈_) (batchReg c vals fin sched st (lookupNode c (EvalSt.nodes st))) r∈)
           (≤-reflexive (sym (batchCt c vals fin sched st (lookupNode c (EvalSt.nodes st))))) so₂
  stepFrame-rule le {κ = κ} (step-from-inner {op = op} {allNid = a} {inst = inst} r) so κ₂ so₂ ag =
    innerReact-rule r (fi-thru {op = op} {a = a} {inst = inst} {le = le} {κ = κ} so) κ₂ so₂
      (fi-agree {op = op} {a = a} {inst = inst} {le = le} {κ = κ} {κ₂ = κ₂} ag)
  stepFrame-rule le (step-thru-outer {op = op} {nid = c} {fin = fin} {sched′ = sched′} {st′ = st′} w) so κ₂ so₂ ag =
    wrap-ot op c fin sched′ st′ (thruWalk-rule w (outer-thru so) κ₂ so₂ ag)

  thruWalk-rule walk-nil        so κ₂ so₂ ag = so₂
  thruWalk-rule (walk-cons c w) so κ₂ so₂ ag =
    thruWalk-rule w (thruConsume-rule c so _ so (λ _ _ _ → refl)) κ₂ (thruConsume-rule c so κ₂ so₂ ag) ag

  thruConsume-rule (consume-all-sub _ _ c)  so κ₂ so₂ ag =
    subscribeInner-rule c (sub-ot (λ r∈ → r∈) ≤-refl so) κ₂ (sub-ot (λ r∈ → r∈) ≤-refl so₂) ag
  thruConsume-rule (consume-all-enqueue _ _) so κ₂ so₂ ag = sub-ot (λ r∈ → r∈) ≤-refl so₂
  thruConsume-rule (consume-all-nil _)       so κ₂ so₂ ag = so₂
  thruConsume-rule (consume-switch-sub {cur = cur} _ kl _ c) so κ₂ so₂ ag =
    subscribeInner-rule c (sub-ot (λ r∈ → r∈) ≤-refl (kill-ot cur kl so)) κ₂
      (sub-ot (λ r∈ → r∈) ≤-refl (kill-ot cur kl so₂)) ag
  thruConsume-rule (consume-switch-nil _)    so κ₂ so₂ ag = so₂
  thruConsume-rule (consume-exhaust-sub _ c) so κ₂ so₂ ag =
    subscribeInner-rule c (sub-ot (λ r∈ → r∈) ≤-refl so) κ₂ (sub-ot (λ r∈ → r∈) ≤-refl so₂) ag
  thruConsume-rule (consume-exhaust-nil _)   so κ₂ so₂ ag = so₂

  innerReact-rule react-false      so κ₂ so₂ ag = so₂
  innerReact-rule (react-alive _)  so κ₂ so₂ ag = so₂
  innerReact-rule (react-dead _ f) so κ₂ so₂ ag = innerFinish-rule f so κ₂ so₂ ag

  innerFinish-rule {a = a} {κ = κ} (finish-all-drain fp dr) so κ₂ so₂ ag =
    sub-ot {κ = κ₂} (λ r∈ → r∈) ≤-refl
      (mergeAllDrain-rule dr (foldPath-rule fp (drop-ot (thru-outer mergeAllᵒ a) ≤-refl κ so) (Thru a κ) so (λ _ _ _ → refl)) κ₂
        (foldPath-rule fp (drop-ot (thru-outer mergeAllᵒ a) ≤-refl κ so) κ₂ so₂
          (λ k h h₂ → ag k (∨-Tʳ {a = any (_≡ᵇ k) (a ∷ [])} h) h₂)) ag)
  innerFinish-rule (finish-switch-clear _) so κ₂ so₂ ag = sub-ot (λ r∈ → r∈) ≤-refl so₂
  innerFinish-rule finish-exhaust-clear    so κ₂ so₂ ag = sub-ot (λ r∈ → r∈) ≤-refl so₂
  innerFinish-rule (finish-nil _)          so κ₂ so₂ ag = so₂

  mergeAllDrain-rule drain-spent       so κ₂ so₂ ag = so₂
  mergeAllDrain-rule drain-nil         so κ₂ so₂ ag = so₂
  mergeAllDrain-rule (drain-no-room _) so κ₂ so₂ ag = so₂
  mergeAllDrain-rule {a = a} {κ = κ} (drain-room _ c _ dr) so κ₂ so₂ ag =
    mergeAllDrain-rule dr (subscribeInner-rule c (sub-ot (λ r∈ → r∈) ≤-refl so) (Thru a κ) (sub-ot (λ r∈ → r∈) ≤-refl so) (λ _ _ _ → refl))
      κ₂ (subscribeInner-rule c (sub-ot (λ r∈ → r∈) ≤-refl so) κ₂ (sub-ot {κ = κ₂} (λ r∈ → r∈) ≤-refl so₂) ag) ag

  foldPath-rule fold-root     so κ₂ so₂ ag = so₂
  foldPath-rule (fold-sink d) so κ₂ so₂ ag = dispatchShare-rule d κ₂ so₂
  foldPath-rule (fold-step {f = f} {le = le} {path′ = p′} sf r) so κ₂ so₂ ag =
    foldPath-rule r (drop-ot f le p′ (stepFrame-rule le sf so (f ↠[ le ] p′) so (λ _ _ _ → refl))) κ₂
      (stepFrame-rule le sf so κ₂ so₂ ag) (λ k h h₂ → ag k (∨-Tʳ {a = any (_≡ᵇ k) (frameNodes f)} h) h₂)

  dispatchShare-rule (disp {i = i} {fin = fin} w) κ₂ so₂ = finish-ot i fin _ (shareWalk-rule w κ₂ (dying-ot i fin so₂))

  shareWalk-rule walk-nil κ₂ so₂ = so₂
  shareWalk-rule {i = i} {sched = sched} {st = st} (walk-end g) κ₂ so₂ =
    shareGo-rule g (λ a∈ → sub-ot (λ r∈ → r∈) ≤-refl (admit-ot i sched st (ruled so₂) a∈))
      (admit-agree i st (termini (ruled so₂))) κ₂ (sub-ot (λ r∈ → r∈) ≤-refl so₂) (admit-agree₂ i so₂)
  shareWalk-rule {i = i} {sched = sched} {st = st} (walk-more g w) κ₂ so₂ =
    shareWalk-rule w κ₂
      (shareGo-rule g (admit-ot i sched st (ruled so₂)) (admit-agree i st (termini (ruled so₂))) κ₂ so₂ (admit-agree₂ i so₂))

  shareGo-rule go-nil       hs pa κ₂ so₂ ak = so₂
  shareGo-rule (go-cut _ g) hs pa κ₂ so₂ ak =
    shareGo-rule g (λ m → hs (there m)) (λ m m′ → pa (there m) (there m′)) κ₂ so₂ (λ m → ak (there m))
  shareGo-rule {ps = (rid , p) ∷ ps} (go-live _ f g) hs pa κ₂ so₂ ak =
    shareGo-rule g
      (λ {x} m → foldPath-rule f (sub-ot (λ r∈ → r∈) ≤-refl (hs (here refl))) (proj₂ x)
                   (sub-ot {κ = proj₂ x} (λ r∈ → r∈) ≤-refl (hs (there m))) (pa (here refl) (there m)))
      (λ m m′ → pa (there m) (there m′)) κ₂
      (foldPath-rule f (sub-ot (λ r∈ → r∈) ≤-refl (hs (here refl))) κ₂ (sub-ot {κ = κ₂} (λ r∈ → r∈) ≤-refl so₂) (ak (here refl)))
      (λ m → ak (there m))

-- THE THREE LEAVES THE CANDIDATE STANDS ON.
step-kept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo ℓ} {f : Frame Γ s u}
              (le : lo ≤ ℓ) {κ : Path Γ ℓ u t} {now vals fin sched st r}
          → stepFrame⇓ {e = e} now f κ vals fin sched st r
          → Sound (f ↠[ le ] κ) sched st
          → Sound (f ↠[ le ] κ) (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
step-kept le d so = stepFrame-rule le d so _ so (λ _ _ _ → refl)

subscribe-kept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {o : Val Γ (obs u)}
                   {κ : Path Γ lo u t} {now sched st r}
               → subscribeE⇓ {e = e} o κ now sched st r → Sound κ sched st
               → ∀ {lo′ s′} (κ₂ : Path Γ lo′ s′ t) → Sound κ₂ sched st → Agree κ κ₂
               → Sound κ₂ (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
subscribe-kept d so = subscribeE-rule d so

fold-kept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {κ : Path Γ lo u t}
              {now vals fin sched st r}
          → foldPath⇓ {e = e} now κ vals fin sched st r → Sound κ sched st
          → ∀ {lo′ s′} (κ₂ : Path Γ lo′ s′ t) → Sound κ₂ sched st → Agree κ κ₂
          → Sound κ₂ (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
fold-kept d so = foldPath-rule d so

-- a fold keeps the rule for its own path
fold-sound : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {κ : Path Γ lo u t}
               {now vals fin sched st r}
           → foldPath⇓ {e = e} now κ vals fin sched st r → Sound κ sched st
           → Sound κ (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
fold-sound {κ = κ} d so = fold-kept d so κ so (λ _ _ _ → refl)
