------------------------------------------------------------------
-- THE PASS DOWN A PATH: one arm per `PathRel` constructor, and an
-- outer's elements walked, over an inner's arms
------------------------------------------------------------------
module Simulation.Pass.Path where

open import Data.Bool    using (true; false; if_then_else_)
open import Data.Fin     using (Fin; toℕ; _↑ʳ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty   using (⊥-elim)
open import Data.Unit    using (tt)
open import Data.List    using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; ++⁺) renaming (map to pw-map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to ++⁺ᵃ)
open import Data.Fin.Properties using (toℕ<n; toℕ-↑ˡ; toℕ-↑ʳ; ↑ʳ-injective) renaming (_≟_ to _≟ᶠ_)
open import Data.Nat     using (ℕ; suc; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂; [_,_])
open import Data.Vec     using (lookup)
open import Data.List.Properties using (++-identityʳ; map-id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Rx.Prim      using (valueᵖ; completeᵖ)
open import Rx.Exp       using (Ctx; Closed; Val; applyClo)
open import Rx.Evaluator using (Sched; EvalSt; Path; share-sink; _↠[_]_; map-f; thru-outer; echoᵗ; thruEvents; atSlot)
open import Rx.Evaluator.Domain using (flatOp; foldPath⇓; fold-root; fold-step; stepFrame⇓; step-map; step-thru-outer; thruWalk⇓;
  walk-nil; walk-echo; walk-cons; shareGo⇓; go-nil; go-cut; go-live; dispatchShare⇓; disp;
  shareWalk⇓; walk-end; walk-more; fold-sink; step-from-inner; react-false; react-alive; react-dead; innerFinish⇓;
  finish-all-drain; finish-switch-clear; finish-exhaust-clear; finish-nil)
open import SExp.Syntax  using (Kinds; plainᵏ; plainᵗ; emitᵗ; sharedᵏ)
open import SExp.Elaborate using (elemᵛ)
open import SExp.InstEmit.Decode using (decodeEmit; decodeEmits)
open import Batchable.Inst-Extract using (instExtract; emitValues)
open import Simulation.Stores using (Lifts; sharedEq; PathRel; root~; sink~; map~; scan~; takeWhile~; spentWhile~;
  outerElem~; outerExplode~; inner~; deferInner~; RowRel; read~; []; _∷_; partner-row;
  Store)
open import Simulation.After using (module Kept)
open import Simulation.Take using (module Takes)
open import Simulation.Scan using (module Scans)
open import Simulation.Arm using (Out; out-quiet; out-++; out-tail; Clear; ClearI; missed; unthru; step-clear; fold-clear; consume-clear; adv)
open import Simulation.Sweep using (t≢f)
open import Rx.Evaluator.Reducible.Support using (Sound; drop-ot; sub-ot; Agree; admit-ot; sink-sound)
open import Rx.Evaluator.Reducible.Rule-Kept using (step-kept; fold-kept)
open import Simulation.Pass.Inner using (module PassI)
open import Simulation.Pass.Quiet using (ShareSlot; admit-agrees; delivered; sink-intro; sink-inv; sink-ok; slotpair; tail-of)

module PassP {n} {Γ : Ctx n} (κ : Kinds n) where

  open PassI {Γ = Γ} κ public
  open Takes {Γ = Γ} κ using (module While)
  open Scans {Γ = Γ} κ using (module Cells)

  -- AN EMIT DELIVERED AT `I` PUTS ITS VALUES OUT AT `I`
  at-all : ∀ {A : Set} {i I : ℕ} (l : List A) → i ≡ I → All (λ y → proj₁ y ≡ I) (map (i ,_) l)
  at-all []      _  = []
  at-all (_ ∷ l) eq = eq ∷ at-all l eq

  del-values : ∀ {s I} (e′ : Val (plainᵏ Γ κ) (emitᵗ s)) → DelAt I e′ → All (λ y → proj₁ y ≡ I) (emitValues (decodeEmit e′))
  del-values (_ , _ , _ , inj₁ _) ()
  del-values (_ , _ , _ , inj₂ (inj₁ _)) eq = at-all _ eq
  del-values (_ , _ , _ , inj₂ (inj₂ _)) eq = at-all _ eq

  emits-out : ∀ {s I} (es : List (Val (plainᵏ Γ κ) (emitᵗ s))) → All (DelAt I) es
            → All (λ y → proj₁ y ≡ I) (instExtract (decodeEmits (map valueᵖ es)))
  emits-out []        []       = []
  emits-out (e′ ∷ es) (d ∷ ds) = ++⁺ᵃ (del-values e′ d) (emits-out es ds)

  -- SO A ROOT HANDED A GROUP DELIVERED AT `I`, AND NO END, SENDS AT `I`
  root-out : ∀ {s I} fin (es : List (Val (plainᵏ Γ κ) (emitᵗ s))) → Dlv I fin es
           → Out I ((map valueᵖ es ++ (if fin then completeᵖ ∷ [] else [])) ∷ [])
  root-out true  es (() , _)
  root-out {I = I} false es (_ , ds) =
    subst (λ z → All (λ y → proj₁ y ≡ I) (instExtract (decodeEmits z)))
      (sym (trans (++-identityʳ (map valueᵖ es ++ [])) (++-identityʳ (map valueᵖ es)))) (emits-out es ds)

  -- a lifted step keeps every delivery's stamp
  del-map : ∀ {s u} {G′ : Val (plainᵏ Γ κ) (emitᵗ s) → Val (plainᵏ Γ κ) (emitᵗ u)} {f : Val Γ s → Val Γ u}
          → Lifts κ s u G′ (map f) → ∀ {I es vs} → Carries es vs → All (DelAt I) es → All (DelAt I) (map G′ es)
  del-map L []             []       = []
  del-map {G′ = G′} L (quiet e′ r b) (d ∷ ds) = del-keep (G′ e′) e′ (proj₂ (L e′ [] r)) d ∷ del-map L b ds
  del-map {G′ = G′} L (one e′ {w = w} r b) (d ∷ ds) = del-keep (G′ e′) e′ (proj₂ (L e′ (w ∷ []) r)) d ∷ del-map L b ds

  -- nothing related to nothing
  nil-all : ∀ {A B : Set} {R : A → B → Set} {P : A → Set} {xs} → Pointwise R xs [] → All P xs
  nil-all [] = []

  module InP {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

    open InI {t} {ep} {ei} public
    open Kept {Γ = Γ} κ {t} {ep} {ei}
    open While {t} {ep} {ei} using (takeWhile-arm)
    open Cells {t} {ep} {ei} using (scan-arm)

    -- A RUN THE PLAIN SIDE SENDS NOTHING AGAINST sends nothing to read
    still-out : ∀ {sP stP sI stI} {S : St sP stP sI stI} {sP′ stP′ rI I} → After S ([] , sP′ , stP′) rI → Out I (proj₁ rI)
    still-out A = nil-all (After.values A)

    -- the deliveries of a stamped slot's emits, at the share's type
    DelU : ∀ {u u′} → u′ ≡ emitᵗ u → ℕ → List (Val (plainᵏ Γ κ) u′) → Set
    DelU refl I es = All (DelAt I) es

    del-cast : ∀ {u u′} (ε : u′ ≡ emitᵗ u) {I} {es : List (Val (plainᵏ Γ κ) (emitᵗ u))}
             → All (DelAt I) es → DelU ε I (map (subst (Val (plainᵏ Γ κ)) (sym ε)) es)
    del-cast refl {I} {es} ds = subst (All (DelAt I)) (sym (map-id es)) ds

    mutual
      path-pass : ∀ {lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)} → Pass p q
      path-pass S root~ b _ _ (fold-root {fin = fin}) fold-root =
        after S (λ x → x) (λ x → x) (root-values b fin) (λ x → x) , root~ , root-out fin _
      path-pass S r@(sink~ sh) b sp si dP dI = sink-pass sh S r b sp si dP dI
      path-pass S (map~ L r) b sp si (fold-step step-map dP) (fold-step step-map dI) =
        let X = path-pass S r (carries-map L b) (drop-ot _ _ _ sp) (drop-ot _ _ _ si) dP dI
        in proj₁ X , map~ L (proj₁ (proj₂ X)) , λ { (f , ds) → proj₂ (proj₂ X) (f , del-map L b ds) }
      path-pass S r@(scan~ _ _ _ _ _ _) b sp si (fold-step d dP) dI = resume (scan-arm S r b sp si d dI) (adv d sp) dP
      path-pass S r@(takeWhile~ _ _ _ _ _ _) b sp si (fold-step d dP) dI = resume (takeWhile-arm S r b sp si d dI) (adv d sp) dP
      path-pass S r@(spentWhile~ _ _ _ _) b sp si (fold-step d dP) dI = resume (takeWhile-arm S r b sp si d dI) (adv d sp) dP
      path-pass S (outerElem~ fl r) b sp si (fold-step d dP) dI = resume (outerElem-arm S (fl , r) b sp si d dI) (adv d sp) dP
      path-pass S (outerExplode~ fl r) b sp si (fold-step d dP) dI = resume (outerExplode-arm S (fl , r) b sp si d dI) (adv d sp) dP
      path-pass S r@(inner~ {op = op} refl _ _ _) b sp si (fold-step d@(step-from-inner react-false) dP) dI =
        resume (inner-pass {op = op} S r b sp si (inj₁ refl) dI) (adv d sp) dP
      path-pass S r@(inner~ {op = op} refl _ _ _) b sp si (fold-step d@(step-from-inner (react-alive al)) dP) dI =
        resume (inner-pass {op = op} S r b sp si (inj₂ al) dI) (adv d sp) dP
      path-pass S r@(inner~ {op = op} refl _ _ _) b sp si (fold-step d@(step-from-inner (react-dead dd F)) dP) dI =
        let X = resume (inner-dies {op = op} S r b sp si dd F (tail-at F) dI) (adv d sp) dP in proj₁ X , proj₁ (proj₂ X) , λ { (() , _) }
      path-pass S r@(deferInner~ _ _ _ _ _ _ _) b sp si (fold-step d@(step-from-inner react-false) dP) dI =
        resume (deferInner-pass S r b sp si (inj₁ refl) dI) (adv d sp) dP
      path-pass S r@(deferInner~ _ _ _ _ _ _ _) b sp si (fold-step d@(step-from-inner (react-alive al)) dP) dI =
        resume (deferInner-pass S r b sp si (inj₂ al) dI) (adv d sp) dP
      path-pass S r@(deferInner~ _ _ _ _ _ _ _) b sp si (fold-step d@(step-from-inner (react-dead dd F)) dP) dI =
        let X = resume (deferInner-dies S r b sp si dd F (tail-at F) dI) (adv d sp) dP in proj₁ X , proj₁ (proj₂ X) , λ { (() , _) }

      -- a merge's finish folds its tail: the pass recurses on that fold
      tail-at : ∀ {lo lo′ s op m j now vs sP mx r} {stP : EvalSt ep} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
                (F : innerFinish⇓ op m j p now vs sP stP mx r) → TailAt q F
      tail-at (finish-all-drain fP _) S r b sp si dq = let X = path-pass S r b sp si fP dq in proj₁ X , proj₁ (proj₂ X)
      tail-at (finish-switch-clear _) = tt
      tail-at finish-exhaust-clear    = tt
      tail-at (finish-nil _)          = tt

      resume : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now oP sP₁ stP₁ ℓ u} {p : Path Γ ℓ u t} {vs fin G H rP rI}
             → Arm S now oP sP₁ stP₁ p vs fin G H rI → Sound p sP₁ stP₁ → foldPath⇓ now p vs fin sP₁ stP₁ rP
             → Σ (After S (oP ++ proj₁ rP , proj₂ rP) rI) λ A
                 → G (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
                 × (∀ {I} → H I → Out I (proj₁ rI))
      resume (arm {oI = oI} {rI = rI} A r b si dI rb o) sp dP =
        let X = path-pass (After.store A) r b sp si dP dI
        in A ⨾ proj₁ X , rb dP (proj₁ X) (proj₁ (proj₂ X)) ,
           λ h → out-++ {Δ = plainᵏ Γ κ} {t = plainᵗ t} oI (proj₁ rI) (proj₁ (o h)) (out-tail {Δ = plainᵏ Γ κ} {t = plainᵗ t} {o = proj₁ rI} (proj₂ (o h)) (proj₂ (proj₂ X)))

      -- a slot's partnered reader, by the row the store pairs it with
      slot-pass : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n} {u u′ rid rid′}
                    {p : Path Γ (suc (toℕ i)) u t} {p′ : Path (plainᵏ Γ κ) (suc (toℕ (n ↑ʳ i))) u′ (emitᵗ t)}
                    {vs es} (εI : u′ ≡ emitᵗ u)
                → RowRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI)
                    (rid , atSlot i , (u , p)) (rid′ , atSlot (n ↑ʳ i) , (u′ , p′))
                → CarriesU εI es vs
                → Sound p sP stP → Sound p′ sI stI
                → ∀ {now fin rP rI} → foldPath⇓ now p vs fin sP stP rP → foldPath⇓ now p′ es fin sI stI rI
                → Σ (After S rP rI) λ _ → ∀ {I} → fin ≡ false → DelU εI I es → Out I (proj₁ rI)
      slot-pass S refl (read~ hk r refl) c sp si dP dI =
        let X = resume (read-arm S hk r c si dI) sp dP in proj₁ X , λ f ds → proj₂ (proj₂ X) (f , ds)

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
               → Σ (After S (oP , sP₁ , stP₁) (oI , sI₁ , stI₁)) λ _ → ∀ {I} → fin ≡ false → DelU εI I es → Out I oI
      share-go S εI c [] _ _ _ _ go-nil go-nil = after S (λ x → x) (λ x → x) [] (λ x → x) , λ _ _ → out-quiet [] refl
      share-go S εI c (slotpair (inj₁ _) ∷ ps) hP aP hI aI (go-cut _ g) (go-cut _ g′) =
        share-go S εI c ps (λ m → hP (there m)) (λ m m′ → aP (there m) (there m′)) (λ m → hI (there m)) (λ m m′ → aI (there m) (there m′)) g g′
      share-go S εI c (slotpair (inj₁ (x , _)) ∷ _) _ _ _ _ (go-live y _ _) _ = ⊥-elim (t≢f (trans (sym x) y))
      share-go S εI c (slotpair (inj₁ (_ , x)) ∷ _) _ _ _ _ (go-cut _ _) (go-live y _ _) = ⊥-elim (t≢f (trans (sym x) y))
      share-go S εI c (slotpair (inj₂ (x , _)) ∷ _) _ _ _ _ (go-cut y _) _ = ⊥-elim (t≢f (trans (sym y) x))
      share-go S εI c (slotpair (inj₂ (_ , x , _)) ∷ _) _ _ _ _ (go-live _ _ _) (go-cut y _) = ⊥-elim (t≢f (trans (sym y) x))
      share-go S {i = i} εI c (slotpair (inj₂ (_ , _ , pr)) ∷ ps) hP aP hI aI (go-live _ dP g) (go-live {emits = eI} _ dI g′) =
        rebase (A ⨾ proj₁ Y) , λ f ds → out-++ {Δ = plainᵏ Γ κ} {t = plainᵗ t} eI _ (proj₂ Z f ds) (proj₂ Y f ds)
        where
          sP₀ = sub-ot (λ r∈ → r∈) ≤-refl (hP (here refl))
          sI₀ = sub-ot (λ r∈ → r∈) ≤-refl (hI (here refl))
          Z = slot-pass (delivered S pr) εI (partner-row κ _ _ _ _ _ (Store.rows S) pr) c sP₀ sI₀ dP dI
          A = proj₁ Z
          Y = share-go (After.store A) εI c (share-keeps {S₀ = S} {S₁ = After.store A} {i = i} (After.keeps A) ps)
                (λ m → fold-kept dP sP₀ _ (sub-ot (λ r∈ → r∈) ≤-refl (hP (there m))) (aP (here refl) (there m)))
                (λ m m′ → aP (there m) (there m′))
                (λ m → fold-kept dI sI₀ _ (sub-ot (λ r∈ → r∈) ≤-refl (hI (there m))) (aI (here refl) (there m)))
                (λ m m′ → aI (there m) (there m′)) g g′

      -- A SHARE'S WALK ON BOTH SIDES, one emit at a time: a value every
      -- reader takes on both sides, an emit carrying none the impl's
      -- readers take alone, and the end over the share closed
      share-walk : ∀ {sP stP sI stI} (S : St sP stP sI stI) {lo lo′} {i : Fin n} {h : lo ≤ toℕ i} {h′ : lo′ ≤ toℕ (n ↑ʳ i)}
                     (sh : lookup κ i ≡ sharedᵏ) {now es vs fin rP rI}
                 → Carries es vs
                 → shareWalk⇓ now i vs fin sP stP rP
                 → shareWalk⇓ now (n ↑ʳ i) (map (slot-cast sh) es) fin sI stI rI
                 → Σ (After S rP rI) λ _ → ∀ {I} → Dlv I fin es → Out I (proj₁ rI)
      share-walk S sh [] walk-nil walk-nil = after S (λ x → x) (λ x → x) [] (λ x → x) , λ _ → out-quiet [] refl
      share-walk S {i = i} sh [] (walk-end gP) (walk-end gI) = D ⨾ proj₁ (fan (After.store D) (carries-cast ε []) gP gI) , λ { (() , _) }
        where
          ε = sharedEq {Γ = Γ} κ i sh
          D = share-spend S sh
          fan = λ S′ c → share-go S′ ε c (share-rows S′) (admit-ot i _ _ (Store.ruleP S′)) (admit-agrees i (Store.ruleP S′))
                           (admit-ot (n ↑ʳ i) _ _ (Store.ruleI S′)) (admit-agrees (n ↑ʳ i) (Store.ruleI S′))
      share-walk S {i = i} {h = h} {h′ = h′} sh (quiet x b c) wP (walk-more {emits = eI} gI wI) =
        Q ⨾ proj₁ Y , λ { (f , _ ∷ ds) → out-++ {Δ = plainᵏ Γ κ} {t = plainᵗ t} eI _ (still-out Q) (proj₂ Y (f , ds)) }
        where
          ε = sharedEq {Γ = Γ} κ i sh
          Q = after-out (++-identityʳ _)
                (proj₁ (quiet-sink {h = h} {h′ = h′} sh S (sink~ sh) (quiet x b []) refl (sink-sound i h (Store.ruleP S)) (sink-ok ε (Store.ruleI S))
                          (sink-intro ε (fold-sink (disp (walk-more gI walk-nil))))))
          Y = share-walk (After.store Q) {h = h} {h′ = h′} sh c wP wI
      share-walk S {i = i} {h = h} {h′ = h′} sh (one x r c) (walk-more gP wP) (walk-more {emits = eI} gI wI) =
        A ⨾ proj₁ Y , λ { (f , d ∷ ds) → out-++ {Δ = plainᵏ Γ κ} {t = plainᵗ t} eI _ (proj₂ Z refl (del-cast ε (d ∷ []))) (proj₂ Y (f , ds)) }
        where
          ε = sharedEq {Γ = Γ} κ i sh
          Z = share-go S ε (carries-cast ε (one x r [])) (share-rows S)
                (admit-ot i _ _ (Store.ruleP S)) (admit-agrees i (Store.ruleP S))
                (admit-ot (n ↑ʳ i) _ _ (Store.ruleI S)) (admit-agrees (n ↑ʳ i) (Store.ruleI S)) gP gI
          A = proj₁ Z
          Y = share-walk (After.store A) {h = h} {h′ = h′} sh c wP wI

      -- A SHARE'S DISPATCH: the walk, between the share marked dying and
      -- its readers dropped when the group ends it
      share-dispatch : ∀ {sP stP sI stI} (S : St sP stP sI stI) {lo lo′} {i : Fin n} {h : lo ≤ toℕ i} {h′ : lo′ ≤ toℕ (n ↑ʳ i)}
                         (sh : lookup κ i ≡ sharedᵏ) {now es vs fin rP rI}
                     → Carries es vs
                     → dispatchShare⇓ now i h vs fin sP stP rP
                     → dispatchShare⇓ now (n ↑ʳ i) h′ (map (slot-cast sh) es) fin sI stI rI
                     → Σ (After S rP rI) λ _ → ∀ {I} → Dlv I fin es → Out I (proj₁ rI)
      share-dispatch S {h = h} {h′ = h′} sh c (disp {fin = false} wP) (disp wI) = share-walk S {h = h} {h′ = h′} sh c wP wI
      share-dispatch S {i = i} {h = h} {h′ = h′} sh c (disp {fin = true} wP) (disp wI) =
        W ⨾∅ share-finish (After.store W) sh , λ { (() , _) }
        where
          D = dying-after S i sh
          W = D ⨾ proj₁ (share-walk (After.store D) {h = h} {h′ = h′} sh c wP wI)

      -- a share's subject, fanning the group out to every reader
      sink-pass : ∀ {lo lo′} {i : Fin n} {h : lo ≤ toℕ i} {h′ : lo′ ≤ toℕ (n ↑ʳ i)} (sh : lookup κ i ≡ sharedᵏ)
                → Pass (share-sink i h)
                       (subst (λ u → Path (plainᵏ Γ κ) lo′ u (emitᵗ t)) (sharedEq {Γ = Γ} κ i sh) (share-sink (n ↑ʳ i) h′))
      sink-pass {i = i} {h = h} {h′ = h′} sh S _ b _ _ (fold-sink dP) dI =
        let X = share-dispatch S {h = h} {h′ = h′} sh b dP (sink-inv (sharedEq {Γ = Γ} κ i sh) dI) in proj₁ X , sink~ sh , proj₂ X

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
                           (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q))) (λ I → Dlv {echoᵗ u} I fin es) rI
      outerElem-arm S {op = op} {Θ₀ = Θ₀} {ρ₀} {fin = fin} w b sp si dW@(step-thru-outer W) (fold-step step-map (fold-step dW′@(step-thru-outer W′) dR)) =
        let si′ = drop-ot _ _ _ si
            X   = elem-walk S {op = op} {Θ₀ = Θ₀} {ρ₀} (unthru sp) (unthru si′) w b W W′
        in wrap-arm (proj₁ X) (unthru (step-kept _ dW sp))
             (outer-wrap (After.store (proj₁ X)) {op = op} {fin = fin} (proj₂ X) (unthru (step-kept _ dW′ si′)) dR)
             λ { (f , ds) → elem-out S {op = op} {Θ₀ = Θ₀} {ρ₀} (unthru si′) w b W′ ds , f }

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
            E  = quiet-tail (flat-echo S w (quiet _ bx []) d₁) (proj₂ cP) (tail-of c₁) dq
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
            E  = quiet-tail (flat-echo S w (quiet _ r []) d₁) (proj₂ cP) (tail-of c₁) dq
            X  = elem-walk (After.store (proj₁ E)) cP (fold-clear dq (proj₂ (proj₁ (tail-of c₁))) refl c₁) (proj₂ E) b W W′
        in proj₁ E ⨾ proj₁ X , proj₂ X
      one-step S cP cI w (elem {w = inj₁ _} r (a-lane ob)) b (walk-cons c W) (walk-echo (fold-step d₁ (fold-step step-map dq)) (walk-cons c′ W′)) =
        let c₁ = step-clear d₁ cI
            E  = quiet-tail (flat-echo S w (quiet _ r []) d₁) (proj₂ cP) (tail-of c₁) dq
            c₂ = fold-clear dq (proj₂ (proj₁ (tail-of c₁))) refl c₁
            C  = consume-pair (After.store (proj₁ E)) (proj₂ E) ob cP c₂ c c′
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
            C   = consume-pair (After.store (proj₁ E)) (proj₂ E) ob cP₂ c₂ c c′
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
        in A ⨾ proj₁ X , F , proj₁ (proj₂ X)
