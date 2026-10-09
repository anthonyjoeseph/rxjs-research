------------------------------------------------------------------
-- THE PASS DOWN A PATH: one arm per `PathRel` constructor, and an
-- outer's elements walked, over an inner's arms
------------------------------------------------------------------
module Simulation.Pass.Path where

open import Data.Bool    using (true; false; if_then_else_; _∨_; _∧_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Bool.ListAction using (any)
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
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _<_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂; [_,_])
open import Data.Vec     using (lookup)
open import Data.List.Properties using (++-identityʳ; map-id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Rx.Prim      using (valueᵖ; completeᵖ)
open import Rx.Exp       using (Ctx; Closed; Val; applyClo)
open import Rx.Evaluator using (Sched; EvalSt; Path; share-sink; _↠[_]_; map-f; thru-outer; echoᵗ; thruEvents; atSlot; skipᵇ; markDlv; memberSource)
open import Decide using (≡ᵇ-refl)
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
open import Simulation.After using (skip-cut; module Kept)
open import Simulation.Take using (module Takes)
open import Simulation.Scan using (module Scans)
open import Simulation.Arm using (Out; out-quiet; out-++; out-tail; Clear; ClearI; missed; unthru; step-clear; fold-clear; consume-clear; adv; Gone)
open import Simulation.Sweep using (t≢f; same-refl)
open import Rx.Evaluator.Reducible.Support using (Sound; drop-ot; sub-ot; Agree; admit-ot; sink-sound)
open import Rx.Evaluator.Reducible.Rule-Kept using (step-kept; fold-kept)
open import Simulation.Pass.Inner using (module PassI)
open import Simulation.Walks using (module Walkers)
open import Simulation.Size using (sz-foldPath; sz-innerFinish; sz-shareGo; sz-shareWalk; sz-dispatchShare; sz-stepFrame; sz-thruWalk; sz-l; sz-r; sz-1)
open import Simulation.Pass.Quiet using (ShareSlot; admit-agrees; delivered; sink-intro; sink-inv; sink-ok; slotpair; tail-of)

module PassP {n} {Γ : Ctx n} (κ : Kinds n) where

  open PassI {Γ = Γ} κ public
  open Walkers {Γ = Γ} κ using (Walker)
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

    postulate
      -- A READER ITS SHARE HAS ENDED LEAVES NOTHING AT ITS HEAD: its own
      -- row is skipped, and no other row reaches the node it starts at.
      gone-skipped : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n} {u u′ rid rid′}
                       {p : Path Γ (suc (toℕ i)) u t} {p′ : Path (plainᵏ Γ κ) (suc (toℕ (n ↑ʳ i))) u′ (emitᵗ t)}
                   → RowRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI)
                       (rid , atSlot i , (u , p)) (rid′ , atSlot (n ↑ʳ i) , (u′ , p′))
                   → skipᵇ (toℕ (n ↑ʳ i)) rid′ stI ≡ true → Gone p′ stI

      -- A FOLD KEEPS A SHARE'S DYING MARK: only the share's own finish
      -- retires it, and that runs after its walk.
      dying-kept : ∀ {now lo s k} {p : Path (plainᵏ Γ κ) lo s (emitᵗ t)} {vs f sched} {st : EvalSt ei} {r}
                 → foldPath⇓ now p vs f sched st r
                 → memberSource k (EvalSt.dying st) ≡ true → memberSource k (EvalSt.dying (proj₂ (proj₂ r))) ≡ true

    -- and so does a fan-out, one reader's fold at a time
    go-dying : ∀ {lo now k} {i : Fin (n + n)} {vals fin chs sched} {st : EvalSt ei} {r}
             → shareGo⇓ {lo = lo} now i vals fin chs sched st r
             → memberSource k (EvalSt.dying st) ≡ true → memberSource k (EvalSt.dying (proj₂ (proj₂ r))) ≡ true
    go-dying go-nil d = d
    go-dying (go-cut _ g) d = go-dying g d
    go-dying (go-live _ f g) d = go-dying g (dying-kept f d)

    -- a row marked delivered while its source is dying is skipped
    skip-marked : ∀ {fin s rid} {st : EvalSt ei} → fin ≡ true → memberSource s (EvalSt.dying st) ≡ true
                → skipᵇ s rid (markDlv fin rid st) ≡ true
    skip-marked {rid = rid} {st} refl dy =
      trans (cong (λ b → any (_≡ᵇ rid) (EvalSt.cancelled st) ∨ (b ∧ ((rid ≡ᵇ rid) ∨ any (_≡ᵇ rid) (EvalSt.delivered st)))) dy)
        (trans (cong (λ b → any (_≡ᵇ rid) (EvalSt.cancelled st) ∨ (b ∨ any (_≡ᵇ rid) (EvalSt.delivered st))) (≡ᵇ-refl rid))
          (∨-zeroʳ (any (_≡ᵇ rid) (EvalSt.cancelled st))))

    mutual
      path-pass : ∀ {N} (wk : Walker ep ei N) {lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)} → Pass N p q
      path-pass _ S root~ b _ _ _ (fold-root {fin = fin}) fold-root _ =
        after S (λ x → x) (λ x → x) (root-values b fin) (λ x → x) , root~ , root-out fin _
      path-pass wk S r@(sink~ sh) b sp si g dP dI lt = sink-pass wk sh S r b sp si g dP dI lt
      path-pass wk S (map~ L r) b sp si g (fold-step step-map dP) (fold-step step-map dI) lt =
        let X = path-pass wk S r (carries-map L b) (drop-ot _ _ _ sp) (drop-ot _ _ _ si) g dP dI (sz-r lt)
        in proj₁ X , map~ L (proj₁ (proj₂ X)) , λ { (f , ds) → proj₂ (proj₂ X) (f , del-map L b ds) }
      path-pass wk S r@(scan~ _ _ _ _ _ _) b sp si g (fold-step d dP) dI lt = resume wk (scan-arm S r b sp si g d dI) (adv d sp) dP (sz-r lt)
      path-pass wk S r@(takeWhile~ _ _ _ _ _ _) b sp si g (fold-step d dP) dI lt = resume wk (takeWhile-arm S r b sp si g d dI) (adv d sp) dP (sz-r lt)
      path-pass wk S r@(spentWhile~ _ _ _ _) b sp si g (fold-step d dP) dI lt = resume wk (takeWhile-arm S r b sp si g d dI) (adv d sp) dP (sz-r lt)
      path-pass wk S (outerElem~ fl r) b sp si g (fold-step d dP) dI lt = resume wk (outerElem-arm wk S (fl , r) b sp si g d dI (sz-l lt)) (adv d sp) dP (sz-r lt)
      path-pass wk S (outerExplode~ fl x r) b sp si g (fold-step d dP) dI lt = resume wk (outerExplode-arm S (fl , x , r) b sp si g d dI) (adv d sp) dP (sz-r lt)
      path-pass wk S r@(inner~ {op = op} refl _ _ _) b sp si g (fold-step d@(step-from-inner react-false) dP) dI lt =
        resume wk (inner-pass {op = op} S r b sp si (inj₁ refl) dI) (adv d sp) dP (sz-r lt)
      path-pass wk S r@(inner~ {op = op} refl _ _ _) b sp si g (fold-step d@(step-from-inner (react-alive al)) dP) dI lt =
        resume wk (inner-pass {op = op} S r b sp si (inj₂ al) dI) (adv d sp) dP (sz-r lt)
      path-pass wk S r@(inner~ {op = op} refl _ _ _) b sp si g (fold-step d@(step-from-inner (react-dead dd F)) dP) dI lt =
        let X = resume wk (inner-dies wk {op = op} S r b sp si dd F (tail-at wk F (sz-1 (sz-1 (sz-l lt)))) dI (sz-1 (sz-1 (sz-l lt)))) (adv d sp) dP (sz-r lt) in proj₁ X , proj₁ (proj₂ X) , λ { (() , _) }
      path-pass wk S r@(deferInner~ _ _ _ _ _ _ _ _) b sp si g (fold-step d@(step-from-inner react-false) dP) dI lt =
        resume wk (deferInner-pass S r b sp si (inj₁ refl) dI) (adv d sp) dP (sz-r lt)
      path-pass wk S r@(deferInner~ _ _ _ _ _ _ _ _) b sp si g (fold-step d@(step-from-inner (react-alive al)) dP) dI lt =
        resume wk (deferInner-pass S r b sp si (inj₂ al) dI) (adv d sp) dP (sz-r lt)
      path-pass wk S r@(deferInner~ _ _ _ _ _ _ _ _) b sp si g (fold-step d@(step-from-inner (react-dead dd F)) dP) dI lt =
        let X = resume wk (deferInner-dies S r b sp si dd F (tail-at wk F (sz-1 (sz-1 (sz-l lt)))) dI) (adv d sp) dP (sz-r lt) in proj₁ X , proj₁ (proj₂ X) , λ { (() , _) }

      -- a merge's finish folds its tail: the pass recurses on that fold
      tail-at : ∀ {N} (wk : Walker ep ei N) {lo lo′ s op m j now vs sP mx r} {stP : EvalSt ep} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
                (F : innerFinish⇓ op m j p now vs sP stP mx r) → sz-innerFinish F < N → TailAt q F
      tail-at wk (finish-all-drain fP _) lt S r b sp si g dq = let X = path-pass wk S r b sp si g fP dq (sz-l lt) in proj₁ X , proj₁ (proj₂ X)
      tail-at _ (finish-switch-clear _) _ = tt
      tail-at _ finish-exhaust-clear    _ = tt
      tail-at _ (finish-nil _)          _ = tt

      resume : ∀ {N} (wk : Walker ep ei N) {sP stP sI stI} {S : St sP stP sI stI} {now oP sP₁ stP₁ ℓ u} {p : Path Γ ℓ u t} {vs fin G H rP rI}
             → Arm S now oP sP₁ stP₁ p vs fin G H rI → Sound p sP₁ stP₁ → (dP : foldPath⇓ now p vs fin sP₁ stP₁ rP)
             → sz-foldPath dP < N
             → Σ (After S (oP ++ proj₁ rP , proj₂ rP) rI) λ A
                 → G (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
                 × (∀ {I} → H I → Out I (proj₁ rI))
      resume wk (arm {oI = oI} {rI = rI} A r b si g dI rb o) sp dP lt =
        let X = path-pass wk (After.store A) r b sp si g dP dI lt
        in A ⨾ proj₁ X , rb dP (proj₁ X) (proj₁ (proj₂ X)) ,
           λ h → out-++ {Δ = plainᵏ Γ κ} {t = plainᵗ t} oI (proj₁ rI) (proj₁ (o h)) (out-tail {Δ = plainᵏ Γ κ} {t = plainᵗ t} {o = proj₁ rI} (proj₂ (o h)) (proj₂ (proj₂ X)))

      -- a slot's partnered reader, by the row the store pairs it with
      slot-pass : ∀ {N} (wk : Walker ep ei N) {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n} {u u′ rid rid′}
                    {p : Path Γ (suc (toℕ i)) u t} {p′ : Path (plainᵏ Γ κ) (suc (toℕ (n ↑ʳ i))) u′ (emitᵗ t)}
                    {vs es} (εI : u′ ≡ emitᵗ u)
                → RowRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI)
                    (rid , atSlot i , (u , p)) (rid′ , atSlot (n ↑ʳ i) , (u′ , p′))
                → CarriesU εI es vs
                → Sound p sP stP → Sound p′ sI stI
                → ∀ {now fin rP rI} → (dP : foldPath⇓ now p vs fin sP stP rP) → foldPath⇓ now p′ es fin sI stI rI
                → (fin ≡ true → skipᵇ (toℕ (n ↑ʳ i)) rid′ stI ≡ true)
                → sz-foldPath dP < N
                → Σ (After S rP rI) λ _ → ∀ {I} → fin ≡ false → DelU εI I es → Out I (proj₁ rI)
      slot-pass wk S refl rr@(read~ hk r refl) c sp si dP dI sk lt =
        let X = resume wk (read-arm S hk r c si (λ e → gone-skipped S rr (sk e)) dI) sp dP lt in proj₁ X , λ f ds → proj₂ (proj₂ X) (f , ds)

      -- A SHARE'S FAN-OUT ON BOTH SIDES, one partnered reader at a time,
      -- a cut one on both sides skipped
      share-go : ∀ {N} (wk : Walker ep ei N) {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n}
                   (εI : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (lookup Γ i)) {es now vs fin}
               → CarriesU εI es vs
               → (fin ≡ true → memberSource (toℕ (n ↑ʳ i)) (EvalSt.dying stI) ≡ true)
               → ∀ {chs adm}
               → Pointwise (ShareSlot (Store.rows S) (EvalSt.cancelled stP) (EvalSt.cancelled stI) i) chs adm
               → (∀ {x} → x ∈ chs → Sound (proj₂ x) sP stP)
               → (∀ {x y} → x ∈ chs → y ∈ chs → Agree (proj₂ x) (proj₂ y))
               → (∀ {x} → x ∈ adm → Sound (proj₂ x) sI stI)
               → (∀ {x y} → x ∈ adm → y ∈ adm → Agree (proj₂ x) (proj₂ y))
               → ∀ {oP sP₁ stP₁ oI sI₁ stI₁}
               → (g : shareGo⇓ now i vs fin chs sP stP (oP , sP₁ , stP₁))
               → shareGo⇓ now (n ↑ʳ i) es fin adm sI stI (oI , sI₁ , stI₁)
               → sz-shareGo g < N
               → Σ (After S (oP , sP₁ , stP₁) (oI , sI₁ , stI₁)) λ _ → ∀ {I} → fin ≡ false → DelU εI I es → Out I oI
      share-go _ S εI c _ [] _ _ _ _ go-nil go-nil _ = after S (λ x → x) (λ x → x) [] (λ x → x) , λ _ _ → out-quiet [] refl
      share-go wk S εI c dy (slotpair _ ∷ ps) hP aP hI aI (go-cut _ g) (go-cut _ g′) lt =
        share-go wk S εI c dy ps (λ m → hP (there m)) (λ m m′ → aP (there m) (there m′)) (λ m → hI (there m)) (λ m m′ → aI (there m) (there m′)) g g′ (sz-1 lt)
      share-go _ S εI c _ (slotpair q ∷ _) _ _ _ _ (go-cut y _) (go-live y′ _ _) _ = ⊥-elim (t≢f (trans (sym y) (trans (skip-alike S q) y′)))
      share-go _ S εI c _ (slotpair q ∷ _) _ _ _ _ (go-live y _ _) (go-cut y′ _) _ = ⊥-elim (t≢f (trans (sym y′) (trans (sym (skip-alike S q)) y)))
      share-go _ S εI c _ (slotpair (inj₁ (x , _)) ∷ _) _ _ _ _ (go-live {i = i₀} {rid = rid} {st₀ = st₀} y _ _) (go-live _ _ _) _ =
        ⊥-elim (t≢f (trans (sym (skip-cut {s = toℕ i₀} {rid} {st₀} x)) y))
      share-go wk S {i = i} εI {fin = fin} c dy (slotpair (inj₂ (_ , _ , pr)) ∷ ps) hP aP hI aI (go-live _ dP g) (go-live {emits = eI} _ dI g′) lt =
        rebase {fin = fin} (A ⨾ proj₁ Y) , λ f ds → out-++ {Δ = plainᵏ Γ κ} {t = plainᵗ t} eI _ (proj₂ Z f ds) (proj₂ Y f ds)
        where
          sP₀ = sub-ot (λ r∈ → r∈) ≤-refl (hP (here refl))
          sI₀ = sub-ot (λ r∈ → r∈) ≤-refl (hI (here refl))
          Z = slot-pass wk (delivered S {fin} pr) εI (partner-row κ _ _ _ _ _ (Store.rows S) pr) c sP₀ sI₀ dP dI (λ e → skip-marked e (dy e)) (sz-l lt)
          A = proj₁ Z
          Y = share-go wk (After.store A) εI c (λ e → dying-kept dI (dy e)) (share-keeps {S₀ = S} {S₁ = After.store A} {i = i} (After.keeps A) ps)
                (λ m → fold-kept dP sP₀ _ (sub-ot (λ r∈ → r∈) ≤-refl (hP (there m))) (aP (here refl) (there m)))
                (λ m m′ → aP (there m) (there m′))
                (λ m → fold-kept dI sI₀ _ (sub-ot (λ r∈ → r∈) ≤-refl (hI (there m))) (aI (here refl) (there m)))
                (λ m m′ → aI (there m) (there m′)) g g′ (sz-r lt)

      -- A SHARE'S WALK ON BOTH SIDES, one emit at a time: a value every
      -- reader takes on both sides, an emit carrying none the impl's
      -- readers take alone, and the end over the share closed
      share-walk : ∀ {N} (wk : Walker ep ei N) {sP stP sI stI} (S : St sP stP sI stI) {lo lo′} {i : Fin n} {h : lo ≤ toℕ i} {h′ : lo′ ≤ toℕ (n ↑ʳ i)}
                     (sh : lookup κ i ≡ sharedᵏ) {now es vs fin rP rI}
                 → Carries es vs
                 → (fin ≡ true → memberSource (toℕ (n ↑ʳ i)) (EvalSt.dying stI) ≡ true)
                 → (wP : shareWalk⇓ now i vs fin sP stP rP)
                 → shareWalk⇓ now (n ↑ʳ i) (map (slot-cast sh) es) fin sI stI rI
                 → sz-shareWalk wP < N
                 → Σ (After S rP rI) λ _ → ∀ {I} → Dlv I fin es → Out I (proj₁ rI)
      share-walk _ S sh [] _ walk-nil walk-nil _ = after S (λ x → x) (λ x → x) [] (λ x → x) , λ _ → out-quiet [] refl
      share-walk wk S {i = i} sh [] dy (walk-end gP) (walk-end gI) lt = D ⨾ proj₁ (fan (After.store D) (carries-cast ε []) gP gI (sz-1 lt)) , λ { (() , _) }
        where
          ε = sharedEq {Γ = Γ} κ i sh
          D = share-spend S sh
          fan = λ S′ c → share-go wk S′ ε c dy (share-rows S′) (admit-ot i _ _ (Store.ruleP S′)) (admit-agrees i (Store.ruleP S′))
                           (admit-ot (n ↑ʳ i) _ _ (Store.ruleI S′)) (admit-agrees (n ↑ʳ i) (Store.ruleI S′))
      share-walk wk S {i = i} {h = h} {h′ = h′} sh (quiet x b c) dy wP (walk-more {emits = eI} gI wI) lt =
        Q ⨾ proj₁ Y , λ { (f , _ ∷ ds) → out-++ {Δ = plainᵏ Γ κ} {t = plainᵗ t} eI _ (still-out Q) (proj₂ Y (f , ds)) }
        where
          ε = sharedEq {Γ = Γ} κ i sh
          Q = after-out (++-identityʳ _)
                (proj₁ (quiet-sink {h = h} {h′ = h′} sh S (sink~ sh) (quiet x b []) refl (sink-sound i h (Store.ruleP S)) (sink-ok ε (Store.ruleI S))
                          (sink-intro ε (fold-sink (disp (walk-more gI walk-nil))))))
          Y = share-walk wk (After.store Q) {h = h} {h′ = h′} sh c (λ e → go-dying gI (dy e)) wP wI lt
      share-walk wk S {i = i} {h = h} {h′ = h′} sh (one x r c) dy (walk-more gP wP) (walk-more {emits = eI} gI wI) lt =
        A ⨾ proj₁ Y , λ { (f , d ∷ ds) → out-++ {Δ = plainᵏ Γ κ} {t = plainᵗ t} eI _ (proj₂ Z refl (del-cast ε (d ∷ []))) (proj₂ Y (f , ds)) }
        where
          ε = sharedEq {Γ = Γ} κ i sh
          Z = share-go wk S ε (carries-cast ε (one x r [])) (λ ()) (share-rows S)
                (admit-ot i _ _ (Store.ruleP S)) (admit-agrees i (Store.ruleP S))
                (admit-ot (n ↑ʳ i) _ _ (Store.ruleI S)) (admit-agrees (n ↑ʳ i) (Store.ruleI S)) gP gI (sz-l lt)
          A = proj₁ Z
          Y = share-walk wk (After.store A) {h = h} {h′ = h′} sh c (λ e → go-dying gI (dy e)) wP wI (sz-r lt)

      -- A SHARE'S DISPATCH: the walk, between the share marked dying and
      -- its readers dropped when the group ends it
      share-dispatch : ∀ {N} (wk : Walker ep ei N) {sP stP sI stI} (S : St sP stP sI stI) {lo lo′} {i : Fin n} {h : lo ≤ toℕ i} {h′ : lo′ ≤ toℕ (n ↑ʳ i)}
                         (sh : lookup κ i ≡ sharedᵏ) {now es vs fin rP rI}
                     → Carries es vs
                     → (dP : dispatchShare⇓ now i h vs fin sP stP rP)
                     → dispatchShare⇓ now (n ↑ʳ i) h′ (map (slot-cast sh) es) fin sI stI rI
                     → sz-dispatchShare dP < N
                     → Σ (After S rP rI) λ _ → ∀ {I} → Dlv I fin es → Out I (proj₁ rI)
      share-dispatch wk S {h = h} {h′ = h′} sh c (disp {fin = false} wP) (disp wI) lt = share-walk wk S {h = h} {h′ = h′} sh c (λ ()) wP wI (sz-1 lt)
      share-dispatch wk {stI = stI} S {i = i} {h = h} {h′ = h′} sh c (disp {fin = true} wP) (disp wI) lt =
        W ⨾∅ share-finish (After.store W) sh , λ { (() , _) }
        where
          D = dying-after S i sh
          W = D ⨾ proj₁ (share-walk wk (After.store D) {h = h} {h′ = h′} sh c
                (λ _ → cong (λ b → b ∨ memberSource (toℕ (n ↑ʳ i)) (EvalSt.dying stI)) (same-refl (toℕ (n ↑ʳ i)))) wP wI (sz-1 lt))

      -- a share's subject, fanning the group out to every reader
      sink-pass : ∀ {N} (wk : Walker ep ei N) {lo lo′} {i : Fin n} {h : lo ≤ toℕ i} {h′ : lo′ ≤ toℕ (n ↑ʳ i)} (sh : lookup κ i ≡ sharedᵏ)
                → Pass N (share-sink i h)
                       (subst (λ u → Path (plainᵏ Γ κ) lo′ u (emitᵗ t)) (sharedEq {Γ = Γ} κ i sh) (share-sink (n ↑ʳ i) h′))
      sink-pass wk {i = i} {h = h} {h′ = h′} sh S _ b _ _ _ (fold-sink dP) dI lt =
        let X = share-dispatch wk S {h = h} {h′ = h′} sh b dP (sink-inv (sharedEq {Γ = Γ} κ i sh) dI) (sz-1 lt) in proj₁ X , sink~ sh , proj₂ X

      -- AN OUTER'S ELEMENT, ONE PER EMIT, HANDED THE FLATTENER: the
      -- walk, then the outer's end, then the tail resumed on the empty
      -- group.  Handed the flattener and the tails apart, since the frame's
      -- relation does not invert at a variable policy.
      outerElem-arm : ∀ {N} (wk : Walker ep ei N) {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                        {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ n + ℓ} {h₃ : n + ℓ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                        {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)}
                        {vs es fin oP vs₁ fin₁ sP₁ stP₁ rI}
                    → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) → Carries es vs
                    → Sound (thru-outer (flatOp op) m ↠[ h ] p) sP stP
                    → Sound (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q)) sI stI
                    → (fin ≡ true → Gone (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) stI)
                    → (dW : stepFrame⇓ now (thru-outer (flatOp op) m) p vs fin sP stP (oP , vs₁ , fin₁ , sP₁ , stP₁))
                    → foldPath⇓ now (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q))
                        es fin sI stI rI
                    → sz-stepFrame dW < N
                    → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                        (λ π NP NI → PathRel κ π NP NI (thru-outer (flatOp op) m ↠[ h ] p)
                           (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q))) (λ I → Dlv {echoᵗ u} I fin es) rI
      outerElem-arm wk S {op = op} {Θ₀ = Θ₀} {ρ₀} {h₂ = h₂} {fin = fin} w b sp si g dW@(step-thru-outer W) (fold-step step-map (fold-step dW′@(step-thru-outer W′) dR)) lt =
        let si′ = drop-ot _ _ _ si
            X   = elem-walk wk S {op = op} {Θ₀ = Θ₀} {ρ₀} (unthru sp) (unthru si′) w b W W′ (sz-1 lt)
        in wrap-arm (proj₁ X) (unthru (step-kept _ dW sp))
             (outer-wrap (After.store (proj₁ X)) {op = op} {fin = fin} (proj₂ X) (λ e → gone-walk S {h = h₂} W′ (g e)) (unthru (step-kept _ dW′ si′)) dR)
             λ { (f , ds) → elem-out S {op = op} {Θ₀ = Θ₀} {ρ₀} (unthru si′) w b W′ ds , f }

      -- THE OUTER'S WALK, an element at a time
      elem-walk : ∀ {N} (wk : Walker ep ei N) {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                    {h₃ : n + ℓ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {es vs rP rI}
                → Clear m p sP stP → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
                → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                → Carries {echoᵗ u} es vs
                → (W : thruWalk⇓ (flatOp op) m p now (thruEvents vs) sP stP rP)
                → thruWalk⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now
                    (thruEvents (map (applyClo (Θ₀ , elemᵛ , ρ₀)) es)) sI stI rI
                → sz-thruWalk W < N
                → Σ (After S rP rI) λ A
                    → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
      elem-walk _ S cP cI w [] walk-nil walk-nil _ = after S (λ x → x) (λ x → x) [] (λ x → x) , w
      elem-walk wk S {Θ₀ = Θ₀} {ρ₀} cP cI w (quiet e′ bq b) W W′ lt = quiet-step wk S cP cI w (elem-quiet {Θ = Θ₀} {ρ₀} e′ bq) b W W′ lt
      elem-walk wk S {Θ₀ = Θ₀} {ρ₀} cP cI w (one e′ r b) W W′ lt = one-step wk S cP cI w (elem-one {Θ = Θ₀} {ρ₀} e′ r) b W W′ lt

      -- an emit with no element: its bare echo, on the impl side alone
      quiet-step : ∀ {N} (wk : Walker ep ei N) {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                     {h₃ : n + ℓ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {z es vs rP rI}
                 → Clear m p sP stP → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
                 → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                 → QuietElem {u} z → Carries {echoᵗ u} es vs
                 → (W : thruWalk⇓ (flatOp op) m p now (thruEvents vs) sP stP rP)
                 → thruWalk⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now
                     (thruEvents (z ∷ map (applyClo (Θ₀ , elemᵛ , ρ₀)) es)) sI stI rI
                 → sz-thruWalk W < N
                 → Σ (After S rP rI) λ A
                     → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
      quiet-step wk S cP cI w (quiet-elem bx) b W (walk-echo (fold-step d₁ (fold-step step-map dq)) W′) lt =
        let c₁ = step-clear d₁ cI
            E  = quiet-tail (flat-echo S w (quiet _ bx []) d₁) (proj₂ cP) (tail-of c₁) dq
            X  = elem-walk wk (After.store (proj₁ E)) cP (fold-clear dq (proj₂ (proj₁ (tail-of c₁))) refl c₁) (proj₂ E) b W W′ lt
        in proj₁ E ⨾ proj₁ X , proj₂ X

      -- an emit with one element: its echo, then its lane
      one-step : ∀ {N} (wk : Walker ep ei N) {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                   {h₃ : n + ℓ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {w z es vs rP rI}
               → Clear m p sP stP → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
               → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
               → Elem {u} w z → Carries {echoᵗ u} es vs
               → (W : thruWalk⇓ (flatOp op) m p now (thruEvents (w ∷ vs)) sP stP rP)
               → thruWalk⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now
                   (thruEvents (z ∷ map (applyClo (Θ₀ , elemᵛ , ρ₀)) es)) sI stI rI
               → sz-thruWalk W < N
               → Σ (After S rP rI) λ A
                   → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
      one-step wk S cP cI w (elem {w = inj₁ _} r no-lane) b W (walk-echo (fold-step d₁ (fold-step step-map dq)) W′) lt =
        let c₁ = step-clear d₁ cI
            E  = quiet-tail (flat-echo S w (quiet _ r []) d₁) (proj₂ cP) (tail-of c₁) dq
            X  = elem-walk wk (After.store (proj₁ E)) cP (fold-clear dq (proj₂ (proj₁ (tail-of c₁))) refl c₁) (proj₂ E) b W W′ lt
        in proj₁ E ⨾ proj₁ X , proj₂ X
      one-step wk S cP cI w (elem {w = inj₁ _} r (a-lane ob)) b (walk-cons c W) (walk-echo (fold-step d₁ (fold-step step-map dq)) (walk-cons c′ W′)) lt =
        let c₁ = step-clear d₁ cI
            E  = quiet-tail (flat-echo S w (quiet _ r []) d₁) (proj₂ cP) (tail-of c₁) dq
            c₂ = fold-clear dq (proj₂ (proj₁ (tail-of c₁))) refl c₁
            C  = consume-pair wk (After.store (proj₁ E)) (proj₂ E) ob cP c₂ c c′ (sz-l lt)
            X  = elem-walk wk (After.store (proj₁ C)) (consume-clear c cP)
                   (consume-clear c′ c₂) (proj₂ C) b W W′ (sz-r lt)
        in proj₁ E ⨾ (proj₁ C ⨾ proj₁ X) , proj₂ X
      one-step wk S cP cI w (elem {w = inj₂ _} r no-lane) b (walk-echo dv W) (walk-echo (fold-step d₁ (fold-step step-map dq)) W′) lt =
        let c₁ = step-clear d₁ cI
            E  = echo-go wk dv cP (flat-echo S w (one _ r []) d₁) (tail-of c₁) dq (sz-l lt)
            X  = elem-walk wk (After.store (proj₁ E)) (fold-clear dv (proj₂ cP) refl cP)
                   (fold-clear dq (proj₂ (proj₁ (tail-of c₁))) refl c₁) (proj₂ E) b W W′ (sz-r lt)
        in proj₁ E ⨾ proj₁ X , proj₂ X
      one-step wk S cP cI w (elem {w = inj₂ _} r (a-lane ob)) b (walk-echo dv (walk-cons c W)) (walk-echo (fold-step d₁ (fold-step step-map dq)) (walk-cons c′ W′)) lt =
        let c₁  = step-clear d₁ cI
            E   = echo-go wk dv cP (flat-echo S w (one _ r []) d₁) (tail-of c₁) dq (sz-l lt)
            cP₂ = fold-clear dv (proj₂ cP) refl cP
            c₂  = fold-clear dq (proj₂ (proj₁ (tail-of c₁))) refl c₁
            C   = consume-pair wk (After.store (proj₁ E)) (proj₂ E) ob cP₂ c₂ c c′ (sz-l (sz-r lt))
            X   = elem-walk wk (After.store (proj₁ C)) (consume-clear c cP₂)
                    (consume-clear c′ c₂) (proj₂ C) b W W′ (sz-r (sz-r lt))
        in proj₁ E ⨾ (proj₁ C ⨾ proj₁ X) , proj₂ X

      -- a valued echo, restamped: down both tails
      echo-go : ∀ {N} (wk : Walker ep ei N) {sP stP sI stI} {S : St sP stP sI stI} {now ℓ ℓ₄ u op m m′ ks}
                  {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {v rP es fin oI sI₁ stI₁ r}
              → (dv : foldPath⇓ now p (v ∷ []) false sP stP rP) → Clear m p sP stP
              → Restamped S op m m′ ks p q (v ∷ []) es fin oI sI₁ stI₁ → ClearI m′ ks q sI₁ stI₁ → foldPath⇓ now q es fin sI₁ stI₁ r
              → sz-foldPath dv < N
              → Σ (After S rP (oI ++ proj₁ r , proj₂ r)) λ A
                  → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ r)))
      echo-go wk {stP = stP} {rP = rP} {stI₁ = stI₁} {r = r} dv cP (restamped A (fl , rel) c refl) cI dq lt =
        let X  = path-pass wk (After.store A) rel c (proj₂ cP) (proj₂ (proj₁ cI)) (λ ()) dv dq lt
            F  = flat-move (EvalSt.nodes stP) (EvalSt.nodes stI₁) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ r)))
                   (After.grows (proj₁ X)) (missed dv cP) (missed dq (proj₁ cI)) (missed dq (proj₂ cI , proj₂ (proj₁ cI))) fl
        in A ⨾ proj₁ X , F , proj₁ (proj₂ X)
