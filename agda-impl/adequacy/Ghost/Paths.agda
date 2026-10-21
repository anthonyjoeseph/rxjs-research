{-# OPTIONS --guardedness #-}

module adequacy.Ghost.Paths where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Nat.Properties using (≤-refl; m<m+n)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map) renaming (lookup to lookupᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.List.Relation.Unary.Linked using (_∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (Lift; lift)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Nat using (ℕ; suc; _<_; _+_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import denotation.MonotonicList.Events using (Events∞; Pos; Timeline; _<ᵖ_; <ᵖ-trans; <ᵖ-apart)
import denotation.Unfold as U
open import denotation.MonotonicList.Events using () renaming (sub to subᴾ)
open import adequacy.Sorted using (_≤ᵖ_; Under)
open import adequacy.Sorted.Walk using (module SortingWalk)
open import operation.Machine using (module Machine)
open import adequacy.Strong using (module Strongly)
open import adequacy.Strong.Against using (module StrongAgainst)
open import adequacy.Strong.Held using (module StrongHeld)
open import adequacy.Moves using (module Moving)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Sane using (Sane)
open import adequacy.Deep using (Deep)
open import adequacy.Placed.Order using (Placed)
open import denotation.Denote using (⟦_⟧)
import Tree as T
open import operation.PureObservable using (Out; Pureᴾ; module Pure)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Bool.Properties using (∨-zeroʳ)
open import adequacy.Ghost using (module Ghosting)
open Events∞

module GhostingPaths (R : Set) where
  open Machine R using (Mach; Step; silent; value; complete; drained; step; begin; Read)
  open Shared Timeline (Out R) using (Conf; Heapᴹ; Stack; run)
  open Heap using (World; _⊑_)
  open SortingWalk R using (WellMach; WellStep; silentʷ; valueʷ; preserve; Beyond)
  open Run (Pureᴾ R) using (Act; Observer; _>>ᴬ_; Subject; module Kit; module FlatKit)
  open Strongly R using (Sub; ofˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ; deferˢ; Lane; lane; here; module At; Path; done≗; Call; taking; PathLanes; this-lane; next-lane; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; _⊕_; _⊕ᴸ_; Here; walk; walkLanes; top; _≗_; outers; outers-⊕; ≗-refl) renaming (⟦_⟧ to ⟦_⟧ᶜ)
  open StrongAgainst R using (Books; Queue; Kernels; Meaning; Owned; Each; Lingers; seen; seenL; isTaking; seen-up; seen-join; ∧-split; ∧-join)
  open StrongHeld R using (Strong; strong-begin; Carried; carried; closing; Heads; DoneBy; Untold; Ended)
  open StrongAgainst.Against R using (calmAs; noteAs; runAs; subAs; burstAs; bottomAs; restAs; backAs; reholdAs; StackAs; CtlAs; agenda; bursts; begins) renaming (Placed to Placedᴬ)
  open Pure R using (End; finished; dry; cutOff)
  open Moving R using (pend; takes)
  open Unsubbing R using (_⇝_; now; then; ⇝-trans)
  open Read
  open Ghosting R using (Hopped; Lefts; LeftsL; Lifts; LiftsLane; Load; _≼_; lifts-body; lifts-defer; lifts-here; lifts-lanes; lifts-map; lifts-next; lifts-outer; lifts-scan; lifts-shut; lifts-source; lifts-take; lifts-this; load; loadOf; sorted-⇝; ≼-trans)

  -- Lifting along two paths is lifting along each.
  mutual
    lifts-split : ∀ {h} {H : Heapᴹ h} {Δ A Δ′ A′ Δ″ A″} {t : Sub h Δ A} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (ρ : Path t u) (τ : Path u v) {s S}
                → Lifts H (ρ ⊕ τ) s S → Σ (U.Step Δ′ A′) λ S′ → Lifts H τ s S′ × Lifts H ρ S′ S
    lifts-split here          τ L                          = _ , L , lifts-here
    lifts-split (in-map ρ)    τ (lifts-map L)              with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-map Lρ
    lifts-split (in-scan ρ)   τ (lifts-scan L)             with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-scan Lρ
    lifts-split (in-take ρ)   τ (lifts-take lv L)          with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-take lv Lρ
    lifts-split (in-outer ρ)  τ (lifts-outer of pb L)      with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-outer of pb Lρ
    lifts-split (in-lanes πL) τ (lifts-lanes L ea lf pb)   with liftsL-split πL τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-lanes Lρ ea lf pb
    lifts-split (in-source ρ) τ (lifts-source pb sf L)     with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-source pb sf Lρ
    lifts-split (in-body ρ)   τ (lifts-body pt bf L)       with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-body pt bf Lρ
    lifts-split (in-body ρ)   τ (lifts-shut pt e rb L)     with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-shut pt e rb Lρ
    lifts-split (in-defer ρ)  τ (lifts-defer L)            with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-defer Lρ

    liftsL-split : ∀ {h} {H : Heapᴹ h} {Δ B Δ′ A′ Δ″ A″} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″}
                   (πL : PathLanes ls u) (τ : Path u v) {s bs S as}
                 → LiftsLane H (πL ⊕ᴸ τ) s bs S as → Σ (U.Step Δ′ A′) λ S′ → Lifts H τ s S′ × LiftsLane H πL S′ bs S as
    liftsL-split (this-lane ρ)  τ (lifts-this lv L) with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-this lv Lρ
    liftsL-split (next-lane πL) τ (lifts-next L)    with liftsL-split πL τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-next Lρ

  -- What a lift leaves free, each half of it leaves free.
  mutual
    lefts-split : ∀ {h} {H : Heapᴹ h} {Δ A Δ′ A′ Δ″ A″} {t : Sub h Δ A} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (ρ : Path t u) (τ : Path u v) {s S}
                  (L : Lifts H (ρ ⊕ τ) s S) → Lefts H L
                → Lefts H (proj₁ (proj₂ (lifts-split ρ τ L))) × Lefts H (proj₂ (proj₂ (lifts-split ρ τ L)))
    lefts-split here          τ L                          lt        = lt , lift tt
    lefts-split (in-map ρ)    τ (lifts-map L)              lt        with lifts-split ρ τ L | lefts-split ρ τ L lt
    ... | _ , _ , _ | lτ , lρ = lτ , lρ
    lefts-split (in-scan ρ)   τ (lifts-scan L)             lt        with lifts-split ρ τ L | lefts-split ρ τ L lt
    ... | _ , _ , _ | lτ , lρ = lτ , lρ
    lefts-split (in-take ρ)   τ (lifts-take lv L)          lt        with lifts-split ρ τ L | lefts-split ρ τ L lt
    ... | _ , _ , _ | lτ , lρ = lτ , lρ
    lefts-split (in-outer ρ)  τ (lifts-outer of pb L)      (lo , lt) with lifts-split ρ τ L | lefts-split ρ τ L lt
    ... | _ , _ , _ | lτ , lρ = lτ , (lo , lρ)
    lefts-split (in-lanes πL) τ (lifts-lanes {l = l} L ea lf pb) lt  with liftsL-split πL τ L | leftsL-split πL τ {l = l} L lt
    ... | _ , _ , _ | lτ , lρ = lτ , lρ
    lefts-split (in-source ρ) τ (lifts-source pb sf L)     (lc , lt) with lifts-split ρ τ L | lefts-split ρ τ L lt
    ... | _ , _ , _ | lτ , lρ = lτ , (lc , lρ)
    lefts-split (in-body ρ)   τ (lifts-body pt bf L)       lt        with lifts-split ρ τ L | lefts-split ρ τ L lt
    ... | _ , _ , _ | lτ , lρ = lτ , lρ
    lefts-split (in-body ρ)   τ (lifts-shut pt e rb L)     lt        with lifts-split ρ τ L | lefts-split ρ τ L lt
    ... | _ , _ , _ | lτ , lρ = lτ , lρ
    lefts-split (in-defer ρ)  τ (lifts-defer L)            lt        with lifts-split ρ τ L | lefts-split ρ τ L lt
    ... | _ , _ , _ | lτ , lρ = lτ , lρ

    leftsL-split : ∀ {h} {H : Heapᴹ h} {Δ B Δ′ A′ Δ″ A″} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″}
                   (πL : PathLanes ls u) (τ : Path u v) {s bs S as l} (L : LiftsLane H (πL ⊕ᴸ τ) s bs S as) → LeftsL H l L
                 → Lefts H (proj₁ (proj₂ (liftsL-split πL τ L))) × LeftsL H l (proj₂ (proj₂ (liftsL-split πL τ L)))
    leftsL-split (this-lane ρ)  τ (lifts-this lv L) (ll , lt) with lifts-split ρ τ L | lefts-split ρ τ L lt
    ... | _ , _ , _ | lτ , lρ = lτ , (ll , lρ)
    leftsL-split (next-lane πL) τ {l = l} (lifts-next L) lt   with liftsL-split πL τ L | leftsL-split πL τ {l = l} L lt
    ... | _ , _ , _ | lτ , lρ = lτ , lρ

  -- Read off a split named by its outcome.
  lefts-up : ∀ {h} {H : Heapᴹ h} {Δ A Δ′ A′ Δ″ A″} {t : Sub h Δ A} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (ρ : Path t u) (τ : Path u v) {s S}
             {L : Lifts H (ρ ⊕ τ) s S} {S′} {Lτ : Lifts H τ s S′} {Lρ : Lifts H ρ S′ S} → lifts-split ρ τ L ≡ (S′ , Lτ , Lρ) → Lefts H L → Lefts H Lρ
  lefts-up {H = H} ρ τ {L = L} eq lt = subst (λ w → Lefts H (proj₂ (proj₂ w))) eq (proj₂ (lefts-split ρ τ L lt))

  -- A source rewritten in place: the free nodes are the derivation's.
  lefts-subst : ∀ {h} {H : Heapᴹ h} {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} {ρ : Path t u} {ℓ} {X : Set ℓ} (f : X → U.Step Δ′ A′) {S x y}
                (e : x ≡ y) {L : Lifts H ρ (f x) S} → Lefts H L → Lefts H (subst (λ z → Lifts H ρ (f z) S) e L)
  lefts-subst f refl lt = lt

  lefts-subst₂ : ∀ {h} {H : Heapᴹ h} {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} {ρ : Path t u} {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} (f : X → Y → U.Step Δ′ A′) {S x₁ x₂ y₁ y₂}
                 (e₁ : x₁ ≡ x₂) (e₂ : y₁ ≡ y₂) {L : Lifts H ρ (f x₁ y₁) S} → Lefts H L → Lefts H (subst₂ (λ x y → Lifts H ρ (f x y) S) e₁ e₂ L)
  lefts-subst₂ f refl refl lt = lt

  -- What lifts along a path, the path sees.
  mutual
    lifts-seen : ∀ {h} {H : Heapᴹ h} {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} {ρ : Path t u} {s S} → Lifts H ρ s S → seen H ρ ≡ true
    lifts-seen lifts-here = refl
    lifts-seen (lifts-map L) = lifts-seen L
    lifts-seen (lifts-scan L) = lifts-seen L
    lifts-seen (lifts-take lv L) = ∧-join lv (∧-join refl (lifts-seen L))
    lifts-seen (lifts-outer _ _ L) = lifts-seen L
    lifts-seen (lifts-lanes L _ _ _) = liftsL-seen L
    lifts-seen (lifts-source pb _ L) = ∧-join (cong is-just pb) (lifts-seen L)
    lifts-seen (lifts-body {e = e} pt _ L) = ∧-join (cong (λ z → is-just z ∨ is-just e) pt) (lifts-seen L)
    lifts-seen {H = H} (lifts-shut {t = t} _ e _ L) = ∧-join (trans (cong (λ z → is-just (At.part H t) ∨ is-just z) e) (∨-zeroʳ _)) (lifts-seen L)
    lifts-seen (lifts-defer L) = lifts-seen L

    liftsL-seen : ∀ {h} {H : Heapᴹ h} {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} {πL : PathLanes ls u} {s bs S as}
                → LiftsLane H πL s bs S as → seenL H πL ≡ true
    liftsL-seen (lifts-this lv L) = ∧-join lv (lifts-seen L)
    liftsL-seen (lifts-next L) = liftsL-seen L

  -- A node whose next event is past `p` and everything under it.
  record Far {Γ A} (p : Pos) (c : U.Node Γ A) : Set where
    constructor far
    field far-at : ∀ {k} → U.headˢ (U.step c) ≡ just k → Beyond p k

  -- A node whose next event is not under `p`.
  Off : ∀ {Γ A} → Pos → U.Node Γ A → Set
  Off p c = ∀ {k} → U.headˢ (U.step c) ≡ just k → Under p k → ⊥

  -- No earlier than `p` and not under it: past all of it.
  beyond-apart : ∀ {p k} → p ≤ᵖ k → (Under p k → ⊥) → Beyond p k
  beyond-apart {p} (inj₁ refl) nu = ⊥-elim (nu ([] , sym (++-identityʳ p)))
  beyond-apart {p} {k} (inj₂ lt) nu = record { past = λ y → <ᵖ-apart p k y lt (λ ys e → nu (ys , e)) }

  far-apart : ∀ {p Γ A} {c : U.Node Γ A} → Heads p c → Off p c → Far p c
  far-apart hd off = far λ e → beyond-apart (hd e) (off e)

  Opt : (∀ {Γ A} → U.Node Γ A → Set) → ∀ {Γ A} → Maybe (U.Node Γ A) → Set
  Opt P nothing  = ⊤
  Opt P (just c) = P c

  -- What a held node's ended parts left running passes `P`: a flatMap's
  -- pool, a connect's ended source's rest.
  Pooled : ∀ {h} (H : Heapᴹ h) (P : ∀ {Γ A} → U.Node Γ A → Set) {Δ B Δ′ B′} → U.Node Δ B → Sub h Δ′ B′ → Set₁
  Pooled H P pl u = ∀ {c} → At.part H u ≡ just c → P pl

  Rested : ∀ {h} (H : Heapᴹ h) (P : ∀ {Γ A} → U.Node Γ A → Set) {Δ A Δ′ B′} → U.Node Δ A → Sub h Δ A → Maybe Pos → Sub h Δ′ B′ → Set₁
  Rested H P rt src e u = ∀ {n} → At.part H u ≡ just n → At.part H src ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt

  -- EVERY SIBLING THE PATH PASSES PASSES `P`: a flatMap's other lanes,
  -- its outer and its pool, a connect's source or body and an ended
  -- source's rest.  At `Far p`, what each side condition of `Lifts` asks,
  -- given the step at the path's end is under `p`.
  mutual
    Clear : ∀ {h} (H : Heapᴹ h) (P : ∀ {Γ A} → U.Node Γ A → Set) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → Set₁
    Clear H P here                    = Lift _ ⊤
    Clear H P (in-map ρ)              = Clear H P ρ
    Clear H P (in-scan ρ)             = Clear H P ρ
    Clear H P (in-take ρ)             = Clear H P ρ
    Clear H P (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {t} {ls} ρ) =
      All P (At.partLanes H ls) × Pooled H P pl (flatMapˢ op f fl oc k r pl t ls) × Clear H P ρ
    Clear H P (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t} {ls} πL) =
      Opt P (At.part H t) × Pooled H P pl (flatMapˢ op f fl oc k r pl t ls) × ClearL H P πL
    Clear H P (in-source {bd = bd} ρ) = Opt P (At.part H bd) × Clear H P ρ
    Clear H P (in-body {S = Sj} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t} {bd} ρ) =
      Opt P (At.part H t) × Rested H P rt t e (connectˢ Sj c b kb k fd rp e rt t bd) × Clear H P ρ
    Clear H P (in-defer ρ)            = Clear H P ρ

    ClearL : ∀ {h} (H : Heapᴹ h) (P : ∀ {Γ A} → U.Node Γ A → Set) {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′}
           → PathLanes ls u → Set₁
    ClearL H P (this-lane {ls = ls} ρ) = All P (At.partLanes H ls) × Clear H P ρ
    ClearL H P (next-lane {l = l} πL)  = All P (At.partLanes H (l ∷ [])) × ClearL H P πL

  -- Two facts of every sibling, one.
  module _ {P Q R′ : ∀ {Γ A} → U.Node Γ A → Set} (f : ∀ {Γ A} {c : U.Node Γ A} → P c → Q c → R′ c) where
    all-zip : ∀ {Γ A} {cs : List (U.Node Γ A)} → All P cs → All Q cs → All R′ cs
    all-zip []       []       = []
    all-zip (a ∷ as) (b ∷ bs) = f a b ∷ all-zip as bs

    opt-zip : ∀ {Γ A} (o : Maybe (U.Node Γ A)) → Opt P o → Opt Q o → Opt R′ o
    opt-zip nothing  _ _ = tt
    opt-zip (just c) a b = f a b

    mutual
      clear-zip : ∀ {h} {H : Heapᴹ h} {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) → Clear H P π → Clear H Q π → Clear H R′ π
      clear-zip here          _         _         = lift tt
      clear-zip (in-map ρ)    a         b         = clear-zip ρ a b
      clear-zip (in-scan ρ)   a         b         = clear-zip ρ a b
      clear-zip (in-take ρ)   a         b         = clear-zip ρ a b
      clear-zip (in-outer ρ)  (a , pa , a′)  (b , pb , b′)  = all-zip a b , (λ e → f (pa e) (pb e)) , clear-zip ρ a′ b′
      clear-zip {H = H} (in-lanes {t = t} πL) (a , pa , a′) (b , pb , b′) =
        opt-zip (At.part H t) a b , (λ e → f (pa e) (pb e)) , clearL-zip πL a′ b′
      clear-zip {H = H} (in-source {bd = bd} ρ) (a , a′) (b , b′) = opt-zip (At.part H bd) a b , clear-zip ρ a′ b′
      clear-zip {H = H} (in-body {t = t} ρ) (a , ra , a′) (b , rb , b′) =
        opt-zip (At.part H t) a b , (λ e n j → f (ra e n j) (rb e n j)) , clear-zip ρ a′ b′
      clear-zip (in-defer ρ)  a         b         = clear-zip ρ a b

      clearL-zip : ∀ {h} {H : Heapᴹ h} {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (πL : PathLanes ls u)
                 → ClearL H P πL → ClearL H Q πL → ClearL H R′ πL
      clearL-zip (this-lane ρ)  (a , a′) (b , b′) = all-zip a b , clear-zip ρ a′ b′
      clearL-zip (next-lane πL) (a , a′) (b , b′) = all-zip a b , clearL-zip πL a′ b′

  -- What every node below passes, every sibling along a path does.
  module _ {h} {H : Heapᴹ h} {P : ∀ {Γ A} → U.Node Γ A → Set} where
    opt-each : ∀ {Γ A} (o : Maybe (U.Node Γ A)) → (∀ {c} → o ≡ just c → P c) → Opt P o
    opt-each nothing  f = tt
    opt-each (just c) f = f refl

    lane-only : ∀ {Δ B Δ′ A′} {l : Lane h Δ B} {ls} {u : Sub h Δ′ A′} → PathLanes (l ∷ []) u → PathLanes (l ∷ ls) u
    lane-only (this-lane ρ)  = this-lane ρ
    lane-only (next-lane ())

    seenL-only : ∀ {Δ B Δ′ A′} {l : Lane h Δ B} {ls} {u : Sub h Δ′ A′} (πL : PathLanes (l ∷ []) u) → seenL H (lane-only {ls = ls} πL) ≡ seenL H πL
    seenL-only (this-lane ρ)  = refl
    seenL-only (next-lane ())

    ∨-true : ∀ {x y} → x ≡ true → x ∨ y ≡ true
    ∨-true refl = refl

    each-lanes : ∀ {Δ B} (ls : List (Lane h Δ B))
               → (∀ {Δ′ A′} {u : Sub h Δ′ A′} (πL : PathLanes ls u) → seenL H πL ≡ true → ∀ {c} → At.part H u ≡ just c → P c)
               → All P (At.partLanes H ls)
    each-lanes []                f = []
    each-lanes (lane c k s ∷ ls) f with At.val H (Kit.live c) in lv
    ... | false = each-lanes ls (λ πL → f (next-lane πL))
    ... | true with At.part H s in e
    ...   | nothing = each-lanes ls (λ πL → f (next-lane πL))
    ...   | just x  = f (this-lane here) (∧-join lv refl) e ∷ each-lanes ls (λ πL → f (next-lane πL))

    each-sub : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Each H P t → (ρ : Path t u) → seen H ρ ≡ true → Each H P u
    each-sub ev ρ sρ = record
      { parts = λ ψ sψ → Each.parts ev (ρ ⊕ ψ) (seen-join H ρ ψ sρ sψ)
      ; pools = λ ψ sψ → Each.pools ev (ρ ⊕ ψ) (seen-join H ρ ψ sρ sψ)
      ; rests = λ ψ sψ → Each.rests ev (ρ ⊕ ψ) (seen-join H ρ ψ sρ sψ) }

    -- Along a path the ghost holds to a part it holds.
    mutual
      clear-each : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Each H P t → (π : Path t u) → seen H π ≡ true
                 → is-just (At.part H u) ≡ true → Clear H P π
      clear-each ev here                    _  _ = lift tt
      clear-each ev (in-map ρ)              sn j = clear-each (each-sub ev (in-map here) refl) ρ sn j
      clear-each ev (in-scan ρ)             sn j = clear-each (each-sub ev (in-scan here) refl) ρ sn j
      clear-each ev (in-take {c = c} {tk = tk} ρ) sn j with ∧-split (At.val H (Kit.live c)) sn
      ... | lv , r with ∧-split (isTaking tk) r
      ... | tg , sρ = clear-each (each-sub ev (in-take here) (∧-join lv (∧-join tg refl))) ρ sρ j
      clear-each ev (in-outer {ls = ls} ρ)  sn j =
        each-lanes ls (λ πL sL → Each.parts ev (in-lanes πL) sL) , Each.pools ev here refl , clear-each (each-sub ev (in-outer here) refl) ρ sn j
      clear-each ev (in-lanes {t = t} πL)   sn j =
        opt-each (At.part H t) (Each.parts ev (in-outer here) refl) , Each.pools ev here refl
        , clearL-each (λ πL′ sL → each-sub ev (in-lanes πL′) sL) πL sn j
      clear-each ev (in-source {bd = bd} ρ) sn j with ∧-split (is-just (At.part H bd)) sn
      ... | jb , sρ = opt-each (At.part H bd) (Each.parts ev (in-body here) (∧-join (∨-true (seen-up H ρ sρ j)) refl))
                    , clear-each (each-sub ev (in-source here) (∧-join jb refl)) ρ sρ j
      clear-each ev (in-body {e = e} {t = t} ρ) sn j with ∧-split (is-just (At.part H t) ∨ is-just e) sn
      ... | js , sρ = opt-each (At.part H t) (Each.parts ev (in-source here) (∧-join (seen-up H ρ sρ j) refl)) , Each.rests ev here refl
                    , clear-each (each-sub ev (in-body here) (∧-join js refl)) ρ sρ j
      clear-each ev (in-defer ρ)            sn j = clear-each (each-sub ev (in-defer here) refl) ρ sn j

      clearL-each : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′}
                  → (∀ {Δ″ A″} {w : Sub h Δ″ A″} (πL : PathLanes ls w) → seenL H πL ≡ true → Each H P w)
                  → (πL : PathLanes ls u) → seenL H πL ≡ true → is-just (At.part H u) ≡ true → ClearL H P πL
      clearL-each f (this-lane {c = c} {ls = ls} ρ) sn j with ∧-split (At.val H (Kit.live c)) sn
      ... | lv , sρ = each-lanes ls (λ πL sL → Each.parts (f (next-lane πL) sL) here refl) , clear-each (f (this-lane here) (∧-join lv refl)) ρ sρ j
      clearL-each f (next-lane {l = l} πL)  sn j =
        each-lanes (l ∷ []) (λ πL′ sL → Each.parts (f (lane-only πL′) (trans (seenL-only πL′) sL)) here refl)
        , clearL-each (λ πL′ → f (next-lane πL′)) πL sn j

  -- Walking two paths is walking each.
  mutual
    walk-⊕ : ∀ {h Δ A Δ′ A′ Δ″ A″} {t : Sub h Δ A} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (ρ : Path t u) (τ : Path u v) (W : Here h Δ A)
           → walk (ρ ⊕ τ) W ≡ walk τ (walk ρ W)
    walk-⊕ here          τ W = refl
    walk-⊕ (in-map ρ)    τ W = walk-⊕ ρ τ _
    walk-⊕ (in-scan ρ)   τ W = walk-⊕ ρ τ _
    walk-⊕ (in-take ρ)   τ W = walk-⊕ ρ τ _
    walk-⊕ (in-outer ρ)  τ W = walk-⊕ ρ τ _
    walk-⊕ (in-lanes {op = op} {f} {fl} πL) τ W = walkL-⊕ op f fl W πL τ
    walk-⊕ (in-source ρ) τ W = walk-⊕ ρ τ _
    walk-⊕ (in-body ρ)   τ W = walk-⊕ ρ τ _
    walk-⊕ (in-defer ρ)  τ W = walk-⊕ ρ τ _

    walkL-⊕ : ∀ {h Δ A B Δ′ A′ Δ″ A″} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (op : T.FlatOp)
              (f : A → T.Obs Timeline Δ B) (fl : FlatKit.Flat A h) (W : Here h Δ B) (πL : PathLanes ls u) (τ : Path u v)
            → walkLanes op f fl W (πL ⊕ᴸ τ) ≡ walk τ (walkLanes op f fl W πL)
    walkL-⊕ op f fl W (this-lane ρ)  τ = walk-⊕ ρ τ _
    walkL-⊕ op f fl W (next-lane πL) τ = walkL-⊕ op f fl W πL τ

  -- A path one operator long.
  mutual
    data One {h} : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → Set₁ where
      one-map    : ∀ {Δ A B} {f : A → B} {t : Sub h Δ A} → One (in-map {f = f} {t = t} here)
      one-scan   : ∀ {Δ A B} {f : B → A → B} {r} {t : Sub h Δ A} → One (in-scan {f = f} {r} {t = t} here)
      one-take   : ∀ {Δ A} {i p c k tk} {t : Sub h Δ A} → One (in-take {i = i} {p} {c} {k} {tk} {t = t} here)
      one-outer  : ∀ {Δ A B} {op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)} → One (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {t = t} {ls} here)
      one-lanes  : ∀ {Δ A B} {op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u}
                 → OneLane πL → One (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t = t} πL)
      one-source : ∀ {Δ A B} {Sj c b kb k fd e rp rt} {t : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} → One (in-source {S = Sj} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = t} {bd} here)
      one-body   : ∀ {Δ A B} {Sj c b kb k fd e rp rt} {t : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} → One (in-body {S = Sj} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = t} {bd} here)
      one-defer  : ∀ {Δ A} {k} {t : Sub h Δ A} → One (in-defer {k = k} {t = t} here)

    data OneLane {h} : ∀ {Δ B} {ls : List (Lane h Δ B)} {u : Sub h Δ B} → PathLanes ls u → Set₁ where
      one-this : ∀ {Δ B} {c k} {t : Sub h Δ B} {ls} → OneLane (this-lane {c = c} {k} {t = t} {ls} here)
      one-next : ∀ {Δ B} {l} {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} → OneLane πL → OneLane (next-lane {l = l} πL)

  -- A path read from its far end: none, or a path and one operator more.
  data Last {h Δ A} {t : Sub h Δ A} : ∀ {Δ′ A′} {v : Sub h Δ′ A′} → Path t v → Set₁ where
    whole : Last here
    snoc  : ∀ {Δ′ A′ Δ″ A″} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (ρ : Path t u) (s : Path u v) → One s → Last (ρ ⊕ s)

  data LastL {h Δ B} {ls : List (Lane h Δ B)} : ∀ {Δ′ A′} {v : Sub h Δ′ A′} → PathLanes ls v → Set₁ where
    oneL  : ∀ {v : Sub h Δ B} {πL : PathLanes ls v} → OneLane πL → LastL πL
    snocL : ∀ {Δ′ A′ Δ″ A″} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (πL : PathLanes ls u) (s : Path u v) → One s → LastL (πL ⊕ᴸ s)

  mutual
    view : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {v : Sub h Δ′ A′} (σ : Path t v) → Last σ
    view here = whole
    view (in-map p) with view p
    ... | whole      = snoc here (in-map here) one-map
    ... | snoc ρ s o = snoc (in-map ρ) s o
    view (in-scan p) with view p
    ... | whole      = snoc here (in-scan here) one-scan
    ... | snoc ρ s o = snoc (in-scan ρ) s o
    view (in-take p) with view p
    ... | whole      = snoc here (in-take here) one-take
    ... | snoc ρ s o = snoc (in-take ρ) s o
    view (in-outer p) with view p
    ... | whole      = snoc here (in-outer here) one-outer
    ... | snoc ρ s o = snoc (in-outer ρ) s o
    view (in-lanes p) with viewL p
    ... | oneL o      = snoc here (in-lanes p) (one-lanes o)
    ... | snocL ρ s o = snoc (in-lanes ρ) s o
    view (in-source p) with view p
    ... | whole      = snoc here (in-source here) one-source
    ... | snoc ρ s o = snoc (in-source ρ) s o
    view (in-body p) with view p
    ... | whole      = snoc here (in-body here) one-body
    ... | snoc ρ s o = snoc (in-body ρ) s o
    view (in-defer p) with view p
    ... | whole      = snoc here (in-defer here) one-defer
    ... | snoc ρ s o = snoc (in-defer ρ) s o

    viewL : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {v : Sub h Δ′ A′} (πL : PathLanes ls v) → LastL πL
    viewL (this-lane p) with view p
    ... | whole      = oneL one-this
    ... | snoc ρ s o = snocL (this-lane ρ) s o
    viewL (next-lane p) with viewL p
    ... | oneL o      = oneL (one-next o)
    ... | snocL ρ s o = snocL (next-lane ρ) s o

  -- How many operators a path passes.
  mutual
    height : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → ℕ
    height here          = 0
    height (in-map p)    = suc (height p)
    height (in-scan p)   = suc (height p)
    height (in-take p)   = suc (height p)
    height (in-outer p)  = suc (height p)
    height (in-lanes p)  = heightL p
    height (in-source p) = suc (height p)
    height (in-body p)   = suc (height p)
    height (in-defer p)  = suc (height p)

    heightL : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → PathLanes ls u → ℕ
    heightL (this-lane p) = suc (height p)
    heightL (next-lane p) = heightL p

  mutual
    height-⊕ : ∀ {h Δ A Δ′ A′ Δ″ A″} {t : Sub h Δ A} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (ρ : Path t u) (τ : Path u v)
             → height (ρ ⊕ τ) ≡ height ρ + height τ
    height-⊕ here          τ = refl
    height-⊕ (in-map ρ)    τ = cong suc (height-⊕ ρ τ)
    height-⊕ (in-scan ρ)   τ = cong suc (height-⊕ ρ τ)
    height-⊕ (in-take ρ)   τ = cong suc (height-⊕ ρ τ)
    height-⊕ (in-outer ρ)  τ = cong suc (height-⊕ ρ τ)
    height-⊕ (in-lanes πL) τ = heightL-⊕ πL τ
    height-⊕ (in-source ρ) τ = cong suc (height-⊕ ρ τ)
    height-⊕ (in-body ρ)   τ = cong suc (height-⊕ ρ τ)
    height-⊕ (in-defer ρ)  τ = cong suc (height-⊕ ρ τ)

    heightL-⊕ : ∀ {h Δ B Δ′ A′ Δ″ A″} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (πL : PathLanes ls u) (τ : Path u v)
              → heightL (πL ⊕ᴸ τ) ≡ heightL πL + height τ
    heightL-⊕ (this-lane ρ)  τ = cong suc (height-⊕ ρ τ)
    heightL-⊕ (next-lane πL) τ = heightL-⊕ πL τ

  mutual
    height-one : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} {s : Path t u} → One s → height s ≡ 1
    height-one one-map       = refl
    height-one one-scan      = refl
    height-one one-take      = refl
    height-one one-outer     = refl
    height-one (one-lanes o) = heightL-one o
    height-one one-source    = refl
    height-one one-body      = refl
    height-one one-defer     = refl

    heightL-one : ∀ {h Δ B} {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} → OneLane πL → heightL πL ≡ 1
    heightL-one one-this     = refl
    heightL-one (one-next o) = heightL-one o

  one-lower : ∀ {h Δ A Δ′ A′ Δ″ A″} {t : Sub h Δ A} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (ρ : Path t u) {s : Path u v} → One s
            → height ρ < height (ρ ⊕ s)
  one-lower ρ {s} o = subst (height ρ <_) (sym (trans (height-⊕ ρ s) (cong (height ρ +_) (height-one o)))) (m<m+n (height ρ) ≤-refl)

  -- Whether the observer an `of` at the path's end emits to reads open,
  -- from the root's open record down: a kill switch or a lane's cut
  -- closes it, a connect's subject reads afresh.
  mutual
    opened : ∀ {h} (H : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Bool → Path t u → Bool
    opened H o here                       = o
    opened H o (in-map p)                 = opened H o p
    opened H o (in-scan p)                = opened H o p
    opened H o (in-take {c = c} p)        = opened H (At.val H (Kit.live c) ∧ o) p
    opened H o (in-outer {oc = oc} p)     = opened H (At.val H (Kit.live oc) ∧ o) p
    opened H o (in-lanes p)               = openedL H o p
    opened H o (in-source {S = Sj} p)     = opened H (not (At.val H (Subject.closed Sj))) p
    opened H o (in-body p)                = opened H o p
    opened H o (in-defer p)               = opened H o p

    openedL : ∀ {h} (H : Heapᴹ h) {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → Bool → PathLanes ls u → Bool
    openedL H o (this-lane {c = c} p) = opened H (At.val H (Kit.live c) ∧ o) p
    openedL H o (next-lane p)         = openedL H o p

  -- What climbs a path: a value, or an end with the calls `ks` owed
  -- after it.
  data Signal {h} (T : Sub h [] R) (A : Set) : Set₁ where
    sends  : A → Signal T A
    closes : List (Call T) → Signal T A

  -- The calls owed past a signal.
  owed : ∀ {h} {T : Sub h [] R} {A} → Signal T A → List (Call T)
  owed (sends _)   = []
  owed (closes ks) = ks

  -- What a signal makes of the observer it is told to.
  said : ∀ {h} {T : Sub h [] R} {A} → Observer A h → Signal T A → Act h ⊤
  said o (sends y)   = Observer.next o y
  said o (closes ks) = Observer.complete o >>ᴬ ⟦ ks ⟧ᶜ

  -- AN END ON ITS WAY UP HAS ALREADY REACHED EVERY CONNECT IT KILLS: a
  -- connect the path enters by its source, that source's part gone, has
  -- its end staged at the run's position.  The end climbs at one
  -- instant, so the connect's part never reads gone while its body runs.
  mutual
    Healed : ∀ {h} (H : Heapᴹ h) (q : Pos) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → Set₁
    Healed H q here                            = Lift _ ⊤
    Healed H q (in-map p)                      = Healed H q p
    Healed H q (in-scan p)                     = Healed H q p
    Healed H q (in-take p)                     = Healed H q p
    Healed H q (in-outer p)                    = Healed H q p
    Healed H q (in-lanes p)                    = HealedL H q p
    Healed H q (in-source {e = e} {t = s} p)   = (At.part H s ≡ nothing → e ≡ just q) × Healed H q p
    Healed H q (in-body p)                     = Healed H q p
    Healed H q (in-defer p)                    = Healed H q p

    HealedL : ∀ {h} (H : Heapᴹ h) (q : Pos) {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → PathLanes ls u → Set₁
    HealedL H q (this-lane p) = Healed H q p
    HealedL H q (next-lane p) = HealedL H q p

  mutual
    healed-split : ∀ {h} {H : Heapᴹ h} {q} {Δ A Δ′ A′ Δ″ A″} {t : Sub h Δ A} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (ρ : Path t u) (τ : Path u v)
                 → Healed H q (ρ ⊕ τ) → Healed H q ρ
    healed-split here          τ _       = lift tt
    healed-split (in-map ρ)    τ hl      = healed-split ρ τ hl
    healed-split (in-scan ρ)   τ hl      = healed-split ρ τ hl
    healed-split (in-take ρ)   τ hl      = healed-split ρ τ hl
    healed-split (in-outer ρ)  τ hl      = healed-split ρ τ hl
    healed-split (in-lanes πL) τ hl      = healedL-split πL τ hl
    healed-split (in-source ρ) τ (x , hl) = x , healed-split ρ τ hl
    healed-split (in-body ρ)   τ hl      = healed-split ρ τ hl
    healed-split (in-defer ρ)  τ hl      = healed-split ρ τ hl

    healedL-split : ∀ {h} {H : Heapᴹ h} {q} {Δ B Δ′ A′ Δ″ A″} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (πL : PathLanes ls u) (τ : Path u v)
                  → HealedL H q (πL ⊕ᴸ τ) → HealedL H q πL
    healedL-split (this-lane ρ)  τ hl = healed-split ρ τ hl
    healedL-split (next-lane πL) τ hl = healedL-split πL τ hl

  -- An end reaching a connect's source: the connect's own end staged.
  mutual
    healed-end : ∀ {h} {H : Heapᴹ h} {q} {Δ A Δ′ A′ B′ Sj c b kb k fd e rp rt} {t : Sub h Δ A} {s : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
                 (ρ : Path t (connectˢ Sj c b kb k fd rp e rt s bd)) → Healed H q (ρ ⊕ in-source here) → At.part H s ≡ nothing → e ≡ just q
    healed-end here          (x , _) = x
    healed-end (in-map ρ)    hl      = healed-end ρ hl
    healed-end (in-scan ρ)   hl      = healed-end ρ hl
    healed-end (in-take ρ)   hl      = healed-end ρ hl
    healed-end (in-outer ρ)  hl      = healed-end ρ hl
    healed-end (in-lanes πL) hl      = healedL-end πL hl
    healed-end (in-source ρ) (_ , hl) = healed-end ρ hl
    healed-end (in-body ρ)   hl      = healed-end ρ hl
    healed-end (in-defer ρ)  hl      = healed-end ρ hl

    healedL-end : ∀ {h} {H : Heapᴹ h} {q} {Δ B Δ′ A′ B′ Sj c b kb k fd e rp rt} {ls : List (Lane h Δ B)} {s : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
                  (πL : PathLanes ls (connectˢ Sj c b kb k fd rp e rt s bd)) → HealedL H q (πL ⊕ᴸ in-source here) → At.part H s ≡ nothing → e ≡ just q
    healedL-end (this-lane ρ)  hl = healed-end ρ hl
    healedL-end (next-lane πL) hl = healedL-end πL hl

  -- The node a signal reaches already past it, and the ghost's step the
  -- signal lifted along the path: a value leaves the node standing, an
  -- end leaves it gone, every connect it killed on the way ended.
  Passed : ∀ {h} (H : Heapᴹ h) (q : Pos) (g : U.Node [] R) {T : Sub h [] R} {Δ A} {v : Sub h Δ A} → Path T v → Signal T A → Set₁
  Passed H q g {Δ = Δ} {A} {v} σ (sends y) =
    Σ (U.Node Δ A) λ c′ → At.part H v ≡ just c′ × Σ (U.Step [] R) λ S → Lifts H σ (U.outˢ q y c′) S × U.step g ≡ S
  Passed H q g {v = v} σ (closes _) =
    At.part H v ≡ nothing × Σ (U.Step [] R) λ S → Lifts H σ (U.endˢ q) S × U.step g ≡ S × Healed H q σ

  -- What a closed sub leaves running heads no earlier than the run.
  ClosedHeads : ∀ {h} (H : Heapᴹ h) (q : Pos) {T : Sub h [] R} {Δ A} {v : Sub h Δ A} → Path T v → Signal T A → Set
  ClosedHeads H q σ (sends _)          = ⊤
  ClosedHeads H q {v = v} σ (closes _) = Heads q (U.restᶜ {B = ⊤} (At.leftover H {B = ⊤} v))

  -- What the climbing signal's lift leaves free, left alike.
  LeftsOf : ∀ {h} (H : Heapᴹ h) (q : Pos) (g : U.Node [] R) {T : Sub h [] R} {Δ A} {v : Sub h Δ A} (σ : Path T v) (sg : Signal T A) → Passed H q g σ sg → Set₁
  LeftsOf H q g σ (sends y)  (_ , _ , _ , L , _) = Lefts H L
  LeftsOf H q g σ (closes _) (_ , _ , L , _)     = Lefts H L

  -- A SIGNAL ON ITS WAY UP: `sg` about to be told to the observer the
  -- path walks to, the agenda empty above the stack but for the calls
  -- the signal owes.
  record Calling (g : U.Node [] R) (ℓ : Load) (m₁ : Mach) {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
                 (σ : Path T v) (sg : Signal T A) : Set₁ where
    field
      sane    : Sane [] g
      placed  : Placed g []
      deep    : Deep g []
      {w}     : World
      {ϑ}     : w ⊑ Conf.world (Mach.conf m₁)
      {act}   : Act (Conf.world (Mach.conf m₁)) ⊤
      {K}     : Stack w ⊤
      ctl     : Conf.ctl (Mach.conf m₁) ≡ run act ϑ K
      code    : act ≗ said (Here.obs (walk σ top)) sg
      stack   : StackAs T (Conf.pos (Mach.conf m₁)) ϑ K (Mach.bursts m₁)
      lifted  : Passed (Conf.heap (Mach.conf m₁)) (Conf.pos (Mach.conf m₁)) g σ sg
      lefts   : LeftsOf (Conf.heap (Mach.conf m₁)) (Conf.pos (Mach.conf m₁)) g σ sg lifted
      rest-heads : ClosedHeads (Conf.heap (Mach.conf m₁)) (Conf.pos (Mach.conf m₁)) σ sg
      owned   : Owned (Conf.heap (Mach.conf m₁)) T (runAs (owed sg) (≗-refl _) stack)
      kernels : Kernels (Conf.heap (Mach.conf m₁)) T
      meaning : Meaning (Conf.heap (Mach.conf m₁)) T
      queue   : Queue (Conf.heap (Mach.conf m₁)) (Conf.pos (Mach.conf m₁)) (Mach.clock m₁) (Mach.timers m₁) T
      books   : Books T (runAs (owed sg) (≗-refl _) stack) m₁
      sorted  : Σ Pos λ lo → WellMach lo m₁
      behind  : Each (Conf.heap (Mach.conf m₁)) (Heads (Conf.pos (Mach.conf m₁))) T
      lingers : Lingers (Conf.heap (Mach.conf m₁)) T
      told    : Untold (Conf.heap (Mach.conf m₁)) (Conf.pos (Mach.conf m₁)) T
      ended   : Ended (Conf.heap (Mach.conf m₁)) T
      flags   : DoneBy (Conf.heap (Mach.conf m₁)) T (outers σ)
      kept    : load m₁ T ≼ ℓ

  -- Done flags read as they were, one step up a path entering no outer.
  done-up : ∀ {h} {H : Heapᴹ h} {T : Sub h [] R} {Δ A Δ′ A′} {x : Sub h Δ A} {v : Sub h Δ′ A′} (ρ : Path T x) (c : Path x v)
          → outers c ≡ [] → DoneBy H T (outers (ρ ⊕ c)) → DoneBy H T (outers ρ)
  done-up {H = H} {T = T} ρ c e d = subst (DoneBy H T) (trans (outers-⊕ ρ c) (trans (cong (outers ρ ++_) e) (++-identityʳ (outers ρ)))) d

  -- The same call, the signal restated at another path, owing as much.
  recall : ∀ {g ℓ m₁ Δ A Δ′ A′} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
             {v′ : Sub (Conf.world (Mach.conf m₁)) Δ′ A′} {σ : Path T v} {sg : Signal T A} (cl : Calling g ℓ m₁ σ sg) {σ′ : Path T v′} {sg′ : Signal T A′}
         → owed sg′ ≡ owed sg
         → Calling.act cl ≗ said (Here.obs (walk σ′ top)) sg′
         → (lf : Passed (Conf.heap (Mach.conf m₁)) (Conf.pos (Mach.conf m₁)) g σ′ sg′)
         → LeftsOf (Conf.heap (Mach.conf m₁)) (Conf.pos (Mach.conf m₁)) g σ′ sg′ lf
         → ClosedHeads (Conf.heap (Mach.conf m₁)) (Conf.pos (Mach.conf m₁)) σ′ sg′
         → DoneBy (Conf.heap (Mach.conf m₁)) T (outers σ′)
         → Calling g ℓ m₁ σ′ sg′
  recall {m₁ = m₁} {T = T} cl ow cd lf lt es dn = record
    { sane = Calling.sane cl ; placed = Calling.placed cl ; deep = Calling.deep cl ; ctl = Calling.ctl cl ; code = cd ; stack = Calling.stack cl ; lifted = lf ; lefts = lt ; rest-heads = es
    ; owned = subst (λ ks → Owned (Conf.heap (Mach.conf m₁)) T (runAs ks (≗-refl _) (Calling.stack cl))) (sym ow) (Calling.owned cl)
    ; kernels = Calling.kernels cl ; meaning = Calling.meaning cl ; queue = Calling.queue cl
    ; books = subst (λ ks → Books T (runAs ks (≗-refl _) (Calling.stack cl)) m₁) (sym ow) (Calling.books cl)
    ; sorted = Calling.sorted cl ; behind = Calling.behind cl ; lingers = Calling.lingers cl ; told = Calling.told cl ; ended = Calling.ended cl ; flags = dn ; kept = Calling.kept cl }

  -- The same call, held to a load no lighter.
  relevel : ∀ {g ℓ ℓ′ m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A} {σ : Path T v} {sg : Signal T A}
          → Calling g ℓ′ m₁ σ sg → ℓ′ ≼ ℓ → Calling g ℓ m₁ σ sg
  relevel cl le = record
    { sane = Calling.sane cl ; placed = Calling.placed cl ; deep = Calling.deep cl ; ctl = Calling.ctl cl ; code = Calling.code cl ; stack = Calling.stack cl
    ; lifted = Calling.lifted cl ; lefts = Calling.lefts cl ; rest-heads = Calling.rest-heads cl ; owned = Calling.owned cl ; kernels = Calling.kernels cl ; meaning = Calling.meaning cl
    ; queue = Calling.queue cl ; books = Calling.books cl ; sorted = Calling.sorted cl ; behind = Calling.behind cl ; lingers = Calling.lingers cl ; told = Calling.told cl ; ended = Calling.ended cl ; flags = Calling.flags cl
    ; kept = ≼-trans (Calling.kept cl) le }

  -- A signal one operator higher, the path shorter, the load at most `ℓ`.
  data Rises (g : U.Node [] R) (ℓ : Load) (m₁ : Mach) {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
             (σ : Path T v) : Set₁ where
    rises : ∀ {m₂ Δ′ A′} {T′ : Sub (Conf.world (Mach.conf m₂)) [] R} {v′ : Sub (Conf.world (Mach.conf m₂)) Δ′ A′} {σ′ : Path T′ v′} {sg′ : Signal T′ A′}
          → m₁ ⇝ m₂ → height σ′ < height σ → Calling g ℓ m₂ σ′ sg′ → Rises g ℓ m₁ σ

  -- One operator called: a re-entry configuration reached, or a signal
  -- one operator higher, the path shorter.
  data Called {g m} (st : Strong g m) (m₁ : Mach) {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
              (σ : Path T v) : Set₁ where
    landed : Hopped st m₁ → Called st m₁ σ
    rose   : ∀ {m₂ Δ′ A′} {T′ : Sub (Conf.world (Mach.conf m₂)) [] R} {v′ : Sub (Conf.world (Mach.conf m₂)) Δ′ A′} {σ′ : Path T′ v′} {sg′ : Signal T′ A′}
           → m₁ ⇝ m₂ → height σ′ < height σ → Calling g (loadOf st) m₂ σ′ sg′ → Called st m₁ σ

  -- Some signal on its way up.
  data Aloft (g : U.Node [] R) (ℓ : Load) (m₁ : Mach) : Set₁ where
    aloft : ∀ {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A} {σ : Path T v} {sg : Signal T A}
          → Calling g ℓ m₁ σ sg → Aloft g ℓ m₁

  -- A hop's machine sorted.
  hop-sorted : ∀ {g m m′ m₀} → Carried g m → step m ≡ silent m′ → m′ ⇝ m₀ → Σ Pos λ lo → WellMach lo m₀
  hop-sorted cr e p = sorted-⇝ (Carried.sorted cr) (then e p)

  -- The run moved back: every node still heads no earlier.
  heads-back : ∀ {q p Γ A} {c : U.Node Γ A} → q <ᵖ p ≡ true → Heads p c → Heads q c
  heads-back {q} {p} qp hd hk with hd hk
  ... | inj₁ refl = inj₂ qp
  ... | inj₂ pk   = inj₂ (<ᵖ-trans q p _ qp pk)

  each-back : ∀ {h} {H : Heapᴹ h} {t : Sub h [] R} {q p} → q <ᵖ p ≡ true → Each H (Heads p) t → Each H (Heads q) t
  each-back qp ev = record
    { parts = λ ψ sψ {c} e → heads-back {c = c} qp (Each.parts ev ψ sψ e)
    ; pools = λ {pl = pl} ψ sψ e → heads-back {c = pl} qp (Each.pools ev ψ sψ e)
    ; rests = λ {rt = rt} ψ sψ e n j → heads-back {c = rt} qp (Each.rests ev ψ sψ e n j) }

  hopped-pre : ∀ {g m m′ m₁} {st : Strong g m} → m′ ⇝ m₁ → Hopped st m₁ → Hopped st m′
  hopped-pre path (g″ , m₀ , path′ , st₀ , gn) = g″ , m₀ , ⇝-trans path path′ , st₀ , gn
