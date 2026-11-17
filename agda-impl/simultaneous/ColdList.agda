{-# OPTIONS --guardedness #-}

-- THE ELABORATED COLD'S LISTING IS ITS WRITTEN-OUT ROWS (`cold-rows`).
-- A merge's listing is the merge of its parts' listings, each lane read
-- off its own listing (`merge-tr`); the elaborated cold is the merge of
-- the scan's rows and each tag's render, so its rows are `CRow`'s once
-- the scan's and each render's are.
--
-- The joiner's two side conditions come from one fact about the order
-- (`srow-lane-end`): every tag's render ends before the scan does.  So
-- the scan's end has every part ended, and a render's end never does.
module simultaneous.ColdList where

open import Data.Bool using (Bool; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Tree using (Obs; mergeᶠ; flatMap; cold; of; map; scan; merge)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; last; _⊕_)
open import denotation.Events using (Timeline; From; fixed; fresh; start)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Den; coldAt; enter; After; LaneOf; Reach; Ended; Work; _≺_; _≼_; module Merge)
open import denotation.Laws.Modulus using (≼-refl; ≺→≼)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (Row; rows; afterL)
open import quickcheck.Tabled.Exact using (merge-exact; truncate-exact)
open import quickcheck.Tabled.Exact.Base using (Exact; Exactly; sound; complete; bind⁻; lanes-from; lanes-to; afterL-exact)
open import simultaneous.SObs using (Tag; val; cdone; tick; lone; module Elaborate)
open import simultaneous.Listing using (walkN; listC; listC-ok; UncutEnv)
open import simultaneous.TableCorr using (TR)
open import simultaneous.ColdRows using (module At)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; coldˢ; concatˢ; phase; render)

------------------------------------------------------------------------
-- A listing is exact for its own table

tr-at : ∀ {X : Set} {m : Maybe (Tb.Listed X)} {L k e} → m ≡ just L → TR m k e → (k , e) ∈ rows L
tr-at refl (_ , refl , x) = x

at-tr : ∀ {X : Set} {m : Maybe (Tb.Listed X)} {L k e} → m ≡ just L → (k , e) ∈ rows L → TR m k e
at-tr {L = L} eq x = L , eq , x

self-exact : ∀ {X : Set} {m : Maybe (Tb.Listed X)} {L} → m ≡ just L → Exactly L (TR m)
self-exact eq _ = record { sound = at-tr eq ; complete = tr-at eq }

-- Every row of a listed table waits on finitely many: the listing's.
reach-tr : ∀ {X : Set} {m : Maybe (Tb.Listed X)} {L k e} → m ≡ just L → Reach (TR m) k e
reach-tr {L = L} eq = mapL proj₁ (rows L) , λ x _ _ → ∈-map⁺ proj₁ (tr-at eq x)

------------------------------------------------------------------------
-- A merge's listing

-- Each lane read off its own listing, wherever it is subscribed.
laneD : ∀ {Γ} {X Y : Set} → ℕ → ℕ → (X → Obs Timeline Γ Y) → All Tb.Listed Γ → X → Den Y
laneD K n f ρ x = coldAt (λ s → TR (listC K n (f x) ρ s))

merge-tr : ∀ {Γ} {X Y : Set} K n (f : X → Obs Timeline Γ Y) (s : Obs Timeline Γ X) {ρ : All Tb.Listed Γ} → UncutEnv ρ → ∀ p {k e}
  → TR (listC K n (flatMap (mergeᶠ nothing) f s) ρ p) k e ⇔ Merge.JoinT (laneD K n f ρ) (TR (listC K n s ρ p)) k e
merge-tr K n f s {ρ} uρ p with listC-ok K n (flatMap (mergeᶠ nothing) f s) uρ p
... | L , eq , u with bind⁻ {m = listC K n s ρ p} eq
... | o , eo , e₁ with bind⁻ {m = Tb.lanes (afterL (λ a → listC K n (f a) ρ)) (Tb.values (rows o))} e₁
... | ls , els , refl = mk⇔ (λ x → sound ex (tr-at eq x)) (λ x → at-tr eq (complete ex x))
  where
    ex : Exact L (Merge.JoinT (laneD K n f ρ) (TR (listC K n s ρ p)))
    ex = merge-exact (laneD K n f ρ) o ls (self-exact eo)
      (lanes-from {ln = afterL (λ a → listC K n (f a) ρ)} {D = λ a → After (laneD K n f ρ a)}
        (afterL-exact {ln = λ a → listC K n (f a) ρ} {D = λ a → enter (laneD K n f ρ a)} (λ el → truncate-exact (self-exact el))) els)
      (lanes-to {ln = afterL (λ a → listC K n (f a) ρ)} els) u

------------------------------------------------------------------------
-- The elaborated cold

module Cold {A : Set} (K n : ℕ) {Δ : List Set} (ρ : All Tb.Listed Δ) (uρ : UncutEnv ρ) (m : From A 0) (P : Pos) where
  open At {A} P using (C₀; c₀; SRow; Rend; CRow; r-end; c-skp; c-end; c-val; c-lane; c-lend)

  J : List (Row A)
  J = walkN K (start c₀ m)

  -- The scan the renders hang off.
  scanned : Obs Timeline Δ (Bool × Tag A)
  scanned = scan phase (false , tick) (merge (concatˢ (map val (cold (fixed m))) (of (cdone ∷ []))) (of (tick ∷ [])))

  fR : Bool × Tag A → Den (IE A)
  fR = laneD K n render ρ

  open Merge fR (TR (listC K n scanned ρ P)) using (JoinT; Done; val; step; opin; oend; opass; lane; lend; lpass; hand; left; run; rend; rpass; rhand)

  postulate
    -- THE COLD'S ROWS.
    scan-rows     : ∀ {k e} → TR (listC K n scanned ρ P) k e ⇔ SRow J k e
    rend-rows     : ∀ q x {k e} → LaneOf fR q x k e ⇔ Rend q x k e
    srow-lane-end : ∀ {q x c} → SRow J q (out x) → SRow J c end → (q ⊕ (ix 1 ∷ last ∷ [])) ≺ c

  private
    to-s : ∀ {k e} → TR (listC K n scanned ρ P) k e → SRow J k e
    to-s = Equivalence.to scan-rows

    fr-s : ∀ {k e} → SRow J k e → TR (listC K n scanned ρ P) k e
    fr-s = Equivalence.from scan-rows

    -- At the scan's end every part has ended.
    done : ∀ {c} → SRow J c end → Done c
    done {c} s = (c , fr-s s , ≼-refl {c})
               , λ {q} {a} x _ _ _ → q ⊕ (ix 1 ∷ last ∷ []) , Equivalence.from (rend-rows q a) r-end
                                   , ≺→≼ {q ⊕ (ix 1 ∷ last ∷ [])} {c} (srow-lane-end (to-s x) s)

    -- At a render's end the scan has not.
    undone : ∀ {q x} → SRow J q (out x) → Done (q ⊕ (ix 1 ∷ last ∷ [])) → ⊥
    undone {q} s ((c₁ , t , le) , _) = le (srow-lane-end {q} {c = c₁} s (to-s t))

  top-to : ∀ {k e} → JoinT k e → CRow J k e
  top-to (val x)             = c-val (to-s x)
  top-to (step x)            = c-skp (to-s x)
  top-to (opin x)            with to-s x
  ... | ()
  top-to (oend x _)          = c-end (to-s x)
  top-to (opass x nD)        = ⊥-elim (nD (done (to-s x)))
  top-to (lane {q} {a} x _ l _ w) = c-lane (to-s x) (Equivalence.to (rend-rows q a) l) w
  top-to (lend {q} {a} x _ l _ _ D) with Equivalence.to (rend-rows q a) l
  ... | r-end = ⊥-elim (undone (to-s x) D)
  top-to (lpass {q} {a} x _ l _ _ _) with Equivalence.to (rend-rows q a) l
  ... | r-end = c-lend (to-s x)
  top-to (hand _ _ _ _ ())
  top-to (left {q} {a} x _ l _ _) with Equivalence.to (rend-rows q a) l
  ... | ()
  top-to (run () _)
  top-to (rend () _ _)
  top-to (rpass () _ _)
  top-to (rhand () _)

  top-from : ∀ {k e} → CRow J k e → JoinT k e
  top-from (c-skp s)    = step (fr-s s)
  top-from (c-end s)    = oend (fr-s s) (done s)
  top-from (c-val s)    = val (fr-s s)
  top-from (c-lane {q} {x} s r w) = lane (fr-s s) tt (Equivalence.from (rend-rows q x) r) (λ ()) w
  top-from (c-lend {q} {x} s) = lpass (fr-s s) tt (Equivalence.from (rend-rows q x) r-end) (λ ()) (λ ()) (undone s)

  cold-rows : ∀ {k e} → TR (listC K n (coldˢ (fixed m)) ρ P) k e ⇔ CRow J k e
  cold-rows = mk⇔ (λ x → top-to (Equivalence.to (merge-tr K n render scanned uρ P) x))
                  (λ x → Equivalence.from (merge-tr K n render scanned uρ P) (top-from x))
