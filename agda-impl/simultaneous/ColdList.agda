{-# OPTIONS --guardedness #-}

-- THE ELABORATED COLD'S LISTING IS ITS WRITTEN-OUT ROWS (`cold-rows`).
-- The elaborated cold is the merge of the scan's rows (`scan-rows`) and
-- each tag's render (`rend-rows`), so its rows are `CRow`'s.  They are
-- read at depth `3 + N`, where a render's mint is listed whole.
--
-- The joiner's two side conditions come from one fact about the order
-- (`srow-lane-end`): every tag's render ends before the scan does.  So
-- the scan's end has every part ended, and a render's end never does.
-- An end in the burst lies under the merge's last label, past every
-- value's render under its first; a later end lies past the burst, and
-- past every other row of the cold an instant apart.
module simultaneous.ColdList where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst₂)
open import Data.Unit using (tt)
open import Function using (_⇔_; mk⇔; Equivalence)

open import denotation.Position using (Pos; root; _≟ᵖ_; _<ˡ_; ix; last; _⊕_)
open import denotation.Events using (Timeline; From; fixed; fresh)
open import denotation.EmissionSet using (out; end; _≺_; module Merge)
open import denotation.Laws.Modulus using (≼-refl; ≺→≼; ≺-trans; ≺-absurd)
open import denotation.Laws.Worlds using (_⊑_; ⊑-refl; ⊑-snoc⁺; ⊑-trans; ⊕-assoc)
open import simultaneous.Instants using (_≺ⁱ_; ≺-instant; instant-≺)
open import simultaneous.Readings using (instantOf)
open import simultaneous.TakeCut using (inst-⊕)
import quickcheck.Tabled as Tb
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Listing using (listC; UncutEnv)
open import simultaneous.TableCorr using (TR)
open import simultaneous.ColdRows using (module At)
open import simultaneous.ColdOrder using (walk-under; walk-end; walk-before; walk-apart; part; ≺-flat; ≺-≢; nest2; dn2; module Ord)
open import simultaneous.ColdScan using (module Phase)
open import simultaneous.ColdRend using (module Rnd)
open import simultaneous.ListTR using (merge-tr)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; coldˢ; render)

------------------------------------------------------------------------
-- Order under positions

private
  sn : ∀ {w z} → w ⊑ z → ∀ l → w ⊑ (z ⊕ [ l ])
  sn {z = z} wz l = ⊑-trans wz (⊑-snoc⁺ z)

  -- Two subtrees apart, in their labels' order, at any depth.
  lt-⊑ : ∀ x {a b} → a <ˡ b ≡ true → ∀ {u v} → (x ⊕ [ a ]) ⊑ u → (x ⊕ [ b ]) ⊑ v → u ≺ v
  lt-⊑ x {a} {b} h (us , refl) (vs , refl) = ≺-flat (⊕-assoc x [ a ] us) (⊕-assoc x [ b ] vs) (part x us vs h)

  -- Two instants apart stay apart below.
  apart-⊕ : ∀ {x y} → x ≺ y → (instantOf x ≡ instantOf y → ⊥) → ∀ xs ys → (x ⊕ xs) ≺ (y ⊕ ys)
  apart-⊕ {x} {y} lt ne xs ys = instant-≺ (x ⊕ xs) (y ⊕ ys)
    (subst₂ _≺ⁱ_ (sym (inst-⊕ x xs)) (sym (inst-⊕ y ys)) (≺-instant x y lt ne))

------------------------------------------------------------------------
-- The elaborated cold

module Cold {A : Set} (N n : ℕ) {Δ : List Set} (ρ : All Tb.Listed Δ) (uρ : UncutEnv ρ) (m : From A 0) (P : Pos) where
  open At {A} P using (C₀; c₀; sync; sync-in; SRow; tk; cval; se-d; se-e; ae-d; ae-e; Rend; CRow; r-end; c-skp; c-end; c-val; c-lane; c-lend)

  open Rnd {A} N n ρ uρ P using (K; fR; rend-rows)
  open Ord {A} P K m using (J; T₀; inP; c₀-in; T₀-in; sync-or; sync-out; late)
  open Phase K n ρ uρ m P using (scanned; scan-rows)

  open Merge fR (TR (listC K n scanned ρ P)) using (JoinT; Done; val; step; opin; oend; opass; lane; lend; lpass; hand; left; run; rend; rpass; rhand)

  private
    lateQ : ∀ {c} → (c , end) ∈ J → sync c ≡ false → ∀ z → instantOf z ≡ instantOf P → z ≺ (c ⊕ [ ix 1 ] ⊕ [ last ])
    lateQ {c} y s z iz = ≺-trans {z} {c} {c ⊕ [ ix 1 ] ⊕ [ last ]} (late y s z iz) (dn2 c (ix 1) last)

    -- A value's place under the merge's first lane, for an end in the burst.
    under0 : ∀ {u} → (P ⊕ [ ix 0 ]) ⊑ u → (u ⊕ [ ix 1 ] ⊕ [ last ]) ≺ (P ⊕ [ last ])
    under0 {u} w = lt-⊑ P refl (sn (sn w (ix 1)) last) (⊑-refl (P ⊕ [ last ]))

    -- A value of the burst: one label under the cold.
    sync-row : ∀ {y e} → (y , e) ∈ J → sync y ≡ true → (P ⊕ [ ix 0 ]) ⊑ y
    sync-row {y} x s with walk-under K c₀ m x (trans (sync-in {y} s) (sym c₀-in))
    ... | l , refl = sn (sn (sn (sn (⊑-refl (P ⊕ [ ix 0 ])) (ix 1)) (ix 0)) (ix 1)) l

  -- Every tag's render ends before the scan does.
  srow-lane-end : ∀ {q x c} → SRow J q (out x) → SRow J c end → (q ⊕ [ ix 1 ] ⊕ [ last ]) ≺ c
  srow-lane-end tk (se-e _ _) =
    lt-⊑ P refl (sn (sn (sn (sn (⊑-refl (P ⊕ [ ix 1 ])) (ix 1)) (ix 0)) (ix 1)) last) (⊑-refl (P ⊕ [ last ]))
  srow-lane-end tk (ae-e y s) = lateQ y s (T₀ ⊕ [ ix 1 ] ⊕ [ last ]) (inP (T₀ ⊕ [ ix 1 ]) last (inP T₀ (ix 1) T₀-in))
  srow-lane-end (cval {y} x _) (se-e {c} y′ s′) with sync-or y
  ... | inj₁ s = under0 (sync-row x s)
  ... | inj₂ s = ⊥-elim (≺-absurd {y} {c} (walk-before K c₀ m y′ x tt) (late {y} x s c (sync-in {c} s′)))
  srow-lane-end (cval {y} x _) (ae-e {c} y′ s′) = ≺-flat (nest2 y (ix 1) last) (nest2 c (ix 1) last) (apart-⊕ {y} {c} lt ne (ix 1 ∷ last ∷ []) (ix 1 ∷ last ∷ []))
    where
      lt : y ≺ c
      lt = walk-before K c₀ m y′ x tt

      ne : instantOf y ≡ instantOf c → ⊥
      ne eq with sync-or y
      ... | inj₁ s = sync-out {c} s′ (trans (sym eq) (sync-in {y} s))
      ... | inj₂ s = ≺-≢ {y} {c} lt (walk-apart K c₀ m x y′ eq (λ e → sync-out {y} s (trans e c₀-in)))
  srow-lane-end (se-d _ _) (se-e _ _) =
    under0 (sn (sn (sn (sn (⊑-refl (P ⊕ [ ix 0 ])) (ix 1)) (ix 1)) (ix 1)) (ix 0))
  srow-lane-end (se-d y s) (ae-e y′ s′) with walk-end K c₀ m y y′
  ... | refl with trans (sym s) s′
  ...   | ()
  srow-lane-end (ae-d y s) (se-e y′ s′) with walk-end K c₀ m y y′
  ... | refl with trans (sym s′) s
  ...   | ()
  srow-lane-end (ae-d {c} y _) (ae-e y′ _) with walk-end K c₀ m y y′
  ... | refl = lt-⊑ (c ⊕ [ ix 1 ]) refl (sn (sn (⊑-refl (c ⊕ [ ix 1 ] ⊕ [ ix 0 ])) (ix 1)) last) (⊑-refl (c ⊕ [ ix 1 ] ⊕ [ last ]))

  private
    to-s : ∀ {k e} → TR (listC K n scanned ρ P) k e → SRow J k e
    to-s = Equivalence.to scan-rows

    fr-s : ∀ {k e} → SRow J k e → TR (listC K n scanned ρ P) k e
    fr-s = Equivalence.from scan-rows

    -- At the scan's end every part has ended.
    done : ∀ {c} → SRow J c end → Done c
    done {c} s = (c , fr-s s , ≼-refl {c})
               , λ {q} {a} x _ _ _ → q ⊕ [ ix 1 ] ⊕ [ last ] , Equivalence.from (rend-rows q a) r-end
                                   , ≺→≼ {q ⊕ [ ix 1 ] ⊕ [ last ]} {c} (srow-lane-end (to-s x) s)

    -- At a render's end the scan has not.
    undone : ∀ {q x} → SRow J q (out x) → Done (q ⊕ [ ix 1 ] ⊕ [ last ]) → ⊥
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
