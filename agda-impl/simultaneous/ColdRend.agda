{-# OPTIONS --guardedness #-}

-- A TAG'S RENDER LISTS ITS WRITTEN-OUT ROWS (`rend-rows`).  The render
-- is subscribed one step under the tag.  An early value is one `of`; a
-- late value and a late completion read a minted name off `mint`, a
-- cold of three rows: the name, the burst's close, its end.  A late
-- value's `begin`, value and `over` sit in the name's lane, which ends
-- before the mint does, so the mint's end is the render's.
--
-- The mint is walked to the same depth as every cold, so its three rows
-- are all listed only from depth three: the rows hold at `3 + N`, and
-- at a shallower walk the render lists less than `Rend`.
module simultaneous.ColdRend where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; cold; of; empty)
open import denotation.Position using (Pos; _≟ᵖ_; root; ix; last; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Den; Ended; Work; LaneOf; MapT; _≺_; _≼_;
  map-out; map-skip; map-pin; map-end; module Merge)
open import denotation.Laws.Modulus using (≼-refl; ≺→≼)
import quickcheck.Tabled as Tb
open import simultaneous.InstEmit using (InstEmit; instEmit; value; mark; begin; over)
open import simultaneous.SObs using (Tag; val; cdone; tick; lone; module Elaborate)
open import simultaneous.Listing using (listC; UncutEnv)
open import simultaneous.TableCorr using (TR)
open import simultaneous.ListTR using (laneD; ent; merge-tr; map-tr; Of1; o₀; oₑ; of1)
open import simultaneous.ColdOrder using (down; dn2; dn3; part; nest3; ≺-flat)
open import simultaneous.ColdRows using (module At)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (render)

------------------------------------------------------------------------
-- Three values

data Of3 {X : Set} (p : Pos) (x y z : X) : Pos → Ev X → Set where
  t₀ : Of3 p x y z (p ⊕ [ ix 0 ]) (out x)
  t₁ : Of3 p x y z (p ⊕ [ ix 1 ]) (out y)
  t₂ : Of3 p x y z (p ⊕ [ ix 2 ]) (out z)
  tₑ : Of3 p x y z (p ⊕ [ last ]) end

of3 : ∀ {Γ} {X : Set} K n (x y z : X) {ρ : All Tb.Listed Γ} p {k e}
  → TR (listC K n (of (x ∷ y ∷ z ∷ [])) ρ p) k e ⇔ Of3 p x y z k e
of3 K n x y z p = mk⇔
  (λ { (_ , refl , here refl) → t₀ ; (_ , refl , there (here refl)) → t₁ ; (_ , refl , there (there (here refl))) → t₂
     ; (_ , refl , there (there (there (here refl)))) → tₑ ; (_ , refl , there (there (there (there ())))) })
  (λ { t₀ → _ , refl , here refl ; t₁ → _ , refl , there (here refl) ; t₂ → _ , refl , there (there (here refl))
     ; tₑ → _ , refl , there (there (there (here refl))) })

------------------------------------------------------------------------
-- The mint's rows

data MintRow (s : Pos) : Pos → Ev Pos → Set where
  mn₀ : MintRow s (s ⊕ [ ix 0 ]) (out s)
  mn₁ : MintRow s (s ⊕ [ ix 1 ]) skip
  mnₑ : MintRow s (s ⊕ [ last ]) end

module Rnd {A : Set} (N n : ℕ) {Δ : List Set} (ρ : All Tb.Listed Δ) (uρ : UncutEnv ρ) (P : Pos) where
  open At {A} P using (Rend; r-end; r-sv; r-mn; r-mv; r-mc; r-ab; r-av; r-ao; r-ae; r-cb)

  K : ℕ
  K = 3 + N

  fR : Bool × Tag A → Den (InstEmit Pos A)
  fR = laneD K n render ρ

  Mint : Pos → EmissionSet Pos
  Mint s = TR (listC K n (cold (fresh (λ p → p))) ρ s)

  private
    mint-to : ∀ {s k e} → Mint s k e → MintRow s k e
    mint-to (_ , refl , here refl)                       = mn₀
    mint-to (_ , refl , there (here refl))               = mn₁
    mint-to (_ , refl , there (there (here refl)))       = mnₑ
    mint-to (_ , refl , there (there (there ())))

    mint-fr : ∀ {s k e} → MintRow s k e → Mint s k e
    mint-fr mn₀ = _ , refl , here refl
    mint-fr mn₁ = _ , refl , there (here refl)
    mint-fr mnₑ = _ , refl , there (there (here refl))

    mint-pin : ∀ {s k r} → MintRow s k (pin r) → ⊥
    mint-pin ()

  -- A late value's lane, under the minted name.
  fv : A → Pos → Obs Timeline Δ (InstEmit Pos A)
  fv a m = of (instEmit (mark begin) m ∷ instEmit (value a) m ∷ instEmit (mark over) m ∷ [])

  module V (a : A) (q : Pos) where
    s : Pos
    s = q ⊕ [ ix 1 ]

    L₀ : Pos
    L₀ = s ⊕ [ ix 0 ] ⊕ [ ix 1 ]

    Row3 : Pos → Ev (InstEmit Pos A) → Set
    Row3 = Of3 L₀ (instEmit (mark begin) s) (instEmit (value a) s) (instEmit (mark over) s)

    open Merge (laneD K n (fv a) ρ) (Mint s) using (JoinT; Done; val; step; opin; oend; opass; lane; lend; lpass; hand; left; run; rend; rpass; rhand)

    private
      r3-to : ∀ {k e} → TR (listC K n (fv a s) ρ L₀) k e → Row3 k e
      r3-to = Equivalence.to (of3 K n (instEmit (mark begin) s) (instEmit (value a) s) (instEmit (mark over) s) {ρ = ρ} L₀)

      r3-fr : ∀ {k e} → Row3 k e → TR (listC K n (fv a s) ρ L₀) k e
      r3-fr = Equivalence.from (of3 K n (instEmit (mark begin) s) (instEmit (value a) s) (instEmit (mark over) s) {ρ = ρ} L₀)

      r3-pin : ∀ {k r} → Row3 k (pin r) → ⊥
      r3-pin ()

      past3 : ∀ {k e} → Row3 k e → L₀ ≺ k
      past3 t₀ = down L₀ (ix 0)
      past3 t₁ = down L₀ (ix 1)
      past3 t₂ = down L₀ (ix 2)
      past3 tₑ = down L₀ last

      lane3 : ∀ {k e} → Row3 k e → LaneOf (laneD K n (fv a) ρ) (s ⊕ [ ix 0 ]) s k e
      lane3 r = ent K n (fv a s) uρ L₀ (r3-fr r) , past3 r

      -- The lane ends before the mint.
      ltE : (L₀ ⊕ [ last ]) ≺ (s ⊕ [ last ])
      ltE = ≺-flat (nest3 s (ix 0) (ix 1) last) refl (part s (ix 1 ∷ last ∷ []) [] refl)

      over-at : ∀ {c} → Ended (Mint s) c → (s ⊕ [ last ]) ≼ c
      over-at (_ , x , le) with mint-to x
      ... | mnₑ = le

      doneE : Done (s ⊕ [ last ])
      doneE = (s ⊕ [ last ] , mint-fr mnₑ , ≼-refl {s ⊕ [ last ]}) , ends
        where
          ends : ∀ {q′ b} → Mint s q′ (out b) → ⊤ → q′ ≺ (s ⊕ [ last ]) → ¬ ⊥ → Ended (LaneOf (laneD K n (fv a) ρ) q′ b) (s ⊕ [ last ])
          ends x _ _ _ with mint-to x
          ... | mn₀ = L₀ ⊕ [ last ] , lane3 tₑ , ≺→≼ {L₀ ⊕ [ last ]} {s ⊕ [ last ]} ltE

      l-work : ∀ {k e} → Row3 k e → Work e → Rend q (true , val a) k e
      l-work t₀ _ = r-ab
      l-work t₁ _ = r-av
      l-work t₂ _ = r-ao
      l-work tₑ ()

      l-end : ∀ {c} → Row3 c end → Done c → Rend q (true , val a) c end
      l-end tₑ D = ⊥-elim (over-at {L₀ ⊕ [ last ]} (proj₁ D) ltE)

      l-pass : ∀ {c} → Row3 c end → Rend q (true , val a) c skip
      l-pass tₑ = r-ae

    v-to : ∀ {k e} → JoinT k e → Rend q (true , val a) k e
    v-to (val x) with mint-to x
    ... | mn₀ = r-mn
    v-to (step x) with mint-to x
    ... | mn₁ = r-mv
    v-to (opin x) = ⊥-elim (mint-pin (mint-to x))
    v-to (oend x _) with mint-to x
    ... | mnₑ = r-end
    v-to (opass x nD) with mint-to x
    ... | mnₑ = ⊥-elim (nD doneE)
    v-to (lane x _ l _ w) with mint-to x
    ... | mn₀ = l-work (r3-to (proj₁ (proj₁ l))) w
    v-to (lend x _ l _ _ D) with mint-to x
    ... | mn₀ = l-end (r3-to (proj₁ (proj₁ l))) D
    v-to (lpass x _ l _ _ _) with mint-to x
    ... | mn₀ = l-pass (r3-to (proj₁ (proj₁ l)))
    v-to (hand _ _ _ _ ())
    v-to (left x _ l _ _) with mint-to x
    ... | mn₀ = ⊥-elim (r3-pin (r3-to (proj₁ (proj₁ l))))
    v-to (run () _)
    v-to (rend () _ _)
    v-to (rpass () _ _)
    v-to (rhand () _)

    v-fr : ∀ {k e} → Rend q (true , val a) k e → JoinT k e
    v-fr r-end = oend (mint-fr mnₑ) doneE
    v-fr r-mn  = val (mint-fr mn₀)
    v-fr r-mv  = step (mint-fr mn₁)
    v-fr r-ab  = lane (mint-fr mn₀) tt (lane3 t₀) (λ ()) tt
    v-fr r-av  = lane (mint-fr mn₀) tt (lane3 t₁) (λ ()) tt
    v-fr r-ao  = lane (mint-fr mn₀) tt (lane3 t₂) (λ ()) tt
    v-fr r-ae  = lpass (mint-fr mn₀) tt (lane3 tₑ) (λ ()) (λ ()) (λ D → over-at {L₀ ⊕ [ last ]} (proj₁ D) ltE)

  private
    -- A late completion: the minted name's `begin`.
    gb : Pos → InstEmit Pos A
    gb m = instEmit (mark begin) m

    c-to : ∀ {q k e} → MapT gb (Mint (q ⊕ [ ix 1 ])) k e → Rend q (true , cdone) k e
    c-to (map-out x) with mint-to x
    ... | mn₀ = r-cb
    c-to (map-skip x) with mint-to x
    ... | mn₁ = r-mc
    c-to (map-end x) with mint-to x
    ... | mnₑ = r-end
    c-to (map-pin x) = ⊥-elim (mint-pin (mint-to x))

    c-fr : ∀ {q k e} → Rend q (true , cdone) k e → MapT gb (Mint (q ⊕ [ ix 1 ])) k e
    c-fr r-cb  = map-out (mint-fr mn₀)
    c-fr r-mc  = map-skip (mint-fr mn₁)
    c-fr r-end = map-end (mint-fr mnₑ)

    -- An early value.
    s-to : ∀ {q a k e} → Of1 (q ⊕ [ ix 1 ]) (instEmit (value a) root) k e → Rend q (false , val a) k e
    s-to o₀ = r-sv
    s-to oₑ = r-end

    s-fr : ∀ {q a k e} → Rend q (false , val a) k e → Of1 (q ⊕ [ ix 1 ]) (instEmit (value a) root) k e
    s-fr r-sv  = o₀
    s-fr r-end = oₑ

    -- No render.
    e-to : ∀ {q x k e} → TR (listC K n (empty {A = InstEmit Pos A}) ρ (q ⊕ [ ix 1 ])) k e → Rend q x k e
    e-to (_ , refl , here refl) = r-end
    e-to (_ , refl , there ())

  rend-to : ∀ q x {k e} → TR (listC K n (render x) ρ (q ⊕ [ ix 1 ])) k e → Rend q x k e
  rend-to q (false , val a) t = s-to (Equivalence.to (of1 K n (instEmit (value a) root) {ρ = ρ} (q ⊕ [ ix 1 ])) t)
  rend-to q (true  , val a) t = V.v-to a q (Equivalence.to (merge-tr K n (fv a) (cold (fresh (λ p → p))) uρ (q ⊕ [ ix 1 ])) t)
  rend-to q (true  , cdone) t = c-to (Equivalence.to (map-tr K n gb (cold (fresh (λ p → p))) uρ (q ⊕ [ ix 1 ])) t)
  rend-to q (false , cdone) t = e-to t
  rend-to q (true  , tick)  t = e-to t
  rend-to q (false , tick)  t = e-to t

  rend-fr : ∀ q x {k e} → Rend q x k e → TR (listC K n (render x) ρ (q ⊕ [ ix 1 ])) k e
  rend-fr q (false , val a) r = Equivalence.from (of1 K n (instEmit (value a) root) {ρ = ρ} (q ⊕ [ ix 1 ])) (s-fr r)
  rend-fr q (true  , val a) r = Equivalence.from (merge-tr K n (fv a) (cold (fresh (λ p → p))) uρ (q ⊕ [ ix 1 ])) (V.v-fr a q r)
  rend-fr q (true  , cdone) r = Equivalence.from (map-tr K n gb (cold (fresh (λ p → p))) uρ (q ⊕ [ ix 1 ])) (c-fr r)
  rend-fr q (false , cdone) r-end = _ , refl , here refl
  rend-fr q (true  , tick)  r-end = _ , refl , here refl
  rend-fr q (false , tick)  r-end = _ , refl , here refl

  -- A render's rows lie under its subscription.
  rend-past : ∀ q {x k e} → Rend q x k e → (q ⊕ [ ix 1 ]) ≺ k
  rend-past q r-end = down (q ⊕ [ ix 1 ]) last
  rend-past q r-sv  = down (q ⊕ [ ix 1 ]) (ix 0)
  rend-past q r-mn  = dn2 (q ⊕ [ ix 1 ]) (ix 0) (ix 0)
  rend-past q r-mv  = down (q ⊕ [ ix 1 ]) (ix 1)
  rend-past q r-mc  = down (q ⊕ [ ix 1 ]) (ix 1)
  rend-past q r-ab  = dn3 (q ⊕ [ ix 1 ]) (ix 0) (ix 1) (ix 0)
  rend-past q r-av  = dn3 (q ⊕ [ ix 1 ]) (ix 0) (ix 1) (ix 1)
  rend-past q r-ao  = dn3 (q ⊕ [ ix 1 ]) (ix 0) (ix 1) (ix 2)
  rend-past q r-ae  = dn3 (q ⊕ [ ix 1 ]) (ix 0) (ix 1) last
  rend-past q r-cb  = down (q ⊕ [ ix 1 ]) (ix 0)

  rend-rows : ∀ q x {k e} → LaneOf fR q x k e ⇔ Rend q x k e
  rend-rows q x = mk⇔ (λ l → rend-to q x (proj₁ (proj₁ l)))
                      (λ r → ent K n (render x) uρ (q ⊕ [ ix 1 ]) (rend-fr q x r) , rend-past q r)
