{-# OPTIONS --guardedness #-}

-- WHAT A SUBSCRIPTION ENTERS: a merge entered is the merge part way
-- through with nothing begun, read as entered.
module adequacy.Enter where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Maybe using (nothing; just)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Unit using (tt)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ; map; scan; flatMap)
open import denotation.Events using (Pos; Timeline)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; pin; end; Reach; PDep; enter; ⟦_⟧; DenEnv;
  MapT; map-out; map-skip; map-pin; map-end; module Scan; module Joining)
open import denotation.Laws.Modulus using (reach-via; entered-reach)
open import adequacy.Rows using (acc-val; ∅; pendRows; reads; _≃_; _⇄_; module Flat; module BoundedF; module SwitchF; module ExhaustF)
open import adequacy.Up using (trunc-≃)

open _≃_

-- Two joiners on one outer and like lane readings, with the same begun
-- rows and over at the same places: the same rows.
module _ {A B : Set} {Lane Lane′ : Pos → A → EmissionSet B} {O : EmissionSet A} {Bg Bg′ : EmissionSet B} {Over Over′ : Pos → Set}
         {Runs : Pos → Set} {Cut : Pos → Pos → Set} {Hand : Pos → Set}
         (ln : ∀ {q a} → Lane q a ≃ Lane′ q a) (bg : Bg ≃ Bg′) (ov : ∀ {c} → Over c → Over′ c) (vo : ∀ {c} → Over′ c → Over c) where
  private
    module X = Joining Lane O Bg Over Runs Cut Hand
    module Y = Joining Lane′ O Bg′ Over′ Runs Cut Hand

    xy : ∀ {c} → X.Done c → Y.Done c
    xy (o , h) = ov o , λ x r lt nc → let (c₀ , e , le) = h x r lt nc in c₀ , to ln e , le

    yx : ∀ {c} → Y.Done c → X.Done c
    yx (o , h) = vo o , λ x r lt nc → let (c₀ , e , le) = h x r lt nc in c₀ , from ln e , le

  joining-≃ : X.JoinT ≃ Y.JoinT
  joining-≃ = fwd ⇄ bwd
    where
      fwd : ∀ {k e} → X.JoinT k e → Y.JoinT k e
      fwd (X.val x)             = Y.val x
      fwd (X.step x)            = Y.step x
      fwd (X.opin x)            = Y.opin x
      fwd (X.oend x d)          = Y.oend x (xy d)
      fwd (X.opass x nd)        = Y.opass x λ d → nd (yx d)
      fwd (X.lane x r l nc w)   = Y.lane x r (to ln l) nc w
      fwd (X.lend x r l nc nh d)   = Y.lend x r (to ln l) nc nh (xy d)
      fwd (X.lpass x r l nc nh nd) = Y.lpass x r (to ln l) nc nh λ d → nd (yx d)
      fwd (X.hand x r l nc h)      = Y.hand x r (to ln l) nc h
      fwd (X.left x r l c i)    = Y.left x r (to ln l) c i
      fwd (X.run x w)           = Y.run (to bg x) w
      fwd (X.rend x nh d)       = Y.rend (to bg x) nh (xy d)
      fwd (X.rpass x nh nd)     = Y.rpass (to bg x) nh λ d → nd (yx d)
      fwd (X.rhand x h)         = Y.rhand (to bg x) h
      bwd : ∀ {k e} → Y.JoinT k e → X.JoinT k e
      bwd (Y.val x)             = X.val x
      bwd (Y.step x)            = X.step x
      bwd (Y.opin x)            = X.opin x
      bwd (Y.oend x d)          = X.oend x (yx d)
      bwd (Y.opass x nd)        = X.opass x λ d → nd (xy d)
      bwd (Y.lane x r l nc w)   = X.lane x r (from ln l) nc w
      bwd (Y.lend x r l nc nh d)   = X.lend x r (from ln l) nc nh (yx d)
      bwd (Y.lpass x r l nc nh nd) = X.lpass x r (from ln l) nc nh λ d → nd (xy d)
      bwd (Y.hand x r l nc h)      = X.hand x r (from ln l) nc h
      bwd (Y.left x r l c i)    = X.left x r (from ln l) c i
      bwd (Y.run x w)           = X.run (from bg x) w
      bwd (Y.rend x nh d)       = X.rend (from bg x) nh (yx d)
      bwd (Y.rpass x nh nd)     = X.rpass (from bg x) nh λ d → nd (xy d)
      bwd (Y.rhand x h)         = X.rhand (from bg x) h

-- A merge with no outer rows and no lane begun: no rows.
flat-∅ : ∀ {A B} (L : A → Pos → EmissionSet B) d → Flat.RowT L ∅ d [] ≃ ∅
flat-∅ L d = (λ (r , _) → to′ r) ⇄ λ ()
  where
    to′ : ∀ {k e} → Flat.JoinT L ∅ d [] k e → ⊥
    to′ (Flat.val ())
    to′ (Flat.step ())
    to′ (Flat.opin ())
    to′ (Flat.oend () _)
    to′ (Flat.opass () _)
    to′ (Flat.lane () _ _ _ _)
    to′ (Flat.lend () _ _ _ _ _)
    to′ (Flat.lpass () _ _ _ _ _)
    to′ (Flat.hand () _ _ _ _)
    to′ (Flat.left () _ _ _ _)
    to′ (Flat.run () _)
    to′ (Flat.rend () _ _)
    to′ (Flat.rpass () _ _)
    to′ (Flat.rhand () _)

-- A JOINER WITH NO OUTER ROWS, NOTHING BEGUN AND NOTHING QUEUED: no rows.
switch-∅ : ∀ {A B} (L : A → Pos → EmissionSet B) d n → SwitchF.RowT L ∅ d n [] ≃ ∅
switch-∅ L d n = (λ (r , _) → to′ r) ⇄ λ ()
  where
    to′ : ∀ {k e} → SwitchF.JoinT L ∅ d n [] k e → ⊥
    to′ (SwitchF.val ())
    to′ (SwitchF.step ())
    to′ (SwitchF.opin ())
    to′ (SwitchF.oend () _)
    to′ (SwitchF.opass () _)
    to′ (SwitchF.lane () _ _ _ _)
    to′ (SwitchF.lend () _ _ _ _ _)
    to′ (SwitchF.lpass () _ _ _ _ _)
    to′ (SwitchF.hand () _ _ _ _)
    to′ (SwitchF.left () _ _ _ _)
    to′ (SwitchF.run (SwitchF.bg () _) _)
    to′ (SwitchF.rend (SwitchF.bg () _) _ _)
    to′ (SwitchF.rpass (SwitchF.bg () _) _ _)
    to′ (SwitchF.rhand (SwitchF.bg () _) _)
    to′ (SwitchF.run (SwitchF.bpin () _ _) _)

exhaust-∅ : ∀ {A B} (L : A → Pos → EmissionSet B) d n → ExhaustF.RowT L ∅ d n [] ≃ ∅
exhaust-∅ L d n = (λ (r , _) → to′ r) ⇄ λ ()
  where
    to′ : ∀ {k e} → ExhaustF.JoinT L ∅ d n [] k e → ⊥
    to′ (ExhaustF.val ())
    to′ (ExhaustF.step ())
    to′ (ExhaustF.opin ())
    to′ (ExhaustF.oend () _)
    to′ (ExhaustF.opass () _)
    to′ (ExhaustF.lane () _ _ _ _)
    to′ (ExhaustF.lend () _ _ _ _ _)
    to′ (ExhaustF.lpass () _ _ _ _ _)
    to′ (ExhaustF.hand () _ _ _ _)
    to′ (ExhaustF.left () _ _ _ _)
    to′ (ExhaustF.run () _)
    to′ (ExhaustF.rend () _ _)
    to′ (ExhaustF.rpass () _ _)
    to′ (ExhaustF.rhand () _)

bounded-∅ : ∀ {A B} m (L : A → Pos → EmissionSet B) d n → BoundedF.RowT m L ∅ d n [] [] ≃ ∅
bounded-∅ m L d n = (λ (r , _) → to′ r) ⇄ λ ()
  where
    to′ : ∀ {k e} → BoundedF.JoinT m L ∅ d n [] [] k e → ⊥
    to′ (BoundedF.val ())
    to′ (BoundedF.step ())
    to′ (BoundedF.opin ())
    to′ (BoundedF.oend () _)
    to′ (BoundedF.opass () _)
    to′ (BoundedF.lane () _ _ _ _)
    to′ (BoundedF.lend () _ _ _ _ _)
    to′ (BoundedF.lpass () _ _ _ _ _)
    to′ (BoundedF.hand () _ _ _ _)
    to′ (BoundedF.left () _ _ _ _)
    to′ (BoundedF.run (BoundedF.begun ()) _)
    to′ (BoundedF.rend (BoundedF.begun ()) _ _)
    to′ (BoundedF.rpass (BoundedF.begun ()) _ _)
    to′ (BoundedF.rhand (BoundedF.begun ()) _)
    to′ (BoundedF.run (BoundedF.waits (BoundedF.queued () , _) _) _)
    to′ (BoundedF.rend (BoundedF.waits (BoundedF.queued () , _) _) _ _)
    to′ (BoundedF.rpass (BoundedF.waits (BoundedF.queued () , _) _) _ _)
    to′ (BoundedF.rhand (BoundedF.waits (BoundedF.queued () , _) _) _)

-- A BOUNDED MERGE, A SWITCH, AN EXHAUST ENTERED: the joiner part way
-- through at its outer entered, not done, nothing begun or queued.
postulate
  enter-bounded : ∀ {Γ A B} (ρ : DenEnv Γ) m (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p
                → pendRows ρ (flatMap (mergeᶠ (just m)) f s) p ≃ BoundedF.RowT m (λ a → pendRows ρ (f a)) (pendRows ρ s p) false 0 [] []
  enter-switch  : ∀ {Γ A B} (ρ : DenEnv Γ) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p
                → pendRows ρ (flatMap switchᶠ f s) p ≃ SwitchF.RowT (λ a → pendRows ρ (f a)) (pendRows ρ s p) false 0 []
  enter-exhaust : ∀ {Γ A B} (ρ : DenEnv Γ) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p
                → pendRows ρ (flatMap exhaustᶠ f s) p ≃ ExhaustF.RowT (λ a → pendRows ρ (f a)) (pendRows ρ s p) false 0 []

-- A MAP ENTERED: its source entered, mapped.
enter-map : ∀ {Γ A B} (ρ : DenEnv Γ) (f : A → B) (s : Obs Timeline Γ A) p → pendRows ρ (map f s) p ≃ MapT f (pendRows ρ s p)
enter-map ρ f s p = proj₁ ⇄ λ x → x , reach′ x
  where
    t = enter (⟦ s ⟧ ρ) p

    src : ∀ {k e} → MapT f t k e → Σ (Ev _) (t k)
    src (map-out y)  = _ , y
    src (map-skip y) = _ , y
    src (map-pin y)  = _ , y
    src (map-end y)  = _ , y

    -- A pin's source row is the same pin.
    pd : ∀ {k e r} (x : MapT f t k e) → PDep r k e → PDep r k (proj₁ (src x))
    pd x            (inj₁ kr)   = inj₁ kr
    pd (map-pin y)  (inj₂ refl) = inj₂ refl
    pd (map-out y)  (inj₂ ())
    pd (map-skip y) (inj₂ ())
    pd (map-end y)  (inj₂ ())

    reach′ : ∀ {q e} → MapT f t q e → Reach (MapT f t) q e
    reach′ (map-out {a = a} y) = reach-via {e = out (f a)} {out a} (λ x _ _ → proj₁ (src x) , proj₂ (src x) , tt) (entered-reach (⟦ s ⟧ ρ) p y)
    reach′ (map-skip y) = reach-via {e = skip} {skip} (λ x _ _ → proj₁ (src x) , proj₂ (src x) , tt) (entered-reach (⟦ s ⟧ ρ) p y)
    reach′ (map-end y)  = reach-via {e = end} {end} (λ x _ _ → proj₁ (src x) , proj₂ (src x) , tt) (entered-reach (⟦ s ⟧ ρ) p y)
    reach′ (map-pin {r = r} y) = reach-via {e = pin r} {pin r} (λ x _ d → proj₁ (src x) , proj₂ (src x) , λ i → pd x (d i)) (entered-reach (⟦ s ⟧ ρ) p y)

-- A MERGE ENTERED: the merge part way through, at its outer entered, not
-- done, nothing begun.
enter-merge : ∀ {Γ A B} (ρ : DenEnv Γ) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p
            → pendRows ρ (flatMap (mergeᶠ nothing) f s) p ≃ Flat.RowT (λ a → pendRows ρ (f a)) (pendRows ρ s p) false []
enter-merge ρ f s p =
  trunc-≃ (joining-≃ ((λ (l , p) → reads l p) ⇄ λ (reads l p) → l , p) ((λ ()) ⇄ λ ()) (λ e → inj₂ e , tt) λ { (inj₁ () , _) ; (inj₂ e , _) → e })

-- A SCAN ENTERED: its source entered, scanned.
enter-scan : ∀ {Γ A B} (ρ : DenEnv Γ) (f : B → A → B) z (s : Obs Timeline Γ A) p → pendRows ρ (scan f z s) p ≃ Scan.ScanT f z (pendRows ρ s p)
enter-scan ρ f z s p = proj₁ ⇄ λ x → x , reach′ x
  where
    t = enter (⟦ s ⟧ ρ) p

    src : ∀ {k e} → Scan.ScanT f z t k e → Σ (Ev _) (t k)
    src (Scan.sval a)  = _ , proj₂ (acc-val a)
    src (Scan.sstep y) = _ , y
    src (Scan.spin y)  = _ , y
    src (Scan.send y)  = _ , y

    -- A pin's source row is the same pin.
    pd : ∀ {k e r} (x : Scan.ScanT f z t k e) → PDep r k e → PDep r k (proj₁ (src x))
    pd x             (inj₁ kr)   = inj₁ kr
    pd (Scan.spin y) (inj₂ refl) = inj₂ refl
    pd (Scan.sval y)  (inj₂ ())
    pd (Scan.sstep y) (inj₂ ())
    pd (Scan.send y)  (inj₂ ())

    reach′ : ∀ {q e} → Scan.ScanT f z t q e → Reach (Scan.ScanT f z t) q e
    reach′ (Scan.sval {b = b} a) = reach-via {e = out b} {out (proj₁ (acc-val a))} (λ x _ _ → proj₁ (src x) , proj₂ (src x) , tt) (entered-reach (⟦ s ⟧ ρ) p (proj₂ (acc-val a)))
    reach′ (Scan.sstep y) = reach-via {e = skip} {skip} (λ x _ _ → proj₁ (src x) , proj₂ (src x) , tt) (entered-reach (⟦ s ⟧ ρ) p y)
    reach′ (Scan.send y)  = reach-via {e = end} {end} (λ x _ _ → proj₁ (src x) , proj₂ (src x) , tt) (entered-reach (⟦ s ⟧ ρ) p y)
    reach′ (Scan.spin {r = r} y) = reach-via {e = pin r} {pin r} (λ x _ d → proj₁ (src x) , proj₂ (src x) , λ i → pd x (d i)) (entered-reach (⟦ s ⟧ ρ) p y)
