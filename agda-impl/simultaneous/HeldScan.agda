{-# OPTIONS --guardedness #-}

-- A SCAN IS ITS SOURCE, ROW FOR ROW, at any subscription: each row met of
-- it is its source's row at the same position, a value folded into the
-- state before it, the end the end.  So a scan of marks that sends every
-- mark on as it came, read back through `proj₂`, holds what its source
-- holds.
module simultaneous.HeldScan where

open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; skip; pin; Den; enter; module Op; module Scan; _≼_; _≺_; Few)
open import denotation.Read using (Run; []; _∷_; Visible; After)
open import denotation.Laws.Modulus using (entered-reach; entered-few)
open import denotation.Laws.Fold using (fold)
open import adequacy.SubOne using (scan-reach)
open import simultaneous.InstEmit using (instEmit; value; mark)
open import simultaneous.SObs using (module Elaborate)
open import simultaneous.Relations using (Met)
open import simultaneous.Routed using (HeldD)
open import simultaneous.Relabel using (Same; same-mark; same-value; Rows≈; []; _∷_; ev-out; ev-end; held-same; rest-same)
open import simultaneous.HeldMap using (module MapRun; mapRows)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) using (IE; scanIE)

------------------------------------------------------------------------
-- Runs

module ScanRun {A B : Set} (f : B → A → B) (z : B) (d : Den A) (p : Pos) where
  open Scan f z (enter d p) using (Acc; acc₀; acc; ScanT; sval; sstep; spin; send)

  S : EmissionSet A
  S = enter d p

  Sc : EmissionSet B
  Sc = enter (Op.scan f z d) p

  toSc : ∀ {y e} → ScanT y e → Sc y e
  toSc x = x , scan-reach (entered-reach d p) x

  -- The value a fold stepped by, at its own position, and the state before.
  accv : ∀ {q b} → Acc q b → Σ B λ c → Σ A λ a → S q (out a) × b ≡ f c a
  accv (acc₀ x _)    = _ , _ , x , refl
  accv (acc _ x _ _) = _ , _ , x , refl

  -- A scan's value is some state stepped by its source's.
  data ScanEv : Ev B → Ev A → Set where
    so-out : ∀ {b c a} → b ≡ f c a → ScanEv (out b) (out a)
    so-end : ScanEv end end

  data ScanRows : List (Pos × Ev B) → List (Pos × Ev A) → Set where
    []  : ScanRows [] []
    _∷_ : ∀ {q e′ e rs′ rs} → ScanEv e′ e → ScanRows rs′ rs → ScanRows ((q , e′) ∷ rs′) ((q , e) ∷ rs)

  -- What is least among the scan's rows is least among the source's.
  least-src : ∀ {c q} → (∀ {k e} → Sc k e → Visible e → After c k → q ≼ k)
            → ∀ {k e} → S k e → Visible e → After c k → q ≼ k
  least-src lst {e = out _} y _ ak kq = fold f z S (entered-few d p tt y) y λ { (_ , ac) → lst (toSc (sval ac)) tt ak kq }
  least-src lst {e = end}   y _ ak    = lst (toSc (send y)) tt ak

  back : ∀ {c sc} → Run Sc c sc → Σ _ λ rx → Run S c rx × ScanRows sc rx
  back [] = [] , [] , []
  back {c} (((((sval ac , _) , prop) , _) , _ , aft , lst) ∷ run) with accv ac | back run
  ... | _ , _ , x , eq | rx , run′ , rel =
    _ ∷ rx ,
    (((x , λ y → prop (toSc (send y))) , entered-few d p tt x) , tt , aft , least-src {c} lst) ∷ run′ ,
    so-out eq ∷ rel
  back {c} (((((send y , _) , prop) , _) , _ , aft , lst) ∷ run) with back run
  ... | rx , run′ , rel =
    (_ , end) ∷ rx ,
    (((y , λ y′ → prop (toSc (send y′))) , entered-few d p tt y) , tt , aft , least-src {c} lst) ∷ run′ ,
    so-end ∷ rel
  back (((((sstep _ , _) , _) , _) , () , _) ∷ _)
  back (((((spin _ , _) , _) , _) , () , _) ∷ _)

------------------------------------------------------------------------
-- Held through a scan of marks

same-scanIE : ∀ {A B : Set} {f : B → A → B} {b} st (x : IE A) → b ≡ scanIE f st x → Same (proj₂ b) x
same-scanIE st (instEmit (value _) _) refl = same-value
same-scanIE st (instEmit (mark _) _)  refl = same-mark

held-scan-den : ∀ {A B : Set} (f : B → A → B) (z : B × IE B) (d : Den (IE A)) {W} cs → HeldD W d cs
              → HeldD W (Op.map proj₂ (Op.scan (scanIE f) z d)) cs
held-scan-den f z d cs h p ok ep = held-same row end-row back′ fwd (rest-same every back′) (h p ok ep)
  where
    module Sr = ScanRun (scanIE f) z d p
    module Mr = MapRun proj₂ (Op.scan (scanIE f) z d) p

    row : ∀ {y x′} → Mr.M y (out x′) → Σ _ λ x → Sr.S y (out x) × Same x′ x
    row m with Mr.unmap m
    ... | out _ , (Scan.sval ac , _) , refl with Sr.accv ac
    ...   | c , x , y , eq = x , y , same-scanIE c x eq

    -- Every row of the scan lies where one of its source's does.
    every : ∀ {y e′} → Mr.M y e′ → Σ _ (Sr.S y)
    every m with Mr.unmap m
    ... | _ , (Scan.sval ac , _) , _ = _ , proj₁ (proj₂ (proj₂ (Sr.accv ac)))
    ... | _ , (Scan.sstep x , _) , _ = _ , x
    ... | _ , (Scan.spin x , _) , _  = _ , x
    ... | _ , (Scan.send x , _) , _  = _ , x

    end-row : ∀ {y} → Mr.M y end → Sr.S y end
    end-row m with Mr.unmap m
    ... | end , (Scan.send y , _) , refl = y

    rows : ∀ {sc rx} → Sr.ScanRows sc rx → Rows≈ (mapRows proj₂ sc) rx
    rows Sr.[]                       = []
    rows (Sr.so-out {c = c} {x} eq Sr.∷ rel) = ev-out (same-scanIE c x eq) ∷ rows rel
    rows (Sr.so-end Sr.∷ rel)           = ev-end ∷ rows rel

    -- Every source row is the scan's, its value classically folded.
    fwd : ∀ {w} → Few Mr.M w → ∀ {k e} → Sr.S k e → k ≺ w → ¬ ¬ Σ _ λ e′ → Mr.M k e′ × (Visible e → Visible e′)
    fwd _ {e = out _} x _ no = fold (scanIE f) z Sr.S (entered-few d p tt x) x λ (_ , ac) → no (_ , Mr.lift (Sr.toSc (Scan.sval ac)) , λ _ → tt)
    fwd _ {e = skip}  x _ no = no (_ , Mr.lift (Sr.toSc (Scan.sstep x)) , λ ())
    fwd _ {e = pin _} x _ no = no (_ , Mr.lift (Sr.toSc (Scan.spin x)) , λ ())
    fwd _ {e = end}   x _ no = no (_ , Mr.lift (Sr.toSc (Scan.send x)) , λ _ → tt)

    back′ : ∀ {rs′} → Met Mr.M rs′ → Σ _ λ rs → Met Sr.S rs × Rows≈ rs′ rs
    back′ m with Mr.back m
    ... | sc , run , refl with Sr.back run
    ...   | rx , run′ , rel = rx , run′ , rows rel
