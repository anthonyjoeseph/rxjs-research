{-# OPTIONS --guardedness #-}

-- A SUBSCRIBE KEEPS APART: whatever a subscription at `p` comes to owe
-- sits under `p` — its values and end, its cut, a connect's source, a
-- cold's first frame or the timer cascade after it — so inside the run.
module adequacy.Apart.Begin where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; [_])
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Binary.Permutation.Propositional using (↭-refl)
open import Data.List.Relation.Binary.Sublist.Propositional using (⊆-refl)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (m<m+n)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)

open import Tree using (cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer; Later)
open import denotation.Position using (Label; ix; last; tick; root; nested; fired; _▸_; _⊕_)
open import denotation.Events using (Frame; timelineAt; done; quiet; at)
open import denotation.Simultaneity using (effect-tick)
open import operation.PureObservable using (PureObs; module Machine; play; ending; over; baseOf; stepOf)
open Machine using (Ctx; inBody; St; pend; coldS; ofS; mapS; scanS; cutS; takeS; flatS; connS; joinS; cs; attAt; free;
                    closedUp; scopeOf; subscribing; absorbed; begin)
open import adequacy.Apart.Cone using (Cone; tag; cone-trans; cone-up) renaming (pre to under)
open import adequacy.Apart.Region using (cn; tl; pt; bk; cl; Sub; sub-refl; sub-down; sub-pt; sub-bk; sub-cl; f-tl; self)
open import adequacy.Apart.Kit using (W; AS; stay; quit; grow; cl-pt; cl-cn; sub-child; sub-vals; sub-frame; base-in)

-- A timer cascade a cold subscribed at `p` fires, under `p`.
sub-cascade : ∀ {A p w} T (fr : Frame A w) → tick (p ⊕ [ last ]) < T
            → Sub (tl (baseOf (fired T (p ⊕ [ last ])) fr) (stepOf 0 fr)) (cl p)
sub-cascade {p = p} T fr lt = sub-cl (f-tl _ _) (λ y iy → inc (base-in fr iy)) (λ iy → out (base-in fr iy))
  where
    e = p ⊕ [ last ]
    inc : ∀ {y} → (Σ Label λ l → Σ (List Label) λ ls → Cone (fired T e ▸ l ⊕ ls) y) → Cone p y
    inc (l , ls , c) = cone-trans (tag ls lt (under [ last ])) c
    out : (Σ Label λ l → Σ (List Label) λ ls → Cone (fired T e ▸ l ⊕ ls) p) → ⊥
    out (l , ls , c) = cone-up last [] (cone-trans (tag ls lt (self e)) c)

module _ {R : Set} where
  begin-ap : ∀ {Γ A} (c : Ctx R Γ A) (o : PureObs Γ A) p → W c (pend o p) [ cl p ] → AS (begin c o p)
  begin-ap c (cold x) p h with timelineAt x p
  ... | done = grow c {t = pend (cold x) p} {t′ = coldS true (ending (p ⊕ [ last ]))} p [] [ cn (p ⊕ [ last ]) ] [] [] ↭-refl ↭-refl
                 (sub-child last ∷ []) ([] ∷ []) h
  ... | quiet = quit c {t = pend (cold x) p} {t′ = coldS true over} ⊆-refl h
  ... | at zero _ b = grow c {t = pend (cold x) p} {t′ = coldS true (play (tick p) (nested p) 0 0 b)} p [] [ tl (baseOf (nested p) b) (stepOf 0 b) ] [] [] ↭-refl ↭-refl
                        (sub-frame b ∷ []) ([] ∷ []) h
  ... | at (suc t) le b =
    grow c {t = pend (cold x) p} {t′ = coldS true (play (tick p) (fired (tick p + suc t) (p ⊕ [ last ])) 0 (suc t) b)} p []
      [ tl (baseOf (fired (tick p + suc t) (p ⊕ [ last ])) b) (stepOf 0 b) ] [] [] ↭-refl ↭-refl
      (sub-cascade (tick p + suc t) b (subst (_< tick p + suc t) (sym (effect-tick p [ last ])) (m<m+n (tick p) (s≤s z≤n))) ∷ []) ([] ∷ []) h
  begin-ap c empty p h =
    grow c {t = pend empty p} {t′ = ofS 0 p []} p [] [ cn (p ⊕ [ last ]) ] [] [] ↭-refl ↭-refl (sub-child last ∷ []) ([] ∷ []) h
  begin-ap c (of []) p h =
    grow c {t = pend (of []) p} {t′ = ofS 0 p []} p [] [ cn (p ⊕ [ last ]) ] [] [] ↭-refl ↭-refl (sub-child last ∷ []) ([] ∷ []) h
  begin-ap c (of (x ∷ xs)) p h =
    grow c {t = pend (of (x ∷ xs)) p} {t′ = ofS 0 p (x ∷ xs)} p [] [ tl (nested p) 0 ] [] [] ↭-refl ↭-refl (sub-vals 0 ∷ []) ([] ∷ []) h
  begin-ap c (map f s) p h = stay c {t = pend (map f s) p} {t′ = mapS f (pend s p)} subscribing ⊆-refl h
  begin-ap c (scan f z s) p h = stay c {t = pend (scan f z s) p} {t′ = scanS f z (pend s p)} subscribing ⊆-refl h
  begin-ap c (takeWhile i q s) p h =
    grow c {t = pend (takeWhile i q s) p} {t′ = takeS i q free (cutS true (attAt p) (pend s p))} p [ cl p ] [ pt p ] [] [] ↭-refl ↭-refl
      (sub-refl (cl p) ∷ sub-pt (self p) ∷ []) ((cl-pt ∷ []) ∷ [] ∷ []) h
  begin-ap c (flatMap op f s) p h =
    grow c {t = pend (flatMap op f s) p} {t′ = flatS op f (s , p) false 0 [] (cutS true (attAt p) (pend s p)) []} p [ cl p ] [ pt p ] [] [] ↭-refl ↭-refl
      (sub-refl (cl p) ∷ sub-pt (self p) ∷ []) ((cl-pt ∷ []) ∷ [] ∷ []) h
  begin-ap c (connect s b) p h =
    grow c {t = pend (connect s b) p} {t′ = connS (cs false true false (just p) nothing nothing p root s (scopeOf c)) (pend s (p ⊕ [ ix 1 ])) (pend b (p ⊕ [ ix 0 ]))}
      p [ cl (p ⊕ [ ix 0 ]) ] [ cn (p ⊕ [ ix 1 ]) ] [] [] ↭-refl ↭-refl
      (sub-down (ix 0) ∷ sub-child (ix 1) ∷ []) ((cl-cn refl ∷ []) ∷ [] ∷ []) h
  begin-ap c (connected x) p h with closedUp c x
  ... | true  = grow c {t = pend (connected x) p} {t′ = ofS 0 p []} p [] [ cn (p ⊕ [ last ]) ] [] [] ↭-refl ↭-refl (sub-child last ∷ []) ([] ∷ []) h
  ... | false = grow c {t = pend (connected x) p} {t′ = joinS p true x []} p [] [ bk p ] [] [] ↭-refl ↭-refl (sub-bk ∷ []) ([] ∷ []) h
  begin-ap c (defer l) p h =
    grow c {t = pend (defer l) p} {t′ = pend (Later.force l) (p ⊕ [ ix 1 ])} p [ cl (p ⊕ [ ix 1 ]) ] [] [] [] ↭-refl ↭-refl
      (sub-down (ix 1) ∷ []) ([] ∷ []) h
