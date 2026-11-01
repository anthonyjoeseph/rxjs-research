{-# OPTIONS --guardedness #-}

-- A SUBSCRIBE KEEPS APART: whatever a subscription at `p` comes to owe
-- sits under `p` — its values and end, its cut, a connect's source, a
-- cold's first frame or the timer cascade after it — so inside the run.
module adequacy.Apart.Begin where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; [_]; _++_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Binary.Permutation.Propositional using (↭-refl)
open import Data.List.Relation.Binary.Sublist.Propositional using (⊆-refl)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (m<m+n)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)

open import Tree using (cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer; Later)
open import denotation.Events using (Pos; ix; last; tick; root; timelineAt; done; quiet; at) renaming (sub to subᴾ)
open import operation.PureObservable using (PureObs; module Machine; play; ending; over)
open Machine using (Ctx; inBody; St; pend; coldS; ofS; mapS; scanS; cutS; takeS; flatS; connS; joinS; cs; attAt; free;
                    closedUp; scopeOf; subscribing; absorbed; begin)
open import adequacy.Stamped using (Ix)
open import adequacy.Apart.Cone using (Cone; tag; cone-trans; cone-up) renaming (pre to under)
open import adequacy.Apart.Region using (cn; tl; pt; bk; cl; In; Sub; sub-refl; sub-down; sub-pt; sub-bk; sub-cl; f-tl; self)
open import adequacy.Apart.Kit using (W; AS; stay; quit; grow; cl-pt; cl-cn; sub-child; sub-vals; tick-ix)

-- A timer cascade a cold subscribed at `p` fires, under `p`.
sub-cascade : ∀ {p} T → Ix p → tick (p ++ [ last ]) < T → Sub (tl (ix T ∷ subᴾ (p ++ [ last ]) ∷ []) 0) (cl p)
sub-cascade {p} T hp lt = sub-cl hp (f-tl _ 0) inc out
  where
    e = p ++ [ last ]
    inc : ∀ y → In (tl (ix T ∷ subᴾ e ∷ []) 0) y → Cone p y
    inc y (inj₁ (j , _ , c)) = cone-trans (tag [ ix j ] lt (under [ last ])) c
    inc y (inj₂ c)           = cone-trans (tag [ last ] lt (under [ last ])) c
    out : In (tl (ix T ∷ subᴾ e ∷ []) 0) p → _
    out (inj₁ (j , _ , c)) = cone-up last [] (cone-trans (tag [ ix j ] lt (self e)) c)
    out (inj₂ c)           = cone-up last [] (cone-trans (tag [ last ] lt (self e)) c)

module _ {R : Set} where
  begin-ap : ∀ {Γ A} (c : Ctx R Γ A) (o : PureObs Γ A) p → Ix p → W c (pend o p) [ cl p ] → AS (begin c o p)
  begin-ap c (cold x) p hp h with timelineAt x p
  ... | done = grow c {t = pend (cold x) p} {t′ = coldS true (ending (p ++ [ last ]))} p [] [ cn (p ++ [ last ]) ] [] [] ↭-refl ↭-refl
                 (sub-child last hp ∷ []) ([] ∷ []) h
  ... | quiet = quit c {t = pend (cold x) p} {t′ = coldS true over} ⊆-refl h
  ... | at zero _ b = grow c {t = pend (cold x) p} {t′ = coldS true (play (tick p) p 0 0 b)} p [] [ tl p 0 ] [] [] ↭-refl ↭-refl
                        (sub-vals 0 hp ∷ []) ([] ∷ []) h
  ... | at (suc t) le b =
    grow c {t = pend (cold x) p} {t′ = coldS true (play (tick p) (ix (tick p + suc t) ∷ subᴾ (p ++ [ last ]) ∷ []) 0 (suc t) b)} p []
      [ tl (ix (tick p + suc t) ∷ subᴾ (p ++ [ last ]) ∷ []) 0 ] [] [] ↭-refl ↭-refl
      (sub-cascade (tick p + suc t) hp (subst (_< tick p + suc t) (sym (tick-ix p [ last ] hp)) (m<m+n (tick p) (s≤s z≤n))) ∷ []) ([] ∷ []) h
  begin-ap c empty p hp h =
    grow c {t = pend empty p} {t′ = ofS 0 p []} p [] [ cn (p ++ [ last ]) ] [] [] ↭-refl ↭-refl (sub-child last hp ∷ []) ([] ∷ []) h
  begin-ap c (of []) p hp h =
    grow c {t = pend (of []) p} {t′ = ofS 0 p []} p [] [ cn (p ++ [ last ]) ] [] [] ↭-refl ↭-refl (sub-child last hp ∷ []) ([] ∷ []) h
  begin-ap c (of (x ∷ xs)) p hp h =
    grow c {t = pend (of (x ∷ xs)) p} {t′ = ofS 0 p (x ∷ xs)} p [] [ tl p 0 ] [] [] ↭-refl ↭-refl (sub-vals 0 hp ∷ []) ([] ∷ []) h
  begin-ap c (map f s) p hp h = stay c {t = pend (map f s) p} {t′ = mapS f (pend s p)} subscribing ⊆-refl h
  begin-ap c (scan f z s) p hp h = stay c {t = pend (scan f z s) p} {t′ = scanS f z (pend s p)} subscribing ⊆-refl h
  begin-ap c (takeWhile i q s) p hp h =
    grow c {t = pend (takeWhile i q s) p} {t′ = takeS i q free (cutS true (attAt p) (pend s p))} p [ cl p ] [ pt p ] [] [] ↭-refl ↭-refl
      (sub-refl (cl p) ∷ sub-pt (self p) ∷ []) ((cl-pt ∷ []) ∷ [] ∷ []) h
  begin-ap c (flatMap op f s) p hp h =
    grow c {t = pend (flatMap op f s) p} {t′ = flatS op f false 0 [] (cutS true (attAt p) (pend s p)) []} p [ cl p ] [ pt p ] [] [] ↭-refl ↭-refl
      (sub-refl (cl p) ∷ sub-pt (self p) ∷ []) ((cl-pt ∷ []) ∷ [] ∷ []) h
  begin-ap c (connect s b) p hp h =
    grow c {t = pend (connect s b) p} {t′ = connS (cs false true false (just p) nothing nothing p root s (scopeOf c)) (pend s (p ++ [ ix 1 ])) (pend b (p ++ [ ix 0 ]))}
      p [ cl (p ++ [ ix 0 ]) ] [ cn (p ++ [ ix 1 ]) ] [] [] ↭-refl ↭-refl
      (sub-down (ix 0) hp ∷ sub-child (ix 1) hp ∷ []) ((cl-cn hp refl ∷ []) ∷ [] ∷ []) h
  begin-ap c (connected x) p hp h with closedUp c x
  ... | true  = grow c {t = pend (connected x) p} {t′ = ofS 0 p []} p [] [ cn (p ++ [ last ]) ] [] [] ↭-refl ↭-refl (sub-child last hp ∷ []) ([] ∷ []) h
  ... | false = grow c {t = pend (connected x) p} {t′ = joinS p true x []} p [] [ bk p ] [] [] ↭-refl ↭-refl (sub-bk ∷ []) ([] ∷ []) h
  begin-ap c (defer l) p hp h =
    grow c {t = pend (defer l) p} {t′ = pend (Later.force l) (p ++ [ ix 1 ])} p [ cl (p ++ [ ix 1 ]) ] [] [] [] ↭-refl ↭-refl
      (sub-down (ix 1) hp ∷ []) ([] ∷ []) h
