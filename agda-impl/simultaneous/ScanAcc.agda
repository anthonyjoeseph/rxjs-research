{-# OPTIONS --guardedness #-}

-- A SCAN'S FOLD AT A VALUE IS THE FOLD OF A RUN MET UP TO IT.  The fold
-- names the values before it in order, each the least past the last, and
-- a lawful stream ends past every value, so they are what a subscriber
-- meets.
module simultaneous.ScanAcc where

open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Properties using (foldl-++)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import denotation.Position using (Pos)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; Few; _≺_; _≼_; module Scan)
open import denotation.Read using (Run; _∷_; []; Visible)
open import denotation.Laws.Worlds using (InvAt)
open import simultaneous.Relations using (Met; values; values-++)
open import simultaneous.Layers using (pinby-vis; run-++; cursor-snoc)

module AccRun {A B : Set} (f : B → A → B) (z : B) {H : Pos → Set} {P : Pos} {S : EmissionSet A} (IS : InvAt H P S)
              (few : ∀ {q e} → S q e → Visible e → Few S q) where
  open Scan f z S using (Acc; acc₀; acc)

  -- A value lies before the end.
  val-end : ∀ {q a c} → S q (out a) → S c end → q ≼ c
  val-end x ce cq = pinby-vis tt (InvAt.quiet IS ce x cq)

  acc-run : ∀ {q b} → Acc q b
          → Σ (List (Pos × Ev A)) λ rx → Σ A λ a → S q (out a) × Met S (rx ++ [ (q , out a) ]) × b ≡ f (L.foldl f z (values rx)) a
  acc-run (acc₀ {q} {a} x mn) = [] , a , x , (((x , val-end x) , few x tt) , tt , tt , least) ∷ [] , refl
    where
      least : ∀ {k e} → S k e → Visible e → ⊤ → q ≼ k
      least {e = out _} y _ _ = mn y
      least {e = end}   y _ _ = val-end x y
  acc-run (acc {q} {b} {q′} {a′} ac x lt nx) with acc-run ac
  ... | rx , a , _ , run , eq =
    rx ++ [ (q , out a) ] , a′ , x ,
    run-++ run (subst (λ c → Run S c [ (q′ , out a′) ]) (sym (cursor-snoc _ rx)) ((((x , val-end x) , few x tt) , tt , lt , least) ∷ [])) ,
    cong (λ w → f w a′) (trans eq (sym (trans (cong (L.foldl f z) (values-++ rx [ (q , out a) ])) (foldl-++ f z (values rx) [ a ]))))
    where
      least : ∀ {k e} → S k e → Visible e → q ≺ k → q′ ≼ k
      least {e = out _} y _ qk = nx y qk
      least {e = end}   y _ _  = val-end x y
