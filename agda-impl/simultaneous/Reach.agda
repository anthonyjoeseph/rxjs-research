{-# OPTIONS --guardedness #-}

-- EVERY ROW TOLD OF IS MET, classically: a visible row of a lawful
-- stream has finitely many rows before it, so the latest visible one
-- among them is met first, or none is.  Which of those rows is visible is
-- not decidable, so the run is not constructed; a conclusion that is
-- decidable, as everything read off a run's count is, may still use it.
module simultaneous.Reach where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (nothing; just)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import denotation.Events using (Pos)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; skip; pin; Den; enter; Seen; Few; _≺_; _≼_)
open import denotation.Read using (Run; []; _∷_; Visible)
open import denotation.Laws.Worlds using (InvAt)
open import denotation.Laws.Modulus using (entered-few; few-ind)
open import denotation.Laws.Fold using (latest)
open import simultaneous.Relations using (Met)
open import simultaneous.Layers using (pinby-vis; run-++; cursor-snoc)

module Reached {A : Set} {H : Pos → Set} (d : Den A) (p : Pos) (IS : InvAt H p (enter d p)) where

  S : EmissionSet A
  S = enter d p

  seen : ∀ {q e} → S q e → Visible e → Seen S q e
  seen {e = out _} x _ = (x , λ y cq → pinby-vis tt (InvAt.quiet IS y x cq)) , entered-few d p tt x
  seen {e = end}   x _ = (x , λ y cq → pinby-vis tt (InvAt.quiet IS y x cq)) , entered-few d p tt x
  seen {e = skip}  _ ()
  seen {e = pin _} _ ()

  Shown : Pos → Set
  Shown k = Σ (Ev A) λ e → S k e × Visible e

  Reaches : Pos → Set
  Reaches w = ∀ {e} → S w e → Visible e → ¬ ¬ Σ _ λ rs → Met S (rs ++ [ (w , e) ])

  reached : ∀ {w} → Few S w → Reaches w
  reached = few-ind Reaches step
    where
      step : ∀ {w} → Few S w → (∀ {v e} → S v e → v ≺ w → Reaches v) → Reaches w
      step {w} (ks , h) ih {e} x vi ¬R = latest Shown w ks λ
        { (inj₁ none) → ¬R ([] , (seen x vi , vi , tt , λ y vy _ kw → none (h y kw) (_ , y , vy) kw) ∷ [])
        ; (inj₂ (v , (ev , xv , vv) , vw , mx)) → ih xv vw xv vv λ
            { (rs , run) → ¬R (rs ++ [ (v , ev) ] ,
                run-++ run (subst (λ c → Run S c [ (w , e) ]) (sym (cursor-snoc nothing rs))
                  ((seen x vi , vi , vw , λ y vy vk kw → mx (h y kw) (_ , y , vy) kw vk) ∷ []))) } }

  -- A visible row is met at the end of some run, classically.
  reach : ∀ {w e} → S w e → Visible e → ¬ ¬ Σ _ λ rs → Met S (rs ++ [ (w , e) ])
  reach {e = out _} x vi = reached (entered-few d p tt x) x vi
  reach {e = end}   x vi = reached (entered-few d p tt x) x vi
  reach {e = skip}  _ ()
  reach {e = pin _} _ ()
