{-# OPTIONS --guardedness --large-indices #-}

-- THE ROOT'S RECORD UNDER ONE STEP: a silent step leaves it as it was; a
-- value step appends that value, at the step's time, its mark the step's
-- position.  Only `step`'s note writes the record, so every other move of
-- the driver is a record update that never names it.
module adequacy.Record where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; _++_; [_])
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Level using (lower)
open import Data.Empty using (⊥)

open import operation.AbstractObservable using (module Heap) renaming (module Machine to Shared)
open import operation.PureObservable using (Out; note; fin)
open import denotation.MonotonicList.Events using (timelineAt; done; quiet; at; emit; stall; close; Timeline; Frame∞; From∞; ix; last)
open import operation.Machine using (module Machine)

module Recording (R : Set) where
  open Heap using (same; grow)
  open Shared Timeline (Out R) using (Conf; spent?; transition; go; deliver; poll; ⟨_,_,_⟩; run; ret; held; asking; next; start; perform; stopped; closedIs)
  open Machine R using (Mach; mach; Playing; step; silent; value; feed; fed′; moved; paid; answer′; asked; starting; schedule; play; turned)

  -- The record and its marks as they were.
  Keeps : Mach → Mach → Set
  Keeps m m′ = Mach.log m′ ≡ Mach.log m × Mach.marks m′ ≡ Mach.marks m

  -- Fed: the record, its marks and the clock as they were.
  Fed : Mach → Mach → Set
  Fed m m′ = Keeps m m′ × Mach.clock m′ ≡ Mach.clock m

  schedule-keeps : ∀ m {A u} s hd now e f → Fed m (schedule m {A} {u} s hd now e f)
  schedule-keeps m s hd now e done       = (refl , refl) , refl
  schedule-keeps m s hd now e quiet      = (refl , refl) , refl
  schedule-keeps m s hd now e (at _ _ _) = (refl , refl) , refl

  starting-keeps : ∀ m {A} s hd f → Fed m (starting m {A} s hd f)
  starting-keeps m s hd (at zero _ _)    = (refl , refl) , refl
  starting-keeps m s hd (at (suc t) q b) = schedule-keeps m s hd 0 (Conf.pos (Mach.conf m) ++ [ last ]) (at (suc t) q b)
  starting-keeps m s hd done             = (refl , refl) , refl
  starting-keeps m s hd quiet            = (refl , refl) , refl

  asked-keeps : ∀ m os → Fed m (asked m os)
  asked-keeps m []                  = (refl , refl) , refl
  asked-keeps m (perform _ ∷ _)     = (refl , refl) , refl
  asked-keeps m (start c s hd ∷ _)  = starting-keeps m s hd (timelineAt c (Conf.pos (Mach.conf m)))
  asked-keeps m (stopped _ ∷ _)     = (refl , refl) , refl
  asked-keeps m (closedIs false ∷ _) = (refl , refl) , refl
  asked-keeps m (closedIs true ∷ _) with Mach.bursts m
  ... | _ ∷ _ = (refl , refl) , refl
  ... | []    = (refl , refl) , refl

  fed-keeps : ∀ m n → Fed m (fed′ m n)
  fed-keeps m (next ⟨ hp , p , c ⟩ same os) = asked-keeps (record m { conf = ⟨ hp , p , c ⟩ }) os
  fed-keeps m (next c (grow ρ) os)          = asked-keeps (moved m (next c (grow ρ) os)) os

  feed-keeps : ∀ m i → Fed m (feed m i)
  feed-keeps m i = fed-keeps m (transition (Mach.conf m) i)

  play-keeps : ∀ m b bs → Fed m (play m b bs)
  play-keeps m b bs with Playing.frame b
  ... | emit a k′ = feed-keeps (record m { bursts = just (record b { index = suc (Playing.index b) ; frame = Frame∞.force k′ ; polled = false }) ∷ bs })
                              (deliver (Playing.sink b) a (Playing.under′ b ++ [ ix (Playing.index b) ]))
  ... | stall _  = (refl , refl) , refl
  ... | close k′ = schedule-keeps (record m { bursts = bs }) (Playing.sink b) (Playing.handle b) (Playing.at′ b) (Playing.under′ b ++ [ last ]) (From∞.force k′)

  turned-keeps : ∀ m bs {m′} → turned m bs ≡ silent m′ → Keeps m m′
  turned-keeps m (nothing ∷ bs) refl = proj₁ (feed-keeps (record m { bursts = bs }) go)
  turned-keeps m (just b ∷ bs) eq with spent? (Conf.heap (Mach.conf m)) (Playing.handle b)
  turned-keeps m (just b ∷ bs) refl | true = proj₁ (feed-keeps (record m { bursts = bs }) go)
  turned-keeps m (just b ∷ bs) eq   | false with Playing.polled b
  turned-keeps m (just b ∷ bs) refl | false | true  = proj₁ (play-keeps m b bs)
  turned-keeps m (just b ∷ bs) refl | false | false = proj₁ (feed-keeps (record m { bursts = just (record b { polled = true }) ∷ bs }) (poll (Playing.sink b)))
  turned-keeps m [] eq with Mach.timers m
  turned-keeps m [] () | []
  turned-keeps m [] refl | _ ∷ _ = refl , refl

  -- The driver's turn shows no value.
  turned-silent : ∀ m bs {t p a m′} → turned m bs ≡ value t p a m′ → ⊥
  turned-silent m (nothing ∷ bs) ()
  turned-silent m (just b ∷ bs) eq with spent? (Conf.heap (Mach.conf m)) (Playing.handle b)
  turned-silent m (just b ∷ bs) () | true
  turned-silent m (just b ∷ bs) eq | false with Playing.polled b
  turned-silent m (just b ∷ bs) () | false | true
  turned-silent m (just b ∷ bs) () | false | false
  turned-silent m [] eq with Mach.timers m
  turned-silent m [] () | []
  turned-silent m [] () | _ ∷ _

  -- A silent step keeps the record.
  silent-keeps : ∀ m {m′} → step m ≡ silent m′ → Keeps m m′
  silent-keeps m@(mach ⟨ hp , p , asking (note a) k σ s ⟩ cl tm bu td lg true mk) refl = proj₁ (feed-keeps m (answer′ refl))
  silent-keeps (mach ⟨ hp , p , asking (note a) k σ s ⟩ cl tm bu td lg false mk) ()
  silent-keeps m@(mach ⟨ hp , p , asking fin k σ s ⟩ cl tm bu td lg true mk) refl = proj₁ (feed-keeps m (answer′ refl))
  silent-keeps (mach ⟨ hp , p , asking fin k σ s ⟩ cl tm bu td lg false mk) ()
  silent-keeps m@(mach ⟨ hp , p , run _ _ _ ⟩ cl tm bu td lg en mk) refl = proj₁ (feed-keeps m go)
  silent-keeps m@(mach ⟨ hp , p , ret _ _ _ ⟩ cl tm bu td lg en mk) refl = proj₁ (feed-keeps m go)
  silent-keeps m@(mach ⟨ hp , p , held _ _ ⟩ cl tm bu (t ∷ ts) lg en mk) refl = proj₁ (feed-keeps (record m { todo = ts }) (paid m t))
  silent-keeps m@(mach ⟨ hp , p , held _ _ ⟩ cl tm bu [] lg en mk) eq = turned-keeps m bu eq

  -- A value step appends its value, at its time, marked at its position,
  -- and leaves the clock at that time.
  value-notes : ∀ m {t p a m′} → step m ≡ value t p a m′ → (Mach.log m′ ≡ Mach.log m ++ [ (t , a) ] × Mach.marks m′ ≡ Mach.marks m ++ [ p ]) × Mach.clock m′ ≡ t
  value-notes (mach ⟨ hp , p , asking (note a) k σ s ⟩ cl tm bu td lg true mk) ()
  value-notes m@(mach ⟨ hp , p , asking (note a) k σ s ⟩ cl tm bu td lg false mk) refl = feed-keeps (record m { log = lg ++ [ (cl , a) ] ; marks = mk ++ [ p ] }) (answer′ refl)
  value-notes (mach ⟨ hp , p , asking fin k σ s ⟩ cl tm bu td lg true mk) ()
  value-notes (mach ⟨ hp , p , asking fin k σ s ⟩ cl tm bu td lg false mk) ()
  value-notes (mach ⟨ hp , p , run _ _ _ ⟩ cl tm bu td lg en mk) ()
  value-notes (mach ⟨ hp , p , ret _ _ _ ⟩ cl tm bu td lg en mk) ()
  value-notes (mach ⟨ hp , p , held _ _ ⟩ cl tm bu (t ∷ ts) lg en mk) ()
  value-notes m@(mach ⟨ hp , p , held _ _ ⟩ cl tm bu [] lg en mk) eq with turned-silent m bu eq
  ... | ()
