{-# OPTIONS --guardedness #-}

-- FLATMAP'S SCAN PARKS ONLY ON A CONNECT HOLDING A ROUTE (`past-park`).
-- A cut parks routes only while a connect in scope holds one of the
-- instant; a tracker's row that leaves none holding unparks them all;
-- a new instant and an over start with none parked; every other step
-- leaves the instant, the trackers and what is parked alone.  So it
-- holds of every state the scan reaches, whatever it read.
module simultaneous.FlatPark where

open import Data.Bool using (true; false; _∧_; _∨_; if_then_else_)
open import Data.Maybe using (just; nothing)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc; _+_; _∸_; _⊓_)
open import Data.Product using (proj₁; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (out; end; skip; pin)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; stop; over; outerOpen; outerClose; laneStart; carry; laneDone;
  burstEnd; outerDone; subscribed; completed)
open import simultaneous.SObs using (Flat; outerB; laneB; closeB; isZero; lone; module Elaborate)
open import simultaneous.HeldComb using (past)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (Out; react; onMark; begun; entered; bump; stopped; overed;
  cut; unpark; arrive; ended; burstOver; left; anyHolds; setAt; share; anew)

-- Nothing parked, or a connect in scope holds a route of the instant.
Parks : Flat Pos → Set
Parks s = Flat.parked s ≡ 0 ⊎ anyHolds (Flat.at s) (Flat.live s) ≡ true

private
  bump-park : ∀ b f s → Parks s → Parks (bump b f s)
  bump-park outerB f s p = p
  bump-park laneB  f s p = p
  bump-park closeB f s p = p

  cut-park : ∀ {B} k n s → Parks s → Parks (proj₁ (cut {B} k n s))
  none : ∀ {A : Set} → A ⊎ false ≡ true → A
  none (inj₁ a) = a

  cut-park k n s p with Flat.spent s | anyHolds (Flat.at s) (Flat.live s) in e
  ... | true  | true  = inj₂ e
  ... | true  | false = inj₁ (none p)
  ... | false | true  = inj₂ e
  ... | false | false = inj₁ (none p)

  unpark-park : ∀ {B} n s → Parks (proj₁ (unpark {B} n s))
  unpark-park n s with anyHolds (Flat.at s) (Flat.live s) in e
  ... | true  = inj₂ e
  ... | false = inj₁ refl

  entered-park : ∀ b n s → Parks s → Parks (entered b n s)
  entered-park b n s p with does (n ≟ᵖ Flat.at s)
  ... | true  = bump-park b suc s p
  ... | false = bump-park b suc (anew n s) (inj₁ refl)

  begun-park : ∀ {B} b n s → Parks s → Parks (proj₁ (begun {B} b n s))
  begun-park b n s p with does (n ≟ᵖ Flat.at s) ∧ Flat.spent s
  ... | true  = p
  ... | false = entered-park b n s p

  stopped-park : ∀ {B} b n s k → Parks s → Parks (proj₁ (stopped {B} b n s k))
  stopped-park b n s zero    p = p
  stopped-park b n s (suc _) p = bump-park b (_∸ 1) s p

  overed-park : ∀ {B} n s → Parks s → Parks (proj₁ (overed {B} n s))
  overed-park n s p with Flat.spent s
  ... | true  = p
  ... | false = inj₁ refl

  arrive-park : ∀ {B} op n s → Parks s → Parks (proj₁ (arrive {B} op n s))
  arrive-park (mergeᶠ (just _)) n s p = p
  arrive-park (mergeᶠ nothing)  n s p = p
  arrive-park switchᶠ           n s p = cut-park (Flat.lanes s) n (record s { active = 0 ; lanes = 0 }) p
  arrive-park exhaustᶠ          n s p = p

  ended-park : ∀ {B} k n s → Parks s → Parks (proj₁ (ended {B} k n s))
  ended-park k n s p with isZero (Flat.queue s)
  ... | false = p
  ... | true with Flat.finished s ∧ isZero (Flat.active s)
  ...   | true  = p
  ...   | false = cut-park (k + Flat.held s) n (record s { held = 0 }) p

  burst-park : ∀ {B} h n s → Parks s → Parks (proj₁ (burstOver {B} h n s))
  burst-park true  n s p = p
  burst-park false n s p = cut-park (Flat.held s) n (record s { held = 0 }) p

  left-park : ∀ {B} n s → Parks s → Parks (proj₁ (left {B} n s))
  left-park n s p with isZero (Flat.active s) ∧ isZero (Flat.queue s)
  ... | true  = p
  ... | false = cut-park (Flat.outer s) n (record s { outer = 0 }) p

  onMark-park : ∀ {B} op b m n s → Parks s → Parks (proj₁ (onMark {B} op b s m n))
  onMark-park op b begin      n s p = begun-park b n s p
  onMark-park op b stop       n s p = stopped-park b n s (if Flat.spent s then 0 else share b s) p
  onMark-park op b over       n s p = overed-park n s p
  onMark-park op b carry      n s p = p
  onMark-park op b outerOpen  n s p = arrive-park op n s p
  onMark-park op b outerClose n s p = p
  onMark-park op b laneStart  n s p = p
  onMark-park op b laneDone   n s p = ended-park (Flat.acc s ⊓ Flat.lanes s) n (record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ Flat.acc s ; acc = 0 ; dead = true }) p
  onMark-park op b burstEnd   n s p = burst-park (isZero (Flat.held s) ∨ Flat.dead s) n s p
  onMark-park op b outerDone  n s p = left-park n (record s { finished = true }) p
  onMark-park op b subscribed n s p = p
  onMark-park op b completed  n s p = p

  react-park : ∀ {B} op (o : Out B) x → Parks (proj₁ o) → Parks (proj₁ (react op o x))
  react-park op o (just (inj₁ (b , instEmit (value v) n))) p = p
  react-park op o (just (inj₁ (b , instEmit (mark m) n)))  p = onMark-park op b m n (proj₁ o) p
  react-park op o (just (inj₂ (j , r)))                    p = unpark-park root (record (proj₁ o) { live = setAt j r (Flat.live (proj₁ o)) })
  react-park op o nothing                                  p = p

-- THE SCAN PARKS ONLY ON A CONNECT HOLDING A ROUTE, past any run read.
past-park : ∀ {B} op (o : Out B) rx → Parks (proj₁ o) → Parks (proj₁ (past op o rx))
past-park op o []                 p = p
past-park op o ((q , out x) ∷ rx) p = past-park op (react op o x) rx (react-park op o x p)
past-park op o ((q , end) ∷ rx)   p = p
past-park op o ((q , skip) ∷ rx)  p = past-park op o rx p
past-park op o ((q , pin _) ∷ rx) p = past-park op o rx p
