-- THE SCAN'S LANE COUNTERS, ROW BY ROW: `active` rises at a lane's
-- `laneStart`, falls at its `laneDone` and empties at a switch's
-- arrival; a bounded merge's `queue` rises at an arrival and falls at a
-- `laneStart`.  No other row moves either (`past-active`, `past-queue`).
module simultaneous.ScanCount where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (true; false; _∧_; _∨_; if_then_else_)
open import Data.Nat using (suc; _∸_; _⊓_; _+_)
open import Relation.Nullary using (does)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; end; skip; pin)
open import simultaneous.InstEmit using (instEmit; value; mark; Mark; begin; over; stop; outerOpen; outerClose; laneStart; carry;
  laneDone; burstEnd; outerDone; subscribed; completed)
open import simultaneous.SObs using (Flat; isZero; Branch; outerB; laneB; closeB; lone; module Elaborate)
open import simultaneous.HeldComb using (past)
open import simultaneous.LaneCount using (Kind; kStart; kDone; kCut; kOther; stepK)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone
  using (IE; Out; Input; anyHolds; setAt; share; react; cut; unpark; ended; burstOver; left; begun; stopped; overed; arrive)

-- How a mark moves `active`,
markAct : FlatOp → Mark → Kind
markAct _       laneStart = kStart
markAct _       laneDone  = kDone
markAct switchᶠ outerOpen = kCut
markAct _       _         = kOther

-- and `queue`.
markQue : FlatOp → Mark → Kind
markQue _                 laneStart = kDone
markQue (mergeᶠ (just _)) outerOpen = kStart
markQue _                 _         = kOther

evKind : ∀ {B} → (FlatOp → Mark → Kind) → FlatOp → Ev (Maybe (Input B)) → Kind
evKind k op (out (just (inj₁ (_ , instEmit (mark m) _)))) = k op m
evKind k op _                                              = kOther

rowKind : ∀ {B} → (FlatOp → Mark → Kind) → FlatOp → Pos × Ev (Maybe (Input B)) → Kind
rowKind k op (_ , e) = evKind k op e

private
  cut-act : ∀ {B} k n s → Flat.active (proj₁ (cut {B} k n s)) ≡ Flat.active s × Flat.queue (proj₁ (cut {B} k n s)) ≡ Flat.queue s
  cut-act k n s with Flat.spent s | anyHolds (Flat.at s) (Flat.live s)
  ... | true  | _     = refl , refl
  ... | false | true  = refl , refl
  ... | false | false = refl , refl

  unpark-act : ∀ {B} n s → Flat.active (proj₁ (unpark {B} n s)) ≡ Flat.active s × Flat.queue (proj₁ (unpark {B} n s)) ≡ Flat.queue s
  unpark-act n s with anyHolds (Flat.at s) (Flat.live s)
  ... | true  = refl , refl
  ... | false = refl , refl

  ended-act : ∀ {B} k n s → Flat.active (proj₁ (ended {B} k n s)) ≡ Flat.active s × Flat.queue (proj₁ (ended {B} k n s)) ≡ Flat.queue s
  ended-act k n s with isZero (Flat.queue s)
  ... | false = refl , refl
  ... | true with Flat.finished s ∧ isZero (Flat.active s)
  ...   | true  = refl , refl
  ...   | false = cut-act (k + Flat.held s) n (record s { held = 0 })

  burst-act : ∀ {B} b n s → Flat.active (proj₁ (burstOver {B} b n s)) ≡ Flat.active s × Flat.queue (proj₁ (burstOver {B} b n s)) ≡ Flat.queue s
  burst-act true  n s = refl , refl
  burst-act false n s = cut-act (Flat.held s) n (record s { held = 0 })

  left-act : ∀ {B} n s → Flat.active (proj₁ (left {B} n s)) ≡ Flat.active s × Flat.queue (proj₁ (left {B} n s)) ≡ Flat.queue s
  left-act n s with isZero (Flat.active s) ∧ isZero (Flat.queue s)
  ... | true  = refl , refl
  ... | false = cut-act (Flat.outer s) n (record s { outer = 0 })

  begun-act : ∀ {B} b n s → Flat.active (proj₁ (begun {B} b n s)) ≡ Flat.active s × Flat.queue (proj₁ (begun {B} b n s)) ≡ Flat.queue s
  begun-act b n s with does (n ≟ᵖ Flat.at s) ∧ Flat.spent s
  ... | true  = refl , refl
  ... | false with does (n ≟ᵖ Flat.at s)
  ...   | true with b
  ...     | outerB = refl , refl
  ...     | laneB  = refl , refl
  ...     | closeB = refl , refl
  begun-act b n s | false | false with b
  ...     | outerB = refl , refl
  ...     | laneB  = refl , refl
  ...     | closeB = refl , refl

  stopped-act : ∀ {B} b n s k → Flat.active (proj₁ (stopped {B} b n s k)) ≡ Flat.active s × Flat.queue (proj₁ (stopped {B} b n s k)) ≡ Flat.queue s
  stopped-act b      n s 0       = refl , refl
  stopped-act outerB n s (suc _) = refl , refl
  stopped-act laneB  n s (suc _) = refl , refl
  stopped-act closeB n s (suc _) = refl , refl

  overed-act : ∀ {B} n s → Flat.active (proj₁ (overed {B} n s)) ≡ Flat.active s × Flat.queue (proj₁ (overed {B} n s)) ≡ Flat.queue s
  overed-act n s with Flat.spent s
  ... | true  = refl , refl
  ... | false = refl , refl

-- A ROW MOVES THE COUNTERS BY ITS KIND.
react-active : ∀ {B} op (o : Out B) x → Flat.active (proj₁ (react op o x)) ≡ stepK (evKind markAct op (out x)) (Flat.active (proj₁ o))
react-active op (s , _) nothing = refl
react-active op (s , _) (just (inj₂ (i , r))) = proj₁ (unpark-act root (record s { live = setAt i r (Flat.live s) }))
react-active op (s , _) (just (inj₁ (b , instEmit (value _) _))) = refl
react-active op (s , _) (just (inj₁ (b , instEmit (mark begin) n))) = proj₁ (begun-act b n s)
react-active op (s , _) (just (inj₁ (b , instEmit (mark over) n))) = proj₁ (overed-act n s)
react-active op (s , _) (just (inj₁ (b , instEmit (mark stop) n))) = proj₁ (stopped-act b n s (if Flat.spent s then 0 else share b s))
react-active (mergeᶠ (just _)) (s , _) (just (inj₁ (b , instEmit (mark outerOpen) n))) = refl
react-active (mergeᶠ nothing)  (s , _) (just (inj₁ (b , instEmit (mark outerOpen) n))) = refl
react-active switchᶠ           (s , _) (just (inj₁ (b , instEmit (mark outerOpen) n))) = proj₁ (cut-act (Flat.lanes s) n (record s { active = 0 ; lanes = 0 }))
react-active exhaustᶠ          (s , _) (just (inj₁ (b , instEmit (mark outerOpen) n))) = refl
react-active op (s , _) (just (inj₁ (b , instEmit (mark outerClose) n))) = refl
react-active op (s , _) (just (inj₁ (b , instEmit (mark laneStart) n))) = refl
react-active op (s , _) (just (inj₁ (b , instEmit (mark carry) n))) = refl
react-active op (s , _) (just (inj₁ (b , instEmit (mark laneDone) n))) = proj₁ (ended-act (Flat.acc s ⊓ Flat.lanes s) n (record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ Flat.acc s ; acc = 0 ; dead = true }))
react-active op (s , _) (just (inj₁ (b , instEmit (mark burstEnd) n))) = proj₁ (burst-act (isZero (Flat.held s) ∨ Flat.dead s) n s)
react-active op (s , _) (just (inj₁ (b , instEmit (mark outerDone) n))) = proj₁ (left-act n (record s { finished = true }))
react-active op (s , _) (just (inj₁ (b , instEmit (mark subscribed) n))) = refl
react-active op (s , _) (just (inj₁ (b , instEmit (mark completed) n))) = refl

react-queue : ∀ {B} op (o : Out B) x → Flat.queue (proj₁ (react op o x)) ≡ stepK (evKind markQue op (out x)) (Flat.queue (proj₁ o))
react-queue op (s , _) nothing = refl
react-queue op (s , _) (just (inj₂ (i , r))) = proj₂ (unpark-act root (record s { live = setAt i r (Flat.live s) }))
react-queue op (s , _) (just (inj₁ (b , instEmit (value _) _))) = refl
react-queue op (s , _) (just (inj₁ (b , instEmit (mark begin) n))) = proj₂ (begun-act b n s)
react-queue op (s , _) (just (inj₁ (b , instEmit (mark over) n))) = proj₂ (overed-act n s)
react-queue op (s , _) (just (inj₁ (b , instEmit (mark stop) n))) = proj₂ (stopped-act b n s (if Flat.spent s then 0 else share b s))
react-queue (mergeᶠ (just _)) (s , _) (just (inj₁ (b , instEmit (mark outerOpen) n))) = refl
react-queue (mergeᶠ nothing)  (s , _) (just (inj₁ (b , instEmit (mark outerOpen) n))) = refl
react-queue switchᶠ           (s , _) (just (inj₁ (b , instEmit (mark outerOpen) n))) = proj₂ (cut-act (Flat.lanes s) n (record s { active = 0 ; lanes = 0 }))
react-queue exhaustᶠ          (s , _) (just (inj₁ (b , instEmit (mark outerOpen) n))) = refl
react-queue op (s , _) (just (inj₁ (b , instEmit (mark outerClose) n))) = refl
react-queue op (s , _) (just (inj₁ (b , instEmit (mark laneStart) n))) = refl
react-queue op (s , _) (just (inj₁ (b , instEmit (mark carry) n))) = refl
react-queue op (s , _) (just (inj₁ (b , instEmit (mark laneDone) n))) = proj₂ (ended-act (Flat.acc s ⊓ Flat.lanes s) n (record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ Flat.acc s ; acc = 0 ; dead = true }))
react-queue op (s , _) (just (inj₁ (b , instEmit (mark burstEnd) n))) = proj₂ (burst-act (isZero (Flat.held s) ∨ Flat.dead s) n s)
react-queue op (s , _) (just (inj₁ (b , instEmit (mark outerDone) n))) = proj₂ (left-act n (record s { finished = true }))
react-queue op (s , _) (just (inj₁ (b , instEmit (mark subscribed) n))) = refl
react-queue op (s , _) (just (inj₁ (b , instEmit (mark completed) n))) = refl

-- The scan past one more row, before any end.
pstep : ∀ {B} → FlatOp → Out B → Pos × Ev (Maybe (Input B)) → Out B
pstep op o (_ , out x) = react op o x
pstep op o _           = o

past-snoc : ∀ {B} op (o : Out B) xs y → (∀ {c} → (c , end) ∈ xs → ⊥) → past op o (xs ++ [ y ]) ≡ pstep op (past op o xs) y
past-snoc op o [] (_ , out _) _ = refl
past-snoc op o [] (_ , end)   _ = refl
past-snoc op o [] (_ , skip)  _ = refl
past-snoc op o [] (_ , pin _) _ = refl
past-snoc op o ((_ , out x) ∷ xs) y ne = past-snoc op (react op o x) xs y (λ i → ne (there i))
past-snoc op o ((_ , end)   ∷ xs) y ne = ⊥-elim (ne (here refl))
past-snoc op o ((_ , skip)  ∷ xs) y ne = past-snoc op o xs y (λ i → ne (there i))
past-snoc op o ((_ , pin _) ∷ xs) y ne = past-snoc op o xs y (λ i → ne (there i))

-- THE COUNTERS PAST ONE MORE ROW, before any end.
past-active : ∀ {B} op (o : Out B) xs y → (∀ {c} → (c , end) ∈ xs → ⊥)
            → Flat.active (proj₁ (past op o (xs ++ [ y ]))) ≡ stepK (rowKind markAct op y) (Flat.active (proj₁ (past op o xs)))
past-active op o xs (q , out x) ne rewrite past-snoc op o xs (q , out x) ne = react-active op (past op o xs) x
past-active op o xs (q , end) ne = cong (λ o′ → Flat.active (proj₁ o′)) (past-snoc op o xs (q , end) ne)
past-active op o xs (q , skip) ne = cong (λ o′ → Flat.active (proj₁ o′)) (past-snoc op o xs (q , skip) ne)
past-active op o xs (q , pin _) ne = cong (λ o′ → Flat.active (proj₁ o′)) (past-snoc op o xs (q , pin _) ne)

past-queue : ∀ {B} op (o : Out B) xs y → (∀ {c} → (c , end) ∈ xs → ⊥)
           → Flat.queue (proj₁ (past op o (xs ++ [ y ]))) ≡ stepK (rowKind markQue op y) (Flat.queue (proj₁ (past op o xs)))
past-queue op o xs (q , out x) ne rewrite past-snoc op o xs (q , out x) ne = react-queue op (past op o xs) x
past-queue op o xs (q , end) ne = cong (λ o′ → Flat.queue (proj₁ o′)) (past-snoc op o xs (q , end) ne)
past-queue op o xs (q , skip) ne = cong (λ o′ → Flat.queue (proj₁ o′)) (past-snoc op o xs (q , skip) ne)
past-queue op o xs (q , pin _) ne = cong (λ o′ → Flat.queue (proj₁ o′)) (past-snoc op o xs (q , pin _) ne)
