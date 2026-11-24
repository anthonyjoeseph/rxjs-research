{-# OPTIONS --guardedness #-}

-- FLATMAP'S SCAN HOLDS ROUTES ONLY FROM A LANE'S END, IN ITS INSTANT
-- (`held-onset`).  Only a `laneDone` adds to what is held, and only from
-- the lanes' own count; a new instant and an over start with none held,
-- a cut empties it, and every other step leaves the instant and what is
-- held alone.  So past any run read, a scan holding routes has held them
-- since one `laneDone`, in the instant it read that mark in, and either
-- rxjs had a lane queued there, or the flatMap ended with that lane
-- (`onset-why`).
module simultaneous.FlatHeld where

open import Data.Bool using (true; false; _∧_; _∨_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊓_)
import Data.Nat.Properties as ℕP
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)
open import Relation.Nullary using (¬_; does; Dec; yes; no)

open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; end; skip; pin)
open import simultaneous.InstEmit using (instEmit; value; mark; Mark; begin; stop; over; outerOpen; outerClose; laneStart; laneDone;
  burstEnd; outerDone; subscribed; completed)
open import simultaneous.SObs using (Flat; Branch; outerB; laneB; closeB; isZero; lone; module Elaborate)
open import simultaneous.HeldComb using (past; init)
open import simultaneous.FlatLanes using (bump-at)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Out; Input; react; onMark; begun; entered; bump; stopped; overed;
  cut; unpark; arrive; ended; burstOver; left; anyHolds; setAt; anew)

-- A step from `s` to `s′`: holding routes after, it keeps the instant,
-- and held them before, or `D` holds and it took them from the lanes.
record Step (D : Set) (s s′ : Flat Pos) : Set where
  constructor step
  field
    run : ¬ Flat.held s′ ≡ 0 → Flat.at s′ ≡ Flat.at s × (¬ Flat.held s ≡ 0 ⊎ (D × Flat.held s ≡ 0 × ¬ Flat.lanes s ≡ 0))

-- The row a scan reads a `laneDone` from.
LD : ∀ {B} → Maybe (Input B) → Set
LD x = Σ Branch λ b → Σ ℕ λ kd → Σ Pos λ n → x ≡ just (inj₁ (b , instEmit (mark (laneDone kd)) n))

private
  keep : ∀ {D s s′} → Flat.held s′ ≡ Flat.held s → Flat.at s′ ≡ Flat.at s → Step D s s′
  keep h a = step λ nz → a , inj₁ (λ z → nz (trans h z))

  none : ∀ {D s s′} → Flat.held s′ ≡ 0 → Step D s s′
  none h = step λ nz → ⊥-elim (nz h)

  bump-held : ∀ b f s → Flat.held (bump b f s) ≡ Flat.held s
  bump-held outerB f s = refl
  bump-held laneB  f s = refl
  bump-held closeB f s = refl

  cut-held : ∀ {B} k n s → Flat.held (proj₁ (cut {B} k n s)) ≡ Flat.held s
  cut-held k n s with Flat.spent s | anyHolds (Flat.at s) (Flat.live s)
  ... | true  | _     = refl
  ... | false | true  = refl
  ... | false | false = refl

  cut-at : ∀ {B} k n s → Flat.at (proj₁ (cut {B} k n s)) ≡ Flat.at s
  cut-at k n s with Flat.spent s | anyHolds (Flat.at s) (Flat.live s)
  ... | true  | _     = refl
  ... | false | true  = refl
  ... | false | false = refl

  plus-nz : ∀ a k → ¬ a + k ≡ 0 → ¬ a ≡ 0 ⊎ (a ≡ 0 × ¬ k ≡ 0)
  plus-nz zero    k nz = inj₂ (refl , nz)
  plus-nz (suc a) k nz = inj₁ λ ()

  ⊓-nz : ∀ kd l → ¬ kd ⊓ l ≡ 0 → ¬ l ≡ 0
  ⊓-nz kd l nz refl = nz (ℕP.⊓-zeroʳ kd)

  -- A lane's end: what it hands on is the lanes' own.
  ended-step : ∀ {B D} → D → ∀ kd s n s′ → Flat.held s′ ≡ Flat.held s → Flat.at s′ ≡ Flat.at s
             → Step D s (proj₁ (ended {B} (kd ⊓ Flat.lanes s) n s′))
  ended-step d kd s n s′ h a with isZero (Flat.queue s′)
  ... | false = step λ nz → a , grow (plus-nz (Flat.held s′) (kd ⊓ Flat.lanes s) nz)
    where
      grow : ¬ Flat.held s′ ≡ 0 ⊎ (Flat.held s′ ≡ 0 × ¬ kd ⊓ Flat.lanes s ≡ 0) → ¬ Flat.held s ≡ 0 ⊎ (_ × Flat.held s ≡ 0 × ¬ Flat.lanes s ≡ 0)
      grow (inj₁ hz)       = inj₁ λ z → hz (trans h z)
      grow (inj₂ (z , kz)) = inj₂ (d , trans (sym h) z , ⊓-nz kd (Flat.lanes s) kz)
  ... | true with Flat.finished s′ ∧ isZero (Flat.active s′)
  ...   | true  = step λ nz → a , grow (plus-nz (Flat.held s′) (kd ⊓ Flat.lanes s) nz)
    where
      grow : ¬ Flat.held s′ ≡ 0 ⊎ (Flat.held s′ ≡ 0 × ¬ kd ⊓ Flat.lanes s ≡ 0) → ¬ Flat.held s ≡ 0 ⊎ (_ × Flat.held s ≡ 0 × ¬ Flat.lanes s ≡ 0)
      grow (inj₁ hz)       = inj₁ λ z → hz (trans h z)
      grow (inj₂ (z , kz)) = inj₂ (d , trans (sym h) z , ⊓-nz kd (Flat.lanes s) kz)
  ...   | false = none (cut-held (kd ⊓ Flat.lanes s + Flat.held s′) n (record s′ { held = 0 }))

  begun-step : ∀ {B D} b n s → Step D s (proj₁ (begun {B} b n s))
  begun-step b n s with does (n ≟ᵖ Flat.at s) ∧ Flat.spent s
  ... | true  = keep refl refl
  ... | false with does (n ≟ᵖ Flat.at s)
  ...   | true  = keep (bump-held b suc s) (bump-at b suc s)
  ...   | false = none (bump-held b suc (anew n s))

  stopped-step : ∀ {B D} b n s k → Step D s (proj₁ (stopped {B} b n s k))
  stopped-step b n s zero    = keep refl refl
  stopped-step b n s (suc _) = keep (bump-held b (_∸ 1) s) (bump-at b (_∸ 1) s)

  overed-step : ∀ {B D} n s → Step D s (proj₁ (overed {B} n s))
  overed-step n s with Flat.spent s
  ... | true  = keep refl refl
  ... | false = none refl

  arrive-step : ∀ {B D} op n s → Step D s (proj₁ (arrive {B} op n s))
  arrive-step (mergeᶠ (just _)) n s = keep refl refl
  arrive-step (mergeᶠ nothing)  n s = keep refl refl
  arrive-step switchᶠ           n s = keep (cut-held (Flat.lanes s) n (record s { active = 0 ; lanes = 0 })) (cut-at (Flat.lanes s) n (record s { active = 0 ; lanes = 0 }))
  arrive-step exhaustᶠ          n s = keep refl refl

  burst-step : ∀ {B D} h n s → Step D s (proj₁ (burstOver {B} h n s))
  burst-step true  n s = keep refl refl
  burst-step false n s = none (cut-held (Flat.held s) n (record s { held = 0 }))

  left-step : ∀ {B D} n s → Step D s (proj₁ (left {B} n (record s { finished = true })))
  left-step n s with isZero (Flat.active s) ∧ isZero (Flat.queue s)
  ... | true  = keep refl refl
  ... | false = keep (cut-held (Flat.outer s) n (record s { finished = true ; outer = 0 })) (cut-at (Flat.outer s) n (record s { finished = true ; outer = 0 }))

  unpark-step : ∀ {B D} n s₀ s → Flat.held s ≡ Flat.held s₀ → Flat.at s ≡ Flat.at s₀ → Step D s₀ (proj₁ (unpark {B} n s))
  unpark-step n s₀ s h a with anyHolds (Flat.at s) (Flat.live s)
  ... | true  = keep h a
  ... | false = keep h a

  IsDone : Mark → Set
  IsDone m = Σ ℕ λ kd → m ≡ laneDone kd

  onMark-step : ∀ {B} op b m n s → Step (IsDone m) s (proj₁ (onMark {B} op b s m n))
  onMark-step op b begin         n s = begun-step b n s
  onMark-step op b stop          n s = stopped-step b n s (if Flat.spent s then 0 else _)
  onMark-step op b over          n s = overed-step n s
  onMark-step op b outerOpen     n s = arrive-step op n s
  onMark-step op b outerClose    n s = keep refl refl
  onMark-step op b laneStart     n s = keep refl refl
  onMark-step op b (laneDone kd) n s =
    ended-step (kd , refl) kd s n (record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ kd ; dead = true }) refl refl
  onMark-step op b burstEnd      n s = burst-step (isZero (Flat.held s) ∨ Flat.dead s) n s
  onMark-step op b outerDone     n s = left-step n s
  onMark-step op b subscribed    n s = keep refl refl
  onMark-step op b completed     n s = keep refl refl

  step-map : ∀ {D D′ s s′} → (D → D′) → Step D s s′ → Step D′ s s′
  step-map {D} {D′} f st = step λ nz → go (Step.run st nz)
    where
      go : ∀ {A H L : Set} → A × (H ⊎ (D × L)) → A × (H ⊎ (D′ × L))
      go (a , inj₁ h)        = a , inj₁ h
      go (a , inj₂ (d , l)) = a , inj₂ (f d , l)

-- ONE ROW READ.
react-step : ∀ {B} op (o : Out B) x → Step (LD x) (proj₁ o) (proj₁ (react op o x))
react-step op o (just (inj₁ (b , instEmit (value v) n))) = keep refl refl
react-step op o (just (inj₁ (b , instEmit (mark m) n)))  =
  step-map (λ { (kd , refl) → b , kd , n , refl }) (onMark-step op b m n (proj₁ o))
react-step op o (just (inj₂ (j , r)))                    = unpark-step root (proj₁ o) (record (proj₁ o) { live = setAt j r (Flat.live (proj₁ o)) }) refl refl
react-step op o nothing                                  = keep refl refl

-- The scan holds routes after every row of a run, from `o` on.
Thru : ∀ {B} → FlatOp → Out B → List (Pos × Ev (Maybe (Input B))) → Set
Thru op o []                 = ¬ Flat.held (proj₁ o) ≡ 0
Thru op o ((q , out x) ∷ rx) = ¬ Flat.held (proj₁ o) ≡ 0 × Thru op (react op o x) rx
Thru op o ((q , end) ∷ rx)   = ¬ Flat.held (proj₁ o) ≡ 0
Thru op o ((q , skip) ∷ rx)  = Thru op o rx
Thru op o ((q , pin _) ∷ rx) = Thru op o rx

-- Where a run's routes held began: the `laneDone` read with none held,
-- taken from the lanes, the instant kept since, held throughout.
Onset : ∀ {B} → FlatOp → Out B → List (Pos × Ev (Maybe (Input B))) → Set
Onset {B} op o rx = Σ (List (Pos × Ev (Maybe (Input B)))) λ r₁ → Σ Pos λ d → Σ (Maybe (Input B)) λ xd → Σ (List (Pos × Ev (Maybe (Input B)))) λ r₂ →
  rx ≡ r₁ ++ (d , out xd) ∷ r₂ × LD xd × Flat.held (proj₁ (past op o r₁)) ≡ 0 × ¬ Flat.lanes (proj₁ (past op o r₁)) ≡ 0
  × Flat.at (proj₁ (past op o rx)) ≡ Flat.at (proj₁ (past op o r₁)) × Thru op (react op (past op o r₁) xd) r₂

thru-head : ∀ {B} op {o : Out B} rx → Thru op o rx → ¬ Flat.held (proj₁ o) ≡ 0
thru-head op []                 h       = h
thru-head op ((_ , out _) ∷ _)  (h , _) = h
thru-head op ((_ , end) ∷ _)    h       = h
thru-head op ((_ , skip) ∷ r)   h       = thru-head op r h
thru-head op ((_ , pin _) ∷ r)  h       = thru-head op r h

held-back : ∀ {B} op (o : Out B) rx → ¬ Flat.held (proj₁ (past op o rx)) ≡ 0
          → (Flat.at (proj₁ (past op o rx)) ≡ Flat.at (proj₁ o) × Thru op o rx) ⊎ Onset op o rx
held-back op o []                 nz = inj₁ (refl , nz)
held-back op o ((q , end) ∷ rx)   nz = inj₁ (refl , nz)
held-back op o ((q , skip) ∷ rx)  nz with held-back op o rx nz
... | inj₁ r = inj₁ r
... | inj₂ (r₁ , d , xd , r₂ , refl , rest) = inj₂ ((q , skip) ∷ r₁ , d , xd , r₂ , refl , rest)
held-back op o ((q , pin w) ∷ rx) nz with held-back op o rx nz
... | inj₁ r = inj₁ r
... | inj₂ (r₁ , d , xd , r₂ , refl , rest) = inj₂ ((q , pin w) ∷ r₁ , d , xd , r₂ , refl , rest)
held-back op o ((q , out x) ∷ rx) nz with held-back op (react op o x) rx nz
... | inj₂ (r₁ , d , xd , r₂ , refl , rest) = inj₂ ((q , out x) ∷ r₁ , d , xd , r₂ , refl , rest)
... | inj₁ (a , th) with Step.run (react-step op o x) (thru-head op rx th)
...   | a′ , inj₁ hz             = inj₁ (trans a a′ , hz , th)
...   | a′ , inj₂ (ld , z , ln) = inj₂ ([] , q , x , rx , refl , ld , z , ln , trans a a′ , th)

-- FROM THE SCAN'S START, routes held began at a lane's end.
held-onset : ∀ {B} op rx → ¬ Flat.held (proj₁ (past {B} op init rx)) ≡ 0 → Onset op init rx
held-onset op rx nz with held-back op init rx nz
... | inj₂ on      = on
... | inj₁ (_ , th) = ⊥-elim (thru-head op rx th refl)

private
  ended-why : ∀ {B} k n s → ¬ Flat.held (proj₁ (ended {B} k n s)) ≡ 0
            → ¬ Flat.queue s ≡ 0 ⊎ (Flat.queue s ≡ 0 × Flat.finished s ≡ true × Flat.active s ≡ 0)
  ended-why k n s with Flat.queue s
  ... | suc _ = λ _ → inj₁ λ ()
  ... | zero with Flat.finished s | Flat.active s
  ...   | true  | zero  = λ _ → inj₂ (refl , refl , refl)
  ...   | true  | suc _ = λ nz → ⊥-elim (nz (cut-held (k + Flat.held s) n (record s { held = 0 })))
  ...   | false | _     = λ nz → ⊥-elim (nz (cut-held (k + Flat.held s) n (record s { held = 0 })))

-- WHY A LANE'S END HELD ITS ROUTES: rxjs had a lane queued, or the outer
-- had ended with no other lane running, so the flatMap ended with it.
onset-why : ∀ {B} op (o : Out B) {xd} → LD xd → ¬ Flat.held (proj₁ (react op o xd)) ≡ 0
          → ¬ Flat.queue (proj₁ o) ≡ 0 ⊎ (Flat.queue (proj₁ o) ≡ 0 × Flat.finished (proj₁ o) ≡ true × Flat.active (proj₁ o) ∸ 1 ≡ 0)
onset-why op o (b , kd , n , refl) = ended-why (kd ⊓ Flat.lanes (proj₁ o)) n
  (record (proj₁ o) { active = Flat.active (proj₁ o) ∸ 1 ; lanes = Flat.lanes (proj₁ o) ∸ kd ; dead = true })

-- ONLY A BOUNDED MERGE QUEUES: no other flatMap's scan counts a lane
-- waiting, past any run read.
private
  record Q (s s′ : Flat Pos) : Set where
    constructor qs
    field
      qrun : Flat.queue s ≡ 0 → Flat.queue s′ ≡ 0

  cut-queue : ∀ {B} k n s → Flat.queue (proj₁ (cut {B} k n s)) ≡ Flat.queue s
  cut-queue k n s with Flat.spent s | anyHolds (Flat.at s) (Flat.live s)
  ... | true  | _     = refl
  ... | false | true  = refl
  ... | false | false = refl

  bump-queue : ∀ b f s → Flat.queue (bump b f s) ≡ Flat.queue s
  bump-queue outerB f s = refl
  bump-queue laneB  f s = refl
  bump-queue closeB f s = refl

  qk : ∀ {s s′} → Flat.queue s′ ≡ Flat.queue s → Q s s′
  qk e = qs λ z → trans e z

  begun-q : ∀ {B} b n s → Q s (proj₁ (begun {B} b n s))
  begun-q b n s with does (n ≟ᵖ Flat.at s) ∧ Flat.spent s
  ... | true  = qk refl
  ... | false with does (n ≟ᵖ Flat.at s)
  ...   | true  = qk (bump-queue b suc s)
  ...   | false = qk (bump-queue b suc (anew n s))

  stopped-q : ∀ {B} b n s k → Q s (proj₁ (stopped {B} b n s k))
  stopped-q b n s zero    = qk refl
  stopped-q b n s (suc _) = qk (bump-queue b (_∸ 1) s)

  overed-q : ∀ {B} n s → Q s (proj₁ (overed {B} n s))
  overed-q n s with Flat.spent s
  ... | true  = qk refl
  ... | false = qk refl

  arrive-q : ∀ {B} op → (∀ k → ¬ op ≡ mergeᶠ (just k)) → ∀ n s → Q s (proj₁ (arrive {B} op n s))
  arrive-q (mergeᶠ (just k)) nb n s = ⊥-elim (nb k refl)
  arrive-q (mergeᶠ nothing)  nb n s = qk refl
  arrive-q switchᶠ           nb n s = qk (cut-queue (Flat.lanes s) n (record s { active = 0 ; lanes = 0 }))
  arrive-q exhaustᶠ          nb n s = qk refl

  ended-q : ∀ {B} k n s₀ s → Flat.queue s ≡ Flat.queue s₀ → Q s₀ (proj₁ (ended {B} k n s))
  ended-q k n s₀ s e with isZero (Flat.queue s)
  ... | false = qk e
  ... | true with Flat.finished s ∧ isZero (Flat.active s)
  ...   | true  = qk e
  ...   | false = qk (trans (cut-queue (k + Flat.held s) n (record s { held = 0 })) e)

  burst-q : ∀ {B} h n s → Q s (proj₁ (burstOver {B} h n s))
  burst-q true  n s = qk refl
  burst-q false n s = qk (cut-queue (Flat.held s) n (record s { held = 0 }))

  left-q : ∀ {B} n s → Q s (proj₁ (left {B} n (record s { finished = true })))
  left-q n s with isZero (Flat.active s) ∧ isZero (Flat.queue s)
  ... | true  = qk refl
  ... | false = qk (cut-queue (Flat.outer s) n (record s { finished = true ; outer = 0 }))

  unpark-q : ∀ {B} n s → Q s (proj₁ (unpark {B} n s))
  unpark-q n s with anyHolds (Flat.at s) (Flat.live s)
  ... | true  = qk refl
  ... | false = qk refl

  onMark-q : ∀ {B} op → (∀ k → ¬ op ≡ mergeᶠ (just k)) → ∀ b m n s → Q s (proj₁ (onMark {B} op b s m n))
  onMark-q op nb b begin         n s = begun-q b n s
  onMark-q op nb b stop          n s = stopped-q b n s (if Flat.spent s then 0 else _)
  onMark-q op nb b over          n s = overed-q n s
  onMark-q op nb b outerOpen     n s = arrive-q op nb n s
  onMark-q op nb b outerClose    n s = qk refl
  onMark-q op nb b laneStart     n s = qs λ z → cong (_∸ 1) z
  onMark-q op nb b (laneDone kd) n s =
    ended-q (kd ⊓ Flat.lanes s) n s (record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ kd ; dead = true }) refl
  onMark-q op nb b burstEnd      n s = burst-q (isZero (Flat.held s) ∨ Flat.dead s) n s
  onMark-q op nb b outerDone     n s = left-q n s
  onMark-q op nb b subscribed    n s = qk refl
  onMark-q op nb b completed     n s = qk refl

  react-q : ∀ {B} op → (∀ k → ¬ op ≡ mergeᶠ (just k)) → ∀ (o : Out B) x → Q (proj₁ o) (proj₁ (react op o x))
  react-q op nb o (just (inj₁ (b , instEmit (value v) n))) = qk refl
  react-q op nb o (just (inj₁ (b , instEmit (mark m) n)))  = onMark-q op nb b m n (proj₁ o)
  react-q op nb o (just (inj₂ (j , r)))                    = qs (Q.qrun (unpark-q root (record (proj₁ o) { live = setAt j r (Flat.live (proj₁ o)) })))
  react-q op nb o nothing                                  = qk refl

  past-q : ∀ {B} op → (∀ k → ¬ op ≡ mergeᶠ (just k)) → ∀ (o : Out B) rx → Flat.queue (proj₁ o) ≡ 0 → Flat.queue (proj₁ (past op o rx)) ≡ 0
  past-q op nb o []                 z = z
  past-q op nb o ((q , out x) ∷ rx) z = past-q op nb (react op o x) rx (Q.qrun (react-q op nb o x) z)
  past-q op nb o ((q , end) ∷ rx)   z = z
  past-q op nb o ((q , skip) ∷ rx)  z = past-q op nb o rx z
  past-q op nb o ((q , pin _) ∷ rx) z = past-q op nb o rx z

queue-free : ∀ {B} op → (∀ k → ¬ op ≡ mergeᶠ (just k)) → ∀ rx → Flat.queue (proj₁ (past {B} op init rx)) ≡ 0
queue-free op nb rx = past-q op nb init rx refl

bounded? : ∀ op → (Σ ℕ λ k → op ≡ mergeᶠ (just k)) ⊎ (∀ k → ¬ op ≡ mergeᶠ (just k))
bounded? (mergeᶠ (just k)) = inj₁ (k , refl)
bounded? (mergeᶠ nothing)  = inj₂ λ _ ()
bounded? switchᶠ           = inj₂ λ _ ()
bounded? exhaustᶠ          = inj₂ λ _ ()

-- A step from `s` to `s′`: finished after, it was finished before, or `D`.
record Fin (D : Set) (s s′ : Flat Pos) : Set where
  constructor fin
  field frun : Flat.finished s′ ≡ true → Flat.finished s ≡ true ⊎ D

-- The row a scan reads an `outerDone` from.
OD : ∀ {B} → Maybe (Input B) → Set
OD x = Σ Branch λ b → Σ Pos λ n → x ≡ just (inj₁ (b , instEmit (mark outerDone) n))

private
  fkeep : ∀ {D s s′} → Flat.finished s′ ≡ Flat.finished s → Fin D s s′
  fkeep e = fin λ t → inj₁ (trans (sym e) t)

  bump-fin : ∀ b f s → Flat.finished (bump b f s) ≡ Flat.finished s
  bump-fin outerB f s = refl
  bump-fin laneB  f s = refl
  bump-fin closeB f s = refl

  cut-fin : ∀ {B} k n s → Flat.finished (proj₁ (cut {B} k n s)) ≡ Flat.finished s
  cut-fin k n s with Flat.spent s | anyHolds (Flat.at s) (Flat.live s)
  ... | true  | _     = refl
  ... | false | true  = refl
  ... | false | false = refl

  ended-fin : ∀ {B} k n s → Flat.finished (proj₁ (ended {B} k n s)) ≡ Flat.finished s
  ended-fin k n s with isZero (Flat.queue s)
  ... | false = refl
  ... | true with Flat.finished s ∧ isZero (Flat.active s)
  ...   | true  = refl
  ...   | false = cut-fin (k + Flat.held s) n (record s { held = 0 })

  begun-fin : ∀ {B} b n s → Flat.finished (proj₁ (begun {B} b n s)) ≡ Flat.finished s
  begun-fin b n s with does (n ≟ᵖ Flat.at s) ∧ Flat.spent s
  ... | true  = refl
  ... | false with does (n ≟ᵖ Flat.at s)
  ...   | true  = bump-fin b suc s
  ...   | false = bump-fin b suc (anew n s)

  stopped-fin : ∀ {B} b n s k → Flat.finished (proj₁ (stopped {B} b n s k)) ≡ Flat.finished s
  stopped-fin b n s zero    = refl
  stopped-fin b n s (suc _) = bump-fin b (_∸ 1) s

  overed-fin : ∀ {B} n s → Flat.finished (proj₁ (overed {B} n s)) ≡ Flat.finished s
  overed-fin n s with Flat.spent s
  ... | true  = refl
  ... | false = refl

  arrive-fin : ∀ {B} op n s → Flat.finished (proj₁ (arrive {B} op n s)) ≡ Flat.finished s
  arrive-fin (mergeᶠ (just _)) n s = refl
  arrive-fin (mergeᶠ nothing)  n s = refl
  arrive-fin switchᶠ           n s = cut-fin (Flat.lanes s) n (record s { active = 0 ; lanes = 0 })
  arrive-fin exhaustᶠ          n s = refl

  burst-fin : ∀ {B} h n s → Flat.finished (proj₁ (burstOver {B} h n s)) ≡ Flat.finished s
  burst-fin true  n s = refl
  burst-fin false n s = cut-fin (Flat.held s) n (record s { held = 0 })

  unpark-fin : ∀ {B} n s → Flat.finished (proj₁ (unpark {B} n s)) ≡ Flat.finished s
  unpark-fin n s with anyHolds (Flat.at s) (Flat.live s)
  ... | true  = refl
  ... | false = refl

  onMark-fin : ∀ {B} op b m n s → Fin (m ≡ outerDone) s (proj₁ (onMark {B} op b s m n))
  onMark-fin op b begin         n s = fkeep (begun-fin b n s)
  onMark-fin op b stop          n s = fkeep (stopped-fin b n s (if Flat.spent s then 0 else _))
  onMark-fin op b over          n s = fkeep (overed-fin n s)
  onMark-fin op b outerOpen     n s = fkeep (arrive-fin op n s)
  onMark-fin op b outerClose    n s = fkeep refl
  onMark-fin op b laneStart     n s = fkeep refl
  onMark-fin op b (laneDone kd) n s =
    fkeep (ended-fin (kd ⊓ Flat.lanes s) n (record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ kd ; dead = true }))
  onMark-fin op b burstEnd      n s = fkeep (burst-fin (isZero (Flat.held s) ∨ Flat.dead s) n s)
  onMark-fin op b outerDone     n s = fin λ _ → inj₂ refl
  onMark-fin op b subscribed    n s = fkeep refl
  onMark-fin op b completed     n s = fkeep refl

  od-of : ∀ {B} b {m} n → m ≡ outerDone → OD {B} (just (inj₁ (b , instEmit (mark m) n)))
  od-of b n refl = b , n , refl

-- ONE ROW READ: only an `outerDone` finishes the scan.
react-fin : ∀ {B} op (o : Out B) x → Fin (OD x) (proj₁ o) (proj₁ (react op o x))
react-fin op o (just (inj₁ (b , instEmit (value v) n))) = fkeep refl
react-fin op o (just (inj₁ (b , instEmit (mark m) n)))  =
  fin λ t → [ inj₁ , (λ e → inj₂ (od-of b n e)) ]′ (Fin.frun (onMark-fin op b m n (proj₁ o)) t)
react-fin op o (just (inj₂ (j , r)))                    = fkeep (unpark-fin root (record (proj₁ o) { live = setAt j r (Flat.live (proj₁ o)) }))
react-fin op o nothing                                  = fkeep refl

-- Where a run's scan finished: before it, or at an `outerDone` in it.
FinIn : ∀ {B} → Out B → List (Pos × Ev (Maybe (Input B))) → Set
FinIn {B} o rx = Flat.finished (proj₁ o) ≡ true ⊎ (Σ (List (Pos × Ev (Maybe (Input B)))) λ r₁ → Σ Pos λ k → Σ (Maybe (Input B)) λ x →
  Σ (List (Pos × Ev (Maybe (Input B)))) λ r₂ → rx ≡ r₁ ++ (k , out x) ∷ r₂ × OD x)

fin-back : ∀ {B} op (o : Out B) rx → Flat.finished (proj₁ (past op o rx)) ≡ true → FinIn o rx
fin-back op o []                 h = inj₁ h
fin-back op o ((q , end) ∷ rx)   h = inj₁ h
fin-back op o ((q , skip) ∷ rx)  h with fin-back op o rx h
... | inj₁ g = inj₁ g
... | inj₂ (r₁ , k , x , r₂ , refl , od) = inj₂ ((q , skip) ∷ r₁ , k , x , r₂ , refl , od)
fin-back op o ((q , pin w) ∷ rx) h with fin-back op o rx h
... | inj₁ g = inj₁ g
... | inj₂ (r₁ , k , x , r₂ , refl , od) = inj₂ ((q , pin w) ∷ r₁ , k , x , r₂ , refl , od)
fin-back op o ((q , out x) ∷ rx) h with fin-back op (react op o x) rx h
... | inj₂ (r₁ , k , y , r₂ , refl , od) = inj₂ ((q , out x) ∷ r₁ , k , y , r₂ , refl , od)
... | inj₁ g with Fin.frun (react-fin op o x) g
...   | inj₁ g′ = inj₁ g′
...   | inj₂ od = inj₂ ([] , q , x , rx , refl , od)

-- A SCAN FINISHED PAST A RUN READ AN `outerDone` IN IT.
finished-from : ∀ {B} op rx → Flat.finished (proj₁ (past {B} op init rx)) ≡ true
              → Σ (List (Pos × Ev (Maybe (Input B)))) λ r₁ → Σ Pos λ k → Σ (Maybe (Input B)) λ x → Σ (List (Pos × Ev (Maybe (Input B)))) λ r₂ →
                rx ≡ r₁ ++ (k , out x) ∷ r₂ × OD x
finished-from op rx f with fin-back op init rx f
... | inj₁ ()
... | inj₂ r = r

-- WHERE A LANE'S BURST CAN END ITS HANDED ROUTES: `dead` is set by a
-- `laneDone` alone and cleared by a `laneStart`; with none dead, a
-- `burstEnd` stops whatever is held.
private
  cut-dead : ∀ {B} k n s → Flat.dead (proj₁ (cut {B} k n s)) ≡ Flat.dead s
  cut-dead k n s with Flat.spent s | anyHolds (Flat.at s) (Flat.live s)
  ... | true  | _     = refl
  ... | false | true  = refl
  ... | false | false = refl

  bump-dead : ∀ b f s → Flat.dead (bump b f s) ≡ Flat.dead s
  bump-dead outerB f s = refl
  bump-dead laneB  f s = refl
  bump-dead closeB f s = refl

  unpark-dead : ∀ {B} n s → Flat.dead (proj₁ (unpark {B} n s)) ≡ Flat.dead s
  unpark-dead n s with anyHolds (Flat.at s) (Flat.live s)
  ... | true  = refl
  ... | false = refl

  begun-dead : ∀ {B} b n s → Flat.dead (proj₁ (begun {B} b n s)) ≡ Flat.dead s
  begun-dead b n s with does (n ≟ᵖ Flat.at s) ∧ Flat.spent s
  ... | true  = refl
  ... | false with does (n ≟ᵖ Flat.at s)
  ...   | true  = bump-dead b suc s
  ...   | false = bump-dead b suc (anew n s)

  stopped-dead : ∀ {B} b n s k → Flat.dead (proj₁ (stopped {B} b n s k)) ≡ Flat.dead s
  stopped-dead b n s zero    = refl
  stopped-dead b n s (suc _) = bump-dead b (_∸ 1) s

  overed-dead : ∀ {B} n s → Flat.dead (proj₁ (overed {B} n s)) ≡ Flat.dead s
  overed-dead n s with Flat.spent s
  ... | true  = refl
  ... | false = refl

  arrive-dead : ∀ {B} op n s → Flat.dead (proj₁ (arrive {B} op n s)) ≡ Flat.dead s
  arrive-dead (mergeᶠ (just _)) n s = refl
  arrive-dead (mergeᶠ nothing)  n s = refl
  arrive-dead switchᶠ           n s = cut-dead (Flat.lanes s) n (record s { active = 0 ; lanes = 0 })
  arrive-dead exhaustᶠ          n s = refl

  burst-dead : ∀ {B} h n s → Flat.dead (proj₁ (burstOver {B} h n s)) ≡ Flat.dead s
  burst-dead true  n s = refl
  burst-dead false n s = cut-dead (Flat.held s) n (record s { held = 0 })

  left-dead : ∀ {B} n s → Flat.dead (proj₁ (left {B} n (record s { finished = true }))) ≡ Flat.dead s
  left-dead n s with isZero (Flat.active s) ∧ isZero (Flat.queue s)
  ... | true  = refl
  ... | false = cut-dead (Flat.outer s) n (record s { finished = true ; outer = 0 })

  onMark-dead : ∀ {B} op b m n s → ¬ IsDone m → Flat.dead s ≡ false → Flat.dead (proj₁ (onMark {B} op b s m n)) ≡ false
  onMark-dead op b begin         n s _  h = trans (begun-dead b n s) h
  onMark-dead op b stop          n s _  h = trans (stopped-dead b n s (if Flat.spent s then 0 else _)) h
  onMark-dead op b over          n s _  h = trans (overed-dead n s) h
  onMark-dead op b outerOpen     n s _  h = trans (arrive-dead op n s) h
  onMark-dead op b outerClose    n s _  h = h
  onMark-dead op b laneStart     n s _  h = refl
  onMark-dead op b (laneDone kd) n s nd h = ⊥-elim (nd (kd , refl))
  onMark-dead op b burstEnd      n s _  h = trans (burst-dead (isZero (Flat.held s) ∨ Flat.dead s) n s) h
  onMark-dead op b outerDone     n s _  h = trans (left-dead n s) h
  onMark-dead op b subscribed    n s _  h = h
  onMark-dead op b completed     n s _  h = h

-- ONE ROW READ, no `laneDone`: none dead stays none dead.
react-dead : ∀ {B} op (o : Out B) x → ¬ LD x → Flat.dead (proj₁ o) ≡ false → Flat.dead (proj₁ (react op o x)) ≡ false
react-dead op o (just (inj₁ (b , instEmit (value v) n))) nd h = h
react-dead op o (just (inj₁ (b , instEmit (mark m) n)))  nd h = onMark-dead op b m n (proj₁ o) (λ { (kd , refl) → nd (b , kd , n , refl) }) h
react-dead op o (just (inj₂ (j , r)))                    nd h = trans (unpark-dead root (record (proj₁ o) { live = setAt j r (Flat.live (proj₁ o)) })) h
react-dead op o nothing                                  nd h = h

-- A `laneStart` read: none dead.
start-dead : ∀ {B} op (o : Out B) b n → Flat.dead (proj₁ (react op o (just (inj₁ (b , instEmit (mark laneStart) n))))) ≡ false
start-dead op o b n = refl

-- A run read with no `laneDone` and no end: none dead stays none dead.
past-dead : ∀ {B} op (o : Out B) rx → (∀ {c} → (c , end) ∈ rx → ⊥) → (∀ {q x} → (q , out x) ∈ rx → ¬ LD x)
          → Flat.dead (proj₁ o) ≡ false → Flat.dead (proj₁ (past op o rx)) ≡ false
past-dead op o []                 ne nl h = h
past-dead op o ((q , out x) ∷ rx) ne nl h = past-dead op (react op o x) rx (λ i → ne (there i)) (λ i → nl (there i)) (react-dead op o x (nl (here refl)) h)
past-dead op o ((q , end) ∷ rx)   ne nl h = ⊥-elim (ne (here refl))
past-dead op o ((q , skip) ∷ rx)  ne nl h = past-dead op o rx (λ i → ne (there i)) (λ i → nl (there i)) h
past-dead op o ((q , pin _) ∷ rx) ne nl h = past-dead op o rx (λ i → ne (there i)) (λ i → nl (there i)) h

-- A `burstEnd` read holding routes, none dead: it stops them all.
burst-clears : ∀ {B} op (o : Out B) b n → ¬ Flat.held (proj₁ o) ≡ 0 → Flat.dead (proj₁ o) ≡ false
             → Flat.held (proj₁ (react op o (just (inj₁ (b , instEmit (mark burstEnd) n))))) ≡ 0
burst-clears op (s , _) b n nz df with Flat.held s | Flat.dead s
... | zero  | _     = ⊥-elim (nz refl)
burst-clears op (s , _) b n nz () | suc _ | true
... | suc _ | false = cut-held (Flat.held s) n (record s { held = 0 })

-- The scan holding routes throughout a run, at one of its rows.
thru-split : ∀ {B} op (o : Out B) ra {b xb rb} → (∀ {c} → (c , end) ∈ ra → ⊥) → Thru op o (ra ++ (b , out xb) ∷ rb)
           → ¬ Flat.held (proj₁ (past op o ra)) ≡ 0 × Thru op (react op (past op o ra) xb) rb
thru-split op o []                 ne th       = th
thru-split op o ((q , out x) ∷ ra) ne (_ , th) = thru-split op (react op o x) ra (λ i → ne (there i)) th
thru-split op o ((q , end) ∷ ra)   ne th       = ⊥-elim (ne (here refl))
thru-split op o ((q , skip) ∷ ra)  ne th       = thru-split op o ra (λ i → ne (there i)) th
thru-split op o ((q , pin _) ∷ ra) ne th       = thru-split op o ra (λ i → ne (there i)) th

-- Whether a row is a `laneDone`.
ld? : ∀ {B} (x : Maybe (Input B)) → Dec (LD x)
ld? (just (inj₁ (b , instEmit (value _) _)))           = no λ { (_ , _ , _ , ()) }
ld? (just (inj₁ (b , instEmit (mark begin) _)))        = no λ { (_ , _ , _ , ()) }
ld? (just (inj₁ (b , instEmit (mark over) _)))         = no λ { (_ , _ , _ , ()) }
ld? (just (inj₁ (b , instEmit (mark stop) _)))         = no λ { (_ , _ , _ , ()) }
ld? (just (inj₁ (b , instEmit (mark outerOpen) _)))    = no λ { (_ , _ , _ , ()) }
ld? (just (inj₁ (b , instEmit (mark outerClose) _)))   = no λ { (_ , _ , _ , ()) }
ld? (just (inj₁ (b , instEmit (mark laneStart) _)))    = no λ { (_ , _ , _ , ()) }
ld? (just (inj₁ (b , instEmit (mark burstEnd) _)))     = no λ { (_ , _ , _ , ()) }
ld? (just (inj₁ (b , instEmit (mark outerDone) _)))    = no λ { (_ , _ , _ , ()) }
ld? (just (inj₁ (b , instEmit (mark (laneDone kd)) n))) = yes (b , kd , n , refl)
ld? (just (inj₁ (b , instEmit (mark subscribed) _)))   = no λ { (_ , _ , _ , ()) }
ld? (just (inj₁ (b , instEmit (mark completed) _)))    = no λ { (_ , _ , _ , ()) }
ld? (just (inj₂ _))                                    = no λ { (_ , _ , _ , ()) }
ld? nothing                                            = no λ { (_ , _ , _ , ()) }

private
  ld-skip : ∀ {B} q (e : Ev (Maybe (Input B))) → (∀ {x} → e ≡ out x → ⊥) → ∀ {rx}
          → (Σ (List (Pos × Ev (Maybe (Input B)))) λ r₁ → Σ Pos λ k → Σ (Maybe (Input B)) λ x → Σ (List (Pos × Ev (Maybe (Input B)))) λ r₂ →
               rx ≡ r₁ ++ (k , out x) ∷ r₂ × LD x)
            ⊎ (∀ {k x} → (k , out x) ∈ rx → ¬ LD x)
          → (Σ (List (Pos × Ev (Maybe (Input B)))) λ r₁ → Σ Pos λ k → Σ (Maybe (Input B)) λ x → Σ (List (Pos × Ev (Maybe (Input B)))) λ r₂ →
               (q , e) ∷ rx ≡ r₁ ++ (k , out x) ∷ r₂ × LD x)
            ⊎ (∀ {k x} → (k , out x) ∈ ((q , e) ∷ rx) → ¬ LD x)
  ld-skip q e no-out (inj₁ (r₁ , k , y , r₂ , refl , l)) = inj₁ ((q , e) ∷ r₁ , k , y , r₂ , refl , l)
  ld-skip q e no-out (inj₂ none) = inj₂ λ { (here eq) → ⊥-elim (no-out (sym (cong proj₂ eq))) ; (there i) → none i }

-- A run's first `laneDone`, or none.
find-ld : ∀ {B} (rx : List (Pos × Ev (Maybe (Input B))))
        → (Σ (List (Pos × Ev (Maybe (Input B)))) λ r₁ → Σ Pos λ q → Σ (Maybe (Input B)) λ x → Σ (List (Pos × Ev (Maybe (Input B)))) λ r₂ →
             rx ≡ r₁ ++ (q , out x) ∷ r₂ × LD x)
        ⊎ (∀ {q x} → (q , out x) ∈ rx → ¬ LD x)
find-ld [] = inj₂ λ ()
find-ld ((q , out x) ∷ rx) with ld? x
... | yes l = inj₁ ([] , q , x , rx , refl , l)
... | no nl with find-ld rx
...   | inj₁ (r₁ , k , y , r₂ , refl , l) = inj₁ ((q , out x) ∷ r₁ , k , y , r₂ , refl , l)
...   | inj₂ none = inj₂ λ { (here refl) → nl ; (there i) → none i }
find-ld ((q , end) ∷ rx)   = ld-skip q end (λ ()) (find-ld rx)
find-ld ((q , skip) ∷ rx)  = ld-skip q skip (λ ()) (find-ld rx)
find-ld ((q , pin w) ∷ rx) = ld-skip q (pin w) (λ ()) (find-ld rx)

-- The scan past a row, past what it read before.
past-app : ∀ {B} op (o : Out B) r₁ {q x r₂} → (∀ {c} → (c , end) ∈ r₁ → ⊥)
         → past op o (r₁ ++ (q , out x) ∷ r₂) ≡ past op (react op (past op o r₁) x) r₂
past-app op o []                 ne = refl
past-app op o ((k , out y) ∷ r₁) ne = past-app op (react op o y) r₁ (λ i → ne (there i))
past-app op o ((k , end) ∷ r₁)   ne = ⊥-elim (ne (here refl))
past-app op o ((k , skip) ∷ r₁)  ne = past-app op o r₁ (λ i → ne (there i))
past-app op o ((k , pin _) ∷ r₁) ne = past-app op o r₁ (λ i → ne (there i))
