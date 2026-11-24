{-# OPTIONS --guardedness #-}

-- ROUTES HELD SURVIVE A RUN THAT ASKS NOTHING OF THEM (`held-on`).  Held
-- routes are dropped only by a begin of another instant, an over, a
-- lane's end with no lane queued and the flatMap not ending with it, or a
-- burst's end with its lane still running; each row of the run names the
-- held instant, or finds a lane queued, or the last lane done (`Keeps`).
-- An over read past them leaves the scan spent to the end.
module simultaneous.HeldKeep where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊓_)
open import Data.Nat.Properties using (m+n≡0⇒m≡0)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Relation.Nullary using (¬_; does)

open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; end; skip; pin)
open import simultaneous.InstEmit using (instEmit; value; mark; Mark; begin; stop; over; outerOpen; outerClose; laneStart; laneDone;
  burstEnd; outerDone; subscribed; completed)
open import simultaneous.SObs using (Flat; Branch; isZero; lone; module Elaborate)
open import simultaneous.HeldComb using (past)
open import simultaneous.FlatLanes using (bump-at; bump-sp; does-no)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Out; Input; react; onMark; begun; bump; stopped; overed;
  cut; unpark; arrive; ended; burstOver; left; anyHolds; setAt)

-- What a row read at `s` asks for the routes of `A` held to survive it.
Keeps : ∀ {B} → Pos → Flat Pos → Maybe (Input B) → Set
Keeps A s (just (inj₁ (_ , instEmit (mark begin) n)))        = n ≡ A
Keeps A s (just (inj₁ (_ , instEmit (mark (laneDone _)) _))) = ¬ Flat.queue s ≡ 0 ⊎ (Flat.finished s ≡ true × Flat.active s ∸ 1 ≡ 0)
Keeps A s (just (inj₁ (_ , instEmit (mark burstEnd) _)))     = Flat.dead s ≡ true
Keeps A s _                                                 = ⊤

-- What a row asks for the instant and a spent mark to survive it.
Names : ∀ {B} → Pos → Maybe (Input B) → Set
Names A (just (inj₁ (_ , instEmit (mark begin) n))) = n ≡ A
Names A _                                           = ⊤

-- A row names `A` when, being a begin, it names `A`.
names-of : ∀ {B A} (x : Maybe (Input B)) → (∀ {b n} → x ≡ just (inj₁ (b , instEmit (mark begin) n)) → n ≡ A) → Names A x
names-of (just (inj₁ (_ , instEmit (mark begin) n)))        e = e refl
names-of (just (inj₁ (_ , instEmit (mark stop) n)))         e = tt
names-of (just (inj₁ (_ , instEmit (mark over) n)))         e = tt
names-of (just (inj₁ (_ , instEmit (mark outerOpen) n)))    e = tt
names-of (just (inj₁ (_ , instEmit (mark outerClose) n)))   e = tt
names-of (just (inj₁ (_ , instEmit (mark laneStart) n)))    e = tt
names-of (just (inj₁ (_ , instEmit (mark (laneDone _)) n))) e = tt
names-of (just (inj₁ (_ , instEmit (mark burstEnd) n)))     e = tt
names-of (just (inj₁ (_ , instEmit (mark outerDone) n)))    e = tt
names-of (just (inj₁ (_ , instEmit (mark subscribed) n)))   e = tt
names-of (just (inj₁ (_ , instEmit (mark completed) n)))    e = tt
names-of (just (inj₁ (_ , instEmit (value _) n)))           e = tt
names-of (just (inj₂ _))                                    e = tt
names-of nothing                                            e = tt

-- Every row of a run.
Named : ∀ {B} → Pos → List (Pos × Ev (Maybe (Input B))) → Set
Named A rx = ∀ r₁ {q x} r₂ → rx ≡ r₁ ++ (q , out x) ∷ r₂ → Names A x

-- Every row of a run, read where the scan stands.
Along : ∀ {B} → FlatOp → Pos → Out B → List (Pos × Ev (Maybe (Input B))) → Set
Along op A o rx = ∀ r₁ {q x} r₂ → rx ≡ r₁ ++ (q , out x) ∷ r₂ → Keeps A (proj₁ (past op o r₁)) x

-- An over a run reads.
OverIn : ∀ {B} → List (Pos × Ev (Maybe (Input B))) → Set
OverIn rx = Σ _ λ r₁ → Σ Pos λ q → Σ Branch λ b → Σ Pos λ n → Σ _ λ r₂ → rx ≡ r₁ ++ (q , out (just (inj₁ (b , instEmit (mark over) n)))) ∷ r₂

private
  t≢f : true ≡ false → ⊥
  t≢f ()

  -- A step that keeps the instant and an over's mark, and the routes
  -- held unless it is an over.
  record Moved (s s′ : Flat Pos) (Ov : Set) : Set where
    constructor moved
    field
      at′ : Flat.at s′ ≡ Flat.at s
      sp′ : Flat.spent s ≡ true → Flat.spent s′ ≡ true
      hd′ : ¬ Flat.held s ≡ 0 → ¬ Flat.held s′ ≡ 0 ⊎ (Ov × Flat.spent s′ ≡ true)

  -- The instant, the spent mark and the routes held, all three.
  record Same (s s′ : Flat Pos) : Set where
    constructor same
    field
      hd : Flat.held s′ ≡ Flat.held s
      at : Flat.at s′ ≡ Flat.at s
      sp : Flat.spent s′ ≡ Flat.spent s

  mv : ∀ {s s′ Ov} → Same s s′ → Moved s s′ Ov
  mv (same h a p) = moved a (λ z → trans p z) λ nz → inj₁ λ z → nz (trans (sym h) z)

  same-then : ∀ {s s₁ s₂} → Same s s₁ → Same s₁ s₂ → Same s s₂
  same-then (same h a p) (same h′ a′ p′) = same (trans h′ h) (trans a′ a) (trans p′ p)

  bump-same : ∀ b f s → Same s (bump b f s)
  bump-same b f s = same (hd b) (bump-at b f s) (bump-sp b f s)
    where
      hd : ∀ b → Flat.held (bump b f s) ≡ Flat.held s
      hd Branch.outerB = refl
      hd Branch.laneB  = refl
      hd Branch.closeB = refl

  cut-same : ∀ {B} k n s → Same s (proj₁ (cut {B} k n s))
  cut-same k n s with Flat.spent s | anyHolds (Flat.at s) (Flat.live s)
  ... | true  | _     = same refl refl refl
  ... | false | true  = same refl refl refl
  ... | false | false = same refl refl refl

  unpark-same : ∀ {B} n s → Same s (proj₁ (unpark {B} n s))
  unpark-same n s with anyHolds (Flat.at s) (Flat.live s)
  ... | true  = same refl refl refl
  ... | false = same refl refl refl

  isZero-0 : ∀ {k} → isZero k ≡ true → k ≡ 0
  isZero-0 {zero} _ = refl
  isZero-0 {suc _} ()

  begun-mv : ∀ {B Ov} A b n s → n ≡ A → Flat.at s ≡ A → Moved s (proj₁ (begun {B} b n s)) Ov
  begun-mv A b n s e a with does (n ≟ᵖ Flat.at s) ∧ Flat.spent s
  ... | true  = mv (same refl refl refl)
  ... | false with does (n ≟ᵖ Flat.at s) in d
  ...   | true  = mv (bump-same b suc s)
  ...   | false = ⊥-elim (does-no d (trans e (sym a)))

  stopped-mv : ∀ {B Ov} b n s k → Moved s (proj₁ (stopped {B} b n s k)) Ov
  stopped-mv b n s zero    = mv (same refl refl refl)
  stopped-mv b n s (suc _) = mv (bump-same b (_∸ 1) s)

  overed-mv : ∀ {B Ov} → Ov → ∀ n s → Moved s (proj₁ (overed {B} n s)) Ov
  overed-mv ov n s with Flat.spent s in e
  ... | true  = mv (same refl refl refl)
  ... | false = moved refl (λ z → ⊥-elim (t≢f (trans (sym z) e))) λ _ → inj₂ (ov , refl)

  arrive-mv : ∀ {B Ov} op n s → Moved s (proj₁ (arrive {B} op n s)) Ov
  arrive-mv (mergeᶠ (just _)) n s = mv (same refl refl refl)
  arrive-mv (mergeᶠ nothing)  n s = mv (same refl refl refl)
  arrive-mv switchᶠ           n s = mv (same-then (same refl refl refl) (cut-same (Flat.lanes s) n (record s { active = 0 ; lanes = 0 })))
  arrive-mv exhaustᶠ          n s = mv (same refl refl refl)

  -- A lane's end, past a lane queued or with the flatMap ending: the
  -- routes it hands are added to those held.
  ended-mv : ∀ {B Ov} k n s₀ s → Same s₀ s → (¬ Flat.queue s ≡ 0 ⊎ (Flat.finished s ≡ true × Flat.active s ≡ 0))
           → Moved s₀ (proj₁ (ended {B} k n s)) Ov
  ended-mv k n s₀ s (same h a p) kp with isZero (Flat.queue s) in e
  ... | false = moved a (λ z → trans p z) λ nz → inj₁ λ z → nz (trans (sym h) (m+n≡0⇒m≡0 (Flat.held s) z))
  ... | true with Flat.finished s ∧ isZero (Flat.active s) in e₂
  ...   | true  = moved a (λ z → trans p z) λ nz → inj₁ λ z → nz (trans (sym h) (m+n≡0⇒m≡0 (Flat.held s) z))
  ...   | false = ⊥-elim (no kp)
    where
      no : ¬ Flat.queue s ≡ 0 ⊎ (Flat.finished s ≡ true × Flat.active s ≡ 0) → ⊥
      no (inj₁ qn)        = qn (isZero-0 e)
      no (inj₂ (f , a0)) = t≢f (trans (sym (cong₂∧ f (cong isZero a0))) e₂)
        where
          cong₂∧ : ∀ {x y} → x ≡ true → y ≡ true → x ∧ y ≡ true
          cong₂∧ refl refl = refl

  burst-mv : ∀ {B Ov} h n s → h ≡ true → Moved s (proj₁ (burstOver {B} h n s)) Ov
  burst-mv .true n s refl = mv (same refl refl refl)

  left-mv : ∀ {B Ov} n s → Moved s (proj₁ (left {B} n (record s { finished = true }))) Ov
  left-mv n s with isZero (Flat.active s) ∧ isZero (Flat.queue s)
  ... | true  = mv (same refl refl refl)
  ... | false = mv (same-then (same refl refl refl) (cut-same (Flat.outer s) n (record s { finished = true ; outer = 0 })))

  IsOver : ∀ {B} → Maybe (Input B) → Set
  IsOver {B} x = Σ Branch λ b → Σ Pos λ n → x ≡ just (inj₁ (b , instEmit (mark over) n))

  onMark-mv : ∀ {B} op A b m n s → Keeps {B} A s (just (inj₁ (b , instEmit (mark m) n))) → Flat.at s ≡ A
            → Moved s (proj₁ (onMark {B} op b s m n)) (IsOver {B} (just (inj₁ (b , instEmit (mark m) n))))
  onMark-mv op A b begin         n s k a = begun-mv A b n s k a
  onMark-mv op A b stop          n s k a = stopped-mv b n s (if Flat.spent s then 0 else _)
  onMark-mv op A b over          n s k a = overed-mv (b , n , refl) n s
  onMark-mv op A b outerOpen     n s k a = arrive-mv op n s
  onMark-mv op A b outerClose    n s k a = mv (same refl refl refl)
  onMark-mv op A b laneStart     n s k a = mv (same refl refl refl)
  onMark-mv op A b (laneDone kd) n s k a =
    ended-mv (kd ⊓ Flat.lanes s) n s (record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ kd ; dead = true }) (same refl refl refl) k
  onMark-mv op A b burstEnd      n s k a = burst-mv _ n s (trans (cong (isZero (Flat.held s) ∨_) k) (∨-zeroʳ _))
  onMark-mv op A b outerDone     n s k a = left-mv n s
  onMark-mv op A b subscribed    n s k a = mv (same refl refl refl)
  onMark-mv op A b completed     n s k a = mv (same refl refl refl)

  react-mv : ∀ {B} op A (o : Out B) x → Keeps A (proj₁ o) x → Flat.at (proj₁ o) ≡ A → Moved (proj₁ o) (proj₁ (react op o x)) (IsOver x)
  react-mv op A o (just (inj₁ (b , instEmit (value v) n))) k a = mv (same refl refl refl)
  react-mv op A o (just (inj₁ (b , instEmit (mark m) n)))  k a = onMark-mv op A b m n (proj₁ o) k a
  react-mv op A o (just (inj₂ (j , r)))                    k a = mv (same-then (same refl refl refl) (unpark-same root (record (proj₁ o) { live = setAt j r (Flat.live (proj₁ o)) })))
  react-mv op A o nothing                                  k a = mv (same refl refl refl)

  -- A step that keeps the instant and a spent mark.
  record Kept (s s′ : Flat Pos) : Set where
    constructor kept
    field
      at″ : Flat.at s′ ≡ Flat.at s
      sp″ : Flat.spent s ≡ true → Flat.spent s′ ≡ true

  kp : ∀ {s s′ Ov} → Moved s s′ Ov → Kept s s′
  kp (moved a p _) = kept a p

  kthen : ∀ {s₀ s s′} → Kept s₀ s → Same s s′ → Kept s₀ s′
  kthen (kept a p) (same _ a′ p′) = kept (trans a′ a) (λ z → trans p′ (p z))

  ended-kept : ∀ {B} k n s₀ s → Same s₀ s → Kept s₀ (proj₁ (ended {B} k n s))
  ended-kept k n s₀ s (same h a p) with isZero (Flat.queue s)
  ... | false = kept a (λ z → trans p z)
  ... | true with Flat.finished s ∧ isZero (Flat.active s)
  ...   | true  = kept a (λ z → trans p z)
  ...   | false = kthen (kept a (λ z → trans p z)) (cut-same (k + Flat.held s) n (record s { held = 0 }))

  burst-kept : ∀ {B} h n s → Kept s (proj₁ (burstOver {B} h n s))
  burst-kept true  n s = kept refl (λ z → z)
  burst-kept false n s = kthen (kept refl (λ z → z)) (cut-same (Flat.held s) n (record s { held = 0 }))

  onMark-kept : ∀ {B} op A b m n s → Names {B} A (just (inj₁ (b , instEmit (mark m) n))) → Flat.at s ≡ A
              → Kept s (proj₁ (onMark {B} op b s m n))
  onMark-kept op A b begin         n s k a = kp (begun-mv {Ov = ⊤} A b n s k a)
  onMark-kept op A b stop          n s k a = kp (stopped-mv {Ov = ⊤} b n s (if Flat.spent s then 0 else _))
  onMark-kept op A b over          n s k a = kp (overed-mv {Ov = ⊤} tt n s)
  onMark-kept op A b outerOpen     n s k a = kp (arrive-mv {Ov = ⊤} op n s)
  onMark-kept op A b outerClose    n s k a = kept refl (λ z → z)
  onMark-kept op A b laneStart     n s k a = kept refl (λ z → z)
  onMark-kept op A b (laneDone kd) n s k a =
    ended-kept (kd ⊓ Flat.lanes s) n s (record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ kd ; dead = true }) (same refl refl refl)
  onMark-kept op A b burstEnd      n s k a = burst-kept (isZero (Flat.held s) ∨ Flat.dead s) n s
  onMark-kept op A b outerDone     n s k a = kp (left-mv {Ov = ⊤} n s)
  onMark-kept op A b subscribed    n s k a = kept refl (λ z → z)
  onMark-kept op A b completed     n s k a = kept refl (λ z → z)

  react-kept : ∀ {B} op A (o : Out B) x → Names A x → Flat.at (proj₁ o) ≡ A → Kept (proj₁ o) (proj₁ (react op o x))
  react-kept op A o (just (inj₁ (b , instEmit (value v) n))) k a = kept refl (λ z → z)
  react-kept op A o (just (inj₁ (b , instEmit (mark m) n)))  k a = onMark-kept op A b m n (proj₁ o) k a
  react-kept op A o (just (inj₂ (j , r)))                    k a = kp (mv {Ov = ⊤} (same-then (same refl refl refl) (unpark-same root (record (proj₁ o) { live = setAt j r (Flat.live (proj₁ o)) }))))
  react-kept op A o nothing                                  k a = kept refl (λ z → z)

  keeps-names : ∀ {B A s} (x : Maybe (Input B)) → Keeps A s x → Names A x
  keeps-names x k = names-of x λ { refl → k }

  named : ∀ {B} op A (o : Out B) rx → Along op A o rx → Named A rx
  named op A o rx al r₁ {x = x} r₂ eq = keeps-names x (al r₁ r₂ eq)

-- PAST AN OVER, SPENT: no row the run reads begins another instant.
spent-on : ∀ {B} op A (o : Out B) rx → Named A rx → Flat.at (proj₁ o) ≡ A → Flat.spent (proj₁ o) ≡ true
         → Flat.spent (proj₁ (past op o rx)) ≡ true
spent-on op A o []               nm a sp = sp
spent-on op A o ((q , end) ∷ rx) nm a sp = sp
spent-on op A o ((q , skip) ∷ rx) nm a sp = spent-on op A o rx (λ r₁ r₂ eq → nm ((q , skip) ∷ r₁) r₂ (cong (_ ∷_) eq)) a sp
spent-on op A o ((q , pin w) ∷ rx) nm a sp = spent-on op A o rx (λ r₁ r₂ eq → nm ((q , pin w) ∷ r₁) r₂ (cong (_ ∷_) eq)) a sp
spent-on op A o ((q , out x) ∷ rx) nm a sp =
  spent-on op A (react op o x) rx (λ r₁ r₂ eq → nm ((q , out x) ∷ r₁) r₂ (cong (_ ∷_) eq)) (trans (Kept.at″ K) a) (Kept.sp″ K sp)
  where
    K = react-kept op A o x (nm [] rx refl) a

-- ROUTES HELD SURVIVE A RUN ASKING NOTHING OF THEM, unless it reads an
-- over and the scan is live past it.
held-on : ∀ {B} op A (o : Out B) rx → Along op A o rx → Flat.at (proj₁ o) ≡ A → ¬ Flat.held (proj₁ o) ≡ 0
        → (OverIn rx → Flat.spent (proj₁ (past op o rx)) ≡ false) → ¬ Flat.held (proj₁ (past op o rx)) ≡ 0
held-on op A o []               al a nz lv = nz
held-on op A o ((q , end) ∷ rx) al a nz lv = nz
held-on op A o ((q , skip) ∷ rx) al a nz lv =
  held-on op A o rx (λ r₁ r₂ eq → al ((q , skip) ∷ r₁) r₂ (cong (_ ∷_) eq)) a nz
    λ (r₁ , ov) → lv ((q , skip) ∷ r₁ , let (k , b , n , r₂ , eq) = ov in k , b , n , r₂ , cong (_ ∷_) eq)
held-on op A o ((q , pin w) ∷ rx) al a nz lv =
  held-on op A o rx (λ r₁ r₂ eq → al ((q , pin w) ∷ r₁) r₂ (cong (_ ∷_) eq)) a nz
    λ (r₁ , ov) → lv ((q , pin w) ∷ r₁ , let (k , b , n , r₂ , eq) = ov in k , b , n , r₂ , cong (_ ∷_) eq)
held-on op A o ((q , out x) ∷ rx) al a nz lv = go (Moved.hd′ M nz)
  where
    M = react-mv op A o x (al [] rx refl) a

    al′ : Along op A (react op o x) rx
    al′ r₁ r₂ eq = al ((q , out x) ∷ r₁) r₂ (cong (_ ∷_) eq)

    go : ¬ Flat.held (proj₁ (react op o x)) ≡ 0 ⊎ (IsOver x × Flat.spent (proj₁ (react op o x)) ≡ true)
       → ¬ Flat.held (proj₁ (past op o ((q , out x) ∷ rx))) ≡ 0
    go (inj₁ nz′) = held-on op A (react op o x) rx al′ (trans (Moved.at′ M) a) nz′
      λ (r₁ , ov) → lv ((q , out x) ∷ r₁ , let (k , b , n , r₂ , eq) = ov in k , b , n , r₂ , cong (_ ∷_) eq)
    go (inj₂ ((b , n , e) , sp)) =
      ⊥-elim (t≢f (trans (sym (spent-on op A (react op o x) rx (named op A (react op o x) rx al′) (trans (Moved.at′ M) a) sp))
        (lv ([] , q , b , n , rx , cong (λ z → (q , out z) ∷ rx) e))))
