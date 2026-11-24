{-# OPTIONS --guardedness #-}

-- FLATMAP'S SCAN COUNTS AT LEAST THE OUTER'S ROUTES OF AN INSTANT
-- (`past-above`), wherever the rows met before it keep to that instant.
-- Begins of the instant's name fall in the instant and every begin in it
-- names it; no over and no `outerDone` falls in it; and from the first
-- row in it on, every row is in it.  Then once the scan's instant is the
-- name, it stays the name, nothing spends it, and every outer begin of
-- the name adds to the outer counter as to the outer's count, every outer
-- stop takes from both, and nothing else lowers the counter.
module simultaneous.ScanAbove where

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m∸n≤m; ∸-monoˡ-≤)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
import Data.Bool.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_; does; yes; no)
open import quickcheck.Tabled.Exact.Base using (≟-true)

open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Position using (Pos; root; _≟ᵖ_; sub; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; end; skip; pin)
open import simultaneous.InstEmit using (instEmit; value; mark; Mark; begin; stop; over; outerOpen; outerClose; laneStart;
  laneDone; burstEnd; outerDone; subscribed; completed)
open import simultaneous.SObs using (Flat; Branch; outerB; laneB; closeB; isZero; lone; module Elaborate)
open import simultaneous.Relations using (values)
open import simultaneous.HeldComb using (past)
open import simultaneous.FlatLanes using (Tg; brTag; BProj; keep; drop; module BProj; other; tagged; bump-at; bump-sp; bump-other; ∧-t; does-no)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Routes; count; Out; Input; react; onMark; begun; entered;
  bump; share; stopped; overed; cut; unpark; arrive; ended; burstOver; left; anyHolds; setAt; anew; opening)

Row : Set → Set
Row B = Pos × Ev (Maybe (Input B))

------------------------------------------------------------------------
-- Steps that keep the instant, the over and the outer counter

record Keeps (s s′ : Flat Pos) : Set where
  constructor keeps
  field
    at≡  : Flat.at s′ ≡ Flat.at s
    sp≡  : Flat.spent s′ ≡ Flat.spent s
    out≡ : Flat.outer s′ ≡ Flat.outer s

keeps-trans : ∀ {s₁ s₂ s₃} → Keeps s₁ s₂ → Keeps s₂ s₃ → Keeps s₁ s₃
keeps-trans (keeps a₁ p₁ o₁) (keeps a₂ p₂ o₂) = keeps (trans a₂ a₁) (trans p₂ p₁) (trans o₂ o₁)

cut-keeps : ∀ {B} k n s → Keeps s (proj₁ (cut {B} k n s))
cut-keeps k n s with Flat.spent s | anyHolds (Flat.at s) (Flat.live s)
... | true  | _     = keeps refl refl refl
... | false | true  = keeps refl refl refl
... | false | false = keeps refl refl refl

arrive-keeps : ∀ {B} op n s → Keeps s (proj₁ (arrive {B} op n s))
arrive-keeps (mergeᶠ (just _)) n s = keeps refl refl refl
arrive-keeps (mergeᶠ nothing)  n s = keeps refl refl refl
arrive-keeps switchᶠ           n s = keeps-trans (keeps refl refl refl) (cut-keeps (Flat.lanes s) n (record s { active = 0 ; lanes = 0 }))
arrive-keeps exhaustᶠ          n s = keeps refl refl refl

ended-keeps : ∀ {B} k n s → Keeps s (proj₁ (ended {B} k n s))
ended-keeps k n s with isZero (Flat.queue s)
... | false = keeps refl refl refl
... | true with Flat.finished s ∧ isZero (Flat.active s)
...   | true  = keeps refl refl refl
...   | false = keeps-trans (keeps refl refl refl) (cut-keeps (k + Flat.held s) n (record s { held = 0 }))
  where open Data.Nat using (_+_)

burst-keeps : ∀ {B} h n s → Keeps s (proj₁ (burstOver {B} h n s))
burst-keeps true  n s = keeps refl refl refl
burst-keeps false n s = keeps-trans (keeps refl refl refl) (cut-keeps (Flat.held s) n (record s { held = 0 }))

unpark-keeps : ∀ {B} n s → Keeps s (proj₁ (unpark {B} n s))
unpark-keeps n s with anyHolds (Flat.at s) (Flat.live s)
... | true  = keeps refl refl refl
... | false = keeps refl refl refl

-- A mark no route reads, and no outer end.
quiet-keeps : ∀ {B} op b m n s → (m ≡ begin → ⊥) → (m ≡ stop → ⊥) → (m ≡ over → ⊥) → (m ≡ outerDone → ⊥)
            → Keeps s (proj₁ (onMark {B} op b s m n))
quiet-keeps op b begin         n s nb _  _  _  = ⊥-elim (nb refl)
quiet-keeps op b stop          n s _  ns _  _  = ⊥-elim (ns refl)
quiet-keeps op b over          n s _  _  no′ _ = ⊥-elim (no′ refl)
quiet-keeps op b outerDone     n s _  _  _  nd = ⊥-elim (nd refl)
quiet-keeps op b outerOpen     n s _  _  _  _  = arrive-keeps op n s
quiet-keeps op b outerClose    n s _  _  _  _  = keeps refl refl refl
quiet-keeps op b laneStart     n s _  _  _  _  = keeps refl refl refl
quiet-keeps op b (laneDone kd) n s _  _  _  _  =
  keeps-trans (keeps refl refl refl) (ended-keeps (kd Data.Nat.⊓ Flat.lanes s) n (record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ kd ; dead = true }))
quiet-keeps op b burstEnd      n s _  _  _  _  = burst-keeps (isZero (Flat.held s) Data.Bool.∨ Flat.dead s) n s
quiet-keeps op b subscribed    n s _  _  _  _  = keeps refl refl refl
quiet-keeps op b completed     n s _  _  _  _  = keeps refl refl refl

-- A stop lowers its branch's counter by one, or leaves it.
stopped-cases : ∀ {B} b n s k → proj₁ (stopped {B} b n s k) ≡ s ⊎ proj₁ (stopped {B} b n s k) ≡ bump b (_∸ 1) s
stopped-cases b n s zero    = inj₁ refl
stopped-cases b n s (suc _) = inj₂ refl

-- A begin past the instant's over is dropped; else counted, under its
-- name kept or begun afresh.
entered-cases : ∀ b n s → (n ≡ Flat.at s × entered b n s ≡ bump b suc s) ⊎ (¬ n ≡ Flat.at s × entered b n s ≡ bump b suc (anew n s))
entered-cases b n s with does (n ≟ᵖ Flat.at s) in e
... | true  = inj₁ (≟-true {n} {Flat.at s} e , refl)
... | false = inj₂ (does-no {n} {Flat.at s} e , refl)

∧-l : ∀ {a b : Bool} → a ∧ b ≡ true → a ≡ true
∧-l {true} _ = refl

does-yes : ∀ {n m : Pos} → n ≡ m → does (n ≟ᵖ m) ≡ true
does-yes {n} {m} e with n ≟ᵖ m
... | yes _ = refl
... | no ne = ⊥-elim (ne e)

begun-cases : ∀ {B} b n s → (n ≡ Flat.at s × Flat.spent s ≡ true × proj₁ (begun {B} b n s) ≡ s)
            ⊎ (n ≡ Flat.at s × Flat.spent s ≡ false × proj₁ (begun {B} b n s) ≡ bump b suc s)
            ⊎ (¬ n ≡ Flat.at s × proj₁ (begun {B} b n s) ≡ bump b suc (anew n s))
begun-cases b n s with does (n ≟ᵖ Flat.at s) ∧ Flat.spent s in e
... | true  = inj₁ (≟-true {n} {Flat.at s} (∧-l {does (n ≟ᵖ Flat.at s)} {Flat.spent s} e) , ∧-t {does (n ≟ᵖ Flat.at s)} {Flat.spent s} e , refl)
... | false with entered-cases b n s
...   | inj₁ (nat , eq) = inj₂ (inj₁ (nat , subst (λ d → d ∧ Flat.spent s ≡ false) (does-yes nat) e , eq))
...   | inj₂ ne = inj₂ (inj₂ ne)

-- Every mark but a begin keeps the instant.
at-same : ∀ {B} op b m n s → (m ≡ begin → ⊥) → Flat.at (proj₁ (onMark {B} op b s m n)) ≡ Flat.at s
at-same op b begin n s nb = ⊥-elim (nb refl)
at-same {B} op b stop n s _ with stopped-cases {B} b n s (if Flat.spent s then 0 else share b s)
... | inj₁ e = cong Flat.at e
... | inj₂ e = trans (cong Flat.at e) (bump-at b (_∸ 1) s)
at-same op b over n s _ with Flat.spent s
... | true  = refl
... | false = refl
at-same op b outerDone n s _ with isZero (Flat.active s) ∧ isZero (Flat.queue s)
... | true  = refl
... | false = Keeps.at≡ (cut-keeps (Flat.outer s) n (record s { finished = true ; outer = 0 }))
at-same op b outerOpen     n s _ = Keeps.at≡ (quiet-keeps op b outerOpen n s (λ ()) (λ ()) (λ ()) (λ ()))
at-same op b outerClose    n s _ = refl
at-same op b laneStart     n s _ = refl
at-same op b (laneDone kd) n s _ = Keeps.at≡ (quiet-keeps op b (laneDone kd) n s (λ ()) (λ ()) (λ ()) (λ ()))
at-same op b burstEnd      n s _ = Keeps.at≡ (quiet-keeps op b burstEnd n s (λ ()) (λ ()) (λ ()) (λ ()))
at-same op b subscribed    n s _ = refl
at-same op b completed     n s _ = refl

------------------------------------------------------------------------
-- The invariant

-- What a row met before the instant's last row keeps to: a begin names
-- the instant's name just where it is in the instant, an over in it
-- grants `Ov`, and no outer end is in it.
record Good {B} (N : Pos) (In : Pos → Set) (Ov : Set) (q : Pos) (e : Ev (Maybe (Input B))) : Set where
  field
    beg : ∀ {b n} → e ≡ out (Tg b (instEmit (mark begin) n)) → (n ≡ N → In q) × (In q → n ≡ N)
    ov  : ∀ {b n} → In q → e ≡ out (Tg b (instEmit (mark over) n)) → Ov
    nod : ∀ {b n} → In q → e ≡ out (Tg b (instEmit (mark outerDone) n)) → ⊥

-- Past a row in the instant, only rows in it.
Conv : ∀ {B} → (Pos → Set) → List (Row B) → Set
Conv In rx = ∀ r₁ {q e} r₂ → rx ≡ r₁ ++ (q , e) ∷ r₂ → In q → ∀ {k e′} → (k , e′) ∈ r₂ → In k

-- The scan once at the name: unspent unless an over granted `Ov`,
-- holding at least the outer's routes of the name unless spent, and with
-- only rows of the instant left.
record Above {B} (N : Pos) (In : Pos → Set) (Ov : Set) (s : Flat Pos) (c : Routes) (rest : List (Row B)) : Set where
  field
    live  : Flat.at s ≡ N → Flat.spent s ≡ false ⊎ Ov
    below : proj₁ c ≡ N → Flat.at s ≡ N × (Flat.spent s ≡ true ⊎ proj₂ c ≤ Flat.outer s)
    ahead : Flat.at s ≡ N → ∀ {k e} → (k , e) ∈ rest → In k

module _ {B : Set} {N : Pos} {In : Pos → Set} {Ov : Set} where
  private
    Ab = Above {B} N In Ov
    Gd = Good {B} N In Ov

  off-above : ∀ {s c rest} → ¬ Flat.at s ≡ N → ¬ proj₁ c ≡ N → Ab s c rest
  off-above na nc = record { live = λ a → ⊥-elim (na a) ; below = λ e → ⊥-elim (nc e) ; ahead = λ a → ⊥-elim (na a) }

  c-off : ∀ {s c rest} → Ab s c rest → ¬ Flat.at s ≡ N → ¬ proj₁ c ≡ N
  c-off L na e = na (proj₁ (Above.below L e))

  keeps-above : ∀ {s s′ c r rest} → Keeps s s′ → Ab s c (r ∷ rest) → Ab s′ c rest
  keeps-above {c = c} (keeps a p o) L = record
    { live  = λ e → [ (λ f → inj₁ (trans p f)) , inj₂ ]′ (Above.live L (trans (sym a) e))
    ; below = λ e → let (a′ , l) = Above.below L e in trans a a′ , [ (λ t → inj₁ (trans p t)) , (λ l′ → inj₂ (subst (proj₂ c ≤_) (sym o) l′)) ]′ l
    ; ahead = λ e i → Above.ahead L (trans (sym a) e) (there i) }

  -- An outer stop takes one from the count and at most one from the counter.
  stop-above : ∀ {s s′ c r rest} → s′ ≡ s ⊎ s′ ≡ bump outerB (_∸ 1) s → Ab s c (r ∷ rest) → Ab s′ (proj₁ c , proj₂ c ∸ 1) rest
  stop-above {c = c} (inj₁ refl) L = record
    { live  = Above.live L
    ; below = λ e → let (a , l) = Above.below L e in a , [ inj₁ , (λ l′ → inj₂ (≤-trans (m∸n≤m (proj₂ c) 1) l′)) ]′ l
    ; ahead = λ e i → Above.ahead L e (there i) }
  stop-above {c = c} (inj₂ refl) L = record
    { live  = Above.live L
    ; below = λ e → let (a , l) = Above.below L e in a , [ inj₁ , (λ l′ → inj₂ (∸-monoˡ-≤ 1 l′)) ]′ l
    ; ahead = λ e i → Above.ahead L e (there i) }

  -- A begin's name is the count's or its own.
  count-name : ∀ {A₀ : Set} c n → proj₁ (count c (instEmit {A = A₀} (mark begin) n)) ≡ proj₁ c ⊎ proj₁ (count c (instEmit {A = A₀} (mark begin) n)) ≡ n
  count-name c n with does (n ≟ᵖ proj₁ c)
  ... | true  = inj₁ refl
  ... | false = inj₂ refl

  off-begin : ∀ {A₀ : Set} {s′ c} n → ¬ Flat.at s′ ≡ N → ¬ proj₁ c ≡ N → ¬ n ≡ N → ∀ {rest} → Ab s′ (count c (instEmit {A = A₀} (mark begin) n)) rest
  off-begin {A₀} {c = c} n na nc nn with count-name {A₀} c n
  ... | inj₁ e = off-above na (λ e′ → nc (trans (sym e) e′))
  ... | inj₂ e = off-above na (λ e′ → nn (trans (sym e) e′))

  -- THE OUTER'S BEGIN.
  own-begin : ∀ {A₀ : Set} {q} n s c rest → Gd q (out (Tg {B} outerB (instEmit (mark begin) n)))
            → (In q → ∀ {k e} → (k , e) ∈ rest → In k)
            → Ab s c ((q , out (Tg outerB (instEmit (mark begin) n))) ∷ rest)
            → Ab (proj₁ (begun {B} outerB n s)) (count c (instEmit {A = A₀} (mark begin) n)) rest
  own-begin {A₀} {q} n s c rest G cv L with Flat.at s ≟ᵖ N
  ... | yes a with Good.beg G refl
  ...   | (_ , nN) with nN (Above.ahead L a (here refl)) | begun-cases {B} outerB n s
  ...     | refl | inj₁ (_ , sp , eq) = subst (λ z → Ab z (count c (instEmit {A = A₀} (mark begin) N)) rest) (sym eq) (record
    { live  = Above.live L
    ; below = λ _ → a , inj₁ sp
    ; ahead = λ e i → Above.ahead L e (there i) })
  ...     | refl | inj₂ (inj₂ (ne , _)) = ⊥-elim (ne (sym a))
  ...     | refl | inj₂ (inj₁ (_ , sf , eq)) = subst (λ z → Ab z (count c (instEmit {A = A₀} (mark begin) N)) rest) (sym eq) (record
    { live  = λ _ → inj₁ sf
    ; below = bl
    ; ahead = λ e i → Above.ahead L e (there i) })
    where
      bl : proj₁ (count c (instEmit {A = A₀} (mark begin) N)) ≡ N
         → Flat.at s ≡ N × (Flat.spent s ≡ true ⊎ proj₂ (count c (instEmit {A = A₀} (mark begin) N)) ≤ suc (Flat.outer s))
      bl e with does (N ≟ᵖ proj₁ c)
      ... | false = a , inj₂ (s≤s z≤n)
      ... | true with proj₂ (Above.below L e)
      ...   | inj₁ t = ⊥-elim (Data.Bool.Properties.not-¬ (trans (sym sf) t) refl)
      ...   | inj₂ l = a , inj₂ (s≤s l)
  own-begin {A₀} {q} n s c rest G cv L | no na with begun-cases {B} outerB n s
  ... | inj₁ (nat , _ , eq) = subst (λ z → Ab z (count c (instEmit {A = A₀} (mark begin) n)) rest) (sym eq)
                                (off-begin {A₀} n na (c-off L na) (λ nN → na (trans (sym nat) nN)))
  ... | inj₂ (inj₁ (nat , _ , eq)) = subst (λ z → Ab z (count c (instEmit {A = A₀} (mark begin) n)) rest) (sym eq)
                                (off-begin {A₀} n na (c-off L na) (λ nN → na (trans (sym nat) nN)))
  ... | inj₂ (inj₂ (_ , eq)) = subst (λ z → Ab z (count c (instEmit {A = A₀} (mark begin) n)) rest) (sym eq) (fresh′ (n ≟ᵖ N))
    where
      fresh′ : Relation.Nullary.Dec (n ≡ N) → Ab (bump outerB suc (anew n s)) (count c (instEmit {A = A₀} (mark begin) n)) rest
      fresh′ (no nN)    = off-begin {A₀} n nN (c-off L na) nN
      fresh′ (yes refl) = record
        { live  = λ _ → inj₁ refl
        ; below = bl
        ; ahead = λ _ → cv (proj₁ (Good.beg G refl) refl) }
        where
          bl : proj₁ (count c (instEmit {A = A₀} (mark begin) N)) ≡ N → N ≡ N × (false ≡ true ⊎ proj₂ (count c (instEmit {A = A₀} (mark begin) N)) ≤ 1)
          bl e with does (N ≟ᵖ proj₁ c) in d
          ... | true  = ⊥-elim (c-off L na (sym (≟-true {N} {proj₁ c} d)))
          ... | false = refl , inj₂ ≤-refl

  -- ANOTHER BRANCH'S BEGIN.
  other-begin : ∀ {q} b n s c rest → (b ≡ outerB → ⊥) → Gd q (out (Tg {B} b (instEmit (mark begin) n)))
              → (In q → ∀ {k e} → (k , e) ∈ rest → In k)
              → Ab s c ((q , out (Tg b (instEmit (mark begin) n))) ∷ rest) → Ab (proj₁ (begun {B} b n s)) c rest
  other-begin {q} b n s c rest nb G cv L with Flat.at s ≟ᵖ N
  ... | yes a with Good.beg G refl
  ...   | (_ , nN) with nN (Above.ahead L a (here refl)) | begun-cases {B} b n s
  ...     | refl | inj₁ (_ , _ , eq) = keeps-above (subst (Keeps s) (sym eq) (keeps refl refl refl)) L
  ...     | refl | inj₂ (inj₂ (ne , _)) = ⊥-elim (ne (sym a))
  ...     | refl | inj₂ (inj₁ (_ , _ , eq)) =
    keeps-above (subst (Keeps s) (sym eq) (keeps (bump-at b suc s) (bump-sp b suc s) (bump-other outerB b suc s nb))) L
  other-begin {q} b n s c rest nb G cv L | no na with begun-cases {B} b n s
  ... | inj₁ (_ , _ , eq) = subst (λ z → Ab z c rest) (sym eq) (off-above na (c-off L na))
  ... | inj₂ (inj₁ (_ , _ , eq)) = subst (λ z → Ab z c rest) (sym eq) (off-above (λ e → na (trans (sym (bump-at b suc s)) e)) (c-off L na))
  ... | inj₂ (inj₂ (_ , eq)) = subst (λ z → Ab z c rest) (sym eq) (fresh′ (n ≟ᵖ N))
    where
      fresh′ : Relation.Nullary.Dec (n ≡ N) → Ab (bump b suc (anew n s)) c rest
      fresh′ (no nN)    = off-above (λ e → nN (trans (sym (bump-at b suc (anew n s))) e)) (c-off L na)
      fresh′ (yes refl) = record
        { live  = λ _ → inj₁ (bump-sp b suc (anew N s))
        ; below = λ e → ⊥-elim (c-off L na e)
        ; ahead = λ _ → cv (proj₁ (Good.beg G refl) refl) }

  -- An over or an outer end: never in the instant, so never at the name.
  off-mark : ∀ {q e} op b m n s c c′ rest → (m ≡ begin → ⊥) → (In q → ⊥) → proj₁ c′ ≡ proj₁ c
           → Ab s c ((q , e) ∷ rest) → Ab (proj₁ (onMark {B} op b s m n)) c′ rest
  off-mark op b m n s c c′ rest nb nq cc L with Flat.at s ≟ᵖ N
  ... | yes a = ⊥-elim (nq (Above.ahead L a (here refl)))
  ... | no na = off-above (λ e → na (trans (sym (at-same op b m n s nb)) e)) (λ e → c-off L na (trans (sym cc) e))

  -- An over at the name spends it.
  over-on : ∀ {q e c c′ rest} n s → Flat.at s ≡ N → Ov → Ab s c ((q , e) ∷ rest) → Ab (proj₁ (overed {B} n s)) c′ rest
  over-on n s a ov L with Flat.spent s in sp
  ... | true  = record { live = λ _ → inj₂ ov ; below = λ _ → a , inj₁ sp ; ahead = λ e i → Above.ahead L e (there i) }
  ... | false = record { live = λ _ → inj₂ ov ; below = λ _ → a , inj₁ refl ; ahead = λ e i → Above.ahead L e (there i) }

  -- THE OUTER'S MARK.
  own-mark : ∀ {A₀ : Set} {q} op m n s c rest → Gd q (out (Tg {B} outerB (instEmit (mark m) n)))
           → (In q → ∀ {k e} → (k , e) ∈ rest → In k)
           → Ab s c ((q , out (Tg outerB (instEmit (mark m) n))) ∷ rest)
           → Ab (proj₁ (onMark {B} op outerB s m n)) (count c (instEmit {A = A₀} (mark m) n)) rest
  own-mark {A₀} op begin n s c rest G cv L = own-begin {A₀} n s c rest G cv L
  own-mark op stop  n s c rest G cv L = stop-above (stopped-cases outerB n s (if Flat.spent s then 0 else Flat.outer s)) L
  own-mark op over  n s c rest G cv L with Flat.at s ≟ᵖ N
  ... | yes a = over-on n s a (Good.ov G (Above.ahead L a (here refl)) refl) L
  ... | no na = off-above (λ e → na (trans (sym (at-same op outerB over n s (λ ()))) e)) (c-off L na)
  own-mark op outerDone n s c rest G cv L with Flat.at s ≟ᵖ N
  ... | yes a = ⊥-elim (Good.nod G (Above.ahead L a (here refl)) refl)
  ... | no na = off-above (λ e → na (trans (sym (at-same op outerB outerDone n s (λ ()))) e)) (c-off L na)
  own-mark op outerOpen     n s c rest G cv L = keeps-above (quiet-keeps {B} op outerB outerOpen n s (λ ()) (λ ()) (λ ()) (λ ())) L
  own-mark op outerClose    n s c rest G cv L = keeps-above (quiet-keeps {B} op outerB outerClose n s (λ ()) (λ ()) (λ ()) (λ ())) L
  own-mark op laneStart     n s c rest G cv L = keeps-above (quiet-keeps {B} op outerB laneStart n s (λ ()) (λ ()) (λ ()) (λ ())) L
  own-mark op (laneDone kd) n s c rest G cv L = keeps-above (quiet-keeps {B} op outerB (laneDone kd) n s (λ ()) (λ ()) (λ ()) (λ ())) L
  own-mark op burstEnd      n s c rest G cv L = keeps-above (quiet-keeps {B} op outerB burstEnd n s (λ ()) (λ ()) (λ ()) (λ ())) L
  own-mark op subscribed    n s c rest G cv L = keeps-above (quiet-keeps {B} op outerB subscribed n s (λ ()) (λ ()) (λ ()) (λ ())) L
  own-mark op completed     n s c rest G cv L = keeps-above (quiet-keeps {B} op outerB completed n s (λ ()) (λ ()) (λ ()) (λ ())) L

  -- ANOTHER BRANCH'S MARK.
  other-mark : ∀ {q} op b m n s c rest → (b ≡ outerB → ⊥) → Gd q (out (Tg {B} b (instEmit (mark m) n)))
             → (In q → ∀ {k e} → (k , e) ∈ rest → In k)
             → Ab s c ((q , out (Tg b (instEmit (mark m) n))) ∷ rest) → Ab (proj₁ (onMark {B} op b s m n)) c rest
  other-mark op b begin n s c rest nb G cv L = other-begin b n s c rest nb G cv L
  other-mark op b stop  n s c rest nb G cv L with stopped-cases {B} b n s (if Flat.spent s then 0 else share b s)
  ... | inj₁ eq = keeps-above (subst (Keeps s) (sym eq) (keeps refl refl refl)) L
  ... | inj₂ eq = keeps-above (subst (Keeps s) (sym eq) (keeps (bump-at b (_∸ 1) s) (bump-sp b (_∸ 1) s) (bump-other outerB b (_∸ 1) s nb))) L
  other-mark op b over  n s c rest nb G cv L with Flat.at s ≟ᵖ N
  ... | yes a = over-on n s a (Good.ov G (Above.ahead L a (here refl)) refl) L
  ... | no na = off-above (λ e → na (trans (sym (at-same op b over n s (λ ()))) e)) (c-off L na)
  other-mark op b outerDone n s c rest nb G cv L with Flat.at s ≟ᵖ N
  ... | yes a = ⊥-elim (Good.nod G (Above.ahead L a (here refl)) refl)
  ... | no na = off-above (λ e → na (trans (sym (at-same op b outerDone n s (λ ()))) e)) (c-off L na)
  other-mark op b outerOpen     n s c rest nb G cv L = keeps-above (quiet-keeps {B} op b outerOpen n s (λ ()) (λ ()) (λ ()) (λ ())) L
  other-mark op b outerClose    n s c rest nb G cv L = keeps-above (quiet-keeps {B} op b outerClose n s (λ ()) (λ ()) (λ ()) (λ ())) L
  other-mark op b laneStart     n s c rest nb G cv L = keeps-above (quiet-keeps {B} op b laneStart n s (λ ()) (λ ()) (λ ()) (λ ())) L
  other-mark op b (laneDone kd) n s c rest nb G cv L = keeps-above (quiet-keeps {B} op b (laneDone kd) n s (λ ()) (λ ()) (λ ()) (λ ())) L
  other-mark op b burstEnd      n s c rest nb G cv L = keeps-above (quiet-keeps {B} op b burstEnd n s (λ ()) (λ ()) (λ ()) (λ ())) L
  other-mark op b subscribed    n s c rest nb G cv L = keeps-above (quiet-keeps {B} op b subscribed n s (λ ()) (λ ()) (λ ()) (λ ())) L
  other-mark op b completed     n s c rest nb G cv L = keeps-above (quiet-keeps {B} op b completed n s (λ ()) (λ ()) (λ ()) (λ ())) L

  -- A row of another branch, or of a tracker.
  step-drop : ∀ {q} op (o : Out B) x c rest → brTag {B} outerB (out x) ≡ nothing → Gd q (out x)
            → (In q → ∀ {k e} → (k , e) ∈ rest → In k)
            → Ab (proj₁ o) c ((q , out x) ∷ rest) → Ab (proj₁ (react op o x)) c rest
  step-drop op o nothing c rest _ G cv L = keeps-above (keeps refl refl refl) L
  step-drop op o (just (inj₂ (j , r))) c rest _ G cv L =
    keeps-above (keeps-trans (keeps refl refl refl) (unpark-keeps root (record (proj₁ o) { live = setAt j r (Flat.live (proj₁ o)) }))) L
  step-drop op o (just (inj₁ (b , instEmit (value _) n))) c rest _ G cv L = keeps-above (keeps refl refl refl) L
  step-drop op o (just (inj₁ (b , instEmit (mark m) n))) c rest nl G cv L =
    other-mark op b m n (proj₁ o) c rest (other outerB b nl) G cv L

  -- A row of the outer, opened.
  step-keep : ∀ {q} op (o : Out B) {A} (x : IE A) c rest → Gd q (out (Tg {B} outerB (opening x)))
            → (In q → ∀ {k e} → (k , e) ∈ rest → In k)
            → Ab (proj₁ o) c ((q , out (Tg outerB (opening x))) ∷ rest) → Ab (proj₁ (react op o (Tg outerB (opening x)))) (count c x) rest
  step-keep op o (instEmit (value _) n) c rest G cv L = keeps-above (quiet-keeps {B} op outerB outerOpen n (proj₁ o) (λ ()) (λ ()) (λ ()) (λ ())) L
  step-keep op o (instEmit (mark m) n)  c rest G cv L = own-mark op m n (proj₁ o) c rest G cv L

  -- THE SCAN HOLDS AT LEAST THE OUTER'S ROUTES OF THE NAME, past a run
  -- that meets nothing past its end.
  past-above : ∀ {A} J op (o : Out B) c rx rs → (∀ r₁ {q} r₂ → rx ≡ r₁ ++ (q , end) ∷ r₂ → r₂ ≡ [])
             → BProj outerB (opening {A} {B}) J rx rs → (∀ {q e} → (q , e) ∈ rx → Gd q e) → Conv In rx
             → Ab (proj₁ o) c rx → Ab (proj₁ (past op o rx)) (L.foldl count c (values rs)) []
  past-above J op o c [] [] _ BProj.[] _ _ L = L
  past-above J op o c (_ ∷ rx) (_ ∷ rs) tl (keep {x = x} pr) gd cv L =
    past-above J op (react op o (Tg outerB (opening x))) (count c x) rx rs (λ r₁ r₂ eq → tl (_ ∷ r₁) r₂ (cong (_ ∷_) eq)) pr
      (λ i → gd (there i)) (λ r₁ r₂ eq → cv (_ ∷ r₁) r₂ (cong (_ ∷_) eq))
      (step-keep op o x c rx (gd (here refl)) (cv [] rx refl) L)
  past-above J op o c ((q , out x) ∷ rx) rs tl (drop tg pr) gd cv L =
    past-above J op (react op o x) c rx rs (λ r₁ r₂ eq → tl (_ ∷ r₁) r₂ (cong (_ ∷_) eq)) pr
      (λ i → gd (there i)) (λ r₁ r₂ eq → cv (_ ∷ r₁) r₂ (cong (_ ∷_) eq))
      (step-drop op o x c rx tg (gd (here refl)) (cv [] rx refl) L)
  past-above J op o c ((q , end) ∷ rx) rs tl (drop _ pr) gd cv L with tl [] rx refl
  past-above J op o c ((q , end) ∷ .[]) .[] tl (drop _ BProj.[]) gd cv L | refl = keeps-above (keeps refl refl refl) L
  past-above J op o c ((q , skip) ∷ rx) rs tl (drop _ pr) gd cv L =
    past-above J op o c rx rs (λ r₁ r₂ eq → tl (_ ∷ r₁) r₂ (cong (_ ∷_) eq)) pr
      (λ i → gd (there i)) (λ r₁ r₂ eq → cv (_ ∷ r₁) r₂ (cong (_ ∷_) eq)) (keeps-above (keeps refl refl refl) L)
  past-above J op o c ((q , pin _) ∷ rx) rs tl (drop _ pr) gd cv L =
    past-above J op o c rx rs (λ r₁ r₂ eq → tl (_ ∷ r₁) r₂ (cong (_ ∷_) eq)) pr
      (λ i → gd (there i)) (λ r₁ r₂ eq → cv (_ ∷ r₁) r₂ (cong (_ ∷_) eq)) (keeps-above (keeps refl refl refl) L)

-- A projection's last row of the branch, kept last.
bproj-snoc : ∀ {A B b} {h : IE A → IE B} {J} rx {q v rs′} → BProj b h J (rx ++ (q , out (Tg b v)) ∷ []) rs′
           → Σ _ λ rs → Σ Pos λ y → Σ (IE A) λ x → BProj b h J rx rs × rs′ ≡ rs ++ (y , out x) ∷ [] × q ≡ y ⊕ (sub J ∷ []) × v ≡ h x
bproj-snoc []                 (keep BProj.[]) = [] , _ , _ , BProj.[] , refl , refl , refl
bproj-snoc {b = b}  []        (drop nl _)     = ⊥-elim (tagged b nl)
bproj-snoc (_ ∷ rx) (keep pr) with bproj-snoc rx pr
... | rs , y , x , pr′ , refl , eq , ev = _ ∷ rs , y , x , keep pr′ , refl , eq , ev
bproj-snoc (_ ∷ rx) (drop nl pr) with bproj-snoc rx pr
... | rs , y , x , pr′ , refl , eq , ev = rs , y , x , drop nl pr′ , refl , eq , ev
