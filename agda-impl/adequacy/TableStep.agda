-- ONE ENGINE STEP AGAINST THE TABLE.  At an unbounded merge's frame, the
-- engine's race (`raceT`) picks a key no later than every row the frame
-- still owes, and what it shows is one of those rows.  It needs only that
-- each child's candidate does the same for that child's remaining rows: a
-- per-node lower bound, never a walk along a stream.
--
-- The frame's remaining rows are `FlatRem`: the outer's still to come, the
-- lane each future outer value begins, and the running lanes' rows.  Kinds
-- are elided where they do not move a position: the bound reads positions,
-- and what a row shows is read only at the winner.
--
-- Two invariants of the table, not of the engine, carry the proof: the
-- outer owes one row per position (`Single`), and a lane begun at `p` owes
-- nothing before `p` (`Inside`).  Both are per-node and compositional.
module adequacy.TableStep where

open import Data.Bool using (true; false; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _++_; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (pred; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import denotation.MonotonicList.Events using (Pos; ix)
open import denotation.Table using (Table; out; skip; end)
open import operation.Key using (Key; at; after; _<ᴷ_)
open import operation.PureObservable using (module Machine)
open import adequacy.Engine.Head using (≮ᴷ-trans; <ᴷ-trans; <ᴷ-irrefl; ext-≮; clash)
open import adequacy.Engine.Head.Race using (shift-≮)

open Machine using (Cand; Out; still; shows; nx; cp; raceT; outerT; laneT; shift) renaming (Ev to Evᴹ)

------------------------------------------------------------------------
-- Bounds

-- At or past.  A record, so that it is read by its two keys.
record _⊒_ (a b : Key) : Set where
  constructor ge
  field un : a <ᴷ b ≡ false
open _⊒_

-- Every row at or past a key.
From : ∀ {A} → Key → Table A → Set
From h t = ∀ {q e} → t q e → at q ⊒ h

evᵀ : ∀ {A} → Evᴹ A → denotation.Table.Ev A
evᵀ (nx a) = out a
evᵀ cp     = end

-- What a candidate shows is a row at its key.
Shows : ∀ {A} → Table A → Key → Out A → Set
Shows t h         still     = ⊤
Shows t (at p)    (shows e) = t p (evᵀ e)
Shows t (after p) (shows e) = ⊥

-- A candidate bounds a table: none, and the table owes nothing; else its
-- key is no later than any row, and what it shows is a row.
Bound : ∀ {R A} → Table A → Maybe (Cand R A) → Set
Bound t nothing  = ∀ {q e} → ¬ t q e
Bound t (just c) = From (proj₁ (proj₂ c)) t × Shows t (proj₁ (proj₂ c)) (proj₂ (proj₂ c))

-- One row per position.
Single : ∀ {A} → Table A → Set
Single t = ∀ {q e e′} → t q e → t q e′ → e ≡ e′

-- A lane begun at `p` owes nothing before `p`.
Inside : ∀ {A B} → (A → Pos → Table B) → Set
Inside f = ∀ {a p q e} → f a p q e → at q ⊒ at p

-- An outer's row that is not a value, as the frame passes it on.
pass : ∀ {A B} → denotation.Table.Ev A → denotation.Table.Ev B
pass end = end
pass _   = skip

-- An unbounded merge's remaining rows: an outer value's skip just past
-- it, the lane it begins, the outer's other rows, the running lanes' rows.
data FlatRem {A B : Set} (o : Table A) (f : A → Pos → Table B) (l : Table B) : Table B where
  oval  : ∀ {q a} → o q (out a) → FlatRem o f l (q ++ [ ix 0 ]) skip
  olane : ∀ {q a r e} → o q (out a) → f a (q ++ [ ix 1 ]) r e → FlatRem o f l r e
  opass : ∀ {q e} → o q e → (∀ {a} → ¬ e ≡ out a) → FlatRem o f l q (pass e)
  lane  : ∀ {q e} → l q e → FlatRem o f l q e

------------------------------------------------------------------------
-- Keys

postulate
  -- Just past a key: nothing strictly between.
  <ᴷ-step  : ∀ {h k} → h <ᴷ k ≡ true → k ⊒ shift h
  -- A lane's slot is past its value's skip.
  ix-past  : ∀ q → at (q ++ [ ix 1 ]) ⊒ at (q ++ [ ix 0 ])
  -- At or past: the same key, or strictly past.
  ⊒-split  : ∀ {a b} → a ⊒ b → a ≡ b ⊎ b <ᴷ a ≡ true

⊒-trans : ∀ {a b c} → a ⊒ b → b ⊒ c → a ⊒ c
⊒-trans {a} {b} {c} (ge x) (ge y) = ge (≮ᴷ-trans a b c x y)

<ᴷ-asym : ∀ {a b} → a <ᴷ b ≡ true → b ⊒ a
<ᴷ-asym {a} {b} ab with b <ᴷ a in ba
... | false = ge ba
... | true  = ⊥-elim (clash (<ᴷ-trans a b a ab ba) (<ᴷ-irrefl a))

-- Under a position is not before it.
under : ∀ q x → at (q ++ x) ⊒ at q
under q x = ge (ext-≮ q x)

-- Just past what is not before a key: not before just past it.
shifted : ∀ {q h} → at q ⊒ h → at (q ++ [ ix 0 ]) ⊒ shift h
shifted {q} {h} (ge x) = ge (shift-≮ q h x)

-- Every row of a lane begun under an outer row at or past `h`.
lane-past : ∀ {q r h} → at r ⊒ at (q ++ [ ix 1 ]) → at q ⊒ h → at r ⊒ h
lane-past {q} rq qh = ⊒-trans (⊒-trans rq (under q [ ix 1 ])) qh

-- Read at a merge's lane key: a merge's lane end never shifts.
lane-from : ∀ {A B : Set} d n k (ol : Out B) {t : Table B} → From k t → From (proj₁ (laneT {A = A} d n [] k ol)) t
lane-from d n k still          fk r = fk r
lane-from d n k (shows (nx b)) fk r = fk r
lane-from d n k (shows cp)     fk r = fk r

------------------------------------------------------------------------
-- The race

-- The outer wins at `h`: every row at or past where its event lands,
-- given the lanes' rows are.
outer-wins : ∀ {A B} {o : Table A} {f : A → Pos → Table B} {l : Table B} → Single o → Inside f → ∀ n h (oo : Out A) →
  From h o → Shows o h oo → (∀ {q e} → l q e → at q ⊒ proj₁ (outerT {B = B} n [] h oo)) →
  From (proj₁ (outerT {B = B} n [] h oo)) (FlatRem o f l)
outer-wins sg ins n h still          oh sh lh (oval {q} r)    = ⊒-trans (under q [ ix 0 ]) (oh r)
outer-wins sg ins n h still          oh sh lh (olane r fr)    = lane-past (ins fr) (oh r)
outer-wins sg ins n h still          oh sh lh (opass r _)     = oh r
outer-wins sg ins n h still          oh sh lh (lane r)        = lh r
outer-wins sg ins n h (shows cp)     oh sh lh (oval {q} r)    = ⊒-trans (under q [ ix 0 ]) (oh r)
outer-wins sg ins n h (shows cp)     oh sh lh (olane r fr)    = lane-past (ins fr) (oh r)
outer-wins sg ins n h (shows cp)     oh sh lh (opass r _)     = oh r
outer-wins sg ins n h (shows cp)     oh sh lh (lane r)        = lh r
outer-wins sg ins n h (shows (nx a)) oh sh lh (oval r)        = shifted (oh r)
outer-wins sg ins n h (shows (nx a)) oh sh lh (olane {q} r fr) = ⊒-trans (ins fr) (⊒-trans (ix-past q) (shifted (oh r)))
outer-wins sg ins n (at p) (shows (nx a)) oh sh lh (opass r no) with ⊒-split (oh r)
... | inj₁ refl = ⊥-elim (no (sg r sh))
... | inj₂ pq   = <ᴷ-step pq
outer-wins sg ins n (after p) (shows (nx a)) oh () lh (opass r no)
outer-wins sg ins n h (shows (nx a)) oh sh lh (lane r)        = lh r

-- A lane wins at `k`, the outer at or past it: every row at or past `k`.
lane-wins : ∀ {A B} {o : Table A} {f : A → Pos → Table B} {l : Table B} → Inside f → ∀ {h k} →
  From h o → From k l → h ⊒ k → From k (FlatRem o f l)
lane-wins ins oh lk hk (oval {q} r)  = ⊒-trans (⊒-trans (under q [ ix 0 ]) (oh r)) hk
lane-wins ins oh lk hk (olane r fr)  = ⊒-trans (lane-past (ins fr) (oh r)) hk
lane-wins ins oh lk hk (opass r _)   = ⊒-trans (oh r) hk
lane-wins ins oh lk hk (lane r)      = lk r

-- The outer's event as the frame shows it is a row of the frame.
outer-shows : ∀ {A B} {o : Table A} {f : A → Pos → Table B} {l : Table B} → ∀ n h (oo : Out A) →
  Shows o h oo → Shows (FlatRem o f l) (proj₁ (outerT {B = B} n [] h oo)) (proj₂ (outerT {B = B} n [] h oo))
outer-shows n h          still          sh = tt
outer-shows n h          (shows (nx a)) sh = tt
outer-shows n (at p)     (shows cp)     sh with n ≡ᵇ 0
... | true  = opass sh (λ ())
... | false = tt
outer-shows n (after p)  (shows cp)     ()

-- A lane's event as the frame shows it is a row of the frame.
lane-shows : ∀ {A B} {o : Table A} {f : A → Pos → Table B} {l : Table B} → ∀ d n k (ol : Out B) →
  Shows l k ol → Shows (FlatRem o f l) (proj₁ (laneT {A = A} d n [] k ol)) (proj₂ (laneT {A = A} d n [] k ol))
lane-shows d n k         still          sh = tt
lane-shows d n (at p)    (shows (nx b)) sh = lane sh
lane-shows d n (after p) (shows (nx b)) ()
lane-shows d n (at p)    (shows cp)     sh with d ∧ (pred n ≡ᵇ 0)
... | true  = lane sh
... | false = tt
lane-shows d n (after p) (shows cp)     ()

-- THE STEP: the race at an unbounded merge's frame bounds the frame's
-- remaining rows, given its outer's candidate and its lanes' do.
race-bound : ∀ {R A B} {o : Table A} {f : A → Pos → Table B} {l : Table B} → Single o → Inside f → ∀ d n
  (co : Maybe (Cand R A)) (cl : Maybe (Cand R B)) → Bound o co → Bound l cl →
  Bound (FlatRem o f l) (raceT d n [] co cl)
race-bound sg ins d n nothing nothing bo bl (oval r)    = bo r
race-bound sg ins d n nothing nothing bo bl (olane r _) = bo r
race-bound sg ins d n nothing nothing bo bl (opass r _) = bo r
race-bound sg ins d n nothing nothing bo bl (lane r)    = bl r
race-bound {A = A} {o = o} {f} {l} sg ins d n nothing (just (g , k , ol)) bo (lk , sh) =
  lane-from {A = A} d n k ol {t = FlatRem o f l} only , lane-shows {A = A} d n k ol sh
  where
    only : From k (FlatRem o f l)
    only (oval r)    = ⊥-elim (bo r)
    only (olane r _) = ⊥-elim (bo r)
    only (opass r _) = ⊥-elim (bo r)
    only (lane r)    = lk r
race-bound sg ins d n (just (fo , h , oo)) nothing (oh , sh) bl =
  outer-wins sg ins n h oo oh sh (λ r → ⊥-elim (bl r)) , outer-shows n h oo sh
race-bound {A = A} {B} {o = o} {f} {l} sg ins d n (just (fo , h , oo)) (just (g , k , ol)) (oh , sh) (lk , lsh) with h <ᴷ k in hk
... | true  = outer-wins sg ins n h oo oh sh (λ r → ⊒-trans (lk r) (past oo)) , outer-shows n h oo sh
  where
    past : ∀ (u : Out A) → k ⊒ proj₁ (outerT {B = B} n [] h u)
    past still          = <ᴷ-asym hk
    past (shows cp)     = <ᴷ-asym hk
    past (shows (nx a)) = <ᴷ-step hk
... | false = lane-from {A = A} d n k ol {t = FlatRem o f l} (lane-wins ins oh lk (ge hk)) , lane-shows {A = A} d n k ol lsh
