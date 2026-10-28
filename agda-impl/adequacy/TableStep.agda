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
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (pred; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Pos; Timeline; ix)
open import denotation.Table using (Table; out; skip; end)
open import operation.Key using (Key; at; after; _<ᴷ_)
open import operation.PureObservable using (module Machine)
open import adequacy.Engine.Head using (≮ᴷ-trans; <ᴷ-trans; <ᴷ-irrefl; ext-≮; clash)
open import adequacy.Engine.Head.Race using (shift-≮)

open Machine using (Cand; Out; still; shows; nx; cp; raceT; outerT; laneT; shift; St; Ctx; closed; Conf; dequeue) renaming (Ev to Evᴹ)

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

------------------------------------------------------------------------
-- Concat: one lane at a time, the rest queued

-- The outer's part of a concat frame's remaining rows: a value's skip
-- just past it, the lane it begins, at once or from the queue at a later
-- end (either way at or past that skip), its other rows.
data OuterRem {A B : Set} (o : Table A) (f : A → Pos → Table B) : Table B where
  oval  : ∀ {q a} → o q (out a) → OuterRem o f (q ++ [ ix 0 ]) skip
  olane : ∀ {q a p r e} → o q (out a) → at p ⊒ at (q ++ [ ix 0 ]) → f a p r e → OuterRem o f r e
  opass : ∀ {q e} → o q e → (∀ {a} → ¬ e ≡ out a) → OuterRem o f q (pass e)

-- The running lane's part: its rows short of its end; its end, nothing
-- waiting; the skip handing over to the queue; each queued lane, begun at
-- or past the slot after that end.
data LaneRem {A B : Set} (f : A → Pos → Table B) (l : Table B) (qs : List A) : Table B where
  lrow    : ∀ {q e} → l q e → ¬ e ≡ end → LaneRem f l qs q e
  lend    : ∀ {c} → l c end → qs ≡ [] → LaneRem f l qs c end
  handoff : ∀ {c} → l c end → ¬ qs ≡ [] → LaneRem f l qs (c ++ [ ix 0 ]) skip
  queued  : ∀ {c a p r e} → l c end → a ∈ qs → at p ⊒ at (c ++ [ ix 1 ]) → f a p r e → LaneRem f l qs r e

data ConcRem {A B : Set} (o : Table A) (f : A → Pos → Table B) (l : Table B) (qs : List A) : Table B where
  outer : ∀ {q e} → OuterRem o f q e → ConcRem o f l qs q e
  inner : ∀ {q e} → LaneRem f l qs q e → ConcRem o f l qs q e

-- No outer row where the running lane ends.
Apart : ∀ {A B} → Table A → Table B → Set
Apart o l = ∀ {q e} → o q e → ¬ l q end

-- At or past a position, and not it: at or past just after it.
past-end : ∀ {q c} → at q ⊒ at c → ¬ q ≡ c → at q ⊒ shift (at c)
past-end qc ne with ⊒-split qc
... | inj₁ refl = ⊥-elim (ne refl)
... | inj₂ x    = <ᴷ-step x

-- Every outer row at or past the outer's key.
outer-from : ∀ {A B} {o : Table A} {f : A → Pos → Table B} → Inside f → ∀ {h} → From h o → From h (OuterRem o f)
outer-from ins oh (oval {q} r)        = ⊒-trans (under q [ ix 0 ]) (oh r)
outer-from ins oh (olane {q} r pq fr) = ⊒-trans (ins fr) (⊒-trans pq (⊒-trans (under q [ ix 0 ]) (oh r)))
outer-from ins oh (opass r _)         = oh r

-- Every lane row at or past the lane's key.
lane-from-c : ∀ {A B} {f : A → Pos → Table B} {l : Table B} {qs : List A} → Inside f → ∀ {k} → From k l → From k (LaneRem f l qs)
lane-from-c ins lk (lrow r _)               = lk r
lane-from-c ins lk (lend r _)               = lk r
lane-from-c ins lk (handoff {c} r _)        = ⊒-trans (under c [ ix 0 ]) (lk r)
lane-from-c ins lk (queued {c} r _ pc fr)   = ⊒-trans (ins fr) (⊒-trans pc (⊒-trans (under c [ ix 1 ]) (lk r)))

-- The outer wins: every outer row at or past where its event lands.
outer-wins-c : ∀ {A B} {o : Table A} {f : A → Pos → Table B} → Single o → Inside f → ∀ n qs h (oo : Out A) →
  From h o → Shows o h oo → From (proj₁ (outerT {B = B} n qs h oo)) (OuterRem o f)
outer-wins-c sg ins n qs h still      oh sh r = outer-from ins oh r
outer-wins-c sg ins n qs h (shows cp) oh sh r = outer-from ins oh r
outer-wins-c sg ins n qs h (shows (nx a)) oh sh (oval r)        = shifted (oh r)
outer-wins-c sg ins n qs h (shows (nx a)) oh sh (olane r pq fr) = ⊒-trans (ins fr) (⊒-trans pq (shifted (oh r)))
outer-wins-c sg ins n qs (at p) (shows (nx a)) oh sh (opass r no) with ⊒-split (oh r)
... | inj₁ refl = ⊥-elim (no (sg r sh))
... | inj₂ pq   = <ᴷ-step pq
outer-wins-c sg ins n qs (after p) (shows (nx a)) oh () (opass r no)

-- The lane wins: every lane row at or past where its event lands.  A
-- lane end with a value waiting lands just past the end, so every other
-- row must be strictly past it: the lane's own by `Single`, the handoff
-- and the queued lanes by position.
lane-wins-c : ∀ {A B} {f : A → Pos → Table B} {l : Table B} → Single l → Inside f → ∀ d n (qs : List A) k (ol : Out B) →
  From k l → Shows l k ol → From (proj₁ (laneT {A = A} d n qs k ol)) (LaneRem f l qs)
lane-wins-c sl ins d n []       k still          lk sh r = lane-from-c ins lk r
lane-wins-c sl ins d n (_ ∷ _)  k still          lk sh r = lane-from-c ins lk r
lane-wins-c sl ins d n []       k (shows (nx b)) lk sh r = lane-from-c ins lk r
lane-wins-c sl ins d n (_ ∷ _)  k (shows (nx b)) lk sh r = lane-from-c ins lk r
lane-wins-c sl ins d n []       k (shows cp)     lk sh r = lane-from-c ins lk r
lane-wins-c sl ins d n (_ ∷ _) (after p) (shows cp) lk () r
lane-wins-c sl ins d n (_ ∷ _) (at c) (shows cp) lk sh (lrow r ne) = past-end (lk r) λ { refl → ne (sl r sh) }
lane-wins-c sl ins d n (_ ∷ _) (at c) (shows cp) lk sh (lend r ())
lane-wins-c sl ins d n (_ ∷ _) (at c) (shows cp) lk sh (handoff r _) = shifted (lk r)
lane-wins-c sl ins d n (_ ∷ _) (at c) (shows cp) lk sh (queued {c′} r _ pc fr) =
  ⊒-trans (ins fr) (⊒-trans pc (⊒-trans (ix-past c′) (shifted (lk r))))

-- The lane wins, the outer at or past it: every outer row at or past
-- where the lane's event lands.  Just past a lane end needs the outer
-- never to sit at that end (`Apart`).
outer-under : ∀ {A B} {o : Table A} {f : A → Pos → Table B} {l : Table B} → Inside f → Apart o l → ∀ d n (qs : List A) h k (ol : Out B) →
  From h o → Shows l k ol → h ⊒ k → From (proj₁ (laneT {A = A} d n qs k ol)) (OuterRem o f)
outer-under ins ap d n []      h k still          oh sh hk r = ⊒-trans (outer-from ins oh r) hk
outer-under ins ap d n (_ ∷ _) h k still          oh sh hk r = ⊒-trans (outer-from ins oh r) hk
outer-under ins ap d n []      h k (shows (nx b)) oh sh hk r = ⊒-trans (outer-from ins oh r) hk
outer-under ins ap d n (_ ∷ _) h k (shows (nx b)) oh sh hk r = ⊒-trans (outer-from ins oh r) hk
outer-under ins ap d n []      h k (shows cp)     oh sh hk r = ⊒-trans (outer-from ins oh r) hk
outer-under ins ap d n (_ ∷ _) h (after p) (shows cp) oh () hk r
outer-under ins ap d n (_ ∷ _) h (at c) (shows cp) oh sh hk (oval {q} r) =
  ⊒-trans (under q [ ix 0 ]) (past-end (⊒-trans (oh r) hk) λ { refl → ap r sh })
outer-under ins ap d n (_ ∷ _) h (at c) (shows cp) oh sh hk (olane {q} r pq fr) =
  ⊒-trans (ins fr) (⊒-trans pq (⊒-trans (under q [ ix 0 ]) (past-end (⊒-trans (oh r) hk) λ { refl → ap r sh })))
outer-under ins ap d n (_ ∷ _) h (at c) (shows cp) oh sh hk (opass r _) =
  past-end (⊒-trans (oh r) hk) λ { refl → ap r sh }

-- What the frame shows is a row of the frame.
outer-shows-c : ∀ {A B} {o : Table A} {f : A → Pos → Table B} {l : Table B} → ∀ n (qs : List A) h (oo : Out A) →
  Shows o h oo → Shows (ConcRem o f l qs) (proj₁ (outerT {B = B} n qs h oo)) (proj₂ (outerT {B = B} n qs h oo))
outer-shows-c n qs h          still          sh = tt
outer-shows-c n qs h          (shows (nx a)) sh = tt
outer-shows-c n qs (after p)  (shows cp)     ()
outer-shows-c n qs (at p)     (shows cp)     sh with n ≡ᵇ 0
outer-shows-c n []      (at p) (shows cp) sh | true  = outer (opass sh (λ ()))
outer-shows-c n (_ ∷ _) (at p) (shows cp) sh | true  = tt
outer-shows-c n qs      (at p) (shows cp) sh | false = tt

lane-shows-c : ∀ {A B} {o : Table A} {f : A → Pos → Table B} {l : Table B} → ∀ d n (qs : List A) k (ol : Out B) →
  Shows l k ol → Shows (ConcRem o f l qs) (proj₁ (laneT {A = A} d n qs k ol)) (proj₂ (laneT {A = A} d n qs k ol))
lane-shows-c d n []      k         still          sh = tt
lane-shows-c d n (_ ∷ _) k         still          sh = tt
lane-shows-c d n []      (at p)    (shows (nx b)) sh = inner (lrow sh (λ ()))
lane-shows-c d n (_ ∷ _) (at p)    (shows (nx b)) sh = inner (lrow sh (λ ()))
lane-shows-c d n []      (after p) (shows (nx b)) ()
lane-shows-c d n (_ ∷ _) (after p) (shows (nx b)) ()
lane-shows-c d n []      (at p)    (shows cp)     sh with d ∧ (pred n ≡ᵇ 0)
... | true  = inner (lend sh refl)
... | false = tt
lane-shows-c d n []      (after p) (shows cp)     ()
lane-shows-c d n (_ ∷ _) k         (shows cp)     sh = tt

-- THE CONCAT STEP: the race at a concat frame bounds the frame's
-- remaining rows, given its outer's candidate and its running lane's do.
race-bound-c : ∀ {R A B} {o : Table A} {f : A → Pos → Table B} {l : Table B} → Single o → Single l → Inside f → Apart o l →
  ∀ d n (qs : List A) (co : Maybe (Cand R A)) (cl : Maybe (Cand R B)) → Bound o co → Bound l cl →
  Bound (ConcRem o f l qs) (raceT d n qs co cl)
race-bound-c so sl ins ap d n qs nothing nothing bo bl (outer (oval r))        = bo r
race-bound-c so sl ins ap d n qs nothing nothing bo bl (outer (olane r _ _))   = bo r
race-bound-c so sl ins ap d n qs nothing nothing bo bl (outer (opass r _))     = bo r
race-bound-c so sl ins ap d n qs nothing nothing bo bl (inner (lrow r _))      = bl r
race-bound-c so sl ins ap d n qs nothing nothing bo bl (inner (lend r _))      = bl r
race-bound-c so sl ins ap d n qs nothing nothing bo bl (inner (handoff r _))   = bl r
race-bound-c so sl ins ap d n qs nothing nothing bo bl (inner (queued r _ _ _)) = bl r
race-bound-c {A = A} {o = o} {f} {l} so sl ins ap d n qs nothing (just (g , k , ol)) bo (lk , sh) = only , lane-shows-c {A = A} d n qs k ol sh
  where
    only : From (proj₁ (laneT {A = A} d n qs k ol)) (ConcRem o f l qs)
    only (outer (oval r))      = ⊥-elim (bo r)
    only (outer (olane r _ _)) = ⊥-elim (bo r)
    only (outer (opass r _))   = ⊥-elim (bo r)
    only (inner r)             = lane-wins-c sl ins d n qs k ol lk sh r
race-bound-c {B = B} {o = o} {f} {l} so sl ins ap d n qs (just (fo , h , oo)) nothing (oh , sh) bl = only , outer-shows-c n qs h oo sh
  where
    only : From (proj₁ (outerT {B = B} n qs h oo)) (ConcRem o f l qs)
    only (outer r)                = outer-wins-c so ins n qs h oo oh sh r
    only (inner (lrow r _))       = ⊥-elim (bl r)
    only (inner (lend r _))       = ⊥-elim (bl r)
    only (inner (handoff r _))    = ⊥-elim (bl r)
    only (inner (queued r _ _ _)) = ⊥-elim (bl r)
race-bound-c {A = A} {B} {o = o} {f} {l} so sl ins ap d n qs (just (fo , h , oo)) (just (g , k , ol)) (oh , sh) (lk , lsh) with h <ᴷ k in hk
... | true  = won , outer-shows-c n qs h oo sh
  where
    past : ∀ (u : Out A) → k ⊒ proj₁ (outerT {B = B} n qs h u)
    past still          = <ᴷ-asym hk
    past (shows cp)     = <ᴷ-asym hk
    past (shows (nx a)) = <ᴷ-step hk
    won : From (proj₁ (outerT {B = B} n qs h oo)) (ConcRem o f l qs)
    won (outer r) = outer-wins-c so ins n qs h oo oh sh r
    won (inner r) = ⊒-trans (lane-from-c ins lk r) (past oo)
... | false = won , lane-shows-c {A = A} d n qs k ol lsh
  where
    won : From (proj₁ (laneT {A = A} d n qs k ol)) (ConcRem o f l qs)
    won (outer r) = outer-under ins ap d n qs h k ol oh lsh (ge hk) r
    won (inner r) = lane-wins-c sl ins d n qs k ol lk lsh r

------------------------------------------------------------------------
-- The dequeue

-- A lane end with a value waiting begins that value's lane at the slot
-- after the end, unless the frame's own observer is closed.
dequeue-pos : ∀ {R Γ A B} (c : Ctx R Γ B) op (g : A → Obs Timeline Γ B) d n a q (o : St Γ A) ls p →
  closed c ≡ false → Conf.pos (dequeue c op g d n (a ∷ q) o ls p) ≡ p ++ [ ix 1 ]
dequeue-pos c op g d n a q o ls p cl rewrite cl = refl

-- So every row of the lane `dequeue` begins is a queued row of the
-- frame's table, at the queue's head.
dequeue-rows : ∀ {R Γ A B} (c : Ctx R Γ B) op (g : A → Obs Timeline Γ B) d n a q (o : St Γ A) ls p →
  ∀ {f : A → Pos → Table B} {l : Table B} {r e} → closed c ≡ false → l p end →
  f a (Conf.pos (dequeue c op g d n (a ∷ q) o ls p)) r e → LaneRem f l (a ∷ q) r e
dequeue-rows c op g d n a q o ls p {f} {r = r} {e} cl lp fr =
  queued lp (here refl) (ge (<ᴷ-irrefl (at (p ++ [ ix 1 ])))) (subst (λ x → f a x r e) (dequeue-pos c op g d n a q o ls p cl) fr)
