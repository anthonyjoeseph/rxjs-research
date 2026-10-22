{-# OPTIONS --guardedness #-}

-- THE LINK, ON THE STATE-TREE ENGINE.  The pure semantics the harness
-- runs (`operation.StateTree.Pure`) agrees with the denotation: the limit
-- of its prefixes, the n-th read for n steps up to tick n, is the meaning
-- observed at the root, with positions forgotten down to ticks.
--
-- The halves are `adequacy.Adequacy`'s, over the state tree's run.
-- BELOW, safety: every prefix's record is sorted (`sortedˢ`) and alike
-- the meaning's events as a set (`contentˢ`), so placed against them.
-- ABOVE, liveness: whatever the meaning shows, some prefix reaches
-- (`reachedˢ`).  The driver's reader keeps no positions, so the proof
-- reads the same run with the position of each entry (`readingᵐ`), and
-- forgets them (`forgets`).
module adequacy.StateTree where

open import Data.Bool using (true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; _<ᵇ_)
open import Data.Nat.Properties using (≤-<-trans; <ᵇ⇒<; <⇒<ᵇ; n≤1+n)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import operation.Placed using (Ahead; items; ahead; framed; shows; placed-⊑; frames-cut)
open import operation.PureObservable using (PureObs; module Pure)
open import operation.StateTree.Pure using (module Driver) renaming (run to prefixˢ)
open import adequacy.Adequacy using (module Link)
open import adequacy.Sorted using (module Sorting)
open import adequacy.Ghost using (module Ghosting)
open import denotation.MonotonicList.Events using (ML; Pos; Time; root)
open import denotation.MonotonicList using (observe; ticks)
open import denotation.Order using (_⊑_; _≃_; Shows; Chain; limit; limit-ub; limit-least; shows-≼; shows-cmp; cmp-long)
open import denotation.Observe using (events)
open import denotation.Denote using (⟦_⟧)

-- The pure semantics' run: the limit of its prefixes, the n-th read for n
-- steps up to tick n.
runˢ : ∀ {A} → PureObs [] A → ML A
runˢ o = limit λ n → prefixˢ n n o

module Linkˢ (R : Set) where
  open Driver R using (Trace; Trace∞; tau; out; end; idle; trace; begin; reading; Read; read; log; ending)
  open Pure R using (End; finished; cutOff; frames) renaming (dry to dryᴱ)
  open Sorting R using (Ascending)
  open Ghosting R using (Alike)
  open Link R using (placing; ticks-up)

  ----------------------------------------------------------------------
  -- The run, read with its marks

  -- What the driver's reader keeps, and the position each entry was
  -- made at, its completion's last.
  record Readᵐ : Set where
    constructor readᵐ
    field
      marks : List Pos
      logᵐ  : List (Time × R)
      endᵐ  : End
  open Readᵐ

  noted : Pos → Time × R → Readᵐ → Readᵐ
  noted p x r = readᵐ (p ∷ marks r) (x ∷ logᵐ r) (endᵐ r)

  readingᵐ : Time → ℕ → Time → Trace → Readᵐ
  readingᵐ h zero    c _             = readᵐ [] [] (cutOff c)
  readingᵐ h (suc n) c (tau t k)     with h <ᵇ t
  ... | true  = readᵐ [] [] (cutOff c)
  ... | false = readingᵐ h n t (Trace∞.force k)
  readingᵐ h (suc n) c (out t p a k) with h <ᵇ t
  ... | true  = readᵐ [] [] (cutOff c)
  ... | false = noted p (t , a) (readingᵐ h n t (Trace∞.force k))
  readingᵐ h (suc n) c (end p)       = readᵐ [ p ] [] finished
  readingᵐ h (suc n) c idle          = readᵐ [] [] dryᴱ

  forget : Readᵐ → Read
  forget r = read (logᵐ r) (endᵐ r)

  -- Read with marks, the run is what the driver's reader reads.
  forgets : ∀ h n c l → forget (readingᵐ h n c l) ≡ reading h n c l
  forgets h zero    c l             = refl
  forgets h (suc n) c (tau t k)     with h <ᵇ t
  ... | true  = refl
  ... | false = forgets h n t (Trace∞.force k)
  forgets h (suc n) c (out t p a k) with h <ᵇ t
  ... | true  = refl
  ... | false = cong (λ r → read ((t , a) ∷ log r) (ending r)) (forgets h n t (Trace∞.force k))
  forgets h (suc n) c (end p)       = refl
  forgets h (suc n) c idle          = refl

  -- A program's first n steps up to tick h, with marks.
  readᵐ-of : PureObs [] R → ℕ → Time → Readᵐ
  readᵐ-of o n h = readingᵐ h n 0 (trace (begin o))

  ----------------------------------------------------------------------
  -- The two halves

  postulate
    -- SORTED: a prefix's marks never fall.
    sortedˢ : (o : PureObs [] R) (n h : ℕ) → Ascending root (marks (readᵐ-of o n h))

    -- ALIKE: a prefix's record is the meaning's events, as a set.
    contentˢ : (o : PureObs [] R) (n h : ℕ) → Alike (endᵐ (readᵐ-of o n h)) (marks (readᵐ-of o n h)) (logᵐ (readᵐ-of o n h)) (events o)

    -- LIVENESS: whatever item the meaning's events reach, the run reaches
    -- within finitely many steps up to as many ticks.
    reachedˢ : (o : PureObs [] R) → ∀ {k} → Ahead (events o) k → Σ ℕ λ n → k ≤ length (items (logᵐ (readᵐ-of o n n)) (endᵐ (readᵐ-of o n n)))

  -- Each prefix is below the meaning.
  complete : (o : PureObs [] R) (n : ℕ) → prefixˢ n n o ⊑ ticks (events o)
  complete o n = subst (λ r → frames (log r) (ending r) ⊑ ticks (events o)) (forgets n n 0 (trace (begin o)))
                   (placed-⊑ (ticks-up o) (placing o (sortedˢ o n n) (contentˢ o n n)))

  -- Whatever the meaning shows, some prefix shows.
  reaches : (o : PureObs [] R) → ∀ {is} → Shows (ticks (events o)) is → Σ ℕ λ n → Shows (prefixˢ n n o) is
  reaches o {is} s with reachedˢ o (ahead s)
  ... | n , long = n , subst (λ r → Shows (frames (log r) (ending r)) is) (forgets n n 0 (trace (begin o)))
                         (shows-≼ (cmp-long (shows-cmp s (shows (ticks-up o) (placing o (sortedˢ o n n) (contentˢ o n n)))) long)
                                  (framed (logᵐ r) (endᵐ r)))
    where r = readᵐ-of o n n

  ----------------------------------------------------------------------
  -- The prefixes, a chain

  -- A longer prefix to a later tick is the same, or extends the record
  -- of a cut one.
  private
    data Grows : Read → Read → Set where
      stays : ∀ {r} → Grows r r
      cuts  : ∀ {xs c e′} ys → Grows (read xs (cutOff c)) (read (xs ++ ys) e′)

    noted-grows : ∀ {x r r′} → Grows r r′ → Grows (read (x ∷ log r) (ending r)) (read (x ∷ log r′) (ending r′))
    noted-grows stays     = stays
    noted-grows (cuts ys) = cuts ys

    -- A tick past a horizon is past any earlier one.
    past : ∀ {h h′} t → h ≤ h′ → (h <ᵇ t) ≡ false → (h′ <ᵇ t) ≡ true → ⊥
    past {h} {h′} t le f tr = subst T f (<⇒<ᵇ (≤-<-trans le (<ᵇ⇒< h′ t (subst T (sym tr) tt))))

    grows : ∀ {h h′ n n′} c l → h ≤ h′ → n ≤ n′ → Grows (reading h n c l) (reading h′ n′ c l)
    grows {n = zero} c l hh nn = cuts _
    grows {h} {h′} {suc n} {suc n′} c (tau t k) hh (s≤s nn) with h <ᵇ t in e | h′ <ᵇ t in e′
    ... | true  | _     = cuts _
    ... | false | true  = ⊥-elim (past t hh e e′)
    ... | false | false = grows t (Trace∞.force k) hh nn
    grows {h} {h′} {suc n} {suc n′} c (out t p a k) hh (s≤s nn) with h <ᵇ t in e | h′ <ᵇ t in e′
    ... | true  | _     = cuts _
    ... | false | true  = ⊥-elim (past t hh e e′)
    ... | false | false = noted-grows (grows t (Trace∞.force k) hh nn)
    grows {n = suc n} {suc n′} c (end p) hh (s≤s nn) = stays
    grows {n = suc n} {suc n′} c idle    hh (s≤s nn) = stays

    grows-⊑ : ∀ {r r′} → Grows r r′ → frames (log r) (ending r) ⊑ frames (log r′) (ending r′)
    grows-⊑ stays s                               = s
    grows-⊑ (cuts {xs = xs} {c = c} {e′ = e′} ys) = frames-cut xs ys c e′

  prefix-chain : (o : PureObs [] R) → Chain (λ n → prefixˢ n n o)
  prefix-chain o n = grows-⊑ (grows 0 (trace (begin o)) (n≤1+n n) (n≤1+n n))

adequacyˢ : ∀ {A} (o : PureObs [] A) → runˢ o ≃ ticks (observe (⟦ o ⟧ []) root)
adequacyˢ {A} o = limit-least (prefix-chain o) (complete o)
                , λ s → limit-ub (prefix-chain o) (proj₁ (reaches o s)) (proj₂ (reaches o s))
  where open Linkˢ A
