{-# OPTIONS --guardedness #-}

-- THE LINK, PORTED to the state-tree engine.  The pure semantics the
-- harness runs (`operation.StateTree.Pure`) agrees with the denotation:
-- the limit of its prefixes, the n-th read for n steps up to tick n, is
-- the meaning observed at the root, with positions forgotten down to
-- ticks.
--
-- Two halves, proven apart.  BELOW, safety: every prefix's
-- record is sorted and alike the meaning's events as a set, so placed
-- against them.  ABOVE, liveness: whatever the meaning shows, some prefix
-- reaches.
module port.Adequacy where

open import Data.Bool using (true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _++_)
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; _<ᵇ_)
open import Data.Nat.Properties using (≤-<-trans; <ᵇ⇒<; <⇒<ᵇ; n≤1+n)
open import Data.Product using (_,_; Σ; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)

open import operation.Placed using (Up; Placed; ahead; framed; shows; placed-⊑; frames-cut)
open import operation.PureObservable using (PureObs; module Pure)
open import operation.StateTree.Pure using (module Driver) renaming (run to prefix)
open import port.Sorted using (module Sorting)
open import port.Sorted.Walk using (module SortingWalk)
open import port.Content using (module Honesty)
open import port.Ghost using (module Ghosting)
open import port.Progress using (module Progressing)
open import denotation.MonotonicList.Events using (ML; Time; root)
open import denotation.MonotonicList using (observe; ticks)
open import denotation.Order using (_⊑_; _≃_; Shows; Chain; limit; limit-ub; limit-least; shows-≼; shows-cmp; cmp-long)
open import denotation.Observe using (events)
open import denotation.Denote using (⟦_⟧)

-- The pure run: the limit of its prefixes, the n-th read for n steps up
-- to tick n.
run : ∀ {A} → PureObs [] A → ML A
run o = limit λ n → prefix n n o

module Link (R : Set) where
  open Driver R using (Trace∞; tau; out; end; idle; trace; begin; reading; Read; read; marks; log; ending; noted)
  open Pure R using (finished; cutOff; frames)
  open Sorting R using (Ascending; ascending)
  open SortingWalk R using (sorted)
  open Ghosting R using (Alike)
  open Honesty R using (content)
  open Progressing R using (reached)

  -- The first n steps up to tick h, read.
  read-of : PureObs [] R → ℕ → Time → Read
  read-of o n h = reading h n 0 (trace (begin o))

  postulate
    -- SORTED AND ALIKE IS PLACED: a record ascending in its marks and
    -- alike a program's events as a set is those events, in order.  No
    -- machine: the fold's positions ascend too, so two ascending lists
    -- with the same members agree.  Stated at a program's events, not
    -- any events, since only the fold's are known to ascend.
    placing : (o : PureObs [] R) → ∀ {en qs xs} → Ascending root qs → Alike en qs xs (events o) → Placed en qs xs (events o)

  -- SAFETY: every prefix of the run is placed against the meaning's
  -- events.
  placedᴿ : (o : PureObs [] R) (n h : ℕ) → Placed (ending (read-of o n h)) (marks (read-of o n h)) (log (read-of o n h)) (events o)
  placedᴿ o n h = placing o (ascending (sorted o) n h 0) (content o n h)

  postulate
    -- The meaning's ticks never fall.
    --
    -- RECOVERY: `git show a2e0bb8b` restores `<ᵖ-trans`, `<ᵖ-irrefl` and
    --   `<ᵖ-ix` in `denotation.MonotonicList`: positions strictly ordered,
    --   and an earlier one at no later a tick.
    ticks-up : (o : PureObs [] R) → Up 0 (events o)

  -- Whatever the meaning shows, some prefix shows.
  reaches : (o : PureObs [] R) → ∀ {is} → Shows (ticks (events o)) is → Σ ℕ λ n → Shows (prefix n n o) is
  reaches o s with reached o (ahead s)
  ... | n , long = n , shows-≼ (cmp-long (shows-cmp s (shows (ticks-up o) (placedᴿ o n n))) long) (framed (log r) (ending r))
    where r = read-of o n n

  -- Each prefix is below the meaning.
  complete : (o : PureObs [] R) (n : ℕ) → prefix n n o ⊑ ticks (events o)
  complete o n = placed-⊑ (ticks-up o) (placedᴿ o n n)

  ----------------------------------------------------------------------
  -- The prefixes, a chain

  -- A longer prefix to a later tick is the same, or extends the record
  -- of a cut one.
  private
    data Grows : Read → Read → Set where
      stays : ∀ {r} → Grows r r
      cuts  : ∀ {ms xs c ms′ e′} ys → Grows (read ms xs (cutOff c)) (read ms′ (xs ++ ys) e′)

    noted-grows : ∀ {p x r r′} → Grows r r′ → Grows (noted p x r) (noted p x r′)
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

  prefix-chain : (o : PureObs [] R) → Chain (λ n → prefix n n o)
  prefix-chain o n = grows-⊑ (grows 0 (trace (begin o)) (n≤1+n n) (n≤1+n n))

adequacy : ∀ {A} (o : PureObs [] A) → run o ≃ ticks (observe (⟦ o ⟧ []) root)
adequacy {A} o = limit-least (prefix-chain o) (complete o)
               , λ s → limit-ub (prefix-chain o) (proj₁ (reaches o s)) (proj₂ (reaches o s))
  where open Link A
