{-# OPTIONS --guardedness #-}

-- THE LINK.  The pure runtime and the denotation agree: the limit of the
-- machine's prefixes is the meaning, observed at the root, with positions
-- forgotten down to ticks.  The meaning is `denotation.Denote`'s fold,
-- read directly: no stepper stands between them.
--
-- Two halves, proven apart.  BELOW: every prefix's record, positions and
-- all, is placed against the meaning's events (`operation.Placed`), so
-- shows nothing they do not — SAFETY, a fact about every finite prefix.
-- Safety is two facts that never meet: the record is SORTED
-- (`adequacy.Sorted`, the machine alone) and ALIKE the events as a set
-- (content, one observer at a time); sorted and alike is placed.
-- ABOVE: whatever the meaning shows lies within some prefix — LIVENESS.
-- Neither half is stated against the other's steps.
module adequacy.Adequacy where

open import Data.List using ([]; _++_; [_]; length)
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Product using (_,_; Σ; proj₁; proj₂)

open import operation.Placed using (Up; Placed; Ahead; items; ahead; framed; shows; placed-⊑; frames-cut)
open import operation.Machine using (module Machine)
open import operation.PureObservable using (PureObs; module Pure)
open import denotation.MonotonicList.Events using (ML; root)
open import denotation.MonotonicList using (observe; ticks)
open import adequacy.Sorted using (module Sorting)
open import adequacy.Sorted.Walk using (module SortingWalk)
open import adequacy.Content using (module Honesty)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Progress using (module Progressing)
open import denotation.Order using (_⊑_; _≃_; Shows; Chain; limit; limit-ub; limit-least; shows-≼; shows-cmp; cmp-long)
open import denotation.Denote using (⟦_⟧)
open import denotation.Observe using (events)

-- The pure run: the limit of the machine's prefixes.
run : ∀ {A} → PureObs [] A → ML A
run {A} o = limit λ n → Machine.prefix A n o

module Link (R : Set) where
  open Machine R using (prefix; reading; trace; begin; launch; Read; read; Trace∞; tau; out; end; idle)
  open Pure R using (End; finished; dry; cutOff; frames; recorder)
  open Sorting R using (Ascending; ascending)
  open SortingWalk R using (sorted)
  open Ghosting R using (Alike)
  open Honesty R using (content)
  open Progressing R using (reached)
  open Read

  -- The first n steps, read.
  read-of : PureObs [] R → ℕ → Read
  read-of o n = reading n 0 (trace (begin o))

  postulate
    -- SORTED AND ALIKE IS PLACED: a record ascending in its marks and
    -- alike a program's events as a set is those events, in order.  No
    -- machine: the fold's positions ascend too, so two ascending lists
    -- with the same members agree.  Stated at a program's events, not
    -- any events, since only the fold's are known to ascend.
    placing : (o : PureObs [] R) → ∀ {en qs xs} → Ascending root qs → Alike en qs xs (events o) → Placed en qs xs (events o)

  -- SAFETY: every prefix of the run is placed against the meaning's
  -- events: each value the root was sent is the events' next `out`, at
  -- its position, and the run ends as they do.
  --
  -- DEAD ROUTE: a step-by-step simulation against a stepper that picks
  --   the configuration's earliest node (`denotation.Unfold`).  Every
  --   step owes that every other live node is past the one the machine
  --   moved, re-established across a reconstruction of the tree at the
  --   machine's control, so each new kernel or death reopened it.
  --
  -- RECOVERY: `git show fbdfc8ed` restores that simulation:
  --   `adequacy.Carrier`, `adequacy.Kept`, `adequacy.Plug`,
  --   `adequacy.Aim`, `adequacy.Wait` and `adequacy.Simulation`'s
  --   relation, with the stepper's link to the fold (`stepped`).  The
  --   same commit restores the order on positions in
  --   `denotation.MonotonicList` (`<ᵖ-trans`, `<ᵖ-asym`, `<ᵖ-tick`,
  --   `<ᵖ-++ʳ`), and `denotation.Unfold`'s stepper proven the fold's.
  placedᴿ : (o : PureObs [] R) (n : ℕ) → Placed (ending (read-of o n)) (marks (read-of o n)) (log (read-of o n)) (events o)
  placedᴿ o n = placing o (ascending (sorted o) n 0) (content o n)

  -- LIVENESS: whatever item the meaning's events reach, finitely many
  -- steps of the machine reach.
  reachedᴿ : (o : PureObs [] R) → ∀ {k} → Ahead (events o) k → Σ ℕ λ n → k ≤ length (items (log (read-of o n)) (ending (read-of o n)))
  reachedᴿ = reached

  postulate
    -- The meaning's ticks never fall.
    --
    -- RECOVERY: `git show a2e0bb8b` restores `<ᵖ-trans`, `<ᵖ-irrefl` and
    --   `<ᵖ-ix` in `denotation.MonotonicList`: positions strictly ordered,
    --   and an earlier one at no later a tick.
    ticks-up : (o : PureObs [] R) → Up 0 (events o)

  -- THE UPPER HALF: whatever the meaning shows, some prefix shows.  It
  -- shows as many items, and they are the meaning's.
  reaches : (o : PureObs [] R) → ∀ {is} → Shows (ticks (events o)) is → Σ ℕ λ n → Shows (prefix n o) is
  reaches o s with reachedᴿ o (ahead s)
  ... | n , long = n , shows-≼ (cmp-long (shows-cmp s (shows (ticks-up o) (placedᴿ o n))) long) (framed (log r) (ending r))
    where r = read-of o n

  -- Each prefix is below the meaning.
  complete : (o : PureObs [] R) (n : ℕ) → prefix n o ⊑ ticks (events o)
  complete o n = placed-⊑ (ticks-up o) (placedᴿ o n)

  ------------------------------------------------------------------------
  -- The prefixes, a chain

  -- A longer prefix is the same, or extends the record of a cut one.
  private
    data Grows : Read → Read → Set where
      stays : ∀ {r} → Grows r r
      cuts  : ∀ {ms xs c ms′ e′} ys → Grows (read ms xs (cutOff c)) (read ms′ (xs ++ ys) e′)

    noted-grows : ∀ {p x r r′} → Grows r r′ → Grows (Machine.noted R p x r) (Machine.noted R p x r′)
    noted-grows stays     = stays
    noted-grows (cuts ys) = cuts ys

    grows : ∀ n c l → Grows (reading n c l) (reading (suc n) c l)
    grows zero    c (tau t k)     = cuts []
    grows zero    c (out t p a k) = cuts [ (t , a) ]
    grows zero    c (end p)       = cuts []
    grows zero    c idle          = cuts []
    grows (suc n) c (tau t k)     = grows n t (Trace∞.force k)
    grows (suc n) c (out t p a k) = noted-grows (grows n t (Trace∞.force k))
    grows (suc n) c (end p)       = stays
    grows (suc n) c idle          = stays

    grows-⊑ : ∀ {r r′} → Grows r r′ → frames (log r) (ending r) ⊑ frames (log r′) (ending r′)
    grows-⊑ stays s                               = s
    grows-⊑ (cuts {xs = xs} {c = c} {e′ = e′} ys) = frames-cut xs ys c e′

  prefix-chain : (o : PureObs [] R) → Chain (λ n → prefix n o)
  prefix-chain o n = grows-⊑ (grows n 0 (trace (begin o)))

adequacy : ∀ {A} (o : PureObs [] A) → run o ≃ ticks (observe (⟦ o ⟧ []) root)
adequacy {A} o = limit-least (prefix-chain o) (complete o)
               , λ s → limit-ub (prefix-chain o) (proj₁ (reaches o s)) (proj₂ (reaches o s))
  where open Link A
