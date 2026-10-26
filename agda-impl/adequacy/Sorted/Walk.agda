{-# OPTIONS --guardedness #-}

-- THE WALK: a well configuration rises.  A configuration is well past
-- `lo` when it runs a ghost (`Mirror`) showing nothing before `lo`: the
-- order is the meaning's, read through `Strong`, and the machine keeps
-- none of its own.  Every step keeps it (`preserve`, by the strong step)
-- and the launch holds it (`begin-well`, the meaning headed at the root);
-- a run from a well configuration is a rising one.
module adequacy.Sorted.Walk where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.List.Relation.Unary.All using ([])
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import denotation.MonotonicList.Events using (Events; Pos; root; _<ᵖ_; <ᵖ-split)
import denotation.Unfold as U
open import operation.PureObservable using (PureObs; module Driver; module Machine)
open import adequacy.Sorted using (_≤ᵖ_; ≤ᵖ-trans; module Sorting)
open import adequacy.Placed.Order using (Atop; Ordered; ordered)
open import adequacy.Placed.Rising using (rise-sub)
open import adequacy.Engine.Meaning using (Has; atOut; atEnd; pastOut; pastSkip)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Strong using (module Strongly)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Content using (module Honesty)

-- A head nothing precedes `k` lies at or past `k`.
atop-le : ∀ k h → h <ᵖ k ≡ false → k ≤ᵖ h
atop-le k h a with <ᵖ-split k h a
... | inj₁ lt = inj₂ lt
... | inj₂ eq = inj₁ eq

-- Ordered events headed at or past `k`: every event of them is.
atop-has : ∀ {A k} {e : Events A} → Ordered e → Atop k e → ∀ {q b} → Has e q b → k ≤ᵖ q
atop-has {k = k} o a (atOut {k = h})      = atop-le k h a
atop-has {k = k} o a (atEnd {k = h})      = atop-le k h a
atop-has {k = k} o a (pastOut {k = h} x)  = ≤ᵖ-trans (atop-le k h a) (atop-has (proj₂ (ordered o)) (proj₁ (ordered o)) x)
atop-has {k = k} o a (pastSkip {k = h} x) = ≤ᵖ-trans (atop-le k h a) (atop-has (proj₂ (ordered o)) (proj₁ (ordered o)) x)

-- Nothing at or before `p`: everything past it.
past-least : ∀ {A p} {e : Events A} → (∀ {q b} → Has e q b → q ≤ᵖ p → ⊥) → ∀ {q b} → Has e q b → p ≤ᵖ q
past-least {p = p} no {q} h with q <ᵖ p in e
... | true  = ⊥-elim (no h (inj₂ e))
... | false = atop-le p q e

module SortingWalk (R : Set) where
  open Driver R using (Step; silent; value; complete; drained; step)
  open Machine using (Conf; load)
  open Sorting R using (Rising; RisingStep; silentʳ; valueʳ; completeʳ; drainedʳ)
  open Unsubbing R using (now; then)
  open Strongly R using (strong-begin)
  open Ghosting R using (residual; Mirror; gain-past; past-same)
  open Honesty R using (Hop; valueᴴ; completeᴴ; drainedᴴ; silentᴴ; strong-hop; strong-steps; strong-sane)

  -- A configuration well past `lo`, the last position delivered.
  WellMach : Pos → Conf R → Set₁
  WellMach lo m = Σ (U.Node [] R) λ g → Mirror g m × (∀ {k b} → Has (residual g) k b → lo ≤ᵖ k)

  -- One step, its next configuration well and never earlier.
  data WellStep (lo : Pos) : Step → Set₁ where
    silentʷ   : ∀ {t m lo′} → lo ≤ᵖ lo′ → WellMach lo′ m → WellStep lo (silent t m)
    valueʷ    : ∀ {t p a m} → lo ≤ᵖ p → WellMach p m → WellStep lo (value t p a m)
    completeʷ : ∀ {p} → lo ≤ᵖ p → WellStep lo (complete p)
    drainedʷ  : WellStep lo drained

  -- The machine's fundamental lemma: a well configuration's step keeps
  -- it well, and a value it shows is no earlier than the last.  On the
  -- way to a re-entry configuration the ghost stays; at one, the strong
  -- step shows a value of the ghost's and leaves all of its rest past it.
  preserve : ∀ {lo m} → WellMach lo m → WellStep lo (step m)
  preserve {lo} (g , (m₀ , then eq path , st) , bd) = subst (WellStep lo) (sym eq) (silentʷ (inj₁ refl) (g , (m₀ , path , st) , bd))
  preserve {lo} {m} (g , (_ , now , st) , bd) = hop (strong-hop st)
    where
    hop : Hop st → WellStep lo (step m)
    hop (valueᴴ eq ld ck least mi) = subst (WellStep lo) (sym eq) (valueʷ (bd (proj₁ (strong-steps st ld))) (_ , mi , past-least least))
    hop (completeᴴ eq ld)          = subst (WellStep lo) (sym eq) (completeʷ (bd (proj₁ (strong-steps st ld))))
    hop (drainedᴴ eq no)           = subst (WellStep lo) (sym eq) drainedʷ
    hop (silentᴴ eq (g″ , m₀ , path , st₀ , gn)) =
      subst (WellStep lo) (sym eq) (silentʷ (inj₁ refl) (g″ , (m₀ , path , st₀) , λ h → bd (proj₂ (past-same (gain-past gn)) h)))

  -- The run begins well, the program loaded at the root.
  begin-well : (o : PureObs [] R) → WellMach root (load o)
  begin-well o =
    U.subscribe o root , (load o , now , strong-begin o) , atop-has (proj₁ (proj₂ (strong-sane (strong-begin o)))) (rise-sub o root [] tt)

  mutual
    rising : ∀ {lo m} → WellMach lo m → Rising lo m
    rising w .Rising.rises = risingˢ (preserve w)

    risingˢ : ∀ {lo s} → WellStep lo s → RisingStep lo s
    risingˢ (silentʷ le w)  = silentʳ le (rising w)
    risingˢ (valueʷ le w)   = valueʳ le (rising w)
    risingˢ (completeʷ le)  = completeʳ le
    risingˢ drainedʷ        = drainedʳ

  -- SORTEDNESS: the program's run rises from the root.
  sorted : (o : PureObs [] R) → Rising root (load o)
  sorted o = rising (begin-well o)
