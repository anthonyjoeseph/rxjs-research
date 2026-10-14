{-# OPTIONS --guardedness #-}

-- THE RECORD, PLACED.  What the pure runtime leaves behind — each value
-- the root was sent, at the tick the clock was on, the ghost position it
-- was sent at, and how the run ended — read against the events a
-- subscriber at the root is shown.  When each value sits at its own
-- event, in order, with the tick its position names, and the run ends as
-- the events do, the record shows nothing the events do not: positions
-- forgotten, the order on runs reads it off tick by tick.
--
-- Only the events' ticks must not fall: `ticks` closes a frame at the
-- first event past its tick, and one that fell back would land in the
-- wrong frame.
module operation.Placed where

open import Data.Bool using (Bool; true; false; T)
open import Data.List using (List; []; _∷_; _++_; [_]) renaming (map to mapL)
open import Data.Nat using (ℕ; suc; _≤_; s≤s; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-antisym; ≡ᵇ⇒≡; <ᵇ⇒<)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import denotation.MonotonicList using (ML; Burst; Burst∞; ML∞; at; emit; stall; close; done; quiet; Time; Pos; tick;
                                            Events; Events∞; out; skip; end; hush; ticks; inFrame; within; sameTick)
open import denotation.Order using (Item; val; fin; silent; Shows; ShowsIn; nil; done⁺; quiet⁺; at⁺; emit⁺; stall⁺; close⁺; _⊑_; shows-≼)
  renaming (_≼_ to _≼ˡ_; []≼ to []≼ˡ; ∷≼ to ∷≼ˡ)
open import operation.PureObservable using (module Pure)

open Events∞

------------------------------------------------------------------------
-- Ticks that never fall

private
  T-of : ∀ {b} → b ≡ true → T b
  T-of refl = _

  ≤-pred′ : ∀ {m n} → suc m ≤ suc n → m ≤ n
  ≤-pred′ (s≤s p) = p

-- The tick of the next event, if it has one.
headTick : ∀ {A} → Time → Events A → Time
headTick t (out k _ _) = tick k
headTick t (skip k _)  = tick k
headTick t (end _)     = t
headTick t hush        = t

-- Past the next event.
onward : ∀ {A} → Events A → Events A
onward (out _ _ r) = force r
onward (skip _ r)  = force r
onward e           = e

-- No event of `e` is before tick t, nor before the one ahead of it.
record Up {A} (t : Time) (e : Events A) : Set where
  coinductive
  field
    up   : t ≤ headTick t e
    more : Up (headTick t e) (onward e)
open Up

------------------------------------------------------------------------
-- The record, against the events

module _ {A : Set} where
  open Pure A using (End; finished; dry; cutOff; frames; ending; sameFrame; stalls)
                renaming (inFrame to inFrameᴿ; within to withinᴿ)

  -- What the record shows: each value at its tick, then how it ended.
  items : List (Time × A) → End → List (Item A)
  items ((t , a) ∷ xs) e          = val t a ∷ items xs e
  items []             finished   = fin ∷ []
  items []             dry        = silent ∷ []
  items []             (cutOff _) = []

  -- The record's marks and values, each at its event in order and on the
  -- tick its position names; the completion at the events' end; a run
  -- that fell silent over events that show nothing more, ever.
  data Placed : End → List Pos → List (Time × A) → Events A → Set where
    cut    : ∀ {c e} → Placed (cutOff c) [] [] e
    ends   : ∀ {q} → Placed finished (q ∷ []) [] (end q)
    quiets : Placed dry [] [] hush
    sends  : ∀ {en qs xs k a r} → Placed en qs xs (force r) → Placed en (k ∷ qs) ((tick k , a) ∷ xs) (out k a r)
    skips  : ∀ {en qs xs k r} → Placed en qs xs (force r) → Placed en qs xs (skip k r)

  -- A record shows a prefix of its items.
  private
    blank : ∀ {c is} → ShowsIn c (stall (stalls {A})) is → is ≡ []
    blank nil        = refl
    blank (stall⁺ p) = blank p

    blank≼ : ∀ {c is js} → ShowsIn c (stall (stalls {A})) is → is ≼ˡ js
    blank≼ p with blank p
    ... | refl = []≼ˡ

    mutual
      shown : ∀ xs en {is} → Shows (frames xs en) is → is ≼ˡ items xs en
      shown []             finished   nil      = []≼ˡ
      shown []             finished   done⁺    = ∷≼ˡ []≼ˡ
      shown []             dry        nil      = []≼ˡ
      shown []             dry        quiet⁺   = ∷≼ˡ []≼ˡ
      shown []             (cutOff c) (at⁺ p)  = blank≼ p
      shown []             (cutOff c) nil      = []≼ˡ
      shown ((t , a) ∷ xs) en         nil      = []≼ˡ
      shown ((t , a) ∷ xs) en         (at⁺ nil)       = []≼ˡ
      shown ((t , a) ∷ xs) en         (at⁺ (emit⁺ p)) = ∷≼ˡ (shownIn t xs en p)

      shownIn : ∀ t xs en {is} → ShowsIn t (inFrameᴿ t xs en) is → is ≼ˡ items xs en
      shownIn t []               (cutOff c) p with c ≡ᵇ t
      ... | true  = blank≼ p
      ... | false = closing p
        where
          closing : ∀ {is} → ShowsIn t (close (Pure.later A (ending (cutOff c)))) is → is ≼ˡ []
          closing nil        = []≼ˡ
          closing (close⁺ s) = shown [] (cutOff c) s
      shownIn t []               finished nil        = []≼ˡ
      shownIn t []               finished (close⁺ s) = shown [] finished s
      shownIn t []               dry      nil        = []≼ˡ
      shownIn t []               dry      (close⁺ s) = shown [] dry s
      shownIn t ((t′ , a) ∷ xs) en p with t′ ≡ᵇ t in eq
      ... | true with ≡ᵇ⇒≡ t′ t (T-of eq)
      ...   | refl = sameIn p
        where
          sameIn : ∀ {is} → ShowsIn t (emit a (withinᴿ t xs en)) is → is ≼ˡ items ((t′ , a) ∷ xs) en
          sameIn nil       = []≼ˡ
          sameIn (emit⁺ q) = ∷≼ˡ (shownIn t xs en q)
      shownIn t ((t′ , a) ∷ xs) en p | false = newIn p
        where
          newIn : ∀ {is} → ShowsIn t (close (Pure.later A (frames ((t′ , a) ∷ xs) en))) is → is ≼ˡ items ((t′ , a) ∷ xs) en
          newIn nil        = []≼ˡ
          newIn (close⁺ s) = shown ((t′ , a) ∷ xs) en s

  -- Placed events show every item of the record.
  mutual
    shows : ∀ {f en qs xs e} → Up f e → Placed en qs xs e → Shows (ticks e) (items xs en)
    shows u cut       = nil
    shows u ends      = done⁺
    shows u quiets    = quiet⁺
    shows u (sends p) = at⁺ (emit⁺ (showsIn (more u) p))
    shows u (skips p) = at⁺ (stall⁺ (showsIn (more u) p))

    showsIn : ∀ {t en qs xs e} → Up t e → Placed en qs xs e → ShowsIn t (inFrame t e) (items xs en)
    showsIn u cut    = nil
    showsIn u ends   = close⁺ done⁺
    showsIn u quiets = close⁺ quiet⁺
    showsIn {t} u (sends {k = k} p) with tick k <ᵇ suc t in eq
    ... | false = close⁺ (at⁺ (emit⁺ (showsIn (more u) p)))
    ... | true with ≤-antisym (up u) (≤-pred′ (<ᵇ⇒< (tick k) (suc t) (T-of eq)))
    ...   | refl = emit⁺ (showsIn (more u) p)
    showsIn {t} u (skips {k = k} p) with tick k <ᵇ suc t in eq
    ... | false = close⁺ (at⁺ (stall⁺ (showsIn (more u) p)))
    ... | true with ≤-antisym (up u) (≤-pred′ (<ᵇ⇒< (tick k) (suc t) (T-of eq)))
    ...   | refl = stall⁺ (showsIn (more u) p)

  -- THE RECORD SHOWS NOTHING THE EVENTS DO NOT.
  placed-⊑ : ∀ {f en qs xs e} → Up f e → Placed en qs xs e → frames xs en ⊑ ticks e
  placed-⊑ u p s = shows-≼ (shown _ _ s) (shows u p)

------------------------------------------------------------------------
-- A whole run

module Ran (A : Set) where
  open import operation.AbstractObservable using (module Run)
  open import operation.PureObservable using (Pureᴾ; same)
  open Run (Pureᴾ A) using (Subscribe; module Engine)
  open Pure A using (Res; res; State; endOf; observe; Pureᴿ; runᴺ; loopᴺ; recorder; start)

  -- What `runPure m` reads its record off.
  ran : ℕ → Subscribe A [] → Res [] _
  ran m s = Engine.drive (Pureᴿ m) (runᴺ m m) (loopᴺ m m) s recorder same start

  -- A run's record, placed against the events.
  Recorded : Res [] _ → Events A → Set
  Recorded (res σ st v) = Placed (endOf (State.ended st) v (State.clock st)) (State.marks st) (State.log st)

  recorded-⊑ : ∀ {f} r {e} → Up f e → Recorded r e → observe r ⊑ ticks e
  recorded-⊑ (res σ st v) u p = placed-⊑ u p
