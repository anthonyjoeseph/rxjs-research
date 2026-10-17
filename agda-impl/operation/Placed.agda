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

open import Data.Bool using (true; false; T)
open import Data.List using (List; []; _∷_; _++_; [_]; length) renaming (map to mapL)
open import Data.Nat using (ℕ; suc; _≤_; s≤s; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-antisym; ≡ᵇ⇒≡; <ᵇ⇒<)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.MonotonicList using (emit; stall; close; Time; Pos; tick; Events; Events∞; out; skip; end; hush; ticks; inFrame;
  within)
open import denotation.Order using (Item; val; fin; silent; Shows; ShowsIn; nil; done⁺; quiet⁺; at⁺; emit⁺; stall⁺; close⁺; _⊑_; shows-≼)
  renaming (_≼_ to _≼ˡ_; []≼ to []≼ˡ; ∷≼ to ∷≼ˡ)
open import operation.PureObservable using (module Pure)

open Events∞ using (force)

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
-- How far a reader gets

-- `e` shows k items, each within finitely many events.
data Ahead {A : Set} : Events A → ℕ → Set where
  none  : ∀ {e} → Ahead e 0
  outᵃ  : ∀ {k a r n} → Ahead (force r) n → Ahead (out k a r) (suc n)
  skipᵃ : ∀ {k r n} → Ahead (force r) n → Ahead (skip k r) n
  endᵃ  : ∀ {k} → Ahead (end k) 1
  hushᵃ : Ahead hush 1

-- A reader of the ticks saw no more items than the events reach.
mutual
  ahead : ∀ {A} {e : Events A} {is} → Shows (ticks e) is → Ahead e (length is)
  ahead {e = out k a r} nil             = none
  ahead {e = out k a r} (at⁺ nil)       = none
  ahead {e = out k a r} (at⁺ (emit⁺ s)) = outᵃ (aheadIn _ (force r) _ s)
  ahead {e = skip k r}  nil             = none
  ahead {e = skip k r}  (at⁺ nil)       = none
  ahead {e = skip k r}  (at⁺ (stall⁺ s)) = skipᵃ (aheadIn _ (force r) _ s)
  ahead {e = end k}     nil             = none
  ahead {e = end k}     done⁺           = endᵃ
  ahead {e = hush}      nil             = none
  ahead {e = hush}      quiet⁺          = hushᵃ

  aheadIn : ∀ {A} t (e : Events A) b {is} → ShowsIn t (within t e b) is → Ahead e (length is)
  aheadIn t (out k a r) true  nil        = none
  aheadIn t (out k a r) true  (emit⁺ s)  = outᵃ (aheadIn t (force r) _ s)
  aheadIn t (out k a r) false nil        = none
  aheadIn t (out k a r) false (close⁺ s) = ahead s
  aheadIn t (skip k r)  true  nil        = none
  aheadIn t (skip k r)  true  (stall⁺ s) = skipᵃ (aheadIn t (force r) _ s)
  aheadIn t (skip k r)  false nil        = none
  aheadIn t (skip k r)  false (close⁺ s) = ahead s
  aheadIn t (end k)     b     nil        = none
  aheadIn t (end k)     b     (close⁺ s) = ahead s
  aheadIn t hush        b     nil        = none
  aheadIn t hush        b     (close⁺ s) = ahead s

------------------------------------------------------------------------
-- The record, against the events

module _ {A : Set} where
  open Pure A using (End; finished; dry; cutOff; frames; ending; sameFrame; stalls; later)
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
          closing : ∀ {is} → ShowsIn t (close (later (ending (cutOff c)))) is → is ≼ˡ []
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
          newIn : ∀ {is} → ShowsIn t (close (later (frames ((t′ , a) ∷ xs) en))) is → is ≼ˡ items ((t′ , a) ∷ xs) en
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

  -- The record shows every item of its own.
  mutual
    framed : ∀ xs en → Shows (frames xs en) (items xs en)
    framed []             finished   = done⁺
    framed []             dry        = quiet⁺
    framed []             (cutOff c) = nil
    framed ((t , a) ∷ xs) en         = at⁺ (emit⁺ (framedIn t xs en))

    framedIn : ∀ t xs en → ShowsIn t (inFrameᴿ t xs en) (items xs en)
    framedIn t []               (cutOff c) = nil
    framedIn t []               finished   = close⁺ done⁺
    framedIn t []               dry        = close⁺ quiet⁺
    framedIn t ((t′ , a) ∷ xs) en with t′ ≡ᵇ t in eq
    ... | true with ≡ᵇ⇒≡ t′ t (T-of eq)
    ...   | refl = emit⁺ (framedIn t xs en)
    framedIn t ((t′ , a) ∷ xs) en | false = close⁺ (at⁺ (emit⁺ (framedIn t′ xs en)))

  -- THE RECORD SHOWS NOTHING THE EVENTS DO NOT.
  placed-⊑ : ∀ {f en qs xs e} → Up f e → Placed en qs xs e → frames xs en ⊑ ticks e
  placed-⊑ u p s = shows-≼ (shown _ _ s) (shows u p)

  -- What a reader sees of a record cut short.
  private
    ≡-nil : ∀ {x is} → is ≡ [] → Shows {A} x is
    ≡-nil refl = nil

    ≡-nilIn : ∀ {t b is} → is ≡ [] → ShowsIn {A} t b is
    ≡-nilIn refl = nil

    stalls-nil : ∀ {t is} → ShowsIn {A} t (stall stalls) is → is ≡ []
    stalls-nil nil        = refl
    stalls-nil (stall⁺ s) = stalls-nil s

    ending-nil : ∀ {c is} → Shows {A} (ending (cutOff c)) is → is ≡ []
    ending-nil nil     = refl
    ending-nil (at⁺ s) = stalls-nil s

    sameFrame-nil : ∀ b c t {is} → ShowsIn {A} t (sameFrame b (stall stalls) (close (later (ending (cutOff c))))) is → is ≡ []
    sameFrame-nil true  c t s          = stalls-nil s
    sameFrame-nil false c t nil        = refl
    sameFrame-nil false c t (close⁺ s) = ending-nil s

  mutual
    -- A record cut short shows a prefix of any record extending it.
    frames-cut : ∀ (xs ys : List (Time × A)) c e → frames xs (cutOff c) ⊑ frames (xs ++ ys) e
    frames-cut []             ys c e s                 = ≡-nil (ending-nil s)
    frames-cut ((t , a) ∷ xs) ys c e nil               = nil
    frames-cut ((t , a) ∷ xs) ys c e (at⁺ nil)         = at⁺ nil
    frames-cut ((t , a) ∷ xs) ys c e (at⁺ (emit⁺ s))   = at⁺ (emit⁺ (inFrame-cut t xs ys c e s))

    inFrame-cut : ∀ t (xs ys : List (Time × A)) c e {is} → ShowsIn t (inFrameᴿ t xs (cutOff c)) is → ShowsIn t (inFrameᴿ t (xs ++ ys) e) is
    inFrame-cut t []              ys c e s = ≡-nilIn (sameFrame-nil (c ≡ᵇ t) c t s)
    inFrame-cut t ((t′ , a) ∷ xs) ys c e s = sameFrame-cut (t′ ≡ᵇ t) t t′ a xs ys c e s

    sameFrame-cut : ∀ b t t′ (a : A) xs ys c e {is}
                  → ShowsIn t (sameFrame b (emit a (withinᴿ t xs (cutOff c))) (close (later (frames ((t′ , a) ∷ xs) (cutOff c))))) is
                  → ShowsIn t (sameFrame b (emit a (withinᴿ t (xs ++ ys) e)) (close (later (frames ((t′ , a) ∷ xs ++ ys) e)))) is
    sameFrame-cut true  t t′ a xs ys c e nil        = nil
    sameFrame-cut true  t t′ a xs ys c e (emit⁺ s)  = emit⁺ (inFrame-cut t xs ys c e s)
    sameFrame-cut false t t′ a xs ys c e nil        = nil
    sameFrame-cut false t t′ a xs ys c e (close⁺ s) = close⁺ (frames-cut ((t′ , a) ∷ xs) ys c e s)
