{-# OPTIONS --guardedness #-}

-- COMPARING REPORTED RUNS.  A reader of a timeline sees its values, each
-- at its tick, then whether it completed or fell silent; a `stall`, and a
-- frame holding only stalls, it never sees.  So a run is the set of
-- finite prefixes a reader can see of it, and the order on runs is
-- inclusion of those sets: the lower run shows a prefix of what the
-- upper shows, then nothing more.
--
-- A limit of a chain is read off its members by search, one `stall` per
-- step searched, so it is productive whatever the chain does.
module denotation.Order where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product using (_×_)

open import denotation.MonotonicList using (ML; Burst; Burst∞; ML∞; done; quiet; at; emit; stall; close; Time)

------------------------------------------------------------------------
-- What a reader sees

data Item (A : Set) : Set where
  val    : Time → A → Item A
  fin    : Item A
  silent : Item A

-- `is` is how the run begins, as a reader sees it.  Inside a frame the
-- tick is known, so a value is seen with it.
mutual
  data Shows {A : Set} : ML A → List (Item A) → Set where
    nil    : ∀ {x} → Shows x []
    done⁺  : Shows done (fin ∷ [])
    quiet⁺ : Shows quiet (silent ∷ [])
    at⁺    : ∀ {t b is} → ShowsIn t b is → Shows (at t b) is

  data ShowsIn {A : Set} (t : Time) : Burst A → List (Item A) → Set where
    nil    : ∀ {b} → ShowsIn t b []
    emit⁺  : ∀ {a k is} → ShowsIn t (Burst∞.force k) is → ShowsIn t (emit a k) (val t a ∷ is)
    stall⁺ : ∀ {k is} → ShowsIn t (Burst∞.force k) is → ShowsIn t (stall k) is
    close⁺ : ∀ {k is} → Shows (ML∞.force k) is → ShowsIn t (close k) is

-- The lower run shows nothing the upper does not.
_⊑_ : ∀ {A : Set} → ML A → ML A → Set
x ⊑ y = ∀ {is} → Shows x is → Shows y is

-- The same run, up to what no reader sees.
_≃_ : ∀ {A : Set} → ML A → ML A → Set
x ≃ y = x ⊑ y × y ⊑ x

------------------------------------------------------------------------
-- Searching

private
  -- The longer of two lists, when one is a prefix of the other: the
  -- members of a chain read alike, so they are.
  longer : ∀ {A : Set} → List A → List A → List A
  longer []       ys       = ys
  longer xs       []       = xs
  longer (x ∷ xs) (_ ∷ ys) = x ∷ longer xs ys

  -- The item after `ps` in `qs`, if `qs` reaches that far.
  after : ∀ {A : Set} → List A → List A → Maybe A
  after []       (q ∷ qs) = just q
  after (_ ∷ ps) (_ ∷ qs) = after ps qs
  after _        []       = nothing

------------------------------------------------------------------------
-- Reading with a budget

-- What a reader sees in `f` steps.
private
  mutual
    seen : ∀ {A : Set} → ℕ → ML A → List (Item A)
    seen zero    _        = []
    seen (suc f) done     = fin ∷ []
    seen (suc f) quiet    = silent ∷ []
    seen (suc f) (at t b) = seenIn f t b

    seenIn : ∀ {A : Set} → ℕ → Time → Burst A → List (Item A)
    seenIn zero    t _          = []
    seenIn (suc f) t (emit a k) = val t a ∷ seenIn f t (Burst∞.force k)
    seenIn (suc f) t (stall k)  = seenIn f t (Burst∞.force k)
    seenIn (suc f) t (close k)  = seen f (ML∞.force k)

------------------------------------------------------------------------
-- The limit of a chain

private
  -- The longest of what members 0 … k show in f steps.
  bestAt : ∀ {A : Set} → (ℕ → ML A) → ℕ → ℕ → List (Item A)
  bestAt c f zero    = seen f (c zero)
  bestAt c f (suc k) = longer (seen f (c (suc k))) (bestAt c f k)

  -- Search stage i: members up to i, read for i steps.
  best : ∀ {A : Set} → (ℕ → ML A) → ℕ → List (Item A)
  best c i = bestAt c i i

  -- `ps` already shown; search at stage i.  Outside a frame, then inside
  -- the frame at tick t.
  mutual
    from : ∀ {A : Set} → (ℕ → ML A) → List (Item A) → ℕ → ML A
    from c ps i with after ps (best c i)
    ... | nothing         = at 0 (stall λ where .Burst∞.force → fromIn c 0 ps (suc i))
    ... | just fin        = done
    ... | just silent     = quiet
    ... | just (val t a)  = at t (emit a λ where .Burst∞.force → fromIn c t (ps ++ [ val t a ]) i)

    fromIn : ∀ {A : Set} → (ℕ → ML A) → Time → List (Item A) → ℕ → Burst A
    fromIn c t ps i with after ps (best c i)
    ... | nothing         = stall λ where .Burst∞.force → fromIn c t ps (suc i)
    ... | just fin        = close λ where .ML∞.force → done
    ... | just silent     = close λ where .ML∞.force → quiet
    ... | just (val u a) with u ≡ᵇ t
    ...   | true  = emit a λ where .Burst∞.force → fromIn c t (ps ++ [ val u a ]) i
    ...   | false = close λ where .ML∞.force → at u (emit a λ where .Burst∞.force → fromIn c u (ps ++ [ val u a ]) i)

-- The limit of a chain of runs.
limit : ∀ {A : Set} → (ℕ → ML A) → ML A
limit c = from c [] 0
