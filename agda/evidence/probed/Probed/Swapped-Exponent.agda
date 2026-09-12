-- THE SWAPPED MEASURE, TAKEN TO THE PROGRAMS THAT REFUTE THE LIVE ONE.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHAT IS BEING DECIDED.  The live hop measure charges a power of the
-- STORE BOUND for a fold's refolds, and a refold happens per DELIVERY —
-- which is the whole of what `Refuted.Root-Refold` exhibits, at the one
-- place no store can help: the root subscribe frame.  The restatement
-- that follows from that reads the exponent off the source's own
-- synchronous delivery count instead, and it moves every face of the
-- tower at once.  Both sides COMPUTE, so the question of whether it
-- actually stops the crossing is buyable for rows rather than for a
-- cascade, and this file buys it.
--
-- WHAT IS MIRRORED, AND WHY IT IS MIRRORED RATHER THAN IMPORTED.  The
-- two families below are the live ones clause for clause with ONE
-- difference — the fold exponent — so a row here is evidence about the
-- proposed statement and not about an approximation of it.  The store
-- bound then disappears from the reading entirely, at both families and
-- not only at the fold: once the refolds are paid for in deliveries
-- there is nothing left for it to bound, so the swap is a reading of the
-- TERM in the sense the entry needs, and not a smaller dependence on the
-- store.
--
-- WHAT THE ROWS SAY.  The refutation's family is one fold over k
-- literals, whose live reading is FLAT at a power of the bound while the
-- depth the run hands out climbs one per literal — four against three at
-- the crossing it pins.  The swapped reading climbs with the literals
-- too, and dominates at every one of them, at the bound the crossing is
-- taken at and at the degenerate bound below it.  `measure-fork` proves
-- the two readings apart at exactly the program the refutation crosses
-- at, so what separates them is the same term that refutes the live one.
--
-- THE BOUNDARY, and it is the same one the refutation records.  One fold
-- family, a merge as the only flattener, two store bounds and four
-- source lengths.  Nothing here reaches a switch or an exhaust root, and
-- nothing here says the marker itself stops: the guard is `src`'s and a
-- run against the swapped reading cannot be taken until the swap has
-- landed.  What makes these rows the right evidence anyway is the
-- refutation's own finding — that the report alongside the emissions and
-- the guard are one statement rather than two.
--
-- FORK: dry-operator
module Probed.Swapped-Exponent where

open import Data.Bool using (true; if_then_else_)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc; _+_; _*_; _^_; _⊔_; _⊔′_; _≡ᵇ_; _≤ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEvent; value; InstEmit)
open import Rx.Exp using (Ctx; Closed; Exp; Tm; obs; natᵗ;
                         input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                         mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
                         μᵉ; varᵉ; deferᵉ;
                         varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                         inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ)
open import Rx.Hop-Depth using (varIx; hopDᵉ)
open import Rx.Evaluator using (Stream)

open import Probed.Apparatus using (Separates; separates-at)
open import Probed.Delivery-Count using (dlvᵉ)
open import Refuted.Sync-Count using (Γ₀; ins₀)
open import Refuted.Root-Refold using (burstAt; η; inner₁; inner₂; inner₃; inner₄)

----------------------------------------------------------------------
-- THE MULTIPLICITY, mirrored.  Its own fold clause carries the same
-- exponent, so swapping one and not the other would leave the
-- coefficient priced in the currency the reading has just stopped using.
----------------------------------------------------------------------

mutual
  pm′ᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ν : Fin n → ℕ) (k : ℕ) →
         Exp Γ Δᵍ Δ Θ t → ℕ
  pm′ᵉ ν k (input i)          = 0
  pm′ᵉ ν k (ofᵉ ts)           = pm′ᵗˢ ν k ts
  pm′ᵉ ν k emptyᵉ             = 0
  pm′ᵉ ν k (mapᵉ f e)         =
    pm′ᵗ ν (suc k) f + (pm′ᵗ ν 0 f ⊔′ 1) * pm′ᵉ ν k e
  pm′ᵉ ν k (takeᵉ c e)        = pm′ᵉ ν k e
  pm′ᵉ ν k (scanᵉ f z e)      =
    (2 + pm′ᵗ ν 0 f) ^ dlvᵉ ν e
      * (pm′ᵗ ν (suc k) f + pm′ᵗ ν k z + pm′ᵉ ν k e)
  pm′ᵉ ν k (mergeAllᵉ lim e)  = pm′ᵉ ν k e
  pm′ᵉ ν k (switchAllᵉ e)     = pm′ᵉ ν k e
  pm′ᵉ ν k (exhaustAllᵉ e)    = pm′ᵉ ν k e
  pm′ᵉ ν k (μᵉ e)             = pm′ᵉ ν k e
  pm′ᵉ ν k (varᵉ x)           = 0
  pm′ᵉ ν k (deferᵉ e)         = 0

  pm′ᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ν : Fin n → ℕ) (k : ℕ) →
         Tm Γ Δᵍ Δ Θ t → ℕ
  pm′ᵗ ν k (varᵗ x)      = if varIx x ≡ᵇ k then 1 else 0
  pm′ᵗ ν k unit̂          = 0
  pm′ᵗ ν k (bool̂ _)      = 0
  pm′ᵗ ν k (nat̂ _)       = 0
  pm′ᵗ ν k (pairᵗ a b)   = pm′ᵗ ν k a ⊔′ pm′ᵗ ν k b
  pm′ᵗ ν k (fstᵗ p)      = pm′ᵗ ν k p
  pm′ᵗ ν k (sndᵗ p)      = pm′ᵗ ν k p
  pm′ᵗ ν k (inlᵗ a)      = pm′ᵗ ν k a
  pm′ᵗ ν k (inrᵗ a)      = pm′ᵗ ν k a
  pm′ᵗ ν k (caseᵗ s l r) =
    (pm′ᵗ ν (suc k) l ⊔′ pm′ᵗ ν (suc k) r)
      + (pm′ᵗ ν 0 l ⊔′ pm′ᵗ ν 0 r ⊔′ 1) * pm′ᵗ ν k s
  pm′ᵗ ν k (ifᵗ c a b)   = pm′ᵗ ν k a ⊔′ pm′ᵗ ν k b
  pm′ᵗ ν k (primᵗ _ a)   = 0
  pm′ᵗ ν k (strmᵗ e)     = pm′ᵉ ν k e

  pm′ᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ν : Fin n → ℕ) (k : ℕ) →
          List (Tm Γ Δᵍ Δ Θ t) → ℕ
  pm′ᵗˢ ν k []       = 0
  pm′ᵗˢ ν k (y ∷ ys) = pm′ᵗ ν k y ⊔′ pm′ᵗˢ ν k ys

----------------------------------------------------------------------
-- THE HOP READING, mirrored.  Every clause but the fold's is the live
-- one verbatim — the hop edge still costs exactly one, a defer is still
-- cut, and a slot still reports its environment — so nothing below can
-- be an artefact of a second difference.
----------------------------------------------------------------------

mutual
  hopD′ᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ν : Fin n → ℕ) (η : Fin n → ℕ) →
           Exp Γ Δᵍ Δ Θ t → ℕ
  hopD′ᵉ ν η (input i)          = η i
  hopD′ᵉ ν η (ofᵉ ts)           = hopD′ᵗˢ ν η ts
  hopD′ᵉ ν η emptyᵉ             = 0
  hopD′ᵉ ν η (mapᵉ f e)         =
    hopD′ᵗ ν η f + (pm′ᵗ ν 0 f ⊔′ 1) * hopD′ᵉ ν η e
  hopD′ᵉ ν η (takeᵉ c e)        = hopD′ᵉ ν η e
  hopD′ᵉ ν η (scanᵉ f z e)      =
    (2 + pm′ᵗ ν 0 f) ^ dlvᵉ ν e
      * (hopD′ᵗ ν η f + hopD′ᵗ ν η z + hopD′ᵉ ν η e)
  hopD′ᵉ ν η (mergeAllᵉ lim e)  = suc (hopD′ᵉ ν η e)
  hopD′ᵉ ν η (switchAllᵉ e)     = suc (hopD′ᵉ ν η e)
  hopD′ᵉ ν η (exhaustAllᵉ e)    = suc (hopD′ᵉ ν η e)
  hopD′ᵉ ν η (μᵉ e)             = hopD′ᵉ ν η e
  hopD′ᵉ ν η (varᵉ x)           = 0
  hopD′ᵉ ν η (deferᵉ e)         = 0

  hopD′ᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ν : Fin n → ℕ) (η : Fin n → ℕ) →
           Tm Γ Δᵍ Δ Θ t → ℕ
  hopD′ᵗ ν η (varᵗ x)      = 0
  hopD′ᵗ ν η unit̂          = 0
  hopD′ᵗ ν η (bool̂ _)      = 0
  hopD′ᵗ ν η (nat̂ _)       = 0
  hopD′ᵗ ν η (pairᵗ a b)   = hopD′ᵗ ν η a ⊔′ hopD′ᵗ ν η b
  hopD′ᵗ ν η (fstᵗ p)      = hopD′ᵗ ν η p
  hopD′ᵗ ν η (sndᵗ p)      = hopD′ᵗ ν η p
  hopD′ᵗ ν η (inlᵗ a)      = hopD′ᵗ ν η a
  hopD′ᵗ ν η (inrᵗ a)      = hopD′ᵗ ν η a
  hopD′ᵗ ν η (caseᵗ s l r) =
    (hopD′ᵗ ν η l ⊔′ hopD′ᵗ ν η r)
      + (pm′ᵗ ν 0 l ⊔′ pm′ᵗ ν 0 r ⊔′ 1) * hopD′ᵗ ν η s
  hopD′ᵗ ν η (ifᵗ c a b)   = hopD′ᵗ ν η a ⊔′ hopD′ᵗ ν η b
  hopD′ᵗ ν η (primᵗ _ a)   = 0
  hopD′ᵗ ν η (strmᵗ e)     = hopD′ᵉ ν η e

  hopD′ᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ν : Fin n → ℕ) (η : Fin n → ℕ) →
            List (Tm Γ Δᵍ Δ Θ t) → ℕ
  hopD′ᵗˢ ν η []       = 0
  hopD′ᵗˢ ν η (y ∷ ys) = hopD′ᵗ ν η y ⊔′ hopD′ᵗˢ ν η ys

----------------------------------------------------------------------
-- WHAT THE FRAME HANDS OUT, read at the SWAPPED measure.  The statement
-- being tested reads a depth on both sides, so a row that measured the
-- emissions with the live reading and bounded them with the new one
-- would be comparing two different quantities and could not refute
-- anything.  Only a `value` carries a payload to subscribe, and the join
-- rather than the sum because the claim is about how deep one carrier
-- can be.
----------------------------------------------------------------------

evHop′ : ∀ {n} {Γ : Ctx n} {u} (ν : Fin n → ℕ) (η : Fin n → ℕ) →
         List (InstEvent (Closed Γ u)) → ℕ
evHop′ ν η []             = 0
evHop′ ν η (value v ∷ es) = hopD′ᵉ ν η v ⊔ evHop′ ν η es
evHop′ ν η (_ ∷ es)       = evHop′ ν η es

carried′ : ∀ {n} {Γ : Ctx n} {u} (ν : Fin n → ℕ) (η : Fin n → ℕ) →
           Stream Γ (obs u) → ℕ
carried′ ν η []         = 0
carried′ ν η (em ∷ ems) = evHop′ ν η (InstEmit.events em) ⊔ carried′ ν η ems

----------------------------------------------------------------------
-- THE READING, AND IT IS NO LONGER FLAT.  The live one grows with the
-- store bound and with nothing else — one at bound zero, three at bound
-- one, whatever the source is.  Each row here is LOAD-BEARING in both
-- directions: a reading that still ignored the literals would leave the
-- crossing exactly where it is, and one growing faster than the fold can
-- refold would say the exponent is charged for deliveries that never
-- happen.
----------------------------------------------------------------------

ν₀ η₀ : Fin 0 → ℕ
ν₀ = λ ()
η₀ = λ ()

_ : hopD′ᵉ ν₀ η₀ inner₁ ≡ 3                            -- LOAD-BEARING
_ = refl

_ : hopD′ᵉ ν₀ η₀ inner₂ ≡ 9                            -- LOAD-BEARING
_ = refl

_ : hopD′ᵉ ν₀ η₀ inner₃ ≡ 27                           -- LOAD-BEARING
_ = refl

_ : hopD′ᵉ ν₀ η₀ inner₄ ≡ 81                           -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE SEPARATION, at the term the refutation crosses at.  The live
-- reading is THREE there and the depth the run hands out is four; the
-- swapped one is eighty-one.  What is apart is not a parameter of the
-- measure but the measure itself, which is why this is a fork and not a
-- second receipt for the count.
----------------------------------------------------------------------

Point : Set
Point = Closed Γ₀ (obs natᵗ)

liveRead swappedRead : Point → ℕ
liveRead    e = hopDᵉ 1 (η 1) e
swappedRead e = hopD′ᵉ ν₀ η₀ e

_ : liveRead inner₄ ≡ 3                                -- LOAD-BEARING
_ = refl

measure-fork : Separates liveRead swappedRead
measure-fork = separates-at inner₄ (λ ())

----------------------------------------------------------------------
-- THE CROSSING, RE-TAKEN.  The same depths the refutation measures —
-- one per literal, the rate belonging to the run and not to the bound —
-- now sit under the reading at every length the refutation reaches, at
-- the bound it pins the crossing at and at the degenerate bound below
-- it.  The second row is the one that was FALSE: four against three,
-- and four against eighty-one here.
--
-- AND NOT ONE OF THEM IS TIGHT, WHICH IS A FINDING AND NOT A CAVEAT.
-- The live reading crosses because it is FLAT against a linear rate;
-- this one is GEOMETRIC against that same rate, so it dominates by
-- three, seven, twenty-four and seventy-seven and the margin widens.
-- What the rows establish is therefore that the crossing STOPS, and not
-- that the reading is the right size.  The count the exponent is read
-- off was tight at its own shortest source, so the slack is entirely
-- the fold clause exponentiating a quantity that was already exact.
----------------------------------------------------------------------

_ : carried′ ν₀ η₀ (burstAt 1 inner₄ ins₀) ≡ 4         -- LOAD-BEARING
_ = refl

_ : (carried′ ν₀ η₀ (burstAt 1 inner₁ ins₀) ≤ᵇ hopD′ᵉ ν₀ η₀ inner₁) ≡ true
_ = refl

_ : (carried′ ν₀ η₀ (burstAt 1 inner₂ ins₀) ≤ᵇ hopD′ᵉ ν₀ η₀ inner₂) ≡ true
_ = refl

_ : (carried′ ν₀ η₀ (burstAt 1 inner₃ ins₀) ≤ᵇ hopD′ᵉ ν₀ η₀ inner₃) ≡ true
_ = refl

_ : (carried′ ν₀ η₀ (burstAt 1 inner₄ ins₀) ≤ᵇ hopD′ᵉ ν₀ η₀ inner₄) ≡ true
_ = refl

_ : (carried′ ν₀ η₀ (burstAt 0 inner₁ ins₀) ≤ᵇ hopD′ᵉ ν₀ η₀ inner₁) ≡ true
_ = refl

_ : (carried′ ν₀ η₀ (burstAt 0 inner₂ ins₀) ≤ᵇ hopD′ᵉ ν₀ η₀ inner₂) ≡ true
_ = refl
