{-# OPTIONS --guardedness #-}

-- THE MACHINE'S TRACE, PLACED, TESTED: the bisimulation the adequacy
-- proof runs on, decided on a finite prefix.  Each value the machine
-- records sits at the denotation's next `out`, at the same position, on
-- that position's tick; its completion at the `end`, its queue run dry
-- over `hush`.  Silent steps pass together while both sides have one,
-- alone otherwise, so running out of steps reads as a pass — except at a
-- `hush`, where the machine must run dry within a fixed number of steps:
-- a meaning that says nothing more will ever happen is refuted by a
-- machine still working there, however much it worked before.
--
-- And the events rise, as `ticks-up` needs: each at a position past the
-- last, a skip at one no earlier, headed by its tick.  And they are steady, as `steady-sub`
-- says: nothing strictly inside the position just left, and a value or
-- an end strictly past it.  And nothing is keyed just past another.
module quickcheck.Placing where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.List using (List; []; _∷_; _++_; [_]; length; take)
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _<ᵇ_)
open import Data.String using (String; _==_)
open import Data.Product using (_×_; _,_)

open import denotation.MonotonicList.Events using (Events; Events∞; out; skip; end; hush; Pos; ix; sub; _<ᵖ_; tick; root; Tail; Tail∞; pin; idle)
open import denotation.MonotonicList using (enter)
open import denotation.Unfold using (⟦_⟧ˢ; [])
open import operation.PureObservable using (module Driver; module Machine)
open import quickcheck.Code using (Prog; toObs; timeline)
open import quickcheck.Ty using (natᵗ)

open Driver ℕ using (Trace; Trace∞; tau; out; end; idle; trace)
open Machine using (load)

private
  samePos : Pos → Pos → Bool
  samePos p q = not (p <ᵖ q) ∧ not (q <ᵖ p)

  drains : ℕ → Trace → Bool
  drains zero    _         = false
  drains (suc j) (tau _ l) = drains j (Trace∞.force l)
  drains (suc j) idle      = true
  drains (suc j) _         = false

  placedᵇ : ℕ → ℕ → Trace → Events ℕ → Bool
  placedᵇ d zero    _             _           = true
  placedᵇ d (suc k) m             hush        = drains d m
  placedᵇ d (suc k) (tau _ l)     (skip _ r)  = placedᵇ d k (Trace∞.force l) (Events∞.force r)
  placedᵇ d (suc k) (tau _ l)     e           = placedᵇ d k (Trace∞.force l) e
  placedᵇ d (suc k) m             (skip _ r)  = placedᵇ d k m (Events∞.force r)
  placedᵇ d (suc k) (out t p a l) (out q b r) = samePos p q ∧ (t ≡ᵇ tick q) ∧ (a ≡ᵇ b) ∧ placedᵇ d k (Trace∞.force l) (Events∞.force r)
  placedᵇ d (suc k) (end p)       (end q)     = samePos p q
  placedᵇ d (suc k) _             _           = false

  headed : Pos → Bool
  headed (ix _ ∷ _) = true
  headed _          = false

  rising : ℕ → Pos → Events ℕ → Bool
  rising zero    _ _           = true
  rising (suc k) q (out p _ r) = headed p ∧ (q <ᵖ p) ∧ rising k p (Events∞.force r)
  rising (suc k) q (skip p r)  = headed p ∧ not (p <ᵖ q) ∧ rising k p (Events∞.force r)
  rising (suc k) q (end p)     = headed p ∧ (q <ᵖ p)
  rising (suc k) q hush        = true

  inside : Pos → Pos → Bool
  inside k h = (length k <ᵇ length h) ∧ samePos (take (length k) h) k

  prefixᵇ : Pos → Pos → Bool
  prefixᵇ k h = not (length h <ᵇ length k) ∧ samePos (take (length k) h) k

  mutual
    ownedᵇ : Pos → Pos → Bool
    ownedᵇ k h = prefixᵇ k h ∨ taggedᵇ k h

    taggedᵇ : Pos → Pos → Bool
    taggedᵇ k []          = false
    taggedᵇ k (sub j ∷ h) = ownedᵇ k j ∨ taggedᵇ k h
    taggedᵇ k (_ ∷ h)     = taggedᵇ k h

  positions : ℕ → Events ℕ → List Pos
  positions zero    _           = []
  positions (suc n) (out k _ r) = k ∷ positions n (Events∞.force r)
  positions (suc n) (skip k r)  = k ∷ positions n (Events∞.force r)
  positions (suc n) (end k)     = k ∷ []
  positions (suc n) hush        = []

  allᵇ : (Pos → Bool) → List Pos → Bool
  allᵇ f []       = true
  allᵇ f (x ∷ xs) = f x ∧ allᵇ f xs

  stepsᵇ : List Pos → Bool
  stepsᵇ ps = allᵇ (λ q → allᵇ (λ h → not (ownedᵇ (q ++ [ ix 0 ]) h)) ps) ps

  -- Neither keyed under the other.
  apartᵇ : Pos → Pos → Bool
  apartᵇ a b = not (ownedᵇ a b) ∧ not (ownedᵇ b a)

  -- `n` is `k` and then one or more `ix 0`: a skip marking the step at
  -- `k`, re-shown by every connect it passes untaken.
  marksᵇ : Pos → Pos → Bool
  marksᵇ []      n = zeros n
    where zeros : Pos → Bool
          zeros (ix zero ∷ [])     = true
          zeros (ix zero ∷ y ∷ ys) = zeros (y ∷ ys)
          zeros _                  = false
  marksᵇ (a ∷ k) []      = false
  marksᵇ (a ∷ k) (b ∷ n) = samePos (a ∷ []) (b ∷ []) ∧ marksᵇ k n

-- `adequacy.Placed.Order.Steady`, decided.
pastᵇ : ∀ {A} → Pos → Events A → Bool
pastᵇ k (out h _ _) = (k <ᵖ h) ∧ not (inside k h)
pastᵇ k (skip h _)  = (k <ᵖ h) ∧ not (inside k h)
pastᵇ k (end h)     = (k <ᵖ h) ∧ not (inside k h)
pastᵇ k hush        = true

clearᵇ : ∀ {A} → Pos → Events A → Bool
clearᵇ k (out h _ _) = (k <ᵖ h) ∧ not (inside k h)
clearᵇ k (skip h _)  = not (inside k h)
clearᵇ k (end h)     = (k <ᵖ h) ∧ not (inside k h)
clearᵇ k hush        = true

steadyᵇ : ∀ {A} → ℕ → Events A → Bool
steadyᵇ zero    _           = true
steadyᵇ (suc n) (out k _ r) = pastᵇ k (Events∞.force r) ∧ steadyᵇ n (Events∞.force r)
steadyᵇ (suc n) (skip k r)  = clearᵇ k (Events∞.force r) ∧ steadyᵇ n (Events∞.force r)
steadyᵇ (suc n) _           = true

-- What a cut leaves running trails the run: its steps in order, none
-- before a value coming next nor keyed with it, nor before a skip but
-- a step it marks; all past an end and
-- none inside it, none keyed where that end would subscribe a lane,
-- nor over it; nothing left behind silence.
trailᵇ : ∀ {A} → Events A → Pos → Bool
trailᵇ (out n _ _) k = not (k <ᵖ n) ∧ apartᵇ n k
trailᵇ (skip n _)  k = not (k <ᵖ n) ∨ marksᵇ k n
trailᵇ (end n)     k = (n <ᵖ k) ∧ not (inside n k) ∧ apartᵇ (n ++ [ ix 1 ]) k
trailᵇ hush        k = false

pinsᵇ : ℕ → Tail → List Pos
pinsᵇ zero    _         = []
pinsᵇ (suc n) (pin k u) = k ∷ pinsᵇ n (Tail∞.later u)
pinsᵇ (suc n) idle      = []

sortedᵇ : List Pos → Bool
sortedᵇ (x ∷ y ∷ xs) = not (y <ᵖ x) ∧ sortedᵇ (y ∷ xs)
sortedᵇ _            = true

-- And after a value, nothing left running keyed with it.
trailsᵇ : ∀ {A} → ℕ → Events∞ A → Bool
trailsᵇ zero    r = true
trailsᵇ (suc n) r = sortedᵇ ks ∧ allᵇ (trailᵇ (Events∞.force r)) ks ∧ next (Events∞.force r)
  where ks = pinsᵇ 12 (Events∞.cut r)
        next : Events _ → Bool
        next (out x _ r′) = allᵇ (apartᵇ x) (pinsᵇ 12 (Events∞.cut r′)) ∧ trailsᵇ n r′
        next (skip _ r′)  = trailsᵇ n r′
        next _            = true

private
  -- After a value at `x`, nothing later, shown or left running, keys
  -- where a lane admitted at `x` would, nor under it, nor over it.

  laterᵇ : ℕ → Events∞ ℕ → List Pos
  laterᵇ zero    r = []
  laterᵇ (suc n) r = pinsᵇ 12 (Events∞.cut r) ++ next (Events∞.force r)
    where next : Events ℕ → List Pos
          next (out k _ r′) = k ∷ laterᵇ n r′
          next (skip k r′)  = k ∷ laterᵇ n r′
          next (end k)      = k ∷ []
          next hush         = []

  spreadᵇ : ℕ → Events ℕ → Bool
  spreadᵇ zero    _           = true
  spreadᵇ (suc n) (out x _ r) = allᵇ (λ y → apartᵇ (y ++ [ ix 1 ]) (x ++ [ ix 1 ]) ∧ not (ownedᵇ y (x ++ [ ix 1 ]))) (laterᵇ 60 r) ∧ spreadᵇ n (Events∞.force r)
  spreadᵇ (suc n) (skip _ r)  = spreadᵇ n (Events∞.force r)
  spreadᵇ (suc n) _           = true

-- What a cut leaves running: nothing inside a step before it.
flatᵇ : List Pos → Bool
flatᵇ []       = true
flatᵇ (x ∷ xs) = allᵇ (λ y → not (inside x y)) xs ∧ flatᵇ xs

flatsᵇ : ∀ {A} → ℕ → Events∞ A → Bool
flatsᵇ zero    r = true
flatsᵇ (suc n) r = flatᵇ (pinsᵇ 12 (Events∞.cut r)) ∧ next (Events∞.force r)
  where next : Events _ → Bool
        next (out _ _ r′) = flatsᵇ n r′
        next (skip _ r′)  = flatsᵇ n r′
        next _            = true

-- The machine's trace placed against the meaning, and the meaning rising,
-- steady and keying nothing just past its own events; and what a cut
-- leaves running trailing it, and its values spread.  Each check by name.
checks : Prog natᵗ → List (String × Bool)
checks p = ("placed" , placedᵇ 6000 12000 (trace (load o)) e) ∷ ("rising" , rising 4000 [] e) ∷ ("steady" , steadyᵇ 4000 e)
         ∷ ("steps" , stepsᵇ (positions 200 e)) ∷ ("trails" , trailsᵇ 400 s) ∷ ("spread" , spreadᵇ 100 e)
         ∷ ("flat" , flatsᵇ 400 s) ∷ []
  where o = toObs timeline 3 p [] [] []
        s = enter (⟦ o ⟧ˢ []) root
        e = Events∞.force s

placing : Prog natᵗ → Bool
placing p = allᵇ′ (checks p)
  where allᵇ′ : List (String × Bool) → Bool
        allᵇ′ []             = true
        allᵇ′ ((_ , b) ∷ cs) = b ∧ allᵇ′ cs

-- The checks named `n` (all of them for "all") a program fails, by name.
placingParts : String → Prog natᵗ → List String
placingParts n p = failing (checks p)
  where failing : List (String × Bool) → List String
        failing []              = []
        failing ((m , b) ∷ cs) with (n == "all") ∨ (n == m) | b
        ... | true  | false = m ∷ failing cs
        ... | _     | _     = failing cs
