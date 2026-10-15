{-# OPTIONS --guardedness #-}

-- THE MACHINE'S TRACE, PLACED, TESTED: the machine against the fold's
-- events, positions included, decided on a finite prefix.  Each value the machine
-- records sits at the denotation's next `out`, at the same position, on
-- that position's tick; its completion at the `end`, its queue run dry
-- over `hush`.  Silent steps pass together while both sides have one,
-- alone otherwise, so running out of steps reads as a pass — except at a
-- `hush`, where the machine must run dry within a fixed number of steps:
-- a meaning that says nothing more will ever happen is refuted by a
-- machine still working there, however much it worked before.
--
-- And the events rise: each at a position past the last, headed by its
-- tick.
module quickcheck.Placing where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using (List; []; _∷_; filterᵇ; upTo) renaming (map to mapL)
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)

open import denotation.MonotonicList using (Events; Events∞; out; skip; end; hush; Pos; ix; _<ᵖ_; tick; observe; root)
open import denotation.Denote using (⟦_⟧[_])
open import operation.Machine using (module Machine)
open import quickcheck.Code using (Prog; toObs; timeline)
open import quickcheck.Oracle using (depth)
open import quickcheck.Ty using (natᵗ)
open import quickcheck.Quickcheck using (program)

open Machine ℕ using (Trace; Trace∞; tau; out; end; idle; trace; begin)

private
  samePos : Pos → Pos → Bool
  samePos p q = not (p <ᵖ q) ∧ not (q <ᵖ p)

  drains : ℕ → Trace → Bool
  drains zero    _         = false
  drains (suc j) (tau _ l) = drains j (Trace∞.force l)
  drains (suc j) idle      = true
  drains (suc j) _         = false

  placedᵇ : ℕ → Trace → Events ℕ → Bool
  placedᵇ zero    _             _           = true
  placedᵇ (suc k) m             hush        = drains 20000 m
  placedᵇ (suc k) (tau _ l)     (skip _ r)  = placedᵇ k (Trace∞.force l) (Events∞.force r)
  placedᵇ (suc k) (tau _ l)     e           = placedᵇ k (Trace∞.force l) e
  placedᵇ (suc k) m             (skip _ r)  = placedᵇ k m (Events∞.force r)
  placedᵇ (suc k) (out t p a l) (out q b r) = samePos p q ∧ (t ≡ᵇ tick q) ∧ (a ≡ᵇ b) ∧ placedᵇ k (Trace∞.force l) (Events∞.force r)
  placedᵇ (suc k) (end p)       (end q)     = samePos p q
  placedᵇ (suc k) _             _           = false

  headed : Pos → Bool
  headed (ix _ ∷ _) = true
  headed _          = false

  rising : ℕ → Pos → Events ℕ → Bool
  rising zero    _ _           = true
  rising (suc k) q (out p _ r) = headed p ∧ (q <ᵖ p) ∧ rising k p (Events∞.force r)
  rising (suc k) q (skip p r)  = headed p ∧ (q <ᵖ p) ∧ rising k p (Events∞.force r)
  rising (suc k) q (end p)     = headed p ∧ (q <ᵖ p)
  rising (suc k) q hush        = true

-- The machine's trace placed against the meaning, and the meaning rising.
placing : Prog natᵗ → Bool
placing p = placedᵇ 40000 (trace (begin o)) e ∧ rising 4000 [] e
  where o = toObs timeline 3 p [] [] []
        e = observe (⟦ o ⟧[ depth 3 p ] []) root

-- The seeds from f on which the machine's trace strays from the meaning.
placingFails : ℕ → ℕ → List ℕ
placingFails f c = filterᵇ (λ s → not (placing (program s))) (mapL (f +_) (upTo c))
