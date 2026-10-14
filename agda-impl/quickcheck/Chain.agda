{-# OPTIONS --guardedness #-}

-- THE APPROXIMANTS FORM A CHAIN, TESTED.  `lub` joins approximant n of a
-- program's meaning with every deeper one, and that join means something
-- only if approximant n is approximant n+1 up to some step and `⊥ᴰ`'s
-- spin after it: the same events, then `skip`s forever.  Checked at the
-- root, for every n below the depth at which the approximants stop
-- changing.
module quickcheck.Chain where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using (List; []; _∷_; filterᵇ; upTo) renaming (map to mapL)
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)

open import denotation.MonotonicList using (Events; Events∞; out; skip; end; hush; Pos; _<ᵖ_; observe; root)
open import denotation.Denote using (⟦_⟧[_])
open import quickcheck.Code using (Prog; toObs; timeline)
open import quickcheck.Oracle using (depth)
open import quickcheck.Quickcheck using (program)
open import quickcheck.Ty using (natᵗ)

private
  samePos : Pos → Pos → Bool
  samePos p q = not (p <ᵖ q) ∧ not (q <ᵖ p)

  -- `k` steps of nothing but `skip`s.
  spins : ℕ → Events ℕ → Bool
  spins zero    _          = true
  spins (suc k) (skip _ r) = spins k (Events∞.force r)
  spins (suc k) _          = false

  -- `k` steps of the left below the right: the same events, until the
  -- left turns into a spin.
  below : ℕ → Events ℕ → Events ℕ → Bool
  below zero    _           _           = true
  below (suc k) (out p a l) (out q b r) with samePos p q ∧ (a ≡ᵇ b)
  ... | true  = below k (Events∞.force l) (Events∞.force r)
  ... | false = false
  below (suc k) (skip p l)  (skip q r)  with samePos p q
  ... | true  = below k (Events∞.force l) (Events∞.force r)
  ... | false = spins k (Events∞.force l)
  below (suc k) (end p)     (end q)     = samePos p q
  below (suc k) hush        hush        = true
  below (suc k) l           r           = spins (suc k) l

  every : (ℕ → Bool) → List ℕ → Bool
  every f []       = true
  every f (n ∷ ns) = f n ∧ every f ns

-- Approximant n against n+1, for every n that can differ: `μ` unfolded
-- 3 times and 1000 steps read, as `Quickcheck` reads 500.
chain : Prog natᵗ → Bool
chain p = every (λ n → below 1000 (at n) (at (suc n))) (upTo (depth 3 p))
  where
    at : ℕ → Events ℕ
    at n = observe (⟦ toObs timeline 3 p [] [] [] ⟧[ n ] []) root

-- The seeds from `from`, `count` of them, whose approximants are no chain.
chainFails : ℕ → ℕ → List ℕ
chainFails from count = filterᵇ (λ s → not (chain (program s))) (mapL (from +_) (upTo count))
