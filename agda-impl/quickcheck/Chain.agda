{-# OPTIONS --guardedness #-}

-- THE APPROXIMANTS SETTLE, TESTED.  `lub-limit` reads a program's meaning
-- off its approximants only if they are `Settling`: approximant n agrees
-- with approximant n+1 on its first n steps.  Checked at the root, with
-- the stronger chain shape alongside: the same events, then `⊥ᴰ`'s spin of
-- `skip`s forever.  For every n below the depth at which the approximants
-- stop changing.
module quickcheck.Chain where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using (List; []; _∷_; filterᵇ; upTo; length) renaming (map to mapL)
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_; _⊓_)
open import Data.Nat.ListAction using (sum)

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

  -- `k` steps exactly alike.
  agrees : ℕ → Events ℕ → Events ℕ → Bool
  agrees zero    _           _           = true
  agrees (suc k) (out p a l) (out q b r) = samePos p q ∧ (a ≡ᵇ b) ∧ agrees k (Events∞.force l) (Events∞.force r)
  agrees (suc k) (skip p l)  (skip q r)  = samePos p q ∧ agrees k (Events∞.force l) (Events∞.force r)
  agrees (suc k) (end p)     (end q)     = samePos p q
  agrees (suc k) hush        hush        = true
  agrees (suc k) _           _           = false

  every : (ℕ → Bool) → List ℕ → Bool
  every f []       = true
  every f (n ∷ ns) = f n ∧ every f ns

-- Approximant n against n+1, for every n that can differ: `μ` unfolded
-- 3 times and 1000 steps read, as `Quickcheck` reads 500.
chain : Prog natᵗ → Bool
chain p = every (λ n → below 1000 (at n) (at (suc n)) ∧ agrees n (at n) (at (suc n))) (upTo (depth 3 p))
  where
    at : ℕ → Events ℕ
    at n = observe (⟦ toObs timeline 3 p [] [] [] ⟧[ n ] []) root

-- THE RECORD, PLACED, TESTED: `Bound.places` decided.  Each value of
-- the pure run's record sits at its own `out` of what the denotation shows
-- the root, at the mark the run made it at, on that mark's tick, past
-- `skip`s only; the run ends as the events do — its completion at their
-- `end`, a queue run dry over `hush`, a cut anywhere.  On budgets small
-- enough to cut, and the one the oracle runs.  And the events rise, as
-- `ticks-up` needs.  Skips past the
-- fuel read as a pass: only a `hush` they never reach could refute it.
private
  open import operation.PureObservable using (module Pure)
  open import operation.AbstractObservable using (module Run)
  open import operation.PureObservable using (Pureᴾ; same)
  open import Data.Product using (_×_; _,_)
  open import Data.Unit using (⊤)
  open import denotation.MonotonicList using (tick; ix)
  open Pure ℕ using (End; finished; dry; cutOff; Res; State; endOf; Pureᴿ; runᴺ; loopᴺ; recorder; start; compileᴺ)
  open Run (Pureᴾ ℕ) using (module Engine)

  placedᵇ : ℕ → End → List Pos → List (ℕ × ℕ) → Events ℕ → Bool
  placedᵇ zero    _          _        _               _           = true
  placedᵇ (suc k) (cutOff _) []       []              _           = true
  placedᵇ (suc k) en         qs       xs              (skip _ r)  = placedᵇ k en qs xs (Events∞.force r)
  placedᵇ (suc k) en         (q ∷ qs) ((t , a) ∷ xs) (out p b r) =
    samePos q p ∧ (t ≡ᵇ tick p) ∧ (a ≡ᵇ b) ∧ placedᵇ k en qs xs (Events∞.force r)
  placedᵇ (suc k) finished   (q ∷ []) []              (end p)     = samePos q p
  placedᵇ (suc k) dry        []       []              hush        = true
  placedᵇ (suc k) _          _        _               _           = false

  ran : ℕ → Prog natᵗ → Res [] ⊤
  ran m p = Engine.drive (Pureᴿ m) (runᴺ m m) (loopᴺ m m) (compileᴺ (depth 3 p) (toObs timeline 3 p [] [] []) []) recorder same start

  -- `ticks-up`'s ground: each event at a position past the last, headed
  -- by its tick, so ticks never fall.
  headed : Pos → Bool
  headed (ix _ ∷ _) = true
  headed _          = false

  rising : ℕ → Pos → Events ℕ → Bool
  rising zero    _ _           = true
  rising (suc k) q (out p _ r) = headed p ∧ (q <ᵖ p) ∧ rising k p (Events∞.force r)
  rising (suc k) q (skip p r)  = headed p ∧ (q <ᵖ p) ∧ rising k p (Events∞.force r)
  rising (suc k) q (end p)     = headed p ∧ (q <ᵖ p)
  rising (suc k) q hush        = true

  shown : ℕ → Events ℕ → List Pos
  shown zero    _           = []
  shown (suc k) (out p _ r) = p ∷ shown k (Events∞.force r)
  shown (suc k) (skip _ r)  = shown k (Events∞.force r)
  shown (suc k) (end p)     = p ∷ []
  shown (suc k) hush        = []

places : Prog natᵗ → Bool
places p = rising 4000 [] (observe (⟦ toObs timeline 3 p [] [] [] ⟧[ depth 3 p ] []) root)
          ∧ every at (1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ 500 + depth 3 p ∷ [])
  where
    at : ℕ → Bool
    at m = placedᵇ 4000 (endOf (State.ended st) (Res.value r) (State.clock st)) (State.marks st) (State.log st)
                   (observe (⟦ toObs timeline 3 p [] [] [] ⟧[ depth 3 p ] []) root)
      where r  = ran m p
            st = Res.state r

placeFails : ℕ → ℕ → List ℕ
placeFails from count = filterᵇ (λ s → not (places (program s))) (mapL (from +_) (upTo count))

-- How many positions the seeds compared: a pass over empty records is no pass.
placed : ℕ → ℕ → ℕ
placed from count = sum (mapL (λ s → compared (program s)) (mapL (from +_) (upTo count)))
  where
    compared : Prog natᵗ → ℕ
    compared p = length (State.marks (Res.state (ran (500 + depth 3 p) p))) ⊓ length (shown 2000 (observe (⟦ toObs timeline 3 p [] [] [] ⟧[ depth 3 p ] []) root))

-- The seeds from `from`, `count` of them, whose approximants are no chain.
chainFails : ℕ → ℕ → List ℕ
chainFails from count = filterᵇ (λ s → not (chain (program s))) (mapL (from +_) (upTo count))
