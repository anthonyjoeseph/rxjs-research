{-# OPTIONS --guardedness #-}

-- THE LEAVES OF `compositional`, SAMPLED.  Every operator's input is cut
-- after k steps at every subscription, then spins; if each operator is
-- non-expansive, the program's meaning is unmoved for k steps.  So one
-- program exercises every operator it holds, on inputs that agree for
-- exactly k steps, and a failure names a k and a seed.
module quickcheck.Leaves where

open import Data.Bool using (Bool; true; _∧_; not)
open import Data.List using (List; []; _∷_; _++_; [_]; filterᵇ; upTo) renaming (map to mapL)
open import Data.List.Relation.Unary.All using (_∷_; []; lookup)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Level using (lower)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList using (MonotonicList; Events; Events∞; out; skip; Pos; ix; observe; root; Timeline; coldᴰ; emptyᴰ;
  ofᴰ; mapᴰ; scanᴰ; takeWhileᴰ; flatMapᴰ; connectᴰ; deferᴰ; ⊥ᴰ)
import denotation.MonotonicList as M
open import denotation.Denote using (DenEnv; flatOp; ⟦_⟧[_])
open import quickcheck.Code using (Prog; toObs; timeline)
open import quickcheck.Chain using (agrees)
open import quickcheck.Oracle using (depth)
open import quickcheck.Quickcheck using (program)
open import quickcheck.Ty using (natᵗ)

private
  -- Skips forever, below `p`.
  spinning : ∀ {A} → Pos → ℕ → Events A
  spinning p i = skip (p ++ [ ix i ]) λ where .Events∞.force → spinning p (suc i)

  -- The first k steps, then a spin below the last position shown.
  cutᴱ : ∀ {A} → ℕ → Pos → Events A → Events A
  cutᴱ zero    p _           = spinning p 0
  cutᴱ (suc k) p (out q a r) = out q a λ where .Events∞.force → cutᴱ k q (Events∞.force r)
  cutᴱ (suc k) p (skip q r)  = skip q λ where .Events∞.force → cutᴱ k q (Events∞.force r)
  cutᴱ (suc k) p e           = e

  -- Agrees with its argument for k steps at every subscription, and no more.
  cut : ∀ {A} → ℕ → MonotonicList A → MonotonicList A
  cut k x = M.cold λ p → cutᴱ k p (observe x p)

  -- `Denote`'s approximant, every operator's inputs cut at k.
  approxC : ∀ {Γ A} → ℕ → ℕ → Obs Timeline Γ A → DenEnv Γ → MonotonicList A
  approxC k n       (cold c)          ρ = coldᴰ (lower c)
  approxC k n       empty             ρ = emptyᴰ
  approxC k n       (of xs)           ρ = ofᴰ xs
  approxC k n       (map f s)         ρ = mapᴰ f (cut k (approxC k n s ρ))
  approxC k n       (scan f z s)      ρ = scanᴰ f z (cut k (approxC k n s ρ))
  approxC k n       (takeWhile i p s) ρ = takeWhileᴰ i p (cut k (approxC k n s ρ))
  approxC k n       (flatMap op f s)  ρ = flatMapᴰ (flatOp op) (λ a → cut k (approxC k n (f a) ρ)) (cut k (approxC k n s ρ))
  approxC k n       (connect s b)     ρ = connectᴰ (cut k (approxC k n s ρ)) λ r → cut k (approxC k n b (r ∷ ρ))
  approxC k n       (connected i)     ρ = lookup ρ i
  approxC k zero    (defer l)         ρ = ⊥ᴰ
  approxC k (suc n) (defer l)         ρ = deferᴰ (cut k (approxC k n (Later.force l) ρ))

  every : (ℕ → Bool) → List ℕ → Bool
  every f []       = true
  every f (n ∷ ns) = f n ∧ every f ns

-- The cut program against the uncut one, for every k up to 60, at the
-- root, `μ` unfolded 3 times as `Chain` does.
leaves : Prog natᵗ → Bool
leaves p = every (λ k → agrees k (observe (approxC k n o []) root) (observe (⟦ o ⟧[ n ] []) root)) (upTo 60)
  where
    n = depth 3 p
    o = toObs timeline 3 p [] [] []

-- The seeds from `from`, `count` of them, where some operator reads past
-- its inputs' agreement.
leavesFails : ℕ → ℕ → List ℕ
leavesFails from count = filterᵇ (λ s → not (leaves (program s))) (mapL (from +_) (upTo count))
