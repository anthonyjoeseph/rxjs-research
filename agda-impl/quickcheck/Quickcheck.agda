{-# OPTIONS --guardedness #-}

-- ADEQUACY, TESTED.  The denotation and the pure event loop must give the
-- same trace for every program; `quickcheck k` returns the seeds below k
-- whose program they disagree on.  A trace cut by the step budget only
-- has to be a prefix of the other side's.
module quickcheck.Quickcheck where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using (List; []; _∷_; _++_; filterᵇ; upTo)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _/_; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import operation.abstraction.Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import quickcheck.Ty
open import quickcheck.Tm
open import quickcheck.Code
open import quickcheck.Oracle

------------------------------------------------------------------------
-- The property

private
  eqEvent : ∀ t → Event ⟦ t ⟧ᵀ → Event ⟦ t ⟧ᵀ → Bool
  eqEvent t (tick j) (tick k) = j ≡ᵇ k
  eqEvent t (val a)  (val b)  = eqᵀ t a b
  eqEvent t _        _        = false

  eqEnd : End → End → Bool
  eqEnd completed completed = true
  eqEnd silent    silent    = true
  eqEnd cut       cut       = true
  eqEnd _         _         = false

  -- the left is a prefix of the right
  prefix : ∀ t → List (Event ⟦ t ⟧ᵀ) → List (Event ⟦ t ⟧ᵀ) → Bool
  prefix t []       _        = true
  prefix t (x ∷ xs) []       = false
  prefix t (x ∷ xs) (y ∷ ys) = eqEvent t x y ∧ prefix t xs ys

agrees : ∀ t → Trace ⟦ t ⟧ᵀ → Trace ⟦ t ⟧ᵀ → Bool
agrees t (xs ▸ cut) (ys ▸ _)   = prefix t xs ys
agrees t (xs ▸ _)   (ys ▸ cut) = prefix t ys xs
agrees t (xs ▸ x)   (ys ▸ y)   = prefix t xs ys ∧ prefix t ys xs ∧ eqEnd x y

-- Each `μ` unfolds at most 3 times; each trace is read for 500 steps.
prop : Prog natᵗ → Bool
prop p = agrees natᵗ (denoteTrace 3 500 p) (pureTrace 3 500 p)

------------------------------------------------------------------------
-- Generating: programs over ℕ, every context a list of `natᵗ`s

private
  Gen : Set → Set
  Gen A = ℕ → A × ℕ

  pure : ∀ {A} → A → Gen A
  pure a s = a , s

  _>>=_ : ∀ {A B} → Gen A → (A → Gen B) → Gen B
  (g >>= f) s with g s
  ... | a , s′ = f a s′

  -- a number in 0 … k, off the high bits of a linear congruential step
  roll : ℕ → Gen ℕ
  roll k s = let s′ = (s * 1103515245 + 12345) % 2147483648 in (s′ / 65536) % suc k , s′

  -- the k-th `natᵗ` in a context, if it has one
  pick : ∀ Γ → ℕ → Maybe (natᵗ ∈ Γ)
  pick []           k       = nothing
  pick (natᵗ ∷ Γ)   zero    = just (here refl)
  pick (natᵗ ∷ Γ)   (suc k) = Data.Maybe.map there (pick Γ k)
  pick (_ ∷ Γ)      k       = Data.Maybe.map there (pick Γ k)

  genNat : ℕ → ∀ Θ → Gen (Tm Θ natᵗ)
  genNat d Θ = do
    k ← roll 3
    leaf k d
    where
      leaf : ℕ → ℕ → Gen (Tm Θ natᵗ)
      leaf (suc (suc _)) (suc d) = do
        a ← genNat d Θ
        b ← genNat d Θ
        pure (plus a b)
      leaf k _ with pick Θ k
      ... | just i  = pure (var i)
      ... | nothing = do n ← roll 5 ; pure (nat n)

  genBool : ∀ Θ → Gen (Tm Θ boolᵗ)
  genBool Θ = do
    a ← genNat 1 Θ
    b ← genNat 1 Θ
    pure (less a b)

  genEcho : ∀ Θ → Gen (Tm Θ (maybeᵗ natᵗ))
  genEcho Θ = do
    k ← roll 2
    if0 k
    where
      if0 : ℕ → Gen (Tm Θ (maybeᵗ natᵗ))
      if0 zero    = pure (inl unit)
      if0 (suc _) = do a ← genNat 1 Θ ; pure (inr a)

  genOp : Gen FlatOp
  genOp = do
    k ← roll 3
    pure (op k)
    where
      op : ℕ → FlatOp
      op 0 = mergeᶠ nothing
      op 1 = mergeᶠ (just 1)
      op 2 = switchᶠ
      op _ = exhaustᶠ

  genValues : ℕ → Gen (List ℕ)
  genValues zero    = pure []
  genValues (suc n) = do
    k ← roll 3
    more k
    where
      more : ℕ → Gen (List ℕ)
      more zero    = pure []
      more (suc _) = do x ← roll 4 ; xs ← genValues n ; pure (x ∷ xs)

  -- frame times strictly increase
  genFrames : ℕ → ℕ → Gen (List (ℕ × List ℕ))
  genFrames t zero    = pure []
  genFrames t (suc n) = do
    k ← roll 2
    xs ← genValues 3
    fs ← genFrames (t + suc k) n
    pure ((t + k , xs) ∷ fs)

  genScript : Gen (Script natᵗ)
  genScript = do
    n ← roll 3
    fs ← genFrames 0 n
    c ← roll 1
    pure (script fs (c ≡ᵇ 0))

  genLeaf : ∀ Γ Δᵍ Δ Θ → Gen (Code Γ Δᵍ Δ Θ natᵗ)
  genLeaf Γ Δᵍ Δ Θ = do
    k ← roll 4
    j ← roll 2
    leaf k j
    where
      leaf : ℕ → ℕ → Gen (Code Γ Δᵍ Δ Θ natᵗ)
      leaf 0 _ = pure empty
      leaf 1 _ = do a ← genNat 1 Θ ; b ← genNat 1 Θ ; pure (of (a ∷ b ∷ []))
      leaf 2 j with pick Γ j
      ... | just i  = pure (connected i)
      ... | nothing = do s ← genScript ; pure (cold s)
      leaf 3 j with pick Δ j
      ... | just i  = pure (var i)
      ... | nothing = do s ← genScript ; pure (cold s)
      leaf _ _ = do s ← genScript ; pure (cold s)

  gen : ℕ → ∀ Γ Δᵍ Δ Θ → Gen (Code Γ Δᵍ Δ Θ natᵗ)
  gen zero    Γ Δᵍ Δ Θ = genLeaf Γ Δᵍ Δ Θ
  gen (suc d) Γ Δᵍ Δ Θ = do
    k ← roll 8
    node k
    where
      node : ℕ → Gen (Code Γ Δᵍ Δ Θ natᵗ)
      node 0 = do f ← genNat 2 (natᵗ ∷ Θ) ; s ← gen d Γ Δᵍ Δ Θ ; pure (map f s)
      node 1 = do
        f ← genNat 2 (natᵗ ∷ natᵗ ∷ Θ)
        z ← genNat 1 Θ
        s ← gen d Γ Δᵍ Δ Θ
        pure (scan f z s)
      node 2 = do p ← genBool (natᵗ ∷ Θ) ; s ← gen d Γ Δᵍ Δ Θ ; pure (takeWhile p s)
      node 3 = do
        op ← genOp
        e ← genEcho (natᵗ ∷ Θ)
        h ← genBool (natᵗ ∷ Θ)
        l ← gen d Γ Δᵍ Δ (natᵗ ∷ Θ)
        s ← gen d Γ Δᵍ Δ Θ
        pure (flatten op e h l s)
      node 4 = do s ← gen d Γ Δᵍ Δ Θ ; b ← gen d (natᵗ ∷ Γ) Δᵍ Δ Θ ; pure (connect s b)
      node 5 = do c ← gen d Γ (natᵗ ∷ Δᵍ) Δ Θ ; pure (μ c)
      node 6 = do c ← gen d Γ [] (Δᵍ ++ Δ) Θ ; pure (defer c)
      node _ = genLeaf Γ Δᵍ Δ Θ

-- The program a seed names.
program : ℕ → Prog natᵗ
program seed with gen 4 [] [] [] [] seed
... | p , _ = p

-- The seeds below k on which the two semantics disagree.
quickcheck : ℕ → List ℕ
quickcheck k = filterᵇ (λ seed → not (prop (program seed))) (upTo k)
