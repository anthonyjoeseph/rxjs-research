{-# OPTIONS --guardedness #-}

-- ADEQUACY, TESTED.  The denotation, the pure event loop and the
-- state-tree machine must give the same trace for every program; `quickcheck k` returns the seeds below k
-- whose program they disagree on.  A trace cut by the step budget only
-- has to be a prefix of the other side's.
module quickcheck.Quickcheck where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; filterᵇ; upTo; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _/_; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import quickcheck.Ty using (boolᵗ; natᵗ; nameᵗ; _×ᵗ_; ⟦_⟧ᵀ; eqᵀ)
open import quickcheck.Tm using (Tm; var; nat; plus; less; pair)
open import quickcheck.Code using (Script; script; Code; cold; fresh; empty; of; map; scan; takeWhile; flatMap; connect; connected; μ; var; defer; Prog)
open import quickcheck.Oracle using (Event; _▸_; tick; val; End; completed; silent; cut; Trace; denoteTrace; pureTrace; stateTrace)

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
agrees t (xs ▸ cut) (ys ▸ cut) = prefix t xs ys ∨ prefix t ys xs
agrees t (xs ▸ cut) (ys ▸ _)   = prefix t xs ys
agrees t (xs ▸ _)   (ys ▸ cut) = prefix t ys xs
agrees t (xs ▸ x)   (ys ▸ y)   = prefix t xs ys ∧ prefix t ys xs ∧ eqEnd x y

-- Each `μ` unfolds at most 3 times; each trace is read for 500 steps.
prop : ∀ t → Prog t → Bool
prop t p = agrees t (denoteTrace 3 500 p) (pureTrace 3 500 p) ∧ agrees t (denoteTrace 3 500 p) (stateTrace 3 500 p)

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

  genOp : Gen FlatOp
  genOp = do
    k ← roll 5
    pure (op k)
    where
      op : ℕ → FlatOp
      op 0 = mergeᶠ nothing
      op 1 = mergeᶠ (just 1)
      op 2 = mergeᶠ (just 2)
      op 3 = mergeᶠ (just 3)
      op 4 = switchᶠ
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

  -- each frame's gap after the one before
  genFrames : ℕ → Gen (List (ℕ × List ℕ))
  genFrames zero    = pure []
  genFrames (suc n) = do
    k ← roll 2
    xs ← genValues 3
    fs ← genFrames n
    pure ((k , xs) ∷ fs)

  genScript : Gen (Script natᵗ)
  genScript = do
    n ← roll 3
    fs ← genFrames n
    c ← roll 1
    l ← roll 3
    pure (script fs (c ≡ᵇ 0) (l ≡ᵇ 0))

  genLeaf : ∀ Γ Δᵍ Δ Θ → Gen (Code Γ Δᵍ Δ Θ natᵗ)
  genLeaf Γ Δᵍ Δ Θ = do
    k ← roll 4
    j ← roll 2
    leaf k j
    where
      -- a `connect` in scope, when there is one
      handle : ℕ → Gen (Code Γ Δᵍ Δ Θ natᵗ)
      handle j with pick Γ (j % suc (length Γ)) | pick Γ 0
      ... | just i | _      = pure (connected i)
      ... | _      | just i = pure (connected i)
      ... | _      | _      = do s ← genScript ; pure (cold s)

      leaf : ℕ → ℕ → Gen (Code Γ Δᵍ Δ Θ natᵗ)
      leaf 0 _ = pure empty
      leaf 1 _ = do a ← genNat 1 Θ ; b ← genNat 1 Θ ; pure (of (a ∷ b ∷ []))
      leaf 2 j = handle j
      leaf 3 j with pick Δ j
      ... | just i  = pure (var i)
      ... | nothing = handle j
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
      node 2 = do i ← roll 1 ; p ← genBool (natᵗ ∷ Θ) ; s ← gen d Γ Δᵍ Δ Θ ; pure (takeWhile (i ≡ᵇ 0) p s)
      node 3 = do
        op ← genOp
        l ← gen d Γ Δᵍ Δ (natᵗ ∷ Θ)
        s ← gen d Γ Δᵍ Δ Θ
        pure (flatMap op l s)
      node 4 = do s ← gen d Γ Δᵍ Δ Θ ; b ← gen d (natᵗ ∷ Γ) Δᵍ Δ Θ ; pure (connect s b)
      node 5 = do c ← gen d Γ (natᵗ ∷ Δᵍ) Δ Θ ; pure (μ c)
      node 6 = do c ← gen d Γ [] (Δᵍ ++ Δ) Θ ; pure (defer c)
      node 7 = do s ← gen d Γ Δᵍ Δ Θ ; b ← gen d (natᵗ ∷ Γ) Δᵍ Δ Θ ; pure (connect s b)
      node _ = genLeaf Γ Δᵍ Δ Θ

-- The program a seed names.
program : ℕ → Prog natᵗ
program seed with gen 4 [] [] [] [] seed
... | p , _ = p

-- NAMED: a program's values each tagged with a `fresh` name, one lane per
-- value, so each tag names its own subscription; or that tagged program
-- shared by `connect` with two lanes, so each name is shown twice.  Names
-- compare only by equality, so a trace is read up to renaming them.
private
  tagged : ∀ {Γ Δᵍ Δ Θ} → FlatOp → Code Γ Δᵍ Δ Θ natᵗ → Code Γ Δᵍ Δ Θ (natᵗ ×ᵗ nameᵗ)
  tagged op s = flatMap op (map (pair (var (there (here refl))) (var (here refl))) fresh) s

  shared : ∀ {Γ Δᵍ Δ Θ} → FlatOp → Code Γ Δᵍ Δ Θ natᵗ → Code Γ Δᵍ Δ Θ (natᵗ ×ᵗ nameᵗ)
  shared op s = connect (tagged op s) (flatMap (mergeᶠ nothing) (connected (here refl)) (of (nat 0 ∷ nat 1 ∷ [])))

  genNamed : Gen (Prog (natᵗ ×ᵗ nameᵗ))
  genNamed = do
    s ← gen 4 [] [] [] []
    op ← genOp
    k ← roll 1
    pure (if k ≡ᵇ 0 then tagged op s else shared op s)

named : ℕ → Prog (natᵗ ×ᵗ nameᵗ)
named seed with genNamed seed
... | p , _ = p

-- The seeds below k on which the two semantics disagree, on the seed's
-- program or its named one.  Both read a name as its subscription's
-- position, so here names compare exactly.
quickcheck : ℕ → List ℕ
quickcheck k = filterᵇ (λ seed → not (prop natᵗ (program seed) ∧ prop (natᵗ ×ᵗ nameᵗ) (named seed))) (upTo k)
