{-# OPTIONS --guardedness #-}

-- AN EXHAUST'S POLICY IS DECIDED BEFORE THE ROW.  It runs a value's lane
-- by the ends of the lanes run before it, each before the value, and by
-- the values between: two cuts agreeing on the outer and on those lanes
-- run the same lanes (`ExhaustRuns.runs→`, `ExhaustRuns.runs←`).  A
-- switch's is too (`switch-cut-up`, `switch-cut-to`).
module simultaneous.JoinPolicy where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using ([_,_]′)

open import denotation.Position using (Pos)
open import denotation.EmissionSet using (EmissionSet; end; _≺_; _≼_; out; At; module ExhaustOn; module Values)
open import denotation.Laws.JoinInv using (cur-le; cur-run)
open import denotation.Laws.Modulus using (AgreeTo; upto; ≺→≼; ≺-≼-≺; ≼-trans; ≼-or-≻)
open import simultaneous.HorizonJoin using (module JoinJ)

module ExhaustRuns {A B : Set} (o : ℕ → EmissionSet A) (L : A → Pos → ℕ → EmissionSet B) where

  open JoinJ o L (λ N → ExhaustOn.Run (At (λ a s → L a s N)) (o N)) (λ _ _ _ → ⊥) using (Lane; LanesAgree)

  module X (N : ℕ) = ExhaustOn (Lane N) (o N)

  module Step {N N′ k} (ago : AgreeTo k (o N) (o N′)) (agl : LanesAgree N N′ k) where

    o→ : ∀ {y e} → y ≼ k → o N y e → o N′ y e
    o→ yk = proj₁ (upto ago yk)

    o← : ∀ {y e} → y ≼ k → o N′ y e → o N y e
    o← yk = proj₂ (upto ago yk)

    -- What holds of every value of one cut from `q ≼ k` on, holds of the
    -- other's: a value before `q` lies before `k`, where they agree.
    first→ : ∀ {q} → q ≼ k → (∀ {k′ b} → o N k′ (out b) → q ≼ k′) → ∀ {k′ b} → o N′ k′ (out b) → q ≼ k′
    first→ {q} qk m {k′} x′ = [ (λ qk′ → qk′) , (λ k′q → ⊥-elim (m (o← (≼-trans {k′} {q} {k} (≺→≼ {k′} {q} k′q) qk) x′) k′q)) ]′ (≼-or-≻ q k′)

    first← : ∀ {q} → q ≼ k → (∀ {k′ b} → o N′ k′ (out b) → q ≼ k′) → ∀ {k′ b} → o N k′ (out b) → q ≼ k′
    first← {q} qk m {k′} x = [ (λ qk′ → qk′) , (λ k′q → ⊥-elim (m (o→ (≼-trans {k′} {q} {k} (≺→≼ {k′} {q} k′q) qk) x) k′q)) ]′ (≼-or-≻ q k′)

    next→ : ∀ {q₁ q₂} → q₂ ≼ k → Values.Next (o N) q₁ q₂ → Values.Next (o N′) q₁ q₂
    next→ {q₁} {q₂} q₂k nx {k′} x′ q₁k′ =
      [ (λ q₂k′ → q₂k′) , (λ k′q₂ → ⊥-elim (nx (o← (≼-trans {k′} {q₂} {k} (≺→≼ {k′} {q₂} k′q₂) q₂k) x′) q₁k′ k′q₂)) ]′ (≼-or-≻ q₂ k′)

    next← : ∀ {q₁ q₂} → q₂ ≼ k → Values.Next (o N′) q₁ q₂ → Values.Next (o N) q₁ q₂
    next← {q₁} {q₂} q₂k nx {k′} x q₁k′ =
      [ (λ q₂k′ → q₂k′) , (λ k′q₂ → ⊥-elim (nx (o→ (≼-trans {k′} {q₂} {k} (≺→≼ {k′} {q₂} k′q₂) q₂k) x) q₁k′ k′q₂)) ]′ (≼-or-≻ q₂ k′)

    -- Before `q₂ ≼ k`, so before `k`.
    bef : ∀ {x q₂} → x ≺ q₂ → q₂ ≼ k → x ≼ k
    bef {x} {q₂} xq₂ q₂k = ≺→≼ {x} {k} (≺-≼-≺ {x} {q₂} {k} xq₂ q₂k)

    cur→ : ∀ {q₁ q} → q₁ ≼ k → X.Cur N q₁ q → X.Cur N′ q₁ q
    cur→ q₁k (ExhaustOn.cur₀ x m) = ExhaustOn.cur₀ (o→ q₁k x) (first→ q₁k m)
    cur→ {q₂} q₂k (ExhaustOn.run {q₁} {q} {a} {c} c₁ x l cq₂ x₂ q₁q₂ nx) =
      ExhaustOn.run (cur→ (bef q₁q₂ q₂k) c₁) (o→ qk x) (proj₁ (agl x (cur-run c₁) (bef cq₂ q₂k) (λ ())) (proj₁ l) , proj₂ l)
        cq₂ (o→ q₂k x₂) q₁q₂ (next→ {q₁} {q₂} q₂k nx)
      where
        qk : q ≼ k
        qk = ≼-trans {q} {q₁} {k} (cur-le c₁) (bef q₁q₂ q₂k)
    cur→ {q₂} q₂k (ExhaustOn.drop {q₁} {q} {a} c₁ x nend x₂ q₁q₂ nx) =
      ExhaustOn.drop (cur→ (bef q₁q₂ q₂k) c₁) (o→ qk x) nend′ (o→ q₂k x₂) q₁q₂ (next→ {q₁} {q₂} q₂k nx)
      where
        qk : q ≼ k
        qk = ≼-trans {q} {q₁} {k} (cur-le c₁) (bef q₁q₂ q₂k)

        nend′ : ∀ {c} → Lane N′ q a c end → q₂ ≼ c
        nend′ {c} l′ = [ (λ q₂c → q₂c)
                       , (λ cq₂ → ⊥-elim (nend (proj₂ (agl x (cur-run c₁) (bef cq₂ q₂k) (λ ())) (proj₁ l′) , proj₂ l′) cq₂)) ]′ (≼-or-≻ q₂ c)

    cur← : ∀ {q₁ q} → q₁ ≼ k → X.Cur N′ q₁ q → X.Cur N q₁ q
    cur← q₁k (ExhaustOn.cur₀ x m) = ExhaustOn.cur₀ (o← q₁k x) (first← q₁k m)
    cur← {q₂} q₂k (ExhaustOn.run {q₁} {q} {a} {c} c₁′ x′ l cq₂ x₂ q₁q₂ nx) =
      ExhaustOn.run c₁ x (proj₂ (agl x (cur-run c₁) (bef cq₂ q₂k) (λ ())) (proj₁ l) , proj₂ l) cq₂ (o← q₂k x₂) q₁q₂ (next← {q₁} {q₂} q₂k nx)
      where
        c₁ : X.Cur N q₁ q
        c₁ = cur← (bef q₁q₂ q₂k) c₁′

        x : o N q (out a)
        x = o← (≼-trans {q} {q₁} {k} (cur-le c₁′) (bef q₁q₂ q₂k)) x′
    cur← {q₂} q₂k (ExhaustOn.drop {q₁} {q} {a} c₁′ x′ nend x₂ q₁q₂ nx) =
      ExhaustOn.drop c₁ x nend′ (o← q₂k x₂) q₁q₂ (next← {q₁} {q₂} q₂k nx)
      where
        c₁ : X.Cur N q₁ q
        c₁ = cur← (bef q₁q₂ q₂k) c₁′

        x : o N q (out a)
        x = o← (≼-trans {q} {q₁} {k} (cur-le c₁′) (bef q₁q₂ q₂k)) x′

        nend′ : ∀ {c} → Lane N q a c end → q₂ ≼ c
        nend′ {c} l = [ (λ q₂c → q₂c)
                      , (λ cq₂ → ⊥-elim (nend (proj₁ (agl x (cur-run c₁) (bef cq₂ q₂k) (λ ())) (proj₁ l) , proj₂ l) cq₂)) ]′ (≼-or-≻ q₂ c)

  runs→ : ∀ {N N′ k q} → AgreeTo k (o N) (o N′) → LanesAgree N N′ k → q ≼ k → X.Run N q → X.Run N′ q
  runs→ ago agl = Step.cur→ ago agl

  runs← : ∀ {N N′ k q} → AgreeTo k (o N) (o N′) → LanesAgree N N′ k → q ≼ k → X.Run N′ q → X.Run N q
  runs← ago agl = Step.cur← ago agl
