{-# OPTIONS --guardedness #-}

-- TWO LANES RACING BELOW A ROW.  A joiner's rows before `z` are a few of
-- its own and the rows of two lanes, each lane's rows few before each of
-- them.  A lane row is shown once the joiner's rows before it are few, so
-- where every shown row before `z` is one of a finite list, the rows of
-- any kind before `z` are few: the lowest lane row past the list would
-- be shown.  By induction on each lane's rows before, never on the
-- joiner's.
module simultaneous.Race where

open import Data.List using (List; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)

open import denotation.Position using (Pos)
open import denotation.EmissionSet using (Ev; EmissionSet; _≺_; _≼_; Few; Truncate)
open import denotation.Laws.Modulus using (≺-trans; ≺-≼-≺; ≺→≼; ≼-refl; few-ind)
open import denotation.Laws.Shows using (∈-stable)

module Race {X Y Z : Set} (U : EmissionSet X) (A : EmissionSet Y) (B : EmissionSet Z) (z : Pos)
            (fin G : List Pos)
            (cls : ∀ {r e} → U r e → r ≺ z → r ∈ fin ⊎ (Σ (Ev Y) (A r) ⊎ Σ (Ev Z) (B r)))
            (up  : ∀ {r} → Σ (Ev Y) (A r) ⊎ Σ (Ev Z) (B r) → ¬ ¬ Σ (Ev X) (U r))
            (fewA : ∀ {a e} → A a e → Few A a) (fewB : ∀ {b e} → B b e → Few B b)
            (cov : ∀ {r e} → Truncate U r e → r ≺ z → r ∈ G) where

  -- A lane row before `z` with few rows before it is shown, so listed.
  listed : ∀ {r} → r ≺ z → Few U r → Σ (Ev Y) (A r) ⊎ Σ (Ev Z) (B r) → r ∈ G
  listed rz (ks , h) ab = ∈-stable λ ¬i → up ab λ { (_ , u) → ¬i (cov (u , ks , λ x lt _ → h x lt) rz) }

  -- Before `w`, each lane's rows listed: few rows of any kind.
  few-at : ∀ {w} → w ≼ z → (∀ {a e} → A a e → a ≺ w → a ∈ G) → (∀ {b e} → B b e → b ≺ w → b ∈ G) → Few U w
  few-at {w} wz hA hB = fin ++ G , pick
    where
      pick : ∀ {r e} → U r e → r ≺ w → r ∈ fin ++ G
      pick {r} x rw with cls x (≺-≼-≺ {r} {w} {z} rw wz)
      ... | inj₁ i                = ∈-++⁺ˡ i
      ... | inj₂ (inj₁ (_ , a))   = ∈-++⁺ʳ fin (hA a rw)
      ... | inj₂ (inj₂ (_ , b))   = ∈-++⁺ʳ fin (hB b rw)

  -- Below `w`, with the first lane's rows few-preceded: so are the second's.
  few-B : ∀ {w} → w ≼ z → (∀ {a e} → A a e → a ≺ w → Few U a) → ∀ {b e} → B b e → b ≺ w → Few U b
  few-B {w} wz hA {b} x bw = few-ind {t = B} (λ v → v ≺ w → Few U v) step (fewB x) bw
    where
      step : ∀ {v} → Few B v → (∀ {u e} → B u e → u ≺ v → u ≺ w → Few U u) → v ≺ w → Few U v
      step {v} _ ih vw = few-at vz
        (λ {a} a′ av → listed (≺-trans {a} {v} {z} av vz′) (hA a′ (≺-trans {a} {v} {w} av vw)) (inj₁ (_ , a′)))
        (λ {u} u′ uv → listed (≺-trans {u} {v} {z} uv vz′) (ih u′ uv (≺-trans {u} {v} {w} uv vw)) (inj₂ (_ , u′)))
        where
          vz′ : v ≺ z
          vz′ = ≺-≼-≺ {v} {w} {z} vw wz
          vz : v ≼ z
          vz = ≺→≼ {v} {z} vz′

  -- The first lane's rows before `z` are few-preceded.
  few-A : ∀ {a e} → A a e → a ≺ z → Few U a
  few-A x az = few-ind {t = A} (λ v → v ≺ z → Few U v) step (fewA x) az
    where
      step : ∀ {v} → Few A v → (∀ {u e} → A u e → u ≺ v → u ≺ z → Few U u) → v ≺ z → Few U v
      step {v} _ ih vz = few-at (≺→≼ {v} {z} vz)
        (λ {a} a′ av → listed (≺-trans {a} {v} {z} av vz) (ih a′ av (≺-trans {a} {v} {z} av vz)) (inj₁ (_ , a′)))
        (λ {b} b′ bv → listed (≺-trans {b} {v} {z} bv vz)
                         (few-B (≺→≼ {v} {z} vz) (λ {a} a′ av → ih a′ av (≺-trans {a} {v} {z} av vz)) b′ bv) (inj₂ (_ , b′)))

  -- So few rows of any kind lie before `z`.
  few : Few U z
  few = few-at (≼-refl {z})
    (λ {a} a′ az → listed az (few-A a′ az) (inj₁ (_ , a′)))
    (λ {b} b′ bz → listed bz (few-B (≼-refl {z}) few-A b′ bz) (inj₂ (_ , b′)))
