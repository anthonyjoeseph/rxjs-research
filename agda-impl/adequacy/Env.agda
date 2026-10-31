{-# OPTIONS --guardedness #-}

-- A GOOD TREE'S ENVIRONMENT: each binder in scope at a hole is a
-- connect's source, read lawfully, so the environment keeps the
-- invariant every entered meaning reads.
module adequacy.Env where

open import Data.List using (_∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Sum using (_⊎_)

open import denotation.EmissionSet using (Proper)
open import denotation.Laws.Worlds using (GoodEnv; Lawful)
open import denotation.Laws using (good-cons)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; CS; plug; connS; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (env; rows; Closed)
open import adequacy.Bound using (Good)

postulate
  -- A GOOD TREE'S CONNECT SOURCE READS LAWFULLY: its rows reachable, one
  -- event at a position, none below another, as the binder its body reads.
  src-lawful : ∀ {R Γ X B} (k : CS) (o : St Γ X) (b : St (X ∷ Γ) B) (c : Ctx R Γ B) → Good []ᴬ (plug c (connS k o b))
             → Lawful (Proper (λ q e → rows (env c) o q e ⊎ Closed k q e))

-- A good tree's environment keeps the invariant: each binder a
-- connect's source.
env-good : ∀ {R Γ A} (c : Ctx R Γ A) {s} → Good []ᴬ (plug c s) → GoodEnv (env c)
env-good top                                         _ ()
env-good (inMap f c)                                 g = env-good c g
env-good (inScan f z c)                              g = env-good c g
env-good (inCut l a c)                               g = env-good c g
env-good (inLn b c)                                  g = env-good c g
env-good (inOuter op f d n q ls c)                   g = env-good c g
env-good (inLanes op f d n q o pre post c)           g = env-good c g
env-good (inTake i q w c)                            g = env-good c g
env-good (inSrc k b c)                               g = env-good c g
env-good (inBody k o c) {s}                          g = good-cons (src-lawful k o s c g) (env-good c g)
