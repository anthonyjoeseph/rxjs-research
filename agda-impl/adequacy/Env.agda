{-# OPTIONS --guardedness #-}

-- A GOOD TREE'S ENVIRONMENT: each binder in scope at a hole is a
-- connect's source, read lawfully, so the environment keeps the
-- invariant every entered meaning reads.
module adequacy.Env where

open import Data.List using (_∷_; _++_; [_])
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Sum using (_⊎_)

open import denotation.EmissionSet using (Proper)
open import denotation.Events using (ix)
open import denotation.Laws.Worlds using (GoodEnv; Lawful; Ok; Hots; InvAt)
open import denotation.Laws using (good-cons; inv-⟦⟧)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; CS; plug; connS; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (env; rows; Frozen; Closed)
open import adequacy.Bound using (Good)

postulate
  -- A GOOD TREE'S CONNECT SUBSCRIBED ITS SOURCE ADMISSIBLY, where the
  -- binders in scope are hot: its frozen entry is a lawful reading.
  conn-ok : ∀ {R Γ X B} (k : CS Γ X) (o : St Γ X) (b : St (X ∷ Γ) B) (c : Ctx R Γ B) → Good []ᴬ (plug c (connS k o b))
          → Ok (Hots (env c)) (CS.connAt k ++ [ ix 1 ])

mutual
  -- A GOOD TREE'S CONNECT SOURCE READS LAWFULLY, as the binder its body
  -- reads: every row of it one of its frozen entry's own, before its end.
  src-lawful : ∀ {R Γ X B} (k : CS Γ X) (o : St Γ X) (b : St (X ∷ Γ) B) (c : Ctx R Γ B) → Good []ᴬ (plug c (connS k o b))
             → Lawful (λ q e → Proper (Frozen (env c) k) q e × (rows (env c) o q e ⊎ Closed k q e))
  src-lawful k o b c g = record
    { real   = λ x → InvAt.real I (proj₁ (proj₁ x))
    ; func   = λ x x′ → InvAt.func I (proj₁ (proj₁ x)) (proj₁ (proj₁ x′))
    ; flat   = λ x x′ → InvAt.flat I (proj₁ (proj₁ x)) (proj₁ (proj₁ x′))
    ; proper = λ e y → proj₂ (proj₁ y) (proj₁ (proj₁ e))
    }
    where I = inv-⟦⟧ (CS.src k) (env c) (env-good c g) (CS.connAt k ++ [ ix 1 ]) (conn-ok k o b c g)

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
