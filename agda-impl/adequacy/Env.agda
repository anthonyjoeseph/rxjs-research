{-# OPTIONS --guardedness #-}

-- A GOOD TREE'S ENVIRONMENT: each binder in scope at a hole is a
-- connect's source, read lawfully, so the environment keeps the
-- invariant every entered meaning reads.
module adequacy.Env where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (_∷_; _++_; [_])
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.EmissionSet using (EmissionSet; DenEnv; Proper)
open import denotation.Events using (ix)
open import denotation.Laws.Worlds using (GoodEnv; Lawful; Ok; Hots; InvAt)
open import denotation.Laws using (good-cons; inv-⟦⟧)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; CS; plug; connS; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (env; Frozen; Closed)
open import adequacy.Bound using (Good; Live)
open import adequacy.Inv using (liv; node-good)

live-on : ∀ {b X} → b ≡ true → Live b X → X
live-on refl x = x

∧-true : ∀ a {b} → a ∧ b ≡ true → a ≡ true
∧-true true  _ = refl
∧-true false ()

-- A GOOD TREE'S LIVE CONNECT SUBSCRIBED ITS SOURCE ADMISSIBLY, where the
-- binders in scope are hot: its frozen entry is a lawful reading.  Under
-- a cut switched off a good tree asks only shape, so a connect there may
-- sit anywhere.
conn-ok : ∀ {R Γ X B} (k : CS Γ X) (o : St Γ X) (b : St (X ∷ Γ) B) (c : Ctx R Γ B) → liv c ≡ true → Good []ᴬ (plug c (connS k o b))
        → Ok (Hots (env c)) (CS.connAt k ++ [ ix 1 ])
conn-ok k o b c lv g = live-on lv (proj₂ (proj₂ (proj₂ (proj₂ (node-good c (connS k o b) g (λ ()) (λ ()))))))

-- A BINDER SUBSCRIBED ADMISSIBLY READS LAWFULLY, under lawful binders:
-- every row of it one of its frozen entry's own, before its end.
hot-lawful : ∀ {Γ X} {ρ : DenEnv Γ} (k : CS Γ X) {t : EmissionSet X} → GoodEnv ρ → Ok (Hots ρ) (CS.connAt k ++ [ ix 1 ])
           → Lawful (λ q e → Proper (Frozen ρ k) q e × (t q e ⊎ Closed k q e))
hot-lawful {ρ = ρ} k ge ok = record
  { real   = λ x → InvAt.real I (proj₁ (proj₁ x))
  ; func   = λ x x′ → InvAt.func I (proj₁ (proj₁ x)) (proj₁ (proj₁ x′))
  ; flat   = λ x x′ → InvAt.flat I (proj₁ (proj₁ x)) (proj₁ (proj₁ x′))
  ; proper = λ e y → proj₂ (proj₁ y) (proj₁ (proj₁ e))
  }
  where I = inv-⟦⟧ (CS.src k) ρ ge (CS.connAt k ++ [ ix 1 ]) ok

-- A good tree's environment at a live hole keeps the invariant: each
-- binder a connect's source, subscribed admissibly.
env-good : ∀ {R Γ A} (c : Ctx R Γ A) {s} → liv c ≡ true → Good []ᴬ (plug c s) → GoodEnv (env c)
env-good top                                         _  _ ()
env-good (inMap f c)                                 lv g = env-good c lv g
env-good (inScan f z c)                              lv g = env-good c lv g
env-good (inCut l a c)                               lv g = env-good c (∧-true (liv c) lv) g
env-good (inLn b c)                                  lv g = env-good c lv g
env-good (inOuter op f d n q ls c)                   lv g = env-good c lv g
env-good (inLanes op f d n q o pre post c)           lv g = env-good c lv g
env-good (inTake i q w c)                            lv g = env-good c lv g
env-good (inSrc k b c)                               lv g = env-good c lv g
env-good (inBody k o c) {s}                          lv g = good-cons (hot-lawful k (env-good c lv g) (conn-ok k o s c lv g)) (env-good c lv g)
