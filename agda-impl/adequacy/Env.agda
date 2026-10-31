{-# OPTIONS --guardedness #-}

-- A GOOD TREE'S ENVIRONMENT: each binder in scope at a hole is a
-- connect's source, read lawfully, so the environment keeps the
-- invariant every entered meaning reads.
module adequacy.Env where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (_∷_; _++_; [_])
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.EmissionSet using (EmissionSet; Proper)
open import denotation.Events using (ix)
open import denotation.Laws.Worlds using (GoodEnv; Lawful; InvAt)
open import denotation.Laws using (good-cons; inv-⟦⟧)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; CS; Scope; unbound; binds; plug; connS; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (env; Frozen; Closed; full; ScopeOk; Admits)
open import adequacy.Bound using (Good; Live)
open import adequacy.Inv using (liv; node-good)

live-on : ∀ {b X} → b ≡ true → Live b X → X
live-on refl x = x

∧-true : ∀ a {b} → a ∧ b ≡ true → a ≡ true
∧-true true  _ = refl
∧-true false ()

-- A GOOD TREE'S LIVE CONNECT SUBSCRIBED ITS SOURCE ADMISSIBLY, its
-- binders read whole: its frozen entry is a lawful reading.  Under
-- a cut switched off a good tree asks only shape, so a connect there may
-- sit anywhere.
conn-ok : ∀ {R Γ X B} (k : CS Γ X) (o : St Γ X) (b : St (X ∷ Γ) B) (c : Ctx R Γ B) → liv c ≡ true → Good []ᴬ (plug c (connS k o b))
        → Admits k
conn-ok k o b c lv g = live-on lv (proj₂ (proj₂ (proj₂ (proj₂ (node-good c (connS k o b) g (λ ()) (λ ()))))))

-- An admissible entry read up to its end is lawful.
proper-lawful : ∀ {X H p} {t : EmissionSet X} → InvAt H p t → Lawful (Proper t)
proper-lawful I = record
  { real   = λ x → InvAt.real I (proj₁ x)
  ; func   = λ x x′ → InvAt.func I (proj₁ x) (proj₁ x′)
  ; flat   = λ x x′ → InvAt.flat I (proj₁ x) (proj₁ x′)
  ; proper = λ e y → proj₂ y (proj₁ e)
  }

-- A SCOPE SUBSCRIBED ADMISSIBLY, READ WHOLE, KEEPS THE INVARIANT.
scope-good : ∀ {Γ} (sc : Scope Γ) → ScopeOk sc → GoodEnv (full sc)
scope-good unbound        _         = λ ()
scope-good (binds o p sc) (ok , op) = good-cons (proper-lawful (inv-⟦⟧ o (full sc) (scope-good sc ok) (p ++ [ ix 1 ]) op)) (scope-good sc ok)

-- A BINDER SUBSCRIBED ADMISSIBLY READS LAWFULLY: every row of it one of
-- its frozen entry's own, before its end.
hot-lawful : ∀ {Γ X} (k : CS Γ X) {t : EmissionSet X} → Admits k
           → Lawful (λ q e → Proper (Frozen k) q e × (t q e ⊎ Closed k q e))
hot-lawful k (ok , op) = record
  { real   = λ x → Lawful.real L (proj₁ x)
  ; func   = λ x x′ → Lawful.func L (proj₁ x) (proj₁ x′)
  ; flat   = λ x x′ → Lawful.flat L (proj₁ x) (proj₁ x′)
  ; proper = λ e y → Lawful.proper L (proj₁ e) (proj₁ y)
  }
  where L = proper-lawful (inv-⟦⟧ (CS.src k) (full (CS.scope k)) (scope-good (CS.scope k) ok) (CS.connAt k ++ [ ix 1 ]) op)

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
env-good (inBody k o c) {s}                          lv g = good-cons (hot-lawful k (conn-ok k o s c lv g)) (env-good c lv g)
