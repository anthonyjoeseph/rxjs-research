-- The one denotational fact behind `readme-one-subscribe-one-batch`:
-- a SOURCE-FREE program (Exp 0) emits everything at its subscription
-- instant. No `srcE` exists without a `Fin 0`, so nothing ever fires
-- after the frame; every emission time equals t₀.
--
-- Proven as `close (⟦ e ⟧ em ρ t₀) ≤ t₀` (a static program closes at its
-- subscription instant), from which `BoundedBy t₀ (emits …)` follows by
-- the `bounded` field weakened along the close. Because t₀ is the least
-- time, "≤ t₀" is "= t₀", so every subscription time that arises stays t₀
-- and the induction never has to leave it — collapsing the usual two-sided
-- timing bookkeeping to one-sided `≤ t₀` bounds that compose through every
-- join's close-fold (maxCloses / concatAllClose / lastClose / exhaustClose).
module Formal-Verification.Readme-Semantics.Static where

open import Prelude
open import Shared-Types
open import Spec.MonotonicList
open import Spec.Batch-Simultaneous

module _ (em : Emissions 0) where

  -- a "static environment": every share slot is connected at t₀ and its
  -- history has already closed by t₀ (ρ₀ satisfies it; letShare preserves it)
  SEnv0 : Env → Set
  SEnv0 ρ = (i : ℕ) → (proj₁ (ρ i) ≡ t₀) × (timeLeq (close (proj₂ (ρ i))) t₀ ≡ true)

  ------------------------------------------------------------------
  -- time helpers

  timeMax-le : (x y : Time) → timeLeq x t₀ ≡ true → timeLeq y t₀ ≡ true
             → timeLeq (timeMax x y) t₀ ≡ true
  timeMax-le x y hx hy with timeLeq x y
  ... | true  = hy
  ... | false = hx

  t₀-max-eq : (u : Time) → timeLeq u t₀ ≡ true → u ≡ t₀
  t₀-max-eq (zero  , zero)  p = refl
  t₀-max-eq (zero  , suc b) p = true≢false (sym p)
  t₀-max-eq (suc a , b)     p = true≢false (sym p)

  -- take's manufactured close (nth emit / source close) stays ≤ t₀
  takeCloseL-le : (k : ℕ) (xs : TimedObs Val) (c : Time)
    → BoundedBy t₀ xs → timeLeq c t₀ ≡ true
    → timeLeq (takeCloseL t₀ k xs c) t₀ ≡ true
  takeCloseL-le zero          xs             c _            hc = timeLeq-refl t₀
  takeCloseL-le (suc n)       []             c bb[]         hc = hc
  takeCloseL-le (suc zero)    ((t′ , v) ∷ _) c (bb∷ le _)   hc = le
  takeCloseL-le (suc (suc n)) ((t′ , v) ∷ xs) c (bb∷ _ b)   hc = takeCloseL-le (suc n) xs c b hc

  ------------------------------------------------------------------
  -- every spawned inner arrives at t₀ and has itself closed by t₀

  InnersLE : TimedObs Inner → Set
  InnersLE []            = ⊤
  InnersLE ((a , d) ∷ os) =
    (a ≡ t₀) × (timeLeq (close (d t₀)) t₀ ≡ true) × InnersLE os

  -- each join's close-fold stays ≤ t₀ when its inners do
  maxCloses-le : (c : Time) (os : TimedObs Inner)
    → timeLeq c t₀ ≡ true → InnersLE os → timeLeq (maxCloses c os) t₀ ≡ true
  maxCloses-le c []            hc _              = hc
  maxCloses-le c ((a , d) ∷ os) hc (ha , hd , hos) rewrite ha =
    maxCloses-le (timeMax c (close (d t₀))) os (timeMax-le c (close (d t₀)) hc hd) hos

  concatAllClose-le : (r : Time) (os : TimedObs Inner)
    → r ≡ t₀ → InnersLE os → timeLeq (concatAllClose r os) t₀ ≡ true
  concatAllClose-le r []            req _              rewrite req = timeLeq-refl t₀
  concatAllClose-le r ((a , d) ∷ os) req (ha , hd , hos) rewrite req | ha =
    concatAllClose-le (close (d t₀)) os (t₀-max-eq (close (d t₀)) hd) hos

  lastClose-le : (c : Time) (os : TimedObs Inner)
    → timeLeq c t₀ ≡ true → InnersLE os → timeLeq (lastClose c os) t₀ ≡ true
  lastClose-le c []                hc _              = hc
  lastClose-le c ((a , d) ∷ [])     hc (ha , hd , _)   rewrite ha = hd
  lastClose-le c ((a , d) ∷ x ∷ os) hc (_ , _ , hos)  = lastClose-le c (x ∷ os) hc hos

  exhaustClose-le : (b : Time) (os : TimedObs Inner)
    → timeLeq b t₀ ≡ true → InnersLE os → timeLeq (exhaustClose b os) t₀ ≡ true
  exhaustClose-le b []            hb _              = hb
  exhaustClose-le b ((a , d) ∷ os) hb (ha , hd , hos) rewrite ha with timeLt t₀ b
  ... | true  = exhaustClose-le b os hb hos
  ... | false = exhaustClose-le (close (d t₀)) os hd hos

  ------------------------------------------------------------------
  -- the mutual induction over the source-free grammar

  close-le0   : (e : Exp 0) (ρ : Env) → SEnv0 ρ
              → timeLeq (close (⟦ e ⟧ em ρ t₀)) t₀ ≡ true
  emits-le0   : (e : Exp 0) (ρ : Env) → SEnv0 ρ
              → BoundedBy t₀ (emits (⟦ e ⟧ em ρ t₀))
  closeS-le0  : (ss : ExpS 0) (ρ : Env) → SEnv0 ρ
              → timeLeq (close (⟦ ss ⟧S em ρ t₀)) t₀ ≡ true
  innersLE-S  : (ss : ExpS 0) (ρ : Env) → SEnv0 ρ
              → InnersLE (emits (⟦ ss ⟧S em ρ t₀))
  innersLE-ofS : (es : List (Exp 0)) (ρ : Env) → SEnv0 ρ
              → InnersLE (map (λ d → (t₀ , d)) (⟦ es ⟧L em ρ))

  emits-le0 e ρ senv =
    boundedBy-weaken (close-le0 e ρ senv) (bounded (⟦ e ⟧ em ρ t₀))

  close-le0 (srcE ()) ρ senv
  close-le0 emptyE   ρ senv = timeLeq-refl t₀
  close-le0 (ofE vs) ρ senv = timeLeq-refl t₀
  close-le0 (shareE false i) ρ senv with ρ i | senv i
  ... | (tc ▹ o) | (e1 , e2) = timeMax-le t₀ (close o) (timeLeq-refl t₀) e2
  close-le0 (shareE true i) ρ senv with ρ i | senv i
  ... | (tc ▹ o) | (e1 , e2) rewrite e1 = timeMax-le t₀ (close o) (timeLeq-refl t₀) e2
  close-le0 (letShareE s b) ρ senv =
    close-le0 b (extendEnv (t₀ ▹ ⟦ s ⟧ em ρ t₀) ρ) senv′
    where senv′ : SEnv0 (extendEnv (t₀ ▹ ⟦ s ⟧ em ρ t₀) ρ)
          senv′ zero    = refl , close-le0 s ρ senv
          senv′ (suc i) = senv i
  close-le0 (mapE f e)  ρ senv = close-le0 e ρ senv
  close-le0 (takeE k e) ρ senv =
    takeCloseL-le k (emits (⟦ e ⟧ em ρ t₀)) (close (⟦ e ⟧ em ρ t₀))
      (emits-le0 e ρ senv) (close-le0 e ρ senv)
  close-le0 (scanE f z e) ρ senv = close-le0 e ρ senv
  close-le0 (mergeAllE ss) ρ senv =
    maxCloses-le (close (⟦ ss ⟧S em ρ t₀)) (emits (⟦ ss ⟧S em ρ t₀))
      (closeS-le0 ss ρ senv) (innersLE-S ss ρ senv)
  close-le0 (concatAllE ss) ρ senv =
    timeMax-le (close (⟦ ss ⟧S em ρ t₀)) (concatAllClose t₀ (emits (⟦ ss ⟧S em ρ t₀)))
      (closeS-le0 ss ρ senv)
      (concatAllClose-le t₀ (emits (⟦ ss ⟧S em ρ t₀)) refl (innersLE-S ss ρ senv))
  close-le0 (switchAllE ss) ρ senv =
    timeMax-le (close (⟦ ss ⟧S em ρ t₀))
      (lastClose (close (⟦ ss ⟧S em ρ t₀)) (emits (⟦ ss ⟧S em ρ t₀)))
      (closeS-le0 ss ρ senv)
      (lastClose-le (close (⟦ ss ⟧S em ρ t₀)) (emits (⟦ ss ⟧S em ρ t₀))
        (closeS-le0 ss ρ senv) (innersLE-S ss ρ senv))
  close-le0 (exhaustAllE ss) ρ senv =
    timeMax-le (close (⟦ ss ⟧S em ρ t₀)) (exhaustClose t₀ (emits (⟦ ss ⟧S em ρ t₀)))
      (closeS-le0 ss ρ senv)
      (exhaustClose-le t₀ (emits (⟦ ss ⟧S em ρ t₀)) (timeLeq-refl t₀) (innersLE-S ss ρ senv))

  closeS-le0 (ofS es)   ρ senv = timeLeq-refl t₀
  closeS-le0 (mapS f e) ρ senv = close-le0 e ρ senv

  innersLE-S (ofS es)   ρ senv = innersLE-ofS es ρ senv
  innersLE-S (mapS f e) ρ senv = go (emits (⟦ e ⟧ em ρ t₀)) (emits-le0 e ρ senv)
    where go : (xs : TimedObs Val) → BoundedBy t₀ xs
             → InnersLE (mapL (λ v u → ⟦ f v ⟧ em ρ u) xs)
          go []             bb[]        = tt
          go ((u , v) ∷ xs) (bb∷ le b) =
            t₀-max-eq u le , close-le0 (f v) ρ senv , go xs b

  innersLE-ofS []       ρ senv = tt
  innersLE-ofS (e ∷ es) ρ senv = refl , close-le0 e ρ senv , innersLE-ofS es ρ senv

  ------------------------------------------------------------------
  -- the export: everything an Exp 0 emits is at t₀

  emits-static : (e : Exp 0) → BoundedBy t₀ (emits (⟦ e ⟧ em ρ₀ t₀))
  emits-static e = emits-le0 e ρ₀ (λ i → refl , timeLeq-refl t₀)
