{-# OPTIONS --guardedness #-}

-- CONTENT: every observer is delivered its subtree's meaning, as a set.
-- Sortedness (`adequacy.Sorted`) says nothing of WHAT arrives; this says
-- nothing of the ORDER, so neither proof reads the other.
--
-- The PER-KERNEL CONTRACT: a kernel handed an input honest to a meaning
-- is honest to its operator's meaning over it.  Each contract reads one
-- kernel and one operator's `MonotonicList` function; the tree's honesty
-- is their composition (`compile-honest`), a body.
--
-- HISTORIES, NOT STEPS: honesty compares what an observer has been
-- delivered, as a whole, with the meaning observed where it subscribed.
-- No step of the machine is matched to a step of anything.
module adequacy.Content where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)

import Tree as T
open import Tree using (Obs)
open import denotation.MonotonicList using (MonotonicList)
open import denotation.Denote using (⟦_⟧; DenEnv)
open import operation.AbstractObservable using (module Run)
open import operation.PureObservable using (PureObs; Pureᴾ)

module Honesty (R : Set) where
  open Run (Pureᴾ R) using (Subscribe; Env; compile; emptyᴷ; ofᴷ; mapᴷ; scanᴷ; takeWhileᴷ; flatMapᴷ; connectᴷ; joinᴷ; via; startCold)

  postulate
    -- A subscription honest to a meaning: whatever observer it is handed,
    -- subscribed at whatever position `p`, the machine's deliveries to it
    -- are alike `observe m p` as a set, cut where its subscriber left.
    -- A postulated TYPE, to be defined over the machine's histories.
    Honest : ∀ {A w} → Subscribe A w → MonotonicList A → Set₁

    -- An environment honest to a denotational one: each `connect` in
    -- scope's joiners fed the hot run its source's meaning names.
    HonestEnv : ∀ {Γ w} → Env Γ w → DenEnv Γ → Set₁

  postulate
    -- THE PER-KERNEL CONTRACT, one kernel at a time.
    coldᴷ-honest      : ∀ {Γ A w} c (δ : DenEnv Γ) → Honest {A} {w} (via (startCold c)) (⟦ T.cold c ⟧ δ)
    emptyᴷ-honest     : ∀ {Γ A w} (δ : DenEnv Γ) → Honest {A} {w} emptyᴷ (⟦ T.empty ⟧ δ)
    ofᴷ-honest        : ∀ {Γ A w} xs (δ : DenEnv Γ) → Honest {A} {w} (ofᴷ xs) (⟦ T.of xs ⟧ δ)
    mapᴷ-honest       : ∀ {Γ A B w} f {s} (o : PureObs Γ A) δ → Honest {A} {w} s (⟦ o ⟧ δ) → Honest {B} (mapᴷ f s) (⟦ T.map f o ⟧ δ)
    scanᴷ-honest      : ∀ {Γ A B w} f z {s} (o : PureObs Γ A) δ → Honest {A} {w} s (⟦ o ⟧ δ) → Honest {B} (scanᴷ f z s) (⟦ T.scan f z o ⟧ δ)
    -- The contract's risk: `takeWhile` completes at the value that fails,
    -- and rxjs delivers that completion before the source's next value.
    takeWhileᴷ-honest : ∀ {Γ A w} i p {s} (o : PureObs Γ A) δ → Honest {A} {w} s (⟦ o ⟧ δ) → Honest (takeWhileᴷ i p s) (⟦ T.takeWhile i p o ⟧ δ)
    flatMapᴷ-honest   : ∀ {Γ A B w} op {f s} (g : A → PureObs Γ B) (o : PureObs Γ A) δ
                      → (∀ a → Honest {B} {w} (f a) (⟦ g a ⟧ δ)) → Honest {A} {w} s (⟦ o ⟧ δ)
                      → Honest (flatMapᴷ op f s) (⟦ T.flatMap op g o ⟧ δ)
    -- `connect`: its joiners fed one hot run, the source's, from where
    -- the body subscribed it.
    connectᴷ-honest   : ∀ {Γ A B w} {s b} (o : PureObs Γ A) (c : PureObs (A ∷ Γ) B) δ
                      → Honest {A} {w} s (⟦ o ⟧ δ)
                      → (∀ {v} σ st r → Honest {B} {v} (b σ st) (⟦ c ⟧ (r ∷ δ)))
                      → Honest (connectᴷ s b) (⟦ T.connect o c ⟧ δ)
    joinᴷ-honest      : ∀ {Γ A w} st i (δ : DenEnv Γ) → Honest {A} {w} (joinᴷ st) (⟦ T.connected i ⟧ δ)
    deferᴷ-honest     : ∀ {Γ A w} l (e : Env Γ w) δ → HonestEnv e δ → Honest {A} (compile (T.defer l) e) (⟦ T.defer l ⟧ δ)

  -- THE ASSEMBLY: every compiled tree honest to its meaning, kernel by
  -- kernel.
  compile-honest : ∀ {Γ A w} (o : PureObs Γ A) (e : Env Γ w) δ → HonestEnv e δ → Honest (compile o e) (⟦ o ⟧ δ)
  compile-honest (T.cold c)          e δ he = coldᴷ-honest c δ
  compile-honest T.empty             e δ he = emptyᴷ-honest δ
  compile-honest (T.of xs)           e δ he = ofᴷ-honest xs δ
  compile-honest (T.map f s)         e δ he = mapᴷ-honest f s δ (compile-honest s e δ he)
  compile-honest (T.scan f z s)      e δ he = scanᴷ-honest f z s δ (compile-honest s e δ he)
  compile-honest (T.takeWhile i p s) e δ he = takeWhileᴷ-honest i p s δ (compile-honest s e δ he)
  compile-honest (T.flatMap op f s)  e δ he = flatMapᴷ-honest op f s δ (λ a → compile-honest (f a) e δ he) (compile-honest s e δ he)
  compile-honest (T.connect s b)     e δ he = connectᴷ-honest s b δ (compile-honest s e δ he) λ σ st r → compile-honest b _ (r ∷ δ) _
  compile-honest (T.connected i)     e δ he = joinᴷ-honest _ i δ
  compile-honest (T.defer l)         e δ he = deferᴷ-honest l e δ he

  postulate
    -- The empty environments are honest to each other.
    honest-[] : ∀ {w} → HonestEnv {[]} {w} _ []
