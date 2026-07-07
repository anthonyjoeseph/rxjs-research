-- The IMPLEMENTATION's batchSimultaneous: the machine.
--
-- It never holds the Emissions record. Everything here is a Mealy
-- machine built from Naive-Rx operators; the world reaches it one
-- input at a time through `run` (which lives in Shared-Types, not
-- here). Causality is structural.
--
-- Shape mirrors the TypeScript exactly:
--   compile         ~ building the Instantaneous pipeline (primitives.ts)
--   batchSimultaneousI ~ batchSimultaneous (batch-simultaneous.ts)
-- Discharging a postulate here = transcribing the corresponding
-- TypeScript definition into Naive-Rx operators, one .pipe() stage per
-- machine composition.
module Implementation.Batch-Simultaneous where

open import Prelude
open import Shared-Types
open import Implementation.Naive-Rx

------------------------------------------------------------------------
-- Instantaneous<A> (typescript/src/types.ts): an observable of
-- protocol emits

Inst : ℕ → Set → Set₁
Inst n A = RxObs n (Emit A)

------------------------------------------------------------------------
-- a stream of inner streams, defunctionalized to the two shapes the
-- grammar can build (exactly the InnerTemplate device of the TS model):
-- a static list of compiled inners, or a compiled template spawned per
-- outer value. Joins consume this; it never rides a wire, so everything
-- stays in Set₀ on the wires.

data Joinable (n : ℕ) : Set₁ where
  ofJ  : List₁ (Machine (In n) (Emit Val)) → Joinable n
  mapJ : (Val → Machine (In n) (Emit Val)) → Machine (In n) (Emit Val) → Joinable n

------------------------------------------------------------------------
-- the primitives (typescript/src/primitives.ts), one postulate each

postulate
  -- InstantSubject wired to source slot i (responds to `frame` with its
  -- sync flush + registration, to `next i v` with one emit)
  srcI        : {n : ℕ} → Fin n → Inst n Val
  emptyI      : {n : ℕ} → Inst n Val
  ofI         : {n : ℕ} {A : Set} → List A → Inst n A
  mapI        : {n : ℕ} {A B : Set} → (A → B) → Inst n A → Inst n B
  scanI       : {n : ℕ} → (Val → Val → Val) → Val → Inst n Val → Inst n Val
  takeI       : {n : ℕ} {A : Set} → ℕ → Inst n A → Inst n A
  -- share ref/binder (built on shareRx/connectRx; the flag marks the
  -- connecting ref, as in the grammar)
  shareRefI   : {n : ℕ} → Bool → Inst n Val → Inst n Val
  letShareI   : {n : ℕ} → Inst n Val → (Inst n Val → Inst n Val) → Inst n Val
  -- the four joins (built on mergeMapRx/concatMapRx/switchMapRx/
  -- exhaustMapRx + the SerialState holding-scan)
  mergeAllI   : {n : ℕ} → Joinable n → Inst n Val
  concatAllI  : {n : ℕ} → Joinable n → Inst n Val
  switchAllI  : {n : ℕ} → Joinable n → Inst n Val
  exhaustAllI : {n : ℕ} → Joinable n → Inst n Val

------------------------------------------------------------------------
-- the compiler: real structural recursion over the SHARED grammar,
-- holes only in the primitives above. ShEnv carries the letShare
-- bindings (de Bruijn, matching shareE's index).

ShEnv : ℕ → Set₁
ShEnv n = ℕ → Inst n Val

extendSh : {n : ℕ} → Inst n Val → ShEnv n → ShEnv n
extendSh sh ρ zero    = sh
extendSh sh ρ (suc i) = ρ i

compileE : {n : ℕ} → ShEnv n → Exp n → Inst n Val
compileS : {n : ℕ} → ShEnv n → ExpS n → Joinable n
-- inner lists compiled structurally (a `map` lambda would hide the
-- descent from the termination checker)
compileL : {n : ℕ} → ShEnv n → List (Exp n) → List₁ (Machine (In n) (Emit Val))

compileE ρ (srcE i)         = srcI i
compileE ρ emptyE           = emptyI
compileE ρ (ofE vs)         = ofI vs
compileE ρ (shareE f i)     = shareRefI f (ρ i)
compileE ρ (letShareE s b)  = letShareI (compileE ρ s) (λ sh → compileE (extendSh sh ρ) b)
compileE ρ (mapE f e)       = mapI f (compileE ρ e)
compileE ρ (takeE k e)      = takeI k (compileE ρ e)
compileE ρ (scanE f z e)    = scanI f z (compileE ρ e)
compileE ρ (mergeAllE ss)   = mergeAllI (compileS ρ ss)
compileE ρ (concatAllE ss)  = concatAllI (compileS ρ ss)
compileE ρ (switchAllE ss)  = switchAllI (compileS ρ ss)
compileE ρ (exhaustAllE ss) = exhaustAllI (compileS ρ ss)

compileS ρ (ofS es)   = ofJ (compileL ρ es)
compileS ρ (mapS f e) = mapJ (λ v → compileE ρ (f v)) (compileE ρ e)

compileL ρ []       = []
compileL ρ (e ∷ es) = compileE ρ e ∷ compileL ρ es

compile : {n : ℕ} → Exp n → Inst n Val
compile = compileE (λ _ → emptyI)

------------------------------------------------------------------------
-- the counting machine (typescript/src/batch-simultaneous.ts): decide
-- batch boundaries from init/close registration counts alone —
-- src.pipe(batchSync(), endWith(end), scan(step), mergeMap(flush))

postulate
  batchSimultaneousI : {n : ℕ} → Inst n Val → RxObs n (List Val)

------------------------------------------------------------------------
-- THE IMPLEMENTATION. A machine per program; the subscription log of
-- running it. Note what these two definitions DON'T take: the machine
-- never receives the Emissions.

impl-machine : {n : ℕ} → Exp n → Machine (In n) (List Val)
impl-machine e = batchSimultaneousI (compile e)

impl-batchSimultaneous : {n : ℕ} → Emissions n → Exp n → Subscription (List Val)
impl-batchSimultaneous em e = subscribeRx (impl-machine e) em
