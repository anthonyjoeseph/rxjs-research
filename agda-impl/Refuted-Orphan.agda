{-# OPTIONS --guardedness #-}

-- A `connect` whose source runs forever while its body is silent refutes
-- `run-rel`: `connectᴰ` drops the source's events, so the denotation
-- shows the body's silence; the engine keeps firing the source's timers,
-- so on every budget the run is cut before it can report silence.
module Refuted-Orphan where

open import Data.Empty using (⊥)
import Data.List
open Data.List using (List; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Properties using (n≤1+n; ≤-refl)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (false)
open import Data.Unit using (⊤; tt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (cold; connect)
open import denotation.MonotonicList using (ML; Burst; Burst∞; ML∞; at; close; quiet; stall; Pos; Time; ix; last) renaming (sub to subᴾ)
open import denotation.Order using (_⊑_; Shows; ShowsIn; at⁺; stall⁺; nil; quiet⁺; limit-least)
open import operation.AbstractObservable using (module Run)
open import operation.PureObservable using (PureObs; Pureᴾ; module Pure; same) renaming (_⊑_ to _≤ʷ_)
open import operation.Budget using (module Approx)
open import Adequacy using (module Link)

open Burst∞
open ML∞

beats : ℕ → ML ℕ
beats t = at t (close λ where .force → beats (suc t))

o : PureObs Data.List.[] ℕ
o = connect (cold (lift (beats 1))) (cold (lift quiet))

open Run (Pureᴾ ℕ) using (module Engine; done)
open Pure ℕ using (runPure; compileᴺ; stalls; runᴺ; loopᴺ; recorder; start; Res; res; State; Timer; observe; Pureᴿ)
open Approx ℕ using (runPure-mono)

-- The run, once subscribed, on any budget: one timer, the source's next frame.
sub : ℕ → Res Data.List.[] _
sub m = runᴺ (suc m) (suc m) (compileᴺ (suc m) o All.[] same recorder λ _ _ → done tt) same start

W = Res.reached (sub 0)
st₀ = Res.state (sub 0)

open import operation.PureObservable using (here; there)

frameOf : ML ℕ → Burst ℕ
frameOf (at _ b) = b
frameOf _        = stall stalls

-- The source's timer for its frame at t, due at d, set at e.
tm : ℕ → Time → Pos → Timer W
tm d t e = record { due = d ; sink = there here ; handle = here ; at′ = t ; from = e ; frame = frameOf (beats t) }

-- The run between turns: only the clock, the timer and the ghost move.
St : ℕ → ℕ → Time → Pos → Pos → State W
St c d t e q = record st₀ { clock = c ; timers = tm d t e ∷ Data.List.[] ; pos = q }

-- Nothing recorded, nothing ended, and the run cut.
Blank : ∀ {h} → Res h ⊤ → Set
Blank (res σ st v) = (v ≡ nothing) × (State.log st ≡ Data.List.[]) × (State.ended st ≡ false)

turns : ∀ b j (σ : Data.List.[] ≤ʷ W) c d t e q → Blank (loopᴺ (suc b) j σ (St c d t e q))
turns b zero    σ c d t e q = refl , refl , refl
turns b (suc j) σ c d t e q = turns b j σ d (d + (suc t ∸ t)) (suc t) (ix d ∷ subᴾ e ∷ last ∷ Data.List.[]) _

-- On every budget, the whole run.
runs : ∀ m → Blank (Engine.drive (Pureᴿ m) (runᴺ m m) (loopᴺ m m) (compileᴺ 5 o All.[]) recorder same start)
runs zero    = refl , refl , refl
runs (suc m) = turns m (suc m) _ 0 1 1 (ix 0 ∷ ix 1 ∷ last ∷ Data.List.[]) (ix 0 ∷ ix 1 ∷ Data.List.[])

cutAt0 : ML ℕ
cutAt0 = at 0 (stall stalls)

-- A cut shows nothing, however far it is read.
blank : ∀ {c is} → ShowsIn {ℕ} c (stall stalls) is → is ≡ Data.List.[]
blank nil        = refl
blank (stall⁺ p) = blank p

blank-⊑ : (r : Res Data.List.[] ⊤) → Blank r → observe r ⊑ cutAt0
blank-⊑ (res σ st v) (refl , l , e) s = go (State.log st) (State.ended st) l e s
  where
    go : ∀ lg en {is} → lg ≡ Data.List.[] → en ≡ false → Shows (Pure.frames ℕ lg (Pure.endOf ℕ en nothing (State.clock st))) is → Shows cutAt0 is
    go _ _ refl refl (at⁺ p) with blank p
    ... | refl = nil
    go _ _ refl refl nil = nil

bound : ∀ m → runPure m (compileᴺ 5 o All.[]) ⊑ cutAt0
bound m = blank-⊑ (Engine.drive (Pureᴿ m) (runᴺ m m) (loopᴺ m m) (compileᴺ 5 o All.[]) recorder same start) (runs m)

refuted : ⊥
refuted with limit-least (λ m → runPure-mono {n = 5} o (n≤1+n m) ≤-refl) bound
               (Link.run-rel ℕ (Link.fundamental ℕ 5 o Link.[]) quiet⁺)
... | at⁺ p with blank p
... | ()
