-- ══════════════════════════════════════════════════════════════════
-- THE WALK'S ENTRY STRATIFICATION, IN ITS FREE FORM: two refutations
--
-- REFUTATIONS: machine-checked `… → ⊥`.  Each theorem here says a route
-- CANNOT work, and says it in a form the typechecker rechecks — unlike a
-- prose note, which decays silently.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Walk-Entry-Strat where

open import Data.Bool using (true; false)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; Val; Fn; natᵗ; obs; ofᵉ; emptyᵉ; input;
                         strmᵗ; nat̂; inputsBelowᵛ)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator using (Path; share-sink; _↠_; map-f; Sched; EvalSt;
                                sched-init; st-init)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?; pathFloor; pathStrat?)

------------------------------------------------------------------
-- THE WITNESS PROGRAM.  Two slots, because the defect needs a sink
-- whose floor is genuinely below an input that exists: `share-sink i`
-- reads its floor as `toℕ i`, so a one-slot context can only sink at
-- nought, where no input is available to sit above it.  Slot nought
-- carries an observable, which `isData` refuses to script, so it is a
-- `shared` def reading no input at all; slot one is data.
------------------------------------------------------------------

Γₛ : Ctx 2
Γₛ = obs natᵗ ∷ natᵗ ∷ []

d₀ : Closed Γₛ (obs natᵗ)
d₀ = ofᵉ (strmᵗ emptyᵉ ∷ [])

slₛ : Slots Γₛ
slₛ fzero        = shared d₀
slₛ (fsuc fzero) = shared emptyᵉ

progₛ : Closed Γₛ natᵗ
progₛ = ofᵉ (nat̂ 0 ∷ [])

schedₛ : Sched Γₛ
schedₛ = sched-init progₛ slₛ

stₛ : EvalSt progₛ
stₛ = st-init progₛ

-- A CAP WITH ROOM TO SPARE, so that satisfiability is not the thing in
-- question.  The receipt is taken at the INITIAL state of a real
-- program — the most reachable state there is — which is what stops the
-- reading below being about a state hand-built to fail.
cₛ : Caps
cₛ = caps 1000 1000 1000

okₛ : capsOK? cₛ schedₛ stₛ ≡ true
okₛ = refl

------------------------------------------------------------------
-- (1) THE PATH HALF.  `walk-path-strat` concludes `pathStrat? p ≡ true`
-- from a receipt naming only the caps, the schedule and the state, with
-- `p` quantified independently of all three.  So the statement is
-- equivalent to "if `capsOK?` is satisfiable at all, EVERY path is
-- stratified", and `okₛ` above settles the antecedent.
--
-- The counterexample is one frame over a sink: a `map` whose template
-- names input one, ending at slot nought, whose floor is nought.  The
-- telescope's own stratification cannot reach it — `shared` constrains
-- a slot's DEF, and a path's frames are not any slot's def.
------------------------------------------------------------------

badFn : Fn Γₛ [] [] [] natᵗ (obs natᵗ)
badFn = strmᵗ (input (fsuc fzero))

badPath : Path Γₛ natᵗ natᵗ
badPath = map-f badFn ↠ share-sink fzero

-- LOAD-BEARING: it would read `true` if `pathFloor` took the sink's
-- floor from the context size rather than from the sink's index, or if
-- `frameStrat?` let a `map` template through unread.
badPath-unstratified : pathStrat? badPath ≡ false
badPath-unstratified = refl

walk-path-strat-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
     (c : Caps) (p : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) →
     capsOK? c sched st ≡ true →
     pathStrat? p ≡ true) →
  ⊥
walk-path-strat-absurd h with h {e = progₛ} cₛ badPath schedₛ stₛ okₛ
... | ()

------------------------------------------------------------------
-- (2) THE VALUE HALF, AND IT IS INDEPENDENT.  `walk-vals-strat` reads
-- its floor off a path too, but the values are quantified separately
-- again — so it fails at a path that IS stratified, which is what makes
-- this a second finding rather than a restatement of the first.  A bare
-- sink is stratified; the value handed alongside it is an observable
-- naming input one, and `Val Γ (obs t)` is an arbitrary closed
-- expression, so nothing about the telescope constrains it.
------------------------------------------------------------------

goodPath : Path Γₛ (obs natᵗ) natᵗ
goodPath = share-sink fzero

-- LOAD-BEARING: the row is only a separation while this reads `true`.
goodPath-stratified : pathStrat? goodPath ≡ true
goodPath-stratified = refl

badVal : Val Γₛ (obs natᵗ)
badVal = input (fsuc fzero)

-- LOAD-BEARING: it would read `true` at any input index below the
-- sink's, which is why the sink is taken at nought.
badVal-unstratified : all (inputsBelowᵛ (pathFloor goodPath) (obs natᵗ)) (badVal ∷ []) ≡ false
badVal-unstratified = refl

walk-vals-strat-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
     (c : Caps) (p : Path Γ u t) (vals : List (Val Γ u))
     (sched : Sched Γ) (st : EvalSt e) →
     capsOK? c sched st ≡ true →
     all (inputsBelowᵛ (pathFloor p) u) vals ≡ true) →
  ⊥
walk-vals-strat-absurd h
  with h {e = progₛ} cₛ goodPath (badVal ∷ []) schedₛ stₛ okₛ
... | ()
