------------------------------------------------------------------
-- WHAT A WALK KEEPS, AND THE WALKER A PASS IS HANDED.  A pass folds
-- inners its outer subscribes, and an inner's subscribe is a walk, so
-- the pass needs one -- but the walk at an `of` is a pass.  The cycle
-- closes on the plain derivation: the walker handed in walks only
-- subscribes strictly smaller than a bound the caller's own derivation
-- sits under.
------------------------------------------------------------------
module Simulation.Walks where

open import Data.List    using ([])
open import Data.Nat     using (ℕ; _<_; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₂)

open import Rx.Exp       using (Ctx; Val; Env; Closed; Ren∈; renExp; renTm; evalWith; obs)
open import Rx.Evaluator using (Sched; EvalSt; Path)
open import Rx.Evaluator.Domain using (subscribeE⇓)
open import Rx.Evaluator.Reducible.Support using (Sound)
open import SExp.Syntax  using (SExp; Kinds; plainᵏ; emitᵗ)
open import SExp.Plain   using (plainExp)
open import SExp.Elaborate using (toInstEmit; plainᶜ⁺; frameᵛ)
open import Simulation.After using (module Kept)
open import Simulation.Catch using (Stamps)
open import Simulation.Stores using (Store; PathRel; EnvRel; LiveIf)
open import Simulation.Size using (sz-subscribeE)
open Kept using (After; module After)

module Walkers {n} {Γ : Ctx n} (κ : Kinds n) where

  -- THE FRAME A FORMER'S ELABORATION STAMPS ITS SUBSCRIBE WITH, read
  -- through the renaming it was closed under
  frameAt : ∀ {Θ Θ′} → Ren∈ (plainᶜ⁺ Θ) Θ′ → Env (plainᵏ Γ κ) Θ′ → ℕ
  frameAt {Θ} w ρ′ = evalWith (renTm (λ x → x) (λ x → x) w (frameᵛ {Γ = plainᵏ Γ κ} {[]} {[]} Θ)) ρ′

  module On {t} (ep : Closed Γ t) (ei : Closed (plainᵏ Γ κ) (emitᵗ t)) where

    -- WHAT ONE SUBSCRIBE KEEPS: what a pass keeps, from related stores
    -- and related sound paths, the impl's live unless spent, and the
    -- paths related again after; and
    -- what it sends lands where its path catches its frame `f`.
    --
    -- THE IMPL'S PATH STANDS `n` ABOVE THE PLAIN ONE'S FLOOR, as the roots
    -- do and a slot's stamped twin does: a read decides by its floor.
    -- REFUTED: `Refuted.Read-Floor`, read with
    --   `git show c2e60cb8:agda/evidence/refuted/Refuted/Read-Floor.agda`
    --   -- a read over unrelated floors.
    Walks : ∀ {u} → ℕ → Val (plainᵏ Γ κ) (obs (emitᵗ u)) → Val Γ (obs u) → Set
    Walks {u} f x′ x =
      ∀ {lo} {p : Path Γ lo u t} {q : Path (plainᵏ Γ κ) (n + lo) (emitᵗ u) (emitᵗ t)} {now}
        {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {rP rI}
      → (S : Store κ sP stP sI stI)
      → (pr : PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q)
      → Sound p sP stP → Sound q sI stI → LiveIf q (EvalSt.nodes stI)
      → subscribeE⇓ {e = ep} x p now sP stP rP → subscribeE⇓ {e = ei} x′ q now sI stI rI
      → Σ (After κ S rP rI) λ A
          → PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
          × Stamps κ f pr stI rI

    -- the same, for a plain subscribe under a bound
    Walks< : ∀ {u} → ℕ → ℕ → Val (plainᵏ Γ κ) (obs (emitᵗ u)) → Val Γ (obs u) → Set
    Walks< {u} N f x′ x =
      ∀ {lo} {p : Path Γ lo u t} {q : Path (plainᵏ Γ κ) (n + lo) (emitᵗ u) (emitᵗ t)} {now}
        {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {rP rI}
      → (S : Store κ sP stP sI stI)
      → (pr : PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q)
      → Sound p sP stP → Sound q sI stI → LiveIf q (EvalSt.nodes stI)
      → (dP : subscribeE⇓ {e = ep} x p now sP stP rP) → subscribeE⇓ {e = ei} x′ q now sI stI rI
      → sz-subscribeE dP < N
      → Σ (After κ S rP rI) λ A
          → PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
          × Stamps κ f pr stI rI

    -- the walk at one former, over any related environment
    Elab-Walks : ∀ {Θ u} → SExp Γ [] [] Θ u → Set
    Elab-Walks {Θ} s =
      ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel κ Θ w ρ′ ρ
      → Walks (frameAt w ρ′) (Θ′ , renExp (λ x → x) (λ x → x) w (toInstEmit κ s) , ρ′) (Θ , plainExp s , ρ)

    Elab-Walks< : ∀ {Θ u} → ℕ → SExp Γ [] [] Θ u → Set
    Elab-Walks< {Θ} N s =
      ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel κ Θ w ρ′ ρ
      → Walks< N (frameAt w ρ′) (Θ′ , renExp (λ x → x) (λ x → x) w (toInstEmit κ s) , ρ′) (Θ , plainExp s , ρ)

  -- A WALKER UNDER `N`: the walk at every former, of any subscribe
  -- smaller than `N`
  Walker : ∀ {t} (ep : Closed Γ t) (ei : Closed (plainᵏ Γ κ) (emitᵗ t)) → ℕ → Set
  Walker ep ei N = ∀ {Θ u} (s : SExp Γ [] [] Θ u) → On.Elab-Walks< ep ei N s
