-- THE DERIVATION RELATIONS ARE FUNCTIONS, WHICH IS A CLAIM ABOUT THE
-- RELATIONS AND NOT ABOUT THE EVALUATOR.  `evaluate!` already hands a
-- run back together with its own derivation, so every statement proven
-- ABOUT that run is free of this question: it holds the derivation the
-- builder produced.  What is not free is the other direction — a claim
-- CONSTRUCTED as a derivation by hand, which is how a bounded-delivery
-- statement is naturally written, and which yields "some run does this"
-- until something says the relation admits one output only.
--
-- SO THE NAME IS CLAIMED BY MAIN RATHER THAN BY A CONSUMER, and that is
-- deliberate rather than a wiring workaround.  Its consumers are the
-- semantic claims that construct their own derivations, none of which
-- is written; a fact stated only when its first consumer arrives is a
-- fact the consumer's author has to discover, and the whole reason this
-- one is worth stating early is that it is invisible from the site that
-- needs it — the site typechecks either way and merely proves something
-- weaker than its name.
--
-- AND IT ANSWERS A QUESTION ONE TIER DOWN, WHICH IS THE OTHER HALF OF
-- ITS VALUE.  The protocol face's leaf quantifies over ANY subscribe
-- derivation and ANY drain derivation at its indices, while every
-- program the sampling harness has ever run exercised the builder's.
-- Whether those are the same set is exactly this statement.  Without it
-- the harness's coverage of that leaf has a whole axis it cannot reach
-- by generating more programs; with it, every sampled program becomes a
-- real instantiation.
--
-- WHY THE TWO LEAVES ARE THE HALVES THEY ARE.  The body is one match on
-- the run relation's sole constructor, so the split it needs is the
-- split that constructor already carries — the subscribe frame and the
-- drain.  Each leaf is then a determinacy statement about one family at
-- its own indices, and neither is a hypothesis of the other: the drain
-- half is applied only once the subscribe half has identified the state
-- both drains start from, which is what makes the second leaf's indices
-- well-formed rather than a coincidence of the call site.
--
-- WHAT THE LEAVES COST, stated plainly because it is the reason they
-- are leaves and not bodies: each is a structural recursion over one
-- derivation case-splitting the other, and the families are one mutual
-- ring, so the real proof is a simultaneous determinacy over the whole
-- ring rather than two separate inductions.  The arms that do not
-- follow from the head constructor are separated by equation premises
-- rather than by a search, which is what makes the grind mechanical —
-- and unverified, since nothing here has walked it.
module Verify-Determinacy where

open import Data.List using (_++_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Rx.Prim using (Tick; Fuel; Id)
open import Rx.Exp using (Ctx; Closed; Val; obs; []ᵉ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; root; sched-init; st-init)
open import Rx.Evaluator.Domain using (subscribeE⇓; drain⇓; evaluate⇓; eval-run)

------------------------------------------------------------------
-- THE TWO LEAVES.
------------------------------------------------------------------

postulate
  subscribeE-det :
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
      (b : Val Γ (obs u)) (κ : Path Γ lo u t) (id : Id) (now : Tick)
      (sched : Sched Γ) (st : EvalSt e)
      {r₁ r₂ : Stream Γ u × Sched Γ × EvalSt e} →
    subscribeE⇓ {e = e} b κ id now sched st r₁ →
    subscribeE⇓ {e = e} b κ id now sched st r₂ →
    r₁ ≡ r₂

  drain-det :
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      (fuel : Fuel) (nextId : Id) (sched : Sched Γ) (st : EvalSt e)
      {r₁ r₂ : Stream Γ t} →
    drain⇓ {e = e} fuel nextId sched st r₁ →
    drain⇓ {e = e} fuel nextId sched st r₂ →
    r₁ ≡ r₂

------------------------------------------------------------------
-- THE ASSEMBLY.  One match, because the run relation has one
-- constructor and it carries both halves as fields.
------------------------------------------------------------------

evaluate-deterministic :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ)
    {out₁ out₂ : Stream Γ t} →
  evaluate⇓ fuel e ins out₁ →
  evaluate⇓ fuel e ins out₂ →
  out₁ ≡ out₂
evaluate-deterministic fuel e ins (eval-run s₁ d₁) (eval-run s₂ d₂)
  with subscribeE-det (_ , e , []ᵉ) root 0 0 (sched-init e ins) (st-init e) s₁ s₂
... | refl = cong (_ ++_) (drain-det fuel 1 _ _ d₁ d₂)
