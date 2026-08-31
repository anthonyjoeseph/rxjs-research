-- ══════════════════════════════════════════════════════════════════
-- ONE CHAIN DOES NOT LEAVE THE STORE WHERE IT FOUND IT.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  A round's descent is bounded by a ceiling
-- stated ONCE, at a store bound the whole round shares, and the walk
-- over the chains spends it at every one of them.  That only closes if
-- a chain's own step leaves the bound intact: the chains after the
-- first run on states their predecessors moved.
--
-- WHY IT LOOKED RIGHT.  The other two ends of a cascade preserve the
-- measure outright -- the latch does not take the `Sched` at all and
-- the finish only shortens the lists the measure folds over -- so the
-- shape reads as the third instance of a pattern that already holds
-- twice.
--
-- WHERE IT BREAKS.  The walk is precisely the end that can deepen
-- something, which the growth statement one level up already says in
-- the other direction: it prices a cascade at a FACTOR times the store
-- plus an increment, not at the store.  A chain subscribes what its
-- delivery reaches and installs the nodes for it, and both the live
-- fold and the node fold are places the store measure reads.
--
-- THE WITNESS is `progU 8 6` at the two-slot vocabulary `insF 1 2 2`,
-- whose second slot is HOT, read at the SECOND cascade -- the same
-- instant the round's own rows are read at.  Nine before the chain,
-- sixteen after.  It is not a corner: two further families in the same
-- corpus grow by one each at the same instant, so what fails is the
-- preservation and not a margin.
--
-- WHAT THIS DOES NOT SHOW.  Nothing here touches the round's ceiling,
-- which holds at every instant the corpus reaches and widens as it
-- goes.  What dies is the plan to carry that ceiling across the chains
-- by a store bound the chains preserve; the growth has to be priced.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Chain-Step-Store where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ)
open import Rx.Prim using (gasPad; g0)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next;
         cascade; cascadeLatch; chainStep; chainsOf)
open import Rx.Slots using (Slots)

open import Refuted.Demand-Programs using (Γ₂; progU; insF; sucGU)
open import Verify-Budget-Sufficient.Nest-Store using (storeNestMax)

prog : Closed Γ₂ natᵗ
prog = progU 8 6

slots : Slots Γ₂
slots = insF 1 2 2

sub : Sched Γ₂ × EvalSt prog
sub = let r = subscribeE (gasPad (sucGU 1 2 2 8 6) g0) prog root 0 0
                         (sched-init prog slots) (st-init prog)
      in proj₁ (proj₂ r) , proj₂ (proj₂ r)

-- the state the FIRST cascade leaves, which is the instant the round's
-- own ceiling is read at
after1 : Sched Γ₂ × EvalSt prog
after1 with sched-next (proj₁ sub)
... | inj₁ _        = sub
... | inj₂ (a , sd) =
  let r = cascade a 1 sd (proj₂ sub)
  in proj₁ (proj₂ r) , proj₂ (proj₂ r)

-- the store either side of the round's FIRST chain, both read off
-- states the evaluator reached
row : ℕ × ℕ
row with sched-next (proj₁ after1)
... | inj₁ _        = 0 , 0
... | inj₂ (a , sd) with chainsOf a (proj₂ after1)
...   | []            = 0 , 0
...   | (rid , c) ∷ _ =
        let st₀ = cascadeLatch a (proj₂ after1)
            r   = chainStep 2 a c sd st₀
        in storeNestMax sd st₀
         , storeNestMax (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

-- THE FIGURES, PINNED.  Spelled out so that any repair moving either
-- side fails here, naming the number, rather than quietly turning the
-- crossing into an equality
before≡9 : proj₁ row ≡ 9
before≡9 = refl

after≡16 : proj₂ row ≡ 16
after≡16 = refl

chain-step-store-absurd : proj₂ row ≤ proj₁ row → ⊥
-- `16 ≤ᵇ 9` reduces to `false`, so `T` of it IS the empty type
chain-step-store-absurd h = ≤⇒≤ᵇ h
