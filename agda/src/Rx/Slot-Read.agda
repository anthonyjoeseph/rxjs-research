------------------------------------------------------------------
-- THE SLOT ENVIRONMENT: the ψ that `Rx.Hop-Depth`'s input clause was
-- parameterised FOR.
--
-- `rdᵉ` reads ψ at `input i` and nowhere else, so every consumer of the
-- reading has to say which environment it means.  The constant-zero one
-- is FALSE rather than merely coarse: an obs-typed shared slot's def
-- emits values of positive hop, and a subscription connecting to that
-- slot receives them, so zeroing the share boundary breaks at the first
-- flattener over an input.  What is built here is the honest one.
--
-- A SLOT CARRIES THE DEF'S WHOLE TRIPLE.  A reference stands for the
-- def itself, so what it reports is what the def delivers, what ONE
-- delivered value of it delivers, and how deep it is.  Reporting only
-- the pair a plug takes re-invents the middle component from the top
-- count, and a def delivering one observable of three values then reads
-- as delivering one value of one — a fold above the flattener iterates
-- once where the run refolds three times.
--
-- A SCRIPTED SLOT'S OTHER TWO COMPONENTS ARE ZERO BY THE SYNTAX, AND
-- ONLY THE COUNT IS A CHOICE.  Its payload type satisfies `isData`, so
-- no emission of its can hold an observable and the per-value count and
-- the hop are forced rather than picked.  The count is what a fold
-- sourcing from the slot refolds over, so it is the one component that
-- reaches the hop at all — through the flattener's product and the
-- fold's refold count — which is why it is priced at everything the
-- source is scheduled to deliver and not at the subscribe frame alone.
--
-- IT IS WELL DEFINED BECAUSE THE TELESCOPE IS STRATIFIED.  `Rx.Slots`
-- carries a side condition saying a shared def reads only inputs at
-- strictly smaller indices, so slot k's reading is computable by
-- recursion on k: `ψAt` builds the stage-k environment — correct below
-- k, zero at and above it — and `slotRd` reads each slot off its own
-- stage.  That side condition is in the syntax for this and discharges
-- by unification at every concrete program.
--
-- THE FIXPOINT HALF IS WHAT A CONNECT SPENDS.  The staged reading at a
-- shared slot IS the def's reading under the FULL environment, and that
-- equation is what turns the walk's input clause — which knows only
-- `ψ i` — into a statement about the def the connect is about to
-- subscribe.  It rests on `Rx.Rd-Slot-Cong` and on the staging lemma
-- below, and on no postulate.
--
-- AND THE STAGING HAS BEEN INSTANTIATED, both ways over a def delivering
-- one observable of three values and at a share holding a recursion, by
-- rows `git show 8c6fc8d:agda/evidence/probed/Probed/Slot-Priced.agda`
-- holds.  Their boundary is ONE SLOT — a second stage is the same clause
-- again — and nothing reaching a scripted slot, whose zero components
-- the syntax forces.
------------------------------------------------------------------
module Rx.Slot-Read where

open import Data.Nat  using (ℕ; zero; suc; _+_; _≡ᵇ_; _<ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; <ᵇ⇒<; <⇒<ᵇ; ≤∧≢⇒<; ≤-pred)
open import Data.Fin  using (Fin; toℕ)
open import Data.List using (length)
open import Data.Vec  using (lookup)
open import Data.Bool using (true; false; T; if_then_else_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; sym; subst)

open import Rx.Prim       using (ObservableInput; hot; cold)
open import Rx.Exp        using (Ctx; Closed; inputsBelowᵉ)
open import Rx.Slots      using (Slot; Slots; scripted; shared)
open import Rx.Hop-Depth  using (Rd₃; ε; rdᵉ)
open import Rx.Rd-Slot-Cong using (rd-ψ-congᵉ)

-- how many values an input can ever hand a subscription
--
-- IT COUNTS THE SCHEDULED TAIL, AND THE SUBSCRIBE FRAME IS NOT THE
-- QUANTITY DOWNSTREAM WANTS.  A count priced at the SYNCHRONOUS prefix
-- alone reads a source whose values all arrive late as delivering
-- nothing, and the zero does not stay local: `flatten` multiplies the
-- chain's count through it, and a fold above reads the product as how
-- many times it refolds — so a term over such a slot is read as if the
-- arriving values were never going to come.  `Probed.Entry-Fit` stands
-- at exactly that slot — an empty prefix and one late value — where the
-- frame-only count made the fit at the door FALSE and this one leaves
-- it holding by a margin that widens with the deliveries.
--
-- A HOT SOURCE IS COUNTED THE SAME WAY AND THE ANSWER IS AN UPPER
-- BOUND, WHICH IS THE DIRECTION EVERY CONSUMER NEEDS.  It is anchored
-- at tick zero rather than at the subscription, so a subscription
-- joining late receives a SUFFIX of this list and never more than it;
-- a cold one is re-anchored per subscribe and receives all of it.  So
-- one clause is exact and the other over-approximates, and no consumer
-- can tell the difference, because the reading stands on the right of
-- every comparison that spends it.
emitsOf : ∀ {A : Set} → ObservableInput A → ℕ
emitsOf (hot async)        = length async
emitsOf (cold sync async)  = length sync + length async

-- one slot's reading, given an environment for the inputs its def may
-- read
slotRdD : ∀ {n} {Γ : Ctx n} {k t} (ψ : Fin n → Rd₃) → Slot Γ k t → Rd₃
slotRdD ψ (scripted src) = emitsOf src , 0 , 0
slotRdD ψ (shared d)     = rdᵉ ψ ε d

-- the stage-k environment: the true readings at indices < k, zero
-- above.  Structural on k — this is the recursion stratification pays
-- for.
ψAt : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (k : ℕ) → Fin n → Rd₃
ψAt sl zero    i = 0 , 0 , 0
ψAt sl (suc k) i =
  if toℕ i ≡ᵇ k then slotRdD (ψAt sl k) (sl i)
                else ψAt sl k i

-- THE ENVIRONMENT: each slot read off its own stage
slotRd : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) → Fin n → Rd₃
slotRd sl i = slotRdD (ψAt sl (toℕ i)) (sl i)

-- THE STAGE IS ALREADY RIGHT WHERE IT CLAIMS TO BE: below k, `ψAt`'s
-- answer IS the full environment's.
--
-- Induction on k.  At zero the guard is uninhabited and the statement
-- is vacuous.  At `suc k` the stage branches on `toℕ j ≡ᵇ k`: on TRUE
-- both sides are the same `slotRdD` once the index equality is
-- transported, since `slotRd` reads stage `toℕ j` and the stage here is
-- `k`; on FALSE the guard gives `toℕ j ≤ k` and the branch gives
-- `toℕ j ≢ k`, so the stage delegates one level down and the induction
-- hypothesis closes it.
ψAt-agrees : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (k : ℕ)
  (j : Fin n) → T (toℕ j <ᵇ k) →
  ψAt sl k j ≡ slotRd sl j
ψAt-agrees sl zero    j ()
ψAt-agrees sl (suc k) j lt with toℕ j ≡ᵇ k in eqb
... | true  =
  cong (λ m → slotRdD (ψAt sl m) (sl j))
       (sym (≡ᵇ⇒≡ (toℕ j) k (subst T (sym eqb) tt)))
... | false =
  ψAt-agrees sl k j
    (<⇒<ᵇ (≤∧≢⇒< (≤-pred (<ᵇ⇒< (toℕ j) (suc k) lt))
                 (λ e → subst T eqb (≡⇒≡ᵇ (toℕ j) k e))))

-- THE FIXPOINT, assembled: a shared slot's def reads the SAME at its
-- own stage as under the full environment — which is the equation a
-- connect charges against, since what it is about to subscribe is the
-- def while what its invariant carries is the slot's reading.
--
-- IT IS STATED AT THE DEF AND NOT AT THE SLOT, and that is what makes
-- it spendable.  A walk reaching a slot reference matches the telescope
-- before it can name the def at all, so by the time the obligation
-- exists the caller's reading has ALREADY reduced through `slotRdD` to
-- the def at the stage.  An equation whose left side is `slotRd sl i`
-- would then have to be bridged back across that very match, at the one
-- site that cannot see it.  The side condition is what is really
-- consumed here; the telescope equation is not needed and is not taken.
slotRd-fix : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (i : Fin n)
  (d : Closed Γ (lookup Γ i)) → T (inputsBelowᵉ (toℕ i) d) →
  rdᵉ (ψAt sl (toℕ i)) ε d ≡ rdᵉ (slotRd sl) ε d
slotRd-fix sl i d ok =
  rd-ψ-congᵉ (toℕ i) ε (ψAt-agrees sl (toℕ i)) d ok
