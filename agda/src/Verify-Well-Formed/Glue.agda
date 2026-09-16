-- THE COMPOSITION LAWS THE PROTOCOL ARGUMENT RUNS ON, AND ALL OF THEM
-- ARE PROVEN.  A run's emit stream is built by concatenation — a
-- subscribe frame's burst in front of whatever the drain produces, and
-- inside the drain one cascade's emits in front of the rest — while the
-- automaton is a left fold.  So every assembly in this face has the
-- same shape: two runs meeting at a state, and a law saying the fold
-- over the concatenation is the two folds composed.
--
-- WHY THE LAW IS STATED THROUGH A BIND RATHER THAN OVER TWO `just`s.
-- The general equation holds unconditionally, failure included, and is
-- one induction on the front list; the `just`-to-`just` form every call
-- site actually wants is then a corollary rather than a second
-- induction.  Stating only the corollary would have meant re-proving
-- the induction the first time a site needed the failing case.
--
-- AND ACCEPTANCE IS SEPARATED FROM THE FOLD ON PURPOSE.  Well-formedness
-- is the fold's result passed through a FINAL check, so a bookkeeping
-- argument that has carried a state to the end of the stream still owes
-- one fact — that the last instant settled — and nothing about the fold
-- supplies it.  Keeping that step its own named lemma is what stops the
-- final obligation from being absorbed into a preservation statement,
-- where it would be invisible.
module Verify-Well-Formed.Glue where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Rx.Prim using (InstEmit)
open import Rx.Protocol using (ProtocolSt; stepProtocol; runProtocol; paidUp;
  checkFinal; Accepted; accepted)

_>>=ᴹ_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just a  >>=ᴹ f = f a
nothing >>=ᴹ f = nothing

runProtocol-++ : ∀ {A} (S : ProtocolSt) (xs ys : List (InstEmit A)) →
  runProtocol S (xs ++ ys)
    ≡ (runProtocol S xs >>=ᴹ λ S′ → runProtocol S′ ys)
runProtocol-++ S []       ys = refl
runProtocol-++ S (x ∷ xs) ys with stepProtocol x S
... | just S′ = runProtocol-++ S′ xs ys
... | nothing = refl

run-++-just : ∀ {A} (S : ProtocolSt) (xs ys : List (InstEmit A))
              {S₁ S₂ : ProtocolSt} →
  runProtocol S xs ≡ just S₁ → runProtocol S₁ ys ≡ just S₂ →
  runProtocol S (xs ++ ys) ≡ just S₂
run-++-just S xs ys {S₁} e₁ e₂ =
  trans (runProtocol-++ S xs ys)
        (trans (cong (λ m → m >>=ᴹ (λ S′ → runProtocol S′ ys)) e₁) e₂)

acceptPaid : (S : ProtocolSt) → paidUp S ≡ true → Accepted (checkFinal (just S))
acceptPaid S eq rewrite eq = accepted
