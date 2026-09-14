------------------------------------------------------------------
-- DELETING THE ARM, WHICH IS NOT THE SAME JOB AS PROVING IT
-- UNREACHABLE.  A sketch — nothing here typechecks and nothing imports
-- it; it is deleted by the commit that makes the change.
------------------------------------------------------------------

-- TWO THINGS ARE CALLED KILLING THE DOOR AND THEY SCHEDULE OPPOSITELY
-- (Anthony).  PROVING THE REFUSING ARM UNREACHABLE is a claim about the
-- machine as it stands, and it must come LAST: the arm is reachable
-- today, `Refuted.Dry-Wrap` reaches it at three programs, so a proof
-- that it is not would be a proof of something false.  DELETING THE ARM
-- is the other job and it comes FIRST, because it is what makes the
-- first one true rather than what waits on it.
--
-- AND THE DELETION IS NOT A REMOVAL, IT IS A CHANGE OF WHAT THE
-- RECURSION IS OVER.  `Acc _≺_ τ` is threaded through all sixteen frame
-- signatures already, so the recursion is landed; what it is ordered by
-- is NUMERIC, so every edge that is not structural has to re-establish
-- the order at RUNTIME — and a runtime re-establishment is a decision
-- procedure, so it has a negative answer, so the clause must say
-- something when the answer comes back no.  That sentence is the whole
-- of the door.  Recurse on a DERIVATION instead and each edge's premise
-- is a sub-derivation handed in rather than a comparison performed: no
-- question is asked, so there is no negative answer, so there is no arm
-- and no marker.  No arm, no test, no seed.
--
-- AND KILLING THE DOOR AND INHABITING THE RELATION ARE ONE OBLIGATION,
-- NOT TWO (Anthony).  This is the part that was scheduled wrongly for a
-- structural reason rather than by a priority call: to BUILD a
-- derivation at a hop you must show the guard's positive branch is the
-- one taken, and that is precisely spending the report at the hop site.
-- So the arithmetic does not disappear — it moves out of the machine
-- and into the builder, where its failure is a proof obligation instead
-- of an emitted marker.

-- WHAT EACH OF THE THREE TESTS COSTS, AND IT IS NOT THE SAME PRICE.
-- The μ peel's fact is PROVEN and has been for as long as the peel has
-- existed; the hop's is the substitution report; the connect's is the
-- one genuinely new statement here.  That asymmetry is the finding: the
-- three arms have been treated as one obligation because they share a
-- marker, and only one of them is hard.
module Rx.Evaluator.Doorless where

open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; _∷_)
open import Data.Nat using (ℕ; suc; _<_; _≤_)
open import Data.Nat.Properties using (≤-trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (lookup)

open import Rx.Prim using (Tick; Id; Source; InstEvent)
open import Rx.Exp using (Ty; obs; Ctx; Val; Closed; syncSizeᵉ; unfoldμ; μᵉ)
open import Rx.Obs-Depth using (obsDepthᵉ; unfoldμ-no-deeper)
open import Rx.Sync-Size using (unfoldμ-shrinks)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (Tri; _≺_; ltU; ltR; ltS)
open import Rx.Evaluator using (AllOp; NodeId; Path; Sched; EvalSt;
  unconn; atSlot)

variable
  n  : ℕ
  lo : ℕ

------------------------------------------------------------------
-- THE THREE FACTS.  One per edge, each stated as the descent step the
-- deleted test used to return.
------------------------------------------------------------------

-- THE μ PEEL IS ALREADY FREE, AND NOBODY HAS COLLECTED IT.  The
-- machine asks whether the unfolding is synchronously smaller than a
-- number it was handed; `Rx.Sync-Size.unfoldμ-shrinks` says the
-- unfolding is smaller than the μ ITSELF, which is a fact about the
-- term and mentions no handed number at all.  Composed with the entry
-- invariant the edge is immediate — and the totality proof next door
-- ALREADY writes exactly this composition, inside a `⊥-elim` under the
-- test's negative arm.  The test is therefore doing no work in the one
-- place it is asked: what it buys is the right to be asked without
-- carrying `EntryOK`, and carrying `EntryOK` is what the builder does
-- and the machine must not.
μ-edge : ∀ {U r sz} {Γ : Ctx n} {u} (body : Closed (u ∷ Γ) u)
       → syncSizeᵉ (μᵉ body) ≤ sz
       → obsDepthᵉ (μᵉ body) ≤ r
       → (U , r , syncSizeᵉ (unfoldμ body)) ≺ (U , r , sz)
μ-edge body sz≤ _ = ltS (≤-trans (unfoldμ-shrinks body) sz≤)

-- and the peel's other component, which is not part of the edge but is
-- what keeps the invariant true at the unfolding
μ-entry : ∀ {r} {Γ : Ctx n} {u} (body : Closed (u ∷ Γ) u)
        → obsDepthᵉ (μᵉ body) ≤ r → obsDepthᵉ (unfoldμ body) ≤ r
μ-entry body = ≤-trans (unfoldμ-no-deeper body)

-- THE HOP'S FACT IS THE SUBSTITUTION REPORT, AND IT IS THE ONE THE
-- WHOLE TIER IS ABOUT.  What arrives at the hop is a runtime VALUE,
-- structurally unrelated to the term the clause stands at, so no
-- reading of the program supplies it directly — but where the value was
-- handed on by a `map-f` it is `applyFn fn v`, and
-- `Rx.Obs-Depth.Substitution.obsDepth-applyFn` prices that by the
-- TEMPLATE with nothing carried in.  The residue is a source's output
-- and a fold's, which is what the carried family is for and now the
-- only thing that needs it.
-- IT IS A PREMISE HERE AND NOT A POSTULATE, AND THE DIFFERENCE IS THE
-- WHOLE OF THE STATEMENT.  Quantified freely over the value and the
-- rank the claim is false at a glance — hand the clause anything deep
-- enough and it fails — so the report has to arrive from the SITE that
-- produced the value, which is what `HandedOK` is and what the carried
-- family delivers.  A free postulate here would be that refutation
-- written down as an axiom.
hop-edge : ∀ {U r s} {Γ : Ctx n} {u} (o : Val Γ (obs u))
         → obsDepthᵉ o < r
         → (U , obsDepthᵉ o , syncSizeᵉ o) ≺ (U , r , s)
hop-edge o drop = ltR drop

-- THE CONNECT'S FACT IS THE ONE GENUINELY NEW STATEMENT, AND IT IS
-- COUNTING RATHER THAN DEPTH.  Connecting slot `i` puts `i` into the
-- connected set, and the count the machine reads is over the slots NOT
-- in that set — so the reading drops by exactly the one slot, provided
-- `i` was not already there, which is the branch the caller took to
-- reach this clause at all.  Nothing about the program is read: this is
-- a fact about a list gaining an element it did not have.
postulate
  connect-drops : ∀ {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) (i : Fin n)
                → unconn sl (toℕ i ∷ cs) < unconn sl cs

-- and the edge, which needs the machine's own `U` to BE that count.
-- It is at the connect that the triple is re-seeded, so the equation is
-- the clause's own `refl` rather than something carried: the caller
-- hands over the definition and the component it hands over is the
-- definition's.
connect-edge : ∀ {r s r′ s′} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
                 (i : Fin n)
             → (unconn sl (toℕ i ∷ cs) , r′ , s′) ≺ (unconn sl cs , r , s)
connect-edge sl cs i = ltU (connect-drops sl cs i)
