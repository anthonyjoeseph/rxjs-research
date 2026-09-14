------------------------------------------------------------------
-- THE ORDER, AFTER IT LEFT THE MACHINE.  `Rx.Evaluator` performs no
-- comparison and carries no witness; the three edges it used to
-- re-establish at runtime are stated here as facts, and whoever builds
-- a derivation spends them.
------------------------------------------------------------------

-- WHY THE ORDER IS HERE AND NOT THERE, AND IT IS NOT A FILING CHOICE.
-- What the recursion is ordered by is NUMERIC, so every edge that is
-- not structural has to re-establish the order at RUNTIME — and a
-- runtime re-establishment is a decision procedure, so it has a
-- negative answer, so the clause must say something when the answer
-- comes back no.  That sentence is the whole of the door.  A premise
-- handed to a BUILDER is the same arithmetic with no negative answer to
-- give: a clause nobody can build is a run that does not exist, where a
-- comparison that comes back false is a marker on the output.
--
-- AND KILLING THE DOOR AND INHABITING THE RELATION ARE ONE OBLIGATION,
-- NOT TWO (Anthony).  To BUILD a derivation at a hop you must show the
-- guard's positive branch is the one taken, and that is precisely
-- spending the report at the hop site.  So the arithmetic did not
-- disappear — it moved, and its failure is now an unproven obligation
-- rather than an emitted marker.

-- WHAT EACH OF THE THREE TESTS COSTS, AND IT IS NOT THE SAME PRICE.
-- The μ peel's fact is PROVEN and has been for as long as the peel has
-- existed; the hop's is the substitution report; the connect's is the
-- one genuinely new statement here.  That asymmetry is the finding: the
-- three arms were treated as one obligation because they shared a
-- marker, and only one of them is hard.
module Rx.Evaluator.Doorless where

open import Data.Bool using (false)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _<_; _≤_; _⊔_)
open import Data.Nat.Properties using (≤-trans)
open import Data.Product using (_,_)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim using (Source)
open import Rx.Exp using (obs; Ctx; Exp; Val; Closed; syncSizeᵉ; unfoldμ; μᵉ)
open import Rx.Obs-Depth using (obsDepthᵉ; unfoldμ-no-deeper)
open import Rx.Sync-Size using (unfoldμ-shrinks)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (Tri; _≺_; ltU; ltR; ltS; ≺-wellFounded)
open import Rx.Evaluator using (unconn; memberSource)

variable
  n : ℕ

------------------------------------------------------------------
-- THE THREE FACTS.  One per edge, each stated as the descent step the
-- deleted test used to return.
------------------------------------------------------------------

-- THE μ PEEL IS FREE, AND THE TEST WAS NEVER BUYING ANYTHING.  What it
-- asked was whether the unfolding is synchronously smaller than a
-- number it was handed; `Rx.Sync-Size.unfoldμ-shrinks` says the
-- unfolding is smaller than the μ ITSELF, which is a fact about the
-- term and mentions no handed number at all.  Composed with the entry
-- invariant the edge is immediate.  So what the test bought was the
-- right to be asked without carrying `EntryOK` — and carrying
-- `EntryOK` is what a builder does and what a plain rxjs pipeline
-- cannot, which is why the invariant is here and not there.
μ-edge : ∀ {U r sz} {Γ : Ctx n} {u} (body : Exp Γ (u ∷ []) [] [] u)
       → syncSizeᵉ (μᵉ body) ≤ sz
       → obsDepthᵉ (μᵉ body) ≤ r
       → (U , r , syncSizeᵉ (unfoldμ body)) ≺ (U , r , sz)
μ-edge body sz≤ _ = ltS (≤-trans (unfoldμ-shrinks body) sz≤)

-- and the peel's other component, which is not part of the edge but is
-- what keeps the invariant true at the unfolding
μ-entry : ∀ {r} {Γ : Ctx n} {u} (body : Exp Γ (u ∷ []) [] [] u)
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
-- DEAD ROUTE: giving `thru-outer` a rank FIELD ρ, set at install, so
--   the hop re-seeds at a figure the machine owns and its drop is
--   `ρ < suc ρ`.  It does close the arm without a premise, and it
--   relocates the residue to the *All install, where it is a claim about
--   a TERM.  It is dead because it invents a fourth currency for a
--   question three refutations have already priced: the family's axis
--   set is settled, so a mechanism whose whole content is avoiding the
--   family buys a new shelf of statements nothing has instantiated, in
--   place of five whose regions are known.  It is also strictly weaker
--   about the run — ρ is not claimed to dominate the inners, so a wrong
--   ρ is a silent re-seeding rather than a failed obligation.
-- DEAD ROUTE: threading `HandedOK (o ∷ [])` into `subscribeInner` as an
--   ARGUMENT and spending it for `ltR`.  It makes the evaluator a
--   proof-carrying function: every caller up to `evaluate` acquires an
--   obligation, and the impl stops mirroring anything a plain rxjs
--   pipeline can do.  That is the one line this repo does not cross, and
--   it is what fixes the SHAPE of the totality cutover: the knot is tied
--   ABOVE this module, where a premise costs a proof obligation rather
--   than an argument, so `evaluate` keeps the type a pipeline has.
hop-edge : ∀ {U r s} {Γ : Ctx n} {u} (o : Val Γ (obs u))
         → obsDepthᵉ o < r
         → (U , obsDepthᵉ o , syncSizeᵉ o) ≺ (U , r , s)
hop-edge o drop = ltR drop

-- THE CONNECT'S FACT IS THE ONE GENUINELY NEW STATEMENT, AND IT IS
-- COUNTING RATHER THAN DEPTH.  Connecting slot `i` puts `i` into the
-- connected set, and the count is over the slots NOT in that set — so
-- it drops by exactly the one slot, provided `i` was not already
-- there, which is the branch the caller takes to reach the clause at
-- all.  Nothing about the program is read: this is a fact about a list
-- gaining an element it did not have.
--
-- AND THE MEMBERSHIP PREMISE IS THE STATEMENT RATHER THAN A
-- CONVENIENCE, WHICH IS THE SAME SHAPE THE HOP'S REPORT TURNED OUT TO
-- HAVE.  Unconditioned the claim is false at one line: connect a slot
-- already in the set and the count does not move, so `<` fails on the
-- nose.  The clause is reached only down the branch where the
-- membership reads `false`, so the true statement is the conditioned
-- one and the caller already holds its witness.
postulate
  connect-drops : ∀ {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) (i : Fin n)
                → memberSource (toℕ i) cs ≡ false
                → unconn sl (toℕ i ∷ cs) < unconn sl cs

-- and the edge, which needs the triple's own `U` to BE that count.  It
-- is at the connect that the triple is re-seeded, so the equation is
-- the clause's own `refl` rather than something carried: the caller
-- hands over the definition and the component it hands over is the
-- definition's.
connect-edge : ∀ {r s r′ s′} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
                 (i : Fin n)
             → memberSource (toℕ i) cs ≡ false
             → (unconn sl (toℕ i ∷ cs) , r′ , s′) ≺ (unconn sl cs , r , s)
connect-edge sl cs i fresh = ltU (connect-drops sl cs i fresh)

------------------------------------------------------------------
-- WHERE A DESCENT STARTS.  Every re-entry from OUTSIDE the
-- subscription machine begins a fresh one, so each supplies its own
-- accessibility at the point the program, the slots and the run's own
-- reading determine.
------------------------------------------------------------------

-- ONE DEFINITION BECAUSE THE ENTRY POINTS AGREE, AND BECAUSE EVERY
-- STATEMENT QUANTIFYING OVER AN ENTRY HAS TO NAME THE SAME TRIPLE: a
-- statement entered at a triple nothing else uses is a statement about
-- a run nobody makes.  The reading is what the root has none of —
-- `st-init` holds nothing and a fresh schedule's pending values are the
-- program's own — so the root enters at reading ZERO and `rootTri` is
-- that specialisation rather than a second seeding.
--
-- THE RANK IS THE TERM'S `strmᵗ` NESTING, AND NOTHING IS PRE-PAID.  The
-- hop used to descend on a BUDGET: a figure large enough at entry that
-- every hop the run would ever take could be charged against it, with a
-- bailout standing where the budget ran out.  It descends on
-- `obsDepthᵉ` instead, which the builder compares at the site it hops —
-- so the entry owes a figure dominating the TERM rather than the run,
-- and a subterm satisfies that by construction.
--
-- THE STORE IS JOINED IN BECAUSE AN ARRIVAL CAN SUBSCRIBE WHAT A NODE
-- IS HOLDING.  The term alone does not bound a parked inner or a
-- deepened accumulator, and both are subscribable at a later instant;
-- the join is taken in ONE currency, which is the thing the reading
-- could never do, since a nesting and a reading never met.
--
-- DEAD ROUTE: seeding the component off SYNTAX AS A BUDGET — a power of
--   two in the program's size plus the slot telescope's.  A value
--   deepens on the way OUT, the frames above a flattener re-wrap what
--   it delivers, and it re-enters at the caller's own witness, so
--   whatever seeds that caller has to dominate everything its subtree
--   will ever emit; the run multiplies where the seed merely doubles.
--   Seeding from the entered VALUE fails identically, and a larger seed
--   is the same answer with a larger constant.  It is the BUDGET that
--   is dead and not the syntax: a figure compared at the hop is never
--   asked to dominate an emission, only to be dropped by one.
entryTri : ∀ {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → ℕ → Tri
entryTri e sl m = unconn sl [] , obsDepthᵉ e ⊔ m , syncSizeᵉ e

entryWitness : ∀ {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (m : ℕ)
             → Acc _≺_ (entryTri e sl m)
entryWitness e sl m = ≺-wellFounded (entryTri e sl m)

rootTri : ∀ {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → Tri
rootTri e sl = entryTri e sl 0

rootWitness : ∀ {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
            → Acc _≺_ (rootTri e sl)
rootWitness e sl = entryWitness e sl 0
