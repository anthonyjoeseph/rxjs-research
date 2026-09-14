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
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Nat using (ℕ; suc; _+_; _<_; _≤_; _⊔_)
open import Data.Nat.Properties using (≤-trans; n≤1+n; m≤n+m; m≤n⊔m)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim using (Source; InstEmit; InstEvent; init; value; close; handoff; complete)
open import Rx.Exp using (obs; Ctx; Exp; Ty; Val; Closed; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_;
  syncSizeᵉ; unfoldμ; μᵉ)
open import Rx.Obs-Depth using (obsDepthᵉ; unfoldμ-no-deeper)
open import Rx.Sync-Size using (unfoldμ-shrinks)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (Tri; _≺_; ltU; ltR; ltS; ≺-wellFounded)
open import Rx.Evaluator using (unconn; memberSource; Stream; splitEvents)

variable
  n : ℕ

-- THE ENTRY INVARIANT, AND THE ONLY THING IT STANDS ON IS THAT THE
-- UNCONDITIONAL FORM IS DEAD.  A totality claim quantified freely
-- over the witness says a derivation exists at every entry, and three
-- of the machine's clauses read a component of that entry against the
-- TERM — so a caller free to pick the triple can starve a guard at a
-- program with nothing hard in it.  This is what relates the two ends,
-- and it is the one shape of hypothesis this repo admits without a
-- restatement's cost being a laundering: the conditioned statement is
-- the true one replacing a false one.
--
-- IT CARRIES TWO CONJUNCTS AND IS EXPECTED TO GROW TO THREE, WHICH IS
-- THE CONVERGENCE RATHER THAN AN OMISSION.  One guard per component:
-- the μ unfold reads the synchronous size, the hop reads the rank, the
-- share connect reads the unconnected count.  The third is a reading
-- nothing has forced a shape for yet, and each lands the day its own
-- witness forces it, so the predicate grows against a `⊥` rather than
-- by guess.  The root satisfies both of these out of its own seeding:
-- `evaluate` builds the entry from the program's size and depth.
--
-- AND THE RANK CONJUNCT IS WHAT MAKES THE HOP'S PREMISE PAYABLE, which
-- is why it is here rather than threaded into a signature.  A value a
-- frame hands on is bounded by the depth of the TERM the burst came
-- from, so the statement that pays `HandedOK` needs the entry to bound
-- that depth — and the hop's own re-entry satisfies the conjunct
-- definitionally, since it drops the rank to the inner's own reading.
--
-- REFUTED: git show ba1285b:agda/evidence/refuted/Refuted/Totality-Entry.agda
--   — the statement below WITHOUT this premise, at a `μ` over a one-shot
--   source entered at the zero triple, claiming the unfolding's size
--   beside the run's dryness.  It is at a sha because `src` can no
--   longer state it: the run reads no triple and emits no marker, so
--   neither number the witness put side by side still exists.
EntryOK : ∀ {n} {Γ : Ctx n} {u} → Closed Γ u → Tri → Set
EntryOK b (_ , r , sz) = syncSizeᵉ b ≤ sz × obsDepthᵉ b ≤ r

-- CARRYING THE ENTRY INVARIANT DOWN A FRAME, WHICH IS THE WHOLE OF THE
-- ARITHMETIC THE SUBSCRIBE INDUCTION NEEDS.  `syncSizeᵉ` counts the
-- constructor and the frame's own term before it reaches the source,
-- so a term's inner expression measures strictly below it and the
-- invariant survives every structural descent with room to spare.  The
-- only place a step is not structural is the μ peel, and that one is
-- paid by the unfolding's own measure rather than here.
entry-under : ∀ {c sz} → suc c ≤ sz → c ≤ sz
entry-under le = ≤-trans (n≤1+n _) le

entry-inner : ∀ {a b sz} → suc (a + b) ≤ sz → b ≤ sz
entry-inner {a} {b} le = ≤-trans (m≤n+m b a) (entry-under le)

-- and the rank's own descent, which is a join rather than a successor:
-- every structural clause reads its frame's term BESIDE the source's
-- depth, so the source is a summand and the bound passes through
entry-depth : ∀ {a c r} → a ⊔ c ≤ r → c ≤ r
entry-depth {a} {c} le = ≤-trans (m≤n⊔m a c) le

-- and the two shapes every structural clause takes, so a call site
-- spends one name rather than splitting the pair by hand.  A framed
-- clause carries its frame's term in BOTH components — summed in the
-- size, joined in the depth — while a flattener carries none, so its
-- rank passes through untouched.
inner-ok : ∀ {a b c d sz r} → (suc (a + b) ≤ sz) × (c ⊔ d ≤ r) → (b ≤ sz) × (d ≤ r)
inner-ok (s , p) = entry-inner s , entry-depth p

under-ok : ∀ {b c sz r} → (suc b ≤ sz) × (c ≤ r) → (b ≤ sz) × (c ≤ r)
under-ok (s , p) = entry-under s , p

-- WHAT A CLAUSE IS HANDED, WHICH IS A SEPARATE PREDICATE AND NOT A
-- FOURTH CONJUNCT UP THERE.  The entry invariant speaks about the TERM
-- a subscribe enters at; the hop reads a runtime VALUE that arrives
-- later and is structurally unrelated to that term, so no reading of
-- the program can supply it.  This says exactly what the guard reads —
-- every value the clause receives is written shallower than the rank it
-- is standing at — and it is the one shape of hypothesis this repo
-- admits without a restatement being a laundering.
--
-- AND IT READS THE VALUE'S TYPE, WHICH IS THE DIFFERENCE BETWEEN A
-- PROPERTY OF BURSTS AND A DEMAND ON THE ENTRY.  The bound exists to pay
-- ONE guard — the hop's, which compares an OBSERVABLE against the rank —
-- and an observable reaches a frame as the payload of a `strmᵗ`, the one
-- head the reading charges a successor for.  So the strictness is real
-- exactly where it is spent.  Asked flat, of every value at every type,
-- it reads a numeral at nought and demands nought be strictly below the
-- rank, which is a claim about the caller and not about the burst.
--
-- SO THE CLAUSES MIRROR THE READING'S OWN, RATHER THAN STOPPING AT THE
-- OBSERVABLE HEAD.  A pair or an injection can carry an observable a
-- later projection hands to a hop, so ⊤ at those types would weaken the
-- premise exactly where a frame is free to recover the value — and
-- recursing costs nothing, since the reading already recurses there and
-- the two then correspond clause for clause.
--
-- REFUTED: git show ba1285b:agda/evidence/refuted/Refuted/Hop-Unconditioned.agda
--   — the hop leaf below WITHOUT this premise, at the emptiest inner
--   there is entered at a rank of nought.  What it established survives
--   the cutover and is why this premise is here: the repair relates the
--   two ends rather than reading either more carefully.  It is at a sha
--   because the guard it was strict against is gone.
--
-- REFUTED: `Refuted.Carried-Unranked` — the FLAT reading, asked of every
--   value at every type, at a one-shot source of one numeral entered at
--   the rank the root itself builds. That witness is as far from the
--   risky region as a program gets, which is what says the repair is the
--   type split rather than a hypothesis about the program.
ValOK : ∀ {n} {Γ : Ctx n} (u : Ty) → Tri → Val Γ u → Set
ValOK unitᵗ    _ _           = ⊤
ValOK boolᵗ    _ _           = ⊤
ValOK natᵗ     _ _           = ⊤
ValOK (s ×ᵗ t) τ (a , b)     = ValOK s τ a × ValOK t τ b
ValOK (s +ᵗ t) τ (inj₁ a)    = ValOK s τ a
ValOK (s +ᵗ t) τ (inj₂ b)    = ValOK t τ b
ValOK (obs t)  (_ , r , _) o = obsDepthᵉ o < r

HandedOK : ∀ {n} {Γ : Ctx n} {u} → List (Val Γ u) → Tri → Set
HandedOK {u = u} vs τ = All (ValOK u τ) vs

-- AND THE SAME OVER A BURST, WHICH IS WHERE THOSE VALUES COME FROM.  A
-- push cycle steps one frame per emit and hands that frame the emit's
-- own values, so the premise travels as a property of the whole burst
-- and is split, emit by emit, by the induction that walks it.  Nothing
-- here reads the schedule or the store: the burst is already built when
-- the cycle starts, which is what makes a single `All` sufficient.
--
-- AND IT IS STATED OVER THE EVENTS RATHER THAN OVER THE SPLIT, WHICH IS
-- FORCED AND NOT A PREFERENCE.  The splitter is polymorphic in the type
-- of the bookkeeping half it retags into, and a predicate reading only
-- its first component leaves that parameter free — an unsolved meta at
-- the definition, and two applications at DIFFERENT retag types that no
-- longer agree on an open list.  Reading the events directly names no
-- such parameter, and `split-handed` below carries the property across
-- the splitter at whatever type the call site pins.
EventOK : ∀ {n} {Γ : Ctx n} {u} → Tri → InstEvent (Val Γ u) → Set
EventOK {u = u} τ (value v) = ValOK u τ v
EventOK _ (init _)    = ⊤
EventOK _ (close _ _) = ⊤
EventOK _ (handoff _) = ⊤
EventOK _ complete    = ⊤

BurstOK : ∀ {n} {Γ : Ctx n} {s} → Stream Γ s → Tri → Set
BurstOK bs τ = All (λ em → All (EventOK τ) (InstEmit.events em)) bs

-- the splitter keeps every `value` payload and drops the rest, so a
-- property of the events is a property of the values it grafts — proven
-- over the retag type the call site pins rather than over a chosen one,
-- since the two halves are independent and only the first is read here
split-handed : ∀ {n} {Γ : Ctx n} {u} {A : Set} {τ}
             → (es : List (InstEvent (Val Γ u)))
             → All (EventOK τ) es
             → HandedOK {Γ = Γ} (proj₁ (splitEvents {A = A} es)) τ
split-handed []              []ᵃ        = []ᵃ
split-handed (value v  ∷ es) (p ∷ᵃ ps) = p ∷ᵃ split-handed es ps
split-handed (init _   ∷ es) (_ ∷ᵃ ps) = split-handed es ps
split-handed (close _ _ ∷ es) (_ ∷ᵃ ps) = split-handed es ps
split-handed (handoff _ ∷ es) (_ ∷ᵃ ps) = split-handed es ps
split-handed (complete ∷ es) (_ ∷ᵃ ps) = split-handed es ps

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
-- `Rx.Obs-Depth.Substitution.applyFn-strict` prices that by the
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

-- THE EXTRACTION, WRITTEN OUT BECAUSE IT IS THE WHOLE OF THE ARGUMENT
-- AND READS AS A TRIVIALITY.  It is what the leaf above will `with` on
-- to refute the guard, and stating it separately is what keeps the
-- refutation from being reargued at each of the three consume families.
hop-guard : ∀ {n} {Γ : Ctx n} {u} {U r sz} (o : Val Γ (obs u))
          → HandedOK {Γ = Γ} (o ∷ []) (U , r , sz)
          → obsDepthᵉ o < r
hop-guard o (h ∷ᵃ []ᵃ) = h

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
