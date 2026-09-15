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

open import Data.Bool using (T; false)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Nat using (ℕ; suc; _+_; _<_; _≤_; _⊔_)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; n≤1+n; m≤n+m; m≤n⊔m;
  <-≤-trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Vec using (lookup; []; _∷_)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; sym)

open import Rx.Prim using (Source; InstEmit; InstEvent; init; value; close; handoff; complete)
open import Rx.Exp using (obs; Ctx; Exp; Ty; Val; Closed; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_;
  syncSizeᵉ; unfoldμ; μᵉ; inputsBelowᵉ)
open import Rx.Obs-Depth using (depᵉ; dep-unfoldμ-no-deeper)
open import Rx.Slot-Depth using (slotDepth; slotDepth-fix)
open import Rx.Sync-Size using (unfoldμ-shrinks)
open import Rx.Slots using (Slots; shared)
open import Rx.Strat-Order using (Tri; _≺_; ltU; ltR; ltS; ≺-wellFounded)
open import Rx.Evaluator using (unconn; memberSource; Stream; splitEvents; EvalSt)

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
-- IT CARRIES TWO CONJUNCTS AND NOT THREE, AND THE THIRD COMPONENT IS
-- WHY.  One guard per component would be the tidy shape: the μ unfold
-- reads the synchronous size, the hop reads the rank, the share connect
-- reads the unconnected count.  The connect asks for no conjunct
-- because what it needs is not a demand on the ENTRY at all — it needs
-- the reference's own reading to dominate the definition's, and the
-- environment makes that an equation rather than a premise.  The root
-- satisfies both conjuncts out of its own seeding: `evaluate` builds
-- the entry from the program's size and its reading.
--
-- AND THE READING IS TAKEN IN AN ENVIRONMENT, WHICH IS WHAT THE THIRD
-- CONJUNCT WOULD HAVE BEEN FOR AND COULD NOT HAVE DONE.  A conjunct
-- bounding the slot telescope adds a figure that is CONSTANT in the
-- program, while the rank strictly drops at every hop — so the two
-- reconcile only where a reference's own price already dominates its
-- definition, which is the environment's whole content.
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
EntryOK : ∀ {n} {Γ : Ctx n} {u} (η : Fin n → ℕ) → Closed Γ u → Tri → Set
EntryOK η b (_ , r , sz) = syncSizeᵉ b ≤ sz × depᵉ η b ≤ r

-- AND THE OTHER AGREEMENT A BUILDER CARRIES, WHICH IS ABOUT THE STORE
-- RATHER THAN ABOUT THE TERM.  The connect's edge drops the unconnected
-- count, so a clause reaching it has to know the triple it is standing
-- at still dominates that count — and the count only ever falls, since
-- connecting adds to the set and nothing removes from it.  So this is
-- `≤` and not an equation: the root enters at the count itself, every
-- connect below it widens the gap, and no clause ever has to restore
-- one.  It sits beside the slot-table agreement for the same reason
-- that one exists — a premise fixed by the caller is a constant, where
-- a reading taken off the state in hand would be re-denominated at
-- every recursive call and owe a transport at each.
SharesUnder : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
            → Slots Γ → Tri → EvalSt e → Set
SharesUnder sl τ st = unconn sl (EvalSt.connectedShares st) ≤ proj₁ τ


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
-- REFUTED: git show 80e527f9:agda/evidence/refuted/Refuted/Carried-Unranked.agda
--   — the FLAT reading, asked of every value at every type, at a
--   one-shot source of one numeral entered at the rank the root itself
--   builds. That witness is as far from the risky region as a program
--   gets, which is what says the repair is the type split rather than a
--   hypothesis about the program.  It is at a sha because it read the
--   machine's own subscribe, which `src` no longer has.
ValOK : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) (u : Ty) → Tri → Val Γ u → Set
ValOK η unitᵗ    _ _           = ⊤
ValOK η boolᵗ    _ _           = ⊤
ValOK η natᵗ     _ _           = ⊤
ValOK η (s ×ᵗ t) τ (a , b)     = ValOK η s τ a × ValOK η t τ b
ValOK η (s +ᵗ t) τ (inj₁ a)    = ValOK η s τ a
ValOK η (s +ᵗ t) τ (inj₂ b)    = ValOK η t τ b
ValOK η (obs t)  (_ , r , _) o = depᵉ η o < r

HandedOK : ∀ {n} {Γ : Ctx n} {u} (η : Fin n → ℕ) → List (Val Γ u) → Tri → Set
HandedOK {u = u} η vs τ = All (ValOK η u τ) vs

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
EventOK : ∀ {n} {Γ : Ctx n} {u} (η : Fin n → ℕ) → Tri → InstEvent (Val Γ u) → Set
EventOK {u = u} η τ (value v) = ValOK η u τ v
EventOK η _ (init _)    = ⊤
EventOK η _ (close _ _) = ⊤
EventOK η _ (handoff _) = ⊤
EventOK η _ complete    = ⊤

BurstOK : ∀ {n} {Γ : Ctx n} {s} (η : Fin n → ℕ) → Stream Γ s → Tri → Set
BurstOK η bs τ = All (λ em → All (EventOK η τ) (InstEmit.events em)) bs

-- the splitter keeps every `value` payload and drops the rest, so a
-- property of the events is a property of the values it grafts — proven
-- over the retag type the call site pins rather than over a chosen one,
-- since the two halves are independent and only the first is read here
split-handed : ∀ {n} {Γ : Ctx n} {u} {A : Set} {τ} (η : Fin n → ℕ)
             → (es : List (InstEvent (Val Γ u)))
             → All (EventOK η τ) es
             → HandedOK {Γ = Γ} η (proj₁ (splitEvents {A = A} es)) τ
split-handed η []              []ᵃ        = []ᵃ
split-handed η (value v  ∷ es) (p ∷ᵃ ps) = p ∷ᵃ split-handed η es ps
split-handed η (init _   ∷ es) (_ ∷ᵃ ps) = split-handed η es ps
split-handed η (close _ _ ∷ es) (_ ∷ᵃ ps) = split-handed η es ps
split-handed η (handoff _ ∷ es) (_ ∷ᵃ ps) = split-handed η es ps
split-handed η (complete ∷ es) (_ ∷ᵃ ps) = split-handed η es ps

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
μ-edge : ∀ {U r sz} {Γ : Ctx n} {u} (η : Fin n → ℕ)
         (body : Exp Γ (u ∷ []) [] [] u)
       → syncSizeᵉ (μᵉ body) ≤ sz
       → depᵉ η (μᵉ body) ≤ r
       → (U , r , syncSizeᵉ (unfoldμ body)) ≺ (U , r , sz)
μ-edge η body sz≤ _ = ltS (≤-trans (unfoldμ-shrinks body) sz≤)

-- and the peel's other component, which is not part of the edge but is
-- what keeps the invariant true at the unfolding
μ-entry : ∀ {r} {Γ : Ctx n} {u} (η : Fin n → ℕ)
          (body : Exp Γ (u ∷ []) [] [] u)
        → depᵉ η (μᵉ body) ≤ r → depᵉ η (unfoldμ body) ≤ r
μ-entry η body = ≤-trans (dep-unfoldμ-no-deeper η body)

-- THE HOP'S FACT IS THE SUBSTITUTION REPORT, AND IT IS THE ONE THE
-- WHOLE TIER IS ABOUT.  What arrives at the hop is a runtime VALUE,
-- structurally unrelated to the term the clause stands at, so no
-- reading of the program supplies it directly — but where the value was
-- handed on by a `map-f` it is `applyFn fn v`, which the burst report
-- prices by the TEMPLATE at a data payload, with nothing carried in.
-- The residue is a source's output and a fold's, which is what the
-- carried family is for and now the only thing that needs it.
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
hop-edge : ∀ {U r s} {Γ : Ctx n} {u} (η : Fin n → ℕ) (o : Val Γ (obs u))
         → depᵉ η o < r
         → (U , depᵉ η o , syncSizeᵉ o) ≺ (U , r , s)
hop-edge η o drop = ltR drop

-- THE EXTRACTION, WRITTEN OUT BECAUSE IT IS THE WHOLE OF THE ARGUMENT
-- AND READS AS A TRIVIALITY.  Stating it separately is what keeps the
-- one-element `All` from being taken apart again at each of the three
-- consume families that reach the hop.
--
-- AND τ IS EXPLICIT HERE, WHICH IS FORCED RATHER THAN A STYLE.  `ValOK`
-- at an observable type reads the middle component and nothing else, so
-- both sides of this statement mention τ only under a projection — and a
-- projection is not a pattern, so no argument can ever solve it.  Left
-- implicit, in either the whole-τ or the split-triple spelling, every
-- call reports unsolved metas against the APPLICATION rather than
-- against the statement that cannot determine them.
hop-guard : ∀ {n} {Γ : Ctx n} {u} (η : Fin n → ℕ) (τ : Tri) (o : Val Γ (obs u))
          → HandedOK {Γ = Γ} η (o ∷ []) τ
          → depᵉ η o < proj₁ (proj₂ τ)
hop-guard η _ o (h ∷ᵃ []ᵃ) = h

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
--
-- PROBED: `Probed.Connect-Count` — tables of one and three `shared`
--   slots, connected at the last unconnected one, with slack left
--   over, and at an index that is not the head of the set.  Not
--   reached: a `scripted` slot, which reads nought on both sides.
postulate
  connect-drops : ∀ {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) (i : Fin n)
                → memberSource (toℕ i) cs ≡ false
                → unconn sl (toℕ i ∷ cs) < unconn sl cs

-- AND THE EDGE, WHICH TAKES SLACK RATHER THAN AN EQUATION — WHICH IS
-- WHAT WRITING THE ARM'S BODY FOUND.  Stated with the triple's own `U`
-- fixed to BE the count, it is usable only where the caller's rank was
-- seeded at exactly `unconn sl cs`, and no caller can promise that:
-- every connect the run has already performed dropped the count while
-- the triple the builder was entered at stayed put, so by the second
-- one the two have separated.  The count is MONOTONE against the rank
-- rather than equal to it, so the premise is `≤` and the edge composes
-- the drop through it — the equation is the `≤-refl` instance, which is
-- what the root supplies and nothing below it does.
--
-- WHAT THE RESIDUE IS, AND IT IS A PREMISE THE BUILDER DOES NOT CARRY
-- YET.  The slack has to arrive at the connect arm, so every builder
-- signature owes `unconn sl (EvalSt.connectedShares st) ≤ proj₁ τ`
-- alongside the agreement it already carries for the slot table — and
-- every clause handing a LATER state onward owes that connecting only
-- shrinks the count, which is a statement over the ⇓ families rather
-- than over any function.  That is the same shape the slot-table
-- agreement takes, and it is why the arm is not a body today.
connect-edge : ∀ {U r s r′ s′} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
                 (i : Fin n)
             → memberSource (toℕ i) cs ≡ false
             → unconn sl cs ≤ U
             → (unconn sl (toℕ i ∷ cs) , r′ , s′) ≺ (U , r , s)
connect-edge sl cs i fresh le = ltU (<-≤-trans (connect-drops sl cs i fresh) le)

-- AND THE CONNECT'S OTHER COMPONENT, WHICH IS THE ONE THE ENVIRONMENT
-- WAS BUILT FOR.  The edge drops the count and leaves the rank free, so
-- what has to be shown at the definition is the ENTRY invariant — and it
-- was shown against a reading that priced a reference at nought, which
-- is a claim about a symbol rather than about what the connect plumbs out
-- through it.  Read in the environment there is nothing to carry: the
-- reference's number IS the definition's, so the size is the
-- definition's own and the rank is reached by the fixpoint alone.
--
-- REFUTED: `Refuted.Carried-Derived` — the same connect, with the
--   reference priced at nought instead, at a fresh share whose
--   definition writes one level of observable.

connect-entry : ∀ {U} {Γ : Ctx n} (sl : Slots Γ) (i : Fin n)
                {d : Closed Γ (lookup Γ i)}
                {ok : T (inputsBelowᵉ (toℕ i) d)}
              → sl i ≡ shared d {ok = ok}
              → EntryOK (slotDepth sl) d
                  ( U , slotDepth sl i , syncSizeᵉ d )
connect-entry sl i eq = ≤-refl , ≤-reflexive (sym (slotDepth-fix sl i eq))

------------------------------------------------------------------
-- WHERE A DESCENT STARTS.  Every re-entry from OUTSIDE the
-- subscription machine begins a fresh one, so each supplies its own
-- accessibility at the point the program, the slots and the run's own
-- reading determine.
------------------------------------------------------------------

-- A run entering from outside the subscription machine has put nothing
-- into any store yet — that is the same fact `rootTri` reads off
-- `st-init`, one component over — so the census is all zeros and the
-- only content of the component is how wide it is.  The width has to
-- dominate every depth a store below this entry can come to hold, and
-- a queued observable is written under the rank standing when it was
-- written, which never rises above the rank named here; so the
-- successor of that rank is a width the whole descent can be compared
-- against.  It is fixed at the entry rather than read off the state
-- because a comparison relates two censuses of the SAME width, and a
-- reading taken later would be a different one at every clause.

-- ONE DEFINITION BECAUSE THE ENTRY POINTS AGREE, AND BECAUSE EVERY
-- STATEMENT QUANTIFYING OVER AN ENTRY HAS TO NAME THE SAME TRIPLE: a
-- statement entered at a triple nothing else uses is a statement about
-- a run nobody makes.  The reading is what the root has none of —
-- `st-init` holds nothing and a fresh schedule's pending values are the
-- program's own — so the root enters at reading ZERO and `rootTri` is
-- that specialisation rather than a second seeding.
--
-- THE RANK IS THE TERM'S `strmᵗ` NESTING READ THROUGH THE TELESCOPE,
-- AND NOTHING IS PRE-PAID.  The hop used to descend on a BUDGET: a
-- figure large enough at entry that every hop the run would ever take
-- could be charged against it, with a bailout standing where the budget
-- ran out.  It descends on the reading instead, which the builder
-- compares at the site it hops — so the entry owes a figure dominating
-- the TERM rather than the run, and a subterm satisfies that by
-- construction.  What the environment adds is that a slot reference
-- counts as its definition, so "the term" means the program a connect
-- can actually reach rather than the symbols written in it.
--
-- THE STORE IS JOINED IN BECAUSE AN ARRIVAL CAN SUBSCRIBE WHAT A NODE
-- IS HOLDING.  The term alone does not bound a parked inner or a
-- deepened accumulator, and both are subscribable at a later instant;
-- the join is taken in ONE currency, which is the thing the reading
-- could never do, since a nesting and a reading never met.
--
-- AND THE THIRD ARGUMENT IS WHERE A LENGTH RESERVATION WOULD GO, WHICH
-- IS WORTH SAYING WHILE NOTHING SUPPLIES ONE.  It joins into the same
-- component the hop is dropped in, and every caller passes nought, so
-- the parameter is presently slack rather than a quantity.  The fold's
-- leaf asks for exactly such a reservation while carrying no premise
-- that relates it to a burst, and the frame's rank is seeded from the
-- values in hand, where a count is free to read — so the two ends of
-- the repair already exist and what is unsettled is the SIZE.  It is
-- not the BUDGET the section below kills: a budget had to dominate
-- every later emission, while a reservation re-seeded at each frame
-- step covers one burst, and the run multiplies only across the steps
-- it is re-seeded at.
-- REFUTED: `Refuted.Scan-Length` — the leaf that would spend it, at a
--   burst of five plain numbers
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
entryTri e sl m = unconn sl []
                , depᵉ (slotDepth sl) e ⊔ m
                , syncSizeᵉ e

entryWitness : ∀ {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (m : ℕ)
             → Acc _≺_ (entryTri e sl m)
entryWitness e sl m = ≺-wellFounded (entryTri e sl m)

rootTri : ∀ {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → Tri
rootTri e sl = entryTri e sl 0

rootWitness : ∀ {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
            → Acc _≺_ (rootTri e sl)
rootWitness e sl = entryWitness e sl 0
