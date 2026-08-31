-- WHAT A SUBSCRIPTION'S EMITTED VALUES COST, stated on its own so that
-- the induction establishing it can sit BELOW the descent that spends
-- it.  The descent's own clause for a `*All` head consumes this, so a
-- statement kept beside that clause could never be proven by recursion
-- on the subject without the two becoming mutual for no reason.
module Verify-Budget-Sufficient.Sighted-Fit where

open import Data.Bool using (Bool; T; true; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _+_; _*_; _^_; _≤_)
open import Data.Nat.Properties using (≤-trans; +-monoˡ-≤)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Rx.Prim using (Gas; Id; Tick; InstEmit; InstEvent; init; value; close; handoff; complete)
open import Rx.Exp using (Ty; Ctx; Closed; Val; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs;
  inputsBelowᵉ; syncSizeᵉ)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵛ)
open import Rx.Evaluator using (Sched; EvalSt; Path; Stream; subscribeE; splitEvents)
open import Verify-Budget-Sufficient.Nest-Store using (pathNestD; slotWrapSum)

-- WHICH INPUTS A STORED VALUE MAY NAME, charged through its type
-- exactly as its nesting is, and for the same reason: `Val` is a
-- computed family, so the only way in is to recurse on the `Ty`, and
-- `obs` is where a value becomes syntax again.  Everything else is
-- data and names nothing, which is not a convenience -- a scripted
-- slot is DATA by construction, so the whole of what a value can carry
-- an input inside is an `obs` leaf.
inputsBelowᵛ : ∀ {n} {Γ : Ctx n} (k : ℕ) (t : Ty) → Val Γ t → Bool
inputsBelowᵛ k unitᵗ    _        = true
inputsBelowᵛ k boolᵗ    _        = true
inputsBelowᵛ k natᵗ     _        = true
inputsBelowᵛ k (s ×ᵗ t) (a , b)  = inputsBelowᵛ k s a ∧ inputsBelowᵛ k t b
inputsBelowᵛ k (s +ᵗ t) (inj₁ a) = inputsBelowᵛ k s a
inputsBelowᵛ k (s +ᵗ t) (inj₂ b) = inputsBelowᵛ k t b
inputsBelowᵛ k (obs t)  e        = inputsBelowᵉ k e

-- THE FIT, AT AN ARBITRARY DELIVERED TYPE, and the generality is what
-- makes it inducible rather than a nicety.  A `map` frame's burst is
-- its payload's burst pushed through the function, and the payload's
-- type is whatever the program says -- so a statement that could only
-- be made about `obs`-typed emissions would have no hypothesis to
-- recurse with at the very clause that does the work.
--
-- THE PATH ENTERS AS A NUMBER.  It is read for its nesting and for
-- nothing else, and taking the number rather than the path is what
-- lets a fold be established under one path and spent under another:
-- both places move the same way, so the weakening below carries it.
ValFitG : ∀ {n} {Γ : Ctx n} (k : ℕ) (sl : Slots Γ) (G P : ℕ) (t : Ty)
  → Val Γ t → Set
ValFitG k sl G P t v =
  T (inputsBelowᵛ k t v)
  × (P + nestDᵛ t v + k * slotWrapSum sl ≤ G)

ValsFitG : ∀ {n} {Γ : Ctx n} (k : ℕ) (sl : Slots Γ) (G P : ℕ) (t : Ty)
  → List (Val Γ t) → Set
ValsFitG k sl G P t []       = ⊤
ValsFitG k sl G P t (o ∷ os) = ValFitG k sl G P t o × ValsFitG k sl G P t os

StreamFitG : ∀ {n} {Γ : Ctx n} (k : ℕ) (sl : Slots Γ) (G P : ℕ) (t : Ty)
  → Stream Γ t → Set
StreamFitG k sl G P t []                       = ⊤
StreamFitG {Γ = Γ} k sl G P t (em ∷ ems) =
  ValsFitG k sl G P t (proj₁ (splitEvents {A = Val Γ t} (InstEmit.events em)))
  × StreamFitG k sl G P t ems

-- AND THE EVENT SPLIT'S VALUE SIDE DOES NOT READ THE TYPE IT IS
-- ANNOTATED AT, which has to be said in Agda because the annotation is
-- an argument.  The split reports what a frame will PUSH beside what
-- it will forward, and the pushed side is typed by the frame's output
-- -- a type this fold has no business naming.  So a consumer whose
-- annotation is the frame's and a fold whose annotation is the
-- stream's are talking about the same list, and this is the equation
-- that says so.
splitVals-irr : ∀ {n} {Γ : Ctx n} {u} {A B : Set}
  (es : List (InstEvent (Val Γ u))) →
  proj₁ (splitEvents {Γ = Γ} {A = A} es) ≡ proj₁ (splitEvents {Γ = Γ} {A = B} es)
splitVals-irr []                = refl
splitVals-irr (value v   ∷ es)  = cong (v ∷_) (splitVals-irr es)
splitVals-irr (init s    ∷ es)  = splitVals-irr es
splitVals-irr (close s r ∷ es)  = splitVals-irr es
splitVals-irr (handoff s ∷ es)  = splitVals-irr es
splitVals-irr (complete  ∷ es)  = splitVals-irr es

-- A SMALLER CHARGE AND A LARGER GRANT ARE EACH A WEAKENING, which is
-- the whole content of separating the two numbers.
valsFitG-le : ∀ {n} {Γ : Ctx n} (k : ℕ) (sl : Slots Γ) (G G′ P P′ : ℕ) (t : Ty)
  (os : List (Val Γ t)) → P ≤ P′ → G′ ≤ G →
  ValsFitG k sl G′ P′ t os → ValsFitG k sl G P t os
valsFitG-le k sl G G′ P P′ t []       hp hg h        = tt
valsFitG-le k sl G G′ P P′ t (o ∷ os) hp hg (h , hs) =
  (proj₁ h
  , ≤-trans (+-monoˡ-≤ (k * slotWrapSum sl) (+-monoˡ-≤ (nestDᵛ t o) hp))
            (≤-trans (proj₂ h) hg))
  , valsFitG-le k sl G G′ P P′ t os hp hg hs


-- WHAT A SUBSCRIPTION EMITS, read as values.  It is the half the
-- descent's own induction does not reach: a claim about the STREAM a
-- subscribe hands back rather than about how far it descends, so no
-- row that computes a depth reaches it.
--
-- THE GRANT CARRIES THE SLOT SUMMAND, and it did not always.  A
-- payload may emit a slot REFERENCE, whose syntax says nothing about
-- what the slot holds, so a grant read off the payload alone is
-- pinned at a constant while subscribing the emitted inner runs the
-- slot's definition.  The summand every other bound on this face
-- carries is what pays for that, and adding it here costs the
-- consumer nothing: the walk leaf READS the fit, so a wider grant is
-- a weaker hypothesis there, and the ceiling both are spent under
-- already has the same summand.
--
-- AND THE PAYLOAD'S SIZE IS THE WRONG EXPONENT: THE STATEMENT AS
-- WRITTEN IS FALSE.  A tower over program syntax is owed here rather
-- than per arrival -- that much survives -- but `syncSizeᵉ` reads ONE
-- at a scripted input, so a cold script's synchronous burst is a width
-- the exponent cannot see, while a `scanᵉ` over that input applies its
-- step function once per script value.  Point a step function at its
-- accumulator in both additive slots an inner `scanᵉ` offers and one
-- application doubles the delivered nesting: the left side is a power
-- of two in the SCRIPT's length and the grant is a constant.
--
-- WHAT THE REPAIR IS.  Not a larger constant and not the telescope
-- summand, since a script is charged to neither -- `slotWrapSum` reads
-- nought at a scripted slot.  The currency that already sees a burst
-- is `nestB`, whose exponent carries a WIDTH beside the size cap, and
-- the caps face states its own two subscription-nesting results in it
-- against a `descW` bound.  So the fit is restated in that currency
-- with a width parameter, which is the shape its neighbours already
-- have rather than a new invention.
--
-- REFUTED: `Refuted.Sight-Fit-Scan.scan-fit-absurd` is the one that
--   kills the statement above: a `scanᵉ` whose step doubles, over a
--   scripted slot, delivering `2 ^ N - 1` against a grant of four
--   thousand and ninety-six at every N.  It is a CROSSING and not a
--   scale error -- twelve script values hold at 4095 against 4096,
--   tight to one, and thirteen fail at 8191 -- and the grant is the
--   same number in both rows, which is the finding.  Not covered: the
--   `mapᵉ` and `takeᵉ` frames, and any path but `root`.
-- REFUTED: `Refuted.Sight-All-Stream-Dup.sight-all-stream-dup-absurd`
--   kills the arrival-tower fold at a flat telescope where the wrap is
--   nought: sixteen against eighteen in the exponents, so a quarter of
--   a million demanded against this grant of a hundred and thirty-one
--   thousand.  And `…nest-absurd` again two layers up, where the same
--   rows measure the gap COMPOUNDING.
-- REFUTED: `Refuted.Sight-All-Fit-Slot` kills the payload-only grant
--   at a slot whose definition substitutes per layer -- delivered
--   `8 16 32 64` against a constant sixteen, meeting it exactly at the
--   third layer and doubling past it -- and pins the repair by
--   checking that the summand-carrying grant holds at the deepest of
--   those rows.  Not covered: the two heads other than `mergeAllᵒ`,
--   any path other than the one the row subscribes under, and the
--   store-growth conjuncts, which no row reads apart from the value one.
-- PROBED: `Probed.Sight-All-Stream` INHABITS the fold -- the statement
--   itself, not a boolean mirror of it -- at the duplicating payload
--   the refutations above are taken at, and at three layers of that
--   duplication.  The two columns are the receipt: the charge reads
--   one, two, three, four while the grant's exponent reads sixteen,
--   twenty-three, thirty, thirty-seven, so one side is linear in the
--   layer and the other a tower over something linear in it.  Not
--   covered: the two other heads; any path but `root`, which pins the
--   telescope summand at nought and the wrap with it; a telescope of
--   more than one slot; and an ARRIVAL that is a slot reference, which
--   is the one shape the wrap summand exists for.
postulate
  subscribeE-fit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (g : Gas) (k : ℕ) (b : Closed Γ s) (κ : Path Γ s t)
    (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    T (inputsBelowᵉ k b) →
    StreamFitG k (Sched.slots sched)
      (2 ^ syncSizeᵉ b * (pathNestD κ + nestDᵉ b)
         + k * slotWrapSum (Sched.slots sched))
      (pathNestD κ) s
      (proj₁ (subscribeE g b κ bid now sched st))
