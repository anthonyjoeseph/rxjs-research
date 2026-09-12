------------------------------------------------------------------
-- THE NESTING MEASURE: how many `*All` layers a run can descend
-- through, as opposed to how many payloads travel abreast.  It is the
-- reading the descent's RANK component is about — the rank peels once
-- per `subscribeInner` hop, and a hop is a `*All` layer entered — so
-- this is the one measure an entry invariant can state the rank
-- against.  The three clauses that carry it are read off the
-- evaluator rather than fitted to a number.
--
-- A `*All` LAYER IS WORTH ONE `suc`, because a `thru-outer` frame is
-- where a burst's payload is re-entered as a subject in its own
-- right, and that re-entry is the hop.
--
-- A `scanᵉ` IS WORTH ITS STEP FUNCTION'S LAYERS ONCE, because on any
-- ONE chain the walk enters the step function once per scan frame; the
-- layers the folds pile onto the ACCUMULATOR live in the store, whose
-- measure is read off the state and so sees them as they accrue.  The
-- fold-times-wrap product is real, but it is priced where the folds
-- happen, never inside a measure of syntax, which cannot know a count
-- that has not happened yet.
--
-- A LIST OF PAYLOADS IS WORTH THEIR MAX, NOT THEIR SUM, because a
-- burst's values are entered one at a time, each from the same frame,
-- so two payloads abreast cost what the deeper of them costs.

-- THE MAX IS NOT A TIGHTENING FOR ITS OWN SAKE — the summing form is
-- priced dead by the one statement this measure exists to support.
-- The hop bound needs an emitted inner's nesting to be STRICTLY under
-- its EMITTER'S, since that is what turns one peel of the rank into a
-- re-established invariant.  Under a summing list clause it is not:
-- a step function may hand its input observable to a list TWICE — the
-- emitter reads 2, the inner it emits reads 3, and the inner's own
-- depth is 2, so the sum is over the depth by exactly the duplication.

-- THE DEFER GATE TRUNCATES, AND THE μ CLAUSE IS WHY.  The measure
-- returns zero at a `deferᵉ` — a deferred body is not entered
-- synchronously, it mints its own source and is walked later as a
-- subject in its own right — so passing through the gate would buy
-- nothing on the clause it is read at.  What it would COST is the μ
-- clause, where the walk descends into `unfoldμ body` while the
-- witness keeps its rank, so the bound needs the measure not to grow
-- under unfolding — and unfolding substitutes the whole `μᵉ` term at
-- every guarded occurrence.  With the gate at zero both sides read
-- the body's own reading and the clause is an EQUALITY; passing
-- through, a body naming itself twice under a `*All` doubles the
-- measure per unfold and no bound survives.  Same design as the
-- synchronous size, which truncates at the gate for the same reason,
-- and it is the whole reason this measure reaches where a size bound
-- on the term cannot.

-- THE MEASURE IS RAW, AND ITS TWO PREDECESSORS DIED OF NOT BEING SO.
-- The first read a fold count off the width family at the
-- UNSUBSTITUTED source, where a payload variable weighs nothing, so
-- two programs differing only in how many literals a map consumed
-- shared one bound against depths of 4 and 8.  The second took the
-- count as a PARAMETER and multiplied by it — and any count worth
-- supplying is defined off the recurrence it is meant to bound, so
-- the parameter moves with the instant while a preservation step
-- prices its increment at the old one.  A raw layer count has no
-- parameter to move.

-- THE `input` CLAUSE CONTRIBUTES NOTHING, AND A DESCENDING ONE IS
-- STRUCTURALLY DEAD.  Descending into the slot definition on slot
-- fuel with a visited set does not work here, because a consumer
-- fixes that fuel at the slot COUNT, which is a variable: the clause
-- never reduces, and the parent has no more fuel than the child it
-- would recurse into, so there is no inequality to prove even in
-- principle.  So a slot's nesting is charged where the slots are —
-- which the root seeding already does, since it adds the slot
-- telescope's own size to the rank it seeds.
--
-- DEAD ROUTE: charging a slot's nesting by the number of slots.  The
--   count is a variable in the consumer, so the descending clause
--   never reduces and the child gets no less fuel than the parent.
-- RECOVERY: git show 919f115:agda/src/Rx/Nest-Depth.agda restores the
--   VALUE-level arm `nestDᵛ`, which charges a stored place through its
--   type and meets the term induction at `obs`; and git show
--   919f115:agda/src/Verify-Budget-Sufficient/Nest-Depth-Size.agda its
--   pointwise bound by `sizeᵛ`.  Both are proven and gas-free, and the
--   drain is what will consume them — a slot delivering an observable
--   is the one place a nesting arrives that no expression carries.
------------------------------------------------------------------
module Rx.Nest-Depth where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat  using (ℕ; suc; _+_; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-trans; ≤-reflexive; m≤m+n; m≤n+m; m≤n⇒m≤1+n; +-assoc; +-comm; +-mono-≤; ⊔-lub)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)

open import Rx.Exp using (Ctx; Closed;
  Exp; Tm; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ;
  scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
  varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ;
  strmᵗ; sizeᵉ; sizeᵗ; sizeᵗˢ;
  elimGExp; elimGTm; elimGTms; unfoldμ)

mutual
  nestDᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → ℕ
  nestDᵉ (input i)       = 0
  nestDᵉ (ofᵉ ts)        = nestDᵗˢ ts
  nestDᵉ emptyᵉ          = 0
  nestDᵉ (mapᵉ f e)      = nestDᵗ f + nestDᵉ e
  nestDᵉ (takeᵉ c e)     = nestDᵉ e
  -- THE PRODUCT: one re-wrap per delivered payload
  nestDᵉ (scanᵉ f z e)   = nestDᵗ z + nestDᵗ f + nestDᵉ e
  -- THE SPENDING ARC: one suc per *All layer
  nestDᵉ (mergeAllᵉ lim e)   = suc (nestDᵉ e)
  nestDᵉ (switchAllᵉ e)  = suc (nestDᵉ e)
  nestDᵉ (exhaustAllᵉ e) = suc (nestDᵉ e)
  nestDᵉ (μᵉ e)          = nestDᵉ e
  nestDᵉ (varᵉ x)        = 0
  -- THE GATE TRUNCATES, and it is what makes μ safe
  nestDᵉ (deferᵉ e)      = 0

  nestDᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ Δᵍ Δ Θ t → ℕ
  nestDᵗ (varᵗ x)      = 0
  nestDᵗ unit̂          = 0
  nestDᵗ (bool̂ _)      = 0
  nestDᵗ (nat̂ _)       = 0
  nestDᵗ (pairᵗ a b)   = nestDᵗ a ⊔ nestDᵗ b
  nestDᵗ (fstᵗ p)      = nestDᵗ p
  nestDᵗ (sndᵗ p)      = nestDᵗ p
  nestDᵗ (inlᵗ a)      = nestDᵗ a
  nestDᵗ (inrᵗ a)      = nestDᵗ a
  nestDᵗ (caseᵗ s l r) = nestDᵗ s + (nestDᵗ l ⊔ nestDᵗ r)
  nestDᵗ (ifᵗ c a b)   = nestDᵗ c ⊔ nestDᵗ a ⊔ nestDᵗ b
  nestDᵗ (primᵗ _ a)   = nestDᵗ a
  nestDᵗ (strmᵗ e)     = nestDᵉ e

  nestDᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} →
    List (Tm Γ Δᵍ Δ Θ t) → ℕ
  nestDᵗˢ []       = 0
  nestDᵗˢ (y ∷ ys) = nestDᵗ y ⊔ nestDᵗˢ ys

------------------------------------------------------------------
-- EVERY NEST DEPTH IS UNDER A SIZE, over the whole term language at
-- once.  It is a fact about the TERM LANGUAGE and nothing else — no
-- schedule, no path, no store — which is what lets the root seeding
-- discharge its rank obligation with no induction over the machine at
-- all: the seed already carries the program's size and the slot
-- telescope's, and this says the nesting is under both.
--
-- The mutuality is the language's: a term may carry a stream and a
-- stream may carry terms, so the three arms are one induction.
------------------------------------------------------------------

mutual
  nestDᵉ≤sizeᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) → nestDᵉ e ≤ sizeᵉ e
  nestDᵉ≤sizeᵉ (input i)        = z≤n
  nestDᵉ≤sizeᵉ (ofᵉ ts)         = m≤n⇒m≤1+n (nestDᵗˢ≤sizeᵗˢ ts)
  nestDᵉ≤sizeᵉ emptyᵉ           = z≤n
  nestDᵉ≤sizeᵉ (mapᵉ f e)       = m≤n⇒m≤1+n (+-mono-≤ (nestDᵗ≤sizeᵗ f) (nestDᵉ≤sizeᵉ e))
  nestDᵉ≤sizeᵉ (takeᵉ c e)      = m≤n⇒m≤1+n (≤-trans (nestDᵉ≤sizeᵉ e) (m≤n+m (sizeᵉ e) (sizeᵗ c)))
  nestDᵉ≤sizeᵉ (scanᵉ f z e)    =
    m≤n⇒m≤1+n (+-mono-≤ (≤-trans (+-mono-≤ (nestDᵗ≤sizeᵗ z) (nestDᵗ≤sizeᵗ f))
                                 (≤-reflexive (+-comm (sizeᵗ z) (sizeᵗ f))))
                        (nestDᵉ≤sizeᵉ e))
  nestDᵉ≤sizeᵉ (mergeAllᵉ _ e)  = s≤s (nestDᵉ≤sizeᵉ e)
  nestDᵉ≤sizeᵉ (switchAllᵉ e)   = s≤s (nestDᵉ≤sizeᵉ e)
  nestDᵉ≤sizeᵉ (exhaustAllᵉ e)  = s≤s (nestDᵉ≤sizeᵉ e)
  nestDᵉ≤sizeᵉ (μᵉ e)           = m≤n⇒m≤1+n (nestDᵉ≤sizeᵉ e)
  nestDᵉ≤sizeᵉ (varᵉ x)         = z≤n
  nestDᵉ≤sizeᵉ (deferᵉ e)       = z≤n

  nestDᵗ≤sizeᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (f : Tm Γ Δᵍ Δ Θ t) → nestDᵗ f ≤ sizeᵗ f
  nestDᵗ≤sizeᵗ (varᵗ x)      = z≤n
  nestDᵗ≤sizeᵗ unit̂          = z≤n
  nestDᵗ≤sizeᵗ (bool̂ _)      = z≤n
  nestDᵗ≤sizeᵗ (nat̂ _)       = z≤n
  nestDᵗ≤sizeᵗ (pairᵗ a b)   =
    m≤n⇒m≤1+n (⊔-lub (≤-trans (nestDᵗ≤sizeᵗ a) (m≤m+n (sizeᵗ a) (sizeᵗ b)))
                     (≤-trans (nestDᵗ≤sizeᵗ b) (m≤n+m (sizeᵗ b) (sizeᵗ a))))
  nestDᵗ≤sizeᵗ (fstᵗ p)      = m≤n⇒m≤1+n (nestDᵗ≤sizeᵗ p)
  nestDᵗ≤sizeᵗ (sndᵗ p)      = m≤n⇒m≤1+n (nestDᵗ≤sizeᵗ p)
  nestDᵗ≤sizeᵗ (inlᵗ a)      = m≤n⇒m≤1+n (nestDᵗ≤sizeᵗ a)
  nestDᵗ≤sizeᵗ (inrᵗ a)      = m≤n⇒m≤1+n (nestDᵗ≤sizeᵗ a)
  nestDᵗ≤sizeᵗ (caseᵗ s l r) =
    m≤n⇒m≤1+n (≤-trans
      (+-mono-≤ (nestDᵗ≤sizeᵗ s)
                (⊔-lub (≤-trans (nestDᵗ≤sizeᵗ l) (m≤m+n (sizeᵗ l) (sizeᵗ r)))
                       (≤-trans (nestDᵗ≤sizeᵗ r) (m≤n+m (sizeᵗ r) (sizeᵗ l)))))
      (≤-reflexive (sym (+-assoc (sizeᵗ s) (sizeᵗ l) (sizeᵗ r)))))
  nestDᵗ≤sizeᵗ (ifᵗ c a b)   =
    m≤n⇒m≤1+n (⊔-lub (⊔-lub
      (≤-trans (nestDᵗ≤sizeᵗ c) (≤-trans (m≤m+n (sizeᵗ c) (sizeᵗ a)) (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b))))
      (≤-trans (nestDᵗ≤sizeᵗ a) (≤-trans (m≤n+m (sizeᵗ a) (sizeᵗ c)) (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b)))))
      (≤-trans (nestDᵗ≤sizeᵗ b) (m≤n+m (sizeᵗ b) (sizeᵗ c + sizeᵗ a))))
  nestDᵗ≤sizeᵗ (primᵗ _ a)   = m≤n⇒m≤1+n (nestDᵗ≤sizeᵗ a)
  nestDᵗ≤sizeᵗ (strmᵗ e)     = m≤n⇒m≤1+n (nestDᵉ≤sizeᵉ e)

  nestDᵗˢ≤sizeᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) → nestDᵗˢ ts ≤ sizeᵗˢ ts
  nestDᵗˢ≤sizeᵗˢ []       = z≤n
  nestDᵗˢ≤sizeᵗˢ (y ∷ ys) =
    ⊔-lub (≤-trans (nestDᵗ≤sizeᵗ y) (m≤m+n (sizeᵗ y) (sizeᵗˢ ys)))
          (≤-trans (nestDᵗˢ≤sizeᵗˢ ys) (m≤n+m (sizeᵗˢ ys) (sizeᵗ y)))

------------------------------------------------------------------
-- THE DEPTH READING IS UNMOVED BY A μ-UNFOLDING, and that is the fact
-- the rank peel turns on: the machine descends into the unfolding
-- while the witness keeps its rank, so the invariant's second
-- conjunct has to survive the substitution exactly.  `elimGExp`
-- substitutes only where the guarded variable is reachable, which is
-- under a `deferᵉ`, and the measure reads a `deferᵉ` as a zero leaf —
-- so every clause is homomorphic and the substituted positions are
-- never looked at.  The μ node is TRANSPARENT here, unlike the sync
-- spine's `suc`, so the unfolding is an outright EQUALITY of readings
-- rather than a decrement, and the peel re-establishes its conjunct
-- with no slack spent.
--
-- TWIN: `syncSize-elimG` is this same induction at the sync size,
--   proven, clause for clause; the two measures differ only in which
--   constructors they charge.
------------------------------------------------------------------

mutual
  nestD-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u) →
    nestDᵉ (elimGExp x cl e) ≡ nestDᵉ e
  nestD-elimG x cl (input i)       = refl
  nestD-elimG x cl (ofᵉ ts)        = nestD-elimGᵗˢ x cl ts
  nestD-elimG x cl emptyᵉ          = refl
  nestD-elimG x cl (mapᵉ f e)      =
    cong₂ _+_ (nestD-elimGᵗ x cl f) (nestD-elimG x cl e)
  nestD-elimG x cl (takeᵉ c e)     = nestD-elimG x cl e
  nestD-elimG x cl (scanᵉ f z e)   =
    cong₂ _+_ (cong₂ _+_ (nestD-elimGᵗ x cl z) (nestD-elimGᵗ x cl f))
              (nestD-elimG x cl e)
  nestD-elimG x cl (mergeAllᵉ _ e)   = cong suc (nestD-elimG x cl e)
  nestD-elimG x cl (switchAllᵉ e)  = cong suc (nestD-elimG x cl e)
  nestD-elimG x cl (exhaustAllᵉ e) = cong suc (nestD-elimG x cl e)
  nestD-elimG x cl (μᵉ e)          = nestD-elimG (there x) cl e
  nestD-elimG x cl (varᵉ y)        = refl
  nestD-elimG x cl (deferᵉ e)      = refl

  nestD-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (f : Tm Γ Δᵍ Δ Θ u) →
    nestDᵗ (elimGTm x cl f) ≡ nestDᵗ f
  nestD-elimGᵗ x cl (varᵗ y)      = refl
  nestD-elimGᵗ x cl unit̂          = refl
  nestD-elimGᵗ x cl (bool̂ b)      = refl
  nestD-elimGᵗ x cl (nat̂ k)       = refl
  nestD-elimGᵗ x cl (pairᵗ a b)   =
    cong₂ _⊔_ (nestD-elimGᵗ x cl a) (nestD-elimGᵗ x cl b)
  nestD-elimGᵗ x cl (fstᵗ p)      = nestD-elimGᵗ x cl p
  nestD-elimGᵗ x cl (sndᵗ p)      = nestD-elimGᵗ x cl p
  nestD-elimGᵗ x cl (inlᵗ a)      = nestD-elimGᵗ x cl a
  nestD-elimGᵗ x cl (inrᵗ a)      = nestD-elimGᵗ x cl a
  nestD-elimGᵗ x cl (caseᵗ s l r) =
    cong₂ _+_ (nestD-elimGᵗ x cl s)
              (cong₂ _⊔_ (nestD-elimGᵗ x cl l) (nestD-elimGᵗ x cl r))
  nestD-elimGᵗ x cl (ifᵗ c a b)   =
    cong₂ _⊔_ (cong₂ _⊔_ (nestD-elimGᵗ x cl c) (nestD-elimGᵗ x cl a))
              (nestD-elimGᵗ x cl b)
  nestD-elimGᵗ x cl (primᵗ op a)  = nestD-elimGᵗ x cl a
  nestD-elimGᵗ x cl (strmᵗ e)     = nestD-elimG x cl e

  nestD-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    nestDᵗˢ (elimGTms x cl ts) ≡ nestDᵗˢ ts
  nestD-elimGᵗˢ x cl []       = refl
  nestD-elimGᵗˢ x cl (y ∷ ys) =
    cong₂ _⊔_ (nestD-elimGᵗ x cl y) (nestD-elimGᵗˢ x cl ys)

-- the peel's own equation: the redex and its unfolding read the same,
-- since `nestDᵉ` is transparent at `μᵉ`
nestD-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
  nestDᵉ (unfoldμ body) ≡ nestDᵉ (μᵉ body)
nestD-unfoldμ body = nestD-elimG (here refl) (μᵉ body) body
