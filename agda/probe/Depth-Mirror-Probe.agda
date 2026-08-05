------------------------------------------------------------------
-- THE DEPTH MIRROR, ON A MINI-EVALUATOR — the elaboration gate for
-- Unit 3 (WORKER-HANDOFF § UNIT 3).  Nothing here is about the real
-- evaluator; it is about whether the DESIGN's four mechanisms elaborate
-- at all, settled in seconds instead of one 44-minute Subscribe-Face
-- recheck per question.
--
-- § 0  a two-dispatch mini-evaluator: a `Dec`-forced branch (the model
--   of `innerFinish`'s `w ≟ᵗ s`) and a `Maybe`-scrutinee head.
-- § 1  its MIRROR, per rules R1-R5: one head per evaluator head, same
--   argument list, each clause the `⊔` of its callees' mirrors on the
--   same expressions, `suc` at the two spending arcs, and NO `with` —
--   the type-forced dispatch delegates to a head taking the scrutinee
--   as a real argument (R4b).  R7 is tested by the fact that this
--   typechecks at all: the mirror's termination is the evaluator's.
-- § 2  a fake caps family consuming `mirror ≤ dep`, exercising all
--   three supply moves — (a) projection through `⊔`, (b) the spend:
--   `dep = zero` ABSURD and `suc dep′` peeled, (c) the type-forced
--   dispatch, via the helper head.
-- § 3  and the `with` route for move (c), for any real site that must
--   dispatch in place: abstracting `dpt` ALONGSIDE the scrutinee
--   refines its type, so the mirror's clause fires in the branch.
--
-- The bodies are all `tt` on purpose.  Every claim of the design is in
-- a `where`-bound signature, which Agda checks whether or not the body
-- uses it — so a green check here means every supply term the real
-- pass will write has been elaborated once already.
------------------------------------------------------------------
module Depth-Mirror-Probe where

open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m; n≤1+n)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------
-- § 0.  THE MINI-EVALUATOR.  `t : ℕ` stands for the whole evaluator
-- state; the heads thread it exactly as the real ones thread
-- `sched`/`st`, so the mirror has post-states to recompute.
------------------------------------------------------------------

data Ty : Set where
  natᵗ boolᵗ : Ty

_≟ᵗ_ : (a b : Ty) → Dec (a ≡ b)
natᵗ  ≟ᵗ natᵗ  = yes refl
boolᵗ ≟ᵗ boolᵗ = yes refl
natᵗ  ≟ᵗ boolᵗ = no λ ()
boolᵗ ≟ᵗ natᵗ  = no λ ()

data Ex : Set where
  lf   : Ex
  allᵉ : Ex → Ex          -- an *All: subscribes its source under a frame

data Fr : Set where
  mapf    : Fr            -- reaches no subscribe
  thruOut : Fr            -- SPENDING ARC 1
  fromIn  : Fr            -- reaches the finish

data Nd : Set where
  cst : Ty → List Ex → Nd  -- concat-st: a queue stored at a type

subE   : ℕ → Ex → ℕ → ℕ
walkE  : ℕ → List Ex → ℕ → ℕ
frameE : ℕ → Ty → Fr → List Ex → ℕ → ℕ
finE   : ℕ → Ty → Maybe Nd → ℕ → ℕ
finCE  : ℕ → (w s : Ty) → List Ex → ℕ → Dec (w ≡ s) → ℕ
drainE : ℕ → List Ex → ℕ → ℕ

subE zero    e        t = t
subE (suc g) lf       t = suc t
subE (suc g) (allᵉ b) t = frameE g natᵗ thruOut (b ∷ []) (subE g b t)

walkE g []       t = t
walkE g (o ∷ os) t = walkE g os (subE g o t)

frameE g s mapf    os t = t
frameE g s thruOut os t = walkE g os t
frameE g s fromIn  os t = finE g s (just (cst s os)) t

finE g s (just (cst w q)) t = finCE g w s q t (w ≟ᵗ s)
finE g s nothing          t = t

finCE g w s q t (yes refl) = drainE g q t
finCE g w s q t (no _)     = t

drainE g []      t = t
drainE g (o ∷ q) t = drainE g q (subE g o t)

------------------------------------------------------------------
-- § 1.  THE MIRROR (R1-R5).  Note `dFrame`'s thruOut arm and
-- `dFinC`'s `yes refl` arm: those two `suc`s are the whole design.
------------------------------------------------------------------

dSub   : ℕ → Ex → ℕ → ℕ
dWalk  : ℕ → List Ex → ℕ → ℕ
dFrame : ℕ → Ty → Fr → List Ex → ℕ → ℕ
dFin   : ℕ → Ty → Maybe Nd → ℕ → ℕ
dFinC  : ℕ → (w s : Ty) → List Ex → ℕ → Dec (w ≡ s) → ℕ
dDrain : ℕ → List Ex → ℕ → ℕ

dSub zero    e        t = 0
dSub (suc g) lf       t = 0
dSub (suc g) (allᵉ b) t =
  dSub g b t ⊔ dFrame g natᵗ thruOut (b ∷ []) (subE g b t)

dWalk g []       t = 0
dWalk g (o ∷ os) t = dSub g o t ⊔ dWalk g os (subE g o t)

dFrame g s mapf    os t = 0
dFrame g s thruOut os t = suc (dWalk g os t)
dFrame g s fromIn  os t = dFin g s (just (cst s os)) t

dFin g s (just (cst w q)) t = dFinC g w s q t (w ≟ᵗ s)
dFin g s nothing          t = 0

dFinC g w s q t (yes refl) = suc (dDrain g q t)
dFinC g w s q t (no _)     = 0

dDrain g []      t = 0
dDrain g (o ∷ q) t = dSub g o t ⊔ dDrain g q (subE g o t)

------------------------------------------------------------------
-- § 2.  THE FAKE CAPS FAMILY, and the three supply moves.
------------------------------------------------------------------

Ok : Set
Ok = ⊤

sub-caps   : ∀ (dep g : ℕ) (e : Ex) (t : ℕ) → dSub g e t ≤ dep → Ok
walk-caps  : ∀ (dep g : ℕ) (os : List Ex) (t : ℕ) → dWalk g os t ≤ dep → Ok
frame-caps : ∀ (dep g : ℕ) (s : Ty) (f : Fr) (os : List Ex) (t : ℕ) →
             dFrame g s f os t ≤ dep → Ok
fin-caps   : ∀ (dep g : ℕ) (s : Ty) (nd : Maybe Nd) (t : ℕ) →
             dFin g s nd t ≤ dep → Ok
finC-caps  : ∀ (dep g : ℕ) (w s : Ty) (q : List Ex) (t : ℕ)
             (dc : Dec (w ≡ s)) → dFinC g w s q t dc ≤ dep → Ok
drain-caps : ∀ (dep g : ℕ) (q : List Ex) (t : ℕ) → dDrain g q t ≤ dep → Ok

-- (a) PROJECTION.  The caller's `dpt` reduces to a `⊔` of the callees'
-- mirrors in the clause's own pattern context, so each callee is fed by
-- one lattice projection composed with `dpt` — and nothing else
sub-caps dep zero    e  t dpt = tt
sub-caps dep (suc g) lf t dpt = tt
sub-caps dep (suc g) (allᵉ b) t dpt = tt
  where
  pL : dSub g b t ≤ dep
  pL = ≤-trans (m≤m⊔n _ _) dpt
  pR : dFrame g natᵗ thruOut (b ∷ []) (subE g b t) ≤ dep
  pR = ≤-trans (m≤n⊔m _ _) dpt
  rL : Ok
  rL = sub-caps dep g b t pL
  rR : Ok
  rR = frame-caps dep g natᵗ thruOut (b ∷ []) (subE g b t) pR

walk-caps dep g []       t dpt = tt
walk-caps dep g (o ∷ os) t dpt = tt
  where
  pL : dSub g o t ≤ dep
  pL = ≤-trans (m≤m⊔n _ _) dpt
  pR : dWalk g os (subE g o t) ≤ dep
  pR = ≤-trans (m≤n⊔m _ _) dpt
  rL : Ok
  rL = sub-caps dep g o t pL
  rR : Ok
  rR = walk-caps dep g os (subE g o t) pR

drain-caps dep g []      t dpt = tt
drain-caps dep g (o ∷ q) t dpt = tt
  where
  pL : dSub g o t ≤ dep
  pL = ≤-trans (m≤m⊔n _ _) dpt
  pR : dDrain g q (subE g o t) ≤ dep
  pR = ≤-trans (m≤n⊔m _ _) dpt
  rL : Ok
  rL = sub-caps dep g o t pL
  rR : Ok
  rR = drain-caps dep g q (subE g o t) pR

-- (b) THE SPEND, arc 1.  `dep = zero` is ABSURD BY CONSTRUCTOR — the
-- mirror clause reduces `dpt` to `suc _ ≤ zero`, which is uninhabited —
-- and that is exactly how Subscribe-Face:2280 dies.  At `suc dp` the
-- hypothesis peels an `s≤s` and the callee runs one depth lower
frame-caps dep g s mapf os t dpt = tt
frame-caps zero g s thruOut os t ()
frame-caps (suc dp) g s thruOut os t (s≤s p) = tt
  where
  r : Ok
  r = walk-caps dp g os t p
frame-caps dep g s fromIn os t dpt = fin-caps dep g s (just (cst s os)) t dpt

-- (c) THE TYPE-FORCED DISPATCH, via the helper head (R4b): no `with` on
-- the caps side either, so nothing has to be abstracted
fin-caps dep g s nothing          t dpt = tt
fin-caps dep g s (just (cst w q)) t dpt = finC-caps dep g w s q t (w ≟ᵗ s) dpt

-- and THE SPEND, arc 2 — the model of Subscribe-Face:1834.  Note the
-- `no` clause is NOT absurd at `dep = zero`: that branch spends nothing,
-- which is why the case on `dep` has to sit BELOW the dispatch
finC-caps dep g w s q t (no _) dpt = tt
finC-caps zero g w s q t (yes refl) ()
finC-caps (suc dp) g w s q t (yes refl) (s≤s p) = tt
  where
  r : Ok
  r = drain-caps dp g q t p

------------------------------------------------------------------
-- § 3.  THE `with` ROUTE for move (c), for a real site that cannot
-- delegate — abstract `dpt` ALONGSIDE the scrutinee and its type is
-- refined with the goal, so the mirror's clause fires in the branch.
-- If this failed, every caps clause that already `with`s a type-forced
-- scrutinee would have to be restructured; it does not fail.
------------------------------------------------------------------

fin-caps′ : ∀ (dep g : ℕ) (s : Ty) (nd : Maybe Nd) (t : ℕ) →
            dFin g s nd t ≤ dep → Ok
fin-caps′ dep g s nothing          t dpt = tt
fin-caps′ dep g s (just (cst w q)) t dpt with w ≟ᵗ s | dpt
... | no _     | dpt′ = tt
... | yes refl | dpt′ = drain-caps dep g q t (≤-trans (n≤1+n _) dpt′)

------------------------------------------------------------------
-- § 4.  THE SPEND *INSIDE* A with-CONTINUATION, which is the exact shape
-- `innerFinish-caps`'s concat clause needs and the one shape § 2 does not
-- cover: there the dispatch is delegated to a helper head that can match
-- `dep` in its own LHS, but the real clause reaches `yes refl` through a
-- `with` it already had, and the callee whose depth must descend is bound
-- in that branch's `where`.  So `dep` has to be split a SECOND time,
-- nested under the first `with`, and the tail `dpt″` must still refine.
--
-- It does, and the zero branch is absurd exactly as it is at top level.
-- Note both scrutinees have to be re-listed in the nested `with`: `dep`
-- to split it, and `dpt′` to carry its refinement down.
------------------------------------------------------------------

fin-caps″ : ∀ (dep g : ℕ) (s : Ty) (nd : Maybe Nd) (t : ℕ) →
            dFin g s nd t ≤ dep → Ok
fin-caps″ dep g s nothing          t dpt = tt
fin-caps″ dep g s (just (cst w q)) t dpt with w ≟ᵗ s | dpt
... | no _     | dpt′ = tt
... | yes refl | dpt′ with dep | dpt′
...   | zero   | ()
...   | suc dp | s≤s dpt″ = tt
  where
  -- the callee runs one depth LOWER, off the peeled hypothesis — and it
  -- is bound HERE, so the split cannot be deferred to a helper
  r : Ok
  r = drain-caps dp g q t dpt″
