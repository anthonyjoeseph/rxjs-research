------------------------------------------------------------------
-- THE MINIATURE EVALUATOR — a spike, not proof code.
--
-- It exists to answer ONE question that no amount of reading the real
-- evaluator can settle: does Agda accept a Bove-Capretta domain
-- predicate whose constructor quantifies over the function's OWN
-- OUTPUT?  That is the shape `Rx.Evaluator`'s `subscribeInner` edge
-- forces — an inner subscription's argument is a value drawn from a
-- burst that a recursive call produced — and it is the reason plain
-- `Acc`-recursion cannot see the edge.  Induction-recursion can, in
-- principle; whether Agda's positivity and termination checkers agree
-- is a fact about the implementation, and the only way to learn it is
-- to type it.
--
-- This tree is OUTSIDE every claim root and outside `agda/src` on
-- purpose.  It is a temporary exception to the wiring law, held for
-- exactly as long as the question is open: it is deleted, or its
-- findings are promoted into `src` as a design ruling, and nothing in
-- `src` may ever import it.
--
-- WHAT IT MODELS, and what it deliberately does not.  All four
-- synchronous re-entry edges of the real evaluator are here:
--
--   E1  structural descent      `mapᵉ`/`scanᵉ`/`allᵉ` into its source
--   E2  the μ unfold            `μᵉ b ↦ substE b (μᵉ b)`, gated by `deferᵉ`
--   E3  the inner hop           `allᵉ` subscribing to an emitted `obsᵛ`
--   E4  the share connect       `slotᵉ i` connecting an unconnected slot
--
-- What is absent is the schedule: one instant, no ticks, no drain, no
-- `Fuel`.  `Fuel` is not in scope — it truncates the schedule honestly
-- and is not what this spike is about.  `deferᵉ` therefore parks and
-- emits nothing, which is exactly its role as the gate that makes
-- synchronous self-reference a type error in the real language.
------------------------------------------------------------------
module Spike.Mini where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _⊔_; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------
-- THE LANGUAGE.  Values carry reified observables, which is what makes
-- the inner hop a real edge rather than a structural descent: `obsᵛ`
-- holds an `Exp` that no subterm relation on the emitter can reach.
------------------------------------------------------------------

data Val : Set
data Exp : Set
data Tm  : Set

data Val where
  natᵛ : ℕ → Val
  obsᵛ : Exp → Val

-- A step template, read as a function of (accumulator, incoming
-- value).  `nestᵗ` is the whole reason `Tm` is not just a constant: it
-- REIFIES its argument behind an `allᵉ`, so folding it raises the hop
-- depth by one per fold.  That is the accumulator refold in miniature,
-- and it is the clause the real `hopDᵉ` prices with `(2 + pm)^V`.
data Tm where
  inᵗ    : Tm
  accᵗ   : Tm
  konstᵗ : Val → Tm
  nestᵗ  : Tm → Tm

data Exp where
  ofᵉ    : List Val → Exp
  mapᵉ   : Tm → Exp → Exp
  scanᵉ  : Tm → Val → Exp → Exp
  allᵉ   : Exp → Exp
  μᵉ     : Exp → Exp
  varᵉ   : Exp
  deferᵉ : Exp → Exp
  slotᵉ  : ℕ → Exp

------------------------------------------------------------------
-- TEMPLATE EVALUATION and the μ unfold.  `substE` copies the recursive
-- occurrence under `deferᵉ` and nowhere else, which is what makes the
-- unfold a decrease in the innermost component below.
------------------------------------------------------------------

evalTm : Tm → Val → Val → Val
evalTm inᵗ        a v = v
evalTm accᵗ       a v = a
evalTm (konstᵗ k) a v = k
evalTm (nestᵗ t)  a v = obsᵛ (allᵉ (ofᵉ (evalTm t a v ∷ [])))

substE : Exp → Exp → Exp
substV : Val → Exp → Val
substL : List Val → Exp → List Val
substT : Tm → Exp → Tm

substE (ofᵉ vs)      m = ofᵉ (substL vs m)
substE (mapᵉ f e)    m = mapᵉ (substT f m) (substE e m)
substE (scanᵉ f z e) m = scanᵉ (substT f m) (substV z m) (substE e m)
substE (allᵉ e)      m = allᵉ (substE e m)
substE (μᵉ b)        m = μᵉ b
substE varᵉ          m = m
substE (deferᵉ b)    m = deferᵉ (substE b m)
substE (slotᵉ i)     m = slotᵉ i

substV (natᵛ n) m = natᵛ n
substV (obsᵛ e) m = obsᵛ (substE e m)

substL []       m = []
substL (v ∷ vs) m = substV v m ∷ substL vs m

substT inᵗ        m = inᵗ
substT accᵗ       m = accᵗ
substT (konstᵗ k) m = konstᵗ (substV k m)
substT (nestᵗ t)  m = nestᵗ (substT t m)

unfoldμ : Exp → Exp
unfoldμ b = substE b (μᵉ b)

------------------------------------------------------------------
-- SLOTS.  A flat table; `slotᵉ i` reads entry `i`.  The connected set
-- is a list of indices, EXTENDED BEFORE the recursive call, exactly as
-- `sharedConnect` extends `connectedShares` before recursing.
------------------------------------------------------------------

memberℕ : ℕ → List ℕ → Bool
memberℕ i []       = false
memberℕ i (j ∷ js) = if i ≡ᵇ j then true else memberℕ i js

module Run (sl : List Exp) where

  nth : ℕ → List Exp → Exp
  nth i       []       = ofᵉ []
  nth zero    (e ∷ _)  = e
  nth (suc i) (_ ∷ es) = nth i es

  def : ℕ → Exp
  def i = nth i sl

  ------------------------------------------------------------------
  -- THE DOMAIN PREDICATE AND THE EVALUATOR, defined simultaneously.
  --
  -- `dAll` is the point of the whole file: its second field is a
  -- witness ABOUT `proj₁ (run e cs d)` — the burst the first field's
  -- own run produces.  Nothing structural on `allᵉ e` mentions those
  -- values, so this is the edge that forces induction-recursion.
  ------------------------------------------------------------------

  data Dom  : Exp → List ℕ → Set
  data DomL : List Val → List ℕ → Set
  run  : ∀ e  cs → Dom  e  cs → List Val × List ℕ
  runL : ∀ vs cs → DomL vs cs → List Val × List ℕ

  data Dom where
    dOf    : ∀ {vs cs} → Dom (ofᵉ vs) cs
    dMap   : ∀ {f e cs} → Dom e cs → Dom (mapᵉ f e) cs
    dScan  : ∀ {f z e cs} → Dom e cs → Dom (scanᵉ f z e) cs
    dMu    : ∀ {b cs} → Dom (unfoldμ b) cs → Dom (μᵉ b) cs
    dVar   : ∀ {cs} → Dom varᵉ cs
    dDefer : ∀ {b cs} → Dom (deferᵉ b) cs
    dSlotC : ∀ {i cs} → memberℕ i cs ≡ true → Dom (slotᵉ i) cs
    dSlotN : ∀ {i cs} → memberℕ i cs ≡ false →
             Dom (def i) (i ∷ cs) → Dom (slotᵉ i) cs
    dAll   : ∀ {e cs} (d : Dom e cs) →
             DomL (proj₁ (run e cs d)) (proj₂ (run e cs d)) →
             Dom (allᵉ e) cs

  -- the inner subscriptions of one burst, threaded left to right so a
  -- slot an earlier inner connects is seen by the later ones
  data DomL where
    dLNil : ∀ {cs} → DomL [] cs
    dLNat : ∀ {n vs cs} → DomL vs cs → DomL (natᵛ n ∷ vs) cs
    dLObs : ∀ {o vs cs} (d : Dom o cs) →
            DomL vs (proj₂ (run o cs d)) → DomL (obsᵛ o ∷ vs) cs

  run (ofᵉ vs)      cs dOf           = vs , cs
  run (mapᵉ f e)    cs (dMap d)      =
    let (b , cs₁) = run e cs d in mapB f b , cs₁
    where
      mapB : Tm → List Val → List Val
      mapB f []       = []
      mapB f (v ∷ vs) = evalTm f v v ∷ mapB f vs
  run (scanᵉ f z e) cs (dScan d)     =
    let (b , cs₁) = run e cs d in foldB f z b , cs₁
    where
      foldB : Tm → Val → List Val → List Val
      foldB f a []       = []
      foldB f a (v ∷ vs) = let a′ = evalTm f a v in a′ ∷ foldB f a′ vs
  run (μᵉ b)        cs (dMu d)       = run (unfoldμ b) cs d
  run varᵉ          cs dVar          = [] , cs
  run (deferᵉ b)    cs dDefer        = [] , cs
  run (slotᵉ i)     cs (dSlotC _)    = [] , cs
  run (slotᵉ i)     cs (dSlotN _ d)  = run (def i) (i ∷ cs) d
  run (allᵉ e)      cs (dAll d ds)   =
    runL (proj₁ (run e cs d)) (proj₂ (run e cs d)) ds

  runL []              cs dLNil        = [] , cs
  runL (natᵛ n  ∷ vs)  cs (dLNat ds)   = runL vs cs ds
  runL (obsᵛ o  ∷ vs)  cs (dLObs d ds) =
    let (b₁ , cs₁) = run o cs d
        (b₂ , cs₂) = runL vs cs₁ ds
    in b₁ ++ b₂ , cs₂
