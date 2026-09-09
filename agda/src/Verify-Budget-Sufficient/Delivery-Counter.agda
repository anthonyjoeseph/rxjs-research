------------------------------------------------------------------
-- THE NODE COUNTER ONLY RISES ACROSS THE DELIVERY CLIQUE.
--
-- THE FACT.  `foldPath`, `dispatchShare` and `shareGo` never LOWER
-- `Sched.nextNode`.  Nothing here mints a node -- the clique walks a
-- chain that already exists -- so the counter moves only where a
-- `stepFrame` re-enters a subscribe, and a subscribe mints upward.
--
-- WHY IT IS OWED SEPARATELY FROM `.Node-Fresh`, and this is the whole
-- design point.  That ring proves a STRONGER pair -- the counter rises
-- AND every cell below a watermark is frozen -- at sixteen constructs,
-- and the delivery clique is precisely the region it does not reach.
-- It cannot reach it: `foldPath` steps frames it did not mint, whose
-- nids are BELOW the counter, so the freeze half is FALSE here at any
-- watermark a caller would want.  Splitting the counter half off is
-- what makes the fact statable at all, and it is the half every
-- consumer of this module actually spends.
--
-- WHAT THE FRAME ARM COSTS, which is nothing.  `stepFrame-fresh` takes
-- `w ≤ Sched.nextNode sched` and `frameAbove w f`; at `w = 0` both are
-- free, and the record's `nxMono` field is the conclusion wanted.  So
-- the ring is spent at its weakest instantiation and the induction
-- below carries no store obligation at all.
--
-- TWIN: `foldPath-deliv` in `.Deliveries` -- the same three-member
--   induction over the same clique, at the delivery ledger's order
--   instead of the counter's.  Its clauses correspond one for one, down
--   to the two share-boundary bookkeeping steps that have to be shown
--   invisible before the recursion can be threaded through them.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Delivery-Counter where

open import Data.Bool  using (Bool; true; false; if_then_else_)
open import Data.Nat   using (ℕ; zero; suc; _≤_; z≤n; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive)
open import Data.List  using (List; []; _∷_; _++_)
open import Data.Bool.ListAction using (any)
open import Data.Fin   using (Fin; toℕ)
open import Data.Vec   using (lookup)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit  using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Rx.Prim using (Gas; Tick; Id; Source; InstEvent; close; exhausted)
open import Rx.Exp  using (Ctx; Closed; Val)
open import Rx.Evaluator using
  (Sched; EvalSt; Arrival; RegId; Path; Frame; Stream;
   map-f; scan-f; take-f; from-inner; thru-outer; root; share-sink; _↠_;
   stepFrame; foldPath; dispatchShare; shareGo;
   shareLatch; shareAdmit; shareFinish; chainStep;
   budgetAt; arrTy; arrTick; arrSource; arrVal)
open import Verify-Budget-Sufficient.Node-Fresh
  using (FreshC; frameAbove; stepFrame-fresh)

------------------------------------------------------------------
-- the ring at its weakest watermark
------------------------------------------------------------------

abstract

  -- EVERY frame sits above zero, and the four node-naming shapes say
  -- so by `z≤n`.  This is what lets a chain of frames the walk does
  -- NOT own be stepped under a ring whose arms are keyed on ownership
  frameAbove-zero : ∀ {n} {Γ : Ctx n} {s u} (f : Frame Γ s u) →
                    frameAbove 0 f
  frameAbove-zero (map-f _)          = tt
  frameAbove-zero (scan-f _ _)       = z≤n
  frameAbove-zero (take-f _)         = z≤n
  frameAbove-zero (from-inner _ _ _) = z≤n , z≤n
  frameAbove-zero (thru-outer _ _)   = z≤n

  stepFrame-nextNode : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (g : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    Sched.nextNode sched ≤
      Sched.nextNode (proj₁ (proj₂ (proj₂ (proj₂
        (stepFrame g id now f κ vals fin sched st)))))
  stepFrame-nextNode g id now f κ vals fin sched st =
    FreshC.nxMono
      (stepFrame-fresh 0 g id now f κ vals fin sched st z≤n (frameAbove-zero f))

  -- the share boundary's own bookkeeping is invisible to the counter:
  -- the latch writes the STATE only, and the finish rewrites `live`
  shareFinish-nextNode : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (i : Fin n) (fin : Bool) (out : Stream Γ t × Sched Γ × EvalSt e) →
    Sched.nextNode (proj₁ (proj₂ (shareFinish i fin out)))
      ≡ Sched.nextNode (proj₁ (proj₂ out))
  shareFinish-nextNode i false out = refl
  shareFinish-nextNode i true  out = refl

------------------------------------------------------------------
-- the walk
--
-- The recursion is lexicographic on (dispatch gas, path), exactly as
-- the evaluator's: a frame hop shortens the path at constant gas, the
-- share hop peels one gas.
------------------------------------------------------------------

abstract

  foldPath-nextNode : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    (p : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.nextNode sched ≤
      Sched.nextNode (proj₁ (proj₂
        (foldPath sf gas id now envSrc p vals evs fin sched st)))

  dispatchShare-nextNode : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.nextNode sched ≤
      Sched.nextNode (proj₁ (proj₂
        (dispatchShare {t = t} sf gas id now i vals fin sched st)))

  shareGo-nextNode : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.nextNode sched ≤
      Sched.nextNode (proj₁ (proj₂
        (shareGo sf gas id now i vals fin ps sched st)))

  foldPath-nextNode sf gas id now envSrc root vals evs fin sched st = ≤-refl
  foldPath-nextNode sf gas id now envSrc (share-sink i) vals evs fin sched st =
    dispatchShare-nextNode sf gas id now i vals fin sched st
  foldPath-nextNode sf gas id now envSrc (f ↠ path′) vals evs fin sched st =
    let r = stepFrame sf id now f path′ vals fin sched st in
    ≤-trans (stepFrame-nextNode sf id now f path′ vals fin sched st)
            (foldPath-nextNode sf gas id now envSrc path′ (proj₁ r)
               (evs ++ proj₁ (proj₂ r)) (proj₁ (proj₂ (proj₂ r)))
               (proj₁ (proj₂ (proj₂ (proj₂ r))))
               (proj₂ (proj₂ (proj₂ (proj₂ r)))))

  dispatchShare-nextNode sf zero id now i vals fin sched st = ≤-refl
  dispatchShare-nextNode sf (suc gas) id now i vals fin sched st =
    ≤-trans
      (shareGo-nextNode sf gas id now i vals fin
         (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st))
      (≤-reflexive
        (sym (shareFinish-nextNode i fin
               (shareGo sf gas id now i vals fin
                 (shareAdmit i (EvalSt.registry st)) sched
                 (shareLatch i fin st)))))

  shareGo-nextNode sf gas id now i vals fin []              sched st = ≤-refl
  shareGo-nextNode sf gas id now i vals fin ((rid , p) ∷ ps) sched st
    with any (_≡ᵇ rid) (EvalSt.cancelled st)
  ... | true  = shareGo-nextNode sf gas id now i vals fin ps sched st
  ... | false =
        let fp = foldPath sf gas id now (toℕ i) p vals
                   (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched
                   (record st { delivered = rid ∷ EvalSt.delivered st }) in
        ≤-trans (foldPath-nextNode sf gas id now (toℕ i) p vals
                   (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched
                   (record st { delivered = rid ∷ EvalSt.delivered st }))
                (shareGo-nextNode sf gas id now i vals fin ps
                   (proj₁ (proj₂ fp)) (proj₂ (proj₂ fp)))

  -- the arrival seed is `foldPath` with the arrival's own payload, so
  -- the corollary is the parent applied and nothing else
  chainStep-nextNode : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.nextNode sched ≤
      Sched.nextNode (proj₁ (proj₂ (chainStep id a path sched st)))
  chainStep-nextNode {n = n} {e = e} id a path sched st =
    foldPath-nextNode (budgetAt e (Sched.slots sched) id) n id (arrTick a)
      (arrSource a) path (arrVal a ∷ [])
      (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
      (Arrival.isLast a) sched st
