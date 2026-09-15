------------------------------------------------------------------
-- THE UNCONNECTED COUNT ONLY FALLS ACROSS A SUBSCRIPTION.
------------------------------------------------------------------

-- WHAT THIS ESTABLISHES.  The count is the outermost component of the
-- order the subscription machine descends on, so a clause handing a
-- LATER state onward has to say the count did not rise under it.  It
-- does not: `connectedShares` is written in exactly two places, the two
-- connects, and both PREPEND an index -- which lowers a share's own
-- contribution from one to zero and raises no other.  Everywhere else
-- the set is carried through a record update that does not name it.
--
-- SO THE WALK IS THE SLOT WALK'S SHAPE WITH ONE ARITHMETIC LEAF.  Same
-- SCC, same recursion, `≤-refl` where the equation was `refl` -- and at
-- the two connects the recursion lands at the extended set, where the
-- cons lemma closes the gap.
module Rx.Evaluator.Drops-Unconn where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; _∷_; tabulate)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-mono-≤)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Nat.ListAction using (sum)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Id; Source; Tick)
open import Rx.Exp using (Ctx; Closed; Val; obs)
open import Rx.Slots using (Slots; shared; scripted)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; AllOp; NodeId;
  NodeState; Frame; take-st; scan-st; takeVals; takeDispatch; thruWrap;
  switchKill; lookupNode; mergeAll-st; switch-st; exhaust-st;
  mergeAllᵒ; switchᵒ; exhaustᵒ; unconn; unconnAt; memberSource; sameSource)
open import Rx.Evaluator.Domain using (subscribeE⇓; subscribeAll⇓; pushBurst⇓;
  stepFrame⇓; innerReact⇓; innerFinish⇓; mergeAllDrain⇓; thruWalk⇓;
  thruConsume⇓; subscribeInner⇓; sharedConnect⇓; subscribeSharedSlot⇓;
  subs-floor; subs-shared; subs-hot-done; subs-hot-live; subs-cold-sync;
  subs-cold-async; subs-of; subs-empty; subs-map; subs-take-zero;
  subs-take-suc; subs-scan; subs-merge-all; subs-switch-all; subs-exhaust-all;
  subs-μ; subs-defer; inner;
  consume-all-sub; consume-all-enqueue; consume-all-nil; consume-switch-sub;
  consume-switch-nil; consume-exhaust-sub; consume-exhaust-nil;
  walk-nil; walk-cons; drain-nil; drain-no-room; drain-room;
  finish-all-drain; finish-switch-clear; finish-exhaust-clear; finish-nil;
  react-false; react-alive; react-dead;
  step-map; step-scan; step-scan-nil; step-take; step-from-inner;
  step-thru-outer; push-nil; push-cons; sub-all;
  connect-live; connect-died; slot-spent; slot-join; slot-connect)

------------------------------------------------------------------
-- THE ARITHMETIC LEAF.
------------------------------------------------------------------

-- pointwise sums over the telescope
sum-tab-mono : ∀ {m} (f g : Fin m → ℕ) → (∀ i → f i ≤ g i) →
  sum (tabulate f) ≤ sum (tabulate g)
sum-tab-mono {zero}  f g h = z≤n
sum-tab-mono {suc m} f g h =
  +-mono-≤ (h fzero) (sum-tab-mono _ _ (λ i → h (fsuc i)))

-- adding a member never raises any slot's contribution
unconnAt-cons-≤ : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
  (s : Source) (i : Fin n) → unconnAt sl (s ∷ cs) i ≤ unconnAt sl cs i
unconnAt-cons-≤ sl cs s i with sl i
... | scripted _ = z≤n
... | shared _ with memberSource (toℕ i) cs
...   | true  rewrite ∨-zeroʳ (sameSource (toℕ i) s) = z≤n
...   | false with sameSource (toℕ i) s ∨ false
...     | true  = z≤n
...     | false = ≤-refl

-- and so the count itself only falls
unconn-cons-≤ : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
  (s : Source) → unconn sl (s ∷ cs) ≤ unconn sl cs
unconn-cons-≤ sl cs s = sum-tab-mono _ _ (unconnAt-cons-≤ sl cs s)

------------------------------------------------------------------
-- THE THREE FUNCTIONS A CLAUSE HANDS A STATE TO.
------------------------------------------------------------------

-- None of them names the share set, so each is `≤-refl` under whatever
-- split its own body takes.

take-unconn : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sl : Slots Γ) (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (ns : Maybe (NodeState Γ)) →
  unconn sl (EvalSt.connectedShares (proj₂ (proj₂ (proj₂ (proj₂
    (takeDispatch {e = e} nid vals fin sched st ns))))))
    ≤ unconn sl (EvalSt.connectedShares st)
take-unconn sl nid vals fin sched st (just (take-st k))
  with proj₂ (proj₂ (takeVals k vals))
... | true  = ≤-refl
... | false = ≤-refl
take-unconn sl nid vals fin sched st nothing                      = ≤-refl
take-unconn sl nid vals fin sched st (just (mergeAll-st _ _ _ _)) = ≤-refl
take-unconn sl nid vals fin sched st (just (switch-st _ _))       = ≤-refl
take-unconn sl nid vals fin sched st (just (exhaust-st _ _))      = ≤-refl
take-unconn sl nid vals fin sched st (just (scan-st _))           = ≤-refl

wrap-unconn : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (op : AllOp) (nid : NodeId) (fin : Bool)
  (r : List (Val Γ u) × List _ × Sched Γ × EvalSt e) →
  unconn sl (EvalSt.connectedShares
    (proj₂ (proj₂ (proj₂ (proj₂ (thruWrap op nid fin r))))))
    ≤ unconn sl (EvalSt.connectedShares (proj₂ (proj₂ (proj₂ r))))
wrap-unconn sl op nid false r = ≤-refl
wrap-unconn sl mergeAllᵒ nid true (vs , bs , sched′ , st′)
  with lookupNode nid (EvalSt.nodes st′)
... | just (mergeAll-st _ _ _ _) = ≤-refl
... | just (switch-st _ _)       = ≤-refl
... | just (exhaust-st _ _)      = ≤-refl
... | just (take-st _)           = ≤-refl
... | just (scan-st _)           = ≤-refl
... | nothing                    = ≤-refl
wrap-unconn sl switchᵒ nid true (vs , bs , sched′ , st′)
  with lookupNode nid (EvalSt.nodes st′)
... | just (mergeAll-st _ _ _ _) = ≤-refl
... | just (switch-st _ _)       = ≤-refl
... | just (exhaust-st _ _)      = ≤-refl
... | just (take-st _)           = ≤-refl
... | just (scan-st _)           = ≤-refl
... | nothing                    = ≤-refl
wrap-unconn sl exhaustᵒ nid true (vs , bs , sched′ , st′)
  with lookupNode nid (EvalSt.nodes st′)
... | just (mergeAll-st _ _ _ _) = ≤-refl
... | just (switch-st _ _)       = ≤-refl
... | just (exhaust-st _ _)      = ≤-refl
... | just (take-st _)           = ≤-refl
... | just (scan-st _)           = ≤-refl
... | nothing                    = ≤-refl

switchKill-unconn : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e)
  {res} → switchKill cur sched st ≡ res →
  unconn sl (EvalSt.connectedShares (proj₂ (proj₂ res)))
    ≤ unconn sl (EvalSt.connectedShares st)
switchKill-unconn sl nothing  sched st refl = ≤-refl
switchKill-unconn sl (just v) sched st refl = ≤-refl

------------------------------------------------------------------
-- THE WALK.
------------------------------------------------------------------

mutual

  subs-drops : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {b : Closed Γ u} {κ : Path Γ lo u t} {id : Id} {now : Tick}
    {sched : Sched Γ} {st : EvalSt e} {burst : Stream Γ u}
    {sched′ : Sched Γ} {st′ : EvalSt e} (sl : Slots Γ) →
    subscribeE⇓ {e = e} b κ id now sched st (burst , sched′ , st′) →
    unconn sl (EvalSt.connectedShares st′)
      ≤ unconn sl (EvalSt.connectedShares st)
  subs-drops sl (subs-floor _)            = ≤-refl
  subs-drops sl (subs-shared _ s)         = slot-drops sl s
  subs-drops sl (subs-hot-done _ _ _)     = ≤-refl
  subs-drops sl (subs-hot-live _ _ _)     = ≤-refl
  subs-drops sl (subs-cold-sync _ _ _)    = ≤-refl
  subs-drops sl (subs-cold-async _ _ _ _) = ≤-refl
  subs-drops sl (subs-of _)               = ≤-refl
  subs-drops sl (subs-empty _)            = ≤-refl
  subs-drops sl (subs-map d p)            = ≤-trans (push-drops sl p) (subs-drops sl d)
  subs-drops sl (subs-take-zero _ _)      = ≤-refl
  subs-drops sl (subs-take-suc _ _ d p)   = ≤-trans (push-drops sl p) (subs-drops sl d)
  subs-drops sl (subs-scan _ d p)         = ≤-trans (push-drops sl p) (subs-drops sl d)
  subs-drops sl (subs-merge-all a)        = all-drops sl a
  subs-drops sl (subs-switch-all a)       = all-drops sl a
  subs-drops sl (subs-exhaust-all a)      = all-drops sl a
  subs-drops sl (subs-μ d)                = subs-drops sl d
  subs-drops sl (subs-defer _ _ _)        = ≤-refl

  all-drops : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {op : AllOp} {ns : NodeState Γ} {b : Closed Γ (obs u)}
    {κ : Path Γ lo u t} {id : Id} {now : Tick}
    {sched : Sched Γ} {st : EvalSt e} {burst : Stream Γ u}
    {sched′ : Sched Γ} {st′ : EvalSt e} (sl : Slots Γ) →
    subscribeAll⇓ {e = e} op ns b κ id now sched st (burst , sched′ , st′) →
    unconn sl (EvalSt.connectedShares st′)
      ≤ unconn sl (EvalSt.connectedShares st)
  all-drops sl (sub-all _ d p) = ≤-trans (push-drops sl p) (subs-drops sl d)

  inner-drops : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {op : AllOp} {allNid : NodeId} {κ : Path Γ lo u t} {id : Id} {now : Tick}
    {o : Val Γ (obs u)} {sched : Sched Γ} {st : EvalSt e}
    {inst : NodeId} {vs : List (Val Γ u)} {bs : List _} {done : Bool}
    {sched′ : Sched Γ} {st′ : EvalSt e} (sl : Slots Γ) →
    subscribeInner⇓ {e = e} op allNid κ id now o sched st
      (inst , vs , bs , done , sched′ , st′) →
    unconn sl (EvalSt.connectedShares st′)
      ≤ unconn sl (EvalSt.connectedShares st)
  inner-drops sl (inner _ d _) = subs-drops sl d

  push-drops : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
    {f : Frame Γ s u} {κ : Path Γ lo u t} {id : Id} {now : Tick}
    {ems : Stream Γ s} {sched : Sched Γ} {st : EvalSt e}
    {rest : Stream Γ u} {sched′ : Sched Γ} {st′ : EvalSt e} (sl : Slots Γ) →
    pushBurst⇓ {e = e} id now f κ ems sched st (rest , sched′ , st′) →
    unconn sl (EvalSt.connectedShares st′)
      ≤ unconn sl (EvalSt.connectedShares st)
  push-drops sl push-nil            = ≤-refl
  push-drops sl (push-cons _ sf ps) = ≤-trans (push-drops sl ps) (step-drops sl sf)

  step-drops : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
    {id : Id} {now : Tick} {fr : Frame Γ s u} {κ : Path Γ lo u t}
    {vals : List (Val Γ s)} {fin : Bool} {sched : Sched Γ} {st : EvalSt e}
    {vals′ : List (Val Γ u)} {evs : List _} {fin′ : Bool}
    {sched′ : Sched Γ} {st′ : EvalSt e} (sl : Slots Γ) →
    stepFrame⇓ {e = e} id now fr κ vals fin sched st
      (vals′ , evs , fin′ , sched′ , st′) →
    unconn sl (EvalSt.connectedShares st′)
      ≤ unconn sl (EvalSt.connectedShares st)
  step-drops sl step-map        = ≤-refl
  step-drops sl (step-scan _ _) = ≤-refl
  step-drops sl step-scan-nil   = ≤-refl
  step-drops {vals = vals} {fin = fin} {sched = sched} {st = st} sl
             (step-take {nid = nid}) =
    take-unconn sl nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
  step-drops sl (step-from-inner r) = react-drops sl r
  step-drops {fin = fin} sl (step-thru-outer {op = op} {nid = nid} w) =
    ≤-trans (wrap-unconn sl op nid fin _) (walk-drops sl w)

  react-drops : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
    {op : AllOp} {allNid inst : NodeId} {κ : Path Γ lo s t}
    {id : Id} {now : Tick} {vals : List (Val Γ s)}
    {sched : Sched Γ} {st : EvalSt e} {fin : Bool}
    {vals′ : List (Val Γ s)} {evs : List _} {fin′ : Bool}
    {sched′ : Sched Γ} {st′ : EvalSt e} (sl : Slots Γ) →
    innerReact⇓ {e = e} op allNid inst κ id now vals sched st fin
      (vals′ , evs , fin′ , sched′ , st′) →
    unconn sl (EvalSt.connectedShares st′)
      ≤ unconn sl (EvalSt.connectedShares st)
  react-drops sl react-false      = ≤-refl
  react-drops sl (react-alive _)  = ≤-refl
  react-drops sl (react-dead _ f) = finish-drops sl f

  finish-drops : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
    {op : AllOp} {allNid inst : NodeId} {κ : Path Γ lo s t}
    {id : Id} {now : Tick} {vals : List (Val Γ s)}
    {sched : Sched Γ} {st : EvalSt e} {ns : Maybe (NodeState Γ)}
    {vals′ : List (Val Γ s)} {evs : List _} {fin′ : Bool}
    {sched′ : Sched Γ} {st′ : EvalSt e} (sl : Slots Γ) →
    innerFinish⇓ {e = e} op allNid inst κ id now vals sched st ns
      (vals′ , evs , fin′ , sched′ , st′) →
    unconn sl (EvalSt.connectedShares st′)
      ≤ unconn sl (EvalSt.connectedShares st)
  finish-drops sl (finish-all-drain d)    = drain-drops sl d
  finish-drops sl (finish-switch-clear _) = ≤-refl
  finish-drops sl finish-exhaust-clear    = ≤-refl
  finish-drops sl finish-nil              = ≤-refl

  drain-drops : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
    {allNid : NodeId} {κ : Path Γ lo s t} {id : Id} {now : Tick}
    {lim : Maybe ℕ} {act : ℕ} {od : Bool} {q : List (Closed Γ s)}
    {sched : Sched Γ} {st : EvalSt e}
    {vs : List (Val Γ s)} {bs : List _} {act′ : ℕ} {q′ : List (Closed Γ s)}
    {sched′ : Sched Γ} {st′ : EvalSt e} (sl : Slots Γ) →
    mergeAllDrain⇓ {e = e} allNid κ id now lim act od q sched st
      (vs , bs , act′ , q′ , sched′ , st′) →
    unconn sl (EvalSt.connectedShares st′)
      ≤ unconn sl (EvalSt.connectedShares st)
  drain-drops sl drain-nil          = ≤-refl
  drain-drops sl (drain-no-room _)  = ≤-refl
  drain-drops sl (drain-room _ i d) =
    ≤-trans (drain-drops sl d) (inner-drops sl i)

  walk-drops : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {op : AllOp} {nid : NodeId} {κ : Path Γ lo u t} {id : Id} {now : Tick}
    {os : List (Val Γ (obs u))} {sched : Sched Γ} {st : EvalSt e}
    {vs : List (Val Γ u)} {bs : List _}
    {sched′ : Sched Γ} {st′ : EvalSt e} (sl : Slots Γ) →
    thruWalk⇓ {e = e} op nid κ id now os sched st (vs , bs , sched′ , st′) →
    unconn sl (EvalSt.connectedShares st′)
      ≤ unconn sl (EvalSt.connectedShares st)
  walk-drops sl walk-nil        = ≤-refl
  walk-drops sl (walk-cons c w) =
    ≤-trans (walk-drops sl w) (consume-drops sl c)

  consume-drops : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {op : AllOp} {nid : NodeId} {κ : Path Γ lo u t} {id : Id} {now : Tick}
    {o : Val Γ (obs u)} {sched : Sched Γ} {st : EvalSt e}
    {vals′ : List (Val Γ u)} {evs : List _}
    {sched′ : Sched Γ} {st′ : EvalSt e} (sl : Slots Γ) →
    thruConsume⇓ {e = e} op nid κ id now o sched st
      (vals′ , evs , sched′ , st′) →
    unconn sl (EvalSt.connectedShares st′)
      ≤ unconn sl (EvalSt.connectedShares st)
  consume-drops sl (consume-all-sub _ _ i)   = inner-drops sl i
  consume-drops sl (consume-all-enqueue _ _) = ≤-refl
  consume-drops sl consume-all-nil           = ≤-refl
  consume-drops sl (consume-switch-sub {sched₀ = sched₀} {st₀ = st₀}
                {cur = cur} _ k i) =
    ≤-trans (inner-drops sl i) (switchKill-unconn sl cur sched₀ st₀ k)
  consume-drops sl consume-switch-nil        = ≤-refl
  consume-drops sl (consume-exhaust-sub _ i) = inner-drops sl i
  consume-drops sl consume-exhaust-nil       = ≤-refl

  connect-drops : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
    {i : Fin n} {d : Closed Γ (lookup Γ i)}
    {κ : Path Γ lo (lookup Γ i) t} {below : toℕ i < lo}
    {id : Id} {now : Tick} {sched : Sched Γ} {st : EvalSt e}
    {burst : Stream Γ (lookup Γ i)} {sched′ : Sched Γ} {st′ : EvalSt e}
    (sl : Slots Γ) →
    sharedConnect⇓ {e = e} i d κ below id now sched st
      (burst , sched′ , st′) →
    unconn sl (EvalSt.connectedShares st′)
      ≤ unconn sl (EvalSt.connectedShares st)
  connect-drops {i = i} {st = st} sl (connect-live d _) =
    ≤-trans (subs-drops sl d)
      (unconn-cons-≤ sl (EvalSt.connectedShares st) (toℕ i))
  connect-drops {i = i} {st = st} sl (connect-died d _) =
    ≤-trans (subs-drops sl d)
      (unconn-cons-≤ sl (EvalSt.connectedShares st) (toℕ i))

  slot-drops : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
    {i : Fin n} {d : Closed Γ (lookup Γ i)}
    {κ : Path Γ lo (lookup Γ i) t} {below : toℕ i < lo}
    {id : Id} {now : Tick} {sched : Sched Γ} {st : EvalSt e}
    {burst : Stream Γ (lookup Γ i)} {sched′ : Sched Γ} {st′ : EvalSt e}
    (sl : Slots Γ) →
    subscribeSharedSlot⇓ {e = e} i d κ below id now sched st
      (burst , sched′ , st′) →
    unconn sl (EvalSt.connectedShares st′)
      ≤ unconn sl (EvalSt.connectedShares st)
  slot-drops sl (slot-spent _)       = ≤-refl
  slot-drops sl (slot-join _ _)      = ≤-refl
  slot-drops sl (slot-connect _ _ c) = connect-drops sl c
