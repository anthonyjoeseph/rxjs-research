-- THE SUBSCRIBE-SIDE CEILING, and the induction that carries it.  The
-- statement is one file's worth of subject matter: a descent measured
-- against what the subscribing state can see.  Its shape, what is
-- traded at each edge and what the size factor buys are argued at the
-- assembly below; the leaves above it are the clauses that argument
-- does not close.
module Verify-Budget-Sufficient.Depth-Sighted where

open import Data.Nat using (ℕ; suc; _+_; _≤_; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; ⊔-lub; +-assoc; +-comm)
open import Data.Bool using (false)
open import Data.List using ([])
open import Data.Maybe using (nothing)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)

open import Rx.Exp using (Ctx; Closed; Fn; obs; sizeᵉ; ofᵉ; emptyᵉ; deferᵉ; μᵉ; varᵉ;
  input; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ)
open import Rx.Prim using (Gas; g0; gs; Id; Tick)
open import Rx.Evaluator using (Sched; EvalSt; Path; map-f; _↠_; subscribeE;
  AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ; NodeState; mergeAll-st; switch-st; exhaust-st)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵗ)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE; depthBurst; depthAll)
open import Verify-Budget-Sufficient.Nest-Store using
  (pathNestD; sightCeil; storeNestMax; nestUnit)

-- WHAT THE SUBSCRIBING STATE CAN SEE, named once so the clauses below
-- read as the trade rather than as four arguments.
Sight : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} →
  Closed Γ u → Path Γ u t → Sched Γ → EvalSt e → ℕ
Sight {e = e} b κ sched st =
  sightCeil (sizeᵉ e) (pathNestD κ + nestDᵉ b)
            (storeNestMax sched st) (nestUnit e (Sched.slots sched))

postulate
  -- the slot read: gas is peeled, the subject becomes the shared def --
  -- a term the program contains but the path never charged for -- and
  -- the registry grows under `register`.
  sight-input : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (g : Gas) (i : _) (κ : Path Γ _ t) (bid : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    depthE g (input i) κ bid now sched st ≤ Sight (input i) κ sched st

  -- the map burst, which is the frame's own sweep back out
  sight-map-burst : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (g : Gas) (f : Fn Γ [] [] [] s u) (b : Closed Γ s) (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    (let r = subscribeE g b (map-f f ↠ κ) bid now sched st in
     depthBurst g bid now (map-f f) κ
       (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
      ≤ Sight (mapᵉ f b) κ sched st

  -- the three heads that MINT and INSTALL a node before descending, so
  -- each owes a store transport across `installNode` on top of its trade
  sight-take : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (c : _) (b : Closed Γ u) (κ : Path Γ u t) (bid : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    depthE g (takeᵉ c b) κ bid now sched st ≤ Sight (takeᵉ c b) κ sched st

  sight-scan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (g : Gas) (f : _) (z : _) (b : Closed Γ s) (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    depthE g (scanᵉ f z b) κ bid now sched st ≤ Sight (scanᵉ f z b) κ sched st

-- THE DRAIN, and it is ONE leaf for the three heads rather than three:
-- all of them delegate to `depthAll`, all of them wrap the subject in
-- exactly one nesting level, and none of them is distinguished by
-- anything the bound reads.  The payload subscribe under it is the one
-- descent that charges the path nothing, so this is where the size
-- factor is spent, and it is the head every program in the corpus wears
-- at its root.
--
-- PROBED: `Probed.Depth-Sighted` reads the assembly at `root`, where
--   this head is the one it lands on, at fold depths two and twenty, at
--   nine and eighty-one against ceilings of four hundred and five
--   thousand; on the family whose mergeAll is unbounded, five against
--   three hundred and seventy-two; and under the vocabulary that
--   connects at once rather than late, four against one thousand three
--   hundred and seventy-eight.  Not covered: any `sl` past the two-slot
--   vocabularies, which is where both remaining families are; every path
--   other than `root`, which is the whole of what generalising added;
--   and the two heads other than `mergeAllᵉ`, which no row reaches.
postulate
  sight-all : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (op : AllOp) (ist : NodeState Γ) (b : Closed Γ (obs u))
    (κ : Path Γ u t) (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    depthAll g op ist b κ bid now sched st
      ≤ sightCeil (sizeᵉ e) (pathNestD κ + suc (nestDᵉ b))
                  (storeNestMax sched st) (nestUnit e (Sched.slots sched))

postulate
  -- the unfolding, which is LARGER than the μ it replaces, so its trade
  -- is the one place the subject grows and the measure must be re-read
  sight-mu : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (body : _) (κ : Path Γ u t) (bid : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    depthE (gs g) (μᵉ body) κ bid now sched st ≤ Sight (μᵉ body) κ sched st

-- ANY SUBSCRIBE'S DESCENT AGAINST WHAT IT CAN SEE, which is the
-- statement the induction is actually over.  A sweep crosses
-- `thru-outer` frames and drains bounded mergeAlls, and both are paid
-- for out of structure it already has: the subject it is descending,
-- the path it has built, the store it walks, and the program's own
-- wrap unit.  The entry claim is this at `root`, where the path
-- charges nothing and the two readings of the subject coincide.
--
-- THE SUBJECT AND THE PATH ARE ONE QUANTITY, and stating it that way
-- is the whole reason this form can be induced on.  Every structural
-- descent TRADES: a `map` moves its function's nesting off the subject
-- and onto the frame it pushes, a `*All` moves its own wrap `suc` the
-- same way, and a `scan` moves less than it drops.  So `pathNestD κ +
-- nestDᵉ b` is non-increasing along the walk while neither summand is,
-- and a bound stated on either alone has to be re-established at every
-- edge.
--
-- WHAT THE SIZE FACTOR PAYS FOR IS THE ONE DESCENT THAT DOES NOT
-- TRADE.  A drain runs under a `from-inner`, which the path measure
-- charges nothing for -- deliberately, since the layer it would charge
-- is the one the `thru-outer` above it already bought -- so a program
-- whose folds nest spends one per layer against a sum that sees none
-- of them.  The layers are bounded by the program, which is why the
-- size enters as a FACTOR rather than a summand: as a summand it is
-- outrun, one per delivered value against the descent's eight.
--
-- REFUTED: `Refuted.Nest-Depth-One` is the subscribe-side witness the
--   ceiling is calibrated against -- a limit-one mergeAll over three
--   queued inners under nested folds, read at the root subscribe, whose
--   descent climbs four per fold layer against the bare sum's three.
depthE-sighted : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (bid : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  depthE g b κ bid now sched st ≤ Sight b κ sched st
depthE-sighted g (input i)          κ bid now sched st = sight-input g i κ bid now sched st
depthE-sighted g (ofᵉ ts)           κ bid now sched st = z≤n
depthE-sighted g emptyᵉ             κ bid now sched st = z≤n
depthE-sighted g (deferᵉ b)         κ bid now sched st = z≤n
depthE-sighted g0 (μᵉ body)         κ bid now sched st = z≤n
depthE-sighted (gs g) (μᵉ body)     κ bid now sched st = sight-mu g body κ bid now sched st
depthE-sighted g (varᵉ ())          κ bid now sched st
depthE-sighted g (takeᵉ c b)        κ bid now sched st = sight-take g c b κ bid now sched st
depthE-sighted g (scanᵉ f z b)      κ bid now sched st = sight-scan g f z b κ bid now sched st
depthE-sighted {u = u} g (mergeAllᵉ lim b) κ bid now sched st =
  sight-all g mergeAllᵒ (mergeAll-st {t = u} lim 0 [] false) b κ bid now sched st
depthE-sighted g (switchAllᵉ b)     κ bid now sched st =
  sight-all g switchᵒ (switch-st nothing false) b κ bid now sched st
depthE-sighted g (exhaustAllᵉ b)    κ bid now sched st =
  sight-all g exhaustᵒ (exhaust-st false false) b κ bid now sched st
-- THE ONE CLAUSE THAT IS THE TRADE ITSELF, and it needs no store
-- transport: a map mints nothing, so the state the recursive call reads
-- is the state this call was handed.  The whole step is the charge
-- moving off the subject and onto the frame, which is an associativity
-- and a commutativity on the measure and nothing else.
depthE-sighted {e = e} g (mapᵉ f b) κ bid now sched st =
  ⊔-lub (≤-trans (depthE-sighted g b (map-f f ↠ κ) bid now sched st)
                 (≤-reflexive (cong (λ v → sightCeil (sizeᵉ e) v
                                             (storeNestMax sched st)
                                             (nestUnit e (Sched.slots sched)))
                                    (trade f b κ))))
        (sight-map-burst g f b κ bid now sched st)
  where
  trade : ∀ {s u} (f : Fn _ [] [] [] s u) (b : Closed _ s) (κ : Path _ u _) →
    pathNestD (map-f f ↠ κ) + nestDᵉ b ≡ pathNestD κ + nestDᵉ (mapᵉ f b)
  trade f b κ = trans (cong (_+ nestDᵉ b) (+-comm (nestDᵗ f) (pathNestD κ)))
                      (+-assoc (pathNestD κ) (nestDᵗ f) (nestDᵉ b))
