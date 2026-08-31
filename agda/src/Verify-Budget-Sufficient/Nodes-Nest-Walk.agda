-- THE NODES MAP'S DEPTH ALONG ONE CHAIN, walked frame by frame -- the
-- same induction the registry arm runs, over the same potential, at
-- the other place a frame can store.
--
-- AND IT CARRIES THE REGISTRY'S JOIN, WHICH THE REGISTRY ARM DOES NOT
-- HAVE TO.  A chain that reaches a share does not stop there: the sink
-- fans the same values into every registration on the share, and each
-- of those walks its OWN path and stores at its own node.  Those paths
-- live in the registry, so what the fan-out can leave in the nodes map
-- is bounded by the registry's own nesting and by nothing the walked
-- path says.  The registry arm needs no such term because the fan-out
-- lands in the very place it is already measuring; the nodes arm is
-- measuring somewhere else, so the term has to be in the statement.
--
-- THE INDUCTION CLOSES BECAUSE THE REGISTRY ARM IS ALREADY PROVEN TO
-- STEP.  Carrying a second component would ordinarily cost a second
-- invariant, but the frame leaf for the registry says exactly that the
-- stepped registry is under the entry registry joined with the charge
-- -- so the extra term reproduces itself at each frame and collapses
-- into the same three-way join it started as.
--
-- REFUTED: Refuted.Share-Sink-Nodes
module Verify-Budget-Sufficient.Nodes-Nest-Walk where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; _++_; foldr)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; _≡ᵇ_)
open import Data.Vec using (lookup)
open import Data.Nat.Properties using (≤-trans; ⊔-lub; m≤m⊔n; m≤n⊔m)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim using (Gas; Id; Tick; Source; InstEvent; close; exhausted)
open import Rx.Exp using (Ctx; Closed; Val)
open import Rx.Evaluator
  using (Sched; EvalSt; Path; root; share-sink; _↠_; RegId;
         foldPath; stepFrame; dispatchShare;
         shareGo; shareAdmit; shareLatch)
open import Verify-Budget-Sufficient.Nest-Store using (nodeNest; regsNestMax)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (valsΦ?; PathΦHyp; DispatchΦHyp; ShareGoΦHyp;
         stepFrame-nest-Φ; stepFrame-nest-regs; foldPath-nest-regs)

postulate
  -- ONE FRAME'S NODE STORES, under the potential it was handed.  Only
  -- three of the five kinds store at all -- a scan writes its
  -- accumulator, an inner frame writes its parent *All's queue, and an
  -- outer frame mints the *All node the subscription hangs from -- and
  -- what each writes is a value the potential already covers, since
  -- the factor the frame surrenders is exactly the substitution it
  -- performs.
  --
  -- PROBED: `Probed.Chain-Step-Abs-Charge` reaches this leaf by RUNNING
  --   a whole chain over it, at the second cascade of two reachable
  --   families, taking the chain the evaluator itself presents rather
  --   than one built by hand -- five to six at the fold family against
  --   a charge of thirty-three, eight to sixteen at the demand family
  --   against seventy-one.  The charge read there is the SYNTACTIC one
  --   the size cap is proven to dominate, and the rows discharge no
  --   premise, so each is a stronger claim than the leaf instance.  NOT
  --   covered: one frame in isolation, since the rows read the
  --   composite; and any family whose chain deepens the node table by
  --   more than one step.
  stepFrame-nest-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sf : Gas) (id : Id) (now : Tick) (f : _) (path : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
    (B U : ℕ) →
    valsΦ? B U (f ↠ path) vals ≡ true →
    foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0
      (EvalSt.nodes
        (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path vals fin sched st))))))
      ≤ foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st) ⊔ U

-- THE WALK, AND THE FAN-OUT IT RE-ENTERS.  The frame clause spends
-- three facts and no more: the nodes leaf for what this frame stored,
-- the registry leaf for the term the statement carries, and the
-- potential's own step law -- which is the same one the registry walk
-- spends, so the two arms stay in lockstep and a frame kind that broke
-- one would break both.  The sink's clause spends the registry's whole
-- fan-out bound, which is a theorem of the registry arm rather than an
-- assumption of this one.
mutual
  foldPath-nest-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    (path : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (B U : ℕ) →
    valsΦ? B U path vals ≡ true →
    PathΦHyp sf gas id now B U path vals fin sched st →
    foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0
      (EvalSt.nodes (proj₂ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st))))
      ≤ foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
          ⊔ regsNestMax (EvalSt.registry st) ⊔ U
  foldPath-nest-nodes sf gas id now envSrc root vals evs fin sched st B U hΦ _ =
    ≤-trans (m≤m⊔n (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st))
                   (regsNestMax (EvalSt.registry st)))
            (m≤m⊔n _ U)
  foldPath-nest-nodes sf gas id now envSrc (share-sink i) vals evs fin sched st B U hΦ hD =
    dispatchShare-nest-nodes sf gas id now i vals fin sched st B U hD
  foldPath-nest-nodes sf gas id now envSrc (f ↠ p) vals evs fin sched st B U hΦ (hF , hR) =
    ≤-trans (foldPath-nest-nodes sf gas id now envSrc p
               (proj₁ step) (evs ++ proj₁ (proj₂ step))
               (proj₁ (proj₂ (proj₂ step)))
               (proj₁ (proj₂ (proj₂ (proj₂ step))))
               (proj₂ (proj₂ (proj₂ (proj₂ step)))) B U
               (stepFrame-nest-Φ sf id now f p vals fin sched st B U hΦ hF) hR)
            (⊔-lub (⊔-lub (≤-trans (stepFrame-nest-nodes sf id now f p vals fin sched st B U hΦ)
                                   (⊔-lub (≤-trans (m≤m⊔n N R) (m≤m⊔n _ U))
                                          (m≤n⊔m (N ⊔ R) U)))
                          (≤-trans (stepFrame-nest-regs sf id now f p vals fin sched st B U hΦ)
                                   (⊔-lub (≤-trans (m≤n⊔m N R) (m≤m⊔n _ U))
                                          (m≤n⊔m (N ⊔ R) U))))
                   (m≤n⊔m (N ⊔ R) U))
    where
    step = stepFrame sf id now f p vals fin sched st
    N = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
    R = regsNestMax (EvalSt.registry st)

  -- THE SINK, and none of its three arms touches the node map itself.
  -- Out of dispatch gas the state is returned untouched; the latch
  -- writes the completed and dying ledgers; and the finishing arm
  -- rewrites the registry and the live set.  So the whole of the map's
  -- growth is the fold's.
  dispatchShare-nest-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (B U : ℕ) →
    DispatchΦHyp sf gas id now B U i vals fin sched st →
    foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0
      (EvalSt.nodes (proj₂ (proj₂ (dispatchShare {t = t} sf gas id now i vals fin sched st))))
      ≤ foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
          ⊔ regsNestMax (EvalSt.registry st) ⊔ U
  dispatchShare-nest-nodes sf zero id now i vals fin sched st B U _ =
    ≤-trans (m≤m⊔n (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st))
                   (regsNestMax (EvalSt.registry st)))
            (m≤m⊔n _ U)
  dispatchShare-nest-nodes sf (suc gas) id now i vals false sched st B U hS =
    shareGo-nest-nodes sf gas id now i vals false
      (shareAdmit i (EvalSt.registry st)) sched st B U hS
  dispatchShare-nest-nodes sf (suc gas) id now i vals true sched st B U hS =
    shareGo-nest-nodes sf gas id now i vals true
      (shareAdmit i (EvalSt.registry st)) sched (shareLatch i true st) B U hS

  -- ONE ADMITTED REGISTRATION AT A TIME.  The join telescopes on both
  -- components at once: the map is bounded by the map it entered on
  -- joined with the registry it entered on, and the REGISTRY it entered
  -- on is bounded by the one this fold started at -- which is the
  -- registry arm's own walk theorem, spent here rather than assumed.
  shareGo-nest-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) (B U : ℕ) →
    ShareGoΦHyp sf gas id now B U i vals fin ps sched st →
    foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0
      (EvalSt.nodes (proj₂ (proj₂ (shareGo sf gas id now i vals fin ps sched st))))
      ≤ foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
          ⊔ regsNestMax (EvalSt.registry st) ⊔ U
  shareGo-nest-nodes sf gas id now i vals fin [] sched st B U _ =
    ≤-trans (m≤m⊔n (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st))
                   (regsNestMax (EvalSt.registry st)))
            (m≤m⊔n _ U)
  shareGo-nest-nodes sf gas id now i vals fin ((rid , p) ∷ ps) sched st B U hS
    with any (_≡ᵇ rid) (EvalSt.cancelled st)
  ... | true  = shareGo-nest-nodes sf gas id now i vals fin ps sched st B U hS
  ... | false =
    ≤-trans (shareGo-nest-nodes sf gas id now i vals fin ps
               (proj₁ (proj₂ FP)) (proj₂ (proj₂ FP)) B U (proj₂ (proj₂ hS)))
            (⊔-lub (⊔-lub (foldPath-nest-nodes sf gas id now (toℕ i) p vals
                             EVS fin sched st₀ B U
                             (proj₁ hS) (proj₁ (proj₂ hS)))
                          (≤-trans (foldPath-nest-regs sf gas id now (toℕ i) p vals
                                      EVS fin sched st₀ B U
                                      (proj₁ hS) (proj₁ (proj₂ hS)))
                                   (⊔-lub (≤-trans (m≤n⊔m N R) (m≤m⊔n _ U))
                                          (m≤n⊔m (N ⊔ R) U))))
                   (m≤n⊔m (N ⊔ R) U))
    where
    st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
    EVS = if fin then close (toℕ i) exhausted ∷ [] else []
    FP  = foldPath sf gas id now (toℕ i) p vals EVS fin sched st₀
    N = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
    R = regsNestMax (EvalSt.registry st)
