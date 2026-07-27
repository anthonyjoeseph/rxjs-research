-- Does cutThrough preserve cachesValid?  A hand-built configuration decides it
-- by computation: a merge node whose OUTER is still registered (so the
-- mergeReachable guard is armed) and one inner instance whose only chain runs
-- through a take node.  Cutting that take strips the inner's registration, so
-- countLiveInners drops while merge-st's activeInners does not — the two sides
-- of nodeCacheOK's merge clause come apart.
module Cut-Caches-Probe where

open import Data.Bool    using (Bool; true; false)
open import Data.List    using (List; []; _∷_)
open import Data.Nat     using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Vec     using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
open import Rx.Prim
open import Rx.Evaluator
open import Verify-Well-Formed

Γ₀ : Ctx 0
Γ₀ = []

mnid nid inst : NodeId
mnid = 0
nid  = 1
inst = 2

-- the merge's outer chain, and an inner instance reached through a take
outerP : Path Γ₀ (obs natᵗ) natᵗ
outerP = thru-outer mergeᵒ mnid ↠ root

innerP : Path Γ₀ natᵗ natᵗ
innerP = take-f nid ↠ (from-inner mergeᵒ mnid inst ↠ root)

reg₀ : List (RegId × Source × Chain Γ₀ natᵗ)
reg₀ = (0 , 10 , (obs natᵗ , outerP))
     ∷ (1 , 11 , (natᵗ    , innerP))
     ∷ []

nodes₀ : List (NodeId × NodeState Γ₀)
nodes₀ = (mnid , merge-st 1 false)
       ∷ (nid  , take-st 1)
       ∷ []

-- cut the take: `delivered`/`dying` empty, watermark 0 (the close reason is
-- irrelevant here — only the KEPT registry feeds cachesValid)
kept₀ : List (RegId × Source × Chain Γ₀ natᵗ)
kept₀ = proj₁ (cutThrough nid [] 0 [] reg₀)

-- only the outer survives: the inner's chain passes through nid
_ : kept₀ ≡ (0 , 10 , (obs natᵗ , outerP)) ∷ []
_ = refl

-- the caches are valid BEFORE the cut: activeInners 1 matches the one live
-- inner instance
_ : cachesValid nodes₀ reg₀ ≡ true
_ = refl

-- and INVALID after it: the outer still arms mergeReachable, but the inner
-- instance is gone, so 1 ≢ countLiveInners ≡ 0
_ : cachesValid nodes₀ kept₀ ≡ false
_ = refl

------------------------------------------------------------------
-- The deeper half: cachesValid is not a BURST invariant to begin with.
--
-- thruConsume mergeᵒ runs `subscribeInner` FIRST and only then applies
-- `mergeBump nid done`.  So for the whole of an inner's subscribe burst the
-- inner's registrations already exist while merge-st's activeInners has not
-- been incremented yet — the count TRAILS the registry.  With the outer still
-- registered (subscribeAll registers it before pushBurst), mergeReachable is
-- armed and nodeCacheOK's merge clause is false.
--
-- This is the state BurstInv is asserted of, so BurstInv.caches does not hold
-- of it.  Note the two failures point OPPOSITE ways: mid-subscribe the count
-- trails the registry (k < countLiveInners), and after a cut it leads it
-- (k > countLiveInners).  No inequality between k and countLiveInners survives
-- both, so the merge clause carries no information during a subscribe burst.
------------------------------------------------------------------

-- mid-inner-subscribe: same registry, but the bump has not happened yet
nodesPreBump : List (NodeId × NodeState Γ₀)
nodesPreBump = (mnid , merge-st 0 false)
             ∷ (nid  , take-st 1)
             ∷ []

_ : cachesValid nodesPreBump reg₀ ≡ false
_ = refl

-- and the post-cut state IS consistent with the bump merge actually applies:
-- the inner completed synchronously, so `mergeBump _ true` leaves k at 0
_ : cachesValid nodesPreBump kept₀ ≡ true
_ = refl
