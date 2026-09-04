-- ══════════════════════════════════════════════════════════════════
-- A SUBSTITUTED INNER'S DESCENT IS NOT UNDER THE ROOT'S BURST CEILING,
-- and that kills the one syntactic route the drain conjunct had.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAYS.  The tree bounds `descW` only once, at the
-- root and by syntax: `descW-ceil` puts any closed term's descent under
-- that term's own burst ceiling.  The drain conjuncts of the walk's
-- burst ledger ask for the descent of an inner the EVALUATOR built --
-- a step function applied to a value -- and the route this file kills
-- read that inner's descent against the ROOT's ceiling, the one number
-- the tree already has at every state: an inner a `*All` frame is
-- handed, subscribed at the states the outer's own subscribe returned,
-- descends no wider than the program it was cut from.
--
-- WHERE IT BREAKS.  A template that mentions its argument TWICE, under
-- a `*All` head whose own width the ceiling reads as ZERO.  The root's
-- ceiling is a product of slopes, and a template whose output width is
-- nil -- the inner ends in a map to `emptyᵉ` -- has a nil slope, so the
-- root prices the map at the width of its source alone: the one
-- observable it is handed, `B` values wide.  The substituted inner
-- merges two copies of that observable and hands their `2B` values to
-- its own map, which is the burst `descW` reads.  Two copies of two
-- values read four against two; of three, six against three.  The
-- factor is the mention count, so no constant closes it, and the
-- shape is the affine one `Refuted.Ceil-Unfold-Mu` found at the μ head
-- -- copies of a plug that the syntax counted once -- arriving at the
-- frame instead of the unfold.
--
-- WHAT IT LEAVES.  A ceiling read at the root prices the syntax as it
-- is written, and substitution rewrites it; so the drain conjunct has
-- to be denominated in something the invariant carries PER INNER --
-- the size the node's caps conjunct already bounds -- and not in a
-- number read once at the entry.  The same lesson the joined ceiling
-- taught at the unfold, one level down.
--
-- WHAT IS HAND-BUILT.  Nothing.  The inner is the one value the
-- outer's own subscribe emits, pinned by `refl`; the states are the
-- ones that subscribe returns; the fuel is the statement's own budget.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Drain-Root-Ceil where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _≤_; _⊔_; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; m≤m⊔n)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

open import Rx.Prim using (Gas; g0; gs; Tick; Id)
open import Rx.Exp
  using (Ctx; Closed; Val; Exp; Fn; natᵗ; obs; ofᵉ; emptyᵉ; mapᵉ;
         mergeAllᵉ; strmᵗ; varᵗ)
open import Rx.Slots using (Slots; shared)
open import Rx.Burst-Ceil using (bCeilᵉ; slotsBCeil)
open import Rx.Evaluator
  using (root; sched-init; st-init; subscribeE; budgetAt; EvalSt; Sched;
         Stream; Path; _↠_; thru-outer; from-inner; mergeAllᵒ; NodeId;
         mintNode; installNode; mergeAll-st; splitBurst)
open import Verify-Budget-Sufficient.Nest-Burst
  using (innerW; innerW-gs; descW-merge; descW-map-eq; burstW;
         burstW-eq)
open import Refuted.Demand-Programs using (Γ₂; natsD)

-- no inputs are read, so both slots are empty shares and the slot
-- collector reads zero
slots : Slots Γ₂
slots i = shared emptyᵉ

-- THE STATEMENT.  An inner the outer's subscribe emitted, subscribed
-- at the states that subscribe returned, descends under the root's
-- ceiling -- which is the shape the `thru-outer` conjunct of the burst
-- ledger asks of `innerW`, denominated in the one number the tree
-- bounds syntactically.
InnerUnderRootCeil : Set
InnerUnderRootCeil = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (sl : Slots Γ) (b : Closed Γ (obs u)) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e)
  (o : Val Γ (obs u)) →
  Sched.slots sched ≡ sl →
  o ∈ proj₁ (splitBurst {A = Val Γ t}
        (proj₁ (subscribeE g b (thru-outer mergeAllᵒ nid ↠ κ) id now sched st))) →
  innerW g mergeAllᵒ nid κ id now o
    (proj₁ (proj₂ (subscribeE g b (thru-outer mergeAllᵒ nid ↠ κ) id now sched st)))
    (proj₂ (proj₂ (subscribeE g b (thru-outer mergeAllᵒ nid ↠ κ) id now sched st)))
    ≤ bCeilᵉ n sl e ⊔ slotsBCeil n sl

-- THE WITNESS, at a copy width B.  The step function mentions its
-- argument twice under a merge and ends in a map to nothing, so the
-- root's slope through it is nil.
big : ℕ → Closed Γ₂ natᵗ
big B = ofᵉ (natsD B)

body : Exp Γ₂ [] [] (obs natᵗ ∷ []) natᵗ
body = mergeAllᵉ nothing
         (mapᵉ (strmᵗ emptyᵉ)
           (mergeAllᵉ nothing
             (ofᵉ (varᵗ (here refl) ∷ varᵗ (here refl) ∷ []))))

step : Fn Γ₂ [] [] [] (obs natᵗ) (obs natᵗ)
step = strmᵗ body

outer : ℕ → Closed Γ₂ (obs natᵗ)
outer B = mapᵉ step (ofᵉ (strmᵗ (big B) ∷ []))

prog : ℕ → Closed Γ₂ natᵗ
prog B = mergeAllᵉ nothing (outer B)

-- the inner the map builds: the template with its two mentions filled
inner : ℕ → Closed Γ₂ natᵗ
inner B = mergeAllᵉ nothing
            (mapᵉ (strmᵗ emptyᵉ)
              (mergeAllᵉ nothing
                (ofᵉ (strmᵗ (big B) ∷ strmᵗ (big B) ∷ []))))

-- THE STATEMENT'S OWN FUEL, and the run the root's `mergeAll` head
-- makes: mint the node, install it, subscribe the outer under the
-- `thru-outer` frame -- the evaluator's own arm, arm for arm.
gas : ℕ → Gas
gas B = budgetAt (prog B) slots 0

sched₀ : ℕ → Sched Γ₂
sched₀ B = sched-init (prog B) slots

nid : ℕ → NodeId
nid B = proj₁ (mintNode (sched₀ B))

sched₁ : ℕ → Sched Γ₂
sched₁ B = proj₂ (mintNode (sched₀ B))

st₁ : (B : ℕ) → EvalSt (prog B)
st₁ B = installNode (nid B) (mergeAll-st {t = natᵗ} nothing 0 [] false)
                    (st-init (prog B))

R : (B : ℕ) → Stream Γ₂ (obs natᵗ) × Sched Γ₂ × EvalSt (prog B)
R B = subscribeE (gas B) (outer B) (thru-outer mergeAllᵒ (nid B) ↠ root)
                 0 0 (sched₁ B) (st₁ B)

sched₂ : ℕ → Sched Γ₂
sched₂ B = proj₁ (proj₂ (R B))

st₂ : (B : ℕ) → EvalSt (prog B)
st₂ B = proj₂ (proj₂ (R B))

-- THE INNER IS THE ONE THE OUTER EMITS, at both copy widths
emitted₂ : proj₁ (splitBurst {A = Val Γ₂ natᵗ} (proj₁ (R 2))) ≡ inner 2 ∷ []
emitted₂ = refl

emitted₃ : proj₁ (splitBurst {A = Val Γ₂ natᵗ} (proj₁ (R 3))) ≡ inner 3 ∷ []
emitted₃ = refl

-- THE FIGURES.  The root's ceiling is B: the one observable the map is
-- handed, B wide, through a nil slope.  The inner's map hands back 2B.
ceil : ℕ → ℕ
ceil B = bCeilᵉ 2 slots (prog B) ⊔ slotsBCeil 2 slots

ceil₂≡2 : ceil 2 ≡ 2
ceil₂≡2 = refl

ceil₃≡3 : ceil 3 ≡ 3
ceil₃≡3 = refl

-- the inner's subscribe, as `innerW` peels it: one fuel down, under
-- the fresh instance's `from-inner` frame
peel : Gas → Gas
peel g0     = g0
peel (gs g) = g

fuel : ℕ → Gas
fuel B = peel (gas B)

path : ℕ → Path Γ₂ natᵗ natᵗ
path B = from-inner mergeAllᵒ (nid B) (Sched.nextNode (sched₂ B)) ↠ root

sched₃ : ℕ → Sched Γ₂
sched₃ B = record (sched₂ B) { nextNode = suc (Sched.nextNode (sched₂ B)) }

-- the state and path the inner's own `mergeAll` head hands its map
mapPath : ℕ → Path Γ₂ (obs natᵗ) natᵗ
mapPath B = thru-outer mergeAllᵒ (proj₁ (mintNode (sched₃ B))) ↠ path B

mapSched : ℕ → Sched Γ₂
mapSched B = proj₂ (mintNode (sched₃ B))

mapSt : (B : ℕ) → EvalSt (prog B)
mapSt B = installNode (proj₁ (mintNode (sched₃ B)))
                      (mergeAll-st {t = natᵗ} nothing 0 [] false) (st₂ B)

innerMap : ℕ → Closed Γ₂ (obs natᵗ)
innerMap B = mapᵉ (strmᵗ emptyᵉ)
               (mergeAllᵉ nothing (ofᵉ (strmᵗ (big B) ∷ strmᵗ (big B) ∷ [])))

mapBurst : ℕ → ℕ
mapBurst B = burstW (fuel B) (innerMap B) (mapPath B) 0 0 (mapSched B) (mapSt B)

mapBurst₂≡4 : mapBurst 2 ≡ 4
mapBurst₂≡4 = burstW-eq (fuel 2) (innerMap 2) (mapPath 2) 0 0 (mapSched 2) (mapSt 2)

mapBurst₃≡6 : mapBurst 3 ≡ 6
mapBurst₃≡6 = burstW-eq (fuel 3) (innerMap 3) (mapPath 3) 0 0 (mapSched 3) (mapSt 3)

-- the map's burst is under the inner's descent: one projection at
-- the map, one at the inner's own head, and the peel
under₂ : mapBurst 2 ≤ innerW (gas 2) mergeAllᵒ (nid 2) root 0 0 (inner 2) (sched₂ 2) (st₂ 2)
under₂ =
  ≤-trans (m≤m⊔n _ _)
    (≤-trans (≤-reflexive (sym (descW-map-eq (fuel 2) (strmᵗ emptyᵉ) _ (mapPath 2) 0 0
                                              (mapSched 2) (mapSt 2))))
      (≤-trans (descW-merge (fuel 2) nothing (innerMap 2) (path 2) 0 0 (sched₃ 2) (st₂ 2))
               (innerW-gs (fuel 2) mergeAllᵒ (nid 2) root 0 0 (inner 2) (sched₂ 2) (st₂ 2))))

-- four against two
drain-root-ceil-absurd : InnerUnderRootCeil → ⊥
drain-root-ceil-absurd h =
  go (≤-trans (≤-reflexive (sym mapBurst₂≡4))
              (≤-trans under₂
                       (h (gas 2) slots (outer 2) (nid 2) root 0 0 (sched₁ 2) (st₁ 2)
                          (inner 2) refl
                          (subst (inner 2 ∈_) (sym emitted₂) (here refl)))))
  where
  go : 4 ≤ 2 → ⊥
  go (s≤s (s≤s ()))
