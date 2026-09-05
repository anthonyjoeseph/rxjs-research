-- ══════════════════════════════════════════════════════════════════
-- A μ ARRIVAL SQUARES A SIZE THE RUNG COUNT DOES NOT SEE, so neither
-- the crossing door's burst nor the unfolding beside it survives it.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE TWO STATEMENTS CLAIM.  Both price a subscription in RUNGS
-- of `iterSize` taken from the delivered size bound, and both count
-- the rungs with `layᵉ`: the door gets `suc (layᵉ b) + slotsSize sl`
-- for the source it folds, the unfolding gets `layᵉ (μᵉ body) +
-- slotsSize sl` for the body it substitutes into itself.  A rung
-- multiplies -- at the tightest `S` the statements admit it is
-- `s ↦ 4s + 2` -- so a fixed count buys a fixed FACTOR.
--
-- WHERE THEY BREAK.  Copies, and the count cannot see them.  `layᵉ`
-- charges nothing for a `μ` and nothing under a `defer`, which is the
-- only place a μ-var may stand, so a body mentioning its own
-- recursive occurrence `k` times counts ONE layer however large `k`
-- is -- while unfolding replaces each of those `k` occurrences by a
-- copy of the whole program.  The unfolded syntax is then `k` times
-- the size the bound was taken at, against a factor the layer count
-- fixed before `k` was chosen.  `k` is a free parameter of the
-- program, so no constant closes it: the empty telescope's extra rung
-- moves the crossing and does not remove it, which is what the two
-- pairs of rows below show by bracketing each crossing on both sides.
--
-- AND THE COPIES REACH THE TABLE AS ONE CELL, which is what makes
-- this a STORE reading rather than an arithmetic one.  `boundedNode`
-- at a merging door joins its queue by MAX, so `k` parked copies
-- would prove nothing; here the `k` occurrences sit under a SINGLE
-- defer, and a door with no room parks that one deferred subtree
-- whole.  One cell, `k` copies inside it.
--
-- WHAT IT LEAVES.  The door's burst and the unfolding are the same
-- finding twice, so one witness family kills both: the descent cannot
-- charge a μ edge in rungs denominated by `layᵉ` at all, and has to
-- price the unfold the way the caps face already does -- in a level
-- the statement quantifies over rather than one the syntax hands it.
--
-- WHAT IS HAND-BUILT.  Only the door's own cell and the schedule that
-- has moved past it, which is what the leaf's own premise says the
-- caller left; every table the rows read is REACHED, by subscribing
-- the program and folding the burst it produced.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Burst-Mu-Square where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≤ᵇ_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Gas; g0; gasPad; hot; Tick; Id)
open import Rx.Exp using (Ctx; Exp; Tm; Closed; natᵗ; obs;
  emptyᵉ; ofᵉ; mergeAllᵉ; μᵉ; varᵉ; deferᵉ; strmᵗ; sizeᵉ; unfoldμ)
open import Rx.Slots using (Slots; scripted; slotsSize)
open import Rx.Layer-Count using (layᵉ)
open import Rx.Evaluator using (Sched; EvalSt; Stream; Path; root; _↠_;
  NodeId; AllOp; mergeAllᵒ; thru-outer; mergeAll-st; installNode;
  st-init; sched-init; subscribeE; pushBurst; iterSize)
open import Verify-Budget-Sufficient.Measures using (boundedNode)

----------------------------------------------------------------------
-- THE TWO STATEMENTS, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulates would prove the tower inconsistent instead of refuting
-- anything.
----------------------------------------------------------------------
PushBurstSzStoreOuter : Set
PushBurstSzStoreOuter = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (g : Gas) (op : AllOp) (nid : NodeId)
  (b : Closed Γ (obs u)) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e)
  (r : Stream Γ (obs u) × Sched Γ × EvalSt e) (S B M : ℕ) → 2 ≤ S →
  Sched.slots sched ≡ sl →
  r ≡ subscribeE g b (thru-outer op nid ↠ κ) id now sched st →
  iterSize S (suc (layᵉ b) + slotsSize sl) B ≤ M →
  all (λ kv → boundedNode M (proj₂ kv))
      (EvalSt.nodes (proj₂ (proj₂ r))) ≡ true →
  (sizeᵉ b ≤ᵇ B) ≡ true →
  all (λ kv → boundedNode M (proj₂ kv))
      (EvalSt.nodes
        (proj₂ (proj₂
          (pushBurst g id now (thru-outer op nid) κ
            (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))))))
    ≡ true

SubscribeESzStoreMu : Set
SubscribeESzStoreMu = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (g : Gas) (body : Exp Γ (u ∷ []) [] [] u)
  (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (S B M : ℕ) → 2 ≤ S →
  Sched.slots sched ≡ sl →
  iterSize S (layᵉ (μᵉ body) + slotsSize sl) B ≤ M →
  all (λ kv → boundedNode M (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  (sizeᵉ (μᵉ body) ≤ᵇ B) ≡ true →
  all (λ kv → boundedNode M (proj₂ kv))
      (EvalSt.nodes
        (proj₂ (proj₂ (subscribeE g (unfoldμ body) κ id now sched st))))
    ≡ true

f≡t : false ≡ true → ⊥
f≡t ()

----------------------------------------------------------------------
-- THE PROGRAM FAMILY.  `bodyAt k` mentions its own μ-var `k` times,
-- all of them inside ONE defer -- which is both what the guard demands
-- and what puts every copy into a single parked cell.  The door around
-- them has no room, so subscribing the unfolding parks that cell
-- rather than running it, and `srcAt k` is the one-shot source whose
-- single emission IS the μ.
----------------------------------------------------------------------
Γ : Ctx 1
Γ = natᵗ ∷ⱽ []ⱽ

sl : Slots Γ
sl fzero = scripted (hot [])

mus : (j : ℕ) → List (Tm Γ [] (natᵗ ∷ []) [] (obs natᵗ))
mus zero    = []
mus (suc j) = strmᵗ (varᵉ (here refl)) ∷ mus j

bodyAt : (k : ℕ) → Exp Γ (natᵗ ∷ []) [] [] natᵗ
bodyAt k = mergeAllᵉ (just 0)
             (ofᵉ (strmᵗ (deferᵉ (mergeAllᵉ nothing (ofᵉ (mus k)))) ∷ []))

srcAt : (k : ℕ) → Closed Γ (obs natᵗ)
srcAt k = ofᵉ (strmᵗ (μᵉ (bodyAt k)) ∷ [])

e₀ : Closed Γ natᵗ
e₀ = emptyᵉ

----------------------------------------------------------------------
-- THE FIGURES.  Read at the door's own witness length.
----------------------------------------------------------------------

-- LOAD-BEARING: it is the whole mechanism in five numbers.  The layer
-- count and the program's syntax are LINEAR in `k` -- one layer, and a
-- size the bound is taken at -- while the unfolding is QUADRATIC in
-- it.  A count that had grown with the copies would not report one
-- here, and a bound that had would not report a hundred and
-- sixty-four.
figures : List ℕ
figures = layᵉ (srcAt 66) ∷ sizeᵉ (srcAt 66)
        ∷ sizeᵉ (μᵉ (bodyAt 66)) ∷ sizeᵉ (unfoldμ (bodyAt 66))
        ∷ slotsSize sl ∷ []

figures≡ : figures ≡ 1 ∷ 144 ∷ 141 ∷ 9380 ∷ 1 ∷ []
figures≡ = refl

----------------------------------------------------------------------
-- WITNESS ONE — the burst a crossing door pushes back through itself.
-- The door's cell and the schedule past it are the caller's, so the
-- subscription below is the leaf's own `r` and the fold is entered at
-- exactly the table it left.
----------------------------------------------------------------------
st₀ : EvalSt e₀
st₀ = installNode 0 (mergeAll-st {Γ = Γ} {t = natᵗ} nothing 0 [] false)
        (st-init e₀)

sched₀ : Sched Γ
sched₀ = record (sched-init e₀ sl) { nextNode = 1 }

subAt : (k : ℕ) → Stream Γ (obs natᵗ) × Sched Γ × EvalSt e₀
subAt k = subscribeE (gasPad 64 g0) (srcAt k)
            (thru-outer mergeAllᵒ 0 ↠ root) 0 0 sched₀ st₀

afterAt : (k : ℕ) → EvalSt e₀
afterAt k = proj₂ (proj₂
  (pushBurst (gasPad 64 g0) 0 0 (thru-outer mergeAllᵒ 0) root
     (proj₁ (subAt k)) (proj₁ (proj₂ (subAt k))) (proj₂ (proj₂ (subAt k)))))

-- LOAD-BEARING: the fold has something to push and pushing it WRITES.
-- An empty burst would make `pushBurst` the identity, and a table it
-- left unchanged would make every row below a reading of the
-- subscription instead of the crossing.
liveness : List ℕ
liveness = length (proj₁ (subAt 66))
         ∷ length (EvalSt.nodes (proj₂ (proj₂ (subAt 66))))
         ∷ length (EvalSt.nodes (afterAt 66)) ∷ []

liveness≡ : liveness ≡ 1 ∷ 1 ∷ 2 ∷ []
liveness≡ = refl

Mdoor : ℕ → ℕ
Mdoor k = iterSize 2 (suc (layᵉ (srcAt k)) + slotsSize sl) (sizeᵉ (srcAt k))

doorRow : ℕ → Bool
doorRow k = all (λ kv → boundedNode (Mdoor k) (proj₂ kv))
                (EvalSt.nodes (afterAt k))

-- LOAD-BEARING, and it brackets the crossing rather than exhibiting
-- one side of it.  One mention fewer and the claim HOLDS at the very
-- same rungs, so what fails is the multiplicity and not the door, the
-- gas, or the arithmetic of `iterSize`.
doorRows : List Bool
doorRows = doorRow 65 ∷ doorRow 66 ∷ []

doorRows≡ : doorRows ≡ true ∷ false ∷ []
doorRows≡ = refl

premDoor : all (λ kv → boundedNode (Mdoor 66) (proj₂ kv))
               (EvalSt.nodes (proj₂ (proj₂ (subAt 66)))) ≡ true
premDoor = refl

pushBurst-sz-store-outer-absurd : PushBurstSzStoreOuter → ⊥
pushBurst-sz-store-outer-absurd pr =
  f≡t (trans (sym doorRow66≡false)
             (pr {e = e₀} sl (gasPad 64 g0) mergeAllᵒ 0 (srcAt 66) root 0 0
                 sched₀ st₀ (subAt 66) 2 (sizeᵉ (srcAt 66)) (Mdoor 66)
                 (s≤s (s≤s z≤n)) refl refl ≤-refl premDoor refl))
  where
    doorRow66≡false : doorRow 66 ≡ false
    doorRow66≡false = refl

----------------------------------------------------------------------
-- WITNESS TWO — the unfolding itself, entered at an EMPTY table, so
-- nothing the door did is carrying the failure.  It crosses earlier
-- than the door does, and by exactly the rung the door's `suc` buys.
----------------------------------------------------------------------
muAt : (k : ℕ) → EvalSt e₀
muAt k = proj₂ (proj₂ (subscribeE (gasPad 64 g0) (unfoldμ (bodyAt k))
           root 0 0 (sched-init e₀ sl) (st-init e₀)))

Mmu : ℕ → ℕ
Mmu k = iterSize 2 (layᵉ (μᵉ (bodyAt k)) + slotsSize sl)
                 (sizeᵉ (μᵉ (bodyAt k)))

muRow : ℕ → Bool
muRow k = all (λ kv → boundedNode (Mmu k) (proj₂ kv)) (EvalSt.nodes (muAt k))

-- LOAD-BEARING and bracketing, as above.  The crossing sits at
-- sixteen mentions here against sixty-six at the door, which is the
-- one rung of difference between the two counts and is why one family
-- refutes both.
muRows : List Bool
muRows = muRow 15 ∷ muRow 16 ∷ []

muRows≡ : muRows ≡ true ∷ false ∷ []
muRows≡ = refl

premMu : all (λ kv → boundedNode (Mmu 16) (proj₂ kv))
             (EvalSt.nodes (st-init e₀)) ≡ true
premMu = refl

subscribeE-sz-store-μ-absurd : SubscribeESzStoreMu → ⊥
subscribeE-sz-store-μ-absurd pr =
  f≡t (trans (sym muRow16≡false)
             (pr {e = e₀} sl (gasPad 64 g0) (bodyAt 16) root 0 0
                 (sched-init e₀ sl) (st-init e₀) 2
                 (sizeᵉ (μᵉ (bodyAt 16))) (Mmu 16)
                 (s≤s (s≤s z≤n)) refl ≤-refl premMu refl))
  where
    muRow16≡false : muRow 16 ≡ false
    muRow16≡false = refl

----------------------------------------------------------------------
-- WITNESS THREE — THE ASSEMBLY'S OWN CONCLUSION, which is what makes
-- this a finding about the DENOMINATION and not about two leaves.  The
-- store descent is a real body over those leaves and its conclusion
-- COMPUTES, so it is instantiable at a whole program: a plain merging
-- door over the same source, entered at an empty table, with nothing
-- hand-built anywhere.
----------------------------------------------------------------------
SubscribeESzStore : Set
SubscribeESzStore = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (g : Gas) (o : Closed Γ u) (κ : Path Γ u t)
  (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (S B M : ℕ) → 2 ≤ S →
  Sched.slots sched ≡ sl →
  iterSize S (layᵉ o + slotsSize sl) B ≤ M →
  all (λ kv → boundedNode M (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  (sizeᵉ o ≤ᵇ B) ≡ true →
  all (λ kv → boundedNode M (proj₂ kv))
      (EvalSt.nodes (proj₂ (proj₂ (subscribeE g o κ id now sched st))))
    ≡ true

oAt : (k : ℕ) → Closed Γ natᵗ
oAt k = mergeAllᵉ nothing (srcAt k)

whole : (k : ℕ) → EvalSt e₀
whole k = proj₂ (proj₂ (subscribeE (gasPad 64 g0) (oAt k) root 0 0
            (sched-init e₀ sl) (st-init e₀)))

Mall : ℕ → ℕ
Mall k = iterSize 2 (layᵉ (oAt k) + slotsSize sl) (sizeᵉ (oAt k))

allRow : ℕ → Bool
allRow k = all (λ kv → boundedNode (Mall k) (proj₂ kv))
               (EvalSt.nodes (whole k))

-- LOAD-BEARING and bracketing, as above -- and the door here is the
-- ORDINARY one, with room, so nothing about the failure depends on a
-- degenerate limit at the outside.
allRows : List Bool
allRows = allRow 65 ∷ allRow 66 ∷ []

allRows≡ : allRows ≡ true ∷ false ∷ []
allRows≡ = refl

subscribeE-sz-store-absurd : SubscribeESzStore → ⊥
subscribeE-sz-store-absurd pr =
  f≡t (trans (sym allRow66≡false)
             (pr {e = e₀} sl (gasPad 64 g0) (oAt 66) root 0 0
                 (sched-init e₀ sl) (st-init e₀) 2
                 (sizeᵉ (oAt 66)) (Mall 66)
                 (s≤s (s≤s z≤n)) refl ≤-refl refl refl))
  where
    allRow66≡false : allRow 66 ≡ false
    allRow66≡false = refl
