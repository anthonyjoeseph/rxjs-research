-- THE RULE-KEEP TRIO, INSTANTIATED AT STATES THE BUILDER REACHES.
-- Each program runs through `reducible` to its end, and each row runs
-- the raw evaluator again from that store: `rawFold` down a path the
-- store holds, `rawInner` for a merge's fresh inner.  So the before
-- state is reached by running, and the after state is the one the raw
-- body computes.  Nothing is pinned to a figure: every conclusion is
-- DECIDED at the concrete store, so a row whose run broke the statement
-- fails to typecheck rather than reading green.

-- Both programs read a hot slot that registers and never speaks, which
-- is what leaves a store holding live siblings: `progW` a root switch
-- over a take of it, `progH` a root merge of two takes of it.

-- LOAD-BEARING: `fold-kept`, `step-kept` and `subscribe-kept` for
-- `progH`'s merge handed a fresh take, asked at the first live take's
-- own path, which shares the merge's node.  Each fails if the run writes
-- a row through that node ending off the root, or a node at or past the
-- counter onto the sibling's path.
-- LOAD-BEARING: `fold-kept` for `progW`'s switch, asked at the path of
-- the take it cuts.  It fails if the cut leaves a row through the take's
-- node that the rule no longer admits.

-- NOT COVERED: a scan, or a scripted slot's arrival -- every hot slot
-- here only registers.
module Probed.Base-Leaves where

-- TARGET: step-kept @152c13
-- TARGET: subscribe-kept @93c511
-- TARGET: fold-kept @8401d5

open import Data.Bool using (Bool; true; false; T; not; _∧_; _∨_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Maybe.Properties using (≡-dec)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (≤-refl; _≤?_; _<?_; ≤-pred; ≤∧≢⇒<) renaming (_≟_ to _≟ⁿ_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Vec using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness; from-yes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Probed.Apparatus using (Confirms)
open import Probed.Rule-Kept using (sound?; toSound; step-of; rowNodes)
open import Rx.Exp using (Ctx; Closed; Val; obs; natᵗ; ofᵉ; deferᵉ; mergeAllᵉ; switchAllᵉ; takeᵉ; input; strmᵗ; nat̂;
  []ᵉ; evalWith)
open import Rx.Slots using (Slots; scripted)
open import Rx.Prim using (hot)
open import Rx.Evaluator using (Sched; EvalSt; RegRow; NodeState; Path; root; _↠[_]_; thru-outer; from-inner; mergeAllᵒ;
  switchᵒ; switch-st; atSlot; pathHasNode; lookupNode; sched-init; st-init)
open import Rx.Evaluator.Freshness using (nodeCt)
open import Rx.Evaluator.Reducible using (reducible; red-env; rawFold; rawInner)
open import Rx.Evaluator.Reducible.Support using (rootRP; standing; Sound; sound; rule; grounded; rowThrough; rowEnd; endOf; NodeOn; node-on;
  ∨-T; bumpNode; fold-kept; subscribe-kept; step-kept)

------------------------------------------------------------------
-- `EndsAt`, DECIDED.
------------------------------------------------------------------

∧-split : ∀ a b → T (a ∧ b) → T a × T b
∧-split true  b tb = tt₀ , tb
∧-split false b ()

not-T : ∀ b → T (not b) → T b → ⊥
not-T true () _
not-T false _ ()

module _ {n} {Γ : Ctx n} {t} where

  endsᵇ : ℕ → Maybe (Fin n) → List (RegRow Γ t) → Bool
  endsᵇ k x []       = true
  endsᵇ k x (r ∷ rs) = (not (rowThrough k r) ∨ ⌊ ≡-dec _≟ᶠ_ (rowEnd r) x ⌋) ∧ endsᵇ k x rs

  ends-complete : ∀ {k x} (rs : List (RegRow Γ t)) → T (endsᵇ k x rs)
                → ∀ {r} → r ∈ rs → T (rowThrough k r) → rowEnd r ≡ x
  ends-complete {k} {x} (r ∷ rs) e (here refl) th with ∨-T {not (rowThrough k r)} (proj₁ (∧-split _ _ e))
  ... | inj₁ a = ⊥-elim (not-T (rowThrough k r) a th)
  ... | inj₂ b = toWitness b
  ends-complete [] _ ()
  ends-complete (r ∷ rs) e (there r∈) th = ends-complete rs (proj₂ (∧-split _ _ e)) r∈ th

------------------------------------------------------------------
-- THE STORE, READ.
------------------------------------------------------------------

below : ℕ → List ℕ
below zero    = []
below (suc n) = n ∷ below n

-- a node's rows all end where a path does, decided
nodeOn : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo s} (nid : ℕ) (κ : Path Γ lo s t) {sched : Sched Γ} {st : EvalSt e}
       → T (endsᵇ nid (endOf κ) (EvalSt.registry st)) → nid < nodeCt sched → (T (pathHasNode nid κ) → ⊥)
       → NodeOn nid κ sched st
nodeOn nid κ {st = st} e lt off = node-on (ends-complete (EvalSt.registry st) e) lt off

-- the first node below the counter the test picks, else zero
pick : (ℕ → Bool) → List ℕ → ℕ
pick p []       = 0
pick p (k ∷ ks) = if p k then k else pick p ks

------------------------------------------------------------------
-- THE PROGRAMS.
------------------------------------------------------------------

-- a root switch whose inner reads a hot slot that never speaks, so the
-- store the run leaves still holds that inner, and its take node, live
Γ₂ : Ctx 1
Γ₂ = natᵗ ∷ᵛ []ᵛ

progW : Closed Γ₂ natᵗ
progW = switchAllᵉ (ofᵉ (strmᵗ (takeᵉ (nat̂ 5) (input zero)) ∷ []))

slots₂ : Slots Γ₂
slots₂ zero = scripted {ok = tt₀} (hot [])

runW = let aM = <-wellFounded _ in
       reducible aM progW []ᵉ (red-env {Γ = Γ₂} aM []ᵉ) (root {lo = 1}) (standing tt) rootRP tt 0
         (sched-init progW slots₂) (st-init progW) ≤-refl
         (grounded tt (sound (rule (λ k ()) (λ ()) (λ ())) (λ k ()) (λ k ()) tt))

schedW : Sched Γ₂
schedW = proj₁ (proj₂ (proj₁ runW))

stW : EvalSt progW
stW = proj₂ (proj₂ (proj₁ runW))

running : ∀ {n} {Γ : Ctx n} → Maybe (NodeState Γ) → Bool
running (just (switch-st (just _) _)) = true
running _                             = false

nidW : ℕ
nidW = pick (λ k → running (lookupNode k (EvalSt.nodes stW))) (below (nodeCt schedW))

κW : Path Γ₂ 0 (obs natᵗ) natᵗ
κW = thru-outer switchᵒ nidW ↠[ ≤-refl ] root

innerW : Val Γ₂ (obs natᵗ)
innerW = evalWith {Γ = Γ₂} (strmᵗ (deferᵉ (ofᵉ (nat̂ 9 ∷ [])))) []ᵉ

-- the switch, handed a fresh inner while its first is still registered
foldW = rawFold (<-wellFounded _) ≤-refl (<-wellFounded _) κW 0 (innerW ∷ []) false schedW stW ≤-refl
          (toSound (from-yes (sound? κW (nodeCt schedW) (EvalSt.registry stW))))

schedW′ = proj₁ (proj₂ (proj₁ foldW))
stW′    = proj₂ (proj₂ (proj₁ foldW))

-- the premise that makes the row load-bearing: the fold cut something
_ = from-yes (length (EvalSt.cancelled stW) <? length (EvalSt.cancelled stW′))

------------------------------------------------------------------
-- THE RULE AT A SECOND CONTINUATION CARRYING A NODE OF ITS OWN: a
-- live sibling's own path, read off the registry the run left.
------------------------------------------------------------------

firstRow : ∀ {n} {Γ : Ctx n} {t} → RegRow Γ t → List (RegRow Γ t) → RegRow Γ t
firstRow d []      = d
firstRow d (r ∷ _) = r

-- a root merge of two takes of the hot slot, both left live
progH : Closed Γ₂ natᵗ
progH = mergeAllᵉ nothing (ofᵉ (strmᵗ (takeᵉ (nat̂ 5) (input zero)) ∷ strmᵗ (takeᵉ (nat̂ 6) (input zero)) ∷ []))

runH = let aM = <-wellFounded _ in
       reducible aM progH []ᵉ (red-env {Γ = Γ₂} aM []ᵉ) (root {lo = 1}) (standing tt) rootRP tt 0
         (sched-init progH slots₂) (st-init progH) ≤-refl
         (grounded tt (sound (rule (λ k ()) (λ ()) (λ ())) (λ k ()) (λ k ()) tt))

schedH : Sched Γ₂
schedH = proj₁ (proj₂ (proj₁ runH))

stH : EvalSt progH
stH = proj₂ (proj₂ (proj₁ runH))

-- both inners live, each row through the merge's node and its own take's
_ : map (λ r → rowNodes r , rowEnd r) (EvalSt.registry stH)
      ≡ ((2 ∷ 0 ∷ 1 ∷ []) , nothing) ∷ ((4 ∷ 0 ∷ 3 ∷ []) , nothing) ∷ []
_ = refl

nidH : ℕ
nidH = nodeCt (sched-init progH slots₂)

κH : Path Γ₂ 0 (obs natᵗ) natᵗ
κH = thru-outer mergeAllᵒ nidH ↠[ ≤-refl ] root

κ₂H = proj₂ (proj₂ (proj₂ (firstRow (0 , atSlot zero , (natᵗ , root)) (EvalSt.registry stH))))

innerH : Val Γ₂ (obs natᵗ)
innerH = evalWith {Γ = Γ₂} (strmᵗ (takeᵉ (nat̂ 7) (input zero))) []ᵉ

soH : Sound κH schedH stH
soH = toSound (from-yes (sound? κH (nodeCt schedH) (EvalSt.registry stH)))

so₂H = toSound {κ = κ₂H} {sched = schedH} {st = stH} (from-yes (sound? κ₂H (nodeCt schedH) (EvalSt.registry stH)))

-- the merge handed a fresh take of the same slot
foldH = rawFold (<-wellFounded _) ≤-refl (<-wellFounded _) κH 0 (innerH ∷ []) false schedH stH ≤-refl soH

schedH′ = proj₁ (proj₂ (proj₁ foldH))
stH′    = proj₂ (proj₂ (proj₁ foldH))

-- LOAD-BEARING
_ : Confirms (fold-kept (proj₂ foldH) soH κ₂H so₂H (λ _ _ _ → refl))
_ = toSound {κ = κ₂H} {sched = schedH′} {st = stH′} (from-yes (sound? κ₂H (nodeCt schedH′) (EvalSt.registry stH′)))

-- its head step, at a store holding live rows
stpH = step-of (proj₂ foldH)

-- LOAD-BEARING
_ : Confirms (step-kept ≤-refl (proj₂ stpH) soH)
_ = toSound (from-yes (sound? κH (nodeCt (proj₁ (proj₂ (proj₂ (proj₂ (proj₁ stpH))))))
                                     (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂ (proj₁ stpH))))))))

-- the same fresh take subscribed as the merge's inner
soRH : Sound (root {lo = 0}) schedH stH
soRH = toSound (from-yes (sound? (root {lo = 0}) (nodeCt schedH) (EvalSt.registry stH)))

ndH : NodeOn nidH (root {lo = 0}) schedH stH
ndH = nodeOn nidH root tt₀ (from-yes (nidH <? nodeCt schedH)) (λ ())

innH = rawInner (<-wellFounded _) ≤-refl (<-wellFounded _) mergeAllᵒ nidH (root {lo = 0}) 0 innerH schedH stH ≤-refl soRH ndH
         _ refl (<-wellFounded _) ≤-refl

κIH : Path Γ₂ 0 natᵗ natᵗ
κIH = from-inner mergeAllᵒ nidH (nodeCt schedH) ↠[ ≤-refl ] root

soIH : Sound κIH (bumpNode schedH) stH
soIH = toSound (from-yes (sound? κIH (nodeCt (bumpNode schedH)) (EvalSt.registry stH)))

so₂IH = toSound {κ = κ₂H} {sched = bumpNode schedH} {st = stH} (from-yes (sound? κ₂H (nodeCt (bumpNode schedH)) (EvalSt.registry stH)))

-- LOAD-BEARING
_ : Confirms (subscribe-kept (proj₂ innH) soIH κ₂H so₂IH (λ _ _ _ → refl))
_ = toSound {κ = κ₂H} {sched = proj₁ (proj₂ (proj₁ innH))} {st = proj₂ (proj₂ (proj₁ innH))}
      (from-yes (sound? κ₂H (nodeCt (proj₁ (proj₂ (proj₁ innH)))) (EvalSt.registry (proj₂ (proj₂ (proj₁ innH))))))

-- the switch cutting its sibling, asked at the sibling's own path
κ₂W = proj₂ (proj₂ (proj₂ (firstRow (0 , atSlot zero , (natᵗ , root)) (EvalSt.registry stW))))

so₂W = toSound {κ = κ₂W} {sched = schedW} {st = stW} (from-yes (sound? κ₂W (nodeCt schedW) (EvalSt.registry stW)))

-- LOAD-BEARING
_ : Confirms (fold-kept (proj₂ foldW) (toSound (from-yes (sound? κW (nodeCt schedW) (EvalSt.registry stW))))
               κ₂W so₂W (λ _ _ _ → refl))
_ = toSound {κ = κ₂W} {sched = schedW′} {st = stW′} (from-yes (sound? κ₂W (nodeCt schedW′) (EvalSt.registry stW′)))
