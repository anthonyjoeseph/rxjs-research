-- THE BASE'S TWO LEAVES, INSTANTIATED AT STATES THE BUILDER REACHES.
-- Each program runs through `reducible` to its end, and each row runs
-- the raw evaluator again from that store: `rawFold` down a path the
-- store holds, `rawInner` for a merge's fresh inner.  So the before
-- state is reached by running, and the after state is the one the raw
-- body computes.  Nothing is pinned to a figure: every conclusion is
-- DECIDED at the concrete store, so a row whose run broke the statement
-- fails to typecheck rather than reading green.
--
-- `Kept`'s node conjunct is not decidable as stated, since node states
-- carry no decidable equality, so it is read off one equation: the
-- nodes it guards, listed before and after.  Which nodes it guards is
-- decided by `endsᵇ`, which is sound and complete for `EndsAt`.
--
-- Two programs.  `progR` merges, one lane at a time, two deferred
-- inners at the root.  `progS` reads a share whose def is that same
-- merge, from a merge of its own at the root, so the def runs raw and
-- its merge sits on a path ending at the share's sink.
--
-- LOAD-BEARING: `raw-kept` down the share's sink, which fans out to the
-- reader.  It fails if the fan-out writes a node whose rows end at the
-- sink -- the def's merge and its inners -- which is the one write the
-- statement forbids and the fan-out is the only thing that could make.
-- LOAD-BEARING: `raw-kept` through the def's merge, handed a fresh
-- inner, and the same through the root merge in `progR`.  Each fails if
-- subscribing the inner rewrites a sibling inner's node, which ends
-- where the path does and is off it.
-- LOAD-BEARING: `refill-spends` for a fresh inner of the def's merge,
-- whose values fold to the sink and fan out.  It fails if that fan-out
-- reaches the merge's own outer and queues onto it.
-- NEAR-DEGENERATE: `refill-spends` at `progR`'s root merge.  Nothing
-- re-enters the outer there, so it re-decides that an inner's own run
-- leaves its merge's queue alone.
--
-- NOT COVERED: a queue refilled while an inner runs, which is the
-- statement's whole risky region -- no program here re-enters a merge's
-- outer during one of its inners.  Nor a switch cutting a sibling, an
-- exhaust, a take, a scan, a batchSync or a scripted slot.
module Probed.Base-Leaves where

-- TARGET: raw-kept @2a5289
-- TARGET: refill-spends @731051

open import Data.Bool using (Bool; true; false; T; not; _∧_; _∨_; if_then_else_)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties using (∷-injective)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Maybe.Properties using (≡-dec)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; _≤?_; _<?_; ≤-pred; ≤∧≢⇒<) renaming (_≟_ to _≟ⁿ_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Vec using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness; from-yes; from-no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Probed.Apparatus using (Confirms)
open import Probed.Rule-Kept using (sound?; toSound)
open import Rx.Exp using (Ctx; Closed; Val; obs; natᵗ; ofᵉ; deferᵉ; mergeAllᵉ; input; strmᵗ; nat̂; []ᵉ; evalWith)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator using (Sched; EvalSt; RegRow; NodeState; mergeAll-st; Path; root; share-sink; _↠[_]_;
  thru-outer; mergeAllᵒ; pathHasNode; lookupNode; sched-init; st-init)
open import Rx.Evaluator.Freshness using (nodeCt)
open import Rx.Evaluator.Unconn-Arith using (unconn)
open import Rx.Evaluator.Reducible using (reducible; red-env; rawFold; rawInner)
open import Rx.Evaluator.Reducible.Support using (rootRP; standing; Sound; sound; rule; grounded; rowThrough; rowEnd; endOf; EndsAt; Kept; NodeOn; node-on; colsOf; waiting; ∨-T; raw-kept; refill-spends)

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

  ends-sound : ∀ {k x} (rs : List (RegRow Γ t))
             → (∀ {r} → r ∈ rs → T (rowThrough k r) → rowEnd r ≡ x) → T (endsᵇ k x rs)
  ends-sound []                   h = tt₀
  ends-sound {k} {x} (r ∷ rs) h with rowThrough k r in eq
  ... | false = ends-sound rs (λ r∈ → h (there r∈))
  ... | true with ≡-dec _≟ᶠ_ (rowEnd r) x
  ...   | yes _ = ends-sound rs (λ r∈ → h (there r∈))
  ...   | no ne = ⊥-elim (ne (h (here refl) (subst T (sym eq) tt₀)))

  ends-complete : ∀ {k x} (rs : List (RegRow Γ t)) → T (endsᵇ k x rs)
                → ∀ {r} → r ∈ rs → T (rowThrough k r) → rowEnd r ≡ x
  ends-complete {k} {x} (r ∷ rs) e (here refl) th with ∨-T {not (rowThrough k r)} (proj₁ (∧-split _ _ e))
  ... | inj₁ a = ⊥-elim (not-T (rowThrough k r) a th)
  ... | inj₂ b = toWitness b
  ends-complete [] _ ()
  ends-complete (r ∷ rs) e (there r∈) th = ends-complete rs (proj₂ (∧-split _ _ e)) r∈ th

------------------------------------------------------------------
-- `Kept`, DECIDED: its node conjunct as one equation over the nodes it
-- guards, and its terminus conjunct as a Boolean over the same range.
------------------------------------------------------------------

below : ℕ → List ℕ
below zero    = []
below (suc n) = n ∷ below n

below∈ : ∀ {k N} → k < N → k ∈ below N
below∈ {N = zero} ()
below∈ {k} {suc N} k< with k ≟ⁿ N
... | yes refl = here refl
... | no ne    = there (below∈ (≤∧≢⇒< (≤-pred k<) ne))

all-T : ∀ (p : ℕ → Bool) xs {k} → T (all p xs) → k ∈ xs → T (p k)
all-T p [] _ ()
all-T p (x ∷ xs) a (here refl) = proj₁ (∧-split _ _ a)
all-T p (x ∷ xs) a (there k∈)  = all-T p xs (proj₂ (∧-split _ _ a)) k∈

map-at : ∀ {A B : Set} (f g : A → B) xs {k} → map f xs ≡ map g xs → k ∈ xs → f k ≡ g k
map-at f g [] _ ()
map-at f g (x ∷ xs) eq (here refl) = proj₁ (∷-injective eq)
map-at f g (x ∷ xs) eq (there k∈)  = map-at f g xs (proj₂ (∷-injective eq)) k∈

guarded : ∀ p e → (T p → ⊥) → T e → T (not p ∧ e)
guarded false e _  te = te
guarded true  e np _  = ⊥-elim (np tt₀)

just-if : ∀ {A : Set} {b} {x y : A} → T b
        → (if b then just x else nothing) ≡ (if b then just y else nothing) → x ≡ y
just-if {b = true}  _  refl = refl
just-if {b = false} () _

module _ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u} (κ : Path Γ lo u t) (sched : Sched Γ) (st st′ : EvalSt e) where

  guards : ℕ → Bool
  guards k = not (pathHasNode k κ) ∧ endsᵇ k (endOf κ) (EvalSt.registry st)

  read : EvalSt e → ℕ → Maybe (Maybe (NodeState Γ))
  read s k = if guards k then just (lookupNode k (EvalSt.nodes s)) else nothing

  NodesKept : Set
  NodesKept = map (read st′) (below (nodeCt sched)) ≡ map (read st) (below (nodeCt sched))

  endsKeptᵇ : Bool
  endsKeptᵇ = all (λ k → not (guards k) ∨ endsᵇ k (endOf κ) (EvalSt.registry st′)) (below (nodeCt sched))


  kept′ : ℕ → Bool
  kept′ k = not (guards k) ∨ endsᵇ k (endOf κ) (EvalSt.registry st′)

  guarded-at : ∀ k → (T (pathHasNode k κ) → ⊥) → EndsAt k (endOf κ) st → T (guards k)
  guarded-at k off ea =
    guarded (pathHasNode k κ) (endsᵇ k (endOf κ) (EvalSt.registry st)) off
      (ends-sound {k = k} {x = endOf κ} (EvalSt.registry st) ea)

  ends-kept-at : ∀ k → T (not (guards k)) ⊎ T (endsᵇ k (endOf κ) (EvalSt.registry st′))
               → (T (pathHasNode k κ) → ⊥) → EndsAt k (endOf κ) st → EndsAt k (endOf κ) st′
  ends-kept-at k (inj₁ a) off ea = ⊥-elim (not-T (guards k) a (guarded-at k off ea))
  ends-kept-at k (inj₂ b) off ea = ends-complete (EvalSt.registry st′) b

  keptOf : ∀ {pfs} {sched′ : Sched Γ} → nodeCt sched ≤ nodeCt sched′ → NodesKept → T endsKeptᵇ
         → Kept κ (standing pfs) sched st sched′ st′
  keptOf ct nk ek =
      ct
    , (λ k k< off ea → just-if {b = guards k} (guarded-at k off ea)
                         (map-at (read st′) (read st) (below (nodeCt sched)) nk (below∈ k<)))
    , (λ k k< off ea → ends-kept-at k (∨-T {not (guards k)} (all-T kept′ (below (nodeCt sched)) ek (below∈ k<))) off ea)

-- a node's rows all end where a path does, decided
nodeOn : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo s} (nid : ℕ) (κ : Path Γ lo s t) {sched : Sched Γ} {st : EvalSt e}
       → T (endsᵇ nid (endOf κ) (EvalSt.registry st)) → nid < nodeCt sched → (T (pathHasNode nid κ) → ⊥)
       → NodeOn nid κ sched st
nodeOn nid κ {st = st} e lt off = node-on (ends-complete (EvalSt.registry st) e) lt off

-- the first node below the counter the test picks, else zero
pick : (ℕ → Bool) → List ℕ → ℕ
pick p []       = 0
pick p (k ∷ ks) = if p k then k else pick p ks

oneLane : ∀ {n} {Γ : Ctx n} → Maybe (NodeState Γ) → Bool
oneLane (just (mergeAll-st (just (suc zero)) _ _ _)) = true
oneLane _                                            = false

------------------------------------------------------------------
-- THE PROGRAMS.
------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ᵛ

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ᵛ []ᵛ

progR : Closed Γ₀ natᵗ
progR = mergeAllᵉ (just 1) (ofᵉ (strmᵗ (deferᵉ (ofᵉ (nat̂ 5 ∷ []))) ∷ strmᵗ (deferᵉ (ofᵉ (nat̂ 6 ∷ []))) ∷ []))

def₁ : Closed Γ₁ natᵗ
def₁ = mergeAllᵉ (just 1) (ofᵉ (strmᵗ (deferᵉ (ofᵉ (nat̂ 7 ∷ []))) ∷ strmᵗ (deferᵉ (ofᵉ (nat̂ 8 ∷ []))) ∷ []))

progS : Closed Γ₁ natᵗ
progS = mergeAllᵉ nothing (ofᵉ (strmᵗ (input zero) ∷ []))

noSlots : Slots Γ₀
noSlots ()

slots₁ : Slots Γ₁
slots₁ zero = shared def₁

schedR₀ : Sched Γ₀
schedR₀ = sched-init progR noSlots

stR₀ : EvalSt progR
stR₀ = st-init progR

schedS₀ : Sched Γ₁
schedS₀ = sched-init progS slots₁

stS₀ : EvalSt progS
stS₀ = st-init progS

runR = let aM = <-wellFounded _ in
       reducible aM progR []ᵉ (red-env {Γ = Γ₀} aM []ᵉ) (root {lo = 0}) (standing tt) rootRP tt 0
         schedR₀ stR₀ ≤-refl (grounded tt (sound (rule (λ k ()) (λ ()) (λ ())) (λ k ()) (λ k ()) tt))

runS = let aM = <-wellFounded _ in
       reducible aM progS []ᵉ (red-env {Γ = Γ₁} aM []ᵉ) (root {lo = 1}) (standing tt) rootRP tt 0
         schedS₀ stS₀ ≤-refl (grounded tt (sound (rule (λ k ()) (λ ()) (λ ())) (λ k ()) (λ k ()) tt))

schedR : Sched Γ₀
schedR = proj₁ (proj₂ (proj₁ runR))

stR : EvalSt progR
stR = proj₂ (proj₂ (proj₁ runR))

schedS : Sched Γ₁
schedS = proj₁ (proj₂ (proj₁ runS))

stS : EvalSt progS
stS = proj₂ (proj₂ (proj₁ runS))

-- each merge's node, picked by its lane limit rather than numbered
nidR : ℕ
nidR = pick (λ k → oneLane (lookupNode k (EvalSt.nodes stR))) (below (nodeCt schedR))

nidS : ℕ
nidS = pick (λ k → oneLane (lookupNode k (EvalSt.nodes stS))) (below (nodeCt schedS))

sink₀ : Path Γ₁ 0 natᵗ natᵗ
sink₀ = share-sink zero z≤n

κR : Path Γ₀ 0 (obs natᵗ) natᵗ
κR = thru-outer mergeAllᵒ nidR ↠[ ≤-refl ] root

κS : Path Γ₁ 0 (obs natᵗ) natᵗ
κS = thru-outer mergeAllᵒ nidS ↠[ ≤-refl ] sink₀

innerR : Val Γ₀ (obs natᵗ)
innerR = evalWith {Γ = Γ₀} (strmᵗ (deferᵉ (ofᵉ (nat̂ 9 ∷ [])))) []ᵉ
innerS : Val Γ₁ (obs natᵗ)
innerS = evalWith {Γ = Γ₁} (strmᵗ (deferᵉ (ofᵉ (nat̂ 9 ∷ [])))) []ᵉ

------------------------------------------------------------------
-- `raw-kept`.
------------------------------------------------------------------

-- the share's sink, handed a value: the fan-out to the reader
foldSk = rawFold (<-wellFounded _) ≤-refl (<-wellFounded _) sink₀ 0 (9 ∷ []) false schedS stS ≤-refl
           (toSound (from-yes (sound? sink₀ (nodeCt schedS) (EvalSt.registry stS))))

schedSk = proj₁ (proj₂ (proj₁ foldSk))
stSk    = proj₂ (proj₂ (proj₁ foldSk))

-- LOAD-BEARING
_ : Confirms (raw-kept (proj₂ foldSk) (toSound (from-yes (sound? sink₀ (nodeCt schedS) (EvalSt.registry stS))))
               (from-no (unconn (Sched.slots schedSk) (EvalSt.connectedShares stSk)
                         <? unconn (Sched.slots schedS) (EvalSt.connectedShares stS)))
               {pfs = colsOf sink₀ stS})
_ = keptOf sink₀ schedS stS stSk {sched′ = schedSk} (from-yes (nodeCt schedS ≤? nodeCt schedSk)) refl tt₀

-- the def's merge, handed a fresh inner
foldS = rawFold (<-wellFounded _) ≤-refl (<-wellFounded _) κS 0 (innerS ∷ []) false schedS stS ≤-refl
          (toSound (from-yes (sound? κS (nodeCt schedS) (EvalSt.registry stS))))

schedS′ = proj₁ (proj₂ (proj₁ foldS))
stS′    = proj₂ (proj₂ (proj₁ foldS))

-- LOAD-BEARING
_ : Confirms (raw-kept (proj₂ foldS) (toSound (from-yes (sound? κS (nodeCt schedS) (EvalSt.registry stS))))
               (from-no (unconn (Sched.slots schedS′) (EvalSt.connectedShares stS′)
                         <? unconn (Sched.slots schedS) (EvalSt.connectedShares stS)))
               {pfs = colsOf κS stS})
_ = keptOf κS schedS stS stS′ {sched′ = schedS′} (from-yes (nodeCt schedS ≤? nodeCt schedS′)) refl tt₀

-- the root merge, handed a fresh inner
foldR = rawFold (<-wellFounded _) ≤-refl (<-wellFounded _) κR 0 (innerR ∷ []) false schedR stR ≤-refl
          (toSound (from-yes (sound? κR (nodeCt schedR) (EvalSt.registry stR))))

schedR′ = proj₁ (proj₂ (proj₁ foldR))
stR′    = proj₂ (proj₂ (proj₁ foldR))

-- LOAD-BEARING
_ : Confirms (raw-kept (proj₂ foldR) (toSound (from-yes (sound? κR (nodeCt schedR) (EvalSt.registry stR))))
               (from-no (unconn (Sched.slots schedR′) (EvalSt.connectedShares stR′)
                         <? unconn (Sched.slots schedR) (EvalSt.connectedShares stR)))
               {pfs = colsOf κR stR})
_ = keptOf κR schedR stR stR′ {sched′ = schedR′} (from-yes (nodeCt schedR ≤? nodeCt schedR′)) refl tt₀

------------------------------------------------------------------
-- `refill-spends`.
------------------------------------------------------------------

soSk : Sound sink₀ schedS stS
soSk = toSound (from-yes (sound? sink₀ (nodeCt schedS) (EvalSt.registry stS)))

ndS : NodeOn nidS sink₀ schedS stS
ndS = nodeOn nidS sink₀ tt₀ (from-yes (nidS <? nodeCt schedS)) (λ ())

innS = rawInner (<-wellFounded _) ≤-refl (<-wellFounded _) mergeAllᵒ nidS sink₀ 0 innerS schedS stS ≤-refl soSk ndS
         _ refl (<-wellFounded _)

rS = proj₁ innS

-- LOAD-BEARING
_ : Confirms (refill-spends mergeAllᵒ nidS sink₀ (proj₂ innS) soSk ndS refl
               (from-no (unconn (Sched.slots (proj₁ (proj₂ rS))) (EvalSt.connectedShares (proj₂ (proj₂ rS)))
                         <? unconn (Sched.slots schedS) (EvalSt.connectedShares stS))))
_ = from-yes (waiting (lookupNode nidS (EvalSt.nodes (proj₂ (proj₂ rS)))) ≤? waiting (lookupNode nidS (EvalSt.nodes stS)))

soR : Sound (root {lo = 0}) schedR stR
soR = toSound (from-yes (sound? (root {lo = 0}) (nodeCt schedR) (EvalSt.registry stR)))

ndR : NodeOn nidR (root {lo = 0}) schedR stR
ndR = nodeOn nidR root tt₀ (from-yes (nidR <? nodeCt schedR)) (λ ())

innR = rawInner (<-wellFounded _) ≤-refl (<-wellFounded _) mergeAllᵒ nidR (root {lo = 0}) 0 innerR schedR stR ≤-refl soR ndR
         _ refl (<-wellFounded _)

rR = proj₁ innR

-- NEAR-DEGENERATE
_ : Confirms (refill-spends mergeAllᵒ nidR root (proj₂ innR) soR ndR refl
               (from-no (unconn (Sched.slots (proj₁ (proj₂ rR))) (EvalSt.connectedShares (proj₂ (proj₂ rR)))
                         <? unconn (Sched.slots schedR) (EvalSt.connectedShares stR))))
_ = from-yes (waiting (lookupNode nidR (EvalSt.nodes (proj₂ (proj₂ rR)))) ≤? waiting (lookupNode nidR (EvalSt.nodes stR)))
