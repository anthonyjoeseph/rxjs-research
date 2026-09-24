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
-- `progR` merges, one lane at a time, two deferred inners at the root.
-- `progS` reads a share whose def is that same merge, from a merge of
-- its own at the root, so the def runs raw and its merge sits on a path
-- ending at the share's sink.  The rest read a hot slot that registers
-- and never speaks, which is what leaves a store holding live siblings:
-- `progW` a root switch over a take of it, `progE` the same exhaust,
-- `progB` a root merge of its batchSync, `progH` a root merge of two
-- takes of it.  `progQ` reads, from a root switch re-subscribing on each
-- value, a share whose def is a one-lane merge whose lane a take holds.

-- LOAD-BEARING: `raw-kept` down the share's sink, which fans out to the
-- reader.  It fails if the fan-out writes a node whose rows end at the
-- sink -- the def's merge and its inners -- which is the one write the
-- statement forbids and the fan-out is the only thing that could make.
-- LOAD-BEARING: `raw-kept` through a root switch whose first inner reads
-- a hot slot that never speaks, so the store still holds it, and its
-- take node, live.  Handed a fresh inner, the switch must cut it; the
-- row pins that the fold cut something.  It fails if the cut or the
-- subscribe after it writes the take node, which ends at the root where
-- the path does and is off it.
-- LOAD-BEARING: `raw-kept` through a root merge whose inner batches the
-- hot slot, handed a fresh batched inner.  It fails if the fresh inner's
-- batch node is minted over, or written into, the live one's.
-- NEAR-DEGENERATE: `raw-kept` through a busy root exhaust.  The inner is
-- refused, so it re-decides that a refusal writes nothing it guards.
-- LOAD-BEARING: `raw-kept` through the def's merge, handed a fresh
-- inner, and the same through the root merge in `progR`.  Each fails if
-- subscribing the inner rewrites a sibling inner's node, which ends
-- where the path does and is off it.

-- LOAD-BEARING: `refill-spends` for a fresh inner of the def's merge,
-- whose values fold to the sink and fan out.  It fails if that fan-out
-- reaches the merge's own outer and queues onto it.
-- LOAD-BEARING: `refill-spends` at `progQ`'s full lane, for a fresh
-- inner whose value fans out to the switch, which subscribes the share
-- again mid-emission; the row pins that it did.  It fails if the join
-- re-runs the def's outer, which would queue the take onto the full lane.
-- NEAR-DEGENERATE: `refill-spends` at `progR`'s root merge.  Nothing
-- re-enters the outer there, so it re-decides that an inner's own run
-- leaves its merge's queue alone.

-- LOAD-BEARING: `fold-refill-spends` at the def's merge, an inner's
-- exit frame finishing it: the finish drains the merge's queue and the
-- value folds to the sink and fans out.  It fails if the fan-out queues
-- onto the merge's own outer.
-- LOAD-BEARING: the same at `progQ`'s full lane, the value fanning out
-- to the re-subscribing switch.
-- NEAR-DEGENERATE: the same at `progR`'s root merge, where nothing
-- re-enters the outer.

-- LOAD-BEARING: `fold-kept`, `step-kept` and `subscribe-kept` for
-- `progH`'s merge handed a fresh take, asked at the first live take's
-- own path, which shares the merge's node.  Each fails if the run writes
-- a row through that node ending off the root, or a node at or past the
-- counter onto the sibling's path.
-- LOAD-BEARING: `fold-kept` for `progW`'s switch, asked at the path of
-- the take it cuts.  It fails if the cut leaves a row through the take's
-- node that the rule no longer admits.

-- NOT COVERED: a queue refilled while an inner runs, which is the
-- statement's whole risky region -- no program here re-enters a merge's
-- outer during one of its inners; `progQ` re-enters the share above it,
-- which is the nearest one gets.  Nor a scan, or a scripted slot's
-- arrival -- every hot slot here only registers.
module Probed.Base-Leaves where

-- TARGET: raw-kept @2a5289
-- TARGET: refill-spends @731051
-- TARGET: fold-refill-spends @15a00a
-- TARGET: step-kept @152c13
-- TARGET: subscribe-kept @93c511
-- TARGET: fold-kept @8401d5

open import Data.Bool using (Bool; true; false; T; not; _∧_; _∨_; if_then_else_)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List using (List; []; _∷_; map; length)
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
open import Probed.Rule-Kept using (sound?; toSound; step-of; rowNodes)
open import Rx.Exp using (Ctx; Closed; Val; obs; natᵗ; _×ᵗ_; listᵗ; ofᵉ; deferᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; takeᵉ;
  batchSyncᵉ; mapᵉ; input; strmᵗ; nat̂; []ᵉ; evalWith)
open import Rx.Slots using (Slots; shared; scripted)
open import Rx.Prim using (hot)
open import Rx.Evaluator using (Sched; EvalSt; RegRow; NodeState; mergeAll-st; Path; root; share-sink; _↠[_]_;
  thru-outer; from-inner; mergeAllᵒ; switchᵒ; exhaustᵒ; switch-st; exhaust-st; atSlot; pathHasNode; lookupNode;
  sched-init; st-init)
open import Rx.Evaluator.Freshness using (nodeCt)
open import Rx.Evaluator.Unconn-Arith using (unconn)
open import Rx.Evaluator.Reducible using (reducible; red-env; rawFold; rawInner)
open import Rx.Evaluator.Reducible.Support using (rootRP; standing; Sound; sound; rule; grounded; rowThrough; rowEnd; endOf; EndsAt; Kept; NodeOn; node-on; colsOf; waiting; ∨-T; bumpNode;
  raw-kept; refill-spends; fold-refill-spends; fold-kept; subscribe-kept; step-kept)

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
_ = keptOf κS schedS stS stS′ {pfs = colsOf κS stS} {sched′ = schedS′} (from-yes (nodeCt schedS ≤? nodeCt schedS′)) refl tt₀

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
_ = keptOf κR schedR stR stR′ {pfs = colsOf κR stR} {sched′ = schedR′} (from-yes (nodeCt schedR ≤? nodeCt schedR′)) refl tt₀

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

-- LOAD-BEARING
_ : Confirms (raw-kept (proj₂ foldW) (toSound (from-yes (sound? κW (nodeCt schedW) (EvalSt.registry stW))))
               (from-no (unconn (Sched.slots schedW′) (EvalSt.connectedShares stW′)
                         <? unconn (Sched.slots schedW) (EvalSt.connectedShares stW)))
               {pfs = colsOf κW stW})
_ = keptOf κW schedW stW stW′ {pfs = colsOf κW stW} {sched′ = schedW′} (from-yes (nodeCt schedW ≤? nodeCt schedW′)) refl tt₀

-- a root exhaust whose inner reads the hot slot, so it is busy when a
-- fresh inner arrives and refuses it
progE : Closed Γ₂ natᵗ
progE = exhaustAllᵉ (ofᵉ (strmᵗ (takeᵉ (nat̂ 5) (input zero)) ∷ []))

runE = let aM = <-wellFounded _ in
       reducible aM progE []ᵉ (red-env {Γ = Γ₂} aM []ᵉ) (root {lo = 1}) (standing tt) rootRP tt 0
         (sched-init progE slots₂) (st-init progE) ≤-refl
         (grounded tt (sound (rule (λ k ()) (λ ()) (λ ())) (λ k ()) (λ k ()) tt))

schedE : Sched Γ₂
schedE = proj₁ (proj₂ (proj₁ runE))

stE : EvalSt progE
stE = proj₂ (proj₂ (proj₁ runE))

busy : ∀ {n} {Γ : Ctx n} → Maybe (NodeState Γ) → Bool
busy (just (exhaust-st true _)) = true
busy _                          = false

nidE : ℕ
nidE = pick (λ k → busy (lookupNode k (EvalSt.nodes stE))) (below (nodeCt schedE))

κE : Path Γ₂ 0 (obs natᵗ) natᵗ
κE = thru-outer exhaustᵒ nidE ↠[ ≤-refl ] root

foldE = rawFold (<-wellFounded _) ≤-refl (<-wellFounded _) κE 0 (innerW ∷ []) false schedE stE ≤-refl
          (toSound (from-yes (sound? κE (nodeCt schedE) (EvalSt.registry stE))))

schedE′ = proj₁ (proj₂ (proj₁ foldE))
stE′    = proj₂ (proj₂ (proj₁ foldE))

-- NEAR-DEGENERATE
_ : Confirms (raw-kept (proj₂ foldE) (toSound (from-yes (sound? κE (nodeCt schedE) (EvalSt.registry stE))))
               (from-no (unconn (Sched.slots schedE′) (EvalSt.connectedShares stE′)
                         <? unconn (Sched.slots schedE) (EvalSt.connectedShares stE)))
               {pfs = colsOf κE stE})
_ = keptOf κE schedE stE stE′ {pfs = colsOf κE stE} {sched′ = schedE′} (from-yes (nodeCt schedE ≤? nodeCt schedE′)) refl tt₀

-- a root merge whose one inner batches the hot slot, left live
progB : Closed Γ₂ (natᵗ ×ᵗ listᵗ natᵗ)
progB = mergeAllᵉ nothing (ofᵉ (strmᵗ (batchSyncᵉ (input zero)) ∷ []))

runB = let aM = <-wellFounded _ in
       reducible aM progB []ᵉ (red-env {Γ = Γ₂} aM []ᵉ) (root {lo = 1}) (standing tt) rootRP tt 0
         (sched-init progB slots₂) (st-init progB) ≤-refl
         (grounded tt (sound (rule (λ k ()) (λ ()) (λ ())) (λ k ()) (λ k ()) tt))

schedB : Sched Γ₂
schedB = proj₁ (proj₂ (proj₁ runB))

stB : EvalSt progB
stB = proj₂ (proj₂ (proj₁ runB))

κB : Path Γ₂ 0 (obs (natᵗ ×ᵗ listᵗ natᵗ)) (natᵗ ×ᵗ listᵗ natᵗ)
κB = thru-outer mergeAllᵒ (nodeCt (sched-init progB slots₂)) ↠[ ≤-refl ] root

innerB : Val Γ₂ (obs (natᵗ ×ᵗ listᵗ natᵗ))
innerB = evalWith {Γ = Γ₂} (strmᵗ (batchSyncᵉ (deferᵉ (ofᵉ (nat̂ 9 ∷ []))))) []ᵉ

foldB = rawFold (<-wellFounded _) ≤-refl (<-wellFounded _) κB 0 (innerB ∷ []) false schedB stB ≤-refl
          (toSound (from-yes (sound? κB (nodeCt schedB) (EvalSt.registry stB))))

schedB′ = proj₁ (proj₂ (proj₁ foldB))
stB′    = proj₂ (proj₂ (proj₁ foldB))

-- LOAD-BEARING
_ : Confirms (raw-kept (proj₂ foldB) (toSound (from-yes (sound? κB (nodeCt schedB) (EvalSt.registry stB))))
               (from-no (unconn (Sched.slots schedB′) (EvalSt.connectedShares stB′)
                         <? unconn (Sched.slots schedB) (EvalSt.connectedShares stB)))
               {pfs = colsOf κB stB})
_ = keptOf κB schedB stB stB′ {pfs = colsOf κB stB} {sched′ = schedB′} (from-yes (nodeCt schedB ≤? nodeCt schedB′)) refl tt₀

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

------------------------------------------------------------------
-- `refill-spends`.
------------------------------------------------------------------

soSk : Sound sink₀ schedS stS
soSk = toSound (from-yes (sound? sink₀ (nodeCt schedS) (EvalSt.registry stS)))

ndS : NodeOn nidS sink₀ schedS stS
ndS = nodeOn nidS sink₀ tt₀ (from-yes (nidS <? nodeCt schedS)) (λ ())

innS = rawInner (<-wellFounded _) ≤-refl (<-wellFounded _) mergeAllᵒ nidS sink₀ 0 innerS schedS stS ≤-refl soSk ndS
         _ refl (<-wellFounded _) ≤-refl

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
         _ refl (<-wellFounded _) ≤-refl

rR = proj₁ innR

-- NEAR-DEGENERATE
_ : Confirms (refill-spends mergeAllᵒ nidR root (proj₂ innR) soR ndR refl
               (from-no (unconn (Sched.slots (proj₁ (proj₂ rR))) (EvalSt.connectedShares (proj₂ (proj₂ rR)))
                         <? unconn (Sched.slots schedR) (EvalSt.connectedShares stR))))
_ = from-yes (waiting (lookupNode nidR (EvalSt.nodes (proj₂ (proj₂ rR)))) ≤? waiting (lookupNode nidR (EvalSt.nodes stR)))

------------------------------------------------------------------
-- `fold-refill-spends`.
------------------------------------------------------------------

-- an inner of the def's merge finishing: its exit frame at a fresh
-- instance, over the share's sink
κFS : Path Γ₁ 0 natᵗ natᵗ
κFS = from-inner mergeAllᵒ nidS (nodeCt schedS) ↠[ ≤-refl ] sink₀

soFS : Sound κFS (bumpNode schedS) stS
soFS = toSound (from-yes (sound? κFS (nodeCt (bumpNode schedS)) (EvalSt.registry stS)))

foldFS = rawFold (<-wellFounded _) ≤-refl (<-wellFounded _) κFS 0 (9 ∷ []) true (bumpNode schedS) stS ≤-refl soFS

rFS = proj₁ foldFS

-- LOAD-BEARING
_ : Confirms (fold-refill-spends mergeAllᵒ nidS (nodeCt schedS) sink₀ (proj₂ foldFS) soFS
               (from-no (unconn (Sched.slots (proj₁ (proj₂ rFS))) (EvalSt.connectedShares (proj₂ (proj₂ rFS)))
                         <? unconn (Sched.slots schedS) (EvalSt.connectedShares stS))))
_ = from-yes (waiting (lookupNode nidS (EvalSt.nodes (proj₂ (proj₂ rFS)))) ≤? waiting (lookupNode nidS (EvalSt.nodes stS)))

κFR : Path Γ₀ 0 natᵗ natᵗ
κFR = from-inner mergeAllᵒ nidR (nodeCt schedR) ↠[ ≤-refl ] root

soFR : Sound κFR (bumpNode schedR) stR
soFR = toSound (from-yes (sound? κFR (nodeCt (bumpNode schedR)) (EvalSt.registry stR)))

foldFR = rawFold (<-wellFounded _) ≤-refl (<-wellFounded _) κFR 0 (9 ∷ []) true (bumpNode schedR) stR ≤-refl soFR

rFR = proj₁ foldFR

-- NEAR-DEGENERATE
_ : Confirms (fold-refill-spends mergeAllᵒ nidR (nodeCt schedR) root (proj₂ foldFR) soFR
               (from-no (unconn (Sched.slots (proj₁ (proj₂ rFR))) (EvalSt.connectedShares (proj₂ (proj₂ rFR)))
                         <? unconn (Sched.slots schedR) (EvalSt.connectedShares stR))))
_ = from-yes (waiting (lookupNode nidR (EvalSt.nodes (proj₂ (proj₂ rFR)))) ≤? waiting (lookupNode nidR (EvalSt.nodes stR)))

------------------------------------------------------------------
-- THE REFILL'S EDGE: a one-lane merge held full inside a share, whose
-- fan-out reaches a root switch that re-subscribes to the same share.
------------------------------------------------------------------

Γ₃ : Ctx 2
Γ₃ = natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

defQ : Closed Γ₃ natᵗ
defQ = mergeAllᵉ (just 1) (ofᵉ (strmᵗ (takeᵉ (nat̂ 5) (input zero)) ∷ []))

slots₃ : Slots Γ₃
slots₃ zero       = scripted {ok = tt₀} (hot [])
slots₃ (suc zero) = shared defQ

progQ : Closed Γ₃ natᵗ
progQ = switchAllᵉ (mapᵉ (strmᵗ (input (suc zero))) (input (suc zero)))

runQ = let aM = <-wellFounded _ in
       reducible aM progQ []ᵉ (red-env {Γ = Γ₃} aM []ᵉ) (root {lo = 2}) (standing tt) rootRP tt 0
         (sched-init progQ slots₃) (st-init progQ) ≤-refl
         (grounded tt (sound (rule (λ k ()) (λ ()) (λ ())) (λ k ()) (λ k ()) tt))

schedQ : Sched Γ₃
schedQ = proj₁ (proj₂ (proj₁ runQ))

stQ : EvalSt progQ
stQ = proj₂ (proj₂ (proj₁ runQ))

nidQ : ℕ
nidQ = pick (λ k → oneLane (lookupNode k (EvalSt.nodes stQ))) (below (nodeCt schedQ))

full : ∀ {n} {Γ : Ctx n} → Maybe (NodeState Γ) → Bool
full (just (mergeAll-st (just (suc zero)) (suc zero) [] _)) = true
full _                                                      = false

-- the lane is held by the take and nothing waits
_ : T (full (lookupNode nidQ (EvalSt.nodes stQ)))
_ = tt₀

sinkQ : Path Γ₃ 0 natᵗ natᵗ
sinkQ = share-sink (suc zero) z≤n

innerQ : Val Γ₃ (obs natᵗ)
innerQ = evalWith {Γ = Γ₃} (strmᵗ (deferᵉ (ofᵉ (nat̂ 9 ∷ [])))) []ᵉ

soSkQ : Sound sinkQ schedQ stQ
soSkQ = toSound (from-yes (sound? sinkQ (nodeCt schedQ) (EvalSt.registry stQ)))

ndQ : NodeOn nidQ sinkQ schedQ stQ
ndQ = nodeOn nidQ sinkQ tt₀ (from-yes (nidQ <? nodeCt schedQ)) (λ ())

innQ = rawInner (<-wellFounded _) ≤-refl (<-wellFounded _) mergeAllᵒ nidQ sinkQ 0 innerQ schedQ stQ ≤-refl soSkQ ndQ
         _ refl (<-wellFounded _) ≤-refl

rQ = proj₁ innQ

-- the premise that makes the row load-bearing: the fan-out reached the
-- switch, which subscribed the share again
_ = from-yes (length (EvalSt.registry stQ) <? length (EvalSt.registry (proj₂ (proj₂ rQ))))

-- LOAD-BEARING
_ : Confirms (refill-spends mergeAllᵒ nidQ sinkQ (proj₂ innQ) soSkQ ndQ refl
               (from-no (unconn (Sched.slots (proj₁ (proj₂ rQ))) (EvalSt.connectedShares (proj₂ (proj₂ rQ)))
                         <? unconn (Sched.slots schedQ) (EvalSt.connectedShares stQ))))
_ = from-yes (waiting (lookupNode nidQ (EvalSt.nodes (proj₂ (proj₂ rQ)))) ≤? waiting (lookupNode nidQ (EvalSt.nodes stQ)))

κFQ : Path Γ₃ 0 natᵗ natᵗ
κFQ = from-inner mergeAllᵒ nidQ (nodeCt schedQ) ↠[ ≤-refl ] sinkQ

soFQ : Sound κFQ (bumpNode schedQ) stQ
soFQ = toSound (from-yes (sound? κFQ (nodeCt (bumpNode schedQ)) (EvalSt.registry stQ)))

foldFQ = rawFold (<-wellFounded _) ≤-refl (<-wellFounded _) κFQ 0 (9 ∷ []) true (bumpNode schedQ) stQ ≤-refl soFQ

rFQ = proj₁ foldFQ

-- LOAD-BEARING
_ : Confirms (fold-refill-spends mergeAllᵒ nidQ (nodeCt schedQ) sinkQ (proj₂ foldFQ) soFQ
               (from-no (unconn (Sched.slots (proj₁ (proj₂ rFQ))) (EvalSt.connectedShares (proj₂ (proj₂ rFQ)))
                         <? unconn (Sched.slots schedQ) (EvalSt.connectedShares stQ))))
_ = from-yes (waiting (lookupNode nidQ (EvalSt.nodes (proj₂ (proj₂ rFQ)))) ≤? waiting (lookupNode nidQ (EvalSt.nodes stQ)))
