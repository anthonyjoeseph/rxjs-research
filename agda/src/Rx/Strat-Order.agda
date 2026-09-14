------------------------------------------------------------------
-- THE ORDER THE EVALUATOR DESCENDS ON.

-- The evaluator peels at exactly four edges and holds its witness fixed
-- at every other clause, because every other clause stays at one nesting
-- level.  Each of the four is an edge at which a lexicographic tuple
-- strictly drops — the unconnected shares outermost, then the store's
-- holding, then the current value's rank, then the current expression's
-- syncSize — so the descent buys structural VISIBILITY for the
-- termination checker and nothing else mathematical.

-- WHAT THIS MODULE EXISTS TO SAY IS THAT THE ORDER NEEDS NO CAPS.  The
-- same tuple has a flattening into one natural, and that flattening is
-- where every size and rank ceiling in this development's descent
-- argument comes from: packing the components into a single number
-- requires multipliers that dominate the ones below, so a step that
-- drops the outermost has to be told the rest stayed under theirs.  A
-- lexicographic order packs nothing, and so asks for neither.  Stating
-- it separately is what makes that a checkable claim rather than an
-- observation: the four constructors below carry one inequality each
-- and no ceiling anywhere, and the edges that inhabit them are proven
-- in exactly that form.

-- IT IS IN `Rx` RATHER THAN BESIDE THE MEASURES because it mentions
-- nothing of this development — it is a relation on tuples of naturals
-- and vectors of them, and the evaluator is where it is ultimately
-- spent.  Nothing here may grow a dependency on the measures; a fact
-- that needs one belongs where that measure lives.  That is also why
-- the holding's vector carries no reading of which end is deep: the
-- order compares it left to right and the measure decides what the
-- positions mean.

-- WELL-FOUNDEDNESS IS STATED HERE AND PROVEN, and its shape is not a
-- matter of taste: the proof NESTS one `where` level per component,
-- each binding its own accessibility witness in an enclosing pattern,
-- because a flat helper taking all of them at once cannot work — its
-- off-component arms have to hand the outer witnesses back, and a
-- witness handed back is REBUILT rather than passed on, so nothing is
-- structurally smaller and the checker names every recursive call.
-- The trap itself is a fact about Agda rather than about this order,
-- so it is recorded in `docs/agda-traps.md`.
------------------------------------------------------------------
module Rx.Strat-Order where

open import Data.Nat using (ℕ; zero; suc; pred; _∸_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (<-trans; ≤-trans; n<1+n)
open import Data.List using (List; []; _∷_; map; foldr; _++_)
open import Data.List.Properties using (map-++; foldr-++)
open import Data.List.Relation.Unary.All as All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Vec using (Vec; []; _∷_; replicate)
open import Induction.WellFounded using (Acc; acc; WellFounded)

------------------------------------------------------------------
-- THE HOLDING, AND WHY IT IS A VECTOR OF COUNTS RATHER THAN A NUMBER.
-- The merge drain subscribes something the store has been holding, and
-- what it hands back is emitted under the rank the hop just dropped to
-- — so the step trades one item for any number of STRICTLY SHALLOWER
-- ones.  A census by depth falls at exactly that trade, read
-- left-to-right, and no count of ITEMS does: a bound on how many the
-- run can still write would have to be seeded at the entry, and
-- `syncSizeᵉ`'s own dead route measures a doubling fold outrunning any
-- such seeding.  Weighting the depths into a single natural is that
-- same refutation once more, since the base would have to dominate the
-- number of items a level can gain.

-- THE WIDTH TRAVELS INSIDE THE HOLDING RATHER THAN IN THE TYPE, WHICH
-- IS WHAT KEEPS EVERY CONSUMER'S SIGNATURE UNCHANGED.  A comparison
-- relates two censuses of the SAME width, and a descent never changes
-- it — the width is a reading taken once where a run enters, and the
-- whole subscription below that entry is compared against it.  Indexing
-- the carrier instead would put that reading into some fifty
-- signatures that never look at it.
------------------------------------------------------------------

infix 4 _<ᵛ_

data _<ᵛ_ : ∀ {W} → Vec ℕ W → Vec ℕ W → Set where
  vhere  : ∀ {W} {a b} {xs ys : Vec ℕ W} → a < b   → (a ∷ xs) <ᵛ (b ∷ ys)
  vthere : ∀ {W} {a} {xs ys : Vec ℕ W}   → xs <ᵛ ys → (a ∷ xs) <ᵛ (a ∷ ys)

<ᵛ-wellFounded : ∀ {W} → WellFounded (_<ᵛ_ {W})
<ᵛ-wellFounded {W} = go W
  where
  go : ∀ W (xs : Vec ℕ W) → Acc _<ᵛ_ xs
  go zero    []       = acc λ ()
  go (suc W) (a ∷ xs) = step (<-wellFounded-fast a) (go W xs)
    where
    step : ∀ {a} → Acc _<_ a → ∀ {xs : Vec ℕ W} → Acc _<ᵛ_ xs → Acc _<ᵛ_ (a ∷ xs)
    step {a} (acc fa) = step′
      where
      step′ : ∀ {xs : Vec ℕ W} → Acc _<ᵛ_ xs → Acc _<ᵛ_ (a ∷ xs)
      step′ (acc fxs) = acc λ
        { (vhere p)  → step (fa p) (go W _)
        ; (vthere q) → step′ (fxs q) }

Hold : Set
Hold = Σ ℕ (Vec ℕ)

emptyHold : ℕ → Hold
emptyHold W = W , replicate W 0

infix 4 _<ʰ_

data _<ʰ_ : Hold → Hold → Set where
  hlt : ∀ {W} {v′ v : Vec ℕ W} → v′ <ᵛ v → (W , v′) <ʰ (W , v)

<ʰ-wellFounded : WellFounded _<ʰ_
<ʰ-wellFounded (W , v) = go (<ᵛ-wellFounded v)
  where
  go : ∀ {u : Vec ℕ W} → Acc _<ᵛ_ u → Acc _<ʰ_ (W , u)
  go (acc f) = acc λ { (hlt p) → go (f p) }

------------------------------------------------------------------
-- THE NON-STRICT HOLDING ORDER, AND WHY THE COMPONENT IS A BOUND
-- RATHER THAN A READING.  A rank is what the caller fixed and a census
-- is what the run has actually written, so the two cannot be held
-- equal: an enqueue grows the store without touching any component,
-- and a frame that delivers nothing shrinks it.  The invariant is
-- therefore that the census sits UNDER the component, and the drain's
-- edge is built by taking the census AS the new component and
-- composing -- which is what the two transitivities below are for and
-- their only purpose.
------------------------------------------------------------------

infix 4 _≤ᵛ_

data _≤ᵛ_ : ∀ {W} → Vec ℕ W → Vec ℕ W → Set where
  vnil   : [] ≤ᵛ []
  vhere≤ : ∀ {W} {a b} {xs ys : Vec ℕ W} → a < b    → (a ∷ xs) ≤ᵛ (b ∷ ys)
  vthere≤ : ∀ {W} {a} {xs ys : Vec ℕ W} → xs ≤ᵛ ys → (a ∷ xs) ≤ᵛ (a ∷ ys)

≤ᵛ-refl : ∀ {W} (xs : Vec ℕ W) → xs ≤ᵛ xs
≤ᵛ-refl []       = vnil
≤ᵛ-refl (a ∷ xs) = vthere≤ (≤ᵛ-refl xs)

≤ᵛ-<ᵛ-trans : ∀ {W} {xs ys zs : Vec ℕ W} → xs ≤ᵛ ys → ys <ᵛ zs → xs <ᵛ zs
≤ᵛ-<ᵛ-trans (vhere≤ p)  (vhere q)  = vhere (<-trans p q)
≤ᵛ-<ᵛ-trans (vhere≤ p)  (vthere q) = vhere p
≤ᵛ-<ᵛ-trans (vthere≤ p) (vhere q)  = vhere q
≤ᵛ-<ᵛ-trans (vthere≤ p) (vthere q) = vthere (≤ᵛ-<ᵛ-trans p q)

infix 4 _≤ʰ_

data _≤ʰ_ : Hold → Hold → Set where
  hle : ∀ {W} {v′ v : Vec ℕ W} → v′ ≤ᵛ v → (W , v′) ≤ʰ (W , v)

≤ʰ-refl : ∀ (q : Hold) → q ≤ʰ q
≤ʰ-refl (W , v) = hle (≤ᵛ-refl v)

≤ʰ-<ʰ-trans : ∀ {q″ q′ q} → q″ ≤ʰ q′ → q′ <ʰ q → q″ <ʰ q
≤ʰ-<ʰ-trans (hle p) (hlt q) = hlt (≤ᵛ-<ᵛ-trans p q)

-- THE WEAKENING, WHICH IS WHAT LETS A DRAIN HAND ITS EXACT READING ON
-- AS A BOUND.  The step enters at a triple whose holding IS the census,
-- so what it recovers about the state it comes back with is denominated
-- in that exact reading; the caller is standing at a bound the reading
-- sits strictly under, and this is the one step between the two.
<ᵛ→≤ᵛ : ∀ {W} {xs ys : Vec ℕ W} → xs <ᵛ ys → xs ≤ᵛ ys
<ᵛ→≤ᵛ (vhere p)  = vhere≤ p
<ᵛ→≤ᵛ (vthere p) = vthere≤ (<ᵛ→≤ᵛ p)

<ʰ→≤ʰ : ∀ {q′ q} → q′ <ʰ q → q′ ≤ʰ q
<ʰ→≤ʰ (hlt p) = hle (<ᵛ→≤ᵛ p)

<ᵛ-≤ᵛ-trans : ∀ {W} {xs ys zs : Vec ℕ W} → xs <ᵛ ys → ys ≤ᵛ zs → xs <ᵛ zs
<ᵛ-≤ᵛ-trans (vhere p)  (vhere≤ q)  = vhere (<-trans p q)
<ᵛ-≤ᵛ-trans (vhere p)  (vthere≤ q) = vhere p
<ᵛ-≤ᵛ-trans (vthere p) (vhere≤ q)  = vhere q
<ᵛ-≤ᵛ-trans (vthere p) (vthere≤ q) = vthere (<ᵛ-≤ᵛ-trans p q)

<ʰ-≤ʰ-trans : ∀ {q″ q′ q} → q″ <ʰ q′ → q′ ≤ʰ q → q″ <ʰ q
<ʰ-≤ʰ-trans (hlt p) (hle q) = hlt (<ᵛ-≤ᵛ-trans p q)

≤ᵛ-trans : ∀ {W} {xs ys zs : Vec ℕ W} → xs ≤ᵛ ys → ys ≤ᵛ zs → xs ≤ᵛ zs
≤ᵛ-trans vnil        vnil        = vnil
≤ᵛ-trans (vhere≤ p)  (vhere≤ q)  = vhere≤ (<-trans p q)
≤ᵛ-trans (vhere≤ p)  (vthere≤ q) = vhere≤ p
≤ᵛ-trans (vthere≤ p) (vhere≤ q)  = vhere≤ q
≤ᵛ-trans (vthere≤ p) (vthere≤ q) = vthere≤ (≤ᵛ-trans p q)

≤ʰ-trans : ∀ {q″ q′ q} → q″ ≤ʰ q′ → q′ ≤ʰ q → q″ ≤ʰ q
≤ʰ-trans (hle p) (hle q) = hle (≤ᵛ-trans p q)

------------------------------------------------------------------
-- WHERE A DEPTH IS COUNTED, AND IT IS FORCED BY THE ORDER RATHER THAN
-- CHOSEN.  `_<ᵛ_` compares left to right and the step this component
-- exists for trades one item for any number of strictly SHALLOWER
-- ones, so the traded-away item must sit at a MORE significant
-- position than anything arriving — hence a depth is counted at its
-- distance from the deepest the width admits.  A depth the width does
-- not admit lands at the deepest position rather than nowhere, since
-- a census that silently dropped one would read as falling while the
-- store grew; nothing reaches that case, because the consumer's own
-- invariant carries a range conjunct, and it is a conjunct rather
-- than a side condition here precisely so the drop below can spend it.

-- THE DROP IS STATED OVER POSITIONS AND NOT OVER DEPTHS, WHICH IS
-- WHAT KEEPS IT PROVABLE BY PURE VECTOR INDUCTION.  Turning a depth
-- into a position is a subtraction and reverses the comparison, so
-- carrying that step inside the induction would put an arithmetic
-- obligation in every arm; the consumer does the conversion once and
-- spends this in the form it is already in.
------------------------------------------------------------------

bumpAt : ∀ {W} → ℕ → Vec ℕ W → Vec ℕ W
bumpAt _       []      = []
bumpAt zero    (c ∷ v) = suc c ∷ v
bumpAt (suc k) (c ∷ v) = c ∷ bumpAt k v

censusAt : ∀ {W} → Vec ℕ W → List ℕ → Vec ℕ W
censusAt v ks = foldr bumpAt v ks

-- the conversion is DEFINITIONAL and not a lemma, which is the point of
-- naming it: a census stated over depths reduces to one over positions
-- with no rewrite, so the drop is spent in the form it was proven in
positions : ℕ → List ℕ → List ℕ
positions W ds = map (λ d → W ∸ suc d) ds

censusOfDepths : ∀ {W} → List ℕ → Vec ℕ W
censusOfDepths {W} ds = censusAt (replicate W 0) (positions W ds)

-- a position nothing arriving can reach is a position nothing arriving
-- disturbs: every later bump goes into the tail, definitionally
bump-tail : ∀ {W} (c : ℕ) (v : Vec ℕ W) (ks : List ℕ) → All (0 <_) ks →
            censusAt (c ∷ v) ks ≡ c ∷ censusAt v (map pred ks)
bump-tail c v []             []ᵃ          = refl
bump-tail c v (suc k ∷ ks) (_ ∷ᵃ ps) =
  cong (bumpAt (suc k)) (bump-tail c v ks ps)

census-drop : ∀ {W} (k : ℕ) (v : Vec ℕ W) (ks : List ℕ) →
              k < W → All (k <_) ks →
              censusAt v ks <ᵛ bumpAt k v
census-drop {suc W} zero (c ∷ v) ks _ ps
  rewrite bump-tail c v ks (All.map (λ {x} lt → lt) ps) = vhere (n<1+n c)
census-drop {suc W} (suc k) (c ∷ v) ks (s≤s lt) ps
  rewrite bump-tail c v ks (All.map (λ {x} p → ≤-trans (s≤s z≤n) p) ps) =
    vthere (census-drop k v (map pred ks) lt (pred-all ps))
  where
  pred-all : ∀ {ks} → All (suc k <_) ks → All (k <_) (map pred ks)
  pred-all []ᵃ               = []ᵃ
  pred-all (_∷ᵃ_ {x = suc _} (s≤s p) qs) = p ∷ᵃ pred-all qs

-- AND THE OTHER DROP, WHICH IS PURE REMOVAL AND IS WHAT AN EDGE
-- ACTUALLY SPENDS.  A reading is taken over the WHOLE store, so the one
-- item a step takes out of it sits in the middle of the list rather
-- than at its head; bumps at different positions commute, so the fold
-- may be reassociated around any single element and the removal is then
-- a bump undone at a position the range conjunct already places.
bump-comm : ∀ {W} (j k : ℕ) (v : Vec ℕ W) →
            bumpAt j (bumpAt k v) ≡ bumpAt k (bumpAt j v)
bump-comm j       k       []      = refl
bump-comm zero    zero    (c ∷ v) = refl
bump-comm zero    (suc k) (c ∷ v) = refl
bump-comm (suc j) zero    (c ∷ v) = refl
bump-comm (suc j) (suc k) (c ∷ v) = cong (c ∷_) (bump-comm j k v)

bump-out : ∀ {W} (d : ℕ) (v : Vec ℕ W) (ks : List ℕ) →
           censusAt (bumpAt d v) ks ≡ bumpAt d (censusAt v ks)
bump-out d v []       = refl
bump-out d v (k ∷ ks) =
  trans (cong (bumpAt k) (bump-out d v ks)) (bump-comm k d (censusAt v ks))

census-remove : ∀ {W} (v : Vec ℕ W) (xs ys : List ℕ) (d : ℕ) →
                censusAt v (xs ++ d ∷ ys) ≡ bumpAt d (censusAt v (xs ++ ys))
census-remove v xs ys d =
  trans (foldr-++ bumpAt v xs (d ∷ ys))
    (trans (bump-out d (censusAt v ys) xs)
      (cong (bumpAt d) (sym (foldr-++ bumpAt v xs ys))))

bump-drop : ∀ {W} (k : ℕ) (v : Vec ℕ W) → k < W → v <ᵛ bumpAt k v
bump-drop {suc W} zero    (c ∷ v) _       = vhere (n<1+n c)
bump-drop {suc W} (suc k) (c ∷ v) (s≤s p) = vthere (bump-drop k v p)

census-remove-drop : ∀ {W} (v : Vec ℕ W) (xs ys : List ℕ) (d : ℕ) → d < W →
                     censusAt v (xs ++ ys) <ᵛ censusAt v (xs ++ d ∷ ys)
census-remove-drop v xs ys d lt
  rewrite census-remove v xs ys d = bump-drop d (censusAt v (xs ++ ys)) lt

-- and the same statement read off a list of DEPTHS, which is the form
-- every consumer has: `map` carries the split through the conversion,
-- so the position the removal happens at is the depth's own and no
-- consumer performs the subtraction itself.
census-depths-drop : ∀ {W} (xs ys : List ℕ) (d : ℕ) → W ∸ suc d < W →
                     censusOfDepths {W} (xs ++ ys)
                       <ᵛ censusOfDepths {W} (xs ++ d ∷ ys)
census-depths-drop {W} xs ys d lt
  rewrite map-++ (λ k → W ∸ suc k) xs (d ∷ ys)
        | map-++ (λ k → W ∸ suc k) xs ys =
  census-remove-drop (replicate W 0) (positions W xs) (positions W ys)
    (W ∸ suc d) lt

------------------------------------------------------------------
-- THE CARRIER.  A named synonym rather than a record, because every
-- producer of one of these builds it from measures that are already
-- separately named, and a record would put a constructor between the
-- edge lemmas and the arithmetic they are proven from.
------------------------------------------------------------------

Tri : Set
Tri = ℕ × Hold × ℕ × ℕ

------------------------------------------------------------------
-- THE ORDER.  Lexicographic, outermost component first.  One
-- constructor per RE-ENTRY edge, and that correspondence is the whole
-- design: `ltU` is the connect edge, `ltQ` the merge drain, `ltR` the
-- hop edge, `ltS` the μ edge.  Read the other way it is a coverage
-- claim — a fifth constructor here would mean a fifth edge in the
-- evaluator, and a re-entry site inhabiting none of the four is a site
-- this order does not yet cover.

-- THE HOLDING SITS UNDER THE SHARE COUNT AND OVER THE RANK, AND BOTH
-- sides of that are forced.  A connect subscribes a shared source,
-- which may emit and so may FILL a store — so the holding cannot be
-- outermost.  The drain enters DEEPER than the rank in force, since a
-- value the store has been holding is under whatever rank stood when it
-- was put there and the hop chain below has lowered that rank since —
-- so the rank cannot be above the holding.

-- AND THAT COVERAGE CLAIM IS HELD BY A MACHINE RATHER THAN BY THIS
-- PARAGRAPH, IN TWO PLACES.  The builder takes an `Acc` over this order
-- as an ARGUMENT, so Agda's own termination check holds every member of
-- its cycle to descending on something it carries -- per call site,
-- rather than on a declaration's word.  What that cannot see is a cycle
-- re-entering the block from OUTSIDE it, so `make recursion-cover` cuts
-- the builder's call graph and fails on any cycle the source does not
-- declare; today it leaves exactly the one the builder declares
-- structural.  So the constructors here are not a guess at which sites
-- matter, and a fifth site goes red rather than compiling quietly.
------------------------------------------------------------------

infix 4 _≺_

data _≺_ : Tri → Tri → Set where
  ltU : ∀ {U′ U q′ q r′ r s′ s} → U′ < U   → (U′ , q′ , r′ , s′) ≺ (U , q , r , s)
  ltQ : ∀ {U q′ q r′ r s′ s}    → q′ <ʰ q  → (U  , q′ , r′ , s′) ≺ (U , q , r , s)
  ltR : ∀ {U q r′ r s′ s}       → r′ < r   → (U  , q  , r′ , s′) ≺ (U , q , r , s)
  ltS : ∀ {U q r s′ s}          → s′ < s   → (U  , q  , r  , s′) ≺ (U , q , r , s)

------------------------------------------------------------------
-- WELL-FOUNDEDNESS.  Four nested levels, one per component: the
-- outermost binds the share count's witness, and a drop in it restarts
-- the three below at their own well-foundedness, since none of them is
-- constrained when a component above them moves.

-- IT IS BUILT ON THE SKIPPING WITNESS, AND THAT IS A REDUCTION
-- REQUIREMENT RATHER THAN A TASTE.  The evaluator RUNS on this proof —
-- the bug cache and the oracle both normalise a subscription — so every
-- component's accessibility is unfolded at every edge.  The ordinary
-- witness is structural in the proof it is handed, so it walks the
-- whole component per step; the skipping one hands back an accessor
-- that reads nothing, and the components here are seeded from program
-- size.  The holding's witness inherits that, since its recursion is on
-- the WIDTH and each position is the skipping one again.
------------------------------------------------------------------

≺-wellFounded : WellFounded _≺_
≺-wellFounded (U , q , r , s) =
  goU (<-wellFounded-fast U) (<ʰ-wellFounded q)
      (<-wellFounded-fast r) (<-wellFounded-fast s)
  where
  goU : ∀ {U} → Acc _<_ U → ∀ {q} → Acc _<ʰ_ q →
        ∀ {r} → Acc _<_ r → ∀ {s} → Acc _<_ s → Acc _≺_ (U , q , r , s)
  goU {U} (acc fU) = goQ
    where
    goQ : ∀ {q} → Acc _<ʰ_ q →
          ∀ {r} → Acc _<_ r → ∀ {s} → Acc _<_ s → Acc _≺_ (U , q , r , s)
    goQ {q} (acc fq) = goR
      where
      goR : ∀ {r} → Acc _<_ r → ∀ {s} → Acc _<_ s → Acc _≺_ (U , q , r , s)
      goR {r} (acc fr) = goS
        where
        goS : ∀ {s} → Acc _<_ s → Acc _≺_ (U , q , r , s)
        goS (acc fs) = acc λ
          { (ltU u) → goU (fU u) (<ʰ-wellFounded _)
                          (<-wellFounded-fast _) (<-wellFounded-fast _)
          ; (ltQ p) → goQ (fq p) (<-wellFounded-fast _) (<-wellFounded-fast _)
          ; (ltR p) → goR (fr p) (<-wellFounded-fast _)
          ; (ltS p) → goS (fs p) }
