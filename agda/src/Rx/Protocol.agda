module Rx.Protocol where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_; not)
open import Data.Nat     using (ℕ; zero; suc; _≡ᵇ_)
open import Data.List    using (List; []; _∷_)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)

open import Rx.Prim using (Id; Source; InstEvent; init; value; close; complete;
                           InstEmit; _at_from_)

------------------------------------------------------------------
-- The protocol automaton: InstEmit's contract made explicit.
-- batchSimultaneous is total and trusting — the impl reads only
-- init/close counts, the spec reads only instant ids.  WellFormed
-- is the bridge premise that the two vocabularies tell the same
-- story on a stream: what the evaluator promises
-- (evaluate-well-formed) and what the batcher assumes
-- (batch-agreement).  stepProtocol rejects (nothing) any emit
-- breaking a clause:
--
--   instant freshness   — an instant is one contiguous run of
--                         emits; once left it never recurs
--   bracketing          — every close matches a live init; the
--                         live multiset never underflows
--   fan-out exactness   — within an instant, a source that fires
--                         delivers EXACTLY ONE emit per live
--                         registration: the owed count snapshots
--                         live(s) at s's first delivery and every
--                         delivery pays it down; an instant may
--                         only be left (or the stream end) fully
--                         paid.  This is the clause that makes
--                         owed = live-count recover boundaries.
--   complete discipline — after a complete event the stream ends
--
-- The contested heart is `settle`: which emits PAY the owed count
-- and which are births that owe nothing.  A registration born in
-- the subscribe frame (or a share-connect burst) emits its own
-- init emit; one born mid-arrival-cascade is silent until the next
-- arrival (dispatch snapshots the registry before it joins).  The
-- stream must let a reader tell these apart — that this is exactly
-- possible is a cousin of the open observable-provenance question,
-- and these clauses are the first concrete conjecture:
--   · init s AND close s in one emit from s: a one-shot (born and
--     died here) — owes nothing, pays nothing
--   · leading init s with live(s) = 0: a fresh registration's
--     subscribe emit — its emit is its own birth, net zero
--   · an emit that is EXACTLY [init s] with live(s) > 0: a bare
--     re-registration of an already-live source — net zero
--   · anything else from s is a delivery and pays
-- Expect QuickCheck to tune this file; the SHAPE (an online
-- automaton over live/seen/owed) is the commitment, the clause
-- list is the current best conjecture.
------------------------------------------------------------------

Owed : Set                    -- this instant: remaining owed per source
Owed = List (Source × ℕ)

record ProtocolSt : Set where
  field live    : List Source          -- multiset: one entry per live registration
        seen    : List Id              -- closed instants (freshness)
        current : Maybe (Id × Owed)    -- the open instant, if any
        done    : Bool                 -- a complete event has been consumed

protocol-init : ProtocolSt
protocol-init = record { live = [] ; seen = [] ; current = nothing ; done = false }

------------------------------------------------------------------
-- multiset / association-list plumbing
------------------------------------------------------------------

memberℕ : ℕ → List ℕ → Bool
memberℕ i []       = false
memberℕ i (j ∷ js) = if i ≡ᵇ j then true else memberℕ i js

countIn : Source → List Source → ℕ
countIn s []       = zero
countIn s (x ∷ xs) = if s ≡ᵇ x then suc (countIn s xs) else countIn s xs

removeOne : Source → List Source → Maybe (List Source)
removeOne s []       = nothing
removeOne s (x ∷ xs) with s ≡ᵇ x
... | true  = just xs
... | false with removeOne s xs
...   | just xs′ = just (x ∷ xs′)
...   | nothing  = nothing

hasOwed : Source → Owed → Bool
hasOwed s []             = false
hasOwed s ((x , _) ∷ o) = if s ≡ᵇ x then true else hasOwed s o

payOwed : Source → Owed → Maybe Owed     -- decrement; nothing on underflow
payOwed s [] = nothing
payOwed s ((x , n) ∷ o) with s ≡ᵇ x | n
... | true  | zero  = nothing
... | true  | suc m = just ((x , m) ∷ o)
... | false | _     with payOwed s o
...   | just o′ = just ((x , n) ∷ o′)
...   | nothing = nothing

allZero : Owed → Bool
allZero []                = true
allZero ((_ , zero)  ∷ o) = allZero o
allZero ((_ , suc _) ∷ o) = false

------------------------------------------------------------------
-- reading one emit's event list
------------------------------------------------------------------

hasInit : ∀ {A : Set} → Source → List (InstEvent A) → Bool
hasInit s []             = false
hasInit s (init x ∷ es)  = if s ≡ᵇ x then true else hasInit s es
hasInit s (_      ∷ es)  = hasInit s es

hasClose : ∀ {A : Set} → Source → List (InstEvent A) → Bool
hasClose s []             = false
hasClose s (close x ∷ es) = if s ≡ᵇ x then true else hasClose s es
hasClose s (_       ∷ es) = hasClose s es

leadingInit : ∀ {A : Set} → Source → List (InstEvent A) → Bool
leadingInit s (init x ∷ _) = s ≡ᵇ x
leadingInit s _            = false

exactlyInit : ∀ {A : Set} → Source → List (InstEvent A) → Bool
exactlyInit s (init x ∷ []) = s ≡ᵇ x
exactlyInit s _             = false

-- fold the events through the registry: inits enlist, closes must
-- match (bracketing), complete flips done, values carry no traffic
applyEvents : ∀ {A : Set} → List (InstEvent A) → List Source → Bool
            → Maybe (List Source × Bool)
applyEvents []               live done = just (live , done)
applyEvents (init x   ∷ es) live done = applyEvents es (x ∷ live) done
applyEvents (value _  ∷ es) live done = applyEvents es live done
applyEvents (complete ∷ es) live done = applyEvents es live true
applyEvents (close x  ∷ es) live done with removeOne x live
... | just live′ = applyEvents es live′ done
... | nothing    = nothing

-- fan-out payment: snapshot live(s) at s's first delivery of the
-- instant, then every delivery pays one.  live is the multiset
-- BEFORE this emit's events — births inside the delivery (flattened
-- inner subscriptions) never owe this instant
settle : ∀ {A : Set} → List (InstEvent A) → Source → List Source → Owed
       → Maybe Owed
settle es s live owed =
  if hasInit s es ∧ hasClose s es
  then just owed                                   -- one-shot: born and died here
  else if leadingInit s es ∧ (countIn s live ≡ᵇ 0)
  then just owed                                   -- fresh registration's subscribe emit
  else if exactlyInit s es
  then just owed                                   -- bare re-registration, live source
  else if hasOwed s owed
  then payOwed s owed                              -- delivery: pay
  else payOwed s ((s , countIn s live) ∷ owed)     -- first delivery: snapshot, pay

------------------------------------------------------------------
-- the step
------------------------------------------------------------------

stepProtocol : ∀ {A : Set} → InstEmit A → ProtocolSt → Maybe ProtocolSt
stepProtocol (es at i from s) ps = if ProtocolSt.done ps then nothing else enter
  where
  -- run one emit inside instant i (owed so far, instants closed so far)
  go : Owed → List Id → Maybe ProtocolSt
  go owed seen′ with settle es s (ProtocolSt.live ps) owed
  ... | nothing    = nothing
  ... | just owed′ with applyEvents es (ProtocolSt.live ps) false
  ...   | nothing              = nothing
  ...   | just (live′ , done′) =
          just (record { live    = live′
                       ; seen    = seen′
                       ; current = just (i , owed′)
                       ; done    = done′ })

  enter : Maybe ProtocolSt
  enter with ProtocolSt.current ps
  ... | nothing = if memberℕ i (ProtocolSt.seen ps)
                  then nothing                     -- a closed instant recurring
                  else go [] (ProtocolSt.seen ps)
  ... | just (j , owed) =
        if i ≡ᵇ j
        then go owed (ProtocolSt.seen ps)
        else if allZero owed ∧ not (memberℕ i (j ∷ ProtocolSt.seen ps))
        then go [] (j ∷ ProtocolSt.seen ps)        -- j closes fully paid; i opens
        else nothing

runProtocol : ∀ {A : Set} → ProtocolSt → List (InstEmit A) → Maybe ProtocolSt
runProtocol ps []       = just ps
runProtocol ps (x ∷ xs) with stepProtocol x ps
... | just ps′ = runProtocol ps′ xs
... | nothing  = nothing

-- the stream may end only between cascades: the final instant is
-- held to the same fully-paid bar as a closed one
paidUp : ProtocolSt → Bool
paidUp ps with ProtocolSt.current ps
... | nothing         = true
... | just (_ , owed) = allZero owed

checkFinal : Maybe ProtocolSt → Maybe ProtocolSt
checkFinal nothing   = nothing
checkFinal (just ps) = if paidUp ps then just ps else nothing

data Accepted {A : Set} : Maybe A → Set where
  accepted : ∀ {s} → Accepted (just s)

WellFormed : ∀ {A : Set} → List (InstEmit A) → Set
WellFormed xs = Accepted (checkFinal (runProtocol protocol-init xs))
