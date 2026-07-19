module Rx.Protocol where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_; not)
open import Data.Nat     using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_)
open import Data.List    using (List; []; _∷_)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)

open import Rx.Prim using (Id; Source; InstEvent; init; value; close; handoff;
                           complete; CloseReason; cutPending;
                           EmitKind; subscribe; delivery; plumbing;
                           InstEmit; _at_from_as_)

------------------------------------------------------------------
-- The protocol automaton: InstEmit's contract made explicit.
-- batchSimultaneous is total and trusting — the impl reads only
-- init/close counts, the spec reads only instant ids.  WellFormed
-- is the bridge premise that the two vocabularies tell the same
-- story on a stream: what the evaluator promises
-- (evaluate-well-formed) and what the batcher assumes
-- (batch-agreement).  Every fact here is WRITER-ASSERTED (the kind
-- tag, the handoff announcement, the close reason) and the
-- automaton only checks; it never reconstructs.  stepProtocol
-- rejects (nothing) any emit breaking a clause:
--
--   instant freshness   — an instant is one contiguous run of
--                         emits; once left it never recurs
--   bracketing          — every close matches a live init; the
--                         live multiset never underflows.  The
--                         close REASON is load-bearing for owed:
--                         cutPending marks a registration cut
--                         BEFORE its delivery — it will never pay,
--                         so one owed count is cancelled against it
--   fan-out exactness   — subscribe and plumbing emits owe nothing
--                         and pay nothing.  A delivery from s pays owed[s]:
--                         seeded to live(s) at s's first delivery
--                         of the instant (the arrival's implicit
--                         announcement), and bumped by live(x) at
--                         every `handoff x` (a share's explicit
--                         one — so multi-round fan-outs and
--                         announced-but-missing fan-outs are both
--                         accounted).  An instant may only be left
--                         (or the stream end) fully paid.
--   complete discipline — after a complete event no further VALUE
--                         is emitted.  (Not "the stream ends": a
--                         connected share never disconnects, so its
--                         valueless chain emits and empty fan-outs
--                         legitimately outlive the root's completion)
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
hasOwed s []            = false
hasOwed s ((x , _) ∷ o) = if s ≡ᵇ x then true else hasOwed s o

bumpOwed : Source → ℕ → Owed → Owed
bumpOwed s k []            = (s , k) ∷ []
bumpOwed s k ((x , n) ∷ o) =
  if s ≡ᵇ x then (x , k + n) ∷ o else (x , n) ∷ bumpOwed s k o

payOwed : Source → Owed → Maybe Owed     -- decrement; nothing on underflow
payOwed s [] = nothing
payOwed s ((x , n) ∷ o) with s ≡ᵇ x | n
... | true  | zero  = nothing
... | true  | suc m = just ((x , m) ∷ o)
... | false | _     with payOwed s o
...   | just o′ = just ((x , n) ∷ o′)
...   | nothing = nothing

-- a cutPending victim's cancellation: one owed count forgiven
-- (clamped; a victim of a source not firing this instant is a no-op)
cancelOwed : Source → Owed → Owed
cancelOwed s []            = []
cancelOwed s ((x , n) ∷ o) =
  if s ≡ᵇ x then (x , n ∸ 1) ∷ o else (x , n) ∷ cancelOwed s o

allZero : Owed → Bool
allZero []                = true
allZero ((_ , zero)  ∷ o) = allZero o
allZero ((_ , suc _) ∷ o) = false

------------------------------------------------------------------
-- one emit's events, folded left to right through the state: inits
-- enlist, closes must match (bracketing), a handoff bumps the
-- announced share's owed count by its live registrations AT THE
-- ANNOUNCEMENT (frame traffic earlier in the same emit already
-- applied — matching the dispatch-time registry), complete flips
-- done, values carry no traffic
------------------------------------------------------------------

applyEvents : ∀ {A : Set} → List (InstEvent A)
            → List Source → Owed → Bool
            → Maybe (List Source × Owed × Bool)
applyEvents []                 live owed done = just (live , owed , done)
applyEvents (init x    ∷ es) live owed done = applyEvents es (x ∷ live) owed done
applyEvents (value _   ∷ es) live owed done =
  if done then nothing else applyEvents es live owed done
applyEvents (handoff x ∷ es) live owed done =
  applyEvents es live (bumpOwed x (countIn x live) owed) done
applyEvents (complete  ∷ es) live owed done = applyEvents es live owed true
applyEvents (close x cutPending ∷ es) live owed done with removeOne x live
... | just live′ = applyEvents es live′ (cancelOwed x owed) done
... | nothing    = nothing
applyEvents (close x _ ∷ es) live owed done with removeOne x live
... | just live′ = applyEvents es live′ owed done
... | nothing    = nothing

-- the kind tag IS the payment rule: a subscription's own burst and
-- a share's forwarded connect burst are net zero; a delivery pays
-- owed[s], seeded from live(s) — the multiset BEFORE this emit's
-- events, matching the cascade's chain snapshot — at s's first
-- delivery of the instant
settle : EmitKind → Source → List Source → Owed → Maybe Owed
settle subscribe s live owed = just owed
settle plumbing  s live owed = just owed
settle delivery  s live owed =
  if hasOwed s owed
  then payOwed s owed
  else payOwed s (bumpOwed s (countIn s live) owed)

------------------------------------------------------------------
-- the step
------------------------------------------------------------------

stepProtocol : ∀ {A : Set} → InstEmit A → ProtocolSt → Maybe ProtocolSt
stepProtocol (es at i from s as k) ps = enter
  where
  -- run one emit inside instant i (owed so far, instants closed so far)
  go : Owed → List Id → Maybe ProtocolSt
  go owed seen′ with settle k s (ProtocolSt.live ps) owed
  ... | nothing    = nothing
  ... | just owed′ with applyEvents es (ProtocolSt.live ps) owed′ (ProtocolSt.done ps)
  ...   | nothing                      = nothing
  ...   | just (live′ , owed″ , done′) =
          just (record { live    = live′
                       ; seen    = seen′
                       ; current = just (i , owed″)
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

-- the Bool twin, for the QuickCheck harness: computes the same
-- acceptance the Accepted proof witnesses
accepts? : {A : Set} → Maybe A → Bool
accepts? nothing  = false
accepts? (just _) = true

wellFormed? : ∀ {A : Set} → List (InstEmit A) → Bool
wellFormed? xs = accepts? (checkFinal (runProtocol protocol-init xs))
