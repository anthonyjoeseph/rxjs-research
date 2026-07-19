module Rx.Protocol where

open import Data.Bool    using (Bool; true; false; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _≡ᵇ_; _≤ᵇ_)
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
--   instant completion  — once a SEEDED instant's obligations hit
--                         zero the instant is OVER: further
--                         same-instant traffic is rejected.  This
--                         makes the online batcher's flush point
--                         protocol law — without it, a post-payoff
--                         subscribe emit could smuggle values into
--                         an instant the batcher already closed,
--                         and batch-agreement would be false.
--                         (Obligation-free instants — subscribe
--                         frames, whose owed table never seeds —
--                         are exempt: paidOff [] is false.)
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
        horizon : Id                   -- freshness watermark: every past instant is
                                       -- < horizon (ids mint from arrival position —
                                       -- 0 the subscribe frame, then 1, 2, … — so
                                       -- instants strictly increase along the stream)
        current : Maybe (Id × Owed)    -- the open instant, if any
        done    : Bool                 -- a complete event has been consumed

protocol-init : ProtocolSt
protocol-init = record { live = [] ; horizon = 0 ; current = nothing ; done = false }

------------------------------------------------------------------
-- multiset / association-list plumbing
------------------------------------------------------------------

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

-- a cutPending victim's cancellation: one owed count forgiven.
-- STRICT: cancelling below zero rejects (the writer claimed a victim
-- the source was never owed).  A victim of a source with no entry —
-- one not firing this instant — is a benign no-op: its owed never
-- seeds, or seeds later from a live count the close already shrank.
cancelOwed : Source → Owed → Maybe Owed
cancelOwed s [] = just []
cancelOwed s ((x , n) ∷ o) with s ≡ᵇ x | n
... | true  | zero  = nothing
... | true  | suc m = just ((x , m) ∷ o)
... | false | _     with cancelOwed s o
...   | just o′ = just ((x , n) ∷ o′)
...   | nothing = nothing

allZero : Owed → Bool
allZero []                = true
allZero ((_ , zero)  ∷ o) = allZero o
allZero ((_ , suc _) ∷ o) = false

-- obligations existed and are now discharged — the instant is over.
-- An empty owed table is NOT closure: a subscribe frame never takes
-- on obligations and stays open until the next instant brackets it.
-- Shared with Implementation: the batcher flushes exactly here
paidOff : Owed → Bool
paidOff []      = false
paidOff (e ∷ o) = allZero (e ∷ o)

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
applyEvents (close x cutPending ∷ es) live owed done
  with removeOne x live | cancelOwed x owed
... | just live′ | just owed′ = applyEvents es live′ owed′ done
... | _          | _          = nothing
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

-- leaving the current instant (for a new one, or at end of stream) is
-- legal only fully paid; the departed instant pushes the horizon.
-- THE single instant-close judgment — stepProtocol's id-change and
-- checkFinal both consume it
settleInstant : ProtocolSt → Maybe Id
settleInstant ps with ProtocolSt.current ps
... | nothing         = just (ProtocolSt.horizon ps)
... | just (j , owed) =
      if allZero owed then just (suc j) else nothing

stepProtocol : ∀ {A : Set} → InstEmit A → ProtocolSt → Maybe ProtocolSt
stepProtocol (es at i from s as k) ps = enter
  where
  -- run one emit inside instant i (owed so far, horizon so far)
  go : Owed → Id → Maybe ProtocolSt
  go owed horizon′ with settle k s (ProtocolSt.live ps) owed
  ... | nothing    = nothing
  ... | just owed′ with applyEvents es (ProtocolSt.live ps) owed′ (ProtocolSt.done ps)
  ...   | nothing                      = nothing
  ...   | just (live′ , owed″ , done′) =
          just (record { live    = live′
                       ; horizon = horizon′
                       ; current = just (i , owed″)
                       ; done    = done′ })

  -- a new instant: the old one settles fully paid, and freshness is
  -- one comparison — instants strictly increase (arrival-position ids)
  openFresh : Maybe ProtocolSt
  openFresh with settleInstant ps
  ... | nothing       = nothing
  ... | just horizon′ = if horizon′ ≤ᵇ i then go [] horizon′ else nothing

  enter : Maybe ProtocolSt
  enter with ProtocolSt.current ps
  ... | nothing         = openFresh
  ... | just (j , owed) =
        if i ≡ᵇ j
        then (if paidOff owed
              then nothing   -- instant completion: the instant is over
              else go owed (ProtocolSt.horizon ps))
        else openFresh

runProtocol : ∀ {A : Set} → ProtocolSt → List (InstEmit A) → Maybe ProtocolSt
runProtocol ps []       = just ps
runProtocol ps (x ∷ xs) with stepProtocol x ps
... | just ps′ = runProtocol ps′ xs
... | nothing  = nothing

accepts? : {A : Set} → Maybe A → Bool
accepts? nothing  = false
accepts? (just _) = true

-- the stream may end only between cascades: the final instant is
-- held to the same settleInstant bar as a departed one
paidUp : ProtocolSt → Bool
paidUp ps = accepts? (settleInstant ps)

checkFinal : Maybe ProtocolSt → Maybe ProtocolSt
checkFinal nothing   = nothing
checkFinal (just ps) = if paidUp ps then just ps else nothing

data Accepted {A : Set} : Maybe A → Set where
  accepted : ∀ {s} → Accepted (just s)

WellFormed : ∀ {A : Set} → List (InstEmit A) → Set
WellFormed xs = Accepted (checkFinal (runProtocol protocol-init xs))

-- the Bool twin of WellFormed, for the QuickCheck harness
wellFormed? : ∀ {A : Set} → List (InstEmit A) → Bool
wellFormed? xs = accepts? (checkFinal (runProtocol protocol-init xs))
