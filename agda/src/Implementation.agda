module Implementation where

open import Data.Bool    using (Bool; true; false; if_then_else_)
open import Data.Nat     using (_≡ᵇ_)
open import Data.List    using (List; []; _∷_; _++_)
open import Data.Maybe   using (Maybe; just; nothing; fromMaybe)
open import Data.Product using (_×_; _,_)

open import Rx.Prim using (Id; Source; InstEvent; init; value; close; handoff;
                           complete; EmitKind; subscribe; delivery;
                           InstEmit; _at_from_as_)
open import Rx.Protocol using (Owed; countIn; removeOne; hasOwed; bumpOwed;
                               payOwed; allZero)

------------------------------------------------------------------
-- The ONLINE batcher: one emission at a time, own state only, no
-- lookahead.  It is Rx.Protocol's automaton run in producing mode —
-- the same live/owed arithmetic, but where the automaton REJECTS a
-- broken stream, the batcher clamps (fromMaybe) and carries on, and
-- where the automaton demands "fully paid", the batcher FLUSHES:
-- the moment an instant's obligations hit zero, its batch is
-- emitted — as soon as complete, never later.  Instants that never
-- take on obligations (subscribe frames: owed stays empty) flush
-- lazily, at the next instant or the end of the stream — nothing in
-- the protocol marks a subscribe frame's end from inside.
------------------------------------------------------------------

record OpenBatch (A : Set) : Set where
  field instant : Id              -- the batch's id (a batched stream re-batches)
        source  : Source          -- envelope of the instant's FIRST emit,
        kind    : EmitKind        -- matching the spec's batchOf
        values  : List A          -- accumulated in stream order
        owed    : Owed            -- remaining owed per source

record BatchSt (A : Set) : Set where
  field live    : List Source     -- multiset: one entry per live registration
        current : Maybe (OpenBatch A)

batch-init : ∀ {A : Set} → BatchSt A
batch-init = record { live = [] ; current = nothing }

-- a finished batch: one value event under the instant's own
-- envelope — dropped when valueless (the spec's batchOf, online)
closeBatch : ∀ {A : Set} → OpenBatch A → List (InstEmit (List A))
closeBatch b with OpenBatch.values b
... | []     = []
... | v ∷ vs = ((value (v ∷ vs) ∷ [])
                 at OpenBatch.instant b
                 from OpenBatch.source b
                 as OpenBatch.kind b) ∷ []

-- Rx.Protocol's settle, clamped total: a subscription's own burst is
-- net zero; a delivery pays owed[s], seeded from live(s) — the
-- multiset BEFORE this emit's events — at s's first delivery
settleBatch : EmitKind → Source → List Source → Owed → Owed
settleBatch subscribe s live owed = owed
settleBatch delivery  s live owed =
  let seeded = if hasOwed s owed then owed else bumpOwed s (countIn s live) owed
  in fromMaybe seeded (payOwed s seeded)

-- Rx.Protocol's applyEvents, clamped total, also collecting values:
-- inits enlist, closes retire, a handoff bumps the announced share's
-- owed by its live count AT THE ANNOUNCEMENT, values accumulate
applyBatch : ∀ {A : Set} → List (InstEvent A)
           → List Source → Owed → List A
           → List Source × Owed × List A
applyBatch []                 live owed vs = live , owed , vs
applyBatch (init x    ∷ es) live owed vs = applyBatch es (x ∷ live) owed vs
applyBatch (value v   ∷ es) live owed vs = applyBatch es live owed (vs ++ v ∷ [])
applyBatch (handoff x ∷ es) live owed vs =
  applyBatch es live (bumpOwed x (countIn x live) owed) vs
applyBatch (complete  ∷ es) live owed vs = applyBatch es live owed vs
applyBatch (close x _ ∷ es) live owed vs =
  applyBatch es (fromMaybe live (removeOne x live)) owed vs

-- obligations existed and are now discharged — the instant is over.
-- An empty owed table is NOT closure: a subscribe frame never takes
-- on obligations and stays open until the next instant brackets it
paidOff : Owed → Bool
paidOff []      = false
paidOff (e ∷ o) = allZero (e ∷ o)

step-batch : ∀ {A : Set} → InstEmit A → BatchSt A
           → List (InstEmit (List A)) × BatchSt A
step-batch {A} (es at i from s as k) st = step admitted
  where
  fresh : OpenBatch A
  fresh = record { instant = i ; source = s ; kind = k
                 ; values = [] ; owed = [] }

  -- same instant continues the open batch; a new instant flushes it
  -- (the lazy bracket for obligation-free subscribe frames)
  admitted : List (InstEmit (List A)) × OpenBatch A
  admitted with BatchSt.current st
  ... | nothing = [] , fresh
  ... | just b  = if OpenBatch.instant b ≡ᵇ i
                  then [] , b
                  else closeBatch b , fresh

  step : List (InstEmit (List A)) × OpenBatch A
       → List (InstEmit (List A)) × BatchSt A
  step (flushed , b) =
    let owed₁ = settleBatch k s (BatchSt.live st) (OpenBatch.owed b)
        (live′ , owed₂ , vals′) =
          applyBatch es (BatchSt.live st) owed₁ (OpenBatch.values b)
        b′ = record b { owed = owed₂ ; values = vals′ }
    in if paidOff owed₂
       then flushed ++ closeBatch b′
            , record { live = live′ ; current = nothing }
       else flushed
            , record { live = live′ ; current = just b′ }

flushBatch : ∀ {A : Set} → BatchSt A → List (InstEmit (List A))
flushBatch st with BatchSt.current st
... | nothing = []
... | just b  = closeBatch b

foldBatch : ∀ {A : Set} → BatchSt A → List (InstEmit A) → List (InstEmit (List A))
foldBatch st []       = flushBatch st
foldBatch st (x ∷ xs) = let (out , st′) = step-batch x st
                        in out ++ foldBatch st′ xs

impl-batchSimultaneous : ∀ {A : Set} → List (InstEmit A) → List (InstEmit (List A))
impl-batchSimultaneous = foldBatch batch-init
