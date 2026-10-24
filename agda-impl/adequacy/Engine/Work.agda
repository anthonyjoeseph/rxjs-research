{-# OPTIONS --guardedness #-}

-- WHAT A CONFIGURATION STILL OWES, counted.  Everything finite a state
-- tree holds and will spend by its own marks and subscriptions: a
-- program not yet subscribed, by its syntax up to a `defer`; an of's
-- values and its end; a started cold's stop, and the values its frame
-- plays before it next yields; a kill switch's attach; a takeWhile's owed completion and cut; a
-- flatMap's outer, the values waiting for a slot, each lane's retirement;
-- a connect's body mark, its source's attach and teardown; a joiner's
-- inbox; and an event in flight, owed until it is shown or absorbed.
--
-- Making an event spends what made it and owes the event, so the count
-- stays and the control leaves calm (`calmᶜ`); an event rising spends
-- height (`flightᶜ`).  A stall or a frame's close drops a skip of the
-- meaning (`adequacy.Content.silent-exact`), so a cold owes only the run
-- of values up to its next one, finite by `Frame`.
module adequacy.Engine.Work where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_)

open import denotation.MonotonicList.Events using (Timeline; fixed; fresh; From; done; quiet; at; Frame; emit; stall; close)
open import Tree using (Obs; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import operation.PureObservable using (Tape; play; ending; over; module Machine)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
  Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug; Att; attached; attAt; Owe; free; cpAt; cutAt; overAt; CS; Conf; ⟨_,_,_,_⟩; absorbed; rising)

-- The values a frame plays before it next yields.
run : ∀ {A t} → Frame A t → ℕ
run (emit a k) = suc (run k)
run (stall k)  = 0
run (close k)  = 0

-- A started cold: its stop, and its frame's run.
tapeW : ∀ {A} → Tape A → ℕ
tapeW (play τ u i t fr) = suc (run fr)
tapeW (ending e)        = 1
tapeW over              = 0

-- A cold's first frame, wherever it is played.
firstW : ∀ {A t} → From A t → ℕ
firstW done          = 0
firstW quiet         = 0
firstW (at t′ le fr) = run fr

coldW : ∀ {A} → Timeline A → ℕ
coldW (fixed m) = firstW m
coldW fresh     = 1

-- A program not yet subscribed: each operator what its subscription
-- leaves owed, and one more.  A defer is a skip, so owes only itself.
size : ∀ {Γ A} → Obs Timeline Γ A → ℕ
size (cold x)          = 2 + coldW x
size empty             = 2
size (of xs)           = 2 + length xs
size (map f s)         = suc (size s)
size (scan f z s)      = suc (size s)
size (takeWhile i q s) = 5 + size s
size (flatMap op f s)  = 3 + size s
size (connect s b)     = 4 + size s + size b
size (connected x)     = 2
size (defer l)         = 1

one : Bool → ℕ
one true  = 1
one false = 0

attW : Att → ℕ
attW attached  = 0
attW (attAt p) = 1

-- A takeWhile's completion, then its cut, still owed.
oweW : Owe → ℕ
oweW free       = 3
oweW (cpAt p)   = 2
oweW (cutAt p)  = 1
oweW (overAt p) = 0

just? : ∀ {A : Set} → ℕ → Maybe A → ℕ
just? w (just _) = w
just? w nothing  = 0

-- The body mark, then the source's attach; the teardown, while live.
csW : CS → ℕ
csW k = just? 2 (CS.bodyAt k) + just? 1 (CS.attSrc k) + one (CS.srcLive k)

mutual
  owed : ∀ {Γ A} → St Γ A → ℕ
  owed (pend o)                = size o
  owed (coldS b l)             = tapeW l
  owed (ofS i p xs)            = suc (length xs)
  owed doneS                   = 0
  owed (mapS f s)              = owed s
  owed (scanS f z s)           = owed s
  owed (cutS l a s)            = attW a + owed s
  owed (lnS b s)               = one b + owed s
  owed (takeS i q w s)         = oweW w + owed s
  owed (flatS op f true n q o ls)  = owedL ls + (length q + owed o)
  owed (flatS op f false n q o ls) = suc (owedL ls + (length q + owed o))
  owed (connS k o b)           = csW k + owed o + owed b
  owed (joinS j g x ib)        = length ib

  owedL : ∀ {Γ A} → List (St Γ A) → ℕ
  owedL []       = 0
  owedL (s ∷ ls) = owed s + owedL ls

-- A connect's teardown owed once its body completed.  Counted apart:
-- the completion that owes it spends height, not what the tree owes.
tornC : CS → ℕ
tornC k = just? 1 (CS.owedAt k)

mutual
  torn : ∀ {Γ A} → St Γ A → ℕ
  torn (mapS f s)              = torn s
  torn (scanS f z s)           = torn s
  torn (cutS l a s)            = torn s
  torn (lnS b s)               = torn s
  torn (takeS i q w s)         = torn s
  torn (flatS op f d n q o ls) = tornL ls + torn o
  torn (connS k o b)           = tornC k + torn o + torn b
  torn _                       = 0

  tornL : ∀ {Γ A} → List (St Γ A) → ℕ
  tornL []       = 0
  tornL (s ∷ ls) = torn s + tornL ls

-- How far a context's hole lies below the root.
height : ∀ {R Γ A} → Ctx R Γ A → ℕ
height top                               = 0
height (inMap f c)                       = suc (height c)
height (inScan f z c)                    = suc (height c)
height (inCut l a c)                     = suc (height c)
height (inLn b c)                        = suc (height c)
height (inTake i q w c)                  = suc (height c)
height (inOuter op f d n q ls c)         = suc (height c)
height (inLanes op f d n q o pre post c) = suc (height c)
height (inSrc k b c)                     = suc (height c)
height (inBody k o c)                    = suc (height c)

-- A configuration's counts: what the whole tree owes, an event in flight
-- included; whether everything running is absorbed; how far an event in
-- flight has still to rise; the teardowns owed.
owedᶜ : ∀ {R} → Conf R → ℕ
owedᶜ ⟨ c , s , rising e , p ⟩ = suc (owed (plug c s))
owedᶜ ⟨ c , s , _ , p ⟩        = owed (plug c s)

calmᶜ : ∀ {R} → Conf R → ℕ
calmᶜ ⟨ c , s , absorbed , p ⟩ = 1
calmᶜ ⟨ c , s , _ , p ⟩        = 0

tornᶜ : ∀ {R} → Conf R → ℕ
tornᶜ ⟨ c , s , m , p ⟩ = torn (plug c s)

flightᶜ : ∀ {R} → Conf R → ℕ
flightᶜ ⟨ c , s , rising e , p ⟩ = height c
flightᶜ ⟨ c , s , _ , p ⟩        = 0
