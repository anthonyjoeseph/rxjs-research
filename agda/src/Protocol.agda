-- THE PROTOCOL LAYER: what the TypeScript machinery actually sees.
--
-- The timed denotation (Burst.agda) is the referee: it carries timestamps,
-- and batchSpec groups equal Times. But the implementation lives in a world
-- WITHOUT clocks — all it ever receives is a stream of protocol events in
-- delivery order:
--
--   reg p    a subscription of provenance p came alive
--   val v    a value delivery
--   clo p    a registration of provenance p ended
--
-- A Delivery is what one downstream .next() carries: the provenance of the
-- registration it travels through, plus its events. A Trace is a program's
-- complete observable behavior: the subscription frame's events (one
-- subscribe() = one instant, so the frame needs no windows — its boundary
-- is the subscribe call itself, batchSync's job), then, per driver event,
-- the deliveries the program responds with. The per-event grouping exists
-- for COMPOSITION only; the machine receives the flattened list and must
-- recover the grouping by counting. That is the whole game:
--
--   machine (trace of e) ≡ forgetTimes (batchSpec (timed denotation of e))
--
-- The machine (runMem) is the provenance memory as a pure fold, mirroring
-- the TS scan: totalNum counts live registrations per provenance
-- (maintained from reg/clo events alone), and a delivery arriving with no
-- window open opens the instant of its provenance, owing totalNum p
-- deliveries; the window drains one per delivery and flushes at zero. NO
-- TIME COMPARISON decides a flush — timestamps do not exist in the Ev type.
--
-- The truthfulness invariant (OkTrace, the burst-grammar heir of the old
-- tower's `Instants`): each driver event's response is either empty or a
-- block of deliveries of the firing subject's provenance whose length
-- equals the live-registration count. run-ok says counting is then exact;
-- stamp-batch says the stamped trace batches to the same groups; the
-- combinator lemmas (subjectP/ofP/mapP/mergeP) show every program in the
-- fragment produces truthful traces — merging two arms ADDS their
-- registration counts and CONCATENATES their blocks, which is the diamond
-- argument by construction.
--
-- This module covers the static fragment: subjects, of, map, merge.
-- take (clo events shrinking windows), the joins (reg events spawning
-- mid-instant), share lives (reset on completion/refcount-zero, rxjs
-- semantics ratified 2026-07-07) and delivery ranks extend it.
module Protocol where

open import Prelude
open import Time
open import TimedObs

Prov : Set
Prov = ℕ

predℕ : ℕ → ℕ
predℕ zero    = zero
predℕ (suc n) = n

-- protocol events: no timestamps, anywhere. That is the point.
data Ev (A : Set) : Set where
  reg : Prov → Ev A
  val : A → Ev A
  clo : Prov → Ev A

-- one downstream .next(): the registration it travels through + its events
Delivery : Set → Set
Delivery A = Prov × List (Ev A)

-- a program's observable behavior over a driver run
record Trace (A : Set) : Set where
  constructor tr
  field
    frame  : List (Ev A)                 -- the subscription frame
    reacts : List (List (Delivery A))    -- per driver event, in order
open Trace public

-- the driver: the schedule of subject firings (slot , value), in order
Driver : Set → Set
Driver A = List (ℕ × A)

-- event bookkeeping ----------------------------------------------------------

valsOf : {A : Set} → List (Ev A) → List A
valsOf []           = []
valsOf (reg _ ∷ es) = valsOf es
valsOf (val v ∷ es) = v ∷ valsOf es
valsOf (clo _ ∷ es) = valsOf es

bump : (Prov → ℕ) → Prov → (Prov → ℕ)
bump tn p q = if eqℕ p q then suc (tn q) else tn q

drop1 : (Prov → ℕ) → Prov → (Prov → ℕ)
drop1 tn p q = if eqℕ p q then predℕ (tn q) else tn q

applyEvs : {A : Set} → (Prov → ℕ) → List (Ev A) → (Prov → ℕ)
applyEvs tn []           = tn
applyEvs tn (reg p ∷ es) = applyEvs (bump tn p) es
applyEvs tn (val _ ∷ es) = applyEvs tn es
applyEvs tn (clo p ∷ es) = applyEvs (drop1 tn p) es

-- the machine ------------------------------------------------------------------

-- the provenance memory: live-registration counts + the open window
-- (deliveries still owed to the running instant, values buffered so far)
record Mem (A : Set) : Set where
  constructor mem
  field
    totalNum : Prov → ℕ
    win      : Maybe (ℕ × List A)
open Mem public

consNE : {A : Set} → List A → List (List A) → List (List A)
consNE []       bs = bs
consNE (v ∷ vs) bs = (v ∷ vs) ∷ bs

-- owed hits zero → the instant is over, flush (unless it carried no values:
-- a pure protocol instant — a spawn's registration, a lone close — batches
-- nothing); otherwise keep buffering
push : {A : Set} → (Prov → ℕ) → ℕ → List A → Mem A × List (List A)
push tn zero    acc = mem tn nothing , consNE acc []
push tn (suc k) acc = mem tn (just (suc k , acc)) , []

stepD : {A : Set} → Mem A → Delivery A → Mem A × List (List A)
stepD (mem tn nothing) (p , evs) =
  push (applyEvs tn evs) (predℕ (tn p)) (valsOf evs)
stepD (mem tn (just (k , acc))) (p , evs) =
  push (applyEvs tn evs) (predℕ k) (acc ++ valsOf evs)

runMem : {A : Set} → Mem A → List (Delivery A) → List (List A)
runMem (mem _  nothing)          [] = []
runMem (mem _  (just (_ , acc))) [] = consNE acc []   -- unreachable on truthful traces
runMem m (d ∷ ds) = snd (stepD m d) ++ runMem (fst (stepD m d)) ds

-- THE MACHINE: frame values are one batch (the subscribe call is its own
-- boundary); everything after is decided by counting alone
machine : {A : Set} → Trace A → List (List A)
machine (tr fr rs) =
  consNE (valsOf fr)
         (runMem (mem (applyEvs (λ _ → zero) fr) nothing) (concatMap (λ r → r) rs))

-- the trace combinators (the fragment's protocol semantics) --------------------

mapEv : {A B : Set} → (A → B) → Ev A → Ev B
mapEv f (reg p) = reg p
mapEv f (val v) = val (f v)
mapEv f (clo p) = clo p

mapDel : {A B : Set} → (A → B) → Delivery A → Delivery B
mapDel f (p , es) = p , map (mapEv f) es

zipConcat : {X : Set} → List (List X) → List (List X) → List (List X)
zipConcat []       ys       = ys
zipConcat (x ∷ xs) []       = x ∷ xs
zipConcat (x ∷ xs) (y ∷ ys) = (x ++ y) ∷ zipConcat xs ys

-- a subject subscription: one registration in the frame; responds to its
-- own slot's firings with a single delivery carrying the value
subjectP : {A : Set} → Driver A → Prov → ℕ → Trace A
subjectP d p i =
  tr (reg p ∷ [])
     (map (λ jv → if eqℕ (fst jv) i
                  then ((p , val (snd jv) ∷ []) ∷ [])
                  else [])
          d)

-- a cold of: registers and emits entirely inside the frame
ofP : {A : Set} → Driver A → Prov → List A → Trace A
ofP d p vs = tr (reg p ∷ map val vs) (map (λ _ → []) d)

mapP : {A B : Set} → (A → B) → Trace A → Trace B
mapP f (tr fr rs) = tr (map (mapEv f) fr) (map (map (mapDel f)) rs)

-- merge: frames concatenate (subscription order), responses interleave
-- per driver event, left arm first
mergeP : {A : Set} → Trace A → Trace A → Trace A
mergeP (tr f₁ r₁) (tr f₂ r₂) = tr (f₁ ++ f₂) (zipConcat r₁ r₂)

-- the referee: stamping a trace with the driver's clock ------------------------

t₀ : Time
t₀ = (0 , 0)

tickOf : ℕ → Time
tickOf k = (suc k , 0)

atT : {A : Set} → Time → List A → TimedObs A
atT t vs = map (λ v → t , v) vs

delVals : {A : Set} → List (Delivery A) → List A
delVals ds = concatMap (λ d → valsOf (snd d)) ds

stampFrom : {A : Set} → ℕ → List (List (Delivery A)) → TimedObs A
stampFrom k []       = []
stampFrom k (r ∷ rs) = atT (tickOf k) (delVals r) ++ stampFrom (suc k) rs

-- the timed history a trace claims: frame at t₀, react k at tick k
stamp : {A : Set} → Trace A → TimedObs A
stamp (tr fr rs) = atT t₀ (valsOf fr) ++ stampFrom zero rs

-- the truthfulness invariant --------------------------------------------------
--
-- OkTrace is `Instants` reborn over the burst grammar: every react is
-- either empty or a block of deliveries of ONE provenance — each carrying
-- at least one value and nothing else, in this fragment — whose length is
-- exactly the live-registration count. "totalNum = live subscriptions",
-- as a datatype.

data ValBurst {A : Set} : List (Ev A) → Set where
  vb1 : {v : A} → ValBurst (val v ∷ [])
  vb∷ : {v : A} {es : List (Ev A)} → ValBurst es → ValBurst (val v ∷ es)

data Block {A : Set} (p : Prov) : List (Delivery A) → Set where
  bk[] : Block p []
  bk∷  : {es : List (Ev A)} {ds : List (Delivery A)}
       → ValBurst es → Block p ds → Block p ((p , es) ∷ ds)

data OkReact {A : Set} (tn : Prov → ℕ) : List (Delivery A) → Set where
  okε : OkReact tn []
  okB : {p : Prov} {ds : List (Delivery A)}
      → Block p ds → length ds ≡ tn p → OkReact tn ds

data OkTrace {A : Set} (tn : Prov → ℕ) : List (List (Delivery A)) → Set where
  ot[] : OkTrace tn []
  ot∷  : {r : List (Delivery A)} {rs : List (List (Delivery A))}
       → OkReact tn r → OkTrace tn rs → OkTrace tn (r ∷ rs)

-- value-only deliveries leave the registration counts untouched
applyEvs-vals : {A : Set} {es : List (Ev A)} (tn : Prov → ℕ)
  → ValBurst es → applyEvs tn es ≡ tn
applyEvs-vals tn vb1      = refl
applyEvs-vals tn (vb∷ vb) = applyEvs-vals tn vb

-- what the machine OUGHT to produce: one batch per nonempty react
neOf : {A : Set} → List (List (Delivery A)) → List (List A)
neOf []       = []
neOf (r ∷ rs) = consNE (delVals r) (neOf rs)

-- THE COUNTING THEOREM, delivery side ------------------------------------------

-- an open window (with at least one value already buffered) drains one
-- slot per delivery and flushes exactly at the block boundary
drain : {A : Set} (tn : Prov → ℕ) (p : Prov) (j : ℕ) (w : A) (acc : List A)
        (ds rest : List (Delivery A))
      → Block p ds → length ds ≡ suc j
      → runMem (mem tn (just (suc j , w ∷ acc))) (ds ++ rest)
        ≡ ((w ∷ acc) ++ delVals ds) ∷ runMem (mem tn nothing) rest
drain tn p j w acc [] rest bk[] ()
drain tn p zero w acc ((.p , es) ∷ []) rest (bk∷ vb bk[]) len
  rewrite applyEvs-vals {es = es} tn vb | ++-nil (valsOf es) = refl
drain tn p zero w acc ((.p , es) ∷ d′ ∷ ds″) rest (bk∷ vb (bk∷ _ _)) len =
  zero≢suc (suc-inj (sym len))
drain tn p (suc j′) w acc ((.p , es) ∷ []) rest (bk∷ vb bk[]) len =
  zero≢suc (suc-inj len)
drain tn p (suc j′) w acc ((.p , es) ∷ ds′@(_ ∷ _)) rest (bk∷ vb bk′) len
  rewrite applyEvs-vals {es = es} tn vb
        | drain tn p j′ w (acc ++ valsOf es) ds′ rest bk′ (suc-inj len)
        | ++-assoc acc (valsOf es) (delVals ds′)
  = refl

-- a nonempty truthful block is consumed as exactly one batch
run-block-ne : {A : Set} (tn : Prov → ℕ) (p : Prov) (es : List (Ev A))
               (ds′ rest : List (Delivery A))
  → ValBurst es → Block p ds′ → suc (length ds′) ≡ tn p
  → runMem (mem tn nothing) (((p , es) ∷ ds′) ++ rest)
    ≡ (valsOf es ++ delVals ds′) ∷ runMem (mem tn nothing) rest
run-block-ne tn p (val v ∷ []) [] rest vb1 bk[] len
  rewrite sym len = refl
run-block-ne tn p (val v ∷ es′) [] rest (vb∷ vb′) bk[] len
  rewrite sym len | applyEvs-vals {es = es′} tn vb′
        | ++-nil (valsOf es′) = refl
run-block-ne tn p (val v ∷ []) (d″ ∷ ds″) rest vb1 bk′ len
  rewrite sym len
  = drain tn p (length ds″) v [] (d″ ∷ ds″) rest bk′ refl
run-block-ne tn p (val v ∷ es′) (d″ ∷ ds″) rest (vb∷ vb′) bk′ len
  rewrite sym len | applyEvs-vals {es = es′} tn vb′
  = drain tn p (length ds″) v (valsOf es′) (d″ ∷ ds″) rest bk′ refl

-- a value-burst delivery makes the flushed batch visibly nonempty
consNE-vals : {A : Set} {es : List (Ev A)} → ValBurst es
  → (rest : List A) (l : List (List A))
  → consNE (valsOf es ++ rest) l ≡ (valsOf es ++ rest) ∷ l
consNE-vals vb1     rest l = refl
consNE-vals (vb∷ _) rest l = refl

-- a truthful block is consumed as exactly one batch (or nothing, if empty)
run-block : {A : Set} (tn : Prov → ℕ) (p : Prov) (ds rest : List (Delivery A))
  → Block p ds → length ds ≡ tn p
  → runMem (mem tn nothing) (ds ++ rest)
    ≡ consNE (delVals ds) (runMem (mem tn nothing) rest)
run-block tn p [] rest bk[] len = refl
run-block tn p ((.p , es) ∷ ds′) rest (bk∷ vb bk′) len =
  trans (run-block-ne tn p es ds′ rest vb bk′ len)
        (sym (consNE-vals vb (delVals ds′) (runMem (mem tn nothing) rest)))

-- counting alone recovers the per-event grouping the flattening erased
run-ok : {A : Set} (tn : Prov → ℕ) (rs : List (List (Delivery A)))
  → OkTrace tn rs
  → runMem (mem tn nothing) (concatMap (λ r → r) rs) ≡ neOf rs
run-ok tn [] ot[] = refl
run-ok tn ([] ∷ rs) (ot∷ _ ot) = run-ok tn rs ot
run-ok tn (r ∷ rs) (ot∷ (okB {p} bk len) ot) =
  trans (run-block tn p r (concatMap (λ x → x) rs) bk len)
        (cong (consNE (delVals r)) (run-ok tn rs ot))

-- THE COUNTING THEOREM, referee side ---------------------------------------------

open import Diamond using (HeadNe; hn[]; hn∷; batchSpec-headNe; insert-ne)

consNET : {A : Set} → Time → List A → TimedObs (List A) → TimedObs (List A)
consNET t []       bs = bs
consNET t (v ∷ vs) bs = (t , v ∷ vs) ∷ bs

-- a constant-time block batches as one group in front of the rest
block-batch : {A : Set} (t : Time) (vs : List A) (rest : TimedObs A)
  → HeadNe t rest
  → batchSpec (atT t vs ++ rest) ≡ consNET t vs (batchSpec rest)
block-batch t [] rest ne = refl
block-batch t (v ∷ []) rest ne = insert-ne t v (batchSpec rest) (batchSpec-headNe t rest ne)
block-batch t (v ∷ w ∷ vs) rest ne
  rewrite block-batch t (w ∷ vs) rest ne | timeEq-refl t = refl

-- every stamped react lands strictly after any earlier tick
stampFrom-ne : {A : Set} (m k : ℕ) (rs : List (List (Delivery A)))
  → ltℕ m (suc k) ≡ true
  → HeadNe (m , 0) (stampFrom k rs)
stampFrom-ne m k [] lt = hn[]
stampFrom-ne m k (r ∷ rs) lt with delVals r
... | []     = stampFrom-ne m (suc k) rs (ltℕ-trans m (suc k) (suc (suc k)) lt (ltℕ-suc (suc k)))
... | v ∷ vs = hn∷ (cong (λ b → b ∧ eqℕ 0 0) (ltℕ⇒eqℕ-false m (suc k) lt))

-- the referee's answer, react by react
batchReacts : {A : Set} → ℕ → List (List (Delivery A)) → TimedObs (List A)
batchReacts k []       = []
batchReacts k (r ∷ rs) = consNET (tickOf k) (delVals r) (batchReacts (suc k) rs)

stampFrom-batch : {A : Set} (k : ℕ) (rs : List (List (Delivery A)))
  → batchSpec (stampFrom k rs) ≡ batchReacts k rs
stampFrom-batch k [] = refl
stampFrom-batch k (r ∷ rs) =
  trans (block-batch (tickOf k) (delVals r) (stampFrom (suc k) rs)
          (stampFrom-ne (suc k) (suc k) rs (ltℕ-suc (suc k))))
        (cong (consNET (tickOf k) (delVals r)) (stampFrom-batch (suc k) rs))

stamp-batch : {A : Set} (fr : List (Ev A)) (rs : List (List (Delivery A)))
  → batchSpec (stamp (tr fr rs))
    ≡ consNET t₀ (valsOf fr) (batchReacts zero rs)
stamp-batch fr rs =
  trans (block-batch t₀ (valsOf fr) (stampFrom zero rs)
          (stampFrom-ne zero zero rs refl))
        (cong (consNET t₀ (valsOf fr)) (stampFrom-batch zero rs))

-- assembling the endgame ---------------------------------------------------------

forgetT : {A : Set} → TimedObs A → List A
forgetT = map snd

forgetT-consNET : {A : Set} (t : Time) (vs : List A) (bs : TimedObs (List A))
  → forgetT (consNET t vs bs) ≡ consNE vs (forgetT bs)
forgetT-consNET t []       bs = refl
forgetT-consNET t (v ∷ vs) bs = refl

forgetT-batchReacts : {A : Set} (k : ℕ) (rs : List (List (Delivery A)))
  → forgetT (batchReacts k rs) ≡ neOf rs
forgetT-batchReacts k [] = refl
forgetT-batchReacts k (r ∷ rs) =
  trans (forgetT-consNET (tickOf k) (delVals r) (batchReacts (suc k) rs))
        (cong (consNE (delVals r)) (forgetT-batchReacts (suc k) rs))

-- THE ENDGAME, fragment form: a machine that never sees a clock produces
-- exactly the batches the timestamped referee defines — for any trace
-- whose deliveries are truthfully counted
endgame : {A : Set} (fr : List (Ev A)) (rs : List (List (Delivery A)))
  → OkTrace (applyEvs (λ _ → zero) fr) rs
  → machine (tr fr rs) ≡ forgetT (batchSpec (stamp (tr fr rs)))
endgame fr rs ot
  rewrite stamp-batch fr rs
        | forgetT-consNET t₀ (valsOf fr) (batchReacts zero rs)
        | forgetT-batchReacts zero rs
        | run-ok (applyEvs (λ _ → zero) fr) rs ot
  = refl

-- payoff corollaries --------------------------------------------------------------

valsOf-++ : {A : Set} (es fs : List (Ev A))
  → valsOf (es ++ fs) ≡ valsOf es ++ valsOf fs
valsOf-++ []           fs = refl
valsOf-++ (reg p ∷ es) fs = valsOf-++ es fs
valsOf-++ (val v ∷ es) fs = cong (_∷_ v) (valsOf-++ es fs)
valsOf-++ (clo p ∷ es) fs = valsOf-++ es fs

valsOf-vals : {A : Set} (vs : List A) → valsOf (map val vs) ≡ vs
valsOf-vals []       = refl
valsOf-vals (v ∷ vs) = cong (_∷_ v) (valsOf-vals vs)

emptyReacts : {A : Set} (d : Driver A)
  → concatMap (λ r → r)
      (zipConcat (map (λ _ → []) d) (map (λ _ → ([] {A = Delivery A})) d))
    ≡ []
emptyReacts []      = refl
emptyReacts (e ∷ d) = emptyReacts d

-- ONE SUBSCRIBE = ONE BATCH, protocol side: merged cold sources produce
-- the frame batch and nothing else, whatever the driver later does
frame-batch : {A : Set} (d : Driver A) (p q : Prov) (vs ws : List A)
  → machine (mergeP (ofP d p vs) (ofP d q ws)) ≡ consNE (vs ++ ws) []
frame-batch d p q vs ws
  rewrite valsOf-++ (map val vs) (reg q ∷ map val ws)
        | valsOf-vals vs
        | valsOf-vals ws
        | emptyReacts {_} d
  = refl

-- THE PROTOCOL DIAMOND: what the diamond batches to, per driver event
diaB : {A : Set} → (A → A) → ℕ → Driver A → List (List A)
diaB f i []            = []
diaB f i ((j , v) ∷ d) =
  if eqℕ j i then ((v ∷ f v ∷ []) ∷ diaB f i d) else diaB f i d

diamond-run : {A : Set} (f : A → A) (i : ℕ) (p : Prov) (tn : Prov → ℕ)
              (d : Driver A)
  → tn p ≡ 2
  → runMem (mem tn nothing)
      (concatMap (λ r → r)
        (zipConcat
          (map (λ jv → if eqℕ (fst jv) i
                       then ((p , val (snd jv) ∷ []) ∷ []) else []) d)
          (map (map (mapDel f))
            (map (λ jv → if eqℕ (fst jv) i
                         then ((p , val (snd jv) ∷ []) ∷ []) else []) d))))
    ≡ diaB f i d
diamond-run f i p tn [] tnp = refl
diamond-run f i p tn ((j , v) ∷ d) tnp with eqℕ j i
... | false = diamond-run f i p tn d tnp
... | true rewrite tnp =
  cong (_∷_ (v ∷ f v ∷ [])) (diamond-run f i p tn d tnp)

tn2 : (p : Prov) → bump (bump (λ _ → zero) p) p p ≡ 2
tn2 p rewrite eqℕ-refl p = refl

-- THE DIAMOND, decided by counting alone: two live subscriptions of one
-- subject mean totalNum p ≡ 2, so every firing's two deliveries drain one
-- window and flush as one batch [v , f v] — no clock anywhere
protocol-diamond : {A : Set} (d : Driver A) (p : Prov) (i : ℕ) (f : A → A)
  → machine (mergeP (subjectP d p i) (mapP f (subjectP d p i)))
    ≡ diaB f i d
protocol-diamond d p i f =
  diamond-run f i p (bump (bump (λ _ → zero) p) p) d (tn2 p)

-- SHARE LIVES (rxjs semantics, ratified 2026-07-07) ------------------------------
--
-- A share connects its source when a subscriber arrives and it has none;
-- it RESETS when the source completes or its refcount drains to zero; a
-- subscriber arriving after a reset reconnects — a fresh life — and a cold
-- source replays into it. Confirmed against rxjs 7: merge(shared, shared)
-- of a shared of(5) logs 5 TWICE (the first life completes-and-resets
-- synchronously, inside the frame). Lives are NON-LOCAL — which life a
-- subscriber joins depends on when its siblings closed — which is exactly
-- why they live here, in the operational layer, and not in the flat
-- denotation (Burst.agda), whose share theorems hold for programs whose
-- shares never reset.
--
-- Counting design ratified with this model: registrations are counted per
-- ROOT-CAUSE provenance. A share is counting-transparent — each subscriber
-- registers the ROOT subject feeding the share (reg j), fan-out deliveries
-- travel with the root's provenance, and pure-cold flushes ride their
-- trigger's window. The machine above needs no share-specific state.
--
-- DELIVERY RANKS fall out of the same model: `live` is kept in
-- REGISTRATION order (joins append), and fan-out walks it in order — so a
-- subscriber spawned later delivers later, regardless of where its arm
-- sits syntactically. That is the rank-tagged delivery model, derived from
-- the mechanism instead of decreed.

-- a live subscriber of a share: its arm, and its remaining take budget
LiveRef : Set → Set
LiveRef A = (A → A) × Maybe ℕ

-- a subscriber spec: when it subscribes (nothing = in the frame; just t =
-- spawned when slot t fires), its arm, its take budget
Spec : Set → Set
Spec A = Maybe ℕ × ((A → A) × Maybe ℕ)

-- the share's source: a cold prefix, then (optionally) a root subject
record ShareSrc (A : Set) : Set where
  constructor sharesrc
  field
    coldVals : List A
    tail     : Maybe ℕ
open ShareSrc public

-- deliver one value to a live ref: the events it forwards, and whether it
-- survives (a take budget of 1 emits the value and its own close together)
recv1 : {A : Set} → Prov → A → LiveRef A → List (Ev A) × Maybe (LiveRef A)
recv1 j v (f , nothing)             = val (f v) ∷ []         , just (f , nothing)
recv1 j v (f , just zero)           = clo j ∷ []             , nothing
recv1 j v (f , just (suc zero))     = val (f v) ∷ clo j ∷ [] , nothing
recv1 j v (f , just (suc (suc n)))  = val (f v) ∷ []         , just (f , just (suc n))

-- replay a cold prefix into one ref
recvCold : {A : Set} → Prov → List A → LiveRef A → List (Ev A) × Maybe (LiveRef A)
recvCold j []       r = [] , just r
recvCold j (v ∷ vs) r with recv1 j v r
... | evs , nothing = evs , nothing
... | evs , just r′ with recvCold j vs r′
...   | evs′ , mr = evs ++ evs′ , mr

maybeCons : {X : Set} → Maybe X → List X → List X
maybeCons nothing  xs = xs
maybeCons (just x) xs = x ∷ xs

-- the source fires: every live ref receives, in REGISTRATION order
fanout : {A : Set} → Prov → A → List (LiveRef A)
       → List (Delivery A) × List (LiveRef A)
fanout j v []       = [] , []
fanout j v (r ∷ rs) =
  ((j , fst (recv1 j v r)) ∷ fst (fanout j v rs)) ,
  maybeCons (snd (recv1 j v r)) (snd (fanout j v rs))

-- a subscriber joins the share
--   pure-cold source: connect, replay, source completes, reset — all at once;
--     no root registration (there is no async root to register)
--   live source, no subscribers: CONNECT a fresh life — register the root,
--     receive the cold replay
--   live source, subscribers present: hot join — register, replay nothing
join : {A : Set} → ShareSrc A → List (LiveRef A) → LiveRef A
     → List (Ev A) × List (LiveRef A)
join (sharesrc cold nothing)  live r = map val (valsOf (fst (recvCold 0 cold r))) , live
join (sharesrc cold (just j)) []   r =
  (reg j ∷ fst (recvCold j cold r)) , maybeCons (snd (recvCold j cold r)) []
join (sharesrc cold (just j)) live@(_ ∷ _) r =
  (reg j ∷ []) , live ++ (r ∷ [])

-- the frame: process frame subscribers (and spawned specs' trigger
-- registrations) in pre-order — this IS registration order for statics
frameGo : {A : Set} → ShareSrc A → List (Spec A) → List (LiveRef A)
        → List (Ev A) × List (LiveRef A)
frameGo src []                     live = [] , live
frameGo src ((just t  , r) ∷ ss)   live =
  (reg t ∷ fst (frameGo src ss live)) , snd (frameGo src ss live)
frameGo src ((nothing , r) ∷ ss)   live =
  (fst (join src live r) ++ fst (frameGo src ss (snd (join src live r)))) ,
  snd (frameGo src ss (snd (join src live r)))

-- spawned subscribers joining at event i, in spec order; each join rides
-- its trigger's delivery
joinsAt : {A : Set} → ShareSrc A → ℕ → List (LiveRef A) → List (Spec A)
        → List (Delivery A) × List (LiveRef A)
joinsAt src i live [] = [] , live
joinsAt src i live ((nothing , r) ∷ ss) = joinsAt src i live ss
joinsAt src i live ((just t , r) ∷ ss) with eqℕ t i
... | false = joinsAt src i live ss
... | true  =
  ((i , fst (join src live r)) ∷ fst (joinsAt src i (snd (join src live r)) ss)) ,
  snd (joinsAt src i (snd (join src live r)) ss)

-- fold the driver: fan out first (a spawned ref never sees the event that
-- spawned it — the strictly-after rule), then process joins
reactsGo : {A : Set} → ShareSrc A → List (Spec A) → List (LiveRef A)
         → Driver A → List (List (Delivery A))
reactsGo src specs live [] = []
reactsGo (sharesrc cold nothing) specs live ((i , v) ∷ d) =
  fst (joinsAt (sharesrc cold nothing) i live specs) ∷
  reactsGo (sharesrc cold nothing) specs
           (snd (joinsAt (sharesrc cold nothing) i live specs)) d
reactsGo (sharesrc cold (just j)) specs live ((i , v) ∷ d) with eqℕ j i
... | false =
  fst (joinsAt (sharesrc cold (just j)) i live specs) ∷
  reactsGo (sharesrc cold (just j)) specs
           (snd (joinsAt (sharesrc cold (just j)) i live specs)) d
... | true  =
  (fst (fanout j v live) ++
   fst (joinsAt (sharesrc cold (just j)) i (snd (fanout j v live)) specs)) ∷
  reactsGo (sharesrc cold (just j)) specs
           (snd (joinsAt (sharesrc cold (just j)) i (snd (fanout j v live)) specs)) d

-- the derived trace of a share and its subscribers
shareLives : {A : Set} → ShareSrc A → List (Spec A) → Driver A → Trace A
shareLives src specs d =
  tr (fst (frameGo src specs []))
     (reactsGo src specs (snd (frameGo src specs [])) d)

-- THEOREM (cold share replays — the rxjs-confirmed [5,5]): two frame
-- subscribers of a shared, synchronously completing of(5): the first
-- connects, drains, and RESETS the share inside the frame; the second
-- reconnects and replays. One frame, one batch, the value twice.
cold-share-lives : machine (shareLives (sharesrc (5 ∷ []) nothing)
                     ((nothing , (λ v → v) , nothing) ∷
                      (nothing , (λ v → v) , nothing) ∷ []) [])
                   ≡ (5 ∷ 5 ∷ []) ∷ []
cold-share-lives = refl

-- THEOREM (ranked delivery — the non-canonical tree, decided): the spawn
-- arm is written FIRST (spec order = syntactic order), but the static arm
-- registered first — so the batch is [g v , f v], registration order, not
-- syntactic order. Driver: slot 1 spawns the f-ref, then slot 0 (the
-- share's root) fires v.
ranked-delivery : {A : Set} (f g : A → A) (w v : A)
  → machine (shareLives (sharesrc [] (just 0))
      ((just 1  , f , nothing) ∷      -- spawn arm, syntactically left
       (nothing , g , nothing) ∷ [])  -- static arm, syntactically right
      ((1 , w) ∷ (0 , v) ∷ []))
    ≡ (g v ∷ f v ∷ []) ∷ []
ranked-delivery f g w v = refl

-- THEOREM (refcount-zero reset + replay): a take(1) frame subscriber of a
-- shared (cold 5 + subject 0) drains the cold prefix and closes — refcount
-- zero, the share resets. Slot 0 fires 7 into a DEAD share: nothing. A ref
-- spawned by slot 1 reconnects: a fresh life replays the 5 at its
-- trigger's instant. Slot 0 fires 8 into the new life: [8].
reset-replay : machine (shareLives (sharesrc (5 ∷ []) (just 0))
                 ((nothing , (λ v → v) , just 1) ∷
                  (just 1  , (λ v → v) , nothing) ∷ [])
                 ((0 , 7) ∷ (1 , 9) ∷ (0 , 8) ∷ []))
               ≡ (5 ∷ []) ∷ (5 ∷ []) ∷ (8 ∷ []) ∷ []
reset-replay = refl
