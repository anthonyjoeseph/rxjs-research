-- The IMPLEMENTATION's batchSimultaneous: the machine. FULLY DEFINED —
-- no postulates in this file; the only holes left implementation-side
-- are the Naive-Rx operator semantics.
--
-- It never holds the Emissions record. Everything here is a Mealy
-- machine built from Naive-Rx operators (plus three direct machine
-- definitions where the TypeScript, too, steps outside combinators:
-- the subject, the per-input grouping, and the share ref view); the
-- world reaches it one input at a time through `run` (which lives in
-- Shared-Types, not here). Causality is structural.
--
-- Shape mirrors the TypeScript file for file:
--   srcI … exhaustAllI   ~ primitives.ts
--   batchSimultaneousI   ~ batch-simultaneous.ts (+ batch-sync.ts)
module Implementation.Batch-Simultaneous where

open import Prelude
open import Shared-Types
open import Implementation.Naive-Rx

------------------------------------------------------------------------
-- Instantaneous<A> (typescript/src/types.ts): an observable of
-- protocol emits

Inst : ℕ → Set → Set₁
Inst n A = RxObs n (Emit A)

-- provenances are deterministic here (no freshProvenance counter):
-- 0 is COLD, source slot i is suc i
cold : Prov
cold = 0

srcProv : {n : ℕ} → Fin n → Prov
srcProv i = suc (toℕ i)

------------------------------------------------------------------------
-- registration bookkeeping (typescript/src/primitives.ts: trackRegs,
-- closesFor — association lists instead of Records)

Regs : Set
Regs = List (Prov × ℕ)

lookupRD : ℕ → Regs → Prov → ℕ
lookupRD d []             p = d
lookupRD d ((q , c) ∷ rs) p = if eqℕ q p then c else lookupRD d rs p

bumpUp : Regs → Prov → Regs
bumpUp []             p = (p , 1) ∷ []
bumpUp ((q , c) ∷ rs) p =
  if eqℕ q p then (q , suc c) ∷ rs else (q , c) ∷ bumpUp rs p

bumpDown : Regs → Prov → Regs
bumpDown []             p = []
bumpDown ((q , c) ∷ rs) p =
  if eqℕ q p then (q , c ∸ 1) ∷ rs else (q , c) ∷ bumpDown rs p

trackRegs : {A : Set} → Regs → List (Ev A) → Regs
trackRegs = foldl step′
  where
    step′ : {A : Set} → Regs → Ev A → Regs
    step′ rs (init p)  = bumpUp rs p
    step′ rs (close p) = bumpDown rs p
    step′ rs _         = rs

closesFor : {A : Set} → Regs → List (Ev A)
closesFor = concatMap (λ pc → replicate (snd pc) (close (fst pc)))

------------------------------------------------------------------------
-- two direct machine-transformer combinators. Both exist because the
-- machine model knows which outputs one input caused — knowledge that
-- element-wise piping erases, and exactly what the TypeScript's
-- batchSync gadget works to recover.

-- groupFirstRx f g m: the response to m's FIRST input (its subscription
-- moment) becomes ONE f-item; every output of a later input becomes its
-- own g-item. (TS: batchSync + map — the sync/async split.)
groupFirstRx : {n : ℕ} {O X : Set}
             → (List O → X) → (O → X) → RxObs n O → RxObs n X
groupFirstRx f g m = record
  { State = Bool × State m
  ; start = false , start m
  ; step  = λ s i →
      let r = step m (snd s) i
      in (true , fst r) ,
         (if fst s then map g (snd r) else f (snd r) ∷ [])
  }

-- onFirstRx f m: rewrite only the response to m's first input.
onFirstRx : {n : ℕ} {O : Set}
          → (List O → List O) → RxObs n O → RxObs n O
onFirstRx f m = record
  { State = Bool × State m
  ; start = false , start m
  ; step  = λ s i →
      let r = step m (snd s) i
      in (true , fst r) , (if fst s then snd r else f (snd r))
  }

------------------------------------------------------------------------
-- the shared pipeline tail: scan a step function over an item stream,
-- complete when the state closes, emit the assembled emits
-- (TS: runSerial — r.scan, r.takeWhile(inclusive), r.mergeMap)

-- TS: r.mergeMap((s) => (s.out === null ? r.EMPTY : r.of(s.out)))
-- Written WITHOUT matching on the Maybe so that `State (ofMaybe mo)`
-- reduces to `Bool` for any (even neutral) mo — the counting-factors
-- proof reasons about spawned one-shot inners whose element `out s` is
-- abstract, and a dependent state would block it. Definitionally this
-- is the old `nothing ↦ EMPTY, just x ↦ of [x]`.
ofMaybe : {n : ℕ} {X : Set} → Maybe X → RxObs n X
ofMaybe mo = ofRx (maybe′ [] (λ x → x ∷ []) mo)

runOut : {n : ℕ} {S X : Set}
       → (S → X → S) → S → (S → Bool) → (S → Maybe (Emit Val))
       → RxObs n X → Inst n Val
runOut stp seed alive out items =
  mergeMapRx (λ s → ofMaybe (out s))
    (takeWhileRx alive true
      (scanRx stp seed items))

------------------------------------------------------------------------
-- the sources (TS: InstantSubject). The subject is where TS keeps real
-- mutable state; here it is a STATELESS machine — the world's input is
-- its state. Subscribing registers the root (the frame response); one
-- .next() is one emit; `endSlot i` completes THIS subject with an
-- in-band fin (its own instant, so a concat leg spawned by another
-- source's completion still fins on its own later input). The final
-- teardown sentinel is not the subject's business.
-- A copy spawned mid-run gets a synthesized `spawnAt k` subscription: it
-- registers without replaying (hot), UNLESS its slot has already completed
-- by then (toℕ i < k), in which case it completes the late subscriber
-- immediately — the TS InstantSubject's `ended ? of([fin])`.

srcI : {n : ℕ} → Fin n → Inst n Val
srcI i = record { State = ⊤ ; start = tt ; step = λ _ inp → tt , respond inp }
  where
    respond : In _ → List (Emit Val)
    respond (frame ss) =
      (srcProv i , init (srcProv i) ∷ map value (lookupV ss i)) ∷ []
    -- a mid-run subscription: if this slot has already completed (toℕ i < k)
    -- it completes the late subscriber immediately (TS: `ended ? of([fin])`,
    -- COLD, no registration); otherwise it registers hot and replays nothing
    respond (spawnAt k) =
      if ltℕ (toℕ i) k
      then (cold , fin ∷ []) ∷ []
      else (srcProv i , init (srcProv i) ∷ []) ∷ []
    respond (next j v) =
      if eqℕ (toℕ i) (toℕ j) then (srcProv i , value v ∷ []) ∷ [] else []
    respond (endSlot j) =
      if eqℕ (toℕ i) (toℕ j) then (srcProv i , fin ∷ []) ∷ [] else []
    respond end        = []

------------------------------------------------------------------------
-- cold sources (TS: of, empty)

ofI : {n : ℕ} → List Val → Inst n Val
ofI vs = ofRx ((cold , map value vs ++ (fin ∷ [])) ∷ [])

emptyI : {n : ℕ} → Inst n Val
emptyI = ofI []

------------------------------------------------------------------------
-- map (TS: map — times preserved, values mapped, all other events pass)

mapEvs : (Val → Val) → List (Ev Val) → List (Ev Val)
mapEvs f []             = []
mapEvs f (value v ∷ es) = value (f v) ∷ mapEvs f es
mapEvs f (ev ∷ es)      = ev ∷ mapEvs f es

mapI : {n : ℕ} → (Val → Val) → Inst n Val → Inst n Val
mapI f = mapRx (λ e → fst e , mapEvs f (snd e))

------------------------------------------------------------------------
-- scan (TS: scan — the accumulator threads through the value events in
-- delivery order; a pure fold)

record ScanSt : Set where
  constructor mkScan
  field
    sAcc : Val
    sOut : Emit Val
open ScanSt

scanEvs : (Val → Val → Val) → Val → List (Ev Val) → Val × List (Ev Val)
scanEvs f a []             = a , []
scanEvs f a (value v ∷ es) =
  let r = scanEvs f (f a v) es in fst r , value (f a v) ∷ snd r
scanEvs f a (ev ∷ es)      =
  let r = scanEvs f a es in fst r , ev ∷ snd r

scanI : {n : ℕ} → (Val → Val → Val) → Val → Inst n Val → Inst n Val
scanI f z src =
  mapRx sOut
    (scanRx
      (λ s e → let r = scanEvs f (sAcc s) (snd e)
               in mkScan (fst r) (fst e , snd r))
      (mkScan z (cold , []))
      src)

------------------------------------------------------------------------
-- take (TS: take/takeEvs — counts VALUES, exactly like rxjs, even
-- mid-batch; at the cut it closes every registration it passed
-- downstream and finishes inside the same emit)

record TAcc : Set where
  constructor mkTAcc
  field
    tBudget : ℕ
    tRegs   : Regs
    tDone   : Bool
    tOut    : List (Ev Val)
open TAcc

takeEv : TAcc → Ev Val → TAcc
takeEv a ev =
  if tDone a then a else go ev
  where
    go : Ev Val → TAcc
    go (init p)  = record a { tRegs = bumpUp (tRegs a) p
                            ; tOut = tOut a ++ (init p ∷ []) }
    go (close p) = record a { tRegs = bumpDown (tRegs a) p
                            ; tOut = tOut a ++ (close p ∷ []) }
    go fin       = record a { tDone = true ; tOut = tOut a ++ (fin ∷ []) }
    go (wt k)    = record a { tOut = tOut a ++ (wt k ∷ []) }
    go (value v) =
      if eqℕ (tBudget a) 0 then a
      else if eqℕ (tBudget a) 1
        then mkTAcc 0 [] true
               (tOut a ++ (value v ∷ closesFor (tRegs a) ++ (fin ∷ [])))
        else record a { tBudget = tBudget a ∸ 1
                      ; tOut = tOut a ++ (value v ∷ []) }

record TakeSt : Set where
  constructor mkTake
  field
    kBudget : ℕ
    kRegs   : Regs
    kDone   : Bool
    kOut    : Maybe (Emit Val)
open TakeSt

takeStep : TakeSt → Emit Val → TakeSt
takeStep s e =
  let r = foldl takeEv (mkTAcc (kBudget s) (kRegs s) (kDone s) []) (snd e)
  in mkTake (tBudget r) (tRegs r) (tDone r) (just (fst e , tOut r))

takeI : {n : ℕ} → ℕ → Inst n Val → Inst n Val
takeI zero    src =
  -- completes at subscription — still a fin, so a concat behind it
  -- advances in the frame
  ofRx ((cold , fin ∷ []) ∷ [])
takeI (suc k) src =
  runOut takeStep (mkTake (suc k) [] false nothing)
         (λ s → not (kDone s)) kOut src

------------------------------------------------------------------------
-- the joins — THE primitives, over streams of streams ------------------
--
-- a stream of inner streams reaches a join DEFUNCTIONALIZED, as the two
-- shapes the grammar can build (exactly the InnerTemplate device of the
-- TS model): a static list of compiled inners, or a compiled template
-- spawned per outer value. Motivated by the checkers (see README): it
-- keeps the wires in Set₀ and the compiler structurally recursive.

data Joinable (n : ℕ) : Set₁ where
  ofJ  : List₁ (Machine (In n) (Emit Val)) → Joinable n
  mapJ : (Val → Machine (In n) (Emit Val)) → Machine (In n) (Emit Val) → Joinable n

-- every join runs the mapJ pipeline; ofJ is `of(srcs)` defunctionalized
-- to indices (Val = ℕ pays off) — exactly TS merge = mergeAll(of(srcs))
jTemplate : {n : ℕ} → Joinable n → Val → Machine (In n) (Emit Val)
jTemplate (ofJ ms)    v = lookup₁ ms v emptyI
jTemplate (mapJ t _)  v = t v

jOuter : {n : ℕ} → Joinable n → Inst n Val
jOuter (ofJ ms)    = ofI (upTo (length₁ ms))
jOuter (mapJ _ o)  = o

-- the tagged item stream a join's scan consumes (TS: JoinItem): the
-- outer's emit (its trigger chains' events + how many inners it
-- spawns), each spawned inner's synchronous flush, and inners' later
-- emits
data JoinItem : Set where
  trigger : Prov → List (Ev Val) → ℕ → Bool → JoinItem
  flushJ  : List (Ev Val) → Bool → JoinItem
  emitJ   : Emit Val → JoinItem

triggerOf : Emit Val → JoinItem
triggerOf e =
  trigger (fst e) (initsCloses (snd e)) (length (values (snd e))) (hasFin e)

-- an inner's item stream (TS: innerItems — batchSync + map): its
-- response to its OWN subscription input is one flush item; each later
-- emit is its own item
innerItems : {n : ℕ} → Machine (In n) (Emit Val) → RxObs n JoinItem
innerItems =
  groupFirstRx
    (λ os → flushJ (concatMap (λ e → stripFin (snd e)) os) (anyFin os))
    emitJ
  where
    anyFin : List (Emit Val) → Bool
    anyFin []       = false
    anyFin (e ∷ es) = if hasFin e then true else anyFin es

-- mergeAll's item stream (TS: the r.mergeMap lambda in mergeAll):
-- per outer emit, the trigger item then each spawned inner's items
foldInner : {n : ℕ} → (Val → Machine (In n) (Emit Val)) → List Val
          → RxObs n JoinItem
foldInner tmpl []       = emptyRx
foldInner tmpl (v ∷ vs) = mergeRx (innerItems (tmpl v)) (foldInner tmpl vs)

mergeItems : {n : ℕ} → (Val → Machine (In n) (Emit Val)) → Inst n Val
           → RxObs n JoinItem
mergeItems tmpl om =
  mergeMapRx
    (λ e → mergeRx (ofRx (triggerOf e ∷ []))
                   (foldInner tmpl (values (snd e))))
    om

-- the serial joins' item stream (TS: serialItems). The TS multicasts
-- the outer with r.connect; machine determinism makes that free — the
-- outer machine value is used twice, and the value branch strips
-- everything but values, so registrations are never double-counted.
serialItems : {n : ℕ}
            → ((Val → RxObs n JoinItem) → RxObs n Val → RxObs n JoinItem)
            → (Val → Machine (In n) (Emit Val)) → Inst n Val
            → RxObs n JoinItem
serialItems flat tmpl om =
  mergeRx
    (mapRx triggerOf om)
    (flat (λ v → innerItems (tmpl v))
          (mergeMapRx (λ e → ofRx (values (snd e))) om))

------------------------------------------------------------------------
-- mergeAll (TS: mergeAll/MergeState): every arriving inner is
-- subscribed at its arrival; its synchronous flush is COALESCED into
-- the arrival's emit; its later emits pass through under their own
-- roots; the join finishes when the outer and every inner have finned

record MergeSt : Set where
  constructor mkMerge
  field
    mExpecting : ℕ
    mBuf       : List (Ev Val)
    mProv      : Prov
    mPending   : ℕ
    mOuterDone : Bool
    mClosed    : Bool
    mOut       : Maybe (Emit Val)
open MergeSt

mergeSeed : MergeSt
mergeSeed = mkMerge 0 [] cold 0 false false nothing

mergeStep : MergeSt → JoinItem → MergeSt
mergeStep s (trigger p others spawns outerFin) =
  let pending   = mPending s + spawns
      outerDone = mOuterDone s ∨ outerFin
  in if ltℕ 0 spawns
     then record s { mPending = pending ; mOuterDone = outerDone
                   ; mExpecting = spawns ; mBuf = others ; mProv = p
                   ; mOut = nothing }
     else
       let closes = outerDone ∧ eqℕ pending 0 ∧ not (mClosed s)
       in record s { mPending = pending ; mOuterDone = outerDone
                   ; mClosed = mClosed s ∨ closes
                   ; mOut = just (p , (if closes then others ++ (fin ∷ [])
                                                 else others)) }
mergeStep s (flushJ evs finned) =
  let pending   = if finned then mPending s ∸ 1 else mPending s
      expecting = mExpecting s ∸ 1
      buf       = mBuf s ++ evs
  in if ltℕ 0 expecting
     then record s { mPending = pending ; mExpecting = expecting
                   ; mBuf = buf ; mOut = nothing }
     else
       let closes = mOuterDone s ∧ eqℕ pending 0 ∧ not (mClosed s)
       in record s { mPending = pending ; mExpecting = 0 ; mBuf = []
                   ; mClosed = mClosed s ∨ closes
                   ; mOut = just (mProv s , (if closes then buf ++ (fin ∷ [])
                                                       else buf)) }
mergeStep s (emitJ e) =
  if not (hasFin e)
  then record s { mOut = just e }
  else
    let pending = mPending s ∸ 1
        evs     = stripFin (snd e)
        closes  = mOuterDone s ∧ eqℕ pending 0 ∧ not (mClosed s)
    in record s { mPending = pending ; mClosed = mClosed s ∨ closes
                ; mOut = just (fst e , (if closes then evs ++ (fin ∷ [])
                                                  else evs)) }

------------------------------------------------------------------------
-- the serial joins share one state (TS: SerialState / finalize):
-- an emit being assembled HELD open exactly while more synchronous
-- flushes are guaranteed to follow

record SerialSt : Set where
  constructor mkSerial
  field
    hHolding   : Maybe (Prov × List (Ev Val))
    hQueued    : ℕ
    hOpen      : Bool
    hRegs      : Regs
    hOuterDone : Bool
    hClosed    : Bool
    hWeight    : ℕ                         -- outer emits (chains) coalesced so far
    hLastProv  : Prov                      -- the most recent trigger's root
    hOut       : Maybe (Emit Val)
open SerialSt

serialSeed : SerialSt
serialSeed = mkSerial nothing 0 false [] false false 0 cold nothing

-- the chain-weight of the emit being finalized = the number of distinct outer
-- emits (chains) whose flushes were coalesced into it. Each outer value-emit
-- is ONE chain regardless of how many values it carried (a take of 2 values is
-- one chain, a diamond's two arrivals are two) — so we count TRIGGERS, not
-- flushes. The counting machine drains `owed` by this weight.
stampWeight : ℕ → List (Ev Val) → List (Ev Val)
stampWeight w buf = if leqℕ w 1 then buf else wt w ∷ buf

-- the root of the emit being assembled: the held emit's own root, or — if a
-- previous flush already finalized the held — the most recent trigger's root
-- (a later flush of the same instant inherits its trigger's provenance, not
-- cold, so co-arriving chains still batch by their shared root)
heldProv : SerialSt → Prov
heldProv s = maybe′ (hLastProv s) fst (hHolding s)

heldBuf : SerialSt → List (Ev Val)
heldBuf s = maybe′ [] snd (hHolding s)

-- finalize the held emit; the join fins when the outer is done and
-- nothing is live or queued
finalizeS : SerialSt → Bool → ℕ → Bool → SerialSt
finalizeS s open′ queued outerDone with hHolding s
... | nothing        =
  record s { hOpen = open′ ; hQueued = queued ; hOuterDone = outerDone
           ; hOut = nothing }
... | just (p , buf) =
  let fins = outerDone ∧ not open′ ∧ eqℕ queued 0 ∧ not (hClosed s)
      buf′ = stampWeight (hWeight s) buf
  in record s { hOpen = open′ ; hQueued = queued ; hOuterDone = outerDone
              ; hHolding = nothing ; hClosed = hClosed s ∨ fins ; hWeight = 0
              ; hOut = just (p , (if fins then buf′ ++ (fin ∷ []) else buf′)) }

-- concatAll: one inner live at a time; arrivals during a live inner
-- QUEUE (concatMap, natively); when the live inner FINISHES, the queued
-- inner's flush is grafted into the fin-carrying emit — one instant
concatStep : SerialSt → JoinItem → SerialSt
concatStep s (trigger p others spawns outerFin) =
  let queued    = hQueued s + spawns
      outerDone = hOuterDone s ∨ outerFin
      held      = just (p , others)
  in if hOpen s ∨ eqℕ spawns 0
     then finalizeS (record s { hHolding = held ; hLastProv = p }) (hOpen s) queued outerDone
     else record s { hHolding = held ; hQueued = queued ; hLastProv = p
                   ; hWeight = suc (hWeight s)   -- one more chain queued (all deliver)
                   ; hOuterDone = outerDone ; hOut = nothing }
concatStep s (flushJ evs finned) =
  let queued = hQueued s ∸ 1
      held   = just (heldProv s , heldBuf s ++ evs)
  in if finned ∧ ltℕ 0 queued
     then record s { hHolding = held ; hQueued = queued ; hOut = nothing }
     else finalizeS (record s { hHolding = held })
                    (not finned) queued (hOuterDone s)
concatStep s (emitJ e) =
  if not (hasFin e)
  then record s { hOut = just e }
  else
    let held = just (fst e , stripFin (snd e))
    in if ltℕ 0 (hQueued s)
       then record s { hHolding = held ; hOpen = false ; hOut = nothing }
       else finalizeS (record s { hHolding = held }) false 0 (hOuterDone s)

-- switchAll: a new arrival CUTS the live inner (switchMap, natively) —
-- closes synthesized for the cut inner's registrations ride the
-- switching trigger's emit
switchStep : SerialSt → JoinItem → SerialSt
switchStep s (trigger p others spawns outerFin) =
  let outerDone = hOuterDone s ∨ outerFin
      cuts      = if ltℕ 0 spawns ∧ hOpen s then closesFor (hRegs s) else []
      held      = just (p , others ++ cuts)
  in if eqℕ spawns 0
     then finalizeS (record s { hHolding = held ; hLastProv = p }) (hOpen s) 0 outerDone
     else record s { hHolding = held ; hQueued = spawns ; hOpen = false ; hLastProv = p
                   ; hRegs = [] ; hWeight = 1   -- switch keeps only the latest chain
                   ; hOuterDone = outerDone ; hOut = nothing }
switchStep s (flushJ evs finned) =
  let queued = hQueued s ∸ 1
      regs   = trackRegs [] evs
  in if ltℕ 0 queued
     then -- a later burst sibling follows synchronously and cuts THIS one
       (let cuts = if finned then [] else closesFor regs
            held = just (heldProv s , heldBuf s ++ evs ++ cuts)
        in record s { hHolding = held ; hQueued = queued ; hRegs = []
                    ; hOut = nothing })
     else
       (let held = just (heldProv s , heldBuf s ++ evs)
        in finalizeS (record s { hHolding = held
                               ; hRegs = (if finned then [] else regs) })
                     (not finned) 0 (hOuterDone s))
switchStep s (emitJ e) =
  let regs = trackRegs (hRegs s) (snd e)
  in if not (hasFin e)
     then record s { hRegs = regs ; hOut = just e }
     else
       let held = just (fst e , stripFin (snd e))
       in finalizeS (record s { hHolding = held ; hRegs = [] })
                    false 0 (hOuterDone s)

-- exhaustAll: an arrival is dropped only while the previously accepted
-- inner is STILL OPEN (exhaustMap, natively); dropped arrivals are
-- emptied, never swallowed
exhaustStep : SerialSt → JoinItem → SerialSt
exhaustStep s (trigger p others spawns outerFin) =
  let outerDone = hOuterDone s ∨ outerFin
      held      = just (p , others)
  in if hOpen s ∨ eqℕ spawns 0
     then finalizeS (record s { hHolding = held ; hLastProv = p }) (hOpen s) 0 outerDone
     else record s { hHolding = held ; hQueued = spawns ; hLastProv = p
                   ; hWeight = 1   -- exhaust keeps only the first chain (others dropped)
                   ; hOuterDone = outerDone ; hOut = nothing }
exhaustStep s (flushJ evs finned) =
  let queued = hQueued s ∸ 1
      held   = just (heldProv s , heldBuf s ++ evs)
  in if finned ∧ ltℕ 0 queued
     then record s { hHolding = held ; hQueued = queued ; hOut = nothing }
     else finalizeS (record s { hHolding = held })
                    (not finned) 0 (hOuterDone s)
exhaustStep s (emitJ e) =
  if not (hasFin e)
  then record s { hOut = just e }
  else
    let held = just (fst e , stripFin (snd e))
    in finalizeS (record s { hHolding = held }) false 0 (hOuterDone s)

------------------------------------------------------------------------
-- the joins themselves

-- an inner's item stream completes at its fin — the in-band completion
-- test the serial policies observe (triggers never appear in inner
-- streams, so their case is arbitrary)
lastJ : JoinItem → Bool
lastJ (trigger _ _ _ _)  = false
lastJ (flushJ _ finned)  = finned
lastJ (emitJ e)          = hasFin e

-- a superseded (switch-cut) sibling: its already-delivered VALUES survive,
-- but an OPEN (unfinned) flush's registrations (init/close) are torn down.
-- A finned flush completed on its own — nothing to undo. The flush ITEM is
-- always kept (possibly emptied): the counting machine drains hQueued one
-- flush per spawned sibling, so dropping it entirely would desync the count
-- and strand the surviving sibling's emit in the buffer.
cutJ : JoinItem → List JoinItem
cutJ (flushJ evs finned) =
  if finned then flushJ evs finned ∷ []
            else flushJ (map value (values evs)) false ∷ []
cutJ (emitJ e)          = emitJ e ∷ []
cutJ (trigger p o s b)  = trigger p o s b ∷ []

mergeAllI : {n : ℕ} → Joinable n → Inst n Val
mergeAllI j =
  runOut mergeStep mergeSeed (λ s → not (mClosed s)) mOut
         (mergeItems (jTemplate j) (jOuter j))

concatAllI : {n : ℕ} → Joinable n → Inst n Val
concatAllI j =
  runOut concatStep serialSeed (λ s → not (hClosed s)) hOut
         (serialItems (concatMapRx lastJ) (jTemplate j) (jOuter j))

switchAllI : {n : ℕ} → Joinable n → Inst n Val
switchAllI j =
  runOut switchStep serialSeed (λ s → not (hClosed s)) hOut
         (serialItems (switchMapRx lastJ cutJ) (jTemplate j) (jOuter j))

exhaustAllI : {n : ℕ} → Joinable n → Inst n Val
exhaustAllI j =
  runOut exhaustStep serialSeed (λ s → not (hClosed s)) hOut
         (serialItems (exhaustMapRx lastJ) (jTemplate j) (jOuter j))

------------------------------------------------------------------------
-- share (TS: share — the OTHER inherently stateful TS primitive).
-- Machine determinism replaces the multicast: every ref holds its own
-- copy of the bound source, and copies driven by the same inputs agree,
-- so fan-out is free. What remains of share semantics is the PER-REF
-- VIEW (previously: refView, the ratified connecting-ref model, valid on the
-- Canonical non-resetting domain the theorem is stated over):
--   the CONNECTING ref (the grammar's flag) sees everything from the
--   connection instant; any other ref registers the roots feeding it
--   but replays nothing — its subscription response keeps init/close/
--   fin and drops the values (TS: the registration-only replay merge).
-- A ref inside a spawned inner is hot automatically: its copy's
-- synthesized frame carries no flushes.

lateView : {n : ℕ} → Inst n Val → Inst n Val
lateView = onFirstRx (map (λ e → fst e , dropValues (snd e)))

shareRefI : {n : ℕ} → Bool → Inst n Val → Inst n Val
shareRefI true  sh = sh
shareRefI false sh = lateView sh

letShareI : {n : ℕ} → Inst n Val → (Inst n Val → Inst n Val) → Inst n Val
letShareI src body = body src

------------------------------------------------------------------------
-- the compiler: structural recursion over the SHARED grammar. ShEnv
-- carries the letShare bindings (de Bruijn, matching shareE's index).

ShEnv : ℕ → Set₁
ShEnv n = ℕ → Inst n Val

extendSh : {n : ℕ} → Inst n Val → ShEnv n → ShEnv n
extendSh sh ρ zero    = sh
extendSh sh ρ (suc i) = ρ i

compileE : {n : ℕ} → ShEnv n → Exp n → Inst n Val
compileS : {n : ℕ} → ShEnv n → ExpS n → Joinable n
-- inner lists compiled structurally (a `map` lambda would hide the
-- descent from the termination checker)
compileL : {n : ℕ} → ShEnv n → List (Exp n) → List₁ (Machine (In n) (Emit Val))

compileE ρ (srcE i)         = srcI i
compileE ρ emptyE           = emptyI
compileE ρ (ofE vs)         = ofI vs
compileE ρ (shareE f i)     = shareRefI f (ρ i)
compileE ρ (letShareE s b)  = letShareI (compileE ρ s) (λ sh → compileE (extendSh sh ρ) b)
compileE ρ (mapE f e)       = mapI f (compileE ρ e)
compileE ρ (takeE k e)      = takeI k (compileE ρ e)
compileE ρ (scanE f z e)    = scanI f z (compileE ρ e)
compileE ρ (mergeAllE ss)   = mergeAllI (compileS ρ ss)
compileE ρ (concatAllE ss)  = concatAllI (compileS ρ ss)
compileE ρ (switchAllE ss)  = switchAllI (compileS ρ ss)
compileE ρ (exhaustAllE ss) = exhaustAllI (compileS ρ ss)

compileS ρ (ofS es)   = ofJ (compileL ρ es)
compileS ρ (mapS f e) = mapJ (λ v → compileE ρ (f v)) (compileE ρ e)

compileL ρ []       = []
compileL ρ (e ∷ es) = compileE ρ e ∷ compileL ρ es

compile : {n : ℕ} → Exp n → Inst n Val
compile = compileE (λ _ → emptyI)

------------------------------------------------------------------------
-- the counting machine (typescript/src/batch-simultaneous.ts): decide
-- batch boundaries from init/close registration counts alone —
--   src.pipe(batchSync(), endWith(end), scan(step), mergeMap(flush))

data BItem : Set where
  syncB  : List (Emit Val) → BItem   -- the frame group (TS batchSync "sync")
  asyncB : Emit Val → BItem          -- one async emit, alone (never grouped:
                                     -- recovering the grouping IS the job)
  endB   : BItem                     -- the drain sentinel (TS r.endWith)

-- the frame boundary needs no defer gadget here: the machine model
-- knows the response to the first input, which IS the subscribe call
batchSyncRx : {n : ℕ} → Inst n Val → RxObs n BItem
batchSyncRx = groupFirstRx syncB asyncB

record MemI : Set where
  constructor mkMem
  field
    cTotal : Regs                       -- live registrations per root
    cWin   : Maybe (ℕ × List Val)       -- open window: owed, accumulated
    cFlush : Maybe (List Val)           -- the batch this step flushes
open MemI

nonEmptyM : List Val → Maybe (List Val)
nonEmptyM []       = nothing
nonEmptyM (v ∷ vs) = just (v ∷ vs)

-- the frame: one instant, no window needed — its boundary was the
-- subscribe call
frameStepI : List (Emit Val) → MemI
frameStepI es =
  let evs = concatMap snd es
  in mkMem (trackRegs [] evs) nothing (nonEmptyM (values evs))

-- how many chains of root p end in this emit (a take/switch cut closes the
-- registrations it drops). Those chains will NOT deliver this instant, so
-- the window that is counting p's arrivals must discount them too.
closesOf : Prov → List (Ev Val) → ℕ
closesOf p []             = 0
closesOf p (close q ∷ es) = (if eqℕ q p then 1 else 0) + closesOf p es
closesOf p (_ ∷ es)       = closesOf p es

-- one async emit — owed is computed from the count as of the instant's
-- start, BEFORE this emit's init/close events apply
stepI : MemI → Emit Val → MemI
stepI m (p , evs) =
  let owedStart = maybe′ (lookupRD 1 (cTotal m) p) fst (cWin m)
      -- chains this emit accounts for: those that ARRIVED (weight) or were
      -- CUT (close-p). A cut chain may also have just arrived (take's last
      -- value + its own close), so the two overlap — take the max, not the
      -- sum, so a deliver-then-close chain is not counted twice.
      wv        = weightOf evs
      cl        = closesOf p evs
      w         = if leqℕ wv cl then cl else wv
      acc       = maybe′ [] snd (cWin m) ++ values evs
      total     = trackRegs (cTotal m) evs
  in if leqℕ owedStart w
     then mkMem total nothing (nonEmptyM acc)
     else mkMem total (just (owedStart ∸ w , acc)) nothing

bStep : MemI → BItem → MemI
bStep m (syncB es)  = frameStepI es
bStep m (asyncB e)  = stepI (record m { cFlush = nothing }) e
bStep m endB        =
  -- the stream ending drains a still-open window
  mkMem (cTotal m) nothing (maybe′ nothing (λ w → nonEmptyM (snd w)) (cWin m))

batchSimultaneousI : {n : ℕ} → Inst n Val → RxObs n (List Val)
batchSimultaneousI src =
  mergeMapRx (λ m → ofMaybe (cFlush m))
    (scanRx bStep (mkMem [] nothing nothing)
      (endWithRx endB
        (batchSyncRx src)))

------------------------------------------------------------------------
-- THE IMPLEMENTATION. A machine per program; the subscription log of
-- running it. Note what these two definitions DON'T take: the machine
-- never receives the Emissions.

impl-machine : {n : ℕ} → Exp n → Machine (In n) (List Val)
impl-machine e = batchSimultaneousI (compile e)

impl-batchSimultaneous : {n : ℕ} → Emissions n → Exp n → Subscription (List Val)
impl-batchSimultaneous em e = subscribeRx (impl-machine e) em
