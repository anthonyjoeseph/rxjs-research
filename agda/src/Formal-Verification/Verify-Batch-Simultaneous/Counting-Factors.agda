-- The mechanical half of counting-recovers: the counting pipeline reads
-- only the TRACE. `run (batchSimultaneousI m) is` — the composite Mealy
-- machine batchSync ∘ endWith ∘ scan ∘ mergeMap — equals `countBatches`
-- (a pure fold) of m's grouped output. No grammar, no clocks: pure
-- machine-composition commutation.
--
-- The proof factors into three reusable machine lemmas:
--   mergeMap-oneshot — mergeMap of a family of ONE-SHOT inners (emit on
--     spawn, silent forever after: exactly `ofMaybe`) is just
--     concatMap-of-the-spawn-flush.
--   scan-collect    — scan's running states, flushed and concatenated,
--     ARE collectB of the item stream.
--   batchSync-bItems — batchSync + endWith serialize m's grouped trace
--     into exactly the `bItems` stream countBatches folds over.
module Formal-Verification.Verify-Batch-Simultaneous.Counting-Factors where

open import Prelude
open import Shared-Types
open import Implementation.Naive-Rx
open import Implementation.Batch-Simultaneous
open import Formal-Verification.Verify-Batch-Simultaneous.Bridge

------------------------------------------------------------------------
-- one-shot inners: the mergeMap of `λ s → ofMaybe {n} (out s)`

-- the flush a one-shot inner emits at its spawn
flushGen : {S Y : Set} → (S → Maybe Y) → S → List Y
flushGen out s = maybe′ [] (λ y → y ∷ []) (out s)

concatMap-++ : {A B : Set} (g : A → List B) (xs ys : List A)
  → concatMap g (xs ++ ys) ≡ concatMap g xs ++ concatMap g ys
concatMap-++ g []       ys = refl
concatMap-++ g (x ∷ xs) ys =
  trans (cong (g x ++_) (concatMap-++ g xs ys))
        (sym (++-assoc (g x) (concatMap g xs) (concatMap g ys)))

-- With the non-matching `ofMaybe`, `State (ofMaybe {n} mo) = Bool` and a
-- spawned one-shot inner's state is literally `true` (fired once, silent
-- after). "Spent" is therefore just: the running inner is `(s ▹ true)`.

-- an `ofMaybe {n} mo` inner's spawn emits exactly flushGen, and lands spent
spawn-flush-m : {n : ℕ} {Y : Set} (mo : Maybe Y) (i : In n)
  → snd (step (ofMaybe {n} mo) (start (ofMaybe {n} mo)) i) ≡ maybe′ [] (λ y → y ∷ []) mo
spawn-flush-m mo i = refl

-- all running inners spent (state = true). Independent of the world
-- size and the family: `MMRun (λ s → ofMaybe {n} (out s))` is just
-- `Σ S (λ _ → Bool)` (the one-shot inner's state is Bool), so this
-- predicate has no `n`/`out` to guess.
data AllSpent {S : Set} : List (Σ S (λ _ → Bool)) → Set where
  spNil  : AllSpent []
  spCons : {s : S} {rs : List (Σ S (λ _ → Bool))}
         → AllSpent rs → AllSpent ((s ▹ true) ∷ rs)

AllSpent-++ : {S : Set} {as bs : List (Σ S (λ _ → Bool))}
  → AllSpent as → AllSpent bs → AllSpent (as ++ bs)
AllSpent-++ spNil       bs = bs
AllSpent-++ (spCons as) bs = spCons (AllSpent-++ as bs)

-- stepping a list of spent inners: nothing happens
mmStepAll-spent : {n : ℕ} {Y S : Set} (out : S → Maybe Y) (i : In n)
  {rs : List (MMRun (λ s → ofMaybe {n} (out s)))}
  → AllSpent rs → mmStepAll (λ s → ofMaybe {n} (out s)) i rs ≡ (rs , [])
mmStepAll-spent out i spNil            = refl
mmStepAll-spent out i (spCons {s} {rs} tp)
  rewrite mmStepAll-spent out i tp = refl

-- spawning a burst emits each inner's flush, and the spawned inners are
-- all spent (state = true, by definition of the spawn step)
mmSpawnAll-flush : {n : ℕ} {Y S : Set} (out : S → Maybe Y) (i : In n)
  (xs : List S)
  → snd (mmSpawnAll (λ s → ofMaybe {n} (out s)) i xs) ≡ concatMap (flushGen out) xs
mmSpawnAll-flush out i []       = refl
mmSpawnAll-flush out i (s ∷ xs)
  rewrite spawn-flush-m (out s) i | mmSpawnAll-flush out i xs = refl

mmSpawnAll-spent : {n : ℕ} {Y S : Set} (out : S → Maybe Y) (i : In n)
  (xs : List S)
  → AllSpent (fst (mmSpawnAll (λ s → ofMaybe {n} (out s)) i xs))
mmSpawnAll-spent out i []       = spNil
mmSpawnAll-spent out i (s ∷ xs) = spCons (mmSpawnAll-spent out i xs)

-- THE one-shot lemma, generalized over the machine's live state and its
-- (spent) running inners
mergeMap-oneshot-feed : {n : ℕ} {Y S : Set} (out : S → Maybe Y)
  (M : RxObs n S) (is : List (In n)) (sM : State M)
  {rs : List (MMRun (λ s → ofMaybe {n} (out s)))} → AllSpent rs
  → snd (feed (mergeMapRx (λ s → ofMaybe {n} (out s)) M) (sM , rs) is)
    ≡ concatMap (flushGen out) (snd (feed M sM is))
mergeMap-oneshot-feed out M []       sM asp = refl
mergeMap-oneshot-feed {n} out M (i ∷ is) sM {rs} asp
  rewrite mmStepAll-spent out i asp
        | ++-[] (snd (mmSpawnAll (λ s → ofMaybe {n} (out s)) (spawnInput i)
                        (snd (step M sM i))))
        | mmSpawnAll-flush out (spawnInput i) (snd (step M sM i))
        | mergeMap-oneshot-feed out M is (fst (step M sM i))
            (AllSpent-++ asp
              (mmSpawnAll-spent out (spawnInput i) (snd (step M sM i))))
        | concatMap-++ (flushGen out) (snd (step M sM i))
            (snd (feed M (fst (step M sM i)) is))
  = refl

mergeMap-oneshot : {n : ℕ} {Y S : Set} (out : S → Maybe Y)
  (M : RxObs n S) (is : List (In n))
  → run (mergeMapRx (λ s → ofMaybe {n} (out s)) M) is
    ≡ concatMap (flushGen out) (run M is)
mergeMap-oneshot out M is = mergeMap-oneshot-feed out M is (start M) spNil

------------------------------------------------------------------------
-- the counting reification (owned here; Counting-Recovers imports it):
-- the batching machine read as a pure fold over the grouped trace.
-- `batchSimultaneousI` is  mergeMap ∘ scan ∘ endWith ∘ batchSync.

bItems : List (List (Emit Val)) → List BItem
bItems []       = endB ∷ []
bItems (g ∷ gs) = syncB g ∷ (map asyncB (concatL gs) ++ (endB ∷ []))

flushOf : MemI → List (List Val)
flushOf m = maybe′ [] (λ vs → vs ∷ []) (MemI.cFlush m)

collectB : MemI → List BItem → List (List Val)
collectB m []       = []
collectB m (b ∷ bs) = flushOf (bStep m b) ++ collectB (bStep m b) bs

countBatches : List (List (Emit Val)) → List (List Val)
countBatches gs = collectB (mkMem [] nothing nothing) (bItems gs)

------------------------------------------------------------------------
-- scan-collect: scan's running states, flushed and concatenated, ARE
-- collectB of the item stream

collectB-append : (m : MemI) (xs ys : List BItem)
  → collectB m (xs ++ ys) ≡ collectB m xs ++ collectB (foldl bStep m xs) ys
collectB-append m []       ys = refl
collectB-append m (x ∷ xs) ys =
  trans (cong (flushOf (bStep m x) ++_) (collectB-append (bStep m x) xs ys))
        (sym (++-assoc (flushOf (bStep m x)) (collectB (bStep m x) xs)
                       (collectB (foldl bStep (bStep m x) xs) ys)))

scanBurst-collect : (s : MemI) (bs : List BItem)
  → concatMap flushOf (snd (scanBurst bStep s bs)) ≡ collectB s bs
scanBurst-collect s []       = refl
scanBurst-collect s (b ∷ bs) =
  cong (flushOf (bStep s b) ++_) (scanBurst-collect (bStep s b) bs)

scanBurst-foldl : (s : MemI) (bs : List BItem)
  → fst (scanBurst bStep s bs) ≡ foldl bStep s bs
scanBurst-foldl s []       = refl
scanBurst-foldl s (b ∷ bs) = scanBurst-foldl (bStep s b) bs

scan-collect-feed : {n : ℕ} (z : MemI) (B : RxObs n BItem) (sB : State B)
  (a : MemI) (is : List (In n))
  → concatMap flushOf (snd (feed (scanRx bStep z B) (sB , a) is))
    ≡ collectB a (snd (feed B sB is))
scan-collect-feed z B sB a []       = refl
scan-collect-feed z B sB a (i ∷ is)
  rewrite concatMap-++ flushOf (snd (scanBurst bStep a (snd (step B sB i))))
            (snd (feed (scanRx bStep z B)
              (fst (step B sB i) , fst (scanBurst bStep a (snd (step B sB i)))) is))
        | scanBurst-collect a (snd (step B sB i))
        | scan-collect-feed z B (fst (step B sB i))
            (fst (scanBurst bStep a (snd (step B sB i)))) is
        | collectB-append a (snd (step B sB i)) (snd (feed B (fst (step B sB i)) is))
        | scanBurst-foldl a (snd (step B sB i))
  = refl

scan-collect : {n : ℕ} (z : MemI) (B : RxObs n BItem) (is : List (In n))
  → concatMap flushOf (run (scanRx bStep z B) is) ≡ collectB z (run B is)
scan-collect z B is = scan-collect-feed z B (start B) z is

------------------------------------------------------------------------
-- batchSync-bItems: batchSync + endWith serialize m's grouped trace into
-- exactly the `bItems` stream.  bsB m = the batchSync/endWith front end.

bsB : {n : ℕ} → Inst n Val → RxObs n BItem
bsB m = endWithRx endB (batchSyncRx m)

-- feed splits along an append (state and output)
feed-++-snd : {I O : Set} (M : Machine I O) (s : State M) (xs ys : List I)
  → snd (feed M s (xs ++ ys))
    ≡ snd (feed M s xs) ++ snd (feed M (fst (feed M s xs)) ys)
feed-++-snd M s []       ys = refl
feed-++-snd M s (x ∷ xs) ys =
  trans (cong (snd (step M s x) ++_) (feed-++-snd M (fst (step M s x)) xs ys))
        (sym (++-assoc (snd (step M s x)) (snd (feed M (fst (step M s x)) xs))
                       (snd (feed M (fst (feed M (fst (step M s x)) xs)) ys))))

feed-single : {I O : Set} (M : Machine I O) (s : State M) (i : I)
  → snd (feed M s (i ∷ [])) ≡ snd (step M s i)
feed-single M s i = ++-[] (snd (step M s i))

-- end-freeness, so endWith fires only at the trailing `end`
isEnd : {n : ℕ} → In n → Bool
isEnd end = true
isEnd _   = false

noEnds : {n : ℕ} → List (In n) → Bool
noEnds []       = true
noEnds (x ∷ xs) = not (isEnd x) ∧ noEnds xs

not-true : (b : Bool) → not b ≡ true → b ≡ false
not-true true  ()
not-true false _ = refl

noEnds-++ : {n : ℕ} (xs ys : List (In n))
  → noEnds xs ≡ true → noEnds ys ≡ true → noEnds (xs ++ ys) ≡ true
noEnds-++ []       ys _ q = q
noEnds-++ (x ∷ xs) ys p q
  rewrite ∧-split-left (not (isEnd x)) (noEnds xs) p =
  noEnds-++ xs ys (∧-split-right (not (isEnd x)) (noEnds xs) p) q

noEnds-map-next : {n : ℕ} (xs : List (Fin n × Val))
  → noEnds (map (λ p → next (fst p) (snd p)) xs) ≡ true
noEnds-map-next []       = refl
noEnds-map-next (x ∷ xs) = noEnds-map-next xs

noEnds-map-endSlot : {n : ℕ} (fs : List (Fin n))
  → noEnds (map endSlot fs) ≡ true
noEnds-map-endSlot []       = refl
noEnds-map-endSlot (f ∷ fs) = noEnds-map-endSlot fs

-- one non-frame, non-end input at b = true: the response is map asyncB
-- of m's response (endWith passes it through; batchSync is past its
-- frame). Stated at `snd`/`fst` level so it matches the projected,
-- atEnd-reduced goal term.
stepB-nonend-snd : {n : ℕ} (m : Inst n Val) (sm : State m) (x : In n)
  → isEnd x ≡ false
  → snd (step (bsB m) (true , sm) x) ≡ map asyncB (snd (step m sm x))
stepB-nonend-snd m sm (frame ss) _ = refl
stepB-nonend-snd m sm (next j v) _ = refl
stepB-nonend-snd m sm (endSlot j) _ = refl
stepB-nonend-snd m sm end          ()

-- feeding an end-free burst at b = true: exactly map asyncB of m's trace
feedB-mid : {n : ℕ} (m : Inst n Val) (sm : State m) (xs : List (In n))
  → noEnds xs ≡ true
  → feed (bsB m) (true , sm) xs
    ≡ ((true , fst (feed m sm xs)) , map asyncB (snd (feed m sm xs)))
feedB-mid m sm []       _  = refl
feedB-mid m sm (x ∷ xs) ne
  rewrite feedB-mid m (fst (step m sm x)) xs
            (∧-split-right (not (isEnd x)) (noEnds xs) ne)
        | stepB-nonend-snd m sm x
            (not-true (isEnd x) (∧-split-left (not (isEnd x)) (noEnds xs) ne))
        | map-++ asyncB (snd (step m sm x)) (snd (feed m (fst (step m sm x)) xs))
  = refl

-- an end-free prefix then the trailing `end`: map asyncB then one endB
feedB-tail : {n : ℕ} (m : Inst n Val) (sm : State m) (xs : List (In n))
  → noEnds xs ≡ true
  → snd (feed (bsB m) (true , sm) (xs ++ (end ∷ [])))
    ≡ map asyncB (snd (feed m sm (xs ++ (end ∷ [])))) ++ (endB ∷ [])
feedB-tail m sm xs ne
  rewrite feed-++-snd (bsB m) (true , sm) xs (end ∷ [])
        | feedB-mid m sm xs ne
        | feed-single (bsB m) (true , fst (feed m sm xs)) end
        | feed-++-snd m sm xs (end ∷ [])
        | feed-single m (fst (feed m sm xs)) end
        | map-++ asyncB (snd (feed m sm xs)) (snd (step m (fst (feed m sm xs)) end))
        | ++-assoc (map asyncB (snd (feed m sm xs)))
                   (map asyncB (snd (step m (fst (feed m sm xs)) end))) (endB ∷ [])
  = refl

batchSync-bItems : {n : ℕ} (m : Inst n Val) (em : Emissions n)
  → run (bsB m) (flatten em) ≡ bItems (groupsOf m (flatten em))
batchSync-bItems {n} m em
  rewrite sym (++-assoc (map (λ p → next (fst p) (snd p)) (asyncs em))
                        (map endSlot allFins) (end ∷ []))
        | feedB-tail m (fst (step m (start m) (frame (syncs em))))
            (map (λ p → next (fst p) (snd p)) (asyncs em) ++ map endSlot allFins)
            (noEnds-++ (map (λ p → next (fst p) (snd p)) (asyncs em))
                       (map endSlot allFins)
                       (noEnds-map-next (asyncs em)) (noEnds-map-endSlot (allFins {n})))
        | feed-groups m (fst (step m (start m) (frame (syncs em))))
            ((map (λ p → next (fst p) (snd p)) (asyncs em) ++ map endSlot allFins)
             ++ (end ∷ []))
  = refl

------------------------------------------------------------------------
-- THE mechanical half: the counting pipeline reads only the trace

counting-factors : {n : ℕ} (em : Emissions n) (m : Inst n Val)
  → run (batchSimultaneousI m) (flatten em)
    ≡ countBatches (groupsOf m (flatten em))
counting-factors em m =
  trans (mergeMap-oneshot MemI.cFlush
           (scanRx bStep (mkMem [] nothing nothing) (bsB m)) (flatten em))
        (trans (scan-collect (mkMem [] nothing nothing) (bsB m) (flatten em))
               (cong (collectB (mkMem [] nothing nothing)) (batchSync-bItems m em)))

------------------------------------------------------------------------
-- tripwire: counting-factors holds BY COMPUTATION on the diamond

private
  emX : Emissions 1
  emX = emissions ([] ∷ []) ((fzero , 5) ∷ [])

  eX : Exp 1
  eX = mergeE (srcE fzero) (mapE suc (srcE fzero))

  counting-factors-diamond :
    run (batchSimultaneousI (compile eX)) (flatten emX)
    ≡ countBatches (groupsOf (compile eX) (flatten emX))
  counting-factors-diamond = refl
