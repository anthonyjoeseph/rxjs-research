{-# OPTIONS --guardedness #-}

-- THE AUTHOR'S PROGRAM AND ITS ELABORATION.  An `SObs` is what a user
-- writes against srxjs: the same primitives as plain rxjs, so the same
-- tree, its leaves fixed timelines, and its plain reading (`plain`) is
-- the tree itself.  `batchSimultaneous` stands only on top, applied to
-- the elaboration, so it is not a former.
--
-- NO AUTHOR'S LEAF IS FRESH: a `fresh` leaf shows its subscription
-- position, which the elaboration moves, so the two readings could not
-- show the same values.  Only the elaboration mints.
--
-- `elaborate` is srxjs written in rxjs, one former at a time: each
-- primitive rebuilt over InstEmits, one emit per plain emit plus marks.
-- It is generic in the leaves and in the names, so every runtime runs
-- the same elaboration, and nothing in it can do more with a name than
-- compare it.  A name is drawn from `mint`, a leaf that emits a name no
-- other subscription has.

-- AN INSTANT IS NAMED WHERE IT STARTS.  Every instant after the
-- subscribe burst is one async step of one cold.  The cold mints there
-- and sends `begin` under the minted name, ahead of the step itself;
-- the top restamps every emit with the name of the last `begin` it saw,
-- so the names agree with the instants by construction.
--
-- AN INSTANT'S END IS COUNTED AT THE TOP.  Each copy of a `begin`
-- reaching the batcher is a ROUTE: a path from the firing cold up, which
-- ends in `over` (the cold's step returned, so the whole cascade is
-- done) or `stop` (the path was cut first).  The batcher releases at the
-- first `over`, or when every route has stopped, or when the run
-- completes.  A completion is no mark: the routes a stream holds when it
-- completes are carried on by whatever reads it, and stopped by the
-- first flatMap that outlives it.

-- EVERY STREAM'S COUNT IS EXACT: its `begin`s less its `stop`s, so no
-- path is stopped twice.  A reader subscribed to a `connect` mid-instant
-- meets the instant's later emits without the `begin`s that opened it,
-- so it JOINS: before the first emit it meets, or the source's end, it
-- sends one `begin` per route the source holds then.  Every connect
-- source is counted for this, its count riding beside each emit and
-- beside a last item telling its end.
--
-- A FLATMAP SIMULATES ITS OWN BOOKKEEPING.  Its outer is shared, read by
-- the real flatMap and by a scan beside it; the outer's marks go around
-- the real flatMap, so a switch, an exhaust or a queue never swallows
-- one.  Each lane reports its start, the routes it holds as it ends, its
-- end and the end of its subscribe burst; each outer value opens a
-- bracket; and from those the scan knows what the real flatMap does
-- when a lane ends: subscribe a queued lane, whose burst the ended
-- lane's routes cover, complete, carrying them, or neither, which stops
-- them.  The outer's routes stop at its end unless the flatMap ends with
-- it, and a switch stops its lane's.

-- A CUT ROUTE IS PARKED WHILE THE INSTANT CAN STILL COME BACK.  Past a
-- cut, the instant reaches the flatMap again only through a lane reading
-- a connect late, and only while that connect still holds a route of it.
-- So the scan watches every connect in scope, and a route it would stop
-- waits instead until none of them holds a route of the instant.
--
-- AN OVER ENDS EVERY ROUTE OF ITS INSTANT, so what a lane sends of the
-- instant past another lane's over is dropped: a stop of a parked route
-- released once its connect is over, a begin of a reader joining there,
-- another lane's copy of the over, and the scan's own cuts.  A lane ends
-- handing on at most the routes the scan counts of the lanes.
-- A stop of a branch the scan counts no route of is dropped likewise.
--
-- The plumbing is `connect`: a source subscribes after its body, so
-- nested connects put the outer's readers in the order rxjs would meet
-- them, and a choice among programs is a choice among `connected`
-- handles, never among children.
open import Relation.Binary.Definitions using (DecidableEquality)

module simultaneous.SObs where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.List using (List; []; _∷_; _∷ʳ_; _++_; concat; replicate)
open import Data.List.Properties using (++-identityʳ)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<ᵇ_; _⊓_; z≤n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Relation.Nullary using (does)

open import Tree using (Obs; Later; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer; merge)
open import denotation.Events using (Timeline; From; fixed)
import denotation.Events as Evs
open import simultaneous.InstEmit using (InstEmit; instEmit; value; mark; Mark; begin; over; stop; outerOpen; outerClose; laneStart; carry; laneDone; burstEnd; outerDone; subscribed; completed; valuesOf)

-- An author's cold: a timeline fixed relative to its subscription.
data Fixed (A : Set) : Set₁ where
  fixedˢ : From A 0 → Fixed A

SObs : List Set → Set → Set₁
SObs = Obs Fixed

-- The program as plain rxjs runs it.
mutual
  plain : ∀ {Γ A} → SObs Γ A → Obs Timeline Γ A
  plain (cold (fixedˢ m))  = cold (fixed m)
  plain empty              = empty
  plain (of xs)            = of xs
  plain (map f s)          = map f (plain s)
  plain (scan f z s)       = scan f z (plain s)
  plain (takeWhile i p s)  = takeWhile i p (plain s)
  plain (flatMap op f s)   = flatMap op (λ a → plain (f a)) (plain s)
  plain (connect s b)      = connect (plain s) (plain b)
  plain (connected i)      = connected i
  plain (defer l)          = defer (plainˡ l)

  plainˡ : ∀ {Γ A} → Later Fixed Γ A → Later Timeline Γ A
  plainˡ l .Later.force = plain (Later.force l)

-- A cold's emits as its elaboration reads them: a value, its completion,
-- or the end of its subscribe burst.
data Tag (A : Set) : Set where
  val   : A → Tag A
  cdone : Tag A
  tick  : Tag A

-- A lane is subscribed as two parts: the lane, between its start and its
-- end, and then the end of its subscribe burst.
data Part : Set where
  lanePart burstPart : Part

-- What a flatMap's scan reads: the outer, the real flatMap, and the
-- closing of each outer value.
data Branch : Set where
  outerB laneB closeB : Branch

-- A flatMap's bookkeeping, as its scan simulates it, for the instant
-- named `at`.
record Flat (N : Set) : Set where
  constructor flat
  field
    at : N
    active queue : ℕ
    -- the outer completed; the next lane started is a queued one; the
    -- last lane started has ended
    finished popping dead : Bool
    -- the instant's over has passed
    spent : Bool
    -- routes open through the outer and through the lanes; routes of an
    -- ended lane covering a queued lane's burst; routes the lane now
    -- ending holds; routes cut, waiting on the connects in scope
    outer lanes held acc parked : ℕ
    -- each connect in scope, by index: the routes it holds
    live : List (N × ℕ)

-- The batcher's state: past the subscribe burst, the open instant, its
-- values, its routes still open.
record Batching (A : Set) (N : Set) : Set where
  constructor batching
  field
    late   : Bool
    at     : N
    held   : List A
    routes : ℕ

isZero : ℕ → Bool
isZero zero    = true
isZero (suc _) = false

private
  isTick : ∀ {A} → Tag A → Bool
  isTick tick = true
  isTick _    = false

  isLane : Part → Bool
  isLane lanePart  = true
  isLane burstPart = false

  ext : ∀ {X : Set} {Γ Δ : List Set} → (∀ {Y} → Y ∈ Γ → Y ∈ Δ) → ∀ {Y} → Y ∈ X ∷ Γ → Y ∈ X ∷ Δ
  ext ρ (here p)  = here p
  ext ρ (there i) = there (ρ i)

-- A leaf emitting its value as it is subscribed, then silent forever.
lone : ∀ {A} → A → Timeline A
lone a = fixed (Evs.at 0 z≤n (Evs.emit a (Evs.close silence)))
  where
    silence : ∀ {A t} → Evs.From∞ A t
    silence .Evs.From∞.force = Evs.quiet

module Elaborate {C : Set → Set₁} {N : Set} (_≟_ : DecidableEquality N) (name : N) (mint : C N) (once : ∀ {A} → A → C A) where

  -- What the engine runs: the author's leaves.
  E : List Set → Set → Set₁
  E = Obs C

  IE : Set → Set
  IE = InstEmit N

  ------------------------------------------------------------------------
  -- Plumbing, never around a child

  marked : ∀ {A} → Mark → IE A
  marked m = instEmit (mark m) name

  concatˢ : ∀ {Γ X} → E Γ X → E Γ X → E Γ X
  concatˢ s t = flatMap (mergeᶠ (just 1)) (λ b → if b then s else t) (of (true ∷ false ∷ []))

  each : ∀ {Γ X Y} → (X → List Y) → E Γ X → E Γ Y
  each f s = flatMap (mergeᶠ nothing) (λ x → of (f x)) s

  ------------------------------------------------------------------------
  -- Routes

  -- A stream's open routes, of the instant it last began.
  Routes : Set
  Routes = N × ℕ

  -- An emit of a connect source, or its end, beside the routes the
  -- source held before it.
  AIE : Set → Set
  AIE X = Routes × Maybe (IE X)

  -- A `begin` adds a route, starting afresh under a new name; a `stop`
  -- takes one; an `over` ends them all.
  count : ∀ {A} → Routes → IE A → Routes
  count (m , k) (instEmit (mark begin) n) with does (n ≟ m)
  ... | true  = m , suc k
  ... | false = n , 1
  count (m , k) (instEmit (mark stop) _) = m , k ∸ 1
  count (m , k) (instEmit (mark over) _) = m , 0
  count r       _                        = r

  annStep : ∀ {A} → Routes × AIE A → Maybe (IE A) → Routes × AIE A
  annStep (r , _) (just e) = count r e , (r , just e)
  annStep (r , _) nothing  = r , (r , nothing)

  -- The source read through its own subject, then its end.
  annotate : ∀ {Γ A} → E Γ (IE A) → E Γ (AIE A)
  annotate s = map proj₂ (scan annStep ((name , 0) , ((name , 0) , nothing))
    (connect (map just s) (concatˢ (connected (here refl)) (of (nothing ∷ [])))))
  {-# INLINE annotate #-}

  -- What a reader sends before the first emit it meets: a `begin` for
  -- each route the source holds of that emit's instant.
  joins : ∀ {A} → Routes → IE A → List (IE A)
  joins (m , k) (instEmit (mark begin) n) with does (n ≟ m)
  ... | true  = replicate k (instEmit (mark begin) m)
  ... | false = []
  joins (m , k) _ = replicate k (instEmit (mark begin) m)

  joinStep : ∀ {A} → Bool × List (IE A) → AIE A → Bool × List (IE A)
  joinStep (true  , _) (r , just e)  = false , joins r e ++ e ∷ []
  joinStep (true  , _) (r , nothing) = false , replicate (proj₂ r) (instEmit (mark begin) (proj₁ r))
  joinStep (false , _) (r , just e)  = false , e ∷ []
  joinStep (false , _) (r , nothing) = false , []

  reader : ∀ {Γ A} → E Γ (AIE A) → E Γ (IE A)
  reader s = each proj₂ (scan joinStep (true , []) s)

  -- The routes a connect holds past an emit, or past its end.
  past : ∀ {X} → AIE X → Routes
  past (r , just e)  = count r e
  past (r , nothing) = proj₁ r , 0

  -- Every connect in scope, from index `i`, telling the routes it holds.
  trackers : ∀ {Δ} (Γ : List Set) → ℕ → (∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → E Δ (ℕ × Routes)
  trackers []      i ρ = empty
  trackers (X ∷ Γ) i ρ = merge (map (λ a → i , past a) (connected (ρ (here refl)))) (trackers Γ (suc i) (λ j → ρ (there j)))

  ------------------------------------------------------------------------
  -- The leaves and the one-to-one formers

  phase : ∀ {A} → Bool × Tag A → Tag A → Bool × Tag A
  phase (late , _) t = (late ∨ isTick t) , t

  -- An async step mints its instant's name and sends `begin` first; a
  -- value's step ends in `over`, a completion's is carried on by the
  -- completion itself.  Each is its own instant: a completion is an
  -- async call of its own, even straight after a value.
  render : ∀ {Γ A} → Bool × Tag A → E Γ (IE A)
  render (false , val a) = of (instEmit (value a) name ∷ [])
  render (true  , val a) =
    flatMap (mergeᶠ nothing) (λ n → of (instEmit (mark begin) n ∷ instEmit (value a) n ∷ instEmit (mark over) n ∷ [])) (cold mint)
  render (true  , cdone) = map (λ n → instEmit (mark begin) n) (cold mint)
  render _               = empty

  coldˢ : ∀ {Γ A} → C A → E Γ (IE A)
  coldˢ c = flatMap (mergeᶠ nothing) render
    (scan phase (false , tick) (merge (concatˢ (map val (cold c)) (of (cdone ∷ []))) (of (tick ∷ []))))
  {-# INLINE coldˢ #-}

  ofˢ : ∀ {Γ A} → List A → E Γ (IE A)
  ofˢ xs = of (L.map (λ x → instEmit (value x) name) xs)
  {-# INLINE ofˢ #-}

  mapIE : ∀ {A B} → (A → B) → IE A → IE B
  mapIE f (instEmit (value a) n) = instEmit (value (f a)) n
  mapIE f (instEmit (mark m) n)  = instEmit (mark m) n

  mapˢ : ∀ {Γ A B} → (A → B) → E Γ (IE A) → E Γ (IE B)
  mapˢ f s = map (mapIE f) s
  {-# INLINE mapˢ #-}

  scanIE : ∀ {A B} → (B → A → B) → B × IE B → IE A → B × IE B
  scanIE f (b , _) (instEmit (value a) n) = f b a , instEmit (value (f b a)) n
  scanIE f (b , _) (instEmit (mark m) n)  = b , instEmit (mark m) n

  scanˢ : ∀ {Γ A B} → (B → A → B) → B → E Γ (IE A) → E Γ (IE B)
  scanˢ f z s = map proj₂ (scan (scanIE f) (z , marked begin) s)
  {-# INLINE scanˢ #-}

  passes : ∀ {A} → (A → Bool) → IE A → Bool
  passes p (instEmit (value a) _) = p a
  passes p (instEmit (mark _) _)  = true

  takeWhileˢ : ∀ {Γ A} → Bool → (A → Bool) → E Γ (IE A) → E Γ (IE A)
  takeWhileˢ i p s = takeWhile i (passes p) s
  {-# INLINE takeWhileˢ #-}

  ------------------------------------------------------------------------
  -- flatMap

  -- The outer as the scan reads it: a value opens its bracket.
  opening : ∀ {A B} → IE A → IE B
  opening (instEmit (value _) n) = instEmit (mark outerOpen) n
  opening (instEmit (mark m) n)  = instEmit (mark m) n

  closing : ∀ {A B} → IE A → List (IE B)
  closing (instEmit (value _) n) = instEmit (mark outerClose) n ∷ []
  closing (instEmit (mark _) _)  = []

  -- Read after the real flatMap: each value's bracket closes, then the
  -- outer's end.
  closer : ∀ {Δ A B} → E (IE A ∷ Δ) (IE B)
  closer = concatˢ (each closing (connected (here refl))) (of (marked outerDone ∷ []))

  piece : ∀ {Θ B} → Part → ℕ → E (IE B ∷ Θ) (IE B)
  piece lanePart  0 = of (marked laneStart ∷ [])
  piece burstPart 0 = of (marked burstEnd ∷ [])
  piece _         1 = connected (here refl)
  piece lanePart  2 = of (marked laneDone ∷ [])
  piece _         _ = empty

  framed : ∀ {Θ B} → Part → E (IE B ∷ Θ) (IE B)
  framed k = flatMap (mergeᶠ (just 1)) (piece k) (of (0 ∷ 1 ∷ 2 ∷ []))

  -- A lane counts its routes, and tells them as it ends.
  laneStep : ∀ {A} → Routes × List (IE A) → IE A → Routes × List (IE A)
  laneStep (r , _) (instEmit (mark laneDone) n) = r , replicate (proj₂ r) (marked carry) ++ instEmit (mark laneDone) n ∷ []
  laneStep (r , _) e = count r e , e ∷ []

  counted : ∀ {Θ B} → E Θ (IE B) → E Θ (IE B)
  counted s = each proj₂ (scan laneStep ((name , 0) , []) s)

  -- The lane, gated to its own part, under its subject.
  laneˢ : ∀ {Θ B} → E Θ (IE B) → E Θ (IE B)
  laneˢ x = flatMap (mergeᶠ nothing)
    (λ k → connect (flatMap (mergeᶠ nothing) (λ _ → x) (takeWhile false isLane (of (k ∷ [])))) (counted (framed k)))
    (of (lanePart ∷ burstPart ∷ []))
  {-# INLINE laneˢ #-}

  Out : Set → Set
  Out B = Flat N × List (IE B)

  stops : ∀ {B} → ℕ → N → List (IE B)
  stops k n = replicate k (instEmit (mark stop) n)

  holds : N → Routes → Bool
  holds n (m , k) = does (m ≟ n) ∧ not (isZero k)

  anyHolds : N → List Routes → Bool
  anyHolds n []      = false
  anyHolds n (r ∷ σ) = holds n r ∨ anyHolds n σ

  setAt : ℕ → Routes → List Routes → List Routes
  setAt zero    r []      = r ∷ []
  setAt zero    r (_ ∷ σ) = r ∷ σ
  setAt (suc i) r []      = (name , 0) ∷ setAt i r []
  setAt (suc i) r (x ∷ σ) = x ∷ setAt i r σ

  -- Routes cut: parked while a connect in scope holds a route of the
  -- instant, else stopped.
  cut : ∀ {B} → ℕ → N → Flat N → Out B
  cut k n s with Flat.spent s | anyHolds (Flat.at s) (Flat.live s)
  ... | true  | _     = s , []
  ... | false | true  = record s { parked = Flat.parked s + k } , []
  ... | false | false = s , stops k n

  -- A connect in scope moved: parked routes stop once none holds one.
  unpark : ∀ {B} → N → Flat N → Out B
  unpark n s with anyHolds (Flat.at s) (Flat.live s)
  ... | true  = s , []
  ... | false = record s { parked = 0 } , stops (Flat.parked s) n

  -- How the flatMap takes an outer value: a switch stops its lane's
  -- routes.
  arrive : ∀ {B} → FlatOp → N → Flat N → Out B
  arrive (mergeᶠ (just k)) n s with Flat.active s <ᵇ k
  ... | true  = s , []
  ... | false = record s { queue = suc (Flat.queue s) } , []
  arrive (mergeᶠ nothing) n s = s , []
  arrive switchᶠ          n s = cut (Flat.lanes s) n (record s { active = 0 ; lanes = 0 })
  arrive exhaustᶠ         n s = s , []

  -- A lane ended holding `k` routes: held for the queued lane rxjs
  -- subscribes next, or for the flatMap's own completion, which carries
  -- them; else stopped here, with any it was handed.
  ended : ∀ {B} → ℕ → N → Flat N → Out B
  ended k n s with isZero (Flat.queue s)
  ... | false = record s { held = Flat.held s + k } , []
  ... | true with Flat.finished s ∧ isZero (Flat.active s)
  ...   | true  = record s { held = Flat.held s + k } , []
  ...   | false = cut (k + Flat.held s) n (record s { held = 0 })

  -- A queued lane's burst is over: the routes it was handed stop.
  burstOver : ∀ {B} → Bool → N → Flat N → Out B
  burstOver true  n s = s , []
  burstOver false n s = cut (Flat.held s) n (record s { held = 0 })

  -- The outer ended: its routes stop, unless the flatMap ends with it.
  left : ∀ {B} → N → Flat N → Out B
  left n s with isZero (Flat.active s) ∧ isZero (Flat.queue s)
  ... | true  = s , []
  ... | false = cut (Flat.outer s) n (record s { outer = 0 })

  bump : Branch → (ℕ → ℕ) → Flat N → Flat N
  bump outerB f s = record s { outer = f (Flat.outer s) }
  bump laneB  f s = record s { lanes = f (Flat.lanes s) }
  bump closeB f s = s

  -- The routes a branch holds of the instant, as the scan counts them.
  share : Branch → Flat N → ℕ
  share outerB s = Flat.outer s
  share laneB  s = Flat.lanes s
  share closeB s = 0

  -- A branch's stop, unless the branch holds no route the scan counts: a
  -- route an over has ended is stopped by no one.
  stopped : ∀ {B} → Branch → N → Flat N → ℕ → Out B
  stopped b n s zero    = s , []
  stopped b n s (suc _) = bump b (_∸ 1) s , instEmit (mark stop) n ∷ []

  anew : N → Flat N → Flat N
  anew n s = record s { at = n ; outer = 0 ; lanes = 0 ; held = 0 ; acc = 0 ; parked = 0 ; spent = false }

  entered : Branch → N → Flat N → Flat N
  entered b n s with does (n ≟ Flat.at s)
  ... | true  = bump b suc s
  ... | false = bump b suc (anew n s)

  -- A begin of the instant past its over is a reader joining routes that
  -- are already ended: nothing to count.
  begun : ∀ {B} → Branch → N → Flat N → Out B
  begun b n s with does (n ≟ Flat.at s) ∧ Flat.spent s
  ... | true  = s , []
  ... | false = entered b n s , instEmit (mark begin) n ∷ []

  -- The instant's first over ends its routes; any later one is a copy.
  overed : ∀ {B} → N → Flat N → Out B
  overed n s with Flat.spent s
  ... | true  = s , []
  ... | false = record (anew (Flat.at s) s) { spent = true } , instEmit (mark over) n ∷ []

  onMark : ∀ {B} → FlatOp → Branch → Flat N → Mark → N → Out B
  onMark op b s begin      n = begun b n s
  onMark op b s stop       n = stopped b n s (if Flat.spent s then 0 else share b s)
  onMark op b s over       n = overed n s
  onMark op b s carry      n = record s { acc = suc (Flat.acc s) } , []
  onMark op b s outerOpen  n = arrive op n s
  onMark op b s outerClose n = s , []
  onMark op b s laneStart  n =
    record s { active = suc (Flat.active s)
             ; queue = if Flat.popping s then Flat.queue s ∸ 1 else Flat.queue s
             ; popping = false ; dead = false } , []
  onMark op b s laneDone   n =
    ended (Flat.acc s ⊓ Flat.lanes s) n
      (record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ Flat.acc s ; acc = 0
                ; popping = not (isZero (Flat.queue s)) ; dead = true })
  onMark op b s burstEnd   n = burstOver (isZero (Flat.held s) ∨ Flat.dead s) n s
  onMark op b s outerDone  n = left n (record s { finished = true })
  onMark op b s m          n = s , instEmit (mark m) n ∷ []

  Input : Set → Set
  Input B = (Branch × IE B) ⊎ (ℕ × Routes)

  react : ∀ {B} → FlatOp → Out B → Maybe (Input B) → Out B
  react op (s , _) (just (inj₁ (b , instEmit (value v) n))) = s , instEmit (value v) n ∷ []
  react op (s , _) (just (inj₁ (b , instEmit (mark m) n)))  = onMark op b s m n
  react op (s , _) (just (inj₂ (i , r)))                    = unpark name (record s { live = setAt i r (Flat.live s) })
  react op (s , _) nothing                                  = s , []

  branch : ∀ {Δ A B} → Branch → E (IE B ∷ IE B ∷ IE A ∷ Δ) (IE B)
  branch outerB = map opening (connected (there (there (here refl))))
  branch laneB  = connected (here refl)
  branch closeB = connected (there (here refl))

  going : ∀ {X : Set} → Maybe X → Bool
  going (just _) = true
  going nothing  = false

  -- The flatMap's own branches, then a last item telling they are done.
  own : ∀ {Δ A B} → E (IE B ∷ IE B ∷ IE A ∷ Δ) (Maybe (Input B))
  own = concatˢ (flatMap (mergeᶠ nothing) (λ b → map (λ e → just (inj₁ (b , e))) (branch b)) (of (outerB ∷ laneB ∷ closeB ∷ [])))
                (of (nothing ∷ []))

  -- The connects in scope are watched first, before any reader the
  -- flatMap's own outer subscribes, and only until its own branches are
  -- done: a connect outliving the flatMap never holds it open.
  fed : ∀ {Δ A B} → E (IE B ∷ IE B ∷ IE A ∷ Δ) (ℕ × Routes) → Bool → E (IE B ∷ IE B ∷ IE A ∷ Δ) (Maybe (Input B))
  fed tk true  = map (λ x → just (inj₂ x)) tk
  fed tk false = own

  combined : ∀ {Δ A B} → FlatOp → E (IE B ∷ IE B ∷ IE A ∷ Δ) (ℕ × Routes) → E (IE B ∷ IE B ∷ IE A ∷ Δ) (IE B)
  combined op tk = each proj₂
    (scan (react op) (flat name 0 0 false false false false 0 0 0 0 0 [] , [])
      (takeWhile false going (flatMap (mergeᶠ nothing) (fed tk) (of (true ∷ false ∷ [])))))

  -- The outer `O` is read first by the scan, then by the real flatMap,
  -- then by `closer`: the order the nested connects subscribe them in.
  flatMapˢ : ∀ {Δ A B} → FlatOp → E (IE B ∷ IE B ∷ IE A ∷ Δ) (ℕ × Routes) → (A → E (IE B ∷ IE A ∷ Δ) (IE B)) → E Δ (IE A) → E Δ (IE B)
  flatMapˢ op tk g s =
    connect s (connect closer
      (connect (flatMap op (λ a → laneˢ (g a)) (each valuesOf (connected (there (here refl))))) (combined op tk)))
  {-# INLINE flatMapˢ #-}

  ------------------------------------------------------------------------
  -- The elaboration

  -- `elab`, one clause per former, each operator inlined around the
  -- elaborated child: Agda's productivity check accepts recursion through
  -- `defer` only under constructors, and sees through `INLINE`, nested
  -- too.  An opaque definition around any recursive call sinks the whole
  -- mutual block, and so does a pattern-matching lambda whose arm holds
  -- the child: Agda lifts it out as a definition of its own.
  --
  -- The rule binds only the path down to a child.  Data may pass through
  -- anything, so an operator's logic stays opaque once it reads its child
  -- as a `connect`'s source through `connected`, and a choice between
  -- parts gates each with a `takeWhile` on a one-value `of`.  A child
  -- moved under a new binder is elaborated under a renaming, since
  -- `rename` is opaque.
  --
  -- DEAD ROUTE: postulated operators around the calls.  Measured: a
  --   postulate, or a definition without `INLINE`, in place of any
  --   constructor fails termination at every clause, `connect`'s included.
  mutual
    elab : ∀ {Γ Δ A} → (∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → Obs C Γ A → E Δ (IE A)
    elab ρ (cold c)          = coldˢ c
    elab ρ empty             = empty
    elab ρ (of xs)           = ofˢ xs
    elab ρ (map f s)         = mapˢ f (elab ρ s)
    elab ρ (scan f z s)      = scanˢ f z (elab ρ s)
    elab ρ (takeWhile i p s) = takeWhileˢ i p (elab ρ s)
    elab {Γ} ρ (flatMap op f s) =
      flatMapˢ op (trackers Γ 0 (λ i → there (there (there (ρ i))))) (λ a → elab (λ i → there (there (ρ i))) (f a)) (elab ρ s)
    elab ρ (connect s b)     = connect (annotate (elab ρ s)) (elab (ext ρ) b)
    elab ρ (connected i)     = reader (connected (ρ (∈-map⁺ AIE i)))
    elab ρ (defer l)         = defer (elabˡ ρ l)

    elabˡ : ∀ {Γ Δ A} → (∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → Later C Γ A → Later C Δ (IE A)
    elabˡ ρ l .Later.force = elab ρ (Later.force l)

  -- Every emit under the name of the last `begin` before it.
  restamp : ∀ {A} → N × IE A → IE A → N × IE A
  restamp (n , _) (instEmit (mark begin) m) = m , instEmit (mark begin) m
  restamp (n , _) (instEmit ev _)           = n , instEmit ev n

  -- Any emit but the completion mark.
  unfinished : ∀ {A} → IE A → Bool
  unfinished (instEmit (mark completed) _) = false
  unfinished _                             = true

  -- The run, its completion told by a mark as it completes: read through
  -- its own subject by a concat queueing the mark, so the mark leaves
  -- from the run's completion, even where its subscription never returns.
  completing : ∀ {Δ A} → E Δ (IE A) → E Δ (IE A)
  completing s = connect s (concatˢ (connected (here refl)) (of (marked completed ∷ [])))

  -- The closed run, then the end of its subscribe burst, told by a mark
  -- from a lane that never ends, so the program ends at the completion
  -- mark and there only: the subscribe mark follows it only if the run
  -- is still going as its subscription returns.
  wrapped : ∀ {Δ A} → E Δ (IE A) → E Δ (IE A)
  wrapped s = takeWhile true unfinished (merge (completing s) (cold (once (marked subscribed))))

  -- A batcher reads the elaborated program as the source of its own scan,
  -- subscribed where the program alone would be, so the names it mints
  -- are the program's own.
  elaborate : ∀ {Γ A} → Obs C Γ A → E (L.map AIE Γ) (IE A)
  elaborate o = map proj₂ (scan restamp (name , marked begin) (wrapped (elab (λ i → i) o)))

  ------------------------------------------------------------------------
  -- The batcher

  -- The batcher's state, and what its last step released.
  Step : Set → Set
  Step A = Batching A N × List (IE (List A))

  private
    release : ∀ {A} → Batching A N → List (IE (List A))
    release b with Batching.held b
    ... | []     = []
    ... | v ∷ vs = instEmit (value (v ∷ vs)) (Batching.at b) ∷ []

    now : ∀ {A} → Batching A N → Step A
    now b = record b { held = [] ; routes = 0 } , release b

    onBegin : ∀ {A} → N → Batching A N → Step A
    onBegin n b with does (n ≟ Batching.at b)
    ... | true  = record b { routes = suc (Batching.routes b) } , []
    ... | false = record b { at = n ; held = [] ; routes = 1 } , release b

    onStop : ∀ {A} → Batching A N → Step A
    onStop b with isZero (Batching.routes b ∸ 1)
    ... | true  = now b
    ... | false = record b { routes = Batching.routes b ∸ 1 } , []

    marking : ∀ {A} → Bool → Mark → N → Batching A N → Step A
    marking _    subscribed n b = now (record b { late = true })
    marking _    completed  n b = now b
    marking true begin      n b = onBegin n b
    marking true over       n b = now b
    marking true stop       n b = onStop b
    marking _    _          _ b = b , []

  bstep : ∀ {A} → Step A → IE A → Step A
  bstep (b , _) (instEmit (value a) _) = record b { held = Batching.held b ∷ʳ a } , []
  bstep (b , _) (instEmit (mark m) n)  = marking (Batching.late b) m n b

  bstart : ∀ {A} → Step A
  bstart = batching false name [] 0 , []

  -- The values batches carry, in order.
  unbatched : ∀ {A} → List (IE (List A)) → List A
  unbatched es = concat (concat (L.map valuesOf es))

  private
    release-vals : ∀ {A} (b : Batching A N) → unbatched (release b) ≡ Batching.held b
    release-vals b with Batching.held b
    ... | []     = refl
    ... | v ∷ vs = ++-identityʳ (v ∷ vs)

    now-held : ∀ {A} (b : Batching A N) → unbatched (proj₂ (now b)) ++ Batching.held (proj₁ (now b)) ≡ Batching.held b ++ []
    now-held b = cong (_++ []) (release-vals b)

    kept : ∀ {A} (b : Batching A N) → Batching.held b ≡ Batching.held b ++ []
    kept b = sym (++-identityʳ (Batching.held b))

    mark-held : ∀ {A} l m n (b : Batching A N)
              → unbatched (proj₂ (marking l m n b)) ++ Batching.held (proj₁ (marking l m n b)) ≡ Batching.held b ++ []
    mark-held _     subscribed n b = now-held (record b { late = true })
    mark-held _     completed  n b = now-held b
    mark-held true  begin      n b with does (n ≟ Batching.at b)
    ... | true  = kept b
    ... | false = now-held b
    mark-held false begin      n b = kept b
    mark-held true  over       n b = now-held b
    mark-held false over       n b = kept b
    mark-held true  stop       n b with isZero (Batching.routes b ∸ 1)
    ... | true  = now-held b
    ... | false = kept b
    mark-held false stop       n b = kept b
    mark-held _     outerOpen  n b = kept b
    mark-held _     outerClose n b = kept b
    mark-held _     laneStart  n b = kept b
    mark-held _     carry      n b = kept b
    mark-held _     laneDone   n b = kept b
    mark-held _     burstEnd   n b = kept b
    mark-held _     outerDone  n b = kept b

  -- What a step releases, then holds, is what was held, then the emit's
  -- values.
  bstep-held : ∀ {A} (s : Step A) v → unbatched (proj₂ (bstep s v)) ++ Batching.held (proj₁ (bstep s v)) ≡ Batching.held (proj₁ s) ++ valuesOf v
  bstep-held s       (instEmit (value a) _) = refl
  bstep-held (b , _) (instEmit (mark m) n)  = mark-held (Batching.late b) m n b

  -- A completion releases everything held.
  completed-held : ∀ {A} (s : Step A) n → Batching.held (proj₁ (bstep s (instEmit (mark completed) n))) ≡ []
  completed-held s n = refl

  -- What is held, as the batch it would leave as.
  pendingOf : ∀ {A : Set} → N → List A → List (N × List A)
  pendingOf i []       = []
  pendingOf i (v ∷ vs) = (i , v ∷ vs) ∷ []

  pending : ∀ {A : Set} → Batching A N → List (N × List A)
  pending b = pendingOf (Batching.at b) (Batching.held b)

  -- Batches as emits.
  asEmits : ∀ {A : Set} → List (N × List A) → List (IE (List A))
  asEmits P = L.map (λ g → instEmit (value (proj₂ g)) (proj₁ g)) P

  private
    release-pending : ∀ {A : Set} (b : Batching A N) → release b ≡ asEmits (pending b)
    release-pending b with Batching.held b
    ... | []     = refl
    ... | v ∷ vs = refl

    flushed : ∀ {A : Set} (b : Batching A N) → (proj₂ (now b) ≡ [] × pending (proj₁ (now b)) ≡ pending b)
                                        ⊎ (proj₂ (now b) ≡ asEmits (pending b) × pending (proj₁ (now b)) ≡ [])
    flushed b = inj₂ (release-pending b , refl)

  -- A mark either keeps what is held and releases nothing, or releases
  -- all of it.
  mark-step : ∀ {A : Set} l m n (b : Batching A N)
            → (proj₂ (marking l m n b) ≡ [] × pending (proj₁ (marking l m n b)) ≡ pending b)
            ⊎ (proj₂ (marking l m n b) ≡ asEmits (pending b) × pending (proj₁ (marking l m n b)) ≡ [])
  mark-step _     subscribed n b = flushed (record b { late = true })
  mark-step _     completed  n b = flushed b
  mark-step true  begin      n b with does (n ≟ Batching.at b)
  ... | true  = inj₁ (refl , refl)
  ... | false = inj₂ (release-pending b , refl)
  mark-step false begin      n b = inj₁ (refl , refl)
  mark-step true  over       n b = flushed b
  mark-step false over       n b = inj₁ (refl , refl)
  mark-step true  stop       n b with isZero (Batching.routes b ∸ 1)
  ... | true  = flushed b
  ... | false = inj₁ (refl , refl)
  mark-step false stop       n b = inj₁ (refl , refl)
  mark-step _     outerOpen  n b = inj₁ (refl , refl)
  mark-step _     outerClose n b = inj₁ (refl , refl)
  mark-step _     laneStart  n b = inj₁ (refl , refl)
  mark-step _     carry      n b = inj₁ (refl , refl)
  mark-step _     laneDone   n b = inj₁ (refl , refl)
  mark-step _     burstEnd   n b = inj₁ (refl , refl)
  mark-step _     outerDone  n b = inj₁ (refl , refl)

  -- The subscribe burst is one batch, released when it is over; after
  -- it, an instant's batch is released when its routes are.  The run is
  -- read as the scan's source, so it is subscribed where it would be
  -- alone.
  batchSimultaneous : ∀ {Γ A} → E Γ (IE A) → E Γ (IE (List A))
  batchSimultaneous s = each proj₂ (scan bstep bstart s)
