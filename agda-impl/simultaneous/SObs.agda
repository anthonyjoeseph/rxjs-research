{-# OPTIONS --guardedness #-}

-- THE AUTHOR'S PROGRAM AND ITS ELABORATION.  An `SObs` is what a user
-- writes against srxjs: the same primitives as plain rxjs, so the same
-- tree, and its plain reading is the tree itself.  `batchSimultaneous`
-- stands only on top, applied to the elaboration, so it is not a former.
--
-- `elaborate` is srxjs written in rxjs, one former at a time: each
-- primitive rebuilt over InstEmits, one emit per plain emit plus marks.
-- It is generic in the leaves and in the names, so every runtime runs
-- the same elaboration, and nothing in it can do more with a name than
-- compare it.  A name is drawn from `mint`, a leaf that emits a name no
-- other subscription has.
--
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
-- completes.  A completion is no mark: the path it ends is carried on by
-- whatever reads it, and stopped by the first flatMap that outlives it.
--
-- A FLATMAP SIMULATES ITS OWN BOOKKEEPING.  Its outer is shared, read by
-- the real flatMap and by a scan beside it; the outer's marks go around
-- the real flatMap, so a switch, an exhaust or a queue never swallows
-- one.  Each lane reports its start, its end and the end of its
-- subscribe burst; each outer value is bracketed; and from those the
-- scan knows what the real flatMap does when a lane ends: subscribe a
-- queued lane, complete, or neither, which stops the route.  A `stop`
-- from below, met inside a bracket or a handed-off burst, is part of the
-- route that opened it, and is dropped.
--
-- The plumbing is `connect`: a source subscribes after its body, so
-- nested connects put the outer's readers in the order rxjs would meet
-- them, and a choice among programs is a choice among `connected`
-- handles, never among children.
open import Relation.Binary.Definitions using (DecidableEquality)

module simultaneous.SObs where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.List using (List; []; _∷_; _∷ʳ_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _∸_; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (does)

open import Tree using (Obs; Later; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer; merge)
open import denotation.Events using (Timeline)
open import simultaneous.InstEmit using (InstEmit; instEmit; value; mark; Mark; begin; over; stop; outerOpen; outerClose; laneStart; laneDone; burstEnd; outerDone; subscribed; completed; valuesOf)

SObs : List Set → Set → Set₁
SObs = Obs Timeline

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

-- A flatMap's bookkeeping, as its scan simulates it.
record Flat : Set where
  constructor flat
  field
    active queue : ℕ
    -- the outer completed; an outer value is being read; a queued lane
    -- carries a route through its subscribe burst; the next lane started
    -- is a queued one; the last lane started has ended
    finished bracket handoff popping dead : Bool

-- The batcher's state: past the subscribe burst, the open instant, its
-- values, its routes still open.
record Batching (A : Set) (N : Set) : Set where
  constructor batching
  field
    late   : Bool
    at     : N
    held   : List A
    routes : ℕ

private
  isTick : ∀ {A} → Tag A → Bool
  isTick tick = true
  isTick _    = false

  isLane : Part → Bool
  isLane lanePart  = true
  isLane burstPart = false

  isZero : ℕ → Bool
  isZero zero    = true
  isZero (suc _) = false

  ext : ∀ {X : Set} {Γ Δ : List Set} → (∀ {Y} → Y ∈ Γ → Y ∈ Δ) → ∀ {Y} → Y ∈ X ∷ Γ → Y ∈ X ∷ Δ
  ext ρ (here p)  = here p
  ext ρ (there i) = there (ρ i)

module Elaborate {C : Set → Set₁} {N : Set} (_≟_ : DecidableEquality N) (name : N) (mint : C N) where

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
  -- The leaves and the one-to-one formers

  phase : ∀ {A} → Bool × Tag A → Tag A → Bool × Tag A
  phase (late , _) t = (late ∨ isTick t) , t

  -- An async step mints its instant's name and sends `begin` first; a
  -- value's step ends in `over`, a completion's is carried on by the
  -- completion itself.
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

  -- The lane, gated to its own part, under its subject.
  laneˢ : ∀ {Θ B} → E Θ (IE B) → E Θ (IE B)
  laneˢ x = flatMap (mergeᶠ nothing)
    (λ k → connect (flatMap (mergeᶠ nothing) (λ _ → x) (takeWhile false isLane (of (k ∷ [])))) (framed k))
    (of (lanePart ∷ burstPart ∷ []))
  {-# INLINE laneˢ #-}

  Out : Set → Set
  Out B = Flat × List (IE B)

  -- How the flatMap takes an outer value.
  arrive : FlatOp → Flat → Flat
  arrive (mergeᶠ (just k)) s with Flat.active s <ᵇ k
  ... | true  = s
  ... | false = record s { queue = suc (Flat.queue s) }
  arrive (mergeᶠ nothing) s = s
  arrive switchᶠ          s = record s { active = 0 }
  arrive exhaustᶠ         s = s

  stopUnless : ∀ {B} → Bool → N → Flat → Out B
  stopUnless true  n s = s , []
  stopUnless false n s = s , instEmit (mark stop) n ∷ []

  -- A lane ended outside a bracket, and the route through it with it:
  -- handed to the queued lane rxjs subscribes next, carried on by the
  -- flatMap's own completion, or stopped here.
  verdict : ∀ {B} → N → Flat → Out B
  verdict n s with isZero (Flat.queue s)
  ... | false = record s { handoff = true } , []
  ... | true  = stopUnless (Flat.finished s ∧ isZero (Flat.active s)) n (record s { handoff = false })

  settle : ∀ {B} → Bool → N → Flat → Out B
  settle true  n s = s , []
  settle false n s = verdict n s

  -- A handed-off lane's burst is over: the route stops here if it lives.
  burstOver : ∀ {B} → Bool → N → Flat → Out B
  burstOver true  n s = record s { handoff = false } , instEmit (mark stop) n ∷ []
  burstOver false n s = s , []

  onMark : ∀ {B} → FlatOp → Flat → Mark → N → Out B
  onMark op s outerOpen  n = arrive op (record s { bracket = true }) , []
  onMark op s outerClose n = record s { bracket = false } , []
  onMark op s laneStart  n =
    record s { active = suc (Flat.active s)
             ; queue = if Flat.popping s then Flat.queue s ∸ 1 else Flat.queue s
             ; popping = false ; dead = false } , []
  onMark op s laneDone   n =
    settle (Flat.bracket s) n
      (record s { active = Flat.active s ∸ 1 ; popping = not (isZero (Flat.queue s)) ; dead = true })
  onMark op s burstEnd   n = burstOver (Flat.handoff s ∧ not (Flat.dead s)) n s
  onMark op s outerDone  n =
    stopUnless (Flat.bracket s ∨ Flat.handoff s ∨ (isZero (Flat.queue s) ∧ isZero (Flat.active s))) n
      (record s { finished = true })
  onMark op s stop       n = stopUnless (Flat.bracket s ∨ Flat.handoff s) n s
  onMark op s m          n = s , instEmit (mark m) n ∷ []

  react : ∀ {B} → FlatOp → Out B → IE B → Out B
  react op (s , _) (instEmit (value b) n) = s , instEmit (value b) n ∷ []
  react op (s , _) (instEmit (mark m) n)  = onMark op s m n

  branch : ∀ {Δ A B} → Branch → E (IE B ∷ IE B ∷ IE A ∷ Δ) (IE B)
  branch outerB = map opening (connected (there (there (here refl))))
  branch laneB  = connected (here refl)
  branch closeB = connected (there (here refl))

  combined : ∀ {Δ A B} → FlatOp → E (IE B ∷ IE B ∷ IE A ∷ Δ) (IE B)
  combined op = each proj₂
    (scan (react op) (flat 0 0 false false false false false , [])
      (flatMap (mergeᶠ nothing) branch (of (outerB ∷ laneB ∷ closeB ∷ []))))

  -- The outer `O` is read first by the scan, then by the real flatMap,
  -- then by `closer`: the order the nested connects subscribe them in.
  flatMapˢ : ∀ {Δ A B} → FlatOp → (A → E (IE B ∷ IE A ∷ Δ) (IE B)) → E Δ (IE A) → E Δ (IE B)
  flatMapˢ op g s =
    connect s (connect closer
      (connect (flatMap op (λ a → laneˢ (g a)) (each valuesOf (connected (there (here refl))))) (combined op)))
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
    elab : ∀ {Γ Δ A} → (∀ {X} → X ∈ L.map IE Γ → X ∈ Δ) → Obs C Γ A → E Δ (IE A)
    elab ρ (cold c)          = coldˢ c
    elab ρ empty             = empty
    elab ρ (of xs)           = ofˢ xs
    elab ρ (map f s)         = mapˢ f (elab ρ s)
    elab ρ (scan f z s)      = scanˢ f z (elab ρ s)
    elab ρ (takeWhile i p s) = takeWhileˢ i p (elab ρ s)
    elab ρ (flatMap op f s)  = flatMapˢ op (λ a → elab (λ i → there (there (ρ i))) (f a)) (elab ρ s)
    elab ρ (connect s b)     = connect (elab ρ s) (elab (ext ρ) b)
    elab ρ (connected i)     = connected (ρ (∈-map⁺ IE i))
    elab ρ (defer l)         = defer (elabˡ ρ l)

    elabˡ : ∀ {Γ Δ A} → (∀ {X} → X ∈ L.map IE Γ → X ∈ Δ) → Later C Γ A → Later C Δ (IE A)
    elabˡ ρ l .Later.force = elab ρ (Later.force l)

  -- Every emit under the name of the last `begin` before it.
  restamp : ∀ {A} → N × IE A → IE A → N × IE A
  restamp (n , _) (instEmit (mark begin) m) = m , instEmit (mark begin) m
  restamp (n , _) (instEmit ev _)           = n , instEmit ev n

  -- The run, then the end of its subscribe burst, then its completion,
  -- each told by a mark: a batcher reads the elaborated program as the
  -- source of its own scan, subscribed where the program alone would be,
  -- so the names it mints are the program's own.
  elaborate : ∀ {Γ A} → Obs C Γ A → E (L.map IE Γ) (IE A)
  elaborate o = map proj₂ (scan restamp (name , marked begin)
    (concatˢ (merge (elab (λ i → i) o) (of (marked subscribed ∷ []))) (of (marked completed ∷ []))))

  ------------------------------------------------------------------------
  -- The batcher

  private
    Step : Set → Set
    Step A = Batching A N × List (IE (List A))

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

  -- The subscribe burst is one batch, released when it is over; after
  -- it, an instant's batch is released when its routes are.  The run is
  -- read as the scan's source, so it is subscribed where it would be
  -- alone.
  batchSimultaneous : ∀ {Γ A} → E Γ (IE A) → E Γ (IE (List A))
  batchSimultaneous s = each proj₂ (scan bstep (batching false name [] 0 , []) s)
