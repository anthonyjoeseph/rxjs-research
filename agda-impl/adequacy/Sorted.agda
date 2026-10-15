{-# OPTIONS --guardedness --large-indices #-}

-- SORTEDNESS: the machine shows the root its values at positions that
-- never fall.  A fact about the machine alone; no meaning is consulted.
--
-- The position is SCOPED (`operation.AbstractObservable`'s `under`): it
-- is always the path of labels the run is under, put back when a scope
-- returns.  So the order of the run's positions is the pre-order of a
-- tree, and sortedness splits three ways.  THE WALK, once: a run that
-- enters each scope's children in increasing label order, and delivers
-- nothing at a position after entering one of its children, is sorted.
-- THE PROTOCOL, one kernel at a time: each kernel is well-positioned
-- (`Well`), given that the observer it delivers to is.  THE TIMERS: a
-- turn opens a fresh cascade past every position the run has shown.
--
-- `Well` is UNARY: it relates a computation to positions, never to a
-- meaning, so a kernel's case reads only the kernel.
module adequacy.Sorted where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (suc)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Maybe using (maybe)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Level using (Lift; lift)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Tree as T
open import Tree using (Obs)
open import denotation.MonotonicList using (Pos; ix; root; _<ᵖ_; Timeline)
open import operation.AbstractObservable using (module Run; module Heap) renaming (module Machine to Shared)
open import operation.PureObservable using (PureObs; Pureᴾ; Out; note; fin; module Pure)
open Heap using (World; _⊑_; same; Sink; Handle)
open import operation.Machine using (module Machine)

------------------------------------------------------------------------
-- The order, reflexive

_≤ᵖ_ : Pos → Pos → Set
p ≤ᵖ q = p ≡ q ⊎ p <ᵖ q ≡ true

-- `q` is `p`, or under it.
Under : Pos → Pos → Set
Under p q = Σ Pos λ y → q ≡ p ++ y

-- Where a scope at `p` may leave the last delivery, starting from `lo`:
-- no earlier, and nowhere outside `p`'s subtree but `lo` itself.
Settled : Pos → Pos → Pos → Set
Settled p lo lo′ = lo ≤ᵖ lo′ × (lo ≡ lo′ ⊎ Under p lo′)

module Sorting (R : Set) where
  open Machine R using (Mach; mach; Playing; Step; silent; value; complete; drained; step; trace; shown; begin; launch; reading; Read)
  open Shared Timeline (Out R) using (Conf; ⟨_,_,_⟩; Ctl; run; ret; held; asking; Stack; bottom; push; Wait; rest; back; rehold; told
                                     ; Heapᴹ; Callbacks; cbs)
  open Run (Pureᴾ R) using (Act; Ref; El; done; newRef; readRef; writeRef; register; send; finish; startCold; stop; eff; here; under; diverge; unfold
                           ; Observer; Subscription; Subscribe; Kont; Env; Subject; wkEnv; compile; emptyᴷ; ofᴷ; mapᴷ; scanᴷ; takeWhileᴷ; flatMapᴷ; connectᴷ; joinᴷ; via)
  open Pure R using (Timer; cascade; recorder)
  open Read

  ----------------------------------------------------------------------
  -- What is claimed: the root's values at positions that never fall

  mutual
    record Rising (lo : Pos) (m : Mach) : Set₁ where
      coinductive
      field rises : RisingStep lo (step m)

    data RisingStep (lo : Pos) : Step → Set₁ where
      silentʳ   : ∀ {m} → Rising lo m → RisingStep lo (silent m)
      valueʳ    : ∀ {t p a m} → lo ≤ᵖ p → Rising p m → RisingStep lo (value t p a m)
      completeʳ : ∀ {p} → lo ≤ᵖ p → RisingStep lo (complete p)
      drainedʳ  : RisingStep lo drained

  data Ascending (lo : Pos) : List Pos → Set where
    []ᵃ  : Ascending lo []
    _∷ᵃ_ : ∀ {p ps} → lo ≤ᵖ p → Ascending p ps → Ascending lo (p ∷ ps)

  -- A rising run's record is ascending, however far it is read.
  mutual
    ascending : ∀ {lo m} → Rising lo m → ∀ n c → Ascending lo (marks (reading n c (trace m)))
    ascending r 0       c = []ᵃ
    ascending r (suc n) c = ascendingˢ (Rising.rises r) n c

    ascendingˢ : ∀ {lo s} → RisingStep lo s → ∀ n c → Ascending lo (marks (reading (suc n) c (shown s)))
    ascendingˢ (silentʳ r)     n c = ascending r n _
    ascendingˢ (valueʳ le r)   n c = le ∷ᵃ ascending r n _
    ascendingˢ (completeʳ le)  n c = le ∷ᵃ []ᵃ
    ascendingˢ drainedʳ        n c = []ᵃ

  ----------------------------------------------------------------------
  -- THE PROTOCOL: a computation well-positioned

  -- `Well p lo m`: run at position `p`, the last delivery at `lo`, `m`
  -- delivers at no position before the last, and every scope it opens
  -- leaves the last delivery `Settled` in it.  A delivery is the root's
  -- record, or an observer's callback run; an observer's callbacks are
  -- well wherever they are called no earlier than the last delivery.
  mutual
    data Well {w B} (p lo : Pos) : Act w B → Set₁ where
      doneʷ     : ∀ {b} → Well p lo (done b)
      newRefʷ   : ∀ {t a} {k : ∀ {v} → w ⊑ v → Ref v t → Act v B} → (∀ {v} (σ : w ⊑ v) r → Well p lo (k σ r)) → Well p lo (newRef t a k)
      readRefʷ  : ∀ {t} {r : Ref w t} {k : ∀ {v} → w ⊑ v → El v t → Act v B} → (∀ {v} (σ : w ⊑ v) a → Well p lo (k σ a)) → Well p lo (readRef {t = t} r k)
      writeRefʷ : ∀ {t} {r : Ref w t} {a : El w t} {k : Act w B} → Well p lo k → Well p lo (writeRef {t = t} r a k)
      registerʷ : ∀ {A} {n : A → Act w ⊤} {c : Act w ⊤} {x : Act w Bool} {k : ∀ {v} → w ⊑ v → Sink v A → Act v B} → WellObs (record { next = n ; complete = c ; closed = x })
                → (∀ {v} (σ : w ⊑ v) s → Well p lo (k σ s)) → Well p lo (register n c x k)
      sendʷ     : ∀ {A} {s : Sink w A} {a : A} {k : Act w B} → lo ≤ᵖ p → (∀ lo′ → Settled p lo lo′ → Well p lo′ k) → Well p lo (send s a k)
      finishʷ   : ∀ {A} {s : Sink w A} {k : Act w B} → lo ≤ᵖ p → (∀ lo′ → Settled p lo lo′ → Well p lo′ k) → Well p lo (finish {A = A} s k)
      startColdʷ : ∀ {A} {c : Timeline A} {s : Sink w A} {k : ∀ {v} → w ⊑ v → Handle v → Act v B} → lo ≤ᵖ p → (∀ lo′ → Settled p lo lo′ → ∀ {v} (σ : w ⊑ v) h → Well p lo′ (k σ h))
                 → Well p lo (startCold {A = A} c s k)
      stopʷ     : ∀ {h : Handle w} {k : Act w B} → Well p lo k → Well p lo (stop h k)
      noteʷ     : ∀ {a} {k : ⊤ → Act w B} → lo ≤ᵖ p → Well p p (k _) → Well p lo (eff (note a) k)
      finʷ      : ∀ {k : ⊤ → Act w B} → lo ≤ᵖ p → Well p lo (eff fin k)
      hereʷ     : ∀ {k : Pos → Act w B} → Well p lo (k p) → Well p lo (here k)
      underʷ    : ∀ {l} {m : Act w ⊤} {k : Act w B} → Well (p ++ [ l ]) lo m → (∀ lo′ → Settled (p ++ [ l ]) lo lo′ → Well p lo′ k) → Well p lo (under l m k)
      divergeʷ  : Well p lo diverge
      unfoldʷ   : ∀ {Γ A} {l : T.Later Timeline Γ A} {e : Env Γ w} {n : A → Act w ⊤} {c : Act w ⊤} {x : Act w Bool}
                    {k : ∀ {v} → w ⊑ v → Sink v ⊤ → Act v ⊤} {m : Act w B} → WellEnv {Γ} e → WellObs {A} (record { next = n ; complete = c ; closed = x })
                → (∀ lo′ → Settled (p ++ [ ix 1 ]) lo lo′ → Well p lo′ m) → Well p lo (unfold l e n c x k m)

    -- An observer: each callback well wherever it is called no earlier
    -- than the last delivery.  Asking whether it is closed delivers nothing.
    WellObs : ∀ {A w} → Observer A w → Set₁
    WellObs o = (∀ a q lo → lo ≤ᵖ q → Well q lo (Observer.next o a))
              × (∀ q lo → lo ≤ᵖ q → Well q lo (Observer.complete o))
              × (∀ q lo → Well q lo (Observer.closed o))

    -- The connects in scope: each subject's joins well.
    WellEnv : ∀ {Γ w} → Env Γ w → Set₁
    WellEnv e = Lift _ ⊤

  -- A continuation places nothing: well wherever it runs.
  WellKont : ∀ {w} → Kont w → Set₁
  WellKont {w} k = ∀ {v} (σ : w ⊑ v) (sub : Subscription v) p lo → Well p lo (k σ sub)

  -- A subscription: subscribed fresh, with a well observer and a
  -- continuation that places nothing, it is well.
  WellSub : ∀ {A w} → Subscribe A w → Set₁
  WellSub {A} {w} s = ∀ {v} (ρ : w ⊑ v) (o : Observer A v) (k : Kont v) p lo → lo ≤ᵖ p → WellObs o → WellKont k → Well p lo (s ρ o k)

  postulate
    -- THE PROTOCOL, ONE KERNEL AT A TIME.
    emptyᴷ-well     : ∀ {A w} → WellSub (emptyᴷ {A} {w})
    ofᴷ-well        : ∀ {A w} xs → WellSub (ofᴷ {A} {w} xs)
    coldᴷ-well      : ∀ {A w} c → WellSub (via {A} {w} (startCold c))
    mapᴷ-well       : ∀ {A B w} f {s : Subscribe A w} → WellSub {A} {w} s → WellSub (mapᴷ {A} {B} f s)
    scanᴷ-well      : ∀ {A B w} f z {s : Subscribe A w} → WellSub {A} {w} s → WellSub (scanᴷ {A} {B} f z s)
    -- The risk of the protocol: a `takeWhile` completing under `last`
    -- after its value went down, where the observer below may have
    -- completed under the same `last` already.  Only that observer
    -- being closed keeps the second completion from delivering, so
    -- `Settled` may need to know what the heap's flags say.
    takeWhileᴷ-well : ∀ {A w} i p {s : Subscribe A w} → WellSub {A} {w} s → WellSub (takeWhileᴷ i p s)
    flatMapᴷ-well   : ∀ {A B w} op {f : A → Subscribe B w} {s : Subscribe A w} → (∀ a → WellSub {B} {w} (f a)) → WellSub {A} {w} s → WellSub (flatMapᴷ op f s)
    connectᴷ-well   : ∀ {A B w} {s : Subscribe A w} {b : ∀ {v} → w ⊑ v → Subject A v → Subscribe B v} → WellSub {A} {w} s → (∀ {v} σ st → WellSub {B} {v} (b σ st)) → WellSub (connectᴷ s b)
    joinᴷ-well      : ∀ {A w} st → WellSub (joinᴷ {A} {w} st)

  -- Every compiled tree well, kernel by kernel.
  compile-well : ∀ {Γ A w} (o : Obs _ Γ A) (e : Env Γ w) → WellEnv e → WellSub (compile o e)
  compile-well (T.cold c)          e we = coldᴷ-well c
  compile-well T.empty             e we = emptyᴷ-well
  compile-well (T.of xs)           e we = ofᴷ-well xs
  compile-well (T.map f s)         e we = mapᴷ-well f (compile-well s e we)
  compile-well (T.scan f z s)      e we = scanᴷ-well f z (compile-well s e we)
  compile-well (T.takeWhile i p s) e we = takeWhileᴷ-well i p (compile-well s e we)
  compile-well (T.flatMap op f s)  e we = flatMapᴷ-well op (λ a → compile-well (f a) e we) (compile-well s e we)
  compile-well (T.connect s b)     e we = connectᴷ-well (compile-well s e we) λ σ st → compile-well b (st ∷ wkEnv σ e) (lift tt)
  compile-well (T.connected i)     e we = joinᴷ-well _
  compile-well (T.defer l)         e we = λ ρ o k p lo le wo wk → unfoldʷ (lift tt) wo λ lo′ st → doneʷ

  ----------------------------------------------------------------------
  -- THE WALK: a well configuration rises

  -- What waits on the stack, well: each continuation well where it
  -- resumes, given the last delivery no later than there.
  data WellStack (p : Pos) : ∀ {w X} → Stack w X → Set₁ where
    bottomʷ : ∀ {w} → WellStack p (bottom {w})
    restʷ   : ∀ {u w B} {m : Act w B} {ρ : u ⊑ w} {k : Stack u B} → (∀ lo → lo ≤ᵖ p → Well p lo m) → WellStack p k → WellStack p (push (rest m) ρ k)
    backʷ   : ∀ {u w B} q {m : Act w B} {ρ : u ⊑ w} {k : Stack u B} → (∀ lo → lo ≤ᵖ q → Well q lo m) → WellStack q k → WellStack p (push (back q m) ρ k)
    reholdʷ : ∀ {u w} {ρ : u ⊑ w} {k : Stack u ⊤} → WellStack p k → WellStack p (push rehold ρ k)
    toldʷ   : ∀ {u w} {ρ : u ⊑ w} {k : Stack u ⊤} → WellStack p k → WellStack p (push told ρ k)

  -- What runs next, well at the configuration's position.
  data WellCtl {h : World} (lo p : Pos) : Ctl h → Set₁ where
    runʷ    : ∀ {w B a} {σ : w ⊑ h} {k : Stack w B} → Well p lo a → WellStack p k → WellCtl lo p (run a σ k)
    retʷ    : ∀ {w X x} {σ : w ⊑ h} {k : Stack w X} → WellStack p k → WellCtl lo p (ret x σ k)
    heldʷ   : ∀ {w} {σ : w ⊑ h} {k : Stack w ⊤} → WellStack p k → WellCtl lo p (held σ k)
    askingʷ : ∀ {w X B e k′} {σ : w ⊑ h} {k : Stack w B} → (∀ x → Well p p (k′ x)) → WellStack p k → WellCtl lo p (asking {X = X} e k′ σ k)

  -- Every observer the heap holds, well.
  WellHeap : ∀ {h} → Heapᴹ h → Set₁
  WellHeap {h} hp = ∀ {A} (s : _) → WellObs {A} {h} (record { next = Callbacks.onNext (cbs hp s) ; complete = Callbacks.onComplete (cbs hp s)
                                                           ; closed = Callbacks.isClosed (cbs hp s) })

  -- The run well: the running computation and every frame waiting on
  -- the stack, every callback the heap holds, every burst playing past
  -- every position shown.
  record WellRun (lo : Pos) (m : Mach) : Set₁ where
    field
      ctl    : WellCtl lo (Conf.pos (Mach.conf m)) (Conf.ctl (Mach.conf m))
      heap   : WellHeap (Conf.heap (Mach.conf m))
      bursts : All (maybe (λ b → lo ≤ᵖ Playing.under′ b) (Lift _ ⊤)) (Mach.bursts m)

  -- One timer pops before another: its cascade is the earlier, so two
  -- due on one tick pop in the order of the positions they were set at.
  Before : ∀ {h} → Timer h → Timer h → Set
  Before tm t′ = cascade tm <ᵖ cascade t′ ≡ true

  -- The queue well: every timer past every position shown, and in the
  -- order they pop.
  record WellQueue (lo : Pos) (m : Mach) : Set₁ where
    field
      timers : All (λ tm → lo <ᵖ cascade tm ≡ true) (Mach.timers m)
      queued : AllPairs Before (Mach.timers m)

  record WellMach (lo : Pos) (m : Mach) : Set₁ where
    field
      going : WellRun lo m
      queue : WellQueue lo m

  -- One step, its next configuration `P` and never earlier.
  data StepBy (P : Pos → Mach → Set₁) (lo : Pos) : Step → Set₁ where
    silentʷ   : ∀ {m} → P lo m → StepBy P lo (silent m)
    valueʷ    : ∀ {t p a m} → lo ≤ᵖ p → P p m → StepBy P lo (value t p a m)
    completeʷ : ∀ {p} → lo ≤ᵖ p → StepBy P lo (complete p)
    drainedʷ  : StepBy P lo drained

  WellStep : Pos → Step → Set₁
  WellStep = StepBy WellMach

  joinʷ : ∀ {lo s} → StepBy WellRun lo s → StepBy WellQueue lo s → WellStep lo s
  joinʷ (silentʷ r)     (silentʷ q)     = silentʷ (record { going = r ; queue = q })
  joinʷ (valueʷ le r)   (valueʷ _ q)    = valueʷ le (record { going = r ; queue = q })
  joinʷ (completeʷ le)  (completeʷ _)   = completeʷ le
  joinʷ drainedʷ        drainedʷ        = drainedʷ

  -- The loop's turn: held, nothing playing, so the next step pops a timer.
  idle : Mach → Bool
  idle m with Conf.ctl (Mach.conf m) | Mach.bursts m
  ... | held _ _ | [] = true
  ... | _        | _  = false

  postulate
    -- THE TREE WALK: a step that is not the loop's turn runs the
    -- computation, or plays a burst, at the configuration's position;
    -- the protocol's indices carry the last delivery, so the run stays
    -- well and a value shown is no earlier than the last.
    walk-tree : ∀ {lo m} → WellMach lo m → idle m ≡ false → StepBy WellRun lo (step m)

    -- THE TIMERS: a step that is not the loop's turn shows values only
    -- under the playing burst's cascade, so every timer queued stays past
    -- them; a timer it sets is queued at its due tick after every timer
    -- set earlier on that tick.
    walk-timers : ∀ {lo m} → WellMach lo m → idle m ≡ false → StepBy WellQueue lo (step m)

    -- THE LOOP'S TURN: the earliest timer popped, its frame played from
    -- its cascade, which every other timer is past.
    turn : ∀ {lo m} → WellMach lo m → idle m ≡ true → WellStep lo (step m)

  walk : ∀ {lo m} → WellMach lo m → idle m ≡ false → WellStep lo (step m)
  walk w b = joinʷ (walk-tree w b) (walk-timers w b)

  -- The machine's fundamental lemma: a well configuration's step keeps
  -- it well, and a value it shows is no earlier than the last.
  preserve : ∀ {lo m} → WellMach lo m → WellStep lo (step m)
  preserve {m = m} w with idle m in eq
  ... | true  = turn w eq
  ... | false = walk w eq

  -- The recorder is well: a value or completion at no earlier a position.
  recorder-well : WellObs recorder
  recorder-well = (λ a q lo le → noteʷ le doneʷ) , (λ q lo le → finʷ le) , (λ q lo → doneʷ)

  -- The run begins well: the program compiled at the root, the recorder
  -- its observer, nothing on the heap, queued or playing.
  begin-well : (o : PureObs [] R) → WellMach root (begin o)
  begin-well o = record
    { going = record { ctl    = runʷ (compile-well o [] (lift tt) same recorder _ root root (inj₁ refl) recorder-well (λ σ sub p lo → doneʷ)) bottomʷ
                     ; heap   = λ ()
                     ; bursts = [] }
    ; queue = record { timers = [] ; queued = AllPairs.[] } }

  mutual
    rising : ∀ {lo m} → WellMach lo m → Rising lo m
    rising w .Rising.rises = risingˢ (preserve w)

    risingˢ : ∀ {lo s} → WellStep lo s → RisingStep lo s
    risingˢ (silentʷ w)     = silentʳ (rising w)
    risingˢ (valueʷ le w)   = valueʳ le (rising w)
    risingˢ (completeʷ le)  = completeʳ le
    risingˢ drainedʷ        = drainedʳ

  -- SORTEDNESS: the program's run rises from the root.
  sorted : (o : PureObs [] R) → Rising root (begin o)
  sorted o = rising (begin-well o)
