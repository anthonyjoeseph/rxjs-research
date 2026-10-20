{-# OPTIONS --guardedness --large-indices #-}

module adequacy.Sorted.Walk where

open import Data.Bool using (Bool; true; false; T)
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_; _<_; _≤_; _≤′_; ≤′-refl; ≤′-step; z<s)
open import Data.Nat.Properties using (m<m+n; m<n⇒0<n∸m; ≤ᵇ⇒≤; ≤⇒≤ᵇ; ≰⇒>; m≤n⇒m<n∨m≡n; <⇒<′)
open import Data.List using (List; []; _∷_; _++_; [_]; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe using (Maybe; maybe; just; nothing) renaming (map to mapMaybe)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to mapAll)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Level using (Lift; lift; lower)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

import Tree as T
open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Pos; From; done; quiet; at; emit; stall; close; From∞; ix; last; root; _<ᵖ_; <ᵖ-trans; <ᵖ-below; <ᵖ-part; <ᵖ-sub; <ᵖ-ix; Timeline) renaming (sub to subᴾ)
open import operation.AbstractObservable using (Ty; _⊗_; joins; fifo; gate; module Run; module Heap)
  renaming (base to baseᵗ; ref to refᵗ; sink to sinkᵗ; quiet to quietᵗ; list to listᵗ; maybe to maybeᵗ) renaming (module Machine to Shared)
open import operation.PureObservable using (PureObs; Pureᴾ; Out; note; fin; module Pure)
open import adequacy.Sorted using (Settled; Under; _≤ᵖ_; settled-next; settled-refl; settled-trans; ≤ᵖ-child; ≤ᵖ-trans; module Sorting)
open Heap using (World; _⊑_; _⨾_; _∋_; here; there; new; wk∋; cell; slot; hush; play; same; Sink; Quiet; Handle)
open import operation.Machine using (module Machine)

module SortingWalk (R : Set) where
  open Machine R using (Mach; mach; Playing; wkPlaying; Todo; resume; owing; starting; feed; Step; silent; value; complete; drained; step; trace; shown; begin; launch; reading; Read) renaming (play to playᴹ)
  open Shared Timeline (Out R) using (Conf; ⟨_,_,_⟩; go; Ctl; run; ret; held; asking; Stack; bottom; push; Wait; rest; back; rehold; told
                                     ; Heapᴹ; Callbacks; cbs; look; spent?; Val; Stored; get; put; store; extend; wkAll; wkVal; stored)
  open Run (Pureᴾ R) using (Act; Ref; El; wkEl; done; newRef; readRef; writeRef; register; send; finish; startCold; stop; stash; cancel; eff; here; under; diverge; unfold
                           ; Observer; Subscription; Subscribe; Kont; Env; Subject; wkEnv; wkR; compile; wkAct; wkObs; _>>=ᴬ_; _>>ᴬ_; module Kit; emptyᴷ; ofᴷ; mapᴷ; scanᴷ; takeWhileᴷ; flatMapᴷ; connectᴷ; joinᴷ; via; emitAll; wkSub; module FlatKit)
  open Pure R using (Timer; wkTimer; insert; cascade; recorder; mapList)
  open Kit using (Cut; wkCut; cut; guard; guarded; attach; when; skipᴬ; each; unsubscribeVia; readB; readF; modify; newCut)
  open FlatKit using (Flat; wkFlat; newFlat; module FlatMap)
  open Read
  open Sorting R using (Fits; Rising; RisingStep; Still; Well; WellEnv; WellObs; WellSub; cancelʷ; cancelˢ; coldᴷ-well; completeʳ; connectᴷ-well; divergeʷ; doneʷ; doneˢ; drainedʳ; emptyᴷ-well; finishʷ; finʷ; fits-wk; flatMapᴷ-well; hereʷ; joinᴷ-well; mapᴷ-well; newRefʷ; newRefˢ; noteʷ; ofᴷ-well; readRefʷ; readRefˢ; registerʷ; scanᴷ-well; sendʷ; silentʳ; startColdʷ; stashʷ; stopʷ; stopˢ; takeWhileᴷ-well; underʷ; unfoldʷ; valueʳ; wk-obs; wk-still; wk-well; writeRefʷ; writeRefˢ)

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
  compile-well (T.defer l)         e we = λ ρ o k p lo le wo wk → unfoldʷ (lift tt) wo (λ τ t → wk τ _ (cancelˢ doneˢ)) le λ lo′ st → doneʷ

  ----------------------------------------------------------------------
  -- THE WALK: a well configuration rises

  -- A level's burst, by position: playing from `c` at its `i`-th frame,
  -- or over, its completion owed or delivered.
  data Entry : Set where
    playing : Pos → ℕ → Entry
    over    : Entry

  entry : ∀ {h} → Maybe (Playing h) → Entry
  entry (just b) = playing (Playing.under′ b) (Playing.index b)
  entry nothing  = over

  -- What is owed, by position: a resume, or a completion there.
  due : ∀ {h} → Todo h → Maybe Pos
  due resume        = nothing
  due (owing _ _ e) = just e

  -- `q` is past `p` and everything under it.
  record Beyond (p q : Pos) : Set where
    constructor beyond
    field past : ∀ y → (p ++ y) <ᵖ q ≡ true
  open Beyond

  -- The epoch: the cascade the clock's tick opened.  The last delivery
  -- is no later than it, or in it.
  InEpoch : Pos → Pos → Set
  InEpoch E lo = lo ≤ᵖ E ⊎ Under E lo

  under-trans : ∀ {a b c} → Under a b → Under b c → Under a c
  under-trans {a} (y , refl) (z , refl) = y ++ z , ++-assoc a y z

  -- The last settled in a scope of the epoch stays in it.
  in-epoch : ∀ {E p lo lo′} → Under E p → Settled p lo lo′ → InEpoch E lo → InEpoch E lo′
  in-epoch u (_ , inj₁ refl) w = w
  in-epoch u (_ , inj₂ v)    _ = inj₂ (under-trans u v)

  -- The root's level in the epoch `E`, held over the bottom: the burst
  -- of the timer that opened it playing, its completion owed, delivered,
  -- its frames rescheduled, or nothing.
  data RootAt (E lo : Pos) : List Entry → List (Maybe Pos) → Set where
    playingʳ : ∀ {i} → lo ≤ᵖ (E ++ [ ix i ]) → RootAt E lo [ playing E i ] []
    owingʳ   : lo ≤ᵖ (E ++ [ last ]) → RootAt E lo [ over ] [ just (E ++ [ last ]) ]
    overʳ    : RootAt E lo [ over ] []
    resumeʳ  : RootAt E lo [] [ nothing ]
    idleʳ    : RootAt E lo [] []

  -- A cold's level, started at `P` over the levels `es`: its burst
  -- playing under `P`, its completion owed at `P ++ [ last ]`, delivered,
  -- or its frames on timers.
  data ColdAt (P lo : Pos) (es : List Entry) : List Entry → List (Maybe Pos) → Set where
    playingᶜ : ∀ {i} → lo ≤ᵖ (P ++ [ ix i ]) → ColdAt P lo es (playing P i ∷ es) []
    owingᶜ   : lo ≤ᵖ (P ++ [ last ]) → ColdAt P lo es (over ∷ es) [ just (P ++ [ last ]) ]
    overᶜ    : ColdAt P lo es (over ∷ es) []
    resumeᶜ  : ColdAt P lo es es [ nothing ]

  mutual
    -- What waits on the stack, well, in the epoch `E`.  `WellStack E p lo
    -- k es`: pushed at `p` with the last delivery at `lo`, `k` resumes
    -- well from wherever a scope at `p` may leave the last, as `Well`'s
    -- own continuations do; `es`, the bursts of the levels it holds.  A
    -- scope's frame puts back an enclosing position in the epoch.  A
    -- delivery's frames hand the turn back to the level that fed it, from
    -- wherever the delivery left the last.
    data WellStack (E p lo : Pos) : ∀ {w X} → Stack w X → List Entry → Set₁ where
      bottomʷ : ∀ {w} → WellStack E p lo (bottom {w}) []
      restʷ   : ∀ {u w B lo₀ es} {m : Act w B} {ρ : u ⊑ w} {k : Stack u B} → Under E p → Settled p lo₀ lo → (∀ lo′ → Settled p lo lo′ → Well p lo′ m)
              → WellStack E p lo₀ k es → WellStack E p lo (push (rest m) ρ k) es
      backʷ   : ∀ {u w B lo₀ es} q {m : Act w B} {ρ : u ⊑ w} {k : Stack u B} → Under E q → Under q p → Settled q lo₀ lo → (∀ lo′ → Settled p lo lo′ → Well q lo′ m)
              → WellStack E q lo₀ k es → WellStack E p lo (push (back q m) ρ k) es
      fedʷ    : ∀ {t u w es} P {ρ : u ⊑ w} {σ : t ⊑ u} {k : Stack t ⊤} → (∀ lo′ → Settled p lo lo′ → WellHeld E lo′ P k es [])
              → WellStack E p lo (push (back P (done tt)) ρ (push rehold σ k)) es

    -- What waits on a `Still` computation: it returns to the last exactly
    -- where it found it.  A cancel's frame, a still frame, the turn handed
    -- back after a delivery, or a poll's answer.
    data StillStack (E p lo : Pos) : ∀ {w X} → Stack w X → List Entry → Set₁ where
      stillRestʷ  : ∀ {u w B lo₀ es} {m : Act w B} {ρ : u ⊑ w} {k : Stack u B} → Under E p → Settled p lo₀ lo → Well p lo m → WellStack E p lo₀ k es
                  → StillStack E p lo (push (rest m) ρ k) es
      stillStillʷ : ∀ {u w B es} {m : Act w B} {ρ : u ⊑ w} {k : Stack u B} → Still m → StillStack E p lo k es → StillStack E p lo (push (rest m) ρ k) es
      reholdʷ     : ∀ {u w es} {ρ : u ⊑ w} {k : Stack u ⊤} → WellHeld E lo p k es [] → StillStack E p lo (push rehold ρ k) es
      toldʷ       : ∀ {u w c i es} {ρ : u ⊑ w} {k : Stack u ⊤} → WellHeld E lo p k (playing c i ∷ es) [] → StillStack E p lo (push told ρ k) (playing c i ∷ es)

    -- The driver's turn at `P`, well: over the bottom, the root's level;
    -- over a cold's frame, that cold's level, the last settled in `P`
    -- from where its frame was pushed.  `ts`: what is owed it.
    data WellHeld (E lo P : Pos) : ∀ {w} → Stack w ⊤ → List Entry → List (Maybe Pos) → Set₁ where
      rootʰ : ∀ {w es ts} → RootAt E lo es ts → WellHeld E lo P (bottom {w}) es ts
      coldʰ : ∀ {u w B lo₀ es₀ es ts} {m : Act w B} {ρ : u ⊑ w} {k : Stack u B} → Settled P lo₀ lo → WellStack E P lo₀ (push (rest m) ρ k) es₀
            → ColdAt P lo es₀ es ts → WellHeld E lo P (push (rest m) ρ k) es ts

  -- A cold's frame was pushed in the epoch.
  rest-under : ∀ {E P lo u w B es} {m : Act w B} {ρ : u ⊑ w} {k : Stack u B} → WellStack E P lo (push (rest m) ρ k) es → Under E P
  rest-under (restʷ u _ _ _) = u

  -- What runs next, well at the configuration's position, the last
  -- delivery settled from where the top frame was pushed.  A `Still`
  -- computation runs over a `StillStack`.  Nothing is owed but at the
  -- driver's turn.
  data WellCtl {h : World} (E lo p : Pos) : Ctl h → List Entry → List (Maybe Pos) → Set₁ where
    runʷ      : ∀ {w B a lo₀ es} {σ : w ⊑ h} {k : Stack w B} → Under E p → Settled p lo₀ lo → Well p lo a → WellStack E p lo₀ k es → WellCtl E lo p (run a σ k) es []
    retʷ      : ∀ {w X x lo₀ es} {σ : w ⊑ h} {k : Stack w X} → Settled p lo₀ lo → WellStack E p lo₀ k es → WellCtl E lo p (ret x σ k) es []
    stillʷ    : ∀ {w B a es} {σ : w ⊑ h} {k : Stack w B} → Still a → StillStack E p lo k es → WellCtl E lo p (run a σ k) es []
    stillRetʷ : ∀ {w X x es} {σ : w ⊑ h} {k : Stack w X} → StillStack E p lo k es → WellCtl E lo p (ret x σ k) es []
    heldʷ     : ∀ {w es ts} {σ : w ⊑ h} {k : Stack w ⊤} → WellHeld E lo p k es ts → WellCtl E lo p (held σ k) es ts
    notingʷ   : ∀ {w B a lo₀ es} {k′ : ⊤ → Act h B} {σ : w ⊑ h} {k : Stack w B} → Under E p → lo ≤ᵖ p → Settled p lo₀ lo → Well p p (k′ tt) → WellStack E p lo₀ k es
              → WellCtl E lo p (asking (note a) k′ σ k) es []
    finningʷ  : ∀ {w B es} {k′ : ⊤ → Act h B} {σ : w ⊑ h} {k : Stack w B} → lo ≤ᵖ p → WellCtl E lo p (asking fin k′ σ k) es []

  -- What an entry holds, well: a cell fitting the last delivery, a well
  -- observer's callbacks, a `Still` unsubscribe.
  WellVal : ∀ {w} → Pos → ∀ k → Val w k → Set₁
  WellVal lo (cell t) x  = Lift _ (Fits lo t (lower x))
  WellVal lo (slot A) cb = WellObs (record { next = Callbacks.onNext cb ; complete = Callbacks.onComplete cb ; closed = Callbacks.isClosed cb })
  WellVal lo hush m      = Still m
  WellVal lo play _      = Lift _ ⊤

  -- Every entry the heap holds well, as it was stored.
  record WellHeap {h} (lo : Pos) (hp : Heapᴹ h) : Set₁ where
    constructor heapʷ
    field holds : ∀ {k} (i : h ∋ k) → WellVal lo k (Stored.val (get hp i))
  open WellHeap

  -- One timer pops before another: its cascade, and everything under
  -- it, is before the other's.  So two due on one tick pop in the order
  -- of the positions they were set at.
  Before : ∀ {h} → Timer h → Timer h → Set
  Before tm t′ = Beyond (cascade tm) (cascade t′)

  -- A timer queued in the epoch `E`, the last at `lo`: its cascade past
  -- the epoch's, set no later than the last.
  Queued : Pos → Pos → ∀ {h} → Timer h → Set
  Queued E lo tm = Beyond E (cascade tm) × Timer.from tm ≤ᵖ lo

  -- The queue well: the epoch opened at the clock's tick, the last in
  -- it, every timer queued past it, in the order they pop.
  record WellQueue (E lo : Pos) (clock : ℕ) {h} (tms : List (Timer h)) : Set₁ where
    constructor queueʷ
    field
      opened : Σ Pos λ z → E ≡ ix clock ∷ z
      within : InEpoch E lo
      timers : All (Queued E lo) tms
      queued : AllPairs Before tms

  -- The machine well: what runs next and every frame waiting on the
  -- stack, every level's burst playing past the last, everything the
  -- heap holds, the root not yet complete, and the queue.
  record WellMach (lo : Pos) (m : Mach) : Set₁ where
    constructor wellʳ
    field
      {E}     : Pos
      {es}    : List Entry
      {ts}    : List (Maybe Pos)
      ctl     : WellCtl E lo (Conf.pos (Mach.conf m)) (Conf.ctl (Mach.conf m)) es ts
      entries : map entry (Mach.bursts m) ≡ es
      dues    : map due (Mach.todo m) ≡ ts
      heap    : WellHeap lo (Conf.heap (Mach.conf m))
      fresh   : Mach.ended m ≡ false
      queue   : WellQueue E lo (Mach.clock m) (Mach.timers m)

  -- One step, its next configuration well and never earlier.
  data WellStep (lo : Pos) : Step → Set₁ where
    silentʷ   : ∀ {m lo′} → lo ≤ᵖ lo′ → WellMach lo′ m → WellStep lo (silent m)
    valueʷ    : ∀ {t p a m} → lo ≤ᵖ p → WellMach p m → WellStep lo (value t p a m)
    completeʷ : ∀ {p} → lo ≤ᵖ p → WellStep lo (complete p)
    drainedʷ  : WellStep lo drained

  -- The loop's turn: held, nothing playing or owed, so the next step pops
  -- a timer.
  idle : Mach → Bool
  idle m with Conf.ctl (Mach.conf m) | Mach.bursts m | Mach.todo m
  ... | held _ _ | [] | [] = true
  ... | _        | _  | _  = false

  -- A cell's fit holds of any later last.
  fits-up : ∀ {w lo lo′} t {a : El w t} → lo ≤ᵖ lo′ → Fits lo t a → Fits lo′ t a
  fits-up (joins A)  le (ps , below) = ps , All-map le below
    where All-map : ∀ {lo lo′} → lo ≤ᵖ lo′ → ∀ {xs} → All (λ i → i <ᵖ lo ≡ true) xs → All (λ i → i <ᵖ lo′ ≡ true) xs
          All-map le []                 = []
          All-map (inj₁ refl) (x ∷ xs)  = x ∷ All-map (inj₁ refl) xs
          All-map {lo} {lo′} (inj₂ h) {i ∷ _} (x ∷ xs) = <ᵖ-trans i lo lo′ x h ∷ All-map (inj₂ h) xs
  fits-up (baseᵗ X)  le f = tt
  fits-up (refᵗ t)   le f = tt
  fits-up (sinkᵗ A)  le f = tt
  fits-up quietᵗ     le f = tt
  fits-up (listᵗ t)  le f = tt
  fits-up (maybeᵗ t) le f = tt
  fits-up (s ⊗ t)   le f = tt
  fits-up (fifo X)   le f = tt
  fits-up gate       le f = tt

  heap-up : ∀ {h lo lo′} {hp : Heapᴹ h} → lo ≤ᵖ lo′ → WellHeap lo hp → WellHeap lo′ hp
  heap-up le wh = heapʷ λ where
    {cell t} i → lift (fits-up t le (lower (holds wh i)))
    {slot A} i → holds wh i
    {hush}   i → holds wh i
    {play}   i → holds wh i

  -- The last at a delivery: settled there from any no later.
  settled-at : ∀ {p lo₀ lo} → Settled p lo₀ lo → lo ≤ᵖ p → Settled p lo₀ p
  settled-at {p} (a , _) le = ≤ᵖ-trans a le , inj₂ ([] , sym (++-identityʳ p))

  -- The machine's driver state weakened, by position unmoved.
  entries-wk : ∀ {h v} (ρ : h ⊑ v) (bs : List (Maybe (Playing h))) → map entry (mapList (mapMaybe (wkPlaying ρ)) bs) ≡ map entry bs
  entries-wk ρ []             = refl
  entries-wk ρ (just b ∷ bs)  = cong (_ ∷_) (entries-wk ρ bs)
  entries-wk ρ (nothing ∷ bs) = cong (_ ∷_) (entries-wk ρ bs)

  -- An entry well, weakened.
  val-wk : ∀ {w v lo} k (ρ : w ⊑ v) {x : Val w k} → WellVal lo k x → WellVal lo k (wkVal k ρ x)
  val-wk (cell t) ρ {x} f = lift (fits-wk _ t ρ (lower x) (lower f))
  val-wk (slot A) ρ wo    = wk-obs ρ wo
  val-wk hush     ρ s     = wk-still ρ s
  val-wk play     ρ _     = lift tt

  look-well : ∀ {h lo} {hp : Heapᴹ h} → WellHeap lo hp → ∀ {k} (i : h ∋ k) → WellVal lo k (look hp i)
  look-well {hp = hp} wh {k} i = val-wk k (Stored.into (get hp i)) (holds wh i)

  -- The heap grown, and written, well.
  wkAll-well : ∀ {h v w lo} (ρ : h ⊑ v) (xs : All (Stored h) w) → (∀ {k} (i : w ∋ k) → WellVal lo k (Stored.val (get xs i)))
             → ∀ {k} (i : w ∋ k) → WellVal lo k (Stored.val (get (wkAll ρ xs) i))
  wkAll-well ρ (stored x σ ∷ xs) wx here      = wx here
  wkAll-well ρ (stored x σ ∷ xs) wx (there i) = wkAll-well ρ xs (λ j → wx (there j)) i

  extend-well : ∀ {h lo k} {hp : Heapᴹ h} {x : Val (k ∷ h) k} → WellHeap lo hp → WellVal lo k x → WellHeap lo (extend hp x)
  extend-well {hp = hp} wh wx = heapʷ λ where
    here      → wx
    (there i) → wkAll-well new hp (holds wh) i

  put-well : ∀ {h w lo k} (xs : All (Stored h) w) (i : w ∋ k) {y : Stored h k} → WellVal lo k (Stored.val y) → (∀ {k′} (j : w ∋ k′) → WellVal lo k′ (Stored.val (get xs j)))
           → ∀ {k′} (j : w ∋ k′) → WellVal lo k′ (Stored.val (get (put xs i y) j))
  put-well (x ∷ xs) here      wy wx here      = wy
  put-well (x ∷ xs) here      wy wx (there j) = wx (there j)
  put-well (x ∷ xs) (there i) wy wx here      = wx here
  put-well (x ∷ xs) (there i) wy wx (there j) = put-well xs i wy (λ j′ → wx (there j′)) j

  store-well : ∀ {h lo k} {hp : Heapᴹ h} (i : h ∋ k) {x : Val h k} → WellHeap lo hp → WellVal lo k x → WellHeap lo (store hp i x)
  store-well {hp = hp} i wh wx = heapʷ (put-well hp i wx (holds wh))

  ≤ᵖ-< : ∀ {a b c} → a ≤ᵖ b → b <ᵖ c ≡ true → a <ᵖ c ≡ true
  ≤ᵖ-< (inj₁ refl) h = h
  ≤ᵖ-< {a} {b} {c} (inj₂ g) h = <ᵖ-trans a b c g h

  -- Ticks part in order.
  <ᵖ-ticks : ∀ {m n} → suc m ≤′ n → (ix m ∷ []) <ᵖ (ix n ∷ []) ≡ true
  <ᵖ-ticks {m} ≤′-refl         = <ᵖ-ix m
  <ᵖ-ticks {m} (≤′-step {n} h) = <ᵖ-trans (ix m ∷ []) (ix n ∷ []) (ix (suc n) ∷ []) (<ᵖ-ticks h) (<ᵖ-ix n)

  beyond-tick : ∀ {m n} z w → m < n → Beyond (ix m ∷ z) (ix n ∷ w)
  beyond-tick {m} {n} z w h = beyond λ y → <ᵖ-part [] {ix m} {ix n} (z ++ y) w (<ᵖ-ticks (<⇒<′ h))

  beyond-trans : ∀ {a b c} → Beyond a b → Beyond b c → Beyond a c
  beyond-trans {a} {b} {c} h₁ h₂ = beyond λ y → <ᵖ-trans (a ++ y) b c (past h₁ y) (subst (λ z → z <ᵖ c ≡ true) (++-identityʳ b) (past h₂ []))

  -- Of two timers, the one due first, or set first on one tick, pops
  -- first.
  pops-before : ∀ {h} (a b : Timer h) → Timer.due a ≤ Timer.due b → Timer.from a <ᵖ Timer.from b ≡ true → Before a b
  pops-before a b le h with m≤n⇒m<n∨m≡n le
  ... | inj₁ lt = beyond-tick _ _ lt
  ... | inj₂ eq rewrite eq = beyond λ y → <ᵖ-part (ix (Timer.due b) ∷ []) {subᴾ (Timer.from a)} {subᴾ (Timer.from b)} y [] (<ᵖ-sub (Timer.from a) (Timer.from b) h)

  all-insert : ∀ {h} {P : Timer h → Set} tm ts → P tm → All P ts → All P (insert tm ts)
  all-insert tm []        p []       = p ∷ []
  all-insert tm (t′ ∷ ts) p (q ∷ qs) with Timer.due t′ ≤ᵇ Timer.due tm
  ... | true  = q ∷ all-insert tm ts p qs
  ... | false = p ∷ q ∷ qs

  -- A timer set after every one queued is queued in the order they pop.
  insert-well : ∀ {h} tm (ts : List (Timer h)) → All (λ t → Timer.from t <ᵖ Timer.from tm ≡ true) ts → AllPairs Before ts → AllPairs Before (insert tm ts)
  insert-well tm []        []       AllPairs.[] = [] AllPairs.∷ AllPairs.[]
  insert-well tm (t′ ∷ ts) (f ∷ fs) (r AllPairs.∷ rs) with Timer.due t′ ≤ᵇ Timer.due tm in e
  ... | true  = all-insert tm ts (pops-before t′ tm (≤ᵇ⇒≤ _ _ (subst T (sym e) tt)) f) r AllPairs.∷ insert-well tm ts fs rs
  ... | false = (b ∷ mapAll (beyond-trans b) r) AllPairs.∷ r AllPairs.∷ rs
    where b = beyond-tick _ _ (≰⇒> λ (le : Timer.due t′ ≤ Timer.due tm) → subst T e (≤⇒≤ᵇ {Timer.due t′} {Timer.due tm} le))

  -- The queue weakened, by position unmoved.
  timers-wk : ∀ {E lo h v} (ρ : h ⊑ v) {tms : List (Timer h)} → All (Queued E lo) tms → All (Queued E lo) (mapList (wkTimer ρ) tms)
  timers-wk ρ []       = []
  timers-wk ρ (q ∷ qs) = q ∷ timers-wk ρ qs

  before-wk : ∀ {h v} (ρ : h ⊑ v) {tm : Timer h} {xs} → All (Before tm) xs → All (Before (wkTimer ρ tm)) (mapList (wkTimer ρ) xs)
  before-wk ρ []       = []
  before-wk ρ {tm} (b ∷ bs) = b ∷ before-wk ρ {tm} bs

  queued-wk : ∀ {h v} (ρ : h ⊑ v) {tms : List (Timer h)} → AllPairs Before tms → AllPairs Before (mapList (wkTimer ρ) tms)
  queued-wk ρ AllPairs.[]       = AllPairs.[]
  queued-wk ρ {x ∷ _} (r AllPairs.∷ rs) = before-wk ρ {x} r AllPairs.∷ queued-wk ρ rs

  queue-wk : ∀ {E lo cl h v} {tms : List (Timer h)} (ρ : h ⊑ v) → WellQueue E lo cl tms → WellQueue E lo cl (mapList (wkTimer ρ) tms)
  queue-wk ρ (queueʷ o w ts qs) = queueʷ o w (timers-wk ρ ts) (queued-wk ρ qs)

  -- The last moved on in the epoch: every timer still set no later.
  queue-up : ∀ {E lo lo′ cl h} {tms : List (Timer h)} → lo ≤ᵖ lo′ → InEpoch E lo′ → WellQueue E lo cl tms → WellQueue E lo′ cl tms
  queue-up le w (queueʷ o _ ts qs) = queueʷ o w (mapAll (λ (b , f) → b , ≤ᵖ-trans f le) ts) qs

  -- A timer set in the epoch past the last, due after the clock: queued
  -- after every timer due no later, the last moved on to where it was
  -- set.
  queue-set : ∀ {E lo cl h} {tms : List (Timer h)} (tm : Timer h) → cl < Timer.due tm → lo <ᵖ Timer.from tm ≡ true → Under E (Timer.from tm)
            → WellQueue E lo cl tms → WellQueue E (Timer.from tm) cl (insert tm tms)
  queue-set tm lt h u (queueʷ (z , refl) w ts qs) =
    queueʷ (z , refl) (inj₂ u) (all-insert tm _ (beyond-tick z _ lt , inj₁ refl) (mapAll (λ (b , f) → b , inj₂ (≤ᵖ-< f h)) ts))
           (insert-well tm _ (mapAll (λ (_ , f) → ≤ᵖ-< f h) ts) qs)

  -- Past an epoch, past the last in it.
  epoch-past : ∀ {E lo q} → InEpoch E lo → Beyond E q → lo <ᵖ q ≡ true
  epoch-past {E} {q = q} (inj₁ (inj₁ refl)) b = subst (λ z → z <ᵖ q ≡ true) (++-identityʳ E) (past b [])
  epoch-past {E} {lo} {q} (inj₁ (inj₂ l)) b = <ᵖ-trans lo E q l (subst (λ z → z <ᵖ q ≡ true) (++-identityʳ E) (past b []))
  epoch-past (inj₂ (y , refl)) b = past b y

  -- The timers after the first, queued past its cascade.
  popped : ∀ {E lo h} {t : Timer h} {xs : List (Timer h)} → All (Before t) xs → All (Queued E lo) xs → All (Queued (cascade t) lo) xs
  popped []       []             = []
  popped {E} {lo} {t = t} (r ∷ rs) ((_ , f) ∷ qs) = (r , f) ∷ popped {E} {lo} {t = t} rs qs

  -- A cold started at `p`: its first frame playing, or its completion
  -- owed, or its frames on timers, the last moved on to where they were
  -- set.
  started-well : ∀ {E lo h A} {hp : Heapᴹ h} {p u B es} {m : Act h B} {ρ : u ⊑ h} {k : Stack u B} {cl tm bu lg mk}
                 (s : Sink h A) (hd : Handle h) (f : From A 0) → lo ≤ᵖ p → WellStack E p lo (push (rest m) ρ k) es → map entry bu ≡ es → WellHeap lo hp
               → WellQueue E lo cl tm → WellStep lo (silent (starting (mach ⟨ hp , p , held same (push (rest m) ρ k) ⟩ cl tm bu [] lg false mk) s hd f))
  started-well s hd done            le ws eb wh wq = silentʷ (inj₁ refl) (wellʳ (heldʷ (coldʰ settled-refl ws (owingᶜ (≤ᵖ-child _ le)))) (cong (over ∷_) eb) refl wh refl wq)
  started-well s hd quiet           le ws eb wh wq = silentʷ (inj₁ refl) (wellʳ (heldʷ (coldʰ settled-refl ws resumeᶜ)) eb refl wh refl wq)
  started-well s hd (at zero _ b)   le ws eb wh wq = silentʷ (inj₁ refl) (wellʳ (heldʷ (coldʰ settled-refl ws (playingᶜ (≤ᵖ-child _ le)))) (cong (_ ∷_) eb) refl wh refl wq)
  started-well {hp = hp} {p = p} {cl = cl} s hd (at (suc t) _ b) le ws eb wh wq =
    silentʷ (≤ᵖ-child p le) (wellʳ (heldʷ (coldʰ (≤ᵖ-child p le , inj₂ ([ last ] , refl)) ws resumeᶜ)) eb refl (heap-up {hp = hp} (≤ᵖ-child p le) wh) refl
                                   (queue-set _ (m<m+n cl z<s) (≤ᵖ-< le (<ᵖ-below p [])) (under-trans (rest-under ws) ([ last ] , refl)) wq))

  -- A run step from a well computation.
  runs-run : ∀ {E lo lo₀ h} {hp : Heapᴹ h} {p w B es} {a : Act h B} {σ : w ⊑ h} {k : Stack w B} {cl tm bu lg mk}
           → Under E p → Settled p lo₀ lo → Well p lo a → WellStack E p lo₀ k es → map entry bu ≡ es → WellHeap lo hp → WellQueue E lo cl tm
           → WellStep lo (step (mach ⟨ hp , p , run a σ k ⟩ cl tm bu [] lg false mk))
  runs-run u st doneʷ ws eb wh wq = silentʷ (inj₁ refl) (wellʳ (retʷ st ws) eb refl wh refl wq)
  runs-run {lo = lo} {bu = bu} u st (newRefʷ {t} {a} f h) ws eb wh wq =
    silentʷ (inj₁ refl) (wellʳ (runʷ u st (h new here) ws) (trans (entries-wk new bu) eb) refl (extend-well wh (lift (fits-wk lo t new a f))) refl (queue-wk new wq))
  runs-run {hp = hp} u st (readRefʷ {r = r} h) ws eb wh wq = silentʷ (inj₁ refl) (wellʳ (runʷ u st (h same _ (lower (look-well {hp = hp} wh r))) ws) eb refl wh refl wq)
  runs-run {hp = hp} u st (writeRefʷ {r = r} lo′ st′ f wk) ws eb wh wq =
    silentʷ (proj₁ st′) (wellʳ (runʷ u (settled-trans st st′) wk ws) eb refl (store-well r (heap-up {hp = hp} (proj₁ st′) wh) (lift f)) refl
                               (queue-up (proj₁ st′) (in-epoch u st′ (WellQueue.within wq)) wq))
  runs-run {bu = bu} u st (registerʷ wo h) ws eb wh wq =
    silentʷ (inj₁ refl) (wellʳ (runʷ u st (h new here) ws) (trans (entries-wk new bu) eb) refl (extend-well wh (wk-obs new wo)) refl (queue-wk new wq))
  runs-run {lo = lo} {hp = hp} {p = p} u st (sendʷ {s = s} {a = a} le h) ws eb wh wq =
    silentʷ (inj₁ refl) (wellʳ (runʷ u settled-refl (proj₁ (look-well {hp = hp} wh s) a p lo le) (restʷ u st h ws)) eb refl wh refl wq)
  runs-run {lo = lo} {hp = hp} {p = p} u st (finishʷ {s = s} le h) ws eb wh wq =
    silentʷ (inj₁ refl) (wellʳ (runʷ u settled-refl (proj₁ (proj₂ (look-well {hp = hp} wh s)) p lo le) (restʷ u st h ws)) eb refl wh refl wq)
  runs-run {bu = bu} u st (startColdʷ {c = c} {s = s} le h) ws eb wh wq =
    started-well (wk∋ new s) here (lower c) le (restʷ u st (λ lo′ st′ → h lo′ st′ new here) ws) (trans (entries-wk new bu) eb) (extend-well wh (lift tt)) (queue-wk new wq)
  runs-run u st (stopʷ {h = hd} wk) ws eb wh wq = silentʷ (inj₁ refl) (wellʳ (runʷ u st wk ws) eb refl (store-well hd wh (lift tt)) refl wq)
  runs-run {bu = bu} u st (stashʷ sm h) ws eb wh wq =
    silentʷ (inj₁ refl) (wellʳ (runʷ u st (h new here) ws) (trans (entries-wk new bu) eb) refl (extend-well wh (wk-still new sm)) refl (queue-wk new wq))
  runs-run {hp = hp} u st (cancelʷ {t = t} wk) ws eb wh wq = silentʷ (inj₁ refl) (wellʳ (stillʷ (look-well {hp = hp} wh t) (stillRestʷ u st wk ws)) eb refl wh refl wq)
  runs-run u st (noteʷ le wk) ws eb wh wq = silentʷ (inj₁ refl) (wellʳ (notingʷ u le st wk ws) eb refl wh refl wq)
  runs-run u st (finʷ le) ws eb wh wq = silentʷ (inj₁ refl) (wellʳ (finningʷ le) eb refl wh refl wq)
  runs-run u st (hereʷ wk) ws eb wh wq = silentʷ (inj₁ refl) (wellʳ (runʷ u st wk ws) eb refl wh refl wq)
  runs-run {p = p} u st (underʷ {l = l} wm h) ws eb wh wq =
    silentʷ (inj₁ refl) (wellʳ (runʷ (under-trans u ([ l ] , refl)) settled-refl wm (backʷ p u ([ l ] , refl) st h ws)) eb refl wh refl wq)
  runs-run u st divergeʷ ws eb wh wq = silentʷ (inj₁ refl) (wellʳ (runʷ u st divergeʷ ws) eb refl wh refl wq)
  runs-run {p = p} u st (unfoldʷ {l = l} {e = e} we wo kp le h) ws eb wh wq =
    silentʷ (inj₁ refl) (wellʳ (runʷ u settled-refl (underʷ (compile-well (T.Later.force l) e (lift tt) same _ _ (p ++ [ ix 1 ]) _ (≤ᵖ-child p le) wo
                                                           λ σ′ sub us p′ lo′ → stashʷ us λ τ t → kp (σ′ ⨾ τ) t p′ lo′)
                                                   λ _ _ → doneʷ)
                                (restʷ u st h ws)) eb refl wh refl wq)

  -- A run step from a still computation.
  runs-still : ∀ {E lo h} {hp : Heapᴹ h} {p w B es} {a : Act h B} {σ : w ⊑ h} {k : Stack w B} {cl tm bu lg mk}
             → Still a → StillStack E p lo k es → map entry bu ≡ es → WellHeap lo hp → WellQueue E lo cl tm
             → WellStep lo (step (mach ⟨ hp , p , run a σ k ⟩ cl tm bu [] lg false mk))
  runs-still doneˢ ss eb wh wq = silentʷ (inj₁ refl) (wellʳ (stillRetʷ ss) eb refl wh refl wq)
  runs-still {lo = lo} {bu = bu} (newRefˢ {t} {a} f h) ss eb wh wq =
    silentʷ (inj₁ refl) (wellʳ (stillʷ (h new here) ss) (trans (entries-wk new bu) eb) refl (extend-well wh (lift (fits-wk lo t new a (f lo)))) refl (queue-wk new wq))
  runs-still (readRefˢ h) ss eb wh wq = silentʷ (inj₁ refl) (wellʳ (stillʷ (h same _) ss) eb refl wh refl wq)
  runs-still {lo = lo} (writeRefˢ {r = r} f k) ss eb wh wq = silentʷ (inj₁ refl) (wellʳ (stillʷ k ss) eb refl (store-well r wh (lift (f lo))) refl wq)
  runs-still {hp = hp} (cancelˢ {t = t} k) ss eb wh wq = silentʷ (inj₁ refl) (wellʳ (stillʷ (look-well {hp = hp} wh t) (stillStillʷ k ss)) eb refl wh refl wq)
  runs-still (stopˢ {h = hd} k) ss eb wh wq = silentʷ (inj₁ refl) (wellʳ (stillʷ k ss) eb refl (store-well hd wh (lift tt)) refl wq)

  runs-well : ∀ {lo h} {hp : Heapᴹ h} {p w B} {a : Act h B} {σ : w ⊑ h} {k : Stack w B} {cl tm bu td lg en mk}
            → WellMach lo (mach ⟨ hp , p , run a σ k ⟩ cl tm bu td lg en mk) → WellStep lo (step (mach ⟨ hp , p , run a σ k ⟩ cl tm bu td lg en mk))
  runs-well {td = []} (wellʳ (runʷ u st wa ws) eb refl wh refl wq) = runs-run u st wa ws eb wh wq
  runs-well {td = []} (wellʳ (stillʷ sa ss) eb refl wh refl wq)    = runs-still sa ss eb wh wq
  runs-well {td = _ ∷ _} (wellʳ (runʷ _ _ _ _) _ () _ _ _)
  runs-well {td = _ ∷ _} (wellʳ (stillʷ _ _) _ () _ _ _)

  -- Settled in a scope is settled in any enclosing one.
  settled-up : ∀ {q p lo lo′} → Under q p → Settled p lo lo′ → Settled q lo lo′
  settled-up         u            (a , inj₁ e)            = a , inj₁ e
  settled-up {q} (y , refl) (a , inj₂ (z , refl)) = a , inj₂ (y ++ z , ++-assoc q y z)

  ∷-tail : ∀ {x y : Entry} {xs ys : List Entry} → _≡_ {A = List Entry} (x ∷ xs) (y ∷ ys) → xs ≡ ys
  ∷-tail refl = refl

  -- A poll answered closed: the level's burst over, a resume owed.
  quit-well : ∀ {E lo P w c i es} {k : Stack w ⊤} → WellHeld E lo P k (playing c i ∷ es) [] → WellHeld E lo P k es [ nothing ]
  quit-well (rootʰ (playingʳ _))       = rootʰ resumeʳ
  quit-well (coldʰ st ws (playingᶜ _)) = coldʰ st ws resumeᶜ

  -- A return to a well stack.
  returns-run : ∀ {E lo lo₀ h} {hp : Heapᴹ h} {p w X es} {x : X} {σ : w ⊑ h} {k : Stack w X} {cl tm bu lg mk}
              → Settled p lo₀ lo → WellStack E p lo₀ k es → map entry bu ≡ es → WellHeap lo hp → WellQueue E lo cl tm
              → WellStep lo (step (mach ⟨ hp , p , ret x σ k ⟩ cl tm bu [] lg false mk))
  returns-run st bottomʷ eb wh wq = silentʷ (inj₁ refl) (wellʳ (heldʷ (rootʰ idleʳ)) eb refl wh refl wq)
  returns-run {lo = lo} {σ = σ} st (restʷ u st₁ h ws) eb wh wq = silentʷ (inj₁ refl) (wellʳ (runʷ u (settled-trans st₁ st) (wk-well σ (h lo st)) ws) eb refl wh refl wq)
  returns-run {lo = lo} {σ = σ} st (backʷ q uq u st₁ h ws) eb wh wq =
    silentʷ (inj₁ refl) (wellʳ (runʷ uq (settled-trans st₁ (settled-up u st)) (wk-well σ (h lo st)) ws) eb refl wh refl wq)
  returns-run {lo = lo} st (fedʷ P h) eb wh wq = silentʷ (inj₁ refl) (wellʳ (stillʷ doneˢ (reholdʷ (h lo st))) eb refl wh refl wq)

  -- A return to a still stack: the last where it was.
  returns-still : ∀ {E lo h} {hp : Heapᴹ h} {p w X es} {x : X} {σ : w ⊑ h} {k : Stack w X} {cl tm bu lg mk}
                → StillStack E p lo k es → map entry bu ≡ es → WellHeap lo hp → WellQueue E lo cl tm
                → WellStep lo (step (mach ⟨ hp , p , ret x σ k ⟩ cl tm bu [] lg false mk))
  returns-still {σ = σ} (stillRestʷ u st h ws) eb wh wq = silentʷ (inj₁ refl) (wellʳ (runʷ u st (wk-well σ h) ws) eb refl wh refl wq)
  returns-still {σ = σ} (stillStillʷ sm ss) eb wh wq = silentʷ (inj₁ refl) (wellʳ (stillʷ (wk-still σ sm) ss) eb refl wh refl wq)
  returns-still (reholdʷ wh′) eb wh wq = silentʷ (inj₁ refl) (wellʳ (heldʷ wh′) eb refl wh refl wq)
  returns-still {x = false} (toldʷ wh′) eb wh wq = silentʷ (inj₁ refl) (wellʳ (heldʷ wh′) eb refl wh refl wq)
  returns-still {x = true} {bu = b ∷ bu} (toldʷ wh′) eb wh wq = silentʷ (inj₁ refl) (wellʳ (heldʷ (quit-well wh′)) (∷-tail eb) refl wh refl wq)
  returns-still {x = true} {bu = []} (toldʷ wh′) () wh wq

  returns-well : ∀ {lo h} {hp : Heapᴹ h} {p w X} {x : X} {σ : w ⊑ h} {k : Stack w X} {cl tm bu td lg en mk}
               → WellMach lo (mach ⟨ hp , p , ret x σ k ⟩ cl tm bu td lg en mk) → WellStep lo (step (mach ⟨ hp , p , ret x σ k ⟩ cl tm bu td lg en mk))
  returns-well {td = []} (wellʳ (retʷ st ws) eb refl wh refl wq)  = returns-run st ws eb wh wq
  returns-well {td = []} (wellʳ (stillRetʷ ss) eb refl wh refl wq) = returns-still ss eb wh wq
  returns-well {td = _ ∷ _} (wellʳ (retʷ _ _) _ () _ _ _)
  returns-well {td = _ ∷ _} (wellʳ (stillRetʷ _) _ () _ _ _)

  ∷-head : ∀ {x y : Entry} {xs ys : List Entry} → _≡_ {A = List Entry} (x ∷ xs) (y ∷ ys) → x ≡ y
  ∷-head refl = refl

  -- At most one thing is owed.
  owed-once : ∀ {E lo P w es x y zs} {k : Stack w ⊤} → WellHeld E lo P k es (x ∷ y ∷ zs) → ⊥
  owed-once (rootʰ ())
  owed-once (coldʰ _ _ ())

  -- A resume paid: the level returns to the frame its cold was started
  -- from, or the root's turn comes round.
  paid-resume : ∀ {E lo h} {hp : Heapᴹ h} {p w es} {σ : w ⊑ h} {k : Stack w ⊤} {cl tm bu lg mk}
              → WellHeld E lo p k es [ nothing ] → map entry bu ≡ es → WellHeap lo hp → WellQueue E lo cl tm
              → WellStep lo (step (mach ⟨ hp , p , held σ k ⟩ cl tm bu (resume ∷ []) lg false mk))
  paid-resume (rootʰ resumeʳ)       eb wh wq = silentʷ (inj₁ refl) (wellʳ (heldʷ (rootʰ idleʳ)) eb refl wh refl wq)
  paid-resume (coldʰ st ws resumeᶜ) eb wh wq = returns-run st ws eb wh wq

  -- A completion paid: delivered at its position, the level's turn
  -- handed back from wherever it leaves the last, the burst over.
  paid-owing : ∀ {E lo h A} {hp : Heapᴹ h} {p w es e} {σ : w ⊑ h} {k : Stack w ⊤} {hd : Handle h} {s : Sink h A} {cl tm bu lg mk}
             → WellHeld E lo p k es [ just e ] → map entry bu ≡ es → WellHeap lo hp → WellQueue E lo cl tm
             → WellStep lo (step (mach ⟨ hp , p , held σ k ⟩ cl tm bu (owing hd s e ∷ []) lg false mk))
  paid-owing {lo = lo} {hp = hp} {p} {hd = hd} {s} (rootʰ (owingʳ le)) eb wh wq =
    silentʷ (inj₁ refl) (wellʳ (runʷ ([ last ] , refl) settled-refl (proj₁ (proj₂ (look-well wh s)) _ lo le) (fedʷ p λ lo′ st → rootʰ overʳ)) eb refl wh′ refl wq)
    where wh′ = store-well {hp = hp} hd wh (lift tt)
  paid-owing {lo = lo} {hp = hp} {p} {hd = hd} {s} (coldʰ st ws (owingᶜ le)) eb wh wq =
    silentʷ (inj₁ refl) (wellʳ (runʷ (under-trans (rest-under ws) ([ last ] , refl)) settled-refl (proj₁ (proj₂ (look-well wh s)) (p ++ [ last ]) lo le)
                                     (fedʷ p λ lo′ st′ → coldʰ (settled-trans st (settled-up ([ last ] , refl) st′)) ws overᶜ)) eb refl wh′ refl wq)
    where wh′ = store-well {hp = hp} hd wh (lift tt)

  paid-well : ∀ {lo h} {hp : Heapᴹ h} {p w} {σ : w ⊑ h} {k : Stack w ⊤} {cl tm bu t td lg en mk}
            → WellMach lo (mach ⟨ hp , p , held σ k ⟩ cl tm bu (t ∷ td) lg en mk) → WellStep lo (step (mach ⟨ hp , p , held σ k ⟩ cl tm bu (t ∷ td) lg en mk))
  paid-well {t = resume}        {td = []}    (wellʳ (heldʷ wh) eb refl wh′ refl wq) = paid-resume wh eb wh′ wq
  paid-well {t = owing hd s e} {td = []}    (wellʳ (heldʷ wh) eb refl wh′ refl wq) = paid-owing wh eb wh′ wq
  paid-well                     {td = _ ∷ _} (wellʳ (heldʷ wh) eb refl wh′ refl wq) = ⊥-elim (owed-once wh)

  -- The top level's burst over: the level returns, or the root's turn
  -- comes round.
  leave-well : ∀ {E lo h} {hp : Heapᴹ h} {p w x es} {σ : w ⊑ h} {k : Stack w ⊤} {cl tm bu lg mk}
             → WellHeld E lo p k (x ∷ es) [] → map entry bu ≡ es → WellHeap lo hp → WellQueue E lo cl tm
             → WellStep lo (silent (feed (mach ⟨ hp , p , held σ k ⟩ cl tm bu [] lg false mk) go))
  leave-well (rootʰ (playingʳ _))       eb wh wq = silentʷ (inj₁ refl) (wellʳ (heldʷ (rootʰ idleʳ)) eb refl wh refl wq)
  leave-well (rootʰ overʳ)              eb wh wq = silentʷ (inj₁ refl) (wellʳ (heldʷ (rootʰ idleʳ)) eb refl wh refl wq)
  leave-well (coldʰ st ws (playingᶜ _)) eb wh wq = returns-run st ws eb wh wq
  leave-well (coldʰ st ws overᶜ)        eb wh wq = returns-run st ws eb wh wq

  -- A frame played on: its value delivered at its index, a stall
  -- skipped, or the burst closed and the rest scheduled, a timer set
  -- where the burst ends.
  play-well : ∀ {E lo h} {hp : Heapᴹ h} {p w es c i} {σ : w ⊑ h} {k : Stack w ⊤} {cl tm lg mk} (b : Playing h) {bu}
            → Playing.under′ b ≡ c → Playing.index b ≡ i → WellHeld E lo p k (playing c i ∷ es) [] → map entry bu ≡ es → WellHeap lo hp → WellQueue E lo cl tm
            → WellStep lo (silent (playᴹ (mach ⟨ hp , p , held σ k ⟩ cl tm (just b ∷ bu) [] lg false mk) b bu))
  play-well b refl refl wh eb hw wq with Playing.frame b
  play-well {lo = lo} {p = p} {c = c} {i} b refl refl (rootʰ (playingʳ le)) eb hw wq | emit a k′ =
    silentʷ (inj₁ refl) (wellʳ (runʷ ([ ix i ] , refl) settled-refl (proj₁ (look-well hw (Playing.sink b)) a (c ++ [ ix i ]) lo le)
                                     (fedʷ p λ lo′ st → rootʰ (playingʳ (settled-next c (<ᵖ-ix i) (≤ᵖ-trans le (inj₂ (<ᵖ-part c [] [] (<ᵖ-ix i)))) st))))
                               (cong (_ ∷_) eb) refl hw refl wq)
  play-well {lo = lo} {p = p} {i = i} b refl refl (coldʰ st ws (playingᶜ le)) eb hw wq | emit a k′ =
    silentʷ (inj₁ refl) (wellʳ (runʷ (under-trans (rest-under ws) ([ ix i ] , refl)) settled-refl (proj₁ (look-well hw (Playing.sink b)) a (p ++ [ ix i ]) lo le)
                                     (fedʷ p λ lo′ st′ → coldʰ (settled-trans st (settled-up ([ ix i ] , refl) st′)) ws
                                                               (playingᶜ (settled-next p (<ᵖ-ix i) (≤ᵖ-trans le (inj₂ (<ᵖ-part p [] [] (<ᵖ-ix i)))) st′))))
                               (cong (_ ∷_) eb) refl hw refl wq)
  play-well {c = c} {i} b refl refl (rootʰ (playingʳ le)) eb hw wq | stall k′ =
    silentʷ (inj₁ refl) (wellʳ (heldʷ (rootʰ (playingʳ (≤ᵖ-trans le (inj₂ (<ᵖ-part c [] [] (<ᵖ-ix i))))))) (cong (_ ∷_) eb) refl hw refl wq)
  play-well {p = p} {i = i} b refl refl (coldʰ st ws (playingᶜ le)) eb hw wq | stall k′ =
    silentʷ (inj₁ refl) (wellʳ (heldʷ (coldʰ st ws (playingᶜ (≤ᵖ-trans le (inj₂ (<ᵖ-part p [] [] (<ᵖ-ix i))))))) (cong (_ ∷_) eb) refl hw refl wq)
  play-well b refl refl wh eb hw wq | close k′ with From∞.force k′
  play-well {c = c} b refl refl (rootʰ (playingʳ le)) eb hw wq | close k′ | done =
    silentʷ (inj₁ refl) (wellʳ (heldʷ (rootʰ (owingʳ (≤ᵖ-trans le (inj₂ (<ᵖ-part c [] [] refl)))))) (cong (_ ∷_) eb) refl hw refl wq)
  play-well {p = p} b refl refl (coldʰ st ws (playingᶜ le)) eb hw wq | close k′ | done =
    silentʷ (inj₁ refl) (wellʳ (heldʷ (coldʰ st ws (owingᶜ (≤ᵖ-trans le (inj₂ (<ᵖ-part p [] [] refl)))))) (cong (_ ∷_) eb) refl hw refl wq)
  play-well b refl refl (rootʰ (playingʳ le)) eb hw wq | close k′ | quiet = silentʷ (inj₁ refl) (wellʳ (heldʷ (rootʰ resumeʳ)) eb refl hw refl wq)
  play-well b refl refl (coldʰ st ws (playingᶜ le)) eb hw wq | close k′ | quiet = silentʷ (inj₁ refl) (wellʳ (heldʷ (coldʰ st ws resumeᶜ)) eb refl hw refl wq)
  play-well {hp = hp} {c = c} {cl = cl} b refl refl (rootʰ (playingʳ le)) eb hw wq | close k′ | at t′ lt _ =
    silentʷ (inj₂ ends) (wellʳ (heldʷ (rootʰ resumeʳ)) eb refl (heap-up {hp = hp} (inj₂ ends) hw) refl
                               (queue-set _ (m<m+n cl (m<n⇒0<n∸m lt)) ends ([ last ] , refl) wq))
    where ends = ≤ᵖ-< le (<ᵖ-part c [] [] refl)
  play-well {hp = hp} {p = p} {cl = cl} b refl refl (coldʰ st ws (playingᶜ le)) eb hw wq | close k′ | at t′ lt _ =
    silentʷ (inj₂ ends) (wellʳ (heldʷ (coldʰ (settled-trans st (inj₂ ends , inj₂ ([ last ] , refl))) ws resumeᶜ)) eb refl (heap-up {hp = hp} (inj₂ ends) hw) refl
                               (queue-set _ (m<m+n cl (m<n⇒0<n∸m lt)) ends (under-trans (rest-under ws) ([ last ] , refl)) wq))
    where ends = ≤ᵖ-< le (<ᵖ-part p [] [] refl)

  playing-inj : ∀ {c c′ i i′} → playing c i ≡ playing c′ i′ → c ≡ c′ × i ≡ i′
  playing-inj refl = refl , refl

  -- A playing burst: spent, it is over; polled, it plays; else its sink
  -- is asked whether it is closed, which is `Still`.
  turned-playing : ∀ {E lo h} {hp : Heapᴹ h} {p w es c i} {σ : w ⊑ h} {k : Stack w ⊤} {cl tm lg mk} (b : Playing h) {bu}
                 → Playing.under′ b ≡ c → Playing.index b ≡ i → WellHeld E lo p k (playing c i ∷ es) [] → map entry bu ≡ es → WellHeap lo hp → WellQueue E lo cl tm
                 → WellStep lo (step (mach ⟨ hp , p , held σ k ⟩ cl tm (just b ∷ bu) [] lg false mk))
  turned-playing {hp = hp} b ec ei wh eb hw wq with spent? hp (Playing.handle b)
  ... | true  = leave-well wh eb hw wq
  ... | false with Playing.polled b
  ...   | true  = play-well b ec ei wh eb hw wq
  ...   | false rewrite ec | ei = silentʷ (inj₁ refl) (wellʳ (stillʷ (proj₂ (proj₂ (look-well hw (Playing.sink b)))) (toldʷ wh)) (cong (_ ∷_) eb) refl hw refl wq)

  turned-well : ∀ {lo h} {hp : Heapᴹ h} {p w} {σ : w ⊑ h} {k : Stack w ⊤} {cl tm b bu lg en mk}
              → WellMach lo (mach ⟨ hp , p , held σ k ⟩ cl tm (b ∷ bu) [] lg en mk) → WellStep lo (step (mach ⟨ hp , p , held σ k ⟩ cl tm (b ∷ bu) [] lg en mk))
  turned-well {b = nothing} (wellʳ (heldʷ wh@(rootʰ overʳ)) eb refl hw refl wq)        = leave-well wh (∷-tail eb) hw wq
  turned-well {b = nothing} (wellʳ (heldʷ wh@(coldʰ _ _ overᶜ)) eb refl hw refl wq)    = leave-well wh (∷-tail eb) hw wq
  turned-well {b = nothing} (wellʳ (heldʷ (rootʰ (playingʳ _))) eb refl hw refl wq)     with ∷-head eb
  ... | ()
  turned-well {b = nothing} (wellʳ (heldʷ (coldʰ _ _ (playingᶜ _))) eb refl hw refl wq) with ∷-head eb
  ... | ()
  turned-well {b = nothing} (wellʳ (heldʷ (rootʰ idleʳ)) () refl hw refl wq)
  turned-well {b = just b} (wellʳ (heldʷ wh@(rootʰ (playingʳ _))) eb refl hw refl wq) =
    turned-playing b (proj₁ (playing-inj (∷-head eb))) (proj₂ (playing-inj (∷-head eb))) wh (∷-tail eb) hw wq
  turned-well {b = just b} (wellʳ (heldʷ wh@(coldʰ _ _ (playingᶜ _))) eb refl hw refl wq) =
    turned-playing b (proj₁ (playing-inj (∷-head eb))) (proj₂ (playing-inj (∷-head eb))) wh (∷-tail eb) hw wq
  turned-well {b = just b} (wellʳ (heldʷ (rootʰ overʳ)) eb refl hw refl wq) with ∷-head eb
  ... | ()
  turned-well {b = just b} (wellʳ (heldʷ (coldʰ _ _ overᶜ)) eb refl hw refl wq) with ∷-head eb
  ... | ()
  turned-well {b = just b} (wellʳ (heldʷ (rootʰ idleʳ)) () refl hw refl wq)

  -- THE LOOP'S TURN: nothing held but the root's level, nothing playing
  -- or owed.  The earliest timer popped opens the next epoch at its
  -- cascade, which the last is before and every other timer past.
  turn-well : ∀ {E lo h} {hp : Heapᴹ h} {p w} {σ : w ⊑ h} {cl tm lg mk}
            → WellHeap lo hp → WellQueue E lo cl tm → WellStep lo (step (mach ⟨ hp , p , held σ (bottom {w}) ⟩ cl tm [] [] lg false mk))
  turn-well {tm = []}     wh wq = drainedʷ
  turn-well {lo = lo} {tm = t ∷ ts} wh (queueʷ _ w ((b , _) ∷ qs) (r AllPairs.∷ rs)) =
    silentʷ (inj₁ refl) (wellʳ {E = cascade t} (heldʷ (rootʰ (playingʳ (inj₂ (<ᵖ-trans lo (cascade t) (cascade t ++ [ ix 0 ]) (epoch-past w b) (<ᵖ-below (cascade t) {ix 0} []))))))
                               refl refl wh refl (queueʷ (subᴾ (Timer.from t) ∷ [] , refl) (inj₁ (inj₂ (epoch-past w b))) (popped {t = t} r qs) rs))

  -- The machine's fundamental lemma: a well configuration's step keeps
  -- it well, and a value it shows is no earlier than the last.
  preserve : ∀ {lo m} → WellMach lo m → WellStep lo (step m)
  preserve {m = mach ⟨ hp , p , asking (note a) k σ s ⟩ cl tm bu td lg en mk} (wellʳ (notingʷ u le st wk ws) eb dq wh refl wq) =
    valueʷ le (wellʳ (runʷ u (settled-at st le) wk ws) eb dq (heap-up {hp = hp} le wh) refl (queue-up le (inj₂ u) wq))
  preserve {m = mach ⟨ hp , p , asking fin k σ s ⟩ cl tm bu td lg en mk} (wellʳ (finningʷ le) _ _ _ refl _) = completeʷ le
  preserve {m = mach ⟨ hp , p , run a σ k ⟩ cl tm bu td lg en mk} w = runs-well w
  preserve {m = mach ⟨ hp , p , ret x σ k ⟩ cl tm bu td lg en mk} w = returns-well w
  preserve {m = mach ⟨ hp , p , held σ k ⟩ cl tm bu (t ∷ td) lg en mk} w = paid-well w
  preserve {m = mach ⟨ hp , p , held σ k ⟩ cl tm (x ∷ bu) [] lg en mk} w = turned-well w
  preserve {m = mach ⟨ hp , p , held σ k ⟩ cl tm [] [] lg en mk} (wellʳ (heldʷ (rootʰ idleʳ)) refl refl wh refl wq) = turn-well wh wq
  preserve {m = mach ⟨ hp , p , held σ k ⟩ cl tm [] [] lg en mk} (wellʳ (heldʷ (coldʰ _ _ ())) refl refl _ _ _)

  -- The recorder is well: a value or completion at no earlier a position.
  recorder-well : WellObs recorder
  recorder-well = (λ a q lo le → noteʷ le doneʷ) , (λ q lo le → finʷ le) , doneˢ

  -- The run begins well: the program compiled at the root, in the epoch
  -- the clock's first tick opens, the recorder its observer, nothing on
  -- the heap, queued or playing.
  begin-well : (o : PureObs [] R) → WellMach root (begin o)
  begin-well o = wellʳ {E = root} (runʷ ([] , refl) (inj₁ refl , inj₁ refl)
                                          (compile-well o [] (lift tt) same recorder _ root root (inj₁ refl) recorder-well (λ σ sub _ p lo → doneʷ)) bottomʷ)
                       refl refl (heapʷ λ ()) refl (queueʷ ([] , refl) (inj₁ (inj₁ refl)) [] AllPairs.[])

  mutual
    rising : ∀ {lo m} → WellMach lo m → Rising lo m
    rising w .Rising.rises = risingˢ (preserve w)

    risingˢ : ∀ {lo s} → WellStep lo s → RisingStep lo s
    risingˢ (silentʷ le w)  = silentʳ le (rising w)
    risingˢ (valueʷ le w)   = valueʳ le (rising w)
    risingˢ (completeʷ le)  = completeʳ le
    risingˢ drainedʷ        = drainedʳ

  -- SORTEDNESS: the program's run rises from the root.
  sorted : (o : PureObs [] R) → Rising root (begin o)
  sorted o = rising (begin-well o)
