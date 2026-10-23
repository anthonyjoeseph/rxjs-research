{-# OPTIONS --guardedness #-}

-- THE CLIMB: a signal carried from its emitter up the context, each
-- operator's frame one rise, to a re-entry configuration.
module port.Climbs where

open import Data.List using (List; []; _++_; [_])
open import Data.List.Properties using (++-conicalʳ)
open import Data.List.Relation.Unary.All using ([])
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-pred)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.MonotonicList.Events using (Pos)
open import denotation.MonotonicList using (agree-refl)
import denotation.Unfold as U
open import operation.PureObservable using (module Machine; module Driver)
open import port.Sane using (Sane)
open import port.Placed.Order using (Placed)
open import port.Unsub using (module Unsubbing)
open import port.Strong using (module Strongly)
open import port.Sorted.Walk using (module SortingWalk)
open import port.Ghost using (module Ghosting)
open import port.Ghost.Paths using (module GhostingPaths)

open Machine using (St; Ctx; Conf; Job; Ev; nx; cp; dirs; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc;
  ⟨_,_,_,_,_⟩; rising)

module Ascending (R : Set) where
  open Driver R using (Mach; mach)
  open Unsubbing R using (_⇝_; now)
  open SortingWalk R using (WellMach)
  open Strongly R using (Sub; Path; here; Strong; Carried; carried; closing; noteAs; Owned; Kernels; Meaning; Queue; Books;
    Each; Heads; Lingers; Untold; Ended; DoneBy; outers; part; leftover)
  open Ghosting R using (Hopped; Load; _≼_; load; loadOf; hopped-pre; showing; agrees)
  open GhostingPaths R using (_⊕_; Lifts; lifts-here; Lefts; Healed; One; whole; snoc; view; height; one-lower;
    one-map; one-scan; one-cut; one-lane; one-take; one-outer; one-lanes; one-source; one-body)

  -- The node a signal reaches already past it, and the ghost's step the
  -- signal lifted along the path: a value leaves the node standing, an
  -- end leaves it gone, every connect it killed on the way ended.
  Passed : (q : Pos) (g : U.Node [] R) {T : Sub [] R} → ∀ {Δ A} {v : Sub Δ A} {π} → Path T v π → Ev A → Set₁
  Passed q g {Δ = Δ} {A} {v} σ (nx y) =
    Σ (U.Node Δ A) λ c′ → part v ≡ just c′ × Σ (U.Step [] R) λ S → Lifts σ (U.outˢ q y c′) S × U.step g ≡ S
  Passed q g {v = v} σ cp =
    part v ≡ nothing × Σ (U.Step [] R) λ S → Lifts σ (U.endˢ q) S × U.step g ≡ S × Healed q σ

  -- What a closed sub leaves running heads no earlier than the run.
  ClosedHeads : (q : Pos) {T : Sub [] R} → ∀ {Δ A} {v : Sub Δ A} {π} → Path T v π → Ev A → Set
  ClosedHeads q σ (nx _)     = ⊤
  ClosedHeads q {v = v} σ cp = Heads q (U.restᶜ {B = ⊤} (leftover {B = ⊤} v))

  -- What the climbing signal's lift leaves free, left alike.
  LeftsOf : (q : Pos) (g : U.Node [] R) {T : Sub [] R} → ∀ {Δ A} {v : Sub Δ A} {π} (σ : Path T v π) (e : Ev A) → Passed q g σ e → Set₁
  LeftsOf q g σ (nx y) (_ , _ , _ , L , _) = Lefts L
  LeftsOf q g σ cp     (_ , _ , L , _)     = Lefts L

  -- A SIGNAL ON ITS WAY UP: `e` about to be told to the frame above the
  -- node the path walks to, the witness holding everything else the
  -- carrier does, the flags of the outers it climbs out of unset.
  record Calling (g : U.Node [] R) (ℓ : Load) (m₁ : Mach) {Δ A} {T : Sub [] R} {v : Sub Δ A} {π}
                 (σ : Path T v π) (e : Ev A) : Set₁ where
    field
      sane    : Sane [] g
      placed  : Placed g []
      {c}     : Ctx R Δ A
      {s}     : St Δ A
      {p}     : Pos
      {rs}    : List Job
      ctl     : Mach.conf m₁ ≡ ⟨ c , s , rising e , p , rs ⟩
      at      : dirs c ≡ π
      lifted  : Passed (Conf.pos (Mach.conf m₁)) g σ e
      lefts   : LeftsOf (Conf.pos (Mach.conf m₁)) g σ e lifted
      rest-heads : ClosedHeads (Conf.pos (Mach.conf m₁)) σ e
      owned   : Owned T m₁
      kernels : Kernels T (Mach.conf m₁)
      meaning : Meaning T (Mach.conf m₁)
      queue   : Queue (Conf.pos (Mach.conf m₁)) (Mach.clock m₁) (Mach.timers m₁) T
      books   : Books T m₁
      sorted  : Σ Pos λ lo → WellMach lo m₁
      behind  : Each (Heads (Conf.pos (Mach.conf m₁))) T
      lingers : Lingers T
      told    : Untold (Conf.pos (Mach.conf m₁)) T
      ended   : Ended T
      flags   : DoneBy T (outers σ)
      kept    : load m₁ T ≼ ℓ

  -- One operator called: a re-entry configuration reached, or a signal
  -- one operator higher, the path shorter.
  data Called {g m} (st : Strong g m) (m₁ : Mach) {Δ A} {T : Sub [] R} {v : Sub Δ A} {π} (σ : Path T v π) : Set₁ where
    landed : Hopped st m₁ → Called st m₁ σ
    rose   : ∀ {m₂ Δ′ A′} {T′ : Sub [] R} {v′ : Sub Δ′ A′} {π′} {σ′ : Path T′ v′ π′} {e′ : Ev A′}
           → m₁ ⇝ m₂ → height σ′ < height σ → Calling g (loadOf st) m₂ σ′ e′ → Called st m₁ σ

  -- Some signal on its way up.
  data Aloft (g : U.Node [] R) (ℓ : Load) (m₁ : Mach) : Set₁ where
    aloft : ∀ {Δ A} {T : Sub [] R} {v : Sub Δ A} {π} {σ : Path T v π} {e : Ev A}
          → Calling g ℓ m₁ σ e → Aloft g ℓ m₁

  -- A signal at the root: a value about to be shown, the ghost's step
  -- showing it; an end, the ghost's step its end.
  private
    -- A context with no directions is the root's.
    top-of : ∀ {c : Ctx R [] R} → dirs c ≡ [] → c ≡ top
    top-of {top} e = refl
    top-of {inMap _ c} e with ++-conicalʳ (dirs c) _ e
    ... | ()
    top-of {inScan _ _ c} e with ++-conicalʳ (dirs c) _ e
    ... | ()
    top-of {inCut _ _ c} e with ++-conicalʳ (dirs c) _ e
    ... | ()
    top-of {inLn _ c} e with ++-conicalʳ (dirs c) _ e
    ... | ()
    top-of {inTake _ _ c} e with ++-conicalʳ (dirs c) _ e
    ... | ()
    top-of {inOuter _ _ _ _ _ _ c} e with ++-conicalʳ (dirs c) _ e
    ... | ()
    top-of {inLanes _ _ _ _ _ _ _ _ c} e with ++-conicalʳ (dirs c) _ e
    ... | ()
    top-of {inSrc _ _ c} e with ++-conicalʳ (dirs c) _ e
    ... | ()

  call-root : ∀ {g m} (st : Strong g m) {ℓ m₁} {T : Sub [] R} {e : Ev R} → Calling g ℓ m₁ {T = T} here e → Hopped st m₁
  call-root {g} st {m₁ = mach k clk tms ts} {T} {nx y} cl
    with Calling.c cl | top-of (Calling.at cl) | Calling.ctl cl | Calling.lifted cl
  ... | .top | refl | refl | c′ , pv , _ , lifts-here , sg =
    g , _ , now
    , carried (record
        { sane = Calling.sane cl ; placed = Calling.placed cl ; tree = T ; kernels = Calling.kernels cl
        ; ctlAs = noteAs refl (Books.clocked (Calling.books cl)) ; meets = c′ , pv , sg
        ; owned = Calling.owned cl ; meaning = Calling.meaning cl ; queue = Calling.queue cl ; books = Calling.books cl
        ; sorted = Calling.sorted cl ; behind = Calling.behind cl ; lingers = Calling.lingers cl ; told = Calling.told cl
        ; ended = Calling.ended cl ; flags = Calling.flags cl })
    , showing (agrees (λ n → agree-refl n _)) (λ ())
  call-root {g} st {m₁ = mach k clk tms ts} {T} {cp} cl
    with Calling.c cl | top-of (Calling.at cl) | Calling.ctl cl | Calling.lifted cl
  ... | .top | refl | refl | _ , _ , lifts-here , sg , _ =
    g , _ , now , closing refl sg (Calling.sane cl) (Calling.placed cl) , showing (agrees (λ n → agree-refl n _)) (λ ())

  -- ONE OPERATOR CALLED, by the operator: its frame's rise, the signal
  -- one operator higher or the climb landed.
  postulate
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Base.agda
    call-map : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub [] R} {u : Sub Δ A} {v : Sub Δ′ A′} {π τ} (ρ : Path T u π) {s : Path u v τ}
             → One s → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ s) e → Called st m₁ (ρ ⊕ s)
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Scan.agda
    call-scan : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub [] R} {u : Sub Δ A} {v : Sub Δ′ A′} {π τ} (ρ : Path T u π) {s : Path u v τ}
              → One s → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ s) e → Called st m₁ (ρ ⊕ s)
    call-cut : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub [] R} {u : Sub Δ A} {v : Sub Δ′ A′} {π τ} (ρ : Path T u π) {s : Path u v τ}
             → One s → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ s) e → Called st m₁ (ρ ⊕ s)
    call-lane : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub [] R} {u : Sub Δ A} {v : Sub Δ′ A′} {π τ} (ρ : Path T u π) {s : Path u v τ}
              → One s → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ s) e → Called st m₁ (ρ ⊕ s)
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Take.agda
    call-take : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub [] R} {u : Sub Δ A} {v : Sub Δ′ A′} {π τ} (ρ : Path T u π) {s : Path u v τ}
              → One s → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ s) e → Called st m₁ (ρ ⊕ s)
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Flat/Plant.agda
    call-outer : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub [] R} {u : Sub Δ A} {v : Sub Δ′ A′} {π τ} (ρ : Path T u π) {s : Path u v τ}
               → One s → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ s) e → Called st m₁ (ρ ⊕ s)
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Lanes/Queue.agda
    call-lanes : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub [] R} {u : Sub Δ A} {v : Sub Δ′ A′} {π τ} (ρ : Path T u π) {s : Path u v τ}
               → One s → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ s) e → Called st m₁ (ρ ⊕ s)
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Connect.agda
    call-source : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub [] R} {u : Sub Δ A} {v : Sub Δ′ A′} {π τ} (ρ : Path T u π) {s : Path u v τ}
                → One s → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ s) e → Called st m₁ (ρ ⊕ s)
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Base.agda
    call-body : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub [] R} {u : Sub Δ A} {v : Sub Δ′ A′} {π τ} (ρ : Path T u π) {s : Path u v τ}
              → One s → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ s) e → Called st m₁ (ρ ⊕ s)

  call-step : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub [] R} {u : Sub Δ A} {v : Sub Δ′ A′} {π τ}
              (ρ : Path T u π) {s : Path u v τ} → One s → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ s) e → Called st m₁ (ρ ⊕ s)
  call-step st ρ o@one-map       cl = call-map st ρ o cl
  call-step st ρ o@one-scan      cl = call-scan st ρ o cl
  call-step st ρ o@one-cut       cl = call-cut st ρ o cl
  call-step st ρ o@one-lane      cl = call-lane st ρ o cl
  call-step st ρ o@one-take      cl = call-take st ρ o cl
  call-step st ρ o@one-outer     cl = call-outer st ρ o cl
  call-step st ρ o@(one-lanes _) cl = call-lanes st ρ o cl
  call-step st ρ o@one-source    cl = call-source st ρ o cl
  call-step st ρ o@one-body      cl = call-body st ρ o cl

  -- A SIGNAL CLIMBS TO A RE-ENTRY CONFIGURATION: one operator at a time,
  -- from the path's far end, each step to a shorter path.
  call : ∀ {g m} (st : Strong g m) (n : ℕ) {m₁ Δ A} {T : Sub [] R} {v : Sub Δ A} {π}
         (σ : Path T v π) {e : Ev A} → height σ < n → Calling g (loadOf st) m₁ σ e → Hopped st m₁
  call st zero    σ () cl
  call st (suc n) σ lt cl with view σ
  ... | whole      = call-root st cl
  ... | snoc ρ s o with call-step st ρ o cl
  ...   | landed hp         = hp
  ...   | rose path lt′ cl′ = hopped-pre path (call st n _ (≤-trans lt′ (≤-pred lt)) cl′)

  soar : ∀ {g m m′} (st : Strong g m) → Σ Mach (λ m₁ → m′ ⇝ m₁ × Aloft g (loadOf st) m₁) → Hopped st m′
  soar st (m₁ , path , aloft {σ = σ} cl) = hopped-pre path (call st (suc (height σ)) σ ≤-refl cl)
