{-# OPTIONS --guardedness #-}

-- THE CLIMB: a signal carried from its emitter up the context, each
-- operator's frame one rise, to a re-entry configuration.
module port.Climbs where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; [_]; map)
open import Data.List.Properties using (++-conicalʳ)
open import Data.List.Relation.Unary.All using ([]) renaming (lookup to lookupᴬ)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-pred)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂; sym; trans)

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
open import port.Moves using (module Moving)

open Machine using (St; Ctx; Conf; Job; Ev; nx; cp; dirs; plug; scanS; connS; owed; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody;
  ⟨_,_,_,_,_⟩; rising)

module Ascending (R : Set) where
  open Driver R using (Mach; mach; step; silent)
  open Unsubbing R using (_⇝_; now; then)
  open SortingWalk R using (WellMach; WellStep; silentʷ; preserve)
  open Strongly R using (Sub; Path; here; Strong; Carried; carried; closing; noteAs; Owned; Kernels; Meaning; Queue; Books;
    Each; Heads; connected; Lingers; Untold; Ended; DoneBy; outers; outersL; part; leftover; forget; mapᴹ; Feed; owing; Fed; FedLanes;
    Begins; focused; attaching; PathLanes; this-lane; next-lane; in-map; in-scan; in-cut; in-lane; in-take; in-outer; in-lanes;
    in-source; in-body; pendingˢ; coldˢ; ofˢ; doneˢ; mapˢ; scanˢ; cutˢ; laneˢ; takeWhileˢ; flatMapˢ; connectˢ; joinˢ)
  open Moving R using (plant; planted; plantedᴸ)
  open Ghosting R using (Hopped; Load; _≼_; load; loadOf; hopped-pre; showing; agrees)
  open GhostingPaths R using (_⊕_; _⊕ᴸ_; Lifts; lifts-here; lifts-map; lifts-scan; lifts-take; lifts-body; lifts-shut; lefts-subst; lifts-split; lefts-up; healed-split; Lefts; Healed; One; whole; snoc; view;
    height; heightL; one-lower;
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
    with Calling.c cl | top-of {Calling.c cl} (Calling.at cl) | Calling.ctl cl | Calling.lifted cl
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
    with Calling.c cl | top-of {Calling.c cl} (Calling.at cl) | Calling.ctl cl | Calling.lifted cl
  ... | .top | refl | refl | _ , _ , lifts-here , sg , _ =
    g , _ , now , closing refl sg (Calling.sane cl) (Calling.placed cl) , showing (agrees (λ n → agree-refl n _)) (λ ())

  -- ONE OPERATOR CALLED, by the operator: its frame's rise, the signal
  -- one operator higher or the climb landed.
  postulate
    call-cut : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub [] R} {u : Sub Δ A} {v : Sub Δ′ A′} {π τ} (ρ : Path T u π) {s : Path u v τ}
             → One s → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ s) e → Called st m₁ (ρ ⊕ s)
    call-lane : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub [] R} {u : Sub Δ A} {v : Sub Δ′ A′} {π τ} (ρ : Path T u π) {s : Path u v τ}
              → One s → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ s) e → Called st m₁ (ρ ⊕ s)
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Flat/Plant.agda
    --
    -- DEAD ROUTE: the old body plants the inner on the heap's cells; the state tree's `admit` starts it in the flatMap's lanes.
    call-outer : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub [] R} {u : Sub Δ A} {v : Sub Δ′ A′} {π τ} (ρ : Path T u π) {s : Path u v τ}
               → One s → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ s) e → Called st m₁ (ρ ⊕ s)
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Lanes/Queue.agda
    --
    -- DEAD ROUTE: the old body frees the lane's heap slot; the state tree's `dequeue` starts the queue's head in place.
    call-lanes : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub [] R} {u : Sub Δ A} {v : Sub Δ′ A′} {π τ} (ρ : Path T u π) {s : Path u v τ}
               → One s → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ s) e → Called st m₁ (ρ ⊕ s)
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Connect.agda
    --
    -- DEAD ROUTE: the old body writes the subject's heap cells; the state tree appends to the connect's `feeds` and resumes feeding.
    --
    -- RECOVERY: git show b039ebbb:agda-impl/port/Ghost/Paths.agda restores `healed-end`, an end reaching a connect's source read off `Healed`, and `lefts-subst₂`
    call-source : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub [] R} {u : Sub Δ A} {v : Sub Δ′ A′} {π τ} (ρ : Path T u π) {s : Path u v τ}
                → One s → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ s) e → Called st m₁ (ρ ⊕ s)

  ------------------------------------------------------------------------
  -- THE CLIMB THROUGH A SCAN: a value accumulated, the scan's node
  -- rewritten; an end as it is.

  -- A silent step keeps the machine sorted.
  sorted-step : ∀ {m m′} → Σ Pos (λ lo → WellMach lo m) → step m ≡ silent m′ → Σ Pos λ lo → WellMach lo m′
  sorted-step (lo , w) e with subst (WellStep lo) e (preserve w)
  ... | silentʷ _ w′ = _ , w′

  private
    mutual
      outers-up : ∀ {Γ A Δ B Ε C π τ} {t : Sub Γ A} {u : Sub Δ B} {v : Sub Ε C} (ρ : Path t u π) (σ : Path u v τ)
                → outers σ ≡ [] → outers (ρ ⊕ σ) ≡ outers ρ
      outers-up here                σ e = e
      outers-up (in-map ρ)          σ e = cong (map (0 ∷_)) (outers-up ρ σ e)
      outers-up (in-scan ρ)         σ e = cong (map (0 ∷_)) (outers-up ρ σ e)
      outers-up (in-cut ρ)          σ e = cong (map (0 ∷_)) (outers-up ρ σ e)
      outers-up (in-lane ρ)         σ e = cong (map (0 ∷_)) (outers-up ρ σ e)
      outers-up (in-take ρ)         σ e = cong (map (0 ∷_)) (outers-up ρ σ e)
      outers-up (in-outer ρ)        σ e = cong (λ ns → [] ∷ map (0 ∷_) ns) (outers-up ρ σ e)
      outers-up (in-lanes {i = i} ρ) σ e = cong (map (suc i ∷_)) (outersL-up ρ σ e)
      outers-up (in-source ρ)       σ e = cong (map (0 ∷_)) (outers-up ρ σ e)
      outers-up (in-body ρ)         σ e = cong (map (1 ∷_)) (outers-up ρ σ e)

      outersL-up : ∀ {Γ A Δ B Ε C i π τ} {ls : List (Sub Γ A)} {u : Sub Δ B} {v : Sub Ε C} (πL : PathLanes ls u i π) (σ : Path u v τ)
                 → outers σ ≡ [] → outersL (πL ⊕ᴸ σ) ≡ outersL πL
      outersL-up (this-lane ρ)  σ e = outers-up ρ σ e
      outersL-up (next-lane πL) σ e = outersL-up πL σ e

    mutual
      height-planted : ∀ {Γ A Δ B π} {t : Sub Γ A} {u : Sub Δ B} (ψ : Path t u π) (w : Sub Δ B) → height (planted ψ w) ≡ height ψ
      height-planted here          w = refl
      height-planted (in-map ψ)    w = cong suc (height-planted ψ w)
      height-planted (in-scan ψ)   w = cong suc (height-planted ψ w)
      height-planted (in-cut ψ)    w = cong suc (height-planted ψ w)
      height-planted (in-lane ψ)   w = cong suc (height-planted ψ w)
      height-planted (in-take ψ)   w = cong suc (height-planted ψ w)
      height-planted (in-outer ψ)  w = cong suc (height-planted ψ w)
      height-planted (in-lanes ψ)  w = heightL-planted ψ w
      height-planted (in-source ψ) w = cong suc (height-planted ψ w)
      height-planted (in-body ψ)   w = cong suc (height-planted ψ w)

      heightL-planted : ∀ {Γ A Δ B i π} {ls : List (Sub Γ A)} {u : Sub Δ B} (ψ : PathLanes ls u i π) (w : Sub Δ B)
                      → heightL (plantedᴸ ψ w) ≡ heightL ψ
      heightL-planted (this-lane ψ) w = cong suc (height-planted ψ w)
      heightL-planted (next-lane ψ) w = heightL-planted ψ w

    -- What a joiner is owed reads the configuration only through `owing`.
    mutual
      fed-same : ∀ {k₁ k₂ : Conf R} → (∀ {X} (b : Feed X) π j → owing k₁ b π j ≡ owing k₂ b π j)
               → ∀ {Γ A} (t : Sub Γ A) {π ν} → Fed k₁ t π ν → Fed k₂ t π ν
      fed-same h (pendingˢ _ _)              _       = tt
      fed-same h (coldˢ _ _)                 _       = tt
      fed-same h (ofˢ _ _ _)                 _       = tt
      fed-same h doneˢ                       _       = tt
      fed-same h (mapˢ _ s)                  d       = fed-same h s d
      fed-same h (scanˢ _ _ s)               d       = fed-same h s d
      fed-same h (cutˢ _ _ s)                d       = fed-same h s d
      fed-same h (laneˢ _ s)                 d       = fed-same h s d
      fed-same h (takeWhileˢ _ _ _ s)        d       = fed-same h s d
      fed-same h (flatMapˢ _ _ _ _ _ _ o ls) (d , e) = fed-same h o d , fedL-same h ls e
      fed-same h (connectˢ _ _ _ _ s b)      (d , e) = fed-same h s d , fed-same h b e
      fed-same h (joinˢ j _ x _) {π} {ν}     d       = λ g → trans (d g) (h (lookupᴬ ν x) π j)

      fedL-same : ∀ {k₁ k₂ : Conf R} → (∀ {X} (b : Feed X) π j → owing k₁ b π j ≡ owing k₂ b π j)
                → ∀ {Γ B} (ls : List (Sub Γ B)) {π i ν} → FedLanes k₁ ls π i ν → FedLanes k₂ ls π i ν
      fedL-same h []       _       = tt
      fedL-same h (s ∷ ls) (d , e) = fed-same h s d , fedL-same h ls e

    -- Rising, the jobs owed are the suspended ones alone.
    owned-rise : ∀ {T : Sub [] R} {Γ A Γ′ A′} {c : Ctx R Γ A} {x e p rs} {c′ : Ctx R Γ′ A′} {x′ e′ p′ clk tms ts clk′ tms′ ts′}
               → Owned T (mach ⟨ c , x , rising e , p , rs ⟩ clk tms ts) → Owned T (mach ⟨ c′ , x′ , rising e′ , p′ , rs ⟩ clk′ tms′ ts′)
    owned-rise o = record
      { ofs = Owned.ofs o ; begun = λ ψ → rebegin (Owned.begun o ψ) ; attached = Owned.attached o ; ends = Owned.ends o
      ; cuts = Owned.cuts o ; feeds = Owned.feeds o ; bodies = Owned.bodies o ; sources = Owned.sources o ; owes = Owned.owes o }
      where rebegin : ∀ {π q} → Begins _ π q → Begins _ π q
            rebegin (focused _ () _)
            rebegin (attaching ρ p e a q) = attaching ρ p e a q

  -- Done flags read as they were, one step up a path entering no outer.
  done-up : ∀ {Δ A Δ′ A′ π τ} {T : Sub [] R} {x : Sub Δ A} {v : Sub Δ′ A′} (ρ : Path T x π) (c : Path x v τ)
          → outers c ≡ [] → DoneBy T (outers (ρ ⊕ c)) → DoneBy T (outers ρ)
  done-up {T = T} ρ c e d = subst (DoneBy T) (outers-up ρ c e) d

  postulate
    -- A context climbing through a scan, the scan's own frame first.
    scan-at : ∀ {Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π)
              {c : Ctx R Δ A} {x} → dirs c ≡ π ++ [ 0 ] → forget T ≡ plug c x
            → Σ (Ctx R Δ B) λ c₀ → c ≡ inScan f z c₀ × dirs c₀ ≡ π

    -- The tree with the scan's accumulator rewritten is the machine's.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Frame/Repool.agda
    --
    -- DEAD ROUTE: the old body is a heap write's frame; the state tree has no heap, the write is a `plant`.
    scan-kernels : ∀ {Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π)
                   {c₀ : Ctx R Δ B} {x} → dirs c₀ ≡ π → forget T ≡ plug c₀ (scanS f z x)
                 → ∀ z′ → forget (plant ρ (scanˢ f z′ v)) ≡ plug c₀ (scanS f z′ x)

    -- A value through a scan, the carrier's parts on the rewritten tree.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Frame/Repool.agda
    --
    -- DEAD ROUTE: the old bodies are a heap write's frames; the state tree has no heap, the write is a `plant`.
    scan-lifts : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
               → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y)
               → Passed (Conf.pos (Mach.conf m₁)) g (planted ρ (scanˢ f (f z y) v)) (nx (f z y))
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Frame/Lefts.agda
    --
    -- DEAD ROUTE: the old body reads the scan's leftover unchanged across a heap store (leftover-off over Off); a `plant` aliases nothing.
    scan-lefts : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
               → (cl : Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y))
               → LeftsOf (Conf.pos (Mach.conf m₁)) g (planted ρ (scanˢ f (f z y) v)) (nx (f z y)) (scan-lifts ρ cl)
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Scan.agda
    --
    -- DEAD ROUTE: the old body is the heap-write Shift frame's wr-owned over store-held; the state tree owes its jobs on `rets`, not in heap cells.
    scan-owned : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
               → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y) → ∀ {m₂} → step m₁ ≡ silent m₂
               → Owned (plant ρ (scanˢ f (f z y) v)) m₂
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Frame/Repool.agda
    scan-meaning : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
                 → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y) → ∀ {m₂} → step m₁ ≡ silent m₂
                 → Meaning (plant ρ (scanˢ f (f z y) v)) (Mach.conf m₂)
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Scan.agda
    --
    -- DEAD ROUTE: the old body keeps the queue across a heap store (store-keeps); the state tree's queue is not stored in a heap.
    scan-queue : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
               → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y)
               → Queue (Conf.pos (Mach.conf m₁)) (Mach.clock m₁) (Mach.timers m₁) (plant ρ (scanˢ f (f z y) v))
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Frame/Repool.agda
    --
    -- DEAD ROUTE: the old body splits on heap aliasing after the store (scan-sees, part-alike); a `plant` rewrites the node itself.
    --
    -- RECOVERY: git show 9ec3e6c62e05857feabffdd65a05929de347e532:agda-impl/adequacy/Frame.agda restores `heads-rescan`, a scan heading where its source does whatever its accumulator
    scan-behind : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
                → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y)
                → Each (Heads (Conf.pos (Mach.conf m₁))) (plant ρ (scanˢ f (f z y) v))
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Scan.agda
    --
    -- DEAD ROUTE: the old body is the heap-write Shift frame, its lingering read by comparing two heaps (leftover-alike); a `plant` has no second heap.
    scan-lingers : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
                 → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y) → Lingers (plant ρ (scanˢ f (f z y) v))
    scan-told : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
              → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y) → Untold (Conf.pos (Mach.conf m₁)) (plant ρ (scanˢ f (f z y) v))
    scan-ended : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
               → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y) → Ended (plant ρ (scanˢ f (f z y) v))
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Scan.agda
    --
    -- DEAD ROUTE: the old body is the heap-write Shift frame, its flags read by comparing two heaps (flags-alike); a `plant` has no second heap.
    scan-flags : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
               → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y)
               → DoneBy (plant ρ (scanˢ f (f z y) v)) (outers (planted ρ (scanˢ f (f z y) v)))

    -- The books and the load, the accumulator rewritten.
    scan-books : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
               → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y) → ∀ {m₂} → step m₁ ≡ silent m₂
               → Books (plant ρ (scanˢ f (f z y) v)) m₂
    scan-load : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
              → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y) → ∀ {m₂} → step m₁ ≡ silent m₂
              → load m₂ (plant ρ (scanˢ f (f z y) v)) ≡ load m₁ T

  call-scan : ∀ {g m} (st : Strong g m) {m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π)
            → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ in-scan here) e → Called st m₁ (ρ ⊕ in-scan here)
  call-scan st {m₁ = mach k clk tms ts} {f = f} {z} {v} ρ {nx y} cl
    with Calling.c cl | Calling.s cl | Calling.at cl | Calling.ctl cl | Calling.kernels cl
  ... | c | x | at | refl | kn with scan-at ρ {c = c} {x} at kn
  ...   | c₀ , refl , at₀ =
    rose {σ′ = planted ρ (scanˢ f (f z y) v)} {e′ = nx (f z y)} (then refl now)
      (subst (_< height (ρ ⊕ in-scan here)) (sym (height-planted ρ (scanˢ f (f z y) v))) (one-lower ρ one-scan))
      (record
        { sane = Calling.sane cl ; placed = Calling.placed cl ; ctl = refl ; at = at₀
        ; lifted = scan-lifts ρ cl ; lefts = scan-lefts ρ cl ; rest-heads = tt
        ; owned = scan-owned ρ cl refl ; kernels = scan-kernels ρ {c₀ = c₀} {x} at₀ kn (f z y) ; meaning = scan-meaning ρ cl refl
        ; queue = scan-queue ρ cl ; books = scan-books ρ cl refl ; sorted = sorted-step (Calling.sorted cl) refl
        ; behind = scan-behind ρ cl ; lingers = scan-lingers ρ cl ; told = scan-told ρ cl ; ended = scan-ended ρ cl
        ; flags = scan-flags ρ cl ; kept = subst (_≼ loadOf st) (sym (scan-load ρ cl refl)) (Calling.kept cl) })
  call-scan st {m₁ = mach k clk tms ts} {T = T} {f = f} {z} {v} ρ {cp} cl
    with Calling.c cl | Calling.s cl | Calling.at cl | Calling.ctl cl | Calling.kernels cl | Calling.lifted cl | Calling.lefts cl
  ... | c | x | at | refl | kn | gn , S , L , sg , hl | lt with scan-at ρ {c = c} {x} at kn
  ...   | c₀ , refl , at₀ with lifts-split ρ (in-scan here) L in eqS
  ...     | _ , lifts-scan lifts-here , Lρ =
    rose {σ′ = ρ} {e′ = cp} (then refl now) (one-lower ρ one-scan)
      (record
        { sane = Calling.sane cl ; placed = Calling.placed cl ; ctl = refl ; at = at₀
        ; lifted = cong (mapᴹ (U.scanᶜ f z)) gn , S , Lρ , sg , healed-split ρ (in-scan here) hl
        ; lefts = lefts-up ρ (in-scan here) eqS lt ; rest-heads = Calling.rest-heads cl
        ; owned = owned-rise (Calling.owned cl) ; kernels = kn ; meaning = fed-same (λ _ _ _ → refl) T (Calling.meaning cl)
        ; queue = Calling.queue cl
        ; books = record { clocked = Books.clocked (Calling.books cl) ; ticked = Books.ticked (Calling.books cl) ; turned = Books.turned (Calling.books cl) }
        ; sorted = sorted-step (Calling.sorted cl) refl
        ; behind = Calling.behind cl ; lingers = Calling.lingers cl ; told = Calling.told cl ; ended = Calling.ended cl
        ; flags = done-up ρ (in-scan here) refl (Calling.flags cl) ; kept = Calling.kept cl })

  ------------------------------------------------------------------------
  -- THE CLIMB THROUGH A MAP: the signal mapped, the tree as it is.

  postulate
    -- A context climbing through a map, the map's own frame first.
    map-at : ∀ {Δ A B π} {T : Sub [] R} {f : A → B} {v : Sub Δ A} (ρ : Path T (mapˢ f v) π)
             {c : Ctx R Δ A} {x} → dirs c ≡ π ++ [ 0 ] → forget T ≡ plug c x
           → Σ (Ctx R Δ B) λ c₀ → c ≡ inMap f c₀ × dirs c₀ ≡ π

  call-map : ∀ {g m} (st : Strong g m) {m₁ Δ A B π} {T : Sub [] R} {f : A → B} {v : Sub Δ A} (ρ : Path T (mapˢ f v) π)
           → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ in-map here) e → Called st m₁ (ρ ⊕ in-map here)
  call-map st {m₁ = mach k clk tms ts} {T = T} {f = f} {v} ρ {nx y} cl
    with Calling.c cl | Calling.s cl | Calling.at cl | Calling.ctl cl | Calling.kernels cl | Calling.lifted cl | Calling.lefts cl
  ... | c | x | at | refl | kn | c′ , pv , S , L , sg | lt with map-at ρ {c = c} {x} at kn
  ...   | c₀ , refl , at₀ with lifts-split ρ (in-map here) L in eqS
  ...     | _ , lifts-map lifts-here , Lρ =
    rose {σ′ = ρ} {e′ = nx (f y)} (then refl now) (one-lower ρ one-map)
      (record
        { sane = Calling.sane cl ; placed = Calling.placed cl ; ctl = refl ; at = at₀
        ; lifted = U.mapᶜ f c′ , cong (mapᴹ (U.mapᶜ f)) pv , S , Lρ , sg
        ; lefts = lefts-up ρ (in-map here) eqS lt ; rest-heads = tt
        ; owned = owned-rise (Calling.owned cl) ; kernels = kn ; meaning = fed-same (λ _ _ _ → refl) T (Calling.meaning cl)
        ; queue = Calling.queue cl
        ; books = record { clocked = Books.clocked (Calling.books cl) ; ticked = Books.ticked (Calling.books cl) ; turned = Books.turned (Calling.books cl) }
        ; sorted = sorted-step (Calling.sorted cl) refl
        ; behind = Calling.behind cl ; lingers = Calling.lingers cl ; told = Calling.told cl ; ended = Calling.ended cl
        ; flags = done-up ρ (in-map here) refl (Calling.flags cl) ; kept = Calling.kept cl })
  call-map st {m₁ = mach k clk tms ts} {T = T} {f = f} {v} ρ {cp} cl
    with Calling.c cl | Calling.s cl | Calling.at cl | Calling.ctl cl | Calling.kernels cl | Calling.lifted cl | Calling.lefts cl
  ... | c | x | at | refl | kn | gn , S , L , sg , hl | lt with map-at ρ {c = c} {x} at kn
  ...   | c₀ , refl , at₀ with lifts-split ρ (in-map here) L in eqS
  ...     | _ , lifts-map lifts-here , Lρ =
    rose {σ′ = ρ} {e′ = cp} (then refl now) (one-lower ρ one-map)
      (record
        { sane = Calling.sane cl ; placed = Calling.placed cl ; ctl = refl ; at = at₀
        ; lifted = cong (mapᴹ (U.mapᶜ f)) gn , S , Lρ , sg , healed-split ρ (in-map here) hl
        ; lefts = lefts-up ρ (in-map here) eqS lt ; rest-heads = Calling.rest-heads cl
        ; owned = owned-rise (Calling.owned cl) ; kernels = kn ; meaning = fed-same (λ _ _ _ → refl) T (Calling.meaning cl)
        ; queue = Calling.queue cl
        ; books = record { clocked = Books.clocked (Calling.books cl) ; ticked = Books.ticked (Calling.books cl) ; turned = Books.turned (Calling.books cl) }
        ; sorted = sorted-step (Calling.sorted cl) refl
        ; behind = Calling.behind cl ; lingers = Calling.lingers cl ; told = Calling.told cl ; ended = Calling.ended cl
        ; flags = done-up ρ (in-map here) refl (Calling.flags cl) ; kept = Calling.kept cl })

  ------------------------------------------------------------------------
  -- THE CLIMB THROUGH A TAKEWHILE: a value passed, the take ended over
  -- it or out under it; an end as it is.

  postulate
    -- A context climbing through a takeWhile, the take's own frame first.
    take-at : ∀ {Δ A π} {T : Sub [] R} {i q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ i q tk v) π)
              {c : Ctx R Δ A} {x} → dirs c ≡ π ++ [ 0 ] → forget T ≡ plug c x
            → Σ (Ctx R Δ A) λ c₀ → c ≡ inTake i q c₀ × dirs c₀ ≡ π

    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Take.agda
    --
    -- DEAD ROUTE: the old body reads the take's liveness off a heap cell; the state tree holds it as the `Taking` stage.
    gone-take : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {i q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ i q tk v) π)
              → Calling g ℓ m₁ (ρ ⊕ in-take here) cp → part (takeWhileˢ i q tk v) ≡ nothing

    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Base.agda
    --
    -- DEAD ROUTE: the old bodies are heap writes of the take's liveness; the state tree's rise rewrites no node.
    take-pass : ∀ {g m} (st : Strong g m) {m₁ Δ A π} {T : Sub [] R} {i q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ i q tk v) π) {y}
              → q y ≡ true → Calling g (loadOf st) m₁ (ρ ⊕ in-take here) (nx y) → Called st m₁ (ρ ⊕ in-take here)
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Take.agda
    --
    -- DEAD ROUTE: the old body reads the take's liveness off a heap ref into the end's ghost (end-ghost); the state tree holds it as the `Taking` stage.
    take-out : ∀ {g m} (st : Strong g m) {m₁ Δ A π} {T : Sub [] R} {i q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ i q tk v) π) {y}
             → q y ≡ false → i ≡ true → Calling g (loadOf st) m₁ (ρ ⊕ in-take here) (nx y) → Called st m₁ (ρ ⊕ in-take here)
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Take.agda
    --
    -- DEAD ROUTE: the old body reads the take's liveness off a heap ref into the end's ghost (end-ghost); the state tree holds it as the `Taking` stage.
    take-end : ∀ {g m} (st : Strong g m) {m₁ Δ A π} {T : Sub [] R} {i q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ i q tk v) π) {y}
             → q y ≡ false → i ≡ false → Calling g (loadOf st) m₁ (ρ ⊕ in-take here) (nx y) → Called st m₁ (ρ ⊕ in-take here)

  call-take : ∀ {g m} (st : Strong g m) {m₁ Δ A π} {T : Sub [] R} {i q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ i q tk v) π)
            → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ in-take here) e → Called st m₁ (ρ ⊕ in-take here)
  call-take st {i = i} {q} ρ {nx y} cl with q y in qy | i
  ... | true  | _     = take-pass st ρ qy cl
  ... | false | true  = take-out st ρ qy refl cl
  ... | false | false = take-end st ρ qy refl cl
  call-take st {m₁ = mach k clk tms ts} {T = T} {i = i} {q} {tk} {v} ρ {cp} cl
    with Calling.c cl | Calling.s cl | Calling.at cl | Calling.ctl cl | Calling.kernels cl | Calling.lifted cl | Calling.lefts cl
  ... | c | x | at | refl | kn | gn , S , L , sg , hl | lt with take-at ρ {c = c} {x} at kn
  ...   | c₀ , refl , at₀ with lifts-split ρ (in-take here) L in eqS
  ...     | _ , lifts-take lifts-here , Lρ =
    rose {σ′ = ρ} {e′ = cp} (then refl now) (one-lower ρ one-take)
      (record
        { sane = Calling.sane cl ; placed = Calling.placed cl ; ctl = refl ; at = at₀
        ; lifted = gone-take ρ cl , S , Lρ , sg , healed-split ρ (in-take here) hl
        ; lefts = lefts-up ρ (in-take here) eqS lt ; rest-heads = Calling.rest-heads cl
        ; owned = owned-rise (Calling.owned cl) ; kernels = kn ; meaning = fed-same (λ _ _ _ → refl) T (Calling.meaning cl)
        ; queue = Calling.queue cl
        ; books = record { clocked = Books.clocked (Calling.books cl) ; ticked = Books.ticked (Calling.books cl) ; turned = Books.turned (Calling.books cl) }
        ; sorted = sorted-step (Calling.sorted cl) refl
        ; behind = Calling.behind cl ; lingers = Calling.lingers cl ; told = Calling.told cl ; ended = Calling.ended cl
        ; flags = done-up ρ (in-take here) refl (Calling.flags cl) ; kept = Calling.kept cl })

  ------------------------------------------------------------------------
  -- THE CLIMB THROUGH A CONNECT'S BODY: a value as it is; an end, the
  -- body's completion owed ahead of the agenda.

  postulate
    -- A context climbing through a connect's body, the body's own frame first.
    body-at : ∀ {Δ X B π} {T : Sub [] R} {k r ej rt} {s : Sub Δ X} {b : Sub (X ∷ Δ) B} (ρ : Path T (connectˢ k r ej rt s b) π)
              {c : Ctx R (X ∷ Δ) B} {x} → dirs c ≡ π ++ [ 1 ] → forget T ≡ plug c x
            → Σ (Ctx R Δ B) λ c₀ → c ≡ inBody k (forget s) c₀ × dirs c₀ ≡ π

  private
    -- A connect whose body is gone is gone.
    gone-connect : ∀ {Δ X B} {k r ej rt} {s : Sub Δ X} {b : Sub (X ∷ Δ) B} → part b ≡ nothing → part (connectˢ k r ej rt s b) ≡ nothing
    gone-connect gn rewrite gn = refl

    -- An end lifted out of a body is the connect's end.
    body-end : ∀ {Δ X B} {k r ej rt} {s : Sub Δ X} {b : Sub (X ∷ Δ) B} {q S}
             → Lifts (in-body {k = k} {r = r} {e = ej} {rt = rt} {s = s} (here {t = b})) (U.endˢ q) S → S ≡ U.endˢ q
    body-end (lifts-body _ _ lifts-here)   = refl
    body-end (lifts-shut _ _ _ lifts-here) = refl

  postulate
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Base.agda
    --
    -- DEAD ROUTE: the old body reads the body's rest off the heap's leftover; the state tree's leftover is `Strong`'s.
    body-rest-heads : ∀ {g ℓ m₁ Δ X B π} {T : Sub [] R} {k r ej rt} {s : Sub Δ X} {b : Sub (X ∷ Δ) B} (ρ : Path T (connectˢ k r ej rt s b) π)
                    → Calling g ℓ m₁ (ρ ⊕ in-body here) cp → ClosedHeads (Conf.pos (Mach.conf m₁)) ρ cp

    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Base.agda
    --
    -- DEAD ROUTE: the old body owes the body's cut on the heap's agenda; the state tree pushes the job onto `rets`.
    owned-body : ∀ {T : Sub [] R} {Δ X B} {c : Ctx R Δ B} {k o x p rs clk tms ts}
               → Owned T (mach ⟨ inBody {X = X} k o c , x , rising cp , p , rs ⟩ clk tms ts)
               → Owned T (mach ⟨ c , connS k o x , rising cp , p , (dirs c , owed , p) ∷ rs ⟩ clk tms ts)

    -- The meaning and the books with the body's completion owed.
    body-meaning : ∀ {T : Sub [] R} {Δ X B} {c : Ctx R Δ B} {k o x p rs}
                 → Meaning T ⟨ inBody {X = X} k o c , x , rising cp , p , rs ⟩
                 → Meaning T ⟨ c , connS k o x , rising cp , p , (dirs c , owed , p) ∷ rs ⟩
    body-books : ∀ {T : Sub [] R} {Δ X B} {c : Ctx R Δ B} {k o x p rs clk tms ts}
               → Books T (mach ⟨ inBody {X = X} k o c , x , rising cp , p , rs ⟩ clk tms ts)
               → Books T (mach ⟨ c , connS k o x , rising cp , p , (dirs c , owed , p) ∷ rs ⟩ clk tms ts)

  call-body : ∀ {g m} (st : Strong g m) {m₁ Δ X B π} {T : Sub [] R} {k r ej rt} {s : Sub Δ X} {b : Sub (X ∷ Δ) B}
              (ρ : Path T (connectˢ k r ej rt s b) π) → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ in-body here) e → Called st m₁ (ρ ⊕ in-body here)
  call-body st {m₁ = mach kk clk tms ts} {T = T} {r = r} {ej} {rt} ρ {nx y} cl
    with Calling.c cl | Calling.s cl | Calling.at cl | Calling.ctl cl | Calling.kernels cl | Calling.lifted cl | Calling.lefts cl
  ... | c | x | at | refl | kn | c′ , pv , S , L , sg | lt with body-at ρ {c = c} {x} at kn
  ...   | c₀ , refl , at₀ with lifts-split ρ (in-body here) L in eqS
  ...     | _ , lifts-body pt _ lifts-here , Lρ =
    rose {σ′ = ρ} {e′ = nx y} (then refl now) (one-lower ρ one-body)
      (record
        { sane = Calling.sane cl ; placed = Calling.placed cl ; ctl = refl ; at = at₀
        ; lifted = _ , cong₂ (connected r ej rt) pt pv , S , Lρ , sg
        ; lefts = lefts-up ρ (in-body here) eqS lt ; rest-heads = tt
        ; owned = owned-rise (Calling.owned cl) ; kernels = kn ; meaning = fed-same (λ _ _ _ → refl) T (Calling.meaning cl)
        ; queue = Calling.queue cl
        ; books = record { clocked = Books.clocked (Calling.books cl) ; ticked = Books.ticked (Calling.books cl) ; turned = Books.turned (Calling.books cl) }
        ; sorted = sorted-step (Calling.sorted cl) refl
        ; behind = Calling.behind cl ; lingers = Calling.lingers cl ; told = Calling.told cl ; ended = Calling.ended cl
        ; flags = done-up ρ (in-body here) refl (Calling.flags cl) ; kept = Calling.kept cl })
  ...     | _ , lifts-shut pt refl _ lifts-here , Lρ =
    rose {σ′ = ρ} {e′ = nx y} (then refl now) (one-lower ρ one-body)
      (record
        { sane = Calling.sane cl ; placed = Calling.placed cl ; ctl = refl ; at = at₀
        ; lifted = _ , cong₂ (connected r ej rt) pt pv , S , Lρ , sg
        ; lefts = lefts-up ρ (in-body here) eqS lt ; rest-heads = tt
        ; owned = owned-rise (Calling.owned cl) ; kernels = kn ; meaning = fed-same (λ _ _ _ → refl) T (Calling.meaning cl)
        ; queue = Calling.queue cl
        ; books = record { clocked = Books.clocked (Calling.books cl) ; ticked = Books.ticked (Calling.books cl) ; turned = Books.turned (Calling.books cl) }
        ; sorted = sorted-step (Calling.sorted cl) refl
        ; behind = Calling.behind cl ; lingers = Calling.lingers cl ; told = Calling.told cl ; ended = Calling.ended cl
        ; flags = done-up ρ (in-body here) refl (Calling.flags cl) ; kept = Calling.kept cl })
  call-body st {m₁ = mach kk clk tms ts} {T = T} {k = k} {r} {ej} {rt} {s} {b} ρ {cp} cl
    with Calling.c cl | Calling.s cl | Calling.at cl | Calling.ctl cl | Calling.kernels cl | Calling.lifted cl | Calling.lefts cl
  ... | c | x | at | refl | kn | gn , S , L , sg , hl | lt with body-at ρ {c = c} {x} at kn
  ...   | c₀ , refl , at₀ with lifts-split ρ (in-body here) L in eqB
  ...     | _ , Lb , Lρ =
    rose {σ′ = ρ} {e′ = cp} (then refl now) (one-lower ρ one-body)
      (record
        { sane = Calling.sane cl ; placed = Calling.placed cl ; ctl = refl ; at = at₀
        ; lifted = gone-connect {k = k} {r} {ej} {rt} {s} {b} gn , S , subst (λ w → Lifts ρ w S) (body-end Lb) Lρ , sg , healed-split ρ (in-body here) hl
        ; lefts = lefts-subst (λ w → w) (body-end Lb) (lefts-up ρ (in-body here) eqB lt) ; rest-heads = body-rest-heads ρ cl
        ; owned = owned-body (Calling.owned cl) ; kernels = kn ; meaning = body-meaning {T = T} {c = c₀} {k = k} {o = forget s} {x = x} (Calling.meaning cl)
        ; queue = Calling.queue cl ; books = body-books (Calling.books cl)
        ; sorted = sorted-step (Calling.sorted cl) refl
        ; behind = Calling.behind cl ; lingers = Calling.lingers cl ; told = Calling.told cl ; ended = Calling.ended cl
        ; flags = done-up ρ (in-body here) refl (Calling.flags cl) ; kept = Calling.kept cl })

  call-step : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub [] R} {u : Sub Δ A} {v : Sub Δ′ A′} {π τ}
              (ρ : Path T u π) {s : Path u v τ} → One s → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ s) e → Called st m₁ (ρ ⊕ s)
  call-step st ρ one-map         cl = call-map st ρ cl
  call-step st ρ one-scan        cl = call-scan st ρ cl
  call-step st ρ o@one-cut       cl = call-cut st ρ o cl
  call-step st ρ o@one-lane      cl = call-lane st ρ o cl
  call-step st ρ one-take        cl = call-take st ρ cl
  call-step st ρ o@one-outer     cl = call-outer st ρ o cl
  call-step st ρ o@(one-lanes _) cl = call-lanes st ρ o cl
  call-step st ρ o@one-source    cl = call-source st ρ o cl
  call-step st ρ one-body        cl = call-body st ρ cl

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
