{-# OPTIONS --guardedness #-}

-- THE CLIMB: a signal carried from its emitter up the context, each
-- operator's frame one rise, to a re-entry configuration.
module adequacy.Climbs where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; [_]; map)
open import Data.List.Properties using (++-conicalʳ)
open import Data.List.Relation.Unary.All using ([]) renaming (lookup to lookupᴬ; map to mapᴬ)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-pred)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂; sym; trans)

open import denotation.MonotonicList.Events using (Pos; ix; last)
open import denotation.MonotonicList using (agree-refl)
import denotation.Unfold as U
open import operation.PureObservable using (module Machine; module Driver)
open import adequacy.Sane using (Sane)
open import adequacy.Placed.Order using (Placed)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Strong using (module Strongly)
open import adequacy.Sorted.Walk using (module SortingWalk)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Ghost.Paths using (module GhostingPaths)
open import adequacy.Moves using (module Moving)
open import adequacy.Told using (untold)
open import adequacy.Frame using (module Framing)
open import adequacy.Replant using (module Replanting)
open import adequacy.Replant.Keep using (module Keeping)
open import adequacy.Leaves using (tw-refl)
open import adequacy.Plugged using (module Plugging)

open Machine using (St; Ctx; Conf; Job; Ev; nx; cp; dirs; plug; scanS; takeS; connS; owed; owedCp; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody;
  ⟨_,_,_,_,_⟩; rising)

module Ascending (R : Set) where
  open Driver R using (Mach; mach; step; silent)
  open Unsubbing R using (_⇝_; now; then)
  open SortingWalk R using (WellMach; WellStep; silentʷ; preserve)
  open Strongly R using (Sub; Path; here; Strong; Carried; carried; closing; noteAs; Owned; Kernels; Meaning; Queue; Books;
    Each; Heads; connected; Lingers; Untold; Ended; DoneBy; outers; outersL; part; leftover; forget; mapᴹ; Feed; owing; Fed; FedLanes;
    Begins; focused; attaching; PathLanes; this-lane; next-lane; in-map; in-scan; in-cut; in-lane; in-take; in-outer; in-lanes;
    in-source; in-body; pendingˢ; coldˢ; ofˢ; doneˢ; mapˢ; scanˢ; cutˢ; laneˢ; takeWhileˢ; flatMapˢ; connectˢ; joinˢ; pooledL; Timed; Joined; seen;
    Taking; taking; ending; taken; taking?; isTaking)
  open Moving R using (plant; plantᴸ; planted; plantedᴸ; replanted)
  open Framing R using (heads-scan)
  open Plugging R using (ctxAt; dirs-at; ctx-⊕; plant-plug; at-path)
  open Replanting R using (module Shift; Heading; Pred; ≡-⊑; map-fwd; map-back; each-scan; each-sub; lingers-sub; lg-scan; lg-take)
  open Keeping R using (module Keep; Alive; Route; route-pre; route-post; _≈_; same; ≈-scan; ≈-of; ≈-pending; ≈-cold; ≈-join; ≈-cut-of; ≈-take-of; ≈-take-cut;
    ≈-connect-of; Back)
  open Ghosting R using (Hopped; Load; _≼_; load; loadOf; hopped-pre; showing; agrees)
  open GhostingPaths R using (_⊕_; _⊕ᴸ_; Lifts; LiftsLane; lifts-here; lifts-map; lifts-scan; lifts-cut; lifts-lane; lifts-take; lifts-outer; lifts-lanes;
    lifts-source; lifts-body; lifts-shut; lifts-this; lifts-next; lefts-subst; lifts-split; lefts-up; healed-split; Lefts; Healed; One; whole; snoc; view;
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

  -- A value climbs a live route; an end may climb out of a node already
  -- past its end.
  Live : {T : Sub [] R} → ∀ {Δ A} {v : Sub Δ A} {π} → Path T v π → Ev A → Set
  Live σ (nx _) = Route σ
  Live σ cp     = ⊤

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
      route   : Live σ e
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
    -- DEAD ROUTE: the old body plants the inner on the heap's cells; the state tree's `admit` starts it in the flatMap's lanes.
    call-outer : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub [] R} {u : Sub Δ A} {v : Sub Δ′ A′} {π τ} (ρ : Path T u π) {s : Path u v τ}
               → One s → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ s) e → Called st m₁ (ρ ⊕ s)
    -- DEAD ROUTE: the old body frees the lane's heap slot; the state tree's `dequeue` starts the queue's head in place.
    call-lanes : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub [] R} {u : Sub Δ A} {v : Sub Δ′ A′} {π τ} (ρ : Path T u π) {s : Path u v τ}
               → One s → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ s) e → Called st m₁ (ρ ⊕ s)
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

    mutual
      outers-planted : ∀ {Γ A Δ B π} {t : Sub Γ A} {u : Sub Δ B} (ψ : Path t u π) (w : Sub Δ B) → outers (planted ψ w) ≡ outers ψ
      outers-planted here          w = refl
      outers-planted (in-map ψ)    w = cong (map (0 ∷_)) (outers-planted ψ w)
      outers-planted (in-scan ψ)   w = cong (map (0 ∷_)) (outers-planted ψ w)
      outers-planted (in-cut ψ)    w = cong (map (0 ∷_)) (outers-planted ψ w)
      outers-planted (in-lane ψ)   w = cong (map (0 ∷_)) (outers-planted ψ w)
      outers-planted (in-take ψ)   w = cong (map (0 ∷_)) (outers-planted ψ w)
      outers-planted (in-outer ψ)  w = cong (λ ns → [] ∷ map (0 ∷_) ns) (outers-planted ψ w)
      outers-planted (in-lanes {i = i} ψ) w = cong (map (suc i ∷_)) (outersL-planted ψ w)
      outers-planted (in-source ψ) w = cong (map (0 ∷_)) (outers-planted ψ w)
      outers-planted (in-body ψ)   w = cong (map (1 ∷_)) (outers-planted ψ w)

      outersL-planted : ∀ {Γ A Δ B i π} {ls : List (Sub Γ A)} {u : Sub Δ B} (ψ : PathLanes ls u i π) (w : Sub Δ B)
                      → outersL (plantedᴸ ψ w) ≡ outersL ψ
      outersL-planted (this-lane ψ) w = outers-planted ψ w
      outersL-planted (next-lane ψ) w = outersL-planted ψ w

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

  -- A context climbing through a scan, the scan's own frame first.
  scan-at : ∀ {Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π)
            {c : Ctx R Δ A} {x} → dirs c ≡ π ++ [ 0 ] → forget T ≡ plug c x
          → Σ (Ctx R Δ B) λ c₀ → c ≡ inScan f z c₀ × dirs c₀ ≡ π
  scan-at ρ d e = ctxAt top ρ , trans (proj₁ (at-path (ρ ⊕ in-scan here) d e)) (ctx-⊕ top ρ (in-scan here)) , dirs-at top ρ

  -- The tree with the scan's accumulator rewritten is the machine's.
  scan-kernels : ∀ {Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π)
                 {c₀ : Ctx R Δ B} {x} → dirs c₀ ≡ π → forget T ≡ plug c₀ (scanS f z x)
               → ∀ z′ → forget (plant ρ (scanˢ f z′ v)) ≡ plug c₀ (scanS f z′ x)
  scan-kernels ρ {c₀} d e z′ with at-path ρ {c = c₀} d e
  ... | refl , refl = plant-plug top ρ _

  -- A lift reads the frames' siblings, never the node it starts from:
  -- the same lift from wherever a node is planted.
  mutual
    lifts-planted : ∀ {Γ A Δ B π} {t : Sub Γ A} {u : Sub Δ B} (ψ : Path t u π) (w : Sub Δ B) {s S}
                  → Lifts ψ s S → Lifts (planted ψ w) s S
    lifts-planted here          w lifts-here                = lifts-here
    lifts-planted (in-map ψ)    w (lifts-map L)             = lifts-map (lifts-planted ψ w L)
    lifts-planted (in-scan ψ)   w (lifts-scan L)            = lifts-scan (lifts-planted ψ w L)
    lifts-planted (in-cut ψ)    w (lifts-cut e L)           = lifts-cut e (lifts-planted ψ w L)
    lifts-planted (in-lane ψ)   w (lifts-lane L)            = lifts-lane (lifts-planted ψ w L)
    lifts-planted (in-take ψ)   w (lifts-take L)            = lifts-take (lifts-planted ψ w L)
    lifts-planted (in-outer ψ)  w (lifts-outer of pb L)     = lifts-outer of pb (lifts-planted ψ w L)
    lifts-planted (in-lanes ψ)  w (lifts-lanes L ea lf pb)  = lifts-lanes (liftsL-planted ψ w L) ea lf pb
    lifts-planted (in-source ψ) w (lifts-source pb sf L)    = lifts-source pb sf (lifts-planted ψ w L)
    lifts-planted (in-body ψ)   w (lifts-body ps bf L)      = lifts-body ps bf (lifts-planted ψ w L)
    lifts-planted (in-body ψ)   w (lifts-shut ps pe rb L)   = lifts-shut ps pe rb (lifts-planted ψ w L)

    liftsL-planted : ∀ {Γ A Δ B i π} {ls : List (Sub Γ A)} {u : Sub Δ B} (ψ : PathLanes ls u i π) (w : Sub Δ B) {s bs S as}
                   → LiftsLane ψ s bs S as → LiftsLane (plantedᴸ ψ w) s bs S as
    liftsL-planted (this-lane ψ) w (lifts-this L) = lifts-this (lifts-planted ψ w L)
    liftsL-planted (next-lane ψ) w (lifts-next L) = lifts-next (liftsL-planted ψ w L)

  private
    -- A scan's own frame lifts a step by the scan.
    scan-one : ∀ {Δ A B} {f : B → A → B} {z} {v : Sub Δ A} {s S′} → Lifts (in-scan {f = f} {z = z} (here {t = v})) s S′ → S′ ≡ U.scanˢ f z s
    scan-one (lifts-scan lifts-here) = refl

  -- A value through a scan: the accumulated value from the scan planted
  -- with its new accumulator, lifted as the value was.
  scan-lifts : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
             → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y)
             → Passed (Conf.pos (Mach.conf m₁)) g (planted ρ (scanˢ f (f z y) v)) (nx (f z y))
  scan-lifts {f = f} {z} {v} ρ {y} cl =
    let c₁ , pv , S , L , sg = Calling.lifted cl
        _ , Lσ , Lρ = lifts-split ρ (in-scan here) L
    in U.scanᶜ f (f z y) c₁ , cong (mapᴹ (U.scanᶜ f (f z y))) pv , S
       , lifts-planted ρ (scanˢ f (f z y) v) (subst (λ x → Lifts ρ x S) (scan-one Lσ) Lρ) , sg

  postulate
    -- DEAD ROUTE: the old body reads the scan's leftover unchanged across a heap store (leftover-off over Off); a `plant` aliases nothing.
    scan-lefts : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
               → (cl : Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y))
               → LeftsOf (Conf.pos (Mach.conf m₁)) g (planted ρ (scanˢ f (f z y) v)) (nx (f z y)) (scan-lifts ρ cl)

    -- The books and the load, the accumulator rewritten.
    scan-books : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
               → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y) → ∀ {m₂} → step m₁ ≡ silent m₂
               → Books (plant ρ (scanˢ f (f z y) v)) m₂
    scan-load : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
              → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y) → ∀ {m₂} → step m₁ ≡ silent m₂
              → load m₂ (plant ρ (scanˢ f (f z y) v)) ≡ load m₁ T

  -- A SCAN'S ACCUMULATOR REWRITTEN: the node shows, ends, tells and
  -- flags as before, and heads as its source does.
  private
    rescan-told : ∀ {Γ A B C} (i : C ∈ᴸ Γ) {f : B → A → B} {z z′} (m : Maybe (U.Node Γ A)) {b₀ b′}
                → mapᴹ (U.scanᶜ f z) m ≡ just b₀ → mapᴹ (U.scanᶜ f z′) m ≡ just b′ → untold i b′ ≡ untold i b₀
    rescan-told i (just c) refl refl = refl

    rescan-root : ∀ {Γ A B q} {f : B → A → B} {z} {m : Maybe (U.Node Γ A)} → (∀ {c} → m ≡ just c → Heads q c)
                → ∀ {c} → mapᴹ (U.scanᶜ f z) m ≡ just c → Heads q c
    rescan-root {f = f} {z} {just c} h refl = heads-scan f z {c} (h refl)

    scan-heading : ∀ {Δ A B q} {f : B → A → B} {z z′} {v : Sub Δ A} {E : Pred Δ} → Heading q E (scanˢ f z v) (scanˢ f z′ v)
    scan-heading {v = v} = record
      { head-revive = λ j → map-fwd (part v) (map-back (part v) j)
      ; head-take   = λ j → j
      ; head-told   = λ i _ e₀ e′ → ≡-⊑ (rescan-told i (part v) e₀ e′)
      ; head-below  = λ ev → each-scan (rescan-root (Each.parts ev (in-scan here) refl)) (each-sub ev (in-scan here) refl) }

    scan-alive : ∀ {Δ A B} {f : B → A → B} {z z′} {v : Sub Δ A} → Alive (scanˢ f z v) (scanˢ f z′ v)
    scan-alive {v = v} = record
      { alive-back  = λ j → map-fwd (part v) (map-back (part v) j)
      ; alive-fwd   = λ j → map-fwd (part v) (map-back (part v) j)
      ; take-back   = λ j → j
      ; take-fwd    = λ j → j
      ; alive-ended = λ en → λ { (in-scan ψ) → en (in-scan ψ) }
      ; alive-flags = λ N fl → λ { (in-scan ψ) → fl (in-scan ψ) } }

    -- A scan beside its accumulator rewritten, every node under it the same.
    scan-back : ∀ {Δ A B} {f : B → A → B} {z z′} {v : Sub Δ A} → Back (scanˢ f z v) (scanˢ f z′ v)
    scan-back here        = _ , here , ≈-scan , λ e → e
    scan-back (in-scan ψ) = _ , in-scan ψ , same , λ e → e

    along : ∀ {Γ A Δ B π} {t : Sub Γ A} {x₀ x : Sub Δ B} → x₀ ≡ x → Path t x₀ π → Path t x π
    along refl ψ = ψ

    along-seen : ∀ {Γ A Δ B π} {t : Sub Γ A} {x₀ x : Sub Δ B} (e : x₀ ≡ x) (ψ : Path t x₀ π) → seen ψ ≡ true → seen (along e ψ) ≡ true
    along-seen refl ψ s = s

    -- Every job a tree's nodes owe, owed by the nodes beside them.
    owned-back : ∀ {T T′ : Sub [] R} {m} → Back T T′ → Owned T m → Owned T′ m
    owned-back bk o = record
      { ofs      = λ ψ → let x₀ , ψ₀ , b , h = bk ψ in Owned.ofs o (along (≈-of b) ψ₀)
      ; begun    = λ ψ → let x₀ , ψ₀ , b , h = bk ψ in Owned.begun o (along (≈-pending b) ψ₀)
      ; attached = λ ψ → let x₀ , ψ₀ , b , h = bk ψ in Owned.attached o (along (proj₂ (≈-cut-of b)) ψ₀)
      ; ends     = λ ψ → let x₀ , ψ₀ , b , h = bk ψ in Owned.ends o (along (proj₂ (≈-take-of b)) ψ₀)
      ; cuts     = λ ψ → let x₀ , ψ₀ , b , h = bk ψ in Owned.cuts o (along (proj₂ (≈-take-cut b)) ψ₀)
      ; feeds    = λ ψ → let x₀ , ψ₀ , b , h = bk ψ in Owned.feeds o (along (proj₂ (proj₂ (proj₂ (≈-connect-of b)))) ψ₀)
      ; bodies   = λ ψ → let x₀ , ψ₀ , b , h = bk ψ in Owned.bodies o (along (proj₂ (proj₂ (proj₂ (≈-connect-of b)))) ψ₀)
      ; sources  = λ ψ → let x₀ , ψ₀ , b , h = bk ψ in Owned.sources o (along (proj₂ (proj₂ (proj₂ (≈-connect-of b)))) ψ₀)
      ; owes     = λ ψ sn sl pn → let x₀ , ψ₀ , b , h = bk ψ ; s₀ , b₀ , nb , eq = ≈-connect-of b
                                  in Owned.owes o (along eq ψ₀) (along-seen eq ψ₀ (h sn)) sl (nb pn) }

    -- Every timer a cold's and every joiner in place, each node beside
    -- one of the other tree's both ways round.
    queue-back : ∀ {T T′ : Sub [] R} {p clk tms} → Back T T′ → Back T′ T → Queue p clk tms T → Queue p clk tms T′
    queue-back {T} {T′} bk fw q = record
      { timed = mapᴬ timed′ (Queue.timed q) ; joined = joined′ ; ordered = Queue.ordered q ; ahead = Queue.ahead q }
      where
        timed′ : ∀ {tm} → Timed T tm → Timed T′ tm
        timed′ (Γ , A , ph , b , ψ , w) = let x₀ , ψ₀ , c , h = fw ψ in Γ , A , ph , b , along (≈-cold c) ψ₀ , w

        joiner : ∀ {ρ} {sj : List ℕ × Pos}
               → Σ (List Set) (λ Δ → Σ Set λ A → Σ (A ∈ᴸ Δ) λ x → Σ (Maybe (List (Pos × Maybe A) × Maybe Pos)) λ st → Σ Bool λ g
                   → Path T (joinˢ {Δ} {A} (proj₂ sj) g x st) (ρ ++ proj₁ sj))
               → Σ (List Set) (λ Δ → Σ Set λ A → Σ (A ∈ᴸ Δ) λ x → Σ (Maybe (List (Pos × Maybe A) × Maybe Pos)) λ st → Σ Bool λ g
                   → Path T′ (joinˢ {Δ} {A} (proj₂ sj) g x st) (ρ ++ proj₁ sj))
        joiner (Δ , A , x , st , g , ψ) = let x₀ , ψ₀ , c , h = fw ψ in Δ , A , x , st , g , along (≈-join c) ψ₀

        joined′ : Joined T′
        joined′ ψ = let x₀ , ψ₀ , c , h = bk ψ ; s₀ , b₀ , nb , eq = ≈-connect-of c
                    in mapᴬ (λ {sj} j → joiner {sj = sj} j) (Queue.joined q (along eq ψ₀))

    -- What every joiner is owed, the node's joiners owed alike.
    mutual
      fed-plant : ∀ {k : Conf R} {Δ A} {u v : Sub Δ A} → (∀ {π ν} → Fed k u π ν → Fed k v π ν)
                → ∀ {Γ B π₀} {t : Sub Γ B} (ρ : Path t u π₀) {π ν} → Fed k t π ν → Fed k (plant ρ v) π ν
      fed-plant h here          d       = h d
      fed-plant h (in-map ρ)    d       = fed-plant h ρ d
      fed-plant h (in-scan ρ)   d       = fed-plant h ρ d
      fed-plant h (in-cut ρ)    d       = fed-plant h ρ d
      fed-plant h (in-lane ρ)   d       = fed-plant h ρ d
      fed-plant h (in-take ρ)   d       = fed-plant h ρ d
      fed-plant h (in-outer ρ)  (d , e) = fed-plant h ρ d , e
      fed-plant h (in-lanes ρ)  (d , e) = d , fedL-plant h ρ e
      fed-plant h (in-source ρ) (d , e) = fed-plant h ρ d , e
      fed-plant h (in-body ρ)   (d , e) = d , fed-plant h ρ e

      fedL-plant : ∀ {k : Conf R} {Δ A} {u v : Sub Δ A} → (∀ {π ν} → Fed k u π ν → Fed k v π ν)
                 → ∀ {Γ B i₀ π₀} {ls : List (Sub Γ B)} (ρ : PathLanes ls u i₀ π₀) {π i ν} → FedLanes k ls π i ν → FedLanes k (plantᴸ ρ v) π i ν
      fedL-plant h (this-lane ρ) (d , e) = fed-plant h ρ d , e
      fedL-plant h (next-lane ρ) (d , e) = d , fedL-plant h ρ e

  -- A value through a scan, the rewritten tree's heads, ends, joiners
  -- and flags.
  scan-behind : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
              → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y)
              → Each (Heads (Conf.pos (Mach.conf m₁))) (plant ρ (scanˢ f (f z y) v))
  scan-behind ρ cl = Shift.shift-behind ρ _ (Calling.told cl) (Calling.ended cl) scan-heading (Calling.behind cl)

  scan-told : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
            → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y) → Untold (Conf.pos (Mach.conf m₁)) (plant ρ (scanˢ f (f z y) v))
  scan-told ρ cl =
    Keep.shift-told ρ _ scan-alive scan-heading (λ _ ut → λ { (in-scan ψ) → ut (in-scan ψ) }) (Calling.told cl) (Calling.ended cl)

  scan-ended : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
             → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y) → Ended (plant ρ (scanˢ f (f z y) v))
  scan-ended ρ cl = Keep.shift-ended ρ _ scan-alive (Calling.ended cl)

  scan-flags : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
             → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y)
             → DoneBy (plant ρ (scanˢ f (f z y) v)) (outers (planted ρ (scanˢ f (f z y) v)))
  scan-flags {f = f} {z} {v} ρ {y} cl =
    subst (DoneBy (plant ρ w)) (sym (outers-planted ρ w)) (Keep.shift-flags ρ w scan-alive (done-up ρ (in-scan here) refl (Calling.flags cl)))
    where w = scanˢ f (f z y) v

  -- A value through a scan, the jobs owed, the joiners fed and the queue
  -- read off the rewritten tree, every node beside the tree's.
  scan-owned : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
             → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y) → ∀ {m₂} → step m₁ ≡ silent m₂
             → Owned (plant ρ (scanˢ f (f z y) v)) m₂
  scan-owned {m₁ = mach k clk tms ts} ρ cl e
    with Calling.c cl | Calling.s cl | Calling.at cl | Calling.ctl cl | Calling.kernels cl
  ... | c | x | at | refl | kn with scan-at ρ {c = c} {x} at kn
  ...   | c₀ , refl , at₀ with e
  ...     | refl = owned-back (Keep.back-planted ρ _ scan-alive ≈-scan scan-back) (owned-rise (Calling.owned cl))

  scan-meaning : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
               → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y) → ∀ {m₂} → step m₁ ≡ silent m₂
               → Meaning (plant ρ (scanˢ f (f z y) v)) (Mach.conf m₂)
  scan-meaning {m₁ = mach k clk tms ts} {T = T} ρ cl e
    with Calling.c cl | Calling.s cl | Calling.at cl | Calling.ctl cl | Calling.kernels cl
  ... | c | x | at | refl | kn with scan-at ρ {c = c} {x} at kn
  ...   | c₀ , refl , at₀ with e
  ...     | refl = fed-plant (λ d → d) ρ (fed-same (λ _ _ _ → refl) T (Calling.meaning cl))

  scan-queue : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
             → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y)
             → Queue (Conf.pos (Mach.conf m₁)) (Mach.clock m₁) (Mach.timers m₁) (plant ρ (scanˢ f (f z y) v))
  scan-queue {f = f} {z} {v} ρ {y} cl =
    queue-back (Keep.back-planted ρ w scan-alive ≈-scan scan-back)
      (subst (Back (plant ρ w)) (replanted ρ w) (Keep.back-planted (planted ρ w) (scanˢ f z v) scan-alive ≈-scan scan-back))
      (Calling.queue cl)
    where w = scanˢ f (f z y) v

  -- A held connect's leftover reads its running source's part, which the
  -- accumulator moves; a value's route reads none, every lane on it
  -- running, every outer unended, every source showing.
  scan-lingers : ∀ {g ℓ m₁ Δ A B π} {T : Sub [] R} {f : B → A → B} {z} {v : Sub Δ A} (ρ : Path T (scanˢ f z v) π) {y}
               → Calling g ℓ m₁ (ρ ⊕ in-scan here) (nx y) → Lingers (plant ρ (scanˢ f (f z y) v))
  scan-lingers ρ cl =
    Keep.route-lingers ρ _ scan-alive (route-pre ρ (in-scan here) (Calling.route cl)) (λ {ls} → tw-refl (pooledL ls))
      (λ lg → lg-scan (lingers-sub lg (in-scan here) refl)) (Calling.lingers cl)

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
        ; flags = scan-flags ρ cl ; route = Keep.route-planted ρ _ scan-alive (route-pre ρ (in-scan here) (Calling.route cl)) ; kept = subst (_≼ loadOf st) (sym (scan-load ρ cl refl)) (Calling.kept cl) })
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
        ; flags = done-up ρ (in-scan here) refl (Calling.flags cl) ; route = tt ; kept = Calling.kept cl })

  ------------------------------------------------------------------------
  -- THE CLIMB THROUGH A MAP: the signal mapped, the tree as it is.

  -- A context climbing through a map, the map's own frame first.
  map-at : ∀ {Δ A B π} {T : Sub [] R} {f : A → B} {v : Sub Δ A} (ρ : Path T (mapˢ f v) π)
           {c : Ctx R Δ A} {x} → dirs c ≡ π ++ [ 0 ] → forget T ≡ plug c x
         → Σ (Ctx R Δ B) λ c₀ → c ≡ inMap f c₀ × dirs c₀ ≡ π
  map-at ρ d e = ctxAt top ρ , trans (proj₁ (at-path (ρ ⊕ in-map here) d e)) (ctx-⊕ top ρ (in-map here)) , dirs-at top ρ

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
        ; flags = done-up ρ (in-map here) refl (Calling.flags cl) ; route = route-pre ρ (in-map here) (Calling.route cl) ; kept = Calling.kept cl })
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
        ; flags = done-up ρ (in-map here) refl (Calling.flags cl) ; route = tt ; kept = Calling.kept cl })

  ------------------------------------------------------------------------
  -- THE CLIMB THROUGH A TAKEWHILE: a value passed, the take ended over
  -- it or out under it; an end as it is.

  -- A context climbing through a takeWhile, the take's own frame first.
  take-at : ∀ {Δ A π} {T : Sub [] R} {i q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ i q tk v) π)
            {c : Ctx R Δ A} {x} → dirs c ≡ π ++ [ 0 ] → forget T ≡ plug c x
          → Σ (Ctx R Δ A) λ c₀ → c ≡ inTake i q c₀ × dirs c₀ ≡ π
  take-at ρ d e = ctxAt top ρ , trans (proj₁ (at-path (ρ ⊕ in-take here) d e)) (ctx-⊕ top ρ (in-take here)) , dirs-at top ρ

  postulate
    -- DEAD ROUTE: the old body reads the take's liveness off a heap cell; the state tree holds it as the `Taking` stage.
    gone-take : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {i q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ i q tk v) π)
              → Calling g ℓ m₁ (ρ ⊕ in-take here) cp → part (takeWhileˢ i q tk v) ≡ nothing

    -- DEAD ROUTE: the old bodies are heap writes of the take's liveness; the state tree's rise rewrites no node.
    take-pass : ∀ {g m} (st : Strong g m) {m₁ Δ A π} {T : Sub [] R} {i q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ i q tk v) π) {y}
              → q y ≡ true → Calling g (loadOf st) m₁ (ρ ⊕ in-take here) (nx y) → Called st m₁ (ρ ⊕ in-take here)
    -- DEAD ROUTE: the old body reads the take's liveness off a heap ref into the end's ghost (end-ghost); the state tree holds it as the `Taking` stage.
    take-end : ∀ {g m} (st : Strong g m) {m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ false q tk v) π) {y}
             → q y ≡ false → Calling g (loadOf st) m₁ (ρ ⊕ in-take here) (nx y) → Called st m₁ (ρ ⊕ in-take here)

  -- An inclusive take's failing value: shown, the take's completion owed
  -- where the value reached it.
  take-out-step : ∀ {Δ A} {c₀ : Ctx R Δ A} {q : A → Bool} {x y p rs clk tms ts} → q y ≡ false
                → step (mach ⟨ inTake true q c₀ , x , rising (nx y) , p , rs ⟩ clk tms ts)
                  ≡ silent (mach ⟨ c₀ , takeS true q x , rising (nx y) , p ++ [ ix 0 ] , (dirs c₀ , owedCp , p) ∷ rs ⟩ clk tms ts)
  take-out-step {q = q} {y = y} qy with q y
  take-out-step qy | false = refl

  private
    -- A take's own frame lifts a step by the take.
    take-one : ∀ {Δ A i q tk} {v : Sub Δ A} {s S′} → Lifts (in-take {i = i} {q} {tk = tk} (here {t = v})) s S′ → S′ ≡ U.takeWhileˢ i q s
    take-one (lifts-take lifts-here) = refl

    -- A take over a source showing shows by its stage alone.
    take-shown : ∀ {Γ A i q} {tk : Taking Γ A} {v : Sub Γ A} {c} → part v ≡ just c → part (takeWhileˢ i q tk v) ≡ taking? i q tk (just c)
    take-shown {i = i} {q} {tk} {pendingˢ _ _}                pv = cong (taking? i q tk) pv
    take-shown {i = i} {q} {tk} {coldˢ _ _}                   pv = cong (taking? i q tk) pv
    take-shown {i = i} {q} {tk} {ofˢ _ _ _}                   pv = cong (taking? i q tk) pv
    take-shown                  {v = doneˢ}                   ()
    take-shown {i = i} {q} {tk} {mapˢ _ _}                    pv = cong (taking? i q tk) pv
    take-shown {i = i} {q} {tk} {scanˢ _ _ _}                 pv = cong (taking? i q tk) pv
    take-shown {i = i} {q} {tk} {cutˢ true _ _}               pv = cong (taking? i q tk) pv
    take-shown                  {v = cutˢ false _ _}          ()
    take-shown {i = i} {q} {tk} {laneˢ _ _}                   pv = cong (taking? i q tk) pv
    take-shown {i = i} {q} {tk} {takeWhileˢ _ _ _ _}          pv = cong (taking? i q tk) pv
    take-shown {i = i} {q} {tk} {flatMapˢ _ _ _ _ _ _ _ _}    pv = cong (taking? i q tk) pv
    take-shown {i = i} {q} {tk} {connectˢ _ _ _ _ _ _}        pv = cong (taking? i q tk) pv
    take-shown {i = i} {q} {tk} {joinˢ _ _ _ _}               pv = cong (taking? i q tk) pv

    taking-of : ∀ {Γ A} {tk : Taking Γ A} → isTaking tk ≡ true → tk ≡ taking
    taking-of {tk = taking}     refl = refl
    taking-of {tk = ending _ _} ()
    taking-of {tk = taken}      ()

    -- A take past its failing value lives as it did; nothing under it is
    -- held any more.
    take-alive : ∀ {Δ A q k} {v : Sub Δ A} {c₁} → part v ≡ just c₁ → Alive (takeWhileˢ true q taking v) (takeWhileˢ true q (ending k c₁) v)
    take-alive {q = q} {k} {v} {c₁} pv = record
      { alive-back  = λ _ → cong is-just (take-shown {i = true} {q} {taking} {v} pv)
      ; alive-fwd   = λ _ → cong is-just (take-shown {i = true} {q} {ending k c₁} {v} pv)
      ; take-back   = λ j → j
      ; take-fwd    = λ j → j
      ; alive-ended = λ en → λ { (in-take ψ) () }
      ; alive-flags = λ N fl → λ { (in-take ψ) () } }

  -- The tree with the take's stage rewritten is the machine's.
  take-kernels : ∀ {Δ A π} {T : Sub [] R} {i q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ i q tk v) π)
                 {c₀ : Ctx R Δ A} {x} → dirs c₀ ≡ π → forget T ≡ plug c₀ (takeS i q x)
               → ∀ tk′ → forget (plant ρ (takeWhileˢ i q tk′ v)) ≡ plug c₀ (takeS i q x)
  take-kernels ρ {c₀} d e tk′ with at-path ρ {c = c₀} d e
  ... | refl , refl = plant-plug top ρ _

  -- The take past the value climbing it, its completion owed where the
  -- value reached it.
  outed : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {i q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ i q tk v) π) {y}
        → Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y) → Sub Δ A
  outed {m₁ = m₁} {i = i} {q} {v = v} ρ cl = takeWhileˢ i q (ending (Conf.pos (Mach.conf m₁)) (proj₁ (Calling.lifted cl))) v

  -- An inclusive take's failing value: from the take planted past it,
  -- lifted as the value was.
  take-out-lifts : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ true q tk v) π) {y}
                 → q y ≡ false → (cl : Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y))
                 → Passed (Conf.pos (Mach.conf m₁) ++ [ ix 0 ]) g (planted ρ (outed ρ cl)) (nx y)
  take-out-lifts {m₁ = m₁} {q = q} {v = v} ρ {y} qy cl =
    let c₁ , pv , S , L , sg = Calling.lifted cl
        _ , Lσ , Lρ = lifts-split ρ (in-take here) L
        p = Conf.pos (Mach.conf m₁)
    in U.endingᶜ (p ++ [ last ]) c₁ , take-shown {i = true} {q} {ending p c₁} {v} pv , S
       , lifts-planted ρ (outed ρ cl) (subst (λ x → Lifts ρ x S) (trans (take-one Lσ) (cong (U.taking true q p y c₁) qy)) Lρ) , sg

  postulate
    -- What the take past its failing value leaves free, left alike.
    take-out-lefts : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ true q tk v) π) {y}
                   → (qy : q y ≡ false) (cl : Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y))
                   → LeftsOf (Conf.pos (Mach.conf m₁) ++ [ ix 0 ]) g (planted ρ (outed ρ cl)) (nx y) (take-out-lifts ρ qy cl)

    -- The take past its failing value, its completion owed: the jobs, the
    -- queue, the books, the heads, the joiners told and the load.
    take-out-owned : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ true q tk v) π) {y}
                   → q y ≡ false → (cl : Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y)) → ∀ {m₂} → step m₁ ≡ silent m₂
                   → Owned (plant ρ (outed ρ cl)) m₂
    take-out-queue : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ true q tk v) π) {y}
                   → q y ≡ false → (cl : Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y)) → ∀ {m₂} → step m₁ ≡ silent m₂
                   → Queue (Conf.pos (Mach.conf m₂)) (Mach.clock m₂) (Mach.timers m₂) (plant ρ (outed ρ cl))
    take-out-books : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ true q tk v) π) {y}
                   → q y ≡ false → (cl : Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y)) → ∀ {m₂} → step m₁ ≡ silent m₂
                   → Books (plant ρ (outed ρ cl)) m₂
    take-out-behind : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ true q tk v) π) {y}
                    → q y ≡ false → (cl : Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y)) → ∀ {m₂} → step m₁ ≡ silent m₂
                    → Each (Heads (Conf.pos (Mach.conf m₂))) (plant ρ (outed ρ cl))
    take-out-told : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ true q tk v) π) {y}
                  → q y ≡ false → (cl : Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y)) → ∀ {m₂} → step m₁ ≡ silent m₂
                  → Untold (Conf.pos (Mach.conf m₂)) (plant ρ (outed ρ cl))
    take-out-load : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ true q tk v) π) {y}
                  → q y ≡ false → (cl : Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y)) → ∀ {m₂} → step m₁ ≡ silent m₂
                  → load m₂ (plant ρ (outed ρ cl)) ≡ load m₁ T

  -- AN INCLUSIVE TAKE'S FAILING VALUE: the value climbs on from the take
  -- planted past it, its route still taking, the take's completion owed.
  take-out : ∀ {g m} (st : Strong g m) {m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ true q tk v) π) {y}
           → q y ≡ false → Calling g (loadOf st) m₁ (ρ ⊕ in-take here) (nx y) → Called st m₁ (ρ ⊕ in-take here)
  take-out st {m₁ = mach k clk tms ts} {T = T} {q = q} {tk} {v} ρ {y} qy cl
    with Calling.c cl | Calling.s cl | Calling.at cl | Calling.ctl cl | Calling.kernels cl
  ... | c | x | at | refl | kn with take-at ρ {c = c} {x} at kn
  ...   | c₀ , refl , at₀ with taking-of (proj₁ (route-post ρ (in-take here) (Calling.route cl)))
  ...     | refl =
    rose {σ′ = planted ρ w} {e′ = nx y} (then st₁ now)
      (subst (_< height (ρ ⊕ in-take here)) (sym (height-planted ρ w)) (one-lower ρ one-take))
      (record
        { sane = Calling.sane cl ; placed = Calling.placed cl ; ctl = refl ; at = at₀
        ; lifted = take-out-lifts ρ qy cl ; lefts = take-out-lefts ρ qy cl ; rest-heads = tt
        ; owned = take-out-owned ρ qy cl st₁ ; kernels = take-kernels ρ {c₀ = c₀} {x} at₀ kn _
        ; meaning = fed-plant (λ d → d) ρ (fed-same (λ _ _ _ → refl) T (Calling.meaning cl))
        ; queue = take-out-queue ρ qy cl st₁ ; books = take-out-books ρ qy cl st₁ ; sorted = sorted-step (Calling.sorted cl) st₁
        ; behind = take-out-behind ρ qy cl st₁
        ; lingers = Keep.route-lingers ρ w alive rt (λ {ls} → tw-refl (pooledL ls)) (λ _ → lg-take (λ ())) (Calling.lingers cl)
        ; told = take-out-told ρ qy cl st₁ ; ended = Keep.shift-ended ρ w alive (Calling.ended cl)
        ; flags = subst (DoneBy (plant ρ w)) (sym (outers-planted ρ w)) (Keep.shift-flags ρ w alive (done-up ρ (in-take here) refl (Calling.flags cl)))
        ; route = Keep.route-planted ρ w alive rt ; kept = subst (_≼ loadOf st) (sym (take-out-load ρ qy cl st₁)) (Calling.kept cl) })
    where w     = outed ρ cl
          st₁   = take-out-step {c₀ = c₀} {q = q} {x = x} {y = y} {p = Calling.p cl} {rs = Calling.rs cl} {clk} {tms} {ts} qy
          alive = take-alive {q = q} (proj₁ (proj₂ (Calling.lifted cl)))
          rt    = route-pre ρ (in-take here) (Calling.route cl)

  call-take : ∀ {g m} (st : Strong g m) {m₁ Δ A π} {T : Sub [] R} {i q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ i q tk v) π)
            → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ in-take here) e → Called st m₁ (ρ ⊕ in-take here)
  call-take st {i = i} {q} ρ {nx y} cl with q y in qy | i
  ... | true  | _     = take-pass st ρ qy cl
  ... | false | true  = take-out st ρ qy cl
  ... | false | false = take-end st ρ qy cl
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
        ; flags = done-up ρ (in-take here) refl (Calling.flags cl) ; route = tt ; kept = Calling.kept cl })

  ------------------------------------------------------------------------
  -- THE CLIMB THROUGH A CONNECT'S BODY: a value as it is; an end, the
  -- body's completion owed ahead of the agenda.

  -- A context climbing through a connect's body, the body's own frame first.
  body-at : ∀ {Δ X B π} {T : Sub [] R} {k r ej rt} {s : Sub Δ X} {b : Sub (X ∷ Δ) B} (ρ : Path T (connectˢ k r ej rt s b) π)
            {c : Ctx R (X ∷ Δ) B} {x} → dirs c ≡ π ++ [ 1 ] → forget T ≡ plug c x
          → Σ (Ctx R Δ B) λ c₀ → c ≡ inBody k (forget s) c₀ × dirs c₀ ≡ π
  body-at ρ d e = ctxAt top ρ , trans (proj₁ (at-path (ρ ⊕ in-body here) d e)) (ctx-⊕ top ρ (in-body here)) , dirs-at top ρ

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
    -- DEAD ROUTE: the old body reads the body's rest off the heap's leftover; the state tree's leftover is `Strong`'s.
    body-rest-heads : ∀ {g ℓ m₁ Δ X B π} {T : Sub [] R} {k r ej rt} {s : Sub Δ X} {b : Sub (X ∷ Δ) B} (ρ : Path T (connectˢ k r ej rt s b) π)
                    → Calling g ℓ m₁ (ρ ⊕ in-body here) cp → ClosedHeads (Conf.pos (Mach.conf m₁)) ρ cp

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
        ; flags = done-up ρ (in-body here) refl (Calling.flags cl) ; route = route-pre ρ (in-body here) (Calling.route cl) ; kept = Calling.kept cl })
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
        ; flags = done-up ρ (in-body here) refl (Calling.flags cl) ; route = route-pre ρ (in-body here) (Calling.route cl) ; kept = Calling.kept cl })
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
        ; flags = done-up ρ (in-body here) refl (Calling.flags cl) ; route = tt ; kept = Calling.kept cl })

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
