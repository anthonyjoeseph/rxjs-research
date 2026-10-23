{-# OPTIONS --guardedness #-}

module adequacy.Climbs.Take where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using ([]) renaming (lookup to lookupᴬ; map to mapᴬ)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Data.Maybe using (just; nothing; is-just)
open import Data.Nat using (_<_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym; trans)

open import denotation.MonotonicList.Events using (Pos; ix; last)
import denotation.Unfold as U
open import operation.PureObservable using (module Machine; module Driver)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Strong using (module Strongly)
open import adequacy.Sorted.Walk using (module SortingWalk)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Ghost.Paths using (module GhostingPaths)
open import adequacy.Moves using (module Moving)
open import adequacy.Frame using (module Framing)
open import adequacy.Replant using (module Replanting)
open import adequacy.Replant.Keep using (module Keeping)
open import adequacy.Leaves using (tw-refl)
open import adequacy.Plugged using (module Plugging)
open import adequacy.Climbs using (module Ascending)
open Machine using (St; Ctx; Conf; Job; Ev; nx; cp; dirs; plug; mapS; scanS; cutS; lnS; takeS; flatS; connS; owed; owedCp; owedCut; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody;
  ⟨_,_,_,_,_⟩; rising)

module AscendingTake (R : Set) where
  open Driver R using (Mach; mach; step; silent)
  open Unsubbing R using (_⇝_; now; then)
  open SortingWalk R using (WellMach; WellStep; silentʷ; preserve)
  open Strongly R using (Sub; Path; here; Strong; Carried; carried; closing; noteAs; Owned; Kernels; Meaning; Queue; Books;
    Each; Ahead; connected; Lingers; Untold; Ended; DoneBy; outers; outersL; part; leftover; forget; forgetᴸ; mapᴹ; Feed; owing; Fed; FedLanes;
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
    lifts-source; lifts-body; lifts-shut; lifts-this; lifts-next; lefts-subst; lifts-split; lefts-up; healed-split; Lefts; Healed; HealedL; One; whole; snoc; view;
    height; heightL; one-lower;
    one-map; one-scan; one-cut; one-lane; one-take; one-outer; one-lanes; one-source; one-body)
  open Ascending R using (Called; Calling; ClosedHeads; LeftsOf; Passed; done-up; fed-plant; fed-same; height-planted; lifts-planted; outers-planted; owned-rise; rose; sorted-step;
    heal; healing; heal-healed; lifts-healed; forget-heal; heal-height)

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
                    → Each (Ahead (Conf.pos (Mach.conf m₂))) (plant ρ (outed ρ cl))
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

  -- A non-inclusive take's failing value: the take gone, its end at
  -- `last`, every connect whose source it leaves gone staged to end there.
  take-end-step : ∀ {Δ A} {c₀ : Ctx R Δ A} {q : A → Bool} {x y p rs clk tms ts} → q y ≡ false
                → step (mach ⟨ inTake false q c₀ , x , rising (nx y) , p , rs ⟩ clk tms ts)
                  ≡ silent (mach ⟨ c₀ , takeS false q x , rising cp , p ++ [ last ] , (dirs c₀ , owedCut , p) ∷ rs ⟩ clk tms ts)
  take-end-step {q = q} {y = y} qy with q y
  take-end-step qy | false = refl

  fallen : ∀ {Γ A Δ B π} {t : Sub Γ A} {i q tk} {v : Sub Δ B} → Path t (takeWhileˢ i q tk v) π → Pos → Sub Γ A
  fallen {i = i} {q} {v = v} ρ p = heal (p ++ [ last ]) (planted ρ (takeWhileˢ i q taken v))

  fall : ∀ {Γ A Δ B π} {t : Sub Γ A} {i q tk} {v : Sub Δ B} (ρ : Path t (takeWhileˢ i q tk v) π) (p : Pos)
       → Path (fallen ρ p) (takeWhileˢ i q taken v) π
  fall {i = i} {q} {v = v} ρ p = healing (p ++ [ last ]) (planted ρ (takeWhileˢ i q taken v))

  -- A non-inclusive take's failing value: the take's end from the take
  -- planted gone, lifted as the value was.
  take-end-lifts : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ false q tk v) π) {y}
                 → q y ≡ false → (cl : Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y))
                 → Passed (Conf.pos (Mach.conf m₁) ++ [ last ]) g (fall ρ (Conf.pos (Mach.conf m₁))) cp
  take-end-lifts {m₁ = m₁} {q = q} {v = v} ρ {y} qy cl =
    let c₁ , pv , S , L , sg = Calling.lifted cl
        _ , Lσ , Lρ = lifts-split ρ (in-take here) L
        p = Conf.pos (Mach.conf m₁)
        w = takeWhileˢ false q taken v
    in take-shown {i = false} {q} {taken} {v} pv , S
       , lifts-healed (p ++ [ last ]) (planted ρ w)
           (lifts-planted ρ w (subst (λ x → Lifts ρ x S) (trans (take-one Lσ) (cong (U.taking false q p y c₁) qy)) Lρ))
       , sg , heal-healed (p ++ [ last ]) (planted ρ w)

  postulate
    -- What the take's end leaves free, left alike; and what its closed
    -- source leaves running heads no earlier than the end.
    take-end-lefts : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ false q tk v) π) {y}
                   → (qy : q y ≡ false) (cl : Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y))
                   → LeftsOf (Conf.pos (Mach.conf m₁) ++ [ last ]) g (fall ρ (Conf.pos (Mach.conf m₁))) cp (take-end-lifts ρ qy cl)
    take-end-rest-heads : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ false q tk v) π) {y}
                        → q y ≡ false → Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y)
                        → ClosedHeads (Conf.pos (Mach.conf m₁) ++ [ last ]) (fall ρ (Conf.pos (Mach.conf m₁))) cp

    -- The take gone, its connects staged: every held connect ended, every
    -- tie, every done flag.
    take-end-ended : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ false q tk v) π) {y}
                   → q y ≡ false → Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y) → Ended (fallen ρ (Conf.pos (Mach.conf m₁)))
    take-end-lingers : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ false q tk v) π) {y}
                     → q y ≡ false → Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y) → Lingers (fallen ρ (Conf.pos (Mach.conf m₁)))
    take-end-flags : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ false q tk v) π) {y}
                   → q y ≡ false → Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y)
                   → DoneBy (fallen ρ (Conf.pos (Mach.conf m₁))) (outers (fall ρ (Conf.pos (Mach.conf m₁))))

    -- The take gone, its source's cut owed: the jobs, the meaning, the
    -- queue, the books, the heads, the joiners told and the load.
    take-end-owned : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ false q tk v) π) {y}
                   → q y ≡ false → Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y) → ∀ {m₂} → step m₁ ≡ silent m₂
                   → Owned (fallen ρ (Conf.pos (Mach.conf m₁))) m₂
    take-end-meaning : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ false q tk v) π) {y}
                     → q y ≡ false → Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y) → ∀ {m₂} → step m₁ ≡ silent m₂
                     → Meaning (fallen ρ (Conf.pos (Mach.conf m₁))) (Mach.conf m₂)
    take-end-queue : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ false q tk v) π) {y}
                   → q y ≡ false → Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y) → ∀ {m₂} → step m₁ ≡ silent m₂
                   → Queue (Conf.pos (Mach.conf m₂)) (Mach.clock m₂) (Mach.timers m₂) (fallen ρ (Conf.pos (Mach.conf m₁)))
    take-end-books : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ false q tk v) π) {y}
                   → q y ≡ false → Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y) → ∀ {m₂} → step m₁ ≡ silent m₂
                   → Books (fallen ρ (Conf.pos (Mach.conf m₁))) m₂
    take-end-behind : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ false q tk v) π) {y}
                    → q y ≡ false → Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y) → ∀ {m₂} → step m₁ ≡ silent m₂
                    → Each (Ahead (Conf.pos (Mach.conf m₂))) (fallen ρ (Conf.pos (Mach.conf m₁)))
    take-end-told : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ false q tk v) π) {y}
                  → q y ≡ false → Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y) → ∀ {m₂} → step m₁ ≡ silent m₂
                  → Untold (Conf.pos (Mach.conf m₂)) (fallen ρ (Conf.pos (Mach.conf m₁)))
    take-end-load : ∀ {g ℓ m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ false q tk v) π) {y}
                  → q y ≡ false → Calling g ℓ m₁ (ρ ⊕ in-take here) (nx y) → ∀ {m₂} → step m₁ ≡ silent m₂
                  → load m₂ (fallen ρ (Conf.pos (Mach.conf m₁))) ≡ load m₁ T

  -- A NON-INCLUSIVE TAKE'S FAILING VALUE: the take's end climbs from the
  -- take planted gone, its source's cut owed.
  take-end : ∀ {g m} (st : Strong g m) {m₁ Δ A π} {T : Sub [] R} {q tk} {v : Sub Δ A} (ρ : Path T (takeWhileˢ false q tk v) π) {y}
           → q y ≡ false → Calling g (loadOf st) m₁ (ρ ⊕ in-take here) (nx y) → Called st m₁ (ρ ⊕ in-take here)
  take-end st {m₁ = mach k clk tms ts} {T = T} {q = q} {tk} {v} ρ {y} qy cl
    with Calling.c cl | Calling.s cl | Calling.at cl | Calling.ctl cl | Calling.kernels cl
  ... | c | x | at | refl | kn with take-at ρ {c = c} {x} at kn
  ...   | c₀ , refl , at₀ =
    rose {σ′ = fall ρ (Calling.p cl)} {e′ = cp} (then st₁ now)
      (subst (_< height (ρ ⊕ in-take here)) (sym (trans (heal-height _ (planted ρ w)) (height-planted ρ w))) (one-lower ρ one-take))
      (record
        { sane = Calling.sane cl ; placed = Calling.placed cl ; ctl = refl ; at = at₀
        ; lifted = take-end-lifts ρ qy cl ; lefts = take-end-lefts ρ qy cl ; rest-heads = take-end-rest-heads ρ qy cl
        ; owned = take-end-owned ρ qy cl st₁ ; kernels = trans (forget-heal _ (planted ρ w)) (take-kernels ρ {c₀ = c₀} {x} at₀ kn taken)
        ; meaning = take-end-meaning ρ qy cl st₁
        ; queue = take-end-queue ρ qy cl st₁ ; books = take-end-books ρ qy cl st₁ ; sorted = sorted-step (Calling.sorted cl) st₁
        ; behind = take-end-behind ρ qy cl st₁ ; lingers = take-end-lingers ρ qy cl
        ; told = take-end-told ρ qy cl st₁ ; ended = take-end-ended ρ qy cl ; flags = take-end-flags ρ qy cl
        ; route = tt ; kept = subst (_≼ loadOf st) (sym (take-end-load ρ qy cl st₁)) (Calling.kept cl) })
    where w   = takeWhileˢ false q taken v
          st₁ = take-end-step {c₀ = c₀} {q = q} {x = x} {y = y} {p = Calling.p cl} {rs = Calling.rs cl} {clk} {tms} {ts} qy


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
