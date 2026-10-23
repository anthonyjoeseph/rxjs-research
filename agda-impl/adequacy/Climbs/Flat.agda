{-# OPTIONS --guardedness #-}

-- THE CLIMB THROUGH A FLATMAP: a lane's value as it is; the end of the
-- last thing running, the flatMap planted done and its end climbing on;
-- every other end, and the outer's value, landing.
module adequacy.Climbs.Flat where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; [_]; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ; ++-conicalˡ; ++-conicalʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; pred; _<_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym; trans)

open import denotation.MonotonicList.Events using (Pos)
import denotation.Unfold as U
open import operation.PureObservable using (module Machine; module Driver)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Strong using (module Strongly)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Ghost.Paths using (module GhostingPaths)
open import adequacy.Moves using (module Moving)
open import adequacy.Replant.Keep using (module Keeping)
open import adequacy.Plugged using (module Plugging)
open import adequacy.Climbs using (module Ascending)
open Machine using (St; Ctx; Conf; Ev; nx; cp; dirs; plug; flatS; top; inOuter; inLanes; ⟨_,_,_,_,_⟩; rising) renaming (ended to endedᴹ)

module AscendingFlat (R : Set) where
  open Driver R using (Mach; mach; step; silent)
  open Unsubbing R using (now; then)
  open Strongly R using (Sub; Path; PathLanes; here; Strong; Owned; Meaning; Queue; Books; Each; Heads; Lingers; Untold; Ended; DoneBy;
    outers; outersL; part; partLanes; merged; consᴹ; forget; forgetᴸ; in-outer; in-lanes; this-lane; next-lane;
    pendingˢ; coldˢ; ofˢ; doneˢ; mapˢ; scanˢ; cutˢ; laneˢ; takeWhileˢ; flatMapˢ; connectˢ; joinˢ)
  open Moving R using (plantᴸ; planted)
  open Plugging R using (ctxAt; ctxAtᴸ; dirs-at; ctx-⊕; plant-plug; at-path)
  open Keeping R using (route-pre)
  open Ghosting R using (Hopped; _≼_; load; loadOf)
  open GhostingPaths R using (_⊕_; Lifts; LiftsLane; lifts-here; lifts-outer; lifts-lanes; lifts-this; lifts-next; lifts-split; lefts-up;
    OneLane; one-this; one-next; one-outer; one-lanes; one-lower; height)
  open Ascending R using (Called; Calling; ClosedHeads; LeftsOf; Passed; landed; rose; done-up; fed-same; height-planted; lifts-planted;
    owned-rise; sorted-step; heal; healing; heal-healed; lifts-healed; forget-heal; heal-height)

  ------------------------------------------------------------------------
  -- ONE LANE: a path into a flatMap's lanes one operator long

  -- The lane, of the flatMap's own type.
  data LaneOf {Γ A} {ls : List (Sub Γ A)} : ∀ {Δ B i π} {u : Sub Δ B} → PathLanes ls u i π → Set₁ where
    lane-of : ∀ {i} {u : Sub Γ A} {πL : PathLanes ls u i []} → LaneOf πL

  laneOf : ∀ {Γ A Δ B i π} {ls : List (Sub Γ A)} {u : Sub Δ B} {πL : PathLanes ls u i π} → OneLane πL → LaneOf πL
  laneOf one-this = lane-of
  laneOf (one-next ol) with laneOf ol
  ... | lane-of = lane-of

  -- The machine's lanes either side of it.
  lane-ctx : ∀ {Γ A i} {ls : List (Sub Γ A)} {u : Sub Γ A} (πL : PathLanes ls u i [])
             (F : List (St Γ A) → List (St Γ A) → Ctx R Γ A) (pre : List (St Γ A))
           → Σ (List (St Γ A)) λ bf → Σ (List (St Γ A)) λ af
             → ctxAtᴸ F pre πL ≡ F (pre ++ bf) af × (∀ w → forgetᴸ (plantᴸ πL w) ≡ bf ++ forget w ∷ af)
  lane-ctx (this-lane {ls = ls} here) F pre =
    [] , forgetᴸ ls , cong (λ z → F z (forgetᴸ ls)) (sym (++-identityʳ pre)) , λ _ → refl
  lane-ctx (next-lane {l = l} πL) F pre with lane-ctx πL F (pre ++ [ forget l ])
  ... | bf , af , e , h = forget l ∷ bf , af , trans e (cong (λ z → F z af) (++-assoc pre [ forget l ] bf)) , λ w → cong (forget l ∷_) (h w)

  lane-lifts : ∀ {Γ A i} {ls : List (Sub Γ A)} {u : Sub Γ A} (πL : PathLanes ls u i []) {s bs S as}
             → LiftsLane πL s bs S as → S ≡ s
  lane-lifts (this-lane here) (lifts-this lifts-here) = refl
  lane-lifts (next-lane πL)   (lifts-next L)          = lane-lifts πL L

  lane-outers : ∀ {Γ A i} {ls : List (Sub Γ A)} {u : Sub Γ A} (πL : PathLanes ls u i []) → outersL πL ≡ []
  lane-outers (this-lane here) = refl
  lane-outers (next-lane πL)   = lane-outers πL

  -- The parts of the lanes: the lane's own between those its lift reads
  -- before and after it.
  cons-++ : ∀ {X : Set₁} (x : Maybe X) (bs as : List X) → consᴹ x (bs ++ as) ≡ (consᴹ x [] ++ bs) ++ as
  cons-++ nothing  bs as = refl
  cons-++ (just x) bs as = refl

  lanes-live : ∀ {Γ A i} {ls : List (Sub Γ A)} {u : Sub Γ A} (πL : PathLanes ls u i []) {s bs S as c}
             → LiftsLane πL s bs S as → part u ≡ just c → partLanes ls ≡ bs ++ c ∷ as
  lanes-live (this-lane {ls = ls} here) (lifts-this lifts-here) pu = cong (λ z → consᴹ z (partLanes ls)) pu
  lanes-live (next-lane {l = l} πL)     (lifts-next L)          pu = trans (cong (consᴹ (part l)) (lanes-live πL L pu)) (cons-++ (part l) _ _)

  lanes-gone : ∀ {Γ A i} {ls : List (Sub Γ A)} {u : Sub Γ A} (πL : PathLanes ls u i []) {s bs S as}
             → LiftsLane πL s bs S as → part u ≡ nothing → partLanes ls ≡ bs ++ as
  lanes-gone (this-lane {ls = ls} here) (lifts-this lifts-here) pu = cong (λ z → consᴹ z (partLanes ls)) pu
  lanes-gone (next-lane {l = l} πL)     (lifts-next L)          pu = trans (cong (consᴹ (part l)) (lanes-gone πL L pu)) (cons-++ (part l) _ _)

  -- Planted with a node reading as the lane did, the lanes read alike.
  lanes-planted : ∀ {Γ A i} {ls : List (Sub Γ A)} {u : Sub Γ A} (πL : PathLanes ls u i []) (w : Sub Γ A)
                → part w ≡ part u → partLanes (plantᴸ πL w) ≡ partLanes ls
  lanes-planted (this-lane {ls = ls} here) w e = cong (λ z → consᴹ z (partLanes ls)) e
  lanes-planted (next-lane {l = l} πL)     w e = cong (consᴹ (part l)) (lanes-planted πL w e)

  -- A flatMap with a lane running is open; with nothing running, closed.
  merged-cons : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (o : Maybe (U.Node Γ A)) bs c as qs pl
              → merged op g o (bs ++ c ∷ as) qs pl ≡ just (U.flatMapᶜ op g o (bs ++ c ∷ as) qs pl)
  merged-cons op g (just _) bs       c as qs pl = refl
  merged-cons op g nothing  []       c as qs pl = refl
  merged-cons op g nothing  (_ ∷ _)  c as qs pl = refl

  merged-gone : ∀ {Γ A B op} {g : A → Pos → U.Node Γ B} {o : Maybe (U.Node Γ A)} {ls pl} → o ≡ nothing → ls ≡ []
              → merged op g o ls [] pl ≡ nothing
  merged-gone refl refl = refl

  ------------------------------------------------------------------------
  -- A LANE'S VALUE: as it is, the flatMap's own

  -- A context climbing through a flatMap's lanes, the lane's own frame
  -- first.
  lanes-at : ∀ {Γ X A π i} {T : Sub [] R} {op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
             (ρ : Path T (flatMapˢ op f d n qs pl o ls) π) (πL : PathLanes ls u i [])
             {c : Ctx R Γ A} {x} → dirs c ≡ π ++ [ suc i ] → forget T ≡ plug c x
           → Σ (List (St Γ A)) λ bf → Σ (List (St Γ A)) λ af
             → c ≡ inLanes op f d n qs (forget o) bf af (ctxAt top ρ) × x ≡ forget u
               × (∀ w → forgetᴸ (plantᴸ πL w) ≡ bf ++ forget w ∷ af)
  lanes-at {op = op} {f} {d} {n} {qs} {o = o} ρ πL {c} {x} dc e
    with lane-ctx πL (λ bf af → inLanes op f d n qs (forget o) bf af (ctxAt top ρ)) []
  ... | bf , af , ec , h =
    bf , af , trans (proj₁ (at-path (ρ ⊕ in-lanes πL) {c} {x} dc e)) (trans (ctx-⊕ top ρ (in-lanes πL)) ec)
    , proj₂ (at-path (ρ ⊕ in-lanes πL) {c} {x} dc e) , h

  lanes-out : ∀ {g m} (st : Strong g m) {m₁ Γ X A π i} {T : Sub [] R} {op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
              (ρ : Path T (flatMapˢ op f d n qs pl o ls) π) (πL : PathLanes ls u i []) → OneLane πL
            → ∀ {y} → Calling g (loadOf st) m₁ (ρ ⊕ in-lanes πL) (nx y) → Called st m₁ (ρ ⊕ in-lanes πL)
  lanes-out st {m₁ = mach k clk tms ts} {T = T} {op = op} {f} {qs = qs} {pl} {o} ρ πL ol {y} cl
    with Calling.c cl | Calling.s cl | Calling.at cl | Calling.ctl cl | Calling.kernels cl | Calling.lifted cl | Calling.lefts cl
  ... | c | x | at | refl | kn | c′ , pv , S , L , sg | lt with lanes-at ρ πL {c = c} {x} at kn
  ...   | bf , af , refl , refl , _ with lifts-split ρ (in-lanes πL) L in eqS
  ...     | _ , lifts-lanes {bs = bs} {as = as} LL _ _ _ , Lρ with lane-lifts πL LL
  ...       | refl =
    rose {σ′ = ρ} {e′ = nx y} (then refl now) (one-lower ρ (one-lanes ol))
      (record
        { sane = Calling.sane cl ; placed = Calling.placed cl ; ctl = refl ; at = dirs-at top ρ
        ; lifted = U.flatMapᶜ op g (part o) (bs ++ c′ ∷ as) qs pl
                 , trans (cong (λ ps → merged op g (part o) ps qs pl) (lanes-live πL LL pv)) (merged-cons op g (part o) bs c′ as qs pl)
                 , S , Lρ , sg
        ; lefts = lefts-up ρ (in-lanes πL) eqS lt ; rest-heads = tt
        ; owned = owned-rise (Calling.owned cl) ; kernels = kn ; meaning = fed-same (λ _ _ _ → refl) T (Calling.meaning cl)
        ; queue = Calling.queue cl
        ; books = record { clocked = Books.clocked (Calling.books cl) ; ticked = Books.ticked (Calling.books cl) ; turned = Books.turned (Calling.books cl) }
        ; sorted = sorted-step (Calling.sorted cl) refl
        ; behind = Calling.behind cl ; lingers = Calling.lingers cl ; told = Calling.told cl ; ended = Calling.ended cl
        ; flags = done-up ρ (in-lanes πL) (cong (map _) (lane-outers πL)) (Calling.flags cl)
        ; route = route-pre ρ (in-lanes πL) (Calling.route cl) ; kept = Calling.kept cl })
    where g = λ a r → U.subscribe (f a) r

  ------------------------------------------------------------------------
  -- THE LAST LANE'S END: the lane's node ended, the flatMap planted done,
  -- every connect it leaves gone staged to end there

  endedˢ : ∀ {Γ A} → Sub Γ A → Sub Γ A
  endedˢ (laneˢ b (cutˢ l a s)) = laneˢ b (cutˢ false a s)
  endedˢ s                      = s

  data Ends {Γ A} : Sub Γ A → Set₁ where
    ends-cut   : ∀ {b l a} {s : Sub Γ A} → Ends (laneˢ b (cutˢ l a s))
    ends-other : ∀ {s : Sub Γ A} → endedˢ s ≡ s → endedᴹ (forget s) ≡ forget s → Ends s

  ends : ∀ {Γ A} (s : Sub Γ A) → Ends s
  ends (laneˢ _ (cutˢ _ _ _))              = ends-cut
  ends (laneˢ _ (pendingˢ _ _))            = ends-other refl refl
  ends (laneˢ _ (coldˢ _ _))               = ends-other refl refl
  ends (laneˢ _ (ofˢ _ _ _))               = ends-other refl refl
  ends (laneˢ _ doneˢ)                     = ends-other refl refl
  ends (laneˢ _ (mapˢ _ _))                = ends-other refl refl
  ends (laneˢ _ (scanˢ _ _ _))             = ends-other refl refl
  ends (laneˢ _ (laneˢ _ _))               = ends-other refl refl
  ends (laneˢ _ (takeWhileˢ _ _ _ _))      = ends-other refl refl
  ends (laneˢ _ (flatMapˢ _ _ _ _ _ _ _ _)) = ends-other refl refl
  ends (laneˢ _ (connectˢ _ _ _ _ _ _))    = ends-other refl refl
  ends (laneˢ _ (joinˢ _ _ _ _))           = ends-other refl refl
  ends (pendingˢ _ _)                      = ends-other refl refl
  ends (coldˢ _ _)                         = ends-other refl refl
  ends (ofˢ _ _ _)                         = ends-other refl refl
  ends doneˢ                               = ends-other refl refl
  ends (mapˢ _ _)                          = ends-other refl refl
  ends (scanˢ _ _ _)                       = ends-other refl refl
  ends (cutˢ _ _ _)                        = ends-other refl refl
  ends (takeWhileˢ _ _ _ _)                = ends-other refl refl
  ends (flatMapˢ _ _ _ _ _ _ _ _)          = ends-other refl refl
  ends (connectˢ _ _ _ _ _ _)              = ends-other refl refl
  ends (joinˢ _ _ _ _)                     = ends-other refl refl

  forget-ended : ∀ {Γ A} (s : Sub Γ A) → forget (endedˢ s) ≡ endedᴹ (forget s)
  forget-ended s with ends s
  ... | ends-cut         = refl
  ... | ends-other e e′  = trans (cong forget e) (sym e′)

  part-ended : ∀ {Γ A} (s : Sub Γ A) → part s ≡ nothing → part (endedˢ s) ≡ nothing
  part-ended s ps with ends s
  ... | ends-cut       = refl
  ... | ends-other e _ = trans (cong part e) ps

  drained : ∀ {Γ X A π i} {T : Sub [] R} {op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
          → Path T (flatMapˢ op f d n qs pl o ls) π → PathLanes ls u i [] → Sub Γ A
  drained {op = op} {f} {n = n} {pl = pl} {o} {u = u} _ πL = flatMapˢ op f true (pred n) [] pl o (plantᴸ πL (endedˢ u))

  drainedAt : ∀ {Γ X A π i} {T : Sub [] R} {op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
            → Path T (flatMapˢ op f d n qs pl o ls) π → PathLanes ls u i [] → Pos → Sub [] R
  drainedAt ρ πL p = heal p (planted ρ (drained ρ πL))

  drain : ∀ {Γ X A π i} {T : Sub [] R} {op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
          (ρ : Path T (flatMapˢ op f d n qs pl o ls) π) (πL : PathLanes ls u i []) (p : Pos) → Path (drainedAt ρ πL p) (drained ρ πL) π
  drain ρ πL p = healing p (planted ρ (drained ρ πL))

  lanes-step : ∀ {Γ X A} {c₀ : Ctx R Γ A} {op} {f : X → _} {n o′ bf af x p rs clk tms ts} → pred n ≡ 0
             → step (mach ⟨ inLanes op f true n [] o′ bf af c₀ , x , rising cp , p , rs ⟩ clk tms ts)
               ≡ silent (mach ⟨ c₀ , flatS op f true (pred n) [] o′ (bf ++ endedᴹ x ∷ af) , rising cp , p , rs ⟩ clk tms ts)
  lanes-step {n = zero}        _ = refl
  lanes-step {n = suc zero}    _ = refl
  lanes-step {n = suc (suc _)} ()

  lanes-over : ∀ {Γ A B op} {g : A → Pos → U.Node Γ B} {o : Maybe (U.Node Γ A)} {bs l q as pl}
             → o ≡ nothing → bs ≡ [] → as ≡ [] → U.laneˢ op g o bs l (U.endˢ q) as [] pl ≡ U.endˢ q
  lanes-over refl refl refl = refl

  postulate
    -- The flatMap done, no lane but this one counted: its outer and
    -- every lane gone.
    lanes-drained : ∀ {g ℓ m₁ Γ X A π i} {T : Sub [] R} {op f n pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
                    (ρ : Path T (flatMapˢ op f true n [] pl o ls) π) (πL : PathLanes ls u i [])
                  → Calling g ℓ m₁ (ρ ⊕ in-lanes πL) cp → pred n ≡ 0 → part o ≡ nothing × partLanes ls ≡ []

  -- The last lane's end: from the flatMap planted done, lifted as the
  -- lane's was.
  lanes-end-lifts : ∀ {g ℓ m₁ Γ X A π i} {T : Sub [] R} {op f n pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
                    (ρ : Path T (flatMapˢ op f true n [] pl o ls) π) (πL : PathLanes ls u i [])
                  → (cl : Calling g ℓ m₁ (ρ ⊕ in-lanes πL) cp) → pred n ≡ 0
                  → Passed (Conf.pos (Mach.conf m₁)) g (drain ρ πL (Conf.pos (Mach.conf m₁))) cp
  lanes-end-lifts {m₁ = m₁} {u = u} ρ πL cl pn with Calling.lifted cl | lanes-drained ρ πL cl pn
  ... | pu , S , L , sg , _ | po , pls with lifts-split ρ (in-lanes πL) L
  ...   | _ , lifts-lanes {bs = bs} {as = as} LL _ _ _ , Lρ with lane-lifts πL LL
  ...     | refl =
    merged-gone po (trans (lanes-planted πL (endedˢ u) (trans (part-ended u pu) (sym pu))) pls) , S
    , lifts-healed p (planted ρ w)
        (lifts-planted ρ w (subst (λ z → Lifts ρ z S) (lanes-over po (++-conicalˡ bs as bas) (++-conicalʳ bs as bas)) Lρ))
    , sg , heal-healed p (planted ρ w)
    where p   = Conf.pos (Mach.conf m₁)
          w   = drained ρ πL
          bas = trans (sym (lanes-gone πL LL pu)) pls

  postulate
    -- What the last lane's end leaves free, left alike; and what the
    -- flatMap leaves running heads no earlier than the end.
    lanes-end-lefts : ∀ {g ℓ m₁ Γ X A π i} {T : Sub [] R} {op f n pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
                      (ρ : Path T (flatMapˢ op f true n [] pl o ls) π) (πL : PathLanes ls u i [])
                    → (cl : Calling g ℓ m₁ (ρ ⊕ in-lanes πL) cp) (pn : pred n ≡ 0)
                    → LeftsOf (Conf.pos (Mach.conf m₁)) g (drain ρ πL (Conf.pos (Mach.conf m₁))) cp (lanes-end-lifts ρ πL cl pn)
    lanes-end-rest-heads : ∀ {g ℓ m₁ Γ X A π i} {T : Sub [] R} {op f n pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
                           (ρ : Path T (flatMapˢ op f true n [] pl o ls) π) (πL : PathLanes ls u i [])
                         → Calling g ℓ m₁ (ρ ⊕ in-lanes πL) cp → pred n ≡ 0
                         → ClosedHeads (Conf.pos (Mach.conf m₁)) (drain ρ πL (Conf.pos (Mach.conf m₁))) cp

    -- The flatMap planted done, its connects staged: every held connect
    -- ended, every tie, every done flag.
    lanes-end-ended : ∀ {g ℓ m₁ Γ X A π i} {T : Sub [] R} {op f n pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
                      (ρ : Path T (flatMapˢ op f true n [] pl o ls) π) (πL : PathLanes ls u i [])
                    → Calling g ℓ m₁ (ρ ⊕ in-lanes πL) cp → pred n ≡ 0 → Ended (drainedAt ρ πL (Conf.pos (Mach.conf m₁)))
    lanes-end-lingers : ∀ {g ℓ m₁ Γ X A π i} {T : Sub [] R} {op f n pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
                        (ρ : Path T (flatMapˢ op f true n [] pl o ls) π) (πL : PathLanes ls u i [])
                      → Calling g ℓ m₁ (ρ ⊕ in-lanes πL) cp → pred n ≡ 0 → Lingers (drainedAt ρ πL (Conf.pos (Mach.conf m₁)))
    lanes-end-flags : ∀ {g ℓ m₁ Γ X A π i} {T : Sub [] R} {op f n pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
                      (ρ : Path T (flatMapˢ op f true n [] pl o ls) π) (πL : PathLanes ls u i [])
                    → Calling g ℓ m₁ (ρ ⊕ in-lanes πL) cp → pred n ≡ 0
                    → DoneBy (drainedAt ρ πL (Conf.pos (Mach.conf m₁))) (outers (drain ρ πL (Conf.pos (Mach.conf m₁))))

    -- The flatMap planted done: the jobs, the meaning, the queue, the
    -- books, the heads, the joiners told and the load.
    lanes-end-owned : ∀ {g ℓ m₁ Γ X A π i} {T : Sub [] R} {op f n pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
                      (ρ : Path T (flatMapˢ op f true n [] pl o ls) π) (πL : PathLanes ls u i [])
                    → Calling g ℓ m₁ (ρ ⊕ in-lanes πL) cp → pred n ≡ 0 → ∀ {m₂} → step m₁ ≡ silent m₂
                    → Owned (drainedAt ρ πL (Conf.pos (Mach.conf m₁))) m₂
    lanes-end-meaning : ∀ {g ℓ m₁ Γ X A π i} {T : Sub [] R} {op f n pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
                        (ρ : Path T (flatMapˢ op f true n [] pl o ls) π) (πL : PathLanes ls u i [])
                      → Calling g ℓ m₁ (ρ ⊕ in-lanes πL) cp → pred n ≡ 0 → ∀ {m₂} → step m₁ ≡ silent m₂
                      → Meaning (drainedAt ρ πL (Conf.pos (Mach.conf m₁))) (Mach.conf m₂)
    lanes-end-queue : ∀ {g ℓ m₁ Γ X A π i} {T : Sub [] R} {op f n pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
                      (ρ : Path T (flatMapˢ op f true n [] pl o ls) π) (πL : PathLanes ls u i [])
                    → Calling g ℓ m₁ (ρ ⊕ in-lanes πL) cp → pred n ≡ 0 → ∀ {m₂} → step m₁ ≡ silent m₂
                    → Queue (Conf.pos (Mach.conf m₂)) (Mach.clock m₂) (Mach.timers m₂) (drainedAt ρ πL (Conf.pos (Mach.conf m₁)))
    lanes-end-books : ∀ {g ℓ m₁ Γ X A π i} {T : Sub [] R} {op f n pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
                      (ρ : Path T (flatMapˢ op f true n [] pl o ls) π) (πL : PathLanes ls u i [])
                    → Calling g ℓ m₁ (ρ ⊕ in-lanes πL) cp → pred n ≡ 0 → ∀ {m₂} → step m₁ ≡ silent m₂
                    → Books (drainedAt ρ πL (Conf.pos (Mach.conf m₁))) m₂
    lanes-end-behind : ∀ {g ℓ m₁ Γ X A π i} {T : Sub [] R} {op f n pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
                       (ρ : Path T (flatMapˢ op f true n [] pl o ls) π) (πL : PathLanes ls u i [])
                     → Calling g ℓ m₁ (ρ ⊕ in-lanes πL) cp → pred n ≡ 0 → ∀ {m₂} → step m₁ ≡ silent m₂
                     → Each (Heads (Conf.pos (Mach.conf m₂))) (drainedAt ρ πL (Conf.pos (Mach.conf m₁)))
    lanes-end-told : ∀ {g ℓ m₁ Γ X A π i} {T : Sub [] R} {op f n pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
                     (ρ : Path T (flatMapˢ op f true n [] pl o ls) π) (πL : PathLanes ls u i [])
                   → Calling g ℓ m₁ (ρ ⊕ in-lanes πL) cp → pred n ≡ 0 → ∀ {m₂} → step m₁ ≡ silent m₂
                   → Untold (Conf.pos (Mach.conf m₂)) (drainedAt ρ πL (Conf.pos (Mach.conf m₁)))
    lanes-end-load : ∀ {g ℓ m₁ Γ X A π i} {T : Sub [] R} {op f n pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
                     (ρ : Path T (flatMapˢ op f true n [] pl o ls) π) (πL : PathLanes ls u i [])
                   → Calling g ℓ m₁ (ρ ⊕ in-lanes πL) cp → pred n ≡ 0 → ∀ {m₂} → step m₁ ≡ silent m₂
                   → load m₂ (drainedAt ρ πL (Conf.pos (Mach.conf m₁))) ≡ load m₁ T

    -- A lane's end leaving something running, or a value waiting: the
    -- waiting value's lane begun, or nothing more until the rest ends.
    lanes-dequeue : ∀ {g m} (st : Strong g m) {m₁ Γ X A π i} {T : Sub [] R} {op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
                    (ρ : Path T (flatMapˢ op f d n qs pl o ls) π) (πL : PathLanes ls u i [])
                  → Calling g (loadOf st) m₁ (ρ ⊕ in-lanes πL) cp → (qs ≡ [] → d ≡ true → pred n ≡ 0 → ⊥) → Hopped st m₁

  -- THE LAST LANE'S END: the end climbs on from the flatMap planted done.
  lanes-end : ∀ {g m} (st : Strong g m) {m₁ Γ X A π i} {T : Sub [] R} {op f n pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Γ A}
              (ρ : Path T (flatMapˢ op f true n [] pl o ls) π) (πL : PathLanes ls u i []) → OneLane πL → pred n ≡ 0
            → Calling g (loadOf st) m₁ (ρ ⊕ in-lanes πL) cp → Called st m₁ (ρ ⊕ in-lanes πL)
  lanes-end st {m₁ = mach k clk tms ts} {T = T} {op = op} {f} {n} {pl} {o} {ls} {u} ρ πL ol pn cl
    with Calling.c cl | Calling.s cl | Calling.at cl | Calling.ctl cl | Calling.kernels cl
  ... | c | x | at | refl | kn with lanes-at ρ πL {c = c} {x} at kn
  ...   | bf , af , refl , refl , fl =
    rose {σ′ = drain ρ πL (Calling.p cl)} {e′ = cp} (then st₁ now)
      (subst (_< height (ρ ⊕ in-lanes πL)) (sym (trans (heal-height _ (planted ρ w)) (height-planted ρ w))) (one-lower ρ (one-lanes ol)))
      (record
        { sane = Calling.sane cl ; placed = Calling.placed cl ; ctl = refl ; at = dirs-at top ρ
        ; lifted = lanes-end-lifts ρ πL cl pn ; lefts = lanes-end-lefts ρ πL cl pn ; rest-heads = lanes-end-rest-heads ρ πL cl pn
        ; owned = lanes-end-owned ρ πL cl pn st₁ ; kernels = trans (forget-heal _ (planted ρ w)) (plant-plug top ρ w)
        ; meaning = lanes-end-meaning ρ πL cl pn st₁
        ; queue = lanes-end-queue ρ πL cl pn st₁ ; books = lanes-end-books ρ πL cl pn st₁ ; sorted = sorted-step (Calling.sorted cl) st₁
        ; behind = lanes-end-behind ρ πL cl pn st₁ ; lingers = lanes-end-lingers ρ πL cl pn
        ; told = lanes-end-told ρ πL cl pn st₁ ; ended = lanes-end-ended ρ πL cl pn ; flags = lanes-end-flags ρ πL cl pn
        ; route = tt ; kept = subst (_≼ loadOf st) (sym (lanes-end-load ρ πL cl pn st₁)) (Calling.kept cl) })
    where w   = drained ρ πL
          st₁ = trans (lanes-step {c₀ = ctxAt top ρ} {op = op} {f} {n} {forget o} {bf} {af} {forget u} {Calling.p cl} {Calling.rs cl} {clk} {tms} {ts} pn)
                      (cong (λ ps → silent (mach ⟨ ctxAt top ρ , flatS op f true (pred n) [] (forget o) ps , rising cp , Calling.p cl , Calling.rs cl ⟩ clk tms ts))
                            (sym (trans (fl (endedˢ u)) (cong (λ z → bf ++ z ∷ af) (forget-ended u)))))

  lanes-cp : ∀ {g m} (st : Strong g m) {m₁ Γ X A π i} {T : Sub [] R} {op f} {d : Bool} {qs : List X} {n : ℕ} {pl} {o : Sub Γ X}
             {ls : List (Sub Γ A)} {u : Sub Γ A} (ρ : Path T (flatMapˢ op f d n qs pl o ls) π) (πL : PathLanes ls u i []) → OneLane πL
           → Calling g (loadOf st) m₁ (ρ ⊕ in-lanes πL) cp → Called st m₁ (ρ ⊕ in-lanes πL)
  lanes-cp st {d = true}  {qs = []}    {n = zero}        ρ πL ol cl = lanes-end st ρ πL ol refl cl
  lanes-cp st {d = true}  {qs = []}    {n = suc zero}    ρ πL ol cl = lanes-end st ρ πL ol refl cl
  lanes-cp st {d = true}  {qs = []}    {n = suc (suc _)} ρ πL ol cl = landed (lanes-dequeue st ρ πL cl λ _ _ ())
  lanes-cp st {d = true}  {qs = _ ∷ _}                   ρ πL ol cl = landed (lanes-dequeue st ρ πL cl λ ())
  lanes-cp st {d = false}                                ρ πL ol cl = landed (lanes-dequeue st ρ πL cl λ _ ())

  call-lanes : ∀ {g m} (st : Strong g m) {m₁ Γ X A Δ B i τ π} {T : Sub [] R} {op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
               {u : Sub Δ B} (ρ : Path T (flatMapˢ op f d n qs pl o ls) π) {πL : PathLanes ls u i τ} → OneLane πL
             → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ in-lanes πL) e → Called st m₁ (ρ ⊕ in-lanes πL)
  call-lanes st ρ ol {nx _} cl with laneOf ol
  ... | lane-of = lanes-out st ρ _ ol cl
  call-lanes st ρ ol {cp} cl with laneOf ol
  ... | lane-of = lanes-cp st ρ _ ol cl

  ------------------------------------------------------------------------
  -- THE OUTER'S END: with no lane running and nothing waiting, the
  -- flatMap planted done and its end climbing on

  -- A context climbing through a flatMap's outer, the outer's own frame
  -- first.
  outer-at : ∀ {Γ X A π} {T : Sub [] R} {op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
             (ρ : Path T (flatMapˢ op f d n qs pl o ls) π)
             {c : Ctx R Γ X} {x} → dirs c ≡ π ++ [ 0 ] → forget T ≡ plug c x
           → c ≡ inOuter op f d n qs (forgetᴸ ls) (ctxAt top ρ) × x ≡ forget o
  outer-at ρ {c} {x} dc e =
    trans (proj₁ (at-path (ρ ⊕ in-outer here) {c} {x} dc e)) (ctx-⊕ top ρ (in-outer here)) , proj₂ (at-path (ρ ⊕ in-outer here) {c} {x} dc e)

  spent : ∀ {Γ X A π} {T : Sub [] R} {op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
        → Path T (flatMapˢ op f d n qs pl o ls) π → Sub Γ A
  spent {op = op} {f} {n = n} {qs} {pl} {o} {ls} _ = flatMapˢ op f true n qs pl o ls

  spentAt : ∀ {Γ X A π} {T : Sub [] R} {op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
          → Path T (flatMapˢ op f d n qs pl o ls) π → Pos → Sub [] R
  spentAt ρ p = heal p (planted ρ (spent ρ))

  spend : ∀ {Γ X A π} {T : Sub [] R} {op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
          (ρ : Path T (flatMapˢ op f d n qs pl o ls) π) (p : Pos) → Path (spentAt ρ p) (spent ρ) π
  spend ρ p = healing p (planted ρ (spent ρ))

  outer-over : ∀ {Γ A B op} {g : A → Pos → U.Node Γ B} {o : U.Node Γ A} {ls q pl} → ls ≡ [] → U.outerˢ op g o (U.endˢ q) ls [] pl ≡ U.endˢ q
  outer-over refl = refl

  postulate
    -- The outer gone, no lane counted: every lane gone.
    outer-drained : ∀ {g ℓ m₁ Γ X A π} {T : Sub [] R} {op f d pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
                    (ρ : Path T (flatMapˢ op f d zero [] pl o ls) π)
                  → Calling g ℓ m₁ (ρ ⊕ in-outer here) cp → partLanes ls ≡ []

  -- The outer's end: from the flatMap planted done, lifted as the
  -- outer's was.
  outer-end-lifts : ∀ {g ℓ m₁ Γ X A π} {T : Sub [] R} {op f d pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
                    (ρ : Path T (flatMapˢ op f d zero [] pl o ls) π)
                  → (cl : Calling g ℓ m₁ (ρ ⊕ in-outer here) cp)
                  → Passed (Conf.pos (Mach.conf m₁)) g (spend ρ (Conf.pos (Mach.conf m₁))) cp
  outer-end-lifts {m₁ = m₁} ρ cl with Calling.lifted cl | outer-drained ρ cl
  ... | po , S , L , sg , _ | pls with lifts-split ρ (in-outer here) L
  ...   | _ , lifts-outer _ _ lifts-here , Lρ =
    merged-gone po pls , S
    , lifts-healed p (planted ρ w) (lifts-planted ρ w (subst (λ z → Lifts ρ z S) (outer-over pls) Lρ))
    , sg , heal-healed p (planted ρ w)
    where p = Conf.pos (Mach.conf m₁)
          w = spent ρ

  postulate
    -- What the outer's end leaves free, left alike; and what the flatMap
    -- leaves running heads no earlier than the end.
    outer-end-lefts : ∀ {g ℓ m₁ Γ X A π} {T : Sub [] R} {op f d pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
                      (ρ : Path T (flatMapˢ op f d zero [] pl o ls) π) (cl : Calling g ℓ m₁ (ρ ⊕ in-outer here) cp)
                    → LeftsOf (Conf.pos (Mach.conf m₁)) g (spend ρ (Conf.pos (Mach.conf m₁))) cp (outer-end-lifts ρ cl)
    outer-end-rest-heads : ∀ {g ℓ m₁ Γ X A π} {T : Sub [] R} {op f d pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
                           (ρ : Path T (flatMapˢ op f d zero [] pl o ls) π) → Calling g ℓ m₁ (ρ ⊕ in-outer here) cp
                         → ClosedHeads (Conf.pos (Mach.conf m₁)) (spend ρ (Conf.pos (Mach.conf m₁))) cp

    -- The flatMap planted done, its connects staged: every held connect
    -- ended, every tie, every done flag.
    outer-end-ended : ∀ {g ℓ m₁ Γ X A π} {T : Sub [] R} {op f d pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
                      (ρ : Path T (flatMapˢ op f d zero [] pl o ls) π) → Calling g ℓ m₁ (ρ ⊕ in-outer here) cp
                    → Ended (spentAt ρ (Conf.pos (Mach.conf m₁)))
    outer-end-lingers : ∀ {g ℓ m₁ Γ X A π} {T : Sub [] R} {op f d pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
                        (ρ : Path T (flatMapˢ op f d zero [] pl o ls) π) → Calling g ℓ m₁ (ρ ⊕ in-outer here) cp
                      → Lingers (spentAt ρ (Conf.pos (Mach.conf m₁)))
    outer-end-flags : ∀ {g ℓ m₁ Γ X A π} {T : Sub [] R} {op f d pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
                      (ρ : Path T (flatMapˢ op f d zero [] pl o ls) π) → Calling g ℓ m₁ (ρ ⊕ in-outer here) cp
                    → DoneBy (spentAt ρ (Conf.pos (Mach.conf m₁))) (outers (spend ρ (Conf.pos (Mach.conf m₁))))

    -- The flatMap planted done: the jobs, the meaning, the queue, the
    -- books, the heads, the joiners told and the load.
    outer-end-owned : ∀ {g ℓ m₁ Γ X A π} {T : Sub [] R} {op f d pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
                      (ρ : Path T (flatMapˢ op f d zero [] pl o ls) π) → Calling g ℓ m₁ (ρ ⊕ in-outer here) cp
                    → ∀ {m₂} → step m₁ ≡ silent m₂ → Owned (spentAt ρ (Conf.pos (Mach.conf m₁))) m₂
    outer-end-meaning : ∀ {g ℓ m₁ Γ X A π} {T : Sub [] R} {op f d pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
                        (ρ : Path T (flatMapˢ op f d zero [] pl o ls) π) → Calling g ℓ m₁ (ρ ⊕ in-outer here) cp
                      → ∀ {m₂} → step m₁ ≡ silent m₂ → Meaning (spentAt ρ (Conf.pos (Mach.conf m₁))) (Mach.conf m₂)
    outer-end-queue : ∀ {g ℓ m₁ Γ X A π} {T : Sub [] R} {op f d pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
                      (ρ : Path T (flatMapˢ op f d zero [] pl o ls) π) → Calling g ℓ m₁ (ρ ⊕ in-outer here) cp
                    → ∀ {m₂} → step m₁ ≡ silent m₂
                    → Queue (Conf.pos (Mach.conf m₂)) (Mach.clock m₂) (Mach.timers m₂) (spentAt ρ (Conf.pos (Mach.conf m₁)))
    outer-end-books : ∀ {g ℓ m₁ Γ X A π} {T : Sub [] R} {op f d pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
                      (ρ : Path T (flatMapˢ op f d zero [] pl o ls) π) → Calling g ℓ m₁ (ρ ⊕ in-outer here) cp
                    → ∀ {m₂} → step m₁ ≡ silent m₂ → Books (spentAt ρ (Conf.pos (Mach.conf m₁))) m₂
    outer-end-behind : ∀ {g ℓ m₁ Γ X A π} {T : Sub [] R} {op f d pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
                       (ρ : Path T (flatMapˢ op f d zero [] pl o ls) π) → Calling g ℓ m₁ (ρ ⊕ in-outer here) cp
                     → ∀ {m₂} → step m₁ ≡ silent m₂ → Each (Heads (Conf.pos (Mach.conf m₂))) (spentAt ρ (Conf.pos (Mach.conf m₁)))
    outer-end-told : ∀ {g ℓ m₁ Γ X A π} {T : Sub [] R} {op f d pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
                     (ρ : Path T (flatMapˢ op f d zero [] pl o ls) π) → Calling g ℓ m₁ (ρ ⊕ in-outer here) cp
                   → ∀ {m₂} → step m₁ ≡ silent m₂ → Untold (Conf.pos (Mach.conf m₂)) (spentAt ρ (Conf.pos (Mach.conf m₁)))
    outer-end-load : ∀ {g ℓ m₁ Γ X A π} {T : Sub [] R} {op f d pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
                     (ρ : Path T (flatMapˢ op f d zero [] pl o ls) π) → Calling g ℓ m₁ (ρ ⊕ in-outer here) cp
                   → ∀ {m₂} → step m₁ ≡ silent m₂ → load m₂ (spentAt ρ (Conf.pos (Mach.conf m₁))) ≡ load m₁ T

    -- The outer's end with a lane running or a value waiting: nothing
    -- more until the rest ends.
    outer-settle : ∀ {g m} (st : Strong g m) {m₁ Γ X A π} {T : Sub [] R} {op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
                   (ρ : Path T (flatMapˢ op f d n qs pl o ls) π)
                 → Calling g (loadOf st) m₁ (ρ ⊕ in-outer here) cp → (n ≡ 0 → qs ≡ [] → ⊥) → Hopped st m₁

    -- An outer value: admitted, its lane begun, queued or dropped.
    outer-admit : ∀ {g m} (st : Strong g m) {m₁ Γ X A π} {T : Sub [] R} {op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
                  (ρ : Path T (flatMapˢ op f d n qs pl o ls) π) {y}
                → Calling g (loadOf st) m₁ (ρ ⊕ in-outer here) (nx y) → Hopped st m₁

  -- THE OUTER'S END: the end climbs on from the flatMap planted done.
  outer-end : ∀ {g m} (st : Strong g m) {m₁ Γ X A π} {T : Sub [] R} {op f d pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
              (ρ : Path T (flatMapˢ op f d zero [] pl o ls) π)
            → Calling g (loadOf st) m₁ (ρ ⊕ in-outer here) cp → Called st m₁ (ρ ⊕ in-outer here)
  outer-end st {m₁ = mach k clk tms ts} {T = T} ρ cl
    with Calling.c cl | Calling.s cl | Calling.at cl | Calling.ctl cl | Calling.kernels cl
  ... | c | x | at | refl | kn with outer-at ρ {c = c} {x} at kn
  ...   | refl , refl =
    rose {σ′ = spend ρ (Calling.p cl)} {e′ = cp} (then st₁ now)
      (subst (_< height (ρ ⊕ in-outer here)) (sym (trans (heal-height _ (planted ρ w)) (height-planted ρ w))) (one-lower ρ one-outer))
      (record
        { sane = Calling.sane cl ; placed = Calling.placed cl ; ctl = refl ; at = dirs-at top ρ
        ; lifted = outer-end-lifts ρ cl ; lefts = outer-end-lefts ρ cl ; rest-heads = outer-end-rest-heads ρ cl
        ; owned = outer-end-owned ρ cl st₁ ; kernels = trans (forget-heal _ (planted ρ w)) (plant-plug top ρ w)
        ; meaning = outer-end-meaning ρ cl st₁
        ; queue = outer-end-queue ρ cl st₁ ; books = outer-end-books ρ cl st₁ ; sorted = sorted-step (Calling.sorted cl) st₁
        ; behind = outer-end-behind ρ cl st₁ ; lingers = outer-end-lingers ρ cl
        ; told = outer-end-told ρ cl st₁ ; ended = outer-end-ended ρ cl ; flags = outer-end-flags ρ cl
        ; route = tt ; kept = subst (_≼ loadOf st) (sym (outer-end-load ρ cl st₁)) (Calling.kept cl) })
    where w   = spent ρ
          st₁ = refl

  outer-cp : ∀ {g m} (st : Strong g m) {m₁ Γ X A π} {T : Sub [] R} {op f d} {n : ℕ} {qs : List X} {pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
             (ρ : Path T (flatMapˢ op f d n qs pl o ls) π)
           → Calling g (loadOf st) m₁ (ρ ⊕ in-outer here) cp → Called st m₁ (ρ ⊕ in-outer here)
  outer-cp st {n = zero}  {qs = []}    ρ cl = outer-end st ρ cl
  outer-cp st {n = zero}  {qs = _ ∷ _} ρ cl = landed (outer-settle st ρ cl λ _ ())
  outer-cp st {n = suc _}              ρ cl = landed (outer-settle st ρ cl λ ())

  call-outer : ∀ {g m} (st : Strong g m) {m₁ Γ X A π} {T : Sub [] R} {op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
               (ρ : Path T (flatMapˢ op f d n qs pl o ls) π)
             → ∀ {e} → Calling g (loadOf st) m₁ (ρ ⊕ in-outer here) e → Called st m₁ (ρ ⊕ in-outer here)
  call-outer st ρ {nx _} cl = landed (outer-admit st ρ cl)
  call-outer st ρ {cp}   cl = outer-cp st ρ cl
