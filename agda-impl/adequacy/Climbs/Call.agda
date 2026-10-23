{-# OPTIONS --guardedness #-}

module adequacy.Climbs.Call where

open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using ([]) renaming (lookup to lookupᴬ; map to mapᴬ)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-pred)
open import Data.Product using (_×_; _,_; Σ; proj₁)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong₂; trans)

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
open import adequacy.Plugged using (module Plugging)
open import adequacy.Climbs using (module Ascending)
open import adequacy.Climbs.Take using (module AscendingTake)
open import adequacy.Climbs.Flat using (module AscendingFlat)
open Machine using (St; Ctx; Conf; Job; Ev; nx; cp; dirs; plug; mapS; scanS; cutS; lnS; takeS; flatS; connS; owed; owedCp; owedCut; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody;
  ⟨_,_,_,_,_⟩; rising)

module AscendingCall (R : Set) where
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
  open Ascending R using (Aloft; Called; Calling; ClosedHeads; aloft; call-cut; call-lane; call-map; call-root; call-scan; call-source; done-up; fed-same; landed; owned-rise; rose; sorted-step)
  open AscendingTake R using (call-take)
  open AscendingFlat R using (call-lanes; call-outer)

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
  call-step st ρ one-outer       cl = call-outer st ρ cl
  call-step st ρ (one-lanes ol)  cl = call-lanes st ρ ol cl
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
