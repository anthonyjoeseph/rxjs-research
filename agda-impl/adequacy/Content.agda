{-# OPTIONS --guardedness #-}

-- CONTENT: the root's record is the meaning's events, as a set.
-- Sortedness (`adequacy.Sorted`) says nothing of WHAT arrives; this
-- says nothing of the ORDER, so neither proof reads the other.
--
-- A GHOST: the meaning's own configuration (`denotation.Unfold`'s
-- `Node`), which the machine's configuration runs.  What is still to be
-- delivered is the ghost's residual, its meaning (`U.meaning`); at the
-- launch the ghost is the program subscribed there, so the residual is
-- the meaning's events (`begun`, by `subscribed`).  Each step keeps the
-- residual or delivers a least event of it (`Shows`).  No step of the
-- machine is matched to a step of a stepper.  Only the run's re-entry
-- configurations are related to the ghost (`Strong`); every other is
-- reached from one by its own silent steps.
module adequacy.Content where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; length; reverse; _ʳ++_; map)
open import Data.List.Properties using (++-identityʳ; map-++; reverse-involutive; ʳ++-defn)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁻ʳ)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl; <-trans; ≤-<-trans; m≤n⇒m≤1+n)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Tree using (Obs; Later; defer; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Timeline; Events; Events∞; Pos; Time; tick; root; out; end; hush; ix; _<ᵖ_; <ᵖ-irrefl;
  <ᵖ-asym; emit; stall; close; last; Frame∞; From; From∞; idle; done; at; _∪_) renaming (quiet to silentᶠ)
open import denotation.MonotonicList using (MonotonicList; admit; enter; head; cuts; Agreeᵀ; Agree; agree-refl; agree-sym; agree-trans;
  agreeᵀ-refl; agreeᵀ-sym; agreeᵀ-trans; frames; _≈[_]_)
open import denotation.NonExpansive using (_,ˢ_; Lanes; ∪-ne)
open import denotation.Compositional using (env-refl)
open import adequacy.Record using (Ahead; outᵃ; skipᵃ; endᵃ; hushᵃ) renaming (none to noneᵃ)
import denotation.Unfold as U
open import denotation.Denote using (flatOp)
open import operation.PureObservable using (PureObs; module Driver; module Machine; module Pure; play; ending; over) renaming (rest to restᵀ)
open import adequacy.Sorted using (_≤ᵖ_)
open import adequacy.Sane using (Sane; SaneS; step-sane; sane-out)
open import adequacy.Placed.Order using (Placed)
open import adequacy.Placed.Trail using (t≢f; SortedT; sortedT-idle; sortedT-∪)
open import adequacy.Stepper.Past using (_≃_; Placedˢ)
open import adequacy.Stepper.Within using (placed-after)
open import adequacy.Stepper using (step-skips)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Engine.Drop using (Drops; drop; drops; Dropsˢ; dropˢ; Pass; lift-drops; outer-admits; lane-admits; ≋-⊒; Eraseᴱ; stopᴱ; outᴱ;
  skipᴱ; erasedᴱ; endᴱ; hushᴱ)
open import adequacy.Engine.Union using (∪-idleᵀ; ∪-assocᵀ; ∪-commᵀ)
open import adequacy.Engine.Meaning using (M; flagOf; envAt; risen; gh; lane; laneᴹ; lanesL; deadL; deadOne; outerFrame; lanesFrame; laneRuns; poolRuns; poolT; tailsOn; outerT; holeT; lanes-refl; Has; atOut; atEnd; pastOut; _≅_; ≅-refl; ≅-sym; ≅-trans; agree-≅; ≋-by)
open import adequacy.Engine.Inv using (Inv; module Inv; module Base; wfI; search-hit; NextInv; inv-next)
open import adequacy.Engine.Spent using (module Spending)
open import adequacy.Engine.Kept using (KeptFrom; refocus-agree; rests-++; lanes-runs; pool-runs; dead-hole) renaming (kept to engine-kept)
open import adequacy.Engine.Head using (Frag; Lane) renaming (Lanes to Lanesᴴ)
open import adequacy.Engine.Pick using (Beat; Beats; module Order; frag-flat; frag-parts; lanes-ʳsplit)
open import adequacy.Engine.Ahead using (Sides; shows; shows-open; ahead-mono) renaming (Ahead to Aheadᶠ)
open import adequacy.Engine.Race using (After; TailNotBefore)
open import adequacy.Engine.Shown using (beat-pass; cold-key; Links; pass-of)
open import adequacy.Strong using (module Strongly)
open Events∞ using (force)


module Honesty (R : Set) where
  open Driver R using (Step; silent; value; complete; drained; step; reading; Read; read; later; played; took)
  open Machine using (Conf; ⟨_,_,_,_⟩; load; moved; starting; turn; quiet; gone; leaf; nx; cp; St; pend; coldS; Ctx; top; inOuter; inLanes;
    plug; closed; alive; search; found; leafM; still; subscribing; absorbed; rising; _⊕_; inCut; inLn; attAt; flatS; killAll; lnS; cutS) renaming (step to stepᴹ; ended to endedˢ)
  open Spending R using (Skipped; outerᵏ; laneᵏ; deferᵏ; stallᵏ; closeᵏ; silent-spent)
  open Pure R using (End; finished; dry; cutOff)
  open Unsubbing R using (_⇝_; now; then)
  open Ghosting R using (Sent; sentHere; sentLater; Alike; residual; Reached; launchedʰ; silentʰ; valueʰ;
    Stands; cutʰ; finʰ; dryʰ; Mirror; Inner; Logged; Shows; silentˢ; valueˢ; completeˢ; drainedˢ; inner-launch;
    Steps; after; steps-after; Hopped; onward; Past; past-same; agrees; skipped; lowered; Lowers; depth; ahead-agree; work; _≺_)
  open Strongly R using (Strong; Carried; module Carried; Agrees; module Agrees; Leads; shown; skips; carried; carried-sane)

  -- WHERE THE GHOST'S SKIPS LEAD: a ghost past them, keeping the
  -- stepper's invariants, whose own step is the one led to.
  leads-past : ∀ {g s} → Sane [] g → Placed g [] → Leads g s
             → Σ (U.Node [] R) λ g₀ → Past (residual g) (residual g₀) × U.step g₀ ≡ s × Sane [] g₀ × Placed g₀ []
  leads-past {g} sn pl (shown e) = g , agrees (λ n → agree-refl n _) , e , sn , pl
  leads-past {g} sn pl (skips e l)
    with leads-past (subst (SaneS []) e (step-sane g sn)) (proj₂ (subst (Placedˢ []) e (placed-after g sn pl))) l
  ... | g₀ , p , e₀ , sn₀ , pl₀ =
    g₀ , skipped (λ n → subst (λ s → Agree n (residual g) (after s)) e (_≃_.agreeing (step-skips g sn pl) n)) p , e₀ , sn₀ , pl₀

  -- What a ghost's skips lead to is what it shows: a ghost past the
  -- skips, alike at every depth with the step led to.
  led-agrees : ∀ {g s} → Sane [] g → Placed g [] → Leads g s → Σ (Events R) λ y → Past (residual g) y × (∀ n → Agree n y (after s))
  led-agrees sn pl l with leads-past sn pl l
  ... | g₀ , p , e₀ , sn₀ , pl₀ = residual g₀ , p , λ n → subst (λ s → Agree n (residual g₀) (after s)) e₀ (_≃_.agreeing (step-skips g₀ sn₀ pl₀) n)

  led-same : ∀ {g s} → Sane [] g → Placed g [] → Leads g s → residual g ≅ after s
  led-same sn pl l with led-agrees sn pl l
  ... | y , p , ag = ≅-trans (past-same p) (agree-≅ ag)

  -- What a re-entry configuration's ghost is held to.
  strong-sane : ∀ {g m} → Strong g m → Sane [] g × Placed g []
  strong-sane (carried cr) = carried-sane cr

  -- Whatever a re-entry configuration's ghost reaches, it reaches.
  strong-ahead : ∀ {g m k} → Strong g m → Ahead (residual g) k → Ahead (M m) k
  strong-ahead (carried cr) = Agrees.ahead (Carried.agrees cr)

  -- Back from what a ghost's step shows to the ghost.
  step-ahead : ∀ {g s k} → Sane [] g → Placed g [] → U.step g ≡ s → Ahead (after s) k → Ahead (residual g) k
  step-ahead {g} sn pl e a =
    proj₁ (ahead-agree (λ n → agree-sym (subst (λ s → Agree n (residual g) (after s)) e (_≃_.agreeing (step-skips g sn pl) n))) a)

  -- Whatever the stepped ghost reaches, the ghost reaches with the
  -- value its skips lead to before it.
  leads-ahead : ∀ {g p a g′ k} → Sane [] g → Placed g [] → Leads g (U.outˢ p a g′) → Ahead (residual g′) k → Ahead (residual g) (suc k)
  leads-ahead sn pl (shown e) x = step-ahead sn pl e (outᵃ x)
  leads-ahead {g} sn pl (skips e l) x =
    step-ahead sn pl e (skipᵃ (leads-ahead (subst (SaneS []) e (step-sane g sn)) (proj₂ (subst (Placedˢ []) e (placed-after g sn pl))) l x))

  strong-steps : ∀ {g m s} → Strong g m → Leads g s → Steps (residual g) s
  strong-steps st l = steps-after _ (led-same (proj₁ (strong-sane st)) (proj₂ (strong-sane st)) l)

  -- THE STRONG STEP: from a re-entry configuration the machine records
  -- the value the ghost's skips lead to, a least of what it leaves, and
  -- runs the stepped ghost; or ends with the ghost; or drains over a
  -- ghost showing nothing; or runs silently to a ghost past this one's
  -- skips.
  data Hop {g m} (st : Strong g m) : Set₁ where
    valueᴴ    : ∀ {t p a m′ g′} → step m ≡ value t p a m′ → Leads g (U.outˢ p a g′) → t ≡ tick p
              → (∀ {q b} → Has (residual g′) q b → q ≤ᵖ p → ⊥) → Mirror g′ m′ → Hop st
    completeᴴ : ∀ {p} → step m ≡ complete p → Leads g (U.endˢ p) → Hop st
    drainedᴴ  : step m ≡ drained → (∀ {k b} → Has (residual g) k b → ⊥) → Hop st
    silentᴴ   : ∀ {t m′} → step m ≡ silent t m′ → Hopped st m′ → Hop st

  -- WHAT A CONFIGURATION RUNNING ITS GHOST DOES NEXT: the value the
  -- ghost's skips lead to, running the stepped ghost; the ghost's
  -- completion; a drain over a ghost showing nothing; or a silent step.
  data Moves (g : U.Node [] R) (m : Conf R) : Set₁ where
    valueᴹ    : ∀ {t p a m′ g′} → step m ≡ value t p a m′ → Leads g (U.outˢ p a g′) → t ≡ tick p
              → (∀ {q b} → Has (residual g′) q b → q ≤ᵖ p → ⊥) → Agrees g′ m′ → Moves g m
    completeᴹ : ∀ {p} → step m ≡ complete p → Leads g (U.endˢ p) → Moves g m
    drainedᴹ  : step m ≡ drained → (∀ {k b} → Has (residual g) k b → ⊥) → Moves g m
    silentᴹ   : ∀ {t m′} → step m ≡ silent t m′ → Moves g m

  -- A leaf's turn shows no value.
  played-novalue : ∀ pk {t p a m′} → played pk ≡ value t p a m′ → ⊥
  played-novalue gone ()
  played-novalue (leaf b (ending e) cl dv st) ()
  played-novalue (leaf false (play τ u i t fr) cl dv st) ()
  played-novalue (leaf false over cl dv st) ()
  played-novalue (leaf true (play τ u i t fr) true dv st) ()
  played-novalue (leaf true over true dv st) ()
  played-novalue (leaf true (play τ u i t (emit a k)) false dv st) ()
  played-novalue (leaf true (play τ u i t (stall k)) false dv st) ()
  played-novalue (leaf true (play τ u i t (close k)) false dv st) ()
  played-novalue (leaf true over false dv st) ()

  -- A value is shown on its own mark's tick.
  took-tick : ∀ x {t p a m′} → took x ≡ value t p a m′ → t ≡ tick p
  took-tick (moved c ((p , nx a) ∷ _) _) refl = refl
  took-tick (moved c ((p , cp) ∷ _) _)   ()
  took-tick (moved c [] _)               ()
  took-tick (starting x p k)             ()
  took-tick (turn pk)                    e = ⊥-elim (played-novalue pk e)
  took-tick quiet                        ()

  -- Two runs past `p`, alike after the same value at `p`, are alike.
  out-cancel : ∀ {p a} {x y : Events∞ R} → (∀ {q b} → Has (force x) q b → p <ᵖ q ≡ true)
             → (∀ {q b} → Has (force y) q b → p <ᵖ q ≡ true) → out p a x ≅ out p a y → force x ≅ force y
  out-cancel {p} {a} px py (to , from) = tail to px , tail from py
    where
    tail : ∀ {u v : Events∞ R} → (∀ {q b} → Has (out p a u) q b → Has (out p a v) q b)
         → (∀ {q b} → Has (force u) q b → p <ᵖ q ≡ true) → ∀ {q b} → Has (force u) q b → Has (force v) q b
    tail f pu h with f (pastOut h)
    ... | atOut      = ⊥-elim (t≢f (trans (sym (pu h)) (<ᵖ-irrefl p)))
    ... | pastOut h′ = h′

  postulate
    -- AFTER A VALUE THE ENGINE IS PAST IT: what the configuration it
    -- leaves means lies strictly after the value's mark.
    value-past : ∀ {m t p a m′} → Inv m → step m ≡ value t p a m′ → ∀ {q b} → Has (M m′) q b → p <ᵖ q ≡ true

    -- A GHOST'S LEAST VALUE IS WHERE ITS SKIPS LEAD: a value its residual
    -- holds, nothing earlier, is the step its skips come to, and what the
    -- stepped ghost leaves lies strictly after.
    ghost-out : ∀ {g p a} → Sane [] g → Placed g [] → Has (residual g) p (just a)
              → (∀ {q b} → Has (residual g) q b → q ≡ p ⊎ p <ᵖ q ≡ true)
              → Σ (U.Node [] R) λ g′ → Leads g (U.outˢ p a g′) × (∀ {q b} → Has (residual g′) q b → p <ᵖ q ≡ true)

    -- A GHOST'S END, NO VALUE BEFORE IT, IS WHERE ITS SKIPS LEAD.
    ghost-end : ∀ {g p} → Sane [] g → Placed g [] → Has (residual g) p nothing
              → (∀ {q a} → Has (residual g) q (just a) → ⊥) → Leads g (U.endˢ p)

    -- A VALUE SHOWN IS THE FIRST ITEM: whatever the configuration's
    -- meaning reaches past it, the configuration it leaves reaches.
    value-ahead : ∀ {m t p a m′ k} → Inv m → step m ≡ value t p a m′ → Ahead (M m) (suc k) → Ahead (M m′) k

  -- AN ENGINE RUNNING ITS GHOST MOVES AS THE GHOST'S SKIPS LEAD: by what
  -- the step keeps of the configuration's meaning.
  agrees-moves : ∀ {g m} → Sane [] g → Placed g [] → Agrees g m → Moves g m
  agrees-moves {g} {m} sn pl ag with step m in e | engine-kept m (Agrees.inv ag) | inv-next m (Agrees.inv ag)
  ... | silent t m′    | _ | _ = silentᴹ e
  ... | drained        | k | _ = drainedᴹ e λ h → no-hush (proj₁ (≅-trans (Agrees.same ag) k) h)
    where no-hush : ∀ {q b} → Has hush q b → ⊥
          no-hush ()
  ... | complete p     | k | _ = completeᴹ e (ghost-end sn pl (proj₂ x atEnd) λ h → no-value (proj₁ x h))
    where x = ≅-trans (Agrees.same ag) k
          no-value : ∀ {q a} → Has (end p) q (just a) → ⊥
          no-value ()
  ... | value t p a m′ | k | iv with ghost-out sn pl (proj₂ x atOut) order
    where x = ≅-trans (Agrees.same ag) k
          order : ∀ {q b} → Has (residual g) q b → q ≡ p ⊎ p <ᵖ q ≡ true
          order h with proj₁ x h
          ... | atOut      = inj₁ refl
          ... | pastOut h′ = inj₂ (value-past (Agrees.inv ag) e h′)
  ...   | g′ , ld , above = valueᴹ e ld (took-tick (stepᴹ m) e) least (record { inv = iv ; same = same′ ; ahead = λ x → value-ahead (Agrees.inv ag) e (Agrees.ahead ag (leads-ahead sn pl ld x)) })
    where
    least : ∀ {q b} → Has (residual g′) q b → q ≤ᵖ p → ⊥
    least h (inj₁ refl) = t≢f (trans (sym (above h)) (<ᵖ-irrefl p))
    least {q} h (inj₂ qp) = t≢f (trans (sym (above h)) (<ᵖ-asym q p qp))
    same′ : residual g′ ≅ M m′
    same′ = out-cancel above (value-past (Agrees.inv ag) e)
              (≅-trans (≅-sym (led-same sn pl ld)) (≅-trans (Agrees.same ag) k))

  -- A step dropping leading skips of what its configuration means, the
  -- rest with skips erased.
  Drop : Conf R → Conf R → Set
  Drop m m′ = Drops (M m) (M m′)

  -- Two configurations meaning the same, at every depth.
  Same : Conf R → Conf R → Set
  Same m m′ = ∀ n → Agree n (M m) (M m′)

  postulate
    -- A SILENT STEP DROPS SKIPS OR KEEPS ITS MEANING: a stall, a frame's
    -- close, a defer begun or a value absorbed drops one or more leading
    -- skips of what the configuration means (a defer begun drops every
    -- skip its subscription's subtree leads with), and erases none or
    -- more past them, each a lane's sight of a dropped skip from before
    -- it joined (`adequacy.Engine.Drop`); every other silent step means
    -- the same.
    silent-exact : ∀ {m t m′} → Inv m → step m ≡ silent t m′ → Drop m m′ ⊎ Same m m′

    -- EACH STEP WHOSE WORK MAY GROW DROPS A SKIP (`adequacy.Engine.Spent`'s
    -- `Skipped`): what the step leaves means less by at least one leading
    -- skip, never the same.  Every other silent step lowers its work.
    -- A STALL OR A CLOSE WHERE ONLY TAILS ARE READ, as `defer-tail`.
    stall-tail : ∀ {Γ A Γ′ A′} {c : Ctx R Γ A} {s : St Γ A} {c′ : Ctx R Γ′ A′} {τ u i t₀ k key p t m′}
               → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , coldS true (play τ u i t₀ (stall k))) leafM key)
               → shows c′ true ≡ false → Inv ⟨ c , s , absorbed , p ⟩ → step ⟨ c , s , absorbed , p ⟩ ≡ silent t m′
               → Drop ⟨ c , s , absorbed , p ⟩ m′
    close-tail : ∀ {Γ A Γ′ A′} {c : Ctx R Γ A} {s : St Γ A} {c′ : Ctx R Γ′ A′} {τ u i t₀ k key p t m′}
               → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , coldS true (play τ u i t₀ (close k))) leafM key)
               → shows c′ true ≡ false → Inv ⟨ c , s , absorbed , p ⟩ → step ⟨ c , s , absorbed , p ⟩ ≡ silent t m′
               → Drop ⟨ c , s , absorbed , p ⟩ m′

    -- A DEFER BEGUN WHERE IT IS SHOWN: every live source above passes
    -- its skip, as `outer-begins-links`.
    defer-links : ∀ {Γ A} {c : Ctx R Γ A} {l p} → shows c true ≡ true → Inv ⟨ c , pend (defer l) , subscribing , p ⟩
                → Links (_≡ p ⊕ [ ix 0 ]) c true (U.stateᴺ (U.deferᶜ l p []) (envAt c))
                    (U.stateᴺ (U.subscribe (Later.force l) (p ⊕ [ ix 1 ])) (envAt c))

    -- A DEFER BEGUN WHERE ONLY TAILS ARE READ drops its skip through the
    -- tail that pins it: a takeWhile past its decision above a connect
    -- still subscribing its source reads the connect's tail, and the
    -- connect's burst pins its source's steps (`quickcheck.KeptDepth`'s
    -- closed-cut programs drop there).
    --
    -- DEAD ROUTE: `lift-drops` alone. Its `Pass` is empty at every frame
    --   reading only a tail, since `Dropsˢ` says nothing of the hole's tail
    --   before the skip; a lift through such a frame needs each dropped skip
    --   carried with the pin it leaves in the tail.
    defer-tail : ∀ {Γ A} {c : Ctx R Γ A} {l p} → shows c true ≡ false → Inv ⟨ c , pend (defer l) , subscribing , p ⟩
               → Drop ⟨ c , pend (defer l) , subscribing , p ⟩ ⟨ c , pend (Later.force l) , subscribing , p ⊕ [ ix 1 ] ⟩

  -- A DEFER'S HOLE IS THE PROGRAM IT DEFERS PAST ONE SKIP: the
  -- meaning's lead skip, then the program subscribed just past it, its
  -- tail with it (`denotation.Unfold.subscribed`).
  defer-hole : ∀ {Γ A} l p (ρ : U.NEnv Γ)
             → Dropsˢ {A} (_≡ p ⊕ [ ix 0 ]) (U.stateᴺ (U.deferᶜ l p []) ρ) (U.stateᴺ (U.subscribe (Later.force l) (p ⊕ [ ix 1 ])) ρ)
  defer-hole l p ρ =
    dropˢ refl (λ n → agree-refl n _)
      (≋-⊒ (λ n → agreeᵀ-sym (_≈[_]_.agreeᵀ (s n) (p ⊕ [ ix 1 ])) ,ˢ agree-sym (_≈[_]_.agree (s n) (p ⊕ [ ix 1 ]))))
    where s = λ n → U.subscribed (Later.force l) {ρ} (env-refl {n} (U.hots ρ))

  -- A DEFER BEGUN WHERE IT IS SHOWN IS SHOWN NEXT: every frame above it
  -- passes its skip, at the skip's own position, under the subscription
  -- the order leads.  Asked at every position, a lane's frame beside an
  -- older lane with a pending head refutes it.
  defer-pass : ∀ {Γ A} {c : Ctx R Γ A} {l p} → shows c true ≡ true → Inv ⟨ c , pend (defer l) , subscribing , p ⟩
             → Pass (_≡ p ⊕ [ ix 0 ]) c (flagOf (pend (defer l))) (U.stateᴺ (U.deferᶜ l p []) (envAt c))
                 (U.stateᴺ (U.subscribe (Later.force l) (p ⊕ [ ix 1 ])) (envAt c))
  defer-pass {c = c} {p = p} sh iv =
    pass-of (_≡ p ⊕ [ ix 0 ]) c true (ahead-mono (λ k e → p , refl , [ ix 0 ] , e) c true (Order.lead (Inv.ord iv) sh)) (defer-links sh iv)

  -- A defer begun drops its skip.
  defer-drop : ∀ {Γ A} {c : Ctx R Γ A} {l p t m′}
             → Inv ⟨ c , pend (defer l) , subscribing , p ⟩ → step ⟨ c , pend (defer l) , subscribing , p ⟩ ≡ silent t m′
             → Drop ⟨ c , pend (defer l) , subscribing , p ⟩ m′
  defer-drop {c = c} {l} {p} iv refl with shows c true in sh
  ... | true  = lift-drops (_≡ p ⊕ [ ix 0 ]) c (flagOf (pend (defer l))) (defer-hole l p (envAt c)) (defer-pass sh iv)
  ... | false = defer-tail sh iv

  -- What a value admitted into a flatMap's lanes leaves running: the
  -- lanes a switch kills gone, and its count from none.
  keptLanes : ∀ {Γ B} → FlatOp → List (St Γ B) → List (St Γ B)
  keptLanes switchᶠ    ls = proj₁ (killAll ls)
  keptLanes (mergeᶠ m) ls = ls
  keptLanes exhaustᶠ   ls = ls

  running : FlatOp → ℕ → ℕ
  running switchᶠ    n = 0
  running (mergeᶠ m) n = n
  running exhaustᶠ   n = n

  -- As `admit` decides on the count of lanes running: an outer's value
  -- begins its lane, is queued behind a full merge, or is dropped by a
  -- busy exhaust.
  Begins : FlatOp → ℕ → Set
  Begins (mergeᶠ nothing)  n = ⊤
  Begins (mergeᶠ (just k)) n = (n <ᵇ k) ≡ true
  Begins switchᶠ           n = ⊤
  Begins exhaustᶠ          n = (n ≡ᵇ 0) ≡ true

  Queues : FlatOp → ℕ → Set
  Queues (mergeᶠ (just k)) n = (n <ᵇ k) ≡ false
  Queues _                 n = ⊥

  Ignores : FlatOp → ℕ → Set
  Ignores exhaustᶠ n = (n ≡ᵇ 0) ≡ false
  Ignores _        n = ⊥

  -- An outer's value admitted: its lane begun, or queued, or dropped by
  -- a busy exhaust.
  data Admitted {Γ A B} (c : Ctx R Γ B) (op : FlatOp) (f : A → Obs Timeline Γ B) (d : Bool) (n : ℕ) (q : List A) (o : St Γ A)
                (ls : List (St Γ B)) (a : A) (p : Pos) : Conf R → Set₁ where
    begun   : ∀ {ls′} → Begins op n → ls′ ≡ keptLanes op ls
            → Admitted c op f d n q o ls a p
                ⟨ inCut true (attAt (p ⊕ [ ix 1 ])) (inLn true (inLanes op f d (suc (running op n)) q o (reverse ls′) [] c)) , pend (f a) , subscribing , p ⊕ [ ix 1 ] ⟩
    queued  : Queues op n → Admitted c op f d n q o ls a p ⟨ c , flatS op f d n (q ++ [ a ]) o ls , absorbed , p ⟩
    ignored : Ignores op n → Admitted c op f d n q o ls a p ⟨ c , flatS op f d n q o ls , absorbed , p ⟩

  admitted : ∀ {Γ A B} {c : Ctx R Γ B} {op f d n q} {o : St Γ A} {ls a p t m′} → closed c ≡ false
           → step ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩ ≡ silent t m′ → Admitted c op f d n q o ls a p m′
  admitted {c = c} {op = mergeᶠ nothing} cl e with closed c | cl | e
  ... | false | refl | refl = begun tt refl
  admitted {c = c} {op = mergeᶠ (just k)} {n = n} cl e with n <ᵇ k in b | closed c | cl | e
  ... | true  | false | refl | refl = begun b refl
  ... | false | _     | _    | refl = queued b
  admitted {c = c} {op = switchᶠ} {ls = ls} cl e with killAll ls in ek | closed c | cl | e
  ... | ls′ , _ | false | refl | refl = begun tt (cong proj₁ (sym ek))
  admitted {c = c} {op = exhaustᶠ} {n = n} cl e with n ≡ᵇ 0 in b | e
  ... | false | refl = ignored b
  ... | true  | e′ with closed c | cl | e′
  ...   | false | refl | refl = begun b refl

  -- The outer frame with its value risen, and what each admission leaves.
  outerX : ∀ {Γ A B} → Ctx R Γ B → FlatOp → (A → Obs Timeline Γ B) → Bool → List A → List (St Γ B) → St Γ A → A → Pos → Events∞ B
  outerX c op f d q ls o a p = outerFrame op (lane f) d q (lanesL ls) (deadL ls) (envAt c) (risen (gh o) (envAt c) (nx a) p)

  begunY : ∀ {Γ A B} → Ctx R Γ B → FlatOp → (A → Obs Timeline Γ B) → Bool → List A → St Γ A → List (St Γ B) → A → Pos → Events∞ B
  begunY c op f d q o ls a p =
    lanesFrame op (lane f) d q (gh o) (reverse (reverse ls)) [] true (envAt c) (U.stateᴺ (U.subscribe (f a) (p ⊕ [ ix 1 ])) (envAt c))

  postulate
    -- AN OUTER'S VALUE ADMITTED WHERE IT IS SHOWN PASSES EVERY LIVE SOURCE
    -- ABOVE: each source's skips pass its connect, whatever the admission
    -- left.
    outer-begins-links : ∀ {Γ A B} {c : Ctx R Γ B} {op d n q ls} {f : A → Obs Timeline Γ B} {o : St Γ A} {a p}
                       → shows (inOuter op f d n q ls c) true ≡ true → Inv ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
                       → Links (_≡ p ⊕ [ ix 0 ]) c true (outerX c op f d q ls o a p) (begunY c op f d q o (keptLanes op ls) a p)
    outer-queues-links : ∀ {Γ A B} {c : Ctx R Γ B} {op d n q ls} {f : A → Obs Timeline Γ B} {o : St Γ A} {a p}
                       → shows (inOuter op f d n q ls c) true ≡ true → Inv ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
                       → Links (_≡ p ⊕ [ ix 0 ]) c true (outerX c op f d q ls o a p) (U.stateᴺ (gh (flatS op f d n (q ++ [ a ]) o ls)) (envAt c))
    outer-ignores-links : ∀ {Γ A B} {c : Ctx R Γ B} {op d n q ls} {f : A → Obs Timeline Γ B} {o : St Γ A} {a p}
                        → shows (inOuter op f d n q ls c) true ≡ true → Inv ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
                        → Links (_≡ p ⊕ [ ix 0 ]) c true (outerX c op f d q ls o a p) (U.stateᴺ (gh (flatS op f d n q o ls)) (envAt c))

  -- An outer's value shown where it rises is ahead in every frame above
  -- (`Clear`).
  outer-ahead : ∀ {Γ A B} {c : Ctx R Γ B} {op d n q ls} {f : A → Obs Timeline Γ B} {o : St Γ A} {a p}
              → shows (inOuter op f d n q ls c) true ≡ true → Inv ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
              → Aheadᶠ (_≡ p ⊕ [ ix 0 ]) c true
  outer-ahead {d = true}  () iv
  outer-ahead {d = false} sh iv = proj₂ (proj₂ (proj₂ (Order.lead (Inv.ord iv)))) sh

  -- AN OUTER'S VALUE ADMITTED WHERE IT IS SHOWN IS SHOWN NEXT: every
  -- frame above passes its skip, whatever the admission left.
  outer-begins-pass : ∀ {Γ A B} {c : Ctx R Γ B} {op d n q ls} {f : A → Obs Timeline Γ B} {o : St Γ A} {a p}
                    → shows (inOuter op f d n q ls c) true ≡ true → Inv ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
                    → Pass (_≡ p ⊕ [ ix 0 ]) c true (outerX c op f d q ls o a p) (begunY c op f d q o (keptLanes op ls) a p)
  outer-begins-pass {c = c} {p = p} sh iv = pass-of (_≡ p ⊕ [ ix 0 ]) c true (outer-ahead sh iv) (outer-begins-links sh iv)

  outer-queues-pass : ∀ {Γ A B} {c : Ctx R Γ B} {op d n q ls} {f : A → Obs Timeline Γ B} {o : St Γ A} {a p}
                    → shows (inOuter op f d n q ls c) true ≡ true → Inv ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
                    → Pass (_≡ p ⊕ [ ix 0 ]) c true (outerX c op f d q ls o a p) (U.stateᴺ (gh (flatS op f d n (q ++ [ a ]) o ls)) (envAt c))
  outer-queues-pass {c = c} {p = p} sh iv = pass-of (_≡ p ⊕ [ ix 0 ]) c true (outer-ahead sh iv) (outer-queues-links sh iv)

  outer-ignores-pass : ∀ {Γ A B} {c : Ctx R Γ B} {op d n q ls} {f : A → Obs Timeline Γ B} {o : St Γ A} {a p}
                     → shows (inOuter op f d n q ls c) true ≡ true → Inv ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
                     → Pass (_≡ p ⊕ [ ix 0 ]) c true (outerX c op f d q ls o a p) (U.stateᴺ (gh (flatS op f d n q o ls)) (envAt c))
  outer-ignores-pass {c = c} {p = p} sh iv = pass-of (_≡ p ⊕ [ ix 0 ]) c true (outer-ahead sh iv) (outer-ignores-links sh iv)

  postulate
    -- AN OUTER'S VALUE ADMITTED WHERE ONLY TAILS ARE READ drops its skip
    -- through the tail that pins it, as `defer-tail`.
    outer-tail : ∀ {Γ A B op d n q ls} {f : A → Obs Timeline Γ B} {c : Ctx R Γ B} {o : St Γ A} {a p t m′}
               → shows (inOuter op f d n q ls c) true ≡ false → Inv ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
               → step ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩ ≡ silent t m′
               → Drop ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩ m′

  -- The lanes a flatMap counts, the lanes its meaning holds.
  states-length : ∀ {Γ B} (ls : List (U.Node Γ B)) (ρ : U.NEnv Γ) → length (U.states ls ρ) ≡ length ls
  states-length []       ρ = refl
  states-length (l ∷ ls) ρ = cong suc (states-length ls ρ)

  -- A full merge queues what arrives; a busy exhaust drops it.
  queue-admits : ∀ {B} k (m : MonotonicList B) ls qs r → (length ls <ᵇ k) ≡ false → admit (flatOp (mergeᶠ (just k))) r m ls qs ≡ (ls , qs ++ [ m ] , idle)
  queue-admits k m ls qs r e rewrite e = refl

  ignore-admits : ∀ {B} (m : MonotonicList B) ls qs r → (length ls ≡ᵇ 0) ≡ false → admit (flatOp exhaustᶠ) r m ls qs ≡ (ls , qs , idle)
  ignore-admits m (l ∷ ls) qs r e = refl

  -- AN OUTER'S VALUE QUEUED, OR DROPPED BY A BUSY EXHAUST, IS ITS SKIP:
  -- the outer is first among the parts (`Clear`), and its count is its
  -- meaning's (`Frag`).
  outer-queues : ∀ {Γ A B} {c : Ctx R Γ B} {op d n q ls} {f : A → Obs Timeline Γ B} {o : St Γ A} {a p}
               → Queues op n → Inv ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
               → Dropsˢ (_≡ p ⊕ [ ix 0 ]) (outerX c op f d q ls o a p) (U.stateᴺ (gh (flatS op f d n (q ++ [ a ]) o ls)) (envAt c))
  outer-queues {op = mergeᶠ (just k)} {true} b iv = ⊥-elim (Order.lead (Inv.ord iv))
  outer-queues {c = c} {mergeᶠ (just k)} {false} {n} {q} {ls} {f} {o} {a} {p} b iv with Order.lead (Inv.ord iv)
  ... | _ , al , tn , _ =
    outer-admits (mergeᶠ (just k)) (lane f) q (lanesL ls) (deadL ls) (envAt c) (gh o) a p _
      (trans (queue-admits k (laneᴹ (lane f) (envAt c) a) (U.states (lanesL ls) (envAt c)) (map (laneᴹ (lane f) (envAt c)) q) (p ⊕ [ ix 1 ])
                (subst (λ x → (x <ᵇ k) ≡ false) (trans en (sym (states-length (lanesL ls) (envAt c)))) b))
             (cong (λ x → U.states (lanesL ls) (envAt c) , x , idle) (sym (map-++ (laneᴹ (lane f) (envAt c)) q [ a ]))))
      refl refl (λ m → lanes-refl m _) (λ m → ∪-idleᵀ m _) al tn
    where en = proj₁ (proj₂ (proj₂ (frag-flat c (mergeᶠ (just k)) f false n q o ls (Order.shape (Inv.ord iv)))))
  outer-queues {op = mergeᶠ nothing} ()
  outer-queues {op = switchᶠ}        ()
  outer-queues {op = exhaustᶠ}       ()

  outer-ignores : ∀ {Γ A B} {c : Ctx R Γ B} {op d n q ls} {f : A → Obs Timeline Γ B} {o : St Γ A} {a p}
                → Ignores op n → Inv ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
                → Dropsˢ (_≡ p ⊕ [ ix 0 ]) (outerX c op f d q ls o a p) (U.stateᴺ (gh (flatS op f d n q o ls)) (envAt c))
  outer-ignores {op = exhaustᶠ} {true} b iv = ⊥-elim (Order.lead (Inv.ord iv))
  outer-ignores {c = c} {exhaustᶠ} {false} {n} {q} {ls} {f} {o} {a} {p} b iv with Order.lead (Inv.ord iv)
  ... | _ , al , tn , _ =
    outer-admits exhaustᶠ (lane f) q (lanesL ls) (deadL ls) (envAt c) (gh o) a p _
      (ignore-admits (laneᴹ (lane f) (envAt c) a) (U.states (lanesL ls) (envAt c)) (map (laneᴹ (lane f) (envAt c)) q) (p ⊕ [ ix 1 ])
         (subst (λ x → (x ≡ᵇ 0) ≡ false) (trans en (sym (states-length (lanesL ls) (envAt c)))) b))
      refl refl (λ m → lanes-refl m _) (λ m → ∪-idleᵀ m _) al tn
    where en = proj₁ (proj₂ (proj₂ (frag-flat c exhaustᶠ f false n q o ls (Order.shape (Inv.ord iv)))))
  outer-ignores {op = mergeᶠ m} ()
  outer-ignores {op = switchᶠ}  ()

  -- A merge with room, or an idle exhaust, begins the lane it admits.
  begin-admits : ∀ {B} k (m : MonotonicList B) ls qs r → (length ls <ᵇ k) ≡ true → admit (flatOp (mergeᶠ (just k))) r m ls qs ≡ (enter m r ∷ ls , qs , idle)
  begin-admits k m ls qs r e rewrite e = refl

  exhaust-admits : ∀ {B} (m : MonotonicList B) ls qs r → (length ls ≡ᵇ 0) ≡ true → admit (flatOp exhaustᶠ) r m ls qs ≡ (enter m r ∷ ls , qs , idle)
  exhaust-admits m []       qs r e = refl
  exhaust-admits m (l ∷ ls) qs r ()

  -- A lane begun ahead of those kept: the merge's lanes, newest first,
  -- and the pool the kept leave.
  begun-runs : ∀ {Γ B} (ls : List (St Γ B)) (ρ : U.NEnv Γ) h → h ∷ U.states (lanesL ls) ρ ≡ laneRuns (reverse (reverse ls)) [] true ρ h
  begun-runs ls ρ h = cong (λ x → h ∷ U.states (lanesL x) ρ) (sym (reverse-involutive ls))

  begun-pool : ∀ {Γ B} (ls : List (St Γ B)) (ρ : U.NEnv Γ) h → poolT (deadL ls) ρ ≡ poolRuns (reverse (reverse ls)) [] true ρ h
  begun-pool {B = B} ls ρ h rewrite reverse-involutive ls =
    trans (cong (λ x → U.cutᴺ (U.restsᶜ {B = B} x) ρ) (sym (++-identityʳ (deadL ls)))) (rests-++ (deadL ls) [] ρ)

  -- A switch's kill leaves no lane live.
  kill-lanes : ∀ {Γ B} (ls : List (St Γ B)) → Lanesᴴ ls → lanesL (proj₁ (killAll ls)) ≡ []
  kill-lanes []                                _        = refl
  kill-lanes (lnS true (cutS true a s) ∷ ls)   (_ , fl) with Machine.cut (cutS true a s) | killAll ls | kill-lanes ls fl
  ... | s′ , u | ls′ , t | e = cong (_++ []) e
  kill-lanes (lnS false (cutS false a s) ∷ ls) (_ , fl) with killAll ls | kill-lanes ls fl
  ... | ls′ , t | e = cong (_++ []) e

  postulate
    -- A SWITCH'S KILL POOLS WHAT IT KILLED: each lane it switches off
    -- leaves in the pool the tail the merge's `cuts` reads of it.
    kill-pool : ∀ {Γ B} (ls : List (St Γ B)) (ρ : U.NEnv Γ) → Lanesᴴ ls
              → ∀ n → Agreeᵀ n (poolT (deadL ls) ρ ∪ cuts (U.states (lanesL ls) ρ)) (poolT (deadL (proj₁ (killAll ls))) ρ)

  -- An outer's value begun past its skip, as `admit` begins it.
  begun-drops : ∀ {Γ A B} (c : Ctx R Γ B) op q ls (f : A → Obs Timeline Γ B) (o : St Γ A) a p ls′ {Ls t′}
              → admit (flatOp op) (p ⊕ [ ix 1 ]) (laneᴹ (lane f) (envAt c) a) (U.states (lanesL ls) (envAt c)) (map (laneᴹ (lane f) (envAt c)) q)
                  ≡ (Ls , map (laneᴹ (lane f) (envAt c)) q , t′)
              → (∀ n → Lanes n Ls (U.stateᴺ (U.subscribe (f a) (p ⊕ [ ix 1 ])) (envAt c) ∷ U.states (lanesL ls′) (envAt c)))
              → (∀ n → Agreeᵀ n (poolT (deadL ls) (envAt c) ∪ t′) (poolT (deadL ls′) (envAt c)))
              → All (λ l → After p (head (force l))) (U.states (lanesL ls) (envAt c)) → TailNotBefore p (poolT (deadL ls) (envAt c))
              → Dropsˢ (_≡ p ⊕ [ ix 0 ]) (outerX c op f false q ls o a p) (begunY c op f false q o ls′ a p)
  begun-drops c op q ls f o a p ls′ ad la ta al tn =
    outer-admits op (lane f) q (lanesL ls) (deadL ls) (envAt c) (gh o) a p (begunY c op f false q o ls′ a p) ad refl refl
      (λ n → subst (Lanes n _) (begun-runs ls′ (envAt c) h) (la n)) (λ n → subst (Agreeᵀ n _) (begun-pool ls′ (envAt c) h) (ta n)) al tn
    where h = U.stateᴺ (U.subscribe (f a) (p ⊕ [ ix 1 ])) (envAt c)

  -- AN OUTER'S VALUE BEGINS ITS LANE PAST ONE SKIP: the flatMap shows
  -- the value as a skip, then the lane subscribed just past it.
  outer-begins : ∀ {Γ A B} {c : Ctx R Γ B} {op d n q ls} {f : A → Obs Timeline Γ B} {o : St Γ A} {a p}
               → Begins op n → Inv ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
               → Dropsˢ (_≡ p ⊕ [ ix 0 ]) (outerX c op f d q ls o a p) (begunY c op f d q o (keptLanes op ls) a p)
  outer-begins {d = true} b iv = ⊥-elim (Order.lead (Inv.ord iv))
  outer-begins {c = c} {mergeᶠ nothing} {false} {n} {q} {ls} {f} {o} {a} {p} b iv with Order.lead (Inv.ord iv)
  ... | _ , al , tn , _ = begun-drops c (mergeᶠ nothing) q ls f o a p ls refl (λ m → lanes-refl m _) (λ m → ∪-idleᵀ m _) al tn
  outer-begins {c = c} {mergeᶠ (just k)} {false} {n} {q} {ls} {f} {o} {a} {p} b iv with Order.lead (Inv.ord iv)
  ... | _ , al , tn , _ =
    begun-drops c (mergeᶠ (just k)) q ls f o a p ls
      (begin-admits k (laneᴹ (lane f) (envAt c) a) (U.states (lanesL ls) (envAt c)) (map (laneᴹ (lane f) (envAt c)) q) (p ⊕ [ ix 1 ])
         (subst (λ x → (x <ᵇ k) ≡ true) (trans en (sym (states-length (lanesL ls) (envAt c)))) b))
      (λ m → lanes-refl m _) (λ m → ∪-idleᵀ m _) al tn
    where en = proj₁ (proj₂ (proj₂ (frag-flat c (mergeᶠ (just k)) f false n q o ls (Order.shape (Inv.ord iv)))))
  outer-begins {c = c} {exhaustᶠ} {false} {n} {q} {ls} {f} {o} {a} {p} b iv with Order.lead (Inv.ord iv)
  ... | _ , al , tn , _ =
    begun-drops c exhaustᶠ q ls f o a p ls
      (exhaust-admits (laneᴹ (lane f) (envAt c) a) (U.states (lanesL ls) (envAt c)) (map (laneᴹ (lane f) (envAt c)) q) (p ⊕ [ ix 1 ])
         (subst (λ x → (x ≡ᵇ 0) ≡ true) (trans en (sym (states-length (lanesL ls) (envAt c)))) b))
      (λ m → lanes-refl m _) (λ m → ∪-idleᵀ m _) al tn
    where en = proj₁ (proj₂ (proj₂ (frag-flat c exhaustᶠ f false n q o ls (Order.shape (Inv.ord iv)))))
  outer-begins {c = c} {switchᶠ} {false} {n} {q} {ls} {f} {o} {a} {p} b iv with Order.lead (Inv.ord iv)
  ... | _ , al , tn , _ =
    begun-drops c switchᶠ q ls f o a p (proj₁ (killAll ls)) refl
      (λ m → subst (λ x → Lanes m (h ∷ []) (h ∷ U.states x (envAt c))) (sym (kill-lanes ls fl)) (lanes-refl m (h ∷ [])))
      (kill-pool ls (envAt c) fl) al tn
    where fl = proj₁ (proj₂ (frag-flat c switchᶠ f false n q o ls (Order.shape (Inv.ord iv))))
          h  = U.stateᴺ (U.subscribe (f a) (p ⊕ [ ix 1 ])) (envAt c)

  -- An outer's value admitted drops its skip.
  outer-drop : ∀ {Γ A B op d n q ls} {f : A → Obs Timeline Γ B} {c : Ctx R Γ B} {o : St Γ A} {a p t m′}
             → Inv ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
             → step ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩ ≡ silent t m′
             → Drop ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩ m′
  outer-drop {op = op} {d} {n} {q} {ls} {f} {c} {o} {a} {p} iv e with shows (inOuter op f d n q ls c) true in sh
  ... | false = outer-tail sh iv e
  ... | true with admitted {c = c} {op = op} (shows-open (inOuter op f d n q ls c) true sh) e
  ...   | begun b refl = lift-drops (_≡ p ⊕ [ ix 0 ]) c true (outer-begins b iv) (outer-begins-pass sh iv)
  ...   | queued b     = lift-drops (_≡ p ⊕ [ ix 0 ]) c true (outer-queues b iv) (outer-queues-pass sh iv)
  ...   | ignored b    = lift-drops (_≡ p ⊕ [ ix 0 ]) c true (outer-ignores b iv) (outer-ignores-pass sh iv)

  -- A lane's completion under a queue, and the queue's next lane begun.
  laneX : ∀ {Γ A B} → Ctx R Γ B → FlatOp → (A → Obs Timeline Γ B) → Bool → List A → St Γ A → List (St Γ B) → List (St Γ B) → St Γ B → Pos → Events∞ B
  laneX c op f d q o pre post s p = lanesFrame op (lane f) d q (gh o) (reverse pre) post true (envAt c) (risen (gh s) (envAt c) cp p)

  -- A tail joined behind a pool joins it at the pool's end.
  tails-ended : ∀ {Γ B} n (ds : List (U.Node Γ B)) (ρ : U.NEnv Γ) t u → SortedT t → SortedT u → Agreeᵀ n (tailsOn ds ρ t ∪ u) (tailsOn ds ρ (u ∪ t))
  tails-ended n []       ρ t u st su = ∪-commᵀ n t u st su
  tails-ended n (x ∷ ds) ρ t u st su =
    agreeᵀ-trans (∪-assocᵀ n (U.cutᴺ x ρ) (tailsOn ds ρ t) u) (∪-ne (agreeᵀ-refl n (U.cutᴺ x ρ)) (tails-ended n ds ρ t u st su))

  pool-ended : ∀ {Γ A B} n d (o : U.Node Γ A) (ds : List (U.Node Γ B)) (ρ : U.NEnv Γ) t u → SortedT t → SortedT u
             → Agreeᵀ n (outerT d o ρ (tailsOn ds ρ t) ∪ u) (outerT d o ρ (tailsOn ds ρ (u ∪ t)))
  pool-ended n false o ds ρ t u st su = tails-ended n ds ρ t u st su
  pool-ended n true  o ds ρ t u st su =
    agreeᵀ-trans (∪-assocᵀ n (U.cutᴺ o ρ) (tailsOn ds ρ t) u) (∪-ne (agreeᵀ-refl n (U.cutᴺ o ρ)) (tails-ended n ds ρ t u st su))

  -- A pool of tails each in position order is.
  hole-sorted : ∀ {B} b (h : Events∞ B) t → SortedT (Events∞.cut h) → SortedT t → SortedT (holeT b h ∪ t)
  hole-sorted true  h t sh st = st
  hole-sorted false h t sh st = sortedT-∪ (Events∞.cut h) t sh st

  pool-sorted : ∀ {Γ B} (ls : List (St Γ B)) (ρ : U.NEnv Γ) → All (λ s → SortedT (U.cutᴺ (gh s) ρ)) ls → SortedT (poolT (deadL ls) ρ)
  pool-sorted []       ρ []       = sortedT-idle
  pool-sorted (x ∷ ls) ρ (sx ∷ sl) =
    subst SortedT (sym (trans (rests-++ (deadOne x) (deadL ls) ρ) (dead-hole x ρ _)))
      (hole-sorted (flagOf x) (U.stateᴺ (gh x) ρ) _ sx (pool-sorted ls ρ sl))

  -- A lane's context keeps the lanes before it nearest first.
  all-at : ∀ {Γ B} {P : St Γ B → Set} pre {s post} → All P (pre ʳ++ s ∷ post) → P s × All P post
  all-at pre a with ++⁻ʳ (reverse pre) (subst (All _) (ʳ++-defn pre) a)
  ... | x ∷ xs = x , xs

  -- A lane ended under a queue: its end a skip, past it the queue's next
  -- lane begun ahead of the rest, the ended lane's tail in the pool where
  -- the lane sat.
  ended-begins : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d a q (o : St Γ A) pre post (s : St Γ B) p
               → Lane s → alive s ≡ true → SortedT (U.cutᴺ (gh s) (envAt c)) → SortedT (poolT (deadL post) (envAt c))
               → Sides p f d o (reverse pre) post (envAt c)
               → Dropsˢ (_≡ p ⊕ [ ix 0 ]) (laneX c op f d (a ∷ q) o pre post s p) (begunY c op f d q o (pre ʳ++ endedˢ s ∷ post) a p)
  ended-begins c op f d a q o pre post (lnS true (cutS true x s₀)) p fs al ss sp sd =
    lane-admits op (lane f) d a q (gh o) (reverse pre) post ρ (gh s₀) p (begunY c op f d q o L a p) sd refl refl
      (λ m → subst (Lanes m _) (begun-runs L ρ h)
               (subst (λ z → Lanes m (h ∷ U.states (lanesL post) ρ ++ U.states (lanesL (reverse pre)) ρ) (h ∷ z)) runs
                  (lanes-refl m (h ∷ U.states (lanesL post) ρ ++ U.states (lanesL (reverse pre)) ρ))))
      (λ m → subst (λ z → Agreeᵀ m (outerT d (gh o) ρ (tailsOn (deadL (reverse pre)) ρ (poolT (deadL post) ρ)) ∪ U.cutᴺ (gh s₀) ρ) (outerT d (gh o) ρ z)) pool
               (pool-ended m d (gh o) (deadL (reverse pre)) ρ (poolT (deadL post) ρ) (U.cutᴺ (gh s₀) ρ) sp ss))
    where
      ρ = envAt c
      e = lnS false (cutS false x s₀)
      L = pre ʳ++ e ∷ post
      h = U.stateᴺ (U.subscribe (f a) (p ⊕ [ ix 1 ])) ρ
      runs : U.states (lanesL post) ρ ++ U.states (lanesL (reverse pre)) ρ ≡ U.states (lanesL L) ρ
      runs = trans (sym (lanes-runs (reverse pre) e post ρ)) (cong (λ z → U.states (lanesL z) ρ) (sym (ʳ++-defn pre)))
      pool : tailsOn (deadL (reverse pre)) ρ (U.cutᴺ (gh s₀) ρ ∪ poolT (deadL post) ρ) ≡ poolRuns (reverse (reverse L)) [] true ρ h
      pool = trans (sym (pool-runs (reverse pre) e post ρ)) (trans (cong (λ z → poolT (deadL z) ρ) (sym (ʳ++-defn pre))) (begun-pool L ρ h))
  ended-begins c op f d a q o pre post (lnS false (cutS false x s₀)) p fs () ss sp sd

  postulate
    -- EVERY LANE OF A FRAGMENT'S FLATMAP LEAVES ITS TAIL IN POSITION ORDER.
    lanes-sorted : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls
                 → Frag (plug c (flatS op f d n q o ls)) → All (λ s → SortedT (U.cutᴺ (gh s) (envAt c))) ls
    -- A LANE'S COMPLETION UNDER A CLOSED FRAME, as `lane-begins` under an open one.
    lane-begins-shut : ∀ {Γ A B op d n a q pre post} {f : A → Obs Timeline Γ B} {c : Ctx R Γ B} {o : St Γ A} {s : St Γ B} {p}
                     → alive s ≡ true → Inv ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩ → closed c ≡ true
                     → Dropsˢ (_≡ p ⊕ [ ix 0 ]) (laneX c op f d (a ∷ q) o pre post s p) (begunY c op f d q o (pre ʳ++ endedˢ s ∷ post) a p)

  -- A LANE'S COMPLETION UNDER A QUEUE BEGINS THE NEXT LANE PAST ONE SKIP:
  -- the lane's end is first among its flatMap's parts (`Ends`).
  lane-begins : ∀ {Γ A B op d n a q pre post} {f : A → Obs Timeline Γ B} {c : Ctx R Γ B} {o : St Γ A} {s : St Γ B} {p}
              → alive s ≡ true → Inv ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩
              → Dropsˢ (_≡ p ⊕ [ ix 0 ]) (laneX c op f d (a ∷ q) o pre post s p) (begunY c op f d q o (pre ʳ++ endedˢ s ∷ post) a p)
  lane-begins {op = op} {d} {n} {a} {q} {pre} {post} {f} {c} {o} {s} {p} al iv with closed c in cl
  ... | true  = lane-begins-shut al iv cl
  ... | false =
    ended-begins c op f d a q o pre post s p (proj₁ (proj₂ (lanes-ʳsplit pre fl))) al (proj₁ ss) (pool-sorted post (envAt c) (proj₂ ss))
      (proj₁ (proj₂ (Order.lead (Inv.ord iv))) cl)
    where
      ft = Order.shape (Inv.ord iv)
      fl = proj₂ (frag-parts op f d n (a ∷ q) o (pre ʳ++ s ∷ post) (frag-flat c op f d n (a ∷ q) o (pre ʳ++ s ∷ post) ft))
      ss = all-at pre (lanes-sorted c op f d n (a ∷ q) o (pre ʳ++ s ∷ post) ft)

  postulate
    -- AND WHERE IT IS SHOWN PASSES EVERY LIVE SOURCE ABOVE.
    lane-begins-links : ∀ {Γ A B op d n a q pre post} {f : A → Obs Timeline Γ B} {c : Ctx R Γ B} {o : St Γ A} {s : St Γ B} {p}
                      → shows (inLanes op f d n (a ∷ q) o pre post c) true ≡ true → Inv ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩
                      → Links (_≡ p ⊕ [ ix 0 ]) c true (laneX c op f d (a ∷ q) o pre post s p) (begunY c op f d q o (pre ʳ++ endedˢ s ∷ post) a p)
    -- A LANE'S COMPLETION WHERE ONLY TAILS ARE READ, as `defer-tail`.
    lane-tail : ∀ {Γ A B op d n a q pre post} {f : A → Obs Timeline Γ B} {c : Ctx R Γ B} {o : St Γ A} {s : St Γ B} {p t m′}
              → alive s ≡ true → shows (inLanes op f d n (a ∷ q) o pre post c) true ≡ false
              → Inv ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩
              → step ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩ ≡ silent t m′
              → Drop ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩ m′

  -- AND WHERE IT IS SHOWN IS SHOWN NEXT: the frames above are ahead of
  -- the skip just past the lane's end (`Ends`).
  lane-begins-pass : ∀ {Γ A B op d n a q pre post} {f : A → Obs Timeline Γ B} {c : Ctx R Γ B} {o : St Γ A} {s : St Γ B} {p}
                   → shows (inLanes op f d n (a ∷ q) o pre post c) true ≡ true → Inv ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩
                   → Pass (_≡ p ⊕ [ ix 0 ]) c true (laneX c op f d (a ∷ q) o pre post s p) (begunY c op f d q o (pre ʳ++ endedˢ s ∷ post) a p)
  lane-begins-pass {c = c} {p = p} sh iv =
    pass-of (_≡ p ⊕ [ ix 0 ]) c true (proj₂ (proj₂ (proj₂ (Order.lead (Inv.ord iv)))) sh) (lane-begins-links sh iv)

  -- A lane's completion under a queue drops its skip.
  lane-drop : ∀ {Γ A B op d n a q pre post} {f : A → Obs Timeline Γ B} {c : Ctx R Γ B} {o : St Γ A} {s : St Γ B} {p t m′}
            → alive s ≡ true → Inv ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩
            → step ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩ ≡ silent t m′
            → Drop ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩ m′
  lane-drop {op = op} {d} {n} {a} {q} {pre} {post} {f} {c} {o} {s} {p} al iv e with shows (inLanes op f d n (a ∷ q) o pre post c) true in sh
  ... | false = lane-tail al sh iv e
  ... | true with alive s | al | closed c | shows-open (inLanes op f d n (a ∷ q) o pre post c) true sh | e
  ...   | true | refl | false | refl | refl = lift-drops (_≡ p ⊕ [ ix 0 ]) c true (lane-begins al iv) (lane-begins-pass sh iv)

  -- Drops past a meaning alike at every depth.
  drops-agree : ∀ {A} {e e₀ e′ : Events A} → (∀ n → Agree n e e₀) → Drops e₀ e′ → Drops e e′
  drops-agree x (drop ag ag′) = drop (λ n → agree-trans (x n) (ag n)) ag′
  drops-agree x (drops ag d)  = drops (λ n → agree-trans (x n) (ag n)) d

  -- A stall's hole: its lead skip, then the frame's rest.
  stall-hole : ∀ {Γ A τ u i t₀ k} (ρ : U.NEnv Γ)
             → Dropsˢ {A} (_≡ u ++ [ ix i ]) (U.stateᴺ (gh (coldS true (play τ u i t₀ (stall k)))) ρ) (U.stateᴺ (gh (coldS true (play τ u (suc i) t₀ (Frame∞.force k)))) ρ)
  stall-hole ρ = dropˢ refl (λ n → agree-refl n _) (≋-⊒ (≋-by refl refl))

  -- A close's hole: its lead skip, then the frames after it.
  close-hole : ∀ {Γ A τ u i t₀ k} (ρ : U.NEnv Γ)
             → Dropsˢ {A} (_≡ u ++ [ ix i ]) (U.stateᴺ (gh (coldS true (play τ u i t₀ (close k)))) ρ) (U.stateᴺ (gh (coldS true (restᵀ τ (u ++ [ last ]) (From∞.force k)))) ρ)
  close-hole {A = A} {τ = τ} {u} {k = k} ρ = dropˢ refl (λ n → agree-refl n _) (≋-⊒ (≋-by (rest-frames (From∞.force k)) (rest-cut (From∞.force k))))
    where
    rest-frames : ∀ {t} (m : From A t) → frames τ (u ++ [ last ]) m ≡ U.meaning (gh (coldS true (restᵀ τ (u ++ [ last ]) m))) ρ
    rest-frames done        = refl
    rest-frames silentᶠ     = refl
    rest-frames (at _ _ _)  = refl
    rest-cut : ∀ {t} (m : From A t) → idle ≡ U.cutᴺ (gh (coldS true (restᵀ τ (u ++ [ last ]) m))) ρ
    rest-cut done        = refl
    rest-cut silentᶠ     = refl
    rest-cut (at _ _ _)  = refl

  -- What a stall leaves: its cold one frame on, still absorbed.
  stall-next : ∀ {Γ A Γ′ A′} {c : Ctx R Γ A} {s : St Γ A} {c′ : Ctx R Γ′ A′} {τ u i t₀ k key p}
             → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , coldS true (play τ u i t₀ (stall k))) leafM key)
             → closed c′ ≡ false → ∀ {t m′} → step ⟨ c , s , absorbed , p ⟩ ≡ silent t m′
             → m′ ≡ ⟨ c′ , coldS true (play τ u (suc i) t₀ (Frame∞.force k)) , absorbed , p ⟩
  stall-next eq ce rewrite eq | ce = λ { refl → refl }

  -- What a close leaves: its cold rekeyed to the frames after it.
  close-next : ∀ {Γ A Γ′ A′} {c : Ctx R Γ A} {s : St Γ A} {c′ : Ctx R Γ′ A′} {τ u i t₀ k key p}
             → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , coldS true (play τ u i t₀ (close k))) leafM key)
             → closed c′ ≡ false → ∀ {t m′} → step ⟨ c , s , absorbed , p ⟩ ≡ silent t m′
             → m′ ≡ ⟨ c′ , coldS true (restᵀ τ (u ++ [ last ]) (From∞.force k)) , absorbed , p ⟩
  close-next eq ce rewrite eq | ce = λ { refl → refl }

  -- A stall drops its skip: the tree refocused at the cold searched out.
  -- A STALL OR A CLOSE WHERE IT IS SHOWN IS SHOWN NEXT: every frame
  -- above the cold searched out passes its lead skip, its key the cold's.
  stall-pass : ∀ {Γ A Γ′ A′} {c : Ctx R Γ A} {s : St Γ A} {c′ : Ctx R Γ′ A′} {τ u i t₀ k key p}
             → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , coldS true (play τ u i t₀ (stall k))) leafM key)
             → shows c′ true ≡ true → Inv ⟨ c , s , absorbed , p ⟩
             → Pass (_≡ u ++ [ ix i ]) c′ true (U.stateᴺ (gh (coldS true (play τ u i t₀ (stall k)))) (envAt c′))
                 (U.stateᴺ (gh (coldS true (play τ u (suc i) t₀ (Frame∞.force k)))) (envAt c′))
  stall-pass {c = c} {s} {c′} {τ} {u} {i} {t₀} {k} eq sh iv =
    beat-pass false (u ++ [ ix i ]) c′ (coldS true (play τ u i t₀ (stall k))) true (λ _ e → e)
      (subst (λ x → Beat x c′ (coldS true (play τ u i t₀ (stall k)))) (cold-key (plug c s) eq) (subst Beats eq (Order.apart (Inv.ord iv)) refl))
      (subst Frag (sym (proj₁ (search-hit (plug c s) eq))) (Order.shape (Inv.ord iv))) tt
      sh refl (≋-by refl refl) (stall-hole (envAt c′))

  close-pass : ∀ {Γ A Γ′ A′} {c : Ctx R Γ A} {s : St Γ A} {c′ : Ctx R Γ′ A′} {τ u i t₀ k key p}
             → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , coldS true (play τ u i t₀ (close k))) leafM key)
             → shows c′ true ≡ true → Inv ⟨ c , s , absorbed , p ⟩
             → Pass (_≡ u ++ [ ix i ]) c′ true (U.stateᴺ (gh (coldS true (play τ u i t₀ (close k)))) (envAt c′))
                 (U.stateᴺ (gh (coldS true (restᵀ τ (u ++ [ last ]) (From∞.force k)))) (envAt c′))
  close-pass {c = c} {s} {c′} {τ} {u} {i} {t₀} {k} eq sh iv =
    beat-pass false (u ++ [ ix i ]) c′ (coldS true (play τ u i t₀ (close k))) true (λ _ e → e)
      (subst (λ x → Beat x c′ (coldS true (play τ u i t₀ (close k)))) (cold-key (plug c s) eq) (subst Beats eq (Order.apart (Inv.ord iv)) refl))
      (subst Frag (sym (proj₁ (search-hit (plug c s) eq))) (Order.shape (Inv.ord iv))) tt
      sh refl (≋-by refl refl) (close-hole (envAt c′))

  stall-drop : ∀ {Γ A Γ′ A′} {c : Ctx R Γ A} {s : St Γ A} {c′ : Ctx R Γ′ A′} {τ u i t₀ k key p t m′}
             → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , coldS true (play τ u i t₀ (stall k))) leafM key)
             → closed c′ ≡ false → Inv ⟨ c , s , absorbed , p ⟩ → step ⟨ c , s , absorbed , p ⟩ ≡ silent t m′
             → Drop ⟨ c , s , absorbed , p ⟩ m′
  stall-drop {c = c} {s} {c′} {τ} {u} {i} {t₀} {k} {p = p} eq ce iv e with shows c′ true in sh
  ... | false = stall-tail eq sh iv e
  ... | true with stall-next {c = c} {s = s} {p = p} eq ce e
  ...   | refl = drops-agree (refocus-agree c s c′ (coldS true (play τ u i t₀ (stall k))) p (Base.settled (Inv.base iv)) tt (wfI (Inv.base iv)) (proj₁ (search-hit (plug c s) eq)))
                   (lift-drops (_≡ u ++ [ ix i ]) c′ true (stall-hole (envAt c′)) (stall-pass eq sh iv))

  -- A close drops its skip, as a stall does.
  close-drop : ∀ {Γ A Γ′ A′} {c : Ctx R Γ A} {s : St Γ A} {c′ : Ctx R Γ′ A′} {τ u i t₀ k key p t m′}
             → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , coldS true (play τ u i t₀ (close k))) leafM key)
             → closed c′ ≡ false → Inv ⟨ c , s , absorbed , p ⟩ → step ⟨ c , s , absorbed , p ⟩ ≡ silent t m′
             → Drop ⟨ c , s , absorbed , p ⟩ m′
  close-drop {c = c} {s} {c′} {τ} {u} {i} {t₀} {k} {p = p} eq ce iv e with shows c′ true in sh
  ... | false = close-tail eq sh iv e
  ... | true with close-next {c = c} {s = s} {p = p} eq ce e
  ...   | refl = drops-agree (refocus-agree c s c′ (coldS true (play τ u i t₀ (close k))) p (Base.settled (Inv.base iv)) tt (wfI (Inv.base iv)) (proj₁ (search-hit (plug c s) eq)))
                   (lift-drops (_≡ u ++ [ ix i ]) c′ true (close-hole (envAt c′)) (close-pass eq sh iv))

  -- A step whose work may grow drops a skip.
  skipped-drop : ∀ {m t m′} → Inv m → step m ≡ silent t m′ → Skipped m → Drop m m′
  skipped-drop iv e outerᵏ          = outer-drop iv e
  skipped-drop iv e (laneᵏ al)      = lane-drop al iv e
  skipped-drop iv e deferᵏ          = defer-drop iv e
  skipped-drop iv e (stallᵏ eq ce)  = stall-drop eq ce iv e
  skipped-drop iv e (closeᵏ eq ce)  = close-drop eq ce iv e

  -- Past erased skips every item lies no deeper.
  ahead-erase : ∀ {x y : Events R} {k n} → Eraseᴱ n x y → (a : Ahead x k) → depth a < n → Σ (Ahead y k) λ b → depth b ≤ depth a
  ahead-erase e noneᵃ lt = noneᵃ , z≤n
  ahead-erase stopᴱ (outᵃ a) ()
  ahead-erase stopᴱ (skipᵃ a) ()
  ahead-erase stopᴱ endᵃ ()
  ahead-erase stopᴱ hushᵃ ()
  ahead-erase (outᴱ e) (outᵃ a) (s≤s lt) with ahead-erase e a lt
  ... | b , le = outᵃ b , s≤s le
  ahead-erase (skipᴱ e) (skipᵃ a) (s≤s lt) with ahead-erase e a lt
  ... | b , le = skipᵃ b , s≤s le
  ahead-erase (erasedᴱ e) (skipᵃ a) (s≤s lt) with ahead-erase e a lt
  ... | b , le = b , m≤n⇒m≤1+n le
  ahead-erase endᴱ endᵃ lt = endᵃ , z≤n
  ahead-erase hushᴱ hushᵃ lt = hushᵃ , z≤n

  -- Past dropped skips every item lies shallower.
  drop-suc : ∀ {e e′ k} → Drops e e′ → (c : Ahead e (suc k)) → Σ (Ahead e′ (suc k)) λ c₀ → depth c₀ < depth c
  drop-suc (drop ag ag′) c with ahead-agree ag c
  ... | skipᵃ c′ , de with ahead-erase (ag′ (suc (depth c′))) c′ ≤-refl
  ...   | c₀ , le = c₀ , ≤-<-trans le (subst (depth c′ <_) de ≤-refl)
  drop-suc (drops ag d) c with ahead-agree ag c
  ... | skipᵃ c′ , de with drop-suc d c′
  ...   | c₀ , lt = c₀ , <-trans lt (subst (depth c′ <_) de ≤-refl)

  -- A silent step brings every item the configuration's meaning reaches
  -- nearer: shallower, or as deep with less work left.
  silent-lowers : ∀ {m t m′} → Inv m → step m ≡ silent t m′ → Lowers m m′
  silent-lowers iv e c with silent-exact iv e | silent-spent iv e
  ... | inj₁ d  | _       = proj₁ (drop-suc d c) , inj₁ (proj₂ (drop-suc d c))
  ... | inj₂ sm | inj₁ lt = proj₁ (ahead-agree sm c) , inj₂ (proj₂ (ahead-agree sm c) , lt)
  ... | inj₂ sm | inj₂ sk = proj₁ (drop-suc (skipped-drop iv e sk) c) , inj₁ (proj₂ (drop-suc (skipped-drop iv e sk) c))

  -- A silent step keeps the configuration running its ghost.
  agrees-silent : ∀ {g m t m′} → Agrees g m → step m ≡ silent t m′ → Agrees g m′
  agrees-silent {m = m} {m′ = m′} ag e = record
    { inv   = subst NextInv e (inv-next m (Agrees.inv ag))
    ; same  = ≅-trans (Agrees.same ag) (subst (KeptFrom (M m)) e (engine-kept m (Agrees.inv ag)))
    ; ahead = λ x → nearer (Agrees.ahead ag x)
    }
    where
    nearer : ∀ {k} → Ahead (M m) k → Ahead (M m′) k
    nearer {zero}  c = noneᵃ
    nearer {suc k} c = proj₁ (silent-lowers (Agrees.inv ag) e c)

  -- A carried configuration's silent step runs on to a re-entry
  -- configuration: the same ghost, every item nearer.
  carried-silent : ∀ {g m t m′} (cr : Carried g m) → step m ≡ silent t m′ → Hopped (carried cr) m′
  carried-silent {g} {m} {t} {m′} cr e =
    g , m′ , now , carried cr′ , lowered (λ n → agree-refl n _) (silent-lowers (Agrees.inv (Carried.agrees cr)) e)
    where
    cr′ : Carried g m′
    cr′ = record { sane = Carried.sane cr ; placed = Carried.placed cr ; agrees = agrees-silent (Carried.agrees cr) e }

  -- A carried configuration's step: its value shown, its completion,
  -- its drain, or a silent run on to a re-entry configuration.  After a
  -- value the stepped ghost keeps the stepper's invariants.
  carried-hop : ∀ {g m} (cr : Carried g m) → Hop (carried cr)
  carried-hop {g} cr with agrees-moves (Carried.sane cr) (Carried.placed cr) (Carried.agrees cr)
  ... | valueᴹ {m′ = m′} eq ld ck least ag with leads-past (Carried.sane cr) (Carried.placed cr) ld
  ...   | g₀ , _ , e₀ , sn₀ , pl₀ = valueᴴ eq ld ck least (m′ , now , carried record
          { sane = sane-out {g = g₀} sn₀ e₀ ; placed = proj₂ (subst (Placedˢ []) e₀ (placed-after g₀ sn₀ pl₀)) ; agrees = ag })
  carried-hop cr | completeᴹ eq ld = completeᴴ eq ld
  carried-hop cr | drainedᴹ eq no  = drainedᴴ eq no
  carried-hop cr | silentᴹ eq      = silentᴴ eq (carried-silent cr eq)

  -- By the re-entry state.
  strong-hop : ∀ {g m} (st : Strong g m) → Hop st
  strong-hop (carried cr) = carried-hop cr

  strong-shows : ∀ {rest g m} → Strong g m → rest ≅ residual g → Shows rest (step m)
  strong-shows {rest} {g} st e with strong-hop st
  ... | valueᴴ {g′ = g′} eq ld ck least mi = subst (Shows rest) (sym eq)
    (valueˢ ck (proj₂ e (proj₁ rs)) (λ h → proj₂ e (proj₁ (proj₂ rs) h)) (λ h → proj₂ (proj₂ rs) (proj₁ e h)) least
      (record { ghost = g′ ; same = ≅-refl ; mirror = mi }))
    where rs = strong-steps st ld
  ... | completeᴴ eq ld = subst (Shows rest) (sym eq) (completeˢ (proj₂ e (proj₁ rs)) λ h → proj₂ rs (proj₁ e h))
    where rs = strong-steps st ld
  ... | drainedᴴ eq no = subst (Shows rest) (sym eq) (drainedˢ λ h → no (proj₁ e h))
  ... | silentᴴ eq h = subst (Shows rest) (sym eq) (silentˢ (onward {g = g} e h))

  -- Every step shows the residual: on the way to a re-entry
  -- configuration a silent step keeps the ghost.
  inner-next : ∀ {rest m} → Inner rest m → Shows rest (step m)
  inner-next i with Inner.mirror i
  ... | m₀ , now , st          = strong-shows st (Inner.same i)
  ... | m₀ , then eq path , st =
    subst (Shows _) (sym eq) (silentˢ (record { ghost = Inner.ghost i ; same = Inner.same i ; mirror = m₀ , path , st }))
