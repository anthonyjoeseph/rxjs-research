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

open import Data.Bool using (true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ʳ; ++⁻)
open import Data.List.Relation.Unary.All using ([])
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Nat using (ℕ; zero; suc; _<_; _<ᵇ_)
open import Data.Nat.Properties using (suc-injective; ≤-refl; <-trans)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList.Events using (Events; Events∞; Pos; Time; tick; root; out; skip; end; hush; _<ᵖ_; <ᵖ-irrefl; <ᵖ-asym; emit; stall; close)
open import denotation.MonotonicList using (observe; Agree; agree-refl; agree-sym)
open import adequacy.Record using (Ahead; outᵃ; skipᵃ) renaming (none to noneᵃ)
import denotation.Unfold as U
open import denotation.Denote using (⟦_⟧)
open import operation.PureObservable using (PureObs; module Driver; module Machine; module Pure; play; ending; over)
open import adequacy.Sorted using (_≤ᵖ_)
open import adequacy.Sane using (Sane; SaneS; step-sane; sane-out)
open import adequacy.Placed.Order using (Placed)
open import adequacy.Placed.Trail using (t≢f)
open import adequacy.Stepper.Past using (_≃_; Placedˢ)
open import adequacy.Stepper.Within using (placed-after)
open import adequacy.Stepper using (step-skips)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Engine.Meaning using (M; Has; atOut; atEnd; pastOut; _≅_; ≅-refl; ≅-sym; ≅-trans; agree-≅)
open import adequacy.Engine.Inv using (Inv; NextInv; inv-next)
open import adequacy.Engine.Kept using (KeptFrom) renaming (kept to engine-kept)
open import adequacy.Strong using (module Strongly)
open Events∞ using (force)

module Honesty (R : Set) where
  open Driver R using (Step; silent; value; complete; drained; step; reading; Read; read; later; played; took)
  open Machine using (Conf; load; moved; starting; turn; quiet; gone; leaf; nx; cp) renaming (step to stepᴹ)
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

  -- A run past one or more of its leading skips.
  data Drops (e e′ : Events R) : Set where
    drop  : ∀ {k r} → (∀ n → Agree n e (skip k r)) → (∀ n → Agree n (force r) e′) → Drops e e′
    drops : ∀ {k r} → (∀ n → Agree n e (skip k r)) → Drops (force r) e′ → Drops e e′

  -- A step dropping leading skips of what its configuration means.
  Drop : Conf R → Conf R → Set
  Drop m m′ = Drops (M m) (M m′)

  -- Two configurations meaning the same, at every depth.
  Same : Conf R → Conf R → Set
  Same m m′ = ∀ n → Agree n (M m) (M m′)

  postulate
    -- A SILENT STEP DROPS SKIPS OR KEEPS ITS MEANING: a stall, a frame's
    -- close, a defer begun or a value absorbed drops one or more leading
    -- skips of what the configuration means (a defer begun drops every
    -- skip its subscription's subtree leads with); every other silent
    -- step means the same.
    silent-exact : ∀ {m t m′} → Inv m → step m ≡ silent t m′ → Drop m m′ ⊎ Same m m′

    -- A SILENT STEP KEEPING ITS MEANING IS WORK DONE in the
    -- configuration's control.
    --
    -- DEAD ROUTE: a measure on the configuration alone, lowered while the
    --   ghost's next step is no skip.  Agreement as a set lets a ghost
    --   showing nothing run a cold stalling forever, whose silent run no
    --   measure bounds; only an item its meaning reaches bounds it.
    silent-work : ∀ {m t m′} → Inv m → step m ≡ silent t m′ → Same m m′ → work m′ ≺ work m

  -- Past dropped skips every item lies shallower.
  drop-suc : ∀ {e e′ k} → Drops e e′ → (c : Ahead e (suc k)) → Σ (Ahead e′ (suc k)) λ c₀ → depth c₀ < depth c
  drop-suc (drop ag ag′) c with ahead-agree ag c
  ... | skipᵃ c′ , de with ahead-agree ag′ c′
  ...   | c₀ , de′ = c₀ , subst (_< _) (sym de′) (subst (depth c′ <_) de ≤-refl)
  drop-suc (drops ag d) c with ahead-agree ag c
  ... | skipᵃ c′ , de with drop-suc d c′
  ...   | c₀ , lt = c₀ , <-trans lt (subst (depth c′ <_) de ≤-refl)

  -- A silent step brings every item the configuration's meaning reaches
  -- nearer: shallower, or as deep with less work left.
  silent-lowers : ∀ {m t m′} → Inv m → step m ≡ silent t m′ → Lowers m m′
  silent-lowers iv e c with silent-exact iv e
  ... | inj₁ d  = proj₁ (drop-suc d c) , inj₁ (proj₂ (drop-suc d c))
  ... | inj₂ sm = proj₁ (ahead-agree sm c) , inj₂ (proj₂ (ahead-agree sm c) , silent-work iv e sm)

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

  -- THE MACHINE HONEST TO `e`: what its record has is among `e`, and
  -- what of `e` it has not lies in `rest`, past every mark, which the
  -- configuration will deliver.
  record HonMach (e : Events R) (qs : List Pos) (xs : List (Time × R)) (m : Conf R) : Set₁ where
    field
      rest   : Events R
      logged : ∀ {k a} → Sent qs xs k a → Has e k (just a)
      split  : ∀ {k b} → Has e k b → Logged qs xs k b ⊎ Has rest k b
      past   : ∀ {k b} → Has rest k b → Any (k ≤ᵖ_) qs → ⊥
      paired : length qs ≡ length xs
      within : ∀ {k b} → Has rest k b → Has e k b
      inner  : Inner rest m

  -- A completion is the events' end, the residual holding no value.
  ends : ∀ {e qs xs m p} (h : HonMach e qs xs m) → step m ≡ complete p → Has e p nothing × (∀ {k a} → Has (HonMach.rest h) k (just a) → ⊥)
  ends h eq with subst (Shows (HonMach.rest h)) eq (inner-next (HonMach.inner h))
  ... | completeˢ x none = HonMach.within h x , none

  -- A drained run has delivered all of it.
  dries : ∀ {e qs xs m} (h : HonMach e qs xs m) → step m ≡ drained → ∀ {k b} → Has (HonMach.rest h) k b → ⊥
  dries h eq with subst (Shows (HonMach.rest h)) eq (inner-next (HonMach.inner h))
  ... | drainedˢ none = none

  -- A launch is honest to the meaning's events at the root, all of them
  -- still owed.
  honest-launch : (o : PureObs [] R) → HonMach (observe (⟦ o ⟧ []) root) [] [] (load o)
  honest-launch o = record
    { rest = observe (⟦ o ⟧ []) root ; logged = λ () ; split = inj₂ ; past = λ _ () ; paired = refl ; within = λ x → x ; inner = inner-launch o }

  -- A value sent is at one of the record's marks.
  sent-mark : ∀ {qs xs k a} → Sent qs xs k a → Any (k ≡_) qs
  sent-mark sentHere      = here refl
  sent-mark (sentLater s) = there (sent-mark s)

  -- Marks past the record's end send nothing more, and lose nothing.
  sent-++ : ∀ {qs xs k a} ys → Sent qs xs k a → Sent (qs ++ ys) xs k a
  sent-++ ys sentHere      = sentHere
  sent-++ ys (sentLater s) = sentLater (sent-++ ys s)

  sent-cut : ∀ {qs xs ys k a} → length qs ≡ length xs → Sent (qs ++ ys) xs k a → Sent qs xs k a
  sent-cut {[]}    {[]}    eq ()
  sent-cut {_ ∷ _} {_ ∷ _} eq sentHere      = sentHere
  sent-cut {_ ∷ qs} {_ ∷ xs} eq (sentLater s) = sentLater (sent-cut {qs} {xs} (suc-injective eq) s)

  -- An honest machine's record is alike its events, however it stands.
  honest-alike : ∀ {e qs xs m en qs′} → HonMach e qs xs m → Stands m qs en qs′ → Alike en qs′ xs e
  honest-alike h cutʰ = record
    { sound = logged
    ; whole = λ x ow → [ (λ s → s) , (λ r → ⊥-elim (past r ow)) ]′ (split x)
    ; ended = tt
    }
    where open HonMach h
  honest-alike {qs = qs} {xs} h (finʰ {p} eq) = record
    { sound = λ s → logged (sent-cut {qs} {xs} paired s)
    ; whole = λ x _ → [ sent-++ [ p ] , (λ r → ⊥-elim (proj₂ (ends h eq) r)) ]′ (split x)
    ; ended = p , proj₁ (ends h eq) , ++⁺ʳ qs (here refl)
    }
    where open HonMach h
  honest-alike h (dryʰ eq) = record
    { sound = logged
    ; whole = λ x _ → [ (λ s → s) , (λ r → ⊥-elim (dries h eq r)) ]′ (split x)
    ; ended = ended
    }
    where
    open HonMach h
    ended : ∀ {k b} → Has _ k b → Any (k ≤ᵖ_) _
    ended {b = just a}  x with split x
    ... | inj₁ s = Any.map inj₁ (sent-mark s)
    ... | inj₂ r = ⊥-elim (dries h eq r)
    ended {b = nothing} x with split x
    ... | inj₁ ()
    ... | inj₂ r = ⊥-elim (dries h eq r)

  -- The record grown by one entry keeps what it sent, and sends the new
  -- entry at its mark.
  sent-snoc-keep : ∀ {qs xs ys zs k a} → Sent qs xs k a → Sent (qs ++ ys) (xs ++ zs) k a
  sent-snoc-keep sentHere      = sentHere
  sent-snoc-keep (sentLater s) = sentLater (sent-snoc-keep s)

  logged-snoc : ∀ {qs xs ys zs k b} → Logged qs xs k b → Logged (qs ++ ys) (xs ++ zs) k b
  logged-snoc {b = just a} s = sent-snoc-keep s

  sent-last : ∀ {qs xs q a} → length qs ≡ length xs → Sent (qs ++ [ q ]) (xs ++ [ (tick q , a) ]) q a
  sent-last {[]}     {[]}     eq = sentHere
  sent-last {_ ∷ qs} {_ ∷ xs} eq = sentLater (sent-last {qs} {xs} (suc-injective eq))

  sent-snoc : ∀ {qs xs q x k a} → length qs ≡ length xs → Sent (qs ++ [ q ]) (xs ++ [ x ]) k a → Sent qs xs k a ⊎ (k ≡ q × x ≡ (tick k , a))
  sent-snoc {[]}    {[]}    eq sentHere      = inj₂ (refl , refl)
  sent-snoc {[]}    {[]}    eq (sentLater ())
  sent-snoc {_ ∷ _} {_ ∷ _} eq sentHere      = inj₁ sentHere
  sent-snoc {_ ∷ qs} {_ ∷ xs} eq (sentLater s) = [ (λ s′ → inj₁ (sentLater s′)) , inj₂ ]′ (sent-snoc {qs} {xs} (suc-injective eq) s)

  snoc-length : ∀ {A B : Set} {qs : List A} {xs : List B} {q x} → length qs ≡ length xs → length (qs ++ [ q ]) ≡ length (xs ++ [ x ])
  snoc-length {qs = []}    {[]}    eq = refl
  snoc-length {qs = _ ∷ qs} {_ ∷ xs} eq = cong suc (snoc-length {qs = qs} {xs} (suc-injective eq))

  -- One step keeps the machine honest: a silent one keeps its record
  -- and its residual; a value moves the residual's lead into the record.
  honest-step : ∀ {e qs xs m t m′} → HonMach e qs xs m → step m ≡ silent t m′ → HonMach e qs xs m′
  honest-step h eq with subst (Shows (HonMach.rest h)) eq (inner-next (HonMach.inner h))
  ... | silentˢ i = record { rest = rest ; logged = logged ; split = split ; past = past ; paired = paired ; within = within ; inner = i }
    where open HonMach h

  private
    honest-value : ∀ {e qs xs m t p a m′} → HonMach e qs xs m → step m ≡ value t p a m′ → HonMach e (qs ++ [ p ]) (xs ++ [ (t , a) ]) m′
    honest-value {e} {qs} {xs} {m} {t} {p} {a} h eq with subst (Shows (HonMach.rest h)) eq (inner-next (HonMach.inner h))
    ... | valueˢ {r = r′} tp x₀ sub sp beyond i = record
      { rest   = r′
      ; logged = logged′
      ; split  = split′
      ; past   = past′
      ; paired = snoc-length {qs = qs} {xs} paired
      ; within = λ x → within (sub x)
      ; inner  = i
      }
      where
      open HonMach h
      logged′ : ∀ {k a′} → Sent (qs ++ [ p ]) (xs ++ [ (t , a) ]) k a′ → Has e k (just a′)
      logged′ s with sent-snoc {qs} {xs} paired s
      ... | inj₁ s′       = logged s′
      ... | inj₂ (kp , x) = subst₂ (λ k a′ → Has e k (just a′)) (sym kp) (cong proj₂ x) (within x₀)
      split′ : ∀ {k b} → Has e k b → Logged (qs ++ [ p ]) (xs ++ [ (t , a) ]) k b ⊎ Has r′ k b
      split′ x with split x
      ... | inj₁ lg = inj₁ (logged-snoc lg)
      ... | inj₂ y with sp y
      ...   | inj₂ y′       = inj₂ y′
      ...   | inj₁ (kp , ba) = inj₁ (subst₂ (λ k b → Logged (qs ++ [ p ]) (xs ++ [ (t , a) ]) k b) (sym kp) (sym ba)
                                      (subst (λ t′ → Sent (qs ++ [ p ]) (xs ++ [ (t′ , a) ]) p a) (sym tp) (sent-last {qs} {xs} paired)))
      past′ : ∀ {k b} → Has r′ k b → Any (k ≤ᵖ_) (qs ++ [ p ]) → ⊥
      past′ x ow with ++⁻ qs ow
      ... | inj₁ o          = past (sub x) o
      ... | inj₂ (here kp)  = beyond x kp
      ... | inj₂ (there ())

  -- Every configuration reached from a launch is honest.
  honest : ∀ {e qs xs m} → Reached e qs xs m → HonMach e qs xs m
  honest (launchedʰ o refl) = honest-launch o
  honest (silentʰ r eq)     = honest-step (honest r) eq
  honest (valueʰ r eq)      = honest-value (honest r) eq

  -- THE MACHINE'S CONTENT: a configuration reached from a launch keeps
  -- a record alike its meaning's events, however it stands.
  kept : ∀ {e qs xs m en qs′} → Reached e qs xs m → Stands m qs en qs′ → Alike en qs′ xs e
  kept r = honest-alike (honest r)

  -- What a reader of the run from a reached configuration has, put after
  -- that configuration's record, is the record of one reached from it,
  -- standing as the reader's run stands.
  Onward : Events R → List Pos → List (Time × R) → Read → Set₁
  Onward e qs xs x = Σ (Conf R) λ m′ → Σ (List Pos) λ qs₁ → Σ (List (Time × R)) λ xs′ → Σ (Reached e qs₁ xs′ m′) λ _ → Σ End λ en
                   → Σ (List Pos) λ qs′ → Stands m′ qs₁ en qs′ × read (qs ++ Read.marks x) (xs ++ Read.log x) (Read.endedAs x) ≡ read qs′ xs′ en

  -- Read to tick `h`: a step past it cuts the record where it stands.
  read-on : ∀ {e qs xs m} → Reached e qs xs m → ∀ h n c → Onward e qs xs (reading h n c m)
  read-on {qs = qs} {xs} {m} r h zero    c = m , qs , xs , r , _ , _ , cutʰ , cong₂ (λ ms ls → read ms ls _) (++-identityʳ qs) (++-identityʳ xs)
  read-on {qs = qs} {xs} {m} r h (suc n) c with step m in eq
  ... | silent t m₁ with h <ᵇ t
  ...   | true  = m , qs , xs , r , _ , _ , cutʰ , cong₂ (λ ms ls → read ms ls _) (++-identityʳ qs) (++-identityʳ xs)
  ...   | false = read-on (silentʰ r eq) h n _
  read-on {qs = qs} {xs} {m} r h (suc n) c | value t p a m₁ with h <ᵇ t
  ...   | true  = m , qs , xs , r , _ , _ , cutʰ , cong₂ (λ ms ls → read ms ls _) (++-identityʳ qs) (++-identityʳ xs)
  ...   | false with read-on (valueʰ r eq) h n t
  ...     | m′ , qs₁ , xs′ , r′ , en , qs′ , st , x = m′ , qs₁ , xs′ , r′ , en , qs′ , st ,
              trans (cong₂ (λ ms ls → read ms ls _) (sym (++-assoc qs [ p ] _)) (sym (++-assoc xs [ (t , a) ] _))) x
  read-on {qs = qs} {xs} {m} r h (suc n) c | complete p = m , qs , xs , r , finished , _ , finʰ eq , cong (λ ls → read _ ls finished) (++-identityʳ xs)
  read-on {qs = qs} {xs} {m} r h (suc n) c | drained    = m , qs , xs , r , dry , _ , dryʰ eq , cong₂ (λ ms ls → read ms ls dry) (++-identityʳ qs) (++-identityʳ xs)

  -- The launch's first n steps, read to tick h, are the record of a
  -- configuration reached from it.
  read-is-kept : (o : PureObs [] R) (n h : ℕ) → Σ (Conf R) λ m′ → Σ (List Pos) λ qs₁ → Σ (List (Time × R)) λ xs′
               → Σ (Reached (observe (⟦ o ⟧ []) root) qs₁ xs′ m′) λ _ → Σ End λ en
               → Σ (List Pos) λ qs → Stands m′ qs₁ en qs × reading h n 0 (load o) ≡ read qs xs′ en
  read-is-kept o n h = read-on (launchedʰ o refl) h n 0

  -- CONTENT: every prefix's record alike the meaning's events as a set.
  content : (o : PureObs [] R) (n h : ℕ) → let x = reading h n 0 (load o) in Alike (Read.endedAs x) (Read.marks x) (Read.log x) (observe (⟦ o ⟧ []) root)
  content o n h with read-is-kept o n h
  ... | m′ , qs₁ , xs′ , r′ , en , qs , st , eq rewrite eq = kept r′ st
