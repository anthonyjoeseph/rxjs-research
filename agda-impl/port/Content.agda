{-# OPTIONS --guardedness #-}

-- CONTENT: the root's record is the meaning's events, as a set.
-- Sortedness (`port.Sorted`) says nothing of WHAT arrives; this says
-- nothing of the ORDER, so neither proof reads the other.
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
module port.Content where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ʳ; ++⁻)
open import Data.List.Relation.Unary.All as All using ([])
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (suc-injective; +-suc; +-monoʳ-≤; n≤1+n; ≤-reflexive; n<1+n; <-trans)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList.Events using (Events; Pos; Time; tick; root; last; ix)
open import denotation.MonotonicList using (observe; Agree; agree-refl)
import denotation.Unfold as U
open import denotation.Denote using (⟦_⟧)
open import operation.PureObservable using (PureObs; module Pure; module Driver; module Machine)
open import port.Sorted using (_≤ᵖ_)
open import port.Sane using (Sane)
open import port.Placed.Order using (Placed)
open import port.Stepper.Past using (_≃_)
open import port.Stepper using (step-skips)
open import port.Unsub using (module Unsubbing)
open import port.Ghost using (module Ghosting)
open import port.Strong using (module Strongly)
open import port.Sorted.Walk using (module SortingWalk)
open import port.Climbs using (module Ascending)

module Honesty (R : Set) where
  open Driver R using (Mach; mach; depthOf; Step; silent; value; complete; drained; step; trace; shown; reading; begin; Read; read; marks; log; ending; noted)
  open Pure R using (End; finished; dry; cutOff)
  open Unsubbing R using (_⇝_; now; then)
  open Ghosting R using (Has; Sent; sentHere; sentLater; Alike; _≋_; same-agree; residual; Reached; launchedʰ; silentʰ; valueʰ;
    Stands; cutʰ; finʰ; dryʰ; Mirror; Inner; Logged; Shows; silentˢ; valueˢ; completeˢ; drainedˢ; inner-launch; ≋-refl;
    Steps; after; steps-after; Hopped; onward; lowered; weight; loadOf)
  open Strongly R using (Strong; Carried; carried; closing; CtlAs; Meets; calmAs; noteAs; runAs; subAs; burstAs; popAs; Pops;
    Kernels; Owned; Meaning; Books; Path; ofˢ; seen)
  open Ascending R using (Aloft; soar)
  open SortingWalk R using (WellMach)
  open Machine using (Ctx; top; plug; downs; dirs; closed; doneS; cp; _⊕_; ⟨_,_,_,_,_⟩; absorbed; rising; resuming; subscribing; nx; pend;
    ofS; cutS; takeS; connS; joinS; next; att; owedCp; owedCut; feeding; attBody; owed; go;
    res; ofR; attR; cpR; cutR; feedR; bodyR; srcR; endR; joinR; idle)

  step-alike : ∀ g → Sane [] g → Placed g [] → residual g ≋ after (U.step g)
  step-alike g sn pl = same-agree (_≃_.agreeing (step-skips g sn pl))

  residual-steps : ∀ g → Sane [] g → Placed g [] → Steps (residual g) (U.step g)
  residual-steps g sn pl = steps-after (U.step g) (step-alike g sn pl)

  -- What a re-entry configuration's ghost is held to.
  strong-sane : ∀ {g m} → Strong g m → Sane [] g × Placed g []
  strong-sane (carried cr)        = Carried.sane cr , Carried.placed cr
  strong-sane (closing _ _ sn pl) = sn , pl

  -- The ghost's residual is what its step shows, at every depth.
  strong-agrees : ∀ {g m} → Strong g m → ∀ n → Agree n (residual g) (after (U.step g))
  strong-agrees {g} st = _≃_.agreeing (step-skips g (proj₁ (strong-sane st)) (proj₂ (strong-sane st)))

  -- THE STRONG STEP: from a re-entry configuration the machine records
  -- the value the ghost's step shows, a least of what it leaves, and runs
  -- the stepped ghost; or ends with the ghost; or drains over a ghost
  -- showing nothing; or runs silently to a ghost past this one's skips.
  data Hop {g m} (st : Strong g m) : Set₁ where
    valueᴴ    : ∀ {t p a m′ g′} → step m ≡ value t p a m′ → U.step g ≡ U.outˢ p a g′ → t ≡ tick p
              → (∀ {q b} → Has (residual g′) q b → q ≤ᵖ p → ⊥) → Mirror g′ m′ → Hop st
    completeᴴ : ∀ {p} → step m ≡ complete p → U.step g ≡ U.endˢ p → Hop st
    drainedᴴ  : step m ≡ drained → (∀ {k b} → Has (residual g) k b → ⊥) → Hop st
    silentᴴ   : ∀ {m′} → step m ≡ silent m′ → Hopped st m′ → Hop st

  postulate
    -- The turn, nothing owed and no timer queued: the ghost shows
    -- nothing.
    turn-dry : ∀ {g m Γ A} {c : Ctx R Γ A} {s p} → Carried g m → Mach.conf m ≡ ⟨ c , s , absorbed , p , [] ⟩
             → Mach.turns m ≡ [] → Mach.timers m ≡ [] → ∀ {k b} → Has (residual g) k b → ⊥

    -- A value recorded is the least the ghost still holds.
    note-least : ∀ {g g′ m s a p rs} → Carried g m → Mach.conf m ≡ ⟨ top , s , rising (nx a) , p , rs ⟩
               → U.step g ≡ U.outˢ p a g′ → ∀ {q b} → Has (residual g′) q b → q ≤ᵖ p → ⊥

    -- The value shown, the configuration runs the stepped ghost.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs.agda
    note-onward : ∀ {g g′ m s a p rs} → Carried g m → Mach.conf m ≡ ⟨ top , s , rising (nx a) , p , rs ⟩
                → U.step g ≡ U.outˢ p a g′ → Mirror g′ (record m { conf = ⟨ top , s , absorbed , p , rs ⟩ })

    -- The `of` a job resumes is the witness's at the job's path.
    of-path : ∀ {g m Γ A} {c : Ctx R Γ A} {xs i p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , ofS xs , resuming (next i) , p , rs ⟩
            → Σ Pos λ p₀ → Σ ℕ λ j → Path (Carried.tree cr) (ofˢ {Γ} {A} p₀ j xs) (dirs c)

    -- An `of` under a closed observer: done, the ghost alike.
    emit-shut : ∀ {g m Γ A} {c : Ctx R Γ A} {xs i p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , ofS xs , resuming (next i) , p , rs ⟩
              → closed c ≡ true → Hopped (carried cr) (record m { conf = ⟨ c , doneS , absorbed , p , rs ⟩ })

    -- A spent `of` the ghost does not hold: its completion climbs
    -- unseen.
    last-void : ∀ {g m Γ A} {c : Ctx R Γ A} {i p rs p₀ j} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , ofS [] , resuming (next i) , p , rs ⟩
              → closed c ≡ false → (ψ : Path (Carried.tree cr) (ofˢ {Γ} {A} p₀ j []) (dirs c)) → seen ψ ≡ false
              → Hopped (carried cr) (record m { conf = ⟨ c , doneS , rising cp , p ⊕ [ last ] , rs ⟩ })

    -- A spent `of` the ghost holds: its completion on its way up.
    last-enter : ∀ {g m Γ A} {c : Ctx R Γ A} {i p rs p₀ j} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , ofS [] , resuming (next i) , p , rs ⟩
               → closed c ≡ false → (ψ : Path (Carried.tree cr) (ofˢ {Γ} {A} p₀ j []) (dirs c)) → seen ψ ≡ true
               → Σ Mach λ m₁ → record m { conf = ⟨ c , doneS , rising cp , p ⊕ [ last ] , rs ⟩ } ⇝ m₁ × Aloft g (loadOf (carried cr)) m₁

    -- An open `of` the ghost does not hold: its value climbs unseen.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Lift/Order.agda
    emit-void : ∀ {g m Γ A} {c : Ctx R Γ A} {x xs i p rs p₀ j} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , ofS (x ∷ xs) , resuming (next i) , p , rs ⟩
              → closed c ≡ false → (ψ : Path (Carried.tree cr) (ofˢ {Γ} {A} p₀ j (x ∷ xs)) (dirs c)) → seen ψ ≡ false
              → Hopped (carried cr) (record m { conf = ⟨ c , ofS xs , rising (nx x) , p ⊕ [ ix i ] , (dirs c , next (suc i) , p) ∷ rs ⟩ })

    -- An open `of` the ghost holds: its value on its way up, the ghost's
    -- step that value lifted.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs.agda
    emit-open : ∀ {g m Γ A} {c : Ctx R Γ A} {x xs i p rs p₀ j} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , ofS (x ∷ xs) , resuming (next i) , p , rs ⟩
              → closed c ≡ false → (ψ : Path (Carried.tree cr) (ofˢ {Γ} {A} p₀ j (x ∷ xs)) (dirs c)) → seen ψ ≡ true
              → Σ Mach λ m₁ → record m { conf = ⟨ c , ofS xs , rising (nx x) , p ⊕ [ ix i ] , (dirs c , next (suc i) , p) ∷ rs ⟩ } ⇝ m₁
                × Aloft g (loadOf (carried cr)) m₁

    -- A subscription's cut handed its unsubscribe, which it stashes, or
    -- throws if already cut: the ghost alike, a job fewer.
    kont-onward : ∀ {g m Γ A} {c : Ctx R Γ A} {l a s p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , cutS l a s , resuming att , p , rs ⟩
                → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′

    -- A takeWhile's completion delivered under its failing value, then
    -- its cut.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs.agda
    take1-onward : ∀ {g m Γ A} {c : Ctx R Γ A} {i q s p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , takeS i q s , resuming owedCp , p , rs ⟩
                 → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′

    -- A takeWhile's cut: what it holds unsubscribed; the ghost alike, a
    -- job fewer.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Lift.agda
    cut-onward : ∀ {g m Γ A} {c : Ctx R Γ A} {i q s p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , takeS i q s , resuming owedCut , p , rs ⟩
               → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′

    -- The rest of a connect's feed: the next joiner fed, or the feed
    -- done.
    feed-onward : ∀ {g m Γ A X} {c : Ctx R Γ A} {k : Machine.CS X} {o b js p rs} (cr : Carried g m)
                → Mach.conf m ≡ ⟨ c , connS k o b , resuming (feeding js) , p , rs ⟩
                → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′

    -- A connect's source subscribed once its body is.
    src-onward : ∀ {g m Γ A X} {c : Ctx R Γ A} {k : Machine.CS X} {o b p rs} (cr : Carried g m)
               → Mach.conf m ≡ ⟨ c , connS k o b , resuming attBody , p , rs ⟩
               → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′

    -- A connect's source handed its unsubscribe: thrown if the body has
    -- ended.
    src-cut-onward : ∀ {g m Γ A X} {c : Ctx R Γ A} {k : Machine.CS X} {o b p rs} (cr : Carried g m)
                   → Mach.conf m ≡ ⟨ c , connS k o b , resuming att , p , rs ⟩
                   → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′

    -- A connect's body ended: its source unsubscribed if attached.
    body-cut-onward : ∀ {g m Γ A X} {c : Ctx R Γ A} {k : Machine.CS X} {o b p rs} (cr : Carried g m)
                    → Mach.conf m ≡ ⟨ c , connS k o b , resuming owed , p , rs ⟩
                    → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′

    -- A joiner fed: what its subject holds for it, on its way up.
    join-onward : ∀ {g m Γ A} {c : Ctx R Γ A} {j x p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , joinS j true x , resuming go , p , rs ⟩
                → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′

    -- AN IDLE JOB DROPPED: what is owed stays owed, what the joiners are
    -- owed stays theirs, the machine stays sorted.
    owned-idle : ∀ {t m Γ A} {c : Ctx R Γ A} {s τ p rs} → Kernels t (Mach.conf m) → Owned t m
               → Mach.conf m ≡ ⟨ c , s , resuming τ , p , rs ⟩ → res s τ ≡ idle
               → Owned t (record m { conf = ⟨ c , s , absorbed , p , rs ⟩ })
    meaning-idle : ∀ {t Γ A} {c : Ctx R Γ A} {s τ p rs} → Kernels t ⟨ c , s , resuming τ , p , rs ⟩
                 → Meaning t ⟨ c , s , resuming τ , p , rs ⟩ → res s τ ≡ idle → Meaning t ⟨ c , s , absorbed , p , rs ⟩
    sorted-idle : ∀ {lo m Γ A} {c : Ctx R Γ A} {s τ p rs} → WellMach lo m
                → Mach.conf m ≡ ⟨ c , s , resuming τ , p , rs ⟩ → res s τ ≡ idle
                → WellMach lo (record m { conf = ⟨ c , s , absorbed , p , rs ⟩ })

    -- A pending node begun, likewise.
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Lift/Order.agda
    sub-onward : ∀ {g m Γ A} {c : Ctx R Γ A} {o p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , pend o , subscribing , p , rs ⟩
               → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′

    -- A turn played, likewise.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Base.agda
    burst-onward : ∀ {g m Γ A} {c : Ctx R Γ A} {s p rs t ts} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , s , absorbed , p , rs ⟩
                 → Mach.turns m ≡ t ∷ ts → (depthOf t <ᵇ length rs) ≡ false
                 → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′

    -- A job owed above the next turn popped and resumed, likewise.
    -- A JOB POPPED: its path leads from the root to where it was
    -- suspended, and resuming it there keeps what is owed; a path leading
    -- nowhere drops it.
    downs-plug : ∀ {q x Γ A} {c′ : Ctx R Γ A} {s′} → downs q top x ≡ just (Γ , A , c′ , s′) → plug c′ s′ ≡ x
    owned-pop : ∀ {t m Γ A Γ′ A′} {c : Ctx R Γ A} {s p q τ p′ rs} {c′ : Ctx R Γ′ A′} {s′}
              → Kernels t (Mach.conf m) → Owned t m → Mach.conf m ≡ ⟨ c , s , absorbed , p , (q , τ , p′) ∷ rs ⟩
              → downs q top (plug c s) ≡ just (_ , _ , c′ , s′)
              → Owned t (record m { conf = ⟨ c′ , s′ , resuming τ , p′ , rs ⟩ })
    meaning-pop : ∀ {t Γ A Γ′ A′} {c : Ctx R Γ A} {s p q τ p′ rs} {c′ : Ctx R Γ′ A′} {s′}
                → Kernels t ⟨ c , s , absorbed , p , (q , τ , p′) ∷ rs ⟩ → Meaning t ⟨ c , s , absorbed , p , (q , τ , p′) ∷ rs ⟩
                → downs q top (plug c s) ≡ just (_ , _ , c′ , s′) → Meaning t ⟨ c′ , s′ , resuming τ , p′ , rs ⟩
    sorted-pop : ∀ {lo m Γ A Γ′ A′} {c : Ctx R Γ A} {s p q τ p′ rs} {c′ : Ctx R Γ′ A′} {s′} → WellMach lo m
               → Mach.conf m ≡ ⟨ c , s , absorbed , p , (q , τ , p′) ∷ rs ⟩ → downs q top (plug c s) ≡ just (_ , _ , c′ , s′)
               → WellMach lo (record m { conf = ⟨ c′ , s′ , resuming τ , p′ , rs ⟩ })
    owned-drop : ∀ {t m Γ A} {c : Ctx R Γ A} {s p j rs} → Kernels t (Mach.conf m) → Owned t m
               → Mach.conf m ≡ ⟨ c , s , absorbed , p , j ∷ rs ⟩ → downs (proj₁ j) top (plug c s) ≡ nothing
               → Owned t (record m { conf = ⟨ c , s , absorbed , p , rs ⟩ })
    meaning-drop : ∀ {t Γ A} {c : Ctx R Γ A} {s p j rs} → Kernels t ⟨ c , s , absorbed , p , j ∷ rs ⟩
                 → Meaning t ⟨ c , s , absorbed , p , j ∷ rs ⟩ → downs (proj₁ j) top (plug c s) ≡ nothing
                 → Meaning t ⟨ c , s , absorbed , p , rs ⟩
    sorted-drop : ∀ {lo m Γ A} {c : Ctx R Γ A} {s p j rs} → WellMach lo m
                → Mach.conf m ≡ ⟨ c , s , absorbed , p , j ∷ rs ⟩ → downs (proj₁ j) top (plug c s) ≡ nothing
                → WellMach lo (record m { conf = ⟨ c , s , absorbed , p , rs ⟩ })

    -- The next timer fired, likewise.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs.agda
    turn-pops : ∀ {g m Γ A} {c : Ctx R Γ A} {s p tm tms} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , s , absorbed , p , [] ⟩
              → Mach.turns m ≡ [] → Mach.timers m ≡ tm ∷ tms → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′

  -- An absorbed configuration is a re-entry state: calm, a turn to play,
  -- or a job to pop.
  private
    settled : ∀ {Γ A} {c : Ctx R Γ A} {s p} rs clk tms ts → CtlAs (mach ⟨ c , s , absorbed , p , rs ⟩ clk tms ts)
    settled []       clk tms []       = calmAs refl refl
    settled []       clk tms (t ∷ ts) = burstAs refl refl refl
    settled (j ∷ rs) clk tms []       = popAs refl tt
    settled (j ∷ rs) clk tms (t ∷ ts) with depthOf t <ᵇ suc (length rs) in d
    ... | true  = popAs refl d
    ... | false = burstAs refl refl d

    settled-meets : ∀ {Γ A} {c : Ctx R Γ A} {s p} rs clk tms ts {n g} → n ≡ just g → Meets (settled {c = c} {s} {p} rs clk tms ts) n g
    settled-meets []       clk tms []       e = e
    settled-meets []       clk tms (t ∷ ts) e = e
    settled-meets (j ∷ rs) clk tms []       e = e
    settled-meets (j ∷ rs) clk tms (t ∷ ts) e with depthOf t <ᵇ suc (length rs)
    ... | true  = e
    ... | false = e

    -- Settling a job's run weighs less than running it.
    settled-lighter : ∀ {Γ A} {c : Ctx R Γ A} {s p} rs clk tms ts
                    → weight (settled {c = c} {s} {p} rs clk tms ts) < suc (length rs) + suc (length rs)
    settled-lighter []       clk tms []       = s≤s z≤n
    settled-lighter []       clk tms (t ∷ ts) = s≤s z≤n
    settled-lighter (j ∷ rs) clk tms []       = popped (suc (length rs))
      where popped : ∀ a → suc (suc (a + a)) ≤ suc a + suc a
            popped a = s≤s (s≤s (≤-reflexive (sym (+-suc a a))))
    settled-lighter (j ∷ rs) clk tms (t ∷ ts) with depthOf t <ᵇ suc (length rs)
    ... | true  = s≤s (s≤s (≤-reflexive (sym (+-suc (suc (length rs)) (suc (length rs))))))
    ... | false = s≤s (+-monoʳ-≤ (suc (length rs)) (n≤1+n (suc (length rs))))

  -- A job owed nothing by its node: dropped, the ghost alike, the
  -- control lighter.
  idle-onward : ∀ {g m Γ A} {c : Ctx R Γ A} {s t p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , s , resuming t , p , rs ⟩
              → res s t ≡ idle → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′
  idle-onward {g} {mach _ clk tms ts} {c = c} {s} {t} {p} {rs} cr refl r with Carried.ctlAs cr | Carried.meets cr
  ... | runAs refl | mt =
    m′ , cong (Driver.took R _) (cong (λ x → Machine.resumeR c x p rs) r)
    , g , m′ , now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = Carried.tree cr
        ; kernels = Carried.kernels cr ; ctlAs = settled rs clk tms ts ; meets = settled-meets rs clk tms ts mt
        ; owned = owned-idle (Carried.kernels cr) (Carried.owned cr) refl r
        ; meaning = meaning-idle (Carried.kernels cr) (Carried.meaning cr) r
        ; queue = Carried.queue cr
        ; books = record { clocked = tt ; ticked = Books.ticked (Carried.books cr) ; turned = Books.turned (Carried.books cr) }
        ; sorted = proj₁ (Carried.sorted cr) , sorted-idle (proj₂ (Carried.sorted cr)) refl r
        ; behind = Carried.behind cr ; lingers = Carried.lingers cr ; told = Carried.told cr
        ; ended = Carried.ended cr ; flags = Carried.flags cr })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , settled-lighter rs clk tms ts))
    where m′ = mach ⟨ c , s , absorbed , p , rs ⟩ clk tms ts
  ... | calmAs () _  | _
  ... | noteAs () _  | _
  ... | subAs ()     | _
  ... | burstAs () _ _ | _
  ... | popAs () _   | _

  private
    -- A pop is the configuration's own step: the turns wait.
    pop-step : ∀ {m Γ A} {c : Ctx R Γ A} {s p j rs} → Mach.conf m ≡ ⟨ c , s , absorbed , p , j ∷ rs ⟩
             → Pops (Mach.turns m) (suc (length rs)) → step m ≡ Driver.took R m (Machine.step (Mach.conf m))
    pop-step {mach _ _ _ []} refl _ = refl
    pop-step {mach _ _ _ (t ∷ ts)} {rs = rs} refl ps with depthOf t <ᵇ suc (length rs) | ps
    ... | true | refl = refl

    popping : ∀ {Γ A Γ′ A′} {c : Ctx R Γ A} {s p q τ p′ rs} {c′ : Ctx R Γ′ A′} {s′}
            → downs q top (plug c s) ≡ just (_ , _ , c′ , s′)
            → Machine.step ⟨ c , s , absorbed , p , (q , τ , p′) ∷ rs ⟩ ≡ Machine.ok ⟨ c′ , s′ , resuming τ , p′ , rs ⟩
    popping d rewrite d = refl

    dropping : ∀ {Γ A} {c : Ctx R Γ A} {s p q τ p′ rs} → downs q top (plug c s) ≡ nothing
             → Machine.step ⟨ c , s , absorbed , p , (q , τ , p′) ∷ rs ⟩ ≡ Machine.ok ⟨ c , s , absorbed , p , rs ⟩
    dropping d rewrite d = refl

  -- A job popped: resumed where it was suspended, or dropped, the ghost
  -- alike, the control lighter.
  pop-onward : ∀ {g m Γ A} {c : Ctx R Γ A} {s p j rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , s , absorbed , p , j ∷ rs ⟩
             → Pops (Mach.turns m) (suc (length rs)) → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′
  pop-onward {g} {mach k clk tms ts} {c = c} {s} {p} {q , τ , p′} {rs} cr e ps
    with Carried.ctlAs cr | Carried.meets cr | downs q top (plug c s) in d
  ... | popAs refl _ | mt | just (_ , _ , c′ , s′) =
    m′ , trans (pop-step e ps) (cong (Driver.took R _) (popping d))
    , g , m′ , now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = Carried.tree cr
        ; kernels = trans (Carried.kernels cr) (sym (downs-plug d)) ; ctlAs = runAs refl ; meets = mt
        ; owned = owned-pop (Carried.kernels cr) (Carried.owned cr) e d
        ; meaning = meaning-pop (Carried.kernels cr) (Carried.meaning cr) d
        ; queue = Carried.queue cr
        ; books = record { clocked = All.head (Books.ticked (Carried.books cr))
                         ; ticked = All.tail (Books.ticked (Carried.books cr)) ; turned = Books.turned (Carried.books cr) }
        ; sorted = proj₁ (Carried.sorted cr) , sorted-pop (proj₂ (Carried.sorted cr)) e d
        ; behind = Carried.behind cr ; lingers = Carried.lingers cr ; told = Carried.told cr
        ; ended = Carried.ended cr ; flags = Carried.flags cr })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , n<1+n _))
    where m′ = mach ⟨ c′ , s′ , resuming τ , p′ , rs ⟩ clk tms ts
  ... | popAs refl _ | mt | nothing =
    m′ , trans (pop-step e ps) (cong (Driver.took R _) (dropping d))
    , g , m′ , now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = Carried.tree cr
        ; kernels = Carried.kernels cr ; ctlAs = settled rs clk tms ts ; meets = settled-meets rs clk tms ts mt
        ; owned = owned-drop (Carried.kernels cr) (Carried.owned cr) e d
        ; meaning = meaning-drop (Carried.kernels cr) (Carried.meaning cr) d
        ; queue = Carried.queue cr
        ; books = record { clocked = tt ; ticked = All.tail (Books.ticked (Carried.books cr)) ; turned = Books.turned (Carried.books cr) }
        ; sorted = proj₁ (Carried.sorted cr) , sorted-drop (proj₂ (Carried.sorted cr)) e d
        ; behind = Carried.behind cr ; lingers = Carried.lingers cr ; told = Carried.told cr
        ; ended = Carried.ended cr ; flags = Carried.flags cr })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , <-trans (settled-lighter rs clk tms ts) (n<1+n _)))
    where m′ = mach ⟨ c , s , absorbed , p , rs ⟩ clk tms ts
  ... | calmAs () _  | _ | _
  ... | noteAs () _  | _ | _
  ... | runAs ()     | _ | _
  ... | subAs ()     | _ | _
  ... | burstAs () _ _ | _ | _

  private
    shut-step : ∀ {Γ A} {c : Ctx R Γ A} {xs i p rs} → closed c ≡ true
              → Machine.resumeR c (ofR xs i) p rs ≡ Machine.ok ⟨ c , doneS , absorbed , p , rs ⟩
    shut-step e rewrite e = refl

    last-step : ∀ {Γ A} {c : Ctx R Γ A} {i p rs} → closed c ≡ false
              → Machine.resumeR c (ofR [] i) p rs ≡ Machine.ok ⟨ c , doneS , rising cp , p ⊕ [ last ] , rs ⟩
    last-step e rewrite e = refl

    emit-step : ∀ {Γ A} {c : Ctx R Γ A} {x xs i p rs} → closed c ≡ false
              → Machine.resumeR c (ofR (x ∷ xs) i) p rs ≡ Machine.ok ⟨ c , ofS xs , rising (nx x) , p ⊕ [ ix i ] , (dirs c , next (suc i) , p) ∷ rs ⟩
    emit-step e rewrite e = refl

  -- A spent `of` the ghost holds: its completion delivered at its end.
  emit-last : ∀ {g m Γ A} {c : Ctx R Γ A} {i p rs p₀ j} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , ofS [] , resuming (next i) , p , rs ⟩
            → closed c ≡ false → (ψ : Path (Carried.tree cr) (ofˢ {Γ} {A} p₀ j []) (dirs c)) → seen ψ ≡ true
            → Hopped (carried cr) (record m { conf = ⟨ c , doneS , rising cp , p ⊕ [ last ] , rs ⟩ })
  emit-last cr e cl ψ sn = soar (carried cr) (last-enter cr e cl ψ sn)

  -- An `of`'s next value climbs the observers above it; spent, its
  -- completion; under a closed observer, nothing.
  emit-onward : ∀ {g m Γ A} {c : Ctx R Γ A} {xs i p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , ofS xs , resuming (next i) , p , rs ⟩
              → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′
  emit-onward {m = mach _ clk tms ts} {c = c} {xs} cr refl with closed c in cl
  ... | true = _ , cong (Driver.took R _) (shut-step cl) , emit-shut cr refl cl
  emit-onward {m = mach _ clk tms ts} {c = c} {[]} cr refl | false with of-path cr refl
  ... | _ , _ , ψ with seen ψ in sn
  ...   | false = _ , cong (Driver.took R _) (last-step cl) , last-void cr refl cl ψ sn
  ...   | true  = _ , cong (Driver.took R _) (last-step cl) , emit-last cr refl cl ψ sn
  emit-onward {m = mach _ clk tms ts} {c = c} {x ∷ xs} cr refl | false with of-path cr refl
  ... | _ , _ , ψ with seen ψ in sn
  ...   | false = _ , cong (Driver.took R _) (emit-step cl) , emit-void cr refl cl ψ sn
  ...   | true  = _ , cong (Driver.took R _) (emit-step cl) , soar (carried cr) (emit-open cr refl cl ψ sn)

  -- A job resumed runs silently on to a re-entry configuration the
  -- configuration gains: by the job the node owes (`res`).
  run-onward : ∀ {g m Γ A} {c : Ctx R Γ A} {s t p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , s , resuming t , p , rs ⟩
             → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′
  run-onward {s = s} {t} cr e with s | t | res s t in r
  ... | .(ofS _)          | .(next _)     | ofR _ _       = emit-onward cr e
  ... | .(cutS _ _ _)     | .att          | attR _ _ _    = kont-onward cr e
  ... | .(takeS _ _ _)    | .owedCp       | cpR _ _ _     = take1-onward cr e
  ... | .(takeS _ _ _)    | .owedCut      | cutR _ _ _    = cut-onward cr e
  ... | .(connS _ _ _)    | .(feeding _)  | feedR _ _ _ _ = feed-onward cr e
  ... | .(connS _ _ _)    | .attBody      | bodyR _ _ _   = src-onward cr e
  ... | .(connS _ _ _)    | .att          | srcR _ _ _    = src-cut-onward cr e
  ... | .(connS _ _ _)    | .owed         | endR _ _ _    = body-cut-onward cr e
  ... | .(joinS _ true _) | .go           | joinR _ _     = join-onward cr e
  ... | _                 | _             | idle          = idle-onward cr e r

  -- By the re-entry state.
  strong-hop : ∀ {g m} (st : Strong g m) → Hop st
  strong-hop {m = mach k clk tms ts} (closing refl stp sn pl) = completeᴴ refl stp
  strong-hop {m = mach k clk tms ts} (carried cr) with Carried.ctlAs cr | Carried.meets cr
  ... | noteAs refl ck | g′ , _ , stp = valueᴴ refl stp ck (note-least cr refl stp) (note-onward cr refl stp)
  ... | runAs e | _ with run-onward cr e
  ...   | m′ , eq , h = silentᴴ eq h
  strong-hop {m = mach k clk tms ts} (carried cr) | subAs e | _ with sub-onward cr e
  ...   | m′ , eq , h = silentᴴ eq h
  strong-hop {m = mach k clk tms ts} (carried cr) | burstAs e et lt | _ with burst-onward cr e et lt
  ...   | m′ , eq , h = silentᴴ eq h
  strong-hop {m = mach k clk tms ts} (carried cr) | popAs e ps | _ with pop-onward cr e ps
  ...   | m′ , eq , h = silentᴴ eq h
  strong-hop {m = mach k clk [] ts} (carried cr) | calmAs refl refl | _ = drainedᴴ refl (turn-dry cr refl refl refl)
  strong-hop {m = mach k clk (tm ∷ tms) ts} (carried cr) | calmAs refl refl | _ = silentᴴ refl (turn-pops cr refl refl refl refl)

  strong-shows : ∀ {rest g m} → Strong g m → rest ≋ residual g → Shows rest (step m)
  strong-shows {rest} {g} st e with strong-hop st
  ... | valueᴴ {g′ = g′} eq stp ck least mi = subst (Shows rest) (sym eq)
    (valueˢ ck (proj₂ e (proj₁ rs)) (λ h → proj₂ e (proj₁ (proj₂ rs) h)) (λ h → proj₂ (proj₂ rs) (proj₁ e h)) least
      (record { ghost = g′ ; same = ≋-refl ; mirror = mi }))
    where rs = subst (Steps (residual g)) stp (residual-steps g (proj₁ (strong-sane st)) (proj₂ (strong-sane st)))
  ... | completeᴴ eq stp = subst (Shows rest) (sym eq) (completeˢ (proj₂ e (proj₁ rs)) λ h → proj₂ rs (proj₁ e h))
    where rs = subst (Steps (residual g)) stp (residual-steps g (proj₁ (strong-sane st)) (proj₂ (strong-sane st)))
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
  record HonMach (e : Events R) (qs : List Pos) (xs : List (Time × R)) (m : Mach) : Set₁ where
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
  honest-launch : (o : PureObs [] R) → HonMach (observe (⟦ o ⟧ []) root) [] [] (begin o)
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
  honest-step : ∀ {e qs xs m m′} → HonMach e qs xs m → step m ≡ silent m′ → HonMach e qs xs m′
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
  Onward e qs xs x = Σ Mach λ m′ → Σ (List Pos) λ qs₁ → Σ (List (Time × R)) λ xs′ → Σ (Reached e qs₁ xs′ m′) λ _ → Σ End λ en
                   → Σ (List Pos) λ qs′ → Stands m′ qs₁ en qs′ × read (qs ++ marks x) (xs ++ log x) (ending x) ≡ read qs′ xs′ en

  -- Read to tick `h`: a step past it cuts the record where it stands.
  mutual
    read-on : ∀ {e qs xs m} → Reached e qs xs m → ∀ h n c → Onward e qs xs (reading h n c (trace m))
    read-on {qs = qs} {xs} {m} r h zero    c = m , qs , xs , r , _ , _ , cutʰ , cong₂ (λ ms ls → read ms ls _) (++-identityʳ qs) (++-identityʳ xs)
    read-on {m = m}            r h (suc n) c = read-step r h n c (step m) refl

    read-step : ∀ {e qs xs m} → Reached e qs xs m → ∀ h n c s → step m ≡ s → Onward e qs xs (reading h (suc n) c (shown s))
    read-step {qs = qs} {xs} {m} r h n c (silent m₁) eq with h <ᵇ Mach.clock m₁
    ... | true  = m , qs , xs , r , _ , _ , cutʰ , cong₂ (λ ms ls → read ms ls _) (++-identityʳ qs) (++-identityʳ xs)
    ... | false = read-on (silentʰ r eq) h n _
    read-step {qs = qs} {xs} {m} r h n c (value t p a m₁) eq with h <ᵇ t
    ... | true  = m , qs , xs , r , _ , _ , cutʰ , cong₂ (λ ms ls → read ms ls _) (++-identityʳ qs) (++-identityʳ xs)
    ... | false with read-on (valueʰ r eq) h n t
    ...   | m′ , qs₁ , xs′ , r′ , en , qs′ , st , x = m′ , qs₁ , xs′ , r′ , en , qs′ , st ,
              trans (cong₂ (λ ms ls → read ms ls _) (sym (++-assoc qs [ p ] _)) (sym (++-assoc xs [ (t , a) ] _))) x
    read-step {qs = qs} {xs} {m} r h n c (complete p) eq = m , qs , xs , r , finished , _ , finʰ eq , cong (λ ls → read _ ls finished) (++-identityʳ xs)
    read-step {qs = qs} {xs} {m} r h n c drained      eq = m , qs , xs , r , dry , _ , dryʰ eq , cong₂ (λ ms ls → read ms ls dry) (++-identityʳ qs) (++-identityʳ xs)

  -- The launch's first n steps, read to tick h, are the record of a
  -- configuration reached from it.
  read-is-kept : (o : PureObs [] R) (n h : ℕ) → Σ Mach λ m′ → Σ (List Pos) λ qs₁ → Σ (List (Time × R)) λ xs′
               → Σ (Reached (observe (⟦ o ⟧ []) root) qs₁ xs′ m′) λ _ → Σ End λ en
               → Σ (List Pos) λ qs → Stands m′ qs₁ en qs × reading h n 0 (trace (begin o)) ≡ read qs xs′ en
  read-is-kept o n h = read-on (launchedʰ o refl) h n 0

  -- CONTENT: every prefix's record alike the meaning's events as a set.
  content : (o : PureObs [] R) (n h : ℕ) → let x = reading h n 0 (trace (begin o)) in Alike (ending x) (marks x) (log x) (observe (⟦ o ⟧ []) root)
  content o n h with read-is-kept o n h
  ... | m′ , qs₁ , xs′ , r′ , en , qs , st , eq rewrite eq = kept r′ st
