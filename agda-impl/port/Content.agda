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

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; [_]; length; head)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ʳ; ++⁻)
import Data.List.Relation.Unary.All as All
open All using (All; []; _∷_)
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.Linked as Linked
open Linked using (Linked)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Nat using (ℕ; zero; suc; _+_; _<ᵇ_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (suc-injective; +-suc; +-monoʳ-≤; n≤1+n; ≤-reflexive; n<1+n; <-trans)
open import Data.Maybe using (just; nothing)
import Data.Maybe.Relation.Unary.All as MAll
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList.Events using (Events; Pos; Time; tick; root; last; ix; Frame; at; done; quiet; emit; stall; close; _<ᵖ_; <ᵖ-tick)
  renaming (sub to subᴾ)
open import denotation.MonotonicList using (observe; Agree; agree-refl)
import denotation.Unfold as U
import Tree as T
open import denotation.Denote using (⟦_⟧)
open import operation.PureObservable using (PureObs; module Pure; module Driver; module Machine; tape; over)
open import port.Sorted using (_≤ᵖ_)
open import port.Sane using (Sane; sane-out)
open import port.Stepper.Within using (placed-after)
open import port.Placed.Order using (Placed)
open import port.Stepper.Past using (_≃_; Placedˢ)
open import port.Stepper using (step-skips)
open import port.Unsub using (module Unsubbing)
open import port.Ghost using (module Ghosting)
open import port.Strong using (module Strongly)
open import port.Sorted.Walk using (module SortingWalk)
open import port.Climbs using (module Ascending)
open import port.Moves using (module Moving)

module Honesty (R : Set) where
  open Driver R using (Mach; mach; depthOf; Timer; play; finish; cascade; Step; silent; value; complete; drained; step; trace; shown; reading; begin; Read; read; marks; log; ending; noted)
  open Pure R using (End; finished; dry; cutOff)
  open Unsubbing R using (_⇝_; now; then)
  open Ghosting R using (Has; Sent; sentHere; sentLater; Alike; _≋_; same-agree; residual; Reached; launchedʰ; silentʰ; valueʰ;
    Stands; cutʰ; finʰ; dryʰ; Mirror; Inner; Logged; Shows; silentˢ; valueˢ; completeˢ; drainedˢ; inner-launch; ≋-refl;
    Steps; after; steps-after; Hopped; onward; lowered; weight; loadOf; load; _≼_; _≺_; _⊏_)
  open Strongly R using (Strong; Carried; carried; closing; CtlAs; Meets; calmAs; noteAs; runAs; subAs; burstAs; popAs;
    Kernels; Owned; Meaning; Books; Path; ofˢ; seen; Sub; takeWhileˢ; part; Queue; BurstClocked; Each; Heads;
    Lingers; Untold; Ended; DoneBy; Begins; focused; attaching; coldˢ; waiting; fired; playing; Timed; Joined)
  open Ascending R using (Aloft; soar)
  open Moving R using (plant; planted; later)
  open SortingWalk R using (WellMach)
  open Machine using (Conf; Ctx; top; plug; downs; dirs; closed; doneS; cp; _⊕_; ⟨_,_,_,_,_⟩; absorbed; rising; resuming; subscribing; nx; pend;
    ofS; cutS; takeS; connS; joinS; next; att; owedCp; owedCut; feeding; attBody; owed; go;
    res; ofR; attR; cpR; cutR; feedR; bodyR; srcR; endR; joinR; idle; cut; Poke; gone; leaf; poke)

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

  private
    -- Whether a turn's leaf still runs.
    live : Poke R → Bool
    live gone             = false
    live (leaf b _ _ _ _) = b

  postulate
    -- The turn, nothing owed and no timer queued: the ghost shows
    -- nothing.
    turn-dry : ∀ {g m Γ A} {c : Ctx R Γ A} {s p} → Carried g m → Mach.conf m ≡ ⟨ c , s , absorbed , p , [] ⟩
             → Mach.turns m ≡ [] → Mach.timers m ≡ [] → ∀ {k b} → Has (residual g) k b → ⊥

    -- A value recorded is the least the ghost still holds.
    note-least : ∀ {g g′ m s a p rs} → Carried g m → Mach.conf m ≡ ⟨ top , s , rising (nx a) , p , rs ⟩
               → U.step g ≡ U.outˢ p a g′ → ∀ {q b} → Has (residual g′) q b → q ≤ᵖ p → ⊥

    -- A VALUE SHOWN, ABSORBED: what each subject owes its joiners, and
    -- the machine's order, read alike at rest.
    meaning-note : ∀ {t Γ A} {c : Ctx R Γ A} {s a p rs} → Kernels t ⟨ c , s , rising (nx a) , p , rs ⟩
                 → Meaning t ⟨ c , s , rising (nx a) , p , rs ⟩ → Meaning t ⟨ c , s , absorbed , p , rs ⟩
    sorted-note : ∀ {lo m Γ A} {c : Ctx R Γ A} {s a p rs} → WellMach lo m
                → Mach.conf m ≡ ⟨ c , s , rising (nx a) , p , rs ⟩
                → WellMach lo (record m { conf = ⟨ c , s , absorbed , p , rs ⟩ })

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

    -- The takeWhile a job resumes is the witness's at the job's path.
    take-path : ∀ {g m Γ A} {c : Ctx R Γ A} {i q s τ p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , takeS i q s , resuming τ , p , rs ⟩
              → Σ _ λ tk → Σ (Sub Γ A) λ u → Path (Carried.tree cr) (takeWhileˢ i q tk u) (dirs c)

    -- A takeWhile's completion the ghost does not hold: it climbs unseen.
    take1-void : ∀ {g m Γ A} {c : Ctx R Γ A} {i q s p rs tk u} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , takeS i q s , resuming owedCp , p , rs ⟩
               → (ψ : Path (Carried.tree cr) (takeWhileˢ {Γ} {A} i q tk u) (dirs c)) → seen ψ ≡ false
               → Hopped (carried cr) (record m { conf = ⟨ c , takeS i q s , rising cp , p ⊕ [ last ] , (dirs c , owedCut , p) ∷ rs ⟩ })

    -- A takeWhile's completion the ghost holds: on its way up.
    take1-enter : ∀ {g m Γ A} {c : Ctx R Γ A} {i q s p rs tk u} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , takeS i q s , resuming owedCp , p , rs ⟩
                → (ψ : Path (Carried.tree cr) (takeWhileˢ {Γ} {A} i q tk u) (dirs c)) → seen ψ ≡ true
                → Σ Mach λ m₁ → record m { conf = ⟨ c , takeS i q s , rising cp , p ⊕ [ last ] , (dirs c , owedCut , p) ∷ rs ⟩ } ⇝ m₁
                  × Aloft g (loadOf (carried cr)) m₁

    -- A TAKEWHILE'S CUT, ON THE WITNESS: the tree with that node torn,
    -- read alike by the ghost (`part`), and every column kept.
    --
    -- RECOVERY: git show b039ebbb restores `port/Frame`, `port/Retag` and `port/Retag/Shut`, the old shut lemmas over the denotation's nodes (`untold-apart`, `shut-down`, `tells`), untypechecked
    cut-torn : ∀ {g m Γ A} {c : Ctx R Γ A} {i q s p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , takeS i q s , resuming owedCut , p , rs ⟩
             → Σ (Sub [] R) λ t′ → Kernels t′ ⟨ c , takeS i q (proj₁ (cut s)) , absorbed , p , rs ⟩ × part t′ ≡ part (Carried.tree cr)
    cut-owned : ∀ {g m Γ A} {c : Ctx R Γ A} {i q s p rs} (cr : Carried g m) (e : Mach.conf m ≡ ⟨ c , takeS i q s , resuming owedCut , p , rs ⟩)
              → Owned (proj₁ (cut-torn cr e)) (record m { conf = ⟨ c , takeS i q (proj₁ (cut s)) , absorbed , p , rs ⟩ })
    cut-meaning : ∀ {g m Γ A} {c : Ctx R Γ A} {i q s p rs} (cr : Carried g m) (e : Mach.conf m ≡ ⟨ c , takeS i q s , resuming owedCut , p , rs ⟩)
                → Meaning (proj₁ (cut-torn cr e)) ⟨ c , takeS i q (proj₁ (cut s)) , absorbed , p , rs ⟩
    cut-queue : ∀ {g m Γ A} {c : Ctx R Γ A} {i q s p rs} (cr : Carried g m) (e : Mach.conf m ≡ ⟨ c , takeS i q s , resuming owedCut , p , rs ⟩)
              → Queue p (Mach.clock m) (Mach.timers m) (proj₁ (cut-torn cr e))
    cut-turned : ∀ {g m Γ A} {c : Ctx R Γ A} {i q s p rs} (cr : Carried g m) (e : Mach.conf m ≡ ⟨ c , takeS i q s , resuming owedCut , p , rs ⟩)
               → All (BurstClocked (proj₁ (cut-torn cr e)) (Mach.clock m)) (Mach.turns m)
    cut-sorted : ∀ {lo m Γ A} {c : Ctx R Γ A} {i q s p rs} → WellMach lo m → Mach.conf m ≡ ⟨ c , takeS i q s , resuming owedCut , p , rs ⟩
               → WellMach lo (record m { conf = ⟨ c , takeS i q (proj₁ (cut s)) , absorbed , p , rs ⟩ })
    cut-behind : ∀ {g m Γ A} {c : Ctx R Γ A} {i q s p rs} (cr : Carried g m) (e : Mach.conf m ≡ ⟨ c , takeS i q s , resuming owedCut , p , rs ⟩)
               → Each (Heads p) (proj₁ (cut-torn cr e))
    cut-lingers : ∀ {g m Γ A} {c : Ctx R Γ A} {i q s p rs} (cr : Carried g m) (e : Mach.conf m ≡ ⟨ c , takeS i q s , resuming owedCut , p , rs ⟩)
                → Lingers (proj₁ (cut-torn cr e))
    cut-told : ∀ {g m Γ A} {c : Ctx R Γ A} {i q s p rs} (cr : Carried g m) (e : Mach.conf m ≡ ⟨ c , takeS i q s , resuming owedCut , p , rs ⟩)
             → Untold p (proj₁ (cut-torn cr e))
    cut-ended : ∀ {g m Γ A} {c : Ctx R Γ A} {i q s p rs} (cr : Carried g m) (e : Mach.conf m ≡ ⟨ c , takeS i q s , resuming owedCut , p , rs ⟩)
              → Ended (proj₁ (cut-torn cr e))
    cut-flags : ∀ {g m Γ A} {c : Ctx R Γ A} {i q s p rs} (cr : Carried g m) (e : Mach.conf m ≡ ⟨ c , takeS i q s , resuming owedCut , p , rs ⟩)
              → DoneBy (proj₁ (cut-torn cr e)) []
    -- Tearing frees what it reaches: the load never rises.
    cut-load : ∀ {g m Γ A} {c : Ctx R Γ A} {i q s p rs} (cr : Carried g m) (e : Mach.conf m ≡ ⟨ c , takeS i q s , resuming owedCut , p , rs ⟩)
             → load (record m { conf = ⟨ c , takeS i q (proj₁ (cut s)) , absorbed , p , rs ⟩ }) (proj₁ (cut-torn cr e)) ≼ loadOf (carried cr)

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

    -- A SUBSCRIPTION BEGUN, BY ITS PROGRAM: a cold started, an `of` or
    -- `empty` set running, an operator's source pending below it, a
    -- joiner joined, a defer's body pending.  The ghost alike.
    sub-cold    : ∀ {g m Γ A} {c : Ctx R Γ A} {x p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , pend (T.cold x) , subscribing , p , rs ⟩
                → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′
    sub-empty   : ∀ {g m Γ A} {c : Ctx R Γ A} {p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , pend T.empty , subscribing , p , rs ⟩
                → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′
    sub-of      : ∀ {g m Γ A} {c : Ctx R Γ A} {xs p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , pend (T.of xs) , subscribing , p , rs ⟩
                → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′
    sub-map     : ∀ {g m Γ A X} {c : Ctx R Γ A} {f : X → A} {o p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , pend (T.map f o) , subscribing , p , rs ⟩
                → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′
    sub-scan    : ∀ {g m Γ A X} {c : Ctx R Γ A} {f : A → X → A} {z o p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , pend (T.scan f z o) , subscribing , p , rs ⟩
                → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′
    sub-take    : ∀ {g m Γ A} {c : Ctx R Γ A} {i q o p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , pend (T.takeWhile i q o) , subscribing , p , rs ⟩
                → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′
    sub-flat    : ∀ {g m Γ A X} {c : Ctx R Γ A} {op} {f : X → _} {o p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , pend (T.flatMap op f o) , subscribing , p , rs ⟩
                → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′
    sub-connect : ∀ {g m Γ A X} {c : Ctx R Γ A} {o : T.Obs _ Γ X} {b p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , pend (T.connect o b) , subscribing , p , rs ⟩
                → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′
    sub-joined  : ∀ {g m Γ A} {c : Ctx R Γ A} {x p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , pend (T.connected x) , subscribing , p , rs ⟩
                → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′
    sub-defer   : ∀ {g m Γ A} {c : Ctx R Γ A} {l p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , pend (T.defer l) , subscribing , p , rs ⟩
                → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′

    -- A spent burst dropped, the stack resumed: the turn over nothing.
    -- The ghost alike, a turn fewer.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Climbs/Base.agda
    burst-spent : ∀ {g m Γ A} {c : Ctx R Γ A} {s p rs π u i pl d ts} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , s , absorbed , p , rs ⟩
                → Mach.turns m ≡ play π u i pl d ∷ ts → (d <ᵇ length rs) ≡ false → live (poke π (Mach.conf m)) ≡ false
                → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′

    -- A live burst's sink polled: open, the frame to play; closed, the
    -- burst dropped and the stack resumed.
    burst-poll : ∀ {g m Γ A} {c : Ctx R Γ A} {s p rs π u i d ts} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , s , absorbed , p , rs ⟩
               → Mach.turns m ≡ play π u i false d ∷ ts → (d <ᵇ length rs) ≡ false → live (poke π (Mach.conf m)) ≡ true
               → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′

    -- A polled burst's frame played: a value delivered and run to the
    -- next re-entry state, a stall's skip passed, or a close scheduling
    -- the rest.
    burst-play : ∀ {g m Γ A} {c : Ctx R Γ A} {s p rs π u i d ts} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , s , absorbed , p , rs ⟩
               → Mach.turns m ≡ play π u i true d ∷ ts → (d <ᵇ length rs) ≡ false → live (poke π (Mach.conf m)) ≡ true
               → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′

    -- A cold's completion owed at the turn: delivered under its
    -- position, the leaf spent.
    burst-finish : ∀ {g m Γ A} {c : Ctx R Γ A} {s p rs π e d ts} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , s , absorbed , p , rs ⟩
                 → Mach.turns m ≡ finish π e d ∷ ts → (d <ᵇ length rs) ≡ false
                 → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′

    -- A job owed above the next turn popped and resumed, likewise.
    -- A JOB POPPED: its path leads from the root to where it was
    -- suspended, and resuming it there keeps what is owed; a path leading
    -- nowhere drops it.
    downs-plug : ∀ {q x Γ A} {c′ : Ctx R Γ A} {s′} → downs q top x ≡ just (Γ , A , c′ , s′) → plug c′ s′ ≡ x
    owned-popped : ∀ {t m Γ A Γ′ A′} {c : Ctx R Γ A} {s p q τ p′ rs} {c′ : Ctx R Γ′ A′} {s′}
              → Kernels t (Mach.conf m) → Owned t m → Mach.conf m ≡ ⟨ c , s , absorbed , p , (q , τ , p′) ∷ rs ⟩
              → downs q top (plug c s) ≡ just (_ , _ , c′ , s′)
              → Owned t (record m { conf = ⟨ c′ , s′ , resuming τ , p′ , rs ⟩ })
    meaning-pop : ∀ {t Γ A Γ′ A′} {c : Ctx R Γ A} {s p q τ p′ rs} {c′ : Ctx R Γ′ A′} {s′}
                → Kernels t ⟨ c , s , absorbed , p , (q , τ , p′) ∷ rs ⟩ → Meaning t ⟨ c , s , absorbed , p , (q , τ , p′) ∷ rs ⟩
                → downs q top (plug c s) ≡ just (_ , _ , c′ , s′) → Meaning t ⟨ c′ , s′ , resuming τ , p′ , rs ⟩
    sorted-pop : ∀ {lo m Γ A Γ′ A′} {c : Ctx R Γ A} {s p q τ p′ rs} {c′ : Ctx R Γ′ A′} {s′} → WellMach lo m
               → Mach.conf m ≡ ⟨ c , s , absorbed , p , (q , τ , p′) ∷ rs ⟩ → downs q top (plug c s) ≡ just (_ , _ , c′ , s′)
               → WellMach lo (record m { conf = ⟨ c′ , s′ , resuming τ , p′ , rs ⟩ })
    owned-dropped : ∀ {t m Γ A} {c : Ctx R Γ A} {s p j rs} → Kernels t (Mach.conf m) → Owned t m
               → Mach.conf m ≡ ⟨ c , s , absorbed , p , j ∷ rs ⟩ → downs (proj₁ j) top (plug c s) ≡ nothing
               → Owned t (record m { conf = ⟨ c , s , absorbed , p , rs ⟩ })
    meaning-drop : ∀ {t Γ A} {c : Ctx R Γ A} {s p j rs} → Kernels t ⟨ c , s , absorbed , p , j ∷ rs ⟩
                 → Meaning t ⟨ c , s , absorbed , p , j ∷ rs ⟩ → downs (proj₁ j) top (plug c s) ≡ nothing
                 → Meaning t ⟨ c , s , absorbed , p , rs ⟩
    sorted-drop : ∀ {lo m Γ A} {c : Ctx R Γ A} {s p j rs} → WellMach lo m
                → Mach.conf m ≡ ⟨ c , s , absorbed , p , j ∷ rs ⟩ → downs (proj₁ j) top (plug c s) ≡ nothing
                → WellMach lo (record m { conf = ⟨ c , s , absorbed , p , rs ⟩ })

    -- A TIMER FIRED, ON THE WITNESS: its cold's phase fired, which the
    -- machine's tree does not read, the ghost alike, every column kept
    -- with the timer gone and its turn held.
    fire-kernels : ∀ {t k Γ A w τ e u x b π} {fr : Frame A u} (ψ : Path t (coldˢ {Γ} {A} b (waiting {u = w} τ e (at u x fr))) π)
                 → Kernels t k → Kernels (plant ψ (coldˢ b (fired τ e (at u x fr)))) k
    fire-part : ∀ {t : Sub [] R} {Γ A w τ e u x b π} {fr : Frame A u} (ψ : Path t (coldˢ {Γ} {A} b (waiting {u = w} τ e (at u x fr))) π)
              → part (plant ψ (coldˢ b (fired τ e (at u x fr)))) ≡ part t
    fire-load : ∀ {g m Γ A w τ e u x b π tm tms} {fr : Frame A u} (cr : Carried g m) → Mach.timers m ≡ tm ∷ tms
              → (ψ : Path (Carried.tree cr) (coldˢ {Γ} {A} b (waiting {u = w} τ e (at u x fr))) π)
              → load (record m { clock = Timer.due tm ; timers = tms ; turns = [ play π (cascade tm) 0 false 0 ] })
                     (plant ψ (coldˢ b (fired τ e (at u x fr)))) ⊏ loadOf (carried cr)
    fire-owned : ∀ {g m Γ A w τ e u x b π tm tms} {fr : Frame A u} (cr : Carried g m) → Mach.timers m ≡ tm ∷ tms
               → (ψ : Path (Carried.tree cr) (coldˢ {Γ} {A} b (waiting {u = w} τ e (at u x fr))) π)
               → Owned (plant ψ (coldˢ b (fired τ e (at u x fr)))) (record m { clock = Timer.due tm ; timers = tms ; turns = [ play π (cascade tm) 0 false 0 ] })
    fire-meaning : ∀ {t k Γ A w τ e u x b π} {fr : Frame A u} (ψ : Path t (coldˢ {Γ} {A} b (waiting {u = w} τ e (at u x fr))) π)
                 → Meaning t k → Meaning (plant ψ (coldˢ b (fired τ e (at u x fr)))) k
    fire-timed : ∀ {t Γ A w τ e u x b π tm tms} {fr : Frame A u} (ψ : Path t (coldˢ {Γ} {A} b (waiting {u = w} τ e (at u x fr))) π)
               → All (Timed t) (tm ∷ tms) → Timer.path tm ≡ π → All (Timed (plant ψ (coldˢ b (fired τ e (at u x fr))))) tms
    fire-joined : ∀ {t Γ A w τ e u x b π} {fr : Frame A u} (ψ : Path t (coldˢ {Γ} {A} b (waiting {u = w} τ e (at u x fr))) π)
                → Joined t → Joined (plant ψ (coldˢ b (fired τ e (at u x fr))))
    fire-sorted : ∀ {lo m tm tms} → WellMach lo m → Mach.turns m ≡ [] → Mach.timers m ≡ tm ∷ tms
                → WellMach lo (record m { clock = Timer.due tm ; timers = tms ; turns = [ play (Timer.path tm) (cascade tm) 0 false 0 ] })
    fire-flags : ∀ {t Γ A w τ e u x b π} {fr : Frame A u} (ψ : Path t (coldˢ {Γ} {A} b (waiting {u = w} τ e (at u x fr))) π)
               → DoneBy t [] → DoneBy (plant ψ (coldˢ b (fired τ e (at u x fr)))) []
    fire-told : ∀ {g m Γ A w τ e u x b π} {fr : Frame A u} (cr : Carried g m)
                (ψ : Path (Carried.tree cr) (coldˢ {Γ} {A} b (waiting {u = w} τ e (at u x fr))) π)
              → Untold (Conf.pos (Mach.conf m)) (plant ψ (coldˢ b (fired τ e (at u x fr))))
    fire-ended : ∀ {g m Γ A w τ e u x b π} {fr : Frame A u} (cr : Carried g m)
                 (ψ : Path (Carried.tree cr) (coldˢ {Γ} {A} b (waiting {u = w} τ e (at u x fr))) π)
               → Ended (plant ψ (coldˢ b (fired τ e (at u x fr))))

    -- A live timer popped at the turn: its cold, fired, heads past where
    -- the run is.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Lift.agda
    behind-fire : ∀ {g m Γ A w τ e u x b π} {fr : Frame A u} (cr : Carried g m)
                  (ψ : Path (Carried.tree cr) (coldˢ {Γ} {A} b (waiting {u = w} τ e (at u x fr))) π)
                → Each (Heads (Conf.pos (Mach.conf m))) (plant ψ (coldˢ b (fired τ e (at u x fr))))

    -- A timer fired leaves every tie held: a cold runs nothing past its end.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Lift.agda
    fire-lingers : ∀ {g m Γ A w τ e u x b π} {fr : Frame A u} (cr : Carried g m)
                   (ψ : Path (Carried.tree cr) (coldˢ {Γ} {A} b (waiting {u = w} τ e (at u x fr))) π)
                 → Lingers (plant ψ (coldˢ b (fired τ e (at u x fr))))

  -- An absorbed configuration is a re-entry state: calm, a turn to play,
  -- or a job to pop.
  private
    -- The job's turn or the turn's, as the turn's depth decides.
    picked : ∀ {Γ A} {c : Ctx R Γ A} {s p j rs clk tms t ts} (b : Bool) → (depthOf t <ᵇ suc (length rs)) ≡ b
           → CtlAs (mach ⟨ c , s , absorbed , p , j ∷ rs ⟩ clk tms (t ∷ ts))
    picked true  d = popAs refl (MAll.just d)
    picked false d = burstAs refl refl d

    settled : ∀ {Γ A} {c : Ctx R Γ A} {s p} rs clk tms ts → CtlAs (mach ⟨ c , s , absorbed , p , rs ⟩ clk tms ts)
    settled []       clk tms []       = calmAs refl refl
    settled []       clk tms (t ∷ ts) = burstAs refl refl refl
    settled (j ∷ rs) clk tms []       = popAs refl MAll.nothing
    settled (j ∷ rs) clk tms (t ∷ ts) = picked _ refl

    settled-meets : ∀ {Γ A} {c : Ctx R Γ A} {s p} rs clk tms ts {n g} → n ≡ just g → Meets (settled {c = c} {s} {p} rs clk tms ts) n g
    settled-meets []       clk tms []       e = e
    settled-meets []       clk tms (t ∷ ts) e = e
    settled-meets (j ∷ rs) clk tms []       e = e
    settled-meets (j ∷ rs) clk tms (t ∷ ts) e = picked-meets _ refl e
      where picked-meets : ∀ {Γ A} {c : Ctx R Γ A} {s p n g} b (d : (depthOf t <ᵇ suc (length rs)) ≡ b) → n ≡ just g
                         → Meets (picked {c = c} {s} {p} {j} {rs} {clk} {tms} {t} {ts} b d) n g
            picked-meets true  d e = e
            picked-meets false d e = e

    -- Settling a job's run weighs less than running it.
    settled-lighter : ∀ {Γ A} {c : Ctx R Γ A} {s p} rs clk tms ts
                    → weight (settled {c = c} {s} {p} rs clk tms ts) < suc (length rs) + suc (length rs)
    settled-lighter []       clk tms []       = s≤s z≤n
    settled-lighter []       clk tms (t ∷ ts) = s≤s z≤n
    settled-lighter (j ∷ rs) clk tms []       = popped (suc (length rs))
      where popped : ∀ a → suc (suc (a + a)) ≤ suc a + suc a
            popped a = s≤s (≤-reflexive (sym (+-suc a a)))
    settled-lighter (j ∷ rs) clk tms (t ∷ ts) = picked-lighter _ refl
      where picked-lighter : ∀ {Γ A} {c : Ctx R Γ A} {s p} b (d : (depthOf t <ᵇ suc (length rs)) ≡ b)
                           → weight (picked {c = c} {s} {p} {j} {rs} {clk} {tms} {t} {ts} b d) < suc (length (j ∷ rs)) + suc (length (j ∷ rs))
            picked-lighter true  d = s≤s (s≤s (≤-reflexive (sym (+-suc (length rs) (suc (length rs))))))
            picked-lighter false d = s≤s (+-monoʳ-≤ (suc (length rs)) (n≤1+n (suc (length rs))))

    -- At rest, a shown value's jobs are the same jobs.
    owned-note : ∀ {t s a p rs clk tms ts} → Owned t (mach ⟨ top , s , rising (nx a) , p , rs ⟩ clk tms ts)
               → Owned t (mach ⟨ top , s , absorbed , p , rs ⟩ clk tms ts)
    owned-note {s = s} {a} {p} {rs} o = record
      { ofs = Owned.ofs o ; begun = λ ψ → rebegin (Owned.begun o ψ) ; attached = Owned.attached o ; ends = Owned.ends o
      ; cuts = Owned.cuts o ; feeds = Owned.feeds o ; bodies = Owned.bodies o ; sources = Owned.sources o ; owes = Owned.owes o }
      where rebegin : ∀ {π q} → Begins ⟨ top , s , rising (nx a) , p , rs ⟩ π q → Begins ⟨ top , s , absorbed , p , rs ⟩ π q
            rebegin (focused _ () _)
            rebegin (attaching ρ p′ e j e′) = attaching ρ p′ e j e′

  -- Past a value shown, the configuration runs the stepped ghost: at
  -- rest, on the agenda.
  note-onward : ∀ {g g′ m s a p rs} → Carried g m → Mach.conf m ≡ ⟨ top , s , rising (nx a) , p , rs ⟩
              → U.step g ≡ U.outˢ p a g′ → Mirror g′ (record m { conf = ⟨ top , s , absorbed , p , rs ⟩ })
  note-onward {g} {m = mach _ clk tms ts} {s} {p = p} {rs} cr refl stp with Carried.ctlAs cr | Carried.meets cr
  ... | calmAs () _    | _
  ... | runAs ()       | _
  ... | subAs ()       | _
  ... | burstAs () _ _ | _
  ... | popAs () _     | _
  ... | noteAs refl ck | g″ , pe , st″ with trans (sym st″) stp
  ...   | refl = m′ , now , carried (record
          { sane = sane-out {g = g} (Carried.sane cr) stp
          ; placed = proj₂ (subst (Placedˢ []) stp (placed-after g (Carried.sane cr) (Carried.placed cr)))
          ; tree = Carried.tree cr ; kernels = Carried.kernels cr
          ; ctlAs = settled rs clk tms ts ; meets = settled-meets rs clk tms ts pe
          ; owned = owned-note (Carried.owned cr) ; meaning = meaning-note (Carried.kernels cr) (Carried.meaning cr)
          ; queue = Carried.queue cr
          ; books = record { clocked = tt ; ticked = Books.ticked (Carried.books cr) ; turned = Books.turned (Carried.books cr) }
          ; sorted = proj₁ (Carried.sorted cr) , sorted-note (proj₂ (Carried.sorted cr)) refl
          ; behind = Carried.behind cr ; lingers = Carried.lingers cr ; told = Carried.told cr
          ; ended = Carried.ended cr ; flags = Carried.flags cr })
    where m′ = mach ⟨ top , s , absorbed , p , rs ⟩ clk tms ts

  -- The queue's head popped: the rest due no earlier than it.
  ahead-pop : ∀ {p : Pos} {clk} {tm : Timer} {ts}
            → Linked (λ x y → cascade x <ᵖ cascade y ≡ true) (tm ∷ ts)
            → All (λ x → clk ≤ Timer.due x × p <ᵖ cascade x ≡ true) (tm ∷ ts)
            → All (λ x → Timer.due tm ≤ Timer.due x × p <ᵖ cascade x ≡ true) ts
  ahead-pop {p = p} {tm = tm} lk (_ ∷ ah) = ahead-go (later lk) ah
    where
      ahead-go : ∀ {clk xs} → All (λ x → cascade tm <ᵖ cascade x ≡ true) xs → All (λ x → clk ≤ Timer.due x × p <ᵖ cascade x ≡ true) xs
         → All (λ x → Timer.due tm ≤ Timer.due x × p <ᵖ cascade x ≡ true) xs
      ahead-go []       []             = []
      ahead-go {xs = x ∷ _} (c ∷ cs) ((_ , a) ∷ as) = (<ᵖ-tick (Timer.due tm) (Timer.due x) (subᴾ (Timer.from tm) ∷ []) (subᴾ (Timer.from x) ∷ []) c , a) ∷ ahead-go cs as

  -- THE TURN POPPING A TIMER: its cold fired, the same meaning node with
  -- its burst held, a timer fewer.
  turn-pops : ∀ {g m Γ A} {c : Ctx R Γ A} {s p tm tms} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , s , absorbed , p , [] ⟩
            → Mach.turns m ≡ [] → Mach.timers m ≡ tm ∷ tms → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′
  turn-pops {g} {mach _ clk (tm ∷ tms) []} {c = c} {s} {p} cr refl refl refl refl
    with Carried.ctlAs cr | Carried.meets cr | All.head (Queue.timed (Carried.queue cr))
  ... | calmAs refl refl | mt | _ , _ , waiting τ e (at u x fr) , b , ψ , dd , _ =
    g , m′ , now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = plant ψ v
        ; kernels = fire-kernels {t = Carried.tree cr} {k = ⟨ c , s , absorbed , p , [] ⟩} ψ (Carried.kernels cr)
        ; ctlAs = burstAs refl refl refl ; meets = trans (fire-part {t = Carried.tree cr} ψ) mt
        ; owned = fire-owned cr refl ψ ; meaning = fire-meaning ψ (Carried.meaning cr)
        ; queue = record { timed = fire-timed ψ (Queue.timed q) refl ; joined = fire-joined ψ (Queue.joined q)
                         ; ordered = Linked.tail (Queue.ordered q) ; ahead = ahead-pop {p = p} (Queue.ordered q) (Queue.ahead q) }
        ; books = record { clocked = tt ; ticked = [] ; turned = (refl , _ , _ , _ , b , planted ψ v , dd) ∷ [] }
        ; sorted = proj₁ (Carried.sorted cr) , fire-sorted (proj₂ (Carried.sorted cr)) refl refl
        ; behind = behind-fire cr ψ ; lingers = fire-lingers cr ψ ; told = fire-told cr ψ
        ; ended = fire-ended cr ψ ; flags = fire-flags ψ (Carried.flags cr) })
    , lowered (λ n → agree-refl n _) (inj₁ (fire-load cr refl ψ))
    where q = Carried.queue cr
          v = coldˢ b (fired τ e (at u x fr))
          m′ = mach ⟨ c , s , absorbed , p , [] ⟩ (Timer.due tm) tms [ play (Timer.path tm) (cascade tm) 0 false 0 ]
  ... | calmAs refl refl | _ | _ , _ , waiting _ _ done  , _ , _ , ()
  ... | calmAs refl refl | _ | _ , _ , waiting _ _ quiet , _ , _ , ()
  ... | calmAs refl refl | _ | _ , _ , fired _ _ _       , _ , _ , ()
  ... | calmAs refl refl | _ | _ , _ , playing _ _ _ _   , _ , _ , ()
  ... | noteAs () _    | _ | _
  ... | runAs ()       | _ | _
  ... | subAs ()       | _ | _
  ... | burstAs _ () _ | _ | _
  ... | popAs () _     | _ | _

  private
    -- A turn played is silent, whatever the leaf.
    playing-silent : ∀ m π u i pl d ts pk → Σ Mach λ m′ → Driver.playing R m π u i pl d ts pk ≡ silent m′
    playing-silent m π u i pl    d ts gone                                       = _ , refl
    playing-silent m π u i pl    d ts (leaf false l cl dv st)                    = _ , refl
    playing-silent m π u i false d ts (leaf true l true dv st)                   = _ , refl
    playing-silent m π u i false d ts (leaf true l false dv st)                  = _ , refl
    playing-silent m π u i true  d ts (leaf true (tape t (emit a k)) cl dv st)   = _ , refl
    playing-silent m π u i true  d ts (leaf true (tape t (stall k)) cl dv st)    = _ , refl
    playing-silent m π u i true  d ts (leaf true (tape t (close k)) cl dv st)    = _ , refl
    playing-silent m π u i true  d ts (leaf true over cl dv st)                  = _ , refl

    finishing-silent : ∀ m e ts pk → Σ Mach λ m′ → Driver.finishing R m e ts pk ≡ silent m′
    finishing-silent m e ts gone              = _ , refl
    finishing-silent m e ts (leaf b l cl dv st) = _ , refl

    -- Nothing owed above it: the turn is played.
    burst-step : ∀ {Γ A} {c : Ctx R Γ A} {s p rs clk tms t ts} → (depthOf t <ᵇ length rs) ≡ false
               → step (mach ⟨ c , s , absorbed , p , rs ⟩ clk tms (t ∷ ts)) ≡ Driver.played R (mach ⟨ c , s , absorbed , p , rs ⟩ clk tms (t ∷ ts)) t ts
    burst-step d rewrite d = refl

  -- A turn played: spent, dropped; live and unpolled, polled; polled,
  -- its frame played; a completion owed, delivered.
  burst-onward : ∀ {g m Γ A} {c : Ctx R Γ A} {s p rs t ts} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , s , absorbed , p , rs ⟩
               → Mach.turns m ≡ t ∷ ts → (depthOf t <ᵇ length rs) ≡ false
               → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′
  burst-onward {m = mach k clk tms (play π u i pl d ∷ ts)} {c = c} {s} {p} {rs} cr refl refl dl
    with playing-silent (mach k clk tms (play π u i pl d ∷ ts)) π u i pl d ts (poke π k)
  ... | m′ , ps with live (poke π k) in lv | pl
  ...   | false | _     = m′ , trans (burst-step {c = c} {s} {p} {rs} {clk} {tms} {_} {ts} dl) ps , burst-spent cr refl refl dl lv (trans (burst-step {c = c} {s} {p} {rs} {clk} {tms} {_} {ts} dl) ps)
  ...   | true  | false = m′ , trans (burst-step {c = c} {s} {p} {rs} {clk} {tms} {_} {ts} dl) ps , burst-poll cr refl refl dl lv (trans (burst-step {c = c} {s} {p} {rs} {clk} {tms} {_} {ts} dl) ps)
  ...   | true  | true  = m′ , trans (burst-step {c = c} {s} {p} {rs} {clk} {tms} {_} {ts} dl) ps , burst-play cr refl refl dl lv (trans (burst-step {c = c} {s} {p} {rs} {clk} {tms} {_} {ts} dl) ps)
  burst-onward {m = mach k clk tms (finish π e d ∷ ts)} {c = c} {s} {p} {rs} cr refl refl dl
    with finishing-silent (mach k clk tms (finish π e d ∷ ts)) e ts (poke π k)
  ... | m′ , fs = m′ , trans (burst-step {c = c} {s} {p} {rs} {clk} {tms} {_} {ts} dl) fs , burst-finish cr refl refl dl (trans (burst-step {c = c} {s} {p} {rs} {clk} {tms} {_} {ts} dl) fs)

  private
    -- A joiner's subscription is silent, joined or completed.
    joined-silent : ∀ {Γ A} {c : Ctx R Γ A} {x p rs clk tms ts}
                  → Σ Mach λ m′ → step (mach ⟨ c , pend (T.connected x) , subscribing , p , rs ⟩ clk tms ts) ≡ silent m′
    joined-silent {c = c} {x} {p} with Machine.joinUp p c x []
    ... | true  , _ = _ , refl
    ... | false , _ = _ , refl

  -- A subscription begun, by its program.
  sub-onward : ∀ {g m Γ A} {c : Ctx R Γ A} {o p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , pend o , subscribing , p , rs ⟩
             → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′
  sub-onward {m = mach _ _ _ _} {o = T.cold _}          cr refl = _ , refl , sub-cold cr refl refl
  sub-onward {m = mach _ _ _ _} {o = T.empty}           cr refl = _ , refl , sub-empty cr refl refl
  sub-onward {m = mach _ _ _ _} {o = T.of _}            cr refl = _ , refl , sub-of cr refl refl
  sub-onward {m = mach _ _ _ _} {o = T.map _ _}         cr refl = _ , refl , sub-map cr refl refl
  sub-onward {m = mach _ _ _ _} {o = T.scan _ _ _}      cr refl = _ , refl , sub-scan cr refl refl
  sub-onward {m = mach _ _ _ _} {o = T.takeWhile _ _ _} cr refl = _ , refl , sub-take cr refl refl
  sub-onward {m = mach _ _ _ _} {o = T.flatMap _ _ _}   cr refl = _ , refl , sub-flat cr refl refl
  sub-onward {m = mach _ _ _ _} {o = T.connect _ _}     cr refl = _ , refl , sub-connect cr refl refl
  sub-onward {m = mach _ _ _ _} {o = T.defer _}         cr refl = _ , refl , sub-defer cr refl refl
  sub-onward {m = mach _ _ _ _} {o = T.connected _}     cr refl with joined-silent
  ... | m′ , js = m′ , js , sub-joined cr refl js

  private
    -- A job owed nothing by its node: dropped, the ghost alike, the
    -- control lighter.
    idle-onward : ∀ {g m Γ A} {c : Ctx R Γ A} {s t p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , s , resuming t , p , rs ⟩
                → res s t ≡ idle → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′
    idle-onward {g} {mach _ clk tms ts} {c = c} {s} {t} {p} {rs} cr refl r with Carried.ctlAs cr in eqc | Carried.meets cr
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
      , lowered (λ n → agree-refl n _) (inj₂ (refl , subst (weight (settled rs clk tms ts) <_) (cong weight (sym eqc)) (settled-lighter rs clk tms ts)))
      where m′ = mach ⟨ c , s , absorbed , p , rs ⟩ clk tms ts
    ... | calmAs () _  | _
    ... | noteAs () _  | _
    ... | subAs ()     | _
    ... | burstAs () _ _ | _
    ... | popAs () _   | _

  private
    -- A pop is the configuration's own step: the turns wait.
    pop-step : ∀ {m Γ A} {c : Ctx R Γ A} {s p j rs} → Mach.conf m ≡ ⟨ c , s , absorbed , p , j ∷ rs ⟩
             → MAll.All (λ t → (depthOf t <ᵇ suc (length rs)) ≡ true) (head (Mach.turns m)) → step m ≡ Driver.took R m (Machine.step (Mach.conf m))
    pop-step {mach _ _ _ []} refl _ = refl
    pop-step {mach _ _ _ (t ∷ ts)} {rs = rs} refl (MAll.just ps) with depthOf t <ᵇ suc (length rs) | ps
    ... | true | refl = refl

    popping : ∀ {Γ A Γ′ A′} {c : Ctx R Γ A} {s p q τ p′ rs} {c′ : Ctx R Γ′ A′} {s′}
            → downs q top (plug c s) ≡ just (_ , _ , c′ , s′)
            → Machine.step ⟨ c , s , absorbed , p , (q , τ , p′) ∷ rs ⟩ ≡ Machine.moved ⟨ c′ , s′ , resuming τ , p′ , rs ⟩ [] []
    popping d rewrite d = refl

    dropping : ∀ {Γ A} {c : Ctx R Γ A} {s p q τ p′ rs} → downs q top (plug c s) ≡ nothing
             → Machine.step ⟨ c , s , absorbed , p , (q , τ , p′) ∷ rs ⟩ ≡ Machine.moved ⟨ c , s , absorbed , p , rs ⟩ [] []
    dropping d rewrite d = refl

  -- A job resumed runs at the position it was suspended at, the carrier's
  -- position-read parts read there.
  postulate
    pop-queue  : ∀ {g m Γ A} {c : Ctx R Γ A} {s p q τ p′ rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , s , absorbed , p , (q , τ , p′) ∷ rs ⟩
               → Queue p′ (Mach.clock m) (Mach.timers m) (Carried.tree cr)
    pop-behind : ∀ {g m Γ A} {c : Ctx R Γ A} {s p q τ p′ rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , s , absorbed , p , (q , τ , p′) ∷ rs ⟩
               → Each (Heads p′) (Carried.tree cr)
    pop-told   : ∀ {g m Γ A} {c : Ctx R Γ A} {s p q τ p′ rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , s , absorbed , p , (q , τ , p′) ∷ rs ⟩
               → Untold p′ (Carried.tree cr)

  private
    -- A job popped: resumed where it was suspended, or dropped, the ghost
    -- alike, the control lighter.
    pop-onward : ∀ {g m Γ A} {c : Ctx R Γ A} {s p j rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , s , absorbed , p , j ∷ rs ⟩
               → MAll.All (λ t → (depthOf t <ᵇ suc (length rs)) ≡ true) (head (Mach.turns m)) → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′
    pop-onward {g} {mach k clk tms ts} {c = c} {s} {p} {q , τ , p′} {rs} cr refl ps
      with Carried.ctlAs cr in eqc | Carried.meets cr | downs q top (plug c s) in d
    ... | popAs refl _ | mt | just (_ , _ , c′ , s′) =
      m′ , trans (pop-step refl ps) (cong (Driver.took R _) (popping {c = c} {s} {p} {q} {τ} {p′} {rs} d))
      , g , m′ , now
      , carried (record
          { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = Carried.tree cr
          ; kernels = trans (Carried.kernels cr) (sym (downs-plug {q = q} {plug c s} d)) ; ctlAs = runAs refl ; meets = mt
          ; owned = owned-popped {c = c} {s = s} {q = q} (Carried.kernels cr) (Carried.owned cr) refl d
          ; meaning = meaning-pop {c = c} {s = s} {q = q} (Carried.kernels cr) (Carried.meaning cr) d
          ; queue = pop-queue cr refl
          ; books = record { clocked = All.head (Books.ticked (Carried.books cr))
                           ; ticked = All.tail (Books.ticked (Carried.books cr)) ; turned = Books.turned (Carried.books cr) }
          ; sorted = proj₁ (Carried.sorted cr) , sorted-pop {c = c} {s = s} {q = q} (proj₂ (Carried.sorted cr)) refl d
          ; behind = pop-behind cr refl ; lingers = Carried.lingers cr ; told = pop-told cr refl
          ; ended = Carried.ended cr ; flags = Carried.flags cr })
      , lowered (λ n → agree-refl n _) (inj₂ (refl , subst (_ <_) (cong weight (sym eqc)) (n<1+n _)))
      where m′ = mach ⟨ c′ , s′ , resuming τ , p′ , rs ⟩ clk tms ts
    ... | popAs refl _ | mt | nothing =
      m′ , trans (pop-step refl ps) (cong (Driver.took R _) (dropping {c = c} {s} {p} {q} {τ} {p′} {rs} d))
      , g , m′ , now
      , carried (record
          { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = Carried.tree cr
          ; kernels = Carried.kernels cr ; ctlAs = settled rs clk tms ts ; meets = settled-meets rs clk tms ts mt
          ; owned = owned-dropped {c = c} {s = s} {j = q , τ , p′} (Carried.kernels cr) (Carried.owned cr) refl d
          ; meaning = meaning-drop {c = c} {s = s} {j = q , τ , p′} (Carried.kernels cr) (Carried.meaning cr) d
          ; queue = Carried.queue cr
          ; books = record { clocked = tt ; ticked = All.tail (Books.ticked (Carried.books cr)) ; turned = Books.turned (Carried.books cr) }
          ; sorted = proj₁ (Carried.sorted cr) , sorted-drop {c = c} {s = s} {j = q , τ , p′} (proj₂ (Carried.sorted cr)) refl d
          ; behind = Carried.behind cr ; lingers = Carried.lingers cr ; told = Carried.told cr
          ; ended = Carried.ended cr ; flags = Carried.flags cr })
      , lowered (λ n → agree-refl n _) (inj₂ (refl , subst (weight (settled rs clk tms ts) <_) (cong weight (sym eqc)) (<-trans (settled-lighter rs clk tms ts) (n<1+n _))))
      where m′ = mach ⟨ c , s , absorbed , p , rs ⟩ clk tms ts
    ... | calmAs () _  | _ | _
    ... | noteAs () _  | _ | _
    ... | runAs ()     | _ | _
    ... | subAs ()     | _ | _
    ... | burstAs refl refl lt | _ | _ = ⊥-elim (unpoppable refl lt ps)
      where unpoppable : ∀ {Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ p′ rs′ t} → ⟨ c′ , s′ , absorbed , p′ , rs′ ⟩ ≡ ⟨ c , s , absorbed , p , (q , τ , p′) ∷ rs ⟩
                       → (depthOf t <ᵇ length rs′) ≡ false → MAll.All (λ t → (depthOf t <ᵇ suc (length rs)) ≡ true) (just t) → ⊥
            unpoppable refl lt (MAll.just pt) with trans (sym lt) pt
            ... | ()

  -- A spent `of` the ghost holds: its completion delivered at its end.
  emit-last : ∀ {g m Γ A} {c : Ctx R Γ A} {i p rs p₀ j} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , ofS [] , resuming (next i) , p , rs ⟩
            → closed c ≡ false → (ψ : Path (Carried.tree cr) (ofˢ {Γ} {A} p₀ j []) (dirs c)) → seen ψ ≡ true
            → Hopped (carried cr) (record m { conf = ⟨ c , doneS , rising cp , p ⊕ [ last ] , rs ⟩ })
  emit-last cr e cl ψ sn = soar (carried cr) (last-enter cr e cl ψ sn)

  -- An `of`'s next value climbs the observers above it; spent, its
  -- completion; under a closed observer, nothing.
  emit-onward : ∀ {g m Γ A} {c : Ctx R Γ A} {xs i p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , ofS xs , resuming (next i) , p , rs ⟩
              → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′
  emit-onward {m = mach _ clk tms ts} {c = c} {xs} {i} {p} {rs} cr refl with closed c in cl
  ... | true = _ , refl , emit-shut cr refl cl
  emit-onward {m = mach _ clk tms ts} {c = c} {[]} {i} {p} {rs} cr refl | false with of-path cr refl
  ... | _ , _ , ψ with seen ψ in sn
  ...   | false = _ , refl , last-void cr refl cl ψ sn
  ...   | true  = _ , refl , emit-last cr refl cl ψ sn
  emit-onward {m = mach _ clk tms ts} {c = c} {x ∷ xs} {i} {p} {rs} cr refl | false with of-path cr refl
  ... | _ , _ , ψ with seen ψ in sn
  ...   | false = _ , refl , emit-void cr refl cl ψ sn
  ...   | true  = _ , refl , soar (carried cr) (emit-open cr refl cl ψ sn)

  -- A takeWhile's completion delivered under its failing value, then
  -- its cut.
  take1-onward : ∀ {g m Γ A} {c : Ctx R Γ A} {i q s p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , takeS i q s , resuming owedCp , p , rs ⟩
               → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′
  take1-onward {m = mach _ clk tms ts} cr refl with take-path cr refl
  ... | _ , _ , ψ with seen ψ in sn
  ...   | false = _ , refl , take1-void cr refl ψ sn
  ...   | true  = _ , refl , soar (carried cr) (take1-enter cr refl ψ sn)

  private
    -- A load no higher and a lighter control weigh less.
    under-lighter : ∀ {ℓ ℓ′ w w′} → ℓ′ ≼ ℓ → w′ < w → (ℓ′ , w′) ≺ (ℓ , w)
    under-lighter (inj₁ refl) lt = inj₂ (refl , lt)
    under-lighter (inj₂ lt)   _  = inj₁ lt

  -- A takeWhile's cut: what it holds unsubscribed; the ghost alike, a
  -- job fewer.
  cut-onward : ∀ {g m Γ A} {c : Ctx R Γ A} {i q s p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , takeS i q s , resuming owedCut , p , rs ⟩
             → Σ Mach λ m′ → step m ≡ silent m′ × Hopped (carried cr) m′
  cut-onward {g} {mach _ clk tms ts} {c = c} {i} {q} {s} {p} {rs} cr refl with Carried.ctlAs cr in eqc | Carried.meets cr
  ... | runAs refl | mt =
    m′ , refl
    , g , m′ , now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = proj₁ (cut-torn cr refl)
        ; kernels = proj₁ (proj₂ (cut-torn cr refl)) ; ctlAs = settled rs clk tms ts
        ; meets = settled-meets rs clk tms ts (trans (proj₂ (proj₂ (cut-torn cr refl))) mt)
        ; owned = cut-owned cr refl ; meaning = cut-meaning cr refl ; queue = cut-queue cr refl
        ; books = record { clocked = tt ; ticked = Books.ticked (Carried.books cr) ; turned = cut-turned cr refl }
        ; sorted = proj₁ (Carried.sorted cr) , cut-sorted (proj₂ (Carried.sorted cr)) refl
        ; behind = cut-behind cr refl ; lingers = cut-lingers cr refl ; told = cut-told cr refl
        ; ended = cut-ended cr refl ; flags = cut-flags cr refl })
    , lowered (λ n → agree-refl n _) (under-lighter (cut-load cr refl) (subst (weight (settled rs clk tms ts) <_) (cong weight (sym eqc)) (settled-lighter rs clk tms ts)))
    where m′ = mach ⟨ c , takeS i q (proj₁ (cut s)) , absorbed , p , rs ⟩ clk tms ts
  ... | calmAs () _  | _
  ... | noteAs () _  | _
  ... | subAs ()     | _
  ... | burstAs () _ _ | _
  ... | popAs () _   | _

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
