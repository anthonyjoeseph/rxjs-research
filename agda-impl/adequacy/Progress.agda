{-# OPTIONS --guardedness #-}

-- PROGRESS: whatever item the meaning's events reach, finitely many steps
-- of the machine reach.  The upper half of the link (`adequacy.Adequacy`).
--
-- From a re-entry configuration the machine records the ghost's value,
-- ends or drains with it, or runs silently to a ghost past its skips
-- (`adequacy.Content`'s `Hop`).  A value or a skip passed lowers how far
-- into the residual the item lies; a ghost left where it was lowers
-- nothing, so a run is owed to be calm: no endless silent run of re-entry
-- configurations over one residual.
module adequacy.Progress where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; length)
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; m≤n⇒m≤1+n; ≤-trans)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import denotation.MonotonicList using (Events; Events∞; out; end; Agree; out⁼; skip⁼; end⁼; hush⁼; agree-refl; agree-trans; observe; root)
open import denotation.Denote using (⟦_⟧)
import denotation.Unfold as U
open import operation.Machine using (module Machine)
open import operation.Placed using (Ahead; none; outᵃ; skipᵃ; endᵃ; hushᵃ; items)
open import operation.PureObservable using (PureObs)
open import adequacy.Content using (module Honesty)
open import adequacy.Strong using (module Strongly)

open Events∞

module Progressing (R : Set) where
  open Machine R using (Mach; step; silent; value; complete; drained; trace; shown; reading; begin; Read; Trace; Trace∞; tau; idle)
    renaming (out to outᵗ; end to endᵗ)
  open Honesty R using (Has; atOut; pastSkip; residual; begun; _⇝_; now; then; Past; agrees; skipped; past-pre; tail-out; tail-skip;
    has-agree; after; Hop; valueᴴ; completeᴴ; drainedᴴ; silentᴴ; strong-hop; strong-agrees)
  open Strongly R using (Strong; strong-begin)
  open Read

  ----------------------------------------------------------------------
  -- How far a trace gets

  -- The trace shows `k` items, each within finitely many steps.
  data Gets : Trace → ℕ → Set where
    zeroᵍ : ∀ {t} → Gets t 0
    tauᵍ  : ∀ {c l n} → Gets (Trace∞.force l) n → Gets (tau c l) n
    outᵍ  : ∀ {c p a l n} → Gets (Trace∞.force l) n → Gets (outᵗ c p a l) (suc n)
    endᵍ  : ∀ {p} → Gets (endᵗ p) 1
    idleᵍ : Gets idle 1

  -- Some prefix reads as many items as a trace gets.
  gets-reading : ∀ {t k} → Gets t k → ∀ c → Σ ℕ λ n → k ≤ length (items (log (reading n c t)) (ending (reading n c t)))
  gets-reading zeroᵍ c = 0 , z≤n
  gets-reading (tauᵍ {c = c′} g) c with gets-reading g c′
  ... | n , le = suc n , le
  gets-reading (outᵍ {c = c′} g) c with gets-reading g c′
  ... | n , le = suc n , s≤s le
  gets-reading endᵍ  c = 1 , ≤-refl
  gets-reading idleᵍ c = 1 , ≤-refl

  -- A silent run adds nothing to what a trace gets.
  walk : ∀ {m m₀ k} → m ⇝ m₀ → Gets (trace m₀) k → Gets (trace m) k
  walk now           g = g
  walk (then eq path) g = subst (λ s → Gets (shown s) _) (sym eq) (tauᵍ (walk path g))

  ----------------------------------------------------------------------
  -- How far into the events an item lies

  depth : ∀ {e : Events R} {k} → Ahead e k → ℕ
  depth none      = 0
  depth (outᵃ a)  = suc (depth a)
  depth (skipᵃ a) = suc (depth a)
  depth endᵃ      = 0
  depth hushᵃ     = 0

  ahead-agree : ∀ {x y k} → (∀ n → Agree n x y) → (a : Ahead x k) → Σ (Ahead y k) λ b → depth b ≡ depth a
  ahead-agree ag none = none , refl
  ahead-agree ag (outᵃ a) with ag 1
  ... | out⁼ _ with ahead-agree (λ n → tail-out (ag (suc n))) a
  ...   | b , eq = outᵃ b , cong suc eq
  ahead-agree ag (skipᵃ a) with ag 1
  ... | skip⁼ _ with ahead-agree (λ n → tail-skip (ag (suc n))) a
  ...   | b , eq = skipᵃ b , cong suc eq
  ahead-agree ag endᵃ with ag 1
  ... | end⁼ = endᵃ , refl
  ahead-agree ag hushᵃ with ag 1
  ... | hush⁼ = hushᵃ , refl

  -- Past a skip an item lies no deeper.
  ahead-past : ∀ {x y k} → Past x y → (a : Ahead x k) → Σ (Ahead y k) λ b → depth b ≤ depth a
  ahead-past (agrees ag) a = proj₁ (ahead-agree ag a) , ≤-reflexive (proj₂ (ahead-agree ag a))
  ahead-past (skipped ag p) a with ahead-agree ag a
  ... | none , eq = none , z≤n
  ... | skipᵃ a′ , eq with ahead-past p a′
  ...   | b , le = b , subst (depth b ≤_) eq (m≤n⇒m≤1+n le)

  -- Events with nothing in them reach their silence at most.
  ahead-none : ∀ {e k} → (∀ {q b} → Has e q b → ⊥) → Ahead e k → k ≤ 1
  ahead-none no none      = z≤n
  ahead-none no (outᵃ a)  = ⊥-elim (no atOut)
  ahead-none no (skipᵃ a) = ahead-none (λ h → no (pastSkip h)) a
  ahead-none no endᵃ      = ≤-refl
  ahead-none no hushᵃ     = ≤-refl

  ----------------------------------------------------------------------
  -- THE RUN IS CALM

  -- No endless silent run of re-entry configurations whose ghosts all
  -- show `e`: each re-entry reached silently over `e` is calm again, and
  -- the chain is finite.
  data Calm (e : Events R) (m : Mach) : Set₁ where
    calm : (∀ {m′ m₀ g′} → step m ≡ silent m′ → m′ ⇝ m₀ → Strong g′ m₀ → (∀ n → Agree n e (residual g′)) → Calm e m₀) → Calm e m

  postulate
    -- A RE-ENTRY CONFIGURATION IS CALM over its ghost's residual: the
    -- silent hops that leave the ghost where it is — a popped timer, a
    -- poll, a spent burst dropped, a burst over, owed todos paid — come
    -- finitely often before one moves it.
    calm-leaf : ∀ {g m} → Strong g m → Calm (residual g) m

  ----------------------------------------------------------------------
  -- THE ASSEMBLY

  -- A value the ghost shows lies one item in.
  value-step : ∀ {f e p a r k} (x : Ahead e (suc k)) → depth x ≤ f → (∀ n → Agree n e (out p a r)) → Σ (Ahead (force r) k) λ b → depth b < f
  value-step x le ag with ahead-agree ag x
  ... | outᵃ b , de = b , subst (_≤ _) (sym de) le

  -- The ghost's end is the last item.
  end-gets : ∀ {e p q k} → Ahead e k → (∀ n → Agree n e (end q)) → Gets (endᵗ p) k
  end-gets x ag with ahead-agree ag x
  ... | none , _ = zeroᵍ
  ... | endᵃ , _ = endᵍ

  -- A ghost showing nothing shows its silence at most.
  idle-gets : ∀ {e k} → Ahead e k → (∀ {q b} → Has e q b → ⊥) → Gets idle k
  idle-gets x no with ahead-none no x
  ... | z≤n     = zeroᵍ
  ... | s≤s z≤n = idleᵍ

  -- A ghost past `e` shows it alike, or past a skip, an item lying
  -- shallower.
  past-split : ∀ {f e y k} → Past e y → (a : Ahead e (suc k)) → depth a ≤ f
             → (∀ n → Agree n e y) ⊎ Σ (Ahead y (suc k)) λ b → depth b < f
  past-split (agrees ag) a le = inj₁ ag
  past-split {f} (skipped ag p) a le with ahead-agree ag a
  ... | skipᵃ a′ , de with ahead-past p a′
  ...   | b , le′ = inj₂ (b , ≤-trans (s≤s le′) (subst (_≤ f) (sym de) le))

  -- From a re-entry configuration over `e`, the machine gets as far as
  -- `e` reaches.  By the item's depth, then the run's calm.
  reentry : ∀ f {e g m k} (a : Ahead e k) → depth a < f → Strong g m → (∀ n → Agree n e (residual g)) → Calm e m → Hop g m
          → Gets (trace m) k
  reentry f       {k = zero}  a lt st ag cm h = zeroᵍ
  reentry zero    {k = suc k} a () st ag cm h
  reentry (suc f) {g = g} {k = suc k} a (s≤s lt) st ag cm (valueᴴ eq stp _ _ (m₀ , path , st₀)) =
    subst (λ s → Gets (shown s) (suc k)) (sym eq)
      (outᵍ (walk path (reentry f (proj₁ v) (proj₂ v) st₀ (λ n → agree-refl n _) (calm-leaf st₀) (strong-hop st₀))))
    where v = value-step a lt (λ n → agree-trans (ag n) (subst (λ s → Agree n (residual g) (after s)) stp (strong-agrees st n)))
  reentry (suc f) {g = g} {k = suc k} a (s≤s lt) st ag cm (completeᴴ eq stp) =
    subst (λ s → Gets (shown s) (suc k)) (sym eq)
      (end-gets a (λ n → agree-trans (ag n) (subst (λ s → Agree n (residual g) (after s)) stp (strong-agrees st n))))
  reentry (suc f) {k = suc k} a (s≤s lt) st ag cm (drainedᴴ eq no) =
    subst (λ s → Gets (shown s) (suc k)) (sym eq) (idle-gets a (λ h → no (has-agree ag h)))
  reentry (suc f) {k = suc k} a (s≤s lt) st ag (calm cm) (silentᴴ eq (g″ , past , m₀ , path , st₀)) =
    subst (λ s → Gets (shown s) (suc k)) (sym eq) (tauᵍ (walk path
      ([ (λ ag″ → reentry (suc f) a (s≤s lt) st₀ ag″ (cm eq path st₀ ag″) (strong-hop st₀))
       , (λ b → reentry f (proj₁ b) (proj₂ b) st₀ (λ n → agree-refl n _) (calm-leaf st₀) (strong-hop st₀)) ]′
       (past-split (past-pre ag past) a lt))))

  -- LIVENESS: whatever item the meaning's events reach, some prefix of
  -- the launch's run reads.
  reached : (o : PureObs [] R) → ∀ {k} → Ahead (observe (⟦ o ⟧ []) root) k
          → Σ ℕ λ n → k ≤ length (items (log (reading n 0 (trace (begin o)))) (ending (reading n 0 (trace (begin o)))))
  reached o a = gets-reading (reentry (suc (depth b)) b ≤-refl st (λ n → agree-refl n _) (calm-leaf st) (strong-hop st)) 0
    where b  = proj₁ (ahead-agree (begun o) a)
          st = strong-begin o
