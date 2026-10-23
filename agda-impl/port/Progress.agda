{-# OPTIONS --guardedness #-}

-- PROGRESS: whatever item the meaning's events reach, finitely many steps
-- of the machine, read to as many ticks, reach.  The upper half of the
-- link (`port.Adequacy`).
--
-- From a re-entry configuration the machine records the ghost's value,
-- ends or drains with it, or runs silently to a ghost past its skips
-- (`port.Content`'s `Hop`).  A value or a skip passed lowers how far
-- into the residual the item lies; a ghost left where it was lowers the
-- witness's remaining work (`measure`), which is well-founded.
module port.Progress where

open import Data.Bool using (true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; length)
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s; _⊔_; _<ᵇ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m; <ᵇ⇒<; <⇒≱)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import Induction.WellFounded using (Acc; acc)

open import denotation.MonotonicList.Events using (Events∞; Time; out; skip; end; root)
open import denotation.MonotonicList using (Agree; agree-refl; agree-trans; observe)
open import denotation.Denote using (⟦_⟧)
import denotation.Unfold as U
open import operation.Placed using (Ahead; none; outᵃ; skipᵃ; endᵃ; hushᵃ; items)
open import operation.PureObservable using (PureObs; module Driver)
open import port.Content using (module Honesty)
open import port.Ghost using (module Ghosting)
open import port.Strong using (module Strongly)
open import port.Unsub using (module Unsubbing)

open Events∞

module Progressing (R : Set) where
  open Driver R using (Mach; step; silent; value; complete; drained; trace; shown; reading; begin; Trace; Trace∞; tau; idle; log; ending)
    renaming (out to outᵗ; end to endᵗ)
  open Unsubbing R using (_⇝_; now; then)
  open Ghosting R using (Has; atOut; pastSkip; residual; begun; Past; past-pre; passed; lowered; showing;
    has-agree; after; _≺_; ≺-wf; measure; depth; ahead-agree)
  open Strongly R using (Strong; strong-begin)
  open Honesty R using (Hop; valueᴴ; completeᴴ; drainedᴴ; silentᴴ; strong-hop; strong-agrees)

  ----------------------------------------------------------------------
  -- How far a trace gets

  -- The trace shows `k` items, each within finitely many steps.
  data Gets : Trace → ℕ → Set where
    zeroᵍ : ∀ {t} → Gets t 0
    tauᵍ  : ∀ {c l n} → Gets (Trace∞.force l) n → Gets (tau c l) n
    outᵍ  : ∀ {c p a l n} → Gets (Trace∞.force l) n → Gets (outᵗ c p a l) (suc n)
    endᵍ  : ∀ {p} → Gets (endᵗ p) 1
    idleᵍ : Gets idle 1

  private
    -- A tick no later than the horizon is not past it.
    within : ∀ {t h} → t ≤ h → (h <ᵇ t) ≡ false
    within {t} {h} le with h <ᵇ t in e
    ... | false = refl
    ... | true  = ⊥-elim (<⇒≱ (<ᵇ⇒< h t (subst T (sym e) tt)) le)

  -- Some prefix reads as many items as a trace gets: every prefix of at
  -- least so many steps, read to at least so late a tick.
  gets-reading : ∀ {t k} → Gets t k → ∀ c → Σ ℕ λ s → Σ Time λ b
               → ∀ n h → s ≤ n → b ≤ h → k ≤ length (items (log (reading h n c t)) (ending (reading h n c t)))
  gets-reading zeroᵍ c = 0 , 0 , λ n h _ _ → z≤n
  gets-reading (tauᵍ {c = c′} {l} {k} g) c = suc s , c′ ⊔ b , go
    where
    ih = gets-reading g c′
    s  = proj₁ ih
    b  = proj₁ (proj₂ ih)
    go : ∀ n h → suc s ≤ n → c′ ⊔ b ≤ h → k ≤ length (items (log (reading h n c (tau c′ l))) (ending (reading h n c (tau c′ l))))
    go (suc n) h (s≤s le) bh rewrite within {c′} {h} (≤-trans (m≤m⊔n c′ b) bh) = proj₂ (proj₂ ih) n h le (≤-trans (m≤n⊔m c′ b) bh)
  gets-reading (outᵍ {c = c′} {p} {a} {l} {k} g) c = suc s , c′ ⊔ b , go
    where
    ih = gets-reading g c′
    s  = proj₁ ih
    b  = proj₁ (proj₂ ih)
    go : ∀ n h → suc s ≤ n → c′ ⊔ b ≤ h → suc k ≤ length (items (log (reading h n c (outᵗ c′ p a l))) (ending (reading h n c (outᵗ c′ p a l))))
    go (suc n) h (s≤s le) bh rewrite within {c′} {h} (≤-trans (m≤m⊔n c′ b) bh) = s≤s (proj₂ (proj₂ ih) n h le (≤-trans (m≤n⊔m c′ b) bh))
  gets-reading endᵍ  c = 1 , 0 , λ { (suc n) h (s≤s _) _ → ≤-refl }
  gets-reading idleᵍ c = 1 , 0 , λ { (suc n) h (s≤s _) _ → ≤-refl }

  -- A silent run adds nothing to what a trace gets.
  walk : ∀ {m m₀ k} → m ⇝ m₀ → Gets (trace m₀) k → Gets (trace m) k
  walk now           g = g
  walk (then eq path) g = subst (λ s → Gets (shown s) _) (sym eq) (tauᵍ (walk path g))

  -- Events with nothing in them reach their silence at most.
  ahead-none : ∀ {e k} → (∀ {q b} → Has e q b → ⊥) → Ahead e k → k ≤ 1
  ahead-none no none      = z≤n
  ahead-none no (outᵃ a)  = ⊥-elim (no atOut)
  ahead-none no (skipᵃ a) = ahead-none (λ h → no (pastSkip h)) a
  ahead-none no endᵃ      = ≤-refl
  ahead-none no hushᵃ     = ≤-refl

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

  -- Past a skip of `e`, an item lies shallower.
  skipped-split : ∀ {f e q r y k} → (∀ n → Agree n e (skip q r)) → Past (force r) y → (a : Ahead e (suc k)) → depth a ≤ f
                → Σ (Ahead y (suc k)) λ b → depth b < f
  skipped-split {f} ag p a le with ahead-agree ag a
  ... | skipᵃ a′ , de with Past.fewer p a′
  ...   | b , le′ = b , ≤-trans (s≤s le′) (subst (_≤ f) (sym de) le)

  value≢silent : ∀ {t p a m′ m″} → value t p a m′ ≢ silent m″
  value≢silent ()

  complete≢silent : ∀ {p m″} → complete p ≢ silent m″
  complete≢silent ()

  drained≢silent : ∀ {m″} → drained ≢ silent m″
  drained≢silent ()

  -- From a re-entry configuration over `e`, the machine gets as far as
  -- `e` reaches.  By the item's depth, then the work left before the
  -- ghost moves; a configuration whose step shows something by depth
  -- alone.
  mutual
    reentry : ∀ f {e g m k} (a : Ahead e k) → depth a < f → (st : Strong g m) → (∀ n → Agree n e (residual g))
            → Acc _≺_ (measure st) → Hop st → Gets (trace m) k
    reentry f a lt st ag ac h@(valueᴴ eq _ _ _ _) = shown-gets f a lt st ag h (λ eq′ → value≢silent (trans (sym eq) eq′))
    reentry f a lt st ag ac h@(completeᴴ eq _)    = shown-gets f a lt st ag h (λ eq′ → complete≢silent (trans (sym eq) eq′))
    reentry f a lt st ag ac h@(drainedᴴ eq _)     = shown-gets f a lt st ag h (λ eq′ → drained≢silent (trans (sym eq) eq′))
    reentry f       {k = zero}  a lt st ag ac (silentᴴ _ _) = zeroᵍ
    reentry zero    {k = suc k} a () st ag ac (silentᴴ _ _)
    reentry (suc f) {k = suc k} a (s≤s lt) st ag (acc rs) (silentᴴ eq (g″ , m₀ , path , st₀ , lowered ag″ lo)) =
      subst (λ s → Gets (shown s) (suc k)) (sym eq)
        (tauᵍ (walk path (reentry (suc f) a (s≤s lt) st₀ (λ n → agree-trans (ag n) (ag″ n)) (rs lo) (strong-hop st₀))))
    reentry (suc f) {k = suc k} a (s≤s lt) st ag ac (silentᴴ eq (g″ , m₀ , path , st₀ , passed ag₁ p)) =
      subst (λ s → Gets (shown s) (suc k)) (sym eq)
        (tauᵍ (walk path (reentry f (proj₁ b) (proj₂ b) st₀ (λ n → agree-refl n _) (≺-wf _) (strong-hop st₀))))
      where b = skipped-split (λ n → agree-trans (ag n) (ag₁ n)) p a lt
    reentry (suc f) {k = suc k} a (s≤s lt) st ag ac (silentᴴ eq (g″ , m₀ , path , st₀ , showing p ns)) =
      subst (λ s → Gets (shown s) (suc k)) (sym eq)
        (tauᵍ (walk path (shown-gets (suc f) (proj₁ b) (s≤s (≤-trans (proj₂ b) lt)) st₀ (λ n → agree-refl n _) (strong-hop st₀) ns)))
      where b = Past.fewer (past-pre ag p) a

    -- A re-entry configuration whose step shows something.
    shown-gets : ∀ f {e g m k} (a : Ahead e k) → depth a < f → (st : Strong g m) → (∀ n → Agree n e (residual g)) → Hop st
               → (∀ {m″} → step m ≢ silent m″) → Gets (trace m) k
    shown-gets f       {k = zero}  a lt st ag h ns = zeroᵍ
    shown-gets zero    {k = suc k} a () st ag h ns
    shown-gets (suc f) {g = g} {k = suc k} a (s≤s lt) st ag (valueᴴ eq stp _ _ (m₀ , path , st₀)) ns =
      subst (λ s → Gets (shown s) (suc k)) (sym eq)
        (outᵍ (walk path (reentry f (proj₁ v) (proj₂ v) st₀ (λ n → agree-refl n _) (≺-wf _) (strong-hop st₀))))
      where v = value-step a lt (λ n → agree-trans (ag n) (subst (λ s → Agree n (residual g) (after s)) stp (strong-agrees st n)))
    shown-gets (suc f) {g = g} {k = suc k} a (s≤s lt) st ag (completeᴴ eq stp) ns =
      subst (λ s → Gets (shown s) (suc k)) (sym eq)
        (end-gets a (λ n → agree-trans (ag n) (subst (λ s → Agree n (residual g) (after s)) stp (strong-agrees st n))))
    shown-gets (suc f) {k = suc k} a (s≤s lt) st ag (drainedᴴ eq no) ns =
      subst (λ s → Gets (shown s) (suc k)) (sym eq) (idle-gets a (λ h → no (has-agree ag h)))
    shown-gets (suc f) {k = suc k} a lt st ag (silentᴴ eq _) ns = ⊥-elim (ns eq)

  -- LIVENESS: whatever item the meaning's events reach, some prefix of
  -- the launch's run reads, as many steps as ticks.
  reached : (o : PureObs [] R) → ∀ {k} → Ahead (observe (⟦ o ⟧ []) root) k
          → Σ ℕ λ n → k ≤ length (items (log (reading n n 0 (trace (begin o)))) (ending (reading n n 0 (trace (begin o)))))
  reached o a with gets-reading (reentry (suc (depth b)) b ≤-refl st (λ n → agree-refl n _) (≺-wf _) (strong-hop st)) 0
    where b  = proj₁ (ahead-agree (begun o) a)
          st = strong-begin o
  ... | s , c , f = s ⊔ c , f (s ⊔ c) (s ⊔ c) (m≤m⊔n s c) (m≤n⊔m s c)
