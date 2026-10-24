{-# OPTIONS --guardedness #-}

-- PROGRESS: whatever item the meaning's events reach, finitely many steps
-- of the machine, read to as many ticks, reach.  The upper half of the
-- link (`adequacy.Adequacy`).
--
-- From a re-entry configuration the machine records the ghost's value,
-- ends or drains with it, or runs silently to a ghost past its skips
-- (`adequacy.Content`'s `Hop`).  A value or a skip passed lowers how
-- far into the residual the item lies; a ghost left where it was lowers
-- the witness's remaining work (`measure`), which is well-founded.
module adequacy.Progress where

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

open import denotation.MonotonicList.Events using (Events; Events∞; Time; out; skip; end; root)
open import denotation.MonotonicList using (Agree; agree-refl; agree-trans; observe)
open import denotation.Denote using (⟦_⟧)
open import adequacy.Record using (Ahead; none; outᵃ; skipᵃ; endᵃ; hushᵃ; items)
open import operation.PureObservable using (PureObs; module Driver; module Machine)
open import adequacy.Content using (module Honesty)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Engine.Meaning using (Has; atOut; pastSkip; has-agree)
open import adequacy.Strong using (module Strongly)
open import adequacy.Unsub using (module Unsubbing)

open Events∞

module Progressing (R : Set) where
  open Driver R using (step; silent; value; complete; drained; reading; Read; later)
  open Machine using (Conf; load)
  open Unsubbing R using (_⇝_; now; then)
  open Ghosting R using (residual; begun; Past; past-pre; passed; lowered; showing;
    after; _≺_; ≺-wf; measure; depth; ahead-agree)
  open Strongly R using (Strong; strong-begin)
  open Honesty R using (Hop; valueᴴ; completeᴴ; drainedᴴ; silentᴴ; strong-hop; strong-sane; led-agrees)

  ----------------------------------------------------------------------
  -- How far a run gets

  -- The run from `m` shows `k` items, each within finitely many steps.
  data Gets : Conf R → ℕ → Set₁ where
    zeroᵍ : ∀ {m} → Gets m 0
    tauᵍ  : ∀ {m t m′ n} → step m ≡ silent t m′ → Gets m′ n → Gets m n
    outᵍ  : ∀ {m t p a m′ n} → step m ≡ value t p a m′ → Gets m′ n → Gets m (suc n)
    endᵍ  : ∀ {m p} → step m ≡ complete p → Gets m 1
    idleᵍ : ∀ {m} → step m ≡ drained → Gets m 1

  private
    -- A tick no later than the horizon is not past it.
    within : ∀ {t h} → t ≤ h → (h <ᵇ t) ≡ false
    within {t} {h} le with h <ᵇ t in e
    ... | false = refl
    ... | true  = ⊥-elim (<⇒≱ (<ᵇ⇒< h t (subst T (sym e) tt)) le)

  -- Some prefix reads as many items as a run gets: every prefix of at
  -- least so many steps, read to at least so late a tick.
  gets-reading : ∀ {m k} → Gets m k → ∀ c → Σ ℕ λ s → Σ Time λ b
               → ∀ n h → s ≤ n → b ≤ h → k ≤ length (items (Read.log (reading h n c m)) (Read.endedAs (reading h n c m)))
  gets-reading zeroᵍ c = 0 , 0 , λ n h _ _ → z≤n
  gets-reading {m} {k} (tauᵍ {t = t} {m′} eq g) c = suc s , t ⊔ b , go
    where
    ih = gets-reading g (later c t)
    s  = proj₁ ih
    b  = proj₁ (proj₂ ih)
    go : ∀ n h → suc s ≤ n → t ⊔ b ≤ h → k ≤ length (items (Read.log (reading h n c m)) (Read.endedAs (reading h n c m)))
    go (suc n) h (s≤s le) bh rewrite eq | within {t} {h} (≤-trans (m≤m⊔n t b) bh) = proj₂ (proj₂ ih) n h le (≤-trans (m≤n⊔m t b) bh)
  gets-reading {m} {suc k} (outᵍ {t = t} {m′ = m′} eq g) c = suc s , t ⊔ b , go
    where
    ih = gets-reading g t
    s  = proj₁ ih
    b  = proj₁ (proj₂ ih)
    go : ∀ n h → suc s ≤ n → t ⊔ b ≤ h → suc k ≤ length (items (Read.log (reading h n c m)) (Read.endedAs (reading h n c m)))
    go (suc n) h (s≤s le) bh rewrite eq | within {t} {h} (≤-trans (m≤m⊔n t b) bh) = s≤s (proj₂ (proj₂ ih) n h le (≤-trans (m≤n⊔m t b) bh))
  gets-reading {m} (endᵍ eq)  c = 1 , 0 , go
    where
    go : ∀ n h → 1 ≤ n → 0 ≤ h → 1 ≤ length (items (Read.log (reading h n c m)) (Read.endedAs (reading h n c m)))
    go (suc n) h (s≤s _) _ rewrite eq = ≤-refl
  gets-reading {m} (idleᵍ eq) c = 1 , 0 , go
    where
    go : ∀ n h → 1 ≤ n → 0 ≤ h → 1 ≤ length (items (Read.log (reading h n c m)) (Read.endedAs (reading h n c m)))
    go (suc n) h (s≤s _) _ rewrite eq = ≤-refl

  -- A silent run adds nothing to what a run gets.
  walk : ∀ {m m₀ k} → m ⇝ m₀ → Gets m₀ k → Gets m k
  walk now            g = g
  walk (then eq path) g = tauᵍ eq (walk path g)

  -- Events with nothing in them reach their silence at most.
  ahead-none : ∀ {e : Events R} {k} → (∀ {q b} → Has e q b → ⊥) → Ahead e k → k ≤ 1
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
  end-gets : ∀ {m e p q k} → step m ≡ complete p → Ahead e k → (∀ n → Agree n e (end q)) → Gets m k
  end-gets eq x ag with ahead-agree ag x
  ... | none , _ = zeroᵍ
  ... | endᵃ , _ = endᵍ eq

  -- A ghost showing nothing shows its silence at most.
  idle-gets : ∀ {m} {e : Events R} {k} → step m ≡ drained → Ahead e k → (∀ {q b} → Has e q b → ⊥) → Gets m k
  idle-gets eq x no with ahead-none no x
  ... | z≤n     = zeroᵍ
  ... | s≤s z≤n = idleᵍ eq

  -- Past a skip of `e`, an item lies shallower.
  skipped-split : ∀ {f e q r y k} → (∀ n → Agree n e (skip q r)) → Past (force r) y → (a : Ahead e (suc k)) → depth a ≤ f
                → Σ (Ahead y (suc k)) λ b → depth b < f
  skipped-split {f} ag p a le with ahead-agree ag a
  ... | skipᵃ a′ , de with Past.fewer p a′
  ...   | b , le′ = b , ≤-trans (s≤s le′) (subst (_≤ f) (sym de) le)

  value≢silent : ∀ {t p a m′ t′ m″} → value t p a m′ ≢ silent t′ m″
  value≢silent ()

  complete≢silent : ∀ {p t m″} → complete p ≢ silent t m″
  complete≢silent ()

  drained≢silent : ∀ {t m″} → drained ≢ silent t m″
  drained≢silent ()

  -- From a re-entry configuration over `e`, the machine gets as far as
  -- `e` reaches.  By the item's depth, then the work left before the
  -- ghost moves; a configuration whose step shows something by depth
  -- alone.
  mutual
    reentry : ∀ f {e g m k} (a : Ahead e k) → depth a < f → (st : Strong g m) → (∀ n → Agree n e (residual g))
            → Acc _≺_ (measure st) → Hop st → Gets m k
    reentry f a lt st ag ac h@(valueᴴ eq _ _ _ _) = shown-gets f a lt st ag h (λ eq′ → value≢silent (trans (sym eq) eq′))
    reentry f a lt st ag ac h@(completeᴴ eq _)    = shown-gets f a lt st ag h (λ eq′ → complete≢silent (trans (sym eq) eq′))
    reentry f a lt st ag ac h@(drainedᴴ eq _)     = shown-gets f a lt st ag h (λ eq′ → drained≢silent (trans (sym eq) eq′))
    reentry f       {k = zero}  a lt st ag ac (silentᴴ _ _) = zeroᵍ
    reentry zero    {k = suc k} a () st ag ac (silentᴴ _ _)
    reentry (suc f) {k = suc k} a (s≤s lt) st ag (acc rs) (silentᴴ eq (g″ , m₀ , path , st₀ , lowered ag″ lo)) =
      tauᵍ eq (walk path (reentry (suc f) a (s≤s lt) st₀ (λ n → agree-trans (ag n) (ag″ n)) (rs lo) (strong-hop st₀)))
    reentry (suc f) {k = suc k} a (s≤s lt) st ag ac (silentᴴ eq (g″ , m₀ , path , st₀ , passed ag₁ p)) =
      tauᵍ eq (walk path (reentry f (proj₁ b) (proj₂ b) st₀ (λ n → agree-refl n _) (≺-wf _) (strong-hop st₀)))
      where b = skipped-split (λ n → agree-trans (ag n) (ag₁ n)) p a lt
    reentry (suc f) {k = suc k} a (s≤s lt) st ag ac (silentᴴ eq (g″ , m₀ , path , st₀ , showing p ns)) =
      tauᵍ eq (walk path (shown-gets (suc f) (proj₁ b) (s≤s (≤-trans (proj₂ b) lt)) st₀ (λ n → agree-refl n _) (strong-hop st₀) ns))
      where b = Past.fewer (past-pre ag p) a

    -- A re-entry configuration whose step shows something.
    shown-gets : ∀ f {e g m k} (a : Ahead e k) → depth a < f → (st : Strong g m) → (∀ n → Agree n e (residual g)) → Hop st
               → (∀ {t m″} → step m ≢ silent t m″) → Gets m k
    shown-gets f       {k = zero}  a lt st ag h ns = zeroᵍ
    shown-gets zero    {k = suc k} a () st ag h ns
    shown-gets (suc f) {k = suc k} a (s≤s lt) st ag (valueᴴ eq ld _ _ (m₀ , path , st₀)) ns
      with led-agrees (proj₁ (strong-sane st)) (proj₂ (strong-sane st)) ld
    ... | y , p , ag′ with Past.fewer (past-pre ag p) a
    ...   | b , le with value-step b (≤-trans le lt) ag′
    ...     | v , lt′ = outᵍ eq (walk path (reentry f v lt′ st₀ (λ n → agree-refl n _) (≺-wf _) (strong-hop st₀)))
    shown-gets (suc f) {k = suc k} a (s≤s lt) st ag (completeᴴ eq ld) ns
      with led-agrees (proj₁ (strong-sane st)) (proj₂ (strong-sane st)) ld
    ... | y , p , ag′ = end-gets eq (proj₁ (Past.fewer (past-pre ag p) a)) ag′
    shown-gets (suc f) {k = suc k} a (s≤s lt) st ag (drainedᴴ eq no) ns =
      idle-gets eq a (λ h → no (has-agree ag h))
    shown-gets (suc f) {k = suc k} a lt st ag (silentᴴ eq _) ns = ⊥-elim (ns eq)

  -- LIVENESS: whatever item the meaning's events reach, some prefix of
  -- the launch's run reads, as many steps as ticks.
  reached : (o : PureObs [] R) → ∀ {k} → Ahead (observe (⟦ o ⟧ []) root) k
          → Σ ℕ λ n → k ≤ length (items (Read.log (reading n n 0 (load o))) (Read.endedAs (reading n n 0 (load o))))
  reached o a with gets-reading (reentry (suc (depth b)) b ≤-refl st (λ n → agree-refl n _) (≺-wf _) (strong-hop st)) 0
    where b  = proj₁ (ahead-agree (begun o) a)
          st = strong-begin o
  ... | s , c , f = s ⊔ c , f (s ⊔ c) (s ⊔ c) (m≤m⊔n s c) (m≤n⊔m s c)
