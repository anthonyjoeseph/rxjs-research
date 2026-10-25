{-# OPTIONS --guardedness #-}

-- A CONNECT'S BODY BESIDE ITS SOURCE, EACH FED A RUN WITH SKIPS ERASED,
-- RUNS WITH SKIPS ERASED (`body-⊒`), its source subscribed where the
-- connect is (`Sourced`).
--
-- Its tail pins the source's steps under the subscription: a step erased
-- there is a pin erased, and no later than what the other pins next
-- (`run-erase`), since what the other leaves running trails its next.  A
-- step erased past the subscription is past every pin.
--
-- Its run shows each source step at its first effect and the body's
-- between them.  A source step kept shows on both sides where the
-- body's next stands against it, and an erased body step before it
-- moves no kept one past it (`walkK`).  A source step erased shows
-- before whatever the other shows next: the other's source step is at
-- or past it, and the body steps it lets through come no later
-- (`walkA`, `walkH`).
module adequacy.Engine.Beside where

open import Data.Bool using (true; false)
open import Data.List using (_++_; [_])
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import denotation.MonotonicList.Events using (Events; Events∞; Tail; Pos; out; skip; end; hush; pin; idle; _∪_; ix; _<ᵖ_; inside;
  inside-self; inside-++; <ᵖ-split; <ᵖ-between; <ᵖ-asym; <ᵖ-shift; ≮-trans)
import denotation.MonotonicList as M′
open import denotation.MonotonicList using (head; tailᴱ; Agree; Agreeᵀ; agree-sym; agreeᵀ-refl; agreeᵀ-sym)
open import denotation.NonExpansive using (Agreeˢ; ∪-ne)
open import adequacy.Engine.Meaning using (_≋_; bodyConn)
open import adequacy.Engine.Race using (After; NotBefore; TailNotBefore)
open import adequacy.Engine.Erase using (Eraseᵀ; Erase; Lead⁼; Eraseˢ; _,ᵉ_; cutᵉ; nowᵉ; _⊒_; stopᵉ; pinᵉ; unpin; idleᵉ; outᵉ; skipᵉ;
  erased; endᵉ; hushᵉ; outᴸ; skipᴸ; endᴸ; hushᴸ; eraseᵀ-pred; eraseˢ-pred; after-nb; after-erase; ∪-erase)
open import adequacy.Placed.Order using (Atop; Ordered; ordered; EveryT; everyᵀ)
open import adequacy.Placed.Trail using (Trail; TrailE; Trailing; trail; trailᶠ; trail-≈; inside-under)
open import adequacy.Placed.Keys using (atop-agree; ordered-≈)
open import adequacy.Placed.Rising using (AtopT; atop-weaken; prefix-rest)
open import adequacy.Placed.Burst using (module Bursting; trail-tail; atop-tailᴱ; ordered-tail)
open import adequacy.Stepper using (side-hush)
open Events∞
open Agreeˢ

------------------------------------------------------------------------
-- A source subscribed where the connect is

-- Its next no earlier, its run in order, and what it leaves running
-- trailing it.
record Sourced {X : Set} (r : Pos) (σ : Events∞ X) : Set where
  constructor sourced
  field
    srcAtop  : Atop r (force σ)
    srcOrd   : Ordered (force σ)
    srcTrail : Trailing σ

-- So past a skip it agrees with.
sourced-skip : ∀ {X r k} {σ σ₁ : Events∞ X} → Sourced r σ → (∀ n → Agree n (force σ) (skip k σ₁)) → Sourced r σ₁
sourced-skip {r = r} {k} {σ} {σ₁} (sourced a o t) ag =
  sourced (atop-weaken k r (force σ₁) (atop-agree (ag 1) a) (proj₁ (ordered o′))) (proj₂ (ordered o′)) (proj₂ (proj₂ (trail t′)))
  where
    o′ = ordered-≈ (force σ) (skip k σ₁) ag o
    t′ = trail-≈ (force σ) (skip k σ₁) (cut σ) (cut σ) ag (λ n → agreeᵀ-refl n (cut σ)) t

-- And so is what agrees with one.
sourced-≋ : ∀ {X r} {σ σ′ : Events∞ X} → σ ≋ σ′ → Sourced r σ′ → Sourced r σ
sourced-≋ {σ = σ} {σ′} x (sourced a o t) =
  sourced (atop-agree (agree-sym (nowˢ (x 1))) a) (ordered-≈ (force σ′) (force σ) (λ n → agree-sym (nowˢ (x n))) o)
    (trail-≈ (force σ′) (force σ) (cut σ′) (cut σ) (λ n → agree-sym (nowˢ (x n))) (λ n → agreeᵀ-sym (cutˢ (x n))) t)

------------------------------------------------------------------------
-- Positions

-- Past a subscription and not under it, so is all that comes no earlier.
outside : ∀ r p q → inside r p ≡ false → p <ᵖ r ≡ false → q <ᵖ p ≡ false → inside r q ≡ false
outside r p q ip pr qp with inside r q in iq
... | false = refl
... | true with prefix-rest r q (inside-under r q iq)
...   | zs , refl with <ᵖ-split r p pr
...     | inj₂ refl with () ← trans (sym (inside-self r)) ip
...     | inj₁ rp with <ᵖ-split p (r ++ zs) qp
...       | inj₂ refl with () ← trans (sym iq) ip
...       | inj₁ pq with <ᵖ-between r p zs rp pq
...         | ws , refl with () ← trans (sym (inside-++ r r ws (inside-self r))) ip

after-before : ∀ {B} q (e : Events B) → After q (head e) → M′.before q e ≡ true
after-before q (out k a r) a′ = a′
after-before q (skip k r)  a′ = a′
after-before q (end k)     a′ = a′
after-before q hush        a′ = refl

private
  before-after : ∀ {B} q (e : Events B) → M′.before q e ≡ true → After q (head e)
  before-after q (out _ _ _) b = b
  before-after q (skip _ _)  b = b
  before-after q (end _)     b = b
  before-after q hush        b = tt

  nb-atop : ∀ {A p} (e : Events A) → NotBefore p (head e) → Atop p e
  nb-atop (out _ _ _) n = n
  nb-atop (skip _ _)  n = n
  nb-atop (end _)     n = n
  nb-atop hush        n = tt

  atopT-tnb : ∀ {p} t → AtopT p t → TailNotBefore p t
  atopT-tnb (pin _ _) a = a
  atopT-tnb idle      a = tt

  tnb-head : ∀ {A p} t → TailNotBefore p t → NotBefore p (head (tailᴱ {A} t))
  tnb-head (pin _ _) o = o
  tnb-head idle      o = tt

  -- Hushed and trailing, it leaves nothing running.
  hush-idle : ∀ {A} t → Trail {A} hush t → t ≡ idle
  hush-idle (pin _ _) tr with () ← proj₁ (everyᵀ (proj₁ (proj₂ (trail tr))))
  hush-idle idle      tr = refl

  lead-hushed : ∀ {A} {x y : Events A} → Lead⁼ x y → x ≡ hush → y ≡ hush
  lead-hushed hushᴸ refl = refl

  before-lead : ∀ {A} q {x y : Events A} → Lead⁼ x y → M′.before q x ≡ M′.before q y
  before-lead q outᴸ  = refl
  before-lead q skipᴸ = refl
  before-lead q endᴸ  = refl
  before-lead q hushᴸ = refl

-- What a run left past its end leaves, erased, as a run.
tail-erase : ∀ {A k} {t t′ : Tail} → Eraseᵀ k t t′ → Erase {A} k (tailᴱ t) t′ (tailᴱ t′)
tail-erase stopᵉ                 = stopᵉ
tail-erase (pinᵉ e)              = skipᵉ e (tail-erase e)
tail-erase (unpin {r = t′} o e)  = erased (tnb-head t′ o) e (tail-erase e)
tail-erase idleᵉ                 = hushᵉ

------------------------------------------------------------------------
-- The burst, erased

module _ (r : Pos) where
  open Bursting r using (atopT-run)

  private
    -- Under none of it, it runs on as left.
    run-outside : ∀ {A p} (e : Events A) t → inside r p ≡ false → p <ᵖ r ≡ false → NotBefore p (head e) → M′.runOn r e t ≡ t
    run-outside {p = p} (out q _ _) t ip pr n rewrite outside r p q ip pr n = refl
    run-outside {p = p} (skip q _)  t ip pr n rewrite outside r p q ip pr n = refl
    run-outside (end _) t ip pr n = refl
    run-outside hush    t ip pr n = refl

    atopT-end : ∀ {A} c t → c <ᵖ r ≡ false → EveryT (TrailE {A} (end c)) t → AtopT r t
    atopT-end c (pin k _) a ev = ≮-trans r c k a (<ᵖ-asym c k (proj₁ (proj₁ (everyᵀ ev))))
    atopT-end c idle      a ev = tt

  -- THE BURST, ERASED: a pin erased is a step erased under the
  -- subscription, no later than what the other pins next.
  run-erase : ∀ {A k} {x y : Events A} {cL t} → Atop r x → Ordered x → Trail y t → Eraseᵀ k cL t → Erase k x t y
            → Eraseᵀ k (M′.runOn r x cL) (M′.runOn r y t)
  run-erase a o tr c stopᵉ = stopᵉ
  run-erase {k = suc k} {cL = cL} {t} a o tr c (outᵉ {p = p} {l = l} {r = l′} et ex) =
    kept (inside r p) (run-erase (atop-weaken p r (force l) a (proj₁ (ordered o))) (proj₂ (ordered o)) (proj₁ (proj₂ (proj₂ (trail tr)))) et ex)
    where
      kept : ∀ b → Eraseᵀ k (M′.burstOn r l) (M′.burstOn r l′) → Eraseᵀ (suc k) (M′.pinned r p l cL b) (M′.pinned r p l′ t b)
      kept true  e = pinᵉ e
      kept false e = c
  run-erase {k = suc k} {cL = cL} {t} a o tr c (skipᵉ {p = p} {l = l} {r = l′} et ex) =
    kept (inside r p) (run-erase (atop-weaken p r (force l) a (proj₁ (ordered o))) (proj₂ (ordered o)) (proj₂ (proj₂ (trail tr))) et ex)
    where
      kept : ∀ b → Eraseᵀ k (M′.burstOn r l) (M′.burstOn r l′) → Eraseᵀ (suc k) (M′.pinned r p l cL b) (M′.pinned r p l′ t b)
      kept true  e = pinᵉ e
      kept false e = c
  run-erase {k = k} {y = y} {cL} {t} a o tr c (erased {p = p} {l = l} n et ex) =
    gone (inside r p) refl (run-erase (atop-weaken p r (force l) a (proj₁ (ordered o))) (proj₂ (ordered o)) tr et ex)
    where
      gone : ∀ b → inside r p ≡ b → Eraseᵀ k (M′.burstOn r l) (M′.runOn r y t) → Eraseᵀ k (M′.pinned r p l cL b) (M′.runOn r y t)
      gone true  ib e = unpin (atopT-tnb (M′.runOn r y t) (atopT-run p y t (nb-atop y n) tr ib)) e
      gone false ib e = subst (Eraseᵀ k cL) (sym (run-outside y t ib a n)) c
  run-erase a o tr c endᵉ  = c
  run-erase a o tr c hushᵉ = c

  burst-erase : ∀ {A k} {σ σ′ : Events∞ A} → Sourced r σ → Trailing σ′ → Eraseˢ k σ σ′ → Eraseᵀ k (M′.burstOn r σ) (M′.burstOn r σ′)
  burst-erase (sourced a o _) tr (c ,ᵉ x) = run-erase a o tr c x

  ------------------------------------------------------------------------
  -- Past the source's step

  private
    sourced-at : ∀ {X} {σ : Events∞ X} x → Sourced r σ → Atop r x → Ordered x → Trail x (cut σ) → Sourced r (M′.onward∞ σ x)
    sourced-at (out p _ l) so a o t = sourced (atop-weaken p r (force l) a (proj₁ (ordered o))) (proj₂ (ordered o)) (proj₁ (proj₂ (proj₂ (trail t))))
    sourced-at (skip p l)  so a o t = sourced (atop-weaken p r (force l) a (proj₁ (ordered o))) (proj₂ (ordered o)) (proj₂ (proj₂ (trail t)))
    sourced-at {X} {σ} (end c) so a o t =
      sourced (atop-tailᴱ r (cut σ) (atopT-end {X} c (cut σ) a (proj₁ (proj₂ (trail t))))) (ordered-tail (cut σ) (proj₁ (trail t)))
        (trail-tail (cut σ) (proj₁ (trail t)) (trailᶠ t))
    sourced-at hush so a o t = so

    sourced-on : ∀ {X} {σ : Events∞ X} → Sourced r σ → Sourced r (M′.onward∞ σ (force σ))
    sourced-on {σ = σ} so@(sourced a o t) = sourced-at (force σ) so a o t

    trailing-at : ∀ {X} {σ : Events∞ X} x → Trailing σ → Trail x (cut σ) → Trailing (M′.onward∞ σ x)
    trailing-at (out _ _ _) tσ t = proj₁ (proj₂ (proj₂ (trail t)))
    trailing-at (skip _ _)  tσ t = proj₂ (proj₂ (trail t))
    trailing-at {σ = σ} (end _) tσ t = trail-tail (cut σ) (proj₁ (trail t)) (trailᶠ t)
    trailing-at hush        tσ t = tσ

    trailing-on : ∀ {X} {σ : Events∞ X} → Trailing σ → Trailing (M′.onward∞ σ (force σ))
    trailing-on {σ = σ} t = trailing-at (force σ) t t

    onward-≡ : ∀ {X n} {σ σ′ : Events∞ X} {x x′} → force σ ≡ x → force σ′ ≡ x′ → Eraseˢ n (M′.onward∞ σ x) (M′.onward∞ σ′ x′)
             → Eraseˢ n (M′.onward∞ σ (force σ)) (M′.onward∞ σ′ (force σ′))
    onward-≡ {n = n} {σ} {σ′} eq eq′ e = subst₂ (Eraseˢ n) (cong (M′.onward∞ σ) (sym eq)) (cong (M′.onward∞ σ′) (sym eq′)) e

    gone-on : ∀ {X n p} {σ σ′ : Events∞ X} {l x′} → force σ ≡ skip p l → force σ′ ≡ x′ → Eraseᵀ n (cut l) (cut σ′)
            → Erase n (force l) (cut σ′) x′ → Eraseˢ n (M′.onward∞ σ (force σ)) σ′
    gone-on {n = n} {σ = σ} {σ′} {l} eq eq′ et ex =
      subst (λ z → Eraseˢ n (M′.onward∞ σ z) σ′) (sym eq) (et ,ᵉ subst (Erase n (force l) (cut σ′)) (sym eq′) ex)

  -- A hushed source bursts nothing.
  burst-hush : ∀ {X} {σ : Events∞ X} → force σ ≡ hush → M′.burstOn r σ ≡ cut σ
  burst-hush {σ = σ} eq = cong (λ z → M′.runOn r z (cut σ)) eq

  burst-hushed : ∀ {X} {σ : Events∞ X} → Trailing σ → force σ ≡ hush → M′.burstOn r σ ≡ idle
  burst-hushed {X} {σ} tr eq = trans (burst-hush {σ = σ} eq) (hush-idle {X} (cut σ) (subst (λ z → Trail z (cut σ)) eq tr))

  ------------------------------------------------------------------------
  -- The source's step and the body's

  private
    head-body : ∀ {X B} (σ : Events∞ X) q (e : Events B) → head (M′.body r σ q e) ≡ head e
    head-body σ q (out _ _ _) = refl
    head-body σ q (skip _ _)  = refl
    head-body σ q (end _)     = refl
    head-body σ q hush        = refl

    head-ahead : ∀ {X B k} (β : Events∞ B) (σ : Events∞ X) q b → NotBefore k (just q) → NotBefore k (head (force β))
               → NotBefore k (head (M′.ahead r β σ q b))
    head-ahead β σ q true  nq nb = nq
    head-ahead {k = k} β σ q false nq nb = subst (NotBefore k) (sym (head-body σ q (force β))) nb

    -- The body's next before the source's step, the body's shows.
    ahead-body : ∀ {X B} {β : Events∞ B} {σ : Events∞ X} {q b y} → force β ≡ y → M′.before q (force β) ≡ b → M′.before q y ≡ false
               → M′.ahead r β σ q b ≡ M′.body r σ q y
    ahead-body {q = q} {true} eq bq bf with () ← trans (sym bq) (trans (cong (M′.before q) eq) bf)
    ahead-body {β = β} {σ} {q} {false} eq bq bf = cong (M′.body r σ q) eq

  -- THE CONNECT, ERASED.
  mutual
    beside-erase : ∀ {X B n} {σ σ′ : Events∞ X} {β β′ : Events∞ B} → Sourced r σ → Trailing σ′ → Eraseˢ n σ σ′ → Eraseˢ n β β′
                 → Erase n (M′.beside r β σ) (M′.burstOn r σ′ ∪ cut β′) (M′.beside r β′ σ′)
    beside-erase {n = zero}  so tr es eb = stopᵉ
    beside-erase {n = suc n} {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} so tr es eb =
      side-erase {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} so tr es eb refl refl (nowᵉ es)

    side-erase : ∀ {X B n} {σ σ′ : Events∞ X} {β β′ : Events∞ B} {x x′} → Sourced r σ → Trailing σ′ → Eraseˢ (suc n) σ σ′
               → Eraseˢ (suc n) β β′ → force σ ≡ x → force σ′ ≡ x′ → Erase (suc n) x (cut σ′) x′
               → Erase (suc n) (M′.side r β σ x) (M′.burstOn r σ′ ∪ cut β′) (M′.side r β′ σ′ x′)
    side-erase {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} so tr es eb eq eq′ hushᵉ =
      subst (λ T → Erase _ (force β) (T ∪ cut β′) (force β′)) (sym (burst-hushed {σ = σ′} tr eq′)) (nowᵉ eb)
    side-erase {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} so tr es eb eq eq′ (outᵉ {p = p} et ex) =
      walkK {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} (p ++ [ ix 0 ]) refl refl (burst-erase so tr es) (sourced-on so) (trailing-on {σ = σ′} tr)
        (onward-≡ {σ = σ} {σ′ = σ′} eq eq′ (et ,ᵉ ex)) eb
    side-erase {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} so tr es eb eq eq′ (skipᵉ {p = p} et ex) =
      walkK {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} (p ++ [ ix 0 ]) refl refl (burst-erase so tr es) (sourced-on so) (trailing-on {σ = σ′} tr)
        (onward-≡ {σ = σ} {σ′ = σ′} eq eq′ (et ,ᵉ ex)) eb
    side-erase {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} so tr es eb eq eq′ (endᵉ {p = c}) =
      walkK {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} (c ++ [ ix 0 ]) refl refl (burst-erase so tr es) (sourced-on so) (trailing-on {σ = σ′} tr)
        (onward-≡ {σ = σ} {σ′ = σ′} eq eq′ (eraseᵀ-pred (cutᵉ es) ,ᵉ tail-erase (eraseᵀ-pred (cutᵉ es)))) eb
    side-erase {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} so tr es eb eq eq′ (erased {p = p} {e = hush} o et ex) =
      subst (λ T → Erase _ _ (T ∪ cut β′) (force β′)) (sym bi)
        (walkH {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} (p ++ [ ix 0 ]) bi (λ {β″} → cong (M′.side r β″ σ′) eq′) refl (burst-erase so tr es)
          (sourced-on so) tr (gone-on {σ = σ} {σ′ = σ′} eq eq′ et ex) eb)
      where bi = burst-hushed {σ = σ′} tr eq′
    side-erase {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} so tr es eb eq eq′ (erased {p = p} {e = out h _ _} o et ex) =
      walkA {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} (p ++ [ ix 0 ]) (h ++ [ ix 0 ]) (<ᵖ-shift h p o) (λ {β″} → cong (M′.side r β″ σ′) eq′) refl refl
        (burst-erase so tr es) (sourced-on so) tr (gone-on {σ = σ} {σ′ = σ′} eq eq′ et ex) eb
    side-erase {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} so tr es eb eq eq′ (erased {p = p} {e = skip h _} o et ex) =
      walkA {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} (p ++ [ ix 0 ]) (h ++ [ ix 0 ]) (<ᵖ-shift h p o) (λ {β″} → cong (M′.side r β″ σ′) eq′) refl refl
        (burst-erase so tr es) (sourced-on so) tr (gone-on {σ = σ} {σ′ = σ′} eq eq′ et ex) eb
    side-erase {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} so tr es eb eq eq′ (erased {p = p} {e = end h} o et ex) =
      walkA {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} (p ++ [ ix 0 ]) (h ++ [ ix 0 ]) (<ᵖ-shift h p o) (λ {β″} → cong (M′.side r β″ σ′) eq′) refl refl
        (burst-erase so tr es) (sourced-on so) tr (gone-on {σ = σ} {σ′ = σ′} eq eq′ et ex) eb

    -- A source step kept, shown at `q` on both sides.
    walkK : ∀ {X B m} {σ σ′ : Events∞ X} {β β′ : Events∞ B} q {b b′} → M′.before q (force β) ≡ b → M′.before q (force β′) ≡ b′
          → Eraseᵀ (suc m) (M′.burstOn r σ) (M′.burstOn r σ′) → Sourced r (M′.onward∞ σ (force σ)) → Trailing (M′.onward∞ σ′ (force σ′))
          → Eraseˢ m (M′.onward∞ σ (force σ)) (M′.onward∞ σ′ (force σ′)) → Eraseˢ (suc m) β β′
          → Erase (suc m) (M′.ahead r β σ q b) (M′.burstOn r σ′ ∪ cut β′) (M′.ahead r β′ σ′ q b′)
    walkK {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} q {true} {true} bq bq′ bu so tr oe eb =
      skipᵉ (∪-erase (burst-erase so tr oe) (eraseᵀ-pred (cutᵉ eb)))
        (beside-erase {σ = M′.onward∞ σ (force σ)} {σ′ = M′.onward∞ σ′ (force σ′)} {β = β} {β′ = β′} so tr oe (eraseˢ-pred eb))
    walkK {β = β} {β′ = β′} q {true} {false} bq bq′ bu so tr oe eb
      with () ← trans (sym (after-before q (force β′) (after-erase (nowᵉ eb) (before-after q (force β) bq)))) bq′
    walkK {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} q {false} bq bq′ bu so tr oe eb =
      bodyK {σ = σ} {σ′ = σ′} {β′ = β′} q refl bq′ bq bu so tr oe (nowᵉ eb)

    walk↓K : ∀ {X B m} {σ σ′ : Events∞ X} {β β′ : Events∞ B} q {b b′} → M′.before q (force β) ≡ b → M′.before q (force β′) ≡ b′
           → Eraseᵀ m (M′.burstOn r σ) (M′.burstOn r σ′) → Sourced r (M′.onward∞ σ (force σ)) → Trailing (M′.onward∞ σ′ (force σ′))
           → Eraseˢ m (M′.onward∞ σ (force σ)) (M′.onward∞ σ′ (force σ′)) → Eraseˢ m β β′
           → Erase m (M′.ahead r β σ q b) (M′.burstOn r σ′ ∪ cut β′) (M′.ahead r β′ σ′ q b′)
    walk↓K {m = zero}  q bq bq′ bu so tr oe eb = stopᵉ
    walk↓K {m = suc m} {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} q bq bq′ bu so tr oe eb =
      walkK {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} q bq bq′ bu so tr (eraseˢ-pred oe) eb

    bodyK : ∀ {X B m} {σ σ′ : Events∞ X} {β′ : Events∞ B} q {b′ y y′} → force β′ ≡ y′ → M′.before q (force β′) ≡ b′ → M′.before q y ≡ false
          → Eraseᵀ (suc m) (M′.burstOn r σ) (M′.burstOn r σ′) → Sourced r (M′.onward∞ σ (force σ)) → Trailing (M′.onward∞ σ′ (force σ′))
          → Eraseˢ m (M′.onward∞ σ (force σ)) (M′.onward∞ σ′ (force σ′)) → Erase (suc m) y (cut β′) y′
          → Erase (suc m) (M′.body r σ q y) (M′.burstOn r σ′ ∪ cut β′) (M′.ahead r β′ σ′ q b′)
    bodyK {σ = σ} {σ′ = σ′} {β′ = β′} q eq bq′ bf bu so tr oe (outᵉ {l = β₁} {r = β₁′} et ex) =
      subst (Erase _ _ _) (sym (ahead-body {β = β′} {σ = σ′} {q = q} eq bq′ bf))
        (outᵉ (∪-erase (eraseᵀ-pred bu) et) (walk↓K {σ = σ} {σ′ = σ′} {β = β₁} {β′ = β₁′} q refl refl (eraseᵀ-pred bu) so tr oe (et ,ᵉ ex)))
    bodyK {σ = σ} {σ′ = σ′} {β′ = β′} q eq bq′ bf bu so tr oe (skipᵉ {l = β₁} {r = β₁′} et ex) =
      subst (Erase _ _ _) (sym (ahead-body {β = β′} {σ = σ′} {q = q} eq bq′ bf))
        (skipᵉ (∪-erase (eraseᵀ-pred bu) et) (walk↓K {σ = σ} {σ′ = σ′} {β = β₁} {β′ = β₁′} q refl refl (eraseᵀ-pred bu) so tr oe (et ,ᵉ ex)))
    bodyK {σ′ = σ′} {β′ = β′} q eq bq′ bf bu so tr oe endᵉ = subst (Erase _ _ _) (sym (ahead-body {β = β′} {σ = σ′} {q = q} eq bq′ bf)) endᵉ
    bodyK q eq bq′ () bu so tr oe hushᵉ
    bodyK {σ = σ} {σ′ = σ′} {β′ = β′} q {b′} eq bq′ bf bu so tr oe (erased {p = k} {l = β₁} o et ex) =
      erased (head-ahead β′ σ′ q b′ bf (subst (λ z → NotBefore k (head z)) (sym eq) o)) (∪-erase (eraseᵀ-pred bu) et)
        (walk↓K {σ = σ} {σ′ = σ′} {β = β₁} {β′ = β′} q refl bq′ (eraseᵀ-pred bu) so tr oe (et ,ᵉ subst (Erase _ (force β₁) (cut β′)) (sym eq) ex))

    -- A source step erased, the other's at `q′` at or past it.
    walkA : ∀ {X B m} {σ σ′ : Events∞ X} {β β′ : Events∞ B} q q′ {b b′} → q′ <ᵖ q ≡ false
          → (∀ {β″ : Events∞ B} → M′.beside r β″ σ′ ≡ M′.ahead r β″ σ′ q′ (M′.before q′ (force β″)))
          → M′.before q (force β) ≡ b → M′.before q′ (force β′) ≡ b′
          → Eraseᵀ (suc m) (M′.burstOn r σ) (M′.burstOn r σ′) → Sourced r (M′.onward∞ σ (force σ)) → Trailing σ′
          → Eraseˢ m (M′.onward∞ σ (force σ)) σ′ → Eraseˢ (suc m) β β′
          → Erase (suc m) (M′.ahead r β σ q b) (M′.burstOn r σ′ ∪ cut β′) (M′.ahead r β′ σ′ q′ b′)
    walkA {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} q q′ {true} {b′} qq′ sa bq bq′ bu so tr oe eb =
      erased (head-ahead β′ σ′ q′ b′ qq′ (after-nb (head (force β′)) (after-erase (nowᵉ eb) (before-after q (force β) bq))))
        (∪-erase (burst-erase so tr oe) (eraseᵀ-pred (cutᵉ eb)))
        (subst (Erase _ _ _) (trans (sa {β′}) (cong (M′.ahead r β′ σ′ q′) bq′))
          (beside-erase {σ = M′.onward∞ σ (force σ)} {σ′ = σ′} {β = β} {β′ = β′} so tr oe (eraseˢ-pred eb)))
    walkA {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} q q′ {false} qq′ sa bq bq′ bu so tr oe eb =
      bodyA {σ = σ} {σ′ = σ′} {β′ = β′} q q′ qq′ sa refl bq′ bq bu so tr oe (nowᵉ eb)

    walk↓A : ∀ {X B m} {σ σ′ : Events∞ X} {β β′ : Events∞ B} q q′ {b b′} → q′ <ᵖ q ≡ false
           → (∀ {β″ : Events∞ B} → M′.beside r β″ σ′ ≡ M′.ahead r β″ σ′ q′ (M′.before q′ (force β″)))
           → M′.before q (force β) ≡ b → M′.before q′ (force β′) ≡ b′
           → Eraseᵀ m (M′.burstOn r σ) (M′.burstOn r σ′) → Sourced r (M′.onward∞ σ (force σ)) → Trailing σ′
           → Eraseˢ m (M′.onward∞ σ (force σ)) σ′ → Eraseˢ m β β′
           → Erase m (M′.ahead r β σ q b) (M′.burstOn r σ′ ∪ cut β′) (M′.ahead r β′ σ′ q′ b′)
    walk↓A {m = zero}  q q′ qq′ sa bq bq′ bu so tr oe eb = stopᵉ
    walk↓A {m = suc m} {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} q q′ qq′ sa bq bq′ bu so tr oe eb =
      walkA {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} q q′ qq′ sa bq bq′ bu so tr (eraseˢ-pred oe) eb

    bodyA : ∀ {X B m} {σ σ′ : Events∞ X} {β′ : Events∞ B} q q′ {b′ y y′} → q′ <ᵖ q ≡ false
          → (∀ {β″ : Events∞ B} → M′.beside r β″ σ′ ≡ M′.ahead r β″ σ′ q′ (M′.before q′ (force β″)))
          → force β′ ≡ y′ → M′.before q′ (force β′) ≡ b′ → M′.before q y ≡ false
          → Eraseᵀ (suc m) (M′.burstOn r σ) (M′.burstOn r σ′) → Sourced r (M′.onward∞ σ (force σ)) → Trailing σ′
          → Eraseˢ m (M′.onward∞ σ (force σ)) σ′ → Erase (suc m) y (cut β′) y′
          → Erase (suc m) (M′.body r σ q y) (M′.burstOn r σ′ ∪ cut β′) (M′.ahead r β′ σ′ q′ b′)
    bodyA {σ = σ} {σ′ = σ′} {β′ = β′} q q′ qq′ sa eq bq′ bf bu so tr oe (outᵉ {p = k} {l = β₁} {r = β₁′} et ex) =
      subst (Erase _ _ _) (sym (ahead-body {β = β′} {σ = σ′} {q = q′} eq bq′ (≮-trans k q q′ bf qq′)))
        (outᵉ (∪-erase (eraseᵀ-pred bu) et) (walk↓A {σ = σ} {σ′ = σ′} {β = β₁} {β′ = β₁′} q q′ qq′ sa refl refl (eraseᵀ-pred bu) so tr oe (et ,ᵉ ex)))
    bodyA {σ = σ} {σ′ = σ′} {β′ = β′} q q′ qq′ sa eq bq′ bf bu so tr oe (skipᵉ {p = k} {l = β₁} {r = β₁′} et ex) =
      subst (Erase _ _ _) (sym (ahead-body {β = β′} {σ = σ′} {q = q′} eq bq′ (≮-trans k q q′ bf qq′)))
        (skipᵉ (∪-erase (eraseᵀ-pred bu) et) (walk↓A {σ = σ} {σ′ = σ′} {β = β₁} {β′ = β₁′} q q′ qq′ sa refl refl (eraseᵀ-pred bu) so tr oe (et ,ᵉ ex)))
    bodyA {σ′ = σ′} {β′ = β′} q q′ qq′ sa eq bq′ bf bu so tr oe (endᵉ {p = c}) =
      subst (Erase _ _ _) (sym (ahead-body {β = β′} {σ = σ′} {q = q′} eq bq′ (≮-trans c q q′ bf qq′))) endᵉ
    bodyA q q′ qq′ sa eq bq′ () bu so tr oe hushᵉ
    bodyA {σ = σ} {σ′ = σ′} {β′ = β′} q q′ {b′} qq′ sa eq bq′ bf bu so tr oe (erased {p = k} {l = β₁} o et ex) =
      erased (head-ahead β′ σ′ q′ b′ (≮-trans k q q′ bf qq′) (subst (λ z → NotBefore k (head z)) (sym eq) o)) (∪-erase (eraseᵀ-pred bu) et)
        (walk↓A {σ = σ} {σ′ = σ′} {β = β₁} {β′ = β′} q q′ qq′ sa refl bq′ (eraseᵀ-pred bu) so tr oe
          (et ,ᵉ subst (Erase _ (force β₁) (cut β′)) (sym eq) ex))

    -- A source step erased, the other's source hushed.
    walkH : ∀ {X B m} {σ σ′ : Events∞ X} {β β′ : Events∞ B} q {b} → M′.burstOn r σ′ ≡ idle
          → (∀ {β″ : Events∞ B} → M′.beside r β″ σ′ ≡ force β″) → M′.before q (force β) ≡ b
          → Eraseᵀ (suc m) (M′.burstOn r σ) (M′.burstOn r σ′) → Sourced r (M′.onward∞ σ (force σ)) → Trailing σ′
          → Eraseˢ m (M′.onward∞ σ (force σ)) σ′ → Eraseˢ (suc m) β β′
          → Erase (suc m) (M′.ahead r β σ q b) (cut β′) (force β′)
    walkH {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} q {true} bi sh bq bu so tr oe eb =
      erased (after-nb (head (force β′)) (after-erase (nowᵉ eb) (before-after q (force β) bq)))
        (subst (λ T → Eraseᵀ _ _ (T ∪ cut β′)) bi (∪-erase (burst-erase so tr oe) (eraseᵀ-pred (cutᵉ eb))))
        (subst₂ (Erase _ _) (cong (_∪ cut β′) bi) (sh {β′})
          (beside-erase {σ = M′.onward∞ σ (force σ)} {σ′ = σ′} {β = β} {β′ = β′} so tr oe (eraseˢ-pred eb)))
    walkH {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} q {false} bi sh bq bu so tr oe eb =
      bodyH {σ = σ} {σ′ = σ′} {β′ = β′} q bi sh refl bq bu so tr oe (nowᵉ eb)

    walk↓H : ∀ {X B m} {σ σ′ : Events∞ X} {β β′ : Events∞ B} q {b} → M′.burstOn r σ′ ≡ idle
           → (∀ {β″ : Events∞ B} → M′.beside r β″ σ′ ≡ force β″) → M′.before q (force β) ≡ b
           → Eraseᵀ m (M′.burstOn r σ) (M′.burstOn r σ′) → Sourced r (M′.onward∞ σ (force σ)) → Trailing σ′
           → Eraseˢ m (M′.onward∞ σ (force σ)) σ′ → Eraseˢ m β β′
           → Erase m (M′.ahead r β σ q b) (cut β′) (force β′)
    walk↓H {m = zero}  q bi sh bq bu so tr oe eb = stopᵉ
    walk↓H {m = suc m} {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} q bi sh bq bu so tr oe eb =
      walkH {σ = σ} {σ′ = σ′} {β = β} {β′ = β′} q bi sh bq bu so tr (eraseˢ-pred oe) eb

    bodyH : ∀ {X B m} {σ σ′ : Events∞ X} {β′ : Events∞ B} q {y y′} → M′.burstOn r σ′ ≡ idle
          → (∀ {β″ : Events∞ B} → M′.beside r β″ σ′ ≡ force β″) → force β′ ≡ y′ → M′.before q y ≡ false
          → Eraseᵀ (suc m) (M′.burstOn r σ) (M′.burstOn r σ′) → Sourced r (M′.onward∞ σ (force σ)) → Trailing σ′
          → Eraseˢ m (M′.onward∞ σ (force σ)) σ′ → Erase (suc m) y (cut β′) y′
          → Erase (suc m) (M′.body r σ q y) (cut β′) y′
    bodyH {σ = σ} {σ′ = σ′} q bi sh eq bf bu so tr oe (outᵉ {l = β₁} {r = β₁′} et ex) =
      outᵉ (subst (λ T → Eraseᵀ _ _ (T ∪ cut β₁′)) bi (∪-erase (eraseᵀ-pred bu) et))
        (walk↓H {σ = σ} {σ′ = σ′} {β = β₁} {β′ = β₁′} q bi sh refl (eraseᵀ-pred bu) so tr oe (et ,ᵉ ex))
    bodyH {σ = σ} {σ′ = σ′} q bi sh eq bf bu so tr oe (skipᵉ {l = β₁} {r = β₁′} et ex) =
      skipᵉ (subst (λ T → Eraseᵀ _ _ (T ∪ cut β₁′)) bi (∪-erase (eraseᵀ-pred bu) et))
        (walk↓H {σ = σ} {σ′ = σ′} {β = β₁} {β′ = β₁′} q bi sh refl (eraseᵀ-pred bu) so tr oe (et ,ᵉ ex))
    bodyH q bi sh eq bf bu so tr oe endᵉ = endᵉ
    bodyH q bi sh eq () bu so tr oe hushᵉ
    bodyH {σ = σ} {σ′ = σ′} {β′ = β′} q bi sh eq bf bu so tr oe (erased {l = β₁} o et ex) =
      erased o (subst (λ T → Eraseᵀ _ _ (T ∪ cut β′)) bi (∪-erase (eraseᵀ-pred bu) et))
        (subst (Erase _ _ _) eq (walk↓H {σ = σ} {σ′ = σ′} {β = β₁} {β′ = β′} q bi sh refl (eraseᵀ-pred bu) so tr oe
          (et ,ᵉ subst (Erase _ (force β₁) (cut β′)) (sym eq) ex)))

  ------------------------------------------------------------------------
  -- The same next

  private
    body-lead : ∀ {X B} {σ σ′ : Events∞ X} q {x y : Events B} → Lead⁼ x y → Lead⁼ (M′.body r σ q x) (M′.body r σ′ q y)
    body-lead q outᴸ  = outᴸ
    body-lead q skipᴸ = skipᴸ
    body-lead q endᴸ  = endᴸ
    body-lead q hushᴸ = hushᴸ

    ahead-lead : ∀ {X B} {σ σ′ : Events∞ X} {β β′ : Events∞ B} q b → Lead⁼ (force β) (force β′)
               → Lead⁼ (M′.ahead r β σ q b) (M′.ahead r β′ σ′ q b)
    ahead-lead q true  l = skipᴸ
    ahead-lead {σ = σ} {σ′} q false l = body-lead {σ = σ} {σ′} q l

    shown-lead : ∀ {X B} {σ σ′ : Events∞ X} {β β′ : Events∞ B} q → Lead⁼ (force β) (force β′)
               → Lead⁼ (M′.ahead r β σ q (M′.before q (force β))) (M′.ahead r β′ σ′ q (M′.before q (force β′)))
    shown-lead {σ = σ} {σ′} {β} {β′} q l rewrite before-lead q l = ahead-lead {σ = σ} {σ′} {β} {β′} q (M′.before q (force β′)) l

  side-lead : ∀ {X B} {σ σ′ : Events∞ X} {β β′ : Events∞ B} {x x′} → Lead⁼ x x′ → Lead⁼ (force β) (force β′)
            → Lead⁼ (M′.side r β σ x) (M′.side r β′ σ′ x′)
  side-lead {σ = σ} {σ′} {β} {β′} (outᴸ {p = q}) l = shown-lead {σ = σ} {σ′} {β} {β′} (q ++ [ ix 0 ]) l
  side-lead {σ = σ} {σ′} {β} {β′} (skipᴸ {p = q}) l = shown-lead {σ = σ} {σ′} {β} {β′} (q ++ [ ix 0 ]) l
  side-lead {σ = σ} {σ′} {β} {β′} (endᴸ {p = c}) l = shown-lead {σ = σ} {σ′} {β} {β′} (c ++ [ ix 0 ]) l
  side-lead hushᴸ l = l

-- THE ERASURE, AT A CONNECT: a body and its source each fed a run with
-- skips erased run with skips erased, the next kept, the source fed one
-- subscribed where the connect is, and the run it is fed trailing too.
--
-- REFUTED: 71fa7920 without each premise of `Sourced`: a tail pinned
--   before an erased skip, an erased skip outside the burst between two
--   inside it, and an erased skip before the subscription.
-- REFUTED: f1f7d119 without the other's trail (`body-untrailed`): an
--   erased step spends depth, so infinitely many erased skips satisfy
--   every depth before a kept one that pins past them.  Nor does a run
--   with skips erased trail because the run does (`erase-untrailed`).
body-⊒ : ∀ {X B} r {σ σ′ : Events∞ X} {β β′ : Events∞ B} → Sourced r σ → Trailing σ′ → σ ⊒ σ′ → β ⊒ β′ → bodyConn r σ β ⊒ bodyConn r σ′ β′
body-⊒ r {σ} {σ′} {β} {β′} so tr (lσ , hσ , eσ) (lβ , hβ , eβ) =
  side-lead r {σ = σ} {σ′} {β} {β′} lσ lβ , hushed , λ n → ∪-erase (burst-erase r so tr (eσ n)) (cutᵉ (eβ n)) ,ᵉ beside-erase r so tr (eσ n) (eβ n)
  where
    hushed : M′.beside r β σ ≡ hush → ∀ d → Agreeᵀ d (M′.burstOn r σ ∪ cut β) (M′.burstOn r σ′ ∪ cut β′)
    hushed h d with side-hush r β σ (force σ) h
    ... | hs , hb = subst₂ (λ u u′ → Agreeᵀ d (u ∪ cut β) (u′ ∪ cut β′))
                      (sym (cong (λ z → M′.runOn r z (cut σ)) hs)) (sym (cong (λ z → M′.runOn r z (cut σ′)) (lead-hushed lσ hs)))
                      (∪-ne (hσ hs d) (hβ hb d))
