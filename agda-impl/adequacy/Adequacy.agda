{-# OPTIONS --guardedness #-}

-- THE LINK.  The pure runtime and the denotation agree: the limit of the
-- machine's prefixes is the meaning, observed at the root, with positions
-- forgotten down to ticks.  The meaning is `denotation.Denote`'s fold; the
-- simulation is run against `denotation.Unfold`'s stepper, a proof device,
-- and `unfolded` carries its reading to the fold's: the stepper to its
-- configuration's meaning (`stepped`), that meaning to the fold's
-- (`denotation.Unfold.denoted`).
--
-- Both halves are read off one simulation between the machine's trace
-- and the events the root is shown (`Simulation`).  BELOW: every prefix's
-- record, positions and all, is placed against those events
-- (`operation.Placed`), so shows nothing they do not.  ABOVE: whatever
-- the meaning shows lies within some prefix, which shows the same.
module adequacy.Adequacy where

open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; Σ; proj₁; proj₂)

open import operation.Placed using (Up; ahead; framed; shows; placed-⊑)
open import operation.Machine using (module Machine)
open import operation.PureObservable using (PureObs)
open import adequacy.Simulation using (module Sim)
open import denotation.MonotonicList using (ML; MonotonicList; Events; Events∞; out; skip; end; hush; Agree; out⁼; skip⁼; end⁼; hush⁼;
  agree; agree-sym; _≈_; observe; root; ticks; inFrame; tick)
open import denotation.Order using (_⊑_; _≃_; Shows; ShowsIn; nil; at⁺; emit⁺; stall⁺; close⁺; limit; limit-ub; limit-least; shows-≼; shows-cmp; cmp-long)
open import denotation.Denote using (⟦_⟧)
open import Data.List.Relation.Unary.All using ([])
open import denotation.Unfold using ([]; unfold; subscribe; denoted) renaming (⟦_⟧ to ⟦_⟧ᵘ)
open import Data.Bool using (true; false)
open import Data.Nat using (suc; _<ᵇ_)

-- The pure run: the limit of the machine's prefixes.
run : ∀ {A} → PureObs [] A → ML A
run {A} o = limit λ n → Machine.prefix A n o

-- The stepper's run, as the run reports one.
meaning : ∀ {A} → PureObs [] A → ML A
meaning o = ticks (unfold (subscribe o root))

------------------------------------------------------------------------
-- Runs alike for any number of steps report the same

private
  Same : ∀ {A} → Events A → Events A → Set
  Same x y = ∀ k → Agree k x y

  data Twin {A : Set} : Events A → Events A → Set where
    outᵗ  : ∀ {p a l r} → Same (Events∞.force l) (Events∞.force r) → Twin (out p a l) (out p a r)
    skipᵗ : ∀ {p l r} → Same (Events∞.force l) (Events∞.force r) → Twin (skip p l) (skip p r)
    endᵗ  : ∀ {p} → Twin (end p) (end p)
    hushᵗ : Twin hush hush

  out-rest : ∀ {A k p q} {a b : A} {l r} → Agree (suc k) (out p a l) (out q b r) → Agree k (Events∞.force l) (Events∞.force r)
  out-rest (out⁼ x) = x

  skip-rest : ∀ {A k p q} {l r : Events∞ A} → Agree (suc k) (skip p l) (skip q r) → Agree k (Events∞.force l) (Events∞.force r)
  skip-rest (skip⁼ x) = x

  twin : ∀ {A} {x y : Events A} → Same x y → Twin x y
  twin s with s 1
  ... | out⁼ _  = outᵗ λ k → out-rest (s (suc k))
  ... | skip⁼ _ = skipᵗ λ k → skip-rest (s (suc k))
  ... | end⁼    = endᵗ
  ... | hush⁼   = hushᵗ

  mutual
    shows-twin : ∀ {A} {x y : Events A} → Twin x y → ∀ {is} → Shows (ticks x) is → Shows (ticks y) is
    shows-twin (outᵗ s)  nil              = nil
    shows-twin (outᵗ s)  (at⁺ nil)        = at⁺ nil
    shows-twin (outᵗ s)  (at⁺ (emit⁺ sh)) = at⁺ (emit⁺ (in-twin (twin s) sh))
    shows-twin (skipᵗ s) nil              = nil
    shows-twin (skipᵗ s) (at⁺ nil)        = at⁺ nil
    shows-twin (skipᵗ s) (at⁺ (stall⁺ sh)) = at⁺ (stall⁺ (in-twin (twin s) sh))
    shows-twin endᵗ      sh               = sh
    shows-twin hushᵗ     sh               = sh

    in-twin : ∀ {A t} {x y : Events A} → Twin x y → ∀ {is} → ShowsIn t (inFrame t x) is → ShowsIn t (inFrame t y) is
    in-twin {t = t} (outᵗ {p = p} s) sh with tick p <ᵇ suc t
    in-twin (outᵗ s) nil           | true  = nil
    in-twin (outᵗ s) (emit⁺ sh)    | true  = emit⁺ (in-twin (twin s) sh)
    in-twin (outᵗ s) nil           | false = nil
    in-twin (outᵗ s) (close⁺ sh)   | false = close⁺ (shows-twin (outᵗ s) sh)
    in-twin {t = t} (skipᵗ {p = p} s) sh with tick p <ᵇ suc t
    in-twin (skipᵗ s) nil          | true  = nil
    in-twin (skipᵗ s) (stall⁺ sh)  | true  = stall⁺ (in-twin (twin s) sh)
    in-twin (skipᵗ s) nil          | false = nil
    in-twin (skipᵗ s) (close⁺ sh)  | false = close⁺ (shows-twin (skipᵗ s) sh)
    in-twin endᵗ  sh = sh
    in-twin hushᵗ sh = sh

-- The same meaning reports the same run, wherever it is subscribed.
ticks-≈ : ∀ {A} {x y : MonotonicList A} → x ≈ y → ∀ p → ticks (observe x p) ≃ ticks (observe y p)
ticks-≈ xy p = shows-twin (twin λ k → agree (xy k) p) , shows-twin (twin λ k → agree-sym (agree (xy k) p))

module Link (R : Set) where
  open Machine R using (prefix; reading; trace; begin; Read)
  open Sim R using (sim; placed; got)
  open Read

  postulate
    -- The meaning's ticks never fall.
    --
    -- RECOVERY: `git show a2e0bb8b` restores `<ᵖ-trans`, `<ᵖ-irrefl` and
    --   `<ᵖ-ix` in `denotation.MonotonicList`: positions strictly ordered,
    --   and an earlier one at no later a tick.
    ticks-up : (o : PureObs [] R) → Up 0 (unfold (subscribe o root))

  -- THE UPPER HALF: whatever the meaning shows, some prefix shows.  It
  -- shows as many items, and they are the meaning's.
  reaches : (o : PureObs [] R) → ∀ {is} → Shows (meaning o) is → Σ ℕ λ n → Shows (prefix n o) is
  reaches o s with got 0 (ahead s) (sim o)
  ... | n , long = n , shows-≼ (cmp-long (shows-cmp s (shows (ticks-up o) (placed n 0 (sim o)))) long) (framed (log r) (ending r))
    where r = reading n 0 (trace (begin o))

  -- Each prefix is below the meaning.
  complete : (o : PureObs [] R) (n : ℕ) → prefix n o ⊑ meaning o
  complete o n = placed-⊑ (ticks-up o) (placed n 0 (sim o))

postulate
  -- The stepper shows what its configuration means: each value at its
  -- tick, in order, then completion or silence.  Every node's step is its
  -- operator's stream function taken one event at a time, but at a
  -- `connect`: the stepper feeds its joiners from the source as it runs,
  -- where the meaning hands each joiner the source's whole run, rejoined.
  stepped : ∀ {A} (o : PureObs [] A) → meaning o ≃ ticks (observe (⟦ o ⟧ᵘ []) root)

-- The stepper and the fold show the same.
unfolded : ∀ {A} (o : PureObs [] A) → meaning o ≃ ticks (observe (⟦ o ⟧ []) root)
unfolded o = (λ s → proj₁ d (proj₁ (stepped o) s)) , λ s → proj₂ (stepped o) (proj₂ d s)
  where d = ticks-≈ (denoted o) root

adequacy : ∀ {A} (o : PureObs [] A) → run o ≃ ticks (observe (⟦ o ⟧ []) root)
adequacy {A} o = (λ s → proj₁ (unfolded o) (limit-least (prefix-chain o) (complete o) s))
               , λ s → limit-ub (prefix-chain o) (proj₁ (reaches o (proj₂ (unfolded o) s))) (proj₂ (reaches o (proj₂ (unfolded o) s)))
  where open Link A
        open Sim A using (prefix-chain)
