{-# OPTIONS --guardedness #-}

-- SCAN, LISTED EXACTLY: every fold `Scan.Acc` reaches, chained value by
-- value through the listed values.  A chain climbs strictly, so it is no
-- longer than the values before its last, and the listing's bound is
-- never what stops it.
module quickcheck.Tabled.Exact.Scan where

open import Data.List using (List; []; _∷_; [_]; length) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; suc; _<_; s≤s)
open import Data.Nat.Properties using (<-≤-trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import denotation.EmissionSet using (out; skip; end; EmissionSet)
import denotation.EmissionSet as Tb
open import quickcheck.Tabled using (Listed; rows; when; scanRows; module ScanL; module Order)
open import quickcheck.Tabled.Exact.Base
  using (Exact; Exactly; sound; complete; fromT; when⁻; when⁺; if⁻; if-t; single⁻; cm⁻; cm⁺; values⁻; values⁺;
  cnt; cnt≤; cnt-lt; module OrderX)

module ScanX {A B : Set} (f : B → A → B) (z : B) (t : EmissionSet A) (o : Listed A) (ex : Exact o t) where
  open Tb.Scan f z t using (Acc; acc₀; acc; ScanT; sval; sstep; send)
  open ScanL f z o using (vals; accs; prior; scanRow)
  open Order vals using (minᵇ; nextᵇ)
  open OrderX ex using (min→; →min; next→; →next)

  acc-s : ∀ n {q a b} → t q (out a) → b ∈ accs n q a → Acc q b
  acc-s zero x ()
  acc-s (suc n) {q} {a} x m with ∈-++⁻ (when (minᵇ q) (f z a)) m
  ... | inj₁ h with when⁻ h
  ... | (mn , refl) = acc₀ x (min→ mn)
  acc-s (suc n) {q} {a} x m | inj₂ h with cm⁻ {xs = vals} h
  ... | ((q₀ , a₀) , vm , h′) with if⁻ {b = nextᵇ q₀ q} h′
  ... | inj₂ (_ , ())
  ... | inj₁ (nx , h″) with ∈-map⁻ (λ b → f b a) h″
  ... | (b₀ , bm , refl) = acc (acc-s n (sound ex (values⁻ vm)) bm) x (proj₁ (next→ q₀ q nx)) (proj₂ (next→ q₀ q nx))

  -- A fold, with the value it ends at, listed by any bound past the
  -- values before it.
  acc-c : ∀ {q b} → Acc q b → Σ A λ a → t q (out a) × (∀ n → cnt q vals < n → b ∈ accs n q a)
  acc-c (acc₀ {q} {a} x mn) = a , x , λ { zero () ; (suc n) _ → ∈-++⁺ˡ (when⁺ (→min mn)) }
  acc-c (acc {q} {b} {q′} {a′} y x lt nx) with acc-c y
  ... | (a₀ , x₀ , k) = a′ , x , λ { zero () ; (suc n) (s≤s le) →
    let v₀ = values⁺ (complete ex x₀) in
    ∈-++⁺ʳ (when (minᵇ q′) (f z a′))
      (cm⁺ v₀ (if-t (→next q q′ lt nx) (∈-map⁺ (λ b → f b a′) (k n (<-≤-trans (cnt-lt v₀ (fromT lt)) le))))) }

  sound-s : ∀ {q e} → (q , e) ∈ rows (scanRows f z o) → ScanT q e
  sound-s m with cm⁻ {xs = rows o} m
  ... | ((k , out a) , km , h) with ∈-map⁻ (λ b → k , out b) h
  ... | (b , bm , refl) = sval (acc-s (suc (length vals)) (sound ex km) bm)
  sound-s m | ((k , skip) , km , h) with single⁻ h
  ... | refl = sstep (sound ex km)
  sound-s m | ((k , end) , km , h) with single⁻ h
  ... | refl = send (sound ex km)

  complete-s : ∀ {q e} → ScanT q e → (q , e) ∈ rows (scanRows f z o)
  complete-s (sval {q} y) with acc-c y
  ... | (a , x , k) = cm⁺ (complete ex x) (∈-map⁺ (λ b → q , out b) (k _ (s≤s (cnt≤ vals))))
  complete-s (sstep x) = cm⁺ (complete ex x) (here refl)
  complete-s (send x)  = cm⁺ (complete ex x) (here refl)

scan-exact : ∀ {A B} (f : B → A → B) (z : B) {t : EmissionSet A} (o : Listed A) → Exactly o t
  → Exactly (scanRows f z o) (Tb.Scan.ScanT f z t)
scan-exact f z {t} o eo u = record { sound = sound-s ; complete = complete-s }
  where open ScanX f z t o (eo u)
