-- WHICH SOURCE ROWS' FIRST CHILDREN A CONNECT SHOWS, decided: a burst
-- row wherever it lies in the subscription; an echo, or a kept pin,
-- wherever the body lives at it, or at its pin's subscription.  Liveness
-- and the bound are decidable stand-ins, so the decision is over
-- variables.
module simultaneous.ConnPick where

open import Data.Bool using (T; not)
open import Data.Empty using (⊥-elim)
open import Data.List using ([_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

open import denotation.Position using (Pos; _⊕_; inside; ix)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet)
open import simultaneous.ToldRows using (T-or; not-T)

module Pick {X Y : Set} (σ : EmissionSet X) (U : EmissionSet Y) (r : Pos)
            (P : Pos → Set) (P? : ∀ l → Dec (P l)) (Live : Pos → Set) (Live? : ∀ j → Dec (Live j))
            (burst : ∀ {k e} → σ k e → T (inside r k) → P (k ⊕ [ ix 0 ]) → Σ (Ev Y) (U (k ⊕ [ ix 0 ])))
            (echo  : ∀ {k e} → σ k e → Live k → Unpinned e → T (not (inside r k)) → P (k ⊕ [ ix 0 ]) → Σ (Ev Y) (U (k ⊕ [ ix 0 ])))
            (kept  : ∀ {k x} → σ k (pin x) → Live x → T (not (inside r k)) → T (inside x k) → P (k ⊕ [ ix 0 ]) → Σ (Ev Y) (U (k ⊕ [ ix 0 ])))
            where

  Row : Set
  Row = Maybe (Σ Pos λ l → Σ (Ev Y) (U l))

  echo′ : ∀ {k e} → σ k e → Unpinned e → T (not (inside r k)) → P (k ⊕ [ ix 0 ]) → Row
  echo′ {k} y up ni un with Live? k
  ... | yes lv = just (_ , echo y lv up ni un)
  ... | no _   = nothing

  kept′ : ∀ {k x} → σ k (pin x) → T (not (inside r k)) → T (inside x k) → P (k ⊕ [ ix 0 ]) → Row
  kept′ {k} {x} y ni ins un with Live? x
  ... | yes lv = just (_ , kept y lv ni ins un)
  ... | no _   = nothing

  quiet : ∀ {k} e → σ k e → T (not (inside r k)) → P (k ⊕ [ ix 0 ]) → Row
  quiet (out _)     y ni un = echo′ y tt ni un
  quiet skip        y ni un = echo′ y tt ni un
  quiet end         y ni un = echo′ y tt ni un
  quiet {k} (pin x) y ni un with T-or (inside x k)
  ... | inj₁ ins = kept′ y ni ins un
  ... | inj₂ _   = nothing

  loud : ∀ {k e} → σ k e → P (k ⊕ [ ix 0 ]) → Row
  loud {k} {e} y un with T-or (inside r k)
  ... | inj₁ i  = just (_ , burst y i un)
  ... | inj₂ ni = quiet e y ni un

  pick : ∀ {k e} → σ k e → Row
  pick {k} y with P? (k ⊕ [ ix 0 ])
  ... | yes un = loud y un
  ... | no _   = nothing

  Is : Pos → Row → Set
  Is l w = Σ (Σ (Ev Y) (U l)) λ v → w ≡ just (l , v)

  Picked : ∀ {k e} → σ k e → Set
  Picked {k} y = Is (k ⊕ [ ix 0 ]) (pick y)

  on-P : ∀ {k e} (y : σ k e) → P (k ⊕ [ ix 0 ]) → (∀ un → Is (k ⊕ [ ix 0 ]) (loud y un)) → Picked y
  on-P {k} y un f with P? (k ⊕ [ ix 0 ])
  ... | yes un′ = f un′
  ... | no ¬u   = ⊥-elim (¬u un)

  -- A burst row is picked.
  picked-burst : ∀ {k e} (y : σ k e) → P (k ⊕ [ ix 0 ]) → T (inside r k) → Picked y
  picked-burst {k} y un i = on-P y un go
    where
      go : ∀ un′ → Is (k ⊕ [ ix 0 ]) (loud y un′)
      go un′ with T-or (inside r k)
      ... | inj₁ _  = _ , refl
      ... | inj₂ ni = ⊥-elim (not-T ni i)

  -- An echo is picked where the body lives.
  picked-echo : ∀ {k e} (y : σ k e) → P (k ⊕ [ ix 0 ]) → Live k → Unpinned e → T (not (inside r k)) → Picked y
  picked-echo {k} {e} y un lv up ni = on-P y un go
    where
      ech : ∀ {e} (y : σ k e) (up : Unpinned e) ni′ un′ → Is (k ⊕ [ ix 0 ]) (echo′ y up ni′ un′)
      ech y up ni′ un′ with Live? k
      ... | yes _ = _ , refl
      ... | no ¬l = ⊥-elim (¬l lv)
      qu : ∀ e (y : σ k e) → Unpinned e → ∀ ni′ un′ → Is (k ⊕ [ ix 0 ]) (quiet e y ni′ un′)
      qu (out _) y up = ech y up
      qu skip    y up = ech y up
      qu end     y up = ech y up
      qu (pin _) y ()
      go : ∀ un′ → Is (k ⊕ [ ix 0 ]) (loud y un′)
      go un′ with T-or (inside r k)
      ... | inj₁ i   = ⊥-elim (not-T ni i)
      ... | inj₂ ni′ = qu e y up ni′ un′

  -- A kept pin is picked where the body lives at its subscription.
  picked-kept : ∀ {k x} (y : σ k (pin x)) → P (k ⊕ [ ix 0 ]) → Live x → T (not (inside r k)) → T (inside x k) → Picked y
  picked-kept {k} {x} y un lv ni ins = on-P y un go
    where
      kp : ∀ ni′ ins′ un′ → Is (k ⊕ [ ix 0 ]) (kept′ y ni′ ins′ un′)
      kp ni′ ins′ un′ with Live? x
      ... | yes _ = _ , refl
      ... | no ¬l = ⊥-elim (¬l lv)
      qu : ∀ ni′ un′ → Is (k ⊕ [ ix 0 ]) (quiet (pin x) y ni′ un′)
      qu ni′ un′ with T-or (inside x k)
      ... | inj₁ ins′ = kp ni′ ins′ un′
      ... | inj₂ nins = ⊥-elim (not-T nins ins)
      go : ∀ un′ → Is (k ⊕ [ ix 0 ]) (loud y un′)
      go un′ with T-or (inside r k)
      ... | inj₁ i   = ⊥-elim (not-T ni i)
      ... | inj₂ ni′ = qu ni′ un′
