-- ══════════════════════════════════════════════════════════════════
-- THE ENTRY FOLD DIES AT A SCRIPT, AND THE AXIS IS THE INSTANT'S WIDTH.
--
-- REFUTATION, not a claim: this file STATES the proposition and derives
-- `⊥` from it.  Checked by `make refuted`, claimed by `Refuted.Main`.
--
-- WHAT IS REFUTED.  The fold prices a subscription's emitted values at
-- `2 ^ syncSizeᵉ b` times the path-plus-subject nesting.  The exponent
-- is meant to pay for a step function that is written once and applied
-- once per value of an instant -- so its size class has to see how WIDE
-- an instant can be.  `syncSizeᵉ` reads ONE at a scripted input, and a
-- cold script's synchronous burst is as wide as the script.  So a
-- `scanᵉ` over such an input applies its step function as many times as
-- the script is long while the exponent does not move at all.
--
-- THE FAMILY, and it is the one that killed the descent's flat charge:
-- a step function naming its accumulator in the two additive slots an
-- inner `scanᵉ` offers, so one application DOUBLES the delivered depth.
-- Over the script the delivered side is a power of two in the script's
-- length and the grant is the constant `1024`.
--
-- IT IS A CROSSING AND NOT A SCALE ERROR.  At twelve script values the
-- fold HOLDS -- 4095 against 4096, tight to one -- and at thirteen it
-- fails, 8191 against the same 4096.  The grant is the same number in
-- both rows, because a script is charged to neither side of it: it is
-- invisible to `syncSizeᵉ`, and `slotWrapSum` reads zero at a scripted
-- slot, so the telescope summand cannot pay for it either.
--
-- WHAT THE REPAIR CANNOT BE.  Not a larger constant, since the left
-- side doubles per script value while the right stands still.  Not the
-- telescope summand, for the same reason.  What the exponent is missing
-- is a width the program's syntax does not carry -- the quantity that
-- DOES see a script is the slot size, which is what the caps face
-- reaches for when the identical family kills its own flat form.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Sight-Fit-Scan where

open import Data.Bool using (T)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; _+_; _*_; _^_; _≤_; z≤n)
open import Data.Nat.Properties using (≤⇒≤ᵇ; ≤-trans; ⊔-lub; m≤n+m; m≤m+n)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEmit)
open import Rx.Exp using (Ty; Ctx; Val; natᵗ; obs; inputsBelowᵉ; syncSizeᵉ)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵛ)
open import Rx.Evaluator using (Stream; Path; splitEvents; subscribeE; root; sched-init; st-init)
open import Verify-Budget-Sufficient.Nest-Store using (pathNestD; slotWrapSum)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ; nestDᵛˢ-++)
open import Refuted.Demand-Programs using (Γ₂)
open import Refuted.Scan-Burst-Nest using (prog; slots; gas)

-- the fold's NUMERIC half, restated: refuting the weaker statement
-- refutes the one that also asks which inputs a value may name.
ValsFitR : ∀ {n} {Γ : Ctx n} (k : ℕ) (sl : Slots Γ) (G P : ℕ) (t : Ty)
  → List (Val Γ t) → Set
ValsFitR k sl G P t []       = ⊤
ValsFitR k sl G P t (o ∷ os) =
  (P + nestDᵛ t o + k * slotWrapSum sl ≤ G) × ValsFitR k sl G P t os

StreamFitR : ∀ {n} {Γ : Ctx n} (k : ℕ) (sl : Slots Γ) (G P : ℕ) (t : Ty)
  → Stream Γ t → Set
StreamFitR k sl G P t []                 = ⊤
StreamFitR {Γ = Γ} k sl G P t (em ∷ ems) =
  ValsFitR k sl G P t (proj₁ (splitEvents {A = Val Γ t} (InstEmit.events em)))
  × StreamFitR k sl G P t ems

burstVals : ∀ {n} {Γ : Ctx n} {t} → Stream Γ t → List (Val Γ t)
burstVals []                       = []
burstVals {Γ = Γ} {t = t} (em ∷ ems) =
  proj₁ (splitEvents {A = Val Γ t} (InstEmit.events em)) ++ burstVals ems

vals-le : ∀ {n} {Γ : Ctx n} (k : ℕ) (sl : Slots Γ) (G P : ℕ) (t : Ty)
  (os : List (Val Γ t)) → ValsFitR k sl G P t os → nestDᵛˢ os ≤ G
vals-le k sl G P t []       h        = z≤n
vals-le k sl G P t (o ∷ os) (h , hs) =
  ⊔-lub (≤-trans (≤-trans (m≤n+m (nestDᵛ t o) P)
                          (m≤m+n (P + nestDᵛ t o) (k * slotWrapSum sl))) h)
        (vals-le k sl G P t os hs)

str-le : ∀ {n} {Γ : Ctx n} (k : ℕ) (sl : Slots Γ) (G P : ℕ) (t : Ty)
  (str : Stream Γ t) → StreamFitR k sl G P t str → nestDᵛˢ (burstVals str) ≤ G
str-le k sl G P t []         h        = z≤n
str-le {Γ = Γ} k sl G P t (em ∷ ems) (h , hs) =
  ≤-trans (nestDᵛˢ-++ (proj₁ (splitEvents {A = Val Γ t} (InstEmit.events em)))
                      (burstVals ems))
          (⊔-lub (vals-le k sl G P t _ h) (str-le k sl G P t ems hs))

κ₀ : Path Γ₂ (obs natᵗ) (obs natᵗ)
κ₀ = root

runAt : ℕ → _
runAt N = subscribeE gas prog κ₀ 0 0 (sched-init prog (slots N)) (st-init prog)

Grant : ℕ → ℕ
Grant N = 2 ^ syncSizeᵉ prog * (pathNestD κ₀ + nestDᵉ prog)
        + 2 * slotWrapSum (slots N)

-- the hypothesis is DISCHARGED, not assumed: the subject names slot one
ok₂ : T (inputsBelowᵉ 2 prog)
ok₂ = tt

figs : ℕ
figs = nestDᵛˢ (burstVals (proj₁ (runAt 12)))
     + 100000 * nestDᵛˢ (burstVals (proj₁ (runAt 13)))
     + 10000000000 * Grant 13

figs≡ : figs ≡ 40960819104095
figs≡ = refl

scan-fit-absurd :
  StreamFitR 2 (slots 13) (Grant 13) (pathNestD κ₀) (obs natᵗ)
    (proj₁ (runAt 13)) → ⊥
scan-fit-absurd fit =
  ≤⇒≤ᵇ (str-le 2 (slots 13) (Grant 13) (pathNestD κ₀) (obs natᵗ)
          (proj₁ (runAt 13)) fit)
