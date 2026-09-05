------------------------------------------------------------------
-- THE LAYER COUNT: how many operators a runtime observable will run,
-- and nothing about how much data it carries.
--
-- WHY IT EXISTS, AND IT IS NOT A SECOND SIZE.  A frame that subscribes
-- an arriving observable charges rungs because running it can grow
-- what it emits, and the growth is per OPERATOR: each map, take, scan
-- or `*All` layer transforms once, and `iterSize` doubles per rung, so
-- a count of layers is the quantity a crossing's emission is
-- exponential in.  What it must NOT read is the arrival's payload,
-- because the walk manufactures payload: a frame applies a CLOSED
-- function and `applyFn` REIFIES the arriving value into the term, so
-- any measure charging a function's syntax is grown by the very ladder
-- it is meant to price.
--
-- WHAT THAT BUYS.  A reified datum contributes no layer however large,
-- so an arrival's count is bounded by the layers of the program that
-- wrote it rather than by the store bound the walk climbs.  That is
-- the whole difference from `sizeᵛ`, which a single frame can drive
-- from nothing to the arrival's own size.
--
-- WHERE IT JOINS BY MAX.  Every position carrying a PAYLOAD -- a
-- pair's arms, a sum's injection, an `ofᵉ` list, a case or an if
-- branch -- takes `⊔`, because two payloads abreast are entered
-- separately from the same frame and neither runs the other.  Every
-- position that CHAINS takes the layer plus what feeds it.
--
-- NOT A REPLACEMENT FOR `sizeᵛ` OR FOR `spnᵛ`.  It bounds no amount of
-- syntax and no depth: an arrival of one map layer over a million-node
-- literal counts one.  Its one job is to be the rung count a crossing
-- frame charges.
------------------------------------------------------------------
module Rx.Layer-Count where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc; _⊔_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import Rx.Exp using (Ty; Ctx; Exp; Tm; Val;
                          unitᵗ; boolᵗ; natᵗ; obs; _×ᵗ_; _+ᵗ_;
                          input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                          mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          μᵉ; varᵉ; deferᵉ;
                          varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                          inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ)

mutual
  -- `deferᵉ` counts nothing: its body is subscribed at a LATER tick, so
  -- it is not part of the synchronous run this count prices -- the same
  -- truncation `syncSizeᵉ` and `nestDᵉ` take, and for the same reason.
  layᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → ℕ
  layᵉ (input i)         = 0
  layᵉ (ofᵉ ts)          = layᵗˢ ts
  layᵉ emptyᵉ            = 0
  layᵉ (mapᵉ f e)        = suc (layᵗ f ⊔ layᵉ e)
  layᵉ (takeᵉ c e)       = suc (layᵗ c ⊔ layᵉ e)
  layᵉ (scanᵉ f z e)     = suc (layᵗ f ⊔ layᵗ z ⊔ layᵉ e)
  layᵉ (mergeAllᵉ lim e) = suc (layᵉ e)
  layᵉ (switchAllᵉ e)    = suc (layᵉ e)
  layᵉ (exhaustAllᵉ e)   = suc (layᵉ e)
  layᵉ (μᵉ e)            = layᵉ e
  layᵉ (varᵉ x)          = 0
  layᵉ (deferᵉ e)        = 0

  -- A term contributes only through the observables it EMBEDS, and
  -- never through its own shape: that is what makes the count blind to
  -- a reified payload.
  layᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ Δᵍ Δ Θ t → ℕ
  layᵗ (varᵗ x)      = 0
  layᵗ unit̂          = 0
  layᵗ (bool̂ _)      = 0
  layᵗ (nat̂ _)       = 0
  layᵗ (pairᵗ a b)   = layᵗ a ⊔ layᵗ b
  layᵗ (fstᵗ p)      = layᵗ p
  layᵗ (sndᵗ p)      = layᵗ p
  layᵗ (inlᵗ a)      = layᵗ a
  layᵗ (inrᵗ a)      = layᵗ a
  layᵗ (caseᵗ s l r) = layᵗ s ⊔ (layᵗ l ⊔ layᵗ r)
  layᵗ (ifᵗ c a b)   = layᵗ c ⊔ layᵗ a ⊔ layᵗ b
  layᵗ (primᵗ _ a)   = layᵗ a
  layᵗ (strmᵗ e)     = layᵉ e

  layᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  layᵗˢ []       = 0
  layᵗˢ (y ∷ ys) = layᵗ y ⊔ layᵗˢ ys

layᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) → Val Γ t → ℕ
layᵛ unitᵗ    _        = 0
layᵛ boolᵗ    _        = 0
layᵛ natᵗ     _        = 0
layᵛ (s ×ᵗ t) (a , b)  = layᵛ s a ⊔ layᵛ t b
layᵛ (s +ᵗ t) (inj₁ a) = layᵛ s a
layᵛ (s +ᵗ t) (inj₂ b) = layᵛ t b
layᵛ (obs t)  e        = layᵉ e
