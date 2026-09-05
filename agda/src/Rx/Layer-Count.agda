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
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; suc; _⊔_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Rx.Exp using (Ty; Ctx; Exp; Tm; Val;
                          unitᵗ; boolᵗ; natᵗ; obs; _×ᵗ_; _+ᵗ_;
                          input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                          mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          μᵉ; varᵉ; deferᵉ;
                          varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                          inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
                          elimGExp; elimGTm; elimGTms; unfoldμ)

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

-- A RECURSIVE-OCCURRENCE SUBSTITUTION MOVES NO LAYER, which is the one
-- fact about `μ` this count carries.  The occurrence is a Δᵍ variable,
-- and a Δᵍ variable becomes substitutable only by crossing into Δ at a
-- `deferᵉ` -- so every position the closure can land at sits under a
-- defer, and a defer is charged nothing.  The count therefore reads the
-- unfolding and the `μ` alike, however many times the body mentions
-- itself, which is exactly what makes the layer count blind to the
-- multiplicity the SIZE side is squared by.
mutual
  lay-elimGᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (b : Exp Γ Δᵍ Δ Θ u) →
    layᵉ (elimGExp x cl b) ≡ layᵉ b
  lay-elimGᵉ x cl (input i)         = refl
  lay-elimGᵉ x cl (ofᵉ ts)          = lay-elimGᵗˢ x cl ts
  lay-elimGᵉ x cl emptyᵉ            = refl
  lay-elimGᵉ x cl (mapᵉ f b)        =
    cong suc (cong₂ _⊔_ (lay-elimGᵗ x cl f) (lay-elimGᵉ x cl b))
  lay-elimGᵉ x cl (takeᵉ c b)       =
    cong suc (cong₂ _⊔_ (lay-elimGᵗ x cl c) (lay-elimGᵉ x cl b))
  lay-elimGᵉ x cl (scanᵉ f z b)     =
    cong suc (cong₂ _⊔_ (cong₂ _⊔_ (lay-elimGᵗ x cl f) (lay-elimGᵗ x cl z))
                        (lay-elimGᵉ x cl b))
  lay-elimGᵉ x cl (mergeAllᵉ lim b) = cong suc (lay-elimGᵉ x cl b)
  lay-elimGᵉ x cl (switchAllᵉ b)    = cong suc (lay-elimGᵉ x cl b)
  lay-elimGᵉ x cl (exhaustAllᵉ b)   = cong suc (lay-elimGᵉ x cl b)
  lay-elimGᵉ x cl (μᵉ b)            = lay-elimGᵉ (there x) cl b
  lay-elimGᵉ x cl (varᵉ y)          = refl
  lay-elimGᵉ x cl (deferᵉ b)        = refl

  lay-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (f : Tm Γ Δᵍ Δ Θ u) →
    layᵗ (elimGTm x cl f) ≡ layᵗ f
  lay-elimGᵗ x cl (varᵗ y)      = refl
  lay-elimGᵗ x cl unit̂          = refl
  lay-elimGᵗ x cl (bool̂ b)      = refl
  lay-elimGᵗ x cl (nat̂ m)       = refl
  lay-elimGᵗ x cl (pairᵗ a b)   = cong₂ _⊔_ (lay-elimGᵗ x cl a) (lay-elimGᵗ x cl b)
  lay-elimGᵗ x cl (fstᵗ p)      = lay-elimGᵗ x cl p
  lay-elimGᵗ x cl (sndᵗ p)      = lay-elimGᵗ x cl p
  lay-elimGᵗ x cl (inlᵗ a)      = lay-elimGᵗ x cl a
  lay-elimGᵗ x cl (inrᵗ a)      = lay-elimGᵗ x cl a
  lay-elimGᵗ x cl (caseᵗ s l r) =
    cong₂ _⊔_ (lay-elimGᵗ x cl s)
              (cong₂ _⊔_ (lay-elimGᵗ x cl l) (lay-elimGᵗ x cl r))
  lay-elimGᵗ x cl (ifᵗ c a b)   =
    cong₂ _⊔_ (cong₂ _⊔_ (lay-elimGᵗ x cl c) (lay-elimGᵗ x cl a))
              (lay-elimGᵗ x cl b)
  lay-elimGᵗ x cl (primᵗ op a)  = lay-elimGᵗ x cl a
  lay-elimGᵗ x cl (strmᵗ b)     = lay-elimGᵉ x cl b

  lay-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    layᵗˢ (elimGTms x cl ts) ≡ layᵗˢ ts
  lay-elimGᵗˢ x cl []       = refl
  lay-elimGᵗˢ x cl (y ∷ ys) =
    cong₂ _⊔_ (lay-elimGᵗ x cl y) (lay-elimGᵗˢ x cl ys)

lay-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
  layᵉ (unfoldμ body) ≡ layᵉ (μᵉ body)
lay-unfoldμ body = lay-elimGᵉ (here refl) (μᵉ body) body

-- THE MU DEPTH: how many times a descent can UNFOLD, and nothing about
-- what an unfolding contains.
--
-- WHY IT IS A SECOND COUNT AND NOT PART OF THE FIRST.  A `μ` costs the
-- layer count nothing, and the block above says why: the substitution
-- lands only under defers, and a defer runs no operator.  What it does
-- cost is SYNTAX -- an unfolding plants a copy of the whole program at
-- every recursive occurrence, so a body mentioning itself `k` times is
-- squared however few layers it has.  The quantity a descent's size
-- bound is squared by is therefore the μ NESTING, and it is a separate
-- count for exactly the reason the layer count cannot see it.
--
-- WHERE IT STOPS, AND IT STOPS ONE POSITION WIDER THAN THE LAYER COUNT.
-- It reads only what a subscription DESCENDS INTO: an operator's source
-- and a `μ`'s own body.  An `ofᵉ` list is handed out rather than
-- entered, and a `deferᵉ` is entered at a later tick, so both count
-- zero -- and an embedded observable inside a term is charged where it
-- is subscribed, which is the door that receives it and not the
-- descent that emits it.
muDepthᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → ℕ
muDepthᵉ (input i)         = 0
muDepthᵉ (ofᵉ ts)          = 0
muDepthᵉ emptyᵉ            = 0
muDepthᵉ (mapᵉ f e)        = muDepthᵉ e
muDepthᵉ (takeᵉ c e)       = muDepthᵉ e
muDepthᵉ (scanᵉ f z e)     = muDepthᵉ e
muDepthᵉ (mergeAllᵉ lim e) = muDepthᵉ e
muDepthᵉ (switchAllᵉ e)    = muDepthᵉ e
muDepthᵉ (exhaustAllᵉ e)   = muDepthᵉ e
muDepthᵉ (μᵉ e)            = suc (muDepthᵉ e)
muDepthᵉ (varᵉ x)          = 0
muDepthᵉ (deferᵉ e)        = 0

muDepthᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) → Val Γ t → ℕ
muDepthᵛ unitᵗ    _        = 0
muDepthᵛ boolᵗ    _        = 0
muDepthᵛ natᵗ     _        = 0
muDepthᵛ (s ×ᵗ t) (a , b)  = muDepthᵛ s a ⊔ muDepthᵛ t b
muDepthᵛ (s +ᵗ t) (inj₁ a) = muDepthᵛ s a
muDepthᵛ (s +ᵗ t) (inj₂ b) = muDepthᵛ t b
muDepthᵛ (obs t)  e        = muDepthᵉ e

-- AND A RECURSIVE-OCCURRENCE SUBSTITUTION MOVES NO NESTING EITHER, for
-- a reason the layer count's version does not have available: this one
-- needs no companion over terms at all, because an `ofᵉ` is already
-- zero on both sides.  The `μ` arm is where the two differ -- the count
-- is `suc` there rather than a pass-through, so the arm carries a
-- `cong suc` the layer version does not need.
muDepth-elimGᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
  (cl : Exp Γ [] [] [] t) (b : Exp Γ Δᵍ Δ Θ u) →
  muDepthᵉ (elimGExp x cl b) ≡ muDepthᵉ b
muDepth-elimGᵉ x cl (input i)         = refl
muDepth-elimGᵉ x cl (ofᵉ ts)          = refl
muDepth-elimGᵉ x cl emptyᵉ            = refl
muDepth-elimGᵉ x cl (mapᵉ f b)        = muDepth-elimGᵉ x cl b
muDepth-elimGᵉ x cl (takeᵉ c b)       = muDepth-elimGᵉ x cl b
muDepth-elimGᵉ x cl (scanᵉ f z b)     = muDepth-elimGᵉ x cl b
muDepth-elimGᵉ x cl (mergeAllᵉ lim b) = muDepth-elimGᵉ x cl b
muDepth-elimGᵉ x cl (switchAllᵉ b)    = muDepth-elimGᵉ x cl b
muDepth-elimGᵉ x cl (exhaustAllᵉ b)   = muDepth-elimGᵉ x cl b
muDepth-elimGᵉ x cl (μᵉ b)            = cong suc (muDepth-elimGᵉ (there x) cl b)
muDepth-elimGᵉ x cl (varᵉ y)          = refl
muDepth-elimGᵉ x cl (deferᵉ b)        = refl

muDepth-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
  muDepthᵉ (unfoldμ body) ≡ muDepthᵉ body
muDepth-unfoldμ body = muDepth-elimGᵉ (here refl) (μᵉ body) body
