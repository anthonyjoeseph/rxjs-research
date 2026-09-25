-- THE IMPL SIDE'S OWN ELABORATION, AND IT IS WHERE THE ENVELOPE IS FREE.
-- The walk is the spec's walk former for former; what may differ is the
-- per-former body each arm calls, because the top line compares raw
-- values per arrival and never the envelope around them.  An arm calling
-- the spec's body is one no batching failure has yet asked to change.
module Implementation.Elaborate where

open import Data.List using (List; []; _∷_)
open import Data.List.Properties using (map-++)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Vec using (lookup)
open import Data.Vec.Properties using (lookup-zipWith)
open import Relation.Binary.PropositionalEquality using (subst; refl)

open import Rx.Exp using (Ty; Ctx; Exp; Tm; Fn; obs; listᵗ; boolᵗ; uniqᵗ; _×ᵗ_; input; μᵉ; varᵉ; deferᵉ; mintᵉ;
  ofᵉ; emptyᵉ; mapᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; letᵗ; appendᵗ;
  varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; nilᵗ; consᵗ; inlᵗ; inrᵗ; caseᵗ;
  foldᵗ; ifᵗ; primᵗ; strmᵗ; add; sub; mul; eqᵖ; ltᵖ; eqᵘ; notᵖ)
open import Rx.Envelope using (machineEmitᵗ; instEventᵗ; eventsᵛ; splitEventsᵛ; reassembleᵛ)
open import Rx.SExp using (SExp; STm; inputˢ; ofˢ; emptyˢ; takeˢ; mapˢ; scanˢ; mergeAllˢ; switchAllˢ; exhaustAllˢ; μˢ;
  varˢ; deferˢ; varˢᵗ; unitˢ; boolˢ; natˢ; pairˢ; fstˢ; sndˢ; nilˢ; consˢ; inlˢ; inrˢ; caseˢ;
  foldˢ; ifˢ; primˢ; strmˢ; plainᵗ; plainᶜ; emitᵗ; emitᶜ; Kinds; scriptedᵏ; sharedᵏ; slotTy;
  plainᵏ)
open import Rx.Elaborate using (plainᶜ⁺; frameᵛ; inputᵖ; ofᵖ; emptyᵖ; takeᵖ; mapᵖ; scanᵖ;
  mergeObsᵛ)

-- ONE OUTER EMIT'S LANE, WITH ITS BOOKKEEPING LAST.  The spec's lane
-- (`Rx.Elaborate.laneᵛ`) runs the re-stamped outer envelope FIRST and the
-- inner streams behind it, so a delivery is paid off before the values it
-- caused arrive, and the completion it carries rides ahead of them too.
-- Run last, the payment is the final synchronous thing a lane does, so an
-- instant is paid off exactly when every value it caused through this
-- lane has been emitted -- which is the flush point the batcher reads.
laneᴵ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
      → Fn Γ Δᵍ Δ Θ (emitᵗ (obs t)) (obs (emitᵗ t))
laneᴵ {Θ = Θ} {t = t} =
  letᵗ (splitEventsᵛ {b = plainᵗ t} (eventsᵛ (varᵗ (here refl))))
       (strmᵗ emptyᵉ) body
  where
  SP : Ty
  SP = listᵗ (instEventᵗ uniqᵗ (plainᵗ t)) ×ᵗ (listᵗ (plainᵗ (obs t)) ×ᵗ boolᵗ)

  body : Tm _ _ _ (SP ∷ emitᵗ (obs t) ∷ Θ) (obs (emitᵗ t))
  body = mergeObsᵛ (appendᵗ (fstᵗ (sndᵗ split)) (consᵗ bookLane nilᵗ))
    where
    split = varᵗ (here refl)
    env   = varᵗ (there (here refl))

    bookLane = strmᵗ (ofᵉ (reassembleᵛ env (fstᵗ split) nilᵗ
                                       (sndᵗ (sndᵗ split)) ∷ []))

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

 mutual

   toImpl : ∀ {Δᵍ Δ Θ : List Ty} {t : Ty}
          → SExp Γ Δᵍ Δ Θ t
          → Exp (plainᵏ Γ κ) (emitᶜ Δᵍ) (emitᶜ Δ) (plainᶜ⁺ Θ) (emitᵗ t)
   toImpl {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (inputˢ i)
     with lookup κ i | lookup-zipWith slotTy i Γ κ
   ... | scriptedᵏ | eq =
         subst (λ u → Exp (plainᵏ Γ κ) (emitᶜ Δᵍ) (emitᶜ Δ) (plainᶜ⁺ Θ)
                          (machineEmitᵗ u))
               eq (inputᵖ i (frameᵛ Θ))
   ... | sharedᵏ   | eq =
         subst (λ u → Exp (plainᵏ Γ κ) (emitᶜ Δᵍ) (emitᶜ Δ) (plainᶜ⁺ Θ) u)
               eq (input i)
   toImpl {Θ = Θ} (ofˢ ts)    = ofᵖ (frameᵛ Θ) (toImplTms ts)
   toImpl {Θ = Θ} emptyˢ      = emptyᵖ (frameᵛ Θ)
   toImpl (takeˢ k e)         = takeᵖ (toImplTm k) (toImpl e)
   toImpl (mapˢ f e)          = mapᵖ (toImplTm f) (toImpl e)
   toImpl (scanˢ f z e)       = scanᵖ (toImplTm f) (toImplTm z) (toImpl e)
   toImpl (mergeAllˢ k e)     = mergeAllᵉ k (mapᵉ laneᴵ (toImpl e))
   toImpl (switchAllˢ e)      = switchAllᵉ (mapᵉ laneᴵ (toImpl e))
   toImpl (exhaustAllˢ e)     = exhaustAllᵉ (mapᵉ laneᴵ (toImpl e))
   toImpl (μˢ e)              = μᵉ (toImpl e)
   toImpl (varˢ x)            = varᵉ (∈-map⁺ emitᵗ x)
   toImpl {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (deferˢ {t = t} e) =
     deferᵉ (subst (λ ζ → Exp (plainᵏ Γ κ) [] ζ (plainᶜ⁺ Θ) (emitᵗ t))
                   (map-++ emitᵗ Δᵍ Δ) (toImpl e))

   toImplTm : ∀ {Δᵍ Δ Θ : List Ty} {t : Ty}
            → STm Γ Δᵍ Δ Θ t
            → Tm (plainᵏ Γ κ) (emitᶜ Δᵍ) (emitᶜ Δ) (plainᶜ⁺ Θ) (plainᵗ t)
   toImplTm (varˢᵗ x)      = varᵗ (∈-++⁺ˡ (∈-map⁺ plainᵗ x))
   toImplTm unitˢ          = unit̂
   toImplTm (boolˢ b)      = bool̂ b
   toImplTm (natˢ k)       = nat̂ k
   toImplTm (pairˢ a b)    = pairᵗ (toImplTm a) (toImplTm b)
   toImplTm (fstˢ p)       = fstᵗ (toImplTm p)
   toImplTm (sndˢ p)       = sndᵗ (toImplTm p)
   toImplTm nilˢ           = nilᵗ
   toImplTm (consˢ h t)    = consᵗ (toImplTm h) (toImplTm t)
   toImplTm (inlˢ a)       = inlᵗ (toImplTm a)
   toImplTm (inrˢ b)       = inrᵗ (toImplTm b)
   toImplTm (caseˢ s l r)  = caseᵗ (toImplTm s) (toImplTm l) (toImplTm r)
   toImplTm (foldˢ l z f)  = foldᵗ (toImplTm l) (toImplTm z) (toImplTm f)
   toImplTm (ifˢ c a b)    = ifᵗ (toImplTm c) (toImplTm a) (toImplTm b)
   toImplTm (primˢ add a)  = primᵗ add  (toImplTm a)
   toImplTm (primˢ sub a)  = primᵗ sub  (toImplTm a)
   toImplTm (primˢ mul a)  = primᵗ mul  (toImplTm a)
   toImplTm (primˢ eqᵖ a)  = primᵗ eqᵖ  (toImplTm a)
   toImplTm (primˢ ltᵖ a)  = primᵗ ltᵖ  (toImplTm a)
   toImplTm (primˢ eqᵘ a)  = primᵗ eqᵘ  (toImplTm a)
   toImplTm (primˢ notᵖ a) = primᵗ notᵖ (toImplTm a)
   toImplTm (strmˢ e)      = strmᵗ (toImpl e)

   toImplTms : ∀ {Δᵍ Δ Θ : List Ty} {t : Ty}
             → List (STm Γ Δᵍ Δ Θ t)
             → List (Tm (plainᵏ Γ κ) (emitᶜ Δᵍ) (emitᶜ Δ) (plainᶜ⁺ Θ) (plainᵗ t))
   toImplTms []       = []
   toImplTms (m ∷ ms) = toImplTm m ∷ toImplTms ms

-- one mint above the walk, as on the spec side
elaborateᴵ : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {Δᵍ Δ : List Ty} {t : Ty}
           → SExp Γ Δᵍ Δ [] t
           → Exp (plainᵏ Γ κ) (emitᶜ Δᵍ) (emitᶜ Δ) [] (emitᵗ t)
elaborateᴵ κ e = mintᵉ (toImpl κ e)
