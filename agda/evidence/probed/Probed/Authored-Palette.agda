-- THE PALETTE INSTANTIATED, and the three accepted definitions of
-- Probed.Share-Channel exhibited as inhabitants of it.
--
-- WHAT THIS IS FOR.  `Rx.Authored` is a predicate, and a predicate that
-- admitted nothing would satisfy every soundness claim made about it
-- while making the evaluator useless.  These rows are the other half:
-- the data-typed definition, the static observable-typed one and the
-- DYNAMIC observable-typed one all derive, the evaluator runs at
-- `sexpPalette` with them installed, and the protocol accepts.
module Probed.Authored-Palette where

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; concat)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; false; true)
open import Data.Product using (_,_)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (cold; after_,_)
open import Rx.Exp using (Ctx; Ty; obs; natᵗ; Closed;
  input; ofᵉ; mergeAllᵉ; mapᵉ; strmᵗ; renExp)
open import Rx.SExp using (SExp; inputˢ; mergeAllˢ; plainᵛ; emitᵗ)
open import Rx.Elaborate using (elaborate)
open import Rx.Authored using (Authored; Authᵉ; isEnvᵗ;
  auth-input; auth-of; auth-map; auth-merge; auth-strm; auth-strmᵉ;
  auth-[]; auth-∷; elab-toPlain; elab-mint; elab-ren)
open import Rx.Palette.SExp using (sexpPalette)
open import Rx.Slots sexpPalette using (Slots; scripted; shared)
open import Rx.Envelope.Decode using (decodeStream)
open import Rx.Evaluator.Builder sexpPalette using (evaluate↓)
open import Rx.Protocol using (ProtocolSt; protocol-init; runProtocol)

-- THE BAR ENGAGES EXACTLY AT THE ENVELOPE, which is what makes the two
-- `strmᵗ` clauses do different work rather than one subsuming the other.
bar-off : isEnvᵗ natᵗ ≡ false
bar-off = refl

bar-on : isEnvᵗ (emitᵗ natᵗ) ≡ true
bar-on = refl

------------------------------------------------------------------
-- A DATA-typed slot: authorship is unconditional below the envelope.
------------------------------------------------------------------

Γᴰ : Ctx 2
Γᴰ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

defᴰ : Closed (plainᵛ Γᴰ) natᵗ
defᴰ = mergeAllᵉ nothing (ofᵉ (strmᵗ (input zero) ∷ []))

authᴰ : Authᵉ defᴰ
authᴰ = auth-merge (auth-of (auth-∷ (auth-strm (auth-input zero)) auth-[]))

insᴰ : Slots (plainᵛ Γᴰ)
insᴰ zero          = scripted (cold (1 ∷ []) ((after 0 , 2) ∷ []))
insᴰ (suc zero)    = shared (defᴰ , authᴰ)
insᴰ (suc (suc ()))

Sᴰ : Maybe ProtocolSt
Sᴰ = runProtocol protocol-init
       (decodeStream {Γ = plainᵛ Γᴰ} {a = natᵗ}
         (concat (evaluate↓ 60 (elaborate (inputˢ (suc zero))) insᴰ)))

------------------------------------------------------------------
-- An OBSERVABLE-typed slot, static and dynamic.
------------------------------------------------------------------

Γᴼ : Ctx 2
Γᴼ = natᵗ ∷ⱽ obs natᵗ ∷ⱽ []ⱽ

progᴼ : Closed (plainᵛ Γᴼ) (emitᵗ natᵗ)
progᴼ = elaborate (mergeAllˢ nothing (inputˢ {Γ = Γᴼ} (suc zero)))

defᴼ : Closed (plainᵛ Γᴼ) (obs (emitᵗ natᵗ))
defᴼ = ofᵉ (strmᵗ (elaborate (inputˢ {Γ = Γᴼ} zero)) ∷ [])

authᴼ : Authᵉ defᴼ
authᴼ = auth-of (auth-∷ (auth-strmᵉ (elab-mint (elab-toPlain (inputˢ {Γ = Γᴼ} zero)))) auth-[])

insᴼ : Slots (plainᵛ Γᴼ)
insᴼ zero          = scripted (cold (1 ∷ []) ((after 0 , 2) ∷ []))
insᴼ (suc zero)    = shared (defᴼ , authᴼ)
insᴼ (suc (suc ()))

Sᴼ : Maybe ProtocolSt
Sᴼ = runProtocol protocol-init
       (decodeStream {Γ = plainᵛ Γᴼ} {a = natᵗ} (concat (evaluate↓ 60 progᴼ insᴼ)))

defʸ : Closed (plainᵛ Γᴼ) (obs (emitᵗ natᵗ))
defʸ = mapᵉ (strmᵗ (renExp (λ x → x) (λ x → x) (λ ())
                     (elaborate (inputˢ {Γ = Γᴼ} {Δᵍ = []} {Δ = []} zero))))
            (input zero)

authʸ : Authᵉ defʸ
authʸ = auth-map (auth-strmᵉ (elab-ren (λ x → x) (λ x → x) (λ ()) (elab-mint
                    (elab-toPlain (inputˢ {Γ = Γᴼ} {Δᵍ = []} {Δ = []} zero)))))
                 (auth-input zero)

insʸ : Slots (plainᵛ Γᴼ)
insʸ zero          = scripted (cold (1 ∷ []) ((after 0 , 2) ∷ []))
insʸ (suc zero)    = shared (defʸ , authʸ)
insʸ (suc (suc ()))

Sʸ : Maybe ProtocolSt
Sʸ = runProtocol protocol-init
       (decodeStream {Γ = plainᵛ Γᴼ} {a = natᵗ} (concat (evaluate↓ 60 progᴼ insʸ)))

------------------------------------------------------------------
-- DELIBERATELY WRONG: read the normal forms off the errors.
------------------------------------------------------------------

okᴰ : Sᴰ ≡ just (record { live = 4 ∷ [] ; horizon = 7
                        ; current = just (7 , (4 , 0) ∷ []) ; done = false })
okᴰ = refl

okᴼ : Sᴼ ≡ just (record { live = 7 ∷ 4 ∷ [] ; horizon = 10
                        ; current = just (10 , (7 , 0) ∷ []) ; done = false })
okᴼ = refl

okʸ : Sʸ ≡ just (record { live = 13 ∷ 8 ∷ 4 ∷ [] ; horizon = 17
                        ; current = just (17 , (13 , 0) ∷ []) ; done = false })
okʸ = refl
