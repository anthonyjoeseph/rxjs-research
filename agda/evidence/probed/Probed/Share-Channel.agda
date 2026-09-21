-- WHICH SLOT TYPES OPEN THE FORGERY CHANNEL, measured rather than
-- argued.  `subs-shared` subscribes a shared def STRAIGHT DOWN the
-- consumer's path -- no `inputᵖ`, no `stamp` -- so every slot type is a
-- candidate hole.  Four readings say the hole is at exactly one of
-- them, and a fifth refutes the obvious repair.
--
--   D  data-typed slot, adversarial plain def       ACCEPTED
--   O  obs-typed slot, def = `ofᵉ (strmᵗ (elaborate e) ∷ [])`   ACCEPTED
--   F  obs-typed slot, def = a forged envelope      REJECTED
--   L  obs-typed slot, def = `mapᵉ laneᵛ (elaborate e)`         REJECTED
--   E  the same, over an EMPTY inner                REJECTED
--   Y  obs-typed slot, def DYNAMIC (`mapᵉ` over a live source) ACCEPTED
--
-- WHAT D SAYS.  A data-typed share cannot forge, and the reason is
-- structural rather than lucky: the reference site elaborates to
-- `inputᵖ i`, whose `deliveries` arm is `mergeAllᵉ (mapᵉ stamp
-- (batchSyncᵉ (input i)))`, and `subs-shared` fires at that INNER
-- `input i` -- so the def's emissions are substituted UNDER `stamp` and
-- are wrapped on their way out.  The def here is a raw `input` beneath
-- a flattener, the exact shape refuted in Refuted.Flattened-Input when
-- it appears in an ELABORATED tree, and at data type it is harmless.
-- So `isData` was never the property doing the work; being wrapped by
-- `stamp` was.
--
-- WHAT O AND F SAY TOGETHER.  At `plainᵗ (obs u) = obs (emitᵗ u)` the
-- slot's VALUES are themselves observables of envelopes, and a
-- `mergeAllˢ` on the reference flattens them via `mapᵉ laneᵛ` -- which
-- subscribes them directly, so their emissions reach the wire having
-- never passed `stamp`.  F is that hole exercised; O is a legitimate
-- inhabitant AT THE SLOT'S EXISTING TYPE.  The channel is real, it is
-- live today, and it is confined to `obs`.
--
-- WHAT L AND E REFUTE.  The tidy repair is to make the palette's
-- `embed` the lane extraction the flattener already performs --
-- `mapᵉ laneᵛ ∘ elaborate` -- which typechecks exactly at the slot
-- type and would let `Tree` at an `obs` slot simply BE `SExp`.  It is
-- wrong, and E says structurally so rather than by content: an empty
-- inner is rejected too.  The reference's own `mergeAllᵖ` already
-- applies `laneᵛ`, so a def that applies it as well is laned twice.
-- The shape that survives is O's -- elaborations carried AS VALUES,
-- with the single lane left to the consumer.
--
-- WHAT Y SAYS, and it is what decides the palette's SHAPE.  O's def is
-- a static list, and a palette admitting only static lists would be a
-- narrowing: an author's `source$.pipe(map(x => inner$))` produces its
-- inner observables one per arrival.  Y is that def -- a `mapᵉ` over a
-- live source handing back `strmᵗ` of an elaboration -- and it is
-- accepted, three sources deep and correctly bracketed.  So the
-- palette does NOT reduce to a list of elaborations: the def may be an
-- arbitrary plain tree, and the only thing barred is a `strmᵗ` at an
-- envelope-carrying type that no elaboration produced.
--
-- WHY THE BAR IS ON `strmᵗ` AND NOT ON THE TYPE.  `strmᵗ` is the only
-- INTRODUCTION form for an observable-typed value -- every other `Tm`
-- at `obs _` is a projection, a variable or a branch, and destructs one
-- that was introduced somewhere.  So a rule stated at `strmᵗ` catches
-- observables buried in products and lists without the family having to
-- recurse into the slot's TYPE at all, which is what D shows is
-- necessary: D's def flattens an `obs natᵗ` that is outside the image
-- of `plainᵗ` entirely, and any type-indexed family would have excluded
-- it.
module Probed.Share-Channel where

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; concat)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Bool using (false)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (ObservableInput; cold; after_,_)
open import Rx.Exp using (Ctx; Ty; obs; natᵗ; []ᵉ; Closed; Exp; Tm;
  input; ofᵉ; mergeAllᵉ; mapᵉ; strmᵗ; mintᵉ; nilᵗ; varᵗ; renExp)
open import Rx.SExp using (SExp; inputˢ; mergeAllˢ; ofˢ; strmˢ; emptyˢ; plainᵛ; plainᵗ; emitᵗ)
open import Rx.Envelope using (instEmitᵛ)
open import Data.List.Relation.Unary.Any using (here)
open import Rx.Elaborate using (elaborate; deliveryᵛ; laneᵛ)
open import Rx.Palette using (plainPalette)
open import Rx.Slots plainPalette using (Slots; scripted; shared)
open import Rx.Envelope.Decode using (decodeStream)
open import Rx.Evaluator.Builder plainPalette using (evaluate↓)
open import Rx.Protocol using (ProtocolSt; protocol-init; runProtocol)

------------------------------------------------------------------
-- PROBE D: a DATA-typed share slot, with the most adversarial plain
-- def available at that type -- a raw `input` under a flattener, the
-- exact shape that is refuted when it appears in an ELABORATED tree.
------------------------------------------------------------------

Γᴰ : Ctx 2
Γᴰ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

defᴰ : Closed (plainᵛ Γᴰ) natᵗ
defᴰ = mergeAllᵉ nothing (ofᵉ (strmᵗ (input zero) ∷ []))

insᴰ : Slots (plainᵛ Γᴰ)
insᴰ zero          = scripted (cold (1 ∷ []) ((after 0 , 2) ∷ []))
insᴰ (suc zero)    = shared defᴰ
insᴰ (suc (suc ()))

progᴰ : Closed (plainᵛ Γᴰ) (emitᵗ natᵗ)
progᴰ = elaborate (inputˢ (suc zero))

Sᴰ : Maybe ProtocolSt
Sᴰ = runProtocol protocol-init
       (decodeStream {Γ = plainᵛ Γᴰ} {a = natᵗ} (concat (evaluate↓ 60 progᴰ insᴰ)))

------------------------------------------------------------------
-- PROBE O: an OBSERVABLE-typed share slot whose def is LEGITIMATE --
-- a one-element stream carrying an elaboration, which is exactly what
-- an author's `of(inner$)` would produce.
------------------------------------------------------------------

Γᴼ : Ctx 2
Γᴼ = natᵗ ∷ⱽ obs natᵗ ∷ⱽ []ⱽ

defᴼ : Closed (plainᵛ Γᴼ) (obs (emitᵗ natᵗ))
defᴼ = ofᵉ (strmᵗ (elaborate (inputˢ {Γ = Γᴼ} zero)) ∷ [])

insᴼ : Slots (plainᵛ Γᴼ)
insᴼ zero          = scripted (cold (1 ∷ []) ((after 0 , 2) ∷ []))
insᴼ (suc zero)    = shared defᴼ
insᴼ (suc (suc ()))

progᴼ : Closed (plainᵛ Γᴼ) (emitᵗ natᵗ)
progᴼ = elaborate (mergeAllˢ nothing (inputˢ {Γ = Γᴼ} (suc zero)))

Sᴼ : Maybe ProtocolSt
Sᴼ = runProtocol protocol-init
       (decodeStream {Γ = plainᵛ Γᴼ} {a = natᵗ} (concat (evaluate↓ 60 progᴼ insᴼ)))

------------------------------------------------------------------
-- PROBE F: the same OBSERVABLE-typed slot, def replaced by a FORGED
-- envelope -- a `delivery` whose source token no `init` ever enlisted.
------------------------------------------------------------------

defᶠ : Closed (plainᵛ Γᴼ) (obs (emitᵗ natᵗ))
defᶠ = ofᵉ (strmᵗ (mintᵉ (ofᵉ (instEmitᵛ nilᵗ (varᵗ (here refl))
                                        (varᵗ (here refl)) deliveryᵛ ∷ []))) ∷ [])

insᶠ : Slots (plainᵛ Γᴼ)
insᶠ zero          = scripted (cold (1 ∷ []) ((after 0 , 2) ∷ []))
insᶠ (suc zero)    = shared defᶠ
insᶠ (suc (suc ()))

Sᶠ : Maybe ProtocolSt
Sᶠ = runProtocol protocol-init
       (decodeStream {Γ = plainᵛ Γᴼ} {a = natᵗ} (concat (evaluate↓ 60 progᴼ insᶠ)))

------------------------------------------------------------------
-- PROBE L: the def built by the CANDIDATE `embed` -- `mapᵉ laneᵛ ∘
-- elaborate`, i.e. exactly the lane extraction the flattener already
-- performs -- over an ordinary author-written SExp.
------------------------------------------------------------------

innerᴸ : SExp Γᴼ [] [] [] (obs natᵗ)
innerᴸ = ofˢ (strmˢ emptyˢ ∷ [])

defᴸ : Closed (plainᵛ Γᴼ) (obs (emitᵗ natᵗ))
defᴸ = mapᵉ laneᵛ (elaborate innerᴸ)

insᴸ : Slots (plainᵛ Γᴼ)
insᴸ zero          = scripted (cold (1 ∷ []) ((after 0 , 2) ∷ []))
insᴸ (suc zero)    = shared defᴸ
insᴸ (suc (suc ()))

-- bisect: an EMPTY inner, so the lane carries only bookkeeping
defᴱ : Closed (plainᵛ Γᴼ) (obs (emitᵗ natᵗ))
defᴱ = mapᵉ laneᵛ (elaborate (emptyˢ {Γ = Γᴼ} {t = obs natᵗ}))

insᴱ : Slots (plainᵛ Γᴼ)
insᴱ zero          = scripted (cold (1 ∷ []) ((after 0 , 2) ∷ []))
insᴱ (suc zero)    = shared defᴱ
insᴱ (suc (suc ()))

Sᴱ : Maybe ProtocolSt
Sᴱ = runProtocol protocol-init
       (decodeStream {Γ = plainᵛ Γᴼ} {a = natᵗ} (concat (evaluate↓ 60 progᴼ insᴱ)))

Sᴸ : Maybe ProtocolSt
Sᴸ = runProtocol protocol-init
       (decodeStream {Γ = plainᵛ Γᴼ} {a = natᵗ} (concat (evaluate↓ 60 progᴼ insᴸ)))

------------------------------------------------------------------
-- PROBE Y: a DYNAMIC obs-typed def -- the inner observables are
-- produced by a `mapᵉ` over a live source rather than listed
-- statically, which is what an author's `source$.pipe(map(x => inner$))`
-- elaborates to.  If this is accepted the palette need not be a static
-- list.
------------------------------------------------------------------

defʸ : Closed (plainᵛ Γᴼ) (obs (emitᵗ natᵗ))
defʸ = mapᵉ (strmᵗ (renExp (λ x → x) (λ x → x) (λ ())
                     (elaborate (inputˢ {Γ = Γᴼ} {Δᵍ = []} {Δ = []} zero))))
            (input zero)

insʸ : Slots (plainᵛ Γᴼ)
insʸ zero          = scripted (cold (1 ∷ []) ((after 0 , 2) ∷ []))
insʸ (suc zero)    = shared defʸ
insʸ (suc (suc ()))

Sʸ : Maybe ProtocolSt
Sʸ = runProtocol protocol-init
       (decodeStream {Γ = plainᵛ Γᴼ} {a = natᵗ} (concat (evaluate↓ 60 progᴼ insʸ)))

-- DELIBERATELY WRONG: read the normal forms off the errors.
sawᴰ : Sᴰ ≡ just (record { live = 4 ∷ [] ; horizon = 7
                         ; current = just (7 , (4 , 0) ∷ []) ; done = false })
sawᴰ = refl

sawᴼ : Sᴼ ≡ just (record { live = 7 ∷ 4 ∷ [] ; horizon = 10
                         ; current = just (10 , (7 , 0) ∷ []) ; done = false })
sawᴼ = refl

sawᶠ : Sᶠ ≡ nothing
sawᶠ = refl

sawᴸ : Sᴸ ≡ nothing
sawᴸ = refl

sawᴱ : Sᴱ ≡ nothing
sawᴱ = refl

sawʸ : Sʸ ≡ just (record { live = 13 ∷ 8 ∷ 4 ∷ [] ; horizon = 17
                         ; current = just (17 , (13 , 0) ∷ []) ; done = false })
sawʸ = refl
