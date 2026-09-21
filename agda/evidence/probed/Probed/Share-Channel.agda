-- WHICH SLOT TYPES OPENED THE FORGERY CHANNEL, measured rather than
-- argued, and the bar that closed it.  The survey was taken over the
-- SHARED arm because the scripted one had carried `isData` all along
-- (for descent, Rx.Slots), leaving shared the only arm at which an
-- observable-typed slot could still be written.  The channel itself is
-- in the TYPE and not in the arm -- see Rx.Slots -- so what the six
-- readings vary is the definition, at a slot type held fixed:
--
--   D  data-typed slot, adversarial plain def       ACCEPTED
--   O  obs-typed slot, def = `ofᵉ (strmᵗ (elaborate e) ∷ [])`   ACCEPTED
--   F  obs-typed slot, def = a forged envelope      REJECTED
--   L  obs-typed slot, def = `mapᵉ laneᵛ (elaborate e)`         REJECTED
--   E  the same, over an EMPTY inner                REJECTED
--   Y  obs-typed slot, def DYNAMIC (`mapᵉ` over a live source) ACCEPTED
--
-- FIVE OF THE SIX NO LONGER TYPECHECK, and that is the finding being
-- banked rather than a loss of coverage.  `Rx.Slots` now charges
-- `T (isData t)` against BOTH slot arms, so `Γᴼ = natᵗ ∷ⱽ obs natᵗ`
-- admits no table at all: `bar-engages` below is the one-line proof,
-- and it is what O, F, L, E and Y have collapsed into.  D survives
-- because a data-typed slot was never the hole.
--
-- WHAT D SAYS, AND IT IS WHY THE BAR IS NOT A CONFESSION.  A
-- data-typed share cannot forge, and the reason is structural rather
-- than lucky: the reference site elaborates to `inputᵖ i`, whose
-- `deliveries` arm is `mergeAllᵉ (mapᵉ stamp (batchSyncᵉ (input i)))`,
-- and `subs-shared` fires at that INNER `input i` -- so the def's
-- emissions are substituted UNDER `stamp` and are wrapped on their way
-- out.  The def here is a raw `input` beneath a flattener, the exact
-- shape refuted in Refuted.Flattened-Input when it appears in an
-- ELABORATED tree, and at data type it is harmless.  So `isData` was
-- never the property doing the work at a data slot; being wrapped by
-- `stamp` was, and `isData` is merely the cheapest predicate that
-- happens to name the slots where the wrapping holds.
--
-- WHAT O AND F SAID TOGETHER.  At `plainᵗ (obs u) = obs (emitᵗ u)` the
-- slot's VALUES are themselves observables of envelopes, and a
-- `mergeAllˢ` on the reference flattens them via `mapᵉ laneᵛ` -- which
-- subscribes them directly, so their emissions reached the wire having
-- never passed `stamp`.  F was that hole exercised -- `Sᶠ ≡ nothing`,
-- a `delivery` whose source no `init` ever enlisted, with the author
-- having written nothing unusual.  O was a legitimate inhabitant at
-- the same type, which is why the channel could not be closed by
-- inspecting the def alone.
--
-- WHAT L AND E REFUTED, and it still stands as a warning.  The tidy
-- repair was to read a def through the lane extraction the flattener
-- already performs -- `mapᵉ laneᵛ ∘ elaborate` -- which typechecks
-- exactly at the slot type.  It is wrong, and E said so structurally
-- rather than by content: an empty inner was rejected too.  The
-- reference's own `mergeAllᵖ` already applies `laneᵛ`, so a def that
-- applies it as well is laned twice.
--
-- WHAT Y SAID, AND WHAT THE BAR THEREFORE COSTS.  O's def was a static
-- list; Y's was a `mapᵉ` over a live source handing back `strmᵗ` of an
-- elaboration -- an author's `source$.pipe(map(x => inner$))` -- and
-- it was accepted, three sources deep and correctly bracketed.  Both
-- are barred now.  That is the price and it is stated plainly: a slot
-- may no longer SUPPLY observables.
--
-- WHY THE PRICE IS ZERO IN PRACTICE.  Nothing builds such a slot.  The
-- TS generator draws every slot type from `genValTy`, whose comment
-- reads "value types only (no obs)", and marks the `obs` arm of
-- `genVal` unreachable with "slots are value-typed"; the CLI decoder
-- now rejects the type in both arms; and the library's surface rejects
-- it a third time, `wrapCold` being overloaded to return `never` on an
-- `Observable<Observable<A>>`.  The restriction is the spec of srxjs,
-- not the proof narrowing the evaluator behind the spec's back -- and
-- THAT is what licenses it, since the earlier reading (Rx.Palette, now
-- deleted) correctly refused to spend evaluator scope on the proof's
-- behalf and was wrong only in believing the scope was occupied.
module Probed.Share-Channel where

open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_; concat)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (false)
open import Data.Product using (_,_)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (cold; after_,_)
open import Rx.Exp using (Ctx; obs; natᵗ; Closed; isData;
  input; ofᵉ; mergeAllᵉ; strmᵗ)
open import Rx.SExp using (inputˢ; plainᵛ; emitᵗ)
open import Rx.Elaborate using (elaborate)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Envelope.Decode using (decodeStream)
open import Rx.Evaluator.Builder using (evaluate↓)
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

-- DELIBERATELY WRONG: read the normal forms off the errors.
sawᴰ : Sᴰ ≡ just (record { live = 4 ∷ [] ; horizon = 7
                         ; current = just (7 , (4 , 0) ∷ []) ; done = false })
sawᴰ = refl

------------------------------------------------------------------
-- THE BAR, which is what O, F, L, E and Y collapsed into.
------------------------------------------------------------------

-- THE CHANNEL'S SLOT TYPE IS UNINHABITED BY ANY TABLE.  `Slot` charges
-- `T (isData t)` on both arms and `T false` is empty, so no `Slots`
-- exists over a context carrying `obs natᵗ` -- in EITHER arm, so the
-- forged def has nowhere left to stand and neither does the legitimate
-- one.  The five collapsed probes are not missing coverage; they are
-- this equation, which is why it is stated rather than assumed.
bar-engages : isData (obs natᵗ) ≡ false
bar-engages = refl
