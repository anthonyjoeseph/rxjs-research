-- A COUNTEREXAMPLE TO `elaborated-accepted`, AND A SMALL ONE.
--
-- This began as a measurement of option 1's crux -- whether the
-- per-source delivery count is recoverable from the stream -- and
-- turned up something worse on the way.  The program below is an
-- ordinary one: a single scripted input, flattened by a mergeAll.  No
-- shares, no forgery, nothing at observable type in the slot table.
-- Its run is REJECTED by the protocol automaton, at every fuel, and
-- the ROOT SUBSCRIBE'S OWN BURST is already rejected before the drain
-- ever runs.
--
-- THE BRACKET, measured by bisection:
--
--   emptyˢ                              ACCEPTED  (Probe-Empty)
--   inputˢ zero                         ACCEPTED  (Probe-Input)
--   mergeAllˢ (ofˢ (strmˢ emptyˢ))      ACCEPTED  -- flattener alone is fine
--   mergeAllˢ (ofˢ (strmˢ (inputˢ 0)))  REJECTED  <- this file
--
-- So it is neither the input nor the flattener: it is an INPUT UNDER A
-- FLATTENER.  `inputᵖ` elaborates to its own `mintᵉ`-bound announce
-- plus a deliveries stream; something about that pair does not survive
-- being subscribed through `mergeAllᵉ`.
module Refuted.Flattened-Input where

open import Data.Fin using (zero)
open import Data.List using (List; []; _∷_; concat; map; length)
open import Data.Maybe using (Maybe; nothing)
open import Data.Nat using (ℕ; zero)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (cold; after_,_)
open import Rx.Exp using (Ctx; obs; natᵗ; []ᵉ; Closed)
open import Rx.SExp using (SExp; inputˢ; ofˢ; strmˢ; mergeAllˢ; plainᵏ; Kinds; scriptedᵏ; emitᵗ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Elaborate using (elaborate)
open import Rx.Envelope.Decode using (decodeStream)
open import Rx.Evaluator using
  (EvalSt; sched-init; st-init; root; regSource)
open import Rx.Evaluator.Reducible using (reducible)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Rx.Protocol using (ProtocolSt; protocol-init; runProtocol)

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

-- the one slot is an external source, so the elaboration reads it at
-- the author's payload and `inputᵖ` wraps each arrival
κ₁ : Kinds 1
κ₁ = scriptedᵏ ∷ⱽ []ⱽ

ins₁ : Slots (plainᵏ Γ₁ κ₁)
ins₁ zero = scripted (cold (1 ∷ []) ((after 0 , 2) ∷ []))

-- ONE input, TWO subscribers
inner : SExp Γ₁ [] [] [] (obs natᵗ)
inner = ofˢ (strmˢ (inputˢ zero) ∷ [])

src : SExp Γ₁ [] [] [] natᵗ
src = mergeAllˢ nothing inner

prog : Closed (plainᵏ Γ₁ κ₁) (emitᵗ natᵗ)
prog = elaborate κ₁ src

rootRun = reducible prog []ᵉ tt (root {lo = 1}) 0
            (sched-init prog ins₁) (st-init prog)

burst₀ = proj₁ (proj₁ rootRun)
st₀    = proj₂ (proj₂ (proj₁ rootRun))

regLive : List ℕ
regLive = map (λ r → regSource (proj₁ (proj₂ r))) (EvalSt.registry st₀)

S₀ : Maybe ProtocolSt
S₀ = runProtocol protocol-init
       (decodeStream {Γ = plainᵏ Γ₁ κ₁} {a = natᵗ} (concat burst₀))

Sfull : Maybe ProtocolSt
Sfull = runProtocol protocol-init
          (decodeStream {Γ = plainᵏ Γ₁ κ₁} {a = natᵗ}
            (concat (evaluate↓ 60 prog ins₁)))

-- DELIBERATELY WRONG: read the normal forms off the errors
saw-count : length regLive ≡ 1
saw-count = refl

-- the ROOT BURST ALONE is already rejected -- no drain involved
saw-root : S₀ ≡ nothing
saw-root = refl

-- and so is the whole run, at fuel 4, 12, 30 and 60 alike
saw-full : Sfull ≡ nothing
saw-full = refl
