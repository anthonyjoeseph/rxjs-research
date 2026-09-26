-- THE BATCHING OPERATOR, AS A PROGRAM.
--
-- `batchSimultaneousᵖ` is a former over the PLAIN tree: it takes a
-- stream of machine envelopes and hands back a stream of envelopes
-- carrying batched payloads.  It lives here rather than in a
-- verification module because it is an operator and not a claim -- the
-- harness runs it, and the proof quantifies over it.
--
-- ONE ENVELOPE OUT PER GROUP IN, AND THE GROUP IS WHAT `batchSyncᵉ`
-- HANDS OVER.  The subscribe frame's emits arrive as ONE group, so the
-- whole of burst 0 is in hand at once and is batched as a list: one
-- batch per instant, in order of the instant's first emit, holding every value that instant carried, and
-- no batch for an instant with no values.  The batches ride ONE output
-- envelope as its value events, so an envelope may carry several
-- batches or none -- the subscriber sees the batches, and the envelope
-- around them is bookkeeping the top line never compares.
--
-- THE ENVELOPE'S TOKENS ARE FORWARDED FROM THE GROUP'S FIRST EMIT,
-- because `uniqᵗ` has no term former: only `mintᵉ` introduces one, so
-- that no program can forge a token in use.  A group is nonempty by
-- construction, which is what makes the forwarding total.
--
-- WHAT THIS DOES NOT YET DO is batch a LATER arrival's emits: after the
-- subscribe frame `batchSyncᵉ` hands over singletons, and each is
-- batched alone.
module Rx.Batch where

open import Data.List using (List; _∷_)
open import Data.Bool using (true; false)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp      using (Ctx; Ty; Exp; Tm; listᵗ; uniqᵗ; boolᵗ; _×ᵗ_; varᵗ; bool̂; fstᵗ; sndᵗ;
  pairᵗ; nilᵗ; consᵗ; foldᵗ; ifᵗ; primᵗ; eqᵘ; appendᵗ; revᵗ; renTm; mapᵉ; batchSyncᵉ)
open import Rx.Envelope using (machineEmitᵗ; eventsᵛ; instantᵛ; sourceᵛ; kindᵛ; instEmitᵛ;
  valueᵛ; splitEventsᵛ)

module _ {n} {Γ : Ctx n} {Δᵍ Δ : List Ty} where

  -- past the element and the accumulator a `foldᵗ` body binds
  ⇑ : ∀ {Θ x y r} → Tm Γ Δᵍ Δ Θ r → Tm Γ Δᵍ Δ (x ∷ y ∷ Θ) r
  ⇑ = renTm (λ z → z) (λ z → z) (λ z → there (there z))

  -- this emit's own payloads, at the author's type
  payloadsᵇ : ∀ {Θ a} → Tm Γ Δᵍ Δ Θ (machineEmitᵗ a) → Tm Γ Δᵍ Δ Θ (listᵗ a)
  -- `b` is pinned because only the payload component is used, so
  -- nothing else would determine the retagging type
  payloadsᵇ {a = a} e = fstᵗ (sndᵗ (splitEventsᵛ {b = a} (eventsᵛ e)))

  memberᵇ : ∀ {Θ} → Tm Γ Δᵍ Δ Θ uniqᵗ → Tm Γ Δᵍ Δ Θ (listᵗ uniqᵗ) → Tm Γ Δᵍ Δ Θ boolᵗ
  memberᵇ u us = foldᵗ us (bool̂ false)
    (ifᵗ (varᵗ (there (here refl))) (bool̂ true)
         (primᵗ eqᵘ (pairᵗ (varᵗ (here refl)) (⇑ u))))

  nullᵇ : ∀ {Θ s} → Tm Γ Δᵍ Δ Θ (listᵗ s) → Tm Γ Δᵍ Δ Θ boolᵗ
  nullᵇ xs = foldᵗ xs (bool̂ true) (bool̂ false)

  -- every value the list's emits carry under instant u
  valuesAtᵇ : ∀ {Θ a} → Tm Γ Δᵍ Δ Θ uniqᵗ → Tm Γ Δᵍ Δ Θ (listᵗ (machineEmitᵗ a))
            → Tm Γ Δᵍ Δ Θ (listᵗ a)
  valuesAtᵇ u es = foldᵗ es nilᵗ
    (ifᵗ (primᵗ eqᵘ (pairᵗ (instantᵛ (varᵗ (here refl))) (⇑ u)))
         (appendᵗ (varᵗ (there (here refl))) (payloadsᵇ (varᵗ (here refl))))
         (varᵗ (there (here refl))))

  -- a list's batches, values only: the instants seen so far
  -- and the batches so far, reversed while the fold runs
  batchesᵇ : ∀ {Θ a} → Tm Γ Δᵍ Δ Θ (listᵗ (machineEmitᵗ a)) → Tm Γ Δᵍ Δ Θ (listᵗ (listᵗ a))
  batchesᵇ {Θ} {a} es = revᵗ (sndᵗ (foldᵗ es (pairᵗ nilᵗ nilᵗ) body))
    where
    A : Ty
    A = listᵗ uniqᵗ ×ᵗ listᵗ (listᵗ a)

    body : Tm Γ Δᵍ Δ (machineEmitᵗ a ∷ A ∷ Θ) A
    body = ifᵗ (memberᵇ i (fstᵗ acc)) acc
               (pairᵗ (consᵗ i (fstᵗ acc))
                      (ifᵗ (nullᵇ vs) (sndᵗ acc) (consᵗ vs (sndᵗ acc))))
      where
      acc = varᵗ (there (here refl))
      i   = instantᵛ (varᵗ (here refl))
      vs  = valuesAtᵇ i (⇑ es)

  -- one group in, one envelope out: a value event per batch, under the
  -- group's first emit's tokens
  groupEmitᵇ : ∀ {Θ a} → Tm Γ Δᵍ Δ Θ (machineEmitᵗ a ×ᵗ listᵗ (machineEmitᵗ a))
             → Tm Γ Δᵍ Δ Θ (machineEmitᵗ (listᵗ a))
  groupEmitᵇ g =
    instEmitᵛ (foldᵗ (revᵗ (batchesᵇ (consᵗ (fstᵗ g) (sndᵗ g)))) nilᵗ
                     (consᵗ (valueᵛ (varᵗ (here refl))) (varᵗ (there (here refl)))))
              (instantᵛ (fstᵗ g)) (sourceᵛ (fstᵗ g)) (kindᵛ (fstᵗ g))

batchSimultaneousᵖ :
  ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {a : Ty}
  → Exp Γ Δᵍ Δ Θ (machineEmitᵗ a)
  → Exp Γ Δᵍ Δ Θ (machineEmitᵗ (listᵗ a))
batchSimultaneousᵖ e = mapᵉ (groupEmitᵇ (varᵗ (here refl))) (batchSyncᵉ e)
