-- THE BATCHING OPERATOR, AS A PROGRAM.
--
-- `batchSimultaneousᵖ` is a former over the PLAIN tree: it takes a
-- stream of machine InstEmits and hands back a stream of InstEmits
-- carrying batched payloads.  It lives here rather than in a
-- verification module because it is an operator and not a claim -- the
-- harness runs it, and the proof quantifies over it.
--
-- ONE INSTEMIT OUT PER GROUP IN, AND THE GROUP IS WHAT `batchSyncᵉ`
-- HANDS OVER: the whole subscribe frame at once, then one emit per
-- arrival.  Within a group the batches are one per instant, in order of
-- the instant's first emit, holding every value that instant carried;
-- the batches ride the output InstEmit as its value events, so an
-- InstEmit may carry several batches or none -- the subscriber sees the
-- batches, and the InstEmit around them is bookkeeping the top line
-- never compares.
--
-- AN INSTANT STAYS OPEN ACROSS GROUPS, AND CLOSES LAZILY.  A later
-- instant can arrive as several groups -- a share's delivery reaching
-- two subscribers is two emits one tick apart in the second run -- so
-- the last instant a group touched is carried in the scan's state, and
-- its batch leaves when a group brings a different instant, or with
-- the group whose events complete the stream.  The twin's online
-- batcher closes the same way when it has no obligations to count;
-- this one never counts them.
--
-- THE TOKENS ARE FORWARDED FROM THE GROUP'S FIRST EMIT, because
-- `uniqᵗ` has no term former: only `mintᵉ` introduces one, so that no
-- program can forge a token in use.  The one mint here stands for the
-- instant open before anything arrived, which no emit can carry.
module SExp.Batch where

open import Data.List using (List; _∷_)
open import Data.Bool using (true; false)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp      using (Ctx; Ty; Exp; Tm; listᵗ; uniqᵗ; boolᵗ; _×ᵗ_; varᵗ; bool̂; unit̂; fstᵗ; sndᵗ;
  pairᵗ; nilᵗ; consᵗ; inlᵗ; foldᵗ; ifᵗ; letᵗ; primᵗ; eqᵘ; appendᵗ; revᵗ; renTm; renExp; mapᵉ; scanᵉ;
  mintᵉ; batchSyncᵉ)
open import SExp.InstEmit using (machineEmitᵗ; eventsᵛ; instantᵛ; sourceᵛ; kindᵛ; instEmitᵛ;
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

  -- the stream completes with one of the list's emits
  finᵇ : ∀ {Θ a} → Tm Γ Δᵍ Δ Θ (listᵗ (machineEmitᵗ a)) → Tm Γ Δᵍ Δ Θ boolᵗ
  finᵇ {a = a} es = foldᵗ es (bool̂ false)
    (ifᵗ (varᵗ (there (here refl))) (bool̂ true)
         (sndᵗ (sndᵗ (splitEventsᵛ {b = a} (eventsᵛ (varᵗ (here refl)))))))

  -- the list's instants other than o, in order of first appearance
  newInstantsᵇ : ∀ {Θ a} → Tm Γ Δᵍ Δ Θ uniqᵗ → Tm Γ Δᵍ Δ Θ (listᵗ (machineEmitᵗ a))
               → Tm Γ Δᵍ Δ Θ (listᵗ uniqᵗ)
  newInstantsᵇ o es = revᵗ (foldᵗ es nilᵗ
    (ifᵗ (primᵗ eqᵘ (pairᵗ i (⇑ o))) acc
         (ifᵗ (memberᵇ i acc) acc (consᵗ i acc))))
    where
    i   = instantᵛ (varᵗ (here refl))
    acc = varᵗ (there (here refl))

  -- the nonempty lists, in reverse
  keepRevᵇ : ∀ {Θ a} → Tm Γ Δᵍ Δ Θ (listᵗ (listᵗ a)) → Tm Γ Δᵍ Δ Θ (listᵗ (listᵗ a))
  keepRevᵇ xs = foldᵗ xs nilᵗ
    (ifᵗ (nullᵇ (varᵗ (here refl))) (varᵗ (there (here refl)))
         (consᵗ (varᵗ (here refl)) (varᵗ (there (here refl)))))

  -- one group against the open instant: the instant left open, and the
  -- batches closed, in order.  The open instant's values come first, the
  -- group's instants follow it, and every one but the last closes --
  -- the last too when the group completes the stream.
  closeGroupᵇ : ∀ {Θ a} → Tm Γ Δᵍ Δ Θ (uniqᵗ ×ᵗ listᵗ a) → Tm Γ Δᵍ Δ Θ (listᵗ (machineEmitᵗ a))
              → Tm Γ Δᵍ Δ Θ ((uniqᵗ ×ᵗ listᵗ a) ×ᵗ listᵗ (listᵗ a))
  closeGroupᵇ {Θ} {a} op es = letᵗ run (pairᵗ op nilᵗ) finish
    where
    Run : Ty
    Run = listᵗ (listᵗ a) ×ᵗ (uniqᵗ ×ᵗ listᵗ a)

    -- the batches closed so far, reversed, and the instant still open
    run : Tm Γ Δᵍ Δ Θ Run
    run = foldᵗ (newInstantsᵇ (fstᵗ op) es)
                (pairᵗ nilᵗ (pairᵗ (fstᵗ op) (appendᵗ (sndᵗ op) (valuesAtᵇ (fstᵗ op) es))))
                (pairᵗ (consᵗ (sndᵗ (sndᵗ acc)) (fstᵗ acc))
                       (pairᵗ (varᵗ (here refl)) (valuesAtᵇ (varᵗ (here refl)) (⇑ es))))
      where
      acc = varᵗ (there (here refl))

    finish : Tm Γ Δᵍ Δ (Run ∷ Θ) ((uniqᵗ ×ᵗ listᵗ a) ×ᵗ listᵗ (listᵗ a))
    finish = ifᵗ (finᵇ (↑ es))
                 (pairᵗ (pairᵗ (fstᵗ (sndᵗ r)) nilᵗ) (keepRevᵇ (consᵗ (sndᵗ (sndᵗ r)) (fstᵗ r))))
                 (pairᵗ (sndᵗ r) (keepRevᵇ (fstᵗ r)))
      where
      r = varᵗ (here refl)
      ↑ = renTm (λ z → z) (λ z → z) there

  -- the batches as one InstEmit's value events, under the group's first
  -- emit's tokens
  batchEmitᵇ : ∀ {Θ a} → Tm Γ Δᵍ Δ Θ (machineEmitᵗ a) → Tm Γ Δᵍ Δ Θ (listᵗ (listᵗ a))
             → Tm Γ Δᵍ Δ Θ (machineEmitᵗ (listᵗ a))
  batchEmitᵇ e bs =
    instEmitᵛ (foldᵗ (revᵗ bs) nilᵗ (consᵗ (valueᵛ (varᵗ (here refl))) (varᵗ (there (here refl)))))
              (instantᵛ e) (sourceᵛ e) (kindᵛ e)

batchSimultaneousᵖ :
  ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {a : Ty}
  → Exp Γ Δᵍ Δ Θ (machineEmitᵗ a)
  → Exp Γ Δᵍ Δ Θ (machineEmitᵗ (listᵗ a))
batchSimultaneousᵖ {Θ = Θ} {a = a} e =
  mintᵉ (mapᵉ (sndᵗ (varᵗ (here refl)))
              (scanᵉ step seed (batchSyncᵉ (renExp (λ z → z) (λ z → z) there e))))
  where
  -- the open instant and its values, and the InstEmit put out
  S : Ty
  S = (uniqᵗ ×ᵗ listᵗ a) ×ᵗ machineEmitᵗ (listᵗ a)

  seed : Tm _ _ _ (uniqᵗ ∷ Θ) S
  seed = pairᵗ (pairᵗ tok nilᵗ) (instEmitᵛ nilᵗ tok tok (inlᵗ unit̂))
    where
    tok = varᵗ (here refl)

  step : Tm _ _ _ ((S ×ᵗ (machineEmitᵗ a ×ᵗ listᵗ (machineEmitᵗ a))) ∷ uniqᵗ ∷ Θ) S
  step = letᵗ (closeGroupᵇ (fstᵗ (fstᵗ p)) (consᵗ (fstᵗ g) (sndᵗ g))) (fstᵗ p)
              (pairᵗ (fstᵗ (varᵗ (here refl)))
                     (batchEmitᵇ (renTm (λ z → z) (λ z → z) there (fstᵗ g)) (sndᵗ (varᵗ (here refl)))))
    where
    p = varᵗ (here refl)
    g = sndᵗ p
