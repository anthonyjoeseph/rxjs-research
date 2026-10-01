-- THE BATCHING OPERATOR, AS A PROGRAM.
--
-- `batchSimultaneousᵖ` is a former over the PLAIN tree: it takes a
-- stream of machine InstEmits and hands back a stream of InstEmits
-- carrying batched payloads.  It lives here rather than in a
-- verification module because it is an operator and not a claim -- the
-- harness runs it, and the proof quantifies over it.
--
-- IT CUTS WHERE THE SPEC CUTS: a batch is a maximal run of values under
-- one instant, and an emit carrying no value is invisible to it.  So
-- one scan carries the open instant and its values, and a value under
-- any other instant closes the batch.  An instant arriving as several
-- emits, at any distance apart, is one batch for as long as no other
-- instant's value comes between them, which is why nothing here groups
-- by synchrony.  Each batch rides an output InstEmit as one value
-- event under its own instant; an InstEmit closing nothing carries no
-- events, and is bookkeeping the top line never compares.
--
-- THE LAST BATCH LEAVES WHEN THE RUN COMPLETES, AND THE RUN SAYS SO
-- ONLY OUT OF BAND.  The twin batches on completion (`toArray`), and no
-- emit is obliged to carry the completion in its events.  So the run is
-- concatenated with a one-emit marker -- a merging `flattenᵉ` at one
-- lane subscribes it exactly when the run completes -- and the marker
-- closes the open batch.  A run that never completes keeps its last
-- batch.
--
-- THE TOKENS COME FROM THE STREAM, because `uniqᵗ` has no term former:
-- only `mintᵉ` introduces one, so that no program can forge a token in
-- use.  The one mint here stands for the instant open before anything
-- arrived, which no emit can carry.
module SExp.Batch where

open import Data.List using (List; []; _∷_)
open import Data.Bool using (true; false)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp      using (Ctx; Ty; Exp; Tm; listᵗ; uniqᵗ; boolᵗ; unitᵗ; obs; _×ᵗ_; _+ᵗ_; varᵗ;
  bool̂; unit̂; fstᵗ; sndᵗ; pairᵗ; nilᵗ; consᵗ; inlᵗ; inrᵗ; caseᵗ; foldᵗ; ifᵗ; primᵗ; eqᵘ; appendᵗ;
  strmᵗ; renExp; ofᵉ; mapᵉ; scanᵉ; mintᵉ; flattenᵉ; mergeᶠ)
open import SExp.InstEmit using (machineEmitᵗ; instEventᵗ; eventsᵛ; instantᵛ; sourceᵛ; kindᵛ;
  instEmitᵛ; valueᵛ; splitEventsᵛ)

module _ {n} {Γ : Ctx n} {Δᵍ Δ : List Ty} where

  -- this emit's own payloads, at the author's type
  payloadsᵇ : ∀ {Θ a} → Tm Γ Δᵍ Δ Θ (machineEmitᵗ a) → Tm Γ Δᵍ Δ Θ (listᵗ a)
  -- `b` is pinned because only the payload component is used, so
  -- nothing else would determine the retagging type
  payloadsᵇ {a = a} e = fstᵗ (sndᵗ (splitEventsᵛ {b = a} (eventsᵛ e)))

  nullᵇ : ∀ {Θ s} → Tm Γ Δᵍ Δ Θ (listᵗ s) → Tm Γ Δᵍ Δ Θ boolᵗ
  nullᵇ xs = foldᵗ xs (bool̂ true) (bool̂ false)

  -- one batch, as an InstEmit's events: none when it is empty
  batchEventsᵇ : ∀ {Θ a} → Tm Γ Δᵍ Δ Θ (listᵗ a) → Tm Γ Δᵍ Δ Θ (listᵗ (instEventᵗ uniqᵗ (listᵗ a)))
  batchEventsᵇ vs = ifᵗ (nullᵇ vs) nilᵗ (consᵗ (valueᵛ vs) nilᵗ)

batchSimultaneousᵖ :
  ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {a : Ty}
  → Exp Γ Δᵍ Δ Θ (machineEmitᵗ a)
  → Exp Γ Δᵍ Δ Θ (machineEmitᵗ (listᵗ a))
batchSimultaneousᵖ {Γ = Γ} {Δᵍ} {Δ} {Θ} {a} e =
  mintᵉ (mapᵉ (sndᵗ (varᵗ (here refl))) (scanᵉ step seed marked))
  where
  -- an emit of the run, or the marker that it completed
  X : Ty
  X = machineEmitᵗ a +ᵗ unitᵗ

  lane : Exp Γ Δᵍ Δ (uniqᵗ ∷ Θ) X → Tm Γ Δᵍ Δ (uniqᵗ ∷ Θ) ((unitᵗ +ᵗ X) ×ᵗ (unitᵗ +ᵗ obs X))
  lane x = pairᵗ (inlᵗ unit̂) (inrᵗ (strmᵗ x))

  marked : Exp Γ Δᵍ Δ (uniqᵗ ∷ Θ) X
  marked = flattenᵉ (mergeᶠ (just 1)) (ofᵉ (
    lane (mapᵉ (inlᵗ (varᵗ (here refl))) (renExp (λ z → z) (λ z → z) there e)) ∷
    lane (ofᵉ (inrᵗ unit̂ ∷ [])) ∷ []))

  -- the open instant and its values, and the InstEmit put out
  S : Ty
  S = (uniqᵗ ×ᵗ listᵗ a) ×ᵗ machineEmitᵗ (listᵗ a)

  seed : Tm Γ Δᵍ Δ (uniqᵗ ∷ Θ) S
  seed = pairᵗ (pairᵗ tok nilᵗ) (instEmitᵛ nilᵗ tok tok (inlᵗ unit̂))
    where
    tok = varᵗ (here refl)

  step : Tm Γ Δᵍ Δ ((S ×ᵗ X) ∷ uniqᵗ ∷ Θ) S
  step = caseᵗ (sndᵗ (varᵗ (here refl))) onEmit onEnd
    where
    -- inside an arm: the arm's own binder, then the step's argument
    open′ : ∀ {x} → Tm Γ Δᵍ Δ (x ∷ (S ×ᵗ X) ∷ uniqᵗ ∷ Θ) (uniqᵗ ×ᵗ listᵗ a)
    open′ = fstᵗ (fstᵗ (varᵗ (there (here refl))))

    o : ∀ {x} → Tm Γ Δᵍ Δ (x ∷ (S ×ᵗ X) ∷ uniqᵗ ∷ Θ) uniqᵗ
    o = fstᵗ open′

    os : ∀ {x} → Tm Γ Δᵍ Δ (x ∷ (S ×ᵗ X) ∷ uniqᵗ ∷ Θ) (listᵗ a)
    os = sndᵗ open′

    onEmit : Tm Γ Δᵍ Δ (machineEmitᵗ a ∷ (S ×ᵗ X) ∷ uniqᵗ ∷ Θ) S
    onEmit =
      ifᵗ (nullᵇ vs) (pairᵗ open′ nothing′)
        (ifᵗ (primᵗ eqᵘ (pairᵗ (instantᵛ em) o))
             (pairᵗ (pairᵗ o (appendᵗ os vs)) nothing′)
             (pairᵗ (pairᵗ (instantᵛ em) vs)
                    (instEmitᵛ (batchEventsᵇ os) o (sourceᵛ em) (kindᵛ em))))
      where
      em = varᵗ (here refl)
      vs = payloadsᵇ em
      nothing′ = instEmitᵛ nilᵗ (instantᵛ em) (sourceᵛ em) (kindᵛ em)

    onEnd : Tm Γ Δᵍ Δ (unitᵗ ∷ (S ×ᵗ X) ∷ uniqᵗ ∷ Θ) S
    onEnd = pairᵗ (pairᵗ o nilᵗ) (instEmitᵛ (batchEventsᵇ os) o o (inlᵗ unit̂))
