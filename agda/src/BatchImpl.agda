-- The implementation-side port of batchSimultaneous, and the correspondence
-- theorem relating it to the specification.
--
-- The TS implementation cannot look ahead: it buffers the values of the
-- current instant and flushes when the instant is over (the provenance
-- memory's totalNum/awaitingValueCount windows exist to *decide* that flush
-- point without timestamps). Denotationally, its observable behavior is this
-- accumulate-and-flush fold. The correspondence theorem says the fold agrees
-- with the specification (group equal Times) on EVERY stream — so on the
-- denotation of every combination of primitives, at any depth.
--
-- (Refining the fold to the count-based memory itself — proving that the
-- totalNum bookkeeping computes exactly these flush points — is the
-- remaining step toward the rxjs machinery, tracked in the README.)
module BatchImpl where

open import Prelude
open import Time
open import TimedObs
open import Diamond

-- the port: buffer the running instant, flush when the time changes
batchAcc : {A : Set} → Time → List A → TimedObs A → TimedObs (List A)
batchAcc t acc [] = (t , acc) ∷ []
batchAcc t acc ((t′ , v) ∷ xs) =
  if timeEq t t′
  then batchAcc t (acc ++ (v ∷ [])) xs
  else ((t , acc) ∷ batchAcc t′ (v ∷ []) xs)

batchImpl : {A : Set} → TimedObs A → TimedObs (List A)
batchImpl []             = []
batchImpl ((t , v) ∷ xs) = batchAcc t (v ∷ []) xs

-- joinHead t vs S: prepend the values vs to S's first group when the times
-- match; the bridge between the fold's accumulator and the specification
joinHead : {A : Set} → Time → List A → TimedObs (List A) → TimedObs (List A)
joinHead t vs [] = (t , vs) ∷ []
joinHead t vs ((t′ , g) ∷ rest) =
  if timeEq t t′
  then ((t , vs ++ g) ∷ rest)
  else ((t , vs) ∷ (t′ , g) ∷ rest)

insert-join : {A : Set} (t : Time) (v : A) (s : TimedObs (List A))
  → insertBatch t v s ≡ joinHead t (v ∷ []) s
insert-join t v [] = refl
insert-join t v ((t′ , g) ∷ rest) with timeEq t t′
... | true  = refl
... | false = refl

join-snoc : {A : Set} (t : Time) (acc : List A) (v : A) (s : TimedObs (List A))
  → joinHead t (acc ++ (v ∷ [])) s ≡ joinHead t acc (insertBatch t v s)
join-snoc t acc v [] rewrite timeEq-refl t = refl
join-snoc t acc v ((t″ , g) ∷ rest) with timeEq t t″
... | true  rewrite timeEq-refl t | ++-snoc acc v g = refl
... | false rewrite timeEq-refl t = refl

joinHead-neq : {A : Set} (t t′ : Time) (acc : List A) (v : A)
               (s : TimedObs (List A))
  → timeEq t t′ ≡ false
  → joinHead t acc (insertBatch t′ v s) ≡ (t , acc) ∷ insertBatch t′ v s
joinHead-neq t t′ acc v [] ne rewrite ne = refl
joinHead-neq t t′ acc v ((t″ , g) ∷ rest) ne with timeEq t′ t″
... | true  rewrite ne = refl
... | false rewrite ne = refl

batchAcc-spec : {A : Set} (t : Time) (acc : List A) (xs : TimedObs A)
  → batchAcc t acc xs ≡ joinHead t acc (batchSpec xs)
batchAcc-spec t acc [] = refl
batchAcc-spec t acc ((t′ , v) ∷ xs) with timeEq t t′ in e
... | true rewrite timeEq-sound t t′ e =
  trans (batchAcc-spec t′ (acc ++ (v ∷ [])) xs)
        (join-snoc t′ acc v (batchSpec xs))
... | false =
  trans (cong (_∷_ (t , acc))
          (trans (batchAcc-spec t′ (v ∷ []) xs)
                 (sym (insert-join t′ v (batchSpec xs)))))
        (sym (joinHead-neq t t′ acc v (batchSpec xs) e))

-- THE CORRESPONDENCE THEOREM: the implementation's accumulate-and-flush
-- behavior IS the specification, on every stream whatsoever
batchImpl-spec : {A : Set} (xs : TimedObs A) → batchImpl xs ≡ batchSpec xs
batchImpl-spec []             = refl
batchImpl-spec ((t , v) ∷ xs) =
  trans (batchAcc-spec t (v ∷ []) xs)
        (sym (insert-join t v (batchSpec xs)))

-- corollary: the implementation satisfies the anchor law
impl-diamond : {A : Set} (xs : TimedObs A) → StrictMono xs
  → batchImpl (mergeT xs xs) ≡ mapT dbl xs
impl-diamond xs m = trans (batchImpl-spec (mergeT xs xs)) (diamond xs m)
