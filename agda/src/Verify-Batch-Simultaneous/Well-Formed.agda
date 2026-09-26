------------------------------------------------------------------
-- WHAT IT MEANS FOR A RUN'S INSTANTS TO BE RIGHT, AND NOTHING ELSE.
--
-- A run is the impl's output cut at the evaluator's ARRIVALS
-- (`Rx.Arrivals`): arrival zero is the `subscribe()` frame, and each
-- later one is a single scheduled delivery -- one `.next()` of a hot
-- input, one async emission of a cold one -- together with its whole
-- synchronous cascade.  An instant is meant to be exactly that, so the
-- record below asks for one instant per arrival and says so in the two
-- halves that each rule out one cheat: `same` refuses a fresh instant
-- per emit, `distinct` refuses one instant for everything.  The cut is
-- the fixed evaluator's, never the impl's, so neither half is the
-- impl's to arrange.
--
-- IT IS DELIBERATELY NOT A SECOND SEMANTICS (Anthony).  A per-former
-- definition -- `WellFormed (merge a b)` from its parts -- would have
-- to say what `switchAll` cancels, when a share connects and what
-- order a diamond's emits come in, which is the evaluator again,
-- written a second time and free to disagree with the first.  Reading
-- the evaluator's own cut leaks one of its internals, and buys a
-- definition four fields long.
--
-- `ends` IS WHAT LETS A BATCHER NOT WAIT.  The envelope marks the last
-- emit of every arrival and no earlier one, read by the protocol's
-- counting automaton, so a batch can leave with the emit that ends its
-- instant instead of with the next arrival's first.
------------------------------------------------------------------
module Verify-Batch-Simultaneous.Well-Formed where

open import Data.Bool    using (Bool; true; false; T; if_then_else_)
open import Data.Empty   using (⊥-elim)
open import Data.List    using (List; []; _∷_; _++_; _∷ʳ_; concat; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ; map-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to mapᴬ; head to headᴬ)
open import Data.List.Relation.Unary.All.Properties using (++⁺; concat⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Nat     using (_≟_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)

open import Rx.Prim     using (Id; InstEvent; value; InstEmit)
open import Rx.Protocol using (ProtocolSt; protocol-init; stepProtocol; runProtocol;
                               Accepted; paidOff)
import Spec
open Spec Id _≟_ using (spec-batchSimultaneous; batchFrom)

------------------------------------------------------------------
-- What a subscriber sees of a run, and what the spec is handed.
------------------------------------------------------------------

valuesᴱ : ∀ {A : Set} → List (InstEvent A) → List A
valuesᴱ []             = []
valuesᴱ (value v ∷ es) = v ∷ valuesᴱ es
valuesᴱ (_       ∷ es) = valuesᴱ es

-- every value the emits carry, in order; a valueless emit contributes
-- nothing, which is what a subscriber would see of it
valuesOf : ∀ {A : Set} → List (InstEmit A) → List A
valuesOf []       = []
valuesOf (x ∷ xs) = valuesᴱ (InstEmit.events x) ++ valuesOf xs

-- the spec's input: every value tagged with its emit's instant
toSpec : ∀ {A : Set} → List (InstEmit A) → List (Id × A)
toSpec []       = []
toSpec (x ∷ xs) = map (InstEmit.instant x ,_) (valuesᴱ (InstEmit.events x)) ++ toSpec xs

------------------------------------------------------------------
-- `ends`, read by the protocol automaton.
------------------------------------------------------------------

-- the open instant is paid off: nothing more can join it
closes : ProtocolSt → Bool
closes ps with ProtocolSt.current ps
... | just (_ , owed) = paidOff owed
... | nothing         = false

-- one arrival: every emit but the last leaves its instant open, and
-- the last one closes it
markStep : ∀ {A : Set} → Maybe ProtocolSt → List (InstEmit A) → Maybe ProtocolSt
markStep nothing    _        = nothing
markStep (just ps) []       = if closes ps then just ps else nothing
markStep (just ps) (y ∷ ys) = if closes ps then nothing else markStep (stepProtocol y ps) ys

marks : ∀ {A : Set} → ProtocolSt → List (InstEmit A) → Maybe ProtocolSt
marks ps []       = just ps
marks ps (x ∷ xs) = markStep (stepProtocol x ps) xs

endsFrom : ∀ {A : Set} → Maybe ProtocolSt → List (List (InstEmit A)) → Bool
endsFrom nothing    _           = false
endsFrom (just ps) []          = true
endsFrom (just ps) (arr ∷ run) = endsFrom (marks ps arr) run

ends? : ∀ {A : Set} → ProtocolSt → List (List (InstEmit A)) → Bool
ends? ps run = endsFrom (just ps) run

------------------------------------------------------------------
-- The record.
------------------------------------------------------------------

record WellFormed {A : Set} (run : List (List (InstEmit A))) : Set where
  field
    -- every emit of one arrival carries one instant
    same     : All (λ arr → Σ Id (λ i → All (λ x → InstEmit.instant x ≡ i) arr)) run
    -- emits of different arrivals carry different instants
    distinct : AllPairs (λ arr arr′ → All (λ x → All (λ y →
                 InstEmit.instant x ≢ InstEmit.instant y) arr′) arr) run
    -- the envelope obeys the protocol
    accepted : Accepted (runProtocol protocol-init (concat run))
    -- and marks the last emit of each arrival, and no earlier one
    ends     : T (ends? protocol-init run)

------------------------------------------------------------------
-- THE HUB: over a well-formed run the spec's batches are one per
-- arrival that carried a value, each holding that arrival's values in
-- order.  Only `same` and `distinct` are read.  Every README semantics
-- claim is this, applied to the arrivals of one program.
------------------------------------------------------------------

-- all of an arrival's values, or no batch if it carried none
batchOfValues : ∀ {A : Set} → List A → List (List A)
batchOfValues []       = []
batchOfValues (v ∷ vs) = (v ∷ vs) ∷ []

private
  toSpec-++ : ∀ {A : Set} (xs ys : List (InstEmit A))
            → toSpec (xs ++ ys) ≡ toSpec xs ++ toSpec ys
  toSpec-++ []       ys = refl
  toSpec-++ (x ∷ xs) ys =
    trans (cong (map (InstEmit.instant x ,_) (valuesᴱ (InstEmit.events x)) ++_)
                (toSpec-++ xs ys))
          (sym (++-assoc (map (InstEmit.instant x ,_) (valuesᴱ (InstEmit.events x)))
                         (toSpec xs) (toSpec ys)))

  tagged : ∀ {A : Set} {P : Id → Set} {i} (vs : List A) → P i
         → All (λ p → P (proj₁ p)) (map (i ,_) vs)
  tagged []       pi = []
  tagged (v ∷ vs) pi = pi ∷ tagged vs pi

  All-toSpec : ∀ {A : Set} {P : Id → Set} {xs : List (InstEmit A)}
             → All (λ x → P (InstEmit.instant x)) xs → All (λ p → P (proj₁ p)) (toSpec xs)
  All-toSpec {xs = []}     []         = []
  All-toSpec {xs = x ∷ xs} (px ∷ pxs) =
    ++⁺ (tagged (valuesᴱ (InstEmit.events x)) px) (All-toSpec pxs)

  proj₂-tagged : ∀ {A : Set} (i : Id) (vs : List A) → map proj₂ (map (i ,_) vs) ≡ vs
  proj₂-tagged i []       = refl
  proj₂-tagged i (v ∷ vs) = cong (v ∷_) (proj₂-tagged i vs)

  toSpec-values : ∀ {A : Set} (xs : List (InstEmit A)) → map proj₂ (toSpec xs) ≡ valuesOf xs
  toSpec-values []       = refl
  toSpec-values {A} (x ∷ xs) =
    trans (map-++ (λ (p : Id × A) → proj₂ p) (map (InstEmit.instant x ,_) (valuesᴱ (InstEmit.events x))) (toSpec xs))
          (trans (cong (_++ map proj₂ (toSpec xs))
                       (proj₂-tagged (InstEmit.instant x) (valuesᴱ (InstEmit.events x))))
                 (cong (valuesᴱ (InstEmit.events x) ++_) (toSpec-values xs)))

  -- a run of one instant stays one batch
  batchFrom-same : ∀ {A : Set} i (vs : List A) (xs : List (Id × A))
                 → All (λ p → proj₁ p ≡ i) xs
                 → batchFrom i vs xs ≡ (vs ++ map proj₂ xs) ∷ []
  batchFrom-same i vs [] [] = cong (_∷ []) (sym (++-identityʳ vs))
  batchFrom-same i vs ((j , v) ∷ xs) (j≡i ∷ ps) with i ≟ j
  ... | yes _  = trans (batchFrom-same i (vs ∷ʳ v) xs ps)
                       (cong (_∷ []) (++-assoc vs (v ∷ []) (map proj₂ xs)))
  ... | no i≢j = ⊥-elim (i≢j (sym j≡i))

  -- and closes the moment a different instant arrives
  batchFrom-run : ∀ {A : Set} i (vs : List A) (xs ys : List (Id × A))
                → All (λ p → proj₁ p ≡ i) xs → All (λ p → i ≢ proj₁ p) ys
                → batchFrom i vs (xs ++ ys) ≡ (vs ++ map proj₂ xs) ∷ spec-batchSimultaneous ys
  batchFrom-run i vs [] [] [] [] = cong (_∷ []) (sym (++-identityʳ vs))
  batchFrom-run i vs [] ((j , v) ∷ ys) [] (i≢j ∷ _) with i ≟ j
  ... | yes i≡j = ⊥-elim (i≢j i≡j)
  ... | no _    = cong (_∷ spec-batchSimultaneous ((j , v) ∷ ys)) (sym (++-identityʳ vs))
  batchFrom-run i vs ((j , v) ∷ xs) ys (j≡i ∷ ps) qs with i ≟ j
  ... | yes _  = trans (batchFrom-run i (vs ∷ʳ v) xs ys ps qs)
                       (cong (_∷ spec-batchSimultaneous ys) (++-assoc vs (v ∷ []) (map proj₂ xs)))
  ... | no i≢j = ⊥-elim (i≢j (sym j≡i))

  spec-same : ∀ {A : Set} i (xs : List (Id × A)) → All (λ p → proj₁ p ≡ i) xs
            → spec-batchSimultaneous xs ≡ batchOfValues (map proj₂ xs)
  spec-same i []             []           = refl
  spec-same i ((.i , v) ∷ xs) (refl ∷ ps) = batchFrom-same i (v ∷ []) xs ps

  spec-++ : ∀ {A : Set} i (xs ys : List (Id × A))
          → All (λ p → proj₁ p ≡ i) xs → All (λ p → i ≢ proj₁ p) ys
          → spec-batchSimultaneous (xs ++ ys)
              ≡ spec-batchSimultaneous xs ++ spec-batchSimultaneous ys
  spec-++ i []              ys []          qs = refl
  spec-++ i ((.i , v) ∷ xs) ys (refl ∷ ps) qs =
    trans (batchFrom-run i (v ∷ []) xs ys ps qs)
          (sym (cong (_++ spec-batchSimultaneous ys) (batchFrom-same i (v ∷ []) xs ps)))

-- one arrival's spec batch is its values, if it had any
wf-arrival-batch : ∀ {A : Set} {i} (arr : List (InstEmit A))
                 → All (λ x → InstEmit.instant x ≡ i) arr
                 → spec-batchSimultaneous (toSpec arr) ≡ batchOfValues (valuesOf arr)
wf-arrival-batch {A} {i} arr same =
  trans (spec-same i (toSpec arr) (All-toSpec {A = A} {P = λ j → j ≡ i} {xs = arr} same))
        (cong batchOfValues (toSpec-values arr))

-- the whole run's batches are the arrivals', side by side
wf-batches : ∀ {A : Set} {run : List (List (InstEmit A))} → WellFormed run
           → spec-batchSimultaneous (toSpec (concat run))
               ≡ concat (map (λ arr → spec-batchSimultaneous (toSpec arr)) run)
wf-batches wf = go _ (WellFormed.same wf) (WellFormed.distinct wf)
  where
  go : ∀ {A : Set} (run : List (List (InstEmit A)))
     → All (λ arr → Σ Id (λ i → All (λ x → InstEmit.instant x ≡ i) arr)) run
     → AllPairs (λ arr arr′ → All (λ x → All (λ y →
         InstEmit.instant x ≢ InstEmit.instant y) arr′) arr) run
     → spec-batchSimultaneous (toSpec (concat run))
         ≡ concat (map (λ arr → spec-batchSimultaneous (toSpec arr)) run)
  go []                 []                  []            = refl
  go ([] ∷ run)         (_ ∷ sames)         (_ ∷ dists)   = go run sames dists
  go {A} ((x ∷ xs) ∷ run) ((i , sx ∷ sxs) ∷ sames) (far ∷ dists) =
    trans (cong (spec-batchSimultaneous {A = A}) (toSpec-++ (x ∷ xs) (concat run)))
          (trans (spec-++ i (toSpec (x ∷ xs)) (toSpec (concat run))
                          (All-toSpec {A = A} {P = λ j → j ≡ i} {xs = x ∷ xs} (sx ∷ sxs))
                          (All-toSpec {A = A} {P = λ j → i ≢ j} {xs = concat run} later))
                 (cong (spec-batchSimultaneous (toSpec (x ∷ xs)) ++_) (go run sames dists)))
    where
    later : All (λ y → i ≢ InstEmit.instant y) (concat run)
    later = concat⁺ (mapᴬ (λ h → mapᴬ (λ ne eq → ne (trans sx eq)) (headᴬ h)) far)
