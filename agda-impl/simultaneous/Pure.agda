{-# OPTIONS --guardedness #-}

-- THE SPEC ON THE PURE RUNTIME, carried across `adequacy`: what a reader
-- of the pure run sees, the batched program's and the plain one's, meets
-- `left-to-right` and `batchable`.  Both bodies are real; the gap is
-- only how a reader's prefix of `ticks e` and the first n events of `e`
-- read alike, which is about the denotation alone.
--
-- `coherent` does not cross.  `adequacy` keeps ticks and forgets
-- positions, and two timer cascades at one tick are two instants a
-- reader of the pure run cannot tell apart.  What does cross is each
-- value's tick, so a batch released late still shows on the pure run.
module simultaneous.Pure where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; concat; map)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; cong₂; subst₂)

open import adequacy.Adequacy using (run; adequacy)
open import denotation.MonotonicList using (ticks)
open import denotation.MonotonicList.Events using (Events)
open import denotation.Order using (Item; val; fin; silent; Shows)
open import denotation.Observe using (events)
open import simultaneous.InstEmit using (InstEmit; Provenance)
open import simultaneous.SObs using (SObs; elaborate)
open import simultaneous.Spec using (batchSimultaneousᴰ)
open import simultaneous.Readings using (values; over; FiniteInstants; stamped; closed)
open import simultaneous.Statement using (batchedObs; left-to-right; batchable)

-- A reader's prefix as the spec reads it: its values, and whether the
-- run is over.
valsᴵ : ∀ {A} → List (Item A) → List A
valsᴵ []             = []
valsᴵ (val _ a ∷ is) = a ∷ valsᴵ is
valsᴵ (fin ∷ is)     = valsᴵ is
valsᴵ (silent ∷ is)  = valsᴵ is

endedᴵ : ∀ {A} → List (Item A) → Bool
endedᴵ []             = false
endedᴵ (val _ _ ∷ is) = endedᴵ is
endedᴵ (fin ∷ _)      = true
endedᴵ (silent ∷ _)   = true

-- A reader's prefix and the first n events, read alike.
Reads : ∀ {A} → List (Item A) → ℕ → Events A → Set
Reads is n e = valsᴵ is ≡ values n e × endedᴵ is ≡ over n e

postulate
  shown-read : ∀ {A} (e : Events A) {is} → Shows (ticks e) is → Σ ℕ λ n → Reads is n e
  read-shown : ∀ {A} (e : Events A) n → Σ (List (Item A)) λ is → Shows (ticks e) is × Reads is n e

joinedᴾ : ∀ {A} → List (InstEmit (List A)) → List A
joinedᴾ vs = concat (map proj₂ (stamped vs))

groupedᴾ : ∀ {A} → List (InstEmit A) → Bool → List (Provenance × List A)
groupedᴾ vs b = closed b (batchSimultaneousᴰ (stamped vs))

Left-To-Rightᴾ : Set₁
Left-To-Rightᴾ = ∀ {A} (o : SObs [] A) →
  (∀ {is} → Shows (run (batchedObs o)) is →
     Σ (List (Item A)) λ js → Shows (run o) js × Prefix _≡_ (joinedᴾ (valsᴵ is)) (valsᴵ js)) ×
  (FiniteInstants (events o) → ∀ {js} → Shows (run o) js →
     Σ (List (Item (InstEmit (List A)))) λ is → Shows (run (batchedObs o)) is × Prefix _≡_ (valsᴵ js) (joinedᴾ (valsᴵ is)))

Batchableᴾ : Set₁
Batchableᴾ = ∀ {A} (o : SObs [] A) →
  (∀ {is} → Shows (run (batchedObs o)) is →
     Σ (List (Item (InstEmit A))) λ js → Shows (run (elaborate o)) js ×
       Prefix _≡_ (stamped (valsᴵ is)) (groupedᴾ (valsᴵ js) (endedᴵ js))) ×
  (∀ {js} → Shows (run (elaborate o)) js →
     Σ (List (Item (InstEmit (List A)))) λ is → Shows (run (batchedObs o)) is ×
       Prefix _≡_ (groupedᴾ (valsᴵ js) (endedᴵ js)) (stamped (valsᴵ is)))

left-to-rightᴾ : Left-To-Rightᴾ
left-to-rightᴾ o = ahead , behind
  where
  ahead : ∀ {is} → Shows (run (batchedObs o)) is → Σ _ λ js → Shows (run o) js × Prefix _≡_ (joinedᴾ (valsᴵ is)) (valsᴵ js)
  ahead s with shown-read (events (batchedObs o)) (proj₁ (adequacy (batchedObs o)) s)
  ... | n , vs , _ with proj₁ (left-to-right o) n
  ...   | m , pre with read-shown (events o) m
  ...     | js , sj , vs′ , _ = js , proj₂ (adequacy o) sj , subst₂ (Prefix _≡_) (cong joinedᴾ (sym vs)) (sym vs′) pre

  behind : FiniteInstants (events o) → ∀ {js} → Shows (run o) js → Σ _ λ is → Shows (run (batchedObs o)) is × Prefix _≡_ (valsᴵ js) (joinedᴾ (valsᴵ is))
  behind fi s with shown-read (events o) (proj₁ (adequacy o) s)
  ... | m , vs , _ with proj₂ (left-to-right o) fi m
  ...   | n , pre with read-shown (events (batchedObs o)) n
  ...     | is , si , vs′ , _ = is , proj₂ (adequacy (batchedObs o)) si , subst₂ (Prefix _≡_) (sym vs) (cong joinedᴾ (sym vs′)) pre

batchableᴾ : Batchableᴾ
batchableᴾ o = ahead , behind
  where
  ahead : ∀ {is} → Shows (run (batchedObs o)) is → Σ _ λ js → Shows (run (elaborate o)) js × Prefix _≡_ (stamped (valsᴵ is)) (groupedᴾ (valsᴵ js) (endedᴵ js))
  ahead s with shown-read (events (batchedObs o)) (proj₁ (adequacy (batchedObs o)) s)
  ... | n , vs , _ with proj₁ (batchable o) n
  ...   | m , pre with read-shown (events (elaborate o)) m
  ...     | js , sj , vs′ , en = js , proj₂ (adequacy (elaborate o)) sj , subst₂ (Prefix _≡_) (cong stamped (sym vs)) (cong₂ groupedᴾ (sym vs′) (sym en)) pre

  behind : ∀ {js} → Shows (run (elaborate o)) js → Σ _ λ is → Shows (run (batchedObs o)) is × Prefix _≡_ (groupedᴾ (valsᴵ js) (endedᴵ js)) (stamped (valsᴵ is))
  behind s with shown-read (events (elaborate o)) (proj₁ (adequacy (elaborate o)) s)
  ... | m , vs , en with proj₂ (batchable o) m
  ...   | n , pre with read-shown (events (batchedObs o)) n
  ...     | is , si , vs′ , _ = is , proj₂ (adequacy (batchedObs o)) si , subst₂ (Prefix _≡_) (cong₂ groupedᴾ (sym vs) (sym en)) (cong stamped (sym vs′)) pre
