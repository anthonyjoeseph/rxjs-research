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
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst₂)

open import adequacy.Adequacy using (run; adequacy)
open import denotation.MonotonicList using (ticks; inFrame; within; sameTick)
open import denotation.MonotonicList.Events using (_≟ᵖ_; Events; Events∞; out; skip; end; hush; tick; Pos; Timeline; root)
open import denotation.Order using (Item; val; fin; silent; Shows; ShowsIn; nil; done⁺; quiet⁺; at⁺; emit⁺; stall⁺; close⁺)
open import denotation.Observe using (events)
open import simultaneous.InstEmit using (InstEmit)
open import simultaneous.SObs using (SObs; module Elaborate)
import simultaneous.Spec as Spec
open Spec _≟ᵖ_ using (batchSimultaneousᴰ)
open import simultaneous.Readings using (values; over; FiniteInstants; stamped; closed)
open import simultaneous.Statement using (batchedObs; elaborated; batched; left-to-right; batchable)

open Elaborate {C = Timeline} _≟ᵖ_ root using (elaborate)
open Events∞ using (force)

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

-- A reader's prefix is the first n events, read: each value shown is an
-- `out`, a stall a `skip`, and the run's end its `end` or `hush`.  Both
-- by recursion through the frames `ticks` builds, splitting on whether
-- the next event is still in the frame.
mutual
  shown-read : ∀ {A} (e : Events A) {is} → Shows (ticks e) is → Σ ℕ λ n → Reads is n e
  shown-read (out p a r) nil             = 0 , refl , refl
  shown-read (out p a r) (at⁺ nil)       = 0 , refl , refl
  shown-read (out p a r) (at⁺ (emit⁺ d)) with shown-readIn (force r) d
  ... | n , v , o = suc n , cong (a ∷_) v , o
  shown-read (skip p r)  nil              = 0 , refl , refl
  shown-read (skip p r)  (at⁺ nil)        = 0 , refl , refl
  shown-read (skip p r)  (at⁺ (stall⁺ d)) with shown-readIn (force r) d
  ... | n , v , o = suc n , v , o
  shown-read (end c)     nil             = 0 , refl , refl
  shown-read (end c)     done⁺           = 1 , refl , refl
  shown-read hush        nil             = 0 , refl , refl
  shown-read hush        quiet⁺          = 1 , refl , refl

  shown-readIn : ∀ {A t} (e : Events A) {is} → ShowsIn t (inFrame t e) is → Σ ℕ λ n → Reads is n e
  shown-readIn {t = t} e d = shown-readWithin e (sameTick t e) d

  shown-readWithin : ∀ {A t} (e : Events A) b {is} → ShowsIn t (within t e b) is → Σ ℕ λ n → Reads is n e
  shown-readWithin (out p a r) true  nil        = 0 , refl , refl
  shown-readWithin (out p a r) true  (emit⁺ d)  with shown-readIn (force r) d
  ... | n , v , o = suc n , cong (a ∷_) v , o
  shown-readWithin (skip p r)  true  nil        = 0 , refl , refl
  shown-readWithin (skip p r)  true  (stall⁺ d) with shown-readIn (force r) d
  ... | n , v , o = suc n , v , o
  shown-readWithin (out p a r) false nil        = 0 , refl , refl
  shown-readWithin (out p a r) false (close⁺ d) = shown-read (out p a r) d
  shown-readWithin (skip p r)  false nil        = 0 , refl , refl
  shown-readWithin (skip p r)  false (close⁺ d) = shown-read (skip p r) d
  shown-readWithin (end c)     b     nil        = 0 , refl , refl
  shown-readWithin (end c)     b     (close⁺ d) = shown-read (end c) d
  shown-readWithin hush        b     nil        = 0 , refl , refl
  shown-readWithin hush        b     (close⁺ d) = shown-read hush d

mutual
  read-shown : ∀ {A} (e : Events A) n → Σ (List (Item A)) λ is → Shows (ticks e) is × Reads is n e
  read-shown e           zero    = [] , nil , refl , refl
  read-shown (out p a r) (suc n) with read-shownIn (force r) n
  ... | is , d , v , o = val (tick p) a ∷ is , at⁺ (emit⁺ d) , cong (a ∷_) v , o
  read-shown (skip p r)  (suc n) with read-shownIn (force r) n
  ... | is , d , v , o = is , at⁺ (stall⁺ d) , v , o
  read-shown (end c)     (suc n) = fin ∷ [] , done⁺ , refl , refl
  read-shown hush        (suc n) = silent ∷ [] , quiet⁺ , refl , refl

  read-shownIn : ∀ {A} {t} (e : Events A) n → Σ (List (Item A)) λ is → ShowsIn t (inFrame t e) is × Reads is n e
  read-shownIn {t = t} e n = read-shownWithin e (sameTick t e) n

  read-shownWithin : ∀ {A} {t} (e : Events A) b n → Σ (List (Item A)) λ is → ShowsIn t (within t e b) is × Reads is n e
  read-shownWithin e b zero = [] , nil , refl , refl
  read-shownWithin {t = t} (out p a r) true (suc n) with read-shownIn (force r) n
  ... | is , d , v , o = val t a ∷ is , emit⁺ d , cong (a ∷_) v , o
  read-shownWithin (skip p r) true (suc n) with read-shownIn (force r) n
  ... | is , d , v , o = is , stall⁺ d , v , o
  read-shownWithin (out p a r) false (suc n) with read-shown (out p a r) (suc n)
  ... | is , d , ro = is , close⁺ d , ro
  read-shownWithin (skip p r) false (suc n) with read-shown (skip p r) (suc n)
  ... | is , d , ro = is , close⁺ d , ro
  read-shownWithin (end c) b (suc n) with read-shown (end c) (suc n)
  ... | is , d , ro = is , close⁺ d , ro
  read-shownWithin hush b (suc n) with read-shown hush (suc n)
  ... | is , d , ro = is , close⁺ d , ro

joinedᴾ : ∀ {A} → List (InstEmit Pos (List A)) → List A
joinedᴾ vs = concat (map proj₂ (stamped vs))

groupedᴾ : ∀ {A} → List (InstEmit Pos A) → Bool → List (Pos × List A)
groupedᴾ vs b = closed b (batchSimultaneousᴰ (stamped vs))

Left-To-Rightᴾ : Set₁
Left-To-Rightᴾ = ∀ {A} (o : SObs [] A) →
  (∀ {is} → Shows (run (batchedObs o)) is →
     Σ (List (Item A)) λ js → Shows (run o) js × Prefix _≡_ (joinedᴾ (valsᴵ is)) (valsᴵ js)) ×
  (FiniteInstants (events o) → ∀ {js} → Shows (run o) js →
     Σ (List (Item (InstEmit Pos (List A)))) λ is → Shows (run (batchedObs o)) is × Prefix _≡_ (valsᴵ js) (joinedᴾ (valsᴵ is)))

Batchableᴾ : Set₁
Batchableᴾ = ∀ {A} (o : SObs [] A) →
  (∀ {is} → Shows (run (batchedObs o)) is →
     Σ (List (Item (InstEmit Pos A))) λ js → Shows (run (elaborate o)) js ×
       Prefix _≡_ (stamped (valsᴵ is)) (groupedᴾ (valsᴵ js) (endedᴵ js))) ×
  (∀ {js} → Shows (run (elaborate o)) js →
     Σ (List (Item (InstEmit Pos (List A)))) λ is → Shows (run (batchedObs o)) is ×
       Prefix _≡_ (groupedᴾ (valsᴵ js) (endedᴵ js)) (stamped (valsᴵ is)))

left-to-rightᴾ : Left-To-Rightᴾ
left-to-rightᴾ o = ahead , behind
  where
  ahead : ∀ {is} → Shows (run (batchedObs o)) is → Σ _ λ js → Shows (run o) js × Prefix _≡_ (joinedᴾ (valsᴵ is)) (valsᴵ js)
  ahead s with shown-read (batched o) (proj₁ (adequacy (batchedObs o)) s)
  ... | n , vs , _ with proj₁ (left-to-right o) n
  ...   | m , pre with read-shown (events o) m
  ...     | js , sj , vs′ , _ = js , proj₂ (adequacy o) sj , subst₂ (Prefix _≡_) (cong joinedᴾ (sym vs)) (sym vs′) pre

  behind : FiniteInstants (events o) → ∀ {js} → Shows (run o) js → Σ _ λ is → Shows (run (batchedObs o)) is × Prefix _≡_ (valsᴵ js) (joinedᴾ (valsᴵ is))
  behind fi s with shown-read (events o) (proj₁ (adequacy o) s)
  ... | m , vs , _ with proj₂ (left-to-right o) fi m
  ...   | n , pre with read-shown (batched o) n
  ...     | is , si , vs′ , _ = is , proj₂ (adequacy (batchedObs o)) si , subst₂ (Prefix _≡_) (sym vs) (cong joinedᴾ (sym vs′)) pre

batchableᴾ : Batchableᴾ
batchableᴾ o = ahead , behind
  where
  ahead : ∀ {is} → Shows (run (batchedObs o)) is → Σ _ λ js → Shows (run (elaborate o)) js × Prefix _≡_ (stamped (valsᴵ is)) (groupedᴾ (valsᴵ js) (endedᴵ js))
  ahead s with shown-read (batched o) (proj₁ (adequacy (batchedObs o)) s)
  ... | n , vs , _ with proj₁ (batchable o) n
  ...   | m , pre with read-shown (elaborated o) m
  ...     | js , sj , vs′ , en = js , proj₂ (adequacy (elaborate o)) sj , subst₂ (Prefix _≡_) (cong stamped (sym vs)) (cong₂ groupedᴾ (sym vs′) (sym en)) pre

  behind : ∀ {js} → Shows (run (elaborate o)) js → Σ _ λ is → Shows (run (batchedObs o)) is × Prefix _≡_ (groupedᴾ (valsᴵ js) (endedᴵ js)) (stamped (valsᴵ is))
  behind s with shown-read (elaborated o) (proj₁ (adequacy (elaborate o)) s)
  ... | m , vs , en with proj₂ (batchable o) m
  ...   | n , pre with read-shown (batched o) n
  ...     | is , si , vs′ , _ = is , proj₂ (adequacy (batchedObs o)) si , subst₂ (Prefix _≡_) (cong₂ groupedᴾ (sym vs) (sym en)) (cong stamped (sym vs′)) pre
