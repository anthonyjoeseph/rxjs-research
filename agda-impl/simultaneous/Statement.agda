{-# OPTIONS --guardedness #-}

-- THE SIMULTANEOUS SPEC, over the emission set, in one statement:
-- elaborate the author's program, put `batchSimultaneous` on top, and the
-- batched run, each batch stamped with the instant it leaves in, is the
-- spec's grouping of the plain run, each value stamped with the instant
-- it leaves in.  The stamps are the denotation's own
-- (`simultaneous.Relations`): no program can read one, and the
-- elaboration's names appear nowhere, so the batcher is held to a
-- property of stamps it never sees.
--
-- WHAT ONE EQUATION CLOSES.  Elaborating every program to `empty` fails
-- it: the grouping is not empty.  Stamping every emit alike fails it:
-- one batch where the grouping has one per instant.  Releasing a batch
-- late fails it: a batch released in the next instant carries that
-- instant's stamp, and no row of the grouping does.  Restamping a batch
-- to its release instant cannot be written: the stamp is read off the
-- batch's own position.  Holding a value to a later instant inside the
-- elaboration fails it: the plain run's stamps are the plain program's,
-- which the elaboration never touches.
--
-- WHAT IT DOES NOT PIN: where inside its instant a batch leaves, past the
-- instant's last value.  The batcher releases when its instant is over,
-- and the equation asks only that the batch leave within it, after its
-- last value.
--
-- AN INSTANT'S END IS A FACT OF THE ROWS, NOT OF WHAT IS SHOWN: work no
-- subscriber sees (a skip, a pin) still runs in some instant, so an
-- instant is left by every row past it.  Those are read off the emission
-- set directly, over its reached rows (`Seen`), never through a reader.
--
-- EACH DIRECTION IS OVER PREFIXES, since a run need not end: what has
-- come out is within what the grouping allows, and everything the
-- grouping allows, once its instant is over, comes out.  A prefix is what
-- a subscriber is shown first (`denotation.Read.Meets`), the reader
-- adequacy reads by.
module simultaneous.Statement where

open import Data.Bool using (Bool)
open import Data.List using ([]; [_])
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym) renaming (trans to ≡-trans)

open import denotation.EmissionSet using (EmissionSet)
open import simultaneous.SObs using (SObs)
open import simultaneous.Relations using (events; batched; Met; ranked; Closes; Ends; joined; values; stampedᴰ; stampedᴮ; grouped;
  Groups; Batches; Erases; EndsWith)
open import simultaneous.Batcher using (batcher-ends)
open import simultaneous.Closing using (batches)
open import simultaneous.Erasure using (erases)

------------------------------------------------------------------------
-- The statement

Spec : Set₁
Spec = ∀ {A} (o : SObs [] A) → Groups (batched o) (events o)

-- A batched prefix is within the grouping of an elaborated prefix, which
-- erases, stamp for stamp, to a plain one; and back.  At the end, the
-- values: the batcher ends with the elaborated run, which ends with the
-- plain one.  Composed over the three runs as variables, so no proof's
-- body is ever unfolded to check the composition.
grouping : ∀ {A} {b x} {e : EmissionSet A} → Batches b x → Erases x e → EndsWith b x → Groups b e
grouping {b = b} {x} {e} bat era bend = sound , complete , ends-out , ends-in
  where
    sound : ∀ {rs} → Met (ranked b) rs →
            Σ _ λ rs′ → Σ Bool λ ov → Met (ranked e) rs′ × Closes [_] e rs′ ov ×
            Prefix _≡_ (stampedᴮ rs) (grouped ov (stampedᴰ rs′))
    sound {rs} m with proj₁ bat m
    ... | rx , ov , mx , cl , p with proj₁ era {ov = ov} mx cl
    ...   | rs′ , me , cl′ , eq = rs′ , ov , me , cl′ , subst (λ ys → Prefix _≡_ (stampedᴮ rs) (grouped ov ys)) eq p

    complete : ∀ {rs′ ov} → Met (ranked e) rs′ → Closes [_] e rs′ ov →
               Σ _ λ rs → Met (ranked b) rs × Prefix _≡_ (grouped ov (stampedᴰ rs′)) (stampedᴮ rs)
    complete {rs′} {ov} m cl with proj₁ (proj₂ era) {ov = ov} m cl
    ... | rx , mx , clx , eq with proj₂ bat {ov = ov} mx clx
    ...   | rs , mb , p = rs , mb , subst (λ ys → Prefix _≡_ (grouped ov ys) (stampedᴮ rs)) (sym eq) p

    ends-out : ∀ {rs} → Met b rs → Ends rs → Σ _ λ rs′ → Met e rs′ × Ends rs′ × joined rs ≡ values rs′
    ends-out m en with proj₁ bend m en
    ... | rx , mx , ex , eq with proj₁ (proj₂ (proj₂ era)) mx ex
    ...   | rs′ , me , es , eq′ = rs′ , me , es , ≡-trans eq eq′

    ends-in : ∀ {rs′} → Met e rs′ → Ends rs′ → Σ _ λ rs → Met b rs × Ends rs × values rs′ ≡ joined rs
    ends-in m en with proj₂ (proj₂ (proj₂ era)) m en
    ... | rx , mx , ex , eq with proj₂ bend mx ex
    ...   | rs , mb , eb , eq′ = rs , mb , eb , ≡-trans eq eq′

spec : Spec
spec o = grouping (batches o) (erases o) (batcher-ends o)
