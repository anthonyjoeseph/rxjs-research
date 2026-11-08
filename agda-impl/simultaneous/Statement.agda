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
open import Data.List using ([_])
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym) renaming (trans to ≡-trans)

open import denotation.EmissionSet using (Seen)
open import simultaneous.SObs using (SObs)
open import simultaneous.Readings using (Rooted)
open import simultaneous.Relations using (events; elaborated; batched; Met; ranked; Closes; Ends; joined; values;
  stampedᴰ; stampedᴮ; grouped; Groups; Erases; Batches)
open import simultaneous.Batcher using (batcher-ends)

------------------------------------------------------------------------
-- The pieces

-- THE ERASURE: the elaboration adds no instant and holds no value, so a
-- prefix of the elaborated run erases to a prefix of the plain one with
-- the same stamped values, and an instant over on one side is over on
-- the other.  Switch, exhaust and the bounded queue are the real cases.
--
-- THE BATCHER: the batcher groups by the names the elaboration mints,
-- and the names agree with the instants — each async cold step mints one
-- and its whole cascade carries it — so grouping by name is grouping by
-- stamp, and each group is released the moment its instant is over,
-- through every flatMap policy and connect.  The names agreeing with the
-- instants is the lemma the body needs first, and it is stated for no
-- one until the body exists.
--
-- RECOVERY: git show d9f6134:agda-impl/simultaneous/Statement.agda
--   restores `coherent`, the names-agree-with-instants statement, over
--   `InstantsAgree` in `simultaneous/Relations.agda` at that sha.
postulate
  erases    : ∀ {A} (o : SObs [] A) → Erases (elaborated o) (events o)
  batchable : ∀ {A} (o : SObs [] A) → Batches (batched o) (elaborated o)

-- THE INSTANTS: every position a program reaches lies under the subscribe
-- frame or one timer cascade, which is what makes `instantOf` read an
-- instant, and a stamp count them.
Positioned : Set₁
Positioned = ∀ {A} (o : SObs [] A) {k e} → Seen (events o) k e → Rooted k

postulate
  positioned : Positioned

------------------------------------------------------------------------
-- The statement

Spec : Set₁
Spec = ∀ {A} (o : SObs [] A) → Groups (batched o) (events o)

-- A batched prefix is within the grouping of an elaborated prefix, which
-- erases, stamp for stamp, to a plain one; and back.  At the end, the
-- values: the batcher ends with the elaborated run, which ends with the
-- plain one.
spec : Spec
spec o = sound , complete , ends-out , ends-in
  where
    sound : ∀ {rs} → Met (ranked (batched o)) rs →
            Σ _ λ rs′ → Σ Bool λ ov → Met (ranked (events o)) rs′ × Closes [_] (events o) rs′ ov ×
            Prefix _≡_ (stampedᴮ rs) (grouped ov (stampedᴰ rs′))
    sound {rs} m with proj₁ (batchable o) m
    ... | rx , ov , mx , cl , p with proj₁ (erases o) mx cl
    ...   | rs′ , me , cl′ , eq = rs′ , ov , me , cl′ , subst (λ ys → Prefix _≡_ (stampedᴮ rs) (grouped ov ys)) eq p

    complete : ∀ {rs′ ov} → Met (ranked (events o)) rs′ → Closes [_] (events o) rs′ ov →
               Σ _ λ rs → Met (ranked (batched o)) rs × Prefix _≡_ (grouped ov (stampedᴰ rs′)) (stampedᴮ rs)
    complete {rs′} {ov} m cl with proj₁ (proj₂ (erases o)) m cl
    ... | rx , mx , clx , eq with proj₂ (batchable o) mx clx
    ...   | rs , mb , p = rs , mb , subst (λ ys → Prefix _≡_ (grouped ov ys) (stampedᴮ rs)) (sym eq) p

    ends-out : ∀ {rs} → Met (batched o) rs → Ends rs → Σ _ λ rs′ → Met (events o) rs′ × Ends rs′ × joined rs ≡ values rs′
    ends-out m en with proj₁ (batcher-ends o) m en
    ... | rx , mx , ex , eq with proj₁ (proj₂ (proj₂ (erases o))) mx ex
    ...   | rs′ , me , es , eq′ = rs′ , me , es , ≡-trans eq eq′

    ends-in : ∀ {rs′} → Met (events o) rs′ → Ends rs′ → Σ _ λ rs → Met (batched o) rs × Ends rs × values rs′ ≡ joined rs
    ends-in m en with proj₂ (proj₂ (proj₂ (erases o))) m en
    ... | rx , mx , ex , eq with proj₂ (batcher-ends o) mx ex
    ...   | rs , mb , eb , eq′ = rs , mb , eb , ≡-trans eq eq′
