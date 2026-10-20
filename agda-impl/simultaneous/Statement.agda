{-# OPTIONS --guardedness #-}

-- THE SIMULTANEOUS SPEC, over the denotation: elaborate the author's
-- program, put `batchSimultaneous` on top, and what comes out is what
-- plain rxjs delivers, grouped by instant, released the moment each
-- instant is over.  Three statements, each closing a cheat the others
-- leave open.
--
-- `left-to-right`: the batches, joined back up, are the plain run's
-- values, in order.  Elaborating every program to `empty` is trivially
-- batched, and fails it.
--
-- `coherent`: two emits share a provenance exactly when they sit in one
-- instant, valueless ones too, both the elaborated run's and the
-- batcher's.  Stamping every emit alike, or each apart, fails it on the
-- elaborated run; on the batcher's, it pins a batch to the moment its
-- instant is over, since a batch released late sits in an instant that
-- is not its own.
--
-- `batchable`: the batches, each with its provenance, are the spec's
-- grouping of the elaborated run's values.  A batch restamped to the
-- instant it was released in, to pass `coherent`, fails it.
--
-- EACH IS TWO DIRECTIONS OVER PREFIXES, since a run need not end: what
-- has come out is within what the spec allows, and everything the spec
-- allows comes out eventually.  Only `left-to-right`'s second half needs
-- the plain run's instants finite: an instant that never ends is never
-- released, so `ones` batched shows nothing, as specified.
--
-- EACH IS THE ROOT CASE OF ONE AT EVERY SUBSCRIPTION, in every
-- environment of hot sources, since that is the form an induction over
-- the program needs.  `coherent`'s is assembled here one former at a
-- time: an elaborated program is `Sound` because each elaborated former
-- keeps it, one approximant at a time, and soundness survives the limit.
module simultaneous.Statement where

open import Data.List using (List; []; _∷_; concat)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; _,_; proj₂)
open import Function using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Tree using (Later; FlatOp; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (Events; Pos; Timeline; root)
open import denotation.MonotonicList using (MonotonicList; observe; ⊥ᴰ; deferᴰ; spin)
open import denotation.Denote using (DenEnv; ⟦_⟧)
open import denotation.Compositional using (Admissible; module Over)
open import denotation.Observe using (events)
open import simultaneous.InstEmit using (InstEmit)
open import simultaneous.Leaf using (leafᴰ; _≟ᵖ_; approxˢ; ⟦_⟧ˢ)
open import simultaneous.SObs using (SObs; module Elaborate)
open import simultaneous.Spec _≟ᵖ_ using (batchSimultaneousᴰ)
open import simultaneous.Readings using (instantOf; outs; values; positions; over; FiniteInstants; Rooted; Site; at-root; stamped; closed)

open Elaborate {C = Timeline} _≟ᵖ_ using (E; IE; elaborate; batchSimultaneous; coldˢ; emptyˢ; ofˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ)
open Over leafᴰ using (through-limit)

-- The program the author's stands for: elaborated, batched on top.
batchedObs : ∀ {A} → SObs [] A → E [] (IE (List A))
batchedObs o = batchSimultaneous (elaborate o)

-- The elaborated program's run, and the batcher's on top of it.
elaborated : ∀ {A} → SObs [] A → Events (IE A)
elaborated o = observe (⟦ elaborate o ⟧ˢ []) root

batched : ∀ {A} → SObs [] A → Events (IE (List A))
batched o = observe (⟦ batchedObs o ⟧ˢ []) root

------------------------------------------------------------------------
-- The three relations, between runs

-- The batches among the first n events, each with its provenance.
batchesOut : ∀ {A} → ℕ → Events (IE (List A)) → List (Pos × List A)
batchesOut n b = stamped (values n b)

-- The batches among the first n events, joined back up.
joined : ∀ {A} → ℕ → Events (IE (List A)) → List A
joined n b = concat (L.map proj₂ (batchesOut n b))

-- The values among the first n events of an elaborated run, unwrapped.
unwrapped : ∀ {A} → ℕ → Events (IE A) → List A
unwrapped n x = L.map proj₂ (stamped (values n x))

-- The spec's grouping of the first m events, but for an instant that may
-- still be running.
grouped : ∀ {A} → ℕ → Events (IE A) → List (Pos × List A)
grouped m x = closed (over m x) (batchSimultaneousᴰ (stamped (values m x)))

-- left-to-right: a batched run, joined, is a plain run.
Joins : ∀ {A} → Events (IE (List A)) → Events A → Set
Joins b e =
  (∀ n → Σ ℕ λ m → Prefix _≡_ (joined n b) (values m e)) ×
  (FiniteInstants e → ∀ m → Σ ℕ λ n → Prefix _≡_ (values m e) (joined n b))

-- batchable: a batcher's run is the spec's grouping of its input's.
Batches : ∀ {A} → Events (IE (List A)) → Events (IE A) → Set
Batches b x =
  (∀ n → Σ ℕ λ m → Prefix _≡_ (batchesOut n b) (grouped m x)) ×
  (∀ m → Σ ℕ λ n → Prefix _≡_ (grouped m x) (batchesOut n b))

-- An elaborated run, unwrapped, is a plain run.  No instant is held
-- back, so neither half needs the instants finite.
Erases : ∀ {A} → Events (IE A) → Events A → Set
Erases x e =
  (∀ n → Σ ℕ λ m → Prefix _≡_ (unwrapped n x) (values m e)) ×
  (∀ m → Σ ℕ λ n → Prefix _≡_ (values m e) (unwrapped n x))

-- coherent: provenances agree exactly when instants do.
SameInstant : Pos × Pos → Pos × Pos → Set
SameInstant (p , i) (q , j) = (i ≡ j) ⇔ (instantOf p ≡ instantOf q)

-- An emit at its position, read as its position and its name.
named : ∀ {A} → Pos × IE A → Pos × Pos
named (p , x) = p , InstEmit.instant x

InstantsAgree : ∀ {A} → Events (IE A) → Set
InstantsAgree e = ∀ n → AllPairs SameInstant (L.map named (outs n e))

------------------------------------------------------------------------
-- Soundness: what `coherent` is the root case of

-- An emit's name lies in its own instant: it was minted there.
Within : ∀ {A} → Pos × IE A → Set
Within (q , x) = instantOf (InstEmit.instant x) ≡ instantOf q

-- Emits of one instant share its name.
Shares : ∀ {A} → Pos × IE A → Pos × IE A → Set
Shares (q , x) (r , y) = instantOf q ≡ instantOf r → InstEmit.instant x ≡ InstEmit.instant y

-- At every subscription, every name in its own instant, and one name per
-- instant.  The first makes names of different instants differ, across
-- streams too, which is what lets an operator merging two sound streams
-- stay sound.
record Sound {A} (m : MonotonicList (IE A)) : Set where
  field
    within : ∀ {p} → Site p → ∀ n → All Within (outs n (observe m p))
    shares : ∀ {p} → Site p → ∀ n → AllPairs Shares (outs n (observe m p))
open Sound

-- Every hot source in scope sound.
data Sounds : ∀ {Γ} → DenEnv (L.map IE Γ) → Set₁ where
  []  : Sounds {[]} []
  _∷_ : ∀ {A Γ} {r : MonotonicList (IE A)} {ρ : DenEnv (L.map IE Γ)} → Sound r → Sounds {Γ} ρ → Sounds {A ∷ Γ} (r ∷ ρ)

-- Every hot source in scope sound, and its plain counterpart what it
-- unwraps to.
data Related : ∀ {Γ} → DenEnv (L.map IE Γ) → DenEnv Γ → Set₁ where
  []  : Related {[]} [] []
  _∷_ : ∀ {A Γ} {r′ : MonotonicList (IE A)} {r : MonotonicList A} {ρ′ ρ}
      → Sound r′ × (∀ {p} → Site p → Erases (observe r′ p) (observe r p))
      → Related {Γ} ρ′ ρ → Related {A ∷ Γ} (r′ ∷ ρ′) (r ∷ ρ)

-- A sound run's instants agree with its names.
agreeing : ∀ {A} (xs : List (Pos × IE A)) → All Within xs → AllPairs Shares xs
         → AllPairs SameInstant (L.map named xs)
agreeing []       []        []        = []
agreeing (x ∷ xs) (wx ∷ ws) (sx ∷ ss) = pairs x wx xs ws sx ∷ agreeing xs ws ss
  where
  pairs : ∀ {A} (x : Pos × IE A) → Within x → (ys : List (Pos × IE A)) → All Within ys → All (Shares x) ys
        → All (SameInstant (named x)) (L.map named ys)
  pairs (p , a) wx []             []        []        = []
  pairs (p , a) wx ((q , b) ∷ ys) (wy ∷ ws) (sy ∷ ss) =
    mk⇔ (λ e → trans (sym wx) (trans (cong instantOf e) wy)) sy ∷ pairs (p , a) wx ys ws ss

sound-agrees : ∀ {A} {m : MonotonicList (IE A)} → Sound m → InstantsAgree (observe m root)
sound-agrees s n = agreeing _ (within s at-root n) (shares s at-root n)

-- The handle a `connected` names, sound as its environment is.
looked : ∀ {Γ A} {ρ : DenEnv (L.map IE Γ)} → Sounds ρ → (i : A ∈ Γ) → Sound (lookup ρ (∈-map⁺ IE i))
looked (s ∷ _)  (here refl) = s
looked (_ ∷ ss) (there i)   = looked ss i

-- `⊥ᴰ` shows nothing at all.
spin-silent : ∀ {A} p i n → outs {A} n (spin p i) ≡ []
spin-silent p i zero    = refl
spin-silent p i (suc n) = spin-silent p (suc i) n

⊥-sound : ∀ {A} → Sound {A} ⊥ᴰ
⊥-sound {A} = record
  { within = λ {p} _ n → subst-nil (spin-silent {IE A} p 0 n)
  ; shares = λ {p} _ n → subst-pairs (spin-silent {IE A} p 0 n)
  }
  where
  subst-nil : ∀ {xs : List (Pos × IE A)} → xs ≡ [] → All Within xs
  subst-nil refl = []
  subst-pairs : ∀ {xs : List (Pos × IE A)} → xs ≡ [] → AllPairs Shares xs
  subst-pairs refl = []

------------------------------------------------------------------------
-- The leaves: each elaborated former keeps soundness, one approximant at
-- a time, and soundness survives the limit.

postulate
  sound-admissible : ∀ {A} → Admissible (Sound {A})
  defer-sound      : ∀ {A} {m : MonotonicList (IE A)} → Sound m → Sound (deferᴰ m)

  coldˢ-sound      : ∀ {Γ A} n (c : Timeline A) {ρ : DenEnv Γ} → Sound (approxˢ n (coldˢ {Γ = Γ} c) ρ)
  emptyˢ-sound     : ∀ {Γ A} n {ρ : DenEnv Γ} → Sound (approxˢ n (emptyˢ {Γ = Γ} {A = A}) ρ)
  ofˢ-sound        : ∀ {Γ A} n (xs : List A) {ρ : DenEnv Γ} → Sound (approxˢ n (ofˢ {Γ = Γ} xs) ρ)
  mapˢ-sound       : ∀ {Γ A B} n (f : A → B) (s : E Γ (IE A)) {ρ : DenEnv Γ}
                   → Sound (approxˢ n s ρ) → Sound (approxˢ n (mapˢ f s) ρ)
  scanˢ-sound      : ∀ {Γ A B} n (f : B → A → B) z (s : E Γ (IE A)) {ρ : DenEnv Γ}
                   → Sound (approxˢ n s ρ) → Sound (approxˢ n (scanˢ f z s) ρ)
  takeWhileˢ-sound : ∀ {Γ A} n i p (s : E Γ (IE A)) {ρ : DenEnv Γ}
                   → Sound (approxˢ n s ρ) → Sound (approxˢ n (takeWhileˢ i p s) ρ)
  flatMapˢ-sound   : ∀ {Γ A B} n (op : FlatOp) (f : A → E Γ (IE B)) (s : E Γ (IE A)) {ρ : DenEnv Γ}
                   → (∀ a → Sound (approxˢ n (f a) ρ)) → Sound (approxˢ n s ρ) → Sound (approxˢ n (flatMapˢ op f s) ρ)
  connectˢ-sound   : ∀ {Γ A B} n (s : E Γ (IE A)) (b : E (IE A ∷ Γ) (IE B)) {ρ : DenEnv Γ}
                   → Sound (approxˢ n s ρ) → (∀ {r} → Sound r → Sound (approxˢ n b (r ∷ ρ)))
                   → Sound (approxˢ n (connectˢ s b) ρ)

-- Induction on (n , program), as `approx` recurses.
approx-sound : ∀ {Γ A} n (o : SObs Γ A) {ρ : DenEnv (L.map IE Γ)} → Sounds ρ → Sound (approxˢ n (elaborate o) ρ)
approx-sound n       (cold c)          ss = coldˢ-sound n c
approx-sound n       empty             ss = emptyˢ-sound n
approx-sound n       (of xs)           ss = ofˢ-sound n xs
approx-sound n       (map f s)         ss = mapˢ-sound n f (elaborate s) (approx-sound n s ss)
approx-sound n       (scan f z s)      ss = scanˢ-sound n f z (elaborate s) (approx-sound n s ss)
approx-sound n       (takeWhile i p s) ss = takeWhileˢ-sound n i p (elaborate s) (approx-sound n s ss)
approx-sound n       (flatMap op f s)  ss =
  flatMapˢ-sound n op (λ a → elaborate (f a)) (elaborate s) (λ a → approx-sound n (f a) ss) (approx-sound n s ss)
approx-sound n       (connect s b)     ss =
  connectˢ-sound n (elaborate s) (elaborate b) (approx-sound n s ss) (λ sr → approx-sound n b (sr ∷ ss))
approx-sound n       (connected i)     ss = looked ss i
approx-sound zero    (defer l)         ss = ⊥-sound
approx-sound (suc n) (defer l)         ss = defer-sound (approx-sound n (Later.force l) ss)

elaborated-sound : ∀ {Γ A} (o : SObs Γ A) {ρ : DenEnv (L.map IE Γ)} → Sounds ρ → Sound (⟦ elaborate o ⟧ˢ ρ)
elaborated-sound o {ρ} ss = through-limit sound-admissible (elaborate o) ρ λ n → approx-sound n o ss

------------------------------------------------------------------------
-- At every subscription, in every environment

postulate
  -- The batcher on an elaborated program releases each batch in its own
  -- instant, named as the instant is.
  batched-sound  : ∀ {Γ A} (o : SObs Γ A) {ρ : DenEnv (L.map IE Γ)} → Sounds ρ
                 → Sound (⟦ batchSimultaneous (elaborate o) ⟧ˢ ρ)
  left-to-rightˢ : ∀ {Γ A} (o : SObs Γ A) {ρ′ : DenEnv (L.map IE Γ)} {ρ : DenEnv Γ} → Related ρ′ ρ → ∀ {p} → Site p
                 → Joins (observe (⟦ batchSimultaneous (elaborate o) ⟧ˢ ρ′) p) (observe (⟦ o ⟧ ρ) p)
  batchableˢ     : ∀ {Γ A} (o : SObs Γ A) {ρ : DenEnv (L.map IE Γ)} → Sounds ρ → ∀ {p} → Site p
                 → Batches (observe (⟦ batchSimultaneous (elaborate o) ⟧ˢ ρ) p) (observe (⟦ elaborate o ⟧ˢ ρ) p)

------------------------------------------------------------------------
-- The statements: each the root case

Left-To-Right : Set₁
Left-To-Right = ∀ {A} (o : SObs [] A) → Joins (batched o) (events o)

Coherent : Set₁
Coherent = ∀ {A} (o : SObs [] A) → InstantsAgree (elaborated o) × InstantsAgree (batched o)

Batchable : Set₁
Batchable = ∀ {A} (o : SObs [] A) → Batches (batched o) (elaborated o)

-- The anchor for `instantOf`: every position a program's run shows
-- lies under the subscribe frame or under one step of a timer cascade.
Positioned : Set₁
Positioned = ∀ {A} (o : SObs [] A) n → All Rooted (positions n (events o))

postulate
  positioned : Positioned

left-to-right : Left-To-Right
left-to-right o = left-to-rightˢ o [] at-root

coherent : Coherent
coherent o = sound-agrees (elaborated-sound o []) , sound-agrees (batched-sound o [])

batchable : Batchable
batchable o = batchableˢ o [] at-root
