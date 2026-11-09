{-# OPTIONS --guardedness #-}

-- NAMES TO RANKS: the batcher groups by the names the elaboration mints,
-- the spec by the instant's rank.  Grouping commutes with any
-- relabelling that agrees both ways, one rank per name and one name per
-- rank; read off a run, a value's name and its row's rank are so
-- related, and a batch carries the rank of the values it releases.
module simultaneous.Ranks where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
import Data.List.Relation.Binary.Pointwise as Pointwise
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix; []; _∷_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (yes; no)

open import denotation.Position using (Pos; _≟ᵖ_)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Seen)
open import denotation.Read using (Run; []; _∷_)
open import simultaneous.InstEmit using (InstEmit; instEmit; value; mark)
open import simultaneous.SObs using (SObs)
open import simultaneous.Readings using (instantOf; stamped; closed)
open import simultaneous.Relations using (Met; values; ranked; Rank; stampedᴮ; elaborated; batched)
open import simultaneous.Protocol using (named)
import simultaneous.Spec as Spec

------------------------------------------------------------------------
-- A ranked run, its ranks dropped

unrankᴱ : ∀ {A : Set} → Ev (ℕ × A) → Ev A
unrankᴱ (out (_ , a)) = out a
unrankᴱ skip          = skip
unrankᴱ end           = end
unrankᴱ (pin p)       = pin p

unrank : ∀ {A : Set} → List (Pos × Ev (ℕ × A)) → List (Pos × Ev A)
unrank []             = []
unrank ((q , e) ∷ rs) = (q , unrankᴱ e) ∷ unrank rs

-- Every run met has its ranks, and a ranked run met is met unranked.
-- Neither holds of an arbitrary emission set: a rank lists the instants
-- before a row, and a row reached has finitely many rows before it but
-- no way to tell which positions of a finite cover hold one.
Ranks : ∀ {A : Set} → EmissionSet A → Set
Ranks t = (∀ {rs} → Met t rs → Σ _ λ rs′ → Met (ranked t) rs′ × unrank rs′ ≡ rs)
        × (∀ {rs} → Met (ranked t) rs → Met t (unrank rs))

------------------------------------------------------------------------
-- Relabelling commutes with grouping

module Relabel {P Q : Set} (_≟P_ : DecidableEquality P) (_≟Q_ : DecidableEquality Q) (R : P → Q → Set) where
  private
    module SP = Spec _≟P_
    module SQ = Spec _≟Q_

  -- Labels related, values equal.
  Lab : ∀ {X : Set} → P × X → Q × X → Set
  Lab (p , a) (n , b) = R p n × a ≡ b

  Functional : Set
  Functional = ∀ {p n m} → R p n → R p m → n ≡ m

  Injective : Set
  Injective = ∀ {p q n} → R p n → R q n → p ≡ q

  module _ (fun : Functional) (inj : Injective) where

    from-rel : ∀ {X : Set} i n (vs : List X) {xs ys} → R i n → Pointwise Lab xs ys
             → Pointwise Lab (SP.batchFrom i vs xs) (SQ.batchFrom n vs ys)
    from-rel i n vs r [] = (r , refl) ∷ []
    from-rel i n vs {(j , v) ∷ xs} {(m , w) ∷ ys} r ((r′ , refl) ∷ ps) with i ≟P j | n ≟Q m
    ... | yes refl | yes refl = from-rel i n (vs ∷ʳ v) r ps
    ... | yes refl | no ne    = ⊥-elim (ne (fun r r′))
    ... | no ne    | yes refl = ⊥-elim (ne (inj r r′))
    ... | no _     | no _     = (r , refl) ∷ from-rel j m (v ∷ []) r′ ps

    group-rel : ∀ {X : Set} {xs : List (P × X)} {ys} → Pointwise Lab xs ys
              → Pointwise Lab (SP.batchSimultaneousᴰ xs) (SQ.batchSimultaneousᴰ ys)
    group-rel []                                             = []
    group-rel {xs = (i , v) ∷ _} {(n , _) ∷ _} ((r , refl) ∷ ps) = from-rel i n (v ∷ []) r ps

  -- A prefix of one side is a prefix of the other.
  prefix-rel : Functional → ∀ {X : Set} {xs xs′ : List (P × X)} {ys ys′}
             → Pointwise Lab xs ys → Pointwise Lab xs′ ys′ → Prefix _≡_ xs xs′ → Prefix _≡_ ys ys′
  prefix-rel fun [] _ [] = []
  prefix-rel fun {xs = (p , a) ∷ _} {ys = (n , _) ∷ _} {(n′ , _) ∷ _} ((r , refl) ∷ ps) ((r′ , refl) ∷ ps′) (refl ∷ pre) =
    cong (λ k → k , a) (fun r r′) ∷ prefix-rel fun ps ps′ pre

closed-rel : ∀ {X Y : Set} {L : X → Y → Set} ov {xs ys} → Pointwise L xs ys → Pointwise L (closed ov xs) (closed ov ys)
closed-rel true  ps           = ps
closed-rel false []           = []
closed-rel false (p ∷ [])     = []
closed-rel false (p ∷ q ∷ ps) = p ∷ closed-rel false (q ∷ ps)

------------------------------------------------------------------------
-- A ranked run's names and ranks

-- A value named `p` at a reached row of rank `n`.
Carries : ∀ {X : Set} → EmissionSet (InstEmit Pos X) → Pos → ℕ → Set
Carries t p n = Σ Pos λ q → Σ _ λ v → Seen (ranked t) q (out (n , instEmit (value v) p))

-- A ranked run's values, by name and by rank, row for row.
carried-rel : ∀ {X : Set} {t : EmissionSet (InstEmit Pos X)} {c rs} → Run (ranked t) c rs
            → Pointwise (Relabel.Lab _≟ᵖ_ _≟_ (Carries t)) (stamped (values (unrank rs))) (stampedᴮ rs)
carried-rel []                                                                   = []
carried-rel {rs = (q , out (n , instEmit (value v) p)) ∷ _} ((seen , _) ∷ run) = ((q , v , seen) , refl) ∷ carried-rel run
carried-rel {rs = (q , out (n , instEmit (mark _) _)) ∷ _}  (_ ∷ run)          = carried-rel run
carried-rel {rs = (q , skip) ∷ _}                           (_ ∷ run)          = carried-rel run
carried-rel {rs = (q , end) ∷ _}                            (_ ∷ run)          = carried-rel run
carried-rel {rs = (q , pin _) ∷ _}                          (_ ∷ run)          = carried-rel run

------------------------------------------------------------------------
-- The elaborated run's names agree with its ranks

-- THE RANKS OF AN ELABORATED PROGRAM: its runs and its batcher's carry
-- ranks; rows of one instant share a rank, and rows of two do not.
postulate
  ranks-x      : ∀ {A} (o : SObs [] A) → Ranks (elaborated o)
  ranks-b      : ∀ {A} (o : SObs [] A) → Ranks (batched o)
  instant-rank : ∀ {A} (o : SObs [] A) {q q′ e e′ n m} → elaborated o q e → elaborated o q′ e′
               → Rank (elaborated o) q n → Rank (elaborated o) q′ m → instantOf q ≡ instantOf q′ → n ≡ m
  rank-instant : ∀ {A} (o : SObs [] A) {q q′ e e′ n} → elaborated o q e → elaborated o q′ e′
               → Rank (elaborated o) q n → Rank (elaborated o) q′ n → instantOf q ≡ instantOf q′

-- THE VALUES OF ONE INSTANT CARRY ONE NAME: each carries its instant's
-- last begin, or the root through the subscribe burst.
postulate
  one-value-name : ∀ {A} (o : SObs [] A) {q q′ v v′ p p′} → elaborated o q (out (instEmit (value v) p))
                 → elaborated o q′ (out (instEmit (value v′) p′)) → instantOf q ≡ instantOf q′ → p ≡ p′

-- A BATCH LEAVES IN ITS OWN INSTANT: released when its instant is over,
-- it leaves within it, at the rank its values carry.
postulate
  batch-rank : ∀ {A} (o : SObs [] A) {p n} → Carries (batched o) p n → Carries (elaborated o) p n

module _ {A : Set} (o : SObs [] A) where
  private
    X = elaborated o

    row : ∀ {p n} → Carries X p n → Σ Pos λ q → Σ A λ v → X q (out (instEmit (value v) p)) × Rank X q n
    row (q , v , seen) = q , v , proj₁ (proj₁ seen)

  -- One rank per name: a name is its instant's.
  name-rank : Relabel.Functional _≟ᵖ_ _≟_ (Carries X)
  name-rank c c′ with row c | row c′
  ... | q , v , x , r | q′ , v′ , x′ , r′ = instant-rank o x x′ r r′ (trans (sym (named o x)) (named o x′))

  -- One name per rank: a rank is its instant's.
  rank-name : Relabel.Injective _≟ᵖ_ _≟_ (Carries X)
  rank-name c c′ with row c | row c′
  ... | q , v , x , r | q′ , v′ , x′ , r′ = one-value-name o x x′ (rank-instant o x x′ r r′)
