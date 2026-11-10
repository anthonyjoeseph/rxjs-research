{-# OPTIONS --guardedness #-}

-- NAMES TO RANKS: the batcher groups by the names the elaboration mints,
-- the spec by the instant's rank.  Grouping commutes with any
-- relabelling that agrees both ways, one rank per name and one name per
-- rank; read off a run, a value's name and its row's rank are so
-- related, and a batch carries the rank of the values it releases.
--
-- A RANK IS READ OFF THE ROWS BEFORE IT, LISTED EXACTLY (`Listed`).  A
-- cover (`Few`) may hold positions with no row, and a rank counts only
-- instants some row lies in.  Listed, the instants are inserted in order,
-- the frame first, the row's own dropped.  Every visible row of a reading
-- has a cover, since a reading truncates at the first infinity, so a
-- reading whose covers are listed has its ranks, both ways.
--
-- ONE INSTANT, ONE RANK, by the order alone: rows of one instant have
-- the instants before them in common, and a row of a later instant has
-- every one an earlier row has, and that row's own.
module simultaneous.Ranks where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _∷ʳ_; foldr; filter; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using ([])
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs.Properties using (filter⁺)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
import Data.List.Relation.Binary.Pointwise as Pointwise
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; _≟_; suc; _≤_)
open import Data.Nat.Properties using (≤-antisym; n≮n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (mk⇔; Equivalence)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (yes; no; ¬?)

open import denotation.Position using (Pos; _≟ᵖ_; Instant; frame; root; _≟ⁱ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Seen; Den; hot; coldAt; enter; Truncate; Few; _≺_; ⟦_⟧)
open import denotation.Read using (Run; []; _∷_; Visible)
open import simultaneous.InstEmit using (InstEmit; instEmit; value; mark)
open import simultaneous.SObs using (SObs; module Elaborate)
open import simultaneous.Readings using (instantOf; stamped; closed)
open import simultaneous.Relations using (Met; values; ranked; Rank; Before; stampedᴮ; events; elaborated; batched; batchedObs)
open import simultaneous.Instants using (_≺ⁱ_; Sorted; irrⁱ; transⁱ; triⁱ; frame-least; insertⁱ; sorted-insert; ∈-insert⁻; ∈-insert⁺; sorted-⊆; sorted-⊂; ≺-instant; instant-≺)
open import simultaneous.Protocol using (named)
import simultaneous.Spec as Spec

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) using (elaborate)
open Equivalence using (to; from)

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
-- A rank, read off the rows before it

-- The rows before `q`, every one and nothing else.
Listed : ∀ {A} → EmissionSet A → Pos → Set
Listed t q = Σ (List Pos) λ ks → (∀ {k e} → t k e → k ≺ q → k ∈ ks) × (∀ {k} → k ∈ ks → k ≺ q × Σ _ (t k))

-- Wherever finitely many rows precede, they are listed.
Listing : ∀ {A} → EmissionSet A → Set
Listing t = ∀ {q} → Few t q → Listed t q

-- The subscribe frame and every listed position's instant, in order.
instantsOf : List Pos → List Instant
instantsOf = foldr (λ k → insertⁱ (instantOf k)) (frame ∷ [])

sorted-instants : ∀ ks → Sorted (instantsOf ks)
sorted-instants []       = [] ∷ []
sorted-instants (k ∷ ks) = sorted-insert (instantsOf ks) (sorted-instants ks)

instants⁻ : ∀ {i} ks → i ∈ instantsOf ks → i ≡ frame ⊎ Σ Pos λ k → k ∈ ks × instantOf k ≡ i
instants⁻ []       (here refl) = inj₁ refl
instants⁻ (k ∷ ks) m with ∈-insert⁻ (instantsOf ks) m
... | inj₁ refl = inj₂ (k , here refl , refl)
... | inj₂ m′ with instants⁻ ks m′
...   | inj₁ f              = inj₁ f
...   | inj₂ (k′ , km , eq) = inj₂ (k′ , there km , eq)

instants⁺ : ∀ {i} ks → i ≡ frame ⊎ Σ Pos (λ k → k ∈ ks × instantOf k ≡ i) → i ∈ instantsOf ks
instants⁺ []       (inj₁ refl)                    = here refl
instants⁺ (k ∷ ks) (inj₁ f)                       = ∈-insert⁺ (instantsOf ks) (inj₂ (instants⁺ ks (inj₁ f)))
instants⁺ (k ∷ ks) (inj₂ (_ , here refl , refl)) = ∈-insert⁺ (instantsOf ks) (inj₁ refl)
instants⁺ (k ∷ ks) (inj₂ (k′ , there km , eq))   = ∈-insert⁺ (instantsOf ks) (inj₂ (instants⁺ ks (inj₂ (k′ , km , eq))))

-- `q`'s rank: the listed instants but its own.
rank-of : ∀ {A} {t : EmissionSet A} {q} → Listed t q → Σ ℕ (Rank t q)
rank-of {t = t} {q} (ks , cover , sound) = length is , is , filter⁺ ne? (sorted-instants ks) , refl , mk⇔ into back
  where
    ne? = λ i → ¬? (i ≟ⁱ instantOf q)
    is  = filter ne? (instantsOf ks)

    into : ∀ {i} → i ∈ is → Before t q i
    into m with ∈-filter⁻ ne? m
    ... | m′ , ne with instants⁻ ks m′
    ...   | inj₁ f            = ne , inj₁ f
    ...   | inj₂ (k , km , eq) with sound km
    ...     | lt , e , row    = ne , inj₂ (k , e , row , lt , eq)

    back : ∀ {i} → Before t q i → i ∈ is
    back (ne , inj₁ f)                       = ∈-filter⁺ ne? (instants⁺ ks (inj₁ f)) ne
    back (ne , inj₂ (k , e , row , lt , eq)) = ∈-filter⁺ ne? (instants⁺ ks (inj₂ (k , cover row lt , eq))) ne

------------------------------------------------------------------------
-- One instant, one rank

private
  -- Rows of one instant have the instants before them in common.
  same-before : ∀ {A} {t : EmissionSet A} {q q′ i} → instantOf q ≡ instantOf q′ → Before t q i → Before t q′ i
  same-before same (ne , inj₁ f) = (λ e → ne (trans e (sym same))) , inj₁ f
  same-before {q = q} {q′} same (ne , inj₂ (k , e , row , lt , eq)) =
    (λ e′ → ne (trans e′ (sym same))) ,
    inj₂ (k , e , row , instant-≺ k q′ (subst (instantOf k ≺ⁱ_) same (≺-instant k q lt λ e″ → ne (trans (sym eq) e″))) , eq)

  -- A row of a later instant has every instant before an earlier row.
  later-before : ∀ {A} {t : EmissionSet A} {q q′ i} → instantOf q ≺ⁱ instantOf q′ → Before t q i → Before t q′ i
  later-before {q′ = q′} lt (ne , inj₁ refl) = (λ e → frame-least (subst (_ ≺ⁱ_) (sym e) lt)) , inj₁ refl
  later-before {q = q} {q′} lt (ne , inj₂ (k , e , row , kq , eq)) =
    (λ e′ → irrⁱ (subst (_≺ⁱ instantOf q′) (trans eq e′) kq′)) , inj₂ (k , e , row , instant-≺ k q′ kq′ , eq)
    where
      kq′ = transⁱ (≺-instant k q kq λ e″ → ne (trans (sym eq) e″)) lt

  -- ... and the earlier row's own.
  grow : ∀ {A} {t : EmissionSet A} {q q′ e n} → t q e → Rank t q n → Rank t q′ n → instantOf q ≺ⁱ instantOf q′ → ⊥
  grow {q = q} {q′} x (is , s , refl , iff) (js , s′ , len , iff′) lt =
    n≮n _ (subst (suc (length is) ≤_) len
      (sorted-⊂ s s′ (λ m → from iff′ (later-before lt (to iff m)))
        (from iff′ ((λ e → irrⁱ (subst (instantOf q ≺ⁱ_) (sym e) lt)) , inj₂ (q , _ , x , instant-≺ q q′ lt , refl)))
        (λ m → proj₁ (to iff m) refl)))

-- Rows of one instant share a rank.
instant-rank : ∀ {A} {t : EmissionSet A} {q q′ n m} → Rank t q n → Rank t q′ m → instantOf q ≡ instantOf q′ → n ≡ m
instant-rank (is , s , refl , iff) (js , s′ , refl , iff′) same =
  ≤-antisym (sorted-⊆ s s′ λ m → from iff′ (same-before same (to iff m)))
            (sorted-⊆ s′ s λ m → from iff (same-before (sym same) (to iff′ m)))

-- Rows of two instants do not.
rank-instant : ∀ {A} {t : EmissionSet A} {q q′ e e′ n} → t q e → t q′ e′ → Rank t q n → Rank t q′ n → instantOf q ≡ instantOf q′
rank-instant {q = q} {q′} x x′ r r′ with triⁱ (instantOf q) (instantOf q′)
... | inj₁ lt          = ⊥-elim (grow x r r′ lt)
... | inj₂ (inj₁ same) = same
... | inj₂ (inj₂ gt)   = ⊥-elim (grow x′ r′ r gt)

------------------------------------------------------------------------
-- A reading's ranks

-- A visible row truncated has finitely many rows before it.
truncate-few : ∀ {A} {X : EmissionSet A} {q e} → Truncate X q e → Visible e → Few (Truncate X) q
truncate-few {e = out _} (_ , ks , c) _ = ks , λ r lt → c (proj₁ r) lt tt
truncate-few {e = end}   (_ , ks , c) _ = ks , λ r lt → c (proj₁ r) lt tt

-- So has a visible row of a reading.
enter-few : ∀ {A} (d : Den A) p {q e} → enter d p q e → Visible e → Few (enter d p) q
enter-few (hot t)    p = truncate-few
enter-few (coldAt f) p = truncate-few

-- A ranked row is a row.
ranked→ : ∀ {A} {t : EmissionSet A} {q e} → ranked t q e → t q (unrankᴱ e)
ranked→ {e = out _} r = proj₁ r
ranked→ {e = skip}  r = r
ranked→ {e = end}   r = r
ranked→ {e = pin _} r = r

unrank-visible : ∀ {A} {e : Ev (ℕ × A)} → Visible e → Visible (unrankᴱ e)
unrank-visible {e = out _} v = v
unrank-visible {e = end}   v = v

-- A reading whose visible rows are few, its covers listed, has its ranks.
module _ {A : Set} {t : EmissionSet A} (few : ∀ {q e} → t q e → Visible e → Few t q) (listing : Listing t) where
  private
    lift : ∀ {q e} → t q e → Visible e → Σ _ λ e′ → ranked t q e′ × unrankᴱ e′ ≡ e × Visible e′
    lift {e = out a} r v = out (proj₁ (rank-of (listing (few r v))) , a) , (r , proj₂ (rank-of (listing (few r v)))) , refl , tt
    lift {e = end}   r v = end , r , refl , tt

    up : ∀ {c rs} → Run t c rs → Σ _ λ rs′ → Run (ranked t) c rs′ × unrank rs′ ≡ rs
    up [] = [] , [] , refl
    up {rs = (q , _) ∷ _} ((((r , ends) , ks , cov) , v , aft , least) ∷ rn) with lift r v | up rn
    ... | e′ , r′ , refl , v′ | rs′ , rn′ , refl =
      (q , e′) ∷ rs′ , (((r′ , ends) , ks , λ {k} {e} x lt → cov (ranked→ {t = t} {k} {e} x) lt) , v′ , aft ,
                        λ {k} {e} x vx a → least (ranked→ {t = t} {k} {e} x) (unrank-visible {e = e} vx) a) ∷ rn′ , refl

    down : ∀ {c rs} → Run (ranked t) c rs → Run t c (unrank rs)
    down [] = []
    down {rs = (q , e) ∷ _} ((((r , ends) , _) , v , aft , least) ∷ rn) =
      (((ranked→ {t = t} {q} {e} r , ends) , few (ranked→ {t = t} {q} {e} r) (unrank-visible {e = e} v)) , unrank-visible {e = e} v , aft ,
       λ x vx a kq → least (proj₁ (proj₂ (lift x vx))) (proj₂ (proj₂ (proj₂ (lift x vx)))) a kq) ∷ down rn

  ranks : Ranks t
  ranks = up , down

------------------------------------------------------------------------
-- The elaborated run's names agree with its ranks

-- THE ROWS OF A PROGRAM'S READING ARE LISTED: wherever finitely many
-- precede, which positions of a cover hold one is decided.  Owed operator
-- by operator, in the plain program, its elaboration and the batcher.
postulate
  listed-e : ∀ {A} (o : SObs [] A) → Listing (events o)
  listed-x : ∀ {A} (o : SObs [] A) → Listing (elaborated o)
  listed-b : ∀ {A} (o : SObs [] A) → Listing (batched o)

ranks-e : ∀ {A} (o : SObs [] A) → Ranks (events o)
ranks-e o = ranks (λ {q} {e} → enter-few (⟦ o ⟧ []) root {q} {e}) (λ {q} → listed-e o {q})

ranks-x : ∀ {A} (o : SObs [] A) → Ranks (elaborated o)
ranks-x o = ranks (λ {q} {e} → enter-few (⟦ elaborate o ⟧ []) root {q} {e}) (λ {q} → listed-x o {q})

ranks-b : ∀ {A} (o : SObs [] A) → Ranks (batched o)
ranks-b o = ranks (λ {q} {e} → enter-few (⟦ batchedObs o ⟧ []) root {q} {e}) (λ {q} → listed-b o {q})

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
  ... | q , v , x , r | q′ , v′ , x′ , r′ = instant-rank r r′ (trans (sym (named o x)) (named o x′))

  -- One name per rank: a rank is its instant's.
  rank-name : Relabel.Injective _≟ᵖ_ _≟_ (Carries X)
  rank-name c c′ with row c | row c′
  ... | q , v , x , r | q′ , v′ , x′ , r′ = one-value-name o x x′ (rank-instant x x′ r r′)
