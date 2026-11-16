{-# OPTIONS --guardedness #-}

-- THE ERASURE OVER CUT TABLES.  At each approximant, the elaborated run
-- attributes the plain one (`erasingᵀ`), read off finite tables: a row
-- with finitely many rows before it is a row of a cut program deep
-- enough (`denotation.Laws.Cut.cut-ne`), the cut program's rows are its
-- table's (`simultaneous.Listing.listC-exact`), and the two programs'
-- tables at one cut correspond along a map of positions (`Tables`).
-- What crosses from a table back to the approximant is placement, not
-- agreement: a cut agreeing with the plain run up to a row need not
-- agree with the elaborated run up to its image, since the elaboration
-- reads cold leaves of its own (a minted name, the subscribed mark) that
-- a shallow cut truncates; so each table row placed for an agreed plain
-- row is itself the approximant's (`img-row`, `put-row`), agreement
-- crosses back only from the elaborated side (`causal←`); and a finite
-- plain run has a finite elaborated run (`whole-ahead`).
--
-- WHAT CROSSES BACK IS READ OFF CUTS ALONE.  Every cut is at least three
-- rows deep, past the elaboration's own leaves.  An elaborated row a cut
-- reaches is a row of every cut deep enough (`denotation.Laws.Cut.cut-ne`);
-- two cuts agreeing up to an image (`stable`, `stable←`) put every reached
-- row before it in the shallower cut's finite table; and an approximant
-- shows its hangs (`shows-approx`), so where the table lists every
-- reached row before a position, it lists every row.
module simultaneous.TableErasure where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using ([])
import Data.List.Relation.Unary.Any as Any
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; suc; _≤_; _⊔_; _+_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; m≤n+m; ≤-trans) renaming (≤-refl to ≤-refl′)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (tt)
open import Function using (_⇔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Tree using (Obs)
open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Few; _≺_; _≼_; enter; approx)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; ≼-refl; ≺→≼; ≼-trans; ≼-split; ≼-or-≻; ≺-irrefl; ≺-absurd;
  AgreeTo-trans; AgreeTo-sym)
open import denotation.Laws.Count using (AgC-sym; ag-cnt)
open import denotation.Laws.Cut using (capprox; cut-ne)
open import denotation.Laws.Worlds using (⊑-refl; Shows)
open import denotation.Laws.Shows using (k-shows; ∈-stable; few-down)
open import denotation.Laws.ShowsEv using (sk-approx)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (rows)
open import quickcheck.Tabled.Exact.Base using (Exact; sound; complete)
open import quickcheck.Tabled.Exact using ([])
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.SObs using (SObs; plain; lone; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Relations using (Spent)
open import simultaneous.Listing using (listC-ok; listC-exact)
open import simultaneous.Attribution using (Live; Attribution; Every; One; Reads; Match; Shown; Into)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; elaborate)

-- Rows of a cut program's table.
Rows : ∀ {X : Set} → Tb.Listed X → Pos → Ev X → Set
Rows L k e = (k , e) ∈ rows L

-- An approximant shows its hangs (`denotation.Laws.ShowsEv.sk-approx`).
shows-approx : ∀ {X} n (R : Obs Timeline [] X) → Shows (enter (approx n R []) root)
shows-approx n R = k-shows (λ m → sk-approx m n R [] (λ ()) root (tt , λ ()))

-- Where every reached row before a position is listed, every row is: it
-- has few rows before it, not not, and membership is decidable.
reached-few : ∀ {X} n (R : Obs Timeline [] X) q (ls : List Pos)
            → (∀ {y e} → enter (approx n R []) root y e → y ≺ q → Few (enter (approx n R []) root) y → y ∈ ls)
            → Few (enter (approx n R []) root) q
reached-few n R q ls h = ls , λ {y} x yq → ∈-stable λ ¬in →
  shows-approx n R {q} (ls , λ x′ fy yv → h x′ yv fy) λ fq → ¬in (h x yq (few-down fq (≺→≼ {y} {q} yq)))

-- Where every reached row is listed, every row is.
every-listed : ∀ {X} n (R : Obs Timeline [] X) (ls : List Pos)
             → (∀ {y e} → enter (approx n R []) root y e → Few (enter (approx n R []) root) y → y ∈ ls)
             → ∀ {y e} → enter (approx n R []) root y e → y ∈ ls
every-listed n R ls h {y} x = ∈-stable λ ¬in → shows-approx n R {y} (ls , λ x′ fy _ → h x′ fy) λ fy → ¬in (h x fy)

-- Three bounds under their join.
⊔₁ : ∀ a b c → a ≤ a ⊔ (b ⊔ c)
⊔₁ a b c = m≤m⊔n a (b ⊔ c)

⊔₂ : ∀ a b c → b ≤ a ⊔ (b ⊔ c)
⊔₂ a b c = ≤-trans (m≤m⊔n b c) (m≤n⊔m a (b ⊔ c))

⊔₃ : ∀ a b c → c ≤ a ⊔ (b ⊔ c)
⊔₃ a b c = ≤-trans (m≤n⊔m b c) (m≤n⊔m a (b ⊔ c))

M : ∀ {A : Set} → Ev A → Ev (IE A) → Set
M = Match Every (One valuesOf) (Reads valuesOf)

-- TWO RUNS CORRESPOND along `φ`: each unpinned plain
-- row on its image, a skip possibly put late instead, as a pin is (`put`,
-- homed in the subscription's instant or a carried row's before it);
-- each shown elaborated row back on a plain one; each elaborated row in
-- the subscription's instant or a carried row's, the image at or before
-- it unless the row leads its instant (an async step's `begin` comes
-- before the step's value); the images keeping the order and the
-- instants of the rows they image.
record Corr {A : Set} (φ : Pos → Pos) (Put : Pos → Pos → Set) (L : EmissionSet A) (L* : EmissionSet (IE A)) : Set where
  Imaged : Pos → Ev A → Set
  Imaged k e = Σ (Ev (IE A)) λ e′ → L* (φ k) e′ × M e e′

  Homed : Pos → Set
  Homed k = instantOf k ≡ instantOf root ⊎ Σ Pos λ k₀ → Σ (Ev A) λ e₀ → L k₀ e₀ × Unpinned e₀ × Imaged k₀ e₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k

  PutAt : Pos → Set
  PutAt k = (Σ Pos λ l → Σ (Ev (IE A)) λ e′ → L* l e′ × Put k l) × Homed k

  -- No unpinned row of its instant lies before `k`.
  Leads : Pos → Set
  Leads k = ∀ {k′ e′} → L k′ e′ → Unpinned e′ → instantOf k′ ≡ instantOf k → k ≼ k′

  field
    row→   : ∀ {k e} → L k e → Unpinned e → Imaged k e ⊎ (e ≡ skip × PutAt k)
    pin→   : ∀ {k p} → L k (pin p) → PutAt k
    shown← : ∀ {l e′} → L* l e′ → Shown (One valuesOf) e′
           → Σ Pos λ k → Σ (Ev A) λ e → l ≡ φ k × L k e × Unpinned e × M e e′
    place  : ∀ {m e′} → L* m e′
           → instantOf m ≡ instantOf root ⊎ Σ Pos λ k → Σ (Ev A) λ e → L k e × Unpinned e × Imaged k e × (φ k ≼ m ⊎ Leads k) × instantOf (φ k) ≡ instantOf m
    mono   : ∀ {k k′ e e′} → L k e → L k′ e′ → Unpinned e → Unpinned e′ → k ≺ k′ → φ k ≺ φ k′
    inst   : ∀ {k k′ e e′} → L k e → L k′ e′ → Unpinned e → Unpinned e′
           → (instantOf (φ k) ≡ instantOf (φ k′) ⇔ instantOf k ≡ instantOf k′)
    home   : ∀ {k e} → L k e → Unpinned e → (instantOf (φ k) ≡ instantOf root ⇔ instantOf k ≡ instantOf root)

-- The two tables of one cut correspond.
Tables : ∀ {A : Set} → (Pos → Pos) → (Pos → Pos → Set) → Tb.Listed A → Tb.Listed (IE A) → Set
Tables φ Put L L* = Corr φ Put (Rows L) (Rows L*)

-- A correspondence carries to runs holding the same rows: two cuts to
-- their tables.
corr-≃ : ∀ {A φ Put} {L K : EmissionSet A} {L* K* : EmissionSet (IE A)}
       → (∀ {k e} → L k e → K k e) → (∀ {k e} → K k e → L k e)
       → (∀ {k e} → L* k e → K* k e) → (∀ {k e} → K* k e → L* k e)
       → Corr φ Put L L* → Corr φ Put K K*
corr-≃ {A} {φ} {Put} {L} {K} {L*} {K*} to from to* from* C = record
  { row→ = λ x un → [ (λ im → inj₁ (imaged im)) , (λ { (eq , pa) → inj₂ (eq , putAt pa) }) ] (C.row→ (from x) un)
  ; pin→ = λ x → putAt (C.pin→ (from x))
  ; shown← = λ y sh → let (k , e , eq , x , un , m) = C.shown← (from* y) sh in k , e , eq , to x , un , m
  ; place = λ {m} y → [ inj₁ , (λ { (k , e , x , un , im , le , eq) → inj₂ (k , e , to x , un , imaged im , leadsOr {k} {m} le , eq) }) ] (C.place (from* y))
  ; mono = λ x x′ → C.mono (from x) (from x′)
  ; inst = λ x x′ → C.inst (from x) (from x′)
  ; home = λ x → C.home (from x)
  }
  where
    module C = Corr C

    Imaged : Pos → Ev A → Set
    Imaged k e = Σ (Ev (IE A)) λ e′ → K* (φ k) e′ × M e e′

    imaged : ∀ {k e} → C.Imaged k e → Imaged k e
    imaged (e′ , y , m) = e′ , to* y , m

    Homed : Pos → Set
    Homed k = instantOf k ≡ instantOf root ⊎ Σ Pos λ k₀ → Σ (Ev A) λ e₀ → K k₀ e₀ × Unpinned e₀ × Imaged k₀ e₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k

    homed : ∀ {k} → C.Homed k → Homed k
    homed (inj₁ eq) = inj₁ eq
    homed (inj₂ (k₀ , e₀ , x , un , im , lt , eq)) = inj₂ (k₀ , e₀ , to x , un , imaged im , lt , eq)

    leadsOr : ∀ {k m} → φ k ≼ m ⊎ C.Leads k → φ k ≼ m ⊎ (∀ {k′ e′} → K k′ e′ → Unpinned e′ → instantOf k′ ≡ instantOf k → k ≼ k′)
    leadsOr (inj₁ le) = inj₁ le
    leadsOr (inj₂ ld) = inj₂ (λ x → ld (from x))

    putAt : ∀ {k} → C.PutAt k → (Σ Pos λ l → Σ (Ev (IE A)) λ e′ → K* l e′ × Put k l) × Homed k
    putAt ((l , e′ , y , pl) , h) = (l , e′ , to* y , pl) , homed h

-- Every cut from depth `N` on agrees with the run up to `q`.
Settled : ∀ {X : Set} → EmissionSet X → (ℕ → EmissionSet X) → ℕ → Pos → Set
Settled a c N q = ∀ {N′} → N ≤ N′ → AgreeTo q a (c N′)

-- Reading a run off the tables of programs agreeing with it up to a row.
module Rowed {X : Set} (a : EmissionSet X) (c : ℕ → EmissionSet X) (L : ℕ → Tb.Listed X) (ex : ∀ N → Exact (L N) (c N)) where
  now : ∀ {N q} → Settled a c N q → AgreeTo q a (c N)
  now s = s ≤-refl′

  sdown : ∀ {N q k} → Settled a c N q → k ≼ q → Settled a c N k
  sdown {q = q} {k} s kq le = ⟨ (λ {y} {e} yk → upto (s le) {y} {e} (≼-trans {y} {k} {q} yk kq)) ⟩

  -- Where a cut agrees, finitely many rows precede: the table's.
  few-at : ∀ {N q} → AgreeTo q a (c N) → Few a q
  few-at {N} {q} ag = mapL proj₁ (rows (L N)) ,
    λ {k} {e} x kq → ∈-map⁺ proj₁ (complete (ex N) (proj₁ (upto ag {k} {e} (≺→≼ {k} {q} kq)) x))

  -- A row where a cut agrees is its table's, and back.
  to-row : ∀ {N q k e} → AgreeTo q a (c N) → k ≼ q → a k e → Rows (L N) k e
  to-row {N} ag kq x = complete (ex N) (proj₁ (upto ag kq) x)

  of-row : ∀ {N q k e} → AgreeTo q a (c N) → k ≼ q → Rows (L N) k e → a k e
  of-row {N} ag kq m = proj₂ (upto ag kq) (sound (ex N) m)

-- The attribution, over any two runs read off corresponding tables.
module Erase {A : Set} (t : EmissionSet A) (u : EmissionSet (IE A))
  (c : ℕ → EmissionSet A) (d : ℕ → EmissionSet (IE A)) (L : ℕ → Tb.Listed A) (L* : ℕ → Tb.Listed (IE A))
  (ex : ∀ N → Exact (L N) (c N)) (ex* : ∀ N → Exact (L* N) (d N))
  (bP : ∀ {q} → Few t q → ℕ) (cutP : ∀ {q} (fw : Few t q) {N} → bP fw ≤ N → AgreeTo q t (c N))
  (bQ : ∀ {q} → Few u q → ℕ) (cutQ : ∀ {q} (fw : Few u q) {N} → bQ fw ≤ N → AgreeTo q u (d N))
  (φ : Pos → Pos) (Put : Pos → Pos → Set) (T : ∀ N → Tables φ Put (L N) (L* N))
  (bk : Pos → List Pos) (in-bk : ∀ k → k ∈ bk (φ k)) (pb-few : ∀ l → Σ (List Pos) λ ks → ∀ {k} → Put k l → k ∈ ks)
  (img-row : ∀ {N k e e′} → Settled t c N k → Rows (L N) k e → Unpinned e → Rows (L* N) (φ k) e′ → u (φ k) e′)
  (img-few : ∀ {N k e e′} → Settled t c N k → Rows (L N) k e → Unpinned e → Rows (L* N) (φ k) e′ → Few u (φ k))
  (causal← : ∀ {N k e} → Rows (L N) k e → Unpinned e → Settled u d N (φ k) → Settled t c N k)
  (put-row : ∀ {N k l e′} → Settled t c N k → Rows (L* N) l e′ → Put k l → u l e′)
  (lead : ∀ {N k e m} → Rows (L N) k e → Unpinned e → Corr.Leads (T N) k → instantOf m ≡ instantOf (φ k)
        → Settled u d N m → Settled u d N (φ k))
  (whole-ahead : (ks : List Pos) → (∀ {k e} → t k e → k ∈ ks) → Σ (List Pos) λ ls → ∀ {l e} → u l e → l ∈ ls)
  where
  module RP = Rowed t c L ex
  module RQ = Rowed u d L* ex*

  cutS : ∀ {q} (fw : Few t q) {N} → bP fw ≤ N → Settled t c N q
  cutS fw le le′ = cutP fw (≤-trans le le′)

  cutQS : ∀ {q} (fw : Few u q) {N} → bQ fw ≤ N → Settled u d N q
  cutQS fw le le′ = cutQ fw (≤-trans le le′)

  -- A plain row on its image.
  Img : Pos → Pos → Set
  Img k l = l ≡ φ k × Σ (Ev A) λ e → t k e × Unpinned e × Few t k × Few u l × Σ (Ev (IE A)) λ e′ → u l e′ × M e e′

  PB : Pos → Pos → Set
  PB = Put

  img-at : ∀ {k l} → Img k l → Σ (Ev (IE A)) (u l)
  img-at (_ , _ , _ , _ , _ , _ , e′ , y , _) = e′ , y

  -- An image read off the tables of a cut agreeing up to the row.
  imaged : ∀ {N k e} → Settled t c N k → t k e → Unpinned e → Corr.Imaged (T N) k e
         → Σ (Ev (IE A)) λ e′ → u (φ k) e′ × Few u (φ k) × M e e′
  imaged {N} {k} ag x un (e′ , m , mt) =
    let r = RP.to-row (RP.now ag) (≼-refl {k}) x in
    e′ , img-row ag r un m , img-few ag r un m , mt

  -- The image of a row read off a cut agreeing up to it.
  img-of : ∀ {N k e} → Settled t c N k → t k e → Unpinned e → Corr.Imaged (T N) k e → Img k (φ k)
  img-of {N} {k} ag x un im with imaged ag x un im
  ... | e′ , y , fw* , mt = refl , _ , x , un , RP.few-at (RP.now ag) , fw* , e′ , y , mt

  homed : ∀ {N k} → Settled t c N k → Corr.Homed (T N) k
        → instantOf k ≡ instantOf root ⊎ Σ Pos λ k₀ → Σ Pos λ l₀ → Img k₀ l₀ × Σ (Ev (IE A)) (u l₀) × Few u l₀ × instantOf k₀ ≡ instantOf k
  homed ag (inj₁ e) = inj₁ e
  homed {N} {k} ag (inj₂ (k₀ , e₀ , m , un , im , lt , ie)) =
    let ag₀ = RP.sdown ag (≺→≼ {k₀} {k} lt)
        x₀ = RP.of-row (RP.now ag₀) (≼-refl {k₀}) m
        i = img-of ag₀ x₀ un im
    in inj₂ (k₀ , φ k₀ , i , img-at i , proj₁ (proj₂ (proj₂ (imaged ag₀ x₀ un im))) , ie)

  into : ∀ {N k} → Settled t c N k → Corr.PutAt (T N) k → Into Img u PB root k
  into ag ((l , e′ , m , pk) , h) = (l , (e′ , put-row ag m pk) , pk) , homed ag h

  img : ∀ {k e} → t k e → Unpinned e → Live t k → Few t k
      → (Σ Pos λ l → Img k l × Σ (Ev (IE A)) λ e′ → u l e′ × Few u l × M e e′) ⊎ (e ≡ skip × Into Img u PB root k)
  img {k} x un _ fw with cutS fw {bP fw} ≤-refl′
  ... | ag with Corr.row→ (T (bP fw)) (RP.to-row (RP.now ag) (≼-refl {k}) x) un
  ...   | inj₂ (eq , pa) = inj₂ (eq , into ag pa)
  ...   | inj₁ im with imaged ag x un im
  ...     | e′ , y , fw* , mt = inj₁ (φ k , (refl , _ , x , un , fw , fw* , e′ , y , mt) , e′ , y , fw* , mt)

  shown : ∀ {l e′} → u l e′ → Shown (One valuesOf) e′ → Live u l → Few u l
        → Σ Pos λ k → Img k l × Σ (Ev A) λ e → t k e × M e e′
  shown {l} {e′} y sh _ fw with cutQS fw {bQ fw} ≤-refl′
  ... | ag* with Corr.shown← (T (bQ fw)) (RQ.to-row (RQ.now ag*) (≼-refl {l}) y) sh
  ...   | k , e , refl , m , un , mt =
    let ag = RP.now (causal← m un ag*)
        x = RP.of-row ag (≼-refl {k}) m
    in k , (refl , e , x , un , RP.few-at ag , fw , e′ , y , mt) , e , x , mt

  -- Two rows, read off one cut agreeing up to the later.
  both : ∀ {k k′} → Few t k → Few t k′ → Σ ℕ λ N → AgreeTo k t (c N) × AgreeTo k′ t (c N)
  both fw fw′ = bP fw ⊔ bP fw′ , cutP fw (m≤m⊔n (bP fw) (bP fw′)) , cutP fw′ (m≤n⊔m (bP fw) (bP fw′))

  img-mono : ∀ {k k′ l l′} → Img k l → Img k′ l′ → k ≺ k′ → l ≺ l′
  img-mono {k} {k′} (refl , e , x , un , fw , _) (refl , e′ , x′ , un′ , fw′ , _) lt =
    let (N , ag , ag′) = both fw fw′
    in Corr.mono (T N) (RP.to-row ag (≼-refl {k}) x) (RP.to-row ag′ (≼-refl {k′}) x′) un un′ lt

  inst : ∀ {k k′ l l′} → Img k l → Img k′ l′ → (instantOf l ≡ instantOf l′ ⇔ instantOf k ≡ instantOf k′)
  inst {k} {k′} (refl , e , x , un , fw , _) (refl , e′ , x′ , un′ , fw′ , _) =
    let (N , ag , ag′) = both fw fw′
    in Corr.inst (T N) (RP.to-row ag (≼-refl {k}) x) (RP.to-row ag′ (≼-refl {k′}) x′) un un′

  home : ∀ {k l} → Img k l → (instantOf l ≡ instantOf root ⇔ instantOf k ≡ instantOf root)
  home {k} (refl , e , x , un , fw , _) =
    Corr.home (T (bP fw)) (RP.to-row (cutP fw ≤-refl′) (≼-refl {k}) x) un

  place : ∀ {m e} → u m e → Live u m → Few u m → instantOf m ≡ instantOf root ⊎ Σ Pos λ k → Σ Pos λ l → Img k l × instantOf l ≡ instantOf m
  place {m} y _ fw with cutQS fw {bQ fw} ≤-refl′
  ... | ag* with Corr.place (T (bQ fw)) (RQ.to-row (RQ.now ag*) (≼-refl {m}) y)
  ...   | inj₁ e = inj₁ e
  ...   | inj₂ (k , e , r , un , im , at , ie) =
    let ag = causal← r un (upto-img at)
    in inj₂ (k , φ k , img-of ag (RP.of-row (RP.now ag) (≼-refl {k}) r) un im , ie)
    where
      upto-img : φ k ≼ m ⊎ Corr.Leads (T (bQ fw)) k → Settled u d (bQ fw) (φ k)
      upto-img (inj₁ km) = RQ.sdown ag* km
      upto-img (inj₂ ld) = lead r un ld (sym ie) ag*

  -- An image lies at or before every elaborated end: an end before it is
  -- a plain end's image, which the plain row precedes.
  ends : ∀ {e : Ev A} → Unpinned e → M e end → e ≡ end
  ends {out a} _ (c , _) with c tt
  ... | _ , () , _
  ends {skip} _ (_ , d) = ⊥-elim (d (λ ()) tt)
  ends {end} _ _ = refl

  live : ∀ {k l} → Img k l → Live t k → Live u l
  live {k} (refl , e , x , un , fw , fw* , e′ , y , _) lv {c*} uc with ≼-or-≻ (φ k) c*
  ... | inj₁ le = le
  ... | inj₂ lt with cutP fw (m≤m⊔n (bP fw) (bQ fw*)) | cutQS fw* (m≤n⊔m (bP fw) (bQ fw*))
  ...   | ag | ag* with Corr.shown← (T (bP fw ⊔ bQ fw*)) (RQ.to-row (RQ.now ag*) (≺→≼ {c*} {φ k} lt) uc) tt
  ...     | k′ , e₀ , refl , m , un′ , mt with ends un′ mt
  ...       | refl with ≼-split {k} {k′} (lv (RP.of-row (RP.now (causal← m un′ (RQ.sdown ag* (≺→≼ {φ k′} {φ k} lt)))) (≼-refl {k′}) m))
  ...         | inj₁ kk = ⊥-elim (≺-absurd {φ k} {φ k′} (Corr.mono (T (bP fw ⊔ bQ fw*)) (RP.to-row ag (≼-refl {k}) x) m un un′ kk) lt)
  ...         | inj₂ refl = ⊥-elim (≺-irrefl {φ k} lt)

  pinned : ∀ {k p} → t k (pin p) → Live t k → Few t k → Into Img u PB root k
  pinned {k} x _ fw = let ag = cutS fw {bP fw} ≤-refl′ in into ag (Corr.pin→ (T (bP fw)) (RP.to-row (RP.now ag) (≼-refl {k}) x))

  -- Past a row, a plain run with finitely many rows is all listed, and
  -- so is the elaborated run.
  rest : ∀ {k} → Few t k → Spent t (just k) → Σ (List Pos) λ ls → ∀ {r e} → u r e → φ k ≺ r → r ∈ ls
  rest {k} (ks₁ , f₁) (ks₂ , f₂) = proj₁ w , λ y _ → proj₂ w y
    where
    ks : List Pos
    ks = k ∷ ks₁ ++ ks₂

    every : ∀ {k′ e} → t k′ e → k′ ∈ ks
    every {k′} x with ≼-or-≻ k′ k
    ... | inj₂ kk = there (∈-++⁺ʳ ks₁ (proj₁ (f₂ x kk)))
    ... | inj₁ kk with ≼-split {k′} {k} kk
    ...   | inj₁ lt = there (∈-++⁺ˡ (f₁ x lt))
    ...   | inj₂ refl = here refl

    w : Σ (List Pos) λ ls → ∀ {l e} → u l e → l ∈ ls
    w = whole-ahead ks every

  erasing : Attribution Every (One valuesOf) (Reads valuesOf) t u root root
  erasing = record
    { Img = Img ; PB = PB ; pb-few = λ {l} _ → pb-few l
    ; img = img ; shown = shown
    ; img-row = λ { (_ , e , x , un , _) → e , x , un }
    ; img-fun = λ { (refl , _) (refl , _) → refl }
    ; img-mono = img-mono ; inst = inst ; home = home ; place = place ; live = live
    ; spent = λ { (refl , _ , _ , _ , fw , _) sp _ → rest fw sp }
    ; bk = bk ; in-bk = λ { {k} (refl , _) → in-bk k }
    ; pinned = pinned }

module At (n : ℕ) {A : Set} (o : SObs [] A) where
  P : Obs Timeline [] A
  P = plain o

  Q : Obs Timeline [] (IE A)
  Q = elaborate P

  t : EmissionSet A
  t = enter (approx n P []) root

  u : EmissionSet (IE A)
  u = enter (approx n Q []) root

  -- A closed program's cut at `N`, its table, and the table's exactness.
  module Cut {X : Set} (R : Obs Timeline [] X) where
    a : EmissionSet X
    a = enter (approx n R []) root

    c : ℕ → EmissionSet X
    c N = enter (capprox N n R []) root

    L : ℕ → Tb.Listed X
    L N = proj₁ (listC-ok N n R tt root)

    ex : ∀ N → Exact (L N) (c N)
    ex N = listC-exact N n R [] root (proj₁ (proj₂ (listC-ok N n R tt root))) (proj₂ (proj₂ (listC-ok N n R tt root)))

    -- A row with finitely many rows before it lies where every cut deep
    -- enough agrees.
    bound : ∀ {q} → Few a q → ℕ
    bound (ks , _) = suc (suc (length ks))

    cut-at : ∀ {q} (fw : Few a q) {N} → bound fw ≤ N → AgreeTo q a (c N)
    cut-at {q} (ks , few) {N} le =
      ag-cnt (AgC-sym (cut-ne {m = length ks} {N} le n R [] (λ ()) root (tt , λ ()))) q
        (inj₁ (ks , ≤-refl′ , λ x lt → inj₂ (Any.map (λ { refl → ⊑-refl _ }) (few x lt))))

    -- The cuts at least three rows deep: past the elaboration's own leaves.
    c₃ : ℕ → EmissionSet X
    c₃ N = c (3 + N)

    L₃ : ℕ → Tb.Listed X
    L₃ N = L (3 + N)

    ex₃ : ∀ N → Exact (L₃ N) (c₃ N)
    ex₃ N = ex (3 + N)

    cut-at₃ : ∀ {q} (fw : Few a q) {N} → bound fw ≤ N → AgreeTo q a (c₃ N)
    cut-at₃ fw {N} le = cut-at fw (≤-trans le (m≤n+m N 3))

    module R₃ = Rowed a c₃ L₃ ex₃

  module CP = Cut P
  module CQ = Cut Q

  postulate
    -- THE CUTS CORRESPOND at every depth, along one map of positions and
    -- one late placement, each position imaged by finitely many.
    -- RECOVERY: git show e63b1f32 restores the per-former inversions of an elaborated run over approx (simultaneous/ReadRows.agda, ReadLane, ReadMap, ReadFold, FlatRows, ToldRows), each to be restated over capprox for the per-former correspondence.
    corr : Σ (Pos → Pos) λ φ → Σ (Pos → Pos → Set) λ Put → (∀ N → Corr φ Put (CP.c₃ N) (CQ.c₃ N))
         × Σ (Pos → List Pos) λ bk → (∀ k → k ∈ bk (φ k)) × (∀ l → Σ (List Pos) λ ks → ∀ {k} → Put k l → k ∈ ks)

  -- The tables of each cut correspond as the cuts do.
  tables : Σ (Pos → Pos) λ φ → Σ (Pos → Pos → Set) λ Put → (∀ N → Tables φ Put (CP.L₃ N) (CQ.L₃ N))
         × Σ (Pos → List Pos) λ bk → (∀ k → k ∈ bk (φ k)) × (∀ l → Σ (List Pos) λ ks → ∀ {k} → Put k l → k ∈ ks)
  tables = let (φ′ , Put′ , C , rest) = corr in
    φ′ , Put′ , (λ N → corr-≃ (complete (CP.ex₃ N)) (sound (CP.ex₃ N)) (complete (CQ.ex₃ N)) (sound (CQ.ex₃ N)) (C N)) , rest

  φ : Pos → Pos
  φ = proj₁ tables

  Put : Pos → Pos → Set
  Put = proj₁ (proj₂ tables)

  postulate
    -- THE LIFTING: two plain cuts agreeing up to a table row put the two
    -- elaborated cuts in agreement up to its image; and back.
    elab-causal : ∀ {N N′ k e} → N ≤ N′ → Rows (CP.L₃ N) k e → Unpinned e → AgreeTo k (CP.c₃ N′) (CP.c₃ N)
                → AgreeTo (φ k) (CQ.c₃ N′) (CQ.c₃ N)
    stable← : ∀ {N N′ k e} → N ≤ N′ → Rows (CP.L₃ N) k e → Unpinned e → AgreeTo (φ k) (CQ.c₃ N′) (CQ.c₃ N)
            → AgreeTo k (CP.c₃ N′) (CP.c₃ N)
    -- And up to a late placement found where the plain cut agrees.
    stable-put : ∀ {N N′ k l e′} → N ≤ N′ → AgreeTo k t (CP.c₃ N) → Rows (CQ.L₃ N) l e′ → Put k l
               → AgreeTo l (CQ.c₃ N′) (CQ.c₃ N)
    -- And from a row of the instant a table row leads to that row's image.
    stable-lead : ∀ {N N′ k e m} → N ≤ N′ → Rows (CP.L₃ N) k e → Unpinned e → Corr.Leads (proj₁ (proj₂ (proj₂ tables)) N) k
                → instantOf m ≡ instantOf (φ k) → AgreeTo m (CQ.c₃ N′) (CQ.c₃ N) → AgreeTo (φ k) (CQ.c₃ N′) (CQ.c₃ N)
    -- And everywhere: two plain cuts agreeing at every row put the two
    -- elaborated cuts' rows in one another.
    elab-all : ∀ {N N′} → N ≤ N′ → (∀ q → AgreeTo q (CP.c₃ N′) (CP.c₃ N)) → ∀ {y e} → CQ.c₃ N′ y e → CQ.c₃ N y e

  -- A FINITE PLAIN RUN: past its count, every plain cut is the run, so
  -- every deeper elaborated cut's rows are that cut's.
  stable-all : (ks : List Pos) → (∀ {k e} → t k e → k ∈ ks) → Σ ℕ λ N → ∀ {N′} → N ≤ N′ → ∀ {y e} → CQ.c₃ N′ y e → CQ.c₃ N y e
  stable-all ks every = B , λ le → elab-all le λ q → AgreeTo-trans (AgreeTo-sym (all q le)) (all q ≤-refl′)
    where
      fw : ∀ q → Few t q
      fw q = ks , λ x _ → every x

      B : ℕ
      B = CP.bound (fw root)

      all : ∀ q {N′} → B ≤ N′ → AgreeTo q t (CP.c₃ N′)
      all q = CP.cut-at₃ (fw q)

  -- TWO ELABORATED CUTS AGREE UP TO AN IMAGE where the plain cuts are
  -- settled up to its row.
  stable : ∀ {N N′ k e} → N ≤ N′ → Settled t CP.c₃ N k → Rows (CP.L₃ N) k e → Unpinned e
         → AgreeTo (φ k) (CQ.c₃ N′) (CQ.c₃ N)
  stable le ag r un = elab-causal le r un (AgreeTo-trans (AgreeTo-sym (ag le)) (ag ≤-refl′))

  -- Where every deeper elaborated cut agrees with this one up to `l`, the
  -- elaborated run does, every reached row before `l` the cut's.
  agree-at : ∀ {N l} → (∀ {N′} → N ≤ N′ → AgreeTo l (CQ.c₃ N′) (CQ.c₃ N)) → AgreeTo l u (CQ.c₃ N)
  agree-at {N} {l} st =
    AgreeTo-trans (CQ.cut-at₃ fq (m≤m⊔n (CQ.bound fq) N)) (st (m≤n⊔m (CQ.bound fq) N))
    where
      fq : Few u l
      fq = reached-few n Q l (mapL proj₁ (rows (CQ.L₃ N))) λ {y} {e} x yl fy →
        let x′ = proj₁ (upto (CQ.cut-at₃ fy {CQ.bound fy ⊔ N} (m≤m⊔n (CQ.bound fy) N)) {y} {e} (≼-refl {y})) x
        in ∈-map⁺ proj₁ (complete (CQ.ex₃ N) (proj₁ (upto (st (m≤n⊔m (CQ.bound fy) N)) {y} {e} (≺→≼ {y} {l} yl)) x′))

  -- Settled up to a row of the instant a table row leads, settled up to
  -- its image.
  lead : ∀ {N k e m} → Rows (CP.L₃ N) k e → Unpinned e → Corr.Leads (proj₁ (proj₂ (proj₂ tables)) N) k
       → instantOf m ≡ instantOf (φ k) → Settled u CQ.c₃ N m → Settled u CQ.c₃ N (φ k)
  lead {N} {k} r un ld ie ag* {N′} le =
    AgreeTo-trans (agree-at {N} {φ k} (λ le′ → stable-lead le′ r un ld ie (AgreeTo-trans (AgreeTo-sym (ag* le′)) (ag* ≤-refl′))))
      (AgreeTo-sym (stable-lead le r un ld ie (AgreeTo-trans (AgreeTo-sym (ag* le)) (ag* ≤-refl′))))

  -- An agreed table row's image: the elaborated run agrees with the cut
  -- up to it.
  img-agree : ∀ {N k e} → Settled t CP.c₃ N k → Rows (CP.L₃ N) k e → Unpinned e → AgreeTo (φ k) u (CQ.c₃ N)
  img-agree ag r un = agree-at (λ le → stable le ag r un)

  -- A late placement found in a table is a row of the approximant.
  put-row : ∀ {N k l e′} → Settled t CP.c₃ N k → Rows (CQ.L₃ N) l e′ → Put k l → u l e′
  put-row {l = l} ag m pl = CQ.R₃.of-row (agree-at (λ le → stable-put le (ag ≤-refl′) m pl)) (≼-refl {l}) m

  -- A table's image of a plain row at a cut agreeing up to the row is the
  -- approximant's, with finitely many rows before it.
  img-row : ∀ {N k e e′} → Settled t CP.c₃ N k → Rows (CP.L₃ N) k e → Unpinned e → Rows (CQ.L₃ N) (φ k) e′ → u (φ k) e′
  img-row {N} {k} ag r un m = CQ.R₃.of-row (img-agree ag r un) (≼-refl {φ k}) m

  img-few : ∀ {N k e e′} → Settled t CP.c₃ N k → Rows (CP.L₃ N) k e → Unpinned e → Rows (CQ.L₃ N) (φ k) e′ → Few u (φ k)
  img-few ag r un _ = CQ.R₃.few-at (img-agree ag r un)

  -- Where the elaborated cut agrees up to a table row's image, the plain
  -- cut agrees up to the row.
  causal-now : ∀ {N k e} → Rows (CP.L₃ N) k e → Unpinned e → AgreeTo (φ k) u (CQ.c₃ N) → AgreeTo k t (CP.c₃ N)
  causal-now {N} {k} r un ag* =
    AgreeTo-trans (CP.cut-at₃ fk (⊔₁ (CP.bound fk) N (CQ.bound fu))) (back (⊔₂ (CP.bound fk) N (CQ.bound fu)) (⊔₃ (CP.bound fk) N (CQ.bound fu)))
    where
      fu : Few u (φ k)
      fu = CQ.R₃.few-at ag*

      back : ∀ {N′} → N ≤ N′ → CQ.bound fu ≤ N′ → AgreeTo k (CP.c₃ N′) (CP.c₃ N)
      back le le′ = stable← le r un (AgreeTo-trans (AgreeTo-sym (CQ.cut-at₃ fu le′)) ag*)

      fk : Few t k
      fk = reached-few n P k (mapL proj₁ (rows (CP.L₃ N))) λ {y} {e} x yk fy →
        let x′ = proj₁ (upto (CP.cut-at₃ fy (⊔₁ (CP.bound fy) N (CQ.bound fu))) {y} {e} (≼-refl {y})) x
            b = back (⊔₂ (CP.bound fy) N (CQ.bound fu)) (⊔₃ (CP.bound fy) N (CQ.bound fu))
        in ∈-map⁺ proj₁ (complete (CP.ex₃ N) (proj₁ (upto b {y} {e} (≺→≼ {y} {k} yk)) x′))

  -- And from every deeper cut on.
  causal← : ∀ {N k e} → Rows (CP.L₃ N) k e → Unpinned e → Settled u CQ.c₃ N (φ k) → Settled t CP.c₃ N k
  causal← r un ag* le =
    AgreeTo-trans (causal-now r un (ag* ≤-refl′)) (AgreeTo-sym (stable← le r un (AgreeTo-trans (AgreeTo-sym (ag* le)) (ag* ≤-refl′))))

  -- A FINITE PLAIN RUN HAS A FINITE ELABORATED RUN: one cut's table lists it.
  whole-ahead : (ks : List Pos) → (∀ {k e} → t k e → k ∈ ks) → Σ (List Pos) λ ls → ∀ {l e} → u l e → l ∈ ls
  whole-ahead ks every =
    let (N , st) = stable-all ks every
        ls = mapL proj₁ (rows (CQ.L₃ N))
    in ls , every-listed n Q ls λ {y} {e} x fy →
         ∈-map⁺ proj₁ (complete (CQ.ex₃ N) (st (m≤n⊔m (CQ.bound fy) N)
           (proj₁ (upto (CQ.cut-at₃ fy (m≤m⊔n (CQ.bound fy) N)) {y} {e} (≼-refl {y})) x)))

  erasingᵀ : Attribution Every (One valuesOf) (Reads valuesOf) t u root root
  erasingᵀ = Erase.erasing t u CP.c₃ CQ.c₃ CP.L₃ CQ.L₃ CP.ex₃ CQ.ex₃
    (λ {q} → CP.bound {q}) (λ {q} fw {N} → CP.cut-at₃ {q} fw {N}) (λ {q} → CQ.bound {q}) (λ {q} fw {N} → CQ.cut-at₃ {q} fw {N})
    φ (proj₁ (proj₂ tables)) (proj₁ (proj₂ (proj₂ tables)))
    (proj₁ (proj₂ (proj₂ (proj₂ tables)))) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ tables))))) (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ tables)))))
    (λ {N} {k} {e} {e′} → img-row {N} {k} {e} {e′}) (λ {N} {k} {e} {e′} → img-few {N} {k} {e} {e′}) (λ {N} {k} {e} → causal← {N} {k} {e}) (λ {N} {k} {l} {e′} → put-row {N} {k} {l} {e′})
    (λ {N} {k} {e} {m} → lead {N} {k} {e} {m}) whole-ahead
