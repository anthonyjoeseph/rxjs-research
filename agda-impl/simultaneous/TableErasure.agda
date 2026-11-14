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
-- plain run has a finite elaborated run (`whole-ahead`), the elaborated
-- program reading what its plain program reads
-- (`simultaneous.Consume.sim-root`).
module simultaneous.TableErasure where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using ([])
import Data.List.Relation.Unary.Any as Any
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; suc; _≤_; _⊔_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m) renaming (≤-refl to ≤-refl′)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_⇔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Obs)
open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Few; _≺_; _≼_; enter; approx)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; ≼-refl; ≺→≼; ≼-trans; ≼-split; ≼-or-≻; ≺-irrefl; ≺-absurd)
open import denotation.Laws.Count using (AgC-sym; ag-cnt)
open import denotation.Laws.Cut using (capprox; cut-ne)
open import denotation.Laws.Worlds using (⊑-refl)
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
open import simultaneous.Consume using (sim-root; sim-whole)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; elaborate)

-- Rows of a cut program's table.
Rows : ∀ {X : Set} → Tb.Listed X → Pos → Ev X → Set
Rows L k e = (k , e) ∈ rows L

M : ∀ {A : Set} → Ev A → Ev (IE A) → Set
M = Match Every (One valuesOf) (Reads valuesOf)

-- THE TWO TABLES OF ONE CUT CORRESPOND along `φ`: each unpinned plain
-- row on its image, a skip possibly put late instead, as a pin is (`put`,
-- homed in the subscription's instant or a carried row's before it);
-- each shown elaborated row back on a plain one; each elaborated row in
-- the subscription's instant or a carried row's at or before it; the
-- images keeping the order and the instants of the rows they image.
record Tables {A : Set} (φ : Pos → Pos) (Put : Pos → Pos → Set) (L : Tb.Listed A) (L* : Tb.Listed (IE A)) : Set where
  Imaged : Pos → Ev A → Set
  Imaged k e = Σ (Ev (IE A)) λ e′ → Rows L* (φ k) e′ × M e e′

  Homed : Pos → Set
  Homed k = instantOf k ≡ instantOf root ⊎ Σ Pos λ k₀ → Σ (Ev A) λ e₀ → Rows L k₀ e₀ × Unpinned e₀ × Imaged k₀ e₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k

  PutAt : Pos → Set
  PutAt k = (Σ Pos λ l → Σ (Ev (IE A)) λ e′ → Rows L* l e′ × Put k l) × Homed k

  field
    row→   : ∀ {k e} → Rows L k e → Unpinned e → Imaged k e ⊎ (e ≡ skip × PutAt k)
    pin→   : ∀ {k p} → Rows L k (pin p) → PutAt k
    shown← : ∀ {l e′} → Rows L* l e′ → Shown (One valuesOf) e′
           → Σ Pos λ k → Σ (Ev A) λ e → l ≡ φ k × Rows L k e × Unpinned e × M e e′
    place  : ∀ {m e′} → Rows L* m e′
           → instantOf m ≡ instantOf root ⊎ Σ Pos λ k → Σ (Ev A) λ e → Rows L k e × Unpinned e × Imaged k e × φ k ≼ m × instantOf (φ k) ≡ instantOf m
    mono   : ∀ {k k′ e e′} → Rows L k e → Rows L k′ e′ → Unpinned e → Unpinned e′ → k ≺ k′ → φ k ≺ φ k′
    inst   : ∀ {k k′ e e′} → Rows L k e → Rows L k′ e′ → Unpinned e → Unpinned e′
           → (instantOf (φ k) ≡ instantOf (φ k′) ⇔ instantOf k ≡ instantOf k′)
    home   : ∀ {k e} → Rows L k e → Unpinned e → (instantOf (φ k) ≡ instantOf root ⇔ instantOf k ≡ instantOf root)

-- Reading a run off the tables of programs agreeing with it up to a row.
module Rowed {X : Set} (a : EmissionSet X) (c : ℕ → EmissionSet X) (L : ℕ → Tb.Listed X) (ex : ∀ N → Exact (L N) (c N)) where
  -- Where a cut agrees, finitely many rows precede: the table's.
  few-at : ∀ {N q} → AgreeTo q a (c N) → Few a q
  few-at {N} {q} ag = mapL proj₁ (rows (L N)) ,
    λ {k} {e} x kq → ∈-map⁺ proj₁ (complete (ex N) (proj₁ (upto ag {k} {e} (≺→≼ {k} {q} kq)) x))

  down : ∀ {N q k} → AgreeTo q a (c N) → k ≼ q → AgreeTo k a (c N)
  down {q = q} {k} ag kq = ⟨ (λ {y} {e} yk → upto ag {y} {e} (≼-trans {y} {k} {q} yk kq)) ⟩

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
  (img-row : ∀ {N k e e′} → AgreeTo k t (c N) → Rows (L N) k e → Unpinned e → Rows (L* N) (φ k) e′ → u (φ k) e′)
  (img-few : ∀ {N k e e′} → AgreeTo k t (c N) → Rows (L N) k e → Unpinned e → Rows (L* N) (φ k) e′ → Few u (φ k))
  (causal← : ∀ {N k e} → Rows (L N) k e → Unpinned e → AgreeTo (φ k) u (d N) → AgreeTo k t (c N))
  (put-row : ∀ {N k l e′} → AgreeTo k t (c N) → Rows (L* N) l e′ → Put k l → u l e′)
  (whole-ahead : (ks : List Pos) → (∀ {k e} → t k e → k ∈ ks) → Σ (List Pos) λ ls → ∀ {l e} → u l e → l ∈ ls)
  where
  module RP = Rowed t c L ex
  module RQ = Rowed u d L* ex*

  -- A plain row on its image.
  Img : Pos → Pos → Set
  Img k l = l ≡ φ k × Σ (Ev A) λ e → t k e × Unpinned e × Few t k × Few u l × Σ (Ev (IE A)) λ e′ → u l e′ × M e e′

  PB : Pos → Pos → Set
  PB = Put

  img-at : ∀ {k l} → Img k l → Σ (Ev (IE A)) (u l)
  img-at (_ , _ , _ , _ , _ , _ , e′ , y , _) = e′ , y

  -- An image read off the tables of a cut agreeing up to the row.
  imaged : ∀ {N k e} → AgreeTo k t (c N) → t k e → Unpinned e → Tables.Imaged (T N) k e
         → Σ (Ev (IE A)) λ e′ → u (φ k) e′ × Few u (φ k) × M e e′
  imaged {N} {k} ag x un (e′ , m , mt) =
    let r = RP.to-row ag (≼-refl {k}) x in
    e′ , img-row ag r un m , img-few ag r un m , mt

  -- The image of a row read off a cut agreeing up to it.
  img-of : ∀ {N k e} → AgreeTo k t (c N) → t k e → Unpinned e → Tables.Imaged (T N) k e → Img k (φ k)
  img-of {N} {k} ag x un im with imaged ag x un im
  ... | e′ , y , fw* , mt = refl , _ , x , un , RP.few-at ag , fw* , e′ , y , mt

  homed : ∀ {N k} → AgreeTo k t (c N) → Tables.Homed (T N) k
        → instantOf k ≡ instantOf root ⊎ Σ Pos λ k₀ → Σ Pos λ l₀ → Img k₀ l₀ × Σ (Ev (IE A)) (u l₀) × Few u l₀ × instantOf k₀ ≡ instantOf k
  homed ag (inj₁ e) = inj₁ e
  homed {N} {k} ag (inj₂ (k₀ , e₀ , m , un , im , lt , ie)) =
    let ag₀ = RP.down ag (≺→≼ {k₀} {k} lt)
        x₀ = RP.of-row ag₀ (≼-refl {k₀}) m
        i = img-of ag₀ x₀ un im
    in inj₂ (k₀ , φ k₀ , i , img-at i , proj₁ (proj₂ (proj₂ (imaged ag₀ x₀ un im))) , ie)

  into : ∀ {N k} → AgreeTo k t (c N) → Tables.PutAt (T N) k → Into Img u PB root k
  into ag ((l , e′ , m , pk) , h) = (l , (e′ , put-row ag m pk) , pk) , homed ag h

  img : ∀ {k e} → t k e → Unpinned e → Live t k → Few t k
      → (Σ Pos λ l → Img k l × Σ (Ev (IE A)) λ e′ → u l e′ × Few u l × M e e′) ⊎ (e ≡ skip × Into Img u PB root k)
  img {k} x un _ fw with cutP fw {bP fw} ≤-refl′
  ... | ag with Tables.row→ (T (bP fw)) (RP.to-row ag (≼-refl {k}) x) un
  ...   | inj₂ (eq , pa) = inj₂ (eq , into ag pa)
  ...   | inj₁ im with imaged ag x un im
  ...     | e′ , y , fw* , mt = inj₁ (φ k , (refl , _ , x , un , fw , fw* , e′ , y , mt) , e′ , y , fw* , mt)

  shown : ∀ {l e′} → u l e′ → Shown (One valuesOf) e′ → Live u l → Few u l
        → Σ Pos λ k → Img k l × Σ (Ev A) λ e → t k e × M e e′
  shown {l} {e′} y sh _ fw with cutQ fw {bQ fw} ≤-refl′
  ... | ag* with Tables.shown← (T (bQ fw)) (RQ.to-row ag* (≼-refl {l}) y) sh
  ...   | k , e , refl , m , un , mt =
    let ag = causal← m un ag*
        x = RP.of-row ag (≼-refl {k}) m
    in k , (refl , e , x , un , RP.few-at ag , fw , e′ , y , mt) , e , x , mt

  -- Two rows, read off one cut agreeing up to the later.
  both : ∀ {k k′} → Few t k → Few t k′ → Σ ℕ λ N → AgreeTo k t (c N) × AgreeTo k′ t (c N)
  both fw fw′ = bP fw ⊔ bP fw′ , cutP fw (m≤m⊔n (bP fw) (bP fw′)) , cutP fw′ (m≤n⊔m (bP fw) (bP fw′))

  img-mono : ∀ {k k′ l l′} → Img k l → Img k′ l′ → k ≺ k′ → l ≺ l′
  img-mono {k} {k′} (refl , e , x , un , fw , _) (refl , e′ , x′ , un′ , fw′ , _) lt =
    let (N , ag , ag′) = both fw fw′
    in Tables.mono (T N) (RP.to-row ag (≼-refl {k}) x) (RP.to-row ag′ (≼-refl {k′}) x′) un un′ lt

  inst : ∀ {k k′ l l′} → Img k l → Img k′ l′ → (instantOf l ≡ instantOf l′ ⇔ instantOf k ≡ instantOf k′)
  inst {k} {k′} (refl , e , x , un , fw , _) (refl , e′ , x′ , un′ , fw′ , _) =
    let (N , ag , ag′) = both fw fw′
    in Tables.inst (T N) (RP.to-row ag (≼-refl {k}) x) (RP.to-row ag′ (≼-refl {k′}) x′) un un′

  home : ∀ {k l} → Img k l → (instantOf l ≡ instantOf root ⇔ instantOf k ≡ instantOf root)
  home {k} (refl , e , x , un , fw , _) =
    Tables.home (T (bP fw)) (RP.to-row (cutP fw ≤-refl′) (≼-refl {k}) x) un

  place : ∀ {m e} → u m e → Live u m → Few u m → instantOf m ≡ instantOf root ⊎ Σ Pos λ k → Σ Pos λ l → Img k l × instantOf l ≡ instantOf m
  place {m} y _ fw with cutQ fw {bQ fw} ≤-refl′
  ... | ag* with Tables.place (T (bQ fw)) (RQ.to-row ag* (≼-refl {m}) y)
  ...   | inj₁ e = inj₁ e
  ...   | inj₂ (k , e , r , un , im , km , ie) =
    let ag = causal← r un (RQ.down ag* km)
    in inj₂ (k , φ k , img-of ag (RP.of-row ag (≼-refl {k}) r) un im , ie)

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
  ... | inj₂ lt with cutP fw (m≤m⊔n (bP fw) (bQ fw*)) | cutQ fw* (m≤n⊔m (bP fw) (bQ fw*))
  ...   | ag | ag* with Tables.shown← (T (bP fw ⊔ bQ fw*)) (RQ.to-row ag* (≺→≼ {c*} {φ k} lt) uc) tt
  ...     | k′ , e₀ , refl , m , un′ , mt with ends un′ mt
  ...       | refl with ≼-split {k} {k′} (lv (RP.of-row (causal← m un′ (RQ.down ag* (≺→≼ {φ k′} {φ k} lt))) (≼-refl {k′}) m))
  ...         | inj₁ kk = ⊥-elim (≺-absurd {φ k} {φ k′} (Tables.mono (T (bP fw ⊔ bQ fw*)) (RP.to-row ag (≼-refl {k}) x) m un un′ kk) lt)
  ...         | inj₂ refl = ⊥-elim (≺-irrefl {φ k} lt)

  pinned : ∀ {k p} → t k (pin p) → Live t k → Few t k → Into Img u PB root k
  pinned {k} x _ fw = let ag = cutP fw {bP fw} ≤-refl′ in into ag (Tables.pin→ (T (bP fw)) (RP.to-row ag (≼-refl {k}) x))

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

  module CP = Cut P
  module CQ = Cut Q

  postulate
    -- THE TABLES CORRESPOND at every cut, along one map of positions and
    -- one late placement, each position imaged by finitely many.
    tables : Σ (Pos → Pos) λ φ → Σ (Pos → Pos → Set) λ Put → (∀ N → Tables φ Put (CP.L N) (CQ.L N))
           × Σ (Pos → List Pos) λ bk → (∀ k → k ∈ bk (φ k)) × (∀ l → Σ (List Pos) λ ks → ∀ {k} → Put k l → k ∈ ks)

  φ : Pos → Pos
  φ = proj₁ tables

  postulate
    -- A table's image of a plain row at a cut agreeing up to the row is
    -- the approximant's, with finitely many rows before it; where the
    -- elaborated cut agrees up to a table row's image, the plain cut
    -- agrees up to the row.
    img-row : ∀ {N k e e′} → AgreeTo k t (CP.c N) → Rows (CP.L N) k e → Unpinned e → Rows (CQ.L N) (φ k) e′ → u (φ k) e′
    img-few : ∀ {N k e e′} → AgreeTo k t (CP.c N) → Rows (CP.L N) k e → Unpinned e → Rows (CQ.L N) (φ k) e′ → Few u (φ k)
    causal← : ∀ {N k e} → Rows (CP.L N) k e → Unpinned e → AgreeTo (φ k) u (CQ.c N) → AgreeTo k t (CP.c N)
    -- A late placement found in a table is a row of the approximant.
    put-row : ∀ {N k l e′} → AgreeTo k t (CP.c N) → Rows (CQ.L N) l e′ → proj₁ (proj₂ tables) k l → u l e′

  -- A FINITE PLAIN RUN HAS A FINITE ELABORATED RUN.
  whole-ahead : (ks : List Pos) → (∀ {k e} → t k e → k ∈ ks) → Σ (List Pos) λ ls → ∀ {l e} → u l e → l ∈ ls
  whole-ahead ks every with sim-root n o
  ... | _ , _ , S = sim-whole S (λ ()) ks every

  erasingᵀ : Attribution Every (One valuesOf) (Reads valuesOf) t u root root
  erasingᵀ = Erase.erasing t u CP.c CQ.c CP.L CQ.L CP.ex CQ.ex
    (λ {q} → CP.bound {q}) (λ {q} fw {N} → CP.cut-at {q} fw {N}) (λ {q} → CQ.bound {q}) (λ {q} fw {N} → CQ.cut-at {q} fw {N})
    φ (proj₁ (proj₂ tables)) (proj₁ (proj₂ (proj₂ tables)))
    (proj₁ (proj₂ (proj₂ (proj₂ tables)))) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ tables))))) (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ tables)))))
    (λ {N} {k} {e} {e′} → img-row {N} {k} {e} {e′}) (λ {N} {k} {e} {e′} → img-few {N} {k} {e} {e′}) (λ {N} {k} {e} → causal← {N} {k} {e}) (λ {N} {k} {l} {e′} → put-row {N} {k} {l} {e′}) whole-ahead
