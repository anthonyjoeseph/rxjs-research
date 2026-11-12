{-# OPTIONS --guardedness #-}

-- A CONNECT'S ROWS LISTED from its body's and its source's, and what a
-- listing gives: its proper rows, its ends, a row's first child.
module simultaneous.ConnLists where

open import Data.Bool using (T; not; true; false)
open import Data.Bool.Properties using (T?)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Data.List using (List; []; _∷_; [_]; _++_; filter)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.All using (all?; tabulate; lookup)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_; ¬?; Dec; yes; no)
open import Relation.Nullary.Decidable using (decidable-stable)

open import denotation.Position using (Pos; ix; _⊕_; inside; _≟ᵖ_; root; _<ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Few; Truncate; Proper; Den; hot; _≺_; _≼_;
  module Connect)
open import denotation.Laws.Modulus using (≼-or-≻; ≺-ext; ≼-split; ≺-trans; ≺-irrefl; ≼-≺-≺; ≺-≼-≺)
open import denotation.Laws.BoundedInv using (first-child)
open import denotation.Laws.Shows using (few-reach)
open import denotation.Laws.Worlds using (InvD; InvAt; Lawful; Ok; _∪ʰ_; _⊑_; ⊑-refl; ⊑-≼; ⊑-trans; ⊕-injˡ; inside-⊑)
import denotation.Laws.Connect as LC
open import denotation.Laws.ConnectNe using (module Rows)
import denotation.Laws.Truth.Connect.Cuts as Cuts
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Attribution using (Live)
open import simultaneous.Listing using (Listed)
open import simultaneous.CarryBase using (Emb; ahead-over; few-sub; sub-listed)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE)

-- Past an embedded point, nothing over a later point's image precedes
-- the earlier point's.
follows : ∀ {M x y x′ y′ l} → Emb M → M x y → M x′ y′ → x ≺ x′ → y′ ⊑ l → l ≺ y → ⊥
follows {y = y} {l = l} E m m′ xx yl ly =
  ≺-irrefl {l} (≺-trans {l} {y} {l} ly (proj₁ (ahead-over (Emb.mono E m m′ xx , λ yy → ⊑-≼ {y} {l} (⊑-trans yy yl) ly) yl)))

nin : ∀ {r k} → T (not (inside r k)) → T (inside r k) → ⊥
nin {r} {k} ni i with inside r k
... | Data.Bool.true  = ni
... | Data.Bool.false = i

trunc-few : ∀ {X : Set} {C : EmissionSet X} {k} → Few C k → Few (Truncate C) k
trunc-few (ks , h) = ks , λ y kq → h (proj₁ y) kq

-- One event per row.
Func : ∀ {X : Set} → EmissionSet X → Set
Func t = ∀ {k e e′} → t k e → t k e′ → e ≡ e′

-- The positions a listing's rows name, a list for each.
gather : (ks : List Pos) → (∀ {k} → k ∈ ks → List Pos) → List Pos
gather []       d = []
gather (k ∷ ks) d = d (here refl) ++ gather ks (λ m → d (there m))

gather-sound : ∀ ks (d : ∀ {k} → k ∈ ks → List Pos) {j} → j ∈ gather ks d → Σ Pos λ k → Σ (k ∈ ks) λ m → j ∈ d m
gather-sound (k ∷ ks) d m with ∈-++⁻ (d (here refl)) m
... | inj₁ m′ = k , here refl , m′
... | inj₂ m′ with gather-sound ks (λ m → d (there m)) m′
...   | k′ , mk , jd = k′ , there mk , jd

gather-complete : ∀ ks (d : ∀ {k} → k ∈ ks → List Pos) {k j} (m : k ∈ ks) → j ∈ d m → j ∈ gather ks d
gather-complete (k ∷ ks) d (here refl) jd = ∈-++⁺ˡ jd
gather-complete (k ∷ ks) d (there m)   jd = ∈-++⁺ʳ (d (here refl)) (gather-complete ks (λ m → d (there m)) m jd)

-- The end a listed row is.
endOf : ∀ {X : Set} → Pos → Ev X → List Pos
endOf c end     = [ c ]
endOf c (out _) = []
endOf c skip    = []
endOf c (pin _) = []

endOf-sound : ∀ {X : Set} c (e : Ev X) {j} → j ∈ endOf c e → j ≡ c × e ≡ end
endOf-sound c end (here refl) = refl , refl

-- The ends a functional set lists before a position.
ends-of : ∀ {X : Set} {t : EmissionSet X} {q} → Func t → Listed t q
        → Σ (List Pos) λ es → (∀ {c} → c ∈ es → c ≺ q × t c end) × (∀ {c} → t c end → c ≺ q → c ∈ es)
ends-of {X} {t} {q} f (ks , F , B) = gather ks d , is-end , has-end
  where
    d : ∀ {k} → k ∈ ks → List Pos
    d {k} m = endOf k (proj₁ (proj₂ (B m)))

    is-end : ∀ {c} → c ∈ gather ks d → c ≺ q × t c end
    is-end m with gather-sound ks d m
    ... | k , mk , jd with endOf-sound k (proj₁ (proj₂ (B mk))) jd
    ...   | refl , eq = proj₁ (B mk) , subst (t k) eq (proj₂ (proj₂ (B mk)))

    has-end : ∀ {c} → t c end → c ≺ q → c ∈ gather ks d
    has-end {c} x cq = gather-complete ks d (F x cq) (subst (λ e → c ∈ endOf c e) (f x (proj₂ (proj₂ (B (F x cq))))) (here refl))

-- A functional set listed: its proper rows listed, a row proper where
-- no end listed precedes it.
listed-proper : ∀ {X : Set} {t : EmissionSet X} {q} → Func t → Listed t q → Listed (Proper t) q
listed-proper {X} {t} {q} f L@(ks , F , B) = filter keep? ks , cover , back
  where
    E = ends-of f L

    keep? : ∀ j → _
    keep? j = all? (λ c → ¬? (T? (c <ᵖ j))) (proj₁ E)

    cover : ∀ {j e} → Proper t j e → j ≺ q → j ∈ filter keep? ks
    cover {j} (x , pr) jq = ∈-filter⁺ keep? (F x jq) (tabulate λ {c} mc cj → ≺-irrefl {j} (≼-≺-≺ {j} {c} {j} (pr (proj₂ (proj₁ (proj₂ E) mc))) cj))

    back : ∀ {j} → j ∈ filter keep? ks → j ≺ q × Σ (Ev X) (Proper t j)
    back {j} m with ∈-filter⁻ keep? {xs = ks} m
    ... | mj , al with B mj
    ...   | jq , e , x = jq , e , x , pr
      where
        pr : ∀ {c} → t c end → j ≼ c
        pr {c} y with ≼-or-≻ j c
        ... | inj₁ jc = jc
        ... | inj₂ cj = ⊥-elim (lookup al (proj₂ (proj₂ E) y (≺-trans {c} {j} {q} cj jq)) cj)

-- A functional set listed before a position: alive there, or ended
-- before it.
live-or-ended : ∀ {X : Set} {t : EmissionSet X} {q} → Func t → Listed t q → Live t q ⊎ Σ Pos λ c → c ≺ q × t c end
live-or-ended {t = t} {q} f L with ends-of f L
... | c ∷ _ , is , _ = inj₂ (c , is (here refl))
... | [] , _ , has = inj₁ go
  where
    go : ∀ {c} → t c end → q ≼ c
    go {c} y with ≼-or-≻ q c
    ... | inj₁ qc = qc
    ... | inj₂ cq with has y cq
    ...   | ()

-- Whether a position before the listing's bound precedes every end.
before-ends? : ∀ {X : Set} {t : EmissionSet X} {q} → Func t → Listed t q → ∀ {j} → j ≺ q → Dec (∀ {c} → t c end → j ≺ c)
before-ends? {t = t} {q} f L {j} jq with all? (λ c → T? (j <ᵖ c)) (proj₁ E)
  where E = ends-of f L
... | yes al = yes go
  where
    go : ∀ {c} → t c end → j ≺ c
    go {c} y with ≼-or-≻ q c
    ... | inj₁ qc = ≺-≼-≺ {j} {q} {c} jq qc
    ... | inj₂ cq = lookup al (proj₂ (proj₂ (ends-of f L)) y cq)
... | no nal = no λ h → nal (tabulate λ mc → h (proj₂ (proj₁ (proj₂ (ends-of f L)) mc)))

-- Listed past a row: the row itself is all that lies before its first child.
listed-step : ∀ {X : Set} {a : EmissionSet X} {l e} → Listed a l → a l e → Listed a (l ⊕ [ ix 0 ])
listed-step {X} {a} {l} (ks , F , B) x = l ∷ ks , cover , back
  where
    cover : ∀ {k e′} → a k e′ → k ≺ (l ⊕ [ ix 0 ]) → k ∈ l ∷ ks
    cover {k} y kl with ≼-or-≻ k l
    ... | inj₂ lk = ⊥-elim (first-child l lk kl)
    ... | inj₁ kl′ with ≼-split {k} {l} kl′
    ...   | inj₁ lt   = there (F y lt)
    ...   | inj₂ refl = here refl

    back : ∀ {k} → k ∈ l ∷ ks → k ≺ (l ⊕ [ ix 0 ]) × Σ (Ev X) (a k)
    back (here refl) = ≺-ext l [] , _ , x
    back {k} (there m) = ≺-trans {k} {l} {l ⊕ [ ix 0 ]} (proj₁ (B m)) (≺-ext l []) , proj₂ (B m)

-- A CONNECT'S ROWS LISTED from its body's and its source's: each body
-- row, and each source row's image one label down, alive or in the
-- burst.
module ConnLists {A B : Set} {H : Pos → Set} {s : Den A} {F : Den A → Den B}
                 (Is : InvD H s) (IF : ∀ {t} → Lawful t → InvD (H ∪ʰ t) (F (hot t))) (p : Pos) (ok : Ok H p) where
  private
    module C = Connect s F p
    module S = Cuts.Side {s = s} {F = F} Is IF p ok
    module R = Rows {s = s} {F = F} Is IF p ok

    Iσ = LC.Iσ {s = s} {F = F} Is IF p ok
    Iβ = LC.Iβ {s = s} {F = F} Is IF p ok

    r : Pos
    r = p ⊕ [ ix 1 ]

    t : EmissionSet B
    t = Truncate C.ConnT

    bodyOf : ∀ {k e} → C.ConnT k e → List Pos
    bodyOf {k} (C.body _)   = [ k ]
    bodyOf (C.burst _ _)    = []
    bodyOf (C.echo _ _ _ _) = []
    bodyOf (C.kept _ _ _ _) = []

    bodyOf-sound : ∀ {k e} (w : C.ConnT k e) {j} → j ∈ bodyOf w → j ≡ k × Σ (Ev B) (C.β k)
    bodyOf-sound (C.body b) (here refl) = refl , _ , b

    bodyOf-complete : ∀ {k e e′} → C.β k e → (w : C.ConnT k e′) → k ∈ bodyOf w
    bodyOf-complete b (C.body _)       = here refl
    bodyOf-complete b (C.burst x _)    = ⊥-elim (S.img-body x b (⊑-refl _))
    bodyOf-complete b (C.echo x _ _ _) = ⊥-elim (S.img-body x b (⊑-refl _))
    bodyOf-complete b (C.kept x _ _ _) = ⊥-elim (S.img-body x b (⊑-refl _))

    srcOf : ∀ {k e} → C.ConnT k e → List Pos
    srcOf (C.body _)           = []
    srcOf (C.burst {j} _ _)    = [ j ]
    srcOf (C.echo {j} _ _ _ _) = [ j ]
    srcOf (C.kept {j} _ _ _ _) = [ j ]

    srcOf-sound : ∀ {k e} (w : C.ConnT k e) {j} → j ∈ srcOf w → Σ (Ev A) (C.σ j) × k ≡ j ⊕ [ ix 0 ]
    srcOf-sound (C.burst x _)    (here refl) = (_ , x) , refl
    srcOf-sound (C.echo x _ _ _) (here refl) = (_ , x) , refl
    srcOf-sound (C.kept x _ _ _) (here refl) = (_ , x) , refl

    srcOf-complete : ∀ {j e₀ k e} → C.σ j e₀ → (w : C.ConnT k e) → k ≡ j ⊕ [ ix 0 ] → j ∈ srcOf w
    srcOf-complete x (C.body b) refl                = ⊥-elim (S.img-body x b (⊑-refl _))
    srcOf-complete {j} x (C.burst {j′} _ _) eq    = here (⊕-injˡ j j′ (sym eq))
    srcOf-complete {j} x (C.echo {j′} _ _ _ _) eq = here (⊕-injˡ j j′ (sym eq))
    srcOf-complete {j} x (C.kept {j′} _ _ _ _) eq = here (⊕-injˡ j j′ (sym eq))

    -- What makes a source row's image a row: the burst, the row alive,
    -- or its pin's connect alive.
    src-row : ∀ {k e′} (c : C.ConnT k e′) {j e} → C.σ j e → k ≡ j ⊕ [ ix 0 ]
            → T (inside r j) ⊎ (C.Alive j × Unpinned e) ⊎ Σ Pos (λ q → e ≡ pin q × C.Alive q)
    src-row (C.body b) x refl = ⊥-elim (S.img-body x b (⊑-refl _))
    src-row (C.burst {j₂} _ i) {j} x eq with ⊕-injˡ j₂ j eq
    ... | refl = inj₁ i
    src-row (C.echo {j₂} x₂ al un _) {j} x eq with ⊕-injˡ j₂ j eq
    ... | refl with InvAt.func Iσ x₂ x
    ...   | refl = inj₂ (inj₁ (al , un))
    src-row (C.kept {j₂} {q} x₂ al _ _) {j} x eq with ⊕-injˡ j₂ j eq
    ... | refl with InvAt.func Iσ x₂ x
    ...   | refl = inj₂ (inj₂ (q , refl , al))

    pin-gone : ∀ {X : Set} {e : Ev X} {q} → Unpinned e → e ≡ pin q → ⊥
    pin-gone un refl = un

  body-listed : ∀ {k} → Few C.ConnT k → Listed t k → Listed C.β k
  body-listed {k} Fk (ks , Fl , Bk) = gather ks d , cover , back
    where
      d : ∀ {j} → j ∈ ks → List Pos
      d m = bodyOf (proj₁ (proj₂ (proj₂ (Bk m))))

      cover : ∀ {j e} → C.β j e → j ≺ k → j ∈ gather ks d
      cover {j} b jk = gather-complete ks d m (bodyOf-complete b (proj₁ (proj₂ (proj₂ (Bk m)))))
        where m = Fl (C.body b , few-reach {e = _} (few-sub {a = C.ConnT} {w = k} {v = j} Fk jk)) jk

      back : ∀ {j} → j ∈ gather ks d → j ≺ k × Σ (Ev B) (C.β j)
      back mj with gather-sound ks d mj
      ... | _ , mk , jd with bodyOf-sound (proj₁ (proj₂ (proj₂ (Bk mk)))) jd
      ...   | refl , w = proj₁ (Bk mk) , w

  -- The source rows before a position, each alive and shown below it.
  src-listed : ∀ {q} → Few C.ConnT q → Listed t q → (∀ {j e} → C.σ j e → j ≺ q → C.Alive j × (j ⊕ [ ix 0 ]) ≺ q) → Listed C.σ q
  src-listed {q} Fq (ks , Fl , Bk) sh = gather ks d , cover , back
    where
      d : ∀ {j} → j ∈ ks → List Pos
      d m = srcOf (proj₁ (proj₂ (proj₂ (Bk m))))

      cover : ∀ {j e} → C.σ j e → j ≺ q → j ∈ gather ks d
      cover {j} x jq with sh x jq
      ... | al , jq′ with R.img x (inj₁ al)
      ...   | _ , c = gather-complete ks d m (srcOf-complete x (proj₁ (proj₂ (proj₂ (Bk m)))) refl)
        where m = Fl (c , few-reach {e = _} (few-sub {a = C.ConnT} {w = q} {v = j ⊕ [ ix 0 ]} Fq jq′)) jq′

      back : ∀ {j} → j ∈ gather ks d → j ≺ q × Σ (Ev A) (C.σ j)
      back {j} mj with gather-sound ks d mj
      ... | k , mk , jd with srcOf-sound (proj₁ (proj₂ (proj₂ (Bk mk)))) jd
      ...   | w , refl = ≺-trans {j} {j ⊕ [ ix 0 ]} {q} (≺-ext j []) (proj₁ (Bk mk)) , w

  -- A source row before a body row, or another source row, shows below it.
  below-β : ∀ {j k e₀ e} → C.σ j e₀ → C.β k e → j ≺ k → (j ⊕ [ ix 0 ]) ≺ k
  below-β {j} {k} x b jk with ≼-split {j ⊕ [ ix 0 ]} {k} (Cuts.step≼ {j} {k} jk)
  ... | inj₁ lt   = lt
  ... | inj₂ refl = ⊥-elim (S.img-body x b (⊑-refl _))

  below-σ : ∀ {j k e₀ e} → C.σ j e₀ → C.σ k e → j ≺ k → (j ⊕ [ ix 0 ]) ≺ k
  below-σ {j} {k} x y jk with ≼-split {j ⊕ [ ix 0 ]} {k} (Cuts.step≼ {j} {k} jk)
  ... | inj₁ lt   = lt
  ... | inj₂ refl = ⊥-elim (InvAt.flat Iσ x y)

  -- The source before a body row, listed.
  src-under : ∀ {k} → ¬ ¬ Σ (Ev B) (C.β k) → Few C.ConnT k → Listed t k → Listed C.σ k
  src-under {k} nb Fk L = src-listed Fk L λ {j} x jk →
      (λ {c} ce → decidable-stable (T? (j <ᵖ c)) λ n → nb λ (_ , b) → n (R.alive-β b x jk ce))
    , decidable-stable (T? ((j ⊕ [ ix 0 ]) <ᵖ k)) λ n → nb λ (_ , b) → n (below-β x b jk)

  -- The hot a body row reads, listed before it.
  hot-listed : ∀ {k e} → C.β k e → Few C.ConnT k → Listed t k → Listed (Proper C.σ) k
  hot-listed b Fk L = listed-proper (InvAt.func Iσ) (src-under (λ n → n (_ , b)) Fk L)

  -- The source before an echo's row, listed.
  src-before : ∀ {k e} → C.σ k e → C.Alive k → Few C.ConnT (k ⊕ [ ix 0 ]) → Listed t (k ⊕ [ ix 0 ]) → Listed C.σ k
  src-before {k} x al F L =
    src-listed (few-sub {a = C.ConnT} {w = k ⊕ [ ix 0 ]} {v = k} F kk) (sub-listed L kk)
               λ {j} y jk → (λ {c} ce → ≺-trans {j} {k} {c} jk (al ce)) , below-σ y x jk
    where kk = ≺-ext k []

  -- Few rows before where the body and the source are listed.
  conn-few : ∀ {q} → Listed C.β q → Listed C.σ q → Few C.ConnT q
  conn-few {q} (bs , Fb , _) (ss , Fs , _) = bs ++ L.map (_⊕ [ ix 0 ]) ss , pick
    where
      pick : ∀ {k e} → C.ConnT k e → k ≺ q → k ∈ bs ++ L.map (_⊕ [ ix 0 ]) ss
      pick (C.body b) kq = ∈-++⁺ˡ (Fb b kq)
      pick (C.burst {j} x _) kq    = ∈-++⁺ʳ bs (∈-map⁺ (_⊕ [ ix 0 ]) (Fs x (≺-trans {j} {j ⊕ [ ix 0 ]} {q} (≺-ext j []) kq)))
      pick (C.echo {j} x _ _ _) kq = ∈-++⁺ʳ bs (∈-map⁺ (_⊕ [ ix 0 ]) (Fs x (≺-trans {j} {j ⊕ [ ix 0 ]} {q} (≺-ext j []) kq)))
      pick (C.kept {j} x _ _ _) kq = ∈-++⁺ʳ bs (∈-map⁺ (_⊕ [ ix 0 ]) (Fs x (≺-trans {j} {j ⊕ [ ix 0 ]} {q} (≺-ext j []) kq)))

  -- Whether a source row before a listed body's bound shows: in the
  -- burst; outside it, alive, or its pin's connect alive.
  shows? : ∀ {q j e} → Listed C.β q → C.σ j e → j ≺ q → Dec (Σ (Ev B) (C.ConnT (j ⊕ [ ix 0 ])))
  shows? {q} {j} {e} Lβ x jq with inside r j in ij
  ... | true  = yes (_ , C.burst x (subst T (sym ij) tt))
  ... | false = out? e x (subst (T ∘ not) (sym ij) tt)
    where
      unp? : ∀ {e′} → Unpinned e′ → C.σ j e′ → T (not (inside r j)) → Dec (Σ (Ev B) (C.ConnT (j ⊕ [ ix 0 ])))
      unp? un x′ ni with before-ends? (InvAt.func Iβ) Lβ {j} jq
      ... | yes al = yes (R.shown x′ al ni)
      ... | no nal = no λ { (_ , c) → no-row′ c }
        where
          no-row′ : ∀ {e″} → C.ConnT (j ⊕ [ ix 0 ]) e″ → ⊥
          no-row′ c with src-row c x′ refl
          ... | inj₁ i                     = nin {r} {j} ni i
          ... | inj₂ (inj₁ (al , _))       = nal al
          ... | inj₂ (inj₂ (_ , eq , _))   = pin-gone un eq

      out? : ∀ e′ → C.σ j e′ → T (not (inside r j)) → Dec (Σ (Ev B) (C.ConnT (j ⊕ [ ix 0 ])))
      out? (pin q′) x′ ni with before-ends? (InvAt.func Iβ) Lβ {q′} (≼-≺-≺ {q′} {j} {q} (⊑-≼ (inside-⊑ q′ j (proj₂ (InvAt.pinned Iσ x′)))) jq)
      ... | yes al = yes (_ , C.kept x′ al ni (proj₂ (InvAt.pinned Iσ x′)))
      ... | no nal = no λ { (_ , c) → no-row′ c }
        where
          no-row′ : ∀ {e″} → C.ConnT (j ⊕ [ ix 0 ]) e″ → ⊥
          no-row′ c with src-row c x′ refl
          ... | inj₁ i                       = nin {r} {j} ni i
          ... | inj₂ (inj₁ (_ , un))         = un
          ... | inj₂ (inj₂ (_ , refl , al))  = nal al
      out? (out _) x′ ni = unp? _ x′ ni
      out? skip    x′ ni = unp? _ x′ ni
      out? end     x′ ni = unp? _ x′ ni

  private
    pickI : ∀ {j q} → Dec (Σ (Ev B) (C.ConnT (j ⊕ [ ix 0 ]))) → Dec ((j ⊕ [ ix 0 ]) ≺ q) → List Pos
    pickI {j} (yes _) (yes _) = [ j ⊕ [ ix 0 ] ]
    pickI     (yes _) (no _)  = []
    pickI     (no _)  _       = []

    pickI-sound : ∀ {j q} (a : Dec (Σ (Ev B) (C.ConnT (j ⊕ [ ix 0 ])))) (b : Dec ((j ⊕ [ ix 0 ]) ≺ q)) {y}
                → y ∈ pickI {j} {q} a b → y ≡ j ⊕ [ ix 0 ] × Σ (Ev B) (C.ConnT (j ⊕ [ ix 0 ])) × (j ⊕ [ ix 0 ]) ≺ q
    pickI-sound (yes w) (yes lt) (here refl) = refl , w , lt

    pickI-complete : ∀ {j q} (a : Dec (Σ (Ev B) (C.ConnT (j ⊕ [ ix 0 ])))) (b : Dec ((j ⊕ [ ix 0 ]) ≺ q))
                   → Σ (Ev B) (C.ConnT (j ⊕ [ ix 0 ])) → (j ⊕ [ ix 0 ]) ≺ q → (j ⊕ [ ix 0 ]) ∈ pickI {j} {q} a b
    pickI-complete (yes _) (yes _) _ _  = here refl
    pickI-complete (yes _) (no nb) _ lt = ⊥-elim (nb lt)
    pickI-complete (no na) _       w _  = ⊥-elim (na w)

  -- Listed where the body and the source are: the body's rows, and each
  -- listed source row's image that is a row.
  conn-listed : ∀ {q} → Listed C.β q → Listed C.σ q → Listed t q
  conn-listed {q} Lβ@(bs , Fb , Bb) Lσ@(ss , Fs , Bs) = bs ++ gather ss d , cover , back
    where
      Fq = conn-few Lβ Lσ

      d : ∀ {j} → j ∈ ss → List Pos
      d {j} m = pickI {j} {q} (shows? Lβ (proj₂ (proj₂ (Bs m))) (proj₁ (Bs m))) (T? ((j ⊕ [ ix 0 ]) <ᵖ q))

      reached : ∀ {k e} → C.ConnT k e → k ≺ q → t k e
      reached c kq = c , few-reach {e = _} (few-sub {a = C.ConnT} {w = q} Fq kq)

      img-in : ∀ {j e₀ e} → C.σ j e₀ → C.ConnT (j ⊕ [ ix 0 ]) e → (j ⊕ [ ix 0 ]) ≺ q → (j ⊕ [ ix 0 ]) ∈ bs ++ gather ss d
      img-in {j} x c lt = ∈-++⁺ʳ bs (gather-complete ss d m (pickI-complete (shows? Lβ (proj₂ (proj₂ (Bs m))) (proj₁ (Bs m))) (T? ((j ⊕ [ ix 0 ]) <ᵖ q)) (_ , c) lt))
        where m = Fs x (≺-trans {j} {j ⊕ [ ix 0 ]} {q} (≺-ext j []) lt)

      cover : ∀ {k e} → t k e → k ≺ q → k ∈ bs ++ gather ss d
      cover (C.body b , _) kq          = ∈-++⁺ˡ (Fb b kq)
      cover (c@(C.burst x _) , _) kq    = img-in x c kq
      cover (c@(C.echo x _ _ _) , _) kq = img-in x c kq
      cover (c@(C.kept x _ _ _) , _) kq = img-in x c kq

      back : ∀ {k} → k ∈ bs ++ gather ss d → k ≺ q × Σ (Ev B) (t k)
      back m with ∈-++⁻ bs m
      ... | inj₁ mb with Bb mb
      ...   | kq , e , b = kq , e , reached (C.body b) kq
      back m | inj₂ mg with gather-sound ss d mg
      ... | j , mj , yd with pickI-sound {j} {q} (shows? Lβ (proj₂ (proj₂ (Bs mj))) (proj₁ (Bs mj))) (T? ((j ⊕ [ ix 0 ]) <ᵖ q)) yd
      ...   | refl , (e′ , c) , lt = lt , e′ , reached c lt
