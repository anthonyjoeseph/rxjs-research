{-# OPTIONS --guardedness #-}

-- THE CONNECT CARRIES ITS ROWS from its body's carry and its annotated
-- source's: each body row on its body carrier, each source row's echo
-- one label under its annotation's image, each burst, kept or heard row
-- into its instant on the annotation's carrier one label down.  A row
-- is carried only where the connect reaches it: few rows of the connect
-- before it.
module simultaneous.CarryConn where

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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; ¬?; Dec; yes; no)
open import Relation.Nullary.Decidable using (decidable-stable)

open import denotation.Position using (Pos; ix; _⊕_; inside; _≟ᵖ_; root; _<ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Few; Truncate; Proper; Den; hot; _≺_; _≼_;
  module Connect)
open import denotation.Laws.Modulus using (≼-or-≻; ≺→≼; ≺-ext; reach-few; ≼-split; ≺-trans; ≺-irrefl; ≼-≺-≺; ≺-≼-≺)
open import denotation.Laws.BoundedInv using (first-child)
open import denotation.Laws.Shows using (few-reach)
open import denotation.Laws.Worlds using (InvD; InvAt; Lawful; Ok; _∪ʰ_; _⊑_; ⊑-refl; ⊑-≼; ⊑-trans; ⊕-identityʳ; ⊕-injˡ; inside-⊑; full)
import denotation.Laws.Connect as LC
open import denotation.Laws.ConnectNe using (module Rows)
import denotation.Laws.Truth.Connect.Cuts as Cuts
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (Live; Shown; Match; Every; One; Reads)
open import simultaneous.Listing using (Listed)
open import simultaneous.CarryBase using (unp-pin; PMap; _∪ᴹ_; _⊆ᴹ_; Emb; CarryAt; IntoAt; Near; Home; Whole; From; Ahead; ahead-under; ahead-over; few-sub;
  sub-listed; instant-⊕)
open import simultaneous.Carry using (annValues; PastOver; Anchor)
open import simultaneous.ReadRows using (up; up-⊕)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE)

private
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

module ConnCarry {A B : Set} {HP HE LP : Pos → Set} {sP : Den A} {FP : Den A → Den B} {sE : Den (AIE A)} {FE : Den (AIE A) → Den (IE B)}
                 (IsP : InvD HP sP) (IFP : ∀ {t} → Lawful t → InvD (HP ∪ʰ t) (FP (hot t)))
                 (IsE : InvD HE sE) (IFE : ∀ {t} → Lawful t → InvD (HE ∪ʰ t) (FE (hot t)))
                 (p p′ : Pos) (okP : Ok HP p) (okE : Ok HE p′) (lp↓ : ∀ {x y} → x ≼ y → LP y → LP x)
                 (M_s : PMap) (c_a : CarryAt annValues M_s HP HE LP (Connect.σ sP FP p) (Connect.σ sE FE p′) (p ⊕ [ ix 1 ]) (p′ ⊕ [ ix 1 ])) where
  module CP = Connect sP FP p
  module CE = Connect sE FE p′
  module A′ = CarryAt c_a
  module SP = Cuts.Side {s = sP} {F = FP} IsP IFP p okP
  module SE = Cuts.Side {s = sE} {F = FE} IsE IFE p′ okE

  module RP = Rows {s = sP} {F = FP} IsP IFP p okP
  module PL = ConnLists {s = sP} {F = FP} IsP IFP p okP
  module EL = ConnLists {s = sE} {F = FE} IsE IFE p′ okE

  Iσ : InvAt HP (p ⊕ [ ix 1 ]) CP.σ
  Iσ = LC.Iσ {s = sP} {F = FP} IsP IFP p okP

  -- A body position leads no source position.
  leads : ∀ {k k′ e₀ e} → CP.β k e₀ → CP.σ k′ e → k ⊑ k′ → ⊥
  leads b x = LC.body-leads {s = sP} {F = FP} IsP IFP p okP (LC.bw {s = sP} {F = FP} IsP IFP p okP b) (LC.sw {s = sP} {F = FP} IsP IFP p okP x)

  -- An unpinned source row lies before the source's end.
  src-live : ∀ {k e} → CP.σ k e → Unpinned e → Live CP.σ k
  src-live {k} x un {c} y with ≼-or-≻ k c
  ... | inj₁ kc = kc
  ... | inj₂ ck with InvAt.quiet Iσ y x ck
  ...   | q , refl , _ = ⊥-elim (unp-pin {A} {q} un)

  r : Pos
  r = p ⊕ [ ix 1 ]

  -- Each source row's echo, paired one label under its annotation's.
  Echo : PMap
  Echo x y = Σ Pos λ k₀ → Σ Pos λ l₀ → Σ (Ev A) (CP.σ k₀) × A′.Img k₀ l₀ × x ≡ k₀ ⊕ [ ix 0 ] × y ≡ l₀ ⊕ [ ix 0 ]

  t : EmissionSet B
  t = Truncate CP.ConnT

  u : EmissionSet (IE B)
  u = Truncate CE.ConnT

  module Body (M_b : PMap) (ms_b : M_s ⊆ᴹ M_b) (emb′ : Emb (M_b ∪ᴹ Echo))
              (c_b : CarryAt valuesOf M_b (HP ∪ʰ Proper CP.σ) (HE ∪ʰ Proper CE.σ) (λ q → Listed (Proper CP.σ) q × LP q)
                             CP.β CE.β (p ⊕ [ ix 0 ]) (p′ ⊕ [ ix 0 ]))
              (past-a : PastOver c_a M_b)
              (nest : ∀ {k l e₀ h L a σ} → CarryAt.PB c_b k l → CP.β k e₀ → Live CP.β k → Σ (Ev A) (Proper CP.σ h) → CarryAt.Img c_a h L → k ≡ h ⊕ (a ∷ σ)
                    → Anchor M_b k l h a) where
    module B′ = CarryAt c_b

    M′ : PMap
    M′ = M_b ∪ᴹ Echo

    -- A body row the connect reaches, on its body carrier.
    BodyImg : Pos → Pos → Set
    BodyImg k l = B′.Img k l × Few CP.ConnT k

    -- A source row's echo the connect reaches, on its annotation's echo.
    EchoImg : Pos → Pos → Set
    EchoImg k l = Σ Pos λ k₀ → Σ Pos λ l₀ → Σ (Ev A) (λ e₀ → CP.σ k₀ e₀ × Unpinned e₀) × CP.Alive k₀ × T (not (inside r k₀))
                × A′.Img k₀ l₀ × Few CP.ConnT k × k ≡ k₀ ⊕ [ ix 0 ] × l ≡ l₀ ⊕ [ ix 0 ]

    ConnImg : Pos → Pos → Set
    ConnImg k l = BodyImg k l ⊎ EchoImg k l

    -- A source row carried into its instant, or in the burst on its
    -- image: one label down on the annotation's carrier.
    SrcPB : Pos → Pos → Set
    SrcPB k l = Σ Pos λ k₀ → Σ Pos λ l₀ → Σ (Ev A) (CP.σ k₀) × ((A′.Img k₀ l₀ × T (inside r k₀)) ⊎ A′.PB k₀ l₀)
              × k ≡ k₀ ⊕ [ ix 0 ] × l ≡ l₀ ⊕ [ ix 0 ] × Σ (Ev (AIE A)) (CE.σ l₀)

    PB′ : Pos → Pos → Set
    PB′ k l = (B′.PB k l × Σ (Ev B) (CP.β k) × Σ (Ev (IE B)) (CE.β l)) ⊎ SrcPB k l

    ext′ : ∀ {k l} → ConnImg k l → Σ Pos λ y → M′ k y × y ⊑ l
    ext′ (inj₁ (i , _)) with B′.ext i
    ... | y , m , yl = y , inj₁ m , yl
    ext′ (inj₂ (k₀ , l₀ , (e₀ , x , _) , _ , _ , i , _ , refl , refl)) = l₀ ⊕ [ ix 0 ] , inj₂ (k₀ , l₀ , (e₀ , x) , i , refl , refl) , ⊑-refl _

    few′ : ∀ {k l} → ConnImg k l → Few t k
    few′ (inj₁ (_ , F))                          = trunc-few F
    few′ (inj₂ (_ , _ , _ , _ , _ , _ , F , _)) = trunc-few F

    img-row′ : ∀ {k l} → ConnImg k l → ¬ ¬ Σ (Ev B) λ e → t k e × Unpinned e
    img-row′ (inj₁ (i , F)) n = B′.img-row i λ { (e , b , un) → n (e , (CP.body b , few-reach {e = e} F) , un) }
    img-row′ (inj₂ (_ , _ , (_ , x , un) , al , ni , _ , F , refl , _)) n = n (skip , (CP.echo x al un ni , few-reach {e = skip} F) , _)

    img-fun′ : ∀ {k a b} → ConnImg k a → ConnImg k b → a ≡ b
    img-fun′ (inj₁ (i , _)) (inj₁ (i′ , _)) = B′.img-fun i i′
    img-fun′ {a = a} {b} (inj₁ (i , _)) (inj₂ (_ , _ , (_ , x , _) , _ , _ , _ , _ , refl , _)) =
      decidable-stable (a ≟ᵖ b) λ _ → B′.img-row i λ { (_ , y , _) → SP.img-body x y (⊑-refl _) }
    img-fun′ {a = a} {b} (inj₂ (_ , _ , (_ , x , _) , _ , _ , _ , _ , refl , _)) (inj₁ (i , _)) =
      decidable-stable (a ≟ᵖ b) λ _ → B′.img-row i λ { (_ , y , _) → SP.img-body x y (⊑-refl _) }
    img-fun′ (inj₂ (k₀ , _ , _ , _ , _ , i , _ , e , refl)) (inj₂ (k₁ , _ , _ , _ , _ , i′ , _ , e′ , refl))
      with ⊕-injˡ k₀ k₁ (trans (sym e) e′)
    ... | refl = cong (_⊕ [ ix 0 ]) (A′.img-fun i i′)

    pb-img′ : ∀ {k l l′} → PB′ k l → ConnImg k l′ → ⊥
    pb-img′ (inj₁ (pb , _)) (inj₁ (i , _)) = B′.pb-img pb i
    pb-img′ (inj₁ (_ , (_ , b) , _)) (inj₂ (_ , _ , (_ , x , _) , _ , _ , _ , _ , refl , _)) = SP.img-body x b (⊑-refl _)
    pb-img′ (inj₂ (_ , _ , (_ , x) , _ , refl , _)) (inj₁ (i , _)) = B′.img-row i λ { (_ , y , _) → SP.img-body x y (⊑-refl _) }
    pb-img′ (inj₂ (k₀ , _ , _ , w , e , _)) (inj₂ (k₁ , _ , _ , _ , ni , i′ , _ , e′ , _)) with ⊕-injˡ k₀ k₁ (trans (sym e) e′)
    pb-img′ (inj₂ (_ , _ , _ , inj₁ (_ , ins) , _ , _)) (inj₂ (k₀ , _ , _ , _ , ni , _ , _ , _ , _)) | refl = nin {r} {k₀} ni ins
    pb-img′ (inj₂ (_ , _ , _ , inj₂ pb , _ , _))       (inj₂ (_ , _ , _ , _ , _ , i′ , _ , _ , _)) | refl = A′.pb-img pb i′

    -- The rows a carrier carries: the body's, and the echoes of the
    -- annotation's.
    bk′ : Pos → List Pos
    bk′ l = B′.bk l ++ L.map (_⊕ [ ix 0 ]) (A′.bk (up l))

    in-bk′ : ∀ {k l} → ConnImg k l → k ∈ bk′ l
    in-bk′ (inj₁ (i , _)) = ∈-++⁺ˡ (B′.in-bk i)
    in-bk′ {l = l} (inj₂ (k₀ , l₀ , _ , _ , _ , i , _ , refl , refl)) =
      ∈-++⁺ʳ (B′.bk l) (∈-map⁺ (_⊕ [ ix 0 ]) (subst (λ z → k₀ ∈ A′.bk z) (sym (up-⊕ l₀ (ix 0))) (A′.in-bk i)))

    -- A body row the connect reaches is live in the body where it is in
    -- the connect: the body's ends are the connect's.
    body-live : ∀ {k} → Few CP.ConnT k → Live t k → Live CP.β k
    body-live {k} F lv {c} b with ≼-or-≻ k c
    ... | inj₁ kc = kc
    ... | inj₂ ck = lv (CP.body b , few-reach {e = end} (few-sub {a = CP.ConnT} {w = k} {v = c} F ck))

    live-u : ∀ {l} → Live CE.β l → Live u l
    live-u lv (CE.body b , _) = lv b

    postulate
      -- An echo is carried live: the elaborated body is alive past the
      -- annotation's image where the plain body is past the row.
      conn-echo-live : ∀ {k l} → EchoImg k l → Live t k → Live u l

    live′ : ∀ {k l} → ConnImg k l → Live t k → Live u l
    live′ (inj₁ (i , F)) lv = live-u (B′.live i (body-live F lv))
    live′ (inj₂ ei)      lv = conn-echo-live ei lv

    -- `conn-pb-past`: a body row's late carrier is past the map by the body's carry,
    -- given the body alive there; a pin's reach waits only on its
    -- connect's past, so a body ended between its pin's connect and it is
    -- seen by no row of the connect.
    -- An echo's late carriers: the annotation's carried at the source
    -- row, or imaged there in the burst.
    from-src : ∀ {j e₁} → CE.σ j e₁ → Σ (List Pos) λ ks → ∀ {k} → PB′ k (j ⊕ [ ix 0 ]) → k ∈ ks
    from-src {j} y = L.map (_⊕ [ ix 0 ]) (A′.bk j ++ proj₁ (A′.pb-few y)) , mem
      where
        mem : ∀ {k} → PB′ k (j ⊕ [ ix 0 ]) → k ∈ L.map (_⊕ [ ix 0 ]) (A′.bk j ++ proj₁ (A′.pb-few y))
        mem (inj₁ (_ , _ , (_ , bl))) = ⊥-elim (SE.img-body y bl (⊑-refl _))
        mem (inj₂ (k₀ , l₀ , _ , w , refl , eq , _)) with ⊕-injˡ j l₀ eq
        ... | refl with w
        ...   | inj₁ (i , _) = ∈-map⁺ (_⊕ [ ix 0 ]) (∈-++⁺ˡ (A′.in-bk i))
        ...   | inj₂ pb      = ∈-map⁺ (_⊕ [ ix 0 ]) (∈-++⁺ʳ (A′.bk j) (proj₂ (A′.pb-few y) pb))

    -- The late carriers a row of the elaborated connect carries: a body
    -- row's, the body's; an echo's, the annotation's, one label up.
    pb-few′ : ∀ {l e} → u l e → Σ (List Pos) λ ks → ∀ {k} → PB′ k l → k ∈ ks
    pb-few′ {l} (CE.body b , _) with B′.pb-few b
    ... | ks , h = ks , λ { (inj₁ (pb , _)) → h pb
                          ; (inj₂ (_ , l₀ , _ , _ , _ , eq , (_ , y))) → ⊥-elim (SE.img-body y b ([] , trans eq (sym (⊕-identityʳ (l₀ ⊕ [ ix 0 ]))))) }
    pb-few′ (CE.burst y _ , _)    = from-src y
    pb-few′ (CE.echo y _ _ _ , _) = from-src y
    pb-few′ (CE.kept y _ _ _ , _) = from-src y

    postulate
      conn-pb-past : ∀ {k l e₀ e x y} → PB′ k l → t k e₀ → Live t k → u l e → M′ x y → x ≺ k → ¬ (x ⊑ k) → Ahead y l
      conn-img¬¬ : ∀ {k e} → t k e → Unpinned e → Live t k → Few t k
                 → ¬ ¬ ((Σ Pos λ l → ConnImg k l × Σ (Ev (IE B)) λ e′ → u l e′ × Match Every (One valuesOf) (Reads valuesOf) e e′) ⊎ e ≡ skip)
      conn-shown : ∀ {l e} → u l e → Shown (One valuesOf) e → Live u l → Few u l
                 → Σ Pos λ k → ConnImg k l × Σ (Ev B) λ e₀ → t k e₀ × Match Every (One valuesOf) (Reads valuesOf) e₀ e
      conn-place : ∀ {m e} → u m e → Live u m → Listed u m
                 → instantOf m ≡ instantOf p′ ⊎ (Σ Pos λ k → Σ Pos λ l → ConnImg k l × instantOf l ≡ instantOf m × Near u m l)
                   ⊎ Σ Pos λ h → HE h × instantOf h ≡ instantOf m
      conn-whole : Whole t → (∀ {c} → t c end → ⊥) → (∀ {q} → LP q) → Whole u
      conn-cover : ∀ {v w} → Listed t v → LP v → Live t v → From ConnImg PB′ t u v w → Listed u w
      conn-pinned : ∀ {k q} → t k (pin q) → Live t k → Listed t k → LP k
                  → (Σ Pos λ l → Σ Pos λ q′ → u l (pin q′) × PB′ k l × (∀ {k′ l′} → ConnImg k′ l′ → l′ ≺ q′ → k′ ≺ q) × Listed u l)
                    × (instantOf k ≡ instantOf p ⊎ (Σ Pos λ k₀ → k₀ ≺ q × Home t k₀ × instantOf k₀ ≡ instantOf k)
                       ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)

    -- ACROSS THE CONNECT'S TWO SUBTERMS: the elaborated source listed
    -- before the elaborated body row a reached body row is carried on,
    -- and the elaborated body before the echo of a reached source row's
    -- carrier.  Each side lists its own rows (the carriers' outputs);
    -- what neither carry says is how many rows of the other subterm,
    -- annotation marks included, precede.
    -- DEAD ROUTE: covering the elaborated source's rows before the body
    --   row by images of the plain source's rows before it (`shown` back,
    --   the order embedding forward) covers only the shown ones; nothing
    --   bounds the unshown rows between two images.
    -- RECOVERY: git show 018ed286 restores `listed-in`, a subterm listed
    --   where few of its rows precede under listed functional hots.
    postulate
      conn-σ-late : ∀ {k l e} → ¬ ¬ Σ (Ev B) (CP.β k) → Few CP.ConnT k → Listed t k → LP k → B′.PB k l → CE.β l e → Listed CE.β l
                  → Listed CE.σ l
      conn-σ-ended : ∀ {k l c e} → ¬ ¬ Σ (Ev B) (CP.β k) → B′.Img k l → c ≺ k → CP.σ c end → Listed CP.σ k → LP k → CE.β l e
                   → Listed CE.β l → Listed CE.σ l
      conn-β-late : ∀ {k l e e′} → CP.σ k e → Unpinned e → CP.Alive k → T (not (inside r k)) → Few CP.ConnT (k ⊕ [ ix 0 ]) → Listed t (k ⊕ [ ix 0 ])
                  → LP (k ⊕ [ ix 0 ]) → Live t (k ⊕ [ ix 0 ]) → A′.PB k l → CE.σ l e′ → Listed CE.σ l → Listed CE.β (l ⊕ [ ix 0 ])

    -- A reached echo's annotation image is echoed, unshown, in the
    -- elaborated connect; one carried only into its instant is carried
    -- one label under the annotation's carrier.
    postulate
      conn-echo-row : ∀ {k l e e′} → CP.σ k e → Unpinned e → CP.Alive k → T (not (inside r k)) → Few CP.ConnT (k ⊕ [ ix 0 ])
                    → A′.Img k l → CE.σ l e′ → Match Every (One annValues) (Reads annValues) e e′
                    → Σ (Ev (IE B)) λ e″ → CE.ConnT (l ⊕ [ ix 0 ]) e″ × ¬ Shown (One valuesOf) e″
      conn-src-carrier : ∀ {k l e e′} → CP.σ k e → CP.Alive k → T (not (inside r k)) → Few CP.ConnT (k ⊕ [ ix 0 ])
                       → A′.PB k l → CE.σ l e′ → Σ (Ev (IE B)) (CE.ConnT (l ⊕ [ ix 0 ]))

    -- A body row's image follows every elaborated source row carrying a
    -- live source row from the body row on: an image by the order
    -- embedding, a late carrier by the source's carry.
    body-from : ∀ {k l} → ¬ ¬ Σ (Ev B) (CP.β k) → B′.Img k l → From A′.Img A′.PB CP.σ CE.σ k l
    body-from {k} {l} nb i {k′} {_} {l′} tk′ lk′ kk′ m ul′ l′l =
      ≺-irrefl {l} (≺-trans {l} {l′} {l} (proj₁ (ahead-under (ahead m) (proj₂ (proj₂ (B′.ext i))))) l′l)
      where
        y = proj₁ (B′.ext i)
        my = proj₁ (proj₂ (B′.ext i))

        nk : ¬ (k ⊑ k′)
        nk kk = nb λ (_ , b) → leads b tk′ kk

        lt : k ≺ k′
        lt with ≼-split {k} {k′} kk′
        ... | inj₁ lt′ = lt′
        ... | inj₂ eq  = ⊥-elim (nk (subst (k ⊑_) eq (⊑-refl k)))

        ahead : A′.Img k′ l′ ⊎ A′.PB k′ l′ → Ahead y l′
        ahead (inj₁ i′) = ahead-over (Emb.mono emb′ (inj₁ my) (inj₁ (ms_b my′)) lt , λ yy → nk (Emb.reflect emb′ (inj₁ my) (inj₁ (ms_b my′)) yy))
                                     (proj₂ (proj₂ (A′.ext i′)))
          where my′ = proj₁ (proj₂ (A′.ext i′))
        ahead (inj₂ pb) = past-a pb tk′ lk′ ul′ my lt nk

    -- The elaborated source listed before a reached body row's carrier:
    -- the source's carry covers it from the body row on, while the
    -- source is alive there.
    conn-σ-body : ∀ {k l e} → ¬ ¬ Σ (Ev B) (CP.β k) → Few CP.ConnT k → Listed t k → LP k → B′.Img k l ⊎ B′.PB k l → CE.β l e → Listed CE.β l
                → Listed CE.σ l
    conn-σ-body nb F L lp (inj₂ pb) ul Lβ = conn-σ-late nb F L lp pb ul Lβ
    conn-σ-body nb F L lp (inj₁ i) ul Lβ with live-or-ended (InvAt.func Iσ) (PL.src-under nb F L)
    ... | inj₁ lv = A′.cover (PL.src-under nb F L) lp lv (body-from nb i)
    ... | inj₂ (c , ck , ce) = conn-σ-ended nb i ck ce (PL.src-under nb F L) lp ul Lβ

    -- An echo's carrier follows every elaborated body row carrying a live
    -- body row from the echo on: an image past the echo by the order
    -- embedding; a late carrier past the source row by the body's carry,
    -- under it by its anchor.
    echo-from : ∀ {k l e} → CP.σ k e → Unpinned e → A′.Img k l → From B′.Img B′.PB CP.β CE.β (k ⊕ [ ix 0 ]) (l ⊕ [ ix 0 ])
    echo-from {k} {l} x un i {k₂} {_} {l₂} b₂ lk₂ kk₂ m ul₂ l₂l = go m
      where
        E : M′ (k ⊕ [ ix 0 ]) (l ⊕ [ ix 0 ])
        E = inj₂ (k , l , (_ , x) , i , refl , refl)

        ff : ∀ {x′ y′} → M′ x′ y′ → (k ⊕ [ ix 0 ]) ≺ x′ → y′ ⊑ l₂ → ⊥
        ff m′ lt′ yl = follows emb′ E m′ lt′ yl l₂l

        lt : (k ⊕ [ ix 0 ]) ≺ k₂
        lt with ≼-split {k ⊕ [ ix 0 ]} {k₂} kk₂
        ... | inj₁ lt′ = lt′
        ... | inj₂ eq  = ⊥-elim (SP.img-body x b₂ (subst ((k ⊕ [ ix 0 ]) ⊑_) eq (⊑-refl _)))

        kk : k ≺ k₂
        kk = ≺-trans {k} {k ⊕ [ ix 0 ]} {k₂} (≺-ext k []) lt

        past : ¬ (k ⊑ k₂) → B′.PB k₂ l₂ → ⊥
        past nk pb = ≺-irrefl {l₂} (≺-trans {l₂} {l ⊕ [ ix 0 ]} {l₂} l₂l
                       (proj₁ (ahead-under (ahead-under (B′.pb-past pb b₂ lk₂ ul₂ (ms_b my) kk nk) yl) ([ ix 0 ] , refl))))
          where my = proj₁ (proj₂ (A′.ext i))
                yl = proj₂ (proj₂ (A′.ext i))

        under : B′.PB k₂ l₂ → k ⊑ k₂ → ⊥
        under pb ([] , eq) = ≺-irrefl {k} (subst (k ≺_) (trans eq (⊕-identityʳ k)) kk)
        under pb (a ∷ σ , eq) with nest pb b₂ lk₂ (_ , x , src-live x un) i eq
        ... | _ , _ , m′ , yl , inj₂ kx = ff (inj₁ m′) (≺-trans {k ⊕ [ ix 0 ]} {k₂} {_} lt kx) yl
        ... | x′ , _ , m′ , yl , inj₁ (ax , xk) = ff (inj₁ m′) (≺-≼-≺ {k ⊕ [ ix 0 ]} {k ⊕ [ a ]} {x′} ka (⊑-≼ ax)) yl
          where
            ka : (k ⊕ [ ix 0 ]) ≺ (k ⊕ [ a ])
            ka with ≼-or-≻ (k ⊕ [ ix 0 ]) (k ⊕ [ a ])
            ... | inj₂ ak = ⊥-elim (first-child k (≺-ext k []) ak)
            ... | inj₁ le with ≼-split {k ⊕ [ ix 0 ]} {k ⊕ [ a ]} le
            ...   | inj₁ lt′ = lt′
            ...   | inj₂ eq′ = ⊥-elim (SP.img-body x b₂ (subst (_⊑ k₂) (sym eq′) (⊑-trans ax xk)))

        go : B′.Img k₂ l₂ ⊎ B′.PB k₂ l₂ → ⊥
        go (inj₁ i₂) = ff (inj₁ (proj₁ (proj₂ (B′.ext i₂)))) lt (proj₂ (proj₂ (B′.ext i₂)))
        go (inj₂ pb) = past (under pb) pb

    -- The elaborated body listed before a reached echo's carrier: the
    -- body's carry covers it from the echo on, the elaborated body alive
    -- there.
    conn-β-echo : ∀ {k l e e′} → CP.σ k e → Unpinned e → CP.Alive k → T (not (inside r k)) → Few CP.ConnT (k ⊕ [ ix 0 ]) → Listed t (k ⊕ [ ix 0 ])
                → LP (k ⊕ [ ix 0 ]) → Live t (k ⊕ [ ix 0 ]) → A′.Img k l ⊎ A′.PB k l → CE.σ l e′ → Listed CE.σ l → Listed CE.β (l ⊕ [ ix 0 ])
    conn-β-echo x un al ni F L lp lv (inj₂ pb) ul Lσ = conn-β-late x un al ni F L lp lv pb ul Lσ
    conn-β-echo x un al ni F L lp lv (inj₁ i) ul Lσ =
      B′.cover (PL.body-listed F L) (listed-proper (InvAt.func Iσ) (listed-step (PL.src-before x al F L) x) , lp) (body-live F lv) (echo-from x un i)

    -- An elaborated body row, listed with the source before it, is a row
    -- of the elaborated connect listed there.
    body-row : ∀ {l e} → CE.β l e → Listed CE.β l → Listed CE.σ l → u l e × Listed u l
    body-row ul Lβ Lσ = (CE.body ul , few-reach {e = _} (EL.conn-few Lβ Lσ)) , EL.conn-listed Lβ Lσ

    -- A row one label under a listed source row, the body listed there.
    echo-row : ∀ {l e e′} → CE.σ l e′ → Listed CE.σ l → Listed CE.β (l ⊕ [ ix 0 ]) → CE.ConnT (l ⊕ [ ix 0 ]) e
             → u (l ⊕ [ ix 0 ]) e × Listed u (l ⊕ [ ix 0 ])
    echo-row ul Lσ Lβ c = (c , few-reach {e = _} (EL.conn-few Lβ Lσ′)) , EL.conn-listed Lβ Lσ′
      where Lσ′ = listed-step Lσ ul

    -- What the connect's instants are: the subscribe frame's, a carried
    -- row's, or an environment hot's.
    Homed : Pos → Set
    Homed k = instantOf k ≡ instantOf p
            ⊎ (Σ Pos λ k₀ → Σ Pos λ l₀ → ConnImg k₀ l₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k × Σ (Ev (IE B)) (u l₀) × Listed u l₀)
            ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k

    -- A source row's instant, a reached row's: its source's, an echo's.
    postulate
      conn-heard-home : ∀ {h k e e′} → CP.σ h e → instantOf h ≡ instantOf k → t k e′ → Listed t k → Homed k
      conn-src-home : ∀ {k₀ k₁ l₁ e₀ e₁} → CP.σ k₀ e₀ → CP.Alive k₀ → T (not (inside r k₀)) → Listed t (k₀ ⊕ [ ix 0 ])
                    → A′.Img k₁ l₁ → k₁ ≺ k₀ → instantOf k₁ ≡ instantOf k₀ → CE.σ l₁ e₁ → Listed CE.σ l₁ → Homed (k₀ ⊕ [ ix 0 ])

    private
      -- A reached row of the connect: few rows of the connect before it.
      reached : ∀ {k e} → t k e → Unpinned e → Few CP.ConnT k
      reached (_ , R) un = reach-few (full un) R

      body-home : ∀ {k e} → CP.β k e → Few CP.ConnT k → Listed t k → LP k
                → instantOf k ≡ instantOf (p ⊕ [ ix 0 ])
                  ⊎ (Σ Pos λ k₀ → Σ Pos λ l₀ → B′.Img k₀ l₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k × Σ (Ev (IE B)) (CE.β l₀) × Listed CE.β l₀)
                  ⊎ Σ Pos (λ h → (HP ∪ʰ Proper CP.σ) h × instantOf h ≡ instantOf k)
                → Homed k
      body-home {k} b F L lp (inj₁ e) = inj₁ (trans e (instant-⊕ p [ ix 0 ]))
      body-home {k} b F L lp (inj₂ (inj₁ (k₀ , l₀ , i , kk , ek , (e₀ , ul) , L₀))) =
        inj₂ (inj₁ (k₀ , l₀ , inj₁ (i , F₀) , kk , ek , (e₀ , proj₁ R) , proj₂ R))
        where F₀ = few-sub {a = CP.ConnT} {w = k} {v = k₀} F kk
              R = body-row ul L₀ (conn-σ-body (λ n → B′.img-row i λ (e , b , _) → n (e , b)) F₀ (sub-listed L kk) (lp↓ (≺→≼ {k₀} {k} kk) lp) (inj₁ i) ul L₀)
      body-home b F L lp (inj₂ (inj₂ (h , inj₂ hp , eh))) = inj₂ (inj₂ (h , hp , eh))
      body-home b F L lp (inj₂ (inj₂ (h , inj₁ (_ , x , _) , eh))) = conn-heard-home x eh (CP.body b , few-reach {e = _} F) L

      src-home : ∀ {k₀ e₀} → CP.σ k₀ e₀ → CP.Alive k₀ → T (not (inside r k₀)) → Listed t (k₀ ⊕ [ ix 0 ])
               → instantOf k₀ ≡ instantOf r
                 ⊎ (Σ Pos λ k₁ → Σ Pos λ l₁ → A′.Img k₁ l₁ × k₁ ≺ k₀ × instantOf k₁ ≡ instantOf k₀ × Σ (Ev (AIE A)) (CE.σ l₁) × Listed CE.σ l₁)
                 ⊎ Σ Pos (λ h → HP h × instantOf h ≡ instantOf k₀)
               → Homed (k₀ ⊕ [ ix 0 ])
      src-home {k₀} x al ni L (inj₁ e) = inj₁ (trans (instant-⊕ k₀ [ ix 0 ]) (trans e (instant-⊕ p [ ix 1 ])))
      src-home x al ni L (inj₂ (inj₁ (k₁ , l₁ , i , kk , ek , (_ , y) , L₁))) = conn-src-home x al ni L i kk ek y L₁
      src-home {k₀} x al ni L (inj₂ (inj₂ (h , hp , eh))) = inj₂ (inj₂ (h , hp , trans eh (sym (instant-⊕ k₀ [ ix 0 ]))))

    conn-img : ∀ {k e} → t k e → Unpinned e → Live t k → Listed t k → LP k
             → (Σ Pos λ l → ConnImg k l × Σ (Ev (IE B)) λ e′ → u l e′ × Listed u l × Match Every (One valuesOf) (Reads valuesOf) e e′)
               ⊎ (e ≡ skip × IntoAt ConnImg u PB′ HP p k)
    conn-img tk@(CP.body b , _) un lv L lp with B′.img b un (body-live (reached tk un) lv) (PL.body-listed (reached tk un) L) (PL.hot-listed b (reached tk un) L , lp)
    ... | inj₁ (l , i , e′ , ul , Lβ , m) = inj₁ (l , inj₁ (i , F) , e′ , proj₁ R , proj₂ R , m)
      where F = reached tk un
            R = body-row ul Lβ (conn-σ-body (λ n → n (_ , b)) F L lp (inj₁ i) ul Lβ)
    ... | inj₂ (es , ((l , (e″ , ul) , Lβ , pb) , h)) =
      inj₂ (es , ((l , (e″ , proj₁ R) , proj₂ R , inj₁ (pb , (_ , b) , (e″ , ul))) , body-home b F L lp h))
      where F = reached tk un
            R = body-row ul Lβ (conn-σ-body (λ n → n (_ , b)) F L lp (inj₂ pb) ul Lβ)
    conn-img (CP.burst _ _ , _) ()
    conn-img (CP.kept _ _ _ _ , _) ()
    conn-img {k} tk@(CP.echo {k₀} x al un₀ ni , _) un lv L lp
      with A′.img x un₀ (src-live x un₀) (PL.src-before x al (reached tk un) L) (lp↓ (≺→≼ {k₀} {k} (≺-ext k₀ [])) lp)
    ... | inj₁ (l₀ , i , e′ , ul₀ , L₀ , m) with conn-echo-row x un₀ al ni (reached tk un) i ul₀ m
    ...   | e″ , c , ns =
      inj₁ (l₀ ⊕ [ ix 0 ] , inj₂ (k₀ , l₀ , (_ , x , un₀) , al , ni , i , reached tk un , refl , refl) , e″ , proj₁ R , proj₂ R
           , (λ ()) , λ _ → ns)
      where R = echo-row ul₀ L₀ (conn-β-echo x un₀ al ni (reached tk un) L lp lv (inj₁ i) ul₀ L₀) c
    conn-img tk@(CP.echo {k₀} x al un₀ ni , _) un lv L lp | inj₂ (_ , ((l , (_ , ul) , Ll , pb) , h)) with conn-src-carrier x al ni (reached tk un) pb ul
    ... | e″ , c = inj₂ (refl , ((l ⊕ [ ix 0 ] , (e″ , proj₁ R) , proj₂ R , inj₂ (k₀ , l , (_ , x) , inj₂ pb , refl , refl , (_ , ul))) , src-home x al ni L h))
      where R = echo-row ul Ll (conn-β-echo x un₀ al ni (reached tk un) L lp lv (inj₂ pb) ul Ll) c

    carried : CarryAt valuesOf M′ HP HE LP t u p p′
    carried = record
      { Img = ConnImg ; ext = ext′ ; PB = PB′ ; pb-few = pb-few′ ; pb-img = pb-img′ ; pb-past = conn-pb-past
      ; img = conn-img ; img¬¬ = conn-img¬¬ ; shown = conn-shown ; img-row = img-row′ ; img-fun = img-fun′
      ; place = conn-place ; live = live′ ; few = few′ ; whole = conn-whole ; bk = bk′ ; in-bk = in-bk′ ; pinned = conn-pinned ; cover = conn-cover }
