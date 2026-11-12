{-# OPTIONS --guardedness #-}

-- THE CONNECT CARRIES ITS ROWS from its body's carry and its annotated
-- source's: each body row on its body carrier, each source row's echo
-- one label under its annotation's image, each burst, kept or heard row
-- into its instant on the annotation's carrier one label down.  A row
-- is carried only where the connect reaches it: few rows of the connect
-- before it.
module simultaneous.CarryConn where

open import Data.Bool using (T; not)
open import Data.Bool.Properties using (T?)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; filter)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.All using (All; all?; tabulate; lookup)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; ¬?)
open import Relation.Nullary.Decidable using (decidable-stable)

open import denotation.Position using (Pos; ix; _⊕_; inside; _≟ᵖ_; root; _<ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Few; Reach; Truncate; Proper; Den; hot; _≺_; _≼_; module Connect)
open import denotation.Laws.Modulus using (≼-or-≻; ≺→≼; ≺-ext; reach-few; ≼-split; ≺-trans; ≺-irrefl; ≼-≺-≺)
open import denotation.Laws.Shows using (few-reach)
open import denotation.Laws.Worlds using (InvD; InvAt; Lawful; Ok; _∪ʰ_; _⊑_; ⊑-refl; ⊕-injˡ; full)
import denotation.Laws.Connect as LC
open import denotation.Laws.ConnectNe using (module Rows)
import denotation.Laws.Truth.Connect.Cuts as Cuts
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (Live; Shown; Match; Every; One; Reads)
open import simultaneous.Listing using (Listed)
open import simultaneous.CarryBase using (PMap; _∪ᴹ_; _⊆ᴹ_; Emb; CarryAt; IntoAt; Near; Home; Whole; Ahead; few-sub; sub-listed; listed-≼; instant-⊕)
open import simultaneous.ListedIn using (Func)
open import simultaneous.Carry using (annValues)
open import simultaneous.ReadRows using (up; up-⊕)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE)

private
  nin : ∀ {r k} → T (not (inside r k)) → T (inside r k) → ⊥
  nin {r} {k} ni i with inside r k
  ... | Data.Bool.true  = ni
  ... | Data.Bool.false = i

  trunc-few : ∀ {X : Set} {C : EmissionSet X} {k} → Few C k → Few (Truncate C) k
  trunc-few (ks , h) = ks , λ y kq → h (proj₁ y) kq

  pin-un : ∀ {X : Set} {q} → Unpinned {X} (pin q) → ⊥
  pin-un ()

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

  -- A functional set listed: its proper rows listed, a row proper where
  -- no end listed precedes it.
  listed-proper : ∀ {X : Set} {t : EmissionSet X} {q} → Func t → Listed t q → Listed (Proper t) q
  listed-proper {X} {t} {q} f (ks , F , B) = filter keep? ks , cover , back
    where
      d : ∀ {k} → k ∈ ks → List Pos
      d {k} m = endOf k (proj₁ (proj₂ (B m)))

      ends : List Pos
      ends = gather ks d

      is-end : ∀ {c} → c ∈ ends → t c end
      is-end m with gather-sound ks d m
      ... | k , mk , jd with endOf-sound k (proj₁ (proj₂ (B mk))) jd
      ...   | refl , eq = subst (t k) eq (proj₂ (proj₂ (B mk)))

      has-end : ∀ {c} → t c end → c ≺ q → c ∈ ends
      has-end {c} x cq = gather-complete ks d (F x cq) (subst (λ e → c ∈ endOf c e) (f x (proj₂ (proj₂ (B (F x cq))))) (here refl))

      keep? : ∀ j → _
      keep? j = all? (λ c → ¬? (T? (c <ᵖ j))) ends

      cover : ∀ {j e} → Proper t j e → j ≺ q → j ∈ filter keep? ks
      cover {j} (x , pr) jq = ∈-filter⁺ keep? (F x jq) (tabulate λ {c} mc cj → ≺-irrefl {j} (≼-≺-≺ {j} {c} {j} (pr (is-end mc)) cj))

      back : ∀ {j} → j ∈ filter keep? ks → j ≺ q × Σ (Ev X) (Proper t j)
      back {j} m with ∈-filter⁻ keep? {xs = ks} m
      ... | mj , al with B mj
      ...   | jq , e , x = jq , e , x , pr
        where
          pr : ∀ {c} → t c end → j ≼ c
          pr {c} y with ≼-or-≻ j c
          ... | inj₁ jc = jc
          ... | inj₂ cj = ⊥-elim (lookup al (has-end y (≺-trans {c} {j} {q} cj jq)) cj)

module ConnCarry {A B : Set} {HP HE LP : Pos → Set} {sP : Den A} {FP : Den A → Den B} {sE : Den (AIE A)} {FE : Den (AIE A) → Den (IE B)}
                 (IsP : InvD HP sP) (IFP : ∀ {t} → Lawful t → InvD (HP ∪ʰ t) (FP (hot t)))
                 (IsE : InvD HE sE) (IFE : ∀ {t} → Lawful t → InvD (HE ∪ʰ t) (FE (hot t)))
                 (p p′ : Pos) (okP : Ok HP p) (okE : Ok HE p′) (lp↓ : ∀ {x y} → x ≼ y → LP y → LP x)
                 (M_s : PMap) (c_a : CarryAt annValues M_s HP HE LP (Connect.σ sP FP p) (Connect.σ sE FE p′) (p ⊕ [ ix 1 ]) (p′ ⊕ [ ix 1 ])) where
  module CP = Connect sP FP p
  module CE = Connect sE FE p′
  module A′ = CarryAt c_a
  module SP = Cuts.Side {s = sP} {F = FP} IsP IFP p okP

  module RP = Rows {s = sP} {F = FP} IsP IFP p okP

  Iσ : InvAt HP (p ⊕ [ ix 1 ]) CP.σ
  Iσ = LC.Iσ {s = sP} {F = FP} IsP IFP p okP

  -- An unpinned source row lies before the source's end.
  src-live : ∀ {k e} → CP.σ k e → Unpinned e → Live CP.σ k
  src-live {k} x un {c} y with ≼-or-≻ k c
  ... | inj₁ kc = kc
  ... | inj₂ ck with InvAt.quiet Iσ y x ck
  ...   | q , refl , _ = ⊥-elim (pin-un {A} {q} un)

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
                             CP.β CE.β (p ⊕ [ ix 0 ]) (p′ ⊕ [ ix 0 ])) where
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

    Img′ : Pos → Pos → Set
    Img′ k l = BodyImg k l ⊎ EchoImg k l

    -- A source row carried into its instant, or in the burst on its
    -- image: one label down on the annotation's carrier.
    SrcPB : Pos → Pos → Set
    SrcPB k l = Σ Pos λ k₀ → Σ Pos λ l₀ → Σ (Ev A) (CP.σ k₀) × ((A′.Img k₀ l₀ × T (inside r k₀)) ⊎ A′.PB k₀ l₀)
              × k ≡ k₀ ⊕ [ ix 0 ] × l ≡ l₀ ⊕ [ ix 0 ]

    PB′ : Pos → Pos → Set
    PB′ k l = (B′.PB k l × Σ (Ev B) (CP.β k)) ⊎ SrcPB k l

    ext′ : ∀ {k l} → Img′ k l → Σ Pos λ y → M′ k y × y ⊑ l
    ext′ (inj₁ (i , _)) with B′.ext i
    ... | y , m , yl = y , inj₁ m , yl
    ext′ (inj₂ (k₀ , l₀ , (e₀ , x , _) , _ , _ , i , _ , refl , refl)) = l₀ ⊕ [ ix 0 ] , inj₂ (k₀ , l₀ , (e₀ , x) , i , refl , refl) , ⊑-refl _

    few′ : ∀ {k l} → Img′ k l → Few t k
    few′ (inj₁ (_ , F))                          = trunc-few F
    few′ (inj₂ (_ , _ , _ , _ , _ , _ , F , _)) = trunc-few F

    img-row′ : ∀ {k l} → Img′ k l → ¬ ¬ Σ (Ev B) λ e → t k e × Unpinned e
    img-row′ (inj₁ (i , F)) no = B′.img-row i λ { (e , b , un) → no (e , (CP.body b , few-reach {e = e} F) , un) }
    img-row′ (inj₂ (_ , _ , (_ , x , un) , al , ni , _ , F , refl , _)) no = no (skip , (CP.echo x al un ni , few-reach {e = skip} F) , _)

    img-fun′ : ∀ {k a b} → Img′ k a → Img′ k b → a ≡ b
    img-fun′ (inj₁ (i , _)) (inj₁ (i′ , _)) = B′.img-fun i i′
    img-fun′ {a = a} {b} (inj₁ (i , _)) (inj₂ (_ , _ , (_ , x , _) , _ , _ , _ , _ , refl , _)) =
      decidable-stable (a ≟ᵖ b) λ _ → B′.img-row i λ { (_ , y , _) → SP.img-body x y (⊑-refl _) }
    img-fun′ {a = a} {b} (inj₂ (_ , _ , (_ , x , _) , _ , _ , _ , _ , refl , _)) (inj₁ (i , _)) =
      decidable-stable (a ≟ᵖ b) λ _ → B′.img-row i λ { (_ , y , _) → SP.img-body x y (⊑-refl _) }
    img-fun′ (inj₂ (k₀ , _ , _ , _ , _ , i , _ , e , refl)) (inj₂ (k₁ , _ , _ , _ , _ , i′ , _ , e′ , refl))
      with ⊕-injˡ k₀ k₁ (trans (sym e) e′)
    ... | refl = cong (_⊕ [ ix 0 ]) (A′.img-fun i i′)

    pb-img′ : ∀ {k l l′} → PB′ k l → Img′ k l′ → ⊥
    pb-img′ (inj₁ (pb , _)) (inj₁ (i , _)) = B′.pb-img pb i
    pb-img′ (inj₁ (_ , _ , b)) (inj₂ (_ , _ , (_ , x , _) , _ , _ , _ , _ , refl , _)) = SP.img-body x b (⊑-refl _)
    pb-img′ (inj₂ (_ , _ , (_ , x) , _ , refl , _)) (inj₁ (i , _)) = B′.img-row i λ { (_ , y , _) → SP.img-body x y (⊑-refl _) }
    pb-img′ (inj₂ (k₀ , _ , _ , w , e , _)) (inj₂ (k₁ , _ , _ , _ , ni , i′ , _ , e′ , _)) with ⊕-injˡ k₀ k₁ (trans (sym e) e′)
    pb-img′ (inj₂ (_ , _ , _ , inj₁ (_ , ins) , _ , _)) (inj₂ (k₀ , _ , _ , _ , ni , _ , _ , _ , _)) | refl = nin {r} {k₀} ni ins
    pb-img′ (inj₂ (_ , _ , _ , inj₂ pb , _ , _))       (inj₂ (_ , _ , _ , _ , _ , i′ , _ , _ , _)) | refl = A′.pb-img pb i′

    -- The rows a carrier carries: the body's, and the echoes of the
    -- annotation's.
    bk′ : Pos → List Pos
    bk′ l = B′.bk l ++ L.map (_⊕ [ ix 0 ]) (A′.bk (up l))

    in-bk′ : ∀ {k l} → Img′ k l → k ∈ bk′ l
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

    live′ : ∀ {k l} → Img′ k l → Live t k → Live u l
    live′ (inj₁ (i , F)) lv = live-u (B′.live i (body-live F lv))
    live′ (inj₂ ei)      lv = conn-echo-live ei lv

    postulate
      conn-pb-few : ∀ {l e} → u l e → Σ (List Pos) λ ks → ∀ {k} → PB′ k l → k ∈ ks
      conn-pb-past : ∀ {k l e₀ e x y} → PB′ k l → t k e₀ → Live t k → u l e → M′ x y → x ≺ k → ¬ (x ⊑ k) → Ahead y l
      conn-img¬¬ : ∀ {k e} → t k e → Unpinned e → Live t k → Few t k
                 → ¬ ¬ ((Σ Pos λ l → Img′ k l × Σ (Ev (IE B)) λ e′ → u l e′ × Match Every (One valuesOf) (Reads valuesOf) e e′) ⊎ e ≡ skip)
      conn-shown : ∀ {l e} → u l e → Shown (One valuesOf) e → Live u l → Few u l
                 → Σ Pos λ k → Img′ k l × Σ (Ev B) λ e₀ → t k e₀ × Match Every (One valuesOf) (Reads valuesOf) e₀ e
      conn-place : ∀ {m e} → u m e → Live u m → Listed u m
                 → instantOf m ≡ instantOf p′ ⊎ (Σ Pos λ k → Σ Pos λ l → Img′ k l × instantOf l ≡ instantOf m × Near u m l)
                   ⊎ Σ Pos λ h → HE h × instantOf h ≡ instantOf m
      conn-whole : Whole t → (∀ {c} → t c end → ⊥) → (∀ {q} → LP q) → Whole u
      conn-pinned : ∀ {k q} → t k (pin q) → Live t k → Listed t k → LP k
                  → (Σ Pos λ l → Σ Pos λ q′ → u l (pin q′) × PB′ k l × (∀ {k′ l′} → Img′ k′ l′ → l′ ≺ q′ → k′ ≺ q) × Listed u l)
                    × (instantOf k ≡ instantOf p ⊎ (Σ Pos λ k₀ → k₀ ≺ q × Home t k₀ × instantOf k₀ ≡ instantOf k)
                       ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)

    -- The rows the connect lists before a row it reaches: its body's,
    -- and its source's wherever each shows below the row.
    private
      bodyOf : ∀ {k e} → CP.ConnT k e → List Pos
      bodyOf {k} (CP.body _)   = [ k ]
      bodyOf (CP.burst _ _)    = []
      bodyOf (CP.echo _ _ _ _) = []
      bodyOf (CP.kept _ _ _ _) = []

      bodyOf-sound : ∀ {k e} (w : CP.ConnT k e) {j} → j ∈ bodyOf w → j ≡ k × Σ (Ev B) (CP.β k)
      bodyOf-sound (CP.body b) (here refl) = refl , _ , b

      bodyOf-complete : ∀ {k e e′} → CP.β k e → (w : CP.ConnT k e′) → k ∈ bodyOf w
      bodyOf-complete b (CP.body _)       = here refl
      bodyOf-complete b (CP.burst x _)    = ⊥-elim (SP.img-body x b (⊑-refl _))
      bodyOf-complete b (CP.echo x _ _ _) = ⊥-elim (SP.img-body x b (⊑-refl _))
      bodyOf-complete b (CP.kept x _ _ _) = ⊥-elim (SP.img-body x b (⊑-refl _))

      srcOf : ∀ {k e} → CP.ConnT k e → List Pos
      srcOf (CP.body _)           = []
      srcOf (CP.burst {j} _ _)    = [ j ]
      srcOf (CP.echo {j} _ _ _ _) = [ j ]
      srcOf (CP.kept {j} _ _ _ _) = [ j ]

      srcOf-sound : ∀ {k e} (w : CP.ConnT k e) {j} → j ∈ srcOf w → Σ (Ev A) (CP.σ j) × k ≡ j ⊕ [ ix 0 ]
      srcOf-sound (CP.burst x _)    (here refl) = (_ , x) , refl
      srcOf-sound (CP.echo x _ _ _) (here refl) = (_ , x) , refl
      srcOf-sound (CP.kept x _ _ _) (here refl) = (_ , x) , refl

      srcOf-complete : ∀ {j e₀ k e} → CP.σ j e₀ → (w : CP.ConnT k e) → k ≡ j ⊕ [ ix 0 ] → j ∈ srcOf w
      srcOf-complete x (CP.body b) refl                      = ⊥-elim (SP.img-body x b (⊑-refl _))
      srcOf-complete {j} x (CP.burst {j′} _ _) eq    = here (⊕-injˡ j j′ (sym eq))
      srcOf-complete {j} x (CP.echo {j′} _ _ _ _) eq = here (⊕-injˡ j j′ (sym eq))
      srcOf-complete {j} x (CP.kept {j′} _ _ _ _) eq = here (⊕-injˡ j j′ (sym eq))

    body-listed : ∀ {k} → Few CP.ConnT k → Listed t k → Listed CP.β k
    body-listed {k} Fk (ks , Fl , Bk) = gather ks d , cover , back
      where
        d : ∀ {j} → j ∈ ks → List Pos
        d m = bodyOf (proj₁ (proj₂ (proj₂ (Bk m))))

        cover : ∀ {j e} → CP.β j e → j ≺ k → j ∈ gather ks d
        cover {j} b jk = gather-complete ks d m (bodyOf-complete b (proj₁ (proj₂ (proj₂ (Bk m)))))
          where m = Fl (CP.body b , few-reach {e = _} (few-sub {a = CP.ConnT} {w = k} {v = j} Fk jk)) jk

        back : ∀ {j} → j ∈ gather ks d → j ≺ k × Σ (Ev B) (CP.β j)
        back mj with gather-sound ks d mj
        ... | _ , mk , jd with bodyOf-sound (proj₁ (proj₂ (proj₂ (Bk mk)))) jd
        ...   | refl , w = proj₁ (Bk mk) , w

    -- The source rows before a position, each alive and shown below it.
    src-listed : ∀ {q} → Few CP.ConnT q → Listed t q → (∀ {j e} → CP.σ j e → j ≺ q → CP.Alive j × (j ⊕ [ ix 0 ]) ≺ q) → Listed CP.σ q
    src-listed {q} Fq (ks , Fl , Bk) sh = gather ks d , cover , back
      where
        d : ∀ {j} → j ∈ ks → List Pos
        d m = srcOf (proj₁ (proj₂ (proj₂ (Bk m))))

        cover : ∀ {j e} → CP.σ j e → j ≺ q → j ∈ gather ks d
        cover {j} x jq with sh x jq
        ... | al , jq′ with RP.img x (inj₁ al)
        ...   | _ , c = gather-complete ks d m (srcOf-complete x (proj₁ (proj₂ (proj₂ (Bk m)))) refl)
          where m = Fl (c , few-reach {e = _} (few-sub {a = CP.ConnT} {w = q} {v = j ⊕ [ ix 0 ]} Fq jq′)) jq′

        back : ∀ {j} → j ∈ gather ks d → j ≺ q × Σ (Ev A) (CP.σ j)
        back {j} mj with gather-sound ks d mj
        ... | k , mk , jd with srcOf-sound (proj₁ (proj₂ (proj₂ (Bk mk)))) jd
        ...   | w , refl = ≺-trans {j} {j ⊕ [ ix 0 ]} {q} (≺-ext j []) (proj₁ (Bk mk)) , w

    -- A source row before a body row, or another source row, shows below it.
    below-β : ∀ {j k e₀ e} → CP.σ j e₀ → CP.β k e → j ≺ k → (j ⊕ [ ix 0 ]) ≺ k
    below-β {j} {k} x b jk with ≼-split {j ⊕ [ ix 0 ]} {k} (Cuts.step≼ {j} {k} jk)
    ... | inj₁ lt   = lt
    ... | inj₂ refl = ⊥-elim (SP.img-body x b (⊑-refl _))

    below-σ : ∀ {j k e₀ e} → CP.σ j e₀ → CP.σ k e → j ≺ k → (j ⊕ [ ix 0 ]) ≺ k
    below-σ {j} {k} x y jk with ≼-split {j ⊕ [ ix 0 ]} {k} (Cuts.step≼ {j} {k} jk)
    ... | inj₁ lt   = lt
    ... | inj₂ refl = ⊥-elim (InvAt.flat Iσ x y)

    -- The hot a body row reads, listed before it.
    hot-listed : ∀ {k e} → CP.β k e → Few CP.ConnT k → Listed t k → Listed (Proper CP.σ) k
    hot-listed b Fk L = listed-proper (InvAt.func Iσ) (src-listed Fk L λ x jk → RP.alive-β b x jk , below-β x b jk)

    -- The source before an echo's row, listed.
    src-before : ∀ {k e} → CP.σ k e → CP.Alive k → Few CP.ConnT (k ⊕ [ ix 0 ]) → Listed t (k ⊕ [ ix 0 ]) → Listed CP.σ k
    src-before {k} x al F L =
      src-listed (few-sub {a = CP.ConnT} {w = k ⊕ [ ix 0 ]} {v = k} F kk) (sub-listed L kk)
                 λ {j} y jk → (λ {c} ce → ≺-trans {j} {k} {c} jk (al ce)) , below-σ y x jk
      where kk = ≺-ext k []

    -- The elaborated connect reaches what its body carries a reached
    -- body row on, and lists it where the plain connect is listed.
    postulate
      conn-body-reach : ∀ {k l e} → Few CP.ConnT k → B′.Img k l ⊎ B′.PB k l → CE.β l e → Reach CE.ConnT l e
      conn-body-listed : ∀ {k l e} → Few CP.ConnT k → Listed t k → B′.Img k l ⊎ B′.PB k l → CE.β l e → Listed CE.β l → Listed u l

    -- A reached echo's annotation image is echoed, unshown, in the
    -- elaborated connect, which is listed there where the plain one is
    -- at the echo.
    postulate
      conn-echo-row : ∀ {k l e e′} → CP.σ k e → Unpinned e → CP.Alive k → T (not (inside r k)) → Few CP.ConnT (k ⊕ [ ix 0 ])
                    → A′.Img k l → CE.σ l e′ → Match Every (One annValues) (Reads annValues) e e′
                    → Σ (Ev (IE B)) λ e″ → u (l ⊕ [ ix 0 ]) e″ × ¬ Shown (One valuesOf) e″
      conn-echo-listed : ∀ {k l e e′} → CP.σ k e → CP.Alive k → T (not (inside r k)) → Listed t (k ⊕ [ ix 0 ])
                       → A′.Img k l → CE.σ l e′ → Listed CE.σ l → Listed u (l ⊕ [ ix 0 ])

    -- A reached echo whose source row is carried only into its instant
    -- is carried one label under the annotation's carrier.
    postulate
      conn-src-carrier : ∀ {k l e e′} → CP.σ k e → CP.Alive k → T (not (inside r k)) → Listed t (k ⊕ [ ix 0 ])
                       → A′.PB k l → CE.σ l e′ → Listed CE.σ l → Σ (Ev (IE B)) (u (l ⊕ [ ix 0 ])) × Listed u (l ⊕ [ ix 0 ])

    -- What the connect's instants are: the subscribe frame's, a carried
    -- row's, or an environment hot's.
    Homed : Pos → Set
    Homed k = instantOf k ≡ instantOf p
            ⊎ (Σ Pos λ k₀ → Σ Pos λ l₀ → Img′ k₀ l₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k × Σ (Ev (IE B)) (u l₀) × Listed u l₀)
            ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k

    -- A source row's instant, a reached row's: its source's, an echo's.
    postulate
      conn-heard-home : ∀ {h k e e′} → CP.σ h e → instantOf h ≡ instantOf k → t k e′ → Listed t k → Homed k
      conn-src-home : ∀ {k₀ k₁ l₁ e₀ e₁} → CP.σ k₀ e₀ → CP.Alive k₀ → T (not (inside r k₀)) → Listed t (k₀ ⊕ [ ix 0 ])
                    → A′.Img k₁ l₁ → k₁ ≺ k₀ → instantOf k₁ ≡ instantOf k₀ → CE.σ l₁ e₁ → Listed CE.σ l₁ → Homed (k₀ ⊕ [ ix 0 ])

    private
      few-l : ∀ {X : Set} {a : EmissionSet X} {q} → Listed a q → Few a q
      few-l (ks , F , _) = ks , F

      -- A reached row of the connect: few rows of the connect before it.
      reached : ∀ {k e} → t k e → Unpinned e → Few CP.ConnT k
      reached (_ , R) un = reach-few (full un) R

      body-home : ∀ {k e} → CP.β k e → Few CP.ConnT k → Listed t k
                → instantOf k ≡ instantOf (p ⊕ [ ix 0 ])
                  ⊎ (Σ Pos λ k₀ → Σ Pos λ l₀ → B′.Img k₀ l₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k × Σ (Ev (IE B)) (CE.β l₀) × Listed CE.β l₀)
                  ⊎ Σ Pos (λ h → (HP ∪ʰ Proper CP.σ) h × instantOf h ≡ instantOf k)
                → Homed k
      body-home {k} b F L (inj₁ e) = inj₁ (trans e (instant-⊕ p [ ix 0 ]))
      body-home {k} b F L (inj₂ (inj₁ (k₀ , l₀ , i , kk , ek , (e₀ , ul) , L₀))) =
        inj₂ (inj₁ (k₀ , l₀ , inj₁ (i , F₀) , kk , ek , (e₀ , CE.body ul , conn-body-reach F₀ (inj₁ i) ul)
                   , conn-body-listed F₀ (listed-≼ L (≺→≼ {k₀} {k} kk)) (inj₁ i) ul L₀))
        where F₀ = few-sub {a = CP.ConnT} {w = k} {v = k₀} F kk
      body-home b F L (inj₂ (inj₂ (h , inj₂ hp , eh))) = inj₂ (inj₂ (h , hp , eh))
      body-home b F L (inj₂ (inj₂ (h , inj₁ (_ , x , _) , eh))) = conn-heard-home x eh (CP.body b , few-reach {e = _} F) L

      src-home : ∀ {k₀ e₀} → CP.σ k₀ e₀ → CP.Alive k₀ → T (not (inside r k₀)) → Listed t (k₀ ⊕ [ ix 0 ])
               → instantOf k₀ ≡ instantOf r
                 ⊎ (Σ Pos λ k₁ → Σ Pos λ l₁ → A′.Img k₁ l₁ × k₁ ≺ k₀ × instantOf k₁ ≡ instantOf k₀ × Σ (Ev (AIE A)) (CE.σ l₁) × Listed CE.σ l₁)
                 ⊎ Σ Pos (λ h → HP h × instantOf h ≡ instantOf k₀)
               → Homed (k₀ ⊕ [ ix 0 ])
      src-home {k₀} x al ni L (inj₁ e) = inj₁ (trans (instant-⊕ k₀ [ ix 0 ]) (trans e (instant-⊕ p [ ix 1 ])))
      src-home x al ni L (inj₂ (inj₁ (k₁ , l₁ , i , kk , ek , (_ , y) , L₁))) = conn-src-home x al ni L i kk ek y L₁
      src-home {k₀} x al ni L (inj₂ (inj₂ (h , hp , eh))) = inj₂ (inj₂ (h , hp , trans eh (sym (instant-⊕ k₀ [ ix 0 ]))))

    conn-img : ∀ {k e} → t k e → Unpinned e → Live t k → Listed t k → LP k
             → (Σ Pos λ l → Img′ k l × Σ (Ev (IE B)) λ e′ → u l e′ × Listed u l × Match Every (One valuesOf) (Reads valuesOf) e e′)
               ⊎ (e ≡ skip × IntoAt Img′ u PB′ HP p k)
    conn-img tk@(CP.body b , _) un lv L lp with B′.img b un (body-live (reached tk un) lv) (body-listed (reached tk un) L) (hot-listed b (reached tk un) L , lp)
    ... | inj₁ (l , i , e′ , ul , Lβ , m) =
      inj₁ (l , inj₁ (i , F) , e′ , (CE.body ul , conn-body-reach F (inj₁ i) ul) , conn-body-listed F L (inj₁ i) ul Lβ , m)
      where F = reached tk un
    ... | inj₂ (es , ((l , (e″ , ul) , Lβ , pb) , h)) =
      inj₂ (es , ((l , (e″ , CE.body ul , conn-body-reach F (inj₂ pb) ul) , conn-body-listed F L (inj₂ pb) ul Lβ , inj₁ (pb , (_ , b))) , body-home b F L h))
      where F = reached tk un
    conn-img (CP.burst _ _ , _) ()
    conn-img (CP.kept _ _ _ _ , _) ()
    conn-img {k} tk@(CP.echo {k₀} x al un₀ ni , _) un lv L lp
      with A′.img x un₀ (src-live x un₀) (src-before x al (reached tk un) L) (lp↓ (≺→≼ {k₀} {k} (≺-ext k₀ [])) lp)
    ... | inj₁ (l₀ , i , e′ , ul₀ , L₀ , m) with conn-echo-row x un₀ al ni (reached tk un) i ul₀ m
    ...   | e″ , ur , ns =
      inj₁ (l₀ ⊕ [ ix 0 ] , inj₂ (k₀ , l₀ , (_ , x , un₀) , al , ni , i , reached tk un , refl , refl) , e″ , ur
           , conn-echo-listed x al ni L i ul₀ L₀ , (λ ()) , λ _ → ns)
    conn-img tk@(CP.echo {k₀} x al un₀ ni , _) un lv L lp | inj₂ (_ , ((l , (_ , ul) , Ll , pb) , h)) with conn-src-carrier x al ni L pb ul Ll
    ... | ur , Lu = inj₂ (refl , ((l ⊕ [ ix 0 ] , ur , Lu , inj₂ (k₀ , l , (_ , x) , inj₂ pb , refl , refl)) , src-home x al ni L h))

    carried : CarryAt valuesOf M′ HP HE LP t u p p′
    carried = record
      { Img = Img′ ; ext = ext′ ; PB = PB′ ; pb-few = conn-pb-few ; pb-img = pb-img′ ; pb-past = conn-pb-past
      ; img = conn-img ; img¬¬ = conn-img¬¬ ; shown = conn-shown ; img-row = img-row′ ; img-fun = img-fun′
      ; place = conn-place ; live = live′ ; few = few′ ; whole = conn-whole ; bk = bk′ ; in-bk = in-bk′ ; pinned = conn-pinned }
