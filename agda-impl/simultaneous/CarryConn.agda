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
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (decidable-stable)
open import Data.List.Properties using (∷-injectiveˡ)

open import denotation.Position using (Pos; ix; _⊕_; inside; _≟ᵖ_; root; _<ᵖ_)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Few; Truncate; Proper; Den; hot; _≺_; _≼_;
  module Connect)
open import denotation.Laws.Modulus using (≼-or-≻; ≺→≼; ≺-ext; reach-few; few-ind; ≼-split; ≺-trans; ≺-irrefl; ≺-≼-≺)
open import denotation.Laws.BoundedInv using (first-child)
open import denotation.Laws.Shows using (few-reach)
open import denotation.Laws.Worlds using (InvD; InvAt; Lawful; Ok; _∪ʰ_; ⊑-snoc; _⊑_; ⊑-refl; ⊑-≼; ⊑-trans; ⊕-identityʳ; ⊕-injˡ; full;
  shrink; ⊑-inside; ext≢; ⊕-cancelˡ; ⊕-assoc)
import denotation.Laws.Connect as LC
open import denotation.Laws.ConnectNe using (module Rows)
import denotation.Laws.Truth.Connect.Cuts as Cuts
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (Live; Shown; Match; Every; One; Reads)
open import simultaneous.Listing using (Listed)
open import simultaneous.CarryBase using (unp-pin; follows; Targeted; PMap; _∪ᴹ_; _⊆ᴹ_; Emb; CarryAt; Narrow; PinList; IntoAt; Near; Home; Whole; From;
  Ahead; ahead-under; ahead-over; few-sub; sub-listed; instant-⊕; apart)
open import denotation.Laws.Count using (⊑?)
open import simultaneous.Carry using (annValues; PastOver; Anchor; anchor-grow)
open import simultaneous.ReadRows using (up; up-⊕)
open import simultaneous.ConnLists using (module ConnLists; listed-proper; listed-step; live-or-ended; nin; trunc-few)
open import denotation.Events using (Timeline; fresh)
open import simultaneous.SObs using (lone; module Elaborate)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE)

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

  Iβ : InvAt (HP ∪ʰ Proper CP.σ) (p ⊕ [ ix 0 ]) CP.β
  Iβ = LC.Iβ {s = sP} {F = FP} IsP IFP p okP

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
              (nest : ∀ {k l e₀ h L a σ} → CarryAt.PB c_b k l → CP.β k e₀ → (Unpinned e₀ → Live CP.β k) → Σ (Ev A) (Proper CP.σ h) → CarryAt.Img c_a h L → k ≡ h ⊕ (a ∷ σ)
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

    private
      -- A carrier of the end shows the end.
      ended : ∀ {e₀ : Ev B} → Match Every (One valuesOf) (Reads valuesOf) e₀ (end {IE B}) → e₀ ≡ end
      ended {out _} (c , _) with c tt
      ... | _ , () , _
      ended {end}   _       = refl
      ended {skip}  (_ , n) = ⊥-elim (n (λ ()) tt)
      ended {pin _} (_ , n) = ⊥-elim (n (λ ()) tt)

      βfew : ∀ {w} → Few CE.ConnT w → Few CE.β w
      βfew (ks , h) = ks , λ b kw → h (CE.body b) kw

    -- An echo is carried live: the first end of the elaborated body
    -- before the echo's carrier would carry a plain body end, which the
    -- order embedding puts before the echo, where the connect is alive.
    echo-live : ∀ {k l} → EchoImg k l → Live t k → Live u l
    echo-live {k} {l} (k₀ , l₀ , (_ , x , _) , _ , _ , i , F , refl , refl) lv {c} uc cl =
      few-ind P step (reach-few {q = c} {e = end} (λ {k₁} {e₁} → full {X = IE B} {q = c} {e = end} tt {k₁} {e₁}) (proj₂ uc)) (proj₁ uc) cl
      where
        E : M′ (k₀ ⊕ [ ix 0 ]) (l₀ ⊕ [ ix 0 ])
        E = inj₂ (k₀ , l₀ , (_ , x) , i , refl , refl)

        P : Pos → Set
        P w = CE.ConnT w end → w ≺ l → ⊥

        past : ∀ {w k′} → w ≺ l → B′.Img k′ w → CP.β k′ end → ⊥
        past {w} {k′} wl i′ b′ with ≼-or-≻ k k′
        ... | inj₂ k′k = lv (CP.body b′ , few-reach {e = end} (few-sub {a = CP.ConnT} {w = k} {v = k′} F k′k)) k′k
        ... | inj₁ le with ≼-split {k} {k′} le
        ...   | inj₂ refl = SP.img-body x b′ (⊑-refl _)
        ...   | inj₁ lt   = ≺-irrefl {l} (≺-trans {l} {w} {l} (proj₁ (ahead-over ah (proj₂ (proj₂ (B′.ext i′))))) wl)
          where
            my′ = proj₁ (proj₂ (B′.ext i′))
            ah : Ahead l (proj₁ (B′.ext i′))
            ah = Emb.mono emb′ E (inj₁ my′) lt , λ ly → SP.img-body x b′ (Emb.reflect emb′ E (inj₁ my′) ly)

        fin : ∀ {w k′ e₀} → w ≺ l → B′.Img k′ w → CP.β k′ e₀ → Match Every (One valuesOf) (Reads valuesOf) e₀ (end {IE B}) → ⊥
        fin wl i′ b′ m with ended m
        ... | refl = past wl i′ b′

        step : ∀ {w} → Few CE.ConnT w → (∀ {v e} → CE.ConnT v e → v ≺ w → P v) → P w
        step {w} Fw ih (CE.body b) wl =
          let (_ , i′ , _ , b′ , m) = B′.shown b tt lβ (βfew Fw) in fin wl i′ b′ m
          where
            lβ : Live CE.β w
            lβ {c₂} b₂ c₂w = ih (CE.body b₂) c₂w (CE.body b₂) (≺-trans {c₂} {w} {l} c₂w wl)

    live′ : ∀ {k l} → ConnImg k l → Live t k → Live u l
    live′ (inj₁ (i , F)) lv = live-u (B′.live i (body-live F lv))
    live′ (inj₂ ei)      lv = echo-live ei lv

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

    private
      ahead-stable : ∀ {y l} → ¬ ¬ Ahead y l → Ahead y l
      ahead-stable {y} {l} n = decidable-stable (T? (y <ᵖ l)) (λ m → n (λ a → m (proj₁ a))) , λ yl → n (λ a → proj₂ a yl)

      pin-or : ∀ {X} (e : Ev X) → Unpinned e ⊎ Σ Pos λ q → e ≡ pin q
      pin-or (out _) = inj₁ tt
      pin-or skip    = inj₁ tt
      pin-or end     = inj₁ tt
      pin-or (pin q) = inj₂ (q , refl)

      -- Before a first child and not above it: before its parent, and
      -- not above that.
      below-first : ∀ {x y} → x ≺ (y ⊕ [ ix 0 ]) → ¬ (x ⊑ (y ⊕ [ ix 0 ])) → x ≺ y × ¬ (x ⊑ y)
      below-first {x} {y} xy nx = lt , λ xy′ → nx (⊑-trans xy′ ([ ix 0 ] , refl))
        where
          lt : x ≺ y
          lt with ≼-or-≻ x y
          ... | inj₂ yx = ⊥-elim (first-child y yx xy)
          ... | inj₁ le with ≼-split {x} {y} le
          ...   | inj₁ l′   = l′
          ...   | inj₂ refl = ⊥-elim (nx ([ ix 0 ] , refl))

    -- A body row's late carrier, the body alive there: past the body's
    -- points by the body's carry; past an echo apart from the row by the
    -- body's carry at the echo's source row, and past one above the row
    -- by the anchor the body nests on that source row.
    past-body : ∀ {k l e_b e x y} → B′.PB k l → CP.β k e_b → CE.β l e → (Unpinned e_b → Live CP.β k) → M′ x y → x ≺ k → ¬ (x ⊑ k) → Ahead y l
    past-body pb b ul lβ (inj₁ m) xk nx = B′.pb-past pb b lβ ul m xk nx
    past-body {k} {l} pb b ul lβ (inj₂ (k₀ , l₀ , (_ , x₀) , i , refl , refl)) xk nx =
      ahead-stable λ n → A′.img-row i λ (_ , x₁ , un₁) → n (go x₁ un₁)
      where
        my = proj₁ (proj₂ (A′.ext i))
        yl = proj₂ (proj₂ (A′.ext i))

        E : M′ (k₀ ⊕ [ ix 0 ]) (l₀ ⊕ [ ix 0 ])
        E = inj₂ (k₀ , l₀ , (_ , x₀) , i , refl , refl)

        kk : k₀ ≺ k
        kk = ≺-trans {k₀} {k₀ ⊕ [ ix 0 ]} {k} (≺-ext k₀ []) xk

        go : ∀ {e₁} → CP.σ k₀ e₁ → Unpinned e₁ → Ahead (l₀ ⊕ [ ix 0 ]) l
        go x₁ un₁ with ⊑? k₀ k
        ... | no nk = ahead-under (ahead-under (B′.pb-past pb b lβ ul (ms_b my) kk nk) yl) ([ ix 0 ] , refl)
        ... | yes ([] , eq) = ⊥-elim (≺-irrefl {k₀} (subst (k₀ ≺_) (trans eq (⊕-identityʳ k₀)) kk))
        ... | yes (a ∷ σ , eq) with nest pb b lβ (_ , x₁ , src-live x₁ un₁) i eq
        ...   | x′ , _ , m′ , yl′ , inj₂ kx′ =
          ahead-over (Emb.mono emb′ E (inj₁ m′) (≺-trans {k₀ ⊕ [ ix 0 ]} {k} {x′} xk kx′) , λ yy → nxx (Emb.reflect emb′ E (inj₁ m′) yy)) yl′
          where
            nxx : ¬ ((k₀ ⊕ [ ix 0 ]) ⊑ x′)
            nxx (σ′ , refl) = ≺-irrefl {k} (≺-trans {k} {_} {k} kx′ (subst (((k₀ ⊕ [ ix 0 ]) ⊕ σ′) ≺_) (⊕-identityʳ k) (apart xk nx σ′ [])))
        ...   | x′ , _ , m′ , yl′ , inj₁ (ax , xk′) =
          ahead-over (Emb.mono emb′ E (inj₁ m′) (≺-≼-≺ {k₀ ⊕ [ ix 0 ]} {k₀ ⊕ [ a ]} {x′} ka (⊑-≼ ax)) , λ yy → nx (⊑-trans (Emb.reflect emb′ E (inj₁ m′) yy) xk′)) yl′
          where
            ka : (k₀ ⊕ [ ix 0 ]) ≺ (k₀ ⊕ [ a ])
            ka with ≼-or-≻ (k₀ ⊕ [ ix 0 ]) (k₀ ⊕ [ a ])
            ... | inj₂ ak = ⊥-elim (first-child k₀ (≺-ext k₀ []) ak)
            ... | inj₁ le with ≼-split {k₀ ⊕ [ ix 0 ]} {k₀ ⊕ [ a ]} le
            ...   | inj₁ lt′ = lt′
            ...   | inj₂ eq′ = ⊥-elim (nx (subst (_⊑ k) (sym eq′) (⊑-trans ax xk′)))

    -- An echo's late carrier: past the body's points by the annotation's
    -- carry, which a body point before the echo and not above it is
    -- before the echo's source row and not above it; past another echo's
    -- by the annotation's carry at that echo's source row, which lies
    -- above no other source row: the source is flat.
    past-echo : ∀ {k₀ l₀ e₀ e′ x y} → CP.σ k₀ e₀ → (Unpinned e₀ → Live CP.σ k₀)
              → A′.PB k₀ l₀ → CE.σ l₀ e′ → M′ x y → x ≺ (k₀ ⊕ [ ix 0 ]) → ¬ (x ⊑ (k₀ ⊕ [ ix 0 ])) → Ahead y (l₀ ⊕ [ ix 0 ])
    past-echo x₀ lσ pb ul (inj₁ m) xk nx with below-first xk nx
    ... | lt , nk = ahead-over (past-a pb x₀ lσ ul m lt nk) ([ ix 0 ] , refl)
    past-echo {k₀} x₀ lσ pb ul (inj₂ (k₁ , l₁ , (_ , x₁) , i , refl , refl)) xk nx with ≼-or-≻ k₀ k₁
    ... | inj₁ le with ≼-split {k₀} {k₁} le
    ...   | inj₁ lt   = ⊥-elim (first-child k₀ (≺-trans {k₀} {k₁} {_} lt (≺-ext k₁ [])) xk)
    ...   | inj₂ refl = ⊥-elim (nx (⊑-refl _))
    past-echo {k₀} x₀ lσ pb ul (inj₂ (k₁ , l₁ , (_ , x₁) , i , refl , refl)) xk nx | inj₂ k₁k₀ with ⊑? k₁ k₀
    ... | no nk  = ahead-over (ahead-under (ahead-under (A′.pb-past pb x₀ lσ ul my k₁k₀ nk) yl) ([ ix 0 ] , refl)) ([ ix 0 ] , refl)
      where my = proj₁ (proj₂ (A′.ext i))
            yl = proj₂ (proj₂ (A′.ext i))
    ... | yes ([] , eq) = ⊥-elim (≺-irrefl {k₁} (subst (k₁ ≺_) (trans eq (⊕-identityʳ k₁)) k₁k₀))
    ... | yes (_ ∷ _ , refl) = ⊥-elim (InvAt.flat Iσ x₁ x₀)

    -- An unpinned row of the connect carried into its instant one label
    -- under a source row is that row's echo.
    past-src : ∀ {k l e₀ x y} → CP.ConnT k e₀ → Unpinned e₀ → Live t k → SrcPB k l → M′ x y → x ≺ k → ¬ (x ⊑ k) → Ahead y l
    past-src (CP.body b) _ _ (_ , l₀ , (_ , x₀) , _ , eq , _) = ⊥-elim (SP.img-body x₀ b ([] , trans eq (sym (⊕-identityʳ _))))
    past-src (CP.burst _ _) un = ⊥-elim (unp-pin {B} {p} un)
    past-src (CP.kept {p′ = q} _ _ _ _) un = ⊥-elim (unp-pin {B} {q} un)
    past-src (CP.echo {k₁} x₁ al un₁ ni) _ lv (k₀ , _ , _ , w , eq , refl , (_ , ul)) with ⊕-injˡ k₁ k₀ eq
    ... | refl with w
    ...   | inj₁ (_ , ins) = ⊥-elim (nin {r} {k₁} ni ins)
    ...   | inj₂ pb        = past-echo x₁ (λ _ {c} → src-live x₁ un₁ {c}) pb ul

    -- A pinned row's late carrier: a body pin's, the body's carry's; a
    -- source pin's in the burst, past every point before its echo by the
    -- embedding; a source pin's carried late, the annotation's carry's.
    conn-pb-pin : ∀ {k l q e x y} → PB′ k l → t k (pin q) → u l e → M′ x y → x ≺ k → ¬ (x ⊑ k) → Ahead y l
    conn-pb-pin (inj₁ (pb , _ , (_ , ul))) (CP.body b′ , _) _ m xk nx = past-body pb b′ ul (λ ()) m xk nx
    conn-pb-pin (inj₁ (_ , (_ , b) , _)) (CP.burst x _ , _)    _ _ _ _ = ⊥-elim (SP.img-body x b (⊑-refl _))
    conn-pb-pin (inj₁ (_ , (_ , b) , _)) (CP.kept x _ _ _ , _) _ _ _ _ = ⊥-elim (SP.img-body x b (⊑-refl _))
    conn-pb-pin (inj₂ (k₀ , l₀ , (_ , x₀) , inj₁ (i , _) , refl , refl , _)) _ _ m xk nx =
      Emb.mono emb′ m E xk , λ yl → nx (Emb.reflect emb′ m E yl)
      where
        E : M′ (k₀ ⊕ [ ix 0 ]) (l₀ ⊕ [ ix 0 ])
        E = inj₂ (k₀ , l₀ , (_ , x₀) , i , refl , refl)
    conn-pb-pin (inj₂ (k₀ , l₀ , (_ , x₀) , inj₂ pb , refl , refl , (_ , ul))) _ _ m xk nx =
      past-echo x₀ (λ un {c} → src-live x₀ un {c}) pb ul m xk nx

    conn-pb-past : ∀ {k l e₀ e x y} → PB′ k l → t k e₀ → (Unpinned e₀ → Live t k) → u l e → M′ x y → x ≺ k → ¬ (x ⊑ k) → Ahead y l
    conn-pb-past {e₀ = e₀} pb tk lv ul m xk nx with pin-or e₀
    ... | inj₂ (_ , refl) = conn-pb-pin pb tk ul m xk nx
    conn-pb-past (inj₁ (pb , (_ , b) , (_ , ul))) tk lv _ m xk nx | inj₁ un =
      past-body pb b ul (λ _ → body-live (reach-few (full un) (proj₂ tk)) (lv un)) m xk nx
    conn-pb-past (inj₂ sp) (c , _) lv _ m xk nx | inj₁ un = past-src c un (lv un) sp m xk nx

    -- An anchor of a source row's late carrier, one label down: past
    -- the row is past its first child, nothing the source's map pairs
    -- lying strictly under it.
    anchor-down : ∀ {k₀ l₀ e₀ h a} → (∀ {k e x y} → CP.σ k e → M_s x y → k ⊑ x → x ≡ k) → CP.σ k₀ e₀
                → Anchor M_s k₀ l₀ h a → Anchor M′ (k₀ ⊕ [ ix 0 ]) (l₀ ⊕ [ ix 0 ]) h a
    anchor-down bs x₀ (x , y , m , yl , inj₁ (ax , xk)) = x , y , inj₁ (ms_b m) , ⊑-trans yl ([ ix 0 ] , refl) , inj₁ (ax , ⊑-trans xk ([ ix 0 ] , refl))
    anchor-down {k₀} bs x₀ (x , y , m , yl , inj₂ kx) = x , y , inj₁ (ms_b m) , ⊑-trans yl ([ ix 0 ] , refl) , inj₂ lt
      where
        lt : (k₀ ⊕ [ ix 0 ]) ≺ x
        lt with ⊑? k₀ x
        ... | yes kx′ = ⊥-elim (≺-irrefl {x} (subst (_≺ x) (sym (bs x₀ m kx′)) kx))
        ... | no nk   = subst ((k₀ ⊕ [ ix 0 ]) ≺_) (⊕-identityʳ x) (apart kx nk [ ix 0 ] [])

    -- A LATE CARRIER UNDER A HOT ROW IS ANCHORED: a body row's by the
    -- body's anchor; a burst at an image at its echo; a source row's by
    -- the annotation's anchor one label down, past the source row's
    -- point when past it, nothing the source's map pairs lying strictly
    -- under a source row. No source row lies at a hot row: it is a world
    -- point.
    nest′ : ∀ {Row : Pos → Set} {Img₀ : Pos → Pos → Set} → (∀ {h} → Row h → HP h)
          → (∀ {k l e₀ h L a σ} → B′.PB k l → CP.β k e₀ → (Unpinned e₀ → Live CP.β k) → Row h → Img₀ h L → k ≡ h ⊕ (a ∷ σ) → Anchor M_b k l h a)
          → (∀ {k l e₀ h L a σ} → A′.PB k l → CP.σ k e₀ → (Unpinned e₀ → Live CP.σ k) → Row h → Img₀ h L → k ≡ h ⊕ (a ∷ σ) → Anchor M_s k l h a)
          → (∀ {k e x y} → CP.σ k e → M_s x y → k ⊑ x → x ≡ k)
          → ∀ {k l e₀ h L a σ} → PB′ k l → t k e₀ → (Unpinned e₀ → Live t k) → Row h → Img₀ h L → k ≡ h ⊕ (a ∷ σ) → Anchor M′ k l h a
    nest′ hr nb na bs (inj₁ (pb , _)) (CP.body b′ , rch) lv rw ci e =
      anchor-grow inj₁ (nb pb b′ (λ un → body-live (reach-few (full un) rch) (lv un)) rw ci e)
    nest′ hr nb na bs (inj₁ (_ , (_ , b) , _)) (CP.burst x _ , _)    _ _ _ _ = ⊥-elim (SP.img-body x b (⊑-refl _))
    nest′ hr nb na bs (inj₁ (_ , (_ , b) , _)) (CP.echo x _ _ _ , _) _ _ _ _ = ⊥-elim (SP.img-body x b (⊑-refl _))
    nest′ hr nb na bs (inj₁ (_ , (_ , b) , _)) (CP.kept x _ _ _ , _) _ _ _ _ = ⊥-elim (SP.img-body x b (⊑-refl _))
    nest′ hr nb na bs {h = h} {a = a} {σ = σ} (inj₂ (k₀ , l₀ , (_ , x₀) , inj₁ (i , _) , refl , refl , _)) tk lv rw ci e =
      k₀ ⊕ [ ix 0 ] , l₀ ⊕ [ ix 0 ] , inj₂ (k₀ , l₀ , (_ , x₀) , i , refl , refl) , ⊑-refl _
      , inj₁ ((σ , trans e (sym (⊕-assoc h [ a ] σ))) , ⊑-refl _)
    nest′ hr nb na bs {h = h} {a = a} {σ = σ} (inj₂ (k₀ , l₀ , (e₀ , x₀) , inj₂ pb , refl , refl , _)) tk lv rw ci e
      with ⊑-snoc k₀ (a ∷ σ , e)
    ... | inj₂ eq = ⊥-elim (ext≢ h σ (trans (sym e) (sym eq)))
    ... | inj₁ ([] , hk) =
      ⊥-elim (proj₂ okP (hr rw) (shrink (InvAt.world Iσ x₀)) (⊑-inside ([] , trans (trans (sym (⊕-identityʳ h)) (sym hk)) (sym (⊕-identityʳ k₀)))))
    ... | inj₁ (b ∷ τ , refl) with ∷-injectiveˡ (⊕-cancelˡ h (b ∷ τ ++ [ ix 0 ]) (a ∷ σ) (trans (sym (⊕-assoc h (b ∷ τ) [ ix 0 ])) e))
    ...   | refl = anchor-down bs x₀ (na pb x₀ (λ un {c} → src-live x₀ un {c}) rw ci refl)

    postulate
      conn-img¬¬ : ∀ {k e} → t k e → Unpinned e → Live t k → Few t k
                 → ¬ ¬ ((Σ Pos λ l → ConnImg k l × Σ (Ev (IE B)) λ e′ → u l e′ × Match Every (One valuesOf) (Reads valuesOf) e e′) ⊎ e ≡ skip)
      conn-shown : ∀ {l e} → u l e → Shown (One valuesOf) e → Live u l → Few u l
                 → Σ Pos λ k → ConnImg k l × Σ (Ev B) λ e₀ → t k e₀ × Match Every (One valuesOf) (Reads valuesOf) e₀ e
      conn-place : ∀ {m e} → u m e → Live u m → Listed u m
                 → instantOf m ≡ instantOf p′ ⊎ (Σ Pos λ k → Σ Pos λ l → ConnImg k l × instantOf l ≡ instantOf m × Near u m l)
                   ⊎ Σ Pos λ h → HE h × instantOf h ≡ instantOf m
      conn-whole : Whole t → (∀ {c} → t c end → ⊥) → (∀ {q} → LP q) → Whole u
      conn-cover : ∀ {v w} → Listed t v → LP v → Live t v → From ConnImg PB′ t u v w → Listed u w
      conn-pinned : ∀ {k q} → t k (pin q) → Listed t k → LP k
                  → (Σ Pos λ l → Σ Pos λ q′ → u l (pin q′) × PB′ k l × Targeted M′ q q′ × Listed u l)
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
        ahead (inj₂ pb) = past-a pb tk′ (λ _ {c} → lk′ {c}) ul′ my lt nk

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
                       (proj₁ (ahead-under (ahead-under (B′.pb-past pb b₂ (λ _ {c} → lk₂ {c}) ul₂ (ms_b my) kk nk) yl) ([ ix 0 ] , refl))))
          where my = proj₁ (proj₂ (A′.ext i))
                yl = proj₂ (proj₂ (A′.ext i))

        under : B′.PB k₂ l₂ → k ⊑ k₂ → ⊥
        under pb ([] , eq) = ≺-irrefl {k} (subst (k ≺_) (trans eq (⊕-identityʳ k)) kk)
        under pb (a ∷ σ , eq) with nest pb b₂ (λ _ {c} → lk₂ {c}) (_ , x , src-live x un) i eq
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

    -- A pin carried from its own connect's past: a body pin by the body's
    -- carry, a burst or kept pin by the annotated source's, its carrier
    -- with the elaborated pins of its connect before it.
    postulate
      conn-pinned↓ : ∀ {k q} → t k (pin q) → Listed t q → PinList t q k → LP q
                   → (Σ Pos λ l → Σ Pos λ q′ → u l (pin q′) × PB′ k l × Targeted M′ q q′ × PinList u q′ l)
                     × (instantOf k ≡ instantOf p ⊎ (Σ Pos λ k₀ → k₀ ≺ q × Home t k₀ × instantOf k₀ ≡ instantOf k)
                        ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)

    narrowed : Narrow carried
    narrowed = record { pinned↓ = conn-pinned↓ }
