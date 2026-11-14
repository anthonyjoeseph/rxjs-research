{-# OPTIONS --guardedness #-}

-- A READER KEEPS EVERY BINDER'S LATE CARRIERS: past its joins, and
-- anchored when they lie under a hot row.
module simultaneous.CarryJoins where


open import Data.Bool using (T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (lookup; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (decidable-stable)
open import Data.Bool.Properties using (T?)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Tree using (connected)
open import denotation.Position using (sub; last; _⊕_; _<ᵖ_; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (end; Den; hot; enter; Proper; DenEnv; shown; _≺_)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≺-trans; ≺-ext; ≺→≼; ≼-split)
open import denotation.Laws.Worlds using (Hots; Ok; InvAt; _⊑_; ⊑-refl; ⊑-snoc⁺; ⊑-trans; ⊕-identityʳ; conv)
open import denotation.Laws.Count using (⊑?)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.CarryBase using (PMap; _⊆ᴹ_; Emb; Fresh; CarryAt; Narrow; unpinned-narrow; apart; Ahead; ahead-over; ahead-under)
open import simultaneous.Carry using (at-foot; Within; Bare; Carry; carry; EnvRel; Bound; HotsListed; NotHot; BoundRow; Joins; Apart;
  EnvPast; PBNest; Nests; env-past; nest-or; BoundSrc; Rows; rows-at; clear-not)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; annotate)

open import simultaneous.CarryRead using (Reading; read-post; read-post-pb)
open import simultaneous.Rejoined using (split-at; same-hot)

open import simultaneous.CarryReader using (HotOf′; module Read)

------------------------------------------------------------------------
-- One reader's joins

module ReadPast {Γ Δ} {M₀ : PMap} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {envP : DenEnv Γ} {envE : DenEnv Δ}
                (hm : Emb M₀) (er : EnvRel M₀ ρ envP envE) (jn : Joins ρ envP envE er M₀) (ap : Apart envP)
                {X} (i : X ∈ Γ) {p p′} (m₀ : M₀ p p′) (okP : Ok (Hots envP) p) (okE : Ok (Hots envE) p′)
                (nh : NotHot (Rows er) p) (fr : Fresh (Hots envP) M₀ p) where
  open Read {M₀ = M₀} {ρ = ρ} {envP = envP} {envE = envE} hm er jn ap i m₀ okP okE nh fr

  -- EVERY BINDER'S LATE CARRIERS STAY PAST THE JOINS: a join before a
  -- late carrier's row and not over it is past and apart from it when its
  -- hot row is; when the row lies under its hot row, the row's anchor
  -- lies past the join, and the joins keep the embedding.
  ep₀ : EnvPast er M₀
  ep₀ = env-past er

  -- Being ahead is decided, so held classically.
  ahead-st : ∀ {y l} → ¬ ¬ Ahead y l → Ahead y l
  ahead-st {y} {l} nn = decidable-stable (T? (y <ᵖ l)) (λ n → nn λ a → n (proj₁ a)) , λ yl → nn λ a → proj₂ a yl

  reader-past : Nests er M₀ → EnvPast er M
  reader-past ns j pb tk lv ul (inj₁ m) xk nxk = ep₀ j pb tk lv ul m xk nxk
  reader-past ns j {k} pb tk lv ul (inj₂ (inj₂ (refl , refl))) xk nxk =
    ahead-under (ep₀ j pb tk lv ul m₀ (≺-trans {p} {p ⊕ [ last ]} {k} (≺-ext p []) xk)
                   (nh (rows-at er j tk))) (⊑-snoc⁺ p′)
  reader-past ns j {k} {l} pb tk lv ul (inj₂ (inj₁ (q , L , nbr , ci , pq , refl , refl))) xk nxk =
    ahead-st {L ⊕ [ sub p′ ]} {l} λ n → nbr λ br → n (go br)
    where
     go : BoundRow (er i) q → Ahead (L ⊕ [ sub p′ ]) l
     go br with C.ext ci
     ... | yq , myq , yqL with cmp3 q k
     ...   | inj₂ (inj₁ e) = ⊥-elim (≺-absurd {q ⊕ [ sub p ]} {q} (subst ((q ⊕ [ sub p ]) ≺_) (sym e) xk) (≺-ext q []))
     ...   | inj₂ (inj₂ kq) = ⊥-elim (≺-absurd {q ⊕ [ sub p ]} {k} xk (≺-trans {k} {q} {q ⊕ [ sub p ]} kq (≺-ext q [])))
     ...   | inj₁ qk with ⊑? q k
     ...     | no nqk = ahead-under (ep₀ j pb tk lv ul myq qk nqk) (⊑-trans yqL (⊑-snoc⁺ L))
     ...     | yes ([] , e) = ⊥-elim (≺-irrefl {q} (subst (q ≺_) (trans e (⊕-identityʳ q)) qk))
     ...     | yes (a ∷ σ , e) with ns j i pb tk lv br ci e
     ...       | x₀ , y₀ , m , y₀l , w =
      ahead-over (Emb.mono reader-emb jq (inj₁ m) (proj₁ zx) , λ yy → proj₂ zx (Emb.reflect reader-emb jq (inj₁ m) yy)) y₀l
      where
       jq : M (q ⊕ [ sub p ]) (L ⊕ [ sub p′ ])
       jq = inj₂ (inj₁ (q , L , (λ n → n br) , ci , pq , refl , refl))

       zx-of : ((((q ⊕ [ a ]) ⊑ x₀) × x₀ ⊑ k) ⊎ k ≺ x₀) → (q ⊕ [ sub p ]) ≺ x₀ × ¬ ((q ⊕ [ sub p ]) ⊑ x₀)
       zx-of (inj₂ kx) = ≺-trans {q ⊕ [ sub p ]} {k} {x₀} xk kx , λ zx₀ → nxk (conv (⊑-refl _) (≺→≼ {q ⊕ [ sub p ]} {k} xk) kx zx₀)
       zx-of (inj₁ (hx , x₀k)) with cmp3 (q ⊕ [ sub p ]) x₀
       ...   | inj₁ zx₀ = zx₀ , λ zx₀′ → nxk (⊑-trans zx₀′ x₀k)
       ...   | inj₂ (inj₁ refl) = ⊥-elim (nxk x₀k)
       ...   | inj₂ (inj₂ x₀z) with ⊑? x₀ (q ⊕ [ sub p ])
       ...     | yes x₀z′ = ⊥-elim (nxk (subst (λ b → (q ⊕ [ b ]) ⊑ k) (sib-eq q (⊑-trans hx x₀z′)) (⊑-trans hx x₀k)))
       ...     | no nx₀z = ⊥-elim (≺-absurd {q ⊕ [ sub p ]} {k} xk (past {x₀} {q ⊕ [ sub p ]} {k} x₀z nx₀z x₀k))

       zx : (q ⊕ [ sub p ]) ≺ x₀ × ¬ ((q ⊕ [ sub p ]) ⊑ x₀)
       zx = zx-of w

  private
    -- Past a row the hot carries into its instant, and apart from it: no
    -- point of the map so far lies under such a row.
    pb-past-row : ∀ {q l₀ e x y} → C.PB q l₀ → Proper T₀ q e → M₀ x y → q ≺ x → (q ⊕ [ sub p ]) ≺ x
    pb-past-row {q} {x = x} pb tq m qx with ⊑? q x
    ... | no nq = subst ((q ⊕ [ sub p ]) ≺_) (⊕-identityʳ x) (apart {q} {x} qx nq [ sub p ] [])
    ... | yes ([] , e) = ⊥-elim (≺-irrefl {q} (subst (q ≺_) (trans e (⊕-identityʳ q)) qx))
    ... | yes (_ ∷ _ , e) with jn i m (_ , tq) e
    ...   | _ , _ , _ , _ , _ , ci , _ = ⊥-elim (C.pb-img pb ci)

  -- THE JOINS' LATE CARRIERS ARE ANCHORED: one on a hot row's carrier,
  -- where that row's is; one trailing the annotated end, at the end's join.
  reader-nest : Nests er M₀ → PBNest er M reader-rejoined
  reader-nest ns i₂ {h = h} {L = L₂} (q , l₀ , pbq , (_ , tq) , _ , pq , refl , inj₁ refl) _ _ brh cih e with split-at h q e
  ... | inj₁ (refl , _) = ⊥-elim (same-hot envP ap i i₂ (Bound.isP (er i)) (Bound.isP (er i₂)) (λ n → n (_ , tq)) (λ n → n brh)
                                   (λ j → CarryAt.Img (Bound.carried (er j)) q L₂ → ⊥) (C.pb-img pbq) cih)
  ... | inj₂ (_ , qe) with ns i i₂ pbq (proj₁ tq) (λ _ {c} → proj₂ tq {c}) brh cih qe
  ...   | x₀ , y₀ , m , y₀l , inj₁ (hx , x₀q) = x₀ , y₀ , inj₁ m , ⊑-trans y₀l (⊑-snoc⁺ l₀) , inj₁ (hx , ⊑-trans x₀q (⊑-snoc⁺ q))
  ...   | x₀ , y₀ , m , y₀l , inj₂ qx₀ = x₀ , y₀ , inj₁ m , ⊑-trans y₀l (⊑-snoc⁺ l₀) , inj₂ (pb-past-row pbq tq m qx₀)
  reader-nest ns i₂ (q , l₀ , pbq , (_ , tq) , _ , pq , refl , inj₂ (c′ , tc′ , _ , refl)) _ _ _ _ _
    with C.shown-end tc′ (λ {c₉} → endE {_} {c₉} tc′) (fewE tc′ tt)
  ... | k₁ , ci₁ , ntk₁ with ≼-split {q} {k₁} (λ kq → ntk₁ λ tk₁ → proj₂ tq tk₁ kq)
  ...   | inj₂ e = ⊥-elim (C.pb-img pbq (subst (λ z → C.Img z c′) (sym e) ci₁))
  ...   | inj₁ qk = k₁ ⊕ [ sub p ] , c′ ⊕ [ sub p′ ] , rk , ⊑-refl _ , inj₂ (apart {q} {k₁} qk (λ le → nbr₁ λ br₁ → flat-lead (_ , tq) br₁ qk le) [ sub p ] [ sub p ])
    where
      nbr₁ : ¬ ¬ BoundRow (er i) k₁
      nbr₁ n = ntk₁ λ tk₁ → n (end , tk₁ , λ {c} tc → endP tk₁ tc)

      rk : M (k₁ ⊕ [ sub p ]) (c′ ⊕ [ sub p′ ])
      rk = inj₂ (inj₁ (k₁ , c′ , nbr₁ , ci₁ , ≺-trans {p} {q} {k₁} pq qk , refl , refl))

------------------------------------------------------------------------
-- The former

private
  read-at : ∀ {Γ Δ} {M₀ : PMap} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {envP : DenEnv Γ} {envE : DenEnv Δ}
            (hm : Emb M₀) (er : EnvRel M₀ ρ envP envE) (jn : Joins ρ envP envE er M₀) (ap : Apart envP)
            {X} (i : X ∈ Γ) {p p′} (m₀ : M₀ p p′) (okP : Ok (Hots envP) p) (okE : Ok (Hots envE) p′)
            (nh : NotHot (Rows er) p) (fr : Fresh (Hots envP) M₀ p) {dP : Den X} {dE : Den (AIE X)}
          → dP ≡ hot (Proper (BoundSrc (er i))) → dE ≡ hot (Proper (HotOf′ (er i))) → InvAt (Hots envE) p′ (enter dE p′)
          → Nests er M₀
          → Σ PMap λ M → M₀ ⊆ᴹ M × Emb M × Within (Hots envP) M₀ M p × Bare M (enter dP p) × Joins ρ envP envE er M × EnvPast er M
            × Σ (CarryAt valuesOf M (Hots envP) (Hots envE) (HotsListed envP) (enter dP p) (enter (Reading dE) p′) p p′) (λ c → PBNest er M c × Narrow c)
  read-at {M₀ = M₀} {ρ} {envP} {envE} hm er jn ap i m₀ okP okE nh fr refl refl Iu ns =
    R.M , inj₁ , R.reader-emb , R.reader-within , R.reader-bare , R.reader-joins , R′.reader-past ns
    , read-post {T = Proper (HotOf′ (er i))} Iu R.reader-rejoined (λ { (shown _ () _ , _) })
    , nest-or {er = er} {c = R.reader-rejoined} {c′ = read-post {T = Proper (HotOf′ (er i))} Iu R.reader-rejoined (λ { (shown _ () _ , _) })} (λ m → m)
        (λ pb tk lv → let (l , pb₀ , ll) = read-post-pb {T = Proper (HotOf′ (er i))} Iu R.reader-rejoined (λ { (shown _ () _ , _) }) pb in inj₁ (l , pb₀ , ll , _ , tk , lv))
        (R′.reader-nest ns)
    , unpinned-narrow (λ { (shown _ () _ , _) }) (read-post {T = Proper (HotOf′ (er i))} Iu R.reader-rejoined (λ { (shown _ () _ , _) }))
    where
      module R  = Read {M₀ = M₀} {ρ = ρ} {envP = envP} {envE = envE} hm er jn ap i m₀ okP okE nh fr
      module R′ = ReadPast {M₀ = M₀} {ρ = ρ} {envP = envP} {envE = envE} hm er jn ap i m₀ okP okE nh fr

-- A READER of a bound hot carries it.
carry-connected : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) → Carry m ρ (connected i)
carry-connected n ρ i = carry λ envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr →
  read-at {ρ = ρ} {envP = envP} {envE = envE} hm er jn ap i (at-foot {M₀} m₀) okP okE (clear-not nh) fr {dP = lookup envP i} {dE = lookup envE (ρ (∈-map⁺ AIE i))}
    (Bound.isP (er i)) (Bound.isE (er i)) (proj₁ (gE (ρ (∈-map⁺ AIE i))) p′ okE) ns
