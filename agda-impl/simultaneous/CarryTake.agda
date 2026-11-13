{-# OPTIONS --guardedness #-}

-- A TAKEWHILE CARRIES what its source did.  Before the first failing
-- value the two runs are their sources' rows, carried as the source
-- carried them; the failing value itself is carried by the elaborated
-- run's failing value, shown alike, so the cuts one label under each —
-- the value kept (`ix 0`) and the end (`last`) — are paired by growing
-- the map one label under the pair.  A mark passes, so only values fail.
--
-- A row of the elaborated run is placed from its source's placing: near
-- a carrier at or before it, or near one listed up to, where the listing
-- decides the first failing value between them, whose end is then the
-- nearer carrier.  A run with no end has no failure, since the first one
-- ends it, so its rows are its source's.
module simultaneous.CarryTake where

open import Data.Bool using (Bool; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Tree using (takeWhile)
open import denotation.Position using (Pos; ix; last; _⊕_; root; _≟ᵖ_; inside)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Den; enter; Reach; Few; _≺_; _≼_; module Op;
  approx)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≺-absurd; ≺→≼; ≼-refl; ≼-or-≻; ≼-split; ≺-ext; entered-reach)
open import denotation.Laws.Worlds using (InvAt; W⁼; inW; step; _⊑_; ⊑-refl; ⊑-trans; ⊑-≼; ⊑-snoc; ⊑-snoc⁺; ⊕-identityʳ; ⊕-assoc;
  ⊕-injʳ; inside-⊑; ⊑-inside; W; conv)
open import denotation.Laws using (inv-approx)
open import adequacy.SubOne using (at-or-before)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.InstEmit using (valuesOf; instEmit; value; mark)
open import simultaneous.Attribution using (Live; Shown; Match; Every; One; Reads)
open import simultaneous.Listing using (Listed)
open import simultaneous.Readings using (instantOf; parent; parent-snoc)
open import simultaneous.CarryBase using (From; Targeted; Narrow; PinList; unp-pin; ahead-under; pin-bound; PMap; _⊆ᴹ_; _∪ᴹ_; Emb;
  CarryAt; Near; Whole; Home; module Mono; emb-at; emb-pairs; instant-⊕; sub-listed; few-sub;
  match-val; carried-val; IntoAt; Ahead; ahead-over)
open import simultaneous.Carry using (Carry; carry; Bare; Within; listed↓; Grown; joins-grow; grown-past; nest-or)
open import simultaneous.CarryLeaves using (module OneAt)
open import simultaneous.TakeSide using (Keeps; Lab; module Side; between; cut-match; cut-unp; cutEv; lab-plain)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; passes)

------------------------------------------------------------------------
-- The carrier

private
  -- A row not shown is kept by the elaborated takeWhile.
  hid : ∀ {A : Set} {kp : A → Bool} (e′ : Ev (IE A)) → ¬ Shown (One valuesOf) e′ → Keeps (passes kp) e′
  hid (out (instEmit (value b) _)) h = ⊥-elim (h (b , refl))
  hid (out (instEmit (mark _) _))  _ = tt
  hid skip    _ = tt
  hid end     _ = tt
  hid (pin _) _ = tt

  -- A row and its carrier are kept alike.
  keeps→ : ∀ {A : Set} {kp : A → Bool} {e e′} → Match Every (One valuesOf) (Reads valuesOf) e e′ → Keeps kp e → Keeps (passes kp) e′
  keeps→ {e = out a} mt p with carried-val mt
  ... | _ , refl = p
  keeps→ {e = end} (cr , _) _ with cr tt
  ... | refl = tt
  keeps→ {kp = kp} {e = skip}  {e′} (_ , ns) _ = hid {kp = kp} e′ (ns λ ())
  keeps→ {kp = kp} {e = pin _} {e′} (_ , ns) _ = hid {kp = kp} e′ (ns λ ())

  keeps← : ∀ {A : Set} {kp : A → Bool} {e e′} → Match Every (One valuesOf) (Reads valuesOf) e e′ → Keeps (passes kp) e′ → Keeps kp e
  keeps← {e = out a} mt p with carried-val mt
  ... | _ , refl = p
  keeps← {e = end}   _ _ = tt
  keeps← {e = skip}  _ _ = tt
  keeps← {e = pin _} _ _ = tt

  within-∘ : ∀ {H : Pos → Set} {M₀ M M′ : PMap} {p} → Within H M₀ M p → (∀ {x y} → M′ x y → M x y ⊎ W⁼ H p x) → Within H M₀ M′ p
  within-∘ wi wi′ m′ with wi′ m′
  ... | inj₁ m = wi m
  ... | inj₂ w = inj₂ w

module Core {A : Set} (incl : Bool) (keep : A → Bool) {M : PMap} {HP HE LP H₁ H₂ : Pos → Set}
  {t : EmissionSet A} {u : EmissionSet (IE A)} {s s′ : Pos} (hm : Emb M)
  (rcT : ∀ {q e} → t q e → Reach t q e) (rcU : ∀ {q e} → u q e → Reach u q e)
  (It : InvAt H₁ s t) (Iu : InvAt H₂ s′ u) (br : Bare M t) (lp↓ : ∀ {x y} → x ≼ y → LP y → LP x)
  (c : CarryAt valuesOf M HP HE LP t u s s′) (nar : Narrow c) where
  private
    module C = CarryAt c
  module P = Side incl keep t (λ {y} {e} → rcT {y} {e}) It
  module Q = Side incl (passes keep) u (λ {y} {e} → rcU {y} {e}) Iu

  private
    flatP : ∀ {y e l ys e′} → t y e → t (y ⊕ (l ∷ ys)) e′ → ⊥
    flatP = InvAt.flat It

    img-mono : ∀ {k k′ l l′} → C.Img k l → C.Img k′ l′ → k ≺ k′ → l ≺ l′
    img-mono = Mono.img-mono hm (λ {y} {e} {l} {ys} {e′} → InvAt.flat It {y} {e} {l} {ys} {e′}) c

    -- A carrier with no failure before it carries a row with none.
    e1 : ∀ {k l} → C.Img k l → ¬ P.Failed k → ¬ Q.Failed l
    e1 i nf (q , instEmit (mark _) _ , _ , () , _)
    e1 {k} {l} i nf (q , instEmit (value b) n , uq , nb , ql) with C.shown uq (b , refl) (Q.live-out uq) (Q.few-out uq)
    ... | k′ , i′ , e₀ , tk′ , mt with match-val mt
    ...   | refl with ≼-or-≻ k k′
    ...     | inj₂ k′k = nf (k′ , b , tk′ , nb , k′k)
    ...     | inj₁ kk′ with ≼-split {k} {k′} kk′
    ...       | inj₁ k≺k′ = ≺-absurd {l} {q} (img-mono i i′ k≺k′) ql
    ...       | inj₂ refl = ≺-irrefl {q} (subst (q ≺_) (C.img-fun i i′) ql)

    -- A row with no failure before its carrier has none before it.
    e2 : ∀ {k l} → C.Img k l → ¬ Q.Failed l → ¬ P.Failed k
    e2 {k} {l} i nf (q , b , tq , nb , qk) = C.img¬¬ tq tt (P.live-out tq) (P.few-out tq) λ { (inj₁ (l′ , i′ , e′ , ul′ , mt)) → fl i′ ul′ mt ; (inj₂ ()) }
      where
        fl : ∀ {l′ e′} → C.Img q l′ → u l′ e′ → Match Every (One valuesOf) (Reads valuesOf) (out b) e′ → ⊥
        fl i′ ul′ mt with carried-val mt
        ... | _ , refl = nf (_ , _ , ul′ , nb , img-mono i′ i qk)

    -- A row whose carrier does not fail does not fail.
    unfails← : ∀ {k l} → C.Img k l → ¬ Q.Fails l → ¬ P.Fails k
    unfails← {k} {l} i nq (b , tk , nb) = C.img¬¬ tk tt (P.live-out tk) (P.few-out tk) λ { (inj₁ (l′ , i′ , e′ , ul′ , mt)) → fl i′ ul′ mt ; (inj₂ ()) }
      where
        fl : ∀ {l′ e′} → C.Img k l′ → u l′ e′ → Match Every (One valuesOf) (Reads valuesOf) (out b) e′ → ⊥
        fl i′ ul′ mt with carried-val mt
        ... | _ , refl = nq (_ , subst (λ z → u z _) (C.img-fun i′ i) ul′ , nb)

    -- A carrier of a row that does not fail does not fail.
    unfails→ : ∀ {k l} → C.Img k l → ¬ P.Fails k → ¬ Q.Fails l
    unfails→ i nfs (instEmit (mark _) _ , _ , ())
    unfails→ {k} {l} i nfs (instEmit (value b) n , ul , nb) with C.shown ul (b , refl) (Q.live-out ul) (Q.few-out ul)
    ... | k′ , i′ , e₀ , tk′ , mt with match-val mt
    ...   | refl with ≼-or-≻ k k′
    ...     | inj₂ k′k = ≺-irrefl {l} (img-mono i′ i k′k)
    ...     | inj₁ kk′ with ≼-split {k} {k′} kk′
    ...       | inj₁ lt   = ≺-irrefl {l} (img-mono i i′ lt)
    ...       | inj₂ refl = nfs (b , tk′ , nb)

  -- THE CUT UNDER THE FIRST FAILING VALUE, on the same label under its
  -- carrier, the failing value of the elaborated run.
  data Cut (k l : Pos) : Set where
    cut : ∀ {k₀ l₀ a b n} → t k₀ (out b) → T (not (keep b)) → ¬ P.Failed k₀ → C.Img k₀ l₀
        → u l₀ (out (instEmit (value b) n)) → Lab incl a → k ≡ k₀ ⊕ [ a ] → l ≡ l₀ ⊕ [ a ] → Cut k l

  Img′ : Pos → Pos → Set
  Img′ k l = (C.Img k l × ¬ P.Failed k × ¬ P.Fails k) ⊎ Cut k l

  M′ : PMap
  M′ = M ∪ᴹ Cut

  -- WHAT THE TAKEWHILE PUTS INTO ITS INSTANT: its source's, on a row of
  -- its source; and a row before the first failing value, on the end cut
  -- under that value's carrier.
  -- A row before the failure, or a pin, which stays past it.
  Kept : Pos → Set
  Kept k = ¬ P.Failed k ⊎ Σ Pos λ r → t k (pin r)

  PB′ : Pos → Pos → Set
  PB′ k m = (Σ (Ev (IE A)) (u m) × Σ (Ev A) (t k) × Kept k × C.PB k m)
          ⊎ Σ Pos λ f → Σ Pos λ k₀ → Q.First f × C.Img k₀ f × m ≡ f ⊕ [ last ] × P.First k₀ × k ≺ k₀ × Σ (Ev A) (t k) × Σ Pos (C.PB k)

  private
    live-of : ∀ {k e₀} → Kept k → t k e₀ → (Unpinned e₀ → Live P.T′ k) → Unpinned e₀ → Live t k
    live-of (inj₁ nfk)      _   lv un = P.live← nfk (lv un)
    live-of (inj₂ (r , tk)) tk′ _  un = ⊥-elim (unp-pin {A} {r} (subst Unpinned (InvAt.func It tk′ tk) un))

    firstQ : ∀ {k₀ l₀ b n} → t k₀ (out b) → T (not (keep b)) → ¬ P.Failed k₀ → C.Img k₀ l₀ → u l₀ (out (instEmit (value b) n)) → Q.First l₀
    firstQ tk nk nf i ul = (_ , ul , nk) , e1 i nf

    -- The cut under a first failing value of `u`, and what it carries.
    cut-shown : ∀ {q y a} → u q (out y) → T (not (passes keep y)) → ¬ Q.Failed q → Lab incl a
              → Σ Pos λ k → Img′ k (q ⊕ [ a ]) × Σ (Ev A) λ e₀ → P.T′ k e₀ × Match Every (One valuesOf) (Reads valuesOf) e₀ (cutEv y a)
    cut-shown {y = instEmit (mark _) _} _ () _ _
    cut-shown {q} {instEmit (value b) n} {a} uq nb nfq lb with C.shown uq (b , refl) (Q.live-out uq) (Q.few-out uq)
    ... | k₀ , i , e₀ , tk , mt with match-val mt
    ...   | refl = k₀ ⊕ [ a ] , inj₂ (cut tk nb (e2 i nfq) i uq lb refl refl) , cutEv b a , P.cut-row tk nb (e2 i nfq) lb , cut-match lb

    ----------------------------------------------------------------------
    -- The map grown: two cuts pair under one failing value

    Kc : ∀ {x y} → Cut x y → PMap
    Kc (cut {k₀} {l₀} _ _ _ _ _ _ _ _) = M ∪ᴹ OneAt.N k₀ l₀

    embK : ∀ {x y} (c′ : Cut x y) → Emb (Kc c′)
    embK (cut {k₀} {l₀} tk _ _ i _ _ _ _) with C.ext i
    ... | y₀ , m₀ , pp = emb-at hm (λ m kx → br tk m kx) m₀ pp (OneAt.embN k₀ l₀) λ { (a , _ , refl , refl) → a , [] , a , [] , refl , refl }

    selfK : ∀ {x y} (c′ : Cut x y) → Kc c′ x y
    selfK (cut _ _ _ _ _ lb refl refl) = inj₂ (_ , lab-plain lb , refl , refl)

    otherK : ∀ {x y x′ y′} (c′ : Cut x y) → M′ x′ y′ → Kc c′ x′ y′
    otherK (cut _ _ _ _ _ _ _ _) (inj₁ m) = inj₁ m
    otherK (cut tk nk nf i _ _ _ _) (inj₂ (cut tk′ nk′ nf′ i′ _ lb′ refl refl)) with P.first ((_ , tk , nk) , nf) ((_ , tk′ , nk′) , nf′)
    ... | refl with C.img-fun i i′
    ...   | refl = inj₂ (_ , lab-plain lb′ , refl , refl)

  emb′ : Emb M′
  emb′ = emb-pairs pair
    where
      pair : ∀ {x y x′ y′} → M′ x y → M′ x′ y′ → Σ PMap λ K → Emb K × K x y × K x′ y′
      pair (inj₁ m) (inj₁ m′) = M , hm , m , m′
      pair (inj₂ c′) n        = Kc c′ , embK c′ , selfK c′ , otherK c′ n
      pair (inj₁ m) (inj₂ c′) = Kc c′ , embK c′ , otherK c′ (inj₁ m) , selfK c′

  -- A cut lies one label under a point of the map, holding no hot row.
  grown′ : ∀ {R} → (∀ {q w} → R q → W H₁ s w → T (inside w q) → ⊥) → ∀ {x y} → M′ x y → M x y ⊎ Grown M R x y
  grown′ _  (inj₁ m) = inj₁ m
  grown′ dj (inj₂ (cut tk _ _ i _ _ refl refl)) with C.ext i
  ... | y₀ , m₀ , pp = inj₂ (_ , y₀ , _ , m₀ , ⊑-trans pp (⊑-snoc⁺ _) , refl , λ hq kq → dj hq (InvAt.world It tk) (⊑-inside kq))

  within′ : ∀ {x y} → M′ x y → M x y ⊎ W⁼ H₁ s x
  within′ (inj₁ m) = inj₁ m
  within′ (inj₂ (cut tk _ _ _ _ lb refl _)) = inj₂ (inW (step (inW (InvAt.world It tk)) (lab-plain lb)))

  private
    bare-M : ∀ {k e x y} → P.TakeT k e → M x y → k ⊑ x → x ≡ k
    bare-M r m kx with P.view r
    ... | inj₁ (tk , _) = br tk m kx
    ... | inj₂ (q , _ , tq , _ , _ , a , _ , refl , _) with br tq m (⊑-trans (⊑-snoc⁺ q) kx)
    ...   | refl = ⊥-elim (⊑-≼ kx (≺-ext q []))

    bare-cut : ∀ {k e x y} → P.TakeT k e → Cut x y → k ⊑ x → x ≡ k
    bare-cut {k} r (cut {k₀} tk₀ nk nf _ _ _ refl _) kx with ⊑-snoc k₀ kx
    ... | inj₂ e = sym e
    ... | inj₁ kk with P.view r
    ...   | inj₂ (q , _ , tq , _ , _ , a′ , _ , refl , _) with kk
    ...     | zs , refl = ⊥-elim (flatP tq (subst (λ z → t z _) (⊕-assoc q [ a′ ] zs) tk₀))
    bare-cut {k} r (cut {k₀} tk₀ nk nf _ _ _ refl _) kx | inj₁ kk | inj₁ (tk , _) with kk
    ... | [] , refl    = ⊥-elim (P.none-at ((_ , tk₀ , nk) , nf) (subst (λ z → P.TakeT z _) (sym (⊕-identityʳ k)) r))
    ... | _ ∷ _ , refl = ⊥-elim (flatP tk tk₀)

  bare′ : Bare M′ P.T′
  bare′ r (inj₁ m)  kx = bare-M (proj₁ r) m kx
  bare′ r (inj₂ c′) kx = bare-cut (proj₁ r) c′ kx

  private
    ----------------------------------------------------------------------
    -- The fields

    ext′ : ∀ {k l} → Img′ k l → Σ Pos λ y → M′ k y × y ⊑ l
    ext′ (inj₁ (i , _)) = let (y , m , yl) = C.ext i in y , inj₁ m , yl
    ext′ (inj₂ c′)      = _ , inj₂ c′ , ⊑-refl _

    img-row′ : ∀ {k l} → Img′ k l → ¬ ¬ Σ (Ev A) λ e → P.T′ k e × Unpinned e
    img-row′ (inj₁ (i , nf , nfs)) n = C.img-row i λ { (e , tk , un) → n (e , P.up tk nf (P.pass-of nfs tk) , un) }
    img-row′ (inj₂ (cut tk nk nf _ _ lb refl _)) n = n (_ , P.cut-row tk nk nf lb , cut-unp lb)

    img-fun′ : ∀ {k l l′} → Img′ k l → Img′ k l′ → l ≡ l′
    img-fun′ (inj₁ (i , _)) (inj₁ (i′ , _)) = C.img-fun i i′
    img-fun′ (inj₁ (i , _)) (inj₂ (cut tk _ _ _ _ _ refl _)) = ⊥-elim (C.img-row i λ { (_ , tk′ , _) → flatP tk tk′ })
    img-fun′ (inj₂ (cut tk _ _ _ _ _ refl _)) (inj₁ (i , _)) = ⊥-elim (C.img-row i λ { (_ , tk′ , _) → flatP tk tk′ })
    img-fun′ (inj₂ (cut {k₀} tk nk nf i _ _ refl refl)) (inj₂ (cut tk′ nk′ nf′ i′ _ _ ek refl))
      with P.first ((_ , tk , nk) , nf) ((_ , tk′ , nk′) , nf′)
    ... | refl with ⊕-injʳ k₀ k₀ ek | C.img-fun i i′
    ...   | refl | refl = refl

    few′ : ∀ {k l} → Img′ k l → Few P.T′ k
    few′ (inj₁ (i , _))                   = P.few→ (C.few i)
    few′ (inj₂ (cut tk _ _ i _ _ refl _)) = P.few→ (P.few-snoc tk (C.few i))

    live′ : ∀ {k l} → Img′ k l → Live P.T′ k → Live Q.T′ l
    live′ (inj₁ (i , nf , _)) lv = Q.live→ (e1 i nf) (C.live i (P.live← nf lv))
    live′ (inj₂ (cut tk nk nf i ul lb refl refl)) _ = Q.live-cut (firstQ tk nk nf i ul) (lab-plain lb)

    bk′ : Pos → List Pos
    bk′ l = C.bk l ++ L.map (λ k → k ⊕ [ ix 0 ]) (C.bk (parent l)) ++ L.map (λ k → k ⊕ [ last ]) (C.bk (parent l))

    in-bk′ : ∀ {k l} → Img′ k l → k ∈ bk′ l
    in-bk′ (inj₁ (i , _)) = ∈-++⁺ˡ (C.in-bk i)
    in-bk′ (inj₂ (cut {k₀} {l₀} _ _ _ i _ (inj₁ (refl , _)) refl refl)) =
      ∈-++⁺ʳ (C.bk (l₀ ⊕ [ ix 0 ])) (∈-++⁺ˡ (∈-map⁺ (λ k → k ⊕ [ ix 0 ]) (subst (λ z → k₀ ∈ C.bk z) (sym (parent-snoc l₀ (ix 0))) (C.in-bk i))))
    in-bk′ (inj₂ (cut {k₀} {l₀} _ _ _ i _ (inj₂ refl) refl refl)) =
      ∈-++⁺ʳ (C.bk (l₀ ⊕ [ last ])) (∈-++⁺ʳ (L.map (λ k → k ⊕ [ ix 0 ]) (C.bk (parent (l₀ ⊕ [ last ]))))
        (∈-map⁺ (λ k → k ⊕ [ last ]) (subst (λ z → k₀ ∈ C.bk z) (sym (parent-snoc l₀ last)) (C.in-bk i))))

    -- A skip carried into its instant keeps a carrier: its own, before
    -- the failure, or the end cut under the first failing value.
    cut-into : ∀ {k f l₁} → t k skip → ¬ P.Failed k → C.PB k l₁ → Q.First f → Listed u f
             → Σ Pos λ m → Σ (Ev (IE A)) (Q.T′ m) × Listed Q.T′ m × PB′ k m
    cut-into tk nfk _ ((instEmit (mark _) _ , _ , ()) , _) L
    cut-into {k} {f} tk nfk pb ff@((instEmit (value b) n , uf , ny) , nff) L with C.shown uf (b , refl) (Q.live-out uf) (Q.few-out uf)
    ... | k₀ , i₀ , e₀ , tk₀ , mt with match-val mt
    ...   | refl = f ⊕ [ last ] , (end , Q.cut-row uf ny nff (inj₂ refl)) , Q.lst-cut ff L (inj₂ refl)
                 , inj₂ (f , k₀ , ff , i₀ , refl , ((b , tk₀ , ny) , e2 i₀ nff) , before , (skip , tk) , (_ , pb))
      where
        before : k ≺ k₀
        before with ≼-or-≻ k k₀
        ... | inj₂ k₀k = ⊥-elim (nfk (k₀ , b , tk₀ , ny , k₀k))
        ... | inj₁ kk₀ with ≼-split {k} {k₀} kk₀
        ...   | inj₁ lt   = lt
        ...   | inj₂ refl with InvAt.func It tk tk₀
        ...     | ()

    into-row : ∀ {k l e} → t k skip → ¬ P.Failed k → u l e → Listed u l → C.PB k l
             → Σ Pos λ m → Σ (Ev (IE A)) (Q.T′ m) × Listed Q.T′ m × PB′ k m
    into-row {l = l} tk nfk ul L pb with Q.search L | Q.fails? ul
    ... | inj₁ nfl | inj₂ nfsl       = l , (_ , Q.up ul nfl (Q.pass-of nfsl ul)) , Q.lst→ nfl L , inj₁ ((_ , ul) , (_ , tk) , inj₁ nfk , pb)
    ... | inj₁ nfl | inj₁ (_ , ul′ , ny) = cut-into tk nfk pb ((_ , ul′ , ny) , nfl) L
    ... | inj₂ (f , ff , fl) | _     = cut-into tk nfk pb ff (sub-listed L fl)

    into-at : ∀ {k} → t k skip → ¬ P.Failed k → IntoAt C.Img u C.PB HP s k → IntoAt Img′ Q.T′ PB′ HP s k
    into-at {k} tk nf ((l , (_ , ul) , L , pb) , h) = into-row tk nf ul L pb , at h
      where
        at : _ → _
        at (inj₁ e) = inj₁ e
        at (inj₂ (inj₁ (k₀ , l₀ , i , kk , ek , (e₀ , ul₀) , L₀))) =
          let nf₀ = P.unfailed nf (≺→≼ {k₀} {k} kk)
              nfs₀ : ¬ P.Fails k₀
              nfs₀ = λ { (a , x , nk) → nf (k₀ , a , x , nk , kk) }
          in inj₂ (inj₁ (k₀ , l₀ , inj₁ (i , nf₀ , nfs₀) , kk , ek
                        , (e₀ , Q.up ul₀ (e1 i nf₀) (Q.pass-of (unfails→ i nfs₀) ul₀)) , Q.lst→ (e1 i nf₀) L₀))
        at (inj₂ (inj₂ h)) = inj₂ (inj₂ h)

    src-img : ∀ {k e} → t k e → Keeps keep e → ¬ P.Failed k → Unpinned e → Live P.T′ k → Listed P.T′ k → LP k
            → (Σ Pos λ l → Img′ k l × Σ (Ev (IE A)) λ e′ → Q.T′ l e′ × Listed Q.T′ l × Match Every (One valuesOf) (Reads valuesOf) e e′)
              ⊎ (e ≡ skip × IntoAt Img′ Q.T′ PB′ HP s k)
    src-img tk pe nf un lv L lp with C.img tk un (P.live← nf lv) (P.lst← nf L) lp
    ... | inj₁ (l , i , e′ , ul , Lu , mt) =
      inj₁ (l , inj₁ (i , nf , P.pass-fails tk pe) , e′ , Q.up ul (e1 i nf) (keeps→ {kp = keep} mt pe) , Q.lst→ (e1 i nf) Lu , mt)
    ... | inj₂ (refl , h) = inj₂ (refl , into-at tk nf h)

    pb-few′ : ∀ {m e} → Q.T′ m e → Σ (List Pos) λ ks → ∀ {k} → PB′ k m → k ∈ ks
    pb-few′ (r , _) with Q.view r
    ... | inj₁ (um , _) = proj₁ (C.pb-few um) , λ { (inj₁ (_ , _ , _ , pb)) → proj₂ (C.pb-few um) pb
                                                   ; (inj₂ (_ , _ , ((_ , uf , _) , _) , _ , eq , _)) → ⊥-elim (InvAt.flat Iu uf (subst (λ z → u z _) eq um)) }
    ... | inj₂ (q , instEmit (mark _) _ , _ , () , _)
    ... | inj₂ (q , instEmit (value b) n , uq , ny , nfq , a , lb , refl , refl) with C.shown uq (b , refl) (Q.live-out uq) (Q.few-out uq)
    ...   | k₀ , i₀ , e₀ , tk₀ , mt with match-val mt
    ...     | refl = proj₁ (C.few i₀) , mem
      where
        mem : ∀ {k} → PB′ k (q ⊕ [ a ]) → k ∈ proj₁ (C.few i₀)
        mem (inj₁ ((_ , um) , _)) = ⊥-elim (InvAt.flat Iu uq um)
        mem (inj₂ (f , k₁ , ff , i₁ , _ , pf , kk , (_ , tk) , _)) with Q.first ((_ , uq , ny) , nfq) ff
        ... | refl with P.first pf ((_ , tk₀ , ny) , e2 i₀ nfq)
        ...   | refl = proj₂ (C.few i₀) tk kk

    cut-img : ∀ {q b a} → t q (out b) → T (not (keep b)) → ¬ P.Failed q → Lab incl a → Listed P.T′ (q ⊕ [ a ]) → LP (q ⊕ [ a ])
            → Σ Pos λ l → Img′ (q ⊕ [ a ]) l × Σ (Ev (IE A)) λ e′ → Q.T′ l e′ × Listed Q.T′ l
              × Match Every (One valuesOf) (Reads valuesOf) (cutEv b a) e′
    cut-img {q} {b} {a} tq nk nf lb L lp
      with C.img tq tt (P.live-out tq) (P.lst← nf (sub-listed L (≺-ext q []))) (lp↓ (≺→≼ {q} {q ⊕ [ a ]} (≺-ext q [])) lp)
    ... | inj₂ (() , _)
    ... | inj₁ (l₀ , i , e′ , ul , Lu , mt) with carried-val mt
    ...   | n , refl = l₀ ⊕ [ a ] , inj₂ (cut tq nk nf i ul lb refl refl) , cutEv (instEmit (value b) n) a
                       , Q.cut-row ul nk (e1 i nf) lb , Q.lst-cut (firstQ tq nk nf i ul) Lu lb , cut-match lb

    img′ : ∀ {k e} → P.T′ k e → Unpinned e → Live P.T′ k → Listed P.T′ k → LP k
         → (Σ Pos λ l → Img′ k l × Σ (Ev (IE A)) λ e′ → Q.T′ l e′ × Listed Q.T′ l × Match Every (One valuesOf) (Reads valuesOf) e e′)
           ⊎ (e ≡ skip × IntoAt Img′ Q.T′ PB′ HP s k)
    img′ (r , _) un lv L lp with P.view r
    ... | inj₁ (tk , pe) = src-img tk pe (P.live-unfailed lv tk) un lv L lp
    ... | inj₂ (_ , _ , tq , nk , nf , _ , lb , refl , refl) = inj₁ (cut-img tq nk nf lb L lp)

    cut¬¬ : ∀ {q b a l₀ e′} → t q (out b) → T (not (keep b)) → ¬ P.Failed q → Lab incl a → C.Img q l₀ → u l₀ e′
          → Match Every (One valuesOf) (Reads valuesOf) (out b) e′
          → ¬ (Σ Pos λ l → Img′ (q ⊕ [ a ]) l × Σ (Ev (IE A)) λ e″ → Q.T′ l e″ × Match Every (One valuesOf) (Reads valuesOf) (cutEv b a) e″)
          → ⊥
    cut¬¬ {a = a} {l₀} tq nk nf lb i ul mt n with carried-val mt
    ... | _ , refl = n (l₀ ⊕ [ a ] , inj₂ (cut tq nk nf i ul lb refl refl) , _ , Q.cut-row ul nk (e1 i nf) lb , cut-match lb)

    img¬¬′ : ∀ {k e} → P.T′ k e → Unpinned e → Live P.T′ k → Few P.T′ k
           → ¬ ¬ ((Σ Pos λ l → Img′ k l × Σ (Ev (IE A)) λ e′ → Q.T′ l e′ × Match Every (One valuesOf) (Reads valuesOf) e e′) ⊎ e ≡ skip)
    img¬¬′ (r , _) un lv fw n with P.view r
    ... | inj₁ (tk , pe) = let nf = P.live-unfailed lv tk in
      C.img¬¬ tk un (P.live← nf lv) (P.few← nf fw) λ { (inj₁ (l , i , e′ , ul , mt)) →
        n (inj₁ (l , inj₁ (i , nf , P.pass-fails tk pe) , e′ , Q.up ul (e1 i nf) (keeps→ {kp = keep} mt pe) , mt))
        ; (inj₂ es) → n (inj₂ es) }
    ... | inj₂ (q , _ , tq , nk , nf , _ , lb , refl , refl) =
      C.img¬¬ tq tt (P.live-out tq) (P.few← nf (few-sub fw (≺-ext q []))) λ { (inj₁ (_ , i , _ , ul , mt)) → cut¬¬ tq nk nf lb i ul mt (λ x → n (inj₁ x))
                                                                            ; (inj₂ ()) }

    src-shown : ∀ {l e} → u l e → Keeps (passes keep) e → ¬ Q.Failed l → Shown (One valuesOf) e → Live Q.T′ l → Few Q.T′ l
              → Σ Pos λ k → Img′ k l × Σ (Ev A) λ e₀ → P.T′ k e₀ × Match Every (One valuesOf) (Reads valuesOf) e₀ e
    src-shown ul pe nf sw lv fw with C.shown ul sw (Q.live← nf lv) (Q.few← nf fw)
    ... | k , i , e₀ , tk , mt =
      k , inj₁ (i , e2 i nf , P.pass-fails tk (keeps← {kp = keep} mt pe)) , e₀ , P.up tk (e2 i nf) (keeps← {kp = keep} mt pe) , mt

    shown′ : ∀ {l e} → Q.T′ l e → Shown (One valuesOf) e → Live Q.T′ l → Few Q.T′ l
           → Σ Pos λ k → Img′ k l × Σ (Ev A) λ e₀ → P.T′ k e₀ × Match Every (One valuesOf) (Reads valuesOf) e₀ e
    shown′ (r , _) sw lv fw with Q.view r
    ... | inj₁ (ul , pe) = src-shown ul pe (Q.live-unfailed lv ul) sw lv fw
    ... | inj₂ (_ , _ , uq , ny , nfq , _ , lb , refl , refl) = cut-shown uq ny nfq lb

    ----------------------------------------------------------------------
    -- Placing a row from its source's placing

    Placed : Pos → Set
    Placed m = instantOf m ≡ instantOf s′ ⊎ (Σ Pos λ k → Σ Pos λ l → Img′ k l × instantOf l ≡ instantOf m × Near Q.T′ m l)
               ⊎ Σ Pos λ h → HE h × instantOf h ≡ instantOf m

    m≺f : ∀ {m e f} → Q.TakeT m e → ¬ Q.Failed m → Q.First f → m ≺ f
    m≺f {m} {f = f} r nfm ff@((y , uf , ny) , _) with ≼-or-≻ f m
    ... | inj₂ mf = mf
    ... | inj₁ fm with at-or-before {f} {m} fm
    ...   | inj₁ refl = ⊥-elim (Q.none-at ff r)
    ...   | inj₂ fm′  = ⊥-elim (nfm (f , y , uf , ny , fm′))

    -- Past the row, a carrier listed up to: the first failing value
    -- between them is found, and its end is the nearer carrier.
    near-past : ∀ {m e k l} → Q.TakeT m e → ¬ Q.Failed m → C.Img k l → instantOf l ≡ instantOf m → m ≺ l → Near u m l → Placed m
    near-past r nfm i il ml (inj₁ lm) = ⊥-elim (lm ml)
    near-past {m} {k = k} {l} r nfm i il ml (inj₂ ((e″ , ul) , Lul)) with Q.search Lul | Q.fails? ul
    ... | inj₁ nfl | inj₂ nfsl =
      inj₂ (inj₁ (k , l , inj₁ (i , e2 i nfl , unfails← i nfsl) , il , inj₂ ((e″ , Q.up ul nfl (Q.pass-of nfsl ul)) , Q.lst→ nfl Lul)))
    ... | inj₁ nfl | inj₁ (y , ul′ , ny) =
      let (k₀ , i₀ , _) = cut-shown ul′ ny nfl (inj₂ refl)
      in inj₂ (inj₁ (k₀ , l ⊕ [ last ] , i₀ , trans (instant-⊕ l [ last ]) il
                    , inj₂ ((end , Q.cut-row ul′ ny nfl (inj₂ refl)) , Q.lst-cut ((y , ul′ , ny) , nfl) Lul (inj₂ refl))))
    ... | inj₂ (f , ff@((y , uf , ny) , nff) , fl) | _ =
      let (k₀ , i₀ , _) = cut-shown uf ny nff (inj₂ refl)
      in inj₂ (inj₁ (k₀ , f ⊕ [ last ] , i₀ , trans (instant-⊕ f [ last ]) (between {m} {f} {l} (m≺f r nfm ff) fl il)
                    , inj₂ ((end , Q.cut-row uf ny nff (inj₂ refl)) , Q.lst-cut ff (sub-listed Lul fl) (inj₂ refl))))

    near-place : ∀ {m e k l} → Q.TakeT m e → ¬ Q.Failed m → C.Img k l → instantOf l ≡ instantOf m → Near u m l → Placed m
    near-place {m} {k = k} {l} r nfm i il near with ≼-or-≻ l m
    ... | inj₁ lm = inj₂ (inj₁ (k , l , inj₁ (i , e2 i (Q.unfailed nfm lm) , unfails← i (Q.unfails nfm r lm)) , il , inj₁ lm))
    ... | inj₂ ml = near-past r nfm i il ml near

    src-place : ∀ {m e} → Q.TakeT m e → u m e → ¬ Q.Failed m → Live Q.T′ m → Listed Q.T′ m → Placed m
    src-place r um nfm lv L with C.place um (Q.live← nfm lv) (Q.lst← nfm L)
    ... | inj₁ e                          = inj₁ e
    ... | inj₂ (inj₂ h)                   = inj₂ (inj₂ h)
    ... | inj₂ (inj₁ (k , l , i , il , near)) = near-place r nfm i il near

    place′ : ∀ {m e} → Q.T′ m e → Live Q.T′ m → Listed Q.T′ m → Placed m
    place′ (r , _) lv L with Q.view r
    ... | inj₁ (um , _) = src-place r um (Q.live-unfailed lv um) lv L
    ... | inj₂ (q , _ , uq , ny , nfq , a , lb , refl , refl) =
      let (k , i , _) = cut-shown uq ny nfq lb in inj₂ (inj₁ (k , q ⊕ [ a ] , i , refl , inj₁ (≼-refl {q ⊕ [ a ]})))

    ----------------------------------------------------------------------
    -- With no end, nothing fails, so every row is its source's

    u-fail : (∀ {c} → P.T′ c end → ⊥) → ∀ {q y} → u q (out y) → T (not (passes keep y)) → ⊥
    u-fail ne {y = instEmit (mark _) _} _ ()
    u-fail ne {y = instEmit (value b) n} uq nb with C.shown uq (b , refl) (Q.live-out uq) (Q.few-out uq)
    ... | _ , _ , _ , tk , mt with match-val mt
    ...   | refl = P.no-fail ne tk nb

    pickW : (∀ {c} → P.T′ c end → ⊥) → ∀ {ls} → (∀ {r e} → u r e → r ∈ ls) → ∀ {r e} → Q.T′ r e → r ∈ ls
    pickW ne F (r , _) with Q.view r
    ... | inj₁ (ur , _) = F ur
    ... | inj₂ (_ , _ , uq , ny , _) = ⊥-elim (u-fail ne uq ny)

    nfQ : (∀ {c} → P.T′ c end → ⊥) → ∀ {k} → ¬ Q.Failed k
    nfQ ne (_ , _ , x , nk , _) = u-fail ne x nk

    whole′ : Whole P.T′ → (∀ {c} → P.T′ c end → ⊥) → (∀ {q} → LP q) → Whole Q.T′
    whole′ wt ne lp = let (ls , F , B) = C.whole (P.whole← ne wt) (P.ended← ne) lp in
      ls , pickW ne F , λ m → let (e , ur) = B m in e , Q.up ur (nfQ ne) (Q.pass-of (λ { (_ , x , nk) → u-fail ne x nk }) ur)

    ----------------------------------------------------------------------
    -- Rows carried into their instant: no carrier in order, and past what
    -- the map puts before them.  A cut lies under a failing value, which
    -- an unfailed row and the first failing value both precede.

    pb-img′ : ∀ {k l l′} → PB′ k l → Img′ k l′ → ⊥
    pb-img′ (inj₁ (_ , _ , _ , pb)) (inj₁ (i , _)) = C.pb-img pb i
    pb-img′ (inj₁ (_ , (_ , tk) , _)) (inj₂ (cut tk₀ _ _ _ _ _ refl _)) = flatP tk₀ tk
    pb-img′ (inj₂ (_ , _ , _ , _ , _ , _ , _ , _ , (_ , pb))) (inj₁ (i , _)) = C.pb-img pb i
    pb-img′ (inj₂ (_ , _ , _ , _ , _ , _ , _ , (_ , tk) , _)) (inj₂ (cut tk₀ _ _ _ _ _ refl _)) = flatP tk₀ tk

    pb-past′ : ∀ {k l e₀ e x y} → PB′ k l → P.T′ k e₀ → (Unpinned e₀ → Live P.T′ k) → Q.T′ l e → M′ x y → x ≺ k → ¬ (x ⊑ k) → Ahead y l
    pb-past′ (inj₁ ((_ , um) , (_ , tk) , nfk , pb)) (r , _) lv _ (inj₁ m) xk nxk with P.view r
    ... | inj₁ (tk′ , _) = C.pb-past pb tk′ (live-of nfk tk′ lv) um m xk nxk
    ... | inj₂ (_ , _ , x₀ , _ , _ , _ , _ , refl , _) = ⊥-elim (flatP x₀ tk)
    pb-past′ {k} (inj₁ (_ , _ , inj₁ nfk , _)) _ _ _ (inj₂ (cut {k₀ = k₁} {a = a} tk₁ nk₁ _ _ _ _ refl refl)) xk _ =
      ⊥-elim (nfk (k₁ , _ , tk₁ , nk₁ , ≺-trans {k₁} {k₁ ⊕ [ a ]} {k} (≺-ext k₁ []) xk))
    pb-past′ {k} (inj₁ ((_ , um) , _ , inj₂ (r , tk) , pb)) _ _ _ (inj₂ (cut {k₀ = k₁} {a = a} tk₁ nk₁ _ i₁ _ _ refl refl)) xk _ with C.ext i₁
    ... | y₀ , m₀ , y₀l₁ =
      ahead-under (C.pb-past pb tk (λ un → ⊥-elim (unp-pin {A} {r} un)) um m₀ k₁k (P.not-under tk₁ tk k₁k)) (⊑-trans y₀l₁ (⊑-snoc⁺ _))
      where
        k₁k : k₁ ≺ k
        k₁k = ≺-trans {k₁} {k₁ ⊕ [ a ]} {k} (≺-ext k₁ []) xk
    pb-past′ {k} {x = x} {y} (inj₂ (f , k₀ , _ , i₀ , refl , _ , kk , _)) _ _ _ (inj₁ m) xk nxk with C.ext i₀
    ... | y₀ , m₀ , y₀f =
      ahead-over (Emb.mono hm m m₀ xk₀ , λ yy → nxk₀ (Emb.reflect hm m m₀ yy)) (⊑-trans y₀f (⊑-snoc⁺ f))
      where
        xk₀ : x ≺ k₀
        xk₀ = ≺-trans {x} {k} {k₀} xk kk
        nxk₀ : ¬ (x ⊑ k₀)
        nxk₀ xk′ = nxk (conv (⊑-refl x) (≺→≼ {x} {k} xk) kk xk′)
    pb-past′ {k} (inj₂ (_ , k₀ , _ , _ , refl , (_ , nf₀) , kk , _)) _ _ _ (inj₂ (cut {k₀ = k₁} {a = a} tk₁ nk₁ _ _ _ _ refl refl)) xk _ =
      ⊥-elim (nf₀ (k₁ , _ , tk₁ , nk₁ , ≺-trans {k₁} {k} {k₀} (≺-trans {k₁} {k₁ ⊕ [ a ]} {k} (≺-ext k₁ []) xk) kk))

    ----------------------------------------------------------------------
    -- Pins: kept with their connect unfailed, past no carried failure

    pin-unfailed : ∀ {p p′} → ¬ P.Failed p → Targeted M p p′ → ¬ Q.Failed p′
    pin-unfailed nfp tg (q , instEmit (mark _) _ , _ , () , _)
    pin-unfailed nfp tg (q , instEmit (value b) n , uq , nb , qp) with C.shown uq (b , refl) (Q.live-out uq) (Q.few-out uq)
    ... | k′ , i′ , _ , tk′ , mt with match-val mt
    ...   | refl = nfp (k′ , b , tk′ , nb , pin-bound hm tg (proj₁ (proj₂ (C.ext i′))) (proj₂ (proj₂ (C.ext i′))) qp)

    aimed : ∀ {p p′} → Targeted M p p′ → Targeted M′ p p′
    aimed (y , m , py) = y , inj₁ m , py

    home-up : ∀ {p k₀} → ¬ P.Failed p → k₀ ≺ p → Home t k₀ → Home P.T′ k₀
    home-up {p} {k₀} nfp kp h n = h λ { (e , tk , un) → n (e , P.up tk (P.unfailed nfp (≺→≼ {k₀} {p} kp)) (P.pass-before tk kp nfp) , un) }

    PinOut : Pos → Pos → Set
    PinOut k p = (Σ Pos λ l → Σ Pos λ p′ → Q.T′ l (pin p′) × PB′ k l × Targeted M′ p p′ × Listed Q.T′ l)
                 × (instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → k₀ ≺ p × Home P.T′ k₀ × instantOf k₀ ≡ instantOf k)
                    ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)

    homed : ∀ {k p} → ¬ P.Failed p
          → instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → k₀ ≺ p × Home t k₀ × instantOf k₀ ≡ instantOf k) ⊎ Σ Pos (λ h → HP h × instantOf h ≡ instantOf k)
          → instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → k₀ ≺ p × Home P.T′ k₀ × instantOf k₀ ≡ instantOf k) ⊎ Σ Pos (λ h → HP h × instantOf h ≡ instantOf k)
    homed nfp (inj₁ e)                        = inj₁ e
    homed nfp (inj₂ (inj₁ (k₀ , kp , h , ek))) = inj₂ (inj₁ (k₀ , kp , home-up nfp kp h , ek))
    homed nfp (inj₂ (inj₂ hh))                = inj₂ (inj₂ hh)

    -- The source's pin and its connect's past, from the taken run's.
    lst-at : ∀ {k p} → ¬ P.Failed p → p ≼ k → Listed P.T′ k → Listed t p
    lst-at {k} {p} nfp pk L with ≼-split {p} {k} pk
    ... | inj₁ lt = P.lst← nfp (sub-listed L lt)
    ... | inj₂ e  = P.lst← nfp (subst (Listed P.T′) (sym e) L)

    under : ∀ {k p} → t k (pin p) → p ≼ k
    under {k} {p} tk = ⊑-≼ (inside-⊑ p k (P.ins tk))

    -- The rows before a pin kept past the failure are listed.  Past
    -- the elaborated failure they are the kept pins of the connects the
    -- failure lies in: the carrier's own connect's come listed with the
    -- carrier, and the rest are pins of connects in that connect's body,
    -- which the pin does not wait on.  Each of those carries a plain
    -- pin, kept in the plain body and so before the pin listed; what is
    -- open is that correspondence, since the map need not keep the plain
    -- nesting of a body under its connect.
    -- DEAD ROUTE: the source's `pinned` on the source pin.  It asks the
    --   source listed up to the pin, and past the failure the source's
    --   rows are hidden: the takeWhile lists only the pins it keeps,
    --   while the source may make infinitely many rows between.
    -- DEAD ROUTE: the plain pins before the pin, carried.  A connect pins
    --   every row of its source's burst, values too, and a pin carried
    --   late passes a value the plain run puts after it: the elaborated
    --   pin of that value lies before the carrier, its plain pin after
    --   the pin.
    postulate
      take-pin-listed : ∀ {k p l p′} → P.T′ k (pin p) → P.Failed k → Listed P.T′ k → LP k
                      → u l (pin p′) → C.PB k l → Targeted M p p′ → PinList u p′ l → Listed Q.T′ l

    pinned′ : ∀ {k p} → P.T′ k (pin p) → Listed P.T′ k → LP k → PinOut k p
    pinned′ {k} {p} tk′@(P.left tk nfp _ , _) L lp with P.failed-at? L tk
    ... | yes fk with Narrow.pinned↓ nar tk (lst-at nfp (under tk) L) (P.pins-of nfp L) (lp↓ (under tk) lp)
    ...   | (l , p′ , ul , mb , bd , Pu) , h =
      (l , p′ , Q.lift (Q.left ul (pin-unfailed nfp bd) (Q.ins ul)) , inj₁ ((pin p′ , ul) , (_ , tk) , inj₂ (_ , tk) , mb) , aimed bd
         , take-pin-listed tk′ fk L lp ul mb bd Pu) , homed {k} {p} nfp h
    pinned′ {k} {p} tk′@(P.left tk nfp _ , _) L lp | no nfk with C.pinned tk (P.lst← nfk L) lp
    ... | (l , p′ , ul , mb , bd , ls) , h =
      (l , p′ , Q.lift (Q.left ul (pin-unfailed nfp bd) (Q.ins ul)) , inj₁ ((pin p′ , ul) , (_ , tk) , inj₁ nfk , mb) , aimed bd , Q.lst-any ls) , homed {k} {p} nfp h

    -- A PIN KEPT IS CARRIED FROM ITS OWN PAST, as its source's: its
    -- connect is subscribed before the failure, so the rows before it
    -- and its pins are the source's.
    pinned↓′ : ∀ {k p} → P.T′ k (pin p) → Listed P.T′ p → PinList P.T′ p k → LP p
             → (Σ Pos λ l → Σ Pos λ p′ → Q.T′ l (pin p′) × PB′ k l × Targeted M′ p p′ × PinList Q.T′ p′ l)
               × (instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → k₀ ≺ p × Home P.T′ k₀ × instantOf k₀ ≡ instantOf k)
                  ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)
    pinned↓′ {k} {p} (P.left tk nfp _ , _) L Pk lp with Narrow.pinned↓ nar tk (P.lst← nfp L) (P.pins← nfp Pk) lp
    ... | (l , p′ , ul , mb , bd , Pu) , h =
      (l , p′ , Q.lift (Q.left ul (pin-unfailed nfp bd) (Q.ins ul)) , inj₁ ((pin p′ , ul) , (_ , tk) , inj₂ (_ , tk) , mb) , aimed bd
         , Q.pins→ (pin-unfailed nfp bd) Pu) , homed {k} {p} nfp h

  -- The taken run listed before a point its carriers follow.
  postulate
    take-cover : ∀ {v w} → Listed P.T′ v → LP v → Live P.T′ v → From Img′ PB′ P.T′ Q.T′ v w → Listed Q.T′ w

  carried′ : CarryAt valuesOf M′ HP HE LP P.T′ Q.T′ s s′
  carried′ = record
    { Img = Img′ ; ext = ext′ ; img = img′ ; img¬¬ = img¬¬′ ; shown = shown′ ; img-row = img-row′ ; img-fun = img-fun′
    ; place = place′ ; live = live′ ; few = few′ ; whole = whole′ ; cover = take-cover ; bk = bk′ ; in-bk = in-bk′ ; PB = PB′ ; pb-few = pb-few′ ; pinned = pinned′
    ; pb-img = pb-img′ ; pb-past = pb-past′ }

  narrowed′ : Narrow carried′
  narrowed′ = record { pinned↓ = pinned↓′ }

  -- A row carried into its instant: its source's, or anchored past by the
  -- first failing value it precedes.
  pb-anchor : ∀ {k l e₀} → PB′ k l → P.T′ k e₀ → (Unpinned e₀ → Live P.T′ k)
            → (Σ Pos λ l₀ → C.PB k l₀ × l₀ ⊑ l × Σ (Ev A) λ e → t k e × (Unpinned e → Live t k)) ⊎ Σ Pos λ x → Σ Pos λ y → M′ x y × y ⊑ l × k ≺ x
  pb-anchor {l = l} (inj₁ (_ , (_ , tk) , nfk , pb)) (r , _) lv with P.view r
  ... | inj₁ (tk′ , _) = inj₁ (l , pb , ⊑-refl l , _ , tk′ , live-of nfk tk′ lv)
  ... | inj₂ (_ , _ , x₀ , _ , _ , _ , _ , refl , _) = ⊥-elim (flatP x₀ tk)
  pb-anchor (inj₂ (f , k₀ , _ , i₀ , refl , _ , kk , _)) _ _ with C.ext i₀
  ... | y₀ , m₀ , y₀f = inj₂ (k₀ , y₀ , inj₁ m₀ , ⊑-trans y₀f (⊑-snoc⁺ f) , kk)

------------------------------------------------------------------------
-- The former

-- THE ELABORATED TAKEWHILE CARRIES the plain one, its map grown by the
-- cuts under the first failing value.
take-carry : ∀ {A} incl (keep : A → Bool) (d : Den A) (d′ : Den (IE A)) {M HP HE LP H₁ H₂ R} p p′ → Emb M
           → InvAt H₁ p (enter d p) → InvAt H₂ p′ (enter d′ p′) → (∀ {q w} → R q → W H₁ p w → T (inside w q) → ⊥) → Bare M (enter d p) → (∀ {x y} → x ≼ y → LP y → LP x)
           → (c : CarryAt valuesOf M HP HE LP (enter d p) (enter d′ p′) p p′) → Narrow c
           → Σ PMap λ M′ → M ⊆ᴹ M′ × Emb M′ × (∀ {x y} → M′ x y → M x y ⊎ W⁼ H₁ p x) × Bare M′ (enter (Op.takeWhile incl keep d) p)
             × (∀ {x y} → M′ x y → M x y ⊎ Grown M R x y)
             × Σ (CarryAt valuesOf M′ HP HE LP (enter (Op.takeWhile incl keep d) p) (enter (Op.takeWhile incl (passes keep) d′) p′) p p′) λ c′
                 → Narrow c′ × ∀ {k l e₀} → CarryAt.PB c′ k l → enter (Op.takeWhile incl keep d) p k e₀ → (Unpinned e₀ → Live (enter (Op.takeWhile incl keep d) p) k)
                   → (Σ Pos λ l₀ → CarryAt.PB c k l₀ × l₀ ⊑ l × Σ (Ev A) λ e → enter d p k e × (Unpinned e → Live (enter d p) k)) ⊎ Σ Pos λ x → Σ Pos λ y → M′ x y × y ⊑ l × k ≺ x
take-carry incl keep d d′ p p′ hm It Iu dj br lp c nc = K.M′ , inj₁ , K.emb′ , K.within′ , K.bare′ , K.grown′ dj , K.carried′ , K.narrowed′ , K.pb-anchor
  where module K = Core incl keep hm (λ {q} {e} → entered-reach d p {q} {e}) (λ {q} {e} → entered-reach d′ p′ {q} {e}) It Iu br lp c nc

carry-takeWhile : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) i (p : A → Bool) s → Carry m ρ s → Carry m ρ (takeWhile i p s)
carry-takeWhile n ρ i k s (carry h) = carry λ envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr →
  let (M , ms , hm′ , wi , br , jn′ , ep , c , nc , nr) = h envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr
      (M′ , ms′ , hm″ , wi′ , br′ , gr , c′ , nr′ , dn) = take-carry i k (approx n s envP) (approx n (elab ρ s) envE) p p′ hm′
        (inv-approx n s envP gP p okP) (inv-approx n (elab ρ s) envE gE p′ okE) (λ r w i → nh r (inW w) i) br (λ {x} {y} → listed↓ envP {x} {y}) c nr
  in M′ , (λ m → ms′ (ms m)) , hm″ , within-∘ {M₀ = M₀} {M = M} {M′ = M′} {p = p} wi (λ {x} {y} → wi′ {x} {y}) , br′
     , joins-grow {ρ = ρ} {envP = envP} {envE = envE} {er = er} {M = M} {N = M′} (λ {x} {y} → ms′ {x} {y}) jn′ (λ {x} {y} → gr {x} {y})
     , grown-past {ρ = ρ} {envP = envP} {envE = envE} er ep (λ {x} {y} → gr {x} {y})
     , c′ , nest-or {er = er} {c = c} {c′ = c′} (λ {x} {y} → ms′ {x} {y}) (λ {k} {l} {e₀} → dn {k} {l} {e₀}) nc , nr′
