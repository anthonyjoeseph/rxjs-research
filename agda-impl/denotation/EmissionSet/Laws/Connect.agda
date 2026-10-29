{-# OPTIONS --guardedness #-}

-- A CONNECT KEEPS THE INVARIANT.  Subscribed at `p`, its body is read at
-- `p ++ [ ix 0 ]` and its source at `p ++ [ ix 1 ]`: sibling worlds, which
-- share no position (`apart`).
--
-- A body position leads no source position (`body-leads`).  A source
-- position leads a body position only through a source row the body
-- joined (`source-leads`).  Every flat and burst obligation of the
-- connect's rows reduces to these two, the source's own flatness, and the
-- body's own burst.
module denotation.EmissionSet.Laws.Connect where

open import Data.Bool using (T)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_)

open import denotation.MonotonicList.Events using (Pos; ix; sub; inside; <ᵖ-part; <ᵖ-between)
open import denotation.EmissionSet using (Ev; end; skip; EmissionSet; _≺_; Den; hot; Truncate; Proper; module Connect; connectᵀ)
open import denotation.EmissionSet.Laws.Modulus using (≺-absurd; ≼-≺-≺; ≺-≼-≺; ≼-or-≻; ≺-ext)
open import denotation.EmissionSet.Laws.Worlds
  using (W; W⁼; step; timer; join; here; inW; plain-ix; Real; Ok; _⊕_; Lawful; InvAt; InvD; ok-step;
  real-snoc; shrink; shrink⁼; narrow; narrow⁼; ext≢; _⊑_; ⊑-refl; ⊑-snoc⁺; ⊑-trans; ⊑-snoc;
  ⊑-cmp; ⊑-inside; inside-⊑; diverge; same-lead; flat-under; Anc; world-anc; world-anc⁼; anc-≼;
  apart; anc-lead; tick-lead)

module _ {A B : Set} {H : Pos → Set} {s : Den A} {F : Den A → Den B}
         (Is : InvD H s) (IF : ∀ {t} → Lawful t → InvD (H ⊕ t) (F (hot t)))
         (p : Pos) (ok : Ok H p) where

  open Connect s F p

  private
    p₀ : Pos
    p₀ = p ++ [ ix 0 ]

    σ′ : EmissionSet A
    σ′ = Proper σ

    H₀ : Pos → Set
    H₀ = H ⊕ σ′

    rp : Real p
    rp = proj₁ ok

    Iσ : InvAt H r σ
    Iσ = Is r (ok-step p ok)

    σ-wp : ∀ {h e} → σ′ h e → W H p h
    σ-wp x = shrink (InvAt.world Iσ (proj₁ x))

    -- A BODY POSITION LEADS NO SOURCE POSITION.
    mutual
      body-leads : ∀ {w x} → W⁼ H₀ p₀ w → W⁼ H r x → w ⊑ x → ⊥
      body-leads {w} bw here le with ⊑-snoc p le
      ... | inj₂ refl = apart rp (world-anc⁼ bw) (world-anc⁼ {H} here)
      ... | inj₁ wp   = anc-lead (world-anc⁼ bw) wp rp (≺-ext p [])
      body-leads bw (inW sx) le = body-leads′ bw sx le

      body-leads′ : ∀ {w x} → W⁼ H₀ p₀ w → W H r x → w ⊑ x → ⊥
      body-leads′ bw (step {x′} sx pl) le with ⊑-snoc x′ le
      ... | inj₁ le′  = body-leads bw sx le′
      ... | inj₂ refl = apart rp (world-anc⁼ bw) (world-anc (step sx pl))
      body-leads′ bw (timer t sx) le with ⊑-snoc (ix t ∷ []) le
      ... | inj₁ le′  = tick-lead rp (world-anc⁼ bw) le′
      ... | inj₂ refl = apart rp (world-anc⁼ bw) (world-anc (timer t sx))
      body-leads′ bw (join {h} (inj₁ hh) sx eh) le with ⊑-snoc h le
      ... | inj₁ le′  = proj₂ ok hh (narrow⁼ σ-wp bw) (⊑-inside le′)
      ... | inj₂ refl = apart rp (world-anc⁼ bw) (world-anc (join (inj₁ hh) sx eh))
      body-leads′ bw (join {h} (inj₂ sh) sx eh) le with ⊑-snoc h le
      ... | inj₁ le′  = body-leads′ bw sh le′
      ... | inj₂ refl = apart rp (world-anc⁼ bw) (world-anc (join (inj₂ sh) sx eh))

    -- A source row joined under `sub e`, between a source position and a
    -- body position it leads.
    Through : Pos → Pos → Set
    Through x y = Σ Pos λ h → Σ Pos λ e → Σ (Ev A) (σ′ h) × x ⊑ h × (h ++ [ sub e ]) ⊑ y

    later : ∀ {x y z} → Through x y → y ⊑ z → Through x z
    later (h , e , σh , xh , hy) yz = h , e , σh , xh , ⊑-trans hy yz

    -- A SOURCE POSITION LEADS A BODY POSITION ONLY THROUGH A JOINED ROW.
    mutual
      source-leads : ∀ {x y} → W⁼ H r x → W⁼ H₀ p₀ y → x ⊑ y → Through x y
      source-leads sx here le with ⊑-snoc p le
      ... | inj₂ refl = ⊥-elim (apart rp (world-anc⁼ {H₀} here) (world-anc⁼ sx))
      ... | inj₁ xp   = ⊥-elim (anc-lead (world-anc⁼ sx) xp rp (≺-ext p []))
      source-leads sx (inW by) le = source-leads′ sx by le

      source-leads′ : ∀ {x y} → W⁼ H r x → W H₀ p₀ y → x ⊑ y → Through x y
      source-leads′ sx (step {y′} by pl) le with ⊑-snoc y′ le
      ... | inj₁ le′  = later (source-leads sx by le′) (⊑-snoc⁺ y′)
      ... | inj₂ refl = ⊥-elim (apart rp (world-anc (step by pl)) (world-anc⁼ sx))
      source-leads′ sx (timer t by) le with ⊑-snoc (ix t ∷ []) le
      ... | inj₁ le′  = ⊥-elim (tick-lead rp (world-anc⁼ sx) le′)
      ... | inj₂ refl = ⊥-elim (apart rp (world-anc (timer t by)) (world-anc⁼ sx))
      source-leads′ sx (join {h} {e} (inj₁ (inj₁ σh)) by eh) le with ⊑-snoc h le
      ... | inj₁ le′  = h , e , σh , le′ , ⊑-refl (h ++ [ sub e ])
      ... | inj₂ refl = ⊥-elim (apart rp (world-anc (join (inj₁ (inj₁ σh)) by eh)) (world-anc⁼ sx))
      source-leads′ sx (join {h} (inj₁ (inj₂ hh)) by eh) le with ⊑-snoc h le
      ... | inj₁ le′  = ⊥-elim (proj₂ ok hh (shrink⁼ sx) (⊑-inside le′))
      ... | inj₂ refl = ⊥-elim (apart rp (world-anc (join (inj₁ (inj₂ hh)) by eh)) (world-anc⁼ sx))
      source-leads′ sx (join {h} {e} (inj₂ bh) by eh) le with ⊑-snoc h le
      ... | inj₁ le′  = later (source-leads′ sx bh le′) (⊑-snoc⁺ h)
      ... | inj₂ refl = ⊥-elim (apart rp (world-anc (join (inj₂ bh) by eh)) (world-anc⁼ sx))

    lawful : Lawful σ′
    lawful = record
      { real   = λ x → InvAt.real Iσ (proj₁ x)
      ; flat   = λ x x′ → InvAt.flat Iσ (proj₁ x) (proj₁ x′)
      ; proper = λ c y → proj₂ y (proj₁ c)
      }

    ok₀ : Ok H₀ p₀
    ok₀ = real-snoc p plain-ix rp , dj
      where
        dj : ∀ {h w} → H₀ h → W H₀ p₀ w → T (inside w h) → ⊥
        dj (inj₂ hh)      w i = proj₂ ok hh (narrow σ-wp w) i
        dj (inj₁ (_ , x)) w i = body-leads (inW w) (inW (InvAt.world Iσ (proj₁ x))) (inside-⊑ _ _ i)

    Iβ : InvAt H₀ p₀ β
    Iβ = IF lawful p₀ ok₀

    bw : ∀ {y e} → β y e → W⁼ H₀ p₀ y
    bw x = inW (InvAt.world Iβ x)

    sw : ∀ {y e} → σ y e → W⁼ H r y
    sw x = inW (InvAt.world Iσ x)

    -- A connect row, its position free.
    data V (y : Pos) (e : Ev B) : Set where
      vb : β y e → V y e
      vs : ∀ {k e′} → σ k e′ → Alive k → y ≡ k ++ [ ix 0 ] → e ≡ skip → V y e
      vp : ∀ {e′} → σ y e′ → ¬ Alive y → T (inside r y) → e ≡ skip → V y e

    view : ∀ {y e} → Truncate ConnT y e → V y e
    view (body x , _)       = vb x
    view (shown x a , _)    = vs x a refl refl
    view (pinned x a i , _) = vp x a i refl

    -- UNDER A SOURCE ROW THE BODY IS ALIVE: an end at or before it would
    -- put the body row in that end's burst, below a body position leading
    -- the source row.
    alive-at : ∀ {k e l ys e′} → σ k e → β (k ++ l ∷ ys) e′ → Alive k
    alive-at {k} {l = l} {ys} x b {c} ce with ≼-or-≻ c k
    ... | inj₂ kc = kc
    ... | inj₁ ck with InvAt.burst Iβ ce b (≼-≺-≺ {c} {k} {k ++ l ∷ ys} ck (≺-ext k ys))
    ...   | w , w⁼ , ic , ib with ⊑-cmp w k (inside-⊑ w _ ib) (l ∷ ys , refl)
    ...     | inj₁ wk = ⊥-elim (body-leads w⁼ (sw x) wk)
    ...     | inj₂ kw with ⊑-trans kw (inside-⊑ w c ic)
    ...       | [] , eq     = ⊥-elim (apart rp (subst (Anc p₀) (trans eq (++-identityʳ k)) (world-anc⁼ (bw ce))) (world-anc⁼ (sw x)))
    ...       | z ∷ zs , eq = subst (k ≺_) (sym eq) (≺-ext k zs)

    fl : ∀ {y e l ys e′} → V y e → V (y ++ l ∷ ys) e′ → ⊥
    fl (vb b) (vb b′) = InvAt.flat Iβ b b′
    fl {y} {l = l} {ys} (vb b) (vs {k} x _ eq _) with ⊑-snoc k (l ∷ ys , sym eq)
    ... | inj₁ yk = body-leads (bw b) (sw x) yk
    ... | inj₂ e₂ = ext≢ y ys (trans eq (sym e₂))
    fl {l = l} {ys} (vb b) (vp x _ _ _) = body-leads (bw b) (sw x) (l ∷ ys , refl)
    fl {l = l} {ys} (vs {k} x _ refl _) (vb b) with source-leads (sw x) (bw b) (ix 0 ∷ l ∷ ys , ++-assoc k [ ix 0 ] (l ∷ ys))
    ... | h , e , (_ , σh) , kh , (ms , eq) with same-lead Iσ x (proj₁ σh) kh
    ...   | refl = diverge k (l ∷ ys) ms (λ ()) eq
    fl {l = l} {ys} (vs {k} x _ refl _) (vs {k′} x′ _ eq _) with ⊑-snoc k′ (l ∷ ys , sym eq)
    ... | inj₁ le = flat-under Iσ x x′ le
    ... | inj₂ e₂ = ext≢ (k ++ [ ix 0 ]) ys (trans eq (sym e₂))
    fl {l = l} {ys} (vs x _ refl _) (vp x′ _ _ _) = flat-under Iσ x x′ (l ∷ ys , refl)
    fl (vp x na _ _) (vb b) = na (alive-at x b)
    fl {y} {l = l} {ys} (vp x na _ _) (vs {k′} x′ a′ eq _) with ⊑-snoc k′ (l ∷ ys , sym eq)
    ... | inj₂ e₂ = ext≢ y ys (trans eq (sym e₂))
    ... | inj₁ yk with same-lead Iσ x x′ yk
    ...   | refl = na a′
    fl (vp x _ _ _) (vp x′ _ _ _) = InvAt.flat Iσ x x′

    -- A pinned row lies under `p`, and so does anything between `p` and it.
    pinned-under : ∀ {k} → T (inside r k) → p ⊑ k
    pinned-under {k} i with inside-⊑ r k i
    ... | zs , eq = ix 1 ∷ zs , trans eq (++-assoc p [ ix 1 ] zs)

    between : ∀ {c k} → p ≺ c → c ≺ k → p ⊑ k → p ⊑ c
    between {c} pc ck (zs , refl) = <ᵖ-between p c zs (Equivalence.to T-≡ pc) (Equivalence.to T-≡ ck)

    bu : ∀ {c y e} → V c end → V y e → c ≺ y → Σ Pos λ w → W⁼ H p w × T (inside w c) × T (inside w y)
    bu (vs _ _ _ ()) _ _
    bu (vp _ _ _ ()) _ _
    bu (vb ce) (vb b) cy with InvAt.burst Iβ ce b cy
    ... | w , w⁼ , i = w , inW (narrow⁼ σ-wp w⁼) , i
    bu {c} (vb ce) (vs {k} x a refl _) cy with <ᵖ-between k c [ ix 0 ] (Equivalence.to T-≡ (a ce)) (Equivalence.to T-≡ cy)
    ... | zs , refl with source-leads (sw x) (bw ce) (zs , refl)
    ...   | h , e , (_ , σh) , kh , (ms , eq) with same-lead Iσ x (proj₁ σh) kh
    ...     | refl = ⊥-elim (≺-absurd {k ++ zs} {k ++ [ ix 0 ]} cy
                       (subst ((k ++ [ ix 0 ]) ≺_) (sym (trans eq (++-assoc k [ sub e ] ms)))
                         (Equivalence.from T-≡ (<ᵖ-part k {ix 0} {sub e} [] ms refl))))
    bu {c} {k} (vb ce) (vp x na i _) cy = p , here , ⊑-inside (between pc cy pk) , ⊑-inside pk
      where
        pk = pinned-under i
        pc : p ≺ c
        pc = ≺-≼-≺ {p} {p₀} {c} (≺-ext p []) (anc-≼ (world-anc⁼ (bw ce)) (InvAt.real Iβ ce))

  -- The connect's reading at an admissible `p`.
  connect-at : InvAt H p (Truncate ConnT)
  connect-at = record
    { world = wo
    ; real  = re
    ; flat  = λ x x′ → fl (view x) (view x′)
    ; burst = λ c y cy → bu (view c) (view y) cy
    }
    where
      wo : ∀ {y e} → Truncate ConnT y e → W H p y
      wo (body x , _)       = narrow σ-wp (InvAt.world Iβ x)
      wo (shown x _ , _)    = step (inW (shrink (InvAt.world Iσ x))) plain-ix
      wo (pinned x _ _ , _) = shrink (InvAt.world Iσ x)

      re : ∀ {y e} → Truncate ConnT y e → Real y
      re (body x , _)       = InvAt.real Iβ x
      re (shown {k} x _ , _) = real-snoc k {ix 0} plain-ix (InvAt.real Iσ x)
      re (pinned x _ _ , _) = InvAt.real Iσ x

connect-inv : ∀ {A B H} {s : Den A} {F : Den A → Den B} → InvD H s → (∀ {t} → Lawful t → InvD (H ⊕ t) (F (hot t))) → InvD H (connectᵀ s F)
connect-inv Is IF p ok = connect-at Is IF p ok
