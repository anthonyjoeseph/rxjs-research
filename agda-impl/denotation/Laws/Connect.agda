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
module denotation.Laws.Connect where

open import Data.Bool using (T; true; false; not; if_then_else_)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc; ++-identityʳ; ∷ʳ-injectiveˡ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_)

open import denotation.Events using (Pos; ix; sub; inside; <ᵖ-part; <ᵖ-between)
open import denotation.EmissionSet using (Ev; out; end; skip; pin; Unpinned; Silent; hush; held; EmissionSet; _≺_; Den; hot; Truncate; Proper; module Connect; module Op)
open import denotation.Laws.Modulus using (≺-absurd; ≼-≺-≺; ≺-≼-≺; ≼-or-≻; ≺-ext)
open import denotation.Laws.Worlds
  using (W; W⁼; step; timer; join; here; inW; plain-ix; Real; Ok; _⊕_; Lawful; InvAt; InvD; ok-step;
  real-snoc; shrink; shrink⁼; narrow; narrow⁼; ext≢; _⊑_; ⊑-refl; ⊑-snoc⁺; ⊑-trans; ⊑-snoc;
  ⊑-cmp; ⊑-inside; inside-⊑; diverge; same-lead; flat-under; Anc; world-anc; world-anc⁼; anc-≼;
  apart; anc-lead; tick-lead; Plain; widen⁼; nest⁼; w-up)

module _ {A B : Set} {H : Pos → Set} {s : Den A} {F : Den A → Den B}
         (Is : InvD H s) (IF : ∀ {t} → Lawful t → InvD (H ⊕ t) (F (hot t)))
         (p : Pos) (ok : Ok H p) where

  open Connect s F p

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
    ; func   = λ x x′ → InvAt.func Iσ (proj₁ x) (proj₁ x′)
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

  -- A pinned row lies under `p`, and so does anything between `p` and it.
  pinned-under : ∀ {k} → T (inside r k) → p ⊑ k
  pinned-under {k} i with inside-⊑ r k i
  ... | zs , eq = ix 1 ∷ zs , trans eq (++-assoc p [ ix 1 ] zs)

  -- What a source row at `k` shows as: this connect's pin in its burst, a
  -- pin of its own outside, and a skip otherwise.
  own : Ev A → Ev B
  own (pin p′) = pin p′
  own _        = skip

  tag : Pos → Ev A → Ev B
  tag k e = if inside r k then pin p else own e

  tag-in : ∀ {k e} → T (inside r k) → pin p ≡ tag k e
  tag-in {k} i with inside r k
  ... | true  = refl
  ... | false = ⊥-elim i

  tag-out : ∀ {k e} → T (not (inside r k)) → own e ≡ tag k e
  tag-out {k} i with inside r k
  ... | true  = ⊥-elim i
  ... | false = refl

  own-unpinned : ∀ {e} → Unpinned e → skip ≡ own e
  own-unpinned {out _} _ = refl
  own-unpinned {skip}  _ = refl
  own-unpinned {end}   _ = refl
  own-unpinned {pin _} ()

  tag-silent : ∀ k e → Silent (tag k e)
  tag-silent k e with inside r k
  ... | true  = held
  ... | false = own-silent e
    where
      own-silent : ∀ e → Silent (own e)
      own-silent (out _) = hush
      own-silent skip    = hush
      own-silent end     = hush
      own-silent (pin _) = held

  end-tag : ∀ {X : Set} k e → end ≡ tag k e → X
  end-tag k e eq with tag k e | tag-silent k e
  end-tag k e () | .skip | hush
  end-tag k e () | .(pin _) | held

  -- A tagged source row's pin lies at the connect, or where the source's does.
  pin-at : ∀ {y r′} k e → σ k e → k ⊑ y → pin r′ ≡ tag k e → W⁼ H p r′ × T (inside r′ y)
  pin-at {y} k e x ky eq with inside r k in ik
  pin-at {y} k e x ky refl | true = here , ⊑-inside (⊑-trans (pinned-under (subst T (sym ik) tt)) ky)
  pin-at {y} k (pin p′) x ky refl | false with InvAt.pinned Iσ x
  ... | w⁼ , i = inW (shrink⁼ w⁼) , ⊑-inside (⊑-trans (inside-⊑ p′ k i) ky)

  -- Why a source row shows: the body still runs, it is in the burst, or
  -- it is a pin whose connect subscribed while the body ran.
  data Why (k : Pos) : Ev A → Set where
    live : ∀ {e′} → Alive k → Why k e′
    brst : ∀ {e′} → T (inside r k) → Why k e′
    kpt  : ∀ {p′} → Alive p′ → Why k (pin p′)

  -- A connect row, its position free.
  data V (y : Pos) (e : Ev B) : Set where
    vb : β y e → V y e
    vs : ∀ {k e′} → σ k e′ → Why k e′ → y ≡ k ++ [ ix 0 ] → e ≡ tag k e′ → V y e

  view : ∀ {y e} → Truncate ConnT y e → V y e
  view (body x , _)       = vb x
  view (burst x i , _)    = vs x (brst i) refl (tag-in i)
  view (echo x a u o , _) = vs x (live a) refl (trans (own-unpinned u) (tag-out o))
  view (kept x a o _ , _) = vs x (kpt a) refl (tag-out o)

  -- A body row is not a source row's first child, nor a source row.
  shown-body : ∀ {y e k e′} → β y e → σ k e′ → y ≡ k ++ [ ix 0 ] → ⊥
  shown-body {k = k} b x refl with source-leads (sw x) (bw b) ([ ix 0 ] , refl)
  ... | h , e , (_ , σh) , kh , (ms , eq) with same-lead Iσ x (proj₁ σh) kh
  ...   | refl = diverge k [] ms (λ ()) (trans (++-identityʳ (k ++ [ ix 0 ])) eq)

  fu : ∀ {y e e′} → V y e → V y e′ → e ≡ e′
  fu (vb b)         (vb b′)        = InvAt.func Iβ b b′
  fu (vb b)         (vs x _ eq _)  = ⊥-elim (shown-body b x eq)
  fu (vs x _ eq _)  (vb b)         = ⊥-elim (shown-body b x eq)
  fu (vs {k} x _ eq e₁) (vs {k′} x′ _ eq′ e₂) with ∷ʳ-injectiveˡ k k′ (trans (sym eq) eq′)
  ... | refl with InvAt.func Iσ x x′
  ...   | refl = trans e₁ (sym e₂)

  fl : ∀ {y e l ys e′} → V y e → V (y ++ l ∷ ys) e′ → ⊥
  fl (vb b) (vb b′) = InvAt.flat Iβ b b′
  fl {y} {l = l} {ys} (vb b) (vs {k} x _ eq _) with ⊑-snoc k (l ∷ ys , sym eq)
  ... | inj₁ yk = body-leads (bw b) (sw x) yk
  ... | inj₂ e₂ = ext≢ y ys (trans eq (sym e₂))
  fl {l = l} {ys} (vs {k} x _ refl _) (vb b) with source-leads (sw x) (bw b) (ix 0 ∷ l ∷ ys , ++-assoc k [ ix 0 ] (l ∷ ys))
  ... | h , e , (_ , σh) , kh , (ms , eq) with same-lead Iσ x (proj₁ σh) kh
  ...   | refl = diverge k (l ∷ ys) ms (λ ()) eq
  fl {l = l} {ys} (vs {k} x _ refl _) (vs {k′} x′ _ eq _) with ⊑-snoc k′ (l ∷ ys , sym eq)
  ... | inj₁ le = flat-under Iσ x x′ le
  ... | inj₂ e₂ = ext≢ (k ++ [ ix 0 ]) ys (trans eq (sym e₂))

  between : ∀ {b c k} → b ≺ c → c ≺ k → b ⊑ k → b ⊑ c
  between {b} {c} bc ck (zs , refl) = <ᵖ-between b c zs (Equivalence.to T-≡ bc) (Equivalence.to T-≡ ck)

  bu : ∀ {c y e} → V c end → V y e → c ≺ y → Σ Pos λ w → W⁼ H p w × T (inside w c) × T (inside w y)
  bu (vs {k} {e′} _ _ _ eq) _ _ = end-tag k e′ eq
  bu (vb ce) (vb b) cy with InvAt.burst Iβ ce b cy
  ... | w , w⁼ , i = w , inW (narrow⁼ σ-wp w⁼) , i
  bu {c} (vb ce) (vs {k} x (live a) refl _) cy with <ᵖ-between k c [ ix 0 ] (Equivalence.to T-≡ (a ce)) (Equivalence.to T-≡ cy)
  ... | zs , refl with source-leads (sw x) (bw ce) (zs , refl)
  ...   | h , e , (_ , σh) , kh , (ms , eq) with same-lead Iσ x (proj₁ σh) kh
  ...     | refl = ⊥-elim (≺-absurd {k ++ zs} {k ++ [ ix 0 ]} cy
                     (subst ((k ++ [ ix 0 ]) ≺_) (sym (trans eq (++-assoc k [ sub e ] ms)))
                       (Equivalence.from T-≡ (<ᵖ-part k {ix 0} {sub e} [] ms refl))))
  bu {c} (vb ce) (vs {k} x (brst i) refl _) cy = p , here , ⊑-inside (between pc cy py) , ⊑-inside py
    where
      py = ⊑-trans (pinned-under i) (⊑-snoc⁺ k)
      pc : p ≺ c
      pc = ≺-≼-≺ {p} {p₀} {c} (≺-ext p []) (anc-≼ (world-anc⁼ (bw ce)) (InvAt.real Iβ ce))
  bu {c} (vb ce) (vs {k} x (kpt {p′} a′) refl _) cy with InvAt.pinned Iσ x
  ... | w⁼ , i = p′ , inW (shrink⁼ w⁼) , ⊑-inside (between (a′ ce) cy py) , ⊑-inside py
    where py = ⊑-trans (inside-⊑ p′ k i) (⊑-snoc⁺ k)

  qu : ∀ {c y e} → V c end → V y e → c ≺ y → Silent e
  qu (vs {k} {e′} _ _ _ eq) _ _ = end-tag k e′ eq
  qu (vb ce) (vb b) cy                = InvAt.quiet Iβ ce b cy
  qu (vb _) (vs {k} {e′} _ _ _ refl) _ = tag-silent k e′

  -- A pin, where it lies.
  pi : ∀ {y r′} → V y (pin r′) → W⁼ H p r′ × T (inside r′ y)
  pi (vb b) with InvAt.pinned Iβ b
  ... | w⁼ , i = inW (narrow⁼ σ-wp w⁼) , i
  pi (vs {k} {e′} x _ refl eq) = pin-at k e′ x (⊑-snoc⁺ k) eq

  -- UNDER A ROW'S CHILD LIES NO ROW: a body row's child is in the body's
  -- world, and a source row's in the source's.
  un : ∀ {q y w l e e′} → V q e → V y e′ → Plain l → W⁼ H (q ++ [ l ]) w → w ⊑ y → ⊥
  un (vb b) (vb b′) pl v le = InvAt.under Iβ b b′ pl (widen⁼ σ′ v) le
  un {q} {l = l} (vb b) (vs {k} x _ refl _) pl v le with ⊑-snoc k le
  ... | inj₁ le′ = body-leads (nest⁼ (inW (step (bw b) pl)) (widen⁼ σ′ v)) (sw x) le′
  ... | inj₂ e with w-up plain-ix (subst (W⁼ H (q ++ [ l ])) e v)
  ...   | inj₁ eq = body-leads (subst (W⁼ H₀ p₀) (∷ʳ-injectiveˡ q k eq) (bw b)) (sw x) (⊑-refl k)
  ...   | inj₂ v′ = body-leads (nest⁼ (inW (step (bw b) pl)) (widen⁼ σ′ v′)) (sw x) (⊑-refl k)
  un (vs {k} x _ refl _) (vb b) pl v le with source-leads (nest⁼ (inW (step (inW (step (sw x) plain-ix)) pl)) v) (bw b) le
  ... | h , _ , (_ , σh) , wh , _ = InvAt.under Iσ x (proj₁ σh) plain-ix (nest⁼ (inW (step here pl)) v) wh
  un {l = l} (vs {k} x _ refl _) (vs {k′} x′ _ refl _) pl v le with ⊑-snoc k′ le
  ... | inj₁ le′ = InvAt.under Iσ x x′ plain-ix (nest⁼ (inW (step here pl)) v) le′
  ... | inj₂ e with w-up plain-ix (subst (W⁼ H ((k ++ [ ix 0 ]) ++ [ l ])) e v)
  ...   | inj₁ eq = InvAt.flat Iσ x (subst (λ z → σ z _) (sym (∷ʳ-injectiveˡ (k ++ [ ix 0 ]) k′ eq)) x′)
  ...   | inj₂ v′ = InvAt.under Iσ x x′ plain-ix (nest⁼ (inW (step here pl)) v′) (⊑-refl k′)

  -- The connect's reading at an admissible `p`.
  connect-at : InvAt H p (Truncate ConnT)
  connect-at = record
    { world = wo
    ; real  = re
    ; func  = λ x x′ → fu (view x) (view x′)
    ; flat  = λ x x′ → fl (view x) (view x′)
    ; burst = λ c y cy → bu (view c) (view y) cy
    ; under = λ x y → un (view x) (view y)
    ; quiet = λ c y cy → qu (view c) (view y) cy
    ; pinned = λ x → pi (view x)
    }
    where
      wo : ∀ {y e} → Truncate ConnT y e → W H p y
      wo (body x , _)       = narrow σ-wp (InvAt.world Iβ x)
      wo (burst x _ , _)    = step (inW (shrink (InvAt.world Iσ x))) plain-ix
      wo (echo x _ _ _ , _) = step (inW (shrink (InvAt.world Iσ x))) plain-ix
      wo (kept x _ _ _ , _) = step (inW (shrink (InvAt.world Iσ x))) plain-ix

      re : ∀ {y e} → Truncate ConnT y e → Real y
      re (body x , _)       = InvAt.real Iβ x
      re (burst {k} x _ , _)    = real-snoc k {ix 0} plain-ix (InvAt.real Iσ x)
      re (echo {k} x _ _ _ , _) = real-snoc k {ix 0} plain-ix (InvAt.real Iσ x)
      re (kept {k} x _ _ _ , _) = real-snoc k {ix 0} plain-ix (InvAt.real Iσ x)

connect-inv : ∀ {A B H} {s : Den A} {F : Den A → Den B} → InvD H s → (∀ {t} → Lawful t → InvD (H ⊕ t) (F (hot t))) → InvD H (Op.connect s F)
connect-inv {s = s} {F} Is IF p ok = connect-at {s = s} {F = F} Is IF p ok
