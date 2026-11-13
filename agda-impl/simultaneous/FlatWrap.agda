{-# OPTIONS --guardedness #-}

-- THE FLATMAP CARRIES ITS ROWS from its outer's carry and its lanes': the
-- elaborated flatMap is a connect over the elaborated outer, so each lane
-- row rides the elaborated body's carrier, and each outer row its
-- carrier's echo — a value's silent first child one label under it, any
-- other row at it — or, in the subscribe burst or carried late, the
-- burst or kept row one label under the carrier.  A row is carried only
-- where the flatMap reaches it: few rows of it before it.
module simultaneous.FlatWrap where

open import Data.Bool using (T; not)
open import Data.Bool.Properties using (T?)
open import Function using (mk⇔)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (decidable-stable)
open import Data.List.Properties using (∷-injectiveˡ)

open import denotation.Position using (Pos; ix; sub; _⊕_; inside; _≟ᵖ_; root)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Few; Truncate; Proper; Den; hot; _≺_; Ended;
  module Joining; module Connect)
open import denotation.Laws.Modulus using (≼-or-≻; ≺-irrefl; ≺-ext; ≺-absurd; ≺-≼-≺; ticks)
open import denotation.Laws.Shows using (few-reach)
open import denotation.Laws.Worlds using (InvD; InvAt; Lawful; Ok; W; W⁼; _∪ʰ_; _⊑_; ⊑-refl; ⊑-trans; ⊑-snoc; ⊕-identityʳ; ⊕-injˡ; ⊕-assoc;
  ⊕-cancelˡ; ext≢; ⊑-inside; inside-⊑; ⊑-≼; ⊑-snoc⁺; inW; nest; step; plain-ix)
open import denotation.Laws.Truth.Joining using (Slots)
import denotation.Laws.JoinInv as JI
import denotation.Laws.Truth.Connect.Cuts as Cuts
open import denotation.Laws.Count using (⊑?)
open import Relation.Nullary using (yes; no)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (Live; Shown; Match; Every; One; Reads)
open import simultaneous.Listing using (Listed)
open import simultaneous.CarryBase using (InOrder; Targeted; PMap; _∪ᴹ_; _⊆ᴹ_; Emb; CarryAt; Narrow; PinList; IntoAt; Near; Home; Whole; From;
  unp-pin; apart; Ahead; emb-at; emb-pairs; instant-⊕)
open import simultaneous.CarryLeaves using (module OneAt; ix-sub)
open import simultaneous.CarryConnect using (Two; emb-two; emb-two′; one-label; tick-read; one-sh)
open import simultaneous.Carry using (PastOver; Anchor; anchor-grow; anchor-up)
open import simultaneous.ReadRows using (up; up-⊕)
open import simultaneous.ConnLists using (trunc-few; nin)
open import denotation.Events using (Timeline; fresh)
open import simultaneous.SObs using (lone; module Elaborate)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

module FlatCarry {A B : Set} {HP HE LP : Pos → Set} (p p′ : Pos) (okP : Ok HP p) (okE : Ok HE p′)
                 {o : EmissionSet A} (Io : InvAt HP p o) (g : A → Den B) (Ig : ∀ a → InvD HP (g a))
                 (Ln : Pos → A → EmissionSet B) (Runs : Pos → Set) (Cut : Pos → Pos → Set) (Hand : Pos → Set) (SL : Slots HP g o Ln)
                 {sE : Den (IE A)} {FE : Den (IE A) → Den (IE B)}
                 (IsE : InvD HE sE) (IFE : ∀ {t} → Lawful t → InvD (HE ∪ʰ t) (FE (hot t)))
                 (M_s : PMap) (c_s : CarryAt valuesOf M_s HP HE LP o (Connect.σ sE FE p′) p (p′ ⊕ [ ix 1 ])) where
  module J  = Joining Ln o (λ _ _ → ⊥) (Ended o) Runs Cut Hand
  module CE = Connect sE FE p′
  module S′ = CarryAt c_s
  module SE = Cuts.Side {s = sE} {F = FE} IsE IFE p′ okE
  module JK = JI.Join okP g Ig Io

  t : EmissionSet B
  t = Truncate J.JoinT

  u : EmissionSet (IE B)
  u = Truncate (Connect.ConnT sE FE p′)

  r′ : Pos
  r′ = p′ ⊕ [ ix 1 ]

  -- WHERE AN OUTER ROW SHOWS in the flatMap: a value silent one label
  -- under it, any other row at it, an end only while a lane runs.
  data Shows (q : Pos) : Ev A → Pos → Ev B → Set where
    s-val  : ∀ {a k} → k ≡ q ⊕ [ ix 0 ] → Shows q (out a) k skip
    s-skip : ∀ {k} → k ≡ q → Shows q skip k skip
    s-pin  : ∀ {r k} → k ≡ q → Shows q (pin r) k (pin r)
    s-pass : ∀ {k} → k ≡ q → ¬ J.Done q → Shows q end k skip

  shows-row : ∀ {k₀ e₀ k e} → o k₀ e₀ → Shows k₀ e₀ k e → J.JoinT k e
  shows-row x (s-val refl)    = J.val x
  shows-row x (s-skip refl)   = J.step x
  shows-row x (s-pin refl)    = J.opin x
  shows-row x (s-pass refl n) = J.opass x n

  shown-unp : ∀ {k₀ e₀ k e} → Shows k₀ e₀ k e → Unpinned e₀ → Unpinned e
  shown-unp (s-val _)    _ = tt
  shown-unp (s-skip _)   _ = tt
  shown-unp (s-pass _ _) _ = tt

  -- A JOINED ROW OF THE LANES, not the outer's.
  Bod : ∀ {k e} → J.JoinT k e → Set
  Bod (J.val _)     = ⊥
  Bod (J.step _)    = ⊥
  Bod (J.opin _)    = ⊥
  Bod (J.opass _ _) = ⊥
  Bod _             = ⊤

  tB : EmissionSet B
  tB k e = Σ (t k e) λ x → Bod (proj₁ x)

  -- Every row of the flatMap is a lane's or shows an outer row.
  classify : ∀ {k e} (x : t k e) → tB k e ⊎ Σ Pos λ k₀ → Σ (Ev A) λ e₀ → o k₀ e₀ × Shows k₀ e₀ k e
  classify (J.val x , _)                = inj₂ (_ , _ , x , s-val refl)
  classify (J.step x , _)               = inj₂ (_ , _ , x , s-skip refl)
  classify (J.opin x , _)               = inj₂ (_ , _ , x , s-pin refl)
  classify (J.opass x n , _)            = inj₂ (_ , _ , x , s-pass refl n)
  classify r@(J.oend _ _ , _)           = inj₁ (r , tt)
  classify r@(J.lane _ _ _ _ _ , _)     = inj₁ (r , tt)
  classify r@(J.lend _ _ _ _ _ _ , _)   = inj₁ (r , tt)
  classify r@(J.lpass _ _ _ _ _ _ , _)  = inj₁ (r , tt)
  classify r@(J.hand _ _ _ _ _ , _)     = inj₁ (r , tt)
  classify r@(J.left _ _ _ _ _ , _)     = inj₁ (r , tt)
  classify (J.run () _ , _)
  classify (J.rend () _ _ , _)
  classify (J.rpass () _ _ , _)
  classify (J.rhand () _ , _)

  -- A lane row lies in the world of some value's second child.
  lane-w : ∀ {q a k e} → o q (out a) → Ln q a k e → Σ Pos λ ρ → Σ A λ b → o ρ (out b) × W HP (ρ ⊕ [ ix 1 ]) k
  lane-w x l with Slots.slot SL l
  ... | s , sl , af with Slots.seat SL x sl
  ...   | ρ , b , xρ , _ , w⁼ = ρ , b , xρ , nest w⁼ (InvAt.world (Ig _ s (Slots.okS SL x sl)) (proj₁ af))

  -- No outer row, nor a value's first child, lies in a lane's world.
  off-lane : ∀ {k₀ e₀ k e ρ b} → o k₀ e₀ → Shows k₀ e₀ k e → o ρ (out b) → W HP (ρ ⊕ [ ix 1 ]) k → ⊥
  off-lane x (s-val refl)    xρ w = JK.val-lane x xρ w
  off-lane x (s-skip refl)   xρ w = JK.o-lane x xρ w
  off-lane x (s-pin refl)    xρ w = JK.o-lane x xρ w
  off-lane x (s-pass refl _) xρ w = JK.o-lane x xρ w

  private
    -- An outer row showing where the outer ends, the joiner done there.
    end-apart : ∀ {k₀ e₀ k e} → o k₀ e₀ → Shows k₀ e₀ k e → o k end → J.Done k → ⊥
    end-apart x (s-val refl) xc _ = InvAt.flat Io x xc
    end-apart x (s-skip refl) xc _ with InvAt.func Io x xc
    ... | ()
    end-apart x (s-pin refl) xc _ with InvAt.func Io x xc
    ... | ()
    end-apart x (s-pass refl n) _ dn = n dn

  -- A LANE ROW is the outer's end where the joiner is done, or lies in a
  -- value's second child's world.
  lane-at : ∀ {k e} → tB k e → (o k end × J.Done k) ⊎ Σ Pos λ ρ → Σ A λ b → o ρ (out b) × W HP (ρ ⊕ [ ix 1 ]) k
  lane-at ((J.oend xc dn , _) , _)         = inj₁ (xc , dn)
  lane-at ((J.lane xq _ l _ _ , _) , _)    = inj₂ (lane-w xq l)
  lane-at ((J.lend xq _ l _ _ _ , _) , _)  = inj₂ (lane-w xq l)
  lane-at ((J.lpass xq _ l _ _ _ , _) , _) = inj₂ (lane-w xq l)
  lane-at ((J.left xq _ l _ _ , _) , _)    = inj₂ (lane-w xq l)
  lane-at ((J.hand xq _ l _ _ , _) , _)    = let (ρ , b , xρ , w) = lane-w xq l in inj₂ (ρ , b , xρ , step (inW w) plain-ix)
  lane-at ((J.run () _ , _) , _)
  lane-at ((J.rend () _ _ , _) , _)
  lane-at ((J.rpass () _ _ , _) , _)
  lane-at ((J.rhand () _ , _) , _)
  lane-at ((J.val _ , _) , ())
  lane-at ((J.step _ , _) , ())
  lane-at ((J.opin _ , _) , ())
  lane-at ((J.opass _ _ , _) , ())

  -- NO LANE ROW SHOWS WHERE AN OUTER ROW DOES: a lane's lie in a value's
  -- second child's world, which holds no outer row.
  flat-apart : ∀ {k₀ e₀ k e e′} → o k₀ e₀ → Shows k₀ e₀ k e → tB k e′ → ⊥
  flat-apart x s b with lane-at b
  ... | inj₁ (xc , dn)        = end-apart x s xc dn
  ... | inj₂ (_ , _ , xρ , w) = off-lane x s xρ w

  -- One outer row shows at a position.
  shows-at : ∀ {k₀ k₁ e₀ e₁ k e e′} → o k₀ e₀ → Shows k₀ e₀ k e → o k₁ e₁ → Shows k₁ e₁ k e′ → k₀ ≡ k₁
  shows-at {k₀} {k₁} _ (s-val e) _ (s-val e′) = ⊕-injˡ k₀ k₁ (trans (sym e) e′)
  shows-at x (s-val refl) x′ (s-skip e′)   = ⊥-elim (InvAt.flat Io x (subst (λ z → o z _) (sym e′) x′))
  shows-at x (s-val refl) x′ (s-pin e′)    = ⊥-elim (InvAt.flat Io x (subst (λ z → o z _) (sym e′) x′))
  shows-at x (s-val refl) x′ (s-pass e′ _) = ⊥-elim (InvAt.flat Io x (subst (λ z → o z _) (sym e′) x′))
  shows-at x (s-skip refl)   x′ (s-val refl) = ⊥-elim (InvAt.flat Io x′ x)
  shows-at x (s-pin refl)    x′ (s-val refl) = ⊥-elim (InvAt.flat Io x′ x)
  shows-at x (s-pass refl _) x′ (s-val refl) = ⊥-elim (InvAt.flat Io x′ x)
  shows-at _ (s-skip e)   _ (s-skip e′)   = trans (sym e) e′
  shows-at _ (s-skip e)   _ (s-pin e′)    = trans (sym e) e′
  shows-at _ (s-skip e)   _ (s-pass e′ _) = trans (sym e) e′
  shows-at _ (s-pin e)    _ (s-skip e′)   = trans (sym e) e′
  shows-at _ (s-pin e)    _ (s-pin e′)    = trans (sym e) e′
  shows-at _ (s-pin e)    _ (s-pass e′ _) = trans (sym e) e′
  shows-at _ (s-pass e _) _ (s-skip e′)   = trans (sym e) e′
  shows-at _ (s-pass e _) _ (s-pin e′)    = trans (sym e) e′
  shows-at _ (s-pass e _) _ (s-pass e′ _) = trans (sym e) e′

  -- An unpinned outer row lies before the outer's end.
  src-live : ∀ {k e} → o k e → Unpinned e → Live o k
  src-live {k} x un {c} y with ≼-or-≻ k c
  ... | inj₁ kc = kc
  ... | inj₂ ck with InvAt.quiet Io y x ck
  ...   | q , refl , _ = ⊥-elim (unp-pin {A} {q} un)

  -- EACH VALUE'S ECHO, paired one label under its carrier.
  Echo : PMap
  Echo x y = Σ Pos λ k₀ → Σ Pos λ l₀ → Σ A (λ a → o k₀ (out a)) × S′.Img k₀ l₀ × x ≡ k₀ ⊕ [ ix 0 ] × y ≡ l₀ ⊕ [ ix 0 ]

  -- An echo lies one label under a value in the world, past the outer's
  -- pair for the value.
  echo-at : ∀ {x y} → Echo x y → Σ Pos λ k₀ → Σ Pos λ y₀ → M_s k₀ y₀ × y₀ ⊑ y × x ≡ k₀ ⊕ [ ix 0 ] × W HP p k₀
  echo-at (k₀ , l₀ , (_ , x₀) , i₀ , refl , refl) =
    let (y₀ , m₀ , p₀) = S′.ext i₀ in k₀ , y₀ , m₀ , ⊑-trans p₀ ([ ix 0 ] , refl) , refl , InvAt.world Io x₀

  echo-world : ∀ {x y} → Echo x y → W⁼ HP p x
  echo-world (_ , _ , (_ , x₀) , _ , refl , _) = inW (step (inW (InvAt.world Io x₀)) plain-ix)

  -- No outer row lies under another.
  o-flat : ∀ {k h e e′} → o k e → o h e′ → k ⊑ h → k ≡ h
  o-flat {k} x x′ ([] , refl) = sym (⊕-identityʳ k)
  o-flat x x′ (_ ∷ _ , refl) = ⊥-elim (InvAt.flat Io x x′)

  private
    at-bare : ∀ {k e k₀ a} → o k e → (∀ {b} → e ≡ out b → ⊥) → o k₀ (out a) → k ⊑ (k₀ ⊕ [ ix 0 ]) → k₀ ⊕ [ ix 0 ] ≡ k
    at-bare {k₀ = k₀} x nv x₀ kx with ⊑-snoc k₀ kx
    ... | inj₂ e = sym e
    ... | inj₁ kk with o-flat x x₀ kk
    ...   | refl = ⊥-elim (nv (InvAt.func Io x x₀))

    shown-bare : ∀ {k₁ e₁ k e k₀ a} → o k₁ e₁ → Shows k₁ e₁ k e → o k₀ (out a) → k ⊑ (k₀ ⊕ [ ix 0 ]) → k₀ ⊕ [ ix 0 ] ≡ k
    shown-bare {k₁} {k₀ = k₀} x₁ (s-val refl) x₀ kx with ⊑-snoc k₀ kx
    ... | inj₂ e = sym e
    ... | inj₁ kk with o-flat x₁ x₀ (⊑-trans (⊑-snoc⁺ k₁) kk)
    ...   | refl = ⊥-elim (⊑-≼ kk (≺-ext k₁ []))
    shown-bare x₁ (s-skip refl)   x₀ kx = at-bare x₁ (λ ()) x₀ kx
    shown-bare x₁ (s-pin refl)    x₀ kx = at-bare x₁ (λ ()) x₀ kx
    shown-bare x₁ (s-pass refl _) x₀ kx = at-bare x₁ (λ ()) x₀ kx

    lane-bare : ∀ {ρ b k k₀ a} → o ρ (out b) → W HP (ρ ⊕ [ ix 1 ]) k → o k₀ (out a) → k ⊑ (k₀ ⊕ [ ix 0 ]) → k₀ ⊕ [ ix 0 ] ≡ k
    lane-bare {k₀ = k₀} xρ w x₀ kx with ⊑-snoc k₀ kx
    ... | inj₂ e  = sym e
    ... | inj₁ kk = ⊥-elim (InvAt.under Io xρ x₀ plain-ix (inW w) kk)

  -- NO ROW LIES STRICTLY UNDER AN ECHO: an outer row's are outer rows,
  -- flat; a lane's lie in another value's lane world, which holds no
  -- outer row above it.
  echo-bare : ∀ {k e x y} → t k e → Echo x y → k ⊑ x → x ≡ k
  echo-bare tk (_ , _ , (_ , x₀) , _ , refl , _) kx with classify tk
  ... | inj₂ (_ , _ , x₁ , s) = shown-bare x₁ s x₀ kx
  ... | inj₁ b with lane-at b
  ...   | inj₁ (xc , _)         = at-bare xc (λ ()) x₀ kx
  ...   | inj₂ (_ , _ , xρ , w) = lane-bare xρ w x₀ kx

  -- WHAT A LANE MAP PAIRS STRICTLY UNDER A VALUE lies under its second
  -- child, imaged under a reading of its carrier.
  LaneHere : PMap → Set
  LaneHere N = ∀ {k₀ a l₀ x y} → o k₀ (out a) → S′.Img k₀ l₀ → N x y → k₀ ⊑ x → (x ≡ k₀ → ⊥)
             → (k₀ ⊕ [ ix 1 ]) ⊑ x × Σ Pos λ e → (l₀ ⊕ [ sub e ]) ⊑ y

  -- THE ECHOES EMBED with such a map: two echoes one label under their
  -- values' carriers; an echo before what is paired under its value's
  -- second child, on both sides.
  module Paired (M_b : PMap) (ms_b : M_s ⊆ᴹ M_b) (hm_b : Emb M_b) (lh : LaneHere M_b) where
    private
      ix-one : ix 1 ≡ ix 0 → ⊥
      ix-one ()

      at-s : ∀ {k₀ l₀} → S′.Img k₀ l₀ → Σ Pos λ y₀ → M_b k₀ y₀ × y₀ ⊑ l₀
      at-s i = let (y₀ , m , yl) = S′.ext i in y₀ , ms_b m , yl

      echo-echo : ∀ {x y x′ y′} → Echo x y → Echo x′ y′ → Σ PMap λ K → Emb K × K x y × K x′ y′
      echo-echo (k₀ , l₀ , (_ , tk₀) , i₀ , refl , refl) (k₁ , l₁ , (_ , tk₁) , i₁ , refl , refl) with k₀ ≟ᵖ k₁
      ... | yes refl with S′.img-fun i₀ i₁
      ...   | refl = OneAt.N k₀ l₀ , OneAt.embN k₀ l₀ , (ix 0 , plain-ix , refl , refl) , (ix 0 , plain-ix , refl , refl)
      echo-echo (k₀ , l₀ , (_ , tk₀) , i₀ , refl , refl) (k₁ , l₁ , (_ , tk₁) , i₁ , refl , refl) | no ne with at-s i₀ | at-s i₁
      ... | y₀ , m₀ , p₀ | y₁ , m₁ , p₁ =
        (Two k₀ y₀ k₁ y₁ ∪ᴹ OneAt.N k₀ l₀) ∪ᴹ OneAt.N k₁ l₁ , E₁ , inj₁ (inj₂ (ix 0 , plain-ix , refl , refl)) , inj₂ (ix 0 , plain-ix , refl , refl)
        where
          at₀ : ∀ {x y} → Two k₀ y₀ k₁ y₁ x y → k₀ ⊑ x → x ≡ k₀
          at₀ (inj₁ (refl , _)) _  = refl
          at₀ (inj₂ (refl , _)) kx = ⊥-elim (ne (o-flat tk₀ tk₁ kx))

          E₀ : Emb (Two k₀ y₀ k₁ y₁ ∪ᴹ OneAt.N k₀ l₀)
          E₀ = emb-at (emb-two hm_b m₀ m₁) at₀ (inj₁ (refl , refl)) p₀ (OneAt.embN k₀ l₀) (λ {x} {y} q → one-sh {k₀} {l₀} {x} {y} q)

          at₁ : ∀ {x y} → (Two k₀ y₀ k₁ y₁ ∪ᴹ OneAt.N k₀ l₀) x y → k₁ ⊑ x → x ≡ k₁
          at₁ (inj₁ (inj₁ (refl , _))) kx = ⊥-elim (ne (sym (o-flat tk₁ tk₀ kx)))
          at₁ (inj₁ (inj₂ (refl , _))) _  = refl
          at₁ (inj₂ (a , _ , refl , _)) kx with ⊑-snoc k₀ kx
          ... | inj₁ kk = ⊥-elim (ne (sym (o-flat tk₁ tk₀ kk)))
          ... | inj₂ e  = ⊥-elim (ne (o-flat tk₀ tk₁ (subst (k₀ ⊑_) (sym e) (⊑-snoc⁺ k₀))))

          E₁ : Emb ((Two k₀ y₀ k₁ y₁ ∪ᴹ OneAt.N k₀ l₀) ∪ᴹ OneAt.N k₁ l₁)
          E₁ = emb-at E₀ at₁ (inj₁ (inj₂ (refl , refl))) p₁ (OneAt.embN k₁ l₁) (λ {x} {y} q → one-sh {k₁} {l₁} {x} {y} q)

      echo-under : ∀ {k₀ l₀ x′ y′} → S′.Img k₀ l₀ → M_b x′ y′ → (k₀ ⊑ x′ → x′ ≡ k₀)
                 → Σ PMap λ K → Emb K × K (k₀ ⊕ [ ix 0 ]) (l₀ ⊕ [ ix 0 ]) × K x′ y′
      echo-under {k₀} {l₀} {x′ = x′} {y′} i₀ m kx′ with at-s i₀
      ... | y₀ , m₀ , p₀ =
        Two k₀ y₀ x′ y′ ∪ᴹ OneAt.N k₀ l₀ , emb-at (emb-two hm_b m₀ m) at (inj₁ (refl , refl)) p₀ (OneAt.embN k₀ l₀) (λ {x} {y} q → one-sh {k₀} {l₀} {x} {y} q)
          , inj₂ (ix 0 , plain-ix , refl , refl) , inj₁ (inj₂ (refl , refl))
        where
          at : ∀ {x y} → Two k₀ y₀ x′ y′ x y → k₀ ⊑ x → x ≡ k₀
          at (inj₁ (refl , _)) _  = refl
          at (inj₂ (refl , _)) kx = kx′ kx

      echo-read : ∀ {k₀ l₀ a x′ y′} → o k₀ (out a) → S′.Img k₀ l₀ → M_b x′ y′ → k₀ ⊑ x′ → (x′ ≡ k₀ → ⊥)
                → Emb (Two (k₀ ⊕ [ ix 0 ]) (l₀ ⊕ [ ix 0 ]) x′ y′)
      echo-read {k₀} {l₀} x₀ i₀ m kx ne with lh x₀ i₀ m kx ne
      ... | (zs , refl) , e′ , (ws , refl) =
        emb-two′ (λ q → ix-one (one-label k₀ (zs , refl) (subst ((k₀ ⊕ [ ix 0 ]) ⊑_) q (⊑-refl _))))
                 (λ _ → ≺-≼-≺ {l₀ ⊕ [ ix 0 ]} {l₀ ⊕ [ sub e′ ]} {(l₀ ⊕ [ sub e′ ]) ⊕ ws} (ix-sub l₀ e′) (⊑-≼ {l₀ ⊕ [ sub e′ ]} (ws , refl)))
                 (λ h → ⊥-elim (≺-absurd {(k₀ ⊕ [ ix 1 ]) ⊕ zs} {k₀ ⊕ [ ix 0 ]} h
                          (≺-≼-≺ {k₀ ⊕ [ ix 0 ]} {k₀ ⊕ [ ix 1 ]} {(k₀ ⊕ [ ix 1 ]) ⊕ zs} (ticks k₀ 0) (⊑-≼ {k₀ ⊕ [ ix 1 ]} (zs , refl)))))
                 (λ h → ⊥-elim (tick-read l₀ (ws , refl) h))
                 (λ h → ⊥-elim (tick-read l₀ (⊑-trans (ws , refl) h) (⊑-refl _)))
                 (mk⇔ (λ _ → trans (instant-⊕ k₀ [ ix 0 ]) (sym (trans (instant-⊕ (k₀ ⊕ [ ix 1 ]) zs) (instant-⊕ k₀ [ ix 1 ]))))
                      (λ _ → trans (instant-⊕ l₀ [ ix 0 ]) (sym (trans (instant-⊕ (l₀ ⊕ [ sub e′ ]) ws) (instant-⊕ l₀ [ sub e′ ])))))

      echo-m : ∀ {x y x′ y′} → Echo x y → M_b x′ y′ → Σ PMap λ K → Emb K × K x y × K x′ y′
      echo-m {x′ = x′} (k₀ , l₀ , (_ , x₀) , i₀ , refl , refl) m with x′ ≟ᵖ k₀
      ... | yes e = echo-under i₀ m (λ _ → e)
      ... | no ne with T? (inside k₀ x′)
      ...   | no nk  = echo-under i₀ m (λ kx → ⊥-elim (nk (⊑-inside kx)))
      ...   | yes ik = _ , echo-read x₀ i₀ m (inside-⊑ k₀ x′ ik) ne , inj₁ (refl , refl) , inj₂ (refl , refl)

      swap : ∀ {x y x′ y′} → (Σ PMap λ K → Emb K × K x y × K x′ y′) → Σ PMap λ K → Emb K × K x′ y′ × K x y
      swap (K , E , k , k′) = K , E , k′ , k

      pair : ∀ {x y x′ y′} → (M_b ∪ᴹ Echo) x y → (M_b ∪ᴹ Echo) x′ y′ → Σ PMap λ K → Emb K × K x y × K x′ y′
      pair (inj₁ m) (inj₁ m′) = M_b , hm_b , m , m′
      pair (inj₂ e) (inj₂ e′) = echo-echo e e′
      pair (inj₂ e) (inj₁ m)  = echo-m e m
      pair (inj₁ m) (inj₂ e)  = swap (echo-m e m)

    emb′ : Emb (M_b ∪ᴹ Echo)
    emb′ = emb-pairs pair

  module Body (M_b : PMap) (ms_b : M_s ⊆ᴹ M_b) (emb′ : Emb (M_b ∪ᴹ Echo))
              (c_b : CarryAt valuesOf M_b HP (HE ∪ʰ Proper CE.σ) (λ q → Listed o q × LP q) tB CE.β p (p′ ⊕ [ ix 0 ]))
              (past-s : PastOver c_s M_b)
              (nest-v : ∀ {k l e₀ h L a σ} → CarryAt.PB c_b k l → tB k e₀ → (Unpinned e₀ → Live tB k) → Σ A (λ b → o h (out b)) → S′.Img h L
                      → k ≡ h ⊕ (a ∷ σ) → Anchor M_b k l h a) where
    module B′ = CarryAt c_b

    M′ : PMap
    M′ = M_b ∪ᴹ Echo

    -- A lane row the flatMap reaches, on the body's carrier.
    BodyImg : Pos → Pos → Set
    BodyImg k l = B′.Img k l × Few J.JoinT k

    -- An unpinned outer row the flatMap reaches, past the subscribe
    -- burst, on its carrier's echo.
    SrcImg : Pos → Pos → Set
    SrcImg k l = Σ Pos λ k₀ → Σ Pos λ l₀ → Σ (Ev A) λ e₀ → Σ (Ev B) λ e → (o k₀ e₀ × Unpinned e₀ × Shows k₀ e₀ k e)
               × S′.Img k₀ l₀ × T (not (inside r′ l₀)) × Few J.JoinT k × l ≡ l₀ ⊕ [ ix 0 ]

    FlatImg : Pos → Pos → Set
    FlatImg k l = BodyImg k l ⊎ SrcImg k l

    -- An outer row carried into its instant: one label under its
    -- carrier in the subscribe burst, or under its late carrier.
    SrcPB : Pos → Pos → Set
    SrcPB k l = Σ Pos λ k₀ → Σ Pos λ l₀ → Σ (Ev A) λ e₀ → Σ (Ev B) λ e → (o k₀ e₀ × Shows k₀ e₀ k e)
              × ((S′.Img k₀ l₀ × T (inside r′ l₀)) ⊎ S′.PB k₀ l₀) × l ≡ l₀ ⊕ [ ix 0 ] × Σ (Ev (IE A)) (CE.σ l₀)

    PB′ : Pos → Pos → Set
    PB′ k l = (B′.PB k l × Σ (Ev B) (tB k) × Σ (Ev (IE B)) (CE.β l)) ⊎ SrcPB k l

    -- The pair an outer row's image is under: a value's echo, any other
    -- row's own pair.
    src-pair : ∀ {k l} → SrcImg k l → Σ Pos λ y → M′ k y × y ⊑ l
    src-pair (k₀ , l₀ , _ , _ , (x , _ , s-val refl) , i , _ , _ , refl) = l₀ ⊕ [ ix 0 ] , inj₂ (k₀ , l₀ , (_ , x) , i , refl , refl) , ⊑-refl _
    src-pair (k₀ , l₀ , _ , _ , (x , _ , s-skip refl) , i , _ , _ , refl) =
      let (y , m , yl) = S′.ext i in y , inj₁ (ms_b m) , ⊑-trans yl ([ ix 0 ] , refl)
    src-pair (k₀ , l₀ , _ , _ , (x , _ , s-pass refl _) , i , _ , _ , refl) =
      let (y , m , yl) = S′.ext i in y , inj₁ (ms_b m) , ⊑-trans yl ([ ix 0 ] , refl)

    ext′ : ∀ {k l} → FlatImg k l → Σ Pos λ y → M′ k y × y ⊑ l
    ext′ (inj₁ (i , _)) with B′.ext i
    ... | y , m , yl = y , inj₁ m , yl
    ext′ (inj₂ si) = src-pair si

    few′ : ∀ {k l} → FlatImg k l → Few t k
    few′ (inj₁ (_ , F))                              = trunc-few F
    few′ (inj₂ (_ , _ , _ , _ , _ , _ , _ , F , _)) = trunc-few F

    img-row′ : ∀ {k l} → FlatImg k l → ¬ ¬ Σ (Ev B) λ e → t k e × Unpinned e
    img-row′ (inj₁ (i , _)) n = B′.img-row i λ { (e , b , un) → n (e , proj₁ b , un) }
    img-row′ (inj₂ (_ , _ , _ , e , (x , un , s) , _ , _ , F , _)) n = n (e , (shows-row x s , few-reach {e = e} F) , shown-unp s un)

    img-fun′ : ∀ {k a b} → FlatImg k a → FlatImg k b → a ≡ b
    img-fun′ (inj₁ (i , _)) (inj₁ (i′ , _)) = B′.img-fun i i′
    img-fun′ {a = a} {b} (inj₁ (i , _)) (inj₂ (_ , _ , _ , _ , (x , _ , s) , _)) =
      decidable-stable (a ≟ᵖ b) λ _ → B′.img-row i λ { (_ , y , _) → flat-apart x s y }
    img-fun′ {a = a} {b} (inj₂ (_ , _ , _ , _ , (x , _ , s) , _)) (inj₁ (i , _)) =
      decidable-stable (a ≟ᵖ b) λ _ → B′.img-row i λ { (_ , y , _) → flat-apart x s y }
    img-fun′ (inj₂ (_ , _ , _ , _ , (x , _ , s) , i , _ , _ , refl)) (inj₂ (_ , _ , _ , _ , (x′ , _ , s′) , i′ , _ , _ , refl))
      with shows-at x s x′ s′
    ... | refl = cong (_⊕ [ ix 0 ]) (S′.img-fun i i′)

    pb-img′ : ∀ {k l l′} → PB′ k l → FlatImg k l′ → ⊥
    pb-img′ (inj₁ (pb , _)) (inj₁ (i , _)) = B′.pb-img pb i
    pb-img′ (inj₁ (_ , (_ , b) , _)) (inj₂ (_ , _ , _ , _ , (x , _ , s) , _)) = flat-apart x s b
    pb-img′ (inj₂ (_ , _ , _ , _ , (x , s) , _)) (inj₁ (i , _)) = B′.img-row i λ { (_ , y , _) → flat-apart x s y }
    pb-img′ (inj₂ (_ , _ , _ , _ , (x , s) , w , _)) (inj₂ (_ , _ , _ , _ , (x′ , _ , s′) , i′ , ni , _)) with shows-at x s x′ s′
    pb-img′ (inj₂ (_ , _ , _ , _ , _ , inj₁ (i , ins) , _)) (inj₂ (_ , l₁ , _ , _ , _ , i′ , ni , _)) | refl with S′.img-fun i i′
    ... | refl = nin {r′} {l₁} ni ins
    pb-img′ (inj₂ (_ , _ , _ , _ , _ , inj₂ pb , _)) (inj₂ (_ , _ , _ , _ , _ , i′ , _)) | refl = S′.pb-img pb i′

    private
      -- An outer row, or a value's first child, from its position.
      in-shown : ∀ {k k₀ e₀ e} (X : List Pos) → Shows k₀ e₀ k e → k₀ ∈ X → k ∈ L.map (_⊕ [ ix 0 ]) X ++ X
      in-shown X (s-val refl)    m = ∈-++⁺ˡ (∈-map⁺ (_⊕ [ ix 0 ]) m)
      in-shown X (s-skip refl)   m = ∈-++⁺ʳ (L.map (_⊕ [ ix 0 ]) X) m
      in-shown X (s-pin refl)    m = ∈-++⁺ʳ (L.map (_⊕ [ ix 0 ]) X) m
      in-shown X (s-pass refl _) m = ∈-++⁺ʳ (L.map (_⊕ [ ix 0 ]) X) m

    -- The rows a carrier carries: the body's, and the outer rows its
    -- echo shows.
    bk′ : Pos → List Pos
    bk′ l = B′.bk l ++ (L.map (_⊕ [ ix 0 ]) (S′.bk (up l)) ++ S′.bk (up l))

    in-bk′ : ∀ {k l} → FlatImg k l → k ∈ bk′ l
    in-bk′ (inj₁ (i , _)) = ∈-++⁺ˡ (B′.in-bk i)
    in-bk′ {l = l} (inj₂ (k₀ , l₀ , _ , _ , (_ , _ , s) , i , _ , _ , refl)) =
      ∈-++⁺ʳ (B′.bk l) (in-shown (S′.bk (up l)) s (subst (λ z → k₀ ∈ S′.bk z) (sym (up-⊕ l₀ (ix 0))) (S′.in-bk i)))

    -- An echo's late carriers: the outer's carried at the source row, or
    -- imaged there in the burst.
    from-src : ∀ {j e₁} → CE.σ j e₁ → Σ (List Pos) λ ks → ∀ {k} → PB′ k (j ⊕ [ ix 0 ]) → k ∈ ks
    from-src {j} y = L.map (_⊕ [ ix 0 ]) X ++ X , mem
      where
        X = S′.bk j ++ proj₁ (S′.pb-few y)

        mem : ∀ {k} → PB′ k (j ⊕ [ ix 0 ]) → k ∈ L.map (_⊕ [ ix 0 ]) X ++ X
        mem (inj₁ (_ , _ , (_ , bl))) = ⊥-elim (SE.img-body y bl (⊑-refl _))
        mem (inj₂ (k₀ , l₀ , _ , _ , (_ , s) , w , eq , _)) with ⊕-injˡ j l₀ eq
        ... | refl with w
        ...   | inj₁ (i , _) = in-shown X s (∈-++⁺ˡ (S′.in-bk i))
        ...   | inj₂ pb      = in-shown X s (∈-++⁺ʳ (S′.bk j) (proj₂ (S′.pb-few y) pb))

    pb-few′ : ∀ {l e} → u l e → Σ (List Pos) λ ks → ∀ {k} → PB′ k l → k ∈ ks
    pb-few′ {l} (CE.body b , _) with B′.pb-few b
    ... | ks , h = ks , λ { (inj₁ (pb , _)) → h pb
                          ; (inj₂ (_ , l₀ , _ , _ , _ , _ , eq , (_ , y))) → ⊥-elim (SE.img-body y b ([] , trans eq (sym (⊕-identityʳ (l₀ ⊕ [ ix 0 ]))))) }
    pb-few′ (CE.burst y _ , _)    = from-src y
    pb-few′ (CE.echo y _ _ _ , _) = from-src y
    pb-few′ (CE.kept y _ _ _ , _) = from-src y

    -- A lane row live in the flatMap is live in the lanes: the lanes'
    -- ends are the flatMap's.
    body-live : ∀ {k} → Live t k → Live tB k
    body-live lv tc = lv (proj₁ tc)

    live-u : ∀ {l} → Live CE.β l → Live u l
    live-u lv (CE.body b , _) = lv b

    postulate
      flat-src-live : ∀ {k l} → SrcImg k l → Live t k → Live u l

    live′ : ∀ {k l} → FlatImg k l → Live t k → Live u l
    live′ (inj₁ (i , _)) lv = live-u (B′.live i (body-live lv))
    live′ (inj₂ si)      lv = flat-src-live si lv

    -- One label under an outer row's late carrier, anchored where the
    -- outer's carry anchors it, nothing the outer's map pairs lying
    -- strictly under an outer row.
    anchor-down : ∀ {k₀ l₀ e₀ h a} → (∀ {k e x y} → o k e → M_s x y → k ⊑ x → x ≡ k) → o k₀ e₀
                → Anchor M_s k₀ l₀ h a → Anchor M′ (k₀ ⊕ [ ix 0 ]) (l₀ ⊕ [ ix 0 ]) h a
    anchor-down bs x₀ (x , y , m , yl , inj₁ (ax , xk)) = x , y , inj₁ (ms_b m) , ⊑-trans yl ([ ix 0 ] , refl) , inj₁ (ax , ⊑-trans xk ([ ix 0 ] , refl))
    anchor-down {k₀} bs x₀ (x , y , m , yl , inj₂ kx) = x , y , inj₁ (ms_b m) , ⊑-trans yl ([ ix 0 ] , refl) , inj₂ lt
      where
        lt : (k₀ ⊕ [ ix 0 ]) ≺ x
        lt with ⊑? k₀ x
        ... | yes kx′ = ⊥-elim (≺-irrefl {x} (subst (_≺ x) (sym (bs x₀ m kx′)) kx))
        ... | no nk   = subst ((k₀ ⊕ [ ix 0 ]) ≺_) (⊕-identityʳ x) (apart kx nk [ ix 0 ] [])

    -- A LATE CARRIER UNDER A HOT ROW IS ANCHORED: a lane row's by the
    -- lanes' anchor; an outer row's at its own pair in the burst, else by
    -- the outer's anchor, one label down for a value.  No outer row lies
    -- at a hot row: it is a world point.
    nest′ : ∀ {Row : Pos → Set} {Img₀ : Pos → Pos → Set} → (∀ {h} → Row h → HP h)
          → (∀ {k l e₀ h L a σ} → B′.PB k l → tB k e₀ → (Unpinned e₀ → Live tB k) → Row h → Img₀ h L → k ≡ h ⊕ (a ∷ σ) → Anchor M_b k l h a)
          → (∀ {k l e₀ h L a σ} → S′.PB k l → o k e₀ → (Unpinned e₀ → Live o k) → Row h → Img₀ h L → k ≡ h ⊕ (a ∷ σ) → Anchor M_s k l h a)
          → (∀ {k e x y} → o k e → M_s x y → k ⊑ x → x ≡ k)
          → ∀ {k l e₀ h L a σ} → PB′ k l → t k e₀ → (Unpinned e₀ → Live t k) → Row h → Img₀ h L → k ≡ h ⊕ (a ∷ σ) → Anchor M′ k l h a
    nest′ hr nb na bs (inj₁ (pb , (_ , b) , _)) tk lv rw ci e with classify tk
    ... | inj₁ tb = anchor-grow inj₁ (nb pb tb (λ un → body-live (lv un)) rw ci e)
    ... | inj₂ (_ , _ , x , s) = ⊥-elim (flat-apart x s b)
    nest′ hr nb na bs {h = h} {a = a} {σ = σ} (inj₂ (k₀ , l₀ , _ , _ , (x₀ , s-val refl) , inj₁ (i , _) , refl , _)) tk lv rw ci e =
      k₀ ⊕ [ ix 0 ] , l₀ ⊕ [ ix 0 ] , inj₂ (k₀ , l₀ , (_ , x₀) , i , refl , refl) , ⊑-refl _
      , inj₁ ((σ , trans e (sym (⊕-assoc h [ a ] σ))) , ⊑-refl _)
    nest′ hr nb na bs {h = h} {a = a} {σ = σ} (inj₂ (k₀ , l₀ , _ , _ , (x₀ , s-skip refl) , inj₁ (i , _) , refl , _)) tk lv rw ci e =
      let (y , m , yl) = S′.ext i in
      k₀ , y , inj₁ (ms_b m) , ⊑-trans yl ([ ix 0 ] , refl) , inj₁ ((σ , trans e (sym (⊕-assoc h [ a ] σ))) , ⊑-refl _)
    nest′ hr nb na bs {h = h} {a = a} {σ = σ} (inj₂ (k₀ , l₀ , _ , _ , (x₀ , s-pin refl) , inj₁ (i , _) , refl , _)) tk lv rw ci e =
      let (y , m , yl) = S′.ext i in
      k₀ , y , inj₁ (ms_b m) , ⊑-trans yl ([ ix 0 ] , refl) , inj₁ ((σ , trans e (sym (⊕-assoc h [ a ] σ))) , ⊑-refl _)
    nest′ hr nb na bs {h = h} {a = a} {σ = σ} (inj₂ (k₀ , l₀ , _ , _ , (x₀ , s-pass refl _) , inj₁ (i , _) , refl , _)) tk lv rw ci e =
      let (y , m , yl) = S′.ext i in
      k₀ , y , inj₁ (ms_b m) , ⊑-trans yl ([ ix 0 ] , refl) , inj₁ ((σ , trans e (sym (⊕-assoc h [ a ] σ))) , ⊑-refl _)
    nest′ hr nb na bs (inj₂ (k₀ , l₀ , _ , _ , (x₀ , s-skip refl) , inj₂ pb , refl , _)) tk lv rw ci e =
      anchor-up (anchor-grow (λ m → inj₁ (ms_b m)) (na pb x₀ (λ un {c} → src-live x₀ un {c}) rw ci e)) ([ ix 0 ] , refl)
    nest′ hr nb na bs (inj₂ (k₀ , l₀ , _ , _ , (x₀ , s-pin refl) , inj₂ pb , refl , _)) tk lv rw ci e =
      anchor-up (anchor-grow (λ m → inj₁ (ms_b m)) (na pb x₀ (λ un {c} → src-live x₀ un {c}) rw ci e)) ([ ix 0 ] , refl)
    nest′ hr nb na bs (inj₂ (k₀ , l₀ , _ , _ , (x₀ , s-pass refl _) , inj₂ pb , refl , _)) tk lv rw ci e =
      anchor-up (anchor-grow (λ m → inj₁ (ms_b m)) (na pb x₀ (λ un {c} → src-live x₀ un {c}) rw ci e)) ([ ix 0 ] , refl)
    nest′ hr nb na bs {h = h} {a = a} {σ = σ} (inj₂ (k₀ , l₀ , _ , _ , (x₀ , s-val refl) , inj₂ pb , refl , _)) tk lv rw ci e
      with ⊑-snoc k₀ (a ∷ σ , e)
    ... | inj₂ eq = ⊥-elim (ext≢ h σ (trans (sym e) (sym eq)))
    ... | inj₁ ([] , hk) =
      ⊥-elim (proj₂ okP (hr rw) (InvAt.world Io x₀) (⊑-inside ([] , trans (trans (sym (⊕-identityʳ h)) (sym hk)) (sym (⊕-identityʳ k₀)))))
    ... | inj₁ (b ∷ τ , refl) with ∷-injectiveˡ (⊕-cancelˡ h (b ∷ τ ++ [ ix 0 ]) (a ∷ σ) (trans (sym (⊕-assoc h (b ∷ τ) [ ix 0 ])) e))
    ...   | refl = anchor-down bs x₀ (na pb x₀ (λ un {c} → src-live x₀ un {c}) rw ci refl)

    -- What is open: the outer rows' late carriers past the map, each
    -- reached row's carrier listed, each shown carrier's plain row, the
    -- rows' instants, the whole run, the cover past both subterms, and
    -- each live pin's carrier in order.
    postulate
      flat-pb-past : ∀ {k l e₀ e x y} → PB′ k l → t k e₀ → (Unpinned e₀ → Live t k) → u l e → M′ x y → x ≺ k → ¬ (x ⊑ k) → Ahead y l
      flat-img : ∀ {k e} → t k e → Unpinned e → Live t k → Listed t k → LP k
               → (Σ Pos λ l → FlatImg k l × Σ (Ev (IE B)) λ e′ → u l e′ × Listed u l × Match Every (One valuesOf) (Reads valuesOf) e e′)
                 ⊎ (e ≡ skip × IntoAt FlatImg u PB′ HP p k)
      flat-img¬¬ : ∀ {k e} → t k e → Unpinned e → Live t k → Few t k
                 → ¬ ¬ ((Σ Pos λ l → FlatImg k l × Σ (Ev (IE B)) λ e′ → u l e′ × Match Every (One valuesOf) (Reads valuesOf) e e′) ⊎ e ≡ skip)
      flat-shown : ∀ {l e} → u l e → Shown (One valuesOf) e → Live u l → Few u l
                 → Σ Pos λ k → FlatImg k l × Σ (Ev B) λ e₀ → t k e₀ × Match Every (One valuesOf) (Reads valuesOf) e₀ e
      flat-place : ∀ {m e} → u m e → Live u m → Listed u m
                 → instantOf m ≡ instantOf p′ ⊎ (Σ Pos λ k → Σ Pos λ l → FlatImg k l × instantOf l ≡ instantOf m × Near u m l)
                   ⊎ Σ Pos λ h → HE h × instantOf h ≡ instantOf m
      flat-whole : Whole t → (∀ {c} → t c end → ⊥) → (∀ {q} → LP q) → Whole u
      flat-cover : ∀ {v w} → Listed t v → LP v → Live t v → From FlatImg PB′ t u v w → Listed u w
      flat-first : ∀ {k q} → t k (pin q) → Live t k → Listed t k → LP k
                 → (Σ Pos λ l → Σ (Ev (IE B)) (u l) × PB′ k l × From FlatImg PB′ t u k l)
                   × (instantOf k ≡ instantOf p ⊎ (Σ Pos λ k₀ → k₀ ≺ q × Home t k₀ × instantOf k₀ ≡ instantOf k)
                      ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)
      flat-pinned↓ : ∀ {k q} → t k (pin q) → Listed t q → PinList t q k → LP q
                   → (Σ Pos λ l → Σ Pos λ q′ → u l (pin q′) × PB′ k l × Targeted M′ q q′ × PinList u q′ l)
                     × (instantOf k ≡ instantOf p ⊎ (Σ Pos λ k₀ → k₀ ≺ q × Home t k₀ × instantOf k₀ ≡ instantOf k)
                        ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)

    -- Listed before it as the flatMap is before the pin.
    flat-pinned : ∀ {k q} → t k (pin q) → Live t k → Listed t k → LP k
                → InOrder FlatImg PB′ t u k
                  × (instantOf k ≡ instantOf p ⊎ (Σ Pos λ k₀ → k₀ ≺ q × Home t k₀ × instantOf k₀ ≡ instantOf k)
                     ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)
    flat-pinned {k} tk lv L lp with flat-first tk lv L lp
    ... | (l , ul , pb , F) , h = (l , ul , pb , flat-cover L lp lv (λ {k₁} {e₁} {l₁} {e₂} → F {k₁} {e₁} {l₁} {e₂}) , (λ {k₁} {e₁} {l₁} {e₂} → F {k₁} {e₁} {l₁} {e₂})) , h

    carried : CarryAt valuesOf M′ HP HE LP t u p p′
    carried = record
      { Img = FlatImg ; ext = ext′ ; PB = PB′ ; pb-few = pb-few′ ; pb-img = pb-img′ ; pb-past = flat-pb-past
      ; img = flat-img ; img¬¬ = flat-img¬¬ ; shown = flat-shown ; img-row = img-row′ ; img-fun = img-fun′
      ; place = flat-place ; live = live′ ; few = few′ ; whole = flat-whole ; bk = bk′ ; in-bk = in-bk′ ; pinned = flat-pinned ; cover = flat-cover }

    narrowed : Narrow carried
    narrowed = record { pinned↓ = flat-pinned↓ }
