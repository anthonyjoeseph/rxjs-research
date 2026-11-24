{-# OPTIONS --guardedness #-}

-- A BINDER'S SOURCE IDLES AT A POSITION A READING OF IT BOUNDS.  Wherever
-- a reading of the source shows each source row past the source's cursor
-- below itself, and has no visible row it is ahead of before `w`, the
-- source's run idles at `w`: below a source row past the cursor, that
-- row's route; below none, few source rows lie before `w`, each shown,
-- and none past the cursor.
module simultaneous.IdleAt where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (any?; here; there) renaming (map to any-map)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (_≟_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable using (decidable-stable; _⊎-dec_)
import Relation.Nullary as Nl

open import denotation.Position using (Pos; Path; Label; ix; _⊕_; _≟ᵖ_)
open import denotation.EmissionSet using (EmissionSet; Den; Ev; out; end; Few; Silent; _≺_; _≼_)
open import denotation.Events using (<ᵖ-apart; <ᵖ-between)
open import denotation.Read using (Visible; After; cursor; loud)
open import denotation.Laws.Modulus using (≼-split; ≺-irrefl; ≺-≼-≺; ≺-trans; ≼-or-≻; entered-few; ≺→≼)
open import denotation.Laws.Worlds using (InvAt; Hots; Shows; ok-step; full; ⊑-≼; ⊕-identityʳ; _⊑_)
open import denotation.Laws.Shows using (cover; cov-∈; few-down)
open import simultaneous.Relations using (Met)
open import simultaneous.Routed using (Held; Idle; cnt; nameOf)
open import simultaneous.Layers using (run-row; pinby-vis; from≺; to≺)
open import simultaneous.LaneLocal using (inv-ev)
open import simultaneous.HeldComb using (ev)
open import simultaneous.HeldBase using (Bound; shows-ev)
open import simultaneous.HeldRead using (Rl; Src; held-src; s₀)
open import simultaneous.HeldHot using (em)
open import simultaneous.HeldTake using (name-ext)
open import denotation.Events using (Timeline; fresh)
open import denotation.Position using (root)
open import simultaneous.SObs using (lone; module Elaborate)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE)

-- THE LAWS OF A BINDER'S SOURCE where the binder subscribes it.
module SrcLaws {X} {d : Den (AIE X)} {cs} (b : Bound d cs) where

  HS : Held (Src b) (s₀ b ∷ Bound.outer b)
  HS = held-src b

  IS : InvAt (Hots (Bound.env b)) (s₀ b) (Src b)
  IS = inv-ev (Bound.m b) (Bound.src b) (Bound.env b) (Bound.good b) (s₀ b)
         (ok-step (Bound.at b ⊕ [ ix 1 ]) (ok-step (Bound.at b) (Bound.ok b)))

  -- Below a row of the source, before a later one.
  past : ∀ {k y e e′} zs → Src b k e → Src b y e′ → k ≺ y → (k ⊕ zs) ≺ y
  past {k} {y} zs sk sy ky = to≺ (k ⊕ zs) y (<ᵖ-apart k y zs (from≺ k y ky) apart)
    where
      apart : ∀ ys → y ≡ k ⊕ ys → ⊥
      apart [] eq = ≺-irrefl {k} (subst (k ≺_) (trans eq (⊕-identityʳ k)) ky)
      apart (l ∷ ls)    eq = InvAt.flat IS sk (subst (λ z → Src b z _) eq sy)

  -- A visible row of the source has few rows before it, and lies before every end.
  few-vis : ∀ {k e} → Src b k e → Visible e → Few (Src b) k
  few-vis {k} {out x} sk _ = entered-few (ev (Bound.m b) (Bound.src b) (Bound.env b)) (s₀ b) (λ {k′} {e′} → full {q = k} {e = out x} tt {k′} {e′}) sk
  few-vis {k} {end}   sk _ = entered-few (ev (Bound.m b) (Bound.src b) (Bound.env b)) (s₀ b) (λ {k′} {e′} → full {q = k} {e = end} tt {k′} {e′}) sk

  live : ∀ {k e} → Src b k e → Visible e → ∀ {c} → Src b c end → k ≼ c
  live sk v sc ck = pinby-vis v (InvAt.quiet IS sc sk ck)

  shS : Shows (Src b)
  shS = shows-ev (Bound.m b) (Bound.src b) (Bound.env b) (Bound.good b) (s₀ b)
          (ok-step (Bound.at b ⊕ [ ix 1 ]) (ok-step (Bound.at b) (Bound.ok b)))

-- A run's count is of a position's instant, or none.
Goal : ∀ {X} → List (Pos × Ev (IE X)) → Pos → Set
Goal rs w = proj₂ (cnt rs) ≡ 0 ⊎ proj₁ (cnt rs) ≡ nameOf w

module IdleAt {X V} {d : Den (AIE X)} {cs} (b : Bound d cs) {S : List (Pos × Ev (IE X))} (run : Met (Src b) S)
              (ne : ∀ {c} → (c , end) ∈ S → ⊥) {c e₁} (ec : cursor nothing S ≡ just c) (i₁ : (c , e₁) ∈ S)
              (T : EmissionSet V) (Ahead : Pos → Ev V → Set) {w} (F : Few T w) (cw : c ≺ w)
              (lw : ∀ {y e} → T y e → Visible e → Ahead y e → w ≼ y)
              (shown : ∀ {k e} → Src b k e → c ≺ k → Few (Src b) k → (∀ {c₁} → Src b c₁ end → k ≼ c₁) → k ≺ w
                     → (Σ Path (λ ys → w ≡ k ⊕ ys) → ⊥) → (Silent e → ∀ {y} → Rl y k → Few T y)
                     → Nl.¬ Nl.¬ (Σ Path λ zs → Σ (Ev V) λ e′ → T (k ⊕ zs) e′ × (Visible e → Visible e′) × Ahead (k ⊕ zs) e′)) where
  open SrcLaws b

  I : Idle (Src b)
  I = Held.idle HS

  sc : Src b c e₁
  sc = proj₁ (run-row run i₁)

  vc : Visible e₁
  vc = proj₂ (run-row run i₁)

  a-of : ∀ {y} → c ≺ y → After (cursor nothing S) y
  a-of {y} cy = subst (λ x → After x y) (sym ec) cy

  c-of : ∀ {y} → After (cursor nothing S) y → c ≺ y
  c-of {y} a = subst (λ x → After x y) ec a

  Shown : Pos → Ev (IE X) → Set
  Shown k e = Σ Path λ zs → Σ (Ev V) λ e′ → T (k ⊕ zs) e′ × (Visible e → Visible e′) × Ahead (k ⊕ zs) e′

  -- Before the position, not above it: below it, before it too.
  under-before : ∀ {k} → k ≺ w → (Σ Path (λ ys → w ≡ k ⊕ ys) → ⊥) → ∀ zs → (k ⊕ zs) ≺ w
  under-before {k} kw np zs = to≺ (k ⊕ zs) w (<ᵖ-apart k w zs (from≺ k w kw) λ ys eq → np (ys , eq))

  blocked : ∀ {k e} → Visible e → k ≺ w → (Σ Path (λ ys → w ≡ k ⊕ ys) → ⊥) → Shown k e → ⊥
  blocked v kw np (zs , e′ , r , vv , a) = lw r (vv v) a (under-before kw np zs)

  Beneath : Set
  Beneath = Σ Pos λ y → Σ (Ev (IE X)) λ e → Src b y e × Visible e × c ≺ y × Σ Label λ l → Σ Path λ zs → w ≡ y ⊕ (l ∷ zs)

  -- Below a source row past the cursor: that row's route.
  beneath : Beneath → Goal S w
  beneath (y , e , sy , vy , cy , l , zs , eq) =
    [ inj₁ , (λ nq → inj₂ (trans nq (sym (trans (cong nameOf eq) (name-ext y (l ∷ zs)))))) ]′ (I run ne (few-vis sy vy) (a-of cy) least)
    where
      yw : y ≼ w
      yw = subst (y ≼_) (sym eq) (⊑-≼ {y} {y ⊕ (l ∷ zs)} (l ∷ zs , refl))

      least : ∀ {y₂ e₂} → Src b y₂ e₂ → Visible e₂ → After (cursor nothing S) y₂ → y ≼ y₂
      least {y₂} {e₂} s₂ v₂ a₂ lt =
        shown s₂ (c-of a₂) (few-vis s₂ v₂) (live s₂ v₂) (≺-≼-≺ {y₂} {y} {w} lt yw) np (λ sl → ⊥-elim (loud v₂ sl))
          (blocked v₂ (≺-≼-≺ {y₂} {y} {w} lt yw) np)
        where
          np : Σ Path (λ ys → w ≡ y₂ ⊕ ys) → ⊥
          np (ys , eq′) = yw (subst (_≺ y) (sym eq′) (past ys s₂ sy lt))

  -- Below no source row past the cursor: the source's own route.
  clear : (Beneath → ⊥) → Few (Src b) w → Goal S w
  clear nu fw = I run ne fw (a-of cw) not-past
    where
      not-past : ∀ {y e} → Src b y e → Visible e → After (cursor nothing S) y → w ≼ y
      not-past {y} {e} sy vy ay yw = em {Σ Path λ ys → w ≡ y ⊕ ys} λ
        { (inj₁ ([] , eq)) → ≺-irrefl {y} (subst (y ≺_) (trans eq (⊕-identityʳ y)) yw)
        ; (inj₁ (l ∷ zs , eq))       → nu (y , e , sy , vy , c-of ay , l , zs , eq)
        ; (inj₂ np)                  → shown sy (c-of ay) (few-vis sy vy) (live sy vy) yw np (λ sl → ⊥-elim (loud vy sl)) (blocked vy yw np) }

  fc : Few (Src b) c
  fc = few-vis sc vc

  ls : List Pos
  ls = c ∷ proj₁ fc ++ cover w (proj₁ F)

  -- A row past the cursor and before the position lies before every end:
  -- an end past the cursor is shown, and the position lies below it.
  live-past : ∀ {k e} → Src b k e → c ≺ k → k ≺ w → ∀ {c₁} → Src b c₁ end → k ≼ c₁
  live-past {k} {e} sk ck kw {c₁} se c₁k = [ before-c , after-c ]′ (≼-or-≻ c₁ c)
    where
      before-c : c₁ ≼ c → ⊥
      before-c c₁c =
        [ (λ lt → pinby-vis vc (InvAt.quiet IS se sc lt))
        , (λ eq → ne (subst (λ e′ → (c , e′) ∈ S) (InvAt.func IS sc (subst (λ z → Src b z end) eq se)) i₁)) ]′ (≼-split {c₁} {c} c₁c)

      flat-k : Σ Path (λ zs′ → k ≡ c₁ ⊕ zs′) → ⊥
      flat-k ([] , eq) = ≺-irrefl {c₁} (subst (c₁ ≺_) (trans eq (⊕-identityʳ c₁)) c₁k)
      flat-k (l ∷ zs′ , eq)      = InvAt.flat IS se (subst (λ z → Src b z e) eq sk)

      c₁w : c₁ ≺ w
      c₁w = ≺-trans {c₁} {k} {w} c₁k kw

      after-c : c ≺ c₁ → ⊥
      after-c cc₁ = em {Σ Path λ ys → w ≡ c₁ ⊕ ys} λ
        { (inj₁ (ys , eq)) → flat-k (<ᵖ-between c₁ k ys (from≺ c₁ k c₁k) (from≺ k (c₁ ⊕ ys) (subst (k ≺_) eq kw)))
        ; (inj₂ np)        → shown se cc₁ (few-vis se tt) (live se tt) c₁w np (λ ()) (blocked {e = end} tt c₁w np) }

  -- A source row with few rows before it, before the position, is listed:
  -- at or before the cursor, or shown, below a row of the reading's or above the position.
  listed : ∀ {k e} → Src b k e → Few (Src b) k → k ≺ w → k ∈ ls
  listed {k} {e} sk fk kw = decidable-stable (any? (k ≟ᵖ_) ls) λ nin →
    [ (λ kc → [ (λ lt → nin (there (∈-++⁺ˡ (proj₂ fc sk lt)))) , (λ eq → nin (here eq)) ]′ (≼-split {k} {c} kc))
    , past-c nin ]′ (≼-or-≻ k c)
    where
      past-c : (k ∈ ls → ⊥) → c ≺ k → ⊥
      past-c nin ck = em {Σ Path λ ys → w ≡ k ⊕ ys} λ
        { (inj₁ (ys , eq)) → nin (there (∈-++⁺ʳ (proj₁ fc) (cov-∈ {w} {proj₁ F} (inj₁ (ys , eq)))))
        ; (inj₂ np)        → shown sk ck fk (live-past sk ck kw) kw np (λ _ → few-below np) (into np) }
        where
          -- Below `k`, before the position: the reading has few rows there.
          few-below : (Σ Path (λ ys → w ≡ k ⊕ ys) → ⊥) → ∀ {y} → Rl y k → Few T y
          few-below np (zs , refl) = few-down F (≺→≼ {k ⊕ zs} {w} (under-before kw np zs))

          into : (Σ Path (λ ys → w ≡ k ⊕ ys) → ⊥) → Shown k e → ⊥
          into np (zs , e′ , r , _ , _) =
            nin (there (∈-++⁺ʳ (proj₁ fc) (cov-∈ {w} {proj₁ F} (inj₂ (any-map (λ eq → subst (k ⊑_) eq (zs , refl))
              (proj₂ F r (under-before kw np zs)))))))

  goal : Goal S w
  goal = decidable-stable ((proj₂ (cnt S) ≟ 0) ⊎-dec (proj₁ (cnt S) ≟ᵖ nameOf w)) λ ng → em {Beneath} λ
    { (inj₁ u)  → ng (beneath u)
    ; (inj₂ nu) → shS (ls , listed) λ fw → ng (clear nu fw) }
