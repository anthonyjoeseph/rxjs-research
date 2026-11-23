{-# OPTIONS --guardedness #-}

-- A SOURCE READ HOT HOLDS WHAT IT HOLDS.  A reader subscribed at `sb`,
-- before every row of the source, meets each proper row moved under its
-- own `sub sb` child: in the same instant, in the same order, a pin heard
-- as a step.  So each run met is the source's, moved, and so is each
-- count.
--
-- A wait is the one thing the move does not keep.  A pin heard as a step
-- waits on every row before it, where the pin waited on its own connect's
-- burst alone, so the reading drops a heard pin with infinitely many rows
-- before it, and a position past one may have few rows before it in the
-- reading but not in the source.  But a row of the source with few rows
-- before it is read, so the rows of the source with few rows before such
-- a position are listed, and a source whose hangs show (`Shows`) has few
-- rows before it.
module simultaneous.HeldHot where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there; any?)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_≟_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (decidable-stable; _⊎-dec_)

open import denotation.Position using (Pos; root; _≟ᵖ_; _∙_; Path; Label; sub; _⊕_)
open import denotation.Events using (Timeline; fresh; <ᵖ-down; <ᵖ-apart)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; pin; end; Few; Reach; Proper; Rejoin; shown; heard; ended; late; hot; Bare; Unpinned;
  enter; _≺_; _≼_)
open import denotation.Read using (Run; []; _∷_; Visible; After; cursor)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≺-absurd; ≼-or-≻; ≼-split; ≼-antisym; ≺-ext; entered-few)
open import denotation.Laws.Worlds using (_⊑_; ⊑-trans; ⊕-identityʳ; ⊕-injˡ; Shows; full)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.InstEmit using (instEmit; mark; begin)
open import simultaneous.Relations using (Met)
open import simultaneous.Readings using (rootOf; parent; parent-snoc)
open import simultaneous.Routed using (Held; Idle; Rest; cnt; nameOf; nm; opos)
open import simultaneous.Relabel using (same-mark; EvSame; ev-out; ev-end; RowsAt; []ᵃ; _∷ᵃ_; cntAt; memAt; endAt; held-move)
open import simultaneous.HeldConnect using (rootOf-ext; early-inst; same-refl)
open import simultaneous.HeldTake using (ex-ext)
open import simultaneous.Layers using (to≺; from≺; last-met)
import simultaneous.Layers as Layers

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

-- The positions a position lies under, itself included.
heads : Path → List Path
heads []       = [] ∷ []
heads (l ∷ ls) = [] ∷ L.map (l ∷_) (heads ls)

head-in : ∀ (x ys : Path) → x ∈ heads (x L.++ ys)
head-in []      []      = here refl
head-in []      (_ ∷ _) = here refl
head-in (l ∷ x) ys      = there (∈-map⁺ (l ∷_) (head-in x ys))

prefixes : Pos → List Pos
prefixes (i ∙ x) = L.map (i ∙_) (heads x)

prefix-in : ∀ k ys {w} → w ≡ k ⊕ ys → k ∈ prefixes w
prefix-in (i ∙ x) ys refl = ∈-map⁺ (i ∙_) (head-in x ys)

em : ∀ {P : Set} → ¬ ¬ (P ⊎ ¬ P)
em k = k (inj₂ λ x → k (inj₁ x))

module HotRun {A : Set} (S : EmissionSet A) (sb : Pos)
               (flat  : ∀ {y e l ys e′} → S y e → S (y ⊕ (l ∷ ys)) e′ → ⊥)
               (func  : ∀ {y e e′} → S y e → S y e′ → e ≡ e′)
               (after : ∀ {y e} → S y e → sb ≺ y)
               (few-vis : ∀ {y e} → S y e → Visible e → Few S y)
               (proper-vis : ∀ {c y e} → S c end → S y e → Visible e → y ≼ c) where

  σ : EmissionSet A
  σ = Proper S

  Rd : EmissionSet A
  Rd = enter (hot σ) sb

  shift : Pos → Pos
  shift k = k ⊕ [ sub sb ]

  Sh : Pos → Pos → Set
  Sh y′ y = y′ ≡ shift y

  ----------------------------------------------------------------------
  -- Order

  -- No row of the source lies under another.
  apart : ∀ {k y e e′} → S k e → S y e′ → k ≺ y → ∀ ys → y ≡ k ⊕ ys → ⊥
  apart {k} sk sy ky []       eq = ≺-irrefl {k} (subst (k ≺_) (trans eq (⊕-identityʳ k)) ky)
  apart     sk sy ky (l ∷ ls) eq = flat sk (subst (λ z → S z _) eq sy)

  -- Below a row of the source, before a later one.
  past : ∀ {k y e e′} zs → S k e → S y e′ → k ≺ y → (k ⊕ zs) ≺ y
  past {k} {y} zs sk sy ky = to≺ (k ⊕ zs) y (<ᵖ-apart k y zs (from≺ k y ky) (apart sk sy ky))

  down : ∀ {k y e e′} → S k e → S y e′ → k ≺ y → shift k ≺ shift y
  down {k} {y} sk sy ky = to≺ (shift k) (shift y) (<ᵖ-down k y (sub sb) (sub sb) (from≺ k y ky) λ l ls → apart sk sy ky (l ∷ ls))

  reflect : ∀ {k y e e′} → S k e → S y e′ → shift k ≺ shift y → k ≺ y
  reflect {k} {y} sk sy lt with ≼-or-≻ y k
  ... | inj₂ ky = ky
  ... | inj₁ yk with ≼-split {y} {k} yk
  ...   | inj₁ yk′ = ⊥-elim (≺-absurd {shift k} {shift y} lt (down sy sk yk′))
  ...   | inj₂ refl = ⊥-elim (≺-irrefl {shift k} lt)

  ----------------------------------------------------------------------
  -- Rows

  -- Every row of the reading is a proper row of the source, moved.
  src : ∀ {y e} → Rejoin sb σ y e → Σ Pos λ k → y ≡ shift k × Σ _ (S k)
  src (shown x _ _) = _ , refl , _ , proj₁ x
  src (heard x _)   = _ , refl , _ , proj₁ x
  src (ended x _)   = _ , refl , _ , proj₁ x
  src (late x c≼)   = ⊥-elim (c≼ (after (proj₁ x)))

  src-vis : ∀ {y e} → Rejoin sb σ y e → Visible e → Σ Pos λ k → y ≡ shift k × σ k e
  src-vis (shown x _ _) _  = _ , refl , x
  src-vis (heard x _)   ()
  src-vis (ended x _)   _  = _ , refl , x
  src-vis (late x c≼)   _  = ⊥-elim (c≼ (after (proj₁ x)))

  -- Every proper row of the source is one of the reading's, moved.
  rj : ∀ {k e} → σ k e → Σ _ (Rejoin sb σ (shift k))
  rj {e = out _} x = _ , shown x tt (after (proj₁ x))
  rj {e = skip}  x = _ , shown x tt (after (proj₁ x))
  rj {e = pin _} x = _ , heard x (after (proj₁ x))
  rj {e = end}   x = _ , ended x (after (proj₁ x))

  -- Where the source's rows before a row are listed, the reading's are.
  reach-from : ∀ {k e₀} (ls : List Pos) → (∀ {j e} → S j e → j ≺ k → j ∈ ls) → S k e₀ → ∀ {e′} → Reach (Rejoin sb σ) (shift k) e′
  reach-from ls cov sk = L.map shift ls , λ y lt _ → pick y lt
    where
      pick : ∀ {y e} → Rejoin sb σ y e → y ≺ shift _ → y ∈ L.map shift ls
      pick y lt with src y
      ... | j , refl , _ , sj = ∈-map⁺ shift (cov sj (reflect sj sk lt))

  lift-vis : ∀ {k e} → S k e → Visible e → Rd (shift k) e
  lift-vis {e = out x} sk v = shown (sk , λ sc → proper-vis sc sk v) tt (after sk) , reach-from (proj₁ (few-vis sk v)) (proj₂ (few-vis sk v)) sk {out x}
  lift-vis {e = end}   sk v = ended (sk , λ sc → proper-vis sc sk v) (after sk) , reach-from (proj₁ (few-vis sk v)) (proj₂ (few-vis sk v)) sk {end}
  lift-vis {e = skip}  _ ()
  lift-vis {e = pin _} _ ()


  ----------------------------------------------------------------------
  -- The reading's own shape

  rj-σ : ∀ {y e} → Rejoin sb σ y e → Σ Pos λ k → y ≡ shift k × Σ _ (σ k)
  rj-σ (shown x _ _) = _ , refl , _ , x
  rj-σ (heard x _)   = _ , refl , _ , x
  rj-σ (ended x _)   = _ , refl , _ , x
  rj-σ (late x c≼)   = ⊥-elim (c≼ (after (proj₁ x)))

  -- Every row of the reading lies at or before its end.
  rd-proper : ∀ {q e c} → Rd q e → Rd c end → q ≼ c
  rd-proper (x , _) (y , _) with rj-σ x | src-vis y tt
  ... | k , refl , _ , σk | k′ , refl , σk′ = λ lt → proj₂ σk (proj₁ σk′) (reflect (proj₁ σk′) (proj₁ σk) lt)

  bare-pin : ∀ {e : Ev A} {r} → Bare e → e ≡ pin r → ⊥
  bare-pin {pin _} () _
  bare-pin {out _} _ ()
  bare-pin {skip}  _ ()
  bare-pin {end}   _ ()

  bare-end : ∀ {e : Ev A} → Bare e → e ≡ end → ⊥
  bare-end {end}   () _
  bare-end {out _} _ ()
  bare-end {skip}  _ ()
  bare-end {pin _} _ ()

  -- One row to a position.
  rd-func : ∀ {q e e′} → Rd q e → Rd q e′ → e ≡ e′
  rd-func (x , _) (x′ , _) = go x x′ refl
    where
      go : ∀ {y y′ e e′} → Rejoin sb σ y e → Rejoin sb σ y′ e′ → y ≡ y′ → e ≡ e′
      go (late x c≼) _ _ = ⊥-elim (c≼ (after (proj₁ x)))
      go _ (late x c≼) _ = ⊥-elim (c≼ (after (proj₁ x)))
      go (shown x b _) (shown x′ _ _) eq with ⊕-injˡ _ _ eq
      ... | refl = func (proj₁ x) (proj₁ x′)
      go (shown x b _) (heard x′ _) eq with ⊕-injˡ _ _ eq
      ... | refl = ⊥-elim (bare-pin b (func (proj₁ x) (proj₁ x′)))
      go (shown x b _) (ended x′ _) eq with ⊕-injˡ _ _ eq
      ... | refl = ⊥-elim (bare-end b (func (proj₁ x) (proj₁ x′)))
      go (heard x _) (shown x′ b _) eq with ⊕-injˡ _ _ eq
      ... | refl = ⊥-elim (bare-pin b (func (proj₁ x′) (proj₁ x)))
      go (heard x _) (heard x′ _) _ = refl
      go (heard x _) (ended x′ _) eq with ⊕-injˡ _ _ eq
      ... | refl with func (proj₁ x) (proj₁ x′)
      ...   | ()
      go (ended x _) (shown x′ b _) eq with ⊕-injˡ _ _ eq
      ... | refl = ⊥-elim (bare-end b (func (proj₁ x′) (proj₁ x)))
      go (ended x _) (heard x′ _) eq with ⊕-injˡ _ _ eq
      ... | refl with func (proj₁ x′) (proj₁ x)
      ...   | ()
      go (ended x _) (ended x′ _) _ = refl

  rd-nopin : ∀ {k r} → Rd k (pin r) → ⊥
  rd-nopin {r = r} (shown _ b _ , _) = bare-pin {pin r} b refl

  rd-few : ∀ {q e} → Rd q e → Few Rd q
  rd-few {e = e} x = entered-few (hot σ) sb (full (un e x)) x
    where
      un : ∀ {q} e → Rd q e → Unpinned e
      un (out _) _ = tt
      un skip    _ = tt
      un end     _ = tt
      un (pin _) x = ⊥-elim (rd-nopin x)

  -- The reading's rows lie past whatever the source's do.
  rd-past : ∀ {v} → (∀ {y e} → S y e → v ≺ y) → ∀ {k e} → Rd k e → v ≺ k
  rd-past {v} vs (x , _) with src x
  ... | k , refl , _ , sk = ≺-trans {v} {k} {shift k} (vs sk) (≺-ext k {sub sb} [])

  ----------------------------------------------------------------------
  -- Runs

  shiftM : Maybe Pos → Maybe Pos
  shiftM nothing  = nothing
  shiftM (just y) = just (shift y)

  -- A reader's cursor: none yet, or a row of the source.
  data Cur : Maybe Pos → Set where
    none : Cur nothing
    some : ∀ {y e} → S y e → Cur (just y)

  aft-back : ∀ {c k e} → Cur c → S k e → After (shiftM c) (shift k) → After c k
  aft-back none      _  _ = tt
  aft-back (some sy) sk a = reflect sy sk a

  aft-fwd : ∀ {c k e} → Cur c → S k e → After c k → After (shiftM c) (shift k)
  aft-fwd none      _  _ = tt
  aft-fwd (some sy) sk a = down sy sk a

  -- Every run met of the reading is the source's, moved.
  shR : Pos × Ev A → Pos × Ev A
  shR (y , e) = shift y , e

  run-back : ∀ {c rs′} → Cur c → Run Rd (shiftM c) rs′ → Σ _ λ rs → Run S c rs × rs′ ≡ L.map shR rs
  run-back cu [] = [] , [] , refl
  run-back {c} cu (((((x , _) , _) , _) , vi , ac , lf) ∷ run) with src-vis x vi
  ... | k , refl , σk with run-back (some (proj₁ σk)) run
  ...   | rs , run′ , refl =
    (k , _) ∷ rs , (((σk , few-vis (proj₁ σk) vi) , vi , aft-back cu (proj₁ σk) ac , least) ∷ run′) , refl
    where
      least : ∀ {k₂ e₂} → S k₂ e₂ → Visible e₂ → After c k₂ → k ≼ k₂
      least s₂ v₂ a₂ lt = lf (lift-vis s₂ v₂) v₂ (aft-fwd cu s₂ a₂) (down s₂ (proj₁ σk) lt)

  Last : Maybe Pos → List (Pos × Ev A) → Set
  Last = Layers.Last S

  last-cur : ∀ {c rs} → Last c rs → Cur c
  last-cur {nothing} _               = none
  last-cur {just _}  (_ , _ , sy , _) = some sy

  -- WHERE A POSITION HAS FEW ROWS BEFORE IT IN THE READING, BEFORE EVERY
  -- END, it has few before it in the source: a row of the source before it
  -- is proper, and is in the reading once every row before it is.
  module FewBack (shows : Shows S) {w} (F : Few Rd w) (wend : ∀ {c} → S c end → w ≼ shift c) where

    ls : List Pos
    ls = L.map parent (proj₁ F) ++ prefixes w

    proper-below : ∀ {k e} → S k e → k ≺ w → ∀ {c} → S c end → k ≼ c
    proper-below {k} sk kw {c} sc ck = wend sc (≺-trans {shift c} {k} {w} (past [ sub sb ] sc sk ck) kw)

    -- A row with few rows before it is read, so it is listed.
    listed : ∀ {k e} → S k e → Few S k → k ≺ w → k ∈ ls
    listed {k} sk fk kw = decidable-stable (any? (k ≟ᵖ_) ls) λ nin → em {Σ Path λ ys → w ≡ k ⊕ ys} λ
      { (inj₁ (ys , eq)) → nin (∈-++⁺ʳ (L.map parent (proj₁ F)) (prefix-in k ys eq))
      ; (inj₂ np) → nin (∈-++⁺ˡ (subst (_∈ L.map parent (proj₁ F)) (parent-snoc k (sub sb))
                          (∈-map⁺ parent (proj₂ F (proj₂ r , reach-from (proj₁ fk) (proj₂ fk) sk {proj₁ r}) (moved np))))) }
      where
        r = rj (sk , proper-below sk kw)
        moved : ¬ Σ Path (λ ys → w ≡ k ⊕ ys) → shift k ≺ w
        moved np = to≺ (shift k) w (<ᵖ-apart k w [ sub sb ] (from≺ k w kw) λ ys eq → np (ys , eq))

    few : ¬ ¬ Few S w
    few = shows (ls , listed)

-- Over marks, the reading holds what the source holds.
module HotRead {A : Set} (S : EmissionSet (IE A)) (sb : Pos)
               (flat  : ∀ {y e l ys e′} → S y e → S (y ⊕ (l ∷ ys)) e′ → ⊥)
               (func  : ∀ {y e e′} → S y e → S y e′ → e ≡ e′)
               (after : ∀ {y e} → S y e → sb ≺ y)
               (few-vis : ∀ {y e} → S y e → Visible e → Few S y)
               (proper-vis : ∀ {c y e} → S c end → S y e → Visible e → y ≼ c)
               (shows : Shows S) where
  open HotRun S sb flat func after few-vis proper-vis public

  ev-same : ∀ {e : Ev (IE A)} → Visible e → EvSame e e
  ev-same {out x} _ = ev-out (same-refl x)
  ev-same {end}   _ = ev-end
  ev-same {skip}  ()
  ev-same {pin _} ()

  -- A run of the source's rows, moved, relabels nothing.
  rows-at : ∀ {c rs} → Run S c rs → RowsAt Sh (L.map shR rs) rs
  rows-at [] = []ᵃ
  rows-at ((_ , vi , _) ∷ run) = (refl , ev-same vi) ∷ᵃ rows-at run

  back : ∀ {rs′} → Met Rd rs′ → Σ _ λ rs → Met S rs × RowsAt Sh rs′ rs
  back m with run-back none m
  ... | rs , run , refl = rs , run , rows-at run

  cursor-at : ∀ {rs′ rs : List (Pos × Ev (IE A))} → RowsAt Sh rs′ rs → ∀ c → cursor (shiftM c) rs′ ≡ shiftM (cursor c rs)
  cursor-at []ᵃ              c = refl
  cursor-at ((refl , _) ∷ᵃ eq) c = cursor-at eq (just _)
  ----------------------------------------------------------------------
  -- Rest

  rest-hot : Rest S → Rest Rd
  rest-hot R {rs′} m z bq with back m
  ... | rs , run , eq with memAt eq bq
  ...   | q , _ , bq′ , refl , same-mark e
    with R run (subst (λ r → proj₂ r ≡ 0) (cntAt eq) z)
           (subst (λ n → (q , out (instEmit (mark begin) n)) ∈ rs) (trans (sym (e refl)) (cong proj₁ (cntAt eq))) bq′)
  ...     | ks , h = L.map shift ks , pick
    where
      pick : ∀ {y e} → Rd y e → After (cursor nothing rs′) y → rootOf y ≡ rootOf (shift q) → y ∈ L.map shift ks
      pick (x , _) ay iq with src x
      ... | k , refl , _ , sk =
        ∈-map⁺ shift (h sk (aft-back (last-cur (last-met run)) sk (subst (λ c → After c (shift k)) (cursor-at eq nothing) ay))
                           (trans (sym (rootOf-ext k _)) (trans iq (rootOf-ext q _))))

  ----------------------------------------------------------------------
  -- Idle

  Goal : List (Pos × Ev (IE A)) → Pos → Set
  Goal rs w = proj₂ (cnt rs) ≡ 0 ⊎ proj₁ (cnt rs) ≡ nameOf w

  module IdleAt (I : Idle S) {rs} (run : Met S rs) (ne : ∀ {c} → (c , end) ∈ rs → ⊥) {w} (F : Few Rd w) where

    -- A row of the source met, after the cursor, that the position lies under.
    Under : Maybe Pos → Set
    Under c = Σ Pos λ y → Σ _ λ e → S y e × Visible e × After c y × Σ Label λ l → Σ Path λ zs → w ≡ y ⊕ (l ∷ zs)

    -- Every end of the source lies after the cursor, so is a row the position is not past.
    wend : ∀ {c} → Last c rs → (∀ {y e} → Rd y e → Visible e → After (shiftM c) y → w ≼ y) → ∀ {c₀} → S c₀ end → w ≼ shift c₀
    wend {nothing} _                  lw sc = lw (lift-vis sc tt) tt tt
    wend {just y}  (e , iy , sy , vy) lw {c₀} sc with ≼-or-≻ c₀ y
    ... | inj₂ yc = lw (lift-vis sc tt) tt (down sy sc yc)
    ... | inj₁ cy = ⊥-elim (ne (subst (λ e′ → (y , e′) ∈ rs) (func sy (subst (λ z → S z end) eq sc)) iy))
      where
        eq : c₀ ≡ y
        eq = ≼-antisym {c₀} {y} cy (proper-vis sc sy vy)

    aft-in : ∀ {c} → Cur c → After (shiftM c) w → After c w
    aft-in none      _ = tt
    aft-in (some {y} _) a = ≺-trans {y} {shift y} {w} (≺-ext y {sub sb} []) a

    goal : ∀ {c} → c ≡ cursor nothing rs → Last c rs → After (shiftM c) w
         → (∀ {y e} → Rd y e → Visible e → After (shiftM c) y → w ≼ y) → Goal rs w
    goal {c} refl lc aw lw =
      decidable-stable ((proj₂ (cnt rs) ≟ 0) ⊎-dec (proj₁ (cnt rs) ≟ᵖ nameOf w)) λ ng → em {Under c} λ
        { (inj₁ (y , e , sy , vy , ay , l , zs , eq)) → ng (under y sy vy ay l zs eq)
        ; (inj₂ nu) → FewBack.few shows F (wend lc lw) λ fw → ng (clear nu fw) }
      where
        cu = last-cur lc

        -- The position under a row met after the cursor: that row's route.
        under : ∀ y {e} → S y e → Visible e → After c y → ∀ l zs → w ≡ y ⊕ (l ∷ zs) → Goal rs w
        under y {e} sy vy ay l zs refl
          with I run ne (few-vis sy vy) ay
                 (λ {y₂} s₂ v₂ a₂ lt → lw (lift-vis s₂ v₂) v₂ (aft-fwd cu s₂ a₂)
                                          (≺-trans {shift y₂} {y} {w} (past [ sub sb ] s₂ sy lt) (≺-ext y {l} zs)))
        ... | inj₁ z  = inj₁ z
        ... | inj₂ nq = inj₂ (trans nq (cong nm (sym (rootOf-ext y (l ∷ zs)))))

        -- Under no row met after the cursor: the source's own route.
        clear : ¬ Under c → Few S w → Goal rs w
        clear nu fw = I run ne fw (aft-in cu aw) not-past
          where
            not-past : ∀ {y e} → S y e → Visible e → After c y → w ≼ y
            not-past {y} sy vy ay yw = em {Σ Path λ ys → w ≡ y ⊕ ys} λ
              { (inj₁ ([] , eq))     → ≺-irrefl {y} (subst (y ≺_) (trans eq (⊕-identityʳ y)) yw)
              ; (inj₁ (l ∷ zs , eq)) → nu (y , _ , sy , vy , ay , l , zs , eq)
              ; (inj₂ np) → lw (lift-vis sy vy) vy (aft-fwd cu sy ay)
                               (to≺ (shift y) w (<ᵖ-apart y w [ sub sb ] (from≺ y w yw) λ ys eq → np (ys , eq))) }

  idle-hot : Idle S → Idle Rd
  idle-hot I {rs′} m ne′ {w} F aw lw with back m
  ... | rs , run , eq =
    subst (λ r → proj₂ r ≡ 0 ⊎ proj₁ r ≡ nameOf w) (sym (cntAt eq))
      (IdleAt.goal I run ne F refl (last-met run) (subst (λ c → After c w) (cursor-at eq nothing) aw)
         (λ {y} r v a → lw r v (subst (λ c → After c y) (sym (cursor-at eq nothing)) a)))
    where
      ne : ∀ {c} → (c , end) ∈ rs → ⊥
      ne bc = ne′ (proj₁ (proj₂ (endAt eq bc)))

  ----------------------------------------------------------------------
  -- The reading holds

  held-hot : ∀ {cs} → Held S cs → Held Rd cs
  held-hot = held-move Sh
    (λ { {y = y} refl → rootOf-ext y _ })
    (λ { {y = y} refl x → ex-ext [ sub sb ] x })
    (λ { {y = y} refl x → early-inst [ sub sb ] x })
    (λ { {y = y} refl h → subst (λ I → opos I ⊑ shift y) (sym (rootOf-ext y _)) (⊑-trans h ([ sub sb ] , refl)) })
    (λ { (x , _) → let (k , eq , σk) = src-vis x tt in k , _ , eq , proj₁ σk , same-refl _ })
    (λ { (x , _) → let (k , eq , σk) = src-vis x tt in k , eq , proj₁ σk })
    back idle-hot rest-hot
