{-# OPTIONS --guardedness #-}

-- A JOINER CARRIES A JOINER when its outer's running values are paired
-- with the other's, value for value, and each lane is carried into its
-- partner's.  A lane row rides its lane's carrier; a lane's end, carried
-- end for end, is joined where its partner's is.
module simultaneous.JoinCarry where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary using (¬_)
open import Function using (_⇔_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import denotation.Position using (Pos; _≟ᵖ_; root)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Truncate; Few; Ended; _≺_; module Joining)
open import denotation.Laws.Worlds using (_⊑_; _∪ʰ_)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (Live; Shown; Match; Every; One; Reads)
open import simultaneous.Listing using (Listed)
open import simultaneous.ConnLists using (trunc-few)
open import denotation.Events using (Timeline; fresh)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.CarryBase using (PMap; _⊆ᴹ_; CarryAt; IntoAt; Near; Whole; From; InOrder; Home; Ahead)
open import simultaneous.SObs using (lone; module Elaborate)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

-- A JOINER'S LANE ROWS, not its outer's.
module Lanes {A B : Set} (Ln : Pos → A → EmissionSet B) (o : EmissionSet A) (Runs : Pos → Set) (Cut : Pos → Pos → Set) (Hand : Pos → Set) where
  module J = Joining Ln o (λ _ _ → ⊥) (Ended o) Runs Cut Hand

  t : EmissionSet B
  t = Truncate J.JoinT

  Bod : ∀ {k e} → J.JoinT k e → Set
  Bod (J.val _)     = ⊥
  Bod (J.step _)    = ⊥
  Bod (J.opin _)    = ⊥
  Bod (J.opass _ _) = ⊥
  Bod _             = ⊤

  tB : EmissionSet B
  tB k e = Σ (t k e) λ x → Bod (proj₁ x)

-- The plain joiner over `Ln`, the elaborated over `Ln*`; `V q a q*`
-- pairs the plain running value `a` at `q` with the elaborated at `q*`,
-- whose lane carries the plain one's along its own map, part of `N`.
module Joined {A B : Set} {HP HE LP : Pos → Set} (p p′ : Pos)
              (o : EmissionSet A) (Ln : Pos → A → EmissionSet B) (Runs : Pos → Set) (Cut : Pos → Pos → Set) (Hand : Pos → Set)
              (o* : EmissionSet A) (Ln* : Pos → A → EmissionSet (IE B)) (Runs* : Pos → Set) (Cut* : Pos → Pos → Set) (Hand* : Pos → Set)
              (V : Pos → A → Pos → Set)
              (v-at : ∀ {q a q*} → V q a q* → o q (out a) × Runs q × o* q* (out a) × Runs* q*)
              (N : PMap) (LM : ∀ {q a q*} → V q a q* → PMap) (lm-sub : ∀ {q a q*} (v : V q a q*) → LM v ⊆ᴹ N)
              (lc : ∀ {q a q*} (v : V q a q*) → Σ Pos λ s → Σ Pos λ s* → CarryAt valuesOf (LM v) HP HE LP (Ln q a) (Ln* q* a) s s*)
              -- Two lanes' rows lie apart: one row is one lane's, imaged once.
              (img-apart : ∀ {q a q* q′ a′ q*′} (v : V q a q*) (v′ : V q′ a′ q*′) {k l l′}
                         → CarryAt.Img (proj₂ (proj₂ (lc v))) k l → CarryAt.Img (proj₂ (proj₂ (lc v′))) k l′ → l ≡ l′)
              (pb-apart : ∀ {q a q* q′ a′ q*′} (v : V q a q*) (v′ : V q′ a′ q*′) {k l l′}
                        → CarryAt.PB (proj₂ (proj₂ (lc v))) k l → CarryAt.Img (proj₂ (proj₂ (lc v′))) k l′ → ⊥)
              -- THE PAIRED JOINERS AGREE: every running value is paired, a
              -- lane is cut where its partner is, and its end is joined, and
              -- handed off, where its partner's is.
              (paired : ∀ {q a} → o q (out a) → Runs q → Listed o q → LP q → Σ Pos (V q a))
              (cut-agree : ∀ {q a q*} (v : V q a q*) {k l} → CarryAt.Img (proj₂ (proj₂ (lc v))) k l → Cut q k ⇔ Cut* q* l)
              (done-agree : ∀ {q a q*} (v : V q a q*) {c c*} → CarryAt.Img (proj₂ (proj₂ (lc v))) c c* → Ln q a c end
                          → Joining.Done Ln o (λ _ _ → ⊥) (Ended o) Runs Cut Hand c ⇔ Joining.Done Ln* o* (λ _ _ → ⊥) (Ended o*) Runs* Cut* Hand* c*)
              (hand-agree : ∀ {q a q*} (v : V q a q*) {c c*} → CarryAt.Img (proj₂ (proj₂ (lc v))) c c* → Ln q a c end → Hand c ⇔ Hand* c*) where
  open Lanes Ln o Runs Cut Hand public
  module J* = Joining Ln* o* (λ _ _ → ⊥) (Ended o*) Runs* Cut* Hand*

  u : EmissionSet (IE B)
  u = Truncate J*.JoinT

  -- Each value's lane carry.
  module L {q a q*} (v : V q a q*) = CarryAt (proj₂ (proj₂ (lc v)))

  -- A lane row the joiner reaches, on its lane's carrier.
  LaneImg : Pos → Pos → Set
  LaneImg k l = Σ Pos λ q → Σ A λ a → Σ Pos λ q* → Σ (V q a q*) λ v → L.Img v k l × Few J.JoinT k × (Cut q k → ⊥)

  -- A lane row carried into its instant, by its lane.
  LanePB : Pos → Pos → Set
  LanePB k l = Σ Pos λ q → Σ A λ a → Σ Pos λ q* → Σ (V q a q*) λ v → L.PB v k l × Σ (Ev B) (tB k) × Σ (Ev (IE B)) (u l)

  LP′ : Pos → Set
  LP′ q = Listed o q × LP q

  ext : ∀ {k l} → LaneImg k l → Σ Pos λ y → N k y × y ⊑ l
  ext (_ , _ , _ , v , i , _) with L.ext v i
  ... | y , m , yl = y , lm-sub v m , yl

  few : ∀ {k l} → LaneImg k l → Few tB k
  few (_ , _ , _ , _ , _ , F , _) = let (ks , h) = trunc-few F in ks , λ y kq → h (proj₁ y) kq

  -- THE JOINED LANES' FIELDS: each a lane's own, the lanes lying apart,
  -- a lane's end joined as its partner's is.
  postulate
    join-pb-few  : ∀ {l e} → u l e → Σ (List Pos) λ ks → ∀ {k} → LanePB k l → k ∈ ks
    join-pb-past : ∀ {k l e₀ e x y} → LanePB k l → tB k e₀ → (Unpinned e₀ → Live tB k) → u l e → N x y → x ≺ k → ¬ (x ⊑ k) → Ahead y l
    join-img     : ∀ {k e} → tB k e → Unpinned e → Live tB k → Listed tB k → LP′ k
                 → (Σ Pos λ l → LaneImg k l × Σ (Ev (IE B)) λ e′ → u l e′ × Listed u l × Match Every (One valuesOf) (Reads valuesOf) e e′)
                   ⊎ (e ≡ skip × IntoAt LaneImg u LanePB (HP ∪ʰ o) p k)
    join-img¬¬   : ∀ {k e} → tB k e → Unpinned e → Live tB k → Few tB k
                 → ¬ ¬ ((Σ Pos λ l → LaneImg k l × Σ (Ev (IE B)) λ e′ → u l e′ × Match Every (One valuesOf) (Reads valuesOf) e e′) ⊎ e ≡ skip)
    join-shown   : ∀ {l e} → u l e → Shown (One valuesOf) e → Live u l → Few u l
                 → Σ Pos λ k → LaneImg k l × Σ (Ev B) λ e₀ → tB k e₀ × Match Every (One valuesOf) (Reads valuesOf) e₀ e
    join-img-row : ∀ {k l} → LaneImg k l → ¬ ¬ Σ (Ev B) λ e → tB k e × Unpinned e
    join-place   : ∀ {m e} → u m e → Live u m → Listed u m
                 → instantOf m ≡ instantOf p′ ⊎ (Σ Pos λ k → Σ Pos λ l → LaneImg k l × instantOf l ≡ instantOf m × Near u m l)
                   ⊎ Σ Pos λ h → HE h × instantOf h ≡ instantOf m
    join-live    : ∀ {k l} → LaneImg k l → Live tB k → Live u l
    join-whole   : Whole tB → (∀ {c} → tB c end → ⊥) → (∀ {q} → LP′ q) → Whole u
    join-cover   : ∀ {v w} → Listed tB v → LP′ v → Live tB v → From LaneImg LanePB tB u v w → Listed u w
    join-bk      : Σ (Pos → List Pos) λ bk → ∀ {k l} → LaneImg k l → k ∈ bk l
    join-pinned  : ∀ {k r} → tB k (pin r) → Live tB k → Listed tB k → LP′ k
                 → InOrder LaneImg LanePB tB u k
                   × (instantOf k ≡ instantOf p ⊎ (Σ Pos λ k₀ → k₀ ≺ r × Home tB k₀ × instantOf k₀ ≡ instantOf k)
                      ⊎ Σ Pos λ h → (HP ∪ʰ o) h × instantOf h ≡ instantOf k)

  img-fun : ∀ {k l l′} → LaneImg k l → LaneImg k l′ → l ≡ l′
  img-fun (_ , _ , _ , v , i , _) (_ , _ , _ , v′ , i′ , _) = img-apart v v′ i i′

  pb-img : ∀ {k l l′} → LanePB k l → LaneImg k l′ → ⊥
  pb-img (_ , _ , _ , v , pb , _) (_ , _ , _ , v′ , i , _) = pb-apart v v′ pb i

  -- A lane's row carried into its instant may lie in its value's: the
  -- outer's rows stand with the environment's hots, its echo carrying
  -- them once the joiner sits under its outer's connect.
  carried : CarryAt valuesOf N (HP ∪ʰ o) HE LP′ tB u p p′
  carried = record
    { Img = LaneImg ; ext = ext ; PB = LanePB ; pb-few = join-pb-few ; pb-img = pb-img ; pb-past = join-pb-past
    ; img = join-img ; img¬¬ = join-img¬¬ ; shown = join-shown ; img-row = join-img-row ; img-fun = img-fun
    ; place = join-place ; live = join-live ; few = few ; whole = join-whole ; cover = join-cover ; bk = proj₁ join-bk
    ; in-bk = proj₂ join-bk ; pinned = join-pinned }
