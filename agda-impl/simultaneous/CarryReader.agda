{-# OPTIONS --guardedness #-}

-- A READER CARRIES ITS HOT.  The plain reader of a bound hot shows each
-- row of the hot past its subscription, joined under it; the elaborated
-- reader reads the annotated hot so, then folds `joinStep` over what it
-- reads and sends each fold's emits, a reader joining late sending the
-- routes the hot holds first.  Every emit the annotated hot shows, the
-- reader sends, so the reader carries what the hot's carry carries.
--
-- The map grows by the reader's joins: each row of the hot past the
-- subscription, joined under it, put on its carrier joined under the
-- elaborated subscription; and the late end on the late end.  A hot row
-- holds the joins of every reader of it in their subscriptions' order
-- (`simultaneous.Carry.Joins`), so the map stays an embedding.
module simultaneous.CarryReader where

open import Data.List using ([]; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (lookup)
open import Data.Maybe using (nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (connected; mergeᶠ)
open import denotation.Position using (Pos; ix; sub; last; _⊕_; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Den; hot; enter; Proper; DenEnv; Truncate; Rejoin; _≺_; approx; module Op)
open import denotation.Laws.Worlds using (Hots; Ok; InvAt)
open import simultaneous.SObs using (module Elaborate)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.Carry using (PMap; _∪ᴹ_; _⊆ᴹ_; Emb; Fresh; Within; Bare; CarryAt; Carry; carry; EnvRel; Bound; HotsListed;
  NotHot; BoundRow; Joins; Apart; annValues)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) using (IE; AIE; elab; annotate; joinStep)

-- The elaborated reader's run over a handle: the fold of `joinStep`,
-- each fold's emits sent.
Reading : ∀ {X} → Den (AIE X) → Den (IE X)
Reading d = Op.flatMap (mergeᶠ nothing) (λ x → Op.of (proj₂ x)) (Op.scan joinStep (true , []) d)

-- THE READER'S SENDING carries what its reading carries: a fold's emits
-- are the emit it folds in, past the routes a late reader joins.
postulate
  read-post : ∀ {X : Set} {M : PMap} {HP HE LP H : Pos → Set} {t : EmissionSet X} {d′ : Den (AIE X)} {s s′}
            → InvAt H s′ (enter d′ s′) → CarryAt annValues M HP HE LP t (enter d′ s′) s s′
            → CarryAt valuesOf M HP HE LP t (enter (Reading d′) s′) s s′

-- A binder's hot, plain and annotated.
HotOf : ∀ {M₀ LP X} {d : Den X} {d′ : Den (AIE X)} → Bound M₀ LP d d′ → EmissionSet X
HotOf b = enter (approx (Bound.m b) (Bound.src b) (Bound.envP b)) (Bound.at b ⊕ [ ix 1 ])

HotOf′ : ∀ {M₀ LP X} {d : Den X} {d′ : Den (AIE X)} → Bound M₀ LP d d′ → EmissionSet (AIE X)
HotOf′ b = enter (approx (Bound.m b) (annotate (elab (Bound.σ b) (Bound.src b))) (Bound.envE b)) (Bound.at′ b ⊕ [ ix 1 ])

-- One reader of the binder `i`, subscribed at `p` and at its image `p′`.
module Read {Γ Δ} {M₀ : PMap} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {envP : DenEnv Γ} {envE : DenEnv Δ}
            (hm : Emb M₀) (er : EnvRel M₀ ρ envP envE) (jn : Joins ρ envP envE er M₀) (ap : Apart envP)
            {X} (i : X ∈ Γ) {p p′} (m₀ : M₀ p p′) (okP : Ok (Hots envP) p) (okE : Ok (Hots envE) p′)
            (nh : NotHot (Hots envP) p) (fr : Fresh (Hots envP) M₀ p) where
  private
    module C = CarryAt (Bound.carried (er i))

  T₀ : EmissionSet X
  T₀ = HotOf (er i)

  T₀′ : EmissionSet (AIE X)
  T₀′ = HotOf′ (er i)

  -- The reader's joins: a hot row past the subscription, joined under it,
  -- on its carrier joined under the image; and the late end.
  R : PMap
  R x y = (Σ Pos λ q → Σ Pos λ l → BoundRow (er i) q × C.Img q l × p ≺ q × x ≡ q ⊕ [ sub p ] × y ≡ l ⊕ [ sub p′ ])
        ⊎ (x ≡ p ⊕ [ last ] × y ≡ p′ ⊕ [ last ])

  M : PMap
  M = M₀ ∪ᴹ R

  postulate
    reader-emb      : Emb M
    reader-within   : Within (Hots envP) M₀ M p
    reader-bare     : Bare M (Truncate (Rejoin p (Proper T₀)))
    reader-joins    : Joins ρ envP envE er M
    reader-rejoined : CarryAt annValues M (Hots envP) (Hots envE) (HotsListed envP)
                        (Truncate (Rejoin p (Proper T₀))) (Truncate (Rejoin p′ (Proper T₀′))) p p′

------------------------------------------------------------------------
-- The former

private
  read-at : ∀ {Γ Δ} {M₀ : PMap} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {envP : DenEnv Γ} {envE : DenEnv Δ}
            (hm : Emb M₀) (er : EnvRel M₀ ρ envP envE) (jn : Joins ρ envP envE er M₀) (ap : Apart envP)
            {X} (i : X ∈ Γ) {p p′} (m₀ : M₀ p p′) (okP : Ok (Hots envP) p) (okE : Ok (Hots envE) p′)
            (nh : NotHot (Hots envP) p) (fr : Fresh (Hots envP) M₀ p) {dP : Den X} {dE : Den (AIE X)}
          → dP ≡ hot (Proper (HotOf (er i))) → dE ≡ hot (Proper (HotOf′ (er i))) → InvAt (Hots envE) p′ (enter dE p′)
          → Σ PMap λ M → M₀ ⊆ᴹ M × Emb M × Within (Hots envP) M₀ M p × Bare M (enter dP p) × Joins ρ envP envE er M
            × CarryAt valuesOf M (Hots envP) (Hots envE) (HotsListed envP) (enter dP p) (enter (Reading dE) p′) p p′
  read-at {M₀ = M₀} {ρ} {envP} {envE} hm er jn ap i m₀ okP okE nh fr refl refl Iu =
    R.M , inj₁ , R.reader-emb , R.reader-within , R.reader-bare , R.reader-joins , read-post {d′ = hot (Proper (HotOf′ (er i)))} Iu R.reader-rejoined
    where module R = Read {M₀ = M₀} {ρ = ρ} {envP = envP} {envE = envE} hm er jn ap i m₀ okP okE nh fr

-- A READER of a bound hot carries it.
carry-connected : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) → Carry m ρ (connected i)
carry-connected n ρ i = carry λ envP envE gP gE M₀ hm er jn ap p p′ m₀ okP okE nh fr →
  read-at {ρ = ρ} {envP = envP} {envE = envE} hm er jn ap i m₀ okP okE nh fr {dP = lookup envP i} {dE = lookup envE (ρ (∈-map⁺ AIE i))}
    (Bound.isP (er i)) (Bound.isE (er i)) (proj₁ (gE (ρ (∈-map⁺ AIE i))) p′ okE)
