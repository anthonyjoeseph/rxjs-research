{-# OPTIONS --guardedness #-}

-- A FLATMAP IS CARRIED when its outer and its lanes are.  The outer is
-- subscribed where the flatMap is plainly and, elaborated, as its
-- connect's source; the lanes ride that connect's body, whose rows the
-- lanes' carry pairs.
module simultaneous.CarryFlat where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.List using (_∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; flatMap; connect; connected)
open import denotation.Position using (Pos; Label; ix; _⊕_; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; Unpinned; EmissionSet; Truncate; Proper; Den; hot; enter; DenEnv; approx; Ended; LaneOf;
  module Joining; module Connect; module Bounded; module Switch; module Exhaust)
open import denotation.Laws.Worlds using (_⊑_; ⊑-trans; ⊑-snoc⁺; ⊑-inside; ⊕-assoc; Hots; GoodEnv; Ok; ok-step; InvAt; Lawful; InvD; _∪ʰ_;
  inW; step; plain-ix)
open import denotation.Laws using (inv-approx; good-cons)
open import denotation.Laws.Truth.Joining using (Slots)
open import denotation.Laws.Truth.Join using (module JoinerSide)
open import denotation.Laws.Truth.Bounded using (module BoundedSide)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.Attribution using (Live)
open import simultaneous.Listing using (Listed)
open import simultaneous.CarryBase using (PMap; _∪ᴹ_; _⊆ᴹ_; Emb; Fresh; CarryAt; Narrow)
open import simultaneous.Carry using (Carry; carry; CarriesAt; Within; Bare; EnvRel; HotsListed; Grown; Joins; joins-grow; Apart; EnvPast;
  PastOver; PBNest; Nests; Anchor; bound-hot; grown-past; Clear; Rows; foot)
open import simultaneous.CarryDefer using (env-grow; past-shrink; joins-shrink)
open import simultaneous.FlatWrap using (module FlatCarry)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; E; elab; closer; laneˢ; each; combined; trackers)

------------------------------------------------------------------------
-- The joiners

-- EACH JOINER'S PARTS: its lanes, which values run one, where a lane is
-- cut, and which ends hand off to a queued lane.
module Parts {A B : Set} (g : A → Den B) (o : EmissionSet A) where
  Ln : FlatOp → Pos → A → EmissionSet B
  Ln (mergeᶠ nothing)  = LaneOf g
  Ln (mergeᶠ (just m)) = Bounded.Lane m g o
  Ln switchᶠ           = LaneOf g
  Ln exhaustᶠ          = LaneOf g

  Runs : FlatOp → Pos → Set
  Runs (mergeᶠ nothing)  = λ _ → ⊤
  Runs (mergeᶠ (just m)) = Bounded.Indexed m g o
  Runs switchᶠ           = λ _ → ⊤
  Runs exhaustᶠ          = Exhaust.Run g o

  Cut : FlatOp → Pos → Pos → Set
  Cut (mergeᶠ nothing)  = λ _ _ → ⊥
  Cut (mergeᶠ (just m)) = λ _ _ → ⊥
  Cut switchᶠ           = Switch.Cut g o
  Cut exhaustᶠ          = λ _ _ → ⊥

  Hand : FlatOp → Pos → Set
  Hand (mergeᶠ nothing)  = λ _ → ⊥
  Hand (mergeᶠ (just m)) = Bounded.Queued m g o
  Hand switchᶠ           = λ _ → ⊥
  Hand exhaustᶠ          = λ _ → ⊥

  slots : ∀ op {H p} → Ok H p → (∀ a → InvD H (g a)) → InvAt H p o → Slots H g o (Ln op)
  slots (mergeᶠ nothing)  ok Ig Io = JoinerSide.slots ok g Ig Io
  slots (mergeᶠ (just m)) ok Ig Io = BoundedSide.slots ok m g Ig Io
  slots switchᶠ           ok Ig Io = JoinerSide.slots ok g Ig Io
  slots exhaustᶠ          ok Ig Io = JoinerSide.slots ok g Ig Io

------------------------------------------------------------------------
-- The assembly

module Assembly {Γ Δ A B} (n : ℕ) (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (op : FlatOp) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
                (hs : Carry n ρ s) (hf : ∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → Carry n ρ′ (f a))
                (envP : DenEnv Γ) (envE : DenEnv Δ) (gP : GoodEnv envP) (gE : GoodEnv envE) (M₀ : PMap) (hm : Emb M₀)
                (er : EnvRel M₀ ρ envP envE) (jn : Joins ρ envP envE er M₀) (ns : Nests er M₀) (ap : Apart envP)
                (p p′ : Pos) (m₀ : M₀ p (p′ ⊕ (ix 1 ∷ foot s))) (okP : Ok (Hots envP) p) (okE : Ok (Hots envE) p′)
                (nh : Clear (Rows er) (Hots envP) p) (fr : Fresh (Hots envP) M₀ p) where
  g : A → Den B
  g a = approx n (f a) envP

  Ig : ∀ a → InvD (Hots envP) (g a)
  Ig a = inv-approx n (f a) envP gP

  o : EmissionSet A
  o = enter (approx n s envP) p

  Io : InvAt (Hots envP) p o
  Io = inv-approx n s envP gP p okP

  module P = Parts g o
  module J = Joining (P.Ln op) o (λ _ _ → ⊥) (Ended o) (P.Runs op) (P.Cut op) (P.Hand op)

  t : EmissionSet B
  t = Truncate J.JoinT

  -- Carried into the run of an elaborated program `X`.
  CarriesX : E Δ (IE B) → Set₁
  CarriesX X = Σ PMap λ M → M₀ ⊆ᴹ M × Emb M × Within (Hots envP) M₀ M p × Bare M t × Joins ρ envP envE er M × EnvPast er M
             × Σ (CarryAt valuesOf M (Hots envP) (Hots envE) (HotsListed envP) t (enter (approx n X envE) p′) p p′) (λ c → PBNest er M c × Narrow c)

  Carries : Set₁
  Carries = CarriesX (elab ρ (flatMap op f s))

  -- THE ELABORATED FLATMAP IS A CONNECT over the elaborated outer, its
  -- body read off `elab` itself.  The assembly runs over a body held
  -- abstract and is moved along this equation: compared against `elab`'s
  -- unfolding, any other spelling of the body unfolds the whole program.
  split : Σ (E (IE A L.∷ Δ) (IE B)) λ b → elab ρ (flatMap op f s) ≡ connect (elab ρ s) b
  split = _ , refl

  -- Past the outer.
  module AfterSource (M_s : PMap) (ms_s : M₀ ⊆ᴹ M_s) (hm_s : Emb M_s) (wi_s : Within (Hots envP) M₀ M_s p) (br_s : Bare M_s o)
                     (jn_s : Joins ρ envP envE er M_s) (ep_s : EnvPast er M_s)
                     (c_s : CarryAt valuesOf M_s (Hots envP) (Hots envE) (HotsListed envP) o (enter (approx n (elab ρ s) envE) (p′ ⊕ [ ix 1 ])) p (p′ ⊕ [ ix 1 ]))
                     (nc_s : PBNest er M_s c_s) where
    er₂ : EnvRel M_s ρ envP envE
    er₂ = env-grow {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} ms_s er ep_s

    module AtBody (bE : E (IE A L.∷ Δ) (IE B)) where
      module FW = FlatCarry {HP = Hots envP} {HE = Hots envE} {LP = HotsListed envP} p p′ okP okE Io g Ig (P.Ln op) (P.Runs op) (P.Cut op) (P.Hand op)
                    (P.slots op okP Ig Io) {sE = approx n (elab ρ s) envE} {FE = λ h → approx n bE (h ∷ envE)}
                    (inv-approx n (elab ρ s) envE gE) (λ {t} L → inv-approx n bE (hot t ∷ envE) (good-cons L gE)) M_s c_s

      -- The lanes' carry.
      LaneCarry : PMap → Set₁
      LaneCarry M_b = CarryAt valuesOf M_b (Hots envP) (Hots envE ∪ʰ Proper FW.CE.σ) (λ q → Listed o q × HotsListed envP q) FW.tB FW.CE.β p (p′ ⊕ [ ix 0 ])

      -- A lane's late carrier strictly under a value's row, anchored.
      NestV : (M_b : PMap) → LaneCarry M_b → Set
      NestV M_b c_b = ∀ {k l e₀ h L a σ} → CarryAt.PB c_b k l → FW.tB k e₀ → (Unpinned e₀ → Live FW.tB k) → Σ A (λ b → o h (out b)) → FW.S′.Img h L
                    → k ≡ h ⊕ (a ∷ σ) → Anchor M_b k l h a

      -- THE LANES ARE CARRIED by the connect's body: every lane row past the
      -- outer's map, nothing paired under a value but under its second
      -- child, each binder's late carriers past it, and the outer's.
      LanesFact : Set₁
      LanesFact = Σ PMap λ M_b → M_s ⊆ᴹ M_b × Emb M_b × Within (Hots envP) M_s M_b p × Bare M_b FW.t × FW.LaneHere M_b
                  × Joins ρ envP envE er₂ M_b × EnvPast er₂ M_b × PastOver c_s M_b
                  × Σ (LaneCarry M_b) λ c_b → PBNest er₂ M_b c_b × NestV M_b c_b

      module Lanes (M_b : PMap) (ms_b : M_s ⊆ᴹ M_b) (hm_b : Emb M_b) (wi_b : Within (Hots envP) M_s M_b p) (br_b : Bare M_b FW.t)
                   (lh : FW.LaneHere M_b) (jn_b : Joins ρ envP envE er₂ M_b) (ep_b : EnvPast er₂ M_b) (past-s : PastOver c_s M_b)
                   (c_b : LaneCarry M_b) (nc_b : PBNest er₂ M_b c_b) (nest-v : NestV M_b c_b) where
        emb′ : Emb (M_b ∪ᴹ FW.Echo)
        emb′ = FW.Paired.emb′ M_b ms_b hm_b lh

        module FB = FW.Body M_b ms_b emb′ c_b past-s (λ {k} {l} {e₀} {h} {L} {a} {σ} → nest-v {k} {l} {e₀} {h} {L} {a} {σ})

        within′ : Within (Hots envP) M₀ FB.M′ p
        within′ (inj₁ m) = [ (λ ms → wi_s ms) , inj₂ ]′ (wi_b m)
        within′ (inj₂ e) = inj₂ (FW.echo-world e)

        bare′ : Bare FB.M′ t
        bare′ tk (inj₁ m) kx = br_b tk m kx
        bare′ tk (inj₂ e) kx = FW.echo-bare tk e kx

        -- An echo lies one label under its value's carrier, holding no hot
        -- row.
        grown′ : ∀ {x y} → FB.M′ x y → M_b x y ⊎ Grown M_b (Rows er) x y
        grown′ (inj₁ m) = inj₁ m
        grown′ (inj₂ e) =
          let (k₀ , y₀ , m₀ , yl , xe , w) = FW.echo-at e in inj₂ (k₀ , y₀ , ix 0 , ms_b m₀ , yl , xe , λ hq kq → nh hq (inW w) (⊑-inside kq))

        past-b : EnvPast er M_b
        past-b = past-shrink {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} ms_s er ep_s ep_b

        joins″ : Joins ρ envP envE er FB.M′
        joins″ = joins-grow {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} {er = er} {M = M_b} {N = FB.M′} inj₁
                   (joins-shrink {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} ms_s er ep_s jn_b) (λ {x} {y} → grown′ {x} {y})

        -- Its late carriers under a bound hot's row are anchored: the lanes'
        -- by the lanes' anchors, the outer's by the outer's.
        nest : PBNest er FB.M′ FB.carried
        nest i = FB.nest′ (λ {h} → bound-hot {ρ = λ {X} → ρ {X}} envP {envE = envE} er i {h})
                   (λ {k} {l} {e₀} {h} {L} {a} {σ} → nc_b i {k} {l} {e₀} {h} {L} {a} {σ})
                   (λ {k} {l} {e₀} {h} {L} {a} {σ} → nc_s i {k} {l} {e₀} {h} {L} {a} {σ})
                   (λ {k} {e} {x} {y} → br_s {k} {e} {x} {y})

        result : CarriesX (connect (elab ρ s) bE)
        result = FB.M′ , (λ m → inj₁ (ms_b (ms_s m))) , emb′ , within′ , bare′ , joins″
               , grown-past {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} er past-b (λ {x} {y} → grown′ {x} {y})
               , FB.carried , nest , FB.narrowed

      result : LanesFact → CarriesX (connect (elab ρ s) bE)
      result (M_b , ms_b , hm_b , wi_b , br_b , lh , jn_b , ep_b , past-s , c_b , nc_b , nest-v) =
        Lanes.result M_b ms_b hm_b wi_b br_b lh jn_b ep_b past-s c_b nc_b nest-v

    postulate
      flat-lanes : AtBody.LanesFact (proj₁ split)

    result : CarriesX (connect (elab ρ s) (proj₁ split))
    result = AtBody.result (proj₁ split) flat-lanes

  after : CarriesAt n ρ s envP envE M₀ er p (p′ ⊕ [ ix 1 ]) → CarriesX (connect (elab ρ s) (proj₁ split))
  after (M_s , ms_s , hm_s , wi_s , br_s , jn_s , ep_s , c_s , nc_s , _) = AfterSource.result M_s ms_s hm_s wi_s br_s jn_s ep_s c_s nc_s

  result : Carries
  result = subst CarriesX (sym (proj₂ split)) (after (Carry.carries hs envP envE gP gE M₀ hm er jn ns ap p (p′ ⊕ [ ix 1 ]) (subst (M₀ p) (sym (⊕-assoc p′ [ ix 1 ] (foot s))) m₀)
                    okP (ok-step p′ okE) nh fr))

-- A `flatMap` carries when its outer and its lanes do.
carry-flatMap : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) s → Carry m ρ s
              → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → Carry m ρ′ (f a)) → Carry m ρ (flatMap op f s)
carry-flatMap n ρ (mergeᶠ nothing) f s hs hf = carry λ envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr →
  Assembly.result n ρ (mergeᶠ nothing) f s hs hf envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr
carry-flatMap n ρ (mergeᶠ (just k)) f s hs hf = carry λ envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr →
  Assembly.result n ρ (mergeᶠ (just k)) f s hs hf envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr
carry-flatMap n ρ switchᶠ f s hs hf = carry λ envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr →
  Assembly.result n ρ switchᶠ f s hs hf envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr
carry-flatMap n ρ exhaustᶠ f s hs hf = carry λ envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr →
  Assembly.result n ρ exhaustᶠ f s hs hf envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr
