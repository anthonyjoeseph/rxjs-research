{-# OPTIONS --guardedness #-}

-- A FLATMAP IS CARRIED when its outer and its lanes are.  The outer is
-- subscribed where the flatMap is plainly and, elaborated, as its
-- connect's source; the lanes ride that connect's body, whose rows the
-- lanes' carry pairs.
module simultaneous.CarryFlat where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using (_∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.Nat using (ℕ)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; flatMap; connect; connected)
open import denotation.Position using (Pos; Label; ix; sub; _⊕_; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; end; Unpinned; EmissionSet; Truncate; Proper; Den; hot; enter; DenEnv; approx; Ended; LaneOf;
  module Joining; module Op; module Bounded; module Switch; module Exhaust; module Connect)
open import denotation.Laws.Worlds using (⊑-inside; ⊕-assoc; Hots; GoodEnv; Ok; ok-step; InvAt; InvD; _∪ʰ_; inW)
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
open import simultaneous.JoinCarry using (module Joined)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; E; elab; closer; laneˢ; each; combined; trackers; Routes)

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

-- THE PLAIN FLATMAP IS ITS JOINER over the parts.
joins-flat : ∀ {A B} op (g : A → Den B) (sD : Den A) p
           → Truncate (Joining.JoinT (Parts.Ln g (enter sD p) op) (enter sD p) (λ _ _ → ⊥) (Ended (enter sD p))
                (Parts.Runs g (enter sD p) op) (Parts.Cut g (enter sD p) op) (Parts.Hand g (enter sD p) op))
             ≡ enter (Op.flatMap op g sD) p
joins-flat (mergeᶠ nothing)  g sD p = refl
joins-flat (mergeᶠ (just m)) g sD p = refl
joins-flat switchᶠ           g sD p = refl
joins-flat exhaustᶠ          g sD p = refl

-- ONLY A SWITCH CUTS, only a bounded merge hands off, and only a bounded
-- merge or an exhaust runs some values and not others.
cut-by : ∀ {A B A′ B′} (g : A → Den B) (o : EmissionSet A) (g′ : A′ → Den B′) (o′ : EmissionSet A′) op {q k q′ k′}
       → (op ≡ switchᶠ → Parts.Cut g o op q k ⇔ Parts.Cut g′ o′ op q′ k′) → Parts.Cut g o op q k ⇔ Parts.Cut g′ o′ op q′ k′
cut-by g o g′ o′ (mergeᶠ nothing)  h = mk⇔ (λ ()) (λ ())
cut-by g o g′ o′ (mergeᶠ (just m)) h = mk⇔ (λ ()) (λ ())
cut-by g o g′ o′ switchᶠ           h = h refl
cut-by g o g′ o′ exhaustᶠ          h = mk⇔ (λ ()) (λ ())

hand-by : ∀ {A B A′ B′} (g : A → Den B) (o : EmissionSet A) (g′ : A′ → Den B′) (o′ : EmissionSet A′) op {c c′}
        → (∀ m → op ≡ mergeᶠ (just m) → Parts.Hand g o op c ⇔ Parts.Hand g′ o′ op c′) → Parts.Hand g o op c ⇔ Parts.Hand g′ o′ op c′
hand-by g o g′ o′ (mergeᶠ nothing)  h = mk⇔ (λ ()) (λ ())
hand-by g o g′ o′ (mergeᶠ (just m)) h = h m refl
hand-by g o g′ o′ switchᶠ           h = mk⇔ (λ ()) (λ ())
hand-by g o g′ o′ exhaustᶠ          h = mk⇔ (λ ()) (λ ())

runs-by : ∀ {A B A′ B′} (g : A → Den B) (o : EmissionSet A) (g′ : A′ → Den B′) (o′ : EmissionSet A′) op {q q′}
        → (∀ m → op ≡ mergeᶠ (just m) → Parts.Runs g o op q → Parts.Runs g′ o′ op q′) → (op ≡ exhaustᶠ → Parts.Runs g o op q → Parts.Runs g′ o′ op q′)
        → Parts.Runs g o op q → Parts.Runs g′ o′ op q′
runs-by g o g′ o′ (mergeᶠ nothing)  b x r = tt
runs-by g o g′ o′ (mergeᶠ (just m)) b x r = b m refl r
runs-by g o g′ o′ switchᶠ           b x r = tt
runs-by g o g′ o′ exhaustᶠ          b x r = x refl r

-- CARRIED from the plain rows `T` into the elaborated program `X`: what
-- `CarriesAt` asks, the plain run given only by its rows.  A record,
-- compared by its arguments: a type that unfolds at a named elaborated
-- flatMap unfolds the whole program, even against its own spelling.
record CarriesOf (n : ℕ) {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (envP : DenEnv Γ) (envE : DenEnv Δ) (M₀ : PMap)
                 (er : EnvRel M₀ ρ envP envE) (p p′ : Pos) (T : EmissionSet A) (X : E Δ (IE A)) : Set₁ where
  constructor held
  field
    unheld : Σ PMap λ M → M₀ ⊆ᴹ M × Emb M × Within (Hots envP) M₀ M p × Bare M T × Joins ρ envP envE er M × EnvPast er M
             × Σ (CarryAt valuesOf M (Hots envP) (Hots envE) (HotsListed envP) T (enter (approx n X envE) p′) p p′) (λ c → PBNest er M c × Narrow c)

-- Carried at every subscription, held to rows: checked over a program
-- held abstract, so no program is unfolded.
carry-of : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A)
         → (∀ (envP : DenEnv Γ) (envE : DenEnv Δ) → GoodEnv envP → GoodEnv envE
            → ∀ M₀ → Emb M₀ → (er : EnvRel M₀ ρ envP envE) → Joins ρ envP envE er M₀ → Nests er M₀ → Apart envP
            → ∀ p p′ → M₀ p (p′ ⊕ foot o) → Ok (Hots envP) p → Ok (Hots envE) p′ → Clear (Rows er) (Hots envP) p → Fresh (Hots envP) M₀ p
            → CarriesOf n ρ envP envE M₀ er p p′ (enter (approx n o envP) p) (elab ρ o))
         → Carry n ρ o
carry-of n ρ o h = carry λ envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr →
  CarriesOf.unheld (h envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr)

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
  CarriesX X = CarriesOf n ρ envP envE M₀ er p p′ t X

  -- Moved along the plain run's equation, over a program held abstract.
  along : ∀ {X} {T : EmissionSet B} → t ≡ T → CarriesX X → CarriesOf n ρ envP envE M₀ er p p′ T X
  along refl c = c

  -- The elaborated lanes' renaming: past the outer's and the closer's
  -- binders.
  ρ″ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ (IE B L.∷ IE A L.∷ Δ)
  ρ″ i = there (there (ρ i))

  -- THE ELABORATED FLATMAP'S BODY, over its lanes and the connects it
  -- watches: the closer's connect over the joiner's, read by the routing
  -- scan.
  Body : (A → E (IE B L.∷ IE A L.∷ Δ) (IE B)) → E (IE B L.∷ IE B L.∷ IE A L.∷ Δ) (ℕ × Routes) → E (IE A L.∷ Δ) (IE B)
  Body lanesE tk = connect closer (connect (flatMap op (λ a → laneˢ (lanesE a)) (each valuesOf (connected (there (here refl))))) (combined op tk))

  -- THE ELABORATED FLATMAP IS A CONNECT over the elaborated outer, its
  -- body read off `elab` itself.  The assembly runs over the lanes and
  -- trackers held abstract and is moved along this equation: compared
  -- against `elab`'s unfolding, any other spelling unfolds the whole
  -- program.
  split : Σ (A → E (IE B L.∷ IE A L.∷ Δ) (IE B)) λ lanesE → (∀ a → lanesE a ≡ elab ρ″ (f a))
          × Σ (E (IE B L.∷ IE B L.∷ IE A L.∷ Δ) (ℕ × Routes)) λ tk → tk ≡ trackers Γ 0 (λ i → there (there (there (ρ i))))
          × elab ρ (flatMap op f s) ≡ connect (elab ρ s) (connect closer (connect (flatMap op (λ a → laneˢ (lanesE a))
              (each valuesOf (connected (there (here refl))))) (combined op tk)))
  split = _ , (λ a → refl) , _ , refl , refl

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
      LaneCarry M_b = CarryAt valuesOf M_b (Hots envP ∪ʰ o) (Hots envE ∪ʰ Proper FW.CE.σ) (λ q → Listed o q × HotsListed envP q) FW.tB FW.CE.β p (p′ ⊕ [ ix 0 ])

      -- A lane's late carrier strictly under a value's row, anchored.
      NestAt : ∀ {M_b : PMap} {H : Pos → Set} {u : EmissionSet (IE B)} {s′ : Pos} → CarryAt valuesOf M_b (Hots envP ∪ʰ o) H (λ q → Listed o q × HotsListed envP q) FW.tB u p s′ → Set
      NestAt {M_b} c = ∀ {k l : Pos} {e₀ : Ev B} {h L : Pos} {a : Label} {σ : L.List Label} → CarryAt.PB c k l → FW.tB k e₀ → (Unpinned e₀ → Live FW.tB k) → Σ A (λ b → o h (out b)) → FW.S′.Img h L
                     → k ≡ h ⊕ (a ∷ σ) → Anchor M_b k l h a

      NestV : (M_b : PMap) → LaneCarry M_b → Set
      NestV M_b c_b = NestAt {M_b} {Hots envE ∪ʰ Proper FW.CE.σ} {FW.CE.β} {p′ ⊕ [ ix 0 ]} c_b

      -- What the lanes' map keeps: past the outer's, every row in the
      -- world, nothing under a row, nothing under a value but under its
      -- second child, each binder's late carriers past it, and the
      -- outer's.
      Maps : PMap → Set₁
      Maps M_b = M_s ⊆ᴹ M_b × Emb M_b × Within (Hots envP) M_s M_b p × Bare M_b FW.t × FW.LaneHere M_b
                 × Joins ρ envP envE er₂ M_b × EnvPast er₂ M_b × PastOver c_s M_b

      -- The lanes carried into `u`, subscribed at `s′`, under the hots `H`,
      -- their late carriers anchored.
      Staged : PMap → (Pos → Set) → EmissionSet (IE B) → Pos → Set₁
      Staged M_b H u s′ = Σ (CarryAt valuesOf M_b (Hots envP ∪ʰ o) H (λ q → Listed o q × HotsListed envP q) FW.tB u p s′) λ c → PBNest er₂ M_b c × NestAt {M_b} {H} {u} {s′} c

      -- THE LANES ARE CARRIED by the connect's body: every lane row past the
      -- outer's map, nothing paired under a value but under its second
      -- child, each binder's late carriers past it, and the outer's.
      LanesFact : Set₁
      LanesFact = Σ PMap λ M_b → M_s ⊆ᴹ M_b × Emb M_b × Within (Hots envP) M_s M_b p × Bare M_b FW.t × FW.LaneHere M_b
                  × Joins ρ envP envE er₂ M_b × EnvPast er₂ M_b × PastOver c_s M_b
                  × Σ (LaneCarry M_b) λ c_b → PBNest er₂ M_b c_b × NestV M_b c_b

      -- Checked here, the body abstract: at the elaborated body the
      -- comparison unfolds it.
      landed : ∀ M_b → Maps M_b → Staged M_b (Hots envE ∪ʰ Proper FW.CE.σ) FW.CE.β (p′ ⊕ [ ix 0 ]) → LanesFact
      landed M_b (ms_b , hm_b , wi_b , br_b , lh , jn_b , ep_b , past-s) (c_b , nc_b , nest-v) =
        M_b , ms_b , hm_b , wi_b , br_b , lh , jn_b , ep_b , past-s , c_b , nc_b , nest-v

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

        past′ : EnvPast er FB.M′
        past′ = grown-past {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} er past-b (λ {x} {y} → grown′ {x} {y})

        -- Typed apart: inferred inside the tuple, the carry's type is
        -- compared against `CarriesX` far more slowly.
        carry′ : Σ (CarryAt valuesOf FB.M′ (Hots envP) (Hots envE) (HotsListed envP) t (enter (approx n (connect (elab ρ s) bE) envE) p′) p p′)
                   (λ c → PBNest er FB.M′ c × Narrow c)
        carry′ = FB.carried , nest , FB.narrowed

        result : CarriesX (connect (elab ρ s) bE)
        result = held (FB.M′ , (λ m → inj₁ (ms_b (ms_s m))) , emb′ , within′ , bare′ , joins″ , past′ , carry′)

      result : LanesFact → CarriesX (connect (elab ρ s) bE)
      result (M_b , ms_b , hm_b , wi_b , br_b , lh , jn_b , ep_b , past-s , c_b , nc_b , nest-v) =
        Lanes.result M_b ms_b hm_b wi_b br_b lh jn_b ep_b past-s c_b nc_b nest-v

    -- THE LANES' CARRY, STAGE BY STAGE through the elaborated body: the
    -- joiner over the carried lanes, read by the routing scan, under the
    -- joiner's connect, under the closer's.
    module Staged (lanesE : A → E (IE B L.∷ IE A L.∷ Δ) (IE B)) (tk : E (IE B L.∷ IE B L.∷ IE A L.∷ Δ) (ℕ × Routes))
                  (eL : ∀ a → lanesE a ≡ elab ρ″ (f a)) (eT : tk ≡ trackers Γ 0 (λ i → there (there (there (ρ i))))) where
      open AtBody (Body lanesE tk)

      -- The joiner over the lanes, its outer the elaborated outer's values.
      X : E (IE B L.∷ IE A L.∷ Δ) (IE B)
      X = flatMap op (λ a → laneˢ (lanesE a)) (each valuesOf (connected (there (here refl))))

      env₁ : DenEnv (IE A L.∷ Δ)
      env₁ = hot (Proper FW.CE.σ) ∷ envE

      -- The closer's connect, at the body's subscription.
      module C₁ = Connect (approx n closer env₁) (λ h → approx n (connect X (combined op tk)) (h ∷ env₁)) (p′ ⊕ [ ix 0 ])

      env₂ : DenEnv (IE B L.∷ IE A L.∷ Δ)
      env₂ = hot (Proper C₁.σ) ∷ env₁

      -- The joiner's connect, at the closer's body.
      module C₂ = Connect (approx n X env₂) (λ h → approx n (combined op tk) (h ∷ env₂)) (p′ ⊕ [ ix 0 ] ⊕ [ ix 0 ])

      H₂ H₃ : Pos → Set
      H₂ = (Hots envE ∪ʰ Proper FW.CE.σ) ∪ʰ Proper C₁.σ
      H₃ = H₂ ∪ʰ Proper C₂.σ

      -- THE JOINER OVER THE CARRIED LANES: its outer the elaborated
      -- outer's values read back, each plain running value paired with
      -- the value its carrier reads, its lane carried into the partner's.
      q₁ : Pos
      q₁ = p′ ⊕ [ ix 0 ] ⊕ [ ix 0 ] ⊕ [ ix 1 ]

      oE : Den A
      oE = approx n (each valuesOf (connected (there (here refl)))) env₂

      lE : A → Den (IE B)
      lE a = approx n (laneˢ (lanesE a)) env₂

      o* : EmissionSet A
      o* = enter oE q₁

      module P* = Parts lE o*

      V : Pos → A → Pos → Set
      V q a q* = o q (out a) × P.Runs op q × o* q* (out a) × P*.Runs op q*
                 × Σ Pos λ l → FW.S′.Img q l × q* ≡ ((l ⊕ [ sub q₁ ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]

      postulate
        -- Each paired value's lane, carried through the lane's frame.
        lane-framed : ∀ {q a q*} → V q a q* → Σ PMap λ M_l → Σ Pos λ s → Σ Pos λ s*
                    → CarryAt valuesOf M_l (Hots envP) H₂ (HotsListed envP) (P.Ln op q a) (P*.Ln op q* a) s s*

      LI : ∀ {q a q*} → V q a q* → Pos → Pos → Set
      LI v = CarryAt.Img (proj₂ (proj₂ (proj₂ (lane-framed v))))

      postulate
        -- Two lanes' rows lie apart, each imaged once.
        lanes-apart : ∀ {q a q* q′ a′ q*′} (v : V q a q*) (v′ : V q′ a′ q*′) {k l l′} → LI v k l → LI v′ k l′ → l ≡ l′
        lanes-pb-apart : ∀ {q a q* q′ a′ q*′} (v : V q a q*) (v′ : V q′ a′ q*′) {k l l′}
                       → CarryAt.PB (proj₂ (proj₂ (proj₂ (lane-framed v)))) k l → LI v′ k l′ → ⊥
        -- THE ELABORATED JOINER DECIDES AS THE PLAIN ONE: each running
        -- value paired, a lane cut where its partner is, its end joined
        -- and handed off where its partner's is.
        -- A listed value's carrier, read back as the elaborated outer's.
        read-value : ∀ {q a} → o q (out a) → Listed o q → HotsListed envP q
                   → Σ Pos λ l → FW.S′.Img q l × o* (((l ⊕ [ sub q₁ ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) (out a)
        -- A bounded or exhaust value runs where its partner does.
        bounded-runs : ∀ m → op ≡ mergeᶠ (just m) → ∀ {q a l} → o q (out a) → FW.S′.Img q l → P.Runs op q
                     → P*.Runs op (((l ⊕ [ sub q₁ ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ])
        exhaust-runs : op ≡ exhaustᶠ → ∀ {q a l} → o q (out a) → FW.S′.Img q l → P.Runs op q
                     → P*.Runs op (((l ⊕ [ sub q₁ ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ])
        -- A switch's lane is cut where its partner is.
        switch-cut : op ≡ switchᶠ → ∀ {q a q*} (v : V q a q*) {k l} → LI v k l → P.Cut op q k ⇔ P*.Cut op q* l
        pair-done : ∀ {q a q*} (v : V q a q*) {c c*} → LI v c c* → P.Ln op q a c end
                  → Joining.Done (P.Ln op) o (λ _ _ → ⊥) (Ended o) (P.Runs op) (P.Cut op) (P.Hand op) c
                    ⇔ Joining.Done (P*.Ln op) o* (λ _ _ → ⊥) (Ended o*) (P*.Runs op) (P*.Cut op) (P*.Hand op) c*
        -- A bounded lane's end hands off where its partner's does.
        bounded-hand : ∀ m → op ≡ mergeᶠ (just m) → ∀ {q a q*} (v : V q a q*) {c c*} → LI v c c* → P.Ln op q a c end
                     → P.Hand op c ⇔ P*.Hand op c*

      pair-all : ∀ {q a} → o q (out a) → P.Runs op q → Listed o q → HotsListed envP q → Σ Pos (V q a)
      pair-all x r ls lp =
        let (l , i , x*) = read-value x ls lp
        in _ , x , r , x* , runs-by g o lE o* op (λ m e → bounded-runs m e x i) (λ e → exhaust-runs e x i) r , l , i , refl

      pair-cut : ∀ {q a q*} (v : V q a q*) {k l} → LI v k l → P.Cut op q k ⇔ P*.Cut op q* l
      pair-cut v i = cut-by g o lE o* op λ e → switch-cut e v i

      pair-hand : ∀ {q a q*} (v : V q a q*) {c c*} → LI v c c* → P.Ln op q a c end → P.Hand op c ⇔ P*.Hand op c*
      pair-hand v i y = hand-by g o lE o* op λ m e → bounded-hand m e v i y

      N : PMap
      N = M_s ∪ᴹ λ x y → Σ Pos λ q → Σ A λ a → Σ Pos λ q* → Σ (V q a q*) λ v → proj₁ (lane-framed v) x y

      module JD = Joined {HP = Hots envP} {HE = H₂} {LP = HotsListed envP} p q₁ o (P.Ln op) (P.Runs op) (P.Cut op) (P.Hand op)
                    o* (P*.Ln op) (P*.Runs op) (P*.Cut op) (P*.Hand op) V (λ (x , r , x* , r* , _) → x , r , x* , r*)
                    N (λ v → proj₁ (lane-framed v)) (λ {q} {a} {q*} v m → inj₂ (q , a , q* , v , m)) (λ v → proj₂ (lane-framed v))
                    lanes-apart lanes-pb-apart pair-all pair-cut pair-done pair-hand

      postulate
        -- The lanes' map keeps what the outer's does.
        joined-maps : Maps N
        -- The joined lanes' late carriers nest and are anchored.
        joined-nest : PBNest er₂ N JD.carried × NestAt {N} {H₂} {JD.u} {q₁} JD.carried

      shift : ∀ {U} → JD.u ≡ U → Staged N H₂ JD.u q₁ → Staged N H₂ U q₁
      shift refl c = c

      lanes-joined : Σ PMap λ M_b → Maps M_b × Staged M_b H₂ C₂.σ q₁
      lanes-joined = N , joined-maps , shift (joins-flat op lE oE q₁) (JD.carried , joined-nest)

      postulate
        lanes-routed : ∀ {M_b} → Maps M_b → Staged M_b H₂ C₂.σ (p′ ⊕ [ ix 0 ] ⊕ [ ix 0 ] ⊕ [ ix 1 ])
                     → Staged M_b H₃ C₂.β (p′ ⊕ [ ix 0 ] ⊕ [ ix 0 ] ⊕ [ ix 0 ])
        lanes-inner : ∀ {M_b} → Maps M_b → Staged M_b H₃ C₂.β (p′ ⊕ [ ix 0 ] ⊕ [ ix 0 ] ⊕ [ ix 0 ])
                    → Staged M_b H₂ C₁.β (p′ ⊕ [ ix 0 ] ⊕ [ ix 0 ])
        lanes-closer : ∀ {M_b} → Maps M_b → Staged M_b H₂ C₁.β (p′ ⊕ [ ix 0 ] ⊕ [ ix 0 ])
                     → Staged M_b (Hots envE ∪ʰ Proper FW.CE.σ) FW.CE.β (p′ ⊕ [ ix 0 ])

      through : Σ PMap (λ M_b → Maps M_b × Staged M_b H₂ C₂.σ (p′ ⊕ [ ix 0 ] ⊕ [ ix 0 ] ⊕ [ ix 1 ])) → LanesFact
      through (M_b , mp , sX) = landed M_b mp (lanes-closer mp (lanes-inner mp (lanes-routed mp sX)))

      staged : LanesFact
      staged = through lanes-joined

  -- MOVED ALONG THE EQUATION, the body held abstract: the result's type
  -- names no body, so nothing is unified against the elaborated program
  -- before the body is known.
  module Moved (bE : E (IE A L.∷ Δ) (IE B)) (eq : elab ρ (flatMap op f s) ≡ connect (elab ρ s) bE)
               -- the lanes carried past every carry of the outer
               (lanes : ∀ (M_s : PMap) (ms_s : M₀ ⊆ᴹ M_s) (hm_s : Emb M_s) (wi_s : Within (Hots envP) M₀ M_s p) (br_s : Bare M_s o)
                          (jn_s : Joins ρ envP envE er M_s) (ep_s : EnvPast er M_s)
                          (c_s : CarryAt valuesOf M_s (Hots envP) (Hots envE) (HotsListed envP) o (enter (approx n (elab ρ s) envE) (p′ ⊕ [ ix 1 ])) p (p′ ⊕ [ ix 1 ]))
                          (nc_s : PBNest er M_s c_s) → AfterSource.AtBody.LanesFact M_s ms_s hm_s wi_s br_s jn_s ep_s c_s nc_s bE) where
    after : CarriesAt n ρ s envP envE M₀ er p (p′ ⊕ [ ix 1 ]) → CarriesX (connect (elab ρ s) bE)
    after (M_s , ms_s , hm_s , wi_s , br_s , jn_s , ep_s , c_s , nc_s , _) =
      AfterSource.AtBody.result M_s ms_s hm_s wi_s br_s jn_s ep_s c_s nc_s bE (lanes M_s ms_s hm_s wi_s br_s jn_s ep_s c_s nc_s)

    moved : (Y : E Δ (IE B)) → Y ≡ connect (elab ρ s) bE → CarriesX (connect (elab ρ s) bE) → CarriesX Y
    moved _ refl c = c

    result : CarriesX (elab ρ (flatMap op f s))
    result = moved (elab ρ (flatMap op f s)) eq (after (Carry.carries hs envP envE gP gE M₀ hm er jn ns ap p (p′ ⊕ [ ix 1 ]) (subst (M₀ p) (sym (⊕-assoc p′ [ ix 1 ] (foot s))) m₀)
                      okP (ok-step p′ okE) nh fr))

  result : CarriesOf n ρ envP envE M₀ er p p′ (enter (approx n (flatMap op f s) envP) p) (elab ρ (flatMap op f s))
  result with split
  ... | lanesE , eL , tk , eT , eq = along (joins-flat op g (approx n s envP) p)
          (Moved.result (Body lanesE tk) eq (λ M_s ms_s hm_s wi_s br_s jn_s ep_s c_s nc_s → AfterSource.Staged.staged M_s ms_s hm_s wi_s br_s jn_s ep_s c_s nc_s lanesE tk eL eT))

-- A `flatMap` carries when its outer and its lanes do.
carry-flatMap : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) s → Carry m ρ s
              → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → Carry m ρ′ (f a)) → Carry m ρ (flatMap op f s)
carry-flatMap n ρ op f s hs hf = carry-of n ρ (flatMap op f s) λ envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr →
  Assembly.result n ρ op f s hs hf envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr
