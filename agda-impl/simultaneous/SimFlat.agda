{-# OPTIONS --guardedness #-}

-- A FLATMAP SIMULATES ITS FLATMAP.  The elaborated flatMap shares its
-- outer through a trigger's one row, so the outer is simulated at the
-- flatMap's own foot; the real flatMap inside reads that outer's values
-- and runs each lane framed (`laneˢ`), and a scan beside it relays the
-- lanes' rows.  So every plain lane value is its lane's carrier, framed
-- and relayed, and every end is the elaborated flatMap's end.
--
-- A merge, a switch and an exhaust are one joiner each, deciding which
-- values run (`RunsOf`) and where a lane is cut (`CutOf`) by the outer's
-- values and the lanes' ends: so each decision is read off the same
-- definitions on both sides.  A bounded merge's lanes start where
-- earlier lanes end, so its lane pairs follow its schedule
-- (`sim-bounded`).
--
-- The flatMap's map is its outer's, each running lane's subscription
-- pair and map, and its end paired with the elaborated end.
module simultaneous.SimFlat where

import Data.List as L
open import Data.List using (List; []; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Relation.Nullary using (¬_; Dec)
open import Relation.Nullary.Decidable using (_×-dec_)
open import Relation.Nullary.Decidable.Core using (T?)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; flatMap; connect; connected; of)
open import denotation.Position using (Pos; root; _≟ᵖ_; _<ᵖ_; _⊕_; ix; sub)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; end; EmissionSet; Den; hot; DenEnv; Proper; Truncate; Reach; Few; _≺_; _≼_; enter; approx; module Op;
  module Joiner; module Switch; module Exhaust; LaneOf)
open import denotation.Laws using (inv-approx; good-cons)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; ok-step; Lawful; InvAt; world-after; inW; plain-ix; _⊑_; ⊑-refl; ⊑-trans; ⊑-snoc⁺; ⊑-≼; ⊑-inside)
import denotation.Laws.Connect as LC
open import denotation.Laws.Shows using (few-reach)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext; ≺-≼-≺; ≼-≺-≺; ticks; entered-few; ≼-trans; ≺→≼; ≼-refl)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.ElabUndone using (Undone; elab-undone; env-u)
open import simultaneous.Sim using (PMap; _∪ᴹ_; _⊆ᴹ_; Emb; Fresh; Local; NoneUnder; Sim; Run; Lates; Mt; m-out; m-end; Carried; c-out; c-end;
  Upto; Under; Mapped; ListedB; Shows; Shown; HotSim; EnvSim; EnvListed; EnvNeeds; EnvJoins; Joins; Apart; SimIH; sih; foot; outerAt;
  Live; env-live; outer-⊑)
open import simultaneous.ReadMap using (upto-dn; under-down; listed-up)
open import simultaneous.SimReader using (hots-at)
open import simultaneous.Listing using (Listed)
open import simultaneous.AnnRun using (under-⊑; Upto?)
open import simultaneous.ToldRows using (sib-≺)
open import simultaneous.ExMove using (run←)
open import simultaneous.FlatFwd using (trig-fwd; vals-fwd; proper-out; sib-⊑; ⊑³)
open import simultaneous.FlatOrder using (emb-≺; row-apart; row-kid; apart-⊑; upto-or; upto-≼; ≼-elim; module Outs; module Earliest)
open import simultaneous.SimConnect using (Pair; hot-up; img-upto; env-row)

open import simultaneous.FlatRows using (Jn; merge∞; sw; ex; RunsOf; CutOf; inst; laneAt; frameAt; framed; module Rows)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; E; elab; trackers)

-- One value shown is shown, and is that value.
shown-one : ∀ {X} {x : IE X} {a} → valuesOf x ≡ a ∷ [] → Shown x
shown-one e e′ with trans (sym e) e′
... | ()

one-eq : ∀ {X : Set} {a b : X} → a ∷ [] ≡ b ∷ [] → a ≡ b
one-eq refl = refl

-- The rows a simulation lists under a bound's image, before a position
-- under it: listed.
under-listed : ∀ {B} {U : EmissionSet B} {A′ : PMap} c {l₀}
             → (Σ (List Pos) λ ls → (∀ {l e′} → U l e′ → Under A′ c l → l ∈ ls) × (∀ {l} → l ∈ ls → Σ (Ev B) (U l)))
             → Under A′ c l₀ → Listed U l₀
under-listed c {l₀} (ls , cov , back) un =
  L.filter (λ l → T? (l <ᵖ l₀)) ls
  , (λ {l} x lt → ∈-filter⁺ (λ l′ → T? (l′ <ᵖ l₀)) (cov x (under-down c {l₀} {l} lt un)) lt)
  , λ {l} m → let (m′ , lt) = ∈-filter⁻ (λ l′ → T? (l′ <ᵖ l₀)) {xs = ls} m in lt , back m′

-- A value's match is a value.
mt-out : ∀ {A B : Set} {V : A → B → Set} {a} {e′ : Ev B} {X : Ev B → Set} → X e′ → Mt V (out a) e′ → Σ B λ b → X (out b) × V a b
mt-out x (m-out v) = _ , x , v

-- The elaborated rows are given with their equation, so the consumer,
-- whose operator is concrete, compares them by name.
module Flat (n : ℕ) {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) {op : FlatOp} (j : Jn op)
            (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
            (ihs : ∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → SimIH n ρ′ s)
            (ihf : ∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → SimIH n ρ′ (f a))
            (env : DenEnv Γ) (env′ : DenEnv Δ) (Amb : PMap) (ge : GoodEnv env) (ge′ : GoodEnv env′) (ap : Apart env)
            (es : EnvSim ρ Amb env env′) (en : EnvNeeds ρ env env′ es) (em : Emb Amb)
            (p p′ : Pos) (pp : Amb p (foot s (outerAt p′))) (fr : Fresh (Hots env) (Hots env′) Amb p (foot s (outerAt p′)))
            (ok : Ok (Hots env) p) (ok′ : Ok (Hots env′) p′) (nh : ¬ Hots env p)
            (U : EmissionSet (IE B)) (U≡ : enter (approx n (elab ρ (flatMap op f s)) env′) p′ ≡ U) where

  ----------------------------------------------------------------------
  -- The plain flatMap

  ds : Den A
  ds = approx n s env

  g : A → Den B
  g a = approx n (f a) env

  o : EmissionSet A
  o = enter ds p

  module J = Joiner g o (RunsOf j g o) (CutOf j g o)

  T : EmissionSet B
  T = Truncate J.JoinT

  ----------------------------------------------------------------------
  -- The elaborated flatMap

  ρ₀ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ (⊤ ∷ Δ)
  ρ₀ i = there (ρ i)

  ρₗ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ (⊤ ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ)
  ρₗ i = there (there (there (there (ρ i))))

  ρₜ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ (IE B ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ)
  ρₜ i = there (there (there (there (ρ i))))

  s′ : E (⊤ ∷ Δ) (IE A)
  s′ = elab ρ₀ s

  g′ : A → E (⊤ ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ) (IE B)
  g′ a = elab ρₗ (f a)

  module RW = Rows n env′ j s′ g′ (trackers Γ 0 ρₜ) p′ (elab ρ (flatMap op f s)) refl U U≡
  open RW using (σtt; env₀′; o₂; g₂; rd; relay; q₀′; body; U₀)

  -- The real flatMap.
  module J₂ = Joiner g₂ o₂ (RunsOf j g₂ o₂) (CutOf j g₂ o₂)

  lawtt : Lawful (Proper σtt)
  lawtt = LC.lawful {s = Op.of (tt ∷ [])} {F = λ h → approx n body (h ∷ᴬ env′)}
            (inv-approx n (of (tt ∷ [])) env′ ge′) (λ {t} law → inv-approx n body (hot t ∷ᴬ env′) (good-cons law ge′)) p′ ok′

  postulate
    -- The shared outer is subscribed admissibly, its pair alone in its
    -- worlds with the trigger hot.
    ok-o    : Ok (Hots env₀′) q₀′
    fresh-o : Fresh (Hots env) (Hots env₀′) Amb p (foot s q₀′)

  srcIH = SimIH.sims (ihs ρ₀) env env₀′ Amb ge (good-cons lawtt ge′) ap (λ i → es i) (λ i → en i) em p q₀′ pp (fresh-o) ok ok-o nh

  M₀ : PMap
  M₀ = proj₁ srcIH

  R₀ : Run Shows Shown (Amb ∪ᴹ M₀) (EnvListed ρ₀ env env₀′ (λ i → es i) o) o (enter (approx n s′ env₀′) q₀′)
  R₀ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ srcIH))))

  ----------------------------------------------------------------------
  -- The shared outer, forward

  pσ : Pos
  pσ = (p′ ⊕ [ ix 0 ]) ⊕ [ ix 1 ]

  D₁ : Den (IE A)
  D₁ = approx n (flatMap (mergeᶠ nothing) (λ _ → s′) (connected (here refl))) env₀′

  ok₀₀ : Ok (Hots env₀′) (p′ ⊕ [ ix 0 ])
  ok₀₀ = LC.ok₀ {s = Op.of (tt ∷ [])} {F = λ h → approx n body (h ∷ᴬ env′)}
           (inv-approx n (of (tt ∷ [])) env′ ge′) (λ {t} law → inv-approx n body (hot t ∷ᴬ env′) (good-cons law ge′)) p′ ok′

  Iσ₁ : InvAt (Hots env₀′) pσ (enter D₁ pσ)
  Iσ₁ = inv-approx n (flatMap (mergeᶠ nothing) (λ _ → s′) (connected (here refl))) env₀′ (good-cons lawtt ge′) pσ
          (ok-step (p′ ⊕ [ ix 0 ]) ok₀₀)

  -- The real flatMap is lawful where it is subscribed.
  ge₀′ : GoodEnv env₀′
  ge₀′ = good-cons lawtt ge′

  law₁ : Lawful (Proper RW.σ₁)
  law₁ = LC.lawful {s = D₁} {F = λ h → approx n (connect RW.CL (connect RW.RF RW.CB)) (h ∷ᴬ env₀′)}
           (inv-approx n (flatMap (mergeᶠ nothing) (λ _ → s′) (connected (here refl))) env₀′ ge₀′)
           (λ {t} law → inv-approx n (connect RW.CL (connect RW.RF RW.CB)) (hot t ∷ᴬ env₀′) (good-cons law ge₀′)) (p′ ⊕ [ ix 0 ]) ok₀₀

  ok₀₀₀ : Ok (Hots RW.env₁′) ((p′ ⊕ [ ix 0 ]) ⊕ [ ix 0 ])
  ok₀₀₀ = LC.ok₀ {s = D₁} {F = λ h → approx n (connect RW.CL (connect RW.RF RW.CB)) (h ∷ᴬ env₀′)}
            (inv-approx n (flatMap (mergeᶠ nothing) (λ _ → s′) (connected (here refl))) env₀′ ge₀′)
            (λ {t} law → inv-approx n (connect RW.CL (connect RW.RF RW.CB)) (hot t ∷ᴬ env₀′) (good-cons law ge₀′)) (p′ ⊕ [ ix 0 ]) ok₀₀

  ge₁′ : GoodEnv RW.env₁′
  ge₁′ = good-cons law₁ ge₀′

  lawcl : Lawful (Proper RW.σcl)
  lawcl = LC.lawful {s = approx n RW.CL RW.env₁′} {F = λ h → approx n (connect RW.RF RW.CB) (h ∷ᴬ RW.env₁′)}
            (inv-approx n RW.CL RW.env₁′ ge₁′) (λ {t} law → inv-approx n (connect RW.RF RW.CB) (hot t ∷ᴬ RW.env₁′) (good-cons law ge₁′))
            ((p′ ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ok₀₀₀

  okY : Ok (Hots RW.envY) (((p′ ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ⊕ [ ix 0 ])
  okY = LC.ok₀ {s = approx n RW.CL RW.env₁′} {F = λ h → approx n (connect RW.RF RW.CB) (h ∷ᴬ RW.env₁′)}
          (inv-approx n RW.CL RW.env₁′ ge₁′) (λ {t} law → inv-approx n (connect RW.RF RW.CB) (hot t ∷ᴬ RW.env₁′) (good-cons law ge₁′))
          ((p′ ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ok₀₀₀

  Irf : InvAt (Hots RW.envY) RW.z₂ RW.σRF
  Irf = inv-approx n RW.RF RW.envY (good-cons lawcl ge₁′) RW.z₂ (ok-step (((p′ ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) okY)


  -- A row of the real flatMap's joiner, truncated: the real flatMap's.
  rf-in : ∀ {K b} → Truncate J₂.JoinT K (out b) → RW.σRF K (out b)
  rf-in {K} {b} x = subst (λ t → t K (out b)) (sym (inst j g₂ RW.D₂ RW.z₂)) x

  I₀ : InvAt (Hots env₀′) q₀′ U₀
  I₀ = inv-approx n s′ env₀′ (good-cons lawtt ge′) q₀′ ok-o

  q₀′≺ : ∀ {k′ x} → U₀ k′ (out x) → q₀′ ≺ k′
  q₀′≺ u = world-after (InvAt.world I₀ u) (InvAt.real I₀ u)

  -- A value of the shared outer: the trigger's lane's, read.
  σ₁-fwd : ∀ {k′ x} → U₀ k′ (out x) → enter D₁ pσ k′ (out x)
  σ₁-fwd u = trig-fwd (approx n s′ env₀′) (p′ ⊕ [ ix 1 ]) pσ (sib-≺ p′ (ticks p′ 0) [ ix 1 ] [ ix 0 ]) u (q₀′≺ u)

  -- One value of the shared outer: the real flatMap's outer value, read.
  o₂-fwd : ∀ {k′ x a} → U₀ k′ (out x) → valuesOf x ≡ a ∷ [] → o₂ (rd k′) (out a)
  o₂-fwd {k′} u vs =
    vals-fwd (enter D₁ pσ) RW.z₂ (InvAt.flat Iσ₁) s₁ (proper-out Iσ₁ s₁) (entered-few D₁ pσ (λ {k} {e′} → tt) s₁)
             (≺-trans {RW.z₂} {q₀′} {k′} (sib-⊑ p′ (ticks p′ 0) (⊑³ (p′ ⊕ [ ix 0 ])) (⊑³ (p′ ⊕ [ ix 1 ]))) (q₀′≺ u)) vs
    where s₁ = σ₁-fwd u

  ----------------------------------------------------------------------
  -- The lanes at their pairs

  -- A lane: its value's row, and that row's carrier.
  LaneIx : Set
  LaneIx = Σ Pos λ q → Σ Pos λ k′ → Σ A λ a → o q (out a) × Run.Img R₀ q k′

  lq : LaneIx → Pos
  lq L = proj₁ L

  lk′ : LaneIx → Pos
  lk′ L = proj₁ (proj₂ L)

  la : LaneIx → A
  la L = proj₁ (proj₂ (proj₂ L))

  lo : ∀ L → o (lq L) (out (la L))
  lo L = proj₁ (proj₂ (proj₂ (proj₂ L)))

  li : ∀ L → Run.Img R₀ (lq L) (lk′ L)
  li L = proj₂ (proj₂ (proj₂ (proj₂ L)))

  -- The real flatMap's lane, and where its frame subscribes the lane.
  lw : LaneIx → Pos
  lw L = rd (lk′ L) ⊕ [ ix 1 ]

  lsub′ : LaneIx → Pos
  lsub′ L = laneAt (lw L)

  lfoot : LaneIx → Pos
  lfoot L = foot (f (la L)) (lsub′ L)

  -- The lane's share's env.
  envₗ′ : LaneIx → DenEnv (⊤ ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ)
  envₗ′ L = RW.envW ((lw L ⊕ [ ix 0 ]) ⊕ [ ix 1 ])

  Ambₗ : LaneIx → PMap
  Ambₗ L = (Amb ∪ᴹ M₀) ∪ᴹ Pair (lq L ⊕ [ ix 1 ]) (lfoot L)

  TL : LaneIx → EmissionSet B
  TL L = enter (g (la L)) (lq L ⊕ [ ix 1 ])

  Io : InvAt (Hots env) p o
  Io = inv-approx n s env ge p ok

  UL : LaneIx → EmissionSet (IE B)
  UL L = enter (approx n (g′ (la L)) (envₗ′ L)) (lsub′ L)

  postulate
    -- A lane pair holds the lane's worlds alone, keeping the order, and
    -- puts no point under a hot row but a join.
    emb-l   : ∀ L → Emb (Ambₗ L)
    fresh-l : ∀ L → Fresh (Hots env) (Hots (envₗ′ L)) (Ambₗ L) (lq L ⊕ [ ix 1 ]) (lfoot L)
    joins-l : ∀ L {X} (i : X ∈ Γ) → Joins (Ambₗ L) (Ambₗ L) (HotSim.rows (es i)) (HotSim.car (es i))
    -- The lane's hots are lawful; both lanes are subscribed admissibly.
    good-l  : ∀ L → GoodEnv (envₗ′ L)
    ok-l    : ∀ L → Ok (Hots env) (lq L ⊕ [ ix 1 ])
    ok-l′   : ∀ L → Ok (Hots (envₗ′ L)) (lsub′ L)
    nh-l    : ∀ L → ¬ Hots env (lq L ⊕ [ ix 1 ])

  IL : ∀ L → InvAt (Hots env) (lq L ⊕ [ ix 1 ]) (TL L)
  IL L = inv-approx n (f (la L)) env ge (lq L ⊕ [ ix 1 ]) (ok-l L)

  -- A lane's rows lie past its subscription.
  lane-after : ∀ L {k e} → TL L k e → (lq L ⊕ [ ix 1 ]) ≺ k
  lane-after L x = world-after (InvAt.world (IL L) x) (InvAt.real (IL L) x)

  -- No later outer value lies over a lane's row.
  out-lane : ∀ L {q′ a′ k e} → o q′ (out a′) → lq L ≺ q′ → TL L k e → ¬ q′ ⊑ k
  out-lane L oq′ lt tl = row-kid ok Io (lo L) oq′ plain-ix lt (inW (InvAt.world (IL L) tl))

  esₗ : ∀ L → EnvSim ρₗ (Ambₗ L) env (envₗ′ L)
  esₗ L i = hot-up (λ a → inj₁ (inj₁ a)) (es i) (joins-l L i)

  -- No row of a lane's share ends a lane.
  undone-l : ∀ L → Undone (approx n (g′ (la L)) (envₗ′ L))
  undone-l L = elab-undone n ρₗ (f (la L)) (envₗ′ L) (env-u {Γ} {_} {Ambₗ L} {λ {X} → ρₗ {X}} {env} {envₗ′ L} (esₗ L))

  laneIH : ∀ L → _
  laneIH L = SimIH.sims (ihf (la L) ρₗ) env (envₗ′ L) (Ambₗ L) ge (good-l L) ap (esₗ L) (λ i → en i) (emb-l L)
               (lq L ⊕ [ ix 1 ]) (lsub′ L) (inj₂ (refl , refl)) (fresh-l L) (ok-l L) (ok-l′ L) (nh-l L)

  Mₗ : LaneIx → PMap
  Mₗ L = proj₁ (laneIH L)

  Rₗ : ∀ L → Run Shows Shown (Ambₗ L ∪ᴹ Mₗ L) (EnvListed ρₗ env (envₗ′ L) (esₗ L) (TL L)) (TL L) (UL L)
  Rₗ L = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (laneIH L)))))

  ----------------------------------------------------------------------
  -- The map and the carriers

  -- Each running lane's pair and map.
  Lanes : PMap
  Lanes x y = Σ LaneIx λ L → (Pair (lq L ⊕ [ ix 1 ]) (lfoot L) ∪ᴹ Mₗ L) x y

  -- The ends, paired.
  Ends : PMap
  Ends x y = T x end × U y end

  M : PMap
  M = M₀ ∪ᴹ (Lanes ∪ᴹ Ends)

  -- A lane value's carrier: its lane's, framed and relayed.
  ImgL : Pos → Pos → Set
  ImgL k l = Σ LaneIx λ L → Σ Pos λ l₀ → Run.Img (Rₗ L) k l₀ × Σ B (λ b → TL L k (out b)) × l ≡ relay (framed (lw L) l₀)

  Img : Pos → Pos → Set
  Img k l = ImgL k l ⊎ Ends k l

  lane-⊆ : ∀ L → (Ambₗ L ∪ᴹ Mₗ L) ⊆ᴹ (Amb ∪ᴹ M)
  lane-⊆ L (inj₁ (inj₁ (inj₁ a))) = inj₁ a
  lane-⊆ L (inj₁ (inj₁ (inj₂ m))) = inj₂ (inj₁ m)
  lane-⊆ L (inj₁ (inj₂ pr))       = inj₂ (inj₂ (inj₁ (L , inj₁ pr)))
  lane-⊆ L (inj₂ m)               = inj₂ (inj₂ (inj₁ (L , inj₂ m)))

  src-⊆ : (Amb ∪ᴹ M₀) ⊆ᴹ (Amb ∪ᴹ M)
  src-⊆ (inj₁ a) = inj₁ a
  src-⊆ (inj₂ m) = inj₂ (inj₁ m)

  -- Under a lane row, under its framed relay.
  relay-⊑ : ∀ w l → l ⊑ relay (framed w l)
  relay-⊑ w l = ⊑-trans (⊑-trans (⊑-trans (⊑-snoc⁺ l) (⊑-snoc⁺ (l ⊕ [ sub (frameAt w) ]))) (⊑-snoc⁺ _))
                        (⊑-trans (⊑-trans (⊑-snoc⁺ _) (⊑-snoc⁺ _)) (⊑-snoc⁺ _))

  -- Under a lane row, under its frame; under an outer row, under its
  -- read; and under the lane the real flatMap subscribes.
  framed-⊑ : ∀ w l → l ⊑ framed w l
  framed-⊑ w l = ⊑-trans (⊑-snoc⁺ l {sub (frameAt w)}) (⊑-trans (⊑-snoc⁺ (l ⊕ [ sub (frameAt w) ]) {ix 1})
                   (⊑-snoc⁺ ((l ⊕ [ sub (frameAt w) ]) ⊕ [ ix 1 ]) {ix 0}))

  rd-⊑ : ∀ k → k ⊑ rd k
  rd-⊑ k = ⊑-trans (⊑-snoc⁺ k {sub RW.z₂}) (⊑-trans (⊑-snoc⁺ (k ⊕ [ sub RW.z₂ ]) {ix 1}) (⊑-snoc⁺ ((k ⊕ [ sub RW.z₂ ]) ⊕ [ ix 1 ]) {ix 0}))

  at-⊑ : ∀ w → w ⊑ laneAt w
  at-⊑ w = ⊑-trans (⊑-snoc⁺ w {ix 0}) (⊑-trans (⊑-snoc⁺ (w ⊕ [ ix 0 ]) {ix 1})
             (⊑-trans (outer-⊑ ((w ⊕ [ ix 0 ]) ⊕ [ ix 1 ])) (⊑-trans (⊑-snoc⁺ (outerAt ((w ⊕ [ ix 0 ]) ⊕ [ ix 1 ])) {ix 0})
               (⊑-snoc⁺ (outerAt ((w ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) {ix 1}))))

  lane-⊑ : ∀ k → k ⊑ laneAt (rd k ⊕ [ ix 1 ])
  lane-⊑ k = ⊑-trans (rd-⊑ k) (⊑-trans (⊑-snoc⁺ (rd k) {ix 1}) (at-⊑ (rd k ⊕ [ ix 1 ])))

  -- An outer row lies before its lane's rows, relayed.
  k′≺ : ∀ k′ K₀ → laneAt (rd k′ ⊕ [ ix 1 ]) ≺ K₀ → k′ ≺ relay (framed (rd k′ ⊕ [ ix 1 ]) K₀)
  k′≺ k′ K₀ aft = ≺-≼-≺ {k′} {K₀} {relay (framed (rd k′ ⊕ [ ix 1 ]) K₀)}
                    (≼-≺-≺ {k′} {laneAt (rd k′ ⊕ [ ix 1 ])} {K₀} (⊑-≼ (lane-⊑ k′)) aft) (⊑-≼ (relay-⊑ (rd k′ ⊕ [ ix 1 ]) K₀))

  ext : ∀ {k l} → Img k l → Σ Pos λ y → (Amb ∪ᴹ M) k y × y ⊑ l
  ext (inj₁ (L , l₀ , i , _ , refl)) =
    let (y , a , yl) = Run.ext (Rₗ L) i in y , lane-⊆ L a , ⊑-trans yl (relay-⊑ (lw L) l₀)
  ext {k} {l} (inj₂ e) = l , inj₂ (inj₂ (inj₂ e)) , ⊑-refl l

  postulate
    -- One carrier each: a lane row is one lane's, and a value no end.
    flat-img : ∀ {k l l′} → Img k l → Img k l′ → l ≡ l′

  ----------------------------------------------------------------------
  -- The outer, wherever the flatMap is

  -- The flatMap ends only past its outer's end.
  live-o : ∀ {j} → Live o j → Live T j
  live-o {j} l {c} (J.oend _ ((c₀ , y , le) , _) , _)          = ≺-≼-≺ {j} {c₀} {c} (l y) le
  live-o {j} l {c} (J.lend _ _ _ _ _ ((c₀ , y , le) , _) , _)  = ≺-≼-≺ {j} {c₀} {c} (l y) le
  live-o l (J.lane _ _ _ _ () , _)
  live-o l (J.run () _ , _)
  live-o l (J.rend () _ _ , _)

  outer-L : ∀ {A′ c} → EnvListed ρ env env′ es T A′ c → EnvListed ρ₀ env env₀′ (λ i → es i) o A′ c
  outer-L {A′} {c} = env-live {ρ = ρ} {Amb = Amb} {env = env} {env′ = env′} es {T = T} {T′ = o} (λ {j} → live-o {j}) {A′} {c}

  postulate
    -- The outer's rows up to a bound, listed wherever the flatMap's are.
    outer-listed : ∀ {c} → ListedB T c → ListedB o c
    -- An end of the flatMap has an elaborated end.
    flat-end→ : ∀ {k} → T k end → Σ Pos λ l → U l end

  ----------------------------------------------------------------------
  -- The simulation up to a bound

  module FSim (A′ : PMap) (inc : (Amb ∪ᴹ M) ⊆ᴹ A′) (emA : Emb A′) (c : Maybe Pos) (mp : Mapped A′ c)
              (Lr : EnvListed ρ env env′ es T A′ c) (lst : ListedB T c) where

    S₀ : Sim Shows Shown A′ (Run.Img R₀) c o U₀
    S₀ = Run.sim R₀ A′ (λ m → inc (src-⊆ m)) emA c mp (outer-L {A′} {c} Lr) (outer-listed lst)

    --------------------------------------------------------------------
    -- Carriers in order

    img₀ : ∀ {q k′} → Run.Img R₀ q k′ → Σ Pos λ y → A′ q y × y ⊑ k′
    img₀ i = proj₁ (Run.ext R₀ i) , inc (src-⊆ (proj₁ (proj₂ (Run.ext R₀ i)))) , proj₂ (proj₂ (Run.ext R₀ i))

    imgₗ : ∀ L {k l₀} → Run.Img (Rₗ L) k l₀ → Σ Pos λ y → A′ k y × y ⊑ l₀
    imgₗ L i = proj₁ (Run.ext (Rₗ L) i) , inc (lane-⊆ L (proj₁ (proj₂ (Run.ext (Rₗ L) i)))) , proj₂ (proj₂ (Run.ext (Rₗ L) i))

    -- An outer value up to the bound: its carrier.
    fwd₀ : ∀ {q a} → o q (out a) → Upto c q → Σ Pos λ k′ → Run.Img R₀ q k′ × Σ (IE A) λ x → U₀ k′ (out x) × Shows a x
    fwd₀ oq uq =
      let (k′ , i , _ , ux , m) = Sim.fwd S₀ oq c-out uq
          (x , u , sh) = mt-out {X = U₀ k′} ux m
      in k′ , i , x , u , sh

    -- Two outer values' carriers keep their order, read.
    rd-≺ : ∀ {q q′ a a′ k k′} → o q (out a) → o q′ (out a′) → Run.Img R₀ q k → Run.Img R₀ q′ k′ → q ≺ q′ → rd k ≺ rd k′
    rd-≺ {k = k} {k′} oq oq′ i i′ lt =
      emb-≺ emA (proj₁ (proj₂ (img₀ i))) (proj₁ (proj₂ (img₀ i′))) (⊑-trans (proj₂ (proj₂ (img₀ i))) (rd-⊑ k))
            (⊑-trans (proj₂ (proj₂ (img₀ i′))) (rd-⊑ k′)) lt (row-apart Io oq oq′ lt)

    -- An outer value before a lane row: its carrier, read, before the
    -- lane row's, framed.
    lane-≺ : ∀ L {q′ a′ k″ k e l₀} → o q′ (out a′) → lq L ≺ q′ → Run.Img R₀ q′ k″ → TL L k e → Run.Img (Rₗ L) k l₀ → q′ ≺ k
           → rd k″ ≺ framed (lw L) l₀
    lane-≺ L {k″ = k″} {l₀ = l₀} oq′ lt i″ tl iₗ qk =
      emb-≺ emA (proj₁ (proj₂ (img₀ i″))) (proj₁ (proj₂ (imgₗ L iₗ))) (⊑-trans (proj₂ (proj₂ (img₀ i″))) (rd-⊑ k″))
            (⊑-trans (proj₂ (proj₂ (imgₗ L iₗ))) (framed-⊑ (lw L) l₀)) qk (out-lane L oq′ lt tl)

    -- A carrier under the bound's image is up to the bound.
    under-img : ∀ c′ → Mapped A′ c′ → ∀ {k l} → Img k l → Under A′ c′ l → Upto c′ k
    under-img nothing   _ _ _            = tt
    under-img (just c′) _ i (_ , ac , u) = img-upto emA ac (inc (proj₁ (proj₂ (ext i)))) (proj₂ (proj₂ (ext i))) u

    --------------------------------------------------------------------
    -- Each running lane's bound: the flatMap's, or a switch's first
    -- outer value past the lane's, up to it

    OL : ListedB o c
    OL = outer-listed lst

    module O = Outs o

    O₀ : List O.Row
    O₀ = O.outs (proj₁ OL) (proj₂ (proj₂ OL))

    Past : Pos → O.Row → Set
    Past q r = q ≺ proj₁ r × Upto c (proj₁ r)

    past? : ∀ q r → Dec (Past q r)
    past? q r = T? (q <ᵖ proj₁ r) ×-dec Upto? c (proj₁ r)

    module Ea (q : Pos) = Earliest {X = O.Row} proj₁ {P = Past q} (past? q)

    cutAt : ∀ {q} → Maybe (Σ O.Row (Past q)) → Maybe Pos
    cutAt nothing              = c
    cutAt (just ((m , _) , _)) = just m

    nextB : ∀ {op′} → Jn op′ → Pos → Maybe Pos
    nextB merge∞ q = c
    nextB sw     q = cutAt {q} (Ea.first q O₀)
    nextB ex     q = c

    laneB : LaneIx → Maybe Pos
    laneB L = nextB j (lq L)

    postulate
      -- EACH RUNNING LANE'S BOUND: its rows and hots listed up to it.
      --
      -- RECOVERY: git show e8138387:agda-impl/simultaneous/FlatOrder.agda
      --   restores `outs-∈`, every listed value kept by `Outs.outs`.
      lane-env    : ∀ L → EnvListed ρₗ env (envₗ′ L) (esₗ L) (TL L) A′ (laneB L)
      lane-listed : ∀ L → ListedB (TL L) (laneB L)
      -- A RUNNING LANE'S END, READ: the real flatMap's lane at a value's
      -- carrier ends before a later value's carrier, read, exactly when
      -- the plain lane ends before the plain value.
      lane-end← : ∀ L {q′ a′ k″ ce a₂} → o q′ (out a′) → Run.Img R₀ q′ k″ → Under A′ c k″ → o₂ (rd (lk′ L)) (out a₂)
                → LaneOf g₂ (rd (lk′ L)) a₂ ce end → ce ≺ rd k″ → Σ Pos λ c′ → LaneOf g (lq L) (la L) c′ end × c′ ≺ q′
      lane-end→ : ∀ L {q′ a′ k″ c′ a₂} → o q′ (out a′) → Run.Img R₀ q′ k″ → Under A′ c k″ → o₂ (rd (lk′ L)) (out a₂)
                → LaneOf g (lq L) (la L) c′ end → c′ ≺ q′ → Σ Pos λ ce → LaneOf g₂ (rd (lk′ L)) a₂ ce end × ce ≺ rd k″

    -- An outer value up to the bound: its carrier, read by the real
    -- flatMap.
    o₂-row : ∀ {q k′ a} → o q (out a) → Upto c q → Run.Img R₀ q k′ → o₂ (rd k′) (out a)
    o₂-row {a = a} oq uq i =
      let (k″ , i″ , x , u , sh) = fwd₀ oq uq in subst (λ k → o₂ (rd k) (out a)) (Run.img-fun R₀ i″ i) (o₂-fwd u sh)

    --------------------------------------------------------------------
    -- An exhaust's decisions, read back

    -- The outer's carrier under the bound's image: up to the bound.
    under-img₀ : ∀ c′ {q k′} → Run.Img R₀ q k′ → Under A′ c′ k′ → Upto c′ q
    under-img₀ nothing   _ _            = tt
    under-img₀ (just c′) i (_ , ac , u) = img-upto emA ac (proj₁ (proj₂ (img₀ i))) (proj₂ (proj₂ (img₀ i))) u

    -- A plain value up to the bound, read by the real flatMap.
    Rd : Pos → Pos → Set
    Rd q y = (Σ A λ a → o q (out a)) × Upto c q × Σ Pos λ k′ → Run.Img R₀ q k′ × y ≡ rd k′

    rd-mono : ∀ {q q′ y y′} → Rd q y → Rd q′ y′ → q ≺ q′ → y ≺ y′
    rd-mono ((_ , oq) , _ , _ , i , refl) ((_ , oq′) , _ , _ , i′ , refl) lt = rd-≺ oq oq′ i i′ lt

    rd-fun : ∀ {q y y′} → Rd q y → Rd q y′ → y ≡ y′
    rd-fun (_ , _ , _ , i , refl) (_ , _ , _ , i′ , refl) = cong rd (Run.img-fun R₀ i i′)

    rd-o₂ : ∀ {q y} → Rd q y → Σ A λ a → o₂ y (out a)
    rd-o₂ ((a , oq) , uq , _ , i , refl) = a , o₂-row oq uq i

    -- A value's carrier, shown.
    car-u : ∀ {q k a} → o q (out a) → Upto c q → Run.Img R₀ q k → Σ (IE A) λ x → U₀ k (out x)
    car-u oq uq i =
      let (k″ , i″ , x , u , _) = fwd₀ oq uq in x , subst (λ k → U₀ k (out x)) (Run.img-fun R₀ i″ i) u

    -- Below a value's carrier up to the bound's image, read.
    module ExR {q₀ k₀ a₀ x₀} (oq₀ : o q₀ (out a₀)) (i₀ : Run.Img R₀ q₀ k₀) (un₀ : Under A′ c k₀) (u₀ : U₀ k₀ (out x₀)) where

      uq₀ : Upto c q₀
      uq₀ = under-img₀ c i₀ un₀

      -- A carrier read at or before the given one's: under the image.
      un-rd : ∀ {k x} → U₀ k (out x) → rd k ≼ rd k₀ → Under A′ c k
      un-rd {k} u le = ≼-elim {k} {k₀} (Under A′ c) (λ k₀k → le (apart-⊑ (rd-⊑ k₀) (rd-⊑ k) k₀k (row-apart I₀ u₀ u k₀k)))
                         (λ lt → under-down c lt un₀) un₀

      In : Pos → Set
      In y = y ≼ rd k₀

      InP : Pos → Set
      InP q = q ≼ q₀

      in↓ : ∀ {y y′} → In y → y′ ≺ y → In y′
      in↓ {y} {y′} le lt = ≼-trans {y′} {y} {rd k₀} (≺→≼ {y′} {y} lt) le

      inP↓ : ∀ {q q′} → InP q → q′ ≺ q → InP q′
      inP↓ {q} {q′} le lt = ≼-trans {q′} {q} {q₀} (≺→≼ {q′} {q} lt) le

      in-p : ∀ {q y} → Rd q y → In y → InP q
      in-p r le q₀q = le (rd-mono ((_ , oq₀) , uq₀ , _ , i₀ , refl) r q₀q)

      up-p : ∀ {q} → InP q → Upto c q
      up-p {q} le = ≼-elim {q} {q₀} (Upto c) le (λ lt → upto-dn c lt uq₀) uq₀

      back : ∀ {y a₂} → o₂ y (out a₂) → In y → Σ Pos λ q → Rd q y
      back oy le =
        let (k , x , u , vx , eq) = RW.outer-back oy
            unk = un-rd u (subst (_≼ rd k₀) eq le)
            (q , i , a , oq , _) = Sim.val← S₀ u (shown-one vx) unk
        in q , (a , oq) , under-img₀ c i unk , k , i , eq

      fwd : ∀ {q a} → o q (out a) → InP q → Σ Pos λ y → Rd q y
      fwd oq le = let (k , i , _) = fwd₀ oq (up-p le) in rd k , (_ , oq) , up-p le , k , i , refl

      un-of : ∀ {q y} → Rd q y → In y → Σ Pos λ k → y ≡ rd k × Run.Img R₀ q k × Under A′ c k
      un-of ((_ , oq) , uq , k , i , refl) le = k , refl , i , un-rd (proj₂ (car-u oq uq i)) le

      end← : ∀ {q y a a₂ q′ y′ ce} → Exhaust.Run g o q → o q (out a) → o₂ y (out a₂) → Rd q y → Rd q′ y′ → In y′
           → LaneOf g₂ y a₂ ce end → ce ≺ y′ → Σ Pos λ c′ → LaneOf g q a c′ end × c′ ≺ q′
      end← {q} {a = a} {ce = ce} _ oq oy (_ , _ , k , i , refl) r′@((_ , oq′) , _) le l lt =
        let (k′ , e , i′ , un′) = un-of r′ le in lane-end← (q , k , a , oq , i) oq′ i′ un′ oy l (subst (λ z → ce ≺ z) e lt)

      end→ : ∀ {q y a a₂ q′ y′ c′} → Exhaust.Run g o q → o q (out a) → o₂ y (out a₂) → Rd q y → Rd q′ y′ → In y′
           → LaneOf g q a c′ end → c′ ≺ q′ → Σ Pos λ ce → LaneOf g₂ y a₂ ce end × ce ≺ y′
      end→ {q} {a = a} _ oq oy (_ , _ , k , i , refl) r′@((_ , oq′) , _) le l lt =
        let (k′ , e , i′ , un′) = un-of r′ le
            (ce , l₂ , lt₂) = lane-end→ (q , k , a , oq , i) oq′ i′ un′ oy l lt
        in ce , l₂ , subst (λ z → ce ≺ z) (sym e) lt₂

      go : Exhaust.Run g₂ o₂ (rd k₀) → Exhaust.Run g o q₀
      go r = run← g o g₂ o₂ Rd In InP (λ {y} {y′} → in↓ {y} {y′}) (λ {q} {q′} → inP↓ {q} {q′}) (λ {q} {y} → in-p {q} {y}) proj₁
                  (λ {q} {y} → rd-o₂ {q} {y}) back fwd rd-mono rd-fun end← end→ r (≼-refl {rd k₀}) ((a₀ , oq₀) , uq₀ , k₀ , i₀ , refl)

    -- An exhaust running the lane at an outer value's carrier, up to
    -- the bound's image, runs the value's.
    ex-run← : ∀ {q k′ a} → o q (out a) → Run.Img R₀ q k′ → Under A′ c k′ → Exhaust.Run g₂ o₂ (rd k′) → Exhaust.Run g o q
    ex-run← {q} {k′} {a} oq i un r =
      let uq = under-img₀ c i un
          (x , u) = car-u oq uq i
      in ExR.go oq i un u r

    cut-img : ∀ {q} (r : O.Row) → Past q r → Σ Pos λ k′ → Run.Img R₀ (proj₁ r) k′ × Σ Pos λ y → A′ (proj₁ r) y × y ⊑ k′
    cut-img (m , a , x) (_ , um) = let (k′ , i , _) = fwd₀ x um in k′ , i , img₀ i

    mapped-cut : ∀ {q} (r : Maybe (Σ O.Row (Past q))) → Mapped A′ (cutAt {q} r)
    mapped-cut nothing             = mp
    mapped-cut {q} (just (r , pr)) = let (_ , _ , y , ay , _) = cut-img {q} r pr in y , ay

    mapped-b : ∀ {op′} (j′ : Jn op′) q → Mapped A′ (nextB j′ q)
    mapped-b merge∞ q = mp
    mapped-b sw     q = mapped-cut {q} (Ea.first q O₀)
    mapped-b ex     q = mp

    -- A lane row the flatMap shows up to its bound: up to the lane's.
    upto-cut : ∀ {q k} (r : Maybe (Σ O.Row (Past q))) → ¬ Switch.Cut g o q k → Upto c k → Upto (cutAt {q} r) k
    upto-cut nothing                         _  u = u
    upto-cut (just ((m , a , x) , (qm , _))) nc _ = upto-≼ (λ mk → nc (m , a , x , qm , mk))

    upto-b : ∀ {op′} (j′ : Jn op′) {q k} → ¬ CutOf j′ g o q k → Upto c k → Upto (nextB j′ q) k
    upto-b merge∞ _  u = u
    upto-b sw {q} nc u = upto-cut {q} (Ea.first q O₀) nc u
    upto-b ex     _  u = u

    -- A lane row the elaborated flatMap shows uncut, under the bound's
    -- image: under the lane's.  Past a cut's image and outside it, its
    -- carrier, read, would cut it.
    under-cut : ∀ {q k′ a K₀ l} (r : Maybe (Σ O.Row (Past q))) → o q (out a) → Run.Img R₀ q k′ → K₀ ⊑ l → Under A′ c l
              → ¬ Switch.Cut g₂ o₂ (rd k′) (framed (rd k′ ⊕ [ ix 1 ]) K₀) → Under A′ (cutAt {q} r) K₀
    under-cut nothing _ _ kl un _ = under-⊑ c kl un
    under-cut {q} {k′ = k′} {K₀ = K₀} (just ((m , a′ , x) , (qm , um))) oq i kl un nc =
      let (kₘ , iₘ , y , ay , yk) = cut-img {q} (m , a′ , x) (qm , um) in
      y , ay , [ (λ u → u) , (λ yn → ⊥-elim (nc (rd kₘ , a′ , o₂-row x um iₘ , rd-≺ oq x i iₘ qm
                                                , apart-⊑ (⊑-trans yk (rd-⊑ kₘ)) (framed-⊑ (rd k′ ⊕ [ ix 1 ]) K₀) (proj₁ yn) (proj₂ yn)))) ]′ (upto-or y K₀)

    under-b : ∀ {op′} (j′ : Jn op′) {q k′ a K₀ l} → o q (out a) → Run.Img R₀ q k′ → K₀ ⊑ l → Under A′ c l
            → ¬ CutOf j′ g₂ o₂ (rd k′) (framed (rd k′ ⊕ [ ix 1 ]) K₀) → Under A′ (nextB j′ q) K₀
    under-b merge∞ _  _ kl un _  = under-⊑ c kl un
    under-b sw {q} oq i kl un nc = under-cut {q} (Ea.first q O₀) oq i kl un nc
    under-b ex     _  _ kl un _  = under-⊑ c kl un

    --------------------------------------------------------------------
    -- The decisions, read back

    runs← : ∀ {op′} (j′ : Jn op′) {q k′ a} → o q (out a) → Run.Img R₀ q k′ → Under A′ c k′ → RunsOf j′ g₂ o₂ (rd k′) → RunsOf j′ g o q
    runs← merge∞ _  _ _  _ = tt
    runs← sw     _  _ _  _ = tt
    runs← ex     oq i un r = ex-run← oq i un r

    -- A plain cut would be an elaborated cut: its value's carrier, read,
    -- lies between.
    uncut← : ∀ {op′} (j′ : Jn op′) L {k l₀ a} → TL L k (out a) → Run.Img (Rₗ L) k l₀ → Upto c k
           → ¬ CutOf j′ g₂ o₂ (rd (lk′ L)) (framed (lw L) l₀) → ¬ CutOf j′ g o (lq L) k
    uncut← merge∞ L _  _  _  _   ()
    uncut← sw     L tl iₗ uk nc₂ (q′ , a′ , oq′ , lt₁ , lt₂) =
      let uq′ = upto-dn c lt₂ uk
          (k″ , i″ , _) = fwd₀ oq′ uq′
      in nc₂ (rd k″ , a′ , o₂-row oq′ uq′ i″ , rd-≺ (lo L) oq′ (li L) i″ lt₁ , lane-≺ L oq′ lt₁ i″ tl iₗ lt₂)
    uncut← ex     L _  _  _  _   ()

    SL : ∀ L → Sim Shows Shown A′ (Run.Img (Rₗ L)) (laneB L) (TL L) (UL L)
    SL L = Run.sim (Rₗ L) A′ (λ m → inc (lane-⊆ L m)) emA (laneB L) (mapped-b j (lq L)) (lane-env L) (lane-listed L)

    -- A lane row up to its bound: the lane's rows before its carrier,
    -- listed, by the lane's simulation up to the row.
    lane-at : ∀ L {k l₀ b} → TL L k (out b) → Upto (laneB L) k → Run.Img (Rₗ L) k l₀ → Listed (UL L) l₀
    lane-at L {k} {l₀} tl uk iₗ =
      let (y , a) = Run.anchor (Rₗ L) A′ incₗ emA tl c-out envk lstk
          (y₀ , a₀ , yl) = Run.ext (Rₗ L) iₗ
      in under-listed (just k) (Sim.upto (Run.sim (Rₗ L) A′ incₗ emA (just k) (y , incₗ a) envk lstk)) (y₀ , incₗ a₀ , inj₂ yl)
      where
        incₗ : (Ambₗ L ∪ᴹ Mₗ L) ⊆ᴹ A′
        incₗ m = inc (lane-⊆ L m)

        envk : EnvListed ρₗ env (envₗ′ L) (esₗ L) (TL L) A′ (just k)
        envk = env-row {Γ} {_} {λ {X} → ρₗ {X}} {Ambₗ L} {env} {envₗ′ L} (esₗ L) {T = TL L} uk (λ i y kh → proj₂ (ok-l L) (hots-at env i (HotSim.isP (esₗ L i)) y) (InvAt.world (IL L) tl) (⊑-inside kh))
                 {A′} (lane-env L)

        lstk : ListedB (TL L) (just k)
        lstk = listed-up (λ {y} {e} {l} {ys} {e′} → InvAt.flat (IL L) {y} {e} {l} {ys} {e′}) (laneB L) tl uk (lane-listed L)

    -- UNRELAYED: a value the elaborated flatMap shows up to the bound's
    -- image is a running lane's value, framed and relayed, uncut, up to
    -- the lane's bound's image.
    unrelay : ∀ {l b} → U l (out b) → Shown b → Under A′ c l
            → Σ LaneIx λ L → RunsOf j g o (lq L) × Σ Pos λ l₀ → l ≡ relay (framed (lw L) l₀) × Σ (IE B) λ b₁ → UL L l₀ (out b₁)
              × valuesOf b ≡ valuesOf b₁ × Under A′ (laneB L) l₀ × ¬ CutOf j g₂ o₂ (rd (lk′ L)) (framed (lw L) l₀)
    unrelay {l} {b} u sh un =
      L , runs← j oq′ i₀ un₀ Bk.runs , Bk.K₀ , Bk.at , b , Bk.ul , refl
        , under-b j oq′ i₀ (subst (Bk.K₀ ⊑_) (sym Bk.at) (relay-⊑ (rd Bk.k′ ⊕ [ ix 1 ]) Bk.K₀)) un Bk.uncut , Bk.uncut
      where
        bk = RW.back u sh
        module Bk = RW.Back bk
        un₀ : Under A′ c Bk.k′
        un₀ = under-down c (subst (Bk.k′ ≺_) (sym Bk.at) (k′≺ Bk.k′ Bk.K₀ Bk.aft)) un
        v = Sim.val← S₀ Bk.u₀ (shown-one Bk.vx) un₀
        q = proj₁ v
        i₀ = proj₁ (proj₂ v)
        oq′ : o q (out Bk.a)
        oq′ = subst (λ a → o q (out a)) (one-eq (trans (sym (proj₂ (proj₂ (proj₂ (proj₂ v))))) Bk.vx)) (proj₁ (proj₂ (proj₂ (proj₂ v))))
        L : LaneIx
        L = q , Bk.k′ , Bk.a , oq′ , i₀

    -- Each decision forward is taken up to the bound, an implementation
    -- detail that leaves the spec unaffected (Anthony): below it the outer
    -- and each lane are simulated, so a value read back is a plain value.
    postulate
      -- AN EXHAUST'S RUN, READ: a value whose lane the plain exhaust runs
      -- runs the real flatMap's lane at its carrier, read.
      ex-run→ : ∀ {q k′ a} → o q (out a) → Upto c q → Run.Img R₀ q k′ → Exhaust.Run g o q → Exhaust.Run g₂ o₂ (rd k′)
      -- A SWITCH'S CUT, READ: a lane row no later value cuts, framed, is
      -- cut by no later value read.
      cut-sw→ : ∀ L {k l₀ b} → TL L k (out b) → Upto c k → Run.Img (Rₗ L) k l₀ → ¬ Switch.Cut g o (lq L) k
              → ¬ Switch.Cut g₂ o₂ (rd (lk′ L)) (framed (lw L) l₀)
      -- THE REAL FLATMAP'S ROWS BEFORE A LANE ROW, FRAMED: few, wherever the
      -- plain flatMap's before the plain row are.
      few₂ : ∀ L {k l₀ b b₁} → TL L k (out b) → Upto c k → Reach J.JoinT k (out b) → Run.Img (Rₗ L) k l₀ → UL L l₀ (out b₁)
           → Few J₂.JoinT (framed (lw L) l₀)
      -- THE RELAY'S INPUT BEFORE A LANE ROW, FRAMED: listed.  Its rows are
      -- the shared outer's, the real flatMap's and the trackers' before
      -- it, each under the bound's image and so listed by the outer's,
      -- each lane's and each hot's simulation up to the row.
      relay-at : ∀ L {k l₀ b} → TL L k (out b) → Upto c k → Run.Img (Rₗ L) k l₀
               → Listed (enter RW.Dtk RW.p₄) (framed (lw L) l₀ ⊕ [ sub RW.z₃ ])

    runs→ : ∀ {op′} (j′ : Jn op′) {q k′ a} → o q (out a) → Upto c q → Run.Img R₀ q k′ → RunsOf j′ g o q → RunsOf j′ g₂ o₂ (rd k′)
    runs→ merge∞ _  _  _ _ = tt
    runs→ sw     _  _  _ _ = tt
    runs→ ex     oq uq i r = ex-run→ oq uq i r

    uncut→ : ∀ {op′} (j′ : Jn op′) L {k l₀ b} → TL L k (out b) → Upto c k → Run.Img (Rₗ L) k l₀ → ¬ CutOf j′ g o (lq L) k
           → ¬ CutOf j′ g₂ o₂ (rd (lk′ L)) (framed (lw L) l₀)
    uncut→ merge∞ L _  _ _  _  ()
    uncut→ sw     L tl u iₗ nc = cut-sw→ L tl u iₗ nc
    uncut→ ex     L _  _ _  _  ()

    -- RELAYED: a lane value the plain flatMap runs uncut, at an outer
    -- value whose carrier shows it, the real flatMap runs at the carrier,
    -- read, and the scan relays, its carrier's value framed.
    lane-row→ : ∀ L {k l₀ b b₀ b₁} → TL L k (out b) → Upto c k → (lq L ⊕ [ ix 1 ]) ≺ k → RunsOf j g o (lq L) → ¬ CutOf j g o (lq L) k
              → Reach J.JoinT k (out b) → U₀ (lk′ L) (out b₀) → Shows (la L) b₀ → Run.Img (Rₗ L) k l₀ → UL L l₀ (out b₁) → Shown b₁
              → U (relay (framed (lw L) l₀)) (out b₁)
    lane-row→ L {k} {l₀} {b} {b₀} {b₁} tl u ql rq nc re u₀ sh₀ iₗ ul sh₁ = RW.relay-fwd (relay-at L tl u iₗ) (r , proper-out Irf r) sh₁
      where
        uq : Upto c (lq L)
        uq = upto-dn c {k} {lq L} (≺-trans {lq L} {lq L ⊕ [ ix 1 ]} {k} (≺-ext (lq L) {ix 1} []) ql) u

        K : Pos
        K = framed (lw L) l₀

        IUL : InvAt (Hots (envₗ′ L)) (lsub′ L) (UL L)
        IUL = inv-approx n (g′ (la L)) (envₗ′ L) (good-l L) (lsub′ L) (ok-l′ L)

        aft : lsub′ L ≺ l₀
        aft = world-after (InvAt.world IUL ul) (InvAt.real IUL ul)

        lr : enter (g₂ (la L)) (lw L) K (out b₁)
        lr = RW.lane-fwd (la L) (lw L) (lane-at L tl (upto-b j nc u) iₗ) ul aft (λ {c} ce → proper-out IUL ul ce) (λ {k′} {y} r → undone-l L (lsub′ L) {k′} {y} r)

        ql₂ : lw L ≺ K
        ql₂ = ≼-≺-≺ {lw L} {lsub′ L} {K} (⊑-≼ (at-⊑ (lw L))) (≺-≼-≺ {lsub′ L} {l₀} {K} aft (⊑-≼ (framed-⊑ (lw L) l₀)))

        x₂ : J₂.JoinT K (out b₁)
        x₂ = J₂.lane (o₂-fwd u₀ sh₀) (runs→ j (lo L) uq (li L) rq) (lr , ql₂) (uncut→ j L tl u iₗ nc) tt

        r : RW.σRF K (out b₁)
        r = rf-in (x₂ , few-reach {q = K} {e = out b₁} (few₂ L tl u re iₗ ul))

    postulate
      lane-reach : ∀ L {k l₀ a b} (x : J.JoinT k (out a)) → Run.Img (Rₗ L) k l₀ → U (relay (framed (lw L) l₀)) (out b)
                 → Reach J.JoinT k (out a)
      -- An elaborated end up to the bound's image is the plain end's.
      flat-end← : ∀ {l} → U l end → Under A′ c l → Σ Pos λ k → T k end
      -- The elaborated rows up to the bound's image, listed.
      u-upto : Σ (List Pos) λ ls → (∀ {l e′} → U l e′ → Under A′ c l → l ∈ ls) × (∀ {l} → l ∈ ls → Σ (Ev (IE B)) (U l))

    fw : ∀ {k e} → T k e → Carried e → Upto c k → Σ Pos λ l → Img k l × Σ (Ev (IE B)) λ e′ → U l e′ × Mt Shows e e′
    fw (J.lane {q} {a} {k} {out b} oq rq (lr , ql) nc _ , re) c-out u =
      let (k′ , i₀ , _ , u₀x , m₀) = Sim.fwd S₀ oq c-out (upto-dn c {k} {q} (≺-trans {q} {q ⊕ [ ix 1 ]} {k} (≺-ext q {ix 1} []) ql) u)
          (_ , u₀r , sh₀) = mt-out {X = U₀ k′} u₀x m₀
          L = (q , k′ , a , oq , i₀)
          (l₀ , iₗ , _ , ulx , m₁) = Sim.fwd (SL L) lr c-out (upto-b j nc u)
          (b₁ , ulr , sh₁) = mt-out {X = UL L l₀} ulx m₁
      in relay (framed (lw L) l₀) , inj₁ (L , l₀ , iₗ , (b , lr) , refl) , out b₁ , lane-row→ L lr u ql rq nc re u₀r sh₀ iₗ ulr (shown-one sh₁)
       , m-out sh₁
    fw (J.run () _ , _) c-out u
    fw {k} x c-end u = let (l , ul) = flat-end→ x in l , inj₂ (x , ul) , end , ul , m-end

    bv : ∀ {l b} → U l (out b) → Shown b → Under A′ c l → Σ Pos λ k → Img k l × Σ B λ a → T k (out a) × Shows a b
    bv {l} {b} ul sh un =
      let (L , rL , l₀ , eq , b₁ , ulr , vq , un₀ , nc₂) = unrelay ul sh un
          (k , iₗ , a , tl , sh₁) = Sim.val← (SL L) ulr (λ e → sh (trans vq e)) un₀
          ur = subst (λ l′ → U l′ (out b)) eq ul
          uk = under-img c mp (inj₁ (L , l₀ , iₗ , (a , tl) , eq)) un
          x = J.lane {lq L} {la L} {k} {out a} (lo L) rL (tl , lane-after L tl) (uncut← j L tl iₗ uk nc₂) tt
      in k , inj₁ (L , l₀ , iₗ , (a , tl) , eq) , a , (x , lane-reach L x iₗ ur) , trans vq sh₁

    be : ∀ {l} → U l end → Under A′ c l → Σ Pos λ k → Img k l × T k end
    be ul un = let (k , tk) = flat-end← ul un in k , inj₂ (tk , ul) , tk

    sim-f : Sim Shows Shown A′ Img c T U
    sim-f = record { fwd = fw ; val← = bv ; end← = be ; upto = u-upto }

  ----------------------------------------------------------------------
  -- The run

  postulate
    -- THE LATE PINS of the flatMap: its outer's, and each lane's, framed
    -- and relayed.
    late-f : Lates (Amb ∪ᴹ M) (EnvListed ρ env env′ es T) T U
    -- A lane value's anchor: its lane's, wherever the flatMap is listed
    -- up to it.
    anchor-v : ∀ A′ → (Amb ∪ᴹ M) ⊆ᴹ A′ → Emb A′ → ∀ {k b} → T k (out b) → EnvListed ρ env env′ es T A′ (just k) → ListedB T (just k)
             → Σ Pos ((Amb ∪ᴹ M) k)

  anchor-f : ∀ A′ → (Amb ∪ᴹ M) ⊆ᴹ A′ → Emb A′ → ∀ {k e} → T k e → Carried e → EnvListed ρ env env′ es T A′ (just k) → ListedB T (just k)
           → Σ Pos ((Amb ∪ᴹ M) k)
  anchor-f A′ inc emA x c-out lr lst = anchor-v A′ inc emA x lr lst
  anchor-f A′ inc emA x c-end lr lst = let (l , ul) = flat-end→ x in l , inj₂ (inj₂ (inj₂ (x , ul)))

  run : Run Shows Shown (Amb ∪ᴹ M) (EnvListed ρ env env′ es T) T U
  run = record { Img = Img ; img-fun = flat-img ; ext = ext
               ; sim = λ A′ inc emA c mp lr lst → FSim.sim-f A′ inc emA c mp lr lst
               ; late = late-f ; anchor = anchor-f }

  postulate
    -- WHAT THE FLATMAP ADDS lies in its pair's worlds, keeps the order,
    -- pairs nothing under a plain row, and keeps every hot's joins.
    local-f : Local (Hots env) (Hots env′) p p′ M
    emb-f   : Emb (Amb ∪ᴹ M)
    none-f  : NoneUnder M T
    flat-joins    : EnvJoins ρ env env′ es M

  Goal : EmissionSet B → EmissionSet (IE B) → Set₁
  Goal T′ U′ = Σ PMap λ M′ → Local (Hots env) (Hots env′) p p′ M′ × Emb (Amb ∪ᴹ M′) × NoneUnder M′ T′ × EnvJoins ρ env env′ es M′
               × Run Shows Shown (Amb ∪ᴹ M′) (EnvListed ρ env env′ es T′) T′ U′

  result₀ : Goal T U
  result₀ = M , local-f , emb-f , none-f , flat-joins , run

  result : Goal (enter (approx n (flatMap op f s) env) p) U
  result = subst (λ T′ → Goal T′ U) (sym (inst j g ds p)) result₀

------------------------------------------------------------------------
-- The former

postulate
  -- A BOUNDED MERGE SIMULATES ITS BOUNDED MERGE: each lane at its
  -- schedule's start, the schedule decided by the same lanes' ends.
  sim-bounded : ∀ n {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) k (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
              → (∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → SimIH n ρ′ s)
              → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → SimIH n ρ′ (f a)) → SimIH n ρ (flatMap (mergeᶠ (just k)) f s)

sim-flatMap : ∀ n {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
            → (∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → SimIH n ρ′ s)
            → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → SimIH n ρ′ (f a)) → SimIH n ρ (flatMap op f s)
sim-flatMap n ρ (mergeᶠ (just k)) f s ihs ihf = sim-bounded n ρ k f s ihs ihf
sim-flatMap n ρ (mergeᶠ nothing) f s ihs ihf = sih λ env env′ Amb ge ge′ ap es en em p p′ pp fr ok ok′ nh →
  Flat.result n ρ {op = mergeᶠ nothing} merge∞ f s ihs ihf env env′ Amb ge ge′ ap es en em p p′ pp fr ok ok′ nh _ refl
sim-flatMap n ρ switchᶠ f s ihs ihf = sih λ env env′ Amb ge ge′ ap es en em p p′ pp fr ok ok′ nh →
  Flat.result n ρ {op = switchᶠ} sw f s ihs ihf env env′ Amb ge ge′ ap es en em p p′ pp fr ok ok′ nh _ refl
sim-flatMap n ρ exhaustᶠ f s ihs ihf = sih λ env env′ Amb ge ge′ ap es en em p p′ pp fr ok ok′ nh →
  Flat.result n ρ {op = exhaustᶠ} ex f s ihs ihf env env′ Amb ge ge′ ap es en em p p′ pp fr ok ok′ nh _ refl
