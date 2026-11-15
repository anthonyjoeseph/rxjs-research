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
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; flatMap; connect; connected; of)
open import denotation.Position using (Pos; root; _≟ᵖ_; _⊕_; ix; sub)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; end; EmissionSet; Den; hot; DenEnv; Proper; Truncate; Reach; _≺_; enter; approx; module Op;
  module Joiner; module Switch; module Exhaust)
open import denotation.Laws using (inv-approx; good-cons)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; Lawful; _⊑_; ⊑-refl; ⊑-trans; ⊑-snoc⁺)
import denotation.Laws.Connect as LC
open import denotation.Laws.Modulus using (≺-trans; ≺-ext; ≺-≼-≺)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Sim using (PMap; _∪ᴹ_; _⊆ᴹ_; Emb; Fresh; Local; NoneUnder; Sim; Run; Lates; Mt; m-out; m-end; Carried; c-out; c-end;
  Upto; Under; Mapped; ListedB; Shows; Shown; HotSim; EnvSim; EnvListed; EnvNeeds; EnvJoins; Joins; Apart; SimIH; sih; foot; outerAt;
  Live; env-live)
open import simultaneous.ReadMap using (upto-dn)
open import simultaneous.SimConnect using (Pair; hot-up)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; E; elab; closer; laneˢ; each; combined; trackers)

------------------------------------------------------------------------
-- The unbounded joiners

-- A flatMap whose lanes start where their values arrive.
data Jn : FlatOp → Set where
  merge∞ : Jn (mergeᶠ nothing)
  sw     : Jn switchᶠ
  ex     : Jn exhaustᶠ

-- Which values run a lane.
RunsOf : ∀ {op A Y} → Jn op → (A → Den Y) → EmissionSet A → Pos → Set
RunsOf merge∞ g o _ = ⊤
RunsOf sw     g o _ = ⊤
RunsOf ex     g o q = Exhaust.Run g o q

-- Where a lane is cut.
CutOf : ∀ {op A Y} → Jn op → (A → Den Y) → EmissionSet A → Pos → Pos → Set
CutOf merge∞ g o _ _ = ⊥
CutOf sw     g o q k = Switch.Cut g o q k
CutOf ex     g o _ _ = ⊥

-- Each is its joiner.
inst : ∀ {op A Y} (j : Jn op) (g : A → Den Y) (d : Den A) p
     → enter (Op.flatMap op g d) p ≡ Truncate (Joiner.JoinT g (enter d p) (RunsOf j g (enter d p)) (CutOf j g (enter d p)))
inst merge∞ g d p = refl
inst sw     g d p = refl
inst ex     g d p = refl

------------------------------------------------------------------------
-- Where the elaboration puts things

-- Where a framed lane subscribes its lane, under the frame's
-- subscription: the lane part's share, then its gate.
laneAt : Pos → Pos
laneAt w = (outerAt ((w ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]

-- Where a framed lane's frame reads its lane's rows: the frame's middle
-- piece, past its start.
frameAt : Pos → Pos
frameAt w = ((((((w ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ])

-- A lane row, framed: read, counted.
framed : Pos → Pos → Pos
framed w l = ((l ⊕ [ sub (frameAt w) ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]

-- A value's match is a value.
mt-out : ∀ {A B : Set} {V : A → B → Set} {a} {e′ : Ev B} {X : Ev B → Set} → X e′ → Mt V (out a) e′ → Σ B λ b → X (out b) × V a b
mt-out x (m-out v) = _ , x , v

module Flat (n : ℕ) {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) {op : FlatOp} (j : Jn op)
            (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
            (ihs : ∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → SimIH n ρ′ s)
            (ihf : ∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → SimIH n ρ′ (f a))
            (env : DenEnv Γ) (env′ : DenEnv Δ) (Amb : PMap) (ge : GoodEnv env) (ge′ : GoodEnv env′) (ap : Apart env)
            (es : EnvSim ρ Amb env env′) (en : EnvNeeds ρ env env′ es) (em : Emb Amb)
            (p p′ : Pos) (pp : Amb p (foot s (outerAt p′))) (fr : Fresh (Hots env) (Hots env′) Amb p (foot s (outerAt p′)))
            (ok : Ok (Hots env) p) (ok′ : Ok (Hots env′) p′) (nh : ¬ Hots env p) where

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

  U : EmissionSet (IE B)
  U = enter (approx n (elab ρ (flatMap op f s)) env′) p′

  -- The trigger, its shared outer, the outer's closer.
  σtt : EmissionSet ⊤
  σtt = enter (Op.of (tt ∷ [])) (p′ ⊕ [ ix 1 ])

  env₀′ : DenEnv (⊤ ∷ Δ)
  env₀′ = hot (Proper σtt) ∷ᴬ env′

  σ₁ : EmissionSet (IE A)
  σ₁ = enter (approx n (flatMap (mergeᶠ nothing) (λ _ → s′) (connected (here refl))) env₀′) ((p′ ⊕ [ ix 0 ]) ⊕ [ ix 1 ])

  env₁′ : DenEnv (IE A ∷ ⊤ ∷ Δ)
  env₁′ = hot (Proper σ₁) ∷ᴬ env₀′

  σcl : EmissionSet (IE B)
  σcl = enter (approx n closer env₁′) (((p′ ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ])

  envY : DenEnv (IE B ∷ IE A ∷ ⊤ ∷ Δ)
  envY = hot (Proper σcl) ∷ᴬ env₁′

  -- The real flatMap: its outer the shared outer's values, its lanes
  -- framed.
  z₂ : Pos
  z₂ = (((p′ ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]

  o₂ : EmissionSet A
  o₂ = enter (approx n (each valuesOf (connected (there (here refl)))) envY) z₂

  g₂ : A → Den (IE B)
  g₂ a = approx n (laneˢ (g′ a)) envY

  module J₂ = Joiner g₂ o₂ (RunsOf j g₂ o₂) (CutOf j g₂ o₂)

  -- An outer row, read by the real flatMap.
  rd : Pos → Pos
  rd k′ = ((k′ ⊕ [ sub z₂ ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]

  -- Where the scan beside the real flatMap reads its rows.
  z₃ : Pos
  z₃ = ((((((((p′ ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ] ⊕ [ ix 1 ]

  -- A real flatMap row, relayed by the scan.
  relay : Pos → Pos
  relay k = ((k ⊕ [ sub z₃ ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]

  ----------------------------------------------------------------------
  -- The outer at the foot

  q₀′ : Pos
  q₀′ = outerAt p′

  -- What the trigger's one row runs.
  body : E (⊤ ∷ Δ) (IE B)
  body = connect (flatMap (mergeᶠ nothing) (λ _ → s′) (connected (here refl)))
           (connect closer (connect (flatMap op (λ a → laneˢ (g′ a)) (each valuesOf (connected (there (here refl)))))
             (combined op (trackers Γ 0 ρₜ))))

  shared : elab ρ (flatMap op f s) ≡ connect (of (tt ∷ [])) body
  shared = refl

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
  -- The lanes at their pairs

  -- A running lane: its value's row, and that row's carrier.
  LaneIx : Set
  LaneIx = Σ Pos λ q → Σ Pos λ k′ → Σ A λ a → o q (out a) × RunsOf j g o q × Run.Img R₀ q k′

  lq : LaneIx → Pos
  lq L = proj₁ L

  lk′ : LaneIx → Pos
  lk′ L = proj₁ (proj₂ L)

  la : LaneIx → A
  la L = proj₁ (proj₂ (proj₂ L))

  -- The real flatMap's lane, and where its frame subscribes the lane.
  lw : LaneIx → Pos
  lw L = rd (lk′ L) ⊕ [ ix 1 ]

  lsub′ : LaneIx → Pos
  lsub′ L = laneAt (lw L)

  lfoot : LaneIx → Pos
  lfoot L = foot (f (la L)) (lsub′ L)

  -- The lane's share's trigger.
  σttₗ : LaneIx → EmissionSet ⊤
  σttₗ L = enter (Op.of (tt ∷ [])) ((((lw L ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]))

  envₗ′ : LaneIx → DenEnv (⊤ ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ)
  envₗ′ L = hot (Proper (σttₗ L)) ∷ᴬ envY

  Ambₗ : LaneIx → PMap
  Ambₗ L = (Amb ∪ᴹ M₀) ∪ᴹ Pair (lq L ⊕ [ ix 1 ]) (lfoot L)

  TL : LaneIx → EmissionSet B
  TL L = enter (g (la L)) (lq L ⊕ [ ix 1 ])

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

  esₗ : ∀ L → EnvSim ρₗ (Ambₗ L) env (envₗ′ L)
  esₗ L i = hot-up (λ a → inj₁ (inj₁ a)) (es i) (joins-l L i)

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

  ext : ∀ {k l} → Img k l → Σ Pos λ y → (Amb ∪ᴹ M) k y × y ⊑ l
  ext (inj₁ (L , l₀ , i , _ , refl)) =
    let (y , a , yl) = Run.ext (Rₗ L) i in y , lane-⊆ L a , ⊑-trans yl (relay-⊑ (lw L) l₀)
  ext {k} {l} (inj₂ e) = l , inj₂ (inj₂ (inj₂ e)) , ⊑-refl l

  postulate
    -- One carrier each: a lane row is one lane's, and a value no end.
    flat-img : ∀ {k l l′} → Img k l → Img k l′ → l ≡ l′

  ----------------------------------------------------------------------
  -- The outer, wherever the flatMap is

  U₀ : EmissionSet (IE A)
  U₀ = enter (approx n s′ env₀′) q₀′

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

    postulate
      -- EACH RUNNING LANE'S BOUND: the flatMap's bound, or the lane's
      -- cut, mapped, its rows and hots listed, and every row of the lane
      -- the flatMap shows up to its bound up to it.
      lane-bound : ∀ L → Σ (Maybe Pos) λ b → Mapped A′ b × EnvListed ρₗ env (envₗ′ L) (esₗ L) (TL L) A′ b × ListedB (TL L) b
                 × (∀ {k e} → TL L k e → ¬ CutOf j g o (lq L) k → Upto c k → Upto b k)

    SL : ∀ L → Sim Shows Shown A′ (Run.Img (Rₗ L)) (proj₁ (lane-bound L)) (TL L) (UL L)
    SL L = let (b , mb , lb , lsb , _) = lane-bound L in Run.sim (Rₗ L) A′ (λ m → inc (lane-⊆ L m)) emA b mb lb lsb

    postulate
      -- RELAYED: an uncut lane value the plain flatMap runs at an outer
      -- value whose carrier shows it, the elaborated flatMap runs, frames
      -- and relays, showing what the lane's carrier shows.
      lane-row→ : ∀ L {k l₀ b b₀ b₁} → TL L k (out b) → (lq L ⊕ [ ix 1 ]) ≺ k → ¬ CutOf j g o (lq L) k
                → U₀ (lk′ L) (out b₀) → Shows (la L) b₀ → Run.Img (Rₗ L) k l₀ → UL L l₀ (out b₁)
                → Σ (IE B) λ b₂ → U (relay (framed (lw L) l₀)) (out b₂) × valuesOf b₂ ≡ valuesOf b₁
      -- UNRELAYED: a value the elaborated flatMap shows up to the
      -- bound's image is a running lane's value, framed and relayed, up
      -- to the lane's bound's image.
      unrelay : ∀ {l b} → U l (out b) → Shown b → Under A′ c l
              → Σ LaneIx λ L → Σ Pos λ l₀ → l ≡ relay (framed (lw L) l₀) × Σ (IE B) λ b₁ → UL L l₀ (out b₁)
                × valuesOf b ≡ valuesOf b₁ × Under A′ (proj₁ (lane-bound L)) l₀
      -- A lane value relayed is past the lane's subscription and uncut,
      -- and the plain flatMap reaches it.
      lane-uncut : ∀ L {k l₀ a b} → TL L k (out a) → Run.Img (Rₗ L) k l₀ → U (relay (framed (lw L) l₀)) (out b)
               → (lq L ⊕ [ ix 1 ]) ≺ k × ¬ CutOf j g o (lq L) k
      lane-reach : ∀ L {k l₀ a b} (x : J.JoinT k (out a)) → Run.Img (Rₗ L) k l₀ → U (relay (framed (lw L) l₀)) (out b)
                 → Reach J.JoinT k (out a)
      -- An elaborated end up to the bound's image is the plain end's.
      flat-end← : ∀ {l} → U l end → Under A′ c l → Σ Pos λ k → T k end
      -- The elaborated rows up to the bound's image, listed.
      u-upto : Σ (List Pos) λ ls → (∀ {l e′} → U l e′ → Under A′ c l → l ∈ ls) × (∀ {l} → l ∈ ls → Σ (Ev (IE B)) (U l))

    fw : ∀ {k e} → T k e → Carried e → Upto c k → Σ Pos λ l → Img k l × Σ (Ev (IE B)) λ e′ → U l e′ × Mt Shows e e′
    fw (J.lane {q} {a} {k} {out b} oq rq (lr , ql) nc _ , _) c-out u =
      let (k′ , i₀ , _ , u₀x , m₀) = Sim.fwd S₀ oq c-out (upto-dn c {k} {q} (≺-trans {q} {q ⊕ [ ix 1 ]} {k} (≺-ext q {ix 1} []) ql) u)
          (_ , u₀r , sh₀) = mt-out {X = U₀ k′} u₀x m₀
          L = (q , k′ , a , oq , rq , i₀)
          (l₀ , iₗ , _ , ulx , m₁) = Sim.fwd (SL L) lr c-out (proj₂ (proj₂ (proj₂ (proj₂ (lane-bound L)))) lr nc u)
          (_ , ulr , sh₁) = mt-out {X = UL L l₀} ulx m₁
          (b₂ , ur , eq) = lane-row→ L lr ql nc u₀r sh₀ iₗ ulr
      in relay (framed (lw L) l₀) , inj₁ (L , l₀ , iₗ , (b , lr) , refl) , out b₂ , ur , m-out (trans eq sh₁)
    fw (J.run () _ , _) c-out u
    fw {k} x c-end u = let (l , ul) = flat-end→ x in l , inj₂ (x , ul) , end , ul , m-end

    bv : ∀ {l b} → U l (out b) → Shown b → Under A′ c l → Σ Pos λ k → Img k l × Σ B λ a → T k (out a) × Shows a b
    bv {l} {b} ul sh un =
      let (L , l₀ , eq , b₁ , ulr , vq , un₀) = unrelay ul sh un
          (k , iₗ , a , tl , sh₁) = Sim.val← (SL L) ulr (λ e → sh (trans vq e)) un₀
          ur = subst (λ l′ → U l′ (out b)) eq ul
          (ql , nc) = lane-uncut L tl iₗ ur
          x = J.lane {lq L} {la L} {k} {out a} (proj₁ (proj₂ (proj₂ (proj₂ L)))) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ L))))) (tl , ql) nc tt
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

  Goal : EmissionSet B → Set₁
  Goal T′ = Σ PMap λ M′ → Local (Hots env) (Hots env′) p p′ M′ × Emb (Amb ∪ᴹ M′) × NoneUnder M′ T′ × EnvJoins ρ env env′ es M′
            × Run Shows Shown (Amb ∪ᴹ M′) (EnvListed ρ env env′ es T′) T′ U

  result : Goal (enter (Op.flatMap op g ds) p)
  result = subst Goal (sym (inst j g ds p)) (M , local-f , emb-f , none-f , flat-joins , run)

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
  Flat.result n ρ merge∞ f s ihs ihf env env′ Amb ge ge′ ap es en em p p′ pp fr ok ok′ nh
sim-flatMap n ρ switchᶠ f s ihs ihf = sih λ env env′ Amb ge ge′ ap es en em p p′ pp fr ok ok′ nh →
  Flat.result n ρ sw f s ihs ihf env env′ Amb ge ge′ ap es en em p p′ pp fr ok ok′ nh
sim-flatMap n ρ exhaustᶠ f s ihs ihf = sih λ env env′ Amb ge ge′ ap es en em p p′ pp fr ok ok′ nh →
  Flat.result n ρ ex f s ihs ihf env env′ Amb ge ge′ ap es en em p p′ pp fr ok ok′ nh
