{-# OPTIONS --guardedness #-}

-- A READER SIMULATES ITS READER: the plain reader joins the hot's proper
-- rows past its subscription; the elaborated one joins the annotated
-- rows past its own, folds them by `joinStep` and merges each fold's
-- list.  A plain value at the hot row `k` is carried by the last value
-- of the lane of `k`'s carrier joined; an end by the elaborated end.
-- Each joined row is anchored at its hot row's carrier joined at the
-- subscription's image (`Map.Mr`).
module simultaneous.SimReader where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; length)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (lookup) renaming (_∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (pred)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Nullary using (¬_)

open import Tree using (connected; mergeᶠ)
open import denotation.Position using (Pos; Label; Path; root; _≟ᵖ_; _⊕_; sub; ix; last)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; end; Unpinned; Few; EmissionSet; Den; hot; coldAt; Proper; Truncate; Rejoin;
  shown; heard; ended; late; _≺_; _≼_; enter; module Scan; module Op; DenEnv)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-ext; ≼-refl; ≼-≺-≺; ≺→≼; entered-few)
open import denotation.Laws.Worlds using (Hots; Lawful; _⊑_; ⊑-refl; ⊑-trans; ⊑-snoc; ⊑-snoc⁺; ⊕-injˡ; ⊕-injʳ; ⊕-cancelˡ; ⊕-assoc;
  ⊕-identityʳ)
open import denotation.Laws.Worlds.Leaves using (module AccF)
open import adequacy.SubOne using (dep-un)
open import adequacy.SubJoin using (Bind; rejoin-reach)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Sim using (PMap; _∪ᴹ_; Emb; Sim; Carried; c-out; c-end; Mt; m-out; m-end; Local; Fresh; NoneUnder; Joins;
  ListedB; BoundOk; Within; Upto; Under; Mapped; Shows; Shown; AShows; AShown; HotSim; EnvSim; EnvJoins; Apart; SimIH; sih)
open import simultaneous.ReadMap using (module Map; up₀; under?; under-down)
open import simultaneous.ReadRows using (module Rows)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; joinStep)

-- An entered binder's proper rows: few before each unpinned one.
proper-few : ∀ {A} (d : Den A) p {q e} → Proper (enter d p) q e → Unpinned e → Few (Proper (enter d p)) q
proper-few d p r u with entered-few d p (dep-un u) (proj₁ r)
... | ks , h = ks , λ y lt → h (proj₁ y) lt

-- A bound hot's rows lie among the environment's hots.
hots-at : ∀ {Γ} (env : DenEnv Γ) {A} (i : A ∈ Γ) {t : EmissionSet A} → lookup env i ≡ hot t → ∀ {q e} → t q e → Hots env q
hots-at (hot _ ∷ᴬ _)    (here refl) refl x = inj₁ (_ , x)
hots-at (coldAt _ ∷ᴬ _) (here refl) ()   _
hots-at (hot _ ∷ᴬ env)    (there i) eq   x = inj₂ (hots-at env i eq x)
hots-at (coldAt _ ∷ᴬ env) (there i) eq   x = hots-at env i eq x

-- NO POSITION HOLDS ROWS OF TWO HOTS: two bound hots with a row at one
-- position are one.
same-hot : ∀ {Γ} (env : DenEnv Γ) → Apart env → ∀ {X X′} (i : X ∈ Γ) (i′ : X′ ∈ Γ) {t : EmissionSet X} {t′ : EmissionSet X′}
         → lookup env i ≡ hot t → lookup env i′ ≡ hot t′ → ∀ {q e e′} → t q e → t′ q e′ → _≡_ {A = Σ Set (_∈ Γ)} (X , i) (X′ , i′)
same-hot (hot _ ∷ᴬ _)      _        (here refl) (here refl) _    _    _ _  = refl
same-hot (coldAt _ ∷ᴬ _)   _        (here refl) _           ()   _    _ _
same-hot (coldAt _ ∷ᴬ _)   _        _           (here refl) _    ()   _ _
same-hot (hot _ ∷ᴬ env)    (ap , _) (here refl) (there i′)  refl eq′  x x′ = ⊥-elim (ap x (hots-at env i′ eq′ x′))
same-hot (hot _ ∷ᴬ env)    (ap , _) (there i)   (here refl) eq   refl x x′ = ⊥-elim (ap x′ (hots-at env i eq x))
same-hot (hot _ ∷ᴬ env)    (_ , ap) (there i)   (there i′)  eq   eq′  x x′ with same-hot env ap i i′ eq eq′ x x′
... | refl = refl
same-hot (coldAt _ ∷ᴬ env) ap       (there i)   (there i′)  eq   eq′  x x′ with same-hot env ap i i′ eq eq′ x x′
... | refl = refl

-- A position under a row joined: the join itself, or under the row.
join-split : ∀ {k q a₀ a σ} → k ⊕ [ a₀ ] ≡ q ⊕ (a ∷ σ) → (k ≡ q × a ≡ a₀) ⊎ Σ Label λ b → Σ Path λ τ → k ≡ q ⊕ (b ∷ τ) × a ≡ b
join-split {k} {q} {a₀} {a} {σ} e with ⊑-snoc k {a₀} (a ∷ σ , e)
... | inj₂ e′ = ⊥-elim (≺-irrefl {q} (subst (q ≺_) (sym (trans e′ e)) (≺-ext q {a} σ)))
... | inj₁ ([] , refl) with ⊕-cancelˡ q [ a₀ ] (a ∷ σ) (trans (sym (⊕-assoc q [] [ a₀ ])) e)
...   | refl = inj₁ (⊕-identityʳ q , refl)
join-split {k} {q} {a₀} {a} {σ} e | inj₁ ((b ∷ τ) , refl) with ⊕-cancelˡ q ((b ∷ τ) ++ [ a₀ ]) (a ∷ σ) (trans (sym (⊕-assoc q (b ∷ τ) [ a₀ ])) e)
... | refl = inj₂ (b , τ , refl , refl)

------------------------------------------------------------------------
-- A reading, plain and elaborated

module Read {X : Set} (Amb : PMap) (H H′ : Pos → Set) (S : EmissionSet X) (G : EmissionSet (AIE X)) {c₀}
            (hs : Sim AShows AShown Amb c₀ S G) (joins : Joins Amb Amb S (Sim.Img hs))
            (lawS : Lawful S) (lawG : Lawful G)
            (fewS : ∀ {q e} → S q e → Unpinned e → Few S q) (fewG : ∀ {q e} → G q e → Unpinned e → Few G q)
            (hS : ∀ {q e} → S q e → H q) (hG : ∀ {q e} → G q e → H′ q)
            (em : Emb Amb) (p p′ : Pos) (pp : Amb p p′) (fr : Fresh H H′ Amb p p′) (nh : ¬ H p)
            (c : Maybe Pos) (within : Within c c₀) (B : BoundOk H′ Amb (Truncate (Rejoin p S)) c) where

  open Map Amb H H′ S G hs joins lawS lawG fewG hS hG em p p′ pp fr nh
  open Rows G p′ lawG fewG
  open Sim hs using () renaming (Img to Car; img-fun to car-fun; bnd to bnd₀; fwd to fwd₀; val← to val₀; end← to end₀; upto to upto₀)
  open Emb em using () renaming (fun to a-fun)
  open AccF joinStep z₀ {R} r-func using (acc-func)

  T : EmissionSet X
  T = Truncate (Rejoin p S)

  M : PMap
  M = Amb ∪ᴹ Mr

  BS : Bind S
  BS = record { law = lawS ; few = fewS }

  -- The hot's end at or before the subscription: up to the hot's bound.
  late-up : ∀ {q} → q ≼ p → Upto c (p ⊕ [ last ]) → Upto c₀ q
  late-up {q} qp u = up₀ c c₀ within u (≼-≺-≺ {q} {p} {p ⊕ [ last ]} qp (≺-ext p {last} []))

  lc : LateCar c
  lc sq qp u with fwd₀ sq c-end (late-up qp u)
  ... | E , car , _ , gE , m-end = E , car , gE

  module LS = Rows.Listed G p′ lawG fewG (Under Amb c₀) (under? a-fun c₀ bnd₀) (λ {l} {l′} → under-down {Amb} c₀ {l} {l′})
                (proj₁ upto₀) (λ g u → proj₁ (proj₂ upto₀) g u) (proj₂ (proj₂ upto₀))
  open LS using (acc; ksU; covJ; backU; Good; g-row; g-late; u-val; u-end; u-late)

  ----------------------------------------------------------------------
  -- THE READER'S CARRIERS: a joined value at the last value of its
  -- carrier's lane, a joined end at its carrier joined, the late end at
  -- the late end.

  data Img (x l : Pos) : Set where
    ival  : ∀ {k a L r b s} → S k (out a) → p ≺ k → Car k L → G L (out (r , just b)) → Scan.Acc joinStep z₀ R (at L) s
          → x ≡ k ⊕ [ sub p ] → l ≡ at L ⊕ [ ix 1 ] ⊕ [ ix (pred (length (proj₂ s))) ] → Img x l
    iend  : ∀ {k L} → S k end → p ≺ k → Car k L → G L end → x ≡ k ⊕ [ sub p ] → l ≡ at L → Img x l
    ilate : ∀ {q} → S q end → q ≼ p → x ≡ p ⊕ [ last ] → l ≡ p′ ⊕ [ last ] → Img x l

  img-fun : ∀ {x l l′} → Img x l → Img x l′ → l ≡ l′
  img-fun (ival {k} {L = L} _ _ car g a refl refl) (ival {k′} _ _ car′ g′ a′ ex refl) with ⊕-injˡ k k′ ex
  ... | refl with car-fun car car′
  ...   | refl with Lawful.func lawG g g′
  ...     | refl = cong (λ s → at L ⊕ [ ix 1 ] ⊕ [ ix (pred (length (proj₂ s))) ]) (acc-func refl a a′)
  img-fun (ival {k} s _ _ _ _ refl _) (iend {k′} s′ _ _ _ ex _) with ⊕-injˡ k k′ ex
  ... | refl with Lawful.func lawS s s′
  ...   | ()
  img-fun (iend {k} s _ _ _ refl _) (ival {k′} s′ _ _ _ _ ex _) with ⊕-injˡ k k′ ex
  ... | refl with Lawful.func lawS s s′
  ...   | ()
  img-fun (iend {k} _ _ car _ refl refl) (iend {k′} _ _ car′ _ ex refl) with ⊕-injˡ k k′ ex
  ... | refl = cong at (car-fun car car′)
  img-fun (ival {k} _ _ _ _ _ refl _) (ilate _ _ ex _) with ⊕-injʳ k p ex
  ... | ()
  img-fun (iend {k} _ _ _ _ refl _) (ilate _ _ ex _) with ⊕-injʳ k p ex
  ... | ()
  img-fun (ilate _ _ refl _) (ival {k} _ _ _ _ _ ex _) with ⊕-injʳ p k ex
  ... | ()
  img-fun (ilate _ _ refl _) (iend {k} _ _ _ _ ex _) with ⊕-injʳ p k ex
  ... | ()
  img-fun (ilate _ _ _ refl) (ilate _ _ _ refl) = refl

  ext : ∀ {x l} → Img x l → Σ Pos λ y → M x y × y ⊑ l
  ext (ival {L = L} s pk car g _ refl refl) = at L , inj₂ (mrow s c-out pk car g refl refl) , ⊑-trans (⊑-snoc⁺ (at L)) (⊑-snoc⁺ (at L ⊕ [ ix 1 ]))
  ext (iend {L = L} s pk car g refl refl)   = at L , inj₂ (mrow s c-end pk car g refl refl) , ⊑-refl _
  ext (ilate sq qp refl refl)               = p′ ⊕ [ last ] , inj₂ (mlate sq qp refl refl) , ⊑-refl _

  -- The bound's image: ambient, or a plain value's or end's.
  bound : ∀ c′ → Within c′ c₀ → BoundOk H′ Amb T c′ → Mapped M c′
  bound nothing   _  _                  = _
  bound (just _) _ (inj₁ (y , a , _)) = y , inj₁ a
  bound (just _) cc (inj₂ (_ , c-out , (shown {q} s _ pk , _))) with fwd₀ s c-out (up₀ _ c₀ cc (≼-refl {q ⊕ [ sub p ]}) (≺-ext q {sub p} []))
  ... | L′ , car , _ , g , _ = L′ ⊕ [ sub p′ ] , inj₂ (mrow s c-out pk car g refl refl)
  bound (just _) cc (inj₂ (_ , c-end , (shown _ () _ , _)))
  bound (just _) cc (inj₂ (_ , c-end , (ended {q} s pk , _))) with fwd₀ s c-end (up₀ _ c₀ cc (≼-refl {q ⊕ [ sub p ]}) (≺-ext q {sub p} []))
  ... | L′ , car , _ , g , _ = L′ ⊕ [ sub p′ ] , inj₂ (mrow s c-end pk car g refl refl)
  bound (just _) cc (inj₂ (_ , c-end , (late sq qp , _))) = p′ ⊕ [ last ] , inj₂ (mlate sq qp refl refl)

  ----------------------------------------------------------------------
  -- Forward: each plain value and end up to the bound, carried.

  fwd : ∀ {k e} → T k e → Carried e → Upto c k → Σ Pos λ l → Img k l × Σ (Ev (IE X)) λ e′ → U l e′ × Mt Shows e e′
  fwd (shown {q} s _ pk , _) c-out u with fwd₀ s c-out (up₀ c c₀ within u (≺-ext q {sub p} []))
  ... | L′ , car , out (r , nothing) , g , m-out ()
  ... | L′ , car , out (r , just b) , g , m-out sh =
    _ , ival s pk car g (proj₂ (acc g lv)) refl refl , out b , u-val g lv , m-out sh
    where lv = car-ug c₀ bnd₀ s car (up₀ c c₀ within u (≺-ext q {sub p} [])) , past-sup pk car
  fwd (shown _ () _ , _) c-end _
  fwd (heard _ _ , _) () _
  fwd (ended {q} s pk , _) c-end u with fwd₀ s c-end (up₀ c c₀ within u (≺-ext q {sub p} []))
  ... | L′ , car , _ , g , m-end = at L′ , iend s pk car g refl refl , end , u-end g lv , m-end
    where lv = car-ug c₀ bnd₀ s car (up₀ c c₀ within u (≺-ext q {sub p} [])) , past-sup pk car
  fwd (late {q} sq qp , _) c-end u with fwd₀ sq c-end (late-up qp u)
  ... | E , car , _ , gE , m-end =
    p′ ⊕ [ last ] , ilate sq qp refl refl , end , u-late gE (≺→≼ {E} {p′} (late-car sq qp car)) (car-ug c₀ bnd₀ sq car (late-up qp u)) , m-end

  ----------------------------------------------------------------------
  -- Back: each value shown and each end under the bound's image carries
  -- one.

  val← : ∀ {l b} → U l (out b) → Shown b → Under M c l → Σ Pos λ k → Img k l × Σ X λ a → T k (out a) × Shows a b
  val← (j , _) sh u with u-val⁻ j sh
  ... | L′ , r , g , pL , s , a , refl with val₀ g sh (under-row c c₀ within bnd₀ B lc g pL (⊑-trans (⊑-snoc⁺ (at L′)) (⊑-snoc⁺ (at L′ ⊕ [ ix 1 ]))) u)
  ...   | q , car , x , sq , sh′ = q ⊕ [ sub p ] , ival sq pk car g a refl refl , x , (shown sq _ pk , rejoin-reach BS (shown sq _ pk) _) , sh′
    where pk = past-sub sq car pL

  end← : ∀ {l} → U l end → Under M c l → Σ Pos λ k → Img k l × T k end
  end← (j , _) u with u-end⁻ j
  ... | inj₁ (L′ , g , pL , refl) with end₀ g (under-row c c₀ within bnd₀ B lc g pL (⊑-refl _) u)
  ...   | q , car , sq = q ⊕ [ sub p ] , iend sq pk car g refl refl , (ended sq pk , rejoin-reach BS (ended sq pk) _)
    where pk = past-sub sq car pL
  end← (j , _) u | inj₂ (c₂ , g , cp , refl) with end₀ g (under-late c c₀ within bnd₀ B lc g cp u)
  ... | q , car , sq = p ⊕ [ last ] , ilate sq qp refl refl , (late sq qp , rejoin-reach BS (late sq qp) _)
    where qp : q ≼ p
          qp pq = cp (past-sup pq car)

  ----------------------------------------------------------------------
  -- The reader's rows under the bound's image, listed.

  good : ∀ {m} → Origin m → Under M c m → Good m
  good (or-row g pl a)     u = g-row g pl a (under-row c c₀ within bnd₀ B lc g pl a u)
  good (or-late g cp refl) u = g-late g cp refl (under-late c c₀ within bnd₀ B lc g cp u)

  upto : Σ (List Pos) λ ls → (∀ {l e′} → U l e′ → Under M c l → l ∈ ls) × (∀ {l} → l ∈ ls → Σ (Ev (IE X)) (U l))
  upto = ksU , (λ x u → covJ (proj₁ x) (good (origin (proj₁ x)) u)) , backU

  -- THE READER SIMULATES ITS READER.
  sim : Sim Shows Shown M c T U
  sim = record { Img = Img ; img-fun = img-fun ; ext = ext ; bnd = bound c within B ; fwd = fwd ; val← = val← ; end← = end← ; upto = upto }

------------------------------------------------------------------------
-- The former

module Leaf {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) (env : DenEnv Γ) (env′ : DenEnv Δ) (Amb : PMap) (c : Maybe Pos)
            (ap : Apart env) (es : EnvSim ρ Amb c env env′) (em : Emb Amb) (p p′ : Pos) (pp : Amb p p′)
            (fr : Fresh (Hots env) (Hots env′) Amb p p′) (nh : ¬ Hots env p) where
  open HotSim (es i) using (src; at; m; env₀; at′; rows; rows′; sim; isP; isE; law; law′; within; joins) renaming (core to body)
  open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (annotate)
  open import denotation.EmissionSet using (approx)

  fewS = proper-few src at
  fewG = proper-few (approx m (annotate body) env₀) at′
  hS = hots-at env i isP
  hG = hots-at env′ (ρ (∈-map⁺ AIE i)) isE

  open Map Amb (Hots env) (Hots env′) rows rows′ sim joins law law′ fewG hS hG em p p′ pp fr nh using (Mr; mrow; mlate; local; emb; none-under)
  module RD = Read Amb (Hots env) (Hots env′) rows rows′ sim joins law law′ fewS fewG hS hG em p p′ pp fr nh c within

  z₀ = Rows.z₀ rows′ p′ law′ fewG

  Goal : Den A → Den (AIE A) → Set₁
  Goal d d′ = ListedB (enter d p) c → BoundOk (Hots env′) Amb (enter d p) c
    → Σ PMap λ M → Local (Hots env) (Hots env′) p p′ M × Emb (Amb ∪ᴹ M) × NoneUnder M (enter d p)
      × EnvJoins ρ env env′ es M
      × Sim Shows Shown (Amb ∪ᴹ M) c (enter d p) (enter (Op.flatMap (mergeᶠ nothing) (λ s → Op.of (proj₂ s)) (Op.scan joinStep z₀ d′)) p′)

  -- THE READER KEEPS EVERY BOUND HOT'S JOINS: a point it puts under a
  -- row is that row's join, or lies under an ambient point under it.
  reader-joins : EnvJoins ρ env env′ es Mr
  reader-joins i′ (mrow s _ _ car _ refl refl) q′ e with join-split e
  ... | inj₁ (refl , refl) with same-hot env ap i i′ isP (HotSim.isP (es i′)) s q′
  ...   | refl = p , refl , p′ , inj₁ pp , _ , car , ⊑-refl _
  reader-joins i′ (mrow {L = L} s _ _ car _ refl refl) q′ e | inj₂ (b , τ , refl , refl) with Sim.ext sim car
  ... | yk , ak , ykL with HotSim.joins (es i′) ak q′ refl
  ...   | e₁ , refl , e₁′ , a₁ , L₁ , car₁ , h = e₁ , refl , e₁′ , inj₁ a₁ , L₁ , car₁ , ⊑-trans h (⊑-trans ykL (⊑-snoc⁺ L))
  reader-joins i′ (mlate _ _ refl refl) q′ e with join-split e
  ... | inj₁ (refl , refl) = ⊥-elim (nh (hots-at env i′ (HotSim.isP (es i′)) q′))
  ... | inj₂ (b , τ , pe , refl) with HotSim.joins (es i′) pp q′ pe
  ...   | e₁ , refl , e₁′ , a₁ , L₁ , car₁ , h = e₁ , refl , e₁′ , inj₁ a₁ , L₁ , car₁ , ⊑-trans h (⊑-snoc⁺ p′)

  core : Goal (hot rows) (hot rows′)
  core _ B = Mr , local , emb , none-under , reader-joins , RD.sim B

  leaf : Goal (lookup env i) (lookup env′ (ρ (∈-map⁺ AIE i)))
  leaf = subst₂ Goal (sym isP) (sym isE) core

sim-connected : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) → SimIH n ρ (connected i)
sim-connected n ρ i = sih λ env env′ Amb c ge ge′ ap es em p p′ pp fr ok ok′ nh L B →
  Leaf.leaf ρ i env env′ Amb c ap es em p p′ pp fr nh L B
