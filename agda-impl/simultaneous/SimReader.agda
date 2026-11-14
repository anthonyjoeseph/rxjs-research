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
open import denotation.Laws.Modulus using (≺-irrefl; ≺-ext; ≼-≺-≺; ≺-≼-≺; ≺→≼; entered-few)
open import denotation.Laws.Worlds using (Hots; Lawful; _⊑_; ⊑-≼; ⊑-refl; ⊑-trans; ⊑-snoc; ⊑-snoc⁺; ⊕-injˡ; ⊕-injʳ; ⊕-cancelˡ; ⊕-assoc;
  ⊕-identityʳ)
open import denotation.Laws.Worlds.Leaves using (module AccF)
open import adequacy.SubOne using (dep-un)
open import adequacy.SubJoin using (Bind; rejoin-reach)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Sim using (PMap; _∪ᴹ_; Emb; Sim; Carried; c-out; c-end; Mt; m-out; m-end; Local; Fresh; NoneUnder;
  Joins; Upto; Under; Mapped; Run; _⊆ᴹ_; allᴱ; Shows; Shown; AShows; AShown; HotSim; EnvSim;
  EnvListed; ListedB; EnvNeeds; EnvJoins; Apart; SimIH; sih)
open import simultaneous.SimPos using (UpTo)
open import simultaneous.ReadMap using (module Map; upto-dn; under?; under-down)
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

module Read {X : Set} (Amb : PMap) (H H′ : Pos → Set) (S : EmissionSet X) (G : EmissionSet (AIE X))
            (Car : Pos → Pos → Set) (car-fun : ∀ {k l l′} → Car k l → Car k l′ → l ≡ l′)
            (car-ext : ∀ {k l} → Car k l → Σ Pos λ y → Amb k y × y ⊑ l) (joins : Joins Amb Amb S Car)
            (lawS : Lawful S) (lawG : Lawful G)
            (fewS : ∀ {q e} → S q e → Unpinned e → Few S q) (fewG : ∀ {q e} → G q e → Unpinned e → Few G q)
            (hS : ∀ {q e} → S q e → H q) (hG : ∀ {q e} → G q e → H′ q)
            (em : Emb Amb) (p p′ : Pos) (pp : Amb p p′) (fr : Fresh H H′ Amb p p′) (nh : ¬ H p) where

  open Map Amb H H′ S G Car car-fun car-ext joins lawS lawG fewG hS hG em p p′ pp fr nh
  open Rows G p′ lawG fewG
  open AccF joinStep z₀ {R} r-func using (acc-func)

  T : EmissionSet X
  T = Truncate (Rejoin p S)

  M : PMap
  M = Amb ∪ᴹ Mr

  BS : Bind S
  BS = record { law = lawS ; few = fewS }

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

  ----------------------------------------------------------------------
  -- CUT AT A BOUND OF A LATER MAP: the hot cut at the same bound, and a
  -- reader's row up to it carried with the hot cut at its hot row, under
  -- whose anchor the row's carrier lies.  A row under the bound's image
  -- is over a hot row under it.

  module Cut (A′ : PMap) (inc : M ⊆ᴹ A′) (emA : Emb A′) (c : Maybe Pos) (mp : Mapped A′ c)
             (hs : Sim AShows AShown A′ Car c S G)
             (at-row : ∀ {q e} → S q e → Carried e → Upto c q → Mapped A′ (just q) × Sim AShows AShown A′ Car (just q) S G) where

    open Sim hs using () renaming (val← to val₀; end← to end₀; upto to upto₀)

    -- The hot cut at a row: its carrier under the row's anchor.
    module At {q e} (s : S q e) (ce : Carried e) (uq : Upto c q) where
      mq : Mapped A′ (just q)
      mq = proj₁ (at-row s ce uq)

      hq : Sim AShows AShown A′ Car (just q) S G
      hq = proj₂ (at-row s ce uq)
      open Sim hq public using () renaming (fwd to fwdq)
      open Rows.Listed G p′ lawG fewG (Under A′ (just q)) (under? {A′} (λ {x} {y} {y′} → Emb.fun emA {x} {y} {y′}) (just q) mq) (λ {l} {l′} → under-down {A′} (just q) {l} {l′})
                       (proj₁ (Sim.upto hq)) (λ g u → proj₁ (proj₂ (Sim.upto hq)) g u) (proj₂ (proj₂ (Sim.upto hq)))
        public using (acc; u-val; u-end; u-late)

      ug : ∀ {L} → Car q L → Under A′ (just q) L
      ug car with car-ext car
      ... | y , a , yL = proj₁ mq , proj₂ mq , inj₂ (subst (_⊑ _) (Emb.fun emA (inc (inj₁ a)) (proj₂ mq)) yL)

    open Rows.Listed G p′ lawG fewG (Under A′ c) (under? (Emb.fun emA) c mp) (λ {l} {l′} → under-down {A′} c {l} {l′})
                     (proj₁ upto₀) (λ g u → proj₁ (proj₂ upto₀) g u) (proj₂ (proj₂ upto₀))
      using (acc; ksU; covJ; backU; Good; g-row; g-late; u-val; u-end; u-late)

    -- A joined row up to the bound: its hot row too.
    row-up : ∀ {q} → Upto c (q ⊕ [ sub p ]) → Upto c q
    row-up {q} = upto-dn c (≺-ext q {sub p} [])

    late-up : ∀ {q} → q ≼ p → Upto c (p ⊕ [ last ]) → Upto c q
    late-up {q} qp = upto-dn c (≼-≺-≺ {q} {p} {p ⊕ [ last ]} qp (≺-ext p {last} []))

    -- A position under the image over a hot row: the hot row too.
    row-under : ∀ {l m} → at l ⊑ m → Under A′ c m → Under A′ c l
    row-under {l} {m} a = under-down {A′} c (≺-≼-≺ {l} {at l} {m} (≺-ext l {sub p′} []) (⊑-≼ {at l} {m} a))

    late-under : ∀ {c₂} → c₂ ≼ p′ → Under A′ c (p′ ⊕ [ last ]) → Under A′ c c₂
    late-under {c₂} cp = under-down {A′} c (≼-≺-≺ {c₂} {p′} {p′ ⊕ [ last ]} cp (≺-ext p′ {last} []))

    --------------------------------------------------------------------
    -- Forward: each plain value and end up to the bound, carried.

    fwd : ∀ {k e} → T k e → Carried e → Upto c k → Σ Pos λ l → Img k l × Σ (Ev (IE X)) λ e′ → U l e′ × Mt Shows e e′
    fwd (shown {q} s _ pk , _) c-out u with At.fwdq s c-out (row-up u) s c-out (inj₂ (⊑-refl _))
    ... | L′ , car , out (r , nothing) , g , m-out ()
    ... | L′ , car , out (r , just b) , g , m-out sh =
      _ , ival s pk car g (proj₂ (Q.acc g lv)) refl refl , out b , Q.u-val g lv , m-out sh
      where module Q = At s c-out (row-up u)
            lv = Q.ug car , past-sup pk car
    fwd (shown _ () _ , _) c-end _
    fwd (heard _ _ , _) () _
    fwd (ended {q} s pk , _) c-end u with At.fwdq s c-end (row-up u) s c-end (inj₂ (⊑-refl _))
    ... | L′ , car , _ , g , m-end = at L′ , iend s pk car g refl refl , end , Q.u-end g lv , m-end
      where module Q = At s c-end (row-up u)
            lv = Q.ug car , past-sup pk car
    fwd (late {q} sq qp , _) c-end u with At.fwdq sq c-end (late-up qp u) sq c-end (inj₂ (⊑-refl _))
    ... | E , car , _ , gE , m-end =
      p′ ⊕ [ last ] , ilate sq qp refl refl , end , Q.u-late gE (≺→≼ {E} {p′} (late-car sq qp car)) (Q.ug car) , m-end
      where module Q = At sq c-end (late-up qp u)

    --------------------------------------------------------------------
    -- Back: each value shown and each end under the bound's image
    -- carries one.

    val← : ∀ {l b} → U l (out b) → Shown b → Under A′ c l → Σ Pos λ k → Img k l × Σ X λ a → T k (out a) × Shows a b
    val← (j , _) sh u with u-val⁻ j sh
    ... | L′ , r , g , pL , s , a , refl with val₀ g sh (row-under (⊑-trans (⊑-snoc⁺ (at L′)) (⊑-snoc⁺ (at L′ ⊕ [ ix 1 ]))) u)
    ...   | q , car , x , sq , sh′ = q ⊕ [ sub p ] , ival sq pk car g a refl refl , x , (shown sq _ pk , rejoin-reach BS (shown sq _ pk) _) , sh′
      where pk = past-sub sq car pL

    end← : ∀ {l} → U l end → Under A′ c l → Σ Pos λ k → Img k l × T k end
    end← (j , _) u with u-end⁻ j
    ... | inj₁ (L′ , g , pL , refl) with end₀ g (row-under (⊑-refl _) u)
    ...   | q , car , sq = q ⊕ [ sub p ] , iend sq pk car g refl refl , (ended sq pk , rejoin-reach BS (ended sq pk) _)
      where pk = past-sub sq car pL
    end← (j , _) u | inj₂ (c₂ , g , cp , refl) with end₀ g (late-under cp u)
    ... | q , car , sq = p ⊕ [ last ] , ilate sq qp refl refl , (late sq qp , rejoin-reach BS (late sq qp) _)
      where qp : q ≼ p
            qp pq = cp (past-sup pq car)

    --------------------------------------------------------------------
    -- The reader's rows under the bound's image, listed.

    good : ∀ {m} → Origin m → Under A′ c m → Good m
    good (or-row g pl a)     u = g-row g pl a (row-under a u)
    good (or-late g cp refl) u = g-late g cp refl (late-under cp u)

    upto : Σ (List Pos) λ ls → (∀ {l e′} → U l e′ → Under A′ c l → l ∈ ls) × (∀ {l} → l ∈ ls → Σ (Ev (IE X)) (U l))
    upto = ksU , (λ x u → covJ (proj₁ x) (good (origin (proj₁ x)) u)) , backU

    -- THE READER SIMULATES ITS READER.
    sim : Sim Shows Shown A′ Img c T U
    sim = record { fwd = fwd ; val← = val← ; end← = end← ; upto = upto }

------------------------------------------------------------------------
-- The former

module Leaf {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) (env : DenEnv Γ) (env′ : DenEnv Δ) (Amb : PMap)
            (ap : Apart env) (es : EnvSim ρ Amb env env′) (en : EnvNeeds ρ env env′ es) (em : Emb Amb) (p p′ : Pos) (pp : Amb p p′)
            (fr : Fresh (Hots env) (Hots env′) Amb p p′) (nh : ¬ Hots env p) where
  open HotSim (es i) using (src; at; m; env₀; at′; rows; rows′; run; isP; isE; law; law′; joins) renaming (core to body; car to Car)
  open Run run using () renaming (img-fun to car-fun; ext to car-ext)
  open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (annotate)
  open import denotation.EmissionSet using (approx)

  fewS = proper-few src at
  fewG = proper-few (approx m (annotate body) env₀) at′
  hS = hots-at env i isP
  hG = hots-at env′ (ρ (∈-map⁺ AIE i)) isE

  open Map Amb (Hots env) (Hots env′) rows rows′ Car car-fun car-ext joins law law′ fewG hS hG em p p′ pp fr nh
    using (Mr; mrow; mlate; local; emb; none-under)
  module RD = Read Amb (Hots env) (Hots env′) rows rows′ Car car-fun car-ext joins law law′ fewS fewG hS hG em p p′ pp fr nh

  z₀ = Rows.z₀ rows′ p′ law′ fewG

  Goal : Den A → Den (AIE A) → Set₁
  Goal d d′ = Σ PMap λ M → Local (Hots env) (Hots env′) p p′ M × Emb (Amb ∪ᴹ M) × NoneUnder M (enter d p)
      × EnvJoins ρ env env′ es M
      × Run Shows Shown (Amb ∪ᴹ M) (EnvListed ρ env env′ es) (enter d p)
          (enter (Op.flatMap (mergeᶠ nothing) (λ s → Op.of (proj₂ s)) (Op.scan joinStep z₀ d′)) p′)

  -- THE READER KEEPS EVERY BOUND HOT'S JOINS: a point it puts under a
  -- row is that row's join, or lies under an ambient point under it.
  reader-joins : EnvJoins ρ env env′ es Mr
  reader-joins i′ (mrow s _ _ car _ refl refl) q′ e with join-split e
  ... | inj₁ (refl , refl) with same-hot env ap i i′ isP (HotSim.isP (es i′)) s q′
  ...   | refl = p , refl , p′ , inj₁ pp , _ , car , ⊑-refl _
  reader-joins i′ (mrow {L = L} s _ _ car _ refl refl) q′ e | inj₂ (b , τ , refl , refl) with car-ext car
  ... | yk , ak , ykL with HotSim.joins (es i′) ak q′ refl
  ...   | e₁ , refl , e₁′ , a₁ , L₁ , car₁ , h = e₁ , refl , e₁′ , inj₁ a₁ , L₁ , car₁ , ⊑-trans h (⊑-trans ykL (⊑-snoc⁺ L))
  reader-joins i′ (mlate _ _ refl refl) q′ e with join-split e
  ... | inj₁ (refl , refl) = ⊥-elim (nh (hots-at env i′ (HotSim.isP (es i′)) q′))
  ... | inj₂ (b , τ , pe , refl) with HotSim.joins (es i′) pp q′ pe
  ...   | e₁ , refl , e₁′ , a₁ , L₁ , car₁ , h = e₁ , refl , e₁′ , inj₁ a₁ , L₁ , car₁ , ⊑-trans h (⊑-snoc⁺ p′)

  -- Listed up to a bound: listed up to a hot row up to it.
  listed-up : ∀ c {k e₀} → rows k e₀ → Upto c k → ListedB rows c → ListedB rows (just k)
  listed-up c {k} s uk (ks , cov , back) = ks , (λ y u → cov y (up y u)) , back
    where
      up : ∀ {j e} → rows j e → UpTo k j → Upto c j
      up {j} _ (inj₁ jk)             = upto-dn c jk uk
      up     _ (inj₂ ([] , refl))    = subst (Upto c) (sym (⊕-identityʳ k)) uk
      up     y (inj₂ (_ ∷ _ , refl)) = ⊥-elim (Lawful.flat law s y)

  -- The hot cut at a row up to a bound, mapped at its anchor.
  at-row : ∀ A′ → (Amb ∪ᴹ Mr) ⊆ᴹ A′ → Emb A′ → ∀ c → EnvListed ρ env env′ es A′ c
         → ∀ {q e} → rows q e → Carried e → Upto c q → Mapped A′ (just q) × Sim AShows AShown A′ Car (just q) rows rows′
  at-row A′ inc emA c L {q} s ce uq = mq , Run.sim run A′ inc′ emA (just q) mq nq lq
    where
      inc′ : Amb ⊆ᴹ A′
      inc′ a = inc (inj₁ a)
      nq = HotSim.need-row (es i) s uq (en i A′ c L)
      lq = listed-up c s uq (allᴱ L i)
      mq : Mapped A′ (just q)
      mq with Run.anchor run A′ inc′ emA s ce nq lq
      ... | y , a = y , inc′ a

  joined : ∀ A′ → (Amb ∪ᴹ Mr) ⊆ᴹ A′ → Emb A′ → ∀ {q e} → rows q e → Carried e → (pk : p ≺ q)
         → EnvListed ρ env env′ es A′ (just (q ⊕ [ sub p ])) → Σ Pos ((Amb ∪ᴹ Mr) (q ⊕ [ sub p ]))
  joined A′ inc emA {q} s ce pk L with Sim.fwd (proj₂ (at-row A′ inc emA (just (q ⊕ [ sub p ])) L s ce (inj₁ (≺-ext q {sub p} [])))) s ce (inj₂ (⊑-refl _))
  ... | L′ , car , _ , g , _ = L′ ⊕ [ sub p′ ] , inj₂ (mrow s ce pk car g refl refl)

  -- A joined row's anchor: its hot row's carrier joined, the hot cut at
  -- its row.
  anchor : ∀ A′ → (Amb ∪ᴹ Mr) ⊆ᴹ A′ → Emb A′ → ∀ {x e} → RD.T x e → Carried e → EnvListed ρ env env′ es A′ (just x)
         → ListedB RD.T (just x) → Σ Pos ((Amb ∪ᴹ Mr) x)
  anchor A′ inc emA (shown {q} s _ pk , _) ce L _ = joined A′ inc emA s ce pk L
  anchor A′ inc emA (ended {q} s pk , _)   ce L _ = joined A′ inc emA s c-end pk L
  anchor A′ inc emA (late sq qp , _)       ce L _ = p′ ⊕ [ last ] , inj₂ (mlate sq qp refl refl)
  anchor A′ inc emA (heard _ _ , _)        ()

  -- The reader's carriers come first; cut at a later map's bound, the hot
  -- is cut at the same bound.
  core : Goal (hot rows) (hot rows′)
  core = Mr , local , emb , none-under , reader-joins
       , record { Img = RD.Img ; img-fun = RD.img-fun ; ext = RD.ext
                ; sim = λ A′ inc emA c mp L _ → RD.Cut.sim A′ inc emA c mp
                          (Run.sim run A′ (λ a → inc (inj₁ a)) emA c mp (en i A′ c L) (allᴱ L i)) (at-row A′ inc emA c L)
                ; anchor = anchor }

  leaf : Goal (lookup env i) (lookup env′ (ρ (∈-map⁺ AIE i)))
  leaf = subst₂ Goal (sym isP) (sym isE) core

sim-connected : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) → SimIH n ρ (connected i)
sim-connected n ρ i = sih λ env env′ Amb ge ge′ ap es en em p p′ pp fr ok ok′ nh →
  Leaf.leaf ρ i env env′ Amb ap es en em p p′ pp fr nh
