{-# OPTIONS --guardedness #-}

-- FINITELY MANY READER ROWS LIE UNDER A SOURCE ROW.  Every layer between
-- the source and the reader puts its rows at a fixed path below a row of
-- the layer beneath: the annotation's connect one label below a source
-- row or at its body's fixed rows, the hot `sub` its subscription below,
-- the scan and the map in place, the merge one label below its outer row
-- or inside a lane.  A row that lies below both `y₀` and the row it was
-- put under has that row comparable with `y₀`: below `y₀`, where the layer
-- beneath already lists it, or one of `y₀`'s finitely many prefixes.  The
-- lanes are `of`s whose lengths the reader's first scan state bounds, and
-- a value row of the reader reaches that state.
module simultaneous.HeldFan where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; length)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (n≤1+n; ≤-trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Tree using (mergeᶠ)
open import denotation.Position using (Pos; ix; sub; last; _⊕_; _∙_; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh; ofᴱ)
open import denotation.EmissionSet using (EmissionSet; Den; enter; out; hot; Proper; InE; at-out; at-end; on-out; module Op; module Merge; module Scan; module Connecting; LaneOf; _≼_; shown; heard; ended; late; map-out; map-skip; map-pin; map-end)
open import denotation.Laws.Worlds using (InvAt; Hots; ⊕-assoc; ⊕-identityʳ; ⊕-injˡ; ∙-inj; ok-step)
open import denotation.Laws.Modulus using (≼-antisym)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.LaneLocal using (inv-ev)
open import simultaneous.DenRows using (hot-out)
open import simultaneous.HeldComb using (ev)
open import simultaneous.HeldBase using (Bound; Ann)
open import simultaneous.HeldHot using (prefixes; prefix-in)
open import simultaneous.HeldClose using (split₂)
open import simultaneous.HeldRead using (RD; Rl; Src; Rl-trans; rd-mg; module AnnConn; ev-ann; ev-cn; Fm; CnO; JS; Fl; lane-in; row-each; z₀)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; annotate; annStep; joinStep)

------------------------------------------------------------------------
-- Prefixes

-- Two prefixes of one position are comparable.
cmp : ∀ {y x y₀} → Rl y x → Rl y y₀ → Rl x y₀ ⊎ Rl y₀ x
cmp {x = i ∙ q} {j ∙ r} (zs , refl) (ws , eq) with ∙-inj eq
... | refl , eq′ with split₂ q zs r eq′
...   | inj₁ (us , e , _) = inj₂ (us , cong (i ∙_) e)
...   | inj₂ (us , e , _) = inj₁ (us , cong (i ∙_) e)

-- A ROW PUT UNDER `x` AND LYING UNDER `y₀`: `x` is listed below `y₀`, or
-- is one of `y₀`'s prefixes.
cand : ∀ {x y y₀ ks} → (Rl x y₀ → x ∈ ks) → Rl y x → Rl y y₀ → x ∈ ks ++ prefixes y₀
cand h yx yy with cmp yx yy
... | inj₁ r = ∈-++⁺ˡ (h r)
... | inj₂ (zs , eq) = ∈-++⁺ʳ _ (prefix-in _ zs eq)

at-f : ∀ {x y₀ ks} (f : Pos → Pos) → Rl (f x) x → (Rl x y₀ → x ∈ ks) → Rl (f x) y₀ → f x ∈ L.map f (ks ++ prefixes y₀)
at-f {x} f fx h r = ∈-map⁺ f (cand {x} h fx r)

at-ext : ∀ {x y₀ ks} zs → (Rl x y₀ → x ∈ ks) → Rl (x ⊕ zs) y₀ → x ⊕ zs ∈ L.map (_⊕ zs) (ks ++ prefixes y₀)
at-ext {x} zs = at-f {x} (_⊕ zs) (zs , refl)

-- A hot reading's rows: its source's, a `sub` below; or its late end.
HL : Pos → Pos → List Pos → List Pos
HL p y₀ ks = L.map (_⊕ [ sub p ]) (ks ++ prefixes y₀) ++ [ p ⊕ [ last ] ]

hot-in : ∀ {A} {t : EmissionSet A} p y₀ ks → (∀ {q e} → t q e → Rl q y₀ → q ∈ ks)
       → ∀ {k e} → enter (hot t) p k e → Rl k y₀ → k ∈ HL p y₀ ks
hot-in p y₀ ks h (shown x _ _ , _) r = ∈-++⁺ˡ (at-ext [ sub p ] (h x) r)
hot-in p y₀ ks h (heard x _ , _)   r = ∈-++⁺ˡ (at-ext [ sub p ] (h x) r)
hot-in p y₀ ks h (ended x _ , _)   r = ∈-++⁺ˡ (at-ext [ sub p ] (h x) r)
hot-in p y₀ ks h (late _ _ , _)    r = ∈-++⁺ʳ _ (here refl)

-- A scan keeps its source's positions.
scan-in : ∀ {A B} (f : B → A → B) z (d : Den A) p {y₀ ks} → (∀ {q e} → enter d p q e → Rl q y₀ → q ∈ ks)
        → ∀ {k e} → enter (Op.scan f z d) p k e → Rl k y₀ → k ∈ ks
scan-in f z d p h (Scan.sval (Scan.acc₀ t _) , _)   r = h t r
scan-in f z d p h (Scan.sval (Scan.acc _ t _ _) , _) r = h t r
scan-in f z d p h (Scan.sstep t , _)                r = h t r
scan-in f z d p h (Scan.spin t , _)                 r = h t r
scan-in f z d p h (Scan.send t , _)                 r = h t r

-- So does a map.
map-in : ∀ {A B} (f : A → B) (d : Den A) p {y₀ ks} → (∀ {q e} → enter d p q e → Rl q y₀ → q ∈ ks)
       → ∀ {k e} → enter (Op.map f d) p k e → Rl k y₀ → k ∈ ks
map-in f d p h (map-out t , _)  r = h t r
map-in f d p h (map-skip t , _) r = h t r
map-in f d p h (map-pin t , _)  r = h t r
map-in f d p h (map-end t , _)  r = h t r

------------------------------------------------------------------------
-- A scan state's lanes

-- An `of` no longer than `n`, from index `i`.
ofPos : Pos → ℕ → ℕ → List Pos
ofPos s i zero    = [ s ⊕ [ last ] ]
ofPos s i (suc n) = (s ⊕ [ ix i ]) ∷ ofPos s (suc i) n

last-in : ∀ s i n → s ⊕ [ last ] ∈ ofPos s i n
last-in s i zero    = here refl
last-in s i (suc n) = there (last-in s (suc i) n)

of-pos : ∀ {A} s i (xs : List A) n → length xs ≤ n → ∀ {y e} → InE (ofᴱ s i xs) y e → y ∈ ofPos s i n
of-pos s i []       n       _       at-end     = last-in s i n
of-pos s i (x ∷ xs) (suc n) _       at-out     = here refl
of-pos s i (x ∷ xs) (suc n) (s≤s l) (on-out r) = there (of-pos s (suc i) xs n l r)

bind : List Pos → (Pos → List Pos) → List Pos
bind []       f = []
bind (q ∷ qs) f = f q ++ bind qs f

bind-in : ∀ {q k} qs (f : Pos → List Pos) → q ∈ qs → k ∈ f q → k ∈ bind qs f
bind-in (q ∷ qs) f (here refl) i = ∈-++⁺ˡ i
bind-in (q ∷ qs) f (there j)   i = ∈-++⁺ʳ (f q) (bind-in qs f j i)

-- Every row of a scan state's lanes, its lists no longer than `n`.
FL : Pos → ℕ → List Pos
FL s n = O ++ L.map (_⊕ [ ix 0 ]) O ++ bind O (λ q → ofPos (q ⊕ [ ix 1 ]) 0 n)
  where O = ofPos s 0 2

fl-in : ∀ {X} (st : JS X) s n → length (proj₁ (proj₂ st)) ≤ n → length (proj₂ (proj₂ st)) ≤ n
      → ∀ {k e} → enter (Fl st) s k e → k ∈ FL s n
fl-in {X} st s n lj le (r , _) = go r
  where
    F : Bool → Den (IE X)
    F c = Op.of (if c then proj₁ (proj₂ st) else proj₂ (proj₂ st))
    O : List Pos
    O = ofPos s 0 2
    module Mg = Merge F (enter (Op.of (true ∷ false ∷ [])) s)
    o : ∀ {q e} → enter (Op.of (true ∷ false ∷ [])) s q e → q ∈ O
    o x = of-pos s 0 (true ∷ false ∷ []) 2 (s≤s (s≤s z≤n)) (proj₁ x)
    len : ∀ c → length (if c then proj₁ (proj₂ st) else proj₂ (proj₂ st)) ≤ n
    len true  = lj
    len false = le
    viaL : ∀ {q a k e} → enter (Op.of (true ∷ false ∷ [])) s q (out a) → LaneOf F q a k e → k ∈ FL s n
    viaL {q} {a} x (l , _) = ∈-++⁺ʳ O (∈-++⁺ʳ (L.map (_⊕ [ ix 0 ]) O)
                               (bind-in O (λ q′ → ofPos (q′ ⊕ [ ix 1 ]) 0 n) (o x) (of-pos (q ⊕ [ ix 1 ]) 0 _ n (len a) (proj₁ l))))
    go : ∀ {k e} → Mg.JoinT k e → k ∈ FL s n
    go (Mg.val x)              = ∈-++⁺ʳ O (∈-++⁺ˡ (∈-map⁺ (_⊕ [ ix 0 ]) (o x)))
    go (Mg.step x)             = ∈-++⁺ˡ (o x)
    go (Mg.opin x)             = ∈-++⁺ˡ (o x)
    go (Mg.oend x _)           = ∈-++⁺ˡ (o x)
    go (Mg.opass x _)          = ∈-++⁺ˡ (o x)
    go (Mg.lane x _ L _ _)     = viaL x L
    go (Mg.lend x _ L _ _ _)   = viaL x L
    go (Mg.lpass x _ L _ _ _)  = viaL x L
    go (Mg.hand _ _ _ _ ())
    go (Mg.left x _ L _ _)     = viaL x L
    go (Mg.run () _)
    go (Mg.rend () _ _)
    go (Mg.rpass () _ _)
    go (Mg.rhand () _)

------------------------------------------------------------------------
-- The annotation

-- THE ANNOTATION'S ROWS UNDER A SOURCE ROW: the source row's own, one
-- label below, and its hot reading's, besides the body's fixed rows.
module AnnFan {X} {d : Den (AIE X)} {cs} (b : Bound d cs) (y₀ : Pos) where
  module A = AnnConn b

  K : List Pos
  K = [ y₀ ]

  KS : List Pos
  KS = HL A.sb y₀ K

  UL : List Pos
  UL = KS ++ L.map A.CT.hpos (KS ++ prefixes y₀) ++ L.map A.CT.mpos (KS ++ prefixes y₀) ++ L.map A.CT.fpos (KS ++ prefixes y₀)

  AL : List Pos
  AL = L.map (_⊕ [ ix 0 ]) (K ++ prefixes y₀) ++ A.CT.base ++ UL

  IS : InvAt (Hots (Bound.env b)) A.r₁ (Src b)
  IS = inv-ev (Bound.m b) (Bound.src b) (Bound.env b) (Bound.good b) A.r₁ (ok-step A.a₁ A.ok₁)

  module _ {e₀} (sy : Src b y₀ e₀) where
    -- The source is flat: the one source row under `y₀` is `y₀`.
    σ-in : ∀ {k e} → A.σ k e → Rl k y₀ → k ∈ K
    σ-in x ([] , eq)     = here (trans eq (⊕-identityʳ y₀))
    σ-in x (l ∷ ls , eq) = ⊥-elim (InvAt.flat IS sy (subst (λ z → Src b z (proj₁ (A.MR.unmap x))) eq (proj₁ (proj₂ (A.MR.unmap x)))))

    hr-in : ∀ {k e} → A.HR.Rd k e → Rl k y₀ → k ∈ KS
    hr-in = hot-in A.sb y₀ K (λ x → σ-in (proj₁ x))

    u-in : ∀ {k e} → A.CT.U k e → Rl k y₀ → k ∈ UL
    u-in (A.CT.src y _) r = ∈-++⁺ˡ (hr-in (A.to y) r)
    u-in (A.CT.hnd {c} y) r =
      ∈-++⁺ʳ KS (∈-++⁺ˡ (at-f {c} A.CT.hpos ([ ix 0 ] , refl) (hr-in (A.to y)) r))
    u-in (A.CT.mk {c} y) r =
      ∈-++⁺ʳ KS (∈-++⁺ʳ (L.map A.CT.hpos (KS ++ prefixes y₀))
        (∈-++⁺ˡ (at-f {c} A.CT.mpos (ix 1 ∷ ix 0 ∷ [] , ⊕-assoc c [ ix 1 ] [ ix 0 ]) (hr-in (A.to y)) r)))
    u-in (A.CT.fin {c} y) r =
      ∈-++⁺ʳ KS (∈-++⁺ʳ (L.map A.CT.hpos (KS ++ prefixes y₀)) (∈-++⁺ʳ (L.map A.CT.mpos (KS ++ prefixes y₀))
        (at-f {c} A.CT.fpos (ix 1 ∷ last ∷ [] , ⊕-assoc c [ ix 1 ] [ last ]) (hr-in (A.to y)) r)))

    c-in : ∀ {k e} → A.CT.C k e → Rl k y₀ → k ∈ A.CT.base ++ UL
    c-in y r with A.CT.classify (proj₁ y)
    ... | inj₁ i       = ∈-++⁺ˡ i
    ... | inj₂ (_ , u) = ∈-++⁺ʳ A.CT.base (u-in u r)

    module Cc = Connecting A.a₁ A.σ (enter (Fm (Bound.m b) (Bound.env b) (hot (Proper A.σ))) A.P₀)

    cc-in : ∀ {k e} → enter (Op.connect (Op.map just A.D) (Fm (Bound.m b) (Bound.env b))) A.a₁ k e → Rl k y₀ → k ∈ AL
    cc-in (Cc.body y , _)       r = ∈-++⁺ʳ (L.map (_⊕ [ ix 0 ]) (K ++ prefixes y₀)) (c-in y r)
    cc-in (Cc.burst y _ , _)    r = ∈-++⁺ˡ (at-ext [ ix 0 ] (σ-in y) r)
    cc-in (Cc.echo y _ _ _ , _) r = ∈-++⁺ˡ (at-ext [ ix 0 ] (σ-in y) r)
    cc-in (Cc.kept y _ _ _ , _) r = ∈-++⁺ˡ (at-ext [ ix 0 ] (σ-in y) r)

    cn-in : ∀ {k e} → enter (ev (Bound.m b) (CnO (Bound.src b)) (Bound.env b)) A.a₁ k e → Rl k y₀ → k ∈ AL
    cn-in {k} {e} x = cc-in (subst (λ D′ → enter D′ A.a₁ k e) (ev-cn (Bound.m b) (Bound.src b) (Bound.env b)) x)

    ann-in : ∀ {k e} → Ann b k e → Rl k y₀ → k ∈ AL
    ann-in {k} {e} x =
      map-in proj₂ (Op.scan annStep z₀ (ev (Bound.m b) (CnO (Bound.src b)) (Bound.env b))) A.a₁
        (scan-in annStep z₀ (ev (Bound.m b) (CnO (Bound.src b)) (Bound.env b)) A.a₁ cn-in)
        (subst (λ D′ → enter D′ A.a₁ k e) (ev-ann (Bound.m b) (Bound.src b) (Bound.env b)) x)

------------------------------------------------------------------------
-- The reader's scan states

seed : ∀ {X} → JS X
seed = true , ([] , [])

js-flag : ∀ {X} (st : JS X) a → proj₁ (joinStep st a) ≡ false
js-flag (true  , _) (_ , just _)  = refl
js-flag (true  , _) (_ , nothing) = refl
js-flag (false , _) (_ , just _)  = refl
js-flag (false , _) (_ , nothing) = refl

js-later : ∀ {X} (st : JS X) a → proj₁ st ≡ false → proj₁ (proj₂ (joinStep st a)) ≡ []
js-later (false , _) (_ , just _)  refl = refl
js-later (false , _) (_ , nothing) refl = refl

js-emit : ∀ {X} (st : JS X) a → length (proj₂ (proj₂ (joinStep st a))) ≤ 1
js-emit (true  , _) (_ , just _)  = s≤s z≤n
js-emit (true  , _) (_ , nothing) = z≤n
js-emit (false , _) (_ , just _)  = s≤s z≤n
js-emit (false , _) (_ , nothing) = z≤n

------------------------------------------------------------------------
-- The reader

module RdFan {X} {d : Den (AIE X)} {cs} (b : Bound d cs) (p : Pos) where
  D : Den (AIE X)
  D = hot (Proper (Ann b))

  H : EmissionSet (AIE X)
  H = enter D p

  Sc : Den (JS X)
  Sc = Op.scan joinStep seed D

  module SA = Scan joinStep seed H

  IA : InvAt (Hots (Bound.env b)) (Bound.at b ⊕ [ ix 1 ]) (Ann b)
  IA = inv-ev (Bound.m b) (annotate (Bound.src b)) (Bound.env b) (Bound.good b) (Bound.at b ⊕ [ ix 1 ]) (ok-step (Bound.at b) (Bound.ok b))

  -- The hot shows one value at a position.
  h-func : ∀ {q a a′} → H q (out a) → H q (out a′) → a ≡ a′
  h-func x x′ with hot-out x | hot-out x′
  ... | q₁ , (a₁ , _) , _ , refl | q₂ , (a₂ , _) , _ , e with ⊕-injˡ q₁ q₂ e
  ...   | refl with InvAt.func IA a₁ a₂
  ...     | refl = refl

  -- The scan's first value.
  First : Set
  First = Σ Pos λ q₀ → Σ (AIE X) λ a₀ → H q₀ (out a₀) × (∀ {k c} → H k (out c) → q₀ ≼ k)

  first : ∀ {q st} → SA.Acc q st → First
  first (Scan.acc₀ t m)   = _ , _ , t , m
  first (Scan.acc ac _ _ _) = first ac

  acc-flag : ∀ {q st} → SA.Acc q st → proj₁ st ≡ false
  acc-flag (Scan.acc₀ {a = a} _ _)       = js-flag seed a
  acc-flag (Scan.acc {b = st} {a′ = a} _ _ _ _) = js-flag st a

  acc-emit : ∀ {q st} → SA.Acc q st → length (proj₂ (proj₂ st)) ≤ 1
  acc-emit (Scan.acc₀ {a = a} _ _)       = js-emit seed a
  acc-emit (Scan.acc {b = st} {a′ = a} _ _ _ _) = js-emit st a

  module _ (F₀ : First) where
    a₀ : AIE X
    a₀ = proj₁ (proj₂ F₀)

    -- The joins the first state carries.
    J₀ : List _
    J₀ = proj₁ (proj₂ (joinStep seed a₀))

    n : ℕ
    n = suc (length J₀)

    -- Every state's joins are the first's, or none.
    acc-joins : ∀ {q st} → SA.Acc q st → length (proj₁ (proj₂ st)) ≤ n
    acc-joins (Scan.acc₀ {q} {a} t m) with ≼-antisym {q} {proj₁ F₀} (m (proj₁ (proj₂ (proj₂ F₀)))) (proj₂ (proj₂ (proj₂ F₀)) t)
    ... | refl with h-func t (proj₁ (proj₂ (proj₂ F₀)))
    ...   | refl = n≤1+n (length J₀)
    acc-joins (Scan.acc {b = st} {a′ = a} ac _ _ _) =
      subst (λ l → length l ≤ n) (sym (js-later st a (acc-flag ac))) z≤n

    acc-emit′ : ∀ {q st} → SA.Acc q st → length (proj₂ (proj₂ st)) ≤ n
    acc-emit′ ac = ≤-trans (acc-emit ac) (s≤s z≤n)

    module _ (y₀ : Pos) where
      open AnnFan b y₀ using (AL; ann-in)

      SL : List Pos
      SL = HL p y₀ AL

      LL : List Pos
      LL = bind (SL ++ prefixes y₀) (λ q → FL (q ⊕ [ ix 1 ]) n)

      RL : List Pos
      RL = SL ++ L.map (_⊕ [ ix 0 ]) (SL ++ prefixes y₀) ++ LL

      module _ {e₀} (sy : Src b y₀ e₀) where
        sc-in : ∀ {k e} → enter Sc p k e → Rl k y₀ → k ∈ SL
        sc-in = scan-in joinStep seed D p (hot-in p y₀ AL (λ x → ann-in sy (proj₁ x)))

        module Mg = Merge Fl (enter Sc p)

        viaL : ∀ {q st k e} → enter Sc p q (out st) → LaneOf Fl q st k e → Rl k y₀ → k ∈ RL
        viaL {q} {st} x@(Scan.sval ac , _) (l , _) r =
          ∈-++⁺ʳ SL (∈-++⁺ʳ (L.map (_⊕ [ ix 0 ]) (SL ++ prefixes y₀))
            (bind-in (SL ++ prefixes y₀) (λ q′ → FL (q′ ⊕ [ ix 1 ]) n)
              (cand {q} (sc-in x) (Rl-trans (lane-in st (q ⊕ [ ix 1 ]) l) ([ ix 1 ] , refl)) r)
              (fl-in st (q ⊕ [ ix 1 ]) n (acc-joins ac) (acc-emit′ ac) l)))

        rd-in : ∀ {k e} → enter (Op.flatMap (mergeᶠ nothing) Fl Sc) p k e → Rl k y₀ → k ∈ RL
        rd-in (Mg.val {q} x , _)         r = ∈-++⁺ʳ SL (∈-++⁺ˡ (at-ext {q} [ ix 0 ] (sc-in x) r))
        rd-in (Mg.step x , _)            r = ∈-++⁺ˡ (sc-in x r)
        rd-in (Mg.opin x , _)            r = ∈-++⁺ˡ (sc-in x r)
        rd-in (Mg.oend x _ , _)          r = ∈-++⁺ˡ (sc-in x r)
        rd-in (Mg.opass x _ , _)         r = ∈-++⁺ˡ (sc-in x r)
        rd-in (Mg.lane x _ L _ _ , _)    r = viaL x L r
        rd-in (Mg.lend x _ L _ _ _ , _)  r = viaL x L r
        rd-in (Mg.lpass x _ L _ _ _ , _) r = viaL x L r
        rd-in (Mg.hand _ _ _ _ () , _)
        rd-in (Mg.left x _ L _ _ , _)    r = viaL x L r
        rd-in (Mg.run () _ , _)
        rd-in (Mg.rend () _ _ , _)
        rd-in (Mg.rpass () _ _ , _)
        rd-in (Mg.rhand () _ , _)

-- FINITELY MANY READER ROWS LIE UNDER A SOURCE ROW, given a value row of
-- the reader: it reaches the scan's first state, which bounds the lanes.
--
-- DEAD ROUTE: with no reader row in hand the list cannot be built
--   constructively — whether the scan has a first row at all is undecidable,
--   and the first row's lane count is the source's join count at an unknown
--   row, with no bound from `y₀`.
opaque
  read-fan : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p {w x} → enter (RD d) p w (out x) → ∀ y₀
           → Σ (List Pos) λ ks → ∀ {y e e₀} → enter (RD d) p y e → Src b y₀ e₀ → Rl y y₀ → y ∈ ks
  read-fan {X} {d} b p {w} {x} rw y₀ = RdFan.RL b p F₀ y₀ , λ {y} {e} r sy → RdFan.rd-in b p F₀ y₀ sy (rd-mg (RdFan.D b p) p (hot′ r))
    where
      hot′ : ∀ {y e} → enter (RD d) p y e → enter (RD (RdFan.D b p)) p y e
      hot′ {y} {e} r = subst (λ D′ → enter (RD D′) p y e) (Bound.is b) r

      F₀ : RdFan.First b p
      F₀ with row-each (RdFan.D b p) p (hot′ rw)
      ... | _ , _ , (Scan.sval ac , _) , _ , _ = RdFan.first b p ac
