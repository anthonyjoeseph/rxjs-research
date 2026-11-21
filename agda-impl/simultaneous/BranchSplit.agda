{-# OPTIONS --guardedness #-}

-- A BRANCH'S ROWS THE SCAN'S SOURCE MEETS ARE A RUN OF THE BRANCH.  The
-- source reads a branch of the flatMap's own (the outer, or the lanes)
-- through one reader, at a subscription fixed by its own `of`s, the value
-- read through `h` and the chain `D` below the branch's tag: so a branch
-- row it shows carries, level by level, as few rows before it as it has,
-- and any earlier branch row past that reader is shown too, at its own
-- place below.  A branch row the branch would show before the one the
-- source meets is then one the source would have met first.
module simultaneous.BranchSplit where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Nat using (ℕ; suc; s≤s; z≤n)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Effect.Monad using (RawMonad)
open import Level using () renaming (zero to lzero)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (¬¬-Monad)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
import denotation.Read as Run
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)

open import Tree using (mergeᶠ)
open import denotation.Position using (Pos; Path; ix; sub; root; _≟ᵖ_; _⊕_; inside)
open import denotation.Events using (Timeline; fresh; <ᵖ-down)
open import denotation.EmissionSet using (Ev; out; skip; pin; end; EmissionSet; Den; hot; enter; Reach; Rejoin; shown; heard; ended; late;
  Truncate; Seen; Few; LaneOf; _≺_; _≼_; at-out; on-out; MapT; map-out; map-skip; map-pin; map-end; module Op; module TakeWhile; module Merge;
  module Bounded; module Values)
open import denotation.Read using (Run; Least; After; Visible; cursor)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext; ≼-split; reach-few; ≺→≼; ≼-≺-≺; ≺-≼-≺; ≼-refl)
open import denotation.Laws.Worlds using (Lawful; ⊕-assoc; Shows; inside-⊑; ⊑-≼)
open import denotation.Laws.Worlds.Leaves using (of-in; of-rows; of-reach)
open import denotation.Laws.Shows using (Step; k-shows; shows-k; sk-trunc)
open import denotation.Laws.ShowsOps using (sk-mapT)
open import denotation.Laws.Lift using (few-lift; few-below; step-≼)
open import denotation.Laws.Count using (em)
import denotation.Laws.Join as LJ
open import denotation.Laws.Rejoined using (lower; row-few; row-reach)
open import denotation.Up using (up; up-⊕)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
import Data.List as L
open import simultaneous.SObs using (lone; module Elaborate; Branch; outerB; laneB; closeB)
open import simultaneous.FlatLanes using (Tg; brTag; tagged; BProj; keep; drop)
import simultaneous.FlatLanes as FL
open import simultaneous.DenRows using (module Cat)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Input; going)

-- The flatMap's own branches, in the order its `of` emits them.
OwnOf : List Branch
OwnOf = outerB ∷ laneB ∷ closeB ∷ []

idx : Branch → ℕ
idx outerB = 0
idx laneB  = 1
idx closeB = 2

-- A branch's row of that `of` lies at its index.
of-at : ∀ b {s q} → enter (Op.of OwnOf) s q (out b) → q ≡ s ⊕ [ ix (idx b) ]
of-at outerB (at-out , _)                     = refl
of-at outerB (on-out (on-out (on-out ())) , _)
of-at laneB  (on-out at-out , _)              = refl
of-at laneB  (on-out (on-out (on-out ())) , _)
of-at closeB (on-out (on-out at-out) , _)     = refl
of-at closeB (on-out (on-out (on-out ())) , _)

of-own : ∀ b s → enter (Op.of OwnOf) s (s ⊕ [ ix (idx b) ]) (out b)
of-own outerB s = at-out , of-reach s 0 OwnOf {s ⊕ [ ix 0 ]} {out outerB}
of-own laneB  s = on-out at-out , of-reach s 0 OwnOf {s ⊕ [ ix 1 ]} {out laneB}
of-own closeB s = on-out (on-out at-out) , of-reach s 0 OwnOf {s ⊕ [ ix 2 ]} {out closeB}

-- Where the source's reader of a branch subscribes, under its own `of`s.
module Spots (P : Pos) (i : ℕ) where
  q₁ S₂ q₂ s₃ q₃ J : Pos
  q₁ = P ⊕ [ ix 1 ]
  S₂ = q₁ ⊕ [ ix 1 ]
  q₂ = S₂ ⊕ [ ix 0 ]
  s₃ = q₂ ⊕ [ ix 1 ]
  q₃ = s₃ ⊕ [ ix i ]
  J  = q₃ ⊕ [ ix 1 ]

  private
    ext : ∀ {x} → Σ Path (λ zs → x ≡ P ⊕ zs) → ∀ l → Σ Path (λ zs → x ⊕ [ l ] ≡ P ⊕ zs)
    ext (zs , refl) l = zs ++ [ l ] , ⊕-assoc P zs [ l ]

  J-under : Σ Path λ zs → J ≡ P ⊕ zs
  J-under = ext (ext (ext (ext (ext ([ ix 1 ] , refl) (ix 1)) (ix 0)) (ix 1)) (ix i)) (ix 1)

  s₃≺J : s₃ ≺ J
  s₃≺J = ≺-trans {s₃} {q₃} {J} (≺-ext s₃ []) (≺-ext q₃ [])

  S₂≺J : S₂ ≺ J
  S₂≺J = ≺-trans {S₂} {q₂} {J} (≺-ext S₂ []) (≺-trans {q₂} {s₃} {J} (≺-ext q₂ []) s₃≺J)

-- The source as operators: the trackers, then the flatMap's own branches
-- concatenated before a closing `nothing`.
SrcOf : ∀ {B} → (Bool → Den (Maybe (Input B))) → Pos → EmissionSet (Maybe (Input B))
SrcOf F P = enter (Op.takeWhile false going (Op.flatMap (mergeᶠ nothing) F (Op.of (true ∷ false ∷ [])))) P

-- Below a row it reaches few rows before, a level has as few.
tr↓ : ∀ {V} {t : EmissionSet V} Y a {K e} → Reach t Y (out a) → t K e → K ≺ Y → Truncate t K e
tr↓ Y a {K} (ks , h) r KY = r , ks , λ {k} x lt _ → h x (≺-trans {k} {K} {Y} lt KY) tt

-- A map's event.
mev : ∀ {X Y : Set} → (X → Y) → Ev X → Ev Y
mev f (out x) = out (f x)
mev f skip    = skip
mev f (pin r) = pin r
mev f end     = end

-- The shapes a branch's row takes past the branch's reader.
data K {B : Set} (b : Branch) : Ev (Maybe (Input B)) → Set where
  kout  : ∀ x → K b (out (Tg b x))
  kskip : K b skip
  kend  : K b end

-- A joiner's row for a branch's: the same, or its end hushed.
data Same {X : Set} : Ev X → Ev X → Set where
  same : ∀ {e} → Same e e
  hush : Same end skip

same-out : ∀ {X} {e e′ : Ev X} {v} → Same e e′ → e ≡ out v → e′ ≡ out v
same-out same eq = eq
same-out hush ()

same-K : ∀ {B b} {e e′ : Ev (Maybe (Input B))} → Same e e′ → K b e → K b e′
same-K same k = k
same-K hush _ = kskip

-- The concat's, or its end handed to the next lane one step down.
data Moved {X : Set} (k : Pos) (e : Ev X) : Pos → Ev X → Set where
  kept   : ∀ {e′} → Same e e′ → Moved k e k e′
  handed : e ≡ end → Moved k e (k ⊕ [ ix 0 ]) skip

moved-step : ∀ {X k z} {e e′ : Ev X} → Moved k e z e′ → Step k z
moved-step (kept _)   = inj₁ refl
moved-step (handed _) = inj₂ refl

-- Which rows the source meets of a branch, and which it does not.
data BView {B : Set} (b : Branch) : Ev (Maybe (Input B)) → Set where
  isB  : ∀ x → BView b (out (Tg b x))
  notB : ∀ {e} → brTag b e ≡ nothing → BView b e

private
  bv : ∀ {B} b b′ (x : IE B) → BView b (out (just (inj₁ (b′ , x))))
  bv outerB outerB x = isB x
  bv laneB  laneB  x = isB x
  bv closeB closeB x = isB x
  bv outerB laneB  _ = notB refl
  bv outerB closeB _ = notB refl
  bv laneB  outerB _ = notB refl
  bv laneB  closeB _ = notB refl
  bv closeB outerB _ = notB refl
  bv closeB laneB  _ = notB refl

bview : ∀ {B} b (e : Ev (Maybe (Input B))) → BView b e
bview b (out (just (inj₁ (b′ , x)))) = bv b b′ x
bview b (out (just (inj₂ _)))        = notB refl
bview b (out nothing)                = notB refl
bview b skip                         = notB refl
bview b (pin _)                      = notB refl
bview b end                          = notB refl

------------------------------------------------------------------------
-- The branch's own reading, below its tag

module Hot {A : Set} (σ : EmissionSet (IE A)) (Lσ : Lawful σ) (J : Pos) (pastJ : ∀ {k e} → σ k e → J ≺ k) where
  open RawMonad (¬¬-Monad {lzero}) using (_>>=_; pure)

  under-J : ∀ {k} → J ≺ k → J ≺ (k ⊕ [ sub J ])
  under-J {k} jk = ≺-trans {J} {k} {k ⊕ [ sub J ]} jk (≺-ext k [])

  -- Two branch rows one label down keep their order.
  mono : ∀ {k e y e′} → σ k e → σ y e′ → k ≺ y → (k ⊕ [ sub J ]) ≺ (y ⊕ [ sub J ])
  mono {k} {e} {y} {e′} rk ry ky =
    Equivalence.from T-≡ (<ᵖ-down k y (sub J) (sub J) (Equivalence.to T-≡ ky) (λ l ls eq → Lawful.flat Lσ rk (subst (λ z → σ z e′) eq ry)))

  -- A BRANCH ROW A LEVEL SHOWS: the branch's row it shows, as few rows
  -- before it, and every earlier branch row past the reader shown too.
  Split : ∀ {V} → EmissionSet V → (IE A → V) → Pos → IE A → Set
  Split U g Y x = Σ Pos λ y → Y ≡ y ⊕ [ sub J ] × σ y (out x) × J ≺ y × Reach (Rejoin J σ) Y (out x)
                × (∀ {k x′} → σ k (out x′) → J ≺ k → (k ⊕ [ sub J ]) ≺ Y → U (k ⊕ [ sub J ]) (out (g x′)))

  -- A value a level shows, with the branch's value it reads.
  Level : ∀ {V} → EmissionSet V → (IE A → V) → Pos → V → Set
  Level U g Y v = Σ (IE A) λ x → g x ≡ v × Split U g Y x

  l-tr : ∀ {V} {d d′ : Den V} {s g Y v} → d ≡ d′ → Level (enter d s) g Y v → Level (enter d′ s) g Y v
  l-tr refl l = l

  s-hot : ∀ {Y v} → enter (hot σ) J Y (out v) → Level (enter (hot σ) J) (λ x → x) Y v
  s-hot {v = v} (shown {q = y} r _ jy , rch) = v , refl , y , refl , r , jy , rch , λ r′ jk KY → tr↓ (y ⊕ [ sub J ]) v rch (shown r′ tt jk) KY

  s-map : ∀ {X W : Set} (f : X → W) {d : Den X} {g : IE A → X}
        → (∀ {Y v} → enter d J Y (out v) → Level (enter d J) g Y v)
        → ∀ {Y v} → enter (Op.map f d) J Y (out v) → Level (enter (Op.map f d) J) (λ x → f (g x)) Y v
  s-map f {g = g} low {Y} (map-out r , rch) with low r
  ... | x , refl , y , eq , ry , jy , rr , dn = x , refl , y , eq , ry , jy , rr , λ r′ jk KY → tr↓ Y (f (g x)) rch (map-out (dn r′ jk KY)) KY

  rj-past : ∀ {k e} → Rejoin J σ k e → J ≺ k
  rj-past (shown _ _ jq) = under-J jq
  rj-past (heard _ jq)   = under-J jq
  rj-past (ended _ jc)   = under-J jc
  rj-past (late _ _)     = ≺-ext J []

  map-past : ∀ {X W : Set} (f : X → W) {d : Den X} → (∀ {k e} → enter d J k e → J ≺ k) → ∀ {k e} → enter (Op.map f d) J k e → J ≺ k
  map-past f p (map-out r , _)  = p r
  map-past f p (map-skip r , _) = p r
  map-past f p (map-pin r , _)  = p r
  map-past f p (map-end r , _)  = p r

  hot-past : ∀ {k e} → enter (hot σ) J k e → J ≺ k
  hot-past (r , _) = rj-past r

  -- The shapes a branch row takes at its reader.
  data K0 : Ev (IE A) → Set where
    k0out  : ∀ x → K0 (out x)
    k0skip : K0 skip
    k0end  : K0 end

  -- A branch row at the branch's reader.
  rj : ∀ {y e} → σ y e → Σ (Ev (IE A)) λ e₀ → Rejoin J σ (y ⊕ [ sub J ]) e₀ × K0 e₀ × (∀ {x} → e ≡ out x → e₀ ≡ out x)
  rj {e = out x} r = out x , shown r tt (pastJ r) , k0out x , λ { refl → refl }
  rj {e = skip}  r = skip , shown r tt (pastJ r) , k0skip , λ ()
  rj {e = pin _} r = skip , heard r (pastJ r) , k0skip , λ ()
  rj {e = end}   r = end , ended r (pastJ r) , k0end , λ ()

  -- A map level below which a reading shows: as few rows before a
  -- position, and each row no later than it shown above.
  map-shows : ∀ {X W : Set} (f : X → W) (d : Den X) → Shows (enter d J) → Shows (enter (Op.map f d) J)
  map-shows f d sh = k-shows λ n → sk-trunc (sk-mapT f (shows-k {n = n} sh))

  map-lift : ∀ {X W : Set} (f : X → W) (d : Den X) → Shows (enter d J) → ∀ {q} → Few (enter (Op.map f d) J) q
           → Few (enter d J) q × (∀ {Z e} → enter d J Z e → Z ≼ q → ¬ ¬ enter (Op.map f d) J Z (mev f e))
  map-lift f d sh {q} fq = few-below shU fq st , λ t Zq → few-lift shU fq (raw t) Zq
    where
      shU : Shows (MapT f (enter d J))
      shU = k-shows λ n → sk-mapT f (shows-k {n = n} sh)
      raw : ∀ {Z e} → enter d J Z e → MapT f (enter d J) Z (mev f e)
      raw {e = out _} t = map-out t
      raw {e = skip}  t = map-skip t
      raw {e = pin _} t = map-pin t
      raw {e = end}   t = map-end t
      st : ∀ {k e} → enter d J k e → k ≺ q → ¬ ¬ Σ Pos λ z → Σ (Ev _) (MapT f (enter d J) z) × Step k z
      st {k} t _ = pure (k , (_ , raw t) , inj₁ refl)

  -- The branch's row, as its reader shows it: the branch's rows before it
  -- are few, each shown at or before it.
  t0-of : Shows σ → ∀ {q} → Few (enter (hot σ) J) q → ∀ {y e e₀} → σ y e → Rejoin J σ (y ⊕ [ sub J ]) e₀ → (y ⊕ [ sub J ]) ≼ q
        → ¬ ¬ enter (hot σ) J (y ⊕ [ sub J ]) e₀
  t0-of shσ {q} f0 {y} ry r0 Yq = shσ {v = y} (L.map up (proj₁ f0) , pick) >>= λ fy → pure (r0 , row-reach Lσ ry fy (pastJ ry))
    where
      pick : ∀ {k e} → σ k e → Few σ k → k ≺ y → k ∈ L.map up (proj₁ f0)
      pick {k} rk fk ky with rj rk
      ... | _ , rk′ , _ = subst (_∈ L.map up (proj₁ f0)) (up-⊕ k (sub J))
        (∈-map⁺ up (proj₂ f0 (rk′ , row-reach Lσ rk fk (pastJ rk)) (≺-≼-≺ {k ⊕ [ sub J ]} {y ⊕ [ sub J ]} {q} (mono rk ry ky) Yq)))

------------------------------------------------------------------------
-- The branch, through the flatMap's own, the concat, the trackers' merge
-- and the source's takeWhile

module BranchSplit {A B : Set} (σ : EmissionSet (IE A)) (Lσ : Lawful σ) (P : Pos) (b : Branch) (h : IE A → IE B)
                   (F C : Bool → Den (Maybe (Input B))) (G : Branch → Den (Maybe (Input B))) (D : Den (Maybe (Input B)))
                   (eqF : F false ≡ Op.flatMap (mergeᶠ (just 1)) C (Op.of (true ∷ false ∷ [])))
                   (eqC : C true ≡ Op.flatMap (mergeᶠ nothing) G (Op.of OwnOf))
                   (eqG : G b ≡ D)
                   (noF : ∀ {s k x} → enter (F true) s k (out (Tg b x)) → ⊥)
                   (noC : ∀ {s k x} → enter (C false) s k (out (Tg b x)) → ⊥)
                   (noG : ∀ {b′ s k x} → enter (G b′) s k (out (Tg b x)) → b′ ≡ b)
                   (funcM : ∀ {y e e′} → SrcOf F P y e → SrcOf F P y e′ → e ≡ e′)
                   (past : ∀ zs {k e} → σ k e → (P ⊕ zs) ≺ k) where
  open Spots P (idx b) public

  pastJ : ∀ {k e} → σ k e → J ≺ k
  pastJ {k} r = subst (_≺ k) (sym (proj₂ J-under)) (past (proj₁ J-under) r)

  open Hot σ Lσ J pastJ public

  M′ : EmissionSet (Maybe (Input B))
  M′ = SrcOf F P

  -- What the source tags a branch value as.
  g : IE A → Maybe (Input B)
  g x = Tg b (h x)

  T1 : EmissionSet (Maybe (Input B))
  T1 = enter D J

  module Up (sD : ∀ {Y v} → T1 Y (out v) → Level T1 g Y v) where

    s-tag : ∀ {Y v} → enter (G b) J Y (out v) → Level (enter (G b) J) g Y v
    s-tag {Y} {v} r = l-tr (sym eqG) (sD (subst (λ d → enter d J Y (out v)) eqG r))

    -- The flatMap's own branches.
    private module M4 = Merge G (enter (Op.of OwnOf) s₃)

    Own′ : EmissionSet (Maybe (Input B))
    Own′ = enter (Op.flatMap (mergeᶠ nothing) G (Op.of OwnOf)) s₃

    own-b : ∀ b′ {q Y x′} → b′ ≡ b → enter (Op.of OwnOf) s₃ q (out b′)
          → enter (G b′) (q ⊕ [ ix 1 ]) Y (out (Tg b x′)) → Reach M4.JoinT Y (out (Tg b x′)) → Level Own′ g Y (Tg b x′)
    own-b _ {Y = Y} {x′} refl o r rch with of-at b o
    ... | refl with s-tag r
    ...   | x , ex , y , eq , ry , jy , rr , dn =
      x , ex , y , eq , ry , jy , rr , λ r′ jk KY → tr↓ Y (Tg b x′) rch (M4.lane o tt (dn r′ jk KY , under-J jk) (λ ()) tt) KY

    s-own : ∀ {Y x′} → Own′ Y (out (Tg b x′)) → Level Own′ g Y (Tg b x′)
    s-own (M4.lane {a = b′} o _ (r , _) _ _ , rch) = own-b b′ (noG r) o r rch
    s-own (M4.run () _ , _)

    -- The concat: the branches first.
    private module B3 = Bounded 1 C (enter (Op.of (true ∷ false ∷ [])) S₂)

    Cat′ : EmissionSet (Maybe (Input B))
    Cat′ = enter (Op.flatMap (mergeᶠ (just 1)) C (Op.of (true ∷ false ∷ []))) S₂

    cat-first : ∀ {q i s Y x′} → enter (Op.of (true ∷ false ∷ [])) S₂ q (out true) → B3.Indexed q → B3.Sub i q s true
              → enter (C true) s Y (out (Tg b x′)) → Reach B3.JoinT Y (out (Tg b x′)) → Level Cat′ g Y (Tg b x′)
    cat-first {Y = Y} {x′} o ixd sb r rch with Cat.first-sub C S₂ o sb
    ... | refl with l-tr (sym eqC) (s-own (subst (λ d → enter d s₃ Y (out (Tg b x′))) eqC r))
    ...   | x , ex , y , eq , ry , jy , rr , dn =
      x , ex , y , eq , ry , jy , rr , λ {k} r′ jk KY →
        tr↓ Y (Tg b x′) rch (B3.lane o ixd (_ , s₃ , sb , dn r′ jk KY , ≺-trans {s₃} {J} {k ⊕ [ sub J ]} s₃≺J (under-J jk)) (λ ()) tt) KY

    s-cat : ∀ {Y x′} → Cat′ Y (out (Tg b x′)) → Level Cat′ g Y (Tg b x′)
    s-cat (B3.lane {a = true} o ixd (_ , _ , sb , r , _) _ _ , rch) = cat-first o ixd sb r rch
    s-cat (B3.lane {a = false} _ _ (_ , _ , _ , r , _) _ _ , _)  = ⊥-elim (noC r)
    s-cat (B3.run () _ , _)

    -- The trackers and the flatMap's own: the second.
    private module M2 = Merge F (enter (Op.of (true ∷ false ∷ [])) P)

    Fed′ : EmissionSet (Maybe (Input B))
    Fed′ = enter (Op.flatMap (mergeᶠ nothing) F (Op.of (true ∷ false ∷ []))) P

    fed-own : ∀ {Y x′} → enter (F false) S₂ Y (out (Tg b x′)) → Level (enter (F false) S₂) g Y (Tg b x′)
    fed-own {Y} {x′} r = l-tr (sym eqF) (s-cat (subst (λ d → enter d S₂ Y (out (Tg b x′))) eqF r))

    s-fed : ∀ {Y x′} → Fed′ Y (out (Tg b x′)) → Level Fed′ g Y (Tg b x′)
    s-fed (M2.lane {a = true} _ _ (r , _) _ _ , _) = ⊥-elim (noF r)
    s-fed {Y} {x′} (M2.lane {a = false} o@(on-out at-out , _) _ (r , _) _ _ , rch) with fed-own r
    ... | x , ex , y , eq , ry , jy , rr , dn =
      x , ex , y , eq , ry , jy , rr , λ {k} r′ jk KY →
        tr↓ Y (Tg b x′) rch (M2.lane o tt (dn r′ jk KY , ≺-trans {S₂} {J} {k ⊕ [ sub J ]} S₂≺J (under-J jk)) (λ ()) tt) KY
    s-fed (M2.lane {a = false} (on-out (on-out ()) , _) _ _ _ _ , _)
    s-fed (M2.run () _ , _)

    private module TW = TakeWhile false going (enter (Op.flatMap (mergeᶠ nothing) F (Op.of (true ∷ false ∷ []))) P)

    split : ∀ {Y x′} → M′ Y (out (Tg b x′)) → Level M′ g Y (Tg b x′)
    split {Y} {x′} (TW.pass r _ nf , rch) with s-fed r
    ... | x , ex , y , eq , ry , jy , rr , dn =
      x , ex , y , eq , ry , jy , rr , λ {k} r′ jk KY →
        tr↓ Y (Tg b x′) rch (TW.pass (dn r′ jk KY) tt (λ { (q , a , rq , na , qK) → nf (q , a , rq , na , ≺-trans {q} {k ⊕ [ sub J ]} qK KY) })) KY
    split (TW.fail _ _ _ () , _)

    ------------------------------------------------------------------------
    -- The run

    -- WHAT THE TWO READERS HAVE MET: every branch row past the branch's
    -- cursor that the source shows lies past the source's cursor, and the
    -- source's cursor lies past the last branch row met.
    record Inv (cM cσ : Maybe Pos) : Set where
      field
        i1 : ∀ {k x} → σ k (out x) → After cσ k → M′ (k ⊕ [ sub J ]) (out (g x)) → After cM (k ⊕ [ sub J ])
        i2 : ∀ {y} → cσ ≡ just y → Σ (Ev (IE A)) (σ y) × (∀ {Z} → After cM Z → (y ⊕ [ sub J ]) ≺ Z)

    -- The branch row met next lies past the last one met.
    after-last : ∀ {cM y e} cσ → Inv cM cσ → σ y e → After cM (y ⊕ [ sub J ]) → After cσ y
    after-last nothing  _  _  _  = tt
    after-last (just y′) iv ry am with Inv.i2 iv refl
    ... | (_ , ry′) , f = lower Lσ ry ry′ (f am)

    -- Past a branch row met, both cursors there.
    iv-b : ∀ {y e} → σ y e → Inv (just (y ⊕ [ sub J ])) (just y)
    Inv.i1 (iv-b ry) rk yk _ = mono ry rk yk
    Inv.i2 (iv-b ry) refl    = (_ , ry) , λ z → z

    -- Past another row met, only the source's cursor moves: no branch row
    -- it shows lies there, since one event lies at a row.
    iv-other : ∀ {cM cσ q e} → Inv cM cσ → M′ q e → Least M′ cM q → brTag b e ≡ nothing → Inv (just q) cσ
    Inv.i1 (iv-other {q = q} {e} iv mq lst nl) {k} {x} rk ak mK
      with ≼-split {q} {k ⊕ [ sub J ]} (proj₂ lst mK tt (Inv.i1 iv rk ak mK))
    ... | inj₁ lt = lt
    ... | inj₂ eq = ⊥-elim (tagged b (subst (λ z → brTag b z ≡ nothing) (funcM (subst (λ z → M′ z e) eq mq) mK) nl))
    Inv.i2 (iv-other {q = q} iv mq lst nl) {y} eq with Inv.i2 iv eq
    ... | r , f = r , λ {Z} qZ → ≺-trans {y ⊕ [ sub J ]} {q} {Z} (f (proj₁ lst)) qZ

    tg-inj : ∀ {u v : IE B} → Tg b u ≡ Tg b v → u ≡ v
    tg-inj refl = refl

    -- THE BRANCH'S NEXT ROW, where the source's next row is the branch's:
    -- the branch's row it shows, reached, and the first past its cursor.
    next : ∀ {cM cσ q x′} → Inv cM cσ → M′ q (out (Tg b x′)) → Least M′ cM q
         → Σ Pos λ y → Σ (IE A) λ x → h x ≡ x′ × q ≡ y ⊕ [ sub J ] × Seen σ y (out x) × Least σ cσ y
    next {cσ = cσ} iv mq lst with split mq
    ... | x , ex , y , refl , ry , jy , rr , dn = y , x , tg-inj ex , refl , seen , after-last cσ iv ry (proj₁ lst) , least
      where
        seen : Seen σ y (out x)
        seen = (ry , λ c → Lawful.proper Lσ c ry) , row-few Lσ pastJ ry (reach-few {q = y ⊕ [ sub J ]} {e = out x} (λ {k} {e′} → tt) rr)

        least : ∀ {k e′} → σ k e′ → Visible e′ → After cσ k → y ≼ k
        least {k} {out x₀} rk _ ak ky = proj₂ lst mK tt (Inv.i1 iv rk ak mK) KY
          where
            KY = mono rk ry ky
            mK = dn rk (pastJ rk) KY
        least {e′ = end}   rk _ _ = Lawful.proper Lσ rk ry
        least {e′ = skip}  _ ()
        least {e′ = pin _} _ ()

    Runs : Maybe Pos → Maybe Pos → List (Pos × Ev (Maybe (Input B))) → Set
    Runs cM cσ rx = Σ _ λ rs → BProj b h J rx rs × Run σ cσ rs × Inv (cursor cM rx) (cursor cσ rs)

    mutual
      go : ∀ {cM rx} cσ → Run M′ cM rx → Inv cM cσ → Runs cM cσ rx
      go cσ Run.[] iv = [] , FL.[] , Run.[] , iv
      go cσ (Run._∷_ {e = e} row rest) iv = step cσ (bview b e) row rest iv

      step : ∀ {cM q e rx} cσ → BView b e → Seen M′ q e × Visible e × Least M′ cM q → Run M′ (just q) rx → Inv cM cσ
           → Runs cM cσ ((q , e) ∷ rx)
      step cσ (isB x)   (sn , _ , lst) rest iv = b-step cσ (proj₁ (proj₁ sn)) lst rest iv
      step cσ (notB nl) (sn , _ , lst) rest iv with go cσ rest (iv-other iv (proj₁ (proj₁ sn)) lst nl)
      ... | rs , pr , run , iv′ = rs , drop nl pr , run , iv′

      b-step : ∀ {cM q x′ rx} cσ → M′ q (out (Tg b x′)) → Least M′ cM q → Run M′ (just q) rx → Inv cM cσ
             → Runs cM cσ ((q , out (Tg b x′)) ∷ rx)
      b-step cσ mq lst rest iv with next iv mq lst
      ... | y , x , refl , refl , seen , least with go (just y) rest (iv-b (proj₁ (proj₁ seen)))
      ...   | rs , pr , run , iv′ = (y , out x) ∷ rs , keep pr , (seen , tt , least) Run.∷ run , iv′

    -- THE BRANCH'S ROWS A RUN OF THE SOURCE MEETS ARE A RUN OF THE BRANCH.
    run′ : ∀ {rx} → Run M′ nothing rx → Runs nothing nothing rx
    run′ r = go nothing r (record { i1 = λ _ _ _ → tt ; i2 = λ () })

    ------------------------------------------------------------------------
    -- Shown

    -- An of's rows lie past its subscription.
    of-past : ∀ {X : Set} s (xs : List X) {k e} → enter (Op.of xs) s k e → s ≺ k
    of-past {X} s xs (r , _) = rows 0 xs (of-in s 0 xs r)
      where
        rows : ∀ i (ys : List X) {k} → k ∈ of-rows s i ys → s ≺ k
        rows i []       (here refl) = ≺-ext s []
        rows i (_ ∷ _)  (here refl) = ≺-ext s []
        rows i (_ ∷ ys) (there m)   = rows (suc i) ys m

    -- The flatMap's own branches' rows lie past their outer's subscription.
    own-past : ∀ {k e} → Own′ k e → s₃ ≺ k
    own-past (M4.val {q} o , _)                    = ≺-trans {s₃} {q} {q ⊕ [ ix 0 ]} (of-past s₃ _ o) (≺-ext q [])
    own-past (M4.step o , _)                       = of-past s₃ _ o
    own-past (M4.opin o , _)                       = of-past s₃ _ o
    own-past (M4.oend o _ , _)                     = of-past s₃ _ o
    own-past (M4.opass o _ , _)                    = of-past s₃ _ o
    own-past (M4.lane {q} {k = k} o _ (_ , lt) _ _ , _) = ≺-trans {s₃} {q} {k} (of-past s₃ _ o) (≺-trans {q} {q ⊕ [ ix 1 ]} {k} (≺-ext q []) lt)
    own-past (M4.lend {q} {c = c} o _ (_ , lt) _ _ _ , _) = ≺-trans {s₃} {q} {c} (of-past s₃ _ o) (≺-trans {q} {q ⊕ [ ix 1 ]} {c} (≺-ext q []) lt)
    own-past (M4.lpass {q} {c = c} o _ (_ , lt) _ _ _ , _) = ≺-trans {s₃} {q} {c} (of-past s₃ _ o) (≺-trans {q} {q ⊕ [ ix 1 ]} {c} (≺-ext q []) lt)
    own-past (M4.hand {q} {c = c} o _ (_ , lt) _ () , _)
    own-past (M4.left {q} {k = k} o _ (_ , lt) _ _ , _) = ≺-trans {s₃} {q} {k} (of-past s₃ _ o) (≺-trans {q} {q ⊕ [ ix 1 ]} {k} (≺-ext q []) lt)
    own-past (M4.run () _ , _)
    own-past (M4.rend () _ _ , _)
    own-past (M4.rpass () _ _ , _)
    own-past (M4.rhand () _ , _)

    -- The concat's rows lie past its outer's subscription.
    cat-past : ∀ {k e} → Cat′ k e → S₂ ≺ k
    cat-past (B3.val {q} o , _)  = ≺-trans {S₂} {q} {q ⊕ [ ix 0 ]} (of-past S₂ _ o) (≺-ext q [])
    cat-past (B3.step o , _)     = of-past S₂ _ o
    cat-past (B3.opin o , _)     = of-past S₂ _ o
    cat-past (B3.oend o _ , _)   = of-past S₂ _ o
    cat-past (B3.opass o _ , _)  = of-past S₂ _ o
    cat-past (B3.lane {q} {k = k} o _ (_ , s , (_ , st) , (_ , sk)) _ _ , _) =
      ≺-trans {S₂} {q} {k} (of-past S₂ _ o) (≺-trans {q} {s} {k} (LJ.Join.BoundedJ.starts-past P 1 st) sk)
    cat-past (B3.lend {q} {c = c} o _ (_ , s , (_ , st) , (_ , sc)) _ _ _ , _) =
      ≺-trans {S₂} {q} {c} (of-past S₂ _ o) (≺-trans {q} {s} {c} (LJ.Join.BoundedJ.starts-past P 1 st) sc)
    cat-past (B3.lpass {q} {c = c} o _ (_ , s , (_ , st) , (_ , sc)) _ _ _ , _) =
      ≺-trans {S₂} {q} {c} (of-past S₂ _ o) (≺-trans {q} {s} {c} (LJ.Join.BoundedJ.starts-past P 1 st) sc)
    cat-past (B3.hand {q} {c = c} o _ (_ , s , (_ , st) , (_ , sc)) _ _ , _) =
      ≺-trans {S₂} {q} {c ⊕ [ ix 0 ]} (of-past S₂ _ o) (≺-trans {q} {s} {c ⊕ [ ix 0 ]} (LJ.Join.BoundedJ.starts-past P 1 st) (≺-trans {s} {c} {c ⊕ [ ix 0 ]} sc (≺-ext c [])))
    cat-past (B3.left {q} {k = k} o _ (_ , s , (_ , st) , (_ , sk)) _ _ , _) =
      ≺-trans {S₂} {q} {k} (of-past S₂ _ o) (≺-trans {q} {s} {k} (LJ.Join.BoundedJ.starts-past P 1 st) sk)
    cat-past (B3.run () _ , _)
    cat-past (B3.rend () _ _ , _)
    cat-past (B3.rpass () _ _ , _)
    cat-past (B3.rhand () _ , _)

    o₃ : enter (Op.of OwnOf) s₃ q₃ (out b)
    o₃ = of-own b s₃

    o₂ : enter (Op.of (true ∷ false ∷ [])) S₂ q₂ (out true)
    o₂ = at-out , of-reach S₂ 0 (true ∷ false ∷ []) {q₂} {out true}

    o₁ : enter (Op.of (true ∷ false ∷ [])) P q₁ (out false)
    o₁ = on-out at-out , of-reach P 0 (true ∷ false ∷ []) {q₁} {out false}

    ixd : B3.Indexed q₂
    ixd = 0 , true , Values.first o₂ (λ {k} {b} x → Cat.min0 C S₂ {k} {b} x)

    sb₀ : B3.Sub 0 q₂ s₃ true
    sb₀ = proj₂ (proj₂ ixd) , B3.room (s≤s z≤n)

    module Rows (dpast : ∀ {k e} → T1 k e → J ≺ k) where

      m4-lane : ∀ {k e} → T1 k e → LaneOf G q₃ b k e
      m4-lane {k} {e} t = subst (λ d → enter d J k e) (sym eqG) t , dpast t

      b3-lane : ∀ {k e} → Own′ k e → B3.Lane q₂ true k e
      b3-lane {k} {e} r = 0 , s₃ , sb₀ , subst (λ d → enter d s₃ k e) (sym eqC) r , own-past r

      m2-lane : ∀ {k e} → Cat′ k e → LaneOf F q₁ false k e
      m2-lane {k} {e} r = subst (λ d → enter d S₂ k e) (sym eqF) r , cat-past r

      m4-row : ∀ {k e} → T1 k e → ¬ ¬ Σ _ λ e′ → M4.JoinT k e′ × Same e e′
      m4-row {e = out _} t ¬j = ¬j (_ , M4.lane o₃ tt (m4-lane t) (λ ()) tt , same)
      m4-row {e = skip}  t ¬j = ¬j (_ , M4.lane o₃ tt (m4-lane t) (λ ()) tt , same)
      m4-row {e = pin _} t ¬j = ¬j (_ , M4.lane o₃ tt (m4-lane t) (λ ()) tt , same)
      m4-row {k} {end}   t    =
        em {P = M4.Done k} (λ d ¬j → ¬j (_ , M4.lend o₃ tt (m4-lane t) (λ ()) (λ ()) d , same))
                           (λ nd ¬j → ¬j (_ , M4.lpass o₃ tt (m4-lane t) (λ ()) (λ ()) nd , hush))

      b3-row : ∀ {k e} → Own′ k e → ¬ ¬ Σ Pos λ z → Σ _ λ e′ → B3.JoinT z e′ × Moved k e z e′
      b3-row {e = out _} r ¬j = ¬j (_ , _ , B3.lane o₂ ixd (b3-lane r) (λ ()) tt , kept same)
      b3-row {e = skip}  r ¬j = ¬j (_ , _ , B3.lane o₂ ixd (b3-lane r) (λ ()) tt , kept same)
      b3-row {e = pin _} r ¬j = ¬j (_ , _ , B3.lane o₂ ixd (b3-lane r) (λ ()) tt , kept same)
      b3-row {k} {end}   r    =
        em {P = B3.Queued k} (λ h′ ¬j → ¬j (_ , _ , B3.hand o₂ ixd (b3-lane r) (λ ()) h′ , handed refl)) λ nh →
        em {P = B3.Done k} (λ d ¬j → ¬j (_ , _ , B3.lend o₂ ixd (b3-lane r) (λ ()) nh d , kept same))
                           (λ nd ¬j → ¬j (_ , _ , B3.lpass o₂ ixd (b3-lane r) (λ ()) nh nd , kept hush))

      m2-row : ∀ {k e} → Cat′ k e → ¬ ¬ Σ _ λ e′ → M2.JoinT k e′ × Same e e′
      m2-row {e = out _} r ¬j = ¬j (_ , M2.lane o₁ tt (m2-lane r) (λ ()) tt , same)
      m2-row {e = skip}  r ¬j = ¬j (_ , M2.lane o₁ tt (m2-lane r) (λ ()) tt , same)
      m2-row {e = pin _} r ¬j = ¬j (_ , M2.lane o₁ tt (m2-lane r) (λ ()) tt , same)
      m2-row {k} {end}   r    =
        em {P = M2.Done k} (λ d ¬j → ¬j (_ , M2.lend o₁ tt (m2-lane r) (λ ()) (λ ()) d , same))
                           (λ nd ¬j → ¬j (_ , M2.lpass o₁ tt (m2-lane r) (λ ()) (λ ()) nd , hush))

      -- THE BRANCH'S ROWS BEFORE A SOURCE VALUE ARE SHOWN.  Each level the
      -- source's reader passes through shows its hangs, and the source has
      -- few rows before its value: so each level has few there, top down,
      -- and a branch row lifts bottom up, the concat handing a lane's end
      -- on one step down.  A hand-off that would pass the value is the
      -- value itself.  Below the tag, the chain shows its own.
      module Shown (shM4 : Shows M4.JoinT) (shB3 : Shows B3.JoinT) (shM2 : Shows M2.JoinT)
                   (shTW : Shows TW.TakeT) (pinF : ∀ {k r} → Fed′ k (pin r) → T (inside r k)) {q a} (mq : M′ q (out a))
                   (dshow : Few T1 q → ∀ {y e} → σ y e → (y ⊕ [ sub J ]) ≼ q
                          → ¬ ¬ Σ _ λ e₁ → T1 (y ⊕ [ sub J ]) e₁ × K b e₁ × (∀ {x} → e ≡ out x → e₁ ≡ out (g x))) where
        open RawMonad (¬¬-Monad {lzero}) using (_>>=_; pure)

        nfq : ¬ TW.Failed q
        nfq = nf-of mq
          where
            nf-of : ∀ {q a} → M′ q (out a) → ¬ TW.Failed q
            nf-of (TW.pass _ _ nf , _)   = nf
            nf-of (TW.fail _ _ _ () , _)

        nf-mono : ∀ {r k} → r ≼ k → ¬ TW.Failed k → ¬ TW.Failed r
        nf-mono {r} {k} rk nk (w , b′ , x , nb , wr) = nk (w , b′ , x , nb , ≺-≼-≺ {w} {r} {k} wr rk)

        f5 : Few M′ q
        f5 = proj₁ (proj₂ mq) , λ x lt → proj₂ (proj₂ mq) (proj₁ x) lt tt

        st5 : ∀ {k e} → Fed′ k e → k ≺ q → ¬ ¬ Σ Pos λ z → Σ _ (TW.TakeT z) × Step k z
        st5 {k} {out b′} r kq with going b′ in gg
        ... | true  = pure (k , (_ , TW.pass r (Equivalence.from T-≡ gg) (nf-mono (≺→≼ {k} {q} kq) nfq)) , inj₁ refl)
        ... | false = ⊥-elim (nfq (k , b′ , r , subst (λ x → T (not x)) (sym gg) tt , kq))
        st5 {k} {skip}  r kq = pure (k , (_ , TW.step r (nf-mono (≺→≼ {k} {q} kq) nfq)) , inj₁ refl)
        st5 {k} {end}   r kq = pure (k , (_ , TW.tend r (nf-mono (≺→≼ {k} {q} kq) nfq)) , inj₁ refl)
        st5 {k} {pin s} r kq =
          pure (k , (_ , TW.left r (nf-mono {s} {q} (≺→≼ {s} {q} (≼-≺-≺ {s} {k} {q} (⊑-≼ {s} {k} (inside-⊑ s k (pinF r))) kq)) nfq) (pinF r)) , inj₁ refl)

        f4 : Few Fed′ q
        f4 = few-below shTW f5 st5

        st4 : ∀ {k e} → Cat′ k e → k ≺ q → ¬ ¬ Σ Pos λ z → Σ _ (M2.JoinT z) × Step k z
        st4 {k} r _ = m2-row r >>= λ (e′ , u , _) → pure (k , (e′ , u) , inj₁ refl)

        f3 : Few Cat′ q
        f3 = few-below shM2 f4 st4

        st3 : ∀ {k e} → Own′ k e → k ≺ q → ¬ ¬ Σ Pos λ z → Σ _ (B3.JoinT z) × Step k z
        st3 r _ = b3-row r >>= λ (z , e′ , u , mv) → pure (z , (e′ , u) , moved-step mv)

        f2 : Few Own′ q
        f2 = few-below shB3 f3 st3

        st2 : ∀ {k e} → T1 k e → k ≺ q → ¬ ¬ Σ Pos λ z → Σ _ (M4.JoinT z) × Step k z
        st2 {k} t _ = m4-row t >>= λ (e′ , u , _) → pure (k , (e′ , u) , inj₁ refl)

        f1 : Few T1 q
        f1 = few-below shM4 f2 st2

        tw-lift : ∀ {z e} → K b e → Fed′ z e → z ≼ q → TW.TakeT z e
        tw-lift (kout x) r zq = TW.pass r tt (nf-mono zq nfq)
        tw-lift kskip    r zq = TW.step r (nf-mono zq nfq)
        tw-lift kend     r zq = TW.tend r (nf-mono zq nfq)

        -- Past the concat: the source's row there.
        past-cat : ∀ {z e} → K b e → Cat′ z e → z ≼ q → ¬ ¬ Σ _ λ e′ → M′ z e′ × Same e e′
        past-cat k t3 zq =
          m2-row t3 >>= λ (e′ , u4 , s) →
          few-lift shM2 f4 u4 zq >>= λ t4 →
          few-lift shTW f5 (tw-lift (same-K s k) t4 zq) zq >>= λ t5 →
          pure (e′ , t5 , s)

        Lifted : Pos → Ev (Maybe (Input B)) → Set
        Lifted Y e = Σ Pos λ z → Σ _ λ e″ → M′ z e″ × Step Y z × z ≼ q × (∀ {v} → e ≡ out v → z ≡ Y × e″ ≡ out v)

        handed-on : ∀ {Y e z e′} → K b e → Moved Y e z e′ → B3.JoinT z e′ → Y ≼ q → ¬ ¬ Lifted Y e
        handed-on k (kept s) u3 Yq =
          few-lift shB3 f3 u3 Yq >>= λ t3 →
          past-cat (same-K s k) t3 Yq >>= λ (e″ , t5 , s′) →
          pure (_ , e″ , t5 , inj₁ refl , Yq , λ {_} eq → refl , same-out s′ (same-out s eq))
        handed-on {Y} k (handed refl) u3 Yq with ≼-split {Y} {q} Yq
        ... | inj₁ lt =
          few-lift shB3 f3 u3 zq >>= λ t3 →
          past-cat kskip t3 zq >>= λ (e″ , t5 , _) →
          pure (_ , e″ , t5 , inj₂ refl , zq , λ {_} ())
          where
            zq : (Y ⊕ [ ix 0 ]) ≼ q
            zq = step-≼ {Y} {Y ⊕ [ ix 0 ]} {q} (inj₂ refl) lt
        ... | inj₂ eq = pure (q , out a , mq , inj₁ (sym eq) , ≼-refl {q} , λ {_} ())

        lifted : ∀ {Y e} → K b e → T1 Y e → Y ≼ q → ¬ ¬ Lifted Y e
        lifted k t1 Yq =
          m4-row t1 >>= λ (e₂ , u2 , s) →
          few-lift shM4 f2 u2 Yq >>= λ t2 →
          b3-row t2 >>= λ (z , e₃ , u3 , mv) →
          handed-on (same-K s k) mv u3 Yq >>= λ (z′ , e″ , t5 , st , zq , pr) →
          pure (z′ , e″ , t5 , st , zq , λ {_} eq → pr (same-out s eq))

        -- A BRANCH ROW AT OR BEFORE THE SOURCE'S VALUE, as the source shows it.
        shown′ : ∀ {y e} → σ y e → (y ⊕ [ sub J ]) ≼ q
               → ¬ ¬ Σ Pos λ z → Σ _ λ e″ → M′ z e″ × Step (y ⊕ [ sub J ]) z × z ≼ q × (∀ {x} → e ≡ out x → z ≡ y ⊕ [ sub J ] × e″ ≡ out (g x))
        shown′ ry Yq =
          dshow f1 ry Yq >>= λ (e₁ , t1 , k1 , o1) →
          lifted k1 t1 Yq >>= λ (z , e″ , t5 , st , zq , pr) →
          pure (z , e″ , t5 , st , zq , λ {_} eq → pr (o1 eq))
