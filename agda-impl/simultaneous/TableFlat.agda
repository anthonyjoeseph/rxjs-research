{-# OPTIONS --guardedness #-}

-- THE FLATMAP'S CORE (`flat-core`): the plain flatMap's record against
-- its elaboration's innermost layer, the lanes' flatMap (`core`).  The
-- plain side is the flatMap's own table without its source's pins
-- (`Pd`); `simultaneous.TableLayers` carries the elaborated side out
-- through the combined scan, the closer and the share, where they return.
--
-- The source is related once, at the share's subscription, in the
-- environment the share's trigger extends; its hot is the shared table
-- the lanes' flatMap reads.  The lanes are related wherever they are
-- subscribed alike, each in the environment the flatMap's four binders
-- extend, which no lane reads.
--
-- A lane is subscribed past its creator, so its pair is aligned from its
-- creator's.  `flat-core` owes that alignment, one story per operator:
-- merge, switch and exhaust subscribe each lane under its value's row, so
-- the source's `cuts` and `linked` at the row align it; only the bounded
-- merge queues a lane under an earlier lane's end, a run-dependent row.
module simultaneous.TableFlat where

open import Data.Bool using (Bool; true; false; T; if_then_else_; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; InitLast; initLast; _∷ʳ_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-concatMap⁺)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.List.Relation.Unary.Any using (here; there) renaming (map to any-map)
open import Data.Maybe using (Maybe; just; nothing; maybe)
import Data.Maybe as M
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_; does; yes; no)
open import Relation.Nullary.Decidable using (dec-true)

open import Tree using (Obs; FlatOp; mergeᶠ; of; flatMap; connect; connected)
open import denotation.Position using (Pos; Label; _∙_; root; _≟ᵖ_; _<ᵖ_; ix; sub; last; inside; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; Unpinned; out; skip; end; pin; _≼_; _≺_)
open import denotation.Laws.Modulus using (AgreeTo; upto; ag-down; ≼-refl; ≼-trans; ≺→≼; ≺-ext; ≺-trans)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled.Exact.Base using (any⁻; any⁺; ends⁻; ends⁺; bind⁻; values⁺; pastRows⁺)
open import Data.Maybe.Properties using (just-injective)
open import simultaneous.TableRows using (merge-lane-out; lane-of; proper-in; rejoin-in; of-past; part-≺)
open import denotation.Laws.Worlds using (InvAt; PinBy; world-after)
open import quickcheck.Tabled using (hotOf; Row; rows; ends; anyᵇ; values; afterL; bind; lanes; past; rejoin)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Listing using (listC; listC-ok; UncutEnv)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.TableCorr using (Same; φ≡; nl→; Rel; Corr; keys; in-keys; nl-ev)
open import simultaneous.TableKit using (TR; Got; got-bind)
open import simultaneous.Readings using (instantOf)
open import simultaneous.TableEnv using (Ren; wk; got-ok; pin-ok; after-ok; Tab; up; up-⊕; _⊕ˡ_; Linked; linked-l; linked-r;
  linked-r*; linked-later; inst-⊕ˡ; squeeze; ⊑-⊕ˡ; Aligned; aligned-⊕; aligned-past;
  aligned-r*; Rest; Out; scopeOf; EnvR; maps; lw; lw*; unended; den; env-wk; Holds; Admits; admits-step;
  admits-ix; admits-body; admits-row; admits-trig; listHot; den-cons; HotD; DenOf; tab-func;
  tab-flat; tab-at)

open import simultaneous.ElabUndone using (elab-undone)
open import simultaneous.LaneEndSched using (laneXt; trigXs; laneL; laneX; readerR; emitAt; later; later-cases)
open import simultaneous.LaneEnd using (corr-end; module Lane)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; elab; each; laneˢ; closer; combined; trackers)

≟-true : ∀ x y → does (x ≟ᵖ y) ≡ true → x ≡ y
≟-true x y with x ≟ᵖ y
... | yes e = λ _ → e
... | no _  = λ ()

-- Two booleans true together are equal.
bool-≡ : ∀ {b b′ : Bool} → (b ≡ true → b′ ≡ true) → (b′ ≡ true → b ≡ true) → b ≡ b′
bool-≡ {true}  {true}  _ _ = refl
bool-≡ {false} {false} _ _ = refl
bool-≡ {true}  {false} f _ = sym (f refl)
bool-≡ {false} {true}  _ g = g refl

-- Two conditionals alike branch for branch.
if-≡ : ∀ {X : Set} {b b′ : Bool} {x y x′ y′ : X} → b ≡ b′ → (b ≡ true → x ≡ x′) → (b ≡ false → y ≡ y′)
     → (if b then x else y) ≡ (if b′ then x′ else y′)
if-≡ {b = true}  refl t _ = t refl
if-≡ {b = false} refl _ f = f refl

-- A position some row of a list equals is in it.
any-≟ : ∀ {xs k} → anyᵇ (λ k′ → does (k′ ≟ᵖ k)) xs ≡ true → k ∈ xs
any-≟ {k = k} h with any⁻ h
... | k′ , k′∈ , hk with ≟-true k′ k hk
...   | refl = k′∈

-- A row kept unless it is a pin at one of some positions.
keepRow : ∀ {X : Set} → List Pos → Row X → Bool
keepRow ks (k , pin _) = not (anyᵇ (λ k′ → does (k′ ≟ᵖ k)) ks)
keepRow ks _           = true

keep-un : ∀ {X : Set} ks {k} {e : Ev X} → Unpinned e → keepRow ks (k , e) ≡ true
keep-un ks {e = out _} _ = refl
keep-un ks {e = skip}  _ = refl
keep-un ks {e = end}   _ = refl
keep-un ks {e = pin _} ()

filt-sub : ∀ {X : Set} (g : X → Bool) (rs : List X) {x} → x ∈ L.filterᵇ g rs → x ∈ rs
filt-sub g (r ∷ rs) m with g r | m
... | true  | here eq  = here eq
... | true  | there m′ = there (filt-sub g rs m′)
... | false | m′       = there (filt-sub g rs m′)

filt-keep : ∀ {X : Set} (g : X → Bool) (rs : List X) {x} → x ∈ rs → g x ≡ true → x ∈ L.filterᵇ g rs
filt-keep g (r ∷ rs) (here refl) gx rewrite gx = here refl
filt-keep g (r ∷ rs) (there m) gx with g r
... | true  = there (filt-keep g rs m gx)
... | false = filt-keep g rs m gx

-- The pins' positions among some rows.
pinKeys : ∀ {X : Set} → List (Row X) → List Pos
pinKeys = L.concatMap λ { (k , pin _) → [ k ] ; _ → [] }

-- A table without its pins at some positions.
unpinAt : ∀ {X : Set} → List Pos → Tb.Listed X → Tb.Listed X
unpinAt ks Lx = L.filterᵇ (keepRow ks) (rows Lx) Tb.⊣ Tb.short Lx

unpin-sub : ∀ {X : Set} ks (m : Maybe (Tb.Listed X)) {k e} → TR (Tb.bind m λ Lx → just (unpinAt ks Lx)) k e → TR m k e
unpin-sub ks (just Lx) (_ , refl , r) = Lx , refl , filt-sub (keepRow ks) (rows Lx) r
unpin-sub ks nothing   (_ , () , _)

unpin-keep : ∀ {X : Set} ks (m : Maybe (Tb.Listed X)) {k e} → TR m k e → Unpinned e → TR (Tb.bind m λ Lx → just (unpinAt ks Lx)) k e
unpin-keep ks (just Lx) (_ , refl , r) u = unpinAt ks Lx , refl , filt-keep (keepRow ks) (rows Lx) r (keep-un ks u)

in-if : ∀ (b : Bool) {X : Set} (Q : X → Set) {x y} → (b ≡ true → Q x) → (b ≡ false → Q y) → Q (if b then x else y)
in-if true  Q t e = t refl
in-if false Q t e = e refl

≼-ˡ : ∀ x ys → x ≼ (x ⊕ˡ ys)
≼-ˡ x []       = ≼-refl {x}
≼-ˡ x (l ∷ ls) = ≼-trans {x} {x ⊕ [ l ]} {(x ⊕ [ l ]) ⊕ˡ ls} (≺→≼ {x} {x ⊕ [ l ]} (≺-ext x [])) (≼-ˡ (x ⊕ [ l ]) ls)

-- The latest of some positions and a floor lies past the floor.
max-ge : ∀ b xs → b ≼ L.foldr (λ x y → if x <ᵖ y then y else x) b xs
max-ge b []       = ≼-refl {b}
max-ge b (x ∷ xs) = in-if (x <ᵖ r) (λ v → b ≼ v) (λ _ → max-ge b xs)
                      (λ eq → ≼-trans {b} {r} {x} (max-ge b xs) (λ h → subst T eq h))
  where r = L.foldr (λ x y → if x <ᵖ y then y else x) b xs

-- Tables read row by row, the same in every environment.
module TabRows where
  -- A table's ends.
  endsOf : ∀ {X : Set} → Maybe (Tb.Listed X) → List Pos
  endsOf nothing   = []
  endsOf (just Lx) = ends (rows Lx)

  endAt : ∀ {X : Set} → Maybe (Tb.Listed X) → Pos → Bool
  endAt m y = anyᵇ (λ k → does (k ≟ᵖ y)) (endsOf m)

  rowAt : ∀ {X : Set} → Maybe (Tb.Listed X) → Pos → Bool
  rowAt nothing   y = false
  rowAt (just Lx) y = anyᵇ (λ r → does (proj₁ r ≟ᵖ y)) (rows Lx)

  rowAt-T : ∀ {X : Set} (m : Maybe (Tb.Listed X)) {y} → rowAt m y ≡ true → Σ (Ev X) λ e → TR m y e
  rowAt-T nothing ()
  rowAt-T (just Lx) {y} h with any⁻ {xs = rows Lx} h
  ... | (k , e) , m , hk with ≟-true k y hk
  ...   | refl = e , Lx , refl , m

  rowAt-I : ∀ {X : Set} (m : Maybe (Tb.Listed X)) {y e} → TR m y e → rowAt m y ≡ true
  rowAt-I nothing (_ , () , _)
  rowAt-I (just Lx) {y} (_ , refl , m) = any⁺ {p = λ r → does (proj₁ r ≟ᵖ y)} m (dec-true (y ≟ᵖ y) refl)

  endAt-T : ∀ {X : Set} (m : Maybe (Tb.Listed X)) {y} → endAt m y ≡ true → TR m y end
  endAt-T nothing ()
  endAt-T (just Lx) h = Lx , refl , ends⁻ {rs = rows Lx} (any-≟ h)

  endAt-I : ∀ {X : Set} (m : Maybe (Tb.Listed X)) {y} → TR m y end → endAt m y ≡ true
  endAt-I nothing (_ , () , _)
  endAt-I (just Lx) {y} (_ , refl , m) = any⁺ {p = λ k → does (k ≟ᵖ y)} (ends⁺ m) (dec-true (y ≟ᵖ y) refl)

  -- A table quiet up to `k`.
  Quiet : ∀ {X : Set} → Pos → Maybe (Tb.Listed X) → Set
  Quiet {X} k m = ∀ {y} {e : Ev X} → y ≼ k → TR m y e → ⊥

  -- Two tables agreeing up to `k` hold rows and ends alike at or below it.
  rowAt-agree : ∀ {X : Set} {m m′ : Maybe (Tb.Listed X)} {k y} → y ≼ k → AgreeTo k (TR m) (TR m′) → rowAt m y ≡ rowAt m′ y
  rowAt-agree {m = m} {m′} yk ag =
    bool-≡ (λ h → rowAt-I m′ (proj₁ (upto ag yk) (proj₂ (rowAt-T m h)))) (λ h → rowAt-I m (proj₂ (upto ag yk) (proj₂ (rowAt-T m′ h))))

  endAt-agree : ∀ {X : Set} {m m′ : Maybe (Tb.Listed X)} {k y} → y ≼ k → AgreeTo k (TR m) (TR m′) → endAt m y ≡ endAt m′ y
  endAt-agree {m = m} {m′} yk ag =
    bool-≡ (λ h → endAt-I m′ (proj₁ (upto ag yk) (endAt-T m h))) (λ h → endAt-I m (proj₂ (upto ag yk) (endAt-T m′ h)))

  rowAt-F : ∀ {X : Set} {m : Maybe (Tb.Listed X)} {k y} → y ≼ k → Quiet k m → rowAt m y ≡ false
  rowAt-F {m = m} {y = y} yk q with rowAt m y in h
  ... | true  = ⊥-elim (q yk (proj₂ (rowAt-T m h)))
  ... | false = refl

  endAt-F : ∀ {X : Set} {m : Maybe (Tb.Listed X)} {k y} → y ≼ k → Quiet k m → endAt m y ≡ false
  endAt-F {m = m} {y = y} yk q with endAt m y in h
  ... | true  = ⊥-elim (q yk (endAt-T m h))
  ... | false = refl

  -- One label up lies at or before.
  up-≼ : ∀ y → up y ≼ y
  up-≼ (i ∙ ys) with initLast ys
  ... | InitLast.[]          = ≼-refl {i ∙ []}
  ... | zs InitLast.∷ʳ′ l   =
    subst (λ u → u ≼ (i ∙ (zs ∷ʳ l))) (sym (up-⊕ (i ∙ zs) l)) (≺→≼ {i ∙ zs} {i ∙ (zs ∷ʳ l)} (≺-ext (i ∙ zs) {l} []))

  ups : ℕ → Pos → Pos
  ups zero    y = y
  ups (suc i) y = ups i (up y)

  -- An end among some rows.
  endIn : ∀ {X : Set} (rs : List (Row X)) c → Maybe ((c , end) ∈ rs)
  endIn []               c = nothing
  endIn ((k , end) ∷ rs) c with k ≟ᵖ c
  ... | yes refl = just (here refl)
  ... | no _     = M.map there (endIn rs c)
  endIn (_ ∷ rs)         c = M.map there (endIn rs c)

  -- A table's end at a row.
  endsAt : ∀ {X : Set} (m : Maybe (Tb.Listed X)) c → Maybe (TR m c end)
  endsAt nothing   c = nothing
  endsAt (just Lx) c = M.map (λ e → Lx , refl , e) (endIn (rows Lx) c)

-- The source's values, the same in every environment.
module Vals {Γ A} n (s : Obs Timeline Γ A) (ρ : ℕ → All Tb.Listed Γ) (p : Pos) where
  -- The source's tables.
  S : ℕ → Maybe (Tb.Listed A)
  S = Tab n s ρ p

  -- A value of the source at a cut, with its row.
  record ValAt (N : ℕ) : Set where
    constructor valAt
    field
      q   : Pos
      a   : A
      row : TR (S N) q (out a)

  -- The values among some rows, each with its membership.
  valsIn : (rs : List (Row A)) → List (Σ Pos λ q → Σ A λ a → (q , out a) ∈ rs)
  valsIn []                 = []
  valsIn ((q , out a) ∷ rs) = (q , a , here refl) ∷ L.map (λ { (q′ , a′ , m) → q′ , a′ , there m }) (valsIn rs)
  valsIn (_ ∷ rs)           = L.map (λ { (q′ , a′ , m) → q′ , a′ , there m }) (valsIn rs)

  -- The source's values at a cut.
  valsAt : ∀ N → List (ValAt N)
  valsAt N with S N in eq
  ... | nothing = []
  ... | just Lo = L.map (λ { (q , a , m) → valAt q a (Lo , eq , m) }) (valsIn (rows Lo))

  -- The source's value at a row.
  valAtPos : ∀ N → Pos → Maybe (ValAt N)
  valAtPos N q = first (valsAt N)
    where
      first : List (ValAt N) → Maybe (ValAt N)
      first []       = nothing
      first (v ∷ vs) = if does (ValAt.q v ≟ᵖ q) then just v else first vs

  -- A value's marker at a row.
  isMarker : ℕ → Pos → Bool
  isMarker N y = anyᵇ (λ v → does ((ValAt.q v ⊕ [ ix 0 ]) ≟ᵖ y)) (valsAt N)

module Flat {Γ A B} n (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
  (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) (uρ* : ∀ N → UncutEnv (ρ* N))
  (env : EnvR ρ ρι ρ*) (p p* : Pos) (ad : Admits (lw env) p) (ad* : Admits (lw* env) p*) where

  ----------------------------------------------------------------------
  -- The elaborated parts

  ρι⁴ : Ren Γ (⊤ ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ)
  ρι⁴ = wk (wk (wk (wk ρι)))

  s* : Obs Timeline (⊤ ∷ Δ) (IE A)
  s* = elab (wk ρι) s

  core : FlatOp → Obs Timeline (IE B ∷ IE A ∷ ⊤ ∷ Δ) (IE B)
  core op = flatMap op (λ a → laneˢ (elab ρι⁴ (f a))) (each valuesOf (connected (there (here refl))))

  inner : FlatOp → Obs Timeline (IE B ∷ IE A ∷ ⊤ ∷ Δ) (IE B)
  inner op = connect (core op) (combined op (trackers Γ 0 (wk (wk (wk (wk ρι))))))

  body : FlatOp → Obs Timeline (IE A ∷ ⊤ ∷ Δ) (IE B)
  body op = connect closer (inner op)

  shared : Obs Timeline (⊤ ∷ Δ) (IE A)
  shared = flatMap (mergeᶠ nothing) (λ _ → s*) (connected (here refl))

  ----------------------------------------------------------------------
  -- Their subscriptions and hots

  -- The share's body, the closer's body, the combined connect, and the
  -- lanes' flatMap.
  c₃ c₂ c₁ c₀ : Pos
  c₃ = p* ⊕ [ ix 0 ] ⊕ [ ix 0 ]
  c₂ = c₃ ⊕ [ ix 0 ]
  c₁ = c₂ ⊕ [ ix 1 ]
  c₀ = c₂ ⊕ [ ix 0 ]

  -- The source's elaborated subscription: the lane of the trigger's value,
  -- read by the shared flatMap.
  sp* : Pos
  sp* = p* ⊕ˡ (ix 1 ∷ ix 0 ∷ sub (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ]) ∷ ix 1 ∷ [])

  tt-tab : ℕ → Tb.Listed ⊤
  tt-tab N = hotOf (proj₁ (listC-ok (3 + N) n (of (tt ∷ [])) (uρ* N) (p* ⊕ [ ix 1 ])))

  ρ*s : ℕ → All Tb.Listed (⊤ ∷ Δ)
  ρ*s N = tt-tab N ∷ ρ* N

  uρ*s : ∀ N → UncutEnv (ρ*s N)
  uρ*s N = proj₂ (proj₂ (listC-ok (3 + N) n (of (tt ∷ [])) (uρ* N) (p* ⊕ [ ix 1 ]))) , uρ* N

  sh-tab : ℕ → Tb.Listed (IE A)
  sh-tab N = hotOf (proj₁ (listC-ok (3 + N) n shared {ρ*s N} (uρ*s N) (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ])))

  ρ*h : ℕ → All Tb.Listed (IE A ∷ ⊤ ∷ Δ)
  ρ*h N = sh-tab N ∷ ρ*s N

  uρ*h : ∀ N → UncutEnv (ρ*h N)
  uρ*h N = proj₂ (proj₂ (listC-ok (3 + N) n shared {ρ*s N} (uρ*s N) (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ]))) , uρ*s N

  cl-tab : ℕ → Tb.Listed (IE B)
  cl-tab N = hotOf (proj₁ (listC-ok (3 + N) n closer {ρ*h N} (uρ*h N) (c₃ ⊕ [ ix 1 ])))

  ρ*c : ℕ → All Tb.Listed (IE B ∷ IE A ∷ ⊤ ∷ Δ)
  ρ*c N = cl-tab N ∷ ρ*h N

  uρ*c : ∀ N → UncutEnv (ρ*c N)
  uρ*c N = proj₂ (proj₂ (listC-ok (3 + N) n closer {ρ*h N} (uρ*h N) (c₃ ⊕ [ ix 1 ]))) , uρ*h N

  -- Each hot listed off its lawful source, each body admissible.
  ttD : HotD tt-tab
  ttD = listHot n (of (tt ∷ [])) uρ* (lw* env) p* ad*

  Ds : DenOf ρ*s
  Ds = den-cons ttD (lw* env)

  ad₄ : Admits Ds (p* ⊕ [ ix 0 ])
  ad₄ = admits-body n (of (tt ∷ [])) uρ* (lw* env) p* ad*

  shD : HotD sh-tab
  shD = listHot n shared uρ*s Ds (p* ⊕ [ ix 0 ]) ad₄

  Dh : DenOf ρ*h
  Dh = den-cons shD Ds

  ad₃ : Admits Dh c₃
  ad₃ = admits-body n shared uρ*s Ds (p* ⊕ [ ix 0 ]) ad₄

  clD : HotD cl-tab
  clD = listHot n closer uρ*h Dh c₃ ad₃

  Dc : DenOf ρ*c
  Dc = den-cons clD Dh

  ad₂ : Admits Dc c₂
  ad₂ = admits-body n closer uρ*h Dh c₃ ad₃

  ad₁ : Admits Dc c₁
  ad₁ = admits-step Dc ad₂


  open TabRows public
  open Vals n s ρ p public

  ----------------------------------------------------------------------
  -- The children's records

  -- The hots in scope, plain and elaborated, guarding every record here.
  Sc : Scope
  Sc = scopeOf ρ ρι ρ*

  G G* : ℕ → ℕ → Pos → Set
  G  = Scope.G Sc
  G* = Scope.G* Sc

  -- The source, at the share's subscription.
  Src : Set₁
  Src = Out n s ρ (wk ρι) ρ*s (maps env) p sp*

  -- Each lane, wherever subscribed alike, whatever the four binders hold.
  Lanes : Set₁
  Lanes = ∀ a (t₁ : ℕ → Tb.Listed ⊤) (t₂ : ℕ → Tb.Listed (IE B)) (t₃ : ℕ → Tb.Listed (IE A)) (t₄ : ℕ → Tb.Listed ⊤)
        → (∀ N → UncutEnv (t₁ N ∷ t₂ N ∷ t₃ N ∷ t₄ N ∷ ρ* N))
        → (h₁ : HotD t₁) (h₂ : HotD t₂) (h₃ : HotD t₃) (h₄ : HotD t₄)
        → Holds n (f a) ρ ρι⁴ (λ N → t₁ N ∷ t₂ N ∷ t₃ N ∷ t₄ N ∷ ρ* N) (env-wk h₁ (env-wk h₂ (env-wk h₃ (env-wk h₄ env))))

  -- Two records of one lane, its trigger's hot recorded twice: they map
  -- alike and are late alike (`simultaneous.TableEnv.Coh`).
  LanesCoh : Lanes → Set₁
  LanesCoh Ls = ∀ a t₁ t₂ t₃ t₄ u (h₁ h₁′ : HotD t₁) h₂ h₃ h₄ q q* (ad ad′ : Admits (lw env) q)
                  (ad* : Admits (den-cons h₁ (den-cons h₂ (den-cons h₃ (den-cons h₄ (lw* env))))) q*)
                  (ad*′ : Admits (den-cons h₁′ (den-cons h₂ (den-cons h₃ (den-cons h₄ (lw* env))))) q*)
                  (al al′ : Aligned (maps env) ρ q q*) (lk lk′ : Linked q q*) N y
              → Same (Out.rel (Ls a t₁ t₂ t₃ t₄ u h₁ h₂ h₃ h₄ q q* ad ad* al lk)) (Out.rel (Ls a t₁ t₂ t₃ t₄ u h₁′ h₂ h₃ h₄ q q* ad′ ad*′ al′ lk′)) N y

  -- The plain flatMap's tables.
  P : FlatOp → ℕ → _
  P op = Tab n (flatMap op f s) ρ p

  -- THE SOURCE'S PINS are not the lanes' flatMap's to show: it reads the
  -- source off a hot, which shows a pin as a skip.  The share shows them,
  -- so the layers inside it relate the plain flatMap without them.
  srcPins : ℕ → List Pos
  srcPins N = M.maybe (λ Lo → pinKeys (rows Lo)) [] (Tab n s ρ p N)

  Pd : FlatOp → ℕ → Maybe (Tb.Listed B)
  Pd op N = Tb.bind (P op N) λ Lp → just (unpinAt (srcPins N) Lp)

  pd-sub : ∀ {op N k e} → TR (Pd op N) k e → TR (P op N) k e
  pd-sub {op} {N} = unpin-sub (srcPins N) (P op N)

  pd-keep : ∀ {op N k e} → TR (P op N) k e → Unpinned e → TR (Pd op N) k e
  pd-keep {op} {N} = unpin-keep (srcPins N) (P op N)

  pd-got : ∀ op N → Got (Pd op N)
  pd-got op N = got-bind (unpinAt (srcPins N)) (got-ok (3 + N) n (flatMap op f s) {ρ N} (uρ N) p)

  pd-pin-in : ∀ {op N l r} → TR (Pd op N) l (pin r) → T (inside r l)
  pd-pin-in {op} {N} x = pin-ok (3 + N) n (flatMap op f s) {ρ N} p (pd-sub {op} {N} x)

  pd-after : ∀ {op N k e} → TR (Pd op N) k e → p ≼ k
  pd-after {op} {N} x = after-ok (3 + N) n (flatMap op f s) {ρ N} p (pd-sub {op} {N} x)

  postulate
    -- Two cuts agreeing up to a row agree on which pins below it are the
    -- source's: a row of either is the source's or a lane's, and no lane
    -- row sits where a source row does.
    pd-agree : ∀ {op N N′ k} → AgreeTo k (TR (P op N)) (TR (P op N′)) → AgreeTo k (TR (Pd op N)) (TR (Pd op N′))

  -- One event at a position, none under another: each table is listed
  -- off its lawful emission set.
  pd-func : ∀ {op N y e e′} → TR (Pd op N) y e → TR (Pd op N) y e′ → e ≡ e′
  pd-func {op} {N} x x′ = tab-func n (flatMap op f s) uρ (lw env) ad (pd-sub {op} {N} x) (pd-sub {op} {N} x′)

  pd-flat : ∀ {op N y e l ys e′} → TR (Pd op N) y e → TR (Pd op N) (y ⊕ (l ∷ ys)) e′ → ⊥
  pd-flat {op} {N} x x′ = tab-flat n (flatMap op f s) uρ (lw env) ad (pd-sub {op} {N} x) (pd-sub {op} {N} x′)

  core-func : ∀ {op N y e e′} → TR (listC (3 + N) n (core op) (ρ*c N) c₁) y e → TR (listC (3 + N) n (core op) (ρ*c N) c₁) y e′ → e ≡ e′
  core-func {op} = tab-func n (core op) uρ*c Dc ad₁

  core-flat : ∀ {op N y e l ys e′} → TR (listC (3 + N) n (core op) (ρ*c N) c₁) y e → TR (listC (3 + N) n (core op) (ρ*c N) c₁) (y ⊕ (l ∷ ys)) e′ → ⊥
  core-flat {op} = tab-flat n (core op) uρ*c Dc ad₁

  -- The lanes' flatMap related to the plain flatMap.
  Core : FlatOp → Set₁
  Core op = Src → (Ls : Lanes) → LanesCoh Ls → Aligned (maps env) ρ p p* → Linked p p*
          → Rel (Pd op) (λ N → listC (3 + N) n (core op) (ρ*c N) c₁) p c₁ Sc

  ----------------------------------------------------------------------
  -- The layers

  -- THE LANES' FLATMAP: the shared hot is the source's elaborated rows,
  -- each value read off by `each valuesOf` under its image; each value's
  -- elaborated lane is the plain lane's, run through `laneˢ`.  Its rows
  -- are the plain flatMap's values and ends, along the source's map for
  -- the source's rows and each lane's for its own.
  --
  -- A lane's record is had only from a cut: `Lanes` wants the lane's
  -- value and its pair's alignment, and both are read off the source's
  -- row `TR (Ps N) q (out a)` and `Rest.cuts` at it.  So `φ`, `Put` and
  -- the preimage lists are written per cut, each lane row through its own
  -- lane's record at that cut; `back` is what lets the erasure read them
  -- at the cut settling the image.

  ----------------------------------------------------------------------
  -- The lanes

  -- What the source's and lanes' records give, for every operator.
  module Parts (Os : Src) (Ls : Lanes) (Lc : LanesCoh Ls) where

    emit-ups : ∀ l′ x → ups 5 (emitAt (l′ ⊕ [ x ])) ≡ l′
    emit-ups l′ x rewrite up-⊕ ((((l′ ⊕ [ x ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) (ix 0)
                        | up-⊕ (((l′ ⊕ [ x ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) (ix 1)
                        | up-⊕ ((l′ ⊕ [ x ]) ⊕ [ ix 1 ]) (ix 1)
                        | up-⊕ (l′ ⊕ [ x ]) (ix 1)
                        | up-⊕ l′ x = refl

    -- A lane's trigger, under its subscription.
    trig : Pos → ℕ → Tb.Listed ⊤
    trig st N = hotOf (proj₁ (listC-ok (3 + N) n (of (tt ∷ [])) {ρ*c N} (uρ*c N) (laneL st ⊕ [ ix 1 ])))

    utrig : ∀ st N → UncutEnv (trig st N ∷ ρ*c N)
    utrig st N = proj₂ (proj₂ (listC-ok (3 + N) n (of (tt ∷ [])) {ρ*c N} (uρ*c N) (laneL st ⊕ [ ix 1 ]))) , uρ*c N

    -- A value's elaborated row: the shared hot's row of its image, read by
    -- the lanes' flatMap, and the value `each` lists from it.
    val* : ℕ → Pos → Pos
    val* N q = Rel.φ (Out.rel Os) N q ⊕ˡ (sub c₁ ∷ ix 1 ∷ ix 0 ∷ [])

    -- And its lane's subscription.
    st* : ℕ → Pos → Pos
    st* N q = val* N q ⊕ [ ix 1 ]

    -- `laneˢ`'s path from an elaborated lane's subscription to the lane.
    laneXs : Pos → List Label
    laneXs st = ix 0 ∷ ix 1 ∷ laneXt st

    -- The source's values read by `each` at the share's reader.
    eachS : Obs Timeline (IE B ∷ IE A ∷ ⊤ ∷ Δ) A
    eachS = each valuesOf (connected (there (here refl)))

    -- The share's subscription, and the shared flatMap's table there.
    shp : Pos
    shp = p* ⊕ [ ix 0 ] ⊕ [ ix 1 ]

    shL : ℕ → Tb.Listed (IE A)
    shL N = proj₁ (listC-ok (3 + N) n shared {ρ*s N} (uρ*s N) shp)

    shL-eq : ∀ N → listC (3 + N) n shared (ρ*s N) shp ≡ just (shL N)
    shL-eq N = proj₁ (proj₂ (listC-ok (3 + N) n shared {ρ*s N} (uρ*s N) shp))

    -- `each`'s table under the lanes' flatMap.
    okE : ∀ N → _
    okE N = listC-ok (3 + N) n eachS {ρ*c N} (uρ*c N) c₁

    -- The trigger's value, kept before its end and rejoined under the
    -- share.
    trig-row : ∀ N → (p* ⊕ [ ix 1 ] ⊕ [ ix 0 ] ⊕ [ sub shp ] , out tt) ∈ rows (rejoin shp (tt-tab N))
    trig-row N = rejoin-in shp (tt-tab N) r₁ (part-≺ p* (ix 1 ∷ []) (ix 0 ∷ []) refl)
      where
        r₁ = proper-in ((p* ⊕ [ ix 1 ] ⊕ [ ix 0 ] , out tt) ∷ (p* ⊕ [ ix 1 ] ⊕ [ last ] , end) ∷ []) (here refl) λ { (here ()) ; (there (here refl)) → ≺→≼ {p* ⊕ [ ix 1 ] ⊕ [ ix 0 ]} (part-≺ (p* ⊕ [ ix 1 ]) [] [] refl)
                                         ; (there (there ())) }

    -- An elaborated source value is the trigger lane's, which the shared
    -- flatMap shows and, quiet past its end, keeps.
    shared-row : ∀ {N k x′} → TR (Tab n s* ρ*s sp* N) k (out x′) → sp* ≺ k → (k , out x′) ∈ rows (sh-tab N)
    shared-row {N} {k} {x′} (L′ , eqL′ , m′) sk
      with bind⁻ {m = lanes (afterL (λ _ → listC (3 + N) n s* (ρ*s N))) (values (rows (rejoin shp (tt-tab N))))} (shL-eq N)
    ... | (ls , els , e₂) = proper-in (rows (shL N)) r λ cm lt → noPin (InvAt.quiet Ish (shL N , shL-eq N , cm) (shL N , shL-eq N , r) lt)
      where
        Ish = tab-at n shared uρ*s Ds (admits-step Ds ad₄) N
        lm = lane-of {ln = afterL (λ _ → listC (3 + N) n s* (ρ*s N))} els (values⁺ (trig-row N)) (cong (λ m → bind m λ l → just (past sp* l)) eqL′)
        r : (k , out x′) ∈ rows (shL N)
        r = subst (λ L → (k , out x′) ∈ rows L) (just-injective e₂) (merge-lane-out (rejoin shp (tt-tab N)) ls lm (pastRows⁺ (rows L′) m′ sk))
        noPin : ∀ {c} → PinBy c (out x′) → ⊥
        noPin (_ , () , _)

    -- A value the shared hot keeps past the lanes' flatMap's subscription
    -- is listed by `each` one lane down.
    each-at : ∀ {N k x′ a} → (k , out x′) ∈ rows (sh-tab N) → c₁ ≺ k → valuesOf x′ ≡ a ∷ []
            → TR (Tab n eachS ρ*c c₁ N) (k ⊕ˡ (sub c₁ ∷ ix 1 ∷ ix 0 ∷ [])) (out a)
    each-at {N} {k} {x′} {a} r ck rd
      with bind⁻ {m = lanes (afterL (λ x → listC (3 + N) n (of (valuesOf x)) (ρ*c N))) (values (rows (rejoin c₁ (sh-tab N))))} (proj₁ (proj₂ (okE N)))
    ... | (ls , els , e₂) = proj₁ (okE N) , proj₁ (proj₂ (okE N)) , subst (λ L → _ ∈ rows L) (just-injective e₂)
            (merge-lane-out (rejoin c₁ (sh-tab N)) ls (lane-of {ln = afterL (λ x → listC (3 + N) n (of (valuesOf x)) (ρ*c N))} els (values⁺ (rejoin-in c₁ (sh-tab N) r ck)) refl) (of-past (k ⊕ [ sub c₁ ] ⊕ [ ix 1 ]) (valuesOf x′) rd))

    -- THE READER'S ROWS: each value of the source is the elaborated
    -- source's value at its image, which the shared flatMap keeps; the
    -- lanes' flatMap reads it under its subscription.
    each-row : ∀ {N q a} → TR (S N) q (out a) → TR (Tab n eachS ρ*c c₁ N) (val* N q) (out a)
    each-row {N} {q} {a} x with Corr.row→ (Rel.corr (Out.rel Os) N) x tt
    ... | inj₂ (() , _)
    ... | inj₁ ((e′ , y , mt) , _) with proj₁ mt tt
    ...   | x′ , refl , rd = each-at (shared-row y sk) (≺-trans {c₁} {sp*} (part-≺ p* (ix 0 ∷ ix 0 ∷ ix 1 ∷ []) (ix 0 ∷ sub shp ∷ ix 1 ∷ []) refl) sk) rd
      where
        Isp = tab-at n s* uρ*s Ds (admits-trig n uρ* (lw* env) p* ad*) N
        sk : sp* ≺ Rel.φ (Out.rel Os) N q
        sk = world-after (InvAt.world Isp y) (InvAt.real Isp y)

    -- A lane's trigger, listed off its lawful source, and the lane's
    -- elaborated subscription admissible under it.
    trigD : ∀ st → Admits Dc st → HotD (trig st)
    trigD st a = listHot n (of (tt ∷ [])) uρ*c Dc (laneL st) (admits-ix Dc 1 (admits-ix Dc 0 a))

    laneAdm : ∀ st (a : Admits Dc st) → Admits (den-cons (trigD st a) Dc) (laneX st)
    laneAdm st a = admits-ix D′ 1 (admits-ix D′ 0 (admits-trig n uρ*c Dc (laneL st) (admits-ix Dc 1 (admits-ix Dc 0 a))))
      where D′ = den-cons (trigD st a) Dc

    -- A lane related at a cut: its value, its two subscriptions, its
    -- record.
    record LaneRec (N : ℕ) : Set₁ where
      constructor laneRec
      field
        a   : A
        st  : Pos
        stE : Pos
        alL : Aligned (maps env) ρ st (laneL stE)
        adm : Admits (lw env) st
        adm* : Admits Dc stE
        lane : Out n (f a) ρ ρι⁴ (λ N′ → trig stE N′ ∷ ρ*c N′) (maps env) st (laneX stE)

      -- The lane's plain tables.
      tab : Maybe (Tb.Listed B)
      tab = Tab n (f a) ρ st N

      -- Its row's image as the lanes' flatMap shows it: read by
      -- `laneˢ`'s reader and emitted by `counted`; an end at its
      -- `laneDone`'s, which follows the share's end.
      -- The share ends at the later of the lane's end and its trigger's:
      -- a lane ended in its subscribe frame ends first.
      trigEnd : Pos
      trigEnd = laneL stE ⊕ˡ trigXs stE

      endφ : Pos → Pos
      endφ y = later (Rel.φ (Out.rel lane) N y) trigEnd

      outImage endImage : Pos → Pos
      outImage y = emitAt (Rel.φ (Out.rel lane) N y ⊕ [ sub (readerR stE) ])
      endImage y = emitAt (endφ y ⊕ˡ (sub (readerR stE) ∷ ix 1 ∷ ix 0 ∷ [])) ⊕ [ last ]

    -- A lane's end is never late.
    end-nl : ∀ {N} (R : LaneRec N) {c} → TR (LaneRec.tab R) c end → ¬ Rel.Late (Out.rel (LaneRec.lane R)) N c
    end-nl {N} R cx = nl-ev (Rel.corr (Out.rel (LaneRec.lane R)) N) cx (λ ())

    -- A lane row's lane image lies under its images here.
    out-≼ : ∀ {N} (R : LaneRec N) y → Rel.φ (Out.rel (LaneRec.lane R)) N y ≼ LaneRec.outImage R y
    out-≼ {N} R y = ≼-ˡ (Rel.φ (Out.rel (LaneRec.lane R)) N y) (sub (readerR (LaneRec.stE R)) ∷ ix 1 ∷ ix 1 ∷ ix 1 ∷ ix 0 ∷ [])

    end-≼ : ∀ {N} (R : LaneRec N) y → Rel.φ (Out.rel (LaneRec.lane R)) N y ≼ LaneRec.endImage R y
    end-≼ {N} R y = ≼-trans {φy} {e} {LaneRec.endImage R y} (≼-trans {φy} {LaneRec.endφ R y} {e} φ-e (≼-ˡ (LaneRec.endφ R y) ys)) (≼-ˡ e (ix 1 ∷ ix 1 ∷ ix 1 ∷ ix 0 ∷ last ∷ []))
      where
        φy = Rel.φ (Out.rel (LaneRec.lane R)) N y
        ys = sub (readerR (LaneRec.stE R)) ∷ ix 1 ∷ ix 0 ∷ []
        e  = LaneRec.endφ R y ⊕ˡ ys
        φ-e : φy ≼ LaneRec.endφ R y
        φ-e with later-cases φy (LaneRec.trigEnd R)
        ... | inj₁ (eq , _)  = subst (φy ≼_) (sym eq) (≼-refl {φy})
        ... | inj₂ (eq , lt) = subst (φy ≼_) (sym eq) (≺→≼ {φy} {LaneRec.trigEnd R} lt)

    -- THE ELABORATED LANE'S END: where `laneˢ` shows the lane's end, its
    -- `laneDone` taken by the take.
    lane-end-image : ∀ {N} (R : LaneRec N) {c} → TR (LaneRec.tab R) c end
                   → TR (Tab n (laneˢ (elab ρι⁴ (f (LaneRec.a R)))) ρ*c (LaneRec.stE R) N) (LaneRec.endImage R c) end
    lane-end-image {N} R {c} cx = Lane.lane-end n (elab ρι⁴ (f (LaneRec.a R))) uρ*c Dc (LaneRec.stE R) (LaneRec.adm* R) N
                     (λ h → elab-undone (3 + N) n ρι⁴ (f (LaneRec.a R)) (h ∷ den Dc N) (λ i → unended env N i))
                     {t = trig (LaneRec.stE R) N} {o = laneˢ (elab ρι⁴ (f (LaneRec.a R)))} {q = LaneRec.endImage R c}
                     {e = Rel.φ (Out.rel (LaneRec.lane R)) N c} refl refl refl
                     (corr-end (Rel.corr (Out.rel (LaneRec.lane R)) N) cx)

    -- A lane's end, past its trigger's: its own facts there, or, where
    -- the trigger's end is the later, the trigger's.  The trigger's end
    -- is then in the lane's instant, and under the lane's subscription,
    -- which no hot's image is under.
    trig-inst : ∀ {N} (R : LaneRec N) {c} → TR (LaneRec.tab R) c end → Rel.φ (Out.rel (LaneRec.lane R)) N c ≺ LaneRec.trigEnd R
              → instantOf (Rel.φ (Out.rel (LaneRec.lane R)) N c) ≡ instantOf (LaneRec.trigEnd R)
    trig-inst {N} R {c} cx lt =
      squeeze {laneX stE} {Rel.φ (Out.rel lane) N c} {trigEnd} (Rel.after-φ (Out.rel lane) cx tt (end-nl R cx)) lt
        (trans (inst-⊕ˡ (laneL stE) (laneXt stE)) (sym (inst-⊕ˡ (laneL stE) (trigXs stE))))
      where open LaneRec R

    trig-linked : ∀ {N} (R : LaneRec N) {c} → TR (LaneRec.tab R) c end
                → Rel.φ (Out.rel (LaneRec.lane R)) N c ≺ LaneRec.trigEnd R → Linked c (LaneRec.trigEnd R)
    trig-linked {N} R {c} cx lt = linked-later (Rest.linked (Out.rest lane) N cx tt (end-nl R cx)) (trig-inst R cx lt) lt
      where open LaneRec R

    trig-cuts : ∀ {N} (R : LaneRec N) {c} → TR (LaneRec.tab R) c end
              → Rel.φ (Out.rel (LaneRec.lane R)) N c ≺ LaneRec.trigEnd R → Aligned (maps env) ρ c (LaneRec.trigEnd R)
    trig-cuts {N} R {c} cx lt =
      aligned-past {Ψ = maps env} {ρ = ρ} alL
        (≼-trans {laneL stE} {laneX stE} {Rel.φ (Out.rel lane) N c} (≼-ˡ (laneL stE) (laneXt stE)) (Rel.after-φ (Out.rel lane) cx tt (end-nl R cx)))
        lt (⊑-⊕ˡ (laneL stE) (trigXs stE)) (trig-inst R cx lt) (Rest.cuts (Out.rest lane) N cx tt)
      where open LaneRec R

    end-cuts : ∀ {N} (R : LaneRec N) {c} → TR (LaneRec.tab R) c end → Aligned (maps env) ρ c (LaneRec.endφ R c)
    end-cuts {N} R {c} cx with later-cases (Rel.φ (Out.rel (LaneRec.lane R)) N c) (LaneRec.trigEnd R)
    ... | inj₁ (eq , _)  = subst (Aligned (maps env) ρ c) (sym eq) (Rest.cuts (Out.rest (LaneRec.lane R)) N cx tt)
    ... | inj₂ (eq , lt) = subst (Aligned (maps env) ρ c) (sym eq) (trig-cuts R cx lt)

    end-linked : ∀ {N} (R : LaneRec N) {c} → TR (LaneRec.tab R) c end → Linked c (LaneRec.endφ R c)
    end-linked {N} R {c} cx with later-cases (Rel.φ (Out.rel (LaneRec.lane R)) N c) (LaneRec.trigEnd R)
    ... | inj₁ (eq , _)  = subst (Linked c) (sym eq) (Rest.linked (Out.rest (LaneRec.lane R)) N cx tt (end-nl R cx))
    ... | inj₂ (eq , lt) = subst (Linked c) (sym eq) (trig-linked R cx lt)

    -- A value's lane, subscribed under its row: the source's facts at the
    -- row align the lane's pair.
    valRec : ∀ N → ValAt N → LaneRec N
    valRec N (valAt q a x) = laneRec a (q ⊕ [ ix 1 ]) st alL ad₀ ad₀* (
      Ls a (trig st) cl-tab sh-tab tt-tab (utrig st) (trigD st ad₀*) clD shD ttD (q ⊕ [ ix 1 ]) (laneX st) ad₀ (laneAdm st ad₀*)
         (aligned-r* {Ψ = maps env} {ρ = ρ} alL (laneXt st))
         (linked-r* (linked-r (linked-l (Rest.linked (Out.rest Os) N x tt nlx) (ix 1)) (sub c₁)) ys))
      where
        nlx = nl-ev (Rel.corr (Out.rel Os) N) x (λ ())
        st = st* N q
        ys = ix 1 ∷ ix 0 ∷ ix 1 ∷ laneXs st
        ad₀ : Admits (lw env) (q ⊕ [ ix 1 ])
        ad₀ = admits-row n s uρ (lw env) ad x
        ad₀* : Admits Dc st
        ad₀* = admits-row n eachS uρ*c Dc ad₁ (each-row x)
        alL : Aligned (maps env) ρ (q ⊕ [ ix 1 ]) (laneL st)
        alL = aligned-r* {Ψ = maps env} {ρ = ρ} (aligned-⊕ {Ψ = maps env} {ρ = ρ} (Rest.cuts (Out.rest Os) N x tt) (ix 1) (sub c₁))
                (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ [])

    -- A value's lane, queued under the end of the lane it waited on: that
    -- lane's facts at its end align the pair, the elaborated lane queued
    -- under the end's image.
    queuedRec : ∀ N (R : LaneRec N) {c} → TR (LaneRec.tab R) c end → A → LaneRec N
    queuedRec N R {c} cx a = laneRec a (c ⊕ [ ix 1 ]) st alL ad₀ ad₀* (
      Ls a (trig st) cl-tab sh-tab tt-tab (utrig st) (trigD st ad₀*) clD shD ttD (c ⊕ [ ix 1 ]) (laneX st) ad₀ (laneAdm st ad₀*)
         (aligned-r* {Ψ = maps env} {ρ = ρ} alL (laneXt st))
         (linked-r* (linked-r (linked-l (end-linked R cx) (ix 1)) (sub r)) ys))
      where
        r  = readerR (LaneRec.stE R)
        st = LaneRec.endImage R c ⊕ [ ix 1 ]
        ad₀ : Admits (lw env) (c ⊕ [ ix 1 ])
        ad₀ = admits-row n (f (LaneRec.a R)) uρ (lw env) (LaneRec.adm R) cx
        ad₀* : Admits Dc st
        ad₀* = admits-row n (laneˢ (elab ρι⁴ (f (LaneRec.a R)))) uρ*c Dc (LaneRec.adm* R) (lane-end-image R cx)
        ys = ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ ix 1 ∷ ix 0 ∷ last ∷ ix 1 ∷ laneXs st
        alL : Aligned (maps env) ρ (c ⊕ [ ix 1 ]) (laneL st)
        alL = aligned-r* {Ψ = maps env} {ρ = ρ} (aligned-⊕ {Ψ = maps env} {ρ = ρ} (end-cuts R cx) (ix 1) (sub r))
                (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ ix 1 ∷ ix 0 ∷ last ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ [])

    -- The last of some lanes that `h` picks: a queued lane is listed after
    -- the lane it waited on.
    lastWith : ∀ {N} → (LaneRec N → Bool) → List (LaneRec N) → Maybe (LaneRec N)
    lastWith h []       = nothing
    lastWith h (R ∷ Rs) with lastWith h Rs
    ... | just R′ = just R′
    ... | nothing = if h R then just R else nothing

    -- The lane whose table holds a row at `y`: a lane's row need not lie
    -- under its subscription, read off a hot or in a cascade its timer
    -- made.
    holder : ∀ {N} → List (LaneRec N) → Pos → Maybe (LaneRec N)
    holder Rs y = lastWith (λ R → rowAt (LaneRec.tab R) y) Rs

    lastWith-∈ : ∀ {N} h (Rs : List (LaneRec N)) {R} → lastWith h Rs ≡ just R → R ∈ Rs
    lastWith-∈ h (R ∷ Rs) e with lastWith h Rs in eq
    lastWith-∈ h (R ∷ Rs) refl | just R′ = there (lastWith-∈ h Rs eq)
    ... | nothing with h R
    lastWith-∈ h (R ∷ Rs) refl | nothing | true = here refl

    -- The lane among some that ends at `c`.
    waitedOn : ∀ {N} → List (LaneRec N) → ∀ c → Maybe (Σ (LaneRec N) λ R → TR (LaneRec.tab R) c end)
    waitedOn []       c = nothing
    waitedOn (R ∷ Rs) c with endsAt (LaneRec.tab R) c
    ... | just x  = just (R , x)
    ... | nothing = waitedOn Rs c

    -- The last of some lanes `h` picks, `h` picks.
    lastWith-h : ∀ {N} h (Rs : List (LaneRec N)) {R} → lastWith h Rs ≡ just R → h R ≡ true
    lastWith-h h (R ∷ Rs) e with lastWith h Rs in eq
    lastWith-h h (R ∷ Rs) refl | just R′ = lastWith-h h Rs eq
    ... | nothing with h R in hR
    lastWith-h h (R ∷ Rs) refl | nothing | true = hR

    -- TWO CUTS' RECORDS OF ONE LANE, alike up to `k`: subscribed alike,
    -- listing alike, and mapping each row alike, late alike.
    record LaneEq {N N′} (k : Pos) (R : LaneRec N) (R′ : LaneRec N′) : Set where
      field
        stE≡ : LaneRec.stE R ≡ LaneRec.stE R′
        tab≈ : AgreeTo k (TR (LaneRec.tab R)) (TR (LaneRec.tab R′))
        φ≡   : ∀ {y e} → y ≼ k → TR (LaneRec.tab R) y e → Unpinned e → ¬ Rel.Late (Out.rel (LaneRec.lane R)) N y
             → G N N′ y → G* N N′ (Rel.φ (Out.rel (LaneRec.lane R)) N y)
             → Rel.φ (Out.rel (LaneRec.lane R)) N y ≡ Rel.φ (Out.rel (LaneRec.lane R′)) N′ y
        nl≡  : ∀ {y e} → y ≼ k → TR (LaneRec.tab R) y e → Unpinned e → ¬ Rel.Late (Out.rel (LaneRec.lane R)) N y
             → G N N′ y → G* N N′ (Rel.φ (Out.rel (LaneRec.lane R)) N y)
             → ¬ Rel.Late (Out.rel (LaneRec.lane R′)) N′ y

    out-eq : ∀ {N N′ k} {R : LaneRec N} {R′ : LaneRec N′} → LaneEq k R R′ → ∀ {y e} → y ≼ k → TR (LaneRec.tab R) y e → Unpinned e
           → ¬ Rel.Late (Out.rel (LaneRec.lane R)) N y → G N N′ y → G* N N′ (Rel.φ (Out.rel (LaneRec.lane R)) N y)
           → LaneRec.outImage R y ≡ LaneRec.outImage R′ y
    out-eq E yk x un nl g g* = cong₂ (λ u v → emitAt (u ⊕ [ sub (readerR v) ])) (LaneEq.φ≡ E yk x un nl g g*) (LaneEq.stE≡ E)

    end-eq : ∀ {N N′ k} {R : LaneRec N} {R′ : LaneRec N′} → LaneEq k R R′ → ∀ {y e} → y ≼ k → TR (LaneRec.tab R) y e → Unpinned e
           → ¬ Rel.Late (Out.rel (LaneRec.lane R)) N y → G N N′ y → G* N N′ (Rel.φ (Out.rel (LaneRec.lane R)) N y)
           → LaneRec.endImage R y ≡ LaneRec.endImage R′ y
    end-eq E yk x un nl g g* = cong₂ (λ u v → emitAt (later u (laneL v ⊕ˡ trigXs v) ⊕ˡ (sub (readerR v) ∷ ix 1 ∷ ix 0 ∷ [])) ⊕ [ last ])
                             (LaneEq.φ≡ E yk x un nl g g*) (LaneEq.stE≡ E)

    -- Two cuts' lanes, alike up to `k` in order, each unmatched one quiet.
    data LanesEq {N N′} (k : Pos) : List (LaneRec N) → List (LaneRec N′) → Set₁ where
      []ₗ   : LanesEq k [] []
      _∷ₗ_  : ∀ {R R′ Rs Rs′} → LaneEq k R R′ → LanesEq k Rs Rs′ → LanesEq k (R ∷ Rs) (R′ ∷ Rs′)
      skipˡ : ∀ {R Rs Rs′} → Quiet k (LaneRec.tab R) → LanesEq k Rs Rs′ → LanesEq k (R ∷ Rs) Rs′
      skipʳ : ∀ {R′ Rs Rs′} → Quiet k (LaneRec.tab R′) → LanesEq k Rs Rs′ → LanesEq k Rs (R′ ∷ Rs′)

    -- Two picks of lanes: neither, or two records of one lane.
    data Match {N N′} (k : Pos) : Maybe (LaneRec N) → Maybe (LaneRec N′) → Set₁ where
      none : Match k nothing nothing
      both : ∀ {R R′} → LaneEq k R R′ → Match k (just R) (just R′)

    -- Alike lanes, picked alike, give alike picks.
    lastWith-eq : ∀ {N N′ k} (h : LaneRec N → Bool) (h′ : LaneRec N′ → Bool)
                → (∀ {R R′} → LaneEq k R R′ → h R ≡ h′ R′)
                → (∀ {R} → Quiet k (LaneRec.tab R) → h R ≡ false)
                → (∀ {R′} → Quiet k (LaneRec.tab R′) → h′ R′ ≡ false)
                → ∀ {Rs Rs′} → LanesEq k Rs Rs′ → Match k (lastWith h Rs) (lastWith h′ Rs′)
    lastWith-eq h h′ hh q q′ []ₗ = none
    lastWith-eq h h′ hh q q′ (_∷ₗ_ {R} {R′} {Rs} {Rs′} E es) with lastWith h Rs | lastWith h′ Rs′ | lastWith-eq h h′ hh q q′ es
    ... | just A  | just A′ | m    = m
    ... | nothing | nothing | none with h R | hh E
    ...   | true  | e = subst (λ b → Match _ (just R) (if b then just R′ else nothing)) e (both E)
    ...   | false | e = subst (λ b → Match _ nothing (if b then just R′ else nothing)) e none
    lastWith-eq h h′ hh q q′ (skipˡ {R} {Rs} Qr es) with lastWith h Rs | lastWith-eq h h′ hh q q′ es
    ... | just A  | m = m
    ... | nothing | m rewrite q {R} Qr = m
    lastWith-eq h h′ hh q q′ (skipʳ {R′} {Rs} {Rs′} Qr es) with lastWith h′ Rs′ | lastWith-eq h h′ hh q q′ es
    ... | just A′ | m = m
    ... | nothing | m rewrite q′ {R′} Qr = m

    -- A lane related at two cuts' alike subscriptions maps alike and is
    -- late alike: the records differ only in how the subscriptions are
    -- admitted.
    lane-coh : ∀ {a q st st′} → st ≡ st′ → (ad* : Admits Dc st) (ad*′ : Admits Dc st′)
             → (ad ad′ : Admits (lw env) q) (al : Aligned (maps env) ρ q (laneX st)) (al′ : Aligned (maps env) ρ q (laneX st′))
             → (lk : Linked q (laneX st)) (lk′ : Linked q (laneX st′)) → ∀ N y
             → Same (Out.rel (Ls a (trig st) cl-tab sh-tab tt-tab (utrig st) (trigD st ad*) clD shD ttD q (laneX st) ad (laneAdm st ad*) al lk))
                    (Out.rel (Ls a (trig st′) cl-tab sh-tab tt-tab (utrig st′) (trigD st′ ad*′) clD shD ttD q (laneX st′) ad′ (laneAdm st′ ad*′) al′ lk′)) N y
    lane-coh {a} {q} {st} refl ad* ad*′ ad ad′ al al′ lk lk′ =
      Lc a (trig st) cl-tab sh-tab tt-tab (utrig st) (trigD st ad*) (trigD st ad*′) clD shD ttD q (laneX st) ad ad′ (laneAdm st ad*) (laneAdm st ad*′) al al′ lk lk′

    -- TWO CUTS' VALUES, alike up to `k`: at one row, read alike, their
    -- lanes subscribed and listing alike.
    record ValEq {N N′} (k : Pos) (v : ValAt N) (v′ : ValAt N′) : Set where
      field
        q≡   : ValAt.q v ≡ ValAt.q v′
        a≡   : ValAt.a v ≡ ValAt.a v′
        st≡  : st* N (ValAt.q v) ≡ st* N′ (ValAt.q v′)
        tab≈ : AgreeTo k (TR (Tab n (f (ValAt.a v)) ρ (ValAt.q v ⊕ [ ix 1 ]) N)) (TR (Tab n (f (ValAt.a v′)) ρ (ValAt.q v′ ⊕ [ ix 1 ]) N′))

    -- A value's two lanes are one lane's two records.
    valRec-eq : ∀ {N N′ k} {v : ValAt N} {v′ : ValAt N′} → ValEq k v v′ → LaneEq k (valRec N v) (valRec N′ v′)
    valRec-eq {N} {N′} {k} {valAt q a x} {valAt .q .a x′} record { q≡ = refl ; a≡ = refl ; st≡ = st≡ ; tab≈ = tab≈ } = record
      { stE≡ = st≡
      ; tab≈ = tab≈
      ; φ≡   = λ {y} yk ty un nl g g* → trans (Rel.φ-agree (Out.rel (LaneRec.lane (valRec N (valAt q a x)))) {N} {N′} ty un nl g g* (ag-down yk tab≈))
                                      (φ≡ (lane-coh st≡ (LaneRec.adm* (valRec N (valAt q a x))) (LaneRec.adm* (valRec N′ (valAt q a x′))) _ _ _ _ _ _ N′ y))
      ; nl≡  = λ {y} yk ty un nl g g* → nl→ (lane-coh st≡ (LaneRec.adm* (valRec N (valAt q a x))) (LaneRec.adm* (valRec N′ (valAt q a x′))) _ _ _ _ _ _ N′ y)
                                      (Rel.late-agree (Out.rel (LaneRec.lane (valRec N (valAt q a x)))) {N} {N′} ty un nl g g* (ag-down yk tab≈))
      }

    -- Two cuts' values, alike up to `k` in order, each unmatched one's
    -- lane quiet.
    data ValsEq {N N′} (k : Pos) : List (ValAt N) → List (ValAt N′) → Set where
      []ᵥ   : ValsEq k [] []
      _∷ᵥ_  : ∀ {v v′ vs vs′} → ValEq k v v′ → ValsEq k vs vs′ → ValsEq k (v ∷ vs) (v′ ∷ vs′)
      skipᵥˡ : ∀ {v vs vs′} → Quiet k (Tab n (f (ValAt.a v)) ρ (ValAt.q v ⊕ [ ix 1 ]) N) → ValsEq k vs vs′ → ValsEq k (v ∷ vs) vs′
      skipᵥʳ : ∀ {v′ vs vs′} → Quiet k (Tab n (f (ValAt.a v′)) ρ (ValAt.q v′ ⊕ [ ix 1 ]) N′) → ValsEq k vs vs′ → ValsEq k vs (v′ ∷ vs′)

    vals-lanes : ∀ {N N′ k} {vs : List (ValAt N)} {vs′ : List (ValAt N′)} → ValsEq k vs vs′ → LanesEq k (L.map (valRec N) vs) (L.map (valRec N′) vs′)
    vals-lanes []ᵥ          = []ₗ
    vals-lanes (E ∷ᵥ es)    = valRec-eq E ∷ₗ vals-lanes es
    vals-lanes (skipᵥˡ q es) = skipˡ q (vals-lanes es)
    vals-lanes (skipᵥʳ q es) = skipʳ q (vals-lanes es)

    -- The trigger's end, read by the share.
    ttEnd : Pos
    ttEnd = p* ⊕ˡ (ix 1 ∷ last ∷ sub (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ]) ∷ [])

    -- A source row's image, read through the shared hot.
    srcφ : ℕ → Pos → Pos
    srcφ N k = Rel.φ (Out.rel Os) N k ⊕ [ sub c₁ ]

    -- THE MERGES' MAP, given each cut's lanes.  A lane row is imaged
    -- through its lane's record at the cut, a lane's put also where
    -- `laneˢ`'s share shows the lane's row, so its pins; the skip a queue leaves past a
    -- lane's end at its end image's; a value's marker at the marker of its
    -- elaborated value; the source's end at the later of its own and the
    -- trigger's, as the share ends; any other source row through the
    -- shared hot.
    module Tabs (op : FlatOp) (lanes : ∀ N → List (LaneRec N)) where
      -- A row's image, given the lane holding it and the lane ending just
      -- above it.
      rowφ : ∀ N → Pos → Maybe (LaneRec N) → Maybe (LaneRec N) → Pos
      rowφ N y (just R) _        = if endAt (LaneRec.tab R) y then LaneRec.endImage R y else LaneRec.outImage R y
      rowφ N y nothing  (just R) = LaneRec.endImage R (up y) ⊕ [ ix 0 ]
      rowφ N y nothing  nothing  = if isMarker N y then val* N (up y) ⊕ [ ix 0 ]
                                   else if endAt (S N) y then later (Rel.φ (Out.rel Os) N y) ttEnd ⊕ [ sub c₁ ]
                                   else srcφ N y

      ends-above : ∀ {N} → Pos → List (LaneRec N) → Maybe (LaneRec N)
      ends-above y = lastWith (λ R → endAt (LaneRec.tab R) (up y))

      φ′ : ℕ → Pos → Pos
      φ′ N y = rowφ N y (holder (lanes N) y) (ends-above y (lanes N))

      -- A row is late as the lane holding it says, or else a source row
      -- as the source says.
      lateAt : ∀ N → Pos → Maybe (LaneRec N) → Set
      lateAt N y (just R) = Rel.Late (Out.rel (LaneRec.lane R)) N y
      lateAt N y nothing  = (Σ _ λ e → TR (S N) y e) × Rel.Late (Out.rel Os) N y

      Late′ : ℕ → Pos → Set
      Late′ N y = lateAt N y (holder (lanes N) y)

      -- What the map reads off the source where no lane holds the row.
      record SrcAt (N N′ : ℕ) (k : Pos) : Set where
        field
          mark≡ : isMarker N k ≡ isMarker N′ k
          val≡  : isMarker N k ≡ true → val* N (up k) ≡ val* N′ (up k)
          end≡  : endAt (S N) k ≡ endAt (S N′) k
          src≡  : isMarker N k ≡ false → Rel.φ (Out.rel Os) N k ≡ Rel.φ (Out.rel Os) N′ k

      rowφ-eq : ∀ {N N′ k} {m e : Maybe (LaneRec N)} {m′ e′ : Maybe (LaneRec N′)} → Match k m m′ → Match k e e′
              → (∀ {R} → m ≡ just R → Σ (Ev B) λ ev → TR (LaneRec.tab R) k ev × Unpinned ev × ¬ Rel.Late (Out.rel (LaneRec.lane R)) N k)
              → (∀ {R} → e ≡ just R → TR (LaneRec.tab R) (up k) end)
              → (m ≡ nothing → e ≡ nothing → SrcAt N N′ k)
              → G N N′ k → G* N N′ (rowφ N k m e)
              → rowφ N k m e ≡ rowφ N′ k m′ e′
      rowφ-eq {N} {k = k} (both {R} {R′} E) _ un _ _ g g* with un refl
      ... | ev , x , u , nl = if-≡ (endAt-agree {m = LaneRec.tab R} {m′ = LaneRec.tab R′} {k = k} {y = k} (≼-refl {k}) (LaneEq.tab≈ E))
                                   (λ h → end-eq E (≼-refl {k}) (endAt-T (LaneRec.tab R) h) tt nl g gφ) (λ _ → out-eq E (≼-refl {k}) x u nl g gφ)
        where
          gφ : G* _ _ (Rel.φ (Out.rel (LaneRec.lane R)) N k)
          gφ = Scope.g*-down Sc (in-if (endAt (LaneRec.tab R) k) (λ z → Rel.φ (Out.rel (LaneRec.lane R)) N k ≼ z) (λ _ → end-≼ R k) (λ _ → out-≼ R k)) g*
      rowφ-eq {N} {k = k} none (both {R} E) _ en _ g g* =
        cong (_⊕ [ ix 0 ]) (end-eq E (up-≼ k) (en refl) tt (end-nl R (en refl)) (Scope.g-down Sc (up-≼ k) g)
          (Scope.g*-down Sc (≼-trans {Rel.φ (Out.rel (LaneRec.lane R)) N (up k)} {LaneRec.endImage R (up k)} {LaneRec.endImage R (up k) ⊕ [ ix 0 ]}
                               (end-≼ R (up k)) (≼-ˡ (LaneRec.endImage R (up k)) (ix 0 ∷ []))) g*))
      rowφ-eq none none _ _ src _ _ with src refl refl
      ... | S≡ = if-≡ (SrcAt.mark≡ S≡) (λ h → cong (_⊕ [ ix 0 ]) (SrcAt.val≡ S≡ h))
                      (λ h → if-≡ (SrcAt.end≡ S≡) (λ _ → cong (λ u → later u ttEnd ⊕ [ sub c₁ ]) (SrcAt.src≡ S≡ h))
                                                 (λ _ → cong (_⊕ [ sub c₁ ]) (SrcAt.src≡ S≡ h)))

      -- THE MAP AGREES ACROSS CUTS, for every joiner: given two cuts'
      -- lanes alike up to a row, the holder's row unpinned, and the
      -- source read alike where no lane holds it.
      tabs-φ-agree : ∀ {N N′ k} → ¬ Late′ N k → G N N′ k → G* N N′ (φ′ N k) → LanesEq k (lanes N) (lanes N′)
                   → (∀ {R} → holder (lanes N) k ≡ just R → Σ (Ev B) λ ev → TR (LaneRec.tab R) k ev × Unpinned ev)
                   → (holder (lanes N) k ≡ nothing → ends-above k (lanes N) ≡ nothing → SrcAt N N′ k)
                   → φ′ N k ≡ φ′ N′ k
      tabs-φ-agree {N} {N′} {k} nl g g* es un src =
        rowφ-eq (lastWith-eq hr hr′ (λ {R} {R′} E → rowAt-agree {m = LaneRec.tab R} {m′ = LaneRec.tab R′} {k = k} {y = k} (≼-refl {k}) (LaneEq.tab≈ E))
                             (λ {R} Q → rowAt-F {m = LaneRec.tab R} {k = k} {y = k} (≼-refl {k}) Q) (λ {R′} Q → rowAt-F {m = LaneRec.tab R′} {k = k} {y = k} (≼-refl {k}) Q) es)
                (lastWith-eq he he′ (λ {R} {R′} E → endAt-agree {m = LaneRec.tab R} {m′ = LaneRec.tab R′} {k = k} {y = up k} (up-≼ k) (LaneEq.tab≈ E))
                             (λ {R} Q → endAt-F {m = LaneRec.tab R} {k = k} {y = up k} (up-≼ k) Q) (λ {R′} Q → endAt-F {m = LaneRec.tab R′} {k = k} {y = up k} (up-≼ k) Q) es)
                (λ {R} e → let (ev , x , u) = un e in ev , x , u , λ lt → nl (subst (lateAt N k) (sym e) lt))
                (λ {R} e → endAt-T (LaneRec.tab R) (lastWith-h he (lanes N) e)) src g g*
        where
          hr : LaneRec N → Bool
          hr R = rowAt (LaneRec.tab R) k
          hr′ : LaneRec N′ → Bool
          hr′ R = rowAt (LaneRec.tab R) k
          he : LaneRec N → Bool
          he R = endAt (LaneRec.tab R) (up k)
          he′ : LaneRec N′ → Bool
          he′ R = endAt (LaneRec.tab R) (up k)

      -- A row not late stays so at a cut whose lanes are alike up to it,
      -- the holder's through its lane, a source row's through the source.
      late-eq : ∀ {N N′ k} {m e : Maybe (LaneRec N)} {m′ : Maybe (LaneRec N′)} → Match k m m′
              → (∀ {R} → m ≡ just R → Σ (Ev B) λ ev → TR (LaneRec.tab R) k ev × Unpinned ev)
              → (m ≡ nothing → ¬ lateAt N k nothing → ¬ lateAt N′ k nothing)
              → ¬ lateAt N k m → G N N′ k → G* N N′ (rowφ N k m e) → ¬ lateAt N′ k m′
      late-eq {N} {k = k} (both {R} E) un _ nl g g* with un refl
      ... | ev , x , u = LaneEq.nl≡ E (≼-refl {k}) x u nl g gφ
        where
          gφ : G* _ _ (Rel.φ (Out.rel (LaneRec.lane R)) N k)
          gφ = Scope.g*-down Sc (in-if (endAt (LaneRec.tab R) k) (λ z → Rel.φ (Out.rel (LaneRec.lane R)) N k ≼ z) (λ _ → end-≼ R k) (λ _ → out-≼ R k)) g*
      late-eq none _ src nl _ _ = src refl nl

      tabs-late-agree : ∀ {N N′ k} → ¬ Late′ N k → G N N′ k → G* N N′ (φ′ N k) → LanesEq k (lanes N) (lanes N′)
                      → (∀ {R} → holder (lanes N) k ≡ just R → Σ (Ev B) λ ev → TR (LaneRec.tab R) k ev × Unpinned ev)
                      → (holder (lanes N) k ≡ nothing → ¬ lateAt N k nothing → ¬ lateAt N′ k nothing)
                      → ¬ Late′ N′ k
      tabs-late-agree {N} {N′} {k} nl g g* es un src =
        late-eq (lastWith-eq hr hr′ (λ {R} {R′} E → rowAt-agree {m = LaneRec.tab R} {m′ = LaneRec.tab R′} {k = k} {y = k} (≼-refl {k}) (LaneEq.tab≈ E))
                             (λ {R} Q → rowAt-F {m = LaneRec.tab R} {k = k} {y = k} (≼-refl {k}) Q) (λ {R′} Q → rowAt-F {m = LaneRec.tab R′} {k = k} {y = k} (≼-refl {k}) Q) es)
                un src nl g g*
        where
          hr : LaneRec N → Bool
          hr R = rowAt (LaneRec.tab R) k
          hr′ : LaneRec N′ → Bool
          hr′ R = rowAt (LaneRec.tab R) k

      Put′ : ℕ → Pos → Pos → Set
      Put′ N y l with holder (lanes N) y
      ... | just R  = Σ Pos λ l′ → Rel.Put (Out.rel (LaneRec.lane R)) N y l′
                        × (l ≡ emitAt (l′ ⊕ [ sub (readerR (LaneRec.stE R)) ]) ⊎ l ≡ l′ ⊕ [ ix 0 ])
      ... | nothing = (Σ Pos λ l′ → Rel.Put (Out.rel Os) N y l′ × l ≡ l′ ⊕ [ sub c₁ ]) ⊎ ((Σ _ λ e → TR (P op N) y e) × l ≡ φ′ N y)

      -- Few rows put on one image: a lane's put through its lane's, a
      -- source's through the source's, any other a plain row.
      pb-few′ : ∀ N l → Σ (List Pos) λ ks → ∀ {k} → Put′ N k l → k ∈ ks
      pb-few′ N l = ks , λ {k} → go k
        where
          lk : LaneRec N → List Pos
          lk R = proj₁ (Rel.pb-few (Out.rel (LaneRec.lane R)) N (ups 5 l)) ++ proj₁ (Rel.pb-few (Out.rel (LaneRec.lane R)) N (up l))
          ks = L.concatMap lk (lanes N) ++ proj₁ (Rel.pb-few (Out.rel Os) N (up l)) ++ keys (P op N)
          go : ∀ k → Put′ N k l → k ∈ ks
          go k pt with holder (lanes N) k in eh
          go k (l′ , pu , inj₁ e) | just R =
            ∈-++⁺ˡ (∈-concatMap⁺ lk (any-map (λ { refl → ∈-++⁺ˡ (proj₂ (Rel.pb-few (Out.rel (LaneRec.lane R)) N (ups 5 l))
                                                          (subst (Rel.Put (Out.rel (LaneRec.lane R)) N k) (sym (trans (cong (ups 5) e) (emit-ups l′ _))) pu)) })
                                               (lastWith-∈ _ (lanes N) eh)))
          go k (l′ , pu , inj₂ e) | just R =
            ∈-++⁺ˡ (∈-concatMap⁺ lk (any-map (λ { refl → ∈-++⁺ʳ (proj₁ (Rel.pb-few (Out.rel (LaneRec.lane R)) N (ups 5 l)))
                                                          (proj₂ (Rel.pb-few (Out.rel (LaneRec.lane R)) N (up l))
                                                            (subst (Rel.Put (Out.rel (LaneRec.lane R)) N k) (sym (trans (cong up e) (up-⊕ l′ _))) pu)) })
                                               (lastWith-∈ _ (lanes N) eh)))
          go k (inj₁ (l′ , pu , e)) | nothing =
            ∈-++⁺ʳ (L.concatMap lk (lanes N)) (∈-++⁺ˡ (proj₂ (Rel.pb-few (Out.rel Os) N (up l)) (subst (Rel.Put (Out.rel Os) N k) (sym (trans (cong up e) (up-⊕ l′ _))) pu)))
          go k (inj₂ ((_ , x) , _)) | nothing =
            ∈-++⁺ʳ (L.concatMap lk (lanes N)) (∈-++⁺ʳ (proj₁ (Rel.pb-few (Out.rel Os) N (up l))) (in-keys x))

      -- Generous: every lane's preimages of the image stripped each way,
      -- the source's of it stripped, the markers', and the source's ends.
      bk′ : ℕ → Pos → List Pos
      bk′ N l = L.concatMap (λ R → let Rl = Out.rel (LaneRec.lane R) in
                                     Rel.bk Rl N (ups 5 l) ++ Rel.bk Rl N (ups 8 l) ++ L.map (λ k → k ⊕ [ ix 0 ]) (Rel.bk Rl N (ups 9 l))) (lanes N)
             ++ Rel.bk (Out.rel Os) N (up l)
             ++ L.map (λ k → k ⊕ [ ix 0 ]) (Rel.bk (Out.rel Os) N (ups 5 l))
             ++ endsOf (S N)
