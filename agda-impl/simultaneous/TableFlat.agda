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
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; [_]; _++_)
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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; does; yes; no)

open import Tree using (Obs; FlatOp; mergeᶠ; empty; of; flatMap; connect; connected)
open import denotation.Position using (Pos; Label; root; _≟ᵖ_; _<ᵖ_; ix; sub; last; inside; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; Unpinned; out; skip; end; pin; _≼_; _≺_)
open import denotation.Laws.Modulus using (≼-refl; ≼-trans; ≺→≼; ≺-ext; ≺-trans)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled.Exact.Base using (any⁻; any⁺; ends⁺; ends⁻; bind⁻; values⁺; pastRows⁺; complete)
open import Relation.Nullary.Decidable using (dec-true)
open import Data.Maybe.Properties using (just-injective)
open import simultaneous.TableRows using (merge-lane-out; lane-of; proper-in; rejoin-in; of-past; part-≺)
open import denotation.Laws.Worlds using (InvAt; PinBy; world-after)
open import quickcheck.Tabled using (hotOf; Row; rows; ends; anyᵇ; values; afterL; bind; lanes; past; rejoin)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Listing using (listC; listC-ok; listC-exact; UncutEnv)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.TableCorr using (Same; Rel; Corr; keys; in-keys; nl-ev)
open import simultaneous.TableKit using (TR; Got; got-bind)
open import simultaneous.Horizon using (Tag; module Cuts)
open import simultaneous.HorizonTree using (bd; BdEnv)
open import simultaneous.TreeBounded using (tree-bounded; listHot; admits-body; admits-trig)
open import simultaneous.Readings using (instantOf)
open import simultaneous.TableEnv using (Ren; wk; got-ok; pin-ok; after-ok; Tab; up; up-⊕; _⊕ˡ_; Linked; linked-l; linked-r;
  linked-r*; linked-later; inst-⊕ˡ; squeeze; ⊑-⊕ˡ; Aligned; aligned-⊕; aligned-past;
  aligned-r*; Rest; Out; out; SameBd; EnvR; maps; lw; lw*; unended; den; den-ex; dbd; env-wk; Holds; Admits; admits-step;
  admits-ix; admits-row; den-cons; HotD; DenOf; tab-func;
  tab-flat; tab-at)

open import simultaneous.ElabUndone using (elab-undone)
open import simultaneous.LaneEndSched using (laneXt; laneL; laneX; readerR; emitAt; tr-in; module Share)
open import simultaneous.LaneEnd using (corr-end; module Lane)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; elab; each; laneˢ; laneSrc; srcLane; closer; combined; trackers)

≟-true : ∀ x y → does (x ≟ᵖ y) ≡ true → x ≡ y
≟-true x y with x ≟ᵖ y
... | yes e = λ _ → e
... | no _  = λ ()

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

  endAt-I : ∀ {X : Set} (m : Maybe (Tb.Listed X)) {y} → TR m y end → endAt m y ≡ true
  endAt-I nothing (_ , () , _)
  endAt-I (just Lx) {y} (_ , refl , m) = any⁺ {p = λ k → does (k ≟ᵖ y)} (ends⁺ m) (dec-true (y ≟ᵖ y) refl)

  -- An end listed among a table's ends is a row.
  ends-tr : ∀ {X : Set} (m : Maybe (Tb.Listed X)) {c} → c ∈ endsOf m → TR m c end
  ends-tr nothing   ()
  ends-tr (just Lx) c∈ = Lx , refl , ends⁻ {rs = rows Lx} c∈

  endAt-E : ∀ {X : Set} (m : Maybe (Tb.Listed X)) {y} → endAt m y ≡ true → TR m y end
  endAt-E m h = ends-tr m (any-≟ h)

  skip≢end : ∀ {X : Set} → ¬ (skip {X} ≡ end)
  skip≢end ()

  rowAt : ∀ {X : Set} → Maybe (Tb.Listed X) → Pos → Bool
  rowAt nothing   y = false
  rowAt (just Lx) y = anyᵇ (λ r → does (proj₁ r ≟ᵖ y)) (rows Lx)

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

  -- A value of the source at a row.
  isVal : ℕ → Pos → Bool
  isVal N y = anyᵇ (λ v → does (ValAt.q v ≟ᵖ y)) (valsAt N)

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
  core op = flatMap op (λ a → laneˢ (λ k c → laneSrc ρι⁴ (f a) k c)) (each valuesOf (connected (there (here refl))))

  inner : FlatOp → Obs Timeline (IE B ∷ IE A ∷ ⊤ ∷ Δ) (IE B)
  inner op = connect (core op) (combined op (trackers Γ 0 (wk (wk (wk (wk ρι))))))

  body : FlatOp → Obs Timeline (IE A ∷ ⊤ ∷ Δ) (IE B)
  body op = connect closer (inner op)

  shared : Obs Timeline (⊤ ∷ Δ) (IE A)
  shared = flatMap (mergeᶠ (just 1)) (λ c → srcLane ρι s c) (of (true ∷ false ∷ []))

  ----------------------------------------------------------------------
  -- Their subscriptions and hots

  -- The share's body, the closer's body, the combined connect, and the
  -- lanes' flatMap.
  c₃ c₂ c₁ c₀ : Pos
  c₃ = p* ⊕ [ ix 0 ] ⊕ [ ix 0 ]
  c₂ = c₃ ⊕ [ ix 0 ]
  c₁ = c₂ ⊕ [ ix 1 ]
  c₀ = c₂ ⊕ [ ix 0 ]

  -- The source's elaborated subscription: queued behind the blocker,
  -- which ends on the trigger's end.
  sp* : Pos
  sp* = p* ⊕ˡ (ix 1 ∷ last ∷ sub (p* ⊕ˡ (ix 0 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ [])) ∷ ix 1 ∷ [])

  tt-tab : ℕ → Tb.Listed ⊤
  tt-tab N = hotOf (proj₁ (listC-ok (3 + N) n (empty {A = ⊤}) (uρ* N) (p* ⊕ [ ix 1 ])))

  ρ*s : ℕ → All Tb.Listed (⊤ ∷ Δ)
  ρ*s N = tt-tab N ∷ ρ* N

  uρ*s : ∀ N → UncutEnv (ρ*s N)
  uρ*s N = proj₂ (proj₂ (listC-ok (3 + N) n (empty {A = ⊤}) (uρ* N) (p* ⊕ [ ix 1 ]))) , uρ* N

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
  ttD = listHot n (empty {A = ⊤}) uρ* (lw* env) p* ad*

  Ds : DenOf ρ*s
  Ds = den-cons ttD (lw* env)

  ad₄ : Admits Ds (p* ⊕ [ ix 0 ])
  ad₄ = admits-body n (empty {A = ⊤}) uρ* (lw* env) p* ad*

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

  -- The source, at the share's subscription.
  Src : Set₁
  Src = Out n s ρ uρ (wk ρι) ρ*s uρ*s (maps env) (lw env) Ds p sp*

  -- Each lane, wherever subscribed alike, whatever the four binders hold.
  Lanes : Set₁
  Lanes = ∀ a (t₁ : ℕ → Tb.Listed ⊤) (t₂ : ℕ → Tb.Listed (IE B)) (t₃ : ℕ → Tb.Listed (IE A)) (t₄ : ℕ → Tb.Listed ⊤)
        → (u : ∀ N → UncutEnv (t₁ N ∷ t₂ N ∷ t₃ N ∷ t₄ N ∷ ρ* N))
        → (h₁ : HotD t₁) (h₂ : HotD t₂) (h₃ : HotD t₃) (h₄ : HotD t₄)
        → Holds n (f a) ρ uρ ρι⁴ (λ N → t₁ N ∷ t₂ N ∷ t₃ N ∷ t₄ N ∷ ρ* N) u (env-wk h₁ (env-wk h₂ (env-wk h₃ (env-wk h₄ env))))

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

  postulate
    -- THE UNPINNED FLATMAP HANGS WHERE THE FLATMAP DOES: a source's pin
    -- shown as a skip stays at its position.
    pd-bounded : ∀ {op} {Bd : ℕ → Pos → Tag → Set} → Cuts.Bounded (λ N → TR (P op N)) Bd → Cuts.Bounded (λ N → TR (Pd op N)) Bd

  -- THE FLATMAP'S HANGS are its tree's, and the unpinned flatMap's with them.
  jbd : FlatOp → ℕ → Pos → Tag → Set
  jbd op = bd n (flatMap op f s) ρ uρ (dbd (lw env)) p

  jtree : ∀ op → Cuts.Bounded (λ N → TR (P op N)) (jbd op)
  jtree op = tree-bounded n (flatMap op f s) ρ uρ (lw env) p ad

  jbounded : ∀ op → Cuts.Bounded (λ N → TR (Pd op N)) (jbd op)
  jbounded op = pd-bounded {op} (jtree op)

  -- THE LANES' FLATMAP'S HANGS are its tree's, in the closer's scope.
  jbd* : FlatOp → ℕ → Pos → Tag → Set
  jbd* op = bd n (core op) ρ*c uρ*c (dbd Dc) c₁

  jbounded* : ∀ op → Cuts.Bounded (λ N → TR (listC (3 + N) n (core op) (ρ*c N) c₁)) (jbd* op)
  jbounded* op = tree-bounded n (core op) ρ*c uρ*c Dc c₁ ad₁

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
          → Rel (Pd op) (λ N → listC (3 + N) n (core op) (ρ*c N) c₁) p c₁

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
    trig st N = hotOf (proj₁ (listC-ok (3 + N) n (empty {A = ⊤}) {ρ*c N} (uρ*c N) (laneL st ⊕ [ ix 1 ])))

    utrig : ∀ st N → UncutEnv (trig st N ∷ ρ*c N)
    utrig st N = proj₂ (proj₂ (listC-ok (3 + N) n (empty {A = ⊤}) {ρ*c N} (uρ*c N) (laneL st ⊕ [ ix 1 ]))) , uρ*c N

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

    -- An elaborated source value is the child's, which the share shows,
    -- and, quiet past its end, keeps.
    shared-row : ∀ {N k x′} → TR (Tab n s* ρ*s sp* N) k (out x′) → sp* ≺ k → (k , out x′) ∈ rows (sh-tab N)
    shared-row {N} {k} {x′} y sk = proper-in (rows (shL N)) r λ cm lt → noPin (InvAt.quiet Ish (shL N , shL-eq N , cm) (shL N , shL-eq N , r) lt)
      where
        Ish = tab-at n shared uρ*s Ds (admits-step Ds ad₄) N
        module SS = Share n (λ c → srcLane ρι s c) refl uρ* (lw* env) p* ad* N
        r : (k , out x′) ∈ rows (shL N)
        r = complete (listC-exact (3 + N) n shared (den-ex Ds N) shp (shL-eq N) (proj₂ (proj₂ (listC-ok (3 + N) n shared {ρ*s N} (uρ*s N) shp))))
              (SS.share-out (tr-in (3 + N) n s* {ρ*s N} (den-ex Ds N) (uρ*s N) sp* y) sk)
        noPin : ∀ {c} → PinBy c (out x′) → ⊥
        noPin (_ , () , _)

    -- A value the shared hot keeps past the lanes' flatMap's subscription
    -- is listed by `each` one lane down.
    opaque
      each-at : ∀ {N k x′ a} → (k , out x′) ∈ rows (sh-tab N) → c₁ ≺ k → valuesOf x′ ≡ a ∷ []
              → TR (Tab n eachS ρ*c c₁ N) (k ⊕ˡ (sub c₁ ∷ ix 1 ∷ ix 0 ∷ [])) (out a)
      each-at {N} {k} {x′} {a} r ck rd =
        let ls , els , e₂ = bind⁻ {m = lanes (afterL (λ x → listC (3 + N) n (of (valuesOf x)) (ρ*c N))) (values (rows (rejoin c₁ (sh-tab N))))} (proj₁ (proj₂ (okE N)))
        in proj₁ (okE N) , proj₁ (proj₂ (okE N)) , subst (λ L → _ ∈ rows L) (just-injective e₂)
              (merge-lane-out (rejoin c₁ (sh-tab N)) ls (lane-of {ln = afterL (λ x → listC (3 + N) n (of (valuesOf x)) (ρ*c N))} els (values⁺ (rejoin-in c₁ (sh-tab N) r ck)) refl) (of-past (k ⊕ [ sub c₁ ] ⊕ [ ix 1 ]) (valuesOf x′) rd))

    -- THE READER'S ROWS: each value of the source is the elaborated
    -- source's value at its image, which the shared flatMap keeps; the
    -- lanes' flatMap reads it under its subscription.
    each-row : ∀ {N q a} → TR (S N) q (out a) → TR (Tab n eachS ρ*c c₁ N) (val* N q) (out a)
    each-row {N} {q} {a} x with Corr.row→ (Rel.corr (Out.rel Os) N) x tt
    ... | inj₂ (() , _)
    ... | inj₁ ((e′ , y , mt) , _) with proj₁ mt tt
    ...   | x′ , refl , rd = each-at (shared-row y sk) (≺-trans {c₁} {sp*} (part-≺ p* (ix 0 ∷ ix 0 ∷ ix 1 ∷ []) (last ∷ sub (p* ⊕ˡ (ix 0 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ [])) ∷ ix 1 ∷ []) refl) sk) rd
      where
        Isp = tab-at n s* uρ*s Ds (admits-trig n uρ* (lw* env) p* ad*) N
        sk : sp* ≺ Rel.φ (Out.rel Os) N q
        sk = world-after (InvAt.world Isp y) (InvAt.real Isp y)

    -- A lane's trigger, listed off its lawful source, and the lane's
    -- elaborated subscription admissible under it.
    trigD : ∀ st → Admits Dc st → HotD (trig st)
    trigD st a = listHot n (empty {A = ⊤}) uρ*c Dc (laneL st) (admits-ix Dc 1 (admits-ix Dc 0 a))

    laneAdm : ∀ st (a : Admits Dc st) → Admits (den-cons (trigD st a) Dc) (laneX st)
    laneAdm st a = admits-trig n uρ*c Dc (laneL st) (admits-ix Dc 1 (admits-ix Dc 0 a))

    -- A lane's hots, opaque: the record's field type naming `trigD`
    -- exhausts the heap.
    opaque
      laneDen : ∀ st → Admits Dc st → DenOf (λ N′ → trig st N′ ∷ ρ*c N′)
      laneDen st a = den-cons (trigD st a) Dc

    opaque
      unfolding laneDen
      laneDen-pin : ∀ st (a : Admits Dc st) {Bx : ℕ → Pos → Tag → Set} (F : BdEnv (⊤ ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ) → ℕ → Pos → Tag → Set)
                  → SameBd Bx (F (dbd (den-cons (trigD st a) Dc))) → SameBd Bx (F (dbd (laneDen st a)))
      laneDen-pin st a F x = x

    -- A lane's record, its hots named opaquely.
    to-lane : ∀ {a′ st stE} (adm* : Admits Dc stE)
            → Out n (f a′) ρ uρ ρι⁴ (λ N′ → trig stE N′ ∷ ρ*c N′) (utrig stE) (maps env) (lw env) (den-cons (trigD stE adm*) Dc) st (laneX stE)
            → Out n (f a′) ρ uρ ρι⁴ (λ N′ → trig stE N′ ∷ ρ*c N′) (utrig stE) (maps env) (lw env) (laneDen stE adm*) st (laneX stE)
    to-lane {a′} {st} {stE} adm* O =
      out (Out.rel O) (Out.rest O) (Out.bd-pin O)
        (laneDen-pin stE adm* (λ β → bd n (elab ρι⁴ (f a′)) (λ N′ → trig stE N′ ∷ ρ*c N′) (utrig stE) β (laneX stE)) (Out.bd-pin* O))

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
        lane : Out n (f a) ρ uρ ρι⁴ (λ N′ → trig stE N′ ∷ ρ*c N′) (utrig stE) (maps env) (lw env) (laneDen stE adm*) st (laneX stE)

      -- The lane's plain tables.
      tab : Maybe (Tb.Listed B)
      tab = Tab n (f a) ρ st N

      -- Its row's image as the lanes' flatMap shows it: read by
      -- `laneˢ`'s reader and emitted by `counted`; an end at its
      -- `laneDone`'s, which follows the share's end, the lane's own.
      outImage endImage : Pos → Pos
      outImage y = emitAt (Rel.φ (Out.rel lane) N y ⊕ [ sub (readerR stE) ])
      endImage y = emitAt (Rel.φ (Out.rel lane) N y ⊕ˡ (sub (readerR stE) ∷ ix 1 ∷ ix 0 ∷ [])) ⊕ [ last ]

    -- A lane's end is never late.
    end-nl : ∀ {N} (R : LaneRec N) {c} → TR (LaneRec.tab R) c end → ¬ Rel.Late (Out.rel (LaneRec.lane R)) N c
    end-nl {N} R cx = nl-ev (Rel.corr (Out.rel (LaneRec.lane R)) N) cx (λ ())

    -- THE ELABORATED LANE'S END: where `laneˢ` shows the lane's end, its
    -- `laneDone` taken by the take.
    lane-end-image : ∀ {N} (R : LaneRec N) {c} → TR (LaneRec.tab R) c end
                   → TR (Tab n (laneˢ (λ k c′ → laneSrc ρι⁴ (f (LaneRec.a R)) k c′)) ρ*c (LaneRec.stE R) N) (LaneRec.endImage R c) end
    lane-end-image {N} R {c} cx = Lane.lane-end n ρι⁴ (f (LaneRec.a R)) uρ*c Dc (LaneRec.stE R) (LaneRec.adm* R) N
                     (λ h → elab-undone (3 + N) n ρι⁴ (f (LaneRec.a R)) (h ∷ den Dc N) (λ i → unended env N i))
                     {t = trig (LaneRec.stE R) N} {o′ = laneˢ (λ k c′ → laneSrc ρι⁴ (f (LaneRec.a R)) k c′)} {q = LaneRec.endImage R c}
                     {e = Rel.φ (Out.rel (LaneRec.lane R)) N c} refl refl refl
                     (corr-end (Rel.corr (Out.rel (LaneRec.lane R)) N) cx)

    end-cuts : ∀ {N} (R : LaneRec N) {c} → TR (LaneRec.tab R) c end → Aligned (maps env) ρ c (Rel.φ (Out.rel (LaneRec.lane R)) N c)
    end-cuts {N} R {c} cx = Rest.cuts (Out.rest (LaneRec.lane R)) N cx tt

    end-linked : ∀ {N} (R : LaneRec N) {c} → TR (LaneRec.tab R) c end → Linked c (Rel.φ (Out.rel (LaneRec.lane R)) N c)
    end-linked {N} R {c} cx = Rest.linked (Out.rest (LaneRec.lane R)) N cx tt (end-nl R cx)

    -- A value's lane, subscribed under its row: the source's facts at the
    -- row align the lane's pair.
    valRec : ∀ N → ValAt N → LaneRec N
    valRec N (valAt q a x) = laneRec a (q ⊕ [ ix 1 ]) st alL ad₀ ad₀* (to-lane ad₀* (
      Ls a (trig st) cl-tab sh-tab tt-tab (utrig st) (trigD st ad₀*) clD shD ttD (q ⊕ [ ix 1 ]) (laneX st) ad₀ (laneAdm st ad₀*)
         (aligned-r* {Ψ = maps env} {ρ = ρ} alL (laneXt st))
         (linked-r* (linked-r (linked-l (Rest.linked (Out.rest Os) N x tt nlx) (ix 1)) (sub c₁)) ys)))
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
    queuedRec N R {c} cx a = laneRec a (c ⊕ [ ix 1 ]) st alL ad₀ ad₀* (to-lane ad₀* (
      Ls a (trig st) cl-tab sh-tab tt-tab (utrig st) (trigD st ad₀*) clD shD ttD (c ⊕ [ ix 1 ]) (laneX st) ad₀ (laneAdm st ad₀*)
         (aligned-r* {Ψ = maps env} {ρ = ρ} alL (laneXt st))
         (linked-r* (linked-r (linked-l (end-linked R cx) (ix 1)) (sub r)) ys)))
      where
        r  = readerR (LaneRec.stE R)
        st = LaneRec.endImage R c ⊕ [ ix 1 ]
        ad₀ : Admits (lw env) (c ⊕ [ ix 1 ])
        ad₀ = admits-row n (f (LaneRec.a R)) uρ (lw env) (LaneRec.adm R) cx
        ad₀* : Admits Dc st
        ad₀* = admits-row n (laneˢ (λ k c′ → laneSrc ρι⁴ (f (LaneRec.a R)) k c′)) uρ*c Dc (LaneRec.adm* R) (lane-end-image R cx)
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

    -- A source row's image, read through the shared hot.
    srcφ : ℕ → Pos → Pos
    srcφ N k = Rel.φ (Out.rel Os) N k ⊕ [ sub c₁ ]

    -- THE MERGES' MAP, given each cut's lanes.  A lane row is imaged
    -- through its lane's record at the cut, a lane's put also where
    -- `laneˢ`'s share shows the lane's row, so its pins; the skip a queue leaves past a
    -- lane's end at its end image's; a value's marker at the marker of its
    -- elaborated value; any source row through the shared hot, which
    -- ends where the source does.
    module Tabs (op : FlatOp) (lanes : ∀ N → List (LaneRec N)) where
      -- A row's image, given the lane holding it and the lane ending just
      -- above it.
      rowφ : ∀ N → Pos → Maybe (LaneRec N) → Maybe (LaneRec N) → Pos
      rowφ N y (just R) _        = if endAt (LaneRec.tab R) y then LaneRec.endImage R y else LaneRec.outImage R y
      rowφ N y nothing  (just R) = LaneRec.endImage R (up y) ⊕ [ ix 0 ]
      rowφ N y nothing  nothing  = if isMarker N y then val* N (up y) ⊕ [ ix 0 ]
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
