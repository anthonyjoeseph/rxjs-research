{-# OPTIONS --guardedness #-}

-- A COLD'S STEP MAKES FEW ROWS (`cold-step-few`).  Each row of the
-- elaborated cold lies under its subscription, or in an instant fired by
-- a timer made under it or under such an instant (`Fresh`), at one of a
-- few paths (`Place`).  A begin is rendered under a value the scan reads
-- past the tick, and every value of the subscribe instant lies before the
-- tick, so a begin's instant is a fired one: none of its rows lies under
-- the subscription, and they sit at those few paths.
module simultaneous.ColdFew where

open import Data.Bool using (Bool; true; false; T; _∨_; if_then_else_)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; _+_; s≤s; z≤n)
open import Data.Nat.Properties using (<-irrefl; m<n⇒m<1+n; ≤-reflexive; <-trans; ≤-trans; +-monoʳ-≤; +-monoʳ-<; n<1+n; m<m+n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import Tree using (mergeᶠ; cold; of; map)
open import denotation.Position using (Pos; Instant; Label; Path; ix; last; root; frame; cascade; _∙_; _⊕_; _≟ᵖ_; instant; path; nested; fired)
  renaming (tick to tickᵖ)
open import denotation.Events using (Timeline; fresh; From; done; quiet; at; Frame; emit; stall; close; Frame∞; From∞; frames; burst; start; timelineAt; ofᴱ; <ᵖ-part; ix-<)
open import denotation.EmissionSet using (EmissionSet; Den; DenEnv; enter; Ev; out; skip; end; InE; at-out; at-skip; at-end; on-out; on-skip;
  _≺_; _≼_; Truncate; map-out; map-skip; map-pin; map-end; module Op; module Joining;
  module Values; module Bounded; module Merge; module Scan)
open import denotation.Laws.Modulus using (≺-trans; ≼-refl; ≺→≼; ≺-irrefl)
open import denotation.Laws.Worlds using (_⊑_; ⊑-trans; ⊕-assoc)
open import denotation.Laws.Worlds.Leaves using (of-reach; of-idx; ine-pin)
open import denotation.Laws.Cut using (ix-asc)
open import denotation.Laws.Nth using (module Nths)
open import simultaneous.HeldComb using (ev)
open import simultaneous.SObs using (lone; Tag; val; cdone; tick; module Elaborate)
open import simultaneous.InstEmit using (instEmit; mark; value; begin; over)
open import simultaneous.Readings using (rootOf)
open import simultaneous.CombSent using (assoc³)
open import denotation.Laws.Truth using (instant-⊑)
open import simultaneous.Instants using (past-tick)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; coldˢ; render; phase; concatˢ)

------------------------------------------------------------------------
-- Instants fired under a position

mutual
  depth : Pos → ℕ
  depth (i ∙ _) = depthⁱ i

  depthⁱ : Instant → ℕ
  depthⁱ frame           = 0
  depthⁱ (cascade _ e _) = suc (depth e)

-- An instant whose timer was made under `s`, or in such an instant, and
-- fires at a later tick.
data Fresh (s : Pos) : Instant → Set where
  fresh₀ : ∀ {t e l} → s ⊑ e → tickᵖ e < t → Fresh s (cascade t e l)
  fresh₁ : ∀ {t e l} → Fresh s (instant e) → tickᵖ e < t → Fresh s (cascade t e l)

⊑-depth : ∀ {x y} → x ⊑ y → depth y ≡ depth x
⊑-depth {_ ∙ _} (_ , refl) = refl

fresh-deep : ∀ {s I} → Fresh s I → depth s < depthⁱ I
fresh-deep (fresh₀ u _)             = s≤s (≤-reflexive (sym (⊑-depth u)))
fresh-deep (fresh₁ {e = _ ∙ _} f _) = m<n⇒m<1+n (fresh-deep f)

-- No instant is fired under a position of its own.
fresh-self : ∀ {s} → Fresh s (instant s) → ⊥
fresh-self {_ ∙ _} f = <-irrefl refl (fresh-deep f)

fresh-⊑ : ∀ {s s′ I} → s ⊑ s′ → Fresh s′ I → Fresh s I
fresh-⊑ u (fresh₀ v h) = fresh₀ (⊑-trans u v) h
fresh-⊑ u (fresh₁ f h) = fresh₁ (fresh-⊑ u f) h

tick-⊑ : ∀ {x y} → x ⊑ y → tickᵖ y ≡ tickᵖ x
tick-⊑ {frame ∙ _}         (_ , refl) = refl
tick-⊑ {cascade _ _ _ ∙ _} (_ , refl) = refl

tickⁱ : Instant → ℕ
tickⁱ frame           = 0
tickⁱ (cascade t _ _) = t

-- A fresh instant fires past its subscription's tick, so after every row
-- under it.
fresh-tick : ∀ {s I} → Fresh s I → tickᵖ s < tickⁱ I
fresh-tick (fresh₀ u h)                       = subst (_< _) (tick-⊑ u) h
fresh-tick (fresh₁ {e = cascade _ _ _ ∙ _} f h) = <-trans (fresh-tick f) h

fresh-past : ∀ {s x y} → s ⊑ x → Fresh s (instant y) → x ≺ y
fresh-past {s} {x} {cascade t e l ∙ q} u f = past-tick x (subst (_< t) (sym (tick-⊑ u)) (fresh-tick f))

⊑₂ : ∀ s a b → s ⊑ ((s ⊕ [ a ]) ⊕ [ b ])
⊑₂ s a b = a ∷ b ∷ [] , ⊕-assoc s [ a ] [ b ]

------------------------------------------------------------------------
-- Where a row lies: under the subscription, or at one of a few paths of
-- a fired instant

Place : List Path → Pos → Pos → Set
Place Zs s y = s ⊑ y ⊎ (path y ∈ Zs × Fresh s (instant y))

pl-wk : ∀ {Zs Zs′ s y} → (∀ {z} → z ∈ Zs → z ∈ Zs′) → Place Zs s y → Place Zs′ s y
pl-wk w (inj₁ u)       = inj₁ u
pl-wk w (inj₂ (m , f)) = inj₂ (w m , f)

pl-up : ∀ {Zs s s′ y} → s ⊑ s′ → Place Zs s′ y → Place Zs s y
pl-up v (inj₁ u)       = inj₁ (⊑-trans v u)
pl-up v (inj₂ (m , f)) = inj₂ (m , fresh-⊑ v f)

pl-ext : ∀ {Zs s y} w → Place Zs s y → Place (L.map (_++ w) Zs) s (y ⊕ w)
pl-ext {y = _ ∙ _} w (inj₁ u)       = inj₁ (⊑-trans u (w , refl))
pl-ext {y = _ ∙ _} w (inj₂ (m , f)) = inj₂ (∈-map⁺ (_++ w) m , f)

------------------------------------------------------------------------
-- The leaves

One : List Path
One = [] ∷ []

-- A cold leaf's rows: under its subscription, or one apiece in an instant
-- its timers fire, a value or skip at an indexed label, the end at the
-- last.
data Fired {A : Set} (s : Pos) : Pos → Ev A → Set where
  f-out  : ∀ {T e i a} → Fresh s (cascade T e (ix i)) → Fired s (cascade T e (ix i) ∙ []) (out a)
  f-skip : ∀ {T e i} → Fresh s (cascade T e (ix i)) → Fired s (cascade T e (ix i) ∙ []) skip
  f-end  : ∀ {T e} → Fresh s (cascade T e last) → Fired s (cascade T e last ∙ []) end

Leaf : ∀ {A} → Pos → Pos → Ev A → Set
Leaf s y e = s ⊑ y ⊎ Fired s y e

leaf-pl : ∀ {A s y} {e : Ev A} → Leaf s y e → Place One s y
leaf-pl (inj₁ u)          = inj₁ u
leaf-pl (inj₂ (f-out f))  = inj₂ (here refl , f)
leaf-pl (inj₂ (f-skip f)) = inj₂ (here refl , f)
leaf-pl (inj₂ (f-end f))  = inj₂ (here refl , f)

-- A timer made where the leaf ends fires a fresh instant.
lf-fire : ∀ {A s e t l} → Leaf {A} s e end → tickᵖ e < t → Fresh s (cascade t e l)
lf-fire (inj₁ u)         h = fresh₀ u h
lf-fire (inj₂ (f-end f)) h = fresh₁ f h

last-tick : ∀ s → tickᵖ (s ⊕ [ last ]) < tickᵖ s + 1
last-tick s = subst (_< tickᵖ s + 1) (sym (tick-⊑ {s} ([ last ] , refl))) (m<m+n (tickᵖ s) (s≤s z≤n))

-- Each later frame fires its own instant.
mutual
  frames-lf : ∀ {A t} s τ e (m : From A t) {y ev} → Leaf {A} s e end → tickᵖ e < τ + t → InE (frames τ e m) y ev → Leaf s y ev
  frames-lf s τ e done         pe h at-end = pe
  frames-lf s τ e quiet        pe h ()
  frames-lf s τ e (at t′ le b) pe h x      = burst-lf s τ e 0 b (lf-fire pe (≤-trans h (+-monoʳ-≤ τ le))) x

  burst-lf : ∀ {A t} s τ e i (b : Frame A t) {y ev} → (∀ {l} → Fresh s (cascade (τ + t) e l)) → InE (burst τ (fired (τ + t) e) i b) y ev → Leaf s y ev
  burst-lf s τ e i (emit _ k) fr at-out      = inj₂ (f-out fr)
  burst-lf s τ e i (emit _ k) fr (on-out x)  = burst-lf s τ e (suc i) k fr x
  burst-lf s τ e i (stall k)  fr at-skip     = inj₂ (f-skip fr)
  burst-lf s τ e i (stall k)  fr (on-skip x) = burst-lf s τ e (suc i) (Frame∞.force k) fr x
  burst-lf s τ e i (close k)  fr at-skip     = inj₂ (f-skip fr)
  burst-lf {t = t} s τ e i (close k) fr (on-skip x) =
    frames-lf s τ (cascade (τ + t) e last ∙ []) (From∞.force k) (inj₂ (f-end fr)) (+-monoʳ-< τ (n<1+n t)) x

-- Its subscribe frame lies under the subscription.
nested-lf : ∀ {A} s i (b : Frame A 0) {y ev} → InE (burst (tickᵖ s) (nested s) i b) y ev → Leaf s y ev
nested-lf s i (emit _ k) at-out      = inj₁ (_ , refl)
nested-lf s i (emit _ k) (on-out x)  = nested-lf s (suc i) k x
nested-lf s i (stall k)  at-skip     = inj₁ (_ , refl)
nested-lf s i (stall k)  (on-skip x) = nested-lf s (suc i) (Frame∞.force k) x
nested-lf s i (close k)  at-skip     = inj₁ (_ , refl)
nested-lf s i (close k)  (on-skip x) = frames-lf s (tickᵖ s) (s ⊕ [ last ]) (From∞.force k) (inj₁ (_ , refl)) (last-tick s) x

start-lf : ∀ {A} s (m : From A 0) {y ev} → InE (start s m) y ev → Leaf s y ev
start-lf s done              at-end = inj₁ (_ , refl)
start-lf s quiet             ()
start-lf s (at zero _ b)     x      = nested-lf s 0 b x
start-lf s (at (suc t) le b) x      = frames-lf {t = 1} s (tickᵖ s) (s ⊕ [ last ]) (at (suc t) (s≤s z≤n) b) (inj₁ (_ , refl)) (last-tick s) x

cold-pl : ∀ {A} (c : Timeline A) s {y ev} → InE (start s (timelineAt c s)) y ev → Place One s y
cold-pl c s x = leaf-pl (start-lf s (timelineAt c s) x)

-- The rows of `of`.
of-below : ∀ {X} p i (ys : List X) {y e} → InE (ofᴱ p i ys) y e → p ⊑ y
of-below p i ys x with of-idx p i ys x
... | inj₁ (j , _ , eq) = [ ix j ] , eq
... | inj₂ eq           = [ last ] , eq

-- Where a render's rows lie, under its subscription.
RZ : List Path
RZ = (ix 0 ∷ []) ∷ (ix 1 ∷ []) ∷ (last ∷ []) ∷ (ix 0 ∷ ix 0 ∷ []) ∷ (ix 0 ∷ ix 1 ∷ ix 0 ∷ []) ∷ (ix 0 ∷ ix 1 ∷ ix 1 ∷ [])
   ∷ (ix 0 ∷ ix 1 ∷ ix 2 ∷ []) ∷ (ix 0 ∷ ix 1 ∷ last ∷ []) ∷ []

Rendered : Pos → Pos → Set
Rendered s y = Σ Path λ w → w ∈ RZ × y ≡ s ⊕ w

Mint : Timeline Pos
Mint = fresh (λ p → p)

mint-in : ∀ s {y ev} → InE (start s (timelineAt Mint s)) y ev → Rendered s y
mint-in s at-out                   = _ , here refl , refl
mint-in s (on-out at-skip)         = _ , there (here refl) , refl
mint-in s (on-out (on-skip at-end)) = _ , there (there (here refl)) , refl

mint-out : ∀ s {y v} → InE (start s (timelineAt Mint s)) y (out v) → y ≡ s ⊕ [ ix 0 ]
mint-out s at-out = refl
mint-out s (on-out (on-skip ()))

one-in : ∀ {X : Set} s (v : X) {y ev} → InE (ofᴱ s 0 (v ∷ [])) y ev → Rendered s y
one-in s v at-out          = _ , here refl , refl
one-in s v (on-out at-end) = _ , there (there (here refl)) , refl

three-in : ∀ {X : Set} s (a b c : X) {y ev} → InE (ofᴱ ((s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) 0 (a ∷ b ∷ c ∷ [])) y ev → Rendered s y
three-in s a b c at-out                            = _ , there (there (there (there (here refl)))) , assoc³ s (ix 0) (ix 1) (ix 0)
three-in s a b c (on-out at-out)                   = _ , there (there (there (there (there (here refl))))) , assoc³ s (ix 0) (ix 1) (ix 1)
three-in s a b c (on-out (on-out at-out))          = _ , there (there (there (there (there (there (here refl)))))) , assoc³ s (ix 0) (ix 1) (ix 2)
three-in s a b c (on-out (on-out (on-out at-end))) = _ , there (there (there (there (there (there (there (here refl))))))) , assoc³ s (ix 0) (ix 1) last

-- A value's step: begin, value and over under each name minted.
rv-in : ∀ {A : Set} (a : A) s {y ev}
      → enter (Op.flatMap (mergeᶠ nothing) (λ n → Op.of (instEmit (mark begin) n ∷ instEmit (value a) n ∷ instEmit (mark over) n ∷ [])) (Op.cold Mint)) s y ev
      → Rendered s y
rv-in a s (Joining.val (x , _) , _) with mint-out s x
... | refl = _ , there (there (there (here refl))) , ⊕-assoc s [ ix 0 ] [ ix 0 ]
rv-in a s (Joining.step (x , _) , _)    = mint-in s x
rv-in a s (Joining.opin (x , _) , _)    = mint-in s x
rv-in a s (Joining.oend (x , _) _ , _)  = mint-in s x
rv-in a s (Joining.opass (x , _) _ , _) = mint-in s x
rv-in a s (Joining.lane (x , _) _ ((l , _) , _) _ _ , _) with mint-out s x
... | refl = three-in s _ _ _ l
rv-in a s (Joining.lend (x , _) _ ((l , _) , _) _ _ _ , _) with mint-out s x
... | refl = three-in s _ _ _ l
rv-in a s (Joining.lpass (x , _) _ ((l , _) , _) _ _ _ , _) with mint-out s x
... | refl = three-in s _ _ _ l
rv-in a s (Joining.hand _ _ _ _ () , _)
rv-in a s (Joining.left _ _ ((l , _) , _) _ _ , _) = ⊥-elim (ine-pin l)
rv-in a s (Joining.run () _ , _)
rv-in a s (Joining.rend () _ _ , _)
rv-in a s (Joining.rpass () _ _ , _)
rv-in a s (Joining.rhand () _ , _)

-- A completion's step: a begin for the name minted.
cd-in : ∀ {A : Set} s {y ev} → enter (Op.map (λ n → instEmit {A = A} (mark begin) n) (Op.cold Mint)) s y ev → Rendered s y
cd-in s (map-out (x , _) , _)  = mint-in s x
cd-in s (map-skip (x , _) , _) = mint-in s x
cd-in s (map-pin (x , _) , _)  = mint-in s x
cd-in s (map-end (x , _) , _)  = mint-in s x

em-in : ∀ {X : Set} s {y ev} → enter (Op.empty {X}) s y ev → Rendered s y
em-in s (at-end , _) = _ , there (there (here refl)) , refl

-- What a render shows a begin for: a late value or completion.
Late : ∀ {A} → Bool × Tag A → Set
Late (true , val _) = ⊤
Late (true , cdone) = ⊤
Late _              = ⊥

Ticks : ∀ {A} → Ev (Tag A) → Set
Ticks (out tick) = ⊤
Ticks (out _)    = ⊥
Ticks _          = ⊤

Tickless : ∀ {A} → Ev (Tag A) → Set
Tickless (out tick) = ⊥
Tickless _          = ⊤

late-on : ∀ {A} (x : Bool × Tag A) → Late x → T (proj₁ x)
late-on (true , val _) _ = tt
late-on (true , cdone) _ = tt

late-tick : ∀ {A} (x : Bool × Tag A) → Late x → Ticks (out (proj₂ x)) → ⊥
late-tick (true , val _) _ ()
late-tick (true , cdone) _ ()

T∨f : ∀ x → T (x ∨ false) → T x
T∨f true  _ = tt
T∨f false ()

∈-cm : ∀ {X Y : Set} (f : X → List Y) {x y} xs → x ∈ xs → y ∈ f x → y ∈ L.concatMap f xs
∈-cm f (x ∷ xs) (here refl) m = ∈-++⁺ˡ m
∈-cm f (x ∷ xs) (there i)   m = ∈-++⁺ʳ (f x) (∈-cm f xs i m)

-- Two positions under consecutive children part in their order.
sep : ∀ p {a b} → (p ⊕ [ ix 0 ]) ⊑ a → (p ⊕ [ ix 1 ]) ⊑ b → a ≺ b
sep p (ys , refl) (zs , refl) =
  subst₂ _≺_ (sym (⊕-assoc p [ ix 0 ] ys)) (sym (⊕-assoc p [ ix 1 ] zs)) (Equivalence.from T-≡ (<ᵖ-part p ys zs (ix-< {0} {1} (s≤s z≤n))))

------------------------------------------------------------------------
-- The pair a concat and a merge run over

O : Pos → EmissionSet Bool
O s = enter (Op.of (true ∷ false ∷ [])) s

o-row : ∀ s {q a} → O s q (out a) → (q ≡ s ⊕ [ ix 0 ] × a ≡ true) ⊎ (q ≡ s ⊕ [ ix 1 ] × a ≡ false)
o-row s (at-out , _)             = inj₁ (refl , refl)
o-row s (on-out at-out , _)      = inj₂ (refl , refl)
o-row s (on-out (on-out ()) , _)

o-under : ∀ s {y e} → O s y e → s ⊑ y
o-under s (x , _) = of-below s 0 _ x

module Pair (s : Pos) where
  open Values (O s) using (Nth; first; next)

  lt₀₁ : (s ⊕ [ ix 0 ]) ≺ (s ⊕ [ ix 1 ])
  lt₀₁ = ix-asc s (s≤s z≤n)

  o-first : ∀ {k b} → O s k (out b) → (s ⊕ [ ix 0 ]) ≼ k
  o-first x with o-row s x
  ... | inj₁ (refl , _) = ≼-refl {s ⊕ [ ix 0 ]}
  ... | inj₂ (refl , _) = ≺→≼ {s ⊕ [ ix 0 ]} {s ⊕ [ ix 1 ]} lt₀₁

  o-next : ∀ {k b} → O s k (out b) → (s ⊕ [ ix 0 ]) ≺ k → (s ⊕ [ ix 1 ]) ≼ k
  o-next x lt with o-row s x
  ... | inj₁ (refl , _) = ⊥-elim (≺-irrefl {s ⊕ [ ix 0 ]} lt)
  ... | inj₂ (refl , _) = ≼-refl {s ⊕ [ ix 1 ]}

  nth₀ : Nth 0 (s ⊕ [ ix 0 ]) true
  nth₀ = first (at-out , of-reach s 0 (true ∷ false ∷ []) {s ⊕ [ ix 0 ]} {out true}) o-first

  nth₁ : Nth 1 (s ⊕ [ ix 1 ]) false
  nth₁ = next nth₀ (on-out at-out , of-reach s 0 (true ∷ false ∷ []) {s ⊕ [ ix 1 ]} {out false}) lt₀₁ o-next

-- Where a concatenated lane's rows lie in a fired instant, and then the
-- concat's.
Zl : List Path
Zl = [] ∷ (ix 1 ∷ ix 0 ∷ []) ∷ (ix 1 ∷ last ∷ []) ∷ []

Zc : List Path
Zc = Zl ++ L.map (_++ [ ix 0 ]) Zl

Zt : List Path
Zt = Zc ++ (L.map (_++ [ ix 0 ]) Zc ++ L.concatMap (λ z → L.map (λ w → (z ++ [ ix 1 ]) ++ w) RZ) Zc)

------------------------------------------------------------------------
-- The elaborated cold, layer by layer

module Core {A : Set} (Fc Fm : Bool → Den (Tag A)) (R : Bool × Tag A → Den (IE A))
  (fc-true  : ∀ s {y e} → enter (Fc true) s y e → Place One s y × Tickless e)
  (fc-false : ∀ s {y e} → enter (Fc false) s y e → (y ≡ s ⊕ [ ix 0 ] ⊎ y ≡ s ⊕ [ last ]) × Tickless e)
  (fm-true  : ∀ s {y e} → enter (Fm true) s y e → enter (Op.flatMap (mergeᶠ (just 1)) Fc (Op.of (true ∷ false ∷ []))) s y e)
  (fm-false : ∀ s {y e} → enter (Fm false) s y e → s ⊑ y × Ticks e)
  (r-in     : ∀ x s {y e} → enter (R x) s y e → Rendered s y)
  (r-begin  : ∀ x s {y n} → enter (R x) s y (out (instEmit (mark begin) n)) → Late x) where

  S₁ S₂ : Pos → Pos
  S₁ s = (s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]
  S₂ s = (s ⊕ [ ix 1 ]) ⊕ [ ix 1 ]

  -- Where a concat's lane runs: its first, at once; its second, at once
  -- or where the first ends.
  data Ran (s k : Pos) (e : Ev (Tag A)) : Set where
    ran₁ : enter (Fc true) (S₁ s) k e → Ran s k e
    ran₂ : enter (Fc false) (S₂ s) k e → Ran s k e
    ran₃ : ∀ {c} → enter (Fc true) (S₁ s) c end → enter (Fc false) (c ⊕ [ ix 1 ]) k e → Ran s k e

  module Cat (s : Pos) where
    open Bounded 1 Fc (O s) using (Lane; Starts; room; freed; queued; Kth; Sched)
    open Pair s using (nth₀; nth₁)
    open Nths (O s) using (nth-val; nth-inj)
    open Values (O s) using (Nth)

    end-t : ∀ {q a s′ c} → (q ≡ s ⊕ [ ix 0 ] × a ≡ true) ⊎ (q ≡ s ⊕ [ ix 1 ] × a ≡ false) → Nth 0 q a → Starts 0 q [] s′
          → enter (Fc a) s′ c end → enter (Fc true) (S₁ s) c end
    end-t (inj₁ (refl , refl)) nq (room _) r = r
    end-t (inj₁ (refl , refl)) nq (freed () _) r
    end-t (inj₁ (refl , refl)) nq (queued () _ _ _ _) r
    end-t (inj₂ (refl , refl)) nq st r with () ← nth-inj nq nth₁

    first-end : ∀ {c} → Kth (_≡ c) (Sched 1) 0 → enter (Fc true) (S₁ s) c end
    first-end (inj₁ (_ , (q , a , s′ , nq , st , (r , _)) , refl)) = end-t (o-row s (nth-val nq)) nq st r
    first-end (inj₂ ())

    ran-t′ : ∀ {s′ k e} → Starts 0 (s ⊕ [ ix 0 ]) [] s′ → enter (Fc true) s′ k e → Ran s k e
    ran-t′ (room _) r            = ran₁ r
    ran-t′ (freed () _) r
    ran-t′ (queued () _ _ _ _) r

    ran-f′ : ∀ {s′ k e} → Starts 1 (s ⊕ [ ix 1 ]) (Sched 1) s′ → enter (Fc false) s′ k e → Ran s k e
    ran-f′ (room (s≤s ())) r
    ran-f′ (freed _ _) r          = ran₂ r
    ran-f′ (queued _ _ kc _ _) r  = ran₃ (first-end kc) r

    ran-t : ∀ {k e} → Lane (s ⊕ [ ix 0 ]) true k e → Ran s k e
    ran-t (i , s′ , (nd , st) , (r , _)) with nth-inj nd nth₀
    ... | refl = ran-t′ st r

    ran-f : ∀ {k e} → Lane (s ⊕ [ ix 1 ]) false k e → Ran s k e
    ran-f (i , s′ , (nd , st) , (r , _)) with nth-inj nd nth₁
    ... | refl = ran-f′ st r

    lane-ran : ∀ {q a k e} → O s q (out a) → Lane q a k e → Ran s k e
    lane-ran x l with o-row s x
    ... | inj₁ (refl , refl) = ran-t l
    ... | inj₂ (refl , refl) = ran-f l

    two-pl : ∀ {s′ k} → s ⊑ s′ → (k ≡ s′ ⊕ [ ix 0 ] ⊎ k ≡ s′ ⊕ [ last ]) → s ⊑ k
    two-pl u (inj₁ refl) = ⊑-trans u (_ , refl)
    two-pl u (inj₂ refl) = ⊑-trans u (_ , refl)

    ran3-pl : ∀ {c k} l → Place One s c → k ≡ (c ⊕ [ ix 1 ]) ⊕ [ l ] → Place ((ix 1 ∷ l ∷ []) ∷ []) s k
    ran3-pl {c} l pc refl = subst (Place _ s) (sym (⊕-assoc c [ ix 1 ] [ l ])) (pl-ext (ix 1 ∷ l ∷ []) pc)

    ran-pl : ∀ {k e} → Ran s k e → Place Zl s k × Tickless e
    ran-pl (ran₁ r) with fc-true (S₁ s) r
    ... | pc , t = pl-wk (λ { (here refl) → here refl }) (pl-up (⊑₂ s (ix 0) (ix 1)) pc) , t
    ran-pl (ran₂ r) with fc-false (S₂ s) r
    ... | eq , t = inj₁ (two-pl (⊑₂ s (ix 1) (ix 1)) eq) , t
    ran-pl (ran₃ rc r) with fc-false _ r
    ... | inj₁ eq , t = pl-wk (λ { (here refl) → there (here refl) }) (ran3-pl (ix 0) (pl-up (⊑₂ s (ix 0) (ix 1)) (proj₁ (fc-true (S₁ s) rc))) eq) , t
    ... | inj₂ eq , t = pl-wk (λ { (here refl) → there (there (here refl)) }) (ran3-pl last (pl-up (⊑₂ s (ix 0) (ix 1)) (proj₁ (fc-true (S₁ s) rc))) eq) , t

    lane-pl : ∀ {q a k e} → O s q (out a) → Lane q a k e → Place Zc s k × Tickless e
    lane-pl x l with ran-pl (lane-ran x l)
    ... | pk , t = pl-wk (λ m → ∈-++⁺ˡ m) pk , t

    hand-pl : ∀ {q a c e} → O s q (out a) → Lane q a c e → Place Zc s (c ⊕ [ ix 0 ])
    hand-pl x l = pl-wk (λ m → ∈-++⁺ʳ Zl m) (pl-ext [ ix 0 ] (proj₁ (ran-pl (lane-ran x l))))

    -- Each row of the concat, and no tick among its values.
    cat-pl : ∀ {y e} → Bounded.JoinT 1 Fc (O s) y e → Place Zc s y × Tickless e
    cat-pl (Joining.val x)                = inj₁ (⊑-trans (o-under s x) (_ , refl)) , tt
    cat-pl (Joining.step x)               = inj₁ (o-under s x) , tt
    cat-pl (Joining.opin x)               = inj₁ (o-under s x) , tt
    cat-pl (Joining.oend x _)             = inj₁ (o-under s x) , tt
    cat-pl (Joining.opass x _)            = inj₁ (o-under s x) , tt
    cat-pl (Joining.lane x _ l _ _)       = lane-pl x l
    cat-pl (Joining.lend x _ l _ _ _)     = lane-pl x l
    cat-pl (Joining.lpass x _ l _ _ _)    = proj₁ (lane-pl x l) , tt
    cat-pl (Joining.hand x _ l _ _)       = hand-pl x l , tt
    cat-pl (Joining.left x _ l _ _)       = lane-pl x l
    cat-pl (Joining.run () _)
    cat-pl (Joining.rend () _ _)
    cat-pl (Joining.rpass () _ _)
    cat-pl (Joining.rhand () _)

  open Cat using (cat-pl)

  -- The merge of the concat and the tick.
  Mg : Pos → EmissionSet (Tag A)
  Mg p = enter (Op.flatMap (mergeᶠ nothing) Fm (Op.of (true ∷ false ∷ []))) p

  mg-lane : ∀ p {q a k e} → O p q (out a) → enter (Fm a) (q ⊕ [ ix 1 ]) k e
          → (Place Zc (S₁ p) k × Tickless e) ⊎ ((p ⊕ [ ix 1 ]) ⊑ k × Ticks e)
  mg-lane p x l with o-row p x
  ... | inj₁ (refl , refl) = inj₁ (cat-pl (S₁ p) (proj₁ (fm-true _ l)))
  ... | inj₂ (refl , refl) with fm-false _ l
  ...   | u , t = inj₂ (⊑-trans (_ , refl) u , t)

  ml-pl′ : ∀ p {k} {e : Ev (Tag A)} → (Place Zc (S₁ p) k × Tickless e) ⊎ ((p ⊕ [ ix 1 ]) ⊑ k × Ticks e) → Place Zc p k
  ml-pl′ p (inj₁ (pc , _)) = pl-up (⊑₂ p (ix 0) (ix 1)) pc
  ml-pl′ p (inj₂ (u , _))  = inj₁ (⊑-trans (_ , refl) u)

  ml-pl : ∀ p {q a k e} → O p q (out a) → enter (Fm a) (q ⊕ [ ix 1 ]) k e → Place Zc p k
  ml-pl p {e = e} x l = ml-pl′ p {e = e} (mg-lane p x l)

  mg-pl : ∀ p {y e} → Merge.JoinT Fm (O p) y e → Place Zc p y
  mg-pl p (Joining.val x)                    = inj₁ (⊑-trans (o-under p x) (_ , refl))
  mg-pl p (Joining.step x)                   = inj₁ (o-under p x)
  mg-pl p (Joining.opin x)                   = inj₁ (o-under p x)
  mg-pl p (Joining.oend x _)                 = inj₁ (o-under p x)
  mg-pl p (Joining.opass x _)                = inj₁ (o-under p x)
  mg-pl p (Joining.lane x _ (l , _) _ _)     = ml-pl p x l
  mg-pl p (Joining.lend x _ (l , _) _ _ _)   = ml-pl p x l
  mg-pl p (Joining.lpass x _ (l , _) _ _ _)  = ml-pl p x l
  mg-pl p (Joining.hand _ _ _ _ ())
  mg-pl p (Joining.left x _ (l , _) _ _)     = ml-pl p x l
  mg-pl p (Joining.run () _)
  mg-pl p (Joining.rend () _ _)
  mg-pl p (Joining.rpass () _ _)
  mg-pl p (Joining.rhand () _)

  -- A tick lies under the second child; every other value under the
  -- first, or in a fired instant.
  mg-out : ∀ p {y v} → Merge.JoinT Fm (O p) y (out v)
         → (Ticks (out v) × (p ⊕ [ ix 1 ]) ⊑ y) ⊎ (Tickless (out v) × ((p ⊕ [ ix 0 ]) ⊑ y ⊎ Fresh p (instant y)))
  mg-out p (Joining.lane x _ (l , _) _ _) with mg-lane p x l
  ... | inj₁ (inj₁ u , t)       = inj₂ (t , inj₁ (⊑-trans (_ , refl) u))
  ... | inj₁ (inj₂ (_ , f) , t) = inj₂ (t , inj₂ (fresh-⊑ (⊑₂ p (ix 0) (ix 1)) f))
  ... | inj₂ (u , t)            = inj₁ (t , u)
  mg-out p (Joining.run () _)

  -- The scan reads past the tick from it on.
  Acc : Pos → Pos → Bool × Tag A → Set
  Acc p = Scan.Acc phase (false , tick) (Mg p)

  acc-tag : ∀ {p q b} → Acc p q b → Mg p q (out (proj₂ b))
  acc-tag (Scan.acc₀ x _)    = x
  acc-tag (Scan.acc _ x _ _) = x

  acc-late : ∀ {p q b} → Acc p q b → T (proj₁ b) → Σ Pos λ k → Mg p k (out tick) × k ≼ q
  acc-late (Scan.acc₀ {q} {tick} x _) _ = q , x , ≼-refl {q}
  acc-late (Scan.acc₀ {a = val _} x _) ()
  acc-late (Scan.acc₀ {a = cdone} x _) ()
  acc-late (Scan.acc {q′ = q′} {a′ = tick} r x lt nx) _ = q′ , x , ≼-refl {q′}
  acc-late (Scan.acc {q} {b} {q′} {val _} r x lt nx) h = later q q′ lt (acc-late r (T∨f (proj₁ b) h))
    where
      later : ∀ {p} q q′ → q ≺ q′ → Σ Pos (λ k → Mg p k (out tick) × k ≼ q) → Σ Pos λ k → Mg p k (out tick) × k ≼ q′
      later q q′ lt (k , y , le) = k , y , λ q′k → le (≺-trans {q} {q′} {k} lt q′k)
  acc-late (Scan.acc {q} {b} {q′} {cdone} r x lt nx) h = later q q′ lt (acc-late r (T∨f (proj₁ b) h))
    where
      later : ∀ {p} q q′ → q ≺ q′ → Σ Pos (λ k → Mg p k (out tick) × k ≼ q) → Σ Pos λ k → Mg p k (out tick) × k ≼ q′
      later q q′ lt (k , y , le) = k , y , λ q′k → le (≺-trans {q} {q′} {k} lt q′k)

  Sc : Pos → EmissionSet (Bool × Tag A)
  Sc p = enter (Op.scan phase (false , tick) (Op.flatMap (mergeᶠ nothing) Fm (Op.of (true ∷ false ∷ [])))) p

  sc-pl : ∀ p {y e} → Sc p y e → Place Zc p y
  sc-pl p (Scan.sval a , _)  = mg-pl p (proj₁ (acc-tag a))
  sc-pl p (Scan.sstep x , _) = mg-pl p (proj₁ x)
  sc-pl p (Scan.spin x , _)  = mg-pl p (proj₁ x)
  sc-pl p (Scan.send x , _)  = mg-pl p (proj₁ x)

  -- The renders, merged.
  lane-top : ∀ {p q₀ w} → Place Zc p q₀ → w ∈ RZ → Place Zt p ((q₀ ⊕ [ ix 1 ]) ⊕ w)
  lane-top {q₀ = _ ∙ _} {w} (inj₁ u) _ = inj₁ (⊑-trans u (⊑-trans (_ , refl) (w , refl)))
  lane-top {q₀ = _ ∙ ps} (inj₂ (m , f)) wm =
    inj₂ (∈-++⁺ʳ Zc (∈-++⁺ʳ (L.map (_++ [ ix 0 ]) Zc) (∈-cm (λ z → L.map (λ w → (z ++ [ ix 1 ]) ++ w) RZ) Zc m (∈-map⁺ (λ w → (ps ++ [ ix 1 ]) ++ w) wm))) , f)

  tl-pl : ∀ p {q₀ x₀ k e} → Sc p q₀ (out x₀) → enter (R x₀) (q₀ ⊕ [ ix 1 ]) k e → Place Zt p k
  tl-pl p {q₀} {x₀} x l with r-in x₀ (q₀ ⊕ [ ix 1 ]) l
  ... | _ , wm , refl = lane-top (sc-pl p x) wm

  top-pl : ∀ p {y e} → Merge.JoinT R (Sc p) y e → Place Zt p y
  top-pl p (Joining.val x)                   = pl-wk (λ m → ∈-++⁺ʳ Zc (∈-++⁺ˡ m)) (pl-ext [ ix 0 ] (sc-pl p x))
  top-pl p (Joining.step x)                  = pl-wk (λ m → ∈-++⁺ˡ m) (sc-pl p x)
  top-pl p (Joining.opin x)                  = pl-wk (λ m → ∈-++⁺ˡ m) (sc-pl p x)
  top-pl p (Joining.oend x _)                = pl-wk (λ m → ∈-++⁺ˡ m) (sc-pl p x)
  top-pl p (Joining.opass x _)               = pl-wk (λ m → ∈-++⁺ˡ m) (sc-pl p x)
  top-pl p (Joining.lane x _ (l , _) _ _)    = tl-pl p x l
  top-pl p (Joining.lend x _ (l , _) _ _ _)  = tl-pl p x l
  top-pl p (Joining.lpass x _ (l , _) _ _ _) = tl-pl p x l
  top-pl p (Joining.hand _ _ _ _ ())
  top-pl p (Joining.left x _ (l , _) _ _)    = tl-pl p x l
  top-pl p (Joining.run () _)
  top-pl p (Joining.rend () _ _)
  top-pl p (Joining.rpass () _ _)
  top-pl p (Joining.rhand () _)

  -- A begin's instant is a fired one: its value was read past the tick,
  -- which every value of the subscribe instant precedes.
  read-late : ∀ p {q₀ x₀} → Acc p q₀ x₀ → Late x₀ → Fresh p (instant q₀)
  read-late p {x₀ = x₀} ac lt with mg-out p (proj₁ (acc-tag ac))
  ... | inj₁ (tk , _)      = ⊥-elim (late-tick x₀ lt tk)
  ... | inj₂ (_ , inj₂ f)  = f
  ... | inj₂ (_ , inj₁ u₀) with acc-late ac (late-on x₀ lt)
  ...   | k , (kr , _) , le with mg-out p kr
  ...     | inj₁ (_ , u₁) = ⊥-elim (le (sep p u₀ u₁))
  ...     | inj₂ (() , _)

  fresh-at : ∀ {p q₀ q w} → q ≡ (q₀ ⊕ [ ix 1 ]) ⊕ w → Fresh p (instant q₀) → Fresh p (instant q)
  fresh-at {q₀ = _ ∙ _} refl f = f

  top-begin : ∀ p {q n} → Merge.JoinT R (Sc p) q (out (instEmit (mark begin) n)) → Fresh p (instant q)
  top-begin p (Joining.lane {q₀} {x₀} (Scan.sval ac , _) _ (l , _) _ _) with r-in x₀ (q₀ ⊕ [ ix 1 ]) l
  ... | _ , _ , eq = fresh-at eq (read-late p ac (r-begin x₀ (q₀ ⊕ [ ix 1 ]) l))
  top-begin p (Joining.run () _)

  in-at : ∀ {I y} → instant y ≡ I → path y ∈ Zt → y ∈ L.map (I ∙_) Zt
  in-at {y = _ ∙ _} refl m = ∈-map⁺ (_ ∙_) m

  step-few : ∀ p {q n} → Merge.JoinT R (Sc p) q (out (instEmit (mark begin) n))
           → Σ (List Pos) λ ks → ∀ {y e} → Merge.JoinT R (Sc p) y e → instant y ≡ instant q → y ∈ ks
  step-few p {q} bq = L.map (instant q ∙_) Zt , go
    where
      go : ∀ {y e} → Merge.JoinT R (Sc p) y e → instant y ≡ instant q → y ∈ L.map (instant q ∙_) Zt
      go r eq with top-pl p r
      ... | inj₁ u       = ⊥-elim (fresh-self {p} (subst (Fresh p) (trans (sym eq) (instant-⊑ u)) (top-begin p bq)))
      ... | inj₂ (m , _) = in-at eq m

------------------------------------------------------------------------
-- The elaborated cold

module _ {Δ : List Set} (env : DenEnv Δ) where

  map-cold : ∀ {A} (c : Timeline A) s {y e} → enter (Op.map val (Op.cold c)) s y e → Place One s y × Tickless e
  map-cold c s (map-out (x , _) , _)  = cold-pl c s x , tt
  map-cold c s (map-skip (x , _) , _) = cold-pl c s x , tt
  map-cold c s (map-pin (x , _) , _)  = cold-pl c s x , tt
  map-cold c s (map-end (x , _) , _)  = cold-pl c s x , tt

  cd-rows : ∀ {A} s {y e} → enter (Op.of (cdone {A} ∷ [])) s y e → (y ≡ s ⊕ [ ix 0 ] ⊎ y ≡ s ⊕ [ last ]) × Tickless e
  cd-rows s (at-out , _)          = inj₁ refl , tt
  cd-rows s (on-out at-end , _)   = inj₂ refl , tt

  tk-rows : ∀ {A} s {y e} → enter (Op.of (tick {A} ∷ [])) s y e → s ⊑ y × Ticks e
  tk-rows s (at-out , _)          = (_ , refl) , tt
  tk-rows s (on-out at-end , _)   = (_ , refl) , tt

  fc-true : ∀ m {A} (c : Timeline A) s {y e} → enter (ev m (map val (cold c)) env) s y e → Place One s y × Tickless e
  fc-true nothing  c s r = map-cold c s r
  fc-true (just _) c s r = map-cold c s r

  fc-false : ∀ m {A} s {y e} → enter (ev m (of (cdone {A} ∷ [])) env) s y e → (y ≡ s ⊕ [ ix 0 ] ⊎ y ≡ s ⊕ [ last ]) × Tickless e
  fc-false nothing  s r = cd-rows s r
  fc-false (just _) s r = cd-rows s r

  fm-true : ∀ m {A} (c : Timeline A) s {y e} → enter (ev m (concatˢ (map val (cold c)) (of (cdone ∷ []))) env) s y e
          → enter (Op.flatMap (mergeᶠ (just 1)) (λ b → ev m (if b then map val (cold c) else of (cdone ∷ [])) env) (Op.of (true ∷ false ∷ []))) s y e
  fm-true nothing  c s r = r
  fm-true (just _) c s r = r

  fm-false : ∀ m {A} s {y e} → enter (ev m (of (tick {A} ∷ [])) env) s y e → s ⊑ y × Ticks e
  fm-false nothing  s r = tk-rows s r
  fm-false (just _) s r = tk-rows s r

  render-in : ∀ m {A} (x : Bool × Tag A) s {y e} → enter (ev m (render x) env) s y e → Rendered s y
  render-in nothing  (false , val a) s (r , _) = one-in s _ r
  render-in nothing  (true , val a)  s r       = rv-in a s r
  render-in nothing  (true , cdone)  s r       = cd-in s r
  render-in nothing  (false , cdone) s r       = em-in s r
  render-in nothing  (false , tick)  s r       = em-in s r
  render-in nothing  (true , tick)   s r       = em-in s r
  render-in (just _) (false , val a) s (r , _) = one-in s _ r
  render-in (just _) (true , val a)  s r       = rv-in a s r
  render-in (just _) (true , cdone)  s r       = cd-in s r
  render-in (just _) (false , cdone) s r       = em-in s r
  render-in (just _) (false , tick)  s r       = em-in s r
  render-in (just _) (true , tick)   s r       = em-in s r

  render-begin : ∀ m {A} (x : Bool × Tag A) s {y n} → enter (ev m (render x) env) s y (out (instEmit (mark begin) n)) → Late x
  render-begin nothing  (false , val a) s (on-out () , _)
  render-begin nothing  (true , val a)  s _ = tt
  render-begin nothing  (true , cdone)  s _ = tt
  render-begin nothing  (false , cdone) s (() , _)
  render-begin nothing  (false , tick)  s (() , _)
  render-begin nothing  (true , tick)   s (() , _)
  render-begin (just _) (false , val a) s (on-out () , _)
  render-begin (just _) (true , val a)  s _ = tt
  render-begin (just _) (true , cdone)  s _ = tt
  render-begin (just _) (false , cdone) s (() , _)
  render-begin (just _) (false , tick)  s (() , _)
  render-begin (just _) (true , tick)   s (() , _)

  module Cold (m : Maybe ℕ) {A : Set} (c : Timeline A) =
    Core (λ b → ev m (if b then map val (cold c) else of (cdone ∷ [])) env)
         (λ b → ev m (if b then concatˢ (map val (cold c)) (of (cdone ∷ [])) else of (tick ∷ [])) env)
         (λ x → ev m (render x) env)
         (fc-true m c) (fc-false m) (fm-true m c) (fm-false m) (render-in m) (render-begin m)

few : ∀ {X} {t : EmissionSet X} {q} → Σ (List Pos) (λ ks → ∀ {y e} → t y e → instant y ≡ instant q → y ∈ ks)
    → Σ (List Pos) λ ks → ∀ {y e} → Truncate t y e → rootOf y ≡ rootOf q → y ∈ ks
few (ks , h) = ks , λ (r , _) eq → h r (cong instant eq)

-- A cold's step makes finitely many rows, past its over or not.
cold-step-few : ∀ m {Δ A} (c : Timeline A) (env : DenEnv Δ) p {q n} → enter (ev m (coldˢ c) env) p q (out (instEmit (mark begin) n))
              → Σ (List Pos) λ ks → ∀ {y e} → enter (ev m (coldˢ c) env) p y e → rootOf y ≡ rootOf q → y ∈ ks
cold-step-few nothing  c env p {q} (bq , _) = few {q = q} (Cold.step-few env nothing c p bq)
cold-step-few (just n) c env p {q} (bq , _) = few {q = q} (Cold.step-few env (just n) c p bq)
