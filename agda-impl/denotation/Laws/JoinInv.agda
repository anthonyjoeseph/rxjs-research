{-# OPTIONS --guardedness #-}

-- A JOINER KEEPS THE INVARIANT.  Its rows are the outer's skips and ends
-- where they lie, a skip at each value's first child, and each running
-- lane's rows, the lane subscribed at the value's second child.  That
-- subscription lies in the world and is admissible, so the lane's rows
-- keep the lane's invariant.  Rows of different kinds, or of different
-- lanes, never meet: no outer row lies under a value's child's world
-- (`under`), and two values' children's worlds are apart (`apart-w`).
--
-- What follows an end follows the outer's end and every running lane's,
-- so the outer's and the lanes' `burst` and `quiet` carry over.
--
-- A `left` row is a lane's own: a value cutting a lane past a pin's
-- connect would be an outer row under the lane's world.
module denotation.Laws.JoinInv where

open import Data.Bool using (T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Properties using (++-identityʳ; ∷ʳ-injectiveˡ; ∷ʳ-injectiveʳ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import denotation.Events using (Pos; ix; inside; _≟ᵖ_)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Silent; hush; held; EmissionSet; _≺_; _≼_; Work; Den; enter; After; Truncate; module Joiner;
  module Switch; module Exhaust)
open import denotation.Laws.Modulus using (≺-irrefl; ≺→≼; ≼-antisym; ≼-or-≻; ≺-≼-≺; ≼-≺-≺)
open import denotation.Laws.Worlds using (Plain; plain-ix; W; W⁼; step; here; inW; Real; Ok; InvAt; InvD; _⊑_; real-snoc;
  ok-in; nest-in; nest⁼; apart-w; leads; w-up; not-up; conv; ⊑-refl; ⊑-snoc; ⊑-snoc⁺; ⊑-inside; inside-⊑; flat-under; ext≢; out-inj)

out≢skip : ∀ {A} {a : A} → out a ≡ skip → ⊥
out≢skip ()

end≢out : ∀ {A} {a : A} → end ≡ out a → ⊥
end≢out ()

ix01 : ix 0 ≡ ix 1 → ⊥
ix01 ()

ix10 : ix 1 ≡ ix 0 → ⊥
ix10 ()

-- Strictly leading `q ++ [ l′ ]`: leading `q`.
below : ∀ y {l} ys q {l′} → y ++ l ∷ ys ≡ q ++ [ l′ ] → y ⊑ q
below y {l} ys q eq with ⊑-snoc q (l ∷ ys , sym eq)
... | inj₁ le  = le
... | inj₂ eq′ = ⊥-elim (ext≢ y ys (trans eq (sym eq′)))

-- The worlds of a reading's rows' children, the reading at `p`.
module Kids {C : Set} {H : Pos → Set} {p : Pos} (ok : Ok H p) {O : EmissionSet C} (Io : InvAt H p O) where
  open InvAt Io renaming (world to wo; under to U)

  -- Two rows' children: apart worlds.
  kids : ∀ {x x′ e e′ l l′ w} → O x e → O x′ e′ → Plain l → Plain l′ → (x ++ [ l ] ≡ x′ ++ [ l′ ] → ⊥)
       → W⁼ H (x ++ [ l ]) w → W⁼ H (x′ ++ [ l′ ]) w → ⊥
  kids x x′ pl pl′ ne = apart-w pl pl′ ne (λ v → U x′ x pl′ v (⊑-refl _)) (λ v → U x x′ pl v (⊑-refl _))

  -- An outer row's child's world leads no other outer row's child ...
  kid-root : ∀ {x e l w q e′ l′} → O x e → Plain l → W⁼ H (x ++ [ l ]) w → O q e′ → Plain l′
           → (x ++ [ l ] ≡ q ++ [ l′ ] → ⊥) → w ⊑ (q ++ [ l′ ]) → ⊥
  kid-root {q = q} ox pl v oq pl′ ne r with ⊑-snoc q r
  ... | inj₁ wq   = U ox oq pl v wq
  ... | inj₂ refl with w-up pl′ v
  ...   | inj₁ eq = ne eq
  ...   | inj₂ v′ = U ox oq pl v′ (⊑-refl q)

  -- ... nor a row of another's lane.
  kid-lane : ∀ {x e l w q e″ y} → O x e → Plain l → W⁼ H (x ++ [ l ]) w → O q e″ → W H (q ++ [ ix 1 ]) y
           → (x ++ [ l ] ≡ q ++ [ ix 1 ] → ⊥) → w ⊑ y → ⊥
  kid-lane ox pl v xq yw ne le =
    leads (proj₁ ok) (proj₂ ok) (nest-in (step (inW (wo ox)) pl) v) (kids ox xq pl plain-ix ne v) (kid-root ox pl v xq plain-ix ne)
          (inW yw) le

-- An outer `O` read at `p`, and each of its values' lanes.
module Join {A B : Set} {H : Pos → Set} {p : Pos} (ok : Ok H p) (f : A → Den B) (fi : ∀ a → InvD H (f a))
            {O : EmissionSet A} (Io : InvAt H p O) where
  open InvAt Io renaming (world to wo; real to re; func to fu; flat to fl; burst to bu; under to U; quiet to qu)
  open Kids ok Io public

  Lane : Pos → A → EmissionSet B
  Lane q a = After (f a) (q ++ [ ix 1 ])

  sw : ∀ {q a} → O q (out a) → W H p (q ++ [ ix 1 ])
  sw x = step (inW (wo x)) plain-ix

  LI : ∀ {q a} → O q (out a) → InvAt H (q ++ [ ix 1 ]) (enter (f a) (q ++ [ ix 1 ]))
  LI {q} {a} x = fi a (q ++ [ ix 1 ]) (ok-in ok (sw x) (real-snoc q plain-ix (re x)))

  lw : ∀ {q a y e} (x : O q (out a)) → Lane q a y e → W H (q ++ [ ix 1 ]) y
  lw x l = InvAt.world (LI x) (proj₁ l)

  no-skip : ∀ {y} → O y skip → ∀ {a} → O y (out a) → ⊥
  no-skip x x′ = out≢skip (sym (fu x x′))

  no-end : ∀ {y} → O y end → ∀ {a} → O y (out a) → ⊥
  no-end x x′ = end≢out (fu x x′)

  -- An outer row leads no later one.
  strict : ∀ {q q′ e e′} → O q e → O q′ e′ → q ≺ q′ → q ⊑ q′ → ⊥
  strict {q} x x′ lt ([] , eq)       = ≺-irrefl {q} (subst (q ≺_) (trans eq (++-identityʳ q)) lt)
  strict     x x′ lt (z ∷ zs , refl) = fl x x′

  -- Every value comes before the outer's end.
  end-before : ∀ {c₀ q a} → O c₀ end → O q (out a) → q ≺ c₀
  end-before {c₀} {q} oc xq with ≼-or-≻ c₀ q | ≼-or-≻ q c₀
  ... | inj₂ lt | _        = lt
  ... | inj₁ _  | inj₂ lt′ = ⊥-elim (loud (qu oc xq lt′))
    where loud : ∀ {a} → Silent (out a) → ⊥
          loud ()
  ... | inj₁ le | inj₁ le′ = ⊥-elim (no-end oc (subst (λ z → O z (out _)) (≼-antisym {q} {c₀} le′ le) xq))

  -- No value's first child lies past the outer's end.
  val-after : ∀ {c₀ q a} → O c₀ end → O q (out a) → c₀ ≺ (q ++ [ ix 0 ]) → ⊥
  val-after {c₀} {q} oc xq lt =
    strict xq oc (end-before oc xq) (conv {q} {q} {c₀} {q ++ [ ix 0 ]} (⊑-refl q) (≺→≼ {q} {c₀} (end-before oc xq)) lt (⊑-snoc⁺ q))

  -- No outer row lies in a lane's world.
  o-lane : ∀ {y e q a} → O y e → O q (out a) → W H (q ++ [ ix 1 ]) y → ⊥
  o-lane oy xq yw = U xq oy plain-ix (inW yw) (⊑-refl _)

  -- No value's first child is a row of a lane.
  val-lane : ∀ {q q′ a a′} → O q (out a) → O q′ (out a′) → W H (q′ ++ [ ix 1 ]) (q ++ [ ix 0 ]) → ⊥
  val-lane {q} {q′} xq xq′ yw with w-up plain-ix (inW yw)
  ... | inj₁ eq = ix10 (∷ʳ-injectiveʳ q′ q eq)
  ... | inj₂ v  = U xq′ xq plain-ix v (⊑-refl q)

  -- Two lanes with a row at one position are one value's.
  one-lane : ∀ {q q′ a a′ y e e′} → O q (out a) → O q′ (out a′) → Lane q a y e → Lane q′ a′ y e′ → q ≡ q′
  one-lane {q} {q′} x x′ l l′ with q ≟ᵖ q′
  ... | yes eq = eq
  ... | no ne  = ⊥-elim (kids x x′ plain-ix plain-ix (λ eq → ne (∷ʳ-injectiveˡ q q′ eq)) (inW (lw x l)) (inW (lw x′ l′)))

  -- A non-value outer row leads no value ...
  o-lead : ∀ {y e₀ q a} → O y e₀ → (∀ {a′} → O y (out a′) → ⊥) → O q (out a) → y ⊑ q → ⊥
  o-lead {y} x n xq ([] , eq)       = n (subst (λ z → O z (out _)) (trans eq (++-identityʳ y)) xq)
  o-lead     x n xq (z ∷ zs , refl) = fl x xq

  -- ... nor a value's child ...
  o-under : ∀ {y e₀ q a l′} → O y e₀ → (∀ {a′} → O y (out a′) → ⊥) → O q (out a) → y ⊑ (q ++ [ l′ ]) → ⊥
  o-under {q = q} x n xq le with ⊑-snoc q le
  ... | inj₁ yq = o-lead x n xq yq
  ... | inj₂ eq = fl xq (subst (λ z → O z _) eq x)

  -- ... nor a row of its lane.
  o-lane-lead : ∀ {y e₀ q a y′} → O y e₀ → (∀ {a′} → O y (out a′) → ⊥) → O q (out a) → W H (q ++ [ ix 1 ]) y′ → y ⊑ y′ → ⊥
  o-lane-lead {y} x n xq yw le =
    leads (proj₁ ok) (proj₂ ok) (wo x) (λ v → U xq x plain-ix v (⊑-refl y)) (o-under x n xq) (inW yw) le

  -- A joiner's rows, given what ends it (`D`) and when a lane runs (`G`).
  module View (D : Pos → Set) (G : Pos → A → Pos → Set) where

    -- What an outer row shows.
    data OEv (c : Pos) : Ev A → Ev B → Set where
      o-skip : OEv c skip skip
      o-pin  : ∀ {r} → OEv c (pin r) (pin r)
      o-end  : D c → OEv c end end
      o-pass : ¬ D c → OEv c end skip

    -- What a running lane's row shows.
    data LEv (q : Pos) (a : A) (y : Pos) : Ev B → Ev B → Set where
      l-work : ∀ {e} → G q a y → Work e → LEv q a y e e
      l-end  : G q a y → D y → LEv q a y end end
      l-pass : G q a y → ¬ D y → LEv q a y end skip

    data V (y : Pos) : Ev B → Set where
      v-o    : ∀ {e₀ e} → O y e₀ → OEv y e₀ e → V y e
      v-val  : ∀ {q a} → O q (out a) → y ≡ q ++ [ ix 0 ] → V y skip
      v-lane : ∀ {q a e₀ e} → O q (out a) → Lane q a y e₀ → LEv q a y e₀ e → V y e

    o-nout : ∀ {y e₀ e} → OEv y e₀ e → O y e₀ → ∀ {a} → O y (out a) → ⊥
    o-nout o-skip     = no-skip
    o-nout o-pin      = λ x x′ → case (fu x x′) where case : ∀ {r a} → pin r ≡ out a → ⊥
                                                      case ()
    o-nout (o-end _)  = no-end
    o-nout (o-pass _) = no-end

    l-gate : ∀ {q a y e₀ e} → LEv q a y e₀ e → G q a y
    l-gate (l-work g _) = g
    l-gate (l-end g _)  = g
    l-gate (l-pass g _) = g

    o-func : ∀ {y e₀ e e′} → OEv y e₀ e → OEv y e₀ e′ → e ≡ e′
    o-func o-skip      o-skip      = refl
    o-func o-pin       o-pin       = refl
    o-func (o-end _)   (o-end _)   = refl
    o-func (o-end d)   (o-pass nd) = ⊥-elim (nd d)
    o-func (o-pass nd) (o-end d)   = ⊥-elim (nd d)
    o-func (o-pass _)  (o-pass _)  = refl

    l-func : ∀ {q a y e₀ e e′} → LEv q a y e₀ e → LEv q a y e₀ e′ → e ≡ e′
    l-func (l-work _ _)  (l-work _ _)  = refl
    l-func (l-work _ ()) (l-end _ _)
    l-func (l-work _ ()) (l-pass _ _)
    l-func (l-end _ _)   (l-work _ ())
    l-func (l-end _ _)   (l-end _ _)   = refl
    l-func (l-end _ d)   (l-pass _ nd) = ⊥-elim (nd d)
    l-func (l-pass _ _)  (l-work _ ())
    l-func (l-pass _ nd) (l-end _ d)   = ⊥-elim (nd d)
    l-func (l-pass _ _)  (l-pass _ _)  = refl

    o-skipped : ∀ {y e₀ e} → Silent e₀ → OEv y e₀ e → Silent e
    o-skipped hush o-skip = hush
    o-skipped held o-pin  = held

    l-skipped : ∀ {q a y e₀ e} → Silent e₀ → LEv q a y e₀ e → Silent e
    l-skipped s (l-work _ _) = s

    pinned-v : ∀ {y r} → V y (pin r) → W⁼ H p r × T (inside r y)
    pinned-v (v-o x o-pin)            = InvAt.pinned Io x
    pinned-v (v-lane x l (l-work _ _)) with InvAt.pinned (LI x) (proj₁ l)
    ... | w⁼ , i = nest⁼ (inW (sw x)) w⁼ , i

    world-v : ∀ {y e} → V y e → W H p y
    world-v (v-o x _)      = wo x
    world-v (v-val x refl) = step (inW (wo x)) plain-ix
    world-v (v-lane x l _) = nest-in (sw x) (inW (lw x l))

    real-v : ∀ {y e} → V y e → Real y
    real-v (v-o x _)          = re x
    real-v (v-val {q} x refl) = real-snoc q plain-ix (re x)
    real-v (v-lane x l _)     = InvAt.real (LI x) (proj₁ l)

    func-v : ∀ {y e e′} → V y e → V y e′ → e ≡ e′
    func-v (v-o x ev)      (v-o x′ ev′) with fu x x′
    ... | refl = o-func ev ev′
    func-v (v-o x _)       (v-val x′ refl)  = ⊥-elim (fl x′ x)
    func-v (v-o x _)       (v-lane x′ l _)  = ⊥-elim (o-lane x x′ (lw x′ l))
    func-v (v-val x refl)  (v-o x′ _)       = ⊥-elim (fl x x′)
    func-v (v-val _ _)     (v-val _ _)      = refl
    func-v (v-val x refl)  (v-lane x′ l _)  = ⊥-elim (val-lane x x′ (lw x′ l))
    func-v (v-lane x l _)  (v-o x′ _)       = ⊥-elim (o-lane x′ x (lw x l))
    func-v (v-lane x l _)  (v-val x′ refl)  = ⊥-elim (val-lane x′ x (lw x l))
    func-v (v-lane x l ev) (v-lane x′ l′ ev′) with one-lane x x′ l l′
    ... | refl with out-inj (fu x x′)
    ...   | refl with InvAt.func (LI x) (proj₁ l) (proj₁ l′)
    ...     | refl = l-func ev ev′

    flat-v : ∀ {y e l ys e′} → V y e → V (y ++ l ∷ ys) e′ → ⊥
    flat-v (v-o x _) (v-o x′ _) = fl x x′
    flat-v {y} {ys = ys} (v-o x ev) (v-val x′ eq) = o-lead x (o-nout ev x) x′ (below y ys _ eq)
    flat-v {l = l} {ys} (v-o x ev) (v-lane x′ l′ _) = o-lane-lead x (o-nout ev x) x′ (lw x′ l′) (l ∷ ys , refl)
    flat-v {l = l} {ys} (v-val x refl) (v-o x′ _) = flat-under Io {a = ix 0} x x′ (l ∷ ys , refl)
    flat-v {ys = ys} (v-val {q} x refl) (v-val x′ eq) = flat-under Io {a = ix 0} x x′ (below (q ++ [ ix 0 ]) ys _ eq)
    flat-v {l = l} {ys} (v-val x refl) (v-lane x′ l′ _) =
      kid-lane x plain-ix here x′ (lw x′ l′) (λ eq → ix01 (∷ʳ-injectiveʳ _ _ eq)) (l ∷ ys , refl)
    flat-v {l = l} {ys} (v-lane x l₀ _) (v-o x′ _) = U x x′ plain-ix (inW (lw x l₀)) (l ∷ ys , refl)
    flat-v {y} {ys = ys} (v-lane x l₀ _) (v-val x′ eq) = U x x′ plain-ix (inW (lw x l₀)) (below y ys _ eq)
    flat-v (v-lane {q} x l₀ _) (v-lane {q′} x′ l′ _) with q ≟ᵖ q′
    ... | yes refl with out-inj (fu x x′)
    ...   | refl = InvAt.flat (LI x) (proj₁ l₀) (proj₁ l′)
    flat-v {l = l} {ys} (v-lane {q} x l₀ _) (v-lane {q′} x′ l′ _) | no ne =
      kid-lane x plain-ix (inW (lw x l₀)) x′ (lw x′ l′) (λ eq → ne (∷ʳ-injectiveˡ q q′ eq)) (l ∷ ys , refl)

    -- Under a value's first child.
    val-under : ∀ {q a w l y e′} → O q (out a) → W⁼ H ((q ++ [ ix 0 ]) ++ [ l ]) w → W⁼ H (q ++ [ ix 0 ]) w → V y e′ → w ⊑ y → ⊥
    val-under xq v v₀ (v-o oy _) le = U xq oy plain-ix v₀ le
    val-under {q} xq v v₀ (v-val {q′} xq′ refl) le with ⊑-snoc q′ le
    ... | inj₁ wq = U xq xq′ plain-ix v₀ wq
    ... | inj₂ refl with w-up plain-ix v₀
    ...   | inj₁ eq = not-up (real-snoc q plain-ix (re xq)) v (subst (λ z → (q′ ++ [ ix 0 ]) ⊑ z) (sym eq) (⊑-refl _))
    ...   | inj₂ v′ = U xq xq′ plain-ix v′ (⊑-refl q′)
    val-under xq v v₀ (v-lane xq′ l′ _) le = kid-lane xq plain-ix v₀ xq′ (lw xq′ l′) (λ eq → ix01 (∷ʳ-injectiveʳ _ _ eq)) le

    under-v : ∀ {x y w l e e′} → V x e → V y e′ → Plain l → W⁼ H (x ++ [ l ]) w → w ⊑ y → ⊥
    under-v (v-o ox _) (v-o oy _) pl v le = U ox oy pl v le
    under-v {x} (v-o ox ev) (v-val xq refl) pl v le =
      kid-root ox pl v xq plain-ix (λ eq → o-nout ev ox (subst (λ z → O z (out _)) (sym (∷ʳ-injectiveˡ x _ eq)) xq)) le
    under-v {x} (v-o ox ev) (v-lane xq l′ _) pl v le =
      kid-lane ox pl v xq (lw xq l′) (λ eq → o-nout ev ox (subst (λ z → O z (out _)) (sym (∷ʳ-injectiveˡ x _ eq)) xq)) le
    under-v (v-val xq refl) vy pl v le = val-under xq v (nest⁼ (inW (step here pl)) v) vy le
    under-v (v-lane xq l₀ _) (v-o oy _) pl v le = U xq oy plain-ix (nest⁼ (inW (step (inW (lw xq l₀)) pl)) v) le
    under-v (v-lane xq l₀ _) (v-val xq′ refl) pl v le =
      kid-root xq plain-ix (nest⁼ (inW (step (inW (lw xq l₀)) pl)) v) xq′ plain-ix (λ eq → ix10 (∷ʳ-injectiveʳ _ _ eq)) le
    under-v (v-lane {q} xq l₀ _) (v-lane {q′} xq′ l′ _) pl v le with q ≟ᵖ q′
    ... | yes refl with out-inj (fu xq xq′)
    ...   | refl = InvAt.under (LI xq) (proj₁ l₀) (proj₁ l′) pl v le
    under-v (v-lane {q} xq l₀ _) (v-lane {q′} xq′ l′ _) pl v le | no ne =
      kid-lane xq plain-ix (nest⁼ (inW (step (inW (lw xq l₀)) pl)) v) xq′ (lw xq′ l′) (λ eq → ne (∷ʳ-injectiveˡ q q′ eq)) le

    -- What an end leaves: the outer ended by it, and every running lane
    -- with a row past it.
    Ended : Pos → Set
    Ended c = (Σ Pos λ c₀ → O c₀ end × c₀ ≼ c)
            × (∀ {q a y e₀} → O q (out a) → Lane q a y e₀ → G q a y → c ≺ y → Σ Pos λ c′ → Lane q a c′ end × c′ ≼ c)

    done-v : ∀ {c} → V c end → D c
    done-v (v-o _ (o-end d))        = d
    done-v (v-lane _ _ (l-end _ d)) = d
    done-v (v-lane _ _ (l-work _ ()))

    burst-v : (∀ {c} → D c → Ended c) → ∀ {c y e} → V c end → V y e → c ≺ y → Σ Pos λ w → W⁼ H p w × T (inside w c) × T (inside w y)
    burst-v en {c} {y} vc vy cy = go (en (done-v vc)) vy
      where
        go : ∀ {e} → Ended c → V y e → Σ Pos λ w → W⁼ H p w × T (inside w c) × T (inside w y)
        go ((c₀ , oc , le) , _) (v-o oy _) with bu oc oy (≼-≺-≺ {c₀} {c} {y} le cy)
        ... | w , w⁼ , i₁ , i₂ = w , w⁼ , ⊑-inside (conv {w} {c₀} {c} {y} (inside-⊑ w c₀ i₁) le cy (inside-⊑ w y i₂)) , i₂
        go ((c₀ , oc , le) , _) (v-val xq eq) = ⊥-elim (val-after oc xq (subst (c₀ ≺_) eq (≼-≺-≺ {c₀} {c} {y} le cy)))
        go (_ , ln) (v-lane xq l ev) with ln xq l (l-gate ev) cy
        ... | c′ , lc , le with InvAt.burst (LI xq) (proj₁ lc) (proj₁ l) (≼-≺-≺ {c′} {c} {y} le cy)
        ...   | w , w⁼ , i₁ , i₂ =
          w , nest⁼ (inW (sw xq)) w⁼ , ⊑-inside (conv {w} {c′} {c} {y} (inside-⊑ w c′ i₁) le cy (inside-⊑ w y i₂)) , i₂

    quiet-v : (∀ {c} → D c → Ended c) → ∀ {c y e} → V c end → V y e → c ≺ y → Silent e
    quiet-v en {c} {y} vc vy cy = go (en (done-v vc)) vy
      where
        go : ∀ {e} → Ended c → V y e → Silent e
        go ((c₀ , oc , le) , _) (v-o oy ev) = o-skipped (qu oc oy (≼-≺-≺ {c₀} {c} {y} le cy)) ev
        go _ (v-val _ _) = hush
        go (_ , ln) (v-lane xq l ev) with ln xq l (l-gate ev) cy
        ... | c′ , lc , le = l-skipped (InvAt.quiet (LI xq) (proj₁ lc) (proj₁ l) (≼-≺-≺ {c′} {c} {y} le cy)) ev

    inv-v : ∀ {X : EmissionSet B} → (∀ {y e} → X y e → V y e) → (∀ {c} → D c → Ended c) → InvAt H p X
    inv-v vw en = record
      { world = λ x → world-v (vw x)
      ; real  = λ x → real-v (vw x)
      ; func  = λ x x′ → func-v (vw x) (vw x′)
      ; flat  = λ x x′ → flat-v (vw x) (vw x′)
      ; burst = λ c y cy → burst-v en (vw c) (vw y) cy
      ; under = λ x y pl v le → under-v (vw x) (vw y) pl v le
      ; quiet = λ c y cy → quiet-v en (vw c) (vw y) cy
      ; pinned = λ x → pinned-v (vw x)
      }

-- A joiner, given its policy: a cut only ever grows, and never falls
-- past a connect in a lane's world.
module JoinerI {A B H p} (ok : Ok H p) (f : A → Den B) (fi : ∀ a → InvD H (f a)) {O : EmissionSet A} (Io : InvAt H p O)
               (Runs : Pos → Set) (Cut : Pos → Pos → Set) (cut-up : ∀ {q k y} → Cut q k → k ≼ y → Cut q y)
               (uncut : ∀ {q a k r} → O q (out a) → W⁼ H (q ++ [ ix 1 ]) r → T (inside r k) → Cut q k → ¬ Cut q r → ⊥) where
  open Joiner f O Runs Cut using (JoinT; val; step; opin; oend; opass; lane; lend; lpass; hand; left; run; rend; rpass; rhand; Done)
  open Join ok f fi Io using (module View; end-before; LI)
  open View Done (λ q _ y → Runs q × ¬ Cut q y)

  vw : ∀ {y e} → JoinT y e → V y e
  vw (val x)             = v-val x refl
  vw (step x)            = v-o x o-skip
  vw (opin x)            = v-o x o-pin
  vw (oend x d)          = v-o x (o-end d)
  vw (opass x nd)        = v-o x (o-pass nd)
  vw (lane x r l nc w)   = v-lane x l (l-work (r , nc) w)
  vw (lend x r l nc _ d)   = v-lane x l (l-end (r , nc) d)
  vw (lpass x r l nc _ nd) = v-lane x l (l-pass (r , nc) nd)
  vw (hand _ _ _ _ ())
  vw (left x r l nc _)     = v-lane x l (l-work (r , λ c → let (w⁼ , i) = InvAt.pinned (LI x) (proj₁ l) in uncut x w⁼ i c nc) tt)
  vw (run () _)
  vw (rend () _ _)
  vw (rpass () _ _)
  vw (rhand () _)

  en : ∀ {c} → Done c → Ended c
  en {c} ((c₀ , oc , le) , ln) = (c₀ , oc , le) , λ {q} xq _ (r , nc) cy → ln xq r (≺-≼-≺ {q} {c₀} {c} (end-before oc xq) le) (λ ct → nc (cut-up ct (≺→≼ {c} {_} cy)))

  inv : InvAt H p (Truncate JoinT)
  inv = inv-v (λ x → vw (proj₁ x)) en

-- A switch's cut only grows.
switch-cut-up : ∀ {A B : Set} (f : A → Den B) (o : EmissionSet A) {q k y} → Switch.Cut f o q k → k ≼ y → Switch.Cut f o q y
switch-cut-up f o {k = k} {y} (q′ , a′ , x , qq′ , q′k) ky = q′ , a′ , x , qq′ , ≺-≼-≺ {q′} {k} {y} q′k ky

module MergeI {A B H p} (ok : Ok H p) (f : A → Den B) (fi : ∀ a → InvD H (f a)) {O : EmissionSet A} (Io : InvAt H p O) where
  open JoinerI ok f fi Io (λ _ → ⊤) (λ _ _ → ⊥) (λ ()) (λ _ _ _ ()) public using (inv)

module SwitchI {A B H p} (ok : Ok H p) (f : A → Den B) (fi : ∀ a → InvD H (f a)) {O : EmissionSet A} (Io : InvAt H p O) where
  open Switch f O using (Cut)
  open Join ok f fi Io using (strict)
  open InvAt Io renaming (under to U)

  -- A value cuts no lane past a connect in its world: the value would lie
  -- under that world.
  uncut : ∀ {q a k r} → O q (out a) → W⁼ H (q ++ [ ix 1 ]) r → T (inside r k) → Cut q k → ¬ Cut q r → ⊥
  uncut {q} {k = k} {r} xq w⁼ ins (q′ , a′ , xq′ , qq′ , q′k) nc =
    U xq xq′ plain-ix w⁼ (conv {r} {r} {q′} {k} (⊑-refl r) (λ lt → nc (q′ , a′ , xq′ , qq′ , lt)) q′k (inside-⊑ r k ins))

  open JoinerI ok f fi Io (λ _ → ⊤) Cut (λ {q} {k} {y} → switch-cut-up f O {q} {k} {y}) (λ {q} {a} {k} {r} → uncut {q} {a} {k} {r}) public using (inv)

module ExhaustI {A B H p} (ok : Ok H p) (f : A → Den B) (fi : ∀ a → InvD H (f a)) {O : EmissionSet A} (Io : InvAt H p O) where
  open Exhaust f O using (Run)
  open JoinerI ok f fi Io Run (λ _ _ → ⊥) (λ ()) (λ _ _ _ ()) public using (inv)
