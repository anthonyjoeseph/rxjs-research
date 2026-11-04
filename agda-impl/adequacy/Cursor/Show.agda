{-# OPTIONS --guardedness #-}

-- A PIN SHOWS ONE LAYER UP: what a dead node's closure says of each
-- former.  A former that keeps pins in place shows a pin at its own row;
-- a cursor that has moved on has passed whatever its earlier self had.
module adequacy.Cursor.Show where

open import Data.Bool using (Bool; T; true; false; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List using ([]; _∷_; [_]; _++_; map)
open import Data.List.Properties using (++-identityʳ; ++-assoc; ∷ʳ-injectiveˡ; ∷ʳ-injectiveʳ)
open import Data.List.Relation.Unary.All using (All; _∷_) renaming ([] to []ᴬ)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Relation.Nullary using (¬_)

open import Tree using (Obs)
open import denotation.Events using (Pos; Timeline; ix; inside; <ᵖ-step; _<ᵖ_; <ᵖ-split; inside-++; inside-self)
open import denotation.EmissionSet using (EmissionSet; Ev; out; pin; _≺_; _≼_; Reach; Few; PDep; skip; module Connecting; module Joining; module Bounded; MapT; map-pin; ⟦_⟧; module Scan; module TakeWhile)
open import denotation.Laws.Modulus using (≺→≼; ≺-ext; ≺-trans; ≺-irrefl; ≼-refl; ≼-trans; ≺-≼-≺; ≼-≺-≺; ≼-antisym)
open import denotation.Laws.BoundedInv using (first-child)
open import Data.Bool.Properties using (T-≡)
open import Function.Bundles using (Equivalence)
open import Data.Unit using (tt)
open import operation.PureObservable using (module Machine)
open Machine using (Scope; CS)
open import adequacy.Rows using (Frozen; full)
open import adequacy.Cursor using (origin; bef; aft; Thru; Owes; Dom; Up; Bursts; _≈_; voc; NoFail; NoKill; Unkilled; Pol; Runs;
  Lane; polF; up; JoinF; JoinE; JInv; JRo; JRl; LanesIn; Sound; Behind; Parts; Flags; ConnE;
  Src; src-pend; src-on; src-shut; bursts; BurstsAt; notT; AttFin)
open import denotation.Laws.Worlds using (Hots; Real; InvAt; W⁼; here; inW; step; timer; join; real-snoc; plain-ix; real-init; nonempty⁼; world-after; world-after⁼; inside-⊑; ⊑-inside)
open import adequacy.Bound using (next-slot; in-slot; owes?; owes-≼)
open import adequacy.Rows using (≼-≢)
import denotation.Laws.Worlds as W
open import adequacy.PinLift using (reach-≈; reach-img; reach-map; reach-scan; reach-take; reach-few; PinFew)
open import denotation.Laws.JoinInv using (module Join)
open import denotation.Laws.BoundedInv using (module BoundedI)
open import denotation.Laws.Nth using (module Nths)
open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import Data.Maybe using (just; nothing)

-- What the cursor reached lies at or before all it owes.
thru-owes : ∀ C {r q} → Thru C r → Owes C q → r ≼ q
thru-owes origin  ()
thru-owes (bef p) {r} {q} t o = ≼-trans {r} {p} {q} t o
thru-owes (aft p) {r} {q} t o = ≺→≼ {r} {q} (≼-≺-≺ {r} {p} {q} t o)

-- Reached at a cursor: so is anything no later.
thru-dn : ∀ D {r q} → r ≼ q → Thru D q → Thru D r
thru-dn (bef p) {r} {q} rq t = ≼-trans {r} {q} {p} rq t
thru-dn (aft p) {r} {q} rq t = ≼-trans {r} {q} {p} rq t

-- A connect the cursor has passed it has reached.
thru-no : ∀ C {r} → ¬ Owes C r → Thru C r
thru-no origin  n = n tt
thru-no (bef p) {r} n pr = n (≺→≼ {p} {r} pr)
thru-no (aft p) n = n

-- A connect whose source's subscription the cursor is past it has
-- reached: nothing lies between a row and its first effect.
thru-sub : ∀ C {r} → (∀ {y} → Owes C y → (r ++ [ ix 1 ]) ≼ y) → Thru C r
thru-sub origin  {r} ps = ps {r} tt (≺-ext r [])
thru-sub (bef p) {r} ps pr = ps {p} (≼-refl {p}) (≺-trans {p} {r} {r ++ [ ix 1 ]} pr (≺-ext r []))
thru-sub (aft p) {r} ps pr = ≺-irrefl {r} (≺-≼-≺ {r} {r ++ [ ix 1 ]} {r} (≺-ext r [])
                               (≼-trans {r ++ [ ix 1 ]} {p ++ [ ix 0 ]} {r} (ps {p ++ [ ix 0 ]} (≺-ext p [])) (λ t → subst T (<ᵖ-step p r (Equivalence.to T-≡ pr)) t)))

-- A pin kept at its own row.
up-at : ∀ {A B} {D D′} {E : EmissionSet A} {E′ : EmissionSet B}
      → (∀ {y r} → Thru D r → T (inside r y) → E y (pin r) → Reach E y (pin r) → Thru D′ r × E′ y (pin r) × Reach E′ y (pin r))
      → Up D E D′ E′
up-at {E′ = E′} f = up λ {y} {r} nr i x rc → let (n′ , x′ , rc′) = f nr i x rc in [] , r , n′ , subst (λ z → T (inside r z)) (sym (++-identityʳ y)) i
                    , subst (λ z → E′ z (pin r)) (sym (++-identityʳ y)) x′
                    , subst (λ z → Reach E′ z (pin r)) (sym (++-identityʳ y)) rc′ , []ᴬ

up-id : ∀ {A} {D} {E : EmissionSet A} → Up D E D E
up-id {D = D} {E = E} = up-at {D = D} {D′ = D} {E = E} {E′ = E} λ nr _ x rc → nr , x , rc

up-≈ : ∀ {A} {D} {E E′ : EmissionSet A} → E ≈ E′ → Up D E D E′
up-≈ {D = D} {E = E} {E′ = E′} m = up-at {D = D} {D′ = D} {E = E} {E′ = E′} λ nr _ x rc → nr , voc m x , reach-≈ m rc

up-map : ∀ {A B} {f : A → B} {D} {E : EmissionSet A} → Up D E D (MapT f E)
up-map {f = f} {D = D} {E = E} = up-at {D = D} {D′ = D} {E = E} {E′ = MapT f E} λ nr _ x rc → nr , map-pin x , reach-map rc

up-scan : ∀ {A B} {f : B → A → B} {z} {D} {E : EmissionSet A} → Up D E D (Scan.ScanT f z E)
up-scan {f = f} {z = z} {D = D} {E = E} = up-at {D = D} {D′ = D} {E = E} {E′ = Scan.ScanT f z E} λ nr _ x rc → nr , Scan.spin x , reach-scan rc

-- A take whose failure, if any, the cursor has not yet passed.
up-take : ∀ {A} {incl} {keep : A → Bool} {D} {E : EmissionSet A}
        → (∀ {r} → Thru D r → ¬ TakeWhile.Failed incl keep E r) → Up D E D (TakeWhile.TakeT incl keep E)
up-take {incl = incl} {keep = keep} {D = D} {E = E} nf = up-at {D = D} {D′ = D} {E = E} {E′ = TakeWhile.TakeT incl keep E} λ nr i x rc → nr , TakeWhile.left x (nf nr) i , reach-take rc

-- A cursor moved on has passed what its earlier self passed.
up-adv : ∀ {A B} {D₁ D C} {E₁ : EmissionSet A} {E : EmissionSet B} → Dom C D → Up D₁ E₁ D E → Up D₁ E₁ C E
up-adv dm (up u) = up λ nr i x rc → let (xs , r′ , n′ , rest) = u nr i x rc in xs , r′ , dm n′ , rest

-- Two layers.
up-∘ : ∀ {A B X} {D₁ D₂ D₃} {E₁ : EmissionSet A} {E₂ : EmissionSet B} {E₃ : EmissionSet X}
     → Up D₁ E₁ D₂ E₂ → Up D₂ E₂ D₃ E₃ → Up D₁ E₁ D₃ E₃
up-∘ {E₃ = E₃} (up u) (up v) = up λ {y} nr i x rc → let (xs , r′ , n′ , i′ , x′ , rc′ , z′) = u nr i x rc ; (zs , r″ , n″ , i″ , x″ , rc″ , z″) = v n′ i′ x′ rc′ in xs ++ zs , r″ , n″
    , subst (λ z → T (inside r″ z)) (++-assoc y xs zs) i″
    , subst (λ z → E₃ z (pin r″)) (++-assoc y xs zs) x″
    , subst (λ z → Reach E₃ z (pin r″)) (++-assoc y xs zs) rc″ , ++⁺ z′ z″

-- What an earlier cursor reached, a later one has.
up-pre : ∀ {A B} {D C C′} {E : EmissionSet A} {E′ : EmissionSet B} → Dom C D → Up C E C′ E′ → Up D E C′ E′
up-pre dm (up u) = up λ nr → u (dm nr)

-- No failing value passed: none fails before a pin's connect passed.
nofail-up : ∀ {A} {incl} {keep : A → Bool} {C} {E : EmissionSet A} → NoFail C keep E → ∀ {r} → Thru C r → ¬ TakeWhile.Failed incl keep E r
nofail-up {C = C} nf t (q , _ , x , k , qr) = thru-owes C t (nf x k) qr

-- No kill passed: none cuts a lane before a pin's connect passed.
unkilled-no : ∀ {A B} {C} {P : Pol A B} {q} → Unkilled C P q → ∀ {r} → Thru C r → NoKill P q r
unkilled-no {C = C} uk t kl = thru-owes C t (uk kl)

------------------------------------------------------------------------
-- Where a connect's pins lie

-- A reading's pin is of a connect at or past the reading's subscription.
pin-law : ∀ {A H s} {X : EmissionSet A} → Real s → InvAt H s X → ∀ {y r} → X y (pin r) → s ≼ r
pin-law {s = s} rs I {y} {r} x with InvAt.pinned I x
... | w⁼ , ins with inside-⊑ r y ins
...   | zs , refl with real-init r zs (InvAt.real I x)
...     | inj₁ refl = ⊥-elim (nonempty⁼ (λ { refl → rs }) w⁼)
...     | inj₂ rr   = world-after⁼ w⁼ rr

-- First children in their parents' order.
snoc0-≺ : ∀ k y → (k ++ [ ix 0 ]) ≺ (y ++ [ ix 0 ]) → k ≺ y
snoc0-≺ k y lt with k <ᵖ y in e
... | true  = tt
... | false with <ᵖ-split y k e
...   | inj₂ refl = ⊥-elim (≺-irrefl {k ++ [ ix 0 ]} lt)
...   | inj₁ yk   = ⊥-elim (first-child y {k ++ [ ix 0 ]} (≺-trans {y} {k} {k ++ [ ix 0 ]} (Equivalence.from T-≡ yk) (≺-ext k [])) lt)

-- Within a connect's subscription: a first child within the connect.
in-call : ∀ c y → T (inside (c ++ [ ix 1 ]) y) → T (inside c (y ++ [ ix 0 ]))
in-call c y iw with inside-⊑ (c ++ [ ix 1 ]) y iw
... | w , refl = Equivalence.from T-≡ (subst (λ z → inside c z ≡ true)
                   (sym (trans (++-assoc (c ++ [ ix 1 ]) w [ ix 0 ]) (++-assoc c [ ix 1 ] (w ++ [ ix 0 ]))))
                   (inside-++ c c (ix 1 ∷ (w ++ [ ix 0 ])) (inside-self c)))

-- Under what lies under: inside is transitive.
inside-trans : ∀ x y z → T (inside x y) → T (inside y z) → T (inside x z)
inside-trans x y z i j with inside-⊑ x y i
... | zs , refl with inside-⊑ (x ++ zs) z j
...   | ws , refl = ⊑-inside {x} {(x ++ zs) ++ ws} (zs ++ ws , ++-assoc x zs ws)

-- The slot after a subscription is no point of its world.
no-slot : ∀ {H c w} → Real c → W⁼ H (c ++ [ ix 1 ]) w → w ≡ c ++ [ ix 2 ] → ⊥
no-slot {c = c} _ here eq with ∷ʳ-injectiveʳ c c eq
... | ()
no-slot {c = c} rc (inW (step {x} w pl)) eq with ∷ʳ-injectiveˡ x c eq
... | refl = world-after⁼ w rc (≺-ext c [])
no-slot {c = c} _ (inW (timer {e} t _)) eq with ∷ʳ-injectiveʳ (ix t ∷ []) c eq
... | ()
no-slot {c = c} _ (inW (join {h} _ _ _)) eq with ∷ʳ-injectiveʳ h c eq
... | ()

-- AN ISLE'S BURST SHOWS IN ITS CONNECT'S ENTRY: `burst` pins each row of
-- the subscription, and every row before it is a source row's child; the
-- body's rows lie past the connect and pin none of it.  A source's pin is
-- of a connect inside its subscription or past the slot after it, so no
-- row past the subscription pinned no later than that slot is `kept`.
conn-bursts : ∀ {Γ X B} {sc : Scope Γ} {Rg} {k : CS Γ X} {β E : EmissionSet B}
            → Parts sc Rg k β → ConnE (CS.connAt k) (Frozen k) β E → Bursts k E
conn-bursts {X = X} {k = k} {β} {E} pt (ce , _) = bursts wn kp
  where
    c = CS.connAt k
    open Connecting c (Frozen k) β using (ConnT; body; burst; echo; kept)
    rβ : Real (c ++ [ ix 0 ])
    rβ = real-snoc c plain-ix (Parts.cr pt)

    -- the body's rows: past the connect, none pinned to it
    bd : ∀ {q e′} → β q e′ → PDep c q e′ → ⊥
    bd b (inj₁ qc) = ≺-irrefl {c} (≺-trans {c} {c ++ [ ix 0 ]} {c} (≺-ext c [])
                       (≺-trans {c ++ [ ix 0 ]} {_} {c} (world-after (InvAt.world (Parts.iβ pt) b) (InvAt.real (Parts.iβ pt) b)) qc))
    bd b (inj₂ refl) = pin-law rβ (Parts.iβ pt) b (≺-ext c [])

    wn : ∀ {y} {e : Ev X} → Frozen k y e → T (inside (c ++ [ ix 1 ]) y) → Few (Frozen k) y
       → E (y ++ [ ix 0 ]) (pin c) × Reach E (y ++ [ ix 0 ]) (pin c)
    wn {y} x iw (fks , f) = voc ce (burst x iw , rc) , reach-≈ ce (reach-img (λ t → _ , proj₁ t , λ eq → eq) rc)
      where
        rc : Reach ConnT (y ++ [ ix 0 ]) (pin c)
        rc = map (_++ [ ix 0 ]) fks , λ where
          (body b)        _  d → ⊥-elim (bd b (d (in-call c y iw)))
          (burst {k′} x′ _)    lt _ → ∈-map⁺ (_++ [ ix 0 ]) (f x′ (snoc0-≺ k′ y lt))
          (echo {k′} x′ _ _ _) lt _ → ∈-map⁺ (_++ [ ix 0 ]) (f x′ (snoc0-≺ k′ y lt))
          (kept {k′} x′ _ _ _) lt _ → ∈-map⁺ (_++ [ ix 0 ]) (f x′ (snoc0-≺ k′ y lt))

    kp : ∀ {y r} → Frozen k y (pin r) → ¬ T (inside (c ++ [ ix 1 ]) y) → T (inside r y) → r ≼ (c ++ [ ix 2 ])
       → Reach (Frozen k) y (pin r)
       → r ≼ c × E (y ++ [ ix 0 ]) (pin r) × Reach E (y ++ [ ix 0 ]) (pin r)
    kp {y} {r} x ni ir rs _ with inside (c ++ [ ix 1 ]) r in ic
    ... | true  = ⊥-elim (ni (inside-trans (c ++ [ ix 1 ]) r y (Equivalence.from T-≡ ic) ir))
    ... | false = ⊥-elim (no-slot (Parts.cr pt) (proj₁ (InvAt.pinned (Parts.iσ pt) x))
                    (≼-antisym {r} {c ++ [ ix 2 ]} rs
                      (next-slot c r (pin-law (real-snoc c plain-ix (Parts.cr pt)) (Parts.iσ pt) x) (λ t → subst T ic t))))

------------------------------------------------------------------------
-- The joiner and the connect: where a pin shows past a truncation.

postulate
  -- A LANE'S PIN SHOWS IN ITS JOINER'S ENTRY: no kill before its connect,
  -- so `left` keeps it.
  flat-up-lane : ∀ {Γ} {sc : Scope Γ} {Rg C D A B} {op} {f : A → Obs Timeline Γ B} {ω O E q a}
               → JInv sc f O → JoinE sc op f ω O E → Behind C (JoinF op (λ a → ⟦ f a ⟧ (full sc)) O)
               → LanesIn (Hots (full sc)) (JRl sc Rg op f O) (polF op (λ a → ⟦ f a ⟧ (full sc)) O) O
               → O q (out a) → Runs (polF op (λ a → ⟦ f a ⟧ (full sc)) O) q
               → Dom C D → (∀ {r} → Thru D r → NoKill (polF op (λ a → ⟦ f a ⟧ (full sc)) O) q r)
               → Up D (Lane (polF op (λ a → ⟦ f a ⟧ (full sc)) O) q a) C E

-- A joiner's pins of one connect before a row: its outer's, which that
-- row waited on, when no lane pins the connect.
module JoinPins {A B : Set} (Lane : Pos → A → EmissionSet B) (o : EmissionSet A) (Over Runs : Pos → Set) (Cut : Pos → Pos → Set)
                (Hand : Pos → Set) where
  open Joining Lane o (λ _ _ → ⊥) Over Runs Cut Hand using (JoinT; opin; lane; left; run)

  pin-few : ∀ {y r} → T (inside r y) → Reach o y (pin r) → (∀ {q a k} → o q (out a) → Lane q a k (pin r) → ⊥) → PinFew JoinT r y
  pin-few {y} {r} _ (ks , f) nl = ks , g
    where
      g : ∀ {k} → JoinT k (pin r) → k ≺ y → k ∈ ks
      g (opin x) lt         = f x lt (λ _ → inj₂ refl)
      g (lane x _ l _ _) _  = ⊥-elim (nl x l)
      g (left x _ l _ _) _  = ⊥-elim (nl x l)
      g (run () _) _

-- No lane pins an outer pin's connect: that connect leads the outer row,
-- and no outer row lies under a value's lane world.
lane-not-outer : ∀ {Γ A B} {sc : Scope Γ} op {f : A → Obs Timeline Γ B} {O : EmissionSet A} → JInv sc f O
               → ∀ {y r q a k} → O y (pin r) → O q (out a) → Lane (polF op (λ a → ⟦ f a ⟧ (full sc)) O) q a k (pin r) → ⊥
lane-not-outer {sc = sc} op {f} {O} ji {y} {r} xo x l = go op l
  where
    f′ = λ a → ⟦ f a ⟧ (full sc)
    Io = JInv.io ji
    ry = inside-⊑ r y (proj₂ (InvAt.pinned Io xo))
    -- a bounded lane sits in the world of some value's second child
    root : ∀ m {i q s a} → Bounded.Sub m f′ O i q s a → Σ Pos λ q′ → Σ _ λ b → O q′ (out b) × W⁼ (Hots (full sc)) (q′ ++ [ ix 1 ]) s
    root m sb with BoundedI.seat* (JInv.ok ji) m f′ (JInv.fi ji) Io sb
    ... | BoundedI.seat′ _ _ _ nr rw = _ , _ , Nths.nth-val O nr , rw
    go : ∀ op → Lane (polF op f′ O) _ _ _ (pin r) → ⊥
    go (mergeᶠ nothing) (l , _) = InvAt.under Io x xo plain-ix (proj₁ (InvAt.pinned (Join.LI (JInv.ok ji) f′ (JInv.fi ji) Io x) l)) ry
    go switchᶠ          (l , _) = InvAt.under Io x xo plain-ix (proj₁ (InvAt.pinned (Join.LI (JInv.ok ji) f′ (JInv.fi ji) Io x) l)) ry
    go exhaustᶠ         (l , _) = InvAt.under Io x xo plain-ix (proj₁ (InvAt.pinned (Join.LI (JInv.ok ji) f′ (JInv.fi ji) Io x) l)) ry
    go (mergeᶠ (just m)) (_ , _ , sb , l , _) with root m sb
    ... | _ , _ , x′ , rw = InvAt.under Io x′ xo plain-ix (W.nest⁼ rw (proj₁ (InvAt.pinned (BoundedI.LI (JInv.ok ji) m f′ (JInv.fi ji) Io sb) l))) ry

-- Rows before a reached connect: passed, so behind.
thru-few : ∀ {A} C {E : EmissionSet A} {r} → Behind C E → Thru C r → Few E r
thru-few C {r = r} (ks , f) tr = ks , λ {k} x kr → f x (λ o → ≺-irrefl {k} (≺-≼-≺ {k} {r} {k} kr (thru-owes C tr o)))

-- A JOINER'S OUTER PIN SHOWS IN ITS ENTRY, kept by `opin`: what it waits
-- on there is the rows before its connect, which the cursor has behind
-- it, and the connect's other pins, which no lane carries.
flat-up-outer : ∀ {Γ} {sc : Scope Γ} {Rg C A B} {op} {f : A → Obs Timeline Γ B} {ω O E}
              → JInv sc f O → Sound (JRo sc Rg op f O) O → JoinE sc op f ω O E → Behind C (JoinF op (λ a → ⟦ f a ⟧ (full sc)) O)
              → Up C O C E
flat-up-outer {sc = sc} {C = C} {op = op} {f = f} {O = O} {E = E} ji _ je bh = up-at {D = C} {D′ = C} {E = O} {E′ = E} lift
  where
    f′ = λ a → ⟦ f a ⟧ (full sc)
    F = JoinF op f′ O
    held : ∀ op {y r} → O y (pin r) → JoinF op f′ O y (pin r)
    held (mergeᶠ nothing)  x = Joining.opin x
    held (mergeᶠ (just m)) x = Joining.opin x
    held switchᶠ           x = Joining.opin x
    held exhaustᶠ          x = Joining.opin x
    pins : ∀ op {y r} → T (inside r y) → Reach O y (pin r) → (∀ {q a k} → O q (out a) → Lane (polF op f′ O) q a k (pin r) → ⊥)
         → PinFew (JoinF op f′ O) r y
    pins (mergeᶠ nothing)  = JoinPins.pin-few _ O _ _ _ _
    pins (mergeᶠ (just m)) = JoinPins.pin-few _ O _ _ _ _
    pins switchᶠ           = JoinPins.pin-few _ O _ _ _ _
    pins exhaustᶠ          = JoinPins.pin-few _ O _ _ _ _
    lift : ∀ {y r} → Thru C r → T (inside r y) → O y (pin r) → Reach O y (pin r) → Thru C r × E y (pin r) × Reach E y (pin r)
    lift {y} {r} tr i x rc = tr , voc (proj₂ je) (held op x , rk) , reach-≈ (proj₂ je) (reach-img (λ t → _ , proj₁ t , λ eq → eq) rk)
      where
        rk : Reach F y (pin r)
        rk = reach-few i (thru-few C bh tr) (pins op i rc (lane-not-outer op ji x))

-- An attached source: live, its rows inside the subscription few.
src-att : ∀ {Γ X} {sc : Scope Γ} {Rg C} {k : CS Γ X} {o} → T (CS.srcAtt k) → Src sc Rg C k o → T (CS.srcLive k) × AttFin k
src-att sa (src-pend na _ _ _ _ _ _ _ _)  = ⊥-elim (notT _ na sa)
src-att sa (src-on _ _ _ _ af _ _ lv)      = lv , af
src-att sa (src-shut _ _ _ _ _ _ _ _ af lv) = lv , af

pin-inj : ∀ {A} {a b} → pin {A} a ≡ pin b → a ≡ b
pin-inj refl = refl

-- A CONNECT'S BODY PIN SHOWS IN ITS ENTRY, kept by `body`.  What it
-- waits on there: the body's rows it waited on, and the source's rows
-- before its connect, which the cursor has passed and the source has
-- behind it.  No source row is re-pinned to the same connect: a burst's
-- connect is the body's own, before every body pin, and no point of the
-- source's world is the body's.
conn-up-body : ∀ {Γ X B} {sc : Scope Γ} {Rg C} {k : CS Γ X} {o} {β E : EmissionSet B}
             → CS.scope k ≡ sc → (pt : Parts sc Rg k β) → Src sc (Parts.Rs pt) C k o → Behind C β → Flags C k β
             → ConnE (CS.connAt k) (Frozen k) β E → Up C β C E
conn-up-body {C = C} {k = k} {β = β} {E = E} _ pt sr bb _ ce = up-at {D = C} {D′ = C} {E = β} {E′ = E} lift
  where
    c = CS.connAt k
    open Connecting c (Frozen k) β using (ConnT; body; burst; echo; kept)
    Iσ = Parts.iσ pt
    Iβ = Parts.iβ pt

    -- the source's rows the cursor has passed: finitely many
    sbf : ∀ {sc′ Rg′ o′} → Src sc′ Rg′ C k o′ → Σ _ λ ks → ∀ {q e} → Frozen k q e → ¬ Owes C q → q ∈ ks
    sbf (src-pend _ _ _ _ _ _ _ ow _)   = [] , λ x no → ⊥-elim (no (owes-≼ C ow (≺→≼ {c ++ [ ix 1 ]} (world-after (InvAt.world Iσ x) (InvAt.real Iσ x)))))
    sbf (src-on _ _ bs _ _ _ _ _)       = bs
    sbf (src-shut _ _ _ _ _ bs _ _ _ _) = bs
    sb = sbf sr

    lift : ∀ {y r} → Thru C r → T (inside r y) → β y (pin r) → Reach β y (pin r) → Thru C r × E y (pin r) × Reach E y (pin r)
    lift {y} {r} tr ir b (ks , f) = tr , voc (proj₁ ce) (body b , rk) , reach-≈ (proj₁ ce) (reach-img (λ t → _ , proj₁ t , λ eq → eq) rk)
      where
        -- the body's pin: of a connect past the body's subscription
        cr : (c ++ [ ix 0 ]) ≼ r
        cr = pin-law (real-snoc c plain-ix (Parts.cr pt)) Iβ b
        notc : c ≡ r → ⊥
        notc eq = ≺-irrefl {c} (≺-≼-≺ {c} {c ++ [ ix 0 ]} {c} (≺-ext c []) (subst ((c ++ [ ix 0 ]) ≼_) (sym eq) cr))
        notk : ∀ {k′} → Frozen k k′ (pin r) → ⊥
        notk x = Parts.wapart pt (proj₁ (InvAt.pinned Iβ b)) (proj₁ (InvAt.pinned Iσ x)) (W.⊑-refl r)
        -- a source row before the pin's connect: passed
        passed : ∀ {k′ e} → Frozen k k′ e → (k′ ++ [ ix 0 ]) ≺ r → k′ ∈ proj₁ sb
        passed {k′} x lt = proj₂ sb x (λ o → ≺-irrefl {k′} (≺-≼-≺ {k′} {r} {k′} (≺-trans {k′} {k′ ++ [ ix 0 ]} {r} (≺-ext k′ []) lt) (thru-owes C tr o)))
        rk : Reach ConnT y (pin r)
        rk = ks ++ map (_++ [ ix 0 ]) (proj₁ sb) , g
          where
            g : ∀ {q e′} → ConnT q e′ → q ≺ y → (T (inside r y) → PDep r q e′) → q ∈ ks ++ map (_++ [ ix 0 ]) (proj₁ sb)
            g (body b′) lt d = ∈-++⁺ˡ (f b′ lt d)
            g (burst {k′} x _) _ d with d ir
            ... | inj₁ lt = ∈-++⁺ʳ ks (∈-map⁺ (_++ [ ix 0 ]) (passed x lt))
            ... | inj₂ eq = ⊥-elim (notc (pin-inj eq))
            g (echo {k′} x _ _ _) _ d with d ir
            ... | inj₁ lt = ∈-++⁺ʳ ks (∈-map⁺ (_++ [ ix 0 ]) (passed x lt))
            ... | inj₂ ()
            g (kept {k′} x _ _ _) _ d with d ir
            ... | inj₁ lt = ∈-++⁺ʳ ks (∈-map⁺ (_++ [ ix 0 ]) (passed x lt))
            ... | inj₂ refl = ⊥-elim (notk x)

-- AN ATTACHED SOURCE'S PIN SHOWS IN ITS CONNECT'S ENTRY.  Inside the
-- subscription it is re-pinned to the connect by `burst`: every source
-- row before it lies inside the subscription too, the slot after which
-- none reaches, so it has few.  Past the subscription it is kept by
-- `kept`: the body is alive after the pin's connect, whose end the cursor
-- has not passed, or which lies under the body's end still owed, and no
-- point of the source's world is the body's.
conn-up-src : ∀ {Γ X B} {sc : Scope Γ} {Rg C} {k : CS Γ X} {o} {β E : EmissionSet B}
            → T (CS.srcAtt k) → CS.scope k ≡ sc → (pt : Parts sc Rg k β) → Src sc (Parts.Rs pt) C k o → Behind C β → Flags C k β
            → ConnE (CS.connAt k) (Frozen k) β E → Up C (Frozen k) C E
conn-up-src {C = C} {k = k} {β = β} {E = E} sa _ pt sr bb fl ce = up lift
  where
    c = CS.connAt k
    open Connecting c (Frozen k) β using (ConnT; Alive; body; burst; echo; kept)
    lv = proj₁ (src-att sa sr)
    Iσ = Parts.iσ pt
    Iβ = Parts.iβ pt

    -- a source pin's connect: at or past the subscription
    past : ∀ {y r} → Frozen k y (pin r) → (c ++ [ ix 1 ]) ≼ r
    past = pin-law (real-snoc c plain-ix (Parts.cr pt)) Iσ

    -- no point of the source's world is one of the body's
    apart : ∀ {y r q e} → Frozen k y (pin r) → β q e → T (inside q r) → ⊥
    apart {_} {r} {q} x b i = Parts.wapart pt (inW (InvAt.world Iβ b)) (proj₁ (InvAt.pinned Iσ x)) (inside-⊑ q r i)

    -- before a row inside the subscription: only rows inside it
    few : ∀ {y} → T (inside (c ++ [ ix 1 ]) y) → Few (Frozen k) y
    few {y} iw with proj₂ (src-att sa sr) sa
    ... | ks , f = ks , g
      where
        g : ∀ {k′ e′} → Frozen k k′ e′ → k′ ≺ y → k′ ∈ ks
        g {k′} x lt with inside (c ++ [ ix 1 ]) k′ in e
        ... | true  = f x (subst T (sym e) tt)
        ... | false = ⊥-elim (≺-irrefl {c ++ [ ix 2 ]} (≼-≺-≺ {c ++ [ ix 2 ]} {k′} {c ++ [ ix 2 ]}
                        (next-slot c k′ (≺→≼ {c ++ [ ix 1 ]} {k′} (world-after (InvAt.world Iσ x) (InvAt.real Iσ x))) (λ t → subst T e t))
                        (≺-trans {k′} {y} {c ++ [ ix 2 ]} lt (in-slot c y iw))))

    -- the body alive after a reached source pin's connect
    alive : ∀ {y r} → Frozen k y (pin r) → Thru C r → Alive r
    alive {y} {r} x tr {q} b with owes? C q
    ... | inj₁ o  = ≼-≢ {r} {q} (thru-owes C tr o) (λ { refl → apart x b (Equivalence.from T-≡ (inside-self r)) })
    ... | inj₂ no with Flags.owing fl (Flags.ended fl lv b no) tr
    ...   | inj₁ rq = ≼-≢ {r} {q} rq (λ { refl → apart x b (Equivalence.from T-≡ (inside-self r)) })
    ...   | inj₂ i  = ⊥-elim (apart x b i)

    -- what a kept row waits on: the source row's, re-pinned, and the
    -- body's rows before the pin's connect, all behind the cursor
    reach : ∀ {y r} → Frozen k y (pin r) → T (inside r y) → Reach (Frozen k) y (pin r) → Thru C r
          → Reach ConnT (y ++ [ ix 0 ]) (pin r)
    reach {y} {r} x ir (ks , f) tr = map (_++ [ ix 0 ]) ks ++ proj₁ bb , g
      where
        ir′ : T (inside r (y ++ [ ix 0 ]))
        ir′ = inside-trans r y (y ++ [ ix 0 ]) ir (⊑-inside {y} {y ++ [ ix 0 ]} ([ ix 0 ] , refl))
        down : ∀ {k′} → (k′ ++ [ ix 0 ]) ≺ r → k′ ≺ r
        down {k′} lt = ≺-trans {k′} {k′ ++ [ ix 0 ]} {r} (≺-ext k′ []) lt
        notc : c ≡ r → ⊥
        notc eq = ≺-irrefl {c} (≺-≼-≺ {c} {c ++ [ ix 1 ]} {c} (≺-ext c []) (subst ((c ++ [ ix 1 ]) ≼_) (sym eq) (past x)))
        g : ∀ {q e′} → ConnT q e′ → q ≺ (y ++ [ ix 0 ]) → (T (inside r (y ++ [ ix 0 ])) → PDep r q e′) → q ∈ map (_++ [ ix 0 ]) ks ++ proj₁ bb
        g (body {q} b) _ d with d ir′
        ... | inj₁ qr = ∈-++⁺ʳ (map (_++ [ ix 0 ]) ks) (proj₂ bb b (λ o → ≺-irrefl {q} (≺-≼-≺ {q} {r} {q} qr (thru-owes C tr o))))
        ... | inj₂ refl = ⊥-elim (Parts.wapart pt (proj₁ (InvAt.pinned Iβ b)) (proj₁ (InvAt.pinned Iσ x)) (W.⊑-refl r))
        g (burst {k′} x′ _) lt d = ∈-++⁺ˡ (∈-map⁺ (_++ [ ix 0 ]) (f x′ (snoc0-≺ k′ y lt) λ _ → h (d ir′)))
          where h : PDep r (k′ ++ [ ix 0 ]) (pin c) → PDep r k′ _
                h (inj₁ lt′) = inj₁ (down {k′} lt′)
                h (inj₂ eq)  = ⊥-elim (notc (pin-inj eq))
        g (echo {k′} x′ _ _ _) lt d = ∈-++⁺ˡ (∈-map⁺ (_++ [ ix 0 ]) (f x′ (snoc0-≺ k′ y lt) λ _ → h (d ir′)))
          where h : PDep r (k′ ++ [ ix 0 ]) skip → PDep r k′ _
                h (inj₁ lt′) = inj₁ (down {k′} lt′)
                h (inj₂ ())
        g (kept {k′} x′ _ _ _) lt d = ∈-++⁺ˡ (∈-map⁺ (_++ [ ix 0 ]) (f x′ (snoc0-≺ k′ y lt) λ _ → h (d ir′)))
          where h : PDep r (k′ ++ [ ix 0 ]) _ → PDep r k′ _
                h (inj₁ lt′) = inj₁ (down {k′} lt′)
                h (inj₂ eq)  = inj₂ (cong pin (pin-inj eq))

    lift : ∀ {y r} → Thru C r → T (inside r y) → Frozen k y (pin r) → Reach (Frozen k) y (pin r)
         → Σ _ λ xs → Σ _ λ r′ → Thru C r′ × T (inside r′ (y ++ xs)) × E (y ++ xs) (pin r′) × Reach E (y ++ xs) (pin r′) × All (_≡ ix 0) xs
    lift {y} {r} tr ir x rc with inside (c ++ [ ix 1 ]) y in e
    ... | true  = let iw = subst T (sym e) tt ; (w , rw) = BurstsAt.win (conn-bursts pt ce) x iw (few iw)
                  in [ ix 0 ] , c , thru-dn C {c} {r} (≺→≼ {c} {r} (≺-≼-≺ {c} {c ++ [ ix 1 ]} {r} (≺-ext c []) (past x))) tr
                   , in-call c y iw , w , rw , refl ∷ []ᴬ
    ... | false = [ ix 0 ] , r , tr , inside-trans r y (y ++ [ ix 0 ]) ir (⊑-inside {y} {y ++ [ ix 0 ]} ([ ix 0 ] , refl))
                , voc (proj₁ ce) (kp , rk) , reach-≈ (proj₁ ce) (reach-img (λ t → _ , proj₁ t , λ eq → eq) rk) , refl ∷ []ᴬ
      where
        kp = kept x (alive x tr) (subst (λ b → T (not b)) (sym e) tt) ir
        rk = reach x ir rc tr


