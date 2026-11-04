{-# OPTIONS --guardedness #-}

-- A PIN SHOWS ONE LAYER UP: what a dead node's closure says of each
-- former.  A former that keeps pins in place shows a pin at its own row;
-- a cursor that has moved on has passed whatever its earlier self had.
module adequacy.Cursor.Show where

open import Data.Bool using (Bool; T; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List using ([]; _∷_; [_]; _++_; map)
open import Data.List.Properties using (++-identityʳ; ++-assoc; ∷ʳ-injectiveˡ; ∷ʳ-injectiveʳ)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)
open import Relation.Nullary using (¬_)

open import Tree using (Obs)
open import denotation.Events using (Timeline; ix; inside; <ᵖ-step; _<ᵖ_; <ᵖ-split; inside-++; inside-self)
open import denotation.EmissionSet using (EmissionSet; Ev; out; pin; _≺_; _≼_; Reach; Few; PDep; module Connecting; MapT; map-pin; ⟦_⟧; module Scan; module TakeWhile)
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
  Src; bursts)
open import denotation.Laws.Worlds using (Hots; Real; InvAt; W⁼; here; inW; step; timer; join; real-snoc; plain-ix; real-init; nonempty⁼; world-after; world-after⁼; inside-⊑; ⊑-inside)
open import adequacy.Bound using (next-slot)
open import adequacy.PinLift using (reach-≈; reach-img; reach-map; reach-scan; reach-take)

-- What the cursor reached lies at or before all it owes.
thru-owes : ∀ C {r q} → Thru C r → Owes C q → r ≼ q
thru-owes origin  ()
thru-owes (bef p) {r} {q} t o = ≼-trans {r} {p} {q} t o
thru-owes (aft p) {r} {q} t o = ≺→≼ {r} {q} (≼-≺-≺ {r} {p} {q} t o)

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
  -- A JOINER'S OUTER PIN SHOWS IN ITS ENTRY: kept by `opin`, and waiting
  -- in the joiner's rows on no more than it did in the outer's, but for
  -- the rows before its connect, which the cursor has behind it.
  flat-up-outer : ∀ {Γ} {sc : Scope Γ} {Rg C A B} {op} {f : A → Obs Timeline Γ B} {ω O E}
                → JInv sc f O → Sound (JRo sc Rg op f O) O → JoinE sc op f ω O E → Behind C (JoinF op (λ a → ⟦ f a ⟧ (full sc)) O)
                → Up C O C E

  -- A LANE'S PIN SHOWS IN ITS JOINER'S ENTRY: no kill before its connect,
  -- so `left` keeps it.
  flat-up-lane : ∀ {Γ} {sc : Scope Γ} {Rg C D A B} {op} {f : A → Obs Timeline Γ B} {ω O E q a}
               → JInv sc f O → JoinE sc op f ω O E → Behind C (JoinF op (λ a → ⟦ f a ⟧ (full sc)) O)
               → LanesIn (Hots (full sc)) (JRl sc Rg op f O) (polF op (λ a → ⟦ f a ⟧ (full sc)) O) O
               → O q (out a) → Runs (polF op (λ a → ⟦ f a ⟧ (full sc)) O) q
               → Dom C D → (∀ {r} → Thru D r → NoKill (polF op (λ a → ⟦ f a ⟧ (full sc)) O) q r)
               → Up D (Lane (polF op (λ a → ⟦ f a ⟧ (full sc)) O) q a) C E

  -- A CONNECT'S BODY PIN SHOWS IN ITS ENTRY, kept by `body`.
  conn-up-body : ∀ {Γ X B} {sc : Scope Γ} {Rg C} {k : CS Γ X} {o} {β E : EmissionSet B}
               → CS.scope k ≡ sc → (pt : Parts sc Rg k β) → Src sc (Parts.Rs pt) C k o → Behind C β → Flags C k β
               → ConnE (CS.connAt k) (Frozen k) β E → Up C β C E

  -- AN ATTACHED SOURCE'S PIN SHOWS IN ITS CONNECT'S ENTRY: inside the
  -- subscription re-pinned to the connect by `burst`, its few rows there
  -- behind it; past it kept by `kept`, the body alive after it.
  conn-up-src : ∀ {Γ X B} {sc : Scope Γ} {Rg C} {k : CS Γ X} {o} {β E : EmissionSet B}
              → T (CS.srcAtt k) → CS.scope k ≡ sc → (pt : Parts sc Rg k β) → Src sc (Parts.Rs pt) C k o → Behind C β → Flags C k β
              → ConnE (CS.connAt k) (Frozen k) β E → Up C (Frozen k) C E


