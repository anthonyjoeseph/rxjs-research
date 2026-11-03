{-# OPTIONS --guardedness #-}

-- A PIN SHOWS ONE LAYER UP: what a dead node's closure says of each
-- former.  A former that keeps pins in place shows a pin at its own row;
-- a cursor that has moved on has passed whatever its earlier self had.
module adequacy.Cursor.Show where

open import Data.Bool using (Bool; T; not)
open import Data.List using ([]; _∷_; [_]; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import Relation.Nullary using (¬_)

open import Tree using (Obs)
open import denotation.Events using (Pos; Timeline; ix; inside; <ᵖ-step)
open import denotation.EmissionSet using (EmissionSet; out; pin; _≺_; _≼_; Reach; MapT; map-pin; ⟦_⟧; module Scan; module TakeWhile)
open import denotation.Laws.Modulus using (≺→≼; ≺-ext; ≺-trans; ≺-irrefl; ≼-refl; ≼-trans; ≺-≼-≺; ≼-≺-≺)
open import Data.Bool.Properties using (T-≡)
open import Function.Bundles using (Equivalence)
open import Data.Unit using (tt)
open import operation.PureObservable using (module Machine)
open Machine using (Scope; CS)
open import adequacy.Rows using (Frozen; full)
open import adequacy.Cursor using (Cur; origin; bef; aft; Thru; Owes; Dom; Up; Bursts; _≈_; voc; NoFail; NoKill; Unkilled; Pol; Runs; Lane; polF; up; JoinF; JoinE; JInv;
  JRo; JRl; LanesIn; Sound; Behind; Parts; Flags; ConnE; Src)
open import denotation.Laws.Worlds using (Hots)
open import adequacy.PinLift using (reach-≈; reach-map; reach-scan; reach-take)

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
                    , subst (λ z → Reach E′ z (pin r)) (sym (++-identityʳ y)) rc′

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
up-∘ {E₃ = E₃} (up u) (up v) = up λ {y} nr i x rc → let (xs , r′ , n′ , i′ , x′ , rc′) = u nr i x rc ; (zs , r″ , n″ , i″ , x″ , rc″) = v n′ i′ x′ rc′ in xs ++ zs , r″ , n″
    , subst (λ z → T (inside r″ z)) (++-assoc y xs zs) i″
    , subst (λ z → E₃ z (pin r″)) (++-assoc y xs zs) x″
    , subst (λ z → Reach E₃ z (pin r″)) (++-assoc y xs zs) rc″

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

  -- AN ISLE'S BURST SHOWS IN ITS CONNECT'S ENTRY: `burst` pins each row of
  -- the subscription, and nothing before the connect is in it.
  conn-bursts : ∀ {Γ X B} {sc : Scope Γ} {Rg C} {k : CS Γ X} {o} {β E : EmissionSet B}
              → T (not (CS.srcAtt k)) → CS.scope k ≡ sc → (pt : Parts sc Rg k β) → Src sc (Parts.Rs pt) C k o → Behind C β → Flags C k β
              → ConnE (CS.connAt k) (Frozen k) β E → Bursts k E

