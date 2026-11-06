{-# OPTIONS --guardedness #-}

-- A NODE OVER ONE SOURCE, ENTERED.  Its rows lie at its source's rows, or
-- a label under one, and its pins are its source's; so each of its rows
-- waits on finitely many, as its source's do, and entering it keeps every
-- row.  A take's failure leaves under the failing value, and no source
-- row lies under a source row, so what lies before it lies before or at
-- the failing value.  What excludes the source's children excludes the
-- node's, whose rows are the source's or its children.
module adequacy.SubOne where

open import Data.Bool using (Bool; true; false; T)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; concatMap)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-concatMap⁺)
open import Data.List.Relation.Unary.Any using (here; there) renaming (map to any-map)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Tree using (Obs)
open import denotation.Events using (Pos; Label; Timeline; ix; last; inside; _<ᵖ_; <ᵖ-split; <ᵖ-step; <ᵖ-over)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; end; pin; Unpinned; Dep; PDep; Reach; Truncate; _≺_; _≼_; ⟦_⟧;
  MapT; map-out; map-skip; map-pin; map-end; module Scan; module TakeWhile)
open import denotation.Laws.Modulus using (≺-absurd; ≺-irrefl; ≺-ext; ≺→≼; ≼-refl; ≼-≺-≺; ≼-or-≻; ≼-false; entered-reach)
open import denotation.Laws.Worlds using (Ok; plain-ix; plain-last; here; InvAt; Hots; ⊑-inside; inside-⊑; world-after)
open import denotation.Laws using (inv-⟦⟧; defer-lim)
open import denotation.Laws.Worlds using (W; W⁼; Plain; inW; nest-in; nest⁼; world-anc⁼; apart; sib; leads; ok-step) renaming (⊑-refl to ⊑ʷ-refl; _⊑_ to _⊑ʷ_; step to wstep)
open import denotation.EmissionSet using (DeferT) renaming (guard to dg; body to db)
open import Tree using (Later; defer)
open import Data.List.Properties using (∷ʳ-injectiveʳ)
open import adequacy.Cursor using (Excl)
open import operation.PureObservable using (module Machine)
open import adequacy.Rows using (full; pendRows; _⇄_)
open import adequacy.Cursor using (_≈_; Within; Sound; Owes; Rgn; Adm)
open import adequacy.Enter using (Anchor; excl-anchor; within-sound; excl-root)
open import denotation.Read using (Visible)
open import adequacy.PinLift using (tk)
open import adequacy.Bound using (owes-≼; good-full)
open Machine using (Scope)

------------------------------------------------------------------------
-- Entering keeps every row that waits on finitely many.

trunc-≈ : ∀ {A} {E : EmissionSet A} → (∀ {y e} → E y e → Reach E y e) → E ≈ Truncate E
trunc-≈ rc = record { alike = (λ (x , v) → (x , rc x) , v) ⇄ (λ ((x , _) , v) → x , v)
                    ; cov   = [] , λ x → inj₁ (proj₁ x)
                    ; voc   = λ x → x , rc x }

-- Each row of `E′` read off a row of `E` at or before it, among its
-- `g`-images, a pin off the same pin.
Lifted : ∀ {A B} → (Pos → List Pos) → EmissionSet A → EmissionSet B → Set
Lifted {A} g E E′ = ∀ {k′ e′} → E′ k′ e′ → Σ Pos λ k → Σ (Ev A) λ e → E k e × k ≼ k′ × k′ ∈ g k × (∀ {r} → e′ ≡ pin r → e ≡ pin r)

-- An unpinned row waits on everything before it.
dep-un : ∀ {A} {q} {e : Ev A} → Unpinned e → ∀ {k e′} → Dep q e k e′
dep-un {e = out _} _ = tt
dep-un {e = skip}  _ = tt
dep-un {e = end}   _ = tt
dep-un {e = pin _} ()

-- What a lifted row waits on, its source row waits on.
dep-lift : ∀ {A B} {y} (e : Ev B) {e₀ : Ev A} {k k′} {e′ : Ev B} {e″ : Ev A}
         → (∀ {r} → e ≡ pin r → e₀ ≡ pin r) → (Unpinned e → Unpinned e₀) → k ≼ k′
         → (∀ {r} → e′ ≡ pin r → e″ ≡ pin r) → Dep y e k′ e′ → Dep y e₀ k e″
dep-lift {y = y} (pin r) {e₀} {k} {k′} {e′} {e″} p _ le pq d = subst (λ x → Dep y x k e″) (sym (p refl)) (λ i → pd (d i))
  where
    pd : PDep r k′ e′ → PDep r k e″
    pd (inj₁ lt) = inj₁ (≼-≺-≺ {k} {k′} {r} le lt)
    pd (inj₂ eq) = inj₂ (pq eq)
dep-lift (out _) _ u _ _ _ = dep-un (u tt)
dep-lift skip    _ u _ _ _ = dep-un (u tt)
dep-lift end     _ u _ _ _ = dep-un (u tt)

lift-in : ∀ (g : Pos → List Pos) {k k′ ks} → k′ ∈ g k → k ∈ ks → k′ ∈ concatMap g ks
lift-in g m kk = ∈-concatMap⁺ g (any-map (λ { refl → m }) kk)

reach-lift : ∀ {A B} {E : EmissionSet A} {E′ : EmissionSet B} (g : Pos → List Pos) → Lifted g E E′
           → ∀ {y e e₀} → (∀ {r} → e ≡ pin r → e₀ ≡ pin r) → (Unpinned e → Unpinned e₀) → Reach E y e₀ → Reach E′ y e
reach-lift {E′ = E′} g lf {y} {e} {e₀} pp up (ks , h) = concatMap g ks , pick
  where
    pick : ∀ {k′ e′} → E′ k′ e′ → k′ ≺ y → Dep y e k′ e′ → k′ ∈ concatMap g ks
    pick {k′} x ky d with lf x
    ... | k , _ , x′ , le , m , pq = lift-in g m (h x′ (≼-≺-≺ {k} {k′} {y} le ky) (dep-lift e pp up le pq d))

-- Every row of a node at its own place.
lift-reach : ∀ {A B} {E : EmissionSet A} {E′ : EmissionSet B} (g : Pos → List Pos) → Lifted g E E′ → (∀ {y e} → E y e → Reach E y e)
           → ∀ {y} e {e₀} → E y e₀ → (∀ {r} → e ≡ pin r → e₀ ≡ pin r) → (Unpinned e → Unpinned e₀) → Reach E′ y e
lift-reach g lf rc e x pp up = reach-lift g lf {e = e} pp up (rc x)

------------------------------------------------------------------------
-- A map and a scan: each row at its source row's place.

map-lift : ∀ {A B} {f : A → B} {E : EmissionSet A} → Lifted [_] E (MapT f E)
map-lift (map-out {q} x)  = q , _ , x , ≼-refl {q} , here refl , λ ()
map-lift (map-skip {q} x) = q , _ , x , ≼-refl {q} , here refl , λ ()
map-lift (map-pin {q} x)  = q , _ , x , ≼-refl {q} , here refl , λ { refl → refl }
map-lift (map-end {q} x)  = q , _ , x , ≼-refl {q} , here refl , λ ()

map-reach : ∀ {A B} {f : A → B} {E : EmissionSet A} → (∀ {y e} → E y e → Reach E y e) → ∀ {y e} → MapT f E y e → Reach (MapT f E) y e
map-reach {f = f} rc (map-out {a = a} x) = lift-reach [_] map-lift rc (out (f a)) x (λ ()) (λ _ → tt)
map-reach rc (map-skip x)          = lift-reach [_] map-lift rc skip x (λ ()) (λ _ → tt)
map-reach rc (map-pin {r = r} x)   = lift-reach [_] map-lift rc (pin r) x (λ { refl → refl }) (λ ())
map-reach rc (map-end x)           = lift-reach [_] map-lift rc end x (λ ()) (λ _ → tt)

acc-at : ∀ {A B} {f : B → A → B} {z} {E : EmissionSet A} {q b} → Scan.Acc f z E q b → Σ A λ a → E q (out a)
acc-at (Scan.acc₀ x _)    = _ , x
acc-at (Scan.acc _ x _ _) = _ , x

scan-lift : ∀ {A B} {f : B → A → B} {z} {E : EmissionSet A} → Lifted [_] E (Scan.ScanT f z E)
scan-lift (Scan.sval {q} a)  = q , _ , proj₂ (acc-at a) , ≼-refl {q} , here refl , λ ()
scan-lift (Scan.sstep {q} x) = q , _ , x , ≼-refl {q} , here refl , λ ()
scan-lift (Scan.spin {q} x)  = q , _ , x , ≼-refl {q} , here refl , λ { refl → refl }
scan-lift (Scan.send {q} x)  = q , _ , x , ≼-refl {q} , here refl , λ ()

scan-reach : ∀ {A B} {f : B → A → B} {z} {E : EmissionSet A} → (∀ {y e} → E y e → Reach E y e)
           → ∀ {y e} → Scan.ScanT f z E y e → Reach (Scan.ScanT f z E) y e
scan-reach rc (Scan.sval {b = b} a) = lift-reach [_] scan-lift rc (out b) (proj₂ (acc-at a)) (λ ()) (λ _ → tt)
scan-reach rc (Scan.sstep x) = lift-reach [_] scan-lift rc skip x (λ ()) (λ _ → tt)
scan-reach rc (Scan.spin {r = r} x) = lift-reach [_] scan-lift rc (pin r) x (λ { refl → refl }) (λ ())
scan-reach rc (Scan.send x)  = lift-reach [_] scan-lift rc end x (λ ()) (λ _ → tt)

------------------------------------------------------------------------
-- A take: a failure's rows a label under the failing value.

take-lift : ∀ {A} {incl} {keep : A → Bool} {E : EmissionSet A} → Lifted tk E (TakeWhile.TakeT incl keep E)
take-lift (TakeWhile.pass {q} x _ _)   = q , _ , x , ≼-refl {q} , here refl , λ ()
take-lift (TakeWhile.fail {q} x _ _ _) = q , _ , x , ≺→≼ {q} {q ++ [ ix 0 ]} (≺-ext q []) , there (here refl) , λ ()
take-lift (TakeWhile.stop {q} x _ _)   = q , _ , x , ≺→≼ {q} {q ++ [ last ]} (≺-ext q []) , there (there (here refl)) , λ ()
take-lift (TakeWhile.step {q} x _)     = q , _ , x , ≼-refl {q} , here refl , λ ()
take-lift (TakeWhile.tend {q} x _)     = q , _ , x , ≼-refl {q} , here refl , λ ()
take-lift (TakeWhile.left {q} x _ _)   = q , _ , x , ≼-refl {q} , here refl , λ { refl → refl }

-- Before a label under `q`: at or before `q`, or under it.
below-or-under : ∀ k q l → k ≺ (q ++ [ l ]) → k ≼ q ⊎ Σ Label λ l′ → Σ Pos λ ls → k ≡ q ++ l′ ∷ ls
below-or-under k q l lt with ≼-or-≻ k q
... | inj₁ le = inj₁ le
... | inj₂ qk = inj₂ (under (inside q k) refl)
  where
    under : ∀ b → inside q k ≡ b → Σ Label λ l′ → Σ Pos λ ls → k ≡ q ++ l′ ∷ ls
    under true ins with inside-⊑ q k (subst T (sym ins) tt)
    ... | l′ ∷ ls , eq = l′ , ls , eq
    ... | [] , eq      = ⊥-elim (≺-irrefl {q} (subst (q ≺_) (trans eq (++-identityʳ q)) qk))
    under false ins = ⊥-elim (≺-absurd {k} {q ++ [ l ]} lt (Equivalence.from T-≡ (<ᵖ-over q k [ l ] step none)))
      where
        none : ∀ l′ ls → k ≡ q ++ l′ ∷ ls → ⊥
        none l′ ls eq = subst T ins (⊑-inside {q} {k} (l′ ∷ ls , eq))
        step : (q ++ [ ix 0 ]) <ᵖ k ≡ true
        step with <ᵖ-split (q ++ [ ix 0 ]) k (<ᵖ-step q k (Equivalence.to T-≡ qk))
        ... | inj₁ t  = t
        ... | inj₂ eq = ⊥-elim (none (ix 0) [] (sym eq))

at-or-before : ∀ {k q} → k ≼ q → k ≡ q ⊎ k ≺ q
at-or-before {k} {q} le with <ᵖ-split k q (≼-false {k} {q} le)
... | inj₁ t  = inj₂ (Equivalence.from T-≡ t)
... | inj₂ eq = inj₁ eq

-- A row a label under a source value, with no source row under a source
-- row, waits on what that value waits on, and on it.
under-reach : ∀ {A B} {E : EmissionSet A} {E′ : EmissionSet B} (g : Pos → List Pos) → Lifted g E E′
            → (∀ {y e l ys e′} → E y e → E (y ++ l ∷ ys) e′ → ⊥)
            → ∀ {q a l e} → E q (out a) → Reach E q (out a) → Reach E′ (q ++ [ l ]) e
under-reach {E = E} {E′} g lf flat {q} {a} {l} {e} x₀ (ks , h) = concatMap g (q ∷ ks) , pick
  where
    pick : ∀ {k′ e′} → E′ k′ e′ → k′ ≺ (q ++ [ l ]) → Dep (q ++ [ l ]) e k′ e′ → k′ ∈ concatMap g (q ∷ ks)
    pick {k′} x ky _ with lf x
    ... | k , _ , x′ , le , m , _ = lift-in g m (at (below-or-under k q l (≼-≺-≺ {k} {k′} {q ++ [ l ]} le ky)))
      where
        at : k ≼ q ⊎ Σ Label (λ l′ → Σ Pos λ ls → k ≡ q ++ l′ ∷ ls) → k ∈ q ∷ ks
        at (inj₁ kq) with at-or-before {k} {q} kq
        ... | inj₁ eq = here eq
        ... | inj₂ lt = there (h x′ lt tt)
        at (inj₂ (l′ , ls , eq)) = ⊥-elim (flat x₀ (subst (λ y → E y _) eq x′))

take-reach : ∀ {A} {incl} {keep : A → Bool} {E : EmissionSet A} → (∀ {y e} → E y e → Reach E y e)
           → (∀ {y e l ys e′} → E y e → E (y ++ l ∷ ys) e′ → ⊥)
           → ∀ {y e} → TakeWhile.TakeT incl keep E y e → Reach (TakeWhile.TakeT incl keep E) y e
take-reach rc fl (TakeWhile.pass {a = a} x _ _) = lift-reach tk take-lift rc (out a) x (λ ()) (λ _ → tt)
take-reach rc fl (TakeWhile.fail {a = a} x _ _ _) = under-reach tk take-lift fl {l = ix 0} {e = out a} x (rc x)
take-reach rc fl (TakeWhile.stop x _ _)   = under-reach tk take-lift fl {l = last} {e = end} x (rc x)
take-reach rc fl (TakeWhile.step x _)     = lift-reach tk take-lift rc skip x (λ ()) (λ _ → tt)
take-reach rc fl (TakeWhile.tend x _)     = lift-reach tk take-lift rc end x (λ ()) (λ _ → tt)
take-reach rc fl (TakeWhile.left {r = r} x _ _) = lift-reach tk take-lift rc (pin r) x (λ { refl → refl }) (λ ())

------------------------------------------------------------------------
-- Its source's region: what excludes the source's children excludes the
-- node's, whose rows are the source's or a plain label under one.

Placed : ∀ {A B} → (Pos → Set) → EmissionSet A → EmissionSet B → Set
Placed H E E′ = ∀ {k e} → E′ k e → Anchor H E k

placed-trunc : ∀ {A B H} {E : EmissionSet A} {E′ : EmissionSet B} → Placed H E E′ → Placed H E (Truncate E′)
placed-trunc pl x = pl (proj₁ x)

map-placed : ∀ {A B H} {f : A → B} {E : EmissionSet A} → Placed H E (MapT f E)
map-placed (map-out x)  = inj₁ (_ , x)
map-placed (map-skip x) = inj₁ (_ , x)
map-placed (map-pin x)  = inj₁ (_ , x)
map-placed (map-end x)  = inj₁ (_ , x)

scan-placed : ∀ {A B H} {f : B → A → B} {z} {E : EmissionSet A} → Placed H E (Scan.ScanT f z E)
scan-placed (Scan.sval a)  = inj₁ (_ , proj₂ (acc-at a))
scan-placed (Scan.sstep x) = inj₁ (_ , x)
scan-placed (Scan.spin x)  = inj₁ (_ , x)
scan-placed (Scan.send x)  = inj₁ (_ , x)

take-placed : ∀ {A H} {incl} {keep : A → Bool} {E : EmissionSet A} → Placed H E (TakeWhile.TakeT incl keep E)
take-placed (TakeWhile.pass x _ _)           = inj₁ (_ , x)
take-placed (TakeWhile.fail {q} {a} x _ _ _) = inj₂ (q , out a , ix 0 , x , plain-ix , here)
take-placed (TakeWhile.stop {q} {a} x _ _)   = inj₂ (q , out a , last , x , plain-last , here)
take-placed (TakeWhile.step x _)             = inj₁ (_ , x)
take-placed (TakeWhile.tend x _)             = inj₁ (_ , x)
take-placed (TakeWhile.left x _ _)           = inj₁ (_ , x)

------------------------------------------------------------------------
-- The source subscribed at `q` under a node: the node's rows its own
-- truncation, the source's region and soundness the node's, every source
-- row owed where `q` is.

module Entry {Γ A} (sc : Scope Γ) (s : Obs Timeline Γ A) (q : Pos) (ok : Ok (Hots (full sc)) q) (ad : Adm sc) where
  S : EmissionSet A
  S = pendRows (full sc) s q

  Io : InvAt (Hots (full sc)) q S
  Io = inv-⟦⟧ s (full sc) (good-full sc ad) q ok

  rc : ∀ {y e} → S y e → Reach S y e
  rc = entered-reach (⟦ s ⟧ (full sc)) q

  entry : ∀ {B} {N : EmissionSet B} {Rg : Rgn} → (∀ {y e} → N y e → Reach N y e) → Placed (Hots (full sc)) S N
        → Within Rg sc q (Truncate N) → N ≈ Truncate N × Sound Rg S × Within Rg sc q S
  entry {N = N} {Rg = Rg} nr pl wi = trunc-≈ nr , within-sound {sc = sc} Io wi′ , wi′
    where
      wi′ : Within Rg sc q S
      wi′ = proj₁ wi , λ wy ex → proj₂ wi wy (excl-anchor {E′ = Truncate N} (placed-trunc pl) ex)

  map-entry : ∀ {B} {f : A → B} {Rg : Rgn} → Within Rg sc q (Truncate (MapT f S))
            → MapT f S ≈ Truncate (MapT f S) × Sound Rg S × Within Rg sc q S
  map-entry = entry (map-reach rc) map-placed

  scan-entry : ∀ {B} {f : B → A → B} {z} {Rg : Rgn} → Within Rg sc q (Truncate (Scan.ScanT f z S))
             → Scan.ScanT f z S ≈ Truncate (Scan.ScanT f z S) × Sound Rg S × Within Rg sc q S
  scan-entry = entry (scan-reach rc) scan-placed

  take-entry : ∀ {i} {keep : A → Bool} {Rg : Rgn} → Within Rg sc q (Truncate (TakeWhile.TakeT i keep S))
             → TakeWhile.TakeT i keep S ≈ Truncate (TakeWhile.TakeT i keep S) × Sound Rg S × Within Rg sc q S
  take-entry = entry (take-reach rc (InvAt.flat Io)) take-placed

  -- Every source row lies past its subscription.
  owed : ∀ {C} → Owes C q → ∀ {y e} → S y e → Owes C y
  owed {C} ow x = owes-≼ C {q} ow (≺→≼ {q} (world-after (InvAt.world Io x) (InvAt.real Io x)))

------------------------------------------------------------------------
-- A DEFER SUBSCRIBED: its body entered at its second child, owing what the
-- defer owed but its guard, a skip no reader meets.  What lies in the
-- body's world lies in the defer's, and no world below the guard leads
-- it, the guard's and the body's being sibling worlds.

module DeferEntry {Γ A} (sc : Scope Γ) (l : Later Timeline Γ A) (q : Pos) (ok : Ok (Hots (full sc)) q) (ad : Adm sc) where
  H : Pos → Set
  H = Hots (full sc)

  b = ⟦ Later.force l ⟧ (full sc)

  B D : EmissionSet A
  B = pendRows (full sc) (Later.force l) (q ++ [ ix 1 ])
  D = pendRows (full sc) (defer l) q

  out-d : ∀ {r e} → D r e → DeferT b q r e
  out-d x = proj₁ (proj₁ (defer-lim l (full sc) (good-full sc ad) q ok) x)

  reach-d : ∀ {r e} → B r e → Reach (DeferT b q) r e
  reach-d x with entered-reach b (q ++ [ ix 1 ]) x
  ... | ks , h = (q ++ [ ix 0 ]) ∷ ks , λ { dg _ _ → here refl ; (db y) lt d → there (h y lt d) }

  into : ∀ {r e} → B r e → D r e
  into x = proj₂ (defer-lim l (full sc) (good-full sc ad) q ok) (db x , reach-d x)

  -- The guard's children's worlds lead nothing of the body's world.
  guard-apart : ∀ {y l′ w} → W⁼ H (q ++ [ ix 1 ]) y → Plain l′ → W⁼ H ((q ++ [ ix 0 ]) ++ [ l′ ]) w → w ⊑ʷ y → ⊥
  guard-apart wy pl v le = leads (proj₁ ok) (proj₂ ok) (nest-in (wstep here plain-ix) w0) nb nr wy le
    where
      w0 = nest⁼ (inW (wstep here pl)) v
      nb : W⁼ H (q ++ [ ix 1 ]) _ → ⊥
      nb u = apart (proj₁ ok) (world-anc⁼ w0) (world-anc⁼ u)
      nr : _ ⊑ʷ (q ++ [ ix 1 ]) → ⊥
      nr = sib (proj₁ ok) plain-ix (⊑ʷ-refl q) (λ eq → ix10 (∷ʳ-injectiveʳ q q eq)) w0
        where ix10 : ix 1 ≡ ix 0 → ⊥
              ix10 ()

  excl-d : ∀ {y r e l′ w} → W⁼ H (q ++ [ ix 1 ]) y → Excl H B y → DeferT b q r e → Plain l′ → W⁼ H (r ++ [ l′ ]) w → w ⊑ʷ y → ⊥
  excl-d wy ex dg     pl v le = guard-apart wy pl v le
  excl-d wy ex (db x) pl v le = ex x pl v le

  into-w : ∀ {y} → W⁼ H (q ++ [ ix 1 ]) y → W H q y
  into-w = nest-in (wstep here plain-ix)

  entry : ∀ {Rg : Rgn} → Within Rg sc q D → B ≈ D × Within Rg sc (q ++ [ ix 1 ]) B
  entry wi = record { alike = (λ (x , v) → into x , v) ⇄ vis-b ; cov = [ q ++ [ ix 0 ] ] , cv ; voc = into }
           , proj₂ wi (into-w here) (λ x → excl-d here (excl-root Ib (proj₁ (ok-step q ok))) (out-d x))
           , λ wy ex → proj₂ wi (into-w (inW wy)) (λ x → excl-d (inW wy) ex (out-d x))
    where
      vis-b : ∀ {y e} → D y e × Visible e → B y e × Visible e
      vis-b (x , v) with out-d x
      ... | dg   = ⊥-elim v
      ... | db y = y , v
      cv : ∀ {y e} → D y e → B y e ⊎ y ∈ [ q ++ [ ix 0 ] ]
      cv x with out-d x
      ... | dg   = inj₂ (here refl)
      ... | db y = inj₁ y
      Ib = inv-⟦⟧ (Later.force l) (full sc) (good-full sc ad) (q ++ [ ix 1 ]) (ok-step q ok)
