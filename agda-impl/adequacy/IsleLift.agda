{-# OPTIONS --guardedness #-}

-- AN ISLE'S ROW, CLIMBED TO THE ROOT: a row an isle's source makes in its
-- subscribe call, at the step or down the step's first-child chain, shown
-- as a pin of its connect's entry and carried frame by frame to a pin of
-- the root's, still on the chain.
--
-- An enclosing source still in its subscribe call shows a pin inside its
-- subscription only if its rows before the pin are few.  Those are read
-- at the step, off the hole's rows: frame by frame, finitely many owed
-- before the step (`HR`), the cursor having passed the rest; and in a
-- part no live node reads, finitely many of what it still runs before
-- the step (`PLag`).  The enclosing world's own cursor need not reach the
-- step.
module adequacy.IsleLift where

open import Data.Bool using (T; true; false)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (reverse⁺)
open import Data.List.Relation.Unary.All using (All; _∷_) renaming ([] to []ᴬ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import denotation.Position using (Pos; ix; inside; _⊕_; Path)
open import denotation.Events using (inside-self; <ᵖ-split)
open import denotation.EmissionSet using (EmissionSet; pin; Reach; Few; _≺_; _≼_; ⟦_⟧)
open import denotation.Laws.Modulus using (≼-false; ≼-or-≻; ≼-refl; ≺-ext; ≺-trans; ≼-antisym)
open import denotation.Laws.BoundedInv using (first-child)
open import denotation.Laws.Worlds using (⊑-inside; ⊕-assoc; ⊕-identityʳ)
open import operation.Key using (at)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; CS; plug; connS; mapS; scanS; cutS; lnS; takeS; flatS; binds; scopeOf;
                    inOuter; inLanes; inSrc; inBody; inTake)
open import adequacy.Rows using (Frozen; full; module _≃_)
open _≃_ using (from)
open import adequacy.Cursor using (Cur; bef; Thru; Dom; Up; UpA; upa; BurstsAt; Bursts; Behind; alike; ≈-refl; Husk; Burst;
  Subd; SubdAt; AttOwed; _⊑_; _∪ᵖ_; Pts; Hole; h-live; h-end; h-kill; notT; Pol; Kept; Owes;
  polF)
open import adequacy.Cursor.Frame using (Need; owes; dead; lane; lanecut; pnd; ⊥₁; Fr; Unread; un-dead; un-torn;
  f-top; f-map; f-scan; f-cut; f-take; f-took; f-outer; f-lanes; f-lane; f-lnct; f-src; f-srcc; f-srcp; f-body;
  d-map; d-scan; d-cut; d-ln; d-take; d-outer; d-lanes; d-src; d-body; f-isle; f-islec; f-islep)
open import adequacy.Cursor.Show using (up-≈; upa-of; thru-up0; up-map; up-scan; up-take; up-adv; up-∘; up-pre; nofail-up; unkilled-no; thru-sub; thru-dn; thru-few;
  flat-up-outer; flat-up-lane; conn-up-body; conn-up-src; conn-bursts; in-call; inside-trans)
open import adequacy.Cursor.Tear using (by)
open import adequacy.FrShift using (HR; hr; hr-map; hr-outer; hr-lanes; hr-src; hr-body; live-kl; body-env)
open import adequacy.Few using (lag; EnvL; lag-≈; lag-at; map-row; scan-row; take-lag; PLag; plag-∪; plag-under; tailp-lag;
  before; burst-plag; husk-f; huskl-f; srch-f; subd-env; att-slot)
open import adequacy.Bound using (LoP; Env; lo-p; map-b; scan-b; take-b; took-b; ≮-after; ≮-≼; body-key)
open import adequacy.FrameBound using (conn-fb; pre-in; post-in)
open import adequacy.Least using (Lo; k-own; k-kid; k-lane; k-outer; k-body; k-src)
open import adequacy.Floor.Keys using (plug-in; own-bld; os)

------------------------------------------------------------------------
-- THE STEP'S FIRST-CHILD CHAIN

-- The first-child chain below `q`: `q ⊕ [ ix 0 ]`, and each first child
-- of one.
data Zs (q : Pos) : Pos → Set where
  z₁ : Zs q (q ⊕ [ ix 0 ])
  z+ : ∀ {y} → Zs q y → Zs q (y ⊕ [ ix 0 ])

-- A chain's foot past its head.
zs-past : ∀ {q y} → Zs q y → q ≺ y
zs-past {q} z₁ = ≺-ext q []
zs-past {q} (z+ {y} z) = ≺-trans {q} {y} {y ⊕ [ ix 0 ]} (zs-past z) (≺-ext y [])

-- The positions from `q` up to, not including, the chain's foot.
zl : ∀ {q y} → Zs q y → List Pos
zl {q} z₁       = [ q ]
zl (z+ {y} z) = y ∷ zl z

-- Between `q` and a first-child chain's foot: on the chain.
zs-btw : ∀ {q y w} (z : Zs q y) → q ≼ w → w ≺ y → w ∈ zl z
zs-btw {q} {w = w} z₁ qw wy with <ᵖ-split q w (≼-false {q} {w} qw)
... | inj₁ lt   = ⊥-elim (first-child q (Equivalence.from T-≡ lt) wy)
... | inj₂ refl = here refl
zs-btw {w = w} (z+ {y} z) qw wy with ≼-or-≻ y w
... | inj₂ wy′ = there (zs-btw z qw wy′)
... | inj₁ yw with <ᵖ-split y w (≼-false {y} {w} yw)
...   | inj₁ lt   = ⊥-elim (first-child y (Equivalence.from T-≡ lt) wy)
...   | inj₂ refl = here refl

-- A chain's foot lies under the first child.
zs-under : ∀ {q y} → Zs q y → Σ Path λ xs → y ≡ (q ⊕ [ ix 0 ]) ⊕ xs
zs-under z₁ = [] , sym (⊕-identityʳ _)
zs-under (z+ {y} z) with zs-under z
... | xs , refl = xs ++ [ ix 0 ] , ⊕-assoc _ xs [ ix 0 ]

-- A chain's foot lies inside its head.
zs-in : ∀ {q y} → Zs q y → T (inside q y)
zs-in {q} z with zs-under z
... | xs , refl = ⊑-inside {q} {(q ⊕ [ ix 0 ]) ⊕ xs} (ix 0 ∷ xs , ⊕-assoc q [ ix 0 ] xs)

-- First children on from a chain's foot: still on it.
zs-all : ∀ {q y} xs → Zs q y → All (_≡ ix 0) xs → Zs q (y ⊕ xs)
zs-all {q} {y} []       z []ᴬ         = subst (Zs q) (sym (⊕-identityʳ y)) z
zs-all {q} {y} (_ ∷ xs) z (refl ∷ a) = subst (Zs q) (⊕-assoc y [ ix 0 ] xs) (zs-all xs (z+ z) a)

-- Few rows before the chain's head: few before its foot, the chain
-- itself between.
chain-few : ∀ {A} {F : EmissionSet A} {q y} → Few F q → Zs q y → Few F y
chain-few {q = q} (ks , f) z = ks ++ zl z , λ {k} x ky →
  [ (λ qk → ∈-++⁺ʳ ks (zs-btw z qk ky)) , (λ kq → ∈-++⁺ˡ (f x kq)) ]′ (≼-or-≻ q k)

------------------------------------------------------------------------
-- A PIN ON THE CHAIN: a pin of `E` on the step's first-child chain, its
-- connect reached at `D`, finitely many rows it waits on.

data Pin {A} (D : Cur) (E : EmissionSet A) (q : Pos) : Set where
  pn : ∀ {y r} → Thru D r → T (inside r y) → E y (pin r) → Reach E y (pin r) → Zs q y → Pin D E q

upa-pin : ∀ {A B} {D D′} {E : EmissionSet A} {E′ : EmissionSet B} {q} → UpA D E D′ E′ → Pin D E q → Pin D′ E′ q
upa-pin (upa u) (pn tr ir x rc z) with u tr ir x rc
... | xs , _ , tr′ , ir′ , x′ , rc′ , a = pn tr′ ir′ x′ rc′ (zs-all xs z a)

up-pin : ∀ {A B} {D D′} {E : EmissionSet A} {E′ : EmissionSet B} {q} → Up D E D′ E′ → Pin D E q → Pin D′ E′ q
up-pin u = upa-pin (upa-of u)

pin-dom : ∀ {A} {C D} {E : EmissionSet A} {q} → Dom C D → Pin D E q → Pin C E q
pin-dom dm (pn tr ir x rc z) = pn (dm tr) ir x rc z

-- A part's few points before `p`, read through what covers it.
⊑-plag : ∀ {p} {P Q : Pts} → P ⊑ Q → PLag p Q → PLag p P
⊑-plag (ks , f) (ls , g) = ls ++ ks , λ x yp → [ (λ qy → ∈-++⁺ˡ (g qy yp)) , ∈-++⁺ʳ ls ]′ (f x)

-- A source's pin a level down, in its connect's entry: inside the
-- subscription, its burst, the source's rows before it few; past it,
-- kept, its connect no later than the slot after the subscription.
burst-pin : ∀ {X B} {F : EmissionSet X} {c} {E : EmissionSet B} {C D q}
          → BurstsAt F c E → Thru D c → (∀ {r} → Thru C r → r ≼ (c ⊕ [ ix 2 ])) → (∀ {r} → Thru C r → r ≼ c → Thru D r)
          → Few F q → Pin C F q → Pin D E q
burst-pin {c = c} bu tc ic dn fw (pn {y} {r} tr ir x rc z) with inside (c ⊕ [ ix 1 ]) y in e
... | true  = let iw = subst T (sym e) tt in
              pn tc (in-call c y iw) (proj₁ (BurstsAt.win bu x iw (chain-few fw z))) (proj₂ (BurstsAt.win bu x iw (chain-few fw z))) (z+ z)
... | false = let (rc′ , w , rw) = BurstsAt.kept bu x (λ t → subst T e t) ir (ic tr) rc in
              pn (dn tr rc′) (inside-trans r y (y ⊕ [ ix 0 ]) ir (⊑-inside {y} {y ⊕ [ ix 0 ]} ([ ix 0 ] , refl))) w rw (z+ z)

-- An isle's step lies in its source's subscription: the source's attach
-- owed is a key of the tree, so no earlier than the step; a body's mark
-- would be one at the step itself.
step-in : ∀ {Γ X B} {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) B} {q}
        → (CS.connAt k ⊕ [ ix 1 ]) ≼ q → AttOwed k → Lo (connS k o b) (at q)
        → T (inside (CS.connAt k ⊕ [ ix 1 ]) q)
step-in {k = k} {o} {b} {q} cq (inj₁ ae) lo
  with ≮-after (CS.connAt k ⊕ [ ix 1 ]) q (lo (k-own (own-bld k {o = o} {b = b} (os ae))))
... | inj₂ i  = i
... | inj₁ qc with ≼-antisym {q} {CS.connAt k ⊕ [ ix 1 ]} qc cq
...   | refl = Equivalence.from T-≡ (inside-self q)
step-in {k = k} {o} {b} {q} cq (inj₂ (be , _)) lo
  with ≼-antisym {CS.connAt k ⊕ [ ix 1 ]} {q} cq (≮-≼ (CS.connAt k ⊕ [ ix 1 ]) q (lo (k-own (body-key k {o = o} {b = b} be))))
... | refl = Equivalence.from T-≡ (inside-self q)

------------------------------------------------------------------------
-- WHAT A HOLE GIVES THE FRAMES ABOVE IT: under a live node, its rows
-- owed before the step few and its pin read under its scope's binders;
-- in a part no live node reads, its pin and what it still runs before
-- the step few.

data Live {Γ A} (C : Cur) (q : Pos) (sc : Machine.Scope Γ) (E : EmissionSet A) : Set₁ where
  lc : HR C q sc E → (Env (full sc) C q → EnvL (full sc) C q → Pin C E q) → Live C q sc E

data Dead {A} (D : Cur) (q : Pos) (P : Pts) (E : EmissionSet A) : Set₁ where
  dc : Pin D E q → PLag q P → Dead D q P E

Carry : ∀ {Γ A} → Cur → Pos → Machine.Scope Γ → Need → EmissionSet A → Set₁
Carry C q sc owes                E = Live C q sc E
Carry C q sc (dead D P)          E = Dead D q P E
Carry C q sc (lane true _ _)     E = Live C q sc E
Carry C q sc (lane false D P)    E = Dead D q P E
Carry C q sc (lanecut true _ _)  E = Live C q sc E
Carry C q sc (lanecut false D P) E = Dead D q P E
Carry C q sc (pnd _)             E = ⊥₁

-- An ended lane's kept rows before the step: within what it still runs.
dead-kl : ∀ {A B} {C q₀ a Ph q} {P : Pol A B} {E : EmissionSet B}
        → Hole C P q₀ a Ph E false → PLag q Ph
        → Σ (List Pos) λ ks → ∀ {k e} → Kept P q₀ a k e → Owes C k → k ≺ q → k ∈ ks
dead-kl (h-end _ _ tp) pl with tailp-lag tp pl
... | lag ks f = ks , f
dead-kl (h-kill _ _ tp) pl with tailp-lag tp pl
... | lag ks f = ks , f

module _ {R : Set} (Rt : EmissionSet R) where

  mutual
    climbF : ∀ {Cr C Γ A Rg} {c : Ctx R Γ A} {N E} {s : St Γ A} {q}
           → Fr Rt Cr C Rg c N E → LoP (plug c s) q → Carry C q (scopeOf c) N E → Pin Cr Rt q
    climbF (f-top m) lo (lc _ pf) = up-pin (up-≈ m) (pf (λ ()) (λ ()))
    climbF {C = C} {s = s} (f-map fr m _) lo (lc h pf) =
      climbF {s = mapS _ s} fr lo
        (lc (hr-map (λ lg → lag-≈ m (lag-at map-row lg)) (λ bd (x , v , ow) → map-b {C = C} bd (from (alike m) (x , v)) ow) h)
            (λ env ef → up-pin (up-∘ up-map (up-≈ m)) (pf env ef)))
    climbF {C = C} {s = s} (f-scan fr _ m _) lo (lc h pf) =
      climbF {s = scanS _ _ s} fr lo
        (lc (hr-map (λ lg → lag-≈ m (lag-at scan-row lg)) (λ bd (x , v , ow) → scan-b {C = C} bd (from (alike m) (x , v)) ow) h)
            (λ env ef → up-pin (up-∘ up-scan (up-≈ m)) (pf env ef)))
    climbF {s = s} (f-cut fr) lo cr = climbF {s = cutS true _ s} fr lo cr
    climbF {C = C} {s = s} (f-take {i = i} {keep = keep} {E = Es} fr nf m _) lo (lc h pf) =
      climbF {s = takeS _ _ _ s} fr lo
        (lc (hr-map (λ lg → lag-≈ m (take-lag nf lg)) (λ bd (x , v , ow) → take-b {C = C} bd nf (from (alike m) (x , v)) ow) h)
            (λ env ef → up-pin (up-∘ (up-take {incl = i} {keep = keep} {D = C} {E = Es} (nofail-up {incl = i} {keep = keep} {C = C} {E = Es} nf)) (up-≈ m)) (pf env ef)))
    climbF {C = C} {c = inTake _ _ _ c} {s = s} (f-took {i = i} {keep = keep} {D = D} {Es = Es} fr fl g ni oa tp dm nf m sd) lo (dc p pl) =
      climbF {s = takeS _ _ _ s} fr lo
        (lc (hr λ env ef → lag-≈ m (tailp-lag tp pl) ,
               λ (x , v , ow) → took-b {C = C} {s = s} fl g ni oa sd (λ ki → lo (plug-in c ki)) (from (alike m) (x , v)) ow)
            (λ _ _ → up-pin (up-∘ (up-adv {C = C} dm (up-take {incl = i} {keep = keep} {D = D} {E = Es} nf)) (up-≈ m)) p))
    climbF {C = C} {c = inOuter op f ω d n qu ls c} {s = s} (f-outer fr ji jn je sd bh) lo (lc h pf) =
      climbF {s = flatS op f ω d n qu s ls} fr lo
        (lc (hr-outer {C = C} {op = op} {f = f} {ω = ω} jn je (λ i ki → lo (plug-in c (k-kid (k-lane i ki)))) h)
            (λ env ef → up-pin (flat-up-outer {op = op} {f = f} {ω = ω} ji sd je bh) (pf env ef)))
    climbF {C = C} {c = inLanes op f ω d n qu o pre post c} {s = s}
           (f-lanes {E′ = E′} {O = O} {q = q₀} {a = a} {b = true} fr ji sy bg₁ y _ ru hl@(h-live _ le uk _) bg₂ _ _ wh _ ah _ en li je _ _ bh _ _) lo (lc h pf) =
      climbF {s = flatS op f ω d n qu o (pre Data.List.ʳ++ s ∷ post)} fr lo
        (lc (hr-lanes {C = C} {op = op} {f = f} {ω = ω} {pre = pre} {post = post} {s = s} sy bg₁ hl bg₂ y wh ah en je
              (λ ki → lo (plug-in c (k-kid (k-outer ki)))) (λ i ki → lo (plug-in c (k-kid (k-lane i ki))))
              (λ env ef → live-kl hl (proj₁ (HR.run h env ef))) (λ env ef _ → proj₂ (HR.run h env ef)))
            (λ env ef → up-pin (up-∘ (up-≈ le) (flat-up-lane {sc = scopeOf c} {C = C} {D = C} {op = op} {f = f} {ω = ω} {O = O} {E = E′} {q = q₀} {a = a} ji je bh li y ru (λ t → t) (unkilled-no {C = C} {P = polF op (λ a′ → ⟦ f a′ ⟧ (full (scopeOf c))) O} {q = q₀} uk))) (pf env ef)))
    climbF {C = C} {c = inLanes op f ω d n qu o pre post c} {s = s}
           (f-lanes {D = D} {E′ = E′} {O = O} {q = q₀} {a = a} {b = false} fr ji sy bg₁ y _ ru hl bg₂ _ _ wh _ ah _ en li je _ _ bh dl _) lo (dc p pl) with dl tt
    ... | refl , dm , nk =
      climbF {s = flatS op f ω d n qu o (pre Data.List.ʳ++ s ∷ post)} fr lo
        (lc (hr-lanes {C = C} {op = op} {f = f} {ω = ω} {pre = pre} {post = post} {s = s} sy bg₁ hl bg₂ y wh ah en je
              (λ ki → lo (plug-in c (k-kid (k-outer ki)))) (λ i ki → lo (plug-in c (k-kid (k-lane i ki))))
              (λ _ _ → dead-kl hl pl) (λ _ _ ()))
            (λ _ _ → up-pin (flat-up-lane {sc = scopeOf c} {C = C} {D = D} {op = op} {f = f} {ω = ω} {O = O} {E = E′} {q = q₀} {a = a} ji je bh li y ru dm nk) p))
    climbF {s = s} (f-lane {b = true} fr) lo cr = climbF {s = lnS true s} fr lo cr
    climbF {s = s} (f-lane {b = false} fr) lo cr = climbF {s = lnS false s} fr lo cr
    climbF {s = s} (f-lnct {a = a} {b = true} fr) lo cr = climbF {s = cutS true a s} fr lo cr
    climbF {s = s} (f-lnct {a = a} {b = false} fr) lo cr = climbF {s = cutS false a s} fr lo cr
    climbF {C = C} {c = inSrc k b c} {s = s} (f-src fr sc pt lv _ bs bβ fl fe ce bh sd af _ ic _) lo (lc h pf) =
      climbF {s = connS k s b} fr lo (lc (hr-src sc bs fl fe ce bh lob h) pin′)
      where
        lob : LoP b _
        lob ki = lo (plug-in c (k-kid (k-body ki)))
        pin′ : Env (full (scopeOf c)) C _ → EnvL (full (scopeOf c)) C _ → Pin C _ _
        pin′ env ef = by (CS.srcAtt k)
          (λ sa → up-pin (up-∘ (up-≈ fe) (conn-up-src sa sc pt lv af bβ fl ce)) (pf env ef))
          (λ na → burst-pin (conn-bursts pt ce) (thru-sub C (SubdAt.past sd)) (ic na) (λ tr _ → tr)
                    (before bh (lag-≈ fe (proj₁ (HR.run h env ef)))) (up-pin (up-≈ fe) (pf env ef)))
    climbF {C = C} {c = inSrc k b c} {s = s} (f-srcc fr sc pt lv _ sp tp dm bh sd ao af bs bβ fl ce) lo (dc p pl) =
      climbF {s = connS k s b} fr lo (lc (hr-src sc bs fl ≈-refl ce bh lob (hr λ _ _ → tailp-lag tp pl , λ d → ⊥-elim (sp d))) (λ _ _ → pin′))
      where
        lob : LoP b _
        lob ki = lo (plug-in c (k-kid (k-body ki)))
        pin′ : Pin C _ _
        pin′ = by (CS.srcAtt k)
          (λ sa → up-pin (up-pre dm (conn-up-src sa sc pt lv af bβ fl ce)) p)
          (λ na → burst-pin (conn-bursts pt ce) (thru-sub C (SubdAt.past sd)) (λ tr → proj₂ (ao na) (dm tr)) (λ tr _ → dm tr)
                    (before bh (tailp-lag tp pl)) p)
    climbF (f-srcp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) lo ()
    climbF {C = C} {c = inBody k o c} {s = s} (f-body fr sc pt _ sr bE fl ce) lo (lc h pf) =
      climbF {s = connS k o s} fr lo
        (lc (hr-body {s = s} sc sr fl ce loc h)
            (λ env ef → let (envb , efb , _ , _) = body-env {b = s} sc sr env ef loc in up-pin (conn-up-body sc pt sr bE fl ce) (pf envb efb)))
      where
        loc : LoP (connS k o s) _
        loc ki = lo (plug-in c ki)
    climbF {s = s} (d-map fr u) lo (dc p pl) = climbF {s = mapS _ s} fr lo (dc (up-pin u p) pl)
    climbF {s = s} (d-scan fr u) lo (dc p pl) = climbF {s = scanS _ _ s} fr lo (dc (up-pin u p) pl)
    climbF {s = s} (d-cut fr u) lo (dc p pl) = climbF {s = cutS _ _ s} fr lo (dc (up-pin u p) pl)
    climbF {s = s} (d-ln fr u) lo (dc p pl) = climbF {s = lnS _ s} fr lo (dc (up-pin u p) pl)
    climbF {s = s} (d-take fr u) lo (dc p pl) = climbF {s = takeS _ _ _ s} fr lo (dc (up-pin u p) pl)
    climbF {c = inOuter _ _ _ _ _ _ ls c} {s = s} (d-outer fr u hl le) lo (dc p pl) =
      climbF {s = flatS _ _ _ _ _ _ s ls} fr lo (dc (up-pin u p) (⊑-plag le (plag-∪ pl (huskl-f hl (λ i ki → lo (plug-in c (k-kid (k-lane i ki))))))))
    climbF {c = inLanes _ _ _ _ _ _ o pre post c} {s = s} (d-lanes fr ho _ hpre hpost u le) lo (dc p pl) =
      climbF {s = flatS _ _ _ _ _ _ o (pre Data.List.ʳ++ s ∷ post)} fr lo
        (dc (up-pin u p)
            (⊑-plag le (plag-∪ (husk-f ho (λ ki → lo (plug-in c (k-kid (k-outer ki)))))
                       (plag-∪ (huskl-f hpre (λ i ki → lo (plug-in c (k-kid (k-lane (pre-in pre (reverse⁺ i)) ki)))))
                       (plag-∪ pl (huskl-f hpost (λ i ki → lo (plug-in c (k-kid (k-lane (post-in pre i) ki))))))))))
    climbF {c = inSrc k b c} {s = s} (d-src u hb _ u′ le _ _ pz oz iz) lo (dc p pl) =
      climbU {o = s} {b = b} u lo (upa-pin u′ p) (⊑-plag le (plag-∪ (plag-under pl) (husk-f hb (λ ki → lo (plug-in c (k-kid (k-body ki)))))))
    climbF {c = inBody k o c} {s = s} (d-body u sh u′ le oz iz) lo (dc p pl) =
      climbU {o = o} {b = s} u lo (up-pin u′ p)
        (⊑-plag le (plag-∪ (srch-f sh (λ ki → lo (plug-in c (k-kid (k-src ki))))
                                      (λ be → lo (plug-in c (k-own (body-key k {o = o} {b = s} be))))
                                      (λ ae → lo (plug-in c (k-own (own-bld k {o = o} {b = s} (os ae))))))
                           pl))
    climbF {c = inSrc k b c} {s = s} {q} (f-isle {D = D} {Ci = Ci} u hb _ le _ _ bh sd _ ao ic bu nr _ oz iz) lo (lc h pf) =
      climbU {o = s} {b = b} u lo (burst-pin bu (thru-up0 D nr) ic (λ tr rc → thru-dn D rc (thru-up0 D nr)) fw (pf env ef))
        (⊑-plag le (plag-∪ (burst-plag {C = Ci} {k = k} fw) (husk-f hb (λ ki → lo (plug-in c (k-kid (k-body ki)))))))
      where
        ie = subd-env {k = k} sd (att-slot {k = k} {p = q} ao (λ be → lo (plug-in c (k-own (body-key k {o = s} {b = b} be))))
                                                             (λ ae → lo (plug-in c (k-own (own-bld k {o = s} {b = b} (os ae))))))
        env = proj₁ ie
        ef  = proj₂ ie
        fw = before bh (proj₁ (HR.run h env ef))
    climbF {c = inSrc k b c} {s = s} (f-islec {D = D} {Ci = Ci} u hb _ le _ _ _ tp dm bh _ _ ic bu nr oz iz) lo (dc p pl) =
      climbU {o = s} {b = b} u lo (burst-pin bu (thru-up0 D nr) (λ tr → ic (dm tr)) (λ tr rc → thru-dn D rc (thru-up0 D nr)) fw p)
        (⊑-plag le (plag-∪ (burst-plag {C = Ci} {k = k} fw) (husk-f hb (λ ki → lo (plug-in c (k-kid (k-body ki)))))))
      where
        fw = before bh (tailp-lag tp pl)
    climbF (f-islep _ _ _ _ _ _ _ _ _ _ _ _ _ _ oz iz) lo ()

    climbU : ∀ {Cr C D Γ X B} {E β : EmissionSet B} {c : Ctx R Γ B} {k : CS Γ X} {P} {o : St Γ X} {b : St (X ∷ Γ) B} {q}
           → Unread Rt Cr C D E β c k P → LoP (plug c (connS k o b)) q → Pin D E q → PLag q P → Pin Cr Rt q
    climbU {o = o} {b} (un-dead fr) lo p pl = climbF {s = connS _ o b} fr lo (dc p pl)
    climbU {C = C} {k = k} {o = o} {b} (un-torn fr sc _ nl fl ce tp dm) lo p pl =
      climbF {s = connS k o b} fr lo
        (lc (hr λ env ef → lag-≈ (proj₁ ce) (lag-at (λ r → _ , proj₁ r) (tailp-lag tp pl)) ,
                           conn-fb {C = C} sc (λ t → ⊥-elim (notT _ nl t)) (λ t → ⊥-elim (notT _ nl t)) fl env ce)
            (λ _ _ → pin-dom dm p))

  -- AN ISLE'S ROW AT THE ROOT: a source in its subscribe burst under a
  -- connect no live node reads, its row at the step or on its chain,
  -- shown inside its subscription and carried up.
  isle-pin : ∀ {Cr Γ X B} {c : Ctx R Γ B} {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) B} {C D Db P Qb β E′ y e q}
           → Unread Rt Cr C D E′ β c k P → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) Db b β Qb
           → P ⊑ (Burst (bef q) k ∪ᵖ Qb) → Behind (bef q) (Frozen k) → Subd (scopeOf c) (bef q) k → AttOwed k
           → Bursts k E′ → Thru D (CS.connAt k)
           → Lo (plug c (connS k o b)) (at q) → Frozen k y e → y ≡ q ⊎ Zs q y → Pin Cr Rt q
  isle-pin {c = c} {k = k} {o} {b} {y = y} {q = q} u hb le bh sd ao bu nr lof row yq with foot yq
    where
      c₁ = CS.connAt k ⊕ [ ix 1 ]
      fq : Few (Frozen k) q
      fq = thru-few (bef q) bh (≼-refl {q})
      iq : T (inside c₁ q)
      iq = step-in {k = k} {o} {b} (SubdAt.past sd {q} (≼-refl {q})) ao (λ ki → lof (plug-in c ki))
      foot : y ≡ q ⊎ Zs q y → T (inside c₁ y) × Few (Frozen k) y × Zs q (y ⊕ [ ix 0 ])
      foot (inj₁ refl) = iq , fq , z₁
      foot (inj₂ z)    = inside-trans c₁ q y iq (zs-in z) , chain-few fq z , z+ z
  ... | iy , fy , zy =
    climbU {o = o} {b = b} u lo (pn nr (in-call (CS.connAt k) y iy) (proj₁ (BurstsAt.win bu row iy fy)) (proj₂ (BurstsAt.win bu row iy fy)) zy)
      (⊑-plag le (plag-∪ (burst-plag {C = bef q} {k = k} (thru-few (bef q) bh (≼-refl {q}))) (husk-f hb (λ ki → lo (plug-in c (k-kid (k-body ki)))))))
    where
      lo : LoP (plug c (connS k o b)) q
      lo = lo-p lof
