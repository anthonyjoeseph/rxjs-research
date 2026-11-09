{-# OPTIONS --guardedness #-}

-- A COLD'S TICK IS AN ANCESTOR OF A ROW: an open cold's turn at its
-- slot leaves a row of the root's entry under it.  A stall or
-- a frame's close is a skip of the cold's entry there, owed where the
-- search found it, and passes up every live frame at the same position;
-- an emit rises, and its value climbs the frames until the root shows it,
-- a joiner or a source sets it a level down, or a take's failure ends
-- under it.  A row an outer or lane end decides only by whether every
-- part is done, so the climb is classical.
module adequacy.TickRow where

open import Data.Bool using (Bool; T; true; false; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_]; _++_; map; _ʳ++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Position using (Pos; ix; last; root; _⊕_) renaming (Path to Steps)
open import denotation.Events using (Timeline; Frame; emit; stall; close)
open import denotation.EmissionSet using (EmissionSet; Ev; Den; ⟦_⟧; enter; out; skip; end; _≺_; Reach; Dep; InE; at-skip; map-skip;
  map-end; module Scan; module TakeWhile; module Connecting; module Merge; module Bounded;
  module Switch; module Exhaust)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans; ≺→≼; ≺-≼-≺)
open import denotation.Laws.Worlds using (Hots; ⊕-assoc; ⊕-identityʳ)
open import operation.PureObservable using (PureObs; module Machine; play; slotOf; onward)
open Machine using (Ctx; St; Scope; CS; ⟨_,_,_,_⟩; plug; load; search; found; leafM; absorbed; rising; nx; closed; scopeOf;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody;
                    mapS; scanS; cutS; lnS; takeS; flatS; connS; coldS; free; cpAt; cutAt; overAt)
open import operation.Key using (at; after; <ᴷ-irrefl; at-after)
open import adequacy.Least using (Lo; k-own; k-kid; k-take)
open import adequacy.Floor.Keys using (Into; sub-at; lo-weaken)
open import adequacy.Apart.Floor using (floor)
open import adequacy.Rows using (full; tapeE)
open import adequacy.Path using (Path; _⇜_; _▸τ_)
open import adequacy.Simulation using (Simulation; module Along)
open import adequacy.Simulated using (cursor)
open import adequacy.Cursor using (Cur; bef; Behind; _≈_; voc; Rgn; Sound; Lane; Runs; Kill; polF; JoinF; LanesIn; JRl; JRo; JInv;
                                   h-live; h-end; h-kill; Parts; s-cold; s-took; o-cp)
open import adequacy.Cursor.Frame using (Fr; owes; dead; lane; lanecut; pnd; f-top; f-map; f-scan; f-cut; f-take; f-took; f-outer;
                                         f-lanes; f-lane; f-lnct; f-src; f-srcc; f-srcp; f-body; d-map; d-scan; d-cut; d-ln; d-take;
                                         d-outer; d-lanes; d-src; d-body; f-isle; f-islec; f-islep)
open import adequacy.Cursor.Rise using (Inv; settled; flying; adrift)
open import adequacy.Cursor.Tear using (husk-of)
open import adequacy.PinTail using (took-tail)
open import adequacy.FrShift using (fr-shift)
open import adequacy.Dispatch using (module Over; found-lo)
open import adequacy.Walk using (dead-closed)
open import adequacy.IsleLift using (z₁; zs-under)
open import adequacy.Settle using (jlane)
open import adequacy.Guard using (LiveN; Clr; clr-≈; clr-tr; reach-zs; m-skip; jstep; hand-clr; src-behind; lo₀; flo; isle-row;
                                  module Lift; module Outer)

-- A row of `t` at `y` or under it.
Below : ∀ {A} → EmissionSet A → Pos → Set
Below {A} t y = Σ Pos λ r → Σ (Ev A) λ e → t r e × Σ Steps λ xs → r ≡ y ⊕ xs

below-up : ∀ {A} {t : EmissionSet A} {y} zs → Below t (y ⊕ zs) → Below t y
below-up {y = y} zs (r , e , tr , xs , eq) = r , e , tr , zs ++ xs , trans eq (⊕-assoc y zs xs)

-- What lies before `q` and is behind its cursor, a row at `q` reaches.
reach₀ : ∀ {A} {t : EmissionSet A} {q e} → Behind (bef q) t → Reach t q e
reach₀ (ks , f) = ks , λ tk lt _ → f tk (λ qk → qk lt)

conn-reach₀ : ∀ {A B} {p} {σ : EmissionSet A} {β : EmissionSet B} {q e} → Behind (bef q) σ → Reach β q e
            → Reach (Connecting.ConnT p σ β) q e
conn-reach₀ {p = p} {σ} {β} {q} {e} (ks , f) (ls , g) = ls ++ map (_⊕ [ ix 0 ]) ks , go
  where
    sl : ∀ {k e′} → σ k e′ → (k ⊕ [ ix 0 ]) ≺ q → (k ⊕ [ ix 0 ]) ∈ (ls ++ map (_⊕ [ ix 0 ]) ks)
    sl {k} r lt = ∈-++⁺ʳ ls (∈-map⁺ (_⊕ [ ix 0 ]) (f r λ qk → qk (≺-trans {k} {k ⊕ [ ix 0 ]} {q} (≺-ext k []) lt)))
    go : ∀ {k e′} → Connecting.ConnT p σ β k e′ → k ≺ q → Dep q e k e′ → k ∈ (ls ++ map (_⊕ [ ix 0 ]) ks)
    go (Connecting.body r)       lt d = ∈-++⁺ˡ (g r lt d)
    go (Connecting.burst r _)    lt _ = sl r lt
    go (Connecting.echo r _ _ _) lt _ = sl r lt
    go (Connecting.kept r _ _ _) lt _ = sl r lt

-- A skip in its region, or an end.
data Foot {A : Set} (Rg : Rgn) (q : Pos) : Ev A → Set where
  ft-skip : Rg q → Foot Rg q skip
  ft-end  : Foot Rg q end

-- A bounded merge's hand-off at `c`; no other joiner hands off.
HandAt : ∀ {A B} → FlatOp → (A → Den B) → EmissionSet A → Pos → Set
HandAt (mergeᶠ nothing)  F O c = ⊥
HandAt (mergeᶠ (just m)) F O c = Bounded.Queued m F O c
HandAt switchᶠ           F O c = ⊥
HandAt exhaustᶠ          F O c = ⊥

-- An outer's end: the joiner's end, or its skip.
jend : ∀ op {A B} {F : A → Den B} {O : EmissionSet A} {c} → O c end → ¬ ¬ (JoinF op F O c end ⊎ JoinF op F O c skip)
jend (mergeᶠ nothing)  {F = F} {O} x k = k (inj₂ (Merge.opass {f = F} {o = O} x λ dn → k (inj₁ (Merge.oend {f = F} {o = O} x dn))))
jend (mergeᶠ (just m)) {F = F} {O} x k = k (inj₂ (Bounded.opass {n = m} {f = F} {o = O} x λ dn → k (inj₁ (Bounded.oend {n = m} {f = F} {o = O} x dn))))
jend switchᶠ           {F = F} {O} x k = k (inj₂ (Switch.opass {f = F} {o = O} x λ dn → k (inj₁ (Switch.oend {f = F} {o = O} x dn))))
jend exhaustᶠ          {F = F} {O} x k = k (inj₂ (Exhaust.opass {f = F} {o = O} x λ dn → k (inj₁ (Exhaust.oend {f = F} {o = O} x dn))))

-- A running lane's end, uncut: the joiner's end, its skip, or a hand-off.
lfin : ∀ op {A B} {F : A → Den B} {O : EmissionSet A} {q a c}
     → O q (out a) → Runs (polF op F O) q → Lane (polF op F O) q a c end → (∀ {q′} → Kill (polF op F O) q q′ → q′ ≺ c → ⊥)
     → ¬ ¬ (JoinF op F O c end ⊎ (JoinF op F O c skip ⊎ HandAt op F O c))
lfin (mergeᶠ nothing) {F = F} {O} x rn l nk k =
  k (inj₂ (inj₁ (Merge.lpass {f = F} {o = O} x rn l (λ ()) (λ ()) λ dn → k (inj₁ (Merge.lend {f = F} {o = O} x rn l (λ ()) (λ ()) dn)))))
lfin (mergeᶠ (just m)) {F = F} {O} x rn l nk k =
  k (inj₂ (inj₁ (Bounded.lpass {n = m} {f = F} {o = O} x rn l (λ ()) (λ hq → k (inj₂ (inj₂ hq)))
    λ dn → k (inj₁ (Bounded.lend {n = m} {f = F} {o = O} x rn l (λ ()) (λ hq → k (inj₂ (inj₂ hq))) dn)))))
lfin switchᶠ {F = F} {O} x rn l nk k =
  k (inj₂ (inj₁ (Switch.lpass {f = F} {o = O} x rn l uc (λ ()) λ dn → k (inj₁ (Switch.lend {f = F} {o = O} x rn l uc (λ ()) dn)))))
  where uc = λ { (_ , a′ , x′ , lt , lt′) → nk (a′ , x′ , lt) lt′ }
lfin exhaustᶠ {F = F} {O} x rn l nk k =
  k (inj₂ (inj₁ (Exhaust.lpass {f = F} {o = O} x rn l (λ ()) (λ ()) λ dn → k (inj₁ (Exhaust.lend {f = F} {o = O} x rn l (λ ()) (λ ()) dn)))))

-- A hand-off's skip at the first child, clear between.
hand₀ : ∀ op {Γ A B} {sc : Scope Γ} {f : A → Obs Timeline Γ B} {O : EmissionSet A} (ji : JInv sc f O) {Rg : Rgn} {q₀ a₀ q}
        {E : EmissionSet B}
      → LanesIn (Hots (full sc)) (JRl sc Rg op f O) (polF op (λ a → ⟦ f a ⟧ (full sc)) O) O
      → Sound (JRo sc Rg op f O) O → O q₀ (out a₀) → Runs (polF op (λ a → ⟦ f a ⟧ (full sc)) O) q₀
      → E ≈ Lane (polF op (λ a → ⟦ f a ⟧ (full sc)) O) q₀ a₀ → Sound (JRl sc Rg op f O q₀) E → E q end
      → HandAt op (λ a → ⟦ f a ⟧ (full sc)) O q
      → JoinF op (λ a → ⟦ f a ⟧ (full sc)) O (q ⊕ [ ix 0 ]) skip × Clr q (q ⊕ [ ix 0 ]) (JoinF op (λ a → ⟦ f a ⟧ (full sc)) O)
hand₀ (mergeᶠ (just m)) ji li so x rn le sl r hq = hand-clr m ji li so x rn le sl r hq
hand₀ (mergeᶠ nothing)  _ _ _ _ _ _ _ _ ()
hand₀ switchᶠ           _ _ _ _ _ _ _ _ ()
hand₀ exhaustᶠ          _ _ _ _ _ _ _ _ ()

-- A failed take's end key past where it fell.
stop-into : ∀ {Γ A} {i f} (s : St Γ A) q → Into (at (q ⊕ [ last ])) (takeS i f free s) (takeS i f (cpAt q) s)
stop-into s q (k-own (here refl)) = inj₂ (<ᴷ-irrefl (at (q ⊕ [ last ])))
stop-into s q (k-own (there ()))
stop-into s q (k-kid (k-take h)) = inj₁ (k-kid (k-take h))

module _ {R : Set} (o : PureObs [] R) where
  private
    Rt = enter (⟦ o ⟧ []ᴬ) root
  open Lift Rt using (Lifted; Isled; lift)

  -- A lifted row, or an isle's: under the first child.
  lifted-below : ∀ {Cr q S} → Lo S (at q) → Lifted Cr q ⊎ Isled Cr q S → Below Rt q
  lifted-below {q = q} _ (inj₁ (r , e , tr , z , _)) with zs-under z
  ... | xs , eq = r , e , tr , ix 0 ∷ xs , trans eq (⊕-assoc q [ ix 0 ] xs)
  lifted-below {q = q} lo (inj₂ il) with isle-row Rt il lo
  ... | r , e , tr , xs , eq = r , e , tr , ix 0 ∷ xs , trans eq (⊕-assoc q [ ix 0 ] xs)

  -- A SKIP OR END AT THE CURSOR, carried up every live frame: at its
  -- position, or a level down under a joiner's hand-off or a source.
  lift₀ : ∀ {Cr Γ A} {c : Ctx R Γ A} {s : St Γ A} {Rg N E q e} → Fr Rt Cr (bef q) Rg c N E → Lo (plug c s) (at q) → LiveN N
        → E q e → Foot Rg q e → ¬ ¬ Below Rt q
  lift₀ (f-top m) _ _ r _ κ = κ (_ , _ , voc m r , [] , sym (⊕-identityʳ _))
  lift₀ {s = s} (f-map {f = f} fr m _) lo _ r (ft-skip g) = lift₀ {s = mapS f s} fr lo tt (voc m (map-skip r)) (ft-skip g)
  lift₀ {s = s} (f-map {f = f} fr m _) lo _ r ft-end      = lift₀ {s = mapS f s} fr lo tt (voc m (map-end r)) ft-end
  lift₀ {s = s} (f-scan {f = f} {z = z} fr _ m _) lo _ r (ft-skip g) = lift₀ {s = scanS f z s} fr lo tt (voc m (Scan.sstep r)) (ft-skip g)
  lift₀ {s = s} (f-scan {f = f} {z = z} fr _ m _) lo _ r ft-end      = lift₀ {s = scanS f z s} fr lo tt (voc m (Scan.send r)) ft-end
  lift₀ {s = s} (f-cut {a = a} fr) lo _ r ft = lift₀ {s = cutS true a s} fr lo tt r ft
  lift₀ {s = s} (f-take {i = i} {keep = keep} fr nf m _) lo _ r (ft-skip g) =
    lift₀ {s = takeS i keep free s} fr lo tt (voc m (TakeWhile.step r λ { (_ , _ , x , k , lt) → nf x k lt })) (ft-skip g)
  lift₀ {s = s} (f-take {i = i} {keep = keep} fr nf m _) lo _ r ft-end =
    lift₀ {s = takeS i keep free s} fr lo tt (voc m (TakeWhile.tend r λ { (_ , _ , x , k , lt) → nf x k lt })) ft-end
  lift₀ {s = s} (f-lane {b = b} fr) lo l r ft = lift₀ {s = lnS b s} fr lo l r ft
  lift₀ {s = s} (f-lnct {a = a} {b = true} fr) lo _ r ft = lift₀ {s = cutS true a s} fr lo tt r ft
  lift₀ (f-lnct {b = false} _) _ ()
  lift₀ {s = s} (f-outer {op = op} {f = f} {ω = ω} {d = d} {n = n} {qu = qu} {ls = ls} {c = c} {E = O} fr _ _ je _ bh) lo _ r (ft-skip g) =
    lift₀ {s = flatS op f ω d n qu s ls} fr lo tt (voc (proj₂ je) (jstep op {F = F′} {O} r , reach₀ {e = skip} bh)) (ft-skip (proj₁ g))
    where F′ = λ a → ⟦ f a ⟧ (full (scopeOf c))
  lift₀ {s = s} (f-outer {op = op} {f = f} {ω = ω} {d = d} {n = n} {qu = qu} {ls = ls} {c = c} {E = O} fr _ _ je sd bh) lo _ r ft-end κ =
    jend op {F = F′} {O} r λ
      { (inj₁ e)  → lift₀ {s = flatS op f ω d n qu s ls} fr lo tt (voc (proj₂ je) (e , reach₀ {e = end} bh)) ft-end κ
      ; (inj₂ sk) → lift₀ {s = flatS op f ω d n qu s ls} fr lo tt (voc (proj₂ je) (sk , reach₀ {e = skip} bh)) (ft-skip (proj₁ (Sound.rg sd r tt))) κ }
    where F′ = λ a → ⟦ f a ⟧ (full (scopeOf c))
  lift₀ {s = s} (f-lanes {op = op} {f = f} {ω = ω} {d = d} {n = n} {qu = qu} {o = o′} {pre = pre} {post = post} {c = c} {O = O}
                  fr _ _ _ x _ rn (h-live _ le uk _) _ _ _ _ _ _ _ _ _ je _ _ bh _ _) lo _ r (ft-skip g) =
    lift₀ {s = flatS op f ω d n qu o′ (pre ʳ++ s ∷ post)} fr lo tt
      (voc (proj₂ je) (jlane op {F = F′} {O} x rn (voc le r) (λ κ lt → uk κ lt) tt , reach₀ {e = skip} bh)) (ft-skip (proj₁ g))
    where F′ = λ a → ⟦ f a ⟧ (full (scopeOf c))
  lift₀ {s = s} {q = y} (f-lanes {op = op} {f = f} {ω = ω} {d = d} {n = n} {qu = qu} {o = o′} {pre = pre} {post = post} {c = c} {O = O}
                  fr ji _ _ x _ rn (h-live _ le uk _) _ _ _ _ _ _ _ _ li je so sl bh _ _) lo _ r ft-end κ =
    lfin op {F = F′} {O} x rn (voc le r) (λ κ′ lt → uk κ′ lt) λ
      { (inj₁ e)         → lift₀ {s = S} fr lo tt (voc (proj₂ je) (e , reach₀ {e = end} bh)) ft-end κ
      ; (inj₂ (inj₁ sk)) → lift₀ {s = S} fr lo tt (voc (proj₂ je) (sk , reach₀ {e = skip} bh)) (ft-skip (proj₁ (Sound.rg (sl tt) r tt))) κ
      ; (inj₂ (inj₂ hq)) → let hc = hand₀ op ji li so x rn le (sl tt) r hq in
          κ (lifted-below lo (lift {s = S} fr (lo₀ c {S} lo) tt (voc (proj₂ je) (reach-zs bh z₁ (proj₁ hc))) m-skip z₁
                                    (clr-≈ (proj₂ je) (clr-tr (proj₂ hc))) (proj₁ (Sound.rg (sl tt) r tt)))) }
    where F′ = λ a → ⟦ f a ⟧ (full (scopeOf c))
          S = flatS op f ω d n qu o′ (pre ʳ++ s ∷ post)
  lift₀ (f-lanes _ _ _ _ _ _ _ (h-end _ _ _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ ()
  lift₀ (f-lanes _ _ _ _ _ _ _ (h-kill _ _ _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ ()
  lift₀ {s = s} fr@(f-src {k = k} {b = b} {c = c} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) lo _ r (ft-skip g) κ =
    κ (lifted-below lo (Outer.src-at o fr (lo₀ (inSrc k b c) {s} lo) tt r tt g))
  lift₀ {s = s} fr@(f-src {k = k} {b = b} {c = c} _ _ pt _ _ _ _ _ fz _ _ _ _ _ _ _) lo _ r ft-end κ =
    κ (lifted-below lo (Outer.src-at o fr (lo₀ (inSrc k b c) {s} lo) tt r tt (Sound.rg (Parts.ss pt) (voc fz r) tt)))
  lift₀ {s = s} fr@(f-isle {k = k} {b = b} {c = c} _ _ _ _ _ _ _ _ _ _ _ _ _ _ oz iz) lo _ r (ft-skip g) κ =
    κ (lifted-below lo (Outer.src-at o fr (lo₀ (inSrc k b c) {s} lo) tt r tt g))
  lift₀ {s = s} fr@(f-isle {k = k} {b = b} {c = c} _ _ _ _ _ _ _ _ ss _ _ _ _ _ oz iz) lo _ r ft-end κ =
    κ (lifted-below lo (Outer.src-at o fr (lo₀ (inSrc k b c) {s} lo) tt r tt (Sound.rg ss r tt)))
  lift₀ {s = s} (f-body {k = k} {o = o′} fr sc pt _ sr _ _ ce) lo _ r (ft-skip g) =
    lift₀ {s = connS k o′ s} fr lo tt (voc (proj₁ ce) (Connecting.body {p = CS.connAt k} r , conn-reach₀ {p = CS.connAt k} {e = skip} (src-behind sc sr) (proj₂ ce r))) (ft-skip (Parts.b⊆ pt g))
  lift₀ {s = s} (f-body {k = k} {o = o′} fr sc pt _ sr _ _ ce) lo _ r ft-end =
    lift₀ {s = connS k o′ s} fr lo tt (voc (proj₁ ce) (Connecting.body {p = CS.connAt k} r , conn-reach₀ {p = CS.connAt k} {e = end} (src-behind sc sr) (proj₂ ce r))) ft-end
  lift₀ (f-took _ _ _ _ _ _ _ _ _ _) _ ()
  lift₀ (f-srcc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ ()
  lift₀ (f-srcp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ ()
  lift₀ (d-map _ _) _ ()
  lift₀ (d-scan _ _) _ ()
  lift₀ (d-cut _ _) _ ()
  lift₀ (d-ln _ _) _ ()
  lift₀ (d-take _ _) _ ()
  lift₀ (d-outer _ _ _ _) _ ()
  lift₀ (d-lanes _ _ _ _ _ _ _) _ ()
  lift₀ (d-src _ _ _ _ _ _ _ pz oz iz) _ ()
  lift₀ (d-body _ _ _ _ oz iz) _ ()
  lift₀ (f-islec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ oz iz) _ ()
  lift₀ (f-islep _ _ _ _ _ _ _ _ _ _ _ _ _ _ oz iz) _ ()

  -- The cursor invariant where a run has reached.
  inv-at : ∀ {rs k} → Path (load o) rs k → Σ Cur λ Cr → Σ Cur λ C → Inv Rt Cr C k
  inv-at pth with Along.along (cursor o) nothing pth (Simulation.i₀ (cursor o)) (Simulation.t₀ (cursor o))
  ... | (Cr , C , i , _) , _ = Cr , C , i

  -- A part no live node reads is under a closed frame.
  adrift-no : ∀ {Cr C Γ A} {c : Ctx R Γ A} {Rg D P E} → closed c ≡ false → Fr Rt Cr C Rg c (dead D P) E → ⊥
  adrift-no cl fr = subst T cl (dead-closed Rt fr refl)

  -- The rises a climb takes.
  pass-step : ∀ {Γ A} {i} {w : A → Bool} {c : Ctx R Γ A} {s a y} → w a ≡ true
            → ⟨ c , takeS i w free s , rising (nx a) , y ⟩ ⇜ ⟨ inTake i w free c , s , rising (nx a) , y ⟩
  pass-step wa rewrite wa = _ , refl

  incl-step : ∀ {Γ A} {w : A → Bool} {c : Ctx R Γ A} {s a y} → w a ≡ false
            → ⟨ c , takeS true w (cpAt y) s , rising (nx a) , y ⊕ [ ix 0 ] ⟩ ⇜ ⟨ inTake true w free c , s , rising (nx a) , y ⟩
  incl-step wa rewrite wa = _ , refl

  body-step : ∀ {Γ X B} {k : CS Γ X} {o′ : St Γ X} {c : Ctx R Γ B} {s b y} → CS.srcLive k ≡ true
            → ⟨ c , connS k o′ s , rising (nx b) , y ⟩ ⇜ ⟨ inBody k o′ c , s , rising (nx b) , y ⟩
  body-step sl rewrite sl = _ , refl

  emit-step : ∀ {Γ A Γ′ A′} {c : Ctx R Γ A} {s q} {c′ : Ctx R Γ′ A′} {τ u i t a} {f : Frame A′ t} {κ}
            → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , coldS true (play τ u i t (emit a f))) leafM κ) → closed c′ ≡ false
            → ⟨ c′ , coldS true (onward τ u i t f) , rising (nx a) , slotOf u i (emit a f) ⟩ ⇜ ⟨ c , s , absorbed , q ⟩
  emit-step fd cl rewrite fd | cl = _ , refl

  -- A TAKE'S FAILURE ENDS UNDER IT: past the failing value, the take's
  -- end, owed, carried up from the frame above.
  fail-below : ∀ {rs Γ A} {w : A → Bool} {c : Ctx R Γ A} {s a y}
             → Path (load o) rs ⟨ inTake false w free c , s , rising (nx a) , y ⟩ → w a ≡ false → ¬ ¬ Below Rt y
  fail-below {w = w} {c} {s} {a} {y} pth wa with inv-at pth
  ... | _ , _ , flying (f-take fr nf m sd) _ (sy , row) =
    let nk  = subst (λ b → T (not b)) (sym wa) tt
        lo₁ : Lo (plug c (takeS false w (cpAt y) s)) (at (y ⊕ [ last ]))
        lo₁ = sub-at c {X = at (y ⊕ [ last ])} (stop-into {i = false} {f = w} s y) (lo-weaken (at (y ⊕ [ last ])) (after y) (floor o pth tt) (at-after y [ last ]))
        sy′ = s-took (a , row , nk , λ (_ , _ , x , nk′ , qp) → nf x nk′ qp)
                     (λ pq → pq) (λ ()) (o-cp (≺→≼ {y} {y ⊕ [ last ]} (≺-ext y {last} [])))
                     (took-tail sy row nk nf) (proj₂ (husk-of sy)) (λ t → t)
                     (λ {r′} t (q , _ , x , nk′ , qr) → nf x nk′ (≺-≼-≺ {q} {r′} {y} qr t)) m sd
        (_ , fr″ , _ , _) = fr-shift Rt fr sy′ (≺→≼ {y} {y ⊕ [ last ]} (≺-ext y {last} [])) lo₁
    in λ κ → lift₀ fr″ lo₁ tt (voc m (TakeWhile.stop row nk λ { (_ , _ , x , k , lt) → nf x k lt })) ft-end (λ b → κ (below-up [ last ] b))
  ... | _ , _ , flying (f-took _ _ _ _ _ _ _ _ _ _) _ ()
  ... | _ , _ , flying (d-take _ _) _ ()
  ... | _ , _ , adrift fr cl _ = ⊥-elim (adrift-no cl fr)
  ... | _ , _ , settled () _ _

  -- A VALUE RISING CLIMBS: every frame passes it on, until the root
  -- shows it, a joiner or a source sets it a level down, or a take's
  -- failure ends under it.
  climb : ∀ {rs Γ A} {c : Ctx R Γ A} {s a y} → Path (load o) rs ⟨ c , s , rising (nx a) , y ⟩ → closed c ≡ false → ¬ ¬ Below Rt y
  climb {c = top} pth cl with inv-at pth
  ... | _ , _ , flying (f-top m) _ (_ , row) = λ κ → κ (_ , _ , voc m row , [] , sym (⊕-identityʳ _))
  ... | _ , _ , adrift fr cl′ _ = ⊥-elim (adrift-no cl′ fr)
  ... | _ , _ , settled () _ _
  climb {c = inMap f c} pth cl = climb {c = c} (pth ▸τ (_ , refl)) cl
  climb {c = inScan f z c} pth cl = climb {c = c} (pth ▸τ (_ , refl)) cl
  climb {c = inCut true a c} pth cl = climb {c = c} (pth ▸τ (_ , refl)) cl
  climb {c = inCut false a c} pth ()
  climb {c = inLn b c} pth cl = climb {c = c} (pth ▸τ (_ , refl)) cl
  climb {c = inTake i w free c} {s} {a} {y} pth cl with w a in wa
  ... | true = climb {c = c} (pth ▸τ pass-step {i = i} {w = w} {c = c} {s = s} {a = a} {y = y} wa) cl
  climb {c = inTake true w free c} {s} {a} {y} pth cl | false =
    λ κ → climb {c = c} (pth ▸τ incl-step {w = w} {c = c} {s = s} {a = a} {y = y} wa) cl (λ b → κ (below-up [ ix 0 ] b))
  climb {c = inTake false w free c} {s} {a} {y} pth cl | false = fail-below {w = w} {c = c} {s = s} {a = a} {y = y} pth wa
  climb {c = inTake i w (cpAt r) c} pth ()
  climb {c = inTake i w (cutAt r) c} pth ()
  climb {c = inTake i w (overAt r) c} pth ()
  climb {c = inOuter op f ω d n qu ls c} {s} pth cl with inv-at pth
  ... | _ , _ , flying fr _ fy = λ κ → κ (lifted-below (flo o pth tt) (Outer.outer-row o fr (lo₀ c {flatS op f ω d n qu s ls} (flo o pth tt)) fy))
  ... | _ , _ , adrift fr cl′ _ = ⊥-elim (adrift-no cl′ fr)
  ... | _ , _ , settled () _ _
  climb {c = inLanes op f ω d n qu o′ pre post c} pth cl with inv-at pth
  ... | _ , _ , flying (f-lanes {b = true} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (_ , _ , refl , _ , _) = climb {c = c} (pth ▸τ (_ , refl)) cl
  ... | _ , _ , flying (f-lanes {b = false} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (_ , _ , _ , () , _)
  ... | _ , _ , flying (d-lanes _ _ _ _ _ _ _) _ ()
  ... | _ , _ , adrift fr cl′ _ = ⊥-elim (adrift-no cl′ fr)
  ... | _ , _ , settled () _ _
  climb {c = inSrc k b c} {s} pth cl with inv-at pth
  ... | _ , _ , flying fr _ fy = λ κ → κ (lifted-below (flo o pth tt) (Outer.src-step o fr (lo₀ (inSrc k b c) {s} (flo o pth tt)) fy))
  ... | _ , _ , adrift fr cl′ _ = ⊥-elim (adrift-no cl′ fr)
  ... | _ , _ , settled () _ _
  climb {c = inBody k o′ c} pth cl with CS.srcLive k in sl
  ... | true = climb {c = c} (pth ▸τ body-step sl) cl
  climb {c = inBody k o′ c} pth () | false

  -- A stall's or a close's skip: owed where the search found it, in its
  -- entry and region, carried up from the cursor moved to it.
  tick-skip : ∀ {rs Γ A} {c : Ctx R Γ A} {s q Γ′ A′} {c′ : Ctx R Γ′ A′} {l y}
            → Path (load o) rs ⟨ c , s , absorbed , q ⟩
            → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , coldS true l) leafM (at y))
            → closed c′ ≡ false → InE (tapeE l) y skip → ¬ ¬ Below Rt y
  tick-skip {c = c} {s} pth fd cl tr with inv-at pth
  ... | _ , _ , iv with Over.focus Rt pth fd iv
  ...   | _ , settled {N = owes} _ fr h@(s-cold _ _ _ tw) with tw tr
  ...     | ow , r , g with fr-shift Rt fr h ow (proj₂ (found-lo c s fd))
  ...       | _ , fr″ , _ , _ = lift₀ fr″ (proj₂ (found-lo c s fd)) tt r (ft-skip g)
  tick-skip pth fd cl tr | _ , _ , iv | _ , settled {N = dead _ _} _ fr _ = ⊥-elim (adrift-no cl fr)
  tick-skip pth fd cl tr | _ , _ , iv | _ , settled {N = lane _ _ _} _ _ (_ , _ , () , _)
  tick-skip pth fd cl tr | _ , _ , iv | _ , settled {N = lanecut _ _ _} _ _ (_ , _ , () , _)
  tick-skip pth fd cl tr | _ , _ , iv | _ , settled {N = pnd _} _ _ (_ , () , _)

  -- AN OPEN COLD'S TICK IS AN ANCESTOR OF A ROW of the root's entry.
  tick-below : ∀ {rs Γ A} {c : Ctx R Γ A} {s q Γ′ A′} {c′ : Ctx R Γ′ A′} {τ u i t} {fr : Frame A′ t}
             → Path (load o) rs ⟨ c , s , absorbed , q ⟩
             → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , coldS true (play τ u i t fr)) leafM (at (slotOf u i fr)))
             → closed c′ ≡ false → ¬ ¬ Below Rt (slotOf u i fr)
  tick-below {c = c} {s} {q} {fr = emit a f} pth fd cl = climb (pth ▸τ emit-step {c = c} {s = s} {q = q} fd cl) cl
  tick-below {fr = stall f}  pth fd cl = tick-skip pth fd cl at-skip
  tick-below {fr = close f}  pth fd cl = tick-skip pth fd cl at-skip
