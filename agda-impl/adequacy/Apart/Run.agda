{-# OPTIONS --guardedness #-}

-- A MARK RUN KEEPS APART: the least mark runs where it is keyed, its
-- region opening the run there and whatever it owes next inside that
-- region; a frame played on owes inside what it owed; a teardown only
-- drops regions.
module adequacy.Apart.Run where

open import Data.Bool using (true; false; not; _∧_; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; [_]; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-refl)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_; ⊆-refl)
open import Data.List.Relation.Binary.Sublist.Heterogeneous using (_∷ʳ_)
open import Data.List.Relation.Binary.Sublist.Propositional.Properties using (All-resp-⊆) renaming (++⁺ to ⊆-++)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (suc; _+_; _<_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; +-suc; +-monoʳ-≤)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)

open import denotation.Events using (Pos; ix; last; tick; emit; stall; close; From∞; Frame∞; done; quiet; at) renaming (sub to subᴾ)
open import operation.PureObservable using (module Machine; play; ending; over)
open Machine using (Ctx; St; Mode; ofS; doneS; cutS; takeS; joinS; connS; coldS; cs; attAt; attached; cpAt; cutAt; overAt;
                    nx; cp; rising; absorbed; closed; unsubIf; cut; own; run; ofM; attM; bodyM; srcAttM; owedM; cpM; cutM; joinM; leafM)
open import operation.Key using () renaming (at to atᴷ)
open import adequacy.Stamped using (Ix; ix-⊕; StOK)
open import adequacy.Dispatch using (Marked; ofK; attK; conK; joinK; leafK; stopK; cutK)
open import adequacy.Floor.Keys using (own-cls; ob)
open import adequacy.Apart.Cone using (tag; cone-trans)
open import adequacy.Apart.Region using (Rg; cn; tl; pt; cl; In; Sub; Keyed; f-cn; f-tl; sub-fut; sub-at; self)
open import adequacy.Apart.Items using (items; ibI; gI; mI; bodyR; lhs; rhs; plug-items; unsubIf-⊆; cut-⊆)
open import adequacy.Apart.Kit using (W; bI; AS; quit; fewer; refill₀; fire; fire′; none; cl-cn; cl-tl; cl-pt; tick-ix)

private
  -- The values after the next, inside it.
  tl-tl : ∀ {u i} → Sub (tl u (suc i)) (tl u i)
  tl-tl {u} {i} = sub-fut (f-tl u (suc i)) (f-tl u i) inc (λ y o iy → o (inc y iy))
    where
      inc : ∀ y → In (tl u (suc i)) y → In (tl u i) y
      inc y (inj₁ (j , le , c)) = inj₁ (j , ≤-trans (n≤1+n i) le , c)
      inc y (inj₂ c)            = inj₂ c

  -- The end, inside the values.
  cn-tl : ∀ {u i} → Sub (cn (u ++ [ last ])) (tl u i)
  cn-tl {u} {i} = sub-fut (f-cn _) (f-tl u i) (λ y c → inj₂ c) (λ y o c → ⊥-elim (o (inj₂ c)))

  -- A timer cascade after the values, inside their end.
  cas-tl : ∀ {u i T} → tick (u ++ [ last ]) < T → Sub (tl (ix T ∷ subᴾ (u ++ [ last ]) ∷ []) 0) (tl u i)
  cas-tl {u} {i} {T} lt = sub-fut (f-tl _ 0) (f-tl u i) inc (λ y o iy → o (inc y iy))
    where
      inc : ∀ y → In (tl (ix T ∷ subᴾ (u ++ [ last ]) ∷ []) 0) y → In (tl u i) y
      inc y (inj₁ (j , _ , c)) = inj₂ (cone-trans (tag [ ix j ] lt (self (u ++ [ last ]))) c)
      inc y (inj₂ c)           = inj₂ (cone-trans (tag [ last ] lt (self (u ++ [ last ]))) c)

module _ {R : Set} where
  private
    -- Played on at rest, owing inside what was owed.
    narrow : ∀ {Γ A} (c : Ctx R Γ A) {t t′} {x y : Rg} X → items t ↭ x ∷ X → items t′ ↭ y ∷ X → Sub y x → W c t [] → W c t′ []
    narrow c {t} {t′} {x} {y} X pT pT′ s h = refill₀ c {t} {t′} [] [] [ x ] [ y ] X pT pT′ (λ { k (h₀ ∷ []) nc → s k nc h₀ ∷ [] }) ([] ∷ []) h

    -- An end run.
    fire-cn : ∀ {Γ A} (c : Ctx R Γ A) {t t′} (m : Mode A) q X → Ix q → items t ↭ cn q ∷ X → items t′ ↭ X
            → All (Keyed (atᴷ q)) (items (Machine.plug c t)) → W c t [] → W c t′ (bI m q)
    fire-cn c {t} {t′} m q X hq pT pT′ kd h =
      fire′ c {t} {t′} {q} m (cn q) [] X hq (f-cn q) (λ y c → c) (λ y o c → o c) pT pT′ kd [] ([] ∷ []) h

    -- The `i`-th value run, `y` owed next.
    fire-val : ∀ {Γ A} (c : Ctx R Γ A) {t t′ u i} (y : Rg) X → Ix u → Sub y (tl u i) → _
             → items t ↭ tl u i ∷ X → items t′ ↭ y ∷ X → All (Keyed (atᴷ (u ++ [ ix i ]))) (items (Machine.plug c t))
             → W c t [] → W c t′ [ cl (u ++ [ ix i ]) ]
    fire-val c {t} {t′} {u} {i} y X hu sy sep pT pT′ kd h =
      fire c {t} {t′} (tl u i) [ y ] X (ix-⊕ u _ hu) (f-tl u i) (λ z c → inj₁ (i , ≤-refl , c)) (λ z o c → ⊥-elim (o (inj₁ (i , ≤-refl , c))))
        pT pT′ kd (sy ∷ []) ((sep ∷ []) ∷ [] ∷ []) h

    -- Fewer regions, the keys still past.
    keyed-⊆ : ∀ {Γ A} (c : Ctx R Γ A) {t t′ h} → items t′ ⊆ items t → All (Keyed h) (items (Machine.plug c t)) → All (Keyed h) (items (Machine.plug c t′))
    keyed-⊆ c {t} {t′} {h} sub kd =
      subst (All (Keyed h)) (sym (plug-items c t′))
        (All-resp-⊆ (⊆-++ (⊆-refl {x = lhs c}) (⊆-++ sub (⊆-refl {x = rhs c}))) (subst (All (Keyed h)) (plug-items c t) kd))

  run-ap : ∀ {Γ A κ} (c : Ctx R Γ A) {s : St Γ A} {m} r → Marked s m → (m , κ) ∈ own s → StOK s
         → All (Keyed κ) (items (Machine.plug c s)) → W c s [] → AS (run c s m r)
  run-ap c r (ofK i p []) (here refl) hp kd h with closed c
  ... | true  = quit c {t = ofS i p []} {t′ = doneS} (none _) h
  ... | false = fire-cn c {t = ofS i p []} {t′ = doneS} (rising cp) (p ++ [ last ]) [] (ix-⊕ p _ hp) ↭-refl ↭-refl kd h
  run-ap c r (ofK i p []) (there ()) hp kd h
  run-ap c r (ofK i p (x ∷ [])) (here refl) hp kd h with closed c
  ... | true  = quit c {t = ofS i p (x ∷ [])} {t′ = doneS} (none _) h
  ... | false = fire-val c {t = ofS i p (x ∷ [])} {t′ = ofS (suc i) p []} (cn (p ++ [ last ])) [] hp cn-tl (cl-cn hp refl) ↭-refl ↭-refl kd h
  run-ap c r (ofK i p (x ∷ y ∷ xs)) (here refl) hp kd h with closed c
  ... | true  = quit c {t = ofS i p (x ∷ y ∷ xs)} {t′ = doneS} (none _) h
  ... | false = fire-val c {t = ofS i p (x ∷ y ∷ xs)} {t′ = ofS (suc i) p (y ∷ xs)} (tl p (suc i)) [] hp tl-tl (cl-tl hp) ↭-refl ↭-refl kd h
  run-ap c r (ofK i p (_ ∷ _)) (there ()) hp kd h
  run-ap c r (attK l p s) _ hs kd h with unsubIf (not l) s | unsubIf-⊆ (not l) s
  ... | s′ , _ | sub = quit c {t = cutS l (attAt p) s} {t′ = cutS l attached s′} (pt p ∷ʳ sub) h
  run-ap c r′ (stopK i q r s) (here refl) (hr , _) kd h =
    fire-cn c {t = takeS i q (cpAt r) s} {t′ = takeS i q (cutAt r) s} (if not (closed c) then rising cp else absorbed) (r ++ [ last ]) (pt r ∷ items s)
      (ix-⊕ r _ hr) ↭-refl ↭-refl kd h
  run-ap c r′ (stopK i q r s) (there ()) hs kd h
  run-ap c r′ (cutK i q r s) _ hs kd h with cut s | cut-⊆ s
  ... | s′ , _ | sub = quit c {t = takeS i q (cutAt r) s} {t′ = takeS i q (overAt r) s′} (pt r ∷ʳ sub) h
  run-ap c r (joinK j g x q (nx a) ib) (here refl) (_ , hq , _) kd h =
    fire-cn c {t = joinS j g x ((q , nx a) ∷ ib)} {t′ = joinS j g x ib} (if g ∧ not (closed c) then rising (nx a) else absorbed) q (ibI ib ++ gI g j)
      hq ↭-refl ↭-refl kd h
  run-ap c r (joinK j g x q cp ib) (here refl) (_ , hq , _) kd h =
    fewer c {t = joinS j g x ib} {t′ = joinS j false x ib} ⊆-refl (⊆-++ (⊆-refl {x = ibI ib}) (none (gI g j)))
      (fire-cn c {t = joinS j g x ((q , cp) ∷ ib)} {t′ = joinS j g x ib} (if g ∧ not (closed c) then rising cp else absorbed) q (ibI ib ++ gI g j)
        hq ↭-refl ↭-refl kd h)
  run-ap c r (joinK j g x q e ib) (there ()) hs kd h
  run-ap c r (conK (cs z sl sa (just p) nothing ow ca ea sr sc) o b _ (inj₁ refl)) mem ((hp , _) , _) kd h
    with own-cls (cs z sl sa (just p) nothing ow ca ea sr sc) {o} {b} mem
  ... | ob refl =
    fire c {t = connS (cs z sl sa (just p) nothing ow ca ea sr sc) o b} {t′ = connS (cs z sl sa nothing (just (p ++ [ ix 1 ])) ow ca ea sr sc) o b}
      (cn (p ++ [ ix 1 ])) [ pt (p ++ [ ix 1 ]) ] (mI pt ow ++ items o ++ items b) (ix-⊕ p _ hp) (f-cn _) (λ y c → c) (λ y o c → o c)
      ↭-refl ↭-refl kd (sub-at (f-cn _) (self _) ∷ []) ((cl-pt ∷ []) ∷ [] ∷ []) h
  run-ap c r (conK (cs z sl sa (just p) (just a) ow ca ea sr sc) o b _ (inj₁ refl)) mem ((hp , _) , _) kd h
    with own-cls (cs z sl sa (just p) (just a) ow ca ea sr sc) {o} {b} mem
  ... | ob refl =
    fire c {t = mid} {t′ = connS (cs z sl sa nothing (just (p ++ [ ix 1 ])) ow ca ea sr sc) o b}
      (cn (p ++ [ ix 1 ])) [ pt (p ++ [ ix 1 ]) ] (mI pt ow ++ items o ++ items b) (ix-⊕ p _ hp) (f-cn _) (λ y c → c) (λ y o c → o c)
      ↭-refl ↭-refl (keyed-⊆ c {t = old} {t′ = mid} drop-as kd) (sub-at (f-cn _) (self _) ∷ []) ((cl-pt ∷ []) ∷ [] ∷ [])
      (fewer c {t = old} {t′ = mid} ⊆-refl drop-as h)
    where
      old = connS (cs z sl sa (just p) (just a) ow ca ea sr sc) o b
      mid = connS (cs z sl sa (just p) nothing ow ca ea sr sc) o b
      drop-as : items mid ⊆ items old
      drop-as = ⊆-++ (⊆-refl {x = [ cn (p ++ [ ix 1 ]) ]}) (pt a ∷ʳ ⊆-refl)
  run-ap c r (conK (cs z sl sa nothing as ow ca ea sr sc) o b _ (inj₁ refl)) mem hs kd h = h
  run-ap c r (conK (cs z sl sa ba (just p) ow ca ea sr sc) o b _ (inj₂ (inj₁ refl))) mem hs kd h
    with unsubIf (not sl) o | unsubIf-⊆ (not sl) o
  ... | o′ , _ | sub =
    quit c {t = connS (cs z sl sa ba (just p) ow ca ea sr sc) o b} {t′ = connS (cs z sl true ba nothing ow ca ea sr sc) o′ b}
      (⊆-++ (⊆-++ (⊆-refl {x = mI bodyR ba}) (pt p ∷ʳ ⊆-refl)) (⊆-++ sub (⊆-refl {x = items b}))) h
  run-ap c r (conK (cs z sl sa ba nothing ow ca ea sr sc) o b _ (inj₂ (inj₁ refl))) mem hs kd h = h
  run-ap c r (conK (cs z sl sa ba as (just p) ca ea sr sc) o b _ (inj₂ (inj₂ refl))) mem hs kd h
    with unsubIf sa o | unsubIf-⊆ sa o
  ... | o′ , _ | sub =
    quit c {t = connS (cs z sl sa ba as (just p) ca ea sr sc) o b} {t′ = connS (cs z false sa ba as nothing ca ea sr sc) o′ b}
      (⊆-++ (⊆-++ (⊆-refl {x = mI bodyR ba}) (⊆-++ (⊆-refl {x = mI pt as}) (none [ pt p ]))) (⊆-++ sub (⊆-refl {x = items b}))) h
  run-ap c r (conK (cs z sl sa ba as nothing ca ea sr sc) o b _ (inj₂ (inj₂ refl))) mem hs kd h = h
  run-ap c r (leafK false l) mem hs kd h = quit c {t = coldS false l} {t′ = coldS false over} (none _) h
  run-ap c r (leafK true (ending e)) (here refl) he kd h =
    fire-cn c {t = coldS true (ending e)} {t′ = coldS false over} (if not (closed c) then rising cp else absorbed) e [] he ↭-refl ↭-refl kd h
  run-ap c r (leafK true (ending e)) (there ()) he kd h
  run-ap c r (leafK true over) () hs kd h
  run-ap c r (leafK true (play τ u i w fr)) (there ()) hs kd h
  run-ap c r (leafK true (play τ u i w (emit a k))) (here refl) (hu , hw) kd h with closed c
  ... | true  = quit c {t = coldS true (play τ u i w (emit a k))} {t′ = coldS true over} (none _) h
  ... | false = fire-val c {t = coldS true (play τ u i w (emit a k))} {t′ = coldS true (play τ u (suc i) w k)} (tl u (suc i)) [] hu tl-tl (cl-tl hu)
                  ↭-refl ↭-refl kd h
  run-ap c r (leafK true (play τ u i w (stall k))) (here refl) (hu , hw) kd h with closed c
  ... | true  = quit c {t = coldS true (play τ u i w (stall k))} {t′ = coldS true over} (none _) h
  ... | false = narrow c {t = coldS true (play τ u i w (stall k))} {t′ = coldS true (play τ u (suc i) w (Frame∞.force k))} [] ↭-refl ↭-refl tl-tl h
  run-ap c r (leafK true (play τ u i w (close k))) (here refl) (hu , hw) kd h with closed c
  ... | true  = quit c {t = coldS true (play τ u i w (close k))} {t′ = coldS true over} (none _) h
  ... | false with From∞.force k
  ...   | done = narrow c {t = coldS true (play τ u i w (close k))} {t′ = coldS true (ending (u ++ [ last ]))} [] ↭-refl ↭-refl cn-tl h
  ...   | quiet = quit c {t = coldS true (play τ u i w (close k))} {t′ = coldS true over} (none _) h
  ...   | at w′ le fr′ =
    narrow c {t = coldS true (play τ u i w (close k))} {t′ = coldS true (play τ (ix (τ + w′) ∷ subᴾ (u ++ [ last ]) ∷ []) 0 w′ fr′)} [] ↭-refl ↭-refl
      (cas-tl (subst (_< τ + w′) (sym (tick-ix u [ last ] hu)) (≤-trans (s≤s hw) (subst (_≤ τ + w′) (+-suc τ w) (+-monoʳ-≤ τ le))))) h
