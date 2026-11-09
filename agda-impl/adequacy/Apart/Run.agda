{-# OPTIONS --guardedness #-}

-- A MARK RUN KEEPS APART: the least mark runs where it is keyed, its
-- region opening the run there and whatever it owes next inside that
-- region; a frame played on owes inside what it owed; a teardown only
-- drops regions.
module adequacy.Apart.Run where

open import Data.Bool using (true; false; not; _∧_; if_then_else_; _∨_)
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
open import Data.Product using (_,_; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)

open import denotation.Position using (Pos; ix; last; tick; cascade; cascadeAt; _∙_; _⊕_)
open import denotation.Events using (Frame; emit; stall; close; From∞; Frame∞; done; quiet; at)
open import denotation.Simultaneity using (effect-tick)
open import operation.PureObservable using (module Machine; play; ending; over; baseOf; stepOf)
open Machine using (Ctx; St; Mode; ofS; doneS; cutS; takeS; joinS; connS; coldS; cs; attAt; attached; cpAt; cutAt; overAt;
                    nx; cp; rising; absorbed; closed; unsubIf; cut; own; run; ofM; attM; bodyM; srcAttM; owedM; cpM; cutM; joinM; leafM)
open import operation.Key using () renaming (at to atᴷ)
open import adequacy.Stamped using (StOK)
open import adequacy.Found using (Marked; ofK; attK; conK; joinK; leafK; stopK; cutK)
open import adequacy.Floor.Keys using (own-cls; ob)
open import adequacy.Apart.Cone using (Cone; pre; tag; cone-trans)
open import adequacy.Apart.Region using (Rg; cn; tl; pt; cl; In; Sub; Sep; Keyed; f-cn; f-tl; sub-fut; sub-at; self)
open import adequacy.Apart.Items using (items; ibI; gI; mI; bodyR; lhs; rhs; plug-items; unsubIf-⊆; cut-⊆)
open import adequacy.Apart.Kit using (W; bI; AS; quit; fewer; refill₀; fire; fire′; none; cl-cn; cl-tl; cl-pt)

private
  -- The values after the next, inside it.
  tl-tl-in : ∀ {u i y} → In (tl u (suc i)) y → In (tl u i) y
  tl-tl-in {i = i} (inj₁ (j , le , c)) = inj₁ (j , ≤-trans (n≤1+n i) le , c)
  tl-tl-in         (inj₂ c)            = inj₂ c

  tl-tl : ∀ {u i} → Sub (tl u (suc i)) (tl u i)
  tl-tl {u} {i} = sub-fut (f-tl u (suc i)) (f-tl u i) (λ y → tl-tl-in) (λ y o iy → o (tl-tl-in iy))

  -- A frame's next step, inside its later values: a value its frame
  -- closes straight after, under the frame's end.
  nxt : ∀ {A u i w} (fr : Frame A w) y → In (tl (baseOf u fr) (stepOf (suc i) fr)) y → In (tl u (suc i)) y
  nxt (emit _ (close _))  y (inj₁ (j , _ , c)) = inj₂ (cone-trans (pre [ ix j ]) c)
  nxt (emit _ (close _))  y (inj₂ c)           = inj₂ (cone-trans (pre [ last ]) c)
  nxt (emit _ (emit _ _)) y iy                 = iy
  nxt (emit _ (stall _))  y iy                 = iy
  nxt (stall _)           y iy                 = iy
  nxt (close _)           y iy                 = iy

  next-tl : ∀ {A u i w} (fr : Frame A w) → Sub (tl (baseOf u fr) (stepOf (suc i) fr)) (tl u i)
  next-tl {u = u} {i} fr = sub-fut (f-tl _ _) (f-tl u i) (λ y iy → tl-tl-in (nxt fr y iy)) (λ y o iy → o (tl-tl-in (nxt fr y iy)))

  cl-next : ∀ {A u i w} (fr : Frame A w) → Sep (cl (u ⊕ [ ix i ])) (tl (baseOf u fr) (stepOf (suc i) fr))
  cl-next {u = u} {i} fr = (λ y ()) , λ y iy → proj₂ (cl-tl {u} {i}) y (nxt fr y iy)

  -- The end, inside the values.
  cn-tl : ∀ {u i} → Sub (cn (u ⊕ [ last ])) (tl u i)
  cn-tl {u} {i} = sub-fut (f-cn _) (f-tl u i) (λ y c → inj₂ c) (λ y o c → ⊥-elim (o (inj₂ c)))

  -- A timer cascade after the values, inside their end, its first value
  -- under the cascade's own end when its frame closes straight after it.
  cas-in : ∀ {A u i T w} (fr : Frame A w) → tick (u ⊕ [ last ]) < T
         → ∀ y → In (tl (baseOf (cascadeAt T (u ⊕ [ last ])) fr) (stepOf 0 fr)) y → In (tl u i) y
  cas-in {u = u} {T = T} fr lt = inc fr
    where
      under : ∀ {i} l y → Cone (cascade T (u ⊕ [ last ]) ∙ l) y → In (tl u i) y
      under l y c = inj₂ (cone-trans (tag l lt (self (u ⊕ [ last ]))) c)
      inc : ∀ {A w i} (fr : Frame A w) y → In (tl (baseOf (cascadeAt T (u ⊕ [ last ])) fr) (stepOf 0 fr)) y → In (tl u i) y
      inc (emit _ (close _))  y (inj₁ (_ , _ , c)) = under _ y c
      inc (emit _ (close _))  y (inj₂ c)           = under _ y c
      inc (emit _ (emit _ _)) y (inj₁ (_ , _ , c)) = under _ y c
      inc (emit _ (emit _ _)) y (inj₂ c)           = under _ y c
      inc (emit _ (stall _))  y (inj₁ (_ , _ , c)) = under _ y c
      inc (emit _ (stall _))  y (inj₂ c)           = under _ y c
      inc (stall _)           y (inj₁ (_ , _ , c)) = under _ y c
      inc (stall _)           y (inj₂ c)           = under _ y c
      inc (close _)           y (inj₁ (_ , _ , c)) = under _ y c
      inc (close _)           y (inj₂ c)           = under _ y c

  cas-tl : ∀ {A u i T w} (fr : Frame A w) → tick (u ⊕ [ last ]) < T
         → Sub (tl (baseOf (cascadeAt T (u ⊕ [ last ])) fr) (stepOf 0 fr)) (tl u i)
  cas-tl {u = u} {i} fr lt = sub-fut (f-tl _ _) (f-tl u i) (cas-in fr lt) (λ y o iy → o (cas-in fr lt y iy))

  -- The run in a value's subtree, a timer cascade after its frame's end.
  cl-cas : ∀ {A u T w} (fr : Frame A w) → tick (u ⊕ [ last ]) < T
         → Sep (cl (u ⊕ [ ix 0 ])) (tl (baseOf (cascadeAt T (u ⊕ [ last ])) fr) (stepOf 0 fr))
  cl-cas {u = u} fr lt = (λ y ()) , λ y iy → proj₂ (cl-tl {u} {0}) y (cas-in {i = 1} fr lt y iy)

  -- Past a tick, the cascade a frame's end starts.
  later-tick : ∀ {τ w w′} u → suc w ≤ w′ → tick u ≤ τ + w → tick (u ⊕ [ last ]) < τ + w′
  later-tick {τ} {w} {w′} u le hw = subst (_< τ + w′) (sym (effect-tick u [ last ])) (≤-trans (s≤s hw) (subst (_≤ τ + w′) (+-suc τ w) (+-monoʳ-≤ τ le)))

module _ {R : Set} where
  private
    -- Played on at rest, owing inside what was owed.
    narrow : ∀ {Γ A} (c : Ctx R Γ A) {t t′} {x y : Rg} X → items t ↭ x ∷ X → items t′ ↭ y ∷ X → Sub y x → W c t [] → W c t′ []
    narrow c {t} {t′} {x} {y} X pT pT′ s h = refill₀ c {t} {t′} [] [] [ x ] [ y ] X pT pT′ (λ { k (h₀ ∷ []) nc → s k nc h₀ ∷ [] }) ([] ∷ []) h

    -- An end run.
    fire-cn : ∀ {Γ A} (c : Ctx R Γ A) {t t′} (m : Mode A) q X → items t ↭ cn q ∷ X → items t′ ↭ X
            → All (Keyed (atᴷ q)) (items (Machine.plug c t)) → W c t [] → W c t′ (bI m q)
    fire-cn c {t} {t′} m q X pT pT′ kd h =
      fire′ c {t} {t′} {q} m (cn q) [] X (f-cn q) (λ y c → c) (λ y o c → o c) pT pT′ kd [] ([] ∷ []) h

    -- The `i`-th value run, `y` owed next.
    fire-val : ∀ {Γ A} (c : Ctx R Γ A) {t t′ u i} (y : Rg) X → Sub y (tl u i) → _
             → items t ↭ tl u i ∷ X → items t′ ↭ y ∷ X → All (Keyed (atᴷ (u ⊕ [ ix i ]))) (items (Machine.plug c t))
             → W c t [] → W c t′ [ cl (u ⊕ [ ix i ]) ]
    fire-val c {t} {t′} {u} {i} y X sy sep pT pT′ kd h =
      fire c {t} {t′} (tl u i) [ y ] X (f-tl u i) (λ z c → inj₁ (i , ≤-refl , c)) (λ z o c → ⊥-elim (o (inj₁ (i , ≤-refl , c))))
        pT pT′ kd (sy ∷ []) ((sep ∷ []) ∷ [] ∷ []) h

    -- Fewer regions, the keys still past.
    keyed-⊆ : ∀ {Γ A} (c : Ctx R Γ A) {t t′ h} → items t′ ⊆ items t → All (Keyed h) (items (Machine.plug c t)) → All (Keyed h) (items (Machine.plug c t′))
    keyed-⊆ c {t} {t′} {h} sub kd =
      subst (All (Keyed h)) (sym (plug-items c t′))
        (All-resp-⊆ (⊆-++ (⊆-refl {x = lhs c}) (⊆-++ sub (⊆-refl {x = rhs c}))) (subst (All (Keyed h)) (plug-items c t) kd))

  run-ap : ∀ {Γ A κ} (c : Ctx R Γ A) {s : St Γ A} {m} r → Marked s m → (m , κ) ∈ own s → StOK s
         → All (Keyed κ) (items (Machine.plug c s)) → W c s [] → AS (run c s m r)
  run-ap c r (ofK i p []) (here refl) _ kd h with closed c
  ... | true  = quit c {t = ofS i p []} {t′ = doneS} (none _) h
  ... | false = fire-cn c {t = ofS i p []} {t′ = doneS} (rising cp) (p ⊕ [ last ]) [] ↭-refl ↭-refl kd h
  run-ap c r (ofK i p []) (there ()) _ kd h
  run-ap c r (ofK i p (x ∷ [])) (here refl) _ kd h with closed c
  ... | true  = quit c {t = ofS i p (x ∷ [])} {t′ = doneS} (none _) h
  ... | false = fire-val c {t = ofS i p (x ∷ [])} {t′ = ofS (suc i) p []} (cn (p ⊕ [ last ])) [] cn-tl (cl-cn refl) ↭-refl ↭-refl kd h
  run-ap c r (ofK i p (x ∷ y ∷ xs)) (here refl) _ kd h with closed c
  ... | true  = quit c {t = ofS i p (x ∷ y ∷ xs)} {t′ = doneS} (none _) h
  ... | false = fire-val c {t = ofS i p (x ∷ y ∷ xs)} {t′ = ofS (suc i) p (y ∷ xs)} (tl p (suc i)) [] tl-tl cl-tl ↭-refl ↭-refl kd h
  run-ap c r (ofK i p (_ ∷ _)) (there ()) _ kd h
  run-ap c r (attK l p s) _ hs kd h with unsubIf (not l) s | unsubIf-⊆ (not l) s
  ... | s′ , _ | sub = quit c {t = cutS l (attAt p) s} {t′ = cutS l attached s′} (pt p ∷ʳ sub) h
  run-ap c r′ (stopK i q r s) (here refl) _ kd h =
    fire-cn c {t = takeS i q (cpAt r) s} {t′ = takeS i q (cutAt r) s} (if not (closed c) then rising cp else absorbed) (r ⊕ [ last ]) (pt r ∷ items s)
      ↭-refl ↭-refl kd h
  run-ap c r′ (stopK i q r s) (there ()) hs kd h
  run-ap c r′ (cutK i q r s) _ hs kd h with cut s | cut-⊆ s
  ... | s′ , _ | sub = quit c {t = takeS i q (cutAt r) s} {t′ = takeS i q (overAt r) s′} (pt r ∷ʳ sub) h
  run-ap c r (joinK j g x q (nx a) ib) (here refl) _ kd h =
    fire-cn c {t = joinS j g x ((q , nx a) ∷ ib)} {t′ = joinS j g x ib} (if g ∧ not (closed c) then rising (nx a) else absorbed) q (ibI ib ++ gI g j)
      ↭-refl ↭-refl kd h
  run-ap c r (joinK j g x q cp ib) (here refl) _ kd h =
    fewer c {t = joinS j g x ib} {t′ = joinS j false x ib} ⊆-refl (⊆-++ (⊆-refl {x = ibI ib}) (none (gI g j)))
      (fire-cn c {t = joinS j g x ((q , cp) ∷ ib)} {t′ = joinS j g x ib} (if g ∧ not (closed c) then rising cp else absorbed) q (ibI ib ++ gI g j)
        ↭-refl ↭-refl kd h)
  run-ap c r (joinK j g x q e ib) (there ()) hs kd h
  run-ap c r (conK (cs z sl sa (just p) nothing ow ca ea sr sc) o b _ (inj₁ refl)) mem _ kd h
    with own-cls (cs z sl sa (just p) nothing ow ca ea sr sc) {o} {b} mem
  ... | ob refl =
    fire c {t = connS (cs z sl sa (just p) nothing ow ca ea sr sc) o b} {t′ = connS (cs z sl sa nothing (just (p ⊕ [ ix 1 ])) ow ca ea sr sc) o b}
      (cn (p ⊕ [ ix 1 ])) [ pt (p ⊕ [ ix 1 ]) ] (mI pt ow ++ items o ++ items b) (f-cn _) (λ y c → c) (λ y o c → o c)
      ↭-refl ↭-refl kd (sub-at (f-cn _) (self _) ∷ []) ((cl-pt ∷ []) ∷ [] ∷ []) h
  run-ap c r (conK (cs z sl sa (just p) (just a) ow ca ea sr sc) o b _ (inj₁ refl)) mem _ kd h
    with own-cls (cs z sl sa (just p) (just a) ow ca ea sr sc) {o} {b} mem
  ... | ob refl =
    fire c {t = mid} {t′ = connS (cs z sl sa nothing (just (p ⊕ [ ix 1 ])) ow ca ea sr sc) o b}
      (cn (p ⊕ [ ix 1 ])) [ pt (p ⊕ [ ix 1 ]) ] (mI pt ow ++ items o ++ items b) (f-cn _) (λ y c → c) (λ y o c → o c)
      ↭-refl ↭-refl (keyed-⊆ c {t = old} {t′ = mid} drop-as kd) (sub-at (f-cn _) (self _) ∷ []) ((cl-pt ∷ []) ∷ [] ∷ [])
      (fewer c {t = old} {t′ = mid} ⊆-refl drop-as h)
    where
      old = connS (cs z sl sa (just p) (just a) ow ca ea sr sc) o b
      mid = connS (cs z sl sa (just p) nothing ow ca ea sr sc) o b
      drop-as : items mid ⊆ items old
      drop-as = ⊆-++ (⊆-refl {x = [ cn (p ⊕ [ ix 1 ]) ]}) (pt a ∷ʳ ⊆-refl)
  run-ap c r (conK (cs z sl sa nothing as ow ca ea sr sc) o b _ (inj₁ refl)) mem hs kd h = h
  run-ap c r (conK (cs z sl sa ba (just p) ow ca ea sr sc) o b _ (inj₂ (inj₁ refl))) mem hs kd h
    with unsubIf (not sl ∨ closed c) o | unsubIf-⊆ (not sl ∨ closed c) o
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
  run-ap c r (leafK true (ending e)) (here refl) _ kd h =
    fire-cn c {t = coldS true (ending e)} {t′ = coldS false over} (if not (closed c) then rising cp else absorbed) e [] ↭-refl ↭-refl kd h
  run-ap c r (leafK true (ending e)) (there ()) he kd h
  run-ap c r (leafK true over) () hs kd h
  run-ap c r (leafK true (play τ u i w fr)) (there ()) hs kd h
  run-ap c r (leafK true (play τ u i w (emit a (close k)))) (here refl) hw kd h with closed c
  ... | true  = quit c {t = coldS true (play τ u i w (emit a (close k)))} {t′ = coldS true over} (none _) h
  ... | false with From∞.force k
  ...   | done = fire-val c {t = coldS true (play τ u i w (emit a (close k)))} {t′ = coldS true (ending ((u ⊕ [ last ]) ⊕ [ last ]))}
                   (cn ((u ⊕ [ last ]) ⊕ [ last ])) [] cn-tl (cl-cn refl) ↭-refl ↭-refl kd h
  ...   | quiet = fire c {t = coldS true (play τ u i w (emit a (close k)))} {t′ = coldS true over} (tl (u ⊕ [ last ]) 0) [] []
                    (f-tl (u ⊕ [ last ]) 0) (λ z c → inj₁ (0 , ≤-refl , c))
                    (λ z o c → ⊥-elim (o (inj₁ (0 , ≤-refl , c)))) ↭-refl ↭-refl kd [] ([] ∷ []) h
  ...   | at w′ le fr′ =
    fire-val c {t = coldS true (play τ u i w (emit a (close k)))} {t′ = coldS true (play τ (cascadeAt (τ + w′) ((u ⊕ [ last ]) ⊕ [ last ])) 0 w′ fr′)}
      _ [] (cas-tl fr′ lt) (cl-cas fr′ lt) ↭-refl ↭-refl kd h
    where lt = later-tick (u ⊕ [ last ]) le (subst (_≤ τ + w) (sym (effect-tick u [ last ])) hw)
  run-ap c r (leafK true (play τ u i w (emit a k@(emit _ _)))) (here refl) _ kd h with closed c
  ... | true  = quit c {t = coldS true (play τ u i w (emit a k))} {t′ = coldS true over} (none _) h
  ... | false = fire-val c {t = coldS true (play τ u i w (emit a k))} {t′ = coldS true (play τ u (suc i) w k)} _ [] (next-tl k) (cl-next k)
                  ↭-refl ↭-refl kd h
  run-ap c r (leafK true (play τ u i w (emit a k@(stall _)))) (here refl) _ kd h with closed c
  ... | true  = quit c {t = coldS true (play τ u i w (emit a k))} {t′ = coldS true over} (none _) h
  ... | false = fire-val c {t = coldS true (play τ u i w (emit a k))} {t′ = coldS true (play τ u (suc i) w k)} _ [] (next-tl k) (cl-next k)
                  ↭-refl ↭-refl kd h
  run-ap c r (leafK true (play τ u i w (stall k))) (here refl) _ kd h with closed c
  ... | true  = quit c {t = coldS true (play τ u i w (stall k))} {t′ = coldS true over} (none _) h
  ... | false = narrow c {t = coldS true (play τ u i w (stall k))} {t′ = coldS true (play τ u (suc i) w (Frame∞.force k))} [] ↭-refl ↭-refl (next-tl (Frame∞.force k)) h
  run-ap c r (leafK true (play τ u i w (close k))) (here refl) hw kd h with closed c
  ... | true  = quit c {t = coldS true (play τ u i w (close k))} {t′ = coldS true over} (none _) h
  ... | false with From∞.force k
  ...   | done = narrow c {t = coldS true (play τ u i w (close k))} {t′ = coldS true (ending (u ⊕ [ last ]))} [] ↭-refl ↭-refl cn-tl h
  ...   | quiet = quit c {t = coldS true (play τ u i w (close k))} {t′ = coldS true over} (none _) h
  ...   | at w′ le fr′ =
    narrow c {t = coldS true (play τ u i w (close k))} {t′ = coldS true (play τ (cascadeAt (τ + w′) (u ⊕ [ last ])) 0 w′ fr′)} [] ↭-refl ↭-refl
      (cas-tl fr′ (later-tick u le hw)) h
