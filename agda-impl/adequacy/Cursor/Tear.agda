{-# OPTIONS --guardedness #-}

module adequacy.Cursor.Tear where

open import Data.Bool using (Bool; T; true; false; not)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import Tree using (Obs)
open import denotation.Events using (Pos; Timeline)
open import denotation.EmissionSet using (EmissionSet; out)
open import adequacy.Cursor.Show using (up-id; up-≈; up-map; up-scan; up-take; up-adv; up-∘; up-pre; nofail-up; unkilled-no; thru-sub; thru-no;
  flat-up-outer; flat-up-lane; conn-up-body; conn-up-src; conn-bursts)
open import operation.PureObservable using (module Machine)

open Machine using (St; Ctx; Scope; binds; CS; subscribing; absorbed;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    unsub; cut; killAll; unsubIf; off; offL; offIf; attached; attAt;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (_≃_; Frozen)
open import adequacy.Cursor using (Cur; Thru; Lane; Up; up; Dom; Subd; SubdAt; Behind; Flags; ConnE; Runs; NoKill; h-live;
  Begun; Husk; HuskL; LaneSt; Parts; Pol; Pts; Quiet; QuietL; Src; SrcH; Sync; Torn; _∪ᵖ_; _⊑_;
  h-blank; h-conn; h-cut; h-flat; h-ln; h-map; h-scan; h-take; hl-more; hl-none; joined;
  l-dead; l-live; more; none; s-cold; s-conn; s-cut; s-done; s-flat; s-join; s-joinx; s-map;
  s-of; s-scan; s-take; s-took; sh-dead; sh-isle; sh-islec; sh-pend; src-on; src-pend;
  src-shut; under-⊑; ∅ᵖ; ∪-⊑; ⊑-refl)

open _≃_

-- No rise in flight.
data Calm {A : Set} : Machine.Mode A → Set where
  c-sub : Calm subscribing
  c-abs : Calm absorbed

------------------------------------------------------------------------
-- WHAT A PART STILL RUNS, read off a node in step: its isles, each in
-- step at the cursor it was read at.

-- By a flag.
by : ∀ {ℓ} {X : Set ℓ} b → (T b → X) → (T (not b) → X) → X
by true  t _ = t tt
by false _ f = f tt

-- A body's husk read at its connect's own scope.
unbind : ∀ {Γ X B} {k : CS Γ X} {sc} {D} {b : St (X ∷ Γ) B} {β Q} → CS.scope k ≡ sc
       → Husk (binds (CS.src k) (CS.connAt k) sc) D b β Q → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) D b β Q
unbind refl h = h

-- Past its subscription: through its connect.
subd-thru : ∀ {Γ X} {sc : Scope Γ} {C} {k : CS Γ X} → Subd sc C k → Thru C (CS.connAt k)
subd-thru {C = C} sd = thru-sub C (SubdAt.past sd)

-- A cursor moved on: every closure read from it.
mutual
  husk-adv : ∀ {Γ} {sc : Scope Γ} {C D A} {s : St Γ A} {E P} → Dom C D → Husk sc D s E P → Husk sc C s E P
  husk-adv dm (h-blank q)       = h-blank q
  husk-adv dm (h-map hk u)      = h-map hk (up-adv dm u)
  husk-adv dm (h-scan hk u)     = h-scan hk (up-adv dm u)
  husk-adv dm (h-cut hk u)      = h-cut hk (up-adv dm u)
  husk-adv dm (h-ln hk u)       = h-ln hk (up-adv dm u)
  husk-adv dm (h-take hk u)     = h-take hk (up-adv dm u)
  husk-adv dm (h-flat ho u hl)  = h-flat ho (up-adv dm u) (huskL-adv dm hl)
  husk-adv dm (h-conn sh bh u)  = h-conn (srch-adv dm sh) bh (up-adv dm u)

  huskL-adv : ∀ {Γ} {sc : Scope Γ} {C D A} {ls : List (St Γ A)} {E P} → Dom C D → HuskL sc D ls E P → HuskL sc C ls E P
  huskL-adv dm hl-none          = hl-none
  huskL-adv dm (hl-more h u t)  = hl-more h (up-adv dm u) (huskL-adv dm t)

  srch-adv : ∀ {Γ X B} {sc : Scope Γ} {C D} {k : CS Γ X} {o} {E : EmissionSet B} {P} → Dom C D → SrcH sc D k o E P → SrcH sc C k o E P
  srch-adv dm (sh-dead hk u sf)                       = sh-dead hk (up-adv dm u) sf
  srch-adv dm (sh-isle na nc sy bh sd ss ao ic bu nr) = sh-isle na nc sy bh sd ss ao ic bu (dm nr)
  srch-adv dm (sh-islec na cl sp tp hk di bh sd ao ic bu nr) = sh-islec na cl sp tp hk di bh sd ao ic bu (dm nr)
  srch-adv dm (sh-pend na nc ba an sc adm pe wn ss bu nr) = sh-pend na nc ba an sc adm pe wn ss bu (dm nr)

-- Nothing, shown nowhere.
∅E : ∀ {A} → EmissionSet A
∅E _ _ = ⊥

up-∅ : ∀ {A B} {D D′} {E : EmissionSet B} → Up D (∅E {A}) D′ E
up-∅ = up λ _ _ ()

mutual
  husk-of : ∀ {Γ} {sc : Scope Γ} {Rg C A} {s : St Γ A} {E} → Sync sc Rg C s E → Σ Pts (Husk sc C s E)
  husk-of (s-cold _ _ _)            = _ , h-blank tt
  husk-of (s-of _ _)                = _ , h-blank tt
  husk-of (s-done _ _)              = _ , h-blank tt
  husk-of (s-map sy m _)            = _ , h-map (proj₂ (husk-of sy)) (up-∘ up-map (up-≈ m))
  husk-of (s-scan sy _ m _)         = _ , h-scan (proj₂ (husk-of sy)) (up-∘ up-scan (up-≈ m))
  husk-of (s-cut sy)                = _ , h-cut (proj₂ (husk-of sy)) up-id
  husk-of {C = C} (s-take {i = i} {keep = keep} {Es = Es} sy nf m _) =
    _ , h-take (proj₂ (husk-of sy)) (up-∘ (up-take {incl = i} {keep = keep} {D = C} {E = Es} (nofail-up {incl = i} {keep = keep} {C = C} {E = Es} nf)) (up-≈ m))
  husk-of {C = C} (s-took {i = i} {keep = keep} {Es = Es} _ _ _ _ _ {D} hk dm nf m _) =
    _ , h-take hk (up-∘ (up-adv {C = C} dm (up-take {incl = i} {keep = keep} {D = D} {E = Es} nf)) (up-≈ m))
  husk-of {sc = sc} {C = C} (s-flat {op = op} {f = f} {ω = ω} {O = O} {E = E} ji sy (joined bg _ _ _ _ _ _ li) je so bh) =
    _ , h-flat (proj₂ (husk-of sy)) (flat-up-outer {op = op} {f = f} {ω = ω} ji so je bh)
               (proj₂ (begun-husk {O = O} {E = E} (λ {q} {a} {D} x rn dm nk → flat-up-lane {sc = sc} {C = C} {D = D} {op = op} {f = f} {ω = ω} {O = O} {E = E} {q = q} {a = a} ji je bh li x rn dm nk) bg))
  husk-of (s-conn {k = k} sc pt bs bh ss tn fl ce) =
    by (CS.srcLive k) (λ l → _ , h-conn (proj₂ (src-husk sc pt (ss l) (bh l) fl ce))
                                       (unbind {k = k} sc (proj₂ (husk-of (bs l))))
                                       (conn-up-body sc pt (ss l) (bh l) fl ce))
                      (λ nl → _ , h-conn (srch-adv (Torn.dom (tn nl)) (Torn.sh (tn nl))) (Torn.bh (tn nl)) (up-adv (Torn.dom (tn nl)) (Torn.bu (tn nl))))
  husk-of (s-join _ _ _ _ _)        = _ , h-blank tt
  husk-of (s-joinx _ _)             = _ , h-blank tt

  src-husk : ∀ {Γ X B} {sc : Scope Γ} {Rg C} {k : CS Γ X} {o} {β E : EmissionSet B} → CS.scope k ≡ sc → (pt : Parts sc Rg k β)
           → Src sc (Parts.Rs pt) C k o → Behind C β → Flags C k β → ConnE (CS.connAt k) (Frozen k) β E → Σ Pts (SrcH sc C k o E)
  src-husk {C = C} sc pt sr@(src-pend na nc ba an adm pe wn _ nr) bb fl ce =
    _ , sh-pend na nc ba an sc adm pe wn (Parts.ss pt) (conn-bursts pt ce) (thru-no C nr)
  src-husk {k = k} sc pt sr@(src-on nc sy bh sd _ ao ic _) bb fl ce =
    by (CS.srcAtt k) (λ t → _ , sh-dead (proj₂ (husk-of sy)) (conn-up-src t sc pt sr bb fl ce) (inj₁ t))
                     (λ na → _ , sh-isle na nc sy bh sd (Parts.ss pt) (ao na) (ic na) (conn-bursts pt ce) (subd-thru {k = k} sd))
  src-husk {C = C} {k = k} sc pt sr@(src-shut cl sp tp hk dm bh sd ic _ _) bb fl ce =
    by (CS.srcAtt k) (λ t → _ , sh-dead hk (up-pre dm (conn-up-src t sc pt sr bb fl ce)) (inj₁ t))
                     (λ na → _ , sh-islec {Ci = C} na cl sp tp hk dm bh sd (proj₁ (ic na)) (proj₂ (ic na)) (conn-bursts pt ce) (subd-thru {k = k} sd))

  begun-husk : ∀ {Γ A B} {sc : Scope Γ} {Rl C} {P : Pol A B} {O E vs ls n}
             → (∀ {q a D} → O q (out a) → Runs P q → Dom C D → (∀ {r} → Thru D r → NoKill P q r) → Up D (Lane P q a) C E)
             → Begun sc Rl C P O vs ls n → Σ Pts (HuskL sc C ls E)
  begun-husk lf none                 = _ , hl-none
  begun-husk {P = P} {O = O} {E = E} lf (more x _ rn ln bg) =
    lane-husk {P = P} {O = O} {E = E} (λ {q} {a} {D} → lf {q} {a} {D}) x rn ln (proj₂ (begun-husk {O = O} {E = E} (λ {q} {a} {D} → lf {q} {a} {D}) bg))

  lane-husk : ∀ {Γ A B} {sc : Scope Γ} {Rg C} {P : Pol A B} {O E q a l b ls Q}
            → (∀ {q a D} → O q (out a) → Runs P q → Dom C D → (∀ {r} → Thru D r → NoKill P q r) → Up D (Lane P q a) C E)
            → O q (out a) → Runs P q → LaneSt sc Rg C P q a l b → HuskL sc C ls E Q → Σ Pts (HuskL sc C (l ∷ ls) E)
  lane-husk {C = C} {P = P} lf x rn (l-live (h-live _ m uk) sy _) hl =
    _ , hl-more (h-ln (h-cut (proj₂ (husk-of sy)) up-id) up-id) (up-∘ (up-≈ m) (lf {D = C} x rn (λ t → t) (unkilled-no {C = C} {P = P} uk))) hl
  lane-husk lf x rn (l-dead {D = D} _ hk dm nk) hl =
    _ , hl-more (h-ln (h-cut hk up-id) up-id) (lf {D = D} x rn dm nk) hl

-- One node's state in from what still runs around it.
peel-take : ∀ {Γ} {sc : Scope Γ} {D} {A} {i} {keep : A → Bool} {w s E Q} → Husk sc D (takeS i keep w s) E Q
          → Σ Pts λ Q′ → Σ Cur λ D₁ → Σ (EmissionSet A) λ E₁ → Husk sc D₁ s E₁ Q′ × Up D₁ E₁ D E × Q ⊑ Q′
peel-take {D = D} (h-blank q) = _ , D , ∅E , h-blank q , up-∅ , ⊑-refl
peel-take (h-take hk u) = _ , _ , _ , hk , u , ⊑-refl

peel-cut : ∀ {Γ} {sc : Scope Γ} {D} {A} {l a} {s : St Γ A} {E Q} → Husk sc D (cutS l a s) E Q
         → Σ Pts λ Q′ → Σ Cur λ D₁ → Σ (EmissionSet A) λ E₁ → Husk sc D₁ s E₁ Q′ × Up D₁ E₁ D E × Q ⊑ Q′
peel-cut {D = D} (h-blank q) = _ , D , ∅E , h-blank q , up-∅ , ⊑-refl
peel-cut (h-cut hk u)  = _ , _ , _ , hk , u , ⊑-refl

-- A SUBJECT LEFT AT ONCE: turning a part's subscribers off keeps it
-- quiet, and keeps its husk, isles and all.
offIf-off : ∀ {Γ A} b {s : St Γ A} → T (not b) → offIf b s ≡ s
offIf-off false _ = refl

mutual
  quiet-off : ∀ {Γ A} {s : St Γ A} → Quiet s → Quiet (off s)
  quiet-off {s = pend _ _}               ()
  quiet-off {s = coldS _ _}              _             = tt
  quiet-off {s = ofS _ _ _}              _             = tt
  quiet-off {s = doneS}                  _             = tt
  quiet-off {s = mapS _ s}               q             = quiet-off {s = s} q
  quiet-off {s = scanS _ _ s}            q             = quiet-off {s = s} q
  quiet-off {s = cutS _ _ s}             q             = quiet-off {s = s} q
  quiet-off {s = lnS _ s}                q             = quiet-off {s = s} q
  quiet-off {s = takeS _ _ _ s}          q             = quiet-off {s = s} q
  quiet-off {s = flatS _ _ _ _ _ _ o ls} (qo , ql)    = quiet-off {s = o} qo , quiet-offL {ls = ls} ql
  quiet-off {s = connS k _ b}            (f , qo , qb) = f , quiet-offIf (CS.srcAtt k) qo , quiet-off {s = b} qb
  quiet-off {s = joinS _ _ _ _}          _             = tt

  quiet-offL : ∀ {Γ A} {ls : List (St Γ A)} → QuietL ls → QuietL (offL ls)
  quiet-offL {ls = []}     _        = tt
  quiet-offL {ls = l ∷ ls} (q , ql) = quiet-off {s = l} q , quiet-offL {ls = ls} ql

  quiet-offIf : ∀ {Γ A} b {s : St Γ A} → Quiet s → Quiet (offIf b s)
  quiet-offIf true  {s} q = quiet-off {s = s} q
  quiet-offIf false     q = q

mutual
  off-husk : ∀ {Γ} {sc : Scope Γ} {D} {A} {s : St Γ A} {E P} → Husk sc D s E P → Husk sc D (off s) E P
  off-husk {s = s} (h-blank q) = h-blank (quiet-off {s = s} q)
  off-husk (h-map hk u)     = h-map (off-husk hk) u
  off-husk (h-scan hk u)    = h-scan (off-husk hk) u
  off-husk (h-cut hk u)     = h-cut (off-husk hk) u
  off-husk (h-ln hk u)      = h-ln (off-husk hk) u
  off-husk (h-take hk u)    = h-take (off-husk hk) u
  off-husk (h-flat ho u hl) = h-flat (off-husk ho) u (offL-husk hl)
  off-husk (h-conn sh bh u) = h-conn (srch-off sh) (off-husk bh) u

  offL-husk : ∀ {Γ} {sc : Scope Γ} {D} {A} {ls : List (St Γ A)} {E P} → HuskL sc D ls E P → HuskL sc D (offL ls) E P
  offL-husk hl-none         = hl-none
  offL-husk (hl-more h u t) = hl-more (off-husk h) u (offL-husk t)

  srch-off : ∀ {Γ X B} {sc : Scope Γ} {D} {k : CS Γ X} {o} {E : EmissionSet B} {P} → SrcH sc D k o E P → SrcH sc D k (offIf (CS.srcAtt k) o) E P
  srch-off {k = k} (sh-dead hk u sf) = sh-dead (offIf-husk (CS.srcAtt k) hk) u sf
  srch-off {k = k} sh@(sh-isle na _ _ _ _ _ _ _ _ _)  = subst (λ o′ → SrcH _ _ k o′ _ _) (sym (offIf-off (CS.srcAtt k) na)) sh
  srch-off {k = k} sh@(sh-islec na _ _ _ _ _ _ _ _ _ _ _) = subst (λ o′ → SrcH _ _ k o′ _ _) (sym (offIf-off (CS.srcAtt k) na)) sh
  srch-off {k = k} sh@(sh-pend na _ _ _ _ _ _ _ _ _ _) = subst (λ o′ → SrcH _ _ k o′ _ _) (sym (offIf-off (CS.srcAtt k) na)) sh

  offIf-husk : ∀ {Γ} {sc : Scope Γ} {D} {A} {s : St Γ A} {E P} b → Husk sc D s E P → Husk sc D (offIf b s) E P
  offIf-husk true  hk = off-husk hk
  offIf-husk false hk = hk

-- TEARING DOWN KEEPS NOTHING IN STEP: every connect's flags kept, a
-- pending subscription left as it is.
mutual
  quiet-unsub : ∀ {Γ A} {s : St Γ A} → Quiet s → Quiet (proj₁ (unsub s))
  quiet-unsub {s = pend _ _}               ()
  quiet-unsub {s = coldS true _}           _             = tt
  quiet-unsub {s = coldS false _}          _             = tt
  quiet-unsub {s = ofS _ _ _}              _             = tt
  quiet-unsub {s = doneS}                  _             = tt
  quiet-unsub {s = mapS _ s}               q             = quiet-unsub {s = s} q
  quiet-unsub {s = scanS _ _ s}            q             = quiet-unsub {s = s} q
  quiet-unsub {s = cutS _ _ _}             q             = q
  quiet-unsub {s = lnS _ _}                q             = q
  quiet-unsub {s = takeS _ _ _ s}          q             = quiet-cut {s = s} q
  quiet-unsub {s = flatS _ _ _ _ _ _ o ls} (qo , ql)    = quiet-cut {s = o} qo , quiet-kill {ls = ls} ql
  quiet-unsub {s = connS k _ b}            (f , qo , qb) = f , quiet-unsubIf (CS.srcAtt k) qo , quiet-unsub {s = b} qb
  quiet-unsub {s = joinS _ _ _ _}          _             = tt

  quiet-cut : ∀ {Γ A} {s : St Γ A} → Quiet s → Quiet (proj₁ (cut s))
  quiet-cut {s = cutS _ attached s}  q = quiet-unsub {s = s} q
  quiet-cut {s = cutS _ (attAt _) s} q = quiet-off {s = s} q
  quiet-cut {s = pend _ _}           q = q
  quiet-cut {s = coldS _ _}          q = q
  quiet-cut {s = ofS _ _ _}          q = q
  quiet-cut {s = doneS}              q = q
  quiet-cut {s = mapS _ _}           q = q
  quiet-cut {s = scanS _ _ _}        q = q
  quiet-cut {s = lnS _ _}            q = q
  quiet-cut {s = takeS _ _ _ _}      q = q
  quiet-cut {s = flatS _ _ _ _ _ _ _ _} q = q
  quiet-cut {s = connS _ _ _}        q = q
  quiet-cut {s = joinS _ _ _ _}      q = q

  quiet-kill : ∀ {Γ A} {ls : List (St Γ A)} → QuietL ls → QuietL (proj₁ (killAll ls))
  quiet-kill {ls = []}                          _        = tt
  quiet-kill {ls = lnS true s ∷ ls}              (q , ql) = quiet-cut {s = s} q , quiet-kill {ls = ls} ql
  quiet-kill {ls = lnS false _ ∷ ls}             (q , ql) = q , quiet-kill {ls = ls} ql
  quiet-kill {ls = pend _ _ ∷ ls}                (q , ql) = q , quiet-kill {ls = ls} ql
  quiet-kill {ls = coldS _ _ ∷ ls}               (q , ql) = q , quiet-kill {ls = ls} ql
  quiet-kill {ls = ofS _ _ _ ∷ ls}               (q , ql) = q , quiet-kill {ls = ls} ql
  quiet-kill {ls = doneS ∷ ls}                   (q , ql) = q , quiet-kill {ls = ls} ql
  quiet-kill {ls = mapS _ _ ∷ ls}                (q , ql) = q , quiet-kill {ls = ls} ql
  quiet-kill {ls = scanS _ _ _ ∷ ls}             (q , ql) = q , quiet-kill {ls = ls} ql
  quiet-kill {ls = cutS _ _ _ ∷ ls}              (q , ql) = q , quiet-kill {ls = ls} ql
  quiet-kill {ls = takeS _ _ _ _ ∷ ls}           (q , ql) = q , quiet-kill {ls = ls} ql
  quiet-kill {ls = flatS _ _ _ _ _ _ _ _ ∷ ls}   (q , ql) = q , quiet-kill {ls = ls} ql
  quiet-kill {ls = connS _ _ _ ∷ ls}             (q , ql) = q , quiet-kill {ls = ls} ql
  quiet-kill {ls = joinS _ _ _ _ ∷ ls}           (q , ql) = q , quiet-kill {ls = ls} ql

  quiet-unsubIf : ∀ {Γ A} b {s : St Γ A} → Quiet s → Quiet (proj₁ (unsubIf b s))
  quiet-unsubIf true  {s} q = quiet-unsub {s = s} q
  quiet-unsubIf false     q = q

-- UNSUBSCRIBING keeps every isle: it never reaches a source in its
-- subscribe call.
-- An unsubscribe its flag withholds.
unsubIf-off : ∀ {Γ A} b {s : St Γ A} → T (not b) → proj₁ (unsubIf b s) ≡ s
unsubIf-off false _ = refl

mutual
  unsub-husk : ∀ {Γ} {sc : Scope Γ} {D} {A} {s : St Γ A} {E P} → Husk sc D s E P → Σ Pts λ P′ → Husk sc D (proj₁ (unsub s)) E P′ × P ⊑ P′
  unsub-husk {s = s} (h-blank q) = _ , h-blank (quiet-unsub {s = s} q) , ⊑-refl
  unsub-husk (h-map hk u)     = let (_ , h , le) = unsub-husk hk in _ , h-map h u , le
  unsub-husk (h-scan hk u)    = let (_ , h , le) = unsub-husk hk in _ , h-scan h u , le
  unsub-husk (h-cut hk u)     = _ , h-cut hk u , ⊑-refl
  unsub-husk (h-ln hk u)      = _ , h-ln hk u , ⊑-refl
  unsub-husk (h-take hk u)    = let (_ , h , le) = cut-husk hk in _ , h-take h u , le
  unsub-husk (h-flat ho u hl) = let (_ , h , le) = cut-husk ho ; (_ , g , le′) = kill-husk hl in _ , h-flat h u g , ∪-⊑ le le′
  unsub-husk (h-conn sh bh u) = let (_ , h , le) = srch-unsub sh ; (_ , g , le′) = unsub-husk bh in _ , h-conn h g u , ∪-⊑ le le′

  cut-husk : ∀ {Γ} {sc : Scope Γ} {D} {A} {s : St Γ A} {E P} → Husk sc D s E P → Σ Pts λ P′ → Husk sc D (proj₁ (cut s)) E P′ × P ⊑ P′
  cut-husk {s = s} (h-blank q)        = _ , h-blank (quiet-cut {s = s} q) , ⊑-refl
  cut-husk (h-cut {a = attached} hk u) = let (_ , h , le) = unsub-husk hk in _ , h-cut h u , le
  cut-husk (h-cut {a = attAt _} hk u)  = _ , h-cut (off-husk hk) u , ⊑-refl
  cut-husk hk@(h-map _ _)              = _ , hk , ⊑-refl
  cut-husk hk@(h-scan _ _)             = _ , hk , ⊑-refl
  cut-husk hk@(h-ln _ _)               = _ , hk , ⊑-refl
  cut-husk hk@(h-take _ _)             = _ , hk , ⊑-refl
  cut-husk hk@(h-flat _ _ _)           = _ , hk , ⊑-refl
  cut-husk hk@(h-conn _ _ _)           = _ , hk , ⊑-refl

  kill-husk : ∀ {Γ} {sc : Scope Γ} {D} {A} {ls : List (St Γ A)} {E P} → HuskL sc D ls E P → Σ Pts λ P′ → HuskL sc D (proj₁ (killAll ls)) E P′ × P ⊑ P′
  kill-husk hl-none                            = _ , hl-none , ⊑-refl
  kill-husk (hl-more {l = l} (h-blank q) u hl) = kill-blank l q u hl
  kill-husk (hl-more (h-ln {b = true} hk w) u hl) = let (_ , h , le) = cut-husk hk ; (_ , g , le′) = kill-husk hl in _ , hl-more (h-ln h w) u g , ∪-⊑ le le′
  kill-husk (hl-more hk@(h-ln {b = false} _ _) u hl) = kill-keep hk u hl
  kill-husk (hl-more hk@(h-map _ _) u hl)      = kill-keep hk u hl
  kill-husk (hl-more hk@(h-scan _ _) u hl)     = kill-keep hk u hl
  kill-husk (hl-more hk@(h-cut _ _) u hl)      = kill-keep hk u hl
  kill-husk (hl-more hk@(h-take _ _) u hl)     = kill-keep hk u hl
  kill-husk (hl-more hk@(h-flat _ _ _) u hl)   = kill-keep hk u hl
  kill-husk (hl-more hk@(h-conn _ _ _) u hl)   = kill-keep hk u hl

  -- A list entry no kill reaches, kept.
  kill-keep : ∀ {Γ} {sc : Scope Γ} {D D₁} {A} {l : St Γ A} {ls E₁ E P Q} → Husk sc D₁ l E₁ P → Up D₁ E₁ D E → HuskL sc D ls E Q
            → Σ Pts λ P′ → HuskL sc D (l ∷ proj₁ (killAll ls)) E P′ × (P ∪ᵖ Q) ⊑ P′
  kill-keep hk u hl = let (_ , g , le) = kill-husk hl in _ , hl-more hk u g , ∪-⊑ ⊑-refl le

  kill-blank : ∀ {Γ} {sc : Scope Γ} {D D₁} {A} (l : St Γ A) {ls E₁ E Q} → Quiet l → Up D₁ E₁ D E → HuskL sc D ls E Q
             → Σ Pts λ P′ → HuskL sc D (proj₁ (killAll (l ∷ ls))) E P′ × (∅ᵖ ∪ᵖ Q) ⊑ P′
  kill-blank (lnS true s)        q u hl = let (_ , g , le) = kill-husk hl in _ , hl-more (h-blank (quiet-cut {s = s} q)) u g , ∪-⊑ ⊑-refl le
  kill-blank (lnS false _)       q u hl = kill-keep (h-blank q) u hl
  kill-blank (pend _ _)          q u hl = kill-keep (h-blank q) u hl
  kill-blank (coldS _ _)         q u hl = kill-keep (h-blank q) u hl
  kill-blank (ofS _ _ _)         q u hl = kill-keep (h-blank q) u hl
  kill-blank doneS               q u hl = kill-keep (h-blank q) u hl
  kill-blank (mapS _ _)          q u hl = kill-keep (h-blank q) u hl
  kill-blank (scanS _ _ _)       q u hl = kill-keep (h-blank q) u hl
  kill-blank (cutS _ _ _)        q u hl = kill-keep (h-blank q) u hl
  kill-blank (takeS _ _ _ _)     q u hl = kill-keep (h-blank q) u hl
  kill-blank (flatS _ _ _ _ _ _ _ _) q u hl = kill-keep (h-blank q) u hl
  kill-blank (connS _ _ _)       q u hl = kill-keep (h-blank q) u hl
  kill-blank (joinS _ _ _ _)     q u hl = kill-keep (h-blank q) u hl

  unsubIf-husk : ∀ {Γ} {sc : Scope Γ} {D} {A} {s : St Γ A} {E P} b → Husk sc D s E P → Σ Pts λ P′ → Husk sc D (proj₁ (unsubIf b s)) E P′ × P ⊑ P′
  unsubIf-husk true  hk = unsub-husk hk
  unsubIf-husk false hk = _ , hk , ⊑-refl

  srch-unsub : ∀ {Γ X B} {sc : Scope Γ} {D} {k : CS Γ X} {o} {E : EmissionSet B} {P} → SrcH sc D k o E P
             → Σ Pts λ P′ → SrcH sc D k (proj₁ (unsubIf (CS.srcAtt k) o)) E P′ × P ⊑ P′
  srch-unsub {k = k} (sh-dead hk u sf) = let (_ , h , le) = unsubIf-husk (CS.srcAtt k) hk in _ , sh-dead h u sf , under-⊑ le
  srch-unsub {k = k} sh@(sh-isle na _ _ _ _ _ _ _ _ _)  = _ , subst (λ o′ → SrcH _ _ k o′ _ _) (sym (unsubIf-off (CS.srcAtt k) na)) sh , ⊑-refl
  srch-unsub {k = k} sh@(sh-islec na _ _ _ _ _ _ _ _ _ _ _) = _ , subst (λ o′ → SrcH _ _ k o′ _ _) (sym (unsubIf-off (CS.srcAtt k) na)) sh , ⊑-refl
  srch-unsub {k = k} sh@(sh-pend na _ _ _ _ _ _ _ _ _ _) = _ , subst (λ o′ → SrcH _ _ k o′ _ _) (sym (unsubIf-off (CS.srcAtt k) na)) sh , ⊑-refl

------------------------------------------------------------------------
-- NO ISLE IN A PART: every connect in it attached, closed, or not yet
-- subscribed.  An isle's subscribe call is still running, so whatever
-- runs lies inside its source: a connect whose source rises has no isle
-- in its body, and a row fed there reaches none.

isPend : ∀ {Γ A} → St Γ A → Bool
isPend (pend _ _) = true
isPend _          = false

Pending : ∀ {Γ A} → St Γ A → Set
Pending s = T (isPend s)

-- A pending subscription by its shape.
pend-shape : ∀ {Γ A} (s : St Γ A) → Pending s → Σ (Obs Timeline Γ A) λ o → Σ Pos λ q → s ≡ pend o q
pend-shape (pend o q) _ = o , q , refl
pend-shape (coldS _ _) ()
pend-shape (ofS _ _ _) ()
pend-shape doneS ()
pend-shape (mapS _ _) ()
pend-shape (scanS _ _ _) ()
pend-shape (cutS _ _ _) ()
pend-shape (lnS _ _) ()
pend-shape (takeS _ _ _ _) ()
pend-shape (flatS _ _ _ _ _ _ _ _) ()
pend-shape (connS _ _ _) ()
pend-shape (joinS _ _ _ _) ()

-- Not an isle.
Settles : ∀ {Γ X} → CS Γ X → St Γ X → Set
Settles k o = T (CS.srcAtt k) ⊎ T (CS.closed k) ⊎ Pending o

mutual
  NoIsle : ∀ {Γ A} → St Γ A → Set
  NoIsle (mapS _ s)                = NoIsle s
  NoIsle (scanS _ _ s)             = NoIsle s
  NoIsle (cutS _ _ s)              = NoIsle s
  NoIsle (lnS _ s)                 = NoIsle s
  NoIsle (takeS _ _ _ s)           = NoIsle s
  NoIsle (flatS _ _ _ _ _ _ o ls)  = NoIsle o × NoIsleL ls
  NoIsle (connS k o b)             = Settles k o × NoIsle o × NoIsle b
  NoIsle _                         = ⊤

  NoIsleL : ∀ {Γ A} → List (St Γ A) → Set
  NoIsleL []       = ⊤
  NoIsleL (l ∷ ls) = NoIsle l × NoIsleL ls

-- The path clear: no isle in the body of a connect whose source it
-- enters.
Clear : ∀ {R Γ A} → Ctx R Γ A → Set
Clear top                                 = ⊤
Clear (inMap _ c)                         = Clear c
Clear (inScan _ _ c)                      = Clear c
Clear (inCut _ _ c)                       = Clear c
Clear (inLn _ c)                          = Clear c
Clear (inTake _ _ _ c)                    = Clear c
Clear (inOuter _ _ _ _ _ _ _ c)           = Clear c
Clear (inLanes _ _ _ _ _ _ _ _ _ c)       = Clear c
Clear (inSrc _ b c)                       = NoIsle b × Clear c
Clear (inBody _ _ c)                      = Clear c

-- A node in step is no pending subscription.
sync-pend : ∀ {Γ} {sc : Scope Γ} {Rg C A} {s : St Γ A} {E} → Pending s → Sync sc Rg C s E → ⊥
sync-pend {s = s} p sy with pend-shape s p
... | _ , _ , refl with sy
...   | ()
