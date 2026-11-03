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
open import operation.PureObservable using (module Machine)

open Machine using (St; Ctx; Scope; binds; CS; subscribing; absorbed;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    unsub; cut; killAll; unsubIf; off; offL; offIf; attached; attAt;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (_≃_; Frozen; full; pendRows)
open import adequacy.Cursor using (Begun; Husk; HuskL; LaneSt; Parts; Pol; Pts; Quiet; QuietL; Sound; Src; SrcH; Sync; Torn; _∪ᵖ_; _⊑_; h-blank; h-conn; h-cut; h-flat; h-ln; h-map; h-scan; h-take; hl-more; hl-none; joined; l-dead; l-live; more; none; s-cold; s-conn; s-cut; s-done; s-flat; s-join; s-joinx; s-map; s-of; s-scan; s-take; s-took; sh-dead; sh-isle; sh-islec; sh-pend; src-on; src-pend; src-shut; under-⊑; ∅ᵖ; ∪-⊑; ⊑-refl)

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
unbind : ∀ {Γ X B} {k : CS Γ X} {sc} {b : St (X ∷ Γ) B} {Q} → CS.scope k ≡ sc
       → Husk (binds (CS.src k) (CS.connAt k) sc) b Q → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) b Q
unbind refl h = h

mutual
  husk-of : ∀ {Γ} {sc : Scope Γ} {Rg C A} {s : St Γ A} {E} → Sync sc Rg C s E → Σ Pts (Husk sc s)
  husk-of (s-cold _ _ _)            = _ , h-blank tt
  husk-of (s-of _ _)                = _ , h-blank tt
  husk-of (s-done _ _)              = _ , h-blank tt
  husk-of (s-map sy _ _)            = _ , h-map (proj₂ (husk-of sy))
  husk-of (s-scan sy _ _ _)         = _ , h-scan (proj₂ (husk-of sy))
  husk-of (s-cut sy)                = _ , h-cut (proj₂ (husk-of sy))
  husk-of (s-take sy _ _ _)         = _ , h-take (proj₂ (husk-of sy))
  husk-of (s-took _ _ _ _ _ hk _ _) = _ , h-take hk
  husk-of (s-flat _ sy (joined bg _ _ _ _ _ _ _) _ _ _) = _ , h-flat (proj₂ (husk-of sy)) (proj₂ (begun-husk bg))
  husk-of (s-conn {k = k} sc pt bs _ ss tn _ _) =
    by (CS.srcLive k) (λ l → _ , h-conn (proj₂ (src-husk sc (ss l) (Parts.ss pt))) (unbind {k = k} sc (proj₂ (husk-of (bs l)))))
                      (λ nl → _ , h-conn (Torn.sh (tn nl)) (Torn.bh (tn nl)))
  husk-of (s-join _ _ _ _ _)        = _ , h-blank tt
  husk-of (s-joinx _ _)             = _ , h-blank tt

  src-husk : ∀ {Γ X} {sc : Scope Γ} {Rg C} {k : CS Γ X} {o} → CS.scope k ≡ sc → Src sc Rg C k o → Sound Rg (Frozen k) → Σ Pts (SrcH sc k o)
  src-husk sc (src-pend na nc ba an adm pe wn _) ss    = _ , sh-pend na nc ba an sc adm pe wn ss
  src-husk _ (src-on {k = k} nc sy bh sd _ ao) ss       = by (CS.srcAtt k) (λ t → _ , sh-dead (proj₂ (husk-of sy)) (inj₁ t)) (λ na → _ , sh-isle na nc sy bh sd ss (ao na))
  src-husk _ (src-shut {C = C} {k = k} cl sp tp hk bh sd) _ = by (CS.srcAtt k) (λ t → _ , sh-dead hk (inj₁ t)) (λ na → _ , sh-islec {Ci = C} na cl sp tp hk bh sd)

  begun-husk : ∀ {Γ A B} {sc : Scope Γ} {Rl C} {P : Pol A B} {O vs ls n} → Begun sc Rl C P O vs ls n → Σ Pts (HuskL sc ls)
  begun-husk none               = _ , hl-none
  begun-husk (more _ _ _ ln bg) = _ , hl-more (proj₂ (lane-husk ln)) (proj₂ (begun-husk bg))

  lane-husk : ∀ {Γ A B} {sc : Scope Γ} {Rg C} {P : Pol A B} {q a l b} → LaneSt sc Rg C P q a l b → Σ Pts (Husk sc l)
  lane-husk (l-live _ sy _) = _ , h-ln (h-cut (proj₂ (husk-of sy)))
  lane-husk (l-dead _ hk)   = _ , h-ln (h-cut hk)

-- One node's state in from what still runs around it.
peel-take : ∀ {Γ} {sc : Scope Γ} {A} {i} {keep : A → Bool} {w s Q} → Husk sc (takeS i keep w s) Q → Σ Pts λ Q′ → Husk sc s Q′ × Q ⊑ Q′
peel-take (h-blank q) = _ , h-blank q , ⊑-refl
peel-take (h-take hk) = _ , hk , ⊑-refl

peel-cut : ∀ {Γ} {sc : Scope Γ} {A} {l a} {s : St Γ A} {Q} → Husk sc (cutS l a s) Q → Σ Pts λ Q′ → Husk sc s Q′ × Q ⊑ Q′
peel-cut (h-blank q) = _ , h-blank q , ⊑-refl
peel-cut (h-cut hk) = _ , hk , ⊑-refl

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
  off-husk : ∀ {Γ} {sc : Scope Γ} {A} {s : St Γ A} {P} → Husk sc s P → Husk sc (off s) P
  off-husk {s = s} (h-blank q) = h-blank (quiet-off {s = s} q)
  off-husk (h-map hk)     = h-map (off-husk hk)
  off-husk (h-scan hk)    = h-scan (off-husk hk)
  off-husk (h-cut hk)     = h-cut (off-husk hk)
  off-husk (h-ln hk)      = h-ln (off-husk hk)
  off-husk (h-take hk)    = h-take (off-husk hk)
  off-husk (h-flat ho hl) = h-flat (off-husk ho) (offL-husk hl)
  off-husk (h-conn sh bh) = h-conn (srch-off sh) (off-husk bh)

  offL-husk : ∀ {Γ} {sc : Scope Γ} {A} {ls : List (St Γ A)} {P} → HuskL sc ls P → HuskL sc (offL ls) P
  offL-husk hl-none       = hl-none
  offL-husk (hl-more h t) = hl-more (off-husk h) (offL-husk t)

  srch-off : ∀ {Γ X} {sc : Scope Γ} {k : CS Γ X} {o P} → SrcH sc k o P → SrcH sc k (offIf (CS.srcAtt k) o) P
  srch-off {k = k} (sh-dead hk sf) = sh-dead (offIf-husk (CS.srcAtt k) hk) sf
  srch-off {k = k} sh@(sh-isle na _ _ _ _ _ _)  = subst (λ o′ → SrcH _ k o′ _) (sym (offIf-off (CS.srcAtt k) na)) sh
  srch-off {k = k} sh@(sh-islec na _ _ _ _ _ _) = subst (λ o′ → SrcH _ k o′ _) (sym (offIf-off (CS.srcAtt k) na)) sh
  srch-off {k = k} sh@(sh-pend na _ _ _ _ _ _ _ _) = subst (λ o′ → SrcH _ k o′ _) (sym (offIf-off (CS.srcAtt k) na)) sh

  offIf-husk : ∀ {Γ} {sc : Scope Γ} {A} {s : St Γ A} {P} b → Husk sc s P → Husk sc (offIf b s) P
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
  unsub-husk : ∀ {Γ} {sc : Scope Γ} {A} {s : St Γ A} {P} → Husk sc s P → Σ Pts λ P′ → Husk sc (proj₁ (unsub s)) P′ × P ⊑ P′
  unsub-husk {s = s} (h-blank q) = _ , h-blank (quiet-unsub {s = s} q) , ⊑-refl
  unsub-husk (h-map hk)     = let (_ , h , le) = unsub-husk hk in _ , h-map h , le
  unsub-husk (h-scan hk)    = let (_ , h , le) = unsub-husk hk in _ , h-scan h , le
  unsub-husk (h-cut hk)     = _ , h-cut hk , ⊑-refl
  unsub-husk (h-ln hk)      = _ , h-ln hk , ⊑-refl
  unsub-husk (h-take hk)    = let (_ , h , le) = cut-husk hk in _ , h-take h , le
  unsub-husk (h-flat ho hl) = let (_ , h , le) = cut-husk ho ; (_ , g , le′) = kill-husk hl in _ , h-flat h g , ∪-⊑ le le′
  unsub-husk (h-conn sh bh) = let (_ , h , le) = srch-unsub sh ; (_ , g , le′) = unsub-husk bh in _ , h-conn h g , ∪-⊑ le le′

  cut-husk : ∀ {Γ} {sc : Scope Γ} {A} {s : St Γ A} {P} → Husk sc s P → Σ Pts λ P′ → Husk sc (proj₁ (cut s)) P′ × P ⊑ P′
  cut-husk {s = s} (h-blank q)      = _ , h-blank (quiet-cut {s = s} q) , ⊑-refl
  cut-husk (h-cut {a = attached} hk) = let (_ , h , le) = unsub-husk hk in _ , h-cut h , le
  cut-husk (h-cut {a = attAt _} hk)  = _ , h-cut (off-husk hk) , ⊑-refl
  cut-husk hk@(h-map _)              = _ , hk , ⊑-refl
  cut-husk hk@(h-scan _)             = _ , hk , ⊑-refl
  cut-husk hk@(h-ln _)               = _ , hk , ⊑-refl
  cut-husk hk@(h-take _)             = _ , hk , ⊑-refl
  cut-husk hk@(h-flat _ _)           = _ , hk , ⊑-refl
  cut-husk hk@(h-conn _ _)           = _ , hk , ⊑-refl

  kill-husk : ∀ {Γ} {sc : Scope Γ} {A} {ls : List (St Γ A)} {P} → HuskL sc ls P → Σ Pts λ P′ → HuskL sc (proj₁ (killAll ls)) P′ × P ⊑ P′
  kill-husk hl-none                          = _ , hl-none , ⊑-refl
  kill-husk (hl-more {l = l} (h-blank q) hl) = kill-blank l q hl
  kill-husk (hl-more (h-ln {b = true} hk) hl) = let (_ , h , le) = cut-husk hk ; (_ , g , le′) = kill-husk hl in _ , hl-more (h-ln h) g , ∪-⊑ le le′
  kill-husk (hl-more hk@(h-ln {b = false} _) hl) = kill-keep hk hl
  kill-husk (hl-more hk@(h-map _) hl)        = kill-keep hk hl
  kill-husk (hl-more hk@(h-scan _) hl)       = kill-keep hk hl
  kill-husk (hl-more hk@(h-cut _) hl)        = kill-keep hk hl
  kill-husk (hl-more hk@(h-take _) hl)       = kill-keep hk hl
  kill-husk (hl-more hk@(h-flat _ _) hl)     = kill-keep hk hl
  kill-husk (hl-more hk@(h-conn _ _) hl)     = kill-keep hk hl

  -- A list entry no kill reaches, kept.
  kill-keep : ∀ {Γ} {sc : Scope Γ} {A} {l : St Γ A} {ls P Q} → Husk sc l P → HuskL sc ls Q
            → Σ Pts λ P′ → HuskL sc (l ∷ proj₁ (killAll ls)) P′ × (P ∪ᵖ Q) ⊑ P′
  kill-keep hk hl = let (_ , g , le) = kill-husk hl in _ , hl-more hk g , ∪-⊑ ⊑-refl le

  kill-blank : ∀ {Γ} {sc : Scope Γ} {A} (l : St Γ A) {ls Q} → Quiet l → HuskL sc ls Q
             → Σ Pts λ P′ → HuskL sc (proj₁ (killAll (l ∷ ls))) P′ × (∅ᵖ ∪ᵖ Q) ⊑ P′
  kill-blank (lnS true s)        q hl = let (_ , g , le) = kill-husk hl in _ , hl-more (h-blank (quiet-cut {s = s} q)) g , ∪-⊑ ⊑-refl le
  kill-blank (lnS false _)       q hl = kill-keep (h-blank q) hl
  kill-blank (pend _ _)          q hl = kill-keep (h-blank q) hl
  kill-blank (coldS _ _)         q hl = kill-keep (h-blank q) hl
  kill-blank (ofS _ _ _)         q hl = kill-keep (h-blank q) hl
  kill-blank doneS               q hl = kill-keep (h-blank q) hl
  kill-blank (mapS _ _)          q hl = kill-keep (h-blank q) hl
  kill-blank (scanS _ _ _)       q hl = kill-keep (h-blank q) hl
  kill-blank (cutS _ _ _)        q hl = kill-keep (h-blank q) hl
  kill-blank (takeS _ _ _ _)     q hl = kill-keep (h-blank q) hl
  kill-blank (flatS _ _ _ _ _ _ _ _) q hl = kill-keep (h-blank q) hl
  kill-blank (connS _ _ _)       q hl = kill-keep (h-blank q) hl
  kill-blank (joinS _ _ _ _)     q hl = kill-keep (h-blank q) hl

  unsubIf-husk : ∀ {Γ} {sc : Scope Γ} {A} {s : St Γ A} {P} b → Husk sc s P → Σ Pts λ P′ → Husk sc (proj₁ (unsubIf b s)) P′ × P ⊑ P′
  unsubIf-husk true  hk = unsub-husk hk
  unsubIf-husk false hk = _ , hk , ⊑-refl

  srch-unsub : ∀ {Γ X} {sc : Scope Γ} {k : CS Γ X} {o P} → SrcH sc k o P
             → Σ Pts λ P′ → SrcH sc k (proj₁ (unsubIf (CS.srcAtt k) o)) P′ × P ⊑ P′
  srch-unsub {k = k} (sh-dead hk sf) = let (_ , h , le) = unsubIf-husk (CS.srcAtt k) hk in _ , sh-dead h sf , under-⊑ le
  srch-unsub {k = k} sh@(sh-isle na _ _ _ _ _ _)  = _ , subst (λ o′ → SrcH _ k o′ _) (sym (unsubIf-off (CS.srcAtt k) na)) sh , ⊑-refl
  srch-unsub {k = k} sh@(sh-islec na _ _ _ _ _ _) = _ , subst (λ o′ → SrcH _ k o′ _) (sym (unsubIf-off (CS.srcAtt k) na)) sh , ⊑-refl
  srch-unsub {k = k} sh@(sh-pend na _ _ _ _ _ _ _ _) = _ , subst (λ o′ → SrcH _ k o′ _) (sym (unsubIf-off (CS.srcAtt k) na)) sh , ⊑-refl

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
