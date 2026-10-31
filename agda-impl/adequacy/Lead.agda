{-# OPTIONS --guardedness #-}

-- THE FOUND OF LEADS: whatever the search finds, every other part of each
-- merge it rose through lies strictly past it.  A part lost a race: either
-- strictly, so its rows lie past the winner's key, or on a tie, where the
-- winner owns a row at that key and the parts are apart, so the loser's
-- rows there are none.  The winner's key is its event's position or past
-- it, and a lane's later siblings lose ties to it.
module adequacy.Lead where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Bool.Properties using (T-≡)
open import Function.Bundles using (Equivalence)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; drop)
open import Data.List.Relation.Unary.All using ([]) renaming (_∷_ to _∷ᴬ_)
open import Data.Nat using (ℕ; pred; _≡ᵇ_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᴹ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; Timeline; ix; last; emit; stall; close)
open import denotation.EmissionSet using (EmissionSet; DenEnv; Truncate; module Joining; Work; out; skip; pin; end; at-out; at-skip; at-end)
open import denotation.Laws.Modulus using (≺-ext)
open import operation.Key using (Key; at; _<ᴷ_; at-<ᵖ; clash)
open import operation.PureObservable using (module Machine; Tape; play; ending; over)
open Machine using (St; Ctx; CS; Cand; found; Mark; ofM; attM; leafM; Att; Out; still; shows; nx; cp; seek; search; kids; lanes; own; ownBest; first; retag;
                    raceT; outerT; laneT; mapT; scanT; cutT; alive; outOf; closed; attached; attAt;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; cs; bodyM; _⊕_; shift)
open import adequacy.Rows using (env; rows; rowsL; pendRows; toEv; Lanes; Each; module BoundedF)
open import adequacy.Bound using (held; rooted-single; _⊑_; ⊑i; ⊑-refl; ⊑-trans; <→⊑; ext-⊑; From; Bd; OK; OKL; Live; Apart; Spread;
  Parts; rooted-parts; ⊑→≼; MergeG; G; GL; GLn; Good; ofPos; from-weak; lane-ok; raise-map; raise-scan; raise-cut; raise-outer; raise-lane; shift-⊑)
  renaming (After to Afterᶜ)
open import adequacy.Cap using (Before; OKᶜ; OKLᶜ; cap-retag; Quiet; QuietL; EnvGood; body-quiet; first-at; own-stills)
open import adequacy.Search using (bind-good; seek-okᶜ; seek-lnᶜ; lanes-okᶜ; join-okᶜ; calm-fst; calm-snd; flat-race; switch-race; exhaust-race; bounded-race; queued-race; lanes-single; switch-at)
open import adequacy.Flags using (Flags; flat-flags; switch-flags; exhaust-flags; bounded-flags; queued-flags)
open import adequacy.Skip using (After; LeadC)
open import adequacy.ConnLead using (conn-free-lead; conn-held-lead; conn-off-lead)
open import adequacy.Leads using (⊑-<; <-⊑; Beats; Ext; Fits; LeadE; Leads; Leadsᶜ; Occ; OfAt; Tight; before-retag; cut-off; cut-on; eLanes; eOuter; each-past; exact; first-leads; first-leadsᶜ; from-lost; from-none; froms-lost; hit; lead-ext; leads-trunc; lmap; ln-leads; lost-strict; lost-strict-each; lzip; map-leads; none-aft; nones-aft; occ; occ-bind; past-tie; scan-leads; stop; strict; tie; tight-occ; tight-⊑; uncap-lead; up)

open _⊑_
open Bd
open Occ

-- The lanes of a merge, raced among themselves

-- The winning lane's place in its list: the lanes before it lose to it
-- strictly, as the walk saw them; the ones after it lose, ties included.
LL : ∀ {R Γ A B} → Bool → Ctx R Γ B → FlatOp → (A → _) → Bool → _ → List A → St Γ A → List (St Γ B) → List (St Γ B) → Maybe (Cand R B) → Set₁
LL v c op f d n q o pre ls nothing = ⊤₁
LL {Γ = Γ} {B = B} v c op f d n q o pre ls (just (found (_ , _ , c′ , s′) m κ , K , o′)) =
  Σ (List (St Γ B)) λ pre₁ → Σ (List (St Γ B)) λ post₁ → Σ (Ext c′ (inLanes op f d n q o pre₁ post₁ c)) λ e →
    Live v (closed c′ ≡ false → ∀ P → OfAt s′ m P →
      LeadE e P × (Each (After P) (rowsL (env c) pre) → Each (After P) (rowsL (env c) pre₁)) × Each (After P) (rowsL (env c) post₁) × Tight (Lanes (rowsL (env c) ls)) P K o′)

LLᶜ : ∀ {R Γ A B} → Key → Bool → Ctx R Γ B → FlatOp → (A → _) → Bool → _ → List A → St Γ A → List (St Γ B) → List (St Γ B) → Maybe (Cand R B) → Set₁
LLᶜ C v c op f d n q o pre ls y = Before C y → LL v c op f d n q o pre ls y

lzip3 : ∀ v {X Y Z W : Set} → (X → Y → Z → W) → Live v X → Live v Y → Live v Z → Live v W
lzip3 true  h x y z = h x y z
lzip3 false h x y z = tt

-- A lane's rows read in its list: switched off, it owes nothing there.
x-tight : ∀ {Γ B} {ρ : DenEnv Γ} l a (s₀ : St Γ B) Ls {P K} {ox : Out B} → Tight (rows ρ (lnS l (cutS l a s₀))) P K ox
        → Tight (Lanes (rows ρ (lnS l (cutS l a s₀)) ∷ Ls)) P K (Data.Bool.if l then ox else still)
x-tight true  a s₀ Ls tg               = tight-occ (λ oc → occ-bind oc λ x fe → hit (inj₁ x) fe) tg
x-tight false a s₀ Ls (strict lt)      = strict lt
x-tight false a s₀ Ls (tie Q eq pq oc) = ⊥-elim (unocc oc λ ())

-- One lane against the lanes after it: on a tie the earlier wins.
module Step {R Γ A B} (v : Bool) (c : Ctx R Γ B) (op : FlatOp) (f : A → Obs Timeline Γ B) (d : Bool) (n : ℕ) (q : List A) (o : St Γ A) (pre post : List (St Γ B))
            (l : Bool) (a : Att) (s₀ : St Γ B) where

  ρ : DenEnv Γ
  ρ = env c

  s : St Γ B
  s = lnS l (cutS l a s₀)

  ll-shift : ∀ {Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ K} {o′ : Out B}
           → LL v c op f d n q o (s ∷ pre) post (just (found (Γ′ , A′ , c′ , s′) m κ , K , o′))
           → Live v (∀ P → Tight (Lanes (rowsL ρ post)) P K o′ → After P (rows ρ s))
           → LL v c op f d n q o pre (s ∷ post) (just (found (Γ′ , A′ , c′ , s′) m κ , K , o′))
  ll-shift (pre₁ , post₁ , e , ly) as = pre₁ , post₁ , e , lzip v go ly as
    where
      go : _ → _ → _
      go ly as cl P oa = let r = ly cl P oa ; tg = proj₂ (proj₂ (proj₂ r)) in
        proj₁ r , (λ ea → proj₁ (proj₂ r) (as P tg , ea)) , proj₁ (proj₂ (proj₂ r)) , tight-occ (λ oc → occ-bind oc λ x fe → hit (inj₂ x) fe) tg

  x-wins : ∀ {Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ K} (ox : Out B) (e : Ext c′ (inLanes op f d n q o pre post c))
         → Live v (closed c′ ≡ false → ∀ P → OfAt s′ m P → LeadE e P × Tight (rows ρ s) P K ox)
         → Live v (∀ P → Tight (rows ρ s) P K ox → Each (After P) (rowsL ρ post))
         → LL v c op f d n q o pre (s ∷ post) (just (found (Γ′ , A′ , c′ , s′) m κ , cutT l K ox))
  x-wins ox e lx ap = pre , post , e , lzip v go lx ap
    where
      go : _ → _ → _
      go lx ap cl P oa = let r = lx cl P oa in proj₁ r , (λ ea → ea) , ap P (proj₂ r) , x-tight {ρ = ρ} l a s₀ (rowsL ρ post) (proj₂ r)

  step : ∀ C (x y : Maybe (Cand R B)) → Leadsᶜ C v (inLanes op f d n q o pre post c) (rows ρ s) x → LLᶜ C v c op f d n q o (s ∷ pre) post y
       → Live v (OKᶜ C (rows ρ s) (retag (cutT l) x)) → Live v (OKLᶜ C (rowsL ρ post) y) → Live v (Spread (rows ρ s ∷ rowsL ρ post))
       → LLᶜ C v c op f d n q o pre (s ∷ post) (first (retag (cutT l) x) y)
  step C nothing nothing _ _ _ _ _ ()
  step C nothing (just (found (_ , _ , c′ , s′) m κ , K , o′)) _ ly okx _ _ b =
    ll-shift {c′ = c′} {s′} {m} {κ} {K} {o′} (ly b)
      (lmap v {X = OKᶜ {R} C (rows ρ s) nothing} {Y = ∀ P → Tight (Lanes (rowsL ρ post)) P K o′ → After P (rows ρ s)}
         (λ ok P tg → none-aft {R = R} {t = rows ρ s} {C = C} {K = K} (⊑i b) ok P (tight-⊑ tg)) okx)
  step C (just (found (_ , _ , c′ , s′) m κ , K , ox)) nothing lx _ _ oky _ b =
    x-wins {c′ = c′} {s′} {m} {κ} {K} ox (proj₁ (lx b)) (proj₂ (lx b))
      (lmap v {X = OKLᶜ {R} C (rowsL ρ post) nothing} {Y = ∀ P → Tight (rows ρ s) P K ox → Each (After P) (rowsL ρ post)}
         (λ ok P tg → nones-aft {R = R} {C = C} {K = K} (rowsL ρ post) (⊑i b) ok P (tight-⊑ tg)) oky)
  step C (just (found (_ , _ , c′ , s′) m κ , K , ox)) (just (found (_ , _ , c″ , s″) m′ κ′ , K′ , o′)) lx ly okx oky sp b with K′ <ᴷ K in lt
  ... | true  = ll-shift {c′ = c″} {s″} {m′} {κ′} {K′} {o′} (ly b)
                  (lmap v {X = OKᶜ C (rows ρ s) (retag (cutT l) (just (found (_ , _ , c′ , s′) m κ , K , ox)))} {Y = ∀ P → Tight (Lanes (rowsL ρ post)) P K′ o′ → After P (rows ρ s)}
                     (λ ok P tg → lost-strict {R = R} {t = rows ρ s} {C = C} {P = P} {K = K} {K′ = K′} {g = found (_ , _ , c′ , s′) m κ} (tight-⊑ tg) (⊑i b) lt ok) okx)
  ... | false = x-wins {c′ = c′} {s′} {m} {κ} {K} ox (proj₁ (lx b)) (proj₂ (lx b))
                  (lzip v {X = OKLᶜ C (rowsL ρ post) (just (found (_ , _ , c″ , s″) m′ κ′ , K′ , o′))} {Z = ∀ P → Tight (rows ρ s) P K ox → Each (After P) (rowsL ρ post)}
                     (λ ok (sp : Spread (rows ρ s ∷ rowsL ρ post)) P tg → each-past (rowsL ρ post) tg (proj₁ sp) (froms-lost {R = R} {C = C} {K = K} {K′ = K′} {g = found (_ , _ , c″ , s″) m′ κ′} (rowsL ρ post) (⊑i b) (⊑i lt) ok)) oky sp)

------------------------------------------------------------------------
-- A merge: the outer against the lanes

-- A row neither a value nor an end shown: some work.
fits-work : ∀ {B} {o : Out B} → ¬ o ≡ shows cp → ∀ {e} → Fits o e → Work e
fits-work no {out _} _  = tt
fits-work no {skip}  _  = tt
fits-work no {pin _} _  = tt
fits-work no {end}   eq = ⊥-elim (no eq)

-- The lanes' find at or before the cap: exact.
exactL : ∀ {R B} C {Ls : List (EmissionSet B)} (y : Maybe (Cand R B)) → Before C y → OKLᶜ C Ls y → OKL Ls y
exactL C nothing  ()
exactL C (just _) b (inj₁ (p , _)) = ⊥-elim (clash p b)
exactL C (just _) b (inj₂ (_ , o)) = o

-- Just past a position, strictly.
ext-< : ∀ Q → at Q <ᴷ at (Q ++ [ ix 0 ]) ≡ true
ext-< Q = trans (at-<ᵖ Q (Q ++ [ ix 0 ])) (Equivalence.to T-≡ (≺-ext Q []))

module Race {R Γ A B} (v : Bool) (c : Ctx R Γ B) (op : FlatOp) (f : A → Obs Timeline Γ B) (d : Bool) (n : ℕ) (o : St Γ A) (ls : List (St Γ B))
            (Ln : Pos → A → EmissionSet B) (Bg : EmissionSet B) (Over Runs : Pos → Set) (Cut : Pos → Pos → Set) (Hand : Pos → Set)
            (bg-at : ∀ {Q e} → From (at Q) (rows (env c) o) → Lanes (rowsL (env c) ls) Q e → Bg Q e) where

  ρ : DenEnv Γ
  ρ = env c

  module J = Joining Ln (rows ρ o) Bg Over Runs Cut Hand

  FR : EmissionSet B
  FR = J.JoinT

  -- A lane's row, no later than every outer row, neither a value nor an
  -- end shown: begun, and the merge's own.
  lane-occ : ∀ {Q} (o′ : Out B) → ¬ o′ ≡ shows cp → From (at Q) (rows ρ o) → Occ (Lanes (rowsL ρ ls)) Q o′ → Occ FR Q o′
  lane-occ o′ no fk oc = occ-bind oc λ x fe → hit (J.run (bg-at fk x) (fits-work no fe)) fe

  -- A lane's end shown, nothing queued, every part no earlier: handing
  -- off to none, the merge's end exactly where its flag shows it.
  lane-end : ∀ {Q} → Flags (rows ρ o) (rowsL ρ ls) Over Hand d n [] → Parts (rows ρ o) (rowsL ρ ls) → From (at Q) (rows ρ o) → Each (From (at Q)) (rowsL ρ ls)
           → Occ (Lanes (rowsL ρ ls)) Q (shows cp) → Occ FR Q (proj₂ (laneT {A = A} d n [] (at Q) (shows cp)))
  lane-end {Q} (nh , lf , _) pa fk fl oc with d ∧ (pred n ≡ᵇ 0)
  ... | true  = occ-bind oc go
    where
      go : ∀ {e} → Lanes (rowsL ρ ls) Q e → Fits (shows cp) e → Occ FR Q (shows cp)
      go {e = out _} x ()
      go {e = skip}  x _ = hit (J.run (bg-at fk x) tt) tt
      go {e = pin _} x _ = hit (J.run (bg-at fk x) tt) tt
      go {e = end}   x _ = occ λ k → k (J.rpass (bg-at fk x) (nh (proj₁ pa) fk x) λ dn → k (J.rend (bg-at fk x) (nh (proj₁ pa) fk x) dn) refl) tt
  ... | false = occ-bind oc go
    where
      go : ∀ {e} → Lanes (rowsL ρ ls) Q e → Fits (shows cp) e → Occ FR Q still
      go {e = out _} x ()
      go {e = skip}  x _ = hit (J.run (bg-at fk x) tt) tt
      go {e = pin _} x _ = hit (J.run (bg-at fk x) tt) tt
      go {e = end}   x _ = hit (J.rpass (bg-at fk x) (nh (proj₁ pa) fk x) λ dn → lf pa fk fl x (proj₁ dn)) tt

  -- The outer's end shown, every lane past it: the merge's end exactly
  -- where its flag shows it.
  outer-end : ∀ q → Flags (rows ρ o) (rowsL ρ ls) Over Hand d n q → ∀ {Q} → From (at Q) (rows ρ o) → Each (After Q) (rowsL ρ ls) → rows ρ o Q end
            → Occ FR Q (proj₂ (outerT {B = B} n q (at Q) (shows cp)))
  outer-end [] (_ , _ , of) fo al r with n ≡ᵇ 0
  ... | true  = occ λ k → k (J.opass r λ dn → k (J.oend r dn) refl) tt
  ... | false = hit (J.opass r λ dn → of fo al (proj₁ dn)) tt
  outer-end (_ ∷ _) of fo al r with n ≡ᵇ 0
  ... | true  = hit (J.opass r λ dn → of fo al (proj₁ dn)) tt
  ... | false = hit (J.opass r λ dn → of fo al (proj₁ dn)) tt

  outer-still : ∀ {Q} → Occ (rows ρ o) Q still → Occ FR Q still
  outer-still oc = occ-bind oc go
    where
      go : ∀ {Q e} → rows ρ o Q e → Fits still e → Occ FR Q still
      go {e = out _} r ()
      go {e = skip}  r _ = hit (J.step r) tt
      go {e = pin _} r _ = hit (J.opin r) tt
      go {e = end}   r ()

  -- On a tie, the outer no earlier than the lane's row.
  tight-from : ∀ {P k} {o′ o″ : Out B} → (∀ {Q} → From (at Q) (rows ρ o) → Occ (Lanes (rowsL ρ ls)) Q o′ → Occ FR Q o″) → From k (rows ρ o)
             → Tight (Lanes (rowsL ρ ls)) P k o′ → Tight FR P k o″
  tight-from h fk (strict lt)      = strict lt
  tight-from h fk (tie Q eq pq oc) = tie Q eq pq (h (subst (λ K → From K (rows ρ o)) eq fk) oc)

  lane-tight : ∀ q → Flags (rows ρ o) (rowsL ρ ls) Over Hand d n q → ∀ {P k} (o′ : Out B) → Parts (rows ρ o) (rowsL ρ ls) → From k (rows ρ o) → Each (From k) (rowsL ρ ls)
             → Tight (Lanes (rowsL ρ ls)) P k o′ → Tight FR P (proj₁ (laneT {A = A} d n q k o′)) (proj₂ (laneT {A = A} d n q k o′))
  lane-tight []      st still          pa fk fl tg = tight-from (lane-occ still (λ ())) fk tg
  lane-tight (_ ∷ _) st still          pa fk fl tg = tight-from (lane-occ still (λ ())) fk tg
  lane-tight []      st (shows (nx b)) pa fk fl tg = tight-from (lane-occ (shows (nx b)) (λ ())) fk tg
  lane-tight (_ ∷ _) st (shows (nx b)) pa fk fl tg = tight-from (lane-occ (shows (nx b)) (λ ())) fk tg
  lane-tight []      st (shows cp)     pa fk fl (strict lt)        = strict lt
  lane-tight []      st (shows cp)     pa fk fl (tie Q refl pq oc) = tie Q refl pq (lane-end st pa fk fl oc)
  lane-tight (_ ∷ _) st {P} {k} (shows cp) pa fk fl (strict lt)        = strict (<-⊑ {at P} {k} {shift k} lt (shift-⊑ k))
  lane-tight (_ ∷ _) st {P}     (shows cp) pa fk fl (tie Q refl pq oc) = strict (⊑-< {at P} {at Q} {at (Q ++ [ ix 0 ])} pq (ext-< Q))

  outer-tight : ∀ q → Flags (rows ρ o) (rowsL ρ ls) Over Hand d n q → ∀ {P h} (ox : Out A) → Tight (rows ρ o) P h ox → From h (rows ρ o)
              → (∀ P′ → at P′ ⊑ h → Each (After P′) (rowsL ρ ls)) → (∀ {e} → ox ≡ shows e → Σ Pos λ q₀ → h ≡ at q₀ × rows ρ o q₀ (toEv e))
              → Tight FR P (proj₁ (outerT {B = B} n q h ox)) (proj₂ (outerT {B = B} n q h ox))
  outer-tight q st still tg fh al sh = tight-occ outer-still tg
  outer-tight q st (shows (nx x)) tg fh al sh with sh refl
  ... | q₀ , refl , r = tie (q₀ ++ [ ix 0 ]) refl (⊑-trans (tight-⊑ tg) (ext-⊑ q₀ [ ix 0 ])) (hit (J.val r) tt)
  outer-tight q st (shows cp) tg fh al sh with sh refl
  ... | q₀ , refl , r = tie q₀ refl (tight-⊑ tg) (outer-end q st fh (al q₀ (⊑-refl _)) r)

  outer-wins : ∀ q → Flags (rows ρ o) (rowsL ρ ls) Over Hand d n q → ∀ {Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ h} (ox : Out A) (e : Ext c′ (inOuter op f d n q ls c))
             → Live v (closed c′ ≡ false → ∀ P → OfAt s′ m P → LeadE e P × Tight (rows ρ o) P h ox)
             → Live v (Bd (rows ρ o) κ h ox)
             → Live v (∀ P → at P ⊑ h → Each (After P) (rowsL ρ ls))
             → Leads v c FR (just (found (Γ′ , A′ , c′ , s′) m κ , outerT n q h ox))
  outer-wins q st ox e lx b al = eOuter e , lzip3 v go lx b al
    where
      go : _ → _ → _ → _
      go lx b al cl P oa = let r = lx cl P oa in (al P (tight-⊑ (proj₂ r)) , proj₁ r) , outer-tight q st ox (proj₂ r) (Bd.from b) al (Bd.shown b)

  lane-wins : ∀ q → Flags (rows ρ o) (rowsL ρ ls) Over Hand d n q → ∀ {Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ k} (o′ : Out B) pre₁ post₁ (e : Ext c′ (inLanes op f d n q o pre₁ post₁ c))
            → Live v (closed c′ ≡ false → ∀ P → OfAt s′ m P → LeadE e P × (⊤ → Each (After P) (rowsL ρ pre₁)) × Each (After P) (rowsL ρ post₁) × Tight (Lanes (rowsL ρ ls)) P k o′)
            → Live v (∀ P → Tight (Lanes (rowsL ρ ls)) P k o′ → After P (rows ρ o))
            → Live v (From k (rows ρ o) × Each (From k) (rowsL ρ ls) × Parts (rows ρ o) (rowsL ρ ls))
            → Leads v c FR (just (found (Γ′ , A′ , c′ , s′) m κ , laneT {A = A} d n q k o′))
  lane-wins q st o′ pre₁ post₁ e ly ao fp = eLanes e , lzip3 v go ly ao fp
    where
      go : _ → _ → _ → _
      go ly ao (fk , fl , pa) cl P oa = let r = ly cl P oa ; tg = proj₂ (proj₂ (proj₂ r)) in
        (ao P tg , proj₁ (proj₂ r) tt , proj₁ (proj₂ (proj₂ r)) , proj₁ r) , lane-tight q st o′ pa fk fl tg

  race-leads : ∀ q → Flags (rows ρ o) (rowsL ρ ls) Over Hand d n q → ∀ C (x : Maybe (Cand R A)) (y : Maybe (Cand R B))
             → Leadsᶜ C v (inOuter op f d n q ls c) (rows ρ o) x → LLᶜ C v c op f d n q o [] ls y
             → Live v (OKᶜ C (rows ρ o) x) → Live v (OKLᶜ C (rowsL ρ ls) y) → Live v (Parts (rows ρ o) (rowsL ρ ls))
             → Leadsᶜ C v c FR (raceT d n q x y)
  race-leads q st C nothing nothing _ _ _ _ _ ()
  race-leads q st C nothing (just (found (_ , _ , c′ , s′) m κ , k , o′)) _ ly okx oky pa b =
    let kC = up {K = k} {C = C} (raise-lane {A} d n q k o′) b ; (pre₁ , post₁ , e , l) = ly (un kC) in
    lane-wins q st {c′ = c′} {s′} {m} {κ} {k} o′ pre₁ post₁ e l
      (lmap v {X = OKᶜ {R} C (rows ρ o) nothing} {Y = ∀ P → Tight (Lanes (rowsL ρ ls)) P k o′ → After P (rows ρ o)}
         (λ ok P tg → none-aft {R = R} {t = rows ρ o} {C = C} {K = k} kC ok P (tight-⊑ tg)) okx)
      (lzip3 v {X = OKᶜ {R} C (rows ρ o) nothing} {Y = OKLᶜ C (rowsL ρ ls) (just (found (_ , _ , c′ , s′) m κ , k , o′))}
         {Z = Parts (rows ρ o) (rowsL ρ ls)} {W = From k (rows ρ o) × Each (From k) (rowsL ρ ls) × Parts (rows ρ o) (rowsL ρ ls)}
         (λ ok okl p → from-none {R = R} {t = rows ρ o} {C = C} {K = k} kC ok , proj₁ (exactL C (just (found (_ , _ , c′ , s′) m κ , k , o′)) (un kC) okl) , p) okx oky pa)
  race-leads q st C (just (found (_ , _ , c′ , s′) m κ , h , ox)) nothing lx _ okx oky _ b =
    let hC = up {K = h} {C = C} (raise-outer {B = B} n q h ox) b in
    outer-wins q st {c′ = c′} {s′} {m} {κ} {h} ox (proj₁ (lx (un hC))) (proj₂ (lx (un hC)))
      (lmap v (exact C (just (found (_ , _ , c′ , s′) m κ , h , ox)) (un hC)) okx)
      (lmap v {X = OKLᶜ {R} C (rowsL ρ ls) nothing} {Y = ∀ P → at P ⊑ h → Each (After P) (rowsL ρ ls)}
         (λ ok P ph → nones-aft {R = R} {C = C} {K = h} (rowsL ρ ls) hC ok P ph) oky)
  race-leads q st C (just (found (_ , _ , c′ , s′) m κ , h , ox)) (just (found (_ , _ , c″ , s″) m′ κ′ , k , o′)) lx ly okx oky pa b
    with h <ᴷ k in lt
  ... | true  =
    let hC = up {K = h} {C = C} (raise-outer {B = B} n q h ox) b in
    outer-wins q st {c′ = c′} {s′} {m} {κ} {h} ox (proj₁ (lx (un hC))) (proj₂ (lx (un hC)))
      (lmap v (exact C (just (found (_ , _ , c′ , s′) m κ , h , ox)) (un hC)) okx)
      (lmap v {X = OKLᶜ C (rowsL ρ ls) (just (found (_ , _ , c″ , s″) m′ κ′ , k , o′))} {Y = ∀ P → at P ⊑ h → Each (After P) (rowsL ρ ls)}
         (λ ok P ph → lost-strict-each {R = R} {C = C} {P = P} {K = h} {K′ = k} {g = found (_ , _ , c″ , s″) m′ κ′} (rowsL ρ ls) ph hC lt ok) oky)
  ... | false =
    let kC = up {K = k} {C = C} (raise-lane {A} d n q k o′) b ; (pre₁ , post₁ , e′ , l) = ly (un kC) in
    lane-wins q st {c′ = c″} {s″} {m′} {κ′} {k} o′ pre₁ post₁ e′ l
      (lzip v {X = OKᶜ C (rows ρ o) (just (found (_ , _ , c′ , s′) m κ , h , ox))} {Z = ∀ P → Tight (Lanes (rowsL ρ ls)) P k o′ → After P (rows ρ o)}
         (λ ok (pa : Parts (rows ρ o) (rowsL ρ ls)) P tg → past-tie {u = rows ρ o} tg (from-lost {R = R} {t = rows ρ o} {C = C} {h = h} {k = k} {f = found (_ , _ , c′ , s′) m κ} kC lt ok)
                                                            (λ {q} {e} {e′} x r → proj₁ pa {q} {e′} {e} r x)) okx pa)
      (lzip3 v {X = OKᶜ C (rows ρ o) (just (found (_ , _ , c′ , s′) m κ , h , ox))} {Y = OKLᶜ C (rowsL ρ ls) (just (found (_ , _ , c″ , s″) m′ κ′ , k , o′))}
         {Z = Parts (rows ρ o) (rowsL ρ ls)} {W = From k (rows ρ o) × Each (From k) (rowsL ρ ls) × Parts (rows ρ o) (rowsL ρ ls)}
         (λ ok okl p → from-lost {R = R} {t = rows ρ o} {C = C} {h = h} {k = k} {f = found (_ , _ , c′ , s′) m κ} kC lt ok , proj₁ (exactL C (just (found (_ , _ , c″ , s″) m′ κ′ , k , o′)) (un kC) okl) , p) okx oky pa)

------------------------------------------------------------------------
-- Every node

of-out : ∀ {R Γ A} (c : Ctx R Γ A) {i p x xs} → closed c ≡ false → outOf c (ofS i p (x ∷ xs)) ofM ≡ shows (nx x)
of-out c cl with closed c
of-out c () | true
of-out c cl | false = refl

of-end : ∀ {R Γ A} (c : Ctx R Γ A) {i p} → closed c ≡ false → outOf c (ofS {A = A} i p []) ofM ≡ shows cp
of-end c cl with closed c
of-end c () | true
of-end c cl | false = refl

-- Marks no of owns lead nothing.
own-none : ∀ {R Γ A} v (c : Ctx R Γ A) {s : St Γ A} {t} ms → (∀ {m P} → OfAt s m P → ⊥) → Leads v c t (ownBest c s ms)
own-none v     c []       no = tt₁
own-none v c {s} {t} ((m , k) ∷ ms) no = first-leads {v = v} {c = c} {t = t} (just (found (_ , _ , c , s) m k , k , outOf c s m)) (ownBest c s ms) (one v) (λ _ → own-none v c ms no)
  where
    one : ∀ v → Leads v c t (just (found (_ , _ , c , s) m k , k , outOf c s m))
    one true  = stop , λ cl P oa → ⊥-elim (no oa)
    one false = stop , tt

-- A cold's own mark leads: its tape's next step keys its rows, tight.
cold-lead : ∀ {R Γ A} v (c : Ctx R Γ A) b (l : Tape A) → Leads v c (rows (env c) (coldS b l)) (ownBest c (coldS b l) (own (coldS {Γ = Γ} b l)))
cold-lead v     c b     over                       = tt₁
cold-lead false c b     (play τ u i t fr)          = stop , tt
cold-lead false c b     (ending e)                 = stop , tt
cold-lead true  c false (play τ u i t fr)          = stop , λ _ _ ()
cold-lead true  c false (ending e)                 = stop , λ _ _ ()
cold-lead true  c true  (play τ u i t (emit a k))  with closed c
... | false = stop , λ _ _ eq → tt , tie _ refl (subst (λ q → at _ ⊑ at q) eq (⊑-refl _)) (hit at-out refl)
... | true  = stop , λ ()
cold-lead true  c true  (play τ u i t (stall k))   = stop , λ _ _ eq → tt , tie _ refl (subst (λ q → at _ ⊑ at q) eq (⊑-refl _)) (hit at-skip tt)
cold-lead true  c true  (play τ u i t (close k))   = stop , λ _ _ eq → tt , tie _ refl (subst (λ q → at _ ⊑ at q) eq (⊑-refl _)) (hit at-skip tt)
cold-lead true  c true  (ending e)                 with closed c
... | false = stop , λ _ _ eq → tt , tie _ refl (subst (λ q → at _ ⊑ at q) eq (⊑-refl _)) (hit at-end refl)
... | true  = stop , λ ()

-- What is asked of a live node only: nothing under a cut switched off.
data Gate (P : Set₁) : Bool → Set₁ where
  on  : P → Gate P true
  off : Gate P false

gate : ∀ {P Q v} → (P → Q) → Gate P v → Gate Q v
gate f (on p) = on (f p)
gate f off    = off

gate-on : ∀ {P Q} v → (P → Q) → Gate P v → Gate Q (v Data.Bool.∧ true)
gate-on .true  f (on p) = on (f p)
gate-on .false f off    = off

gate-off : ∀ {Q} v → Gate Q (v Data.Bool.∧ false)
gate-off true  = off
gate-off false = off

postulate
  -- A TAKE'S SEARCH LEADS: unfailed, its child's find through the take,
  -- every part it lost past the shown event; failed, nothing shown.
  take-leadᶜ : ∀ {R Γ A} C v (c : Ctx R Γ A) i q w (s : St Γ A) → Gate (EnvGood (env c)) v → G (env c) v (takeS i q w s) → Gate (Quiet C (env c) (takeS i q w s)) v
             → Leadsᶜ C v c (rows (env c) (takeS i q w s)) (kids c (takeS i q w s))


own-lead : ∀ {R Γ A} v (c : Ctx R Γ A) (s : St Γ A) → G (env c) v s → Leads v c (rows (env c) s) (ownBest c s (own s))
own-lead true  c (ofS i p [])         _ = stop , λ { cl _ refl → tt , tie (p ++ [ last ]) refl (⊑-refl _) (hit {e = end} at-end (of-end c {i} {p} cl)) }
own-lead true  c (ofS i p (x ∷ xs))   _ = stop , λ { cl _ refl → tt , tie (p ++ [ ix i ]) refl (⊑-refl _) (hit {e = out x} at-out (of-out c {i} {p} {x} {xs} cl)) }
own-lead true  c (cutS l (attAt q) s) _ = stop , λ cl P ()
own-lead false c (ofS i p [])         _ = stop , tt
own-lead false c (ofS i p (x ∷ xs))   _ = stop , tt
own-lead false c (cutS l (attAt q) s) _ = stop , tt
own-lead v c (cutS l attached s)  _ = tt₁
own-lead v c (mapS f s)           _ = tt₁
own-lead v c doneS                _ = tt₁
own-lead v c (pend o _)             _ = tt₁
own-lead v c (flatS op f d n q o ls) _ = tt₁
own-lead v c (lnS b s)            ()
own-lead v c (scanS f z s)        _ = tt₁
own-lead v c (coldS b l)          _ = cold-lead v c b l
own-lead v c (takeS i q w s)      _ = own-none v c {takeS i q w s} (own (takeS i q w s)) (λ ())
own-lead v c (connS k o b)        _ = own-none v c {connS k o b} (own (connS k o b)) (λ ())
own-lead v c (joinS j g x ib)     _ = own-none v c {joinS j g x ib} (own (joinS j g x ib)) (λ ())

-- A live node's search, at or before the cap.
okᵛ : ∀ {R Γ A} C v (c : Ctx R Γ A) (s : St Γ A) → Gate (EnvGood (env c)) v → G (env c) v s → Gate (Quiet C (env c) s) v → Before C (seek c s) → Live v (OK (rows (env c) s) (seek c s))
okᵛ C true  c s (on es) g (on qt) b = exact C (seek c s) b (seek-okᶜ C c s es g qt)
okᵛ C false c s es g qt b = tt

mutual
  seek-leadᶜ : ∀ {R Γ A} C v (c : Ctx R Γ A) (s : St Γ A) → Gate (EnvGood (env c)) v → G (env c) v s → Gate (Quiet C (env c) s) v → Leadsᶜ C v c (rows (env c) s) (seek c s)
  seek-leadᶜ C v c s es g qt = first-leadsᶜ C (ownBest c s (own s)) (kids c s) (own-lead v c s g) (λ w → kids-leadᶜ C v c s es g qt w)

  kids-leadᶜ : ∀ {R Γ A} C v (c : Ctx R Γ A) (s : St Γ A) → Gate (EnvGood (env c)) v → G (env c) v s → Gate (Quiet C (env c) s) v
             → Beats (ownBest c s (own s)) (kids c s) → Leadsᶜ C v c (rows (env c) s) (kids c s)
  kids-leadᶜ C v c (mapS f s) es g qt _ b =
    map-leads v f (seek (inMap f c) s) (seek-leadᶜ C v (inMap f c) s es g (gate (λ q {X} → q {X}) qt) (before-retag C (mapT f) (raise-map f) (seek (inMap f c) s) b))
  kids-leadᶜ C v c (cutS true a s) es g qt _ b =
    cut-on v (seek (inCut true a c) s) (seek-leadᶜ C (v Data.Bool.∧ true) (inCut true a c) s (gate-on {P = EnvGood (env c)} {Q = EnvGood (env c)} v (λ e → e) es) g (gate-on v (λ q {X} → q {X}) qt) (before-retag C (cutT true) (raise-cut true) (seek (inCut true a c) s) b))
  kids-leadᶜ C v c (cutS false a s) es g qt _ b =
    cut-off v (seek (inCut false a c) s) (seek-leadᶜ C (v Data.Bool.∧ false) (inCut false a c) s (gate-off v) g (gate-off v) (before-retag C (cutT false) (raise-cut false) (seek (inCut false a c) s) b))
  kids-leadᶜ C true c (flatS (mergeᶠ nothing) f d n q o ls) (on es) g (on qt) _ with MergeG.fresh g
  ... | refl = join-leadᶜ C true c (mergeᶠ nothing) f d n [] o ls (λ _ x → x) (flat-flags (λ a → pendRows (env c) (f a)) (rows (env c) o) d n (rowsL (env c) ls)) (on es) outer lanesG (on (calm-fst C (env c) qt)) (on (calm-snd C (env c) qt)) (rooted-parts rooted)
                 (join-okᶜ C c (mergeᶠ nothing) f d n [] o ls (flat-race (λ a → pendRows (env c) (f a)) (rows (env c) o) (rowsL (env c) ls) d n (rooted-single rooted) spent)
                    es outer lanesG (calm-fst C (env c) qt) (calm-snd C (env c) qt))
    where open MergeG g
  kids-leadᶜ C false c (flatS (mergeᶠ nothing) f d n q o ls) es g qt _ with MergeG.fresh g
  ... | refl = join-leadᶜ C false c (mergeᶠ nothing) f d n [] o ls (λ _ x → x) (flat-flags (λ a → pendRows (env c) (f a)) (rows (env c) o) d n (rowsL (env c) ls)) es (MergeG.outer g) (MergeG.lanesG g) off off tt tt
  kids-leadᶜ C true c (flatS (mergeᶠ (just m)) f d n [] o ls) (on es) (g , _) (on qt) _ =
    join-leadᶜ C true c (mergeᶠ (just m)) f d n [] o ls (λ _ x → begun x) (bounded-flags m (λ a → pendRows (env c) (f a)) (rows (env c) o) d n (rowsL (env c) ls)) (on es) outer lanesG (on (calm-fst C (env c) qt)) (on (calm-snd C (env c) qt)) (rooted-parts rooted)
      (join-okᶜ C c (mergeᶠ (just m)) f d n [] o ls (bounded-race m (λ a → pendRows (env c) (f a)) (rows (env c) o) (rowsL (env c) ls) d n (rooted-single rooted) spent)
         es outer lanesG (calm-fst C (env c) qt) (calm-snd C (env c) qt))
    where open MergeG g
          open BoundedF m (λ a → pendRows (env c) (f a)) (rows (env c) o) d n [] (rowsL (env c) ls) using (begun)
  kids-leadᶜ C false c (flatS (mergeᶠ (just m)) f d n [] o ls) es (g , _) qt _ =
    join-leadᶜ C false c (mergeᶠ (just m)) f d n [] o ls (λ _ x → begun x) (bounded-flags m (λ a → pendRows (env c) (f a)) (rows (env c) o) d n (rowsL (env c) ls)) es (MergeG.outer g) (MergeG.lanesG g) off off tt tt
    where open BoundedF m (λ a → pendRows (env c) (f a)) (rows (env c) o) d n [] (rowsL (env c) ls) using (begun)
  kids-leadᶜ C true c (flatS (mergeᶠ (just m)) f d n (a ∷ q) o ls) (on es) (g , full) (on qt) _ =
    join-leadᶜ C true c (mergeᶠ (just m)) f d n (a ∷ q) o ls (λ _ x → begun x) (queued-flags m (λ a → pendRows (env c) (f a)) (rows (env c) o) d n a q (rowsL (env c) ls))
      (on es) outer lanesG (on (calm-fst C (env c) qt)) (on (calm-snd C (env c) qt)) (rooted-parts rooted)
      (join-okᶜ C c (mergeᶠ (just m)) f d n (a ∷ q) o ls
         (queued-race m (λ a → pendRows (env c) (f a)) (rows (env c) o) (rowsL (env c) ls) d n a q (rooted-single rooted) (lanes-single ls (proj₁ es) lanesG) (rooted-parts rooted)
            ([ (λ ()) , (λ e → e) ]′ full))
         es outer lanesG (calm-fst C (env c) qt) (calm-snd C (env c) qt))
    where open MergeG g
          open BoundedF m (λ a → pendRows (env c) (f a)) (rows (env c) o) d n (a ∷ q) (rowsL (env c) ls) using (begun)
  kids-leadᶜ C false c (flatS (mergeᶠ (just m)) f d n (a ∷ q) o ls) es (g , _) qt _ =
    join-leadᶜ C false c (mergeᶠ (just m)) f d n (a ∷ q) o ls (λ _ x → begun x) (queued-flags m (λ a → pendRows (env c) (f a)) (rows (env c) o) d n a q (rowsL (env c) ls))
      es (MergeG.outer g) (MergeG.lanesG g) off off tt tt
    where open BoundedF m (λ a → pendRows (env c) (f a)) (rows (env c) o) d n (a ∷ q) (rowsL (env c) ls) using (begun)
  kids-leadᶜ C true c (flatS switchᶠ f d n q o ls) (on es) g (on qt) _ with MergeG.fresh g
  ... | refl = join-leadᶜ C true c switchᶠ f d n [] o ls (switch-at _ _ _ d n) (switch-flags (λ a → pendRows (env c) (f a)) (rows (env c) o) d n (rowsL (env c) ls)) (on es) outer lanesG (on (calm-fst C (env c) qt)) (on (calm-snd C (env c) qt)) (rooted-parts rooted)
                 (join-okᶜ C c switchᶠ f d n [] o ls (switch-race (λ a → pendRows (env c) (f a)) (rows (env c) o) (rowsL (env c) ls) d n (rooted-single rooted) spent)
                    es outer lanesG (calm-fst C (env c) qt) (calm-snd C (env c) qt))
    where open MergeG g
  kids-leadᶜ C false c (flatS switchᶠ f d n q o ls) es g qt _ with MergeG.fresh g
  ... | refl = join-leadᶜ C false c switchᶠ f d n [] o ls (switch-at _ _ _ d n) (switch-flags (λ a → pendRows (env c) (f a)) (rows (env c) o) d n (rowsL (env c) ls)) es (MergeG.outer g) (MergeG.lanesG g) off off tt tt
  kids-leadᶜ C true c (flatS exhaustᶠ f d n q o ls) (on es) g (on qt) _ with MergeG.fresh g
  ... | refl = join-leadᶜ C true c exhaustᶠ f d n [] o ls (λ _ x → x) (exhaust-flags (λ a → pendRows (env c) (f a)) (rows (env c) o) d n (rowsL (env c) ls)) (on es) outer lanesG (on (calm-fst C (env c) qt)) (on (calm-snd C (env c) qt)) (rooted-parts rooted)
                 (join-okᶜ C c exhaustᶠ f d n [] o ls (exhaust-race (λ a → pendRows (env c) (f a)) (rows (env c) o) (rowsL (env c) ls) d n (rooted-single rooted) spent)
                    es outer lanesG (calm-fst C (env c) qt) (calm-snd C (env c) qt))
    where open MergeG g
  kids-leadᶜ C false c (flatS exhaustᶠ f d n q o ls) es g qt _ with MergeG.fresh g
  ... | refl = join-leadᶜ C false c exhaustᶠ f d n [] o ls (λ _ x → x) (exhaust-flags (λ a → pendRows (env c) (f a)) (rows (env c) o) d n (rowsL (env c) ls)) es (MergeG.outer g) (MergeG.lanesG g) off off tt tt
  kids-leadᶜ C v c (ofS _ _ _)    _ _ _ _ ()
  kids-leadᶜ C v c doneS          _ _ _ _ ()
  kids-leadᶜ C v c (pend _ _)     _ _ _ _ ()
  kids-leadᶜ C v c (coldS _ _)    _ _ _ _ ()
  kids-leadᶜ C v c (joinS _ _ _ _) _ _ _ _ ()
  kids-leadᶜ C v c (lnS _ _)      _ () _ _
  kids-leadᶜ C true c (scanS f z s) es g qt _ b =
    let b′ = before-retag C (scanT f z) (raise-scan f z) (seek (inScan f z c) s) b in
    scan-leads true f z (seek (inScan f z c) s) (okᵛ C true (inScan f z c) s es g qt b′) (seek-leadᶜ C true (inScan f z c) s es g qt b′)
  kids-leadᶜ C false c (scanS f z s) es g qt _ b =
    scan-leads false f z (seek (inScan f z c) s) tt (seek-leadᶜ C false (inScan f z c) s es g qt (before-retag C (scanT f z) (raise-scan f z) (seek (inScan f z c) s) b))
  kids-leadᶜ C v c (takeS i q w s) es g qt _ = take-leadᶜ C v c i q w s es g qt
  kids-leadᶜ C true c (connS k@(cs cl sl sa nothing aS oA ca ea _) o b) (on es) g@(go , gb , _ , tl , _) (on qt) _ =
    conn-free-lead C c k o b es g (seek (inSrc k b c) o) (seek (inBody k o c) b) refl refl
      (seek-leadᶜ C true (inSrc k b c) o (on es) go (on (calm-fst C (env c) qt))) (seek-okᶜ C (inSrc k b c) o es go (calm-fst C (env c) qt))
      (λ C₂ c₂ air → let qb = body-quiet {C = C} {C₂ = C₂} {σ = rows (env c) o} k o b c₂ qt tl air in
         seek-leadᶜ C₂ true (inBody k o c) b (on (bind-good k o b es g)) gb (on qb) , seek-okᶜ C₂ (inBody k o c) b (bind-good k o b es g) gb qb)
  kids-leadᶜ C true c (connS k@(cs cl sl sa (just p) aS oA ca ea _) o b) (on es) g@(held hf , gb , _ , tl , _) (on qt) w =
    conn-held-lead C c k o b (p ⊕ [ ix 1 ]) hf (ownBest c (connS k o b) (own (connS k o b))) (seek (inBody k o c) b)
      (first-at {f = (_ , _ , c , connS k o b)} {m = bodyM} (at (p ⊕ [ ix 1 ])) (ownBest c (connS k o b) (drop 1 (own (connS k o b)))) (own-stills c k o b (drop 1 (own (connS k o b)))))
      (λ C₂ c₂ air → let qb = body-quiet {C = C} {C₂ = C₂} {σ = rows (env c) o} k o b c₂ qt tl air in
         seek-leadᶜ C₂ true (inBody k o c) b (on (bind-good k o b es g)) gb (on qb) , seek-okᶜ C₂ (inBody k o c) b (bind-good k o b es g) gb qb)
      w
  kids-leadᶜ C false c (connS k@(cs cl sl sa nothing aS oA ca ea _) o b) es (go , gb , _) qt w =
    conn-off-lead C c k o b (seek (inSrc k b c) o) (seek (inBody k o c) b) (seek-leadᶜ C false (inSrc k b c) o off go off) (seek-leadᶜ C false (inBody k o c) b off gb off)
  kids-leadᶜ C false c (connS k@(cs cl sl sa (just p) aS oA ca ea _) o b) es (held _ , gb , _) qt w =
    conn-off-lead C c k o b nothing (seek (inBody k o c) b) (λ ()) (seek-leadᶜ C false (inBody k o c) b off gb off)

  -- A joiner, by its policy and its flags: the race's find leads.
  join-leadᶜ : ∀ {R Γ A B} C v (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls
               {Ln : Pos → A → EmissionSet B} {Bg : EmissionSet B} {Over Runs : Pos → Set} {Cut : Pos → Pos → Set} {Hand : Pos → Set}
             → (∀ {Q e} → From (at Q) (rows (env c) o) → Lanes (rowsL (env c) ls) Q e → Bg Q e)
             → Flags (rows (env c) o) (rowsL (env c) ls) Over Hand d n q
             → Gate (EnvGood (env c)) v → G (env c) v o → GL (env c) v ls → Gate (Quiet C (env c) o) v → Gate (QuietL C (env c) ls) v
             → Live v (Parts (rows (env c) o) (rowsL (env c) ls))
             → Live v (OKᶜ C (Joining.JoinT Ln (rows (env c) o) Bg Over Runs Cut Hand)
                          (raceT d n q (seek (inOuter op f d n q ls c) o) (lanes c op f d n q o [] ls)))
             → Leadsᶜ C v c (Truncate (Joining.JoinT Ln (rows (env c) o) Bg Over Runs Cut Hand))
                            (raceT d n q (seek (inOuter op f d n q ls c) o) (lanes c op f d n q o [] ls))
  join-leadᶜ C true c op f d n q o ls {Ln} {Bg} {Over} {Runs} {Cut} {Hand} ba st (on es) go gl (on qo) (on ql) pa ok b =
    leads-trunc true (raceT d n q (seek (inOuter op f d n q ls c) o) (lanes c op f d n q o [] ls))
      (exact C (raceT d n q (seek (inOuter op f d n q ls c) o) (lanes c op f d n q o [] ls)) b ok)
      (Race.race-leads true c op f d n o ls Ln Bg Over Runs Cut Hand ba q st C
        (seek (inOuter op f d n q ls c) o) (lanes c op f d n q o [] ls)
        (seek-leadᶜ C true (inOuter op f d n q ls c) o (on es) go (on qo)) (lanes-leadᶜ C true c op f d n q o [] ls (on es) gl (on ql) (proj₂ pa))
        (seek-okᶜ C (inOuter op f d n q ls c) o es go qo) (lanes-okᶜ C c op f d n q o [] ls es gl ql) pa b)
  join-leadᶜ C false c op f d n q o ls {Ln} {Bg} {Over} {Runs} {Cut} {Hand} ba st es go gl qo ql pa ok b =
    leads-trunc false (raceT d n q (seek (inOuter op f d n q ls c) o) (lanes c op f d n q o [] ls)) tt
      (Race.race-leads false c op f d n o ls Ln Bg Over Runs Cut Hand ba q st C
        (seek (inOuter op f d n q ls c) o) (lanes c op f d n q o [] ls)
        (seek-leadᶜ C false (inOuter op f d n q ls c) o es go qo) (lanes-leadᶜ C false c op f d n q o [] ls es gl ql tt) tt tt tt b)

  seek-ln-leadᶜ : ∀ {R Γ A} C v (c : Ctx R Γ A) (s : St Γ A) → Gate (EnvGood (env c)) v → GLn (env c) v s → Gate (Quiet C (env c) s) v → Leadsᶜ C v c (rows (env c) s) (seek c s)
  seek-ln-leadᶜ C v c (lnS true (cutS .true a s₀)) es (refl , g₀ , _) qt b =
    ln-leads (seek (inLn true c) (cutS true a s₀)) (seek-leadᶜ C v (inLn true c) (cutS true a s₀) es g₀ qt b)
  seek-ln-leadᶜ C v c (lnS false (cutS .false a s₀)) es (refl , g₀ , _) qt b =
    ln-leads (seek (inLn false c) (cutS false a s₀)) (seek-leadᶜ C v (inLn false c) (cutS false a s₀) es g₀ qt b)
  seek-ln-leadᶜ C v c (lnS _ (pend _ _)) _ ()
  seek-ln-leadᶜ C v c (lnS _ (coldS _ _)) _ ()
  seek-ln-leadᶜ C v c (lnS _ (ofS _ _ _)) _ ()
  seek-ln-leadᶜ C v c (lnS _ (doneS)) _ ()
  seek-ln-leadᶜ C v c (lnS _ (mapS _ _)) _ ()
  seek-ln-leadᶜ C v c (lnS _ (scanS _ _ _)) _ ()
  seek-ln-leadᶜ C v c (lnS _ (lnS _ _)) _ ()
  seek-ln-leadᶜ C v c (lnS _ (takeS _ _ _ _)) _ ()
  seek-ln-leadᶜ C v c (lnS _ (flatS _ _ _ _ _ _ _)) _ ()
  seek-ln-leadᶜ C v c (lnS _ (connS _ _ _)) _ ()
  seek-ln-leadᶜ C v c (lnS _ (joinS _ _ _ _)) _ ()
  seek-ln-leadᶜ C v c (pend _ _) _ ()
  seek-ln-leadᶜ C v c (coldS _ _) _ ()
  seek-ln-leadᶜ C v c (ofS _ _ _) _ ()
  seek-ln-leadᶜ C v c doneS _ ()
  seek-ln-leadᶜ C v c (mapS _ _) _ ()
  seek-ln-leadᶜ C v c (scanS _ _ _) _ ()
  seek-ln-leadᶜ C v c (cutS _ _ _) _ ()
  seek-ln-leadᶜ C v c (takeS _ _ _ _) _ ()
  seek-ln-leadᶜ C v c (flatS _ _ _ _ _ _ _) _ ()
  seek-ln-leadᶜ C v c (connS _ _ _) _ ()
  seek-ln-leadᶜ C v c (joinS _ _ _ _) _ ()

  lanes-leadᶜ : ∀ {R Γ A B} C v (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre (ls : List (St Γ B)) → Gate (EnvGood (env c)) v → GL (env c) v ls → Gate (QuietL C (env c) ls) v
              → Live v (Spread (rowsL (env c) ls)) → LLᶜ C v c op f d n q o pre ls (lanes c op f d n q o pre ls)
  lanes-leadᶜ C v c op f d n q o pre [] _ _ _ _ ()
  lanes-leadᶜ C false c op f d n q o pre (lnS l (cutS .l a s₀) ∷ post) es (gs@(refl , _) , gp) ql sp =
    Step.step false c op f d n q o pre post l a s₀ C
      (seek (inLanes op f d n q o pre post c) (lnS l (cutS l a s₀))) (lanes c op f d n q o (lnS l (cutS l a s₀) ∷ pre) post)
      (seek-ln-leadᶜ C false (inLanes op f d n q o pre post c) (lnS l (cutS l a s₀)) es gs off)
      (lanes-leadᶜ C false c op f d n q o (lnS l (cutS l a s₀) ∷ pre) post es gp off tt) tt tt tt
  lanes-leadᶜ C true c op f d n q o pre (lnS l (cutS .l a s₀) ∷ post) (on es) (gs@(refl , _) , gp) (on ql) sp =
    Step.step true c op f d n q o pre post l a s₀ C
      (seek (inLanes op f d n q o pre post c) (lnS l (cutS l a s₀))) (lanes c op f d n q o (lnS l (cutS l a s₀) ∷ pre) post)
      (seek-ln-leadᶜ C true (inLanes op f d n q o pre post c) (lnS l (cutS l a s₀)) (on es) gs (on (calm-fst C (env c) ql)))
      (lanes-leadᶜ C true c op f d n q o (lnS l (cutS l a s₀) ∷ pre) post (on es) gp (on (calm-snd C (env c) ql)) (proj₂ sp))
      (cap-retag C (cutT l) (raise-cut l) (λ r → _ , _ , r , ⊑-refl _) (λ y → lane-ok (lnS l (cutS l a s₀)) y)
         (seek (inLanes op f d n q o pre post c) (lnS l (cutS l a s₀))) (seek-lnᶜ C (inLanes op f d n q o pre post c) (lnS l (cutS l a s₀)) es gs (calm-fst C (env c) ql)))
      (lanes-okᶜ C c op f d n q o (lnS l (cutS l a s₀) ∷ pre) post es gp (calm-snd C (env c) ql))
      sp
  lanes-leadᶜ C v c op f d n q o pre ((lnS _ (pend _ _)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre ((lnS _ (coldS _ _)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre ((lnS _ (ofS _ _ _)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre ((lnS _ (doneS)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre ((lnS _ (mapS _ _)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre ((lnS _ (scanS _ _ _)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre ((lnS _ (lnS _ _)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre ((lnS _ (takeS _ _ _ _)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre ((lnS _ (flatS _ _ _ _ _ _ _)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre ((lnS _ (connS _ _ _)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre ((lnS _ (joinS _ _ _ _)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre ((pend _ _) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre ((coldS _ _) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre ((ofS _ _ _) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre (doneS ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre ((mapS _ _) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre ((scanS _ _ _) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre ((cutS _ _ _) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre ((takeS _ _ _ _) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre ((flatS _ _ _ _ _ _ _) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre ((connS _ _ _) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n q o pre ((joinS _ _ _ _) ∷ post) _ (() , _) _ _

-- At no binder, every cap at once.
seek-lead : ∀ {R A} v (c : Ctx R [] A) (s : St [] A) → G (env c) v s → Leads v c (rows (env c) s) (seek c s)
seek-lead true  c s g = uncap-lead (seek c s) (λ C → seek-leadᶜ C true c s (on ((λ ()) , (λ ()))) g (on (λ ())))
seek-lead false c s g = uncap-lead (seek c s) (λ C → seek-leadᶜ C false c s off g off)

-- What the search finds at an of, every merge above it led.
lead-found : ∀ {R Γ A} {t : St [] R} {c : Ctx R Γ A} {s : St Γ A} {m κ P} → closed c ≡ false → OfAt s m P → Good [] t
           → search top t ≡ just (found (Γ , A , c , s) m κ) → LeadC c P
lead-found {R} {Γ} {A} {t} {c} {s} {m} {κ} {P} cl oa g fd = go (seek top t) (seek-lead true top t g) fd
  where
    go : (y : Maybe (Cand R R)) → Leads true top (rows [] t) y → mapᴹ proj₁ y ≡ just (found (Γ , A , c , s) m κ) → LeadC c P
    go (just (found (_ , _ , c′ , s′) m′ κ′ , K , o)) (e , l) refl = lead-ext e (proj₁ (l cl P oa)) tt
