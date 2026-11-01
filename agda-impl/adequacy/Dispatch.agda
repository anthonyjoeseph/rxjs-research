{-# OPTIONS --guardedness #-}

-- THE RUN, STEP BY STEP, OVER THE CURSOR: every step of the engine is
-- one of the cursor invariant's moves, dispatched by mode and frame; a
-- mark run is a search, moving the focus to the mark and the cursor to
-- just before what it delivers, then the node's own run.  Together they
-- are a `Simulation` of every program's run.
module adequacy.Dispatch where

open import Data.Bool using (Bool; true; false; if_then_else_; not; _∨_; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (_≡ᵇ_; suc)
open import Data.List using (List; []; _∷_; [_]; _ʳ++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᴹ)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Events using (Timeline; root; Pos; ix; last; timelineAt; emit; stall; close)
open import denotation.EmissionSet using (EmissionSet; enter; ⟦_⟧; out; end; at-out; at-end)
open import denotation.Laws.Modulus using (≺-ext)
open import operation.Key using (Key; _<ᴷ_; at)
open import operation.PureObservable using (due; PureObs; module Machine; module Driver; Tape; play; ending; over; opening)
open Machine using (St; Ctx; Conf; Scope; scopeOf; ⟨_,_,_,_⟩; subscribing; absorbed; rising; load; moved; plug; search; found; Mark; ofM; attM;
                    rise; run; alive; nx; cp; attAt; attached; Torn; Stepped; quiet; admit; closed; killAll; unsubIf; unsub; free; cpAt; cutAt; overAt;
                    cut; cpM; cutM; CS; cs; closedUp; _⊕_; unbound; seek; kids; lanes; own; ownBest; first; retag; raceT; sourceT; Cand; Out; bodyM; srcAttM; owedM; joinM; leafM; leaf; starting; turn;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
                    renaming (Shown to Shownᴹ; step to stepᴹ)
open import adequacy.Rows using (≃-refl; Vis; Past; Lowest; _≃_; _⇄_; silent; shown; Moves; this)
open _≃_
open import adequacy.Cursor using (Cur; Rgn; origin; bef; Spent; Due; Sync; _≈_; c-abs; c-sub; Inv; settled; pending; adrift; f-top;
  RT; SimC; keeps; Owes; Fr; Hold; Need; owes; lane; lanecut; pnd; s-of; s-join; s-joinx; s-took;
  f-off; f-map; f-scan; f-cut; f-take; f-took; f-outer; f-lanes; f-lane; f-lnct; f-src; f-srcc; f-srcp; f-srcx; f-body;
  o-cp; rise-top; rise-map; rise-scan-nx; rise-scan-cp; rise-take-pass; rise-take-cp; rise-cut; rise-cutx; rise-ln; rise-took; rise-take-fail; rise-bodyx; run-stop;
  run-cut; run-att)
open import adequacy.Simulation using (Simulation)
open import adequacy.Walk using (due-≈; climb; descend; refocus)
open import adequacy.Least using (Lo; Keeps; mapKp; scanKp; cutKp; takeKp; outerKp; laneKp; seek-lo; seek-none)
open import adequacy.Bound using (bound; shift; due-shift)
open import adequacy.Up using (rise-body-nx; rise-body-cp)

------------------------------------------------------------------------
-- Within what is grown, every step moves or finds nothing to do

Mv : ∀ {R} → Stepped R → Set
Mv (moved _ _ _) = ⊤
Mv _             = ⊥

admit-mv : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q o ls a p → Mv (admit c op f d n q o ls a p)
admit-mv c (Tree.mergeᶠ nothing)  f d n q o ls a p = tt
admit-mv c (Tree.mergeᶠ (just m)) f d n q o ls a p = tt
admit-mv c Tree.switchᶠ           f d n q o ls a p with killAll ls
... | _ = tt
admit-mv c Tree.exhaustᶠ          f d n q o ls a p with n ≡ᵇ 0
... | true  = tt
... | false = tt

rise-mv : ∀ {R Γ A} (c : Ctx R Γ A) s e p → Mv (rise c s e p)
rise-mv top                       s e      p = tt
rise-mv (inMap f c)               s e      p = tt
rise-mv (inScan f z c)            s (nx a) p = tt
rise-mv (inScan f z c)            s cp     p = tt
rise-mv (inCut l a c)             s e      p = tt
rise-mv (inLn b c)                s e      p = tt
rise-mv (inTake i q free c)       s (nx a) p with q a | i
... | true  | _     = tt
... | false | true  = tt
... | false | false = tt
rise-mv (inTake i q free c)       s cp     p = tt
rise-mv (inTake i q (cpAt r) c)   s e      p = tt
rise-mv (inTake i q (cutAt r) c)  s e      p = tt
rise-mv (inTake i q (overAt r) c) s e      p = tt
rise-mv (inOuter op f d n q ls c) o (nx a) p = admit-mv c op f d n q o ls a p
rise-mv (inOuter op f d n q ls c) o cp     p = tt
rise-mv (inLanes op f d n q o pre post c) s (nx b) p = tt
rise-mv (inLanes op f d n q o pre post c) s cp     p = tt
rise-mv (inSrc k b c)             s (nx a) p = tt
rise-mv (inSrc k b c)             s cp     p = tt
rise-mv (inBody k o c)            s (nx b) p with CS.srcLive k
... | true  = tt
... | false = tt
rise-mv (inBody k o c)            s cp     p with CS.srcLive k
... | true  = tt
... | false = tt

run-of-mv : ∀ {R Γ A} (c : Ctx R Γ A) i q (xs : List A) p → Mv (run c (ofS i q xs) ofM p)
run-of-mv c i q xs p with closed c | xs
... | true  | _     = tt
... | false | []    = tt
... | false | _ ∷ _ = tt

run-att-mv : ∀ {R Γ A} (c : Ctx R Γ A) l q (s : St Γ A) p → Mv (run c (cutS l (attAt q) s) attM p)
run-att-mv c l q s p with unsubIf (not l) s
... | _ = tt

run-con-mv : ∀ {R Γ A X} (c : Ctx R Γ A) k (o : St Γ X) b m p → m ≡ bodyM ⊎ (m ≡ srcAttM ⊎ m ≡ owedM) → Mv (run c (connS k o b) m p)
run-con-mv c k o b .bodyM p (inj₁ refl) with CS.bodyAt k
... | just _  = tt
... | nothing = tt
run-con-mv c k o b .srcAttM p (inj₂ (inj₁ refl)) with CS.attSrc k | unsubIf (not (CS.srcLive k)) o
... | just _  | _ = tt
... | nothing | _ = tt
run-con-mv c k o b .owedM p (inj₂ (inj₂ refl)) with CS.owedAt k | unsubIf (CS.srcAtt k) o
... | just _  | _ = tt
... | nothing | _ = tt

run-cut-mv : ∀ {R Γ A} (c : Ctx R Γ A) i (q : A → Bool) r (s : St Γ A) p → Mv (run c (takeS i q (cutAt r) s) cutM p)
run-cut-mv c i q r s p with cut s
... | _ = tt

run-join-mv : ∀ {R Γ A} (c : Ctx R Γ A) j g (x : A ∈ Γ) q e ib p → Mv (run c (joinS j g x ((q , e) ∷ ib)) joinM p)
run-join-mv c j g x q (nx a) ib p = tt
run-join-mv c j g x q cp     ib p = tt

-- The driver's steps read back as the engine's.
module _ {R : Set} where
  open Driver R using (took; value; complete; drained) renaming (silent to τ)

  τ-moved : (x : Stepped R) → Mv x → ∀ {t k′} → took x ≡ τ t k′ → Σ Torn λ tr → x ≡ moved k′ [] tr
  τ-moved (moved k [] tr) _ refl = tr , refl
  τ-moved (moved k ((_ , nx _) ∷ _) tr) _ ()
  τ-moved (moved k ((_ , cp) ∷ _) tr)   _ ()
  τ-moved quiet _ ()

  val-moved : (x : Stepped R) → Mv x → ∀ {t p a k′} → took x ≡ value t p a k′ → Σ (Shownᴹ R) λ rest → Σ Torn λ tr → x ≡ moved k′ ((p , nx a) ∷ rest) tr
  val-moved (moved k [] tr) _ ()
  val-moved (moved k ((_ , nx _) ∷ rest) tr) _ refl = rest , tr , refl
  val-moved (moved k ((_ , cp) ∷ _) tr)      _ ()
  val-moved quiet _ ()

  fin-moved : (x : Stepped R) → Mv x → ∀ {p} → took x ≡ complete p → Σ (Conf R) λ k′ → Σ (Shownᴹ R) λ rest → Σ Torn λ tr → x ≡ moved k′ ((p , cp) ∷ rest) tr
  fin-moved (moved k [] tr) _ ()
  fin-moved (moved k ((_ , nx _) ∷ _) tr)    _ ()
  fin-moved (moved k ((_ , cp) ∷ rest) tr)   _ refl = k , rest , tr , refl
  fin-moved quiet _ ()

  mv-drained : (x : Stepped R) → Mv x → took x ≢ drained
  mv-drained (moved k [] tr)                _ ()
  mv-drained (moved k ((_ , nx _) ∷ _) tr) _ ()
  mv-drained (moved k ((_ , cp) ∷ _) tr)   _ ()
  mv-drained quiet                          () _
  mv-drained (starting _ _ _)               () _
  mv-drained (turn _)                       () _

  quiet-τ : ∀ {x t k′} → x ≡ quiet → took x ≢ τ t k′
  quiet-τ refl ()

  quiet-val : ∀ {x t p a k′} → x ≡ quiet → took x ≢ value t p a k′
  quiet-val refl ()

  quiet-fin : ∀ {x p} → x ≡ quiet → took x ≢ complete p
  quiet-fin refl ()

-- A driver step that shows nothing: a cold's subscription or turn.
module _ {R : Set} where
  open Driver R using (Step; played; value; complete; drained) renaming (silent to τ)

  Hush : Step → Set
  Hush (τ _ _) = ⊤
  Hush _       = ⊥

  played-hush : ∀ {A} b l cl dv st → Hush (played (leaf {A = A} b l cl dv st))
  played-hush true (ending e) cl dv st              = tt
  played-hush false l cl dv st                      = tt
  played-hush true (play τ′ u i t fr) true dv st    = tt
  played-hush true over true dv st                  = tt
  played-hush true (play τ′ u i t (emit a k)) false dv st = tt
  played-hush true (play τ′ u i t (stall k)) false dv st  = tt
  played-hush true (play τ′ u i t (close k)) false dv st  = tt
  played-hush true over false dv st                 = tt

  hush-val : ∀ {x t p a k′} → Hush x → x ≡ value t p a k′ → ⊥
  hush-val h refl = h

  hush-fin : ∀ {x p} → Hush x → x ≡ complete p → ⊥
  hush-fin h refl = h

  hush-drained : ∀ {x} → Hush x → x ≢ drained
  hush-drained h refl = h

------------------------------------------------------------------------
-- What a search finds

-- The marks nodes own.
data Marked {Γ : List Set} : ∀ {A} → St Γ A → Mark → Set₁ where
  ofK   : ∀ {A} i p (xs : List A) → Marked (ofS i p xs) ofM
  attK  : ∀ {A} l p (s : St Γ A) → Marked (cutS l (attAt p) s) attM
  conK  : ∀ {X A} k (o : St Γ X) (b : St (X ∷ Γ) A) m → m ≡ bodyM ⊎ (m ≡ srcAttM ⊎ m ≡ owedM) → Marked (connS k o b) m
  joinK : ∀ {A} j g (x : A ∈ Γ) q e ib → Marked (joinS j g x ((q , e) ∷ ib)) joinM
  leafK : ∀ {A} b (l : Tape A) → Marked (coldS b l) leafM
  stopK : ∀ {A} i (q : A → Bool) r (s : St Γ A) → Marked (takeS i q (cpAt r) s) cpM
  cutK  : ∀ {A} i (q : A → Bool) r (s : St Γ A) → Marked (takeS i q (cutAt r) s) cutM

-- Where a mark run delivers, if it does.
data Delivers {Γ A} : St Γ A → Mark → Pos → Set₁ where
  d-of   : ∀ {i q x xs} → Delivers (ofS i q (x ∷ xs)) ofM (q ⊕ [ ix i ])
  d-ofx  : ∀ {i q} → Delivers (ofS i q []) ofM (q ⊕ [ last ])
  d-join : ∀ {j x q e ib} → Delivers (joinS j true x ((q , e) ∷ ib)) joinM q
  d-stop : ∀ {i keep r s} → Delivers (takeS i keep (cpAt r) s) cpM (r ⊕ [ last ])

-- A candidate's mark is one its node owns, its focus a hole of the tree
-- searched.
data Owned {R A} (t : St [] R) : Maybe (Cand R A) → Set₁ where
  o-none : Owned t nothing
  o-just : ∀ {Γ B c s m κ h o} → Marked {Γ} {B} s m → (m , κ) ∈ own s → plug c s ≡ t → h ≡ κ
         → Owned t (just (found (Γ , B , c , s) m κ , h , o))

first-owned : ∀ {R A t} {x y : Maybe (Cand R A)} → Owned t x → Owned t y → Owned t (first x y)
first-owned o-none                    oy                            = oy
first-owned (o-just mk mi pe hk)      o-none                        = o-just mk mi pe hk
first-owned (o-just {h = h} mk mi pe hk) (o-just {h = h′} mk′ mi′ pe′ hk′) with h′ <ᴷ h
... | true  = o-just mk′ mi′ pe′ hk′
... | false = o-just mk mi pe hk

retag-owned : ∀ {R A B t} {g : Key → Out A → Key × Out B} {x : Maybe (Cand R A)} → Keeps g → Owned t x → Owned t (retag g x)
retag-owned kp o-none                                = o-none
retag-owned kp (o-just {h = h} {o = o} mk mi pe hk) = o-just mk mi pe (trans (kp h o) hk)

race-owned : ∀ {R A B t} d n (q : List A) {x : Maybe (Cand R A)} {y : Maybe (Cand R B)} → Owned t x → Owned t y → Owned t (raceT d n q x y)
race-owned d n q o-none o-none = o-none
race-owned d n q o-none (o-just {h = k} {o = o′} mk mi pe hk) = o-just mk mi pe (trans (laneKp d n q k o′) hk)
race-owned d n q (o-just {h = h} {o = o} mk mi pe hk) o-none = o-just mk mi pe (trans (outerKp n q h o) hk)
race-owned d n q (o-just {h = h} {o = o} mk mi pe hk) (o-just {h = k} {o = o′} mk′ mi′ pe′ hk′) with h <ᴷ k
... | true  = o-just mk mi pe (trans (outerKp n q h o) hk)
... | false = o-just mk′ mi′ pe′ (trans (laneKp d n q k o′) hk′)

source-owned : ∀ {R A B t} {x : Maybe (Cand R A)} {y : Maybe (Cand R B)} → Owned t x → Owned t y → Owned t (sourceT x y)
source-owned o-none                         oy                              = oy
source-owned (o-just mk mi pe hk)           o-none                          = o-just mk mi pe hk
source-owned (o-just {h = h} mk mi pe hk)   (o-just {h = k} mk′ mi′ pe′ hk′) with h <ᴷ k
... | true  = o-just mk mi pe hk
... | false = o-just mk′ mi′ pe′ hk′

own-marked : ∀ {Γ A} (s : St Γ A) → All (λ mk → Marked s (proj₁ mk)) (own s)
own-marked (coldS b l) with due l
... | just _  = leafK b l ∷ᴬ []ᴬ
... | nothing = []ᴬ
own-marked (ofS i p [])                  = ofK i p [] ∷ᴬ []ᴬ
own-marked (ofS i p (x ∷ xs))            = ofK i p (x ∷ xs) ∷ᴬ []ᴬ
own-marked (cutS l (attAt p) s)          = attK l p s ∷ᴬ []ᴬ
own-marked (cutS l attached s)           = []ᴬ
own-marked (takeS i q (cpAt p) s)        = stopK i q p s ∷ᴬ []ᴬ
own-marked (takeS i q (cutAt p) s)       = cutK i q p s ∷ᴬ []ᴬ
own-marked (takeS i q free s)            = []ᴬ
own-marked (takeS i q (overAt p) s)      = []ᴬ
own-marked (connS k o b) with CS.bodyAt k | CS.attSrc k | CS.owedAt k
... | just _  | just _  | just _  = B ∷ᴬ S ∷ᴬ O ∷ᴬ []ᴬ
  where B = conK k o b bodyM (inj₁ refl); S = conK k o b srcAttM (inj₂ (inj₁ refl)); O = conK k o b owedM (inj₂ (inj₂ refl))
... | just _  | just _  | nothing = conK k o b bodyM (inj₁ refl) ∷ᴬ conK k o b srcAttM (inj₂ (inj₁ refl)) ∷ᴬ []ᴬ
... | just _  | nothing | just _  = conK k o b bodyM (inj₁ refl) ∷ᴬ conK k o b owedM (inj₂ (inj₂ refl)) ∷ᴬ []ᴬ
... | just _  | nothing | nothing = conK k o b bodyM (inj₁ refl) ∷ᴬ []ᴬ
... | nothing | just _  | just _  = conK k o b srcAttM (inj₂ (inj₁ refl)) ∷ᴬ conK k o b owedM (inj₂ (inj₂ refl)) ∷ᴬ []ᴬ
... | nothing | just _  | nothing = conK k o b srcAttM (inj₂ (inj₁ refl)) ∷ᴬ []ᴬ
... | nothing | nothing | just _  = conK k o b owedM (inj₂ (inj₂ refl)) ∷ᴬ []ᴬ
... | nothing | nothing | nothing = []ᴬ
own-marked (joinS j g x ((q , e) ∷ ib)) = joinK j g x q e ib ∷ᴬ []ᴬ
own-marked (joinS j g x [])              = []ᴬ
own-marked (pend _ _)                    = []ᴬ
own-marked doneS                         = []ᴬ
own-marked (mapS _ _)                    = []ᴬ
own-marked (scanS _ _ _)                 = []ᴬ
own-marked (lnS _ _)                     = []ᴬ
own-marked (flatS _ _ _ _ _ _ _)         = []ᴬ

ownBest-owned : ∀ {R Γ A} (c : Ctx R Γ A) s ms → All (λ mk → Marked s (proj₁ mk)) ms → (∀ {mk} → mk ∈ ms → mk ∈ own s)
              → Owned (plug c s) (ownBest c s ms)
ownBest-owned c s []       []ᴬ         sub = o-none
ownBest-owned c s (_ ∷ ms) (mk ∷ᴬ mks) sub = first-owned (o-just mk (sub (here refl)) refl refl) (ownBest-owned c s ms mks (λ m → sub (there m)))

mutual
  seek-owned : ∀ {R Γ A} (c : Ctx R Γ A) s → Owned (plug c s) (seek c s)
  seek-owned c s = first-owned (ownBest-owned c s (own s) (own-marked s) (λ m → m)) (kids-owned c s)

  kids-owned : ∀ {R Γ A} (c : Ctx R Γ A) s → Owned (plug c s) (kids c s)
  kids-owned c (mapS f s)              = retag-owned (mapKp f) (seek-owned (inMap f c) s)
  kids-owned c (scanS f z s)           = retag-owned (scanKp f z) (seek-owned (inScan f z c) s)
  kids-owned c (cutS l a s)            = retag-owned (cutKp l) (seek-owned (inCut l a c) s)
  kids-owned c (lnS b s)               = seek-owned (inLn b c) s
  kids-owned c (takeS i q w s)         = retag-owned (takeKp i q w) (seek-owned (inTake i q w c) s)
  kids-owned c (flatS op f d n q o ls) = race-owned d n q (seek-owned (inOuter op f d n q ls c) o) (lanes-owned c op f d n q o [] ls)
  kids-owned c (connS k o b)           = source-owned (seek-owned (inSrc k b c) o) (seek-owned (inBody k o c) b)
  kids-owned c (pend _ _)              = o-none
  kids-owned c (coldS _ _)             = o-none
  kids-owned c (ofS _ _ _)             = o-none
  kids-owned c doneS                   = o-none
  kids-owned c (joinS _ _ _ _)         = o-none

  lanes-owned : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q o pre ls
              → Owned (plug c (flatS op f d n q o (pre ʳ++ ls))) (lanes c op f d n q o pre ls)
  lanes-owned c op f d n q o pre []         = o-none
  lanes-owned c op f d n q o pre (s ∷ post) =
    first-owned (retag-owned (cutKp (alive s)) (seek-owned (inLanes op f d n q o pre post c) s)) (lanes-owned c op f d n q o (s ∷ pre) post)

found-of : ∀ {R B t} {x : Maybe (Cand R B)} {Γ A c′ s′ m κ}
         → Owned t x → mapᴹ proj₁ x ≡ just (found (Γ , A , c′ , s′) m κ) → Marked s′ m × plug c′ s′ ≡ t
found-of o-none               ()
found-of (o-just mk _ pe _) refl = mk , pe

-- The found mark's own key, and no mark of the tree keyed before it.
found-least : ∀ {R} {t : St [] R} {Γ A c′ s′ m κ}
            → search top t ≡ just (found (Γ , A , c′ , s′) m κ) → (m , κ) ∈ own s′ × Lo t κ
found-least {t = t} fd with seek top t in sk | seek-owned top t
found-least refl | just _ | o-just _ mi _ refl = mi , seek-lo top _ sk

-- WHAT A SEARCH FINDS: a node's own mark, as `own` keys it, at a hole of
-- the tree searched.
found-mark : ∀ {R Γ′ A′} (c : Ctx R Γ′ A′) s {Γ A c′ s′ m κ}
           → search top (plug c s) ≡ just (found (Γ , A , c′ , s′) m κ) → Marked s′ m
found-mark c s fd = proj₁ (found-of (seek-owned top (plug c s)) fd)

found-plug : ∀ {R Γ′ A′} (c : Ctx R Γ′ A′) s {Γ A c′ s′ m κ}
           → search top (plug c s) ≡ just (found (Γ , A , c′ , s′) m κ) → plug c′ s′ ≡ plug c s
found-plug c s fd = proj₂ (found-of (seek-owned top (plug c s)) fd)

-- A delivering mark's key is where it delivers.
delivers-key : ∀ {Γ A} {s : St Γ A} {m p κ} → Delivers s m p → (m , κ) ∈ own s → κ ≡ at p
delivers-key d-of   (here refl) = refl
delivers-key d-of   (there ())
delivers-key d-ofx  (here refl) = refl
delivers-key d-ofx  (there ())
delivers-key d-join (here refl) = refl
delivers-key d-join (there ())
delivers-key d-stop (here refl) = refl
delivers-key d-stop (there ())

-- What a node in step delivers, it owes.
delivers-owed : ∀ {Γ} {sc : Scope Γ} {Rg C A} {s : St Γ A} {E m p} → Sync sc Rg C s E → Delivers s m p → Owes C p
delivers-owed (s-of d)                   d-of   = proj₂ (proj₂ (from d (at-out , tt , tt)))
delivers-owed (s-of d)                   d-ofx  = proj₂ (proj₂ (from d (at-end , tt , tt)))
delivers-owed (s-join _ d _ _ _)         d-join = proj₂ (proj₂ (from d (inj₁ this)))
delivers-owed (s-took _ _ _ (o-cp ow) _ _) d-stop = ow

-- No list entry, switch or pending program delivers.
ln-none : ∀ {Γ A} {b} {l : St Γ A} {m p} → Delivers (lnS b l) m p → ⊥
ln-none ()
cut-none : ∀ {Γ A} {b a} {l : St Γ A} {m p} → Delivers (cutS b a l) m p → ⊥
cut-none ()
pend-none : ∀ {Γ A} {o : Obs Timeline Γ A} {q m p} → Delivers (pend o q) m p → ⊥
pend-none ()

-- THE LEAST MARK OVER THE WHOLE TREE: one delivering at an owed `p` leads
-- everything owed, so the cursor moves to just before `p` and the tree
-- stays in step.
least-shift : ∀ {R} {t : St [] R} {Rg C E Γ A} {c′ : Ctx R Γ A} {s′ m κ p}
            → Sync unbound Rg C t E → search top t ≡ just (found (Γ , A , c′ , s′) m κ) → Delivers s′ m p → Owes C p
            → Sync unbound Rg (bef p) t E × Due C E ≃ Due (bef p) E
least-shift {t = t} sy fd dl op with found-least {t = t} fd
... | mi , lo with delivers-key dl mi
... | refl = shift sy op (λ ()) lo , due-shift sy op (λ ()) lo

-- NO MARK, NOTHING OWED.
none-spent : ∀ {R} {t : St [] R} {Rg C E} → Sync unbound Rg C t E → search top t ≡ nothing → Spent C E
none-spent {t = t} sy fd {q} r with seek top t in sk
none-spent {t = t} sy fd {q} r | nothing =
  bound {p = q ⊕ [ ix 0 ]} sy (λ ()) (λ ki → ⊥-elim (seek-none top t sk ki)) r (≺-ext q [])
none-spent sy () r | just _

------------------------------------------------------------------------
-- The steps over a root's entry

module Over {R : Set} (Rt : EmissionSet R) where

  postulate
    --------------------------------------------------------------------
    -- SUBSCRIPTIONS keep the cursor: what the pending program owed is
    -- what the subscribed nodes owe.
    sub-of     : ∀ {C Γ A} {c : Ctx R Γ A} {xs : List A} {q p}
               → Inv Rt C ⟨ c , pend (of xs) q , subscribing , p ⟩ → Inv Rt C ⟨ c , ofS 0 q xs , absorbed , q ⟩
    sub-empty  : ∀ {C Γ A} {c : Ctx R Γ A} {q p}
               → Inv Rt C ⟨ c , pend empty q , subscribing , p ⟩ → Inv Rt C ⟨ c , ofS 0 q [] , absorbed , q ⟩
    sub-map    : ∀ {C Γ A B} {c : Ctx R Γ B} {f : A → B} {s q p}
               → Inv Rt C ⟨ c , pend (map f s) q , subscribing , p ⟩ → Inv Rt C ⟨ inMap f c , pend s q , subscribing , q ⟩
    sub-scan   : ∀ {C Γ A B} {c : Ctx R Γ B} {f : B → A → B} {z s q p}
               → Inv Rt C ⟨ c , pend (scan f z s) q , subscribing , p ⟩ → Inv Rt C ⟨ inScan f z c , pend s q , subscribing , q ⟩
    sub-take   : ∀ {C Γ A} {c : Ctx R Γ A} {i} {w : A → Bool} {s q p}
               → Inv Rt C ⟨ c , pend (takeWhile i w s) q , subscribing , p ⟩
               → Inv Rt C ⟨ inCut true (attAt q) (inTake i w free c) , pend s q , subscribing , q ⟩
    sub-flat   : ∀ {C Γ A B} {c : Ctx R Γ B} {op} {f : A → Obs Timeline Γ B} {s q p}
               → Inv Rt C ⟨ c , pend (flatMap op f s) q , subscribing , p ⟩
               → Inv Rt C ⟨ inCut true (attAt q) (inOuter op f false 0 [] [] c) , pend s q , subscribing , q ⟩
    sub-conn   : ∀ {C Γ A B} {c : Ctx R Γ B} {s : Obs Timeline Γ A} {b q p}
               → Inv Rt C ⟨ c , pend (connect s b) q , subscribing , p ⟩
               → Inv Rt C ⟨ inBody (cs false true false (just q) nothing nothing q root s (scopeOf c)) (pend s (q ⊕ [ ix 1 ])) c
                          , pend b (q ⊕ [ ix 0 ]) , subscribing , q ⊕ [ ix 0 ] ⟩
    sub-cold   : ∀ {C Γ A} {c : Ctx R Γ A} {x : Timeline A} {q p}
               → Inv Rt C ⟨ c , pend (cold x) q , subscribing , p ⟩ → Inv Rt C ⟨ c , coldS true (opening q (timelineAt x q)) , absorbed , q ⟩
    sub-defer  : ∀ {C Γ A} {c : Ctx R Γ A} {l q p}
               → Inv Rt C ⟨ c , pend (defer l) q , subscribing , p ⟩
               → Inv Rt C ⟨ c , pend (Later.force l) (q ⊕ [ ix 1 ]) , subscribing , q ⊕ [ ix 1 ] ⟩
    -- a joiner of a completed subject: its end owed, under `last`
    sub-joined : ∀ {C Γ A} {c : Ctx R Γ A} {x : A ∈ Γ} {q p} → closedUp c x ≡ true
               → Inv Rt C ⟨ c , pend (connected x) q , subscribing , p ⟩ → Inv Rt C ⟨ c , ofS 0 q [] , absorbed , q ⟩
    -- a joiner of a live subject: joined where it subscribed
    sub-join   : ∀ {C Γ A} {c : Ctx R Γ A} {x : A ∈ Γ} {q p} → closedUp c x ≡ false
               → Inv Rt C ⟨ c , pend (connected x) q , subscribing , p ⟩ → Inv Rt C ⟨ c , joinS q true x [] , absorbed , q ⟩

    --------------------------------------------------------------------
    -- RISES that read their frame's bookkeeping.
    -- A TAKEWHILE'S FIRST FAILURE, INCLUSIVE: the row leaves under `ix 0`,
    -- and what is above moves past `p`, which needs no row but this one
    -- at `p`.
    rise-take-failᵢ : ∀ {Γ A} {w : A → Bool} {c : Ctx R Γ A} {s a p} → w a ≡ false
                    → SimC Rt ⟨ inTake true w free c , s , rising (nx a) , p ⟩ [] ⟨ c , takeS true w (cpAt p) s , rising (nx a) , p ⊕ [ ix 0 ] ⟩
    rise-outer-nx : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {d n q ls} {c : Ctx R Γ B} {o a p k′ sh t}
                  → rise (inOuter op f d n q ls c) o (nx a) p ≡ moved k′ sh t → SimC Rt ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩ sh k′
    rise-outer-cp : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {d n q ls} {c : Ctx R Γ B} {o p k′ sh t}
                  → rise (inOuter op f d n q ls c) o cp p ≡ moved k′ sh t → SimC Rt ⟨ inOuter op f d n q ls c , o , rising cp , p ⟩ sh k′
    rise-lane-nx  : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {d n q o pre post} {c : Ctx R Γ B} {s b p k′ sh t}
                  → rise (inLanes op f d n q o pre post c) s (nx b) p ≡ moved k′ sh t
                  → SimC Rt ⟨ inLanes op f d n q o pre post c , s , rising (nx b) , p ⟩ sh k′
    rise-lane-cp  : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {d n q o pre post} {c : Ctx R Γ B} {s p k′ sh t}
                  → rise (inLanes op f d n q o pre post c) s cp p ≡ moved k′ sh t
                  → SimC Rt ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩ sh k′
    -- A feed appends at `p ⊕ [ sub j ]` and the inbox stays ascending:
    -- `Adm` makes the source a lawful hot, its rows none below another.
    -- What the step still owes is moving all but the source from `bef p`
    -- to `aft p`: nothing but the source has a row at `p`.
    -- RECOVERY: git show 1745f869 restores rejoin-mono, good-full and lawful-at.
    rise-src-nx   : ∀ {Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {s a p k′ sh t}
                  → rise (inSrc k b c) s (nx a) p ≡ moved k′ sh t → SimC Rt ⟨ inSrc k b c , s , rising (nx a) , p ⟩ sh k′
    rise-src-cp   : ∀ {Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {s p k′ sh t}
                  → rise (inSrc k b c) s cp p ≡ moved k′ sh t → SimC Rt ⟨ inSrc k b c , s , rising cp , p ⟩ sh k′

    --------------------------------------------------------------------
    -- MARK RUNS, the cursor just before what they deliver.
    run-of-nx     : ∀ {Γ A} {c : Ctx R Γ A} {i q x xs r} → closed c ≡ false
                  → Inv Rt (bef (q ⊕ [ ix i ])) ⟨ c , ofS i q (x ∷ xs) , absorbed , r ⟩
                  → Inv Rt (bef (q ⊕ [ ix i ])) ⟨ c , ofS (suc i) q xs , rising (nx x) , q ⊕ [ ix i ] ⟩
    run-of-end    : ∀ {Γ A} {c : Ctx R Γ A} {i q r} → closed c ≡ false
                  → Inv Rt (bef (q ⊕ [ last ])) ⟨ c , ofS i q [] , absorbed , r ⟩
                  → Inv Rt (bef (q ⊕ [ last ])) ⟨ c , doneS , rising cp , q ⊕ [ last ] ⟩
    run-join-nx   : ∀ {Γ A} {c : Ctx R Γ A} {j} {x : A ∈ Γ} {q a ib r} → closed c ≡ false
                  → Inv Rt (bef q) ⟨ c , joinS j true x ((q , nx a) ∷ ib) , absorbed , r ⟩
                  → Inv Rt (bef q) ⟨ c , joinS j true x ib , rising (nx a) , q ⟩
    run-join-cp   : ∀ {Γ A} {c : Ctx R Γ A} {j} {x : A ∈ Γ} {q ib r} → closed c ≡ false
                  → Inv Rt (bef q) ⟨ c , joinS j true x ((q , cp) ∷ ib) , absorbed , r ⟩
                  → Inv Rt (bef q) ⟨ c , joinS j false x ib , rising cp , q ⟩
    -- a connect's own marks: its source subscribed, attached or torn
    -- down
    run-con       : ∀ {C Γ A X} {c : Ctx R Γ A} {k} {o : St Γ X} {b m r k′ sh t}
                  → m ≡ bodyM ⊎ (m ≡ srcAttM ⊎ m ≡ owedM) → run c (connS k o b) m r ≡ moved k′ sh t
                  → Inv Rt C ⟨ c , connS k o b , absorbed , r ⟩ → sh ≡ [] × Inv Rt C k′
    -- A COLD'S TURN: its tape played one step, a value or its end rising,
    -- a stall or a frame's close moving nothing owed.
    abs-leaf      : ∀ {Γ′ A′ Γ A} {c : Ctx R Γ′ A′} {s} {c′ : Ctx R Γ A} {b} {l : Tape A} {κ t k′ p}
                  → search top (plug c s) ≡ just (found (Γ , A , c′ , coldS b l) leafM κ)
                  → Driver.took R (run c′ (coldS b l) leafM p) ≡ Driver.silent t k′
                  → SimC Rt ⟨ c , s , absorbed , p ⟩ [] k′

  ----------------------------------------------------------------------
  -- THE SEARCH: the tree zipped up, the cursor moved over the whole tree,
  -- and unzipped down to the mark found.

  owed-≃ : ∀ {C C′ E} → E ≈ Rt → Due C E ≃ Due C′ E → Vis (RT Rt C) ≃ Vis (RT Rt C′)
  owed-≃ {C} {C′} e d = (λ (x , v) → to (due-≈ {C = C′} e) (to d (from (due-≈ {C = C} e) x)) , v)
                      ⇄ (λ (x , v) → to (due-≈ {C = C} e) (from d (from (due-≈ {C = C′} e) x)) , v)

  search-none : ∀ {C Γ A} {c : Ctx R Γ A} {s p}
              → Inv Rt C ⟨ c , s , absorbed , p ⟩ → search top (plug c s) ≡ nothing → Spent C Rt
  search-none {C} (settled _ fr h) fd with climb Rt fr h
  ... | _ , _ , e , sy = λ d → none-spent sy fd (from (due-≈ {C = C} e) d)

  search-least : ∀ {C Γ A} {c : Ctx R Γ A} {s r Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ p}
               → Inv Rt C ⟨ c , s , absorbed , r ⟩
               → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , s′) m κ)
               → Delivers s′ m p
               → (Inv Rt (bef p) ⟨ c′ , s′ , absorbed , r ⟩ × Vis (RT Rt C) ≃ Vis (RT Rt (bef p)))
                 ⊎ (Σ Rgn λ Rg → Σ (EmissionSet A′) (Fr Rt C Rg c′ (owes false)))
  search-least {C} {c = c} {s = s} {c′ = c′} {s′ = s′} {p = p} (settled _ fr h) fd dl with climb Rt fr h
  ... | _ , _ , e , sy with descend Rt c′ s′ (subst (λ t → Sync unbound _ _ t _) (sym (found-plug c s fd)) sy) e
  ...   | owes false , _ , _ , fr′ , _ = inj₂ (_ , _ , fr′)
  ...   | lane _ , _ , _ , _ , (_ , _ , refl , _) = ⊥-elim (ln-none dl)
  ...   | lanecut _ , _ , _ , _ , (_ , _ , refl , _) = ⊥-elim (cut-none dl)
  ...   | pnd _ , _ , _ , _ , (_ , refl , _) = ⊥-elim (pend-none dl)
  ...   | owes true , _ , _ , _ , h′ with least-shift sy fd dl (delivers-owed (h′ tt) dl)
  ...     | sy′ , d with descend Rt c′ s′ (subst (λ t → Sync unbound _ _ t _) (sym (found-plug c s fd)) sy′) e
  ...       | _ , _ , _ , fr′ , h″ = inj₁ (settled c-abs fr′ h″ , owed-≃ {C = C} {C′ = bef p} e d)

  -- In a subtree no live node reads, any mode keeps the cursor.
  adrift-any : ∀ {C Γ A} {c : Ctx R Γ A} {Rg E} m {s p} → Fr Rt C Rg c (owes false) E → Inv Rt C ⟨ c , s , m , p ⟩
  adrift-any subscribing fr = settled c-sub fr (λ ())
  adrift-any absorbed    fr = settled c-abs fr (λ ())
  adrift-any (rising _)  fr = adrift fr

  -- A search's outcome, run: the node's run at the shifted cursor, or
  -- adrift.
  stepped : ∀ {C Γ A} {c′ : Ctx R Γ A} {s′ r p s″ m″ p″}
          → (Inv Rt (bef p) ⟨ c′ , s′ , absorbed , r ⟩ × Vis (RT Rt C) ≃ Vis (RT Rt (bef p))) ⊎ (Σ Rgn λ Rg → Σ (EmissionSet A) (Fr Rt C Rg c′ (owes false)))
          → (Inv Rt (bef p) ⟨ c′ , s′ , absorbed , r ⟩ → Inv Rt (bef p) ⟨ c′ , s″ , m″ , p″ ⟩)
          → Σ Cur λ C′ → Inv Rt C′ ⟨ c′ , s″ , m″ , p″ ⟩ × Moves (RT Rt C) [] (RT Rt C′)
  stepped (inj₁ (i , r)) g = _ , g i , silent r
  stepped (inj₂ (_ , _ , fr)) g = _ , adrift-any _ fr , silent ≃-refl

  -- A torn joiner's row dropped: nothing owed before, nothing after.
  joinx-hold : ∀ {Γ A} {sc : Scope Γ} {Rg C w j} {x : A ∈ Γ} {u ib E}
             → Hold sc Rg C w (joinS j false x (u ∷ ib)) E → Hold sc Rg C w (joinS j false x ib) E
  joinx-hold {w = owes _} h t with h t
  ... | s-joinx sp = s-joinx sp
  joinx-hold {w = lane _}    (_ , _ , () , _)
  joinx-hold {w = lanecut _} (_ , _ , () , _)
  joinx-hold {w = pnd _}     (_ , () , _)

  join-off : ∀ {C Γ A} {c : Ctx R Γ A} {j} {x : A ∈ Γ} {u ib r p}
           → Inv Rt C ⟨ c , joinS j false x (u ∷ ib) , absorbed , r ⟩ → Inv Rt C ⟨ c , joinS j false x ib , absorbed , p ⟩
  join-off (settled _ fr h) = settled c-abs fr (joinx-hold h)

  -- Under a closed context nothing is owed: only a connect's ended
  -- source or a switched-off lane closes one, and both owe nothing below.
  Off : Need → Set
  Off (owes b)    = b ≡ false
  Off (lane _)    = ⊥
  Off (lanecut _) = ⊥
  Off (pnd _)     = ⊤

  or-right : ∀ a {b} → T (not a) → T (a ∨ b) → T b
  or-right false _ t = t

  closed-off : ∀ {C Γ A} {c : Ctx R Γ A} {Rg w E} → Fr Rt C Rg c w E → T (closed c) → Off w
  closed-off (f-top _)                         ()
  closed-off (f-off _ _)                       _ = refl
  closed-off (f-map fr _ _)                    t = closed-off fr t
  closed-off (f-scan fr _ _ _)                 t = closed-off fr t
  closed-off (f-cut fr)                        t = closed-off fr t
  closed-off (f-take fr _ _ _)                 t = closed-off fr t
  closed-off (f-took _ _ _ _ _ _ _)            _ = refl
  closed-off (f-outer fr _ _ _)                t = closed-off fr t
  closed-off (f-lanes fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) t with closed-off fr t
  ... | ()
  closed-off (f-lane fr)                       t = closed-off fr t
  closed-off (f-lnct {b = false} fr)           _ = refl
  closed-off (f-lnct {b = true} fr)            t = ⊥-elim (closed-off fr t)
  closed-off (f-src {k = k} fr _ _ _ nc _ _ _ _) t = closed-off fr (or-right (CS.closed k) nc t)
  closed-off (f-srcc _ _ _ _ _ _ _ _ _)        _ = refl
  closed-off (f-srcp _ _ _ _ _ _ _ _ _ _)      _ = tt
  closed-off (f-srcx _ _ _ _ _ _)              _ = refl
  closed-off (f-body fr _ _ refl _ _ _)        t with closed-off fr t
  ... | refl = refl

  off-keep : ∀ {C Γ A} {c : Ctx R Γ A} {Rg w E} {s s′ : St Γ A} {p} → (∀ {o q} → s ≢ pend o q)
           → Fr Rt C Rg c w E → Hold (scopeOf c) Rg C w s E → Off w → Inv Rt C ⟨ c , s′ , absorbed , p ⟩
  off-keep {w = owes _}    _  fr _ refl        = settled c-abs fr (λ ())
  off-keep {w = lane _}    _  _  _ ()
  off-keep {w = lanecut _} _  _  _ ()
  off-keep {w = pnd _}     np _  (_ , e , _) _ = ⊥-elim (np e)

  -- A run under a closed context delivers nothing and owes nothing.
  closed-keep : ∀ {C Γ A} {c : Ctx R Γ A} {s s′ : St Γ A} {r p} → closed c ≡ true → (∀ {o q} → s ≢ pend o q)
              → Inv Rt C ⟨ c , s , absorbed , r ⟩ → Inv Rt C ⟨ c , s′ , absorbed , p ⟩
  closed-keep cl np (settled _ fr h) = off-keep np fr h (closed-off fr (subst T (sym cl) tt))

  -- A mark delivering nothing keeps the cursor: the focus moved to it.
  search-quiet : ∀ {C Γ A} {c : Ctx R Γ A} {s r Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ}
               → Inv Rt C ⟨ c , s , absorbed , r ⟩
               → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , s′) m κ)
               → Inv Rt C ⟨ c′ , s′ , absorbed , r ⟩
  search-quiet {c = c} {s = s} i fd = refocus Rt i (found-plug c s fd)

  ----------------------------------------------------------------------
  -- Mark runs, assembled: the search, then the node's run.

  module _ {Γ′ A′} {c : Ctx R Γ′ A′} {s : St Γ′ A′} {p : Pos} where

    abs-of : ∀ {Γ A} {c′ : Ctx R Γ A} {i q} {xs : List A} {κ k′ sh t}
           → search top (plug c s) ≡ just (found (Γ , A , c′ , ofS i q xs) ofM κ) → run c′ (ofS i q xs) ofM p ≡ moved k′ sh t
           → SimC Rt ⟨ c , s , absorbed , p ⟩ sh k′
    abs-of {c′ = c′} {xs = xs} fd eq with closed c′ in cl | xs | eq
    ... | true  | []     | refl = keeps Rt λ i → closed-keep cl (λ ()) (search-quiet i fd)
    ... | true  | _ ∷ _  | refl = keeps Rt λ i → closed-keep cl (λ ()) (search-quiet i fd)
    ... | false | []     | refl = λ i → stepped (search-least i fd d-ofx) (run-of-end cl)
    ... | false | _ ∷ _  | refl = λ i → stepped (search-least i fd d-of) (run-of-nx cl)

    abs-att : ∀ {Γ A} {c′ : Ctx R Γ A} {l q s₀ κ k′ sh t}
            → search top (plug c s) ≡ just (found (Γ , A , c′ , cutS l (attAt q) s₀) attM κ) → run c′ (cutS l (attAt q) s₀) attM p ≡ moved k′ sh t
            → SimC Rt ⟨ c , s , absorbed , p ⟩ sh k′
    abs-att {l = true}  {s₀ = s₀} fd refl = keeps Rt λ i → run-att Rt (λ _ → refl) (search-quiet i fd)
    abs-att {l = false} {s₀ = s₀} fd eq with unsub s₀ | eq
    ... | s′ , _ | refl = keeps Rt λ i → run-att Rt (λ ()) (search-quiet i fd)

    abs-con : ∀ {Γ A X} {c′ : Ctx R Γ A} {k} {o : St Γ X} {b m κ k′ sh t} → m ≡ bodyM ⊎ (m ≡ srcAttM ⊎ m ≡ owedM)
            → search top (plug c s) ≡ just (found (Γ , A , c′ , connS k o b) m κ) → run c′ (connS k o b) m p ≡ moved k′ sh t
            → SimC Rt ⟨ c , s , absorbed , p ⟩ sh k′
    abs-con w fd eq {C} i with run-con w eq (search-quiet i fd)
    ... | refl , i′ = C , i′ , silent ≃-refl

    abs-join : ∀ {Γ A} {c′ : Ctx R Γ A} {j g} {x : A ∈ Γ} {q e ib κ k′ sh t}
             → search top (plug c s) ≡ just (found (Γ , A , c′ , joinS j g x ((q , e) ∷ ib)) joinM κ)
             → run c′ (joinS j g x ((q , e) ∷ ib)) joinM p ≡ moved k′ sh t
             → SimC Rt ⟨ c , s , absorbed , p ⟩ sh k′
    abs-join {c′ = c′} {g = true} {e = nx a} fd eq with closed c′ in cl | eq
    ... | false | refl = λ i → stepped (search-least i fd d-join) (run-join-nx cl)
    ... | true  | refl = keeps Rt λ i → closed-keep cl (λ ()) (search-quiet i fd)
    abs-join {c′ = c′} {g = true} {e = cp}   fd eq with closed c′ in cl | eq
    ... | false | refl = λ i → stepped (search-least i fd d-join) (run-join-cp cl)
    ... | true  | refl = keeps Rt λ i → closed-keep cl (λ ()) (search-quiet i fd)
    abs-join {g = false} {e = nx a} fd refl   = keeps Rt λ i → join-off (search-quiet i fd)
    abs-join {g = false} {e = cp}   fd refl   = keeps Rt λ i → join-off (search-quiet i fd)

    abs-stop : ∀ {Γ A} {c′ : Ctx R Γ A} {j} {w : A → Bool} {r s₀ κ k′ sh t}
             → search top (plug c s) ≡ just (found (Γ , A , c′ , takeS j w (cpAt r) s₀) cpM κ)
             → run c′ (takeS j w (cpAt r) s₀) cpM p ≡ moved k′ sh t
             → SimC Rt ⟨ c , s , absorbed , p ⟩ sh k′
    abs-stop {c′ = c′} fd eq with closed c′ in cl | eq
    ... | false | refl = λ i → stepped (search-least i fd d-stop) (run-stop Rt)
    ... | true  | refl = keeps Rt λ i → closed-keep cl (λ ()) (search-quiet i fd)

    abs-cut : ∀ {Γ A} {c′ : Ctx R Γ A} {j} {w : A → Bool} {r s₀ κ k′ sh t}
            → search top (plug c s) ≡ just (found (Γ , A , c′ , takeS j w (cutAt r) s₀) cutM κ)
            → run c′ (takeS j w (cutAt r) s₀) cutM p ≡ moved k′ sh t
            → SimC Rt ⟨ c , s , absorbed , p ⟩ sh k′
    abs-cut {s₀ = s₀} fd eq with cut s₀ | eq
    ... | s′ , _ | refl = keeps Rt λ i → run-cut Rt (search-quiet i fd)

  ----------------------------------------------------------------------
  -- Where a step goes: on, linked a step at a time, engine or driver.

  data Reach (k : Conf R) : Set₁ where
    within : Mv (stepᴹ k) → (∀ {k′ sh t} → stepᴹ k ≡ moved k′ sh t → SimC Rt k sh k′) → Reach k
    driven : Hush (Driver.step R k) → (∀ {t k′} → Driver.step R k ≡ Driver.silent t k′ → SimC Rt k [] k′) → Reach k
    stills : stepᴹ k ≡ quiet → (∀ {C} → Inv Rt C k → Spent C Rt) → Reach k

  -- A step linked, read off the step itself, so a search's outcome can be
  -- abstracted in it.
  data Link (k : Conf R) : Stepped R → Set₁ where
    mvL    : ∀ {x} → Mv x → (∀ {k′ sh t} → x ≡ moved k′ sh t → SimC Rt k sh k′) → Link k x
    hushL  : ∀ {x} → Hush (Driver.took R x) → (∀ {t k′} → Driver.took R x ≡ Driver.silent t k′ → SimC Rt k [] k′) → Link k x
    stillL : (∀ {C} → Inv Rt C k → Spent C Rt) → Link k quiet

  linked : ∀ {k : Conf R} → Link k (stepᴹ k) → Reach k
  linked {k = k} = go refl
    where
      go : ∀ {x} → stepᴹ k ≡ x → Link k x → Reach k
      go eq   (stillL v)    = stills eq v
      go refl (mvL mv sim)  = within mv sim
      go refl (hushL h sim) = driven h sim

  -- A mark run, by what the search found.
  abs-link : ∀ {Γ A} (c : Ctx R Γ A) s p → Link ⟨ c , s , absorbed , p ⟩ (stepᴹ ⟨ c , s , absorbed , p ⟩)
  abs-link c s p with search top (plug c s) in fd
  ... | nothing = stillL λ i → search-none i fd
  ... | just (found (_ , _ , c′ , s′) m κ) with found-mark c s fd
  ...   | ofK j q xs        = mvL (run-of-mv c′ j q xs p) (abs-of fd)
  ...   | attK l q s₀       = mvL (run-att-mv c′ l q s₀ p) (abs-att fd)
  ...   | conK k o b m w    = mvL (run-con-mv c′ k o b m p w) (abs-con w fd)
  ...   | joinK j g x q e ib = mvL (run-join-mv c′ j g x q e ib p) (abs-join fd)
  ...   | stopK j q r s₀    = mvL tt (abs-stop fd)
  ...   | cutK j q r s₀     = mvL (run-cut-mv c′ j q r s₀ p) (abs-cut fd)
  ...   | leafK b l         = hushL (played-hush b l (closed c′) (λ e l′ b′ p′ → ⟨ c′ , coldS b′ l′ , (if not (closed c′) then rising e else absorbed) , p′ ⟩)
                                                     (λ l′ → ⟨ c′ , coldS b l′ , absorbed , p ⟩))
                                    (abs-leaf fd)

  -- The record update holds `srcLive` too, so the test is generalised alone.
  body-cp : ∀ {Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} {s p k′ sh t} b → CS.srcLive k ≡ b
          → moved (if b then ⟨ c , connS (record k { owedAt = just p }) o s , rising cp , p ⟩ else ⟨ c , connS k o s , absorbed , p ⟩) [] [] ≡ moved k′ sh t
          → SimC Rt ⟨ inBody k o c , s , rising cp , p ⟩ sh k′
  body-cp true  lv refl = rise-body-cp Rt lv
  body-cp false lv refl = rise-bodyx Rt lv

  -- A rise, by its frame.
  rise-sim : ∀ {Γ A} {k′ : Conf R} {sh t} (c : Ctx R Γ A) (s : St Γ A) e p → rise c s e p ≡ moved k′ sh t → SimC Rt ⟨ c , s , rising e , p ⟩ sh k′
  rise-sim top                       s e      p refl = rise-top Rt
  rise-sim (inMap f c)               s e      p refl = rise-map Rt
  rise-sim (inScan f z c)            s (nx a) p refl = rise-scan-nx Rt
  rise-sim (inScan f z c)            s cp     p refl = rise-scan-cp Rt
  rise-sim (inCut true a c)          s e      p refl = rise-cut Rt
  rise-sim (inCut false a c)         s e      p refl = rise-cutx Rt
  rise-sim (inLn b c)                s e      p refl = rise-ln Rt
  rise-sim (inTake i w free c)       s (nx a) p eq with w a in wa | i | eq
  ... | true  | _     | refl = rise-take-pass Rt wa
  ... | false | true  | refl = rise-take-failᵢ wa
  ... | false | false | refl = rise-take-fail Rt wa
  rise-sim (inTake i w free c)       s cp     p refl = rise-take-cp Rt
  rise-sim (inTake i w (cpAt r) c)   s e      p refl = rise-took Rt (λ ())
  rise-sim (inTake i w (cutAt r) c)  s e      p refl = rise-took Rt (λ ())
  rise-sim (inTake i w (overAt r) c) s e      p refl = rise-took Rt (λ ())
  rise-sim (inOuter op f d n q ls c) o (nx a) p eq   = rise-outer-nx eq
  rise-sim (inOuter op f d n q ls c) o cp     p eq   = rise-outer-cp eq
  rise-sim (inLanes op f d n q o pre post c) s (nx b) p eq = rise-lane-nx eq
  rise-sim (inLanes op f d n q o pre post c) s cp     p eq = rise-lane-cp eq
  rise-sim (inSrc k b c)             s (nx a) p eq   = rise-src-nx eq
  rise-sim (inSrc k b c)             s cp     p eq   = rise-src-cp eq
  rise-sim (inBody k o c)            s (nx b) p eq with CS.srcLive k in lv | eq
  ... | true  | refl = rise-body-nx Rt lv
  ... | false | refl = rise-bodyx Rt lv
  rise-sim (inBody k o c)            s cp     p eq   = body-cp (CS.srcLive k) refl eq

  -- A joiner subscribed, by its subject's end.
  join-mv : ∀ {Γ A} (c : Ctx R Γ A) (x : A ∈ Γ) q {p} → Mv (stepᴹ ⟨ c , pend (connected x) q , subscribing , p ⟩)
  join-mv c x q with closedUp c x
  ... | true  = tt
  ... | false = tt

  join-sim : ∀ {Γ A} {k′ : Conf R} {sh t} (c : Ctx R Γ A) (x : A ∈ Γ) q p
           → stepᴹ ⟨ c , pend (connected x) q , subscribing , p ⟩ ≡ moved k′ sh t → SimC Rt ⟨ c , pend (connected x) q , subscribing , p ⟩ sh k′
  join-sim c x q p eq with closedUp c x in cu | eq
  ... | true  | refl = keeps Rt (sub-joined cu)
  ... | false | refl = keeps Rt (sub-join cu)

  reach-pend : ∀ {Γ A} (c : Ctx R Γ A) (o : Obs Timeline Γ A) q p → Reach ⟨ c , pend o q , subscribing , p ⟩
  reach-pend c empty             q p = within tt λ { refl → keeps Rt sub-empty }
  reach-pend c (of xs)           q p = within tt λ { refl → keeps Rt sub-of }
  reach-pend c (map f s)         q p = within tt λ { refl → keeps Rt sub-map }
  reach-pend c (flatMap op f s)  q p = within tt λ { refl → keeps Rt sub-flat }
  reach-pend c (connected x)     q p = within (join-mv c x q {p}) (join-sim c x q p)
  reach-pend c (cold x)          q p = driven tt λ { refl → keeps Rt sub-cold }
  reach-pend c (scan f z s)      q p = within tt λ { refl → keeps Rt sub-scan }
  reach-pend c (takeWhile b w s) q p = within tt λ { refl → keeps Rt sub-take }
  reach-pend c (connect s b)     q p = within tt λ { refl → keeps Rt sub-conn }
  reach-pend c (defer l)         q p = within tt λ { refl → keeps Rt sub-defer }

  -- Subscribing to a node already running: nothing to do.
  reach : (k : Conf R) → Reach k
  reach ⟨ c , s , rising e , p ⟩                        = within (rise-mv c s e p) (rise-sim c s e p)
  reach ⟨ c , pend o q , subscribing , p ⟩              = reach-pend c o q p
  reach ⟨ c , coldS b l , subscribing , p ⟩             = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , ofS j q xs , subscribing , p ⟩            = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , doneS , subscribing , p ⟩                 = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , mapS f s , subscribing , p ⟩              = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , scanS f z s , subscribing , p ⟩           = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , cutS l a s , subscribing , p ⟩            = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , lnS b s , subscribing , p ⟩               = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , takeS j q w s , subscribing , p ⟩         = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , flatS op f d n q o ls , subscribing , p ⟩ = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , connS k o b , subscribing , p ⟩           = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , joinS j g x ib , subscribing , p ⟩        = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , s , absorbed , p ⟩                        = linked (abs-link c s p)

------------------------------------------------------------------------
-- THE CURSOR SIMULATES EVERY RUN: the carrier a cursor and the invariant
-- at it, read as what the root owes past it.

cursor : ∀ {R} (o : PureObs [] R) → Simulation o
cursor {R} o = record
  { I   = λ k → Σ Cur λ C → Inv Rt C k
  ; T   = λ i → RT Rt (proj₁ i)
  ; i₀  = origin , pending {Rg = λ _ → ⊤} (f-top ≃-refl) (λ _ → tt , (tt , λ ()) , tt , ≃-refl , λ _ → tt)
  ; t₀  = (λ { ((x , v , _) , v′) → x , v′ }) ⇄ (λ { (x , v) → (x , v , tt) , v })
  ; tau = tau
  ; val = val
  ; fin = fin
  ; dry = dry
  }
  where
    Rt : EmissionSet R
    Rt = enter (⟦ o ⟧ []ᴬ) root
    open Over Rt

    tau : ∀ {k k′ t} (i : Σ Cur λ C → Inv Rt C k) → Driver.step R k ≡ Driver.silent t k′
        → Σ (Σ Cur λ C → Inv Rt C k′) λ i′ → Vis (RT Rt (proj₁ i)) ≃ Vis (RT Rt (proj₁ i′))
    tau {k} (C , i) e = go (reach k)
      where
        go : Reach k → _
        go (driven h sim) with sim e i
        ... | C′ , i′ , silent q = (C′ , i′) , q
        go (within mv sim) with τ-moved (stepᴹ k) mv e
        ... | _ , eq with sim eq i
        ...   | C′ , i′ , silent q = (C′ , i′) , q
        go (stills eq _) = ⊥-elim (quiet-τ eq e)

    val : ∀ {k k′ t p a} (i : Σ Cur λ C → Inv Rt C k) → Driver.step R k ≡ Driver.value t p a k′
        → Σ (Σ Cur λ C → Inv Rt C k′) λ i′ → Lowest (RT Rt (proj₁ i)) p (out a) × Vis (Past p (RT Rt (proj₁ i))) ≃ Vis (RT Rt (proj₁ i′))
    val {k} {k′} {t} {p} {a} (C , i) e = go (reach k)
      where
        go : Reach k → Σ (Σ Cur λ C → Inv Rt C k′) λ i′ → Lowest (RT Rt C) p (out a) × Vis (Past p (RT Rt C)) ≃ Vis (RT Rt (proj₁ i′))
        go (driven h _) = ⊥-elim (hush-val h e)
        go (stills eq _) = ⊥-elim (quiet-val eq e)
        go (within mv sim) with val-moved (stepᴹ k) mv e
        ... | rest , tr , eq with sim eq i
        ...   | C′ , i′ , shown v l q = (C′ , i′) , (v , l) , q

    fin : ∀ {k p} (i : Σ Cur λ C → Inv Rt C k) → Driver.step R k ≡ Driver.complete p → Lowest (RT Rt (proj₁ i)) p end
    fin {k} {p} (C , i) e = go (reach k)
      where
        go : Reach k → Lowest (RT Rt C) p end
        go (driven h _) = ⊥-elim (hush-fin h e)
        go (stills eq _) = ⊥-elim (quiet-fin eq e)
        go (within mv sim) with fin-moved (stepᴹ k) mv e
        ... | k′ , rest , tr , eq with sim eq i
        ...   | C′ , i′ , shown v l q = v , l

    dry : ∀ {k} (i : Σ Cur λ C → Inv Rt C k) → Driver.step R k ≡ Driver.drained → ∀ {q e} → Vis (RT Rt (proj₁ i)) q e → ⊥
    dry {k} (C , i) e = go (reach k)
      where
        go : Reach k → ∀ {q e′} → Vis (RT Rt C) q e′ → ⊥
        go (driven h _)   = ⊥-elim (hush-drained h e)
        go (within mv _)  = ⊥-elim (mv-drained (stepᴹ k) mv e)
        go (stills _ sp) v = sp i (proj₁ v)
