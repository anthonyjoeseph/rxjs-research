{-# OPTIONS --guardedness #-}

-- THE RUN, STEP BY STEP, OVER THE CURSOR: every step of the engine is
-- one of the cursor invariant's moves, dispatched by mode and frame; a
-- mark run is a search, moving the focus to the mark and the cursor to
-- just before what it delivers, then the node's own run.  Together they
-- are a `Simulation` of every program's run.
module adequacy.Dispatch where

open import Data.Bool using (Bool; true; false; if_then_else_; not; _∨_; _∧_; T)
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
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Timeline; root; Pos; ix; last; timelineAt; emit; stall; close)
open import denotation.EmissionSet using (EmissionSet; ⟦_⟧; at-out; at-end)
open import denotation.Laws.Modulus using (≺-ext; ≺→≼; entered-reach)
open import denotation.Laws.Worlds using (Ok; Hots; ok-step)
open import operation.Key using (Key; _<ᴷ_; at)
open import operation.PureObservable using (PureObs; due; module Machine; module Driver; Tape; play; ending; over; opening)
open Machine using (St; Ctx; Conf; Scope; binds; scopeOf; ⟨_,_,_,_⟩; subscribing; absorbed; rising; load; moved; plug; search; found; Mark; ofM; attM;
                    rise; run; alive; nx; cp; attAt; attached; Torn; Stepped; quiet; admit; closed; killAll; unsubIf; unsub; free; cpAt; cutAt; overAt;
                    cut; cpM; cutM; CS; cs; closedUp; _⊕_; unbound; seek; kids; lanes; own; ownBest; first; retag; raceT; sourceT; Cand; Out; bodyM; srcAttM; owedM; joinM; leafM; leaf; starting; turn;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
                    renaming (Shown to Shownᴹ; step to stepᴹ)
open import adequacy.Rows using (pendRows; full; ≃-refl; Vis; _≃_; _⇄_; silent; Moves; this)
open _≃_
open import adequacy.Cursor using (Cur; ≈-refl; Rgn; JoinE; Parts; Flags; src-pend; JInv; Joined; JRl; JRo; polF; Sound; Within; Adm; bef; Spent; Sync; _≈_; c-abs; c-sub; Owes; Fr; Hold; Need; owes; dead; lane; lanecut; pnd; Pts; ∅ᵖ; _⊑_; ∅-⊑; ⊑-refl; ⊑-trans; Rest; h-blank; h-take; hl-none; sh-dead; un-dead; Clear; Pending; pend-shape; notT; sync-pend; s-of; s-join; s-joinx; s-took; f-top; f-map; f-scan; f-cut; f-take; f-took; f-outer; f-lanes; f-lane; f-lnct; f-src; f-srcc; f-srcp; f-body; d-map; d-scan; d-cut; d-ln; d-take; d-outer; d-lanes; d-src; d-body; f-isle; f-islec; o-cp)
open import adequacy.Cursor.Rise using (Inv; settled; pending; adrift; RT; SimC; keeps; rise-top; rise-map; rise-scan-nx; rise-scan-cp; rise-take-pass; rise-take-cp; rise-cut; rise-cutx; rise-ln; rise-took; rise-take-fail; rise-bodyx; run-stop; run-cut; run-att)
open import adequacy.Path using (Path)
open import adequacy.Walk using (due-≈; climb; descend; refocus; nowhere; none′)
open import adequacy.Least using (Lo; Keeps; mapKp; scanKp; cutKp; takeKp; outerKp; laneKp; seek-lo; seek-none)
open import adequacy.Bound using (bound; owes-≼; behind-past; behind-pend; join-past)
open import adequacy.Few using (fr-shift)
open import adequacy.Up using (rise-body-nx; rise-body-cp; rise-src-nx; rise-src-cp)

------------------------------------------------------------------------
-- Within what is grown, every step moves or finds nothing to do

Mv : ∀ {R} → Stepped R → Set
Mv (moved _ _ _) = ⊤
Mv _             = ⊥

admit-mv : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) ω d n q o ls a p → Mv (admit c op f ω d n q o ls a p)
admit-mv c (Tree.mergeᶠ nothing)  f ω d n q o ls a p = tt
admit-mv c (Tree.mergeᶠ (just m)) f ω d n q o ls a p = tt
admit-mv c Tree.switchᶠ           f ω d n q o ls a p with killAll ls
... | _ = tt
admit-mv c Tree.exhaustᶠ          f ω d n q o ls a p with n ≡ᵇ 0
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
rise-mv (inOuter op f ω d n q ls c) o (nx a) p = admit-mv c op f ω d n q o ls a p
rise-mv (inOuter op f ω d n q ls c) o cp     p = tt
rise-mv (inLanes op f ω d n q o pre post c) s (nx b) p = tt
rise-mv (inLanes op f ω d n q o pre post c) s cp     p = tt
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
run-con-mv c k o b .srcAttM p (inj₂ (inj₁ refl)) with CS.attSrc k | unsubIf (not (CS.srcLive k) ∨ closed c) o
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
own-marked (flatS _ _ _ _ _ _ _ _)         = []ᴬ

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
  kids-owned c (flatS op f ω d n q o ls) = race-owned d n q (seek-owned (inOuter op f ω d n q ls c) o) (lanes-owned c op f ω d n q o [] ls)
  kids-owned c (connS k o b)           = source-owned (seek-owned (inSrc k b c) o) (seek-owned (inBody k o c) b)
  kids-owned c (pend _ _)              = o-none
  kids-owned c (coldS _ _)             = o-none
  kids-owned c (ofS _ _ _)             = o-none
  kids-owned c doneS                   = o-none
  kids-owned c (joinS _ _ _ _)         = o-none

  lanes-owned : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) ω d n q o pre ls
              → Owned (plug c (flatS op f ω d n q o (pre ʳ++ ls))) (lanes c op f ω d n q o pre ls)
  lanes-owned c op f ω d n q o pre []         = o-none
  lanes-owned c op f ω d n q o pre (s ∷ post) =
    first-owned (retag-owned (cutKp (alive s)) (seek-owned (inLanes op f ω d n q o pre post c) s)) (lanes-owned c op f ω d n q o (s ∷ pre) post)

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
delivers-owed (s-of d _)                 d-of   = proj₂ (proj₂ (from d (at-out , tt , tt)))
delivers-owed (s-of d _)                 d-ofx  = proj₂ (proj₂ (from d (at-end , tt , tt)))
delivers-owed (s-join _ d _ _ _)         d-join = proj₂ (proj₂ (from d (inj₁ this)))
delivers-owed (s-took _ _ _ (o-cp ow) _ _ _ _) d-stop = ow

-- No list entry, switch or pending program delivers.
ln-none : ∀ {Γ A} {b} {l : St Γ A} {m p} → Delivers (lnS b l) m p → ⊥
ln-none ()
cut-none : ∀ {Γ A} {b a} {l : St Γ A} {m p} → Delivers (cutS b a l) m p → ⊥
cut-none ()
pend-none : ∀ {Γ A} {o : Obs Timeline Γ A} {q m p} → Delivers (pend o q) m p → ⊥
pend-none ()

-- The found mark's key, and none keyed before it, at its own focus.
found-lo : ∀ {R Γ′ A′} (c : Ctx R Γ′ A′) s {Γ A c′ s′ m κ}
         → search top (plug c s) ≡ just (found (Γ , A , c′ , s′) m κ) → (m , κ) ∈ own s′ × Lo (plug c′ s′) κ
found-lo c s {κ = κ} fd with found-least {t = plug c s} fd
... | mi , lo = mi , subst (λ t → Lo t κ) (sym (found-plug c s fd)) lo

-- A delivering mark found: nothing keyed before where it delivers.
lo-at : ∀ {R Γ′ A′} (c : Ctx R Γ′ A′) s {Γ A c′ s′ m κ p}
      → search top (plug c s) ≡ just (found (Γ , A , c′ , s′) m κ) → Delivers s′ m p → Lo (plug c′ s′) (at p)
lo-at c s {c′ = c′} {s′ = s′} fd dl with found-lo c s fd
... | mi , lo = subst (Lo (plug c′ s′)) (delivers-key dl mi) lo

-- No pending subscription owns a mark.
marked-pend : ∀ {Γ A} {s : St Γ A} {m} → Pending s → Marked s m → ⊥
marked-pend {s = s} p mk with pend-shape s p
... | _ , _ , refl with mk
...   | ()

vis-≃ : ∀ {A} {E E′ : EmissionSet A} → E ≃ E′ → Vis E ≃ Vis E′
vis-≃ d = (λ (x , v) → to d x , v) ⇄ (λ (x , v) → from d x , v)

or-right : ∀ a {b} → T (not a) → T (a ∨ b) → T b
or-right false _ t = t

and-right : ∀ a {b} → T (a ∧ b) → T b
and-right true t = t

and-left : ∀ a {b} → T (a ∧ b) → T a
and-left true _ = tt

-- What a part no live node reads still runs, kept by a mark's run.
rest-of : ∀ {Γ} {sc : Scope Γ} {A} {i q} {xs : List A} {s″ : St Γ A} {P} → Rest sc (ofS i q xs) P → Rest sc s″ P
rest-of (_ , h-blank , le) = _ , h-blank , le

rest-join : ∀ {Γ} {sc : Scope Γ} {A} {j g} {x : A ∈ Γ} {ib} {s″ : St Γ A} {P} → Rest sc (joinS j g x ib) P → Rest sc s″ P
rest-join (_ , h-blank , le) = _ , h-blank , le

rest-take : ∀ {Γ} {sc : Scope Γ} {A} {i} {keep : A → Bool} {w w′ s₀ P} → Rest sc (takeS i keep w s₀) P → Rest sc (takeS i keep w′ s₀) P
rest-take (_ , h-blank , le)   = _ , h-blank , le
rest-take (_ , h-take hk , le) = _ , h-take hk , le

-- NO MARK, NOTHING OWED.
none-spent : ∀ {R} {t : St [] R} {Rg C E} → Sync unbound Rg C t E → search top t ≡ nothing → Spent C E
none-spent {t = t} sy fd {q} r with seek top t in sk
none-spent {t = t} sy fd {q} r | nothing =
  bound {p = q ⊕ [ ix 0 ]} sy (λ ()) (λ ki → ⊥-elim (seek-none top t sk ki)) r (≺-ext q [])
none-spent sy () r | just _

------------------------------------------------------------------------
-- A connect as entered at `q`: its source live, not yet subscribed.

conn₀ : ∀ {Γ X} → Obs Timeline Γ X → Pos → Scope Γ → CS Γ X
conn₀ s q sc = cs false true false (just q) nothing nothing q root s sc

------------------------------------------------------------------------
-- The steps over a root's entry

module Over {R : Set} (Rt : EmissionSet R) where

  postulate
    --------------------------------------------------------------------
    -- SUBSCRIPTIONS keep the cursors: what the pending program owed is
    -- what the subscribed nodes owe.
    sub-of     : ∀ {Cr C Γ A} {c : Ctx R Γ A} {xs : List A} {q p}
               → Inv Rt Cr C ⟨ c , pend (of xs) q , subscribing , p ⟩ → Inv Rt Cr C ⟨ c , ofS 0 q xs , absorbed , q ⟩
    sub-empty  : ∀ {Cr C Γ A} {c : Ctx R Γ A} {q p}
               → Inv Rt Cr C ⟨ c , pend empty q , subscribing , p ⟩ → Inv Rt Cr C ⟨ c , ofS 0 q [] , absorbed , q ⟩
    sub-map    : ∀ {Cr C Γ A B} {c : Ctx R Γ B} {f : A → B} {s q p}
               → Inv Rt Cr C ⟨ c , pend (map f s) q , subscribing , p ⟩ → Inv Rt Cr C ⟨ inMap f c , pend s q , subscribing , q ⟩
    sub-scan   : ∀ {Cr C Γ A B} {c : Ctx R Γ B} {f : B → A → B} {z s q p}
               → Inv Rt Cr C ⟨ c , pend (scan f z s) q , subscribing , p ⟩ → Inv Rt Cr C ⟨ inScan f z c , pend s q , subscribing , q ⟩
    sub-take   : ∀ {Cr C Γ A} {c : Ctx R Γ A} {i} {w : A → Bool} {s q p}
               → Inv Rt Cr C ⟨ c , pend (takeWhile i w s) q , subscribing , p ⟩
               → Inv Rt Cr C ⟨ inCut true (attAt q) (inTake i w free c) , pend s q , subscribing , q ⟩
    -- A JOINER ENTERED: its outer's entry where it subscribed, every
    -- lane's program admissible, nothing begun or queued, its outer's
    -- rows in its region and clear of every lane's.
    flat-jinv   : ∀ {Γ A B} {sc : Scope Γ} {f : A → Obs Timeline Γ B} {s q}
                → Ok (Hots (full sc)) q → Adm sc → JInv sc f (pendRows (full sc) s q)
    flat-joined : ∀ {C Γ A B} {sc : Scope Γ} {Rg} {op} {f : A → Obs Timeline Γ B} {s q}
                → Owes C q → Ok (Hots (full sc)) q → Adm sc
                → Joined sc (JRl sc Rg op f (pendRows (full sc) s q)) C (polF op (λ a → ⟦ f a ⟧ (full sc)) (pendRows (full sc) s q))
                         (pendRows (full sc) s q) false 0 [] []
    flat-sound  : ∀ {Γ A B} {sc : Scope Γ} {Rg} {op} {f : A → Obs Timeline Γ B} {s q}
                → Ok (Hots (full sc)) q → Adm sc → Within Rg sc q → Sound (JRo sc Rg op f (pendRows (full sc) s q)) (pendRows (full sc) s q)
    flat-within : ∀ {Γ A B} {sc : Scope Γ} {Rg} {op} {f : A → Obs Timeline Γ B} {s q}
                → Ok (Hots (full sc)) q → Within Rg sc q → Within (JRo sc Rg op f (pendRows (full sc) s q)) sc q
    -- A CONNECT ENTERED: its body and source in regions apart and clear
    -- of the scope's hots, its flags fresh, its body admissible.
    conn-parts : ∀ {Γ X B} {sc : Scope Γ} {Rg} {s : Obs Timeline Γ X} {b : Obs Timeline (X ∷ Γ) B} {q}
               → Ok (Hots (full sc)) q → Adm sc → Within Rg sc q
               → Σ (Parts sc Rg (conn₀ s q sc) (pendRows (full (binds s q sc)) b (q ⊕ [ ix 0 ]))) λ pt
                 → Within (Parts.Rb pt) (binds s q sc) (q ⊕ [ ix 0 ]) × Within (Parts.Rs pt) sc (q ⊕ [ ix 1 ])
    conn-flags : ∀ {C Γ X B} {sc : Scope Γ} {s : Obs Timeline Γ X} {b : Obs Timeline (X ∷ Γ) B} {q}
               → Owes C q → Flags C (conn₀ s q sc) (pendRows (full (binds s q sc)) b (q ⊕ [ ix 0 ]))
    conn-ok    : ∀ {Γ X} {sc : Scope Γ} {s : Obs Timeline Γ X} {q}
               → Ok (Hots (full sc)) q → Adm sc → Ok (Hots (full (binds s q sc))) (q ⊕ [ ix 0 ])
    sub-cold   : ∀ {Cr C Γ A} {c : Ctx R Γ A} {x : Timeline A} {q p}
               → Inv Rt Cr C ⟨ c , pend (cold x) q , subscribing , p ⟩ → Inv Rt Cr C ⟨ c , coldS true (opening q (timelineAt x q)) , absorbed , q ⟩
    sub-defer  : ∀ {Cr C Γ A} {c : Ctx R Γ A} {l q p}
               → Inv Rt Cr C ⟨ c , pend (defer l) q , subscribing , p ⟩
               → Inv Rt Cr C ⟨ c , pend (Later.force l) (q ⊕ [ ix 1 ]) , subscribing , q ⊕ [ ix 1 ] ⟩
    -- a joiner of a completed subject: its end owed, under `last`
    sub-joined : ∀ {Cr C Γ A} {c : Ctx R Γ A} {x : A ∈ Γ} {q p} → closedUp c x ≡ true
               → Inv Rt Cr C ⟨ c , pend (connected x) q , subscribing , p ⟩ → Inv Rt Cr C ⟨ c , ofS 0 q [] , absorbed , q ⟩
    -- a joiner of a live subject: joined where it subscribed
    sub-join   : ∀ {Cr C Γ A} {c : Ctx R Γ A} {x : A ∈ Γ} {q p} → closedUp c x ≡ false
               → Inv Rt Cr C ⟨ c , pend (connected x) q , subscribing , p ⟩ → Inv Rt Cr C ⟨ c , joinS q true x [] , absorbed , q ⟩

    --------------------------------------------------------------------
    -- RISES that read their frame's bookkeeping.
    -- A TAKEWHILE'S FIRST FAILURE, INCLUSIVE: the row leaves under `ix 0`,
    -- and what is above moves past `p`, which needs no row but this one
    -- at `p`.
    rise-take-failᵢ : ∀ {Γ A} {w : A → Bool} {c : Ctx R Γ A} {s a p} → w a ≡ false
                    → SimC Rt ⟨ inTake true w free c , s , rising (nx a) , p ⟩ [] ⟨ c , takeS true w (cpAt p) s , rising (nx a) , p ⊕ [ ix 0 ] ⟩
    rise-outer-nx : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {ω} {d n q ls} {c : Ctx R Γ B} {o a p k′ sh t}
                  → rise (inOuter op f ω d n q ls c) o (nx a) p ≡ moved k′ sh t → SimC Rt ⟨ inOuter op f ω d n q ls c , o , rising (nx a) , p ⟩ sh k′
    rise-outer-cp : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {ω} {d n q ls} {c : Ctx R Γ B} {o p k′ sh t}
                  → rise (inOuter op f ω d n q ls c) o cp p ≡ moved k′ sh t → SimC Rt ⟨ inOuter op f ω d n q ls c , o , rising cp , p ⟩ sh k′
    rise-lane-nx  : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {ω} {d n q o pre post} {c : Ctx R Γ B} {s b p k′ sh t}
                  → rise (inLanes op f ω d n q o pre post c) s (nx b) p ≡ moved k′ sh t
                  → SimC Rt ⟨ inLanes op f ω d n q o pre post c , s , rising (nx b) , p ⟩ sh k′
    rise-lane-cp  : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {ω} {d n q o pre post} {c : Ctx R Γ B} {s p k′ sh t}
                  → rise (inLanes op f ω d n q o pre post c) s cp p ≡ moved k′ sh t
                  → SimC Rt ⟨ inLanes op f ω d n q o pre post c , s , rising cp , p ⟩ sh k′
    --------------------------------------------------------------------
    -- MARK RUNS, the hole's cursor just before what they deliver.
    run-of-nx     : ∀ {Cr Γ A} {c : Ctx R Γ A} {i q x xs r} → closed c ≡ false
                  → Inv Rt Cr (bef (q ⊕ [ ix i ])) ⟨ c , ofS i q (x ∷ xs) , absorbed , r ⟩
                  → Inv Rt Cr (bef (q ⊕ [ ix i ])) ⟨ c , ofS (suc i) q xs , rising (nx x) , q ⊕ [ ix i ] ⟩
    run-of-end    : ∀ {Cr Γ A} {c : Ctx R Γ A} {i q r} → closed c ≡ false
                  → Inv Rt Cr (bef (q ⊕ [ last ])) ⟨ c , ofS i q [] , absorbed , r ⟩
                  → Inv Rt Cr (bef (q ⊕ [ last ])) ⟨ c , doneS , rising cp , q ⊕ [ last ] ⟩
    run-join-nx   : ∀ {Cr Γ A} {c : Ctx R Γ A} {j} {x : A ∈ Γ} {q a ib r} → closed c ≡ false
                  → Inv Rt Cr (bef q) ⟨ c , joinS j true x ((q , nx a) ∷ ib) , absorbed , r ⟩
                  → Inv Rt Cr (bef q) ⟨ c , joinS j true x ib , rising (nx a) , q ⟩
    run-join-cp   : ∀ {Cr Γ A} {c : Ctx R Γ A} {j} {x : A ∈ Γ} {q ib r} → closed c ≡ false
                  → Inv Rt Cr (bef q) ⟨ c , joinS j true x ((q , cp) ∷ ib) , absorbed , r ⟩
                  → Inv Rt Cr (bef q) ⟨ c , joinS j false x ib , rising cp , q ⟩
    -- A CONNECT'S OWN MARKS: its source subscribed, attached or torn
    -- down, nothing shown.  Subscribing moves the cursors: the source's
    -- frame reads `Subd`, so the hole's cursor stands at the connect's
    -- `ix 1`, and only the mark's being least over the whole tree keeps
    -- what the root owes.
    run-con       : ∀ {Cr C Γ A X} {c : Ctx R Γ A} {k} {o : St Γ X} {b m κ r k′ sh t}
                  → m ≡ bodyM ⊎ (m ≡ srcAttM ⊎ m ≡ owedM) → run c (connS k o b) m r ≡ moved k′ sh t
                  → (m , κ) ∈ own (connS k o b) → Lo (plug c (connS k o b)) κ
                  → Inv Rt Cr C ⟨ c , connS k o b , absorbed , r ⟩
                  → sh ≡ [] × (Σ Cur λ Cr′ → Σ Cur λ C′ → Inv Rt Cr′ C′ k′ × Moves (RT Rt Cr) [] (RT Rt Cr′))
    -- A COLD'S TURN: its tape played one step, a value or its end rising,
    -- a stall or a frame's close moving nothing owed.
    abs-leaf      : ∀ {Γ′ A′ Γ A} {c : Ctx R Γ′ A′} {s} {c′ : Ctx R Γ A} {b} {l : Tape A} {κ t k′ p}
                  → search top (plug c s) ≡ just (found (Γ , A , c′ , coldS b l) leafM κ)
                  → Driver.took R (run c′ (coldS b l) leafM p) ≡ Driver.silent t k′
                  → SimC Rt ⟨ c , s , absorbed , p ⟩ [] k′
    -- THE PATH TO A FOUND MARK IS CLEAR: on a run's path, a body holding
    -- an isle owns a mark keyed before every mark in its connect's
    -- source, so no search reaches into such a source.
    found-clear   : ∀ {o : PureObs [] R} {rs Γ′ A′} {c : Ctx R Γ′ A′} {s r Γ A} {c′ : Ctx R Γ A} {s′ m κ}
                  → Path (load o) rs ⟨ c , s , absorbed , r ⟩
                  → search top (plug c s) ≡ just (found (Γ , A , c′ , s′) m κ) → Clear c′

  ----------------------------------------------------------------------
  -- A SUBSCRIPTION OWED, whichever way the invariant holds it: pending,
  -- or a connect's source not yet subscribed; or in a part no live node
  -- reads, owing nothing.
  PendV : ∀ {Γ A} → Cur → Cur → Ctx R Γ A → Obs Timeline Γ A → Pos → Set₁
  PendV {A = A} Cr C c o q =
      (Σ Rgn λ Rg → Σ (EmissionSet A) λ E → Fr Rt Cr C Rg c owes E
         × Owes C q × Ok (Hots (full (scopeOf c))) q × Adm (scopeOf c) × pendRows (full (scopeOf c)) o q ≈ E × Within Rg (scopeOf c) q)
    ⊎ (Σ Rgn λ Rg → Σ Pts λ P → Σ (EmissionSet A) λ E → Fr Rt Cr C Rg c (dead P) E × P ⊑ ∅ᵖ)

  -- A pending source, read as subscribing.
  srcp : ∀ {Cr C Γ A} {c : Ctx R Γ A} {o q Rg N E} → Fr Rt Cr C Rg c N E → N ≡ pnd q
       → pendRows (full (scopeOf c)) o q ≈ E → Within Rg (scopeOf c) q → PendV Cr C c o q
  srcp {C = C} (f-srcp {k = k} fr sc pt lv nc ba (ok , adm) bs fl fe eq ow sd nb) refl pe wn =
    inj₁ (_ , _ , f-src fr sc pt lv nc bs fl fe eq (behind-pend {C = C} {k = k} sc (ok , adm) ow) sd nb , ow , ok-step (CS.connAt k) ok , adm , pe , wn)
  srcp (f-top _)                                                ()   _ _
  srcp (f-map _ _ _)                                            ()   _ _
  srcp (f-scan _ _ _ _)                                         ()   _ _
  srcp (f-cut _)                                                ()   _ _
  srcp (f-take _ _ _ _)                                         ()   _ _
  srcp (f-took _ _ _ _ _ _ _ _)                                 ()   _ _
  srcp (f-outer _ _ _ _ _ _)                                    ()   _ _
  srcp (f-lanes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)      ()   _ _
  srcp (f-lane _)                                               ()   _ _
  srcp (f-lnct {b = true} _)                                    ()   _ _
  srcp (f-lnct {b = false} _)                                   ()   _ _
  srcp (f-src _ _ _ _ _ _ _ _ _ _ _ _)                          ()   _ _
  srcp (f-srcc _ _ _ _ _ _ _ _ _ _ _ _)                         ()   _ _
  srcp (f-body _ _ _ _ _ _ _)                                   ()   _ _
  srcp (d-map _)                                                ()   _ _
  srcp (d-scan _)                                               ()   _ _
  srcp (d-cut _)                                                ()   _ _
  srcp (d-ln _)                                                 ()   _ _
  srcp (d-take _)                                               ()   _ _
  srcp (d-outer _ _ _)                                          ()   _ _
  srcp (d-lanes _ _ _ _ _)                                      ()   _ _
  srcp (d-src _ _ _ _)                                          ()   _ _
  srcp (d-body _ _ _)                                           ()   _ _
  srcp (f-isle _ _ _ _ _ _ _ _ _)                               ()   _ _
  srcp (f-islec _ _ _ _ _ _ _ _ _)                              ()   _ _

  pend-view : ∀ {Cr C Γ A} {c : Ctx R Γ A} {o q p} → Inv Rt Cr C ⟨ c , pend o q , subscribing , p ⟩ → PendV Cr C c o q
  pend-view (pending fr h)                                     = inj₁ (_ , _ , fr , h)
  pend-view {o = o} {q} (settled {N = owes} c-sub fr h)       = ⊥-elim (sync-pend {s = pend o q} tt h)
  pend-view (settled {N = dead _} c-sub fr (_ , h-blank , le)) = inj₂ (_ , _ , _ , fr , le)
  pend-view (settled {N = lane _ _} c-sub fr (_ , _ , () , _))
  pend-view (settled {N = lanecut _ _} c-sub fr (_ , _ , () , _))
  pend-view {o = o} (settled {N = pnd _} c-sub fr (_ , refl , pe , wn)) = srcp {o = o} fr refl pe wn

  -- A joiner's entry, its outer's entered where it subscribed.
  flat-entry : ∀ {Γ A B} (sc : Scope Γ) op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) q {E}
             → pendRows (full sc) (flatMap op f s) q ≈ E → JoinE sc op f (s , q) (pendRows (full sc) s q) E
  flat-entry sc (mergeᶠ nothing)  f s q eq = refl , eq
  flat-entry sc (mergeᶠ (just m)) f s q eq = refl , eq
  flat-entry sc switchᶠ           f s q eq = refl , eq
  flat-entry sc exhaustᶠ          f s q eq = refl , eq

  sub-conn : ∀ {Cr C Γ A B} {c : Ctx R Γ B} {s : Obs Timeline Γ A} {b q p}
           → Inv Rt Cr C ⟨ c , pend (connect s b) q , subscribing , p ⟩
           → Inv Rt Cr C ⟨ inBody (conn₀ s q (scopeOf c)) (pend s (q ⊕ [ ix 1 ])) c , pend b (q ⊕ [ ix 0 ]) , subscribing , q ⊕ [ ix 0 ] ⟩
  sub-conn {C = C} {c = c} {s = s} {b = b} {q = q} i with pend-view i
  ... | inj₂ (_ , _ , _ , fr , le) =
    settled {Rg = nowhere} {N = dead ∅ᵖ} {E = none′} c-sub (d-body (un-dead fr) (sh-dead h-blank) (⊑-trans le ∅-⊑)) (∅ᵖ , h-blank , ⊑-refl)
  ... | inj₁ (Rg , _ , fr , ow , ok , ad , eq , wi) =
    let (pt , wb , ws) = conn-parts {s = s} {b = b} ok ad wi
        ow₁ = owes-≼ C {q} {q ⊕ [ ix 1 ]} ow (≺→≼ {q} {q ⊕ [ ix 1 ]} (≺-ext q []))
    in pending (f-body fr refl pt tt (src-pend tt refl (ok , ad) ≈-refl ws ow₁) (conn-flags {s = s} {b = b} ow)
                 (eq , entered-reach (⟦ b ⟧ (full (binds s q (scopeOf c)))) (q ⊕ [ ix 0 ])))
         (owes-≼ C {q} {q ⊕ [ ix 0 ]} ow (≺→≼ {q} {q ⊕ [ ix 0 ]} (≺-ext q [])) , conn-ok {s = s} ok ad , (ok , ad) , ≈-refl , wb)

  sub-flat : ∀ {Cr C Γ A B} {c : Ctx R Γ B} {op} {f : A → Obs Timeline Γ B} {s q p}
           → Inv Rt Cr C ⟨ c , pend (flatMap op f s) q , subscribing , p ⟩
           → Inv Rt Cr C ⟨ inCut true (attAt q) (inOuter op f (s , q) false 0 [] [] c) , pend s q , subscribing , q ⟩
  sub-flat {C = C} {c = c} {op = op} {f = f} {s = s} {q = q} i with pend-view i
  ... | inj₂ (_ , _ , _ , fr , le) =
    settled {Rg = nowhere} {N = dead ∅ᵖ} {E = none′} c-sub (d-cut {Rg = nowhere} {E′ = none′} (d-outer fr hl-none (⊑-trans le ∅-⊑))) (∅ᵖ , h-blank , ⊑-refl)
  ... | inj₁ (Rg , _ , fr , ow , ok , ad , eq , wi) =
    pending (f-cut (f-outer fr (flat-jinv {f = f} {s = s} ok ad) (flat-joined {op = op} {f = f} {s = s} ow ok ad)
              (flat-entry (scopeOf c) op f s q eq) (flat-sound {op = op} {f = f} {s = s} ok ad wi)
              (behind-past C ow (join-past (scopeOf c) op f s ad ok))))
            (ow , ok , ad , ≈-refl , flat-within {op = op} {f = f} {s = s} ok wi)

  ----------------------------------------------------------------------
  -- THE SEARCH: the tree zipped up at the root's cursor, and unzipped
  -- down to the mark found, along a clear path.

  search-none : ∀ {Cr C Γ A} {c : Ctx R Γ A} {s p}
              → Inv Rt Cr C ⟨ c , s , absorbed , p ⟩ → search top (plug c s) ≡ nothing → Spent Cr Rt
  search-none {Cr} (settled _ fr h) fd with climb Rt fr h
  ... | _ , _ , e , sy = λ d → none-spent sy fd (from (due-≈ {C = Cr} e) d)

  -- A search's outcome: the hole's cursor just before what the mark
  -- delivers, the root's moved over nothing it owes; or the mark in a
  -- part no live node reads.
  Next : ∀ {Γ A} → Cur → Ctx R Γ A → St Γ A → Pos → Pos → Set₁
  Next {A = A} Cr c s r p =
      (Σ Cur λ Cr′ → Inv Rt Cr′ (bef p) ⟨ c , s , absorbed , r ⟩ × Vis (RT Rt Cr) ≃ Vis (RT Rt Cr′))
    ⊎ (Σ Cur λ C → Σ Rgn λ Rg → Σ Pts λ P → Σ (EmissionSet A) λ E → Fr Rt Cr C Rg c (dead P) E × Rest (scopeOf c) s P)

  search-least : ∀ {Cr C Γ A} {c : Ctx R Γ A} {s r Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ p}
               → Inv Rt Cr C ⟨ c , s , absorbed , r ⟩ → Clear c′
               → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , s′) m κ) → Delivers s′ m p → Next Cr c′ s′ r p
  search-least {c = c} {s = s} {c′ = c′} {s′ = s′} (settled _ fr h) cl fd dl with climb Rt fr h
  ... | _ , _ , e , sy with descend Rt c′ s′ (λ x → marked-pend x (found-mark c s fd)) cl (subst (λ t → Sync unbound _ _ t _) (sym (found-plug c s fd)) sy) e
  ...   | C′ , dead P , Rg , E , fr′ , h′                    = inj₂ (C′ , Rg , P , E , fr′ , h′)
  ...   | _ , lane _ _ , _ , _ , _ , (_ , _ , refl , _)     = ⊥-elim (ln-none dl)
  ...   | _ , lanecut _ _ , _ , _ , _ , (_ , _ , refl , _)  = ⊥-elim (cut-none dl)
  ...   | _ , pnd _ , _ , _ , _ , (_ , refl , _)            = ⊥-elim (pend-none dl)
  ...   | _ , owes , _ , _ , fr′ , h′ with fr-shift Rt fr′ h′ (delivers-owed h′ dl) (lo-at c s fd dl)
  ...     | Cr′ , fr″ , h″ , d = inj₁ (Cr′ , settled c-abs fr″ h″ , vis-≃ d)

  -- A search's outcome, run: the node's run at the shifted cursor, or
  -- adrift in what it still runs.
  stepped : ∀ {Cr Γ A} {c′ : Ctx R Γ A} {s′ r p s″ e″ p″} → closed c′ ≡ false → Next Cr c′ s′ r p
          → (∀ {Cr′} → Inv Rt Cr′ (bef p) ⟨ c′ , s′ , absorbed , r ⟩ → Inv Rt Cr′ (bef p) ⟨ c′ , s″ , rising e″ , p″ ⟩)
          → (∀ {P} → Rest (scopeOf c′) s′ P → Rest (scopeOf c′) s″ P)
          → Σ Cur λ Cr′ → Σ Cur λ C′ → Inv Rt Cr′ C′ ⟨ c′ , s″ , rising e″ , p″ ⟩ × Moves (RT Rt Cr) [] (RT Rt Cr′)
  stepped      _  (inj₁ (Cr′ , i , d))              g _  = Cr′ , _ , g i , silent d
  stepped {Cr} cl (inj₂ (C′ , _ , _ , _ , fr , h)) _ tr = Cr , C′ , adrift fr cl (tr h) , silent ≃-refl

  -- A torn joiner's row dropped: nothing owed before, nothing after.
  joinx-hold : ∀ {Γ A} {sc : Scope Γ} {Rg C N j} {x : A ∈ Γ} {u ib E}
             → Hold sc Rg C N (joinS j false x (u ∷ ib)) E → Hold sc Rg C N (joinS j false x ib) E
  joinx-hold {N = owes}        (s-joinx sp fn)     = s-joinx sp fn
  joinx-hold {N = dead _}      (_ , h-blank , le)  = _ , h-blank , le
  joinx-hold {N = lane _ _}    (_ , _ , () , _)
  joinx-hold {N = lanecut _ _} (_ , _ , () , _)
  joinx-hold {N = pnd _}       (_ , () , _)

  join-off : ∀ {Cr C Γ A} {c : Ctx R Γ A} {j} {x : A ∈ Γ} {u ib r p}
           → Inv Rt Cr C ⟨ c , joinS j false x (u ∷ ib) , absorbed , r ⟩ → Inv Rt Cr C ⟨ c , joinS j false x ib , absorbed , p ⟩
  join-off (settled _ fr h) = settled c-abs fr (joinx-hold h)

  -- Under a closed context nothing is owed: only a connect's ended
  -- source or a switched-off lane closes one, and both are parts no live
  -- node reads, or a source not yet subscribed.
  Off : Need → Set
  Off owes          = ⊥
  Off (dead _)      = ⊤
  Off (lane _ _)    = ⊥
  Off (lanecut _ _) = ⊥
  Off (pnd _)       = ⊤

  closed-off : ∀ {Cr C Γ A} {c : Ctx R Γ A} {Rg N E} → Fr Rt Cr C Rg c N E → T (closed c) → Off N
  closed-off (f-top _)                                           ()
  closed-off (f-map fr _ _)                                      t = closed-off fr t
  closed-off (f-scan fr _ _ _)                                   t = closed-off fr t
  closed-off (f-cut fr)                                          t = closed-off fr t
  closed-off (f-take fr _ _ _)                                   t = closed-off fr t
  closed-off (f-took _ _ _ _ _ _ _ _)                            _ = tt
  closed-off (f-outer fr _ _ _ _ _)                              t = closed-off fr t
  closed-off (f-lanes fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) t = closed-off fr t
  closed-off (f-lane fr)                                         t = closed-off fr t
  closed-off (f-lnct {b = true} fr)                              t = closed-off fr t
  closed-off (f-lnct {b = false} fr)                             _ = tt
  closed-off (f-src {k = k} fr _ _ _ nc _ _ _ _ _ _ _)           t = closed-off fr (and-right (CS.srcAtt k) (or-right (CS.closed k) nc t))
  closed-off (f-srcc _ _ _ _ _ _ _ _ _ _ _ _)                    _ = tt
  closed-off (f-srcp _ _ _ _ _ _ _ _ _ _ _ _ _ _)                _ = tt
  closed-off (f-body fr _ _ _ _ _ _)                             t = closed-off fr t
  closed-off (d-map _)                                           _ = tt
  closed-off (d-scan _)                                          _ = tt
  closed-off (d-cut _)                                           _ = tt
  closed-off (d-ln _)                                            _ = tt
  closed-off (d-take _)                                          _ = tt
  closed-off (d-outer _ _ _)                                     _ = tt
  closed-off (d-lanes _ _ _ _ _)                                 _ = tt
  closed-off (d-src _ _ _ _)                                     _ = tt
  closed-off (d-body _ _ _)                                      _ = tt
  closed-off (f-isle {k = k} _ _ _ na nc _ _ _ _)                t = ⊥-elim (notT _ na (and-left (CS.srcAtt k) (or-right (CS.closed k) nc t)))
  closed-off (f-islec _ _ _ _ _ _ _ _ _)                         _ = tt

  off-keep : ∀ {Cr C Γ A} {c : Ctx R Γ A} {Rg N E} {s s′ : St Γ A} {p} → (Pending s → ⊥) → (∀ {P} → Rest (scopeOf c) s P → Rest (scopeOf c) s′ P)
           → Fr Rt Cr C Rg c N E → Hold (scopeOf c) Rg C N s E → Off N → Inv Rt Cr C ⟨ c , s′ , absorbed , p ⟩
  off-keep {N = owes}        _  _  _  _           ()
  off-keep {N = dead _}      _  tr fr h           _ = settled c-abs fr (tr h)
  off-keep {N = lane _ _}    _  _  _  _           ()
  off-keep {N = lanecut _ _} _  _  _  _           ()
  off-keep {N = pnd _}       np _  _  (_ , e , _) _ = ⊥-elim (np (subst Pending (sym e) tt))

  -- A run under a closed context delivers nothing and owes nothing.
  closed-keep : ∀ {Cr C Γ A} {c : Ctx R Γ A} {s s′ : St Γ A} {r p} → closed c ≡ true → (Pending s → ⊥)
              → (∀ {P} → Rest (scopeOf c) s P → Rest (scopeOf c) s′ P)
              → Inv Rt Cr C ⟨ c , s , absorbed , r ⟩ → Inv Rt Cr C ⟨ c , s′ , absorbed , p ⟩
  closed-keep cl np tr (settled _ fr h) = off-keep np tr fr h (closed-off fr (subst T (sym cl) tt))

  -- A mark delivering nothing keeps the root's cursor: the focus moved
  -- to it, along a clear path.
  search-quiet : ∀ {Cr C Γ A} {c : Ctx R Γ A} {s r Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ}
               → Inv Rt Cr C ⟨ c , s , absorbed , r ⟩ → Clear c′
               → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , s′) m κ)
               → Σ Cur λ C′ → Inv Rt Cr C′ ⟨ c′ , s′ , absorbed , r ⟩
  search-quiet {c = c} {s = s} i cl fd = refocus Rt i (found-plug c s fd) (λ x → marked-pend x (found-mark c s fd)) cl

  refocused : ∀ {k k′ Γ A} {c′ : Ctx R Γ A} {s′ r}
            → (∀ {Cr C} → Inv Rt Cr C k → Σ Cur λ C′ → Inv Rt Cr C′ ⟨ c′ , s′ , absorbed , r ⟩)
            → (∀ {Cr C} → Inv Rt Cr C ⟨ c′ , s′ , absorbed , r ⟩ → Inv Rt Cr C k′) → SimC Rt k [] k′
  refocused q g {Cr} i with q i
  ... | C′ , i′ = Cr , C′ , g i′ , silent ≃-refl

  ----------------------------------------------------------------------
  -- Mark runs, assembled: the search, then the node's run.

  module _ {Γ′ A′} {c : Ctx R Γ′ A′} {s : St Γ′ A′} {p : Pos} {o : PureObs [] R} {rs} (pth : Path (load o) rs ⟨ c , s , absorbed , p ⟩) where

    focus : ∀ {Γ A} {c′ : Ctx R Γ A} {s′ m κ} → search top (plug c s) ≡ just (found (Γ , A , c′ , s′) m κ)
          → ∀ {Cr C} → Inv Rt Cr C ⟨ c , s , absorbed , p ⟩ → Σ Cur λ C′ → Inv Rt Cr C′ ⟨ c′ , s′ , absorbed , p ⟩
    focus fd i = search-quiet i (found-clear pth fd) fd

    least : ∀ {Γ A} {c′ : Ctx R Γ A} {s′ m κ q} → search top (plug c s) ≡ just (found (Γ , A , c′ , s′) m κ) → Delivers s′ m q
          → ∀ {Cr C} → Inv Rt Cr C ⟨ c , s , absorbed , p ⟩ → Next Cr c′ s′ p q
    least fd dl i = search-least i (found-clear pth fd) fd dl

    abs-of : ∀ {Γ A} {c′ : Ctx R Γ A} {i q} {xs : List A} {κ k′ sh t}
           → search top (plug c s) ≡ just (found (Γ , A , c′ , ofS i q xs) ofM κ) → run c′ (ofS i q xs) ofM p ≡ moved k′ sh t
           → SimC Rt ⟨ c , s , absorbed , p ⟩ sh k′
    abs-of {c′ = c′} {xs = xs} fd eq with closed c′ in cl | xs | eq
    ... | true  | []     | refl = refocused (focus fd) (closed-keep cl (λ ()) rest-of)
    ... | true  | _ ∷ _  | refl = refocused (focus fd) (closed-keep cl (λ ()) rest-of)
    ... | false | []     | refl = λ i → stepped cl (least fd d-ofx i) (run-of-end cl) rest-of
    ... | false | _ ∷ _  | refl = λ i → stepped cl (least fd d-of i) (run-of-nx cl) rest-of

    abs-att : ∀ {Γ A} {c′ : Ctx R Γ A} {l q s₀ κ k′ sh t}
            → search top (plug c s) ≡ just (found (Γ , A , c′ , cutS l (attAt q) s₀) attM κ) → run c′ (cutS l (attAt q) s₀) attM p ≡ moved k′ sh t
            → SimC Rt ⟨ c , s , absorbed , p ⟩ sh k′
    abs-att {l = true}              fd refl = refocused (focus fd) (run-att Rt refl)
    abs-att {l = false} {s₀ = s₀}   fd eq with unsub s₀ in us | eq
    ... | s′ , _ | refl = refocused (focus fd) (run-att Rt (cong proj₁ (sym us)))

    abs-con : ∀ {Γ A X} {c′ : Ctx R Γ A} {k} {o : St Γ X} {b m κ k′ sh t} → m ≡ bodyM ⊎ (m ≡ srcAttM ⊎ m ≡ owedM)
            → search top (plug c s) ≡ just (found (Γ , A , c′ , connS k o b) m κ) → run c′ (connS k o b) m p ≡ moved k′ sh t
            → SimC Rt ⟨ c , s , absorbed , p ⟩ sh k′
    abs-con w fd eq i with focus fd i | found-lo c s fd
    ... | _ , i′ | mi , lo with run-con w eq mi lo i′
    ...   | refl , nx′ = nx′

    abs-join : ∀ {Γ A} {c′ : Ctx R Γ A} {j g} {x : A ∈ Γ} {q e ib κ k′ sh t}
             → search top (plug c s) ≡ just (found (Γ , A , c′ , joinS j g x ((q , e) ∷ ib)) joinM κ)
             → run c′ (joinS j g x ((q , e) ∷ ib)) joinM p ≡ moved k′ sh t
             → SimC Rt ⟨ c , s , absorbed , p ⟩ sh k′
    abs-join {c′ = c′} {g = true} {e = nx a} fd eq with closed c′ in cl | eq
    ... | false | refl = λ i → stepped cl (least fd d-join i) (run-join-nx cl) rest-join
    ... | true  | refl = refocused (focus fd) (closed-keep cl (λ ()) rest-join)
    abs-join {c′ = c′} {g = true} {e = cp}   fd eq with closed c′ in cl | eq
    ... | false | refl = λ i → stepped cl (least fd d-join i) (run-join-cp cl) rest-join
    ... | true  | refl = refocused (focus fd) (closed-keep cl (λ ()) rest-join)
    abs-join {g = false} {e = nx a} fd refl   = refocused (focus fd) join-off
    abs-join {g = false} {e = cp}   fd refl   = refocused (focus fd) join-off

    abs-stop : ∀ {Γ A} {c′ : Ctx R Γ A} {j} {w : A → Bool} {r s₀ κ k′ sh t}
             → search top (plug c s) ≡ just (found (Γ , A , c′ , takeS j w (cpAt r) s₀) cpM κ)
             → run c′ (takeS j w (cpAt r) s₀) cpM p ≡ moved k′ sh t
             → SimC Rt ⟨ c , s , absorbed , p ⟩ sh k′
    abs-stop {c′ = c′} fd eq with closed c′ in cl | eq
    ... | false | refl = λ i → stepped cl (least fd d-stop i) (run-stop Rt cl) rest-take
    ... | true  | refl = refocused (focus fd) (closed-keep cl (λ ()) rest-take)

    abs-cut : ∀ {Γ A} {c′ : Ctx R Γ A} {j} {w : A → Bool} {r s₀ κ k′ sh t}
            → search top (plug c s) ≡ just (found (Γ , A , c′ , takeS j w (cutAt r) s₀) cutM κ)
            → run c′ (takeS j w (cutAt r) s₀) cutM p ≡ moved k′ sh t
            → SimC Rt ⟨ c , s , absorbed , p ⟩ sh k′
    abs-cut {c′ = c′} {j = j} {w = w} {r = r} {s₀ = s₀} fd eq with cut s₀ in ct | eq
    ... | s′ , _ | refl = refocused (focus fd)
      (λ {Cr} {C} i → subst (λ x → Inv Rt Cr C ⟨ c′ , takeS j w (overAt r) x , absorbed , r ⟩) (cong proj₁ ct) (run-cut Rt i))

  ----------------------------------------------------------------------
  -- Where a step goes: on, linked a step at a time, engine or driver.

  data Reach (k : Conf R) : Set₁ where
    within : Mv (stepᴹ k) → (∀ {k′ sh t} → stepᴹ k ≡ moved k′ sh t → SimC Rt k sh k′) → Reach k
    driven : Hush (Driver.step R k) → (∀ {t k′} → Driver.step R k ≡ Driver.silent t k′ → SimC Rt k [] k′) → Reach k
    stills : stepᴹ k ≡ quiet → (∀ {Cr C} → Inv Rt Cr C k → Spent Cr Rt) → Reach k

  -- A step linked, read off the step itself, so a search's outcome can be
  -- abstracted in it.
  data Link (k : Conf R) : Stepped R → Set₁ where
    mvL    : ∀ {x} → Mv x → (∀ {k′ sh t} → x ≡ moved k′ sh t → SimC Rt k sh k′) → Link k x
    hushL  : ∀ {x} → Hush (Driver.took R x) → (∀ {t k′} → Driver.took R x ≡ Driver.silent t k′ → SimC Rt k [] k′) → Link k x
    stillL : (∀ {Cr C} → Inv Rt Cr C k → Spent Cr Rt) → Link k quiet

  linked : ∀ {k : Conf R} → Link k (stepᴹ k) → Reach k
  linked {k = k} = go refl
    where
      go : ∀ {x} → stepᴹ k ≡ x → Link k x → Reach k
      go eq   (stillL v)    = stills eq v
      go refl (mvL mv sim)  = within mv sim
      go refl (hushL h sim) = driven h sim

  -- A mark run, by what the search found.
  abs-link : ∀ {Γ A} (c : Ctx R Γ A) s p {o rs} → Path (load o) rs ⟨ c , s , absorbed , p ⟩ → Link ⟨ c , s , absorbed , p ⟩ (stepᴹ ⟨ c , s , absorbed , p ⟩)
  abs-link c s p pth with search top (plug c s) in fd
  ... | nothing = stillL λ i → search-none i fd
  ... | just (found (_ , _ , c′ , s′) m κ) with found-mark c s fd
  ...   | ofK j q xs         = mvL (run-of-mv c′ j q xs p) (abs-of pth fd)
  ...   | attK l q s₀        = mvL (run-att-mv c′ l q s₀ p) (abs-att pth fd)
  ...   | conK k o b m w     = mvL (run-con-mv c′ k o b m p w) (abs-con pth w fd)
  ...   | joinK j g x q e ib = mvL (run-join-mv c′ j g x q e ib p) (abs-join pth fd)
  ...   | stopK j q r s₀     = mvL tt (abs-stop pth fd)
  ...   | cutK j q r s₀      = mvL (run-cut-mv c′ j q r s₀ p) (abs-cut pth fd)
  ...   | leafK b l          = hushL (played-hush b l (closed c′) (λ e l′ b′ p′ → ⟨ c′ , coldS b′ l′ , (if not (closed c′) then rising e else absorbed) , p′ ⟩)
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
  rise-sim (inOuter op f ω d n q ls c) o (nx a) p eq   = rise-outer-nx eq
  rise-sim (inOuter op f ω d n q ls c) o cp     p eq   = rise-outer-cp eq
  rise-sim (inLanes op f ω d n q o pre post c) s (nx b) p eq = rise-lane-nx eq
  rise-sim (inLanes op f ω d n q o pre post c) s cp     p eq = rise-lane-cp eq
  rise-sim (inSrc k b c)             s (nx a) p eq   = rise-src-nx Rt eq
  rise-sim (inSrc k b c)             s cp     p eq   = rise-src-cp Rt eq
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

  -- Subscribing to a node already running: nothing to do.  A mark run
  -- reads the run's path.
  reach : ∀ {o₀ : PureObs [] R} {rs} (k : Conf R) → Path (load o₀) rs k → Reach k
  reach ⟨ c , s , rising e , p ⟩                        _   = within (rise-mv c s e p) (rise-sim c s e p)
  reach ⟨ c , pend o q , subscribing , p ⟩              _   = reach-pend c o q p
  reach ⟨ c , coldS b l , subscribing , p ⟩             _   = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , ofS j q xs , subscribing , p ⟩            _   = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , doneS , subscribing , p ⟩                 _   = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , mapS f s , subscribing , p ⟩              _   = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , scanS f z s , subscribing , p ⟩           _   = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , cutS l a s , subscribing , p ⟩            _   = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , lnS b s , subscribing , p ⟩               _   = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , takeS j q w s , subscribing , p ⟩         _   = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , flatS op f ω d n q o ls , subscribing , p ⟩ _ = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , connS k o b , subscribing , p ⟩           _   = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , joinS j g x ib , subscribing , p ⟩        _   = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , s , absorbed , p ⟩                        pth = linked (abs-link c s p pth)
