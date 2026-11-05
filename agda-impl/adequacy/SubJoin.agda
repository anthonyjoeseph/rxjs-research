{-# OPTIONS --guardedness #-}

-- A JOINER OF A LIVE SUBJECT, JOINED WHERE IT SUBSCRIBED: what its entry
-- owes is what its subject still feeds it.  Rejoining a hot shows each of
-- its rows past the subscription a label down, and those it owes are
-- exactly the rows the subject owes; the one row it does not take from a
-- row past the subscription, the end of a subject ended by then, is owed
-- because a subject the engine has not closed ends where the cursor has
-- not passed.  A rejoined row has finitely many before it: the hot's rows
-- before its own, each a label down, since none lies under another.
module adequacy.SubJoin where

open import Data.Bool using (T; true; false; not)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; [_]; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (lookup) renaming (_∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.AllPairs using () renaming ([] to []ᴾ)
import Data.List as L
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Tree using (connected)
open import denotation.Events using (Pos; ix; sub; last; _<ᵖ_; <ᵖ-split; <ᵖ-down; <ᵖ-part)
open import denotation.EmissionSet using (EmissionSet; DenEnv; Ev; out; skip; end; pin; Bare; Unpinned; Dep; Few; Reach; enter; ⟦_⟧; Den; hot;
  coldAt; Proper; Rejoin; shown; heard; ended; late; _≺_)
open import denotation.Read using (Visible)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≺→≼; ≼-trans; entered-few)
open import denotation.Laws.Worlds using (Lawful; InvAt; Ok; Hots; ok-step)
open import denotation.Laws using (inv-⟦⟧)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; Scope; binds; CS; ⟨_,_,_,_⟩; scopeOf; closedUp; pend; joinS; subscribing; absorbed;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (full; pendRows; Inbox; _≃_; _⇄_; ≃-sym; ≃-trans)
open import adequacy.Cursor using (Cur; origin; bef; Owes; Onward; Dom; Up; SubdAt; Due; Unfed; Adm; Flags; InCall; Within; _≈_;
  s-join)
open import adequacy.Cursor.Tear using (c-abs)
open import adequacy.Cursor.Show using (owes-onward; up-ward; call-owes; call-onward)
open import adequacy.Cursor.Frame using (Fr; Unread; un-dead; un-torn; Need; owes; dead; lane; lanecut; pnd;
  f-top; f-map; f-scan; f-cut; f-take; f-took; f-outer; f-lanes; f-lane; f-lnct; f-src; f-srcc; f-srcp; f-body;
  d-map; d-scan; d-cut; d-ln; d-take; d-outer; d-lanes; d-src; d-body; f-isle; f-islec; f-islep)
open import adequacy.Cursor.Rise using (Inv; settled)
open import adequacy.Walk using (due-≈)
open import adequacy.Bound using (owes?; owes-≼; good-full)

------------------------------------------------------------------------
-- A hot's ends: each still owed, or past all a cursor has reached.

EndsIn : (Pos → Set) → ∀ {A} → Den A → Set
EndsIn P (hot t)    = ∀ {c} → t c end → P c
EndsIn P (coldAt _) = ⊤

Shut : ∀ {A} → Cur → Den A → Set
Shut C = EndsIn (Owes C)

Onto : ∀ {A} → Cur → Den A → Set
Onto D = EndsIn (Onward D)

ends-imp : ∀ {P Q : Pos → Set} {A} (d : Den A) → (∀ {c} → P c → Q c) → EndsIn P d → EndsIn Q d
ends-imp (hot t)    f e r = f (e r)
ends-imp (coldAt _) _ _   = tt

-- A binder's ends are hot rows of its environment.
ends-hot : ∀ {Γ} (ρ : DenEnv Γ) {A} (x : A ∈ Γ) {P Q : Pos → Set} → (∀ {c} → Hots ρ c → P c → Q c) → EndsIn P (lookup ρ x) → EndsIn Q (lookup ρ x)
ends-hot (hot t ∷ᴬ ρ)    (here refl) f e r = f (inj₁ (_ , r)) (e r)
ends-hot (coldAt _ ∷ᴬ ρ) (here refl) _ _   = tt
ends-hot (hot _ ∷ᴬ ρ)    (there x)   f e   = ends-hot ρ x (λ h → f (inj₂ h)) e
ends-hot (coldAt _ ∷ᴬ ρ) (there x)   f e   = ends-hot ρ x f e

onto-origin : ∀ {A} (d : Den A) → Onto origin d
onto-origin (hot t)    _ ()
onto-origin (coldAt _) = tt

shut-onto : ∀ C {A} {d : Den A} → Shut C d → Onto C d
shut-onto C {d = d} = ends-imp d (λ {c} o → owes-onward C {c} o)

dom-onto : ∀ {C D A} {d : Den A} → Dom C D → Onto C d → Onto D d
dom-onto {d = d} dm = ends-imp d (λ on t → on (dm t))

up-onto : ∀ {A B Y} {D D₁} {E : EmissionSet B} {E′ : EmissionSet Y} {d : Den A} → Up D₁ E D E′ → Onto D d → Onto D₁ d
up-onto {d = d} u = ends-imp d (λ {c} → up-ward {c = c} u)

------------------------------------------------------------------------
-- A binder of an admissible scope: a lawful hot, each unpinned row with
-- finitely many before it.

record Bind {A} (t : EmissionSet A) : Set where
  field
    law : Lawful t
    few : ∀ {q e} → t q e → Unpinned e → Few t q
open Bind

dep-un : ∀ {A} {q} {e : Ev A} → Unpinned e → ∀ {k e′} → Dep q e k e′
dep-un {e = out _} _ = tt
dep-un {e = skip}  _ = tt
dep-un {e = end}   _ = tt
dep-un {e = pin _} ()

bind : ∀ {Γ A} (sc : Scope Γ) (x : A ∈ Γ) → Adm sc → Σ (EmissionSet A) λ t → lookup (full sc) x ≡ hot t × Bind t
bind (binds o p sc) (here refl) (ok , a) = _ , refl , record { law = lw ; few = fw }
  where
    s = p ++ [ ix 1 ]
    I = inv-⟦⟧ o (full sc) (good-full sc a) s (ok-step p ok)
    lw : Lawful (Proper (pendRows (full sc) o s))
    lw = record { real = λ x → InvAt.real I (proj₁ x) ; func = λ x x′ → InvAt.func I (proj₁ x) (proj₁ x′)
                ; flat = λ x x′ → InvAt.flat I (proj₁ x) (proj₁ x′) ; proper = λ c y → proj₂ y (proj₁ c) }
    fw : ∀ {q e} → Proper (pendRows (full sc) o s) q e → Unpinned e → Few (Proper (pendRows (full sc) o s)) q
    fw r u with entered-few (⟦ o ⟧ (full sc)) s (dep-un u) (proj₁ r)
    ... | ks , h = ks , λ y lt → h (proj₁ y) lt
bind (binds o p sc) (there x) (_ , a) = bind sc x a

------------------------------------------------------------------------
-- A rejoined row's past

bare-un : ∀ {A} {e : Ev A} → Bare e → Unpinned e
bare-un {e = out _} _ = tt
bare-un {e = skip}  _ = tt

-- Two rows of a lawful hot, a label down in order: in order.
lower : ∀ {A} {t : EmissionSet A} → Lawful t → ∀ {q k e e′ s} → t q e → t k e′ → (k ++ [ s ]) ≺ (q ++ [ s ]) → k ≺ q
lower {t = t} L {q} {k} {e} {e′} {s} x y lt with q <ᵖ k in qk
... | true  = ⊥-elim (≺-absurd {k ++ [ s ]} {q ++ [ s ]} lt
                (Equivalence.from T-≡ (<ᵖ-down q k s s qk (λ l ls eq → Lawful.flat L x (subst (λ z → t z e′) eq y)))))
... | false with <ᵖ-split k q qk
...   | inj₁ kq   = Equivalence.from T-≡ kq
...   | inj₂ refl = ⊥-elim (≺-irrefl {k ++ [ s ]} lt)

-- A row rejoined from the hot's row at `q`: the hot's rows before `q`.
row-reach : ∀ {A} {t : EmissionSet A} {j} → Bind t → ∀ {q e₀} → t q e₀ → Few t q → j ≺ q → ∀ {e} → Reach (Rejoin j t) (q ++ [ sub j ]) e
row-reach {t = t} {j} B {q} x (ks , h) jq {e} = L.map (_++ [ sub j ]) ks , pick
  where
    pick : ∀ {k e′} → Rejoin j t k e′ → k ≺ (q ++ [ sub j ]) → Dep (q ++ [ sub j ]) e k e′ → k ∈ L.map (_++ [ sub j ]) ks
    pick (shown y _ _)   l _ = ∈-map⁺ (_++ [ sub j ]) (h y (lower (law B) x y l))
    pick (heard y _)     l _ = ∈-map⁺ (_++ [ sub j ]) (h y (lower (law B) x y l))
    pick (ended y _)     l _ = ∈-map⁺ (_++ [ sub j ]) (h y (lower (law B) x y l))
    pick (late {c} y cj) _ _ = ⊥-elim (≼-trans {q} {c} {j} (Lawful.proper (law B) y x) cj jq)

rejoin-reach : ∀ {A} {t : EmissionSet A} {j} → Bind t → ∀ {q e} → Rejoin j t q e → Visible e → Reach (Rejoin j t) q e
rejoin-reach B (shown x b jq) _ = row-reach B x (few B x (bare-un b)) jq
rejoin-reach B (heard _ _) ()
rejoin-reach B (ended x jc) _   = row-reach B x (few B x tt) jc {end}
rejoin-reach {t = t} {j} B (late {c} x cj) _ = [] , pick
  where
    pick : ∀ {k e′} → Rejoin j t k e′ → k ≺ (j ++ [ last ]) → Dep (j ++ [ last ]) end k e′ → k ∈ []
    pick (shown {k} y _ jk) _ _ = ⊥-elim (≼-trans {k} {c} {j} (Lawful.proper (law B) x y) cj jk)
    pick (heard {k} y jk)   _ _ = ⊥-elim (≼-trans {k} {c} {j} (Lawful.proper (law B) x y) cj jk)
    pick (ended {k} y jk)   _ _ = ⊥-elim (≼-trans {k} {c} {j} (Lawful.proper (law B) x y) cj jk)
    pick (late _ _)         l _ = ⊥-elim (≺-irrefl {j ++ [ last ]} l)

------------------------------------------------------------------------
-- What a joiner subscribed at `j` owes: what its subject still feeds it.

join-due : ∀ {A} {C : Cur} {j} (d : Den A) {t} → d ≡ hot t → Bind t → Owes C j → Shut C d
         → Due C (enter d j) ≃ (λ q e → Inbox [] q e ⊎ Due C (Unfed C d j) q e)
join-due {C = C} {j} .(hot t) {t} refl B ow sh = (λ ((r , _) , v , o) → inj₂ (fed r v , v , o)) ⇄ back
  where
    fed : ∀ {q e} → Rejoin j t q e → Visible e → Rejoin j (λ k e → t k e × Owes C k) q e
    fed (shown {q} x b jq) _ = shown (x , owes-≼ C {j} {q} ow (≺→≼ {j} {q} jq)) b jq
    fed (heard _ _)        ()
    fed (ended {c} x jc)   _ = ended (x , owes-≼ C {j} {c} ow (≺→≼ {j} {c} jc)) jc
    fed (late x cj)        _ = late (x , sh x) cj

    unfed : ∀ {q e} → Rejoin j (λ k e → t k e × Owes C k) q e → Rejoin j t q e
    unfed (shown (x , _) b jq) = shown x b jq
    unfed (heard (x , _) jq)   = heard x jq
    unfed (ended (x , _) jc)   = ended x jc
    unfed (late (x , _) cj)    = late x cj

    back : ∀ {q e} → (Inbox [] q e ⊎ Due C (Unfed C (hot t) j) q e) → Due C (enter (hot t) j) q e
    back (inj₁ ())
    back (inj₂ (u , v , o)) = (unfed u , rejoin-reach B (unfed u) v) , v , o

------------------------------------------------------------------------
-- THE SUBJECTS ABOVE A HOLE: each the engine has not closed ends where
-- the hole's live cursor has not passed, and past all its dead cursor
-- has reached.  A binder whose source runs reads it off its flags; a
-- connect no live node reads, off where its body stood when it fell; an
-- isle, off its parent's cursor, which is past its first slot, a hot
-- being in no slot's world.

-- A need some live node reads.
Live : Need → Set
Live owes            = ⊤
Live (dead _ _)      = ⊥
Live (lane _ _ _)    = ⊤
Live (lanecut _ _ _) = ⊤
Live (pnd _)         = ⊤

-- The cursor a hole's need reads past: its live one, or a dead part's.
Reads : Need → Cur → Cur
Reads owes             C = C
Reads (dead D _)       _ = D
Reads (lane true _ _)  C = C
Reads (lane false D _) _ = D
Reads (lanecut true _ _)  C = C
Reads (lanecut false D _) _ = D
Reads (pnd _)          C = C

module _ {R : Set} (Rt : EmissionSet R) where

  mutual
    shut-up : ∀ {Cr C Γ A} {Rg} {c : Ctx R Γ A} {N E} → Fr Rt Cr C Rg c N E → Live N
            → ∀ {X} (x : X ∈ Γ) → closedUp c x ≡ false → Shut C (lookup (full (scopeOf c)) x)
    shut-up (f-top _) _ () _
    shut-up (f-map fr _ _) _ x cu                     = shut-up fr tt x cu
    shut-up (f-scan fr _ _ _) _ x cu                  = shut-up fr tt x cu
    shut-up (f-cut fr) _ x cu                         = shut-up fr tt x cu
    shut-up (f-take fr _ _ _) _ x cu                  = shut-up fr tt x cu
    shut-up (f-took _ _ _ _ _ _ _ _ _ _) () _ _
    shut-up (f-outer fr _ _ _ _ _) _ x cu             = shut-up fr tt x cu
    shut-up (f-lanes fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ x cu = shut-up fr tt x cu
    shut-up (f-lane fr) _ x cu                        = shut-up fr tt x cu
    shut-up (f-lnct fr) _ x cu                        = shut-up fr tt x cu
    shut-up (f-src fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ x cu = shut-up fr tt x cu
    shut-up (f-srcc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) () _ _
    shut-up (f-srcp fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ x cu = shut-up fr tt x cu
    shut-up {C = C} (f-body {k = k} _ _ _ sl _ _ fl _) _ (here refl) cu {c′} r =
      [ (λ o → o) , (λ no → ⊥-elim (subst T cu (Flags.unshut fl sl (proj₁ r) no))) ]′ (owes? C c′)
    shut-up {C = C} (f-body fr sc _ _ _ _ _ _) _ (there x) cu =
      subst (λ s → Shut C (lookup (full s) x)) (sym sc) (shut-up fr tt x cu)
    shut-up (d-map _ _) () _ _
    shut-up (d-scan _ _) () _ _
    shut-up (d-cut _ _) () _ _
    shut-up (d-ln _ _) () _ _
    shut-up (d-take _ _) () _ _
    shut-up (d-outer _ _ _ _) () _ _
    shut-up (d-lanes _ _ _ _ _ _ _) () _ _
    shut-up (d-src _ _ _ _ _ _ _ _ _ _) () _ _
    shut-up (d-body _ _ _ _ _ _) () _ _
    shut-up {C = Ci} {c = inSrc k _ c} (f-isle u _ _ _ _ _ _ sd _ _ ic _ th _ _ _) _ x cu =
      ends-hot (full (scopeOf c)) x (λ hc on → call-owes {r = CS.connAt k} Ci ic (proj₂ (SubdAt.hok sd)) hc (on th)) (unread-past u x cu)
    shut-up (f-islec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) () _ _
    shut-up {c = inSrc k _ c} (f-islep u _ _ _ _ _ _ _ _ adm _ _ th _ _ _) _ x cu =
      ends-hot (full (scopeOf c)) x (λ hc on → call-owes {r = r} (bef (r ++ [ ix 1 ])) slot (proj₂ (proj₁ adm)) hc (on th)) (unread-past u x cu)
      where
        r = CS.connAt k
        slot : InCall (bef (r ++ [ ix 1 ])) k
        slot {s} t = ≼-trans {s} {r ++ [ ix 1 ]} {r ++ [ ix 2 ]} t (≺→≼ {r ++ [ ix 1 ]} {r ++ [ ix 2 ]} (Equivalence.from T-≡ (<ᵖ-part r {ix 1} {ix 2} [] [] refl)))

    -- Past all the cursor its need reads has reached.
    past-up : ∀ {Cr C Γ A} {Rg} {c : Ctx R Γ A} {N E} → Fr Rt Cr C Rg c N E
            → ∀ {X} (x : X ∈ Γ) → closedUp c x ≡ false → Onto (Reads N C) (lookup (full (scopeOf c)) x)
    past-up (f-top _) () _
    past-up fr@(f-map _ _ _)                       x cu = live-onto fr tt x cu
    past-up fr@(f-scan _ _ _ _)                    x cu = live-onto fr tt x cu
    past-up fr@(f-cut _)                           x cu = live-onto fr tt x cu
    past-up fr@(f-take _ _ _ _)                    x cu = live-onto fr tt x cu
    past-up (f-took fr _ _ _ _ _ dm _ _ _)         x cu = dom-onto dm (live-onto fr tt x cu)
    past-up fr@(f-outer _ _ _ _ _ _)               x cu = live-onto fr tt x cu
    past-up fr@(f-lanes {b = true} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) x cu = live-onto fr tt x cu
    past-up (f-lanes {b = false} fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dl _) x cu = dom-onto (proj₁ (proj₂ (dl tt))) (live-onto fr tt x cu)
    past-up (f-lane {b = true} fr)                 x cu = past-up fr x cu
    past-up (f-lane {b = false} fr)                x cu = past-up fr x cu
    past-up (f-lnct {b = true} fr)                 x cu = past-up fr x cu
    past-up (f-lnct {b = false} fr)                x cu = past-up fr x cu
    past-up fr@(f-src _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) x cu = live-onto fr tt x cu
    past-up (f-srcc fr _ _ _ _ _ _ dm _ _ _ _ _ _ _ _) x cu = dom-onto dm (live-onto fr tt x cu)
    past-up fr@(f-srcp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) x cu = live-onto fr tt x cu
    past-up fr@(f-body _ _ _ _ _ _ _ _)            x cu = live-onto fr tt x cu
    past-up (d-map fr u)                           x cu = up-onto u (past-up fr x cu)
    past-up (d-scan fr u)                          x cu = up-onto u (past-up fr x cu)
    past-up (d-cut fr u)                           x cu = up-onto u (past-up fr x cu)
    past-up (d-ln fr u)                            x cu = up-onto u (past-up fr x cu)
    past-up (d-take fr u)                          x cu = up-onto u (past-up fr x cu)
    past-up (d-outer fr u _ _)                     x cu = up-onto u (past-up fr x cu)
    past-up (d-lanes fr _ _ _ _ u _)               x cu = up-onto u (past-up fr x cu)
    past-up {c = inSrc k _ c} (d-src u _ _ _ _ _ _ ps _ _) x cu =
      ends-hot (full (scopeOf c)) x ps (unread-past u x cu)
    past-up {c = inBody k _ c} (d-body _ _ _ _ op _) (here refl) cu r =
      op (subst (λ b → T (not b)) (sym cu) tt) (proj₁ r)
    past-up {c = inBody k _ c} (d-body _ _ _ _ _ (inj₁ refl)) (there x) cu = onto-origin (lookup (full (CS.scope k)) x)
    past-up {c = inBody k _ c} (d-body u _ ub _ _ (inj₂ sc)) (there x) cu =
      subst (λ s → Onto _ (lookup (full s) x)) (sym sc) (up-onto ub (unread-past u x cu))
    past-up fr@(f-isle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) x cu = live-onto fr tt x cu
    past-up {c = inSrc k _ c} (f-islec u _ _ _ _ _ _ _ dm _ sd _ ic _ th _ _) x cu =
      ends-hot (full (scopeOf c)) x (λ hc on {s} t → call-onward {r = CS.connAt k} _ ic (proj₂ (SubdAt.hok sd)) hc (on th) {s} (dm t)) (unread-past u x cu)
    past-up fr@(f-islep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) x cu = live-onto fr tt x cu

    -- A dead part's parent: past all it has reached.
    unread-past : ∀ {Cr C D Γ X B} {c : Ctx R Γ B} {k : CS Γ X} {E β : EmissionSet B} {P}
                → Unread Rt Cr C D E β c k P → ∀ {A} (x : A ∈ Γ) → closedUp c x ≡ false → Onto D (lookup (full (scopeOf c)) x)
    unread-past (un-dead fr) x cu = past-up fr x cu
    unread-past (un-torn fr _ _ _ _ _ _ dm) x cu = dom-onto dm (live-onto fr tt x cu)

    live-onto : ∀ {Cr C Γ A} {Rg} {c : Ctx R Γ A} {N E} → Fr Rt Cr C Rg c N E → Live N
              → ∀ {X} (x : X ∈ Γ) → closedUp c x ≡ false → Onto C (lookup (full (scopeOf c)) x)
    live-onto {C = C} fr l x cu = shut-onto C (shut-up fr l x cu)

  -- A JOINER OF A LIVE SUBJECT: joined where it subscribed, read off its
  -- pending frame.
  join-pend : ∀ {Cr C Rg Γ A} {c : Ctx R Γ A} {x : A ∈ Γ} {q E} → closedUp c x ≡ false → Fr Rt Cr C Rg c owes E
            → Owes C q × Ok (Hots (full (scopeOf c))) q × Adm (scopeOf c) × pendRows (full (scopeOf c)) (connected x) q ≈ E × Within Rg (scopeOf c) q (pendRows (full (scopeOf c)) (connected x) q)
            → Inv Rt Cr C ⟨ c , joinS q true x [] , absorbed , q ⟩
  join-pend {C = C} {c = c} {x = x} {q = q} cu fr (ow , ok , adm , eq , wi) with bind (scopeOf c) x adm
  ... | t , lk , B =
    settled c-abs fr (s-join eq (≃-trans (≃-sym (due-≈ {C = C} eq)) (join-due (lookup (full (scopeOf c)) x) lk B ow (shut-up fr tt x cu)))
                       []ᴾ (λ ()) adm)
