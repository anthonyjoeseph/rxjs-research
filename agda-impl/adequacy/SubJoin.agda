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

open import Data.Bool using (T; true; false)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; [_]; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (lookup)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.AllPairs using () renaming ([] to []ᴾ)
import Data.List as L
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Tree using (connected)
open import denotation.Events using (ix; sub; last; _<ᵖ_; <ᵖ-split; <ᵖ-down; <ᵖ-part)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; end; pin; Bare; Unpinned; Dep; Few; Reach; enter; ⟦_⟧; Den; hot;
  coldAt; Proper; Rejoin; shown; heard; ended; late; _≺_)
open import denotation.Read using (Visible)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≺→≼; ≼-trans; entered-few)
open import denotation.Laws.Worlds using (Lawful; InvAt; Ok; Hots; ok-step)
open import denotation.Laws using (inv-⟦⟧)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; Scope; binds; CS; ⟨_,_,_,_⟩; scopeOf; closedUp; pend; joinS; subscribing; absorbed;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (full; pendRows; Inbox; _≃_; _⇄_; ≃-sym; ≃-trans)
open import adequacy.Cursor using (Cur; bef; Owes; Due; Unfed; Adm; Flags; Subd; subd; InCall; Thru; Within; _≈_; s-join)
open import adequacy.Cursor.Tear using (c-abs)
open import adequacy.Cursor.Frame using (Fr; Unread; Need; owes; dead; lane; lanecut; pnd;
  f-top; f-map; f-scan; f-cut; f-take; f-took; f-outer; f-lanes; f-lane; f-lnct; f-src; f-srcc; f-srcp; f-body;
  d-map; d-scan; d-cut; d-ln; d-take; d-outer; d-lanes; d-src; d-body; f-isle; f-islec; f-islep)
open import adequacy.Cursor.Rise using (Inv; settled)
open import adequacy.Walk using (due-≈)
open import adequacy.Bound using (owes?; owes-≼; good-full)

------------------------------------------------------------------------
-- A hot's ends, each still owed.

Shut : ∀ {A} → Cur → Den A → Set
Shut C (hot t)    = ∀ {c} → t c end → Owes C c
Shut C (coldAt _) = ⊤

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
-- THE SUBJECTS ABOVE A LIVE HOLE: each the engine has not closed ends
-- where the hole's cursor has not passed.  A binder whose source runs
-- reads it off its flags; an isle's hole reads it at the isle's cursor.

-- A need some live node reads.
Live : Need → Set
Live owes            = ⊤
Live (dead _ _)      = ⊥
Live (lane _ _ _)    = ⊤
Live (lanecut _ _ _) = ⊤
Live (pnd _)         = ⊤

module _ {R : Set} (Rt : EmissionSet R) where

  postulate
    -- AN ISLE'S SUBJECTS, at its own cursor: each the engine has not
    -- closed ends past where the isle has reached.
    shut-isle : ∀ {Cr C D Ci Γ X B} {c : Ctx R Γ B} {k : CS Γ X} {E′ : EmissionSet B} {β : EmissionSet B} {P}
              → Unread Rt Cr C D E′ β c k P → Thru D (CS.connAt k) → Subd (scopeOf c) Ci k → InCall Ci k
              → ∀ {A} (x : A ∈ Γ) → closedUp c x ≡ false → Shut Ci (lookup (full (scopeOf c)) x)

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
  shut-up (d-src _ _ _ _ _ _ _) () _ _
  shut-up (d-body _ _ _ _) () _ _
  shut-up (f-isle u _ _ _ _ _ _ sd _ _ ic _ th _) _ x cu = shut-isle u th sd ic x cu
  shut-up (f-islec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) () _ _
  shut-up {c = inSrc k _ c} (f-islep u _ _ _ _ _ _ _ _ adm _ _ th _) _ x cu =
    shut-isle u th (subd (λ o → o) (proj₁ adm)) slot x cu
    where
      r = CS.connAt k
      slot : InCall (bef (r ++ [ ix 1 ])) k
      slot {s} t = ≼-trans {s} {r ++ [ ix 1 ]} {r ++ [ ix 2 ]} t (≺→≼ {r ++ [ ix 1 ]} {r ++ [ ix 2 ]} (Equivalence.from T-≡ (<ᵖ-part r {ix 1} {ix 2} [] [] refl)))

  -- A JOINER OF A LIVE SUBJECT: joined where it subscribed, read off its
  -- pending frame.
  join-pend : ∀ {Cr C Rg Γ A} {c : Ctx R Γ A} {x : A ∈ Γ} {q E} → closedUp c x ≡ false → Fr Rt Cr C Rg c owes E
            → Owes C q × Ok (Hots (full (scopeOf c))) q × Adm (scopeOf c) × pendRows (full (scopeOf c)) (connected x) q ≈ E × Within Rg (scopeOf c) q (pendRows (full (scopeOf c)) (connected x) q)
            → Inv Rt Cr C ⟨ c , joinS q true x [] , absorbed , q ⟩
  join-pend {C = C} {c = c} {x = x} {q = q} cu fr (ow , ok , adm , eq , wi) with bind (scopeOf c) x adm
  ... | t , lk , B =
    settled c-abs fr (s-join eq (≃-trans (≃-sym (due-≈ {C = C} eq)) (join-due (lookup (full (scopeOf c)) x) lk B ow (shut-up fr tt x cu)))
                       []ᴾ (λ ()) adm)
