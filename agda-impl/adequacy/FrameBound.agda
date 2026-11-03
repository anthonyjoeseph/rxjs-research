{-# OPTIONS --guardedness #-}

-- THE ROOT'S BOUND FROM A HOLE'S: the frames above a hole compose its
-- bound up to the root's.  Each live frame is its former's bound over
-- its parts', the hole's read off whatever bounds it and its siblings'
-- off their `Sync`; a frame a dead part opens or an unread connect
-- closes owes its parent's entry outright, so the hole's bound is not
-- read past it.  An isle's frames are read at the cursor above the isle,
-- never the isle's own.
module adequacy.FrameBound where

open import Data.Bool using (Bool; T; true; false; not)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; _∷_; _++_; reverse; _ʳ++_)
open import Data.List.Properties using (ʳ++-defn)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import denotation.Events using (Pos)
open import denotation.EmissionSet using (EmissionSet; out; end; _≼_; ⟦_⟧; module Connecting)
open import denotation.Read using (Visible)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; Scope; binds; CS; scopeOf; plug; takeS; connS; flatS)
open import adequacy.Rows using (full; Frozen)
open import adequacy.Rows using (module _≃_)
open _≃_
open import adequacy.Cursor using (Cur; Owes; Due; Pol; Begun; Lane; Kill; Ends; ConnE; Flags; Src; Hole; h-live; h-end; h-kill;
  joined; alike; notT)
open import adequacy.Cursor.Frame using (Need; owes; dead; lane; lanecut; pnd; ⊥₁; Fr; Unread; un-dead; un-torn;
  f-top; f-map; f-scan; f-cut; f-take; f-took; f-outer; f-lanes; f-lane; f-lnct; f-src; f-srcc; f-srcp; f-body;
  d-map; d-scan; d-cut; d-ln; d-take; d-outer; d-lanes; d-src; d-body; f-isle; f-islec; f-islep)
open import adequacy.Least using (k-kid; k-outer; k-lane; k-src; k-body)
open import adequacy.Floor.Keys using (plug-in)
open import adequacy.Bound using (Bnd; LoP; Env; owes-≼; map-b; scan-b; take-b; took-b; conn-b; flat-b; begun-b; bound; src-b)

------------------------------------------------------------------------
-- What bounds a hole, by its need: its entry under the hole's scope; a
-- lane's while it runs; nothing, where no live node reads it.

HB : ∀ {Γ A} → Cur → Pos → Scope Γ → Need → EmissionSet A → Set₁
HB C p sc owes          E = Env (full sc) C p → Bnd C p E
HB C p sc (dead _)      E = ⊤
HB C p sc (lane b _)    E = T b → Env (full sc) C p → Bnd C p E
HB C p sc (lanecut b _) E = T b → Env (full sc) C p → Bnd C p E
HB C p sc (pnd _)       E = ⊥₁

-- A connect's entry, its body bounded while its source runs.
conn-fb : ∀ {Γ X B} {sc : Scope Γ} {C} {k : CS Γ X} {β E : EmissionSet B} {p}
        → CS.scope k ≡ sc
        → (T (CS.srcLive k) → Env (full (binds (CS.src k) (CS.connAt k) (CS.scope k))) C p → Bnd C p β)
        → (T (CS.srcLive k) → Bnd C p (Frozen k)) → Flags C k β → Env (full sc) C p
        → ConnE (CS.connAt k) (Frozen k) β E → Bnd C p E
conn-fb {C = C} refl bb sb fl env ce (x , v , ow) =
  let ((y , _) , v′) = from (alike (proj₁ ce)) (x , v) in conn-b {C = C} bb sb fl env (y , v′) ow

-- A source in step, under its connect's scope.
src-fb : ∀ {Γ X B} {sc : Scope Γ} {Rg C} {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) B} {p}
       → CS.scope k ≡ sc → Src sc Rg C k o → Env (full sc) C p → LoP (connS k o b) p → Bnd C p (Frozen k)
src-fb refl sr env lo = src-b sr env lo

-- The hole among a joiner's lanes: its rows while it runs; ended or
-- killed, none it still owes.
hole-fb : ∀ {A B} {C} {P : Pol A B} {O : EmissionSet A} {q a Ph E b k e p}
        → Hole C P q a Ph E b → (T b → Bnd C p E) → O q (out a) → Ends P O
        → (∀ {q′} → Kill P q q′ → k ≼ q′) → Lane P q a k e → Visible e → Owes C k → p ≼ k
hole-fb (h-live _ eq _) hb _ _ _ ln v ow = hb _ (proj₁ (from (alike eq) (ln , v)) , v , ow)
hole-fb {C = C} (h-end lc nc _) _ y en _ ln v ow = ⊥-elim (nc (owes-≼ C ow (en y lc ln v)))
hole-fb {C = C} (h-kill kq nq _) _ _ _ kl _ _ ow = ⊥-elim (nq (owes-≼ C ow (kl kq)))

-- A lane before the hole, or after it, among its siblings.
pre-in : ∀ {a} {S : Set a} (pre : List S) {s post x} → x ∈ reverse pre → x ∈ pre ʳ++ s ∷ post
pre-in pre {s} {post} m rewrite ʳ++-defn pre {s ∷ post} = ∈-++⁺ˡ m

post-in : ∀ {a} {S : Set a} (pre : List S) {s post x} → x ∈ post → x ∈ pre ʳ++ s ∷ post
post-in pre {s} {post} m rewrite ʳ++-defn pre {s ∷ post} = ∈-++⁺ʳ (reverse pre) (there m)

-- A joiner's begun lanes, the hole among them.
lanes-b : ∀ {Γ} {sc : Scope Γ} {Rl} {C A B} {P : Pol A B} {O : EmissionSet A} {vs₁ vs₂ : List (Pos × A)}
            {pre post : List (St Γ B)} {s : St Γ B} {n₁ n₂ q a Ph E b p}
        → Begun sc Rl C P O vs₁ (reverse pre) n₁ → Hole C P q a Ph E b → Begun sc Rl C P O vs₂ post n₂
        → O q (out a) → Ends P O → Env (full sc) C p → (T b → Bnd C p E) → (∀ {l} → l ∈ pre ʳ++ s ∷ post → LoP l p)
        → ∀ {q′ a′ k e} → (q′ , a′) ∈ vs₁ ++ (q , a) ∷ vs₂ → (∀ {q″} → Kill P q′ q″ → k ≼ q″) → Lane P q′ a′ k e
        → Visible e → Owes C k → p ≼ k
lanes-b {O = O} {vs₁ = vs₁} {pre = pre} bg₁ hl bg₂ y en env hb lo iv kl ln v ow with ∈-++⁻ vs₁ iv
... | inj₁ i₁          = begun-b {O = O} bg₁ i₁ kl ln v ow en env (λ i → lo (pre-in pre i))
... | inj₂ (here refl) = hole-fb {O = O} hl hb y en kl ln v ow
... | inj₂ (there i₂)  = begun-b {O = O} bg₂ i₂ kl ln v ow en env (λ i → lo (post-in pre i))

module _ {R : Set} (Rt : EmissionSet R) where

  mutual
    fb : ∀ {Cr C Γ A Rg} {c : Ctx R Γ A} {N E} {s : St Γ A} {p}
       → Fr Rt Cr C Rg c N E → LoP (plug c s) p → HB C p (scopeOf c) N E → Bnd Cr p Rt
    fb (f-top eq) lo hb (x , v , ow) = let (y , v′) = from (alike eq) (x , v) in hb (λ {_} ()) (y , v′ , ow)
    fb {C = C} {s = s} (f-map fr m _) lo hb =
      fb {s = Machine.mapS _ s} fr lo λ env (x , v , ow) → map-b {C = C} (hb env) (from (alike m) (x , v)) ow
    fb {C = C} {s = s} (f-scan fr _ m _) lo hb =
      fb {s = Machine.scanS _ _ s} fr lo λ env (x , v , ow) → scan-b {C = C} (hb env) (from (alike m) (x , v)) ow
    fb {s = s} (f-cut fr) lo hb = fb {s = Machine.cutS true _ s} fr lo hb
    fb {C = C} {s = s} (f-take fr nf m _) lo hb =
      fb {s = takeS _ _ _ s} fr lo λ env (x , v , ow) → take-b {C = C} (hb env) nf (from (alike m) (x , v)) ow
    fb {C = C} {c = Machine.inTake _ _ _ c} {s = s} (f-took fr fl g ni oa _ m sd) lo _ =
      fb {s = takeS _ _ _ s} fr lo λ env (x , v , ow) →
        took-b {C = C} {s = s} fl g ni oa sd (λ ki → lo (plug-in c ki)) (from (alike m) (x , v)) ow
    fb {C = C} {c = Machine.inOuter op f _ _ _ _ ls c} {s = s} (f-outer fr _ (joined bg _ wh _ ah _ en _) je _ _) lo hb =
      fb {s = flatS _ _ _ _ _ _ s ls} fr lo λ env (x , v , ow) →
        flat-b {op = op} {F = λ a → ⟦ f a ⟧ (full (scopeOf c))} {C = C} (hb env)
          (λ iv kl ln v′ ow′ → begun-b bg iv kl ln v′ ow′ en env (λ i ki → lo (plug-in c (k-kid (k-lane i ki))))) wh ah
          (proj₁ (proj₁ (from (alike (proj₂ je)) (x , v)))) v ow
    fb {C = C} {c = Machine.inLanes op f _ _ _ _ o pre post c} {s = s}
       (f-lanes {vs₁ = vs₁} fr _ sy bg₁ y _ _ hl bg₂ _ _ wh _ ah _ en _ je _ _ _) lo hb =
      fb {s = flatS _ _ _ _ _ _ o (pre ʳ++ s ∷ post)} fr lo λ env (x , v , ow) →
        flat-b {op = op} {F = λ a → ⟦ f a ⟧ (full (scopeOf c))} {C = C}
          (bound sy env (λ ki → lo (plug-in c (k-kid (k-outer ki)))))
          (lanes-b {pre = pre} {post = post} {s = s} bg₁ hl bg₂ y en env (λ t → hb t env) (λ i ki → lo (plug-in c (k-kid (k-lane i ki)))))
          wh ah (proj₁ (proj₁ (from (alike (proj₂ je)) (x , v)))) v ow
    fb {s = s} (f-lane fr) lo hb = fb {s = Machine.lnS _ s} fr lo hb
    fb {s = s} (f-lnct {b = true} fr) lo hb = fb {s = Machine.cutS true _ s} fr lo (λ _ → hb)
    fb {s = s} (f-lnct {b = false} fr) lo hb = fb {s = Machine.cutS false _ s} fr lo (λ ())
    fb {C = C} {c = Machine.inSrc k b c} {s = s} (f-src fr sc _ _ _ bs _ fl fe ce _ _ _ _ _) lo hb =
      fb {s = connS k s b} fr lo λ env →
        conn-fb {C = C} sc
          (λ _ envb → bound bs (subst (λ x → Env (full (binds (CS.src k) (CS.connAt k) x)) C _) sc envb)
                         (λ ki → lo (plug-in c (k-kid (k-body ki)))))
          (λ _ (x , v , ow) → let (y , v′) = from (alike fe) (x , v) in hb env (y , v′ , ow)) fl env ce
    fb {C = C} {c = Machine.inSrc k b c} {s = s} (f-srcc fr sc _ _ _ sp _ _ _ bs _ fl ce) lo _ =
      fb {s = connS k s b} fr lo λ env →
        conn-fb {C = C} sc
          (λ _ envb → bound bs (subst (λ x → Env (full (binds (CS.src k) (CS.connAt k) x)) C _) sc envb)
                         (λ ki → lo (plug-in c (k-kid (k-body ki)))))
          (λ _ d → ⊥-elim (sp d)) fl env ce
    fb (f-srcp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) lo ()
    fb {C = C} {c = Machine.inBody k o c} {s = s} (f-body fr sc _ _ sr _ fl ce) lo hb =
      fb {s = connS k o s} fr lo λ env →
        conn-fb {C = C} sc (λ _ → hb) (λ _ → src-fb {b = s} sc sr env (λ ki → lo (plug-in c ki))) fl env ce
    fb {s = s} (d-map fr) lo _ = fb {s = Machine.mapS _ s} fr lo _
    fb {s = s} (d-scan fr) lo _ = fb {s = Machine.scanS _ _ s} fr lo _
    fb {s = s} (d-cut fr) lo _ = fb {s = Machine.cutS _ _ s} fr lo _
    fb {s = s} (d-ln fr) lo _ = fb {s = Machine.lnS _ s} fr lo _
    fb {s = s} (d-take fr) lo _ = fb {s = takeS _ _ _ s} fr lo _
    fb {c = Machine.inOuter _ _ _ _ _ _ ls _} {s = s} (d-outer fr _ _) lo _ = fb {s = flatS _ _ _ _ _ _ s ls} fr lo _
    fb {c = Machine.inLanes _ _ _ _ _ _ o pre post _} {s = s} (d-lanes fr _ _ _ _) lo _ =
      fb {s = flatS _ _ _ _ _ _ o (pre ʳ++ s ∷ post)} fr lo _
    fb (d-src u _ _ _ _) lo _ = fb-u u lo
    fb (d-body u _ _) lo _ = fb-u u lo
    fb (f-isle u _ _ _ _ _ _ _ _ _) lo _ = fb-u u lo
    fb (f-islec u _ _ _ _ _ _ _ _) lo _ = fb-u u lo
    fb (f-islep u _ _ _ _ _ _ _ _ _ _) lo _ = fb-u u lo

    fb-u : ∀ {Cr C Γ X B} {c : Ctx R Γ B} {k : CS Γ X} {P} {o : St Γ X} {b : St (X ∷ Γ) B} {p}
         → Unread Rt Cr C c k P → LoP (plug c (connS k o b)) p → Bnd Cr p Rt
    fb-u {o = o} {b} (un-dead fr) lo = fb {s = connS _ o b} fr lo _
    fb-u {C = C} {k = k} {o = o} {b} (un-torn fr sc _ nl fl ce _) lo =
      fb {s = connS k o b} fr lo λ env →
        conn-fb {C = C} sc (λ t → ⊥-elim (notT _ nl t)) (λ t → ⊥-elim (notT _ nl t)) fl env ce
