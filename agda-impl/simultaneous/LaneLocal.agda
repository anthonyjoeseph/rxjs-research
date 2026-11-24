{-# OPTIONS --guardedness #-}

-- WHAT A LANE'S ROWS HOLD, ONE BY ONE: a begin is named for its
-- instant, a value and an end lie before their step's over, an over at
-- it, and a lane's own marks before it too.  Each former the real
-- flatMap is built from keeps that, so its lanes do, given that the
-- programs they subscribe hold.
module simultaneous.LaneLocal where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import denotation.Read using (Visible)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; empty; of; takeWhile; flatMap; connect; connected)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; sub; last; _⊕_)
open import denotation.Events using (Timeline; fresh; ofᴱ)
open import denotation.EmissionSet using (EmissionSet; map-out; map-end; Ev; Den; hot; enter; Proper; DenEnv; out; end; shown; ended;
  late; at-end; InE; at-out; on-out; Superseded; module Op; module Joiner; module Bounded;
  module Values; module Scan; module TakeWhile; module Exhaust; module Connecting)
open import denotation.Laws using (inv-⟦⟧; inv-approx; good-cons)
open import denotation.Laws.Connect using () renaming (lawful to src-lawful; ok₀ to body-ok)
open import denotation.Laws.Worlds using (Ok; InvD; InvAt; Lawful; Hots; GoodEnv; _∪ʰ_; ok-step; ok-in; ⊑-trans; _⊑_; plain-ix)
open import denotation.Laws.Worlds.Leaves using (of-end)
open import simultaneous.SObs using (lone; Part; lanePart; burstPart; module Elaborate)
open import simultaneous.InstEmit using (InstEmit; instEmit; value; mark; begin; over; stop; subscribed; completed; outerOpen; outerClose;
  laneStart; laneDone; burstEnd; outerDone; valuesOf)
open import simultaneous.Routed using (Held; Early; Valued; opos; nameOf; nm; Shown; s-value; s-done; s-end; Placed; Adm; adm-∪; adm-at; ok-ix)
open import simultaneous.Readings using (rootOf)
open import simultaneous.HeldComb using (ev)
open import simultaneous.HeldConnect using (early-inst; rootOf-ext)
open import simultaneous.DenRows using (merge-out; hot-out; of-mem; nth-row)
open import simultaneous.CombSent using (of-at; module EachEnd)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone
  using (IE; AIE; Routes; elab; laneˢ; laneSrc; shareˢ; blockˢ; counted; framed; piece; laneStep; tell; undone; each; marked)

-- Either reading is lawful.
inv-ev : ∀ m {Γ A} (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → InvD (Hots ρ) (ev m o ρ)
inv-ev nothing  o ρ g = inv-⟦⟧ o ρ g
inv-ev (just n) o ρ g = inv-approx n o ρ g

-- Past its over, a step is as late.
late-ext : ∀ {q} zs → Valued (rootOf q) × opos (rootOf q) ⊑ q
         → Valued (rootOf (q ⊕ zs)) × opos (rootOf (q ⊕ zs)) ⊑ (q ⊕ zs)
late-ext {q} zs (v , o) = subst (λ I → Valued I × opos I ⊑ (q ⊕ zs)) (sym (rootOf-ext q zs)) (v , ⊑-trans o (zs , refl))

------------------------------------------------------------------------
-- A row's own claim: an `outerOpen` or an `outerDone`, never, as no lane
-- opens or ends an outer.

Fine : ∀ {A} → IE A → Pos → Set
Fine (instEmit (value _) _)          y = Early y
Fine (instEmit (mark begin) n)       y = n ≡ nameOf y
Fine (instEmit (mark over) _)        y = Valued (rootOf y) × opos (rootOf y) ⊑ y
Fine (instEmit (mark laneStart) _)   y = Early y
Fine (instEmit (mark (laneDone _)) _)    y = Early y
Fine (instEmit (mark burstEnd) _)    y = Early y
Fine (instEmit (mark stop) _)        y = ⊤
Fine (instEmit (mark subscribed) _)  y = ⊤
Fine (instEmit (mark completed) _)   y = Early y
Fine (instEmit (mark outerOpen) _)   y = ⊥
Fine (instEmit (mark outerClose) _)  y = ⊤
Fine (instEmit (mark outerDone) _)   y = ⊥

-- Below a row, its claim holds as it did.
fine-ext : ∀ {A} (x : IE A) {y} zs → Fine x y → Fine x (y ⊕ zs)
fine-ext (instEmit (value _) _)         zs f = early-inst zs f
fine-ext (instEmit (mark begin) _) {y} zs f = trans f (cong nm (sym (rootOf-ext y zs)))
fine-ext (instEmit (mark over) _) {y} zs f = late-ext {y} zs f
fine-ext (instEmit (mark laneStart) _)  zs f = early-inst zs f
fine-ext (instEmit (mark (laneDone _)) _)   zs f = early-inst zs f
fine-ext (instEmit (mark burstEnd) _)   zs f = early-inst zs f
fine-ext (instEmit (mark stop) _)       zs f = tt
fine-ext (instEmit (mark subscribed) _) zs f = tt
fine-ext (instEmit (mark completed) _)  zs f = early-inst zs f
fine-ext (instEmit (mark outerOpen) _)  zs f = f
fine-ext (instEmit (mark outerClose) _) zs f = tt
fine-ext (instEmit (mark outerDone) _)  zs f = f

-- EVERY ROW AS IT CLAIMS, the end before its step's over, and every row
-- a lane can hang on admissible.
record Fit {A} (Fr : Pos → Set) (t : EmissionSet (IE A)) : Set where
  constructor fit
  field
    fine   : ∀ {y x} → t y (out x) → Fine x y
    ends   : ∀ {y} → t y end → Early y
    placed : Placed Fr t

FitD : ∀ {A} → (Pos → Set) → (Pos → Set) → Den (IE A) → Set
FitD H Fr d = ∀ p → Ok H p → Fr p → Early p → Fit Fr (enter d p)

EndsEarly : ∀ {A} → EmissionSet A → Set
EndsEarly t = ∀ {c} → t c end → Early c

-- A flatMap's outer: its values and end early, every row admissible.
Outer : ∀ {A} → (Pos → Set) → EmissionSet A → Set
Outer Fr t = (∀ {q a} → t q (out a) → Early q) × EndsEarly t × (∀ {q e} → t q e → Visible e → Fr q)

-- A hot's rows, wherever it is read.
FitH : ∀ {A} → (Pos → Set) → EmissionSet (IE A) → Set
FitH Fr t = (∀ {y x} → t y (out x) → Fine x y) × EndsEarly t × Placed Fr t

proper-fit : ∀ {A Fr} {t : EmissionSet (IE A)} → Fit Fr t → Fit Fr (Proper t)
proper-fit F = fit (λ r → Fit.fine F (proj₁ r)) (λ r → Fit.ends F (proj₁ r)) (λ r → Fit.placed F (proj₁ r))

proper-fitH : ∀ {A Fr} {t : EmissionSet (IE A)} → Fit Fr t → FitH Fr (Proper t)
proper-fitH F = (λ r → Fit.fine F (proj₁ r)) , (λ r → Fit.ends F (proj₁ r)) , (λ r → Fit.placed F (proj₁ r))

-- A row a lane can hang on is told of.
shown-vis : ∀ {A} {e : Ev (IE A)} → Shown e → Visible e
shown-vis s-value = tt
shown-vis s-done  = tt
shown-vis s-end   = tt

-- A held stream fits: its marks are routing marks, never a lane's.
held-fit : ∀ {A Fr} {t : EmissionSet (IE A)} {cs} → Held t cs → Placed Fr t → Fit Fr t
held-fit {t = t} H pl = fit fine (Held.ends H) pl
  where
    fine : ∀ {y x} → t y (out x) → Fine x y
    fine {x = instEmit (value _) _}         r = Held.early H r
    fine {x = instEmit (mark begin) _}      r = Held.named H r
    fine {x = instEmit (mark over) _}       r = Held.late H r
    fine {x = instEmit (mark laneStart) _}  r with () ← Held.routing H r
    fine {x = instEmit (mark (laneDone _)) _} r with () ← Held.routing H r
    fine {x = instEmit (mark burstEnd) _}   r with () ← Held.routing H r
    fine {x = instEmit (mark stop) _}       r = tt
    fine {x = instEmit (mark subscribed) _} r = tt
    fine {x = instEmit (mark completed) _}  r = Held.done H r
    fine {x = instEmit (mark outerOpen) _}  r with () ← Held.routing H r
    fine {x = instEmit (mark outerClose) _} r = tt
    fine {x = instEmit (mark outerDone) _}  r with () ← Held.routing H r

------------------------------------------------------------------------
-- The leaves

-- A value of `of` and its end lie at its subscription, each a child of it.
of-early : ∀ {X H Fr} (xs : List X) → Adm H Fr → ∀ p → Ok H p → Fr p → Early p → Outer Fr (enter (Op.of xs) p)
of-early {Fr = Fr} xs ad p ok fp ep =
  (λ (r , _) → let (l , eq) = of-at p 0 xs r in subst Early (sym eq) (early-inst [ l ] ep)) ,
  (λ (r , _) → subst Early (sym (of-end p 0 xs r)) (early-inst [ last ] ep)) ,
  fr
  where
    fr : ∀ {q e} → enter (Op.of xs) p q e → Visible e → Fr q
    fr {e = out _} (r , _) _ = let (l , eq) = of-at p 0 xs r in subst Fr (sym eq) (adm-at ad ok fp l)
    fr {e = end}   (r , _) _ = subst Fr (sym (of-end p 0 xs r)) (Adm.bare ad fp λ ())

-- An `of`'s value lies at an index.
of-ix : ∀ {X} p i (xs : List X) {y a} → InE (ofᴱ p i xs) y (out a) → Σ ℕ λ j → y ≡ p ⊕ [ ix j ]
of-ix p i (_ ∷ _)  at-out     = i , refl
of-ix p i (_ ∷ xs) (on-out r) = of-ix p (suc i) xs r


hot-fit : ∀ {A Fr} {t : EmissionSet (IE A)} → FitH Fr t → ∀ {H} → Adm H Fr → FitD H Fr (hot t)
hot-fit {Fr = Fr} {t = t} (tf , te , tp) ad p _ fp ep = fit fine ends placed
  where
    fine : ∀ {y x} → enter (hot t) p y (out x) → Fine x y
    fine {x = x} (shown y _ _ , _) = fine-ext x [ sub p ] (tf y)
    ends : ∀ {y} → enter (hot t) p y end → Early y
    ends (ended y _ , _)    = early-inst [ sub p ] (te y)
    ends (late _ _ , _)     = early-inst [ last ] ep
    ends (shown _ () _ , _)
    placed : Placed Fr (enter (hot t) p)
    placed (shown y _ _ , _) sh = Adm.copy ad (tp y sh)
    placed (ended y _ , _) _    = Adm.copy ad (tp y s-end)
    placed (late _ _ , _) _     = Adm.bare ad fp λ ()

of-fit : ∀ {A Fr} (xs : List (IE A)) → (∀ {x y} → x ∈ xs → Early y → Fine x y) → ∀ {H} → Adm H Fr → FitD H Fr (Op.of xs)
of-fit {Fr = Fr} xs h ad p ok fp ep = fit fine ends (λ r sh → proj₂ (proj₂ (of-early xs ad p ok fp ep)) r (shown-vis sh))
  where
    fine : ∀ {y x} → enter (Op.of xs) p y (out x) → Fine x y
    fine {x = x} (r , _) = let (l , eq) = of-at p 0 xs r in subst (Fine x) (sym eq) (h (of-mem p 0 xs r) (early-inst [ l ] ep))
    ends : ∀ {y} → enter (Op.of xs) p y end → Early y
    ends (r , _) = subst Early (sym (of-end p 0 xs r)) (early-inst [ last ] ep)

empty-fit : ∀ {A H Fr} → Adm H Fr → FitD H Fr (Op.empty {IE A})
empty-fit ad p _ fp ep = fit (λ { (() , _) }) (λ { (at-end , _) → early-inst [ last ] ep }) (λ { (at-end , _) _ → Adm.bare ad fp λ () })

-- A lone lane mark lies before its step's over wherever it falls.
lone-early : ∀ {B} {x₀ : IE B} → (∀ {y} → Early y → Fine x₀ y) → ∀ {x y} → x ∈ (x₀ ∷ []) → Early y → Fine x y
lone-early h (here refl) e = h e
lone-early h (there ())

------------------------------------------------------------------------
-- A flatMap, under every policy

module FlatFit {A B : Set} {H Fr : Pos → Set} (f : A → Den (IE B)) (d : Den A) (ad : Adm H Fr)
               (Id : InvD H d) (If : ∀ a → InvD H (f a)) (Ff : ∀ a → FitD H Fr (f a))
               (p : Pos) (ok : Ok H p)
               (o-early : ∀ {q a} → enter d p q (out a) → Early q) (o-end : EndsEarly (enter d p))
               (o-fr : ∀ {q e} → enter d p q e → Visible e → Fr q) where

  -- An outer row is reachable and clear of the hot rows.
  ok-o : ∀ {q e} → enter d p q e → Ok H q
  ok-o x = ok-in ok (InvAt.world (Id p ok) x) (InvAt.real (Id p ok) x)

  -- A value's lane, subscribed at its second child.
  val-fit : ∀ {q a} → enter d p q (out a) → Fit Fr (enter (f a) (q ⊕ [ ix 1 ]))
  val-fit {q} {a} x =
    Ff a (q ⊕ [ ix 1 ]) (ok-step q (ok-o x)) (Adm.step ad (ok-o x) (o-fr x tt) plain-ix) (early-inst [ ix 1 ] (o-early x))

  module J (Runs : Pos → Set) (Cut : Pos → Pos → Set) where
    open Joiner f (enter d p) Runs Cut

    fine : ∀ {y x} → JoinT y (out x) → Fine x y
    fine (lane o _ (l , _) _ _) = Fit.fine (val-fit o) l
    fine (run () _)

    ends : ∀ {y} → JoinT y end → Early y
    ends (oend o _)               = o-end o
    ends (lane _ _ _ _ ())
    ends (lend o _ (l , _) _ _ _) = Fit.ends (val-fit o) l
    ends (run () _)
    ends (rend () _ _)

    placed : ∀ {y e} → JoinT y e → Shown e → Fr y
    placed (lane o _ (l , _) _ _) sh    = Fit.placed (val-fit o) l sh
    placed (oend o _) _                 = o-fr o tt
    placed (lend o _ (l , _) _ _ _) _   = Fit.placed (val-fit o) l s-end
    placed (run () _)
    placed (rend () _ _)

  -- A queued lane starts at an earlier lane's end, which fits.
  module Bd (n : ℕ) where
    open Values (enter d p) using (Nth)
    open Bounded n f (enter d p)

    -- Where a lane starts: early, reachable, clear, admissible.
    Start : Pos → Set
    Start s = Early s × Ok H s × Fr s

    at-row : ∀ i {q a} → Nth i q a → Start (q ⊕ [ ix 1 ])
    at-row i {q} N =
      early-inst [ ix 1 ] (o-early (nth-row N)) , ok-step q (ok-o (nth-row N)) , Adm.step ad (ok-o (nth-row N)) (o-fr (nth-row N) tt) plain-ix

    mutual
      start-at : ∀ i {q a s} → Nth i q a → Starts i q (Sched i) s → Start s
      start-at i N (room _)    = at-row i N
      start-at i N (freed _ _) = at-row i N
      start-at i N (queued {c} _ _ one _ _) =
        let (ec , okc , fc) = sched-at i one in early-inst [ ix 1 ] ec , ok-step c okc , Adm.step ad okc fc plain-ix

      sched-at : ∀ i {c} → Kth (_≡ c) (Sched i) 0 → Start c
      sched-at zero ()
      sched-at (suc i) (inj₁ (_ , (_ , _ , _ , N , St , (y , _)) , refl)) = end-at i N St y
      sched-at (suc i) (inj₂ k) = sched-at i k

      end-at : ∀ i {q a s c} → Nth i q a → Starts i q (Sched i) s → enter (f a) s c end → Start c
      end-at i {a = a} {s} N St y =
        let (es , oks , fs) = start-at i N St in
        Fit.ends (Ff a s oks fs es) y , ok-in oks (InvAt.world (If a s oks) y) (InvAt.real (If a s oks) y) , Fit.placed (Ff a s oks fs es) y s-end

    lane-fit : ∀ i {q a s} → Nth i q a → Starts i q (Sched i) s → Fit Fr (enter (f a) s)
    lane-fit i {a = a} {s} N St = let (es , oks , fs) = start-at i N St in Ff a s oks fs es

    fine : ∀ {y x} → JoinT y (out x) → Fine x y
    fine (lane _ _ (i , s , (N , St) , (l , _)) _ _) = Fit.fine (lane-fit i N St) l
    fine (run () _)

    ends : ∀ {y} → JoinT y end → Early y
    ends (oend o _)                                     = o-end o
    ends (lane _ _ _ _ ())
    ends (lend _ _ (i , s , (N , St) , (l , _)) _ _ _)  = proj₁ (end-at i N St l)
    ends (run () _)
    ends (rend () _ _)

    placed : ∀ {y e} → JoinT y e → Shown e → Fr y
    placed (lane _ _ (i , s , (N , St) , (l , _)) _ _) sh = Fit.placed (lane-fit i N St) l sh
    placed (oend o _) _                                   = o-fr o tt
    placed (lend _ _ (i , s , (N , St) , (l , _)) _ _ _) _ = proj₂ (proj₂ (end-at i N St l))
    placed (run () _)
    placed (rend () _ _)

  flat-fit : ∀ op → Fit Fr (enter (Op.flatMap op f d) p)
  flat-fit (mergeᶠ nothing)  = fit (λ (j , _) → J.fine (λ _ → ⊤) (λ _ _ → ⊥) j) (λ (j , _) → J.ends (λ _ → ⊤) (λ _ _ → ⊥) j)
                                   (λ (j , _) → J.placed (λ _ → ⊤) (λ _ _ → ⊥) j)
  flat-fit (mergeᶠ (just n)) = fit (λ (j , _) → Bd.fine n j) (λ (j , _) → Bd.ends n j) (λ (j , _) → Bd.placed n j)
  flat-fit switchᶠ           = fit (λ (j , _) → J.fine (λ _ → ⊤) (Superseded (enter d p)) j)
                                   (λ (j , _) → J.ends (λ _ → ⊤) (Superseded (enter d p)) j)
                                   (λ (j , _) → J.placed (λ _ → ⊤) (Superseded (enter d p)) j)
  flat-fit exhaustᶠ          = fit (λ (j , _) → J.fine (Exhaust.Run f (enter d p)) (λ _ _ → ⊥) j)
                                   (λ (j , _) → J.ends (Exhaust.Run f (enter d p)) (λ _ _ → ⊥) j)
                                   (λ (j , _) → J.placed (Exhaust.Run f (enter d p)) (λ _ _ → ⊥) j)

flat-fitD : ∀ {A B : Set} {H Fr} op {f : A → Den (IE B)} {d : Den A} → Adm H Fr → InvD H d → (∀ a → InvD H (f a)) → (∀ a → FitD H Fr (f a))
          → (∀ p → Ok H p → Fr p → Early p → Outer Fr (enter d p))
          → FitD H Fr (Op.flatMap op f d)
flat-fitD op {f} {d} ad Id If Ff od p ok fp ep =
  FlatFit.flat-fit f d ad Id If Ff p ok (proj₁ (od p ok fp ep)) (proj₁ (proj₂ (od p ok fp ep))) (proj₂ (proj₂ (od p ok fp ep))) op

------------------------------------------------------------------------
-- A takeWhile, a connect, a lane's count

take-fit : ∀ {A H Fr} i keep {d : Den (IE A)} → Adm H Fr → (∀ {x y} → T (not (keep x)) → Fine x y → Early y)
         → (∀ {x} → T (not (keep x)) → Shown (out x)) → FitD H Fr d → FitD H Fr (Op.takeWhile i keep d)
take-fit {Fr = Fr} i keep {d} ad fe fs Fd p ok fp ep = fit fine ends placed
  where
    F = Fd p ok fp ep
    fine : ∀ {y x} → enter (Op.takeWhile i keep d) p y (out x) → Fine x y
    fine (TakeWhile.pass t _ _ , _)         = Fit.fine F t
    fine (TakeWhile.fail {a = a} t _ _ _ , _) = fine-ext a [ ix 0 ] (Fit.fine F t)
    ends : ∀ {y} → enter (Op.takeWhile i keep d) p y end → Early y
    ends (TakeWhile.stop t nk _ , _) = early-inst [ last ] (fe nk (Fit.fine F t))
    ends (TakeWhile.tend t _ , _)    = Fit.ends F t
    placed : Placed Fr (enter (Op.takeWhile i keep d) p)
    placed (TakeWhile.pass t _ _ , _) sh   = Fit.placed F t sh
    placed (TakeWhile.fail t _ _ _ , _) sh = Adm.bare ad (Fit.placed F t sh) λ ()
    placed (TakeWhile.stop t nk _ , _) _   = Adm.bare ad (Fit.placed F t (fs nk)) λ ()
    placed (TakeWhile.tend t _ , _) sh     = Fit.placed F t sh

-- A CONNECT SHOWS ITS BODY, read over the source made hot: what the
-- body fits, given what the source's rows give it.
conn-fit : ∀ {A B H Fr} (Q : EmissionSet A → Set) {s : Den A} {F : Den A → Den (IE B)} (ad : Adm H Fr)
           (Is : InvD H s) (IF : ∀ {t} → Lawful t → InvD (H ∪ʰ t) (F (hot t)))
         → (∀ p → Ok H p → Fr p → Early p → Q (Proper (enter s (p ⊕ [ ix 1 ])))) → (∀ {t} → Lawful t → Q t → FitD (H ∪ʰ t) Fr (F (hot t)))
         → FitD H Fr (Op.connect s F)
conn-fit {Fr = Fr} Q {s} {F} ad Is IF Qs LF p ok fp ep =
  fit (λ { (Connecting.body x , _) → Fit.fine Fb x }) (λ { (Connecting.body x , _) → Fit.ends Fb x })
      (λ { (Connecting.body x , _) sh → Fit.placed Fb x sh })
  where
    Fb : Fit Fr (enter (F (hot (Proper (enter s (p ⊕ [ ix 1 ]))))) (p ⊕ [ ix 0 ]))
    Fb = LF (src-lawful {s = s} {F = F} Is IF p ok) (Qs p ok fp ep) (p ⊕ [ ix 0 ]) (body-ok {s = s} {F = F} Is IF p ok)
            (Adm.bare ad fp λ ()) (early-inst [ ix 0 ] ep)

data Done {B : Set} : IE B → Set where
  done : ∀ {k n} → Done (instEmit (mark (laneDone k)) n)

-- What a lane tells of a row: the row, or at its `laneDone` the routes.
tell-is : ∀ {B} r (x : IE B) → tell r x ≡ x ⊎ (Done x × Done (tell r x))
tell-is r (instEmit (mark (laneDone _)) _) = inj₂ (done , done)
tell-is r (instEmit (value _) _)        = inj₁ refl
tell-is r (instEmit (mark begin) _)      = inj₁ refl
tell-is r (instEmit (mark over) _)       = inj₁ refl
tell-is r (instEmit (mark stop) _)       = inj₁ refl
tell-is r (instEmit (mark subscribed) _) = inj₁ refl
tell-is r (instEmit (mark completed) _)  = inj₁ refl
tell-is r (instEmit (mark outerOpen) _)  = inj₁ refl
tell-is r (instEmit (mark outerClose) _) = inj₁ refl
tell-is r (instEmit (mark laneStart) _)  = inj₁ refl
tell-is r (instEmit (mark burstEnd) _)   = inj₁ refl
tell-is r (instEmit (mark outerDone) _)  = inj₁ refl

done-fine : ∀ {B} {x e : IE B} {y} → Done x → Done e → Fine x y → Fine e y
done-fine done done f = f

tell-fine : ∀ {B} r (x : IE B) {y} → Fine x y → Fine (tell r x) y
tell-fine r x f with tell r x | tell-is r x
... | _ | inj₁ refl       = f
... | _ | inj₂ (dx , de)  = done-fine dx de f

-- A told row a lane can hang on is the row itself.
tell-shown : ∀ {B} r (x : IE B) → Shown (out (tell r x)) → Shown (out x)
tell-shown r x sh with tell r x | tell-is r x
... | _ | inj₁ refl      = sh
... | _ | inj₂ (done , _) = s-done

-- A LANE'S COUNT SHOWS ITS ROWS, each at its row.
module CountedFit {B : Set} {H Fr : Pos → Set} (z : Routes × IE B) (d : Den (IE B))
                  (Fd : FitD H Fr d) (p : Pos) (ok : Ok H p) (fp : Fr p) (ep : Early p) where

  F = Fd p ok fp ep

  acc-last : ∀ {q st} → Scan.Acc laneStep z (enter d p) q st → Σ _ λ st′ → Σ (IE B) λ x → enter d p q (out x) × st ≡ laneStep st′ x
  acc-last (Scan.acc₀ x _)            = z , _ , x , refl
  acc-last (Scan.acc {b = b} _ x _ _) = b , _ , x , refl

  fine : ∀ {y e} → enter (Op.map proj₂ (Op.scan laneStep z d)) p y (out e) → Fine e y
  fine (map-out (Scan.sval ac , _) , _) with acc-last ac
  ... | st′ , x , tq , refl = tell-fine (proj₁ st′) x (Fit.fine F tq)

  ends : ∀ {y} → enter (Op.map proj₂ (Op.scan laneStep z d)) p y end → Early y
  ends (map-end (Scan.send t , _) , _) = Fit.ends F t

  placed : Placed Fr (enter (Op.map proj₂ (Op.scan laneStep z d)) p)
  placed {e = out _} (map-out (Scan.sval ac , _) , _) sh with acc-last ac
  ... | st′ , x , tq , refl = Fit.placed F tq (tell-shown (proj₁ st′) x sh)
  placed {e = end}   (map-end (Scan.send t , _) , _) _ = Fit.placed F t s-end

counted-fit : ∀ {B H Fr} {z : Routes × IE B} {d : Den (IE B)} → FitD H Fr d → FitD H Fr (Op.map proj₂ (Op.scan laneStep z d))
counted-fit {z = z} {d} Fd p ok fp ep =
  fit (CountedFit.fine z d Fd p ok fp ep) (CountedFit.ends z d Fd p ok fp ep) (CountedFit.placed z d Fd p ok fp ep)

-- An `each` that tells nothing, over a lawful hot: it ends where the
-- hot does, or where it is subscribed.
block-fit : ∀ {X B : Set} {Fr} (t : EmissionSet X) → Lawful t → EndsEarly t → (∀ {c} → t c end → Fr c)
          → ∀ {H} → Adm H Fr → FitD H Fr (Op.flatMap (mergeᶠ nothing) (λ (_ : X) → Op.of ([] {A = IE B})) (hot t))
block-fit {Fr = Fr} t L te tf ad p _ fp ep = fit fine (λ r → proj₁ (EE r)) placed
  where
    EE : ∀ {c} → enter (Op.flatMap (mergeᶠ nothing) (λ _ → Op.of []) (hot t)) p c end → Early c × Fr c
    EE = EachEnd.each-end (λ _ → []) t L (λ c → Early c × Fr c) (λ (e , f) l nl → early-inst [ l ] e , Adm.bare ad f nl)
                          (λ y → te y , tf y) p (ep , fp)
    none : ∀ {y x} → enter (Op.flatMap (mergeᶠ nothing) (λ _ → Op.of []) (hot t)) p y (out x) → ⊥
    none r with merge-out (λ _ → Op.of []) (hot t) p r
    ... | _ , _ , _ , l , _ with of-mem _ 0 [] (proj₁ l)
    ...   | ()
    fine : ∀ {y x} → enter (Op.flatMap (mergeᶠ nothing) (λ _ → Op.of []) (hot t)) p y (out x) → Fine x y
    fine r = ⊥-elim (none r)
    placed : Placed Fr (enter (Op.flatMap (mergeᶠ nothing) (λ _ → Op.of []) (hot t)) p)
    placed {e = out _} r _ = ⊥-elim (none r)
    placed {e = end}   r _ = proj₂ (EE r)

val-of : ∀ {N A : Set} {x : InstEmit N A} {a} → a ∈ valuesOf x → Σ N λ n → x ≡ instEmit (value a) n
val-of {x = instEmit (value _) n} (here refl) = n , refl
val-of {x = instEmit (value _) _} (there ())
val-of {x = instEmit (mark _) _}  ()

-- THE OUTER'S VALUES, read through a hot: each at a value row of it.
vals-early : ∀ {A H Fr} (t : EmissionSet (IE A)) → Lawful t → InvD H (hot t) → Adm H Fr
           → (∀ {r b n} → t r (out (instEmit (value b) n)) → Early r) → EndsEarly t → Placed Fr t
           → ∀ p → Ok H p → Fr p → Early p → Outer Fr (enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (valuesOf x)) (hot t)) p)
vals-early {Fr = Fr} t L It ad tv te tp p ok fp ep = (λ r → proj₁ (row r)) , (λ r → proj₁ (EE r)) , fr
  where
    EE : ∀ {c} → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (valuesOf x)) (hot t)) p c end → Early c × Fr c
    EE = EachEnd.each-end valuesOf t L (λ c → Early c × Fr c) (λ (e , f) l nl → early-inst [ l ] e , Adm.bare ad f nl)
                          (λ y → te y , tp y s-end) p (ep , fp)
    row : ∀ {q a} → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (valuesOf x)) (hot t)) p q (out a) → Early q × Fr q
    row r with merge-out (λ x → Op.of (valuesOf x)) (hot t) p r
    ... | k , x , hk , l , _ with hot-out hk
    ...   | r₀ , tr , _ , refl with of-at ((r₀ ⊕ [ sub p ]) ⊕ [ ix 1 ]) 0 (valuesOf x) (proj₁ l) | val-of (of-mem _ 0 (valuesOf x) (proj₁ l))
    ...     | l₀ , refl | _ , refl =
      early-inst [ l₀ ] (early-inst [ ix 1 ] (early-inst [ sub p ] (tv tr))) ,
      adm-at ad (ok-ix _ okk) (Adm.step ad okk (Adm.copy ad (tp tr s-value)) plain-ix) l₀
      where
        okk = ok-in ok (InvAt.world (It p ok) hk) (InvAt.real (It p ok) hk)
    fr : ∀ {q e} → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (valuesOf x)) (hot t)) p q e → Visible e → Fr q
    fr {e = out _} r _ = proj₂ (row r)
    fr {e = end}   r _ = proj₂ (EE r)

-- A lane's `takeWhile` fails only at its own `laneDone`.
undone-done : ∀ {B} {x : IE B} → T (not (undone x)) → Done x
undone-done {x = instEmit (mark (laneDone _)) _} _ = done
undone-done  {x = instEmit (value _) _}         ()
undone-done  {x = instEmit (mark begin) _}      ()
undone-done  {x = instEmit (mark over) _}       ()
undone-done  {x = instEmit (mark stop) _}       ()
undone-done  {x = instEmit (mark subscribed) _} ()
undone-done  {x = instEmit (mark completed) _}  ()
undone-done  {x = instEmit (mark outerOpen) _}  ()
undone-done  {x = instEmit (mark outerClose) _} ()
undone-done  {x = instEmit (mark laneStart) _}  ()
undone-done  {x = instEmit (mark burstEnd) _}   ()
undone-done  {x = instEmit (mark outerDone) _}  ()

undone-fails : ∀ {B} {x : IE B} {y} → T (not (undone x)) → Fine x y → Early y
undone-fails nd f with undone-done nd
... | done = f

undone-shown : ∀ {B} {x : IE B} → T (not (undone x)) → Shown (out x)
undone-shown nd with undone-done nd
... | done = s-done

------------------------------------------------------------------------
-- Under every approximant as under the meaning

flatE : ∀ m {Γ A B Fr} op (g : A → Obs Timeline Γ (IE B)) s (ρ : DenEnv Γ) → GoodEnv ρ → Adm (Hots ρ) Fr
      → (∀ a → FitD (Hots ρ) Fr (ev m (g a) ρ))
      → (∀ p → Ok (Hots ρ) p → Fr p → Early p → Outer Fr (enter (ev m s ρ) p))
      → FitD (Hots ρ) Fr (ev m (flatMap op g s) ρ)
flatE nothing  op g s ρ gd ad Ff od =
  flat-fitD op {f = λ a → ev nothing (g a) ρ} {d = ev nothing s ρ} ad (inv-ev nothing s ρ gd) (λ a → inv-ev nothing (g a) ρ gd) Ff od
flatE (just n) op g s ρ gd ad Ff od =
  flat-fitD op {f = λ a → ev (just n) (g a) ρ} {d = ev (just n) s ρ} ad (inv-ev (just n) s ρ gd) (λ a → inv-ev (just n) (g a) ρ gd) Ff od

takeE : ∀ m {Γ B} i keep (s : Obs Timeline Γ (IE B)) (ρ : DenEnv Γ) {H Fr} → Adm H Fr → (∀ {x y} → T (not (keep x)) → Fine x y → Early y)
      → (∀ {x} → T (not (keep x)) → Shown (out x)) → FitD H Fr (ev m s ρ) → FitD H Fr (ev m (takeWhile i keep s) ρ)
takeE nothing  i keep s ρ ad fe fs F = take-fit i keep {d = ev nothing s ρ} ad fe fs F
takeE (just n) i keep s ρ ad fe fs F = take-fit i keep {d = ev (just n) s ρ} ad fe fs F

connE : ∀ m {Γ X B Fr} (Q : EmissionSet X → Set) (s : Obs Timeline Γ X) (b : Obs Timeline (X ∷ Γ) (IE B)) (ρ : DenEnv Γ) → GoodEnv ρ
      → Adm (Hots ρ) Fr
      → (∀ p → Ok (Hots ρ) p → Fr p → Early p → Q (Proper (enter (ev m s ρ) (p ⊕ [ ix 1 ]))))
      → (∀ {t} → Lawful t → Q t → FitD (Hots (hot t ∷ ρ)) Fr (ev m b (hot t ∷ ρ)))
      → FitD (Hots ρ) Fr (ev m (connect s b) ρ)
connE nothing  Q s b ρ g ad Qs LF =
  conn-fit Q {s = ev nothing s ρ} {F = λ h → ev nothing b (h ∷ ρ)} ad (inv-ev nothing s ρ g) (λ L → inv-ev nothing b (hot _ ∷ ρ) (good-cons L g)) Qs LF
connE (just n) Q s b ρ g ad Qs LF =
  conn-fit Q {s = ev (just n) s ρ} {F = λ h → ev (just n) b (h ∷ ρ)} ad (inv-ev (just n) s ρ g) (λ L → inv-ev (just n) b (hot _ ∷ ρ) (good-cons L g)) Qs LF

ofE : ∀ m {Γ B} (xs : List (IE B)) (ρ : DenEnv Γ) {H Fr} → Adm H Fr → (∀ {x y} → x ∈ xs → Early y → Fine x y) → FitD H Fr (ev m (of xs) ρ)
ofE nothing  xs ρ ad h = of-fit xs h ad
ofE (just n) xs ρ ad h = of-fit xs h ad

of-outer : ∀ m {Γ X H Fr} (xs : List X) (ρ : DenEnv Γ) → Adm H Fr → ∀ p → Ok H p → Fr p → Early p → Outer Fr (enter (ev m (of xs) ρ) p)
of-outer nothing  xs ρ ad = of-early xs ad
of-outer (just n) xs ρ ad = of-early xs ad

emptyE : ∀ m {Γ B} (ρ : DenEnv Γ) {H Fr} → Adm H Fr → FitD H Fr (ev m (empty {A = IE B}) ρ)
emptyE nothing  ρ ad = empty-fit ad
emptyE (just n) ρ ad = empty-fit ad

-- An `empty`'s end, under its subscription.
empty-ends : ∀ m {Γ X H Fr} (ρ : DenEnv Γ) → Adm H Fr → ∀ p → Early p → Fr p
           → EndsEarly (Proper (enter (ev m (empty {A = X}) ρ) p)) × (∀ {c} → Proper (enter (ev m (empty {A = X}) ρ) p) c end → Fr c)
empty-ends nothing  ρ ad p ep fp = (λ { ((at-end , _) , _) → early-inst [ last ] ep }) , (λ { ((at-end , _) , _) → Adm.bare ad fp λ () })
empty-ends (just n) ρ ad p ep fp = (λ { ((at-end , _) , _) → early-inst [ last ] ep }) , (λ { ((at-end , _) , _) → Adm.bare ad fp λ () })

hotE : ∀ m {Θ B} (t : EmissionSet (IE B)) (env : DenEnv Θ) {H Fr} → Adm H Fr → FitH Fr t → FitD H Fr (ev m (connected (here refl)) (hot t ∷ env))
hotE nothing  t env ad F = hot-fit F ad
hotE (just n) t env ad F = hot-fit F ad

blockE : ∀ m {Θ B} (t : EmissionSet ⊤) (env : DenEnv Θ) {H Fr} → Adm H Fr → Lawful t → EndsEarly t → (∀ {c} → t c end → Fr c)
       → FitD H Fr (ev m (blockˢ {Θ} {IE B}) (hot t ∷ env))
blockE nothing  t env ad L te tf = block-fit t L te tf ad
blockE (just n) t env ad L te tf = block-fit t L te tf ad

countedE : ∀ m {Γ B} (s : Obs Timeline Γ (IE B)) (ρ : DenEnv Γ) {H Fr} → Adm H Fr → InvD H (ev m s ρ) → FitD H Fr (ev m s ρ)
         → FitD H Fr (ev m (counted s) ρ)
countedE nothing  s ρ ad I F = counted-fit {d = ev nothing s ρ} F
countedE (just n) s ρ ad I F = counted-fit {d = ev (just n) s ρ} F

each-vals : ∀ m {Θ A B Fr} (t₂ : EmissionSet (IE B)) (t₁ : EmissionSet (IE A)) (env₀ : DenEnv Θ) → GoodEnv (hot t₂ ∷ hot t₁ ∷ env₀)
          → Lawful t₁ → Adm (Hots (hot t₂ ∷ hot t₁ ∷ env₀)) Fr
          → (∀ {r b n} → t₁ r (out (instEmit (value b) n)) → Early r) → EndsEarly t₁ → Placed Fr t₁
          → ∀ p → Ok (Hots (hot t₂ ∷ hot t₁ ∷ env₀)) p → Fr p → Early p
          → Outer Fr (enter (ev m (each valuesOf (connected (there (here refl)))) (hot t₂ ∷ hot t₁ ∷ env₀)) p)
each-vals nothing  t₂ t₁ env₀ g L ad tv te tp =
  vals-early t₁ L (inv-ev nothing (connected (there (here refl))) (hot t₂ ∷ hot t₁ ∷ env₀) g) ad tv te tp
each-vals (just n) t₂ t₁ env₀ g L ad tv te tp =
  vals-early t₁ L (inv-ev (just n) (connected (there (here refl))) (hot t₂ ∷ hot t₁ ∷ env₀) g) ad tv te tp

-- A frame's pieces: its own marks, and the shared lane between them.
pieceE : ∀ m {Θ B Fr} k i (tC : EmissionSet (IE B)) → FitH Fr tC → (env : DenEnv Θ) → Adm (Hots (hot tC ∷ env)) Fr
       → FitD (Hots (hot tC ∷ env)) Fr (ev m (piece {Θ} {B} k i) (hot tC ∷ env))
pieceE m lanePart  0                   tC FC env ad = ofE m _ _ ad (lone-early (λ e → e))
pieceE m burstPart 0                   tC FC env ad = ofE m _ _ ad (lone-early (λ e → e))
pieceE m lanePart  1                   tC FC env ad = hotE m tC env ad FC
pieceE m burstPart 1                   tC FC env ad = hotE m tC env ad FC
pieceE m lanePart  2                   tC FC env ad = ofE m _ _ ad (lone-early (λ e → e))
pieceE m burstPart 2                   tC FC env ad = emptyE m _ ad
pieceE m lanePart  (suc (suc (suc _))) tC FC env ad = emptyE m _ ad
pieceE m burstPart (suc (suc (suc _))) tC FC env ad = emptyE m _ ad

framedE : ∀ m {Θ B Fr} k (tC : EmissionSet (IE B)) → FitH Fr tC → (env : DenEnv Θ) → GoodEnv (hot tC ∷ env) → Adm (Hots (hot tC ∷ env)) Fr
        → FitD (Hots (hot tC ∷ env)) Fr (ev m (framed {Θ} {B} k) (hot tC ∷ env))
framedE m k tC FC env g ad = flatE m (mergeᶠ (just 1)) (piece k) (of (0 ∷ 1 ∷ 2 ∷ [])) (hot tC ∷ env) g ad (λ i → pieceE m k i tC FC env ad)
  (of-outer m _ _ ad)

------------------------------------------------------------------------
-- The real flatMap

-- THE REAL FLATMAP'S ROWS FIT: each lane's, a frame's mark or a row of
-- the program it shares, the outer's ends and its lanes' before their
-- step's over, and every row a lane can hang on admissible, given the
-- outer's.
module LaneReal (m : Maybe ℕ) {Γ Θ A B} {Fr : Pos → Set} (op : FlatOp) (f : A → Obs Timeline Γ B)
                (ρ₄ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ ⊤ ∷ IE B ∷ IE A ∷ Θ)
                (t₂ : EmissionSet (IE B)) (t₁ : EmissionSet (IE A)) (env₀ : DenEnv Θ)
                (g₂ : GoodEnv (hot t₂ ∷ hot t₁ ∷ env₀)) (L₁ : Lawful t₁)
                (tv : ∀ {r b n} → t₁ r (out (instEmit (value b) n)) → Early r) (te : EndsEarly t₁) (tp : Placed Fr t₁)
                (ad : Adm (Hots (hot t₂ ∷ hot t₁ ∷ env₀)) Fr)
                (inner : ∀ a {t} → Lawful t → FitD (Hots (hot t ∷ hot t₂ ∷ hot t₁ ∷ env₀)) Fr (ev m (elab ρ₄ (f a)) (hot t ∷ hot t₂ ∷ hot t₁ ∷ env₀))) where

  env₂ : DenEnv (IE B ∷ IE A ∷ Θ)
  env₂ = hot t₂ ∷ hot t₁ ∷ env₀

  x : A → Part → Bool → Obs Timeline (⊤ ∷ IE B ∷ IE A ∷ Θ) (IE B)
  x a k c = laneSrc ρ₄ (f a) k c

  -- A blocker's end: early and admissible.
  Blocks : EmissionSet ⊤ → Set
  Blocks t = EndsEarly t × (∀ {c} → t c end → Fr c)

  -- The shared program's two lanes: the blocker, then the program.
  srcE : ∀ a k (t : EmissionSet ⊤) → Lawful t → Blocks t → ∀ c → FitD (Hots (hot t ∷ env₂)) Fr (ev m (x a k c) (hot t ∷ env₂))
  srcE a lanePart  t L (tee , tef) true  = blockE m t env₂ (adm-∪ {t = t} ad) L tee tef
  srcE a burstPart t L (tee , tef) true  = blockE m t env₂ (adm-∪ {t = t} ad) L tee tef
  srcE a lanePart  t L _           false = inner a L
  srcE a burstPart t L _           false = emptyE m (hot t ∷ env₂) (adm-∪ {t = t} ad)

  C : A → Part → Obs Timeline (⊤ ∷ IE B ∷ IE A ∷ Θ) (IE B)
  C a k = flatMap (mergeᶠ (just 1)) (x a k) (of (true ∷ false ∷ []))

  CE : ∀ a k (t : EmissionSet ⊤) → Lawful t → Blocks t → FitD (Hots (hot t ∷ env₂)) Fr (ev m (C a k) (hot t ∷ env₂))
  CE a k t L tb = flatE m (mergeᶠ (just 1)) (x a k) (of (true ∷ false ∷ [])) (hot t ∷ env₂) (good-cons L g₂) (adm-∪ {t = t} ad) (srcE a k t L tb)
    (of-outer m _ _ (adm-∪ {t = t} ad))

  shareE : ∀ a k → FitD (Hots env₂) Fr (ev m (shareˢ (x a k) (counted (framed k))) env₂)
  shareE a k = connE m Blocks empty (connect (C a k) (counted (framed k))) env₂ g₂ ad
    (λ p ok fp ep → empty-ends m env₂ ad (p ⊕ [ ix 1 ]) (early-inst [ ix 1 ] ep) (Adm.step ad ok fp plain-ix))
    λ {t} L tb → connE m (FitH Fr) (C a k) (counted (framed k)) (hot t ∷ env₂) (good-cons L g₂) (adm-∪ {t = t} ad)
      (λ p ok fp ep → proper-fitH (CE a k t L tb (p ⊕ [ ix 1 ]) (ok-step p ok) (Adm.step (adm-∪ {t = t} ad) ok fp plain-ix) (early-inst [ ix 1 ] ep)))
      λ {tC} LC FC → countedE m (framed k) (hot tC ∷ hot t ∷ env₂) (adm-∪ {t = tC} (adm-∪ {t = t} ad))
                       (inv-ev m (framed k) _ (good-cons LC (good-cons L g₂)))
                       (framedE m k tC FC (hot t ∷ env₂) (good-cons LC (good-cons L g₂)) (adm-∪ {t = tC} (adm-∪ {t = t} ad)))

  laneE : ∀ a → FitD (Hots env₂) Fr (ev m (laneˢ (x a)) env₂)
  laneE a = takeE m true undone (flatMap (mergeᶠ nothing) (λ k → shareˢ (x a k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ []))) env₂
    ad undone-fails undone-shown
    (flatE m (mergeᶠ nothing) (λ k → shareˢ (x a k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ [])) env₂ g₂ ad (shareE a)
      (of-outer m _ _ ad))

  real : Obs Timeline (IE B ∷ IE A ∷ Θ) (IE B)
  real = flatMap op (λ a → laneˢ (x a)) (each valuesOf (connected (there (here refl))))

  realE : FitD (Hots env₂) Fr (ev m real env₂)
  realE = flatE m op (λ a → laneˢ (x a)) (each valuesOf (connected (there (here refl)))) env₂ g₂ ad laneE
    (each-vals m t₂ t₁ env₀ g₂ L₁ ad tv te tp)
