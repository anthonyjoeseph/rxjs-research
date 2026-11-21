{-# OPTIONS --guardedness #-}

-- WHAT A LANE'S ROWS HOLD, ONE BY ONE: a begin is named for its
-- instant, a value and an end lie before their step's over, an over at
-- it, and a lane's own marks before it too.  Each former the real
-- flatMap is built from keeps that, so its lanes do, given that the
-- programs they subscribe hold.
module simultaneous.LaneLocal where

open import Data.Bool using (Bool; true; false; T; not; if_then_else_)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; replicate)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; empty; of; takeWhile; flatMap; connect; connected)
open import denotation.Position using (Pos; Path; root; _≟ᵖ_; ix; sub; last; _⊕_)
open import denotation.Events using (Timeline; fresh; <ᵖ-apart)
open import denotation.EmissionSet using (EmissionSet; Den; hot; enter; Proper; DenEnv; out; end; _≺_; shown; ended; late; at-end;
  Superseded; module Op; module Joiner; module Bounded; module Values; module Merge;
  module Scan; module TakeWhile; module Exhaust; module Connecting)
open import denotation.Laws using (inv-⟦⟧; inv-approx; good-cons)
open import denotation.Laws.Connect using () renaming (lawful to src-lawful; ok₀ to body-ok)
open import denotation.Laws.Modulus using (≺-irrefl; ≼-split; ≼-or-≻)
open import denotation.Laws.Worlds using (Ok; InvD; InvAt; Lawful; Hots; GoodEnv; _∪ʰ_; ok-step; ok-in; ⊕-assoc; ⊕-identityʳ; ⊑-trans; _⊑_)
open import denotation.Laws.Worlds.Leaves using (of-end)
open import simultaneous.SObs using (lone; Part; lanePart; burstPart; module Elaborate)
open import simultaneous.InstEmit using (InstEmit; instEmit; value; mark; begin; over; stop; subscribed; completed; outerOpen; outerClose;
  laneStart; carry; laneDone; burstEnd; outerDone; valuesOf)
open import simultaneous.Routed using (Held; Early; Valued; opos; nameOf; nm)
open import simultaneous.Readings using (rootOf)
open import simultaneous.HeldComb using (ev)
open import simultaneous.HeldConnect using (early-inst; rootOf-ext)
open import simultaneous.DenRows using (merge-out; hot-out; of-mem; nth-row)
open import simultaneous.CombSent using (of-at; module EachEnd)
open import simultaneous.Layers using (pinby-vis)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone
  using (IE; AIE; Routes; elab; laneˢ; laneSrc; shareˢ; blockˢ; counted; framed; piece; laneStep; undone; each; marked)

-- Either reading is lawful.
inv-ev : ∀ m {Γ A} (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → InvD (Hots ρ) (ev m o ρ)
inv-ev nothing  o ρ g = inv-⟦⟧ o ρ g
inv-ev (just n) o ρ g = inv-approx n o ρ g

-- Past its over, a step is as late.
late-ext : ∀ {q} zs → Valued (rootOf q) × opos (rootOf q) ⊑ q
         → Valued (rootOf (q ⊕ zs)) × opos (rootOf (q ⊕ zs)) ⊑ (q ⊕ zs)
late-ext {q} zs (v , o) = subst (λ I → Valued I × opos I ⊑ (q ⊕ zs)) (sym (rootOf-ext q zs)) (v , ⊑-trans o (zs , refl))

------------------------------------------------------------------------
-- A row's own claim: an `outerOpen`, never, as no lane opens an outer.

Fine : ∀ {A} → IE A → Pos → Set
Fine (instEmit (value _) _)          y = Early y
Fine (instEmit (mark begin) n)       y = n ≡ nameOf y
Fine (instEmit (mark over) _)        y = Valued (rootOf y) × opos (rootOf y) ⊑ y
Fine (instEmit (mark laneStart) _)   y = Early y
Fine (instEmit (mark carry) _)       y = Early y
Fine (instEmit (mark laneDone) _)    y = Early y
Fine (instEmit (mark burstEnd) _)    y = Early y
Fine (instEmit (mark stop) _)        y = ⊤
Fine (instEmit (mark subscribed) _)  y = ⊤
Fine (instEmit (mark completed) _)   y = Early y
Fine (instEmit (mark outerOpen) _)   y = ⊥
Fine (instEmit (mark outerClose) _)  y = ⊤
Fine (instEmit (mark outerDone) _)   y = ⊤

-- Below a row, its claim holds as it did.
fine-ext : ∀ {A} (x : IE A) {y} zs → Fine x y → Fine x (y ⊕ zs)
fine-ext (instEmit (value _) _)         zs f = early-inst zs f
fine-ext (instEmit (mark begin) _) {y} zs f = trans f (cong nm (sym (rootOf-ext y zs)))
fine-ext (instEmit (mark over) _) {y} zs f = late-ext {y} zs f
fine-ext (instEmit (mark laneStart) _)  zs f = early-inst zs f
fine-ext (instEmit (mark carry) _)      zs f = early-inst zs f
fine-ext (instEmit (mark laneDone) _)   zs f = early-inst zs f
fine-ext (instEmit (mark burstEnd) _)   zs f = early-inst zs f
fine-ext (instEmit (mark stop) _)       zs f = tt
fine-ext (instEmit (mark subscribed) _) zs f = tt
fine-ext (instEmit (mark completed) _)  zs f = early-inst zs f
fine-ext (instEmit (mark outerOpen) _)  zs f = f
fine-ext (instEmit (mark outerClose) _) zs f = tt
fine-ext (instEmit (mark outerDone) _)  zs f = tt

-- EVERY ROW AS IT CLAIMS, and the end before its step's over.
record Fit {A} (t : EmissionSet (IE A)) : Set where
  constructor fit
  field
    fine : ∀ {y x} → t y (out x) → Fine x y
    ends : ∀ {y} → t y end → Early y

FitD : ∀ {A} → (Pos → Set) → Den (IE A) → Set
FitD H d = ∀ p → Ok H p → Early p → Fit (enter d p)

EndsEarly : ∀ {A} → EmissionSet A → Set
EndsEarly t = ∀ {c} → t c end → Early c

-- A hot's rows, wherever it is read.
FitH : ∀ {A} → EmissionSet (IE A) → Set
FitH t = (∀ {y x} → t y (out x) → Fine x y) × EndsEarly t

proper-fit : ∀ {A} {t : EmissionSet (IE A)} → Fit t → Fit (Proper t)
proper-fit F = fit (λ r → Fit.fine F (proj₁ r)) (λ r → Fit.ends F (proj₁ r))

proper-fitH : ∀ {A} {t : EmissionSet (IE A)} → Fit t → FitH (Proper t)
proper-fitH F = (λ r → Fit.fine F (proj₁ r)) , (λ r → Fit.ends F (proj₁ r))

-- A held stream fits: its marks are routing marks, never a lane's.
held-fit : ∀ {A} {t : EmissionSet (IE A)} {cs} → Held t cs → Fit t
held-fit {t = t} H = fit fine (Held.ends H)
  where
    fine : ∀ {y x} → t y (out x) → Fine x y
    fine {x = instEmit (value _) _}         r = Held.early H r
    fine {x = instEmit (mark begin) _}      r = Held.named H r
    fine {x = instEmit (mark over) _}       r = Held.late H r
    fine {x = instEmit (mark laneStart) _}  r with () ← Held.routing H r
    fine {x = instEmit (mark carry) _}      r with () ← Held.routing H r
    fine {x = instEmit (mark laneDone) _}   r with () ← Held.routing H r
    fine {x = instEmit (mark burstEnd) _}   r with () ← Held.routing H r
    fine {x = instEmit (mark stop) _}       r = tt
    fine {x = instEmit (mark subscribed) _} r = tt
    fine {x = instEmit (mark completed) _}  r = Held.done H r
    fine {x = instEmit (mark outerOpen) _}  r with () ← Held.routing H r
    fine {x = instEmit (mark outerClose) _} r = tt
    fine {x = instEmit (mark outerDone) _}  r = tt

------------------------------------------------------------------------
-- The leaves

hot-fit : ∀ {A} {t : EmissionSet (IE A)} → FitH t → ∀ {H} → FitD H (hot t)
hot-fit {t = t} (tf , te) p _ ep = fit fine ends
  where
    fine : ∀ {y x} → enter (hot t) p y (out x) → Fine x y
    fine {x = x} (shown y _ _ , _) = fine-ext x [ sub p ] (tf y)
    ends : ∀ {y} → enter (hot t) p y end → Early y
    ends (ended y _ , _)    = early-inst [ sub p ] (te y)
    ends (late _ _ , _)     = early-inst [ last ] ep
    ends (shown _ () _ , _)

of-fit : ∀ {A} (xs : List (IE A)) → (∀ {x y} → x ∈ xs → Early y → Fine x y) → ∀ {H} → FitD H (Op.of xs)
of-fit xs h p _ ep = fit fine ends
  where
    fine : ∀ {y x} → enter (Op.of xs) p y (out x) → Fine x y
    fine {x = x} (r , _) = let (l , eq) = of-at p 0 xs r in subst (Fine x) (sym eq) (h (of-mem p 0 xs r) (early-inst [ l ] ep))
    ends : ∀ {y} → enter (Op.of xs) p y end → Early y
    ends (r , _) = subst Early (sym (of-end p 0 xs r)) (early-inst [ last ] ep)

empty-fit : ∀ {A H} → FitD H (Op.empty {IE A})
empty-fit p _ ep = fit (λ { (() , _) }) (λ { (at-end , _) → early-inst [ last ] ep })

-- A lone lane mark lies before its step's over wherever it falls.
lone-early : ∀ {B} {x₀ : IE B} → (∀ {y} → Early y → Fine x₀ y) → ∀ {x y} → x ∈ (x₀ ∷ []) → Early y → Fine x y
lone-early h (here refl) e = h e
lone-early h (there ())

-- A value of `of` and its end lie at its subscription.
of-early : ∀ {X} (xs : List X) p → Early p
         → (∀ {q a} → enter (Op.of xs) p q (out a) → Early q) × EndsEarly (enter (Op.of xs) p)
of-early xs p ep =
  (λ (r , _) → let (l , eq) = of-at p 0 xs r in subst Early (sym eq) (early-inst [ l ] ep)) ,
  (λ (r , _) → subst Early (sym (of-end p 0 xs r)) (early-inst [ last ] ep))

-- No row lies under another, and none visible past the end: below a
-- row before the end lies nothing past it.
row-before-end : ∀ {A H p} {X : EmissionSet A} → InvAt H p X → ∀ {r c a} → X r (out a) → X c end → ∀ zs → (r ⊕ zs) ≺ c
row-before-end I {r} {c} x y zs = Equivalence.from T-≡ (<ᵖ-apart r c zs (Equivalence.to T-≡ r≺c) apart)
  where
    r≺c : r ≺ c
    r≺c with ≼-or-≻ r c
    ... | inj₂ cr = ⊥-elim (pinby-vis tt (InvAt.quiet I y x cr))
    ... | inj₁ rc with ≼-split {r} {c} rc
    ...   | inj₁ lt = lt
    ...   | inj₂ refl with () ← InvAt.func I x y
    apart : ∀ ys → c ≡ r ⊕ ys → ⊥
    apart []       eq   = ≺-irrefl {r} (subst (r ≺_) (trans eq (⊕-identityʳ r)) r≺c)
    apart (l ∷ ys) refl = InvAt.flat I x y

------------------------------------------------------------------------
-- A flatMap, under every policy

module FlatFit {A B : Set} {H : Pos → Set} (f : A → Den (IE B)) (d : Den A)
               (Id : InvD H d) (If : ∀ a → InvD H (f a)) (Ff : ∀ a → FitD H (f a))
               (p : Pos) (ok : Ok H p)
               (o-early : ∀ {q a} → enter d p q (out a) → Early q) (o-end : EndsEarly (enter d p)) where

  -- A value's lane, subscribed at its second child.
  val-fit : ∀ {q a} → enter d p q (out a) → Fit (enter (f a) (q ⊕ [ ix 1 ]))
  val-fit {q} {a} x =
    Ff a (q ⊕ [ ix 1 ]) (ok-step q (ok-in ok (InvAt.world (Id p ok) x) (InvAt.real (Id p ok) x))) (early-inst [ ix 1 ] (o-early x))

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

  -- A queued lane starts at an earlier lane's end, which fits.
  module Bd (n : ℕ) where
    open Values (enter d p) using (Nth)
    open Bounded n f (enter d p)

    mutual
      start-at : ∀ i {q a s} → Nth i q a → Starts i q (Sched i) s → Early s × Ok H s
      start-at i {q} N (room _) =
        early-inst [ ix 1 ] (o-early (nth-row N)) ,
        ok-step q (ok-in ok (InvAt.world (Id p ok) (nth-row N)) (InvAt.real (Id p ok) (nth-row N)))
      start-at i {q} N (freed _ _) =
        early-inst [ ix 1 ] (o-early (nth-row N)) ,
        ok-step q (ok-in ok (InvAt.world (Id p ok) (nth-row N)) (InvAt.real (Id p ok) (nth-row N)))
      start-at i N (queued {c} _ _ one _ _) =
        let (ec , okc) = sched-at i one in early-inst [ ix 1 ] ec , ok-step c okc

      sched-at : ∀ i {c} → Kth (_≡ c) (Sched i) 0 → Early c × Ok H c
      sched-at zero ()
      sched-at (suc i) (inj₁ (_ , (_ , _ , _ , N , St , (y , _)) , refl)) = end-at i N St y
      sched-at (suc i) (inj₂ k) = sched-at i k

      end-at : ∀ i {q a s c} → Nth i q a → Starts i q (Sched i) s → enter (f a) s c end → Early c × Ok H c
      end-at i {a = a} {s} N St y =
        let (es , oks) = start-at i N St in
        Fit.ends (Ff a s oks es) y , ok-in oks (InvAt.world (If a s oks) y) (InvAt.real (If a s oks) y)

    fine : ∀ {y x} → JoinT y (out x) → Fine x y
    fine (lane _ _ (i , s , (N , St) , (l , _)) _ _) = let (es , oks) = start-at i N St in Fit.fine (Ff _ s oks es) l
    fine (run () _)

    ends : ∀ {y} → JoinT y end → Early y
    ends (oend o _)                                     = o-end o
    ends (lane _ _ _ _ ())
    ends (lend _ _ (i , s , (N , St) , (l , _)) _ _ _)  = proj₁ (end-at i N St l)
    ends (run () _)
    ends (rend () _ _)

  flat-fit : ∀ op → Fit (enter (Op.flatMap op f d) p)
  flat-fit (mergeᶠ nothing)  = fit (λ (j , _) → J.fine (λ _ → ⊤) (λ _ _ → ⊥) j) (λ (j , _) → J.ends (λ _ → ⊤) (λ _ _ → ⊥) j)
  flat-fit (mergeᶠ (just n)) = fit (λ (j , _) → Bd.fine n j) (λ (j , _) → Bd.ends n j)
  flat-fit switchᶠ           = fit (λ (j , _) → J.fine (λ _ → ⊤) (Superseded (enter d p)) j)
                                   (λ (j , _) → J.ends (λ _ → ⊤) (Superseded (enter d p)) j)
  flat-fit exhaustᶠ          = fit (λ (j , _) → J.fine (Exhaust.Run f (enter d p)) (λ _ _ → ⊥) j)
                                   (λ (j , _) → J.ends (Exhaust.Run f (enter d p)) (λ _ _ → ⊥) j)

flat-fitD : ∀ {A B : Set} {H} op {f : A → Den (IE B)} {d : Den A} → InvD H d → (∀ a → InvD H (f a)) → (∀ a → FitD H (f a))
          → (∀ p → Ok H p → Early p → (∀ {q a} → enter d p q (out a) → Early q) × EndsEarly (enter d p))
          → FitD H (Op.flatMap op f d)
flat-fitD op {f} {d} Id If Ff od p ok ep = FlatFit.flat-fit f d Id If Ff p ok (proj₁ (od p ok ep)) (proj₂ (od p ok ep)) op

------------------------------------------------------------------------
-- A takeWhile, a connect, a lane's count

take-fit : ∀ {A H} i keep {d : Den (IE A)} → (∀ {x y} → T (not (keep x)) → Fine x y → Early y) → FitD H d → FitD H (Op.takeWhile i keep d)
take-fit i keep {d} fe Fd p ok ep = fit fine ends
  where
    F = Fd p ok ep
    fine : ∀ {y x} → enter (Op.takeWhile i keep d) p y (out x) → Fine x y
    fine (TakeWhile.pass t _ _ , _)         = Fit.fine F t
    fine (TakeWhile.fail {a = a} t _ _ _ , _) = fine-ext a [ ix 0 ] (Fit.fine F t)
    ends : ∀ {y} → enter (Op.takeWhile i keep d) p y end → Early y
    ends (TakeWhile.stop t nk _ , _) = early-inst [ last ] (fe nk (Fit.fine F t))
    ends (TakeWhile.tend t _ , _)    = Fit.ends F t

-- A CONNECT SHOWS ITS BODY, read over the source made hot: what the
-- body fits, given what the source's rows give it.
conn-fit : ∀ {A B H} (Q : EmissionSet A → Set) {s : Den A} {F : Den A → Den (IE B)}
           (Is : InvD H s) (IF : ∀ {t} → Lawful t → InvD (H ∪ʰ t) (F (hot t)))
         → (∀ p → Ok H p → Early p → Q (Proper (enter s (p ⊕ [ ix 1 ])))) → (∀ {t} → Lawful t → Q t → FitD (H ∪ʰ t) (F (hot t)))
         → FitD H (Op.connect s F)
conn-fit Q {s} {F} Is IF Qs LF p ok ep = fit (λ { (Connecting.body x , _) → Fit.fine Fb x }) (λ { (Connecting.body x , _) → Fit.ends Fb x })
  where
    Fb : Fit (enter (F (hot (Proper (enter s (p ⊕ [ ix 1 ]))))) (p ⊕ [ ix 0 ]))
    Fb = LF (src-lawful {s = s} {F = F} Is IF p ok) (Qs p ok ep) (p ⊕ [ ix 0 ]) (body-ok {s = s} {F = F} Is IF p ok) (early-inst [ ix 0 ] ep)

rep-mem : ∀ {X : Set} k {e x : X} → e ∈ replicate k x → e ≡ x
rep-mem (suc k) (here refl) = refl
rep-mem (suc k) (there m)   = rep-mem k m

-- What a lane tells of a row: the row, or at its `laneDone` the carries.
told-fine : ∀ {B} st (x : IE B) b {e y} → e ∈ (if b then proj₁ (proj₂ (laneStep st x)) else proj₂ (proj₂ (laneStep st x)))
          → Fine x y → Fine e y
told-fine st (instEmit (mark laneDone) _) true  m f with rep-mem (proj₂ (proj₁ st)) m
... | refl = f
told-fine st (instEmit (mark laneDone) _) false (here refl) f = f
told-fine st (instEmit (mark laneDone) _) false (there ())
told-fine st (instEmit (value _) _)         true  ()
told-fine st (instEmit (value _) _)         false (here refl) f = f
told-fine st (instEmit (value _) _)         false (there ())
told-fine st (instEmit (mark begin) _)      true  ()
told-fine st (instEmit (mark begin) _)      false (here refl) f = f
told-fine st (instEmit (mark begin) _)      false (there ())
told-fine st (instEmit (mark over) _)       true  ()
told-fine st (instEmit (mark over) _)       false (here refl) f = f
told-fine st (instEmit (mark over) _)       false (there ())
told-fine st (instEmit (mark stop) _)       true  ()
told-fine st (instEmit (mark stop) _)       false (here refl) f = f
told-fine st (instEmit (mark stop) _)       false (there ())
told-fine st (instEmit (mark subscribed) _) true  ()
told-fine st (instEmit (mark subscribed) _) false (here refl) f = f
told-fine st (instEmit (mark subscribed) _) false (there ())
told-fine st (instEmit (mark completed) _)  true  ()
told-fine st (instEmit (mark completed) _)  false (here refl) f = f
told-fine st (instEmit (mark completed) _)  false (there ())
told-fine st (instEmit (mark outerOpen) _)  true  ()
told-fine st (instEmit (mark outerOpen) _)  false (here refl) f = f
told-fine st (instEmit (mark outerOpen) _)  false (there ())
told-fine st (instEmit (mark outerClose) _) true  ()
told-fine st (instEmit (mark outerClose) _) false (here refl) f = f
told-fine st (instEmit (mark outerClose) _) false (there ())
told-fine st (instEmit (mark laneStart) _)  true  ()
told-fine st (instEmit (mark laneStart) _)  false (here refl) f = f
told-fine st (instEmit (mark laneStart) _)  false (there ())
told-fine st (instEmit (mark carry) _)      true  ()
told-fine st (instEmit (mark carry) _)      false (here refl) f = f
told-fine st (instEmit (mark carry) _)      false (there ())
told-fine st (instEmit (mark burstEnd) _)   true  ()
told-fine st (instEmit (mark burstEnd) _)   false (here refl) f = f
told-fine st (instEmit (mark burstEnd) _)   false (there ())
told-fine st (instEmit (mark outerDone) _)  true  ()
told-fine st (instEmit (mark outerDone) _)  false (here refl) f = f
told-fine st (instEmit (mark outerDone) _)  false (there ())

-- Two `of` lanes over two values end under their subscription.
pair-under : ∀ {X : Set} (F : Bool → List X) s {c}
           → enter (Op.flatMap (mergeᶠ nothing) (λ b → Op.of (F b)) (Op.of (true ∷ false ∷ []))) s c end → Σ Path λ zs → c ≡ s ⊕ zs
pair-under F s (Merge.oend o _ , _) = [ last ] , of-end s 0 (true ∷ false ∷ []) (proj₁ o)
pair-under F s (Merge.lane _ _ _ _ () , _)
pair-under F s (Merge.lend {q} {b} o _ (l , _) _ _ _ , _) with of-at s 0 (true ∷ false ∷ []) (proj₁ o)
... | l₀ , refl = l₀ ∷ ix 1 ∷ last ∷ [] ,
  trans (of-end ((s ⊕ [ l₀ ]) ⊕ [ ix 1 ]) 0 (F b) (proj₁ l))
        (trans (cong (_⊕ [ last ]) (⊕-assoc s [ l₀ ] [ ix 1 ])) (⊕-assoc s (l₀ ∷ ix 1 ∷ []) [ last ]))
pair-under F s (Merge.run () _ , _)
pair-under F s (Merge.rend () _ _ , _)

-- A LANE'S COUNT SHOWS ITS ROWS: each at its row, or a carry beside it.
module CountedFit {B : Set} {H : Pos → Set} (z : Routes × (List (IE B) × List (IE B))) (d : Den (IE B))
                  (Id : InvD H d) (Fd : FitD H d) (p : Pos) (ok : Ok H p) (ep : Early p) where

  Lanes : Routes × (List (IE B) × List (IE B)) → Den (IE B)
  Lanes x = Op.flatMap (mergeᶠ nothing) (λ b → Op.of (if b then proj₁ (proj₂ x) else proj₂ (proj₂ x))) (Op.of (true ∷ false ∷ []))

  S : EmissionSet (Routes × (List (IE B) × List (IE B)))
  S = enter (Op.scan laneStep z d) p

  F = Fd p ok ep

  acc-last : ∀ {q st} → Scan.Acc laneStep z (enter d p) q st → Σ _ λ st′ → Σ (IE B) λ x → enter d p q (out x) × st ≡ laneStep st′ x
  acc-last (Scan.acc₀ x _)            = z , _ , x , refl
  acc-last (Scan.acc {b = b} _ x _ _) = b , _ , x , refl

  fine : ∀ {y e} → enter (Op.flatMap (mergeᶠ nothing) Lanes (Op.scan laneStep z d)) p y (out e) → Fine e y
  fine {e = e} r with merge-out Lanes (Op.scan laneStep z d) p r
  ... | q , st , (Scan.sval ac , _) , l , _
    with merge-out (λ b → Op.of (if b then proj₁ (proj₂ st) else proj₂ (proj₂ st))) (Op.of (true ∷ false ∷ [])) (q ⊕ [ ix 1 ]) l
  ...   | q₂ , b , (o₂ , _) , l₂ , _ with of-at (q ⊕ [ ix 1 ]) 0 (true ∷ false ∷ []) o₂ | of-at (q₂ ⊕ [ ix 1 ]) 0 _ (proj₁ l₂)
  ...     | l₀ , refl | l₁ , refl with acc-last ac
  ...       | st′ , x , tq , refl =
    fine-ext e [ l₁ ] (fine-ext e [ ix 1 ] (fine-ext e [ l₀ ] (fine-ext e [ ix 1 ]
      (told-fine st′ x b (of-mem _ 0 _ (proj₁ l₂)) (Fit.fine F tq)))))

  ends : ∀ {y} → enter (Op.flatMap (mergeᶠ nothing) Lanes (Op.scan laneStep z d)) p y end → Early y
  ends (Merge.oend (Scan.send t , _) _ , _) = Fit.ends F t
  ends (Merge.lane _ _ _ _ () , _)
  ends (Merge.lend {q} (Scan.sval ac , _) _ (l , _) _ _ ((c₀ , (Scan.send t₀ , _) , c₀c) , _) , _)
    with acc-last ac | pair-under _ (q ⊕ [ ix 1 ]) l
  ... | _ , _ , tq , _ | zs , refl = ⊥-elim (c₀c (subst (_≺ c₀) (sym (⊕-assoc q [ ix 1 ] zs)) (row-before-end (Id p ok) tq t₀ (ix 1 ∷ zs))))
  ends (Merge.run () _ , _)
  ends (Merge.rend () _ _ , _)

counted-fit : ∀ {B H} {z : Routes × (List (IE B) × List (IE B))} {d : Den (IE B)} → InvD H d → FitD H d
            → FitD H (Op.flatMap (mergeᶠ nothing)
                        (λ x → Op.flatMap (mergeᶠ nothing) (λ b → Op.of (if b then proj₁ (proj₂ x) else proj₂ (proj₂ x))) (Op.of (true ∷ false ∷ [])))
                        (Op.scan laneStep z d))
counted-fit {z = z} {d} Id Fd p ok ep = fit (CountedFit.fine z d Id Fd p ok ep) (CountedFit.ends z d Id Fd p ok ep)

-- An `each` that tells nothing, over a lawful hot: it ends where the
-- hot does, or where it is subscribed.
block-fit : ∀ {X B : Set} (t : EmissionSet X) → Lawful t → EndsEarly t → ∀ {H} → FitD H (Op.flatMap (mergeᶠ nothing) (λ (_ : X) → Op.of ([] {A = IE B})) (hot t))
block-fit t L te p _ ep = fit fine (λ r → EachEnd.each-end (λ _ → []) t L Early (λ e zs → early-inst zs e) te p ep r)
  where
    fine : ∀ {y x} → enter (Op.flatMap (mergeᶠ nothing) (λ _ → Op.of []) (hot t)) p y (out x) → Fine x y
    fine r with merge-out (λ _ → Op.of []) (hot t) p r
    ... | _ , _ , _ , l , _ with of-mem _ 0 [] (proj₁ l)
    ...   | ()

val-of : ∀ {N A : Set} {x : InstEmit N A} {a} → a ∈ valuesOf x → Σ N λ n → x ≡ instEmit (value a) n
val-of {x = instEmit (value _) n} (here refl) = n , refl
val-of {x = instEmit (value _) _} (there ())
val-of {x = instEmit (mark _) _}  ()

-- THE OUTER'S VALUES, read through a hot: each at a value row of it.
vals-early : ∀ {A} (t : EmissionSet (IE A)) → Lawful t → (∀ {r b n} → t r (out (instEmit (value b) n)) → Early r) → EndsEarly t
           → ∀ p → Early p → (∀ {q a} → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (valuesOf x)) (hot t)) p q (out a) → Early q)
                           × EndsEarly (enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (valuesOf x)) (hot t)) p)
vals-early t L tv te p ep = row , (λ r → EachEnd.each-end valuesOf t L Early (λ e zs → early-inst zs e) te p ep r)
  where
    row : ∀ {q a} → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (valuesOf x)) (hot t)) p q (out a) → Early q
    row r with merge-out (λ x → Op.of (valuesOf x)) (hot t) p r
    ... | k , x , hk , l , _ with hot-out hk
    ...   | r₀ , tr , _ , refl with of-at ((r₀ ⊕ [ sub p ]) ⊕ [ ix 1 ]) 0 (valuesOf x) (proj₁ l) | val-of (of-mem _ 0 (valuesOf x) (proj₁ l))
    ...     | l₀ , refl | _ , refl = early-inst [ l₀ ] (early-inst [ ix 1 ] (early-inst [ sub p ] (tv tr)))

-- A lane's `takeWhile` fails only at its own `laneDone`.
undone-fails : ∀ {B} {x : IE B} {y} → T (not (undone x)) → Fine x y → Early y
undone-fails {x = instEmit (mark laneDone) _}   _ f = f
undone-fails {x = instEmit (value _) _}         ()
undone-fails {x = instEmit (mark begin) _}      ()
undone-fails {x = instEmit (mark over) _}       ()
undone-fails {x = instEmit (mark stop) _}       ()
undone-fails {x = instEmit (mark subscribed) _} ()
undone-fails {x = instEmit (mark completed) _}  ()
undone-fails {x = instEmit (mark outerOpen) _}  ()
undone-fails {x = instEmit (mark outerClose) _} ()
undone-fails {x = instEmit (mark laneStart) _}  ()
undone-fails {x = instEmit (mark carry) _}      ()
undone-fails {x = instEmit (mark burstEnd) _}   ()
undone-fails {x = instEmit (mark outerDone) _}  ()

------------------------------------------------------------------------
-- Under every approximant as under the meaning

flatE : ∀ m {Γ A B} op (F : A → Obs Timeline Γ (IE B)) s (ρ : DenEnv Γ) → GoodEnv ρ → (∀ a → FitD (Hots ρ) (ev m (F a) ρ))
      → (∀ p → Ok (Hots ρ) p → Early p → (∀ {q a} → enter (ev m s ρ) p q (out a) → Early q) × EndsEarly (enter (ev m s ρ) p))
      → FitD (Hots ρ) (ev m (flatMap op F s) ρ)
flatE nothing  op F s ρ g Ff od =
  flat-fitD op {f = λ a → ev nothing (F a) ρ} {d = ev nothing s ρ} (inv-ev nothing s ρ g) (λ a → inv-ev nothing (F a) ρ g) Ff od
flatE (just n) op F s ρ g Ff od =
  flat-fitD op {f = λ a → ev (just n) (F a) ρ} {d = ev (just n) s ρ} (inv-ev (just n) s ρ g) (λ a → inv-ev (just n) (F a) ρ g) Ff od

takeE : ∀ m {Γ B} i keep (s : Obs Timeline Γ (IE B)) (ρ : DenEnv Γ) {H} → (∀ {x y} → T (not (keep x)) → Fine x y → Early y)
      → FitD H (ev m s ρ) → FitD H (ev m (takeWhile i keep s) ρ)
takeE nothing  i keep s ρ fe F = take-fit i keep {d = ev nothing s ρ} fe F
takeE (just n) i keep s ρ fe F = take-fit i keep {d = ev (just n) s ρ} fe F

connE : ∀ m {Γ X B} (Q : EmissionSet X → Set) (s : Obs Timeline Γ X) (b : Obs Timeline (X ∷ Γ) (IE B)) (ρ : DenEnv Γ) → GoodEnv ρ
      → (∀ p → Ok (Hots ρ) p → Early p → Q (Proper (enter (ev m s ρ) (p ⊕ [ ix 1 ]))))
      → (∀ {t} → Lawful t → Q t → FitD (Hots (hot t ∷ ρ)) (ev m b (hot t ∷ ρ)))
      → FitD (Hots ρ) (ev m (connect s b) ρ)
connE nothing  Q s b ρ g Qs LF = conn-fit Q {s = ev nothing s ρ} {F = λ h → ev nothing b (h ∷ ρ)} (inv-ev nothing s ρ g) (λ L → inv-ev nothing b (hot _ ∷ ρ) (good-cons L g)) Qs LF
connE (just n) Q s b ρ g Qs LF = conn-fit Q {s = ev (just n) s ρ} {F = λ h → ev (just n) b (h ∷ ρ)} (inv-ev (just n) s ρ g) (λ L → inv-ev (just n) b (hot _ ∷ ρ) (good-cons L g)) Qs LF

ofE : ∀ m {Γ B} (xs : List (IE B)) (ρ : DenEnv Γ) {H} → (∀ {x y} → x ∈ xs → Early y → Fine x y) → FitD H (ev m (of xs) ρ)
ofE nothing  xs ρ h = of-fit xs h
ofE (just n) xs ρ h = of-fit xs h

of-outer : ∀ m {Γ X} (xs : List X) (ρ : DenEnv Γ) p → Early p
         → (∀ {q a} → enter (ev m (of xs) ρ) p q (out a) → Early q) × EndsEarly (enter (ev m (of xs) ρ) p)
of-outer nothing  xs ρ p ep = of-early xs p ep
of-outer (just n) xs ρ p ep = of-early xs p ep

emptyE : ∀ m {Γ B} (ρ : DenEnv Γ) {H} → FitD H (ev m (empty {A = IE B}) ρ)
emptyE nothing  ρ = empty-fit
emptyE (just n) ρ = empty-fit

empty-ends : ∀ m {Γ X} (ρ : DenEnv Γ) p → Early p → EndsEarly (Proper (enter (ev m (empty {A = X}) ρ) p))
empty-ends nothing  ρ p ep ((at-end , _) , _) = early-inst [ last ] ep
empty-ends (just n) ρ p ep ((at-end , _) , _) = early-inst [ last ] ep

hotE : ∀ m {Θ B} (t : EmissionSet (IE B)) (env : DenEnv Θ) {H} → FitH t → FitD H (ev m (connected (here refl)) (hot t ∷ env))
hotE nothing  t env F = hot-fit F
hotE (just n) t env F = hot-fit F

blockE : ∀ m {Θ B} (t : EmissionSet ⊤) (env : DenEnv Θ) {H} → Lawful t → EndsEarly t → FitD H (ev m (blockˢ {Θ} {IE B}) (hot t ∷ env))
blockE nothing  t env L te = block-fit t L te
blockE (just n) t env L te = block-fit t L te

countedE : ∀ m {Γ B} (s : Obs Timeline Γ (IE B)) (ρ : DenEnv Γ) {H} → InvD H (ev m s ρ) → FitD H (ev m s ρ) → FitD H (ev m (counted s) ρ)
countedE nothing  s ρ I F = counted-fit {d = ev nothing s ρ} I F
countedE (just n) s ρ I F = counted-fit {d = ev (just n) s ρ} I F

each-vals : ∀ m {Θ A B} (t₂ : EmissionSet (IE B)) (t₁ : EmissionSet (IE A)) (env₀ : DenEnv Θ) → Lawful t₁
          → (∀ {r b n} → t₁ r (out (instEmit (value b) n)) → Early r) → EndsEarly t₁ → ∀ p → Early p
          → (∀ {q a} → enter (ev m (each valuesOf (connected (there (here refl)))) (hot t₂ ∷ hot t₁ ∷ env₀)) p q (out a) → Early q)
          × EndsEarly (enter (ev m (each valuesOf (connected (there (here refl)))) (hot t₂ ∷ hot t₁ ∷ env₀)) p)
each-vals nothing  t₂ t₁ env₀ L tv te p ep = vals-early t₁ L tv te p ep
each-vals (just n) t₂ t₁ env₀ L tv te p ep = vals-early t₁ L tv te p ep

-- A frame's pieces: its own marks, and the shared lane between them.
pieceE : ∀ m {Θ B} k i (tC : EmissionSet (IE B)) → FitH tC → (env : DenEnv Θ) → FitD (Hots (hot tC ∷ env)) (ev m (piece {Θ} {B} k i) (hot tC ∷ env))
pieceE m lanePart  0                   tC FC env = ofE m _ _ (lone-early (λ e → e))
pieceE m burstPart 0                   tC FC env = ofE m _ _ (lone-early (λ e → e))
pieceE m lanePart  1                   tC FC env = hotE m tC env FC
pieceE m burstPart 1                   tC FC env = hotE m tC env FC
pieceE m lanePart  2                   tC FC env = ofE m _ _ (lone-early (λ e → e))
pieceE m burstPart 2                   tC FC env = emptyE m _
pieceE m lanePart  (suc (suc (suc _))) tC FC env = emptyE m _
pieceE m burstPart (suc (suc (suc _))) tC FC env = emptyE m _

framedE : ∀ m {Θ B} k (tC : EmissionSet (IE B)) → FitH tC → (env : DenEnv Θ) → GoodEnv (hot tC ∷ env)
        → FitD (Hots (hot tC ∷ env)) (ev m (framed {Θ} {B} k) (hot tC ∷ env))
framedE m k tC FC env g = flatE m (mergeᶠ (just 1)) (piece k) (of (0 ∷ 1 ∷ 2 ∷ [])) (hot tC ∷ env) g (λ i → pieceE m k i tC FC env)
  (λ p _ ep → of-outer m _ _ p ep)

------------------------------------------------------------------------
-- The real flatMap

-- THE REAL FLATMAP'S ROWS FIT: each lane's, a frame's mark or a row of
-- the program it shares, the outer's ends and its lanes' before their
-- step's over.
module LaneReal (m : Maybe ℕ) {Γ Θ A B} (op : FlatOp) (f : A → Obs Timeline Γ B)
                (ρ₄ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ ⊤ ∷ IE B ∷ IE A ∷ Θ)
                (t₂ : EmissionSet (IE B)) (t₁ : EmissionSet (IE A)) (env₀ : DenEnv Θ)
                (g₂ : GoodEnv (hot t₂ ∷ hot t₁ ∷ env₀)) (L₁ : Lawful t₁)
                (tv : ∀ {r b n} → t₁ r (out (instEmit (value b) n)) → Early r) (te : EndsEarly t₁)
                (inner : ∀ a {t} → Lawful t → FitD (Hots (hot t ∷ hot t₂ ∷ hot t₁ ∷ env₀)) (ev m (elab ρ₄ (f a)) (hot t ∷ hot t₂ ∷ hot t₁ ∷ env₀))) where

  env₂ : DenEnv (IE B ∷ IE A ∷ Θ)
  env₂ = hot t₂ ∷ hot t₁ ∷ env₀

  x : A → Part → Bool → Obs Timeline (⊤ ∷ IE B ∷ IE A ∷ Θ) (IE B)
  x a k c = laneSrc ρ₄ (f a) k c

  -- The shared program's two lanes: the blocker, then the program.
  srcE : ∀ a k (t : EmissionSet ⊤) → Lawful t → EndsEarly t → ∀ c → FitD (Hots (hot t ∷ env₂)) (ev m (x a k c) (hot t ∷ env₂))
  srcE a lanePart  t L tee true  = blockE m t env₂ L tee
  srcE a burstPart t L tee true  = blockE m t env₂ L tee
  srcE a lanePart  t L tee false = inner a L
  srcE a burstPart t L tee false = emptyE m (hot t ∷ env₂)

  C : A → Part → Obs Timeline (⊤ ∷ IE B ∷ IE A ∷ Θ) (IE B)
  C a k = flatMap (mergeᶠ (just 1)) (x a k) (of (true ∷ false ∷ []))

  CE : ∀ a k (t : EmissionSet ⊤) → Lawful t → EndsEarly t → FitD (Hots (hot t ∷ env₂)) (ev m (C a k) (hot t ∷ env₂))
  CE a k t L tee = flatE m (mergeᶠ (just 1)) (x a k) (of (true ∷ false ∷ [])) (hot t ∷ env₂) (good-cons L g₂) (srcE a k t L tee)
    (λ p _ ep → of-outer m _ _ p ep)

  shareE : ∀ a k → FitD (Hots env₂) (ev m (shareˢ (x a k) (counted (framed k))) env₂)
  shareE a k = connE m EndsEarly empty (connect (C a k) (counted (framed k))) env₂ g₂
    (λ p _ ep → empty-ends m env₂ (p ⊕ [ ix 1 ]) (early-inst [ ix 1 ] ep))
    λ {t} L tee → connE m FitH (C a k) (counted (framed k)) (hot t ∷ env₂) (good-cons L g₂)
      (λ p ok ep → proper-fitH (CE a k t L tee (p ⊕ [ ix 1 ]) (ok-step p ok) (early-inst [ ix 1 ] ep)))
      λ {tC} LC FC → countedE m (framed k) (hot tC ∷ hot t ∷ env₂) (inv-ev m (framed k) _ (good-cons LC (good-cons L g₂)))
                       (framedE m k tC FC (hot t ∷ env₂) (good-cons LC (good-cons L g₂)))

  laneE : ∀ a → FitD (Hots env₂) (ev m (laneˢ (x a)) env₂)
  laneE a = takeE m true undone (flatMap (mergeᶠ nothing) (λ k → shareˢ (x a k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ []))) env₂
    undone-fails
    (flatE m (mergeᶠ nothing) (λ k → shareˢ (x a k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ [])) env₂ g₂ (shareE a)
      (λ p _ ep → of-outer m _ _ p ep))

  real : Obs Timeline (IE B ∷ IE A ∷ Θ) (IE B)
  real = flatMap op (λ a → laneˢ (x a)) (each valuesOf (connected (there (here refl))))

  realE : FitD (Hots env₂) (ev m real env₂)
  realE = flatE m op (λ a → laneˢ (x a)) (each valuesOf (connected (there (here refl)))) env₂ g₂ laneE
    (λ p _ ep → each-vals m t₂ t₁ env₀ L₁ tv te p ep)
