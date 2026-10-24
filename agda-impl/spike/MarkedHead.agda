{-# OPTIONS --guardedness #-}

-- SPIKE: THE ENGINE'S NEXT MARK IS THE STEPPER'S NEXT EVENT.  Per node,
-- what the engine's search finds under it (`operation.Marked.seek`) is
-- where and what `denotation.Unfold.step` shows next of its ghost
-- (`spike.MarkedGhost.gh`), or a silent mark no later (`Agrees`); under a
-- closed observer, only silent marks (`Quiet`).  It holds of every state
-- of the fragment of / empty / map / merge (`Frag`) by recursion on the
-- state (`head-agrees`): no order between nodes, no births, only each
-- node's own shape.  So it is not an invariant a step must preserve.
module spike.MarkedHead where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᴹ)
open import Data.Nat using (zero)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Pos; Timeline)
open import denotation.Unfold using (Node; Step; outˢ; skipˢ; endˢ; hushˢ; headˢ; step; restˢ; restsˢ; restᴹ; restsᶜ)
open import operation.Key using (Key; at; after; _<ᴷ_)
open import operation.MarkedPure using (module Machine)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; Ctx; closed; inMap; inCut;
  Out; still; shows; Cand; seek; first; retag; mapT; cutT; nx; cp; attached; attAt)
open import spike.MarkedGhost using (gh; lanesL; deadL; outerG; poolG)

------------------------------------------------------------------------
-- The relation

-- What a step shows, and where.
view : ∀ {Γ A} → Step Γ A → Maybe (Key × Out A)
view (outˢ k a _) = just (at k , shows (nx a))
view (skipˢ k _)  = just (at k , still)
view (endˢ k)     = just (at k , shows cp)
view hushˢ        = nothing

-- No later than a head, if there is one.
Upto : Key → Maybe Pos → Set
Upto k nothing  = ⊤
Upto k (just h) = at h <ᴷ k ≡ false

-- The step's own event, or a silent mark no later.
data Agrees {Γ A} : Maybe (Key × Out A) → Step Γ A → Set₁ where
  exact : ∀ {x st} → x ≡ view st → Agrees x st
  early : ∀ {k st} → Upto k (headˢ st) → Agrees (just (k , still)) st

data Quiet {A : Set} : Maybe (Key × Out A) → Set₁ where
  none : Quiet nothing
  calm : ∀ {k} → Quiet (just (k , still))

-- What the engine finds under a node, as its parent reads it.
cand : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Maybe (Key × Out A)
cand c s = mapᴹ proj₂ (seek c s)

HeadAt : ∀ {Γ A} → Bool → Maybe (Key × Out A) → St Γ A → Set₁
HeadAt true  x s = Quiet x
HeadAt false x s = Agrees x (step (gh s))

Head : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Set₁
Head c s = HeadAt (closed c) (cand c s) s

------------------------------------------------------------------------
-- The fragment

mutual
  Frag : ∀ {Γ A} → St Γ A → Set
  Frag (ofS i p xs)                           = ⊤
  Frag doneS                                  = ⊤
  Frag (mapS f s)                             = Frag s
  Frag (cutS l a s)                           = Frag s
  Frag (flatS (mergeᶠ nothing) f d n [] o ls) = Frag o × Lanes ls × n ≡ length (lanesL ls) × (d ≡ true → Done o)
  Frag _                                      = ⊥

  -- Each lane live and switched on, or ended and switched off.
  Lanes : ∀ {Γ A} → List (St Γ A) → Set
  Lanes []       = ⊤
  Lanes (s ∷ ls) = Lane s × Lanes ls

  Lane : ∀ {Γ A} → St Γ A → Set
  Lane (lnS true (cutS true a s))   = Frag s
  Lane (lnS false (cutS false a s)) = Frag s
  Lane _                            = ⊥

  -- Over: nothing left to show.
  Done : ∀ {Γ A} → St Γ A → Set
  Done doneS                                       = ⊤
  Done (mapS f s)                                  = Done s
  Done (cutS l a s)                                = Done s
  Done (flatS (mergeᶠ nothing) f true zero [] o ls) = Done o
  Done _                                           = ⊥

------------------------------------------------------------------------
-- Keys

postulate
  -- Neither strictly before the next, twice: not strictly before the last.
  ≮ᴷ-trans : ∀ a b c → a <ᴷ b ≡ false → b <ᴷ c ≡ false → a <ᴷ c ≡ false

-- A step's own event is where it heads.
upto-view : ∀ {Γ A} (st : Step Γ A) {h o} k → just (h , o) ≡ view st → h <ᴷ k ≡ false → Upto k (headˢ st)
upto-view (outˢ p a n) k refl e = e
upto-view (skipˢ p n)  k refl e = e
upto-view (endˢ p)     k refl e = e

-- Not after a mark no later than the head: no later than the head.
upto-step : ∀ h k (m : Maybe Pos) → Upto h m → h <ᴷ k ≡ false → Upto k m
upto-step h k nothing  u e = tt
upto-step h k (just p) u e = ≮ᴷ-trans (at p) h k u e

------------------------------------------------------------------------
-- Quiet and agreeing candidates

quiet-hush : ∀ {Γ A} {x : Maybe (Key × Out A)} → Quiet x → Agrees {Γ} x hushˢ
quiet-hush none = exact refl
quiet-hush calm = early tt

-- What agrees with a step showing nothing is quiet.
hush-quiet : ∀ {Γ A} {x : Maybe (Key × Out A)} → Agrees {Γ} x hushˢ → Quiet x
hush-quiet (exact refl) = none
hush-quiet (early u)    = calm

-- A silent mark before the rest: no later than the rest's head.
silent-first : ∀ {R Γ A} (F : Machine.Found R) k (y : Maybe (Cand R A)) (st : Step Γ A)
             → Agrees (mapᴹ proj₂ y) st → Agrees (mapᴹ proj₂ (first (just (F , k , still)) y)) st
silent-first F k nothing  st (exact e) with st | e
... | hushˢ | refl = early tt
silent-first F k (just (g , h , o)) st a with h <ᴷ k in hk
silent-first F k (just (g , h , o)) st a           | true  = a
silent-first F k (just (g , h , o)) st (exact e)   | false = early (upto-view st k e hk)
silent-first F k (just (g , h , .still)) st (early u) | false = early (upto-step h k (headˢ st) u hk)

quiet-first : ∀ {R A} (x y : Maybe (Cand R A)) → Quiet (mapᴹ proj₂ x) → Quiet (mapᴹ proj₂ y) → Quiet (mapᴹ proj₂ (first x y))
quiet-first nothing             y        qx qy = qy
quiet-first (just x)            nothing  qx qy = qx
quiet-first (just (f , h , o))  (just (g , h′ , o′)) qx qy with h′ <ᴷ h
... | true  = qy
... | false = qx

------------------------------------------------------------------------
-- Rests and ends of the fragment show nothing

-- Nodes whose rests show nothing.
data AllR {Γ A} (B : Set) : List (Node Γ A) → Set₁ where
  []  : AllR B []
  _∷_ : ∀ {x xs} → restˢ {B = B} x ≡ hushˢ → AllR B xs → AllR B (x ∷ xs)

allR-++ : ∀ {Γ A B} {xs ys : List (Node Γ A)} → AllR B xs → AllR B ys → AllR B (xs ++ ys)
allR-++ []       r = r
allR-++ (h ∷ hs) r = h ∷ allR-++ hs r

rests-hush : ∀ {Γ A B} {xs : List (Node Γ A)} → AllR B xs → restsˢ {B = B} xs ≡ hushˢ
rests-hush []                      = refl
rests-hush {xs = x ∷ xs} (h ∷ hs) rewrite h = rests-hush hs

restsᶜ-hush : ∀ {Γ A B C} {xs : List (Node Γ A)} → AllR B xs → restˢ {B = B} (restsᶜ {B = C} xs) ≡ hushˢ
restsᶜ-hush []                      = refl
restsᶜ-hush {xs = x ∷ xs} (h ∷ hs) rewrite h = restsᶜ-hush hs

mutual
  rest-hush : ∀ {Γ A B} (s : St Γ A) → Frag s → restˢ {B = B} (gh s) ≡ hushˢ
  rest-hush (ofS i p xs) _ = refl
  rest-hush doneS        _ = refl
  rest-hush (mapS f s)   fs = rest-hush s fs
  rest-hush (cutS true a s)  fs = rest-hush s fs
  rest-hush (cutS false a s) fs = rest-hush s fs
  rest-hush {B = B} (flatS (mergeᶠ nothing) f d n [] o ls) (fo , fl , _)
    rewrite outer-hush {B = B} d o fo | rests-hush (live-hush {B = B} ls fl) | pool-hush {B = B} d o ls fo fl = refl

  outer-hush : ∀ {Γ A B} d (o : St Γ A) → Frag o → restᴹ {B = B} (outerG d (gh o)) ≡ hushˢ
  outer-hush true  o fo = refl
  outer-hush false o fo = rest-hush o fo

  live-hush : ∀ {Γ A B} (ls : List (St Γ A)) → Lanes ls → AllR B (lanesL ls)
  live-hush []                              _          = []
  live-hush (lnS true (cutS true a s) ∷ ls)   (fs , fl) = allR-++ (live-hush ls fl) (rest-hush s fs ∷ [])
  live-hush (lnS false (cutS false a s) ∷ ls) (fs , fl) = allR-++ (live-hush ls fl) []

  dead-hush : ∀ {Γ A B} (ls : List (St Γ A)) → Lanes ls → AllR B (deadL ls)
  dead-hush []                              _          = []
  dead-hush (lnS true (cutS true a s) ∷ ls)   (fs , fl) = dead-hush ls fl
  dead-hush (lnS false (cutS false a s) ∷ ls) (fs , fl) = rest-hush s fs ∷ dead-hush ls fl

  pool-hush : ∀ {Γ A B C} d (o : St Γ A) (ls : List (St Γ C)) → Frag o → Lanes ls → restˢ {B = B} (poolG d (gh o) (deadL ls)) ≡ hushˢ
  pool-hush false o ls fo fl = restsᶜ-hush (dead-hush ls fl)
  pool-hush {B = B} true o ls fo fl rewrite rest-hush {B = B} o fo = restsᶜ-hush (dead-hush ls fl)

------------------------------------------------------------------------
-- The fragment's heads

-- An of: its next value, or its end, unless its observer is closed.
of-head : ∀ {R Γ A} (c : Ctx R Γ A) i p (xs : List A) → Head c (ofS i p xs)
of-head c i p [] with closed c
... | true  = calm
... | false = exact refl
of-head c i p (x ∷ xs) with closed c
... | true  = calm
... | false = exact refl

done-head : ∀ {R Γ A} (c : Ctx R Γ A) → Head c (doneS {A = A})
done-head c with closed c
... | true  = none
... | false = exact refl

map-head : ∀ {R Γ A B} b (f : A → B) (y : Maybe (Cand R A)) (s : St Γ A)
         → HeadAt b (mapᴹ proj₂ y) s → HeadAt b (mapᴹ proj₂ (retag (mapT f) y)) (mapS f s)
map-head true  f nothing            s none = none
map-head true  f (just (g , h , o)) s calm = calm
map-head false f nothing            s (exact e) with step (gh s) | e
... | hushˢ | refl = exact refl
map-head false f (just (g , h , o)) s (exact e) with step (gh s) | e
... | outˢ k a n | refl = exact refl
... | skipˢ k n  | refl = exact refl
... | endˢ k     | refl = exact refl
map-head false f (just (g , h , .still)) s (early u) with step (gh s) | u
... | outˢ k a n | u′ = early u′
... | skipˢ k n  | u′ = early u′
... | endˢ k     | u′ = early u′
... | hushˢ      | u′ = early u′

-- A switch on passes its child's mark; one not yet attached runs its
-- attach first on a tie.
on-head : ∀ {R Γ A} b a (y : Maybe (Cand R A)) (s : St Γ A)
        → HeadAt b (mapᴹ proj₂ y) s → HeadAt b (mapᴹ proj₂ (retag (cutT true) y)) (cutS true a s)
on-head true  a nothing            s q = q
on-head true  a (just (g , h , o)) s q = q
on-head false a nothing            s q = q
on-head false a (just (g , h , o)) s q = q

att-head : ∀ {R Γ A} b (F : Machine.Found R) p (y : Maybe (Cand R A)) (s : St Γ A)
         → HeadAt b (mapᴹ proj₂ y) s → HeadAt b (mapᴹ proj₂ (first (just (F , after p , still)) (retag (cutT true) y))) (cutS true (attAt p) s)
att-head true  F p y s q = quiet-first (just (F , after p , still)) (retag (cutT true) y) calm (on-head true (attAt p) y s q)
att-head false F p y s a = silent-first F (after p) (retag (cutT true) y) (step (gh s)) (on-head false (attAt p) y s a)

-- A switch off shows nothing.
off-quiet : ∀ {R A} (y : Maybe (Cand R A)) → Quiet (mapᴹ proj₂ (retag (cutT false) y))
off-quiet nothing            = none
off-quiet (just (g , h , o)) = calm

off-head : ∀ {Γ A} b a (x : Maybe (Key × Out A)) (s : St Γ A) → Frag s → Quiet x → HeadAt b x (cutS false a s)
off-head true  a x s fs q = q
off-head {A = A} false a x s fs q rewrite rest-hush {B = A} s fs = quiet-hush q

postulate
  -- A merge: the outer against its lanes, as the stepper races them.
  flat-head : ∀ {R Γ A B} (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) d n (o : St Γ A) ls
            → Frag (flatS (mergeᶠ nothing) f d n [] o ls) → Head c (flatS (mergeᶠ nothing) f d n [] o ls)

head-agrees : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Frag s → Head c s
head-agrees c (ofS i p xs) _ = of-head c i p xs
head-agrees c doneS        _ = done-head c
head-agrees c (mapS f s) fs = map-head (closed c) f (seek (inMap f c) s) s (head-agrees (inMap f c) s fs)
head-agrees c (cutS true attached s) fs = on-head (closed c) attached (seek (inCut true attached c) s) s (head-agrees (inCut true attached c) s fs)
head-agrees c (cutS true (attAt p) s) fs = att-head (closed c) _ p (seek (inCut true (attAt p) c) s) s (head-agrees (inCut true (attAt p) c) s fs)
head-agrees c (cutS false attached s) fs =
  off-head (closed c) attached _ s fs (off-quiet (seek (inCut false attached c) s))
head-agrees c (cutS false (attAt p) s) fs =
  off-head (closed c) (attAt p) _ s fs (quiet-first (just (_ , after p , still)) (retag (cutT false) (seek (inCut false (attAt p) c) s)) calm (off-quiet (seek (inCut false (attAt p) c) s)))
head-agrees c (flatS (mergeᶠ nothing) f d n [] o ls) fs = flat-head c f d n o ls fs
head-agrees c (pend o)        ()
head-agrees c (coldS b l)     ()
head-agrees c (scanS f z s)   ()
head-agrees c (lnS b s)       ()
head-agrees c (takeS i q w s) ()
head-agrees c (connS k o b)   ()
head-agrees c (joinS j g x ib) ()
head-agrees c (flatS (mergeᶠ nothing) f d n (_ ∷ _) o ls) ()
head-agrees c (flatS (mergeᶠ (just m)) f d n q o ls) ()
head-agrees c (flatS switchᶠ f d n q o ls) ()
head-agrees c (flatS exhaustᶠ f d n q o ls) ()
