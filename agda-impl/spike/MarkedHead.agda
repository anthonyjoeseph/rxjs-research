{-# OPTIONS --guardedness #-}

-- SPIKE: THE ENGINE'S NEXT MARK IS THE STEPPER'S NEXT EVENT.  Per node,
-- what the engine's search finds under it (`operation.Marked.seek`) is
-- where and what `denotation.Unfold.step` shows next of its ghost
-- (`spike.MarkedGhost.gh`), or a silent mark no later (`Agrees`); under a
-- closed observer, only silent marks (`Quiet`).  It holds of every state
-- of the fragment of / empty / map / merge (`Frag`) by recursion on the
-- state (`head-agrees`): no order between nodes, no births, only each
-- node's own shape.  So it is not an invariant a step must preserve.
-- The merge (`flat-at`) races the outer against the stepper's earliest
-- lane (`race`); the engine's oldest-first fold of its lanes meets the
-- stepper's newest-first search by one exchange (`swap`, `win-snoc`).
module spike.MarkedHead where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Properties using (++-identityʳ; length-++)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᴹ)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Pos; Timeline; _<ᵖ_; ix; <ᵖ-trans; ≮-trans)
open import denotation.Unfold using (Node; Step; outˢ; skipˢ; endˢ; hushˢ; headˢ; step; restˢ; restsˢ; restᴹ; restsᶜ; restᶜ; unionˢ;
  Earliest; found; earliest; pick; Outer; doneᵒ; runᵒ; outerOf; goˢ; outerˢ; laneˢ; flatˢ) renaming (none to noneᴱ)
open import operation.Key using (Key; at; after; _<ᴷ_)
open import operation.MarkedPure using (module Machine)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; Ctx; closed; inMap; inCut;
  Out; still; shows; Cand; seek; first; retag; mapT; cutT; nx; cp; attached; attAt; raceT; outerT; laneT; lanes; inOuter; inLanes; inLn)
open import spike.MarkedGhost using (gh; lane; lanesL; deadL; outerG; poolG)

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

------------------------------------------------------------------------
-- Keys, further

postulate
  <ᴷ-trans  : ∀ a b c → a <ᴷ b ≡ true → b <ᴷ c ≡ true → a <ᴷ c ≡ true
  <ᴷ-irrefl : ∀ k → k <ᴷ k ≡ false
  -- At a position, keys compare as positions do.
  at-<ᵖ     : ∀ p q → at p <ᴷ at q ≡ p <ᵖ q
  -- Under a position is not before it.
  ext-≮     : ∀ p x → at (p ++ x) <ᴷ at p ≡ false

clash : ∀ {b} → b ≡ true → b ≡ false → ⊥
clash refl ()

-- No later than the first, strictly before the last: strictly before.
≮<ᴷ : ∀ a b c → b <ᴷ a ≡ false → b <ᴷ c ≡ true → a <ᴷ c ≡ true
≮<ᴷ a b c ba bc with a <ᴷ c in ac
... | true  = refl
... | false = ⊥-elim (clash bc (≮ᴷ-trans b a c ba ac))

<≮ᴷ : ∀ a b c → a <ᴷ b ≡ true → c <ᴷ b ≡ false → a <ᴷ c ≡ true
<≮ᴷ a b c ab cb with a <ᴷ c in ac
... | true  = refl
... | false = ⊥-elim (clash ab (≮ᴷ-trans a c b ac cb))

<-≮ᴷ : ∀ a b c → b <ᴷ c ≡ true → a <ᴷ c ≡ false → a <ᴷ b ≡ false
<-≮ᴷ a b c bc ac with a <ᴷ b in ab
... | false = refl
... | true  = ⊥-elim (clash (<ᴷ-trans a b c ab bc) ac)

------------------------------------------------------------------------
-- Steps, by their heads

agrees-upto : ∀ {Γ A} {h} {o : Out A} (st : Step Γ A) → Agrees (just (h , o)) st → Upto h (headˢ st)
agrees-upto {h = h} st (exact e) = upto-view st h e (<ᴷ-irrefl h)
agrees-upto st (early u) = u

view-key : ∀ {Γ A} {h} {o : Out A} (st : Step Γ A) {p} → just (h , o) ≡ view st → headˢ st ≡ just p → h ≡ at p
view-key (outˢ k a n) refl refl = refl
view-key (skipˢ k n)  refl refl = refl
view-key (endˢ k)     refl refl = refl
view-key hushˢ        () _

none-head : ∀ {Γ A} (st : Step Γ A) {k} → Agrees nothing st → headˢ st ≡ just k → ⊥
none-head hushˢ        _          ()
none-head (outˢ _ _ _) (exact ()) _
none-head (skipˢ _ _)  (exact ()) _
none-head (endˢ _)     (exact ()) _

head-hush : ∀ {Γ A} (st : Step Γ A) → headˢ st ≡ nothing → st ≡ hushˢ
head-hush hushˢ        _  = refl
head-hush (outˢ _ _ _) ()
head-hush (skipˢ _ _)  ()
head-hush (endˢ _)     ()

------------------------------------------------------------------------
-- The pool and an ended outer show nothing

step-rests : ∀ {Γ A B} {xs : List (Node Γ A)} → AllR B xs → step (restsᶜ {B = B} xs) ≡ hushˢ
step-rests []                                = refl
step-rests {B = B} {xs = x ∷ xs} (h ∷ hs) =
  trans (cong (λ r → unionˢ (restᶜ x) r (restsᶜ xs) (restˢ (restsᶜ {B = B} xs))) h) (restsᶜ-hush hs)

pool-step : ∀ {Γ A B} d (o : St Γ A) (ls : List (St Γ B)) → Frag o → Lanes ls → step (poolG d (gh o) (deadL ls)) ≡ hushˢ
pool-step false o ls fo fl = step-rests (dead-hush ls fl)
pool-step {B = B} true o ls fo fl =
  trans (cong (λ r → unionˢ (restᶜ (gh o)) r (restsᶜ (deadL ls)) (restˢ (restsᶜ {B = B} (deadL ls)))) (rest-hush {B = B} o fo))
        (restsᶜ-hush (dead-hush ls fl))

len0 : ∀ {a} {X : Set a} (xs : List X) → zero ≡ length xs → xs ≡ []
len0 []      _ = refl
len0 (_ ∷ _) ()

done-step : ∀ {Γ A} (s : St Γ A) → Frag s → Done s → step (gh s) ≡ hushˢ
done-step doneS            _  _  = refl
done-step (mapS f s)       fs ds rewrite done-step s fs ds = refl
done-step (cutS true a s)  fs ds = done-step s fs ds
done-step {A = A} (cutS false a s) fs ds = rest-hush {B = A} s fs
done-step (flatS (mergeᶠ nothing) f true zero [] o ls) (fo , fl , n0 , _) ds
  rewrite pool-step true o ls fo fl | len0 (lanesL ls) n0 = refl

------------------------------------------------------------------------
-- The earliest lane, as the stepper finds it

-- A search's winner: its head and its step.
win : ∀ {Γ B} → Earliest Γ B → Maybe (Pos × Step Γ B)
win noneᴱ               = nothing
win (found k bs l s as) = just (k , s)

-- A lane met before the winner (newer) wins only strictly first; one met
-- after (older) wins ties too.
pickW : ∀ {Γ B} → Step Γ B → Maybe Pos → Maybe (Pos × Step Γ B) → Maybe (Pos × Step Γ B)
pickW s nothing  w                = w
pickW s (just k) nothing          = just (k , s)
pickW s (just k) (just (k′ , s′)) = if k <ᵖ k′ then just (k , s) else just (k′ , s′)

minS : ∀ {Γ B} → Step Γ B → Maybe Pos → Maybe (Pos × Step Γ B) → Maybe (Pos × Step Γ B)
minS s nothing  w                = w
minS s (just k) nothing          = just (k , s)
minS s (just k) (just (k′ , s′)) = if k′ <ᵖ k then just (k′ , s′) else just (k , s)

win-pick : ∀ {Γ B} (l : Node Γ B) s ls h (E : Earliest Γ B) → win (pick l s ls h E) ≡ pickW s h (win E)
win-pick l s ls nothing  noneᴱ                 = refl
win-pick l s ls nothing  (found k bs c sc as)  = refl
win-pick l s ls (just k) noneᴱ                 = refl
win-pick l s ls (just k) (found k′ bs c sc as) with k <ᵖ k′
... | true  = refl
... | false = refl

pickW-if : ∀ {Γ B} (s : Step Γ B) h b (x y : Maybe (Pos × Step Γ B)) → pickW s h (if b then x else y) ≡ (if b then pickW s h x else pickW s h y)
pickW-if s h true  x y = refl
pickW-if s h false x y = refl

minS-if : ∀ {Γ B} (s : Step Γ B) h b (x y : Maybe (Pos × Step Γ B)) → minS s h (if b then x else y) ≡ (if b then minS s h x else minS s h y)
minS-if s h true  x y = refl
minS-if s h false x y = refl

-- Three by two comparisons, the third their consequence.
sel : ∀ {X : Set₁} (A B C : Bool) (a w m : X) → (A ≡ true → B ≡ true → C ≡ true) → (A ≡ false → B ≡ false → C ≡ false)
    → (if B then (if A then a else w) else (if C then a else m)) ≡ (if A then (if C then a else m) else (if B then w else m))
sel true  true  true  a w m t f = refl
sel true  true  false a w m t f with () ← t refl refl
sel true  false C     a w m t f = refl
sel false true  C     a w m t f = refl
sel false false true  a w m t f with () ← f refl refl
sel false false false a w m t f = refl

-- A newer lane and an older one meet the rest in either order.
swap : ∀ {Γ B} (a m : Step Γ B) ha hm w → pickW a ha (minS m hm w) ≡ minS m hm (pickW a ha w)
swap a m nothing   hm        w                = refl
swap a m (just ka) nothing   w                = refl
swap a m (just ka) (just km) nothing          = refl
swap a m (just ka) (just km) (just (kw , sw)) =
  trans (pickW-if a (just ka) (kw <ᵖ km) _ _)
    (trans (sel (ka <ᵖ kw) (kw <ᵖ km) (ka <ᵖ km) (just (ka , a)) (just (kw , sw)) (just (km , m))
                (<ᵖ-trans ka kw km) (λ x y → ≮-trans km kw ka y x))
           (sym (minS-if m (just km) (ka <ᵖ kw) _ _)))

lone : ∀ {Γ B} (s : Step Γ B) h → pickW s h nothing ≡ minS s h nothing
lone s nothing  = refl
lone s (just k) = refl

-- The oldest lane, last in the stepper's list, met last.
win-snoc : ∀ {Γ B} (LS : List (Node Γ B)) m → win (earliest (LS ++ [ m ])) ≡ minS (step m) (headˢ (step m)) (win (earliest LS))
win-snoc []       m = trans (win-pick m (step m) [] (headˢ (step m)) noneᴱ) (lone (step m) (headˢ (step m)))
win-snoc (l ∷ LS) m =
  trans (win-pick l (step l) (LS ++ [ m ]) (headˢ (step l)) (earliest (LS ++ [ m ])))
    (trans (cong (pickW (step l) (headˢ (step l))) (win-snoc LS m))
      (trans (swap (step l) (step m) (headˢ (step l)) (headˢ (step m)) (win (earliest LS)))
        (cong (minS (step m) (headˢ (step m))) (sym (win-pick l (step l) LS (headˢ (step l)) (earliest LS))))))

-- How many lanes a search saw, the winner among them.
Len : ∀ {Γ B} → Earliest Γ B → ℕ → Set
Len noneᴱ               n = ⊤
Len (found k bs l s as) n = n ≡ suc (length bs + length as)

len-pick : ∀ {Γ B} (l : Node Γ B) s ls h (E : Earliest Γ B) → Len E (length ls) → Len (pick l s ls h E) (suc (length ls))
len-pick l s ls nothing  noneᴱ                 e = tt
len-pick l s ls nothing  (found k bs c sc as)  e = cong suc e
len-pick l s ls (just k) noneᴱ                 e = refl
len-pick l s ls (just k) (found k′ bs c sc as) e with k <ᵖ k′
... | true  = refl
... | false = cong suc e

len-earliest : ∀ {Γ B} (LS : List (Node Γ B)) → Len (earliest LS) (length LS)
len-earliest []       = tt
len-earliest (l ∷ LS) = len-pick l (step l) LS (headˢ (step l)) (earliest LS) (len-earliest LS)

len-mid : ∀ {a} {X : Set a} (bs : List X) l as → length (bs ++ l ∷ as) ≡ suc (length bs + length as)
len-mid bs l as = trans (length-++ bs) (+-suc (length bs) (length as))

------------------------------------------------------------------------
-- The engine's lanes against the stepper's winner

stW : ∀ {Γ B} → Maybe (Pos × Step Γ B) → Step Γ B
stW nothing        = hushˢ
stW (just (k , s)) = s

HeadOK : ∀ {Γ B} → Maybe (Pos × Step Γ B) → Set
HeadOK nothing        = ⊤
HeadOK (just (k , s)) = headˢ s ≡ just k

WA : ∀ {Γ B} → Maybe (Key × Out B) → Maybe (Pos × Step Γ B) → Set₁
WA y w = Agrees y (stW w) × HeadOK w

quiet-wa : ∀ {R Γ B} (x y : Maybe (Cand R B)) (w : Maybe (Pos × Step Γ B)) → Quiet (mapᴹ proj₂ x) → WA (mapᴹ proj₂ y) w
         → WA (mapᴹ proj₂ (first x y)) w
quiet-wa nothing           y w q    a       = a
quiet-wa (just (F , k , o)) y w calm (a , h) = silent-first F k y (stW w) a , h

-- An older lane with its own step against the newer lanes' winner.
tf : ∀ {Γ B} {k h : Key} {o′ : Out B} (sx sw : Step Γ B) {km kw} → headˢ sx ≡ just km → headˢ sw ≡ just kw
   → Agrees (just (k , o′)) sw → k <ᴷ h ≡ true → at km <ᴷ h ≡ false → kw <ᵖ km ≡ false → Agrees (just (k , o′)) sx
tf {h = h} sx sw {km} {kw} hx hw (exact e) t ux u with view-key sw e hw
... | refl = ⊥-elim (clash (trans (sym (at-<ᵖ kw km)) (<≮ᴷ (at kw) h (at km) t ux)) u)
tf {k = k} {h} sx sw {km} hx hw (early v) t ux u = early (subst (Upto k) (sym hx) (<-≮ᴷ (at km) k h t ux))

ft : ∀ {Γ B} {k h : Key} {o : Out B} (sx sw : Step Γ B) {km kw} → headˢ sx ≡ just km → headˢ sw ≡ just kw
   → Agrees (just (h , o)) sx → k <ᴷ h ≡ false → at kw <ᴷ k ≡ false → kw <ᵖ km ≡ true → Agrees (just (h , o)) sw
ft {k = k} sx sw {km} {kw} hx hw (exact e) t uy u with view-key sx e hx
... | refl = ⊥-elim (clash (≮<ᴷ k (at kw) (at km) uy (trans (at-<ᵖ kw km) u)) t)
ft {k = k} {h} sx sw {km} {kw} hx hw (early v) t uy u = early (subst (Upto h) (sym hw) (≮ᴷ-trans (at kw) k h uy t))

min-at : ∀ {R Γ B} (x y : Maybe (Cand R B)) (sx : Step Γ B) km w → headˢ sx ≡ just km → Agrees (mapᴹ proj₂ x) sx
       → WA (mapᴹ proj₂ y) w → WA (mapᴹ proj₂ (first x y)) (minS sx (just km) w)
min-at nothing y sx km w hx ax ay = ⊥-elim (none-head sx ax hx)
min-at (just x) nothing sx km nothing hx ax ay = ax , hx
min-at (just x) nothing sx km (just (kw , sw)) hx ax (ay , hw) = ⊥-elim (none-head sw ay hw)
min-at (just (f , h , o)) (just (g , k , o′)) sx km nothing hx ax (ay , _) = calm-at (hush-quiet ay)
  where
    calm-at : Quiet (just (k , o′)) → WA (mapᴹ proj₂ (first (just (f , h , o)) (just (g , k , o′)))) (just (km , sx))
    calm-at calm with k <ᴷ h in t
    ... | true  = early (subst (Upto k) (sym hx) (<-≮ᴷ (at km) k h t (subst (Upto h) hx (agrees-upto sx ax)))) , hx
    ... | false = ax , hx
min-at (just (f , h , o)) (just (g , k , o′)) sx km (just (kw , sw)) hx ax (ay , hw) with k <ᴷ h in t | kw <ᵖ km in u
... | true  | true  = ay , hw
... | false | false = ax , hx
... | true  | false = tf {k = k} {h} sx sw hx hw ay t (subst (Upto h) hx (agrees-upto sx ax)) u , hx
... | false | true  = ft {k = k} {h} sx sw hx hw ax t (subst (Upto k) hw (agrees-upto sw ay)) u , hw

min-wa : ∀ {R Γ B} (x y : Maybe (Cand R B)) (sx : Step Γ B) w → Agrees (mapᴹ proj₂ x) sx → WA (mapᴹ proj₂ y) w
       → WA (mapᴹ proj₂ (first x y)) (minS sx (headˢ sx) w)
min-wa x y sx w ax ay with headˢ sx in hx
... | nothing = quiet-wa x y w (hush-quiet (subst (Agrees (mapᴹ proj₂ x)) (head-hush sx hx) ax)) ay
... | just km = min-at x y sx km w hx ax ay

on-true : ∀ {R A} (y : Maybe (Cand R A)) → mapᴹ proj₂ (retag (cutT true) y) ≡ mapᴹ proj₂ y
on-true nothing            = refl
on-true (just (g , h , o)) = refl

------------------------------------------------------------------------
-- The merge's race

-- The stepper's outer, done or running, as the engine's search sees it.
data Outer≈ {R Γ A} : Bool → Maybe (Cand R A) → Outer Γ A → Set₁ where
  gone : ∀ {x} → Quiet (mapᴹ proj₂ x) → Outer≈ true x doneᵒ
  runs : ∀ {x O so} → Agrees (mapᴹ proj₂ x) so → Outer≈ false x (runᵒ O so)

data Ran {Γ A} : Bool → Maybe (Node Γ A) → Set₁ where
  noOuter : Ran true nothing
  anOuter : ∀ O → Ran false (just O)

quiet-race : ∀ {R A B} d n (x : Maybe (Cand R A)) (y : Maybe (Cand R B)) → Quiet (mapᴹ proj₂ x) → Quiet (mapᴹ proj₂ y)
           → Quiet (mapᴹ proj₂ (raceT d n [] x y))
quiet-race d n nothing            nothing            qx   qy   = none
quiet-race d n nothing            (just (g , k , o)) qx   calm = calm
quiet-race d n (just (f , h , o)) nothing            calm qy   = calm
quiet-race d n (just (f , h , o)) (just (g , k , o′)) calm calm with h <ᴷ k
... | true  = calm
... | false = calm

outer-upto : ∀ {Γ A B} (g : A → Pos → Node Γ B) (O : Node Γ A) (so : Step Γ A) (L : List (Node Γ B)) P k
           → Upto k (headˢ so) → Upto k (headˢ (outerˢ (mergeᶠ nothing) g O so L [] P))
outer-upto g O (outˢ q a o′) L       P k u = ≮ᴷ-trans (at (q ++ [ ix 0 ])) (at q) k (ext-≮ q [ ix 0 ]) u
outer-upto g O (skipˢ q o′)  L       P k u = u
outer-upto g O (endˢ c)      []      P k u = u
outer-upto g O (endˢ c)      (_ ∷ _) P k u = u
outer-upto g O hushˢ         L       P k u = u

-- The outer's event, read as the merge's.
outer-agrees : ∀ {Γ A B} (g : A → Pos → Node Γ B) (O : Node Γ A) (so : Step Γ A) (L : List (Node Γ B)) P n h (o : Out A)
             → n ≡ length L → Agrees (just (h , o)) so → Agrees (just (outerT n [] h o)) (outerˢ (mergeᶠ nothing) g O so L [] P)
outer-agrees g O (outˢ q a o′) L       P n _ _ e    (exact refl) = exact refl
outer-agrees g O (skipˢ q o′)  L       P n _ _ e    (exact refl) = exact refl
outer-agrees g O (endˢ c)      []      P n _ _ refl (exact refl) = exact refl
outer-agrees g O (endˢ c)      (_ ∷ _) P n _ _ refl (exact refl) = exact refl
outer-agrees g O hushˢ         L       P n h o e    (exact ())
outer-agrees g O so            L       P n h o e    (early u)    = early (outer-upto g O so L P h u)

lane-head : ∀ {Γ A B} (g : A → Pos → Node Γ B) mo bs l (s : Step Γ B) as P
          → headˢ (laneˢ (mergeᶠ nothing) g mo bs l s as [] P) ≡ headˢ s
lane-head g mo       bs      l (outˢ k b c) as      P = refl
lane-head g mo       bs      l (skipˢ k c)  as      P = refl
lane-head g nothing  []      l (endˢ c)     []      P = refl
lane-head g nothing  []      l (endˢ c)     (_ ∷ _) P = refl
lane-head g nothing  (_ ∷ _) l (endˢ c)     as      P = refl
lane-head g (just o) bs      l (endˢ c)     as      P = refl
lane-head g mo       bs      l hushˢ        as      P = refl

-- A lane's event, read as the merge's.
lane-agrees : ∀ {Γ A B} (g : A → Pos → Node Γ B) d mo (bs : List (Node Γ B)) l (s : Step Γ B) as P n k (o : Out B)
            → Ran d mo → n ≡ suc (length bs + length as) → Agrees (just (k , o)) s
            → Agrees (just (laneT {A = A} d n [] k o)) (laneˢ (mergeᶠ nothing) g mo bs l s as [] P)
lane-agrees g d mo bs      l (outˢ k′ b c) as      P n _ _ r           e    (exact refl) = exact refl
lane-agrees g d mo bs      l (skipˢ k′ c)  as      P n _ _ r           e    (exact refl) = exact refl
lane-agrees g d mo []      l (endˢ c)      []      P n _ _ noOuter     refl (exact refl) = exact refl
lane-agrees g d mo []      l (endˢ c)      (_ ∷ _) P n _ _ noOuter     refl (exact refl) = exact refl
lane-agrees g d mo (_ ∷ _) l (endˢ c)      as      P n _ _ noOuter     refl (exact refl) = exact refl
lane-agrees g d mo bs      l (endˢ c)      as      P n _ _ (anOuter O) e    (exact refl) = exact refl
lane-agrees g d mo bs      l hushˢ         as      P n k o r           e    (exact ())
lane-agrees g d mo bs      l s             as      P n k o r           e    (early u)    =
  early (subst (Upto k) (sym (lane-head g mo bs l s as P)) u)

-- A silent mark strictly before a lane's own: no later than the merge's step.
silent-lane : ∀ {Γ A B} (g : A → Pos → Node Γ B) mo bs l (s : Step Γ B) as P {h k′ k} {o′ : Out B}
            → h <ᴷ k′ ≡ true → Agrees (just (k′ , o′)) s → headˢ s ≡ just k
            → Upto h (headˢ (laneˢ (mergeᶠ nothing) g mo bs l s as [] P))
silent-lane g mo bs l s as P {h} {k′} {k} t ay hd =
  subst (Upto h) (sym (lane-head g mo bs l s as P))
    (subst (Upto h) (sym hd) (<-≮ᴷ (at k) h k′ t (subst (Upto k′) hd (agrees-upto s ay))))

-- The engine takes the outer, the stepper the lane: only a silent outer.
out-first : ∀ {Γ A B} (g : A → Pos → Node Γ B) n O (so : Step Γ A) k₀ → headˢ so ≡ just k₀ → ∀ bs l (s : Step Γ B) as P k h (o : Out A) k′ (o′ : Out B)
          → Agrees (just (h , o)) so → Agrees (just (k′ , o′)) s → headˢ s ≡ just k → h <ᴷ k′ ≡ true → k₀ <ᵖ k ≡ false
          → Agrees (just (outerT {B = B} n [] h o)) (laneˢ (mergeᶠ nothing) g (just O) bs l s as [] P)
out-first g n O so k₀ hs bs l s as P k h o k′ o′ (exact e) ay hd t u with view-key so e hs
... | refl = ⊥-elim (clash (trans (sym (at-<ᵖ k₀ k)) (<≮ᴷ (at k₀) k′ (at k) t (subst (Upto k′) hd (agrees-upto s ay)))) u)
out-first g n O so k₀ hs bs l s as P k h o k′ o′ (early v) ay hd t u = early (silent-lane g (just O) bs l s as P t ay hd)

-- The engine takes the lane, the stepper the outer: only a silent lane.
lane-first : ∀ {Γ A B} (g : A → Pos → Node Γ B) n O (so : Step Γ A) k₀ → headˢ so ≡ just k₀ → ∀ bs l (s : Step Γ B) as P k h (o : Out A) k′ (o′ : Out B)
           → Agrees (just (h , o)) so → Agrees (just (k′ , o′)) s → headˢ s ≡ just k → h <ᴷ k′ ≡ false → k₀ <ᵖ k ≡ true
           → Agrees (just (laneT {A = A} false n [] k′ o′)) (outerˢ (mergeᶠ nothing) g O so (bs ++ l ∷ as) [] P)
lane-first g n O so k₀ hs bs l s as P k h o k′ o′ ax (exact e) hd t u with view-key s e hd
... | refl = ⊥-elim (clash (≮<ᴷ h (at k₀) (at k) (subst (Upto h) hs (agrees-upto so ax)) (trans (at-<ᵖ k₀ k) u)) t)
lane-first g n O so k₀ hs bs l s as P k h o k′ o′ ax (early v) hd t u =
  early (outer-upto g O so (bs ++ l ∷ as) P k′ (upto-step h k′ (headˢ so) (agrees-upto so ax) t))

race-run : ∀ {R Γ A B} (g : A → Pos → Node Γ B) n O (so : Step Γ A) k₀ → headˢ so ≡ just k₀ → ∀ (LS : List (Node Γ B)) P k bs l (s : Step Γ B) as
           (f : Machine.Found R) h (o : Out A) (g′ : Machine.Found R) k′ (o′ : Out B)
         → Agrees (just (h , o)) so → Agrees (just (k′ , o′)) s → headˢ s ≡ just k → n ≡ length LS → length LS ≡ suc (length bs + length as)
         → Agrees (mapᴹ proj₂ (raceT false n [] (just (f , h , o)) (just (g′ , k′ , o′))))
                  (if k₀ <ᵖ k then outerˢ (mergeᶠ nothing) g O so (bs ++ l ∷ as) [] P else laneˢ (mergeᶠ nothing) g (just O) bs l s as [] P)
race-run g n O so k₀ hs LS P k bs l s as f h o g′ k′ o′ ax ay hd e le with h <ᴷ k′ in t | k₀ <ᵖ k in u
... | true  | true  = outer-agrees g O so (bs ++ l ∷ as) P n h o (trans e (trans le (sym (len-mid bs l as)))) ax
... | false | false = lane-agrees g false (just O) bs l s as P n k′ o′ (anOuter O) (trans e le) ay
... | true  | false = out-first g n O so k₀ hs bs l s as P k h o k′ o′ ax ay hd t u
... | false | true  = lane-first g n O so k₀ hs bs l s as P k h o k′ o′ ax ay hd t u

out-or-calm : ∀ {R Γ A B} (g : A → Pos → Node Γ B) O (so : Step Γ A) LS P n (f : Machine.Found R) h (o : Out A) (g′ : Machine.Found R) k′ (o′ : Out B)
            → n ≡ length LS → Agrees (just (h , o)) so → Quiet (just (k′ , o′))
            → Agrees (mapᴹ proj₂ (raceT false n [] (just (f , h , o)) (just (g′ , k′ , o′)))) (outerˢ (mergeᶠ nothing) g O so LS [] P)
out-or-calm g O so LS P n f h o g′ k′ o′ e ax calm with h <ᴷ k′ in t
... | true  = outer-agrees g O so LS P n h o e ax
... | false = early (outer-upto g O so LS P k′ (upto-step h k′ (headˢ so) (agrees-upto so ax) t))

-- The merge's step: the outer against the earliest lane.
race : ∀ {R Γ A B} (g : A → Pos → Node Γ B) d n (OUT : Outer Γ A) (LS : List (Node Γ B)) P (E : Earliest Γ B)
         (x : Maybe (Cand R A)) (y : Maybe (Cand R B))
     → Outer≈ d x OUT → WA (mapᴹ proj₂ y) (win E) → n ≡ length LS → Len E (length LS)
     → Agrees (mapᴹ proj₂ (raceT d n [] x y)) (goˢ (mergeᶠ nothing) g OUT LS [] P E)
race g d n doneᵒ LS P noneᴱ x y (gone qx) (ay , _) e _ = quiet-hush (quiet-race d n x y qx (hush-quiet ay))
race g d n doneᵒ LS P (found k bs l s as) x nothing (gone qx) (ay , hd) e le = ⊥-elim (none-head s ay hd)
race g d n doneᵒ LS P (found k bs l s as) nothing (just (g′ , k′ , o′)) (gone qx) (ay , hd) e le =
  lane-agrees g d nothing bs l s as P n k′ o′ noOuter (trans e le) ay
race g d n doneᵒ LS P (found k bs l s as) (just (f , h , o)) (just (g′ , k′ , o′)) (gone calm) (ay , hd) e le with h <ᴷ k′ in t
... | true  = early (silent-lane g nothing bs l s as P t ay hd)
... | false = lane-agrees g d nothing bs l s as P n k′ o′ noOuter (trans e le) ay
race g d n (runᵒ O hushˢ)         LS P noneᴱ nothing y (runs _)          (ay , _) e _ = quiet-hush (quiet-race d n nothing y none (hush-quiet ay))
race g d n (runᵒ O (outˢ _ _ _))  LS P noneᴱ nothing y (runs (exact ())) _ e _
race g d n (runᵒ O (skipˢ _ _))   LS P noneᴱ nothing y (runs (exact ())) _ e _
race g d n (runᵒ O (endˢ _))      LS P noneᴱ nothing y (runs (exact ())) _ e _
race g d n (runᵒ O so) LS P noneᴱ (just (f , h , o)) nothing (runs ax) _ e _ = outer-agrees g O so LS P n h o e ax
race g d n (runᵒ O so) LS P noneᴱ (just (f , h , o)) (just (g′ , k′ , o′)) (runs ax) (ay , _) e _ =
  out-or-calm g O so LS P n f h o g′ k′ o′ e ax (hush-quiet ay)
race g d n (runᵒ O so) LS P (found k bs l s as) x nothing (runs ax) (ay , hd) e le = ⊥-elim (none-head s ay hd)
race g d n (runᵒ O hushˢ)        LS P (found k bs l s as) nothing (just (g′ , k′ , o′)) (runs _) (ay , hd) e le =
  lane-agrees g d (just O) bs l s as P n k′ o′ (anOuter O) (trans e le) ay
race g d n (runᵒ O (outˢ _ _ _)) LS P (found k bs l s as) nothing (just _) (runs (exact ())) _ e le
race g d n (runᵒ O (skipˢ _ _))  LS P (found k bs l s as) nothing (just _) (runs (exact ())) _ e le
race g d n (runᵒ O (endˢ _))     LS P (found k bs l s as) nothing (just _) (runs (exact ())) _ e le
race g d n (runᵒ O hushˢ) LS P (found k bs l s as) (just (f , h , o)) (just (g′ , k′ , o′)) (runs (exact ())) _ e le
race g d n (runᵒ O hushˢ) LS P (found k bs l s as) (just (f , h , o)) (just (g′ , k′ , o′)) (runs (early _)) (ay , hd) e le with h <ᴷ k′ in t
... | true  = early (silent-lane g (just O) bs l s as P t ay hd)
... | false = lane-agrees g d (just O) bs l s as P n k′ o′ (anOuter O) (trans e le) ay
race g d n (runᵒ O (outˢ q a o″)) LS P (found k bs l s as) (just (f , h , o)) (just (g′ , k′ , o′)) (runs ax) (ay , hd) e le =
  race-run g n O (outˢ q a o″) q refl LS P k bs l s as f h o g′ k′ o′ ax ay hd e le
race g d n (runᵒ O (skipˢ q o″)) LS P (found k bs l s as) (just (f , h , o)) (just (g′ , k′ , o′)) (runs ax) (ay , hd) e le =
  race-run g n O (skipˢ q o″) q refl LS P k bs l s as f h o g′ k′ o′ ax ay hd e le
race g d n (runᵒ O (endˢ c)) LS P (found k bs l s as) (just (f , h , o)) (just (g′ , k′ , o′)) (runs ax) (ay , hd) e le =
  race-run g n O (endˢ c) c refl LS P k bs l s as f h o g′ k′ o′ ax ay hd e le

outer-at : ∀ {R Γ A} d (o : St Γ A) (x : Maybe (Cand R A)) → Frag o → (d ≡ true → Done o) → Agrees (mapᴹ proj₂ x) (step (gh o))
         → Outer≈ d x (outerOf (outerG d (gh o)))
outer-at true  o x fo dd a = gone (hush-quiet (subst (Agrees (mapᴹ proj₂ x)) (done-step o fo (dd refl)) a))
outer-at false o x fo dd a = runs a

------------------------------------------------------------------------
-- Every state of the fragment

mutual
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
  head-agrees c (flatS (mergeᶠ nothing) f d n [] o ls) fs = flat-at (closed c) c f d n o ls refl fs
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

  -- A merge: the outer against its lanes, as the stepper races them.
  flat-at : ∀ {R Γ A B} b (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) d n (o : St Γ A) ls → closed c ≡ b
          → Frag (flatS (mergeᶠ nothing) f d n [] o ls) → HeadAt b (cand c (flatS (mergeᶠ nothing) f d n [] o ls)) (flatS (mergeᶠ nothing) f d n [] o ls)
  flat-at true c f d n o ls cl (fo , fl , en , dd) =
    quiet-race d n (seek (inOuter (mergeᶠ nothing) f d n [] ls c) o) (lanes c (mergeᶠ nothing) f d n [] o [] ls)
      (subst (λ b → HeadAt b (cand (inOuter (mergeᶠ nothing) f d n [] ls c) o) o) cl (head-agrees (inOuter (mergeᶠ nothing) f d n [] ls c) o fo))
      (lanes-quiet c f d n o [] ls cl fl)
  flat-at false c f d n o ls cl (fo , fl , en , dd) =
    subst (λ st → Agrees (cand c (flatS (mergeᶠ nothing) f d n [] o ls))
                         (flatˢ (mergeᶠ nothing) (lane f) (outerOf (outerG d (gh o))) (lanesL ls) [] (poolG d (gh o) (deadL ls)) st (earliest (lanesL ls))))
      (sym (pool-step d o ls fo fl))
      (race (lane f) d n (outerOf (outerG d (gh o))) (lanesL ls) (poolG d (gh o) (deadL ls)) (earliest (lanesL ls))
        (seek (inOuter (mergeᶠ nothing) f d n [] ls c) o) (lanes c (mergeᶠ nothing) f d n [] o [] ls)
        (outer-at d o (seek (inOuter (mergeᶠ nothing) f d n [] ls c) o) fo dd
          (subst (λ b → HeadAt b (cand (inOuter (mergeᶠ nothing) f d n [] ls c) o) o) cl (head-agrees (inOuter (mergeᶠ nothing) f d n [] ls c) o fo)))
        (lanes-wa c f d n o [] ls cl fl) en (len-earliest (lanesL ls)))

  -- The engine's lanes, oldest first, against the stepper's earliest.
  lanes-wa : ∀ {R Γ A B} (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) d n (o : St Γ A) pre ls → closed c ≡ false → Lanes ls
           → WA (mapᴹ proj₂ (lanes c (mergeᶠ nothing) f d n [] o pre ls)) (win (earliest (lanesL ls)))
  lanes-wa c f d n o pre [] cl _ = exact refl , tt
  lanes-wa c f d n o pre (lnS true (cutS true a s) ∷ post) cl (fs , fl) =
    subst (WA (mapᴹ proj₂ (lanes c (mergeᶠ nothing) f d n [] o pre (lnS true (cutS true a s) ∷ post)))) (sym (win-snoc (lanesL post) (gh s)))
      (min-wa (retag (cutT true) (seek C (cutS true a s))) (lanes c (mergeᶠ nothing) f d n [] o (pre ++ [ lnS true (cutS true a s) ]) post)
              (step (gh s)) (win (earliest (lanesL post)))
        (subst (λ z → Agrees z (step (gh s))) (sym (on-true (seek C (cutS true a s))))
          (subst (λ b → HeadAt b (cand C (cutS true a s)) (cutS true a s)) cl (head-agrees C (cutS true a s) fs)))
        (lanes-wa c f d n o (pre ++ [ lnS true (cutS true a s) ]) post cl fl))
    where C = inLn true (inLanes (mergeᶠ nothing) f d n [] o pre post c)
  lanes-wa c f d n o pre (lnS false (cutS false a s) ∷ post) cl (fs , fl) =
    subst (WA (mapᴹ proj₂ (lanes c (mergeᶠ nothing) f d n [] o pre (lnS false (cutS false a s) ∷ post))))
          (sym (cong (λ L → win (earliest L)) (++-identityʳ (lanesL post))))
      (quiet-wa (retag (cutT false) (seek C (cutS false a s))) (lanes c (mergeᶠ nothing) f d n [] o (pre ++ [ lnS false (cutS false a s) ]) post)
                (win (earliest (lanesL post))) (off-quiet (seek C (cutS false a s)))
        (lanes-wa c f d n o (pre ++ [ lnS false (cutS false a s) ]) post cl fl))
    where C = inLn false (inLanes (mergeᶠ nothing) f d n [] o pre post c)

  lanes-quiet : ∀ {R Γ A B} (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) d n (o : St Γ A) pre ls → closed c ≡ true → Lanes ls
              → Quiet (mapᴹ proj₂ (lanes c (mergeᶠ nothing) f d n [] o pre ls))
  lanes-quiet c f d n o pre [] cl _ = none
  lanes-quiet c f d n o pre (lnS true (cutS true a s) ∷ post) cl (fs , fl) =
    quiet-first (retag (cutT true) (seek C (cutS true a s))) (lanes c (mergeᶠ nothing) f d n [] o (pre ++ [ lnS true (cutS true a s) ]) post)
      (subst Quiet (sym (on-true (seek C (cutS true a s))))
        (subst (λ b → HeadAt b (cand C (cutS true a s)) (cutS true a s)) cl (head-agrees C (cutS true a s) fs)))
      (lanes-quiet c f d n o (pre ++ [ lnS true (cutS true a s) ]) post cl fl)
    where C = inLn true (inLanes (mergeᶠ nothing) f d n [] o pre post c)
  lanes-quiet c f d n o pre (lnS false (cutS false a s) ∷ post) cl (fs , fl) =
    quiet-first (retag (cutT false) (seek C (cutS false a s))) (lanes c (mergeᶠ nothing) f d n [] o (pre ++ [ lnS false (cutS false a s) ]) post)
      (off-quiet (seek C (cutS false a s)))
      (lanes-quiet c f d n o (pre ++ [ lnS false (cutS false a s) ]) post cl fl)
    where C = inLn false (inLanes (mergeᶠ nothing) f d n [] o pre post c)
