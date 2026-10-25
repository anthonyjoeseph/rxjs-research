{-# OPTIONS --guardedness #-}

-- THE ENGINE'S NEXT MARK IS THE STEPPER'S NEXT EVENT.  Per node,
-- what the engine's search finds under it (`operation.AbstractObservable.seek`) is
-- where and what `denotation.Unfold.step` shows next of its ghost
-- (`adequacy.Engine.Meaning.gh`), or a silent mark no later (`Agrees`); under a
-- closed observer, only silent marks (`Quiet`).  It holds of every state
-- of the fragment of / empty / map / merge / connect / joiner / cold
-- (`Frag`) by recursion on the
-- state (`head-agrees`): no order between nodes, no births, only each
-- node's own shape.  So it is not an invariant a step must preserve.
-- A connect (`conn-at`) races its source's skip against its body's mark;
-- a source not yet subscribed is the body's own silent mark, and the
-- stepper's first step of the fresh subscription lies no earlier
-- (`sub-head`, `sub-bursts`).  A connect lies only where nothing rests
-- (`NoConn`): its rest is the pool's race, outside this fragment.
-- The merge (`flat-at`) races the outer against the stepper's earliest
-- lane (`race`); the engine's oldest-first fold of its lanes meets the
-- stepper's newest-first search by one exchange (`swap`, `win-snoc`).
module adequacy.Engine.Head where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᴹ)
open import Data.Nat using (zero)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Pos; Timeline; _<ᵖ_; ix; emit; stall; close)
open import denotation.Unfold using (Node; Step; outˢ; skipˢ; endˢ; hushˢ; headˢ; step; restˢ; restsˢ; restᴹ; restsᶜ; restᶜ; unionˢ;
  Earliest; found; earliest; pick; Outer; doneᵒ; runᵒ; outerOf; goˢ; outerˢ; laneˢ; flatˢ;
  Source; live; ended; connectᶜ; burstingᶜ; underᶜ; subscribe; sourceˢ; bodyˢ; shutˢᵗ; burstsˢ; beforeˢ) renaming (none to noneᴱ)
open import operation.Key using (Key; at; after; _<ᴷ_)
open import operation.PureObservable using (module Machine; Tape; play; ending) renaming (over to overᵀ)

open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; Ctx; closed; inMap; inCut;
  Out; still; shows; Cand; seek; first; retag; mapT; cutT; nx; cp; attached; attAt; raceT; outerT; laneT; lanes; inOuter; inLanes; inLn; inScan; inTake; free; cpAt; cutAt; overAt;
  CS; cs; inSrc; inBody; own; ownBest; shift; over; sourceT; bodyM; owedM) renaming (found to foundᴹ)
open import adequacy.Engine.Meaning using (gh; lanesL; deadL; outerG; poolG)

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

-- No connect anywhere below.
mutual
  NoConn : ∀ {Γ A} → St Γ A → Set
  NoConn (mapS f s)              = NoConn s
  NoConn (scanS f z s)           = NoConn s
  NoConn (cutS l a s)            = NoConn s
  NoConn (lnS b s)               = NoConn s
  NoConn (takeS i q w s)         = NoConn s
  NoConn (flatS op f d n q o ls) = NoConn o × NoConns ls
  NoConn (connS k o b)           = ⊥
  NoConn _                       = ⊤

  NoConns : ∀ {Γ A} → List (St Γ A) → Set
  NoConns []       = ⊤
  NoConns (s ∷ ls) = NoConn s × NoConns ls

mutual
  Frag : ∀ {Γ A} → St Γ A → Set
  Frag (ofS i p xs)                           = ⊤
  Frag doneS                                  = ⊤
  Frag (mapS f s)                             = Frag s
  Frag (cutS true a s)                        = Frag s
  Frag (cutS false a s)                       = Frag s × NoConn s
  Frag (flatS (mergeᶠ nothing) f d n [] o ls) = Frag o × Lanes ls × n ≡ length (lanesL ls) × (d ≡ true → Done o × NoConn o)
  Frag (connS k o b)                          = Conn k o b
  Frag (joinS j g x ib)                       = ⊤
  Frag (coldS b l)                            = ⊤
  Frag (pend o)                               = ⊤
  Frag (scanS f z s)                          = Frag s
  Frag (takeS i q w s)                        = Frag s
  Frag (flatS (mergeᶠ (just m)) f d n q o ls) = Frag o × Lanes ls × n ≡ length (lanesL ls) × (d ≡ true → Done o × NoConn o)
  Frag (flatS switchᶠ f d n q o ls)           = Frag o × Lanes ls × n ≡ length (lanesL ls) × (d ≡ true → Done o × NoConn o)
  Frag (flatS exhaustᶠ f d n q o ls)          = Frag o × Lanes ls × n ≡ length (lanesL ls) × (d ≡ true → Done o × NoConn o)
  Frag _                                      = ⊥

  -- A connect whose source waits on its subscription mark, subscribed at
  -- the source's position; or whose source is subscribed.  Ended, its
  -- source rests on nothing; over, neither does its done body.
  Conn : ∀ {Γ X B} → CS → St Γ X → St (X ∷ Γ) B → Set
  Conn (cs cl sl sa (just p) nothing ow r e) (pend s) b =
    Frag b × r ≡ p ++ [ ix 1 ] × (over (cs cl sl sa (just p) nothing ow r e) ≡ true → Done b × NoConn b)
  Conn (cs cl sl sa nothing as ow r e) o b =
    Frag o × Frag b × (cl ≡ true → NoConn o) × (over (cs cl sl sa nothing as ow r e) ≡ true → NoConn o × Done b × NoConn b)
  Conn _ _ _ = ⊥

  -- Each lane live and switched on, or ended and switched off.
  Lanes : ∀ {Γ A} → List (St Γ A) → Set
  Lanes []       = ⊤
  Lanes (s ∷ ls) = Lane s × Lanes ls

  Lane : ∀ {Γ A} → St Γ A → Set
  Lane (lnS true (cutS true a s))   = Frag s
  Lane (lnS false (cutS false a s)) = Frag s × NoConn s
  Lane _                            = ⊥

  -- Over: nothing left to show.
  Done : ∀ {Γ A} → St Γ A → Set
  Done doneS                                       = ⊤
  Done (mapS f s)                                  = Done s
  Done (cutS l a s)                                = Done s
  Done (flatS (mergeᶠ nothing) f true zero [] o ls) = Done o
  Done (joinS j false x ib)                        = ⊤
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
  rest-hush : ∀ {Γ A B} (s : St Γ A) → Frag s → NoConn s → restˢ {B = B} (gh s) ≡ hushˢ
  rest-hush (ofS i p xs) _ _ = refl
  rest-hush doneS        _ _ = refl
  rest-hush (mapS f s)   fs ns = rest-hush s fs ns
  rest-hush (cutS true a s)  fs       ns = rest-hush s fs ns
  rest-hush (cutS false a s) (fs , _) ns = rest-hush s fs ns
  rest-hush (joinS j false x ib) _ _ = refl
  rest-hush (joinS j true x ib)  _ _ = refl
  rest-hush (connS k o b) _ ()
  rest-hush (pend o)        _  _  = refl
  rest-hush (scanS f z s)   fs ns = rest-hush s fs ns
  rest-hush (takeS i q free s)       fs ns = rest-hush s fs ns
  rest-hush (takeS i q (cpAt p) s)   fs ns = rest-hush s fs ns
  rest-hush (takeS i q (cutAt p) s)  fs ns = rest-hush s fs ns
  rest-hush (takeS i q (overAt p) s) fs ns = rest-hush s fs ns
  rest-hush {B = B} (flatS (mergeᶠ (just m)) f d n q o ls) (fo , fl , dd) (no , nls)
    rewrite outer-hush {B = B} d o fo no | rests-hush (live-hush {B = B} ls fl nls) | pool-hush {B = B} d o ls fo fl (λ _ → no) = refl
  rest-hush {B = B} (flatS switchᶠ f d n q o ls) (fo , fl , dd) (no , nls)
    rewrite outer-hush {B = B} d o fo no | rests-hush (live-hush {B = B} ls fl nls) | pool-hush {B = B} d o ls fo fl (λ _ → no) = refl
  rest-hush {B = B} (flatS exhaustᶠ f d n q o ls) (fo , fl , dd) (no , nls)
    rewrite outer-hush {B = B} d o fo no | rests-hush (live-hush {B = B} ls fl nls) | pool-hush {B = B} d o ls fo fl (λ _ → no) = refl
  rest-hush (coldS b (ending e))          _ _ = refl
  rest-hush (coldS b overᵀ)               _ _ = refl
  rest-hush (coldS true  (play τ u i t fr)) _ _ = refl
  rest-hush (coldS false (play τ u i t fr)) _ _ = refl
  rest-hush {B = B} (flatS (mergeᶠ nothing) f d n [] o ls) (fo , fl , _) (no , nls)
    rewrite outer-hush {B = B} d o fo no | rests-hush (live-hush {B = B} ls fl nls) | pool-hush {B = B} d o ls fo fl (λ _ → no) = refl

  outer-hush : ∀ {Γ A B} d (o : St Γ A) → Frag o → NoConn o → restᴹ {B = B} (outerG d (gh o)) ≡ hushˢ
  outer-hush true  o fo no = refl
  outer-hush false o fo no = rest-hush o fo no

  live-hush : ∀ {Γ A B} (ls : List (St Γ A)) → Lanes ls → NoConns ls → AllR B (lanesL ls)
  live-hush []                              _          _          = []
  live-hush (lnS true (cutS true a s) ∷ ls)   (fs , fl) (ns , nls) = allR-++ (live-hush ls fl nls) (rest-hush s fs ns ∷ [])
  live-hush (lnS false (cutS false a s) ∷ ls) (fs , fl) (ns , nls) = allR-++ (live-hush ls fl nls) []

  dead-hush : ∀ {Γ A B} (ls : List (St Γ A)) → Lanes ls → AllR B (deadL ls)
  dead-hush []                              _          = []
  dead-hush (lnS true (cutS true a s) ∷ ls)   (fs , fl) = dead-hush ls fl
  dead-hush (lnS false (cutS false a s) ∷ ls) ((fs , ns) , fl) = rest-hush s fs ns ∷ dead-hush ls fl

  pool-hush : ∀ {Γ A B C} d (o : St Γ A) (ls : List (St Γ C)) → Frag o → Lanes ls → (d ≡ true → NoConn o)
            → restˢ {B = B} (poolG d (gh o) (deadL ls)) ≡ hushˢ
  pool-hush false o ls fo fl dn = restsᶜ-hush (dead-hush ls fl)
  pool-hush {B = B} true o ls fo fl dn rewrite rest-hush {B = B} o fo (dn refl) = restsᶜ-hush (dead-hush ls fl)

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

-- A cold: its frame's next event where it sits, or the end it owes;
-- unsubscribed, a silent mark the stepper has no head against.
cold-head : ∀ {R Γ A} (c : Ctx R Γ A) b (l : Tape A) → Head c (coldS b l)
cold-head c b (ending e) with closed c
... | true  = calm
... | false = exact refl
cold-head c b overᵀ with closed c
... | true  = none
... | false = exact refl
cold-head c true (play τ u i t (emit a k)) with closed c
... | true  = calm
... | false = exact refl
cold-head c true (play τ u i t (stall k)) with closed c
... | true  = calm
... | false = exact refl
cold-head c true (play τ u i t (close k)) with closed c
... | true  = calm
... | false = exact refl
cold-head c false (play τ u i t (emit a k)) with closed c
... | true  = calm
... | false = early tt
cold-head c false (play τ u i t (stall k)) with closed c
... | true  = calm
... | false = early tt
cold-head c false (play τ u i t (close k)) with closed c
... | true  = calm
... | false = early tt

done-head : ∀ {R Γ A} (c : Ctx R Γ A) → Head c (doneS {A = A})
done-head c with closed c
... | true  = none
... | false = exact refl

-- Still to subscribe: no mark, and an idle ghost.
pend-head : ∀ {R Γ A} (c : Ctx R Γ A) (o : Obs Timeline Γ A) → Head c (pend o)
pend-head c o with closed c
... | true  = none
... | false = exact refl

-- The formers outside the merge fragment, one fact each.
postulate
  scanS-head : ∀ {R Γ A B} (c : Ctx R Γ B) (f : B → A → B) z (s : St Γ A) → Head (inScan f z c) s → Head c (scanS f z s)
  takeS-head : ∀ {R Γ A} (c : Ctx R Γ A) i q w (s : St Γ A) → Head (inTake i q w c) s → Head c (takeS i q w s)
  limit-head : ∀ {R Γ A B} (c : Ctx R Γ B) m (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls
             → Frag o → Lanes ls → (d ≡ true → Done o × NoConn o) → Head c (flatS (mergeᶠ (just m)) f d n q o ls)
  switch-head : ∀ {R Γ A B} (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls
              → Frag o → Lanes ls → (d ≡ true → Done o × NoConn o) → Head c (flatS switchᶠ f d n q o ls)
  exhaust-head : ∀ {R Γ A B} (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls
               → Frag o → Lanes ls → (d ≡ true → Done o × NoConn o) → Head c (flatS exhaustᶠ f d n q o ls)

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

off-head : ∀ {Γ A} b a (x : Maybe (Key × Out A)) (s : St Γ A) → Frag s → NoConn s → Quiet x → HeadAt b x (cutS false a s)
off-head true  a x s fs ns q = q
off-head {A = A} false a x s fs ns q rewrite rest-hush {B = A} s fs ns = quiet-hush q

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

pool-step : ∀ {Γ A B} d (o : St Γ A) (ls : List (St Γ B)) → Frag o → Lanes ls → (d ≡ true → NoConn o) → step (poolG d (gh o) (deadL ls)) ≡ hushˢ
pool-step false o ls fo fl dn = step-rests (dead-hush ls fl)
pool-step {B = B} true o ls fo fl dn =
  trans (cong (λ r → unionˢ (restᶜ (gh o)) r (restsᶜ (deadL ls)) (restˢ (restsᶜ {B = B} (deadL ls)))) (rest-hush {B = B} o fo (dn refl)))
        (restsᶜ-hush (dead-hush ls fl))

len0 : ∀ {a} {X : Set a} (xs : List X) → zero ≡ length xs → xs ≡ []
len0 []      _ = refl
len0 (_ ∷ _) ()

done-step : ∀ {Γ A} (s : St Γ A) → Frag s → Done s → step (gh s) ≡ hushˢ
done-step doneS            _  _  = refl
done-step (mapS f s)       fs ds rewrite done-step s fs ds = refl
done-step (cutS true a s)  fs ds = done-step s fs ds
done-step {A = A} (cutS false a s) (fs , ns) ds = rest-hush {B = A} s fs ns
done-step (joinS j false x ib) _ _ = refl
done-step (flatS (mergeᶠ nothing) f true zero [] o ls) (fo , fl , n0 , dd) ds
  rewrite pool-step true o ls fo fl (λ _ → proj₂ (dd refl)) | len0 (lanesL ls) n0 = refl
