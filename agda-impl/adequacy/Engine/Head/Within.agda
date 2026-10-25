{-# OPTIONS --guardedness #-}

-- EVERY NODE OF A FRAGMENT TREE IS OF THE FRAGMENT (`fr-at`), read down
-- the context: a lane is a switch over a node of the fragment, so a node
-- under a lane's switch is held as the lane's own (`Fr`).
module adequacy.Engine.Head.Within where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Timeline)
open import operation.PureObservable using (module Machine)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
  Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug; cs)
open import adequacy.Engine.Head using (Frag; Lanes; Lane; Conn)

-- A node's own share of the fragment: a lane's is its switch's.
Fr : ∀ {Γ A} → St Γ A → Set
Fr (lnS b s) = Frag s
Fr s         = Frag s

fr : ∀ {Γ A} (s : St Γ A) → Frag s → Fr s
fr (pend o)                f = f
fr (coldS b l)             f = f
fr (ofS i p xs)            f = f
fr doneS                   f = f
fr (mapS g s)              f = f
fr (scanS g z s)           f = f
fr (cutS l a s)            f = f
fr (lnS b s)               ()
fr (takeS i q w s)         f = f
fr (flatS op g d n q o ls) f = f
fr (connS k o b)           f = f
fr (joinS j g y ib)        f = f

-- A flatMap of the fragment: its outer and its lanes are.
frag-parts : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls → Frag (flatS op f d n q o ls) → Frag o × Lanes ls
frag-parts (mergeᶠ nothing)  f d n []      o ls (fo , fl , _) = fo , fl
frag-parts (mergeᶠ nothing)  f d n (_ ∷ _) o ls ()
frag-parts (mergeᶠ (just m)) f d n q       o ls (fo , fl , _) = fo , fl
frag-parts switchᶠ           f d n q       o ls (fo , fl , _) = fo , fl
frag-parts exhaustᶠ          f d n q       o ls (fo , fl , _) = fo , fl

-- The lanes after those passed.
lanes-ʳ++ : ∀ {Γ A} (pre : List (St Γ A)) {ys} → Lanes (pre ʳ++ ys) → Lanes ys
lanes-ʳ++ []        l = l
lanes-ʳ++ (x ∷ pre) l = proj₂ (lanes-ʳ++ pre l)

-- A lane's switch, held.
lane-fr : ∀ {Γ A} (s : St Γ A) → Lane s → Fr s
lane-fr (lnS true  (cutS true  a s))      l = l
lane-fr (lnS false (cutS false a s))      l = l
lane-fr (lnS true  (cutS false a s))      ()
lane-fr (lnS false (cutS true  a s))      ()
lane-fr (lnS true  (pend o))              ()
lane-fr (lnS false (pend o))              ()
lane-fr (lnS true  (coldS b l))           ()
lane-fr (lnS false (coldS b l))           ()
lane-fr (lnS true  (ofS i p xs))          ()
lane-fr (lnS false (ofS i p xs))          ()
lane-fr (lnS true  doneS)                 ()
lane-fr (lnS false doneS)                 ()
lane-fr (lnS true  (mapS g s))            ()
lane-fr (lnS false (mapS g s))            ()
lane-fr (lnS true  (scanS g z s))         ()
lane-fr (lnS false (scanS g z s))         ()
lane-fr (lnS true  (lnS b s))             ()
lane-fr (lnS false (lnS b s))             ()
lane-fr (lnS true  (takeS i q w s))       ()
lane-fr (lnS false (takeS i q w s))       ()
lane-fr (lnS true  (flatS op g d n q o ls)) ()
lane-fr (lnS false (flatS op g d n q o ls)) ()
lane-fr (lnS true  (connS k o b))         ()
lane-fr (lnS false (connS k o b))         ()
lane-fr (lnS true  (joinS j g y ib))      ()
lane-fr (lnS false (joinS j g y ib))      ()
lane-fr (pend o)                          ()
lane-fr (coldS b l)                       ()
lane-fr (ofS i p xs)                      ()
lane-fr doneS                             ()
lane-fr (mapS g s)                        ()
lane-fr (scanS g z s)                     ()
lane-fr (cutS l a s)                      ()
lane-fr (takeS i q w s)                   ()
lane-fr (flatS op g d n q o ls)           ()
lane-fr (connS k o b)                     ()
lane-fr (joinS j g y ib)                  ()

-- A connect's parts.
conn-src : ∀ {Γ X B} k (o : St Γ X) (b : St (X ∷ Γ) B) → Conn k o b → Frag o
conn-src (cs cl sl sa nothing as ow r e)         o        b (fo , _) = fo
conn-src (cs cl sl sa (just p) (just x) ow r e)  o        b ()
conn-src (cs cl sl sa (just p) nothing ow r e)   (pend s) b _        = tt
conn-src (cs cl sl sa (just p) nothing ow r e) (coldS x y) b ()
conn-src (cs cl sl sa (just p) nothing ow r e) (ofS x y z) b ()
conn-src (cs cl sl sa (just p) nothing ow r e) doneS b ()
conn-src (cs cl sl sa (just p) nothing ow r e) (mapS x y) b ()
conn-src (cs cl sl sa (just p) nothing ow r e) (scanS x y z) b ()
conn-src (cs cl sl sa (just p) nothing ow r e) (cutS x y z) b ()
conn-src (cs cl sl sa (just p) nothing ow r e) (lnS x y) b ()
conn-src (cs cl sl sa (just p) nothing ow r e) (takeS x y z w) b ()
conn-src (cs cl sl sa (just p) nothing ow r e) (flatS x y z w u v t) b ()
conn-src (cs cl sl sa (just p) nothing ow r e) (connS x y z) b ()
conn-src (cs cl sl sa (just p) nothing ow r e) (joinS x y z w) b ()

conn-body : ∀ {Γ X B} k (o : St Γ X) (b : St (X ∷ Γ) B) → Conn k o b → Frag b
conn-body (cs cl sl sa nothing as ow r e)        o        b (_ , fb , _) = fb
conn-body (cs cl sl sa (just p) (just x) ow r e) o        b ()
conn-body (cs cl sl sa (just p) nothing ow r e)  (pend s) b (fb , _)     = fb
conn-body (cs cl sl sa (just p) nothing ow r e) (coldS x y) b ()
conn-body (cs cl sl sa (just p) nothing ow r e) (ofS x y z) b ()
conn-body (cs cl sl sa (just p) nothing ow r e) doneS b ()
conn-body (cs cl sl sa (just p) nothing ow r e) (mapS x y) b ()
conn-body (cs cl sl sa (just p) nothing ow r e) (scanS x y z) b ()
conn-body (cs cl sl sa (just p) nothing ow r e) (cutS x y z) b ()
conn-body (cs cl sl sa (just p) nothing ow r e) (lnS x y) b ()
conn-body (cs cl sl sa (just p) nothing ow r e) (takeS x y z w) b ()
conn-body (cs cl sl sa (just p) nothing ow r e) (flatS x y z w u v t) b ()
conn-body (cs cl sl sa (just p) nothing ow r e) (connS x y z) b ()
conn-body (cs cl sl sa (just p) nothing ow r e) (joinS x y z w) b ()

-- Every node of a fragment tree, held.
fr-at : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Frag (plug c s) → Fr s
fr-at top                               s f = fr s f
fr-at (inMap g c)                       s f = fr s (fr-at c (mapS g s) f)
fr-at (inScan g z c)                    s f = fr s (fr-at c (scanS g z s) f)
fr-at (inCut true a c)                  s f = fr s (fr-at c (cutS true a s) f)
fr-at (inCut false a c)                 s f = fr s (proj₁ (fr-at c (cutS false a s) f))
fr-at (inLn b c)                        s f = fr s (fr-at c (lnS b s) f)
fr-at (inTake i q w c)                  s f = fr s (fr-at c (takeS i q w s) f)
fr-at (inOuter op g d n q ls c)         s f = fr s (proj₁ (frag-parts op g d n q s ls (fr-at c (flatS op g d n q s ls) f)))
fr-at (inLanes op g d n q o pre post c) s f =
  lane-fr s (proj₁ (lanes-ʳ++ pre (proj₂ (frag-parts op g d n q o (pre ʳ++ s ∷ post) (fr-at c (flatS op g d n q o (pre ʳ++ s ∷ post)) f)))))
fr-at (inSrc k b c)                     s f = fr s (conn-src k s b (fr-at c (connS k s b) f))
fr-at (inBody k o c)                    s f = fr s (conn-body k o s (fr-at c (connS k o s) f))

-- A flatMap of a fragment tree is of the fragment.
frag-flat : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls
          → Frag (plug c (flatS op f d n q o ls)) → Frag (flatS op f d n q o ls)
frag-flat c op f d n q o ls = fr-at c (flatS op f d n q o ls)

-- A connect's body in a fragment tree is of the fragment.
frag-body : ∀ {R Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → Frag (plug c (connS k o b)) → Frag b
frag-body c k o b f = conn-body k o b (fr-at c (connS k o b) f)
