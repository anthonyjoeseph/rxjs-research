{-# OPTIONS --guardedness #-}

-- A NODE'S KEYS BOUND WHAT IT OWES: no node owes a visible row before the
-- least key its subtree holds.  Every row a node still owes is shown by
-- one of its own marks, keyed at or before it — an of's next, a cold's
-- next, a takeWhile's owed end, a joiner's inbox head, a connect's source
-- subscription — or is a child's row, which the child bounds; a joiner's
-- unfed rows are its binder's, which the binder's own subtree bounds
-- (`Env`).
module adequacy.Bound where

open import Data.Bool using (Bool; T; true; false; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; lookup) renaming (_∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; Timeline; ix; last; ofᴱ)
open import denotation.Read using (Visible)
open import denotation.EmissionSet using (EmissionSet; out; end; skip; pin; _≺_; _≼_; Den; hot; coldAt; DenEnv; ⟦_⟧; Ended;
  shown; heard; ended; late; InE; at-out; at-end; on-out; MapT; map-out; map-end; map-skip; map-pin;
  LaneOf; module Joining; module Scan; module TakeWhile; module Connecting; module Bounded; module Switch; module Exhaust)
open import denotation.Laws.Modulus using (≼-trans; ≺-≼-≺; ≼-≺-≺; ≺→≼; ≺-ext; ≺-trans; ≼-antisym; ≼-refl; ≼-or-≻)
open import denotation.Laws.Worlds using (Ok; Hots; InvAt; GoodEnv; world-after; ok-step)
open import denotation.Laws using (inv-⟦⟧; good-cons)
open import denotation.Laws.HotInv using (lawful-hot)
open import denotation.Laws.ColdInv using (slot; slot-last; burst-lb)
import denotation.Laws.Connect as LC
open import operation.Key using (at; at-<ᴷ)
open import operation.PureObservable using (module Machine; Tape; play; ending) renaming (over to tapeOver)
open Machine using (St; Scope; unbound; binds; CS; cs; own; bodyM; cpAt; coldS; ofS; takeS; flatS; connS; joinS)
open import adequacy.Rows using (full; pendRows; Frozen; Inbox; this; that; tapeE)
open import adequacy.Rows using (_≃_; ≼-≢)
open _≃_
open import adequacy.Cursor using (Cur; origin; bef; aft; Owes; Due; Unfed; Adm; Ticked; Pol; Lane; Runs; Start; Kill; polF;
  JoinF; h-live; h-end; h-kill; LaneSt; l-live; l-dead; Begun; more; Joined; joined; Ends;
  Flags; Src; src-pend; src-on; src-shut; Failure; Gone; notT; Sound; OweAt; o-cp; o-cut;
  o-over; Behind; FewBefore; few-behind; alike; Sync; s-cold; s-of; s-done; s-map; s-scan;
  s-cut; s-take; s-took; s-flat; s-conn; s-join; s-joinx)
open import adequacy.Least using (KeyIn; k-own; k-kid; k-map; k-scan; k-cut; k-ln; k-take; k-outer; k-lane; k-src; k-body; Lo)

------------------------------------------------------------------------
-- The order, with its positions explicit

tr : ∀ x y z → x ≼ y → y ≼ z → x ≼ z
tr x y z = ≼-trans {x} {y} {z}

on : ∀ x y z → x ≼ y → y ≺ z → x ≼ z
on x y z a b = ≺→≼ {x} {z} (≼-≺-≺ {x} {y} {z} a b)

lt : ∀ x y z → x ≺ y → y ≺ z → x ≺ z
lt x y z = ≺-trans {x} {y} {z}

-- Owed at one position, owed at every later one.
owes-≼ : ∀ C {k r} → Owes C k → k ≼ r → Owes C r
owes-≼ origin  _  _  = tt
owes-≼ (bef p) {k} {r} pk kr = ≼-trans {p} {k} {r} pk kr
owes-≼ (aft p) {k} {r} pk kr = ≺-≼-≺ {p} {k} {r} pk kr

owes? : ∀ C q → Owes C q ⊎ ¬ Owes C q
owes? origin  q = inj₁ tt
owes? (bef p) q with ≼-or-≻ p q
... | inj₁ pq = inj₁ pq
... | inj₂ qp = inj₂ λ pq → pq qp
owes? (aft p) q with ≼-or-≻ q p
... | inj₁ qp = inj₂ λ pq → qp pq
... | inj₂ pq = inj₁ pq

-- Passed and then owed: strictly before.
past : ∀ C {a b} → ¬ Owes C a → Owes C b → a ≺ b
past origin  na _ = ⊥-elim (na tt)
past (bef p) {a} {b} na pb with ≼-or-≻ p a
... | inj₁ pa = ⊥-elim (na pa)
... | inj₂ ap = ≺-≼-≺ {a} {p} {b} ap pb
past (aft p) {a} {b} na pb = ≼-≺-≺ {a} {p} {b} na pb

T? : ∀ b → T b ⊎ T (not b)
T? true  = inj₁ tt
T? false = inj₂ tt

-- A key of the subtree no earlier than `at p`: its position at or past `p`.
lo-at : ∀ {Γ A} {s : St Γ A} {p k} → Lo s (at p) → KeyIn s (at k) → p ≼ k
lo-at {p = p} {k} lo ki t = subst T (trans (sym (at-<ᴷ k p)) (lo ki)) t

------------------------------------------------------------------------
-- What the binders in scope owe

-- A hot's rows the cursor has not passed lie at or past `p`.
Lies : ∀ {A} → Cur → Pos → Den A → Set
Lies C p (hot t)    = ∀ {q e} → Due C t q e → p ≼ q
Lies C p (coldAt _) = ⊤

-- Every binder's.
Env : ∀ {Γ} → DenEnv Γ → Cur → Pos → Set₁
Env {Γ} ρ C p = ∀ {A} (x : A ∈ Γ) → Lies C p (lookup ρ x)

env-bind : ∀ {Γ X} {sc : Scope Γ} {C p} {o : Obs Timeline Γ X} {r}
         → (∀ {q e} → Due C (pendRows (full sc) o (r ++ [ ix 1 ])) q e → p ≼ q) → Env (full sc) C p → Env (full (binds o r sc)) C p
env-bind h env (here refl) ((x , _) , v , ok) = h (x , v , ok)
env-bind h env (there x)                      = env x

-- A joiner's unfed rows: its binder's, rejoined past them.
unfed-b : ∀ {A C p j} (d : Den A) → Lies C p d → ∀ {q e} → Due C (Unfed C d j) q e → p ≼ q
unfed-b {p = p} {j} (hot t) h (shown {q} {e = out _} (x , o) _ _ , _ , _) = on p q (q ++ [ _ ]) (h (x , tt , o)) (≺-ext q [])
unfed-b (hot t) h (shown {e = skip} _ _ _ , () , _)
unfed-b (hot t) h (shown {e = end} _ () _ , _ , _)
unfed-b (hot t) h (shown {e = pin _} _ () _ , _ , _)
unfed-b (hot t) h (heard _ _ , () , _)
unfed-b {p = p} (hot t) h (ended {c} (x , o) _ , _ , _) = on p c (c ++ [ _ ]) (h (x , tt , o)) (≺-ext c [])
unfed-b {p = p} {j} (hot t) h (late {c} (x , o) cj , _ , _) = on p j (j ++ [ last ]) (tr p c j (h (x , tt , o)) cj) (≺-ext j [])
unfed-b (coldAt _) _ (() , _ , _)

-- The binders of an admissible scope, each a lawful hot.
good-full : ∀ {Γ} (sc : Scope Γ) → Adm sc → GoodEnv (full sc)
good-full unbound        _        ()
good-full (binds o p sc) (ok , a) = good-cons (LC.lawful {s = ⟦ o ⟧ (full sc)} {F = λ h → h} (inv-⟦⟧ o (full sc) g) (λ L → lawful-hot L) p ok) g
  where g = good-full sc a

-- A subscription made at `q` under an admissible scope: its rows past `q`.
pend-past : ∀ {Γ A} (sc : Scope Γ) (o : Obs Timeline Γ A) {q} → Adm sc → Ok (Hots (full sc)) q
          → ∀ {k e} → pendRows (full sc) o q k e → q ≺ k
pend-past sc o {q} a ok r = world-after (InvAt.world I r) (InvAt.real I r)
  where I = inv-⟦⟧ o (full sc) (good-full sc a) q ok

------------------------------------------------------------------------
-- The leaves' rows

-- An of's next: its next value's slot, or its end once none is left.
ofKey : ∀ {A : Set} → Pos → ℕ → List A → Pos
ofKey p i []      = p ++ [ last ]
ofKey p i (_ ∷ _) = p ++ [ ix i ]

of-next : ∀ {A} p i (xs : List A) → (p ++ [ ix i ]) ≺ ofKey p (suc i) xs
of-next p i []      = slot-last p i
of-next p i (_ ∷ _) = slot p i

of-lb : ∀ {A} p i (xs : List A) {y e} → InE (ofᴱ p i xs) y e → ofKey p i xs ≼ y
of-lb p i []       at-end     = ≼-refl {p ++ [ last ]}
of-lb p i (x ∷ xs) at-out     = ≼-refl {p ++ [ ix i ]}
of-lb p i (x ∷ xs) {y} (on-out r) =
  ≺→≼ {p ++ [ ix i ]} {y} (≺-≼-≺ {p ++ [ ix i ]} {ofKey p (suc i) xs} {y} (of-next p i xs) (of-lb p (suc i) xs r))

cold-b : ∀ {Γ A p y e} (l : Tape A) → Ticked l → Lo (coldS {Γ} true l) (at p) → InE (tapeE l) y e → p ≼ y
cold-b {p = p} {y} (play τ u i t fr) (re , le) lo r = tr p (u ++ [ ix i ]) y (lo-at lo (k-own (here refl))) (burst-lb τ u i fr re le r)
cold-b (ending c) _ lo at-end = lo-at lo (k-own (here refl))
cold-b tapeOver   _ _  ()

------------------------------------------------------------------------
-- A joiner's visible rows: its outer's end, or a running lane's row no
-- later value has cut

module _ {A B : Set} (L : Pos → A → EmissionSet B) (O : EmissionSet A) (Over : Pos → Set) (R : Pos → Set)
         (Cut : Pos → Pos → Set) (Hand : Pos → Set) where
  open Joining L O (λ _ _ → ⊥) Over R Cut Hand

  jrow : ∀ {k e} → JoinT k e → Visible e → O k end ⊎ Σ Pos λ q → Σ A λ a → O q (out a) × R q × L q a k e × ¬ Cut q k
  jrow (oend x _)           _  = inj₁ x
  jrow (lane x r l nc _)    _  = inj₂ (_ , _ , x , r , l , nc)
  jrow (lend x r l nc _ _)  _  = inj₂ (_ , _ , x , r , l , nc)
  jrow (val _)              ()
  jrow (step _)             ()
  jrow (opin _)             ()
  jrow (opass _ _)          ()
  jrow (lpass _ _ _ _ _ _)  ()
  jrow (hand _ _ _ _ _)     ()
  jrow (left _ _ _ _ _)     ()
  jrow (run () _)           _
  jrow (rend () _ _)        _
  jrow (rpass () _ _)       _
  jrow (rhand () _)         _

nokill : ∀ {A B : Set} {O : EmissionSet A} {k e} (L : Pos → A → EmissionSet B) (R : Pos → Set)
     → O k end ⊎ Σ Pos (λ q → Σ A λ a → O q (out a) × R q × L q a k e × ¬ ⊥)
     → O k end ⊎ Σ Pos (λ q → Σ A λ a → O q (out a) × R q × L q a k e × (∀ {q′} → ⊥ → k ≼ q′))
nokill L R (inj₁ x)                      = inj₁ x
nokill L R (inj₂ (q , a , x , r , l , _)) = inj₂ (q , a , x , r , l , λ ())

join-row : ∀ {A B} op (F : A → Den B) (O : EmissionSet A) {k e} → JoinF op F O k e → Visible e
         → O k end ⊎ Σ Pos λ q → Σ A λ a → O q (out a) × Runs (polF op F O) q × Lane (polF op F O) q a k e
             × (∀ {q′} → Kill (polF op F O) q q′ → k ≼ q′)
join-row (mergeᶠ nothing)  F O r v = nokill {O = O} (LaneOf F) (λ _ → ⊤) (jrow (LaneOf F) O (Ended O) (λ _ → ⊤) (λ _ _ → ⊥) (λ _ → ⊥) r v)
join-row (mergeᶠ (just m)) F O r v =
  nokill {O = O} (Bounded.Lane m F O) (Bounded.Indexed m F O) (jrow (Bounded.Lane m F O) O (Ended O) (Bounded.Indexed m F O) (λ _ _ → ⊥) (Bounded.Queued m F O) r v)
join-row exhaustᶠ          F O r v = nokill {O = O} (LaneOf F) (Exhaust.Run F O) (jrow (LaneOf F) O (Ended O) (Exhaust.Run F O) (λ _ _ → ⊥) (λ _ → ⊥) r v)
join-row switchᶠ           F O {k} r v with jrow (LaneOf F) O (Ended O) (λ _ → ⊤) (Switch.Cut F O) (λ _ → ⊥) r v
... | inj₁ x                       = inj₁ x
... | inj₂ (q , a , x , ru , l , nc) = inj₂ (q , a , x , ru , l , λ { {q′} (a′ , x′ , qq′) q′k → nc (q′ , a′ , x′ , qq′ , q′k) })

-- Where a bounded lane starts: past its value.
starts-past : ∀ {A B} m (F : A → Den B) (O : EmissionSet A) {i q ls s} → Bounded.Starts m F O i q ls s → q ≺ s
starts-past m F O {q = q} (Bounded.room _)    = ≺-ext q []
starts-past m F O {q = q} (Bounded.freed _ _) = ≺-ext q []
starts-past m F O {q = q} (Bounded.queued {c} _ qc _ _ _) = lt q c (c ++ [ ix 1 ]) qc (≺-ext c [])

-- A lane's row: past its start, which is past its value.
lane-st : ∀ {A B} op (F : A → Den B) (O : EmissionSet A) {q a k e} → Lane (polF op F O) q a k e
        → Σ Pos λ s → Start (polF op F O) q a s × q ≺ s × s ≺ k
lane-st (mergeᶠ nothing)  F O {q} (_ , sk) = q ++ [ ix 1 ] , refl , ≺-ext q [] , sk
lane-st (mergeᶠ (just m)) F O (i , s , sb , _ , sk) = s , (i , sb) , starts-past m F O (proj₂ sb) , sk
lane-st switchᶠ           F O {q} (_ , sk) = q ++ [ ix 1 ] , refl , ≺-ext q [] , sk
lane-st exhaustᶠ          F O {q} (_ , sk) = q ++ [ ix 1 ] , refl , ≺-ext q [] , sk

------------------------------------------------------------------------
-- Reading a key off a node's own marks

body-key : ∀ {Γ X B} (k : CS Γ X) {o} {b : St (X ∷ Γ) B} → CS.bodyAt k ≡ just (CS.connAt k)
         → (bodyM , at (CS.connAt k ++ [ ix 1 ])) ∈ own (connS k o b)
body-key (cs _ _ _ (just _) _ _ _ _ _ _) refl = here refl

inbox-lt : ∀ {A} {q₀ : Pos} {ib : List (Pos × Machine.Ev A)} {q e} → All (λ v → q₀ ≺ proj₁ v) ib → Inbox {A} ib q e → q₀ ≺ q
inbox-lt (h ∷ᴬ _)  this     = h
inbox-lt {q₀ = q₀} (_ ∷ᴬ hs) (that i) = inbox-lt {q₀ = q₀} hs i

------------------------------------------------------------------------
-- THE BOUND

mutual
  bound : ∀ {Γ} {sc : Scope Γ} {Rg} {C A} {s : St Γ A} {E p} → Sync sc Rg C s E → Env (full sc) C p → Lo s (at p)
        → ∀ {q e} → Due C E q e → p ≼ q
  bound (s-cold {l = l} tk d _) env lo r = cold-b l tk lo (proj₁ (to d r))
  bound {p = p} (s-of {i = i} {q = q₀} {xs = []} d _) env lo {q} r =
    tr p (q₀ ++ [ last ]) q (lo-at lo (k-own (here refl))) (of-lb q₀ i [] (proj₁ (to d r)))
  bound {p = p} (s-of {i = i} {q = q₀} {xs = x ∷ xs} d _) env lo {q} r =
    tr p (q₀ ++ [ ix i ]) q (lo-at lo (k-own (here refl))) (of-lb q₀ i (x ∷ xs) (proj₁ (to d r)))
  bound (s-done sp _) env lo r = ⊥-elim (sp r)
  bound (s-map sy m _) env lo (x , v , ow) = map-b sy env (λ ki → lo (k-kid (k-map ki))) (from (alike m) (x , v)) ow
  bound (s-scan sy _ m _) env lo (x , v , ow) = scan-b sy env (λ ki → lo (k-kid (k-scan ki))) (from (alike m) (x , v)) ow
  bound (s-cut sy) env lo r = bound sy env (λ ki → lo (k-kid (k-cut ki))) r
  bound (s-take sy nf m _) env lo (x , v , ow) = take-b sy nf env (λ ki → lo (k-kid (k-take ki))) (from (alike m) (x , v)) ow
  bound (s-took fl g ni oa _ m sd) env lo (x , v , ow) = took-b fl g ni oa sd lo (from (alike m) (x , v)) ow
  bound (s-flat _ sy jn m _ _) env lo (x , v , ow) = flat-b sy jn env lo (proj₁ (proj₁ (from (alike (proj₂ m)) (x , v)))) v ow
  bound (s-conn refl _ bs ss fl m) env lo (x , v , ow) = let ((y , _) , v′) = from (alike (proj₁ m)) (x , v) in conn-b bs ss fl env lo (y , v′) ow
  bound {sc = sc} (s-join _ d ap _ _) env lo r = join-b {sc = sc} d ap env lo r
  bound (s-joinx sp _) env lo r = ⊥-elim (sp r)

  map-b : ∀ {Γ} {sc : Scope Γ} {Rg} {C A B} {f : A → B} {s : St Γ A} {Es p q e}
        → Sync sc Rg C s Es → Env (full sc) C p → Lo s (at p)
        → Σ (MapT f Es q e) (λ _ → Visible e) → Owes C q → p ≼ q
  map-b sy env lo (map-out y , _) ow = bound sy env lo (y , tt , ow)
  map-b sy env lo (map-end y , _) ow = bound sy env lo (y , tt , ow)
  map-b sy env lo (map-skip _ , ()) ow
  map-b sy env lo (map-pin _ , ()) ow

  scan-b : ∀ {Γ} {sc : Scope Γ} {Rg} {C A B} {f : B → A → B} {z₀} {s : St Γ A} {Es p q e}
         → Sync sc Rg C s Es → Env (full sc) C p → Lo s (at p)
         → Σ (Scan.ScanT f z₀ Es q e) (λ _ → Visible e) → Owes C q → p ≼ q
  scan-b sy env lo (Scan.sval (Scan.acc₀ y _) , _)     ow = bound sy env lo (y , tt , ow)
  scan-b sy env lo (Scan.sval (Scan.acc _ y _ _) , _)  ow = bound sy env lo (y , tt , ow)
  scan-b sy env lo (Scan.send y , _)                   ow = bound sy env lo (y , tt , ow)
  scan-b sy env lo (Scan.sstep _ , ())                 ow
  scan-b sy env lo (Scan.spin _ , ())                  ow

  take-b : ∀ {Γ} {sc : Scope Γ} {Rg} {C A} {i} {keep : A → Bool} {s : St Γ A} {Es p q e}
         → Sync sc Rg C s Es → (∀ {q a} → Es q (out a) → T (not (keep a)) → Owes C q) → Env (full sc) C p → Lo s (at p)
         → Σ (TakeWhile.TakeT i keep Es q e) (λ _ → Visible e) → Owes C q → p ≼ q
  take-b sy nf env lo (TakeWhile.pass y _ _ , _) ow = bound sy env lo (y , tt , ow)
  take-b sy nf env lo (TakeWhile.tend y _ , _)   ow = bound sy env lo (y , tt , ow)
  take-b {p = p} sy nf env lo (TakeWhile.fail {q} y nk _ _ , _) ow = on p q (q ++ [ ix 0 ]) (bound sy env lo (y , tt , nf y nk)) (≺-ext q [])
  take-b {p = p} sy nf env lo (TakeWhile.stop {q} y nk _ , _)   ow = on p q (q ++ [ last ]) (bound sy env lo (y , tt , nf y nk)) (≺-ext q [])
  take-b sy nf env lo (TakeWhile.step _ _ , ())   ow
  take-b sy nf env lo (TakeWhile.left _ _ _ , ()) ow

  took-b : ∀ {Γ Rg C A} {i} {keep : A → Bool} {w} {s : St Γ A} {Es r p q e}
         → Failure keep Es r → Gone C r → (T i → ¬ Owes C (r ++ [ ix 0 ])) → OweAt C w r → Sound Rg Es → Lo (takeS i keep w s) (at p)
         → Σ (TakeWhile.TakeT i keep Es q e) (λ _ → Visible e) → Owes C q → p ≼ q
  took-b {keep = keep} {r = r} {q = q} (a , y , nk , nf) g ni oa sd lo (TakeWhile.pass y′ kp nfq , _) ow =
    ⊥-elim (nfq (r , a , y , nk , ≼-≢ {r} {q} (g ow) λ { refl → kept (Sound.fn sd y y′ _ _) nk kp }))
    where
      kept : ∀ {b b′} → out b ≡ out b′ → T (not (keep b)) → T (keep b′) → ⊥
      kept {b} refl nb kb = notT (keep b) nb kb
  took-b {r = r} {q = q} (a , y , nk , nf) g ni oa sd lo (TakeWhile.tend y′ nfq , _) ow =
    ⊥-elim (nfq (r , a , y , nk , ≼-≢ {r} {q} (g ow) λ { refl → no-end (Sound.fn sd y y′ _ _) }))
    where
      no-end : ∀ {b} → out b ≡ end → ⊥
      no-end ()
  took-b {C = C} {r = r} (a , y , nk , nf) nr ni oa sd lo (TakeWhile.fail {q} y′ nk′ nfq inc , _) ow
    with ≼-antisym {q} {r} (λ rq → nfq (r , a , y , nk , rq)) (λ qr → nf (q , _ , y′ , nk′ , qr))
  ... | refl = ⊥-elim (ni inc ow)
  took-b {C = C} {r = r} (a , y , nk , nf) nr ni oa sd lo (TakeWhile.stop {q} y′ nk′ nfq , _) ow
    with ≼-antisym {q} {r} (λ rq → nfq (r , a , y , nk , rq)) (λ qr → nf (q , _ , y′ , nk′ , qr))
  ... | refl = took-end oa lo ow
  took-b fl nr ni oa sd lo (TakeWhile.step _ _ , ())   ow
  took-b fl nr ni oa sd lo (TakeWhile.left _ _ _ , ()) ow

  took-end : ∀ {Γ C A} {i} {keep : A → Bool} {w} {s : St Γ A} {r p}
           → OweAt C w r → Lo (takeS i keep w s) (at p) → Owes C (r ++ [ last ]) → p ≼ (r ++ [ last ])
  took-end (o-cp _)    lo ow = lo-at lo (k-own (here refl))
  took-end (o-cut no)  lo ow = ⊥-elim (no ow)
  took-end (o-over no) lo ow = ⊥-elim (no ow)

  conn-b : ∀ {Γ X B} {Rb Rs C} {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) B} {β p q e}
         → (T (CS.srcLive k) → Sync (binds (CS.src k) (CS.connAt k) (CS.scope k)) Rb C b β)
         → (T (CS.srcLive k) → Src (CS.scope k) Rs C k o) → Flags C k β
         → Env (full (CS.scope k)) C p → Lo (connS k o b) (at p)
         → Σ (Connecting.ConnT (CS.connAt k) (adequacy.Rows.Frozen k) β q e) (λ _ → Visible e) → Owes C q → p ≼ q
  conn-b {k = k} bs ss fl env lo (Connecting.body y , v) ow with T? (CS.srcLive k)
  ... | inj₁ t  = bound (bs t) (env-bind {o = CS.src k} {r = CS.connAt k} (src-b (ss t) env lo) env) (λ ki → lo (k-kid (k-body ki))) (y , v , ow)
  ... | inj₂ nt = ⊥-elim (Flags.torn fl nt (y , v , ow))
  conn-b bs ss fl env lo (Connecting.burst _ _ , ())     ow
  conn-b bs ss fl env lo (Connecting.echo _ _ _ _ , ())  ow
  conn-b bs ss fl env lo (Connecting.kept _ _ _ _ , ())  ow

  src-b : ∀ {Γ X B} {Rg C} {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) B} {p}
        → Src (CS.scope k) Rg C k o → Env (full (CS.scope k)) C p → Lo (connS k o b) (at p)
        → ∀ {q e} → Due C (adequacy.Rows.Frozen k) q e → p ≼ q
  src-b (src-on _ sy _) env lo r = bound sy env (λ ki → lo (k-kid (k-src ki))) r
  src-b (src-shut _ sp _ _) env lo r = ⊥-elim (sp r)
  src-b {k = k} {b = b} {p = p} (src-pend {o = o′} _ be (ok , a) _ _ _) env lo {q} (x , _ , _) =
    on p (CS.connAt k ++ [ ix 1 ]) q (lo-at lo (k-own (body-key k {o = Machine.pend o′ (CS.connAt k ++ [ ix 1 ])} {b = b} be)))
       (pend-past (CS.scope k) (CS.src k) a (ok-step {Hots (full (CS.scope k))} (CS.connAt k) ok) x)

  join-b : ∀ {Γ} {sc : Scope Γ} {C A} {j} {x : A ∈ Γ} {ib E p}
         → (Due C E ≃ λ q e → Inbox ib q e ⊎ Due C (Unfed C (lookup (full sc) x) j) q e)
         → AllPairs (λ u v → proj₁ u ≺ proj₁ v) ib
         → Env (full sc) C p → Lo (joinS j true x ib) (at p) → ∀ {q e} → Due C E q e → p ≼ q
  join-b {sc = sc} {x = x} d ap env lo r with to d r
  ... | inj₂ u = unfed-b (lookup (full sc) x) (env x) u
  join-b {ib = (q₀ , _) ∷ _} d (h ∷ _) env lo r | inj₁ this = lo-at lo (k-own (here refl))
  join-b {ib = (q₀ , _) ∷ _} {p = p} d (h ∷ _) env lo {q} r | inj₁ (that i) = on p q₀ q (lo-at lo (k-own (here refl))) (inbox-lt {q₀ = q₀} h i)

  flat-b : ∀ {Γ} {sc : Scope Γ} {Rg Rl} {C A B} {op} {f : A → Obs Timeline Γ B} {ω} {d n qu o ls O p k e}
         → Sync sc Rg C o O → Joined sc Rl C (polF op (λ a → ⟦ f a ⟧ (full sc)) O) O d n qu ls
         → Env (full sc) C p → Lo (flatS op f ω d n qu o ls) (at p)
         → JoinF op (λ a → ⟦ f a ⟧ (full sc)) O k e → Visible e → Owes C k → p ≼ k
  flat-b {sc = sc} {C = C} {op = op} {f} {O = O} {p} {k} sy (joined bg _ wh _ ah _ en _) env lo r v ow
    with join-row op (λ a → ⟦ f a ⟧ (full sc)) O r v
  ... | inj₁ y = bound sy env (λ ki → lo (k-kid (k-outer ki))) (y , tt , ow)
  ... | inj₂ (q , a , y , ru , ln , kl) with lane-st op (λ a → ⟦ f a ⟧ (full sc)) O ln | owes? C q
  ...   | s , st , qs , sk | inj₁ oq =
          on p q k (bound sy env (λ ki → lo (k-kid (k-outer ki))) (y , tt , oq)) (lt q s k qs sk)
  ...   | s , st , qs , sk | inj₂ nq with wh y nq ru
  ...     | inj₁ iv = begun-b {O = O} bg iv kl ln v ow en env (λ i ki → lo (k-kid (k-lane i ki)))
  ...     | inj₂ iw with ah iw st
  ...       | q′ , a′ , c , iv′ , lc , kc , oc , cs′ =
              on p c k (begun-b {O = O} {k = c} {e = end} bg iv′ kc lc tt oc en env (λ i ki → lo (k-kid (k-lane i ki)))) (lt c s k cs′ sk)

  begun-b : ∀ {Γ} {sc : Scope Γ} {Rl} {C A B} {P : Pol A B} {O vs ls n q a k e p}
          → Begun sc Rl C P O vs ls n → (q , a) ∈ vs → (∀ {q′} → Kill P q q′ → k ≼ q′) → Lane P q a k e → Visible e → Owes C k
          → Ends P O → Env (full sc) C p → (∀ {l} → l ∈ ls → Lo l (at p)) → p ≼ k
  begun-b {O = O} (more y _ _ ls _)  (here refl) kl ln v ow en env lo = lane-b {O = O} ls y kl ln v ow en env (lo (here refl))
  begun-b {O = O} (more _ _ _ _ bg) (there i)   kl ln v ow en env lo = begun-b {O = O} bg i kl ln v ow en env (λ i′ → lo (there i′))

  lane-b : ∀ {Γ} {sc : Scope Γ} {Rg} {C A B} {P : Pol A B} {O q a l b k e p}
         → LaneSt sc Rg C P q a l b → O q (out a) → (∀ {q′} → Kill P q q′ → k ≼ q′) → Lane P q a k e → Visible e → Owes C k
         → Ends P O → Env (full sc) C p → Lo l (at p) → p ≼ k
  lane-b (l-live (h-live _ _ eq) sy _) _ _ ln v ow _ env lo =
    bound sy env (λ ki → lo (k-kid (k-ln (k-kid (k-cut ki))))) (proj₁ (to (alike eq) (ln , v)) , v , ow)
  lane-b {C = C} (l-dead (h-end lc nc _)) y _ ln v ow en _ _ = ⊥-elim (nc (owes-≼ C ow (en y lc ln v)))
  lane-b {C = C} (l-dead (h-kill kq nq _)) _ kl _ _ ow _ _ _ = ⊥-elim (nq (owes-≼ C ow (kl kq)))

------------------------------------------------------------------------
-- What a part has passed

-- Nothing passed yet: every row past an owed position.
behind-past : ∀ {A} C {q} {E : EmissionSet A} → Owes C q → (∀ {k e} → E k e → q ≺ k) → Behind C E
behind-past C {q} ow ps = [] , λ {k} r no → ⊥-elim (no (owes-≼ C ow (≺→≼ {q} {k} (ps r))))

-- A source not yet subscribed: nothing of it passed.
behind-pend : ∀ {Γ X} {sc : Scope Γ} {C} {k : CS Γ X} → CS.scope k ≡ sc → Adm (binds (CS.src k) (CS.connAt k) sc)
            → Owes C (CS.connAt k ++ [ ix 1 ]) → Behind C (Frozen k)
behind-pend {C = C} {k = k} refl (ok , a) ow =
  behind-past C ow (pend-past (CS.scope k) (CS.src k) a (ok-step {Hots (full (CS.scope k))} (CS.connAt k) ok))

-- A joiner subscribed at `q`: every row past `q`, its outer's and every
-- lane's, each lane subscribed past its value.
postulate
  join-past : ∀ {Γ A B} (sc : Scope Γ) op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) {q} → Adm sc → Ok (Hots (full sc)) q
            → ∀ {k e} → JoinF op (λ a → ⟦ f a ⟧ (full sc)) (pendRows (full sc) s q) k e → q ≺ k

-- A source's rows a body row at `p` reads: few, by what the source has
-- passed, or none yet, its subscription not before `p`.
few-src : ∀ {Γ X} {sc : Scope Γ} {Rs} {k : CS Γ X} {o : St Γ X} {p} → CS.scope k ≡ sc → Src sc Rs (bef p) k o → FewBefore (Frozen k) p
few-src _ (src-on _ _ bh)   = few-behind bh
few-src _ (src-shut _ _ _ bh) = few-behind bh
few-src {k = k} {p = p} refl (src-pend _ _ (ok , a) _ _ ow) = [] , λ {y} r lt →
  ⊥-elim (ow (≺-trans {CS.connAt k ++ [ ix 1 ]} {y} {p}
               (pend-past (CS.scope k) (CS.src k) a (ok-step {Hots (full (CS.scope k))} (CS.connAt k) ok) r)
               (≺-trans {y} {y ++ [ ix 0 ]} {p} (≺-ext y []) lt)))
