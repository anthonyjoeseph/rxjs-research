{-# OPTIONS --guardedness #-}

-- A NODE'S PAST BELOW ITS LEAST KEY IS FINITE: of the rows a node still
-- owes, finitely many lie before the least key its subtree holds.  A
-- visible one has none (`bound`); a hidden one is a leaf's tail row past
-- its own keys, a former's image of a child's, a joiner's first effect
-- at the cursor, a dead part's within what its isles still run, or a
-- binder's rejoined row under one its connect has passed.  That is what lets the cursor shift
-- up to the least key: a part's past grows by finitely many rows.
module adequacy.Few where

open import Data.Bool using (Bool; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; map)
open import Data.List.Properties using (∷ʳ-injectiveʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (lookup)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Data.Maybe using (just; nothing)
open import Function using (Equivalence)
open import Data.Bool.Properties using (T-≡)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; Timeline; ix; last; sub; ofᴱ; <ᵖ-split; <ᵖ-step; inside; inside-self)
open import denotation.EmissionSet using (EmissionSet; out; end; pin; _≺_; _≼_; Den; hot; coldAt; Proper; DenEnv; ⟦_⟧; Ended; enter; shown; heard;
  ended; late; InE; MapT; map-out; map-end; map-skip; map-pin; module Joining; module Scan;
  module TakeWhile; module Connecting; module Bounded; module Switch)
open import denotation.Laws.Modulus using (≼-≺-≺; ≺-trans; ≺-ext; ≺-absurd; ≼-antisym; ≼-false; ≼-or-≻)
open import operation.Key using (after)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; Scope; scopeOf; plug; unbound; binds; CS; coldS; ofS; takeS; flatS; connS)
open import adequacy.Rows using (full; pendRows; Frozen; _≃_; _⇄_; ≃-sym; ≃-trans)
open _≃_
open import adequacy.Cursor using (Cur; origin; bef; aft; Thru; Owes; Due; Unfed; Pol; Lane; Runs; Kill; kill-out; Hole; OuterDone; Waiting; NoKill; Kept; polF; JoinF; h-live; h-end; h-kill; LaneSt; l-live; l-dead; Begun; none; more; Spent; Folded; fd-none; fd-last; Whole; Ahead; Joined; joined; Flags; Src; src-pend; src-on; src-shut; OweAt; o-cp; o-cut; o-over; NoFail; Behind; Fin; fin-dn; tail-dn; _≈_; cov; Subd; SubdAt; subd; TailP; tailp; tailp-dn; Pts; _∪ᵖ_; Under; Burst; Torn; Husk; HuskL; SrcH; h-blank; h-map; h-scan; h-cut; h-ln; h-take; h-flat; h-conn; hl-none; hl-more; sh-dead; sh-isle; sh-islec; sh-pend; Sync; s-cold; s-of; s-done; s-map; s-scan; s-cut; s-take; s-took; s-flat; s-conn; s-join; s-joinx; AttOwed)
open import adequacy.Cursor.Show using (thru-owes)
open import adequacy.Floor.Keys using (own-bld; os)
open import adequacy.Least using (KeyIn; k-own; k-kid; k-map; k-scan; k-cut; k-ln; k-take; k-outer; k-lane; k-src; k-body)
open import denotation.Read using (Visible)
open import adequacy.Bound using (Bnd; tr; on; lt; owes-≼; owes?; T?; LoP; KAt; next-slot; in-slot; Env; env-bind; unfed-b;
  of-lb; cold-b; lane-st; body-key; bound; src-b; join-b; begun-b; behind-pend; pend-past)
open import denotation.Laws.Worlds using (Hots; ok-step)
import denotation.Laws.Worlds as Wd

------------------------------------------------------------------------
-- Rows owed before `p`

-- The rows of `E` the cursor has not passed that lie before `p`.
record Lag {A} (C : Cur) (p : Pos) (E : EmissionSet A) : Set where
  constructor lag
  field
    lks : List Pos
    has : ∀ {y e} → E y e → Owes C y → y ≺ p → y ∈ lks

-- Not at or past `p`: before it.
unowed : ∀ {p y} → ¬ (p ≼ y) → y ≺ p
unowed {p} {y} n with ≼-or-≻ p y
... | inj₁ py = ⊥-elim (n py)
... | inj₂ yp = yp

-- A child's position before `p`: the parent's too.
below : ∀ y {l p} → (y ++ [ l ]) ≺ p → y ≺ p
below y {l} {p} h = ≺-trans {y} {y ++ [ l ]} {p} (≺-ext y {l} []) h

-- Passed, or owed and before `p`: passed at `p`.
behind-bef : ∀ {A} {C p} {E : EmissionSet A} → Behind C E → Lag C p E → Behind (bef p) E
behind-bef {C = C} {p} (ks , f) (lag ls g) = ks ++ ls , λ {y} r n →
  [ (λ o → ∈-++⁺ʳ ks (g r o (unowed {p} {y} n))) , (λ no → ∈-++⁺ˡ (f r no)) ]′ (owes? C y)

fin-lag : ∀ {A} {C p} {E : EmissionSet A} → Fin C E → Lag C p E
fin-lag (ks , f) = lag ks λ r o _ → f r o

-- Each row of `E′` a row of `E` at its position.
lag-at : ∀ {A B} {C p} {E : EmissionSet A} {E′ : EmissionSet B} → (∀ {y e} → E′ y e → Σ _ (E y)) → Lag C p E → Lag C p E′
lag-at back (lag ks f) = lag ks λ r o yp → f (proj₂ (back r)) o yp

lag-≈ : ∀ {A} {C p} {E E′ : EmissionSet A} → E ≈ E′ → Lag C p E → Lag C p E′
lag-≈ m (lag ks f) with cov m
... | ls , g = lag (ls ++ ks) λ r o yp → [ (λ r′ → ∈-++⁺ʳ ls (f r′ o yp)) , ∈-++⁺ˡ ]′ (g r)

-- The one row a cursor owes whose parent it has passed: the row at it.
cl : Cur → List Pos
cl origin  = []
cl (bef c) = [ c ]
cl (aft c) = [ c ++ [ ix 0 ] ]

nxt : ∀ C {q} → ¬ Owes C q → Owes C (q ++ [ ix 0 ]) → (q ++ [ ix 0 ]) ∈ cl C
nxt origin  n _ = ⊥-elim (n tt)
nxt (bef c) {q} n o with ≼-or-≻ c q
... | inj₁ cq = ⊥-elim (n cq)
... | inj₂ qc = here (≼-antisym {q ++ [ ix 0 ]} {c} (λ t → subst T (<ᵖ-step q c (Equivalence.to T-≡ qc)) t) o)
nxt (aft c) {q} n o with <ᵖ-split q c (≼-false {q} {c} n)
... | inj₁ qc   = ⊥-elim (subst T (<ᵖ-step q c qc) o)
... | inj₂ refl = here refl

ix0 : Pos → Pos
ix0 y = y ++ [ ix 0 ]

------------------------------------------------------------------------
-- The formers' rows, each at a child's

map-row : ∀ {A B} {f : A → B} {E : EmissionSet A} {y e} → MapT f E y e → Σ _ (E y)
map-row (map-out x)  = _ , x
map-row (map-end x)  = _ , x
map-row (map-skip x) = _ , x
map-row (map-pin x)  = _ , x

scan-row : ∀ {A B} {f : B → A → B} {z} {E : EmissionSet A} {y e} → Scan.ScanT f z E y e → Σ _ (E y)
scan-row (Scan.sval (Scan.acc₀ x _))    = _ , x
scan-row (Scan.sval (Scan.acc _ x _ _)) = _ , x
scan-row (Scan.sstep x)                 = _ , x
scan-row (Scan.spin x)                  = _ , x
scan-row (Scan.send x)                  = _ , x

-- A takeWhile's: a child's, or a failing value's first effect or end,
-- the value owed.
take-lag : ∀ {A} {C p} {i} {keep : A → Bool} {E : EmissionSet A} → NoFail C keep E → Lag C p E → Lag C p (TakeWhile.TakeT i keep E)
take-lag {p = p} nf (lag ks f) = lag (ks ++ (map ix0 ks ++ map (λ y → y ++ [ last ]) ks)) λ where
  (TakeWhile.pass x _ _) o yp   → ∈-++⁺ˡ (f x o yp)
  (TakeWhile.step x _) o yp     → ∈-++⁺ˡ (f x o yp)
  (TakeWhile.tend x _) o yp     → ∈-++⁺ˡ (f x o yp)
  (TakeWhile.left x _ _) o yp   → ∈-++⁺ˡ (f x o yp)
  (TakeWhile.fail {q} x nk _ _) o yp → ∈-++⁺ʳ ks (∈-++⁺ˡ (∈-map⁺ ix0 (f x (nf x nk) (below q yp))))
  (TakeWhile.stop {q} x nk _) o yp   →
    ∈-++⁺ʳ ks (∈-++⁺ʳ (map ix0 ks) (∈-map⁺ (λ y → y ++ [ last ]) (f x (nf x nk) (below q yp))))

-- A binder's row passed at `p`.
Early : ∀ {A} → Pos → Den A → Set
Early p (hot t)    = Behind (bef p) t
Early p (coldAt _) = ⊥

-- A joiner's rows rejoined: each under a binder's row before it, or its
-- late end.
early-lag : ∀ {A} {C p} j (d : Den A) → Early p d → Lag C p (enter d j)
early-lag {p = p} j (hot t) (ks , f) = lag (map (λ y → y ++ [ sub j ]) ks ++ [ j ++ [ last ] ]) λ where
  (shown {q} x _ _ , _) o yp → ∈-++⁺ˡ (∈-map⁺ (λ y → y ++ [ sub j ]) (f x (λ pq → pq (below q yp))))
  (heard {q} x _ , _) o yp   → ∈-++⁺ˡ (∈-map⁺ (λ y → y ++ [ sub j ]) (f x (λ pq → pq (below q yp))))
  (ended {c} x _ , _) o yp   → ∈-++⁺ˡ (∈-map⁺ (λ y → y ++ [ sub j ]) (f x (λ pc → pc (below c yp))))
  (late _ _ , _) o yp        → ∈-++⁺ʳ (map (λ y → y ++ [ sub j ]) ks) (here refl)
early-lag j (coldAt _) ()

-- A binder's rows rejoined, read at a cursor: finitely many owed before
-- `p`.
EnvL : ∀ {Γ} → DenEnv Γ → Cur → Pos → Set₁
EnvL {Γ} ρ C p = ∀ {A} (x : A ∈ Γ) j → Lag C p (enter (lookup ρ x) j)

envl-bind : ∀ {Γ X} {sc : Scope Γ} {C p} {o : Obs Timeline Γ X} {r}
          → Behind (bef p) (pendRows (full sc) o (r ++ [ ix 1 ])) → EnvL (full sc) C p → EnvL (full (binds o r sc)) C p
envl-bind {sc = sc} {o = o} {r} (ks , f) el (here refl) j =
  early-lag j (hot (Proper (pendRows (full sc) o (r ++ [ ix 1 ])))) (ks , λ w n → f (proj₁ w) n)
envl-bind _ el (there x) = el x

-- A leaf's rows lie at or past its own keys.
of-p : ∀ {Γ A} {i q} (xs : List A) {p y e} → LoP (ofS {Γ} i q xs) p → InE (ofᴱ q i xs) y e → p ≼ y
of-p {i = i} {q} []       {p} {y} lo t = tr p (q ++ [ last ]) y (lo (k-own (here refl))) (of-lb q i [] t)
of-p {i = i} {q} (x ∷ xs) {p} {y} lo t = tr p (q ++ [ ix i ]) y (lo (k-own (here refl))) (of-lb q i (x ∷ xs) t)

------------------------------------------------------------------------
-- A joiner's rows, of any kind: an outer row, a value's first effect, a
-- lane's row it keeps, or a lane end's hand-off

data JR {A B} (P : Pol A B) (O : EmissionSet A) : Pos → Set where
  jr-o : ∀ {k e} → O k e → JR P O k
  jr-v : ∀ {q a} → O q (out a) → JR P O (q ++ [ ix 0 ])
  jr-l : ∀ {q a k e} → O q (out a) → Runs P q → Kept P q a k e → JR P O k
  jr-h : ∀ {q a c} → O q (out a) → Runs P q → Kept P q a c end → JR P O (c ++ [ ix 0 ])

module _ {A B : Set} (P : Pol A B) (O : EmissionSet A) (Over : Pos → Set) (Cut : Pos → Pos → Set) (Hand : Pos → Set)
         (nk : ∀ {q k} → ¬ Cut q k → NoKill P q k) where
  open Joining (Lane P) O (λ _ _ → ⊥) Over (Runs P) Cut Hand

  jany : ∀ {k e} → JoinT k e → JR P O k
  jany (val x)                 = jr-v x
  jany (step x)                = jr-o x
  jany (opin x)                = jr-o x
  jany (oend x _)              = jr-o x
  jany (opass x _)             = jr-o x
  jany (lane x r l nc _)       = jr-l x r (inj₁ (l , nk nc))
  jany (lend x r l nc _ _)     = jr-l x r (inj₁ (l , nk nc))
  jany (lpass x r l nc _ _)    = jr-l x r (inj₁ (l , nk nc))
  jany (hand x r l nc _)       = jr-h x r (inj₁ (l , nk nc))
  jany (left x r l nc ins)     = jr-l x r (inj₂ (_ , refl , l , nk nc , ins))
  jany (run () _)
  jany (rend () _ _)
  jany (rpass () _ _)
  jany (rhand () _)

  -- A pin: an outer pin, or a pin a begun lane keeps.
  jpin : ∀ {k r} → JoinT k (pin r) → O k (pin r) ⊎ Σ Pos λ q → Σ A λ a → O q (out a) × Runs P q × Kept P q a k (pin r)
  jpin (opin x)             = inj₁ x
  jpin (lane x ru l nc _)   = inj₂ (_ , _ , x , ru , inj₁ (l , nk nc))
  jpin (left x ru l nc ins) = inj₂ (_ , _ , x , ru , inj₂ (_ , refl , l , nk nc , ins))
  jpin (run () _)

join-any : ∀ {A B} op (F : A → Den B) (O : EmissionSet A) {k e} → JoinF op F O k e → JR (polF op F O) O k
join-any (mergeᶠ nothing)  F O = jany (polF (mergeᶠ nothing) F O) O (Ended O) (λ _ _ → ⊥) (λ _ → ⊥) (λ _ ())
join-any (mergeᶠ (just m)) F O = jany (polF (mergeᶠ (just m)) F O) O (Ended O) (λ _ _ → ⊥) (Bounded.Queued m F O) (λ _ ())
join-any switchᶠ           F O = jany (polF switchᶠ F O) O (Ended O) (Switch.Cut F O) (λ _ → ⊥)
  (λ nc {q′} (a′ , x′ , qq′) q′k → nc (q′ , a′ , x′ , qq′ , q′k))
join-any exhaustᶠ          F O = jany (polF exhaustᶠ F O) O (Ended O) (λ _ _ → ⊥) (λ _ → ⊥) (λ _ ())

join-pin : ∀ {A B} op (F : A → Den B) (O : EmissionSet A) {k r} → JoinF op F O k (pin r)
         → O k (pin r) ⊎ Σ Pos λ q → Σ A λ a → O q (out a) × Runs (polF op F O) q × Kept (polF op F O) q a k (pin r)
join-pin (mergeᶠ nothing)  F O = jpin (polF (mergeᶠ nothing) F O) O (Ended O) (λ _ _ → ⊥) (λ _ → ⊥) (λ _ ())
join-pin (mergeᶠ (just m)) F O = jpin (polF (mergeᶠ (just m)) F O) O (Ended O) (λ _ _ → ⊥) (Bounded.Queued m F O) (λ _ ())
join-pin switchᶠ           F O = jpin (polF switchᶠ F O) O (Ended O) (Switch.Cut F O) (λ _ → ⊥)
  (λ nc {q′} (a′ , x′ , qq′) q′k → nc (q′ , a′ , x′ , qq′ , q′k))
join-pin exhaustᶠ          F O = jpin (polF exhaustᶠ F O) O (Ended O) (λ _ _ → ⊥) (λ _ → ⊥) (λ _ ())

kept-lane : ∀ {A B} {P : Pol A B} {q a k e} → Kept P q a k e → Lane P q a k e
kept-lane (inj₁ (l , _))         = l
kept-lane (inj₂ (_ , _ , l , _)) = l

------------------------------------------------------------------------
-- What a part no live node reads still runs, before `p`

PLag : Pos → Pts → Set
PLag p P = Σ (List Pos) λ ks → ∀ {y} → P y → y ≺ p → y ∈ ks

plag-∪ : ∀ {p P Q} → PLag p P → PLag p Q → PLag p (P ∪ᵖ Q)
plag-∪ (ks , f) (ls , g) = ks ++ ls , λ { (inj₁ x) yp → ∈-++⁺ˡ (f x yp) ; (inj₂ x) yp → ∈-++⁺ʳ ks (g x yp) }

plag-under : ∀ {p P} → PLag p P → PLag p (Under P)
plag-under (ks , f) = map ix0 ks , λ { (k , x , refl) yp → ∈-map⁺ ix0 (f x (below k yp)) }

-- Owed rows before `p`: within what still runs, but for finitely many.
tailp-lag : ∀ {A} {C p} {E : EmissionSet A} {P} → TailP C E P → PLag p P → Lag C p E
tailp-lag (tailp ks f) (ls , g) = lag (ls ++ ks) λ r o yp → [ (λ x → ∈-++⁺ˡ (g x yp)) , ∈-++⁺ʳ ls ]′ (f r o)

-- Passed, or owed before `p`: every row before `p`.
before : ∀ {A} {C p} {E : EmissionSet A} → Behind C E → Lag C p E → Σ (List Pos) λ ks → ∀ {y e} → E y e → y ≺ p → y ∈ ks
before {C = C} (ks , f) (lag ls g) = ks ++ ls , λ {y} r yp → [ (λ o → ∈-++⁺ʳ ks (g r o yp)) , (λ no → ∈-++⁺ˡ (f r no)) ]′ (owes? C y)

-- A burst's first effects before `p`: of its source's rows before `p`.
burst-plag : ∀ {Γ X} {C} {k : CS Γ X} {p} → Σ (List Pos) (λ ks → ∀ {y e} → Frozen k y e → y ≺ p → y ∈ ks) → PLag p (Burst C k)
burst-plag (ks , f) = map ix0 ks , λ { (k′ , (_ , x , _) , refl) yp → ∈-map⁺ ix0 (f x (below k′ yp)) }

-- A scope's binders read at a cursor past every hot row before `p`.
scope-env : ∀ {Γ} (sc : Scope Γ) {C p} → (∀ {y} → Hots (full sc) y → Owes C y → p ≼ y) → Env (full sc) C p
scope-env (binds o r sc) h (here refl) (x , _ , ow) = h (inj₁ (_ , x)) ow
scope-env (binds o r sc) h (there x)                = scope-env sc (λ hy → h (inj₂ hy)) x

-- Rejoined likewise: no owed row under a hot row before `p`, only the
-- late end.
scope-envl : ∀ {Γ} (sc : Scope Γ) {C p} → (∀ {y j} → Hots (full sc) y → Owes C (y ++ [ sub j ]) → (y ++ [ sub j ]) ≺ p → ⊥)
           → EnvL (full sc) C p
scope-envl (binds o r sc) h (here refl) j = lag [ j ++ [ last ] ] λ where
  (shown x _ _ , _) ow yp → ⊥-elim (h (inj₁ (_ , x)) ow yp)
  (heard x _ , _)   ow yp → ⊥-elim (h (inj₁ (_ , x)) ow yp)
  (ended x _ , _)   ow yp → ⊥-elim (h (inj₁ (_ , x)) ow yp)
  (late _ _ , _)    ow yp → here refl
scope-envl (binds o r sc) h (there x) = scope-envl sc (λ hy → h (inj₂ hy)) x

-- A SUBSCRIBED SOURCE'S BINDERS, read at its cursor up to its connect's
-- `ix 2`: a hot row it owes lies past the subscription, outside its
-- world, so past the whole slot.
subd-env : ∀ {Γ X} {sc : Scope Γ} {k : CS Γ X} {C p} → Subd sc C k → p ≼ (CS.connAt k ++ [ ix 2 ])
         → Env (full sc) C p × EnvL (full sc) C p
subd-env {sc = sc} {k = k} {C} {p} (subd past (_ , dj)) pq =
  scope-env sc (λ {y} hy ow → tr p q₂ y pq (next-slot c y (past ow) (off hy))) ,
  scope-envl sc (λ {y} {j} hy ow yp → tr p q₂ (y ++ [ sub j ]) pq (next-slot c (y ++ [ sub j ]) (past ow) (sub-off hy)) yp)
  where
    c  = CS.connAt k
    q₂ = c ++ [ ix 2 ]
    off : ∀ {y} → Hots (full sc) y → T (inside (c ++ [ ix 1 ]) y) → ⊥
    off hy i = dj hy (Wd.step Wd.here Wd.plain-ix) i
    sub-off : ∀ {y j} → Hots (full sc) y → T (inside (c ++ [ ix 1 ]) (y ++ [ sub j ])) → ⊥
    sub-off {y} {j} hy i with Wd.⊑-snoc y (Wd.inside-⊑ (c ++ [ ix 1 ]) (y ++ [ sub j ]) i)
    ... | inj₁ w = off hy (Wd.⊑-inside w)
    ... | inj₂ e with ∷ʳ-injectiveʳ c y e
    ...   | ()

-- An isle's attach owed, or its body not yet run: the least key no
-- later than its connect's `ix 2`.
att-slot : ∀ {Γ X} {k : CS Γ X} {p} → AttOwed k → (CS.bodyAt k ≡ just (CS.connAt k) → p ≼ (CS.connAt k ++ [ ix 1 ]))
         → (∀ {y} → CS.attSrc k ≡ just y → KAt p (after y)) → p ≼ (CS.connAt k ++ [ ix 2 ])
att-slot (inj₁ e) _ al = al e refl
att-slot {k = k} {p} (inj₂ (e , _)) bl _ q₂p =
  bl e (≺-trans {q₁} {CS.connAt k ++ [ ix 2 ]} {p} (in-slot (CS.connAt k) q₁ (Equivalence.from T-≡ (inside-self q₁))) q₂p)
  where q₁ = CS.connAt k ++ [ ix 1 ]

-- A connect's while its source runs: its body's, or a source row's
-- first effect, the source passed at `p`.
conn-lag : ∀ {Γ X B} {C} {k : CS Γ X} {β : EmissionSet B} {p}
         → Lag C p β → Behind (bef p) (Frozen k) → Lag C p (Connecting.ConnT (CS.connAt k) (Frozen k) β)
conn-lag {p = p} (lag kb fb) (ks , fs) = lag (kb ++ map ix0 ks) λ where
  (Connecting.body x) o yp           → ∈-++⁺ˡ (fb x o yp)
  (Connecting.burst {y} x _) o yp    → ∈-++⁺ʳ kb (∈-map⁺ ix0 (fs x (λ py → py (below y yp))))
  (Connecting.echo {y} x _ _ _) o yp → ∈-++⁺ʳ kb (∈-map⁺ ix0 (fs x (λ py → py (below y yp))))
  (Connecting.kept {y} x _ _ _) o yp → ∈-++⁺ʳ kb (∈-map⁺ ix0 (fs x (λ py → py (below y yp))))

-- A begun lane's kept rows owed before `p`, for each value in `vs`.
KLag : ∀ {A B} → Cur → Pos → Pol A B → List (Pos × A) → Set
KLag C p P vs = Σ (List Pos) λ ks → ∀ {q a k e} → (q , a) ∈ vs → Kept P q a k e → Owes C k → k ≺ p → k ∈ ks

-- Each begun lane's rows owed at or past `p`.
LBnd : ∀ {A B} → Cur → Pos → Pol A B → List (Pos × A) → Set
LBnd C p P vs = ∀ {q a k e} → (q , a) ∈ vs → (∀ {q′} → Kill P q q′ → k ≼ q′) → Lane P q a k e → Visible e → Owes C k → p ≼ k

-- A live lane's kept rows: its entry's.
hole-kl : ∀ {A B} {C p} {P : Pol A B} {q a} {E : EmissionSet B} → E ≈ Lane P q a → Lag C p E
        → Σ (List Pos) λ ks → ∀ {k e} → Kept P q a k e → Owes C k → k ≺ p → k ∈ ks
hole-kl {P = P} eq (lag ke fe) with cov eq
... | lv , g = lv ++ ke , λ kp o kp′ → [ (λ r → ∈-++⁺ʳ lv (fe r o kp′)) , ∈-++⁺ˡ ]′ (g (kept-lane {P = P} kp))

-- A joiner's: its outer's, a value's first effect, a begun lane's, a
-- hand-off; a value still owed has its lane past `p`, and so has a
-- waiting one.
flat-lag : ∀ {A B} {op} {F : A → Den B} {O : EmissionSet A} {C vs ws p}
         → Lag C p O → Bnd C p O → KLag C p (polF op F O) vs → LBnd C p (polF op F O) vs
         → Whole C (polF op F O) O vs ws → Ahead C (polF op F O) vs ws
         → Lag C p (JoinF op F O)
flat-lag {op = op} {F} {O} {C} {p = p} (lag ko fo) ob (kl , fl) lb wh ah =
  lag (ko ++ (map ix0 ko ++ (kl ++ (map ix0 kl ++ cl C)))) λ r o yp → pick (join-any op F O r) o yp
  where
    lane-in : ∀ {q a k e} → O q (out a) → Runs (polF op F O) q → Kept (polF op F O) q a k e → Owes C k → k ≺ p → k ∈ kl
    lane-in {q} {k = k} x ru kp ok kp′ with lane-st op F O (kept-lane {P = polF op F O} kp)
    ... | s , st , qs , sk with owes? C q
    ...   | inj₁ oq = ⊥-elim (≺-absurd {k} {p} kp′ (≼-≺-≺ {p} {q} {k} (ob (x , tt , oq)) (lt q s k qs sk)))
    ...   | inj₂ nq with wh x nq ru
    ...     | inj₁ iv = fl iv kp ok kp′
    ...     | inj₂ iw with ah iw st
    ...       | _ , _ , c , iv′ , lc , kc , oc , cs′ =
                ⊥-elim (≺-absurd {k} {p} kp′ (≼-≺-≺ {p} {s} {k} (on p c s (lb {e = end} iv′ kc lc tt oc) cs′) sk))

    pick : ∀ {y} → JR (polF op F O) O y → Owes C y → y ≺ p → y ∈ (ko ++ (map ix0 ko ++ (kl ++ (map ix0 kl ++ cl C))))
    pick (jr-o x) o yp = ∈-++⁺ˡ (fo x o yp)
    pick (jr-v {q} x) o yp with owes? C q
    ... | inj₁ oq = ∈-++⁺ʳ ko (∈-++⁺ˡ (∈-map⁺ ix0 (fo x oq (below q yp))))
    ... | inj₂ nq = ∈-++⁺ʳ ko (∈-++⁺ʳ (map ix0 ko) (∈-++⁺ʳ kl (∈-++⁺ʳ (map ix0 kl) (nxt C nq o))))
    pick (jr-l x ru kp) o yp = ∈-++⁺ʳ ko (∈-++⁺ʳ (map ix0 ko) (∈-++⁺ˡ (lane-in x ru kp o yp)))
    pick (jr-h {c = c} x ru kp) o yp with owes? C c
    ... | inj₁ oc = ∈-++⁺ʳ ko (∈-++⁺ʳ (map ix0 ko) (∈-++⁺ʳ kl (∈-++⁺ˡ (∈-map⁺ ix0 (lane-in x ru kp oc (below c yp))))))
    ... | inj₂ nc = ∈-++⁺ʳ ko (∈-++⁺ʳ (map ix0 ko) (∈-++⁺ʳ kl (∈-++⁺ʳ (map ix0 kl) (nxt C nc o))))

------------------------------------------------------------------------
-- THE PAST BELOW THE LEAST KEY

mutual
  husk-f : ∀ {Γ} {sc : Scope Γ} {A} {s : St Γ A} {D E P p} → Husk sc D s E P → LoP s p → PLag p P
  husk-f (h-blank _)    lo = [] , λ ()
  husk-f (h-map hk _)   lo = husk-f hk (λ ki → lo (k-kid (k-map ki)))
  husk-f (h-scan hk _)  lo = husk-f hk (λ ki → lo (k-kid (k-scan ki)))
  husk-f (h-cut hk _)   lo = husk-f hk (λ ki → lo (k-kid (k-cut ki)))
  husk-f (h-ln hk _)    lo = husk-f hk (λ ki → lo (k-kid (k-ln ki)))
  husk-f (h-take hk _)  lo = husk-f hk (λ ki → lo (k-kid (k-take ki)))
  husk-f (h-flat ho _ hl) lo = plag-∪ (husk-f ho (λ ki → lo (k-kid (k-outer ki)))) (huskl-f hl (λ i ki → lo (k-kid (k-lane i ki))))
  husk-f (h-conn {k = k} {o = o} {b = b} sh hb _) lo = plag-∪ (srch-f sh (λ ki → lo (k-kid (k-src ki))) (λ be → lo (k-own (body-key k {o = o} {b = b} be))) (λ ae → lo (k-own (own-bld k {o = o} {b = b} (os ae))))) (husk-f hb (λ ki → lo (k-kid (k-body ki))))

  huskl-f : ∀ {Γ} {sc : Scope Γ} {A} {ls : List (St Γ A)} {D E P p} → HuskL sc D ls E P → (∀ {l} → l ∈ ls → LoP l p) → PLag p P
  huskl-f hl-none         lo = [] , λ ()
  huskl-f (hl-more hk _ hl) lo = plag-∪ (husk-f hk (lo (here refl))) (huskl-f hl (λ i → lo (there i)))

  srch-f : ∀ {Γ X B} {sc : Scope Γ} {k : CS Γ X} {o D} {E : EmissionSet B} {P p} → SrcH sc D k o E P → LoP o p
         → (CS.bodyAt k ≡ just (CS.connAt k) → p ≼ (CS.connAt k ++ [ ix 1 ])) → (∀ {y} → CS.attSrc k ≡ just y → KAt p (after y))
         → PLag p P
  srch-f (sh-dead hk _ _) lo _ _ = plag-under (husk-f hk lo)
  srch-f {k = k} {p = p} (sh-pend _ _ ba _ refl (ok , a) _ _ _ _ _) _ bl _ = [] , λ { (k′ , (_ , x , _) , refl) yp →
    ⊥-elim (bl ba (≺-trans {CS.connAt k ++ [ ix 1 ]} {k′} {p}
                     (pend-past (CS.scope k) (CS.src k) a (ok-step {Hots (full (CS.scope k))} (CS.connAt k) ok) x) (below k′ yp))) }
  srch-f {k = k} {p = p} (sh-isle {Ci = Ci} na nc sy bh sd ss ao _ _) lo bl al =
    let ie = subd-env {k = k} sd (att-slot {k = k} {p = p} ao bl al) in burst-plag {C = Ci} {k = k} (before {C = Ci} {E = Frozen k} bh (few sy (proj₁ ie) (proj₂ ie) lo))
  srch-f {k = k} (sh-islec {Ci = Ci} na cl sp tp hk _ bh sd _ _) lo _ _ = burst-plag {C = Ci} {k = k} (before {C = Ci} {E = Frozen k} bh (tailp-lag {C = Ci} tp (husk-f hk lo)))

  few : ∀ {Γ} {sc : Scope Γ} {Rg} {C A} {s : St Γ A} {E p} → Sync sc Rg C s E → Env (full sc) C p → EnvL (full sc) C p → LoP s p
      → Lag C p E
  few (s-cold {l = l} tk _ (ks , f)) env ef lo = lag ks λ r o yp → [ (λ t → ⊥-elim (cold-b l tk lo t yp)) , (λ i → i) ]′ (f r o)
  few (s-of {xs = xs} _ (ks , f)) env ef lo = lag ks λ r o yp → [ (λ t → ⊥-elim (of-p xs lo t yp)) , (λ i → i) ]′ (f r o)
  few {C = C} (s-done _ fn) env ef lo = fin-lag {C = C} fn
  few (s-map sy m _) env ef lo = lag-≈ m (lag-at map-row (few sy env ef (λ ki → lo (k-kid (k-map ki)))))
  few (s-scan sy _ m _) env ef lo = lag-≈ m (lag-at scan-row (few sy env ef (λ ki → lo (k-kid (k-scan ki)))))
  few (s-cut sy) env ef lo = few sy env ef (λ ki → lo (k-kid (k-cut ki)))
  few (s-take sy nf m _) env ef lo = lag-≈ m (take-lag nf (few sy env ef (λ ki → lo (k-kid (k-take ki)))))
  few {C = C} (s-took _ _ _ _ tp hk _ _ m _) env ef lo = lag-≈ m (tailp-lag {C = C} tp (husk-f hk (λ ki → lo (k-kid (k-take ki)))))
  few (s-flat _ sy jn (_ , m) _ _) env ef lo = lag-≈ m (lag-at (λ r → _ , proj₁ r) (flat-f sy jn env ef lo))
  few (s-conn refl _ bs _ ss tn fl (m , _)) env ef lo = lag-≈ m (lag-at (λ r → _ , proj₁ r) (conn-f bs ss tn fl env ef lo))
  few (s-join {j = j} {x = x} en _ _ _ _) env ef lo = lag-≈ en (ef x j)
  few {C = C} (s-joinx _ fn) env ef lo = fin-lag {C = C} fn

  -- A connect's: its body's, a source step's first effect, the source
  -- passed at `p`; torn, within what its parts still run.
  conn-f : ∀ {Γ X B} {Rb Rs C} {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) B} {β E p}
         → (T (CS.srcLive k) → Sync (binds (CS.src k) (CS.connAt k) (CS.scope k)) Rb C b β)
         → (T (CS.srcLive k) → Src (CS.scope k) Rs C k o) → (T (not (CS.srcLive k)) → Torn (CS.scope k) C k o b β E) → Flags C k β
         → Env (full (CS.scope k)) C p → EnvL (full (CS.scope k)) C p → LoP (connS k o b) p
         → Lag C p (Connecting.ConnT (CS.connAt k) (Frozen k) β)
  conn-f {C = C} {k = k} {o = o} {b = b} bs ss tn fl env ef lo with T? (CS.srcLive k)
  ... | inj₂ nt = tailp-lag {C = C} (Torn.tl (tn nt)) (plag-∪ (srch-f (Torn.sh (tn nt)) (λ ki → lo (k-kid (k-src ki))) (λ be → lo (k-own (body-key k {o = o} {b = b} be)))
                                                     (λ ae → lo (k-own (own-bld k {o = o} {b = b} (os ae))))) (husk-f (Torn.bh (tn nt)) (λ ki → lo (k-kid (k-body ki)))))
  ... | inj₁ t = let bf = src-f (ss t) env ef lo in
    conn-lag {k = k} (few (bs t) (env-bind {o = CS.src k} {r = CS.connAt k} (src-b (ss t) env lo) env)
                       (envl-bind {o = CS.src k} {r = CS.connAt k} bf ef) (λ ki → lo (k-kid (k-body ki)))) bf

  -- A source passed at `p`: what it passed, and what it owes before `p`.
  src-f : ∀ {Γ X B} {Rg C} {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) B} {p}
        → Src (CS.scope k) Rg C k o → Env (full (CS.scope k)) C p → EnvL (full (CS.scope k)) C p → LoP (connS k o b) p
        → Behind (bef p) (Frozen k)
  src-f {C = C} (src-on _ sy bh _ _ _) env ef lo = behind-bef {C = C} bh (few sy env ef (λ ki → lo (k-kid (k-src ki))))
  src-f {C = C} (src-shut _ _ tp hk _ bh _) env ef lo = behind-bef {C = C} bh (tailp-lag {C = C} tp (husk-f hk (λ ki → lo (k-kid (k-src ki)))))
  src-f {k = k} {b = b} {p = p} (src-pend {o = o′} _ _ be _ a _ _ _ _) env ef lo =
    behind-pend {C = bef p} {k = k} refl a (lo (k-own (body-key k {o = Machine.pend o′ (CS.connAt k ++ [ ix 1 ])} {b = b} be)))

  -- A joiner's: its outer's, a value's first effect, a begun lane's, a
  -- hand-off; a value still owed has its lane past `p`, and so has a
  -- waiting one.
  flat-f : ∀ {Γ} {sc : Scope Γ} {Rg Rl} {C A B} {op} {f : A → Obs Timeline Γ B} {ω} {d n qu o ls O p}
         → Sync sc Rg C o O → Joined sc Rl C (polF op (λ a → ⟦ f a ⟧ (full sc)) O) O d n qu ls
         → Env (full sc) C p → EnvL (full sc) C p → LoP (flatS op f ω d n qu o ls) p
         → Lag C p (JoinF op (λ a → ⟦ f a ⟧ (full sc)) O)
  flat-f {sc = sc} {op = op} {f} {O = O} sy (joined bg _ wh _ ah _ en _) env ef lo =
    flat-lag {op = op} {F = λ a → ⟦ f a ⟧ (full sc)} {O = O} (few sy env ef lo′) (bound sy env lo′) (begun-f bg env ef lol)
      (λ iv kl ln v ow → begun-b {O = O} bg iv kl ln v ow en env lol) wh ah
    where
      lo′ = λ {κ} (ki : KeyIn _ κ) → lo (k-kid (k-outer ki))
      lol = λ {l} i {κ} (ki : KeyIn l κ) → lo (k-kid (k-lane i ki))

  -- The begun lanes' kept rows before `p`.
  begun-f : ∀ {Γ} {sc : Scope Γ} {Rl} {C A B} {P : Pol A B} {O vs ls n p}
          → Begun sc Rl C P O vs ls n → Env (full sc) C p → EnvL (full sc) C p → (∀ {l} → l ∈ ls → LoP l p)
          → Σ (List Pos) λ ks → ∀ {q a k e} → (q , a) ∈ vs → Kept P q a k e → Owes C k → k ≺ p → k ∈ ks
  begun-f none env ef lo = [] , λ ()
  begun-f (more _ _ _ ln bg) env ef lo with lane-f ln env ef (lo (here refl)) | begun-f bg env ef (λ i → lo (there i))
  ... | k₁ , f₁ | k₂ , f₂ = k₁ ++ k₂ , λ where
    (here refl) kp o kp′ → ∈-++⁺ˡ (f₁ kp o kp′)
    (there i)   kp o kp′ → ∈-++⁺ʳ k₁ (f₂ i kp o kp′)

  -- A lane's kept rows before `p`: its entry's, live; dead, within what
  -- it still runs.
  lane-f : ∀ {Γ} {sc : Scope Γ} {Rg} {C A B} {P : Pol A B} {q a l b p}
         → LaneSt sc Rg C P q a l b → Env (full sc) C p → EnvL (full sc) C p → LoP l p
         → Σ (List Pos) λ ks → ∀ {k e} → Kept P q a k e → Owes C k → k ≺ p → k ∈ ks
  lane-f {P = P} (l-live (h-live _ eq _) sy _) env ef lo = hole-kl {P = P} eq (few sy env ef (λ ki → lo (k-kid (k-ln (k-kid (k-cut ki))))))
  lane-f {C = C} (l-dead (h-end _ _ tp) hk _ _) env ef lo  with tailp-lag {C = C} tp (husk-f hk (λ ki → lo (k-kid (k-ln (k-kid (k-cut ki))))))
  ... | lag ks f = ks , f
  lane-f {C = C} (l-dead (h-kill _ _ tp) hk _ _) env ef lo with tailp-lag {C = C} tp (husk-f hk (λ ki → lo (k-kid (k-ln (k-kid (k-cut ki))))))
  ... | lag ks f = ks , f


------------------------------------------------------------------------
-- THE CURSOR SHIFTED UP to just before a key no key of the tree precedes:
-- what the tree owes is unchanged, since it owed nothing before that key.
-- What a part owes moves up by `bound`; what it has passed grows by `few`.

due-shift : ∀ {Γ} {sc : Scope Γ} {Rg} {C A} {s : St Γ A} {E p} → Sync sc Rg C s E → Owes C p → Env (full sc) C p → LoP s p
          → Due C E ≃ Due (bef p) E
due-shift {C = C} sy op env lo = (λ r@(x , v , _) → x , v , bound sy env lo r) ⇄ (λ (x , v , pq) → x , v , owes-≼ C op pq)

module Shifted {C : Cur} {p : Pos} (op : Owes C p) where

  dn : ∀ {q} → Owes (bef p) q → Owes C q
  dn = owes-≼ C op

  th : ∀ {r} → Thru C r → Thru (bef p) r
  th t = thru-owes C t op

  nm : ∀ {q} → ¬ Owes C q → ¬ Owes (bef p) q
  nm n o = n (dn o)

  due-dn : ∀ {A} {E : EmissionSet A} {q e} → Due (bef p) E q e → Due C E q e
  due-dn (x , v , o) = x , v , dn o

  spent : ∀ {A} {E : EmissionSet A} → Spent C E → Spent (bef p) E
  spent {E = E} sp r = sp (due-dn {E = E} r)

  fd : ∀ {A} {E : EmissionSet A} → Fin C E → Fin (bef p) E
  fd = fin-dn {C = C} {C′ = bef p} (λ {y} → dn {y})

  td : ∀ {A} {E : EmissionSet A} {P} → TailP C E P → TailP (bef p) E P
  td = tailp-dn {C = C} {C′ = bef p} (λ {y} → dn {y})

  subd′ : ∀ {Γ} {sc : Scope Γ} {r} → SubdAt sc C r → SubdAt sc (bef p) r
  subd′ (subd f ok) = subd (λ {y} o → f {y} (dn {y} o)) ok

  -- A joiner's unfed rows read at either cursor, its binder's rows lying
  -- at or past `p`.
  unfed-up : ∀ {A j} (d : Den A) → adequacy.Bound.Lies C p d → ∀ {q e} → Due C (Unfed C d j) q e → Due (bef p) (Unfed (bef p) d j) q e
  unfed-up {j = j} (hot t) h u@(shown (y , o) b jq , v , _) = shown (y , h (y , v , o)) b jq , v , unfed-b {C = C} {p = p} {j = j} (hot t) h u
  unfed-up (hot t) h (heard _ _ , () , _)
  unfed-up {j = j} (hot t) h u@(ended (y , o) jc , v , _)   = ended (y , h (y , tt , o)) jc , v , unfed-b {C = C} {p = p} {j = j} (hot t) h u
  unfed-up {j = j} (hot t) h u@(late (y , o) cj , v , _)    = late (y , h (y , tt , o)) cj , v , unfed-b {C = C} {p = p} {j = j} (hot t) h u
  unfed-up (coldAt _) _ (() , _ , _)

  unfed-dn : ∀ {A j} (d : Den A) → ∀ {q e} → Due (bef p) (Unfed (bef p) d j) q e → Due C (Unfed C d j) q e
  unfed-dn (hot t) (shown (y , o) b jq , v , w) = shown (y , dn o) b jq , v , dn w
  unfed-dn (hot t) (heard (y , o) jq , v , w)   = heard (y , dn o) jq , v , dn w
  unfed-dn (hot t) (ended (y , o) jc , v , w)   = ended (y , dn o) jc , v , dn w
  unfed-dn (hot t) (late (y , o) cj , v , w)    = late (y , dn o) cj , v , dn w
  unfed-dn (coldAt _) (() , _ , _)

  fold-sh : ∀ {A B} {f : B → A → B} {z₀ z} {Es} → Bnd C p Es → Folded C f z₀ Es z → Folded (bef p) f z₀ Es z
  fold-sh bd (fd-none h)        = fd-none λ y → bd (y , tt , h y)
  fold-sh bd (fd-last ac nq h)  = fd-last ac (nm nq) λ y qk → bd (y , tt , h y qk)

  -- A connect's flags, its source's and body's rows owed at or past `p`.
  flags-sh : ∀ {Γ X B} {k : CS Γ X} {β : EmissionSet B}
           → (T (CS.srcLive k) → Bnd C p (Frozen k)) → (T (CS.srcLive k) → Bnd C p β) → Flags C k β → Flags (bef p) k β
  flags-sh {k = k} {β} sb bb fl = record
    { shut = λ c → proj₁ (Flags.shut fl c) , nm (proj₂ (Flags.shut fl c)) ; unshut = unsh
    ; torn = λ nt → spent (Flags.torn fl nt) ; owed = λ e → proj₁ (Flags.owed fl e) , nm (proj₂ (Flags.owed fl e)) ; ended = ends }
    where
      unsh : T (CS.srcLive k) → ∀ {c} → Frozen k c end → ¬ Owes (bef p) c → T (CS.closed k)
      unsh t {c} y n with owes? C c
      ... | inj₁ o  = ⊥-elim (n (sb t (y , tt , o)))
      ... | inj₂ no = Flags.unshut fl t y no
      ends : T (CS.srcLive k) → ∀ {c} → β c end → ¬ Owes (bef p) c → CS.owedAt k ≡ just c
      ends t {c} y n with owes? C c
      ... | inj₁ o  = ⊥-elim (n (bb t (y , tt , o)))
      ... | inj₂ no = Flags.ended fl t y no

  -- A begun lane read past `p`: no kill it waits on passed.
  hole-sh : ∀ {A B} {P : Pol A B} {q a Ph E b} → (∀ {q′} → Kill P q q′ → Owes C q′ → Owes (bef p) q′)
          → Hole C P q a Ph E b → Hole (bef p) P q a Ph E b
  hole-sh ku (h-live st eq uk) = h-live st eq (λ k → ku k (uk k))
  hole-sh ku (h-end lc nc tp)  = h-end lc (nm nc) (td tp)
  hole-sh ku (h-kill kq nq tp) = h-kill kq (nm nq) (td tp)

  -- A joiner's queue, its whole, its outer's end and its waiting values'
  -- leads, read past `p`: its outer's rows and its begun lanes' owed at
  -- or past `p`.
  waiting-sh : ∀ {A B} {P : Pol A B} {O : EmissionSet A} {vs ws qu} → LBnd C p P vs → Ahead C P vs ws
             → Waiting C P O ws qu → Waiting (bef p) P O ws qu
  waiting-sh {P = P} {O} {ws = ws} lb ah (eq , ap , wf) = eq , ap , wait
    where
      wait : ∀ {q a} → (q , a) ∈ ws → O q (out a) × ¬ Owes (bef p) q × Runs P q × (∀ {s} → adequacy.Cursor.Start P q a s → Owes (bef p) s)
      wait i with wf i
      ... | y , nq , r , _ = y , nm nq , r , λ {s} st → let (_ , _ , c , iv , lc , kc , oc , cz) = ah i st in on p c s (lb {e = end} iv kc lc tt oc) cz

  whole-sh : ∀ {A B} {P : Pol A B} {O : EmissionSet A} {vs ws} → Bnd C p O → Whole C P O vs ws → Whole (bef p) P O vs ws
  whole-sh ob wh {q} y nq r with owes? C q
  ... | inj₁ o = ⊥-elim (nq (ob (y , tt , o)))
  ... | inj₂ n = wh y n r

  od-sh : ∀ {A} {O : EmissionSet A} {d} → Bnd C p O → OuterDone C O d → OuterDone (bef p) O d
  od-sh ob od = (λ t → let (c , y , n) = proj₁ od t in c , y , nm n)
              , (λ {c} y n → [ (λ o → ⊥-elim (n (ob (y , tt , o)))) , proj₂ od y ]′ (owes? C c))

  ahead-sh : ∀ {A B} {P : Pol A B} {vs ws} → LBnd C p P vs → Ahead C P vs ws → Ahead (bef p) P vs ws
  ahead-sh lb ah i st with ah i st
  ... | q′ , a′ , c , iv , lc , kc , oc , cz = q′ , a′ , c , iv , lc , kc , lb {e = end} iv kc lc tt oc , cz

  owe-sh : ∀ {Γ A} {i} {keep : A → Bool} {w} {s : St Γ A} {r}
         → OweAt C w r → LoP (takeS i keep w s) p → OweAt (bef p) w r
  owe-sh (o-cp _)   lo = o-cp (lo (k-own (here refl)))
  owe-sh (o-cut n)  _  = o-cut (nm n)
  owe-sh (o-over n) _  = o-over (nm n)

  mutual
    sh : ∀ {Γ} {sc : Scope Γ} {Rg} {A} {s : St Γ A} {E} → Sync sc Rg C s E → Env (full sc) C p → EnvL (full sc) C p → LoP s p
       → Sync sc Rg (bef p) s E
    sh sy@(s-cold tk d tl) env ef lo = s-cold tk (≃-trans (≃-sym (due-shift sy op env lo)) d) (tail-dn {C = C} {C′ = bef p} (λ {y} → dn {y}) tl)
    sh sy@(s-of d tl)      env ef lo = s-of (≃-trans (≃-sym (due-shift sy op env lo)) d) (tail-dn {C = C} {C′ = bef p} (λ {y} → dn {y}) tl)
    sh (s-done sp fn)      env ef lo = s-done (spent sp) (fd fn)
    sh (s-map sy m sd)  env ef lo = s-map (sh sy env ef (λ ki → lo (k-kid (k-map ki)))) m sd
    sh (s-scan sy fd′ m sd) env ef lo = s-scan (sh sy env ef lo′) (fold-sh (bound sy env lo′) fd′) m sd
      where lo′ = λ {κ} (ki : KeyIn _ κ) → lo (k-kid (k-scan ki))
    sh (s-cut sy)       env ef lo = s-cut (sh sy env ef (λ ki → lo (k-kid (k-cut ki))))
    sh (s-take sy nf m sd) env ef lo = s-take (sh sy env ef lo′) (λ y nk → bound sy env lo′ (y , tt , nf y nk)) m sd
      where lo′ = λ {κ} (ki : KeyIn _ κ) → lo (k-kid (k-take ki))
    sh (s-took fl g ni oa tp hk dm nf m sd) env ef lo = s-took fl (λ {q} o → g {q} (dn o)) (λ t → nm (ni t)) (owe-sh oa lo) (td tp) hk (λ t → th (dm t)) nf m sd
    sh (s-flat {op = op} ji sy jn m sd bh) env ef lo =
      s-flat ji (sh sy env ef lo′) (joined-sh (bound sy env lo′) (kill-out op) jn env ef (λ i ki → lo (k-kid (k-lane i ki)))) m sd
             (behind-bef {C = C} bh (flat-f sy jn env ef lo))
      where lo′ = λ {κ} (ki : KeyIn _ κ) → lo (k-kid (k-outer ki))
    sh {sc = sc} (s-conn {k = k} {β = β} refl pt bs bb ss tn fl m) env ef lo = s-conn refl pt bs′ bb′ (λ t → src-sh (ss t) env ef lo) tn′ fl′ m
      where
        envb : T (CS.srcLive k) → Env (full (binds (CS.src k) (CS.connAt k) sc)) C p
        envb t = env-bind {o = CS.src k} {r = CS.connAt k} (src-b (ss t) env lo) env
        envlb : T (CS.srcLive k) → EnvL (full (binds (CS.src k) (CS.connAt k) sc)) C p
        envlb t = envl-bind {o = CS.src k} {r = CS.connAt k} (src-f (ss t) env ef lo) ef
        bs′ = λ t → sh (bs t) (envb t) (envlb t) (λ ki → lo (k-kid (k-body ki)))
        bb′ = λ t → behind-bef {C = C} (bb t) (few (bs t) (envb t) (envlb t) (λ ki → lo (k-kid (k-body ki))))
        fl′ = flags-sh (λ t → src-b (ss t) env lo) (λ t → bound (bs t) (envb t) (λ ki → lo (k-kid (k-body ki)))) fl
        tn′ = λ nt → let t = tn nt in record { D = Torn.D t ; Db = Torn.Db t ; dom = (λ u → th (Torn.dom t u)) ; bu = Torn.bu t ; Ps = Torn.Ps t ; Pb = Torn.Pb t ; sh = Torn.sh t ; bh = Torn.bh t ; tl = td (Torn.tl t) }
    sh {sc = sc} (s-join {x = x} {E = E} en d ap hd adm) env ef lo = s-join en d′ ap (λ i u → hd i (unfed-dn (lookup (full sc) x) u)) adm
      where
        d′ = (λ r → [ inj₁ , (λ u → inj₂ (unfed-up (lookup (full sc) x) (env x) u)) ]′ (to d (due-dn {E = E} r)))
           ⇄ [ (λ i → let r = from d (inj₁ i) in proj₁ r , proj₁ (proj₂ r) , join-b {sc = sc} d ap env lo r)
             , (λ u → let r = from d (inj₂ (unfed-dn (lookup (full sc) x) u)) in proj₁ r , proj₁ (proj₂ r) , proj₂ (proj₂ u)) ]′
    sh (s-joinx sp fn)     env ef lo = s-joinx (spent sp) (fd fn)

    src-sh : ∀ {Γ X B} {Rg} {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) B}
           → Src (CS.scope k) Rg C k o → Env (full (CS.scope k)) C p → EnvL (full (CS.scope k)) C p → LoP (connS k o b) p
           → Src (CS.scope k) Rg (bef p) k o
    src-sh {k = k} {b = b} (src-pend {o = o′} na nc be an adm pr wn _ nr) env ef lo =
      src-pend na nc be an adm pr wn (lo (k-own (body-key k {o = Machine.pend o′ (CS.connAt k ++ [ ix 1 ])} {b = b} be))) (λ h → nr (owes-≼ C op h))
    src-sh {k = k} (src-on nc sy bh sd af ao) env ef lo =
      src-on nc (sh sy env ef lo′) (behind-bef {C = C} bh (few sy env ef lo′)) (subd′ sd) af ao
      where lo′ = λ {κ} (ki : KeyIn _ κ) → lo (k-kid (k-src ki))
    src-sh {k = k} (src-shut cl sp tp hk dm bh sd) env ef lo =
      src-shut cl (spent sp) (td tp) hk (λ t → th (dm t)) (behind-bef {C = C} bh (tailp-lag {C = C} tp (husk-f hk (λ ki → lo (k-kid (k-src ki)))))) (subd′ sd)

    joined-sh : ∀ {Γ} {sc : Scope Γ} {Rl} {A B} {P : Pol A B} {O : EmissionSet A} {d n qu ls}
              → (∀ {q e} → Due C O q e → p ≼ q) → (∀ {q q′} → Kill P q q′ → Σ A λ a′ → O q′ (out a′) × q ≺ q′) → Joined sc Rl C P O d n qu ls
              → Env (full sc) C p → EnvL (full sc) C p → (∀ {l} → l ∈ ls → LoP l p) → Joined sc Rl (bef p) P O d n qu ls
    joined-sh {P = P} {O} ob kr (joined {vs = vs} {ws = ws} bg wt wh od ah ao en li) env ef lo =
      joined (begun-sh (λ k o → ob (proj₁ (proj₂ (kr k)) , tt , o)) bg env ef lo) (waiting-sh {P = P} {O = O} {vs = vs} {ws = ws} lb ah wt)
             (whole-sh {P = P} {vs = vs} {ws = ws} ob wh) (od-sh {O = O} ob od) (ahead-sh {P = P} {vs = vs} {ws = ws} lb ah) ao en li
      where
        lb : LBnd C p P vs
        lb iv kl ln v ow = begun-b {O = O} bg iv kl ln v ow en env lo

    begun-sh : ∀ {Γ} {sc : Scope Γ} {Rl} {A B} {P : Pol A B} {O vs ls n}
             → (∀ {q q′} → Kill P q q′ → Owes C q′ → Owes (bef p) q′)
             → Begun sc Rl C P O vs ls n → Env (full sc) C p → EnvL (full sc) C p → (∀ {l} → l ∈ ls → LoP l p) → Begun sc Rl (bef p) P O vs ls n
    begun-sh ku none                 env ef lo = none
    begun-sh ku (more y nq r ln bg) env ef lo = more y (nm nq) r (lane-sh ku ln env ef (lo (here refl))) (begun-sh ku bg env ef (λ i → lo (there i)))

    lane-sh : ∀ {Γ} {sc : Scope Γ} {Rg} {A B} {P : Pol A B} {q a l b}
            → (∀ {q′} → Kill P q q′ → Owes C q′ → Owes (bef p) q′)
            → LaneSt sc Rg C P q a l b → Env (full sc) C p → EnvL (full sc) C p → LoP l p → LaneSt sc Rg (bef p) P q a l b
    lane-sh ku (l-live hl sy sd) env ef lo = l-live (hole-sh ku hl) (sh sy env ef (λ ki → lo (k-kid (k-ln (k-kid (k-cut ki)))))) sd
    lane-sh ku (l-dead {E = E} hl hk dm nk) env ef lo = l-dead {E = E} (hole-sh ku hl) hk (λ t → th (dm t)) nk

shift : ∀ {Γ} {sc : Scope Γ} {Rg} {C A} {s : St Γ A} {E p} → Sync sc Rg C s E → Owes C p → Env (full sc) C p → EnvL (full sc) C p
      → LoP s p → Sync sc Rg (bef p) s E
shift sy op env ef lo = Shifted.sh op sy env ef lo
