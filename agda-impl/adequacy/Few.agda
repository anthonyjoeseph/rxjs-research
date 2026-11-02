{-# OPTIONS --guardedness #-}

-- A NODE'S PAST BELOW ITS LEAST KEY IS FINITE: of the rows a node still
-- owes, finitely many lie before the least key its subtree holds.  A
-- visible one has none (`bound`); a hidden one is a leaf's tail row past
-- its own keys, a former's image of a child's, a joiner's first effect
-- at the cursor, a dead part's finitely many, or a binder's rejoined row
-- under one its connect has passed.  That is what lets the cursor shift
-- up to the least key: a part's past grows by finitely many rows.
module adequacy.Few where

open import Data.Bool using (Bool; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; map)
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
open import denotation.Events using (Pos; Timeline; ix; last; sub; inside; ofᴱ; <ᵖ-split; <ᵖ-step)
open import denotation.EmissionSet using (EmissionSet; out; end; pin; _≺_; _≼_; Den; hot; coldAt; DenEnv; ⟦_⟧; Ended; enter;
  shown; heard; ended; late; InE; MapT; map-out; map-end; map-skip; map-pin;
  module Joining; module Scan; module TakeWhile; module Connecting; module Bounded; module Switch)
open import denotation.Laws.Modulus using (≼-trans; ≼-≺-≺; ≺-trans; ≺-ext; ≺-absurd; ≼-antisym; ≼-false; ≼-or-≻)
open import operation.Key using (at)
open import operation.PureObservable using (module Machine)
open Machine using (St; Scope; unbound; binds; CS; coldS; ofS; takeS; flatS; connS)
open import adequacy.Rows using (full; pendRows; Frozen; _≃_; _⇄_; ≃-sym; ≃-trans)
open _≃_
open import adequacy.Cursor using (Cur; origin; bef; aft; Owes; Due; Unfed; Pol; Lane; Runs; NoKill; Kept;
  polF; JoinF; h-live; h-end; h-kill; LaneSt; l-live; l-dead; Begun; none; more; Spent;
  Folded; fd-none; fd-last; Whole; Ahead; Joined; joined; Flags; Src; src-pend; src-on; src-shut; OweAt; o-cp; o-cut; o-over;
  NoFail; Behind; Fin; fin-dn; fin-≈; tail-dn; _≈_; cov; voc;
  Sync; s-cold; s-of; s-done; s-map; s-scan; s-cut; s-take; s-took; s-flat; s-conn; s-join; s-joinx)
open import adequacy.Least using (KeyIn; k-own; k-kid; k-map; k-scan; k-cut; k-ln; k-take; k-outer; k-lane; k-src; k-body; Lo)
open import adequacy.Bound using (tr; on; lt; owes-≼; owes?; T?; lo-at; Env; env-bind; unfed-b; of-lb; cold-b;
  lane-st; body-key; bound; src-b; join-b; begun-b; behind-pend)

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
... | ls , g = lag (ls ++ ks) λ r o yp → [ (λ (_ , r′) → ∈-++⁺ʳ ls (f r′ o yp)) , ∈-++⁺ˡ ]′ (g r)

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

EnvF : ∀ {Γ} → DenEnv Γ → Pos → Set₁
EnvF {Γ} ρ p = ∀ {A} (x : A ∈ Γ) → Early p (lookup ρ x)

envf-bind : ∀ {Γ X} {sc : Scope Γ} {p} {o : Obs Timeline Γ X} {r}
          → Behind (bef p) (pendRows (full sc) o (r ++ [ ix 1 ])) → EnvF (full sc) p → EnvF (full (binds o r sc)) p
envf-bind (ks , f) ef (here refl) = ks , λ r n → f (proj₁ r) n
envf-bind _        ef (there x)   = ef x

-- A joiner's rows rejoined: each under a binder's row before it, or its
-- late end.
early-lag : ∀ {A} {C p} j (d : Den A) → Early p d → Lag C p (enter d j)
early-lag {p = p} j (hot t) (ks , f) = lag (map (λ y → y ++ [ sub j ]) ks ++ [ j ++ [ last ] ]) λ where
  (shown {q} x _ _ , _) o yp → ∈-++⁺ˡ (∈-map⁺ (λ y → y ++ [ sub j ]) (f x (λ pq → pq (below q yp))))
  (heard {q} x _ , _) o yp   → ∈-++⁺ˡ (∈-map⁺ (λ y → y ++ [ sub j ]) (f x (λ pq → pq (below q yp))))
  (ended {c} x _ , _) o yp   → ∈-++⁺ˡ (∈-map⁺ (λ y → y ++ [ sub j ]) (f x (λ pc → pc (below c yp))))
  (late _ _ , _) o yp        → ∈-++⁺ʳ (map (λ y → y ++ [ sub j ]) ks) (here refl)
early-lag j (coldAt _) ()

-- A leaf's rows lie at or past its own keys.
of-p : ∀ {Γ A} {i q} (xs : List A) {p y e} → Lo (ofS {Γ} i q xs) (at p) → InE (ofᴱ q i xs) y e → p ≼ y
of-p {i = i} {q} []       {p} {y} lo t = tr p (q ++ [ last ]) y (lo-at lo (k-own (here refl))) (of-lb q i [] t)
of-p {i = i} {q} (x ∷ xs) {p} {y} lo t = tr p (q ++ [ ix i ]) y (lo-at lo (k-own (here refl))) (of-lb q i (x ∷ xs) t)

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

join-any : ∀ {A B} op (F : A → Den B) (O : EmissionSet A) {k e} → JoinF op F O k e → JR (polF op F O) O k
join-any (mergeᶠ nothing)  F O = jany (polF (mergeᶠ nothing) F O) O (Ended O) (λ _ _ → ⊥) (λ _ → ⊥) (λ _ ())
join-any (mergeᶠ (just m)) F O = jany (polF (mergeᶠ (just m)) F O) O (Ended O) (λ _ _ → ⊥) (Bounded.Queued m F O) (λ _ ())
join-any switchᶠ           F O = jany (polF switchᶠ F O) O (Ended O) (Switch.Cut F O) (λ _ → ⊥)
  (λ nc {q′} (a′ , x′ , qq′) q′k → nc (q′ , a′ , x′ , qq′ , q′k))
join-any exhaustᶠ          F O = jany (polF exhaustᶠ F O) O (Ended O) (λ _ _ → ⊥) (λ _ → ⊥) (λ _ ())

kept-lane : ∀ {A B} {P : Pol A B} {q a k e} → Kept P q a k e → Lane P q a k e
kept-lane (inj₁ (l , _))         = l
kept-lane (inj₂ (_ , _ , l , _)) = l

------------------------------------------------------------------------
-- THE PAST BELOW THE LEAST KEY

mutual
  few : ∀ {Γ} {sc : Scope Γ} {Rg} {C A} {s : St Γ A} {E p} → Sync sc Rg C s E → Env (full sc) C p → EnvF (full sc) p → Lo s (at p)
      → Lag C p E
  few (s-cold {l = l} tk _ (ks , f)) env ef lo = lag ks λ r o yp → [ (λ (_ , t) → ⊥-elim (cold-b l tk lo t yp)) , (λ i → i) ]′ (f r o)
  few (s-of {xs = xs} _ (ks , f)) env ef lo = lag ks λ r o yp → [ (λ (_ , t) → ⊥-elim (of-p xs lo t yp)) , (λ i → i) ]′ (f r o)
  few {C = C} (s-done _ fn) env ef lo = fin-lag {C = C} fn
  few (s-map sy m _) env ef lo = lag-≈ m (lag-at map-row (few sy env ef (λ ki → lo (k-kid (k-map ki)))))
  few (s-scan sy _ m _) env ef lo = lag-≈ m (lag-at scan-row (few sy env ef (λ ki → lo (k-kid (k-scan ki)))))
  few (s-cut sy) env ef lo = few sy env ef (λ ki → lo (k-kid (k-cut ki)))
  few (s-take sy nf m _) env ef lo = lag-≈ m (take-lag nf (few sy env ef (λ ki → lo (k-kid (k-take ki)))))
  few {C = C} (s-took _ _ _ _ fn m _) env ef lo = fin-lag {C = C} (fin-≈ {C = C} m fn)
  few (s-flat _ sy jn (_ , m) _ _) env ef lo = lag-≈ m (lag-at (λ r → _ , proj₁ r) (flat-f sy jn env ef lo))
  few (s-conn refl _ bs ss fl (m , _)) env ef lo = lag-≈ m (lag-at (λ r → _ , proj₁ r) (conn-f bs ss fl env ef lo))
  few {sc = sc} (s-join {j = j} {x = x} en _ _ _ _) env ef lo = lag-≈ en (early-lag j (lookup (full sc) x) (ef x))
  few {C = C} (s-joinx _ fn) env ef lo = fin-lag {C = C} fn

  -- A connect's: its body's, a source step's first effect, the source
  -- passed at `p`; torn, finitely many.
  conn-f : ∀ {Γ X B} {Rb Rs C} {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) B} {β p}
         → (T (CS.srcLive k) → Sync (binds (CS.src k) (CS.connAt k) (CS.scope k)) Rb C b β)
         → (T (CS.srcLive k) → Src (CS.scope k) Rs C k o) → Flags C k β
         → Env (full (CS.scope k)) C p → EnvF (full (CS.scope k)) p → Lo (connS k o b) (at p)
         → Lag C p (Connecting.ConnT (CS.connAt k) (Frozen k) β)
  conn-f {C = C} {k = k} bs ss fl env ef lo with T? (CS.srcLive k)
  ... | inj₂ nt = fin-lag {C = C} (Flags.spun fl nt)
  ... | inj₁ t with src-f (ss t) env ef lo
  ...   | ks , fs with few (bs t) (env-bind {o = CS.src k} {r = CS.connAt k} (src-b (ss t) env lo) env)
                         (envf-bind {o = CS.src k} {r = CS.connAt k} (ks , fs) ef) (λ ki → lo (k-kid (k-body ki)))
  ...     | lag kb fb = lag (kb ++ map ix0 ks) λ where
    (Connecting.body x) o yp           → ∈-++⁺ˡ (fb x o yp)
    (Connecting.burst {y} x _) o yp    → ∈-++⁺ʳ kb (∈-map⁺ ix0 (fs x (λ py → py (below y yp))))
    (Connecting.echo {y} x _ _ _) o yp → ∈-++⁺ʳ kb (∈-map⁺ ix0 (fs x (λ py → py (below y yp))))
    (Connecting.kept {y} x _ _ _) o yp → ∈-++⁺ʳ kb (∈-map⁺ ix0 (fs x (λ py → py (below y yp))))

  -- A source passed at `p`: what it passed, and what it owes before `p`.
  src-f : ∀ {Γ X B} {Rg C} {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) B} {p}
        → Src (CS.scope k) Rg C k o → Env (full (CS.scope k)) C p → EnvF (full (CS.scope k)) p → Lo (connS k o b) (at p)
        → Behind (bef p) (Frozen k)
  src-f {C = C} (src-on _ sy bh) env ef lo = behind-bef {C = C} bh (few sy env ef (λ ki → lo (k-kid (k-src ki))))
  src-f {C = C} (src-shut _ _ fn bh) env ef lo = behind-bef {C = C} bh (fin-lag {C = C} fn)
  src-f {k = k} {b = b} {p = p} (src-pend {o = o′} _ be a _ _ _) env ef lo =
    behind-pend {C = bef p} {k = k} refl a (lo-at lo (k-own (body-key k {o = Machine.pend o′ (CS.connAt k ++ [ ix 1 ])} {b = b} be)))

  -- A joiner's: its outer's, a value's first effect, a begun lane's, a
  -- hand-off; a value still owed has its lane past `p`, and so has a
  -- waiting one.
  flat-f : ∀ {Γ} {sc : Scope Γ} {Rg Rl} {C A B} {op} {f : A → Obs Timeline Γ B} {ω} {d n qu o ls O p}
         → Sync sc Rg C o O → Joined sc Rl C (polF op (λ a → ⟦ f a ⟧ (full sc)) O) O d n qu ls
         → Env (full sc) C p → EnvF (full sc) p → Lo (flatS op f ω d n qu o ls) (at p)
         → Lag C p (JoinF op (λ a → ⟦ f a ⟧ (full sc)) O)
  flat-f {sc = sc} {C = C} {op = op} {f} {O = O} {p} sy (joined bg _ wh _ ah _ en _) env ef lo
    with few sy env ef (λ ki → lo (k-kid (k-outer ki))) | begun-f bg env ef (λ i ki → lo (k-kid (k-lane i ki)))
  ... | lag ko fo | kl , fl = lag (ko ++ (map ix0 ko ++ (kl ++ (map ix0 kl ++ cl C)))) λ r o yp → pick (join-any op F O r) o yp
    where
      F = λ a → ⟦ f a ⟧ (full sc)

      lane-in : ∀ {q a k e} → O q (out a) → Runs (polF op F O) q → Kept (polF op F O) q a k e → Owes C k → k ≺ p → k ∈ kl
      lane-in {q} {k = k} x ru kp ok kp′ with lane-st op F O (kept-lane {P = polF op F O} kp)
      ... | s , st , qs , sk with owes? C q
      ...   | inj₁ oq = ⊥-elim (≺-absurd {k} {p} kp′
                          (≼-≺-≺ {p} {q} {k} (bound sy env (λ ki → lo (k-kid (k-outer ki))) (x , tt , oq)) (lt q s k qs sk)))
      ...   | inj₂ nq with wh x nq ru
      ...     | inj₁ iv = fl iv kp ok kp′
      ...     | inj₂ iw with ah iw st
      ...       | _ , _ , c , iv′ , lc , kc , oc , cs′ =
                  ⊥-elim (≺-absurd {k} {p} kp′ (≼-≺-≺ {p} {s} {k}
                    (on p c s (begun-b {O = O} {k = c} {e = end} bg iv′ kc lc tt oc en env (λ i ki → lo (k-kid (k-lane i ki)))) cs′) sk))

      pick : ∀ {y} → JR (polF op F O) O y → Owes C y → y ≺ p → y ∈ (ko ++ (map ix0 ko ++ (kl ++ (map ix0 kl ++ cl C))))
      pick (jr-o x) o yp = ∈-++⁺ˡ (fo x o yp)
      pick (jr-v {q} x) o yp with owes? C q
      ... | inj₁ oq = ∈-++⁺ʳ ko (∈-++⁺ˡ (∈-map⁺ ix0 (fo x oq (below q yp))))
      ... | inj₂ nq = ∈-++⁺ʳ ko (∈-++⁺ʳ (map ix0 ko) (∈-++⁺ʳ kl (∈-++⁺ʳ (map ix0 kl) (nxt C nq o))))
      pick (jr-l x ru kp) o yp = ∈-++⁺ʳ ko (∈-++⁺ʳ (map ix0 ko) (∈-++⁺ˡ (lane-in x ru kp o yp)))
      pick (jr-h {c = c} x ru kp) o yp with owes? C c
      ... | inj₁ oc = ∈-++⁺ʳ ko (∈-++⁺ʳ (map ix0 ko) (∈-++⁺ʳ kl (∈-++⁺ˡ (∈-map⁺ ix0 (lane-in x ru kp oc (below c yp))))))
      ... | inj₂ nc = ∈-++⁺ʳ ko (∈-++⁺ʳ (map ix0 ko) (∈-++⁺ʳ kl (∈-++⁺ʳ (map ix0 kl) (nxt C nc o))))

  -- The begun lanes' kept rows before `p`.
  begun-f : ∀ {Γ} {sc : Scope Γ} {Rl} {C A B} {P : Pol A B} {O vs ls n p}
          → Begun sc Rl C P O vs ls n → Env (full sc) C p → EnvF (full sc) p → (∀ {l} → l ∈ ls → Lo l (at p))
          → Σ (List Pos) λ ks → ∀ {q a k e} → (q , a) ∈ vs → Kept P q a k e → Owes C k → k ≺ p → k ∈ ks
  begun-f none env ef lo = [] , λ ()
  begun-f (more _ _ _ ln bg) env ef lo with lane-f ln env ef (lo (here refl)) | begun-f bg env ef (λ i → lo (there i))
  ... | k₁ , f₁ | k₂ , f₂ = k₁ ++ k₂ , λ where
    (here refl) kp o kp′ → ∈-++⁺ˡ (f₁ kp o kp′)
    (there i)   kp o kp′ → ∈-++⁺ʳ k₁ (f₂ i kp o kp′)

  -- A lane's kept rows before `p`: its entry's, live; finitely many, dead.
  lane-f : ∀ {Γ} {sc : Scope Γ} {Rg} {C A B} {P : Pol A B} {q a l b p}
         → LaneSt sc Rg C P q a l b → Env (full sc) C p → EnvF (full sc) p → Lo l (at p)
         → Σ (List Pos) λ ks → ∀ {k e} → Kept P q a k e → Owes C k → k ≺ p → k ∈ ks
  lane-f {P = P} (l-live (h-live _ _ eq) sy _) env ef lo with few sy env ef (λ ki → lo (k-kid (k-ln (k-kid (k-cut ki))))) | voc eq
  ... | lag ke fe | lv , g = lv ++ ke , λ kp o kp′ → [ (λ (_ , r) → ∈-++⁺ʳ lv (fe r o kp′)) , ∈-++⁺ˡ ]′ (g (kept-lane {P = P} kp))
  lane-f (l-dead (h-end _ _ (ks , f))) env ef lo  = ks , λ kp o _ → f kp o
  lane-f (l-dead (h-kill _ _ (ks , f))) env ef lo = ks , λ kp o _ → f kp o


------------------------------------------------------------------------
-- THE CURSOR SHIFTED UP to just before a key no key of the tree precedes:
-- what the tree owes is unchanged, since it owed nothing before that key.
-- What a part owes moves up by `bound`; what it has passed grows by `few`.

due-shift : ∀ {Γ} {sc : Scope Γ} {Rg} {C A} {s : St Γ A} {E p} → Sync sc Rg C s E → Owes C p → Env (full sc) C p → Lo s (at p)
          → Due C E ≃ Due (bef p) E
due-shift {C = C} sy op env lo = (λ r@(x , v , _) → x , v , bound sy env lo r) ⇄ (λ (x , v , pq) → x , v , owes-≼ C op pq)

module Shifted {C : Cur} {p : Pos} (op : Owes C p) where

  dn : ∀ {q} → Owes (bef p) q → Owes C q
  dn = owes-≼ C op

  nm : ∀ {q} → ¬ Owes C q → ¬ Owes (bef p) q
  nm n o = n (dn o)

  due-dn : ∀ {A} {E : EmissionSet A} {q e} → Due (bef p) E q e → Due C E q e
  due-dn (x , v , o) = x , v , dn o

  spent : ∀ {A} {E : EmissionSet A} → Spent C E → Spent (bef p) E
  spent {E = E} sp r = sp (due-dn {E = E} r)

  fd : ∀ {A} {E : EmissionSet A} → Fin C E → Fin (bef p) E
  fd = fin-dn {C = C} {C′ = bef p} (λ {y} → dn {y})

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

  fold-sh : ∀ {Γ} {sc : Scope Γ} {Rg} {A B} {f : B → A → B} {z₀ z} {s : St Γ A} {Es}
          → Sync sc Rg C s Es → Env (full sc) C p → Lo s (at p) → Folded C f z₀ Es z → Folded (bef p) f z₀ Es z
  fold-sh sy env lo (fd-none h)        = fd-none λ y → bound sy env lo (y , tt , h y)
  fold-sh sy env lo (fd-last ac nq h)  = fd-last ac (nm nq) λ y qk → bound sy env lo (y , tt , h y qk)

  owe-sh : ∀ {Γ A} {i} {keep : A → Bool} {w} {s : St Γ A} {r}
         → OweAt C w r → Lo (takeS i keep w s) (at p) → OweAt (bef p) w r
  owe-sh (o-cp _)   lo = o-cp (lo-at lo (k-own (here refl)))
  owe-sh (o-cut n)  _  = o-cut (nm n)
  owe-sh (o-over n) _  = o-over (nm n)

  mutual
    sh : ∀ {Γ} {sc : Scope Γ} {Rg} {A} {s : St Γ A} {E} → Sync sc Rg C s E → Env (full sc) C p → EnvF (full sc) p → Lo s (at p)
       → Sync sc Rg (bef p) s E
    sh sy@(s-cold tk d tl) env ef lo = s-cold tk (≃-trans (≃-sym (due-shift sy op env lo)) d) (tail-dn {C = C} {C′ = bef p} (λ {y} → dn {y}) tl)
    sh sy@(s-of d tl)      env ef lo = s-of (≃-trans (≃-sym (due-shift sy op env lo)) d) (tail-dn {C = C} {C′ = bef p} (λ {y} → dn {y}) tl)
    sh (s-done sp fn)      env ef lo = s-done (spent sp) (fd fn)
    sh (s-map sy m sd)  env ef lo = s-map (sh sy env ef (λ ki → lo (k-kid (k-map ki)))) m sd
    sh (s-scan sy fd′ m sd) env ef lo = s-scan (sh sy env ef lo′) (fold-sh sy env lo′ fd′) m sd
      where lo′ = λ {κ} (ki : KeyIn _ κ) → lo (k-kid (k-scan ki))
    sh (s-cut sy)       env ef lo = s-cut (sh sy env ef (λ ki → lo (k-kid (k-cut ki))))
    sh (s-take sy nf m sd) env ef lo = s-take (sh sy env ef lo′) (λ y nk → bound sy env lo′ (y , tt , nf y nk)) m sd
      where lo′ = λ {κ} (ki : KeyIn _ κ) → lo (k-kid (k-take ki))
    sh (s-took fl g ni oa fn m sd) env ef lo = s-took fl (λ {q} o → g {q} (dn o)) (λ t → nm (ni t)) (owe-sh oa lo) (fd fn) m sd
    sh (s-flat ji sy jn m sd bh) env ef lo =
      s-flat ji (sh sy env ef lo′) (joined-sh (bound sy env lo′) jn env ef (λ i ki → lo (k-kid (k-lane i ki)))) m sd
             (behind-bef {C = C} bh (flat-f sy jn env ef lo))
      where lo′ = λ {κ} (ki : KeyIn _ κ) → lo (k-kid (k-outer ki))
    sh {sc = sc} (s-conn {k = k} refl pt bs ss fl m) env ef lo = s-conn refl pt bs′ (λ t → src-sh (ss t) env ef lo) fl′ m
      where
        bs′ = λ t → sh (bs t) (env-bind {o = CS.src k} {r = CS.connAt k} (src-b (ss t) env lo) env)
                       (envf-bind {o = CS.src k} {r = CS.connAt k} (src-f (ss t) env ef lo) ef) (λ ki → lo (k-kid (k-body ki)))
        unsh : T (CS.srcLive k) → ∀ {c} → Frozen k c end → ¬ Owes (bef p) c → T (CS.closed k)
        unsh t {c} y n with owes? C c
        ... | inj₁ o  = ⊥-elim (n (src-b (ss t) env lo (y , tt , o)))
        ... | inj₂ no = Flags.unshut fl t y no
        fl′ = record { shut = λ c → proj₁ (Flags.shut fl c) , nm (proj₂ (Flags.shut fl c)) ; unshut = unsh
                     ; torn = λ nt → spent (Flags.torn fl nt) ; spun = λ nt → fd (Flags.spun fl nt) }
    sh {sc = sc} (s-join {x = x} {E = E} en d ap hd adm) env ef lo = s-join en d′ ap (λ i u → hd i (unfed-dn (lookup (full sc) x) u)) adm
      where
        d′ = (λ r → [ inj₁ , (λ u → inj₂ (unfed-up (lookup (full sc) x) (env x) u)) ]′ (to d (due-dn {E = E} r)))
           ⇄ [ (λ i → let r = from d (inj₁ i) in proj₁ r , proj₁ (proj₂ r) , join-b {sc = sc} d ap env lo r)
             , (λ u → let r = from d (inj₂ (unfed-dn (lookup (full sc) x) u)) in proj₁ r , proj₁ (proj₂ r) , proj₂ (proj₂ u)) ]′
    sh (s-joinx sp fn)     env ef lo = s-joinx (spent sp) (fd fn)

    src-sh : ∀ {Γ X B} {Rg} {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) B}
           → Src (CS.scope k) Rg C k o → Env (full (CS.scope k)) C p → EnvF (full (CS.scope k)) p → Lo (connS k o b) (at p)
           → Src (CS.scope k) Rg (bef p) k o
    src-sh {k = k} {b = b} (src-pend {o = o′} nc be adm pr wn _) env ef lo =
      src-pend nc be adm pr wn (lo-at lo (k-own (body-key k {o = Machine.pend o′ (CS.connAt k ++ [ ix 1 ])} {b = b} be)))
    src-sh (src-on nc sy bh) env ef lo =
      src-on nc (sh sy env ef lo′) (behind-bef {C = C} bh (few sy env ef lo′))
      where lo′ = λ {κ} (ki : KeyIn _ κ) → lo (k-kid (k-src ki))
    src-sh (src-shut cl sp fn bh) env ef lo = src-shut cl (spent sp) (fd fn) (behind-bef {C = C} bh (fin-lag {C = C} fn))

    joined-sh : ∀ {Γ} {sc : Scope Γ} {Rl} {A B} {P : Pol A B} {O : EmissionSet A} {d n qu ls}
              → (∀ {q e} → Due C O q e → p ≼ q) → Joined sc Rl C P O d n qu ls
              → Env (full sc) C p → EnvF (full sc) p → (∀ {l} → l ∈ ls → Lo l (at p)) → Joined sc Rl (bef p) P O d n qu ls
    joined-sh {P = P} {O} ob (joined {vs = vs} {ws = ws} bg (eq , ap , wf) wh od ah ao en li) env ef lo =
      joined (begun-sh bg env ef lo) (eq , ap , wait) whole od′ ahead ao en li
      where
        lead : ∀ {q a s} → (q , a) ∈ ws → adequacy.Cursor.Start P q a s → p ≼ s
        lead i st with ah i st
        ... | q′ , a′ , c , iv , lc , kc , oc , cz = on p c _ (begun-b {O = O} {k = c} {e = end} bg iv kc lc tt oc en env lo) cz
        wait : ∀ {q a} → (q , a) ∈ ws → O q (out a) × ¬ Owes (bef p) q × Runs P q × (∀ {s} → adequacy.Cursor.Start P q a s → Owes (bef p) s)
        wait i with wf i
        ... | y , nq , r , _ = y , nm nq , r , λ {s} st → lead {s = s} i st
        whole : Whole (bef p) P O vs ws
        whole {q} y nq r with owes? C q
        ... | inj₁ o = ⊥-elim (nq (ob (y , tt , o)))
        ... | inj₂ n = wh y n r
        od′ = (λ t → let (c , y , n) = proj₁ od t in c , y , nm n)
            , (λ {c} y n → [ (λ o → ⊥-elim (n (ob (y , tt , o)))) , proj₂ od y ]′ (owes? C c))
        ahead : Ahead (bef p) P vs ws
        ahead i st with ah i st
        ... | q′ , a′ , c , iv , lc , kc , oc , cz = q′ , a′ , c , iv , lc , kc , begun-b {O = O} {k = c} {e = end} bg iv kc lc tt oc en env lo , cz

    begun-sh : ∀ {Γ} {sc : Scope Γ} {Rl} {A B} {P : Pol A B} {O vs ls n}
             → Begun sc Rl C P O vs ls n → Env (full sc) C p → EnvF (full sc) p → (∀ {l} → l ∈ ls → Lo l (at p)) → Begun sc Rl (bef p) P O vs ls n
    begun-sh none                 env ef lo = none
    begun-sh (more y nq r ln bg) env ef lo = more y (nm nq) r (lane-sh ln env ef (lo (here refl))) (begun-sh bg env ef (λ i → lo (there i)))

    lane-sh : ∀ {Γ} {sc : Scope Γ} {Rg} {A B} {P : Pol A B} {q a l b}
            → LaneSt sc Rg C P q a l b → Env (full sc) C p → EnvF (full sc) p → Lo l (at p) → LaneSt sc Rg (bef p) P q a l b
    lane-sh (l-live (h-live st ns eq) sy sd) env ef lo = l-live (h-live st (nm ns) eq) (sh sy env ef (λ ki → lo (k-kid (k-ln (k-kid (k-cut ki)))))) sd
    lane-sh (l-dead {E = E} (h-end lc nc fk)) env ef lo = l-dead {E = E} (h-end lc (nm nc) (fd fk))
    lane-sh (l-dead {E = E} (h-kill kq nq fk)) env ef lo = l-dead {E = E} (h-kill kq (nm nq) (fd fk))

shift : ∀ {Γ} {sc : Scope Γ} {Rg} {C A} {s : St Γ A} {E p} → Sync sc Rg C s E → Owes C p → Env (full sc) C p → EnvF (full sc) p
      → Lo s (at p) → Sync sc Rg (bef p) s E
shift sy op env ef lo = Shifted.sh op sy env ef lo
