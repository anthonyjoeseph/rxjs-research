{-# OPTIONS --guardedness #-}

-- THE TIE: every row a live node's meaning holds is listed, led by a key
-- of the node's own subtree, a joiner's copy of a row its handle holds,
-- or not before the subscription in progress.  Against the floor, which
-- puts every key past the cursor, that leaves finitely many rows before
-- the cursor: of a live connect's source, and of a live joiner, which is
-- what the simulation reads at a body's rise and a joiner's.
--
-- Cursor-free, so a step that only moves the cursor keeps it; held at
-- every node of the tree, live or dead, as one recursion over the state,
-- so a step keeps it by refilling only the subtree it moves.  A dead node
-- owes nothing: a torn-down source's later rows are no live node's.
--
-- A handle's rows are tied where its connect's source lives, never under
-- the joiner, so each node reads them through `HEnv`: a live connect's
-- frozen source, or nothing once the connect is closed off or torn down.
module adequacy.Tie where

open import Data.Bool using (Bool; true; false; T; not; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; _ʳ++_) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs)
open import denotation.Events using (Pos; Timeline; ix; sub; last; <ᵖ-asym)
open import denotation.EmissionSet using (EmissionSet; Ev; _≺_; end) renaming (Reach to Reachᴱ)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext)
open import operation.Key using (Key; at; after; _<ᴷ_; ≮ᴷ-trans)
open import operation.PureObservable using (PureObs; module Machine; module Driver)
open Machine using (St; Ctx; CS; Scope; unbound; binds; plug; scopeOf; closed; Conf; ⟨_,_,_,_⟩; Mode; subscribing; absorbed; rising;
                    search; found; rise; begin; run; load; cp;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (Frozen; toEv)
open import adequacy.Least using (KeyIn; Lo; k-kid; k-map; k-scan; k-cut; k-ln; k-take; k-outer; k-lane; k-src; k-body)
open import adequacy.Cursor using (FewBefore; JoinG)
open import adequacy.Path using (Path; []; tau; val; _▸_)
open import adequacy.Stamped using (pend-focus)
open import adequacy.Floor.Keys using (mem-self; plug-in)
open import adequacy.Apart.Region using (past-at)
open import adequacy.Apart.Floor using (floor)

------------------------------------------------------------------------
-- Rows as positions

Pred : Set₁
Pred = Pos → Set

Rows : ∀ {A} → EmissionSet A → Pred
Rows {A} t y = Σ (Ev A) (t y)

-- Every row of `Y` listed, or led as `X` says.
Cov : Pred → (Pos → Set₁) → Set₁
Cov Y X = Σ (List Pos) λ ks → ∀ {y} → Y y → y ∈ ks ⊎ X y

-- Finitely many rows of `Y` before `p`.
FewP : Pred → Pos → Set
FewP Y p = Σ (List Pos) λ ks → ∀ {y} → Y y → y ≺ p → y ∈ ks

-- A key of `s` at or before `y`.
Ahd : ∀ {Γ A} → St Γ A → Pos → Set₁
Ahd s y = Σ Key λ κ → KeyIn s κ × at y <ᴷ κ ≡ false

-- Led: by a key of the subtree, or by the subscription in progress.
Lead : ∀ {Γ A} → Pred → St Γ A → Pos → Set₁
Lead F s y = Ahd s y ⊎ F y

------------------------------------------------------------------------
-- The handles' rows

-- The rows each handle in scope holds, as far as they are tied.
HEnv : List Set → Set₁
HEnv Γ = ∀ {X} → X ∈ Γ → Pred

none : HEnv []
none ()

_∷ᴴ_ : ∀ {Γ X} → Pred → HEnv Γ → HEnv (X ∷ Γ)
(P ∷ᴴ H) (here refl) = P
(P ∷ᴴ H) (there x)   = H x

-- A connect's handle: its frozen source, while the connect is neither
-- closed off nor torn down.
HK : ∀ {Γ X} → Bool → CS Γ X → Pred
HK cl k y = T (not cl) × T (CS.srcLive k) × Rows (Frozen k) y

-- The rows of `s`'s joiners, each a copy of its handle's under where it
-- joined, or its late end; `cl` whether the node is closed off.
mutual
  Fed : ∀ {Γ A} → HEnv Γ → Bool → St Γ A → Pred
  Fed H cl (pend o q)                y = ⊥
  Fed H cl (coldS b l)               y = ⊥
  Fed H cl (ofS i q xs)              y = ⊥
  Fed H cl doneS                     y = ⊥
  Fed H cl (mapS f s)                y = Fed H cl s y
  Fed H cl (scanS f z s)             y = Fed H cl s y
  Fed H cl (cutS l a s)              y = Fed H (not l ∨ cl) s y
  Fed H cl (lnS b s)                 y = Fed H cl s y
  Fed H cl (takeS i q w s)           y = Fed H cl s y
  Fed H cl (flatS op f ω d n q o ls) y = Fed H cl o y ⊎ FedL H cl ls y
  Fed H cl (connS k o b)             y = Fed H (CS.closed k ∨ cl) o y ⊎ Fed (HK cl k ∷ᴴ H) cl b y
  Fed H cl (joinS j g x ib)          y = (Σ Pos λ h → H x h × y ≡ h ++ [ sub j ]) ⊎ y ≡ j ++ [ last ]

  FedL : ∀ {Γ B} → HEnv Γ → Bool → List (St Γ B) → Pred
  FedL H cl []       y = ⊥
  FedL H cl (l ∷ ls) y = Fed H cl l y ⊎ FedL H cl ls y

------------------------------------------------------------------------
-- THE TIE: at every live connect, its frozen source's rows; at every live
-- joiner, its meaning's rows.

mutual
  Tight : ∀ {Γ A} → Scope Γ → HEnv Γ → Bool → Pred → St Γ A → Set₁
  Tight sc H cl F (pend o q)      = ⊤₁
  Tight sc H cl F (coldS b l)     = ⊤₁
  Tight sc H cl F (ofS i q xs)    = ⊤₁
  Tight sc H cl F doneS           = ⊤₁
  Tight sc H cl F (mapS f s)      = Tight sc H cl F s
  Tight sc H cl F (scanS f z s)   = Tight sc H cl F s
  Tight sc H cl F (cutS l a s)    = Tight sc H (not l ∨ cl) F s
  Tight sc H cl F (lnS b s)       = Tight sc H cl F s
  Tight sc H cl F (takeS i q w s) = Tight sc H cl F s
  Tight sc H cl F (flatS op f ω d n q o ls) =
      (T (not cl) → Cov (Rows (JoinG sc op f ω)) λ y → Lead F (flatS op f ω d n q o ls) y ⊎ Fed H cl (flatS op f ω d n q o ls) y)
    × Tight sc H cl F o × TightL sc H cl F ls
  Tight sc H cl F (connS k o b) =
      (T (not cl) → T (CS.srcLive k) → Cov (Rows (Frozen k)) λ y → Lead F (connS k o b) y ⊎ Fed H (CS.closed k ∨ cl) o y)
    × Tight sc H (CS.closed k ∨ cl) F o × Tight (binds (CS.src k) (CS.connAt k) (CS.scope k)) (HK cl k ∷ᴴ H) cl F b
  Tight sc H cl F (joinS j g x ib) = ⊤₁

  TightL : ∀ {Γ B} → Scope Γ → HEnv Γ → Bool → Pred → List (St Γ B) → Set₁
  TightL sc H cl F []       = ⊤₁
  TightL sc H cl F (l ∷ ls) = Tight sc H cl F l × TightL sc H cl F ls

-- Rows not before a subscription in progress.
Fresh : ∀ {A} → Mode A → Pos → Pred
Fresh subscribing p y = ¬ (y ≺ p)
Fresh absorbed    p y = ⊥
Fresh (rising e)  p y = ⊥

TieK : ∀ {R} → Conf R → Set₁
TieK ⟨ c , s , m , p ⟩ = Tight unbound none false (Fresh m p) (plug c s)

------------------------------------------------------------------------
-- FEW BEFORE THE FLOOR: with every key past `p`, a tied set's rows before
-- `p` are listed or fed, and a handle's are few in turn.

-- Rows of `F` none before `p`.
NoF : Pred → Pos → Set
NoF F p = ∀ {y} → F y → y ≺ p → ⊥

-- Every handle's rows few before `p`.
EnvF : ∀ {Γ} → HEnv Γ → Pos → Set₁
EnvF {Γ} H p = ∀ {X} (x : X ∈ Γ) → FewP (H x) p

private
  F-false : ∀ {b} → b ≡ false → T b → ⊥
  F-false refl ()

  T-not : ∀ {b} → b ≡ false → T (not b)
  T-not refl = tt

  few-∪ : ∀ {Y Z p} → FewP Y p → FewP Z p → FewP (λ y → Y y ⊎ Z y) p
  few-∪ (ks , f) (ks′ , g) = ks ++ ks′ , λ { {y} (inj₁ a) yp → ∈-++⁺ˡ (f {y} a yp) ; {y} (inj₂ z) yp → ∈-++⁺ʳ ks (g {y} z yp) }

  few-∅ : ∀ {p} → FewP (λ _ → ⊥) p
  few-∅ = [] , λ ()

  -- A condition false: nothing.
  cond : ∀ a b {Y p} → (T (not a) → T b → FewP Y p) → FewP (λ y → T (not a) × T b × Y y) p
  cond false true  g with g tt tt
  ... | ks , f = ks , λ { {y} (_ , _ , r) yp → f {y} r yp }
  cond false false g = [] , λ { {_} (_ , () , _) _ }
  cond true  _     g = [] , λ { {_} (() , _) _ }

-- No key before `p`: nothing led by one is.
ahd-lo : ∀ {Γ A} {s : St Γ A} {p y} → Lo s (after p) → Ahd s y → y ≺ p → ⊥
ahd-lo {p = p} {y} lo (κ , ki , le) yp =
  F-false (<ᵖ-asym p y (past-at p y (≮ᴷ-trans (at y) κ (after p) le (lo ki)))) yp

-- A tied set few, given its feeds are.
fin-cov : ∀ {Γ A} {s : St Γ A} {Y F Z p} → Cov Y (λ y → Lead F s y ⊎ Z y) → Lo s (after p) → NoF F p → FewP Z p → FewP Y p
fin-cov {Y = Y} {p = p} (ks , cv) lo nf (ks′ , fz) = ks ++ ks′ , go
  where
    go : ∀ {y} → Y y → y ≺ p → y ∈ ks ++ ks′
    go {y} yy yp with cv yy
    ... | inj₁ m                 = ∈-++⁺ˡ m
    ... | inj₂ (inj₁ (inj₁ a))   = ⊥-elim (ahd-lo {y = y} lo a yp)
    ... | inj₂ (inj₁ (inj₂ f))   = ⊥-elim (nf {y} f yp)
    ... | inj₂ (inj₂ z)          = ∈-++⁺ʳ ks (fz z yp)

-- A joiner's copies few, its handle's rows being few.
copies : ∀ {H : Pred} {j p} → FewP H p → FewP (λ y → (Σ Pos λ h → H h × y ≡ h ++ [ sub j ]) ⊎ y ≡ j ++ [ last ]) p
copies {H = H} {j} {p} (ks , f) = mapL (λ h → h ++ [ sub j ]) ks ++ [ j ++ [ last ] ] , go
  where
    go : ∀ {y} → (Σ Pos λ h → H h × y ≡ h ++ [ sub j ]) ⊎ y ≡ j ++ [ last ] → y ≺ p → y ∈ mapL (λ h → h ++ [ sub j ]) ks ++ [ j ++ [ last ] ]
    go (inj₁ (h , hh , refl)) yp = ∈-++⁺ˡ (∈-map⁺ (λ h → h ++ [ sub j ]) (f {h} hh (≺-trans {h} {h ++ [ sub j ]} {p} (≺-ext h {sub j} []) yp)))
    go (inj₂ refl)            yp = ∈-++⁺ʳ _ (here refl)

-- THE FEEDS FEW: every joiner's copies, each handle's rows few, those of
-- a connect inside the subtree by its own tie.
mutual
  fed-few : ∀ {Γ A} {sc : Scope Γ} {H : HEnv Γ} {cl F p} (s : St Γ A) → Tight sc H cl F s → EnvF H p → Lo s (after p) → NoF F p
          → FewP (Fed H cl s) p
  fed-few (pend o q)                t env lo nf = few-∅
  fed-few (coldS b l)               t env lo nf = few-∅
  fed-few (ofS i q xs)              t env lo nf = few-∅
  fed-few doneS                     t env lo nf = few-∅
  fed-few (mapS f s)                t env lo nf = fed-few s t env (λ h → lo (k-kid (k-map h))) nf
  fed-few (scanS f z s)             t env lo nf = fed-few s t env (λ h → lo (k-kid (k-scan h))) nf
  fed-few (cutS l a s)              t env lo nf = fed-few s t env (λ h → lo (k-kid (k-cut h))) nf
  fed-few (lnS b s)                 t env lo nf = fed-few s t env (λ h → lo (k-kid (k-ln h))) nf
  fed-few (takeS i q w s)           t env lo nf = fed-few s t env (λ h → lo (k-kid (k-take h))) nf
  fed-few (flatS op f ω d n q o ls) (_ , to , tl) env lo nf =
    few-∪ (fed-few o to env (λ h → lo (k-kid (k-outer h))) nf) (fed-fewL ls tl env (λ m h → lo (k-kid (k-lane m h))) nf)
  fed-few (connS k o b)             t@(_ , to , tb) env lo nf =
    few-∪ (fed-few o to env (λ h → lo (k-kid (k-src h))) nf)
          (fed-few b tb (hk-env k o b t env lo nf) (λ h → lo (k-kid (k-body h))) nf)
  fed-few (joinS j g x ib)          t env lo nf = copies (env x)

  fed-fewL : ∀ {Γ B} {sc : Scope Γ} {H : HEnv Γ} {cl F p} (ls : List (St Γ B)) → TightL sc H cl F ls → EnvF H p
           → (∀ {l κ} → l ∈ ls → KeyIn l κ → κ <ᴷ after p ≡ false) → NoF F p → FewP (FedL H cl ls) p
  fed-fewL []       t        env lo nf = few-∅
  fed-fewL (l ∷ ls) (tl , ts) env lo nf = few-∪ (fed-few l tl env (lo (here refl)) nf) (fed-fewL ls ts env (λ m → lo (there m)) nf)

  -- A connect's handle few, by its source's tie.
  hk-few : ∀ {Γ X B} {sc : Scope Γ} {H : HEnv Γ} {cl F p} (k : CS Γ X) o (b : St (X ∷ Γ) B) → Tight sc H cl F (connS k o b) → EnvF H p
         → Lo (connS k o b) (after p) → NoF F p → FewP (HK cl k) p
  hk-few {cl = cl} k o b (tc , to , _) env lo nf =
    cond cl (CS.srcLive k) λ nc sl → fin-cov (tc nc sl) lo nf (fed-few o to env (λ h → lo (k-kid (k-src h))) nf)

  hk-env : ∀ {Γ X B} {sc : Scope Γ} {H : HEnv Γ} {cl F p} (k : CS Γ X) o (b : St (X ∷ Γ) B) → Tight sc H cl F (connS k o b) → EnvF H p
         → Lo (connS k o b) (after p) → NoF F p → EnvF (HK cl k ∷ᴴ H) p
  hk-env k o b t env lo nf (here refl) = hk-few k o b t env lo nf
  hk-env k o b t env lo nf (there x)   = env x

------------------------------------------------------------------------
-- Down a context: the tie at the hole, under the handles its scope binds.

module _ {R : Set} where

  -- The handles in scope at the hole.
  envOf : ∀ {Γ A} → Ctx R Γ A → HEnv Γ
  envOf top                               = none
  envOf (inMap f c)                       = envOf c
  envOf (inScan f z c)                    = envOf c
  envOf (inCut l a c)                     = envOf c
  envOf (inLn b c)                        = envOf c
  envOf (inTake i q w c)                  = envOf c
  envOf (inOuter op f ω d n q ls c)         = envOf c
  envOf (inLanes op f ω d n q o pre post c) = envOf c
  envOf (inSrc k b c)                     = envOf c
  envOf (inBody k o c)                    = HK (closed c) k ∷ᴴ envOf c

  private
    tl-∈ : ∀ {Γ B} {sc : Scope Γ} {H : HEnv Γ} {cl F} {ls : List (St Γ B)} {l} → l ∈ ls → TightL sc H cl F ls → Tight sc H cl F l
    tl-∈ (here refl) (t , _)  = t
    tl-∈ (there m)   (_ , ts) = tl-∈ m ts

  down : ∀ {Γ A} {F} (c : Ctx R Γ A) {s} → Tight unbound none false F (plug c s) → Tight (scopeOf c) (envOf c) (closed c) F s
  down top                               t = t
  down (inMap f c)                       t = down c t
  down (inScan f z c)                    t = down c t
  down (inCut l a c)                     t = down c t
  down (inLn b c)                        t = down c t
  down (inTake i q w c)                  t = down c t
  down (inOuter op f ω d n q ls c)         t = proj₁ (proj₂ (down c t))
  down (inLanes op f ω d n q o pre post c) t = tl-∈ (mem-self pre) (proj₂ (proj₂ (down c t)))
  down (inSrc k b c)                     t = proj₁ (proj₂ (down c t))
  down (inBody k o c)                    t = proj₂ (proj₂ (down c t))

  lo-plug : ∀ {Γ A} (c : Ctx R Γ A) {s h} → Lo (plug c s) h → Lo s h
  lo-plug c lo ki = lo (plug-in c ki)

  -- Every handle in scope at the hole few before the floor.
  env-down : ∀ {Γ A} {F p} (c : Ctx R Γ A) {s} → Tight unbound none false F (plug c s) → Lo (plug c s) (after p) → NoF F p
           → EnvF (envOf c) p
  env-down top                               t lo nf ()
  env-down (inMap f c)                       t lo nf = env-down c t lo nf
  env-down (inScan f z c)                    t lo nf = env-down c t lo nf
  env-down (inCut l a c)                     t lo nf = env-down c t lo nf
  env-down (inLn b c)                        t lo nf = env-down c t lo nf
  env-down (inTake i q w c)                  t lo nf = env-down c t lo nf
  env-down (inOuter op f ω d n q ls c)         t lo nf = env-down c t lo nf
  env-down (inLanes op f ω d n q o pre post c) t lo nf = env-down c t lo nf
  env-down (inSrc k b c)                     t lo nf = env-down c t lo nf
  env-down {p = p} (inBody k o c) {s}        t lo nf = hk-env k o s (down c t) (env-down {p = p} c t lo nf) (lo-plug c {connS k o s} {after p} lo) nf

------------------------------------------------------------------------
-- A STEP KEEPS THE TIE, by the conf's mode: a rise, a subscription, the
-- least mark's run.

module _ {R : Set} where
  open Driver R using (Step; silent; value; complete; drained; took; step)

  NextT : Step → Set₁
  NextT (silent _ k)    = TieK k
  NextT (value _ _ _ k) = TieK k
  NextT (complete _)    = ⊤₁
  NextT drained         = ⊤₁

  postulate
    tie-rise  : ∀ (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s e p}
              → Path (load o) rs ⟨ c , s , rising e , p ⟩ → TieK ⟨ c , s , rising e , p ⟩ → NextT (took (rise c s e p))
    tie-begin : ∀ (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {o′ : PureObs Γ A} {p}
              → Path (load o) rs ⟨ c , pend o′ p , subscribing , p ⟩ → TieK ⟨ c , pend o′ p , subscribing , p ⟩ → NextT (took (begin c o′ p))
    tie-run   : ∀ (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s p Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ}
              → Path (load o) rs ⟨ c , s , absorbed , p ⟩ → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , s′) m κ)
              → TieK ⟨ c , s , absorbed , p ⟩ → NextT (took (run c′ s′ m p))

  tie-step : ∀ (o : PureObs [] R) {rs k} → Path (load o) rs k → TieK k → NextT (step k)
  tie-step o {k = ⟨ c , s , rising e , p ⟩} pth t = tie-rise o pth t
  tie-step o {k = ⟨ c , s , subscribing , p ⟩} pth t with pend-focus o pth
  ... | o′ , refl = tie-begin o pth t
  tie-step o {k = ⟨ c , s , absorbed , p ⟩} pth t with search top (plug c s) in fd
  ... | nothing                            = tt₁
  ... | just (found (_ , _ , c′ , s′) m κ) = tie-run o pth fd t

  tie-path : ∀ (o : PureObs [] R) {rs rs′ k k″} → Path (load o) rs k → TieK k → Path k rs′ k″ → TieK k″
  tie-path o pre t []          = t
  tie-path o pre t (tau e pth) = tie-path o (pre ▸ tau e []) (subst NextT e (tie-step o pre t)) pth
  tie-path o pre t (val e pth) = tie-path o (pre ▸ val e []) (subst NextT e (tie-step o pre t)) pth

  -- THE TIE, everywhere a run reaches.
  tie : ∀ (o : PureObs [] R) {rs k} → Path (load o) rs k → TieK k
  tie o pth = tie-path o [] tt₁ pth

------------------------------------------------------------------------
-- WHAT THE SIMULATION READS: at a live body's rise, its source's rows
-- before it few; at a live joiner's outer end or lane's rise, the joiner's.

module _ {R : Set} (o : PureObs [] R) where

  private
    nf₀ : ∀ {A} {e : Machine.Ev A} {p} → NoF (Fresh (rising e) p) p
    nf₀ ()

  few-body : ∀ {rs Γ X B} {k : CS Γ X} {o′} {c : Ctx R Γ B} {s e p}
           → Path (load o) rs ⟨ inBody k o′ c , s , rising e , p ⟩ → closed c ≡ false → CS.srcLive k ≡ true → FewBefore (Frozen k) p
  few-body {k = k} {o′} {c} {s} {e} {p} pth op lv with down c (tie o pth) | floor o pth tt
  ... | tc@(cv , to , _) | lo = proj₁ fp , λ {y} r yp → proj₂ fp {y} (_ , r) (≺-trans {y} {y ++ [ ix 0 ]} {p} (≺-ext y {ix 0} []) yp)
    where
      fp : FewP (Rows (Frozen k)) p
      fp = fin-cov {p = p} (cv (T-not op) (subst T (sym lv) tt)) (lo-plug c {connS k o′ s} {after p} lo) (λ {y} → nf₀ {e = e} {p} {y})
             (fed-few {p = p} o′ to (env-down {p = p} c {connS k o′ s} (tie o pth) lo (λ {y} → nf₀ {e = e} {p} {y}))
               (λ h → lo-plug c {connS k o′ s} {after p} lo (k-kid (k-src h))) (λ {y} → nf₀ {e = e} {p} {y}))

  -- A live joiner's rows before the floor few.
  flat-few : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {ω d n qu} {ou : St Γ A} {ls} (c : Ctx R Γ B) {F p}
           → Tight unbound none false F (plug c (flatS op f ω d n qu ou ls)) → Lo (plug c (flatS op f ω d n qu ou ls)) (after p) → NoF F p
           → closed c ≡ false → FewP (Rows (JoinG (scopeOf c) op f ω)) p
  flat-few {op = op′} {f} {ω} {d} {n} {qu} {ou} {ls} c {p = p} t lo nf op with down c {flatS op′ f ω d n qu ou ls} t
  ... | cv , to , tl =
    fin-cov {p = p} (cv (T-not op)) (lo-plug c {flatS op′ f ω d n qu ou ls} {after p} lo) nf
      (fed-few {p = p} (flatS op′ f ω d n qu ou ls) (cv , to , tl) (env-down {p = p} c {flatS op′ f ω d n qu ou ls} t lo nf)
        (lo-plug c {flatS op′ f ω d n qu ou ls} {after p} lo) nf)

  few-outer : ∀ {rs Γ A B} {op} {f : A → Obs Timeline Γ B} {ω d n qu ls} {c : Ctx R Γ B} {s : St Γ A} {p}
            → Path (load o) rs ⟨ inOuter op f ω d n qu ls c , s , rising cp , p ⟩ → closed c ≡ false
            → Reachᴱ (JoinG (scopeOf c) op f ω) p end
  few-outer {A = A} {op = op′} {f} {ω} {d} {n} {qu} {ls} {c} {s} {p} pth op
    with flat-few {op = op′} {f} {ω} {d} {n} {qu} {s} {ls} c {p = p} (tie o pth) (floor o pth tt) (λ {y} → nf₀ {A} {cp} {p} {y}) op
  ... | ks , f = ks , λ {y} r kp _ → f {y} (_ , r) kp

  few-lane : ∀ {rs Γ A B} {op} {f : A → Obs Timeline Γ B} {ω d n qu ou pre post} {c : Ctx R Γ B} {s : St Γ B} {e p}
           → Path (load o) rs ⟨ inLanes op f ω d n qu ou pre post c , s , rising e , p ⟩ → closed c ≡ false
           → Reachᴱ (JoinG (scopeOf c) op f ω) p (toEv e)
  few-lane {op = op′} {f} {ω} {d} {n} {qu} {ou} {pre} {post} {c} {s} {e} {p} pth op
    with flat-few {op = op′} {f} {ω} {d} {n} {qu} {ou} {pre ʳ++ s ∷ post} c {p = p} (tie o pth) (floor o pth tt) (λ {y} → nf₀ {e = e} {p} {y}) op
  ... | ks , f = ks , λ {y} r kp _ → f {y} (_ , r) kp
