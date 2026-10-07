------------------------------------------------------------------
-- A FRESH PAIR INSTALLED, AND THE STORES STILL RELATED.  An install
-- writes only at nodes at or above the counters and joins `π` with the
-- pair it wrote.  Every node a relation reads is a key or value of `π`,
-- below the counters by `Store.pairs-below`, or a registered row's, below
-- them by the rule's `fresh-rows`; so every read sees what it saw, and
-- an impl-only node a row reads stays unpaired, the new pair being above
-- it.
------------------------------------------------------------------
module Simulation.Install where

open import Data.Bool    using (T)
open import Data.List    using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Binary.Pointwise using () renaming ([] to []ᵖ)
open import Data.List.Relation.Unary.All using (All; []; _∷_; head; tail; tabulate) renaming (lookup to all-lookup)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.Unique.Propositional.Properties using (++⁺)
open import Data.Nat     using (ℕ; _<_; _≤_)
open import Data.Nat.Properties using (<-≤-trans; <⇒≱; <⇒≤; <⇒≢)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Rx.Exp       using (Ctx; Ty; Closed)
open import Rx.Mint      using (Mint; counter; sourceᵏ; regᵏ; nodeᵏ; freshId)
open import Rx.Evaluator using (NodeId; NodeState; Sched; EvalSt; Path; root; share-sink; _↠[_]_; frameNodes; pathHasNode; RegRow; lookupNode; setNode)
open import Rx.Evaluator.Freshness using (nodeCt; set-above)
open import Rx.Evaluator.Reducible.Support using (sub-rule; fresh-rows; rowThrough; ∨-Tˡ; ∨-Tʳ)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ)
open import Simulation.Stores using (Unpaired; Flattener; PathRel; root~; sink~; map~; scan~; takeWhile~; spentWhile~; outerElem~;
  outerExplode~; inner~; deferInner~; InputBlock; block; RowRel; read~; cold~; defer~; MachRow; hot~; RegRel; []; _∷_; mach;
  Partners; ArrRows; Spent; Store; Arr)
open import Simulation.Grow using (mem-any; nodes-grow)
open import Simulation.Write using () renaming (apart to apart′)
open import Simulation.After using (below-keys; below-vals; apart; module Kept)

-- every node a path names, frame by frame, below a bound
Low : ∀ {n} {Γ : Ctx n} {lo s w} → ℕ → Path Γ lo s w → Set
Low c root             = ⊤
Low c (share-sink _ _) = ⊤
Low c (f ↠[ _ ] q)     = All (_< c) (frameNodes f) × Low c q

low : ∀ {n} {Γ : Ctx n} {lo s w c} (q : Path Γ lo s w) → (∀ k → T (pathHasNode k q) → k < c) → Low c q
low root             _  = tt
low (share-sink _ _) _  = tt
low (f ↠[ _ ] q)     lt = tabulate (λ {k} k∈ → lt k (∨-Tˡ (mem-any k∈))) , low q (λ k h → lt k (∨-Tʳ h))

LowRow : ∀ {n} {Γ : Ctx n} {w} → ℕ → RegRow Γ w → Set
LowRow c (_ , _ , (_ , p)) = Low c p

low-row : ∀ {n} {Γ : Ctx n} {w c} (r : RegRow Γ w) → (∀ k → T (rowThrough k r) → k < c) → LowRow c r
low-row (_ , _ , (_ , p)) = low p

-- a write at or above a bound leaves every node below it as it was
fresh-set : ∀ {n} {Γ : Ctx n} {c} k (v : NodeState Γ) N → c ≤ k → ∀ j → j < c → lookupNode j (setNode k v N) ≡ lookupNode j N
fresh-set k v N le j lt = set-above k j v N (apart′ k j (<⇒≢ (<-≤-trans lt le)))

-- what is below a bound is below a larger one
weak : ∀ {A : Set} {f : A → ℕ} {xs a b} → a ≤ b → All (λ x → f x < a) xs → All (λ x → f x < b) xs
weak le []       = []
weak le (p ∷ ps) = <-≤-trans p le ∷ weak le ps

weak₂ : ∀ {A : Set} {f : A → List ℕ} {xs a b} → a ≤ b → All (λ x → All (_< a) (f x)) xs → All (λ x → All (_< b) (f x)) xs
weak₂ le []       = []
weak₂ le (p ∷ ps) = weak {f = λ x → x} le p ∷ weak₂ le ps

-- a node below a bound is none of a pair above it
above-unpaired : ∀ {n} {Γ : Ctx n} {κ : Kinds n} {π j xs k c} → All (c ≤_) xs → k < c
               → Unpaired {Γ = Γ} κ π k → Unpaired {Γ = Γ} κ ((j , xs) ∷ π) k
above-unpaired {xs = xs} ax lt un k∈ with ∈-++⁻ xs k∈
... | inj₁ kx = <⇒≱ lt (all-lookup ax kx)
... | inj₂ kπ = un kπ

-- THE RELATIONS CARRIED TO THE GROWN `π` AND THE WRITTEN TABLES, each
-- read moved by the bound its node already has
module Move {n} {Γ : Ctx n} (κ : Kinds n) {π : List (NodeId × List NodeId)} {j : NodeId} {xs : List NodeId} {cP cI : ℕ}
            (ax : All (cI ≤_) xs) (bP : All (λ e → proj₁ e < cP) π) (bI : All (λ e → All (_< cI) (proj₂ e)) π)
            {t : Ty} {NP NP′ : List (NodeId × NodeState Γ)} {NI NI′ : List (NodeId × NodeState (plainᵏ Γ κ))}
            (aP : ∀ k → k < cP → lookupNode k NP′ ≡ lookupNode k NP)
            (aI : ∀ k → k < cI → lookupNode k NI′ ≡ lookupNode k NI) where

  Lw : RegRow (plainᵏ Γ κ) (emitᵗ t) → Set
  Lw = LowRow cI

  keyP : ∀ {k ys} → (k , ys) ∈ π → k < cP
  keyP e = all-lookup bP e

  valI : ∀ {k ys z} → (k , ys) ∈ π → z ∈ ys → z < cI
  valI e z∈ = all-lookup (all-lookup bI e) z∈

  rdP : ∀ {k v} → k < cP → lookupNode k NP ≡ v → lookupNode k NP′ ≡ v
  rdP {k} lt l = trans (aP k lt) l

  rdI : ∀ {k v} → k < cI → lookupNode k NI ≡ v → lookupNode k NI′ ≡ v
  rdI {k} lt l = trans (aI k lt) l

  fresh : ∀ {k} → k < cI → Unpaired {Γ = Γ} κ π k → Unpaired {Γ = Γ} κ ((j , xs) ∷ π) k
  fresh = above-unpaired {Γ = Γ} {κ = κ} {π = π} {j = j} ax

  flatM : ∀ {u op m m′ ks ys} → Flattener κ π {t = t} NP NI u op m m′ ks ys → Flattener κ ((j , xs) ∷ π) {t = t} NP′ NI′ u op m m′ ks ys
  flatM (pm , x , x′ , lP , lI , fn , c , lk) =
    there pm , x , x′ , rdP (keyP pm) lP , rdI (valI pm (here refl)) lI , nodes-grow {Γ = Γ} κ there fn , c , rdI (valI pm (there (here refl))) lk

  pathM : ∀ {lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
        → PathRel κ π NP NI p q → PathRel κ ((j , xs) ∷ π) NP′ NI′ p q
  pathM root~                            = root~
  pathM (sink~ sh)                       = sink~ sh
  pathM (map~ L r)                       = map~ L (pathM r)
  pathM (scan~ e l l′ v L r)             = scan~ (there e) (rdP (keyP e) l) (rdI (valI e (here refl)) l′) v L (pathM r)
  pathM (takeWhile~ e l l₁ l₂ L r)       =
    takeWhile~ (there e) (rdP (keyP e) l) (rdI (valI e (here refl)) l₁) (rdI (valI e (there (here refl))) l₂) L (pathM r)
  pathM (spentWhile~ e l l₂ r)           = spentWhile~ (there e) (rdP (keyP e) l) (rdI (valI e (there (here refl))) l₂) (pathM r)
  pathM (outerElem~ f r)                 = outerElem~ (flatM f) (pathM r)
  pathM (outerExplode~ f r)              = outerExplode~ (flatM f) (pathM r)
  pathM (inner~ e f ip r)                = inner~ e (flatM f) (there ip) (pathM r)
  pathM (deferInner~ e₁ e₂ l l′ l₂ a≤ r) =
    deferInner~ (there e₁) (there e₂) (rdP (keyP e₁) l) (rdI (valI e₁ (here refl)) l′) (rdI (valI e₂ (there (here refl))) l₂) a≤ (pathM r)

  blockM : ∀ {a lo ℓ} {full : Path (plainᵏ Γ κ) lo a (emitᵗ t)} {q}
         → Low cI full → InputBlock κ π NP NI a {lo} {ℓ} full q → InputBlock κ ((j , xs) ∷ π) NP′ NI′ a full q
  blockM o (block l₁ a≤ lb l₂ u₁ uj ub u₂) =
    block (rdI (head (proj₁ (proj₂ o))) l₁) a≤ (rdI (head (proj₁ (proj₂ (proj₂ o)))) lb)
          (rdI (head (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ o))))))) l₂)
          (fresh (head (proj₁ (proj₂ o))) u₁) (fresh (head (tail (proj₁ (proj₂ o)))) uj)
          (fresh (head (proj₁ (proj₂ (proj₂ o)))) ub) (fresh (head (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ o))))))) u₂)

  module _ {LP LI} where

    rowM : ∀ {r r′} → Lw r′ → RowRel κ π NP NI LP LI r r′ → RowRel κ ((j , xs) ∷ π) NP′ NI′ LP LI r r′
    rowM o (read~ hs r refl)         = read~ hs (pathM r) refl
    rowM o (cold~ sp b r refl)       = cold~ sp (blockM o b) (pathM r) refl
    rowM o (defer~ sp e l l′ r refl) = defer~ sp (there e) (rdP (keyP e) l) (rdI (valI e (here refl)) l′) (pathM r) refl

    machM : ∀ {r′} → Lw r′ → MachRow κ π {t = t} NP NI LP LI r′ → MachRow κ ((j , xs) ∷ π) NP′ NI′ LP LI r′
    machM o (hot~ hot b refl) = hot~ hot (blockM o b) refl

    regM : ∀ {rs rs′} → (∀ {r′} → r′ ∈ rs′ → Lw r′) → RegRel κ π NP NI LP LI rs rs′ → RegRel κ ((j , xs) ∷ π) NP′ NI′ LP LI rs rs′
    regM o []         = []
    regM o (r ∷ q)    = rowM (o (here refl)) r ∷ regM (λ r∈ → o (there r∈)) q
    regM o (mach r q) = mach (machM (o (here refl)) r) (regM (λ r∈ → o (there r∈)) q)

    -- the registries pair the same rows
    partM : ∀ {rs rs′} (o : ∀ {r′} → r′ ∈ rs′ → Lw r′) (q : RegRel κ π NP NI LP LI rs rs′) {r r′}
          → Partners κ π NP NI LP LI q r r′ → Partners κ ((j , xs) ∷ π) NP′ NI′ LP LI (regM o q) r r′
    partM o (_ ∷ q)    (inj₁ e) = inj₁ e
    partM o (_ ∷ q)    (inj₂ p) = inj₂ (partM (λ r∈ → o (there r∈)) q p)
    partM o (mach _ q) p        = partM (λ r∈ → o (there r∈)) q p

    -- and spend them alike
    spentM : ∀ {rs rs′} (o : ∀ {r′} → r′ ∈ rs′ → Lw r′) (q : RegRel κ π NP NI LP LI rs rs′) {dP dI}
           → Spent κ π NP NI LP LI q dP dI → Spent κ ((j , xs) ∷ π) NP′ NI′ LP LI (regM o q) dP dI
    spentM o []         s       = s
    spentM o (_ ∷ q)    (e , s) = e , spentM (λ r∈ → o (there r∈)) q s
    spentM o (mach _ q) s       = spentM (λ r∈ → o (there r∈)) q s

    -- and the same minted sources
    arrM : ∀ {rs rs′} (o : ∀ {r′} → r′ ∈ rs′ → Lw r′) (q : RegRel κ π NP NI LP LI rs rs′) {s s′ w w′}
         → ArrRows κ π NP NI LP LI q s s′ w w′ → ArrRows κ ((j , xs) ∷ π) NP′ NI′ LP LI (regM o q) s s′ w w′
    arrM o []                          _       = _
    arrM o (read~ _ _ refl ∷ q)        a       = arrM (λ r∈ → o (there r∈)) q a
    arrM o (cold~ _ _ _ refl ∷ q)      (r , a) = r , arrM (λ r∈ → o (there r∈)) q a
    arrM o (defer~ _ _ _ _ _ refl ∷ q) (r , a) = r , arrM (λ r∈ → o (there r∈)) q a
    arrM o (mach _ q)                  a       = arrM (λ r∈ → o (there r∈)) q a

module _ {n} {Γ : Ctx n} (κ : Kinds n) {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

  open Kept {Γ = Γ} κ {t} {ep} {ei}

  -- A FRESH INSTALL ON BOTH SIDES: the plain node at its counter, the
  -- impl's nodes at or above theirs, the counters moved past them and
  -- every node below them reading as it did.  The pair joins `π`, and
  -- whatever the stores related, the written ones relate
  install : ∀ {sP stP sI stI} (S : St sP stP sI stI) {mP mI : Mint} {NP NI xs}
          → nodeCt sP < freshId nodeᵏ mP → nodeCt sI ≤ freshId nodeᵏ mI
          → All (nodeCt sI ≤_) xs → All (_< freshId nodeᵏ mI) xs → Unique xs
          → counter (Sched.mint sP) sourceᵏ ≤ counter mP sourceᵏ → counter (Sched.mint sP) regᵏ ≤ counter mP regᵏ
          → counter (Sched.mint sI) sourceᵏ ≤ counter mI sourceᵏ → counter (Sched.mint sI) regᵏ ≤ counter mI regᵏ
          → (∀ k → k < nodeCt sP → lookupNode k NP ≡ lookupNode k (EvalSt.nodes stP))
          → (∀ k → k < nodeCt sI → lookupNode k NI ≡ lookupNode k (EvalSt.nodes stI))
          → ∀ {lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
          → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
          → Σ (After S ([] , record sP { mint = mP } , record stP { nodes = NP }) ([] , record sI { mint = mI } , record stI { nodes = NI })) λ A
              → (nodeCt sP , xs) ∈ Store.π (After.store A)
              × PathRel κ (Store.π (After.store A)) NP NI p q
  install {sP} {stP} {sI} {stI} S {mP} {mI} {NP} {NI} {xs} kP kI ax ab ux sP≤ rP≤ sI≤ rI≤ aP aI pr =
    after S′ (λ { (inj₁ c) → inj₁ c ; (inj₂ (a , b , pr)) → inj₂ (a , b , M.partM o rows pr) })
             (λ ar → record { boundP = <-≤-trans (Arr.boundP ar) sP≤ ; boundI = <-≤-trans (Arr.boundI ar) sI≤
                             ; rows = M.arrM o rows (Arr.rows ar) ; lists = Arr.lists ar })
             []ᵖ there
    , here refl , M.pathM pr
    where
    open Store S
    module M = Move {Γ = Γ} κ {π = π} {j = nodeCt sP} {xs = xs} ax (proj₁ pairs-below) (proj₂ pairs-below) {t = t}
                 {NP = EvalSt.nodes stP} {NP′ = NP} {NI = EvalSt.nodes stI} {NI′ = NI} aP aI
    o : ∀ {r′} → r′ ∈ EvalSt.registry stI → M.Lw r′
    o {r′} r∈ = low-row r′ (fresh-rows ruleI r∈)
    S′ : St (record sP { mint = mP }) (record stP { nodes = NP }) (record sI { mint = mI }) (record stI { nodes = NI })
    S′ = record
      { π = (nodeCt sP , xs) ∷ π
      ; π-keys = apart (below-keys (proj₁ pairs-below)) ∷ π-keys
      ; π-vals = ++⁺ ux π-vals (λ (v∈xs , v∈π) → <⇒≱ (all-lookup (below-vals (proj₂ pairs-below)) v∈π) (all-lookup ax v∈xs))
      ; pairs-below = kP ∷ weak (<⇒≤ kP) (proj₁ pairs-below)
                    , ab ∷ weak₂ kI (proj₂ pairs-below)
      ; sources = sources ; numbers = numbers ; distinct = distinct ; sync = sync
      ; rows = M.regM o rows ; dlv-alike = M.spentM o rows dlv-alike ; dying-alike = M.spentM o rows dying-alike
      ; latches = latches ; bounded = weak {f = λ x → x} sP≤ (proj₁ bounded) , weak {f = λ x → x} sI≤ (proj₂ bounded) ; swept = swept ; uncut = uncut ; rids = rids
      ; fresh-ids = weak rP≤ (proj₁ fresh-ids) , weak rI≤ (proj₂ fresh-ids) ; above = above
      ; census = census ; owned = owned
      ; ruleP = sub-rule (λ r∈ → r∈) (<⇒≤ kP) ruleP ; ruleI = sub-rule (λ r∈ → r∈) kI ruleI
      ; scripts = scripts }
