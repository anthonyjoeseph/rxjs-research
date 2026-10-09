------------------------------------------------------------------
-- A CUT ON BOTH SIDES.  A switch's cut drops every registration
-- through its running inner, the plain run's through one node and the
-- impl's through the node `π` pairs it with.  The two drop the rows the
-- registries' relation pairs, because a related path names a paired
-- node exactly when its partner names the node's pair: every plain
-- node a path names is a key of `π` whose run of impl nodes the
-- partner names, and every impl node is its key's or `Unpaired`.
------------------------------------------------------------------
module Simulation.Cut where

open import Data.Bool    using (true; false; T; _∨_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Fin     using (Fin; toℕ; _↑ˡ_; _↑ʳ_)
open import Data.Vec     using (lookup)
open import Data.Maybe   using (just)
open import Data.List    using (List; []; _∷_; _++_; map; concatMap; take)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Binary.Pointwise using (Pointwise) renaming ([] to []ᵖ)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (lookup to lookupᵃ; tabulate to tabulateᵃ; map to mapᵃ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to ++⁺ᵃ)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat     using (ℕ; suc; _<_; _≡ᵇ_)
open import Rx.Mint      using (counter; regᵏ)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; 1+n≢0; <⇒≢; <-≤-trans; ≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Data.Bool.ListAction using (any)
open import Rx.Exp       using (Ctx; Ty; Closed; Val)
open import Rx.Evaluator using (NodeId; RegRow; LiveSource; Sched; EvalSt; switchKill; regSource; sameSource; cutThrough; Path; root; share-sink; _↠[_]_; frameNodes; pathHasNode; thru-outer; mergeAllᵒ; lookupNode; cell-st)
open import Rx.Evaluator.Reducible.Support using (∨-Tˡ; ∨-Tʳ; sub-rule; cut-sub)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ)
open import Simulation.Stores using (Named; PathRel; root~; sink~; map~; scan~; takeWhile~; spentWhile~; outerElem~; outerExplode~; inner~;
  deferInner~; srcCount; Census; aboveᵇ; above-≤; guardOf; RegRel; []; _∷_; mach; Partners; partner-row; partner-mem; ArrRows; Spent; spent-subst; Store; Arr; InputBlock; ᵇ-no; block; RowRel; read~; cold~; defer~; MachRow; hot~; sharedEq; hotEq;
  live-mono; skip-cancel)
open import Simulation.Grow using (mem-any)
open import Simulation.Sweep using (T-true; t≢f; count-hit; count-pass; same-eq; raw≢stamped; raw<ₙ; sweepL; sweep-eq; sweepL-pw; all-sweep;
  unique-sweep; sync-sweep; regrel-sweep; rows-guards; part-sweep; arr-sweep; spent-sweep)
open import Simulation.After using (module Kept; PairedR)
open import Simulation.Write using (key-same; vals-same; ∈-vals)

-- the nodes a path names, frame by frame
nodesOf : ∀ {m} {Δ : Ctx m} {lo s u} → Path Δ lo s u → List NodeId
nodesOf root             = []
nodesOf (share-sink _ _) = []
nodesOf (f ↠[ _ ] p)     = frameNodes f ++ nodesOf p

any-mem : ∀ {k} xs → T (any (_≡ᵇ k) xs) → k ∈ xs
any-mem {k} (x ∷ xs) h with x ≡ᵇ k in e
... | true  = here (sym (≡ᵇ⇒≡ x k (subst T (sym e) tt)))
... | false = there (any-mem xs h)

has-node : ∀ {m} {Δ : Ctx m} {lo s u k} (p : Path Δ lo s u) → T (pathHasNode k p) → k ∈ nodesOf p
has-node root             ()
has-node (share-sink _ _) ()
has-node {k = k} (f ↠[ _ ] p) h with any (_≡ᵇ k) (frameNodes f) in e
... | true  = ∈-++⁺ˡ (any-mem (frameNodes f) (subst T (sym e) tt))
... | false = ∈-++⁺ʳ (frameNodes f) (has-node p h)

node-has : ∀ {m} {Δ : Ctx m} {lo s u k} (p : Path Δ lo s u) → k ∈ nodesOf p → T (pathHasNode k p)
node-has root             ()
node-has (share-sink _ _) ()
node-has (f ↠[ _ ] p) m with ∈-++⁻ (frameNodes f) m
... | inj₁ a = ∨-Tˡ (mem-any a)
... | inj₂ b = ∨-Tʳ (node-has p b)

T-≡ : ∀ {a b} → (T a → T b) → (T b → T a) → a ≡ b
T-≡ {true}  {true}  _ _ = refl
T-≡ {true}  {false} f _ = ⊥-elim (f tt)
T-≡ {false} {true}  _ g = ⊥-elim (g tt)
T-≡ {false} {false} _ _ = refl

-- two paths name two nodes alike when each naming gives the other
cut-by : ∀ {m m′} {Δ : Ctx m} {Δ′ : Ctx m′} {lo lo′ a b w w′ k k′} (p : Path Δ lo a w) (q : Path Δ′ lo′ b w′)
       → (k ∈ nodesOf p → k′ ∈ nodesOf q) → (k′ ∈ nodesOf q → k ∈ nodesOf p) → pathHasNode k p ≡ pathHasNode k′ q
cut-by p q f g = T-≡ (λ h → node-has q (f (has-node p h))) (λ h → node-has p (g (has-node q h)))

-- a share's subject names nothing, however its type is rewritten
no-sink : ∀ {m} {Δ : Ctx m} {lo b w} {i : Fin m} {h x} (e : lookup Δ i ≡ b)
        → x ∈ nodesOf (subst (λ u → Path Δ lo u w) e (share-sink i h)) → ⊥
no-sink refl ()

------------------------------------------------------------------
-- The cut as a filter
------------------------------------------------------------------

∨-falseˡ : ∀ {a b} → a ∨ b ≡ false → a ≡ false
∨-falseˡ {false} _ = refl
∨-falseˡ {true}  ()

∨-falseʳ : ∀ {a b} → a ∨ b ≡ false → b ≡ false
∨-falseʳ {false} e = e
∨-falseʳ {true}  ()

-- an id among neither list is among neither joined
none-++ : ∀ {k} xs {ys} → any (_≡ᵇ k) xs ≡ false → any (_≡ᵇ k) ys ≡ false → any (_≡ᵇ k) (xs ++ ys) ≡ false
none-++         []       _ f = f
none-++ {k} (x ∷ xs) h f = cong₂ _∨_ (∨-falseˡ h) (none-++ xs (∨-falseʳ {x ≡ᵇ k} h) f)

-- and one among either is among both joined
hit-++ : ∀ {k} xs {ys} → any (_≡ᵇ k) ys ≡ true → any (_≡ᵇ k) (xs ++ ys) ≡ true
hit-++         []       h = h
hit-++ {k} (x ∷ xs) h = trans (cong ((x ≡ᵇ k) ∨_) (hit-++ xs h)) (∨-zeroʳ _)

hit-in : ∀ {k xs} ys → k ∈ xs → any (_≡ᵇ k) (xs ++ ys) ≡ true
hit-in {k} {_ ∷ xs} ys (here refl) = cong (_∨ any (_≡ᵇ k) (xs ++ ys)) (T-true (≡⇒≡ᵇ k k refl))
hit-in {k} {x ∷ xs} ys (there m)   = trans (cong ((x ≡ᵇ k) ∨_) (hit-in ys m)) (∨-zeroʳ _)

module _ {m} {Δ : Ctx m} {t} (c : NodeId) where

  -- ONE ROW OF THE CUT: through the node, gone and its id named; else kept
  CutStep : RegRow Δ t → List (RegRow Δ t) → Set
  CutStep r K =
      (pathHasNode c (proj₂ (proj₂ (proj₂ r))) ≡ true
       × proj₁ (cutThrough c (r ∷ K)) ≡ proj₁ (cutThrough c K)
       × proj₂ (cutThrough c (r ∷ K)) ≡ proj₁ r ∷ proj₂ (cutThrough c K))
    ⊎ (pathHasNode c (proj₂ (proj₂ (proj₂ r))) ≡ false
       × proj₁ (cutThrough c (r ∷ K)) ≡ r ∷ proj₁ (cutThrough c K)
       × proj₂ (cutThrough c (r ∷ K)) ≡ proj₂ (cutThrough c K))

  cut-step : ∀ r K → CutStep r K
  cut-step (rid , rs , x) K with pathHasNode c (proj₂ x) | cutThrough c K
  ... | true  | _ , _ = inj₁ (refl , refl , refl)
  ... | false | _ , _ = inj₂ (refl , refl , refl)

  all-cut : ∀ {P : RegRow Δ t → Set} {K} → All P K → All P (proj₁ (cutThrough c K))
  all-cut                 []       = []
  all-cut {P = P} {r ∷ K} (p ∷ ps) with cut-step r K
  ... | inj₁ (_ , e , _) = subst (All P) (sym e) (all-cut ps)
  ... | inj₂ (_ , e , _) = subst (All P) (sym e) (p ∷ all-cut ps)

  pairs-cut : ∀ {R : RegRow Δ t → RegRow Δ t → Set} {K} → AllPairs R K → AllPairs R (proj₁ (cutThrough c K))
  pairs-cut                 []       = []
  pairs-cut {R = R} {r ∷ K} (p ∷ ps) with cut-step r K
  ... | inj₁ (_ , e , _) = subst (AllPairs R) (sym e) (pairs-cut ps)
  ... | inj₂ (_ , e , _) = subst (AllPairs R) (sym e) (all-cut p ∷ pairs-cut ps)

  -- every id the cut names is a row's
  named-cut : ∀ {P : ℕ → Set} {K : List (RegRow Δ t)} → All (λ r → P (proj₁ r)) K → All P (proj₂ (cutThrough c K))
  named-cut                 []       = []
  named-cut {P = P} {r ∷ K} (p ∷ ps) with cut-step r K
  ... | inj₁ (_ , _ , e) = subst (All P) (sym e) (p ∷ named-cut ps)
  ... | inj₂ (_ , _ , e) = subst (All P) (sym e) (named-cut ps)

  -- WHAT THE CUT NAMES IS A ROW'S, so below the counter the rows' ids are
  cut-named-st : ∀ {e : Closed Δ t} {f} {sched : Sched Δ} {st : EvalSt e} {g}
               → All (λ r → proj₁ r < counter (Sched.mint sched) regᵏ) (EvalSt.registry st) → Named f sched st
               → Named f (record sched { live = sweepL g (Sched.live sched) })
                         (record st { registry = proj₁ (cutThrough c (EvalSt.registry st))
                                    ; cancelled = proj₂ (cutThrough c (EvalSt.registry st)) ++ EvalSt.cancelled st })
  cut-named-st {g = g} ids N = record
    { slots-below = Named.slots-below N ; ords-below = all-sweep g LiveSource.ordinal (Named.ords-below N)
    ; srcs-below = all-cut (Named.srcs-below N) ; cut-below = ++⁺ᵃ (named-cut ids) (Named.cut-below N)
    ; dlv-below = Named.dlv-below N ; dying-below = Named.dying-below N }

  -- a kept row was there and is not through the node
  kept-in : ∀ {r} K → r ∈ proj₁ (cutThrough c K) → r ∈ K × pathHasNode c (proj₂ (proj₂ (proj₂ r))) ≡ false
  kept-in []      ()
  kept-in (k ∷ K) m with cut-step k K
  ... | inj₁ (_ , e , _) = there (proj₁ (kept-in K (subst (_ ∈_) e m))) , proj₂ (kept-in K (subst (_ ∈_) e m))
  ... | inj₂ (h , e , _) with subst (_ ∈_) e m
  ...   | here refl = here refl , h
  ...   | there m′  = there (proj₁ (kept-in K m′)) , proj₂ (kept-in K m′)

  -- a row through the node has its id named
  cut-named : ∀ {r} K → r ∈ K → pathHasNode c (proj₂ (proj₂ (proj₂ r))) ≡ true → proj₁ r ∈ proj₂ (cutThrough c K)
  cut-named (k ∷ K) (here refl) h with cut-step k K
  ... | inj₁ (_ , _ , e)  = subst (proj₁ k ∈_) (sym e) (here refl)
  ... | inj₂ (h′ , _ , _) = ⊥-elim (t≢f (trans (sym h) h′))
  cut-named {r} (k ∷ K) (there m) h with cut-step k K
  ... | inj₁ (_ , _ , e) = subst (proj₁ r ∈_) (sym e) (there (cut-named K m h))
  ... | inj₂ (_ , _ , e) = subst (proj₁ r ∈_) (sym e) (cut-named K m h)

  -- an id apart from every row's is not named
  ids-apart : ∀ {k} K → All (λ r → k ≢ proj₁ r) K → any (_≡ᵇ k) (proj₂ (cutThrough c K)) ≡ false
  ids-apart          []      []       = refl
  ids-apart {k} (r ∷ K) (ne ∷ a) with cut-step r K
  ... | inj₁ (_ , _ , e) = subst (λ L → any (_≡ᵇ k) L ≡ false) (sym e)
                             (cong₂ _∨_ (ᵇ-no (λ x → ne (sym x))) (ids-apart K a))
  ... | inj₂ (_ , _ , e) = subst (λ L → any (_≡ᵇ k) L ≡ false) (sym e) (ids-apart K a)

  -- so, ids apart, a kept row's id is not named
  kept-apart : ∀ {x} K → AllPairs (λ r r′ → proj₁ r ≢ proj₁ r′) K → x ∈ K → pathHasNode c (proj₂ (proj₂ (proj₂ x))) ≡ false
             → any (_≡ᵇ proj₁ x) (proj₂ (cutThrough c K)) ≡ false
  kept-apart (k ∷ K) (a ∷ ps) (here refl) h with cut-step k K
  ... | inj₁ (h′ , _)      = ⊥-elim (t≢f (trans (sym h′) h))
  ... | inj₂ (_ , _ , e) = subst (λ L → any (_≡ᵇ proj₁ k) L ≡ false) (sym e) (ids-apart K a)
  kept-apart {x} (k ∷ K) (a ∷ ps) (there m) h with cut-step k K
  ... | inj₁ (_ , _ , e) = subst (λ L → any (_≡ᵇ proj₁ x) L ≡ false) (sym e)
                             (cong₂ _∨_ (ᵇ-no (lookupᵃ a m)) (kept-apart K ps m h))
  ... | inj₂ (_ , _ , e) = subst (λ L → any (_≡ᵇ proj₁ x) L ≡ false) (sym e) (kept-apart K ps m h)

  -- a cut never raises a count, and leaves one alone where it takes no row at its source
  count-cut-zero : ∀ k (K : List (RegRow Δ t)) → srcCount k K ≡ 0 → srcCount k (proj₁ (cutThrough c K)) ≡ 0
  count-cut-zero k []      z = refl
  count-cut-zero k (r ∷ K) z = go (cut-step r K) (sameSource k (regSource (proj₁ (proj₂ r)))) refl
    where
    go : CutStep r K → ∀ b → sameSource k (regSource (proj₁ (proj₂ r))) ≡ b → srcCount k (proj₁ (cutThrough c (r ∷ K))) ≡ 0
    go _                  true  s = ⊥-elim (1+n≢0 (trans (sym (count-hit k r K s)) z))
    go (inj₁ (_ , e , _)) false s = trans (cong (srcCount k) e) (count-cut-zero k K (trans (sym (count-pass k r K s)) z))
    go (inj₂ (_ , e , _)) false s = trans (cong (srcCount k) e)
                                      (trans (count-pass k r (proj₁ (cutThrough c K)) s) (count-cut-zero k K (trans (sym (count-pass k r K s)) z)))

  count-cut-keep : ∀ k (K : List (RegRow Δ t))
                 → All (λ r → sameSource k (regSource (proj₁ (proj₂ r))) ≡ true → pathHasNode c (proj₂ (proj₂ (proj₂ r))) ≡ false) K
                 → srcCount k (proj₁ (cutThrough c K)) ≡ srcCount k K
  count-cut-keep k []      _        = refl
  count-cut-keep k (r ∷ K) (a ∷ as) = go (cut-step r K) (sameSource k (regSource (proj₁ (proj₂ r)))) refl
    where
    go : CutStep r K → ∀ b → sameSource k (regSource (proj₁ (proj₂ r))) ≡ b → srcCount k (proj₁ (cutThrough c (r ∷ K))) ≡ srcCount k (r ∷ K)
    go (inj₁ (h , _))     true  s = ⊥-elim (t≢f (trans (sym h) (a s)))
    go (inj₁ (_ , e , _)) false s = trans (cong (srcCount k) e) (trans (count-cut-keep k K as) (sym (count-pass k r K s)))
    go (inj₂ (_ , e , _)) true  s = trans (cong (srcCount k) e)
                                      (trans (count-hit k r (proj₁ (cutThrough c K)) s) (trans (cong suc (count-cut-keep k K as)) (sym (count-hit k r K s))))
    go (inj₂ (_ , e , _)) false s = trans (cong (srcCount k) e)
                                      (trans (count-pass k r (proj₁ (cutThrough c K)) s) (trans (count-cut-keep k K as) (sym (count-pass k r K s))))


  -- a kept row's id is among neither the cut's nor those cancelled before
  uncut-cut : ∀ {K CS} → AllPairs (λ r r′ → proj₁ r ≢ proj₁ r′) K → All (λ r → any (_≡ᵇ proj₁ r) CS ≡ false) K
            → ∀ {r} → r ∈ proj₁ (cutThrough c K) → any (_≡ᵇ proj₁ r) (proj₂ (cutThrough c K) ++ CS) ≡ false
  uncut-cut {K} ps us m =
    none-++ (proj₂ (cutThrough c K)) (kept-apart K ps (proj₁ (kept-in K m)) (proj₂ (kept-in K m))) (lookupᵃ us (proj₁ (kept-in K m)))

  -- a slot's census stands where the cut takes no row at its raw slot
  census-cut : ∀ {raw stamped conn done} (K : List (RegRow Δ t)) → Census raw stamped K conn done
             → All (λ r → sameSource raw (regSource (proj₁ (proj₂ r))) ≡ true → pathHasNode c (proj₂ (proj₂ (proj₂ r))) ≡ false) K
             → Census raw stamped (proj₁ (cutThrough c K)) conn done
  census-cut {raw} K (inj₁ (one , cn)) safe = inj₁ (trans (count-cut-keep raw K safe) one , cn)
  census-cut {raw} {stamped} K (inj₂ (z₁ , z₂ , f)) _ = inj₂ (count-cut-zero raw K z₁ , count-cut-zero stamped K z₂ , f)

------------------------------------------------------------------
-- The cut on both sides
------------------------------------------------------------------

-- WHAT AN IMPL NODE OF A KEY'S RUN SAYS ABOUT THE ROWS: whatever names it
-- names the key, since every impl node is its key's or `Unpaired`; and
-- given the converse, `fwd`, a related pair of rows is cut alike
module Back {n} {Γ : Ctx n} (κ : Kinds n) {π : List (NodeId × List NodeId)}
         (keys : Unique (map proj₁ π)) (vals : Unique (concatMap proj₂ π)) {c : NodeId} {cs} (ce : (c , cs) ∈ π)
         {c′ : NodeId} (cm : c′ ∈ cs) where

  -- an entry naming the cut's impl node is the cut's
  owner : ∀ {k xs} → (k , xs) ∈ π → c′ ∈ xs → c ≡ k
  owner e m = cong proj₁ (vals-same vals ce e cm m)

  -- and no impl-only node is it
  off : ∀ {k} → (k ∈ concatMap proj₂ π → ⊥) → c′ ≡ k → ⊥
  off un refl = un (∈-vals ce cm)

  module _ {t : Ty} {NP NI} where

    bwd : ∀ {lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
        → PathRel κ π NP NI p q → c′ ∈ nodesOf q → c ∈ nodesOf p
    bwd root~                            ()
    bwd (sink~ {lo′ = lo′} {i = i} {h′ = h′} sh) m = ⊥-elim (no-sink {Δ = plainᵏ Γ κ} {lo = lo′} {w = emitᵗ t} {i = n ↑ʳ i} {h = h′} (sharedEq {Γ = Γ} κ i sh) m)
    bwd (map~ _ r)                       m                      = bwd r m
    bwd (scan~ e _ _ _ _ r)              (here eq)              = here (owner e (here eq))
    bwd (scan~ e _ _ _ _ r)              (there m)              = there (bwd r m)
    bwd (takeWhile~ e _ _ _ _ r)         (here eq)              = here (owner e (here eq))
    bwd (takeWhile~ e _ _ _ _ r)         (there (here eq))      = here (owner e (there (here eq)))
    bwd (takeWhile~ e _ _ _ _ r)         (there (there m))      = there (bwd r m)
    bwd (spentWhile~ e _ _ r)            (here eq)              = here (owner e (here eq))
    bwd (spentWhile~ e _ _ r)            (there (here eq))      = here (owner e (there (here eq)))
    bwd (spentWhile~ e _ _ r)            (there (there m))      = there (bwd r m)
    bwd (outerElem~ (pm , _) r)          (here eq)              = here (owner pm (here eq))
    bwd (outerElem~ (pm , _) r)          (there (here eq))      = here (owner pm (there (here eq)))
    bwd (outerElem~ (pm , _) r)          (there (there m))      = there (bwd r m)
    bwd (outerExplode~ (pm , _) _ r)     (here eq)              = here (owner pm (there (there (here eq))))
    bwd (outerExplode~ (pm , _) _ r)     (there (here eq))      = here (owner pm (here eq))
    bwd (outerExplode~ (pm , _) _ r)     (there (there (here eq))) = here (owner pm (there (here eq)))
    bwd (outerExplode~ (pm , _) _ r)     (there (there (there m))) = there (bwd r m)
    bwd (inner~ _ (pm , _) ip r)         (here eq)              = here (owner pm (here eq))
    bwd (inner~ _ (pm , _) ip r)         (there (here eq))      = there (here (owner ip (here eq)))
    bwd (inner~ _ (pm , _) ip r)         (there (there (here eq))) = here (owner pm (there (here eq)))
    bwd (inner~ _ (pm , _) ip r)         (there (there (there m))) = there (there (bwd r m))
    bwd (deferInner~ e₁ e₂ _ _ _ _ _ r)    (here eq)              = there (here (owner e₂ (there (here eq))))
    bwd (deferInner~ e₁ e₂ _ _ _ _ _ r)    (there (here eq))      = there (here (owner e₂ (there (there (here eq)))))
    bwd (deferInner~ e₁ e₂ _ _ _ _ _ r)    (there (there (here eq))) = here (owner e₁ (here eq))
    bwd (deferInner~ e₁ e₂ _ _ _ _ _ r)    (there (there (there (here eq)))) = there (here (owner e₂ (here eq)))
    bwd (deferInner~ e₁ e₂ _ _ _ _ _ r)    (there (there (there (there m)))) = there (there (bwd r m))

    -- an input block names nothing `π` pairs, so its tail names what the whole does
    block-in : ∀ {a lo ℓ} {full : Path (plainᵏ Γ κ) lo a (emitᵗ t)} {q}
             → InputBlock κ π NP NI a {lo} {ℓ} full q → c′ ∈ nodesOf full → c′ ∈ nodesOf q
    block-in (block _ _ _ _ u₁ _ _ _) (here eq)                         = ⊥-elim (off u₁ eq)
    block-in (block _ _ _ _ _ uj _ _) (there (here eq))                 = ⊥-elim (off uj eq)
    block-in (block _ _ _ _ _ _ ub _) (there (there (here eq)))         = ⊥-elim (off ub eq)
    block-in (block _ _ _ _ _ _ _ u₂) (there (there (there (here eq)))) = ⊥-elim (off u₂ eq)
    block-in (block _ _ _ _ _ _ _ _)  (there (there (there (there m)))) = m

    block-out : ∀ {a lo ℓ} {full : Path (plainᵏ Γ κ) lo a (emitᵗ t)} {q}
              → InputBlock κ π NP NI a {lo} {ℓ} full q → c′ ∈ nodesOf q → c′ ∈ nodesOf full
    block-out (block _ _ _ _ _ _ _ _) m = there (there (there (there m)))

    module _ {LP : List (LiveSource Γ)} {LI : List (LiveSource (plainᵏ Γ κ))} where

      -- and the impl's own rows are never cut
      mach-cut : ∀ {x′} → MachRow κ π {t} NP NI LP LI x′ → pathHasNode c′ (proj₂ (proj₂ (proj₂ x′))) ≡ false
      mach-cut (hot~ {i = i} {ℓ = ℓ} hot {h = h′} {full = full} b refl) =
        T-≡ (λ h → ⊥-elim (no-sink {Δ = plainᵏ Γ κ} {lo = ℓ} {w = emitᵗ t} {i = n ↑ʳ i} {h = h′} (hotEq {Γ = Γ} κ i hot) (block-in b (has-node full h)))) (λ ())

  module Rows {t : Ty} {NP NI}
              (fwd : ∀ {lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
                   → PathRel κ π NP NI p q → c ∈ nodesOf p → c′ ∈ nodesOf q)
              (one : ∀ {k k′} → (k , k′ ∷ []) ∈ π → c ≡ k → c′ ≡ k′) where

    path-cut : ∀ {lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
             → PathRel κ π NP NI p q → pathHasNode c p ≡ pathHasNode c′ q
    path-cut {p = p} {q} r = cut-by p q (fwd r) (bwd r)

    module _ {LP : List (LiveSource Γ)} {LI : List (LiveSource (plainᵏ Γ κ))} where

      -- the rows the relation pairs are cut together
      row-cut : ∀ {x x′} → RowRel κ π {t} NP NI LP LI x x′
              → pathHasNode c (proj₂ (proj₂ (proj₂ x))) ≡ pathHasNode c′ (proj₂ (proj₂ (proj₂ x′)))
      row-cut (read~ _ r refl)          = path-cut r
      row-cut (cold~ {p = p} {full = full} _ b r refl) = cut-by p full (λ m → block-out b (fwd r m)) (λ m → bwd r (block-in b m))
      row-cut (defer~ {nid = nid} {nid′ = nid′} {h = h} {h′ = h′} {p = p} {q = q} _ e _ _ r refl) =
        cut-by (thru-outer mergeAllᵒ nid ↠[ h ] p) (thru-outer mergeAllᵒ nid′ ↠[ h′ ] q) d-fwd d-bwd
        where
          d-fwd : c ∈ nid ∷ nodesOf p → c′ ∈ nid′ ∷ nodesOf q
          d-fwd (here eq) = here (one e eq)
          d-fwd (there m) = there (fwd r m)
          d-bwd : c′ ∈ nid′ ∷ nodesOf q → c ∈ nid ∷ nodesOf p
          d-bwd (here eq) = here (owner e (here eq))
          d-bwd (there m) = there (bwd r m)

      RR : List (RegRow Γ t) → List (RegRow (plainᵏ Γ κ) (emitᵗ t)) → Set
      RR = RegRel κ π {t} NP NI LP LI

      part-subst : ∀ {rs rs′ ks ks′} (e : rs ≡ ks) (e′ : rs′ ≡ ks′) (q : RR rs rs′) {x x′}
                 → Partners κ π NP NI LP LI q x x′ → Partners κ π NP NI LP LI (subst₂ RR e e′ q) x x′
      part-subst refl refl q p = p

      arr-subst : ∀ {rs rs′ ks ks′} (e : rs ≡ ks) (e′ : rs′ ≡ ks′) (q : RR rs rs′) {s s′ u u′}
                → ArrRows κ π NP NI LP LI q s s′ u u′ → ArrRows κ π NP NI LP LI (subst₂ RR e e′ q) s s′ u u′
      arr-subst refl refl q a = a

      -- an arrival's pair against a row and its tail, against the tail alone, and the row put back
      arr-tail : ∀ {r r′ rs rs′} (rr : RowRel κ π {t} NP NI LP LI r r′) (q : RR rs rs′) {s s′ u u′}
               → ArrRows κ π NP NI LP LI (rr ∷ q) s s′ u u′ → ArrRows κ π NP NI LP LI q s s′ u u′
      arr-tail (read~ _ _ _)        q a       = a
      arr-tail (cold~ _ _ _ _)      q (_ , a) = a
      arr-tail (defer~ _ _ _ _ _ _) q (_ , a) = a

      arr-cons : ∀ {r r′ rs rs′ ks ks′} (rr : RowRel κ π {t} NP NI LP LI r r′) (q : RR rs rs′) (q′ : RR ks ks′) {s s′ u u′}
               → ArrRows κ π NP NI LP LI (rr ∷ q) s s′ u u′ → ArrRows κ π NP NI LP LI q′ s s′ u u′
               → ArrRows κ π NP NI LP LI (rr ∷ q′) s s′ u u′
      arr-cons (read~ _ _ _)        q q′ _       a = a
      arr-cons (cold~ _ _ _ _)      q q′ (x , _) a = x , a
      arr-cons (defer~ _ _ _ _ _ _) q q′ (x , _) a = x , a

      -- THE ROWS THE CUT KEEPS ARE RELATED, partnered as before and
      -- against an arrival's pair as before
      CutRows : ∀ {rs rs′} → RR rs rs′ → Set
      CutRows {rs} {rs′} q = Σ (RR (proj₁ (cutThrough c rs)) (proj₁ (cutThrough c′ rs′))) λ q′
        → (∀ {x x′} → Partners κ π NP NI LP LI q x x′ → pathHasNode c (proj₂ (proj₂ (proj₂ x))) ≡ false
                    → Partners κ π NP NI LP LI q′ x x′)
        × (∀ {s s′ u u′} → ArrRows κ π NP NI LP LI q s s′ u u′ → ArrRows κ π NP NI LP LI q′ s s′ u u′)
        × (∀ {dP dI} → Spent κ π NP NI LP LI q dP dI → Spent κ π NP NI LP LI q′ dP dI)

      cut-rows : ∀ {rs rs′} (q : RR rs rs′) → CutRows q
      cut-rows [] = [] , (λ ()) , (λ _ → tt) , (λ d → d)
      cut-rows (_∷_ {r = r} {r′ = r′} {rs = rs} {rs′ = rs′} rr q) with cut-rows q | cut-step c r rs | cut-step c′ r′ rs′
      ... | q′ , P , A , D | inj₁ (h , e , _) | inj₁ (_ , e′ , _) =
            subst₂ RR (sym e) (sym e′) q′
          , (λ { (inj₁ (refl , refl)) hx → ⊥-elim (t≢f (trans (sym h) hx))
               ; (inj₂ p) hx → part-subst (sym e) (sym e′) q′ (P p hx) })
          , (λ a → arr-subst (sym e) (sym e′) q′ (A (arr-tail rr q a)))
          , (λ d → spent-subst κ π NP NI LP LI (sym e) (sym e′) q′ (D (proj₂ d)))
      ... | q′ , P , A , D | inj₂ (_ , e , _) | inj₂ (_ , e′ , _) =
            subst₂ RR (sym e) (sym e′) (rr ∷ q′)
          , (λ { (inj₁ eq) _ → part-subst (sym e) (sym e′) (rr ∷ q′) (inj₁ eq)
               ; (inj₂ p) hx → part-subst (sym e) (sym e′) (rr ∷ q′) (inj₂ (P p hx)) })
          , (λ a → arr-subst (sym e) (sym e′) (rr ∷ q′) (arr-cons rr q q′ a (A (arr-tail rr q a))))
          , (λ d → spent-subst κ π NP NI LP LI (sym e) (sym e′) (rr ∷ q′) (proj₁ d , D (proj₂ d)))
      ... | _ | inj₁ (h , _) | inj₂ (h′ , _) = ⊥-elim (t≢f (trans (sym h) (trans (row-cut rr) h′)))
      ... | _ | inj₂ (h , _) | inj₁ (h′ , _) = ⊥-elim (t≢f (trans (sym h′) (trans (sym (row-cut rr)) h)))
      cut-rows (mach {rs = rs} {r′ = r′} {rs′ = rs′} m q) with cut-rows q | cut-step c′ r′ rs′
      ... | q′ , P , A , D | inj₂ (_ , e′ , _) =
            subst₂ RR refl (sym e′) (mach m q′)
          , (λ p hx → part-subst refl (sym e′) (mach m q′) (P p hx))
          , (λ a → arr-subst refl (sym e′) (mach m q′) (A a))
          , (λ d → spent-subst κ π NP NI LP LI refl (sym e′) (mach m q′) (D d))
      ... | _ | inj₁ (h , _) = ⊥-elim (t≢f (trans (sym h) (mach-cut m)))

      -- no row at a raw slot is through the impl's cut: a reader is at its
      -- stamped slot, a minted source above every slot, and the impl's own
      -- rows are never cut
      raw-safe : ∀ (i : Fin n) {rs rs′} → RR rs rs′ → All (λ r → aboveᵇ (proj₁ (proj₂ r)) ≡ true) rs′
               → All (λ r → sameSource (toℕ (i ↑ˡ n)) (regSource (proj₁ (proj₂ r))) ≡ true
                          → pathHasNode c′ (proj₂ (proj₂ (proj₂ r))) ≡ false) rs′
      raw-safe i []                          []       = []
      raw-safe i (read~ {i = j} _ _ _ ∷ q)   (_ ∷ as) = (λ e → ⊥-elim (raw≢stamped i j (same-eq e))) ∷ raw-safe i q as
      raw-safe i (cold~ _ _ _ _ ∷ q)         (a ∷ as) = (λ e → ⊥-elim (<⇒≢ (<-≤-trans (raw<ₙ i) (above-≤ a)) (same-eq e))) ∷ raw-safe i q as
      raw-safe i (defer~ _ _ _ _ _ _ ∷ q)    (a ∷ as) = (λ e → ⊥-elim (<⇒≢ (<-≤-trans (raw<ₙ i) (above-≤ a)) (same-eq e))) ∷ raw-safe i q as
      raw-safe i (mach m q)                  (_ ∷ as) = (λ _ → mach-cut m) ∷ raw-safe i q as

-- THE IMPL'S CUT IS AT ONE OF THE FIRST TWO MEMBERS OF THE RUN `π`
-- PAIRS THE PLAIN CUT'S NODE WITH, the two every path naming the key
-- names: a switch's run is its one node, a count's cut is its second
module At {n} {Γ : Ctx n} (κ : Kinds n) {π : List (NodeId × List NodeId)}
         (keys : Unique (map proj₁ π)) (vals : Unique (concatMap proj₂ π)) {c : NodeId} {cs} (ce : (c , cs) ∈ π)
         {c′ : NodeId} (cm : c′ ∈ take 2 cs) where

  front : ∀ {x : NodeId} (xs : List NodeId) → x ∈ take 2 xs → x ∈ xs
  front (_ ∷ _)     (here eq)          = here eq
  front (_ ∷ _ ∷ _) (there (here eq))  = there (here eq)
  front (_ ∷ [])    (there ())
  front (_ ∷ _ ∷ _) (there (there ()))

  -- the cut's key's run holds the cut's impl node up front
  hit : ∀ {k xs} → (k , xs) ∈ π → k ≡ c → c′ ∈ take 2 xs
  hit e refl = subst (λ ys → c′ ∈ take 2 ys) (sym (key-same keys e ce)) cm

  -- the two up front, where a frame order other than the run's names them
  gap : ∀ {a b x ys} → c′ ∈ a ∷ b ∷ [] → c′ ∈ a ∷ x ∷ b ∷ ys
  gap (here eq)         = here eq
  gap (there (here eq)) = there (there (here eq))
  gap (there (there ()))

  hop : ∀ {x₀ x₁ x₂ y ys} → c′ ∈ x₀ ∷ x₁ ∷ [] → c′ ∈ x₁ ∷ x₂ ∷ y ∷ x₀ ∷ ys
  hop (here eq)         = there (there (there (here eq)))
  hop (there (here eq)) = here eq
  hop (there (there ()))

  module B = Back {Γ = Γ} κ keys vals ce (front cs cm)
  open B public

  module _ {t : Ty} {NP NI} where

    -- a related path names the cut's node exactly when its partner names the pair
    fwd : ∀ {lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
        → PathRel κ π NP NI p q → c ∈ nodesOf p → c′ ∈ nodesOf q
    fwd root~                            ()
    fwd (sink~ _)                        ()
    fwd (map~ _ r)                       m                      = fwd r m
    fwd (scan~ e _ _ _ _ r)              (here eq)              = ∈-++⁺ˡ (hit e (sym eq))
    fwd (scan~ e _ _ _ _ r)              (there m)              = there (fwd r m)
    fwd (takeWhile~ e _ _ _ _ r)         (here eq)              = ∈-++⁺ˡ (hit e (sym eq))
    fwd (takeWhile~ e _ _ _ _ r)         (there m)              = there (there (fwd r m))
    fwd (spentWhile~ e _ _ r)            (here eq)              = ∈-++⁺ˡ (hit e (sym eq))
    fwd (spentWhile~ e _ _ r)            (there m)              = there (there (fwd r m))
    fwd (outerElem~ (pm , _) r)          (here eq)              = ∈-++⁺ˡ (hit pm (sym eq))
    fwd (outerElem~ (pm , _) r)          (there m)              = there (there (fwd r m))
    fwd (outerExplode~ (pm , _) _ r)     (here eq)              = there (∈-++⁺ˡ (hit pm (sym eq)))
    fwd (outerExplode~ (pm , _) _ r)     (there m)              = there (there (there (fwd r m)))
    fwd (inner~ _ (pm , _) ip r)         (here eq)              = gap (hit pm (sym eq))
    fwd (inner~ _ (pm , _) ip r)         (there (here eq))      = there (∈-++⁺ˡ (hit ip (sym eq)))
    fwd (inner~ _ (pm , _) ip r)         (there (there m))      = there (there (there (fwd r m)))
    fwd (deferInner~ e₁ e₂ _ _ _ _ _ r)    (here eq)              = there (there (∈-++⁺ˡ (hit e₁ (sym eq))))
    fwd (deferInner~ e₁ e₂ _ _ _ _ _ r)    (there (here eq))      = hop (hit e₂ (sym eq))
    fwd (deferInner~ e₁ e₂ _ _ _ _ _ r)    (there (there m))      = there (there (there (there (fwd r m))))

  one : ∀ {k k′} → (k , k′ ∷ []) ∈ π → c ≡ k → c′ ≡ k′
  one e eq with hit e (sym eq)
  ... | here x = x
  ... | there ()

  module _ {t : Ty} {NP NI} where
    module R = B.Rows {t} {NP} {NI} (fwd {t} {NP} {NI}) one
    open R public

-- A DEFERRED BODY'S RUN AT ITS THIRD MEMBER, the hop's marker merge's
-- inner.  A run that long is a deferred body's or an exploding
-- flattener's, and the second member tells them apart: the marker merge
-- is a merge where a flattener's restamp is a cell
module Third {n} {Γ : Ctx n} (κ : Kinds n) {π : List (NodeId × List NodeId)}
         (keys : Unique (map proj₁ π)) (vals : Unique (concatMap proj₂ π)) {c x y c′ : NodeId}
         (ce : (c , x ∷ y ∷ c′ ∷ []) ∈ π) where

  module B = Back {Γ = Γ} κ keys vals ce (there (there (here refl)))
  open B public

  same : ∀ {k xs} → (k , xs) ∈ π → c ≡ k → xs ≡ x ∷ y ∷ c′ ∷ []
  same e refl = key-same keys e ce

  len1 : ∀ {a : NodeId} → _≢_ {A = List NodeId} (a ∷ []) (x ∷ y ∷ c′ ∷ [])
  len1 ()

  len2 : ∀ {a b : NodeId} → _≢_ {A = List NodeId} (a ∷ b ∷ []) (x ∷ y ∷ c′ ∷ [])
  len2 ()

  -- the run's key is no inner's
  unkeyed : ∀ {k k′} → (k , k′ ∷ []) ∈ π → c ≢ k
  unkeyed e eq = len1 (same e eq)

  hop₃ : ∀ {a b d : NodeId} {ys} → _≡_ {A = List NodeId} (a ∷ b ∷ d ∷ []) (x ∷ y ∷ c′ ∷ []) → c′ ∈ b ∷ d ∷ ys
  hop₃ refl = there (here refl)

  module _ {t : Ty} {NP NI} (ly : ∀ {w} {v : Val (plainᵏ Γ κ) w} → lookupNode y NI ≢ just (cell-st v)) where

    -- no flattener is keyed at the run's key
    flat-off : ∀ {m m′ ks xs w} {v : Val (plainᵏ Γ κ) w} → (m , m′ ∷ ks ∷ xs) ∈ π → lookupNode ks NI ≡ just (cell-st v) → c ≡ m → ⊥
    flat-off pm lk eq with same pm eq
    ... | refl = ly lk

    fwd₃ : ∀ {lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
         → PathRel κ π NP NI p q → c ∈ nodesOf p → c′ ∈ nodesOf q
    fwd₃ root~                            ()
    fwd₃ (sink~ _)                        ()
    fwd₃ (map~ _ r)                       m                 = fwd₃ r m
    fwd₃ (scan~ e _ _ _ _ r)              (here eq)         = ⊥-elim (len1 (same e eq))
    fwd₃ (scan~ e _ _ _ _ r)              (there m)         = there (fwd₃ r m)
    fwd₃ (takeWhile~ e _ _ _ _ r)         (here eq)         = ⊥-elim (len2 (same e eq))
    fwd₃ (takeWhile~ e _ _ _ _ r)         (there m)         = there (there (fwd₃ r m))
    fwd₃ (spentWhile~ e _ _ r)            (here eq)         = ⊥-elim (len2 (same e eq))
    fwd₃ (spentWhile~ e _ _ r)            (there m)         = there (there (fwd₃ r m))
    fwd₃ (outerElem~ (pm , _ , _ , _ , _ , _ , _ , lk) r)    (here eq) = ⊥-elim (flat-off pm lk eq)
    fwd₃ (outerElem~ _ r)                 (there m)         = there (there (fwd₃ r m))
    fwd₃ (outerExplode~ (pm , _ , _ , _ , _ , _ , _ , lk) _ r) (here eq) = ⊥-elim (flat-off pm lk eq)
    fwd₃ (outerExplode~ _ _ r)            (there m)         = there (there (there (fwd₃ r m)))
    fwd₃ (inner~ _ (pm , _ , _ , _ , _ , _ , _ , lk) ip r)   (here eq) = ⊥-elim (flat-off pm lk eq)
    fwd₃ (inner~ _ _ ip r)                (there (here eq)) = ⊥-elim (len1 (same ip eq))
    fwd₃ (inner~ _ _ ip r)                (there (there m)) = there (there (there (fwd₃ r m)))
    fwd₃ (deferInner~ e₁ e₂ _ _ _ _ _ r)    (here eq)         = ⊥-elim (len1 (same e₁ eq))
    fwd₃ (deferInner~ e₁ e₂ _ _ _ _ _ r)    (there (here eq)) = hop₃ (same e₂ eq)
    fwd₃ (deferInner~ e₁ e₂ _ _ _ _ _ r)    (there (there m)) = there (there (there (there (fwd₃ r m))))

    module R = B.Rows {t} {NP} {NI} fwd₃ (λ {k} {k′} e eq → ⊥-elim (unkeyed {k} {k′} e eq))
    open R public

------------------------------------------------------------------
-- The stores after the cut
------------------------------------------------------------------

module _ {n} {Γ : Ctx n} (κ : Kinds n) {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

  open Kept {Γ = Γ} κ {t} {ep} {ei}

  module _ {sP stP sI stI} (S : St sP stP sI stI) {c cs} (ce : (c , cs) ∈ Store.π S) {c′} (cm : c′ ∈ take 2 cs) where

    open Store S
    module C = At {Γ = Γ} κ π-keys π-vals ce cm

    KP : List (RegRow Γ t)
    KP = proj₁ (cutThrough c (EvalSt.registry stP))

    KI : List (RegRow (plainᵏ Γ κ) (emitᵗ t))
    KI = proj₁ (cutThrough c′ (EvalSt.registry stI))

    cr : C.CutRows rows
    cr = C.cut-rows rows

    G : Pointwise (λ l l′ → guardOf KP l ≡ guardOf KI l′) (Sched.live sP) (Sched.live sI)
    G = rows-guards κ (proj₁ cr) (proj₁ distinct) (proj₂ distinct) numbers

    -- THE STORES ONCE BOTH RUNS CUT AND SWEEP
    cut-go : St (record sP { live = sweepL (guardOf KP) (Sched.live sP) })
                (record stP { registry = KP ; cancelled = proj₂ (cutThrough c (EvalSt.registry stP)) ++ EvalSt.cancelled stP })
                (record sI { live = sweepL (guardOf KI) (Sched.live sI) })
                (record stI { registry = KI ; cancelled = proj₂ (cutThrough c′ (EvalSt.registry stI)) ++ EvalSt.cancelled stI })
    cut-go = record
      { π = π ; π-keys = π-keys ; π-vals = π-vals ; pairs-below = pairs-below
      ; sources = sweepL-pw sources G
      ; numbers = sweepL-pw numbers G
      ; distinct = unique-sweep _ LiveSource.source (proj₁ distinct) , unique-sweep _ LiveSource.source (proj₂ distinct)
      ; sync = sync-sweep sync G
      ; rows = regrel-sweep κ {K = KP} {K′ = KI} G (λ m → m) (proj₁ cr)
      ; dlv-alike = spent-sweep κ {K = KP} {K′ = KI} G (λ m → m) (proj₁ cr) (proj₂ (proj₂ (proj₂ cr)) dlv-alike)
      ; dying-alike = spent-sweep κ {K = KP} {K′ = KI} G (λ m → m) (proj₁ cr) (proj₂ (proj₂ (proj₂ cr)) dying-alike)
      ; latches = latches ; dying-done = dying-done
      ; bounded = all-sweep _ LiveSource.source (proj₁ bounded) , all-sweep _ LiveSource.source (proj₂ bounded)
      ; swept = sweepL-pw G G
      ; uncut = tabulateᵃ (uncut-cut c (proj₁ rids) (proj₁ uncut)) , tabulateᵃ (uncut-cut c′ (proj₂ rids) (proj₂ uncut))
      ; named = cut-named-st c (proj₁ fresh-ids) (proj₁ named) , cut-named-st c′ (proj₂ fresh-ids) (proj₂ named)
      ; rids = pairs-cut c (proj₁ rids) , pairs-cut c′ (proj₂ rids)
      ; fresh-ids = all-cut c (proj₁ fresh-ids) , all-cut c′ (proj₂ fresh-ids)
      ; above = all-cut c (proj₁ above) , all-cut c′ (proj₂ above)
      ; census = λ i h → census-cut c′ (EvalSt.registry stI) (census i h) (C.raw-safe i rows (proj₂ above))
      ; owned = all-cut c′ (mapᵃ (λ f u {j} b → all-cut c′ (f u {j} b)) owned)
      ; ruleP = sub-rule (λ {r} m → cut-sub c (EvalSt.registry stP) r m) ≤-refl ruleP
      ; ruleI = sub-rule (λ {r} m → cut-sub c′ (EvalSt.registry stI) r m) ≤-refl ruleI
      ; scripts = scripts
      ; live-outer = live-mono {st = stI} {st′ = record stI { registry = KI ; cancelled = proj₂ (cutThrough c′ (EvalSt.registry stI)) ++ EvalSt.cancelled stI }}
          (λ {r} m → cut-sub c′ (EvalSt.registry stI) r m) (skip-cancel (proj₂ (cutThrough c′ (EvalSt.registry stI))) {stI}) (λ l → l) live-outer
      }

    -- a pair through the cut leaves on both sides, any other stays partnered
    cut-keeps : Keeps S cut-go
    cut-keeps (inj₁ (a , b)) =
      inj₁ (hit-++ (proj₂ (cutThrough c (EvalSt.registry stP))) a , hit-++ (proj₂ (cutThrough c′ (EvalSt.registry stI))) b)
    cut-keeps {x} {x′} (inj₂ (a , b , pr)) = go (pathHasNode c (proj₂ (proj₂ (proj₂ x)))) refl
      where
        mx = partner-mem κ _ _ _ _ _ rows pr
        rr = partner-row κ _ _ _ _ _ rows pr
        go : ∀ v → pathHasNode c (proj₂ (proj₂ (proj₂ x))) ≡ v
           → PairedR (Store.rows cut-go) (proj₂ (cutThrough c (EvalSt.registry stP)) ++ EvalSt.cancelled stP)
                                         (proj₂ (cutThrough c′ (EvalSt.registry stI)) ++ EvalSt.cancelled stI) x x′
        go true  h = inj₁ ( hit-in (EvalSt.cancelled stP) (cut-named c _ (proj₁ mx) h)
                          , hit-in (EvalSt.cancelled stI) (cut-named c′ _ (proj₂ mx) (trans (sym (C.row-cut rr)) h)) )
        go false h = inj₂ ( none-++ (proj₂ (cutThrough c (EvalSt.registry stP))) (kept-apart c _ (proj₁ rids) (proj₁ mx) h) a
                          , none-++ (proj₂ (cutThrough c′ (EvalSt.registry stI)))
                                    (kept-apart c′ _ (proj₂ rids) (proj₂ mx) (trans (sym (C.row-cut rr)) h)) b
                          , part-sweep κ {K = KP} {K′ = KI} G (λ m → m) (proj₁ cr) (proj₁ (proj₂ cr) pr h) )

    cut-persists : Persists S cut-go
    cut-persists ar = record
      { boundP = Arr.boundP ar ; boundI = Arr.boundI ar
      ; rows = arr-sweep κ {K = KP} {K′ = KI} G (λ m → m) (proj₁ cr) (proj₁ (proj₂ (proj₂ cr)) (Arr.rows ar))
      ; lists = sweepL-pw (Arr.lists ar) G
      }

    -- A SWITCH'S CUT ON BOTH SIDES, as the evaluator writes it: the
    -- pairing is kept as it was
    cut-kill : Σ (After S ([] , switchKill (just c) sP stP) ([] , switchKill (just c′) sI stI))
                 (λ A → Store.π (After.store A) ≡ π)
    cut-kill =
      subst₂ (λ x y → Σ (After S ([] , x , proj₂ (switchKill (just c) sP stP)) ([] , y , proj₂ (switchKill (just c′) sI stI)))
                        (λ A → Store.π (After.store A) ≡ π))
        (cong (λ L → record sP { live = L }) (sym (sweep-eq KP (Sched.live sP))))
        (cong (λ L → record sI { live = L }) (sym (sweep-eq KI (Sched.live sI))))
        (after cut-go cut-keeps cut-persists []ᵖ (λ x → x) , refl)
