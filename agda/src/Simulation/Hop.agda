------------------------------------------------------------------
-- A HOP REGISTERED ON BOTH SIDES, over stores whose merge pair is
-- already installed and paired: each run mints the hop's source,
-- ordinal and registration, conses the pending source onto its live
-- list and registers the path through the merge.
--
-- THE SOURCE IS ABOVE EVERYTHING EITHER STORE NAMES, so every field
-- that compares a source, an ordinal or an id against what is already
-- there reads the new one as apart from all of it: `Store.named`
-- bounds every source, ordinal and id a run has handed out by its
-- counter.  The two registrations go through or are spent alike,
-- since a related pair of paths reads its tests at the same budget,
-- and the new impl row threads only `π`'s nodes, which no input block
-- owns.
------------------------------------------------------------------
module Simulation.Hop where

open import Data.Bool    using (Bool; true; false; T; _∨_; if_then_else_)
open import Data.Bool.Properties using (∨-identityʳ; ∨-assoc; ∨-zeroʳ)
open import Data.Bool.ListAction using (any)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Fin     using (Fin; _↑ʳ_)
open import Data.Vec     using (lookup)
open import Data.List    using (List; []; _∷_; _++_; map; concatMap)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise) renaming ([] to []ᵖ; _∷_ to _∷ᵖ_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᵃ; lookup to lookupᵃ; tabulate to tabulateᵃ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to ++⁺ᵃ)
open import Data.List.Relation.Unary.AllPairs using () renaming ([] to []ᴾ; _∷_ to _∷ᴾ_)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (++⁺ to ++⁺ᴾ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe   using (nothing)
open import Data.Nat     using (ℕ; suc; _+_; _<_; _≤_; s≤s; _≡ᵇ_; _<ᵇ_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; n≤1+n; n<1+n; m<n⇒m<1+n; <⇒≢; <-irrefl; <⇒≤; ≤⇒≤ᵇ; <-trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit    using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Rx.Exp       using (Ctx; Closed)
open import Rx.Mint      using (counter; setAt; nodeᵏ; sourceᵏ; ordinalᵏ; regᵏ; freshId)
open import Rx.Evaluator using (Sched; EvalSt; LiveSource; RegRow; regSource; sameSource; memberSource; Path; share-sink;
                                atDyn; atSlot; thru-outer; mergeAllᵒ; AllOp; _↠[_]_; register; installNode; mergeAll-st; echoᵗ; spentOn; spentAt; pathHasNode)
open import Rx.Evaluator.Freshness using (nodeCt; lookup-set)
open import Rx.Evaluator.Reducible.Support using (Sound; Rule; register-sound; sub-ot; ∨-T; node-eq)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ)
open import Simulation.Schedules using (ord) renaming (_∷_ to _∷ˢ_)
open import Simulation.Stores using (Store; Arr; PathRel; DeferRel; Named; Census; srcCount; guardOf; Unpaired; InputBlock; block;
                                     RowRel; read~; cold~; defer~; hot~; RegRel; Src; []; _∷_; mach; Partners; Spent; ArrRows;
                                     root~; sink~; map~; scan~; takeWhile~; spentWhile~; outerElem~; outerExplode~; inner~; deferInner~;
                                     sharedEq; blockNodes; ᵇ-no; hop; dyn~)
  renaming (here to sp-here; there to sp-there)
open import Simulation.Sweep using (sameSource-lt; sameSource-no; same-refl; lt-false; count-pass; T-true; raw<ₙ; stamped<)
open import Simulation.Cut   using (nodesOf; has-node; no-sink)
open import Simulation.Write using (∈-vals)
open import Simulation.After using (module Kept; apart)

------------------------------------------------------------------
-- Counters
------------------------------------------------------------------

-- nothing below a counter is it
none-below : ∀ {k} {xs : List ℕ} → All (_< k) xs → any (_≡ᵇ k) xs ≡ false
none-below []ᵃ        = refl
none-below (lt ∷ᵃ as) = cong₂ _∨_ (ᵇ-no (<⇒≢ lt)) (none-below as)

member-below : ∀ {k} {xs : List ℕ} → All (_< k) xs → memberSource k xs ≡ false
member-below []ᵃ        = refl
member-below (lt ∷ᵃ as) = cong₂ _∨_ (sameSource-lt lt) (member-below as)

any-snoc : ∀ {A : Set} (p : A → Bool) xs y → any p (xs ++ y ∷ []) ≡ any p xs ∨ p y
any-snoc p []       y = ∨-identityʳ (p y)
any-snoc p (x ∷ xs) y = trans (cong (p x ∨_) (any-snoc p xs y)) (sym (∨-assoc (p x) (any p xs) (p y)))

-- each source a live list holds, ranked against one minted above them all
ranked-top : ∀ {n m} {Γ : Ctx n} {Γ′ : Ctx m} {R : LiveSource Γ → LiveSource Γ′ → Set} {o o′ LP LI}
           → Pointwise R LP LI → All (_< o) (map LiveSource.ordinal LP) → All (_< o′) (map LiveSource.ordinal LI)
           → Pointwise (λ x x′ → (o <ᵇ ord x) ≡ (o′ <ᵇ ord x′)) LP LI
ranked-top []ᵖ       _          _            = []ᵖ
ranked-top (_ ∷ᵖ ps) (a ∷ᵃ as) (a′ ∷ᵃ as′) = trans (lt-false a) (sym (lt-false a′)) ∷ᵖ ranked-top ps as as′

------------------------------------------------------------------
-- A row at a new source, appended
------------------------------------------------------------------

module _ {m} {Δ : Ctx m} {t} where

  -- a row at another source leaves a count alone
  count-snoc : ∀ k (K : List (RegRow Δ t)) r → sameSource k (regSource (proj₁ (proj₂ r))) ≡ false
             → srcCount k (K ++ r ∷ []) ≡ srcCount k K
  count-snoc k []                 r e = count-pass k r [] e
  count-snoc k ((_ , s , _) ∷ K) r e = cong (λ c → if sameSource k (regSource s) then suc c else c) (count-snoc k K r e)

  census-snoc : ∀ {raw stamped} {K : List (RegRow Δ t)} {c d} r
              → sameSource raw (regSource (proj₁ (proj₂ r))) ≡ false → sameSource stamped (regSource (proj₁ (proj₂ r))) ≡ false
              → Census raw stamped K c d → Census raw stamped (K ++ r ∷ []) c d
  census-snoc {raw} {stamped} {K} r e e′ (inj₁ (o , cn))     = inj₁ (trans (count-snoc raw K r e) o , cn)
  census-snoc {raw} {stamped} {K} r e e′ (inj₂ (z , z′ , f)) = inj₂ (trans (count-snoc raw K r e) z , trans (count-snoc stamped K r e′) z′ , f)

module _ {n} {Γ : Ctx n} {t} where

  -- no row at a source above every row's
  none-src : ∀ {s} {K : List (RegRow Γ t)} → All (λ r → regSource (proj₁ (proj₂ r)) < s) K
           → any (λ p → sameSource s (regSource (proj₁ (proj₂ p)))) K ≡ false
  none-src []ᵃ       = refl
  none-src (lt ∷ᵃ a) = cong₂ _∨_ (sameSource-lt lt) (none-src a)

  -- a source above the slots and every row is swept
  guard-none : ∀ (K : List (RegRow Γ t)) (l : LiveSource Γ) → n < LiveSource.source l
             → All (λ r → regSource (proj₁ (proj₂ r)) < LiveSource.source l) K → guardOf K l ≡ false
  guard-none K l lt a = cong₂ _∨_ (lt-false lt) (none-src a)

  -- a row appended at a source keeps it, and leaves every other alone
  guard-new : ∀ (K : List (RegRow Γ t)) r (l : LiveSource Γ) → sameSource (LiveSource.source l) (regSource (proj₁ (proj₂ r))) ≡ true
            → guardOf (K ++ r ∷ []) l ≡ true
  guard-new K r l e =
    trans (cong ((LiveSource.source l <ᵇ n) ∨_)
                (trans (any-snoc (λ p → sameSource (LiveSource.source l) (regSource (proj₁ (proj₂ p)))) K r)
                       (trans (cong (any (λ p → sameSource (LiveSource.source l) (regSource (proj₁ (proj₂ p)))) K ∨_) e) (∨-zeroʳ _))))
          (∨-zeroʳ _)

  guard-snoc : ∀ (K : List (RegRow Γ t)) r (l : LiveSource Γ) → sameSource (LiveSource.source l) (regSource (proj₁ (proj₂ r))) ≡ false
             → guardOf (K ++ r ∷ []) l ≡ guardOf K l
  guard-snoc K r l e =
    cong ((LiveSource.source l <ᵇ n) ∨_)
         (trans (any-snoc (λ p → sameSource (LiveSource.source l) (regSource (proj₁ (proj₂ p)))) K r)
                (trans (cong (any (λ p → sameSource (LiveSource.source l) (regSource (proj₁ (proj₂ p)))) K ∨_) e) (∨-identityʳ _)))

swept-snoc : ∀ {n m} {Γ : Ctx n} {Γ′ : Ctx m} {t t′} {K : List (RegRow Γ t)} {K′ : List (RegRow Γ′ t′)} {r r′} {LP LI}
           → Pointwise (λ l l′ → guardOf K l ≡ guardOf K′ l′) LP LI
           → All (_< regSource (proj₁ (proj₂ r))) (map LiveSource.source LP)
           → All (_< regSource (proj₁ (proj₂ r′))) (map LiveSource.source LI)
           → Pointwise (λ l l′ → guardOf (K ++ r ∷ []) l ≡ guardOf (K′ ++ r′ ∷ []) l′) LP LI
swept-snoc []ᵖ _ _ = []ᵖ
swept-snoc {K = K} {K′} {r} {r′} (_∷ᵖ_ {l} {l′} g gs) (b ∷ᵃ bs) (b′ ∷ᵃ bs′) =
  trans (guard-snoc K r l (sameSource-no (<⇒≢ b))) (trans g (sym (guard-snoc K′ r′ l′ (sameSource-no (<⇒≢ b′)))))
  ∷ᵖ swept-snoc {K = K} {K′} {r} {r′} gs bs bs′

-- a share's subject is never spent, however its type is rewritten
sink-spent : ∀ {m} {Δ : Ctx m} {lo b w} {i : Fin m} {h} {ns} (e : lookup Δ i ≡ b)
           → spentOn (subst (λ u → Path Δ lo u w) e (share-sink i h)) ns ≡ false
sink-spent refl = refl

-- the outer frame at a fresh node: on the path, or the node just handed out
thru-cls : ∀ {m} {Δ : Ctx m} {t ℓ u lo} (op : AllOp) (nid : ℕ) (le : lo ≤ ℓ) (p : Path Δ ℓ u t) k
         → T (pathHasNode k (thru-outer op nid ↠[ le ] p)) → T (pathHasNode k p) ⊎ (nid ≤ k × k < suc nid)
thru-cls op nid le p k h =
  [ (λ a → inj₂ (≤-reflexive (node-eq a) , s≤s (≤-reflexive (sym (node-eq a))))) , inj₁ ]′ (∨-T h)

------------------------------------------------------------------
-- The relation under a new live pair, and a new row pair
------------------------------------------------------------------

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  row-cons : ∀ {t π NP NI LP LI l l′ r r′} → RowRel {Γ = Γ} κ π {t} NP NI LP LI r r′ → RowRel {Γ = Γ} κ π NP NI (l ∷ LP) (l′ ∷ LI) r r′
  row-cons (read~ k pr eq)            = read~ k pr eq
  row-cons (cold~ sp ib pr eq)        = cold~ (sp-there sp) ib pr eq
  row-cons (defer~ sp pm lP lI pr eq) = defer~ (sp-there sp) pm lP lI pr eq

  reg-cons : ∀ {t π NP NI LP LI l l′ rs rs′} → RegRel {Γ = Γ} κ π {t} NP NI LP LI rs rs′ → RegRel {Γ = Γ} κ π NP NI (l ∷ LP) (l′ ∷ LI) rs rs′
  reg-cons []                      = []
  reg-cons (r ∷ q)                 = row-cons r ∷ reg-cons q
  reg-cons (mach (hot~ h ib eq) q) = mach (hot~ h ib eq) (reg-cons q)

  part-cons : ∀ {t π NP NI LP LI l l′ rs rs′} (q : RegRel {Γ = Γ} κ π {t} NP NI LP LI rs rs′) {x x′}
            → Partners {Γ = Γ} κ π NP NI LP LI q x x′ → Partners {Γ = Γ} κ π NP NI (l ∷ LP) (l′ ∷ LI) (reg-cons q) x x′
  part-cons []                      ()
  part-cons (r ∷ q)                 (inj₁ e) = inj₁ e
  part-cons (r ∷ q)                 (inj₂ p) = inj₂ (part-cons q p)
  part-cons (mach (hot~ h ib eq) q) p        = part-cons q p

  spent-cons : ∀ {t π NP NI LP LI l l′ rs rs′} (q : RegRel {Γ = Γ} κ π {t} NP NI LP LI rs rs′) {dP dI}
             → Spent {Γ = Γ} κ π NP NI LP LI q dP dI → Spent {Γ = Γ} κ π NP NI (l ∷ LP) (l′ ∷ LI) (reg-cons q) dP dI
  spent-cons []                      s       = s
  spent-cons (r ∷ q)                 (e , s) = e , spent-cons q s
  spent-cons (mach (hot~ h ib eq) q) s       = spent-cons q s

  arr-cons : ∀ {t π NP NI LP LI l l′ rs rs′} (q : RegRel {Γ = Γ} κ π {t} NP NI LP LI rs rs′) {s s′ u u′}
           → ArrRows {Γ = Γ} κ π NP NI LP LI q s s′ u u′ → ArrRows {Γ = Γ} κ π NP NI (l ∷ LP) (l′ ∷ LI) (reg-cons q) s s′ u u′
  arr-cons []                         a       = a
  arr-cons (read~ _ _ _ ∷ q)          a       = arr-cons q a
  arr-cons (cold~ _ _ _ _ ∷ q)        (x , a) = x , arr-cons q a
  arr-cons (defer~ _ _ _ _ _ _ ∷ q)   (x , a) = x , arr-cons q a
  arr-cons (mach (hot~ h ib eq) q)    a       = arr-cons q a

  reg-snoc : ∀ {t π NP NI LP LI rs rs′ x x′} → RegRel {Γ = Γ} κ π {t} NP NI LP LI rs rs′ → RowRel {Γ = Γ} κ π NP NI LP LI x x′
           → RegRel {Γ = Γ} κ π NP NI LP LI (rs ++ x ∷ []) (rs′ ++ x′ ∷ [])
  reg-snoc []         r = r ∷ []
  reg-snoc (r₀ ∷ q)   r = r₀ ∷ reg-snoc q r
  reg-snoc (mach m q) r = mach m (reg-snoc q r)

  part-snoc : ∀ {t π NP NI LP LI rs rs′ x x′} (q : RegRel {Γ = Γ} κ π {t} NP NI LP LI rs rs′) (r : RowRel {Γ = Γ} κ π NP NI LP LI x x′) {y y′}
            → Partners {Γ = Γ} κ π NP NI LP LI q y y′ → Partners {Γ = Γ} κ π NP NI LP LI (reg-snoc q r) y y′
  part-snoc []         r ()
  part-snoc (r₀ ∷ q)   r (inj₁ e) = inj₁ e
  part-snoc (r₀ ∷ q)   r (inj₂ p) = inj₂ (part-snoc q r p)
  part-snoc (mach m q) r p        = part-snoc q r p

  spent-snoc : ∀ {t π NP NI LP LI rs rs′ x x′} (q : RegRel {Γ = Γ} κ π {t} NP NI LP LI rs rs′) (r : RowRel {Γ = Γ} κ π NP NI LP LI x x′) {dP dI}
             → Spent {Γ = Γ} κ π NP NI LP LI q dP dI → dP x ≡ dI x′ → Spent {Γ = Γ} κ π NP NI LP LI (reg-snoc q r) dP dI
  spent-snoc []         r _        e = e , _
  spent-snoc (r₀ ∷ q)   r (d , ds) e = d , spent-snoc q r ds e
  spent-snoc (mach m q) r ds       e = spent-snoc q r ds e

  arr-snoc : ∀ {t π NP NI LP LI rs rs′ x x′} (q : RegRel {Γ = Γ} κ π {t} NP NI LP LI rs rs′) (r : RowRel {Γ = Γ} κ π NP NI LP LI x x′) {s s′ u u′}
           → ArrRows {Γ = Γ} κ π NP NI LP LI q s s′ u u′ → ArrRows {Γ = Γ} κ π NP NI LP LI (r ∷ []) s s′ u u′
           → ArrRows {Γ = Γ} κ π NP NI LP LI (reg-snoc q r) s s′ u u′
  arr-snoc []                       r _       b = b
  arr-snoc (read~ _ _ _ ∷ q)        r a       b = arr-snoc q r a b
  arr-snoc (cold~ _ _ _ _ ∷ q)      r (x , a) b = x , arr-snoc q r a b
  arr-snoc (defer~ _ _ _ _ _ _ ∷ q) r (x , a) b = x , arr-snoc q r a b
  arr-snoc (mach _ q)               r a       b = arr-snoc q r a b

  -- an input block's nodes are none of `π`'s
  ib-unp : ∀ {t π NP NI a lo ℓ} {full : Path (plainᵏ Γ κ) lo a (emitᵗ t)} {q}
         → InputBlock {Γ = Γ} κ π {t} NP NI a {lo} {ℓ} full q → ∀ {j} → j ∈ blockNodes full → Unpaired {Γ = Γ} κ π j
  ib-unp (block _ _ _ _ u₁ _ _ _) (here refl)                         = u₁
  ib-unp (block _ _ _ _ _ uj _ _) (there (here refl))                 = uj
  ib-unp (block _ _ _ _ _ _ ub _) (there (there (here refl)))         = ub
  ib-unp (block _ _ _ _ _ _ _ u₂) (there (there (there (here refl)))) = u₂
  ib-unp (block _ _ _ _ _ _ _ _)  (there (there (there (there ()))))

  -- so is every node an impl row's block names
  reg-unp : ∀ {t π NP NI LP LI rs rs′} → RegRel {Γ = Γ} κ π {t} NP NI LP LI rs rs′
          → ∀ {r′} → r′ ∈ rs′ → (∀ (k : Fin n) → proj₁ (proj₂ r′) ≡ atSlot (n ↑ʳ k) → ⊥)
          → ∀ {j} → j ∈ blockNodes (proj₂ (proj₂ (proj₂ r′))) → Unpaired {Γ = Γ} κ π j
  reg-unp (read~ {i = i} _ _ _ ∷ q)   (here refl) ns m  = ⊥-elim (ns i refl)
  reg-unp (cold~ _ ib _ refl ∷ q)     (here refl) ns m  = ib-unp ib m
  reg-unp (defer~ _ _ _ _ _ refl ∷ q) (here refl) ns ()
  reg-unp (_ ∷ q)                     (there r∈)  ns m  = reg-unp q r∈ ns m
  reg-unp (mach (hot~ _ ib refl) q)   (here refl) ns m  = ib-unp ib m
  reg-unp (mach _ q)                  (there r∈)  ns m  = reg-unp q r∈ ns m

  -- every node a related impl path names is one of `π`'s
  rel-vals : ∀ {t π NP NI lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
           → PathRel {Γ = Γ} κ π {t} NP NI p q → ∀ {j} → j ∈ nodesOf q → j ∈ concatMap proj₂ π
  rel-vals root~ ()
  rel-vals {t = t} (sink~ {lo′ = lo′} {i = i} {h′ = h′} sh) m =
    ⊥-elim (no-sink {Δ = plainᵏ Γ κ} {lo = lo′} {w = emitᵗ t} {i = n ↑ʳ i} {h = h′} (sharedEq {Γ = Γ} κ i sh) m)
  rel-vals (map~ _ r)                         m                                 = rel-vals r m
  rel-vals (scan~ e _ _ _ _ r)                (here refl)                       = ∈-vals e (here refl)
  rel-vals (scan~ e _ _ _ _ r)                (there m)                         = rel-vals r m
  rel-vals (takeWhile~ e _ _ _ _ r)           (here refl)                       = ∈-vals e (here refl)
  rel-vals (takeWhile~ e _ _ _ _ r)           (there (here refl))               = ∈-vals e (there (here refl))
  rel-vals (takeWhile~ e _ _ _ _ r)           (there (there m))                 = rel-vals r m
  rel-vals (spentWhile~ e _ _ r)              (here refl)                       = ∈-vals e (here refl)
  rel-vals (spentWhile~ e _ _ r)              (there (here refl))               = ∈-vals e (there (here refl))
  rel-vals (spentWhile~ e _ _ r)              (there (there m))                 = rel-vals r m
  rel-vals (outerElem~ (pm , _) r)            (here refl)                       = ∈-vals pm (here refl)
  rel-vals (outerElem~ (pm , _) r)            (there (here refl))               = ∈-vals pm (there (here refl))
  rel-vals (outerElem~ (pm , _) r)            (there (there m))                 = rel-vals r m
  rel-vals (outerExplode~ (pm , _) _ r)       (here refl)                       = ∈-vals pm (there (there (here refl)))
  rel-vals (outerExplode~ (pm , _) _ r)       (there (here refl))               = ∈-vals pm (here refl)
  rel-vals (outerExplode~ (pm , _) _ r)       (there (there (here refl)))       = ∈-vals pm (there (here refl))
  rel-vals (outerExplode~ (pm , _) _ r)       (there (there (there m)))         = rel-vals r m
  rel-vals (inner~ _ (pm , _) ip r)           (here refl)                       = ∈-vals pm (here refl)
  rel-vals (inner~ _ (pm , _) ip r)           (there (here refl))               = ∈-vals ip (here refl)
  rel-vals (inner~ _ (pm , _) ip r)           (there (there (here refl)))       = ∈-vals pm (there (here refl))
  rel-vals (inner~ _ (pm , _) ip r)           (there (there (there m)))         = rel-vals r m
  rel-vals (deferInner~ e₁ e₂ _ _ _ _ _ r)    (here refl)                       = ∈-vals e₂ (there (here refl))
  rel-vals (deferInner~ e₁ e₂ _ _ _ _ _ r)    (there (here refl))               = ∈-vals e₂ (there (there (here refl)))
  rel-vals (deferInner~ e₁ e₂ _ _ _ _ _ r)    (there (there (here refl)))       = ∈-vals e₁ (here refl)
  rel-vals (deferInner~ e₁ e₂ _ _ _ _ _ r)    (there (there (there (here refl)))) = ∈-vals e₂ (here refl)
  rel-vals (deferInner~ e₁ e₂ _ _ _ _ _ r)    (there (there (there (there m)))) = rel-vals r m

  -- A RELATED PAIR OF PATHS IS SPENT ALIKE: each reads its tests at the
  -- same budget, one or zero on both sides
  path-spent : ∀ {t π NP NI lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
             → PathRel {Γ = Γ} κ π {t} NP NI p q → spentOn p NP ≡ spentOn q NI
  path-spent root~                             = refl
  path-spent {NI = NI} (sink~ {i = i} {h′ = h′} sh) = sym (sink-spent {h = h′} {ns = NI} (sharedEq {Γ = Γ} κ i sh))
  path-spent (map~ _ r)                        = path-spent r
  path-spent (scan~ _ _ _ _ _ r)               = path-spent r
  path-spent (takeWhile~ _ lk _ lk₂ _ r)       = cong₂ _∨_ (trans (cong spentAt lk) (sym (cong spentAt lk₂))) (path-spent r)
  path-spent (spentWhile~ _ lk lk₂ r)          = cong₂ _∨_ (trans (cong spentAt lk) (sym (cong spentAt lk₂))) (path-spent r)
  path-spent (outerElem~ _ r)                  = path-spent r
  path-spent (outerExplode~ _ _ r)             = path-spent r
  path-spent (inner~ _ _ _ r)                  = path-spent r
  path-spent (deferInner~ _ _ _ _ _ _ _ r)     = path-spent r

------------------------------------------------------------------
-- The hop
------------------------------------------------------------------

-- the counters move past what they handed out, and the new source's
-- row, if any, is the one at the old source counter
named-hop : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {f} {sched : Sched Δ} {st : EvalSt e} {v v′} {l : LiveSource Δ} {R}
          → Named f (record sched { mint = setAt nodeᵏ v′ (Sched.mint sched) }) st
          → LiveSource.ordinal l ≡ counter (Sched.mint sched) ordinalᵏ
          → All (λ r → regSource (proj₁ (proj₂ r)) < suc (counter (Sched.mint sched) sourceᵏ)) R
          → Named f (record sched { mint = setAt regᵏ (suc (counter (Sched.mint sched) regᵏ)) (setAt nodeᵏ v
                                             (setAt sourceᵏ (suc (counter (Sched.mint sched) sourceᵏ))
                                             (setAt ordinalᵏ (suc (counter (Sched.mint sched) ordinalᵏ)) (Sched.mint sched))))
                                  ; live = l ∷ Sched.live sched })
                    (record st { registry = R })
named-hop N o rs = record
  { slots-below = m<n⇒m<1+n (Named.slots-below N)
  ; ords-below  = subst (_< suc _) (sym o) (n<1+n _) ∷ᵃ mapᵃ m<n⇒m<1+n (Named.ords-below N)
  ; srcs-below  = rs
  ; cut-below   = mapᵃ m<n⇒m<1+n (Named.cut-below N)
  ; dlv-below   = mapᵃ m<n⇒m<1+n (Named.dlv-below N)
  ; dying-below = mapᵃ m<n⇒m<1+n (Named.dying-below N)
  }

module _ {n} {Γ : Ctx n} (κ : Kinds n) {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

  open Kept {Γ = Γ} κ {t} {ep} {ei}

  module Hop {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {u}
             {lo} {p : Path Γ lo u t} {q : Path (plainᵏ Γ κ) (n + lo) (emitᵗ u) (emitᵗ t)} {now x′ x}
             (S : St (record sP { mint = setAt nodeᵏ (suc (nodeCt sP)) (Sched.mint sP) })
                     (installNode (nodeCt sP) (mergeAll-st {t = u} nothing 0 [] false) stP)
                     (record sI { mint = setAt nodeᵏ (suc (nodeCt sI)) (Sched.mint sI) })
                     (installNode (nodeCt sI) (mergeAll-st {t = emitᵗ u} nothing 0 [] false) stI))
             (pm : (nodeCt sP , nodeCt sI ∷ []) ∈ Store.π S)
             (pr : PathRel {Γ = Γ} κ (Store.π S) (EvalSt.nodes (installNode (nodeCt sP) (mergeAll-st {t = u} nothing 0 [] false) stP))
                                         (EvalSt.nodes (installNode (nodeCt sI) (mergeAll-st {t = emitᵗ u} nothing 0 [] false) stI)) p q)
             (rel : DeferRel κ u x′ x) where

    open Store S

    nid = nodeCt sP ; src = freshId sourceᵏ (Sched.mint sP) ; ordP = freshId ordinalᵏ (Sched.mint sP) ; rid = freshId regᵏ (Sched.mint sP)
    nid′ = nodeCt sI ; src′ = freshId sourceᵏ (Sched.mint sI) ; ordI = freshId ordinalᵏ (Sched.mint sI) ; rid′ = freshId regᵏ (Sched.mint sI)

    stP₁ = installNode nid (mergeAll-st {t = u} nothing 0 [] false) stP
    stI₁ = installNode nid′ (mergeAll-st {t = emitᵗ u} nothing 0 [] false) stI

    lP : LiveSource Γ
    lP = record { source = src ; ordinal = ordP ; elemTy = echoᵗ u ; pending = (suc now , (inj₁ tt , inj₂ x)) ∷ [] }
    lI : LiveSource (plainᵏ Γ κ)
    lI = record { source = src′ ; ordinal = ordI ; elemTy = echoᵗ (emitᵗ u) ; pending = (suc now , (inj₁ tt , inj₂ x′)) ∷ [] }

    sP₂ = record sP { mint = setAt regᵏ (suc rid) (setAt nodeᵏ (suc nid) (setAt sourceᵏ (suc src) (setAt ordinalᵏ (suc ordP) (Sched.mint sP))))
                    ; live = lP ∷ Sched.live sP }
    sI₂ = record sI { mint = setAt regᵏ (suc rid′) (setAt nodeᵏ (suc nid′) (setAt sourceᵏ (suc src′) (setAt ordinalᵏ (suc ordI) (Sched.mint sI))))
                    ; live = lI ∷ Sched.live sI }

    rowP : RegRow Γ t
    rowP = rid , atDyn src lo , echoᵗ u , thru-outer mergeAllᵒ nid ↠[ ≤-refl ] p
    rowI : RegRow (plainᵏ Γ κ) (emitᵗ t)
    rowI = rid′ , atDyn src′ (n + lo) , echoᵗ (emitᵗ u) , thru-outer mergeAllᵒ nid′ ↠[ ≤-refl ] q

    KP = EvalSt.registry stP
    KI = EvalSt.registry stI

    stP₂ : List (RegRow Γ t) → EvalSt ep
    stP₂ R = record stP₁ { registry = R }
    stI₂ : List (RegRow (plainᵏ Γ κ) (emitᵗ t)) → EvalSt ei
    stI₂ R = record stI₁ { registry = R }

    bP : n < src
    bP = Named.slots-below (proj₁ named)
    bI : n + n < src′
    bI = Named.slots-below (proj₂ named)

    -- the pair as a live pair, and the hop's rows as the pair's
    new-src : Src {Γ = Γ} κ lP lI
    new-src = defer~ bP (hop rel ∷ᵖ []ᵖ)
    new-row : RowRel {Γ = Γ} κ π {t} (EvalSt.nodes stP₁) (EvalSt.nodes stI₁) (lP ∷ Sched.live sP) (lI ∷ Sched.live sI) rowP rowI
    new-row = defer~ sp-here pm (lookup-set nid (mergeAll-st {t = u} nothing 0 [] false) (EvalSt.nodes stP))
                                (lookup-set nid′ (mergeAll-st {t = emitᵗ u} nothing 0 [] false) (EvalSt.nodes stI)) pr refl

    -- the source counters only grew, and nothing the arrival names is new
    persist : (R : List (RegRow Γ t)) (R′ : List (RegRow (plainᵏ Γ κ) (emitᵗ t)))
              (S₂ : Store κ sP₂ (stP₂ R) sI₂ (stI₂ R′))
            → (∀ {s s′ w w′} → Arr S s s′ w w′ → ArrRows {Γ = Γ} κ (Store.π S₂) _ _ _ _ (Store.rows S₂) s s′ w w′)
            → Persists S S₂
    persist R R′ S₂ ar-rows ar = record
      { boundP = m<n⇒m<1+n (Arr.boundP ar) ; boundI = m<n⇒m<1+n (Arr.boundI ar)
      ; rows   = ar-rows ar
      ; lists  = ((λ e → ⊥-elim (<-irrefl (sym e) (Arr.boundP ar))) , (λ e′ → ⊥-elim (<-irrefl (sym e′) (Arr.boundI ar))))
                 ∷ᵖ Arr.lists ar }

    -- SPENT: the path through the merge already cut, so neither run
    -- registers it, and the pair is live with nothing to deliver to
    spent : Rule sP₂ (stP₂ KP) → Rule sI₂ (stI₂ KI)
          → Σ (After S ([] , sP₂ , stP₂ KP) ([] , sI₂ , stI₂ KI)) λ B → PathRel {Γ = Γ} κ (Store.π (After.store B)) (EvalSt.nodes stP₁) (EvalSt.nodes stI₁) p q
    spent rP rI =
      after S₂ (λ { (inj₁ c) → inj₁ c ; (inj₂ (a , b , pp)) → inj₂ (a , b , part-cons {Γ = Γ} κ rows pp) })
               (persist KP KI S₂ (λ ar → arr-cons {Γ = Γ} κ rows (Arr.rows ar))) []ᵖ (λ m → m)
      , pr
      where
      S₂ : Store κ sP₂ (stP₂ KP) sI₂ (stI₂ KI)
      S₂ = record
        { π = π ; π-keys = π-keys ; π-vals = π-vals ; pairs-below = pairs-below
        ; sources  = new-src ∷ᵖ sources
        ; numbers  = dyn~ bP bI ∷ᵖ numbers
        ; distinct = apart (proj₁ bounded) ∷ᴾ proj₁ distinct , apart (proj₂ bounded) ∷ᴾ proj₂ distinct
        ; sync     = (refl , ranked-top sources (Named.ords-below (proj₁ named)) (Named.ords-below (proj₂ named))) ∷ˢ sync
        ; rows     = reg-cons {Γ = Γ} κ rows
        ; dlv-alike = spent-cons {Γ = Γ} κ rows dlv-alike ; dying-alike = spent-cons {Γ = Γ} κ rows dying-alike
        ; latches  = latches ; dying-done = dying-done
        ; bounded  = n<1+n _ ∷ᵃ mapᵃ m<n⇒m<1+n (proj₁ bounded) , n<1+n _ ∷ᵃ mapᵃ m<n⇒m<1+n (proj₂ bounded)
        ; swept    = trans (guard-none KP lP bP (Named.srcs-below (proj₁ named))) (sym (guard-none KI lI bI (Named.srcs-below (proj₂ named))))
                     ∷ᵖ swept
        ; uncut    = uncut
        ; named    = named-hop (proj₁ named) refl (mapᵃ m<n⇒m<1+n (Named.srcs-below (proj₁ named)))
                   , named-hop (proj₂ named) refl (mapᵃ m<n⇒m<1+n (Named.srcs-below (proj₂ named)))
        ; rids     = rids
        ; fresh-ids = mapᵃ m<n⇒m<1+n (proj₁ fresh-ids) , mapᵃ m<n⇒m<1+n (proj₂ fresh-ids)
        ; above    = above ; census = census ; owned = owned
        ; ruleP    = rP ; ruleI = rI ; scripts = scripts
        }

    -- REGISTERED: the rows join both registries last, paired as `defer~`
    registered : Rule sP₂ (stP₂ (KP ++ rowP ∷ [])) → Rule sI₂ (stI₂ (KI ++ rowI ∷ []))
               → Σ (After S ([] , sP₂ , stP₂ (KP ++ rowP ∷ [])) ([] , sI₂ , stI₂ (KI ++ rowI ∷ []))) λ B
                   → PathRel {Γ = Γ} κ (Store.π (After.store B)) (EvalSt.nodes stP₁) (EvalSt.nodes stI₁) p q
    registered rP rI =
      after S₂ (λ { (inj₁ c) → inj₁ c ; (inj₂ (a , b , pp)) → inj₂ (a , b , part-snoc {Γ = Γ} κ (reg-cons {Γ = Γ} κ rows) new-row (part-cons {Γ = Γ} κ rows pp)) })
               (persist (KP ++ rowP ∷ []) (KI ++ rowI ∷ []) S₂
                  (λ ar → arr-snoc {Γ = Γ} κ (reg-cons {Γ = Γ} κ rows) new-row (arr-cons {Γ = Γ} κ rows (Arr.rows ar))
                            (((λ e → ⊥-elim (<-irrefl e (Arr.boundP ar))) , (λ e′ → ⊥-elim (<-irrefl e′ (Arr.boundI ar)))) , _)))
               []ᵖ (λ m → m)
      , pr
      where
      off-new : ∀ {j} → Unpaired {Γ = Γ} κ π j → j ∈ nodesOf (proj₂ (proj₂ (proj₂ rowI))) → ⊥
      off-new un (here refl) = un (∈-vals pm (here refl))
      off-new un (there m)   = un (rel-vals {Γ = Γ} κ pr m)

      S₂ : Store κ sP₂ (stP₂ (KP ++ rowP ∷ [])) sI₂ (stI₂ (KI ++ rowI ∷ []))
      S₂ = record
        { π = π ; π-keys = π-keys ; π-vals = π-vals ; pairs-below = pairs-below
        ; sources  = new-src ∷ᵖ sources
        ; numbers  = dyn~ bP bI ∷ᵖ numbers
        ; distinct = apart (proj₁ bounded) ∷ᴾ proj₁ distinct , apart (proj₂ bounded) ∷ᴾ proj₂ distinct
        ; sync     = (refl , ranked-top sources (Named.ords-below (proj₁ named)) (Named.ords-below (proj₂ named))) ∷ˢ sync
        ; rows     = reg-snoc {Γ = Γ} κ (reg-cons {Γ = Γ} κ rows) new-row
        ; dlv-alike = spent-snoc {Γ = Γ} κ (reg-cons {Γ = Γ} κ rows) new-row (spent-cons {Γ = Γ} κ rows dlv-alike)
                        (trans (none-below (Named.dlv-below (proj₁ named))) (sym (none-below (Named.dlv-below (proj₂ named)))))
        ; dying-alike = spent-snoc {Γ = Γ} κ (reg-cons {Γ = Γ} κ rows) new-row (spent-cons {Γ = Γ} κ rows dying-alike)
                        (trans (member-below (Named.dying-below (proj₁ named))) (sym (member-below (Named.dying-below (proj₂ named)))))
        ; latches  = latches ; dying-done = dying-done
        ; bounded  = n<1+n _ ∷ᵃ mapᵃ m<n⇒m<1+n (proj₁ bounded) , n<1+n _ ∷ᵃ mapᵃ m<n⇒m<1+n (proj₂ bounded)
        ; swept    = trans (guard-new KP rowP lP (same-refl src)) (sym (guard-new KI rowI lI (same-refl src′)))
                     ∷ᵖ swept-snoc {K = KP} {KI} {rowP} {rowI} swept (proj₁ bounded) (proj₂ bounded)
        ; uncut    = ++⁺ᵃ (proj₁ uncut) (none-below (Named.cut-below (proj₁ named)) ∷ᵃ []ᵃ)
                   , ++⁺ᵃ (proj₂ uncut) (none-below (Named.cut-below (proj₂ named)) ∷ᵃ []ᵃ)
        ; named    = named-hop (proj₁ named) refl (++⁺ᵃ (mapᵃ m<n⇒m<1+n (Named.srcs-below (proj₁ named))) (n<1+n _ ∷ᵃ []ᵃ))
                   , named-hop (proj₂ named) refl (++⁺ᵃ (mapᵃ m<n⇒m<1+n (Named.srcs-below (proj₂ named))) (n<1+n _ ∷ᵃ []ᵃ))
        ; rids     = ++⁺ᴾ (proj₁ rids) ([]ᵃ ∷ᴾ []ᴾ) (mapᵃ (λ lt → <⇒≢ lt ∷ᵃ []ᵃ) (proj₁ fresh-ids))
                   , ++⁺ᴾ (proj₂ rids) ([]ᵃ ∷ᴾ []ᴾ) (mapᵃ (λ lt → <⇒≢ lt ∷ᵃ []ᵃ) (proj₂ fresh-ids))
        ; fresh-ids = ++⁺ᵃ (mapᵃ m<n⇒m<1+n (proj₁ fresh-ids)) (n<1+n _ ∷ᵃ []ᵃ)
                    , ++⁺ᵃ (mapᵃ m<n⇒m<1+n (proj₂ fresh-ids)) (n<1+n _ ∷ᵃ []ᵃ)
        ; above    = ++⁺ᵃ (proj₁ above) (T-true (≤⇒≤ᵇ (<⇒≤ bP)) ∷ᵃ []ᵃ) , ++⁺ᵃ (proj₂ above) (T-true (≤⇒≤ᵇ (<⇒≤ bI)) ∷ᵃ []ᵃ)
        ; census   = λ i h → census-snoc {K = KI} rowI (sameSource-no (<⇒≢ (<-trans (raw<ₙ i) bI))) (sameSource-no (<⇒≢ (<-trans (stamped< i) bI)))
                                             (census i h)
        ; owned    = ++⁺ᵃ (tabulateᵃ (λ {r} r∈ ns {j} b → ++⁺ᵃ (lookupᵃ owned r∈ ns b)
                                        ((λ h → ⊥-elim (off-new (reg-unp {Γ = Γ} κ rows {r′ = r} r∈ ns b) (has-node {k = j} (proj₂ (proj₂ (proj₂ rowI))) (subst T (sym h) tt)))) ∷ᵃ []ᵃ)))
                          ((λ _ {_} ()) ∷ᵃ []ᵃ)
        ; ruleP    = rP ; ruleI = rI ; scripts = scripts
        }

    -- the two registrations agree on whether they are spent
    hop-at : (cP cI : Bool) → cP ≡ cI
           → Rule sP₂ (stP₂ (if cP then KP else KP ++ rowP ∷ [])) → Rule sI₂ (stI₂ (if cI then KI else KI ++ rowI ∷ []))
           → Σ (After S ([] , sP₂ , stP₂ (if cP then KP else KP ++ rowP ∷ [])) ([] , sI₂ , stI₂ (if cI then KI else KI ++ rowI ∷ []))) λ B
               → PathRel {Γ = Γ} κ (Store.π (After.store B)) (EvalSt.nodes stP₁) (EvalSt.nodes stI₁) p q
    hop-at true  true  refl = spent
    hop-at false false refl = registered

  -- THE HOP'S SOURCE AND ROW AGAINST ITS PARTNER'S: the pending pair
  -- relates as `defer~`, both rows through the paired merge, and the
  -- tails stay related.  `Sound` of both paths, at the stores before
  -- the merges were installed, as `register-sound` takes it.
  hop-register : ∀ {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {u}
                   {lo} {p : Path Γ lo u t} {q : Path (plainᵏ Γ κ) (n + lo) (emitᵗ u) (emitᵗ t)} {now x′ x}
                   (S : St (record sP { mint = setAt nodeᵏ (suc (nodeCt sP)) (Sched.mint sP) })
                           (installNode (nodeCt sP) (mergeAll-st {t = u} nothing 0 [] false) stP)
                           (record sI { mint = setAt nodeᵏ (suc (nodeCt sI)) (Sched.mint sI) })
                           (installNode (nodeCt sI) (mergeAll-st {t = emitᵗ u} nothing 0 [] false) stI))
               → (nodeCt sP , nodeCt sI ∷ []) ∈ Store.π S
               → PathRel {Γ = Γ} κ (Store.π S) (EvalSt.nodes (installNode (nodeCt sP) (mergeAll-st {t = u} nothing 0 [] false) stP))
                                       (EvalSt.nodes (installNode (nodeCt sI) (mergeAll-st {t = emitᵗ u} nothing 0 [] false) stI)) p q
               → Sound p sP stP → Sound q sI stI
               → DeferRel κ u x′ x
               → let nid = nodeCt sP ; src = freshId sourceᵏ (Sched.mint sP) ; ord = freshId ordinalᵏ (Sched.mint sP) ; rid = freshId regᵏ (Sched.mint sP)
                     nid′ = nodeCt sI ; src′ = freshId sourceᵏ (Sched.mint sI) ; ord′ = freshId ordinalᵏ (Sched.mint sI) ; rid′ = freshId regᵏ (Sched.mint sI)
                     stP′ = register rid (atDyn src lo) (thru-outer mergeAllᵒ nid ↠[ ≤-refl ] p)
                              (installNode nid (mergeAll-st {t = u} nothing 0 [] false) stP)
                     stI′ = register rid′ (atDyn src′ (n + lo)) (thru-outer mergeAllᵒ nid′ ↠[ ≤-refl ] q)
                              (installNode nid′ (mergeAll-st {t = emitᵗ u} nothing 0 [] false) stI)
                 in Σ (After S
                        ( [] , record sP { mint = setAt regᵏ (suc rid) (setAt nodeᵏ (suc nid) (setAt sourceᵏ (suc src)
                                                    (setAt ordinalᵏ (suc ord) (Sched.mint sP))))
                                         ; live = record { source = src ; ordinal = ord ; elemTy = echoᵗ u
                                                         ; pending = (suc now , (inj₁ tt , inj₂ x)) ∷ [] }
                                                  ∷ Sched.live sP }
                        , stP′ )
                        ( [] , record sI { mint = setAt regᵏ (suc rid′) (setAt nodeᵏ (suc nid′) (setAt sourceᵏ (suc src′)
                                                    (setAt ordinalᵏ (suc ord′) (Sched.mint sI))))
                                         ; live = record { source = src′ ; ordinal = ord′ ; elemTy = echoᵗ (emitᵗ u)
                                                         ; pending = (suc now , (inj₁ tt , inj₂ x′)) ∷ [] }
                                                  ∷ Sched.live sI }
                        , stI′ )) λ B
                    → PathRel {Γ = Γ} κ (Store.π (After.store B)) (EvalSt.nodes stP′) (EvalSt.nodes stI′) p q
  hop-register {sP} {stP} {sI} {stI} {u} {lo} {p} {q} {now} {x′} {x} S pm pr soP soI rel =
    H.hop-at (spentOn p (EvalSt.nodes H.stP₁)) (spentOn q (EvalSt.nodes H.stI₁)) (path-spent {Γ = Γ} κ pr)
      (Sound.ruled (register-sound {κ = p} {sched = sP} {sched′ = H.sP₂} {st = H.stP₁} H.rid (atDyn H.src lo)
                      (thru-outer mergeAllᵒ H.nid ↠[ ≤-refl ] p) (n≤1+n _) refl (thru-cls mergeAllᵒ H.nid ≤-refl p)
                      (λ so → (λ k a h → <-irrefl (sym (node-eq a)) (Sound.fresh-path so k h)) , Sound.distinct so)
                      (sub-ot (λ r∈ → r∈) ≤-refl soP)))
      (Sound.ruled (register-sound {κ = q} {sched = sI} {sched′ = H.sI₂} {st = H.stI₁} H.rid′ (atDyn H.src′ (n + lo))
                      (thru-outer mergeAllᵒ H.nid′ ↠[ ≤-refl ] q) (n≤1+n _) refl (thru-cls mergeAllᵒ H.nid′ ≤-refl q)
                      (λ so → (λ k a h → <-irrefl (sym (node-eq a)) (Sound.fresh-path so k h)) , Sound.distinct so)
                      (sub-ot (λ r∈ → r∈) ≤-refl soI)))
    where module H = Hop {sP} {stP} {sI} {stI} {u} {lo} {p} {q} {now} {x′} {x} S pm pr rel
