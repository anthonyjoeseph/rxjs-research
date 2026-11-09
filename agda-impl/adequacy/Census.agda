{-# OPTIONS --guardedness #-}

-- A BOUNDED MERGE'S LANES COUNTED.  Each lane, by index, is dead, its end
-- passed, or ends at or past an owed end of a begun lane (`Census`).  The
-- dead lanes alone can end before every owed end, and they are as many
-- as the slots the live count leaves out: so a value's lane starts where
-- the schedule says, freed or queued.
module adequacy.Census where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; ≤∧≢⇒<; ≤-pred; m<1+n⇒m<n∨m≡n; m≤m+n; n<1+n; ≤-trans; ≤-reflexive;
                                      ∸-monoʳ-≤; m+n∸n≡m; <-irrefl; <-≤-trans; m≤n+m; m+n≤o⇒m≤o∸n; m≤n⇒m≤1+n)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; yes; no)

open import Tree using (mergeᶠ)
open import denotation.Position using (Pos; ix; _⊕_)
open import denotation.EmissionSet using (EmissionSet; Den; out; end; _≺_; _≼_; enter; module Bounded; module Values)
open import denotation.Laws.Modulus using (≼-or-≻; ≺-irrefl; ≺-trans; ≺-absurd; ≼-refl; ≼-trans; ≼-≺-≺; ≺-ext)
open import denotation.Laws.Worlds using (Ok; InvAt; InvD; world-after)
open import denotation.Laws.Worlds.Leaves using (out-inj)
open import denotation.Laws.Nth using (module Nths)
open import denotation.Laws.BoundedInv using (module BoundedI)
open import adequacy.Cursor using (Cur; Owes; Pol; polF; Begun; none; more; l-live; l-dead; h-live; h-end; h-kill; OwedEnd; Ahead; Head; _≈_)
  renaming (Nths to Listed)
open import adequacy.Rows using (_⇄_)
open import adequacy.Bound using (past)

lt-le : ∀ {x c} → x ≺ c → x ≼ c
lt-le {x} {c} lt cx = ≺-absurd {x} {c} lt cx

eq-le : ∀ {x c} → x ≡ c → x ≼ c
eq-le {x} refl = ≼-refl {x}

module Count {A B H at} (ok : Ok H at) (m : ℕ) (F : A → Den B) (fi : ∀ a → InvD H (F a)) {O : EmissionSet A} (Io : InvAt H at O) where
  open Bounded m F O
  open Values O using (Nth; first; next; Next)
  open BoundedI ok m F fi Io using (kth-cons; kth-down; kth-tail; kth-mono; sub-fun; lane-end; LI)
  open Nths O using (nth-val; nth-fun; nth-lt; nth-inj)

  P : Pol A B
  P = polF (mergeᶠ (just m)) F O

  ------------------------------------------------------------------------
  -- At least k of the lanes end where `Q` holds.

  AtL : (Pos → Set) → List (Pos → Set) → ℕ → Set
  AtL Q ls zero    = ⊤
  AtL Q ls (suc k) = Kth Q ls k

  atl-hit : ∀ {Q l ls k} → Σ Pos (λ c → l c × Q c) → AtL Q ls k → AtL Q (l ∷ ls) (suc k)
  atl-hit {k = zero}  h _ = inj₁ h
  atl-hit {k = suc k} h K = inj₁ (h , K)

  atl-skip : ∀ {Q l ls k} → AtL Q ls k → AtL Q (l ∷ ls) k
  atl-skip {k = zero}  _ = tt
  atl-skip {k = suc k} K = kth-cons K

  kth-le : ∀ {Q} ls {j k} → j ≤ k → Kth Q ls k → Kth Q ls j
  kth-le ls {k = zero} z≤n K = K
  kth-le ls {j} {suc k} le K with j ≟ suc k
  ... | yes refl = K
  ... | no ne    = kth-le ls (≤-pred (≤∧≢⇒< le ne)) (kth-down ls K)

  -- More dead than the live count leaves slots for: a freed slot's lane.
  freed-k : ∀ {Q} N {d n} → d + n ≡ N → n < m → m ≤ N → AtL Q (Sched N) d → Kth Q (Sched N) (N ∸ m)
  freed-k N {zero}      eq lt le _ = ⊥-elim (<-irrefl eq (<-≤-trans lt le))
  freed-k N {suc d} {n} eq lt le K =
    kth-le (Sched N) (≤-trans (∸-monoʳ-≤ N lt) (≤-reflexive (trans (cong (_∸ suc n) (sym eq)) (m+n∸n≡m d n)))) K

  ------------------------------------------------------------------------
  -- A lane's ends, by index and by value

  ends-at : ∀ {i q a c} → Nth i q a → Ends i (Sched i) c → Lane q a c end
  ends-at nx (q′ , a′ , s′ , nq′ , st′ , af) with nth-fun nq′ nx
  ... | refl with out-inj (InvAt.func Io (nth-val nq′) (nth-val nx))
  ...   | refl = _ , s′ , (nq′ , st′) , af

  lane-ends : ∀ {i q a c} → Nth i q a → Lane q a c end → Ends i (Sched i) c
  lane-ends nx (j , s , (nj , st) , af) with nth-inj nj nx
  ... | refl = _ , _ , s , nj , st , af

  ends-fun : ∀ {i c c′} → Ends i (Sched i) c → Ends i (Sched i) c′ → c ≡ c′
  ends-fun (_ , _ , _ , nq , st , af) (_ , _ , _ , nq′ , st′ , af′) with sub-fun (nq , st) (nq′ , st′)
  ... | refl , refl , refl = lane-end (nq , st) af af′

  no-two : ∀ {N c c′} → Ends N (Sched N) c → Ends N (Sched N) c′ → c′ ≺ c → ⊥
  no-two {c = c} e e′ lt = ≺-irrefl {c} (subst (_≺ c) (sym (ends-fun e e′)) lt)

  -- One lane ending at `c` and k + 1 before it: k + 2 at or before it.
  kth-add : ∀ N {c k} → Kth (_≡ c) (Sched N) 0 → Kth (_≺ c) (Sched N) k → Kth (_≼ c) (Sched N) (suc k)
  kth-add zero ()
  kth-add (suc N) {k = zero}  (inj₁ (_ , e₀ , refl)) (inj₁ (_ , e′ , lt))       = ⊥-elim (no-two e₀ e′ lt)
  kth-add (suc N) {c} {zero}  (inj₁ (_ , e₀ , refl)) (inj₂ K)                   = inj₁ ((c , e₀ , ≼-refl {c}) , kth-mono (λ {x} → lt-le {x} {c}) (Sched N) K)
  kth-add (suc N) {c} {zero}  (inj₂ Z)               (inj₁ (c′ , e′ , lt))      = inj₁ ((c′ , e′ , lt-le {c′} {c} lt) , kth-mono (λ {x} → eq-le {x} {c}) (Sched N) Z)
  kth-add (suc N) {k = zero}  (inj₂ Z)               (inj₂ K)                   = inj₂ (kth-add N Z K)
  kth-add (suc N) {k = suc k} (inj₁ (_ , e₀ , refl)) (inj₁ ((_ , e′ , lt) , _)) = ⊥-elim (no-two e₀ e′ lt)
  kth-add (suc N) {c} {suc k} (inj₁ (_ , e₀ , refl)) (inj₂ K)                   = inj₁ ((c , e₀ , ≼-refl {c}) , kth-mono (λ {x} → lt-le {x} {c}) (Sched N) K)
  kth-add (suc N) {c} {suc k} (inj₂ Z)               (inj₁ ((c′ , e′ , lt) , K)) = inj₁ ((c′ , e′ , lt-le {c′} {c} lt) , kth-add N Z K)
  kth-add (suc N) {k = suc k} (inj₂ Z)               (inj₂ K)                   = inj₂ (kth-add N Z K)

  kth-add′ : ∀ N {c d} → Kth (_≡ c) (Sched N) 0 → AtL (_≺ c) (Sched N) d → Kth (_≼ c) (Sched N) d
  kth-add′ N {c} {zero} Z _ = kth-mono (λ {x} → eq-le {x} {c}) (Sched N) Z
  kth-add′ N {d = suc d} Z K = kth-add N Z K

  kth-in : ∀ N {j c} → j < N → Ends j (Sched j) c → Kth (_≡ c) (Sched N) 0
  kth-in (suc N) lt e with m<1+n⇒m<n∨m≡n lt
  ... | inj₁ lt′  = inj₂ (kth-in N lt′ e)
  ... | inj₂ refl = inj₁ (_ , e , refl)

  ------------------------------------------------------------------------
  -- THE CENSUS: each lane by index, at the cursor `C`, dead, its end
  -- passed; or on, every end it has at or past an owed end of a lane
  -- begun in `vs`.  Indexed by the lanes and the dead among them.

  data Census (C : Cur) (vs : List (Pos × A)) : ℕ → ℕ → Set where
    c-nil  : Census C vs 0 0
    c-dead : ∀ {N d c} → Census C vs N d → Ends N (Sched N) c → ¬ Owes C c → Census C vs (suc N) (suc d)
    c-on   : ∀ {N d} → Census C vs N d → (∀ {c} → Ends N (Sched N) c → Σ Pos λ c′ → OwedEnd C P vs c′ × c′ ≼ c)
           → Census C vs (suc N) d

  -- Every dead lane's end where `Q` holds: as many ends.
  cen-lo : ∀ {C vs N d Q} → (∀ {c} → ¬ Owes C c → Q c) → Census C vs N d → AtL Q (Sched N) d
  cen-lo g c-nil = tt
  cen-lo g (c-dead {N} {d} cs e nc) = atl-hit {l = Ends N (Sched N)} {ls = Sched N} {k = d} (_ , e , g nc) (cen-lo g cs)
  cen-lo g (c-on {N} {d} cs _)      = atl-skip {l = Ends N (Sched N)} {ls = Sched N} {k = d} (cen-lo g cs)

  -- No end at or past an owed end where `Q` holds: no more.
  cen-hi : ∀ {C vs N d Q} → (∀ {c′ c} → OwedEnd C P vs c′ → c′ ≼ c → Q c → ⊥) → Census C vs N d → ¬ Kth Q (Sched N) d
  cen-hi g c-nil ()
  cen-hi g (c-dead {N} cs _ _) K = cen-hi g cs (kth-tail (Sched N) K)
  cen-hi g (c-on {N} {zero} cs on) (inj₁ (_ , e , qc))       = let (_ , oe , le) = on e in g oe le qc
  cen-hi g (c-on {N} {zero} cs on) (inj₂ K)                  = cen-hi g cs K
  cen-hi g (c-on {N} {suc d} cs on) (inj₁ ((_ , e , qc) , _)) = let (_ , oe , le) = on e in g oe le qc
  cen-hi g (c-on {N} {suc d} cs on) (inj₂ K)                 = cen-hi g cs K

  -- One more end where `Q` holds than the dead: a lane on ends there.
  cen-find : ∀ {C vs N d Q} → Census C vs N d → Kth Q (Sched N) d
           → Σ Pos λ c → Σ Pos λ c′ → OwedEnd C P vs c′ × c′ ≼ c × Q c
  cen-find c-nil ()
  cen-find (c-dead {N} cs _ _) K = cen-find cs (kth-tail (Sched N) K)
  cen-find (c-on {N} {zero} cs on) (inj₁ (c , e , qc))       = let (c′ , oe , le) = on e in c , c′ , oe , le , qc
  cen-find (c-on {N} {zero} cs on) (inj₂ K)                  = cen-find cs K
  cen-find (c-on {N} {suc d} cs on) (inj₁ ((c , e , qc) , _)) = let (c′ , oe , le) = on e in c , c′ , oe , le , qc
  cen-find (c-on {N} {suc d} cs on) (inj₂ K)                 = cen-find cs K

  ------------------------------------------------------------------------
  -- The census taken: the begun lanes, then the waiting ones.

  -- The begun lanes from index `i`: the dead ones those the live count
  -- leaves out.
  cen-begun : ∀ {Γ sc Rl C vs₀ i vs ls n d} → Listed O i vs → Begun {Γ} sc Rl C P O vs ls n
            → (∀ {x} → x ∈ vs → x ∈ vs₀) → Census C vs₀ i d
            → Σ ℕ λ d′ → Census C vs₀ (i + length vs) d′ × d′ + n ≡ d + length vs
  cen-begun {i = i} {d = d} _ none _ cs = d , subst (λ k → Census _ _ k d) (sym (+-identityʳ i)) cs , refl
  cen-begun {C = C} {vs₀} {i} {d = d} (nx , ns) (more {q} {a} {vs = vs} {n = n} _ _ _ (l-live (h-live _ _ _ ue) _ _) bg) inc cs =
    let (d′ , cs′ , eq) = cen-begun ns bg (λ iv → inc (there iv)) (c-on cs on)
    in d′ , subst (λ k → Census C vs₀ k d′) (sym (+-suc i (length vs))) cs′
          , trans (+-suc d′ n) (trans (cong suc eq) (sym (+-suc d (length vs))))
    where
      on : ∀ {c} → Ends i (Sched i) c → Σ Pos λ c′ → OwedEnd C P vs₀ c′ × c′ ≼ c
      on {c} e = c , (q , a , inc (here refl) , ends-at nx e , (λ ()) , ue (ends-at nx e) (λ ())) , ≼-refl {c}
  cen-begun {C = C} {vs₀} {i} {d = d} (nx , ns) (more {vs = vs} _ _ _ (l-dead (h-end lc nc _) _ _ _) bg) inc cs =
    let (d′ , cs′ , eq) = cen-begun ns bg (λ iv → inc (there iv)) (c-dead cs (lane-ends nx lc) nc)
    in d′ , subst (λ k → Census C vs₀ k d′) (sym (+-suc i (length vs))) cs′ , trans eq (sym (+-suc d (length vs)))
  cen-begun (_ , _) (more _ _ _ (l-dead (h-kill () _ _) _ _ _) _) _ _

  -- The waiting lanes from index `i`: each on, past the owed end it waits on.
  cen-wait : ∀ {C vs ws₀ i ws d} → Listed O i ws → (∀ {x} → x ∈ ws → x ∈ ws₀) → Ahead C P vs ws₀
           → Census C vs i d → Census C vs (i + length ws) d
  cen-wait {i = i} {ws = []} _ _ _ cs = subst (λ k → Census _ _ k _) (sym (+-identityʳ i)) cs
  cen-wait {C = C} {vs} {i = i} {ws = (q , a) ∷ ws} {d} (nx , ns) inc ah cs =
    subst (λ k → Census C vs k d) (sym (+-suc i (length ws))) (cen-wait ns (λ iv → inc (there iv)) ah (c-on cs on))
    where
      on : ∀ {c} → Ends i (Sched i) c → Σ Pos λ c′ → OwedEnd C P vs c′ × c′ ≼ c
      on {c} e with ends-at nx e
      ... | j , s , sub , af with ah {q} {a} {s} (inc (here refl)) (j , sub)
      ...   | q′ , a′ , c′ , iv , lc , kc , oc , cs′ = c′ , (q′ , a′ , iv , lc , (λ {q″} → kc {q″}) , oc) , lt-le {c′} {c} (≺-trans {c′} {s} {c} cs′ (proj₂ af))

  ------------------------------------------------------------------------
  -- The values listed in order

  nths-∈ : ∀ {i xs q a} → Listed O i xs → (q , a) ∈ xs → Σ ℕ λ j → Nth j q a × j < i + length xs
  nths-∈ {i} {_ ∷ xs} (nx , _) (here refl) = i , nx , subst (i <_) (sym (+-suc i (length xs))) (s≤s (m≤m+n i (length xs)))
  nths-∈ {i} {_ ∷ xs} (_ , ns) (there iv) =
    let (j , nj , lt) = nths-∈ ns iv in j , nj , subst (j <_) (sym (+-suc i (length xs))) lt

  nths-split : ∀ {i} xs {ys} → Listed O i (xs ++ ys) → Listed O i xs × Listed O (i + length xs) ys
  nths-split {i} []       {ys} ns        = tt , subst (λ k → Listed O k ys) (sym (+-identityʳ i)) ns
  nths-split {i} (_ ∷ xs) {ys} (nx , ns) =
    let (l , r) = nths-split xs ns in (nx , l) , subst (λ k → Listed O k ys) (sym (+-suc i (length xs))) r

  nths-snoc : ∀ {i} xs {q a} → Listed O i xs → Nth (i + length xs) q a → Listed O i (xs ++ [ (q , a) ])
  nths-snoc {i} []       {q} {a} _         nx = subst (λ k → Nth k q a) (+-identityʳ i) nx , tt
  nths-snoc {i} (_ ∷ xs) {q} {a} (ny , ns) nx = ny , nths-snoc xs ns (subst (λ k → Nth k q a) (+-suc i (length xs)) nx)

  past-head : ∀ {q b} {y : Pos × A} {xs} → (q , b) ∈ (y ∷ xs) → proj₁ y ≺ q → (q , b) ∈ xs
  past-head {q} (here refl) lt = ⊥-elim (≺-irrefl {q} lt)
  past-head     (there iv)  _  = iv

  -- The value at `p`, every value before it listed: next.
  nth-from : ∀ {i q₀ a₀ xs p a} → Nth i q₀ a₀ → Listed O (suc i) xs → q₀ ≺ p
           → (∀ {x} → x ∈ xs → proj₁ x ≺ p) → (∀ {q b} → O q (out b) → q₀ ≺ q → q ≺ p → (q , b) ∈ xs)
           → O p (out a) → Nth (suc i + length xs) p a
  nth-from {i} {q₀} {xs = []} {p} {a} nq _ lt _ wh y = subst (λ k → Nth k p a) (sym (+-identityʳ (suc i))) (next nq y lt nx)
    where
      nx : Next q₀ p
      nx {k} x qk with ≼-or-≻ p k
      ... | inj₁ le = le
      ... | inj₂ kp with wh x qk kp
      ...   | ()
  nth-from {i} {q₀} {xs = (q₁ , a₁) ∷ xs} {p} {a} nq (nq₁ , ns) _ bf wh y =
    subst (λ k → Nth k p a) (sym (+-suc (suc i) (length xs))) (nth-from nq₁ ns (bf (here refl)) (λ iv → bf (there iv)) wh′ y)
    where
      wh′ : ∀ {q b} → O q (out b) → q₁ ≺ q → q ≺ p → (q , b) ∈ xs
      wh′ {q} {b} x lt qp = past-head {q} {b} {q₁ , a₁} (wh x (≺-trans {q₀} {q₁} {q} (nth-lt (n<1+n i) nq nq₁) lt) qp) lt

  nth-new : ∀ {xs p a} → Listed O 0 xs → (∀ {x} → x ∈ xs → proj₁ x ≺ p)
          → (∀ {q b} → O q (out b) → q ≺ p → (q , b) ∈ xs) → O p (out a) → Nth (length xs) p a
  nth-new {[]} {p} _ _ wh y = first y fst
    where
      fst : ∀ {k b} → O k (out b) → p ≼ k
      fst {k} x with ≼-or-≻ p k
      ... | inj₁ le = le
      ... | inj₂ kp with wh x kp
      ...   | ()
  nth-new {(q₀ , a₀) ∷ xs} (nq₀ , ns) bf wh y =
    nth-from nq₀ ns (bf (here refl)) (λ iv → bf (there iv)) (λ {q} {b} x lt qp → past-head {q} {b} {q₀ , a₀} (wh x qp) lt) y

  ------------------------------------------------------------------------
  -- A lane subscribed: its rows the value's, entered where it starts.

  sub-ln : ∀ {i q s a} → Sub i q s a → enter (F a) s ≈ Lane q a
  sub-ln {q = q} {s} {a} sb =
    record { alike = (λ (x , v) → (_ , s , sb , x , g x) , v) ⇄ (λ ((_ , _ , sb′ , x , _) , v) → back sb′ x , v)
           ; cov   = [] , λ (_ , _ , sb′ , x , _) → inj₁ (back sb′ x)
           ; voc   = λ x → _ , s , sb , x , g x }
    where
      g : ∀ {y e} → enter (F a) s y e → s ≺ y
      g x = world-after (InvAt.world (LI sb) x) (InvAt.real (LI sb) x)
      back : ∀ {j s′ y e} → Sub j q s′ a → enter (F a) s′ y e → enter (F a) s y e
      back (nj , st′) x with nth-inj nj (proj₁ sb)
      ... | refl with sub-fun (nj , st′) sb
      ...   | refl , refl , refl = x

  ------------------------------------------------------------------------
  -- EVERY SLOT TAKEN, the census at a passed value's index: its lane has
  -- no room, is not freed, so it is queued past an owed end.

  owed-start : ∀ {C vs N d q s} → Census C vs N d → m ≤ N → d ≤ N ∸ m → ¬ Owes C q → Starts N q (Sched N) s
             → Σ Pos λ q′ → Σ A λ a′ → Σ Pos λ c′ → (q′ , a′) ∈ vs × Lane q′ a′ c′ end × (∀ {q″} → ⊥ → c′ ≼ q″) × Owes C c′ × c′ ≺ s
  owed-start _ le _ _ (room lt) = ⊥-elim (<-irrefl refl (<-≤-trans lt le))
  owed-start {C} {N = N} {q = q} cs _ d≤ nq (freed _ K) =
    ⊥-elim (cen-hi (λ {c′} {c″} (_ , _ , _ , _ , _ , oc) le′ lt′ → ≺-absurd {q} {c′} (past C nq oc) (≼-≺-≺ {c′} {c″} {q} le′ lt′)) cs (kth-le (Sched N) d≤ K))
  owed-start {N = N} cs _ d≤ _ (queued {c₀} _ _ _ K _) =
    let (c″ , c′ , (q′ , a′ , iv , lc , kc , oc) , le′ , le₀) = cen-find {Q = _≼ c₀} cs (kth-le (Sched N) d≤ K)
    in q′ , a′ , c′ , iv , lc , (λ {q″} → kc {q″}) , oc , ≼-≺-≺ {c′} {c₀} {c₀ ⊕ [ ix 1 ]} (≼-trans {c′} {c″} {c₀} le′ le₀) (≺-ext c₀ [])

  -- Every value waiting past index `N`, every slot taken: each lane
  -- starts past an owed end, the earlier ones counted on.
  ahead-from : ∀ {C vs N d} ws → Listed O N ws → (∀ {q a} → (q , a) ∈ ws → ¬ Owes C q) → Census C vs N d → d + m ≤ N → Ahead C P vs ws
  ahead-from [] _ _ _ _ ()
  ahead-from {C} {vs} {N} {d} ((q₁ , a₁) ∷ ws) (n₁ , ns) nq cs le = go
    where
      hd : ∀ {s} → Starts N q₁ (Sched N) s → _
      hd = owed-start cs (≤-trans (m≤n+m m d) le) (m+n≤o⇒m≤o∸n d le) (nq (here refl))
      on : ∀ {c} → Ends N (Sched N) c → Σ Pos λ c′ → OwedEnd C P vs c′ × c′ ≼ c
      on {c} e with ends-at n₁ e
      ... | j , s , (nj , st) , af with nth-inj nj n₁
      ...   | refl with hd st
      ...     | q′ , a′ , c′ , iv , lc , kc , oc , lt = c′ , (q′ , a′ , iv , lc , (λ {q″} → kc {q″}) , oc) , lt-le {c′} {c} (≺-trans {c′} {s} {c} lt (proj₂ af))
      go : Ahead C P vs ((q₁ , a₁) ∷ ws)
      go (here refl) (i , ni , st) with nth-inj ni n₁
      ... | refl = hd st
      go (there iw) st = ahead-from ws ns (λ i → nq (there i)) (c-on cs on) (m≤n⇒m≤1+n le) iw st

  -- The queue's head, every slot taken, at the next index: queued under
  -- the first owed end.
  head-at : ∀ {C vs d q a} → Listed O 0 vs → Census C vs (length vs) d → d + m ≡ length vs → ¬ Owes C q → Nth (length vs) q a
          → ∀ {ws} → Head C P vs ((q , a) ∷ ws)
  head-at {C} {vs} {d} Lv cs dm nq nv {c = c₀} (q′ , a′ , iv , lc , _ , oc) least = length vs , nv , queued m≤v (past C nq oc) kin kle nkl
    where
      m≤v = subst (m ≤_) dm (m≤n+m m d)
      kin = let (j , nj , jlt) = nths-∈ Lv iv in kth-in (length vs) jlt (lane-ends nj lc)
      dv : length vs ∸ m ≡ d
      dv = trans (cong (_∸ m) (sym dm)) (m+n∸n≡m d m)
      kle = subst (Kth (_≼ c₀) (Sched (length vs))) (sym dv)
              (kth-add′ (length vs) kin (cen-lo (λ {c″} nc → past C nc oc) cs))
      nkl = subst (λ k → ¬ Kth (_≺ c₀) (Sched (length vs)) k) (sym dv)
              (cen-hi (λ {c′} {c″} oe′ le′ lt′ → ≼-trans {c₀} {c′} {c″} (least oe′) le′ lt′) cs)
