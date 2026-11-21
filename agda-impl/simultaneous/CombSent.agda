{-# OPTIONS --guardedness #-}

-- WHAT THE SCAN'S SOURCE SENDS, read back: a branch's row is that
-- branch's, where its reader met it, and the trackers and the closing
-- `nothing` send no branch's row.  Nothing under the source is deferred,
-- so every approximant reads it as the meaning does.
module simultaneous.CombSent where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n)
open import Data.Bool.Properties using (T-≡)
open import Function using (Equivalence)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)

open import Tree using (mergeᶠ; takeWhile; flatMap; of; map; connected)
open import denotation.Position using (Pos; Label; root; _≟ᵖ_; ix; last; sub; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Den; EmissionSet; enter; DenEnv; ⟦_⟧; approx; out; end; Reach; InE; at-out; on-out;
  Ended; After; LaneOf; _≺_; _≼_; map-end; hot; Rejoin; shown; ended; late; module Op; module TakeWhile; module Merge; module Bounded; module Values)
open import denotation.Events using (ofᴱ; <ᵖ-part; <ᵖ-apart)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≺-≼-≺; ≼-refl; ≺→≼; ≺-ext; ≼-split)
open import denotation.Laws.Cut using (ix-asc)
open import denotation.Laws.Worlds using (⊕-assoc; ⊕-identityʳ; Lawful)
open import denotation.Laws.Worlds.Leaves using (of-reach; of-end; of-idx)
open import simultaneous.TakeKit using (ix<last)
open import simultaneous.SObs using (lone; module Elaborate; Branch; outerB; laneB; closeB)
open import simultaneous.HeldComb using (ev)
open import simultaneous.DenRows using (merge-out; bounded-out; map-out′; of-mem; each-one; nth-row; module Cat)
open import simultaneous.InstEmit using (instEmit; value; mark; outerClose; outerDone)
open import Data.List.Relation.Unary.All using (lookup)
import Data.List.Relation.Unary.All as All

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (E; IE; Routes; Input; going; fed; branch; closer; closing; marked; each)

-- A takeWhile that never includes its failure keeps a value where it was.
take-at : ∀ {X} (keep : X → Bool) (d : Den X) p {k y} → enter (Op.takeWhile false keep d) p k (out y) → enter d p k (out y)
take-at keep d p (TakeWhile.pass t _ _ , _) = t
take-at keep d p (TakeWhile.fail _ _ _ () , _)

module _ {Δ A B} (tk : E (IE B ∷ IE B ∷ IE A ∷ Δ) (ℕ × Routes)) (env : DenEnv (IE B ∷ IE B ∷ IE A ∷ Δ)) where

  Fed : E (IE B ∷ IE B ∷ IE A ∷ Δ) (Maybe (Input B))
  Fed = flatMap (mergeᶠ nothing) (fed tk) (of (true ∷ false ∷ []))

  Src : E (IE B ∷ IE B ∷ IE A ∷ Δ) (Maybe (Input B))
  Src = takeWhile false going Fed

  -- The flatMap's own branches, each tagged.
  Tag : Branch → E (IE B ∷ IE B ∷ IE A ∷ Δ) (Maybe (Input B))
  Tag b = map (λ e → just (inj₁ (b , e))) (branch b)

  Own : E (IE B ∷ IE B ∷ IE A ∷ Δ) (Maybe (Input B))
  Own = flatMap (mergeᶠ nothing) Tag (of (outerB ∷ laneB ∷ closeB ∷ []))

  Cat-of : Bool → E (IE B ∷ IE B ∷ IE A ∷ Δ) (Maybe (Input B))
  Cat-of c = if c then Own else of (nothing ∷ [])

  -- A branch reads a hot, under every approximant as under the meaning.
  branch-ev : ∀ m b {s q y} → enter (ev m (branch {A = A} {B} b) env) s q y → enter (⟦ branch b ⟧ env) s q y
  branch-ev nothing  b      r = r
  branch-ev (just n) outerB r = r
  branch-ev (just n) laneB  r = r
  branch-ev (just n) closeB r = r

  -- A branch's row the source sends is the branch's, at the same row.
  sent-branch : ∀ m P {q b y} → enter (ev m Src env) P q (out (just (inj₁ (b , y))))
              → Σ Pos λ s → enter (⟦ branch b ⟧ env) s q (out y)
  sent-branch nothing P r with merge-out (λ a → ⟦ fed tk a ⟧ env) (Op.of (true ∷ false ∷ [])) P (take-at going (⟦ Fed ⟧ env) P r)
  ... | _ , true , _ , l , _ with map-out′ _ (⟦ tk ⟧ env) _ l
  ...   | _ , _ , ()
  sent-branch nothing P r | _ , false , _ , l , _ with Cat.cat-out (λ c → ⟦ Cat-of c ⟧ env) _ l
  ... | inj₂ (_ , l′) with of-mem _ 0 (nothing ∷ []) (proj₁ l′)
  ...   | here ()
  ...   | there ()
  sent-branch nothing P r | _ , false , _ , l , _ | inj₁ l′ with merge-out (λ b → ⟦ Tag b ⟧ env) (Op.of (outerB ∷ laneB ∷ closeB ∷ [])) _ l′
  ... | _ , b′ , _ , l″ , _ with map-out′ (λ e → just (inj₁ (b′ , e))) (⟦ branch b′ ⟧ env) _ l″
  ...   | _ , l‴ , refl = _ , l‴
  sent-branch (just n) P r with merge-out (λ a → approx n (fed tk a) env) (Op.of (true ∷ false ∷ [])) P (take-at going (approx n Fed env) P r)
  ... | _ , true , _ , l , _ with map-out′ _ (approx n tk env) _ l
  ...   | _ , _ , ()
  sent-branch (just n) P r | _ , false , _ , l , _ with Cat.cat-out (λ c → approx n (Cat-of c) env) _ l
  ... | inj₂ (_ , l′) with of-mem _ 0 (nothing ∷ []) (proj₁ l′)
  ...   | here ()
  ...   | there ()
  sent-branch (just n) P r | _ , false , _ , l , _ | inj₁ l′ with merge-out (λ b → approx n (Tag b) env) (Op.of (outerB ∷ laneB ∷ closeB ∷ [])) _ l′
  ... | _ , b′ , _ , l″ , _ with map-out′ (λ e → just (inj₁ (b′ , e))) (approx n (branch b′) env) _ l″
  ...   | _ , l‴ , refl = _ , branch-ev (just n) b′ l‴

  -- THE SOURCE AS OPERATORS, level by level, under every approximant as
  -- under the meaning: nothing under it is deferred.
  src-op : ∀ m → ev m Src env ≡ Op.takeWhile false going (Op.flatMap (mergeᶠ nothing) (λ b → ev m (fed tk b) env) (Op.of (true ∷ false ∷ [])))
  src-op nothing  = refl
  src-op (just n) = refl

  own-op : ∀ m → ev m (fed tk false) env ≡ Op.flatMap (mergeᶠ (just 1)) (λ c → ev m (Cat-of c) env) (Op.of (true ∷ false ∷ []))
  own-op nothing  = refl
  own-op (just n) = refl

  cat-op : ∀ m → ev m (Cat-of true) env ≡ Op.flatMap (mergeᶠ nothing) (λ b → ev m (Tag b) env) (Op.of (outerB ∷ laneB ∷ closeB ∷ []))
  cat-op nothing  = refl
  cat-op (just n) = refl

  tag-op : ∀ m → ev m (Tag laneB) env ≡ Op.map (λ e → just (inj₁ (laneB , e))) (lookup env (here refl))
  tag-op nothing  = refl
  tag-op (just n) = refl

  -- The trackers send no branch's row.
  no-track : ∀ m {s k x} → enter (ev m (fed tk true) env) s k (out (just (inj₁ x))) → ⊥
  no-track nothing  r with map-out′ _ (⟦ tk ⟧ env) _ r
  ... | _ , _ , ()
  no-track (just n) r with map-out′ _ (approx n tk env) _ r
  ... | _ , _ , ()

  -- The closing item is `nothing`.
  no-close : ∀ m {s k y} → enter (ev m (Cat-of false) env) s k (out (just y)) → ⊥
  no-close nothing  {s} r with of-mem s 0 (nothing ∷ []) (proj₁ r)
  ... | there ()
  no-close (just n) {s} r with of-mem s 0 (nothing ∷ []) (proj₁ r)
  ... | there ()

  -- A branch's tagged row names that branch.
  tag-branch : ∀ m b {s k b′ x} → enter (ev m (Tag b) env) s k (out (just (inj₁ (b′ , x)))) → b ≡ b′
  tag-branch nothing  b r with map-out′ (λ e → just (inj₁ (b , e))) (⟦ branch b ⟧ env) _ r
  ... | _ , _ , refl = refl
  tag-branch (just n) b r with map-out′ (λ e → just (inj₁ (b , e))) (approx n (branch b) env) _ r
  ... | _ , _ , refl = refl

-- What the closer sends: a bracket's close, then the outer's end.
data Closing {B : Set} : IE B → Set where
  c-close : ∀ {n} → Closing (instEmit (mark outerClose) n)
  c-done  : ∀ {n} → Closing (instEmit (mark outerDone) n)

closing-mark : ∀ {B} {m n} → Closing {B} (instEmit (mark m) n) → (m ≡ outerClose → ⊥) → (m ≡ outerDone → ⊥) → ⊥
closing-mark c-close a _ = a refl
closing-mark c-done  _ b = b refl

closing-value : ∀ {B} {a n} → Closing {B} (instEmit (value a) n) → ⊥
closing-value ()

closer-marks : ∀ m {Δ A B} (env : DenEnv (IE A ∷ Δ)) s {q x} → enter (ev m (closer {Δ} {A} {B}) env) s q (out x) → Closing x
closer-marks nothing env s r with Cat.cat-out _ s r
... | inj₁ l with each-one closing (lookup env (here refl)) _ l
...   | _ , instEmit (value _) _ , _ , here refl = c-close
...   | _ , instEmit (value _) _ , _ , there ()
...   | _ , instEmit (mark _) _ , _ , ()
closer-marks nothing env s r | inj₂ (_ , l) with of-mem _ 0 (marked outerDone ∷ []) (proj₁ l)
... | here refl = c-done
... | there ()
closer-marks (just n) env s r with Cat.cat-out _ s r
... | inj₁ l with each-one closing (lookup env (here refl)) _ l
...   | _ , instEmit (value _) _ , _ , here refl = c-close
...   | _ , instEmit (value _) _ , _ , there ()
...   | _ , instEmit (mark _) _ , _ , ()
closer-marks (just n) env s r | inj₂ (_ , l) with of-mem _ 0 (marked outerDone ∷ []) (proj₁ l)
... | here refl = c-done
... | there ()

------------------------------------------------------------------------
-- Where the source ends

-- A row of an `of`, one label down.
of-at : ∀ {X} p i (xs : List X) {y e} → InE (ofᴱ p i xs) y e → Σ Label λ l → y ≡ p ⊕ [ l ]
of-at p i xs x with of-idx p i xs x
... | inj₁ (j , _ , eq) = ix j , eq
... | inj₂ eq           = last , eq

-- Below its end, a row waits on no more than the end does.
reach-below : ∀ {X} {t : EmissionSet X} {c k a} → Reach t c end → k ≺ c → Reach t k (out a)
reach-below {c = c} {k} (ks , h) kc = ks , λ {k′} x k′k _ → h x (≺-trans {k′} {k} {c} k′k kc) tt

-- A lane a bounded merge schedules starts past its value.
starts-after : ∀ {X Y : Set} {n} {f : X → Den Y} {o : EmissionSet X} {i q ls s} → Bounded.Starts n f o i q ls s → q ≺ s
starts-after {q = q} (Bounded.room _)               = ≺-ext q []
starts-after {q = q} (Bounded.freed _ _)            = ≺-ext q []
starts-after {q = q} (Bounded.queued {c} _ qc _ _ _) = ≺-trans {q} {c} {c ⊕ [ ix 1 ]} qc (≺-ext c [])

-- Two values, the second one index in.
module Two {X : Set} (x y : X) (p : Pos) where

  O : EmissionSet X
  O = enter (Op.of (x ∷ y ∷ [])) p

  snd-row : O (p ⊕ [ ix 1 ]) (out y)
  snd-row = on-out at-out , of-reach p 0 (x ∷ y ∷ []) {p ⊕ [ ix 1 ]} {out y}

  snd-before : ∀ {c} → Ended O c → (p ⊕ [ ix 1 ]) ≺ c
  snd-before {c} (c′ , (e , _) , c′c) with of-end p 0 (x ∷ y ∷ []) e
  ... | refl = ≺-≼-≺ {p ⊕ [ ix 1 ]} {p ⊕ [ last ]} {c} (Equivalence.from T-≡ (<ᵖ-part p [] [] refl)) c′c

  snd-nth : Values.Nth O 1 (p ⊕ [ ix 1 ]) y
  snd-nth = Values.next (Values.first (at-out , of-reach p 0 (x ∷ y ∷ []) {p ⊕ [ ix 0 ]} {out x}) lo) snd-row (ix-asc p (s≤s z≤n)) nx
    where
      lo : ∀ {k b} → O k (out b) → (p ⊕ [ ix 0 ]) ≼ k
      lo (at-out , _)              = ≼-refl {p ⊕ [ ix 0 ]}
      lo (on-out at-out , _)       = ≺→≼ {p ⊕ [ ix 0 ]} {p ⊕ [ ix 1 ]} (ix-asc p (s≤s z≤n))
      lo (on-out (on-out ()) , _)

      nx : ∀ {k b} → O k (out b) → (p ⊕ [ ix 0 ]) ≺ k → (p ⊕ [ ix 1 ]) ≼ k
      nx (at-out , _) lt          = ⊥-elim (≺-irrefl {p ⊕ [ ix 0 ]} lt)
      nx (on-out at-out , _) _    = ≼-refl {p ⊕ [ ix 1 ]}
      nx (on-out (on-out ()) , _) _

-- WHERE A ROW OF THE SOURCE LIES: under its subscription, or past a
-- branch's end, that branch's reader itself so placed.
data Where {Y : Set} (P : Pos) (Br : Branch → Den Y) : Pos → Set where
  under : ∀ zs → Where P Br (P ⊕ zs)
  past  : ∀ {b w c} zs → Where P Br w → enter (Br b) w c end → Where P Br (c ⊕ zs)

where-ext : ∀ {Y P} {Br : Branch → Den Y} {c} → Where P Br c → ∀ ys → Where P Br (c ⊕ ys)
where-ext {P = P} {Br} (under zs) ys = subst (Where P Br) (sym (⊕-assoc P zs ys)) (under (zs ++ ys))
where-ext {P = P} {Br} (past {c = c} zs w x) ys = subst (Where P Br) (sym (⊕-assoc c zs ys)) (past (zs ++ ys) w x)

where-at : ∀ {Y P} {Br : Branch → Den Y} → Where P Br P
where-at {P = P} {Br} = subst (Where P Br) (⊕-identityʳ P) (under [])

where-map : ∀ {Y P} {Br Br′ : Branch → Den Y} → (∀ b {w c} → enter (Br b) w c end → enter (Br′ b) w c end)
          → ∀ {c} → Where P Br c → Where P Br′ c
where-map g (under zs)    = under zs
where-map g (past zs w x) = past zs (where-map g w) (g _ x)

-- THE CONCAT'S END KEEPS what its subscription and its lanes' ends keep,
-- for a property every extension keeps: each lane's end lies where its
-- start does, and a start where its value or the end that frees it does.
module CatGood {X : Set} (G : Bool → Den X) (Good : Pos → Set) (ext : ∀ {c} → Good c → ∀ zs → Good (c ⊕ zs))
               (lane-good : ∀ a {s c} → Good s → enter (G a) s c end → Good c) (s₀ : Pos) (g₀ : Good s₀) where
  private
    module Bd = Bounded 1 G (enter (Op.of (true ∷ false ∷ [])) s₀)

  outer-good : ∀ {q a} → enter (Op.of (true ∷ false ∷ [])) s₀ q (out a) → Good q
  outer-good (x , _) with of-at s₀ 0 _ x
  ... | l , refl = ext g₀ [ l ]

  mutual
    lane-end : ∀ i {q a s c} → Values.Nth (enter (Op.of (true ∷ false ∷ [])) s₀) i q a → Bd.Starts i q (Bd.Sched i) s
             → After (G a) s c end → Good c
    lane-end i nt st (x , _) = lane-good _ (starts i st (outer-good (nth-row nt))) x

    starts : ∀ i {q s} → Bd.Starts i q (Bd.Sched i) s → Good q → Good s
    starts i (Bd.room _)           gq = ext gq [ ix 1 ]
    starts i (Bd.freed _ _)        gq = ext gq [ ix 1 ]
    starts i (Bd.queued _ _ k _ _) gq = ext (sched i k) [ ix 1 ]

    sched : ∀ i {c} → Bd.Kth (_≡ c) (Bd.Sched i) 0 → Good c
    sched zero ()
    sched (suc i) (inj₁ (_ , (_ , _ , _ , nt , st , aft) , refl)) = lane-end i nt st aft
    sched (suc i) (inj₂ k) = sched i k

  cat-end : ∀ {c} → enter (Op.flatMap (mergeᶠ (just 1)) G (Op.of (true ∷ false ∷ []))) s₀ c end → Good c
  cat-end (Bd.oend o _ , _) with of-end s₀ 0 (true ∷ false ∷ []) (proj₁ o)
  ... | refl = ext g₀ [ last ]
  cat-end (Bd.lane _ _ _ _ () , _)
  cat-end (Bd.lend _ _ (i , _ , (nt , st) , aft) _ _ _ , _) = lane-end i nt st aft
  cat-end (Bd.run () _ , _)
  cat-end (Bd.rend () _ _ , _)

assoc³ : ∀ r a b c → ((r ⊕ [ a ]) ⊕ [ b ]) ⊕ [ c ] ≡ r ⊕ (a ∷ b ∷ c ∷ [])
assoc³ r a b c = trans (cong (_⊕ [ c ]) (⊕-assoc r [ a ] [ b ])) (⊕-assoc r (a ∷ b ∷ []) [ c ])

-- AN `each` OVER A LAWFUL HOT ENDS where the hot does, or where it is
-- subscribed: no row lies under another, so a lane of a row before the
-- hot's end ends before it too.
module EachEnd {X Y : Set} (g : X → List Y) (t : EmissionSet X) (L : Lawful t) (Good : Pos → Set)
               (ext : ∀ {c} → Good c → ∀ zs → Good (c ⊕ zs)) (t-end : ∀ {c} → t c end → Good c) (s : Pos) (gs : Good s) where
  private
    module Mg = Merge (λ x → Op.of (g x)) (enter (hot t) s)

  under-before : ∀ {r c a} → t r (out a) → t c end → ∀ zs → (r ⊕ zs) ≺ c
  under-before {r} {c} x y zs = Equivalence.from T-≡ (<ᵖ-apart r c zs (Equivalence.to T-≡ r≺c) apart)
    where
      r≺c : r ≺ c
      r≺c with ≼-split {r} {c} (Lawful.proper L y x)
      ... | inj₁ lt = lt
      ... | inj₂ refl with () ← Lawful.func L x y
      apart : ∀ ys → c ≡ r ⊕ ys → ⊥
      apart []       eq   = ≺-irrefl {r} (subst (r ≺_) (trans eq (⊕-identityʳ r)) r≺c)
      apart (l ∷ ys) refl = Lawful.flat L x y

  lane-past : ∀ {r a c₀} → t r (out a) → s ≺ r → Rejoin s t c₀ end → c₀ ≼ (((r ⊕ [ sub s ]) ⊕ [ ix 1 ]) ⊕ [ last ]) → ⊥
  lane-past {r} x _ (ended {e} y _) c₀c =
    c₀c (≺-trans {((r ⊕ [ sub s ]) ⊕ [ ix 1 ]) ⊕ [ last ]} {e} {e ⊕ [ sub s ]}
          (subst (_≺ e) (sym (assoc³ r (sub s) (ix 1) last)) (under-before x y (sub s ∷ ix 1 ∷ last ∷ []))) (≺-ext e []))
  lane-past {r} x sr (late {e} y es) _ = es (≺-≼-≺ {s} {r} {e} sr (Lawful.proper L y x))
  lane-past x _ (shown _ () _) _

  each-end : ∀ {c} → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (g x)) (hot t)) s c end → Good c
  each-end (Mg.oend (ended y _ , _) _ , _) = ext (t-end y) [ sub s ]
  each-end (Mg.oend (late _ _ , _) _ , _)  = ext gs [ last ]
  each-end (Mg.oend (shown _ () _ , _) _ , _)
  each-end (Mg.lane _ _ _ _ () , _)
  each-end (Mg.lend {q} {a} (shown x _ sr , _) _ (l , _) _ _ ((_ , (rj , _) , c₀c) , _) , _)
    with of-end (q ⊕ [ ix 1 ]) 0 (g a) (proj₁ l)
  ... | refl = ⊥-elim (lane-past x sr rj c₀c)
  each-end (Mg.run () _ , _)
  each-end (Mg.rend () _ _ , _)

-- The closer's two lanes.
Clo : ∀ {Δ A B} → Bool → E (IE A ∷ Δ) (IE B)
Clo b = if b then each closing (connected (here refl)) else of (marked outerDone ∷ [])

-- THE CLOSER ENDS where its subscription or the end of the hot it reads
-- keeps, under every approximant as under the meaning.
closer-good : ∀ m {Δ A B} (t : EmissionSet (IE A)) (env : DenEnv Δ) → Lawful t → (Good : Pos → Set)
            → (∀ {c} → Good c → ∀ zs → Good (c ⊕ zs)) → (∀ {c} → t c end → Good c)
            → ∀ s → Good s → ∀ {c} → enter (ev m (closer {Δ} {A} {B}) (hot t All.∷ env)) s c end → Good c
closer-good nothing {Δ} {A} {B} t env L Good ext t-end s gs x =
  CatGood.cat-end (λ b → ⟦ Clo {Δ} {A} {B} b ⟧ (hot t All.∷ env)) Good ext lane s gs x
  where
    lane : ∀ a {s c} → Good s → enter (⟦ Clo {Δ} {A} {B} a ⟧ (hot t All.∷ env)) s c end → Good c
    lane true  {s} gs x = EachEnd.each-end closing t L Good ext t-end s gs x
    lane false {s} gs x with of-end s 0 (marked outerDone ∷ []) (proj₁ x)
    ... | refl = ext gs [ last ]
closer-good (just n) {Δ} {A} {B} t env L Good ext t-end s gs x =
  CatGood.cat-end (λ b → approx n (Clo {Δ} {A} {B} b) (hot t All.∷ env)) Good ext lane s gs x
  where
    lane : ∀ a {s c} → Good s → enter (approx n (Clo {Δ} {A} {B} a) (hot t All.∷ env)) s c end → Good c
    lane true  {s} gs x = EachEnd.each-end closing t L Good ext t-end s gs x
    lane false {s} gs x with of-end s 0 (marked outerDone ∷ []) (proj₁ x)
    ... | refl = ext gs [ last ]

-- THE SOURCE'S PIECES, as any reading of it gives them: the trackers
-- `Tk`, the flatMap's own branches `Br`, tagged by `T`, concatenated with
-- the closing `nothing` by `G`, fed beside the trackers by `F`.
module SrcEnd {B : Set} (F G : Bool → Den (Maybe (Input B))) (T : Branch → Den (Maybe (Input B)))
              (Br : Branch → Den (IE B)) (Tk : Den (ℕ × Routes)) (P : Pos)
              (eFt : F true ≡ Op.map (λ x → just (inj₂ x)) Tk)
              (eF : F false ≡ Op.flatMap (mergeᶠ (just 1)) G (Op.of (true ∷ false ∷ [])))
              (eG : G false ≡ Op.of (nothing ∷ []))
              (eT : G true ≡ Op.flatMap (mergeᶠ nothing) T (Op.of (outerB ∷ laneB ∷ closeB ∷ [])))
              (eB : ∀ b → T b ≡ Op.map (λ e → just (inj₁ (b , e))) (Br b)) where

  D : Den (Maybe (Input B))
  D = Op.flatMap (mergeᶠ nothing) F (Op.of (true ∷ false ∷ []))

  W : Pos → Set
  W = Where P Br

  -- The branches' merge ends at its outer's end, or past a branch's.
  own-end : ∀ {s c} → W s → enter (G true) s c end → W c
  own-end {s} {c} ws x with subst (λ d → enter d s c end) eT x
  ... | (Merge.oend o _ , _) with of-end s 0 (outerB ∷ laneB ∷ closeB ∷ []) (proj₁ o)
  ...   | refl = where-ext ws [ last ]
  own-end {s} {c} ws x | (Merge.lane _ _ _ _ () , _)
  own-end {s} {c} ws x | (Merge.lend {q} {b} o _ (l , _) _ _ _ , _) with of-at s 0 (outerB ∷ laneB ∷ closeB ∷ []) (proj₁ o)
  ... | l₀ , refl with subst (λ d → enter d (q ⊕ [ ix 1 ]) c end) (eB b) l
  ...   | (map-end br , _) = subst W (⊕-identityʳ c) (past [] (where-ext ws (l₀ ∷ ix 1 ∷ [])) (subst (λ w → enter (Br b) w c end) (⊕-assoc s [ l₀ ] [ ix 1 ]) br))
  own-end {s} {c} ws x | (Merge.run () _ , _)
  own-end {s} {c} ws x | (Merge.rend () _ _ , _)

  -- A lane of the concat ends where its start does.
  lane-w : ∀ a {s c} → W s → enter (G a) s c end → W c
  lane-w true  ws x = own-end ws x
  lane-w false {s} {c} ws x with of-end s 0 (nothing ∷ []) (proj₁ (subst (λ d → enter d s c end) eG x))
  ... | refl = where-ext ws [ last ]

  module CatAt (s₀ : Pos) (w₀ : W s₀) = CatGood G W (λ w zs → where-ext w zs) lane-w s₀ w₀

  -- The closing `nothing` lies under the subscription or past a branch's end.
  nothing-at : ∀ {k} → enter D P k (out nothing) → W k
  nothing-at r with merge-out F (Op.of (true ∷ false ∷ [])) P r
  ... | q , true , _ , l , _ with map-out′ (λ x → just (inj₂ x)) Tk _ (subst (λ d → enter d _ _ (out nothing)) eFt l)
  ...   | _ , _ , ()
  nothing-at r | q , false , oq , l , _ with bounded-out 1 G (Op.of (true ∷ false ∷ [])) _ (subst (λ d → enter d _ _ (out nothing)) eF l)
  ... | q₂ , true , i , s , oq₂ , sb , (l′ , _) with merge-out T (Op.of (outerB ∷ laneB ∷ closeB ∷ [])) s (subst (λ d → enter d _ _ (out nothing)) eT l′)
  ...   | _ , b , _ , l″ , _ with map-out′ (λ e → just (inj₁ (b , e))) (Br b) _ (subst (λ d → enter d _ _ (out nothing)) (eB b) l″)
  ...     | _ , _ , ()
  nothing-at r | q , false , oq , l , _ | q₂ , false , i , s , oq₂ , (nt , st) , (l′ , _)
    with of-at s 0 (nothing ∷ []) (proj₁ (subst (λ d → enter d _ _ (out nothing)) eG l′))
  ... | l₀ , refl = where-ext (CatAt.starts (q ⊕ [ ix 1 ]) wq i st (CatAt.outer-good (q ⊕ [ ix 1 ]) wq oq₂)) [ l₀ ]
    where
      wq : W (q ⊕ [ ix 1 ])
      wq = where-ext (CatAt.outer-good P where-at oq) [ ix 1 ]

  private
    module Mg = Merge F (enter (Op.of (true ∷ false ∷ [])) P)

    sc : Pos
    sc = (P ⊕ [ ix 1 ]) ⊕ [ ix 1 ]

    module Bc = Bounded 1 G (enter (Op.of (true ∷ false ∷ [])) sc)

    mg-done : ∀ {c} → Mg.JoinT c end → Mg.Done c
    mg-done (Mg.oend _ d)         = d
    mg-done (Mg.lane _ _ _ _ ())
    mg-done (Mg.lend _ _ _ _ _ d) = d
    mg-done (Mg.run () _)
    mg-done (Mg.rend () _ _)

    bc-done : ∀ {c} → Bc.JoinT c end → Bc.Done c
    bc-done (Bc.oend _ d)         = d
    bc-done (Bc.lane _ _ _ _ ())
    bc-done (Bc.lend _ _ _ _ _ d) = d
    bc-done (Bc.run () _)
    bc-done (Bc.rend () _ _)

  -- THE SOURCE'S MERGE NEVER ENDS BEFORE ITS `nothing`: its end waits on
  -- the concat, and the concat's on the `nothing`'s lane.
  failed : ∀ {c} → enter D P c end → TakeWhile.Failed false going (enter D P) c
  failed {c} (x , rc) =
    from-lane (proj₂ (mg-done x) (Two.snd-row true false P) tt (Two.snd-before true false P (proj₁ (mg-done x))) (λ ()))
    where
      from-lane : Ended (LaneOf F (P ⊕ [ ix 1 ]) false) c → TakeWhile.Failed false going (enter D P) c
      from-lane (c₀ , (cr , _) , c₀c) = from-cat (subst (λ d → enter d sc c₀ end) eF cr)
        where
          from-cat : enter (Op.flatMap (mergeᶠ (just 1)) G (Op.of (true ∷ false ∷ []))) sc c₀ end → TakeWhile.Failed false going (enter D P) c
          from-cat (y , ry) =
            from-of (proj₂ (bc-done y) (Two.snd-row true false sc) (1 , false , Two.snd-nth true false sc)
                      (Two.snd-before true false sc (proj₁ (bc-done y))) (λ ()))
            where
              from-of : Ended (Bc.Lane (sc ⊕ [ ix 1 ]) false) c₀ → TakeWhile.Failed false going (enter D P) c
              from-of (c₁ , (i , s , (nt , st) , er , _) , c₁c₀) with of-end s 0 (nothing ∷ []) (proj₁ (subst (λ d → enter d s c₁ end) eG er))
              ... | refl = s ⊕ [ ix 0 ] , nothing , (frow , reach-below {a = nothing} rc k≺c) , tt , k≺c
                where
                  k≺c₀ : (s ⊕ [ ix 0 ]) ≺ c₀
                  k≺c₀ = ≺-≼-≺ {s ⊕ [ ix 0 ]} {s ⊕ [ last ]} {c₀} (ix<last s) c₁c₀

                  k≺c : (s ⊕ [ ix 0 ]) ≺ c
                  k≺c = ≺-≼-≺ {s ⊕ [ ix 0 ]} {c₀} {c} k≺c₀ c₀c

                  nrow : enter (G false) s (s ⊕ [ ix 0 ]) (out nothing)
                  nrow = subst (λ d → enter d s (s ⊕ [ ix 0 ]) (out nothing)) (sym eG) (at-out , of-reach s 0 (nothing ∷ []) {s ⊕ [ ix 0 ]} {out nothing})

                  crow : enter (F false) sc (s ⊕ [ ix 0 ]) (out nothing)
                  crow = subst (λ d → enter d sc (s ⊕ [ ix 0 ]) (out nothing)) (sym eF)
                           (Bc.lane (nth-row nt) (i , false , nt) (i , s , (nt , st) , nrow , ≺-ext s []) (λ ()) tt , reach-below {a = nothing} ry k≺c₀)

                  sc≺k : sc ≺ (s ⊕ [ ix 0 ])
                  sc≺k = ≺-trans {sc} {sc ⊕ [ ix 1 ]} {s ⊕ [ ix 0 ]} (≺-ext sc [])
                           (≺-trans {sc ⊕ [ ix 1 ]} {s} {s ⊕ [ ix 0 ]} (starts-after st) (≺-ext s []))

                  frow : Mg.JoinT (s ⊕ [ ix 0 ]) (out nothing)
                  frow = Mg.lane (Two.snd-row true false P) tt (crow , sc≺k) (λ ()) tt

  -- The source ends past its `nothing`, never at its merge's end.
  src-end : ∀ {c} → enter (Op.takeWhile false going D) P c end → W c
  src-end (TakeWhile.stop {a = just _} _ () _ , _)
  src-end (TakeWhile.stop {a = nothing} x _ _ , _) = where-ext (nothing-at x) [ last ]
  src-end (TakeWhile.tend x nF , _)                = ⊥-elim (nF (failed x))

module _ {Δ A B} (tk : E (IE B ∷ IE B ∷ IE A ∷ Δ) (ℕ × Routes)) (env : DenEnv (IE B ∷ IE B ∷ IE A ∷ Δ)) where

  -- Where the scan's source ends, under every approximant as under the meaning.
  src-where : ∀ m P {c} → enter (ev m (Src tk env) env) P c end → Where P (λ b → ⟦ branch {A = A} {B} b ⟧ env) c
  src-where nothing P x =
    SrcEnd.src-end (λ a → ⟦ fed tk a ⟧ env) (λ a → ⟦ Cat-of tk env a ⟧ env) (λ b → ⟦ Tag tk env b ⟧ env)
      (λ b → ⟦ branch b ⟧ env) (⟦ tk ⟧ env) P refl refl refl refl (λ _ → refl) x
  src-where (just n) P x = where-map (λ b → branch-ev tk env (just n) b)
    (SrcEnd.src-end (λ a → approx n (fed tk a) env) (λ a → approx n (Cat-of tk env a) env) (λ b → approx n (Tag tk env b) env)
      (λ b → approx n (branch b) env) (approx n tk env) P refl refl refl refl (λ _ → refl) x)
