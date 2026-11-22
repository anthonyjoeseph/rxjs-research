{-# OPTIONS --guardedness #-}

-- A MERGE OF CLOSED LANES IS ITS SOURCE'S LANES IN TURN.  Each value's
-- lane is met to its end before the next source row, so a source run
-- read lane by lane, each lane by a run met of it, is the merge's run;
-- and a merge run is one read off the source run reaching the source row
-- its last row hangs under.  Generic in the lanes, which give their run
-- and their rows; and in the source, which gives only that it is a
-- function with no row under another and nothing but pins past its end.
module simultaneous.FlatLayer where

open import Data.List using (List; []; _∷_; concatMap; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-concatMap⁺; ∈-++⁺ʳ; ∈-++⁺ˡ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there) renaming (map to any-map)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)

open import Tree using (mergeᶠ)
open import denotation.Position using (Pos; Path; Label; ix; last; _⊕_)
open import denotation.Events using (ofᴱ; <ᵖ-apart; <ᵖ-between; <ᵖ-part; ix-<)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; skip; pin; _≺_; _≼_; enter; Den; module Op; InE;
  at-out; on-out; at-end; Seen; Reach; Dep; Ended; LaneOf; module Merge; module Scan)
open import denotation.Read using (Run; []; _∷_; Visible; After; cursor)
open import denotation.Laws.Worlds using (PinBy; ⊕-assoc; ⊕-identityʳ; ⊕-cancelˡ)
open import denotation.Laws.Worlds.Leaves using (of-end; of-idx; of-reach; of-func; of-end-row; of-rows; of-in; module AccF)
open import denotation.Laws.Modulus using (≼-split; entered-few; ≺-irrefl; ≺-absurd; ≼-refl; ≺→≼; ≺-≼-≺; ≼-trans; ≼-or-≻; ≺-ext)
open import adequacy.SubOne using (lift-in)
open import simultaneous.Relations using (Met)
open import simultaneous.Layers using (to≺; from≺; pinby-vis; after-≺; run-row; run-has; run-det; run-++; run-tail; run-after;
  run-past-end; cursor-++; cursor-snoc; prefix-split; last-in; snoc≢[])

------------------------------------------------------------------------
-- An `of`

-- An `of`'s values, each at its index.
ofVals : ∀ {A : Set} → Pos → ℕ → List A → List (Pos × Ev A)
ofVals p i []       = []
ofVals p i (x ∷ xs) = (p ⊕ [ ix i ] , out x) ∷ ofVals p (suc i) xs

-- AN `of` IS MET IN ORDER: each index the least past the one before.
module OfMet {A : Set} (p : Pos) (xs₀ : List A) where
  O : EmissionSet A
  O = enter (Op.of xs₀) p

  in-rest : ∀ i (xs : List A) {k e} → InE (ofᴱ p (suc i) xs) k e → (p ⊕ [ ix i ]) ≺ k
  in-rest i xs y with of-idx p (suc i) xs y
  ... | inj₁ (j , le , refl) = to≺ (p ⊕ [ ix i ]) (p ⊕ [ ix j ]) (<ᵖ-part p {ix i} {ix j} [] [] (ix-< le))
  ... | inj₂ refl            = to≺ (p ⊕ [ ix i ]) (p ⊕ [ last ]) (<ᵖ-part p {ix i} {last} [] [] refl)

  row : ∀ {k e} → InE (ofᴱ p 0 xs₀) k e → O k e
  row r = r , of-reach p 0 xs₀

  prop : ∀ {k e} → InE (ofᴱ p 0 xs₀) k e → ∀ {c} → O c end → k ≼ c
  prop r (ce , _) with of-end p 0 xs₀ ce | of-idx p 0 xs₀ r
  ... | refl | inj₁ (j , _ , refl) = ≺→≼ {p ⊕ [ ix j ]} {p ⊕ [ last ]} (to≺ (p ⊕ [ ix j ]) (p ⊕ [ last ]) (<ᵖ-part p {ix j} {last} [] [] refl))
  ... | refl | inj₂ refl           = ≼-refl {p ⊕ [ last ]}

  go : ∀ {c} i (xs : List A) → (∀ {k e} → InE (ofᴱ p i xs) k e → InE (ofᴱ p 0 xs₀) k e)
     → (∀ {k e} → O k e → Visible e → After c k → InE (ofᴱ p i xs) k e)
     → (∀ {k e} → InE (ofᴱ p i xs) k e → After c k)
     → Run O c (ofVals p i xs ++ [ (p ⊕ [ last ] , end) ])
  go {c} i [] emb j₁ j₂ = (((row (emb at-end) , prop (emb at-end)) , entered-few (Op.of xs₀) p tt (row (emb at-end))) , tt , j₂ at-end , mn) ∷ []
    where
      mn : ∀ {k e} → O k e → Visible e → After c k → (p ⊕ [ last ]) ≼ k
      mn y vi ak with j₁ y vi ak
      ... | at-end = ≼-refl {p ⊕ [ last ]}
  go {c} i (x ∷ xs) emb j₁ j₂ =
    (((row (emb at-out) , prop (emb at-out)) , entered-few (Op.of xs₀) p tt (row (emb at-out))) , tt , j₂ at-out , mn) ∷
    go (suc i) xs (λ r → emb (on-out r)) j₁′ (in-rest i xs)
    where
      k₀ = p ⊕ [ ix i ]
      mn : ∀ {k e} → O k e → Visible e → After c k → k₀ ≼ k
      mn y vi ak with j₁ y vi ak
      ... | at-out   = ≼-refl {k₀}
      ... | on-out r = ≺→≼ {k₀} {_} (in-rest i xs r)
      j₁′ : ∀ {k e} → O k e → Visible e → After (just k₀) k → InE (ofᴱ p (suc i) xs) k e
      j₁′ y vi ak with j₁ y vi (after-≺ c (j₂ at-out) ak)
      ... | at-out   = ⊥-elim (≺-irrefl {k₀} ak)
      ... | on-out r = r

  of-met : Met O (ofVals p 0 xs₀ ++ [ (p ⊕ [ last ] , end) ])
  of-met = go 0 xs₀ (λ r → r) (λ y _ _ → proj₁ y) (λ _ → tt)

  -- Each row lies one label below.
  of-lab : ∀ {k e} → InE (ofᴱ p 0 xs₀) k e → Σ Label λ x → k ≡ p ⊕ [ x ]
  of-lab r with of-idx p 0 xs₀ r
  ... | inj₁ (j , _ , eq) = ix j , eq
  ... | inj₂ eq           = last , eq

  -- One event at a position, none under another, nothing past the end.
  o-fu : ∀ {y e e′} → O y e → O y e′ → e ≡ e′
  o-fu (r , _) (r′ , _) = of-func p 0 xs₀ r r′

  o-flat : ∀ {y e l ys e′} → O y e → O (y ⊕ (l ∷ ys)) e′ → ⊥
  o-flat {l = l} {ys} (r , _) (r′ , _) with of-lab r
  ... | x , refl with of-lab r′
  ...   | x′ , eq with ⊕-cancelˡ p (x ∷ l ∷ ys) [ x′ ] (trans (sym (⊕-assoc p [ x ] (l ∷ ys))) eq)
  ...     | ()

  o-quiet : ∀ {c y e} → O c end → O y e → c ≺ y → PinBy c e
  o-quiet c (r , _) cy = ⊥-elim (prop r c cy)

  -- A value lies before the end.
  of-past : ∀ {k b} → O k (out b) → k ≺ (p ⊕ [ last ])
  of-past (r , _) with of-idx p 0 xs₀ r
  ... | inj₁ (j , _ , refl) = to≺ (p ⊕ [ ix j ]) (p ⊕ [ last ]) (<ᵖ-part p {ix j} {last} [] [] refl)
  ... | inj₂ refl with of-func p 0 xs₀ r (of-end-row p 0 xs₀)
  ...   | ()

-- Each row of an `of` lies one label below it.
of-rows-at : ∀ {A : Set} p i (xs : List A) {k} → k ∈ of-rows p i xs → Σ Label λ x → Σ Path λ ys → k ≡ p ⊕ (x ∷ ys)
of-rows-at p i []       (here refl) = last , [] , refl
of-rows-at p i (_ ∷ xs) (here refl) = ix i , [] , refl
of-rows-at p i (_ ∷ xs) (there m)   = of-rows-at p (suc i) xs m

------------------------------------------------------------------------
-- A scan

-- A SCAN KEEPS ITS SOURCE'S ORDER: its rows are its source's, at the
-- same positions, its values the folds of its source's.
module ScanOrder {A B : Set} (f : B → A → B) (z : B) (d : Den A) (P : Pos)
  (fu    : ∀ {y e e′} → enter d P y e → enter d P y e′ → e ≡ e′)
  (flat  : ∀ {y e l ys e′} → enter d P y e → enter d P (y ⊕ (l ∷ ys)) e′ → ⊥)
  (quiet : ∀ {c y e} → enter d P c end → enter d P y e → c ≺ y → PinBy c e) where
  open Scan f z (enter d P) using (sval; sstep; spin; send)
  open AccF f z {enter d P} fu using (acc-val; acc-func)

  Sc = enter (Op.scan f z d) P

  -- Its source's row at the same position.
  bk : ∀ {y e} → Sc y e → Σ (Ev A) (enter d P y)
  bk (sval a , _)  = out (proj₁ (acc-val a)) , proj₂ (acc-val a)
  bk (sstep x , _) = _ , x
  bk (spin x , _)  = _ , x
  bk (send x , _)  = _ , x

  sc-fu : ∀ {y e e′} → Sc y e → Sc y e′ → e ≡ e′
  sc-fu (sval a , _)  (sval a′ , _)  = cong out (acc-func refl a a′)
  sc-fu (sstep x , _) (sstep x′ , _) = refl
  sc-fu (send x , _)  (send x′ , _)  = refl
  sc-fu (spin x , _)  (spin x′ , _)  with fu x x′
  ... | refl = refl
  sc-fu (sval a , _)  (sstep x′ , _) with fu (proj₂ (acc-val a)) x′
  ... | ()
  sc-fu (sval a , _)  (spin x′ , _)  with fu (proj₂ (acc-val a)) x′
  ... | ()
  sc-fu (sval a , _)  (send x′ , _)  with fu (proj₂ (acc-val a)) x′
  ... | ()
  sc-fu (sstep x , _) (sval a′ , _)  with fu x (proj₂ (acc-val a′))
  ... | ()
  sc-fu (sstep x , _) (spin x′ , _)  with fu x x′
  ... | ()
  sc-fu (sstep x , _) (send x′ , _)  with fu x x′
  ... | ()
  sc-fu (spin x , _)  (sval a′ , _)  with fu x (proj₂ (acc-val a′))
  ... | ()
  sc-fu (spin x , _)  (sstep x′ , _) with fu x x′
  ... | ()
  sc-fu (spin x , _)  (send x′ , _)  with fu x x′
  ... | ()
  sc-fu (send x , _)  (sval a′ , _)  with fu x (proj₂ (acc-val a′))
  ... | ()
  sc-fu (send x , _)  (sstep x′ , _) with fu x x′
  ... | ()
  sc-fu (send x , _)  (spin x′ , _)  with fu x x′
  ... | ()

  sc-flat : ∀ {y e l ys e′} → Sc y e → Sc (y ⊕ (l ∷ ys)) e′ → ⊥
  sc-flat x x′ = flat (proj₂ (bk x)) (proj₂ (bk x′))

  sc-quiet : ∀ {c y e} → Sc c end → Sc y e → c ≺ y → PinBy c e
  sc-quiet (send x , _) (sval a , _)  cy with quiet x (proj₂ (acc-val a)) cy
  ... | _ , () , _
  sc-quiet (send x , _) (sstep y , _) cy with quiet x y cy
  ... | _ , () , _
  sc-quiet (send x , _) (spin y , _)  cy with quiet x y cy
  ... | _ , refl , lt = _ , refl , lt
  sc-quiet (send x , _) (send y , _)  cy with quiet x y cy
  ... | _ , () , _

------------------------------------------------------------------------
-- A merge of closed lanes

module FlatLayer {X Y : Set} (F : X → Den Y) (d : Den X) (P : Pos)
  (fu    : ∀ {y e e′} → enter d P y e → enter d P y e′ → e ≡ e′)
  (flat  : ∀ {y e l ys e′} → enter d P y e → enter d P (y ⊕ (l ∷ ys)) e′ → ⊥)
  (quiet : ∀ {c y e} → enter d P c end → enter d P y e → c ≺ y → PinBy c e)
  -- Each lane's values met in order, then its end;
  (lrows : X → Pos → List (Pos × Ev Y))
  (lend  : X → Pos → Pos)
  (lrun  : ∀ a l → Met (enter (F a) l) (lrows a l ++ [ (lend a l , end) ]))
  -- every row it has, each below its subscription;
  (lall  : X → Pos → List Pos)
  (lall-in : ∀ a l {k e} → enter (F a) l k e → k ∈ lall a l)
  (lall-at : ∀ a l {k} → k ∈ lall a l → Σ Label λ x → Σ Path λ ys → k ≡ l ⊕ (x ∷ ys))
  -- and its values before its end.
  (lpast : ∀ a l {k b} → enter (F a) l k (out b) → k ≺ lend a l) where

  S = enter d P
  E = enter (Op.flatMap (mergeᶠ nothing) F d) P

  module M = Merge F S

  ln : Pos → Pos
  ln q = q ⊕ [ ix 1 ]

  -- The lanes in turn.
  flatRows : List (Pos × Ev X) → List (Pos × Ev Y)
  flatRows []                 = []
  flatRows ((q , out a) ∷ sc) = lrows a (ln q) ++ flatRows sc
  flatRows ((q , end) ∷ sc)   = (q , end) ∷ []
  flatRows ((q , skip) ∷ sc)  = flatRows sc
  flatRows ((q , pin _) ∷ sc) = flatRows sc

  -- A row of the source under another is none.
  sole : ∀ {q e zs e′} → S q e → S (q ⊕ zs) e′ → zs ≡ []
  sole {zs = []}    _ _ = refl
  sole {zs = _ ∷ _} x y = ⊥-elim (flat x y)

  ext-absurd : ∀ {q e y e′ zs} → S q e → S y e′ → q ≺ y → y ≡ q ⊕ zs → ⊥
  ext-absurd {q} x x′ lt eq with sole x (subst (λ w → S w _) eq x′)
  ... | refl = ≺-irrefl {q} (subst (q ≺_) (trans eq (⊕-identityʳ q)) lt)

  -- What lies under a row of the source lies before the rows past it.
  past-under : ∀ {q e q′ e′} → S q e → S q′ e′ → q ≺ q′ → ∀ ys → (q ⊕ ys) ≺ q′
  past-under {q} {q′ = q′} x x′ lt ys = to≺ (q ⊕ ys) q′ (<ᵖ-apart q q′ ys (from≺ q q′ lt) λ zs eq → ext-absurd x x′ lt eq)

  none-under : ∀ {q e y e′} ys → S q e → S y e′ → q ≺ y → y ≼ (q ⊕ ys) → ⊥
  none-under {q} {y = y} ys x x′ lt le with ≼-split {y} {q ⊕ ys} le
  ... | inj₂ eq = ext-absurd x x′ lt eq
  ... | inj₁ lt′ = ext-absurd x x′ lt (proj₂ (<ᵖ-between q y ys (from≺ q y lt) (from≺ y (q ⊕ ys) lt′)))

  vis-end : ∀ {q e c} → S q e → Visible e → S c end → q ≼ c
  vis-end x vi y cq = pinby-vis vi (quiet y x cq)

  val-end : ∀ {q a c} → S q (out a) → S c end → q ≺ c
  val-end {q} {c = c} x y with ≼-split {q} {c} (vis-end x tt y)
  ... | inj₁ lt   = lt
  ... | inj₂ refl with fu x y
  ...   | ()

  seenS : ∀ {q e} → S q e → Visible e → Seen S q e
  seenS {e = out _} x _ = (x , vis-end x tt) , entered-few d P tt x
  seenS {e = end}   x _ = (x , vis-end x tt) , entered-few d P tt x
  seenS {e = skip}  _ ()
  seenS {e = pin _} _ ()

  -- A lane row lies below its value, under the lane's subscription.
  lane-at : ∀ {q a k e} → enter (F a) (ln q) k e → Σ Path λ ys → k ≡ q ⊕ (ix 1 ∷ ys)
  lane-at {q} {a} y with lall-at a (ln q) (lall-in a (ln q) y)
  ... | x , ys , eq = x ∷ ys , trans eq (⊕-assoc q [ ix 1 ] (x ∷ ys))

  lane-≺ : ∀ {q a k e} → enter (F a) (ln q) k e → ln q ≺ k
  lane-≺ {q} {a} y with lall-at a (ln q) (lall-in a (ln q) y)
  ... | x , ys , eq = subst (ln q ≺_) (sym eq) (≺-ext (ln q) ys)

  lane-≼ : ∀ {q a k e} → enter (F a) (ln q) k e → q ≼ k
  lane-≼ {q} {k = k} y with lane-at y
  ... | ys , eq = ≺→≼ {q} {k} (subst (q ≺_) (sym eq) (≺-ext q ys))

  -- A row told of the merge, by the source row it hangs under.
  data Vis : Pos → Pos → Ev Y → Set where
    vlane : ∀ {q a k b} → S q (out a) → enter (F a) (ln q) k (out b) → Vis k q (out b)
    vend  : ∀ {c} → S c end → Vis c c end

  lend-absurd : ∀ {q a c} → S q (out a) → enter (F a) (ln q) c end → M.Done c → ⊥
  lend-absurd {q} x y ((c₀ , y₀ , le) , _) with lane-at y
  ... | ys , eq = none-under (ix 1 ∷ ys) x y₀ (val-end x y₀) (subst (c₀ ≼_) eq le)

  vis : ∀ {k e} → E k e → Visible e → Σ Pos λ q → Vis k q e
  vis (M.val _ , _) ()
  vis (M.step _ , _) ()
  vis (M.opin _ , _) ()
  vis (M.oend x _ , _) _ = _ , vend x
  vis (M.opass _ _ , _) ()
  vis (M.lane {e = out _} x _ (y , _) _ _ , _) _ = _ , vlane x y
  vis (M.lane {e = end}   _ _ _ _ () , _) _
  vis (M.lane {e = skip}  _ _ _ _ _ , _) ()
  vis (M.lane {e = pin _} _ _ _ _ _ , _) ()
  vis (M.lend x _ (y , _) _ _ dn , _) _ = ⊥-elim (lend-absurd x y dn)
  vis (M.lpass _ _ _ _ _ _ , _) ()
  vis (M.hand _ _ _ _ _ , _) ()
  vis (M.left _ _ _ _ _ , _) ()
  vis (M.run () _ , _) _
  vis (M.rend () _ _ , _) _
  vis (M.rpass _ _ _ , _) ()
  vis (M.rhand _ _ , _) ()

  vis-anc : ∀ {k q e} → Vis k q e → Σ (Ev X) λ e₀ → S q e₀ × Visible e₀
  vis-anc (vlane x _) = _ , x , tt
  vis-anc (vend x)    = _ , x , tt

  vend-src : ∀ {k q} → Vis k q end → S q end
  vend-src (vend x) = x

  vis-under : ∀ {k q e} → Vis k q e → q ≼ k
  vis-under (vlane _ y)  = lane-≼ y
  vis-under (vend {c} _) = ≼-refl {c}

  vis-before : ∀ {k q e q′ e′} → Vis k q e → S q′ e′ → q ≺ q′ → k ≺ q′
  vis-before {q′ = q′} (vlane x y) x′ lt with lane-at y
  ... | ys , eq = subst (_≺ q′) (sym eq) (past-under x x′ lt (ix 1 ∷ ys))
  vis-before (vend _) _ lt = lt

  -- ONE VISIBLE ROW TO A POSITION, where each lane has one: two anchors
  -- of a position are one, as either before the other puts the row
  -- before itself.
  e-fu : (∀ a l {y e e′} → enter (F a) l y e → Visible e → enter (F a) l y e′ → Visible e′ → e ≡ e′)
       → ∀ {y e e′} → E y e → Visible e → E y e′ → Visible e′ → e ≡ e′
  e-fu lfu {y} x vi x′ vi′ = go (proj₂ (vis x vi)) (proj₂ (vis x′ vi′))
    where
      lane-end : ∀ {q a e} → S q (out a) → enter (F a) (ln q) y e → S y end → ⊥
      lane-end s l c with lane-at l
      ... | ys , eq = flat s (subst (λ w → S w end) eq c)

      go : ∀ {q q′ e e′} → Vis y q e → Vis y q′ e′ → e ≡ e′
      go (vend _)    (vend _)      = refl
      go (vlane s l) (vend c)      = ⊥-elim (lane-end s l c)
      go (vend c)    (vlane s l)   = ⊥-elim (lane-end s l c)
      go {q} {q′} v@(vlane s l) v′@(vlane s′ l′) with ≼-or-≻ q′ q
      ... | inj₂ lt = ⊥-elim (vis-under v′ (vis-before v s′ lt))
      ... | inj₁ le with ≼-split {q′} {q} le
      ...   | inj₁ lt   = ⊥-elim (vis-under v (vis-before v′ s lt))
      ...   | inj₂ refl with fu s s′
      ...     | refl = lfu _ (ln q) l tt l′ tt

  -- A row told of the merge lies at or before its end.
  e-proper : ∀ {k q e c} → Vis k q e → S c end → k ≼ c
  e-proper (vend x) y = vis-end x tt y
  e-proper {k} {c = c} v@(vlane x _) y = ≺→≼ {k} {c} (vis-before v y (val-end x y))

  end-vend : ∀ {c} → E c end → S c end
  end-vend y with vis y tt
  ... | _ , vend z = z

  seenE : ∀ {k e} → E k e → Visible e → Seen E k e
  seenE {e = out _} x vi = (x , λ y → e-proper (proj₂ (vis x vi)) (end-vend y)) , entered-few (Op.flatMap (mergeᶠ nothing) F d) P tt x
  seenE {e = end}   x vi = (x , λ y → e-proper (proj₂ (vis x vi)) (end-vend y)) , entered-few (Op.flatMap (mergeᶠ nothing) F d) P tt x
  seenE {e = skip}  _ ()
  seenE {e = pin _} _ ()

  -- Where each row is anchored in its source, against where the merge is read.
  Inv : Maybe Pos → Maybe Pos → Set
  Inv cS cE = ∀ {k q e} → Vis k q e → (After cE k → After cS q) × (After cS q → After cE k)

  -- WHAT A SOURCE RUN REACHES OF THE MERGE.
  module Over (whole : List (Pos × Ev X)) (mw : Met S whole) where

    rowsOf : Pos × Ev X → List Pos
    rowsOf (q , out a) = q ∷ (q ⊕ [ ix 0 ]) ∷ lall a (ln q)
    rowsOf (q , _)     = q ∷ []

    module _ {q e₀} (qin : (q , e₀) ∈ whole) where
      private
        x₀  = proj₁ (run-row mw qin)
        vi₀ = proj₂ (run-row mw qin)
        ksS = proj₁ (proj₂ (seenS x₀ vi₀))
        hS  = proj₂ (proj₂ (seenS x₀ vi₀))

      ks : List Pos
      ks = concatMap (λ q′ → q′ ∷ (q′ ⊕ [ ix 0 ]) ∷ []) ksS ++ concatMap rowsOf whole

      in-whole : ∀ {r k′} → r ∈ whole → k′ ∈ rowsOf r → k′ ∈ ks
      in-whole m r = ∈-++⁺ʳ (concatMap _ ksS) (∈-concatMap⁺ rowsOf (any-map (λ { refl → r }) m))

      row-in : ∀ {q′ e′} → S q′ e′ → q′ ≼ q → q′ ∈ ks
      row-in {e′ = out _} x le = in-whole (run-has fu mw x tt tt le qin) (here refl)
      row-in {e′ = end}   x le = in-whole (run-has fu mw x tt tt le qin) (here refl)
      row-in {q′} {e′ = skip} x le with ≼-split {q′} {q} le
      ... | inj₁ lt = ∈-++⁺ˡ (lift-in (λ q′ → q′ ∷ (q′ ⊕ [ ix 0 ]) ∷ []) (here refl) (hS x lt))
      ... | inj₂ refl = ⊥-elim (skip-vis (fu x x₀) vi₀)
        where skip-vis : ∀ {e : Ev X} → skip ≡ e → Visible e → ⊥
              skip-vis refl ()
      row-in {q′} {e′ = pin r} x le with ≼-split {q′} {q} le
      ... | inj₁ lt = ∈-++⁺ˡ (lift-in (λ q′ → q′ ∷ (q′ ⊕ [ ix 0 ]) ∷ []) (here refl) (hS x lt))
      ... | inj₂ refl = ⊥-elim (pin-vis (fu x x₀) vi₀)
        where pin-vis : ∀ {e : Ev X} → pin r ≡ e → Visible e → ⊥
              pin-vis refl ()

      val-in : ∀ {q′ a′} → S q′ (out a′) → q′ ≼ q → (q′ ⊕ [ ix 0 ]) ∈ ks
      val-in x le = in-whole (run-has fu mw x tt tt le qin) (there (here refl))

      lane-in : ∀ {q′ a′ k′ e′} → S q′ (out a′) → q′ ≼ q → enter (F a′) (ln q′) k′ e′ → k′ ∈ ks
      lane-in {q′} {a′} x le y = in-whole (run-has fu mw x tt tt le qin) (there (there (lall-in a′ (ln q′) y)))

      -- A merge row before a row anchored at `q` hangs under a source row at or before `q`.
      reachE : ∀ {k e} → Vis k q e → Reach M.JoinT k e
      reachE {k} {e} v = ks , pick
        where
          anc : ∀ {q′ e′ k′} → S q′ e′ → q′ ≼ k′ → k′ ≺ k → q′ ≼ q
          anc {q′} {k′ = k′} x le kk qq = ≺-absurd {k} {k′} (≺-≼-≺ {k} {q′} {k′} (vis-before v x qq) le) kk

          pick : ∀ {k′ e′} → M.JoinT k′ e′ → k′ ≺ k → Dep k e k′ e′ → k′ ∈ ks
          pick {k′} (M.val {q′} x) kk _ = val-in x (anc {k′ = k′} x (≺→≼ {q′} {q′ ⊕ [ ix 0 ]} (≺-ext q′ [])) kk)
          pick {k′} (M.step {q′} x) kk _ = row-in x (anc {k′ = k′} x (≼-refl {q′}) kk)
          pick {k′} (M.opin {q′} x) kk _ = row-in x (anc {k′ = k′} x (≼-refl {q′}) kk)
          pick {k′} (M.oend {q′} x _) kk _ = row-in x (anc {k′ = k′} x (≼-refl {q′}) kk)
          pick {k′} (M.opass {q′} x _) kk _ = row-in x (anc {k′ = k′} x (≼-refl {q′}) kk)
          pick {k′} (M.lane x _ (y , _) _ _) kk _ = lane-in x (anc {k′ = k′} x (lane-≼ y) kk) y
          pick {k′} (M.lend x _ (y , _) _ _ _) kk _ = lane-in x (anc {k′ = k′} x (lane-≼ y) kk) y
          pick {k′} (M.lpass x _ (y , _) _ _ _) kk _ = lane-in x (anc {k′ = k′} x (lane-≼ y) kk) y
          pick (M.hand _ _ _ _ ()) _ _
          pick {k′} (M.left x _ (y , _) _ _) kk _ = lane-in x (anc {k′ = k′} x (lane-≼ y) kk) y
          pick (M.run () _) _ _
          pick (M.rend () _ _) _ _
          pick (M.rpass () _ _) _ _
          pick (M.rhand () _) _ _

    -- A LANE READ IN ORDER: the value at `q`, its lane's run met row by row.
    module Lane {q a} (sq : S q (out a)) (qin : (q , out a) ∈ whole) where
      p = ln q
      L = enter (F a) p

      J : Maybe Pos → Maybe Pos → Set
      J c cL = (∀ {k q′ e} → Vis k q′ e → After c k → (q′ ≡ q × Σ Y λ b → e ≡ out b × L k (out b) × After cL k) ⊎ q ≺ q′)
             × (∀ {k q′ e} → Vis k q′ e → q ≺ q′ → After c k)
             × (∀ {k b} → L k (out b) → After cL k → After c k)

      at-k : ∀ {k e q′ e′} → L k e → S q′ e′ → q ≺ q′ → k ≺ q′
      at-k {q′ = q′} y x′ lt with lane-at y
      ... | ys , eq = subst (_≺ q′) (sym eq) (past-under sq x′ lt (ix 1 ∷ ys))

      go : ∀ {c cL} xs → Run L cL (xs ++ [ (lend a p , end) ]) → J c cL → Run E c xs × Inv (just q) (cursor c xs)
      go {c} [] ((_ , _ , _ , lstL) ∷ _) (j₁ , j₂ , _) = [] , λ v → fin v , j₂ v
        where
          fin : ∀ {k q′ e} → Vis k q′ e → After c k → q ≺ q′
          fin v ak with j₁ v ak
          ... | inj₁ (refl , b , refl , lk , akL) = ⊥-elim (lstL lk tt akL (lpast a p lk))
          ... | inj₂ lt = lt
      go {c} ((k , out b) ∷ xs) ((((lk , _) , _) , _ , akL , lstL) ∷ run) (j₁ , j₂ , j₃) with go xs run (j₁′ , j₂′ , λ _ ak′ → ak′)
        where
          j₁′ : ∀ {k′ q′ e} → Vis k′ q′ e → After (just k) k′ → (q′ ≡ q × Σ Y λ b′ → e ≡ out b′ × L k′ (out b′) × After (just k) k′) ⊎ q ≺ q′
          j₁′ v ak with j₁ v (after-≺ c (j₃ lk akL) ak)
          ... | inj₁ (refl , b′ , refl , lk′ , _) = inj₁ (refl , b′ , refl , lk′ , ak)
          ... | inj₂ lt = inj₂ lt
          j₂′ : ∀ {k′ q′ e} → Vis k′ q′ e → q ≺ q′ → After (just k) k′
          j₂′ {k′} {q′} v lt = ≺-≼-≺ {k} {q′} {k′} (at-k lk (proj₁ (proj₂ (vis-anc v))) lt) (vis-under v)
      ... | run′ , inv = (seenE row tt , tt , j₃ lk akL , mn) ∷ run′ , inv
        where
          row : E k (out b)
          row = M.lane sq tt (lk , lane-≺ lk) (λ ()) tt , reachE qin (vlane sq lk)
          mn : ∀ {k′ e′} → E k′ e′ → Visible e′ → After c k′ → k ≼ k′
          mn {k′} y vi ak with vis y vi
          ... | q′ , v′ with j₁ v′ ak
          ...   | inj₁ (refl , b′ , refl , lk′ , akL′) = lstL lk′ tt akL′
          ...   | inj₂ lt = ≺→≼ {k} {k′} (≺-≼-≺ {k} {q′} {k′} (at-k lk (proj₁ (proj₂ (vis-anc v′))) lt) (vis-under v′))
      go ((k , end) ∷ xs) ((((ke , _) , _) , _) ∷ run) _ = ⊥-elim (snoc≢[] xs _ (run-past-end {t = L} ke run))
      go ((_ , skip) ∷ _) ((_ , () , _) ∷ _) _
      go ((_ , pin _) ∷ _) ((_ , () , _) ∷ _) _

    -- The source run read lane by lane.
    each-go : ∀ {cS cE sc} → (∀ {r} → r ∈ sc → r ∈ whole) → Inv cS cE → Run S cS sc
            → Σ _ λ rs → Run E cE rs × rs ≡ flatRows sc × Inv (cursor cS sc) (cursor cE rs)
    each-go _ inv [] = [] , [] , refl , inv
    each-go {cS} {cE} sub inv (_∷_ {q = q} {e = out a} {rs = sc′} (((x , _) , _) , _ , aft , lst) run)
      with Lane.go x (sub (here refl)) (lrows a (ln q)) (lrun a (ln q)) (j₁ , j₂ , j₃)
      where
        j₁ : ∀ {k q′ e} → Vis k q′ e → After cE k → (q′ ≡ q × Σ Y λ b → e ≡ out b × enter (F a) (ln q) k (out b) × After nothing k) ⊎ q ≺ q′
        j₁ v ak with ≼-split {q} {_} (lst (proj₁ (proj₂ (vis-anc v))) (proj₂ (proj₂ (vis-anc v))) (proj₁ (inv v) ak))
        ... | inj₁ lt = inj₂ lt
        j₁ (vlane x′ y) ak | inj₂ refl with fu x′ x
        ... | refl = inj₁ (refl , _ , refl , y , tt)
        j₁ (vend x′) ak | inj₂ refl with fu x x′
        ... | ()
        j₂ : ∀ {k q′ e} → Vis k q′ e → q ≺ q′ → After cE k
        j₂ v lt = proj₂ (inv v) (after-≺ cS aft lt)
        j₃ : ∀ {k b} → enter (F a) (ln q) k (out b) → After nothing k → After cE k
        j₃ y _ = proj₂ (inv (vlane x y)) aft
    ... | runL , invL with each-go (λ m → sub (there m)) invL run
    ...   | rs′ , run′ , eqr′ , inv′ =
      lrows a (ln q) ++ rs′ , run-++ runL run′ , cong (lrows a (ln q) ++_) eqr′ ,
      subst (Inv (cursor (just q) sc′)) (sym (cursor-++ cE (lrows a (ln q)) rs′)) inv′
    each-go {cS} {cE} sub inv (_∷_ {q = c} {e = end} (((x , _) , _) , _ , aft , lst) run) with run-past-end {t = S} x run
    ... | refl = (c , end) ∷ [] , (seenE row tt , tt , proj₂ (inv (vend x)) aft , mn) ∷ [] , refl , inv-end
      where
        lane-ended : ∀ {q′ a′} → S q′ (out a′) → q′ ≺ c → Ended (LaneOf F q′ a′) c
        lane-ended {q′} {a′} x′ lt = lend a′ (ln q′) , (le′ , lane-≺ le′) , ≺→≼ {lend a′ (ln q′)} {c} at′
          where
            le′ = proj₁ (run-row (lrun a′ (ln q′)) (∈-++⁺ʳ (lrows a′ (ln q′)) (here refl)))
            at′ : lend a′ (ln q′) ≺ c
            at′ with lane-at le′
            ... | ys , eq = subst (_≺ c) (sym eq) (past-under x′ x lt (ix 1 ∷ ys))
        row : E c end
        row = M.oend x ((c , x , ≼-refl {c}) , λ x′ _ lt _ → lane-ended x′ lt) , reachE (sub (here refl)) (vend x)
        mn : ∀ {k′ e′} → E k′ e′ → Visible e′ → After cE k′ → c ≼ k′
        mn {k′} y vi ak with vis y vi
        ... | q′ , v′ = ≼-trans {c} {q′} {k′} (lst (proj₁ (proj₂ (vis-anc v′))) (proj₂ (proj₂ (vis-anc v′))) (proj₁ (inv v′) ak)) (vis-under v′)
        inv-end : Inv (just c) (just c)
        inv-end {k} {q′} v = fwd v , λ lt → ≺-≼-≺ {c} {q′} {k} lt (vis-under v)
          where
            fwd : ∀ {k q′ e} → Vis k q′ e → c ≺ k → c ≺ q′
            fwd {k} {q′} v ck with ≼-or-≻ q′ c
            ... | inj₂ lt = lt
            ... | inj₁ le with ≼-split {q′} {c} le
            ...   | inj₁ lt = ⊥-elim (≺-absurd {c} {k} ck (vis-before v x lt))
            fwd (vend _)     ck | inj₁ _ | inj₂ refl = ⊥-elim (≺-irrefl {c} ck)
            fwd (vlane x′ _) ck | inj₁ _ | inj₂ refl with fu x′ x
            ... | ()
    each-go _ _ (_∷_ {e = skip}  (_ , () , _) _)
    each-go _ _ (_∷_ {e = pin _} (_ , () , _) _)

  flat-in : ∀ {sc} → Met S sc → Met E (flatRows sc)
  flat-in {sc} m with Over.each-go sc m (λ r → r) (λ _ → (λ _ → tt) , (λ _ → tt)) m
  ... | rs , run , refl , _ = run

  -- A SOURCE RUN REACHING THE ANCHOR OF A MERGE ROW MET lays out the
  -- merge's run met up to that row, extended.
  found : (∀ {y e e′} → E y e → Visible e → E y e′ → Visible e′ → e ≡ e′) → ∀ {ys k e q e₀} → Met E (ys ++ [ (k , e) ]) → Vis k q e
        → ∀ rs″ → Met S (rs″ ++ [ (q , e₀) ])
        → Prefix _≡_ (ys ++ [ (k , e) ]) (flatRows (rs″ ++ [ (q , e₀) ]))
  found fuE {ys} {k} {e} {q} {e₀} m v rs″ mS with Over.each-go (rs″ ++ [ (q , e₀) ]) mS (λ r → r) (λ _ → (λ _ → tt) , (λ _ → tt)) mS
  ... | rs′ , mE , refl , inv = longer
    where
      rl = ys ++ [ (k , e) ]

      longer : Prefix _≡_ rl rs′
      longer with run-det fuE m mE
      ... | inj₁ pr = pr
      ... | inj₂ pr with prefix-split pr
      ...   | inj₁ eq′ = subst (Prefix _≡_ rl) (sym eq′) (subst (λ w → Prefix _≡_ w rl) eq′ pr)
      ...   | inj₂ ((kz , ez) , zs , eq′) with run-tail rs′ (subst (Run E nothing) eq′ m)
      ...     | tl@((((xz , _) , _) , viz , az , _) ∷ tl′) with vis xz viz
      ...       | qz , vz =
        let qqz : q ≺ qz
            qqz = subst (λ w → After w qz) (cursor-snoc nothing rs″) (proj₁ (inv vz) az)
            kkz : k ≺ kz
            kkz = ≺-≼-≺ {k} {qz} {kz} (vis-before v (proj₁ (proj₂ (vis-anc vz))) qqz) (vis-under vz)
            kzk : kz ≼ k
            kzk = in-tail (last-in ys rs′ eq′)
        in ⊥-elim (kzk kkz)
        where
          in-tail : (k , e) ∈ ((kz , ez) ∷ zs) → kz ≼ k
          in-tail (here refl) = ≼-refl {kz}
          in-tail (there m′)  = ≺→≼ {kz} {k} (run-after tl′ m′)

------------------------------------------------------------------------
-- Two lists per value

-- A VALUE'S TWO LISTS, THE FIRST THEN THE SECOND: each value of the
-- source runs an inner merge over `of` two flags, each flag's lane the
-- `of` of one list.
module Each₂ {X Y : Set} (f g : X → List Y) where
  tf : List Bool
  tf = true ∷ false ∷ []

  H : X → Bool → List Y
  H x c = if c then f x else g x

  Inner : X → Den Y
  Inner x = Op.flatMap (mergeᶠ nothing) (λ c → Op.of (H x c)) (Op.of tf)

  module IL (x : X) (l : Pos) = FlatLayer (λ c → Op.of (H x c)) (Op.of tf) l
    (OfMet.o-fu l tf) (OfMet.o-flat l tf) (OfMet.o-quiet l tf)
    (λ c l′ → ofVals l′ 0 (H x c)) (λ c l′ → l′ ⊕ [ last ]) (λ c l′ → OfMet.of-met l′ (H x c))
    (λ c l′ → of-rows l′ 0 (H x c)) (λ c l′ y → of-in l′ 0 (H x c) (proj₁ y)) (λ c l′ → of-rows-at l′ 0 (H x c))
    (λ c l′ → OfMet.of-past l′ (H x c))

  -- One visible row of the inner merge to a position, as of each list.
  inner-fu : ∀ x l {y e e′} → enter (Inner x) l y e → Visible e → enter (Inner x) l y e′ → Visible e′ → e ≡ e′
  inner-fu x l = IL.e-fu x l (λ c l′ y _ y′ _ → OfMet.o-fu l′ (H x c) y y′)

  -- The inner merge's values: the first list's, then the second's.
  lrows₂ : X → Pos → List (Pos × Ev Y)
  lrows₂ x l = ofVals ((l ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) 0 (f x) ++ ofVals ((l ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) 0 (g x)

  innerRun : ∀ x l → Met (enter (Inner x) l) (lrows₂ x l ++ [ (l ⊕ [ last ] , end) ])
  innerRun x l = subst (Met (enter (Inner x) l))
    (sym (++-assoc (ofVals ((l ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) 0 (f x)) (ofVals ((l ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) 0 (g x)) [ (l ⊕ [ last ] , end) ]))
    (IL.flat-in x l (OfMet.of-met l tf))

  -- Every row of the inner merge: a flag's silent value, then its lane.
  blk : Pos → List Y → List Pos
  blk q ys = (q ⊕ [ ix 0 ]) ∷ of-rows (q ⊕ [ ix 1 ]) 0 ys

  lall₂ : X → Pos → List Pos
  lall₂ x l = blk (l ⊕ [ ix 0 ]) (f x) ++ blk (l ⊕ [ ix 1 ]) (g x) ++ [ l ⊕ [ last ] ]

  in₁ : ∀ x l {k} → k ∈ blk (l ⊕ [ ix 0 ]) (f x) → k ∈ lall₂ x l
  in₁ x l m = ∈-++⁺ˡ m

  in₂ : ∀ x l {k} → k ∈ blk (l ⊕ [ ix 1 ]) (g x) → k ∈ lall₂ x l
  in₂ x l m = ∈-++⁺ʳ (blk (l ⊕ [ ix 0 ]) (f x)) (∈-++⁺ˡ m)

  in₃ : ∀ x l → (l ⊕ [ last ]) ∈ lall₂ x l
  in₃ x l = ∈-++⁺ʳ (blk (l ⊕ [ ix 0 ]) (f x)) (∈-++⁺ʳ (blk (l ⊕ [ ix 1 ]) (g x)) (here refl))

  lall-in₂ : ∀ x l {k e} → enter (Inner x) l k e → k ∈ lall₂ x l
  lall-in₂ x l (Merge.val (at-out , _) , _)                       = in₁ x l (here refl)
  lall-in₂ x l (Merge.val (on-out at-out , _) , _)                = in₂ x l (here refl)
  lall-in₂ x l (Merge.val (on-out (on-out ()) , _) , _)
  lall-in₂ x l (Merge.step (on-out (on-out ()) , _) , _)
  lall-in₂ x l (Merge.opin (on-out (on-out ()) , _) , _)
  lall-in₂ x l (Merge.oend (on-out (on-out at-end) , _) _ , _)    = in₃ x l
  lall-in₂ x l (Merge.opass (on-out (on-out at-end) , _) _ , _)   = in₃ x l
  lall-in₂ x l (Merge.lane (at-out , _) _ (y , _) _ _ , _)         = in₁ x l (there (of-in _ 0 (f x) (proj₁ y)))
  lall-in₂ x l (Merge.lane (on-out at-out , _) _ (y , _) _ _ , _)  = in₂ x l (there (of-in _ 0 (g x) (proj₁ y)))
  lall-in₂ x l (Merge.lane (on-out (on-out ()) , _) _ _ _ _ , _)
  lall-in₂ x l (Merge.lend (at-out , _) _ (y , _) _ _ _ , _)        = in₁ x l (there (of-in _ 0 (f x) (proj₁ y)))
  lall-in₂ x l (Merge.lend (on-out at-out , _) _ (y , _) _ _ _ , _) = in₂ x l (there (of-in _ 0 (g x) (proj₁ y)))
  lall-in₂ x l (Merge.lend (on-out (on-out ()) , _) _ _ _ _ _ , _)
  lall-in₂ x l (Merge.lpass (at-out , _) _ (y , _) _ _ _ , _)        = in₁ x l (there (of-in _ 0 (f x) (proj₁ y)))
  lall-in₂ x l (Merge.lpass (on-out at-out , _) _ (y , _) _ _ _ , _) = in₂ x l (there (of-in _ 0 (g x) (proj₁ y)))
  lall-in₂ x l (Merge.lpass (on-out (on-out ()) , _) _ _ _ _ _ , _)
  lall-in₂ x l (Merge.hand _ _ _ _ () , _)
  lall-in₂ x l (Merge.left (at-out , _) _ (y , _) _ _ , _)         = in₁ x l (there (of-in _ 0 (f x) (proj₁ y)))
  lall-in₂ x l (Merge.left (on-out at-out , _) _ (y , _) _ _ , _)  = in₂ x l (there (of-in _ 0 (g x) (proj₁ y)))
  lall-in₂ x l (Merge.left (on-out (on-out ()) , _) _ _ _ _ , _)
  lall-in₂ x l (Merge.run () _ , _)
  lall-in₂ x l (Merge.rend () _ _ , _)
  lall-in₂ x l (Merge.rpass () _ _ , _)
  lall-in₂ x l (Merge.rhand () _ , _)

  blk-at : ∀ l c (ys : List Y) {k} → k ∈ blk (l ⊕ [ c ]) ys → Σ Path λ zs → k ≡ l ⊕ (c ∷ zs)
  blk-at l c ys (here refl) = ix 0 ∷ [] , ⊕-assoc l [ c ] [ ix 0 ]
  blk-at l c ys (there m) with of-rows-at ((l ⊕ [ c ]) ⊕ [ ix 1 ]) 0 ys m
  ... | x , zs , eq = ix 1 ∷ x ∷ zs , trans eq (trans (⊕-assoc (l ⊕ [ c ]) [ ix 1 ] (x ∷ zs)) (⊕-assoc l [ c ] (ix 1 ∷ x ∷ zs)))

  lall-at₂ : ∀ x l {k} → k ∈ lall₂ x l → Σ Label λ c → Σ Path λ zs → k ≡ l ⊕ (c ∷ zs)
  lall-at₂ x l m with ∈-++⁻ (blk (l ⊕ [ ix 0 ]) (f x)) m
  ... | inj₁ m₁ = ix 0 , blk-at l (ix 0) (f x) m₁
  ... | inj₂ m₂ with ∈-++⁻ (blk (l ⊕ [ ix 1 ]) (g x)) m₂
  ...   | inj₁ m₃          = ix 1 , blk-at l (ix 1) (g x) m₃
  ...   | inj₂ (here refl) = last , [] , refl

  -- A value of the inner merge lies before its end.
  lpast₂ : ∀ x l {k b} → enter (Inner x) l k (out b) → k ≺ (l ⊕ [ last ])
  lpast₂ x l y with IL.vis x l y tt
  ... | _ , v@(IL.vlane x₀ _) = IL.vis-before x l v ce (IL.val-end x l x₀ ce)
    where ce = OfMet.row l tf (of-end-row l 0 tf)

  -- The outer merge, over any source.
  module Outer (d : Den X) (P : Pos)
    (fu    : ∀ {y e e′} → enter d P y e → enter d P y e′ → e ≡ e′)
    (flat  : ∀ {y e l ys e′} → enter d P y e → enter d P (y ⊕ (l ∷ ys)) e′ → ⊥)
    (quiet : ∀ {c y e} → enter d P c end → enter d P y e → c ≺ y → PinBy c e) =
    FlatLayer Inner d P fu flat quiet lrows₂ (λ _ l → l ⊕ [ last ]) innerRun lall₂ lall-in₂ lall-at₂ lpast₂
