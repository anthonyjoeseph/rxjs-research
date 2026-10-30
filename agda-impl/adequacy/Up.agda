{-# OPTIONS --guardedness #-}

-- WHAT THE ROOT OWES RESPECTS THE ROWS: the same rows in the hole, the
-- same rows at the root, frame by frame.  A merge's lanes are matched
-- index by index, so a lane's rows replaced in its list is the same merge.
module adequacy.Up where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos)
open import denotation.EmissionSet using (EmissionSet; Truncate; Reach; MapT; map-out; map-skip; map-pin; map-end; DenEnv; module Connecting; module Scan; module TakeWhile)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; St; CS; free; cpAt; cutAt; overAt; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (TakeR; kept; Stops; stop; left; up; env; rows; Hot; pendRows; Vis; Plus; old; new; rowsL;
  Lanes; Each; Kth; AllEnd; EndsOf; module Flat; module BoundedF; module SwitchF; module ExhaustF; _≃_; _⇄_; ≃-sym)

open _≃_

≃-refl : ∀ {A} {t : EmissionSet A} → t ≃ t
≃-refl = (λ x → x) ⇄ (λ x → x)

≃-trans : ∀ {A} {t u v : EmissionSet A} → t ≃ u → u ≃ v → t ≃ v
≃-trans a b = (λ r → to b (to a r)) ⇄ (λ r → from a (from b r))

vis-≃ : ∀ {A} {t u : EmissionSet A} → t ≃ u → Vis t ≃ Vis u
vis-≃ eq = (λ { (r , v) → to eq r , v }) ⇄ (λ { (r , v) → from eq r , v })

plus-≃ : ∀ {A} {t u : EmissionSet A} {p e} → t ≃ u → Plus t p e ≃ Plus u p e
plus-≃ eq = (λ { (old r) → old (to eq r) ; new → new }) ⇄ (λ { (old r) → old (from eq r) ; new → new })

-- Two lists of lanes, lane by lane the same rows.
data _≈ᴸ_ {B : Set} : List (EmissionSet B) → List (EmissionSet B) → Set₁ where
  []  : [] ≈ᴸ []
  _∷_ : ∀ {t u Ls Ls′} → t ≃ u → Ls ≈ᴸ Ls′ → (t ∷ Ls) ≈ᴸ (u ∷ Ls′)

≈ᴸ-sym : ∀ {B} {Ls Ls′ : List (EmissionSet B)} → Ls ≈ᴸ Ls′ → Ls′ ≈ᴸ Ls
≈ᴸ-sym []       = []
≈ᴸ-sym (e ∷ es) = ≃-sym e ∷ ≈ᴸ-sym es

≈ᴸ-refl : ∀ {B} (Ls : List (EmissionSet B)) → Ls ≈ᴸ Ls
≈ᴸ-refl []       = []
≈ᴸ-refl (_ ∷ Ls) = ≃-refl ∷ ≈ᴸ-refl Ls

ʳ++-≈ : ∀ {B} (xs : List (EmissionSet B)) {ys ys′} → ys ≈ᴸ ys′ → (xs ʳ++ ys) ≈ᴸ (xs ʳ++ ys′)
ʳ++-≈ []       h = h
ʳ++-≈ (x ∷ xs) h = ʳ++-≈ xs (≃-refl ∷ h)

any-≈ : ∀ {B} {Ls Ls′ : List (EmissionSet B)} → Ls ≈ᴸ Ls′ → ∀ {k e} → Lanes Ls k e → Lanes Ls′ k e
any-≈ (e ∷ _)  (inj₁ r) = inj₁ (to e r)
any-≈ (_ ∷ es) (inj₂ x) = inj₂ (any-≈ es x)

-- The same lanes: the same ends, counted.
kth-≃ : ∀ {B} {Ls Ls′ : List (EmissionSet B)} {P : Pos → Set} → Ls ≈ᴸ Ls′ → ∀ {k} → Kth P (EndsOf Ls) k → Kth P (EndsOf Ls′) k
kth-≃ []       ()
kth-≃ (e ∷ es) {zero}  (inj₁ (c , r , pc))       = inj₁ (c , to e r , pc)
kth-≃ (e ∷ es) {zero}  (inj₂ K)                  = inj₂ (kth-≃ es K)
kth-≃ (e ∷ es) {suc k} (inj₁ ((c , r , pc) , K)) = inj₁ ((c , to e r , pc) , kth-≃ es K)
kth-≃ (e ∷ es) {suc k} (inj₂ K)                  = inj₂ (kth-≃ es K)

allEnd-≃ : ∀ {B} {Ls Ls′ : List (EmissionSet B)} {P : Pos → Set} n → Ls ≈ᴸ Ls′ → AllEnd P n (EndsOf Ls) → AllEnd P n (EndsOf Ls′)
allEnd-≃ zero    es _ = _
allEnd-≃ (suc k) es K = kth-≃ es K

------------------------------------------------------------------------
-- A list with a hole: the lanes before it, nearest first, and after.

module _ {B : Set} where

  any-ʳ++ʳ : ∀ (xs : List (EmissionSet B)) {ys k e} → Lanes ys k e → Lanes (xs ʳ++ ys) k e
  any-ʳ++ʳ []       b = b
  any-ʳ++ʳ (z ∷ xs) b = any-ʳ++ʳ xs (inj₂ b)

  any-ʳ++ˡ : ∀ (xs : List (EmissionSet B)) {ys k e} → Lanes xs k e → Lanes (xs ʳ++ ys) k e
  any-ʳ++ˡ (z ∷ xs) (inj₁ r) = any-ʳ++ʳ xs (inj₁ r)
  any-ʳ++ˡ (z ∷ xs) (inj₂ a) = any-ʳ++ˡ xs a

  any-ʳ++ : ∀ (xs : List (EmissionSet B)) {ys k e} → Lanes (xs ʳ++ ys) k e → Lanes xs k e ⊎ Lanes ys k e
  any-ʳ++ []       x = inj₂ x
  any-ʳ++ (z ∷ xs) x with any-ʳ++ xs x
  ... | inj₁ a        = inj₁ (inj₂ a)
  ... | inj₂ (inj₁ r) = inj₁ (inj₁ r)
  ... | inj₂ (inj₂ b) = inj₂ b

  all-ʳ++ : ∀ {P : EmissionSet B → Set} (xs : List (EmissionSet B)) {ys} → Each P xs → Each P ys → Each P (xs ʳ++ ys)
  all-ʳ++ []       _        b = b
  all-ʳ++ (z ∷ xs) (a , as) b = all-ʳ++ xs as (a , b)

-- The same outer and the same lanes: the same merge.
done : ∀ {A B : Set} (L : A → Pos → EmissionSet B) {O O′ : EmissionSet A} {d} n {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′
     → ∀ {c} → Flat.Done L O d n Ls c → Flat.Done L O′ d n Ls′ c
done L n eo es (Flat.over-at (inj₁ td) ls , h) = Flat.over-at (inj₁ td) (allEnd-≃ n es ls) , λ r ru lt nc → h (from eo r) ru lt nc
done L n eo es (Flat.over-at (inj₂ (c₀ , x , le)) ls , h) = Flat.over-at (inj₂ (c₀ , to eo x , le)) (allEnd-≃ n es ls) , λ r ru lt nc → h (from eo r) ru lt nc

flat : ∀ {A B : Set} (L : A → Pos → EmissionSet B) {O O′ : EmissionSet A} {d} n {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′
     → ∀ {q e} → Flat.JoinT L O d n Ls q e → Flat.JoinT L O′ d n Ls′ q e
flat L n eo es (Flat.val r)              = Flat.val (to eo r)
flat L n eo es (Flat.step r)             = Flat.step (to eo r)
flat L n eo es (Flat.opin r)             = Flat.opin (to eo r)
flat L n eo es (Flat.oend r d)           = Flat.oend (to eo r) (done L n eo es d)
flat L n eo es (Flat.opass r nd)         = Flat.opass (to eo r) λ d → nd (done L n (≃-sym eo) (≈ᴸ-sym es) d)
flat L n eo es (Flat.lane r ru l nc w)   = Flat.lane (to eo r) ru l nc w
flat L n eo es (Flat.lend r ru l nc nh d)   = Flat.lend (to eo r) ru l nc nh (done L n eo es d)
flat L n eo es (Flat.lpass r ru l nc nh nd) = Flat.lpass (to eo r) ru l nc nh λ d → nd (done L n (≃-sym eo) (≈ᴸ-sym es) d)
flat L n eo es (Flat.left r ru l nc i)    = Flat.left (to eo r) ru l nc i
flat L n eo es (Flat.hand _ _ _ _ ())
flat L n eo es (Flat.rhand _ ())
flat L n eo es (Flat.run x w)            = Flat.run (any-≈ es x) w
flat L n eo es (Flat.rend x nh d)        = Flat.rend (any-≈ es x) nh (done L n eo es d)
flat L n eo es (Flat.rpass x nh nd)      = Flat.rpass (any-≈ es x) nh λ d → nd (done L n (≃-sym eo) (≈ᴸ-sym es) d)

flat-≃ : ∀ {A B : Set} (L : A → Pos → EmissionSet B) {O O′ : EmissionSet A} {d} n {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′
       → Flat.JoinT L O d n Ls ≃ Flat.JoinT L O′ d n Ls′
flat-≃ L n eo es = flat L n eo es ⇄ flat L n (≃-sym eo) (≈ᴸ-sym es)

-- Fewer rows: no more before any position.
reach-⊆ : ∀ {A} {t u : EmissionSet A} → (∀ {k e} → u k e → t k e) → ∀ {q e} → Reach t q e → Reach u q e
reach-⊆ h (ks , f) = ks , λ x lt d → f (h x) lt d

trunc-≃ : ∀ {A} {t u : EmissionSet A} → t ≃ u → Truncate t ≃ Truncate u
trunc-≃ eq = (λ (r , fw) → to eq r , reach-⊆ (from eq) fw) ⇄ (λ (r , fw) → from eq r , reach-⊆ (to eq) fw)

-- The same outer and the same lanes: the same merge, as entered.
row-≃ : ∀ {A B : Set} (L : A → Pos → EmissionSet B) {O O′ : EmissionSet A} {d} n {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′
      → Flat.RowT L O d n Ls ≃ Flat.RowT L O′ d n Ls′
row-≃ L n eo es = trunc-≃ (flat-≃ L n eo es)

map-≃ : ∀ {A B} (f : A → B) {t u : EmissionSet A} → t ≃ u → MapT f t ≃ MapT f u
map-≃ f eq = go (to eq) ⇄ go (from eq)
  where
    go : ∀ {t u} → (∀ {q e} → t q e → u q e) → ∀ {q e} → MapT f t q e → MapT f u q e
    go h (map-out r)  = map-out (h r)
    go h (map-skip r) = map-skip (h r)
    go h (map-pin r)  = map-pin (h r)
    go h (map-end r)  = map-end (h r)

-- The same rows taken: the same rows kept.
take-≃ : ∀ {A} i (q : A → Bool) w {t u : EmissionSet A} → t ≃ u → TakeR i q w t ≃ TakeR i q w u
take-≃ {A} i q free     eq = trunc-≃ (go (to eq) (from eq) ⇄ go (from eq) (to eq))
  where
    go : ∀ {t u : EmissionSet A} → (∀ {k e} → t k e → u k e) → (∀ {k e} → u k e → t k e) → ∀ {k e} → TakeWhile.TakeT i q t k e → TakeWhile.TakeT i q u k e
    go h h⁻ (TakeWhile.pass r k nf)   = TakeWhile.pass (h r) k λ (k′ , a , x , y , z) → nf (k′ , a , h⁻ x , y , z)
    go h h⁻ (TakeWhile.fail r k nf j) = TakeWhile.fail (h r) k (λ (k′ , a , x , y , z) → nf (k′ , a , h⁻ x , y , z)) j
    go h h⁻ (TakeWhile.stop r k nf)   = TakeWhile.stop (h r) k λ (k′ , a , x , y , z) → nf (k′ , a , h⁻ x , y , z)
    go h h⁻ (TakeWhile.step r nf)     = TakeWhile.step (h r) λ (k′ , a , x , y , z) → nf (k′ , a , h⁻ x , y , z)
    go h h⁻ (TakeWhile.tend r nf)     = TakeWhile.tend (h r) λ (k′ , a , x , y , z) → nf (k′ , a , h⁻ x , y , z)
    go h h⁻ (TakeWhile.left r nf j)   = TakeWhile.left (h r) (λ (k′ , a , x , y , z) → nf (k′ , a , h⁻ x , y , z)) j
take-≃ i q (cpAt p)   eq = go (to eq) ⇄ go (from eq)
  where
    go : ∀ {A} {t u : EmissionSet A} → (∀ {k e} → t k e → u k e) → ∀ {k e} → Stops p t k e → Stops p u k e
    go h stop                = stop
    go h (left (kept r n j)) = left (kept (h r) n j)
take-≃ i q (cutAt p)  eq = (λ { (kept r n j) → kept (to eq r) n j }) ⇄ λ { (kept r n j) → kept (from eq r) n j }
take-≃ i q (overAt p) eq = (λ { (kept r n j) → kept (to eq r) n j }) ⇄ λ { (kept r n j) → kept (from eq r) n j }

-- The same rows scanned: the same folds.
scan-≃ : ∀ {A B} (f : B → A → B) z {t u : EmissionSet A} → t ≃ u → Scan.ScanT f z t ≃ Scan.ScanT f z u
scan-≃ {A} {B} f z eq = go (to eq) (from eq) ⇄ go (from eq) (to eq)
  where
    acc : ∀ {t u : EmissionSet A} → (∀ {q e} → t q e → u q e) → (∀ {q e} → u q e → t q e) → ∀ {q b} → Scan.Acc f z t q b → Scan.Acc f z u q b
    acc h h⁻ (Scan.acc₀ r mn)     = Scan.acc₀ (h r) (λ y → mn (h⁻ y))
    acc h h⁻ (Scan.acc a r lt nx) = Scan.acc (acc h h⁻ a) (h r) lt (λ y → nx (h⁻ y))
    go : ∀ {t u : EmissionSet A} → (∀ {q e} → t q e → u q e) → (∀ {q e} → u q e → t q e) → ∀ {q e} → Scan.ScanT f z t q e → Scan.ScanT f z u q e
    go h h⁻ (Scan.sval a)  = Scan.sval (acc h h⁻ a)
    go h h⁻ (Scan.sstep r) = Scan.sstep (h r)
    go h h⁻ (Scan.spin r)  = Scan.spin (h r)
    go h h⁻ (Scan.send r)  = Scan.send (h r)

-- The same source and the same body: the same connect.
conn-≃ : ∀ {A B : Set} r {σ σ′ : EmissionSet A} {β β′ : EmissionSet B} → σ ≃ σ′ → β ≃ β′ → Connecting.ConnT r σ β ≃ Connecting.ConnT r σ′ β′
conn-≃ {A} {B} r es eb = go es eb ⇄ go (≃-sym es) (≃-sym eb)
  where
    go : ∀ {σ σ′ : EmissionSet A} {β β′ : EmissionSet B} → σ ≃ σ′ → β ≃ β′ → ∀ {q e} → Connecting.ConnT r σ β q e → Connecting.ConnT r σ′ β′ q e
    go es eb (Connecting.body x)           = Connecting.body (to eb x)
    go es eb (Connecting.burst x i)        = Connecting.burst (to es x) i
    go es eb (Connecting.echo x al u ni)   = Connecting.echo (to es x) (λ y → al (from eb y)) u ni
    go es eb (Connecting.kept x al ni i)   = Connecting.kept (to es x) (λ y → al (from eb y)) ni i

-- A BINDER'S MEANING, UP TO THE SAME ROWS: a body reads its binder only
-- through the rows it holds, so the same rows bound give the same body.
-- The same outer and the same lanes: the same joiner part way through.
postulate
  bounded-≃ : ∀ {A B : Set} m (L : A → Pos → EmissionSet B) {O O′ : EmissionSet A} {d n q} {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′
            → BoundedF.RowT m L O d n q Ls ≃ BoundedF.RowT m L O′ d n q Ls′
  switch-≃  : ∀ {A B : Set} (L : A → Pos → EmissionSet B) {O O′ : EmissionSet A} {d n} {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′
            → SwitchF.RowT L O d n Ls ≃ SwitchF.RowT L O′ d n Ls′
  exhaust-≃ : ∀ {A B : Set} (L : A → Pos → EmissionSet B) {O O′ : EmissionSet A} {d n} {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′
            → ExhaustF.RowT L O d n Ls ≃ ExhaustF.RowT L O′ d n Ls′

-- By induction over the state and, under a pending subscription, over
-- the program's meaning, every operator reading its inputs row by row.
postulate
  rows-hot : ∀ {Γ X B} {t u : EmissionSet X} (k : CS) (ρ : DenEnv Γ) (b : St (X ∷ Γ) B) → t ≃ u → rows (Hot t k ∷ᴬ ρ) b ≃ rows (Hot u k ∷ᴬ ρ) b

-- THE CONGRUENCE.
up-≃ : ∀ {R Γ A} (c : Ctx R Γ A) {t u : EmissionSet A} → t ≃ u → up c t ≃ up c u
up-≃ top                                              eq = eq
up-≃ (inMap f c)                                      eq = up-≃ c (map-≃ f eq)
up-≃ (inScan f z c)                                   eq = up-≃ c (scan-≃ f z eq)
up-≃ (inCut true a c)                                 eq = up-≃ c eq
up-≃ (inCut false a c)                                eq = ≃-refl
up-≃ (inLn true c)                                    eq = up-≃ c eq
up-≃ (inLn false c)                                   eq = ≃-refl
up-≃ (inTake i q w c)                                 eq = up-≃ c (take-≃ i q w eq)
up-≃ (inOuter (mergeᶠ nothing) f d n q ls c)          eq = up-≃ c (row-≃ (λ a → pendRows (env c) (f a)) n eq (≈ᴸ-refl (rowsL (env c) ls)))
up-≃ (inOuter (mergeᶠ (just m)) f d n q ls c)         eq = up-≃ c (bounded-≃ m (λ a → pendRows (env c) (f a)) eq (≈ᴸ-refl (rowsL (env c) ls)))
up-≃ (inOuter switchᶠ f d n q ls c)                   eq = up-≃ c (switch-≃ (λ a → pendRows (env c) (f a)) eq (≈ᴸ-refl (rowsL (env c) ls)))
up-≃ (inOuter exhaustᶠ f d n q ls c)                  eq = up-≃ c (exhaust-≃ (λ a → pendRows (env c) (f a)) eq (≈ᴸ-refl (rowsL (env c) ls)))
up-≃ (inLanes (mergeᶠ nothing) f d n q o pre post c)  eq = up-≃ c (row-≃ (λ a → pendRows (env c) (f a)) n ≃-refl (ʳ++-≈ (rowsL (env c) pre) (eq ∷ ≈ᴸ-refl (rowsL (env c) post))))
up-≃ (inLanes (mergeᶠ (just m)) f d n q o pre post c) eq = up-≃ c (bounded-≃ m (λ a → pendRows (env c) (f a)) ≃-refl (ʳ++-≈ (rowsL (env c) pre) (eq ∷ ≈ᴸ-refl (rowsL (env c) post))))
up-≃ (inLanes switchᶠ f d n q o pre post c)           eq = up-≃ c (switch-≃ (λ a → pendRows (env c) (f a)) ≃-refl (ʳ++-≈ (rowsL (env c) pre) (eq ∷ ≈ᴸ-refl (rowsL (env c) post))))
up-≃ (inLanes exhaustᶠ f d n q o pre post c)          eq = up-≃ c (exhaust-≃ (λ a → pendRows (env c) (f a)) ≃-refl (ʳ++-≈ (rowsL (env c) pre) (eq ∷ ≈ᴸ-refl (rowsL (env c) post))))
up-≃ (inSrc k b c)                                    eq = up-≃ c (conn-≃ _ eq (rows-hot k (env c) b eq))
up-≃ (inBody k o c)                                   eq = up-≃ c (conn-≃ _ ≃-refl eq)
