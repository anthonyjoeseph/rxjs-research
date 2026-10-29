{-# OPTIONS --guardedness #-}

-- WHAT THE ROOT OWES RESPECTS THE ROWS: the same rows in the hole, the
-- same rows at the root, frame by frame.  A merge's lanes are matched
-- index by index, so a lane's rows replaced in its list is the same merge.
module adequacy.Up where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos)
open import denotation.EmissionSet using (EmissionSet; MapT; map-out; map-skip; map-end; DenEnv; module Connecting)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; St; CS; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (up; env; rows; Hot; pendRows; Vis; Plus; old; new; rowsL; Gone; Lanes; Each; module Flat; _≃_; _⇄_; ≃-sym)

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

Gone-≃ : ∀ {X} {t u : EmissionSet X} {c} → t ≃ u → Gone t c → Gone u c
Gone-≃ eq g r = g (from eq r)

all-≈ : ∀ {B} {Ls Ls′ : List (EmissionSet B)} → Ls ≈ᴸ Ls′ → ∀ {c} → Each (λ t → Gone t c) Ls → Each (λ t → Gone t c) Ls′
all-≈ []       _        = _
all-≈ (e ∷ es) {c} (g , gs) = Gone-≃ {c = c} e g , all-≈ es {c} gs

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

  all-ʳ++⁻ : ∀ {P : EmissionSet B → Set} (xs : List (EmissionSet B)) {ys} → Each P (xs ʳ++ ys) → Each P xs × Each P ys
  all-ʳ++⁻ []       b = _ , b
  all-ʳ++⁻ (z ∷ xs) b with all-ʳ++⁻ xs b
  ... | a , (pz , c) = (pz , a) , c

-- The same outer and the same lanes: the same merge.
done : ∀ {A B : Set} (L : A → Pos → EmissionSet B) {O O′ : EmissionSet A} {d} {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′
     → ∀ {c} → Flat.Done L O d Ls c → Flat.Done L O′ d Ls′ c
done L eo es {c} ((inj₁ td , ls) , h) = (inj₁ td , all-≈ es {c} ls) , λ r ru lt nc → h (from eo r) ru lt nc
done L eo es {c} ((inj₂ (c₀ , x , le) , ls) , h) = (inj₂ (c₀ , to eo x , le) , all-≈ es {c} ls) , λ r ru lt nc → h (from eo r) ru lt nc

flat : ∀ {A B : Set} (L : A → Pos → EmissionSet B) {O O′ : EmissionSet A} {d} {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′
     → ∀ {q e} → Flat.JoinT L O d Ls q e → Flat.JoinT L O′ d Ls′ q e
flat L eo es (Flat.val r)              = Flat.val (to eo r)
flat L eo es (Flat.step r)             = Flat.step (to eo r)
flat L eo es (Flat.oend r d)           = Flat.oend (to eo r) (done L eo es d)
flat L eo es (Flat.opass r nd)         = Flat.opass (to eo r) λ d → nd (done L (≃-sym eo) (≈ᴸ-sym es) d)
flat L eo es (Flat.lane r ru l nc w)   = Flat.lane (to eo r) ru l nc w
flat L eo es (Flat.lend r ru l nc nh d)   = Flat.lend (to eo r) ru l nc nh (done L eo es d)
flat L eo es (Flat.lpass r ru l nc nh nd) = Flat.lpass (to eo r) ru l nc nh λ d → nd (done L (≃-sym eo) (≈ᴸ-sym es) d)
flat L eo es (Flat.left _ _ _ () _)
flat L eo es (Flat.hand _ _ _ _ ())
flat L eo es (Flat.rhand _ ())
flat L eo es (Flat.run x w)            = Flat.run (any-≈ es x) w
flat L eo es (Flat.rend x nh d)        = Flat.rend (any-≈ es x) nh (done L eo es d)
flat L eo es (Flat.rpass x nh nd)      = Flat.rpass (any-≈ es x) nh λ d → nd (done L (≃-sym eo) (≈ᴸ-sym es) d)

flat-≃ : ∀ {A B : Set} (L : A → Pos → EmissionSet B) {O O′ : EmissionSet A} {d} {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′
       → Flat.JoinT L O d Ls ≃ Flat.JoinT L O′ d Ls′
flat-≃ L eo es = flat L eo es ⇄ flat L (≃-sym eo) (≈ᴸ-sym es)

map-≃ : ∀ {A B} (f : A → B) {t u : EmissionSet A} → t ≃ u → MapT f t ≃ MapT f u
map-≃ f eq = go (to eq) ⇄ go (from eq)
  where
    go : ∀ {t u} → (∀ {q e} → t q e → u q e) → ∀ {q e} → MapT f t q e → MapT f u q e
    go h (map-out r)  = map-out (h r)
    go h (map-skip r) = map-skip (h r)
    go h (map-end r)  = map-end (h r)

-- The same source and the same body: the same connect.
conn-≃ : ∀ {A B : Set} r {σ σ′ : EmissionSet A} {β β′ : EmissionSet B} → σ ≃ σ′ → β ≃ β′ → Connecting.ConnT r σ β ≃ Connecting.ConnT r σ′ β′
conn-≃ {A} {B} r es eb = go es eb ⇄ go (≃-sym es) (≃-sym eb)
  where
    go : ∀ {σ σ′ : EmissionSet A} {β β′ : EmissionSet B} → σ ≃ σ′ → β ≃ β′ → ∀ {q e} → Connecting.ConnT r σ β q e → Connecting.ConnT r σ′ β′ q e
    go es eb (Connecting.body x)           = Connecting.body (to eb x)
    go es eb (Connecting.shown x al)       = Connecting.shown (to es x) λ y → al (from eb y)
    go es eb (Connecting.pinned x nal ins) = Connecting.pinned (to es x) (λ al → nal λ y → al (to eb y)) ins

-- A BINDER'S MEANING, UP TO THE SAME ROWS: a body reads its binder only
-- through the rows it holds, so the same rows bound give the same body.
-- By induction over the state and, under a pending subscription, over
-- the program's meaning, every operator reading its inputs row by row.
postulate
  rows-hot : ∀ {Γ X B} {t u : EmissionSet X} (k : CS) (ρ : DenEnv Γ) (b : St (X ∷ Γ) B) → t ≃ u → rows (Hot t k ∷ᴬ ρ) b ≃ rows (Hot u k ∷ᴬ ρ) b

-- THE CONGRUENCE.
up-≃ : ∀ {R Γ A} (c : Ctx R Γ A) {t u : EmissionSet A} → t ≃ u → up c t ≃ up c u
up-≃ top                                              eq = eq
up-≃ (inMap f c)                                      eq = up-≃ c (map-≃ f eq)
up-≃ (inScan f z c)                                   eq = ≃-refl
up-≃ (inCut true a c)                                 eq = up-≃ c eq
up-≃ (inCut false a c)                                eq = ≃-refl
up-≃ (inLn true c)                                    eq = up-≃ c eq
up-≃ (inLn false c)                                   eq = ≃-refl
up-≃ (inTake i p w c)                                 eq = ≃-refl
up-≃ (inOuter (mergeᶠ nothing) f d n q ls c)          eq = up-≃ c (flat-≃ (λ a → pendRows (env c) (f a)) eq (≈ᴸ-refl (rowsL (env c) ls)))
up-≃ (inOuter (mergeᶠ (just _)) f d n q ls c)         eq = ≃-refl
up-≃ (inOuter switchᶠ f d n q ls c)                   eq = ≃-refl
up-≃ (inOuter exhaustᶠ f d n q ls c)                  eq = ≃-refl
up-≃ (inLanes (mergeᶠ nothing) f d n q o pre post c)  eq = up-≃ c (flat-≃ (λ a → pendRows (env c) (f a)) ≃-refl (ʳ++-≈ (rowsL (env c) pre) (eq ∷ ≈ᴸ-refl (rowsL (env c) post))))
up-≃ (inLanes (mergeᶠ (just _)) f d n q o pre post c) eq = ≃-refl
up-≃ (inLanes switchᶠ f d n q o pre post c)           eq = ≃-refl
up-≃ (inLanes exhaustᶠ f d n q o pre post c)          eq = ≃-refl
up-≃ (inSrc k b c)                                    eq = up-≃ c (conn-≃ _ eq (rows-hot k (env c) b eq))
up-≃ (inBody k o c)                                   eq = up-≃ c (conn-≃ _ ≃-refl eq)
