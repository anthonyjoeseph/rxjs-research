{-# OPTIONS --guardedness #-}

-- WHAT THE ROOT OWES RESPECTS THE ROWS: the same rows in the hole, the
-- same rows at the root, frame by frame.  A merge's lanes are matched
-- index by index, so a lane's rows replaced in its list is the same merge.
module adequacy.Direct.Up where

open import Data.Bool using (true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _ʳ++_; lookup; length)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Pos)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; MapT; map-out; map-skip; map-end)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Direct using (up; rows; rowsL; pendRows; Gone; module Flat; _≃_; _⇄_; ≃-sym)

open _≃_

≃-refl : ∀ {A} {t : EmissionSet A} → t ≃ t
≃-refl = (λ x → x) ⇄ (λ x → x)

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

idx : ∀ {B} {Ls Ls′ : List (EmissionSet B)} → Ls ≈ᴸ Ls′ → Fin (length Ls) → Fin (length Ls′)
idx (_ ∷ _)  zero    = zero
idx (_ ∷ es) (suc i) = suc (idx es i)

lk : ∀ {B} {Ls Ls′ : List (EmissionSet B)} (es : Ls ≈ᴸ Ls′) i → lookup Ls i ≃ lookup Ls′ (idx es i)
lk (e ∷ _)  zero    = e
lk (_ ∷ es) (suc i) = lk es i

Gone-≃ : ∀ {X} {t u : EmissionSet X} {c} → t ≃ u → Gone t c → Gone u c
Gone-≃ eq (inj₁ n)            = inj₁ λ r → n (from eq r)
Gone-≃ eq (inj₂ (c′ , r , le)) = inj₂ (c′ , to eq r , le)

-- The same outer and the same lanes: the same merge.
done : ∀ {A B : Set} (L : A → Pos → EmissionSet B) {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′
     → ∀ {c} → Flat.Done L O Ls c → Flat.Done L O′ Ls′ c
done L eo es {c} (g , h , ls) = Gone-≃ {c = c} eo g , (λ r lt → h (from eo r) lt)
                              , λ j → Gone-≃ {c = c} (≃-sym (lk (≈ᴸ-sym es) j)) (ls (idx (≈ᴸ-sym es) j))

flat : ∀ {A B : Set} (L : A → Pos → EmissionSet B) {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′
     → ∀ {q e} → Flat.FlatR L O Ls q e → Flat.FlatR L O′ Ls′ q e
flat L eo es (Flat.val r)        = Flat.val (to eo r)
flat L eo es (Flat.step r)       = Flat.step (to eo r)
flat L eo es (Flat.oend r d)     = Flat.oend (to eo r) (done L eo es d)
flat L eo es (Flat.opass r nd)   = Flat.opass (to eo r) λ d → nd (done L (≃-sym eo) (≈ᴸ-sym es) d)
flat L eo es (Flat.lane r l w)   = Flat.lane (to eo r) l w
flat L eo es (Flat.lend r l d)   = Flat.lend (to eo r) l (done L eo es d)
flat L eo es (Flat.lpass r l nd) = Flat.lpass (to eo r) l λ d → nd (done L (≃-sym eo) (≈ᴸ-sym es) d)
flat L eo es (Flat.run i r w)    = Flat.run (idx es i) (to (lk es i) r) w
flat L eo es (Flat.rend i r d)   = Flat.rend (idx es i) (to (lk es i) r) (done L eo es d)
flat L eo es (Flat.rpass i r nd) = Flat.rpass (idx es i) (to (lk es i) r) λ d → nd (done L (≃-sym eo) (≈ᴸ-sym es) d)

flat-≃ : ∀ {A B : Set} (L : A → Pos → EmissionSet B) {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′
       → Flat.FlatR L O Ls ≃ Flat.FlatR L O′ Ls′
flat-≃ L eo es = flat L eo es ⇄ flat L (≃-sym eo) (≈ᴸ-sym es)

map-≃ : ∀ {A B} (f : A → B) {t u : EmissionSet A} → t ≃ u → MapT f t ≃ MapT f u
map-≃ f eq = go (to eq) ⇄ go (from eq)
  where
    go : ∀ {t u} → (∀ {q e} → t q e → u q e) → ∀ {q e} → MapT f t q e → MapT f u q e
    go h (map-out r)  = map-out (h r)
    go h (map-skip r) = map-skip (h r)
    go h (map-end r)  = map-end (h r)

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
up-≃ (inOuter (mergeᶠ nothing) f d n q ls c)          eq = up-≃ c (flat-≃ _ eq (≈ᴸ-refl (rowsL ls)))
up-≃ (inOuter (mergeᶠ (just _)) f d n q ls c)         eq = ≃-refl
up-≃ (inOuter switchᶠ f d n q ls c)                   eq = ≃-refl
up-≃ (inOuter exhaustᶠ f d n q ls c)                  eq = ≃-refl
up-≃ (inLanes (mergeᶠ nothing) f d n q o pre post c)  eq = up-≃ c (flat-≃ _ ≃-refl (ʳ++-≈ (rowsL pre) (eq ∷ ≈ᴸ-refl (rowsL post))))
up-≃ (inLanes (mergeᶠ (just _)) f d n q o pre post c) eq = ≃-refl
up-≃ (inLanes switchᶠ f d n q o pre post c)           eq = ≃-refl
up-≃ (inLanes exhaustᶠ f d n q o pre post c)          eq = ≃-refl
up-≃ (inSrc k b c)                                    eq = ≃-refl
up-≃ (inBody k o c)                                   eq = ≃-refl
