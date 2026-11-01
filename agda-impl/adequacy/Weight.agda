{-# OPTIONS --guardedness #-}

-- THE WEIGHT OF A SILENT RUN: what a run still has to do before its
-- clock reaches a listed position, short of `P`.  Each pending
-- subscription weighs its syntax (a defer one), by depth; each admin mark,
-- pending or owed, and each mark keyed at or before `P` at no listed
-- position, an of's every value still owed counted, its depth + 2; a
-- listed mark the clock has reached, its run: its climb and the one mark
-- it may leave, twice its depth + 4; a rise, its depth.  A mark past `P`
-- runs only once the clock has passed `P`, and a listed one ahead of the
-- clock only once the clock reaches it, so neither weighs.

-- Weighed by the clock, a still step raises no mark's weight: a listed
-- mark ahead stays ahead.
module adequacy.Weight where

open import Data.Bool using (Bool; true; false; _∧_; not; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_; _++_; [_]; length; concatMap; _ʳ++_) renaming (map to mapL)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; suc; _+_; _*_; _≤_; _<_; z≤n)
open import Data.Nat.Properties using (≤-refl; +-mono-≤; +-monoʳ-<)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Relation.Nullary using (does; yes; no)

open import Tree using (Obs; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Events using (Pos; Timeline; ix; last; _≟ᵖ_)
open import operation.Key using (Key; at; after; _<ᴷ_)
open import operation.PureObservable using (module Machine; due)
open Machine using (Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; St; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; pend; CS;
                    Conf; ⟨_,_,_,_⟩; plug; dirs; subscribing; absorbed; rising;
                    attAt; attached; free; cpAt; cutAt; overAt)

-- THE RUN'S CLOCK: the least mark due once everything is absorbed; mid-run,
-- where the run is.
Clock : ∀ {R} → Conf R → Key
Clock k with Conf.mode k | Machine.next k
... | absorbed | just κ = κ
... | _        | _      = at (Conf.pos k)

-- A listed position.
listed : List Pos → Key → Bool
listed ks (at q)    = any (λ r → does (q ≟ᵖ r)) ks
listed ks (after _) = false

-- A pending subscription to `o`, `d` deep.
syn : ∀ {Γ A} → ℕ → Obs Timeline Γ A → ℕ
syn d (cold _)          = 3 + d
syn d empty             = 3 + d
syn d (of xs)           = 3 + d + length xs * (2 + d)
syn d (map _ s)         = 1 + syn (suc d) s
syn d (scan _ _ s)      = 1 + syn (suc d) s
syn d (takeWhile _ _ s) = 1 + 2 * (2 + d) + (3 + d) + syn (2 + d) s
syn d (flatMap _ _ s)   = 1 + (3 + d) + syn (2 + d) s
syn d (connect s b)     = 1 + 3 * (2 + d) + syn (suc d) b + syn (suc d) s
syn d (connected _)     = 3 + d
syn d (defer _)         = 1

one : ℕ → Bool → ℕ
one d b = if b then 2 + d else 0

isNone : Maybe Pos → Bool
isNone nothing  = true
isNone (just _) = false

-- How deep a context's hole is.
depth : ∀ {R Γ A} → Ctx R Γ A → ℕ
depth top                       = 0
depth (inMap _ c)               = suc (depth c)
depth (inScan _ _ c)            = suc (depth c)
depth (inCut _ _ c)             = suc (depth c)
depth (inLn _ c)                = suc (depth c)
depth (inTake _ _ _ c)          = suc (depth c)
depth (inOuter _ _ _ _ _ _ c)   = suc (depth c)
depth (inLanes _ _ _ _ _ _ _ _ c) = suc (depth c)
depth (inSrc _ _ c)             = suc (depth c)
depth (inBody _ _ c)            = suc (depth c)

module Weigh (ks : List Pos) (P : Pos) (C : Key) where
  -- A mark keyed `κ`, `d` deep, the clock at `C`.
  wt : ℕ → Key → ℕ
  wt d κ = if at P <ᴷ κ then 0 else if listed ks κ then (if C <ᴷ κ then 0 else 4 + 2 * d) else 2 + d

  bodyP : ℕ → Maybe Pos → ℕ
  bodyP d (just p) = wt d (at (p ++ [ ix 1 ])) + (2 + d)
  bodyP d nothing  = 0

  -- An of's values still owed and its end.
  ofW : ∀ {A : Set} → ℕ → ℕ → Pos → List A → ℕ
  ofW d i p []       = wt d (at (p ++ [ last ]))
  ofW d i p (_ ∷ xs) = wt d (at (p ++ [ ix i ])) + ofW d (suc i) p xs

  -- A connect's admin marks, owed and pending.
  connW : ∀ {Γ X} → ℕ → CS Γ X → ℕ
  connW d k = bodyP d (CS.bodyAt k) + one d (not (isNone (CS.attSrc k))) + one d (not (isNone (CS.owedAt k)))
            + one d (CS.srcLive k ∧ isNone (CS.owedAt k))

  -- A joiner's inbox.
  inbox : ∀ {X : Set} → ℕ → List (Pos × X) → ℕ
  inbox d []             = 0
  inbox d ((q , _) ∷ es) = wt d (at q) + inbox d es

  mutual
    -- A tree `d` deep.
    pot : ∀ {Γ A} → ℕ → St Γ A → ℕ
    pot d (pend o q)               = syn d o
    pot d (coldS b l) with due l
    ... | just κ                   = wt d κ
    ... | nothing                  = 0
    pot d (ofS i p xs)             = ofW d i p xs
    pot d doneS                    = 0
    pot d (mapS _ s)               = pot (suc d) s
    pot d (scanS _ _ s)            = pot (suc d) s
    pot d (cutS _ (attAt _) s)     = (2 + d) + pot (suc d) s
    pot d (cutS _ attached s)      = pot (suc d) s
    pot d (lnS _ s)                = pot (suc d) s
    pot d (takeS _ _ free s)       = 2 * (2 + d) + pot (suc d) s
    pot d (takeS _ _ (cpAt p) s)   = wt d (at (p ++ [ last ])) + (2 + d) + pot (suc d) s
    pot d (takeS _ _ (cutAt _) s)  = (2 + d) + pot (suc d) s
    pot d (takeS _ _ (overAt _) s) = pot (suc d) s
    pot d (flatS _ _ _ _ _ o ls)   = pot (suc d) o + potL (suc d) ls
    pot d (connS k o b)            = connW d k + pot (suc d) o + pot (suc d) b
    pot d (joinS j g x ib)         = inbox d ib

    potL : ∀ {Γ A} → ℕ → List (St Γ A) → ℕ
    potL d []       = 0
    potL d (s ∷ ls) = pot d s + potL d ls

  -- Lanes reversed onto lanes.
  potL-ʳ++ : ∀ {Γ A} d (xs ys : List (St Γ A)) → potL d (xs ʳ++ ys) ≡ potL d xs + potL d ys
  potL-ʳ++ d []       ys = refl
  potL-ʳ++ d (x ∷ xs) ys = trans (potL-ʳ++ d xs (x ∷ ys)) (solve-∀-shift (potL d xs) (pot d x) (potL d ys))
    where
      solve-∀-shift : ∀ a b c → a + (b + c) ≡ (b + a) + c
      solve-∀-shift = solve-∀

  -- What a context weighs around its hole.
  potC : ∀ {R Γ A} → Ctx R Γ A → ℕ
  potC top                                = 0
  potC (inMap _ c)                        = potC c
  potC (inScan _ _ c)                     = potC c
  potC (inCut _ (attAt _) c)              = potC c + (2 + depth c)
  potC (inCut _ attached c)               = potC c
  potC (inLn _ c)                         = potC c
  potC (inTake _ _ free c)                = potC c + 2 * (2 + depth c)
  potC (inTake _ _ (cpAt p) c)            = potC c + (wt (depth c) (at (p ++ [ last ])) + (2 + depth c))
  potC (inTake _ _ (cutAt _) c)           = potC c + (2 + depth c)
  potC (inTake _ _ (overAt _) c)          = potC c
  potC (inOuter _ _ _ _ _ ls c)           = potC c + potL (suc (depth c)) ls
  potC (inLanes _ _ _ _ _ o pre post c)   = potC c + (pot (suc (depth c)) o + (potL (suc (depth c)) pre + potL (suc (depth c)) post))
  potC (inSrc k b c)                      = potC c + (connW (depth c) k + pot (suc (depth c)) b)
  potC (inBody k o c)                     = potC c + (connW (depth c) k + pot (suc (depth c)) o)

  -- A tree weighs its context around its hole and its hole at its depth.
  pot-plug : ∀ {R Γ A} (c : Ctx R Γ A) s → pot 0 (plug c s) ≡ potC c + pot (depth c) s
  pot-plug top s = refl
  pot-plug (inMap f c) s = pot-plug c (mapS f s)
  pot-plug (inScan f z c) s = pot-plug c (scanS f z s)
  pot-plug (inCut l (attAt x) c) s = trans (pot-plug c (cutS l (attAt x) s)) (a3 (potC c) (2 + depth c) (pot (suc (depth c)) s))
    where a3 : ∀ a b c → a + (b + c) ≡ (a + b) + c
          a3 = solve-∀
  pot-plug (inCut l attached c) s = pot-plug c (cutS l attached s)
  pot-plug (inLn b c) s = pot-plug c (lnS b s)
  pot-plug (inTake i q free c) s = trans (pot-plug c (takeS i q free s)) (a3 (potC c) (2 * (2 + depth c)) (pot (suc (depth c)) s))
    where a3 : ∀ a b c → a + (b + c) ≡ (a + b) + c
          a3 = solve-∀
  pot-plug (inTake i q (cpAt p) c) s =
    trans (pot-plug c (takeS i q (cpAt p) s)) (a4 (potC c) (wt (depth c) (at (p ++ [ last ]))) (2 + depth c) (pot (suc (depth c)) s))
    where a4 : ∀ a b c d → a + ((b + c) + d) ≡ (a + (b + c)) + d
          a4 = solve-∀
  pot-plug (inTake i q (cutAt x) c) s = trans (pot-plug c (takeS i q (cutAt x) s)) (a3 (potC c) (2 + depth c) (pot (suc (depth c)) s))
    where a3 : ∀ a b c → a + (b + c) ≡ (a + b) + c
          a3 = solve-∀
  pot-plug (inTake i q (overAt x) c) s = pot-plug c (takeS i q (overAt x) s)
  pot-plug (inOuter op f d n q ls c) s = trans (pot-plug c (flatS op f d n q s ls)) (sw (potC c) (pot (suc (depth c)) s) (potL (suc (depth c)) ls))
    where sw : ∀ a b c → a + (b + c) ≡ (a + c) + b
          sw = solve-∀
  pot-plug (inLanes op f d n q o pre post c) s =
    trans (pot-plug c (flatS op f d n q o (pre ʳ++ s ∷ post)))
      (trans (cong (λ x → potC c + (pot (suc (depth c)) o + x)) (potL-ʳ++ (suc (depth c)) pre (s ∷ post)))
             (ln (potC c) (pot (suc (depth c)) o) (potL (suc (depth c)) pre) (pot (suc (depth c)) s) (potL (suc (depth c)) post)))
    where ln : ∀ a b c d e → a + (b + (c + (d + e))) ≡ (a + (b + (c + e))) + d
          ln = solve-∀
  pot-plug (inSrc k b c) s = trans (pot-plug c (connS k s b)) (sw (potC c) (connW (depth c) k) (pot (suc (depth c)) s) (pot (suc (depth c)) b))
    where sw : ∀ a b c d → a + ((b + c) + d) ≡ (a + (b + d)) + c
          sw = solve-∀
  pot-plug (inBody k o c) s = trans (pot-plug c (connS k o s)) (a4 (potC c) (connW (depth c) k) (pot (suc (depth c)) o) (pot (suc (depth c)) s))
    where a4 : ∀ a b c d → a + ((b + c) + d) ≡ (a + (b + c)) + d
          a4 = solve-∀

  -- A mark strictly past the clock weighs no more than an unlisted one.
  wt-ahead : ∀ d κ → C <ᴷ κ ≡ true → wt d κ ≤ 2 + d
  wt-ahead d κ h with at P <ᴷ κ
  ... | true  = z≤n
  ... | false with listed ks κ
  ...   | true rewrite h = z≤n
  ...   | false = ≤-refl

  -- A lighter hole, a lighter tree.
  lighter-at : ∀ {R Γ A} (c : Ctx R Γ A) {s s′} → pot (depth c) s′ < pot (depth c) s → pot 0 (plug c s′) < pot 0 (plug c s)
  lighter-at c {s} {s′} lt rewrite pot-plug c s | pot-plug c s′ = +-monoʳ-< (potC c) lt

-- What the mode still owes: a rise's climb.
climb : ∀ {R} → Conf R → ℕ
climb ⟨ c , s , rising _ , _ ⟩ = length (dirs c)
climb ⟨ _ , _ , _        , _ ⟩ = 0

-- THE WEIGHT, the clock at `C`.
Wᶜ : ∀ {R} → List Pos → Pos → Key → Conf R → ℕ
Wᶜ ks P C k = Weigh.pot ks P C 0 (plug (Conf.ctx k) (Conf.foc k)) + climb k

-- THE WEIGHT.
W : ∀ {R} → List Pos → Pos → Conf R → ℕ
W ks P k = Wᶜ ks P (Clock k) k

-- Each non-empty prefix of a position, itself included.
prefixes : Pos → List Pos
prefixes []      = []
prefixes (l ∷ q) = [ l ] ∷ mapL (l ∷_) (prefixes q)

-- Each listed position and its ancestors.
anc : List Pos → List Pos
anc = concatMap prefixes

-- Each mark lighter, the whole lighter.
module Mono (ks : List Pos) (P : Pos) (C₁ C₂ : Key)
            (h : ∀ d κ → Weigh.wt ks P C₁ d κ ≤ Weigh.wt ks P C₂ d κ) where
  private
    module A = Weigh ks P C₁
    module B = Weigh ks P C₂

  bodyP-mono : ∀ d m → A.bodyP d m ≤ B.bodyP d m
  bodyP-mono d (just p) = +-mono-≤ (h d (at (p ++ [ ix 1 ]))) ≤-refl
  bodyP-mono d nothing  = z≤n

  ofW-mono : ∀ {X : Set} d i p (xs : List X) → A.ofW d i p xs ≤ B.ofW d i p xs
  ofW-mono d i p []       = h d (at (p ++ [ last ]))
  ofW-mono d i p (_ ∷ xs) = +-mono-≤ (h d (at (p ++ [ ix i ]))) (ofW-mono d (suc i) p xs)

  inbox-mono : ∀ {X : Set} d (ib : List (Pos × X)) → A.inbox d ib ≤ B.inbox d ib
  inbox-mono d []             = z≤n
  inbox-mono d ((q , _) ∷ es) = +-mono-≤ (h d (at q)) (inbox-mono d es)

  connW-mono : ∀ {Γ X} d (k : CS Γ X) → A.connW d k ≤ B.connW d k
  connW-mono d k = +-mono-≤ (+-mono-≤ (+-mono-≤ (bodyP-mono d (CS.bodyAt k)) ≤-refl) ≤-refl) ≤-refl

  mutual
    pot-mono : ∀ {Γ A} d (s : St Γ A) → A.pot d s ≤ B.pot d s
    pot-mono d (pend o q)               = ≤-refl
    pot-mono d (coldS b l) with due l
    ... | just κ                        = h d κ
    ... | nothing                       = z≤n
    pot-mono d (ofS i p xs)             = ofW-mono d i p xs
    pot-mono d doneS                    = z≤n
    pot-mono d (mapS _ s)               = pot-mono (suc d) s
    pot-mono d (scanS _ _ s)            = pot-mono (suc d) s
    pot-mono d (cutS _ (attAt _) s)     = +-mono-≤ (≤-refl {2 + d}) (pot-mono (suc d) s)
    pot-mono d (cutS _ attached s)      = pot-mono (suc d) s
    pot-mono d (lnS _ s)                = pot-mono (suc d) s
    pot-mono d (takeS _ _ free s)       = +-mono-≤ (≤-refl {2 * (2 + d)}) (pot-mono (suc d) s)
    pot-mono d (takeS _ _ (cpAt p) s)   = +-mono-≤ (+-mono-≤ (h d (at (p ++ [ last ]))) (≤-refl {2 + d})) (pot-mono (suc d) s)
    pot-mono d (takeS _ _ (cutAt _) s)  = +-mono-≤ (≤-refl {2 + d}) (pot-mono (suc d) s)
    pot-mono d (takeS _ _ (overAt _) s) = pot-mono (suc d) s
    pot-mono d (flatS _ _ _ _ _ o ls)   = +-mono-≤ (pot-mono (suc d) o) (potL-mono (suc d) ls)
    pot-mono d (connS k o b)            = +-mono-≤ (+-mono-≤ (connW-mono d k) (pot-mono (suc d) o)) (pot-mono (suc d) b)
    pot-mono d (joinS j g x ib)         = inbox-mono d ib

    potL-mono : ∀ {Γ A} d (ls : List (St Γ A)) → A.potL d ls ≤ B.potL d ls
    potL-mono d []       = z≤n
    potL-mono d (s ∷ ls) = +-mono-≤ (pot-mono d s) (potL-mono d ls)

-- A listed position is in the list.
listed-∈ : ∀ ks q → listed ks (at q) ≡ true → q ∈ ks
listed-∈ (r ∷ ks) q e with q ≟ᵖ r
... | yes refl = here refl
... | no _     = there (listed-∈ ks q e)

-- A clock keeping every listed position ahead that was: no mark heavier.
wt-kept : ∀ ks P {C C′} → (∀ {q} → q ∈ ks → C <ᴷ at q ≡ true → C′ <ᴷ at q ≡ true)
        → ∀ d κ → Weigh.wt ks P C′ d κ ≤ Weigh.wt ks P C d κ
wt-kept ks P h d (after r) with at P <ᴷ after r
... | true  = z≤n
... | false = ≤-refl
wt-kept ks P {C} {C′} h d (at q) with at P <ᴷ at q
... | true  = z≤n
... | false with listed ks (at q) in e
...   | false = ≤-refl
...   | true with C <ᴷ at q in c
...     | true rewrite h (listed-∈ ks q e) c = z≤n
...     | false with C′ <ᴷ at q
...       | true  = z≤n
...       | false = ≤-refl

Wᶜ-kept : ∀ {R} ks P {C C′} → (∀ {q} → q ∈ ks → C <ᴷ at q ≡ true → C′ <ᴷ at q ≡ true)
        → (k : Conf R) → Wᶜ ks P C′ k ≤ Wᶜ ks P C k
Wᶜ-kept ks P {C} {C′} h k =
  +-mono-≤ (Mono.pot-mono ks P C′ C (λ d κ → wt-kept ks P {C} {C′} h d κ) 0 (plug (Conf.ctx k) (Conf.foc k))) (≤-refl {climb k})
