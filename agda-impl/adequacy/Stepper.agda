{-# OPTIONS --guardedness #-}

-- THE STEPPER IS THE MEANING, skips aside, node by node.  A node inside
-- a connect's body reads its connects' sources as their runs from where
-- they stand (`ρᴱ`), and its step is the run's next event only if it
-- comes before each running source's (`First`), as a connect's step
-- decides.  Then its meaning is what its step shows, then the meaning of
-- the node it leaves (`os`).
module adequacy.Stepper where

open import Data.Bool using (Bool; true; false; not)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst)

import Tree as T
open import Tree using (Later)
open import denotation.MonotonicList using (Events; Events∞; Pos; From; Frame; Timeline; out; skip; end; hush; ix; _<ᵖ_; Agree; out⁼; skip⁼; end⁼; hush⁼; agree; <ᵖ-trans; <ᵖ-below; <ᵖ-irrefl)
  renaming (sub to subᴾ)
import denotation.MonotonicList as M
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import adequacy.Sane using (Sane; Saneᴹ; Saneᴸ; Told)
open import adequacy.Placed using (Atop; Ordered; ordered; Placed; Within; Placedᴹ; Placedᴸ)

open Events∞

------------------------------------------------------------------------
-- Alike skips aside: the same values and ends in the same order, finitely
-- many skips between them on either side, or both skipping for ever.

mutual
  data _∼_ {A : Set} : Events A → Events A → Set where
    out∼  : ∀ {k a l r} → force l ∼∞ force r → out k a l ∼ out k a r
    end∼  : ∀ {k} → end k ∼ end k
    hush∼ : hush ∼ hush
    skip∼ : ∀ {k k′ l r} → force l ∼∞ force r → skip k l ∼ skip k′ r
    skipˡ : ∀ {k l y} → force l ∼ y → skip k l ∼ y
    skipʳ : ∀ {x k r} → x ∼ force r → x ∼ skip k r

  record _∼∞_ {A : Set} (x y : Events A) : Set where
    coinductive
    field ∼force : x ∼ y

open _∼∞_

mutual
  ∼-sym : ∀ {A} {x y : Events A} → x ∼ y → y ∼ x
  ∼-sym (out∼ r)  = out∼ (∼∞-sym r)
  ∼-sym end∼      = end∼
  ∼-sym hush∼     = hush∼
  ∼-sym (skip∼ r) = skip∼ (∼∞-sym r)
  ∼-sym (skipˡ r) = skipʳ (∼-sym r)
  ∼-sym (skipʳ r) = skipˡ (∼-sym r)

  ∼∞-sym : ∀ {A} {x y : Events A} → x ∼∞ y → y ∼∞ x
  ∼force (∼∞-sym r) = ∼-sym (∼force r)

mutual
  ∼-refl : ∀ {A} (x : Events A) → x ∼ x
  ∼-refl (out k a r) = out∼ (∼∞-refl (force r))
  ∼-refl (skip k r)  = skip∼ (∼∞-refl (force r))
  ∼-refl (end k)     = end∼
  ∼-refl hush        = hush∼

  ∼∞-refl : ∀ {A} (x : Events A) → x ∼∞ x
  ∼force (∼∞-refl x) = ∼-refl x

postulate
  -- Weak bisimilarity is transitive.
  --
  -- DEAD ROUTE: the direct proof by guarded corecursion with an inductive
  --   inner recursion.  A skip matched on the left and unmatched on the
  --   right recurses on the right's premise with the left's coinductive
  --   tail, and the mirror case does the reverse; the size-change check
  --   composes the two into a call that decreases nothing.
  ∼-trans : ∀ {A} {x y z : Events A} → x ∼ y → y ∼ z → x ∼ z

-- The events run for ever, every one before `v`.
mutual
  Stays : ∀ {A} → Pos → Events A → Set
  Stays v (out k _ r) = k <ᵖ v ≡ true × Stalls v (force r)
  Stays v (skip k r)  = k <ᵖ v ≡ true × Stalls v (force r)
  Stays v (end _)     = ⊥
  Stays v hush        = ⊥

  record Stalls {A} (v : Pos) (e : Events A) : Set where
    coinductive
    field stays : Stays v e

open Stalls

-- Alike, and stalling below the same positions.  A merge orders by
-- position, skips included (`M.beside`, `M.go`): a run of skips that never
-- passes `v` holds back whatever the other side has at `v`, so the two
-- stall alike; and it respects the relation only between sorted events.
--
-- REFUTED: 0af1ff0e M.beside respecting `∼` alone, by a source spinning below the body's value
-- REFUTED: d09ec415 M.beside respecting it between unsorted events, by an unmatched skip above the value after it
-- REFUTED: bb8f23b3 a matched skip kept in place, in place of `Stalls`, by two runs of skips each alike their interleaving
-- DEAD ROUTE: an unmatched skip bounded by the event after it, in place
--   of sortedness.  Not transitive: a skip matched on one side above an
--   unmatched one on the other is unbounded once the middle is dropped.
record _≃_ {A : Set} (x y : Events A) : Set where
  field
    alike  : x ∼ y
    stalls : ∀ v → (Stalls v x → Stalls v y) × (Stalls v y → Stalls v x)

open _≃_

≃-refl : ∀ {A} (x : Events A) → x ≃ x
≃-refl x = record { alike = ∼-refl x ; stalls = λ v → id , id }

≃-trans : ∀ {A} {x y z : Events A} → x ≃ y → y ≃ z → x ≃ z
≃-trans p q = record
  { alike  = ∼-trans (alike p) (alike q)
  ; stalls = λ v → (λ s → proj₁ (stalls q v) (proj₁ (stalls p v) s)) , (λ s → proj₂ (stalls p v) (proj₂ (stalls q v) s)) }

-- One event, then tails that force alike.
out-same : ∀ {A k a} {l r : Events∞ A} → force l ≡ force r → out k a l ≃ out k a r
out-same {l = l} e = record
  { alike  = out∼ (record { ∼force = subst (force l ∼_) e (∼-refl (force l)) })
  ; stalls = λ v → (λ s → record { stays = proj₁ (stays s) , subst (Stalls v) e (proj₂ (stays s)) })
                 , (λ s → record { stays = proj₁ (stays s) , subst (Stalls v) (sym e) (proj₂ (stays s)) }) }

skip-same : ∀ {A k} {l r : Events∞ A} → force l ≡ force r → skip k l ≃ skip k r
skip-same {l = l} e = record
  { alike  = skip∼ (record { ∼force = subst (force l ∼_) e (∼-refl (force l)) })
  ; stalls = λ v → (λ s → record { stays = proj₁ (stays s) , subst (Stalls v) e (proj₂ (stays s)) })
                 , (λ s → record { stays = proj₁ (stays s) , subst (Stalls v) (sym e) (proj₂ (stays s)) }) }

------------------------------------------------------------------------
-- The stream functions respect it

mutual
  mapᴱ-∼ : ∀ {A B} (f : A → B) {x y : Events A} → x ∼ y → M.mapᴱ f x ∼ M.mapᴱ f y
  mapᴱ-∼ f (out∼ r)  = out∼ (mapᴱ-∼∞ f r)
  mapᴱ-∼ f end∼      = end∼
  mapᴱ-∼ f hush∼     = hush∼
  mapᴱ-∼ f (skip∼ r) = skip∼ (mapᴱ-∼∞ f r)
  mapᴱ-∼ f (skipˡ r) = skipˡ (mapᴱ-∼ f r)
  mapᴱ-∼ f (skipʳ r) = skipʳ (mapᴱ-∼ f r)

  mapᴱ-∼∞ : ∀ {A B} (f : A → B) {x y : Events A} → x ∼∞ y → M.mapᴱ f x ∼∞ M.mapᴱ f y
  ∼force (mapᴱ-∼∞ f r) = mapᴱ-∼ f (∼force r)

map-stalls : ∀ {A B} (f : A → B) {v} (x : Events A) → Stalls v x → Stalls v (M.mapᴱ f x)
stays (map-stalls f (out k a r) s) = proj₁ (stays s) , map-stalls f (force r) (proj₂ (stays s))
stays (map-stalls f (skip k r)  s) = proj₁ (stays s) , map-stalls f (force r) (proj₂ (stays s))
stays (map-stalls f (end k)     s) = stays s
stays (map-stalls f hush        s) = stays s

map-stalls⁻ : ∀ {A B} (f : A → B) {v} (x : Events A) → Stalls v (M.mapᴱ f x) → Stalls v x
stays (map-stalls⁻ f (out k a r) s) = proj₁ (stays s) , map-stalls⁻ f (force r) (proj₂ (stays s))
stays (map-stalls⁻ f (skip k r)  s) = proj₁ (stays s) , map-stalls⁻ f (force r) (proj₂ (stays s))
stays (map-stalls⁻ f (end k)     s) = stays s
stays (map-stalls⁻ f hush        s) = stays s

mapᴱ-≃ : ∀ {A B} (f : A → B) {x y : Events A} → x ≃ y → M.mapᴱ f x ≃ M.mapᴱ f y
mapᴱ-≃ f {x} {y} p = record
  { alike  = mapᴱ-∼ f (alike p)
  ; stalls = λ v → (λ s → map-stalls f y (proj₁ (stalls p v) (map-stalls⁻ f x s)))
                 , (λ s → map-stalls f x (proj₂ (stalls p v) (map-stalls⁻ f y s))) }

mutual
  scanᴱ-∼ : ∀ {A B} (f : B → A → B) z {x y : Events A} → x ∼ y → M.scanᴱ f z x ∼ M.scanᴱ f z y
  scanᴱ-∼ f z (out∼ r)  = out∼ (scanᴱ-∼∞ f _ r)
  scanᴱ-∼ f z end∼      = end∼
  scanᴱ-∼ f z hush∼     = hush∼
  scanᴱ-∼ f z (skip∼ r) = skip∼ (scanᴱ-∼∞ f z r)
  scanᴱ-∼ f z (skipˡ r) = skipˡ (scanᴱ-∼ f z r)
  scanᴱ-∼ f z (skipʳ r) = skipʳ (scanᴱ-∼ f z r)

  scanᴱ-∼∞ : ∀ {A B} (f : B → A → B) z {x y : Events A} → x ∼∞ y → M.scanᴱ f z x ∼∞ M.scanᴱ f z y
  ∼force (scanᴱ-∼∞ f z r) = scanᴱ-∼ f z (∼force r)

scan-stalls : ∀ {A B} (f : B → A → B) z {v} (x : Events A) → Stalls v x → Stalls v (M.scanᴱ f z x)
stays (scan-stalls f z (out k a r) s) = proj₁ (stays s) , scan-stalls f (f z a) (force r) (proj₂ (stays s))
stays (scan-stalls f z (skip k r)  s) = proj₁ (stays s) , scan-stalls f z (force r) (proj₂ (stays s))
stays (scan-stalls f z (end k)     s) = stays s
stays (scan-stalls f z hush        s) = stays s

scan-stalls⁻ : ∀ {A B} (f : B → A → B) z {v} (x : Events A) → Stalls v (M.scanᴱ f z x) → Stalls v x
stays (scan-stalls⁻ f z (out k a r) s) = proj₁ (stays s) , scan-stalls⁻ f (f z a) (force r) (proj₂ (stays s))
stays (scan-stalls⁻ f z (skip k r)  s) = proj₁ (stays s) , scan-stalls⁻ f z (force r) (proj₂ (stays s))
stays (scan-stalls⁻ f z (end k)     s) = stays s
stays (scan-stalls⁻ f z hush        s) = stays s

scanᴱ-≃ : ∀ {A B} (f : B → A → B) z {x y : Events A} → x ≃ y → M.scanᴱ f z x ≃ M.scanᴱ f z y
scanᴱ-≃ f z {x} {y} p = record
  { alike  = scanᴱ-∼ f z (alike p)
  ; stalls = λ v → (λ s → scan-stalls f z y (proj₁ (stalls p v) (scan-stalls⁻ f z x s)))
                 , (λ s → scan-stalls f z x (proj₂ (stalls p v) (scan-stalls⁻ f z y s))) }

postulate
  -- `M.takeWhileᴱ` respects the relation: it cuts both at the same value,
  -- and one stalls uncut exactly when the other does.
  takeWhileᴱ-≃ : ∀ {A} i (p : A → Bool) {x y : Events A} → x ≃ y → M.takeWhileᴱ i p x ≃ M.takeWhileᴱ i p y

------------------------------------------------------------------------
-- The connects in scope

-- Each connect's source: running, or ended where.
data Env : List Set → Set₁ where
  []  : Env []
  _∷_ : ∀ {Γ A} → U.Source Γ A → Env Γ → Env (A ∷ Γ)

-- Each source's run from where it stands, as the meaning reads it.
ρᴱ : ∀ {Γ} → Env Γ → NEnv Γ
ρᴱ []              = []ᴬ
ρᴱ (U.live s  ∷ δ) = U.meaning s (ρᴱ δ) ∷ᴬ ρᴱ δ
ρᴱ (U.ended c ∷ δ) = end c ∷ᴬ ρᴱ δ

flags : ∀ {Γ} → Env Γ → All (λ _ → Bool) Γ
flags []              = []ᴬ
flags (U.live _  ∷ δ) = true ∷ᴬ flags δ
flags (U.ended _ ∷ δ) = false ∷ᴬ flags δ

-- What a step shows, then the meaning of the node it leaves.
afterᴱ : ∀ {Γ A} → NEnv Γ → U.Step Γ A → Events A
afterᴱ ρ (U.outˢ k a c′) = out k a λ where .force → U.meaning c′ ρ
afterᴱ ρ (U.skipˢ k c′)  = skip k λ where .force → U.meaning c′ ρ
afterᴱ ρ (U.endˢ k)      = end k
afterᴱ ρ U.hushˢ         = hush

-- A step at `k` is taken before a source's next at `q`, as `U.sourceˢ`
-- decides: a silent source never comes first, a silent body never does.
Wins : Maybe Pos → Maybe Pos → Bool
Wins k        nothing  = true
Wins nothing  (just q) = false
Wins (just k) (just q) = not ((q ++ [ ix 0 ]) <ᵖ k)

First : ∀ {Γ} → Maybe Pos → Env Γ → Set
First k []              = ⊤
First k (U.live s  ∷ δ) = Wins k (U.headˢ (U.step s)) ≡ true × First k δ
First k (U.ended _ ∷ δ) = First k δ

-- The node, its meaning read in `δ`, is what its step shows whenever
-- that step comes first.
Shows : ∀ {Γ A} → U.Node Γ A → Env Γ → Set
Shows c δ = First (U.headˢ (U.step c)) δ → U.meaning c (ρᴱ δ) ≃ afterᴱ (ρᴱ δ) (U.step c)

-- Every running source shows its step, and is placed.
Settled : ∀ {Γ} → Env Γ → Set
Settled []              = ⊤
Settled (U.live s  ∷ δ) = Shows s δ × Placed s (ρᴱ δ) × Settled δ
Settled (U.ended _ ∷ δ) = Settled δ

------------------------------------------------------------------------
-- Node by node

frames-after : ∀ {Γ A t} τ e (m : From A t) {ρ : NEnv Γ} → M.frames τ e m ≃ afterᴱ ρ (U.framesˢ τ e m)
burst-after : ∀ {Γ A t} τ r i (b : Frame A t) {ρ : NEnv Γ} → M.burst τ r i b ≃ afterᴱ ρ (U.burstˢ τ r i b)
frames-after τ e M.done       = ≃-refl (end e)
frames-after τ e M.quiet      = ≃-refl hush
frames-after τ e (M.at t _ b) = burst-after τ _ 0 b
burst-after τ r i (M.emit a k) = out-same refl
burst-after τ r i (M.stall k)  = skip-same refl
burst-after τ r i (M.close k)  = skip-same refl

of-after : ∀ {Γ A} p i (xs : List A) {ρ : NEnv Γ} → M.ofᴱ p i xs ≃ afterᴱ ρ (U.ofˢ p i xs)
of-after p i []       = ≃-refl (end _)
of-after p i (x ∷ xs) = out-same refl

map-head : ∀ {Γ A B} (f : A → B) (s : U.Step Γ A) → U.headˢ (U.mapˢ f s) ≡ U.headˢ s
map-head f (U.outˢ k a c) = refl
map-head f (U.skipˢ k c)  = refl
map-head f (U.endˢ k)     = refl
map-head f U.hushˢ        = refl

map-after : ∀ {Γ A B} (f : A → B) {ρ : NEnv Γ} (s : U.Step Γ A) → M.mapᴱ f (afterᴱ ρ s) ≃ afterᴱ ρ (U.mapˢ f s)
map-after f (U.outˢ k a c) = out-same refl
map-after f (U.skipˢ k c)  = skip-same refl
map-after f (U.endˢ k)     = ≃-refl (end k)
map-after f U.hushˢ        = ≃-refl hush

scan-head : ∀ {Γ A B} (f : B → A → B) z (s : U.Step Γ A) → U.headˢ (U.scanˢ f z s) ≡ U.headˢ s
scan-head f z (U.outˢ k a c) = refl
scan-head f z (U.skipˢ k c)  = refl
scan-head f z (U.endˢ k)     = refl
scan-head f z U.hushˢ        = refl

scan-after : ∀ {Γ A B} (f : B → A → B) z {ρ : NEnv Γ} (s : U.Step Γ A) → M.scanᴱ f z (afterᴱ ρ s) ≃ afterᴱ ρ (U.scanˢ f z s)
scan-after f z (U.outˢ k a c) = out-same refl
scan-after f z (U.skipˢ k c)  = skip-same refl
scan-after f z (U.endˢ k)     = ≃-refl (end k)
scan-after f z U.hushˢ        = ≃-refl hush

-- A cut value's step sits at or past it, so a step that comes first
-- before the cut still does.
postulate
  take-first : ∀ {Γ A} i (p : A → Bool) (s : U.Step Γ A) (δ : Env Γ) → First (U.headˢ (U.takeWhileˢ i p s)) δ → First (U.headˢ s) δ

take-after : ∀ {Γ A} i (p : A → Bool) {ρ : NEnv Γ} (s : U.Step Γ A) → M.takeWhileᴱ i p (afterᴱ ρ s) ≃ afterᴱ ρ (U.takeWhileˢ i p s)
take-after i p (U.outˢ k a c) with p a
take-after i     p (U.outˢ k a c) | true  = out-same refl
take-after true  p (U.outˢ k a c) | false = out-same refl
take-after false p (U.outˢ k a c) | false = ≃-refl (end _)
take-after i p (U.skipˢ k c) = skip-same refl
take-after i p (U.endˢ k)    = ≃-refl (end k)
take-after i p U.hushˢ       = ≃-refl hush

-- An untold joiner's step is silent only when its source's is.
postulate
  -- A joiner untold and fed nothing, every running source silent: it
  -- shows nothing.
  join-quiet : ∀ {Γ A} (i : A ∈ Γ) p (δ : Env Γ) → Settled δ → Told (lookup (flags δ) i) nothing → First nothing δ
             → M.rejoin p 0 (lookup (ρᴱ δ) i) ≃ hush

join-after : ∀ {Γ A} (i : A ∈ Γ) p xs e (δ : Env Γ) → Settled δ → Told (lookup (flags δ) i) e → First (U.headˢ (U.joinˢ i p xs e)) δ
           → U.meaning (U.joinᶜ i p xs e) (ρᴱ δ) ≃ afterᴱ (ρᴱ δ) (U.joinˢ i p xs e)
join-after i p ((q , a) ∷ xs) e        δ st t fi = out-same refl
join-after i p []             (just c) δ st t fi = ≃-refl (end c)
join-after i p []             nothing  δ st t fi = join-quiet i p δ st t fi

-- Each lane in flight, or the outer, shows its step.
Showsᴹ : ∀ {Γ A} → Maybe (U.Node Γ A) → Env Γ → Set
Showsᴹ nothing  δ = ⊤
Showsᴹ (just c) δ = Shows c δ

Showsᴸ : ∀ {Γ A} → List (U.Node Γ A) → Env Γ → Set
Showsᴸ []       δ = ⊤
Showsᴸ (c ∷ cs) δ = Shows c δ × Showsᴸ cs δ

postulate
  -- THE MERGE STEPS AS THE MERGE MEANS: the outer and each lane in flight
  -- showing its step whenever it comes first, a flatMap's meaning is what
  -- its step shows.
  go-skips : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) o ls qs (δ : Env Γ) → Settled δ
           → Sane (flags δ) (U.flatMapᶜ op g o ls qs) → Placed (U.flatMapᶜ op g o ls qs) (ρᴱ δ)
           → Showsᴹ o δ → Showsᴸ ls δ → Shows (U.flatMapᶜ op g o ls qs) δ

  -- A DEFER STEPS AS IT MEANS: one skip, then the program it defers
  -- subscribed, as the fold's meaning of it.
  defer-after : ∀ {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) → U.meaning (U.deferᶜ l p) ρ ≃ afterᴱ ρ (U.step (U.deferᶜ l p))

-- `same?` answers yes only for one index.
same-≡ : ∀ {Γ : List Set} {A : Set} (i j : A ∈ Γ) → U.same? i j ≡ just refl → i ≡ j
same-≡ (here refl) (here refl) e = refl
same-≡ (there i)   (there j)   e = cong there (same-≡ i j e)
same-≡ (here refl) (there j)   ()
same-≡ (there i)   (here refl) ()

-- Telling a joiner its source's end changes nothing it means once the
-- source has ended there.
shut-join : ∀ {Γ A B} {ρ : NEnv Γ} (i : A ∈ Γ) c (j : B ∈ Γ) p e → lookup ρ i ≡ end c
          → U.joined j p (U.told i c j p e (U.same? i j)) ρ ≡ U.joined j p e ρ
shut-join i c j p (just e) l with U.same? i j
... | just refl = refl
... | nothing   = refl
shut-join {ρ = ρ} i c j p nothing l with U.same? i j in eq
... | nothing   = refl
... | just refl with same-≡ i j eq
... | refl rewrite l with p <ᵖ c
... | true  = refl
... | false = refl

mutual
  shut-meaning : ∀ {Γ A B} (i : A ∈ Γ) c (n : U.Node Γ B) (ρ : NEnv Γ) → lookup ρ i ≡ end c → U.meaning (U.shut i c n) ρ ≡ U.meaning n ρ
  shut-meaning i c (U.framesᶜ τ e m)         ρ l = refl
  shut-meaning i c (U.burstᶜ τ r k b)        ρ l = refl
  shut-meaning i c (U.endᶜ p)                ρ l = refl
  shut-meaning i c (U.ofᶜ p k xs)            ρ l = refl
  shut-meaning i c (U.mapᶜ f n)              ρ l = cong (M.mapᴱ f) (shut-meaning i c n ρ l)
  shut-meaning i c (U.scanᶜ f z n)           ρ l = cong (M.scanᴱ f z) (shut-meaning i c n ρ l)
  shut-meaning i c (U.takeWhileᶜ k p n)      ρ l = cong (M.takeWhileᴱ k p) (shut-meaning i c n ρ l)
  shut-meaning i c (U.flatMapᶜ op g o ls qs) ρ l
    rewrite shut-meaningᴹ i c o ρ l | shut-meanings i c ls ρ l = refl
  shut-meaning i c (U.joinᶜ j p xs e)        ρ l = cong (U.fedᴺ xs) (shut-join i c j p e l)
  shut-meaning i c (U.connectᶜ b (U.live s)) ρ l
    rewrite shut-meaning i c s ρ l | shut-meaning (there i) c b (U.meaning s ρ ∷ᴬ ρ) l = refl
  shut-meaning i c (U.connectᶜ b (U.ended e)) ρ l = shut-meaning (there i) c b (end e ∷ᴬ ρ) l
  shut-meaning i c (U.deferᶜ k p)            ρ l = refl

  shut-meaningᴹ : ∀ {Γ A B} (i : A ∈ Γ) c (o : Maybe (U.Node Γ B)) (ρ : NEnv Γ) → lookup ρ i ≡ end c → U.meaningᴹ (U.shutᴹ i c o) ρ ≡ U.meaningᴹ o ρ
  shut-meaningᴹ i c nothing  ρ l = refl
  shut-meaningᴹ i c (just n) ρ l = cong just (shut-meaning i c n ρ l)

  shut-meanings : ∀ {Γ A B} (i : A ∈ Γ) c (ns : List (U.Node Γ B)) (ρ : NEnv Γ) → lookup ρ i ≡ end c → U.meanings (U.shutᴸ i c ns) ρ ≡ U.meanings ns ρ
  shut-meanings i c []       ρ l = refl
  shut-meanings i c (n ∷ ns) ρ l = cong₂ _∷_ (shut-meaning i c n ρ l) (shut-meanings i c ns ρ l)

shut-head : ∀ {Γ A B} c (s : U.Step (A ∷ Γ) B) → U.headˢ (U.shutˢᵗ c s) ≡ U.headˢ s
shut-head c (U.outˢ k a b) = refl
shut-head c (U.skipˢ k b)  = refl
shut-head c (U.endˢ e)     = refl
shut-head c U.hushˢ        = refl

shut-after : ∀ {Γ A B} c {ρ : NEnv Γ} (s : U.Step (A ∷ Γ) B) → afterᴱ (end c ∷ᴬ ρ) s ≃ afterᴱ ρ (U.shutˢᵗ c s)
shut-after c {ρ} (U.outˢ k a b) = out-same (sym (shut-meaning (here refl) c b (end c ∷ᴬ ρ) refl))
shut-after c {ρ} (U.skipˢ k b)  = skip-same (sym (shut-meaning (here refl) c b (end c ∷ᴬ ρ) refl))
shut-after c (U.endˢ e)         = ≃-refl (end e)
shut-after c U.hushˢ            = ≃-refl hush

mutual
  shut-placed : ∀ {Γ A B} (i : A ∈ Γ) c (n : U.Node Γ B) (ρ : NEnv Γ) → lookup ρ i ≡ end c → Placed (U.shut i c n) ρ → Placed n ρ
  shut-placed i c n ρ l (o , w) = subst Ordered (shut-meaning i c n ρ l) o , shut-within i c n ρ l w

  shut-within : ∀ {Γ A B} (i : A ∈ Γ) c (n : U.Node Γ B) (ρ : NEnv Γ) → lookup ρ i ≡ end c → Within (U.shut i c n) ρ → Within n ρ
  shut-within i c (U.framesᶜ τ e m)         ρ l w = w
  shut-within i c (U.burstᶜ τ r k b)        ρ l w = w
  shut-within i c (U.endᶜ p)                ρ l w = w
  shut-within i c (U.ofᶜ p k xs)            ρ l w = w
  shut-within i c (U.mapᶜ f n)              ρ l w = shut-placed i c n ρ l w
  shut-within i c (U.scanᶜ f z n)           ρ l w = shut-placed i c n ρ l w
  shut-within i c (U.takeWhileᶜ k p n)      ρ l w = shut-placed i c n ρ l w
  shut-within i c (U.flatMapᶜ op g o ls qs) ρ l (wo , wl) = shut-placedᴹ i c o ρ l wo , shut-placedᴸ i c ls ρ l wl
  shut-within i c (U.joinᶜ j p xs e)        ρ l w = tt
  shut-within i c (U.connectᶜ b (U.live s)) ρ l (wb , ws) =
    shut-placed (there i) c b (U.meaning s ρ ∷ᴬ ρ) l (subst (λ x → Placed (U.shut (there i) c b) (x ∷ᴬ ρ)) (shut-meaning i c s ρ l) wb)
    , shut-placed i c s ρ l ws
  shut-within i c (U.connectᶜ b (U.ended e)) ρ l w = shut-placed (there i) c b (end e ∷ᴬ ρ) l w
  shut-within i c (U.deferᶜ k p)            ρ l w = w

  shut-placedᴹ : ∀ {Γ A B} (i : A ∈ Γ) c (o : Maybe (U.Node Γ B)) (ρ : NEnv Γ) → lookup ρ i ≡ end c → Placedᴹ (U.shutᴹ i c o) ρ → Placedᴹ o ρ
  shut-placedᴹ i c nothing  ρ l w = tt
  shut-placedᴹ i c (just n) ρ l w = shut-placed i c n ρ l w

  shut-placedᴸ : ∀ {Γ A B} (i : A ∈ Γ) c (ns : List (U.Node Γ B)) (ρ : NEnv Γ) → lookup ρ i ≡ end c → Placedᴸ (U.shutᴸ i c ns) ρ → Placedᴸ ns ρ
  shut-placedᴸ i c []       ρ l w        = tt
  shut-placedᴸ i c (n ∷ ns) ρ l (wn , ws) = shut-placed i c n ρ l wn , shut-placedᴸ i c ns ρ l ws

------------------------------------------------------------------------
-- A running connect

≃-sym : ∀ {A} {x y : Events A} → x ≃ y → y ≃ x
≃-sym p = record { alike = ∼-sym (alike p) ; stalls = λ v → proj₂ (stalls p v) , proj₁ (stalls p v) }

skip-cong : ∀ {A k} {l r : Events∞ A} → force l ≃ force r → skip k l ≃ skip k r
skip-cong p = record
  { alike  = skip∼ (record { ∼force = alike p })
  ; stalls = λ v → (λ s → record { stays = proj₁ (stays s) , proj₁ (stalls p v) (proj₂ (stays s)) })
                 , (λ s → record { stays = proj₁ (stays s) , proj₂ (stalls p v) (proj₂ (stays s)) }) }

-- The events' first is taken after a body's event at `k`.
Lags : ∀ {A} → Pos → Events A → Set
Lags k (out h _ _) = (h ++ [ ix 0 ]) <ᵖ k ≡ false
Lags k (skip h _)  = (h ++ [ ix 0 ]) <ᵖ k ≡ false
Lags k (end _)     = ⊤
Lags k hush        = ⊤

-- The source's next taken after the body's, or before it.
ahead-out : ∀ {A B} k (a : B) (r : Events∞ B) q (t : Events∞ A) b (r′ : Events∞ B) → b ≡ false
          → force r′ ≡ M.ahead (force r) q t (M.before q (force r)) → M.ahead (out k a r) q t b ≃ out k a r′
ahead-out k a r q t .false r′ refl e = out-same (sym e)

ahead-skip : ∀ {A B} k (r : Events∞ B) q (t : Events∞ A) b (r′ : Events∞ B) → b ≡ false
           → force r′ ≡ M.ahead (force r) q t (M.before q (force r)) → M.ahead (skip k r) q t b ≃ skip k r′
ahead-skip k r q t .false r′ refl e = skip-same (sym e)

ahead-end : ∀ {A B} k q (t : Events∞ A) b → b ≡ false → M.ahead {B = B} (end k) q t b ≃ end k
ahead-end k q t .false refl = ≃-refl (end k)

ahead-lead : ∀ {A B} (x : Events B) q (t : Events∞ A) b → b ≡ true → M.ahead x q t b ≃ skip q (λ where .force → M.beside x (force t))
ahead-lead x q t .true refl = skip-same refl

beside-out : ∀ {A B} k (a : B) (r : Events∞ B) (e : Events A) (r′ : Events∞ B) → Lags k e
           → force r′ ≡ M.beside (force r) e → M.beside (out k a r) e ≃ out k a r′
beside-out k a r (out h x t) r′ lag f = ahead-out k a r (h ++ [ ix 0 ]) t _ r′ lag f
beside-out k a r (skip h t)  r′ lag f = ahead-out k a r (h ++ [ ix 0 ]) t _ r′ lag f
beside-out k a r (end c)     r′ lag f = out-same (sym f)
beside-out k a r hush        r′ lag f = out-same (sym f)

beside-skip : ∀ {A B} k (r : Events∞ B) (e : Events A) (r′ : Events∞ B) → Lags k e
            → force r′ ≡ M.beside (force r) e → M.beside (skip k r) e ≃ skip k r′
beside-skip k r (out h x t) r′ lag f = ahead-skip k r (h ++ [ ix 0 ]) t _ r′ lag f
beside-skip k r (skip h t)  r′ lag f = ahead-skip k r (h ++ [ ix 0 ]) t _ r′ lag f
beside-skip k r (end c)     r′ lag f = skip-same (sym f)
beside-skip k r hush        r′ lag f = skip-same (sym f)

beside-end : ∀ {A B} k (e : Events A) → Lags k e → M.beside {B = B} (end k) e ≃ end k
beside-end k (out h x t) lag = ahead-end k (h ++ [ ix 0 ]) t _ lag
beside-end k (skip h t)  lag = ahead-end k (h ++ [ ix 0 ]) t _ lag
beside-end k (end c)     lag = ≃-refl (end k)
beside-end k hush        lag = ≃-refl (end k)

-- What a step shows sits atop the stepped node's meaning, and that node
-- is placed.
Placedˢ : ∀ {Γ A} → NEnv Γ → U.Step Γ A → Set
Placedˢ ρ (U.outˢ k a c) = Atop k (U.meaning c ρ) × Placed c ρ
Placedˢ ρ (U.skipˢ k c)  = Atop k (U.meaning c ρ) × Placed c ρ
Placedˢ ρ (U.endˢ k)     = ⊤
Placedˢ ρ U.hushˢ        = ⊤

ordered-after : ∀ {Γ A} (ρ : NEnv Γ) (s : U.Step Γ A) → Placedˢ ρ s → Ordered (afterᴱ ρ s)
ordered (ordered-after ρ (U.outˢ k a c) (at , pl)) = at , proj₁ pl
ordered (ordered-after ρ (U.skipˢ k c)  (at , pl)) = at , proj₁ pl
ordered (ordered-after ρ (U.endˢ k)     _)         = tt
ordered (ordered-after ρ U.hushˢ        _)         = tt

-- A step that comes first just past `q` comes first at `q`.
not-past : ∀ x y z → y <ᵖ z ≡ true → not (x <ᵖ z) ≡ true → not (x <ᵖ y) ≡ true
not-past x y z yz w with x <ᵖ y in e
... | false = refl
... | true  = subst (λ b → not b ≡ true) (<ᵖ-trans x y z e yz) w

first-sub : ∀ {Γ} q (δ : Env Γ) → First (just (q ++ [ ix 0 ])) δ → First (just q) δ
first-sub q []              tt       = tt
first-sub q (U.ended _ ∷ δ) f        = first-sub q δ f
first-sub q (U.live s  ∷ δ) (w , f) = wins (U.headˢ (U.step s)) w , first-sub q δ f
  where wins : ∀ h → Wins (just (q ++ [ ix 0 ])) h ≡ true → Wins (just q) h ≡ true
        wins nothing  w = refl
        wins (just r) w = not-past (r ++ [ ix 0 ]) q (q ++ [ ix 0 ]) (<ᵖ-below q []) w

-- A source's step taken just past itself comes first.
wins-self : ∀ q → Wins (just (q ++ [ ix 0 ])) (just q) ≡ true
wins-self q = cong not (<ᵖ-irrefl (q ++ [ ix 0 ]))

postulate
  -- `M.beside` respects `≃` between events in order.
  beside-≃ : ∀ {A B} {x x′ : Events B} {y y′ : Events A} → Ordered x → Ordered x′ → Ordered y → Ordered y′
           → x ≃ x′ → y ≃ y′ → M.beside x y ≃ M.beside x′ y′

  -- A body reads alike sources alike, both in order and it placed under
  -- each.
  env-≃ : ∀ {Γ A B} (b : U.Node (A ∷ Γ) B) (ρ : NEnv Γ) {x y : Events A} → x ≃ y → Ordered x → Ordered y
        → Placed b (x ∷ᴬ ρ) → Placed b (y ∷ᴬ ρ) → U.meaning b (x ∷ᴬ ρ) ≃ U.meaning b (y ∷ᴬ ρ)

  -- A BODY FED ITS SOURCE'S STEP IS ALIKE THE BODY READING IT: a joiner
  -- fed the value its source shows at `q`, reading the source past it,
  -- the body's meaning showing nothing before the value.  A joiner the
  -- body makes later is never fed, so it must join after the value.
  --
  -- REFUTED: 69f610c0 stated without the body's meaning after the value, by a body joining its source later
  -- DEAD ROUTE: exact agreement per approximant (`same-agree`).  The
  --   meaning's joiner shows each of its source's skips, at `q ++ [ sub p ]`
  --   (`M.rejoin`), and a value from before its join as a skip; the
  --   stepper feeds a joiner values only, and only those after it joined.
  -- DEAD ROUTE: exact agreement per approximant with the stepper's joiner
  --   shown every source step as `M.rejoin` shows it.  A lane a flatMap
  --   has yet to subscribe reads its connect's source from where the
  --   ghost's source stands, so the meaning shows it one pre-join skip at
  --   `p ++ [ ix i ]` per source step before its join, and a source step
  --   leaves one fewer.  Witness 950a4208.
  -- DEAD ROUTE: exact agreement with a ghost anchored in its sources'
  --   step history.  The ghost is the witness's open part (`part`), which
  --   keeps no count of a source's steps, and a silent run is matched by
  --   the residual as a set alone (`Ahead`), so no field of the witness
  --   can keep the count a lane's pre-join skips need.
  -- RECOVERY: git show 950a4208 restores the joiner shown every source step, and step-alike over step-agrees
  fed-≃ : ∀ {Γ A B} (b : U.Node (A ∷ Γ) B) (ρ : NEnv Γ) q (a : A) (l : Events∞ A) {x : Events A} → x ≃ out q a l
        → Ordered x → Ordered (out q a l) → Atop (q ++ [ ix 0 ]) (U.meaning b (x ∷ᴬ ρ))
        → Placed b (x ∷ᴬ ρ) → Placed (U.feed (here refl) q a b) (force l ∷ᴬ ρ)
        → U.meaning b (x ∷ᴬ ρ) ≃ U.meaning (U.feed (here refl) q a b) (force l ∷ᴬ ρ)

  -- A skip atop what follows it is forgotten.
  skip-drop : ∀ {A k} {l : Events∞ A} → Ordered (skip k l) → skip k l ≃ force l

  -- EVENTS AT ONE POSITION COMMUTE: a source's step taken ahead of the
  -- body's events at its own position, the body's tie run shown first.
  ahead-even : ∀ {A B} (x : Events B) q (t : Events∞ A) → Ordered x → Atop (q ++ [ ix 0 ]) x
             → M.before (q ++ [ ix 0 ]) x ≡ false → Atop q (force t)
             → M.ahead x (q ++ [ ix 0 ]) t false ≃ skip (q ++ [ ix 0 ]) (λ where .force → M.beside x (force t))

  -- A NODE'S MEANING LAGS: whatever it shows is taken after a body's
  -- event at `k` that comes before its step and its sources'.
  lags : ∀ {Γ A} (c : U.Node Γ A) (δ : Env Γ) → Settled δ → Placed c (ρᴱ δ) → ∀ k
       → Wins (just k) (U.headˢ (U.step c)) ≡ true → First (just k) δ → Lags k (U.meaning c (ρᴱ δ))

  -- A NODE'S MEANING LEADS NOTHING: whatever it shows comes no earlier
  -- than `j`, which comes before its step and its sources'.  At `j` it
  -- may: a joiner placed at its source's next step shows a pre-join skip
  -- just past it, and nothing in the placing says positions never meet.
  --
  -- REFUTED: 07140662 strictly after `j`, by a joiner placed at its source's next step
  leads : ∀ {Γ A} (c : U.Node Γ A) (δ : Env Γ) → Settled δ → Placed c (ρᴱ δ) → ∀ j
        → U.beforeˢ j (U.step c) ≡ true → First (just j) δ → Atop j (U.meaning c (ρᴱ δ))

  -- A STEP KEEPS THE GHOST PLACED: a step coming first leaves the stepped
  -- node placed, atop what the step shows.
  --
  -- REFUTED: d2d13661 without the step coming first, by a merge whose joiner lane shows its source's earlier event
  -- REFUTED: c8c55884 over a placing with each live joiner joined before its source, by a lane admitted past its source's next event
  placed-after : ∀ {Γ A} (c : U.Node Γ A) (δ : Env Γ) → Settled δ → Sane (flags δ) c → Placed c (ρᴱ δ)
               → First (U.headˢ (U.step c)) δ → Placedˢ (ρᴱ δ) (U.step c)

-- The source's next taken first, ahead of the body's events at the same
-- position.
tie-lead : ∀ {A B} (x : Events B) q (t : Events∞ A) → Ordered x → Atop (q ++ [ ix 0 ]) x → Atop q (force t)
         → M.ahead x (q ++ [ ix 0 ]) t (M.before (q ++ [ ix 0 ]) x) ≃ skip (q ++ [ ix 0 ]) (λ where .force → M.beside x (force t))
tie-lead x q t o a at with M.before (q ++ [ ix 0 ]) x in e
... | true  = ≃-trans (ahead-lead x (q ++ [ ix 0 ]) t true refl) (skip-same refl)
... | false = ≃-trans (ahead-even x q t o a e at) (skip-same refl)

-- The source's next taken after the body's step.
LagsHead : ∀ {Γ A B} → U.Step Γ B → Events A → Set
LagsHead (U.outˢ k _ _) e = Lags k e
LagsHead (U.skipˢ k _)  e = Lags k e
LagsHead (U.endˢ k)     e = Lags k e
LagsHead U.hushˢ        e = ⊥

beside-head : ∀ {Γ A B} (s : U.Node Γ A) (ρ : NEnv Γ) (sb : U.Step (A ∷ Γ) B) → LagsHead sb (U.meaning s ρ)
            → M.beside (afterᴱ (U.meaning s ρ ∷ᴬ ρ) sb) (U.meaning s ρ) ≃ afterᴱ ρ (U.bodyˢ (U.live s) sb)
beside-head s ρ (U.outˢ k a b) lag = beside-out k a _ (U.meaning s ρ) _ lag refl
beside-head s ρ (U.skipˢ k b)  lag = beside-skip k _ (U.meaning s ρ) _ lag refl
beside-head s ρ (U.endˢ k)     lag = beside-end k (U.meaning s ρ) lag

ordered-hush : ∀ {A} → Ordered {A} hush
ordered ordered-hush = tt

ordered-end : ∀ {A} k → Ordered {A} (end k)
ordered (ordered-end k) = tt

-- The connect, its body's step and its source's named.
conn : ∀ {Γ A B} (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (δ : Env Γ) (st : Settled δ)
     → Sane (flags δ) (U.connectᶜ b (U.live s)) → Placed (U.connectᶜ b (U.live s)) (ρᴱ δ)
     → (sb : U.Step (A ∷ Γ) B) (ss : U.Step Γ A)
     → (Wins (U.headˢ sb) (U.headˢ ss) ≡ true → First (U.headˢ sb) δ → U.meaning b (U.meaning s (ρᴱ δ) ∷ᴬ ρᴱ δ) ≃ afterᴱ (U.meaning s (ρᴱ δ) ∷ᴬ ρᴱ δ) sb)
     → (First (U.headˢ ss) δ → U.meaning s (ρᴱ δ) ≃ afterᴱ (ρᴱ δ) ss)
     → (∀ k → Wins (just k) (U.headˢ ss) ≡ true → First (just k) δ → Lags k (U.meaning s (ρᴱ δ)))
     → (∀ j → U.beforeˢ j sb ≡ true → Wins (just j) (U.headˢ ss) ≡ true → First (just j) δ → Atop j (U.meaning b (U.meaning s (ρᴱ δ) ∷ᴬ ρᴱ δ)))
     → (Wins (U.headˢ sb) (U.headˢ ss) ≡ true → First (U.headˢ sb) δ → Placedˢ (U.meaning s (ρᴱ δ) ∷ᴬ ρᴱ δ) sb)
     → (First (U.headˢ ss) δ → Placedˢ (ρᴱ δ) ss)
     → (First (U.headˢ (U.sourceˢ b sb s ss)) δ → Placedˢ (ρᴱ δ) (U.sourceˢ b sb s ss))
     → First (U.headˢ (U.sourceˢ b sb s ss)) δ
     → U.meaning (U.connectᶜ b (U.live s)) (ρᴱ δ) ≃ afterᴱ (ρᴱ δ) (U.sourceˢ b sb s ss)
conn b s δ st sn (_ , pb , ps) sb ss hb hs lg ld pab pas pa fi = go sb ss hb hs lg ld pab pas pa fi
  where
  ρ  = ρᴱ δ
  ms = U.meaning s ρ
  MB = U.meaning b (ms ∷ᴬ ρ)

  -- The body's step taken first.
  body : ∀ sb → Placedˢ (ms ∷ᴬ ρ) sb → MB ≃ afterᴱ (ms ∷ᴬ ρ) sb → LagsHead sb ms → M.beside MB ms ≃ afterᴱ ρ (U.bodyˢ (U.live s) sb)
  body sb pab e lag = ≃-trans (beside-≃ (proj₁ pb) (ordered-after (ms ∷ᴬ ρ) sb pab) (proj₁ ps) (proj₁ ps) e (≃-refl ms)) (beside-head s ρ sb lag)

  go : ∀ sb ss
     → (Wins (U.headˢ sb) (U.headˢ ss) ≡ true → First (U.headˢ sb) δ → MB ≃ afterᴱ (ms ∷ᴬ ρ) sb)
     → (First (U.headˢ ss) δ → ms ≃ afterᴱ ρ ss)
     → (∀ k → Wins (just k) (U.headˢ ss) ≡ true → First (just k) δ → Lags k ms)
     → (∀ j → U.beforeˢ j sb ≡ true → Wins (just j) (U.headˢ ss) ≡ true → First (just j) δ → Atop j MB)
     → (Wins (U.headˢ sb) (U.headˢ ss) ≡ true → First (U.headˢ sb) δ → Placedˢ (ms ∷ᴬ ρ) sb)
     → (First (U.headˢ ss) δ → Placedˢ ρ ss)
     → (First (U.headˢ (U.sourceˢ b sb s ss)) δ → Placedˢ ρ (U.sourceˢ b sb s ss))
     → First (U.headˢ (U.sourceˢ b sb s ss)) δ → M.beside MB ms ≃ afterᴱ ρ (U.sourceˢ b sb s ss)
  go U.hushˢ          U.hushˢ hb hs lg ld pab pas pa fi =
    beside-≃ (proj₁ pb) ordered-hush (proj₁ ps) ordered-hush (hb refl fi) (hs fi)
  go sb@(U.outˢ k _ _) U.hushˢ hb hs lg ld pab pas pa fi = body sb (pab refl fi) (hb refl fi) (lg k refl fi)
  go sb@(U.skipˢ k _)  U.hushˢ hb hs lg ld pab pas pa fi = body sb (pab refl fi) (hb refl fi) (lg k refl fi)
  go sb@(U.endˢ k)     U.hushˢ hb hs lg ld pab pas pa fi = body sb (pab refl fi) (hb refl fi) (lg k refl fi)
  go sb (U.outˢ q x s′) hb hs lg ld pab pas pa fi with U.beforeˢ (q ++ [ ix 0 ]) sb in eq
  go U.hushˢ           (U.outˢ q x s′) hb hs lg ld pab pas pa fi | false with () ← eq
  go sb@(U.outˢ k _ _) (U.outˢ q x s′) hb hs lg ld pab pas pa fi | false = body sb (pab (cong not eq) fi) (hb (cong not eq) fi) (lg k (cong not eq) fi)
  go sb@(U.skipˢ k _)  (U.outˢ q x s′) hb hs lg ld pab pas pa fi | false = body sb (pab (cong not eq) fi) (hb (cong not eq) fi) (lg k (cong not eq) fi)
  go sb@(U.endˢ k)     (U.outˢ q x s′) hb hs lg ld pab pas pa fi | false = body sb (pab (cong not eq) fi) (hb (cong not eq) fi) (lg k (cong not eq) fi)
  go sb (U.outˢ q x s′) hb hs lg ld pab pas pa fi | true =
    ≃-trans (beside-≃ (proj₁ pb) (proj₁ pb) (proj₁ ps) ordOut (≃-refl MB) e₁)
   (≃-trans (tie-lead MB q _ (proj₁ pb) (ld (q ++ [ ix 0 ]) eq (wins-self q) fi) atq)
            (skip-cong (beside-≃ (proj₁ pb) (proj₁ pbf) (proj₁ ps′) (proj₁ ps′) (fed-≃ b ρ q x _ e₁ (proj₁ ps) ordOut (ld (q ++ [ ix 0 ]) eq (wins-self q) fi) pb pbf) (≃-refl _))))
    where e₁ = hs (first-sub q δ fi)
          ordOut = ordered-after ρ (U.outˢ q x s′) (pas (first-sub q δ fi))
          atq = proj₁ (pas (first-sub q δ fi))
          ps′ = proj₂ (pas (first-sub q δ fi))
          pbf = proj₁ (proj₂ (proj₂ (pa fi)))
  go sb (U.skipˢ q s′) hb hs lg ld pab pas pa fi with U.beforeˢ (q ++ [ ix 0 ]) sb in eq
  go U.hushˢ           (U.skipˢ q s′) hb hs lg ld pab pas pa fi | false with () ← eq
  go sb@(U.outˢ k _ _) (U.skipˢ q s′) hb hs lg ld pab pas pa fi | false = body sb (pab (cong not eq) fi) (hb (cong not eq) fi) (lg k (cong not eq) fi)
  go sb@(U.skipˢ k _)  (U.skipˢ q s′) hb hs lg ld pab pas pa fi | false = body sb (pab (cong not eq) fi) (hb (cong not eq) fi) (lg k (cong not eq) fi)
  go sb@(U.endˢ k)     (U.skipˢ q s′) hb hs lg ld pab pas pa fi | false = body sb (pab (cong not eq) fi) (hb (cong not eq) fi) (lg k (cong not eq) fi)
  go sb (U.skipˢ q s′) hb hs lg ld pab pas pa fi | true =
    ≃-trans (beside-≃ (proj₁ pb) (proj₁ pb) (proj₁ ps) ordSk (≃-refl MB) e₁)
   (≃-trans (tie-lead MB q _ (proj₁ pb) (ld (q ++ [ ix 0 ]) eq (wins-self q) fi) atq)
            (skip-cong (beside-≃ (proj₁ pb) (proj₁ pb′) (proj₁ ps′) (proj₁ ps′)
                         (env-≃ b ρ (≃-trans e₁ (skip-drop ordSk)) (proj₁ ps) (proj₁ ps′) pb pb′) (≃-refl _))))
    where e₁ = hs (first-sub q δ fi)
          ordSk = ordered-after ρ (U.skipˢ q s′) (pas (first-sub q δ fi))
          atq = proj₁ (pas (first-sub q δ fi))
          pb′ = proj₁ (proj₂ (proj₂ (pa fi)))
          ps′ = proj₂ (proj₂ (proj₂ (pa fi)))
  go sb (U.endˢ c) hb hs lg ld pab pas pa fi with U.beforeˢ (c ++ [ ix 0 ]) sb in eq
  go U.hushˢ           (U.endˢ c) hb hs lg ld pab pas pa fi | false with () ← eq
  go sb@(U.outˢ k _ _) (U.endˢ c) hb hs lg ld pab pas pa fi | false = body sb (pab (cong not eq) fi) (hb (cong not eq) fi) (lg k (cong not eq) fi)
  go sb@(U.skipˢ k _)  (U.endˢ c) hb hs lg ld pab pas pa fi | false = body sb (pab (cong not eq) fi) (hb (cong not eq) fi) (lg k (cong not eq) fi)
  go sb@(U.endˢ k)     (U.endˢ c) hb hs lg ld pab pas pa fi | false = body sb (pab (cong not eq) fi) (hb (cong not eq) fi) (lg k (cong not eq) fi)
  go sb (U.endˢ c) hb hs lg ld pab pas pa fi | true =
    ≃-trans (beside-≃ (proj₁ pb) (proj₁ pb) (proj₁ ps) (ordered-end c) (≃-refl MB) e₁)
   (≃-trans (env-≃ b ρ e₁ (proj₁ ps) (ordered-end c) pb (shut-placed (here refl) c b (end c ∷ᴬ ρ) refl pbs))
            (subst (λ X → X ≃ afterᴱ ρ (U.skipˢ (c ++ [ ix 0 ]) (U.connectᶜ (U.shut (here refl) c b) (U.ended c))))
                   (shut-meaning (here refl) c b (end c ∷ᴬ ρ) refl)
                   (≃-trans (≃-sym (skip-drop ordSk)) (skip-same refl))))
    where e₁ = hs (first-sub c δ fi)
          ordSk : Ordered (skip (c ++ [ ix 0 ]) (λ where .force → U.meaning (U.shut (here refl) c b) (end c ∷ᴬ ρ)))
          ordered ordSk = proj₁ (pa fi) , proj₁ (proj₂ (pa fi))
          pbs = proj₂ (proj₂ (pa fi))

-- A RUNNING CONNECT STEPS AS IT MEANS: its body, reading its source, and
-- its source, each showing its step whenever it comes first, the
-- connect's meaning is what its step shows: its body's step or its
-- source's, a value fed to the body's joiners.
live-skips : ∀ {Γ A B} (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (δ : Env Γ) → Settled δ
           → Sane (flags δ) (U.connectᶜ b (U.live s)) → Placed (U.connectᶜ b (U.live s)) (ρᴱ δ)
           → Shows b (U.live s ∷ δ) → Shows s δ → Shows (U.connectᶜ b (U.live s)) δ
live-skips b s δ st sn@(snb , sns) pl@(_ , pb , ps) hb hs =
  conn b s δ st sn pl (U.step b) (U.step s) (λ w f → hb (w , f)) hs
       (λ k w f → lags s δ st ps k w f)
       (λ j bj w f → leads b (U.live s ∷ δ) (hs , ps , st) pb j bj (w , f))
       (λ w f → placed-after b (U.live s ∷ δ) (hs , ps , st) snb pb (w , f)) (placed-after s δ st sns ps)
       (placed-after (U.connectᶜ b (U.live s)) δ st sn pl)

------------------------------------------------------------------------
-- Every node

mutual
  os : ∀ {Γ A} (c : U.Node Γ A) (δ : Env Γ) → Settled δ → Sane (flags δ) c → Placed c (ρᴱ δ) → Shows c δ
  os (U.framesᶜ τ e m)    δ st sn pl fi = frames-after τ e m
  os (U.burstᶜ τ r i b)   δ st sn pl fi = burst-after τ r i b
  os (U.endᶜ p)           δ st sn pl fi = ≃-refl (end p)
  os (U.ofᶜ p i xs)       δ st sn pl fi = of-after p i xs
  os (U.mapᶜ f c)         δ st sn (_ , pl) fi =
    ≃-trans (mapᴱ-≃ f (os c δ st sn pl (subst (λ k → First k δ) (map-head f (U.step c)) fi))) (map-after f (U.step c))
  os (U.scanᶜ f z c)      δ st sn (_ , pl) fi =
    ≃-trans (scanᴱ-≃ f z (os c δ st sn pl (subst (λ k → First k δ) (scan-head f z (U.step c)) fi))) (scan-after f z (U.step c))
  os (U.takeWhileᶜ i p c) δ st sn (_ , pl) fi =
    ≃-trans (takeWhileᴱ-≃ i p (os c δ st sn pl (take-first i p (U.step c) δ fi))) (take-after i p (U.step c))
  os (U.flatMapᶜ op g o ls qs) δ st sn pl@(_ , po , pls) =
    go-skips op g o ls qs δ st sn pl (osᴹ o δ st (proj₁ sn) po) (osᴸ ls δ st (proj₁ (proj₂ sn)) pls)
  os (U.joinᶜ i p xs e)   δ st sn pl fi = join-after i p xs e δ st sn fi
  os (U.connectᶜ b (U.live s)) δ st sn@(sb , ss) pl@(_ , pb , ps) =
    live-skips b s δ st sn pl (os b (U.live s ∷ δ) (os s δ st ss ps , ps , st) sb pb) (os s δ st ss ps)
  os (U.connectᶜ b (U.ended c)) δ st sn (_ , pb) fi =
    ≃-trans (os b (U.ended c ∷ δ) st sn pb (subst (λ k → First k δ) (shut-head c (U.step b)) fi)) (shut-after c (U.step b))
  os (U.deferᶜ l p)       δ st sn pl fi = defer-after l p (ρᴱ δ)

  osᴹ : ∀ {Γ A} (o : Maybe (U.Node Γ A)) (δ : Env Γ) → Settled δ → Saneᴹ (flags δ) o → Placedᴹ o (ρᴱ δ) → Showsᴹ o δ
  osᴹ nothing  δ st sn pl = tt
  osᴹ (just c) δ st sn pl = os c δ st sn pl

  osᴸ : ∀ {Γ A} (ls : List (U.Node Γ A)) (δ : Env Γ) → Settled δ → Saneᴸ (flags δ) ls → Placedᴸ ls (ρᴱ δ) → Showsᴸ ls δ
  osᴸ []       δ st sn        pl        = tt
  osᴸ (c ∷ cs) δ st (sc , sl) (pc , pl) = os c δ st sc pc , osᴸ cs δ st sl pl
