{-# OPTIONS --guardedness #-}

-- WHERE THE ELABORATED COLD'S ROWS FALL.  A cold subscribed at `s` lists
-- every row past `s` (`walk-past`); in `s`'s own instant one label down
-- (`walk-under`), so one of the subscribe burst; one end at most
-- (`walk-end`), after every other row (`walk-before`); and past the
-- burst each row in an instant of its own (`walk-apart`).  The elaboration's cold is subscribed at `c₀`, in the
-- burst at `P`: a row of the burst lies below the concat's first lane,
-- before its second (`early`); any later row lies past the whole burst
-- (`late`).
module simultaneous.ColdOrder where

open import Data.Bool using (true; false)
open import Data.Unit using (tt)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
open import Data.List.Properties using (∷ʳ-injectiveˡ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _<ᵇ_; _+_; s≤s; z≤n)
open import Data.Nat.Properties using (<⇒<ᵇ; m<m+n; ≤-trans)
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

open import denotation.Position using (Pos; Label; _∙_; _≟ⁱ_; _<ˡ_; ix; last; _⊕_; instant; tick; frame; cascade; nested; fired)
open import denotation.Events using (<ᵖ-part; Events; From; Frame; start; frames; burst; done; quiet; at; emit; stall; close; Frame∞; From∞)
import denotation.Events as Ev
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Work; _≺_; InE; at-out; at-skip; at-end; on-out; on-skip)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≺-ext)
open import denotation.Laws.Worlds using (⊕-assoc; ∙-inj)
open import quickcheck.Tabled using (Row)
open import simultaneous.Instants using (_≺ⁱ_; ≺-instant; instant-≺)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Listing using (walkN; walkN-exact)
open import quickcheck.Tabled.Exact.Base using (sound)
open import simultaneous.TakeCut using (inst-⊕)
open import simultaneous.ColdRows using (module At)

------------------------------------------------------------------------
-- A cold's walk

-- A row of a later tick lies past the subscription.
past-tick : ∀ s {u e l ys} → tick s < u → s ≺ (cascade u e l ∙ ys)
past-tick (frame ∙ _)         _  = tt
past-tick (cascade t d a ∙ q) {u} lt with t <ᵇ u | <⇒<ᵇ lt
... | true  | _  = tt
... | false | ()

-- EVERY ROW OF A COLD LIES PAST ITS SUBSCRIPTION: the subscribe burst
-- under it, every later frame at a later tick.
mutual
  frames-past : ∀ {A t} s {e} (m : From A t) → 1 ≤ t → s ≺ e → ∀ {y v} → InE (frames (tick s) e m) y v → s ≺ y
  frames-past s done          _   se at-end = se
  frames-past s quiet         _   _  ()
  frames-past s (at t′ le b) one _  x      = fired-past s 0 b (m<m+n (tick s) (≤-trans one le)) x

  fired-past : ∀ {A t} s {e} i (b : Frame A t) → tick s < tick s + t → ∀ {y v} → InE (burst (tick s) (fired (tick s + t) e) i b) y v → s ≺ y
  fired-past s i (emit a k) lt at-out      = past-tick s lt
  fired-past s i (emit a k) lt (on-out x)  = fired-past s (suc i) k lt x
  fired-past s i (stall k)  lt at-skip     = past-tick s lt
  fired-past s i (stall k)  lt (on-skip x) = fired-past s (suc i) (Frame∞.force k) lt x
  fired-past s i (close k)  lt at-skip     = past-tick s lt
  fired-past s i (close k)  lt (on-skip x) = frames-past s (From∞.force k) (s≤s z≤n) (past-tick s lt) x

nested-past : ∀ {A} s i (b : Frame A 0) → ∀ {y v} → InE (burst (tick s) (nested s) i b) y v → s ≺ y
nested-past s i (emit a k) at-out      = ≺-ext s []
nested-past s i (emit a k) (on-out x)  = nested-past s (suc i) k x
nested-past s i (stall k)  at-skip     = ≺-ext s []
nested-past s i (stall k)  (on-skip x) = nested-past s (suc i) (Frame∞.force k) x
nested-past s i (close k)  at-skip     = ≺-ext s []
nested-past s i (close k)  (on-skip x) = frames-past s (From∞.force k) (s≤s z≤n) (≺-ext s []) x

start-past : ∀ {A} s (m : From A 0) {y v} → InE (start s m) y v → s ≺ y
start-past s done              at-end = ≺-ext s []
start-past s quiet             ()
start-past s (at zero _ b)     x      = nested-past s 0 b x
start-past s (at (suc t) le b) x      = fired-past s 0 b (m<m+n (tick s) (s≤s z≤n)) x

walk-past : ∀ {A} K s (m : From A 0) {k e} → (k , e) ∈ walkN K (start s m) → s ≺ k
walk-past K s m x = start-past s m (proj₁ (sound (walkN-exact K (start s m)) x))

postulate
  -- THE COLD'S WALK.
  walk-under : ∀ {A} K s (m : From A 0) {k e} → (k , e) ∈ walkN K (start s m)
             → instantOf k ≡ instantOf s → Σ Label λ l → k ≡ s ⊕ [ l ]
  walk-end   : ∀ {A} K s (m : From A 0) {c c′} → (c , end) ∈ walkN K (start s m) → (c′ , end) ∈ walkN K (start s m) → c ≡ c′
  walk-before : ∀ {A} K s (m : From A 0) {c k e} → (c , end) ∈ walkN K (start s m) → (k , e) ∈ walkN K (start s m)
              → Work e → k ≺ c
  walk-apart : ∀ {A} K s (m : From A 0) {k e k′ e′} → (k , e) ∈ walkN K (start s m) → (k′ , e′) ∈ walkN K (start s m)
             → instantOf k ≡ instantOf k′ → (instantOf k ≡ instantOf s → ⊥) → k ≡ k′

-- A walk shows no pin.
walk-nopin : ∀ {A} K (ev : Events A) {k r} → (k , pin r) ∈ walkN K ev → ⊥
walk-nopin zero    _                 ()
walk-nopin (suc K) (Ev.out _ _ r)    (here ())
walk-nopin (suc K) (Ev.out _ _ r)    (there x) = walk-nopin K (Ev.Events∞.force r) x
walk-nopin (suc K) (Ev.skip _ r)     (here ())
walk-nopin (suc K) (Ev.skip _ r)     (there x) = walk-nopin K (Ev.Events∞.force r) x
walk-nopin (suc K) (Ev.end _)        (here ())
walk-nopin (suc K) (Ev.end _)        (there ())
walk-nopin (suc K) Ev.hush           ()

------------------------------------------------------------------------
-- Positions written label by label

nest2 : ∀ x a b → x ⊕ [ a ] ⊕ [ b ] ≡ x ⊕ (a ∷ b ∷ [])
nest2 x a b = ⊕-assoc x [ a ] [ b ]

nest3 : ∀ x a b c → x ⊕ [ a ] ⊕ [ b ] ⊕ [ c ] ≡ x ⊕ (a ∷ b ∷ c ∷ [])
nest3 x a b c = trans (cong (_⊕ [ c ]) (nest2 x a b)) (⊕-assoc x (a ∷ b ∷ []) [ c ])

nest4 : ∀ x a b c d → x ⊕ [ a ] ⊕ [ b ] ⊕ [ c ] ⊕ [ d ] ≡ x ⊕ (a ∷ b ∷ c ∷ d ∷ [])
nest4 x a b c d = trans (cong (_⊕ [ d ]) (nest3 x a b c)) (⊕-assoc x (a ∷ b ∷ c ∷ []) [ d ])

nest5 : ∀ x a b c d e → x ⊕ [ a ] ⊕ [ b ] ⊕ [ c ] ⊕ [ d ] ⊕ [ e ] ≡ x ⊕ (a ∷ b ∷ c ∷ d ∷ e ∷ [])
nest5 x a b c d e = trans (cong (_⊕ [ e ]) (nest4 x a b c d)) (⊕-assoc x (a ∷ b ∷ c ∷ d ∷ []) [ e ])

-- Two subtrees apart, in their labels' order.
part : ∀ x {a b} ys zs → a <ˡ b ≡ true → (x ⊕ (a ∷ ys)) ≺ (x ⊕ (b ∷ zs))
part x ys zs h = Equivalence.from T-≡ (<ᵖ-part x ys zs h)

≺-flat : ∀ {x y x′ y′} → x ≡ x′ → y ≡ y′ → x′ ≺ y′ → x ≺ y
≺-flat refl refl lt = lt

down : ∀ x l → x ≺ (x ⊕ [ l ])
down x l = ≺-ext x []

-- Two and three labels down.
dn2 : ∀ c a b → c ≺ (c ⊕ [ a ] ⊕ [ b ])
dn2 c a b = ≺-trans {c} {c ⊕ [ a ]} {c ⊕ [ a ] ⊕ [ b ]} (down c a) (down (c ⊕ [ a ]) b)

dn3 : ∀ c a b d → c ≺ (c ⊕ [ a ] ⊕ [ b ] ⊕ [ d ])
dn3 c a b d = ≺-trans {c} {c ⊕ [ a ] ⊕ [ b ]} {c ⊕ [ a ] ⊕ [ b ] ⊕ [ d ]} (dn2 c a b) (down (c ⊕ [ a ] ⊕ [ b ]) d)

≺-≢ : ∀ {x y} → x ≺ y → x ≡ y → ⊥
≺-≢ {x} lt refl = ≺-irrefl {x} lt

-- One label down from two places is two places.
⊕1-inj : ∀ {x y l} → (x ⊕ [ l ]) ≡ (y ⊕ [ l ]) → x ≡ y
⊕1-inj {i ∙ p} {j ∙ r} e with ∙-inj e
... | refl , e₂ = cong (i ∙_) (∷ʳ-injectiveˡ p r e₂)

------------------------------------------------------------------------
-- The elaborated cold's

module Ord {A : Set} (P : Pos) (K : ℕ) (m : From A 0) where
  open At {A} P using (C₀; c₀; sync; sync-in)

  J : List (Row A)
  J = walkN K (start c₀ m)

  -- The tick the scan reads the burst's end off.
  T₀ : Pos
  T₀ = P ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ ix 0 ]

  ------------------------------------------------------------------------
  -- The burst's instant

  inP : ∀ x l → instantOf x ≡ instantOf P → instantOf (x ⊕ [ l ]) ≡ instantOf P
  inP x l e = trans (inst-⊕ x [ l ]) e

  C₀-in : instantOf C₀ ≡ instantOf P
  C₀-in = inP (P ⊕ [ ix 0 ]) (ix 1) (inP P (ix 0) refl)

  c₀-in : instantOf c₀ ≡ instantOf P
  c₀-in = inP (C₀ ⊕ [ ix 0 ]) (ix 1) (inP C₀ (ix 0) C₀-in)

  sync-or : ∀ y → sync y ≡ true ⊎ sync y ≡ false
  sync-or y with instantOf y ≟ⁱ instantOf P
  ... | yes _ = inj₁ refl
  ... | no _  = inj₂ refl

  sync-at : ∀ {y} → instantOf y ≡ instantOf P → sync y ≡ true
  sync-at {y} i with instantOf y ≟ⁱ instantOf P
  ... | yes _ = refl
  ... | no n  = ⊥-elim (n i)

  sync-out : ∀ {y} → sync y ≡ false → instantOf y ≡ instantOf P → ⊥
  sync-out {y} e i with trans (sym (sync-at {y} i)) e
  ... | ()

  ------------------------------------------------------------------------
  -- The cold's rows

  past : ∀ {y e} → (y , e) ∈ J → c₀ ≺ y
  past = walk-past K c₀ m

  -- A row of the burst: below the concat's first lane.
  early : ∀ {y e} → (y , e) ∈ J → sync y ≡ true → y ≺ (C₀ ⊕ [ ix 1 ])
  early {y} x s with walk-under K c₀ m x (trans (sync-in {y} s) (sym c₀-in))
  ... | l , refl = ≺-flat (nest3 C₀ (ix 0) (ix 1) l) refl (part C₀ (ix 1 ∷ l ∷ []) [] refl)

  -- A later row: past everything in the burst.
  late : ∀ {y e} → (y , e) ∈ J → sync y ≡ false → ∀ z → instantOf z ≡ instantOf P → z ≺ y
  late {y} x s z iz = instant-≺ z y (subst (_≺ⁱ instant y) (trans c₀-in (sym iz))
    (≺-instant c₀ y (past x) (λ eq → sync-out {y} s (trans (sym eq) c₀-in))))

  ------------------------------------------------------------------------
  -- The plumbing's positions

  T₀-in : instantOf T₀ ≡ instantOf P
  T₀-in = inP (P ⊕ [ ix 1 ] ⊕ [ ix 1 ]) (ix 0) (inP (P ⊕ [ ix 1 ]) (ix 1) (inP P (ix 1) refl))

  C₀≺c₀ : C₀ ≺ c₀
  C₀≺c₀ = ≺-trans {C₀} {C₀ ⊕ [ ix 0 ]} {c₀} (down C₀ (ix 0)) (down (C₀ ⊕ [ ix 0 ]) (ix 1))

  lt01 : (C₀ ⊕ [ ix 0 ]) ≺ (C₀ ⊕ [ ix 1 ])
  lt01 = part C₀ [] [] refl

  lt0L : (C₀ ⊕ [ ix 0 ]) ≺ (C₀ ⊕ [ last ])
  lt0L = part C₀ [] [] refl

  lt1L : (C₀ ⊕ [ ix 1 ]) ≺ (C₀ ⊕ [ last ])
  lt1L = part C₀ [] [] refl

  lt11L : (C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ last ]) ≺ (C₀ ⊕ [ last ])
  lt11L = ≺-flat (nest3 C₀ (ix 1) (ix 1) last) refl (part C₀ (ix 1 ∷ last ∷ []) [] refl)

  C0c₀ : (C₀ ⊕ [ ix 0 ]) ≺ c₀
  C0c₀ = down (C₀ ⊕ [ ix 0 ]) (ix 1)

  CL-PL : (C₀ ⊕ [ last ]) ≺ (P ⊕ [ last ])
  CL-PL = ≺-flat (nest3 P (ix 0) (ix 1) last) refl (part P (ix 1 ∷ last ∷ []) [] refl)

  TL-PL : (P ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ last ]) ≺ (P ⊕ [ last ])
  TL-PL = ≺-flat (nest3 P (ix 1) (ix 1) last) refl (part P (ix 1 ∷ last ∷ []) [] refl)

  C1-T : (C₀ ⊕ [ ix 1 ]) ≺ T₀
  C1-T = ≺-flat (nest3 P (ix 0) (ix 1) (ix 1)) (nest3 P (ix 1) (ix 1) (ix 0)) (part P (ix 1 ∷ ix 1 ∷ []) (ix 1 ∷ ix 0 ∷ []) refl)

  C110-T : (C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ ix 0 ]) ≺ T₀
  C110-T = ≺-flat (nest5 P (ix 0) (ix 1) (ix 1) (ix 1) (ix 0)) (nest3 P (ix 1) (ix 1) (ix 0))
    (part P (ix 1 ∷ ix 1 ∷ ix 1 ∷ ix 0 ∷ []) (ix 1 ∷ ix 0 ∷ []) refl)

