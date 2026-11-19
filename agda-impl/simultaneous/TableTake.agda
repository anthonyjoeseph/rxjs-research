{-# OPTIONS --guardedness #-}

-- `takeWhile`'S CASE (`take-tab`): a plain takeWhile and the elaborated
-- one carry their child's record.  The map is the child's, but for the
-- two rows under the first failing value, which go under its image
-- (`moved`); each cut's correspondence is `TakeCut`'s.
--
-- Past the elaborated first failure only pins survive, kept where their
-- connect lies before it.
module simultaneous.TableTake where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; map)
open import Data.List.Membership.Propositional using (_∈_; find; lose)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (any?)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (T?)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import denotation.Position using (Pos; Label; root; _≟ᵖ_; _<ᵖ_; ix; last; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; _≺_; _≼_; module TakeWhile)
open import denotation.Laws.Modulus using (AgreeTo; upto; AgreeTo-sym; ag-down; ≺-trans; ≼-refl; ≼-trans; ≺→≼; ≼-or-≻; ≼-≺-≺; ≺-ext)
open import denotation.Laws.Worlds using (⊕-injˡ; ⊕-injʳ)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (rows; bind; takeRows)
open import quickcheck.Tabled.Exact.Base using (Exact)
open import quickcheck.Tabled.Exact using (module TakeX)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf; parent; parent-snoc)
open import simultaneous.TableCorr using (Corr; Rel; module Rel; Same; same; φ≡; nl→; corr-≃; keys; in-keys; tr-few)
open import simultaneous.TableKit using (TR; cons-≤; ag-≃; got-bind)
open import simultaneous.TakeKit using (Run; Lab; lab; ≼-last; module Take)
open import simultaneous.TakeCut using (inst-⊕; module TakeCut)
open import simultaneous.Horizon using (module TakeB; bounded-≃)
open import simultaneous.HorizonCorr using (module Inter; Own; OwnPut)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; passes)

------------------------------------------------------------------------
-- A table's takeWhile

Took : ∀ {X : Set} → Bool → (X → Bool) → Maybe (Tb.Listed X) → Maybe (Tb.Listed X)
Took i keep m = bind m λ l → just (takeRows i keep l)

ex-just : ∀ {X : Set} (L : Tb.Listed X) → Exact L (TR (just L))
ex-just L = record { sound = λ r → L , refl , r ; complete = λ { (_ , refl , r) → r } }

lab-Lab : ∀ b → Lab (lab b)
lab-Lab true  = inj₁ refl
lab-Lab false = inj₂ refl

-- The rows a failing value's two rows go under.
under-bk : (Pos → List Pos) → Pos → List Pos
under-bk bk l = bk l ++ map (_⊕ [ ix 0 ]) (bk (parent l)) ++ map (_⊕ [ last ]) (bk (parent l))

in-under : ∀ (bk : Pos → List Pos) {o z l} → Lab l → o ∈ bk z → (o ⊕ [ l ]) ∈ under-bk bk (z ⊕ [ l ])
in-under bk {o} {z} (inj₁ refl) h =
  ∈-++⁺ʳ (bk (z ⊕ [ ix 0 ])) (∈-++⁺ˡ (∈-map⁺ (_⊕ [ ix 0 ]) (subst (λ w → o ∈ bk w) (sym (parent-snoc z (ix 0))) h)))
in-under bk {o} {z} (inj₂ refl) h =
  ∈-++⁺ʳ (bk (z ⊕ [ last ])) (∈-++⁺ʳ (map (_⊕ [ ix 0 ]) (bk (parent (z ⊕ [ last ]))))
    (∈-map⁺ (_⊕ [ last ]) (subst (λ w → o ∈ bk w) (sym (parent-snoc z last)) h)))

module _ {X : Set} (i : Bool) (keep : X → Bool) where
  open TakeWhile i keep using (TakeT; pass; fail; stop; step; tend; left)

  private
    none : ∀ {k e} → TakeT (TR {X} nothing) k e → ⊥
    none (pass (_ , () , _) _ _)
    none (fail (_ , () , _) _ _ _)
    none (stop (_ , () , _) _ _)
    none (step (_ , () , _) _)
    none (tend (_ , () , _) _)
    none (left (_ , () , _) _ _)

  tr-take→ : ∀ (m : Maybe (Tb.Listed X)) {k e} → TR (Took i keep m) k e → TakeT (TR m) k e
  tr-take→ nothing (_ , () , _)
  tr-take→ (just L) (_ , refl , r) = TakeX.sound-t i keep (TR (just L)) L (ex-just L) r

  tr-take← : ∀ (m : Maybe (Tb.Listed X)) {k e} → TakeT (TR m) k e → TR (Took i keep m) k e
  tr-take← nothing tk = ⊥-elim (none tk)
  tr-take← (just L) tk = takeRows i keep L , refl , TakeX.complete-t i keep (TR (just L)) L (ex-just L) tk

  -- A take's row lies at or under its child's.
  take-row : ∀ {t : EmissionSet X} {k e} → TakeT t k e → Σ Pos λ y → Σ (Ev X) λ e₀ → t y e₀ × y ≼ k
  take-row {k = k} (pass x _ _)      = k , _ , x , ≼-refl {k}
  take-row (fail {q} x _ _ _)        = q , _ , x , ≺→≼ {q} {q ⊕ [ ix 0 ]} (≺-ext q [])
  take-row (stop {q} x _ _)          = q , _ , x , ≺→≼ {q} {q ⊕ [ last ]} (≺-ext q [])
  take-row {k = k} (step x _)        = k , _ , x , ≼-refl {k}
  take-row {k = k} (tend x _)        = k , _ , x , ≼-refl {k}
  take-row {k = k} (left x _ _)      = k , _ , x , ≼-refl {k}

  -- Whether a row fails before `k`, a table fails at all, a position is
  -- under a failing value: each read off the table's rows.
  private
    bad? : ∀ k (r : Pos × Ev X) → Dec (Σ X λ a → proj₂ r ≡ out a × T (not (keep a)) × proj₁ r ≺ k)
    bad? k (q , out a) with T? (not (keep a)) | T? (q <ᵖ k)
    ... | yes nk | yes lt = yes (a , refl , nk , lt)
    ... | no n   | _      = no λ { (_ , refl , nk , _) → n nk }
    ... | yes _  | no n   = no λ { (_ , refl , _ , lt) → n lt }
    bad? k (q , skip)  = no λ { (_ , () , _) }
    bad? k (q , end)   = no λ { (_ , () , _) }
    bad? k (q , pin _) = no λ { (_ , () , _) }

    val? : ∀ (r : Pos × Ev X) → Dec (Σ X λ a → proj₂ r ≡ out a × T (not (keep a)))
    val? (q , out a) with T? (not (keep a))
    ... | yes nk = yes (a , refl , nk)
    ... | no n   = no λ { (_ , refl , nk) → n nk }
    val? (q , skip)  = no λ { (_ , () , _) }
    val? (q , end)   = no λ { (_ , () , _) }
    val? (q , pin _) = no λ { (_ , () , _) }

    at? : ∀ w (r : Pos × Ev X) → Dec (Σ X λ a → Σ Label λ l → proj₂ r ≡ out a × T (not (keep a)) × Lab l × w ≡ proj₁ r ⊕ [ l ])
    at? w (y , out a) with T? (not (keep a)) | w ≟ᵖ (y ⊕ [ ix 0 ]) | w ≟ᵖ (y ⊕ [ last ])
    ... | no n   | _      | _      = no λ { (_ , _ , refl , nk , _) → n nk }
    ... | yes nk | yes e  | _      = yes (a , ix 0 , refl , nk , inj₁ refl , e)
    ... | yes nk | no _   | yes e  = yes (a , last , refl , nk , inj₂ refl , e)
    ... | yes nk | no n₀  | no n₁  = no λ { (_ , _ , refl , _ , inj₁ refl , e) → n₀ e ; (_ , _ , refl , _ , inj₂ refl , e) → n₁ e }
    at? w (y , skip)  = no λ { (_ , _ , () , _) }
    at? w (y , end)   = no λ { (_ , _ , () , _) }
    at? w (y , pin _) = no λ { (_ , _ , () , _) }

  failed? : ∀ (m : Maybe (Tb.Listed X)) w → Dec (TakeWhile.Failed i keep (TR m) w)
  failed? nothing w = no λ { (_ , _ , (_ , () , _) , _) }
  failed? (just L) w with any? (bad? w) (rows L)
  ... | yes h with find h
  ...   | (q , _) , mem , (a , refl , nk , lt) = yes (q , a , (L , refl , mem) , nk , lt)
  failed? (just L) w | no n = no λ { (q , a , (_ , refl , mem) , nk , lt) → n (lose mem (a , refl , nk , lt)) }

  fails? : ∀ (m : Maybe (Tb.Listed X)) → Dec (Σ Pos λ y → Σ X λ a → TR m y (out a) × T (not (keep a)))
  fails? nothing = no λ { (_ , _ , (_ , () , _) , _) }
  fails? (just L) with any? val? (rows L)
  ... | yes h with find h
  ...   | (q , _) , mem , (a , refl , nk) = yes (q , a , (L , refl , mem) , nk)
  fails? (just L) | no n = no λ { (q , a , (_ , refl , mem) , nk) → n (lose mem (a , refl , nk)) }

  UnderAt : Maybe (Tb.Listed X) → Pos → Set
  UnderAt m w = Σ Pos λ y → Σ X λ a → Σ Label λ l → TR m y (out a) × T (not (keep a)) × Lab l × w ≡ y ⊕ [ l ]

  under? : ∀ (m : Maybe (Tb.Listed X)) w → Dec (UnderAt m w)
  under? nothing w = no λ { (_ , _ , _ , (_ , () , _) , _) }
  under? (just L) w with any? (at? w) (rows L)
  ... | yes h with find h
  ...   | (y , _) , mem , (a , l , refl , nk , lb , eq) = yes (y , a , l , (L , refl , mem) , nk , lb , eq)
  under? (just L) w | no n = no λ { (y , a , l , (_ , refl , mem) , nk , lb , eq) → n (lose mem (a , l , refl , nk , lb , eq)) }

  -- THE TAKE'S MAP: the child's, but under a failing value, which goes
  -- under its image.
  moved : (Pos → Pos) → Maybe (Tb.Listed X) → Pos → Pos
  moved φ m w with under? m w
  ... | yes (y , _ , l , _) = φ y ⊕ [ l ]
  ... | no _ = φ w

  -- Children mapping alike, moved alike.
  moved-cong : ∀ {φ φ′ : Pos → Pos} m → (∀ w → φ w ≡ φ′ w) → ∀ w → moved φ m w ≡ moved φ′ m w
  moved-cong m e w with under? m w
  ... | yes (y , _ , l , _) = cong (_⊕ [ l ]) (e y)
  ... | no _ = e w

  moved-old : ∀ φ m → (∀ {y e l ys e′} → TR m y e → TR m (y ⊕ (l ∷ ys)) e′ → ⊥) → ∀ {k e} → TR m k e → moved φ m k ≡ φ k
  moved-old φ m fl {k} x with under? m k
  ... | yes (y , _ , l , xy , _ , _ , refl) = ⊥-elim (fl xy x)
  ... | no _ = refl

  moved-new : ∀ φ m {y a l} → TR m y (out a) → T (not (keep a)) → Lab l → moved φ m (y ⊕ [ l ]) ≡ φ y ⊕ [ l ]
  moved-new φ m {y} {a} {l} x nk lb with under? m (y ⊕ [ l ])
  ... | yes (y′ , _ , l′ , _ , _ , _ , eq) with ⊕-injˡ y y′ eq | ⊕-injʳ y y′ eq
  ...   | refl | refl = refl
  moved-new φ m {y} {a} {l} x nk lb | no n = ⊥-elim (n (y , a , l , x , nk , lb , refl))

------------------------------------------------------------------------
-- The record

module TakeTab {A : Set} (i : Bool) (q : A → Bool) {P : ℕ → Maybe (Tb.Listed A)} {Q : ℕ → Maybe (Tb.Listed (IE A))} {s s* : Pos}
  (R : Rel P Q s s*) where

  module R = Rel R
  module Tp = Take i q
  module Te = Take i (passes q)

  P′ : ℕ → Maybe (Tb.Listed A)
  P′ N = Took i q (P N)

  Q′ : ℕ → Maybe (Tb.Listed (IE A))
  Q′ N = Took i (passes q) (Q N)

  run : ∀ N → Run (TR (P N))
  run N = record { func = R.func {N} ; flat = R.flat {N} ; pin-in = R.pin-in {N} }

  run* : ∀ N → Run (TR (Q N))
  run* N = record { func = R.func* {N} ; flat = R.flat* {N} ; pin-in = R.pin-in* {N} }

  φ′ : ℕ → Pos → Pos
  φ′ N = moved i q (R.φ N) (P N)

  old : ∀ N {k e} → TR (P N) k e → φ′ N k ≡ R.φ N k
  old N = moved-old i q (R.φ N) (P N) (R.flat {N})

  new : ∀ N {y a l} → TR (P N) y (out a) → T (not (q a)) → Lab l → φ′ N (y ⊕ [ l ]) ≡ R.φ N y ⊕ [ l ]
  new N = moved-new i q (R.φ N) (P N)

  module K (N : ℕ) = TakeCut i q (R.corr N) (run N) (run* N)
    (λ w → keys (P N) , λ x _ → in-keys x) (λ w → keys (Q N) , λ x _ → in-keys x)
    (failed? i q (P N)) (failed? i (passes q) (Q N)) (φ′ N) (old N) (new N)

  to : ∀ {N k e} → K.TT N k e → TR (P′ N) k e
  to {N} = tr-take← i q (P N)

  from : ∀ {N k e} → TR (P′ N) k e → K.TT N k e
  from {N} = tr-take→ i q (P N)

  to* : ∀ {N k e} → K.UU N k e → TR (Q′ N) k e
  to* {N} = tr-take← i (passes q) (Q N)

  from* : ∀ {N k e} → TR (Q′ N) k e → K.UU N k e
  from* {N} = tr-take→ i (passes q) (Q N)

  corr : ∀ N → Corr s s* (φ′ N) (K.Put′ N) (K.Late′ N) (TR (P′ N)) (TR (Q′ N))
  corr N = corr-≃ (to {N}) (from {N}) (to* {N}) (from* {N}) (K.corr-take N)

  under≼ : ∀ o l → o ≼ (o ⊕ [ l ])
  under≼ o l = ≺→≼ {o} {o ⊕ [ l ]} (≺-ext o [])

  in-bk : ∀ {N k e} → TR (P′ N) k e → Unpinned e → ¬ K.Late′ N k → k ∈ under-bk (R.bk N) (φ′ N k)
  in-bk {N} {k} x un nl with K.O.kind N (from x) un
  ... | K.O.kept xk _ _ = subst (λ z → k ∈ under-bk (R.bk N) z) (sym (old N xk)) (∈-++⁺ˡ (R.in-bk xk un (K.nl-kept N xk nl)))
  ... | K.O.made {o} xo nk _ (l , refl , m) =
    subst (λ z → (o ⊕ [ l ]) ∈ under-bk (R.bk N) z) (sym (new N xo nk (Tp.made-lab m))) (in-under (R.bk N) (Tp.made-lab m) (R.in-bk xo tt (K.nl-out N xo)))

  pb-in : ∀ N l {k} → K.Put′ N k l → k ∈ (proj₁ (R.pb-few N l) ++ proj₁ (R.pb-few N (parent l)))
  pb-in N l (_ , _ , inj₁ (pl , _)) = ∈-++⁺ˡ (proj₂ (R.pb-few N l) pl)
  pb-in N l {k = k} (_ , _ , inj₂ (y , pl , _ , eq)) =
    ∈-++⁺ʳ (proj₁ (R.pb-few N l)) (subst (λ z → k ∈ proj₁ (R.pb-few N z)) (sym (trans (cong parent eq) (parent-snoc y (lab i)))) (proj₂ (R.pb-few N y) pl))

  after-φ : ∀ {N k e} → TR (P′ N) k e → Unpinned e → ¬ K.Late′ N k → s* ≼ φ′ N k
  after-φ {N} x un nl with K.O.kind N (from x) un
  ... | K.O.kept xk _ _ = subst (s* ≼_) (sym (old N xk)) (R.after-φ xk un (K.nl-kept N xk nl))
  ... | K.O.made {o} xo nk _ (l , refl , m) =
    subst (s* ≼_) (sym (new N xo nk (Tp.made-lab m))) (≼-trans {s*} {R.φ N o} {R.φ N o ⊕ [ l ]} (R.after-φ xo tt (K.nl-out N xo)) (under≼ (R.φ N o) l))

  pin-after* : ∀ {N l r} → TR (Q′ N) l (pin r) → s* ≼ r
  pin-after* {N} y with from* {N} y
  ... | K.W*.left y′ _ _ = R.pin-after* y′

  module TB  = TakeB i q (λ N → TR (P N)) R.Bd run (λ N → failed? i q (P N)) (λ N w → keys (P N) , λ x _ → in-keys x) R.bounded
  module TB* = TakeB i (passes q) (λ N → TR (Q N)) R.Bd* run* (λ N → failed? i (passes q) (Q N)) (λ N w → keys (Q N) , λ x _ → in-keys x) R.bounded*

  -- THE TAKE'S PAIR: the take's rows before a kept boundary are the
  -- child's, and its late placements move onto a failing value's mark.
  -- `TakePair` proves the pair for placements that stay at their row.
  postulate
    take-bcorr : ∀ N → Inter.BCorr (Own (TR (P′ N)) (K.Late′ N)) (φ′ N) (OwnPut (TR (P′ N)) (K.Put′ N)) (TB.Bd′ N) (TB*.Bd′ N)

  rel′ : Rel P′ Q′ s s*
  rel′ = record
    { φ = φ′ ; Put = K.Put′ ; Late = K.Late′ ; corr = corr ; bk = λ N → under-bk (R.bk N) ; in-bk = in-bk
    ; pb-few = λ N l → (proj₁ (R.pb-few N l) ++ proj₁ (R.pb-few N (parent l))) , pb-in N l
    ; Bd = TB.Bd′ ; Bd* = TB*.Bd′ ; bounded = bounded-≃ to from TB.bounded′ ; bounded* = bounded-≃ to* from* TB*.bounded′ ; bcorr = take-bcorr
    ; func = λ {N} x x′ → Run.func (K.O.run-T N) (from x) (from x′)
    ; func* = λ {N} y y′ → Run.func (K.O*.run-T N) (from* y) (from* y′)
    ; flat = λ {N} x x′ → Run.flat (K.O.run-T N) (from x) (from x′)
    ; flat* = λ {N} y y′ → Run.flat (K.O*.run-T N) (from* y) (from* y′)
    ; pin-in = λ {N} x → Run.pin-in (K.O.run-T N) (from x)
    ; pin-in* = λ {N} y → Run.pin-in (K.O*.run-T N) (from* y)
    ; got = λ N → got-bind (takeRows i q) (R.got N)
    ; got* = λ N → got-bind (takeRows i (passes q)) (R.got* N)
    ; after = λ {N} {k} x → let (y , _ , x₀ , le) = take-row i q (from x) in ≼-trans {s} {y} {k} (R.after x₀) le
    ; after* = λ {N} {l} y → let (w , _ , y₀ , le) = take-row i (passes q) (from* y) in ≼-trans {s*} {w} {l} (R.after* y₀) le
    ; after-φ = after-φ ; pin-after* = pin-after* }

take-tab : ∀ {A} (i : Bool) (q : A → Bool) {P Q s s*} → Rel P Q s s*
         → Rel (λ N → bind (P N) λ l → just (takeRows i q l)) (λ N → bind (Q N) λ l → just (takeRows i (passes q) l)) s s*
take-tab i q R = TakeTab.rel′ i q R

-- Children mapping alike, taken alike.
take-cong : ∀ {A} (i : Bool) (q : A → Bool) {P Q s s*} (R R′ : Rel P Q s s*)
          → (∀ N y → Same R R′ N y) → ∀ N y → Same (take-tab i q R) (take-tab i q R′) N y
take-cong i q {P} R R′ e N y = same (moved-cong i q (P N) (λ y → φ≡ (e N y)) y) (λ { nl (x , lt) → nl→ (e N y) (λ lt₀ → nl (x , lt₀)) lt })
