{-# OPTIONS --guardedness #-}

-- `takeWhile`'S CASE (`take-tab`): a plain takeWhile and the elaborated
-- one carry their child's record.  The map is the child's, but for the
-- two rows under the first failing value, which go under its image
-- (`moved`); each cut's correspondence is `TakeCut`'s.  Every lifting
-- fact reads a take's row as kept, so its child's row past no failure, or
-- made under the first failure: agreement crosses the take back at a kept
-- row (`lift`) or the first failure (`lift-fail`), the child's fact moves
-- it to the image, and the take carries it forward (`push`, `push-fail`).
--
-- Past the elaborated first failure only pins survive, kept where their
-- connect lies before it; two cuts agreeing on the plain take keep the
-- same such pins because the child's pins stay (`pin-stable`).
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
open import simultaneous.TableCorr using (TR; Corr; Rel; module Rel; ag-≃; corr-≃; keys; in-keys; tr-few; got-bind)
open import simultaneous.TakeKit using (Run; Lab; lab; ≼-last; module Take)
open import simultaneous.TakeCut using (inst-⊕; module TakeCut)

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

  module T2 N N′ = Tp.Two (run N) (run N′) (tr-few (P N) (P N′)) (R.cons {N} {N′}) (R.cons {N′} {N})
  module T2* N N′ = Te.Two (run* N) (run* N′) (tr-few (Q N) (Q N′)) (R.cons* {N} {N′}) (R.cons* {N′} {N})

  to : ∀ {N k e} → K.TT N k e → TR (P′ N) k e
  to {N} = tr-take← i q (P N)

  from : ∀ {N k e} → TR (P′ N) k e → K.TT N k e
  from {N} = tr-take→ i q (P N)

  to* : ∀ {N k e} → K.UU N k e → TR (Q′ N) k e
  to* {N} = tr-take← i (passes q) (Q N)

  from* : ∀ {N k e} → TR (Q′ N) k e → K.UU N k e
  from* {N} = tr-take→ i (passes q) (Q N)

  ag→ : ∀ {N N′ k} → AgreeTo k (TR (P′ N)) (TR (P′ N′)) → AgreeTo k (K.TT N) (K.TT N′)
  ag→ {N} {N′} = ag-≃ (from {N}) (to {N}) (from {N′}) (to {N′})

  ag→* : ∀ {N N′ k} → AgreeTo k (TR (Q′ N)) (TR (Q′ N′)) → AgreeTo k (K.UU N) (K.UU N′)
  ag→* {N} {N′} = ag-≃ (from* {N}) (to* {N}) (from* {N′}) (to* {N′})

  ag←* : ∀ {N N′ k} → AgreeTo k (K.UU N) (K.UU N′) → AgreeTo k (TR (Q′ N)) (TR (Q′ N′))
  ag←* {N} {N′} = ag-≃ (to* {N}) (from* {N}) (to* {N′}) (from* {N′})

  ag← : ∀ {N N′ k} → AgreeTo k (K.TT N) (K.TT N′) → AgreeTo k (TR (P′ N)) (TR (P′ N′))
  ag← {N} {N′} = ag-≃ (to {N}) (from {N}) (to {N′}) (from {N′})

  corr : ∀ N → Corr s s* (φ′ N) (K.Put′ N) (TR (P′ N)) (TR (Q′ N))
  corr N = corr-≃ (to {N}) (from {N}) (to* {N}) (from* {N}) (K.corr-take N)

  under≼ : ∀ o l → o ≼ (o ⊕ [ l ])
  under≼ o l = ≺→≼ {o} {o ⊕ [ l ]} (≺-ext o [])

  pin-of : ∀ {N y r} → K.TT N y (pin r) → TR (P N) y (pin r)
  pin-of (K.W.left x _ _) = x

  -- A child's pin whose connect no failure precedes is the take's.
  hp-take : ∀ {N N′ k} → (∀ {y r} → r ≼ k → TR (P′ N′) y (pin r) → TR (P′ N) y (pin r))
          → ¬ K.W.Failed N′ k → ∀ {y r} → r ≼ k → TR (P N′) y (pin r) → TR (P N) y (pin r)
  hp-take {N} {N′} {k} hp nF {r = r} rk x₀ =
    pin-of {N} (from {N} (hp rk (to {N′} (K.W.left x₀ (λ F → nF (K.O.failed-≼ N′ {r} {k} rk F)) (R.pin-in x₀)))))

  ----------------------------------------------------------------------
  -- The lifting facts

  φ-agree : ∀ {N N′ k e} → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N)) (TR (P′ N′)) → φ′ N k ≡ φ′ N′ k
  φ-agree {N} {N′} {k} x un ag with K.O.kind N (from x) un
  ... | K.O.kept xk nF nf =
    let agt = T2.lift N N′ (ag→ ag) (from x) (≼-refl {k}) nF nf
    in trans (old N xk) (trans (R.φ-agree xk un agt) (sym (old N′ (proj₁ (upto agt (≼-refl {k})) xk))))
  ... | K.O.made {o} xo nk nF (l , refl , m) =
    let lb  = Tp.made-lab m
        agt = T2.lift-fail N N′ (ag→ ag) (from x) (under≼ o l) xo nk nF
    in trans (new N xo nk lb) (trans (cong (_⊕ [ l ]) (R.φ-agree xo tt agt)) (sym (new N′ (proj₁ (upto agt (≼-refl {o})) xo) nk lb)))

  in-bk : ∀ {N k e} → TR (P′ N) k e → Unpinned e → k ∈ under-bk (R.bk N) (φ′ N k)
  in-bk {N} {k} x un with K.O.kind N (from x) un
  ... | K.O.kept xk _ _ = subst (λ z → k ∈ under-bk (R.bk N) z) (sym (old N xk)) (∈-++⁺ˡ (R.in-bk xk un))
  ... | K.O.made {o} xo nk _ (l , refl , m) =
    subst (λ z → (o ⊕ [ l ]) ∈ under-bk (R.bk N) z) (sym (new N xo nk (Tp.made-lab m))) (in-under (R.bk N) (Tp.made-lab m) (R.in-bk xo tt))

  pb-in : ∀ N l {k} → K.Put′ N k l → k ∈ (proj₁ (R.pb-few N l) ++ proj₁ (R.pb-few N (parent l)))
  pb-in N l (_ , _ , inj₁ (pl , _)) = ∈-++⁺ˡ (proj₂ (R.pb-few N l) pl)
  pb-in N l {k = k} (_ , _ , inj₂ (y , pl , _ , eq)) =
    ∈-++⁺ʳ (proj₁ (R.pb-few N l)) (subst (λ z → k ∈ proj₁ (R.pb-few N z)) (sym (trans (cong parent eq) (parent-snoc y (lab i)))) (proj₂ (R.pb-few N y) pl))

  elab-causal : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
              → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
  elab-causal {N} {N′} {k} le x un ag with K.O.kind N (from x) un
  ... | K.O.kept xk nF nf =
    let agt = AgreeTo-sym (T2.lift N N′ (AgreeTo-sym (ag→ ag)) (from x) (≼-refl {k}) nF nf)
    in subst (λ z → AgreeTo z (TR (Q′ N′)) (TR (Q′ N))) (sym (old N xk)) (ag←* (T2*.push N′ N (R.elab-causal le xk un agt)))
  ... | K.O.made {o} xo nk nF (l , refl , m) =
    let lb  = Tp.made-lab m
        agt = AgreeTo-sym (T2.lift-fail N N′ (AgreeTo-sym (ag→ ag)) (from x) (under≼ o l) xo nk nF)
        agu = R.elab-causal le xo tt agt
        (x* , y , rd) = K.img-out N xo
        nF* = λ F → nF (K.fail← N xo tt F)
        pf = T2*.push-fail N′ N agu (proj₂ (upto agu (≼-refl {R.φ N o})) y) (K.nk* N rd nk)
               (T2*.unfail N N′ (AgreeTo-sym agu) (≼-refl {R.φ N o}) nF*)
    in subst (λ z → AgreeTo z (TR (Q′ N′)) (TR (Q′ N))) (sym (new N xo nk lb))
         (ag←* (ag-down {q = R.φ N o ⊕ [ last ]} {R.φ N o ⊕ [ l ]} (≼-last {R.φ N o} lb) pf))

  stable← : ∀ {N N′ k e e′} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′
          → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo k (TR (P′ N′)) (TR (P′ N))
  stable← {N} {N′} {k} {e′ = e′} le x un y ag* with K.O.kind N (from x) un
  ... | K.O.kept xk nF nf =
    let eq  = old N xk
        uy  = subst (λ z → K.UU N z e′) eq (from* y)
        ag′ = subst (λ z → AgreeTo z (K.UU N′) (K.UU N)) eq (ag→* ag*)
        agu = T2*.lift N N′ (AgreeTo-sym ag′) uy (≼-refl {R.φ N k}) (λ F → nF (K.fail← N xk un F)) (K.img-nofail N xk un nf)
    in ag← (T2.push N′ N (R.stable← le xk un (K.kept-self N xk un nF nf uy) (AgreeTo-sym agu)))
  ... | K.O.made {o} {a} xo nk nF (l , refl , m) =
    let lb  = Tp.made-lab m
        eq  = new N xo nk lb
        uy  = subst (λ z → K.UU N z e′) eq (from* y)
        ag′ = subst (λ z → AgreeTo z (K.UU N′) (K.UU N)) eq (ag→* ag*)
        (x* , yo , rd) = K.img-out N xo
        agu = T2*.lift-fail N N′ (AgreeTo-sym ag′) uy (under≼ (R.φ N o) l) yo (K.nk* N rd nk) (λ F → nF (K.fail← N xo tt F))
        agt = R.stable← le xo tt yo (AgreeTo-sym agu)
        pf  = T2.push-fail N′ N agt (proj₂ (upto agt (≼-refl {o})) xo) nk (T2.unfail N N′ (AgreeTo-sym agt) (≼-refl {o}) nF)
    in ag← (ag-down {q = o ⊕ [ last ]} {o ⊕ [ l ]} (≼-last {o} lb) pf)

  stable-put : ∀ {N N′ k l e′} → N ≤ N′ → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → TR (Q′ N) l e′ → K.Put′ N k l
             → AgreeTo l (TR (Q′ N′)) (TR (Q′ N))
  stable-put {N} {N′} {k} {l} {e′} le ag y ((_ , tk) , nFk , br) = go br
    where
      agt : AgreeTo k (TR (P N′)) (TR (P N))
      agt = AgreeTo-sym (T2.lift N N′ (AgreeTo-sym (ag→ ag)) tk (≼-refl {k}) nFk (K.O.nofail N tk nFk))

      go : (R.Put N k l × Σ (Ev (IE A)) (TR (Q N) l)) ⊎ (Σ Pos λ z → R.Put N k z × K.Failing* N z × l ≡ z ⊕ [ lab i ])
         → AgreeTo l (TR (Q′ N′)) (TR (Q′ N))
      go (inj₁ (pl , _ , ul)) = ag←* (T2*.push N′ N (R.stable-put le agt ul pl))
      go (inj₂ (z , pl , (x* , yz , nk*) , eq)) =
        let agu = R.stable-put le agt yz pl
            nF* = K.under-unfailed N yz (subst (λ w → K.UU N w e′) eq (from* y))
            pf  = T2*.push-fail N′ N agu (proj₂ (upto agu (≼-refl {z})) yz) nk* (T2*.unfail N N′ (AgreeTo-sym agu) (≼-refl {z}) nF*)
        in subst (λ w → AgreeTo w (TR (Q′ N′)) (TR (Q′ N))) (sym eq) (ag←* (ag-down {q = z ⊕ [ last ]} {z ⊕ [ lab i ]} (≼-last {z} (lab-Lab i)) pf))

  -- Agreement up to the elaborated first failure's last row, read from
  -- agreement at a row past it.
  upto-fail : ∀ {N N′ m e* f b} → TR (Q′ N) m e* → AgreeTo m (TR (Q′ N′)) (TR (Q′ N))
            → TR (Q N) f (out b) → T (not (passes q b)) → ¬ K.W*.Failed N f → f ≼ m
            → AgreeTo (f ⊕ [ last ]) (TR (Q′ N′)) (TR (Q′ N))
  upto-fail {N} {N′} {f = f} z ag* yf nkf nFf fm =
    let aguf = T2*.lift-fail N N′ (AgreeTo-sym (ag→* ag*)) (from* z) fm yf nkf nFf
    in ag←* (T2*.push-fail N′ N (AgreeTo-sym aguf) (proj₁ (upto aguf (≼-refl {f})) yf) nkf (T2*.unfail N N′ aguf (≼-refl {f}) nFf))

  stable-lead : ∀ {N N′ k e e′ m e*} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′ → Corr.Leads (corr N) k
              → TR (Q′ N) m e* → instantOf m ≡ instantOf (φ′ N k) → AgreeTo m (TR (Q′ N′)) (TR (Q′ N))
              → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
  stable-lead {N} {N′} {k} {e} {e′} {m} le x un y ld z ie ag* with K.O.kind N (from x) un | failed? i (passes q) (Q N) m
  ... | K.O.kept xk nF nf | yes (f₀ , _ , y₀ , nk₀ , lt₀) with K.fst* N y₀ nk₀
  ...   | f , _ , yf , nkf , nFf , ff₀ with K.shown-fail N yf nkf
  ...     | kf , _ , refl , xkf , nkkf , _ =
    subst (λ w → AgreeTo w (TR (Q′ N′)) (TR (Q′ N))) (sym (old N xk))
      (ag-down {q = R.φ N kf ⊕ [ last ]} {R.φ N k}
        (≺→≼ {R.φ N k} {R.φ N kf ⊕ [ last ]} (≺-trans {R.φ N k} {R.φ N kf} {R.φ N kf ⊕ [ last ]}
          (Corr.mono (R.corr N) xk xkf un tt (K.before-fail N xk nF nf xkf nkkf)) (≺-ext (R.φ N kf) [])))
        (upto-fail z ag* yf nkf nFf (≺→≼ {R.φ N kf} {m} (≼-≺-≺ {R.φ N kf} {f₀} {m} ff₀ lt₀))))
  stable-lead {N} {N′} {k} {e} {e′} {m} le x un y ld z ie ag* | K.O.made {o} xo nk nF (l , refl , mm) | yes (f₀ , _ , y₀ , nk₀ , lt₀) with K.fst* N y₀ nk₀
  ...   | f , _ , yf , nkf , nFf , ff₀ with K.first-img N yf nkf nFf xo nk nF
  ...     | refl =
    subst (λ w → AgreeTo w (TR (Q′ N′)) (TR (Q′ N))) (sym (new N xo nk (Tp.made-lab mm)))
      (ag-down {q = R.φ N o ⊕ [ last ]} {R.φ N o ⊕ [ l ]} (≼-last {R.φ N o} (Tp.made-lab mm))
        (upto-fail z ag* yf nkf nFf (≺→≼ {R.φ N o} {m} (≼-≺-≺ {R.φ N o} {f₀} {m} ff₀ lt₀))))
  stable-lead {N} {N′} {k} {e} {e′} {m} le x un y ld z ie ag* | K.O.kept xk nF nf | no nFm =
    subst (λ w → AgreeTo w (TR (Q′ N′)) (TR (Q′ N))) (sym eq) (ag←* (T2*.push N′ N agφ))
    where
      eq : φ′ N k ≡ R.φ N k
      eq = old N xk

      um = from* z
      agu = T2*.lift N N′ (AgreeTo-sym (ag→* ag*)) um (≼-refl {m}) nFm (K.O*.nofail N um nFm)

      cld : Corr.Leads (R.corr N) k
      cld {k′} x′ un′ ie′ with ≼-or-≻ k k′
      ... | inj₁ h = h
      ... | inj₂ k′k = ld (to (K.O.keep-row N x′ (λ F → nF (K.O.failed-≼ N (≺→≼ {k′} {k} k′k) F)) (K.O.nofail< N nF k′k))) un′ ie′

      agφ = R.stable-lead le xk un (K.kept-self N xk un nF nf (subst (λ w → K.UU N w e′) eq (from* y))) cld
              (K.unfailed-self N um nFm) (trans ie (cong instantOf eq)) (AgreeTo-sym agu)
  stable-lead {N} {N′} {k} {e} {e′} {m} le x un y ld z ie ag* | K.O.made {o} xo nk nF (l , refl , mm) | no nFm =
    subst (λ w → AgreeTo w (TR (Q′ N′)) (TR (Q′ N))) (sym eq) (ag←* (ag-down {q = R.φ N o ⊕ [ last ]} {R.φ N o ⊕ [ l ]} (≼-last {R.φ N o} lb) pf))
    where
      lb = Tp.made-lab mm
      eq = new N xo nk lb
      img = K.img-out N xo

      um = from* z
      agu = T2*.lift N N′ (AgreeTo-sym (ag→* ag*)) um (≼-refl {m}) nFm (K.O*.nofail N um nFm)

      cld : Corr.Leads (R.corr N) o
      cld {k′} x′ un′ ie′ with ≼-or-≻ o k′
      ... | inj₁ h = h
      ... | inj₂ k′o =
        ⊥-elim (ld (to (K.O.keep-row N x′ (λ F → nF (K.O.failed-≼ N (≺→≼ {k′} {o} k′o) F)) (K.O.nofail< N nF k′o))) un′
                  (trans ie′ (sym (inst-⊕ o [ l ]))) (≺-trans {k′} {o} {o ⊕ [ l ]} k′o (≺-ext o [])))

      agφ = R.stable-lead le xo tt (proj₁ (proj₂ img)) cld (K.unfailed-self N um nFm)
              (trans ie (trans (cong instantOf eq) (inst-⊕ (R.φ N o) [ l ]))) (AgreeTo-sym agu)
      pf = T2*.push-fail N′ N agφ (proj₂ (upto agφ (≼-refl {R.φ N o})) (proj₁ (proj₂ img))) (K.nk* N (proj₂ (proj₂ img)) nk)
             (T2*.unfail N N′ (AgreeTo-sym agφ) (≼-refl {R.φ N o}) (λ F → nF (K.fail← N xo tt F)))

  -- With no failing value, the takes keep every row; their children agree.
  no-fail : ∀ {N N′} → N ≤ N′ → (∀ w → AgreeTo w (TR (P′ N′)) (TR (P′ N)))
          → ¬ (Σ Pos λ y → Σ A λ a → TR (P N′) y (out a) × T (not (q a))) → ∀ {y e} → K.UU N′ y e → K.UU N y e
  no-fail {N} {N′} le all none {y} {e} uy = go (K.O*.from N′ uy)
    where
      nf′ : ∀ {z} → K.O.NoFail N′ z
      nf′ {z} {a} x′ with Tp.dec-keep a
      ... | inj₁ p  = p
      ... | inj₂ nk = ⊥-elim (none (z , a , x′ , nk))

      agt : ∀ w → AgreeTo w (TR (P N′)) (TR (P N))
      agt = T2.lift-all N′ N (λ w → ag→ (all w)) (λ {z} → nf′ {z})

      noneN : ∀ {z x} → TR (Q N) z (out x) → T (not (passes q x)) → ⊥
      noneN yz nk with K.shown-fail N yz nk
      ... | kf , a , _ , xkf , nkf , _ = none (kf , a , proj₂ (upto (agt kf) (≼-refl {kf})) xkf , nkf)

      noneN′ : ∀ {z x} → TR (Q N′) z (out x) → T (not (passes q x)) → ⊥
      noneN′ yz nk with K.shown-fail N′ yz nk
      ... | kf , a , _ , xkf , nkf , _ = none (kf , a , xkf , nkf)

      nf* : K.O*.NoFail N y
      nf* {x} yx with Te.dec-keep x
      ... | inj₁ p  = p
      ... | inj₂ nk = ⊥-elim (noneN yx nk)

      go : K.O*.From N′ y e → K.UU N y e
      go (K.O*.self y′ _)     = K.O*.keep-row N (R.elab-all le agt y′) (λ { (_ , _ , yf , nkf , _) → noneN yf nkf }) nf*
      go (K.O*.new yo nk _ _) = ⊥-elim (noneN′ yo nk)

  -- Past a failing value, the takes agree up to its image's last row,
  -- and keep only pins beyond it.
  past-fail : ∀ {N N′ kf a} → N ≤ N′ → (∀ w → AgreeTo w (TR (P′ N′)) (TR (P′ N)))
            → TR (P N′) kf (out a) → T (not (q a)) → ¬ K.W.Failed N′ kf → ∀ {y e} → K.UU N′ y e → K.UU N y e
  past-fail {N} {N′} {kf} {a} le all xkf nkf nFkf {y} {e} uy = go (≼-or-≻ y (R.φ N kf ⊕ [ last ])) uy
    where
      agtk : AgreeTo kf (TR (P N′)) (TR (P N))
      agtk = T2.lift-fail N′ N (ag→ (all (kf ⊕ [ last ]))) (K.O.made-row N′ xkf nkf nFkf Tp.atl) (under≼ kf last) xkf nkf nFkf

      xkfN = proj₁ (upto agtk (≼-refl {kf})) xkf
      agu = R.elab-causal le xkfN tt agtk
      img = K.img-out N xkfN
      ykf′ = proj₂ (upto agu (≼-refl {R.φ N kf})) (proj₁ (proj₂ img))
      nk* = K.nk* N (proj₂ (proj₂ img)) nkf
      nF*′ = T2*.unfail N N′ (AgreeTo-sym agu) (≼-refl {R.φ N kf}) (λ F → T2.unfail N′ N agtk (≼-refl {kf}) nFkf (K.fail← N xkfN tt F))
      pf = T2*.push-fail N′ N agu ykf′ nk* nF*′

      gone : ∀ {y e} → (R.φ N kf ⊕ [ last ]) ≺ y → K.UU N′ y e → Unpinned e → ⊥
      gone {y} ly uy un with K.O*.kind N′ uy un
      ... | K.O*.kept _ nF′ _ = nF′ (R.φ N kf , proj₁ img , ykf′ , nk* , ≺-trans {R.φ N kf} {R.φ N kf ⊕ [ last ]} {y} (≺-ext (R.φ N kf) []) ly)
      ... | K.O*.made {o} yo nk′ nFo (l , refl , mm) with K.O*.first-uniq N′ yo nk′ nFo ykf′ nk* nF*′
      ...   | refl = ≼-last {R.φ N kf} (Te.made-lab mm) ly

      beyond : ∀ {y e} → (R.φ N kf ⊕ [ last ]) ≺ y → K.UU N′ y e → K.UU N y e
      beyond {e = pin r} ly (K.W*.left y′ nF′ ins) =
        let rk : r ≼ R.φ N kf
            rk lt = nF′ (R.φ N kf , proj₁ img , ykf′ , nk* , lt)
        in K.W*.left (R.pin-stable le xkfN tt agtk (hp-take (λ {y₁} _ x₁ → proj₁ (upto (all y₁) (≼-refl {y₁})) x₁) nFkf) rk y′)
                     (T2*.unfail N′ N agu rk nF′) ins
      beyond {e = out _} ly uy = ⊥-elim (gone ly uy tt)
      beyond {e = skip}  ly uy = ⊥-elim (gone ly uy tt)
      beyond {e = end}   ly uy = ⊥-elim (gone ly uy tt)

      go : y ≼ (R.φ N kf ⊕ [ last ]) ⊎ (R.φ N kf ⊕ [ last ]) ≺ y → K.UU N′ y e → K.UU N y e
      go (inj₁ yl) uy′ = proj₁ (upto pf yl) uy′
      go (inj₂ ly) uy′ = beyond ly uy′

  elab-all : ∀ {N N′} → N ≤ N′ → (∀ w → AgreeTo w (TR (P′ N′)) (TR (P′ N))) → ∀ {y e} → TR (Q′ N′) y e → TR (Q′ N) y e
  elab-all {N} {N′} le all yr with fails? i q (P N′)
  ... | no none = to* (no-fail le all none (from* yr))
  ... | yes (_ , _ , x₀ , nk₀) with K.fst N′ x₀ nk₀
  ...   | _ , _ , xkf , nkf , nFkf , _ = to* (past-fail le all xkf nkf nFkf (from* yr))

  after-φ : ∀ {N k e} → TR (P′ N) k e → Unpinned e → s* ≼ φ′ N k
  after-φ {N} x un with K.O.kind N (from x) un
  ... | K.O.kept xk _ _ = subst (s* ≼_) (sym (old N xk)) (R.after-φ xk un)
  ... | K.O.made {o} xo nk _ (l , refl , m) =
    subst (s* ≼_) (sym (new N xo nk (Tp.made-lab m))) (≼-trans {s*} {R.φ N o} {R.φ N o ⊕ [ l ]} (R.after-φ xo tt) (under≼ (R.φ N o) l))

  pin-after* : ∀ {N l r} → TR (Q′ N) l (pin r) → s* ≼ r
  pin-after* {N} y with from* {N} y
  ... | K.W*.left y′ _ _ = R.pin-after* y′

  pin-stable : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
             → (∀ {y r} → r ≼ k → TR (P′ N′) y (pin r) → TR (P′ N) y (pin r))
             → ∀ {y r} → r ≼ φ′ N k → TR (Q′ N′) y (pin r) → TR (Q′ N) y (pin r)
  pin-stable {N} {N′} {k} le x un ag hp {r = r} rk yq with from* {N′} yq | K.O.kind N (from x) un
  ... | K.W*.left y′ nF′ ins | K.O.kept xk nF nf =
    let agt = AgreeTo-sym (T2.lift N N′ (AgreeTo-sym (ag→ ag)) (from x) (≼-refl {k}) nF nf)
        rφ  = subst (r ≼_) (old N xk) rk
        agu = R.elab-causal le xk un agt
    in to* (K.W*.left (R.pin-stable le xk un agt (hp-take hp (T2.unfail N N′ (AgreeTo-sym agt) (≼-refl {k}) nF)) rφ y′)
                      (T2*.unfail N′ N agu rφ nF′) ins)
  ... | K.W*.left y′ nF′ ins | K.O.made {o} xo nk nF (l , refl , m) =
    let agt = AgreeTo-sym (T2.lift-fail N N′ (AgreeTo-sym (ag→ ag)) (from x) (under≼ o l) xo nk nF)
        agu = R.elab-causal le xo tt agt
        (x* , yo , rd) = K.img-out N xo
        yo′ = proj₂ (upto agu (≼-refl {R.φ N o})) yo
        rφ : r ≼ R.φ N o
        rφ lt = nF′ (R.φ N o , x* , yo′ , K.nk* N rd nk , lt)
        hp′ : ∀ {y r₀} → r₀ ≼ o → TR (P′ N′) y (pin r₀) → TR (P′ N) y (pin r₀)
        hp′ {r₀ = r₀} r₀o = hp (≼-trans {r₀} {o} {o ⊕ [ l ]} r₀o (under≼ o l))
    in to* (K.W*.left (R.pin-stable le xo tt agt (hp-take hp′ (T2.unfail N N′ (AgreeTo-sym agt) (≼-refl {o}) nF)) rφ y′)
                      (T2*.unfail N′ N agu rφ nF′) ins)

  postulate
    -- THE TAKE'S CUTS BACK: a cut agreeing up to a row's image agrees up
    -- to the row, and a late placement moves between cuts agreeing up to
    -- its row or its place.
    take-back     : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → AgreeTo (φ′ N′ k) (TR (Q′ N′)) (TR (Q′ N))
                  → AgreeTo k (TR (P′ N′)) (TR (P′ N))
    take-put-up   : ∀ {N N′ k l} → N ≤ N′ → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → K.Put′ N k l → K.Put′ N′ k l
    take-back-put : ∀ {N N′ k l} → N ≤ N′ → K.Put′ N′ k l → AgreeTo l (TR (Q′ N′)) (TR (Q′ N)) → K.Put′ N k l

  rel′ : Rel P′ Q′ s s*
  rel′ = record
    { φ = φ′ ; Put = K.Put′ ; corr = corr ; φ-agree = φ-agree ; bk = λ N → under-bk (R.bk N) ; in-bk = in-bk
    ; pb-few = λ N l → (proj₁ (R.pb-few N l) ++ proj₁ (R.pb-few N (parent l))) , pb-in N l
    ; back = take-back ; put-up = take-put-up ; back-put = take-back-put
    ; elab-causal = elab-causal ; stable← = stable← ; stable-put = stable-put ; stable-lead = stable-lead ; elab-all = elab-all
    ; func = λ {N} x x′ → Run.func (K.O.run-T N) (from x) (from x′)
    ; func* = λ {N} y y′ → Run.func (K.O*.run-T N) (from* y) (from* y′)
    ; flat = λ {N} x x′ → Run.flat (K.O.run-T N) (from x) (from x′)
    ; flat* = λ {N} y y′ → Run.flat (K.O*.run-T N) (from* y) (from* y′)
    ; pin-in = λ {N} x → Run.pin-in (K.O.run-T N) (from x)
    ; pin-in* = λ {N} y → Run.pin-in (K.O*.run-T N) (from* y)
    ; cons = λ {N} {N′} below x x′ yy → to (T2.cons-T N N′ (λ lt → ag→ (below lt)) (from x) (from x′) yy)
    ; cons* = λ {N} {N′} below y y′ yy → to* (T2*.cons-T N N′ (λ lt → ag→* (below lt)) (from* y) (from* y′) yy)
    ; got = λ N → got-bind (takeRows i q) (R.got N)
    ; got* = λ N → got-bind (takeRows i (passes q)) (R.got* N)
    ; after = λ {N} {k} x → let (y , _ , x₀ , le) = take-row i q (from x) in ≼-trans {s} {y} {k} (R.after x₀) le
    ; after* = λ {N} {l} y → let (w , _ , y₀ , le) = take-row i (passes q) (from* y) in ≼-trans {s*} {w} {l} (R.after* y₀) le
    ; after-φ = after-φ ; pin-after* = pin-after* ; pin-stable = pin-stable }

take-tab : ∀ {A} (i : Bool) (q : A → Bool) {P Q s s*} → Rel P Q s s*
         → Rel (λ N → bind (P N) λ l → just (takeRows i q l)) (λ N → bind (Q N) λ l → just (takeRows i (passes q) l)) s s*
take-tab i q R = TakeTab.rel′ i q R
