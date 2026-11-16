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
-- connect lies before it; whether two cuts agreeing on the plain take
-- keep the same such pins is owed (`take-pins`).
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
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Few; _≺_; _≼_; module TakeWhile)
open import denotation.Laws.Modulus using (AgreeTo; upto; AgreeTo-sym; ag-down; ≺-trans; ≺-irrefl; ≼-refl; ≺→≼; ≼-trans; ≼-or-≻; ≼-≺-≺; ≺-ext)
open import denotation.Laws.Worlds using (⊕-injˡ; ⊕-injʳ)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (rows; bind; takeRows)
open import quickcheck.Tabled.Exact.Base using (Exact)
open import quickcheck.Tabled.Exact using (module TakeX)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf; parent; parent-snoc)
open import simultaneous.TableCorr using (TR; Corr; Rel; module Rel; ag-≃; corr-≃; keys; in-keys; tr-few)
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

postulate
  -- THE TAKE'S LATE PINS.  Two cuts agreeing on the whole plain take keep
  -- the same elaborated pins: those past the elaborated first failure
  -- read rows the plain take no longer constrains.
  take-pins : ∀ {A} (i : Bool) (q : A → Bool) {P Q s s*} → Rel P Q s s* → ∀ {N N′} → N ≤ N′
            → (∀ k → AgreeTo k (TR (Took i q (P N′))) (TR (Took i q (P N))))
            → ∀ {y r} → TR (Took i (passes q) (Q N′)) y (pin r) → TR (Took i (passes q) (Q N)) y (pin r)

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

  in-bk : ∀ {N k e} → TR (P′ N) k e → Unpinned e → k ∈ under-bk R.bk (φ′ N k)
  in-bk {N} {k} x un with K.O.kind N (from x) un
  ... | K.O.kept xk _ _ = subst (λ z → k ∈ under-bk R.bk z) (sym (old N xk)) (∈-++⁺ˡ (R.in-bk xk un))
  ... | K.O.made {o} xo nk _ (l , refl , m) =
    subst (λ z → (o ⊕ [ l ]) ∈ under-bk R.bk z) (sym (new N xo nk (Tp.made-lab m))) (in-under R.bk (Tp.made-lab m) (R.in-bk xo tt))

  pb-in : ∀ l {N k} → K.Put′ N k l → k ∈ (proj₁ (R.pb-few l) ++ proj₁ (R.pb-few (parent l)))
  pb-in l (_ , _ , inj₁ (pl , _)) = ∈-++⁺ˡ (proj₂ (R.pb-few l) pl)
  pb-in l {k = k} (_ , _ , inj₂ (y , pl , _ , eq)) =
    ∈-++⁺ʳ (proj₁ (R.pb-few l)) (subst (λ z → k ∈ proj₁ (R.pb-few z)) (sym (trans (cong parent eq) (parent-snoc y (lab i)))) (proj₂ (R.pb-few y) pl))

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
