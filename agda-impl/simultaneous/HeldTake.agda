{-# OPTIONS --guardedness #-}

-- A TAKEWHILE HOLDS WHAT ITS SOURCE HOLDS.  A run met of a take is a run
-- met of its source (`back`), or one cut at the source's first failing
-- row (`Cut`): its source's run up to that row, then the one or two rows
-- the take puts under it, the row itself and the end.  Both sit in the
-- failing row's instant and carry its routes, and a failing row is a
-- value or a completion, so the count reads them as the source's one
-- row.
--
-- A position the take has nothing before but its source has: past the
-- first failure, under it, so named for its instant.
module simultaneous.HeldTake where

open import Data.Bool using (Bool; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Properties using (∷-injective; ++-assoc; ++-identityʳ; foldl-++)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁻ˡ to all-++⁻ˡ)
open import Data.List.Relation.Unary.Any using (here; there) renaming (map to any-map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc) renaming (_≟_ to _≟ⁿ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to ⊎-map)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (decidable-stable; _⊎-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import denotation.Position using (Pos; Label; root; _≟ᵖ_; ix; last; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; skip; pin; Den; enter; module Op; module TakeWhile; Unpinned;
  Seen; Few; _≺_; _≼_)
open import denotation.Read using (Run; []; _∷_; Visible; After; Least; cursor)
open import denotation.Laws.Modulus using (T-not; few-ind; reach-few; entered-reach; ≺-trans; ≺-irrefl; ≺→≼; ≼-refl; ≼-trans;
  ≼-or-≻; ≼-split; ≼-≺-≺; ≺-ext)
open import denotation.Laws.Worlds using (InvD; InvAt; _⊑_; ⊑-trans; ⊑-inside; inside-⊑)
open import adequacy.SubOne using (take-reach; below-or-under)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; stop; over; completed)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (rootOf)
open import simultaneous.Relations using (Met; values; values-++)
open import simultaneous.Shut using (Shut; r₀)
open import simultaneous.Routed using (Held; HeldD; Early; Sync; Ex; Carried; c-value; Routing; r-completed; Idle; Rest; cnt; nameOf; nm;
  Valued; opos)
open import simultaneous.HeldConnect using (rootOf-ext; early-inst)
open import simultaneous.Layers using (cursor-snoc; after-≺)
open import simultaneous.TakeKit using (apart; ix<last; module Take) renaming (Run to Shape)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; count; passes)

------------------------------------------------------------------------
-- Lists

-- Two ways to cut one list.
++-split : ∀ {B : Set} (xs ys r₁ r₂ : List B) → xs ++ ys ≡ r₁ ++ r₂
         → (Σ (List B) λ m → r₁ ≡ xs ++ m × ys ≡ m ++ r₂) ⊎ (Σ (List B) λ m → xs ≡ r₁ ++ m × r₂ ≡ m ++ ys)
++-split []       ys r₁       r₂ eq = inj₁ (r₁ , refl , eq)
++-split (x ∷ xs) ys []       r₂ eq = inj₂ (x ∷ xs , refl , sym eq)
++-split (x ∷ xs) ys (z ∷ r₁) r₂ eq with ∷-injective eq
... | refl , eq′ with ++-split xs ys r₁ r₂ eq′
...   | inj₁ (m , e₁ , e₂) = inj₁ (m , cong (x ∷_) e₁ , e₂)
...   | inj₂ (m , e₁ , e₂) = inj₂ (m , cong (x ∷_) e₁ , e₂)

-- The same, about a row: it falls in the second part, or in the first.
++-split′ : ∀ {B : Set} (xs ys r₁ : List B) z r₂ → xs ++ ys ≡ r₁ ++ z ∷ r₂
          → (Σ (List B) λ m → r₁ ≡ xs ++ m × ys ≡ m ++ z ∷ r₂) ⊎ (Σ (List B) λ m → xs ≡ r₁ ++ z ∷ m × r₂ ≡ m ++ ys)
++-split′ []       ys r₁       z r₂ eq = inj₁ (r₁ , refl , eq)
++-split′ (x ∷ xs) ys []       z r₂ eq with ∷-injective eq
... | refl , eq′ = inj₂ (xs , refl , sym eq′)
++-split′ (x ∷ xs) ys (w ∷ r₁) z r₂ eq with ∷-injective eq
... | refl , eq′ with ++-split′ xs ys r₁ z r₂ eq′
...   | inj₁ (m , e₁ , e₂) = inj₁ (m , cong (x ∷_) e₁ , e₂)
...   | inj₂ (m , e₁ , e₂) = inj₂ (m , cong (x ∷_) e₁ , e₂)

-- Nothing is met past an end.
past-end : ∀ {B : Set} {t : EmissionSet B} {c rs} → t c end → Run t (just c) rs → rs ≡ []
past-end _ []                                   = refl
past-end x ((((_ , pr) , _) , _ , ac , _) ∷ _) = ⊥-elim (pr x ac)

------------------------------------------------------------------------
-- A take's run, read back to its source's

module TakeBack {A : Set} {H : Pos → Set} (incl : Bool) (keep : A → Bool) (d : Den A) (p : Pos) (iv : InvAt H p (enter d p)) where

  S : EmissionSet A
  S = enter d p

  Tk : EmissionSet A
  Tk = enter (Op.takeWhile incl keep d) p

  R : Shape S
  R = record { func = InvAt.func iv ; flat = InvAt.flat iv ; pin-in = λ x → proj₂ (InvAt.pinned iv x) }

  open TakeWhile incl keep S public
  open Take incl keep public using (Made; at0; atl)
  open Take.One incl keep R public using (NoFail; Kind; kept; made; kind; keep-row; nofail<; failed-≼; first-uniq)

  up : ∀ {y e} → TakeT y e → Tk y e
  up x = x , take-reach (entered-reach d p) (InvAt.flat iv) x

  vis-un : ∀ {e : Ev A} → Visible e → Unpinned e
  vis-un {out _} _ = tt
  vis-un {end}   _ = tt
  vis-un {skip}  ()
  vis-un {pin _} ()

  few-S : ∀ {q e} → Visible e → S q e → Few S q
  few-S {q} {out a} _ x = reach-few {t = S} {q} {out a} (λ {_} {_} → tt) (entered-reach d p x)
  few-S {q} {end}   _ x = reach-few {t = S} {q} {end} (λ {_} {_} → tt) (entered-reach d p x)

  -- Below a position no failure precedes, the source's rows are the take's.
  below : ∀ {w k e} → ¬ Failed w → S k e → k ≺ w → Tk k e
  below {w} {k} nF x kw = up (keep-row x (λ F → nF (failed-≼ {k} {w} (≺→≼ {k} {w} kw) F)) (nofail< nF kw))

  -- Where a reader of the take stands: nowhere yet, or at a kept row.
  data Cur : Maybe Pos → Set where
    c-none : Cur nothing
    c-at   : ∀ {r e} → S r e → ¬ Failed r → NoFail r → Cur (just r)

  cur-before : ∀ {c f a} → Cur c → S f (out a) → T (not (keep a)) → After c f
  cur-before c-none _ _ = tt
  cur-before {f = f} {a} (c-at {r} x nF nf) xf nk with ≼-or-≻ r f
  ... | inj₂ fr = ⊥-elim (nF (f , a , xf , nk , fr))
  ... | inj₁ rf with ≼-split {r} {f} rf
  ...   | inj₁ lt   = lt
  ...   | inj₂ refl = ⊥-elim (T-not (nf xf) nk)

  Entry : EmissionSet A → Maybe Pos → Pos → Ev A → Set
  Entry t c q e = Seen t q e × Visible e × Least t c q

  kept-entry : ∀ {c q e} → S q e → ¬ Failed q → Entry Tk c q e → Entry S c q e
  kept-entry x nF (((_ , pr) , _) , vi , ac , lf) =
    ((x , λ x′ cq → pr (below nF x′ cq) cq) , few-S vi x) , vi , ac , λ x′ v′ ak kq → lf (below nF x′ kq) v′ ak kq

  made-entry : ∀ {c f a l e} → Cur c → S f (out a) → T (not (keep a)) → ¬ Failed f → Entry Tk c (f ⊕ [ l ]) e → Entry S c f (out a)
  made-entry {f = f} {l = l} cur xf nk nF (((_ , pr) , _) , _ , _ , lf) =
    ((xf , λ {c′} x′ cf → pr (below nF x′ cf) (≺-trans {c′} {f} {f ⊕ [ l ]} cf (≺-ext f []))) , few-S tt xf) , tt , cur-before cur xf nk ,
    λ {k} x′ v′ ak kf → lf (below nF x′ kf) v′ ak (≺-trans {k} {f} {f ⊕ [ l ]} kf (≺-ext f []))

  -- What a take puts under its first failing value, as it is met.
  data Tl (f : Pos) (a : A) : List (Pos × Ev A) → Set where
    tl-v  : T incl → Tl f a [ (f ⊕ [ ix 0 ] , out a) ]
    tl-ve : T incl → Tl f a ((f ⊕ [ ix 0 ] , out a) ∷ (f ⊕ [ last ] , end) ∷ [])
    tl-e  : Tl f a [ (f ⊕ [ last ] , end) ]

  -- A run cut at the first failing value.
  data Cut (c : Maybe Pos) (rs : List (Pos × Ev A)) : Set where
    cut : ∀ {rs₀ tl f a} → rs ≡ rs₀ ++ tl → Run S c (rs₀ ++ [ (f , out a) ]) → S f (out a) → T (not (keep a)) → ¬ Failed f
        → Tl f a tl → Σ Label (λ l → cursor c rs ≡ just (f ⊕ [ l ])) → Cut c rs

  cons-cut : ∀ {c q e rs} → Entry S c q e → Cut (just q) rs → Cut c ((q , e) ∷ rs)
  cons-cut {q = q} {e} h (cut {rs₀} {tl} sp r fx nk nF sh ld) = cut {rs₀ = (q , e) ∷ rs₀} {tl = tl} (cong ((q , e) ∷_) sp) (h ∷ r) fx nk nF sh ld

  Back : Maybe Pos → List (Pos × Ev A) → Set
  Back c rs = (Run S c rs × Cur (cursor c rs)) ⊎ Cut c rs

  tail₂ : ∀ {c f a q′ e′ rs} → Cur c → S f (out a) → (nk : T (not (keep a))) → (nF : ¬ Failed f) → T incl
        → Entry Tk c (f ⊕ [ ix 0 ]) (out a) → Entry Tk (just (f ⊕ [ ix 0 ])) q′ e′ → Run Tk (just q′) rs → Kind q′ e′
        → Cut c ((f ⊕ [ ix 0 ] , out a) ∷ (q′ , e′) ∷ rs)
  tail₂ {f = f} {a} cur xf nk nF i en (_ , _ , ac , _) run′ (kept x nF′ _) =
    ⊥-elim (nF′ (f , a , xf , nk , ≺-trans {f} {f ⊕ [ ix 0 ]} (≺-ext f []) ac))
  tail₂ {c} {f = f} cur xf nk nF i en en′ run′ (made xf′ nk′ nF′ (l′ , refl , m′)) with first-uniq xf nk nF xf′ nk′ nF′
  ... | refl with m′
  ...   | at0 _ = ⊥-elim (≺-irrefl {f ⊕ [ ix 0 ]} (proj₁ (proj₂ (proj₂ en′))))
  ...   | atl with past-end (up (stop xf nk nF)) run′
  ...     | refl = cut {rs₀ = []} refl (made-entry {c} cur xf nk nF en ∷ []) xf nk nF (tl-ve i) (last , refl)

  tail : ∀ {c f a l e rs} → Cur c → S f (out a) → (nk : T (not (keep a))) → (nF : ¬ Failed f) → Made a l e
       → Entry Tk c (f ⊕ [ l ]) e → Run Tk (just (f ⊕ [ l ])) rs → Cut c ((f ⊕ [ l ] , e) ∷ rs)
  tail {c} cur xf nk nF atl en run with past-end (up (stop xf nk nF)) run
  ... | refl = cut {rs₀ = []} refl (made-entry {c} cur xf nk nF en ∷ []) xf nk nF tl-e (last , refl)
  tail {c} cur xf nk nF (at0 i) en [] = cut {rs₀ = []} refl (made-entry {c} cur xf nk nF en ∷ []) xf nk nF (tl-v i) (ix 0 , refl)
  tail {c} cur xf nk nF (at0 i) en (en′ ∷ run′) =
    tail₂ {c} cur xf nk nF i en en′ run′ (kind (proj₁ (proj₁ (proj₁ (proj₁ en′)))) (vis-un (proj₁ (proj₂ en′))))

  cons : ∀ {c q e rs} → Entry S c q e → Back (just q) rs → Back c ((q , e) ∷ rs)
  cons h (inj₁ (r , cu)) = inj₁ (h ∷ r , cu)
  cons h (inj₂ ct)       = inj₂ (cons-cut h ct)

  mutual
    back : ∀ {c rs} → Cur c → Run Tk c rs → Back c rs
    back cur []         = inj₁ ([] , cur)
    back {c} cur (en ∷ run) = back-step {c} cur en run (kind (proj₁ (proj₁ (proj₁ (proj₁ en)))) (vis-un (proj₁ (proj₂ en))))

    back-step : ∀ {c q e rs} → Cur c → Entry Tk c q e → Run Tk (just q) rs → Kind q e → Back c ((q , e) ∷ rs)
    back-step {c} cur en run (kept x nF nf)                = cons {c} (kept-entry {c} x nF en) (back (c-at x nF nf) run)
    back-step {c} cur en run (made xf nk nF (l , refl , m)) = inj₂ (tail {c} cur xf nk nF m en run)

  -- THE FIRST FAILING VALUE, not constructively: under a stable goal.
  em : ∀ {P : Set} → ¬ ¬ (P ⊎ ¬ P)
  em k = k (inj₂ λ x → k (inj₁ x))

  First≼ : Pos → Set
  First≼ q = Σ Pos λ f → Σ A λ b → S f (out b) × T (not (keep b)) × ¬ Failed f × f ≼ q

  min-fail : ∀ {f₀ a₀} → S f₀ (out a₀) → T (not (keep a₀)) → ¬ ¬ First≼ f₀
  min-fail {f₀} x₀ nk₀ = few-ind {t = S} P go (few-S tt x₀) x₀ nk₀
    where
      P : Pos → Set
      P w = ∀ {a} → S w (out a) → T (not (keep a)) → ¬ ¬ First≼ w

      go : ∀ {w} → Few S w → (∀ {v e} → S v e → v ≺ w → P v) → P w
      go {w} _ ih {a} x nk k = em λ
        { (inj₂ nF) → k (w , a , x , nk , nF , ≼-refl {w})
        ; (inj₁ (q , b , xq , nkq , qw)) → ih xq qw xq nkq λ (f , c , xf , nkf , nFf , fq) →
            k (f , c , xf , nkf , nFf , ≼-trans {f} {q} {w} fq (≺→≼ {q} {w} qw)) }

------------------------------------------------------------------------
-- Positions

name-ext : ∀ y zs → nameOf (y ⊕ zs) ≡ nameOf y
name-ext y zs = cong nm (rootOf-ext y zs)

sync-ext : ∀ {c y} zs → Sync c y → Sync c (y ⊕ zs)
sync-ext {c} {y} zs (ins , rt) =
  ⊑-inside {c} {y ⊕ zs} (⊑-trans {c} {y} {y ⊕ zs} (inside-⊑ c y ins) (zs , refl)) , trans (rootOf-ext y zs) rt

ex-ext : ∀ {cs y} zs → Ex cs y → Ex cs (y ⊕ zs)
ex-ext {y = y} zs = any-map (λ {c} → sync-ext {c} {y} zs)

-- Past a position and at or before its last child: under it.
under-of : ∀ {f w} → f ≺ w → w ≼ (f ⊕ [ last ]) → nameOf w ≡ nameOf f
under-of {f} {w} fw wl with ≼-split {w} {f ⊕ [ last ]} wl
... | inj₂ refl = name-ext f [ last ]
... | inj₁ lt with below-or-under w f last lt
...   | inj₁ wf                = ⊥-elim (wf fw)
...   | inj₂ (l′ , ls , refl) = name-ext f (l′ ∷ ls)

------------------------------------------------------------------------
-- Held through a take

-- What a take may fail at: a value, or a completion.  Neither is
-- counted, and neither is a mark a reader routes by but the completion.
data Inert {X : Set} : IE X → Set where
  i-value : ∀ {v j} → Inert (instEmit (value v) j)
  i-done  : ∀ {j} → Inert (instEmit (mark completed) j)

-- No row failing `keep` has its first effect before `w`.
Unfailed : ∀ {X : Set} → (IE X → Bool) → EmissionSet (IE X) → Pos → Set
Unfailed keep t w = ∀ {f a} → t f (out a) → T (not (keep a)) → (f ⊕ [ ix 0 ]) ≺ w → ⊥

-- IDLE UP TO THE FIRST FAILURE: idle at every position no failing row's
-- first effect precedes.  All a take reads of its source's idleness.
IdleTo : ∀ {X : Set} → (IE X → Bool) → EmissionSet (IE X) → Set
IdleTo keep t = ∀ {rs} → Met t rs → (∀ {c} → (c , end) ∈ rs → ⊥) → ∀ {w} → Unfailed keep t w → Few t w → After (cursor nothing rs) w
              → (∀ {y e} → t y e → Visible e → After (cursor nothing rs) y → w ≼ y)
              → proj₂ (cnt rs) ≡ 0 ⊎ proj₁ (cnt rs) ≡ nameOf w

-- HELD UP TO THE FIRST FAILURE: held, idle only up to the first row
-- failing `keep`.  What a take needs of its source.
record HeldTo {X : Set} (keep : IE X → Bool) (t : EmissionSet (IE X)) (cs : List Pos) : Set where
  field
    named   : ∀ {y n} → t y (out (instEmit (mark begin) n)) → n ≡ nameOf y
    covered : ∀ {rs} → Met t rs → ∀ r₁ {y e} r₂ → rs ≡ r₁ ++ (y , e) ∷ r₂ → Carried e → ¬ Ex cs y
            → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
    exact   : ∀ {rs} → Met t rs → ∀ r₁ {y n} r₂ → rs ≡ r₁ ++ (y , out (instEmit (mark stop) n)) ∷ r₂
            → Σ ℕ λ k → proj₂ (cnt r₁) ≡ suc k
    routing : ∀ {y m n} → t y (out (instEmit (mark m) n)) → Routing m
    shut    : Shut t
    early   : ∀ {y a n} → t y (out (instEmit (value a) n)) → Early y
    ends    : ∀ {y} → t y end → Early y
    done    : ∀ {y n} → t y (out (instEmit (mark completed) n)) → Early y
    late    : ∀ {y n} → t y (out (instEmit (mark over) n)) → Valued (rootOf y) × opos (rootOf y) ⊑ y
    idle    : IdleTo keep t
    rest    : Rest t

held-to : ∀ {X : Set} {keep : IE X → Bool} {t cs} → Held t cs → HeldTo keep t cs
held-to h = record
  { named = H.named ; covered = H.covered ; exact = H.exact ; routing = H.routing ; shut = H.shut
  ; early = H.early ; ends = H.ends ; done = H.done ; late = H.late ; idle = λ m ne _ → H.idle m ne ; rest = H.rest }
  where module H = Held h

-- A TAKE HOLDS WHAT ITS SOURCE HOLDS when it fails only at inert rows
-- whose instant its source holds a route of, early ones.
module Holds {X : Set} (incl : Bool) (keep : IE X → Bool) (d : Den (IE X)) {H : Pos → Set} (cs : List Pos)
             (p : Pos) (iv : InvAt H p (enter d p)) (h : HeldTo keep (enter d p) cs)
             (fails : ∀ {x} → T (not (keep x)) → Inert x)
             (fcov : ∀ {rs} → Met (enter d p) rs → ∀ r₁ {y x} r₂ → rs ≡ r₁ ++ (y , out x) ∷ r₂ → T (not (keep x)) → ¬ Ex cs y
                   → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k))
             (fearly : ∀ {y x} → enter d p y (out x) → T (not (keep x)) → Early y) where

  open TakeBack {H = H} incl keep d p iv
  module HS = HeldTo h

  Row : Set
  Row = Pos × Ev (IE X)

  -- A row the count passes over: the failing value, or the end.
  Q : IE X → Row → Set
  Q a r = proj₂ r ≡ end ⊎ proj₂ r ≡ out a

  cnt-snoc : ∀ {a} → Inert a → ∀ xs {r} → Q a r → cnt (xs ++ [ r ]) ≡ cnt xs
  cnt-snoc _ xs {y , _} (inj₁ refl) = cong (L.foldl count r₀) (trans (values-++ xs [ (y , end) ]) (++-identityʳ (values xs)))
  cnt-snoc i-value xs {y , _} (inj₂ refl) =
    trans (cong (L.foldl count r₀) (values-++ xs [ (y , out _) ])) (foldl-++ count r₀ (values xs) _)
  cnt-snoc i-done xs {y , _} (inj₂ refl) =
    trans (cong (L.foldl count r₀) (values-++ xs [ (y , out _) ])) (foldl-++ count r₀ (values xs) _)

  cnt-pre : ∀ {a} → Inert a → ∀ xs (m : List Row) → All (Q a) m → cnt (xs ++ m) ≡ cnt xs
  cnt-pre va xs []      []       = cong cnt (++-identityʳ xs)
  cnt-pre va xs (r ∷ m) (q ∷ qs) =
    trans (cong cnt (sym (++-assoc xs [ r ] m))) (trans (cnt-pre va (xs ++ [ r ]) m qs) (cnt-snoc va xs q))

  tl-q : ∀ {f a tl} → Tl f a tl → All (Q a) tl
  tl-q (tl-v _)  = inj₂ refl ∷ []
  tl-q (tl-ve _) = inj₂ refl ∷ inj₁ refl ∷ []
  tl-q tl-e      = inj₁ refl ∷ []

  pre-q : ∀ {a tl} m {r} → All (Q a) tl → tl ≡ m ++ r → All (Q a) m
  pre-q m qs eq = all-++⁻ˡ m (subst (All _) eq qs)

  tl-val : ∀ {f a tl y x} → Tl f a tl → (y , out x) ∈ tl → y ≡ f ⊕ [ ix 0 ] × x ≡ a
  tl-val (tl-v _)  (here refl)         = refl , refl
  tl-val (tl-v _)  (there ())
  tl-val (tl-ve _) (here refl)         = refl , refl
  tl-val (tl-ve _) (there (here ()))
  tl-val (tl-ve _) (there (there ()))
  tl-val tl-e      (here ())
  tl-val tl-e      (there ())

  tl-row : ∀ {f a tl y e} → Tl f a tl → (y , e) ∈ tl → Σ Label λ l → y ≡ f ⊕ [ l ]
  tl-row (tl-v _)  (here refl)                = ix 0 , refl
  tl-row (tl-v _)  (there ())
  tl-row (tl-ve _) (here refl)                = ix 0 , refl
  tl-row (tl-ve _) (there (here refl))        = last , refl
  tl-row (tl-ve _) (there (there ()))
  tl-row tl-e      (here refl)                = last , refl
  tl-row tl-e      (there ())

  -- A begin met of a cut run is its source's.
  begin-in : ∀ {rs₀ tl f a q n} → Inert a → Tl f a tl → (q , out (instEmit (mark begin) n)) ∈ rs₀ ++ tl
           → (q , out (instEmit (mark begin) n)) ∈ rs₀
  begin-in {rs₀} i-value sh b with ∈-++⁻ rs₀ b
  ... | inj₁ i = i
  ... | inj₂ i with tl-val sh i
  ...   | _ , ()
  begin-in {rs₀} i-done sh b with ∈-++⁻ rs₀ b
  ... | inj₁ i = i
  ... | inj₂ i with tl-val sh i
  ...   | _ , ()

  ----------------------------------------------------------------------
  -- Row by row

  named : ∀ {y n} → Tk y (out (instEmit (mark begin) n)) → n ≡ nameOf y
  named (tk , _) with kind tk tt
  ... | kept x _ _                    = HS.named x
  ... | made _ nk _ (_ , refl , at0 _) with fails nk
  ...   | ()

  routing : ∀ {y m n} → Tk y (out (instEmit (mark m) n)) → Routing m
  routing (tk , _) with kind tk tt
  ... | kept x _ _                    = HS.routing x
  ... | made _ nk _ (_ , refl , at0 _) with fails nk
  ...   | i-done = r-completed

  late : ∀ {y n} → Tk y (out (instEmit (mark over) n)) → Valued (rootOf y) × opos (rootOf y) ⊑ y
  late (tk , _) with kind tk tt
  ... | kept x _ _                    = HS.late x
  ... | made _ nk _ (_ , refl , at0 _) with fails nk
  ...   | ()

  early : ∀ {y a n} → Tk y (out (instEmit (value a) n)) → Early y
  early (tk , _) with kind tk tt
  ... | kept x _ _                       = HS.early x
  ... | made xf nk _ (_ , refl , at0 _) = early-inst [ ix 0 ] (fearly xf nk)

  ends : ∀ {y} → Tk y end → Early y
  ends (tk , _) with kind tk tt
  ... | kept x _ _ = HS.ends x
  ... | made xf nk _ (_ , refl , atl) = early-inst [ last ] (fearly xf nk)

  done : ∀ {y n} → Tk y (out (instEmit (mark completed) n)) → Early y
  done (tk , _) with kind tk tt
  ... | kept x _ _                       = HS.done x
  ... | made xf nk _ (_ , refl , at0 _) = early-inst [ ix 0 ] (fearly xf nk)

  ----------------------------------------------------------------------
  -- Run by run

  covered-cut : ∀ {rs} → Cut nothing rs → ∀ r₁ {y e} r₂ → rs ≡ r₁ ++ (y , e) ∷ r₂ → Carried e → ¬ Ex cs y
              → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
  covered-cut (cut {rs₀} {tl} {f} {a} refl run fx nk nF sh _) r₁ {y} {e} r₂ eq ce nx with ++-split′ rs₀ tl r₁ (y , e) r₂ eq
  ... | inj₂ (m , refl , refl) = HS.covered run r₁ (m ++ [ (f , out a) ]) (++-assoc r₁ ((y , e) ∷ m) _) ce nx
  ... | inj₁ (m , refl , teq) with tl-row sh (subst ((y , e) ∈_) (sym teq) (∈-++⁺ʳ m (here refl)))
  ...   | l , refl with fcov run rs₀ [] refl nk (λ ex → nx (ex-ext [ l ] ex))
  ...     | k , c = k , trans (cnt-pre (fails nk) rs₀ m (pre-q m (tl-q sh) teq)) (trans c (cong (λ z → z , suc k) (sym (name-ext f [ l ]))))

  covered : ∀ {rs} → Met Tk rs → ∀ r₁ {y e} r₂ → rs ≡ r₁ ++ (y , e) ∷ r₂ → Carried e → ¬ Ex cs y
          → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
  covered m r₁ r₂ eq ce nx with back c-none m
  ... | inj₁ (m′ , _) = HS.covered m′ r₁ r₂ eq ce nx
  ... | inj₂ ct       = covered-cut ct r₁ r₂ eq ce nx

  exact-cut : ∀ {rs} → Cut nothing rs → ∀ r₁ {y n} r₂ → rs ≡ r₁ ++ (y , out (instEmit (mark stop) n)) ∷ r₂
            → Σ ℕ λ k → proj₂ (cnt r₁) ≡ suc k
  exact-cut (cut {rs₀} {tl} {f} {a} refl run fx nk nF sh _) r₁ {y} {n} r₂ eq
    with fails nk | ++-split′ rs₀ tl r₁ (y , out (instEmit (mark stop) n)) r₂ eq
  ... | _ | inj₂ (m , refl , refl) = HS.exact run r₁ (m ++ [ (f , out a) ]) (++-assoc r₁ (_ ∷ m) _)
  ... | i-value | inj₁ (m , refl , teq) with tl-val sh (subst (_ ∈_) (sym teq) (∈-++⁺ʳ m (here refl)))
  ...   | _ , ()
  exact-cut (cut {rs₀} {tl} {f} {a} refl run fx nk nF sh _) r₁ {y} {n} r₂ eq | i-done | inj₁ (m , refl , teq)
    with tl-val sh (subst (_ ∈_) (sym teq) (∈-++⁺ʳ m (here refl)))
  ... | _ , ()

  exact : ∀ {rs} → Met Tk rs → ∀ r₁ {y n} r₂ → rs ≡ r₁ ++ (y , out (instEmit (mark stop) n)) ∷ r₂
        → Σ ℕ λ k → proj₂ (cnt r₁) ≡ suc k
  exact m r₁ r₂ eq with back c-none m
  ... | inj₁ (m′ , _) = HS.exact m′ r₁ r₂ eq
  ... | inj₂ ct       = exact-cut ct r₁ r₂ eq

  shut-cut : ∀ {rs} → Cut nothing rs → ∀ r₁ r₂ → rs ≡ r₁ ++ r₂ → proj₂ (cnt r₁) ≡ 0
           → ∀ {q} → (q , out (instEmit (mark begin) (proj₁ (cnt r₁)))) ∈ r₁
           → ∀ {y a j} → (y , out (instEmit (value a) j)) ∈ r₂ → rootOf y ≡ rootOf q → ⊥
  shut-cut (cut {rs₀} {tl} {f} {a} refl run fx nk nF sh _) r₁ r₂ eq z {q} bq {y} yv rt with ++-split rs₀ tl r₁ r₂ eq
  ... | inj₁ (m , refl , teq) with tl-val sh (subst (_ ∈_) (sym teq) (∈-++⁺ʳ m yv))
  ...   | refl , refl =
    HS.shut run rs₀ [ (f , out a) ] refl (trans (cong proj₂ (sym E)) z)
      (subst (λ n → (q , out (instEmit (mark begin) (proj₁ n))) ∈ rs₀) E (begin-in (fails nk) sh (pre-in bq)))
      (here refl) (trans (sym (rootOf-ext f [ ix 0 ])) rt)
    where
      E : cnt (rs₀ ++ m) ≡ cnt rs₀
      E = cnt-pre (fails nk) rs₀ m (pre-q m (tl-q sh) teq)
      pre-in : ∀ {x} → x ∈ rs₀ ++ m → x ∈ rs₀ ++ tl
      pre-in {x} i with ∈-++⁻ rs₀ i
      ... | inj₁ i₀ = ∈-++⁺ˡ i₀
      ... | inj₂ i₁ = ∈-++⁺ʳ rs₀ (subst (x ∈_) (sym teq) (∈-++⁺ˡ i₁))
  shut-cut (cut {rs₀} {tl} {f} {a} refl run fx nk nF sh _) r₁ r₂ eq z {q} bq {y} yv rt | inj₂ (m , refl , refl)
    with ∈-++⁻ m yv
  ... | inj₁ i = HS.shut run r₁ (m ++ [ (f , out a) ]) (++-assoc r₁ m _) z bq (∈-++⁺ˡ i) rt
  ... | inj₂ i with tl-val sh i
  ...   | refl , refl = HS.shut run r₁ (m ++ [ (f , out a) ]) (++-assoc r₁ m _) z bq (∈-++⁺ʳ m (here refl))
                          (trans (sym (rootOf-ext f [ ix 0 ])) rt)

  shut : Shut Tk
  shut m r₁ r₂ eq z bq yv rt with back c-none m
  ... | inj₁ (m′ , _) = HS.shut m′ r₁ r₂ eq z bq yv rt
  ... | inj₂ ct       = shut-cut ct r₁ r₂ eq z bq yv rt

  ----------------------------------------------------------------------
  -- Idle

  unf : ∀ {w} → ¬ Failed w → Unfailed keep S w
  unf {w} nF {f} {a} x nk fw = nF (f , a , x , nk , ≺-trans {f} {f ⊕ [ ix 0 ]} {w} (≺-ext f {ix 0} []) fw)

  unf₀ : ∀ {f a} → S f (out a) → ¬ Failed f → Unfailed keep S (f ⊕ [ ix 0 ])
  unf₀ {f} fx nF {g} {b} x nk gf with below-or-under g f (ix 0) (≺-trans {g} {g ⊕ [ ix 0 ]} {f ⊕ [ ix 0 ]} (≺-ext g {ix 0} []) gf)
  ... | inj₂ (l′ , ls , refl) = InvAt.flat iv fx x
  ... | inj₁ gf′ with ≼-split {g} {f} gf′
  ...   | inj₁ lt   = nF (g , b , x , nk , lt)
  ...   | inj₂ refl = ≺-irrefl {g ⊕ [ ix 0 ]} gf

  Goal : List Row → Pos → Set
  Goal rs w = proj₂ (cnt rs) ≡ 0 ⊎ proj₁ (cnt rs) ≡ nameOf w

  idle-clean : ∀ {rs} → Met S rs → Cur (cursor nothing rs) → (∀ {c} → (c , end) ∈ rs → ⊥) → ∀ {w} → Few Tk w
             → After (cursor nothing rs) w → (∀ {y e} → Tk y e → Visible e → After (cursor nothing rs) y → w ≼ y) → Goal rs w
  idle-clean {rs} m cu ne {w} fw aw lw =
    decidable-stable ((proj₂ (cnt rs) ≟ⁿ 0) ⊎-dec (proj₁ (cnt rs) ≟ᵖ nameOf w)) λ ng → em λ
      { (inj₂ nF) → ng (HS.idle m ne (unf nF) (proj₁ fw , λ x kw → proj₂ fw (below nF x kw) kw) aw (λ x v ay yw → lw (below nF x yw) v ay yw))
      ; (inj₁ (f₀ , a₀ , x₀ , nk₀ , f₀w)) → min-fail x₀ nk₀ λ (f , b , xf , nkf , nFf , ff₀) →
          let fw′ = ≼-≺-≺ {f} {f₀} {w} ff₀ f₀w
              stp = lw (up (stop xf nkf nFf)) tt (after-≺ (cursor nothing rs) (cur-before cu xf nkf) (≺-ext f []))
          in ng (⊎-map (λ z → z) (λ e → trans e (sym (under-of {f} {w} fw′ stp)))
                  (HS.idle m ne (unf nFf) (few-S tt xf) (cur-before cu xf nkf) λ {y} x v ay yf → lw (below nFf x yf) v ay (≺-trans {y} {f} {w} yf fw′))) }

  idle-v : ∀ {rs₀ f a} → Inert a → Met S (rs₀ ++ [ (f , out a) ]) → S f (out a)
         → T (not (keep a)) → ¬ Failed f
         → (∀ {c} → (c , end) ∈ rs₀ ++ [ (f ⊕ [ ix 0 ] , out a) ] → ⊥) → ∀ {w}
         → After (cursor nothing (rs₀ ++ [ (f ⊕ [ ix 0 ] , out a) ])) w
         → (∀ {y e} → Tk y e → Visible e → After (cursor nothing (rs₀ ++ [ (f ⊕ [ ix 0 ] , out a) ])) y → w ≼ y)
         → Goal (rs₀ ++ [ (f ⊕ [ ix 0 ] , out a) ]) w
  idle-v {rs₀} {f} {a} va run fx nk nF ne {w} aw lw =
    ⊎-map (λ z → trans (cong proj₂ E) z) (λ e → trans (cong proj₁ E) (trans e (trans (name-ext f [ ix 0 ]) (sym nmw))))
      (HS.idle run ne′ (unf₀ fx nF) few0 aft0 least0)
    where
      E : cnt (rs₀ ++ [ (f ⊕ [ ix 0 ] , out a) ]) ≡ cnt (rs₀ ++ [ (f , out a) ])
      E = trans (cnt-snoc va rs₀ (inj₂ refl)) (sym (cnt-snoc va rs₀ (inj₂ refl)))

      aw′ : (f ⊕ [ ix 0 ]) ≺ w
      aw′ = subst (λ c → After c w) (cursor-snoc nothing rs₀) aw

      nmw : nameOf w ≡ nameOf f
      nmw = under-of {f} {w} (≺-trans {f} {f ⊕ [ ix 0 ]} {w} (≺-ext f []) aw′)
              (lw (up (stop fx nk nF)) tt (subst (λ c → After c (f ⊕ [ last ])) (sym (cursor-snoc nothing rs₀)) (ix<last f)))

      ne′ : ∀ {c} → (c , end) ∈ rs₀ ++ [ (f , out a) ] → ⊥
      ne′ x with ∈-++⁻ rs₀ x
      ... | inj₁ i         = ne (∈-++⁺ˡ i)
      ... | inj₂ (here ())
      ... | inj₂ (there ())

      few0 : Few S (f ⊕ [ ix 0 ])
      few0 = f ∷ proj₁ (few-S tt fx) , go
        where
          go : ∀ {k e′} → S k e′ → k ≺ (f ⊕ [ ix 0 ]) → k ∈ f ∷ proj₁ (few-S tt fx)
          go {k} x kf with below-or-under k f (ix 0) kf
          ... | inj₂ (l′ , ls , refl) = ⊥-elim (InvAt.flat iv fx x)
          ... | inj₁ kf′ with ≼-split {k} {f} kf′
          ...   | inj₁ lt   = there (proj₂ (few-S tt fx) x lt)
          ...   | inj₂ refl = here refl

      aft0 : After (cursor nothing (rs₀ ++ [ (f , out a) ])) (f ⊕ [ ix 0 ])
      aft0 = subst (λ c → After c (f ⊕ [ ix 0 ])) (sym (cursor-snoc nothing rs₀)) (≺-ext f [])

      least0 : ∀ {y e} → S y e → Visible e → After (cursor nothing (rs₀ ++ [ (f , out a) ])) y → (f ⊕ [ ix 0 ]) ≼ y
      least0 {y} x _ ay = ≺→≼ {f ⊕ [ ix 0 ]} {y} (apart R [ ix 0 ] fx x (subst (λ c → After c y) (cursor-snoc nothing rs₀) ay))

  idle-cut : ∀ {rs} → Cut nothing rs → (∀ {c} → (c , end) ∈ rs → ⊥) → ∀ {w}
           → After (cursor nothing rs) w → (∀ {y e} → Tk y e → Visible e → After (cursor nothing rs) y → w ≼ y) → Goal rs w
  idle-cut (cut {rs₀} refl run fx nk nF (tl-ve _) _) ne _ _ = ⊥-elim (ne (∈-++⁺ʳ rs₀ (there (here refl))))
  idle-cut (cut {rs₀} refl run fx nk nF tl-e _)     ne _ _ = ⊥-elim (ne (∈-++⁺ʳ rs₀ (here refl)))
  idle-cut (cut {rs₀} refl run fx nk nF (tl-v _) _) ne aw lw = idle-v (fails nk) run fx nk nF ne aw lw

  idle : Idle Tk
  idle m ne fw aw lw with back c-none m
  ... | inj₁ (m′ , cu) = idle-clean m′ cu ne fw aw lw
  ... | inj₂ ct        = idle-cut ct ne aw lw

  ----------------------------------------------------------------------
  -- Rest

  rest-clean : ∀ {rs} → Met S rs → Cur (cursor nothing rs) → proj₂ (cnt rs) ≡ 0
             → ∀ {q} → (q , out (instEmit (mark begin) (proj₁ (cnt rs)))) ∈ rs
             → Σ (List Pos) λ ks → ∀ {y e} → Tk y e → After (cursor nothing rs) y → rootOf y ≡ rootOf q → y ∈ ks
  rest-clean {rs} m cu z {q} bq = ks ++ L.map (_⊕ [ ix 0 ]) ks ++ L.map (_⊕ [ last ]) ks , go
    where
      ks : List Pos
      ks = proj₁ (HS.rest m z bq)

      hk : ∀ {y e} → S y e → After (cursor nothing rs) y → rootOf y ≡ rootOf q → y ∈ ks
      hk = proj₂ (HS.rest m z bq)

      go : ∀ {y e} → Tk y e → After (cursor nothing rs) y → rootOf y ≡ rootOf q → y ∈ ks ++ L.map (_⊕ [ ix 0 ]) ks ++ L.map (_⊕ [ last ]) ks
      go (pass x _ _ , _)   ay rt = ∈-++⁺ˡ (hk x ay rt)
      go (step x _ , _)     ay rt = ∈-++⁺ˡ (hk x ay rt)
      go (tend x _ , _)     ay rt = ∈-++⁺ˡ (hk x ay rt)
      go (left x _ _ , _)   ay rt = ∈-++⁺ˡ (hk x ay rt)
      go (fail {o} x nk _ _ , _) _ rt =
        ∈-++⁺ʳ ks (∈-++⁺ˡ (∈-map⁺ (_⊕ [ ix 0 ]) (hk x (cur-before cu x nk) (trans (sym (rootOf-ext o [ ix 0 ])) rt))))
      go (stop {o} x nk _ , _) _ rt =
        ∈-++⁺ʳ ks (∈-++⁺ʳ (L.map (_⊕ [ ix 0 ]) ks) (∈-map⁺ (_⊕ [ last ]) (hk x (cur-before cu x nk) (trans (sym (rootOf-ext o [ last ])) rt))))

  rest-cut : ∀ {rs} → Cut nothing rs → proj₂ (cnt rs) ≡ 0
           → ∀ {q} → (q , out (instEmit (mark begin) (proj₁ (cnt rs)))) ∈ rs
           → Σ (List Pos) λ ks → ∀ {y e} → Tk y e → After (cursor nothing rs) y → rootOf y ≡ rootOf q → y ∈ ks
  rest-cut (cut {rs₀} {tl} {f} {a} refl run fx nk nF sh (l , ld)) z {q} bq = (f ⊕ [ ix 0 ]) ∷ (f ⊕ [ last ]) ∷ ks , go
    where
      va : Inert a
      va = fails nk

      E : cnt (rs₀ ++ tl) ≡ cnt (rs₀ ++ [ (f , out a) ])
      E = trans (cnt-pre va rs₀ tl (tl-q sh)) (sym (cnt-snoc va rs₀ (inj₂ refl)))

      S-rest : Σ (List Pos) λ ks → ∀ {y e} → S y e → After (cursor nothing (rs₀ ++ [ (f , out a) ])) y → rootOf y ≡ rootOf q → y ∈ ks
      S-rest = HS.rest run (trans (cong proj₂ (sym E)) z)
                 (∈-++⁺ˡ (subst (λ n → (q , out (instEmit (mark begin) (proj₁ n))) ∈ rs₀) E (begin-in va sh bq)))

      ks : List Pos
      ks = proj₁ S-rest

      fy : ∀ {y} → After (cursor nothing (rs₀ ++ tl)) y → f ≺ y
      fy {y} ay = ≺-trans {f} {f ⊕ [ l ]} {y} (≺-ext f []) (subst (λ c → After c y) ld ay)

      fy′ : ∀ {y} → After (cursor nothing (rs₀ ++ tl)) y → After (cursor nothing (rs₀ ++ [ (f , out a) ])) y
      fy′ {y} ay = subst (λ c → After c y) (sym (cursor-snoc nothing rs₀)) (fy ay)

      go : ∀ {y e} → Tk y e → After (cursor nothing (rs₀ ++ tl)) y → rootOf y ≡ rootOf q → y ∈ (f ⊕ [ ix 0 ]) ∷ (f ⊕ [ last ]) ∷ ks
      go (pass _ _ nF′ , _) ay _ = ⊥-elim (nF′ (f , a , fx , nk , fy ay))
      go (step _ nF′ , _)   ay _ = ⊥-elim (nF′ (f , a , fx , nk , fy ay))
      go (tend _ nF′ , _)   ay _ = ⊥-elim (nF′ (f , a , fx , nk , fy ay))
      go (left x _ _ , _)   ay rt = there (there (proj₂ S-rest x (fy′ ay) rt))
      go (fail x′ nk′ nF′ _ , _) _ _ with first-uniq fx nk nF x′ nk′ nF′
      ... | refl = here refl
      go (stop x′ nk′ nF′ , _) _ _ with first-uniq fx nk nF x′ nk′ nF′
      ... | refl = there (here refl)

  rest : Rest Tk
  rest m z bq with back c-none m
  ... | inj₁ (m′ , cu) = rest-clean m′ cu z bq
  ... | inj₂ ct        = rest-cut ct z bq

  holds : Held Tk cs
  holds = record
    { named = named ; covered = covered ; exact = exact ; routing = routing ; shut = shut
    ; early = early ; ends = ends ; done = done ; late = late ; idle = idle ; rest = rest }

held-take-den : ∀ {X : Set} incl (kp : X → Bool) (d : Den (IE X)) {H} cs → HeldD H d cs → InvD H d → HeldD H (Op.takeWhile incl (passes kp) d) cs
held-take-den {X} incl kp d cs h inv p ok ep =
  Holds.holds incl (passes kp) d (p ∷ cs) p (inv p ok) (held-to H) fails (λ m r₁ r₂ eq nk nx → Held.covered H m r₁ r₂ eq (carried nk) nx) fearly
  where
    H = h p ok ep

    fails : ∀ {x : IE X} → T (not (passes kp x)) → Inert x
    fails {instEmit (value _) _} _ = i-value
    fails {instEmit (mark _) _}  ()

    carried : ∀ {x : IE X} → T (not (passes kp x)) → Carried (out x)
    carried {instEmit (value _) _} _ = c-value
    carried {instEmit (mark _) _}  ()

    fearly : ∀ {y} {x : IE X} → enter d p y (out x) → T (not (passes kp x)) → Early y
    fearly {x = instEmit (value _) _} x _ = Held.early H x
    fearly {x = instEmit (mark _) _}  _ ()
