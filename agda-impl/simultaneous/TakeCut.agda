{-# OPTIONS --guardedness #-}

-- ONE CUT'S TAKES CORRESPOND (`corr-take`): a plain takeWhile and the
-- elaborated one, over two runs corresponding along `φ`, correspond
-- along `φ′`, which is `φ` on the plain run's rows and moves the first
-- failing value's two rows under its image.
--
-- A failure is reflected across the map: a plain row has one before it
-- exactly where its image has one (`fail→`, `fail←`), since every
-- elaborated failing value is shown, so imaged.  A skip put late keeps
-- its place unless put on the elaborated failing value, which the
-- elaborated take drops: it is put on what the take puts under it
-- instead (`Put′`).  Where the elaborated row a plain one leads to fails
-- before it, the plain row is the first failure, and leads its instant
-- through the row put under it.
module simultaneous.TakeCut where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_])
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import denotation.Position using (Pos; root; _≟ᵖ_; ix; last; _∙_; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Few; _≺_; _≼_; module TakeWhile)
open import denotation.Laws.Worlds using (⊕-injˡ)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≺-absurd; ≼-refl; ≺→≼; ≼-trans; ≼-or-≻; ≼-split; ≺-≼-≺; ≼-≺-≺; ≺-ext)
open import simultaneous.InstEmit using (valuesOf; instEmit; value; mark)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import denotation.Simultaneity using (between)
open import simultaneous.Attribution using (One; Shown; Live)
open import simultaneous.TableCorr using (M; Corr; ends; m-back; m-val; m-ee)
open import simultaneous.TakeKit using (Run; Lab; lab; lab-cases; snoc-≺; clash; module Take)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; passes)

inst-⊕ : ∀ x ys → instantOf (x ⊕ ys) ≡ instantOf x
inst-⊕ (_ ∙ _) _ = refl

module TakeCut {A : Set} (incl : Bool) (keep : A → Bool) {s s* : Pos} {φ : Pos → Pos} {Put : Pos → Pos → Set}
  {t : EmissionSet A} {u : EmissionSet (IE A)} (C : Corr s s* φ Put t u) (R : Run t) (R* : Run u)
  (fin : ∀ q → Few t q) (fin* : ∀ q → Few u q)
  (dec : ∀ w → Dec (TakeWhile.Failed incl keep t w)) (dec* : ∀ w → Dec (TakeWhile.Failed incl (passes keep) u w))
  (φ′ : Pos → Pos) (φ-old : ∀ {k e} → t k e → φ′ k ≡ φ k)
  (φ-new : ∀ {y a l} → t y (out a) → T (not (keep a)) → Lab l → φ′ (y ⊕ [ l ]) ≡ φ y ⊕ [ l ])
  where

  module C  = Corr C
  module Tp = Take incl keep
  module Te = Take incl (passes keep)
  module W  = TakeWhile incl keep t
  module W* = TakeWhile incl (passes keep) u
  module O  = Tp.One R
  module O* = Te.One R*

  open W using (Failed)

  TT : EmissionSet A
  TT = W.TakeT

  UU : EmissionSet (IE A)
  UU = W*.TakeT

  fst : O.First
  fst = O.first dec fin

  fst* : O*.First
  fst* = O*.first dec* fin*

  ----------------------------------------------------------------------
  -- Values read across

  vals-passes : ∀ {x a} → valuesOf x ≡ a ∷ [] → passes keep x ≡ keep a
  vals-passes {instEmit (value b) _} refl = refl
  vals-passes {instEmit (mark _) _} ()

  nk* : ∀ {x a} → valuesOf x ≡ a ∷ [] → T (not (keep a)) → T (not (passes keep x))
  nk* rd nk = subst (λ b → T (not b)) (sym (vals-passes rd)) nk

  fail-shown : ∀ {x} → T (not (passes keep x)) → Shown (One valuesOf) (out x)
  fail-shown {instEmit (value b) _} _ = b , refl
  fail-shown {instEmit (mark _) _} ()

  -- A plain value's image: a value read the same.
  img-out : ∀ {k a} → t k (out a) → Σ (IE A) λ x → u (φ k) (out x) × valuesOf x ≡ a ∷ []
  img-out x with C.row→ x tt
  ... | inj₁ (e′ , y , m) with proj₁ m tt
  ...   | x′ , refl , rd = x′ , y , rd
  img-out x | inj₂ (() , _)

  -- An elaborated failing value: a plain failing value's image.
  shown-fail : ∀ {l x} → u l (out x) → T (not (passes keep x))
             → Σ Pos λ k → Σ A λ a → l ≡ φ k × t k (out a) × T (not (keep a)) × valuesOf x ≡ a ∷ []
  shown-fail y nk with C.shown← y (fail-shown nk)
  ... | k , e , eq , x , un , m with m-back un m (fail-shown nk)
  ...   | a , refl , rd = k , a , eq , x , subst (λ b → T (not b)) (vals-passes rd) nk , rd

  -- The map is one-to-one on unpinned rows.
  φ-inj : ∀ {k k′ e e′} → t k e → t k′ e′ → Unpinned e → Unpinned e′ → φ k ≡ φ k′ → k ≡ k′
  φ-inj {k} {k′} x x′ un un′ eq with ≼-or-≻ k k′
  ... | inj₂ lt = ⊥-elim (≺-irrefl {φ k′} (subst (φ k′ ≺_) eq (C.mono x′ x un′ un lt)))
  ... | inj₁ le with ≼-split {k} {k′} le
  ...   | inj₁ lt = ⊥-elim (≺-irrefl {φ k′} (subst (_≺ φ k′) eq (C.mono x x′ un un′ lt)))
  ...   | inj₂ e  = e

  ----------------------------------------------------------------------
  -- A failure reflected across the map

  fail→ : ∀ {k e} → t k e → Unpinned e → Failed k → W*.Failed (φ k)
  fail→ x un (q , a , xq , nk , qk) with img-out xq
  ... | x′ , y , rd = φ q , x′ , y , nk* rd nk , C.mono xq x tt un qk

  fail← : ∀ {k e} → t k e → Unpinned e → W*.Failed (φ k) → Failed k
  fail← {k} x un (l , x′ , y , nk , lt) with shown-fail y nk
  ... | k₀ , a , refl , x₀ , nk₀ , _ with ≼-or-≻ k k₀
  ...   | inj₂ k₀k = k₀ , a , x₀ , nk₀ , k₀k
  ...   | inj₁ kk₀ with ≼-split {k} {k₀} kk₀
  ...     | inj₁ lt′ = ⊥-elim (≺-absurd {φ k} {φ k₀} (C.mono x x₀ un tt lt′) lt)
  ...     | inj₂ refl = ⊥-elim (≺-irrefl {φ k} lt)

  -- A kept plain row's image holds no failing value.
  img-nofail : ∀ {k e} → t k e → Unpinned e → O.NoFail k → O*.NoFail (φ k)
  img-nofail x un nf {x′} y with Te.dec-keep x′
  ... | inj₁ p  = p
  ... | inj₂ nk with shown-fail y nk
  ...   | k₀ , a , eq , x₀ , nk₀ , _ with φ-inj x x₀ un tt eq
  ...     | refl = ⊥-elim (clash (nf x₀) nk₀)

  -- A kept plain row lies before every failing value.
  before-fail : ∀ {k e o a} → t k e → ¬ Failed k → O.NoFail k → t o (out a) → T (not (keep a)) → k ≺ o
  before-fail {k} {o = o} {a} x nF nf x₀ nk with ≼-or-≻ k o
  ... | inj₂ ok = ⊥-elim (nF (o , a , x₀ , nk , ok))
  ... | inj₁ ko with ≼-split {k} {o} ko
  ...   | inj₁ lt   = lt
  ...   | inj₂ refl = ⊥-elim (clash (nf x₀) nk)

  -- The elaborated failure no failure precedes is the first plain one's image.
  first-img : ∀ {f x o a} → u f (out x) → T (not (passes keep x)) → ¬ W*.Failed f
            → t o (out a) → T (not (keep a)) → ¬ Failed o → f ≡ φ o
  first-img y nk nF* x nk₀ nF with shown-fail y nk
  ... | k , a , eq , xk , nkk , _ with O.first-uniq xk nkk (λ F → nF* (subst W*.Failed (sym eq) (fail→ xk tt F))) x nk₀ nF
  ...   | refl = eq

  ----------------------------------------------------------------------
  -- Images and placements carried into the takes

  Imaged′ : Pos → Ev A → Set
  Imaged′ k e = Σ (Ev (IE A)) λ e′ → UU (φ′ k) e′ × M e e′

  Homed′ : Pos → Set
  Homed′ k = instantOf k ≡ instantOf s
           ⊎ Σ Pos λ k₀ → Σ (Ev A) λ e₀ → TT k₀ e₀ × Unpinned e₀ × Imaged′ k₀ e₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k

  Leads′ : Pos → Set
  Leads′ k = ∀ {k′ e′} → TT k′ e′ → Unpinned e′ → instantOf k′ ≡ instantOf k → k ≼ k′

  Failing* : Pos → Set
  Failing* y = Σ (IE A) λ x → u y (out x) × T (not (passes keep x))

  -- A late placement: the child's, or under the elaborated failing value
  -- it was put on, from a take's row no failure precedes.
  Put′ : Pos → Pos → Set
  Put′ k l = Σ (Ev A) (TT k) × ¬ Failed k
           × ((Put k l × Σ (Ev (IE A)) (u l)) ⊎ Σ Pos λ y → Put k y × Failing* y × l ≡ y ⊕ [ lab incl ])

  kept-img : ∀ {k e} → t k e → Unpinned e → ¬ Failed k → O.NoFail k → C.Imaged k e → Imaged′ k e
  kept-img {k} x un nF nf (e′ , y , m) =
    e′ , subst (λ z → UU z e′) (sym (φ-old x)) (O*.keep-row y (λ F → nF (fail← x un F)) (img-nofail x un nf)) , m

  made-img : ∀ {o a l e} → t o (out a) → T (not (keep a)) → ¬ Failed o → Tp.Made a l e → Imaged′ (o ⊕ [ l ]) e
  made-img {o} x nk nF (Tp.at0 i) with img-out x
  ... | x′ , y , rd = out x′ , subst (λ z → UU z (out x′)) (sym (φ-new x nk (inj₁ refl))) (W*.fail y (nk* rd nk) (λ F → nF (fail← x tt F)) i) , m-val rd
  made-img {o} x nk nF Tp.atl with img-out x
  ... | x′ , y , rd = end , subst (λ z → UU z end) (sym (φ-new x nk (inj₂ refl))) (W*.stop y (nk* rd nk) (λ F → nF (fail← x tt F))) , m-ee

  homed′ : ∀ {k} → ¬ Failed k → C.Homed k → Homed′ k
  homed′ nF (inj₁ eq) = inj₁ eq
  homed′ {k} nF (inj₂ (k₀ , e₀ , x , un , im , lt , ie)) =
    inj₂ (k₀ , e₀ , O.keep-row x nF₀ nf₀ , un , kept-img x un nF₀ nf₀ im , lt , ie)
    where
      nF₀ : ¬ Failed k₀
      nF₀ F = nF (O.failed-≼ (≺→≼ {k₀} {k} lt) F)

      nf₀ : O.NoFail k₀
      nf₀ = O.nofail< nF lt

  -- Nothing put on a plain skip no failure precedes is past a failure.
  put-unfailed : ∀ {k l} → t k skip → ¬ Failed k → Put k l → ¬ W*.Failed l
  put-unfailed {k} {l} x nF pl (l₀ , x′ , y , nk , lt) with shown-fail y nk
  ... | k₀ , a , refl , x₀ , nk₀ , _ with ≼-or-≻ k k₀
  ...   | inj₂ k₀k = nF (k₀ , a , x₀ , nk₀ , k₀k)
  ...   | inj₁ kk₀ with ≼-split {k} {k₀} kk₀
  ...     | inj₁ lt′ = C.put-before x pl x₀ tt lt′ lt
  ...     | inj₂ refl with Run.func R x x₀
  ...       | ()

  ev-fail? : ∀ (e′ : Ev (IE A)) → (Σ (IE A) λ x → e′ ≡ out x × T (not (passes keep x))) ⊎ (∀ {x} → e′ ≡ out x → T (passes keep x))
  ev-fail? (out x) with Te.dec-keep x
  ... | inj₁ p = inj₂ λ { refl → p }
  ... | inj₂ n = inj₁ (x , refl , n)
  ev-fail? skip    = inj₂ λ ()
  ev-fail? end     = inj₂ λ ()
  ev-fail? (pin _) = inj₂ λ ()

  lab-row : ∀ {y x} → u y (out x) → T (not (passes keep x)) → ¬ W*.Failed y → Σ (Ev (IE A)) (UU (y ⊕ [ lab incl ]))
  lab-row {y} {x} yr nk nF with Te.lab-made x
  ... | e′ , m = e′ , O*.made-row yr nk nF m

  -- Where a plain skip is put late in the take.
  put-at : ∀ {k l e′} → t k skip → ¬ Failed k → Put k l → u l e′ → Σ Pos λ l′ → Σ (Ev (IE A)) λ e″ → UU l′ e″ × Put′ k l′
  put-at {k} {l} {e′} x nF pl y with ev-fail? e′
  ... | inj₁ (x′ , refl , nk) =
    let (e″ , r) = lab-row y nk (put-unfailed x nF pl)
    in l ⊕ [ lab incl ] , e″ , r , (skip , W.step x nF) , nF , inj₂ (l , pl , (x′ , y , nk) , refl)
  ... | inj₂ ok = l , e′ , O*.keep-row y (put-unfailed x nF pl) (λ y′ → ok (Run.func R* y y′)) , (skip , W.step x nF) , nF , inj₁ (pl , e′ , y)

  ----------------------------------------------------------------------
  -- The correspondence

  row→′ : ∀ {k e} → TT k e → Unpinned e → Imaged′ k e ⊎ (e ≡ skip × ((Σ Pos λ l → Σ (Ev (IE A)) λ e′ → UU l e′ × Put′ k l) × Homed′ k))
  row→′ tk un with O.kind tk un
  ... | O.kept x nF nf with C.row→ x un
  ...   | inj₁ im = inj₁ (kept-img x un nF nf im)
  ...   | inj₂ (refl , ((l , e′ , y , pl) , h)) = inj₂ (refl , put-at x nF pl y , homed′ nF h)
  row→′ tk un | O.made x nk nF (l , refl , m) = inj₁ (made-img x nk nF m)

  pin→′ : ∀ {k p} → TT k (pin p) → Live TT k
        → (Σ Pos λ l → Σ Pos λ p′ → UU l (pin p′) × Put′ k l × (∀ {k₀ e₀} → TT k₀ e₀ → Unpinned e₀ → φ′ k₀ ≺ p′ → k₀ ≺ p)) × Homed′ k
  pin→′ {k} {p} tk@(W.left x nFp ins) lv with C.pin→ x (O.live← dec fst lv)
  ... | (l , p′ , y , pl , past) , h = (l , p′ , W*.left y nF* (Run.pin-in R* y) , ((pin p , tk) , nFk , inj₁ (pl , pin p′ , y)) , past′) , homed′ nFk h
    where
      nFk : ¬ Failed k
      nFk = O.live-ok fst x lv

      nF* : ¬ W*.Failed p′
      nF* (l₀ , x′ , y₀ , nk , lt) with shown-fail y₀ nk
      ... | k₀ , a , refl , x₀ , nk₀ , _ = nFp (k₀ , a , x₀ , nk₀ , past x₀ tt lt)

      past′ : ∀ {k₀ e₀} → TT k₀ e₀ → Unpinned e₀ → φ′ k₀ ≺ p′ → k₀ ≺ p
      past′ tk₀ un lt with O.kind tk₀ un
      ... | O.kept x₀ _ _ = past x₀ un (subst (_≺ p′) (φ-old x₀) lt)
      ... | O.made {o} {a} x₀ nk₀ _ (l₀ , refl , m) =
        ⊥-elim (nFp (o , a , x₀ , nk₀ , past x₀ tt (≺-trans {φ o} {φ o ⊕ [ l₀ ]} {p′} (≺-ext (φ o) []) (subst (_≺ p′) (φ-new x₀ nk₀ (Tp.made-lab m)) lt))))

  put-before′ : ∀ {k l k′ e′} → TT k skip → Put′ k l → TT k′ e′ → Unpinned e′ → k ≺ k′ → l ≼ φ′ k′
  put-before′ tk (_ , nFk , br) tk′ un′ lt with O.kind tk tt
  ... | O.made _ _ _ (_ , _ , ())
  ... | O.kept x _ _ with O.kind tk′ un′
  put-before′ {k} {l} {k′} tk (_ , nFk , inj₁ (pl , _)) tk′ un′ lt | O.kept x _ _ | O.kept x′ _ _ =
    subst (l ≼_) (sym (φ-old x′)) (C.put-before x pl x′ un′ lt)
  put-before′ {k} {l} {k′} tk (_ , nFk , inj₂ (y , pl , (x* , yr , nk*) , refl)) tk′ un′ lt | O.kept x _ _ | O.kept x′ nF′ nf′ with shown-fail yr nk*
  ... | kf , a , refl , xf , nkf , _ =
    ⊥-elim (C.put-before x pl x′ un′ lt (C.mono x′ xf un′ tt (before-fail x′ nF′ nf′ xf nkf)))
  put-before′ {k} {l} tk (_ , nFk , br) tk′ un′ lt | O.kept x nF nf | O.made {o} {a} x₀ nk₀ nF₀ (l₀ , refl , m) =
    subst (l ≼_) (sym (φ-new x₀ nk₀ (Tp.made-lab m))) (go br)
    where
      ko : k ≺ o
      ko = before-fail x nFk nf x₀ nk₀

      go : (Put k l × Σ (Ev (IE A)) (u l)) ⊎ (Σ Pos λ y → Put k y × Failing* y × l ≡ y ⊕ [ lab incl ]) → l ≼ (φ o ⊕ [ l₀ ])
      go (inj₁ (pl , _)) = ≼-trans {l} {φ o} {φ o ⊕ [ l₀ ]} (C.put-before x pl x₀ tt ko) (≺→≼ {φ o} {φ o ⊕ [ l₀ ]} (≺-ext (φ o) []))
      go (inj₂ (y , pl , (x* , yr , nk*) , refl)) with shown-fail yr nk*
      ... | kf , a′ , refl , xf , nkf , _ with ≼-or-≻ kf o
      ...   | inj₂ okf = ⊥-elim (C.put-before x pl x₀ tt ko (C.mono x₀ xf tt tt okf))
      ...   | inj₁ kfo with ≼-split {kf} {o} kfo
      ...     | inj₁ lt′ = ⊥-elim (nF₀ (kf , a′ , xf , nkf , lt′))
      ...     | inj₂ refl = Tp.lab-≼ {φ kf} m

  shown←′ : ∀ {l e′} → UU l e′ → Shown (One valuesOf) e′ → Σ Pos λ k → Σ (Ev A) λ e → l ≡ φ′ k × TT k e × Unpinned e × M e e′
  shown←′ {l} {e′} ul sh with O*.kind ul (shown-un e′ sh)
    where
      shown-un : ∀ (e′ : Ev (IE A)) → Shown (One valuesOf) e′ → Unpinned e′
      shown-un (out _) _ = tt
      shown-un end     _ = tt
  ... | O*.kept y nF* nf* with C.shown← y sh
  ...   | k , e , eq , x , un , m =
    k , e , trans eq (sym (φ-old x)) , O.keep-row x nF nf , un , m
    where
      nF : ¬ Failed k
      nF F = nF* (subst W*.Failed (sym eq) (fail→ x un F))

      nf : O.NoFail k
      nf {a} x′ with Tp.dec-keep a
      ... | inj₁ p = p
      ... | inj₂ nk with img-out x′
      ...   | x″ , y′ , rd = ⊥-elim (clash (nf* (subst (λ z → u z (out x″)) (sym eq) y′)) (nk* rd nk))
  shown←′ ul sh | O*.made {o} y nk nF* (l₀ , refl , m*) with shown-fail y nk
  ... | kf , a , refl , xf , nkf , rd = move m*
    where
      nF : ¬ Failed kf
      nF F = nF* (fail→ xf tt F)

      at : ∀ {l} → Lab l → φ kf ⊕ [ l ] ≡ φ′ (kf ⊕ [ l ])
      at lb = sym (φ-new xf nkf lb)

      move : ∀ {e′} → Te.Made _ l₀ e′ → Σ Pos λ k → Σ (Ev A) λ e → (φ kf ⊕ [ l₀ ]) ≡ φ′ k × TT k e × Unpinned e × M e e′
      move (Te.at0 i) = kf ⊕ [ ix 0 ] , out a , at (inj₁ refl) , W.fail xf nkf nF i , tt , m-val rd
      move Te.atl     = kf ⊕ [ last ] , end , at (inj₂ refl) , W.stop xf nkf nF , tt , m-ee

  place′ : ∀ {m e′} → UU m e′ → Live UU m
         → instantOf m ≡ instantOf s* ⊎ Σ Pos λ k → Σ (Ev A) λ e → TT k e × Unpinned e × Imaged′ k e × (φ′ k ≼ m ⊎ Leads′ k) × instantOf (φ′ k) ≡ instantOf m
  place′ {m} um lv with O*.from um
  place′ {m} um lv | O*.new {o} {x} y nk nF* (l , refl , m*) with shown-fail y nk
  ... | kf , a , refl , xf , nkf , rd = inj₂ (move m*)
    where
      nF : ¬ Failed kf
      nF F = nF* (fail→ xf tt F)

      move : ∀ {e′} → Te.Made x l e′ → Σ Pos λ k → Σ (Ev A) λ e → TT k e × Unpinned e × Imaged′ k e × (φ′ k ≼ (φ kf ⊕ [ l ]) ⊎ Leads′ k) × instantOf (φ′ k) ≡ instantOf (φ kf ⊕ [ l ])
      move (Te.at0 i) =
        let eq = φ-new xf nkf (inj₁ refl)
        in kf ⊕ [ ix 0 ] , out a , W.fail xf nkf nF i , tt , made-img xf nkf nF (Tp.at0 i)
         , inj₁ (subst (_≼ (φ kf ⊕ [ ix 0 ])) (sym eq) (≼-refl {φ kf ⊕ [ ix 0 ]})) , cong instantOf eq
      move Te.atl =
        let eq = φ-new xf nkf (inj₂ refl)
        in kf ⊕ [ last ] , end , W.stop xf nkf nF , tt , made-img xf nkf nF Tp.atl
         , inj₁ (subst (_≼ (φ kf ⊕ [ last ])) (sym eq) (≼-refl {φ kf ⊕ [ last ]})) , cong instantOf eq
  place′ {m} um lv | O*.self y _ with C.place y (O*.live← dec* fst* lv)
  ... | inj₁ eq = inj₁ eq
  ... | inj₂ (k , e , x , un , im , at , ie) = inj₂ (go at)
    where
      nFm : ¬ W*.Failed m
      nFm = O*.live-ok fst* y lv

      nfm : O*.NoFail m
      nfm = O*.nofail um nFm

      Out : Set
      Out = Σ Pos λ k → Σ (Ev A) λ e → TT k e × Unpinned e × Imaged′ k e × (φ′ k ≼ m ⊎ Leads′ k) × instantOf (φ′ k) ≡ instantOf m

      ie′ : instantOf (φ′ k) ≡ instantOf m
      ie′ = trans (cong instantOf (φ-old x)) ie

      -- A row put after `k`'s image fails nowhere before it.
      unfailed-at : φ k ≼ m → ¬ Failed k
      unfailed-at km F = nFm (O*.failed-≼ km (fail→ x un F))

      nofail-at : φ k ≼ m → O.NoFail k
      nofail-at km {a} x′ with Tp.dec-keep a
      ... | inj₁ p = p
      ... | inj₂ nk with img-out x′ | ≼-split {φ k} {m} km
      ...   | x″ , y′ , rd | inj₁ lt   = ⊥-elim (nFm (φ k , x″ , y′ , nk* rd nk , lt))
      ...   | x″ , y′ , rd | inj₂ refl = ⊥-elim (clash (nfm y′) (nk* rd nk))

      leads′ : C.Leads k → Leads′ k
      leads′ ld tk′ un′ ie″ with O.kind tk′ un′
      ... | O.kept x′ _ _ = ld x′ un′ ie″
      ... | O.made {o} x₀ _ _ (l₀ , refl , _) =
        ≼-trans {k} {o} {o ⊕ [ l₀ ]} (ld x₀ tt (trans (sym (inst-⊕ o [ l₀ ])) ie″)) (≺→≼ {o} {o ⊕ [ l₀ ]} (≺-ext o []))

      -- `k` leads its instant and fails or is failed: it is the first
      -- failure, which leads through the row put under it.
      first-at : C.Leads k → (Σ A λ a → t k (out a) × T (not (keep a)) × ¬ Failed k) → Out
      first-at ld (a , xk , nk , nFk) with Tp.lab-made a
      ... | e₁ , mm =
        k ⊕ [ lab incl ] , e₁ , O.made-row xk nk nFk mm , Tp.made-un mm , made-img xk nk nFk mm , inj₂ leads
        , trans (cong instantOf (φ-new xk nk (Tp.made-lab mm))) (trans (inst-⊕ (φ k) [ lab incl ]) ie)
        where
          leads : Leads′ (k ⊕ [ lab incl ])
          leads tk′ un′ ie″ with O.kind tk′ un′
          ... | O.kept x′ nF′ nf′ = ⊥-elim (nF′ (k , a , xk , nk , before-k))
            where
              before-k : k ≺ _
              before-k with ≼-split {k} (ld x′ un′ (trans ie″ (inst-⊕ k [ lab incl ])))
              ... | inj₁ lt = lt
              ... | inj₂ refl = ⊥-elim (clash (nf′ xk) nk)
          ... | O.made x₀ nk₀ nF₀ (l₀ , refl , m₀) with O.first-uniq xk nk nFk x₀ nk₀ nF₀
          ...   | refl = Tp.lab-≼ {k} m₀

      -- Otherwise the first failure lies before `k`, in an earlier
      -- instant than `m`'s, which lies before its image.
      fails : C.Leads k → ∀ {f b} → t f (out b) → T (not (keep b)) → ¬ Failed f → f ≼ k → f ≡ k
      fails ld {f} xf nkf nFf fk with ≼-split {f} {k} fk
      ... | inj₂ e = e
      ... | inj₁ fk′ with img-out xf
      ...   | x′ , y′ , rd with ≼-or-≻ m (φ f)
      ...     | inj₂ fm = ⊥-elim (nFm (φ f , x′ , y′ , nk* rd nkf , fm))
      ...     | inj₁ mf with ≼-split {m} {φ f} mf
      ...       | inj₂ refl = ⊥-elim (clash (nfm y′) (nk* rd nkf))
      ...       | inj₁ mf′ =
        let fkk = C.mono xf x tt un fk′
            if = between {m} {φ f} {φ k} (Equivalence.to T-≡ mf′) (Equivalence.to T-≡ fkk) (sym ie)
        in ⊥-elim (≺-irrefl {k} (≼-≺-≺ {k} {f} {k} (ld xf tt (Equivalence.to (C.inst xf x tt un) (trans if (sym ie)))) fk′))

      out-inj : ∀ {a b : A} → out a ≡ out b → a ≡ b
      out-inj refl = refl

      -- `k`'s row is a failing value, or no value at `k` fails.
      split : ∀ {e₀} → t k e₀ → Unpinned e₀ → O.NoFail k ⊎ (Σ A λ a → t k (out a) × T (not (keep a)))
      split {out a} xk _ with Tp.dec-keep a
      ... | inj₂ nk = inj₂ (a , xk , nk)
      ... | inj₁ kp = inj₁ (λ x′ → subst (λ z → T (keep z)) (out-inj (Run.func R xk x′)) kp)
      split {skip} xk _ = inj₁ λ x′ → skip≢ (Run.func R xk x′)
        where skip≢ : ∀ {a} → skip ≡ out a → _
              skip≢ ()
      split {end} xk _ = inj₁ λ x′ → end≢ (Run.func R xk x′)
        where end≢ : ∀ {a} → end ≡ out a → _
              end≢ ()

      go : φ k ≼ m ⊎ C.Leads k → Out
      go (inj₁ km) =
        k , e , O.keep-row x (unfailed-at km) (nofail-at km) , un , kept-img x un (unfailed-at km) (nofail-at km) im
        , inj₁ (subst (_≼ m) (sym (φ-old x)) km) , ie′
      go (inj₂ ld) with dec k
      ... | yes (q , a , xq , nk , qk) with fst xq nk
      ...   | f , b , xf , nkf , nFf , fq with fails ld xf nkf nFf (≺→≼ {f} {k} (≼-≺-≺ {f} {q} {k} fq qk))
      ...     | refl = ⊥-elim (nFf (q , a , xq , nk , ≼-≺-≺ {q} {q} {f} (≼-refl {q}) qk))
      go (inj₂ ld) | no nFk with split x un
      ... | inj₂ (a , xk , nk) = first-at ld (a , xk , nk , nFk)
      ... | inj₁ nf = k , e , O.keep-row x nFk nf , un , kept-img x un nFk nf im , inj₂ (leads′ ld) , ie′

  mono′ : ∀ {k k′ e e′} → TT k e → TT k′ e′ → Unpinned e → Unpinned e′ → k ≺ k′ → φ′ k ≺ φ′ k′
  mono′ {k} {k′} tk tk′ un un′ lt with O.kind tk un | O.kind tk′ un′
  ... | O.kept x _ _ | O.kept x′ _ _ = subst₂ _≺_ (sym (φ-old x)) (sym (φ-old x′)) (C.mono x x′ un un′ lt)
  ... | O.kept x nF nf | O.made {o} x₀ nk₀ _ (l₀ , refl , m₀) =
    subst (φ′ k ≺_) (sym (φ-new x₀ nk₀ (Tp.made-lab m₀))) (subst (_≺ (φ o ⊕ [ l₀ ])) (sym (φ-old x))
      (≺-trans {φ k} {φ o} {φ o ⊕ [ l₀ ]} (C.mono x x₀ un tt (before-fail x nF nf x₀ nk₀)) (≺-ext (φ o) [])))
  ... | O.made {o} x₀ nk₀ _ (l₀ , refl , _) | O.kept x′ nF′ nf′ =
    ⊥-elim (≺-irrefl {o} (≺-trans {o} {o ⊕ [ l₀ ]} {o} (≺-ext o []) (≺-trans {o ⊕ [ l₀ ]} {k′} {o} lt (before-fail x′ nF′ nf′ x₀ nk₀))))
  ... | O.made {o} x₀ nk₀ nF₀ (l₀ , refl , m₀) | O.made {o′} x₁ nk₁ nF₁ (l₁ , refl , m₁) with O.first-uniq x₀ nk₀ nF₀ x₁ nk₁ nF₁
  ...   | refl = subst₂ _≺_ (sym (φ-new x₀ nk₀ (Tp.made-lab m₀))) (sym (φ-new x₁ nk₁ (Tp.made-lab m₁)))
                   (snoc-≺ {o} {φ o} (Tp.made-lab m₀) (Tp.made-lab m₁) lt)

  -- A take's row stands for a plain row of its instant and its image's.
  Rep : Pos → Set
  Rep k = Σ Pos λ r → Σ (Ev A) λ e₀ → t r e₀ × Unpinned e₀ × instantOf k ≡ instantOf r × instantOf (φ′ k) ≡ instantOf (φ r)

  rep : ∀ {k e} → TT k e → Unpinned e → Rep k
  rep {k} {e} tk un with O.kind tk un
  ... | O.kept x _ _ = k , e , x , un , refl , cong instantOf (φ-old x)
  ... | O.made {o} {a} x₀ nk₀ _ (l₀ , refl , m₀) =
    o , out a , x₀ , tt , inst-⊕ o [ l₀ ] , trans (cong instantOf (φ-new x₀ nk₀ (Tp.made-lab m₀))) (inst-⊕ (φ o) [ l₀ ])

  inst′ : ∀ {k k′ e e′} → TT k e → TT k′ e′ → Unpinned e → Unpinned e′
        → (instantOf (φ′ k) ≡ instantOf (φ′ k′) ⇔ instantOf k ≡ instantOf k′)
  inst′ tk tk′ un un′ with rep tk un | rep tk′ un′
  ... | _ , _ , x , u , ik , iφ | _ , _ , x′ , u′ , ik′ , iφ′ =
    mk⇔ (λ h → trans ik (trans (Equivalence.to (C.inst x x′ u u′) (trans (sym iφ) (trans h iφ′))) (sym ik′)))
        (λ h → trans iφ (trans (Equivalence.from (C.inst x x′ u u′) (trans (sym ik) (trans h ik′))) (sym iφ′)))

  home′ : ∀ {k e} → TT k e → Unpinned e → (instantOf (φ′ k) ≡ instantOf s* ⇔ instantOf k ≡ instantOf s)
  home′ tk un with rep tk un
  ... | _ , _ , x , u , ik , iφ =
    mk⇔ (λ h → trans ik (Equivalence.to (C.home x u) (trans (sym iφ) h)))
        (λ h → trans iφ (Equivalence.from (C.home x u) (trans (sym ik) h)))

  corr-take : Corr s s* φ′ Put′ TT UU
  corr-take = record
    { row→ = row→′ ; pin→ = pin→′ ; put-before = put-before′ ; shown← = shown←′
    ; place = place′ ; mono = mono′ ; inst = inst′ ; home = home′ }

  ----------------------------------------------------------------------
  -- Rows the lifting reads

  -- A kept row's image row is the elaborated run's own.
  kept-self : ∀ {k e e′} → t k e → Unpinned e → ¬ Failed k → O.NoFail k → UU (φ k) e′ → u (φ k) e′
  kept-self {k} x un nF nf uu with O*.from uu
  ... | O*.self y _ = y
  ... | O*.new y nk _ (l , eq , _) with shown-fail y nk
  ...   | kf , _ , refl , xf , nkf , _ =
    ⊥-elim (≺-irrefl {φ k} (≺-trans {φ k} {φ kf} {φ k} (C.mono x xf un tt (before-fail x nF nf xf nkf)) (subst (φ kf ≺_) (sym eq) (≺-ext (φ kf) []))))

  -- A row under an elaborated value is made from it, no failure before it.
  under-unfailed : ∀ {y x l e′} → u y (out x) → UU (y ⊕ [ l ]) e′ → ¬ W*.Failed y
  under-unfailed {y} {l = l} yr uu with O*.from uu
  ... | O*.self y′ _ = ⊥-elim (Run.flat R* yr y′)
  ... | O*.new {o} _ _ nF* (_ , eq , _) = subst (λ z → ¬ W*.Failed z) (sym (⊕-injˡ y o eq)) nF*

  -- An elaborated row past no failure is the elaborated run's own.
  unfailed-self : ∀ {m e} → UU m e → ¬ W*.Failed m → u m e
  unfailed-self um nF with O*.from um
  ... | O*.self y _ = y
  ... | O*.new {o} y nk _ (l , refl , _) = ⊥-elim (nF (o , _ , y , nk , ≺-ext o []))
