{-# OPTIONS --guardedness #-}

-- A TAKEWHILE OVER RUN-SHAPED TABLES, READ BACK TO ITS SOURCE.  Every
-- row of a take is its source's own, no failing value, or one of the
-- first failing value's two under it (`From`).  So a take's tables are
-- run-shaped as its source's are (`func-T`, `flat-T`, `pin-in-T`).
--
-- Agreement of two sources carries to their takes (`push`), past a
-- failing value both hold up to its completion (`push-fail`).  Back:
-- two takes agreeing up to a row the first holds, with no failure before
-- it, have sources agreeing up to it (`lift`), and up to the failure for
-- one of its rows (`lift-fail`).  The other source cannot fail there
-- unseen: the first holds a row at or past it, so a value the other
-- holds the first holds too (`Cons`).  And two takes are truncated
-- before they differ as their sources are (`cons-T`).
module simultaneous.TakeKit where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
open import Data.List.Properties using (∷-injectiveʳ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (Equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import denotation.Position using (Pos; Path; Label; ix; last; inside; _⊕_)
open import denotation.Events using (<ᵖ-apart)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Few; _≺_; _≼_; module TakeWhile)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; AgreeTo-sym; ag-down; few-ind; ≺-trans; ≺-irrefl; ≼-refl; ≺→≼; ≼-trans; ≼-or-≻; ≼-split; ≺-≼-≺; ≼-≺-≺; ≺-ext)
open import denotation.Laws.Worlds using (⊑-≼; ⊑-snoc; inside-⊑; ⊕-injˡ; ⊕-injʳ; ⊕-assoc; ⊕-identityʳ; ⊕-cancelˡ; ext≢)
open import simultaneous.Attribution using (Live)
open import simultaneous.TableCorr using (Cons; ag-ind)

-- One event per position, none under another's, a pin inside its connect.
record Run {A : Set} (t : EmissionSet A) : Set where
  field
    func   : ∀ {y e e′} → t y e → t y e′ → e ≡ e′
    flat   : ∀ {y e l ys e′} → t y e → t (y ⊕ (l ∷ ys)) e′ → ⊥
    pin-in : ∀ {l r} → t l (pin r) → T (inside r l)

ix≢last : ∀ {n} → ix n ≡ last → ⊥
ix≢last ()

[]≢∷ : ∀ {X : Set} {x : X} {xs} → [] ≡ x ∷ xs → ⊥
[]≢∷ ()

clash : ∀ {b} → T b → T (not b) → ⊥
clash {true}  _ ()
clash {false} ()

-- Past a row and not under it: past everything under it.
apart : ∀ {A} {t : EmissionSet A} → Run t → ∀ {y c e e′} (ws : Path) → t y e → t c e′ → y ≺ c → (y ⊕ ws) ≺ c
apart {t = t} R {y} {c} {e′ = e′} ws x x′ lt = Equivalence.from T-≡ (<ᵖ-apart y c ws (Equivalence.to T-≡ lt) ne)
  where
    ne : ∀ ys → c ≡ y ⊕ ys → ⊥
    ne []       eq = ≺-irrefl {y} (subst (y ≺_) (trans eq (⊕-identityʳ y)) lt)
    ne (l ∷ ys) eq = Run.flat R x (subst (λ z → t z e′) eq x′)

-- A position at or under another.
sub-or : ∀ {y o} (zs : Path) → o ≡ y ⊕ zs → o ≡ y ⊎ Σ Label λ l → Σ Path λ ys → o ≡ y ⊕ (l ∷ ys)
sub-or {y} []       eq = inj₁ (trans eq (⊕-identityʳ y))
sub-or     (l ∷ ys) eq = inj₂ (l , ys , eq)

module Take {A : Set} (incl : Bool) (keep : A → Bool) where

  dec-keep : ∀ a → T (keep a) ⊎ T (not (keep a))
  dec-keep a with keep a
  ... | true  = inj₁ _
  ... | false = inj₂ _

  -- Where a take's row comes from, the first failure's two at the side.
  New : Pos → Ev A → Pos → A → Set
  New w e o a = (w ≡ o ⊕ [ ix 0 ] × e ≡ out a × T incl) ⊎ (w ≡ o ⊕ [ last ] × e ≡ end)

  at-new : ∀ {w e o a} → New w e o a → Σ Label λ l → w ≡ o ⊕ [ l ]
  at-new (inj₁ (eq , _)) = ix 0 , eq
  at-new (inj₂ (eq , _)) = last , eq

  ----------------------------------------------------------------------
  -- One take

  module One {t : EmissionSet A} (R : Run t) where
    open TakeWhile incl keep t
    open Run R

    NoFail : Pos → Set
    NoFail y = ∀ {a} → t y (out a) → T (keep a)

    data From (w : Pos) (e : Ev A) : Set where
      self : t w e → (∀ {a} → e ≡ out a → T (keep a)) → From w e
      new  : ∀ {o a} → t o (out a) → T (not (keep a)) → ¬ Failed o → New w e o a → From w e

    from : ∀ {w e} → TakeT w e → From w e
    from (pass x k _)     = self x (λ { refl → k })
    from (fail x nk nF i) = new x nk nF (inj₁ (refl , refl , i))
    from (stop x nk nF)   = new x nk nF (inj₂ (refl , refl))
    from (step x _)       = self x (λ ())
    from (tend x _)       = self x (λ ())
    from (left x _ _)     = self x (λ ())

    -- A row at or past `y`, or a failure before it.
    past : ∀ {w e y} → From w e → y ≼ w → (Σ Pos λ o → Σ (Ev A) λ e₀ → t o e₀ × y ≼ o) ⊎ Failed y
    past {e = e} (self x _) yw = inj₁ (_ , e , x , yw)
    past {y = y} (new {o} {a} x nk _ _) yw with ≼-or-≻ y o
    ... | inj₁ yo = inj₁ (o , out a , x , yo)
    ... | inj₂ oy = inj₂ (o , a , x , nk , oy)

    failed-≼ : ∀ {y z} → y ≼ z → Failed y → Failed z
    failed-≼ {y} {z} yz (q , a , x , nk , qy) = q , a , x , nk , ≺-≼-≺ {q} {y} {z} qy yz

    -- No failure before a take's row: it holds no failing value.
    nofail : ∀ {w e} → TakeT w e → ¬ Failed w → NoFail w
    nofail tk nF x′ with from tk
    ... | self x ok = ok (func x x′)
    ... | new {o} {a} x nk _ loc with at-new loc
    ...   | _ , eq = ⊥-elim (nF (o , a , x , nk , subst (o ≺_) (sym eq) (≺-ext o [])))

    -- Kept: a source row no failure precedes, no failing value.
    keep-row : ∀ {y e} → t y e → ¬ Failed y → NoFail y → TakeT y e
    keep-row {e = out a} x nF nf = pass x (nf x) nF
    keep-row {e = skip}  x nF _  = step x nF
    keep-row {e = end}   x nF _  = tend x nF
    keep-row {y} {e = pin r} x nF _ = left x (λ F → nF (failed-≼ {r} {y} (⊑-≼ (inside-⊑ r y (pin-in x))) F)) (pin-in x)

    -- THE FIRST FAILING VALUE, where failing is decidable and rows few.
    First : Set
    First = ∀ {q a} → t q (out a) → T (not (keep a))
          → Σ Pos λ f → Σ A λ b → t f (out b) × T (not (keep b)) × ¬ Failed f × f ≼ q

    first : (∀ w → Dec (Failed w)) → (∀ w → Few t w) → First
    first dec fin {q} x nk = few-ind {t = t} P go (fin q) x nk
      where
        P : Pos → Set
        P w = ∀ {a} → t w (out a) → T (not (keep a)) → Σ Pos λ f → Σ A λ b → t f (out b) × T (not (keep b)) × ¬ Failed f × f ≼ w

        go : ∀ {w} → Few t w → (∀ {v e} → t v e → v ≺ w → P v) → P w
        go {w} _ ih {a} x nk with dec w
        ... | no nF = w , a , x , nk , nF , ≼-refl {w}
        ... | yes (q , b , xq , nkq , qw) with ih xq qw xq nkq
        ...   | f , c , xf , nkf , nFf , fq = f , c , xf , nkf , nFf , ≼-trans {f} {q} {w} fq (≺→≼ {q} {w} qw)

    -- Live in the take: before every end of the source.
    live← : (∀ w → Dec (Failed w)) → First → ∀ {k} → Live TakeT k → Live t k
    live← dec fst {k} lv {c} x with dec c
    ... | no nF = lv (tend x nF)
    ... | yes (q , a , xq , nk , qc) with fst xq nk
    ...   | f , b , xf , nkf , nFf , fq =
      ≺→≼ {k} {c} (≼-≺-≺ {k} {f ⊕ [ last ]} {c} (lv (stop xf nkf nFf)) (apart R [ last ] xf x (≼-≺-≺ {f} {q} {c} fq qc)))

    -- A source row live in the take has no failure before it.
    live-ok : First → ∀ {k e} → t k e → Live TakeT k → ¬ Failed k
    live-ok fst {k} x lv (q , a , xq , nk , qk) with fst xq nk
    ... | f , b , xf , nkf , nFf , fq = lv (stop xf nkf nFf) (apart R [ last ] xf x (≼-≺-≺ {f} {q} {k} fq qk))

    -- A TAKE IS RUN-SHAPED.
    private
      self-new : ∀ {y e e₀ o a} → t y e → t o (out a) → New y e₀ o a → ⊥
      self-new {e = e} {e₀} {a = a} x x₀ loc with at-new {e = e₀} {a = a} loc
      ... | _ , eq = flat x₀ (subst (λ z → t z e) eq x)

      new-new : ∀ {y e e′ o o′ a a′} → t o (out a) → t o′ (out a′) → New y e o a → New y e′ o′ a′ → e ≡ e′
      new-new {o = o} {o′} x x′ (inj₁ (eq , refl , _)) (inj₁ (eq′ , refl , _)) with ⊕-injˡ o o′ (trans (sym eq) eq′)
      ... | refl = func x x′
      new-new {o = o} {o′} x x′ (inj₁ (eq , _)) (inj₂ (eq′ , _)) = ⊥-elim (ix≢last (⊕-injʳ o o′ (trans (sym eq) eq′)))
      new-new {o = o} {o′} x x′ (inj₂ (eq , _)) (inj₁ (eq′ , _)) = ⊥-elim (ix≢last (sym (⊕-injʳ o o′ (trans (sym eq) eq′))))
      new-new x x′ (inj₂ (_ , refl)) (inj₂ (_ , refl)) = refl

    func-T : ∀ {y e e′} → TakeT y e → TakeT y e′ → e ≡ e′
    func-T tk tk′ with from tk | from tk′
    ... | self x _ | self x′ _ = func x x′
    ... | self x _ | new x₀ _ _ loc = ⊥-elim (self-new x x₀ loc)
    ... | new x₀ _ _ loc | self x _ = ⊥-elim (self-new x x₀ loc)
    ... | new x _ _ l₁ | new x′ _ _ l₂ = new-new x x′ l₁ l₂

    flat-T : ∀ {y e l ys e′} → TakeT y e → TakeT (y ⊕ (l ∷ ys)) e′ → ⊥
    flat-T {y} {e} {l} {ys} {e′} tk tk′ with from tk | from tk′
    ... | self x _ | self x′ _ = flat x x′
    ... | self x ok | new {o} {a} x₀ nk _ loc with at-new {e = e′} {a = a} loc
    ...   | l′ , eq with ⊑-snoc o {l′} (l ∷ ys , sym eq)
    ...     | inj₂ eq₂ = ext≢ y ys (trans eq (sym eq₂))
    ...     | inj₁ (zs , eq₁) with sub-or zs eq₁
    ...       | inj₁ eo = clash (ok (func x (subst (λ z → t z (out a)) eo x₀))) nk
    ...       | inj₂ (_ , _ , eo) = flat x (subst (λ z → t z (out a)) eo x₀)
    flat-T {y} {e} {l} {ys} {e′} tk tk′ | new {o} {a} x₀ _ _ loc | self x′ _ with at-new {e = e} {a = a} loc
    ... | l₀ , eq = flat x₀ (subst (λ z → t z e′) (trans (cong (_⊕ (l ∷ ys)) eq) (⊕-assoc o [ l₀ ] (l ∷ ys))) x′)
    flat-T {y} {e} {l} {ys} {e′} tk tk′ | new {o} {a} x₀ _ _ loc | new {o′} {a′} x₀′ _ _ loc′ with at-new {e = e} {a = a} loc | at-new {e = e′} {a = a′} loc′
    ... | l₀ , eq | l₁ , eq′ with ⊑-snoc o′ {l₁} (l₀ ∷ l ∷ ys , trans (sym eq′) (trans (cong (_⊕ (l ∷ ys)) eq) (⊕-assoc o [ l₀ ] (l ∷ ys))))
    ...   | inj₂ eo = flat x₀′ (subst (λ z → t z (out a)) eo x₀)
    ...   | inj₁ (zs , eo′) with sub-or zs eo′
    ...     | inj₂ (_ , _ , eo) = flat x₀ (subst (λ z → t z (out a′)) eo x₀′)
    ...     | inj₁ eo = []≢∷ (∷-injectiveʳ (⊕-cancelˡ o [ l₁ ] (l₀ ∷ l ∷ ys)
                (trans (cong (_⊕ [ l₁ ]) (sym eo)) (trans (sym eq′) (trans (cong (_⊕ (l ∷ ys)) eq) (⊕-assoc o [ l₀ ] (l ∷ ys)))))))

    pin-in-T : ∀ {l r} → TakeT l (pin r) → T (inside r l)
    pin-in-T (left _ _ ins) = ins

    run-T : Run TakeT
    run-T = record { func = func-T ; flat = flat-T ; pin-in = pin-in-T }

  ----------------------------------------------------------------------
  -- Two takes, one way

  module Dir {t t′ : EmissionSet A} (R : Run t) (R′ : Run t′) where
    module W  = TakeWhile incl keep t
    module W′ = TakeWhile incl keep t′
    module O  = One R
    module O′ = One R′

    refail< : ∀ {z} → (∀ {y₀} → y₀ ≺ z → AgreeTo y₀ t t′) → W′.Failed z → W.Failed z
    refail< below (q , a , x′ , nk , qz) = q , a , proj₂ (upto (below {q} qz) {q} {out a} (≼-refl {q})) x′ , nk , qz

    unfail : ∀ {k z} → AgreeTo k t t′ → z ≼ k → ¬ W.Failed z → ¬ W′.Failed z
    unfail {k} {z} ag zk nF (q , a , x′ , nk , qz) = nF (q , a , proj₂ (upto ag {q} {out a} (≺→≼ {q} {k} (≺-≼-≺ {q} {z} {k} qz zk))) x′ , nk , qz)

    -- AGREEMENT CARRIES FORWARD.
    push1 : ∀ {k y e} → AgreeTo k t t′ → y ≼ k → W.TakeT y e → W′.TakeT y e
    push1 ag yk (W.pass x kp nF) = W′.pass (proj₁ (upto ag yk) x) kp (unfail ag yk nF)
    push1 {k} ag yk (W.fail {q} x nk nF i) =
      let qk = ≼-trans {q} {q ⊕ [ ix 0 ]} {k} (≺→≼ {q} {q ⊕ [ ix 0 ]} (≺-ext q [])) yk
      in W′.fail (proj₁ (upto ag qk) x) nk (unfail ag qk nF) i
    push1 {k} ag yk (W.stop {q} x nk nF) =
      let qk = ≼-trans {q} {q ⊕ [ last ]} {k} (≺→≼ {q} {q ⊕ [ last ]} (≺-ext q [])) yk
      in W′.stop (proj₁ (upto ag qk) x) nk (unfail ag qk nF)
    push1 ag yk (W.step x nF) = W′.step (proj₁ (upto ag yk) x) (unfail ag yk nF)
    push1 ag yk (W.tend x nF) = W′.tend (proj₁ (upto ag yk) x) (unfail ag yk nF)
    push1 {k} ag yk (W.left {q} {r} x nF ins) =
      W′.left (proj₁ (upto ag yk) x) (unfail ag (≼-trans {r} {q} {k} (⊑-≼ (inside-⊑ r q ins)) yk) nF) ins

    -- Past a failing value both hold, to its completion.
    push-fail1 : ∀ {y a z e} → AgreeTo y t t′ → t y (out a) → T (not (keep a)) → ¬ W.Failed y
               → z ≼ (y ⊕ [ last ]) → W.TakeT z e → W′.TakeT z e
    push-fail1 {y} {z = z} ag x nk nF zl tk with ≼-or-≻ z y
    ... | inj₁ zy = push1 ag zy tk
    ... | inj₂ yz with O.from tk
    ...   | O.self x′ _ = ⊥-elim (zl (apart R [ last ] x x′ yz))
    ...   | O.new {o} {a₀} x₀ nk₀ nF₀ loc = rebuild loc
      where
        oy : o ≼ y
        oy yo with at-new loc
        ... | _ , eq = zl (≺-trans {y ⊕ [ last ]} {o} {z} (apart R [ last ] x x₀ yo) (subst (o ≺_) (sym eq) (≺-ext o [])))

        rebuild : ∀ {e′} → New z e′ o a₀ → W′.TakeT z e′
        rebuild (inj₁ (eq , refl , i)) = subst (λ w → W′.TakeT w _) (sym eq) (W′.fail (proj₁ (upto ag oy) x₀) nk₀ (unfail ag oy nF₀) i)
        rebuild (inj₂ (eq , refl))     = subst (λ w → W′.TakeT w end) (sym eq) (W′.stop (proj₁ (upto ag oy) x₀) nk₀ (unfail ag oy nF₀))

    -- AT A ROW, agreement below it and of the takes there carries back.
    point1 : ∀ {y e} → (∀ {y₀} → y₀ ≺ y → AgreeTo y₀ t t′) → (∀ {e} → W.TakeT y e → W′.TakeT y e)
           → ¬ W.Failed y → O.NoFail y → t y e → t′ y e
    point1 {y} below tk nF nf x with O′.from (tk (O.keep-row x nF nf))
    ... | O′.self x′ _ = x′
    ... | O′.new {o} {a} x₀ nk _ loc with at-new loc
    ...   | _ , eq = ⊥-elim (nF (refail< below (o , a , x₀ , nk , subst (o ≺_) (sym eq) (≺-ext o []))))

    -- A row the other holds at or past a value carries it.
    row-past : ∀ {y y′ a e′} → (∀ {y₀} → y₀ ≺ y → AgreeTo y₀ t t′) → Cons t t′ → ¬ W.Failed y
             → t y (out a) → W′.TakeT y′ e′ → y ≼ y′ → t′ y (out a)
    row-past below cab nF x tk′ yy′ with O′.past (O′.from tk′) yy′
    ... | inj₁ (o , e₀ , xo , yo) = cab below x xo yo
    ... | inj₂ F = ⊥-elim (nF (refail< below F))

  ----------------------------------------------------------------------
  -- Two takes

  module Two {t t′ : EmissionSet A} (R : Run t) (R′ : Run t′)
    (fin : ∀ q → Few (λ y e → t y e ⊎ t′ y e) q) (cab : Cons t t′) (cba : Cons t′ t) where
    open Dir R R′ public
    module D′ = Dir R′ R

    push : ∀ {k} → AgreeTo k t t′ → AgreeTo k W.TakeT W′.TakeT
    push ag = ⟨ (λ yk → push1 ag yk , D′.push1 (AgreeTo-sym ag) yk) ⟩

    push-fail : ∀ {y a} → AgreeTo y t t′ → t y (out a) → T (not (keep a)) → ¬ W.Failed y
              → AgreeTo (y ⊕ [ last ]) W.TakeT W′.TakeT
    push-fail {y} ag x nk nF =
      ⟨ (λ zl → push-fail1 ag x nk nF zl , D′.push-fail1 (AgreeTo-sym ag) (proj₁ (upto ag (≼-refl {y})) x) nk (unfail ag (≼-refl {y}) nF) zl) ⟩

    private
      sym< : ∀ {y} → (∀ {y₀} → y₀ ≺ y → AgreeTo y₀ t t′) → ∀ {y₀} → y₀ ≺ y → AgreeTo y₀ t′ t
      sym< below {y₀} lt = AgreeTo-sym (below {y₀} lt)

      nf< : ∀ {y z} → ¬ W.Failed z → y ≺ z → O.NoFail y
      nf< {y} nF lt {a} x with dec-keep a
      ... | inj₁ k  = k
      ... | inj₂ nk = ⊥-elim (nF (y , a , x , nk , lt))

    -- AGREEMENT CARRIES BACK, up to a row of the first take's, no failure before it.
    lift : ∀ {k w e} → AgreeTo k W.TakeT W′.TakeT → W.TakeT w e → k ≼ w → ¬ W.Failed k → O.NoFail k → AgreeTo k t t′
    lift {k} {w} agT tw kw nF nf = ag-ind fin step
      where
        step : ∀ {y} → y ≼ k → (∀ {y₀} → y₀ ≺ y → AgreeTo y₀ t t′) → ∀ {e} → (t y e → t′ y e) × (t′ y e → t y e)
        step {y} yk below = point1 below (proj₁ (upto agT yk)) nFy nfy , D′.point1 (sym< below) (proj₂ (upto agT yk)) (unfail< nFy) nf′y
          where
            nFy : ¬ W.Failed y
            nFy F = nF (O.failed-≼ yk F)

            unfail< : ¬ W.Failed y → ¬ W′.Failed y
            unfail< nF′ F = nF′ (refail< below F)

            nfy : O.NoFail y
            nfy {a} x with ≼-split {y} {k} yk
            ... | inj₁ lt   = nf< nF lt x
            ... | inj₂ refl = nf x

            nf′y : O′.NoFail y
            nf′y {a} x′ with dec-keep a
            ... | inj₁ kp = kp
            ... | inj₂ nk with O.past (O.from tw) (≼-trans {y} {k} {w} yk kw)
            ...   | inj₁ (o , e₀ , xo , yo) = ⊥-elim (clash (nfy (cba (sym< below) x′ xo yo)) nk)
            ...   | inj₂ F = ⊥-elim (nFy F)

    -- Up to a failing value, for one of its rows.
    lift-fail : ∀ {w e y a} → AgreeTo w W.TakeT W′.TakeT → W.TakeT w e → y ≼ w
              → t y (out a) → T (not (keep a)) → ¬ W.Failed y → AgreeTo y t t′
    lift-fail {w} {y = y} {a} agT tw yw x nk nF = ⟨ at ⟩
      where
        below : ∀ {y₀} → y₀ ≺ y → AgreeTo y₀ t t′
        below {y₀} lt =
          let y₀w = ≺→≼ {y₀} {w} (≺-≼-≺ {y₀} {y} {w} lt yw)
          in lift (ag-down {q = w} {y₀} y₀w agT) tw y₀w (λ F → nF (O.failed-≼ (≺→≼ {y₀} {y} lt) F)) (nf< nF lt)

        x′ : t′ y (out a)
        x′ = row-past below cab nF x (proj₁ (upto agT (≼-refl {w})) tw) yw

        at : ∀ {z e} → z ≼ y → (t z e → t′ z e) × (t′ z e → t z e)
        at {z} zy with ≼-split {z} {y} zy
        ... | inj₁ lt   = upto (below {z} lt) (≼-refl {z})
        ... | inj₂ refl = (λ x₁ → subst (t′ y) (Run.func R x x₁) x′) , (λ x₁ → subst (t y) (Run.func R′ x′ x₁) x)

    -- TWO TAKES ARE TRUNCATED BEFORE THEY DIFFER.
    cons-T : Cons W.TakeT W′.TakeT
    cons-T {y} below (W.pass x kp nF) tk′ yy′ = W′.pass (row-past cb cab nF x tk′ yy′) kp (λ F → nF (refail< cb F))
      where
        cb : ∀ {y₀} → y₀ ≺ y → AgreeTo y₀ t t′
        cb {y₀} lt = lift (below {y₀} lt) (W.pass x kp nF) (≺→≼ {y₀} {y} lt) (λ F → nF (O.failed-≼ (≺→≼ {y₀} {y} lt) F)) (nf< nF lt)
    cons-T {y′ = y′} below (W.fail {o} x nk nF i) tk′ yy′ =
      W′.fail (row-past cb cab nF x tk′ (≼-trans {o} {o ⊕ [ ix 0 ]} {y′} (≺→≼ {o} {o ⊕ [ ix 0 ]} (≺-ext o [])) yy′)) nk (λ F → nF (refail< cb F)) i
      where
        cb : ∀ {y₀} → y₀ ≺ o → AgreeTo y₀ t t′
        cb {y₀} lt =
          let lt′ = ≺-trans {y₀} {o} {o ⊕ [ ix 0 ]} lt (≺-ext o [])
          in lift (below {y₀} lt′) (W.fail x nk nF i) (≺→≼ {y₀} {o ⊕ [ ix 0 ]} lt′) (λ F → nF (O.failed-≼ (≺→≼ {y₀} {o} lt) F)) (nf< nF lt)
