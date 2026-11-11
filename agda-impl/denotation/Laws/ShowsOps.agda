{-# OPTIONS --guardedness #-}

-- EVERY OPERATOR BUT A JOINER SHOWS ITS HANGS.  A leaf, an end and a hot
-- pin nothing, so every row they show is few.  `map` and `scan` keep their
-- input's positions.  A `takeWhile` is what it passes, closed downward in
-- its input; the failure, one position; and the pins kept past it, whose
-- connects lie before every failing value.  A `connect` is its body and
-- its source's rows one step down: those inside the subscribe burst or
-- before the body ends, closed downward in the source; and the pins kept
-- past the body's end, whose connects lie before every end.
module denotation.Laws.ShowsOps where

open import Data.Bool using (Bool; T; true; false; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

import denotation.Events as E
open import denotation.Position using (Pos; ix; last; inside; _⊕_)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; _≺_; _≼_; Few; Reach; Den; enter; InE;
  at-out; at-skip; at-end; on-out; on-skip; spin; MapT; map-out; map-skip; map-pin; map-end;
  module Scan; module TakeWhile; module Connect; module Op)
open import denotation.Laws.Modulus using (≼-split; T-not; ≺→≼; ≼-or-≻; ≼-≺-≺; ≺-≼-≺; ≼-antisym; entered-reach; entered-few)
open import denotation.Laws.Worlds using (Ok; InvAt; InvD; in-world; ok-step; full; _⊑_; ⊑-refl; ⊑-≼; inside-⊑; conv)
open import denotation.Laws.Count using (em)
open import denotation.Laws.Fold using (fold)
open import denotation.Laws.Shows using (ShowsK; _⊆ᵖ_; Step; sk-few; sk-same; sk-closed; sk-down; sk-∪; sk-left; sk-step; sk-trunc)

------------------------------------------------------------------------
-- Rows with few before them

-- What pins nothing has few rows before each of its rows.
sk-unpinned : ∀ {A n} (d : Den A) p → (∀ {q e} → enter d p q e → Unpinned e) → ShowsK n (enter d p)
sk-unpinned d p un = sk-few λ {q} {e} x → entered-few d p {e = e} (λ {k} {e′} → full {q = q} (un x) {k} {e′}) x

ine-unpinned : ∀ {A} {ev : E.Events A} {q e} → InE ev q e → Unpinned e
ine-unpinned at-out      = tt
ine-unpinned at-skip     = tt
ine-unpinned at-end      = tt
ine-unpinned (on-out x)  = ine-unpinned x
ine-unpinned (on-skip x) = ine-unpinned x

sk-cold : ∀ {A n} (c : E.Timeline A) p → ShowsK n (enter (Op.cold c) p)
sk-cold c p = sk-unpinned (Op.cold c) p λ x → ine-unpinned (proj₁ x)

sk-empty : ∀ {A n} p → ShowsK n (enter (Op.empty {A}) p)
sk-empty p = sk-unpinned Op.empty p λ x → ine-unpinned (proj₁ x)

sk-of : ∀ {A n} (xs : List A) p → ShowsK n (enter (Op.of xs) p)
sk-of xs p = sk-unpinned (Op.of xs) p λ x → ine-unpinned (proj₁ x)

sk-⊥ : ∀ {A n} p → ShowsK n (enter (Op.⊥ {A}) p)
sk-⊥ p = sk-unpinned Op.⊥ p λ { (spin _ , _) → tt }

------------------------------------------------------------------------
-- One input, its positions kept

sk-map : ∀ {A B n} (f : A → B) (d : Den A) p → ShowsK n (enter d p) → ShowsK n (enter (Op.map f d) p)
sk-map f d p sk = sk-trunc (sk-same to back sk)
  where
    to : MapT f (enter d p) ⊆ᵖ enter d p
    to (map-out x)  ¬t = ¬t (_ , x)
    to (map-skip x) ¬t = ¬t (_ , x)
    to (map-pin x)  ¬t = ¬t (_ , x)
    to (map-end x)  ¬t = ¬t (_ , x)

    back : enter d p ⊆ᵖ MapT f (enter d p)
    back {e = out _} x ¬m = ¬m (_ , map-out x)
    back {e = skip}  x ¬m = ¬m (_ , map-skip x)
    back {e = end}   x ¬m = ¬m (_ , map-end x)
    back {e = pin _} x ¬m = ¬m (_ , map-pin x)

sk-scan : ∀ {A B n} (f : B → A → B) (z : B) (d : Den A) p → ShowsK n (enter d p) → ShowsK n (enter (Op.scan f z d) p)
sk-scan f z d p sk = sk-trunc (sk-closed to back sk)
  where
    t = enter d p
    open Scan f z t using (Acc; acc₀; acc; ScanT; sval; sstep; send) renaming (spin to s-pin)

    acc-val : ∀ {q b} → Acc q b → Σ _ λ a → t q (out a)
    acc-val (acc₀ x _)     = _ , x
    acc-val (acc _ x _ _)  = _ , x

    to : ScanT ⊆ᵖ t
    to (sval a)  ¬t = ¬t (_ , proj₂ (acc-val a))
    to (sstep x) ¬t = ¬t (_ , x)
    to (s-pin x) ¬t = ¬t (_ , x)
    to (send x)  ¬t = ¬t (_ , x)

    back : ∀ {q e} → t q e → Few t q → ¬ ¬ Σ _ (ScanT q)
    back {e = out _} x fw ¬s = fold f z t fw x λ { (_ , a) → ¬s (_ , sval a) }
    back {e = skip}  x _ ¬s = ¬s (_ , sstep x)
    back {e = end}   x _ ¬s = ¬s (_ , send x)
    back {e = pin _} x _ ¬s = ¬s (_ , s-pin x)

------------------------------------------------------------------------
-- Booleans

bool : ∀ b → T b ⊎ T (not b)
bool true  = inj₁ tt
bool false = inj₂ tt


------------------------------------------------------------------------
-- takeWhile

module Take {A H n} (i : Bool) (keep : A → Bool) (d : Den A) (p : Pos) (I : InvAt H p (enter d p)) (sk : ShowsK n (enter d p)) where
  t : EmissionSet A
  t = enter d p

  open TakeWhile i keep t using (Failed; TakeT; pass; fail; stop; step; tend; left)

  Passes : Ev A → Set
  Passes (out a) = T (keep a)
  Passes _       = ⊤

  failed-up : ∀ {j k} → Failed j → j ≼ k → Failed k
  failed-up {j} {k} (c , a , x , nk , cj) jk = c , a , x , nk , ≺-≼-≺ {c} {j} {k} cj jk

  -- Before any failure, and not failing.
  Stay : EmissionSet A
  Stay k e = t k e × ¬ Failed k × Passes e

  sk-stay : ShowsK n Stay
  sk-stay = sk-down (λ x ¬t → ¬t (_ , proj₁ x)) dn sk
    where
      dn : ∀ {q e k e′} → Stay q e → t k e′ → k ≺ q → ¬ ¬ Σ _ (Stay k)
      dn {q} {k = k} (_ , nf , _) x kq ¬s = ¬s (_ , x , (λ fk → nf (failed-up fk (≺→≼ {k} {q} kq))) , ps x)
        where
          ps : ∀ {e′} → t k e′ → Passes e′
          ps {out a} x′ with bool (keep a)
          ... | inj₁ ka = ka
          ... | inj₂ nk = ⊥-elim (nf (k , a , x′ , nk , kq))
          ps {skip}  _ = tt
          ps {end}   _ = tt
          ps {pin _} _ = tt

  IsStay : ∀ {q e} → TakeT q e → Set
  IsStay (pass _ _ _)     = ⊤
  IsStay (step _ _)       = ⊤
  IsStay (tend _ _)       = ⊤
  IsStay {q} (left _ _ _) = ¬ Failed q
  IsStay _                = ⊥

  IsFail : ∀ {q e} → TakeT q e → Set
  IsFail (fail _ _ _ _) = ⊤
  IsFail (stop _ _ _)   = ⊤
  IsFail _              = ⊥

  IsPast : ∀ {q e} → TakeT q e → Set
  IsPast {q} (left _ _ _) = Failed q
  IsPast _                = ⊥

  Y₁ Y₂ Y₃ Y₂₃ : EmissionSet A
  Y₁ q e  = Σ (TakeT q e) IsStay
  Y₂ q e  = Σ (TakeT q e) IsFail
  Y₃ q e  = Σ (TakeT q e) IsPast
  Y₂₃ q e = Σ (TakeT q e) λ x → IsFail x ⊎ IsPast x

  sk-y₁ : ShowsK n Y₁
  sk-y₁ = sk-same to back sk-stay
    where
      to : Y₁ ⊆ᵖ Stay
      to (pass x k nf , _)  ¬s = ¬s (_ , x , nf , k)
      to (step x nf , _)    ¬s = ¬s (_ , x , nf , tt)
      to (tend x nf , _)    ¬s = ¬s (_ , x , nf , tt)
      to (left x _ _ , nf)  ¬s = ¬s (_ , x , nf , tt)
      to (fail _ _ _ _ , ())
      to (stop _ _ _ , ())

      back : Stay ⊆ᵖ Y₁
      back {e = out _} (x , nf , k) ¬y = ¬y (_ , pass x k nf , tt)
      back {e = skip}  (x , nf , _) ¬y = ¬y (_ , step x nf , tt)
      back {e = end}   (x , nf , _) ¬y = ¬y (_ , tend x nf , tt)
      back {k} {pin r} (x , nf , _) ¬y = ¬y (_ , left x (λ fr → nf (failed-up fr (⊑-≼ (inside-⊑ r k ins)))) ins , nf)
        where ins = proj₂ (InvAt.pinned I x)

  -- The failing value, the one with none before it.
  failing : ∀ {y e} → Y₂ y e → Σ Pos λ q → Σ A (λ a → t q (out a) × T (not (keep a))) × ¬ Failed q × (y ≡ q ⊕ [ ix 0 ] ⊎ y ≡ q ⊕ [ last ])
  failing (fail x nk nf _ , _) = _ , (_ , x , nk) , nf , inj₁ refl
  failing (stop x nk nf , _)   = _ , (_ , x , nk) , nf , inj₂ refl
  failing (pass _ _ _ , ())
  failing (step _ _ , ())
  failing (tend _ _ , ())
  failing (left _ _ _ , ())

  first : ∀ {q q′ a a′} → t q (out a) → T (not (keep a)) → ¬ Failed q → t q′ (out a′) → T (not (keep a′)) → ¬ Failed q′ → q ≡ q′
  first {q} {q′} x nk nf x′ nk′ nf′ with ≼-or-≻ q q′ | ≼-or-≻ q′ q
  ... | _       | inj₂ lt  = ⊥-elim (nf′ (q , _ , x , nk , lt))
  ... | inj₂ lt | _        = ⊥-elim (nf (q′ , _ , x′ , nk′ , lt))
  ... | inj₁ le | inj₁ le′ = ≼-antisym {q} {q′} le le′

  sk-y₂ : ShowsK n Y₂
  sk-y₂ = sk-few few₂
    where
      few₂ : ∀ {y e} → Y₂ y e → Few Y₂ y
      few₂ y with failing y
      ... | q , (_ , x , nk) , nf , _ = (q ⊕ [ ix 0 ]) ∷ (q ⊕ [ last ]) ∷ [] , λ y′ _ → place (failing y′)
        where
          place : ∀ {y′} → (Σ Pos λ q′ → Σ A (λ a → t q′ (out a) × T (not (keep a))) × ¬ Failed q′ × (y′ ≡ q′ ⊕ [ ix 0 ] ⊎ y′ ≡ q′ ⊕ [ last ]))
                → y′ ∈ (q ⊕ [ ix 0 ]) ∷ (q ⊕ [ last ]) ∷ []
          place (q′ , (_ , x′ , nk′) , nf′ , w) with first x nk nf x′ nk′ nf′
          place (q′ , _ , _ , inj₁ refl) | refl = here refl
          place (q′ , _ , _ , inj₂ refl) | refl = there (here refl)

  data Bad (c : Pos) : Set where
    bad : ∀ {a} → t c (out a) → T (not (keep a)) → Bad c

  sk-y₃ : ShowsK n Y₃
  sk-y₃ = sk-left Bad few-bad sub tgt
    where
      few-bad : ∀ {c} → Bad c → Σ (List Pos) λ L → ∀ {c′} → Bad c′ → c′ ≺ c → c′ ∈ L
      few-bad {c} (bad {a} x _) with entered-few d p {e = out a} (λ {k} {e′} → full {q = c} {e = out a} tt {k} {e′}) x
      ... | ks , h = ks , λ { (bad x′ _) lt → h x′ lt }

      sub : ∀ {k e} → Y₃ k e → t k e
      sub (left x _ _ , _) = x
      sub (pass _ _ _ , ())
      sub (fail _ _ _ _ , ())
      sub (stop _ _ _ , ())
      sub (step _ _ , ())
      sub (tend _ _ , ())

      tgt : ∀ {k e} → Y₃ k e → Σ Pos λ r → e ≡ pin r × Reach t k (pin r) × (∀ {c} → Bad c → r ≼ c) × ¬ ¬ (Σ Pos λ c → Bad c × r ⊑ c)
      tgt {k} (left {r = r} x nr ins , (c , a , xc , nk , ck)) = r , refl , entered-reach d p x , early , λ ¬l → ¬l (c , bad xc nk , conv (⊑-refl r) (early (bad xc nk)) ck (inside-⊑ r k ins))
        where
          early : ∀ {c′} → Bad c′ → r ≼ c′
          early (bad x′ nk′) cr = nr (_ , _ , x′ , nk′ , cr)
      tgt (pass _ _ _ , ())
      tgt (fail _ _ _ _ , ())
      tgt (stop _ _ _ , ())
      tgt (step _ _ , ())
      tgt (tend _ _ , ())

  sk-y₂₃ : ShowsK n Y₂₃
  sk-y₂₃ = sk-∪ (λ { (x , f) ¬y → ¬y (_ , x , inj₁ f) }) (λ { (x , f) ¬y → ¬y (_ , x , inj₂ f) })
                (λ { (x , inj₁ f) ¬c → ¬c (inj₁ (_ , x , f)) ; (x , inj₂ f) ¬c → ¬c (inj₂ (_ , x , f)) }) sk-y₂ sk-y₃

  sk-takeT : ShowsK n TakeT
  sk-takeT = sk-∪ (λ x ¬y → ¬y (_ , proj₁ x)) (λ x ¬y → ¬y (_ , proj₁ x)) parts sk-y₁ sk-y₂₃
    where
      parts : ∀ {q e} → TakeT q e → ¬ ¬ (Σ _ (Y₁ q) ⊎ Σ _ (Y₂₃ q))
      parts x@(pass _ _ _)   ¬c = ¬c (inj₁ (_ , x , tt))
      parts x@(step _ _)     ¬c = ¬c (inj₁ (_ , x , tt))
      parts x@(tend _ _)     ¬c = ¬c (inj₁ (_ , x , tt))
      parts x@(fail _ _ _ _) ¬c = ¬c (inj₂ (_ , x , inj₁ tt))
      parts x@(stop _ _ _)   ¬c = ¬c (inj₂ (_ , x , inj₁ tt))
      parts x@(left _ _ _)      = em (λ f ¬c → ¬c (inj₂ (_ , x , inj₂ f))) (λ nf ¬c → ¬c (inj₁ (_ , x , nf)))

sk-take : ∀ {A H n} (i : Bool) (keep : A → Bool) (d : Den A) p → InvAt H p (enter d p) → ShowsK n (enter d p)
        → ShowsK n (enter (Op.takeWhile i keep d) p)
sk-take i keep d p I sk = sk-trunc (Take.sk-takeT i keep d p I sk)

------------------------------------------------------------------------
-- connect

module Conn {A B H n} (s : Den A) (F : Den A → Den B) (Is : InvD H s) (p : Pos) (ok : Ok H p)
            (sk-s : ShowsK n (enter s (p ⊕ [ ix 1 ]))) (sk-b : ShowsK n (Connect.β s F p)) where
  open Connect s F p using (σ; β; r; Alive; ConnT; body; burst; echo; kept)

  Iσ : InvAt H r σ
  Iσ = Is r (ok-step p ok)

  -- The source rows a connect shows.
  Shown : EmissionSet A
  Shown k e = σ k e × (T (inside r k) ⊎ (Alive k × Unpinned e) ⊎ Σ Pos λ p′ → e ≡ pin p′ × Alive p′ × T (inside p′ k))

  -- In the subscribe burst, or before the body ends.
  Near : EmissionSet A
  Near k e = σ k e × (T (inside r k) ⊎ Alive k)

  -- Pins kept past the body's end.
  Kept : EmissionSet A
  Kept k e = σ k e × (Σ Pos λ p′ → e ≡ pin p′ × Alive p′ × T (inside p′ k)) × ¬ Alive k

  alive-down : ∀ {j k} → Alive k → j ≼ k → Alive j
  alive-down {j} {k} al jk {c} b = ≼-≺-≺ {j} {k} {c} jk (al b)

  sk-near : ShowsK n Near
  sk-near = sk-down (λ x ¬t → ¬t (_ , proj₁ x)) dn sk-s
    where
      dn : ∀ {q e k e′} → Near q e → σ k e′ → k ≺ q → ¬ ¬ Σ _ (Near k)
      dn (_ , inj₁ ins) x kq ¬n = ¬n (_ , x , inj₁ (in-world Iσ x kq ins))
      dn {q} {k = k} (_ , inj₂ al) x kq ¬n = ¬n (_ , x , inj₂ (alive-down {k} {q} al (≺→≼ {k} {q} kq)))

  data End (c : Pos) : Set where
    ended : β c end → End c

  sk-kept : ShowsK n Kept
  sk-kept = sk-left End few-end proj₁ tgt
    where
      few-end : ∀ {c} → End c → Σ (List Pos) λ L → ∀ {c′} → End c′ → c′ ≺ c → c′ ∈ L
      few-end {c} (ended b) with entered-few (F _) (p ⊕ [ ix 0 ]) {e = end} (λ {k} {e′} → full {q = c} {e = end} tt {k} {e′}) b
      ... | ks , h = ks , λ { (ended b′) lt → h b′ lt }

      tgt : ∀ {k e} → Kept k e → Σ Pos λ r′ → e ≡ pin r′ × Reach σ k (pin r′) × (∀ {c} → End c → r′ ≼ c) × ¬ ¬ (Σ Pos λ c → End c × r′ ⊑ c)
      tgt {k} (x , (p′ , refl , al , ins) , nal) = p′ , refl , entered-reach s r x , (λ { {c} (ended b) → ≺→≼ {p′} {c} (al b) }) , led
        where
          led : ¬ ¬ (Σ Pos λ c → End c × p′ ⊑ c)
          led ¬l = nal λ {c} b → after c b
            where
              after : ∀ c → β c end → k ≺ c
              after c b with ≼-or-≻ c k
              ... | inj₂ kc = kc
              ... | inj₁ ck with ≼-split {c} {k} ck
              ...   | inj₁ lt   = ⊥-elim (¬l (c , ended b , conv (⊑-refl p′) (≺→≼ {p′} {c} (al b)) lt (inside-⊑ p′ k ins)))
              ...   | inj₂ refl = ⊥-elim (¬l (c , ended b , inside-⊑ p′ c ins))

  sk-shown : ShowsK n Shown
  sk-shown = sk-∪ near kept′ parts sk-near sk-kept
    where
      near : Near ⊆ᵖ Shown
      near (x , inj₁ ins) ¬s = ¬s (_ , x , inj₁ ins)
      near {e = out _} (x , inj₂ al) ¬s = ¬s (_ , x , inj₂ (inj₁ (al , tt)))
      near {e = skip}  (x , inj₂ al) ¬s = ¬s (_ , x , inj₂ (inj₁ (al , tt)))
      near {e = end}   (x , inj₂ al) ¬s = ¬s (_ , x , inj₂ (inj₁ (al , tt)))
      near {k} {pin p′} (x , inj₂ al) ¬s = ¬s (_ , x , inj₂ (inj₂ (p′ , refl , alive-down {p′} {k} al (⊑-≼ (inside-⊑ p′ k ins)) , ins)))
        where ins = proj₂ (InvAt.pinned Iσ x)

      kept′ : Kept ⊆ᵖ Shown
      kept′ (x , w , _) ¬s = ¬s (_ , x , inj₂ (inj₂ w))

      parts : ∀ {q e} → Shown q e → ¬ ¬ (Σ _ (Near q) ⊎ Σ _ (Kept q))
      parts (x , inj₁ ins)            ¬c = ¬c (inj₁ (_ , x , inj₁ ins))
      parts (x , inj₂ (inj₁ (al , _))) ¬c = ¬c (inj₁ (_ , x , inj₂ al))
      parts (x , inj₂ (inj₂ w))          = em (λ al ¬c → ¬c (inj₁ (_ , x , inj₂ al))) (λ nal ¬c → ¬c (inj₂ (_ , x , w , nal)))

  IsSrc : ∀ {q e} → ConnT q e → Set
  IsSrc (body _) = ⊥
  IsSrc _        = ⊤

  Src : EmissionSet B
  Src q e = Σ (ConnT q e) IsSrc

  sk-src : ShowsK n Src
  sk-src = sk-step pre img sk-shown
    where
      pre : ∀ {y e} → Src y e → ¬ ¬ Σ Pos λ z → Σ _ (Shown z) × Step z y
      pre (burst x ins , _)        ¬p = ¬p (_ , (_ , x , inj₁ ins) , inj₂ refl)
      pre (echo x al un _ , _)     ¬p = ¬p (_ , (_ , x , inj₂ (inj₁ (al , un))) , inj₂ refl)
      pre (kept x al _ ins , _)    ¬p = ¬p (_ , (_ , x , inj₂ (inj₂ (_ , refl , al , ins))) , inj₂ refl)
      pre (body _ , ())

      img : ∀ {z e} → Shown z e → ¬ ¬ Σ Pos λ y → Σ _ (Src y) × Step z y
      img {z} (x , w) ¬i with bool (inside r z)
      ... | inj₁ ins = ¬i (_ , (_ , burst x ins , tt) , inj₂ refl)
      ... | inj₂ nin with w
      ...   | inj₁ ins                          = T-not ins nin
      ...   | inj₂ (inj₁ (al , un))             = ¬i (_ , (_ , echo x al un nin , tt) , inj₂ refl)
      ...   | inj₂ (inj₂ (_ , refl , al , ins)) = ¬i (_ , (_ , kept x al nin ins , tt) , inj₂ refl)

  sk-connT : ShowsK n ConnT
  sk-connT = sk-∪ (λ b ¬c → ¬c (_ , body b)) (λ x ¬c → ¬c (_ , proj₁ x)) parts sk-b sk-src
    where
      parts : ∀ {q e} → ConnT q e → ¬ ¬ (Σ _ (β q) ⊎ Σ _ (Src q))
      parts (body b)          ¬c = ¬c (inj₁ (_ , b))
      parts x@(burst _ _)     ¬c = ¬c (inj₂ (_ , x , tt))
      parts x@(echo _ _ _ _)  ¬c = ¬c (inj₂ (_ , x , tt))
      parts x@(kept _ _ _ _)  ¬c = ¬c (inj₂ (_ , x , tt))

sk-connect : ∀ {A B H n} (s : Den A) (F : Den A → Den B) → InvD H s → ∀ p → Ok H p
           → ShowsK n (enter s (p ⊕ [ ix 1 ])) → ShowsK n (Connect.β s F p) → ShowsK n (enter (Op.connect s F) p)
sk-connect s F Is p ok sk-s sk-b = sk-trunc (Conn.sk-connT s F Is p ok sk-s sk-b)
