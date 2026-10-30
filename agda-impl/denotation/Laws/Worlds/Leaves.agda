{-# OPTIONS --guardedness #-}

module denotation.Laws.Worlds.Leaves where

open import Data.Bool using (T)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc; ++-cancelˡ; ∷ʳ-injectiveʳ)
open import Data.Nat using (ℕ; suc; _⊔_; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; 1+n≰n; m≤m⊔n; m≤n⊔m)
open import Data.List.Relation.Unary.All using (_∷_; [])
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (Equivalence; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

open import denotation.Events using (Pos; Label; ix; last; inside; inside-++; inside-self; <ᵖ-part; <ᵖ-ix)
open import denotation.Events using (ofᴱ; Events)
open import denotation.EmissionSet using (Ev; out; end; skip; pin; Silent; hush; held; EmissionSet; _≺_; Den; enter; Truncate; InE;
  at-out; at-end; on-out; on-skip; spin; MapT; map-out; map-skip; map-end; map-pin; Spin;
  module Scan; DeferT; guard; body; from; module Op)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≺-absurd; ≼-antisym; ≺-ext; LimD)
open import denotation.Laws.Worlds using (InvAt; InvD; Ok; Plain; Real; W; W⁼; _⊑_; anc-lead; apart; ext≢; here; inW; leads; nest-in; nest⁼; not-up; ok-step; plain-ix; plain-last; real-snoc; shrink; shrink⁼; sib; step; world-after; world-anc⁼; ⊑-snoc; ⊑-snoc⁺; ⊑-trans)

------------------------------------------------------------------------
-- The leaves keep it

out-inj : ∀ {A} {a b : A} → out a ≡ out b → a ≡ b
out-inj refl = refl

private
  -- One plain label below `p`.
  Below : Pos → Pos → Set
  Below p y = Σ Label λ l → Plain l × y ≡ p ++ [ l ]

  -- A READING ONE LABEL DEEP keeps the invariant: its rows are siblings,
  -- under `p` together.
  shallow-inv : ∀ {A H p} {X : EmissionSet A} → Ok H p → (∀ {y e} → X y e → Below p y)
              → (∀ {y e e′} → X y e → X y e′ → e ≡ e′) → (∀ {c y e} → X c end → X y e → c ≺ y → Silent e)
              → (∀ {y r} → X y (pin r) → ⊥) → InvAt H p X
  shallow-inv {H = H} {p} (r , _) sh fu qu np = record
    { world = λ x → wo (sh x)
    ; real  = λ x → re (sh x)
    ; func  = fu
    ; flat  = λ x x′ → fl (sh x) (sh x′)
    ; burst = λ c y _ → p , here , ins (sh c) , ins (sh y)
    ; under = λ x y pl v le → un (sh x) (sh y) pl v le
    ; quiet = qu
    ; pinned = λ x → ⊥-elim (np x)
    }
    where
      ne : ∀ {l₁ l₂ l} → p ++ [ l₂ ] ≡ (p ++ [ l₁ ]) ++ [ l ] → ⊥
      ne {l₁} {l₂} {l} eq with ++-cancelˡ p [ l₂ ] (l₁ ∷ l ∷ []) (trans eq (++-assoc p [ l₁ ] [ l ]))
      ... | ()

      un : ∀ {q y w l} → Below p q → Below p y → Plain l → W⁼ H (q ++ [ l ]) w → w ⊑ y → ⊥
      un (_ , pl₁ , refl) (_ , pl₂ , refl) pl v le = sib (real-snoc p pl₁ r) pl₂ (⊑-snoc⁺ p) ne v le

      wo : ∀ {y} → Below p y → W H p y
      wo (_ , pl , refl) = step here pl

      re : ∀ {y} → Below p y → Real y
      re (_ , pl , refl) = real-snoc p pl r

      ins : ∀ {y} → Below p y → T (inside p y)
      ins (l , _ , refl) = Equivalence.from T-≡ (inside-++ p p [ l ] (inside-self p))

      fl : ∀ {y l ys} → Below p y → Below p (y ++ l ∷ ys) → ⊥
      fl {l = l} {ys} (l₀ , _ , refl) (l′ , _ , eq) with ++-cancelˡ p (l₀ ∷ l ∷ ys) [ l′ ] (trans (sym (++-assoc p [ l₀ ] (l ∷ ys))) eq)
      ... | ()

  -- A reading whose rows are another's, ends kept, keeps its invariant.
  inv-via : ∀ {A B H p} {X : EmissionSet A} {Y : EmissionSet B}
          → (bk : ∀ {y e} → X y e → Σ (Ev B) (Y y)) → (∀ {y} → X y end → Y y end)
          → (∀ {y e} (x : X y e) → Silent (proj₁ (bk x)) → Silent e)
          → (∀ {y r} → X y (pin r) → Y y (pin r))
          → (∀ {y e e′} → X y e → X y e′ → e ≡ e′) → InvAt H p Y → InvAt H p X
  inv-via bk be bs bp fu I = record
    { world = λ x → InvAt.world I (proj₂ (bk x))
    ; real  = λ x → InvAt.real I (proj₂ (bk x))
    ; func  = fu
    ; flat  = λ x x′ → InvAt.flat I (proj₂ (bk x)) (proj₂ (bk x′))
    ; burst = λ c y cy → InvAt.burst I (be c) (proj₂ (bk y)) cy
    ; under = λ x y pl v le → InvAt.under I (proj₂ (bk x)) (proj₂ (bk y)) pl v le
    ; quiet = λ c y cy → bs y (InvAt.quiet I (be c) (proj₂ (bk y)) cy)
    ; pinned = λ x → InvAt.pinned I (bp x)
    }

  of-end : ∀ {A} p i (xs : List A) {y} → InE (ofᴱ p i xs) y end → y ≡ p ++ [ last ]
  of-end p i []       at-end     = refl
  of-end p i (x ∷ xs) (on-out r) = of-end p (suc i) xs r

  of-below : ∀ {A} p i (xs : List A) {y e} → InE (ofᴱ p i xs) y e → Below p y
  of-below p i []       at-end     = last , plain-last , refl
  of-below p i (x ∷ xs) at-out     = ix i , plain-ix , refl
  of-below p i (x ∷ xs) (on-out r) = of-below p (suc i) xs r

  acc-row : ∀ {A B} {f : B → A → B} {z} {t : EmissionSet A} {q b} → Scan.Acc f z t q b → Σ (Ev A) (t q)
  acc-row (Scan.acc₀ x _)     = _ , x
  acc-row (Scan.acc _ x _ _)  = _ , x

  spin-skip : ∀ {A p y} {e : Ev A} → Spin p y e → e ≡ skip
  spin-skip (spin _) = refl

  -- The rows of `of`, past the index it is at.
  of-idx : ∀ {A} p i (xs : List A) {y e} → InE (ofᴱ p i xs) y e → (Σ ℕ λ j → i ≤ j × y ≡ p ++ [ ix j ]) ⊎ y ≡ p ++ [ last ]
  of-idx p i []       at-end     = inj₂ refl
  of-idx p i (x ∷ xs) at-out     = inj₁ (i , ≤-refl , refl)
  of-idx p i (x ∷ xs) (on-out r) with of-idx p (suc i) xs r
  ... | inj₁ (j , le , eq) = inj₁ (j , ≤-trans (n≤1+n i) le , eq)
  ... | inj₂ eq            = inj₂ eq

  of-fresh : ∀ {A} p i (xs : List A) {e} → InE (ofᴱ p (suc i) xs) (p ++ [ ix i ]) e → ⊥
  of-fresh p i xs r with of-idx p (suc i) xs r
  ... | inj₁ (j , le , eq) with ∷ʳ-injectiveʳ p p eq
  ...   | refl = 1+n≰n le
  of-fresh p i xs r | inj₂ eq with ∷ʳ-injectiveʳ p p eq
  ... | ()

  of-func : ∀ {A} p i (xs : List A) {y e e′} → InE (ofᴱ p i xs) y e → InE (ofᴱ p i xs) y e′ → e ≡ e′
  of-func p i []       at-end     at-end      = refl
  of-func p i (x ∷ xs) at-out     at-out      = refl
  of-func p i (x ∷ xs) at-out     (on-out r′) = ⊥-elim (of-fresh p i xs r′)
  of-func p i (x ∷ xs) (on-out r) at-out      = ⊥-elim (of-fresh p i xs r)
  of-func p i (x ∷ xs) (on-out r) (on-out r′) = of-func p (suc i) xs r r′

  -- A fold has one value at a position.
  module AccF {A B : Set} (f : B → A → B) (z : B) {t : EmissionSet A} (fu : ∀ {y e e′} → t y e → t y e′ → e ≡ e′) where
    open Scan f z t using (Acc; acc₀; acc)

    acc-val : ∀ {q b} → Acc q b → Σ A λ a → t q (out a)
    acc-val (acc₀ x _)    = _ , x
    acc-val (acc _ x _ _) = _ , x

    acc-func : ∀ {q q′ b b′} → q ≡ q′ → Acc q b → Acc q′ b′ → b ≡ b′
    acc-func refl (acc₀ x _)       (acc₀ x′ _)      = cong (f z) (out-inj (fu x x′))
    acc-func refl (acc₀ _ mn)      (acc a _ lt _)   = ⊥-elim (mn (proj₂ (acc-val a)) lt)
    acc-func refl (acc a _ lt _)   (acc₀ _ mn)      = ⊥-elim (mn (proj₂ (acc-val a)) lt)
    acc-func refl (acc {q₀} a x lt nx) (acc {q₁} a′ x′ lt′ nx′) =
      cong₂ f (acc-func (≼-antisym {q₀} {q₁} (λ h → nx′ (proj₂ (acc-val a)) h lt) (λ h → nx (proj₂ (acc-val a′)) h lt′)) a a′)
              (out-inj (fu x x′))

-- A timeline's rows hold no pin.
ine-pin : ∀ {A} {es : Events A} {y r} → InE es y (pin r) → ⊥
ine-pin (on-out x)  = ine-pin x
ine-pin (on-skip x) = ine-pin x

empty-inv : ∀ {A H} → InvD H (Op.empty {A})
empty-inv p ok = shallow-inv ok (λ { (at-end , _) → last , plain-last , refl }) (λ { (at-end , _) (at-end , _) → refl })
  (λ { (at-end , _) (at-end , _) cy → ⊥-elim (≺-irrefl {p ++ [ last ]} cy) }) λ { (() , _) }

of-inv : ∀ {A H} (xs : List A) → InvD H (Op.of xs)
of-inv xs p ok = shallow-inv ok (λ x → of-below p 0 xs (proj₁ x)) (λ x x′ → of-func p 0 xs (proj₁ x) (proj₁ x′)) qu (ine-pin ∘ proj₁)
  where
    qu : ∀ {c y e} → Truncate (InE (ofᴱ p 0 xs)) c end → Truncate (InE (ofᴱ p 0 xs)) y e → c ≺ y → _
    qu (c , _) (y , _) cy with of-end p 0 xs c | of-idx p 0 xs y
    ... | refl | inj₁ (j , _ , refl) = ⊥-elim (≺-absurd {p ++ [ last ]} {p ++ [ ix j ]} cy (Equivalence.from T-≡ (<ᵖ-part p {ix j} {last} [] [] refl)))
    ... | refl | inj₂ refl           = ⊥-elim (≺-irrefl {p ++ [ last ]} cy)

spin-inv : ∀ {A H} → InvD H (Op.⊥ {A})
spin-inv p ok = shallow-inv ok (λ { (spin i , _) → ix i , plain-ix , refl }) (λ x x′ → trans (spin-skip (proj₁ x)) (sym (spin-skip (proj₁ x′))))
  (λ _ y _ → subst Silent (sym (spin-skip (proj₁ y))) hush) λ { (() , _) }

map-inv : ∀ {A B H} (f : A → B) {s : Den A} → InvD H s → InvD H (Op.map f s)
map-inv {A} {B} f {s} inv p ok = inv-via bk be bs bp fu (inv p ok)
  where
    mapE : Ev A → Ev B
    mapE (out a) = out (f a)
    mapE skip    = skip
    mapE end     = end
    mapE (pin r) = pin r

    bk : ∀ {y e} → Truncate (MapT f (enter s p)) y e → Σ _ (enter s p y)
    bk (map-out x , _)  = _ , x
    bk (map-skip x , _) = _ , x
    bk (map-end x , _)  = _ , x
    bk (map-pin x , _)  = _ , x

    bk-map : ∀ {y e} (x : Truncate (MapT f (enter s p)) y e) → e ≡ mapE (proj₁ (bk x))
    bk-map (map-out x , _)  = refl
    bk-map (map-skip x , _) = refl
    bk-map (map-end x , _)  = refl
    bk-map (map-pin x , _)  = refl

    fu : ∀ {y e e′} → Truncate (MapT f (enter s p)) y e → Truncate (MapT f (enter s p)) y e′ → e ≡ e′
    fu x x′ = trans (bk-map x) (trans (cong mapE (InvAt.func (inv p ok) (proj₂ (bk x)) (proj₂ (bk x′)))) (sym (bk-map x′)))

    be : ∀ {y} → Truncate (MapT f (enter s p)) y end → enter s p y end
    be (map-end x , _) = x

    bs : ∀ {y e} (x : Truncate (MapT f (enter s p)) y e) → Silent (proj₁ (bk x)) → Silent e
    bs (map-skip x , _) _ = hush
    bs (map-pin x , _)  _ = held
    bs (map-out x , _)  ()
    bs (map-end x , _)  ()

    bp : ∀ {y r} → Truncate (MapT f (enter s p)) y (pin r) → enter s p y (pin r)
    bp (map-pin x , _) = x

scan-inv : ∀ {A B H} (f : B → A → B) z {s : Den A} → InvD H s → InvD H (Op.scan f z s)
scan-inv f z {s} inv p ok = inv-via bk be bs bp fu (inv p ok)
  where
    I = inv p ok
    open AccF f z (InvAt.func I)

    fu : ∀ {y e e′} → Truncate (Scan.ScanT f z (enter s p)) y e → Truncate (Scan.ScanT f z (enter s p)) y e′ → e ≡ e′
    fu (Scan.sval a , _)  (Scan.sval a′ , _)  = cong out (acc-func refl a a′)
    fu (Scan.sval a , _)  (Scan.sstep x′ , _) with InvAt.func I (proj₂ (acc-val a)) x′
    ... | ()
    fu (Scan.sval a , _)  (Scan.send x′ , _)  with InvAt.func I (proj₂ (acc-val a)) x′
    ... | ()
    fu (Scan.sstep x , _) (Scan.sval a′ , _)  with InvAt.func I (proj₂ (acc-val a′)) x
    ... | ()
    fu (Scan.sstep x , _) (Scan.sstep x′ , _) = refl
    fu (Scan.sstep x , _) (Scan.send x′ , _)  with InvAt.func I x x′
    ... | ()
    fu (Scan.send x , _)  (Scan.sval a′ , _)  with InvAt.func I (proj₂ (acc-val a′)) x
    ... | ()
    fu (Scan.send x , _)  (Scan.sstep x′ , _) with InvAt.func I x x′
    ... | ()
    fu (Scan.send x , _)  (Scan.send x′ , _)  = refl
    fu (Scan.spin x , _)  (Scan.spin x′ , _)  with InvAt.func I x x′
    ... | refl = refl
    fu (Scan.spin x , _)  (Scan.sval a′ , _)  with InvAt.func I (proj₂ (acc-val a′)) x
    ... | ()
    fu (Scan.spin x , _)  (Scan.sstep x′ , _) with InvAt.func I x x′
    ... | ()
    fu (Scan.spin x , _)  (Scan.send x′ , _)  with InvAt.func I x x′
    ... | ()
    fu (Scan.sval a , _)  (Scan.spin x′ , _)  with InvAt.func I (proj₂ (acc-val a)) x′
    ... | ()
    fu (Scan.sstep x , _) (Scan.spin x′ , _)  with InvAt.func I x x′
    ... | ()
    fu (Scan.send x , _)  (Scan.spin x′ , _)  with InvAt.func I x x′
    ... | ()

    bk : ∀ {y e} → Truncate (Scan.ScanT f z (enter s p)) y e → Σ _ (enter s p y)
    bk (Scan.sval a , _)  = acc-row a
    bk (Scan.sstep x , _) = _ , x
    bk (Scan.send x , _)  = _ , x
    bk (Scan.spin x , _)  = _ , x

    be : ∀ {y} → Truncate (Scan.ScanT f z (enter s p)) y end → enter s p y end
    be (Scan.send x , _) = x

    bs : ∀ {y e} (x : Truncate (Scan.ScanT f z (enter s p)) y e) → Silent (proj₁ (bk x)) → Silent e
    bs (Scan.sval (Scan.acc₀ _ _) , _)    ()
    bs (Scan.sval (Scan.acc _ _ _ _) , _) ()
    bs (Scan.sstep x , _) _ = hush
    bs (Scan.spin x , _)  _ = held
    bs (Scan.send x , _)  ()

    bp : ∀ {y r} → Truncate (Scan.ScanT f z (enter s p)) y (pin r) → enter s p y (pin r)
    bp (Scan.spin x , _) = x

-- A DEFER keeps it: its guard lies before the body's subscription, and
-- the body's world lies in its own.
defer-inv : ∀ {A H} {s : Den A} → InvD H s → InvD H (Op.defer s)
defer-inv {A} {H} {s} inv p ok = record { world = wo ; real = re ; func = λ x x′ → fu (view x) (view x′) ; flat = λ x x′ → fl (view x) (view x′)
  ; burst = λ c y cy → bu (view c) (view y) cy ; under = λ x y → un (view x) (view y) ; quiet = λ c y cy → qu (view c) (view y) cy
  ; pinned = pn }
  where
    I = inv (p ++ [ ix 1 ]) (ok-step p ok)
    B = enter s (p ++ [ ix 1 ])

    View : Pos → Ev A → Set
    View y e = (y ≡ p ++ [ ix 0 ] × e ≡ skip) ⊎ B y e

    view : ∀ {y e} → Truncate (DeferT s p) y e → View y e
    view (guard , _)  = inj₁ (refl , refl)
    view (body x , _) = inj₂ x

    after : ∀ {y e} → B y e → (p ++ [ ix 1 ]) ≺ y
    after x = world-after (InvAt.world I x) (InvAt.real I x)

    -- The guard and what lies under it come before the body's subscription.
    early : ∀ ys → (p ++ ix 0 ∷ ys) ≺ (p ++ [ ix 1 ])
    early ys = Equivalence.from T-≡ (<ᵖ-part p ys [] (<ᵖ-ix 0))

    wo : ∀ {y e} → Truncate (DeferT s p) y e → W H p y
    wo (guard , _)  = step here plain-ix
    wo (body x , _) = shrink (InvAt.world I x)

    re : ∀ {y e} → Truncate (DeferT s p) y e → Real y
    re (guard , _)  = real-snoc p plain-ix (proj₁ ok)
    re (body x , _) = InvAt.real I x

    fu : ∀ {y e e′} → View y e → View y e′ → e ≡ e′
    fu (inj₁ (_ , refl)) (inj₁ (_ , refl)) = refl
    fu (inj₁ (refl , _)) (inj₂ b) = ⊥-elim (≺-absurd {p ++ [ ix 1 ]} {p ++ [ ix 0 ]} (after b) (early []))
    fu (inj₂ b) (inj₁ (refl , _)) = ⊥-elim (≺-absurd {p ++ [ ix 1 ]} {p ++ [ ix 0 ]} (after b) (early []))
    fu (inj₂ b) (inj₂ b′) = InvAt.func I b b′

    fl : ∀ {y e l ys e′} → View y e → View (y ++ l ∷ ys) e′ → ⊥
    fl {ys = ys} (inj₁ (refl , _)) (inj₁ (eq , _)) = ext≢ (p ++ [ ix 0 ]) ys eq
    fl {l = l} {ys} (inj₁ (refl , _)) (inj₂ b) =
      ≺-absurd {p ++ [ ix 1 ]} {(p ++ [ ix 0 ]) ++ l ∷ ys} (after b) (subst (_≺ (p ++ [ ix 1 ])) (sym (++-assoc p [ ix 0 ] (l ∷ ys))) (early (l ∷ ys)))
    fl {y} {l = l} {ys} (inj₂ b) (inj₁ (eq , _)) =
      ≺-absurd {p ++ [ ix 1 ]} {p ++ [ ix 0 ]} (≺-trans {p ++ [ ix 1 ]} {y} {p ++ [ ix 0 ]} (after b) (subst (y ≺_) eq (≺-ext y ys))) (early [])
    fl (inj₂ b) (inj₂ b′) = InvAt.flat I b b′

    bu : ∀ {c y e} → View c end → View y e → c ≺ y → Σ Pos λ w → W⁼ H p w × T (inside w c) × T (inside w y)
    bu (inj₁ (_ , ())) _ _
    bu {c} (inj₂ b) (inj₁ (refl , _)) cy =
      ⊥-elim (≺-absurd {p ++ [ ix 1 ]} {p ++ [ ix 0 ]} (≺-trans {p ++ [ ix 1 ]} {c} {p ++ [ ix 0 ]} (after b) cy) (early []))
    bu (inj₂ b) (inj₂ b′) cy with InvAt.burst I b b′ cy
    ... | w , w⁼ , i = w , inW (shrink⁼ w⁼) , i

    g0 : W H p (p ++ [ ix 0 ])
    g0 = step here plain-ix

    rg : Real (p ++ [ ix 0 ])
    rg = real-snoc p plain-ix (proj₁ ok)

    -- What lies in the guard's child's world is not in the body's.
    off : ∀ {l w} → Plain l → W⁼ H ((p ++ [ ix 0 ]) ++ [ l ]) w → W⁼ H (p ++ [ ix 1 ]) w → ⊥
    off pl v v′ = apart (proj₁ ok) (world-anc⁼ (nest⁼ (inW (step here pl)) v)) (world-anc⁼ v′)

    un : ∀ {q y w l e e′} → View q e → View y e′ → Plain l → W⁼ H (q ++ [ l ]) w → w ⊑ y → ⊥
    un (inj₁ (refl , _)) (inj₁ (refl , _)) pl v le = not-up rg v le
    un (inj₁ (refl , _)) (inj₂ b) pl v le =
      leads (proj₁ ok) (proj₂ ok) (nest-in (step (inW g0) pl) v) (off pl v) nr (inW (InvAt.world I b)) le
      where nr : _ ⊑ (p ++ [ ix 1 ]) → ⊥
            nr le′ with ⊑-snoc p le′
            ... | inj₁ wp   = not-up rg v (⊑-trans wp (⊑-snoc⁺ p))
            ... | inj₂ refl = off pl v here
    un (inj₂ b) (inj₁ (refl , _)) pl v le =
      anc-lead (world-anc⁼ (nest⁼ (inW (step (inW (InvAt.world I b)) pl)) v)) le rg (early [])
    un (inj₂ b) (inj₂ b′) pl v le = InvAt.under I b b′ pl v le

    qu : ∀ {c y e} → View c end → View y e → c ≺ y → Silent e
    qu (inj₁ (_ , ())) _ _
    qu _ (inj₁ (_ , refl)) _ = hush
    qu (inj₂ b) (inj₂ b′) cy = InvAt.quiet I b b′ cy

    pn : ∀ {y r} → Truncate (DeferT s p) y (pin r) → W⁼ H p r × T (inside r y)
    pn (body x , _) with InvAt.pinned I x
    ... | w , i = inW (shrink⁼ w) , i

-- A LIMIT keeps it: any finitely many of its rows are one member's.
lim-inv : ∀ {A H} {c : ℕ → Den A} → (∀ n → InvD H (c n)) → InvD H (LimD c)
lim-inv inv p ok = record
  { world = λ { (from N l , _) → InvAt.world (I N) (l N ≤-refl) }
  ; real  = λ { (from N l , _) → InvAt.real (I N) (l N ≤-refl) }
  ; func  = λ { (from N l , _) (from M m , _) → InvAt.func (I (N ⊔ M)) (l (N ⊔ M) (m≤m⊔n N M)) (m (N ⊔ M) (m≤n⊔m N M)) }
  ; flat  = λ { (from N l , _) (from M m , _) → InvAt.flat (I (N ⊔ M)) (l (N ⊔ M) (m≤m⊔n N M)) (m (N ⊔ M) (m≤n⊔m N M)) }
  ; burst = λ { (from N l , _) (from M m , _) cy → InvAt.burst (I (N ⊔ M)) (l (N ⊔ M) (m≤m⊔n N M)) (m (N ⊔ M) (m≤n⊔m N M)) cy }
  ; under = λ { (from N l , _) (from M m , _) pl v le → InvAt.under (I (N ⊔ M)) (l (N ⊔ M) (m≤m⊔n N M)) (m (N ⊔ M) (m≤n⊔m N M)) pl v le }
  ; quiet = λ { (from N l , _) (from M m , _) cy → InvAt.quiet (I (N ⊔ M)) (l (N ⊔ M) (m≤m⊔n N M)) (m (N ⊔ M) (m≤n⊔m N M)) cy }
  ; pinned = λ { (from N l , _) → InvAt.pinned (I N) (l N ≤-refl) }
  }
  where
    I = λ n → inv n p ok
