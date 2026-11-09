{-# OPTIONS --guardedness #-}

-- A HANG SHOWS, COUNTED: past `v`, a reader reaching few rows before it
-- finds few rows of any kind there, when what it reaches is covered by at
-- most `n` positions (`ShowsK`).  Showing within every bound is showing.
--
-- The count is kept by every operator but `defer`: each place a row sits
-- is read through one cover list, and an operator's rows are a union of
-- parts, each closed downward in an input, relabelled one step down, or
-- pins kept past a cut.  A `defer`'s guard is the one row its body's rows
-- all wait on, so it spends one position of the cover (`sk-guard`).
--
-- PINS KEPT PAST A CUT have finitely many connects: each connect lies at or
-- before every cut and leads one, and a cut has few cuts before it, so the
-- connects are positions the first cut, or one before it, extends
-- (`sk-left`).  A pin with its connect's other pins is few.
--
-- A FAN: a joiner's lanes each lie past the value they run, so a reader
-- few rows into the outer meets finitely many lanes (`sk-fan`).
module denotation.Laws.Shows where

open import Data.Bool using (T)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any.Properties using (map⁺)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; suc; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (decidable-stable)

open import denotation.Position using (Pos; ix; _≟ᵖ_; _⊕_)
open import denotation.Events using (<ᵖ-step)
open import denotation.EmissionSet using (Ev; pin; EmissionSet; _≺_; _≼_; Few; Reach; Truncate; DeferT; guard; body; Den; enter)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≺-absurd; ≺→≼; ≼-refl; ≺-≼-≺; ≼-≺-≺; ≼-or-≻)
open import denotation.Laws.Worlds using (Shows; _⊑_; ⊑-refl; ⊑-≼; ⊑-cmp; conv)
open import denotation.Laws.Count using (Cov; cov-up; cov-down; cov-stable; child; em; pick; under-guard)
open import denotation.Laws.Modulus using (ticks; ≼-split)

------------------------------------------------------------------------
-- Prefixes

-- Every position `y` extends.
pres : Pos → List Pos
pres []      = [] ∷ []
pres (a ∷ y) = [] ∷ L.map (a ∷_) (pres y)

⊑-pres : ∀ {k y} → k ⊑ y → k ∈ pres y
⊑-pres {[]}    {[]}    _ = here refl
⊑-pres {[]}    {a ∷ y} _ = here refl
⊑-pres {a ∷ k} {[]}    (_ , ())
⊑-pres {a ∷ k} {b ∷ y} (zs , refl) = there (∈-map⁺ (a ∷_) (⊑-pres (zs , refl)))

-- What `v` or one of `ks` extends.
cover : Pos → List Pos → List Pos
cover v ks = pres v ++ L.concatMap pres ks

cov-∈ : ∀ {v ks k} → Cov v ks k → k ∈ cover v ks
cov-∈ (inj₁ kv) = ∈-++⁺ˡ (⊑-pres kv)
cov-∈ {v} {ks} {k} (inj₂ a) = ∈-++⁺ʳ (pres v) (go a)
  where
    go : ∀ {ks} → Any (k ⊑_) ks → k ∈ L.concatMap pres ks
    go (here kx)             = ∈-++⁺ˡ (⊑-pres kx)
    go {x ∷ ks} (there a′)   = ∈-++⁺ʳ (pres x) (go a′)

∈-stable : ∀ {k : Pos} {ks} → ¬ ¬ (k ∈ ks) → k ∈ ks
∈-stable {k} {ks} = decidable-stable (any? (k ≟ᵖ_) ks)

lead-∈ : ∀ {r c : Pos} {cs} → r ⊑ c → c ∈ cs → Any (r ⊑_) cs
lead-∈ rc (here refl) = here rc
lead-∈ rc (there m)   = there (lead-∈ rc m)


------------------------------------------------------------------------
-- Few

-- Position by position, up to double negation.
_⊆ᵖ_ : ∀ {A B} → EmissionSet A → EmissionSet B → Set
_⊆ᵖ_ {B = B} Y X = ∀ {q e} → Y q e → ¬ ¬ Σ (Ev B) (X q)

few-via : ∀ {A B} {Y : EmissionSet A} {Z : EmissionSet B} {v} → (∀ {y e} → Y y e → y ≺ v → ¬ ¬ Σ (Ev B) (Z y)) → Few Z v → Few Y v
few-via s (ks , h) = ks , λ y lt → ∈-stable λ ¬i → s y lt λ { (_ , z) → ¬i (h z lt) }

few-sub : ∀ {A B} {Y : EmissionSet A} {X : EmissionSet B} {v} → Y ⊆ᵖ X → Few X v → Few Y v
few-sub s = few-via λ y _ → s y

few-down : ∀ {A} {X : EmissionSet A} {v w} → Few X v → w ≼ v → Few X w
few-down {v = v} {w} (ks , h) wv = ks , λ {k} x kw → h x (≺-≼-≺ {k} {w} {v} kw wv)

-- Every row before `v` covered there: few.
cov-few : ∀ {A} {X : EmissionSet A} {v ks} → (∀ {q e} → X q e → q ≺ v → Cov v ks q) → Few X v
cov-few {v = v} {ks} h = cover v ks , λ x lt → cov-∈ (h x lt)

-- Few before `v` in both parts: few in the whole.
few-∪ : ∀ {A B C} {Y : EmissionSet C} {X : EmissionSet A} {Z : EmissionSet B} {v}
      → (∀ {q e} → Y q e → ¬ ¬ (Σ (Ev A) (X q) ⊎ Σ (Ev B) (Z q))) → Few X v → Few Z v → Few Y v
few-∪ c (la , ha) (lb , hb) = la ++ lb , λ y lt → ∈-stable λ ¬i → c y λ
  { (inj₁ (_ , x)) → ¬i (∈-++⁺ˡ (ha x lt))
  ; (inj₂ (_ , z)) → ¬i (∈-++⁺ʳ la (hb z lt)) }

------------------------------------------------------------------------
-- Showing within a bound

-- The rows few before `v`, covered there by at most `n` positions.
FC : ∀ {A} → ℕ → EmissionSet A → Pos → Set
FC n X v = Σ (List Pos) λ ks → length ks ≤ n × (∀ {q e} → X q e → Few X q → q ≺ v → Cov v ks q)

ShowsK : ∀ {A} → ℕ → EmissionSet A → Set
ShowsK n X = ∀ {v} → FC n X v → ¬ ¬ Few X v

shows-k : ∀ {A n} {X : EmissionSet A} → Shows X → ShowsK n X
shows-k sh {v} (ks , _ , h) = sh (cover v ks , λ x f lt → cov-∈ (h x f lt))

k-shows : ∀ {A} {X : EmissionSet A} → (∀ n → ShowsK n X) → Shows X
k-shows sk (ks , h) = sk (length ks) (ks , ≤-refl , λ x f lt → inj₂ (Any.map (λ { refl → ⊑-refl _ }) (h x f lt)))

-- Every row few.
sk-few : ∀ {A n} {X : EmissionSet A} → (∀ {q e} → X q e → Few X q) → ShowsK n X
sk-few f (ks , _ , h) ¬f = ¬f (cov-few λ x lt → h x (f x) lt)

-- A part keeping every row few in the whole.
sk-closed : ∀ {A B n} {Y : EmissionSet A} {X : EmissionSet B} → Y ⊆ᵖ X → (∀ {q e} → X q e → Few X q → ¬ ¬ Σ (Ev A) (Y q))
          → ShowsK n X → ShowsK n Y
sk-closed s back sk (ks , le , h) ¬f =
  sk (ks , le , λ x f lt → cov-stable λ ¬c → back x f λ { (_ , y) → ¬c (h y (few-sub s f) lt) }) λ fx → ¬f (few-sub s fx)

-- The same positions.
sk-same : ∀ {A B n} {Y : EmissionSet A} {X : EmissionSet B} → Y ⊆ᵖ X → X ⊆ᵖ Y → ShowsK n X → ShowsK n Y
sk-same s s′ = sk-closed s λ x _ → s′ x

-- A part closed downward.
sk-down : ∀ {A B n} {Y : EmissionSet A} {X : EmissionSet B} → Y ⊆ᵖ X
        → (∀ {q e k e′} → Y q e → X k e′ → k ≺ q → ¬ ¬ Σ (Ev A) (Y k)) → ShowsK n X → ShowsK n Y
sk-down {Y = Y} s dn sk {v} (ks , le , h) ¬f = ¬f (cov-few cv)
  where
    cv : ∀ {q e} → Y q e → q ≺ v → Cov v ks q
    cv {q} y qv = cov-stable λ ¬c → sk (ks , le , λ {k} x f kq → cov-stable λ ¬c′ → dn y x kq λ
                    { (_ , y′) → ¬c′ (cov-down (h y′ (few-sub s f) (≺-trans {k} {q} {v} kq qv)) kq (≺→≼ {q} {v} qv)) })
                  λ fx → ¬c (h y (few-sub s fx) qv)

-- A union.
sk-∪ : ∀ {A B C n} {Y : EmissionSet C} {X : EmissionSet A} {Z : EmissionSet B} → X ⊆ᵖ Y → Z ⊆ᵖ Y
     → (∀ {q e} → Y q e → ¬ ¬ (Σ (Ev A) (X q) ⊎ Σ (Ev B) (Z q))) → ShowsK n X → ShowsK n Z → ShowsK n Y
sk-∪ {X = X} {Z} sx sz c skx skz {v} (ks , le , h) ¬f = skx (ks , le , fx) λ fxv → skz (ks , le , fz fxv) λ fzv → ¬f (few-∪ c fxv fzv)
  where
    fx : ∀ {q e} → X q e → Few X q → q ≺ v → Cov v ks q
    fx {q} x f qv = cov-stable λ ¬c →
      skz (ks , le , λ {k} z g kq → cov-stable λ ¬c′ → sz z λ
            { (_ , y) → ¬c′ (cov-down (h y (few-∪ c (few-down f (≺→≼ {k} {q} kq)) g) (≺-trans {k} {q} {v} kq qv)) kq (≺→≼ {q} {v} qv)) })
          λ fz → sx x λ { (_ , y) → ¬c (h y (few-∪ c f fz) qv) }

    fz : Few X v → ∀ {q e} → Z q e → Few Z q → q ≺ v → Cov v ks q
    fz fxv {q} z g qv = cov-stable λ ¬c → sz z λ { (_ , y) → ¬c (h y (few-∪ c (few-down fxv (≺→≼ {q} {v} qv)) g) qv) }

-- The rows of the parts named in a list.
U : ∀ {I : Set} {B} → (I → EmissionSet B) → List I → EmissionSet B
U C R q e = Any (λ i → C i q e) R

sk-U : ∀ {I : Set} {B n} (C : I → EmissionSet B) (R : List I) → (∀ {i} → i ∈ R → ShowsK n (C i)) → ShowsK n (U C R)
sk-U C []      sk = sk-few λ ()
sk-U C (i ∷ R) sk = sk-∪ (λ x ¬u → ¬u (_ , here x)) (λ x ¬u → ¬u (_ , there x))
                         (λ { (here x) ¬c → ¬c (inj₁ (_ , x)) ; (there x) ¬c → ¬c (inj₂ (_ , x)) })
                         (sk (here refl)) (sk-U C R λ m → sk (there m))

------------------------------------------------------------------------
-- Pins kept past a cut

-- Each a pin of a reached `X`, its connect at or before every cut and
-- led by one, a cut with few cuts before it.
sk-left : ∀ {A n} {X K : EmissionSet A} (Bad : Pos → Set)
        → (∀ {c} → Bad c → Σ (List Pos) λ L → ∀ {c′} → Bad c′ → c′ ≺ c → c′ ∈ L)
        → (∀ {k e} → K k e → X k e)
        → (∀ {k e} → K k e → Σ Pos λ r → e ≡ pin r × Reach X k (pin r) × (∀ {c} → Bad c → r ≼ c) × ¬ ¬ (Σ Pos λ c → Bad c × r ⊑ c))
        → ShowsK n K
sk-left {A} {n} {X} {K} Bad few-bad sub tgt {v} fc = em yes no
  where
    no : ¬ (Σ Pos Bad) → ¬ ¬ Few K v
    no nb ¬f = ¬f ([] , λ x _ → ⊥-elim (proj₂ (proj₂ (proj₂ (proj₂ (tgt x)))) λ { (c , b , _) → nb (c , b) }))

    -- The pins of one connect.
    Kr : Pos → EmissionSet A
    Kr r k e = K k e × e ≡ pin r

    few-r : ∀ {r k e} → Kr r k e → Few (Kr r) k
    few-r (x , refl) with tgt x
    ... | _ , refl , (ks , h) , _ = ks , λ { (x′ , refl) lt → h (sub x′) lt (λ _ → inj₂ refl) }

    yes : Σ Pos Bad → ¬ ¬ Few K v
    yes (c* , b*) = sk-same to back (sk-U Kr R λ _ → sk-few few-r) fc
      where
        Lb = proj₁ (few-bad b*)
        R  = cover c* Lb

        to : K ⊆ᵖ U Kr R
        to {k} {e} x ¬u with tgt x
        ... | r , refl , _ , early , led = led λ { (c , b , rc) → ¬u (_ , Any.map (λ { refl → x , refl }) (cov-∈ (place c b rc))) }
          where
            place : ∀ c → Bad c → r ⊑ c → Cov c* Lb r
            place c b rc with ≼-or-≻ c c*
            ... | inj₂ c*c = inj₁ (conv (⊑-refl r) (early b*) c*c rc)
            ... | inj₁ cc* with ≼-split {c} {c*} cc*
            ...   | inj₁ lt   = inj₂ (lead-∈ rc (proj₂ (few-bad b*) b lt))
            ...   | inj₂ refl = inj₁ rc

        back : U Kr R ⊆ᵖ K
        back u ¬k = ¬k (_ , proj₁ (proj₂ (Any.satisfied u)))

------------------------------------------------------------------------
-- A fan

-- A trunk `O` and branches, each past its root `s` and rooted at the trunk
-- row `s ⊕ [ ix 0 ]`: a reader few rows into the trunk meets few branches.
sk-fan : ∀ {B n} {Y O : EmissionSet B} (Br : Pos → EmissionSet B)
       → O ⊆ᵖ Y → (∀ {s} → Br s ⊆ᵖ Y)
       → (∀ {q e} → Y q e → ¬ ¬ (Σ (Ev B) (O q) ⊎ Σ Pos λ s → Σ (Ev B) (Br s q)))
       → (∀ {s y e} → Br s y e → s ≺ y × Σ (Ev B) (O (s ⊕ [ ix 0 ])))
       → ShowsK n O → (∀ s → ShowsK n (Br s)) → ShowsK n Y
sk-fan {B} {n} {Y} {O} Br so sb c root sko skb {v} (ks , le , h) ¬f =
  sko (ks , le , λ {w} x f wv → cov-stable λ ¬c → reach f (≺→≼ {w} {v} wv) λ fy → so x λ { (_ , y) → ¬c (h y fy wv) })
      λ fo → reach fo (≼-refl {v}) ¬f
  where
    C : Maybe Pos → EmissionSet B
    C nothing  = O
    C (just s) = Br s

    reach : ∀ {u} → Few O u → u ≼ v → ¬ ¬ Few Y u
    reach {u} (os , ho) uv ¬f′ = sk-U C R′ skC (ks , le , fz) λ fz′ → ¬f′ (few-via inZ fz′)
      where
        R′ = nothing ∷ L.map just (cover u os)

        skC : ∀ {i} → i ∈ R′ → ShowsK n (C i)
        skC {nothing} _ = sko
        skC {just s}  _ = skb s

        Z = U C R′

        inZ : ∀ {y e} → Y y e → y ≺ u → ¬ ¬ Σ (Ev B) (Z y)
        inZ {y} yr yu ¬z = c yr λ
          { (inj₁ (_ , x))     → ¬z (_ , here x)
          ; (inj₂ (s , _ , b)) → ¬z (_ , there (map⁺ (Any.map (λ { refl → b }) (at s (≺-trans {s} {y} {u} (proj₁ (root b)) yu) (proj₂ (proj₂ (root b))))))) }
          where
            at : ∀ s → s ≺ u → ∀ {e′} → O (s ⊕ [ ix 0 ]) e′ → s ∈ cover u os
            at s su o₀ with child {s} {u} (ix 0) su
            ... | inj₁ su′ = cov-∈ {u} {os} (inj₁ su′)
            ... | inj₂ lt  = cov-∈ {u} {os} (inj₂ (lead-∈ ([ ix 0 ] , refl) (ho o₀ lt)))

        zY : Z ⊆ᵖ Y
        zY u′ with Any.satisfied u′
        ... | nothing , x = so x
        ... | just s  , x = sb x

        fz : ∀ {z e} → Z z e → Few Z z → z ≺ u → Cov u ks z
        fz {z} zr f zu = cov-stable λ ¬c → zY zr λ
          { (_ , y) → ¬c (cov-down (h y (few-via (λ {y′} y′r lt → inZ y′r (≺-trans {y′} {z} {u} lt zu)) f) (≺-≼-≺ {z} {u} {v} zu uv)) zu uv) }

------------------------------------------------------------------------
-- One step down

-- `y` is `z`, or its first child.
Step : Pos → Pos → Set
Step z y = y ≡ z ⊎ y ≡ z ⊕ [ ix 0 ]

step-⊑ : ∀ {z y} → Step z y → z ⊑ y
step-⊑ {z} (inj₁ refl) = ⊑-refl z
step-⊑     (inj₂ refl) = [ ix 0 ] , refl

-- Nothing lies between a position and its first child.
step-order : ∀ {z y z′ y′} → Step z y → Step z′ y′ → y′ ≺ y → z′ ≼ z
step-order {z} {y} {z′} {y′} st st′ lt zz′ with st
... | inj₁ refl = ≺-absurd {z} {z′} zz′ (≼-≺-≺ {z′} {y′} {z} (⊑-≼ (step-⊑ st′)) lt)
... | inj₂ refl = subst T (<ᵖ-step z z′ (Equivalence.to T-≡ zz′)) (≼-≺-≺ {z′} {y′} {z ⊕ [ ix 0 ]} (⊑-≼ (step-⊑ st′)) lt)

steps : List Pos → List Pos
steps = L.concatMap λ z → z ∷ (z ⊕ [ ix 0 ]) ∷ []

step-∈ : ∀ {z y zs} → Step z y → z ∈ zs → y ∈ steps zs
step-∈ (inj₁ refl) (here refl) = here refl
step-∈ (inj₂ refl) (here refl) = there (here refl)
step-∈ {zs = z′ ∷ zs} st (there m) = ∈-++⁺ʳ (z′ ∷ (z′ ⊕ [ ix 0 ]) ∷ []) (step-∈ st m)

-- Each row moved at most one step down.
sk-step : ∀ {A B n} {Y : EmissionSet A} {X : EmissionSet B}
        → (∀ {y e} → Y y e → ¬ ¬ Σ Pos λ z → Σ (Ev B) (X z) × Step z y)
        → (∀ {z e} → X z e → ¬ ¬ Σ Pos λ y → Σ (Ev A) (Y y) × Step z y)
        → ShowsK n X → ShowsK n Y
sk-step {Y = Y} {X} pre img sk {v} (ks , le , h) ¬f = sk (ks , le , fx) λ fxv → ¬f (fv fxv)
  where
    at : ∀ {z y} → Few X z → Step z y → Few Y y
    at {z} {y} (zs , hz) st = steps (z ∷ zs) , λ {y′} y′r lt → ∈-stable λ ¬i → pre y′r λ
      { (z′ , (_ , x′) , st′) → ¬i (step-∈ st′ (pl x′ (≼-split (step-order st st′ lt)))) }
      where
        pl : ∀ {z′ e′} → X z′ e′ → z′ ≺ z ⊎ z′ ≡ z → z′ ∈ z ∷ zs
        pl x′ (inj₁ lt′)  = there (hz x′ lt′)
        pl x′ (inj₂ refl) = here refl

    fx : ∀ {z e} → X z e → Few X z → z ≺ v → Cov v ks z
    fx {z} x f zv = cov-stable λ ¬c → img x λ { (y , (_ , yr) , st) → ¬c (go yr f st) }
      where
        go : ∀ {y e′} → Y y e′ → Few X z → Step z y → Cov v ks z
        go yr f st with child {z} {v} (ix 0) zv
        ... | inj₁ zv′ = inj₁ zv′
        ... | inj₂ lt with st
        ...   | inj₁ refl = h yr (at f st) zv
        ...   | inj₂ refl = cov-up (step-⊑ st) (h yr (at f st) lt)

    fv : Few X v → Few Y v
    fv (zs , hz) = steps zs , λ {y′} y′r lt → ∈-stable λ ¬i → pre y′r λ
      { (z′ , (_ , x′) , st′) → ¬i (step-∈ st′ (hz x′ (≼-≺-≺ {z′} {y′} {v} (⊑-≼ (step-⊑ st′)) lt))) }

------------------------------------------------------------------------
-- Truncation

few-reach : ∀ {A} {t : EmissionSet A} {q e} → Few t q → Reach t q e
few-reach (ks , h) = ks , λ x lt _ → h x lt

sk-trunc : ∀ {A n} {t : EmissionSet A} → ShowsK n t → ShowsK n (Truncate t)
sk-trunc = sk-closed (λ x ¬t → ¬t (_ , proj₁ x)) λ x f ¬y → ¬y (_ , x , few-reach f)

------------------------------------------------------------------------
-- A defer's guard

-- The body's rows past its subscription: the guard spends one position.
module Guard {A : Set} (s : Den A) (p : Pos) (aft : ∀ {y e} → enter s (p ⊕ [ ix 1 ]) y e → (p ⊕ [ ix 1 ]) ≼ y) where
  g b₀ : Pos
  g  = p ⊕ [ ix 0 ]
  b₀ = p ⊕ [ ix 1 ]

  B : EmissionSet A
  B = enter s b₀

  D : EmissionSet A
  D = DeferT s p

  few-g : Few D g
  few-g = [] , λ { guard lt → ⊥-elim (≺-irrefl {g} lt)
                 ; (body {y} x) lt → ⊥-elim (aft x (≺-trans {y} {g} {b₀} lt (ticks p 0))) }

  few-at : ∀ {y} → Few B y → Few D y
  few-at (zs , hz) = g ∷ zs , λ { guard _ → here refl ; (body x′) lt → there (hz x′ lt) }

  bound : ∀ {n k k′} → k ≤ n → suc k′ ≡ k → Σ ℕ λ m → n ≡ suc m × k′ ≤ m
  bound (s≤s le) refl = _ , refl , le

  sk-guard : ∀ {n} → (∀ {m} → n ≡ suc m → ShowsK m B) → ShowsK n D
  sk-guard sk {v} (ks , le , h) ¬f with ≼-or-≻ v g
  ... | inj₁ vg = ¬f ([] , λ { guard lt → ⊥-elim (≺-irrefl {g} (≺-≼-≺ {g} {v} {g} lt vg))
                             ; (body {y} x) lt → ⊥-elim (aft x (≺-trans {y} {g} {b₀} (≺-≼-≺ {y} {v} {g} lt vg) (ticks p 0))) })
  ... | inj₂ gv with h guard few-g gv
  ...   | inj₁ gv′ = ¬f (g ∷ [] , λ { guard _ → here refl
                                    ; (body {y} x) lt → ⊥-elim (aft x (≺-trans {y} {v} {b₀} lt (under-guard p gv′))) })
  ...   | inj₂ a with pick a
  ...     | x , gx , ks′ , eq , sp with bound le eq
  ...       | m , refl , le′ = sk refl (ks′ , le′ , cv) λ f → ¬f (few-at f)
    where
      cv : ∀ {y e} → B y e → Few B y → y ≺ v → Cov v ks′ y
      cv {y} yr f yv with h (body yr) (few-at f) yv
      ... | inj₁ yv′ = inj₁ yv′
      ... | inj₂ a′ with sp a′
      ...   | inj₂ a″ = inj₂ a″
      ...   | inj₁ yx with ⊑-cmp y g yx gx
      ...     | inj₁ yg = ⊥-elim (aft yr (≼-≺-≺ {y} {g} {b₀} (⊑-≼ yg) (ticks p 0)))
      ...     | inj₂ gy = ⊥-elim (aft yr (under-guard p gy))
