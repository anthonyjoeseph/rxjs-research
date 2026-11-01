{-# OPTIONS --guardedness #-}

-- APART: every region a conf owes is separate from every other, the run
-- in progress included.  A step keeps it by refilling the subtree it
-- moves: the new regions inside what they replace, or a level down
-- inside the run.
module adequacy.Apart.Kit where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to all-map; head to all-head; zip to all-zip)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-sym; ↭-trans; ↭-reflexive)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∷↭∷ʳ; ++-comm) renaming (++⁺ˡ to ↭-++ˡ; ++⁺ʳ to ↭-++ʳ)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_; ⊆-reflexive; ⊆-refl)
open import Data.List.Relation.Binary.Sublist.Heterogeneous using (_∷ʳ_) renaming ([] to []ˢ)
open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)

open import denotation.Events using (Pos; Label; ix; last; tick; _<ᵖ_; <ᵖ-irrefl; ix-<)
open import operation.PureObservable using (module Machine; module Driver)
open Machine using (Ctx; St; Mode; Conf; ⟨_,_,_,_⟩; plug; subscribing; absorbed; rising; Stepped)
open import operation.Key using (at; after; _<ᴷ_; <ᴷ-irrefl; clash)
open import adequacy.Stamped using (Ix)
open import adequacy.Floor.Keys using (asym)
open import adequacy.Apart.Cone using (Cone; pre; cone-trans; cone-up; cone-apart; cone-after)
open import adequacy.Apart.Region using (Rg; cn; tl; pt; cl; In; Out; Sep; NoCl; Sub; Fut; Keyed; sub-cl; f-cn; f-tl; after-in; far-of)
open import adequacy.Apart.Items using (items; plug-items; lhs; rhs; hole; thin; no-cl; ap-++⁻)

------------------------------------------------------------------------
-- The invariant

-- The run in progress, while one is.
bI : ∀ {A} → Mode A → Pos → List Rg
bI absorbed    p = []
bI subscribing p = [ cl p ]
bI (rising _)  p = [ cl p ]

-- With the run's region `B`.
W : ∀ {R Γ A} → Ctx R Γ A → St Γ A → List Rg → Set
W c t B = AllPairs Sep (B ++ items (plug c t))

Apart : ∀ {R} → Conf R → Set
Apart ⟨ c , s , m , p ⟩ = W c s (bI m p)

------------------------------------------------------------------------
-- Moving a subtree

-- Fewer regions, nothing new.
fewer : ∀ {R Γ A} (c : Ctx R Γ A) {t t′ B B′} → B′ ⊆ B → items t′ ⊆ items t → W c t B → W c t′ B′
fewer c hb ht h = thin c hb ht h

-- The same regions, the run kept.
same : ∀ {R Γ A} (c : Ctx R Γ A) {t t′ B} → items t′ ≡ items t → W c t B → W c t′ B
same c e h = thin c (⊆-reflexive refl) (⊆-reflexive e) h

-- The run over.
drop : ∀ {R Γ A} (c : Ctx R Γ A) {t B} → W c t B → W c t []
drop c {B = B} h = proj₁ (proj₂ (ap-++⁻ B h))

-- New regions `Nn` for old `O`, the rest `X` kept, given what the new
-- owe each other and, from the old, what they owe the rest.
refill : ∀ {R Γ A} {P : Rg → Set} (c : Ctx R Γ A) {t t′} (B B′ O Nn X : List Rg)
       → items t ↭ O ++ X → items t′ ↭ Nn ++ X → All P (items (plug c t))
       → (∀ k → All (λ z → Sep z k) (B ++ O) → P k → All (λ n → Sep n k) (B′ ++ Nn))
       → AllPairs Sep (B′ ++ Nn) → W c t B → W c t′ B′
refill {P = P} c {t} {t′} B B′ O Nn X pT pT′ hp step hn h =
  subst (λ z → AllPairs Sep (B′ ++ z)) (sym (plug-items c t′))
    (hole B B′ O Nn X (lhs c) (rhs c) pT pT′ (subst (All P) (plug-items c t) hp) step hn
      (subst (λ z → AllPairs Sep (B ++ z)) (plug-items c t) h))

-- … with nothing asked of the rest but that it is no run.
refill₀ : ∀ {R Γ A} (c : Ctx R Γ A) {t t′} (B B′ O Nn X : List Rg)
        → items t ↭ O ++ X → items t′ ↭ Nn ++ X
        → (∀ k → All (λ z → Sep z k) (B ++ O) → NoCl k → All (λ n → Sep n k) (B′ ++ Nn))
        → AllPairs Sep (B′ ++ Nn) → W c t B → W c t′ B′
refill₀ c {t} B B′ O Nn X pT pT′ step hn h = refill c B B′ O Nn X pT pT′ (no-cl (plug c t)) step hn h

------------------------------------------------------------------------
-- Regions a step makes

private
  ne-of : ∀ {a b : Label} → [ a ] <ᵖ [ b ] ≡ true → a ≢ b
  ne-of {a} lt refl = clash lt (<ᵖ-irrefl [ a ])

-- Below a stamped position, its clock.
tick-ix : ∀ p q → Ix p → tick (p ++ q) ≡ tick p
tick-ix (ix _ ∷ _) q _ = refl

-- A later sibling's subtree is past the run in an earlier one.
far-sib : ∀ {p a b y} → Ix p → [ a ] <ᵖ [ b ] ≡ true → Cone (p ++ [ b ]) y
        → (at y <ᴷ after (p ++ [ a ]) ≡ false) × (Cone (p ++ [ a ]) y → ⊥)
far-sib {p} {a} {b} {y} hp ab c = asym (after (p ++ [ a ])) (at y) (cone-after hp ab c) , λ c′ → cone-apart hp (ne-of ab) c′ c

-- The run in a child, a later sibling's subtree owed.
cl-cn : ∀ {p a b} → Ix p → [ a ] <ᵖ [ b ] ≡ true → Sep (cl (p ++ [ a ])) (cn (p ++ [ b ]))
cl-cn hp ab = (λ y ()) , λ y c → far-sib hp ab c

-- The run in a value's subtree, the later values and the end owed.
cl-tl : ∀ {u i} → Ix u → Sep (cl (u ++ [ ix i ])) (tl u (suc i))
cl-tl hu = (λ y ()) , far
  where
    far : ∀ y → In (tl _ (suc _)) y → _
    far y (inj₁ (j , le , c)) = far-sib hu (ix-< le) c
    far y (inj₂ c)            = far-sib hu refl c

-- The run at a position, its after owed.
cl-pt : ∀ {q} → Sep (cl q) (pt q)
cl-pt {q} = (<ᴷ-irrefl (after q) , λ _ → refl) , (<ᴷ-irrefl (after q) , λ _ → refl)

-- The run a level down, the after above it owed.
cl-up : ∀ {p l} → Sep (cl (p ++ [ l ])) (pt p)
cl-up {p} {l} = out , out
  where
    out : Out (cl (p ++ [ l ])) p
    out = asym (after (p ++ [ l ])) (after p) (after-in p l []) , λ c → ⊥-elim (cone-up l [] c)

-- A child's subtree owed, the after above it owed.
cn-up : ∀ {p l} → Sep (cn (p ++ [ l ])) (pt p)
cn-up {p} {l} = (λ c → ⊥-elim (cone-up l [] c)) , λ y ()

-- A child's subtree, inside the run.
sub-child : ∀ {p} l → Ix p → Sub (cn (p ++ [ l ])) (cl p)
sub-child {p} l hp = sub-cl hp (f-cn _) (λ y c → cone-trans (pre [ l ]) c) (λ c → ⊥-elim (cone-up l [] c))

-- An of's or a cold's values, inside the run.
sub-vals : ∀ {p} i → Ix p → Sub (tl p i) (cl p)
sub-vals {p} i hp = sub-cl hp (f-tl p i) inc out
  where
    inc : ∀ y → In (tl p i) y → Cone p y
    inc y (inj₁ (j , _ , c)) = cone-trans (pre [ ix j ]) c
    inc y (inj₂ c)           = cone-trans (pre [ last ]) c
    out : In (tl p i) p → ⊥
    out (inj₁ (j , _ , c)) = cone-up (ix j) [] c
    out (inj₂ c)           = cone-up last [] c

------------------------------------------------------------------------
-- The shapes a step takes

-- A run's region, at most the run at its position.
bI-⊆ : ∀ {A} (m : Mode A) p → bI m p ⊆ [ cl p ]
bI-⊆ absorbed    p = cl p ∷ʳ []ˢ
bI-⊆ subscribing p = ⊆-refl
bI-⊆ (rising _)  p = ⊆-refl

none : ∀ (L : List Rg) → [] ⊆ L
none []      = []ˢ
none (y ∷ L) = y ∷ʳ none L

-- On at the run's position, owing no more.
stay : ∀ {R Γ A} (c : Ctx R Γ A) {t t′ p} (m : Mode A) → items t′ ⊆ items t → W c t [ cl p ] → W c t′ (bI m p)
stay c {p = p} m ht h = thin c (bI-⊆ m p) ht h

-- Absorbed, owing no more.
quit : ∀ {R Γ A} (c : Ctx R Γ A) {t t′ B} → items t′ ⊆ items t → W c t B → W c t′ []
quit c {B = B} ht h = thin c (none B) ht h

-- On from the run at `p`, every new region inside it.
grow : ∀ {R Γ A} (c : Ctx R Γ A) {t t′} p (B′ Nn O X : List Rg)
     → items t ↭ O ++ X → items t′ ↭ Nn ++ X
     → All (λ n → Sub n (cl p)) (B′ ++ Nn) → AllPairs Sep (B′ ++ Nn) → W c t [ cl p ] → W c t′ B′
grow c p B′ Nn O X pT pT′ subs hn h =
  refill₀ c [ cl p ] B′ O Nn X pT pT′ (λ k hk nc → all-map (λ s → s k nc (all-head hk)) subs) hn h

-- From rest, the least mark `R₀` run at `q`: the run opens there, the
-- rest of what it owed inside it.
fire : ∀ {R Γ A} (c : Ctx R Γ A) {t t′ q} (R₀ : Rg) (Nn X : List Rg) → Ix q → Fut R₀
     → (∀ y → Cone q y → In R₀ y) → (∀ y → Out R₀ y → Cone q y → y ≡ q)
     → items t ↭ R₀ ∷ X → items t′ ↭ Nn ++ X → All (Keyed (at q)) (items (plug c t))
     → All (λ n → Sub n R₀) Nn → AllPairs Sep (cl q ∷ Nn) → W c t [] → W c t′ [ cl q ]
fire c {t} {q = q} R₀ Nn X hq f₀ inc oq pT pT′ kd subs hn h =
  refill {P = λ k → NoCl k × Keyed (at q) k} c [] [ cl q ] [ R₀ ] Nn X pT pT′ (all-zip (no-cl (plug c t) , kd)) step hn h
  where
    step : ∀ k → All (λ z → Sep z k) [ R₀ ] → NoCl k × Keyed (at q) k → All (λ n → Sep n k) (cl q ∷ Nn)
    step k (h₀ ∷ []) (nc , kk) = far-of hq f₀ inc oq k nc kk h₀ ∷ all-map (λ s → s k nc h₀) subs

-- … the run's mode read.
fire′ : ∀ {R Γ A} (c : Ctx R Γ A) {t t′ q} (m : Mode A) (R₀ : Rg) (Nn X : List Rg) → Ix q → Fut R₀
      → (∀ y → Cone q y → In R₀ y) → (∀ y → Out R₀ y → Cone q y → y ≡ q)
      → items t ↭ R₀ ∷ X → items t′ ↭ Nn ++ X → All (Keyed (at q)) (items (plug c t))
      → All (λ n → Sub n R₀) Nn → AllPairs Sep (cl q ∷ Nn) → W c t [] → W c t′ (bI m q)
fire′ c {t} {t′} {q} m R₀ Nn X hq f₀ inc oq pT pT′ kd subs hn h =
  thin c {t = t′} {t′ = t′} (bI-⊆ m q) ⊆-refl (fire c {t} {t′} R₀ Nn X hq f₀ inc oq pT pT′ kd subs hn h)

------------------------------------------------------------------------
-- Moving regions in a list

-- One at the end, to the front.
to-front : ∀ (L : List Rg) v → L ++ [ v ] ↭ v ∷ L
to-front L v = ↭-sym (∷↭∷ʳ v L)

-- A middle part, to the front.
pull : ∀ (L M N : List Rg) → L ++ M ++ N ↭ M ++ L ++ N
pull L M N = ↭-trans (↭-reflexive (sym (++-assoc L M N))) (↭-trans (↭-++ʳ N (++-comm L M)) (↭-reflexive (++-assoc M L N)))

------------------------------------------------------------------------
-- What a step hands on

module _ {R : Set} where
  open Driver R using (Step; silent; value; complete; drained; took)

  -- Wherever a step lands.
  Next : Step → Set
  Next (silent _ k)    = Apart k
  Next (value _ _ _ k) = Apart k
  Next (complete _)    = ⊤
  Next drained         = ⊤

  AS : Stepped R → Set
  AS x = Next (took x)
