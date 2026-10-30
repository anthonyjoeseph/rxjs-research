{-# OPTIONS --guardedness #-}

-- A SEARCH UNDER BINDERS IT CANNOT SEE: a joiner's rows read its binder,
-- which no search below the binder's connect finds, so a find keys the
-- rows only up to a cap `C` — the rows past `C` owe it nothing.  Below
-- the cap the find is exact; past it, every row is.  A binder whose rows
-- lie past the cap, or whose joiners were all told its end, leaves the
-- search exact up to it.  At no binder the cap is free, so every cap at
-- once is the uncapped bound.
module adequacy.Cap where

open import Data.Bool using (true; false; T; if_then_else_; _∧_; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (lookup) renaming (_∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import denotation.Events using (Pos; ix; last; sub; _<ᵖ_; <ᵖ-below; <ᵖ-part)
open import denotation.EmissionSet using (EmissionSet; Ev; _≼_; enter; Rejoin; Proper; DenEnv; module Connecting)
open import operation.Key using (Key; at; after; _<ᴷ_; <ᴷ-irrefl; ≮ᴷ-trans; at-<ᵖ; clash)
open import operation.PureObservable using (module Machine)

open Machine using (St; Ctx; CS; cs; Cand; found; Out; still; shows; seek; own; ownBest; first; sourceT; shift; closed; outOf; same?;
                    connS; joinS; joinM; cp) renaming (Ev to Evᴹ)
open import adequacy.Rows using (toEv; Each; Hot; Inbox; _∪_; this; that; Closed; shut)
open import adequacy.Bound using (_⊑_; ⊑i; ⊑-refl; ⊑-trans; <→⊑; ≺→⊑; ext-⊑; shift-≮; raise-src; Above; After; From; Single;
  Empty; Bd; OK; OKL; Mk; Fed; Told; ToldL; ToldAt)

open _⊑_
open Bd

------------------------------------------------------------------------
-- Keys

irr : ∀ a → a <ᴷ a ≡ true → ⊥
irr a h = clash h (<ᴷ-irrefl a)

⊑-< : ∀ {a b} c → a ⊑ b → b <ᴷ c ≡ true → a <ᴷ c ≡ true
⊑-< {a} {b} c ab bc with a <ᴷ c in ac
... | true  = refl
... | false = ⊥-elim (clash bc (≮ᴷ-trans b a c (un ab) ac))

<-⊑ : ∀ a {b c} → a <ᴷ b ≡ true → b ⊑ c → a <ᴷ c ≡ true
<-⊑ a {b} {c} ab bc with a <ᴷ c in ac
... | true  = refl
... | false = ⊥-elim (clash ab (≮ᴷ-trans a c b ac (un bc)))

⊑-<⊑ : ∀ {a b} c → a ⊑ b → b <ᴷ c ≡ true → a ⊑ c
⊑-<⊑ {a} c ab bc = <→⊑ a c (⊑-< c ab bc)

≼→⊑ : ∀ {p q} → p ≼ q → at p ⊑ at q
≼→⊑ {p} {q} pq = ⊑i (trans (at-<ᵖ q p) (no (q <ᵖ p) refl))
  where
    no : ∀ b → q <ᵖ p ≡ b → q <ᵖ p ≡ false
    no true  e = ⊥-elim (pq (subst T (sym e) tt))
    no false e = e

-- Not before, as an order.
≮ : ∀ a b → b <ᴷ a ≡ false → a ⊑ b
≮ a b = ⊑i

-- Two keys, compared.
dec : ∀ a b → a <ᴷ b ≡ true ⊎ a <ᴷ b ≡ false
dec a b with a <ᴷ b
... | true  = inj₁ refl
... | false = inj₂ refl

-- Strictly under a position is strictly later.
ext-< : ∀ x l → at x <ᴷ at (x ++ [ l ]) ≡ true
ext-< x l = trans (at-<ᵖ x (x ++ [ l ])) (<ᵖ-below x [])

-- A source's event, raised as its connect reads it, before anything a
-- joiner hears of a row no earlier.
bind-past : ∀ v h x l → [ ix 0 ] <ᵖ [ l ] ≡ true → h ⊑ at x → (if v then h else shift h) <ᴷ at (x ++ [ l ]) ≡ true
bind-past true  h         x l lt u = ⊑-< (at (x ++ [ l ])) u (ext-< x l)
bind-past false (at p)    x l lt u = ⊑-< (at (x ++ [ l ])) (shift-≮ x (at p) u) (trans (at-<ᵖ (x ++ [ ix 0 ]) (x ++ [ l ])) (<ᵖ-part x [] [] lt))
bind-past false (after p) x l lt u = ⊑-< (at (x ++ [ l ])) u (ext-< x l)

-- A source's row, echoed just past it, no earlier than its raised event.
src-past : ∀ v h k → h ⊑ at k → (if v then h else shift h) ⊑ at (k ++ [ ix 0 ])
src-past true  h k u = ⊑-trans u (ext-⊑ k [ ix 0 ])
src-past false h k u = shift-≮ k h u

-- The earlier of two keys, the first on a tie.
meet : Key → Key → Key
meet a b = if a <ᴷ b then a else b

meet-ˡ : ∀ a b → meet a b ⊑ a
meet-ˡ a b with a <ᴷ b in ab
... | true  = ⊑-refl a
... | false = ⊑i ab

meet-ʳ : ∀ a b → meet a b ⊑ b
meet-ʳ a b with a <ᴷ b in ab
... | true  = <→⊑ a b ab
... | false = ⊑-refl b

meet-lo : ∀ a b → a <ᴷ b ≡ true → a ⊑ meet a b
meet-lo a b ab rewrite ab = ⊑-refl a

meet-hi : ∀ a b → b ⊑ a → b ⊑ meet a b
meet-hi a b ba with a <ᴷ b in ab
... | true  = ⊥-elim (clash ab (un ba))
... | false = ⊑-refl b

------------------------------------------------------------------------
-- A capped find

-- Its key past the cap.
Past : ∀ {R A} → Key → Maybe (Cand R A) → Set
Past C nothing            = ⊤
Past C (just (_ , K , _)) = C <ᴷ K ≡ true

-- Its key at or before the cap.
Before : ∀ {R A} → Key → Maybe (Cand R A) → Set
Before C nothing            = ⊥
Before C (just (_ , K , _)) = C <ᴷ K ≡ false

-- Past the cap, only that every row is; at or before it, exact.
OKᶜ : ∀ {R A} → Key → EmissionSet A → Maybe (Cand R A) → Set
OKᶜ C t y = (Past C y × After C t) ⊎ (Before C y × OK t y)

OKLᶜ : ∀ {R B} → Key → List (EmissionSet B) → Maybe (Cand R B) → Set
OKLᶜ C Ls y = (Past C y × Each (After C) Ls) ⊎ (Before C y × OKL Ls y)

each-map : ∀ {B} {P Q : EmissionSet B → Set} (Ls : List (EmissionSet B)) → (∀ {t} → P t → Q t) → Each P Ls → Each Q Ls
each-map []       f _        = tt
each-map (_ ∷ Ls) f (p , ps) = f p , each-map Ls f ps

-- Exact, a fortiori exact up to any cap.
ok-cap : ∀ {R A} C {t : EmissionSet A} (y : Maybe (Cand R A)) → OK t y → OKᶜ C t y
ok-cap C nothing            e = inj₁ (tt , λ {_} {_} r → ⊥-elim (e r))
ok-cap C (just (f , K , o)) b with C <ᴷ K in lt
... | true  = inj₁ (refl , λ r → <-⊑ C lt (from b r))
... | false = inj₂ (refl , b)

-- Exact up to every cap: exact.
uncap : ∀ {R A} {t : EmissionSet A} (y : Maybe (Cand R A)) → (∀ C → OKᶜ C t y) → OK t y
uncap nothing h {q} r with h (at q)
... | inj₁ (_ , a) = irr (at q) (a r)
... | inj₂ (() , _)
uncap (just (f , K , o)) h with h K
... | inj₁ (p , _) = ⊥-elim (irr K p)
... | inj₂ (_ , b) = b

uncapL : ∀ {R B} (Ls : List (EmissionSet B)) (y : Maybe (Cand R B)) → (∀ C → OKLᶜ C Ls y) → OKL Ls y
uncapL {R} Ls nothing h = none Ls (λ C → past C (h C))
  where
    past : ∀ C → OKLᶜ {R} C Ls nothing → Each (After C) Ls
    past C (inj₁ (_ , e)) = e
    past C (inj₂ (() , _))
    none : ∀ Ls′ → (∀ C → Each (After C) Ls′) → Each Empty Ls′
    none []        _ = tt
    none (_ ∷ Ls′) a = (λ {q} r → irr (at q) (proj₁ (a (at q)) r)) , none Ls′ (λ C → proj₂ (a C))
uncapL Ls (just (f , K , o)) h with h K
... | inj₁ (p , _) = ⊥-elim (irr K p)
... | inj₂ (_ , b) = b

-- An exact lemma, carried to a cap: past it, the parent's rows lie past it too.
lift-cap : ∀ {R A B} C {t : EmissionSet A} {u : EmissionSet B} (F : Maybe (Cand R A) → Maybe (Cand R B))
         → (∀ y → OK t y → OK u (F y)) → (∀ y → Past C y → After C t → OKᶜ C u (F y))
         → ∀ y → OKᶜ C t y → OKᶜ C u (F y)
lift-cap C F L A y (inj₁ (p , a)) = A y p a
lift-cap C F L A y (inj₂ (_ , b)) = ok-cap C (F y) (L y b)

-- A rise read off its child's rows, each at or past one of the child's.
cap-retag : ∀ {R A B} C {t : EmissionSet A} {u : EmissionSet B} (T′ : Key → Out A → Key × Out B) → (∀ h o → h ⊑ proj₁ (T′ h o))
          → (∀ {q e} → u q e → Σ Pos λ q′ → Σ (Ev A) λ e′ → t q′ e′ × at q′ ⊑ at q)
          → (∀ y → OK t y → OK u (Machine.retag T′ y)) → ∀ (y : Maybe (Cand R A)) → OKᶜ C t y → OKᶜ C u (Machine.retag T′ y)
cap-retag C {t} {u} T′ r below L = lift-cap C (Machine.retag T′) L A
  where
    up : After C t → After C u
    up a x = let (_ , _ , y , le) = below x in <-⊑ C (a y) le
    A : ∀ y → Past C y → After C t → OKᶜ C u (Machine.retag T′ y)
    A nothing            _ a = inj₁ (tt , up a)
    A (just (f , K , o)) p a = inj₁ (<-⊑ C p (r K o) , up a)

-- Fewer rows, the same find.
cap-sub : ∀ {R A} C {t u : EmissionSet A} → (∀ y → OK t y → OK u y) → (∀ {q e} → u q e → t q e)
        → ∀ (y : Maybe (Cand R A)) → OKᶜ C t y → OKᶜ C u y
cap-sub C L s = lift-cap C (λ y → y) L (λ y p a → inj₁ (p , λ r → a (s r)))

------------------------------------------------------------------------
-- Silent own marks

-- Finding nothing, or a mark showing nothing, no later than its key.
data Stills {R A} : Maybe (Cand R A) → Set₁ where
  none : Stills nothing
  one  : ∀ {f m κ h} → κ ⊑ h → Stills (just (found f m κ , h , still))

first-stills : ∀ {R A} (x y : Maybe (Cand R A)) → Stills x → Stills y → Stills (first x y)
first-stills _ _ none               sy = sy
first-stills _ _ (one kh)           none = one kh
first-stills _ _ (one {h = h} kh) (one {h = h′} kh′) with h′ <ᴷ h
... | true  = one kh′
... | false = one kh

-- A connect's own marks show nothing.
own-stills : ∀ {R Γ A X} (c : Ctx R Γ A) k (o : St Γ X) b ms → Stills (ownBest c (connS k o b) ms)
own-stills c k o b []             = none
own-stills c k o b ((m , κ) ∷ ms) = first-stills _ _ (one (⊑-refl κ)) (own-stills c k o b ms)

-- A silent mark first, or its child's on a strict win.
first-stillsᶜ : ∀ {R A} C {t : EmissionSet A} (x y : Maybe (Cand R A)) → Stills x → OKᶜ C t y → OKᶜ C t (first x y)
first-stillsᶜ C _ y none oy = oy
first-stillsᶜ C _ nothing (one {h = h} kh) (inj₁ (_ , a)) with C <ᴷ h in ch
... | true  = inj₁ (refl , a)
... | false = inj₂ (refl , record { from = λ {q} r → ⊑-<⊑ (at q) (≮ h C ch) (a r) ; mark = kh ; shown = λ () })
first-stillsᶜ C _ nothing (one kh) (inj₂ (() , _))
first-stillsᶜ C _ (just (g , K , o)) (one {h = h} kh) oy with K <ᴷ h in kl
... | true  = oy
... | false with C <ᴷ h in ch | oy
...   | true  | inj₁ (_ , a)  = inj₁ (refl , a)
...   | true  | inj₂ (_ , b)  = inj₁ (refl , λ r → <-⊑ C ch (⊑-trans (≮ h K kl) (from b r)))
...   | false | inj₁ (_ , a)  = inj₂ (refl , record { from = λ {q} r → ⊑-<⊑ (at q) (≮ h C ch) (a r) ; mark = kh ; shown = λ () })
...   | false | inj₂ (_ , b)  = inj₂ (refl , record { from = λ r → ⊑-trans (≮ h K kl) (from b r) ; mark = kh ; shown = λ () })

-- A silent mark no later than `K`.
data StillAt {R A} (K : Key) : Maybe (Cand R A) → Set₁ where
  still-at : ∀ {f m κ h} → κ ⊑ h → h ⊑ K → StillAt K (just (found f m κ , h , still))

first-at : ∀ {R A} {f m} K (x : Maybe (Cand R A)) → Stills x → StillAt K (first (just (found f m K , K , still)) x)
first-at K _ none             = still-at (⊑-refl K) (⊑-refl K)
first-at K _ (one {h = h} kh) with h <ᴷ K in lt
... | true  = still-at kh (<→⊑ h K lt)
... | false = still-at (⊑-refl K) (⊑-refl K)

------------------------------------------------------------------------
-- The lanes

lanes-firstᶜ : ∀ {R B} C {l : EmissionSet B} {Ls} (x y : Maybe (Cand R B)) → OKᶜ C l x → OKLᶜ C Ls y → OKLᶜ C (l ∷ Ls) (first x y)
lanes-firstᶜ C nothing y (inj₁ (_ , a)) (inj₁ (p , as)) = inj₁ (p , a , as)
lanes-firstᶜ C nothing (just (g , K , o)) (inj₁ (_ , a)) (inj₂ (kc , fy , my , sy)) =
  inj₂ (kc , ((λ {q} r → ⊑-<⊑ (at q) (≮ K C kc) (a r)) , fy) , my , λ eq → let (q , k , x) = sy eq in q , k , inj₂ x)
lanes-firstᶜ C nothing nothing _ (inj₂ (() , _))
lanes-firstᶜ C nothing _ (inj₂ (() , _)) _
lanes-firstᶜ C (just _) nothing _ (inj₂ (() , _))
lanes-firstᶜ C {Ls = Ls} (just (g , h , o)) nothing (inj₂ (hc , bx)) (inj₁ (_ , as)) =
  inj₂ (hc , (from bx , each-map Ls (λ a {q} {_} r → ⊑-<⊑ (at q) (≮ h C hc) (a r)) as) , mark bx , λ eq → let (q , k , r) = shown bx eq in q , k , inj₁ r)
lanes-firstᶜ C (just (g , h , o)) nothing (inj₁ (p , a)) (inj₁ (_ , as)) = inj₁ (p , a , as)
lanes-firstᶜ C {Ls = Ls} (just (g , h , o)) (just (g′ , K , o′)) ox oy with K <ᴷ h in lt | ox | oy
... | true  | inj₁ (_ , a)  | inj₁ (p , as) = inj₁ (p , a , as)
... | true  | inj₁ (_ , a)  | inj₂ (kc , fy , my , sy) =
  inj₂ (kc , ((λ {q} r → ⊑-<⊑ (at q) (≮ K C kc) (a r)) , fy) , my , λ eq → let (q , k , x) = sy eq in q , k , inj₂ x)
... | true  | inj₂ (hc , bx) | inj₁ (p , as) = ⊥-elim (irr C (<-⊑ C p (⊑-trans (<→⊑ K h lt) (≮ h C hc))))
... | true  | inj₂ (hc , bx) | inj₂ (kc , fy , my , sy) =
  inj₂ (kc , ((λ r → ⊑-trans (<→⊑ K h lt) (from bx r)) , fy) , my , λ eq → let (q , k , x) = sy eq in q , k , inj₂ x)
... | false | inj₁ (p , a)  | inj₁ (_ , as) = inj₁ (p , a , as)
... | false | inj₁ (p , a)  | inj₂ (kc , _) = ⊥-elim (irr C (<-⊑ C p (⊑-trans (≮ h K lt) (≮ K C kc))))
... | false | inj₂ (hc , bx) | inj₁ (_ , as) =
  inj₂ (hc , (from bx , each-map Ls (λ a {q} {_} r → ⊑-<⊑ (at q) (≮ h C hc) (a r)) as) , mark bx , λ eq → let (q , k , r) = shown bx eq in q , k , inj₁ r)
... | false | inj₂ (hc , bx) | inj₂ (kc , fy , my , sy) =
  inj₂ (hc , (from bx , each-map Ls (λ fr {_} {_} r → ⊑-trans (≮ h K lt) (fr r)) fy) , mark bx , λ eq → let (q , k , r) = shown bx eq in q , k , inj₁ r)

------------------------------------------------------------------------
-- The binders

-- A binder whose rows lie past `C`, wherever it is joined.
Air : ∀ {Γ X} → Key → DenEnv Γ → X ∈ Γ → Set
Air C ρ x = ∀ j → After C (enter (lookup ρ x) j)

-- Every binder in the air, or `P` of it.
Calm : ∀ {Γ} → Key → DenEnv Γ → (∀ {X} → X ∈ Γ → Set) → Set₁
Calm {Γ} C ρ P = ∀ {X} (x : X ∈ Γ) → Air C ρ x ⊎ P x

-- Every binder in the air, or every joiner of it under `s` told its end.
Quiet : ∀ {Γ A} → Key → DenEnv Γ → St Γ A → Set₁
Quiet C ρ s = Calm C ρ (λ x → Told x s)

QuietL : ∀ {Γ A} → Key → DenEnv Γ → List (St Γ A) → Set₁
QuietL C ρ ls = Calm C ρ (λ x → ToldL x ls)

calm-map : ∀ {Γ} {C} {ρ : DenEnv Γ} {P Q : ∀ {X} → X ∈ Γ → Set} → (∀ {X} (x : X ∈ Γ) → P x → Q x) → Calm C ρ P → Calm C ρ Q
calm-map f q x = map₂ (f x) (q x)

-- One event a row at every binder's every join.
EnvSingle : ∀ {Γ} → DenEnv Γ → Set₁
EnvSingle {Γ} ρ = ∀ {X} (x : X ∈ Γ) j → Single (enter (lookup ρ x) j)

by-closed : ∀ {P Q : Set} cl → (T cl → P) → (¬ T cl → Q) → Q ⊎ P
by-closed true  t _ = inj₂ (t tt)
by-closed false _ a = inj₁ (a (λ ()))

-- A connect's body's binders: its own past `C₂` unless the source closed
-- and every joiner was told; the rest as above it, `C₂` no later.
body-quiet : ∀ {Γ X A} {ρ : DenEnv Γ} {C C₂} {σ : EmissionSet X} k (o : St Γ X) (b : St (X ∷ Γ) A) → C₂ ⊑ C
           → Quiet C ρ (connS k o b) → (T (CS.closed k) → Told (here refl) b) → (¬ T (CS.closed k) → Air C₂ (Hot σ k ∷ᴬ ρ) (here refl))
           → Quiet C₂ (Hot σ k ∷ᴬ ρ) b
body-quiet k o b c₂ q tl air (here refl) = by-closed (CS.closed k) tl air
body-quiet k o b c₂ q tl air (there x) with q x
... | inj₁ a       = inj₁ (λ j {q} r → ⊑-< (at q) c₂ (a j r))
... | inj₂ (_ , t) = inj₂ t

-- An open source's rows, as its binder holds them.
bind-src : ∀ {A} {σ : EmissionSet A} {k} {D : Key → Set} → Above D σ → ¬ T (CS.closed k) → Above D (Proper (λ q e → σ q e ⊎ Closed k q e))
bind-src dσ nc (inj₁ s , _)        = dσ s
bind-src dσ nc (inj₂ (shut cl) , _) = ⊥-elim (nc cl)

-- A binder's rows past `C₂`: each a source's row heard past it, or its
-- end heard late, no earlier than a row `D` bounds.
bind-after : ∀ {A} (σ : EmissionSet A) k C₂ (D : Key → Set) → (∀ {a b} → D a → a ⊑ b → D b) → Above D σ
           → (∀ {x} l → [ ix 0 ] <ᵖ [ l ] ≡ true → D (at x) → C₂ <ᴷ at (x ++ [ l ]) ≡ true)
           → ¬ T (CS.closed k) → ∀ j → After C₂ (enter (Hot σ k) j)
bind-after σ k C₂ D up dσ ext nc j (Rejoin.shown x _ _ , _) = ext (sub j) refl (bind-src {σ = σ} {k = k} {D = D} dσ nc x)
bind-after σ k C₂ D up dσ ext nc j (Rejoin.heard x _ , _)   = ext (sub j) refl (bind-src {σ = σ} {k = k} {D = D} dσ nc x)
bind-after σ k C₂ D up dσ ext nc j (Rejoin.ended x _ , _)   = ext (sub j) refl (bind-src {σ = σ} {k = k} {D = D} dσ nc x)
bind-after σ k C₂ D up dσ ext nc j (Rejoin.late x cj , _)   = ext last refl (up (bind-src {σ = σ} {k = k} {D = D} dσ nc x) (≼→⊑ cj))

-- A connect's row: its body's, or a source row's just past it.
conn-rows : ∀ {A B} {p} {σ : EmissionSet A} {β : EmissionSet B} (X : Key → Set) → (∀ {k e} → σ k e → X (at (k ++ [ ix 0 ])))
          → ∀ {q e} → Connecting.ConnT p σ β q e → β q e ⊎ X (at q)
conn-rows X f (Connecting.body r)        = inj₁ r
conn-rows X f (Connecting.burst s _)     = inj₂ (f s)
conn-rows X f (Connecting.echo s _ _ _)  = inj₂ (f s)
conn-rows X f (Connecting.kept s _ _ _)  = inj₂ (f s)

------------------------------------------------------------------------
-- A silent mark against a body capped no later

-- `h` a silent mark's key, the body capped at `C₂`: no later than `C`,
-- `C` itself when `h` is past it, no earlier than `h` when `h` is not;
-- every other row past `C` or no earlier than `h`.
module Vs {R B : Set} (C C₂ h : Key) {T′ β : EmissionSet B}
          (c₂C : C₂ ⊑ C) (lo : C <ᴷ h ≡ true → C ⊑ C₂) (hi : h ⊑ C → h ⊑ C₂)
          (split : ∀ {q e} → T′ q e → β q e ⊎ (C <ᴷ at q ≡ true ⊎ h ⊑ at q))
          (inj : ∀ {q e} → β q e → T′ q e) where

  -- The body's rows past `C` when `h` is, no body find before `h`.
  β-after : C <ᴷ h ≡ true → ∀ (y : Maybe (Cand R B)) → (∀ {g K o} → y ≡ just (g , K , o) → h ⊑ K) → OKᶜ C₂ β y → After C β
  β-after ch _                  _  (inj₁ (_ , a)) {q} r = ⊑-< (at q) (lo ch) (a r)
  β-after ch nothing            _  (inj₂ (() , _)) r
  β-after ch (just (g , K , o)) aw (inj₂ (_ , b)) r = <-⊑ C ch (⊑-trans (aw refl) (from b r))

  -- No earlier than `h` when `h` is no later than `C`.
  β-from : h ⊑ C → ∀ (y : Maybe (Cand R B)) → (∀ {g K o} → y ≡ just (g , K , o) → h ⊑ K) → OKᶜ C₂ β y → From h β
  β-from hc _                  _  (inj₁ (_ , a)) {q} r = ⊑-<⊑ (at q) (hi hc) (a r)
  β-from hc nothing            _  (inj₂ (() , _)) r
  β-from hc (just (g , K , o)) aw (inj₂ (_ , b)) r = ⊑-trans (aw refl) (from b r)

  -- No body find wins strictly before `h`: the mark's.
  a-wins : ∀ {f m κ} (y : Maybe (Cand R B)) → κ ⊑ h → (∀ {g K o} → y ≡ just (g , K , o) → h ⊑ K) → OKᶜ C₂ β y
         → OKᶜ {R} C T′ (just (found f m κ , h , still))
  a-wins y kh aw by with dec C h
  ... | inj₁ ch = inj₁ (ch , λ r → [ β-after ch y aw by , [ (λ c → c) , <-⊑ C ch ]′ ]′ (split r))
  ... | inj₂ ch = inj₂ (ch , record { from = λ {q} r → [ β-from (≮ h C ch) y aw by , [ ⊑-<⊑ (at q) (≮ h C ch) , (λ hr → hr) ]′ ]′ (split r)
                                    ; mark = kh ; shown = λ () })

  -- A body find no later than `h`: the body's.
  y-wins : ∀ {g K o} → K ⊑ h → OKᶜ {R} C₂ β (just (g , K , o)) → OKᶜ C T′ (just (g , K , o))
  y-wins {K = K} kh (inj₁ (c₂K , a)) with dec C K
  ... | inj₁ cK = inj₁ (cK , λ {q} r → [ (λ x → ⊑-< (at q) (lo (<-⊑ C cK kh)) (a x)) , [ (λ c → c) , (λ hr → <-⊑ C cK (⊑-trans kh hr)) ]′ ]′ (split r))
  ... | inj₂ cK with dec C h
  ...   | inj₁ ch = ⊥-elim (irr C₂ (<-⊑ C₂ c₂K (⊑-trans (≮ K C cK) (lo ch))))
  ...   | inj₂ ch = ⊥-elim (irr C₂ (<-⊑ C₂ c₂K (⊑-trans kh (hi (≮ h C ch)))))
  y-wins {K = K} kh (inj₂ (kc₂ , b)) =
    inj₂ (un kC , record { from = λ {q} r → [ from b , [ ⊑-<⊑ (at q) kC , (λ hr → ⊑-trans kh hr) ]′ ]′ (split r)
                         ; mark = mark b ; shown = λ eq → let (q , k , r) = shown b eq in q , k , inj r })
    where
      kC : K ⊑ C
      kC = ⊑-trans (≮ K C₂ kc₂) c₂C

  -- The source's raised event against the body's, the body's on a tie.
  src-vs : ∀ {Y : Set} {f m κ h₀} {o : Out Y} v → h ≡ (if v then h₀ else shift h₀) → κ ⊑ h₀ → (y : Maybe (Cand R B)) → OKᶜ C₂ β y
         → OKᶜ {R} C T′ (sourceT v (just (found f m κ , h₀ , o)) y)
  src-vs {f = f} {m = m} {κ = κ} {h₀ = h₀} v eq kh nothing by =
    subst (λ z → OKᶜ {R} C T′ (just (found f m κ , z , still))) eq
      (a-wins {f} {m} {κ} nothing (subst (κ ⊑_) (sym eq) (⊑-trans kh (raise-src v h₀))) (λ ()) by)
  src-vs {f = f} {m = m} {κ = κ} {h₀ = h₀} v eq kh (just (g , K , o′)) by with (if v then h₀ else shift h₀) <ᴷ K in lt
  ... | true  = subst (λ z → OKᶜ {R} C T′ (just (found f m κ , z , still))) eq
                  (a-wins {f} {m} {κ} (just (g , K , o′)) (subst (κ ⊑_) (sym eq) (⊑-trans kh (raise-src v h₀)))
                          (λ { refl → <→⊑ h K (trans (cong (_<ᴷ K) eq) lt) }) by)
  ... | false = y-wins {g} {K} {o′} (≮ K h (trans (cong (_<ᴷ K) eq) lt)) by

  -- The connect's own mark against the body's, its own on a tie.
  own-vs : ∀ {f m κ} → κ ⊑ h → (y : Maybe (Cand R B)) → OKᶜ C₂ β y → OKᶜ {R} C T′ (first (just (found f m κ , h , still)) y)
  own-vs {f} {m} {κ} kh nothing by = a-wins {f} {m} {κ} nothing kh (λ ()) by
  own-vs {f} {m} {κ} kh (just (g , K , o′)) by with K <ᴷ h in lt
  ... | true  = y-wins {g} {K} {o′} (<→⊑ K h lt) by
  ... | false = a-wins {f} {m} {κ} (just (g , K , o′)) kh (λ { refl → ≮ h K lt }) by

------------------------------------------------------------------------
-- A connect

module _ {R B X : Set} {Γ} {ρ : DenEnv Γ} (k : CS) (σ : EmissionSet X) {β : EmissionSet B} where
  open Connecting (CS.connAt k) σ β using (ConnT; body)

  -- A body under binders past `C₂`, `C₂` no later than `C`.
  Body : Key → Maybe (Cand R B) → Set
  Body C y = ∀ C₂ → C₂ ⊑ C → (¬ T (CS.closed k) → Air C₂ (Hot σ k ∷ᴬ ρ) (here refl)) → OKᶜ C₂ β y

  -- Every other row past `C`: the body's find, uncapped.
  body-only : ∀ C (y : Maybe (Cand R B)) → (∀ {q e} → ConnT q e → β q e ⊎ C <ᴷ at q ≡ true) → OKᶜ C β y → OKᶜ C ConnT y
  body-only C y sp (inj₁ (p , a)) = inj₁ (p , λ r → [ a , (λ c → c) ]′ (sp r))
  body-only C nothing sp (inj₂ (() , _))
  body-only C (just (g , K , o)) sp (inj₂ (kc , b)) =
    inj₂ (kc , record { from = λ {q} r → [ from b , ⊑-<⊑ (at q) (≮ K C kc) ]′ (sp r)
                      ; mark = mark b ; shown = λ eq → let (q , e , r) = shown b eq in q , e , body r })

  -- Its source subscribed: the source's find raised against the body's,
  -- the body capped no later than the source's.
  conn-free : ∀ C v (x : Maybe (Cand R X)) (y : Maybe (Cand R B)) → OKᶜ C σ x → Mk x → Body C y → OKᶜ C ConnT (sourceT v x y)
  conn-free C v nothing y (inj₁ (_ , aσ)) _ bd =
    body-only C y (conn-rows (λ a → C <ᴷ a ≡ true) (λ {k′} s → <-⊑ C (aσ s) (ext-⊑ k′ [ ix 0 ])))
      (bd C (⊑-refl C) (λ nc → bind-after σ k C (λ a → C <ᴷ a ≡ true) (λ d e → <-⊑ C d e) aσ (λ {x} l _ c → <-⊑ C c (ext-⊑ x [ l ])) nc))
  conn-free C v nothing y (inj₂ (() , _)) _ bd
  conn-free C v (just (found f m κ , h₀ , o)) y (inj₁ (ch , aσ)) kh bd =
    Vs.src-vs C (meet C h) h (meet-ˡ C h) (meet-lo C h) (meet-hi C h)
      (conn-rows (λ a → C <ᴷ a ≡ true ⊎ h ⊑ a) (λ {k′} s → inj₁ (<-⊑ C (aσ s) (ext-⊑ k′ [ ix 0 ])))) body v refl kh y
      (bd (meet C h) (meet-ˡ C h)
          (λ nc → bind-after σ k (meet C h) (λ a → C <ᴷ a ≡ true) (λ d e → <-⊑ C d e) aσ (λ {x} l _ c → ⊑-< (at (x ++ [ l ])) (meet-ˡ C h) (<-⊑ C c (ext-⊑ x [ l ]))) nc))
    where
      h : Key
      h = if v then h₀ else shift h₀
  conn-free C v (just (found f m κ , h₀ , o)) y (inj₂ (_ , bσ)) kh bd =
    Vs.src-vs C (meet C h) h (meet-ˡ C h) (meet-lo C h) (meet-hi C h)
      (conn-rows (λ a → C <ᴷ a ≡ true ⊎ h ⊑ a) (λ {k′} s → inj₂ (src-past v h₀ k′ (from bσ s)))) body v refl kh y
      (bd (meet C h) (meet-ˡ C h)
          (λ nc → bind-after σ k (meet C h) (h₀ ⊑_) ⊑-trans (from bσ) (λ {x} l lt d → ⊑-< (at (x ++ [ l ])) (meet-ʳ C h) (bind-past v h₀ x l lt d)) nc))
    where
      h : Key
      h = if v then h₀ else shift h₀

  -- Its body subscribing, its source owing nothing before the body's
  -- `ix 1`: its own marks, the earliest no later than that, against the body's.
  conn-held : ∀ C q (x : Maybe (Cand R B)) (y : Maybe (Cand R B)) → From (at q) σ → StillAt (at q) x → Body C y → OKᶜ C ConnT (first x y)
  conn-held C q _ y fσ (still-at {h = h} kh hq) bd =
    Vs.own-vs C (meet C h) h (meet-ˡ C h) (meet-lo C h) (meet-hi C h)
      (conn-rows (λ a → C <ᴷ a ≡ true ⊎ h ⊑ a) (λ {k′} s → inj₂ (⊑-trans hq (⊑-trans (fσ s) (ext-⊑ k′ [ ix 0 ]))))) body kh y
      (bd (meet C h) (meet-ˡ C h)
          (λ nc → bind-after σ k (meet C h) (at q ⊑_) ⊑-trans fσ (λ {x} l _ d → ⊑-< (at (x ++ [ l ])) (⊑-trans (meet-ʳ C h) (⊑-trans hq d)) (ext-< x l)) nc))

------------------------------------------------------------------------
-- A joiner

same?-refl : ∀ {Γ : List Set} {X} (x : X ∈ Γ) → same? x x ≡ just refl
same?-refl (here refl) = refl
same?-refl (there x)   = same?-refl x

-- Told its end with nothing waiting: impossible.
told-nil : ∀ {Γ : List Set} {X} (x : X ∈ Γ) → ToldAt (same? x x) [] → ⊥
told-nil x t with subst (λ m → ToldAt m []) (same?-refl x) t
... | ()

-- Its inbox's head before every row it owes.
fed-from : ∀ {A} {q e ib} {t : EmissionSet A} → Fed ((q , e) ∷ ib) t → From (at q) (Inbox ((q , e) ∷ ib) ∪ t)
fed-from _            (inj₁ this)     = ⊑-refl _
fed-from (ib< , _ , _) (inj₁ (that x)) = ≺→⊑ (ib< x)
fed-from (_ , t< , _) (inj₂ r) with t< r
... | inj₁ lt         = ≺→⊑ lt
... | inj₂ (refl , _) = ⊑-refl _

-- A joiner's own mark, its inbox's head, shown while it reads.
join-head : ∀ {R Γ A} (c : Ctx R Γ A) j g (x : A ∈ Γ) q e ib {t : EmissionSet A} → Fed ((q , e) ∷ ib) t
          → OK (Inbox ((q , e) ∷ ib) ∪ t) (seek c (joinS j g x ((q , e) ∷ ib)))
join-head c j g x q e ib {t} fd = record { from = fed-from fd ; mark = ⊑-refl _ ; shown = sh g (closed c) }
  where
    sh : ∀ g′ cl {e′} → (if g′ ∧ not cl then shows e else still) ≡ shows e′ → Σ Pos λ q′ → at q ≡ at q′ × (Inbox ((q , e) ∷ ib) ∪ t) q′ (toEv e′)
    sh true  false refl = q , refl , inj₁ this
    sh true  true  ()
    sh false _     ()
