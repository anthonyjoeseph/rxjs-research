-- ROWS A TABLE HOLDS, READ OFF HOW IT IS LISTED: a lane's value among a
-- merge's rows, a hot's row its `proper` keeps, a row a rejoin shows, an
-- `of`'s value past its subscription; and the order of positions that
-- part at one label.
module simultaneous.TableRows where

open import Data.Bool using (true; T)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Data.List using (List; []; _∷_; [_]; length)
open import Data.Nat using (suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ; ∈-map⁺; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import denotation.Position using (Pos; ix; sub; last; _<ˡ_; _<ᵖ_; _⊕_)
open import denotation.Events using (<ᵖ-part; ofᴱ)
open import denotation.EmissionSet using (Ev; out; end; skip; pin; _≺_; _≼_)
open import denotation.Laws.Modulus using (≺-ext)
open import denotation.Laws.Worlds using (⊕-assoc; ⊕-identityʳ)
open import quickcheck.Tabled using (Row; Listed; _⊣_; rows; bind; lanes; mergeRows; proper; properAt; ends; allᵇ; _≼ᵇ_; rejoin; rejoinRow; pastRows)
open import quickcheck.Tabled.Exact.Base using (cm⁺; cm⁻; when⁺; when⁻; if⁻; offT; all⁺; T-not; ends⁻; mapM⁺; fromT; pastRows⁺)
open import simultaneous.Listing using (walkN)
open import simultaneous.TableEnv using (_⊕ˡ_)

------------------------------------------------------------------------
-- Positions

toT : ∀ {b} → b ≡ true → T b
toT refl = tt

⊕ˡ-⊕ : ∀ q ls → q ⊕ˡ ls ≡ q ⊕ ls
⊕ˡ-⊕ q []       = sym (⊕-identityʳ q)
⊕ˡ-⊕ q (l ∷ ls) = trans (⊕ˡ-⊕ (q ⊕ [ l ]) ls) (⊕-assoc q [ l ] ls)

-- Two positions parting at one label, ordered by it.
part-≺ : ∀ p {a b} ys zs → a <ˡ b ≡ true → (p ⊕ˡ (a ∷ ys)) ≺ (p ⊕ˡ (b ∷ zs))
part-≺ p {a} {b} ys zs h =
  subst (λ y → (p ⊕ˡ (a ∷ ys)) ≺ y) (sym (⊕ˡ-⊕ p (b ∷ zs)))
    (subst (λ x → x ≺ (p ⊕ (b ∷ zs))) (sym (⊕ˡ-⊕ p (a ∷ ys))) (toT (<ᵖ-part p ys zs h)))

------------------------------------------------------------------------
-- Rows

-- A value of a lane a merge runs is a value of the merge.
merge-lane-out : ∀ {A B : Set} (o : Listed A) (ls : List (Pos × A × Listed B)) {q a l k b}
               → (q , a , l) ∈ ls → (k , out b) ∈ rows l → (k , out b) ∈ rows (mergeRows o ls)
merge-lane-out o ls lm r = ∈-++⁺ʳ _ (cm⁺ lm (∈-map⁺ _ r))

-- A value's lane, listed at its subscription, is among the lanes.
lane-of : ∀ {A B : Set} {ln : A → Pos → Maybe (Listed B)} {vs ls} → lanes ln vs ≡ just ls
        → ∀ {q a l} → (q , a) ∈ vs → ln a (q ⊕ [ ix 1 ]) ≡ just l → (q , a , l) ∈ ls
lane-of {ln = ln} {vs = vs} e {q} {a} {l} vm el with mapM⁺ {xs = vs} e vm
... | (y , ym , fx) = subst (_∈ _) (just-injective (trans (sym fx) (cong (λ m → bind m λ l′ → just (q , a , l′)) el))) ym

-- A row at or before every end is kept by `proper`.
proper-in : ∀ {A} (rs : List (Row A)) {k e} → (k , e) ∈ rs → (∀ {c} → (c , end) ∈ rs → k ≼ c) → (k , e) ∈ proper rs
proper-in rs m h = cm⁺ m (when⁺ (all⁺ λ cm → T-not (h (ends⁻ cm))))

-- A value past a rejoin's subscription is shown under it.
rejoin-in : ∀ {A} p (l : Listed A) {k a} → (k , out a) ∈ rows l → p ≺ k → (k ⊕ [ sub p ] , out a) ∈ rows (rejoin p l)
rejoin-in p l m pk = cm⁺ m (when⁺ (fromT pk))

-- An `of` of one value lists it past its subscription.
of-past : ∀ {X : Set} s (xs : List X) {a} → xs ≡ a ∷ [] → (s ⊕ [ ix 0 ] , out a) ∈ pastRows s (walkN (suc (length xs)) (ofᴱ s 0 xs))
of-past s .(_ ∷ []) refl = pastRows⁺ {s = s} (walkN 2 (ofᴱ s 0 (_ ∷ []))) (here refl) (≺-ext s {ix 0} [])

-- A hot's proper rows are among its rows.
proper⊆ : ∀ {X} es (rs : List (Row X)) {r} → r ∈ properAt es rs → r ∈ rs
proper⊆ es []             ()
proper⊆ es ((q , e) ∷ rs) m with ∈-++⁻ _ m
... | inj₂ h = there (proper⊆ es rs h)
... | inj₁ h with when⁻ {b = allᵇ (q ≼ᵇ_) es} {x = (q , e)} h
...   | (_ , refl) = here refl

-- A pin read as a skip.
unpin : ∀ {X : Set} → Ev X → Ev X
unpin (pin _) = skip
unpin e       = e

-- A REJOINED ROW: a hot row past the subscription one label down, a pin
-- as a skip; or the end, at the subscription's last, of a hot ended at
-- or before it.
RjRow : ∀ {X : Set} → Pos → Listed X → Pos → Ev X → Set
RjRow {X} q L k e = (Σ Pos λ h → Σ (Ev X) λ e₀ → (h , e₀) ∈ rows L × q ≺ h × k ≡ h ⊕ [ sub q ] × e ≡ unpin e₀)
                  ⊎ (Σ Pos λ h → (h , end) ∈ rows L × ¬ (q ≺ h) × k ≡ q ⊕ [ last ] × e ≡ end)

rejoin-inv : ∀ {X : Set} q (L : Listed X) {k e} → (k , e) ∈ rows (rejoin q L) → RjRow q L k e
rejoin-inv q (rs ⊣ _) m with cm⁻ {f = rejoinRow q} {xs = rs} m
... | ((h , out a) , hm , w) with when⁻ {b = q <ᵖ h} {x = (h ⊕ [ sub q ] , out a)} w
...   | (b , refl) = inj₁ (h , out a , hm , toT b , refl , refl)
rejoin-inv q (rs ⊣ _) m | ((h , skip) , hm , w) with when⁻ {b = q <ᵖ h} {x = (h ⊕ [ sub q ] , skip)} w
...   | (b , refl) = inj₁ (h , skip , hm , toT b , refl , refl)
rejoin-inv q (rs ⊣ _) m | ((h , pin r) , hm , w) with when⁻ {b = q <ᵖ h} {x = (h ⊕ [ sub q ] , skip)} w
...   | (b , refl) = inj₁ (h , pin r , hm , toT b , refl , refl)
rejoin-inv q (rs ⊣ _) m | ((h , end) , hm , w) with if⁻ {b = q <ᵖ h} w
...   | inj₁ (b , here refl) = inj₁ (h , end , hm , toT b , refl , refl)
...   | inj₁ (_ , there ())
...   | inj₂ (b , here refl) = inj₂ (h , hm , offT b , refl , refl)
...   | inj₂ (_ , there ())

-- A value a rejoin shows of a hot listed off one value: that value's row,
-- under the rejoin.
rejoin-one : ∀ {A} p h c {a : A} {s k b} → (k , out b) ∈ rows (rejoin p (proper ((h , out a) ∷ (c , end) ∷ []) ⊣ s)) → k ≡ h ⊕ [ sub p ]
rejoin-one p h c {a} {s} {k} {b} m with rejoin-inv p (proper ((h , out a) ∷ (c , end) ∷ []) ⊣ s) m
... | inj₁ (_ , _ , hm , _ , kk , eu) = one (proper⊆ (ends rs) rs hm) kk eu
  where
    rs = (h , out a) ∷ (c , end) ∷ []
    one : ∀ {h′ e₀} → (h′ , e₀) ∈ ((h , out a) ∷ (c , end) ∷ []) → k ≡ h′ ⊕ [ sub p ] → out b ≡ unpin e₀ → k ≡ h ⊕ [ sub p ]
    one (here refl)         kk _  = kk
    one (there (here refl)) _  ()
    one (there (there ()))
... | inj₂ (_ , _ , _ , _ , ())
