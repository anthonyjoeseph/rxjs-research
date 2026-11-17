-- ROWS A TABLE HOLDS, READ OFF HOW IT IS LISTED: a lane's value among a
-- merge's rows, a hot's row its `proper` keeps, a row a rejoin shows, an
-- `of`'s value past its subscription; and the order of positions that
-- part at one label.
module simultaneous.TableRows where

open import Data.Bool using (Bool; true; T)
open import Data.List using (List; []; _∷_; [_]; _++_; length)
open import Data.Nat using (suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe using (Maybe; just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import denotation.Position using (Pos; Label; ix; sub; _<ˡ_; _<ᵖ_; _⊕_; _∙_)
open import denotation.Events using (<ᵖ-part; Events; ofᴱ)
open import denotation.EmissionSet using (Ev; out; end; _≺_; _≼_)
open import denotation.Laws.Modulus using (≺-ext)
open import denotation.Laws.Worlds using (⊕-assoc)
open import quickcheck.Tabled using (Row; Listed; rows; _⊣_; bind; lanes; values; mergeRows; proper; rejoin; pastRows)
open import quickcheck.Tabled.Exact.Base using (cm⁺; when⁺; all⁺; T-not; ends⁻; mapM⁺; fromT; pastRows⁺)
open import simultaneous.Listing using (walkN)
open import simultaneous.TableEnv using (_⊕ˡ_)

------------------------------------------------------------------------
-- Positions

toT : ∀ {b} → b ≡ true → T b
toT refl = tt

⊕-[] : ∀ q → q ⊕ [] ≡ q
⊕-[] (i ∙ p) = cong (i ∙_) (++-identityʳ p)

⊕ˡ-⊕ : ∀ q ls → q ⊕ˡ ls ≡ q ⊕ ls
⊕ˡ-⊕ q []       = sym (⊕-[] q)
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
