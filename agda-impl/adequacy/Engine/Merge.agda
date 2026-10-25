{-# OPTIONS --guardedness #-}

-- A MERGE FED PARTS WITH SKIPS ERASED RUNS WITH SKIPS ERASED (`go-erase`).
-- Erasing only moves a part's next later, never earlier, so a kept part
-- the merge picks on the one side it picks on the other (`go-rise`,
-- `go-outer`), and an erased one it picks comes no later than anything
-- the other shows (`head-go`).  What the merge picks next is read off
-- the parts' heads alone, so parts with the same next give the same
-- next (`go-lead`); and the merge hushes only when every part has
-- (`go-hush`).
module adequacy.Engine.Merge where

open import Data.Bool using (true; false; _∧_) renaming (T to Holds)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
import Data.List as L
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺; ++⁻ʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _<ᵇ_; _+_; _≤_)
open import Data.Nat.Properties using (+-suc; +-assoc; ≤-pred; ≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import denotation.MonotonicList.Events using (Events; Events∞; Tail; pin; Pos; out; skip; end; hush; idle; _∪_; ix; _<ᵖ_; <ᵖ-irrefl; <ᵖ-trans)
open import denotation.MonotonicList using (MonotonicList; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; head; headᴼ; Earliest; none; found;
  earliest; clear; clears; ahead-of; cuts; cutᴼ; whole; admit; enter; go; parts; viaOuter;
  race; outer; lane; mapᴱ; agreeᵀ-refl)
open import denotation.NonExpansive using (∪-ne)
open import denotation.Unfold using (Node; NEnv; states; outerᴺ)
open import denotation.Denote using (flatOp)
open import adequacy.Engine.Meaning using (outerFrame; lanesFrame; outerOf; laneᴹ; lanesL; outerG; outerT; poolRuns; poolT; cuts-hole)
open import adequacy.Engine.Race using (After; NotBefore; TailNotBefore; First; first; go-rise; go-outer)
open import adequacy.Engine.Erase using (Eraseᵀ; Erase; Lead⁼; Eraseˢ; _,ᵉ_; cutᵉ; nowᵉ; _⊒_; stopᵉ; idleᵉ; pinᵉ; unpin; outᵉ; skipᵉ; erased; endᵉ;
  hushᵉ; outᴸ; skipᴸ; endᴸ; hushᴸ; eraseᵀ-agree; eraseˢ-refl; eraseᵀ-pred; eraseˢ-pred; lead-head; after-le; after-nb; below-on; nb-erase;
  after-erase; hushed-erase; tnb-erase; ∪-erase; map-erase; map-lead)
open Events∞

------------------------------------------------------------------------
-- Parts and their heads

Hushed : ∀ {B} → Events∞ B → Set
Hushed l = head (force l) ≡ nothing

NBₗ : ∀ {B} → Pos → Events∞ B → Set
NBₗ p l = NotBefore p (head (force l))

Afterₗ : ∀ {B} → Pos → Events∞ B → Set
Afterₗ p l = After p (head (force l))

private
  after-lt : ∀ {p q} h → p <ᵖ q ≡ true → After q h → After p h
  after-lt nothing   _ _ = tt
  after-lt {p} {q} (just h) x y = <ᵖ-trans p q h x y

  afters-nb : ∀ {B p} {ls : List (Events∞ B)} → All (Afterₗ p) ls → All (NBₗ p) ls
  afters-nb []                  = []
  afters-nb {ls = l ∷ _} (a ∷ as) = after-nb (head (force l)) a ∷ afters-nb as

  nbs-after : ∀ {B p q} {ls : List (Events∞ B)} → p <ᵖ q ≡ true → All (NBₗ q) ls → All (Afterₗ p) ls
  nbs-after lt []                  = []
  nbs-after {ls = l ∷ _} lt (n ∷ ns) = after-le (head (force l)) lt n ∷ nbs-after lt ns

  afters-lt : ∀ {B p q} {ls : List (Events∞ B)} → p <ᵖ q ≡ true → All (Afterₗ q) ls → All (Afterₗ p) ls
  afters-lt lt []                  = []
  afters-lt {ls = l ∷ _} lt (a ∷ as) = after-lt (head (force l)) lt a ∷ afters-lt lt as

  hushed-after : ∀ {B p} {ls : List (Events∞ B)} → All Hushed ls → All (Afterₗ p) ls
  hushed-after {p = p} []       = []
  hushed-after {p = p} (h ∷ hs) = subst (After p) (sym h) tt ∷ hushed-after hs

  hushed-nb : ∀ {B p} {ls : List (Events∞ B)} → All Hushed ls → All (NBₗ p) ls
  hushed-nb {p = p} []       = []
  hushed-nb {p = p} (h ∷ hs) = subst (NotBefore p) (sym h) tt ∷ hushed-nb hs

  nb-self : ∀ {B p} {l : Events∞ B} → head (force l) ≡ just p → NBₗ p l
  nb-self {p = p} hc = subst (NotBefore p) (sym hc) (<ᵖ-irrefl p)

  all-mid : ∀ {B} {P : Events∞ B → Set} {bs as} {c : Events∞ B} → All P bs → P c → All P as → All P (bs ++ c ∷ as)
  all-mid b c a = ++⁺ b (c ∷ a)

  head-hush : ∀ {A} (x : Events A) → head x ≡ nothing → x ≡ hush
  head-hush hush _ = refl

  map-hush : ∀ {A B} (g : A → B) (x : Events A) → head (mapᴱ g x) ≡ nothing → x ≡ hush
  map-hush g hush _ = refl

-- The lane a race finds: the list split around it, and its place among
-- the rest; none found, every lane hushed.
Found : ∀ {B} → List (Events∞ B) → Earliest B → Set
Found ls none              = All Hushed ls
Found ls (found p bs l as) = ls ≡ bs ++ l ∷ as × head (force l) ≡ just p × All (NBₗ p) bs × All (Afterₗ p) as

earliest-found : ∀ {B} (ls : List (Events∞ B)) → Found ls (earliest ls)
earliest-found []       = []
earliest-found (l ∷ ls) with head (force l) in h | earliest ls | earliest-found ls
... | nothing | none             | n                  = h ∷ n
... | nothing | found k bs c as  | (eq , hc , nb , af) = cong (l ∷_) eq , hc , subst (NotBefore k) (sym h) tt ∷ nb , af
... | just j  | none             | n                  = refl , h , [] , hushed-after n
... | just j  | found k bs c as  | (eq , hc , nb , af) with j <ᵖ k in lt
...   | true  = refl , h , [] , subst (All (Afterₗ j)) (sym eq) (all-mid (nbs-after lt nb) (subst (After j) (sym hc) lt) (afters-lt lt af))
...   | false = cong (l ∷_) eq , hc , subst (NotBefore k) (sym h) lt ∷ nb , af

earliest-hushed : ∀ {B} (ls : List (Events∞ B)) → All Hushed ls → earliest ls ≡ none
earliest-hushed []       []       = refl
earliest-hushed (l ∷ ls) (h ∷ hs) rewrite h | earliest-hushed ls hs = refl

------------------------------------------------------------------------
-- What the ended left, against the parts' heads

private
  clear-after : ∀ {k} h → clear k h ≡ true → After k h
  clear-after nothing  _ = tt
  clear-after (just h) a = a

  after-clear : ∀ {k} h → After k h → clear k h ≡ true
  after-clear nothing  _ = refl
  after-clear (just h) a = a

  clears-after : ∀ {B} k (ls : List (Events∞ B)) → clears k ls ≡ true → All (Afterₗ k) ls
  clears-after k []       _  = []
  clears-after k (l ∷ ls) eq with clear k (head (force l)) in c
  clears-after k (l ∷ ls) eq | true  = clear-after (head (force l)) c ∷ clears-after k ls eq
  clears-after k (l ∷ ls) () | false

  afters-clear : ∀ {B k} (ls : List (Events∞ B)) → All (Afterₗ k) ls → clears k ls ≡ true
  afters-clear []       []       = refl
  afters-clear (l ∷ ls) (a ∷ as) rewrite after-clear (head (force l)) a | afters-clear ls as = refl

-- Ahead of every part: after each head.
ahead-split : ∀ {B} k (o : Maybe (Events∞ (MonotonicList B))) ls → ahead-of k o ls ≡ true → After k (headᴼ o) × All (Afterₗ k) ls
ahead-split k o ls eq with clear k (headᴼ o) in c
ahead-split k o ls eq | true  = clear-after (headᴼ o) c , clears-after k ls eq
ahead-split k o ls () | false

after-ahead : ∀ {B k} (o : Maybe (Events∞ (MonotonicList B))) ls → After k (headᴼ o) → All (Afterₗ k) ls → ahead-of k o ls ≡ true
after-ahead o ls a al rewrite after-clear (headᴼ o) a | afters-clear ls al = refl

-- What ended parts left is not ahead of every part.
Low : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → List (Events∞ B) → Tail → Set
Low o ls idle      = Data.Unit.⊤
Low o ls (pin k _) = ahead-of k o ls ≡ false

-- Not ahead, it is no later than whatever part comes first.
low-tail : ∀ {B p} (o : Maybe (Events∞ (MonotonicList B))) ls t → Low o ls t → NotBefore p (headᴼ o) → All (NBₗ p) ls → TailNotBefore p t
low-tail o ls idle      lo n a = tt
low-tail {p = p} o ls (pin k u) lo n a with k <ᵖ p in lt
... | false = refl
... | true  = ⊥-elim (subst Holds (trans (sym (after-ahead o ls (after-le (headᴼ o) lt n) (nbs-after lt a))) lo) tt)

low-hushed : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) ls k → ahead-of k o ls ≡ false → headᴼ o ≡ nothing → All Hushed ls → ⊥
low-hushed o ls k lo ho hs = subst Holds (trans (sym (after-ahead o ls (subst (After k) (sym ho) tt) (hushed-after hs))) lo) tt

low-idle : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) ls t → Low o ls t → headᴼ o ≡ nothing → All Hushed ls → t ≡ idle
low-idle o ls idle      lo ho hs = refl
low-idle o ls (pin k u) lo ho hs = ⊥-elim (low-hushed o ls k lo ho hs)

------------------------------------------------------------------------
-- Parts erased

data OuterE {B : Set} (m : ℕ) : Maybe (Events∞ (MonotonicList B)) → Maybe (Events∞ (MonotonicList B)) → Set where
  doneᴱ : OuterE m nothing nothing
  liveᴱ : ∀ {e e′} → Eraseˢ m e e′ → OuterE m (just e) (just e′)

data LanesE {B : Set} (m : ℕ) : List (Events∞ B) → List (Events∞ B) → Set where
  []ᴱ  : LanesE m [] []
  _∷ᴱ_ : ∀ {l l′ ls ls′} → Eraseˢ m l l′ → LanesE m ls ls′ → LanesE m (l ∷ ls) (l′ ∷ ls′)

infixr 5 _∷ᴱ_

-- How many erased steps each part leads with: an erased step spends no
-- depth, so the merge walks a run of them on this fuel.
gapᵉ : ∀ {A k} {x : Events A} {t y} → Erase k x t y → ℕ
gapᵉ (erased _ _ x) = suc (gapᵉ x)
gapᵉ _              = 0

gapᵀ : ∀ {k} {x y : Tail} → Eraseᵀ k x y → ℕ
gapᵀ (unpin _ e) = suc (gapᵀ e)
gapᵀ _           = 0

gapᴼ : ∀ {B m} {o o′ : Maybe (Events∞ (MonotonicList B))} → OuterE m o o′ → ℕ
gapᴼ doneᴱ     = 0
gapᴼ (liveᴱ x) = gapᵉ (nowᵉ x)

gapᴸ : ∀ {B m} {ls ls′ : List (Events∞ B)} → LanesE m ls ls′ → ℕ
gapᴸ []ᴱ      = 0
gapᴸ (x ∷ᴱ l) = gapᵉ (nowᵉ x) + gapᴸ l

Gaps : ∀ {B m} {o o′ : Maybe (Events∞ (MonotonicList B))} {ls ls′ : List (Events∞ B)} {t t′} → OuterE m o o′ → LanesE m ls ls′ → Eraseᵀ m t t′ → ℕ
Gaps r l te = gapᴼ r + gapᴸ l + gapᵀ te

private
  outerE-pred : ∀ {B m} {o o′ : Maybe (Events∞ (MonotonicList B))} → OuterE (suc m) o o′ → OuterE m o o′
  outerE-pred doneᴱ     = doneᴱ
  outerE-pred (liveᴱ x) = liveᴱ (eraseˢ-pred x)

  lanesE-pred : ∀ {B m} {ls ls′ : List (Events∞ B)} → LanesE (suc m) ls ls′ → LanesE m ls ls′
  lanesE-pred []ᴱ      = []ᴱ
  lanesE-pred (x ∷ᴱ l) = eraseˢ-pred x ∷ᴱ lanesE-pred l

  lanesE-++ : ∀ {B m} {as as′ bs bs′ : List (Events∞ B)} → LanesE m as as′ → LanesE m bs bs′ → LanesE m (as ++ bs) (as′ ++ bs′)
  lanesE-++ []ᴱ      b = b
  lanesE-++ (x ∷ᴱ l) b = x ∷ᴱ lanesE-++ l b

  gap-++ : ∀ {B m} {as as′ bs bs′ : List (Events∞ B)} (a : LanesE m as as′) (b : LanesE m bs bs′) → gapᴸ (lanesE-++ a b) ≡ gapᴸ a + gapᴸ b
  gap-++ []ᴱ      b = refl
  gap-++ (x ∷ᴱ l) b = trans (cong (gapᵉ (nowᵉ x) +_) (gap-++ l b)) (sym (+-assoc (gapᵉ (nowᵉ x)) (gapᴸ l) (gapᴸ b)))

  -- A lane leading the run, read off the lanes it splits into.
  to-lane : ∀ {B m} {o o′ : Maybe (Events∞ (MonotonicList B))} {bs bs′ : List (Events∞ B)} {c c′ : Events∞ B} {as as′ : List (Events∞ B)} {t t′ g} (r : OuterE m o o′) (lb : LanesE m bs bs′)
            (lc : Eraseˢ m c c′) (la : LanesE m as as′) (te : Eraseᵀ m t t′)
          → Gaps r (lanesE-++ lb (lc ∷ᴱ la)) te ≤ g → gapᴼ r + (gapᴸ lb + (gapᵉ (nowᵉ lc) + gapᴸ la)) + gapᵀ te ≤ g
  to-lane {g = g} r lb lc la te = subst (λ z → gapᴼ r + z + gapᵀ te ≤ g) (gap-++ lb (lc ∷ᴱ la))

  lane-gap : ∀ a b c e → a + (b + suc c) + e ≡ suc (a + (b + c) + e)
  lane-gap a b c e = cong (_+ e) (trans (cong (a +_) (+-suc b c)) (+-suc a (b + c)))

  -- A lane's erased step burns one unit of fuel.
  lane-fuel : ∀ {B m} {o o′ : Maybe (Events∞ (MonotonicList B))} {bs bs′ : List (Events∞ B)} {c c′ : Events∞ B} {as as′ : List (Events∞ B)} {t t′ g} (r : OuterE m o o′) (lb : LanesE m bs bs′)
              (lc : Eraseˢ m c c′) (la : LanesE m as as′) (te : Eraseᵀ m t t′)
            → gapᴼ r + (gapᴸ lb + suc (gapᵉ (nowᵉ lc) + gapᴸ la)) + gapᵀ te ≤ suc g → Gaps r (lanesE-++ lb (lc ∷ᴱ la)) te ≤ g
  lane-fuel {g = g} r lb lc la te p =
    subst (λ z → gapᴼ r + z + gapᵀ te ≤ g) (sym (gap-++ lb (lc ∷ᴱ la)))
      (≤-pred (subst (_≤ suc g) (lane-gap (gapᴼ r) (gapᴸ lb) (gapᵉ (nowᵉ lc) + gapᴸ la) (gapᵀ te)) p))

  lane-none : ∀ a b c e → a + (b + suc c) + e ≤ 0 → ⊥
  lane-none a b c e p with subst (_≤ 0) (lane-gap a b c e) p
  ... | ()

  -- A tail's erased step burns one unit of fuel.
  tail-fuel : ∀ a c {g} → a + suc c ≤ suc g → a + c ≤ g
  tail-fuel a c {g} p = ≤-pred (subst (_≤ suc g) (+-suc a c) p)

  tail-none : ∀ a c → a + suc c ≤ 0 → ⊥
  tail-none a c p with subst (_≤ 0) (+-suc a c) p
  ... | ()

  lanesE-length : ∀ {B m} {ls ls′ : List (Events∞ B)} → LanesE m ls ls′ → length ls ≡ length ls′
  lanesE-length []ᴱ      = refl
  lanesE-length (_ ∷ᴱ l) = cong suc (lanesE-length l)

  idle-erase : ∀ m → Eraseᵀ m idle idle
  idle-erase m = eraseᵀ-agree (agreeᵀ-refl m idle)

  lanes-nb : ∀ {B m p} {ls ls′ : List (Events∞ B)} → LanesE (suc m) ls ls′ → All (NBₗ p) ls → All (NBₗ p) ls′
  lanes-nb []ᴱ              []       = []
  lanes-nb ((_ ,ᵉ x) ∷ᴱ l) (n ∷ ns) = nb-erase x n ∷ lanes-nb l ns

  lanes-after : ∀ {B m p} {ls ls′ : List (Events∞ B)} → LanesE (suc m) ls ls′ → All (Afterₗ p) ls → All (Afterₗ p) ls′
  lanes-after []ᴱ              []       = []
  lanes-after ((_ ,ᵉ x) ∷ᴱ l) (a ∷ as) = after-erase x a ∷ lanes-after l as

  lanes-hushed : ∀ {B m} {ls ls′ : List (Events∞ B)} → LanesE (suc m) ls ls′ → All Hushed ls → All Hushed ls′
  lanes-hushed []ᴱ              []       = []
  lanes-hushed ((_ ,ᵉ x) ∷ᴱ l) (h ∷ hs) = hushed-erase x h ∷ lanes-hushed l hs

  outer-nb : ∀ {B m p} {o o′ : Maybe (Events∞ (MonotonicList B))} → OuterE (suc m) o o′ → NotBefore p (headᴼ o) → NotBefore p (headᴼ o′)
  outer-nb doneᴱ             n = n
  outer-nb (liveᴱ (_ ,ᵉ x)) n = nb-erase x n

  outer-after : ∀ {B m p} {o o′ : Maybe (Events∞ (MonotonicList B))} → OuterE (suc m) o o′ → After p (headᴼ o) → After p (headᴼ o′)
  outer-after doneᴱ             a = a
  outer-after (liveᴱ (_ ,ᵉ x)) a = after-erase x a

  -- Ahead of the parts, ahead of them erased.
  ahead-mono : ∀ {B m k} {o o′ : Maybe (Events∞ (MonotonicList B))} {ls ls′} → OuterE (suc m) o o′ → LanesE (suc m) ls ls′
             → ahead-of k o ls ≡ true → ahead-of k o′ ls′ ≡ true
  ahead-mono {k = k} {o} {o′} {ls} {ls′} r l eq with ahead-split k o ls eq
  ... | a , al = after-ahead o′ ls′ (outer-after r a) (lanes-after l al)

  first-erase : ∀ {B m p} {o o′ : Maybe (Events∞ (MonotonicList B))} {bs bs′ as as′ t t′} → OuterE (suc m) o o′ → LanesE (suc m) bs bs′
              → LanesE (suc m) as as′ → Eraseᵀ (suc m) t t′ → First p o bs as t → First p o′ bs′ as′ t′
  first-erase r lb la te (first nb af on tn) = first (lanes-nb lb nb) (lanes-after la af) (outer-nb r on) (tnb-erase te tn)

-- A lane in the list, its counterpart in the other.
data Split {B : Set} (m : ℕ) (bs : List (Events∞ B)) (c : Events∞ B) (as : List (Events∞ B)) (g : ℕ) : List (Events∞ B) → Set where
  split : ∀ {bs′ c′ as′} (lb : LanesE m bs bs′) (lc : Eraseˢ m c c′) (la : LanesE m as as′) → gapᴸ (lanesE-++ lb (lc ∷ᴱ la)) ≡ g
        → Split m bs c as g (bs′ ++ c′ ∷ as′)

lanesE-split : ∀ {B m} (bs : List (Events∞ B)) {c as ls′} (l : LanesE m (bs ++ c ∷ as) ls′) → Split m bs c as (gapᴸ l) ls′
lanesE-split []       (x ∷ᴱ l) = split []ᴱ x l refl
lanesE-split (b ∷ bs) (x ∷ᴱ l) with lanesE-split bs l
... | split lb lc la e = split (x ∷ᴱ lb) lc la (cong (gapᵉ (nowᵉ x) +_) e)

cuts-erase : ∀ {B m} {ls ls′ : List (Events∞ B)} → LanesE m ls ls′ → Eraseᵀ m (cuts ls) (cuts ls′)
cuts-erase {m = m} []ᴱ = idle-erase m
cuts-erase ((t ,ᵉ _) ∷ᴱ l) = ∪-erase t (cuts-erase l)

whole-erase : ∀ {B m} {o o′ : Maybe (Events∞ (MonotonicList B))} {ls ls′ t t′} → OuterE m o o′ → LanesE m ls ls′ → Eraseᵀ m t t′
            → Eraseᵀ m (whole o ls t) (whole o′ ls′ t′)
whole-erase {m = m} doneᴱ l t = ∪-erase (idle-erase m) (∪-erase (cuts-erase l) t)
whole-erase (liveᴱ (u ,ᵉ _)) l t = ∪-erase u (∪-erase (cuts-erase l) t)

-- Lanes erased admit the same lane, queue alike, and drop erased.
admit-erase : ∀ {B m} op q (x : MonotonicList B) {ls ls′} qs → LanesE m ls ls′
            → LanesE m (proj₁ (admit op q x ls qs)) (proj₁ (admit op q x ls′ qs))
            × proj₁ (proj₂ (admit op q x ls qs)) ≡ proj₁ (proj₂ (admit op q x ls′ qs))
            × Eraseᵀ m (proj₂ (proj₂ (admit op q x ls qs))) (proj₂ (proj₂ (admit op q x ls′ qs)))
admit-erase {m = m} (mergeᶠ nothing)  q x qs l = eraseˢ-refl m (enter x q) ∷ᴱ l , refl , idle-erase m
admit-erase {m = m} (mergeᶠ (just n)) q x {ls} {ls′} qs l rewrite lanesE-length l with length ls′ <ᵇ n
... | true  = eraseˢ-refl m (enter x q) ∷ᴱ l , refl , idle-erase m
... | false = l , refl , idle-erase m
admit-erase {m = m} switchᶠ           q x qs l        = eraseˢ-refl m (enter x q) ∷ᴱ []ᴱ , refl , cuts-erase l
admit-erase {m = m} exhaustᶠ          q x qs []ᴱ      = eraseˢ-refl m (enter x q) ∷ᴱ []ᴱ , refl , idle-erase m
admit-erase {m = m} exhaustᶠ          q x qs (y ∷ᴱ l) = y ∷ᴱ l , refl , idle-erase m

------------------------------------------------------------------------
-- The merge

-- The outer's next, where the merge reads it: hushed, with every lane
-- hushed and nothing left running; else before every lane, and no later
-- than what ended parts left.
data Guard {B : Set} (ls : List (Events∞ B)) (t : Tail) : Maybe Pos → Set where
  hushedᴳ : All Hushed ls → t ≡ idle → Guard ls t nothing
  ledᴳ    : ∀ {p} → All (Afterₗ p) ls → TailNotBefore p t → Guard ls t (just p)

via-guard : ∀ {B} (e : Events∞ (MonotonicList B)) ls t → Low (just e) ls t → All Hushed ls → Guard ls t (head (force e))
via-guard e ls t lo hs with head (force e) in he
... | nothing = hushedᴳ hs (low-idle (just e) ls t lo he hs)
... | just p  = ledᴳ (hushed-after hs) (low-tail (just e) ls t lo (subst (NotBefore p) (sym he) (<ᵖ-irrefl p)) (hushed-nb hs))

module _ {B : Set} (op : FlatOp) where

  -- Its next, from its parts' heads.
  head-outer : ∀ {k} (e : Events∞ (MonotonicList B)) ls qs t ev → NotBefore k (head ev) → NotBefore k (head (outer op e ls qs t ev))
  head-outer e ls       qs       t (out q x r) n with admit op (q ++ [ ix 1 ]) x ls qs
  ... | _ , _ , _ = below-on q (ix 0) n
  head-outer e ls       qs       t (skip q r)  n = n
  head-outer e []       []       t (end c)     n = n
  head-outer e []       (x ∷ qs) t (end c)     n = n
  head-outer e (l ∷ ls) qs       t (end c)     n = n
  head-outer e ls       qs       t hush        n = n

  head-lane : ∀ {k} (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t ev → NotBefore k (head ev)
            → NotBefore k (head (lane op o bs l as qs t ev))
  head-lane o        bs       l as       qs       t (out _ _ _) n = n
  head-lane o        bs       l as       qs       t (skip _ _)  n = n
  head-lane o        bs       l as       (x ∷ qs) t (end c)     n = below-on c (ix 0) n
  head-lane nothing  []       l []       []       t (end c)     n = n
  head-lane nothing  []       l (a ∷ as) []       t (end c)     n = n
  head-lane nothing  (b ∷ bs) l as       []       t (end c)     n = n
  head-lane (just e) bs       l as       []       t (end c)     n = n
  head-lane o        bs       l as       qs       t hush        n = n

  head-race : ∀ {k} (o : Maybe (Events∞ (MonotonicList B))) p bs (l : Events∞ B) as qs t → NotBefore k (headᴼ o) → NBₗ k l
            → NotBefore k (head (race op o p bs l as qs t))
  head-race nothing  p bs l as qs t n nl = head-lane nothing bs l as qs t (force l) nl
  head-race {k} (just e) p bs l as qs t n nl with head (force e) in he
  ... | nothing = head-lane (just e) bs l as qs t (force l) nl
  ... | just p′ with p′ <ᵖ p
  ...   | true  = head-outer e (bs ++ l ∷ as) qs t (force e) (subst (NotBefore k) (sym he) n)
  ...   | false = head-lane (just e) bs l as qs t (force l) nl

  head-parts : ∀ {k} (o : Maybe (Events∞ (MonotonicList B))) ls qs t → NotBefore k (headᴼ o) → All (NBₗ k) ls
             → NotBefore k (head (parts op o ls qs t))
  head-parts o ls qs t n a with earliest ls | earliest-found ls
  head-parts nothing  ls qs t n a | none | _ = tt
  head-parts (just e) ls qs t n a | none | _ = head-outer e ls qs t (force e) n
  head-parts o ls qs t n a | found p bs l as | (refl , _ , _ , _) = head-race o p bs l as qs t n (mid bs a)
    where mid : ∀ {k} bs {as} → All (NBₗ k) (bs ++ l ∷ as) → NBₗ k l
          mid []       (x ∷ _) = x
          mid (_ ∷ bs) (_ ∷ a) = mid bs a

  -- THE MERGE'S NEXT is no earlier than every part's.
  head-go : ∀ {k} (o : Maybe (Events∞ (MonotonicList B))) ls qs t → NotBefore k (headᴼ o) → All (NBₗ k) ls → TailNotBefore k t
          → NotBefore k (head (go op o ls qs t))
  head-go o ls qs idle      n a tn = head-parts o ls qs idle n a
  head-go o ls qs (pin j u) n a tn with ahead-of j o ls
  ... | true  = tn
  ... | false = head-parts o ls qs (pin j u) n a

  -- Every part hushed and nothing left running, the merge hushes.
  go-hushed : ∀ (e : Events∞ (MonotonicList B)) ls qs → All Hushed ls → force e ≡ hush → go op (just e) ls qs idle ≡ hush
  go-hushed e ls qs hs he rewrite earliest-hushed ls hs | he = refl

  -- THE MERGE, ERASED.
  mutual
    go-erase : ∀ {m} {o o′ : Maybe (Events∞ (MonotonicList B))} {ls ls′ : List (Events∞ B)} qs {t t′ g} (r : OuterE m o o′) (l : LanesE m ls ls′) (te : Eraseᵀ m t t′)
             → Gaps r l te ≤ g → Erase m (go op o ls qs t) (whole o′ ls′ t′) (go op o′ ls′ qs t′)
    go-erase {0}     qs r l te b = stopᵉ
    go-erase {suc m} qs r l te b = go-erase⁺ _ qs r l te b

    -- Past a kept step, at the depth left; past an erased one, at the same.
    go-erase⁺ : ∀ {m} {o o′ : Maybe (Events∞ (MonotonicList B))} {ls ls′ : List (Events∞ B)} g qs {t t′} (r : OuterE (suc m) o o′)
                (l : LanesE (suc m) ls ls′) (te : Eraseᵀ (suc m) t t′)
              → Gaps r l te ≤ g → Erase (suc m) (go op o ls qs t) (whole o′ ls′ t′) (go op o′ ls′ qs t′)
    go-erase⁺ g qs r l idleᵉ b = parts-erase g qs r l idleᵉ tt b
    go-erase⁺ {o = o} {o′} {ls} {ls′} g qs r l (pinᵉ {p = k} e) b with ahead-of k o ls in eq
    ... | true rewrite ahead-mono {k = k} r l eq =
      skipᵉ (whole-erase (outerE-pred r) (lanesE-pred l) e) (go-erase qs (outerE-pred r) (lanesE-pred l) e ≤-refl)
    ... | false = parts-erase g qs r l (pinᵉ e) eq b
    go-erase⁺ {o = o} {o′} {ls} {ls′} g qs {t′ = t′} r l (unpin {p = k} tn e) b with ahead-of k o ls in eq
    go-erase⁺ 0 qs r l (unpin tn e) b | true = ⊥-elim (tail-none (gapᴼ r + gapᴸ l) (gapᵀ e) b)
    go-erase⁺ {o = o} {o′} {ls} {ls′} (suc g) qs {t′ = t′} r l (unpin {p = k} tn e) b | true with ahead-split k o ls eq
    ... | a , al = erased (head-go o′ ls′ qs t′ (after-nb (headᴼ o′) (outer-after r a)) (afters-nb (lanes-after l al)) tn)
                          (whole-erase r l e) (go-erase⁺ g qs r l e (tail-fuel (gapᴼ r + gapᴸ l) (gapᵀ e) b))
    go-erase⁺ g qs r l (unpin tn e) b | false = parts-erase g qs r l (unpin tn e) eq b

    parts-erase : ∀ {m} {o o′ : Maybe (Events∞ (MonotonicList B))} {ls ls′ : List (Events∞ B)} g qs {t t′} (r : OuterE (suc m) o o′) (l : LanesE (suc m) ls ls′)
                  (te : Eraseᵀ (suc m) t t′) → Low o ls t → Gaps r l te ≤ g
                → Erase (suc m) (parts op o ls qs t) (whole o′ ls′ t′) (go op o′ ls′ qs t′)
    parts-erase {ls = ls} g qs r l te lo b with earliest ls | earliest-found ls
    ... | none            | hs                   = via-erase g qs r l te lo hs b
    ... | found p bs c as | (refl , hc , nb , af) with lanesE-split bs l
    ...   | split lb lc la e = race-erase g qs r lb lc la te lo hc nb af (subst (λ z → gapᴼ r + z + gapᵀ te ≤ _) (sym e) b)

    via-erase : ∀ {m} {o o′ : Maybe (Events∞ (MonotonicList B))} {ls ls′ : List (Events∞ B)} g qs {t t′} (r : OuterE (suc m) o o′) (l : LanesE (suc m) ls ls′)
                (te : Eraseᵀ (suc m) t t′) → Low o ls t → All Hushed ls → Gaps r l te ≤ g
              → Erase (suc m) (viaOuter op o ls qs t) (whole o′ ls′ t′) (go op o′ ls′ qs t′)
    via-erase {ls′ = ls′} g qs doneᴱ l idleᵉ lo hs b rewrite earliest-hushed ls′ (lanes-hushed l hs) = hushᵉ
    via-erase {ls = ls} g qs doneᴱ l (pinᵉ {p = k} e)    lo hs b = ⊥-elim (low-hushed nothing ls k lo refl hs)
    via-erase {ls = ls} g qs doneᴱ l (unpin {p = k} o e) lo hs b = ⊥-elim (low-hushed nothing ls k lo refl hs)
    via-erase {ls = ls} g qs {t} (liveᴱ {e} (ct ,ᵉ x)) l te lo hs b = outer-erase g qs ct refl x l te (via-guard e ls t lo hs) b

    race-erase : ∀ {m} {o o′ : Maybe (Events∞ (MonotonicList B))} {p bs bs′} {c c′ : Events∞ B} {as as′} g qs {t t′}
                 (r : OuterE (suc m) o o′) (lb : LanesE (suc m) bs bs′) (lc : Eraseˢ (suc m) c c′) (la : LanesE (suc m) as as′) (te : Eraseᵀ (suc m) t t′)
               → Low o (bs ++ c ∷ as) t → head (force c) ≡ just p → All (NBₗ p) bs → All (Afterₗ p) as → Gaps r (lanesE-++ lb (lc ∷ᴱ la)) te ≤ g
               → Erase (suc m) (race op o p bs c as qs t) (whole o′ (bs′ ++ c′ ∷ as′) t′) (go op o′ (bs′ ++ c′ ∷ as′) qs t′)
    race-erase {o = nothing} {p = p} {bs = bs} {c = c} {as = as} g qs {t} doneᴱ lb (ct ,ᵉ x) la te lo hc nb af b =
      lane-erase g qs doneᴱ lb ct refl x la te hc (first nb af tt (low-tail nothing (bs ++ c ∷ as) t lo tt (all-mid {P = NBₗ p} nb (nb-self {l = c} hc) (afters-nb af))))
        (to-lane doneᴱ lb (ct ,ᵉ x) la te b)
    race-erase {o = just e} {just e′} {p = p} {bs} {c = c} {as = as} g qs {t} (liveᴱ (ot ,ᵉ ox)) lb (ct ,ᵉ x) la te lo hc nb af b with head (force e) in he
    ... | nothing =
      lane-erase g qs (liveᴱ (ot ,ᵉ ox)) lb ct refl x la te hc
        (first nb af (subst (NotBefore p) (sym he) tt) (low-tail (just e) (bs ++ c ∷ as) t lo (subst (NotBefore p) (sym he) tt) (all-mid {P = NBₗ p} nb (nb-self {l = c} hc) (afters-nb af))))
        (to-lane {o = just e} {just e′} (liveᴱ (ot ,ᵉ ox)) lb (ct ,ᵉ x) la te b)
    ... | just p′ with p′ <ᵖ p in lt
    ...   | true  = outer-erase {e = e} {e′} g qs ot refl ox (lanesE-++ lb ((ct ,ᵉ x) ∷ᴱ la)) te
                      (subst (Guard (bs ++ c ∷ as) t) (sym he) (ledᴳ ALL (low-tail (just e) (bs ++ c ∷ as) t lo (subst (NotBefore p′) (sym he) (<ᵖ-irrefl p′)) (afters-nb ALL)))) b
      where ALL = all-mid (nbs-after lt nb) (subst (After p′) (sym hc) lt) (afters-lt lt af)
    ...   | false =
      lane-erase g qs (liveᴱ (ot ,ᵉ ox)) lb ct refl x la te hc
        (first nb af (subst (NotBefore p) (sym he) lt) (low-tail (just e) (bs ++ c ∷ as) t lo (subst (NotBefore p) (sym he) lt) (all-mid {P = NBₗ p} nb (nb-self {l = c} hc) (afters-nb af))))
        (to-lane {o = just e} {just e′} (liveᴱ (ot ,ᵉ ox)) lb (ct ,ᵉ x) la te b)

    outer-erase : ∀ {m} {e e′ : Events∞ (MonotonicList B)} {ls ls′ : List (Events∞ B)} g qs {t t′ ev ev′} → Eraseᵀ (suc m) (cut e) (cut e′) → force e′ ≡ ev′
                → (ex : Erase (suc m) ev (cut e′) ev′) (l : LanesE (suc m) ls ls′) (te : Eraseᵀ (suc m) t t′) → Guard ls t (head ev)
                → gapᵉ ex + gapᴸ l + gapᵀ te ≤ g
                → Erase (suc m) (outer op e ls qs t ev) (whole (just e′) ls′ t′) (go op (just e′) ls′ qs t′)
    outer-erase {e′ = e′} {ls} {ls′} g qs {t} {t′} ct eq′ (outᵉ {p = q} {a = x} {l = r} {r = r′} et ex) l te (ledᴳ al tn) b
      rewrite go-outer op e′ ls′ qs t′ (cong head eq′) (lanes-after l al) (tnb-erase te tn) | eq′
      with admit op (q ++ [ ix 1 ]) x ls qs | admit op (q ++ [ ix 1 ]) x ls′ qs | admit-erase op (q ++ [ ix 1 ]) x qs (lanesE-pred l)
    ... | ls₁ , qs₁ , d₁ | ls₁′ , .qs₁ , d₁′ | l₁ , refl , d =
      skipᵉ (whole-erase {o = just r} {just r′} {ls₁} {ls₁′} (liveᴱ (et ,ᵉ ex)) l₁ (∪-erase (eraseᵀ-pred te) d))
            (go-erase {o = just r} {just r′} {ls₁} {ls₁′} qs₁ (liveᴱ (et ,ᵉ ex)) l₁ (∪-erase (eraseᵀ-pred te) d) ≤-refl)
    outer-erase {e′ = e′} {ls} {ls′} g qs {t′ = t′} ct eq′ (skipᵉ {l = r} {r = r′} et ex) l te (ledᴳ al tn) b
      rewrite go-outer op e′ ls′ qs t′ (cong head eq′) (lanes-after l al) (tnb-erase te tn) | eq′ =
      skipᵉ (whole-erase {o = just r} {just r′} {ls} {ls′} (liveᴱ (et ,ᵉ ex)) (lanesE-pred l) (eraseᵀ-pred te))
            (go-erase {o = just r} {just r′} {ls} {ls′} qs (liveᴱ (et ,ᵉ ex)) (lanesE-pred l) (eraseᵀ-pred te) ≤-refl)
    outer-erase 0 qs ct eq′ (erased o et ex) l te gd ()
    outer-erase {e′ = e′} {ls} {ls′} (suc g) qs {t′ = t′} ct refl (erased {l = r} o et ex) l te (ledᴳ al tn) b =
      erased (head-go (just e′) ls′ qs t′ o (afters-nb (lanes-after l al)) (tnb-erase te tn))
             (whole-erase {o = just r} {just e′} {ls} {ls′} (liveᴱ (et ,ᵉ ex)) l te) (go-erase⁺ g qs (liveᴱ (et ,ᵉ ex)) l te (≤-pred b))
    outer-erase {e′ = e′} {ls′ = ls′} g qs {t′ = t′} ct eq′ endᵉ []ᴱ te (ledᴳ al tn) b
      with qs
    ... | [] rewrite go-outer op e′ [] [] t′ (cong head eq′) [] (tnb-erase te tn) | eq′ = endᵉ
    ... | x ∷ qs′ rewrite go-outer op e′ [] (x ∷ qs′) t′ (cong head eq′) [] (tnb-erase te tn) | eq′ =
      skipᵉ (whole-erase {B} doneᴱ []ᴱ T) (go-erase (x ∷ qs′) doneᴱ []ᴱ T ≤-refl)
      where T = ∪-erase (eraseᵀ-pred te) (eraseᵀ-pred ct)
    outer-erase {e′ = e′} {ls′ = ls′} g qs {t′ = t′} ct eq′ endᵉ (y ∷ᴱ l) te (ledᴳ al tn) b
      rewrite go-outer op e′ ls′ qs t′ (cong head eq′) (lanes-after (y ∷ᴱ l) al) (tnb-erase te tn) | eq′ =
      skipᵉ (whole-erase doneᴱ (lanesE-pred (y ∷ᴱ l)) T) (go-erase qs doneᴱ (lanesE-pred (y ∷ᴱ l)) T ≤-refl)
      where T = ∪-erase (eraseᵀ-pred te) (eraseᵀ-pred ct)
    outer-erase {e′ = e′} {ls′ = ls′} g qs ct eq′ hushᵉ l idleᵉ (hushedᴳ hs refl) b
      rewrite go-hushed e′ ls′ qs (lanes-hushed l hs) eq′ = hushᵉ

    lane-erase : ∀ {m} {o o′ : Maybe (Events∞ (MonotonicList B))} {p bs bs′} {c c′ : Events∞ B} {as as′} g qs {t t′ ev ev′}
                 (r : OuterE (suc m) o o′) (lb : LanesE (suc m) bs bs′) → Eraseᵀ (suc m) (cut c) (cut c′) → force c′ ≡ ev′
               → (ex : Erase (suc m) ev (cut c′) ev′) (la : LanesE (suc m) as as′) (te : Eraseᵀ (suc m) t t′) → head ev ≡ just p → First p o bs as t
               → gapᴼ r + (gapᴸ lb + (gapᵉ ex + gapᴸ la)) + gapᵀ te ≤ g
               → Erase (suc m) (lane op o bs c as qs t ev) (whole o′ (bs′ ++ c′ ∷ as′) t′) (go op o′ (bs′ ++ c′ ∷ as′) qs t′)
    lane-erase {o′ = o′} {bs′ = bs′} {c′ = c′} {as′ = as′} g qs {t′ = t′} r lb ct eq′ (outᵉ et ex) la te refl F b
      rewrite go-rise op o′ bs′ c′ as′ qs t′ (cong head eq′) (first-erase r lb la te F) | eq′ =
      outᵉ (whole-erase (outerE-pred r) L (eraseᵀ-pred te)) (go-erase qs (outerE-pred r) L (eraseᵀ-pred te) ≤-refl)
      where L = lanesE-++ (lanesE-pred lb) ((et ,ᵉ ex) ∷ᴱ lanesE-pred la)
    lane-erase {o′ = o′} {bs′ = bs′} {c′ = c′} {as′ = as′} g qs {t′ = t′} r lb ct eq′ (skipᵉ et ex) la te refl F b
      rewrite go-rise op o′ bs′ c′ as′ qs t′ (cong head eq′) (first-erase r lb la te F) | eq′ =
      skipᵉ (whole-erase (outerE-pred r) L (eraseᵀ-pred te)) (go-erase qs (outerE-pred r) L (eraseᵀ-pred te) ≤-refl)
      where L = lanesE-++ (lanesE-pred lb) ((et ,ᵉ ex) ∷ᴱ lanesE-pred la)
    lane-erase 0 qs r lb ct eq′ (erased o et ex) la te refl F b = ⊥-elim (lane-none (gapᴼ r) (gapᴸ lb) (gapᵉ ex + gapᴸ la) (gapᵀ te) b)
    lane-erase {o′ = o′} {p} {bs′ = bs′} {c′ = c′} {as′ = as′} (suc g) qs {t′ = t′} r lb ct refl (erased o et ex) la te refl F b
      with first-erase r lb la te F
    ... | first nb′ af′ on′ tn′ =
      erased (head-go o′ (bs′ ++ c′ ∷ as′) qs t′ on′ (all-mid nb′ o (afters-nb af′)) tn′)
             (whole-erase r L te) (go-erase⁺ g qs r L te (lane-fuel r lb (et ,ᵉ ex) la te b))
      where L = lanesE-++ lb ((et ,ᵉ ex) ∷ᴱ la)
    lane-erase {m} {o′ = o′} {bs′ = bs′} {c′ = c′} {as′ = as′} g qs {t′ = t′} r lb ct eq′ endᵉ la te refl F b
      rewrite go-rise op o′ bs′ c′ as′ qs t′ (cong head eq′) (first-erase r lb la te F) | eq′ = lane-end qs r lb ct la te
    lane-erase g qs r lb ct eq′ hushᵉ la te () F b

    lane-end : ∀ {m} {o o′ : Maybe (Events∞ (MonotonicList B))} {bs bs′} {c c′ : Events∞ B} {as as′} qs {t t′ p}
             → OuterE (suc m) o o′ → LanesE (suc m) bs bs′ → Eraseᵀ (suc m) (cut c) (cut c′) → LanesE (suc m) as as′ → Eraseᵀ (suc m) t t′
             → Erase (suc m) (lane op o bs c as qs t (end p)) (whole o′ (bs′ ++ c′ ∷ as′) t′) (lane op o′ bs′ c′ as′ qs t′ (end p))
    lane-end {m} (x ∷ qs) {p = p} r lb ct la te =
      skipᵉ (whole-erase (outerE-pred r) L T) (go-erase qs (outerE-pred r) L T ≤-refl)
      where L = eraseˢ-refl m (enter x (p ++ [ ix 1 ])) ∷ᴱ lanesE-pred (lanesE-++ lb la)
            T = ∪-erase (eraseᵀ-pred te) (eraseᵀ-pred ct)
    lane-end [] doneᴱ []ᴱ ct []ᴱ te = endᵉ
    lane-end [] doneᴱ []ᴱ ct (y ∷ᴱ la) te =
      skipᵉ (whole-erase doneᴱ L T) (go-erase [] doneᴱ L T ≤-refl)
      where L = lanesE-pred (y ∷ᴱ la)
            T = ∪-erase (eraseᵀ-pred te) (eraseᵀ-pred ct)
    lane-end [] doneᴱ (y ∷ᴱ lb) ct la te =
      skipᵉ (whole-erase doneᴱ L T) (go-erase [] doneᴱ L T ≤-refl)
      where L = lanesE-pred (lanesE-++ (y ∷ᴱ lb) la)
            T = ∪-erase (eraseᵀ-pred te) (eraseᵀ-pred ct)
    lane-end [] r@(liveᴱ _) lb ct la te =
      skipᵉ (whole-erase (outerE-pred r) L T) (go-erase [] (outerE-pred r) L T ≤-refl)
      where L = lanesE-pred (lanesE-++ lb la)
            T = ∪-erase (eraseᵀ-pred te) (eraseᵀ-pred ct)

  ------------------------------------------------------------------------
  -- Parts with the same next

  data OuterL : Maybe (Events∞ (MonotonicList B)) → Maybe (Events∞ (MonotonicList B)) → Set where
    doneˡ : OuterL nothing nothing
    liveˡ : ∀ {e e′} → Lead⁼ (force e) (force e′) → OuterL (just e) (just e′)

  data LanesL : List (Events∞ B) → List (Events∞ B) → Set where
    []ˡ  : LanesL [] []
    _∷ˡ_ : ∀ {l l′ ls ls′} → Lead⁼ (force l) (force l′) → LanesL ls ls′ → LanesL (l ∷ ls) (l′ ∷ ls′)

  data EarliestL : Earliest B → Earliest B → Set where
    noneˡ  : EarliestL none none
    foundˡ : ∀ {k bs bs′ l l′ as as′} → LanesL bs bs′ → Lead⁼ (force l) (force l′) → LanesL as as′
           → EarliestL (found k bs l as) (found k bs′ l′ as′)

  private
    lanesL-++ : ∀ {as as′ bs bs′} → LanesL as as′ → LanesL bs bs′ → LanesL (as ++ bs) (as′ ++ bs′)
    lanesL-++ []ˡ      b = b
    lanesL-++ (a ∷ˡ l) b = a ∷ˡ lanesL-++ l b

    earliest-lead : ∀ {ls ls′} → LanesL ls ls′ → EarliestL (earliest ls) (earliest ls′)
    earliest-lead []ˡ = noneˡ
    earliest-lead {l ∷ ls} {l′ ∷ ls′} (a ∷ˡ as)
      with head (force l) | head (force l′) | lead-head a | earliest ls | earliest ls′ | earliest-lead as
    ... | nothing | _ | refl | none           | _ | noneˡ        = noneˡ
    ... | nothing | _ | refl | found _ _ _ _  | _ | foundˡ b c d = foundˡ (a ∷ˡ b) c d
    ... | just k  | _ | refl | none           | _ | noneˡ        = foundˡ []ˡ a as
    ... | just k  | _ | refl | found k′ _ _ _ | _ | foundˡ b c d with k <ᵖ k′
    ...   | true  = foundˡ []ˡ a as
    ...   | false = foundˡ (a ∷ˡ b) c d

    ahead-lead : ∀ {k o o′ ls ls′} → OuterL o o′ → LanesL ls ls′ → ahead-of k o ls ≡ ahead-of k o′ ls′
    ahead-lead {k} r l = cong₂∧ (cong (clear k) (heads r)) (lanes l)
      where
        cong₂∧ : ∀ {a a′ b b′} → a ≡ a′ → b ≡ b′ → (a ∧ b) ≡ (a′ ∧ b′)
        cong₂∧ refl refl = refl
        heads : ∀ {o o′} → OuterL o o′ → headᴼ o ≡ headᴼ o′
        heads doneˡ     = refl
        heads (liveˡ a) = lead-head a
        lanes : ∀ {ls ls′} → LanesL ls ls′ → clears k ls ≡ clears k ls′
        lanes []ˡ      = refl
        lanes (a ∷ˡ l) = cong₂∧ (cong (clear k) (lead-head a)) (lanes l)

    outer-lead : ∀ {e e′ ls ls′} qs t {ev ev′} → LanesL ls ls′ → Lead⁼ ev ev′ → Lead⁼ (outer op e ls qs t ev) (outer op e′ ls′ qs t ev′)
    outer-lead {ls = ls} {ls′} qs t {out q x _} l outᴸ with admit op (q ++ [ ix 1 ]) x ls qs | admit op (q ++ [ ix 1 ]) x ls′ qs
    ... | _ , _ , _ | _ , _ , _ = skipᴸ
    outer-lead qs       t l          skipᴸ = skipᴸ
    outer-lead []       t []ˡ        endᴸ  = endᴸ
    outer-lead (x ∷ qs) t []ˡ        endᴸ  = skipᴸ
    outer-lead qs       t (a ∷ˡ l)   endᴸ  = skipᴸ
    outer-lead qs       t l          hushᴸ = hushᴸ

    lane-lead : ∀ {o o′ bs bs′} {c c′ : Events∞ B} {as as′} qs t {ev ev′} → OuterL o o′ → LanesL bs bs′ → LanesL as as′ → Lead⁼ ev ev′
              → Lead⁼ (lane op o bs c as qs t ev) (lane op o′ bs′ c′ as′ qs t ev′)
    lane-lead qs       t r         b         d         outᴸ  = outᴸ
    lane-lead qs       t r         b         d         skipᴸ = skipᴸ
    lane-lead (x ∷ qs) t r         b         d         endᴸ  = skipᴸ
    lane-lead []       t doneˡ     []ˡ       []ˡ       endᴸ  = endᴸ
    lane-lead []       t doneˡ     []ˡ       (a ∷ˡ d)  endᴸ  = skipᴸ
    lane-lead []       t doneˡ     (a ∷ˡ b)  d         endᴸ  = skipᴸ
    lane-lead []       t (liveˡ _) b         d         endᴸ  = skipᴸ
    lane-lead qs       t r         b         d         hushᴸ = hushᴸ

    race-lead : ∀ {o o′ k bs bs′} {c c′ : Events∞ B} {as as′} qs t → OuterL o o′ → LanesL bs bs′ → Lead⁼ (force c) (force c′) → LanesL as as′
              → Lead⁼ (race op o k bs c as qs t) (race op o′ k bs′ c′ as′ qs t)
    race-lead qs t doneˡ b c d = lane-lead qs t doneˡ b d c
    race-lead {k = k} qs t o@(liveˡ {e} {e′} a) b c d with head (force e) | head (force e′) | lead-head a
    ... | nothing | _ | refl = lane-lead qs t o b d c
    ... | just k′ | _ | refl with k′ <ᵖ k
    ...   | true  = outer-lead qs t (lanesL-++ b (c ∷ˡ d)) a
    ...   | false = lane-lead qs t o b d c

    parts-lead : ∀ {o o′ ls ls′} qs t → OuterL o o′ → LanesL ls ls′ → Lead⁼ (parts op o ls qs t) (parts op o′ ls′ qs t)
    parts-lead {ls = ls} {ls′} qs t r l with earliest ls | earliest ls′ | earliest-lead l
    parts-lead qs t doneˡ     l | none | _ | noneˡ = hushᴸ
    parts-lead qs t (liveˡ a) l | none | _ | noneˡ = outer-lead qs t l a
    parts-lead qs t r         l | found _ _ _ _ | _ | foundˡ b c d = race-lead qs t r b c d

  -- THE MERGE'S NEXT, from its parts' nexts.
  go-lead : ∀ {o o′ ls ls′} qs t → OuterL o o′ → LanesL ls ls′ → Lead⁼ (go op o ls qs t) (go op o′ ls′ qs t)
  go-lead qs idle r l = parts-lead qs idle r l
  go-lead {o} {o′} {ls} {ls′} qs (pin k u) r l rewrite ahead-lead {k = k} r l with ahead-of k o′ ls′
  ... | true  = skipᴸ
  ... | false = parts-lead qs (pin k u) r l

  private
    outer-hush : ∀ (e : Events∞ (MonotonicList B)) ls qs t ev → outer op e ls qs t ev ≡ hush → head ev ≡ nothing
    outer-hush e ls       qs       t (out q x r) with admit op (q ++ [ ix 1 ]) x ls qs
    ... | _ , _ , _ = λ ()
    outer-hush e ls       qs       t (skip q r)  = λ ()
    outer-hush e []       []       t (end c)     = λ ()
    outer-hush e []       (x ∷ qs) t (end c)     = λ ()
    outer-hush e (l ∷ ls) qs       t (end c)     = λ ()
    outer-hush e ls       qs       t hush        = λ _ → refl

    lane-hush : ∀ (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t ev {p} → head ev ≡ just p
              → lane op o bs l as qs t ev ≡ hush → ⊥
    lane-hush o        bs       l as       qs       t (out _ _ _) _ = λ ()
    lane-hush o        bs       l as       qs       t (skip _ _)  _ = λ ()
    lane-hush o        bs       l as       (x ∷ qs) t (end c)     _ = λ ()
    lane-hush nothing  []       l []       []       t (end c)     _ = λ ()
    lane-hush nothing  []       l (a ∷ as) []       t (end c)     _ = λ ()
    lane-hush nothing  (b ∷ bs) l as       []       t (end c)     _ = λ ()
    lane-hush (just e) bs       l as       []       t (end c)     _ = λ ()
    lane-hush o        bs       l as       qs       t hush        ()

    race-hush : ∀ (o : Maybe (Events∞ (MonotonicList B))) p bs (l : Events∞ B) as qs t → head (force l) ≡ just p
              → race op o p bs l as qs t ≡ hush → ⊥
    race-hush nothing  p bs l as qs t hc = lane-hush nothing bs l as qs t (force l) hc
    race-hush (just e) p bs l as qs t hc with head (force e) in he
    ... | nothing = lane-hush (just e) bs l as qs t (force l) hc
    ... | just p′ with p′ <ᵖ p
    ...   | true  = λ eq → just≢nothing (trans (sym he) (outer-hush e (bs ++ l ∷ as) qs t (force e) eq))
      where just≢nothing : ∀ {x : Pos} → just x ≡ nothing → ⊥
            just≢nothing ()
    ...   | false = lane-hush (just e) bs l as qs t (force l) hc

    parts-hush : ∀ (o : Maybe (Events∞ (MonotonicList B))) ls qs t → parts op o ls qs t ≡ hush → headᴼ o ≡ nothing × All Hushed ls
    parts-hush o ls qs t with earliest ls | earliest-found ls
    parts-hush nothing  ls qs t | none | hs = λ _ → refl , hs
    parts-hush (just e) ls qs t | none | hs = λ eq → outer-hush e ls qs t (force e) eq , hs
    parts-hush o ls qs t | found p bs l as | (refl , hc , _ , _) = λ eq → ⊥-elim (race-hush o p bs l as qs t hc eq)

  -- THE MERGE HUSHED: every part hushed.
  go-hush : ∀ (o : Maybe (Events∞ (MonotonicList B))) ls qs t → go op o ls qs t ≡ hush → headᴼ o ≡ nothing × All Hushed ls
  go-hush o ls qs idle      = parts-hush o ls qs idle
  go-hush o ls qs (pin k u) with ahead-of k o ls
  ... | true  = λ ()
  ... | false = parts-hush o ls qs (pin k u)

------------------------------------------------------------------------
-- THE ERASURE, AT A MERGE'S FRAMES: a merge fed a run with skips erased
-- runs with skips erased, its next kept: it keeps its parts' order, and
-- what the parts leave running is the merge's tail.

private
  outerE-refl : ∀ {B} m (o : Maybe (Events∞ (MonotonicList B))) → OuterE m o o
  outerE-refl m nothing  = doneᴱ
  outerE-refl m (just e) = liveᴱ (eraseˢ-refl m e)

  lanesE-refl : ∀ {B} m (ls : List (Events∞ B)) → LanesE m ls ls
  lanesE-refl m []       = []ᴱ
  lanesE-refl m (l ∷ ls) = eraseˢ-refl m l ∷ᴱ lanesE-refl m ls

  outerL-refl : ∀ {B} (op : FlatOp) (o : Maybe (Events∞ (MonotonicList B))) → OuterL op o o
  outerL-refl op nothing  = doneˡ
  outerL-refl op (just e) = liveˡ (lead-refl (force e))
    where lead-refl : ∀ {A} (x : Events A) → Lead⁼ x x
          lead-refl (out _ _ _) = outᴸ
          lead-refl (skip _ _)  = skipᴸ
          lead-refl (end _)     = endᴸ
          lead-refl hush        = hushᴸ

  lanesL-refl : ∀ {B} (op : FlatOp) (ls : List (Events∞ B)) → LanesL op ls ls
  lanesL-refl op []       = []ˡ
  lanesL-refl op (l ∷ ls) = lead-refl (force l) ∷ˡ lanesL-refl op ls
    where lead-refl : ∀ {A} (x : Events A) → Lead⁼ x x
          lead-refl (out _ _ _) = outᴸ
          lead-refl (skip _ _)  = skipᴸ
          lead-refl (end _)     = endᴸ
          lead-refl hush        = hushᴸ

  eraseᵀ-refl : ∀ m (t : Tail) → Eraseᵀ m t t
  eraseᵀ-refl m t = eraseᵀ-agree (agreeᵀ-refl m t)

outer-⊒ : ∀ {Γ A B} op (g : A → Pos → Node Γ B) q ls ds (ρ : NEnv Γ) {h h′ : Events∞ A}
        → h ⊒ h′ → outerFrame op g false q ls ds ρ h ⊒ outerFrame op g false q ls ds ρ h′
outer-⊒ op g q ls ds ρ {h} {h′} (ld , hu , er) =
  go-lead (flatOp op) Q (poolT ds ρ) (liveˡ (map-lead (laneᴹ g ρ) ld)) (lanesL-refl (flatOp op) (states ls ρ)) ,
  (λ eq d → ∪-ne (hu (map-hush (laneᴹ g ρ) (force h) (proj₁ (go-hush (flatOp op) (just (outerOf g ρ h)) (states ls ρ) Q (poolT ds ρ) eq))) d)
                 (agreeᵀ-refl d (cuts (states ls ρ) ∪ poolT ds ρ))) ,
  λ n → whole-erase (O n) (lanesE-refl n (states ls ρ)) (eraseᵀ-refl n (poolT ds ρ)) ,ᵉ
        go-erase (flatOp op) Q (O n) (lanesE-refl n (states ls ρ)) (eraseᵀ-refl n (poolT ds ρ)) ≤-refl
  where
    Q = L.map (laneᴹ g ρ) q
    O = λ n → liveᴱ {e = outerOf g ρ h} {outerOf g ρ h′} (cutᵉ (er n) ,ᵉ map-erase (laneᴹ g ρ) (nowᵉ (er n)))

lanes-⊒ : ∀ {Γ A B} op (g : A → Pos → Node Γ B) d q (o : Node Γ A) pre post (ρ : NEnv Γ) {h h′ : Events∞ B}
        → h ⊒ h′ → lanesFrame op g d q o pre post true ρ h ⊒ lanesFrame op g d q o pre post true ρ h′
lanes-⊒ op g d q o pre post ρ {h} {h′} (ld , hu , er) =
  go-lead (flatOp op) Q T (outerL-refl (flatOp op) Oᴺ) (lanesL-++′ (lanesL-refl (flatOp op) Post) (ld ∷ˡ lanesL-refl (flatOp op) Pre)) ,
  (λ eq n → ∪-ne (agreeᵀ-refl n (cutᴼ Oᴺ))
                 (∪-ne (cuts-hole Post true Pre h h′ (hu (head-hush (force h) (hole (proj₂ (go-hush (flatOp op) Oᴺ (Post ++ h ∷ Pre) Q T eq))) ) n))
                       (agreeᵀ-refl n T))) ,
  λ n → whole-erase (outerE-refl n Oᴺ) (R n) (eraseᵀ-refl n T) ,ᵉ go-erase (flatOp op) Q (outerE-refl n Oᴺ) (R n) (eraseᵀ-refl n T) ≤-refl
  where
    Q    = L.map (laneᴹ g ρ) q
    Oᴺ   = outerᴺ g (outerG d o) ρ
    Post = states (lanesL post) ρ
    Pre  = states (lanesL pre) ρ
    T    = outerT d o ρ (poolRuns pre post true ρ h)
    R    = λ n → lanesE-++ (lanesE-refl n Post) (er n ∷ᴱ lanesE-refl n Pre)
    hole : All Hushed (Post ++ h ∷ Pre) → Hushed h
    hole a with ++⁻ʳ Post a
    ... | x ∷ _ = x
    lanesL-++′ : ∀ {as as′ bs bs′} → LanesL (flatOp op) as as′ → LanesL (flatOp op) bs bs′ → LanesL (flatOp op) (as ++ bs) (as′ ++ bs′)
    lanesL-++′ []ˡ      b = b
    lanesL-++′ (a ∷ˡ l) b = a ∷ˡ lanesL-++′ l b
