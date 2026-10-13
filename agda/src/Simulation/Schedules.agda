------------------------------------------------------------------
-- TWO SCHEDULES IN STEP POP THE SAME ARRIVAL.  Two live lists, one per
-- machine, are in step when they pair up source for source, each pair
-- holding the same pending ticks, and each source ordered against every
-- later one the same way on both sides.  The scheduler pops the pending
-- arrival least by tick and then by ordinal, and nothing else it reads
-- differs between the two, so both pop the source at the same position,
-- at the same tick, and are left in step.
--
-- THE ORDINALS NEED NOT BE EQUAL, ONLY ORDERED ALIKE.  The elaboration
-- reads twice the slots the plain program does, so its dynamic sources
-- are numbered from a different seed; what the pop compares is the
-- order, and that is what the relation keeps.
--
-- WHAT A POP HANDS BACK IS GENERIC IN A RELATION ON THE SOURCES, which
-- is how the order reaches the recursion: popping the tail is asked to
-- return its winner related by "ordered against the head alike" as
-- well as by whatever the caller wanted.
------------------------------------------------------------------
module Simulation.Schedules where

open import Data.Bool    using (true; false; _∧_; _∨_)
open import Data.List    using (List; []; _∷_; map; null)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Nat     using (ℕ; _<ᵇ_; _≡ᵇ_)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Data.Empty   using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Rx.Exp       using (Ctx)
open import Rx.Evaluator using (LiveSource; Arrival; schedGo; schedHeadOf; schedEarlier)

ticks : ∀ {k} {Δ : Ctx k} → LiveSource Δ → List ℕ
ticks l = map proj₁ (LiveSource.pending l)

ord : ∀ {k} {Δ : Ctx k} → LiveSource Δ → ℕ
ord = LiveSource.ordinal

-- WHAT ONE POP READS OFF A SOURCE, read back: a source with nothing
-- pending offers nothing, and one with something offers its first tick
-- under its own ordinal and keeps the rest.
module _ {k} {Δ : Ctx k} where

  head-none : ∀ (l : LiveSource Δ) {u} → schedHeadOf l ≡ inj₁ u → map proj₁ (LiveSource.pending l) ≡ []
  head-none l eq with LiveSource.pending l
  head-none l refl | [] = refl

  head-some : ∀ (l : LiveSource Δ) {a l₂} → schedHeadOf l ≡ inj₂ (a , l₂)
            → map proj₁ (LiveSource.pending l) ≡ Arrival.tick a ∷ ticks l₂
            × Arrival.ordinal a ≡ ord l × ord l₂ ≡ ord l × Arrival.isLast a ≡ null (ticks l₂)
  head-some l eq with LiveSource.pending l
  head-some l refl | (t , v) ∷ ps = refl , refl , refl , null-map ps
    where
      null-map : ∀ {A : Set} (xs : List (ℕ × A)) → null xs ≡ null (map proj₁ xs)
      null-map []      = refl
      null-map (_ ∷ _) = refl

  -- the same ordinals, source for source: a pop changes only one pending list
  SameOrd : List (LiveSource Δ) → List (LiveSource Δ) → Set
  SameOrd = Pointwise (λ x y → ord x ≡ ord y)

  same-refl : ∀ (ls : List (LiveSource Δ)) → SameOrd ls ls
  same-refl []       = []
  same-refl (_ ∷ ls) = refl ∷ same-refl ls

-- the arrival a source offers
HeadOf : ∀ {k} {Δ : Ctx k} → LiveSource Δ → Arrival Δ → Set
HeadOf l a = Σ _ λ l₂ → schedHeadOf l ≡ inj₂ (a , l₂)

module _ {n m} {Γ : Ctx n} {Γ′ : Ctx m} where

  -- each later source on one side ordered against `l` as its partner is
  -- against `l′`
  Ranked : LiveSource Γ → LiveSource Γ′ → List (LiveSource Γ) → List (LiveSource Γ′) → Set
  Ranked l l′ = Pointwise (λ x x′ → (ord l <ᵇ ord x) ≡ (ord l′ <ᵇ ord x′))

  -- THE TWO LIVE LISTS IN STEP
  data Sync : List (LiveSource Γ) → List (LiveSource Γ′) → Set where
    []  : Sync [] []
    _∷_ : ∀ {l l′ ls ls′} → ticks l ≡ ticks l′ × Ranked l l′ ls ls′ → Sync ls ls′ → Sync (l ∷ ls) (l′ ∷ ls′)

  -- WHICH SOURCE EACH LIST GAVE UP A VALUE, AND THE ARRIVAL IT OFFERED:
  -- the same place in both, every other source left as it stood
  data PopPair : Arrival Γ → Arrival Γ′ → List (LiveSource Γ) → List (LiveSource Γ) → List (LiveSource Γ′) → List (LiveSource Γ′) → Set where
    here  : ∀ {l l₂ l′ l₂′ ls ls′ a a′} → schedHeadOf l ≡ inj₂ (a , l₂) → schedHeadOf l′ ≡ inj₂ (a′ , l₂′)
          → PopPair a a′ (l ∷ ls) (l₂ ∷ ls) (l′ ∷ ls′) (l₂′ ∷ ls′)
    there : ∀ {a a′ l l′ ls rs ls′ rs′} → PopPair a a′ ls rs ls′ rs′ → PopPair a a′ (l ∷ ls) (l ∷ rs) (l′ ∷ ls′) (l′ ∷ rs′)

  -- BOTH DRY, OR BOTH POP AT ONE TICK FROM PARTNERED SOURCES AND STAY IN
  -- STEP.  `R` is whatever the caller needs of the partners.
  data Popped (R : LiveSource Γ → LiveSource Γ′ → Set) (ls : List (LiveSource Γ)) (ls′ : List (LiveSource Γ′))
       : ⊤ ⊎ (Arrival Γ × List (LiveSource Γ)) → ⊤ ⊎ (Arrival Γ′ × List (LiveSource Γ′)) → Set where
    dry : Popped R ls ls′ (inj₁ tt) (inj₁ tt)
    pop : ∀ {a a′ rs rs′} {l l′}
        → Arrival.tick a ≡ Arrival.tick a′ → Arrival.isLast a ≡ Arrival.isLast a′
        → R l l′ → HeadOf l a → HeadOf l′ a′
        → SameOrd ls rs → SameOrd ls′ rs′ → Sync rs rs′ → PopPair a a′ ls rs ls′ rs′
        → Popped R ls ls′ (inj₂ (a , rs)) (inj₂ (a′ , rs′))

  ranked-moves : ∀ l l′ {ls rs : List (LiveSource Γ)} {ls′ rs′ : List (LiveSource Γ′)} → Ranked l l′ ls ls′ → SameOrd ls rs → SameOrd ls′ rs′ → Ranked l l′ rs rs′
  ranked-moves l l′ []       []       []         = []
  ranked-moves l l′ (q ∷ qs) (e ∷ es) (e′ ∷ es′) =
    trans (cong (ord l <ᵇ_) (sym e)) (trans q (cong (ord l′ <ᵇ_) e′)) ∷ ranked-moves l l′ qs es es′

  ranked-head : ∀ (l l₂ : LiveSource Γ) (l′ l₂′ : LiveSource Γ′) {ls ls′} → ord l₂ ≡ ord l → ord l₂′ ≡ ord l′ → Ranked l l′ ls ls′ → Ranked l₂ l₂′ ls ls′
  ranked-head l l₂ l′ l₂′ e e′ []                   = []
  ranked-head l l₂ l′ l₂′ e e′ (_∷_ {x} {x′} q qs) =
    trans (cong (_<ᵇ ord x) e) (trans q (cong (_<ᵇ ord x′) (sym e′))) ∷ ranked-head l l₂ l′ l₂′ e e′ qs

  both : ∀ {R S : LiveSource Γ → LiveSource Γ′ → Set} {ls ls′}
       → Pointwise R ls ls′ → Pointwise S ls ls′ → Pointwise (λ x x′ → R x x′ × S x x′) ls ls′
  both []       []       = []
  both (r ∷ rs) (s ∷ ss) = (r , s) ∷ both rs ss

  ∷-injʳ : ∀ {x y : ℕ} {xs ys : List ℕ} → x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
  ∷-injʳ refl = refl , refl

  nil≢cons : ∀ {x : ℕ} {xs : List ℕ} → [] ≡ x ∷ xs → ⊥
  nil≢cons ()

  -- the head's arrival against the tail's winner, alike on both sides
  earlier-alike : ∀ {l k : LiveSource Γ} {l′ k′ : LiveSource Γ′} {a b : Arrival Γ} {a′ b′ : Arrival Γ′}
                → Arrival.tick a ≡ Arrival.tick a′ → Arrival.tick b ≡ Arrival.tick b′
                → Arrival.ordinal a ≡ ord l → Arrival.ordinal a′ ≡ ord l′
                → Arrival.ordinal b ≡ ord k → Arrival.ordinal b′ ≡ ord k′
                → (ord l <ᵇ ord k) ≡ (ord l′ <ᵇ ord k′)
                → schedEarlier a b ≡ schedEarlier a′ b′
  earlier-alike {a = a} {a′} {b} {b′} ta tb oa oa′ ob ob′ q =
    cong₂ _∨_ (cong₂ _<ᵇ_ ta tb)
      (cong₂ _∧_ (cong₂ _≡ᵇ_ ta tb)
        (trans (cong₂ _<ᵇ_ oa ob) (trans q (sym (cong₂ _<ᵇ_ oa′ ob′)))))

  -- A POP OF TWO LISTS IN STEP
  sched-pop : ∀ {R ls ls′} → Sync ls ls′ → Pointwise R ls ls′ → Popped R ls ls′ (schedGo ls) (schedGo ls′)
  sched-pop [] [] = dry
  sched-pop {R} {l ∷ ls} {l′ ∷ ls′} ((tk , rk) ∷ s) (r ∷ rs)
    with schedHeadOf l in eh | schedHeadOf l′ in eh′ | schedGo ls | schedGo ls′ | sched-pop s (both rs rk)
  ... | inj₁ _ | inj₁ _ | .(inj₁ tt) | .(inj₁ tt) | dry = dry
  ... | inj₁ _ | inj₁ _ | .(inj₂ _) | .(inj₂ _) | pop ta la (rq , _) hb hb′ es es′ s′ pp =
        pop ta la rq hb hb′ (refl ∷ es) (refl ∷ es′) ((tk , ranked-moves l l′ rk es es′) ∷ s′) (there pp)
  ... | inj₁ _ | inj₂ _ | _ | _ | _ = ⊥-elim (nil≢cons (trans (sym (head-none l eh)) (trans tk (proj₁ (head-some l′ eh′)))))
  ... | inj₂ _ | inj₁ _ | _ | _ | _ = ⊥-elim (nil≢cons (trans (sym (head-none l′ eh′)) (trans (sym tk) (proj₁ (head-some l eh)))))
  ... | inj₂ (a , l₂) | inj₂ (a′ , l₂′) | .(inj₁ tt) | .(inj₁ tt) | dry =
        let (tl , oa , o₂ , la) = head-some l eh ; (tl′ , oa′ , o₂′ , la′) = head-some l′ eh′
            (ta , t₂) = ∷-injʳ (trans (sym tl) (trans tk tl′))
        in pop ta (trans la (trans (cong null t₂) (sym la′))) r (l₂ , eh) (l₂′ , eh′)
               (sym o₂ ∷ same-refl ls) (sym o₂′ ∷ same-refl ls′) ((t₂ , ranked-head l l₂ l′ l₂′ o₂ o₂′ rk) ∷ s) (here eh eh′)
  ... | inj₂ (a , l₂) | inj₂ (a′ , l₂′) | .(inj₂ (b , rs₂)) | .(inj₂ (b′ , rs₂′))
      | pop {a = b} {b′} {rs₂} {rs₂′} {k} {k′} tb lb (rq , ok) (k₂ , hk) (k₂′ , hk′) es es′ s′ pp
        with schedEarlier a b | schedEarlier a′ b′
           | earlier-alike {l = l} {k} {l′} {k′} {a} {b} {a′} {b′}
               (proj₁ (∷-injʳ (trans (sym (proj₁ (head-some l eh))) (trans tk (proj₁ (head-some l′ eh′))))))
               tb (proj₁ (proj₂ (head-some l eh))) (proj₁ (proj₂ (head-some l′ eh′)))
               (proj₁ (proj₂ (head-some k hk))) (proj₁ (proj₂ (head-some k′ hk′))) ok
  ...   | true  | true  | _ =
        let (tl , oa , o₂ , la) = head-some l eh ; (tl′ , oa′ , o₂′ , la′) = head-some l′ eh′
            (ta , t₂) = ∷-injʳ (trans (sym tl) (trans tk tl′))
        in pop ta (trans la (trans (cong null t₂) (sym la′))) r (l₂ , eh) (l₂′ , eh′)
               (sym o₂ ∷ same-refl ls) (sym o₂′ ∷ same-refl ls′) ((t₂ , ranked-head l l₂ l′ l₂′ o₂ o₂′ rk) ∷ s) (here eh eh′)
  ...   | false | false | _ =
        pop tb lb rq (k₂ , hk) (k₂′ , hk′) (refl ∷ es) (refl ∷ es′) ((tk , ranked-moves l l′ rk es es′) ∷ s′) (there pp)
  ...   | true  | false | ()
  ...   | false | true  | ()
