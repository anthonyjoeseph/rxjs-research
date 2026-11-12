{-# OPTIONS --guardedness #-}

-- A CLOSED PROGRAM'S NEXT ROW, DECIDED: past a position with finitely
-- many rows before it, the meaning's first row, or none (`next`).  With
-- `m` rows before `c`, a row past `c` with none between has `c` and those
-- `m` before it, so the meaning agrees there with its `suc m`-th
-- approximant (`denotation.Laws.from`) and with that approximant cut at
-- `m + 3` rows (`denotation.Laws.Cut.cut-ne`), whose rows are listed
-- exactly (`simultaneous.Listing.listC-exact`).  The cut's first row past
-- `c` is the meaning's; where the cut has none, a row of the meaning past
-- `c` with finitely many before it has a least one past `c` by induction
-- on how many, which the cut would show.  A row with no such count shows
-- one (`shows`): the meaning shows as its approximants do.
module simultaneous.NextRow where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length; filter)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁺)
open import Data.List.Properties using (filter-notAll)
open import Data.List.Relation.Unary.All using ([])
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.Any as Any
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-pred; n≤1+n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable.Core using (T?)

open import Tree using (Obs)
open import denotation.Position using (Pos; root; _<ᵖ_)
open import denotation.Events using (Timeline)
open import denotation.EmissionSet using (Ev; EmissionSet; _≺_; _≼_; Few; enter; ⟦_⟧; approx)
open import denotation.Laws using (from)
open import denotation.Laws.Modulus using (AgreeTo; upto; ≺-trans; ≺-irrefl; ≺→≼; ≼-refl; ≼-split; ≼-trans)
open import denotation.Laws.Worlds using (Ok; Hots; Shows; ⊑-refl)
open import denotation.Laws.Count using (Cov; cov-down; AgC; AgC-sym; AgC-trans; ag-cnt)
open import denotation.Laws.Cut using (capprox; cut-ne)
open import denotation.Laws.Shows using (FC)
open import denotation.Laws.ShowsEv using (sk-approx)
open import quickcheck.Tabled using (rows)
open import quickcheck.Tabled.Exact.Base using (Exact; sound; complete)
open import quickcheck.Tabled.Exact using ([])
open import simultaneous.Listing using (listC-ok; listC-exact)

module _ {A : Set} (o : Obs Timeline [] A) where
  private
    M : EmissionSet A
    M = enter (⟦ o ⟧ []) root

    T : ℕ → EmissionSet A
    T n = enter (approx n o []) root

    ok₀ : Ok (Hots []) root
    ok₀ = tt , λ ()

    cov : ∀ {q ks k} → k ∈ ks → Cov q ks k
    cov m = inj₂ (Any.map (λ { refl → ⊑-refl _ }) m)

    -- The positions listed before `w`, one of them `w`: fewer.
    Before : Pos → List Pos → List Pos
    Before w ws = filter (λ k → T? (k <ᵖ w)) ws

    fewer : ∀ {w} ws → w ∈ ws → suc (length (Before w ws)) ≤ length ws
    fewer {w} ws m = filter-notAll (λ k → T? (k <ᵖ w)) ws (Any.map (λ { refl → ≺-irrefl {w} }) m)

    before : ∀ {X : Set} {t : EmissionSet X} {w q ws} → (∀ {u e} → t u e → u ≺ q → u ∈ ws) → w ≺ q
           → ∀ {u e} → t u e → u ≺ w → u ∈ Before w ws
    before {w = w} {q} F wq {u} z uw = ∈-filter⁺ (λ k → T? (k <ᵖ w)) (F z (≺-trans {u} {w} {q} uw wq)) uw

  -- THE MEANING SHOWS: where the rows with finitely many before them that
  -- precede `v` are listed, `v` has finitely many before it, not not.  The
  -- approximant within the list's length shows, and each of its rows with
  -- finitely many before it is, by induction on how many, one of the
  -- meaning's, so listed.
  shows : Shows M
  shows {v} (ks , h) ¬F = sk-approx n n o [] (λ ()) root ok₀ fc λ F → ¬F (few-M F)
    where
      n : ℕ
      n = length ks

      ag : AgC n M (T n)
      ag = from n o [] (λ ()) root ok₀

      covered : ∀ j {q e} → T n q e → (ws : List Pos) → length ws ≤ j → (∀ {w e′} → T n w e′ → w ≺ q → w ∈ ws) → q ≺ v → Cov v ks q
      covered j {q} {e} x ws le F qv = cov (h mq fq qv)
        where
          below : ∀ {w e′} → T n w e′ → w ≺ q → Cov q ks w
          below {w} y wq = cov-down (sub j le) wq (≺→≼ {q} {v} qv)
            where
              sub : ∀ i → length ws ≤ i → Cov v ks w
              sub zero    le′ with ≤-trans (fewer ws (F y wq)) le′
              ... | ()
              sub (suc i) le′ = covered i y (Before w ws) (≤-pred (≤-trans (fewer ws (F y wq)) le′)) (before {t = T n} F wq) (≺-trans {w} {q} {v} wq qv)

          agq : AgreeTo q M (T n)
          agq = ag-cnt ag q (inj₂ (ks , ≤-refl , below))

          mq : M q e
          mq = proj₂ (upto agq {q} (≼-refl {q})) x

          fq : Few M q
          fq = ws , λ {w} y wq → F (proj₁ (upto agq {w} (≺→≼ {w} {q} wq)) y) wq

      fc : FC n (T n) v
      fc = ks , ≤-refl , λ x (ws , F) qv → covered (length ws) x ws ≤-refl F qv

      few-M : Few (T n) v → Few M v
      few-M (ws , F) = ws , λ {w} y wv → F (proj₁ (upto agv {w} (≺→≼ {w} {v} wv)) y) wv
        where
          agv : AgreeTo v M (T n)
          agv = ag-cnt ag v (inj₂ (ks , ≤-refl , λ {w} y wv → covered (length (Before w ws)) y (Before w ws) ≤-refl (before {t = T n} F wv) wv))

  -- THE NEXT ROW: past `c`, with finitely many rows before it, the least
  -- row and finitely many before it, or no row at all.
  next : ∀ {c} → Few M c
       → (Σ Pos λ r → Σ (Ev A) λ e → M r e × c ≺ r × Few M r × (∀ {y e′} → M y e′ → c ≺ y → y ≺ r → ⊥))
         ⊎ (∀ {r e} → M r e → c ≺ r → ⊥)
  next {c} (ks , h) = pick (first (rows L))
    where
      m : ℕ
      m = length ks

      N : ℕ
      N = suc (suc (suc m))

      C : EmissionSet A
      C = enter (capprox N (suc m) o []) root

      ag : AgC (suc m) M C
      ag = AgC-trans (from (suc m) o [] (λ ()) root ok₀) (AgC-sym (cut-ne {m = suc m} {N} ≤-refl (suc m) o [] (λ ()) root ok₀))

      lc = listC-ok N (suc m) o tt root

      L = proj₁ lc

      ex : Exact L C
      ex = listC-exact N (suc m) o [] root (proj₁ (proj₂ lc)) (proj₂ (proj₂ lc))

      -- The first row listed past `c`, or none.
      first : (xs : List (Pos × Ev A))
            → (Σ Pos λ r → Σ (Ev A) λ e → (r , e) ∈ xs × c ≺ r × (∀ {y e′} → (y , e′) ∈ xs → c ≺ y → r ≼ y))
              ⊎ (∀ {y e′} → (y , e′) ∈ xs → c ≺ y → ⊥)
      first [] = inj₂ λ ()
      first ((y , e) ∷ xs) with first xs | T? (c <ᵖ y)
      ... | inj₂ none | no ny = inj₂ λ { (here refl) cy → ny cy ; (there i) cy → none i cy }
      ... | inj₂ none | yes cy =
        inj₁ (y , e , here refl , cy , λ { (here refl) _ → ≼-refl {y} ; (there i) cy′ → ⊥-elim (none i cy′) })
      ... | inj₁ (r , e′ , i , cr , lst) | no ny =
        inj₁ (r , e′ , there i , cr , λ { (here refl) cy → ⊥-elim (ny cy) ; (there i′) cy → lst i′ cy })
      ... | inj₁ (r , e′ , i , cr , lst) | yes cy with T? (y <ᵖ r)
      ...   | yes yr = inj₁ (y , e , here refl , cy ,
        λ { (here refl) _ → ≼-refl {y} ; {y′} (there i′) cy′ → ≼-trans {y} {r} {y′} (≺→≼ {y} {r} yr) (lst i′ cy′) })
      ...   | no ry = inj₁ (r , e′ , there i , cr , λ { (here refl) _ → ry ; (there i′) cy′ → lst i′ cy′ })

      -- Before a row past `c` with none between: `c` and those before it.
      upto-c : ∀ {t : EmissionSet A} {r} → (∀ {y e} → t y e → y ≺ c → M y e)
             → (∀ {y e} → t y e → c ≺ y → y ≺ r → ⊥) → ∀ {y e} → t y e → y ≺ r → y ∈ c ∷ ks
      upto-c back gap {y} z yr with T? (y <ᵖ c)
      ... | yes yc = there (h (back z yc) yc)
      ... | no cy with ≼-split {c} {y} cy
      ...   | inj₁ cy′ = ⊥-elim (gap z cy′ yr)
      ...   | inj₂ refl = here refl

      agc : AgreeTo c M C
      agc = ag-cnt ag c (inj₁ (ks , n≤1+n m , λ y yc → cov (h y yc)))

      Listed₁ : Set
      Listed₁ = (Σ Pos λ r → Σ (Ev A) λ e → (r , e) ∈ rows L × c ≺ r × (∀ {y e′} → (y , e′) ∈ rows L → c ≺ y → r ≼ y))
                ⊎ (∀ {y e′} → (y , e′) ∈ rows L → c ≺ y → ⊥)

      pick : Listed₁ → (Σ Pos λ r → Σ (Ev A) λ e → M r e × c ≺ r × Few M r × (∀ {y e′} → M y e′ → c ≺ y → y ≺ r → ⊥))
                       ⊎ (∀ {r e} → M r e → c ≺ r → ⊥)
      pick (inj₁ (r , e , i , cr , lst)) = inj₁ (r , e , proj₂ (upto agr {r} (≼-refl {r})) (sound ex i) , cr , few-r , gapM)
        where
          gapC : ∀ {y e′} → C y e′ → c ≺ y → y ≺ r → ⊥
          gapC z cy yr = lst (complete ex z) cy yr

          agr : AgreeTo r M C
          agr = ag-cnt ag r (inj₂ (c ∷ ks , ≤-refl ,
                  λ z yr → cov (upto-c (λ {y} z′ yc → proj₂ (upto agc {y} (≺→≼ {y} {c} yc)) z′) gapC z yr)))

          gapM : ∀ {y e′} → M y e′ → c ≺ y → y ≺ r → ⊥
          gapM {y} z cy yr = gapC (proj₁ (upto agr {y} (≺→≼ {y} {r} yr)) z) cy yr

          few-r : Few M r
          few-r = c ∷ ks , upto-c (λ z _ → z) gapM
      pick (inj₂ none) = inj₂ λ {r} x cr → shows {r} (c ∷ ks , cover x cr) λ (ws , F) → counted (length ws) x cr ws ≤-refl F
        where
          -- A row past `c` with finitely many before it: by induction on
          -- how many, none lies between, so the cut shows it.
          counted : ∀ j {r e} → M r e → c ≺ r → (ws : List Pos) → length ws ≤ j → (∀ {w e′} → M w e′ → w ≺ r → w ∈ ws) → ⊥
          counted j {r} x cr ws le F = none (complete ex (proj₁ (upto agr {r} (≼-refl {r})) x)) cr
            where
              gap : ∀ {w e′} → M w e′ → c ≺ w → w ≺ r → ⊥
              gap {w} y cw wr = sub j le
                where
                  sub : ∀ i → length ws ≤ i → ⊥
                  sub zero    le′ with ≤-trans (fewer ws (F y wr)) le′
                  ... | ()
                  sub (suc i) le′ = counted i y cw (Before w ws) (≤-pred (≤-trans (fewer ws (F y wr)) le′)) (before {t = M} F wr)

              agr : AgreeTo r M C
              agr = ag-cnt ag r (inj₁ (c ∷ ks , ≤-refl , λ z yr → cov (upto-c (λ z′ _ → z′) gap z yr)))

          cover : ∀ {r e} → M r e → c ≺ r → ∀ {y e′} → M y e′ → Few M y → y ≺ r → y ∈ c ∷ ks
          cover x cr {y} z (ws , F) yr with T? (y <ᵖ c)
          ... | yes yc = there (h z yc)
          ... | no cy with ≼-split {c} {y} cy
          ...   | inj₁ cy′ = ⊥-elim (counted (length ws) z cy′ ws ≤-refl F)
          ...   | inj₂ refl = here refl
