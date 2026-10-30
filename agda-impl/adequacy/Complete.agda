{-# OPTIONS --guardedness #-}

-- THE COMPLETE HALF: whatever a reader of a program's rows meets, some run
-- shows — row by row, each the next a run shows once it has shown those
-- before.
module adequacy.Complete where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to tt₁)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; subst₂; sym; trans)

open import denotation.Events using (Pos; root)
open import denotation.EmissionSet using (Ev; out; end; EmissionSet; enter; ⟦_⟧; Seen)
open import denotation.Laws.Modulus using (≼-antisym)
open import denotation.Laws.Worlds using (InvAt)
open import denotation.Laws using (inv-⟦⟧)
open import denotation.Read using (Run; Meets; Visible; loud; cursor; []; _∷_)
import denotation.Read as Read
open import operation.PureObservable using (PureObs; module Machine; module Driver)
open Machine using (Conf; load; nx; cp) renaming (Shown to Shownᴹ)
open import adequacy.Rows using (Steps; conv; RT; Vis; Past; Lowest; Beyond; into; back; narrow; past-≃; _≃_; ≃-sym; []; tau;
  val; fin)
open _≃_
open import adequacy.Up using (≃-refl; ≃-trans)
open import adequacy.Inv using (Inv; inv)
open import adequacy.Sim using (sim-tau; sim-val; sim-fin; quiet-root; drained-quiet)

-- A run from `k` to `k′` showing `rs`.
data Path {R : Set} : Conf R → Shownᴹ R → Conf R → Set₁ where
  []  : ∀ {k} → Path k [] k
  tau : ∀ {k k′ k″ t rs} → Driver.step R k ≡ Driver.silent t k′ → Path k′ rs k″ → Path k rs k″
  val : ∀ {k k′ k″ t p a rs} → Driver.step R k ≡ Driver.value t p a k′ → Path k′ rs k″ → Path k ((p , nx a) ∷ rs) k″

_▸_ : ∀ {R} {k k′ k″ : Conf R} {rs rs′} → Path k rs k′ → Path k′ rs′ k″ → Path k (rs ++ rs′) k″
[]        ▸ q = q
tau e pth ▸ q = tau e (pth ▸ q)
val e pth ▸ q = val e (pth ▸ q)

then : ∀ {R} {k k′ : Conf R} {rs rs′} → Path k rs k′ → Steps k′ rs′ → Steps k (rs ++ rs′)
then []        st = st
then (tau e p) st = tau e (then p st)
then (val e p) st = val e (then p st)

-- What a run shows next.
data Next {R : Set} (k : Conf R) (p : Pos) : Ev R → Set₁ where
  more : ∀ {a k′} → Path k [ (p , nx a) ] k′ → Next k p (out a)
  done : Steps k [ (p , cp) ] → Next k p end

-- `k′` a silent step on from `k`.
_⇜_ : ∀ {R} → Conf R → Conf R → Set₁
_⇜_ {R} k′ k = Σ _ λ τ → Driver.step R k ≡ Driver.silent τ k′

postulate
  -- SILENT RUNS ARE FINITE: short of a row a reader meets next, a run
  -- takes finitely many silent steps.  Few rows lie before a met one, and
  -- a silent step drops rows or advances finitely much bookkeeping.
  silent-finite : ∀ {R} (o : PureObs [] R) {rs k p e} → Path (load o) rs k
                → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ]) → Acc _⇜_ k

module _ {R : Set} (o : PureObs [] R) where
  private
    t : EmissionSet R
    t = enter (⟦ o ⟧ []ᴬ) root

    join : ∀ {c} xs {ys} → Run t c xs → Run t (cursor c xs) ys → Run t c (xs ++ ys)
    join []       []      r = r
    join (_ ∷ xs) (h ∷ m) r = h ∷ join xs m r

    conv-++ : ∀ (xs ys : Shownᴹ R) → conv (xs ++ ys) ≡ conv xs ++ conv ys
    conv-++ []       ys = refl
    conv-++ (x ∷ xs) ys = cong (_ ∷_) (conv-++ xs ys)

    cursor-++ : ∀ c (xs ys : List (Pos × Ev R)) → cursor c (xs ++ ys) ≡ cursor (cursor c xs) ys
    cursor-++ c []             ys = refl
    cursor-++ c ((q , _) ∷ xs) ys = cursor-++ (just q) xs ys

    -- Nothing is met past the end.
    over : ∀ {p rs} → t p end → Run t (just p) rs → rs ≡ []
    over _  []                                = refl
    over tp ((((ty , _) , _) , vi , pq , _) ∷ _) = ⊥-elim (loud vi (quiet-root o tp ty pq))

    -- Along a run: the invariant, and the visible rows the program's past
    -- what it has shown.
    along : ∀ {k₀ rs k} c → Path k₀ rs k → Inv k₀ → Vis (RT k₀) ≃ Vis (Beyond t c) → Inv k × Vis (RT k) ≃ Vis (Beyond t (cursor c (conv rs)))
    along c []          i r = i , r
    along {k₀} c (tau {k′ = k₁} e pth) i r =
      let (i′ , q) = sim-tau i e
      in along c pth i′ (≃-trans {t = Vis (RT k₁)} {u = Vis (RT k₀)} {v = Vis (Beyond t c)} (≃-sym q) r)
    along {k₀} c (val {k′ = k₁} {p = p} e pth) i r =
      let (i′ , (v , _) , q) = sim-val i e
          cq = proj₂ (into c (proj₁ (to r v)))
      in along (just p) pth i′
           (≃-trans {t = Vis (RT k₁)} {u = Vis (Past p (RT k₀))} {v = Vis (Beyond t (just p))} (≃-sym q)
             (≃-trans {u = Vis (Past p (Beyond t c))} (past-≃ {t = RT k₀} {u = Beyond t c} {p = p} r) (narrow {t = t} c cq)))

    -- The row met next past `c`.
    Owed : Maybe Pos → Pos → Ev R → Set
    Owed c p e = Seen t p e × Visible e × Read.Least t c p

    -- The least visible row of a state, read as the program's past `c`,
    -- is the row met next.
    same : ∀ k c {p e q e′} → Vis (RT k) ≃ Vis (Beyond t c) → Owed c p e → Lowest (RT k) q e′ → p ≡ q × e ≡ e′
    same _ c r (((tp , _) , _) , vi , ap , lt) (v , lt′) =
      let (tq , cq) = into c (proj₁ (to r v))
          pq = ≼-antisym (lt tq (proj₂ v) cq) (lt′ (from r (back c tp ap , vi)))
      in pq , InvAt.func (inv-⟦⟧ o []ᴬ (λ ()) root (tt , λ ())) tp (subst (λ x → t x _) (sym pq) tq)

    -- From a state on the run, the row met next is the next shown.
    next : ∀ {k} c {p e} → Inv k → Vis (RT k) ≃ Vis (Beyond t c) → Owed c p e → Acc _⇜_ k → Next k p e
    next {k} c {p} {e} i r h@(((tp , _) , _) , vi , ap , _) (acc rec) = go (Driver.step R k) refl
      where
        go : ∀ x → Driver.step R k ≡ x → Next k p e
        go (Driver.silent τ k′) eq with next c (proj₁ (sim-tau i eq)) (≃-trans {t = Vis (RT k′)} {u = Vis (RT k)} {v = Vis (Beyond t c)} (≃-sym (proj₂ (sim-tau i eq))) r) h (rec (τ , eq))
        ... | more pth = more (tau eq pth)
        ... | done st  = done (tau eq st)
        go (Driver.value τ q a k′) eq =
          let (pq , ee) = same k c r h (proj₁ (proj₂ (sim-val i eq))) in subst₂ (Next k) (sym pq) (sym ee) (more (val eq []))
        go (Driver.complete q) eq =
          let (pq , ee) = same k c r h (sim-fin i eq) in subst₂ (Next k) (sym pq) (sym ee) (done (fin eq))
        go Driver.drained eq = ⊥-elim (drained-quiet i eq (from r (back c tp ap , vi)))

    -- The last row met.
    last : ∀ {c} xs {p e} → Run t c (xs ++ [ (p , e) ]) → Owed (cursor c xs) p e
    last []       (h ∷ []) = h
    last (_ ∷ xs) (_ ∷ m)  = last xs m

    progress : ∀ {rs k p e} → Path (load o) rs k → Meets t (conv rs ++ [ (p , e) ]) → Next k p e
    progress {rs} pth m =
      let (i , r) = along nothing pth (inv tt₁ (tt , (tt , λ ()))) (≃-refl {t = Vis (RT (load o))})
      in next (cursor nothing (conv rs)) i r (last {c = nothing} (conv rs) m) (silent-finite o pth m)

    -- Shown what was met so far, a run shows what is met next.
    go : ∀ {rs₀ k} → Path (load o) rs₀ k → Run t nothing (conv rs₀) → ∀ rs → Run t (cursor nothing (conv rs₀)) rs
       → Σ _ λ rs′ → Steps k rs′ × conv rs′ ≡ rs
    go pth met [] _ = [] , [] , refl
    go {rs₀} pth met ((p , e) ∷ rs) (h ∷ r) with progress pth (join (conv rs₀) met (h ∷ []))
    ... | done st = [ (p , cp) ] , st , cong ((p , end) ∷_) (sym (over (proj₁ (proj₁ (proj₁ h))) r))
    ... | more {a} pq =
      let (rs′ , st , eq) = go (pth ▸ pq) (subst (Run t nothing) (sym (conv-++ rs₀ _)) (join (conv rs₀) met (h ∷ []))) rs
                               (subst (λ c → Run t c rs) (sym (trans (cong (cursor nothing) (conv-++ rs₀ _)) (cursor-++ nothing (conv rs₀) _))) r)
      in (p , nx a) ∷ rs′ , then pq st , cong ((p , out a) ∷_) eq

  complete : ∀ {rs} → Meets t rs → Σ _ λ rs′ → Steps (load o) rs′ × conv rs′ ≡ rs
  complete {rs} m = go [] [] rs m
