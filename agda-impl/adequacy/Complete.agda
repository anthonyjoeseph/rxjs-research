{-# OPTIONS --guardedness #-}

-- THE COMPLETE HALF: whatever a reader of a program's rows meets, some run
-- shows — row by row, each the next a run shows once it has shown those
-- before.
module adequacy.Complete where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _<?_; s≤s; z≤n)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-pred; <-≤-trans; n≮0; m≤n⇒m≤1+n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; subst₂; sym; trans)
open import Relation.Nullary using (Dec; yes; no)

open import denotation.Events using (Pos; root; _≟ᵖ_)
open import denotation.EmissionSet using (Ev; out; end; EmissionSet; enter; ⟦_⟧; Seen; _≼_)
open import denotation.Laws.Modulus using (≼-antisym)
open import denotation.Laws.Worlds using (InvAt)
open import denotation.Laws using (inv-⟦⟧)
open import denotation.Read using (Run; Meets; Visible; loud; cursor; []; _∷_)
import denotation.Read as Read
open import operation.PureObservable using (PureObs; module Machine; module Driver)
open Machine using (Conf; load; nx; cp; absorbed) renaming (Shown to Shownᴹ)
open import operation.Key using (Key; at; _<ᴷ_; clash; ≮ᴷ-trans)
open import adequacy.Rows using (≼-≢; Steps; conv; Vis; Past; Lowest; Beyond; into; back; narrow; past-≃; _≃_; ≃-sym; ≃-trans; []; tau;
  val; fin)
open _≃_
open import adequacy.Simulation using (Simulation; quiet-root)
open import adequacy.Weight using (Clock; W; anc)

-- `a` no later than `b`.
record _⊑_ (a b : Key) : Set where
  constructor ⊑i
  field un : b <ᴷ a ≡ false

⊑-trans : ∀ {a b c} → a ⊑ b → b ⊑ c → a ⊑ c
⊑-trans {a} {b} {c} ab bc = ⊑i (≮ᴷ-trans c b a (_⊑_.un bc) (_⊑_.un ab))

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

_▸τ_ : ∀ {R} {k k′ k″ : Conf R} {rs} → Path k rs k′ → k″ ⇜ k′ → Path k rs k″
[]        ▸τ (_ , e) = tau e []
tau e pth ▸τ st      = tau e (pth ▸τ st)
val e pth ▸τ st      = val e (pth ▸τ st)

-- `k′` a silent step on from `k`, its clock passing no listed position.
Still : ∀ {R} → List Pos → Conf R → Conf R → Set₁
Still ks k′ k = k′ ⇜ k × (∀ {q} → q ∈ ks → Clock k <ᴷ at q ≡ true → Clock k′ <ᴷ at q ≡ true)

-- Of `qs`, those strictly past `κ`.
ahead : Key → List Pos → ℕ
ahead κ []       = 0
ahead κ (q ∷ qs) = if κ <ᴷ at q then suc (ahead κ qs) else ahead κ qs

-- Strictly past a later key: strictly past an earlier one.
past-earlier : ∀ {κ κ′} q → κ ⊑ κ′ → κ′ <ᴷ at q ≡ true → κ <ᴷ at q ≡ true
past-earlier {κ} q h p with κ <ᴷ at q in e
... | true  = refl
... | false = ⊥-elim (clash p (_⊑_.un (⊑-trans {at q} {κ} (⊑i e) h)))

ahead-mono : ∀ {κ κ′} → κ ⊑ κ′ → ∀ qs → ahead κ′ qs ≤ ahead κ qs
ahead-mono h [] = z≤n
ahead-mono {κ} {κ′} h (q ∷ qs) with κ′ <ᴷ at q in e′ | κ <ᴷ at q in e
... | true  | true  = s≤s (ahead-mono h qs)
... | true  | false = ⊥-elim (clash (past-earlier q h e′) e)
... | false | true  = m≤n⇒m≤1+n (ahead-mono h qs)
... | false | false = ahead-mono h qs

-- A later clock passing a listed row: fewer ahead.
ahead-drop : ∀ {κ κ′ q qs} → κ ⊑ κ′ → q ∈ qs → κ <ᴷ at q ≡ true → κ′ <ᴷ at q ≡ false → ahead κ′ qs < ahead κ qs
ahead-drop {qs = _ ∷ qs} h (here refl) p n rewrite p | n = s≤s (ahead-mono h qs)
ahead-drop {κ} {κ′} {qs = r ∷ _} h (there m) p n with κ′ <ᴷ at r in e′ | κ <ᴷ at r in e
... | true  | true  = s≤s (ahead-drop h m p n)
... | true  | false = ⊥-elim (clash (past-earlier r h e′) e)
... | false | true  = m≤n⇒m≤1+n (ahead-drop h m p n)
... | false | false = ahead-drop h m p n

postulate
  -- THE CLOCK NEVER RUNS BACK: short of a row a reader meets next, a silent
  -- step's clock is no earlier.  Mid-run the run's position leads every
  -- mark due, and every mark a step makes lies at or past it.
  -- DEAD ROUTE: the least mark due as the clock throughout.  A lane begun
  --   by an outer's value makes marks under that value, before the outer's
  --   next mark, so mid-run the least key falls.
  clock-mono : ∀ {R} (o : PureObs [] R) {rs k k′ p e} → Path (load o) rs k
             → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ]) → k′ ⇜ k → Clock k ⊑ Clock k′

  -- STILL STEPS LIGHTEN: short of a row a reader meets next, a step whose
  -- clock passes no row at or before it, nor any ancestor of one, lowers
  -- the run's weight — a climb by its height, a subscribe by its syntax,
  -- the run of a mark nothing above shows by the mark.
  still-lowers : ∀ {R} (o : PureObs [] R) {rs k k′ p e} → Path (load o) rs k
               → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
               → ∀ ks → (∀ {q e′} → enter (⟦ o ⟧ []ᴬ) root q e′ → q ≼ p → q ∈ ks)
               → Still (ks ++ anc ks) k′ k → W (ks ++ anc ks) p k′ < W (ks ++ anc ks) p k

-- STILL STEPS ARE FEW: short of a row a reader meets next, a run whose
-- clock passes no row at or before it, nor any ancestor of one, takes
-- finitely many steps.
still-finite : ∀ {R} (o : PureObs [] R) {rs k p e} → Path (load o) rs k
             → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
             → ∀ ks → (∀ {q e′} → enter (⟦ o ⟧ []ᴬ) root q e′ → q ≼ p → q ∈ ks) → Acc (Still (ks ++ anc ks)) k
still-finite o {rs} {k} {p} pth₀ m ks cov = go (<-wellFounded (W (ks ++ anc ks) p k)) pth₀
  where
    go : ∀ {k} → Acc _<_ (W (ks ++ anc ks) p k) → Path (load o) rs k → Acc (Still (ks ++ anc ks)) k
    go (acc r) pth = acc λ st → go (r (still-lowers o pth m ks cov st)) (pth ▸τ proj₁ st)

module _ {R : Set} (o : PureObs [] R) (S : Simulation o) where
  open Simulation S using (I; T; i₀; t₀; dry) renaming (tau to simτ; val to simval; fin to simfin)

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
    along : ∀ {k₀ rs k} c → Path k₀ rs k → (i : I k₀) → Vis (T i) ≃ Vis (Beyond t c)
          → Σ (I k) λ i′ → Vis (T i′) ≃ Vis (Beyond t (cursor c (conv rs)))
    along c []          i r = i , r
    along c (tau e pth) i r =
      let (i′ , q) = simτ i e
      in along c pth i′ (≃-trans {t = Vis (T i′)} {u = Vis (T i)} {v = Vis (Beyond t c)} (≃-sym q) r)
    along c (val {p = p} e pth) i r =
      let (i′ , (v , _) , q) = simval i e
          cq = proj₂ (into c (proj₁ (to r v)))
      in along (just p) pth i′
           (≃-trans {t = Vis (T i′)} {u = Vis (Past p (T i))} {v = Vis (Beyond t (just p))} (≃-sym q)
             (≃-trans {u = Vis (Past p (Beyond t c))} (past-≃ {t = T i} {u = Beyond t c} {p = p} r) (narrow {t = t} c cq)))

    -- The row met next past `c`.
    Owed : Maybe Pos → Pos → Ev R → Set
    Owed c p e = Seen t p e × Visible e × Read.Least t c p

    -- The least visible row of a state, read as the program's past `c`,
    -- is the row met next.
    same : ∀ {k} (i : I k) c {p e q e′} → Vis (T i) ≃ Vis (Beyond t c) → Owed c p e → Lowest (T i) q e′ → p ≡ q × e ≡ e′
    same _ c r (((tp , _) , _) , vi , ap , lt) (v , lt′) =
      let (tq , cq) = into c (proj₁ (to r v))
          pq = ≼-antisym (lt tq (proj₂ v) cq) (lt′ (from r (back c tp ap , vi)))
      in pq , InvAt.func (inv-⟦⟧ o []ᴬ (λ ()) root (tt , λ ())) tp (subst (λ x → t x _) (sym pq) tq)

    -- From a state on the run, the row met next is the next shown.
    next : ∀ {k} c {p e} → (i : I k) → Vis (T i) ≃ Vis (Beyond t c) → Owed c p e → Acc _⇜_ k → Next k p e
    next {k} c {p} {e} i r h@(((tp , _) , _) , vi , ap , _) (acc rec) = go (Driver.step R k) refl
      where
        go : ∀ x → Driver.step R k ≡ x → Next k p e
        go (Driver.silent τ k′) eq with simτ i eq
        ... | i′ , q with next c i′ (≃-trans {t = Vis (T i′)} {u = Vis (T i)} {v = Vis (Beyond t c)} (≃-sym q) r) h (rec (τ , eq))
        ...   | more pth = more (tau eq pth)
        ...   | done st  = done (tau eq st)
        go (Driver.value τ q a k′) eq =
          let (pq , ee) = same i c r h (proj₁ (proj₂ (simval i eq))) in subst₂ (Next k) (sym pq) (sym ee) (more (val eq []))
        go (Driver.complete q) eq =
          let (pq , ee) = same i c r h (simfin i eq) in subst₂ (Next k) (sym pq) (sym ee) (done (fin eq))
        go Driver.drained eq = ⊥-elim (dry i eq (from r (back c tp ap , vi)))

    -- The last row met.
    last : ∀ {c} xs {p e} → Run t c (xs ++ [ (p , e) ]) → Owed (cursor c xs) p e
    last []       (h ∷ []) = h
    last (_ ∷ xs) (_ ∷ m)  = last xs m

    -- SILENT RUNS ARE FINITE: short of a row a reader meets next, a run
    -- takes finitely many silent steps.  The fuel: the rows at or before
    -- the met one strictly past the clock, few by `Few`; a step passing
    -- none is still.
    -- DEAD ROUTE: a measure on the rows a silent step drops.  `of-next` reads
    --   an of's run as a full `≃` on rows, as do the subscribes and the climbs,
    --   so most silent steps drop no row and the measure never moves; a
    --   strengthened `Moves.silent` tracking dropped rows would fuel nothing.
    silent-finite : ∀ {rs k p e} → Path (load o) rs k → Meets t (conv rs ++ [ (p , e) ]) → Acc _⇜_ k
    silent-finite {rs} {k₀} {p} {e} pth₀ m = fuel _ ≤-refl (still-finite o pth₀ m ks₀ listed₀) pth₀
      where
        few = proj₂ (proj₁ (last {c = nothing} (conv rs) m))

        ks₀ : List Pos
        ks₀ = p ∷ proj₁ few

        ks : List Pos
        ks = ks₀ ++ anc ks₀

        μ : Conf R → ℕ
        μ k = ahead (Clock k) ks

        listed₀ : ∀ {q e′} → t q e′ → q ≼ p → q ∈ ks₀
        listed₀ {q} tq le with q ≟ᵖ p
        ... | yes refl = here refl
        ... | no ne    = there (proj₂ few tq (≼-≢ le ne))

        mutual
          fuel : ∀ n {k} → μ k ≤ n → Acc (Still ks) k → Path (load o) rs k → Acc _⇜_ k
          fuel n {k} le (acc rec) pth = acc λ {k′} st → on n le rec pth st (μ k′ <? μ k)

          on : ∀ n {k k′} → μ k ≤ n → (∀ {k″} → Still ks k″ k → Acc (Still ks) k″) → Path (load o) rs k → k′ ⇜ k
             → Dec (μ k′ < μ k) → Acc _⇜_ k′
          on zero    le _ _ _ (yes lt) = ⊥-elim (n≮0 (<-≤-trans lt le))
          on (suc n) le _ pth st (yes lt) = fuel n (≤-pred (≤-trans lt le)) (still-finite o (pth ▸τ st) m ks₀ listed₀) (pth ▸τ st)
          on n {k} {k′} le rec pth st (no ¬lt) = fuel n (≤-trans (ahead-mono h ks) le) (rec (st , kept)) (pth ▸τ st)
            where
              h = clock-mono o pth m st
              kept : ∀ {q} → q ∈ ks → Clock k <ᴷ at q ≡ true → Clock k′ <ᴷ at q ≡ true
              kept {q} mq c with Clock k′ <ᴷ at q in e′
              ... | true  = refl
              ... | false = ⊥-elim (¬lt (ahead-drop h mq c e′))

    progress : ∀ {rs k p e} → Path (load o) rs k → Meets t (conv rs ++ [ (p , e) ]) → Next k p e
    progress {rs} pth m =
      let (i , r) = along nothing pth i₀ t₀
      in next (cursor nothing (conv rs)) i r (last {c = nothing} (conv rs) m) (silent-finite pth m)

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
