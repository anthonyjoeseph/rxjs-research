{-# OPTIONS --guardedness #-}

-- THE LEAST MARK LEADS THE ROWS: whatever `seek` finds under a node is
-- keyed no later than every row the node still owes, and an event it
-- shows sits at that key, as a row.  Finding nothing, the node owes
-- nothing.  A merge's race is the only real case: the outer wins only
-- strictly before every lane, and a value it shows is a skip just past it.
module adequacy.Direct.Bound where

open import Data.Bool using (Bool; true; false; T; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; _≟_)
open import Data.List using (List; []; _∷_; _++_; [_]; lookup)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; pred; _≡ᵇ_; _≤_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.List.Properties using (++-identityʳ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Tree using (mergeᶠ)
open import denotation.MonotonicList using (ofᴱ)
open import denotation.MonotonicList.Events using (Pos; ix; last; _<ᵖ_; <ᵖ-asym; <ᵖ-split; <ᵖ-step; <ᵖ-shift; <ᵖ-below; <ᵖ-part; <ᵖ-ix; <ᵖ-irrefl)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; end; _≺_; _≼_; InE; at-out; at-end; on-out; MapT; map-out; map-skip; map-end)
open import operation.Key using (Key; at; after; _<ᴷ_)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; Cand; Found; found; Focus; Mark; Out; still; shows; seek; lanes; raceT; outerT; laneT; retag; first; mapT; cutT; shift; alive; outOf; ofM; closed;
                    ofS; doneS; mapS; cutS; lnS; flatS; inMap; inCut; inLn; inOuter; inLanes; nx; cp; attached; attAt; attM; pend) renaming (Ev to Evᴹ)
open import adequacy.Direct using (Frag; rows; rowsL; pendRows; toEv; Gone; module Flat)

------------------------------------------------------------------------
-- Keys

postulate
  ≮ᴷ-trans  : ∀ a b c → a <ᴷ b ≡ false → b <ᴷ c ≡ false → a <ᴷ c ≡ false
  <ᴷ-trans  : ∀ a b c → a <ᴷ b ≡ true → b <ᴷ c ≡ true → a <ᴷ c ≡ true
  <ᴷ-irrefl : ∀ k → k <ᴷ k ≡ false
  -- At a position, keys compare as positions do.
  at-<ᵖ     : ∀ p q → at p <ᴷ at q ≡ p <ᵖ q
  -- Just past a position, still before a mark's `after` the position is before.
  shift-after : ∀ q r → at q <ᴷ after r ≡ true → after r <ᴷ at (q ++ [ ix 0 ]) ≡ false

-- `a` no later than `b`.
record _⊑_ (a b : Key) : Set where
  constructor ⊑i
  field un : b <ᴷ a ≡ false
open _⊑_

⊑-refl : ∀ k → k ⊑ k
⊑-refl k = ⊑i (<ᴷ-irrefl k)

⊑-trans : ∀ {a b c} → a ⊑ b → b ⊑ c → a ⊑ c
⊑-trans {a} {b} {c} ab bc = ⊑i (≮ᴷ-trans c b a (un bc) (un ab))

clash : ∀ {b} → b ≡ true → b ≡ false → ⊥
clash refl ()

<→⊑ : ∀ a b → a <ᴷ b ≡ true → a ⊑ b
<→⊑ a b ab with b <ᴷ a in ba
... | false = ⊑i ba
... | true  = ⊥-elim (clash (<ᴷ-trans a b a ab ba) (<ᴷ-irrefl a))

T→≡ : ∀ {b} → T b → b ≡ true
T→≡ {true} _ = refl

≺→⊑ : ∀ {p q} → p ≺ q → at p ⊑ at q
≺→⊑ {p} {q} pq = ⊑i (trans (at-<ᵖ q p) (<ᵖ-asym p q (T→≡ pq)))

≼→⊑ : ∀ {p q} → p ≼ q → at p ⊑ at q
≼→⊑ {p} {q} pq with q <ᵖ p in e
... | false = ⊑i (trans (at-<ᵖ q p) e)
... | true  = ⊥-elim (pq tt)

⊑→≼ : ∀ {p q} → at p ⊑ at q → p ≼ q
⊑→≼ {p} {q} h qp = clash (T→≡ qp) (trans (sym (at-<ᵖ q p)) (un h))

-- Under a position is no earlier.
ext-⊑ : ∀ p x → at p ⊑ at (p ++ x)
ext-⊑ p []      rewrite ++-identityʳ p = ⊑-refl (at p)
ext-⊑ p (l ∷ x) = ⊑i (trans (at-<ᵖ (p ++ l ∷ x) p) (<ᵖ-asym p (p ++ l ∷ x) (<ᵖ-below p x)))

-- A lane's first effect is before its subscription.
ix01 : ∀ p → at (p ++ [ ix 0 ]) ⊑ at (p ++ [ ix 1 ])
ix01 p = ⊑i (trans (at-<ᵖ (p ++ [ ix 1 ]) (p ++ [ ix 0 ])) (<ᵖ-asym (p ++ [ ix 0 ]) (p ++ [ ix 1 ]) (<ᵖ-part p [] [] (<ᵖ-ix 0))))

-- Just past is no earlier.
shift-⊑ : ∀ h → h ⊑ shift h
shift-⊑ (at p)    = ext-⊑ p [ ix 0 ]
shift-⊑ (after p) = ⊑-refl (after p)

-- No earlier stays no earlier a step past each.
shift-≮ : ∀ q h → h ⊑ at q → shift h ⊑ at (q ++ [ ix 0 ])
shift-≮ q (at p)    u = ⊑i (trans (at-<ᵖ (q ++ [ ix 0 ]) (p ++ [ ix 0 ])) (<ᵖ-shift q p (trans (sym (at-<ᵖ q p)) (un u))))
shift-≮ q (after p) u = ⊑-trans u (ext-⊑ q [ ix 0 ])

-- Strictly before a key: just past it is no later.
shift-< : ∀ h k → h <ᴷ k ≡ true → shift h ⊑ k
shift-< (at q)    (at r)    h = ⊑i (trans (at-<ᵖ r (q ++ [ ix 0 ])) (<ᵖ-step q r (trans (sym (at-<ᵖ q r)) h)))
shift-< (at q)    (after r) h = ⊑i (shift-after q r h)
shift-< (after p) k         h = <→⊑ (after p) k h

-- Strictly past a position: no earlier than just past it.
past-⊑ : ∀ {p q} → at p ⊑ at q → ¬ p ≡ q → at (p ++ [ ix 0 ]) ⊑ at q
past-⊑ {p} {q} pq ne with <ᵖ-split p q (trans (sym (at-<ᵖ q p)) (un pq))
... | inj₁ lt = ⊑i (trans (at-<ᵖ q (p ++ [ ix 0 ])) (<ᵖ-step p q lt))
... | inj₂ eq = ⊥-elim (ne eq)

------------------------------------------------------------------------
-- What a found mark promises

Empty : ∀ {A} → EmissionSet A → Set
Empty t = ∀ {q e} → ¬ t q e

From : ∀ {A} → Key → EmissionSet A → Set
From K t = ∀ {q e} → t q e → K ⊑ at q

Single : ∀ {A} → EmissionSet A → Set
Single t = ∀ {q e e′} → t q e → t q e′ → e ≡ e′

-- Keyed `K`, the mark itself at `κ`, showing `o`.
record Bd {A : Set} (t : EmissionSet A) (κ K : Key) (o : Out A) : Set where
  field
    from  : From K t
    mark  : κ ⊑ K
    shown : ∀ {e} → o ≡ shows e → Σ Pos λ q → K ≡ at q × t q (toEv e)
open Bd

OK : ∀ {R A} → EmissionSet A → Maybe (Cand R A) → Set
OK t nothing                      = Empty t
OK t (just (found f m κ , K , o)) = Bd t κ K o

-- Over a list of lanes, by index.
OKL : ∀ {R B} → List (EmissionSet B) → Maybe (Cand R B) → Set
OKL Ls nothing                      = ∀ i → Empty (lookup Ls i)
OKL Ls (just (found f m κ , K , o)) =
  (∀ i → From K (lookup Ls i)) × κ ⊑ K × (∀ {e} → o ≡ shows e → Σ _ λ i → Σ Pos λ q → K ≡ at q × lookup Ls i q (toEv e))

------------------------------------------------------------------------
-- The node facts the race reads

record Counts {A B : Set} (O : EmissionSet A) (Ls : List (EmissionSet B)) (d : Bool) (n : ℕ) : Set where
  field
    -- No lane running: every lane begun has ended.
    none : n ≡ 0 → ∀ i → Empty (lookup Ls i)
    -- At most one running: any other lane begun has ended.
    one  : pred n ≡ 0 → ∀ i j → ¬ i ≡ j → ∀ {q e} → lookup Ls i q e → Empty (lookup Ls j)
    -- The outer done: it owes nothing.
    over : T d → Empty O

mutual
  Good : ∀ {Γ A} → St Γ A → Set
  Good (pend o)                                   = Frag o
  Good (ofS i p xs)                               = ⊤
  Good doneS                                      = ⊤
  Good (mapS f s)                                 = Good s
  Good (cutS l a s)                               = Good s
  Good (flatS (mergeᶠ nothing) f d n q o ls)      = Good o × GoodL ls × q ≡ [] × Single (rows o) × Counts (rows o) (rowsL ls) d n
  Good _                                          = ⊥

  GoodL : ∀ {Γ A} → List (St Γ A) → Set
  GoodL []       = ⊤
  GoodL (s ∷ ls) = GoodLn s × GoodL ls

  -- A lane: in its list, or out of it with its switch off.
  GoodLn : ∀ {Γ A} → St Γ A → Set
  GoodLn (lnS true s)                 = Good s
  GoodLn (lnS false (cutS false a s)) = Good s
  GoodLn _                            = ⊥

------------------------------------------------------------------------
-- An of

ofPos : ∀ {A : Set} → Pos → ℕ → List A → Pos
ofPos p i []      = p ++ [ last ]
ofPos p i (_ ∷ _) = p ++ [ ix i ]

of-from : ∀ {A} p i (xs : List A) → From (at (ofPos p i xs)) (InE (ofᴱ p i xs))
of-from p i []       at-end     = ⊑-refl _
of-from p i (x ∷ xs) at-out     = ⊑-refl _
of-from p i (x ∷ xs) (on-out r) = ⊑-trans (next xs) (of-from p (suc i) xs r)
  where
    next : ∀ {A : Set} (ys : List A) → at (p ++ [ ix i ]) ⊑ at (ofPos p (suc i) ys)
    next []      = ≺→⊑ (subst T (sym (<ᵖ-part p [] [] refl)) tt)
    next (_ ∷ _) = ≺→⊑ (subst T (sym (<ᵖ-part p [] [] (<ᵖ-ix i))) tt)

of-shows : ∀ {R Γ A} (c : Ctx R Γ A) i p (xs : List A) {e} → outOf c (ofS i p xs) ofM ≡ shows e → InE (ofᴱ p i xs) (ofPos p i xs) (toEv e)
of-shows c i p []       eq with closed c
of-shows c i p []       ()   | true
of-shows c i p []       refl | false = at-end
of-shows c i p (x ∷ xs) eq with closed c
of-shows c i p (x ∷ xs) ()   | true
of-shows c i p (x ∷ xs) refl | false = at-out

------------------------------------------------------------------------
-- One child

-- A mark of the node's own, shown silently, before or after its child's.
own-first : ∀ {R A} {t : EmissionSet A} (fc : Focus R) (m : Mark) (κ : Key) (y : Maybe (Cand R A)) → OK t y → OK t (first (just (found fc m κ , κ , still)) y)
own-first fc m κ nothing            e = record { from = λ r → ⊥-elim (e r) ; mark = ⊑-refl _ ; shown = λ () }
own-first fc m κ (just (g′ , K , o)) b with K <ᴷ κ in lt
... | true  = b
... | false = record { from = λ r → ⊑-trans (⊑i lt) (from b r) ; mark = ⊑-refl _ ; shown = λ () }

-- Silent, a node owes nothing it shows; its key still bounds what it would.
silenced : ∀ {R A} {t : EmissionSet A} (y : Maybe (Cand R A)) → OK t y → OK {R} {A} (λ _ _ → ⊥) (retag (cutT false) y)
silenced nothing            _ = λ ()
silenced (just (g , K , o)) b = record { from = λ () ; mark = mark b ; shown = λ () }

kept : ∀ {R A} {t : EmissionSet A} (y : Maybe (Cand R A)) → OK t y → OK t (retag (cutT true) y)
kept nothing            b = b
kept (just (g , K , o)) b = b

mapped : ∀ {R A B} (f : A → B) {t : EmissionSet A} (y : Maybe (Cand R A)) → OK t y → OK (MapT f t) (retag (mapT f) y)
mapped f nothing e (map-out r) = e r
mapped f nothing e (map-skip r) = e r
mapped f nothing e (map-end r) = e r
mapped f (just (g , K , still)) b =
  record { from = λ { (map-out r) → from b r ; (map-skip r) → from b r ; (map-end r) → from b r } ; mark = mark b ; shown = λ () }
mapped f (just (g , K , shows (nx a))) b =
  record { from = λ { (map-out r) → from b r ; (map-skip r) → from b r ; (map-end r) → from b r } ; mark = mark b
         ; shown = λ { refl → let (q , k , r) = shown b refl in q , k , map-out r } }
mapped f (just (g , K , shows cp)) b =
  record { from = λ { (map-out r) → from b r ; (map-skip r) → from b r ; (map-end r) → from b r } ; mark = mark b
         ; shown = λ { refl → let (q , k , r) = shown b refl in q , k , map-end r } }

------------------------------------------------------------------------
-- The lanes, one by one

-- A lane read through its list's switch: an ended lane shows nothing.
lane-ok : ∀ {R Γ B} (s : St Γ B) (y : Maybe (Cand R B)) → OK (rows s) y → OK (rows s) (retag (cutT (alive s)) y)
lane-ok (lnS true s)  y b = kept y b
lane-ok (lnS false s) y b = silenced y b
lane-ok (ofS i p xs)          y b = kept y b
lane-ok doneS                 y b = kept y b
lane-ok (mapS f s)            y b = kept y b
lane-ok (cutS l a s)          y b = kept y b
lane-ok (flatS op f d n q o ls) y b = kept y b
lane-ok (Machine.pend o)      y b = kept y b
lane-ok (Machine.coldS v l)   y b = kept y b
lane-ok (Machine.scanS f z s) y b = kept y b
lane-ok (Machine.takeS i q w s) y b = kept y b
lane-ok (Machine.connS k o b′) y b = kept y b
lane-ok (Machine.joinS j g x ib) y b = kept y b

-- The first of a lane and the lanes after it.
lanes-first : ∀ {R B} {l : EmissionSet B} {Ls} (x y : Maybe (Cand R B)) → OK l x → OKL Ls y → OKL (l ∷ Ls) (first x y)
lanes-first nothing nothing ex ey = λ { zero → ex ; (suc i) → ey i }
lanes-first nothing (just (g , K , o)) ex (fy , my , sy) =
  (λ { zero r → ⊥-elim (ex r) ; (suc i) r → fy i r }) , my , λ eq → let (i , q , k , r) = sy eq in suc i , q , k , r
lanes-first (just (g , K , o)) nothing bx ey =
  (λ { zero r → from bx r ; (suc i) r → ⊥-elim (ey i r) }) , mark bx , λ eq → let (q , k , r) = shown bx eq in zero , q , k , r
lanes-first (just (g , K , o)) (just (g′ , K′ , o′)) bx (fy , my , sy) with K′ <ᴷ K in lt
... | true  = (λ { zero r → ⊑-trans (<→⊑ K′ K lt) (from bx r) ; (suc i) r → fy i r }) , my
            , λ eq → let (i , q , k , r) = sy eq in suc i , q , k , r
... | false = (λ { zero r → from bx r ; (suc i) r → ⊑-trans (⊑i lt) (fy i r) }) , mark bx
            , λ eq → let (q , k , r) = shown bx eq in zero , q , k , r

------------------------------------------------------------------------
-- The race

module Race {A B : Set} (L : A → Pos → EmissionSet B) (O : EmissionSet A) (Ls : List (EmissionSet B)) (d : Bool) (n : ℕ)
            (sO : Single O) (cn : Counts O Ls d n) where
  open Flat L O Ls
  open Counts cn

  -- Every row of the merge sits no earlier than some row of a part:
  -- `K` bounding the outer's and the lanes', it bounds the merge's.
  rows-from : ∀ K → From K O → (∀ i → From K (lookup Ls i)) → From K FlatR
  rows-from K fo fl (val r)          = ⊑-trans (fo r) (ext-⊑ _ [ ix 0 ])
  rows-from K fo fl (step r)         = fo r
  rows-from K fo fl (oend r _)       = fo r
  rows-from K fo fl (opass r _)      = fo r
  rows-from K fo fl (lane r (_ , s) _) = ⊑-trans (fo r) (⊑-trans (ext-⊑ _ [ ix 1 ]) (≺→⊑ s))
  rows-from K fo fl (lend r (_ , s) _) = ⊑-trans (fo r) (⊑-trans (ext-⊑ _ [ ix 1 ]) (≺→⊑ s))
  rows-from K fo fl (lpass r (_ , s) _) = ⊑-trans (fo r) (⊑-trans (ext-⊑ _ [ ix 1 ]) (≺→⊑ s))
  rows-from K fo fl (run i r _)      = fl i r
  rows-from K fo fl (rend i r _)     = fl i r
  rows-from K fo fl (rpass i r _)    = fl i r

  -- The outer showing a value at `q₀`: every row sits just past it or later.
  past-val : ∀ {q₀ a} → O q₀ (out a) → From (at q₀) O → (∀ i → From (at (q₀ ++ [ ix 0 ])) (lookup Ls i)) → From (at (q₀ ++ [ ix 0 ])) FlatR
  past-val v fo fl (val r)          = shift-≮ _ (at _) (fo r)
  past-val v fo fl (step r)         = past-⊑ (fo r) λ { refl → skip≢ (sO v r) }
    where skip≢ : ∀ {a} → out a ≡ skip → ⊥
          skip≢ ()
  past-val v fo fl (oend r _)       = past-⊑ (fo r) λ { refl → end≢ (sO v r) }
    where end≢ : ∀ {a} → out a ≡ end → ⊥
          end≢ ()
  past-val v fo fl (opass r _)      = past-⊑ (fo r) λ { refl → end≢ (sO v r) }
    where end≢ : ∀ {a} → out a ≡ end → ⊥
          end≢ ()
  past-val v fo fl (lane r (_ , s) _) = ⊑-trans (shift-≮ _ (at _) (fo r)) (⊑-trans (ix01 _) (≺→⊑ s))
  past-val v fo fl (lend r (_ , s) _) = ⊑-trans (shift-≮ _ (at _) (fo r)) (⊑-trans (ix01 _) (≺→⊑ s))
  past-val v fo fl (lpass r (_ , s) _) = ⊑-trans (shift-≮ _ (at _) (fo r)) (⊑-trans (ix01 _) (≺→⊑ s))
  past-val v fo fl (run i r _)      = fl i r
  past-val v fo fl (rend i r _)     = fl i r
  past-val v fo fl (rpass i r _)    = fl i r

  -- The outer's end at `q₀` with no lane running ends the merge.
  outer-done : ∀ {q₀} → O q₀ end → From (at q₀) O → n ≡ 0 → Done q₀
  outer-done {q₀} r fo nz =
    inj₂ (q₀ , r , λ qq → clash (T→≡ qq) (<ᵖ-irrefl q₀)) ,
    (λ v lt → ⊥-elim (⊑→≼ (fo v) lt)) ,
    λ i → inj₁ (none nz i)

  -- A lane's end at `q`, the outer done and no other lane running, ends it.
  lane-done : ∀ {q} i → lookup Ls i q end → T d → pred n ≡ 0 → Done q
  lane-done {q} i r td pn =
    inj₁ (over td) ,
    (λ v _ → ⊥-elim (over td v)) ,
    λ j → gone j
    where
      gone : ∀ j → Gone (lookup Ls j) q
      gone j with i ≟ j
      ... | yes refl = inj₂ (q , r , λ qq → clash (T→≡ qq) (<ᵖ-irrefl q))
      ... | no ne    = inj₁ (one pn i j ne r)

  empty-flat : Empty O → (∀ i → Empty (lookup Ls i)) → Empty FlatR
  empty-flat eo el (val r)       = eo r
  empty-flat eo el (step r)      = eo r
  empty-flat eo el (oend r _)    = eo r
  empty-flat eo el (opass r _)   = eo r
  empty-flat eo el (lane r _ _)  = eo r
  empty-flat eo el (lend r _ _)  = eo r
  empty-flat eo el (lpass r _ _) = eo r
  empty-flat eo el (run i r _)   = el i r
  empty-flat eo el (rend i r _)  = el i r
  empty-flat eo el (rpass i r _) = el i r

  -- A lane winning, the outer no earlier.
  lane-wins : ∀ {R} (g : Found R) K (o′ : Out B) → From K O → OKL Ls (just (g , K , o′)) → OK FlatR (just (g , laneT {A = A} d n [] K o′))
  lane-wins g K still fo (fl , ml , sl) =
    record { from = rows-from K fo fl ; mark = ml ; shown = λ () }
  lane-wins g K (shows (nx b)) fo (fl , ml , sl) =
    record { from = rows-from K fo fl ; mark = ml
           ; shown = λ { refl → let (i , q , k , r) = sl refl in q , k , run i r tt } }
  lane-wins g K (shows cp) fo (fl , ml , sl) = ends d refl (pred n ≡ᵇ 0) refl
    where
      ends : ∀ b → d ≡ b → ∀ c → (pred n ≡ᵇ 0) ≡ c → OK FlatR (just (g , K , (if b ∧ c then shows cp else still)))
      ends true  de true  pn = record { from = rows-from K fo fl ; mark = ml
                                      ; shown = λ { refl → let (i , q , k , r) = sl refl in q , k , rend i r (lane-done i r (subst T (sym de) tt) (≡ᵇ⇒≡ (pred n) 0 (subst T (sym pn) tt))) } }
      ends true  de false pn = record { from = rows-from K fo fl ; mark = ml ; shown = λ () }
      ends false de c     pn = record { from = rows-from K fo fl ; mark = ml ; shown = λ () }

  -- The outer winning, the lanes no earlier than just past its key.
  outer-wins : ∀ {R} (f : Found R) h (o : Out A) → Bd O (Found.key f) h o → (∀ i → From (shift h) (lookup Ls i)) → OK FlatR (just (f , outerT n [] h o))
  outer-wins f h still b fl =
    record { from = rows-from h (from b) (λ i r → ⊑-trans (shift-⊑ h) (fl i r)) ; mark = mark b ; shown = λ () }
  outer-wins f h (shows (nx a)) b fl with shown b refl
  ... | q₀ , refl , v = record { from = past-val v (from b) fl ; mark = ⊑-trans (mark b) (shift-⊑ (at q₀)) ; shown = λ () }
  outer-wins f h (shows cp) b fl = ends (n ≡ᵇ 0) refl
    where
      ends : ∀ z → (n ≡ᵇ 0) ≡ z → OK FlatR (just (f , h , (if z ∧ true then shows cp else still)))
      ends false nz = record { from = rows-from h (from b) (λ i r → ⊑-trans (shift-⊑ h) (fl i r)) ; mark = mark b ; shown = λ () }
      ends true  nz with shown b refl
      ... | q₀ , refl , r = record { from = rows-from (at q₀) (from b) (λ i r′ → ⊑-trans (shift-⊑ (at q₀)) (fl i r′)) ; mark = mark b
                                   ; shown = λ { refl → q₀ , refl , oend r (outer-done r (from b) (≡ᵇ⇒≡ n 0 (subst T (sym nz) tt))) } }

  race-ok : ∀ {R} (x : Maybe (Cand R A)) (y : Maybe (Cand R B)) → OK O x → OKL Ls y → OK FlatR (raceT d n [] x y)
  race-ok nothing            nothing             eo el = empty-flat eo el
  race-ok nothing            (just (g , k , o′)) eo bl = lane-wins g k o′ (λ r → ⊥-elim (eo r)) bl
  race-ok (just (f , h , o)) nothing             b  el = outer-wins f h o b (λ i r → ⊥-elim (el i r))
  race-ok (just (f , h , o)) (just (g , k , o′)) b  bl with h <ᴷ k in lt
  ... | true  = outer-wins f h o b (λ i r → ⊑-trans (shift-< h k lt) (proj₁ bl i r))
  ... | false = lane-wins g k o′ (λ r → ⊑-trans (⊑i lt) (from b r)) bl

------------------------------------------------------------------------
-- Every node

mutual
  seek-ok : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Good s → OK (rows s) (seek c s)
  seek-ok c (ofS i p [])       _ = record { from = of-from p i [] ; mark = ⊑-refl _ ; shown = λ eq → _ , refl , of-shows c i p [] eq }
  seek-ok c (ofS i p (x ∷ xs)) _ = record { from = of-from p i (x ∷ xs) ; mark = ⊑-refl _ ; shown = λ eq → _ , refl , of-shows c i p (x ∷ xs) eq }
  seek-ok c doneS              _ = λ ()
  seek-ok c (pend o)           _ = λ ()
  seek-ok c (mapS f s)         g = mapped f (seek (inMap f c) s) (seek-ok (inMap f c) s g)
  seek-ok c (cutS true attached s)   g = kept (seek (inCut true attached c) s) (seek-ok (inCut true attached c) s g)
  seek-ok c (cutS false attached s)  g = silenced (seek (inCut false attached c) s) (seek-ok (inCut false attached c) s g)
  seek-ok c (cutS true (attAt p) s)  g =
    own-first (_ , _ , c , cutS true (attAt p) s) attM (after p) _ (kept (seek (inCut true (attAt p) c) s) (seek-ok (inCut true (attAt p) c) s g))
  seek-ok c (cutS false (attAt p) s) g =
    own-first (_ , _ , c , cutS false (attAt p) s) attM (after p) _ (silenced (seek (inCut false (attAt p) c) s) (seek-ok (inCut false (attAt p) c) s g))
  seek-ok c (flatS (mergeᶠ nothing) f d n .[] o ls) (go , gl , refl , sO , cn) =
    Race.race-ok (λ a → pendRows (f a)) (rows o) (rowsL ls) d n sO cn
      (seek (inOuter (mergeᶠ nothing) f d n [] ls c) o) (lanes c (mergeᶠ nothing) f d n [] o [] ls)
      (seek-ok (inOuter (mergeᶠ nothing) f d n [] ls c) o go) (lanes-ok c f d n o [] ls gl)

  seek-ln : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → GoodLn s → OK (rows s) (seek c s)
  seek-ln c (lnS true s)                 g = seek-ok (inLn true c) s g
  seek-ln c (lnS false (cutS false a s)) g = seek-ok (inLn false c) (cutS false a s) g

  lanes-ok : ∀ {R Γ A B} (c : Ctx R Γ B) f d n (o : St Γ A) pre (ls : List (St Γ B)) → GoodL ls
           → OKL (rowsL ls) (lanes c (mergeᶠ nothing) f d n [] o pre ls)
  lanes-ok c f d n o pre []         _          = λ ()
  lanes-ok c f d n o pre (s ∷ post) (gs , gp) =
    lanes-first (retag (cutT (alive s)) (seek (inLanes (mergeᶠ nothing) f d n [] o pre post c) s)) (lanes c (mergeᶠ nothing) f d n [] o (s ∷ pre) post)
      (lane-ok s _ (seek-ln (inLanes (mergeᶠ nothing) f d n [] o pre post c) s gs)) (lanes-ok c f d n o (s ∷ pre) post gp)
