{-# OPTIONS --guardedness #-}

module adequacy.Placed.Calm where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Properties using (++-assoc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All++⁺; ++⁻ˡ to All++⁻ˡ; ++⁻ʳ to All++⁻ʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_)

open import denotation.MonotonicList.Events using (Events; Events∞; Pos; out; skip; end; hush; ix; _<ᵖ_; <ᵖ-split; <ᵖ-trans; <ᵖ-irrefl;
  <ᵖ-below; <ᵖ-step; Tail; Tail∞; pin; idle; _∪_)
open import denotation.MonotonicList using (MonotonicList; none; found)
import denotation.MonotonicList.Events as M
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import denotation.Denote using (flatOp) renaming (⟦_⟧ to ⟦_⟧ᴰ)
open import adequacy.Placed.Order using (Atop; Clear; Disjoint; Every; EveryT; Ext; Ordered; Owned; Past; Steady; every; everyᵀ; ext; ext-eq; ordered; owned-ext; prefix-++; prefix-trans; steady)
open import adequacy.Placed.Keys using (earliest-all; ix-mark; owned-trans; snoc-inj; tagged-++; tagged-mark)
open import adequacy.Placed.Rising using (AtopT; Atopᴹ; Beyond; apart-mark; ext-snoc; prefix-split; snoc-atop)
open import adequacy.Placed.Trail using (FlatT; SortedT; Sp; Trail; TrailE; disjoint-swap; trail; trailᶠ; t≢f)

open Events∞
open Tail∞

------------------------------------------------------------------------
-- An event's first, by whether it is a value and where.
At : ∀ {A} → (Bool → Pos → Set) → Events A → Set
At P (out h _ _) = P true h
At P (skip h _)  = P false h
At P (end h)     = P true h
At P hush        = ⊤

-- What a lane, the outer and the pool would show first in the merge.
LaneAt : ∀ {A B : Set} → (Bool → Pos → Set) → List A → Events B → Set
LaneAt P qs      (out h _ _) = P true h
LaneAt P qs      (skip h _)  = P false h
LaneAt P []      (end c)     = P true c
LaneAt P (_ ∷ _) (end c)     = P false (c ++ [ ix 0 ])
LaneAt P qs      hush        = ⊤

OuterAt : ∀ {A} → (Bool → Pos → Set) → Events A → Set
OuterAt P (out q _ _) = P false (q ++ [ ix 0 ])
OuterAt P (skip q _)  = P false q
OuterAt P (end c)     = P true c
OuterAt P hush        = ⊤

OuterAtᴹ : ∀ {A} → (Bool → Pos → Set) → Maybe (Events∞ A) → Set
OuterAtᴹ P nothing  = ⊤
OuterAtᴹ P (just e) = OuterAt P (force e)

PoolAt : (Bool → Pos → Set) → Tail → Set
PoolAt P (pin k _) = P false k
PoolAt P idle      = ⊤

-- An end shown as a step where other parts run on.
Down : (Bool → Pos → Set) → Set
Down P = ∀ h → P true h → P false h

first-lane : ∀ {B} P → Down P → ∀ op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t (x : Events B) → LaneAt P qs x
           → At P (M′.lane op o bs l as qs t x)
first-lane P dn op o        bs      l as      qs       t (out _ _ _) a = a
first-lane P dn op o        bs      l as      qs       t (skip _ _)  a = a
first-lane P dn op o        bs      l as      (m ∷ qs) t (end c)     a = a
first-lane P dn op nothing  []      l []      []       t (end c)     a = a
first-lane P dn op nothing  []      l (_ ∷ _) []       t (end c)     a = dn c a
first-lane P dn op nothing  (_ ∷ _) l as      []       t (end c)     a = dn c a
first-lane P dn op (just _) bs      l as      []       t (end c)     a = dn c a
first-lane P dn op o        bs      l as      qs       t hush        a = tt

first-outer : ∀ {B} P → Down P → ∀ op (e : Events∞ (MonotonicList B)) ls qs t (x : Events (MonotonicList B)) → OuterAt P x
            → At P (M′.outer op e ls qs t x)
first-outer P dn op e ls qs t (out q m r) a with M′.admit op (q ++ [ ix 1 ]) m ls qs
... | ls′ , qs′ , d = a
first-outer P dn op e ls       qs       t (skip q r) a = a
first-outer P dn op e []       []       t (end c)    a = a
first-outer P dn op e []       (m ∷ qs) t (end c)    a = dn c a
first-outer P dn op e (l ∷ ls) qs       t (end c)    a = dn c a
first-outer P dn op e ls       qs       t hush       a = tt

first-race : ∀ {B} P → Down P → ∀ op (o : Maybe (Events∞ (MonotonicList B))) k′ bs (l : Events∞ B) as qs t → LaneAt P qs (force l) → OuterAtᴹ P o
           → At P (M′.race op o k′ bs l as qs t)
first-race P dn op nothing  k′ bs l as qs t al ao = first-lane P dn op nothing bs l as qs t (force l) al
first-race P dn op (just e) k′ bs l as qs t al ao with M′.head (force e)
... | nothing = first-lane P dn op (just e) bs l as qs t (force l) al
... | just k″ with k″ <ᵖ k′
...   | true  = first-outer P dn op e (bs ++ l ∷ as) qs t (force e) ao
...   | false = first-lane P dn op (just e) bs l as qs t (force l) al

first-via : ∀ {B} P → Down P → ∀ op (o : Maybe (Events∞ (MonotonicList B))) ls qs t → OuterAtᴹ P o → At P (M′.viaOuter op o ls qs t)
first-via P dn op nothing  ls qs t ao = tt
first-via P dn op (just e) ls qs t ao = first-outer P dn op e ls qs t (force e) ao

first-parts : ∀ {B} P → Down P → ∀ op (o : Maybe (Events∞ (MonotonicList B))) ls qs t → All (λ l → LaneAt P qs (force l)) ls → OuterAtᴹ P o
            → At P (M′.parts op o ls qs t)
first-parts P dn op o ls qs t al ao with M′.earliest ls | earliest-all (λ l → LaneAt P qs (force l)) ls al
... | none             | _             = first-via P dn op o ls qs t ao
... | found k′ bs l as | (_ , al′ , _) = first-race P dn op o k′ bs l as qs t al′ ao

first-go : ∀ {B} P → Down P → ∀ op (o : Maybe (Events∞ (MonotonicList B))) ls qs t → All (λ l → LaneAt P qs (force l)) ls → OuterAtᴹ P o → PoolAt P t
         → At P (M′.go op o ls qs t)
first-go P dn op o ls qs idle      al ao at = first-parts P dn op o ls qs idle al ao
first-go P dn op o ls qs (pin k u) al ao at with M′.ahead-of k o ls
... | true  = at
... | false = first-parts P dn op o ls qs (pin k u) al ao

-- After an event at `k`, a value or not, the next: no earlier, past it
-- if either is a value, and never inside it.
Strict : Bool → Bool → Pos → Pos → Set
Strict true  _     k h = k <ᵖ h ≡ true
Strict false true  k h = k <ᵖ h ≡ true
Strict false false k h = ⊤

Clean : Bool → Pos → Bool → Pos → Set
Clean v k v′ h = Strict v v′ k h × ¬ Ext k h

Next : Bool → Pos → Bool → Pos → Set
Next v k v′ h = h <ᵖ k ≡ false × Clean v k v′ h

-- What a state would leave running, sorted, flat and trailing it.
Here : ∀ {A} → Events A → Tail → Set
Here x c = SortedT c × EveryT (TrailE x) c × FlatT c

mutual
  Calms : ∀ {A} → Events A → Set
  Calms (out k _ r) = EveryT (Disjoint k) (cut r) × At (Next true k) (force r) × Here (force r) (cut r) × Calm (force r)
  Calms (skip k r)  = At (Next false k) (force r) × Here (force r) (cut r) × Calm (force r)
  Calms (end _)     = ⊤
  Calms hush        = ⊤

  record Calm {A} (e : Events A) : Set where
    coinductive
    field calms : Calms e

open Calm public

next-atop : ∀ {A} v k (e : Events A) → At (Next v k) e → Atop k e
next-atop v k (out h _ _) n = proj₁ n
next-atop v k (skip h _)  n = proj₁ n
next-atop v k (end h)     n = proj₁ n
next-atop v k hush        n = tt

next-past : ∀ {A} k (e : Events A) → At (Next true k) e → Past k e
next-past k (out h _ _) n = proj₂ n
next-past k (skip h _)  n = proj₂ n
next-past k (end h)     n = proj₂ n
next-past k hush        n = tt

next-clear : ∀ {A} k (e : Events A) → At (Next false k) e → Clear k e
next-clear k (out h _ _) n = proj₂ n
next-clear k (skip h _)  n = proj₂ (proj₂ n)
next-clear k (end h)     n = proj₂ n
next-clear k hush        n = tt

calm-ordered : ∀ {A} (e : Events A) → Calm e → Ordered e
ordered (calm-ordered (out k _ r) c) = next-atop true k _ (proj₁ (proj₂ (calms c))) , calm-ordered _ (proj₂ (proj₂ (proj₂ (calms c))))
ordered (calm-ordered (skip k r)  c) = next-atop false k _ (proj₁ (calms c)) , calm-ordered _ (proj₂ (proj₂ (calms c)))
ordered (calm-ordered (end _)     c) = tt
ordered (calm-ordered hush        c) = tt

calm-steady : ∀ {A} (e : Events A) → Calm e → Steady e
steady (calm-steady (out k _ r) c) = next-past k _ (proj₁ (proj₂ (calms c))) , calm-steady _ (proj₂ (proj₂ (proj₂ (calms c))))
steady (calm-steady (skip k r)  c) = next-clear k _ (proj₁ (calms c)) , calm-steady _ (proj₂ (proj₂ (calms c)))
steady (calm-steady (end _)     c) = tt
steady (calm-steady hush        c) = tt

-- A calm run, each state leaving what trails it, trails from where it
-- does.
calm-trail : ∀ {A} (e : Events A) c → Here e c → Calm e → Trail e c
trail (calm-trail (out k _ r) c (st , et , ft) cm) = st , et , calm-trail (force r) (cut r) (proj₁ (proj₂ (proj₂ (calms cm)))) (proj₂ (proj₂ (proj₂ (calms cm)))) , proj₁ (calms cm)
trail (calm-trail (skip k r)  c (st , et , ft) cm) = st , et , calm-trail (force r) (cut r) (proj₁ (proj₂ (calms cm))) (proj₂ (proj₂ (calms cm)))
trail (calm-trail (end _)     c (st , et , ft) cm) = st , et , tt
trail (calm-trail hush        c (st , et , ft) cm) = st , et , tt
trailᶠ (calm-trail e c (st , et , ft) cm) = ft

-- What the merge's parts would show next, against an event at `k`.
Obl : ∀ {B} → Bool → Pos → Maybe (Events∞ (MonotonicList B)) → List (Events∞ B) → List (MonotonicList B) → Tail → Set
Obl v k o ls qs t = All (λ l → LaneAt (Clean v k) qs (force l)) ls × OuterAtᴹ (Clean v k) o × PoolAt (Clean v k) t

atop-laneAt : ∀ {A B : Set} k (qs : List A) (x : Events B) → Atop k x → LaneAt (λ _ h → h <ᵖ k ≡ false) qs x
atop-laneAt k qs      (out _ _ _) a = a
atop-laneAt k qs      (skip _ _)  a = a
atop-laneAt k []      (end c)     a = a
atop-laneAt k (_ ∷ _) (end c)     a = snoc-atop c (ix 0) k a
atop-laneAt k qs      hush        a = tt

laneAt-zip : ∀ {A B : Set} {P Q : Bool → Pos → Set} (qs : List A) (x : Events B) → LaneAt P qs x → LaneAt Q qs x
           → LaneAt (λ v h → P v h × Q v h) qs x
laneAt-zip qs      (out _ _ _) a b = a , b
laneAt-zip qs      (skip _ _)  a b = a , b
laneAt-zip []      (end c)     a b = a , b
laneAt-zip (_ ∷ _) (end c)     a b = a , b
laneAt-zip qs      hush        a b = tt

outerAt-next : ∀ {A} v k (x : Events A) → Atop k x → OuterAt (Clean v k) x → OuterAt (Next v k) x
outerAt-next v k (out q _ _) a n = snoc-atop q (ix 0) k a , n
outerAt-next v k (skip q _)  a n = a , n
outerAt-next v k (end c)     a n = a , n
outerAt-next v k hush        a n = tt

lanes-next : ∀ {A B : Set} v k (qs : List A) (ls : List (Events∞ B)) → All (λ l → Atop k (force l)) ls → All (λ l → LaneAt (Clean v k) qs (force l)) ls
           → All (λ l → LaneAt (Next v k) qs (force l)) ls
lanes-next v k qs []       []ᴬ       []ᴬ       = []ᴬ
lanes-next v k qs (l ∷ ls) (a ∷ᴬ as) (n ∷ᴬ ns) = laneAt-zip qs (force l) (atop-laneAt k qs (force l) a) n ∷ᴬ lanes-next v k qs ls as ns

outerᴹ-next : ∀ {B} v k (o : Maybe (Events∞ (MonotonicList B))) → Atopᴹ k o → OuterAtᴹ (Clean v k) o → OuterAtᴹ (Next v k) o
outerᴹ-next v k nothing  a n = tt
outerᴹ-next v k (just e) a n = outerAt-next v k (force e) a n

pool-next : ∀ v k t → AtopT k t → PoolAt (Clean v k) t → PoolAt (Next v k) t
pool-next v k (pin _ _) a n = a , n
pool-next v k idle      a n = tt

next-go : ∀ {B} v k op (o : Maybe (Events∞ (MonotonicList B))) ls qs t → All (λ l → Atop k (force l)) ls → Atopᴹ k o → AtopT k t
        → Obl v k o ls qs t → At (Next v k) (M′.go op o ls qs t)
next-go v k op o ls qs t al ao at (nl , no , np) =
  first-go (Next v k) dn op o ls qs t (lanes-next v k qs ls al nl) (outerᴹ-next v k o ao no) (pool-next v k t at np)
  where strict-down : ∀ v {h} → Strict v true k h → Strict v false k h
        strict-down true  s = s
        strict-down false s = tt
        dn : Down (Next v k)
        dn h (a , s , x) = a , strict-down v s , x

-- Strictly past `k`, and not inside it.
Aloof : Pos → Pos → Set
Aloof k h = k <ᵖ h ≡ true × ¬ Ext k h

clean-of : ∀ v v′ {k h} → Aloof k h → Clean v k v′ h
clean-of true  v′    a = a
clean-of false true  a = a
clean-of false false a = tt , proj₂ a

-- Keyed apart from what keys `k`, and no earlier: away from `k`.
apart-clean : ∀ r k h → Owned r k → ¬ Owned r h → h <ᵖ k ≡ false → Aloof k h
apart-clean r k h ok nh a with <ᵖ-split k h a
... | inj₁ kh   = kh , λ x → nh (owned-trans r k h ok (owned-ext x))
... | inj₂ refl = ⊥-elim (nh ok)

-- Aloof from `k`, so is the step just past `c`.
past-step : ∀ k c → Aloof k c → Aloof k (c ++ [ ix 0 ])
past-step k c (kc , nx) = <ᵖ-trans k c (c ++ [ ix 0 ]) kc (<ᵖ-below c []) , λ x → go (ext-snoc k c (ix 0) x)
  where go : Ext k c ⊎ k ≡ c → ⊥
        go (inj₁ e)    = nx e
        go (inj₂ refl) = t≢f (trans (sym kc) (<ᵖ-irrefl k))

-- Aloof from `c`, so from the step just past it.
ext-up : ∀ c x h → Ext (c ++ [ x ]) h → Ext c h
ext-up c x h e = subst (Ext c) (sym (trans (proj₂ (proj₂ (ext-eq e))) (++-assoc c [ x ] _))) (ext x _)

step-past : ∀ c h → Aloof c h → Aloof (c ++ [ ix 0 ]) h
step-past c h (ch , nx) with <ᵖ-split (c ++ [ ix 0 ]) h (<ᵖ-step c h ch)
... | inj₁ sh   = sh , λ e → nx (ext-up c (ix 0) h e)
... | inj₂ refl = ⊥-elim (nx (ext (ix 0) []))

-- What a lane or the outer shows first, read off its own first.
away-lane : ∀ {A B : Set} k (qs : List A) (x : Events B) → At (λ _ → Aloof k) x → LaneAt (λ _ → Aloof k) qs x
away-lane k qs      (out h _ _) a = a
away-lane k qs      (skip h _)  a = a
away-lane k []      (end c)     a = a
away-lane k (_ ∷ _) (end c)     a = past-step k c a
away-lane k qs      hush        a = tt

away-outer : ∀ {A} k (x : Events A) → At (λ _ → Aloof k) x → OuterAt (λ _ → Aloof k) x
away-outer k (out q _ _) a = past-step k q a
away-outer k (skip q _)  a = a
away-outer k (end c)     a = a
away-outer k hush        a = tt

at-apart : ∀ {A} r k (x : Events A) → Owned r k → Atop k x → Every (λ h → ¬ Owned r h) x → At (λ _ → Aloof k) x
at-apart r k (out h _ _) ok a al = apart-clean r k h ok (proj₁ (every al)) a
at-apart r k (skip h _)  ok a al = apart-clean r k h ok (proj₁ (every al)) a
at-apart r k (end c)     ok a al = apart-clean r k c ok (every al) a
at-apart r k hush        ok a al = tt

past-at : ∀ {A} k (x : Events A) → Past k x → At (λ _ → Aloof k) x
past-at k (out h _ _) pk = pk
past-at k (skip h _)  pk = pk
past-at k (end c)     pk = pk
past-at k hush        pk = tt

pool-apart : ∀ r k t → Owned r k → AtopT k t → EveryT (λ h → ¬ Owned r h) t → PoolAt (λ _ → Aloof k) t
pool-apart r k (pin h _) ok a al = apart-clean r k h ok (proj₁ (everyᵀ al)) a
pool-apart r k idle      ok a al = tt

laneAt-map : ∀ {A B : Set} {P Q : Bool → Pos → Set} → (∀ v h → P v h → Q v h) → (qs : List A) (x : Events B) → LaneAt P qs x → LaneAt Q qs x
laneAt-map f qs      (out h _ _) a = f true h a
laneAt-map f qs      (skip h _)  a = f false h a
laneAt-map f []      (end c)     a = f true c a
laneAt-map f (_ ∷ _) (end c)     a = f false (c ++ [ ix 0 ]) a
laneAt-map f qs      hush        a = tt

outerAt-map : ∀ {A} {P Q : Bool → Pos → Set} → (∀ v h → P v h → Q v h) → (x : Events A) → OuterAt P x → OuterAt Q x
outerAt-map f (out q _ _) a = f false (q ++ [ ix 0 ]) a
outerAt-map f (skip q _)  a = f false q a
outerAt-map f (end c)     a = f true c a
outerAt-map f hush        a = tt

poolAt-map : ∀ {P Q : Bool → Pos → Set} → (∀ v h → P v h → Q v h) → (t : Tail) → PoolAt P t → PoolAt Q t
poolAt-map f (pin k _) a = f false k a
poolAt-map f idle      a = tt

poolAt-∪ : ∀ (P : Bool → Pos → Set) t u → PoolAt P t → PoolAt P u → PoolAt P (t ∪ u)
poolAt-∪ P idle      u at au = au
poolAt-∪ P (pin k r) u at au = fst (M.sooner k u) u au
  where fst : ∀ b u → PoolAt P u → PoolAt P (M.first k r u b)
        fst true  u          au = at
        fst false idle       au = at
        fst false (pin k′ u) au = au

outerᴹ-map : ∀ {A} {P Q : Bool → Pos → Set} → (∀ v h → P v h → Q v h) → (o : Maybe (Events∞ A)) → OuterAtᴹ P o → OuterAtᴹ Q o
outerᴹ-map f nothing  a = tt
outerᴹ-map f (just e) a = outerAt-map f (force e) a

-- Past `k`, keying nothing under it: aloof from it.
at-beyond : ∀ {A} k (x : Events A) → Beyond k x → Every (λ h → ¬ Owned k h) x → At (λ _ → Aloof k) x
at-beyond k (out h _ _) b al = b , λ e → proj₁ (every al) (owned-ext e)
at-beyond k (skip h _)  b al = b , λ e → proj₁ (every al) (owned-ext e)
at-beyond k (end c)     b al = b , λ e → every al (owned-ext e)
at-beyond k hush        b al = tt

-- Apart from where a lane admitted at `x` keys, a position is spread
-- from `x`; and so is one apart from `x`.
sp-of : ∀ x y → Disjoint y (x ++ [ ix 1 ]) → Sp x y
sp-of x y d = disjoint-swap _ _ (apart-mark (x ++ [ ix 1 ]) y (ix 1) (ix-mark 1) (disjoint-swap _ _ d)) , proj₁ d

sp-apart : ∀ x y → Disjoint y x → Sp x y
sp-apart x y d = sp-of x y (apart-mark y x (ix 1) (ix-mark 1) d)

-- Keyed under a root apart from where `x`'s lane keys, and over
-- nothing of it.
sp-under : ∀ x j y → Owned j y → Disjoint j (x ++ [ ix 1 ]) → ¬ Owned (x ++ [ ix 1 ]) y → Sp x y
sp-under x j y o d n = sp-of x y ((λ o′ → proj₁ d (owned-trans j y _ o o′)) , n)

-- The step just past a position spread from `x` is.
sp-step : ∀ x h → Sp x h → Sp x (h ++ [ ix 0 ])
sp-step x h (d , n) = sp-of x (h ++ [ ix 0 ]) (fwd , bwd)
  where
    X = x ++ [ ix 1 ]
    fwd : ¬ Owned (h ++ [ ix 0 ]) X
    fwd o = n (owned-trans h (h ++ [ ix 0 ]) X (inj₁ (prefix-++ h [ ix 0 ])) o)
    bwd : ¬ Owned X (h ++ [ ix 0 ])
    bwd (inj₁ q) with prefix-split X h (ix 0) q
    ... | inj₁ q′ = proj₂ d (inj₁ (prefix-trans X h (h ++ [ ix 1 ]) q′ (prefix-++ h [ ix 1 ])))
    ... | inj₂ eq with snoc-inj x h eq
    ...   | _ , ()
    bwd (inj₂ t) = proj₂ d (inj₂ (tagged-++ X h [ ix 1 ] (tagged-mark X h (ix 0) (ix-mark 0) t)))
