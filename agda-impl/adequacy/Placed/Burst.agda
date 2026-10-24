{-# OPTIONS --guardedness #-}

module adequacy.Placed.Burst where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (+-monoʳ-<; <-≤-trans; <-irrefl)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All++⁺; ++⁻ˡ to All++⁻ˡ; ++⁻ʳ to All++⁻ʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_)

open import denotation.MonotonicList.Events using (Events; Events∞; Pos; From; out; skip; end; hush; ix; sub; last; tick; _<ᵖ_; <ᵖ-asym;
  <ᵖ-split; <ᵖ-trans; <ᵖ-irrefl; ≮-trans; <ᵖ-below; <ᵖ-step; Tail∞; pin; idle; _∪_)
open import denotation.MonotonicList using (Agree; out⁼; skip⁼; end⁼; hush⁼; tailᴱ)
import denotation.MonotonicList.Events as M
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import denotation.Denote using (flatOp) renaming (⟦_⟧ to ⟦_⟧ᴰ)
open import adequacy.Placed.Order using (Atop; Clear; Disjoint; Every; EveryT; Every∞; Ext; Ordered; Owned; Past; Prefix; Steady; Tagged; every; everyT-idle; everyT-mono; everyᵀ; ext; ext-irrefl; ordered; prefix-++; steady)
open import adequacy.Placed.Keys using (Mark; everyT-≈; ix-mark; last-mark; owned-trans; owned-weigh; prefix-refl; rest-agree; snoc-inj; tagged-prefix; tagged-sub; tagged-weigh; weigh; weighˡ)
open import adequacy.Placed.Rising using (AtopT; below-under)
open import adequacy.Placed.Trail using (FlatT; Marked; SortedT; Trail; Trailing; atopT-every; ext-prefix; flatT-idle; flatᵀ; inside-prefix; marked-cue; marks-past; marks-prefix; marks-under; past-noext; reshown; shown; sortedT-idle; sortedᵀ; trail; trailᶠ)
open import adequacy.Placed.FlatAfter using (Going; Head; take-ahead)

open Events∞
open Tail∞

------------------------------------------------------------------------
-- A tail run as events, against itself.

atopT-trans : ∀ k j t → j <ᵖ k ≡ false → AtopT j t → AtopT k t
atopT-trans k j (pin h _) jk a = ≮-trans k j h jk a
atopT-trans k j idle      jk a = tt

sorted-above : ∀ k t → SortedT t → AtopT k t → EveryT (λ j → j <ᵖ k ≡ false) t
everyᵀ (sorted-above k (pin j u) st a) = a , sorted-above k (later u) (proj₂ (sortedᵀ st)) (atopT-trans k j (later u) a (proj₁ (sortedᵀ st)))
everyᵀ (sorted-above k idle      st a) = tt

trail-tail : ∀ {A} t → SortedT t → FlatT t → Trail {A} (tailᴱ t) t
trail (trail-tail (pin k u) st ft) =
  st , record { everyᵀ = inj₁ (<ᵖ-irrefl k) , everyT-mono (λ j a → inj₁ a) (later u) (sorted-above k (later u) (proj₂ (sortedᵀ st)) (proj₁ (sortedᵀ st))) }
  , trail-tail (later u) (proj₂ (sortedᵀ st)) (proj₂ (flatᵀ ft))
trailᶠ (trail-tail (pin k u) st ft) = ft
trail (trail-tail idle st ft) = sortedT-idle , everyT-idle , tt
trailᶠ (trail-tail idle st ft) = flatT-idle

atop-tailᴱ : ∀ {A} k t → AtopT k t → Atop k (tailᴱ {A} t)
atop-tailᴱ k (pin h _) a = a
atop-tailᴱ k idle      a = tt

ordered-tail : ∀ {A} t → SortedT t → Ordered (tailᴱ {A} t)
ordered (ordered-tail (pin k u) st) = atop-tailᴱ k (later u) (proj₁ (sortedᵀ st)) , ordered-tail (later u) (proj₂ (sortedᵀ st))
ordered (ordered-tail idle      st) = tt

clear-tail : ∀ {A} k t → EveryT (λ h → ¬ Ext k h) t → Clear k (tailᴱ {A} t)
clear-tail k (pin h _) e = proj₁ (everyᵀ e)
clear-tail k idle      e = tt

steady-tail : ∀ {A} t → FlatT t → Steady (tailᴱ {A} t)
steady (steady-tail (pin k u) ft) = clear-tail k (later u) (proj₁ (flatᵀ ft)) , steady-tail (later u) (proj₂ (flatᵀ ft))
steady (steady-tail idle      ft) = tt

-- A source past its next step, from what its cut trails.
trailing-onward : ∀ {A} (σ : Events∞ A) e → force σ ≡ e → Trail e (cut σ) → Trailing (M′.onward∞ σ e)
trailing-onward σ (out _ _ s) _ tr = proj₁ (proj₂ (proj₂ (trail tr)))
trailing-onward σ (skip _ s)  _ tr = proj₂ (proj₂ (trail tr))
trailing-onward σ (end _)     _ tr = trail-tail (cut σ) (proj₁ (trail tr)) (trailᶠ tr)
trailing-onward σ hush        eq tr = subst (λ z → Trail z (cut σ)) (sym eq) tr

ordered-onward : ∀ {A} (σ : Events∞ A) e → force σ ≡ e → Trail e (cut σ) → Ordered e → Ordered (force (M′.onward∞ σ e))
ordered-onward σ (out _ _ s) _ tr o = proj₂ (ordered o)
ordered-onward σ (skip _ s)  _ tr o = proj₂ (ordered o)
ordered-onward σ (end _)     _ tr o = ordered-tail (cut σ) (proj₁ (trail tr))
ordered-onward σ hush        eq tr o = subst Ordered (sym eq) o

steady-onward : ∀ {A} (σ : Events∞ A) e → force σ ≡ e → Trail e (cut σ) → Steady e → Steady (force (M′.onward∞ σ e))
steady-onward σ (out _ _ s) _ tr st = proj₂ (steady st)
steady-onward σ (skip _ s)  _ tr st = proj₂ (steady st)
steady-onward σ (end _)     _ tr st = steady-tail (cut σ) (trailᶠ tr)
steady-onward σ hush        eq tr st = subst Steady (sym eq) st

-- Beside nothing running, a trail is its own.
trail-hushed : ∀ {B} t u (x : Events B) → EveryT (λ _ → ⊥) t → Trail x u → Trail x (t ∪ u)
trail-hushed idle      u x e tr = tr
trail-hushed (pin k _) u x e tr = ⊥-elim (proj₁ (everyᵀ e))

------------------------------------------------------------------------
-- No later step inside a pinned one.

past-on : ∀ {A} k n (x : Events A) → k <ᵖ n ≡ true → ¬ Ext k n → Past n x → Past k x
past-on k n (out h _ _) kn nx (nh , _) = <ᵖ-trans k n h kn nh , past-noext k n h kn nx (<ᵖ-asym n h nh)
past-on k n (skip h _)  kn nx (nh , _) = <ᵖ-trans k n h kn nh , past-noext k n h kn nx (<ᵖ-asym n h nh)
past-on k n (end h)     kn nx (nh , _) = <ᵖ-trans k n h kn nh , past-noext k n h kn nx (<ᵖ-asym n h nh)
past-on k n hush        kn nx p        = tt

-- A skip showing again where it stood.
Tie : ∀ {A} → Pos → Events A → Set
Tie k (skip n _) = n ≡ k
Tie k _          = ⊥

-- Past `k`'s subtree, or a skip at `k` again.
Fore : ∀ {A} → Pos → Events A → Set
Fore k e = Past k e ⊎ Tie k e

clear-fore : ∀ {A} n (x : Events A) → Clear n x → Atop n x → Fore n x
clear-fore n (out h _ _) c a = inj₁ c
clear-fore n (skip h _)  c a with <ᵖ-split n h a
... | inj₁ nh   = inj₁ (nh , c)
... | inj₂ refl = inj₂ refl
clear-fore n (end h)     c a = inj₁ c
clear-fore n hush        c a = inj₁ tt

fore-trans : ∀ {A} k n (x : Events A) → (k <ᵖ n ≡ true × ¬ Ext k n) ⊎ n ≡ k → Fore n x → Fore k x
fore-trans k n x          (inj₂ refl)       f           = f
fore-trans k n x          (inj₁ (kn , nx)) (inj₁ p)    = inj₁ (past-on k n x kn nx p)
fore-trans k n (skip h _) (inj₁ (kn , nx)) (inj₂ refl) = inj₁ (kn , nx)
fore-trans k n (out _ _ _) (inj₁ _) (inj₂ ())
fore-trans k n (end _)     (inj₁ _) (inj₂ ())
fore-trans k n hush        (inj₁ _) (inj₂ ())

fore-head : ∀ {A} k (e : Events A) → Fore k e → Head (λ h → ¬ Ext k h) e
fore-head k (out h _ _) (inj₁ p)    = proj₂ p
fore-head k (out h _ _) (inj₂ ())
fore-head k (skip h _)  (inj₁ p)    = proj₂ p
fore-head k (skip h _)  (inj₂ refl) = ext-irrefl k
fore-head k (end h)     (inj₁ p)    = proj₂ p
fore-head k (end h)     (inj₂ ())
fore-head k hush        f           = tt

------------------------------------------------------------------------
-- A SOURCE'S BURST, run on under `r`: in order, flat, and trailing
-- where the source's next step shows.

module Bursting (r : Pos) where

  -- `m` no later than where `e` next shows.
  Cue : ∀ {A} → Pos → Events A → Set
  Cue m = Head (λ h → (h ++ [ ix 0 ]) <ᵖ m ≡ false)

  cue-self : ∀ {A} (e : Events A) → Cue (M′.shownAt e) e
  cue-self (out k _ _) = <ᵖ-irrefl (k ++ [ ix 0 ])
  cue-self (skip k _)  = <ᵖ-irrefl (k ++ [ ix 0 ])
  cue-self (end k)     = <ᵖ-irrefl (k ++ [ ix 0 ])
  cue-self hush        = tt

  cue-on : ∀ {A} k m (x : Events A) → (k ++ [ ix 0 ]) <ᵖ m ≡ false → Atop k x → Cue m x
  cue-on k m (out n _ _) c a = ≮-trans m (k ++ [ ix 0 ]) (n ++ [ ix 0 ]) c (M.<ᵖ-shift n k a)
  cue-on k m (skip n _)  c a = ≮-trans m (k ++ [ ix 0 ]) (n ++ [ ix 0 ]) c (M.<ᵖ-shift n k a)
  cue-on k m (end n)     c a = ≮-trans m (k ++ [ ix 0 ]) (n ++ [ ix 0 ]) c (M.<ᵖ-shift n k a)
  cue-on k m hush        c a = tt

  shown-cue : ∀ {A} m (e : Events A) → M′.shownAt e <ᵖ m ≡ false → Cue m e
  shown-cue m (out _ _ _) c = c
  shown-cue m (skip _ _)  c = c
  shown-cue m (end _)     c = c
  shown-cue m hush        c = tt

  cue-shown : ∀ {A} m (e : Events A) → Going e → Cue m e → M′.shownAt e <ᵖ m ≡ false
  cue-shown m (out _ _ _) g c = c
  cue-shown m (skip _ _)  g c = c
  cue-shown m (end _)     g c = c
  cue-shown m hush        () c

  every-cue : ∀ {A} m (e : Events A) → Every (λ h → (h ++ [ ix 0 ]) <ᵖ m ≡ false) e → Cue m e
  every-cue m (out _ _ _) pe = proj₁ (every pe)
  every-cue m (skip _ _)  pe = proj₁ (every pe)
  every-cue m (end _)     pe = every pe
  every-cue m hush        pe = tt

  cue-down : ∀ {A} m m′ (e : Events A) → m <ᵖ m′ ≡ false → Cue m e → Cue m′ e
  cue-down m m′ (out k _ _) mm c = ≮-trans m′ m (k ++ [ ix 0 ]) mm c
  cue-down m m′ (skip k _)  mm c = ≮-trans m′ m (k ++ [ ix 0 ]) mm c
  cue-down m m′ (end k)     mm c = ≮-trans m′ m (k ++ [ ix 0 ]) mm c
  cue-down m m′ hush        mm c = tt

  -- Past an end, what it left running shows past it.
  cue-tail : ∀ {A} m c t → (c ++ [ ix 0 ]) <ᵖ m ≡ false → EveryT (λ j → c <ᵖ j ≡ true × Disjoint (c ++ [ ix 1 ]) j × ¬ Ext c j) t
           → Cue {A} m (tailᴱ t)
  cue-tail m c (pin j u) q e =
    ≮-trans m (c ++ [ ix 0 ]) (j ++ [ ix 0 ]) q
      (<ᵖ-asym (c ++ [ ix 0 ]) (j ++ [ ix 0 ]) (<ᵖ-trans (c ++ [ ix 0 ]) j (j ++ [ ix 0 ]) (marks-past j shown (proj₁ z) (proj₂ (proj₂ z))) (<ᵖ-below j [])))
    where z = proj₁ (everyᵀ e)
  cue-tail m c idle      q e = tt

  -- A source past its next step shows no earlier.
  cue-onward : ∀ {A} m (σ : Events∞ A) e → force σ ≡ e → Trail e (cut σ) → Ordered e → Cue m e → Cue m (force (M′.onward∞ σ e))
  cue-onward m σ (out k _ s) _  tr o c = cue-on k m (force s) c (proj₁ (ordered o))
  cue-onward m σ (skip k s)  _  tr o c = cue-on k m (force s) c (proj₁ (ordered o))
  cue-onward m σ (end c)     _  tr o q = cue-tail m c (cut σ) q (proj₁ (proj₂ (trail tr)))
  cue-onward m σ hush        eq tr o c = subst (Cue m) (sym eq) c

  cue-marked : ∀ k m → (k ++ [ ix 0 ]) <ᵖ m ≡ false → Marked m k
  cue-marked k m c = marked-cue m shown c

  out-marked : ∀ k m → (k ++ [ ix 0 ]) <ᵖ m ≡ false → ∀ j → j <ᵖ k ≡ false × Disjoint k j → Marked m j
  out-marked k m c j (jk , d) = inj₁ (≮-trans m (k ++ [ ix 0 ]) j c (<ᵖ-step k j (take-ahead k j jk d)))

  skip-marked : ∀ k m → (k ++ [ ix 0 ]) <ᵖ m ≡ false → ∀ j → Marked k j → Marked m j
  skip-marked k m c j (inj₁ jk) with <ᵖ-split k j jk
  ... | inj₁ kj   = inj₁ (≮-trans m (k ++ [ ix 0 ]) j c (<ᵖ-step k j kj))
  ... | inj₂ refl = cue-marked k m c
  skip-marked k m c j (inj₂ mk) = marked-cue m (reshown mk) c

  end-marked : ∀ c m → (c ++ [ ix 0 ]) <ᵖ m ≡ false → ∀ j → c <ᵖ j ≡ true × Disjoint (c ++ [ ix 1 ]) j × ¬ Ext c j → Marked m j
  end-marked c m q j (cj , _ , nx) = inj₁ (≮-trans m (c ++ [ ix 0 ]) j q (<ᵖ-asym (c ++ [ ix 0 ]) j (marks-past j shown cj nx)))

  mutual
    lead-run : ∀ {A} m (e : Events A) t → Trail e t → Ordered e → Cue m e → EveryT (Marked m) (M′.runOn r e t)
    lead-run m (out k _ s) t tr o c =
      lead-pinned m k s t (M.inside r k) (cue-marked k m c) (proj₁ (proj₂ (proj₂ (trail tr)))) (proj₂ (ordered o))
        (cue-on k m (force s) c (proj₁ (ordered o))) (everyT-mono (out-marked k m c) t (proj₁ (proj₂ (trail tr))))
    lead-run m (skip k s)  t tr o c =
      lead-pinned m k s t (M.inside r k) (cue-marked k m c) (proj₂ (proj₂ (trail tr))) (proj₂ (ordered o))
        (cue-on k m (force s) c (proj₁ (ordered o))) (everyT-mono (skip-marked k m c) t (proj₁ (proj₂ (trail tr))))
    lead-run m (end k)     t tr o c = everyT-mono (end-marked k m c) t (proj₁ (proj₂ (trail tr)))
    lead-run m hush        t tr o c = everyT-mono (λ _ ()) t (proj₁ (proj₂ (trail tr)))

    lead-pinned : ∀ {A} m k (s : Events∞ A) t b → Marked m k → Trail (force s) (cut s) → Ordered (force s) → Cue m (force s)
                → EveryT (Marked m) t → EveryT (Marked m) (M′.pinned r k s t b)
    everyᵀ (lead-pinned m k s t true  mk tr o c et) = mk , lead-run m (force s) (cut s) tr o c
    everyᵀ (lead-pinned m k s t false mk tr o c et) = everyᵀ et

  -- Every step a run has yet to show, and every step any state of it
  -- would leave running, is marked by where it next shows.
  lead-cut : ∀ {A} m (e : Events A) t → Trail e t → Cue m e → EveryT (Marked m) t
  lead-cut m (out k _ s) t tr c = everyT-mono (out-marked k m c) t (proj₁ (proj₂ (trail tr)))
  lead-cut m (skip k s)  t tr c = everyT-mono (skip-marked k m c) t (proj₁ (proj₂ (trail tr)))
  lead-cut m (end k)     t tr c = everyT-mono (end-marked k m c) t (proj₁ (proj₂ (trail tr)))
  lead-cut m hush        t tr c = everyT-mono (λ _ ()) t (proj₁ (proj₂ (trail tr)))

  lead-every : ∀ {A} m (e : Events A) t → Trail e t → Ordered e → Cue m e → Every (Marked m) e
  every (lead-every m (out k _ s) t tr o c) =
    cue-marked k m c , lead-every m (force s) (cut s) tr′ (proj₂ (ordered o)) c′ , lead-cut m (force s) (cut s) tr′ c′
    where tr′ = proj₁ (proj₂ (proj₂ (trail tr)))
          c′  = cue-on k m (force s) c (proj₁ (ordered o))
  every (lead-every m (skip k s)  t tr o c) =
    cue-marked k m c , lead-every m (force s) (cut s) tr′ (proj₂ (ordered o)) c′ , lead-cut m (force s) (cut s) tr′ c′
    where tr′ = proj₂ (proj₂ (trail tr))
          c′  = cue-on k m (force s) c (proj₁ (ordered o))
  every (lead-every m (end k)     t tr o c) = cue-marked k m c
  every (lead-every m hush        t tr o c) = tt

  lead∞ : ∀ {A} m (s : Events∞ A) → Trailing s → Ordered (force s) → Cue m (force s) → Every∞ (Marked m) s
  lead∞ m s tr o c = lead-every m (force s) (cut s) tr o c , lead-cut m (force s) (cut s) tr c

  atopT-pin : ∀ {A} k n (s : Events∞ A) t b → n <ᵖ k ≡ false → (M.inside r n ≡ false → AtopT k t) → M.inside r n ≡ b
            → AtopT k (M′.pinned r n s t b)
  atopT-pin k n s t true  a f ib = a
  atopT-pin k n s t false a f ib = f ib

  skip-atop : ∀ k n → n <ᵖ k ≡ false → M.inside r k ≡ true → M.inside r n ≡ false → ∀ j → Marked n j → j <ᵖ k ≡ false
  skip-atop k n a ik nb j (inj₁ jn) = ≮-trans k n j a jn
  skip-atop k n a ik nb j (inj₂ mk) with j <ᵖ k in e
  ... | false = refl
  ... | true with () ← trans (sym (inside-prefix r k n ik (marks-under k mk e a))) nb

  -- What runs on past a pinned step comes no earlier.
  atopT-run : ∀ {A} k (e : Events A) t → Atop k e → Trail e t → M.inside r k ≡ true → AtopT k (M′.runOn r e t)
  atopT-run k (out n _ s) t a tr ik =
    atopT-pin k n s t (M.inside r n) a (λ _ → atopT-every k t (λ j tj → ≮-trans k n j a (proj₁ tj)) (proj₁ (proj₂ (trail tr)))) refl
  atopT-run k (skip n s)  t a tr ik =
    atopT-pin k n s t (M.inside r n) a (λ nb → atopT-every k t (skip-atop k n a ik nb) (proj₁ (proj₂ (trail tr)))) refl
  atopT-run k (end c)     t a tr ik = atopT-every k t (λ j tj → ≮-trans k c j a (<ᵖ-asym c j (proj₁ tj))) (proj₁ (proj₂ (trail tr)))
  atopT-run k hush        t a tr ik = atopT-every k t (λ j ()) (proj₁ (proj₂ (trail tr)))

  mutual
    sorted-run : ∀ {A} (e : Events A) t → Ordered e → Trail e t → SortedT (M′.runOn r e t)
    sorted-run (out n _ s) t o tr = sorted-pinned n s t (M.inside r n) refl (proj₂ (ordered o)) (proj₁ (ordered o)) (proj₁ (proj₂ (proj₂ (trail tr)))) (proj₁ (trail tr))
    sorted-run (skip n s)  t o tr = sorted-pinned n s t (M.inside r n) refl (proj₂ (ordered o)) (proj₁ (ordered o)) (proj₂ (proj₂ (trail tr))) (proj₁ (trail tr))
    sorted-run (end _)     t o tr = proj₁ (trail tr)
    sorted-run hush        t o tr = proj₁ (trail tr)

    sorted-pinned : ∀ {A} n (s : Events∞ A) t b → M.inside r n ≡ b → Ordered (force s) → Atop n (force s) → Trail (force s) (cut s)
                  → SortedT t → SortedT (M′.pinned r n s t b)
    sortedᵀ (sorted-pinned n s t true  ib o a tr st) = atopT-run n (force s) (cut s) a tr ib , sorted-run (force s) (cut s) o tr
    sortedᵀ (sorted-pinned n s t false ib o a tr st) = sortedᵀ st

  out-noext : ∀ {A} k n (a : A) (s : Events∞ A) → Fore k (out n a s) → ∀ j → j <ᵖ n ≡ false × Disjoint n j → ¬ Ext k j
  out-noext k n a s (inj₁ (kn , nx)) j (jn , _) = past-noext k n j kn nx jn
  out-noext k n a s (inj₂ ()) j _

  skip-noext : ∀ {A} k n (s : Events∞ A) → Fore k (skip n s) → M.inside r k ≡ true → M.inside r n ≡ false → ∀ j → Marked n j → ¬ Ext k j
  skip-noext k n s (inj₁ (kn , nx)) ik nb j (inj₁ jn) = past-noext k n j kn nx jn
  skip-noext k n s (inj₁ (kn , nx)) ik nb j (inj₂ mk) = λ x → nx (ext-prefix x (marks-prefix mk))
  skip-noext k n s (inj₂ refl)      ik nb j _ with () ← trans (sym ik) nb

  end-noext : ∀ {A} k c → Fore {A} k (end c) → ∀ j → c <ᵖ j ≡ true × Disjoint (c ++ [ ix 1 ]) j × ¬ Ext c j → ¬ Ext k j
  end-noext k c (inj₁ (kc , nx)) j (cj , _) = past-noext k c j kc nx (<ᵖ-asym c j cj)
  end-noext k c (inj₂ ()) j _

  out-fore : ∀ {A} k n (a : A) (s : Events∞ A) → Fore k (out n a s) → (k <ᵖ n ≡ true × ¬ Ext k n) ⊎ n ≡ k
  out-fore k n a s (inj₁ p) = inj₁ p
  out-fore k n a s (inj₂ ())

  mutual
    noext-run : ∀ {A} k (e : Events A) t → Fore k e → M.inside r k ≡ true → Ordered e → Steady e → Trail e t
              → EveryT (λ h → ¬ Ext k h) (M′.runOn r e t)
    noext-run k (out n a s) t f ik o st tr =
      noext-pin k n s t (M.inside r n) refl (fore-head k (out n a s) f) (fore-trans k n (force s) (out-fore k n a s f) (inj₁ (proj₁ (steady st))))
        ik (proj₂ (ordered o)) (proj₂ (steady st)) (proj₁ (proj₂ (proj₂ (trail tr))))
        (λ nb → everyT-mono (out-noext k n a s f) t (proj₁ (proj₂ (trail tr))))
    noext-run k (skip n s)  t f ik o st tr =
      noext-pin k n s t (M.inside r n) refl (fore-head k (skip n s) f)
        (fore-trans k n (force s) f (clear-fore n (force s) (proj₁ (steady st)) (proj₁ (ordered o))))
        ik (proj₂ (ordered o)) (proj₂ (steady st)) (proj₂ (proj₂ (trail tr)))
        (λ nb → everyT-mono (skip-noext k n s f ik nb) t (proj₁ (proj₂ (trail tr))))
    noext-run {A} k (end c) t f ik o st tr = everyT-mono (end-noext {A} k c f) t (proj₁ (proj₂ (trail tr)))
    noext-run k hush        t f ik o st tr = everyT-mono (λ j ()) t (proj₁ (proj₂ (trail tr)))

    noext-pin : ∀ {A} k n (s : Events∞ A) t b → M.inside r n ≡ b → ¬ Ext k n → Fore k (force s) → M.inside r k ≡ true
              → Ordered (force s) → Steady (force s) → Trail (force s) (cut s) → (M.inside r n ≡ false → EveryT (λ h → ¬ Ext k h) t)
              → EveryT (λ h → ¬ Ext k h) (M′.pinned r n s t b)
    everyᵀ (noext-pin k n s t true  ib nn f ik o st tr ft) = nn , noext-run k (force s) (cut s) f ik o st tr
    everyᵀ (noext-pin k n s t false ib nn f ik o st tr ft) = everyᵀ (ft ib)

  mutual
    flat-run : ∀ {A} (e : Events A) t → Ordered e → Steady e → Trail e t → FlatT (M′.runOn r e t)
    flat-run (out n _ s) t o st tr =
      flat-pin n s t (M.inside r n) refl (inj₁ (proj₁ (steady st))) (proj₂ (ordered o)) (proj₂ (steady st)) (proj₁ (proj₂ (proj₂ (trail tr)))) (trailᶠ tr)
    flat-run (skip n s)  t o st tr =
      flat-pin n s t (M.inside r n) refl (clear-fore n (force s) (proj₁ (steady st)) (proj₁ (ordered o)))
        (proj₂ (ordered o)) (proj₂ (steady st)) (proj₂ (proj₂ (trail tr))) (trailᶠ tr)
    flat-run (end _)     t o st tr = trailᶠ tr
    flat-run hush        t o st tr = trailᶠ tr

    flat-pin : ∀ {A} n (s : Events∞ A) t b → M.inside r n ≡ b → Fore n (force s) → Ordered (force s) → Steady (force s)
             → Trail (force s) (cut s) → FlatT t → FlatT (M′.pinned r n s t b)
    flatᵀ (flat-pin n s t true  ib f o st tr ft) = noext-run n (force s) (cut s) f ib o st tr , flat-run (force s) (cut s) o st tr
    flatᵀ (flat-pin n s t false ib f o st tr ft) = flatᵀ ft

------------------------------------------------------------------------
-- What a run leaves running, against what it last showed.

-- What `c` lies inside, keyed with none of `p`, came before `n`, or is a
-- bare tick.
Fresh : Pos → Pos → Pos → Set
Fresh p n c = ∀ k → Ext k c → ¬ Owned p k → k <ᵖ n ≡ true ⊎ Σ ℕ (λ t → k ≡ ix t ∷ [])

-- After each step a run shows, what it leaves running is fresh against it.
mutual
  Freshes : ∀ {A} → Pos → Events A → Set
  Freshes p (out n _ s) = EveryT (Fresh p n) (cut s) × FreshRun p (force s)
  Freshes p (skip n s)  = EveryT (Fresh p n) (cut s) × FreshRun p (force s)
  Freshes p (end _)     = ⊤
  Freshes p hush        = ⊤

  record FreshRun {A} (p : Pos) (e : Events A) : Set where
    coinductive
    field freshᴿ : Freshes p e

open FreshRun public

-- A state fresh against where it subscribed, and as it runs on.
Fresh∞ : ∀ {A} → Pos → Events∞ A → Set
Fresh∞ p σ = EveryT (Fresh p p) (cut σ) × FreshRun p (force σ)

-- Fresh against a step, fresh against any after it.
fresh-up : ∀ p n m c → n <ᵖ m ≡ true ⊎ n ≡ m → Fresh p n c → Fresh p m c
fresh-up p n m c nm f k x d with f k x d
... | inj₂ t  = inj₂ t
... | inj₁ kn with nm
...   | inj₁ lt   = inj₁ (<ᵖ-trans k n m kn lt)
...   | inj₂ refl = inj₁ kn

fresh-past : ∀ p n m c → m <ᵖ n ≡ false → Fresh p n c → Fresh p m c
fresh-past p n m c h = fresh-up p n m c (<ᵖ-split n m h)

-- Fresh against a step under `p`, fresh against `p`.
fresh-under : ∀ p ys c → Fresh p (p ++ ys) c → Fresh p p c
fresh-under p ys c f k x no with f k x no
... | inj₂ t  = inj₂ t
... | inj₁ kl = inj₁ (below-under p k ys (λ q → no (inj₁ q)) kl)

-- What an end left running, all past `m`, runs on fresh.
fresh-tail : ∀ {A} p m t → EveryT (Fresh p m) t → EveryT (λ k → m <ᵖ k ≡ true) t → FreshRun {A} p (tailᴱ t)
freshᴿ (fresh-tail p m (pin k u) ct mt) =
  everyT-mono (λ h → fresh-up p m k h (inj₁ (proj₁ (everyᵀ mt)))) (later u) (proj₂ (everyᵀ ct)) , fresh-tail p m (later u) (proj₂ (everyᵀ ct)) (proj₂ (everyᵀ mt))
freshᴿ (fresh-tail p m idle ct mt) = tt

mutual
  freshes-map : ∀ {A B} (f : A → B) p (x : Events A) → Freshes p x → Freshes p (M′.mapᴱ f x)
  freshes-map f p (out _ _ r) (c , t) = c , fresh-map f p (force r) t
  freshes-map f p (skip _ r)  (c , t) = c , fresh-map f p (force r) t
  freshes-map f p (end _)     t       = tt
  freshes-map f p hush        t       = tt

  fresh-map : ∀ {A B} (f : A → B) p (x : Events A) → FreshRun p x → FreshRun p (M′.mapᴱ f x)
  freshᴿ (fresh-map f p x t) = freshes-map f p x (freshᴿ t)

mutual
  freshes-scan : ∀ {A B} (f : B → A → B) z p (x : Events A) → Freshes p x → Freshes p (M′.scanᴱ f z x)
  freshes-scan f z p (out _ a r) (c , t) = c , fresh-scan f (f z a) p (force r) t
  freshes-scan f z p (skip _ r)  (c , t) = c , fresh-scan f z p (force r) t
  freshes-scan f z p (end _)     t       = tt
  freshes-scan f z p hush        t       = tt

  fresh-scan : ∀ {A B} (f : B → A → B) z p (x : Events A) → FreshRun p x → FreshRun p (M′.scanᴱ f z x)
  freshᴿ (fresh-scan f z p x t) = freshes-scan f z p x (freshᴿ t)

-- A take's last value shows just inside where the source's stood.
mutual
  fresh-take : ∀ {A} i (q : A → Bool) p (x : Events A) → FreshRun p x → FreshRun p (M′.takeWhileᴱ i q x)
  freshᴿ (fresh-take i q p (out k a r) t) = fresh-taking i q p k a (q a) r (freshᴿ t)
  freshᴿ (fresh-take i q p (skip k r)  t) = proj₁ (freshᴿ t) , fresh-take i q p (force r) (proj₂ (freshᴿ t))
  freshᴿ (fresh-take i q p (end k)     t) = tt
  freshᴿ (fresh-take i q p hush        t) = tt

  fresh-taking : ∀ {A} i (q : A → Bool) p k (a : A) b (r : Events∞ A) → Freshes p (out k a r) → Freshes p (M′.taking i q k a b r)
  fresh-taking i     q p k a true  r (c , t) = c , fresh-take i q p (force r) t
  fresh-taking true  q p k a false r (c , t) =
    everyT-mono (λ h → fresh-up p k (k ++ [ ix 0 ]) h (inj₁ (<ᵖ-below k []))) (cut r) c , record { freshᴿ = tt }
  fresh-taking false q p k a false r _       = tt

-- A cold leaf's run, a list's and a joiner's leave nothing running.
mutual
  fresh-frames : ∀ {A t} p τ e (m : From A t) → FreshRun p (M′.frames τ e m)
  fresh-frames p τ e M.done       = record { freshᴿ = tt }
  fresh-frames p τ e M.quiet      = record { freshᴿ = tt }
  fresh-frames p τ e (M.at t _ b) = fresh-burst p τ (ix (τ + t) ∷ sub e ∷ []) 0 b

  fresh-burst : ∀ {A t} p τ r i (b : M.Frame A t) → FreshRun p (M′.burst τ r i b)
  freshᴿ (fresh-burst p τ r i (M.emit a k)) = everyT-idle , fresh-burst p τ r (suc i) k
  freshᴿ (fresh-burst p τ r i (M.stall k))  = everyT-idle , fresh-burst p τ r (suc i) (M.Frame∞.force k)
  freshᴿ (fresh-burst p τ r i (M.close k))  = everyT-idle , fresh-frames p τ (r ++ [ last ]) (M.From∞.force k)

fresh-start : ∀ {Γ A} p (m : From A 0) (ρ : NEnv Γ) → Fresh∞ p (U.stateᴺ (U.startᶜ p m) ρ)
fresh-start p (M.at zero _ b)     ρ = everyT-idle , fresh-burst p (tick p) p 0 b
fresh-start p (M.at (suc t) le b) ρ = everyT-idle , fresh-frames p (tick p) (p ++ [ last ]) (M.at (suc t) le b)
fresh-start p M.done              ρ = everyT-idle , record { freshᴿ = tt }
fresh-start p M.quiet             ρ = everyT-idle , record { freshᴿ = tt }

fresh-of : ∀ {A} p q i (xs : List A) → FreshRun q (M′.ofᴱ p i xs)
freshᴿ (fresh-of p q i [])       = tt
freshᴿ (fresh-of p q i (x ∷ xs)) = everyT-idle , fresh-of p q (suc i) xs

mutual
  fresh-rejoin : ∀ {A} p q (e : Events A) → FreshRun q (M′.rejoin p e)
  fresh-rejoin p q (out j a k) = fresh-shown p q j (just a) k (p <ᵖ j)
  fresh-rejoin p q (skip j k)  = fresh-shown p q j nothing k (p <ᵖ j)
  fresh-rejoin p q (end c) with p <ᵖ c
  ... | true  = record { freshᴿ = tt }
  ... | false = record { freshᴿ = tt }
  fresh-rejoin p q hush        = record { freshᴿ = tt }

  fresh-shown : ∀ {A} p q j (a : Maybe A) (k : Events∞ A) b → FreshRun q (M′.shown p j a k b)
  freshᴿ (fresh-shown p q j (just a) k true)  = everyT-idle , fresh-rejoin p q (force k)
  freshᴿ (fresh-shown p q j nothing  k true)  = everyT-idle , fresh-rejoin p q (force k)
  freshᴿ (fresh-shown p q j (just a) k false) = everyT-idle , fresh-rejoin p q (force k)
  freshᴿ (fresh-shown p q j nothing  k false) = everyT-idle , fresh-rejoin p q (force k)

-- Freshness holds of what agrees with it at every depth, and of a
-- position owning less.
mutual
  fresh-≈ : ∀ {A} p (x y : Events A) → (∀ k → Agree k x y) → FreshRun p x → FreshRun p y
  freshᴿ (fresh-≈ p x y ag fr) = freshes-≈ p x y ag (ag 1) (freshᴿ fr)

  freshes-≈ : ∀ {A} p (x y : Events A) → (∀ k → Agree k x y) → Agree 1 x y → Freshes p x → Freshes p y
  freshes-≈ p (out _ _ l) (out _ _ r) ag (out⁼ _ _) (c , t) =
    everyT-≈ (cut l) (cut r) (λ k → M′.agree-tail (ag (suc k))) c , fresh-≈ p (force l) (force r) (λ k → rest-agree (ag (suc k))) t
  freshes-≈ p (skip _ l)  (skip _ r)  ag (skip⁼ _ _) (c , t) =
    everyT-≈ (cut l) (cut r) (λ k → M′.agree-tail (ag (suc k))) c , fresh-≈ p (force l) (force r) (λ k → rest-agree (ag (suc k))) t
  freshes-≈ p (end _)     (end _)     ag end⁼        t = tt
  freshes-≈ p hush        hush        ag hush⁼       t = tt

mutual
  fresh-widen : ∀ {A} p q → (∀ k → ¬ Owned p k → ¬ Owned q k) → (x : Events A) → FreshRun q x → FreshRun p x
  freshᴿ (fresh-widen p q w x fr) = freshes-widen p q w x (freshᴿ fr)

  freshes-widen : ∀ {A} p q → (∀ k → ¬ Owned p k → ¬ Owned q k) → (x : Events A) → Freshes q x → Freshes p x
  freshes-widen p q w (out _ _ r) (c , t) = everyT-mono (λ h f k x d → f k x (w k d)) (cut r) c , fresh-widen p q w (force r) t
  freshes-widen p q w (skip _ r)  (c , t) = everyT-mono (λ h f k x d → f k x (w k d)) (cut r) c , fresh-widen p q w (force r) t
  freshes-widen p q w (end _)     t       = tt
  freshes-widen p q w hush        t       = tt

owned-drop : ∀ k w h → Owned (k ++ w) h → Owned k h
owned-drop k w h = owned-trans k (k ++ w) h (inj₁ (prefix-++ k w))

-- Keyed under a position tagged with `p`: keyed under `p`.
mutual
  sub-owned : ∀ k p h → Owned (k ++ [ sub p ]) h → Owned p h
  sub-owned k p h (inj₁ pr) = inj₂ (tagged-prefix p (k ++ [ sub p ]) h (tagged-sub k p) pr)
  sub-owned k p h (inj₂ t)  = inj₂ (sub-tagged k p h t)

  sub-tagged : ∀ k p h → Tagged (k ++ [ sub p ]) h → Tagged p h
  sub-tagged k p []          ()
  sub-tagged k p (ix _ ∷ h)  t        = sub-tagged k p h t
  sub-tagged k p (last ∷ h)  t        = sub-tagged k p h t
  sub-tagged k p (sub j ∷ h) (inj₁ o) = inj₁ (sub-owned k p j o)
  sub-tagged k p (sub j ∷ h) (inj₂ t) = inj₂ (sub-tagged k p h t)

-- A position tagged with `p` outweighs it, and a step under `p` too.
heavy : ∀ k p → ¬ Owned (k ++ [ sub p ]) p
heavy k p o = <-irrefl refl (<-≤-trans (tagged-weigh p (k ++ [ sub p ]) (tagged-sub k p)) (owned-weigh _ _ o))

snoc-weigh : ∀ p (l : M.Label) → weigh p < weigh (p ++ [ l ])
snoc-weigh []      (ix _)  = s≤s z≤n
snoc-weigh []      (sub _) = s≤s z≤n
snoc-weigh []      last    = s≤s z≤n
snoc-weigh (a ∷ p) l       = +-monoʳ-< (weighˡ a) (snoc-weigh p l)

longer : ∀ p (l : M.Label) → ¬ Owned (p ++ [ l ]) p
longer p l o = <-irrefl refl (<-≤-trans (snoc-weigh p l) (owned-weigh _ _ o))

mark-sub : ∀ {l} → Mark l → ∀ j → sub j ≢ l
mark-sub (ix-mark _) j ()
mark-sub last-mark   j ()

snoc-ne : ∀ a b {l l′ : M.Label} → l ≢ l′ → a ++ [ l ] ≢ b ++ [ l′ ]
snoc-ne a b ne eq = ne (proj₂ (snoc-inj a b eq))

-- Neither a prefix of the other.
Unrelated : Pos → Pos → Set
Unrelated k h = ¬ Prefix k h × ¬ Prefix h k

ext-prefixed : ∀ {k h} → Ext k h → Prefix k h
ext-prefixed (ext l ls) = prefix-++ _ (l ∷ ls)

-- No later and no prefix is earlier.
strict : ∀ k q → q <ᵖ k ≡ false → ¬ Prefix k q → k <ᵖ q ≡ true
strict k q a np with <ᵖ-split k q a
... | inj₁ kq   = kq
... | inj₂ refl = ⊥-elim (np (prefix-refl k))
