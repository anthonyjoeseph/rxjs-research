{-# OPTIONS --guardedness #-}

module adequacy.Placed.Walk where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All++⁺; ++⁻ˡ to All++⁻ˡ; ++⁻ʳ to All++⁻ʳ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_)

open import denotation.MonotonicList.Events using (Events; Events∞; Pos; out; skip; end; hush; ix; _<ᵖ_; <ᵖ-asym; <ᵖ-split; <ᵖ-trans; ≮-trans;
  <ᵖ-below; Tail∞; pin; idle; _∪_)
open import denotation.MonotonicList using (tailᴱ)
import denotation.MonotonicList.Events as M
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import denotation.Denote using (flatOp) renaming (⟦_⟧ to ⟦_⟧ᴰ)
open import adequacy.Placed.Order using (Atop; Away; Clear; Every; EveryT; Every∞; Ext; Headed; Ordered; Owned; Past; Prefix; Steady; clear-away; every; every-mono; every-onward; everyT-burstOn; everyT-mono; everyT-∪; everyᵀ; every∞-mono; ext-eq; ordered; owned-ext; past-away; prefix-++; prefix-trans; steady; still; under-ext)
open import adequacy.Placed.Keys using (beneath-owned; every-ahead; ix-mark; owned-snoc; owned-tick; owned-trans; snoc-inj; tagged-lane; tagged-mark)
open import adequacy.Placed.Rising using (Disjoint; Rise; apart-mark; atop-ahead; before-atop; below-under; everyT-zip; every∞-zip; prefix-lt; prefix-rest; prefix-split)
open import adequacy.Placed.Trail using (Apart; FlatT; Marked; SortedT; Sp; Spread; Trail; TrailE; Trailing; flatT-∪; inside-under; marked-cue; marks-alien; marks-mid; marks-past; shown; sortedT-∪; spread; trail; trailᶠ; t≢f)
open import adequacy.Placed.Calm using (At; sp-of; sp-step)
open import adequacy.Placed.FlatAfter using (Going; Head; disjoint-snoc; take-ahead)
open import adequacy.Placed.Burst using (module Bursting; Fresh; FreshRun; Unrelated; ext-prefixed; fresh-past; fresh-tail; fresh-under; fresh-up; fresh-widen; freshᴿ; longer; ordered-onward; steady-onward; strict; trail-hushed; trailing-onward)

open Events∞
open Tail∞

------------------------------------------------------------------------
-- THE WALK: a connect's cuts trail its run at every reachable state.

module Walk {A B} (p : Pos) (hp : Headed p) where
  r P₀ : Pos
  r  = p ++ [ ix 1 ]
  P₀ = p ++ [ ix 0 ]

  rt : ∀ t → ¬ Owned r (ix t ∷ [])
  rt t = owned-tick p t hp

  open Bursting r

  record Side (β : Events∞ B) (σ : Events∞ A) : Set where
    field
      tb : Trailing β
      ts : Trailing σ
      os : Ordered (force σ)
      ss : Steady (force σ)
      kb : Every∞ (Owned P₀) β
      ks : Every∞ (Disjoint P₀) σ
      kr : Every∞ (Rise r) β
      hs : Every∞ Headed σ
      rs : Every∞ (Owned r) σ
      lf : Pos
      lo : Owned P₀ lf
      lc : Cue lf (force σ)
      fc : EveryT (Fresh P₀ lf) (cut β)
      fr : FreshRun P₀ (force β)

  -- What the source next shows is keyed with none of the body.
  shown-apart : ∀ (e : Events A) → Going e → Every (Disjoint P₀) e → ¬ Owned P₀ (M′.shownAt e)
  shown-apart (out k _ _) g pe = proj₁ (apart-mark P₀ k (ix 0) (ix-mark 0) (proj₁ (every pe)))
  shown-apart (skip k _)  g pe = proj₁ (apart-mark P₀ k (ix 0) (ix-mark 0) (proj₁ (every pe)))
  shown-apart (end k)     g pe = proj₁ (apart-mark P₀ k (ix 0) (ix-mark 0) (every pe))
  shown-apart hush        () pe

  -- Before the body's next, what it leaves running trails a skip.
  body-lead : ∀ q (x : Events B) c → M′.before q x ≡ true → Trail x c → EveryT (Marked q) c
  body-lead q (out k _ _) c qk tr = everyT-mono (λ j z → inj₁ (≮-trans q k j (<ᵖ-asym q k qk) (proj₁ z))) c (proj₁ (proj₂ (trail tr)))
  body-lead q (skip k _)  c qk tr = everyT-mono lead c (proj₁ (proj₂ (trail tr)))
    where lead : ∀ j → Marked k j → Marked q j
          lead j (inj₁ jk) = inj₁ (≮-trans q k j (<ᵖ-asym q k qk) jk)
          lead j (inj₂ mk) = marked-cue q mk (<ᵖ-asym q k qk)
  body-lead q (end k)     c qk tr = everyT-mono (λ j z → inj₁ (≮-trans q k j (<ᵖ-asym q k qk) (<ᵖ-asym k j (proj₁ z)))) c (proj₁ (proj₂ (trail tr)))
  body-lead q hush        c qk tr = everyT-mono (λ j ()) c (proj₁ (proj₂ (trail tr)))

  -- A body step `n` no later than the source's `q` comes before it.
  below : ∀ q n → ¬ Owned P₀ q → Owned P₀ n → q <ᵖ n ≡ false → n <ᵖ q ≡ true
  below q n nq on nl with <ᵖ-split n q nl
  ... | inj₁ x  = x
  ... | inj₂ eq = ⊥-elim (nq (subst (Owned P₀) eq on))

  -- A burst step the source has not passed lies nowhere before `n`.
  late : ∀ q n j → ¬ Owned P₀ q → Owned P₀ n → q <ᵖ n ≡ false → Disjoint P₀ j → Marked q j → j <ᵖ n ≡ true → ⊥
  late q n j nq on nl dj (inj₁ jq) jn with () ← trans (sym jq) (<ᵖ-trans j n q jn (below q n nq on nl))
  late q n j nq on nl dj (inj₂ mq) jn = marks-alien (marks-mid n mq jn nl) on dj

  -- A body step `n` before the source's `q`, beside a burst step `j`.
  module Pin q n j (nq : ¬ Owned P₀ q) (on : Owned P₀ n) (nl : q <ᵖ n ≡ false) (rn : Rise r n) (dj : Disjoint P₀ j) (hj : Headed j) (oj : Owned r j) where
    unowned : Marked q j → ¬ Owned j n
    unowned mj (inj₁ pr) with prefix-lt j n pr
    ... | inj₁ eq = proj₁ dj (subst (Owned P₀) (sym eq) on)
    ... | inj₂ jn = late q n j nq on nl dj mj jn
    unowned mj (inj₂ t) = late q n j nq on nl dj mj (proj₂ rn j hj oj t)

    unkeys : ¬ Owned n j
    unkeys o = proj₁ dj (owned-trans P₀ n j on o)

    apart : Marked q j → Disjoint n j
    apart mj = unkeys , unowned mj

    atop : Marked q j → j <ᵖ n ≡ false
    atop (inj₁ jq) = ≮-trans n q j nl jq
    atop (inj₂ mq) with j <ᵖ n in e
    ... | false = refl
    ... | true  = ⊥-elim (marks-alien (marks-mid n mq e nl) on dj)

    past : Marked q j → n <ᵖ j ≡ true
    past mj = take-ahead n j (atop mj) (apart mj)

  out-pin : ∀ q n → ¬ Owned P₀ q → Owned P₀ n → q <ᵖ n ≡ false → Rise r n → ∀ j → (Marked q j × Disjoint P₀ j) × Headed j × Owned r j
          → j <ᵖ n ≡ false × Disjoint n j
  out-pin q n nq on nl rn j ((mj , dj) , hj , oj) = atop mj , apart mj
    where open Pin q n j nq on nl rn dj hj oj

  end-pin : ∀ q c → ¬ Owned P₀ q → Owned P₀ c → q <ᵖ c ≡ false → Rise r c → ∀ j → (Marked q j × Disjoint P₀ j) × Headed j × Owned r j
          → c <ᵖ j ≡ true × Disjoint (c ++ [ ix 1 ]) j × ¬ Ext c j
  end-pin q c nq on nl rc j ((mj , dj) , hj , oj) = past mj , disjoint-snoc c j (ix 1) (λ x → tagged-lane j x 1) (apart mj) , λ x → unkeys (owned-ext x)
    where open Pin q c j nq on nl rc dj hj oj

  module At {β σ} (sd : Side β σ) where
    open Side sd

    burst-sorted : SortedT (M′.burstOn r σ ∪ cut β)
    burst-sorted = sortedT-∪ _ _ (sorted-run (force σ) (cut σ) os ts) (proj₁ (trail tb))

    -- Each burst step, against the source's next and the body's.
    pinsAt : ∀ e → force σ ≡ e → EveryT (λ j → Marked (M′.shownAt e) j × Disjoint P₀ j) (M′.burstOn r σ)
    pinsAt e eq = everyT-zip (M′.burstOn r σ) (lead-run (M′.shownAt e) (force σ) (cut σ) ts os (subst (Cue (M′.shownAt e)) (sym eq) (cue-self e)))
                    (everyT-burstOn r σ ks)

    pinsOn : ∀ e → force σ ≡ e → EveryT (λ j → (Marked (M′.shownAt e) j × Disjoint P₀ j) × Headed j × Owned r j) (M′.burstOn r σ)
    pinsOn e eq = everyT-zip (M′.burstOn r σ) (pinsAt e eq) (everyT-zip (M′.burstOn r σ) (everyT-burstOn r σ hs) (everyT-burstOn r σ rs))

    nqAt : ∀ e → force σ ≡ e → Going e → ¬ Owned P₀ (M′.shownAt e)
    nqAt e eq g = shown-apart e g (subst (Every (Disjoint P₀)) eq (proj₁ ks))

    -- No body pin lies inside a burst step: the body passed what it lies
    -- inside, and the source has not.
    pins-apart : ∀ e → force σ ≡ e → Going e → EveryT (λ a → EveryT (Apart a) (cut β)) (M′.burstOn r σ)
    pins-apart e eq g = everyT-mono pair (M′.burstOn r σ) (pinsOn e eq)
      where
        nl = cue-shown lf e g (subst (Cue lf) eq lc)
        pair : ∀ k → (Marked (M′.shownAt e) k × Disjoint P₀ k) × Headed k × Owned r k → EveryT (Apart k) (cut β)
        pair k ((mk , dk) , _ , ok) = everyT-mono apart (cut β) (everyT-zip (cut β) fc (proj₂ kb))
          where
            inside : ∀ h → Fresh P₀ lf h → ¬ Ext k h
            inside h fh x with fh k x (proj₁ dk)
            ... | inj₁ kl       = late (M′.shownAt e) lf k (nqAt e eq g) lo nl dk mk kl
            ... | inj₂ (t , kt) = rt t (subst (Owned r) kt ok)
            apart : ∀ h → Fresh P₀ lf h × Owned P₀ h → Apart k h
            apart h (fh , oh) = inside h fh , λ x → proj₁ dk (owned-trans P₀ h k oh (owned-ext x))

    burst-flat : ∀ e → force σ ≡ e → Going e → FlatT (M′.burstOn r σ ∪ cut β)
    burst-flat e eq g = flatT-∪ _ _ (flat-run (force σ) (cut σ) os ss ts) (trailᶠ tb) (pins-apart e eq g)

    -- The source steps first.
    toSource : ∀ e → force σ ≡ e → Going e → M′.before (M′.shownAt e) (force β) ≡ true → Side β (M′.onward∞ σ (force σ))
    toSource e eq g be = record
      { tb = tb
      ; ts = trailing-onward σ (force σ) refl ts
      ; os = ordered-onward σ (force σ) refl ts os
      ; ss = steady-onward σ (force σ) refl ts ss
      ; kb = kb
      ; ks = every-onward σ (force σ) (proj₁ ks) (proj₂ ks) (proj₁ ks)
      ; kr = kr
      ; hs = every-onward σ (force σ) (proj₁ hs) (proj₂ hs) (proj₁ hs)
      ; rs = every-onward σ (force σ) (proj₁ rs) (proj₂ rs) (proj₁ rs)
      ; lf = lf
      ; lo = lo
      ; lc = cue-onward lf σ (force σ) refl ts os lc
      ; fc = fc
      ; fr = fr
      }

    -- The body steps first.
    toBody : ∀ e → force σ ≡ e → ∀ n → M′.shownAt e <ᵖ n ≡ false → Owned P₀ n → ∀ β′
           → Trailing β′ → Every∞ (Owned P₀) β′ → Every∞ (Rise r) β′ → EveryT (Fresh P₀ n) (cut β′) → FreshRun P₀ (force β′) → Side β′ σ
    toBody e eq n be on β′ tb′ kb′ kr′ fc′ fr′ = record
      { tb = tb′
      ; ts = ts
      ; os = os
      ; ss = ss
      ; kb = kb′
      ; ks = ks
      ; kr = kr′
      ; hs = hs
      ; rs = rs
      ; lf = n
      ; lo = on
      ; lc = subst (Cue n) (sym eq) (shown-cue n e be)
      ; fc = fc′
      ; fr = fr′
      }

  open At

  mutual
    tr-beside : ∀ β σ → Side β σ → Trail (M′.beside r β σ) (M′.burstOn r σ ∪ cut β)
    tr-beside β σ sd = tr-side β σ sd (force σ) refl

    tr-side : ∀ β σ → Side β σ → ∀ e → force σ ≡ e → Trail (M′.side r β σ e) (M′.runOn r e (cut σ) ∪ cut β)
    tr-side β σ sd (out k a s) eq =
      tr-ahead β σ sd (out k a s) eq tt _ refl _ (cong (λ z → M′.runOn r z (cut σ) ∪ cut β) eq)
    tr-side β σ sd (skip k s)  eq =
      tr-ahead β σ sd (skip k s) eq tt _ refl _ (cong (λ z → M′.runOn r z (cut σ) ∪ cut β) eq)
    tr-side β σ sd (end c)     eq =
      tr-ahead β σ sd (end c) eq tt _ refl _ (cong (λ z → M′.runOn r z (cut σ) ∪ cut β) eq)
    tr-side β σ sd hush        eq =
      trail-hushed (cut σ) (cut β) (force β) (proj₁ (proj₂ (trail (subst (λ z → Trail z (cut σ)) eq (Side.ts sd))))) (Side.tb sd)

    tr-ahead : ∀ β σ → Side β σ → ∀ e → force σ ≡ e → Going e → ∀ b → M′.before (M′.shownAt e) (force β) ≡ b
             → ∀ c → M′.burstOn r σ ∪ cut β ≡ c → Trail (M′.ahead r β σ (M′.shownAt e) b) c
    tr-ahead β σ sd e eq g true  be c ce = tr-src β σ sd e eq g be c ce
    tr-ahead β σ sd e eq g false be c ce = tr-body β σ sd e eq g (force β) refl be c ce

    tr-src : ∀ β σ → Side β σ → ∀ e → force σ ≡ e → Going e → M′.before (M′.shownAt e) (force β) ≡ true
           → ∀ c → M′.burstOn r σ ∪ cut β ≡ c → Trail (M′.ahead r β σ (M′.shownAt e) true) c
    trail (tr-src β σ sd e eq g be c ce) =
      subst SortedT ce (burst-sorted sd)
      , subst (EveryT (Marked (M′.shownAt e))) ce (everyT-∪ (M′.burstOn r σ) (cut β) (everyT-mono (λ j z → proj₁ z) (M′.burstOn r σ) (pinsAt sd e eq))
          (body-lead (M′.shownAt e) (force β) (cut β) be (Side.tb sd)))
      , tr-beside β (M′.onward∞ σ (force σ)) (toSource sd e eq g be)
    trailᶠ (tr-src β σ sd e eq g be c ce) = subst FlatT ce (burst-flat sd e eq g)

    tr-body : ∀ β σ → Side β σ → ∀ e → force σ ≡ e → Going e → ∀ x → force β ≡ x → M′.before (M′.shownAt e) x ≡ false
            → ∀ c → M′.burstOn r σ ∪ cut β ≡ c → Trail (M′.body r σ (M′.shownAt e) x) c
    trail (tr-body β σ sd e eq g (out n a β′) xe be c′ ce) =
      subst SortedT ce (burst-sorted sd)
      , subst (EveryT _) ce (everyT-∪ (M′.burstOn r σ) (cut β) (everyT-mono (out-pin q n nq on be rn) (M′.burstOn r σ) (pinsOn sd e eq)) (proj₁ (proj₂ (trail tbx))))
      , tr-ahead β′ σ (toBody sd e eq n be on β′ (proj₁ (proj₂ (proj₂ (trail tbx)))) (proj₂ (every kbx)) (proj₂ (every krx))
                         (proj₁ (freshᴿ frx)) (proj₂ (freshᴿ frx))) e eq g _ refl _ refl
      , everyT-∪ (M′.burstOn r σ) (cut β′) (everyT-mono (λ j z → proj₂ (out-pin q n nq on be rn j z)) (M′.burstOn r σ) (pinsOn sd e eq))
          (proj₂ (proj₂ (proj₂ (trail tbx))))
      where q = M′.shownAt e
            nq = nqAt sd e eq g
            tbx = subst (λ z → Trail z (cut β)) xe (Side.tb sd)
            kbx = subst (Every (Owned P₀)) xe (proj₁ (Side.kb sd))
            on = proj₁ (every kbx)
            krx = subst (Every (Rise r)) xe (proj₁ (Side.kr sd))
            rn = proj₁ (every krx)
            frx = subst (FreshRun P₀) xe (Side.fr sd)
    trail (tr-body β σ sd e eq g (skip n β′) xe be c′ ce) =
      subst SortedT ce (burst-sorted sd)
      , subst (EveryT _) ce (everyT-∪ (M′.burstOn r σ) (cut β) (everyT-mono (λ j z → inj₁ (proj₁ (out-pin q n nq on be rn j z))) (M′.burstOn r σ) (pinsOn sd e eq))
          (proj₁ (proj₂ (trail tbx))))
      , tr-ahead β′ σ (toBody sd e eq n be on β′ (proj₂ (proj₂ (trail tbx))) (proj₂ (every kbx)) (proj₂ (every krx))
                         (proj₁ (freshᴿ frx)) (proj₂ (freshᴿ frx))) e eq g _ refl _ refl
      where q = M′.shownAt e
            nq = nqAt sd e eq g
            tbx = subst (λ z → Trail z (cut β)) xe (Side.tb sd)
            kbx = subst (Every (Owned P₀)) xe (proj₁ (Side.kb sd))
            on = proj₁ (every kbx)
            krx = subst (Every (Rise r)) xe (proj₁ (Side.kr sd))
            rn = proj₁ (every krx)
            frx = subst (FreshRun P₀) xe (Side.fr sd)
    trail (tr-body β σ sd e eq g (end c) xe be c′ ce) =
      subst SortedT ce (burst-sorted sd)
      , subst (EveryT _) ce (everyT-∪ (M′.burstOn r σ) (cut β) (everyT-mono (end-pin q c nq on be rc) (M′.burstOn r σ) (pinsOn sd e eq)) (proj₁ (proj₂ (trail tbx))))
      , tt
      where q = M′.shownAt e
            nq = nqAt sd e eq g
            tbx = subst (λ z → Trail z (cut β)) xe (Side.tb sd)
            on = every (subst (Every (Owned P₀)) xe (proj₁ (Side.kb sd)))
            rc = every (subst (Every (Rise r)) xe (proj₁ (Side.kr sd)))
    trail (tr-body β σ sd e eq g hush xe () c′ ce)
    trailᶠ (tr-body β σ sd e eq g x xe be c′ ce) = subst FlatT ce (burst-flat sd e eq g)

  -- A body step before a source step keys no lane admitted there, nor
  -- does the source step key the body step's.
  sp-late : ∀ n y → Owned P₀ n → Rise r n → Disjoint P₀ y → Headed y → Owned r y → n <ᵖ y ≡ true → Sp n y
  sp-late n y on rn dy hy oy ny = sp-of n y (fwd , bwd)
    where
      on₁ : Owned P₀ (n ++ [ ix 1 ])
      on₁ = beneath-owned P₀ _ (owned-snoc P₀ n (ix 1) on)
      fwd : ¬ Owned y (n ++ [ ix 1 ])
      fwd (inj₁ pr) with prefix-split y n (ix 1) pr
      ... | inj₂ eq  = proj₁ dy (subst (Owned P₀) (sym eq) on₁)
      ... | inj₁ pr′ with prefix-lt y n pr′
      ...   | inj₁ eq = proj₁ dy (subst (Owned P₀) (sym eq) on)
      ...   | inj₂ yn = t≢f (trans (sym yn) (<ᵖ-asym n y ny))
      fwd (inj₂ t) = t≢f (trans (sym (proj₂ rn y hy oy (tagged-mark y n (ix 1) (ix-mark 1) t))) (<ᵖ-asym n y ny))
      bwd : ¬ Owned (n ++ [ ix 1 ]) y
      bwd o = proj₁ dy (owned-trans P₀ (n ++ [ ix 1 ]) y on₁ o)

  every-shown : ∀ {C} {P : Pos → Set} (e : Events C) → Going e → Every (λ y → P y × P (y ++ [ ix 0 ])) e → P (M′.shownAt e)
  every-shown (out _ _ _) g pe = proj₂ (proj₁ (every pe))
  every-shown (skip _ _)  g pe = proj₂ (proj₁ (every pe))
  every-shown (end _)     g pe = proj₂ (every pe)
  every-shown hush        () pe

  -- Past a body step no later than where the source next shows, every
  -- step the source has yet to show or leave running keys no lane the
  -- body step admits, shown or not.
  src-sp : ∀ {β σ} → Side β σ → ∀ e → force σ ≡ e → Going e → ∀ n → M′.shownAt e <ᵖ n ≡ false → Owned P₀ n → Rise r n
         → Every∞ (λ y → Sp n y × Sp n (y ++ [ ix 0 ])) σ
  src-sp {β} {σ} sd e eq g n be on rn =
    every∞-mono f σ (every∞-zip σ (every∞-zip σ (every∞-zip σ mk (Side.ks sd)) (Side.hs sd)) (Side.rs sd))
    where
      q  = M′.shownAt e
      nq = nqAt sd e eq g
      mk = lead∞ q σ (Side.ts sd) (Side.os sd) (subst (Cue q) (sym eq) (cue-self e))
      f : ∀ y → ((Marked q y × Disjoint P₀ y) × Headed y) × Owned r y → Sp n y × Sp n (y ++ [ ix 0 ])
      f y (((my , dy) , hy) , oy) = sy , sp-step n y sy
        where sy = sp-late n y on rn dy hy oy (Pin.past q n y nq on be rn dy hy oy my)

  -- THE SPREAD WALK: after a body value, nothing the connect later shows
  -- or leaves running keys where a lane admitted at it would.
  mutual
    sp-beside : ∀ β σ → Side β σ → Spread (force β) → Spread (M′.beside r β σ)
    sp-beside β σ sd sb = sp-side β σ sd sb (force σ) refl

    sp-side : ∀ β σ → Side β σ → Spread (force β) → ∀ e → force σ ≡ e → Spread (M′.side r β σ e)
    sp-side β σ sd sb (out k a s) eq = sp-ahead β σ sd sb (out k a s) eq tt _ refl
    sp-side β σ sd sb (skip k s)  eq = sp-ahead β σ sd sb (skip k s) eq tt _ refl
    sp-side β σ sd sb (end c)     eq = sp-ahead β σ sd sb (end c) eq tt _ refl
    sp-side β σ sd sb hush        eq = sb

    sp-ahead : ∀ β σ → Side β σ → Spread (force β) → ∀ e → force σ ≡ e → Going e → ∀ b → M′.before (M′.shownAt e) (force β) ≡ b
             → Spread (M′.ahead r β σ (M′.shownAt e) b)
    sp-ahead β σ sd sb e eq g true  be = sp-src β σ sd sb e eq g be
    sp-ahead β σ sd sb e eq g false be = sp-body β σ sd e eq g (force β) refl sb be

    sp-src : ∀ β σ → Side β σ → Spread (force β) → ∀ e → force σ ≡ e → Going e → M′.before (M′.shownAt e) (force β) ≡ true
           → Spread (M′.ahead r β σ (M′.shownAt e) true)
    spread (sp-src β σ sd sb e eq g be) = sp-beside β (M′.onward∞ σ (force σ)) (toSource sd e eq g be) sb

    sp-body : ∀ β σ → Side β σ → ∀ e → force σ ≡ e → Going e → ∀ x → force β ≡ x → Spread x → M′.before (M′.shownAt e) x ≡ false
            → Spread (M′.body r σ (M′.shownAt e) x)
    spread (sp-body β σ sd e eq g (out n a β′) xe sx be) =
      ( every-ahead {P = Sp n} r β′ σ q (M′.before q (force β′)) (proj₁ (spread sx)) ss
          (every-shown e g (subst (Every (λ y → Sp n y × Sp n (y ++ [ ix 0 ]))) eq (proj₁ ss)))
      , everyT-∪ (M′.burstOn r σ) (cut β′) (everyT-burstOn r σ (every∞-mono (λ _ → proj₁) σ ss)) (proj₂ (proj₁ (spread sx))) )
      , sp-ahead β′ σ (toBody sd e eq n be on β′ (proj₁ (proj₂ (proj₂ (trail tbx)))) (proj₂ (every kbx)) (proj₂ (every krx))
                         (proj₁ (freshᴿ frx)) (proj₂ (freshᴿ frx))) (proj₂ (spread sx)) e eq g _ refl
      where q = M′.shownAt e
            tbx = subst (λ z → Trail z (cut β)) xe (Side.tb sd)
            kbx = subst (Every (Owned P₀)) xe (proj₁ (Side.kb sd))
            on = proj₁ (every kbx)
            krx = subst (Every (Rise r)) xe (proj₁ (Side.kr sd))
            frx = subst (FreshRun P₀) xe (Side.fr sd)
            ss = src-sp sd e eq g n be on (proj₁ (every krx))
    spread (sp-body β σ sd e eq g (skip n β′) xe sx be) =
      sp-ahead β′ σ (toBody sd e eq n be on β′ (proj₂ (proj₂ (trail tbx))) (proj₂ (every kbx)) (proj₂ (every krx))
                       (proj₁ (freshᴿ frx)) (proj₂ (freshᴿ frx))) (spread sx) e eq g _ refl
      where tbx = subst (λ z → Trail z (cut β)) xe (Side.tb sd)
            kbx = subst (Every (Owned P₀)) xe (proj₁ (Side.kb sd))
            on = proj₁ (every kbx)
            krx = subst (Every (Rise r)) xe (proj₁ (Side.kr sd))
            frx = subst (FreshRun P₀) xe (Side.fr sd)
    spread (sp-body β σ sd e eq g (end c) xe sx be) = tt
    spread (sp-body β σ sd e eq g hush    xe sx be) = tt

  -- THE ORDER WALK: each step the connect shows no earlier than the one
  -- before, the source's past the body's last and the body's past the
  -- source's last.
  atop-cue : ∀ L (β : Events∞ B) (σ : Events∞ A) (e : Events A) → Cue L e → Atop L (force β) → Atop L (M′.side r β σ e)
  atop-cue L β σ (out q _ _) c a = atop-ahead r β σ (q ++ [ ix 0 ]) (M′.before (q ++ [ ix 0 ]) (force β)) L a c
  atop-cue L β σ (skip q _)  c a = atop-ahead r β σ (q ++ [ ix 0 ]) (M′.before (q ++ [ ix 0 ]) (force β)) L a c
  atop-cue L β σ (end q)     c a = atop-ahead r β σ (q ++ [ ix 0 ]) (M′.before (q ++ [ ix 0 ]) (force β)) L a c
  atop-cue L β σ hush        c a = a

  mutual
    or-beside : ∀ (β : Events∞ B) (σ : Events∞ A) → Trailing σ → Ordered (force σ) → Ordered (force β) → Ordered (M′.beside r β σ)
    or-beside β σ ts os ob = or-side β σ ts os ob (force σ) refl

    or-side : ∀ (β : Events∞ B) (σ : Events∞ A) → Trailing σ → Ordered (force σ) → Ordered (force β) → ∀ e → force σ ≡ e → Ordered (M′.side r β σ e)
    or-side β σ ts os ob (out k a s) eq = or-ahead β σ ts os ob (out k a s) eq tt _ refl
    or-side β σ ts os ob (skip k s)  eq = or-ahead β σ ts os ob (skip k s) eq tt _ refl
    or-side β σ ts os ob (end c)     eq = or-ahead β σ ts os ob (end c) eq tt _ refl
    or-side β σ ts os ob hush        eq = ob

    or-ahead : ∀ (β : Events∞ B) (σ : Events∞ A) → Trailing σ → Ordered (force σ) → Ordered (force β) → ∀ e → force σ ≡ e → Going e → ∀ b
             → M′.before (M′.shownAt e) (force β) ≡ b → Ordered (M′.ahead r β σ (M′.shownAt e) b)
    or-ahead β σ ts os ob e eq g true  be = or-src β σ ts os ob e eq g be
    or-ahead β σ ts os ob e eq g false be = or-body σ ts os e eq g (force β) ob be

    or-src : ∀ (β : Events∞ B) (σ : Events∞ A) → Trailing σ → Ordered (force σ) → Ordered (force β) → ∀ e → force σ ≡ e → Going e
           → M′.before (M′.shownAt e) (force β) ≡ true → Ordered (M′.ahead r β σ (M′.shownAt e) true)
    ordered (or-src β σ ts os ob e eq g be) =
      atop-cue q β σ′ (force σ′) (cue-onward q σ (force σ) refl ts os (subst (λ z → Cue (M′.shownAt z) (force σ)) eq (cue-self (force σ))))
        (before-atop q (force β) be)
      , or-beside β σ′ (trailing-onward σ (force σ) refl ts) (ordered-onward σ (force σ) refl ts os) ob
      where q  = M′.shownAt e
            σ′ = M′.onward∞ σ (force σ)

    or-body : ∀ (σ : Events∞ A) → Trailing σ → Ordered (force σ) → ∀ e → force σ ≡ e → Going e → ∀ x → Ordered x
            → M′.before (M′.shownAt e) x ≡ false → Ordered (M′.body r σ (M′.shownAt e) x)
    ordered (or-body σ ts os e eq g (out n a β′) ox be) =
      atop-ahead r β′ σ (M′.shownAt e) (M′.before (M′.shownAt e) (force β′)) n (proj₁ (ordered ox)) be , or-ahead β′ σ ts os (proj₂ (ordered ox)) e eq g _ refl
    ordered (or-body σ ts os e eq g (skip n β′) ox be) =
      atop-ahead r β′ σ (M′.shownAt e) (M′.before (M′.shownAt e) (force β′)) n (proj₁ (ordered ox)) be , or-ahead β′ σ ts os (proj₂ (ordered ox)) e eq g _ refl
    ordered (or-body σ ts os e eq g (end c)     ox be) = tt
    ordered (or-body σ ts os e eq g hush        ox be) = tt

  -- THE STEADY WALK: a source step's shown position lies outside the
  -- body's next, and the source's; a body step's outside the source's.
  clear-head : ∀ q (x : Events B) → M′.before q x ≡ true → Every (λ k → Unrelated k q) x → Clear q x
  clear-head q (out k _ _) qk ux = qk , λ e → proj₂ (proj₁ (every ux)) (ext-prefixed e)
  clear-head q (skip k _)  qk ux = λ e → proj₂ (proj₁ (every ux)) (ext-prefixed e)
  clear-head q (end k)     qk ux = qk , λ e → proj₂ (every ux) (ext-prefixed e)
  clear-head q hush        qk ux = tt

  clear-body : ∀ q (σ : Events∞ A) q′ (x : Events B) → M′.before q x ≡ true → Every (λ k → Unrelated k q) x → Clear q (M′.body r σ q′ x)
  clear-body q σ q′ (out k a β) qk ux = clear-head q (out k a β) qk ux
  clear-body q σ q′ (skip k β)  qk ux = clear-head q (skip k β) qk ux
  clear-body q σ q′ (end k)     qk ux = clear-head q (end k) qk ux
  clear-body q σ q′ hush        qk ux = tt

  clear-ahead : ∀ q β (σ : Events∞ A) q′ b → M′.before q (force β) ≡ true → Every (λ k → Unrelated k q) (force β) → ¬ Ext q q′
              → Clear q (M′.ahead r β σ q′ b)
  clear-ahead q β σ q′ true  qb ub nx = nx
  clear-ahead q β σ q′ false qb ub nx = clear-body q σ q′ (force β) qb ub

  clear-side : ∀ q β (σ : Events∞ A) e → M′.before q (force β) ≡ true → Every (λ k → Unrelated k q) (force β)
             → Head (λ h → ¬ Ext q (h ++ [ ix 0 ])) e → Clear q (M′.side r β σ e)
  clear-side q β σ (out h _ _) qb ub nx = clear-ahead q β σ (h ++ [ ix 0 ]) (M′.before (h ++ [ ix 0 ]) (force β)) qb ub nx
  clear-side q β σ (skip h _)  qb ub nx = clear-ahead q β σ (h ++ [ ix 0 ]) (M′.before (h ++ [ ix 0 ]) (force β)) qb ub nx
  clear-side q β σ (end h)     qb ub nx = clear-ahead q β σ (h ++ [ ix 0 ]) (M′.before (h ++ [ ix 0 ]) (force β)) qb ub nx
  clear-side q β σ hush        qb ub nx = clear-head q (force β) qb ub

  past-body : ∀ n (σ : Events∞ A) q (x : Events B) → Past n x → Past n (M′.body r σ q x)
  past-body n σ q (out _ _ _) pb = pb
  past-body n σ q (skip _ _)  pb = pb
  past-body n σ q (end _)     pb = pb
  past-body n σ q hush        pb = tt

  past-ahead : ∀ n β (σ : Events∞ A) q b → Past n (force β) → n <ᵖ q ≡ true → ¬ Ext n q → Past n (M′.ahead r β σ q b)
  past-ahead n β σ q true  pb nq nx = nq , nx
  past-ahead n β σ q false pb nq nx = past-body n σ q (force β) pb

  clear-under : ∀ n (σ : Events∞ A) q (x : Events B) → Clear n x → Clear n (M′.body r σ q x)
  clear-under n σ q (out _ _ _) cb = cb
  clear-under n σ q (skip _ _)  cb = cb
  clear-under n σ q (end _)     cb = cb
  clear-under n σ q hush        cb = tt

  clear-next : ∀ n β (σ : Events∞ A) q b → Clear n (force β) → ¬ Ext n q → Clear n (M′.ahead r β σ q b)
  clear-next n β σ q true  cb nx = nx
  clear-next n β σ q false cb nx = clear-under n σ q (force β) cb

  -- Where the source next shows, read off what holds just past each step.
  head-shown : ∀ {P : Pos → Set} (σ : Events∞ A) e → force σ ≡ e → Going e → Every∞ (λ q → P (q ++ [ ix 0 ])) σ → P (M′.shownAt e)
  head-shown {P} σ e eq g u = go e g (subst (Every (λ q → P (q ++ [ ix 0 ]))) eq (proj₁ u))
    where
      go : ∀ e → Going e → Every (λ q → P (q ++ [ ix 0 ])) e → P (M′.shownAt e)
      go (out _ _ _) g pe = proj₁ (every pe)
      go (skip _ _)  g pe = proj₁ (every pe)
      go (end _)     g pe = every pe
      go hush        () pe

  away-head : ∀ k (x : Events A) → Away k x → Head (λ h → ¬ Ext (k ++ [ ix 0 ]) (h ++ [ ix 0 ])) x
  away-head k (out h _ _) aw = λ x → aw (under-ext k h x)
  away-head k (skip h _)  aw = λ x → aw (under-ext k h x)
  away-head k (end h)     aw = λ x → aw (under-ext k h x)
  away-head k hush        aw = tt

  tail-head : ∀ c t → EveryT (TrailE {A} (end c)) t → Head (λ h → ¬ Ext (c ++ [ ix 0 ]) (h ++ [ ix 0 ])) (tailᴱ {A} t)
  tail-head c (pin j u) e = λ x → proj₂ (proj₂ (proj₁ (everyᵀ e))) (under-ext c j x)
  tail-head c idle      e = tt

  -- The source's next shows outside where its step showed.
  next-away : ∀ (σ : Events∞ A) e → Going e → Trail e (cut σ) → Steady e
            → Head (λ h → ¬ Ext (M′.shownAt e) (h ++ [ ix 0 ])) (force (M′.onward∞ σ e))
  next-away σ (out k _ s) g tr se = away-head k (force s) (past-away k (force s) (proj₁ (steady se)))
  next-away σ (skip k s)  g tr se = away-head k (force s) (clear-away k (force s) (proj₁ (steady se)))
  next-away σ (end c)     g tr se = tail-head c (cut σ) (proj₁ (proj₂ (trail tr)))
  next-away σ hush        () tr se

  UB : Events∞ B → Events∞ A → Set
  UB β σ = Every∞ (λ k → Every∞ (λ q → Unrelated k (q ++ [ ix 0 ])) σ) β

  mutual
    st-beside : ∀ (β : Events∞ B) (σ : Events∞ A) → Trailing σ → Ordered (force σ) → Steady (force σ) → Steady (force β) → UB β σ → Steady (M′.beside r β σ)
    st-beside β σ ts os ss sb u = st-side β σ ts os ss sb u (force σ) refl

    st-side : ∀ (β : Events∞ B) (σ : Events∞ A) → Trailing σ → Ordered (force σ) → Steady (force σ) → Steady (force β) → UB β σ → ∀ e → force σ ≡ e
            → Steady (M′.side r β σ e)
    st-side β σ ts os ss sb u (out k a s) eq = st-ahead β σ ts os ss sb u (out k a s) eq tt _ refl
    st-side β σ ts os ss sb u (skip k s)  eq = st-ahead β σ ts os ss sb u (skip k s) eq tt _ refl
    st-side β σ ts os ss sb u (end c)     eq = st-ahead β σ ts os ss sb u (end c) eq tt _ refl
    st-side β σ ts os ss sb u hush        eq = sb

    st-ahead : ∀ (β : Events∞ B) (σ : Events∞ A) → Trailing σ → Ordered (force σ) → Steady (force σ) → Steady (force β) → UB β σ → ∀ e → force σ ≡ e → Going e
             → ∀ b → M′.before (M′.shownAt e) (force β) ≡ b → Steady (M′.ahead r β σ (M′.shownAt e) b)
    st-ahead β σ ts os ss sb u e eq g true  be = st-src β σ ts os ss sb u e eq g be
    st-ahead β σ ts os ss sb u e eq g false be = st-body σ ts os ss e eq g (force β) sb (proj₁ u) be

    st-src : ∀ (β : Events∞ B) (σ : Events∞ A) → Trailing σ → Ordered (force σ) → Steady (force σ) → Steady (force β) → UB β σ → ∀ e → force σ ≡ e → Going e
           → M′.before (M′.shownAt e) (force β) ≡ true → Steady (M′.ahead r β σ (M′.shownAt e) true)
    steady (st-src β σ ts os ss sb u e eq g be) =
      clear-side q β σ′ (force σ′) be (every-mono (λ k w → head-shown {P = Unrelated k} σ e eq g w) (force β) (proj₁ u))
        (subst (λ z → Head (λ h → ¬ Ext q (h ++ [ ix 0 ])) (force (M′.onward∞ σ z))) (sym eq)
           (next-away σ e g (subst (λ z → Trail z (cut σ)) eq ts) (subst Steady eq ss)))
      , st-beside β σ′ (trailing-onward σ (force σ) refl ts) (ordered-onward σ (force σ) refl ts os) (steady-onward σ (force σ) refl ts ss) sb
          (every∞-mono (λ k w → every-onward σ (force σ) (proj₁ w) (proj₂ w) (proj₁ w)) β u)
      where q  = M′.shownAt e
            σ′ = M′.onward∞ σ (force σ)

    st-body : ∀ (σ : Events∞ A) → Trailing σ → Ordered (force σ) → Steady (force σ) → ∀ e → force σ ≡ e → Going e → ∀ x → Steady x
            → Every (λ k → Every∞ (λ q → Unrelated k (q ++ [ ix 0 ])) σ) x → M′.before (M′.shownAt e) x ≡ false
            → Steady (M′.body r σ (M′.shownAt e) x)
    steady (st-body σ ts os ss e eq g (out n a β′) sx ux be) =
      past-ahead n β′ σ q (M′.before q (force β′)) (proj₁ (steady sx)) (strict n q be (proj₁ un)) (λ x → proj₁ un (ext-prefixed x))
      , st-ahead β′ σ ts os ss (proj₂ (steady sx)) (proj₂ (every ux)) e eq g _ refl
      where q  = M′.shownAt e
            un = head-shown {P = Unrelated n} σ e eq g (proj₁ (every ux))
    steady (st-body σ ts os ss e eq g (skip n β′) sx ux be) =
      clear-next n β′ σ q (M′.before q (force β′)) (proj₁ (steady sx)) (λ x → proj₁ un (ext-prefixed x))
      , st-ahead β′ σ ts os ss (proj₂ (steady sx)) (proj₂ (every ux)) e eq g _ refl
      where q  = M′.shownAt e
            un = head-shown {P = Unrelated n} σ e eq g (proj₁ (every ux))
    steady (st-body σ ts os ss e eq g (end c)     sx ux be) = tt
    steady (st-body σ ts os ss e eq g hush        sx ux be) = tt

  -- A body step keyed under it, a source step apart from it and under
  -- the source's root: the body step no prefix of where the source
  -- step shows.
  easy-pt : ∀ k q → Owned P₀ k → Disjoint P₀ q → Owned r q → ¬ Prefix k (q ++ [ ix 0 ])
  easy-pt k q ok dq oq pr with prefix-split k q (ix 0) pr
  ... | inj₁ pk = proj₁ dq (owned-trans P₀ k q ok (inj₁ pk))
  ... | inj₂ eq = shown₀ (subst (Owned P₀) eq ok)
    where
      shown₀ : ¬ Owned P₀ (q ++ [ ix 0 ])
      shown₀ (inj₂ t) = proj₁ dq (inj₂ (tagged-lane P₀ q 0 t))
      shown₀ (inj₁ pq) with prefix-split P₀ q (ix 0) pq
      ... | inj₁ pq′ = proj₁ dq (inj₁ pq′)
      ... | inj₂ e   = longer p (ix 1) (subst (Owned r) (sym (proj₁ (snoc-inj p q e))) oq)

  -- The body unrelated to the source's shown steps, given that none of
  -- its steps lies under one.
  unrelated : ∀ {β σ} → Side β σ → Every∞ (λ k → Every∞ (λ q → ¬ Prefix (q ++ [ ix 0 ]) k) σ) β → UB β σ
  unrelated {β} {σ} sd hard =
    every∞-mono (λ k x → every∞-mono (λ q y → easy-pt k q (proj₁ x) (proj₁ (proj₁ y)) (proj₂ (proj₁ y)) , proj₂ y) σ
                           (every∞-zip σ (every∞-zip σ (Side.ks sd) (Side.rs sd)) (proj₂ x)))
      β (every∞-zip β (Side.kb sd) hard)

  -- Keyed with none of the connect, keyed with none of its body.
  narrow₀ : ∀ k → ¬ Owned p k → ¬ Owned P₀ k
  narrow₀ k no o = no (owned-trans p P₀ k (inj₁ (prefix-++ p [ ix 0 ])) o)

  pinned-under : ∀ k → M.inside r k ≡ true → Σ Pos (λ ys → k ≡ p ++ ys)
  pinned-under k i = prefix-rest p k (prefix-trans p r k (prefix-++ p [ ix 1 ]) (inside-under r k i))

  -- The source's burst, fresh against any step no earlier than the
  -- connect: what its pins lie inside, outside the connect, lies before it.
  mutual
    fresh-burstOn : ∀ L → L <ᵖ p ≡ false → (σ : Events∞ A) → EveryT (Fresh p L) (cut σ) → FreshRun p (force σ)
                  → EveryT (Fresh p L) (M′.burstOn r σ)
    fresh-burstOn L pl σ ct fr = fresh-runOn L pl (force σ) (cut σ) ct fr

    fresh-runOn : ∀ L → L <ᵖ p ≡ false → (e : Events A) → ∀ t → EveryT (Fresh p L) t → FreshRun p e → EveryT (Fresh p L) (M′.runOn r e t)
    fresh-runOn L pl (out k _ s) t ct fr = fresh-pinned L pl k s t (M.inside r k) refl ct (proj₁ (freshᴿ fr)) (proj₂ (freshᴿ fr))
    fresh-runOn L pl (skip k s)  t ct fr = fresh-pinned L pl k s t (M.inside r k) refl ct (proj₁ (freshᴿ fr)) (proj₂ (freshᴿ fr))
    fresh-runOn L pl (end _)     t ct fr = ct
    fresh-runOn L pl hush        t ct fr = ct

    fresh-pinned : ∀ L → L <ᵖ p ≡ false → ∀ k (s : Events∞ A) t b → M.inside r k ≡ b → EveryT (Fresh p L) t
                 → EveryT (Fresh p k) (cut s) → FreshRun p (force s) → EveryT (Fresh p L) (M′.pinned r k s t b)
    everyᵀ (fresh-pinned L pl k s t true  ib ct cs fs) = at-k , fresh-burstOn L pl s (everyT-mono lift (cut s) cs) fs
      where
        ys = proj₁ (pinned-under k ib)
        ke = proj₂ (pinned-under k ib)
        at-k : Fresh p L k
        at-k k′ x no with ext-eq x
        ... | l , ls , e =
          inj₁ (still k′ p L (below-under p k′ ys (λ q → no (inj₁ q)) (subst (λ z → k′ <ᵖ z ≡ true) (trans (sym e) ke) (<ᵖ-below k′ ls))) pl)
        lift : ∀ h → Fresh p k h → Fresh p L h
        lift h f = fresh-past p p L h pl (fresh-under p ys h (subst (λ z → Fresh p z h) ke f))
    everyᵀ (fresh-pinned L pl k s t false ib ct cs fs) = everyᵀ ct

  -- The source past its next step, fresh against where that step shows.
  fresh-onward : ∀ L (σ : Events∞ A) e → Going e → Trail e (cut σ) → M′.shownAt e <ᵖ L ≡ false → EveryT (Fresh p L) (cut σ) → FreshRun p e
               → EveryT (Fresh p (M′.shownAt e)) (cut (M′.onward∞ σ e)) × FreshRun p (force (M′.onward∞ σ e))
  fresh-onward L σ (out k _ s) g tr lq ct fr =
    everyT-mono (λ h → fresh-up p k (k ++ [ ix 0 ]) h (inj₁ (<ᵖ-below k []))) (cut s) (proj₁ (freshᴿ fr)) , proj₂ (freshᴿ fr)
  fresh-onward L σ (skip k s)  g tr lq ct fr =
    everyT-mono (λ h → fresh-up p k (k ++ [ ix 0 ]) h (inj₁ (<ᵖ-below k []))) (cut s) (proj₁ (freshᴿ fr)) , proj₂ (freshᴿ fr)
  fresh-onward L σ (end c)     g tr lq ct fr =
    cq , fresh-tail p (c ++ [ ix 0 ]) (cut σ) cq (everyT-mono (λ j z → marks-past j shown (proj₁ z) (proj₂ (proj₂ z))) (cut σ) (proj₁ (proj₂ (trail tr))))
    where cq = everyT-mono (λ h → fresh-past p L (c ++ [ ix 0 ]) h lq) (cut σ) ct
  fresh-onward L σ hush        () tr lq ct fr

  -- A side the connect last showed at `L`: no earlier than the connect,
  -- nor later than either run's next; both runs' cuts fresh against it.
  record FSide (β : Events∞ B) (σ : Events∞ A) : Set where
    field
      sd : Side β σ
      ob : Ordered (force β)
      L  : Pos
      pL : L <ᵖ p ≡ false
      cL : Cue L (force σ)
      bL : Atop L (force β)
      bc : EveryT (Fresh p L) (cut β)
      sc : EveryT (Fresh p L) (cut σ)
      sr : FreshRun p (force σ)

  -- What a side leaves running is fresh against where it last showed.
  cuts-fresh : ∀ {β σ} (fs : FSide β σ) → EveryT (Fresh p (FSide.L fs)) (M′.burstOn r σ ∪ cut β)
  cuts-fresh {β} {σ} fs = everyT-∪ (M′.burstOn r σ) (cut β) (fresh-burstOn L pL σ sc sr) bc
    where open FSide fs

  toSourceF : ∀ {β σ} (fs : FSide β σ) e → force σ ≡ e → Going e → M′.before (M′.shownAt e) (force β) ≡ true → FSide β (M′.onward∞ σ (force σ))
  toSourceF {β} {σ} fs e eq g be = record
    { sd = toSource sd e eq g be
    ; ob = ob
    ; L  = M′.shownAt e
    ; pL = ≮-trans p L (M′.shownAt e) pL qL
    ; cL = cue-onward (M′.shownAt e) σ (force σ) refl (Side.ts sd) (Side.os sd) (subst (λ z → Cue (M′.shownAt z) (force σ)) eq (cue-self (force σ)))
    ; bL = before-atop (M′.shownAt e) (force β) be
    ; bc = everyT-mono (λ h → fresh-past p L (M′.shownAt e) h qL) (cut β) bc
    ; sc = proj₁ on
    ; sr = proj₂ on
    }
    where
      open FSide fs
      qL = cue-shown L e g (subst (Cue L) eq cL)
      on = subst (λ z → EveryT (Fresh p (M′.shownAt e)) (cut (M′.onward∞ σ z)) × FreshRun p (force (M′.onward∞ σ z))) (sym eq)
             (fresh-onward L σ e g (subst (λ z → Trail z (cut σ)) eq (Side.ts sd)) qL sc (subst (FreshRun p) eq sr))

  -- THE FRESH WALK: at every state the connect reaches, what it leaves
  -- running is fresh against the step it shows.
  mutual
    fr-beside : ∀ β σ → FSide β σ → FreshRun p (M′.beside r β σ)
    fr-beside β σ fs = fr-side β σ fs (force σ) refl

    fr-side : ∀ β σ → FSide β σ → ∀ e → force σ ≡ e → FreshRun p (M′.side r β σ e)
    fr-side β σ fs (out k a s) eq = fr-ahead β σ fs (out k a s) eq tt _ refl
    fr-side β σ fs (skip k s)  eq = fr-ahead β σ fs (skip k s) eq tt _ refl
    fr-side β σ fs (end c)     eq = fr-ahead β σ fs (end c) eq tt _ refl
    fr-side β σ fs hush        eq = fresh-widen p P₀ narrow₀ (force β) (Side.fr (FSide.sd fs))

    fr-ahead : ∀ β σ → FSide β σ → ∀ e → force σ ≡ e → Going e → ∀ b → M′.before (M′.shownAt e) (force β) ≡ b
             → FreshRun p (M′.ahead r β σ (M′.shownAt e) b)
    fr-ahead β σ fs e eq g true  be = fr-src β σ fs e eq g be
    fr-ahead β σ fs e eq g false be = fr-body β σ fs e eq g (force β) refl be

    fr-src : ∀ β σ → FSide β σ → ∀ e → force σ ≡ e → Going e → M′.before (M′.shownAt e) (force β) ≡ true
           → FreshRun p (M′.ahead r β σ (M′.shownAt e) true)
    freshᴿ (fr-src β σ fs e eq g be) = cuts-fresh fs′ , fr-beside β (M′.onward∞ σ (force σ)) fs′
      where fs′ = toSourceF fs e eq g be

    fr-body : ∀ β σ → FSide β σ → ∀ e → force σ ≡ e → Going e → ∀ x → force β ≡ x → M′.before (M′.shownAt e) x ≡ false
            → FreshRun p (M′.body r σ (M′.shownAt e) x)
    freshᴿ (fr-body β σ fs e eq g (out n a β′) xe be) = cuts-fresh fs′ , fr-ahead β′ σ fs′ e eq g _ refl
      where
        open FSide fs
        tbx = subst (λ z → Trail z (cut β)) xe (Side.tb sd)
        kbx = subst (Every (Owned P₀)) xe (proj₁ (Side.kb sd))
        krx = subst (Every (Rise r)) xe (proj₁ (Side.kr sd))
        frx = subst (FreshRun P₀) xe (Side.fr sd)
        obx = subst Ordered xe ob
        bn  = subst (Atop L) xe bL
        fs′ : FSide β′ σ
        fs′ = record
          { sd = toBody sd e eq n be (proj₁ (every kbx)) β′ (proj₁ (proj₂ (proj₂ (trail tbx)))) (proj₂ (every kbx)) (proj₂ (every krx))
                        (proj₁ (freshᴿ frx)) (proj₂ (freshᴿ frx))
          ; ob = proj₂ (ordered obx)
          ; L  = n
          ; pL = ≮-trans p L n pL bn
          ; cL = subst (Cue n) (sym eq) (shown-cue n e be)
          ; bL = proj₁ (ordered obx)
          ; bc = everyT-mono (λ h f k x no → f k x (narrow₀ k no)) (cut β′) (proj₁ (freshᴿ frx))
          ; sc = everyT-mono (λ h → fresh-past p L n h bn) (cut σ) sc
          ; sr = sr
          }
    freshᴿ (fr-body β σ fs e eq g (skip n β′) xe be) = cuts-fresh fs′ , fr-ahead β′ σ fs′ e eq g _ refl
      where
        open FSide fs
        tbx = subst (λ z → Trail z (cut β)) xe (Side.tb sd)
        kbx = subst (Every (Owned P₀)) xe (proj₁ (Side.kb sd))
        krx = subst (Every (Rise r)) xe (proj₁ (Side.kr sd))
        frx = subst (FreshRun P₀) xe (Side.fr sd)
        obx = subst Ordered xe ob
        bn  = subst (Atop L) xe bL
        fs′ : FSide β′ σ
        fs′ = record
          { sd = toBody sd e eq n be (proj₁ (every kbx)) β′ (proj₂ (proj₂ (trail tbx))) (proj₂ (every kbx)) (proj₂ (every krx))
                        (proj₁ (freshᴿ frx)) (proj₂ (freshᴿ frx))
          ; ob = proj₂ (ordered obx)
          ; L  = n
          ; pL = ≮-trans p L n pL bn
          ; cL = subst (Cue n) (sym eq) (shown-cue n e be)
          ; bL = proj₁ (ordered obx)
          ; bc = everyT-mono (λ h f k x no → f k x (narrow₀ k no)) (cut β′) (proj₁ (freshᴿ frx))
          ; sc = everyT-mono (λ h → fresh-past p L n h bn) (cut σ) sc
          ; sr = sr
          }
    freshᴿ (fr-body β σ fs e eq g (end c) xe be) = tt
    freshᴿ (fr-body β σ fs e eq g hush    xe be) = tt
