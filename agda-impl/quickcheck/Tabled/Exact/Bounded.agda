{-# OPTIONS --guardedness #-}

-- BOUNDED MERGE, LISTED EXACTLY: the lanes level by level, as the listing
-- grows them.  The ends passed on below a level list exactly the lanes
-- before it (`Lists`), so a count over them decides `Bounded.Kth`,
-- and each value's entry holds its lane at every start `Starts` allows.
-- A value's level is below its count of values before it, so the
-- listing's levels reach every value.
module quickcheck.Tabled.Exact.Bounded where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.Properties using (T-≡)
open import Function.Bundles using (Equivalence)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; length) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; _<ᵇ_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties
  using (<ᵇ⇒<; <⇒<ᵇ; ≤ᵇ⇒≤; ≤⇒≤ᵇ; ≮⇒≥; <⇒≱; ≤⇒≯; m≤n⇒m<n∨m≡n; +-suc; +-identityʳ; ≤-<-trans; ≤-refl; ≤-trans; n≤1+n; ≤-pred)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import denotation.Events using (Pos; _<ᵖ_; ix; <ᵖ-trans)
open import denotation.EmissionSet using (out; skip; end; EmissionSet; Den; After)
open import denotation.Laws.Nth using (module Nths)
import denotation.EmissionSet as Tb
open import quickcheck.Tabled using (Row; Listed; rows; short; concatMap; mapM; anyᵇ; endBy; values; outerRow; _≼ᵇ_;
  module BoundedL; module Order)
open import quickcheck.Tabled.Exact.Base
  using (Exact; Exactly; sound; complete; fromT; fromNot; offT; not-T; T-not; ∨-false; ∧-true; ∧-intro; off; or-of; or-right;
  ≟-refl; ≟-true; any⁻; any⁺; any-off; all⁻; all⁺; single⁻; when⁻; when⁺; if⁻; if-t; if-f; cm⁻; cm⁺; bind⁻; mapM⁻; mapM⁺;
  values⁺; ends⁻; ends⁺; endBy→; →endBy; cnt-in; module OrderX)

module BoundedX {A B : Set} (n : ℕ) (fD : A → Den B) (t : EmissionSet A) (ln : A → Pos → Maybe (Listed B)) (o : Listed A)
  (eo : Exactly o t) (eln : ∀ {a s l} → ln a s ≡ just l → Exactly l (After (fD a) s))
  (G : List (ℕ × Pos × A × List (Pos × Listed B)))
  (eG : BoundedL.levels n ln o (length (values (rows o))) 0 [] (Order.nths (values (rows o)) 0) ≡ just G)
  (u : short (BoundedL.boundedRows n ln o G) ≡ false)
  where
  open Tb.Bounded n fD t
    using (Kth; Starts; room; freed; queued; Ends; Sched; Sub; Queued; Done; JoinT; Lane; Indexed;
    val; step; oend; opass; lane; lend; lpass; hand; left; run; rend; rpass; rhand)
  open Tb.Values t using (Nth)
  open Nths t using (nth-val; nth-at; nth-inj)
  open BoundedL n ln o
    using (vals; count; starts; Entry; laneAt; entry; laneEnds; entryEnds; endsOf; levels; done; laneRow; boundedRows)
    renaming (queued to queuedᵇ)
  open Order vals using (nths)

  private
    exo : Exact o t
    exo = eo (proj₁ (∨-false {short o} u))

    uncut : ∀ {j q a ss s l} → (j , q , a , ss) ∈ G → (s , l) ∈ ss → short l ≡ false
    uncut {ss = ss} gm sm = any-off {xs = ss} (any-off {xs = G} (proj₂ (∨-false {short o} u)) gm) sm

    exl : ∀ {j q a ss s l} → (j , q , a , ss) ∈ G → (s , l) ∈ ss → ln a s ≡ just l → Exact l (After (fD a) s)
    exl gm sm el = eln el (uncut gm sm)

  open OrderX exo using (nth-s; nth-c; nth-cnt)

  ----------------------------------------------------------------------
  -- The lanes before, as listed

  -- `ess` lists the lanes `ls` exactly, end for end.
  Lists : List (List Pos) → List (Pos → Set) → Set
  Lists []         []       = ⊤
  Lists (es ∷ ess) (l ∷ ls) = ((∀ {c} → c ∈ es → l c) × (∀ {c} → l c → c ∈ es)) × Lists ess ls
  Lists []         (_ ∷ _)  = ⊥
  Lists (_ ∷ _)    []       = ⊥

  private
    Kth-mono : ∀ {P Q : Pos → Set} → (∀ {c} → P c → Q c) → ∀ {ls} k → Kth P ls k → Kth Q ls k
    Kth-mono f {[]}     k       ()
    Kth-mono f {l ∷ ls} zero    (inj₁ (c , lc , pc))       = inj₁ (c , lc , f pc)
    Kth-mono f {l ∷ ls} zero    (inj₂ h)                  = inj₂ (Kth-mono f zero h)
    Kth-mono f {l ∷ ls} (suc k) (inj₁ ((c , lc , pc) , h)) = inj₁ ((c , lc , f pc) , Kth-mono f k h)
    Kth-mono f {l ∷ ls} (suc k) (inj₂ h)                  = inj₂ (Kth-mono f (suc k) h)

  -- `count p` decides `Kth P`, for a test `p` deciding `P`.
  module Count (p : Pos → Bool) (P : Pos → Set) (to : ∀ {c} → p c ≡ true → P c) (from : ∀ {c} → P c → p c ≡ true) where
    count-step : ∀ es ess → count p ess ≤ count p (es ∷ ess)
    count-step es ess with anyᵇ p es
    ... | true  = n≤1+n _
    ... | false = ≤-refl

    at→ : ∀ {ess ls} k → Lists ess ls → Kth P ls k → suc k ≤ count p ess
    at→ {[]}       {[]}     k _ ()
    at→ {[]}       {_ ∷ _}  k () _
    at→ {_ ∷ _}    {[]}     k () _
    at→ {es ∷ ess} {l ∷ ls} zero ((_ , cmp) , L) (inj₁ (c , lc , pc)) with anyᵇ p es in e
    ... | true  = s≤s z≤n
    ... | false = ⊥-elim (offT e (Equivalence.from T-≡ (any⁺ {xs = es} (cmp lc) (from pc))))
    at→ {es ∷ ess} {l ∷ ls} (suc k) ((_ , cmp) , L) (inj₁ ((c , lc , pc) , h)) with anyᵇ p es in e
    ... | true  = s≤s (at→ k L h)
    ... | false = ⊥-elim (offT e (Equivalence.from T-≡ (any⁺ {xs = es} (cmp lc) (from pc))))
    at→ {es ∷ ess} {l ∷ ls} zero    (_ , L) (inj₂ h) = ≤-trans (at→ zero L h) (count-step es ess)
    at→ {es ∷ ess} {l ∷ ls} (suc k) (_ , L) (inj₂ h) = ≤-trans (at→ (suc k) L h) (count-step es ess)

    →at : ∀ {ess ls} k → Lists ess ls → suc k ≤ count p ess → Kth P ls k
    →at {[]}       {[]}     k _ ()
    →at {[]}       {_ ∷ _}  k () _
    →at {_ ∷ _}    {[]}     k () _
    →at {es ∷ ess} {l ∷ ls} zero ((snd , _) , L) le with anyᵇ p es in e
    ... | true  = let (c , cm , pc) = any⁻ {xs = es} e in inj₁ (c , snd cm , to pc)
    ... | false = inj₂ (→at zero L le)
    →at {es ∷ ess} {l ∷ ls} (suc k) ((snd , _) , L) le with anyᵇ p es in e
    ... | true  = let (c , cm , pc) = any⁻ {xs = es} e in inj₁ ((c , snd cm , to pc) , →at k L (≤-pred le))
    ... | false = inj₂ (→at (suc k) L le)

  module Lt (c : Pos) = Count (λ k → k <ᵖ c) (λ k → Tb._≺_ k c) (λ e → Equivalence.from T-≡ e) fromT
  module Le (c : Pos) = Count (λ k → k ≼ᵇ c) (λ k → Tb._≼_ k c) not-T T-not

  private
    one→ : ∀ {ess ls c} → Lists ess ls → Kth (_≡ c) ls 0 → Σ (List Pos) λ es → es ∈ ess × c ∈ es
    one→ {[]}       {[]}     _ ()
    one→ {[]}       {_ ∷ _}  () _
    one→ {_ ∷ _}    {[]}     () _
    one→ {es ∷ ess} {l ∷ ls} ((_ , cmp) , L) (inj₁ (c′ , lc , refl)) = es , here refl , cmp lc
    one→ {es ∷ ess} {l ∷ ls} (_ , L) (inj₂ h) = let (es′ , m , cm) = one→ L h in es′ , there m , cm

    →one : ∀ {ess ls es c} → Lists ess ls → es ∈ ess → c ∈ es → Kth (_≡ c) ls 0
    →one {_ ∷ _} {[]}     () _ _
    →one {_ ∷ _} {l ∷ ls} ((snd , _) , L) (here refl) cm = inj₁ (_ , snd cm , refl)
    →one {_ ∷ _} {l ∷ ls} (_ , L) (there m) cm = inj₂ (→one L m cm)

  ----------------------------------------------------------------------
  -- Where a lane starts

  private
    n≤ : ∀ {i} → (i <ᵇ n) ≡ false → n ≤ i
    n≤ ge = ≮⇒≥ (λ lt → offT ge (<⇒<ᵇ lt))

    lt-off : ∀ {i} → n ≤ i → (i <ᵇ n) ≡ false
    lt-off {i} le = fromNot λ h → <⇒≱ (<ᵇ⇒< i n h) le

    ≺-trans : ∀ {x y z} → Tb._≺_ x y → Tb._≺_ y z → Tb._≺_ x z
    ≺-trans {x} {y} {z} a b = Equivalence.from T-≡ (<ᵖ-trans x y z (Equivalence.to T-≡ a) (Equivalence.to T-≡ b))

  starts-s : ∀ i q {ess ls s} → Lists ess ls → s ∈ starts i q ess → Starts i q ls s
  starts-s i q {ess} {ls} L m with if⁻ {b = i <ᵇ n} m
  ... | inj₁ (lt , h) = subst (Starts i q ls) (sym (single⁻ h)) (room (<ᵇ⇒< i n (Equivalence.from T-≡ lt)))
  ... | inj₂ (ge , h) with if⁻ {b = suc (i ∸ n) ≤ᵇ count (λ k → k <ᵖ q) ess} h
  ... | inj₁ (fr , h′) =
    subst (Starts i q ls) (sym (single⁻ h′)) (freed (n≤ ge) (Lt.→at q (i ∸ n) L (≤ᵇ⇒≤ _ _ (Equivalence.from T-≡ fr))))
  ... | inj₂ (_ , h′) with cm⁻ {xs = ess} h′
  ... | (es , esm , h″) with cm⁻ {xs = es} h″
  ... | (c , cm , h‴) with when⁻ h‴
  ... | (b , e) with ∧-true {q <ᵖ c} b
  ... | (qc , b′) with ∧-true {suc (i ∸ n) ≤ᵇ count (λ k → k ≼ᵇ c) ess} b′
  ... | (le , nlt) = subst (Starts i q ls) (sym e) (queued (n≤ ge) (Equivalence.from T-≡ qc) (→one L esm cm)
    (Le.→at c (i ∸ n) L (≤ᵇ⇒≤ _ _ (Equivalence.from T-≡ le)))
    (λ h → not-T nlt (≤⇒≤ᵇ (Lt.at→ c (i ∸ n) L h))))

  starts-c : ∀ {i q ess ls s} → Lists ess ls → Starts i q ls s → s ∈ starts i q ess
  starts-c L (room lt) = if-t (fromT (<⇒<ᵇ lt)) (here refl)
  starts-c L (freed le h) = if-f (lt-off le) (if-t (fromT (≤⇒≤ᵇ (Lt.at→ _ _ L h))) (here refl))
  starts-c {i} {q} {ess} L (queued {c} le qc one h nh) =
    let (es , esm , cm) = one→ L one in
    if-f (lt-off le) (if-f (fromNot λ fr → nh (Kth-mono (λ {k} kq → ≺-trans {k} {q} {c} kq qc) (i ∸ n) (Lt.→at q (i ∸ n) L (≤ᵇ⇒≤ _ _ fr))))
      (cm⁺ {xs = ess} esm (cm⁺ {xs = es} cm (when⁺ (∧-intro (fromT qc)
        (∧-intro (fromT (≤⇒≤ᵇ (Le.at→ c (i ∸ n) L h))) (T-not λ fr → nh (Lt.→at c (i ∸ n) L (≤ᵇ⇒≤ _ _ fr)))))))))

  ----------------------------------------------------------------------
  -- A level's entries

  -- An entry of level `j`, read against the lanes before it.
  Fine : ℕ → Entry → Set
  Fine j (q , a , ss) = Nth j q a
    × (∀ {s l} → (s , l) ∈ ss → Starts j q (Sched j) s × ln a s ≡ just l)
    × (∀ {s} → Starts j q (Sched j) s → Σ (Listed B) λ l → (s , l) ∈ ss)

  entry-ok : ∀ j {ess} → Lists ess (Sched j) → ∀ {q a e} → (q , a) ∈ nths j → entry j ess (q , a) ≡ just e
    → Σ (List (Pos × Listed B)) λ ss → e ≡ (q , a , ss) × Fine j (q , a , ss)
  entry-ok j {ess} L {q} {a} nm e with bind⁻ {m = mapM (laneAt a) (starts j q ess)} e
  ... | (ss , ems , refl) = ss , refl , nth-s j nm , snd , cmp
    where
    snd : ∀ {s l} → (s , l) ∈ ss → Starts j q (Sched j) s × ln a s ≡ just l
    snd m with mapM⁻ {xs = starts j q ess} ems m
    ... | (s′ , sm , ez) with bind⁻ {m = ln a s′} ez
    ... | (l′ , el , refl) = starts-s j q L sm , el

    cmp : ∀ {s} → Starts j q (Sched j) s → Σ (Listed B) λ l → (s , l) ∈ ss
    cmp {s} St with mapM⁺ {xs = starts j q ess} ems (starts-c L St)
    ... | (y , ym , ey) with bind⁻ {m = ln a s} ey
    ... | (l , el , refl) = l , ym

  -- A level's listed ends are its lanes' ends.
  ends-ok : ∀ i gs → (∀ {e} → e ∈ gs → Fine i e × (i , e) ∈ G)
    → (∀ {q a} → Nth i q a → Σ (List (Pos × Listed B)) λ ss → (q , a , ss) ∈ gs)
    → (∀ {c} → c ∈ endsOf gs → Ends i (Sched i) c) × (∀ {c} → Ends i (Sched i) c → c ∈ endsOf gs)
  ends-ok i gs ok found = snd-e , cmp-e
    where
    snd-e : ∀ {c} → c ∈ endsOf gs → Ends i (Sched i) c
    snd-e m with cm⁻ {xs = gs} m
    ... | ((q , a , ss) , em , h) with cm⁻ {xs = ss} h
    ... | ((s , l) , sm , h′) with ok em
    ... | ((N , snd , _) , gm) = let (St , el) = snd sm in q , a , s , N , St , sound (exl gm sm el) (ends⁻ h′)

    cmp-e : ∀ {c} → Ends i (Sched i) c → c ∈ endsOf gs
    cmp-e (q , a , s , N , St , y) with found N
    ... | (ss , em) with ok em
    ... | ((_ , snd , cmp) , gm) with cmp St
    ... | (l , sm) = cm⁺ {f = entryEnds} {xs = gs} em (cm⁺ {f = laneEnds} {xs = ss} sm (ends⁺ (complete (exl gm sm (proj₂ (snd sm))) y)))

  ----------------------------------------------------------------------
  -- Every level

  levels-ok : ∀ K i ess {G′} → levels K i ess (nths i) ≡ just G′ → (∀ {x} → x ∈ G′ → x ∈ G) → Lists ess (Sched i)
    → (∀ {j e} → (j , e) ∈ G′ → Fine j e)
    × (∀ {j q a} → i ≤ j → j < K + i → Nth j q a → Σ (List (Pos × Listed B)) λ ss → (j , q , a , ss) ∈ G′)
  levels-ok zero i ess refl sub L = (λ ()) , λ le lt N → ⊥-elim (≤⇒≯ le lt)
  levels-ok (suc K) i ess e sub L with bind⁻ {m = mapM (entry i ess) (nths i)} e
  ... | (gs , egs , e′) with bind⁻ {m = levels K (suc i) (endsOf gs ∷ ess) (nths (suc i))} e′
  ... | (rest , erest , refl) = sound-l , complete-l
    where
    good : ∀ {x} → x ∈ gs → Fine i x × (i , x) ∈ G
    good m with mapM⁻ {xs = nths i} egs m
    ... | ((q , a) , nm , ex) with entry-ok i L nm ex
    ... | (ss , refl , fn) = fn , sub (∈-++⁺ˡ (∈-map⁺ (i ,_) m))

    found : ∀ {q a} → Nth i q a → Σ (List (Pos × Listed B)) λ ss → (q , a , ss) ∈ gs
    found N with mapM⁺ {xs = nths i} egs (nth-c N)
    ... | (x , xm , ex) with entry-ok i L (nth-c N) ex
    ... | (ss , refl , _) = ss , xm

    ih = levels-ok K (suc i) (endsOf gs ∷ ess) erest (λ m → sub (∈-++⁺ʳ (mapL (i ,_) gs) m)) (ends-ok i gs good found , L)

    sound-l : ∀ {j x} → (j , x) ∈ mapL (i ,_) gs ++ rest → Fine j x
    sound-l m with ∈-++⁻ (mapL (i ,_) gs) m
    ... | inj₁ h with ∈-map⁻ (i ,_) h
    ... | (x , xm , refl) = proj₁ (good xm)
    sound-l m | inj₂ h = proj₁ ih h

    complete-l : ∀ {j q a} → i ≤ j → j < suc K + i → Nth j q a
      → Σ (List (Pos × Listed B)) λ ss → (j , q , a , ss) ∈ mapL (i ,_) gs ++ rest
    complete-l {j} le lt N with m≤n⇒m<n∨m≡n le
    ... | inj₂ refl = let (ss , xm) = found N in ss , ∈-++⁺ˡ (∈-map⁺ (i ,_) xm)
    ... | inj₁ lt′ = let (ss , xm) = proj₂ ih lt′ (subst (λ x → j < x) (sym (+-suc K i)) lt) N in
      ss , ∈-++⁺ʳ (mapL (i ,_) gs) xm

  private
    levG = levels-ok (length vals) 0 [] eG (λ m → m) tt

    fine-all : ∀ {j e} → (j , e) ∈ G → Fine j e
    fine-all = proj₁ levG

    -- Every value's level is listed.
    found-all : ∀ {j q a} → Nth j q a → Σ (List (Pos × Listed B)) λ ss → (j , q , a , ss) ∈ G
    found-all N = proj₂ levG z≤n
      (subst (λ x → _ < x) (sym (+-identityʳ (length vals)))
        (≤-<-trans (nth-cnt N) (cnt-in (values⁺ (complete exo (nth-val N)))))) N

    sub-of : ∀ {j q a ss s l} → (j , q , a , ss) ∈ G → (s , l) ∈ ss → Sub j q s a × Exact l (After (fD a) s)
    sub-of gm sm = let (N , snd , _) = fine-all gm ; (St , el) = snd sm in (N , St) , exl gm sm el

  ----------------------------------------------------------------------
  -- The tests

  private
    queued→ : ∀ c → queuedᵇ G c ≡ true → Queued c
    queued→ c e with any⁻ {xs = G} e
    ... | ((j , q , a , ss) , gm , h) with any⁻ {xs = ss} h
    ... | ((s , l) , sm , d) with ≟-true {s} {c ++ [ ix 1 ]} d
    ... | refl = j , q , a , proj₁ (sub-of gm sm)

    →queued : ∀ c → Queued c → queuedᵇ G c ≡ true
    →queued c (j , q , a , N , St) =
      let (ss , gm) = found-all N ; (l , sm) = proj₂ (proj₂ (fine-all gm)) St in
      any⁺ {xs = G} gm (any⁺ {xs = ss} sm (≟-refl (c ++ [ ix 1 ])))

    done→ : ∀ c → done G c ≡ true → Done c
    done→ c e with ∧-true {endBy (rows o) c} e
    ... | (e₁ , e₂) = endBy→ exo {c} e₁ , λ x ix qc _ → lanes x ix qc
      where
      lanes : ∀ {q a} → t q (out a) → Indexed q → Tb._≺_ q c → Tb.Ended (Lane q a) c
      lanes x (i , _ , N₀) qc with found-all (nth-at N₀ x)
      ... | (ss , gm) with any⁻ {xs = ss} (or-right (fromT qc) (all⁻ {xs = G} e₂ gm))
      ... | ((s , l) , sm , eb) with sub-of gm sm
      ... | (sb , ex) with endBy→ ex {c} eb
      ... | (c′ , y , le) = c′ , (i , s , sb , y) , le

    →done : ∀ c → Done c → done G c ≡ true
    →done c ((c₀ , x , le) , lanes) = ∧-intro (→endBy exo {c₀} {c} x le) (all⁺ {xs = G} λ { {j , q , a , ss} gm →
      or-of (q <ᵖ c) λ qc →
      let (N , _ , cmp) = fine-all gm ; (c′ , (_ , s , (N′ , St) , y) , le′) = lanes (nth-val N) (_ , _ , N) (Equivalence.from T-≡ qc) (λ ())
          (l , sm) = cmp (subst (λ i → Starts i q (Sched i) s) (nth-inj N′ N) St) in
      any⁺ {xs = ss} sm (→endBy (proj₂ (sub-of gm sm)) {c′} {c} y le′) })

  ----------------------------------------------------------------------
  -- The rows

  private
    if-split : ∀ {X : Set} b {x y z : X} → z ≡ (if b then x else y) → (b ≡ true × z ≡ x) ⊎ (b ≡ false × z ≡ y)
    if-split true  e = inj₁ (refl , e)
    if-split false e = inj₂ (refl , e)

    if≡t : ∀ {X : Set} {b} {x y : X} → b ≡ true → (if b then x else y) ≡ x
    if≡t refl = refl

    if≡f : ∀ {X : Set} {b} {x y : X} → b ≡ false → (if b then x else y) ≡ y
    if≡f refl = refl

    end-row : ∀ {c} → t c end → JoinT c (if done G c then end else skip)
    end-row {c} x with done G c in dc
    ... | true  = oend x (done→ c dc)
    ... | false = opass x (λ D → offT dc (Equivalence.from T-≡ (→done c D)))

    lend-row : ∀ {j q s a c} → Sub j q s a → After (fD a) s c end → ¬ Queued c → JoinT c (if done G c then end else skip)
    lend-row {j} {s = s} {a} {c} sb@(N , _) y nQ with done G c in dc
    ... | true  = lend (nth-val N) (j , a , N) (j , s , sb , y) (λ ()) nQ (done→ c dc)
    ... | false = lpass (nth-val N) (j , a , N) (j , s , sb , y) (λ ()) nQ (λ D → offT dc (Equivalence.from T-≡ (→done c D)))

    outer-s : ∀ {r q e} → r ∈ rows o → (q , e) ∈ outerRow (done G) r → JoinT q e
    outer-s {k , out a} rm h with single⁻ h
    ... | refl = val (sound exo rm)
    outer-s {k , skip} rm h with single⁻ h
    ... | refl = step (sound exo rm)
    outer-s {c , end} rm h with single⁻ h
    ... | refl = end-row (sound exo rm)

    lane-s : ∀ {j q a ss s l r k e} → (j , q , a , ss) ∈ G → (s , l) ∈ ss → r ∈ rows l → (k , e) ≡ laneRow G r → JoinT k e
    lane-s {j} {a = a} {s = s} {r = k′ , out b} gm sm rm refl = let (sb , ex) = sub-of gm sm in
      lane (nth-val (proj₁ sb)) (j , a , proj₁ sb) (j , s , sb , sound ex rm) (λ ()) tt
    lane-s {j} {a = a} {s = s} {r = k′ , skip}  gm sm rm refl = let (sb , ex) = sub-of gm sm in
      lane (nth-val (proj₁ sb)) (j , a , proj₁ sb) (j , s , sb , sound ex rm) (λ ()) tt
    lane-s {j} {a = a} {s = s} {r = c , end} gm sm rm eq with if-split (queuedᵇ G c) eq
    ... | inj₁ (qc , refl) = let (sb , ex) = sub-of gm sm in
      hand (nth-val (proj₁ sb)) (j , a , proj₁ sb) (j , s , sb , sound ex rm) (λ ()) (queued→ c qc)
    ... | inj₂ (nq , refl) = let (sb , ex) = sub-of gm sm in
      lend-row sb (sound ex rm) (λ Q → offT nq (Equivalence.from T-≡ (→queued c Q)))

    outer-end : ∀ {c b} → done G c ≡ b → (c , (if b then end else skip)) ∈ outerRow {A} {B} (done G) (c , end)
    outer-end refl = here refl

    lane-in : ∀ {k e} {rs : List (Row B)} → Tb.Work e → (k , e) ∈ rs → (k , e) ∈ mapL (laneRow G) rs
    lane-in {e = out b} _ r = ∈-map⁺ (laneRow G) r
    lane-in {e = skip}  _ r = ∈-map⁺ (laneRow G) r
    lane-in {e = end}   () r

    -- A lane's row, under some schedule.
    shown : ∀ {j q s a r} → Sub j q s a → (∀ {l} → Exact l (After (fD a) s) → r ∈ mapL (laneRow G) (rows l))
      → r ∈ rows (boundedRows G)
    shown (N , St) h =
      let (ss , gm) = found-all N ; (l , sm) = proj₂ (proj₂ (fine-all gm)) St in
      ∈-++⁺ʳ (concatMap (outerRow (done G)) (rows o)) (cm⁺ {xs = G} gm (cm⁺ {xs = ss} sm (h (proj₂ (sub-of gm sm)))))

    passing : ∀ c → ¬ Queued c → laneRow G (c , end) ≡ (c , (if done G c then end else skip))
    passing c nQ = if≡f {b = queuedᵇ G c} (off (queued→ c) nQ)

  sound-b : ∀ {q e} → (q , e) ∈ rows (boundedRows G) → JoinT q e
  sound-b m with ∈-++⁻ (concatMap (outerRow (done G)) (rows o)) m
  ... | inj₁ h = let (r , rm , h′) = cm⁻ {xs = rows o} h in outer-s rm h′
  ... | inj₂ h with cm⁻ {xs = G} h
  ... | ((j , q , a , ss) , gm , h′) with cm⁻ {xs = ss} h′
  ... | ((s , l) , sm , h″) with ∈-map⁻ (laneRow G) h″
  ... | (r , rm , eq) = lane-s gm sm rm eq

  complete-b : ∀ {q e} → JoinT q e → (q , e) ∈ rows (boundedRows G)
  complete-b (val x)          = ∈-++⁺ˡ (cm⁺ (complete exo x) (here refl))
  complete-b (step x)         = ∈-++⁺ˡ (cm⁺ (complete exo x) (here refl))
  complete-b (oend {c} x D)   = ∈-++⁺ˡ (cm⁺ (complete exo x) (outer-end {c} (→done c D)))
  complete-b (opass {c} x nD) = ∈-++⁺ˡ (cm⁺ (complete exo x) (outer-end {c} (off (done→ c) nD)))
  complete-b (lane _ _ (_ , _ , sb , y) _ w) = shown sb λ ex → lane-in w (complete ex y)
  complete-b (hand {c = c} _ _ (_ , _ , sb , y) _ Q) = shown sb λ ex →
    subst (_∈ _) (if≡t {b = queuedᵇ G c} (→queued c Q)) (∈-map⁺ (laneRow G) (complete ex y))
  complete-b (lend {c = c} _ _ (_ , _ , sb , y) _ nQ D) = shown sb λ ex →
    subst (_∈ _) (trans (passing c nQ) (cong (λ b → c , (if b then end else skip)) (→done c D))) (∈-map⁺ (laneRow G) (complete ex y))
  complete-b (lpass {c = c} _ _ (_ , _ , sb , y) _ nQ nD) = shown sb λ ex →
    subst (_∈ _) (trans (passing c nQ) (cong (λ b → c , (if b then end else skip)) (off (done→ c) nD))) (∈-map⁺ (laneRow G) (complete ex y))
  complete-b (left _ _ _ () _)
  complete-b (run () _)
  complete-b (rend () _ _)
  complete-b (rpass () _ _)
  complete-b (rhand () _)

bounded-exact : ∀ {A B} (k : ℕ) (fD : A → Den B) (t : EmissionSet A) (ln : A → Pos → Maybe (Listed B)) (o : Listed A)
  → Exactly o t → (∀ {a s l} → ln a s ≡ just l → Exactly l (After (fD a) s))
  → ∀ {l} → BoundedL.listB k ln o ≡ just l → Exactly l (Tb.Bounded.JoinT k fD t)
bounded-exact k fD t ln o eo eln e u with bind⁻ {m = BoundedL.levels k ln o (length (values (rows o))) 0 [] (Order.nths (values (rows o)) 0)} e
... | (G , eG , refl) = record { sound = sound-b ; complete = complete-b }
  where open BoundedX k fD t ln o eo eln G eG u
