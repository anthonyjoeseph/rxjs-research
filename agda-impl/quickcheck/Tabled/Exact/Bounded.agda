{-# OPTIONS --guardedness #-}

-- BOUNDED MERGE, LISTED EXACTLY: `Bounded.Sched` level by level, as the
-- listing grows it.  Each level's schedules are exactly that level's
-- `Sched`s, and each value's entry holds its lane under every schedule
-- and every start `Starts` allows.  A value's level is below its count of
-- values before it, so the listing's levels reach every value.
module quickcheck.Tabled.Exact.Bounded where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Bool.Properties using (T-≡)
open import Function.Bundles using (Equivalence)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; length; null) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; _<ᵇ_; _≤ᵇ_; _≡ᵇ_; z≤n)
open import Data.Nat.Properties
  using (<ᵇ⇒<; <⇒<ᵇ; ≡ᵇ⇒≡; ≡⇒≡ᵇ; ≤ᵇ⇒≤; ≤⇒≤ᵇ; ≮⇒≥; <⇒≱; ≤⇒≯; m≤n⇒m<n∨m≡n; +-suc; +-identityʳ; ≤-<-trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import denotation.MonotonicList.Events using (Pos; _<ᵖ_; ix; <ᵖ-asym)
open import denotation.EmissionSet using (out; skip; end; EmissionSet; Den; enter; below)
import denotation.EmissionSet as Tb
open import quickcheck.Tabled using (Row; Listed; rows; short; concatMap; concatMapM; mapM; endBy; ends; values; outerRow;
  module BoundedL; module Order)
open import quickcheck.Tabled.Exact.Base
  using (Exact; Exactly; sound; complete; fromT; fromNot; offT; ∨-false; ∧-true; ∧-intro; off; ≟-refl; ≟-true;
  any⁻; any⁺; any-off; all⁻; all⁺; single⁻; when⁻; when⁺; if⁻; if-t; if-f; cm⁻; cm⁺; bind⁻; mapM⁻; mapM⁺; cmM⁻; cmM⁺;
  null⁻; null⁺; null-off; values⁺; ends⁻; ends⁺; endBy→; →endBy; cnt-in; module OrderX)

module BoundedX {A B : Set} (n : ℕ) (fD : A → Den B) (t : EmissionSet A) (ln : A → Pos → Maybe (Listed B)) (o : Listed A)
  (eo : Exactly o t) (eln : ∀ {a s l} → ln a s ≡ just l → Exactly l (enter (fD a) s))
  (G : List (ℕ × Pos × A × List (List Pos × Pos × Listed B)))
  (eG : BoundedL.levels n ln o (length (values (rows o))) 0 [ [] ] ≡ just G)
  (u : short (BoundedL.boundedRows n ln o G) ≡ false)
  where
  open Tb.Bounded n fD t
    using (Starts; room; freed; queued; Sched; none; ended; runs; held; Sub; Queued; Done; BoundedT;
    val; step; oend; opass; lane; handoff; lend; lpass)
  open Tb.Values t using (Nth)
  open BoundedL n ln o
    using (vals; freedAt; starts; Entry; laneAt; entry; grownE; heldE; grow; levels; done; laneRow; boundedRows)
    renaming (queued to queuedᵇ)
  open Order vals using (nths)

  private
    exo : Exact o t
    exo = eo (proj₁ (∨-false {short o} u))

    uncut : ∀ {j q a ss es s l} → (j , q , a , ss) ∈ G → (es , s , l) ∈ ss → short l ≡ false
    uncut {ss = ss} gm sm = any-off {xs = ss} (any-off {xs = G} (proj₂ (∨-false {short o} u)) gm) sm

    exl : ∀ {j q a ss es s l} → (j , q , a , ss) ∈ G → (es , s , l) ∈ ss → ln a s ≡ just l → Exact l (enter (fD a) s)
    exl gm sm el = eln el (uncut gm sm)

  open OrderX exo using (nth-s; nth-c; nth-out; nth-cnt)

  ----------------------------------------------------------------------
  -- Where a lane starts

  private
    n≤ : ∀ {i} → (i <ᵇ n) ≡ false → n ≤ i
    n≤ ge = ≮⇒≥ (λ lt → offT ge (<⇒<ᵇ lt))

    lt-off : ∀ {i} → n ≤ i → (i <ᵇ n) ≡ false
    lt-off {i} le = fromNot λ h → <⇒≱ (<ᵇ⇒< i n h) le

  freedAt-s : ∀ i q es c {s} → n ≤ i → c ∈ es → s ∈ freedAt i q es c → Starts i q es s
  freedAt-s i q es c le cm h with if⁻ {b = below c es ≡ᵇ (i ∸ n)} h
  ... | inj₂ (_ , ())
  ... | inj₁ (kb , h′) with if⁻ {b = c <ᵖ q} h′
  ... | inj₁ (cq , h″) =
    subst (Starts i q es) (sym (single⁻ h″)) (freed le (cm , ≡ᵇ⇒≡ (below c es) (i ∸ n) (Equivalence.from T-≡ kb)) (Equivalence.from T-≡ cq))
  ... | inj₂ (_ , h″) = let (qc , e) = when⁻ h″ in
    subst (Starts i q es) (sym e) (queued le (cm , ≡ᵇ⇒≡ (below c es) (i ∸ n) (Equivalence.from T-≡ kb)) (Equivalence.from T-≡ qc))

  starts-s : ∀ i q es {s} → s ∈ starts i q es → Starts i q es s
  starts-s i q es m with if⁻ {b = i <ᵇ n} m
  ... | inj₁ (lt , h) = subst (Starts i q es) (sym (single⁻ h)) (room (<ᵇ⇒< i n (Equivalence.from T-≡ lt)))
  ... | inj₂ (ge , h) = let (c , cm , h′) = cm⁻ {xs = es} h in freedAt-s i q es c (n≤ ge) cm h′

  starts-c : ∀ {i q es s} → Starts i q es s → s ∈ starts i q es
  starts-c (room lt) = if-t (fromT (<⇒<ᵇ lt)) (here refl)
  starts-c {i} {q} {es} (freed {c} le (cm , kb) cq) =
    if-f (lt-off le) (cm⁺ cm (if-t (fromT (≡⇒≡ᵇ (below c es) (i ∸ n) kb)) (if-t (fromT cq) (here refl))))
  starts-c {i} {q} {es} (queued {c} le (cm , kb) qc) =
    if-f (lt-off le) (cm⁺ cm (if-t (fromT (≡⇒≡ᵇ (below c es) (i ∸ n) kb)) (if-f (<ᵖ-asym q c (fromT qc)) (when⁺ (fromT qc)))))

  ----------------------------------------------------------------------
  -- A level's entries

  -- An entry of level `j`, built from the schedules `ess`.
  Good : ℕ → List (List Pos) → Entry → Set
  Good j ess (q , a , ss) = Nth j q a
    × (∀ {es s l} → (es , s , l) ∈ ss → es ∈ ess × Starts j q es s × ln a s ≡ just l)
    × (∀ {es s} → es ∈ ess → Starts j q es s → Σ (Listed B) λ l → (es , s , l) ∈ ss)

  -- An entry of level `j`, read against `Sched j`.
  Fine : ℕ → Entry → Set
  Fine j (q , a , ss) = Nth j q a
    × (∀ {es s l} → (es , s , l) ∈ ss → Sched j es × Starts j q es s × ln a s ≡ just l)
    × (∀ {es s} → Sched j es → Starts j q es s → Σ (Listed B) λ l → (es , s , l) ∈ ss)

  -- Level `i`'s schedules are exactly `Sched i`'s.
  Lv : ℕ → List (List Pos) → Set
  Lv i ess = (∀ {es} → es ∈ ess → Sched i es) × (∀ {es} → Sched i es → es ∈ ess)

  entry-ok : ∀ j ess {q a e} → (q , a) ∈ nths j → entry j ess (q , a) ≡ just e
    → Σ (List (List Pos × Pos × Listed B)) λ ss → e ≡ (q , a , ss) × Good j ess (q , a , ss)
  entry-ok j ess {q} {a} nm e with bind⁻ {m = concatMapM (λ es → mapM (laneAt a es) (starts j q es)) ess} e
  ... | (ss , ecm , refl) = ss , refl , nth-s j nm , snd , cmp
    where
    snd : ∀ {es s l} → (es , s , l) ∈ ss → es ∈ ess × Starts j q es s × ln a s ≡ just l
    snd m with cmM⁻ {xs = ess} ecm m
    ... | (es′ , esm , zs , fz , h) with mapM⁻ {xs = starts j q es′} fz h
    ... | (s′ , sm , ez) with bind⁻ {m = ln a s′} ez
    ... | (l′ , el , refl) = esm , starts-s j q es′ sm , el

    cmp : ∀ {es s} → es ∈ ess → Starts j q es s → Σ (Listed B) λ l → (es , s , l) ∈ ss
    cmp {es} {s} esm St with cmM⁺ {xs = ess} ecm esm
    ... | (zs , fz , k) with mapM⁺ {xs = starts j q es} fz (starts-c St)
    ... | (y , ym , ey) with bind⁻ {m = ln a s} ey
    ... | (l , el , refl) = l , k ym

  fine : ∀ {j ess e} → Lv j ess → Good j ess e → Fine j e
  fine {e = q , a , ss} lv (N , snd , cmp) =
    N , (λ m → let (esm , St , el) = snd m in proj₁ lv esm , St , el) , λ S St → cmp (proj₂ lv S) St

  ----------------------------------------------------------------------
  -- The next level

  grow-ok : ∀ i ess gs → Lv i ess → (∀ {e} → e ∈ gs → Fine i e × (i , e) ∈ G)
    → (∀ {q a} → Nth i q a → Σ (List (List Pos × Pos × Listed B)) λ ss → (q , a , ss) ∈ gs)
    → Lv (suc i) (grow i ess gs)
  grow-ok i ess gs lv ok found = sound-g , complete-g
    where
    sound-g : ∀ {es′} → es′ ∈ grow i ess gs → Sched (suc i) es′
    sound-g m with ∈-++⁻ (concatMap grownE gs) m
    ... | inj₁ h with cm⁻ {xs = gs} h
    ... | ((q , a , ss) , em , h′) with cm⁻ {xs = ss} h′
    ... | ((es , s , l) , sm , h″) with ok em
    ... | ((N , snd , _) , gm) with snd sm
    ... | (S , St , el) with if⁻ {b = null (ends (rows l))} h″
    ... | inj₁ (nl , h‴) =
      subst (Sched (suc i)) (sym (single⁻ h‴)) (runs S N St λ y → null⁻ nl (ends⁺ (complete (exl gm sm el) y)))
    ... | inj₂ (_ , h‴) = let (c , cm , e) = ∈-map⁻ (_∷ es) h‴ in
      subst (Sched (suc i)) (sym e) (ended S N St (sound (exl gm sm el) (ends⁻ cm)))
    sound-g m | inj₂ h with cm⁻ {xs = gs} h
    ... | ((q , a , ss) , em , h′) with cm⁻ {xs = ess} h′
    ... | (es , esm , h″) with when⁻ h″
    ... | (hb , refl) with ∧-true {n ≤ᵇ i} hb
    ... | (h₁ , h₂) = held (proj₁ lv esm) (proj₁ (proj₁ (ok em)))
      (≤ᵇ⇒≤ n i (Equivalence.from T-≡ h₁)) (≤ᵇ⇒≤ (length es) (i ∸ n) (Equivalence.from T-≡ h₂))

    complete-g : ∀ {es′} → Sched (suc i) es′ → es′ ∈ grow i ess gs
    complete-g (ended {es = es} S N St y) with found N
    ... | (ss , em) with ok em
    ... | ((_ , snd , cmp) , gm) with cmp S St
    ... | (l , sm) with snd sm
    ... | (_ , _ , el) = let cm = ends⁺ (complete (exl gm sm el) y) in
      ∈-++⁺ˡ (cm⁺ em (cm⁺ sm (if-f (null-off cm) (∈-map⁺ (_∷ es) cm))))
    complete-g (runs S N St ne) with found N
    ... | (ss , em) with ok em
    ... | ((_ , snd , cmp) , gm) with cmp S St
    ... | (l , sm) with snd sm
    ... | (_ , _ , el) = ∈-++⁺ˡ (cm⁺ em (cm⁺ sm (if-t (null⁺ λ cm → ne (sound (exl gm sm el) (ends⁻ cm))) (here refl))))
    complete-g (held S N le le′) with found N
    ... | (ss , em) =
      ∈-++⁺ʳ (concatMap grownE gs) (cm⁺ em (cm⁺ (proj₂ lv S) (when⁺ (∧-intro (fromT (≤⇒≤ᵇ le)) (fromT (≤⇒≤ᵇ le′))))))

  ----------------------------------------------------------------------
  -- Every level

  levels-ok : ∀ K i ess {G′} → levels K i ess ≡ just G′ → (∀ {x} → x ∈ G′ → x ∈ G) → Lv i ess
    → (∀ {j e} → (j , e) ∈ G′ → Fine j e)
    × (∀ {j q a} → i ≤ j → j < K + i → Nth j q a → Σ (List (List Pos × Pos × Listed B)) λ ss → (j , q , a , ss) ∈ G′)
  levels-ok zero i ess refl sub lv = (λ ()) , λ le lt N → ⊥-elim (≤⇒≯ le lt)
  levels-ok (suc K) i ess e sub lv with bind⁻ {m = mapM (entry i ess) (nths i)} e
  ... | (gs , egs , e′) with bind⁻ {m = levels K (suc i) (grow i ess gs)} e′
  ... | (rest , erest , refl) = sound-l , complete-l
    where
    good : ∀ {x} → x ∈ gs → Fine i x × (i , x) ∈ G
    good m with mapM⁻ {xs = nths i} egs m
    ... | ((q , a) , nm , ex) with entry-ok i ess nm ex
    ... | (ss , refl , gd) = fine lv gd , sub (∈-++⁺ˡ (∈-map⁺ (i ,_) m))

    found : ∀ {q a} → Nth i q a → Σ (List (List Pos × Pos × Listed B)) λ ss → (q , a , ss) ∈ gs
    found N with mapM⁺ {xs = nths i} egs (nth-c N)
    ... | (x , xm , ex) with entry-ok i ess (nth-c N) ex
    ... | (ss , refl , _) = ss , xm

    ih = levels-ok K (suc i) (grow i ess gs) erest (λ m → sub (∈-++⁺ʳ (mapL (i ,_) gs) m)) (grow-ok i ess gs lv good found)

    sound-l : ∀ {j x} → (j , x) ∈ mapL (i ,_) gs ++ rest → Fine j x
    sound-l m with ∈-++⁻ (mapL (i ,_) gs) m
    ... | inj₁ h with ∈-map⁻ (i ,_) h
    ... | (x , xm , refl) = proj₁ (good xm)
    sound-l m | inj₂ h = proj₁ ih h

    complete-l : ∀ {j q a} → i ≤ j → j < suc K + i → Nth j q a
      → Σ (List (List Pos × Pos × Listed B)) λ ss → (j , q , a , ss) ∈ mapL (i ,_) gs ++ rest
    complete-l {j} le lt N with m≤n⇒m<n∨m≡n le
    ... | inj₂ refl = let (ss , xm) = found N in ss , ∈-++⁺ˡ (∈-map⁺ (i ,_) xm)
    ... | inj₁ lt′ = let (ss , xm) = proj₂ ih lt′ (subst (λ x → j < x) (sym (+-suc K i)) lt) N in
      ss , ∈-++⁺ʳ (mapL (i ,_) gs) xm

  private
    lv₀ : Lv 0 [ [] ]
    lv₀ = (λ { (here refl) → none ; (there ()) }) , λ { none → here refl }

    levG = levels-ok (length vals) 0 [ [] ] eG (λ m → m) lv₀

    fine-all : ∀ {j e} → (j , e) ∈ G → Fine j e
    fine-all = proj₁ levG

    -- Every value's level is listed.
    found-all : ∀ {j q a} → Nth j q a → Σ (List (List Pos × Pos × Listed B)) λ ss → (j , q , a , ss) ∈ G
    found-all N = proj₂ levG z≤n
      (subst (λ x → _ < x) (sym (+-identityʳ (length vals)))
        (≤-<-trans (nth-cnt N) (cnt-in (values⁺ (complete exo (nth-out N)))))) N

    sub-of : ∀ {j q a ss es s l} → (j , q , a , ss) ∈ G → (es , s , l) ∈ ss → Sub j q s a × Exact l (enter (fD a) s)
    sub-of gm sm = let (N , snd , _) = fine-all gm ; (S , St , el) = snd sm in (_ , S , N , St) , exl gm sm el

  ----------------------------------------------------------------------
  -- The tests

  private
    queued→ : ∀ c → queuedᵇ G c ≡ true → Queued c
    queued→ c e with any⁻ {xs = G} e
    ... | ((j , q , a , ss) , gm , h) with any⁻ {xs = ss} h
    ... | ((es , s , l) , sm , d) with ≟-true {s} {c ++ [ ix 1 ]} d
    ... | refl = j , q , a , proj₁ (sub-of gm sm)

    →queued : ∀ c → Queued c → queuedᵇ G c ≡ true
    →queued c (j , q , a , es , S , N , St) =
      let (ss , gm) = found-all N ; (l , sm) = proj₂ (proj₂ (fine-all gm)) S St in
      any⁺ {xs = G} gm (any⁺ {xs = ss} sm (≟-refl (c ++ [ ix 1 ])))

    done→ : ∀ c → done G c ≡ true → Done c
    done→ c e with ∧-true {endBy (rows o) c} e
    ... | (e₁ , e₂) = endBy→ exo {c} e₁ , lanes
      where
      lanes : ∀ {i q a} → Nth i q a → Σ Pos λ s → Σ Pos λ c′ → Sub i q s a × enter (fD a) s c′ end × Tb._≼_ c′ c
      lanes N with found-all N
      ... | (ss , gm) with any⁻ {xs = ss} (all⁻ {xs = G} e₂ gm)
      ... | ((es , s , l) , sm , eb) with sub-of gm sm
      ... | (sb , ex) with endBy→ ex {c} eb
      ... | (c′ , y , le) = s , c′ , sb , y , le

    →done : ∀ c → Done c → done G c ≡ true
    →done c ((c₀ , x , le) , lanes) = ∧-intro (→endBy exo {c₀} {c} x le) (all⁺ {xs = G} λ { {j , q , a , ss} gm →
      let (N , _ , cmp) = fine-all gm ; (s , c′ , (es , S , _ , St) , y , le′) = lanes N ; (l , sm) = cmp S St in
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

    end-row : ∀ {c} → t c end → BoundedT c (if done G c then end else skip)
    end-row {c} x with done G c in dc
    ... | true  = oend x (done→ c dc)
    ... | false = opass x (λ D → offT dc (Equivalence.from T-≡ (→done c D)))

    lend-row : ∀ {j q s a c} → Sub j q s a → enter (fD a) s c end → ¬ Queued c → BoundedT c (if done G c then end else skip)
    lend-row {c = c} sb y nQ with done G c in dc
    ... | true  = lend sb y nQ (done→ c dc)
    ... | false = lpass sb y nQ (λ D → offT dc (Equivalence.from T-≡ (→done c D)))

    outer-s : ∀ {r q e} → r ∈ rows o → (q , e) ∈ outerRow (done G) r → BoundedT q e
    outer-s {k , out a} rm h with single⁻ h
    ... | refl = val (sound exo rm)
    outer-s {k , skip} rm h with single⁻ h
    ... | refl = step (sound exo rm)
    outer-s {c , end} rm h with single⁻ h
    ... | refl = end-row (sound exo rm)

    lane-s : ∀ {j q a ss es s l r k e} → (j , q , a , ss) ∈ G → (es , s , l) ∈ ss → r ∈ rows l → (k , e) ≡ laneRow G r → BoundedT k e
    lane-s {r = k′ , out b} gm sm rm refl = let (sb , ex) = sub-of gm sm in lane sb (sound ex rm) tt
    lane-s {r = k′ , skip}  gm sm rm refl = let (sb , ex) = sub-of gm sm in lane sb (sound ex rm) tt
    lane-s {r = c , end} gm sm rm eq with if-split (queuedᵇ G c) eq
    ... | inj₁ (qc , refl) = let (sb , ex) = sub-of gm sm in handoff sb (sound ex rm) (queued→ c qc)
    ... | inj₂ (nq , refl) = let (sb , ex) = sub-of gm sm in
      lend-row sb (sound ex rm) (λ Q → offT nq (Equivalence.from T-≡ (→queued c Q)))

    outer-end : ∀ {c b} → done G c ≡ b → (c , (if b then end else skip)) ∈ outerRow {A} {B} (done G) (c , end)
    outer-end refl = here refl

    lane-in : ∀ {k e} {rs : List (Row B)} → Tb.Work e → (k , e) ∈ rs → (k , e) ∈ mapL (laneRow G) rs
    lane-in {e = out b} _ r = ∈-map⁺ (laneRow G) r
    lane-in {e = skip}  _ r = ∈-map⁺ (laneRow G) r
    lane-in {e = end}   () r

    -- A lane's row, under some schedule.
    shown : ∀ {j q s a r} → Sub j q s a → (∀ {l} → Exact l (enter (fD a) s) → r ∈ mapL (laneRow G) (rows l))
      → r ∈ rows (boundedRows G)
    shown (es , S , N , St) h =
      let (ss , gm) = found-all N ; (l , sm) = proj₂ (proj₂ (fine-all gm)) S St in
      ∈-++⁺ʳ (concatMap (outerRow (done G)) (rows o)) (cm⁺ {xs = G} gm (cm⁺ {xs = ss} sm (h (proj₂ (sub-of gm sm)))))

    passing : ∀ c → ¬ Queued c → laneRow G (c , end) ≡ (c , (if done G c then end else skip))
    passing c nQ = if≡f {b = queuedᵇ G c} (off (queued→ c) nQ)

  sound-b : ∀ {q e} → (q , e) ∈ rows (boundedRows G) → BoundedT q e
  sound-b m with ∈-++⁻ (concatMap (outerRow (done G)) (rows o)) m
  ... | inj₁ h = let (r , rm , h′) = cm⁻ {xs = rows o} h in outer-s rm h′
  ... | inj₂ h with cm⁻ {xs = G} h
  ... | ((j , q , a , ss) , gm , h′) with cm⁻ {xs = ss} h′
  ... | ((es , s , l) , sm , h″) with ∈-map⁻ (laneRow G) h″
  ... | (r , rm , eq) = lane-s gm sm rm eq

  complete-b : ∀ {q e} → BoundedT q e → (q , e) ∈ rows (boundedRows G)
  complete-b (val x)          = ∈-++⁺ˡ (cm⁺ (complete exo x) (here refl))
  complete-b (step x)         = ∈-++⁺ˡ (cm⁺ (complete exo x) (here refl))
  complete-b (oend {c} x D)   = ∈-++⁺ˡ (cm⁺ (complete exo x) (outer-end {c} (→done c D)))
  complete-b (opass {c} x nD) = ∈-++⁺ˡ (cm⁺ (complete exo x) (outer-end {c} (off (done→ c) nD)))
  complete-b (lane sb y w)    = shown sb λ ex → lane-in w (complete ex y)
  complete-b (handoff {c = c} sb y Q) = shown sb λ ex →
    subst (_∈ _) (if≡t {b = queuedᵇ G c} (→queued c Q)) (∈-map⁺ (laneRow G) (complete ex y))
  complete-b (lend {c = c} sb y nQ D) = shown sb λ ex →
    subst (_∈ _) (trans (passing c nQ) (cong (λ b → c , (if b then end else skip)) (→done c D))) (∈-map⁺ (laneRow G) (complete ex y))
  complete-b (lpass {c = c} sb y nQ nD) = shown sb λ ex →
    subst (_∈ _) (trans (passing c nQ) (cong (λ b → c , (if b then end else skip)) (off (done→ c) nD))) (∈-map⁺ (laneRow G) (complete ex y))

bounded-exact : ∀ {A B} (k : ℕ) (fD : A → Den B) (t : EmissionSet A) (ln : A → Pos → Maybe (Listed B)) (o : Listed A)
  → Exactly o t → (∀ {a s l} → ln a s ≡ just l → Exactly l (enter (fD a) s))
  → ∀ {l} → BoundedL.listB k ln o ≡ just l → Exactly l (Tb.Bounded.BoundedT k fD t)
bounded-exact k fD t ln o eo eln e u with bind⁻ {m = BoundedL.levels k ln o (length (values (rows o))) 0 [ [] ]} e
... | (G , eG , refl) = record { sound = sound-b ; complete = complete-b }
  where open BoundedX k fD t ln o eo eln G eG u
