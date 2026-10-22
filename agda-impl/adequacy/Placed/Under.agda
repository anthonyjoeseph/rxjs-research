{-# OPTIONS --guardedness #-}

-- UNDER NO STEP: the rules holding a subscription at `P₀` off every
-- position just past a step of `σ`'s run apart from `P₀`.  A frame
-- keys its burst's root, and a join its source, so both carry the
-- clearance up; a source's own shows are clear of its run by its order.
module adequacy.Placed.Under where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)
open import Relation.Nullary using (¬_)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Events; Events∞; Pos; Tail; Tail∞; Timeline; end; hush; idle; ix; out; pin; skip; sub; _<ᵖ_;
  <ᵖ-asym; <ᵖ-below; <ᵖ-between; <ᵖ-irrefl; <ᵖ-split; ≮-trans)
open import denotation.MonotonicList using (tailᴱ)
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import adequacy.Finite using (Finite)
open import adequacy.Placed.Order using (Alienᴱ; Atop; Beneath; Clear; Disjoint; Every; EveryT; Every∞; Ext; Ordered; Owned; Past; Prefix; Steady; ext; everyT-mono; everyᵀ;
  every; every-monoᴱ; every∞-mono; ordered; prefix-++; steady)
open import adequacy.Placed.Keys using (alienᴱ-owned; beneath-owned; beneath-snoc; ix-mark; no-tick; owned-snoc; owned-tagged; owned-trans; prefix-refl; sibling; snoc-inj; tagged-sub)
open import adequacy.Placed.Rising using (Rules; module Reach; Shows; Showsᴱ; apartRules; everyT-zip; everyᴱ-shows; keyedRules; prefix-rest; prefix-split; shows)
open import adequacy.Placed.Trail using (Trail; Trailing; trail)

open Events∞
open Tail∞

-- A source's RUN: every position it shows, and past its end what it
-- leaves running, run on as its steps.  No cut before the end: a pin
-- there is a step it has yet to show.
mutual
  Runsˢ : ∀ {A} → (Pos → Set) → Events A → Tail → Set
  Runsˢ P (out h _ r) t = P h × Run P r
  Runsˢ P (skip h r)  t = P h × Run P r
  Runsˢ P (end h)     t = P h × EveryT P t
  Runsˢ P hush        t = ⊤

  Run : ∀ {A} → (Pos → Set) → Events∞ A → Set
  Run P r = Runs P (force r) (cut r)

  record Runs {A} (P : Pos → Set) (e : Events A) (t : Tail) : Set where
    coinductive
    field runs : Runsˢ P e t

open Runs public

mutual
  runs-mono : ∀ {A} {P Q : Pos → Set} → (∀ h → P h → Q h) → (e : Events A) → ∀ t → Runs P e t → Runs Q e t
  runs (runs-mono f (out h _ r) t pe) = f h (proj₁ (runs pe)) , run-mono f r (proj₂ (runs pe))
  runs (runs-mono f (skip h r)  t pe) = f h (proj₁ (runs pe)) , run-mono f r (proj₂ (runs pe))
  runs (runs-mono f (end h)     t pe) = f h (proj₁ (runs pe)) , everyT-mono f t (proj₂ (runs pe))
  runs (runs-mono f hush        t pe) = tt

  run-mono : ∀ {A} {P Q : Pos → Set} → (∀ h → P h → Q h) → (r : Events∞ A) → Run P r → Run Q r
  run-mono f r = runs-mono f (force r) (cut r)

mutual
  runs-zip : ∀ {A} {P Q : Pos → Set} (e : Events A) t → Runs P e t → Runs Q e t → Runs (λ h → P h × Q h) e t
  runs (runs-zip (out h _ r) t pe qe) = (proj₁ (runs pe) , proj₁ (runs qe)) , run-zip r (proj₂ (runs pe)) (proj₂ (runs qe))
  runs (runs-zip (skip h r)  t pe qe) = (proj₁ (runs pe) , proj₁ (runs qe)) , run-zip r (proj₂ (runs pe)) (proj₂ (runs qe))
  runs (runs-zip (end h)     t pe qe) = (proj₁ (runs pe) , proj₁ (runs qe)) , everyT-zip t (proj₂ (runs pe)) (proj₂ (runs qe))
  runs (runs-zip hush        t pe qe) = tt

  run-zip : ∀ {A} {P Q : Pos → Set} (r : Events∞ A) → Run P r → Run Q r → Run (λ h → P h × Q h) r
  run-zip r = runs-zip (force r) (cut r)

-- A run is no more than the state: every cut, not only the end's.
mutual
  every-runs : ∀ {A} {P : Pos → Set} (e : Events A) t → Every P e → EveryT P t → Runs P e t
  runs (every-runs (out h _ r) t pe pt) = proj₁ (every pe) , every-run r (proj₂ (every pe))
  runs (every-runs (skip h r)  t pe pt) = proj₁ (every pe) , every-run r (proj₂ (every pe))
  runs (every-runs (end h)     t pe pt) = every pe , pt
  runs (every-runs hush        t pe pt) = tt

  every-run : ∀ {A} {P : Pos → Set} (r : Events∞ A) → Every∞ P r → Run P r
  every-run r (pe , pt) = every-runs (force r) (cut r) pe pt

tail-runs : ∀ {A} {P : Pos → Set} t → EveryT P t → Runs {A} P (tailᴱ t) t
runs (tail-runs (pin k u) pt) = proj₁ (everyᵀ pt) , tail-runs (later u) (proj₂ (everyᵀ pt))
runs (tail-runs idle      pt) = tt

-- A source past its next step runs on within its run.
run-onward : ∀ {A} {P : Pos → Set} (σ : Events∞ A) → Run P σ → Run P (M′.onward∞ σ (force σ))
run-onward {P = P} σ u = go (force σ) u
  where
    go : ∀ e → Runs P e (cut σ) → Run P (M′.onward∞ σ e)
    go (out _ _ s) r = proj₂ (runs r)
    go (skip _ s)  r = proj₂ (runs r)
    go (end _)     r = tail-runs (cut σ) (proj₂ (runs r))
    go hush        r = u

-- Nothing at `h` lies just past `q`, when `q` stands apart from `P₀`.
Off : Pos → Pos → Pos → Set
Off P₀ h q = Disjoint P₀ q → ¬ Prefix (q ++ [ ix 0 ]) h

off-snoc : ∀ P₀ j l → Owned P₀ j → ∀ q → Off P₀ j q → Off P₀ (j ++ [ l ]) q
off-snoc P₀ j l oj q d dq pr with prefix-split (q ++ [ ix 0 ]) j l pr
... | inj₁ pr′ = d dq pr′
... | inj₂ eq  = proj₁ dq (subst (Owned P₀) (sym (proj₁ (snoc-inj q j eq))) oj)

frame-off : ∀ n e q → ¬ Prefix (q ++ [ ix 0 ]) (ix (suc n) ∷ sub e ∷ [])
frame-off n e []              (() , _)
frame-off n e (_ ∷ [])        (_ , () , _)
frame-off n e (_ ∷ _ ∷ [])    (_ , _ , ())
frame-off n e (_ ∷ _ ∷ _ ∷ _) (_ , _ , ())

off-join : ∀ P₀ q j q₁ → Off P₀ q q₁ → Off P₀ (q ++ [ sub j ]) q₁
off-join P₀ q j q₁ sq dq pr with prefix-split (q₁ ++ [ ix 0 ]) q (sub j) pr
... | inj₁ pr′ = sq dq pr′
... | inj₂ eq with snoc-inj q₁ q eq
...   | _ , ()

underRules : ∀ {A} → Pos → Events∞ A → Rules
underRules P₀ σ = record
  { S      = λ j → Owned P₀ j × Off∞ j
  ; P      = λ h → Beneath P₀ h × Off∞ h
  ; Src    = Off∞
  ; child  = λ j l _ sj → owned-snoc P₀ j l (proj₁ sj) , run-mono (off-snoc P₀ j l (proj₁ sj)) σ (proj₂ sj)
  ; deeper = λ h l _ ph → beneath-snoc P₀ h l (proj₁ ph) , run-mono (off-snoc P₀ h l (beneath-owned P₀ h (proj₁ ph))) σ (proj₂ ph)
  ; held   = λ h ph → beneath-owned P₀ h (proj₁ ph) , proj₂ ph
  ; frame  = λ n e pe _ → inj₂ (inj₁ (beneath-owned P₀ e (proj₁ pe))) , run-mono (λ q _ _ → frame-off n e q) σ (proj₂ pe)
  ; join   = λ q j sq sj _ → inj₂ (owned-tagged P₀ j (q ++ [ sub j ]) (proj₁ sj) (tagged-sub q j)) , run-mono (off-join P₀ q j) σ sq
  ; source = λ _ → proj₂
  }
  where
    Off∞ : Pos → Set
    Off∞ h = Run (Off P₀ h) σ

-- `e` shows `k`, its end included.
data Shown {A} (k : Pos) : Events A → Set where
  out-at  : ∀ {a r} → Shown k (out k a r)
  skip-at : ∀ {r} → Shown k (skip k r)
  end-at  : Shown k (end k)
  out-on  : ∀ {h a r} → Shown k (force r) → Shown k (out h a r)
  skip-on : ∀ {h r} → Shown k (force r) → Shown k (skip h r)

-- `t` would step at `k`.
data Pinned (k : Pos) : Tail → Set where
  pin-at : ∀ {u} → Pinned k (pin k u)
  pin-on : ∀ {j u} → Pinned k (later u) → Pinned k (pin j u)

-- `e`'s run steps at `k`, past its end running on `t`.
data InRun {A} (k : Pos) : Events A → Tail → Set where
  run-out  : ∀ {a r t} → InRun k (out k a r) t
  run-skip : ∀ {r t} → InRun k (skip k r) t
  run-end  : ∀ {t} → InRun k (end k) t
  run-tail : ∀ {h t} → Pinned k t → InRun k (end h) t
  out-run  : ∀ {h a r t} → InRun k (force r) (cut r) → InRun k (out h a r) t
  skip-run : ∀ {h r t} → InRun k (force r) (cut r) → InRun k (skip h r) t

shows-from : ∀ {A} {P : Pos → Set} (e : Events A) → (∀ k → Shown k e → P k) → Shows P e
shows (shows-from (out h _ r) f) = f h out-at , shows-from (force r) (λ k x → f k (out-on x))
shows (shows-from (skip h r)  f) = f h skip-at , shows-from (force r) (λ k x → f k (skip-on x))
shows (shows-from (end h)     f) = f h end-at
shows (shows-from hush        f) = tt

everyT-from : ∀ {P : Pos → Set} t → (∀ k → Pinned k t → P k) → EveryT P t
everyᵀ (everyT-from (pin j u) f) = f j pin-at , everyT-from (later u) (λ k x → f k (pin-on x))
everyᵀ (everyT-from idle      f) = tt

runs-from : ∀ {A} {P : Pos → Set} (e : Events A) t → (∀ k → InRun k e t → P k) → Runs P e t
runs (runs-from (out h _ r) t f) = f h run-out , runs-from (force r) (cut r) (λ k x → f k (out-run x))
runs (runs-from (skip h r)  t f) = f h run-skip , runs-from (force r) (cut r) (λ k x → f k (skip-run x))
runs (runs-from (end h)     t f) = f h run-end , everyT-from t (λ k x → f k (run-tail x))
runs (runs-from hush        t f) = tt

pinned-every : ∀ {P : Pos → Set} {k t} → Pinned k t → EveryT P t → P k
pinned-every pin-at     pt = proj₁ (everyᵀ pt)
pinned-every (pin-on x) pt = pinned-every x (proj₂ (everyᵀ pt))

-- Just past `q` lies only what `q` comes before, and inside it.
sub-lt : ∀ q k → Prefix (q ++ [ ix 0 ]) k → q <ᵖ k ≡ true
sub-lt q k pr with prefix-rest (q ++ [ ix 0 ]) k pr
... | ys , refl = subst (λ z → q <ᵖ z ≡ true) (sym (++-assoc q [ ix 0 ] ys)) (<ᵖ-below q ys)

sub-ext : ∀ q k → Prefix (q ++ [ ix 0 ]) k → Ext q k
sub-ext q k pr with prefix-rest (q ++ [ ix 0 ]) k pr
... | ys , refl = subst (Ext q) (sym (++-assoc q [ ix 0 ] ys)) (ext (ix 0) ys)

not-sub : ∀ q k → q <ᵖ k ≡ false → ¬ Prefix (q ++ [ ix 0 ]) k
not-sub q k nl pr with () ← trans (sym (sub-lt q k pr)) nl

-- Past `h`, at or past a step `n` outside it, lies nothing inside it.
ext-mid : ∀ h n m → h <ᵖ n ≡ true → m <ᵖ n ≡ false → ¬ Ext h n → ¬ Ext h m
ext-mid h n _ hn mn nx (ext l ls) with <ᵖ-split n (h ++ l ∷ ls) mn
... | inj₂ refl = nx (ext l ls)
... | inj₁ nm with <ᵖ-between h n (l ∷ ls) hn nm
...   | z ∷ zs , refl = nx (ext z zs)
...   | [] , eq with () ← trans (sym hn) (subst (λ x → h <ᵖ x ≡ false) (sym (trans eq (++-identityʳ h))) (<ᵖ-irrefl h))

-- What `e` shows first neither comes before `h` nor lies inside it.
Aloof : ∀ {A} → Pos → Events A → Set
Aloof h (out n _ _) = n <ᵖ h ≡ false × ¬ Ext h n
Aloof h (skip n _)  = n <ᵖ h ≡ false × ¬ Ext h n
Aloof h (end n)     = n <ᵖ h ≡ false × ¬ Ext h n
Aloof h hush        = ⊤

aloof-past : ∀ {A} n (e : Events A) → Atop n e → Past n e → Aloof n e
aloof-past n (out m _ _) a p = a , proj₂ p
aloof-past n (skip m _)  a p = a , proj₂ p
aloof-past n (end m)     a p = a , proj₂ p
aloof-past n hush        a p = tt

aloof-clear : ∀ {A} n (e : Events A) → Atop n e → Clear n e → Aloof n e
aloof-clear n (out m _ _) a c = a , proj₂ c
aloof-clear n (skip m _)  a c = a , c
aloof-clear n (end m)     a c = a , proj₂ c
aloof-clear n hush        a c = tt

onward-ok : ∀ h n m → n <ᵖ h ≡ false × ¬ Ext h n → m <ᵖ n ≡ false × ¬ Ext n m → m <ᵖ h ≡ false × ¬ Ext h m
onward-ok h n m (nh , hx) (mn , nx) with <ᵖ-split h n nh
... | inj₁ hn   = ≮-trans h n m nh mn , ext-mid h n m hn mn hx
... | inj₂ refl = ≮-trans h n m nh mn , nx

aloof-on : ∀ {A} h n (e : Events A) → n <ᵖ h ≡ false × ¬ Ext h n → Aloof n e → Aloof h e
aloof-on h n (out m _ _) hn a = onward-ok h n m hn a
aloof-on h n (skip m _)  hn a = onward-ok h n m hn a
aloof-on h n (end m)     hn a = onward-ok h n m hn a
aloof-on h n hush        hn a = tt

-- A run in order and steady, its first aloof from `h`, shows nothing
-- inside `h`.
shown-clear : ∀ {A} h (e : Events A) → Ordered e → Steady e → Aloof h e → ∀ k → Shown k e → ¬ Ext h k
shown-clear h (out n _ r) o s a k out-at      = proj₂ a
shown-clear h (skip n r)  o s a k skip-at     = proj₂ a
shown-clear h (end n)     o s a k end-at      = proj₂ a
shown-clear h (out n _ r) o s a k (out-on x)  =
  shown-clear h (force r) (proj₂ (ordered o)) (proj₂ (steady s))
    (aloof-on h n (force r) a (aloof-past n (force r) (proj₁ (ordered o)) (proj₁ (steady s)))) k x
shown-clear h (skip n r)  o s a k (skip-on x) =
  shown-clear h (force r) (proj₂ (ordered o)) (proj₂ (steady s))
    (aloof-on h n (force r) a (aloof-clear n (force r) (proj₁ (ordered o)) (proj₁ (steady s)))) k x
shown-clear h hush        o s a k ()

-- A run in order steps, past its end too, at nothing before what it is
-- atop.
run-atop : ∀ {A} h (e : Events A) t → Ordered e → Trail e t → Atop h e → ∀ q → InRun q e t → q <ᵖ h ≡ false
run-atop h (out n _ r) t o tr a q run-out      = a
run-atop h (skip n r)  t o tr a q run-skip     = a
run-atop h (end n)     t o tr a q run-end      = a
run-atop h (end n)     t o tr a q (run-tail x) = ≮-trans h n q a (<ᵖ-asym n q (proj₁ (pinned-every x (proj₁ (proj₂ (trail tr))))))
run-atop h (out n _ r) t o tr a q (out-run x)  =
  ≮-trans h n q a (run-atop n (force r) (cut r) (proj₂ (ordered o)) (proj₁ (proj₂ (proj₂ (trail tr)))) (proj₁ (ordered o)) q x)
run-atop h (skip n r)  t o tr a q (skip-run x) =
  ≮-trans h n q a (run-atop n (force r) (cut r) (proj₂ (ordered o)) (proj₂ (proj₂ (trail tr))) (proj₁ (ordered o)) q x)
run-atop h hush        t o tr a q ()

-- A RUN IN ORDER, STEADY AND TRAILED SHOWS NOTHING JUST PAST ITS OWN
-- STEPS: nothing it shows lies under the position just past any step of
-- its run, its run past an end included.  An earlier step sorts before
-- what lies past it; a later one leaves the earlier's subtree for good,
-- steady; and what runs on past the end lies past it.
unshown : ∀ {A} (e : Events A) t → Ordered e → Steady e → Trail e t → ∀ k q → Shown k e → InRun q e t → ¬ Prefix (q ++ [ ix 0 ]) k
unshown (out n _ r) t o s tr k q out-at      run-out      = not-sub n n (<ᵖ-irrefl n)
unshown (out n _ r) t o s tr k q out-at      (out-run x)  =
  not-sub q n (run-atop n (force r) (cut r) (proj₂ (ordered o)) (proj₁ (proj₂ (proj₂ (trail tr)))) (proj₁ (ordered o)) q x)
unshown (out n _ r) t o s tr k q (out-on y)  run-out      =
  λ pr → shown-clear n (force r) (proj₂ (ordered o)) (proj₂ (steady s))
           (aloof-past n (force r) (proj₁ (ordered o)) (proj₁ (steady s))) k y (sub-ext n k pr)
unshown (out n _ r) t o s tr k q (out-on y)  (out-run x)  =
  unshown (force r) (cut r) (proj₂ (ordered o)) (proj₂ (steady s)) (proj₁ (proj₂ (proj₂ (trail tr)))) k q y x
unshown (skip n r)  t o s tr k q skip-at     run-skip     = not-sub n n (<ᵖ-irrefl n)
unshown (skip n r)  t o s tr k q skip-at     (skip-run x) =
  not-sub q n (run-atop n (force r) (cut r) (proj₂ (ordered o)) (proj₂ (proj₂ (trail tr))) (proj₁ (ordered o)) q x)
unshown (skip n r)  t o s tr k q (skip-on y) run-skip     =
  λ pr → shown-clear n (force r) (proj₂ (ordered o)) (proj₂ (steady s))
           (aloof-clear n (force r) (proj₁ (ordered o)) (proj₁ (steady s))) k y (sub-ext n k pr)
unshown (skip n r)  t o s tr k q (skip-on y) (skip-run x) =
  unshown (force r) (cut r) (proj₂ (ordered o)) (proj₂ (steady s)) (proj₂ (proj₂ (trail tr))) k q y x
unshown (end n)     t o s tr k q end-at      run-end      = not-sub n n (<ᵖ-irrefl n)
unshown (end n)     t o s tr k q end-at      (run-tail x) =
  not-sub q n (<ᵖ-asym n q (proj₁ (pinned-every x (proj₁ (proj₂ (trail tr))))))
unshown hush        t o s tr k q ()          _

-- A CONNECT'S BODY LIES UNDER NONE OF ITS SOURCE'S STEPS, over sources
-- alien to it, its source in order, steady and trailed: nothing the body
-- shows or leaves running lies under where a step of its source's run
-- shows, past an end included.
under-shown-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Finite s → Finite b → ∀ p (ρ : NEnv Γ) → Alienᴱ p ρ
                    → Ordered (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ) → Steady (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ)
                    → Trailing (U.stateᴺ (U.subscribe s (p ++ [ ix 1 ])) ρ)
                    → Every∞ (λ k → Run (λ q → ¬ Prefix (q ++ [ ix 0 ]) k) (U.stateᴺ (U.subscribe s (p ++ [ ix 1 ])) ρ))
                             (U.stateᴺ (U.subscribe b (p ++ [ ix 0 ])) (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ ∷ᴬ ρ))
under-shown-connect s b fs fb p ρ cl os ss ts =
  every∞-mono (λ k fk → run-mono (λ q d x → proj₂ d (proj₁ d) x) Sᶜ (run-zip Sᶜ ks (proj₂ fk))) Bᶜ
    (Reach.reachˢ (underRules P₀ Sᶜ) b fb P₀ ρ′ (inj₁ (prefix-refl P₀) , run-mono start Sᶜ rS) (head , tail))
  where
    r  = p ++ [ ix 1 ]
    P₀ = p ++ [ ix 0 ]
    S  = U.meaning (U.subscribe s r) ρ
    Sᶜ = U.stateᴺ (U.subscribe s r) ρ
    ρ′ = S ∷ᴬ ρ
    Bᶜ = U.stateᴺ (U.subscribe b P₀) ρ′
    cr = alienᴱ-owned p r (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
    ks : Run (Disjoint P₀) Sᶜ
    ks = every-run Sᶜ (Reach.reachᶠ (apartRules P₀ (no-tick p)) s fs r ρ (sibling p (ix-mark _) (λ ()) , sibling p (ix-mark _) (λ ()))
                         (alienᴱ-owned p P₀ (inj₁ (prefix-++ p [ ix 0 ])) ρ cl))
    rS : Run (Beneath r) Sᶜ
    rS = every-run Sᶜ (Reach.reachᶠ (keyedRules r) s fs r ρ (inj₁ (prefix-refl r)) (every-monoᴱ (λ _ _ → tt) ρ cr))
    start : ∀ q → Beneath r q → Off P₀ P₀ q
    start q _ dq pr = proj₂ dq (owned-trans q (q ++ [ ix 0 ]) P₀ (inj₁ (prefix-++ q [ ix 0 ])) (inj₁ pr))
    past : ∀ q → Beneath r q → Owned p (q ++ [ ix 0 ])
    past q bq = beneath-owned p _ (owned-snoc p q (ix 0) (owned-trans p r q (inj₁ (prefix-++ p [ ix 1 ])) (beneath-owned r q bq)))
    head : Shows (λ k → Run (Off P₀ k) Sᶜ) S
    head = shows-from S (λ k sk → runs-from S (cut Sᶜ) (λ q iq _ → unshown S (cut Sᶜ) os ss ts k q sk iq))
    tail : Showsᴱ (λ h → Run (Off P₀ h) Sᶜ) ρ
    tail = everyᴱ-shows ρ (every-monoᴱ (λ h nh → run-mono (λ q bq _ pr → nh (owned-trans p (q ++ [ ix 0 ]) h (past q bq) (inj₁ pr))) Sᶜ rS) ρ cl)
