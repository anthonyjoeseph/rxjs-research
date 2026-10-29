{-# OPTIONS --guardedness #-}

-- THE EMISSION SET'S LAWS: the meaning of a node is its operator applied to its
-- children's meanings, so proofs over it go one operator at a time; and
-- `map` fuses.  Every former but `defer` means its operator by
-- definition; `defer` unfolds.
--
-- THE UNFOLDING is read through the order modulus (`Laws.Count`).  Each
-- approximant is within its index of the next (`settle`): a `defer`'s
-- guard is one more position before its body, so unfolding once more
-- moves only rows with more positions before them.  The meaning is
-- within every index of its approximant (`from`), and `defer` is contractive, so a `defer`'s meaning agrees with
-- its unfolded body at every bound, which is having the same rows.
--
-- Each operator keeps the modulus (`-ne`) only where its subscriptions are
-- ADMISSIBLE (`Laws.Worlds`): reachable positions whose world no hot row
-- lies in, under an environment whose handles keep the invariant.  A
-- `connect` reads its source's rows and its body's apart by their worlds.
--
-- The unfolding holds only there.  At a position headed by `last`, a timer
-- row `ix (τ + t) ∷ sub e ∷ []` sorts before the spin of an unreached
-- `defer`: with `l` a merge over `of [true, false]`, `true` to `defer l`
-- and `false` to a cold whose first frame is at 1, each depth's timer row
-- has an earlier one below it, so the limit truncates them all, while the
-- unfolded body shows the first.  A cold handle whose rows include
-- `[ix 0, sub p]` does the same at a reachable position.
module denotation.Laws where

open import Data.Bool using (Bool; T; true; false; not)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (_∷_; lookup)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (¬¬-excluded-middle)

open import Tree using (Obs; Later; FlatOp; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected;
  defer)
open import denotation.Events using (Timeline; Pos; ix; sub; last; inside)
open import denotation.EmissionSet
  using (Ev; out; skip; end; EmissionSet; _≺_; _≼_; Few; Truncate; Rejoin; shown; ended; late; guard;
  body; Den; hot; enter; DenEnv; approx; ⟦_⟧; MapT; map-out; map-skip; map-end; module Op)
import denotation.EmissionSet as ES
open import denotation.Laws.Modulus
  using (few-ind; entered-few; ≺-trans; ≺→≼; ≼-refl; ≼-trans; ≼-or-≻; ≺-≼-≺; ≼-≺-≺; ≺-ext; few-via;
  AgreeTo; ⟨_⟩; upto; AgreeTo-sym; trunc-to; ~-cold; Same; LimD; _~⟨_⟩_; ~-refl)
open import denotation.Laws.Count
  using (Cnt; AgC; trunc-ag; cnt-up; cnt-down; Img; em; seen; seen-under; _≈ᶜ⟨_∣_⟩_; ≈ᶜ-refl; ≈ᶜ-sym; ≈ᶜ-trans; ≈ᶜ-mono; agree-all; limit; Aft; contract; unfold₀)
open import denotation.Laws.Join using (over; flatMap-causal; flatMap-ne)
open import denotation.Laws.Worlds using (Ok; Lawful; InvAt; in-world; InvD; Hots; GoodEnv; world-after; ok-step; inv-widen; empty-inv;
  of-inv; spin-inv; map-inv; scan-inv; defer-inv; lim-inv)
open import denotation.Laws.Connect using (connect-inv)
open import denotation.Laws.TakeInv using (takeWhile-inv)
open import denotation.Laws.HotInv using (lawful-hot)
open import denotation.Laws.ColdInv using (cold-inv)
open import denotation.Laws.FlatInv using (flatMap-inv)
open import denotation.Laws.ConnectNe using (Causal; proper-ag; connect-ne)

-- The same rows at every subscription.
_≅_ : ∀ {A} → Den A → Den A → Set
d ≅ d′ = ∀ p {q e} → (enter d p q e → enter d′ p q e) × (enter d′ p q e → enter d p q e)

private
  ≅-refl : ∀ {A} (d : Den A) → d ≅ d
  ≅-refl d p = (λ x → x) , (λ x → x)

record Compositional : Set₁ where
  field
    coldᶜ      : ∀ {Γ A} (c : Timeline A) (ρ : DenEnv Γ) → ⟦ cold c ⟧ ρ ≅ Op.cold c
    emptyᶜ     : ∀ {Γ A} (ρ : DenEnv Γ) → ⟦ empty {Γ = Γ} {A = A} ⟧ ρ ≅ Op.empty
    ofᶜ        : ∀ {Γ A} (xs : List A) (ρ : DenEnv Γ) → ⟦ of {Γ = Γ} xs ⟧ ρ ≅ Op.of xs
    mapᶜ       : ∀ {Γ A B} (f : A → B) (s : Obs Timeline Γ A) (ρ : DenEnv Γ) → ⟦ map f s ⟧ ρ ≅ Op.map f (⟦ s ⟧ ρ)
    scanᶜ      : ∀ {Γ A B} (f : B → A → B) z (s : Obs Timeline Γ A) (ρ : DenEnv Γ) → ⟦ scan f z s ⟧ ρ ≅ Op.scan f z (⟦ s ⟧ ρ)
    takeWhileᶜ : ∀ {Γ A} (i : Bool) (k : A → Bool) (s : Obs Timeline Γ A) (ρ : DenEnv Γ) → ⟦ takeWhile i k s ⟧ ρ ≅ Op.takeWhile i k (⟦ s ⟧ ρ)
    flatMapᶜ   : ∀ {Γ A B} (op : FlatOp) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) (ρ : DenEnv Γ)
               → ⟦ flatMap op f s ⟧ ρ ≅ Op.flatMap op (λ a → ⟦ f a ⟧ ρ) (⟦ s ⟧ ρ)
    connectᶜ   : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) (ρ : DenEnv Γ)
               → ⟦ connect s b ⟧ ρ ≅ Op.connect (⟦ s ⟧ ρ) (λ h → ⟦ b ⟧ (h ∷ ρ))
    connectedᶜ : ∀ {Γ A} (i : A ∈ Γ) (ρ : DenEnv Γ) → ⟦ connected i ⟧ ρ ≅ lookup ρ i
    deferᶜ     : ∀ {Γ A} (l : Later Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ
               → Same (Ok (Hots ρ)) (⟦ defer l ⟧ ρ) (Op.defer (⟦ Later.force l ⟧ ρ))

------------------------------------------------------------------------
-- Causality

-- Every handle alike at and below `q`.
EnvAg : ∀ {Γ} → Pos → DenEnv Γ → DenEnv Γ → Set₁
EnvAg {Γ} q ρ ρ′ = ∀ {A} (i : A ∈ Γ) → lookup ρ i ~⟨ q ⟩ lookup ρ′ i

------------------------------------------------------------------------
-- Operators that read a row where it lies

-- MAP KEEPS EVERY ROW where it is.
private
  map-ag : ∀ {A B q} (f : A → B) {t t′ : EmissionSet A} → AgreeTo q t t′ → AgreeTo q (MapT f t) (MapT f t′)
  map-ag {A} f {t} {t′} a = ⟨ (λ {y} yq → go (λ {e} → proj₁ (upto a {y} {e} yq)) , go (λ {e} → proj₂ (upto a {y} {e} yq))) ⟩
    where
      go : ∀ {u u′ : EmissionSet A} {y} → (∀ {e} → u y e → u′ y e) → ∀ {e} → MapT f u y e → MapT f u′ y e
      go h (map-out x)  = map-out (h x)
      go h (map-skip x) = map-skip (h x)
      go h (map-end x)  = map-end (h x)

  map-up : ∀ {A B} (f : A → B) {t : EmissionSet A} {y e} → t y e → Σ (Ev B) (MapT f t y)
  map-up f {e = out a} x = _ , map-out x
  map-up f {e = skip}  x = _ , map-skip x
  map-up f {e = end}   x = _ , map-end x

map-ne : ∀ {A B R k} (f : A → B) {s s′ : Den A} → s ≈ᶜ⟨ R ∣ k ⟩ s′ → Op.map f s ≈ᶜ⟨ R ∣ k ⟩ Op.map f s′
map-ne f ag p r = trunc-ag λ
  { q (inj₁ c) → map-ag f (ag p r q (inj₁ (cnt-up c λ x yq → seen (proj₂ (map-up f x)) yq)))
  ; q (inj₂ c) → map-ag f (ag p r q (inj₂ (cnt-up c λ x yq → seen (proj₂ (map-up f x)) yq))) }

map-causal : ∀ {A B q} (f : A → B) {s s′ : Den A} → s ~⟨ q ⟩ s′ → Op.map f s ~⟨ q ⟩ Op.map f s′
map-causal f a = ~-cold λ p → map-ag f (a p)

-- SCAN AND TAKEWHILE read every value, but past the bound only to know
-- it lies past it.
private
  module SC {A B : Set} (f : B → A → B) (z : B) {Q : Pos} where
    open ES.Scan using (Acc; acc₀; acc; ScanT; sval; sstep; send)

    acc-to : ∀ {t t′ : EmissionSet A} → AgreeTo Q t t′ → ∀ {q b} → q ≼ Q → Acc f z t q b → Acc f z t′ q b
    acc-to a {q} qQ (acc₀ x mn) =
      acc₀ (proj₁ (upto a {q} qQ) x) (over a (λ k → q ≼ k) (λ {k} Qk → ≺→≼ {q} {k} (≼-≺-≺ {q} {Q} {k} qQ Qk)) mn)
    acc-to a {q′} q′Q (acc {q} ac x lt nx) =
      acc (acc-to a qQ ac) (proj₁ (upto a {q′} q′Q) x) lt
          (over a (λ k → q ≺ k → q′ ≼ k) (λ {k} Qk _ → ≺→≼ {q′} {k} (≼-≺-≺ {q′} {Q} {k} q′Q Qk)) nx)
      where qQ = ≺→≼ {q} {Q} (≺-≼-≺ {q} {q′} {Q} lt q′Q)

    scan-to : ∀ {t t′ : EmissionSet A} → AgreeTo Q t t′ → ∀ {y e} → y ≼ Q → ScanT f z t y e → ScanT f z t′ y e
    scan-to a {y} yQ (sval ac) = sval (acc-to a yQ ac)
    scan-to a {y} yQ (sstep x) = sstep (proj₁ (upto a {y} yQ) x)
    scan-to a {y} yQ (send x)  = send (proj₁ (upto a {y} yQ) x)

  module TW {A : Set} (incl : Bool) (keep : A → Bool) (p : Pos) {Q : Pos} where
    open ES.TakeWhile using (TakeT; Failed; pass; fail; stop; step; tend; left)

    fail-to : ∀ {t t′ : EmissionSet A} {q} → AgreeTo Q t t′ → q ≼ Q → Failed incl keep t p q → Failed incl keep t′ p q
    fail-to {q = q} a qQ (q′ , b , x , nk , lt) = q′ , b , proj₁ (upto a {q′} (≺→≼ {q′} {Q} (≺-≼-≺ {q′} {q} {Q} lt qQ))) x , nk , lt

    take-to : ∀ {t t′ : EmissionSet A} → AgreeTo Q t t′ → ∀ {y e} → y ≼ Q → TakeT incl keep t p y e → TakeT incl keep t′ p y e
    take-to a {y} yQ (pass x k nf)      = pass (proj₁ (upto a {y} yQ) x) k (λ g → nf (fail-to (AgreeTo-sym a) yQ g))
    take-to a     yQ (fail {q} x k nf i) = fail (proj₁ (upto a {q} qQ) x) k (λ g → nf (fail-to (AgreeTo-sym a) qQ g)) i
      where qQ = ≺→≼ {q} {Q} (≺-≼-≺ {q} {q ++ [ ix 0 ]} {Q} (≺-ext q []) yQ)
    take-to a     yQ (stop {q} x k nf)  = stop (proj₁ (upto a {q} qQ) x) k (λ g → nf (fail-to (AgreeTo-sym a) qQ g))
      where qQ = ≺→≼ {q} {Q} (≺-≼-≺ {q} {q ++ [ last ]} {Q} (≺-ext q []) yQ)
    take-to a {y} yQ (step x nf)        = step (proj₁ (upto a {y} yQ) x) (λ g → nf (fail-to (AgreeTo-sym a) yQ g))
    take-to a {y} yQ (tend x nf)        = tend (proj₁ (upto a {y} yQ) x) (λ g → nf (fail-to (AgreeTo-sym a) yQ g))
    take-to a {y} yQ (left x fd ins)    = left (proj₁ (upto a {y} yQ) x) (fail-to a yQ fd) ins

scan-causal : ∀ {A B q} (f : B → A → B) z {s s′ : Den A} → s ~⟨ q ⟩ s′ → Op.scan f z s ~⟨ q ⟩ Op.scan f z s′
scan-causal f z a = ~-cold λ p → ⟨ (λ yq → SC.scan-to f z (a p) yq , SC.scan-to f z (AgreeTo-sym (a p)) yq) ⟩

-- A SCAN BOUNDS ITS SOURCE: a value with few rows before it has a fold,
-- from the latest value among those rows, or from none.  Which of them
-- holds a value is not decidable, but the bound is, so it is read
-- classically.
private
  module SN {A B : Set} (f : B → A → B) (z : B) (t : EmissionSet A) where
    open ES.Scan f z t using (Acc; acc₀; acc; ScanT; sval; sstep; send)

    Val : Pos → Set
    Val k = Σ A λ a → t k (out a)

    -- The latest value before `w` among `ks`, or none there.
    Latest : Pos → List Pos → Set
    Latest w ks = (∀ {k} → k ∈ ks → Val k → k ≺ w → ⊥)
                ⊎ Σ Pos λ v → Val v × v ≺ w × (∀ {k} → k ∈ ks → Val k → k ≺ w → k ≼ v)

    latest : ∀ w ks → ¬ ¬ Latest w ks
    latest w []       ¬L = ¬L (inj₁ λ ())
    latest w (k ∷ ks) ¬L = latest w ks λ L → ¬¬-excluded-middle {A = Val k × k ≺ w} λ d → ¬L (add L d)
      where
        add : Latest w ks → Dec (Val k × k ≺ w) → Latest w (k ∷ ks)
        add (inj₁ none) (no ¬h) = inj₁ λ { {_} (here refl) vk kw → ¬h (vk , kw) ; {_} (there m) → none m }
        add (inj₂ (v , vv , vw , mx)) (no ¬h) =
          inj₂ (v , vv , vw , λ { {_} (here refl) vk kw → ⊥-elim (¬h (vk , kw)) ; {_} (there m) → mx m })
        add (inj₁ none) (yes (vk , kw)) =
          inj₂ (k , vk , kw , λ { {_} (here refl) _ _ → ≼-refl {k} ; {_} (there m) vk′ k′w → ⊥-elim (none m vk′ k′w) })
        add (inj₂ (v , vv , vw , mx)) (yes (vk , kw)) with ≼-or-≻ v k
        ... | inj₁ vk≼ = inj₂ (k , vk , kw , λ { {_} (here refl) _ _ → ≼-refl {k} ; {k′} (there m) vk′ k′w → ≼-trans {k′} {v} {k} (mx m vk′ k′w) vk≼ })
        ... | inj₂ kv  = inj₂ (v , vv , vw , λ { {_} (here refl) _ _ → ≺→≼ {k} {v} kv ; {_} (there m) → mx m })

    fold : ∀ {w} → Few t w → ∀ {a} → t w (out a) → ¬ ¬ Σ B (Acc w)
    fold = few-ind (λ w → ∀ {a} → t w (out a) → ¬ ¬ Σ B (Acc w)) step
      where
        step : ∀ {w} → Few t w → (∀ {v e} → t v e → v ≺ w → ∀ {a} → t v (out a) → ¬ ¬ Σ B (Acc v))
             → ∀ {a} → t w (out a) → ¬ ¬ Σ B (Acc w)
        step {w} (ks , h) ih {a} x ¬A = latest w ks λ
          { (inj₁ none) → ¬A (f z a , acc₀ x λ y kw → none (h y kw) (_ , y) kw)
          ; (inj₂ (v , (_ , xv) , vw , mx)) → ih xv vw xv λ
              { (b , av) → ¬A (f b a , acc av x vw λ y vk kw → mx (h y kw) (_ , y) kw vk) } }

scan-ne : ∀ {A B R k} (f : B → A → B) z {s s′ : Den A} → s ≈ᶜ⟨ R ∣ k ⟩ s′ → Op.scan f z s ≈ᶜ⟨ R ∣ k ⟩ Op.scan f z s′
scan-ne {k = k} f z {s} {s′} ag p r = trunc-ag go
  where
    -- A source row shows where it is, a value by its fold.
    img : ∀ (d : Den _) {q y e} → enter d p y e → y ≺ q → ¬ ¬ Img (ES.Scan.ScanT f z (enter d p)) q y
    img d {e = skip}  x yq = seen (ES.Scan.sstep x) yq
    img d {e = end}   x yq = seen (ES.Scan.send x) yq
    img d {e = out _} x yq ¬i = SN.fold f z (enter d p) (entered-few d p x) x λ { (_ , ac) → seen (ES.Scan.sval ac) yq ¬i }

    go : AgC k (ES.Scan.ScanT f z (enter s p)) (ES.Scan.ScanT f z (enter s′ p))
    go q (inj₁ c) = ⟨ (λ yq → SC.scan-to f z a yq , SC.scan-to f z (AgreeTo-sym a) yq) ⟩
      where a = ag p r q (inj₁ (cnt-up c (img s)))
    go q (inj₂ c) = ⟨ (λ yq → SC.scan-to f z a yq , SC.scan-to f z (AgreeTo-sym a) yq) ⟩
      where a = ag p r q (inj₂ (cnt-up c (img s′)))

takeWhile-causal : ∀ {A q} (i : Bool) (keep : A → Bool) {s s′ : Den A} → s ~⟨ q ⟩ s′ → Op.takeWhile i keep s ~⟨ q ⟩ Op.takeWhile i keep s′
takeWhile-causal i keep a = ~-cold λ p → ⟨ (λ yq → TW.take-to i keep p (a p) yq , TW.take-to i keep p (AgreeTo-sym (a p)) yq) ⟩

-- A TAKEWHILE BOUNDS ITS SOURCE before each of its rows' sources.  A
-- source row before the first failure is passed, or is the failure, shown
-- one label down; one past it lies before a row under the subscription,
-- so is under it, and is left as a skip.  Whether a row is past the
-- failure is not decidable, but the bound is.
private
  module TN {A : Set} (incl : Bool) (keep : A → Bool) (p : Pos) where
    open ES.TakeWhile incl keep using (TakeT; Failed; pass; fail; stop; step; tend; left)

    fd-trans : ∀ {X : EmissionSet A} {w z} → Failed X p w → w ≺ z → Failed X p z
    fd-trans {w = w} {z} (q , a , x , nk , lt) wz = q , a , x , nk , ≺-trans {q} {w} {z} lt wz

    -- A row's source is where `at` agrees.
    move : ∀ {X Y : EmissionSet A} {Q} → (∀ {z e} → X z e → z ≼ Q → (Failed X p z → T (inside p z)) → AgreeTo z X Y)
         → ∀ {y e} → y ≼ Q → TakeT X p y e → TakeT Y p y e
    move at {y} yQ (pass x k nf)       = TW.take-to incl keep p (at x yQ (⊥-elim ∘ nf)) (≼-refl {y}) (pass x k nf)
    move at {y} yQ (step x nf)         = TW.take-to incl keep p (at x yQ (⊥-elim ∘ nf)) (≼-refl {y}) (step x nf)
    move at {y} yQ (tend x nf)         = TW.take-to incl keep p (at x yQ (⊥-elim ∘ nf)) (≼-refl {y}) (tend x nf)
    move at {y} yQ (left x fd ins)     = TW.take-to incl keep p (at x yQ (λ _ → ins)) (≼-refl {y}) (left x fd ins)
    move {Q = Q} at yQ (fail {q} x k nf i) =
      fail (proj₁ (upto a {q} (≼-refl {q})) x) k (λ g → nf (TW.fail-to incl keep p (AgreeTo-sym a) (≼-refl {q}) g)) i
      where a = at x (≺→≼ {q} {Q} (≺-≼-≺ {q} {q ++ [ ix 0 ]} {Q} (≺-ext q []) yQ)) (⊥-elim ∘ nf)
    move {Q = Q} at yQ (stop {q} x k nf) =
      stop (proj₁ (upto a {q} (≼-refl {q})) x) k (λ g → nf (TW.fail-to incl keep p (AgreeTo-sym a) (≼-refl {q}) g))
      where a = at x (≺→≼ {q} {Q} (≺-≼-≺ {q} {q ++ [ last ]} {Q} (≺-ext q []) yQ)) (⊥-elim ∘ nf)

    module Core {H : Pos → Set} {k : ℕ} {s s′ : Den A} (Is : InvD H s) (Is′ : InvD H s′)
                (ag : s ≈ᶜ⟨ Ok H ∣ k ⟩ s′) (ok : Ok H p) {Q : Pos}
                (c : Cnt k (TakeT (enter s p) p) Q) where
      t t′ : EmissionSet A
      t  = enter s p
      t′ = enter s′ p
      I  = Is p ok
      I′ = Is′ p ok

      -- A source row before `z`, under the subscription if past the failure, shows before `z`.
      img : ∀ {z} → ∀ {w e} → t w e → w ≺ z → (Failed t p w → T (inside p w)) → ¬ ¬ Img (TakeT t p) z w
      img {z} {w} {e} x wz fw = em (λ f → seen (left x f (fw f)) wz) (pre e x)
        where
          pre : ∀ e → t w e → ¬ Failed t p w → ¬ ¬ Img (TakeT t p) z w
          pre skip    x nf = seen (step x nf) wz
          pre end     x nf = seen (tend x nf) wz
          pre (out a) x nf with keep a in eq
          ... | true  = seen (pass x (subst T (sym eq) tt) nf) wz
          ... | false = seen-under (stop x (subst (T ∘ not) (sym eq) tt) nf) wz

      bnd : ∀ {z e} → t z e → z ≼ Q → (Failed t p z → T (inside p z)) → Cnt k t z
      bnd xz zQ fz = cnt-up (cnt-down c zQ) λ {w} x wz → img x wz (λ f → in-world I x wz (fz (fd-trans {X = t} f wz)))

      bnd′ : ∀ {z e} → t′ z e → z ≼ Q → (Failed t′ p z → T (inside p z)) → Cnt k t′ z
      bnd′ x′ = few-ind P stp (entered-few s′ p x′) x′
        where
          P : Pos → Set
          P z = ∀ {e} → t′ z e → z ≼ Q → (Failed t′ p z → T (inside p z)) → Cnt k t′ z
          stp : ∀ {z} → Few t′ z → (∀ {v e} → t′ v e → v ≺ z → P v) → P z
          stp {z} _ ih xz zQ fz = cnt-up (cnt-down c zQ) λ {w} x′ wz →
            let fw′ = λ f → in-world I′ x′ wz (fz (fd-trans {X = t′} f wz))
                a   = ag p ok w (inj₂ (ih x′ wz x′ (≺→≼ {w} {Q} (≺-≼-≺ {w} {z} {Q} wz zQ)) fw′))
            in img (proj₂ (upto a {w} (≼-refl {w})) x′) wz (λ f → fw′ (TW.fail-to incl keep p {t = t} {t′} a (≼-refl {w}) f))

      agree : AgreeTo Q (TakeT t p) (TakeT t′ p)
      agree = ⟨ (λ yQ → move {Q = Q} (λ {z} x zQ fz → ag p ok z (inj₁ (bnd x zQ fz))) yQ
                      , move {Q = Q} (λ {z} x zQ fz → AgreeTo-sym (ag p ok z (inj₂ (bnd′ x zQ fz)))) yQ) ⟩

takeWhile-ne : ∀ {A H k} (i : Bool) (keep : A → Bool) {s s′ : Den A} → InvD H s → InvD H s′
             → s ≈ᶜ⟨ Ok H ∣ k ⟩ s′ → Op.takeWhile i keep s ≈ᶜ⟨ Ok H ∣ k ⟩ Op.takeWhile i keep s′
takeWhile-ne {H = H} {k} i keep {s} {s′} Is Is′ ag p ok = trunc-ag go
  where
    go : AgC k (ES.TakeWhile.TakeT i keep (enter s p) p) (ES.TakeWhile.TakeT i keep (enter s′ p) p)
    go q (inj₁ c) = TN.Core.agree i keep p {s = s} {s′} Is Is′ ag ok c
    go q (inj₂ c) = AgreeTo-sym (TN.Core.agree i keep p {s = s′} {s} Is′ Is (≈ᶜ-sym {R = Ok H} {k} {s} {s′} ag) ok c)

-- A CONNECT reads its body's end only up to the source step it shows.
private
  alive-to : ∀ {B Q k} {β β′ : EmissionSet B} → AgreeTo Q β β′ → k ≼ Q → (∀ {c} → β c end → k ≺ c) → ∀ {c} → β′ c end → k ≺ c
  alive-to {Q = Q} {k} a kQ al {c} x with ≼-or-≻ c Q
  ... | inj₁ cQ = al (proj₂ (upto a {c} cQ) x)
  ... | inj₂ Qc = ≼-≺-≺ {k} {Q} {c} kQ Qc

  conn-to : ∀ {A B Q} (s s′ : Den A) (F F′ : Den A → Den B) p
          → AgreeTo Q (enter s (p ++ [ ix 1 ])) (enter s′ (p ++ [ ix 1 ]))
          → AgreeTo Q (ES.Connect.β s F p) (ES.Connect.β s′ F′ p)
          → ∀ {y e} → y ≼ Q → ES.Connect.ConnT s F p y e → ES.Connect.ConnT s′ F′ p y e
  conn-to s s′ F F′ p aσ aβ {y} yQ (ES.Connecting.body x) = ES.Connecting.body (proj₁ (upto aβ {y} yQ) x)
  conn-to {Q = Q} s s′ F F′ p aσ aβ yQ (ES.Connecting.shown {k} x al) =
    ES.Connecting.shown (proj₁ (upto aσ {k} kQ) x) (alive-to aβ kQ al)
    where kQ = ≺→≼ {k} {Q} (≺-≼-≺ {k} {k ++ [ ix 0 ]} {Q} (≺-ext k []) yQ)
  conn-to s s′ F F′ p aσ aβ {y} yQ (ES.Connecting.pinned x nal ins) =
    ES.Connecting.pinned (proj₁ (upto aσ {y} yQ) x) (λ al → nal (alive-to (AgreeTo-sym aβ) yQ al)) ins

connect-causal : ∀ {A B q} {s s′ : Den A} {F F′ : Den A → Den B}
               → s ~⟨ q ⟩ s′ → (∀ {t t′} → AgreeTo q t t′ → F (hot t) ~⟨ q ⟩ F′ (hot t′)) → Op.connect s F ~⟨ q ⟩ Op.connect s′ F′
connect-causal {s = s} {s′} {F} {F′} as af = ~-cold λ p →
  ⟨ (λ {y} yq → conn-to s s′ F F′ p (as (p ++ [ ix 1 ])) (af (proper-ag (as (p ++ [ ix 1 ]))) (p ++ [ ix 0 ])) yq
              , conn-to s′ s F′ F p (AgreeTo-sym (as (p ++ [ ix 1 ]))) (AgreeTo-sym (af (proper-ag (as (p ++ [ ix 1 ]))) (p ++ [ ix 0 ]))) yq) ⟩

-- DEFER READS ITS BODY where it lies.
defer-causal : ∀ {A q} {s s′ : Den A} → s ~⟨ q ⟩ s′ → Op.defer s ~⟨ q ⟩ Op.defer s′
defer-causal a = ~-cold λ p →
  ⟨ (λ {y} yq → (λ { guard → guard ; (body x) → body (proj₁ (upto (a (p ++ [ ix 1 ])) {y} yq) x) })
              , (λ { guard → guard ; (body x) → body (proj₂ (upto (a (p ++ [ ix 1 ])) {y} yq) x) })) ⟩

lim-causal : ∀ {A q} {c c′ : ℕ → Den A} → (∀ n → c n ~⟨ q ⟩ c′ n) → LimD c ~⟨ q ⟩ LimD c′
lim-causal a = ~-cold λ p →
  ⟨ (λ {y} yq → (λ { (ES.from N l) → ES.from N λ n le → proj₁ (upto (a n p) {y} yq) (l n le) })
              , (λ { (ES.from N l) → ES.from N λ n le → proj₂ (upto (a n p) {y} yq) (l n le) })) ⟩

-- A JOINED HOT reads a row before the one it shows.
private
  rejoin-ag : ∀ {A q p} {t t′ : EmissionSet A} → AgreeTo q t t′ → ∀ {y e} → y ≼ q → Rejoin p t y e → Rejoin p t′ y e
  rejoin-ag {q = q} {p} a yq (shown {k} x w pk) = shown (proj₁ (upto a {k} (≺→≼ {k} {q} (≺-≼-≺ {k} {k ++ [ sub p ]} {q} (≺-ext k []) yq))) x) w pk
  rejoin-ag {q = q} {p} a yq (ended {c} x pc)   = ended (proj₁ (upto a {c} (≺→≼ {c} {q} (≺-≼-≺ {c} {c ++ [ sub p ]} {q} (≺-ext c []) yq))) x) pc
  rejoin-ag {q = q} {p} a yq (late {c} x cp)    =
    late (proj₁ (upto a {c} (≺→≼ {c} {q} (≺-≼-≺ {c} {p ++ [ last ]} {q} (≼-≺-≺ {c} {p} {p ++ [ last ]} cp (≺-ext p [])) yq))) x) cp

hot-causal : ∀ {A q} {t t′ : EmissionSet A} → AgreeTo q t t′ → hot t ~⟨ q ⟩ hot t′
hot-causal {q = q} a p = trunc-to ⟨ (λ {y} yq → rejoin-ag {q = q} {p} a yq , rejoin-ag {q = q} {p} (AgreeTo-sym a) yq) ⟩

------------------------------------------------------------------------
-- The environment

good-cons : ∀ {Γ A} {t : EmissionSet A} {ρ : DenEnv Γ} → Lawful t → GoodEnv ρ → GoodEnv (hot t ∷ ρ)
good-cons L g (here refl)          = lawful-hot L
good-cons {t = t} {ρ} L g (there i) = inv-widen {t = t} {d = lookup ρ i} (g i)

private
  ag-cons : ∀ {Γ A q} {d d′ : Den A} {ρ ρ′ : DenEnv Γ} → d ~⟨ q ⟩ d′ → EnvAg q ρ ρ′ → EnvAg q (d ∷ ρ) (d′ ∷ ρ′)
  ag-cons a e (here refl) = a
  ag-cons a e (there i)   = e i

------------------------------------------------------------------------
-- By structure

-- THE INVARIANT HOLDS of every approximant and of the meaning.
inv-approx : ∀ {Γ A} n (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → InvD (Hots ρ) (approx n o ρ)
inv-approx n       (cold c)          ρ g = cold-inv c
inv-approx n       empty             ρ g = empty-inv
inv-approx n       (of xs)           ρ g = of-inv xs
inv-approx n       (map f s)         ρ g = map-inv f {approx n s ρ} (inv-approx n s ρ g)
inv-approx n       (scan f z s)      ρ g = scan-inv f z {approx n s ρ} (inv-approx n s ρ g)
inv-approx n       (takeWhile i k s) ρ g = takeWhile-inv i k {approx n s ρ} (inv-approx n s ρ g)
inv-approx n       (flatMap op f s)  ρ g = flatMap-inv op (inv-approx n s ρ g) λ a → inv-approx n (f a) ρ g
inv-approx n       (connect s b)     ρ g = connect-inv {s = approx n s ρ} {F = λ h → approx n b (h ∷ ρ)} (inv-approx n s ρ g) λ {t} L → inv-approx n b (hot t ∷ ρ) (good-cons L g)
inv-approx n       (connected i)     ρ g = g i
inv-approx zero    (defer l)         ρ g = spin-inv
inv-approx (suc n) (defer l)         ρ g = defer-inv (inv-approx n (Later.force l) ρ g)

inv-⟦⟧ : ∀ {Γ A} (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → InvD (Hots ρ) (⟦ o ⟧ ρ)
inv-⟦⟧ (cold c)          ρ g = cold-inv c
inv-⟦⟧ empty             ρ g = empty-inv
inv-⟦⟧ (of xs)           ρ g = of-inv xs
inv-⟦⟧ (map f s)         ρ g = map-inv f {⟦ s ⟧ ρ} (inv-⟦⟧ s ρ g)
inv-⟦⟧ (scan f z s)      ρ g = scan-inv f z {⟦ s ⟧ ρ} (inv-⟦⟧ s ρ g)
inv-⟦⟧ (takeWhile i k s) ρ g = takeWhile-inv i k {⟦ s ⟧ ρ} (inv-⟦⟧ s ρ g)
inv-⟦⟧ (flatMap op f s)  ρ g = flatMap-inv op (inv-⟦⟧ s ρ g) λ a → inv-⟦⟧ (f a) ρ g
inv-⟦⟧ (connect s b)     ρ g = connect-inv {s = ⟦ s ⟧ ρ} {F = λ h → ⟦ b ⟧ (h ∷ ρ)} (inv-⟦⟧ s ρ g) λ {t} L → inv-⟦⟧ b (hot t ∷ ρ) (good-cons L g)
inv-⟦⟧ (connected i)     ρ g = g i
inv-⟦⟧ (defer l)         ρ g = lim-inv {c = λ n → approx n (defer l) ρ} λ n → inv-approx n (defer l) ρ g

-- EVERY APPROXIMANT AND THE MEANING ARE CAUSAL in the environment.
causal-approx : ∀ {Γ A q} n (o : Obs Timeline Γ A) {ρ ρ′ : DenEnv Γ} → EnvAg q ρ ρ′ → approx n o ρ ~⟨ q ⟩ approx n o ρ′
causal-approx n       (cold c)          e = ~-refl (Op.cold c)
causal-approx n       empty             e = ~-refl Op.empty
causal-approx n       (of xs)           e = ~-refl (Op.of xs)
causal-approx n       (map f s)         {ρ} {ρ′} e = map-causal f {approx n s ρ} {approx n s ρ′} (causal-approx n s e)
causal-approx n       (scan f z s)      {ρ} {ρ′} e = scan-causal f z {approx n s ρ} {approx n s ρ′} (causal-approx n s e)
causal-approx n       (takeWhile i k s) {ρ} {ρ′} e = takeWhile-causal i k {approx n s ρ} {approx n s ρ′} (causal-approx n s e)
causal-approx n       (flatMap op f s)  e = flatMap-causal op (causal-approx n s e) λ a → causal-approx n (f a) e
causal-approx n       (connect s b)     {ρ} {ρ′} e = connect-causal {s = approx n s ρ} {approx n s ρ′} {λ h → approx n b (h ∷ ρ)} {λ h → approx n b (h ∷ ρ′)} (causal-approx n s e) λ a → causal-approx n b (ag-cons (hot-causal a) e)
causal-approx n       (connected i)     e = e i
causal-approx zero    (defer l)         e = ~-refl Op.⊥
causal-approx (suc n) (defer l)         e = defer-causal (causal-approx n (Later.force l) e)

causal-⟦⟧ : ∀ {Γ A q} (o : Obs Timeline Γ A) {ρ ρ′ : DenEnv Γ} → EnvAg q ρ ρ′ → ⟦ o ⟧ ρ ~⟨ q ⟩ ⟦ o ⟧ ρ′
causal-⟦⟧ (cold c)          e = ~-refl (Op.cold c)
causal-⟦⟧ empty             e = ~-refl Op.empty
causal-⟦⟧ (of xs)           e = ~-refl (Op.of xs)
causal-⟦⟧ (map f s)         {ρ} {ρ′} e = map-causal f {⟦ s ⟧ ρ} {⟦ s ⟧ ρ′} (causal-⟦⟧ s e)
causal-⟦⟧ (scan f z s)      {ρ} {ρ′} e = scan-causal f z {⟦ s ⟧ ρ} {⟦ s ⟧ ρ′} (causal-⟦⟧ s e)
causal-⟦⟧ (takeWhile i k s) {ρ} {ρ′} e = takeWhile-causal i k {⟦ s ⟧ ρ} {⟦ s ⟧ ρ′} (causal-⟦⟧ s e)
causal-⟦⟧ (flatMap op f s)  e = flatMap-causal op (causal-⟦⟧ s e) λ a → causal-⟦⟧ (f a) e
causal-⟦⟧ (connect s b)     {ρ} {ρ′} e = connect-causal {s = ⟦ s ⟧ ρ} {⟦ s ⟧ ρ′} {λ h → ⟦ b ⟧ (h ∷ ρ)} {λ h → ⟦ b ⟧ (h ∷ ρ′)} (causal-⟦⟧ s e) λ a → causal-⟦⟧ b (ag-cons (hot-causal a) e)
causal-⟦⟧ (connected i)     e = e i
causal-⟦⟧ (defer l) {ρ} {ρ′} e = lim-causal {c = λ n → approx n (defer l) ρ} {c′ = λ n → approx n (defer l) ρ′} λ n → causal-approx n (defer l) e

private
  same-env : ∀ {Γ q} (ρ : DenEnv Γ) → EnvAg q ρ ρ
  same-env ρ i = ~-refl (lookup ρ i)

  causal-at : ∀ {Γ A B} n (b : Obs Timeline (A ∷ Γ) B) (ρ : DenEnv Γ) → Causal (λ h → approx n b (h ∷ ρ))
  causal-at n b ρ a = causal-approx n b (ag-cons (hot-causal a) (same-env ρ))

  causal-in : ∀ {Γ A B} (b : Obs Timeline (A ∷ Γ) B) (ρ : DenEnv Γ) → Causal (λ h → ⟦ b ⟧ (h ∷ ρ))
  causal-in b ρ a = causal-⟦⟧ b (ag-cons (hot-causal a) (same-env ρ))

------------------------------------------------------------------------
-- The approximants

-- A body's rows lie past its subscription.
aft : ∀ {A H} (d : Den A) → InvD H d → Aft (Ok H) d
aft d Id p ok {y} x = ≺→≼ {p ++ [ ix 1 ]} {y} (world-after (InvAt.world I x) (InvAt.real I x))
  where I = Id (p ++ [ ix 1 ]) (ok-step p ok)

-- THE RECURSION SETTLES: each approximant is within its index of the
-- next.  The first unfolding replaces the spin by the guard, the body
-- lying after it; each later one is the last, one level down.
settle : ∀ {Γ A} n (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → approx n o ρ ≈ᶜ⟨ Ok (Hots ρ) ∣ n ⟩ approx (suc n) o ρ
settle n       (cold c)          ρ g = ≈ᶜ-refl (Op.cold c)
settle n       empty             ρ g = ≈ᶜ-refl Op.empty
settle n       (of xs)           ρ g = ≈ᶜ-refl (Op.of xs)
settle n       (map f s)         ρ g = map-ne f {approx n s ρ} {approx (suc n) s ρ} (settle n s ρ g)
settle n       (scan f z s)      ρ g = scan-ne f z {approx n s ρ} {approx (suc n) s ρ} (settle n s ρ g)
settle n       (takeWhile i k s) ρ g = takeWhile-ne i k {approx n s ρ} {approx (suc n) s ρ} (inv-approx n s ρ g) (inv-approx (suc n) s ρ g) (settle n s ρ g)
settle n       (flatMap op f s)  ρ g =
  flatMap-ne op (inv-approx n s ρ g) (inv-approx (suc n) s ρ g) (λ a → inv-approx n (f a) ρ g) (λ a → inv-approx (suc n) (f a) ρ g)
    (settle n s ρ g) λ a → settle n (f a) ρ g
settle n       (connect s b)     ρ g =
  connect-ne {s = approx n s ρ} {approx (suc n) s ρ} {λ h → approx n b (h ∷ ρ)} {λ h → approx (suc n) b (h ∷ ρ)} (inv-approx n s ρ g) (inv-approx (suc n) s ρ g)
    (λ {t} L → inv-approx n b (hot t ∷ ρ) (good-cons L g)) (λ {t} L → inv-approx (suc n) b (hot t ∷ ρ) (good-cons L g))
    (causal-at n b ρ) (causal-at (suc n) b ρ)
    (settle n s ρ g) λ {t} L → settle n b (hot t ∷ ρ) (good-cons L g)
settle n       (connected i)     ρ g = ≈ᶜ-refl (lookup ρ i)
settle zero    (defer l)         ρ g = unfold₀ (aft (approx zero (Later.force l) ρ) (inv-approx zero (Later.force l) ρ g))
settle (suc n) (defer l)         ρ g =
  contract ok-step (aft (approx n (Later.force l) ρ) (inv-approx n (Later.force l) ρ g)) (aft (approx (suc n) (Later.force l) ρ) (inv-approx (suc n) (Later.force l) ρ g)) (settle n (Later.force l) ρ g)

-- THE MEANING IS WITHIN EVERY INDEX of its approximant: the limit of a
-- chain settling as above.
from : ∀ {Γ A} k (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → ⟦ o ⟧ ρ ≈ᶜ⟨ Ok (Hots ρ) ∣ k ⟩ approx k o ρ
from k (cold c)          ρ g = ≈ᶜ-refl (Op.cold c)
from k empty             ρ g = ≈ᶜ-refl Op.empty
from k (of xs)           ρ g = ≈ᶜ-refl (Op.of xs)
from k (map f s)         ρ g = map-ne f {⟦ s ⟧ ρ} {approx k s ρ} (from k s ρ g)
from k (scan f z s)      ρ g = scan-ne f z {⟦ s ⟧ ρ} {approx k s ρ} (from k s ρ g)
from k (takeWhile i p s) ρ g = takeWhile-ne i p {⟦ s ⟧ ρ} {approx k s ρ} (inv-⟦⟧ s ρ g) (inv-approx k s ρ g) (from k s ρ g)
from k (flatMap op f s)  ρ g =
  flatMap-ne op (inv-⟦⟧ s ρ g) (inv-approx k s ρ g) (λ a → inv-⟦⟧ (f a) ρ g) (λ a → inv-approx k (f a) ρ g)
    (from k s ρ g) λ a → from k (f a) ρ g
from k (connect s b)     ρ g =
  connect-ne {s = ⟦ s ⟧ ρ} {approx k s ρ} {λ h → ⟦ b ⟧ (h ∷ ρ)} {λ h → approx k b (h ∷ ρ)} (inv-⟦⟧ s ρ g) (inv-approx k s ρ g)
    (λ {t} L → inv-⟦⟧ b (hot t ∷ ρ) (good-cons L g)) (λ {t} L → inv-approx k b (hot t ∷ ρ) (good-cons L g))
    (causal-in b ρ) (causal-at k b ρ)
    (from k s ρ g) λ {t} L → from k b (hot t ∷ ρ) (good-cons L g)
from k (connected i)     ρ g = ≈ᶜ-refl (lookup ρ i)
from k (defer l)         ρ g =
  ≈ᶜ-sym {R = Ok (Hots ρ)} {k} {approx k (defer l) ρ} {⟦ defer l ⟧ ρ} (limit {c = λ n → approx n (defer l) ρ} (λ n → settle n (defer l) ρ g) k)

-- THE UNFOLDING: a `defer` agrees at every bound with its body unfolded
-- once, through the approximant one past the bound.
defer-lim : ∀ {Γ A} (l : Later Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ
          → Same (Ok (Hots ρ)) (⟦ defer l ⟧ ρ) (Op.defer (⟦ Later.force l ⟧ ρ))
defer-lim l ρ g = agree-all {R = Ok (Hots ρ)} {⟦ defer l ⟧ ρ} {Op.defer b} λ k →
  ≈ᶜ-mono {R = Ok (Hots ρ)} {k} {suc k} {⟦ defer l ⟧ ρ} {Op.defer b} (n≤1+n k)
    (≈ᶜ-trans {R = Ok (Hots ρ)} {suc k} {⟦ defer l ⟧ ρ} {Op.defer (approx k (Later.force l) ρ)} {Op.defer b}
      (from (suc k) (defer l) ρ g)
      (contract {R = Ok (Hots ρ)} {k} {approx k (Later.force l) ρ} {b} ok-step (aft (approx k (Later.force l) ρ) (inv-approx k (Later.force l) ρ g)) (aft b (inv-⟦⟧ (Later.force l) ρ g))
        (≈ᶜ-sym {R = Ok (Hots ρ)} {k} {b} {approx k (Later.force l) ρ} (from k (Later.force l) ρ g))))
  where b = ⟦ Later.force l ⟧ ρ

-- THE MEANING IS COMPOSITIONAL.
compositional : Compositional
compositional = record
  { coldᶜ      = λ c ρ → ≅-refl (Op.cold c)
  ; emptyᶜ     = λ ρ → ≅-refl Op.empty
  ; ofᶜ        = λ xs ρ → ≅-refl (Op.of xs)
  ; mapᶜ       = λ f s ρ → ≅-refl (Op.map f (⟦ s ⟧ ρ))
  ; scanᶜ      = λ f z s ρ → ≅-refl (Op.scan f z (⟦ s ⟧ ρ))
  ; takeWhileᶜ = λ i k s ρ → ≅-refl (Op.takeWhile i k (⟦ s ⟧ ρ))
  ; flatMapᶜ   = λ op f s ρ → ≅-refl (Op.flatMap op (λ a → ⟦ f a ⟧ ρ) (⟦ s ⟧ ρ))
  ; connectᶜ   = λ s b ρ → ≅-refl (Op.connect (⟦ s ⟧ ρ) (λ h → ⟦ b ⟧ (h ∷ ρ)))
  ; connectedᶜ = λ i ρ → ≅-refl (lookup ρ i)
  ; deferᶜ     = defer-lim
  }

-- MAP FUSES: `map (f ∘ g)` and `map f ∘ map g` have the same rows.
map-fusion : ∀ {Γ A B C} (f : B → C) (g : A → B) (s : Obs Timeline Γ A) (ρ : DenEnv Γ)
            → ⟦ map (f ∘ g) s ⟧ ρ ≅ ⟦ map f (map g s) ⟧ ρ
map-fusion f g s ρ p = fuse , split
  where
    down : ∀ {t k e} → MapT (f ∘ g) t k e → Σ (Ev _) (MapT g t k)
    down (map-out x)  = _ , map-out x
    down (map-skip x) = _ , map-skip x
    down (map-end x)  = _ , map-end x

    up : ∀ {t k e} → MapT g t k e → Σ (Ev _) (MapT (f ∘ g) t k)
    up (map-out x)  = _ , map-out x
    up (map-skip x) = _ , map-skip x
    up (map-end x)  = _ , map-end x

    across : ∀ {t k e} → MapT f (Truncate (MapT g t)) k e → Σ (Ev _) (MapT (f ∘ g) t k)
    across (map-out (map-out x , _))   = _ , map-out x
    across (map-skip (map-skip x , _)) = _ , map-skip x
    across (map-end (map-end x , _))   = _ , map-end x

    fuse : ∀ {t q e} → Truncate (MapT (f ∘ g) t) q e → Truncate (MapT f (Truncate (MapT g t))) q e
    fuse (map-out x , F)  = map-out (map-out x , few-via up F) , few-via across F
    fuse (map-skip x , F) = map-skip (map-skip x , few-via up F) , few-via across F
    fuse (map-end x , F)  = map-end (map-end x , few-via up F) , few-via across F

    split : ∀ {t q e} → Truncate (MapT f (Truncate (MapT g t))) q e → Truncate (MapT (f ∘ g) t) q e
    split (map-out (map-out x , G) , _)   = map-out x , few-via down G
    split (map-skip (map-skip x , G) , _) = map-skip x , few-via down G
    split (map-end (map-end x , G) , _)   = map-end x , few-via down G
