{-# OPTIONS --guardedness #-}

-- THE LISTING IS THE TABLE: an uncut listing (`quickcheck.Tabled`) holds
-- exactly the rows of the table approximant it mirrors, so every trace
-- the oracle compares against rxjs is read off the relation itself.
--
-- Exact, not merely sound: a listed end or skip decides a table predicate
-- that quantifies over the inputs' rows (`Merge.Done`, `Concat.Drained`,
-- `Connect.Alive`, `Proper`), so it is sound only if those inputs were
-- listed completely.  A cut listing claims nothing.
module quickcheck.Tabled.Exact where

open import Data.Bool using (Bool; true; false; T; not; _∧_; _∨_; if_then_else_)
open import Data.Bool.Properties using (T-≡)
open import Function.Bundles using (Equivalence)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; null) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; z<s; s≤s)
open import Data.Nat.Properties using (m≤n⇒m<n∨m≡n; m<n⇒m<1+n; <-trans; n<1+n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; Later; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
import denotation.MonotonicList.Events as E
open import denotation.MonotonicList.Events using (Pos; Timeline; _<ᵖ_; inside; ix)
open import denotation.Table
  using (Ev; out; skip; end; Table; _≺_; _≼_; InE; at-out; at-skip; at-end; on-out; on-skip; Proper; Rejoin; ended; late;
         Den; enter; MapT; map-out; map-skip; map-end; DeferT; guard; DenEnv; approxᵀ)
import denotation.Table as Tb
open import quickcheck.Tabled
  using (Row; Listed; _⊣_; rows; short; bind; concatMap; mapM; when; anyᵇ; allᵇ; isEnd; endBy; endBefore; ends; properᵇ; proper; values;
         fuel; horizon; walk; mapRow; mapRows; rejoinRow; rejoin; hotOf; outerRow; mergeRows; connRows; module MergeL; module ConcatL; module ConnL; listT)

------------------------------------------------------------------------
-- Exactness

record Exact {A : Set} (l : Listed A) (t : Table A) : Set where
  field
    sound    : ∀ {q e} → (q , e) ∈ rows l → t q e
    complete : ∀ {q e} → t q e → (q , e) ∈ rows l
open Exact public

Exactly : ∀ {A} → Listed A → Table A → Set
Exactly l t = short l ≡ false → Exact l t

------------------------------------------------------------------------
-- Booleans

private
  fromT : ∀ {b} → T b → b ≡ true
  fromT {true} _ = refl

  fromNot : ∀ {b} → ¬ T b → b ≡ false
  fromNot {true}  n = ⊥-elim (n tt)
  fromNot {false} _ = refl

  offT : ∀ {b} → b ≡ false → ¬ T b
  offT refl ()

  not-T : ∀ {b} → not b ≡ true → ¬ T b
  not-T {true}  ()
  not-T {false} _ ()

  T-not : ∀ {b} → ¬ T b → not b ≡ true
  T-not {true}  n = ⊥-elim (n tt)
  T-not {false} _ = refl

  ∨-false : ∀ {a b} → a ∨ b ≡ false → a ≡ false × b ≡ false
  ∨-false {true}  ()
  ∨-false {false} e = refl , e

  ∧-true : ∀ {a b} → a ∧ b ≡ true → a ≡ true × b ≡ true
  ∧-true {true}  e = refl , e
  ∧-true {false} ()

  ∧-intro : ∀ {a b} → a ≡ true → b ≡ true → a ∧ b ≡ true
  ∧-intro refl e = e

  or-right : ∀ {b c} → not b ∨ c ≡ true → b ≡ true → c ≡ true
  or-right e refl = e

  or-intro : ∀ {b c} → (b ≡ true → c ≡ true) → not b ∨ c ≡ true
  or-intro {true}  f = f refl
  or-intro {false} f = refl

  -- A test that would hold had its predicate held.
  off : ∀ {b} {P : Set} → (b ≡ true → P) → ¬ P → b ≡ false
  off {true}  f n = ⊥-elim (n (f refl))
  off {false} _ _ = refl

------------------------------------------------------------------------
-- Lists

  any⁻ : ∀ {X : Set} {p : X → Bool} {xs} → anyᵇ p xs ≡ true → Σ X λ x → x ∈ xs × p x ≡ true
  any⁻ {xs = []} ()
  any⁻ {p = p} {x ∷ xs} e with p x in px
  ... | true  = x , here refl , px
  ... | false = let (y , m , py) = any⁻ {p = p} {xs} e in y , there m , py

  any⁺ : ∀ {X : Set} {p : X → Bool} {xs x} → x ∈ xs → p x ≡ true → anyᵇ p xs ≡ true
  any⁺ {p = p} {y ∷ xs} (here refl) e rewrite e = refl
  any⁺ {p = p} {y ∷ xs} (there m) e with p y
  ... | true  = refl
  ... | false = any⁺ {p = p} m e

  any-off : ∀ {X : Set} {p : X → Bool} {xs x} → anyᵇ p xs ≡ false → x ∈ xs → p x ≡ false
  any-off {p = p} {x = x} e m with p x in px
  ... | true  = ⊥-elim (offT e (Equivalence.from T-≡ (any⁺ {p = p} m px)))
  ... | false = refl

  all⁻ : ∀ {X : Set} {p : X → Bool} {xs x} → allᵇ p xs ≡ true → x ∈ xs → p x ≡ true
  all⁻ {p = p} {y ∷ xs} e (here refl) = proj₁ (∧-true e)
  all⁻ {p = p} {y ∷ xs} e (there m)   = all⁻ {p = p} (proj₂ (∧-true {p y} e)) m

  all⁺ : ∀ {X : Set} {p : X → Bool} {xs} → (∀ {x} → x ∈ xs → p x ≡ true) → allᵇ p xs ≡ true
  all⁺ {xs = []}         f = refl
  all⁺ {p = p} {y ∷ xs} f = ∧-intro (f (here refl)) (all⁺ {p = p} (λ m → f (there m)))

  single⁻ : ∀ {X : Set} {x y : X} → y ∈ [ x ] → y ≡ x
  single⁻ (here e) = e
  single⁻ (there ())

  when⁻ : ∀ {X : Set} {b} {x y : X} → y ∈ when b x → b ≡ true × y ≡ x
  when⁻ {b = true}  m = refl , single⁻ m
  when⁻ {b = false} ()

  when⁺ : ∀ {X : Set} {b} {x : X} → b ≡ true → x ∈ when b x
  when⁺ refl = here refl

  if⁻ : ∀ {X : Set} {b} {xs ys : List X} {x} → x ∈ (if b then xs else ys) → (b ≡ true × x ∈ xs) ⊎ (b ≡ false × x ∈ ys)
  if⁻ {b = true}  m = inj₁ (refl , m)
  if⁻ {b = false} m = inj₂ (refl , m)

  if-t : ∀ {X : Set} {b} {xs ys : List X} {x} → b ≡ true → x ∈ xs → x ∈ (if b then xs else ys)
  if-t refl m = m

  if-f : ∀ {X : Set} {b} {xs ys : List X} {x} → b ≡ false → x ∈ ys → x ∈ (if b then xs else ys)
  if-f refl m = m

  cm⁻ : ∀ {X Y : Set} {f : X → List Y} {xs : List X} {y} → y ∈ concatMap f xs → Σ X λ x → x ∈ xs × y ∈ f x
  cm⁻ {xs = []} ()
  cm⁻ {f = f} {x ∷ xs} m with ∈-++⁻ (f x) m
  ... | inj₁ h = x , here refl , h
  ... | inj₂ h = let (z , zm , zh) = cm⁻ {f = f} {xs} h in z , there zm , zh

  cm⁺ : ∀ {X Y : Set} {f : X → List Y} {xs : List X} {x y} → x ∈ xs → y ∈ f x → y ∈ concatMap f xs
  cm⁺ {f = f} {x ∷ xs} (here refl) h = ∈-++⁺ˡ h
  cm⁺ {f = f} {x ∷ xs} (there m)   h = ∈-++⁺ʳ (f x) (cm⁺ {f = f} m h)

  bind⁻ : ∀ {X Y : Set} {m : Maybe X} {k : X → Maybe Y} {y} → bind m k ≡ just y → Σ X λ x → m ≡ just x × k x ≡ just y
  bind⁻ {m = just x} e = x , refl , e
  bind⁻ {m = nothing} ()

  mapM⁻ : ∀ {X Y : Set} {f : X → Maybe Y} {xs ys y} → mapM f xs ≡ just ys → y ∈ ys → Σ X λ x → x ∈ xs × f x ≡ just y
  mapM⁻ {xs = []} refl ()
  mapM⁻ {f = f} {x ∷ xs} e m with bind⁻ {m = f x} e
  ... | (y₀ , fx , e′) with bind⁻ {m = mapM f xs} e′
  ... | (ys₀ , rest , refl) with m
  ... | here refl = x , here refl , fx
  ... | there m′  = let (z , zm , fz) = mapM⁻ {f = f} rest m′ in z , there zm , fz

  mapM⁺ : ∀ {X Y : Set} {f : X → Maybe Y} {xs ys x} → mapM f xs ≡ just ys → x ∈ xs → Σ Y λ y → y ∈ ys × f x ≡ just y
  mapM⁺ {xs = []} _ ()
  mapM⁺ {f = f} {x ∷ xs} e m with bind⁻ {m = f x} e
  ... | (y₀ , fx , e′) with bind⁻ {m = mapM f xs} e′
  ... | (ys₀ , rest , refl) with m
  ... | here refl = y₀ , here refl , fx
  ... | there m′  = let (z , zm , fz) = mapM⁺ {f = f} rest m′ in z , there zm , fz

  null-gone : ∀ {X : Set} {xs : List X} → not (null xs) ≡ false → ∀ {x} → ¬ x ∈ xs
  null-gone {xs = []} _ ()
  null-gone {xs = _ ∷ _} ()

------------------------------------------------------------------------
-- Rows

  values⁻ : ∀ {A} {rs : List (Row A)} {q a} → (q , a) ∈ values rs → (q , out a) ∈ rs
  values⁻ {rs = (k , out b) ∷ rs} (here refl) = here refl
  values⁻ {rs = (k , out b) ∷ rs} (there m)   = there (values⁻ m)
  values⁻ {rs = (k , skip) ∷ rs}  m           = there (values⁻ m)
  values⁻ {rs = (k , end) ∷ rs}   m           = there (values⁻ m)

  values⁺ : ∀ {A} {rs : List (Row A)} {q a} → (q , out a) ∈ rs → (q , a) ∈ values rs
  values⁺ {rs = (k , out b) ∷ rs} (here refl) = here refl
  values⁺ {rs = (k , out b) ∷ rs} (there m)   = there (values⁺ m)
  values⁺ {rs = (k , skip) ∷ rs}  (here ())
  values⁺ {rs = (k , skip) ∷ rs}  (there m)   = values⁺ m
  values⁺ {rs = (k , end) ∷ rs}   (here ())
  values⁺ {rs = (k , end) ∷ rs}   (there m)   = values⁺ m

  end-at : ∀ {X : Set} {rs : List (Row X)} {c} k (e : Ev X) → (k , e) ∈ rs → c ∈ when (isEnd e) k → (c , end) ∈ rs
  end-at k end     rm (here refl) = rm
  end-at k end     rm (there ())
  end-at k (out _) rm ()
  end-at k skip    rm ()

  ends⁻ : ∀ {X : Set} {rs : List (Row X)} {c} → c ∈ ends rs → (c , end) ∈ rs
  ends⁻ {rs = rs} m with cm⁻ {xs = rs} m
  ... | ((k , e) , rm , h) = end-at k e rm h

  ends⁺ : ∀ {X : Set} {rs : List (Row X)} {c} → (c , end) ∈ rs → c ∈ ends rs
  ends⁺ {rs = rs} m = cm⁺ {xs = rs} m (here refl)

  endBy→ : ∀ {X : Set} {u : Table X} {l : Listed X} → Exact l u → ∀ {c} → endBy (rows l) c ≡ true → Σ Pos λ k → u k end × k ≼ c
  endBy→ {l = l} ex e with any⁻ {xs = rows l} e
  ... | ((k , end) , m , h)   = k , sound ex m , not-T h
  ... | ((k , out _) , m , ())
  ... | ((k , skip) , m , ())

  →endBy : ∀ {X : Set} {u : Table X} {l : Listed X} → Exact l u → ∀ {k c} → u k end → k ≼ c → endBy (rows l) c ≡ true
  →endBy ex x kc = any⁺ (complete ex x) (T-not kc)

  endBefore→ : ∀ {X : Set} {u : Table X} {l : Listed X} → Exact l u → ∀ {c} → endBefore (rows l) c ≡ true → Σ Pos λ k → u k end × k ≺ c
  endBefore→ {l = l} ex e with any⁻ {xs = rows l} e
  ... | ((k , end) , m , h)   = k , sound ex m , Equivalence.from T-≡ h
  ... | ((k , out _) , m , ())
  ... | ((k , skip) , m , ())

  →endBefore : ∀ {X : Set} {u : Table X} {l : Listed X} → Exact l u → ∀ {k c} → u k end → k ≺ c → endBefore (rows l) c ≡ true
  →endBefore ex x kc = any⁺ (complete ex x) (fromT kc)

------------------------------------------------------------------------
-- Leaves

walk-exact : ∀ {A} n (ev : E.Events A) → Exactly (walk n ev) (InE ev)
walk-exact zero ev ()
walk-exact (suc n) (E.out k a r) u with E.tick k Data.Nat.≤ᵇ horizon
... | true = let ih = walk-exact n (E.Events∞.force r) u in record
  { sound    = λ { (here refl) → at-out ; (there m) → on-out (sound ih m) }
  ; complete = λ { at-out → here refl ; (on-out x) → there (complete ih x) } }
... | false = ⊥-elim (offT u (Equivalence.from T-≡ refl))
walk-exact (suc n) (E.skip k r) u with E.tick k Data.Nat.≤ᵇ horizon
... | true = let ih = walk-exact n (E.Events∞.force r) u in record
  { sound    = λ { (here refl) → at-skip ; (there m) → on-skip (sound ih m) }
  ; complete = λ { at-skip → here refl ; (on-skip x) → there (complete ih x) } }
... | false = ⊥-elim (offT u (Equivalence.from T-≡ refl))
walk-exact (suc n) (E.end k) u with E.tick k Data.Nat.≤ᵇ horizon
... | true  = record { sound = λ { (here refl) → at-end ; (there ()) } ; complete = λ { at-end → here refl } }
... | false = ⊥-elim (offT u (Equivalence.from T-≡ refl))
walk-exact (suc n) E.hush u = record { sound = λ () ; complete = λ () }

end-exact : ∀ {A} (k : Pos) → Exactly {A} ([ k , end ] ⊣ false) (InE (E.end k))
end-exact k _ = record { sound = λ { (here refl) → at-end ; (there ()) } ; complete = λ { at-end → here refl } }

------------------------------------------------------------------------
-- One input

map-exact : ∀ {A B} (f : A → B) {l : Listed A} {t : Table A} → Exactly l t → Exactly (mapRows f l) (MapT f t)
map-exact f {l} {t} el u = record { sound = s ; complete = c }
  where
    ex = el u
    s : ∀ {q e} → (q , e) ∈ mapL (mapRow f) (rows l) → MapT f t q e
    s m with ∈-map⁻ (mapRow f) m
    ... | ((q , out a) , m′ , refl) = map-out (sound ex m′)
    ... | ((q , skip)  , m′ , refl) = map-skip (sound ex m′)
    ... | ((q , end)   , m′ , refl) = map-end (sound ex m′)
    c : ∀ {q e} → MapT f t q e → (q , e) ∈ mapL (mapRow f) (rows l)
    c (map-out x)  = ∈-map⁺ (mapRow f) (complete ex x)
    c (map-skip x) = ∈-map⁺ (mapRow f) (complete ex x)
    c (map-end x)  = ∈-map⁺ (mapRow f) (complete ex x)

defer-exact : ∀ {A} {s : Den A} {p} {b : Listed A} → Exactly b (enter s (p ++ [ ix 1 ]))
  → Exactly (((p ++ [ ix 0 ] , skip) ∷ rows b) ⊣ short b) (DeferT s p)
defer-exact eb u = record
  { sound    = λ { (here refl) → guard ; (there m) → Tb.body (sound (eb u) m) }
  ; complete = λ { guard → here refl ; (Tb.body x) → there (complete (eb u) x) } }

-- `Table.Proper`, the rows a hot shows.
proper-exact : ∀ {A} {l : Listed A} {t : Table A} → Exactly l t → Exactly (hotOf l) (Proper t)
proper-exact {A} {l} {t} el u = record { sound = s ; complete = c }
  where
    ex = el u
    pb→ : ∀ {q} → properᵇ (rows l) q ≡ true → ∀ {k} → t k end → q ≼ k
    pb→ e x = not-T (all⁻ e (complete ex x))
    →pb : ∀ {q} → (∀ {k} → t k end → q ≼ k) → properᵇ (rows l) q ≡ true
    →pb h = all⁺ {xs = rows l} λ { {k , out _} m → refl ; {k , skip} m → refl ; {k , end} m → T-not (h (sound ex m)) }
    s : ∀ {q e} → (q , e) ∈ proper (rows l) → Proper t q e
    s m with cm⁻ {xs = rows l} m
    ... | ((k , e′) , m′ , h) with when⁻ h
    ... | (pb , refl) = sound ex m′ , pb→ pb
    c : ∀ {q e} → Proper t q e → (q , e) ∈ proper (rows l)
    c (x , h) = cm⁺ (complete ex x) (when⁺ (→pb h))

-- `Table.Rejoin`, joining a hot at `p`.
private
  rj-row : ∀ {A} {t : Table A} p {k e q e′} → t k e → (q , e′) ∈ rejoinRow p (k , e) → Rejoin p t q e′
  rj-row p {k} {end} x h with if⁻ {b = p <ᵖ k} h
  ... | inj₁ (pk , m) with single⁻ m
  ... | refl = ended x (Equivalence.from T-≡ pk)
  rj-row p {k} {end} x h | inj₂ (pk , m) with single⁻ m
  ... | refl = late x (offT pk)
  rj-row p {k} {out a} x h with when⁻ h
  ... | (pk , refl) = Tb.shown x tt (Equivalence.from T-≡ pk)
  rj-row p {k} {skip} x h with when⁻ h
  ... | (pk , refl) = Tb.shown x tt (Equivalence.from T-≡ pk)

  rj-in : ∀ {A} {t : Table A} p {q e} → Rejoin p t q e → Σ (Row A) λ r → t (proj₁ r) (proj₂ r) × (q , e) ∈ rejoinRow p r
  rj-in p (Tb.shown {k} {out a} x _ pk) = (k , out a) , x , when⁺ (fromT pk)
  rj-in p (Tb.shown {k} {skip} x _ pk)  = (k , skip) , x , when⁺ (fromT pk)
  rj-in p (Tb.shown {k} {end} x () pk)
  rj-in p (ended {c} x pc) = (c , end) , x , if-t (fromT pc) (here refl)
  rj-in p (late {c} x cp)  = (c , end) , x , if-f (fromNot cp) (here refl)

rejoin-exact : ∀ {A} {l : Listed A} {t : Table A} → Exactly l t → ∀ p → Exactly (rejoin p l) (Rejoin p t)
rejoin-exact {l = l} {t} el p u = record { sound = s ; complete = c }
  where
    ex = el u
    s : ∀ {q e} → (q , e) ∈ concatMap (rejoinRow p) (rows l) → Rejoin p t q e
    s m with cm⁻ {xs = rows l} m
    ... | (r , rm , h) = rj-row p (sound ex rm) h
    c : ∀ {q e} → Rejoin p t q e → (q , e) ∈ concatMap (rejoinRow p) (rows l)
    c x with rj-in p x
    ... | ((k , e) , y , h) = cm⁺ (complete ex y) h

------------------------------------------------------------------------
-- Merge

module MergeX {A B : Set} (fD : A → Den B) (t : Table A) (o : Listed A) (ls : List (Pos × A × Listed B))
  (u : short (mergeRows o ls) ≡ false)
  (eo : Exactly o t)
  (ls-from : ∀ {q a l} → (q , a , l) ∈ ls → (q , a) ∈ values (rows o) × Exactly l (enter (fD a) (q ++ [ ix 1 ])))
  (ls-to : ∀ {q a} → (q , a) ∈ values (rows o) → Σ (Listed B) λ l → (q , a , l) ∈ ls)
  where
  open Tb.Merge fD t
  open MergeL o ls using (done; laneRow)

  private
    exo : Exact o t
    exo = eo (proj₁ (∨-false {short o} u))

    uncut : ∀ {q a l} → (q , a , l) ∈ ls → short l ≡ false
    uncut m = any-off {xs = ls} (proj₂ (∨-false {short o} u)) m

    exl : ∀ {q a l} → (q , a , l) ∈ ls → Exact l (enter (fD a) (q ++ [ ix 1 ]))
    exl m = proj₂ (ls-from m) (uncut m)

    out-of : ∀ {q a l} → (q , a , l) ∈ ls → t q (out a)
    out-of m = sound exo (values⁻ (proj₁ (ls-from m)))

    done→ : ∀ c → done c ≡ true → Done c
    done→ c e = endBy→ exo {c} (proj₁ (∧-true {endBy (rows o) c} e)) , λ x →
      let (l , m) = ls-to (values⁺ (complete exo x))
      in endBy→ (exl m) {c} (all⁻ {xs = ls} (proj₂ (∧-true {endBy (rows o) c} e)) m)

    →done : ∀ c → Done c → done c ≡ true
    →done c ((c₀ , x , le) , lanes) = ∧-intro (→endBy exo {c₀} {c} x le) (all⁺ {xs = ls} λ { {q , a , l} m →
      let (c′ , y , le′) = lanes (out-of m) in →endBy (exl m) {c′} {c} y le′ })

    end-row : ∀ {c} → t c end → MergeT c (if done c then end else skip)
    end-row {c} x with done c in dc
    ... | true  = oend x (done→ c dc)
    ... | false = opass x (λ D → offT dc (Equivalence.from T-≡ (→done c D)))

    lend-row : ∀ {q a c} → t q (out a) → Lane q a c end → MergeT c (if done c then end else skip)
    lend-row {c = c} x y with done c in dc
    ... | true  = lend x y (done→ c dc)
    ... | false = lpass x y (λ D → offT dc (Equivalence.from T-≡ (→done c D)))

    outer-s : ∀ {r q e} → r ∈ rows o → (q , e) ∈ outerRow done r → MergeT q e
    outer-s {k , out a} rm h with single⁻ h
    ... | refl = val (sound exo rm)
    outer-s {k , skip} rm h with single⁻ h
    ... | refl = step (sound exo rm)
    outer-s {c , end} rm h with single⁻ h
    ... | refl = end-row (sound exo rm)

    lane-s : ∀ {q₀ a l r q e} → (q₀ , a , l) ∈ ls → r ∈ rows l → (q , e) ≡ laneRow r → MergeT q e
    lane-s {r = k , out b} m rm refl = lane (out-of m) (sound (exl m) rm) tt
    lane-s {r = k , skip}  m rm refl = lane (out-of m) (sound (exl m) rm) tt
    lane-s {r = c , end}   m rm refl = lend-row (out-of m) (sound (exl m) rm)

    outer-end : ∀ {c b} → done c ≡ b → (c , (if b then end else skip)) ∈ outerRow {A} {B} done (c , end)
    outer-end refl = here refl

    lane-end : ∀ {c b} {rs : List (Row B)} → done c ≡ b → (c , end) ∈ rs → (c , (if b then end else skip)) ∈ mapL laneRow rs
    lane-end refl r = ∈-map⁺ laneRow r

    lane-in : ∀ {k e} {rs : List (Row B)} → Tb.Work e → (k , e) ∈ rs → (k , e) ∈ mapL laneRow rs
    lane-in {e = out b} _ r = ∈-map⁺ laneRow r
    lane-in {e = skip}  _ r = ∈-map⁺ laneRow r
    lane-in {e = end}   () r

  sound-m : ∀ {q e} → (q , e) ∈ rows (mergeRows o ls) → MergeT q e
  sound-m m with ∈-++⁻ (concatMap (outerRow done) (rows o)) m
  ... | inj₁ h = let (r , rm , h′) = cm⁻ {xs = rows o} h in outer-s rm h′
  ... | inj₂ h with cm⁻ {xs = ls} h
  ... | ((q₀ , a , l) , lm , h′) with ∈-map⁻ laneRow h′
  ... | (r , rm , eq) = lane-s lm rm eq

  complete-m : ∀ {q e} → MergeT q e → (q , e) ∈ rows (mergeRows o ls)
  complete-m (val x)      = ∈-++⁺ˡ (cm⁺ (complete exo x) (here refl))
  complete-m (step x)     = ∈-++⁺ˡ (cm⁺ (complete exo x) (here refl))
  complete-m (oend {c} x D)   = ∈-++⁺ˡ (cm⁺ (complete exo x) (outer-end {c} (→done c D)))
  complete-m (opass {c} x nD) = ∈-++⁺ˡ (cm⁺ (complete exo x) (outer-end {c} (off (done→ c) nD)))
  complete-m (lane x y w) =
    let (l , m) = ls-to (values⁺ (complete exo x)) in
    ∈-++⁺ʳ (concatMap (outerRow done) (rows o)) (cm⁺ m (lane-in w (complete (exl m) y)))
  complete-m (lend {c = c} x y D) =
    let (l , m) = ls-to (values⁺ (complete exo x)) in
    ∈-++⁺ʳ (concatMap (outerRow done) (rows o)) (cm⁺ m (lane-end {c} (→done c D) (complete (exl m) y)))
  complete-m (lpass {c = c} x y nD) =
    let (l , m) = ls-to (values⁺ (complete exo x)) in
    ∈-++⁺ʳ (concatMap (outerRow done) (rows o)) (cm⁺ m (lane-end {c} (off (done→ c) nD) (complete (exl m) y)))

merge-exact : ∀ {A B} (fD : A → Den B) {t : Table A} (o : Listed A) (ls : List (Pos × A × Listed B)) → Exactly o t
  → (∀ {q a l} → (q , a , l) ∈ ls → (q , a) ∈ values (rows o) × Exactly l (enter (fD a) (q ++ [ ix 1 ])))
  → (∀ {q a} → (q , a) ∈ values (rows o) → Σ (Listed B) λ l → (q , a , l) ∈ ls)
  → Exactly (mergeRows o ls) (Tb.Merge.MergeT fD t)
merge-exact fD {t} o ls eo from to u = record { sound = sound-m ; complete = complete-m }
  where open MergeX fD t o ls u eo from to

------------------------------------------------------------------------
-- Concat

module ConcatX {A B : Set} (fD : A → Den B) (t : Table A) (ln : A → Pos → Maybe (Listed B)) (o : Listed A)
  (exo : Exact o t)
  (el : ∀ {a s l} → ln a s ≡ just l → Exactly l (enter (fD a) s))
  where
  open Tb.Concat fD t
  open ConcatL ln o

  private
    K : ℕ
    K = count vals

    val-out : ∀ {q a} → (q , a) ∈ vals → t q (out a)
    val-out m = sound exo (values⁻ m)

    out-val : ∀ {q a} → t q (out a) → (q , a) ∈ vals
    out-val x = values⁺ (complete exo x)

  -- The i-th values.
  nth-sound : ∀ i {q a} → (q , a) ∈ nthL i → Nth i q a
  nth-sound zero m with cm⁻ {xs = vals} m
  ... | ((q , a) , vm , h) with when⁻ h
  ... | (b , refl) = first (val-out vm) (λ x → not-T (all⁻ b (out-val x)))
  nth-sound (suc i) m with cm⁻ {xs = nthL i} m
  ... | ((q₀ , a₀) , m₀ , h) with cm⁻ {xs = vals} h
  ... | ((q , a) , vm , h′) with when⁻ h′
  ... | (b , refl) = next (nth-sound i m₀) (val-out vm) (Equivalence.from T-≡ (proj₁ (∧-true b)))
                       (λ x qk → not-T (or-right (all⁻ (proj₂ (∧-true b)) (out-val x)) (fromT qk)))

  nth-complete : ∀ {i q a} → Nth i q a → (q , a) ∈ nthL i
  nth-complete (first x all) = cm⁺ {xs = vals} (out-val x) (when⁺ (all⁺ {xs = vals} λ { {k , b} m → T-not (all (val-out m)) }))
  nth-complete {suc i} (next {q = q₀} N x lt all) =
    cm⁺ {xs = nthL i} (nth-complete N) (cm⁺ {f = after q₀} {xs = vals} (out-val x) (when⁺ (∧-intro (fromT lt)
      (all⁺ {xs = vals} λ { {k , b} m → or-intro (λ qk → T-not (all (val-out m) (Equivalence.from T-≡ qk))) }))))

  sub-nth : ∀ {i q s a} → Sub i q s a → Nth i q a
  sub-nth (sub₀ N)         = N
  sub-nth (free _ _ N _)   = N
  sub-nth (queued _ _ N _) = N

  waiting-iff : ∀ lv i c → (waiting lv i c ≡ true → Waiting i c) × (Waiting i c → waiting lv i c ≡ true)
  waiting-iff lv i c = to , fro
    where
      to : waiting lv i c ≡ true → Waiting i c
      to e with any⁻ {xs = nthL (suc i)} e
      ... | ((q , a) , m , h) = q , a , nth-sound (suc i) m , Equivalence.from T-≡ h
      fro : Waiting i c → waiting lv i c ≡ true
      fro (q , a , N , qc) = any⁺ {xs = nthL (suc i)} (nth-complete N) (fromT qc)

  -- Every level past the values is empty.
  private
    Gone : ℕ → Set
    Gone i = ∀ {x} → ¬ x ∈ nthL i

    gone-step : ∀ i → Gone i → Gone (suc i)
    gone-step i g m = let (y , ym , _) = cm⁻ {xs = nthL i} m in g ym

    levels-or-gone : Gone (suc K) → ∀ j → j < suc K ⊎ Gone j
    levels-or-gone g zero = inj₁ z<s
    levels-or-gone g (suc j) with levels-or-gone g j
    ... | inj₂ gj = inj₂ (gone-step j gj)
    ... | inj₁ (s≤s le) with m≤n⇒m<n∨m≡n le
    ...   | inj₁ lt   = inj₁ (s≤s lt)
    ...   | inj₂ refl = inj₂ g

    upto⁺ : ∀ {i n} → i < n → i ∈ upto n
    upto⁺ {i} {suc n} (s≤s le) with m≤n⇒m<n∨m≡n le
    ... | inj₁ lt   = ∈-++⁺ˡ (upto⁺ lt)
    ... | inj₂ refl = ∈-++⁺ʳ (upto i) (here refl)

    upto⁻ : ∀ {i n} → i ∈ upto n → i < n
    upto⁻ {i} {suc n} m with ∈-++⁻ (upto n) m
    ... | inj₁ m′        = m<n⇒m<1+n (upto⁻ m′)
    ... | inj₂ (here refl) = n<1+n n
    ... | inj₂ (there ())

    down : ∀ {i n} → suc i < n → i < n
    down lt = <-trans (n<1+n _) lt

  group⁻ : ∀ {ss q a g} → group ss (q , a) ≡ just g
    → Σ (List (Pos × Listed B)) λ ls → g ≡ (q , a , ls)
        × (∀ {s l} → (s , l) ∈ ls → s ∈ ss × ln a s ≡ just l)
        × (∀ {s} → s ∈ ss → Σ (Listed B) λ l → (s , l) ∈ ls)
  group⁻ {ss} {q} {a} e with bind⁻ {m = mapM (λ s → bind (ln a s) λ l → just (s , l)) ss} e
  ... | (ls , els , refl) = ls , refl , fr , to
    where
      fr : ∀ {s l} → (s , l) ∈ ls → s ∈ ss × ln a s ≡ just l
      fr m with mapM⁻ {xs = ss} els m
      ... | (s′ , sm , fs) with bind⁻ {m = ln a s′} fs
      ... | (l′ , e′ , refl) = sm , e′
      to : ∀ {s} → s ∈ ss → Σ (Listed B) λ l → (s , l) ∈ ls
      to {s′} sm with mapM⁺ {xs = ss} els sm
      ... | ((s″ , l′) , m , fs) with bind⁻ {m = ln a s′} fs
      ... | (l″ , e′ , refl) = l″ , m

  -- A level, listed: each of the i-th values with its lanes.
  record Level (i : ℕ) (gs : List Group) : Set where
    field
      from  : ∀ {q a ls} → (q , a , ls) ∈ gs → (q , a) ∈ nthL i × (∀ {s l} → (s , l) ∈ ls → Sub i q s a × ln a s ≡ just l)
      to    : ∀ {q a} → (q , a) ∈ nthL i → Σ (List (Pos × Listed B)) λ ls → (q , a , ls) ∈ gs
      cover : ∀ {q a ls s} → (q , a , ls) ∈ gs → Sub i q s a → Σ (Listed B) λ l → (s , l) ∈ ls

  module _ (lv : List (ℕ × List Group))
    (lv-ok : mapM (λ i → bind (levelL i) λ gs → just (i , gs)) (upto (suc K)) ≡ just lv)
    (u : short (concatRows lv) ≡ false)
    where

    private
      uncut-lv : ∀ {j l} → (j , l) ∈ lanesOf lv → short l ≡ false
      uncut-lv m = any-off {xs = lanesOf lv} (proj₂ (∨-false {not (null (nthL (suc K)))} (proj₂ (∨-false {short o} u)))) m

      gone-K : Gone (suc K)
      gone-K = null-gone (proj₁ (∨-false {not (null (nthL (suc K)))} (proj₂ (∨-false {short o} u))))

      in-range : ∀ {j q a} → Nth j q a → j < suc K
      in-range {j} N with levels-or-gone gone-K j
      ... | inj₁ lt = lt
      ... | inj₂ g  = ⊥-elim (g (nth-complete N))

      lv-at : ∀ {j gs} → j < suc K → levelL j ≡ just gs → (j , gs) ∈ lv
      lv-at {j} lt e with mapM⁺ {xs = upto (suc K)} lv-ok (upto⁺ lt)
      ... | (y , ym , fy) with bind⁻ {m = levelL j} fy
      ... | (gs′ , e′ , refl) with trans (sym e) e′
      ... | refl = ym

      lv-from : ∀ {j gs} → (j , gs) ∈ lv → j < suc K × levelL j ≡ just gs
      lv-from m with mapM⁻ {xs = upto (suc K)} lv-ok m
      ... | (j′ , jm , fy) with bind⁻ {m = levelL j′} fy
      ... | (gs′ , e′ , refl) = upto⁻ jm , e′

      uncut-at : ∀ {j gs q a ls s l} → j < suc K → levelL j ≡ just gs → (q , a , ls) ∈ gs → (s , l) ∈ ls → short l ≡ false
      uncut-at lt e gm lm = uncut-lv (cm⁺ (lv-at lt e) (cm⁺ gm (∈-map⁺ _ lm)))

    level : ∀ i {gs} → i < suc K → levelL i ≡ just gs → Level i gs

    private
      from₀ : ∀ {gs} → levelL zero ≡ just gs → ∀ {q a ls} → (q , a , ls) ∈ gs
        → (q , a) ∈ nthL zero × (∀ {s l} → (s , l) ∈ ls → Sub zero q s a × ln a s ≡ just l)
      from₀ e m with mapM⁻ {xs = nthL zero} e m
      ... | ((q′ , a′) , xm , fx) with group⁻ {ss = [ q′ ++ [ ix 1 ] ]} fx
      ... | (ls′ , refl , fr , _) = xm , λ m′ →
        let (sm , le) = fr m′ in subst (λ s → Sub zero q′ s a′) (sym (single⁻ sm)) (sub₀ (nth-sound zero xm)) , le

      to₀ : ∀ {gs} → levelL zero ≡ just gs → ∀ {q a} → (q , a) ∈ nthL zero → Σ (List (Pos × Listed B)) λ ls → (q , a , ls) ∈ gs
      to₀ e {q} m with mapM⁺ {xs = nthL zero} e m
      ... | (g , gm , fx) with group⁻ {ss = [ q ++ [ ix 1 ] ]} fx
      ... | (ls , refl , _) = ls , gm

      cover₀ : ∀ {gs} → levelL zero ≡ just gs → ∀ {q a ls s} → (q , a , ls) ∈ gs → Sub zero q s a → Σ (Listed B) λ l → (s , l) ∈ ls
      cover₀ e m (sub₀ N) with mapM⁻ {xs = nthL zero} e m
      ... | ((q′ , a′) , xm , fx) with group⁻ {ss = [ q′ ++ [ ix 1 ] ]} fx
      ... | (ls′ , refl , _ , to′) = to′ (here refl)

      -- Where a lane i+1 may start is where one does.
      start-sub : ∀ i {gs₀ q a s} → i < suc K → levelL i ≡ just gs₀ → (q , a) ∈ nthL (suc i) → s ∈ starts gs₀ q → Sub (suc i) q s a
      start-sub i {gs₀} {q} {a} {s} lt e₀ xm sm with cm⁻ {xs = gs₀} sm
      ... | ((q₀ , a₀ , ls₀) , gm , h) with cm⁻ {xs = ls₀} h
      ... | ((s₀ , l₀) , lm , h′) with cm⁻ {xs = ends (rows l₀)} h′
      ... | (c , cm , h″) with Level.from (level i lt e₀) gm
      ... | (_ , subs) with subs lm
      ... | (S , le) with ∈-++⁻ (when (c <ᵖ q) (q ++ [ ix 1 ])) h″
      ... | inj₁ w = let (cq , eq) = when⁻ w in
        subst (λ s → Sub (suc i) q s a) (sym eq) (free S (sound (el le (uncut-at lt e₀ gm lm)) (ends⁻ cm)) (nth-sound (suc i) xm) (Equivalence.from T-≡ cq))
      ... | inj₂ w = let (qc , eq) = when⁻ w in
        subst (λ s → Sub (suc i) q s a) (sym eq) (queued S (sound (el le (uncut-at lt e₀ gm lm)) (ends⁻ cm)) (nth-sound (suc i) xm) (Equivalence.from T-≡ qc))

      -- Where a lane i+1 starts is where one may.
      sub-start : ∀ i {gs₀ q s a} → i < suc K → levelL i ≡ just gs₀ → Sub (suc i) q s a → s ∈ starts gs₀ q
      sub-start i lt e₀ (free {c = c} S lk N cq) =
        let L = level i lt e₀
            (ls₀ , gm) = Level.to L (nth-complete (sub-nth S))
            (l₀ , lm) = Level.cover L gm S
            (_ , le) = proj₂ (Level.from L gm) lm
        in cm⁺ gm (cm⁺ lm (cm⁺ (ends⁺ (complete (el le (uncut-at lt e₀ gm lm)) lk)) (∈-++⁺ˡ (when⁺ (fromT cq)))))
      sub-start i {q = q} lt e₀ (queued {c = c} S lk N qc) =
        let L = level i lt e₀
            (ls₀ , gm) = Level.to L (nth-complete (sub-nth S))
            (l₀ , lm) = Level.cover L gm S
            (_ , le) = proj₂ (Level.from L gm) lm
        in cm⁺ gm (cm⁺ lm (cm⁺ (ends⁺ (complete (el le (uncut-at lt e₀ gm lm)) lk))
             (∈-++⁺ʳ (when (c <ᵖ q) (q ++ [ ix 1 ])) (when⁺ (fromT qc)))))

      fromₛ : ∀ i {gs} → suc i < suc K → levelL (suc i) ≡ just gs → ∀ {q a ls} → (q , a , ls) ∈ gs
        → (q , a) ∈ nthL (suc i) × (∀ {s l} → (s , l) ∈ ls → Sub (suc i) q s a × ln a s ≡ just l)
      fromₛ i lt e m with bind⁻ {m = levelL i} e
      ... | (gs₀ , e₀ , e₁) with mapM⁻ {xs = nthL (suc i)} e₁ m
      ... | ((q′ , a′) , xm , fx) with group⁻ {ss = starts gs₀ q′} fx
      ... | (ls′ , refl , fr , _) = xm , λ m′ → let (sm , le) = fr m′ in start-sub i (down lt) e₀ xm sm , le

      toₛ : ∀ i {gs} → levelL (suc i) ≡ just gs → ∀ {q a} → (q , a) ∈ nthL (suc i) → Σ (List (Pos × Listed B)) λ ls → (q , a , ls) ∈ gs
      toₛ i e {q} m with bind⁻ {m = levelL i} e
      ... | (gs₀ , e₀ , e₁) with mapM⁺ {xs = nthL (suc i)} e₁ m
      ... | (g , gm , fx) with group⁻ {ss = starts gs₀ q} fx
      ... | (ls , refl , _) = ls , gm

      coverₛ : ∀ i {gs} → suc i < suc K → levelL (suc i) ≡ just gs → ∀ {q a ls s} → (q , a , ls) ∈ gs → Sub (suc i) q s a
        → Σ (Listed B) λ l → (s , l) ∈ ls
      coverₛ i lt e m S with bind⁻ {m = levelL i} e
      ... | (gs₀ , e₀ , e₁) with mapM⁻ {xs = nthL (suc i)} e₁ m
      ... | ((q′ , a′) , xm , fx) with group⁻ {ss = starts gs₀ q′} fx
      ... | (ls′ , refl , _ , to′) = to′ (sub-start i (down lt) e₀ S)

    level zero    lt e = record { from = from₀ e ; to = to₀ e ; cover = cover₀ e }
    level (suc i) lt e = record { from = fromₛ i lt e ; to = toₛ i e ; cover = coverₛ i lt e }

    private
      -- A listed lane is a lane of the table.
      lane-of : ∀ {j l} → (j , l) ∈ lanesOf lv → Σ Pos λ q → Σ Pos λ s → Σ A λ a → Sub j q s a × ln a s ≡ just l
      lane-of m with cm⁻ {xs = lv} m
      ... | ((j′ , gs) , jm , h) with cm⁻ {xs = gs} h
      ... | ((q , a , ls) , gm , h′) with ∈-map⁻ _ h′
      ... | ((s , l′) , sm , refl) with lv-from jm
      ... | (lt , e) = let (S , le) = proj₂ (Level.from (level j′ lt e) gm) sm in q , s , a , S , le

      -- A lane of the table is listed.
      of-lane : ∀ {j q s a} → Sub j q s a → Σ (Listed B) λ l → (j , l) ∈ lanesOf lv × ln a s ≡ just l
      of-lane {j} S with in-range (sub-nth S)
      ... | lt with mapM⁺ {xs = upto (suc K)} lv-ok (upto⁺ lt)
      ... | (y , ym , fy) with bind⁻ {m = levelL j} fy
      ... | (gs , e , refl) =
        let L = level j lt e
            (ls , gm) = Level.to L (nth-complete (sub-nth S))
            (l , lm) = Level.cover L gm S
            (_ , le) = proj₂ (Level.from L gm) lm
        in l , cm⁺ ym (cm⁺ gm (∈-map⁺ _ lm)) , le

      exl : ∀ {j l} → (j , l) ∈ lanesOf lv → ∀ {a s} → ln a s ≡ just l → Exact l (enter (fD a) s)
      exl m le = el le (uncut-lv m)

      over→ : ∀ c → over lv c ≡ true → Over c
      over→ c e = endBefore→ exo {c} e

      →over : ∀ c → Over c → over lv c ≡ true
      →over c (c₀ , x , lt) = →endBefore exo {c₀} {c} x lt

      drained→ : ∀ c → drained lv c ≡ true → Drained c
      drained→ c e {i} N with in-range N
      ... | lt with mapM⁺ {xs = upto (suc K)} lv-ok (upto⁺ lt)
      ... | (y , ym , fy) with bind⁻ {m = levelL i} fy
      ... | (gs , eg , refl) =
        let L = level i lt eg
            (ls , gm) = Level.to L (nth-complete N)
            ((s , l) , lm , h) = any⁻ {xs = ls} (all⁻ (all⁻ e ym) gm)
            (S , le) = proj₂ (Level.from L gm) lm
            (c′ , lk , lt′) = endBefore→ (el le (uncut-at lt eg gm lm)) {c} h
        in s , c′ , S , lk , lt′

      →drained : ∀ c → Drained c → drained lv c ≡ true
      →drained c D = all⁺ {xs = lv} λ { {i , gs} ym → all⁺ {xs = gs} λ { {q , a , ls} gm →
        let (lt , eg) = lv-from ym
            L = level i lt eg
            (s , c′ , S , lk , lt′) = D (nth-sound i (proj₁ (Level.from L gm)))
            (l , lm) = Level.cover L gm S
            (_ , le) = proj₂ (Level.from L gm) lm
        in any⁺ lm (→endBefore (el le (uncut-at lt eg gm lm)) {c′} {c} lk lt′) } }

      end-row : ∀ {c} → t c end → ConcatT c (if drained lv c then end else skip)
      end-row {c} x with drained lv c in dc
      ... | true  = oend x (drained→ c dc)
      ... | false = opass x (λ D → offT dc (Equivalence.from T-≡ (→drained c D)))

      lend-row : ∀ {i q₀ s a c q e} → Sub i q₀ s a → enter (fD a) s c end → (q , e) ≡ laneRow lv i (c , end) → ConcatT q e
      lend-row {i} {c = c} S lk eq with waiting lv i c in w | over lv c in ov | eq
      ... | true  | _     | refl = handoff S lk (proj₁ (waiting-iff lv i c) w)
      ... | false | true  | refl = lend S lk (λ W → offT w (Equivalence.from T-≡ (proj₂ (waiting-iff lv i c) W))) (over→ c ov)
      ... | false | false | refl = lpass S lk (λ W → offT w (Equivalence.from T-≡ (proj₂ (waiting-iff lv i c) W))) (λ O → offT ov (Equivalence.from T-≡ (→over c O)))

      outer-s : ∀ {r q e} → r ∈ rows o → (q , e) ∈ outerRow (drained lv) r → ConcatT q e
      outer-s {k , out a} rm h with single⁻ h
      ... | refl = val (sound exo rm)
      outer-s {k , skip} rm h with single⁻ h
      ... | refl = step (sound exo rm)
      outer-s {c , end} rm h with single⁻ h
      ... | refl = end-row (sound exo rm)

      lane-s : ∀ {j l r q e} → (j , l) ∈ lanesOf lv → r ∈ rows l → (q , e) ≡ laneRow lv j r → ConcatT q e
      lane-s {r = k , out b} m rm refl = let (_ , _ , _ , S , le) = lane-of m in lane S (sound (exl m le) rm) tt
      lane-s {r = k , skip}  m rm refl = let (_ , _ , _ , S , le) = lane-of m in lane S (sound (exl m le) rm) tt
      lane-s {r = c , end}   m rm eq   = let (_ , _ , _ , S , le) = lane-of m in lend-row S (sound (exl m le) rm) eq

      outer-end : ∀ {c b} → drained lv c ≡ b → (c , (if b then end else skip)) ∈ outerRow {A} {B} (drained lv) (c , end)
      outer-end refl = here refl

      lane-end : ∀ {i c bw bo} {rs : List (Row B)} → waiting lv i c ≡ bw → over lv c ≡ bo → (c , end) ∈ rs
        → (if bw then (c ++ [ ix 0 ] , skip) else (c , (if bo then end else skip))) ∈ mapL (laneRow lv i) rs
      lane-end {i} refl refl r = ∈-map⁺ (laneRow lv i) r

      lane-in : ∀ {i k e} {rs : List (Row B)} → Tb.Work e → (k , e) ∈ rs → (k , e) ∈ mapL (laneRow lv i) rs
      lane-in {i} {e = out b} _ r = ∈-map⁺ (laneRow lv i) r
      lane-in {i} {e = skip}  _ r = ∈-map⁺ (laneRow lv i) r
      lane-in {e = end} () r

      outers : List (Row B)
      outers = concatMap (outerRow (drained lv)) (rows o)

    sound-c : ∀ {q e} → (q , e) ∈ rows (concatRows lv) → ConcatT q e
    sound-c m with ∈-++⁻ outers m
    ... | inj₁ h = let (r , rm , h′) = cm⁻ {xs = rows o} h in outer-s rm h′
    ... | inj₂ h with cm⁻ {xs = lanesOf lv} h
    ... | ((j , l) , lm , h′) with ∈-map⁻ (laneRow lv j) h′
    ... | (r , rm , eq) = lane-s lm rm eq

    complete-c : ∀ {q e} → ConcatT q e → (q , e) ∈ rows (concatRows lv)
    complete-c (val x)       = ∈-++⁺ˡ (cm⁺ (complete exo x) (here refl))
    complete-c (step x)      = ∈-++⁺ˡ (cm⁺ (complete exo x) (here refl))
    complete-c (oend {c} x D)    = ∈-++⁺ˡ (cm⁺ (complete exo x) (outer-end {c} (→drained c D)))
    complete-c (opass {c} x nD)  = ∈-++⁺ˡ (cm⁺ (complete exo x) (outer-end {c} (off (drained→ c) nD)))
    complete-c (lane S lk w) =
      let (l , m , le) = of-lane S in ∈-++⁺ʳ outers (cm⁺ m (lane-in w (complete (exl m le) lk)))
    complete-c (handoff {i} {c = c} S lk W) =
      let (l , m , le) = of-lane S in
      ∈-++⁺ʳ outers (cm⁺ m (lane-end {i} {c} (proj₂ (waiting-iff lv i c) W) refl (complete (exl m le) lk)))
    complete-c (lend {i} {c = c} S lk nW O) =
      let (l , m , le) = of-lane S in
      ∈-++⁺ʳ outers (cm⁺ m (lane-end {i} {c} (off (proj₁ (waiting-iff lv i c)) nW) (→over c O) (complete (exl m le) lk)))
    complete-c (lpass {i} {c = c} S lk nW nO) =
      let (l , m , le) = of-lane S in
      ∈-++⁺ʳ outers (cm⁺ m (lane-end {i} {c} (off (proj₁ (waiting-iff lv i c)) nW) (off (over→ c) nO) (complete (exl m le) lk)))

concat-exact : ∀ {A B} (fD : A → Den B) (t : Table A) (ln : A → Pos → Maybe (Listed B)) (o : Listed A)
  → Exactly o t → (∀ {a s l} → ln a s ≡ just l → Exactly l (enter (fD a) s))
  → ∀ {l} → ConcatL.listC ln o ≡ just l → Exactly l (Tb.Concat.ConcatT fD t)
concat-exact fD t ln o eo el e u
  with bind⁻ {m = mapM (λ i → bind (ConcatL.levelL ln o i) λ gs → just (i , gs)) (ConcatL.upto ln o (suc (ConcatL.count ln o (ConcatL.vals ln o))))} e
... | (lv , lv-ok , refl) = record { sound = sound-c lv lv-ok u ; complete = complete-c lv lv-ok u }
  where open ConcatX fD t ln o (eo (proj₁ (∨-false {short o} u))) el

------------------------------------------------------------------------
-- Connect

module ConnX {A B : Set} (sD : Den A) (F : Den A → Den B) (p : Pos) (σl : Listed A) (βl : Listed B)
  (eσ : Exact σl (Tb.Connect.σ sD F p)) (eβ : Exact βl (Tb.Connect.β sD F p))
  where
  open Tb.Connect sD F p using (Alive; ConnT; body; shown; pinned)
  open ConnL (p ++ [ ix 1 ]) σl βl using (alive) renaming (shown to shownL)

  private
    alive→ : ∀ q → alive q ≡ true → Alive q
    alive→ q e x = Equivalence.from T-≡ (all⁻ e (complete eβ x))

    →alive : ∀ q → Alive q → alive q ≡ true
    →alive q h = all⁺ {xs = rows βl} λ { {c , end} m → fromT (h (sound eβ m)) ; {c , out _} m → refl ; {c , skip} m → refl }

    pinned-row : ∀ {k e₀ q e} → Tb.Connect.σ sD F p k e₀ → ¬ Alive (k ++ [ ix 0 ]) → (q , e) ∈ when (inside (p ++ [ ix 1 ]) k) (k , skip) → ConnT q e
    pinned-row x na h with when⁻ h
    ... | (ins , refl) = pinned x na (Equivalence.from T-≡ ins)

    shown-row : ∀ {k e₀ q e} → Tb.Connect.σ sD F p k e₀ → (q , e) ∈ shownL (k , e₀) → ConnT q e
    shown-row {k} x h with if⁻ {b = alive (k ++ [ ix 0 ])} h
    ... | inj₁ (al , m) with single⁻ m
    ... | refl = shown x (alive→ (k ++ [ ix 0 ]) al)
    shown-row {k} x h | inj₂ (al , h′) = pinned-row x (λ A → offT al (Equivalence.from T-≡ (→alive (k ++ [ ix 0 ]) A))) h′

  sound-k : ∀ {q e} → (q , e) ∈ rows (connRows (p ++ [ ix 1 ]) σl βl) → ConnT q e
  sound-k m with ∈-++⁻ (rows βl) m
  ... | inj₁ h = body (sound eβ h)
  ... | inj₂ h = let ((k , e₀) , km , h′) = cm⁻ {xs = rows σl} h in shown-row (sound eσ km) h′

  complete-k : ∀ {q e} → ConnT q e → (q , e) ∈ rows (connRows (p ++ [ ix 1 ]) σl βl)
  complete-k (body x)         = ∈-++⁺ˡ (complete eβ x)
  complete-k (shown {k} x A)      = ∈-++⁺ʳ (rows βl) (cm⁺ (complete eσ x) (if-t (→alive (k ++ [ ix 0 ]) A) (here refl)))
  complete-k (pinned {k} x nA ins) = ∈-++⁺ʳ (rows βl) (cm⁺ (complete eσ x) (if-f (off (alive→ (k ++ [ ix 0 ])) nA) (when⁺ (fromT ins))))

conn-exact : ∀ {A B} (sD : Den A) (F : Den A → Den B) (p : Pos) (σl : Listed A) (βl : Listed B)
  → Exactly σl (Tb.Connect.σ sD F p) → Exactly βl (Tb.Connect.β sD F p)
  → Exactly (connRows (p ++ [ ix 1 ]) σl βl) (Tb.Connect.ConnT sD F p)
conn-exact sD F p σl βl eσ eβ u = record { sound = sound-k ; complete = complete-k }
  where open ConnX sD F p σl βl (eσ (proj₁ (∨-false {short σl} u))) (eβ (proj₂ (∨-false {short σl} u)))

------------------------------------------------------------------------
-- A program tree

-- Each listed hot in scope, joined anywhere, is exactly its table joined.
data EnvRel : ∀ {Γ} → All Listed Γ → DenEnv Γ → Set₁ where
  []  : EnvRel [] []
  _∷_ : ∀ {A Γ} {l : Listed A} {d : Den A} {ρL : All Listed Γ} {ρD : DenEnv Γ}
      → (∀ p → Exactly (rejoin p l) (enter d p)) → EnvRel ρL ρD → EnvRel (l ∷ ρL) (d ∷ ρD)

env-lookup : ∀ {Γ A} {ρL : All Listed Γ} {ρD : DenEnv Γ} → EnvRel ρL ρD → (i : A ∈ Γ)
  → ∀ p → Exactly (rejoin p (lookup ρL i)) (enter (lookup ρD i) p)
env-lookup (r ∷ _) (here refl) = r
env-lookup (_ ∷ ρ) (there i)   = env-lookup ρ i

-- THE LISTING IS THE TABLE: whatever `listT` lists uncut is exactly the
-- rows of `approxᵀ` at the same approximant.
listT-exact : ∀ {Γ A} n (o : Obs Timeline Γ A) {ρL : All Listed Γ} {ρD : DenEnv Γ} → EnvRel ρL ρD
  → ∀ p {l} → listT n o ρL p ≡ just l → Exactly l (enter (approxᵀ n o ρD) p)
listT-exact n (cold c)  ρ p refl = walk-exact fuel _
listT-exact n empty     ρ p refl = end-exact _
listT-exact n (of xs)   ρ p refl = walk-exact fuel _
listT-exact n (map f s) {ρL} ρ p e with bind⁻ {m = listT n s ρL p} e
... | (l₀ , e₀ , refl) = map-exact f (listT-exact n s ρ p e₀)
listT-exact n (scan f z s)      ρ p ()
listT-exact n (takeWhile i q s) ρ p ()
listT-exact n (flatMap (mergeᶠ nothing) f s) {ρL} {ρD} ρ p e with bind⁻ {m = listT n s ρL p} e
... | (o , eo , e₁)
  with bind⁻ {m = mapM (λ qa → bind (listT n (f (proj₂ qa)) ρL (proj₁ qa ++ [ ix 1 ])) λ l → just (proj₁ qa , proj₂ qa , l)) (values (rows o))} e₁
... | (ls , els , refl) = merge-exact (λ a → approxᵀ n (f a) ρD) o ls (listT-exact n s ρ p eo) from to
  where
    from : ∀ {q a l} → (q , a , l) ∈ ls → (q , a) ∈ values (rows o) × Exactly l (enter (approxᵀ n (f a) ρD) (q ++ [ ix 1 ]))
    from m with mapM⁻ {xs = values (rows o)} els m
    ... | ((q′ , a′) , vm , fx) with bind⁻ {m = listT n (f a′) ρL (q′ ++ [ ix 1 ])} fx
    ... | (l′ , el′ , refl) = vm , listT-exact n (f a′) ρ (q′ ++ [ ix 1 ]) el′
    to : ∀ {q a} → (q , a) ∈ values (rows o) → Σ (Listed _) λ l → (q , a , l) ∈ ls
    to {q} {a} vm with mapM⁺ {xs = values (rows o)} els vm
    ... | (y , ym , fx) with bind⁻ {m = listT n (f a) ρL (q ++ [ ix 1 ])} fx
    ... | (l′ , _ , refl) = l′ , ym
listT-exact n (flatMap (mergeᶠ (just zero)) f s) ρ p ()
listT-exact n (flatMap (mergeᶠ (just (suc zero))) f s) {ρL} {ρD} ρ p e with bind⁻ {m = listT n s ρL p} e
... | (o , eo , e₁) =
  concat-exact (λ a → approxᵀ n (f a) ρD) _ (λ a → listT n (f a) ρL) o (listT-exact n s ρ p eo)
    (λ {a} {s′} el → listT-exact n (f a) ρ s′ el) e₁
listT-exact n (flatMap (mergeᶠ (just (suc (suc k)))) f s) ρ p ()
listT-exact n (flatMap switchᶠ f s)  ρ p ()
listT-exact n (flatMap exhaustᶠ f s) ρ p ()
listT-exact n (connect s b) {ρL} {ρD} ρ p e with bind⁻ {m = listT n s ρL (p ++ [ ix 1 ])} e
... | (σl , eσ , e₁) with bind⁻ {m = listT n b (hotOf σl ∷ ρL) (p ++ [ ix 0 ])} e₁
... | (βl , eβ , refl) =
  conn-exact (approxᵀ n s ρD) (λ h → approxᵀ n b (h ∷ ρD)) p σl βl σx
    (listT-exact n b ((λ p′ → rejoin-exact (proper-exact σx) p′) ∷ ρ) (p ++ [ ix 0 ]) eβ)
  where
    σx = listT-exact n s ρ (p ++ [ ix 1 ]) eσ
listT-exact n (connected i) ρ p refl = env-lookup ρ i p
listT-exact zero    (defer l) ρ p refl = λ ()
listT-exact (suc n) (defer l) {ρL} ρ p e with bind⁻ {m = listT n (Later.force l) ρL (p ++ [ ix 1 ])} e
... | (b , eb , refl) = defer-exact (listT-exact n (Later.force l) ρ (p ++ [ ix 1 ]) eb)

-- A closed program, as the oracle lists it.
tabled-exact : ∀ {A} n (o : Obs Timeline [] A) p {l} → listT n o [] p ≡ just l → Exactly l (enter (approxᵀ n o []) p)
tabled-exact n o p = listT-exact n o [] p
