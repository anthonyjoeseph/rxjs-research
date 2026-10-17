{-# OPTIONS --guardedness #-}

-- COMPARING REPORTED RUNS.  A reader of a timeline sees its values, each
-- at its tick, then whether it completed or fell silent; a `stall`, and a
-- frame holding only stalls, it never sees.  So a run is the set of
-- finite prefixes a reader can see of it, and the order on runs is
-- inclusion of those sets: the lower run shows a prefix of what the
-- upper shows, then nothing more.
--
-- A limit of a chain is read off its members by search, one `stall` per
-- step searched, so it is productive whatever the chain does.
module denotation.Order where

open import Data.Bool using (true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_; _≤_; z≤n; s≤s; _⊔_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m; n≤1+n; ≤⇒≤′; ≡ᵇ⇒≡; +-identityʳ; +-suc; m≤n⇒m<n∨m≡n)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import denotation.MonotonicList using (ML; Burst; Burst∞; ML∞; done; quiet; at; emit; stall; close; Time)

------------------------------------------------------------------------
-- What a reader sees

data Item (A : Set) : Set where
  val    : Time → A → Item A
  fin    : Item A
  silent : Item A

-- `is` is how the run begins, as a reader sees it.  Inside a frame the
-- tick is known, so a value is seen with it.
mutual
  data Shows {A : Set} : ML A → List (Item A) → Set where
    nil    : ∀ {x} → Shows x []
    done⁺  : Shows done (fin ∷ [])
    quiet⁺ : Shows quiet (silent ∷ [])
    at⁺    : ∀ {t b is} → ShowsIn t b is → Shows (at t b) is

  data ShowsIn {A : Set} (t : Time) : Burst A → List (Item A) → Set where
    nil    : ∀ {b} → ShowsIn t b []
    emit⁺  : ∀ {a k is} → ShowsIn t (Burst∞.force k) is → ShowsIn t (emit a k) (val t a ∷ is)
    stall⁺ : ∀ {k is} → ShowsIn t (Burst∞.force k) is → ShowsIn t (stall k) is
    close⁺ : ∀ {k is} → Shows (ML∞.force k) is → ShowsIn t (close k) is

-- The lower run shows nothing the upper does not.
_⊑_ : ∀ {A : Set} → ML A → ML A → Set
x ⊑ y = ∀ {is} → Shows x is → Shows y is

-- The same run, up to what no reader sees.
_≃_ : ∀ {A : Set} → ML A → ML A → Set
x ≃ y = x ⊑ y × y ⊑ x

-- Each run shows at least what the one before it does.
Chain : ∀ {A : Set} → (ℕ → ML A) → Set
Chain c = ∀ n → c n ⊑ c (suc n)

------------------------------------------------------------------------
-- Prefixes

data _≼_ {A : Set} : List A → List A → Set where
  []≼ : ∀ {ys} → [] ≼ ys
  ∷≼  : ∀ {x xs ys} → xs ≼ ys → (x ∷ xs) ≼ (x ∷ ys)

-- A reader who saw a prefix saw each shorter one.
mutual
  shows-≼ : ∀ {A : Set} {x : ML A} {is js} → js ≼ is → Shows x is → Shows x js
  shows-≼ []≼    _          = nil
  shows-≼ (∷≼ p) done⁺      with p
  ... | []≼ = done⁺
  shows-≼ (∷≼ p) quiet⁺     with p
  ... | []≼ = quiet⁺
  shows-≼ p      (at⁺ s)    = at⁺ (showsIn-≼ p s)

  showsIn-≼ : ∀ {A : Set} {t} {b : Burst A} {is js} → js ≼ is → ShowsIn t b is → ShowsIn t b js
  showsIn-≼ []≼    _          = nil
  showsIn-≼ (∷≼ p) (emit⁺ s)  = emit⁺ (showsIn-≼ p s)
  showsIn-≼ p      (stall⁺ s) = stall⁺ (showsIn-≼ p s)
  showsIn-≼ p      (close⁺ s) = close⁺ (shows-≼ p s)

-- What two readers of one run saw, one saw a prefix of.
Comparable : ∀ {A : Set} → List A → List A → Set
Comparable xs ys = xs ≼ ys ⊎ ys ≼ xs

cons-cmp : ∀ {A : Set} {x : A} {xs ys} → Comparable xs ys → Comparable (x ∷ xs) (x ∷ ys)
cons-cmp (inj₁ p) = inj₁ (∷≼ p)
cons-cmp (inj₂ p) = inj₂ (∷≼ p)

mutual
  shows-cmp : ∀ {A : Set} {x : ML A} {is js} → Shows x is → Shows x js → Comparable is js
  shows-cmp nil     _       = inj₁ []≼
  shows-cmp _       nil     = inj₂ []≼
  shows-cmp done⁺   done⁺   = inj₁ (∷≼ []≼)
  shows-cmp quiet⁺  quiet⁺  = inj₁ (∷≼ []≼)
  shows-cmp (at⁺ s) (at⁺ r) = showsIn-cmp s r

  showsIn-cmp : ∀ {A : Set} {t} {b : Burst A} {is js} → ShowsIn t b is → ShowsIn t b js → Comparable is js
  showsIn-cmp nil        _          = inj₁ []≼
  showsIn-cmp _          nil        = inj₂ []≼
  showsIn-cmp (emit⁺ s)  (emit⁺ r)  = cons-cmp (showsIn-cmp s r)
  showsIn-cmp (stall⁺ s) (stall⁺ r) = showsIn-cmp s r
  showsIn-cmp (close⁺ s) (close⁺ r) = shows-cmp s r

-- A prefix no shorter than the other is all of it.
cmp-long : ∀ {A : Set} {xs ys : List A} → Comparable xs ys → length xs ≤ length ys → xs ≼ ys
cmp-long (inj₁ p) _ = p
cmp-long (inj₂ p) l = long p l
  where
    long : ∀ {A : Set} {xs ys : List A} → ys ≼ xs → length xs ≤ length ys → xs ≼ ys
    long {xs = []}    []≼    _       = []≼
    long {xs = _ ∷ _} []≼    ()
    long              (∷≼ p) (s≤s l) = ∷≼ (long p l)

private
  ≼-refl : ∀ {A} (xs : List A) → xs ≼ xs
  ≼-refl []       = []≼
  ≼-refl (x ∷ xs) = ∷≼ (≼-refl xs)

  ≼-trans : ∀ {A : Set} {xs ys zs : List A} → xs ≼ ys → ys ≼ zs → xs ≼ zs
  ≼-trans []≼     _       = []≼
  ≼-trans (∷≼ p) (∷≼ q) = ∷≼ (≼-trans p q)

  -- The longer of two lists, when one is a prefix of the other.
  longer : ∀ {A : Set} → List A → List A → List A
  longer []       ys       = ys
  longer xs       []       = xs
  longer (x ∷ xs) (_ ∷ ys) = x ∷ longer xs ys

  longer-≼ˡ : ∀ {A : Set} {xs ys : List A} → xs ≼ ys → longer xs ys ≡ ys
  longer-≼ˡ {ys = ys} []≼ = refl
  longer-≼ˡ (∷≼ p) = cong (_ ∷_) (longer-≼ˡ p)

  longer-≼ʳ : ∀ {A : Set} {xs ys : List A} → ys ≼ xs → longer xs ys ≡ xs
  longer-≼ʳ {xs = []}     []≼ = refl
  longer-≼ʳ {xs = _ ∷ _}  []≼ = refl
  longer-≼ʳ (∷≼ p) = cong (_ ∷_) (longer-≼ʳ p)

  longer-ub₁ : ∀ {A : Set} {xs ys : List A} → Comparable xs ys → xs ≼ longer xs ys
  longer-ub₁ (inj₁ p) rewrite longer-≼ˡ p = p
  longer-ub₁ {xs = xs} (inj₂ p) rewrite longer-≼ʳ p = ≼-refl xs

  longer-ub₂ : ∀ {A : Set} {xs ys : List A} → Comparable xs ys → ys ≼ longer xs ys
  longer-ub₂ {ys = ys} (inj₁ p) rewrite longer-≼ˡ p = ≼-refl ys
  longer-ub₂ (inj₂ p) rewrite longer-≼ʳ p = p

  -- The item after `ps` in `qs`, if `qs` reaches that far.
  after : ∀ {A : Set} → List A → List A → Maybe A
  after []       (q ∷ qs) = just q
  after (_ ∷ ps) (_ ∷ qs) = after ps qs
  after _        []       = nothing

  after-just : ∀ {A : Set} {ps qs : List A} {q} → after ps qs ≡ just q → Comparable ps qs → (ps ++ [ q ]) ≼ qs
  after-just {ps = []}     {q ∷ qs} refl _        = ∷≼ []≼
  after-just {ps = _ ∷ ps} {_ ∷ qs} e (inj₁ (∷≼ p)) = ∷≼ (after-just e (inj₁ p))
  after-just {ps = _ ∷ ps} {_ ∷ qs} e (inj₂ (∷≼ p)) = ∷≼ (after-just e (inj₂ p))

  after-reach : ∀ {A : Set} {ps qs : List A} {j js} → (ps ++ (j ∷ js)) ≼ qs → after ps qs ≡ just j
  after-reach {ps = []}     (∷≼ p) = refl
  after-reach {ps = _ ∷ ps} (∷≼ p) = after-reach {ps = ps} p

  after-≼ : ∀ {A : Set} {ps xs ys : List A} {q} → xs ≼ ys → after ps xs ≡ just q → after ps ys ≡ just q
  after-≼ {ps = []}     (∷≼ p) e = e
  after-≼ {ps = _ ∷ ps} (∷≼ p) e = after-≼ {ps = ps} p e

  -- What is past the prefix of one list, the other agrees with.
  agree : ∀ {A : Set} {ps xs ys : List A} {q j js} → after ps xs ≡ just q → (ps ++ (j ∷ js)) ≼ ys → Comparable xs ys → q ≡ j
  agree {ps = ps} e p (inj₁ xy) with trans (sym (after-≼ {ps = ps} xy e)) (after-reach {ps = ps} p)
  ... | refl = refl
  agree {ps = ps} e p (inj₂ yx) with trans (sym e) (after-≼ {ps = ps} yx (after-reach {ps = ps} p))
  ... | refl = refl

  found-nothing : ∀ {A : Set} {ps qs : List A} {j js} → after ps qs ≡ nothing → (ps ++ (j ∷ js)) ≼ qs → ⊥
  found-nothing {ps = ps} e p with trans (sym e) (after-reach {ps = ps} p)
  ... | ()

  -- Nothing is seen after the completion or the silence.
  data Past {A : Set} : List (Item A) → Set where
    fin-past    : ∀ {y ys} → Past (fin ∷ y ∷ ys)
    silent-past : ∀ {y ys} → Past (silent ∷ y ∷ ys)
    later       : ∀ {z zs} → Past zs → Past (z ∷ zs)

  past : ∀ {A : Set} (ps : List (Item A)) {j y ys} → j ≡ fin ⊎ j ≡ silent → Past (ps ++ (j ∷ y ∷ ys))
  past []       (inj₁ refl) = fin-past
  past []       (inj₂ refl) = silent-past
  past (_ ∷ ps) j           = later (past ps j)

  mutual
    no-past : ∀ {A : Set} {x : ML A} {zs} → Past zs → Shows x zs → ⊥
    no-past (later ()) done⁺
    no-past (later ()) quiet⁺
    no-past p (at⁺ s) = noIn-past p s

    noIn-past : ∀ {A : Set} {t} {b : Burst A} {zs} → Past zs → ShowsIn t b zs → ⊥
    noIn-past (later p) (emit⁺ s) = noIn-past p s
    noIn-past p (stall⁺ s) = noIn-past p s
    noIn-past p (close⁺ s) = no-past p s

------------------------------------------------------------------------
-- Reading with a budget

-- What a reader sees in `f` steps.
private
  mutual
    seen : ∀ {A : Set} → ℕ → ML A → List (Item A)
    seen zero    _        = []
    seen (suc f) done     = fin ∷ []
    seen (suc f) quiet    = silent ∷ []
    seen (suc f) (at t b) = seenIn f t b

    seenIn : ∀ {A : Set} → ℕ → Time → Burst A → List (Item A)
    seenIn zero    t _          = []
    seenIn (suc f) t (emit a k) = val t a ∷ seenIn f t (Burst∞.force k)
    seenIn (suc f) t (stall k)  = seenIn f t (Burst∞.force k)
    seenIn (suc f) t (close k)  = seen f (ML∞.force k)

  mutual
    seen-shows : ∀ {A} f (x : ML A) → Shows x (seen f x)
    seen-shows zero    _        = nil
    seen-shows (suc f) done     = done⁺
    seen-shows (suc f) quiet    = quiet⁺
    seen-shows (suc f) (at t b) = at⁺ (seenIn-shows f t b)

    seenIn-shows : ∀ {A} f t (b : Burst A) → ShowsIn t b (seenIn f t b)
    seenIn-shows zero    t _          = nil
    seenIn-shows (suc f) t (emit a k) = emit⁺ (seenIn-shows f t (Burst∞.force k))
    seenIn-shows (suc f) t (stall k)  = stall⁺ (seenIn-shows f t (Burst∞.force k))
    seenIn-shows (suc f) t (close k)  = close⁺ (seen-shows f (ML∞.force k))

  -- More budget, more seen.
  mutual
    seen-mono : ∀ {A : Set} {f g} → f ≤ g → (x : ML A) → seen f x ≼ seen g x
    seen-mono z≤n       _        = []≼
    seen-mono (s≤s f≤g) done     = ∷≼ []≼
    seen-mono (s≤s f≤g) quiet    = ∷≼ []≼
    seen-mono (s≤s f≤g) (at t b) = seenIn-mono f≤g t b

    seenIn-mono : ∀ {A : Set} {f g} → f ≤ g → ∀ t (b : Burst A) → seenIn f t b ≼ seenIn g t b
    seenIn-mono z≤n       t _          = []≼
    seenIn-mono (s≤s f≤g) t (emit a k) = ∷≼ (seenIn-mono f≤g t (Burst∞.force k))
    seenIn-mono (s≤s f≤g) t (stall k)  = seenIn-mono f≤g t (Burst∞.force k)
    seenIn-mono (s≤s f≤g) t (close k)  = seen-mono f≤g (ML∞.force k)

  -- Whatever a reader sees, some budget sees.
  mutual
    shows-seen : ∀ {A : Set} {x : ML A} {is} → Shows x is → ∃ λ f → is ≼ seen f x
    shows-seen nil     = 0 , []≼
    shows-seen done⁺   = 1 , ∷≼ []≼
    shows-seen quiet⁺  = 1 , ∷≼ []≼
    shows-seen (at⁺ s) with showsIn-seen s
    ... | f , p = suc f , p

    showsIn-seen : ∀ {A : Set} {t} {b : Burst A} {is} → ShowsIn t b is → ∃ λ f → is ≼ seenIn f t b
    showsIn-seen nil        = 0 , []≼
    showsIn-seen (emit⁺ s)  with showsIn-seen s
    ... | f , p = suc f , ∷≼ p
    showsIn-seen (stall⁺ s) with showsIn-seen s
    ... | f , p = suc f , p
    showsIn-seen (close⁺ s) with shows-seen s
    ... | f , p = suc f , p

------------------------------------------------------------------------
-- The limit of a chain

private
  -- The longest of what members 0 … k show in f steps.
  bestAt : ∀ {A : Set} → (ℕ → ML A) → ℕ → ℕ → List (Item A)
  bestAt c f zero    = seen f (c zero)
  bestAt c f (suc k) = longer (seen f (c (suc k))) (bestAt c f k)

  -- Search stage i: members up to i, read for i steps.
  best : ∀ {A : Set} → (ℕ → ML A) → ℕ → List (Item A)
  best c i = bestAt c i i

  -- `ps` already shown; search at stage i.  Outside a frame, then inside
  -- the frame at tick t.
  mutual
    from : ∀ {A : Set} → (ℕ → ML A) → List (Item A) → ℕ → ML A
    from c ps i with after ps (best c i)
    ... | nothing         = at 0 (stall λ where .Burst∞.force → fromIn c 0 ps (suc i))
    ... | just fin        = done
    ... | just silent     = quiet
    ... | just (val t a)  = at t (emit a λ where .Burst∞.force → fromIn c t (ps ++ [ val t a ]) i)

    fromIn : ∀ {A : Set} → (ℕ → ML A) → Time → List (Item A) → ℕ → Burst A
    fromIn c t ps i with after ps (best c i)
    ... | nothing         = stall λ where .Burst∞.force → fromIn c t ps (suc i)
    ... | just fin        = close λ where .ML∞.force → done
    ... | just silent     = close λ where .ML∞.force → quiet
    ... | just (val u a) with u ≡ᵇ t
    ...   | true  = emit a λ where .Burst∞.force → fromIn c t (ps ++ [ val u a ]) i
    ...   | false = close λ where .ML∞.force → at u (emit a λ where .Burst∞.force → fromIn c u (ps ++ [ val u a ]) i)

-- The least upper bound of a chain of runs.
limit : ∀ {A : Set} → (ℕ → ML A) → ML A
limit c = from c [] 0

------------------------------------------------------------------------
-- The limit is the least upper bound

private
  module _ {A : Set} {c : ℕ → ML A} (ch : Chain c) where
    chain-≤′ : ∀ {k j} → k ≤′ j → c k ⊑ c j
    chain-≤′ ≤′-refl     s = s
    chain-≤′ (≤′-step p) s = ch _ (chain-≤′ p s)

    chain-≤ : ∀ {k j} → k ≤ j → c k ⊑ c j
    chain-≤ p = chain-≤′ (≤⇒≤′ p)

    -- Two lists members of the chain show, read at a common member.
    cmp : ∀ {k j is js} → Shows (c k) is → Shows (c j) js → Comparable is js
    cmp {k} {j} s r = shows-cmp (chain-≤ (m≤m⊔n k j) s) (chain-≤ (m≤n⊔m k j) r)

    -- What stage f's longest is: one member's reading.
    bestAt-is : ∀ f k → ∃ λ k′ → k′ ≤ k × bestAt c f k ≡ seen f (c k′)
    bestAt-is f zero    = zero , z≤n , refl
    bestAt-is f (suc k) with bestAt-is f k
    ... | k′ , k′≤k , eq rewrite eq with cmp (seen-shows f (c (suc k))) (seen-shows f (c k′))
    ...   | inj₁ p rewrite longer-≼ˡ p = k′ , ≤-trans k′≤k (n≤1+n k) , refl
    ...   | inj₂ p rewrite longer-≼ʳ p = suc k , ≤-refl , refl

    bestAt-shows : ∀ f k → Shows (c k) (bestAt c f k)
    bestAt-shows f k with bestAt-is f k
    ... | k′ , k′≤k , eq rewrite eq = chain-≤ k′≤k (seen-shows f (c k′))

    bestAt-≥ : ∀ f {k j} → k ≤ j → seen f (c k) ≼ bestAt c f j
    bestAt-≥ f {j = zero}  z≤n = ≼-refl _
    bestAt-≥ f {k} {suc j} k≤ with m≤n⇒m<n∨m≡n k≤
    ... | inj₂ refl = longer-ub₁ (cmp (seen-shows f (c (suc j))) (bestAt-shows f j))
    ... | inj₁ (s≤s k≤j) = ≼-trans (bestAt-≥ f k≤j) (longer-ub₂ (cmp (seen-shows f (c (suc j))) (bestAt-shows f j)))

    best-mono : ∀ {i j} → i ≤ j → best c i ≼ best c j
    best-mono {i} {j} i≤j with bestAt-is i i
    ... | k′ , k′≤i , eq rewrite eq = ≼-trans (seen-mono i≤j (c k′)) (bestAt-≥ j (≤-trans k′≤i i≤j))

    -- Whatever a member shows, some stage of the search has.
    reached : ∀ {k is} → Shows (c k) is → ∃ λ N → is ≼ best c N
    reached {k} s with shows-seen s
    ... | f , p = f ⊔ k , ≼-trans p (≼-trans (seen-mono (m≤m⊔n f k) (c k)) (bestAt-≥ (f ⊔ k) (m≤n⊔m f k)))

    best-cmp : ∀ i j → Comparable (best c i) (best c j)
    best-cmp i j = cmp (bestAt-shows i i) (bestAt-shows j j)

    -- SOUND: the limit shows only what some member does.
    found : ∀ {ps i q} → Shows (c i) ps → after ps (best c i) ≡ just q → Shows (c i) (ps ++ [ q ])
    found {i = i} sp e = shows-≼ (after-just e (cmp sp (bestAt-shows i i))) (bestAt-shows i i)

    mutual
      from-sound : ∀ {ps i js} → Shows (c i) ps → Shows (from c ps i) js → ∃ λ k → Shows (c k) (ps ++ js)
      from-sound {ps} {i} {[]} sp s = i , subst (Shows (c i)) (sym (++-identityʳ ps)) sp
      from-sound {ps} {i} {j ∷ js} sp s with after ps (best c i) in e
      ... | nothing with s
      ...   | at⁺ (stall⁺ r) = fromIn-sound (ch i sp) r
      from-sound {ps} {i} {j ∷ js} sp s | just fin with s
      ...   | done⁺ = i , found sp e
      from-sound {ps} {i} {j ∷ js} sp s | just silent with s
      ...   | quiet⁺ = i , found sp e
      from-sound {ps} {i} {j ∷ js} sp s | just (val t a) with s
      ...   | at⁺ (emit⁺ r) with fromIn-sound (found sp e) r
      ...     | k , q = k , subst (Shows (c k)) (++-assoc ps [ val t a ] js) q

      fromIn-sound : ∀ {t ps i js} → Shows (c i) ps → ShowsIn t (fromIn c t ps i) js → ∃ λ k → Shows (c k) (ps ++ js)
      fromIn-sound {t} {ps} {i} {[]} sp s = i , subst (Shows (c i)) (sym (++-identityʳ ps)) sp
      fromIn-sound {t} {ps} {i} {j ∷ js} sp s with after ps (best c i) in e
      ... | nothing with s
      ...   | stall⁺ r = fromIn-sound (ch i sp) r
      fromIn-sound {t} {ps} {i} {j ∷ js} sp s | just fin with s
      ...   | close⁺ done⁺ = i , found sp e
      fromIn-sound {t} {ps} {i} {j ∷ js} sp s | just silent with s
      ...   | close⁺ quiet⁺ = i , found sp e
      fromIn-sound {t} {ps} {i} {j ∷ js} sp s | just (val u a) with u ≡ᵇ t in b
      ... | true with ≡ᵇ⇒≡ u t (subst T (sym b) _)
      ...   | refl with s
      ...     | emit⁺ r with fromIn-sound (found sp e) r
      ...       | k , q = k , subst (Shows (c k)) (++-assoc ps [ val u a ] js) q
      fromIn-sound {t} {ps} {i} {j ∷ js} sp s | just (val u a) | false with s
      ...   | close⁺ (at⁺ (emit⁺ r)) with fromIn-sound (found sp e) r
      ...     | k , q = k , subst (Shows (c k)) (++-assoc ps [ val u a ] js) q

    -- COMPLETE: the limit shows whatever a member does.  `d` bounds the
    -- stages still to search before stage N, where all of it is found.
    mutual
      from-complete : ∀ {N} js {ps i} d → N ≤ i + d → (ps ++ js) ≼ best c N → Shows (from c ps i) js
      from-complete []        _ _ _ = nil
      from-complete {N} (j ∷ js) {ps} {i} d N≤ p with after ps (best c i) in e
      ... | nothing with d
      ...   | zero    = ⊥-elim (found-nothing e (≼-trans p (best-mono (subst (N ≤_) (+-identityʳ i) N≤))))
      ...   | suc d′  = at⁺ (stall⁺ (fromIn-complete (j ∷ js) d′ (subst (N ≤_) (+-suc i d′) N≤) p))
      from-complete {N} (j ∷ js) {ps} {i} d N≤ p | just q with agree e p (best-cmp i N)
      from-complete {N} (fin ∷ js) {ps} {i} d N≤ p | just fin | refl with js
      ... | [] = done⁺
      ... | _ ∷ _ = ⊥-elim (no-past (past ps (inj₁ refl)) (shows-≼ p (bestAt-shows N N)))
      from-complete {N} (silent ∷ js) {ps} {i} d N≤ p | just silent | refl with js
      ... | [] = quiet⁺
      ... | _ ∷ _ = ⊥-elim (no-past (past ps (inj₂ refl)) (shows-≼ p (bestAt-shows N N)))
      from-complete {N} (val t a ∷ js) {ps} {i} d N≤ p | just (val t a) | refl =
        at⁺ (emit⁺ (fromIn-complete js d N≤ (subst (_≼ best c N) (sym (++-assoc ps [ val t a ] js)) p)))

      fromIn-complete : ∀ {N t} js {ps i} d → N ≤ i + d → (ps ++ js) ≼ best c N → ShowsIn t (fromIn c t ps i) js
      fromIn-complete []        _ _ _ = nil
      fromIn-complete {N} (j ∷ js) {ps} {i} d N≤ p with after ps (best c i) in e
      ... | nothing with d
      ...   | zero    = ⊥-elim (found-nothing e (≼-trans p (best-mono (subst (N ≤_) (+-identityʳ i) N≤))))
      ...   | suc d′  = stall⁺ (fromIn-complete (j ∷ js) d′ (subst (N ≤_) (+-suc i d′) N≤) p)
      fromIn-complete {N} (j ∷ js) {ps} {i} d N≤ p | just q with agree e p (best-cmp i N)
      fromIn-complete {N} (fin ∷ js) {ps} {i} d N≤ p | just fin | refl with js
      ... | [] = close⁺ done⁺
      ... | _ ∷ _ = ⊥-elim (no-past (past ps (inj₁ refl)) (shows-≼ p (bestAt-shows N N)))
      fromIn-complete {N} (silent ∷ js) {ps} {i} d N≤ p | just silent | refl with js
      ... | [] = close⁺ quiet⁺
      ... | _ ∷ _ = ⊥-elim (no-past (past ps (inj₂ refl)) (shows-≼ p (bestAt-shows N N)))
      fromIn-complete {N} {t} (val u a ∷ js) {ps} {i} d N≤ p | just (val u a) | refl with u ≡ᵇ t in b
      ... | true with ≡ᵇ⇒≡ u t (subst T (sym b) _)
      ...   | refl = emit⁺ (fromIn-complete js d N≤ (subst (_≼ best c N) (sym (++-assoc ps [ val t a ] js)) p))
      fromIn-complete {N} {t} (val u a ∷ js) {ps} {i} d N≤ p | just (val u a) | refl | false = close⁺ (at⁺ (emit⁺ (fromIn-complete js d N≤ (subst (_≼ best c N) (sym (++-assoc ps [ val u a ] js)) p))))

-- The limit of a chain is above each member, and below any run every
-- member is below.
limit-ub : ∀ {A : Set} {c : ℕ → ML A} → Chain c → ∀ k → c k ⊑ limit c
limit-ub ch k s with reached ch s
... | N , p = from-complete ch _ {[]} {0} N ≤-refl p

limit-least : ∀ {A : Set} {c : ℕ → ML A} {y} → Chain c → (∀ k → c k ⊑ y) → limit c ⊑ y
limit-least ch below s with from-sound ch {[]} {0} nil s
... | k , r = below k r
