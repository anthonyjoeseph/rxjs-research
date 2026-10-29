{-# OPTIONS --guardedness #-}

-- THE ROWS BUT FOR A SKIP AT THE FOCUS: two holes owing the same rows
-- but for skips at `p`, read up a context whose other parts lie past
-- `p`, owe the same rows at the root but for skips at `p`.  A merge's end
-- waits on every part's rows, and a row at `p` lies by any end at or past
-- `p`, so where the two disagree no end reads them differently.
module direct.Skip where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _ʳ++_; _++_; [_])
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool using (true; false)
open import direct.Up using (all-ʳ++)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Pos; ix)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; end; _≺_; _≼_; MapT; map-out; map-skip; map-end)
open import denotation.EmissionSet.Laws.Modulus using (≺-trans; ≺→≼; ≼-≺-≺; ≺-ext)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import direct.Rows using (up; rows; rowsL; pendRows; Gone; Lanes; Each; module Flat; _≃_; _⇄_; Vis)

------------------------------------------------------------------------
-- Rows past a position

-- Every row strictly past `p`.
After : ∀ {A} → Pos → EmissionSet A → Set
After p t = ∀ {q e} → t q e → p ≺ q

-- Every row at or past `p`.
Since : ∀ {A} → Pos → EmissionSet A → Set
Since p t = ∀ {q e} → t q e → p ≼ q

-- What a rising event at `p` is owed past: frame by frame, every other
-- part of a merge it rises through.
LeadC : ∀ {R Γ A} → Ctx R Γ A → Pos → Set
LeadC (inMap f c)                                    p = LeadC c p
LeadC (inCut l a c)                                  p = LeadC c p
LeadC (inLn b c)                                     p = LeadC c p
LeadC (inOuter (mergeᶠ nothing) f d n q ls c)        p = Each (After p) (rowsL ls) × LeadC c p
LeadC (inLanes (mergeᶠ nothing) f d n q o pre post c) p =
  After p (rows o) × Each (After p) (rowsL pre) × Each (After p) (rowsL post) × LeadC c p
LeadC _                                              p = ⊤

after-since : ∀ {B} {p} (Ls : List (EmissionSet B)) → Each (After p) Ls → Each (Since p) Ls
after-since []       _        = _
after-since {p = p} (_ ∷ Ls) (a , as) = (λ {q} {e} r → ≺→≼ {p} {q} (a {q} {e} r)) , after-since Ls as

since-lanes : ∀ {B} {p} (Ls : List (EmissionSet B)) → Each (Since p) Ls → Since p (Lanes Ls)
since-lanes (_ ∷ _)  (s , _)  {q} {e} (inj₁ r) = s {q} {e} r
since-lanes (_ ∷ Ls) (_ , ss) {q} {e} (inj₂ x) = since-lanes Ls ss {q} {e} x

------------------------------------------------------------------------
-- The relation

Skip : ∀ {A} → Pos → Pos → Ev A → Set
Skip p q e = q ≡ p × e ≡ skip

record _≈⟨_⟩_ {A : Set} (t : EmissionSet A) (p : Pos) (u : EmissionSet A) : Set where
  constructor _⇆_
  field
    fwd : ∀ {q e} → t q e → u q e ⊎ Skip p q e
    bwd : ∀ {q e} → u q e → t q e ⊎ Skip p q e
open _≈⟨_⟩_

≈-sym : ∀ {A} {t u : EmissionSet A} {p} → t ≈⟨ p ⟩ u → u ≈⟨ p ⟩ t
≈-sym (f ⇆ b) = b ⇆ f

≈-refl : ∀ {A} {t : EmissionSet A} {p} → t ≈⟨ p ⟩ t
≈-refl = inj₁ ⇆ inj₁

-- A skip is never seen.
≈-vis : ∀ {A} {t u : EmissionSet A} {p} → t ≈⟨ p ⟩ u → Vis t ≃ Vis u
≈-vis eq = go (fwd eq) ⇄ go (bwd eq)
  where
    go : ∀ {A} {t u : EmissionSet A} {p} → (∀ {q e} → t q e → u q e ⊎ Skip p q e) → ∀ {q e} → Vis t q e → Vis u q e
    go h (r , v) with h r
    ... | inj₁ r′          = r′ , v
    ... | inj₂ (refl , refl) = ⊥-elim v

gone-≈ : ∀ {A} {t u : EmissionSet A} {p c} → t ≈⟨ p ⟩ u → p ≼ c → Gone t c → Gone u c
gone-≈ {c = c} eq pc g {k} {e} r with bwd eq r
... | inj₁ r′            = g {k} {e} r′
... | inj₂ (refl , refl) = pc

data _≈ᴸ⟨_⟩_ {B : Set} : List (EmissionSet B) → Pos → List (EmissionSet B) → Set₁ where
  []  : ∀ {p} → [] ≈ᴸ⟨ p ⟩ []
  _∷_ : ∀ {p t u Ls Ls′} → t ≈⟨ p ⟩ u → Ls ≈ᴸ⟨ p ⟩ Ls′ → (t ∷ Ls) ≈ᴸ⟨ p ⟩ (u ∷ Ls′)

≈ᴸ-sym : ∀ {B} {Ls Ls′ : List (EmissionSet B)} {p} → Ls ≈ᴸ⟨ p ⟩ Ls′ → Ls′ ≈ᴸ⟨ p ⟩ Ls
≈ᴸ-sym []       = []
≈ᴸ-sym (e ∷ es) = ≈-sym e ∷ ≈ᴸ-sym es

≈ᴸ-refl : ∀ {B} (Ls : List (EmissionSet B)) {p} → Ls ≈ᴸ⟨ p ⟩ Ls
≈ᴸ-refl []       = []
≈ᴸ-refl (_ ∷ Ls) = ≈-refl ∷ ≈ᴸ-refl Ls

-- One lane changed, the rest kept.
≈ᴸ-hole : ∀ {B} (xs : List (EmissionSet B)) {ys ys′ p} → ys ≈ᴸ⟨ p ⟩ ys′ → (xs ʳ++ ys) ≈ᴸ⟨ p ⟩ (xs ʳ++ ys′)
≈ᴸ-hole []       h = h
≈ᴸ-hole (x ∷ xs) h = ≈ᴸ-hole xs (≈-refl ∷ h)

lanes-≈ : ∀ {B} {Ls Ls′ : List (EmissionSet B)} {p} → Ls ≈ᴸ⟨ p ⟩ Ls′ → ∀ {k e} → Lanes Ls k e → Lanes Ls′ k e ⊎ Skip p k e
lanes-≈ (e ∷ _)  (inj₁ r) with fwd e r
... | inj₁ r′ = inj₁ (inj₁ r′)
... | inj₂ sk = inj₂ sk
lanes-≈ (_ ∷ es) (inj₂ x) with lanes-≈ es x
... | inj₁ x′ = inj₁ (inj₂ x′)
... | inj₂ sk = inj₂ sk

each-≈ : ∀ {B} {Ls Ls′ : List (EmissionSet B)} {p c} → Ls ≈ᴸ⟨ p ⟩ Ls′ → p ≼ c → Each (λ t → Gone t c) Ls → Each (λ t → Gone t c) Ls′
each-≈ []       pc _        = _
each-≈ {c = c} (e ∷ es) pc (g , gs) = gone-≈ {c = c} e pc g , each-≈ {c = c} es pc gs

------------------------------------------------------------------------
-- Up a map, up a merge

map-≈ : ∀ {A B} (f : A → B) {t u : EmissionSet A} {p} → t ≈⟨ p ⟩ u → MapT f t ≈⟨ p ⟩ MapT f u
map-≈ f eq = go (fwd eq) ⇆ go (bwd eq)
  where
    go : ∀ {t u : EmissionSet _} {p} → (∀ {q e} → t q e → u q e ⊎ Skip p q e) → ∀ {q e} → MapT f t q e → MapT f u q e ⊎ Skip p q e
    go h (map-out r) with h r
    ... | inj₁ r′     = inj₁ (map-out r′)
    ... | inj₂ (_ , ())
    go h (map-skip r) with h r
    ... | inj₁ r′            = inj₁ (map-skip r′)
    ... | inj₂ (refl , refl) = inj₂ (refl , refl)
    go h (map-end r) with h r
    ... | inj₁ r′     = inj₁ (map-end r′)
    ... | inj₂ (_ , ())

since-map : ∀ {A B} (f : A → B) {t : EmissionSet A} {p} → Since p t → Since p (MapT f t)
since-map f s (map-out r)  = s r
since-map f s (map-skip r) = s r
since-map f s (map-end r)  = s r

module _ {A B : Set} (L : A → Pos → EmissionSet B) {p : Pos} where

  -- A lane begun past an outer value lies past what the value lies past.
  lane-since : ∀ {O : EmissionSet A} {Ls q a k e} → Since p O → O q (out a) → Flat.Lane L O Ls q a k e → p ≼ k
  lane-since {q = q} {a = a} {k = k} so r (_ , s) =
    ≺→≼ {p} {k} (≺-trans {p} {q ++ [ ix 1 ]} {k} (≼-≺-≺ {p} {q} {q ++ [ ix 1 ]} (so {q} {out a} r) (≺-ext q [])) s)

  since-flat : ∀ (O : EmissionSet A) (Ls : List (EmissionSet B)) → Since p O → Each (Since p) Ls → Since p (Flat.FlatR L O Ls)
  since-flat O Ls so sl (Flat.val {q} {a} r) = ≺→≼ {p} {q ++ [ ix 0 ]} (≼-≺-≺ {p} {q} {q ++ [ ix 0 ]} (so {q} {out a} r) (≺-ext q []))
  since-flat O Ls so sl (Flat.step r)     = so r
  since-flat O Ls so sl (Flat.oend r _)   = so r
  since-flat O Ls so sl (Flat.opass r _)  = so r
  since-flat O Ls so sl (Flat.lane {q} {a} r l _) = lane-since {O = O} {Ls = Ls} {q = q} {a = a} so r l
  since-flat O Ls so sl (Flat.lend {q} {a} r l _) = lane-since {O = O} {Ls = Ls} {q = q} {a = a} so r l
  since-flat O Ls so sl (Flat.lpass {q} {a} r l _) = lane-since {O = O} {Ls = Ls} {q = q} {a = a} so r l
  since-flat O Ls so sl (Flat.run x _)    = since-lanes Ls sl x
  since-flat O Ls so sl (Flat.rend x _)   = since-lanes Ls sl x
  since-flat O Ls so sl (Flat.rpass x _)  = since-lanes Ls sl x

  -- A merge done by an end at or past the focus is done either way.
  done-≈ : ∀ {O O′ : EmissionSet A} {Ls Ls′} c → O ≈⟨ p ⟩ O′ → Ls ≈ᴸ⟨ p ⟩ Ls′ → p ≼ c → Flat.Done L O Ls c → Flat.Done L O′ Ls′ c
  done-≈ {O′ = O′} {Ls′ = Ls′} c eo es pc (g , h , ls) = gone-≈ {c = c} eo pc g , h′ , each-≈ {c = c} es pc ls
    where
      h′ : ∀ {q a} → O′ q (out a) → q ≺ c → Σ Pos λ c′ → Flat.Lane L O′ Ls′ q a c′ end × c′ ≼ c
      h′ {q} {a} r lt with bwd eo r
      ... | inj₁ r′ = h {q} {a} r′ lt
      ... | inj₂ (_ , ())

  flat-→ : ∀ {O O′ : EmissionSet A} (Ls Ls′ : List (EmissionSet B)) → O ≈⟨ p ⟩ O′ → Ls ≈ᴸ⟨ p ⟩ Ls′ → Since p O → Each (Since p) Ls
         → ∀ {k e} → Flat.FlatR L O Ls k e → Flat.FlatR L O′ Ls′ k e ⊎ Skip p k e
  flat-→ Ls Ls′ eo es so sl (Flat.val r) with fwd eo r
  ... | inj₁ r′       = inj₁ (Flat.val r′)
  ... | inj₂ (_ , ())
  flat-→ Ls Ls′ eo es so sl (Flat.step r) with fwd eo r
  ... | inj₁ r′       = inj₁ (Flat.step r′)
  ... | inj₂ (eq , _) = inj₂ (eq , refl)
  flat-→ Ls Ls′ eo es so sl (Flat.oend {c} r d) with fwd eo r
  ... | inj₁ r′       = inj₁ (Flat.oend r′ (done-≈ c eo es (so r) d))
  ... | inj₂ (_ , ())
  flat-→ Ls Ls′ eo es so sl (Flat.opass {c} r nd) with fwd eo r
  ... | inj₁ r′       = inj₁ (Flat.opass r′ λ d → nd (done-≈ c (≈-sym eo) (≈ᴸ-sym es) (so r) d))
  ... | inj₂ (_ , ())
  flat-→ Ls Ls′ eo es so sl (Flat.lane r l w) with fwd eo r
  ... | inj₁ r′       = inj₁ (Flat.lane r′ l w)
  ... | inj₂ (_ , ())
  flat-→ {O = O} Ls Ls′ eo es so sl (Flat.lend {q} {a} {c} r l d) with fwd eo r
  ... | inj₁ r′       = inj₁ (Flat.lend r′ l (done-≈ c eo es (lane-since {O = O} {Ls = Ls} {q = q} {a = a} so r l) d))
  ... | inj₂ (_ , ())
  flat-→ {O = O} Ls Ls′ eo es so sl (Flat.lpass {q} {a} {c} r l nd) with fwd eo r
  ... | inj₁ r′       = inj₁ (Flat.lpass r′ l λ d → nd (done-≈ c (≈-sym eo) (≈ᴸ-sym es) (lane-since {O = O} {Ls = Ls} {q = q} {a = a} so r l) d))
  ... | inj₂ (_ , ())
  flat-→ Ls Ls′ eo es so sl (Flat.run x w) with lanes-≈ es x
  ... | inj₁ x′ = inj₁ (Flat.run x′ w)
  ... | inj₂ sk = inj₂ sk
  flat-→ Ls Ls′ eo es so sl (Flat.rend {c} x d) with lanes-≈ es x
  ... | inj₁ x′       = inj₁ (Flat.rend x′ (done-≈ c eo es (since-lanes Ls sl x) d))
  ... | inj₂ (_ , ())
  flat-→ Ls Ls′ eo es so sl (Flat.rpass {c} x nd) with lanes-≈ es x
  ... | inj₁ x′       = inj₁ (Flat.rpass x′ λ d → nd (done-≈ c (≈-sym eo) (≈ᴸ-sym es) (since-lanes Ls sl x) d))
  ... | inj₂ (_ , ())

  flat-≈ : ∀ {O O′ : EmissionSet A} (Ls Ls′ : List (EmissionSet B)) → O ≈⟨ p ⟩ O′ → Ls ≈ᴸ⟨ p ⟩ Ls′
         → Since p O → Since p O′ → Each (Since p) Ls → Each (Since p) Ls′ → Flat.FlatR L O Ls ≈⟨ p ⟩ Flat.FlatR L O′ Ls′
  flat-≈ Ls Ls′ eo es so so′ sl sl′ = flat-→ Ls Ls′ eo es so sl ⇆ flat-→ Ls′ Ls (≈-sym eo) (≈ᴸ-sym es) so′ sl′

------------------------------------------------------------------------
-- THE LIFT

up-≈ : ∀ {R Γ A} (c : Ctx R Γ A) {t u : EmissionSet A} {p} → LeadC c p → Since p t → Since p u → t ≈⟨ p ⟩ u → up c t ≈⟨ p ⟩ up c u
up-≈ top                                     ld st su eq = eq
up-≈ (inMap f c)                             ld st su eq = up-≈ c ld (since-map f st) (since-map f su) (map-≈ f eq)
up-≈ (inScan f z c)                          ld st su eq = ≈-refl
up-≈ (inCut true a c)                        ld st su eq = up-≈ c ld st su eq
up-≈ (inCut false a c)                       ld st su eq = ≈-refl
up-≈ (inLn true c)                           ld st su eq = up-≈ c ld st su eq
up-≈ (inLn false c)                          ld st su eq = ≈-refl
up-≈ (inTake i q w c)                        ld st su eq = ≈-refl
up-≈ (inOuter (mergeᶠ nothing) f d n q ls c) {t} {u} (al , ld) st su eq =
  up-≈ c ld (since-flat L t Ls st sl) (since-flat L u Ls su sl) (flat-≈ L Ls Ls eq (≈ᴸ-refl Ls) st su sl sl)
  where
    L  = λ a → pendRows (f a)
    Ls = rowsL ls
    sl = after-since Ls al
up-≈ (inOuter (mergeᶠ (just _)) f d n q ls c) ld st su eq = ≈-refl
up-≈ (inOuter switchᶠ f d n q ls c)           ld st su eq = ≈-refl
up-≈ (inOuter exhaustᶠ f d n q ls c)          ld st su eq = ≈-refl
up-≈ (inLanes (mergeᶠ nothing) f d n q o pre post c) {t} {u} (ao , apre , apost , ld) st su eq =
  up-≈ c ld (since-flat L O Lt so slt) (since-flat L O Lu so slu)
       (flat-≈ L Lt Lu ≈-refl (≈ᴸ-hole (rowsL pre) (eq ∷ ≈ᴸ-refl (rowsL post))) so so slt slu)
  where
    L   = λ a → pendRows (f a)
    O   = rows o
    Lt  = rowsL pre ʳ++ (t ∷ rowsL post)
    Lu  = rowsL pre ʳ++ (u ∷ rowsL post)
    so  = λ {q} {e} r → ≺→≼ {_} {q} (ao {q} {e} r)
    slt = all-ʳ++ (rowsL pre) (after-since (rowsL pre) apre) (st , after-since (rowsL post) apost)
    slu = all-ʳ++ (rowsL pre) (after-since (rowsL pre) apre) (su , after-since (rowsL post) apost)
up-≈ (inLanes (mergeᶠ (just _)) f d n q o pre post c) ld st su eq = ≈-refl
up-≈ (inLanes switchᶠ f d n q o pre post c)   ld st su eq = ≈-refl
up-≈ (inLanes exhaustᶠ f d n q o pre post c)  ld st su eq = ≈-refl
up-≈ (inSrc k b c)                            ld st su eq = ≈-refl
up-≈ (inBody k o c)                           ld st su eq = ≈-refl
