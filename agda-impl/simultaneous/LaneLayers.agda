{-# OPTIONS --guardedness #-}

-- WHERE A LANE'S LAYERS PUT THEIR ROWS: positions below a position, and
-- each operator's rows, and its rows before a position, read from its
-- inputs'.
module simultaneous.LaneLayers where

open import Data.Bool using (Bool; T; not)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.Nat using (ℕ; _<_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Tree using (of)
open import denotation.Position using (Pos; Label; ix; last; root; _≟ᵖ_; _⊕_)
open import denotation.Events using (Timeline; fresh; ofᴱ; <ᵖ-part; ix-<)
open import denotation.EmissionSet using (EmissionSet; Den; enter; out; InE; at-out; on-out; at-end; _≺_; Few; Truncate; module Op;
  module Joining; module Bounded; module Scan; module TakeWhile; module Connecting)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans; ≺-absurd)
open import denotation.Laws.Worlds using (⊕-assoc; ⊕-identityʳ)
open import denotation.Laws.Worlds.Leaves using (of-idx)
open import denotation.Laws.Shows using (few-reach)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.InstEmit using (instEmit; mark; laneStart; laneDone; value; begin; over; stop; outerOpen; outerClose; burstEnd; outerDone; subscribed; completed)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; laneˢ; laneSrc; laneStep; undone; marked; piece)

------------------------------------------------------------------------
-- Positions below a position

Under : Pos → Pos → Set
Under x y = Σ (List Label) λ ys → y ≡ x ⊕ ys

under-refl : ∀ x → Under x x
under-refl x = [] , sym (⊕-identityʳ x)

under-⊕ : ∀ {x y} → Under x y → ∀ l → Under x (y ⊕ [ l ])
under-⊕ {x} (ys , refl) l = ys ++ [ l ] , ⊕-assoc x ys [ l ]

under-trans : ∀ {x y z} → Under x y → Under y z → Under x z
under-trans {x} (ys , refl) (zs , refl) = ys ++ zs , ⊕-assoc x ys zs

-- A position below a child lies past its parent,
under-ext : ∀ x {l y} → Under (x ⊕ [ l ]) y → x ≺ y
under-ext x {l} (ys , refl) = subst (x ≺_) (sym (⊕-assoc x [ l ] ys)) (≺-ext x ys)

-- and before every later child.
under-≺ : ∀ p {i j y} → i < j → Under (p ⊕ [ ix i ]) y → y ≺ (p ⊕ [ ix j ])
under-≺ p {i} {j} lt (ys , refl) = subst (_≺ (p ⊕ [ ix j ])) (sym (⊕-assoc p [ ix i ] ys)) (Equivalence.from T-≡ (<ᵖ-part p ys [] (ix-< lt)))

-- and before its parent's last.
under-last : ∀ p {i y} → Under (p ⊕ [ ix i ]) y → y ≺ (p ⊕ [ last ])
under-last p {i} (ys , refl) = subst (_≺ (p ⊕ [ last ])) (sym (⊕-assoc p [ ix i ] ys)) (Equivalence.from T-≡ (<ᵖ-part p ys [] refl))

------------------------------------------------------------------------
-- Where an operator's rows lie, from where its inputs' do

-- A lane starts past its value,
starts-after : ∀ {A B} {n : ℕ} {f : A → Den B} {o : EmissionSet A} {i q ls′ s} → Bounded.Starts n f o i q ls′ s → q ≺ s
starts-after {q = q} (Bounded.room _)                    = ≺-ext q []
starts-after {q = q} (Bounded.freed _ _)                 = ≺-ext q []
starts-after {q = q} (Bounded.queued {c} _ qc _ _ _)     = ≺-trans {q} {c} {c ⊕ [ ix 1 ]} qc (≺-ext c [])

-- so its rows do.
bd-lane-past : ∀ {A B} {n : ℕ} {f : A → Den B} {o : EmissionSet A} {q a k e} → Bounded.Lane n f o q a k e → q ≺ k
bd-lane-past {q = q} {k = k} (_ , s , (_ , st) , (_ , sl)) = ≺-trans {q} {s} {k} (starts-after st) sl

-- A list's rows lie past its subscription.
of-after : ∀ {X : Set} p (xs : List X) {k e} → enter (Op.of xs) p k e → p ≺ k
of-after p xs (x , _) with of-idx p 0 xs x
... | inj₁ (j , _ , refl) = ≺-ext p []
... | inj₂ refl           = ≺-ext p []

-- A one-value list's rows are its value and its end.
one-rows : ∀ {X : Set} p (x : X) {y e} → InE (ofᴱ p 0 (x ∷ [])) y e → y ≡ p ⊕ [ ix 0 ] ⊎ y ≡ p ⊕ [ last ]
one-rows p x at-out          = inj₁ refl
one-rows p x (on-out at-end) = inj₂ refl

-- A joiner's rows lie past `p` when its outer's, its lanes' and its
-- background's do.
join-past : ∀ {A B} {Lane : Pos → A → EmissionSet B} {o : EmissionSet A} {Bg : EmissionSet B} {Over Runs : Pos → Set} {Cut : Pos → Pos → Set} {Hand : Pos → Set} {p}
          → (∀ {k e} → o k e → p ≺ k) → (∀ {q a k e} → o q (out a) → Lane q a k e → q ≺ k) → (∀ {k e} → Bg k e → p ≺ k)
          → ∀ {k e} → Joining.JoinT Lane o Bg Over Runs Cut Hand k e → p ≺ k
join-past {p = p} po pl pb (Joining.val {q} x)               = ≺-trans {p} {q} {q ⊕ [ ix 0 ]} (po x) (≺-ext q [])
join-past po pl pb (Joining.step x)                          = po x
join-past po pl pb (Joining.opin x)                          = po x
join-past po pl pb (Joining.oend x _)                        = po x
join-past po pl pb (Joining.opass x _)                       = po x
join-past {p = p} po pl pb (Joining.lane {q} {k = k} x _ l _ _)  = ≺-trans {p} {q} {k} (po x) (pl x l)
join-past {p = p} po pl pb (Joining.lend {q} {c = c} x _ l _ _ _)  = ≺-trans {p} {q} {c} (po x) (pl x l)
join-past {p = p} po pl pb (Joining.lpass {q} {c = c} x _ l _ _ _) = ≺-trans {p} {q} {c} (po x) (pl x l)
join-past {p = p} po pl pb (Joining.hand {q} {c = c} x _ l _ _)  = ≺-trans {p} {c} {c ⊕ [ ix 0 ]} (≺-trans {p} {q} {c} (po x) (pl x l)) (≺-ext c [])
join-past {p = p} po pl pb (Joining.left {q} {k = k} x _ l _ _)  = ≺-trans {p} {q} {k} (po x) (pl x l)
join-past po pl pb (Joining.run b _)                         = pb b
join-past po pl pb (Joining.rend b _ _)                      = pb b
join-past po pl pb (Joining.rpass b _ _)                     = pb b
join-past {p = p} po pl pb (Joining.rhand {c} b _)           = ≺-trans {p} {c} {c ⊕ [ ix 0 ]} (pb b) (≺-ext c [])

-- What fails a lane's `takeWhile` is a `laneDone`.
done-of : ∀ {B} (a : IE B) → T (not (undone a)) → Σ ℕ λ k → Σ Pos λ n → a ≡ instEmit (mark (laneDone k)) n
done-of (instEmit (mark (laneDone k)) n) _  = k , n , refl
done-of (instEmit (value _) _)      ()
done-of (instEmit (mark begin) _)      ()
done-of (instEmit (mark over) _)       ()
done-of (instEmit (mark stop) _)       ()
done-of (instEmit (mark subscribed) _) ()
done-of (instEmit (mark completed) _)  ()
done-of (instEmit (mark outerOpen) _)  ()
done-of (instEmit (mark outerClose) _) ()
done-of (instEmit (mark laneStart) _)  ()
done-of (instEmit (mark burstEnd) _)   ()
done-of (instEmit (mark outerDone) _)  ()

------------------------------------------------------------------------
-- An operator's rows before `v`, from its inputs'

few-tr : ∀ {A} {t : EmissionSet A} {v} → Few t v → Few (Truncate t) v
few-tr (ks , h) = ks , λ x lt → h (proj₁ x) lt

few-row : ∀ {A} {t : EmissionSet A} {q e} → t q e → Few t q → Truncate t q e
few-row x F = x , few-reach F

-- A joiner's: its outer's, its lanes', its background's, and the
-- first child of each.
join-few : ∀ {A B} {Lane : Pos → A → EmissionSet B} {o : EmissionSet A} {Bg : EmissionSet B} {Over Runs : Pos → Set} {Cut : Pos → Pos → Set} {Hand : Pos → Set} {v}
         → Few o v → (Σ (List Pos) λ kl → ∀ {q a k e} → o q (out a) → Lane q a k e → k ≺ v → k ∈ kl) → Few Bg v
         → Few (Joining.JoinT Lane o Bg Over Runs Cut Hand) v
join-few {Lane = Lane} {o} {Bg} {Over} {Runs} {Cut} {Hand} {v} (ko , ho) (kl , hl) (kb , hb) = Ks , go
  where
    ix₀ : Pos → Pos
    ix₀ k = k ⊕ [ ix 0 ]

    Ks : List Pos
    Ks = ko ++ (L.map ix₀ ko ++ (kl ++ (L.map ix₀ kl ++ (kb ++ L.map ix₀ kb))))

    dn : ∀ {k} → (k ⊕ [ ix 0 ]) ≺ v → k ≺ v
    dn {k} lt = ≺-trans {k} {k ⊕ [ ix 0 ]} {v} (≺-ext k []) lt

    i₂ : ∀ {k} → k ∈ L.map ix₀ ko → k ∈ Ks
    i₃ : ∀ {k} → k ∈ kl → k ∈ Ks
    i₄ : ∀ {k} → k ∈ L.map ix₀ kl → k ∈ Ks
    i₅ : ∀ {k} → k ∈ kb → k ∈ Ks
    i₆ : ∀ {k} → k ∈ L.map ix₀ kb → k ∈ Ks
    i₂ i = ∈-++⁺ʳ ko (∈-++⁺ˡ i)
    i₃ i = ∈-++⁺ʳ ko (∈-++⁺ʳ (L.map ix₀ ko) (∈-++⁺ˡ i))
    i₄ i = ∈-++⁺ʳ ko (∈-++⁺ʳ (L.map ix₀ ko) (∈-++⁺ʳ kl (∈-++⁺ˡ i)))
    i₅ i = ∈-++⁺ʳ ko (∈-++⁺ʳ (L.map ix₀ ko) (∈-++⁺ʳ kl (∈-++⁺ʳ (L.map ix₀ kl) (∈-++⁺ˡ i))))
    i₆ i = ∈-++⁺ʳ ko (∈-++⁺ʳ (L.map ix₀ ko) (∈-++⁺ʳ kl (∈-++⁺ʳ (L.map ix₀ kl) (∈-++⁺ʳ kb i))))

    go : ∀ {k e} → Joining.JoinT Lane o Bg Over Runs Cut Hand k e → k ≺ v → k ∈ Ks
    go (Joining.val {q} x) lt               = i₂ (∈-map⁺ ix₀ (ho x (dn {q} lt)))
    go (Joining.step x) lt                  = ∈-++⁺ˡ (ho x lt)
    go (Joining.opin x) lt                  = ∈-++⁺ˡ (ho x lt)
    go (Joining.oend x _) lt                = ∈-++⁺ˡ (ho x lt)
    go (Joining.opass x _) lt               = ∈-++⁺ˡ (ho x lt)
    go (Joining.lane x _ l _ _) lt          = i₃ (hl x l lt)
    go (Joining.lend x _ l _ _ _) lt        = i₃ (hl x l lt)
    go (Joining.lpass x _ l _ _ _) lt       = i₃ (hl x l lt)
    go (Joining.hand {c = c} x _ l _ _) lt  = i₄ (∈-map⁺ ix₀ (hl x l (dn {c} lt)))
    go (Joining.left x _ l _ _) lt          = i₃ (hl x l lt)
    go (Joining.run b _) lt                 = i₅ (hb b lt)
    go (Joining.rend b _ _) lt              = i₅ (hb b lt)
    go (Joining.rpass b _ _) lt             = i₅ (hb b lt)
    go (Joining.rhand {c} b _) lt           = i₆ (∈-map⁺ ix₀ (hb b (dn {c} lt)))

-- A connect's: its body's, when its source's rows lie past `v`.
conn-few : ∀ {A B} p (σ : EmissionSet A) (β : EmissionSet B) {v} → (∀ {k e} → σ k e → v ≺ k) → Few β v → Few (Connecting.ConnT p σ β) v
conn-few p σ β {v} past (ks , h) = ks , go
  where
    no : ∀ {k e} → σ k e → (k ⊕ [ ix 0 ]) ≺ v → ∀ {z} → z ∈ ks
    no {k} x lt = ⊥-elim (≺-absurd {v} {k} (past x) (≺-trans {k} {k ⊕ [ ix 0 ]} {v} (≺-ext k []) lt))

    go : ∀ {k e} → Connecting.ConnT p σ β k e → k ≺ v → k ∈ ks
    go (Connecting.body b) lt         = h b lt
    go (Connecting.burst x _) lt      = no x lt
    go (Connecting.echo x _ _ _) lt   = no x lt
    go (Connecting.kept x _ _ _) lt   = no x lt

-- A scan's: its input's.
acc-row : ∀ {A B} {f : B → A → B} {z : B} {t : EmissionSet A} {q b} → Scan.Acc f z t q b → Σ A λ a → t q (out a)
acc-row (Scan.acc₀ x _)    = _ , x
acc-row (Scan.acc _ x _ _) = _ , x

scan-few : ∀ {A B} (f : B → A → B) (z : B) (t : EmissionSet A) {v} → Few t v → Few (Scan.ScanT f z t) v
scan-few f z t {v} (ks , h) = ks , go
  where
    go : ∀ {k e} → Scan.ScanT f z t k e → k ≺ v → k ∈ ks
    go (Scan.sval a) lt  = h (proj₂ (acc-row a)) lt
    go (Scan.sstep x) lt = h x lt
    go (Scan.spin x) lt  = h x lt
    go (Scan.send x) lt  = h x lt

-- A takeWhile's: its input's, and their first and last children.
take-few : ∀ {A} incl (keep : A → Bool) (t : EmissionSet A) {v} → Few t v → Few (TakeWhile.TakeT incl keep t) v
take-few incl keep t {v} (ks , h) = Ks , go
  where
    Ks : List Pos
    Ks = ks ++ (L.map (λ k → k ⊕ [ ix 0 ]) ks ++ L.map (λ k → k ⊕ [ last ]) ks)

    go : ∀ {k e} → TakeWhile.TakeT incl keep t k e → k ≺ v → k ∈ Ks
    go (TakeWhile.pass x _ _) lt       = ∈-++⁺ˡ (h x lt)
    go (TakeWhile.fail {q} x _ _ _) lt = ∈-++⁺ʳ ks (∈-++⁺ˡ (∈-map⁺ (λ k → k ⊕ [ ix 0 ]) (h x (≺-trans {q} {q ⊕ [ ix 0 ]} {v} (≺-ext q []) lt))))
    go (TakeWhile.stop {q} x _ _) lt   = ∈-++⁺ʳ ks (∈-++⁺ʳ (L.map (λ k → k ⊕ [ ix 0 ]) ks) (∈-map⁺ (λ k → k ⊕ [ last ]) (h x (≺-trans {q} {q ⊕ [ last ]} {v} (≺-ext q []) lt))))
    go (TakeWhile.step x _) lt         = ∈-++⁺ˡ (h x lt)
    go (TakeWhile.tend x _) lt         = ∈-++⁺ˡ (h x lt)
    go (TakeWhile.left x _ _) lt       = ∈-++⁺ˡ (h x lt)
