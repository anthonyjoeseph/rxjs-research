{-# OPTIONS --guardedness #-}

-- A LANE SHOWS ITS `laneStart` (`lane-start-row`), and its `laneDone`
-- FOLLOWS IT, both past its subscription (`lane-starts`).  Read down, the
-- `laneDone` is the lane part's: its frame's second or third piece,
-- scheduled after the first, whose mark is the `laneStart`.  Read back up,
-- that mark is a row of every layer, each with few rows before it: its
-- frame's first value and step, the scan's one-value split, and nothing of
-- the share, whose rows all lie past it.
module simultaneous.LaneStart where

open import Data.Bool using (Bool; true; false; T; not; if_then_else_)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _<_; s≤s; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; mergeᶠ; empty; of; flatMap)
open import denotation.Position using (Pos; Label; ix; last; root; _≟ᵖ_; _⊕_)
open import denotation.Events using (Timeline; fresh; ofᴱ; <ᵖ-part; ix-<)
open import denotation.EmissionSet using (EmissionSet; Den; DenEnv; hot; enter; out; Proper; InE; at-out; on-out; at-end; _≺_; _≼_; Few; Truncate; LaneOf;
  module Op; module Joining; module Values; module Bounded; module Merge; module Scan;
  module TakeWhile; module Connecting)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans; ≼-refl; ≺→≼; ≺-irrefl; ≺-absurd)
open import denotation.Laws.Worlds using (⊕-assoc; ⊕-identityʳ; notT)
open import denotation.Laws.Worlds.Leaves using (of-reach; of-idx)
open import denotation.Laws.Cut using (ix-asc)
open import denotation.Laws.Count using (reach-down)
open import denotation.Laws.Shows using (few-reach)
open import simultaneous.HeldComb using (ev)
open import simultaneous.DenRows using (conn-out; merge-out; scan-out; bounded-out; hot-out; each-one; of-mem)
open import simultaneous.LaneEndSched using (ls-one; ls-true; of-one)
open import simultaneous.SObs using (lone; Part; lanePart; burstPart; module Elaborate)
open import simultaneous.InstEmit using (instEmit; mark; laneStart; laneDone; value; begin; over; stop; outerOpen; outerClose; carry; burstEnd; outerDone; subscribed; completed)

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
done-of : ∀ {B} (a : IE B) → T (not (undone a)) → Σ Pos λ n → a ≡ instEmit (mark laneDone) n
done-of (instEmit (mark laneDone) n) _  = n , refl
done-of (instEmit (value _) _)      ()
done-of (instEmit (mark begin) _)      ()
done-of (instEmit (mark over) _)       ()
done-of (instEmit (mark stop) _)       ()
done-of (instEmit (mark subscribed) _) ()
done-of (instEmit (mark completed) _)  ()
done-of (instEmit (mark outerOpen) _)  ()
done-of (instEmit (mark outerClose) _) ()
done-of (instEmit (mark laneStart) _)  ()
done-of (instEmit (mark carry) _)      ()
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

------------------------------------------------------------------------
-- The lane, as layers of operators over its children

z₀ : ∀ {B} → Routes × (List (IE B) × List (IE B))
z₀ = (root , 0) , ([] , [])

-- A lane's lane part, subscribed under its first value.
laneAt : Pos → Pos
laneAt s = (s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]

module Core {B : Set} (SH : Part → Den ⊤ → Den (IE B)) (PC : Part → ℕ → Den ⊤ → Den (IE B) → Den (IE B))
  -- The lane part's first piece shows its mark at its first child,
  (pc0    : ∀ h h′ s → enter (PC lanePart 0 h h′) s (s ⊕ [ ix 0 ]) (out (marked laneStart)))
  -- and either part's shows only there, and ends no lane.
  (pc0-at : ∀ k h h′ s {y a} → enter (PC k 0 h h′) s y (out a) → y ≡ s ⊕ [ ix 0 ] × T (undone a))
  -- The second piece reads the share.
  (pc1    : ∀ k h h′ s {y a} → enter (PC k 1 h h′) s y (out a) → enter h′ s y (out a))
  -- The burst part's third piece shows nothing,
  (pc2    : ∀ h h′ s {y a} → enter (PC burstPart 2 h h′) s y (out a) → ⊥)
  -- nor does its share.
  (sh-b   : ∀ h p {y a} → enter (SH burstPart h) p y (out a) → ⊥)
  -- The burst part's first piece shows no `laneStart`, nor the lane part's third.
  (pc0-b  : ∀ h h′ s {y n} → enter (PC burstPart 0 h h′) s y (out (instEmit (mark laneStart) n)) → ⊥)
  (pc2-l  : ∀ h h′ s {y n} → enter (PC lanePart 2 h h′) s y (out (instEmit (mark laneStart) n)) → ⊥)
  -- Either part's first piece's rows are its mark and its end, the lane
  -- part's mark its `laneStart`.
  (pc0-rows : ∀ k h h′ s {y e} → enter (PC k 0 h h′) s y e → y ≡ s ⊕ [ ix 0 ] ⊎ y ≡ s ⊕ [ last ])
  (pc0-ls   : ∀ h h′ s {y a} → enter (PC lanePart 0 h h′) s y (out a) → a ≡ marked laneStart)
  (pc0-be   : ∀ h h′ s {y a} → enter (PC burstPart 0 h h′) s y (out a) → a ≡ marked burstEnd)
  -- A share's rows lie past its subscription.
  (sh-past  : ∀ k h p {y e} → enter (SH k h) p y e → p ≺ y) where

  ls : IE B
  ls = marked laneStart

  Inner : Routes × (List (IE B) × List (IE B)) → Den (IE B)
  Inner y = Op.flatMap (mergeᶠ nothing) (λ b → Op.of (if b then proj₁ (proj₂ y) else proj₂ (proj₂ y))) (Op.of (true ∷ false ∷ []))

  Fr : Part → Den ⊤ → Den (IE B) → Den (IE B)
  Fr k h h′ = Op.flatMap (mergeᶠ (just 1)) (λ j → PC k j h h′) (Op.of (0 ∷ 1 ∷ 2 ∷ []))

  Sc : Part → Den ⊤ → Den (IE B) → Den (Routes × (List (IE B) × List (IE B)))
  Sc k h h′ = Op.scan laneStep z₀ (Fr k h h′)

  Ct : Part → Den ⊤ → Den (IE B) → Den (IE B)
  Ct k h h′ = Op.flatMap (mergeᶠ nothing) Inner (Sc k h h′)

  Sv : Part → Den (IE B)
  Sv k = Op.connect Op.empty (λ h → Op.connect (SH k h) (λ h′ → Ct k h h′))

  MM : Den (IE B)
  MM = Op.flatMap (mergeᶠ nothing) Sv (Op.of (lanePart ∷ burstPart ∷ []))

  LaneD : Den (IE B)
  LaneD = Op.takeWhile true undone MM

  -- A part's lane, its connect at `P`.
  H₁ : Pos → Den ⊤
  H₁ P = hot (Proper (enter (Op.empty {⊤}) (P ⊕ [ ix 1 ])))

  H₂ : Pos → Part → Den (IE B)
  H₂ P k = hot (Proper (enter (SH k (H₁ P)) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ])))

  Bp : Pos → Pos
  Bp P = (P ⊕ [ ix 0 ]) ⊕ [ ix 0 ]

  mid-out : ∀ k P {y a} → enter (Sv k) P y (out a) → enter (Op.connect (SH k (H₁ P)) (λ h′ → Ct k (H₁ P) h′)) (P ⊕ [ ix 0 ]) y (out a)
  mid-out k P r = conn-out Op.empty (λ h → Op.connect (SH k h) (λ h′ → Ct k h h′)) P r

  sv-out : ∀ k P {y a} → enter (Sv k) P y (out a) → enter (Ct k (H₁ P) (H₂ P k)) (Bp P) y (out a)
  sv-out k P r = conn-out (SH k (H₁ P)) (λ h′ → Ct k (H₁ P) h′) (P ⊕ [ ix 0 ]) (mid-out k P r)

  ----------------------------------------------------------------------
  -- The frame's schedule

  module Frame (k : Part) (h : Den ⊤) (h′ : Den (IE B)) (P : Pos) where
    O : EmissionSet ℕ
    O = enter (Op.of (0 ∷ 1 ∷ 2 ∷ [])) P

    f : ℕ → Den (IE B)
    f j = PC k j h h′

    module Bd = Bounded 1 f O
    open Values O using (Nth)

    ob₀ : O (P ⊕ [ ix 0 ]) (out 0)
    ob₀ = at-out , of-reach P 0 (0 ∷ 1 ∷ 2 ∷ []) {P ⊕ [ ix 0 ]} {out 0}

    ob-min : ∀ {q b} → O q (out b) → (P ⊕ [ ix 0 ]) ≼ q
    ob-min (at-out , _)                         = ≼-refl {P ⊕ [ ix 0 ]}
    ob-min (on-out at-out , _)                  = ≺→≼ {P ⊕ [ ix 0 ]} {P ⊕ [ ix 1 ]} (ix-asc P (s≤s z≤n))
    ob-min (on-out (on-out at-out) , _)         = ≺→≼ {P ⊕ [ ix 0 ]} {P ⊕ [ ix 2 ]} (ix-asc P (s≤s z≤n))
    ob-min (on-out (on-out (on-out ())) , _)

    nth₀ : Nth 0 (P ⊕ [ ix 0 ]) 0
    nth₀ = Values.first ob₀ ob-min

    S₀ : Pos
    S₀ = (P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]

    sb₀ : Bd.Sub 0 (P ⊕ [ ix 0 ]) S₀ 0
    sb₀ = nth₀ , Bd.room (s≤s z≤n)

    -- No value precedes the first.
    nth-o : ∀ {i q a} → Nth i q a → O q (out a)
    nth-o (Values.first x _)    = x
    nth-o (Values.next _ x _ _) = x

    before-0 : ∀ {q a} → O q (out a) → q ≺ (P ⊕ [ ix 0 ]) → ⊥
    before-0 (at-out , _)                 lt = ≺-irrefl {P ⊕ [ ix 0 ]} lt
    before-0 (on-out at-out , _)          lt = ≺-absurd {P ⊕ [ ix 1 ]} {P ⊕ [ ix 0 ]} lt (ix-asc P (s≤s z≤n))
    before-0 (on-out (on-out at-out) , _) lt = ≺-absurd {P ⊕ [ ix 2 ]} {P ⊕ [ ix 0 ]} lt (ix-asc P (s≤s z≤n))
    before-0 (on-out (on-out (on-out ())) , _) _

    nth-zero : ∀ {i a} → Nth i (P ⊕ [ ix 0 ]) a → i ≡ 0
    nth-zero (Values.first _ _)       = refl
    nth-zero (Values.next n _ lt _)   = ⊥-elim (before-0 (nth-o n) lt)

    -- The first lane starts at its value's second child.
    starts-0 : ∀ {s} → Bd.Starts 0 (P ⊕ [ ix 0 ]) [] s → s ≡ S₀
    starts-0 (Bd.room _)        = refl
    starts-0 (Bd.freed () _)
    starts-0 (Bd.queued () _ _ _ _)

    -- The first piece's mark, a row of the frame,
    V₀ : Pos
    V₀ = S₀ ⊕ [ ix 0 ]

    u-V₀ : Under (P ⊕ [ ix 0 ]) V₀
    u-V₀ = under-⊕ (under-⊕ (under-refl (P ⊕ [ ix 0 ])) (ix 1)) (ix 0)

    fr₀ : k ≡ lanePart → Bd.JoinT V₀ (out ls)
    fr₀ refl = Joining.lane ob₀ (0 , 0 , nth₀) (0 , S₀ , sb₀ , (pc0 h h′ S₀ , ≺-ext S₀ [])) (λ ()) tt

    -- precedes every other.
    fr-min : ∀ {y b} → enter (Fr k h h′) P y (out b) → V₀ ≼ y
    fr-min r with bounded-out 1 f (Op.of (0 ∷ 1 ∷ 2 ∷ [])) P r
    ... | q , j , i , s , oq , sb , (l , sl) = go oq sb l sl
      where
        go : ∀ {q j i s y b} → O q (out j) → Bd.Sub i q s j → enter (f j) s y (out b) → s ≺ y → V₀ ≼ y
        go {i = i} {s} {y} (at-out , _) (nth , st) l _ with nth-zero nth
        ... | refl with starts-0 st
        ...   | refl with pc0-at k h h′ S₀ l
        ...     | refl , _ = ≼-refl {V₀}
        go {s = s} {y} (on-out at-out , _) (_ , st) _ sl =
          ≺→≼ {V₀} {y} (≺-trans {V₀} {P ⊕ [ ix 1 ]} {y} (under-≺ P (s≤s z≤n) u-V₀) (≺-trans {P ⊕ [ ix 1 ]} {s} {y} (starts-after st) sl))
        go {s = s} {y} (on-out (on-out at-out) , _) (_ , st) _ sl =
          ≺→≼ {V₀} {y} (≺-trans {V₀} {P ⊕ [ ix 2 ]} {y} (under-≺ P (s≤s z≤n) u-V₀) (≺-trans {P ⊕ [ ix 2 ]} {s} {y} (starts-after st) sl))
        go (on-out (on-out (on-out ())) , _) _ _ _

    -- Below the first piece's mark, the frame's rows are its first value,
    -- that value's step, and the mark.
    o-few : ∀ {v} → Under V₀ v → Few O v
    o-few {v} uv = [ P ⊕ [ ix 0 ] ] , go
      where
        u : Under (P ⊕ [ ix 0 ]) v
        u = under-trans u-V₀ uv

        go : ∀ {y e} → O y e → y ≺ v → y ∈ [ P ⊕ [ ix 0 ] ]
        go (at-out , _) _                                = here refl
        go (on-out at-out , _) lt                        = ⊥-elim (≺-absurd {v} {P ⊕ [ ix 1 ]} (under-≺ P (s≤s z≤n) u) lt)
        go (on-out (on-out at-out) , _) lt               = ⊥-elim (≺-absurd {v} {P ⊕ [ ix 2 ]} (under-≺ P (s≤s z≤n) u) lt)
        go (on-out (on-out (on-out at-end)) , _) lt      = ⊥-elim (≺-absurd {v} {P ⊕ [ last ]} (under-last P u) lt)

    l-few : ∀ {v} → Under V₀ v → ∀ {q j y e} → O q (out j) → Bd.Lane q j y e → y ≺ v → y ∈ [ V₀ ]
    l-few {v} uv (at-out , _) (_ , _ , (nth , st) , (l , _)) lt with nth-zero nth
    ... | refl with starts-0 st
    ...   | refl with pc0-rows k h h′ S₀ l
    ...     | inj₁ refl = here refl
    ...     | inj₂ refl = ⊥-elim (≺-absurd {v} {S₀ ⊕ [ last ]} (under-last S₀ uv) lt)
    l-few {v} uv {y = y} (on-out at-out , _) (_ , s , (_ , st) , (_ , sl)) lt =
      ⊥-elim (≺-absurd {v} {P ⊕ [ ix 1 ]} (under-≺ P (s≤s z≤n) (under-trans u-V₀ uv)) (≺-trans {P ⊕ [ ix 1 ]} {s} {v} (starts-after st) (≺-trans {s} {y} {v} sl lt)))
    l-few {v} uv {y = y} (on-out (on-out at-out) , _) (_ , s , (_ , st) , (_ , sl)) lt =
      ⊥-elim (≺-absurd {v} {P ⊕ [ ix 2 ]} (under-≺ P (s≤s z≤n) (under-trans u-V₀ uv)) (≺-trans {P ⊕ [ ix 2 ]} {s} {v} (starts-after st) (≺-trans {s} {y} {v} sl lt)))
    l-few uv (on-out (on-out (on-out ())) , _) _ _

    fr-few : ∀ {v} → Under V₀ v → Few Bd.JoinT v
    fr-few uv = join-few (o-few uv) ([ V₀ ] , l-few uv) ([] , λ ())

    -- The frame's only value below its first mark is the mark,
    fr-out-at : ∀ {v y b} → Under V₀ v → enter (Fr k h h′) P y (out b) → y ≺ v → y ≡ V₀
    fr-out-at {v} uv r with bounded-out 1 f (Op.of (0 ∷ 1 ∷ 2 ∷ [])) P r
    ... | _ , _ , _ , _ , oq , sb , (l , sl) = go oq sb l sl
      where
        go : ∀ {q j i s y b} → O q (out j) → Bd.Sub i q s j → enter (f j) s y (out b) → s ≺ y → y ≺ v → y ≡ V₀
        go (at-out , _) (nth , st) l _ _ with nth-zero nth
        ... | refl with starts-0 st
        ...   | refl = proj₁ (pc0-at k h h′ S₀ l)
        go {s = s} {y} (on-out at-out , _) (_ , st) _ sl lt =
          ⊥-elim (≺-absurd {v} {P ⊕ [ ix 1 ]} (under-≺ P (s≤s z≤n) (under-trans u-V₀ uv)) (≺-trans {P ⊕ [ ix 1 ]} {s} {v} (starts-after st) (≺-trans {s} {y} {v} sl lt)))
        go {s = s} {y} (on-out (on-out at-out) , _) (_ , st) _ sl lt =
          ⊥-elim (≺-absurd {v} {P ⊕ [ ix 2 ]} (under-≺ P (s≤s z≤n) (under-trans u-V₀ uv)) (≺-trans {P ⊕ [ ix 2 ]} {s} {v} (starts-after st) (≺-trans {s} {y} {v} sl lt)))
        go (on-out (on-out (on-out ())) , _) _ _ _ _

    -- the lane part's `laneStart`,
    fr-val : k ≡ lanePart → ∀ {a} → enter (Fr k h h′) P V₀ (out a) → a ≡ marked laneStart
    fr-val refl r with bounded-out 1 f (Op.of (0 ∷ 1 ∷ 2 ∷ [])) P r
    ... | _ , _ , _ , _ , oq , sb , (l , sl) = go oq sb l sl
      where
        go : ∀ {q j i s a} → O q (out j) → Bd.Sub i q s j → enter (f j) s V₀ (out a) → s ≺ V₀ → a ≡ marked laneStart
        go (at-out , _) (nth , st) l _ with nth-zero nth
        ... | refl with starts-0 st
        ...   | refl = pc0-ls h h′ S₀ l
        go {s = s} (on-out at-out , _) (_ , st) _ sl =
          ⊥-elim (≺-absurd {V₀} {P ⊕ [ ix 1 ]} (under-≺ P (s≤s z≤n) u-V₀) (≺-trans {P ⊕ [ ix 1 ]} {s} {V₀} (starts-after st) sl))
        go {s = s} (on-out (on-out at-out) , _) (_ , st) _ sl =
          ⊥-elim (≺-absurd {V₀} {P ⊕ [ ix 2 ]} (under-≺ P (s≤s z≤n) u-V₀) (≺-trans {P ⊕ [ ix 2 ]} {s} {V₀} (starts-after st) sl))
        go (on-out (on-out (on-out ())) , _) _ _ _

    -- so the scan's fold there is its first step.
    sc-val : k ≡ lanePart → ∀ {b} → Scan.Acc laneStep z₀ (enter (Fr k h h′) P) V₀ b → b ≡ laneStep z₀ (marked laneStart)
    sc-val e (Scan.acc₀ x _)   = cong (laneStep z₀) (fr-val e x)
    sc-val e (Scan.acc a _ lt _) = ⊥-elim (fr-min (proj₂ (acc-row a)) lt)

    -- What ends a lane in the frame is the lane part's second or third
    -- piece, past every position below the first value.
    fr-done : ∀ {y n} → enter (Fr k h h′) P y (out (instEmit (mark laneDone) n))
            → (k ≡ burstPart → (∀ {p y a} → enter h′ p y (out a) → ⊥)) → k ≡ lanePart × (∀ {u} → Under (P ⊕ [ ix 0 ]) u → u ≺ y)
    fr-done r hb with bounded-out 1 f (Op.of (0 ∷ 1 ∷ 2 ∷ [])) P r
    ... | q , j , i , s , oq , sb , (l , sl) = go k refl oq sb l sl
      where
        go : ∀ k′ → k′ ≡ k → ∀ {q j i s y n} → O q (out j) → Bd.Sub i q s j → enter (f j) s y (out (instEmit (mark laneDone) n)) → s ≺ y
           → k ≡ lanePart × (∀ {u} → Under (P ⊕ [ ix 0 ]) u → u ≺ y)
        go _ _ {s = s} (at-out , _) _ l _ = ⊥-elim (proj₂ (pc0-at k h h′ s l))
        go lanePart refl {s = s} {y} (on-out at-out , _) (_ , st) _ sl =
          refl , λ {u} un → ≺-trans {u} {P ⊕ [ ix 1 ]} {y} (under-≺ P {0} {1} {u} (s≤s z≤n) un) (≺-trans {P ⊕ [ ix 1 ]} {s} {y} (starts-after st) sl)
        go burstPart refl {s = s} (on-out at-out , _) _ l _ = ⊥-elim (hb refl (pc1 burstPart h h′ s l))
        go lanePart refl {s = s} {y} (on-out (on-out at-out) , _) (_ , st) _ sl =
          refl , λ {u} un → ≺-trans {u} {P ⊕ [ ix 2 ]} {y} (under-≺ P {0} {2} {u} (s≤s z≤n) un) (≺-trans {P ⊕ [ ix 2 ]} {s} {y} (starts-after st) sl)
        go burstPart refl {s = s} (on-out (on-out at-out) , _) _ l _ = ⊥-elim (pc2 h h′ s l)
        go _ _ (on-out (on-out (on-out ())) , _) _ _ _

    -- What shows `laneStart` in the frame is the lane part's first piece's
    -- mark, when the share shows none.
    fr-start : ∀ {y n} → enter (Fr k h h′) P y (out (instEmit (mark laneStart) n)) → (∀ {p y n} → enter h′ p y (out (instEmit (mark laneStart) n)) → ⊥)
             → k ≡ lanePart × y ≡ V₀
    fr-start r hn with bounded-out 1 f (Op.of (0 ∷ 1 ∷ 2 ∷ [])) P r
    ... | q , j , i , s , oq , sb , (l , _) = go k refl oq sb l
      where
        go : ∀ k′ → k′ ≡ k → ∀ {q j i s y n} → O q (out j) → Bd.Sub i q s j → enter (f j) s y (out (instEmit (mark laneStart) n)) → k ≡ lanePart × y ≡ V₀
        go lanePart refl (at-out , _) (nth , st) l with nth-zero nth
        ... | refl with starts-0 st
        ...   | refl with pc0-at k h h′ S₀ l
        ...     | refl , _ = refl , refl
        go burstPart refl {s = s} (at-out , _) _ l = ⊥-elim (pc0-b h h′ s l)
        go _ _ {s = s} (on-out at-out , _) _ l = ⊥-elim (hn (pc1 k h h′ s l))
        go lanePart refl {s = s} (on-out (on-out at-out) , _) _ l = ⊥-elim (pc2-l h h′ s l)
        go burstPart refl {s = s} (on-out (on-out at-out) , _) _ l = ⊥-elim (pc2 h h′ s l)
        go _ _ (on-out (on-out (on-out ())) , _) _ _

    -- What shows a `begin` in the frame is the lane part's second or third
    -- piece, past every position below the first value.
    fr-begin : ∀ {y n} → enter (Fr k h h′) P y (out (instEmit (mark begin) n))
             → (k ≡ burstPart → (∀ {p y a} → enter h′ p y (out a) → ⊥)) → k ≡ lanePart × (∀ {u} → Under (P ⊕ [ ix 0 ]) u → u ≺ y)
    fr-begin r hb with bounded-out 1 f (Op.of (0 ∷ 1 ∷ 2 ∷ [])) P r
    ... | q , j , i , s , oq , sb , (l , sl) = go k refl oq sb l sl
      where
        go : ∀ k′ → k′ ≡ k → ∀ {q j i s y n} → O q (out j) → Bd.Sub i q s j → enter (f j) s y (out (instEmit (mark begin) n)) → s ≺ y
           → k ≡ lanePart × (∀ {u} → Under (P ⊕ [ ix 0 ]) u → u ≺ y)
        go lanePart refl {s = s} (at-out , _) _ l _ with pc0-ls h h′ s l
        ... | ()
        go burstPart refl {s = s} (at-out , _) _ l _ with pc0-be h h′ s l
        ... | ()
        go lanePart refl {s = s} {y} (on-out at-out , _) (_ , st) _ sl =
          refl , λ {u} un → ≺-trans {u} {P ⊕ [ ix 1 ]} {y} (under-≺ P {0} {1} {u} (s≤s z≤n) un) (≺-trans {P ⊕ [ ix 1 ]} {s} {y} (starts-after st) sl)
        go burstPart refl {s = s} (on-out at-out , _) _ l _ = ⊥-elim (hb refl (pc1 burstPart h h′ s l))
        go lanePart refl {s = s} {y} (on-out (on-out at-out) , _) (_ , st) _ sl =
          refl , λ {u} un → ≺-trans {u} {P ⊕ [ ix 2 ]} {y} (under-≺ P {0} {2} {u} (s≤s z≤n) un) (≺-trans {P ⊕ [ ix 2 ]} {s} {y} (starts-after st) sl)
        go burstPart refl {s = s} (on-out (on-out at-out) , _) _ l _ = ⊥-elim (pc2 h h′ s l)
        go _ _ (on-out (on-out (on-out ())) , _) _ _ _

  ----------------------------------------------------------------------
  -- The scan's split

  -- What the split shows that ends a lane is what the scan read.
  pick : ∀ (y : Routes × (List (IE B) × List (IE B))) st a₀ → y ≡ laneStep st a₀ → ∀ {U w c q a}
       → InE (ofᴱ U 0 (true ∷ false ∷ [])) w (out c)
       → InE (ofᴱ (w ⊕ [ ix 1 ]) 0 (if c then proj₁ (proj₂ y) else proj₂ (proj₂ y))) q (out a) → T (not (undone a)) → a ≡ a₀
  pick _ st a₀ refl at-out l nu = ⊥-elim (notT _ nu (ls-true st a₀ (of-mem _ 0 _ l)))
  pick _ st a₀ refl (on-out at-out) l nu with of-one _ a₀ (subst (λ xs → InE (ofᴱ _ 0 xs) _ (out _)) (ls-one st a₀) l)
  ... | refl , refl = refl
  pick _ _ _ refl (on-out (on-out ())) _ _

  -- The split's first list holds no `laneStart`: carries, if anything.
  rep-no : ∀ k {n} → instEmit (mark laneStart) n ∈ L.replicate k (marked {B} carry) → ⊥
  rep-no (suc k) (here ())
  rep-no (suc k) (there i) = rep-no k i

  ls-no : ∀ (st : Routes × (List (IE B) × List (IE B))) e {n} → instEmit (mark laneStart) n ∈ proj₁ (proj₂ (laneStep st e)) → ⊥
  ls-no st (instEmit (value _) _)      ()
  ls-no st (instEmit (mark begin) _)      ()
  ls-no st (instEmit (mark over) _)       ()
  ls-no st (instEmit (mark stop) _)       ()
  ls-no st (instEmit (mark outerOpen) _)  ()
  ls-no st (instEmit (mark outerClose) _) ()
  ls-no st (instEmit (mark laneStart) _)  ()
  ls-no st (instEmit (mark carry) _)      ()
  ls-no st (instEmit (mark laneDone) _) i = rep-no (proj₂ (proj₁ st)) i
  ls-no st (instEmit (mark burstEnd) _)   ()
  ls-no st (instEmit (mark outerDone) _)  ()
  ls-no st (instEmit (mark subscribed) _) ()
  ls-no st (instEmit (mark completed) _)  ()

  -- The split of the first piece's mark, at `U`, shows it at its second
  -- lane's first child: one of few rows.
  module Split (U : Pos) where
    W₀ E₀ : Pos
    W₀ = U ⊕ [ ix 1 ]
    E₀ = (W₀ ⊕ [ ix 1 ]) ⊕ [ ix 0 ]

    ks : List Pos
    ks = ((U ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ∷ (W₀ ⊕ [ ix 0 ]) ∷ (U ⊕ [ last ]) ∷ (((U ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ last ])
       ∷ E₀ ∷ ((W₀ ⊕ [ ix 1 ]) ⊕ [ last ]) ∷ []

    Sp : EmissionSet (IE B)
    Sp = enter (Inner (laneStep z₀ ls)) U

    Raw : EmissionSet (IE B)
    Raw = Merge.JoinT (λ b → Op.of (if b then proj₁ (proj₂ (laneStep z₀ ls)) else proj₂ (proj₂ (laneStep z₀ ls)))) (enter (Op.of (true ∷ false ∷ [])) U)

    all-in : ∀ {y e} → Raw y e → y ∈ ks
    all-in (Joining.val (at-out , _))                                         = here refl
    all-in (Joining.val (on-out at-out , _))                                  = there (here refl)
    all-in (Joining.val (on-out (on-out ()) , _))
    all-in (Joining.step (on-out (on-out ()) , _))
    all-in (Joining.opin (on-out (on-out ()) , _))
    all-in (Joining.oend (on-out (on-out at-end) , _) _)                      = there (there (here refl))
    all-in (Joining.opass (on-out (on-out at-end) , _) _)                     = there (there (here refl))
    all-in (Joining.lane (at-out , _) _ ((at-end , _) , _) _ ())
    all-in (Joining.lane (on-out at-out , _) _ ((at-out , _) , _) _ _)        = there (there (there (there (here refl))))
    all-in (Joining.lane (on-out at-out , _) _ ((on-out at-end , _) , _) _ ())
    all-in (Joining.lane (on-out (on-out ()) , _) _ _ _ _)
    all-in (Joining.lend (at-out , _) _ ((at-end , _) , _) _ _ _)             = there (there (there (here refl)))
    all-in (Joining.lend (on-out at-out , _) _ ((on-out at-end , _) , _) _ _ _) = there (there (there (there (there (here refl)))))
    all-in (Joining.lend (on-out (on-out ()) , _) _ _ _ _ _)
    all-in (Joining.lpass (at-out , _) _ ((at-end , _) , _) _ _ _)            = there (there (there (here refl)))
    all-in (Joining.lpass (on-out at-out , _) _ ((on-out at-end , _) , _) _ _ _) = there (there (there (there (there (here refl)))))
    all-in (Joining.lpass (on-out (on-out ()) , _) _ _ _ _ _)
    all-in (Joining.hand _ _ _ _ ())
    all-in (Joining.left (at-out , _) _ ((() , _) , _) _ _)
    all-in (Joining.left (on-out at-out , _) _ ((on-out () , _) , _) _ _)
    all-in (Joining.left (on-out (on-out ()) , _) _ _ _ _)
    all-in (Joining.run () _)
    all-in (Joining.rend () _ _)
    all-in (Joining.rpass () _ _)
    all-in (Joining.rhand () _)

    row : Sp E₀ (out ls)
    row = Joining.lane (on-out at-out , of-reach U 0 (true ∷ false ∷ []) {W₀} {out false}) tt ((at-out , of-reach (W₀ ⊕ [ ix 1 ]) 0 (ls ∷ []) {E₀} {out ls}) , ≺-ext (W₀ ⊕ [ ix 1 ]) [])
            (λ ()) tt
        , ks , λ x _ _ → all-in x

  -- What the split shows as `laneStart` is the scan's read, at its second
  -- lane's first child.
  pick-at : ∀ (y : Routes × (List (IE B) × List (IE B))) st a₀ → y ≡ laneStep st a₀ → ∀ {U w c q n}
          → InE (ofᴱ U 0 (true ∷ false ∷ [])) w (out c)
          → InE (ofᴱ (w ⊕ [ ix 1 ]) 0 (if c then proj₁ (proj₂ y) else proj₂ (proj₂ y))) q (out (instEmit (mark laneStart) n))
          → a₀ ≡ instEmit (mark laneStart) n × q ≡ Split.E₀ U
  pick-at _ st a₀ refl at-out l = ⊥-elim (ls-no st a₀ (of-mem _ 0 _ l))
  pick-at _ st a₀ refl (on-out at-out) l with of-one _ a₀ (subst (λ xs → InE (ofᴱ _ 0 xs) _ (out _)) (ls-one st a₀) l)
  ... | refl , refl = refl , refl
  pick-at _ _ _ refl (on-out (on-out ())) _

  -- The split's first list holds no `begin` either,
  bg-rep : ∀ k {n} → instEmit (mark begin) n ∈ L.replicate k (marked {B} carry) → ⊥
  bg-rep (suc k) (here ())
  bg-rep (suc k) (there i) = bg-rep k i

  bg-no : ∀ (st : Routes × (List (IE B) × List (IE B))) e {n} → instEmit (mark begin) n ∈ proj₁ (proj₂ (laneStep st e)) → ⊥
  bg-no st (instEmit (value _) _)      ()
  bg-no st (instEmit (mark begin) _)      ()
  bg-no st (instEmit (mark over) _)       ()
  bg-no st (instEmit (mark stop) _)       ()
  bg-no st (instEmit (mark outerOpen) _)  ()
  bg-no st (instEmit (mark outerClose) _) ()
  bg-no st (instEmit (mark laneStart) _)  ()
  bg-no st (instEmit (mark carry) _)      ()
  bg-no st (instEmit (mark laneDone) _) i = bg-rep (proj₂ (proj₁ st)) i
  bg-no st (instEmit (mark burstEnd) _)   ()
  bg-no st (instEmit (mark outerDone) _)  ()
  bg-no st (instEmit (mark subscribed) _) ()
  bg-no st (instEmit (mark completed) _)  ()

  -- so a `begin` the split shows is the scan's read.
  pick-begin : ∀ (y : Routes × (List (IE B) × List (IE B))) st a₀ → y ≡ laneStep st a₀ → ∀ {U w c q n}
             → InE (ofᴱ U 0 (true ∷ false ∷ [])) w (out c)
             → InE (ofᴱ (w ⊕ [ ix 1 ]) 0 (if c then proj₁ (proj₂ y) else proj₂ (proj₂ y))) q (out (instEmit (mark begin) n))
             → a₀ ≡ instEmit (mark begin) n
  pick-begin _ st a₀ refl at-out l = ⊥-elim (bg-no st a₀ (of-mem _ 0 _ l))
  pick-begin _ st a₀ refl (on-out at-out) l with of-one _ a₀ (subst (λ xs → InE (ofᴱ _ 0 xs) _ (out _)) (ls-one st a₀) l)
  ... | _ , refl = refl
  pick-begin _ _ _ refl (on-out (on-out ())) _

  ----------------------------------------------------------------------
  -- Down, then up

  -- The `laneDone` a part's connect shows is the lane part's, past its
  -- frame's first piece.
  down : ∀ k P {e₂ n} → enter (Sv k) P e₂ (out (instEmit (mark laneDone) n))
       → k ≡ lanePart × Σ Pos λ v₂ → Σ _ λ yst → Σ _ λ a₂ → enter (Sc k (H₁ P) (H₂ P k)) (Bp P) v₂ (out yst)
         × enter (Fr k (H₁ P) (H₂ P k)) (Bp P) v₂ (out a₂) × (∀ {u} → Under (Bp P ⊕ [ ix 0 ]) u → u ≺ v₂) × v₂ ≺ e₂
  down k P {e₂} svr =
    let (v₂ , yst , scr , inr , lt₁) = merge-out Inner (Sc k (H₁ P) (H₂ P k)) (Bp P) (sv-out k P svr)
        (w , c , ow , ll , _) = merge-out (λ b → Op.of (if b then proj₁ (proj₂ yst) else proj₂ (proj₂ yst))) (Op.of (true ∷ false ∷ [])) (v₂ ⊕ [ ix 1 ]) inr
        (st , a₀ , fa , eq) = scan-out laneStep z₀ (Fr k (H₁ P) (H₂ P k)) (Bp P) scr
        ea = pick yst st a₀ eq (proj₁ ow) (proj₁ ll) tt
        (ek , vlt) = Frame.fr-done k (H₁ P) (H₂ P k) (Bp P) (subst (λ a → enter (Fr k (H₁ P) (H₂ P k)) (Bp P) v₂ (out a)) (sym ea) fa)
                       (λ { refl r → sh-b (H₁ P) _ (proj₁ (proj₁ (proj₂ (hot-out r)))) })
    in ek , v₂ , yst , a₀ , scr , fa , vlt , ≺-trans {v₂} {v₂ ⊕ [ ix 1 ]} {e₂} (≺-ext v₂ []) lt₁

  -- What a part's connect shows as `laneStart` is the lane part's split of
  -- its frame's first mark, when its share shows none.
  down-start : ∀ k P {y n} → enter (Sv k) P y (out (instEmit (mark laneStart) n)) → (∀ {p y n} → enter (H₂ P k) p y (out (instEmit (mark laneStart) n)) → ⊥)
             → k ≡ lanePart × y ≡ Split.E₀ (Frame.V₀ k (H₁ P) (H₂ P k) (Bp P) ⊕ [ ix 1 ])
  down-start k P svr hn =
    let (v₂ , yst , scr , inr , _) = merge-out Inner (Sc k (H₁ P) (H₂ P k)) (Bp P) (sv-out k P svr)
        (w , c , ow , ll , _) = merge-out (λ b → Op.of (if b then proj₁ (proj₂ yst) else proj₂ (proj₂ yst))) (Op.of (true ∷ false ∷ [])) (v₂ ⊕ [ ix 1 ]) inr
        (st , a₀ , fa , eq) = scan-out laneStep z₀ (Fr k (H₁ P) (H₂ P k)) (Bp P) scr
        (ea , ey) = pick-at yst st a₀ eq (proj₁ ow) (proj₁ ll)
        (ek , ev₂) = Frame.fr-start k (H₁ P) (H₂ P k) (Bp P) (subst (λ a → enter (Fr k (H₁ P) (H₂ P k)) (Bp P) v₂ (out a)) ea fa) hn
    in ek , trans ey (cong (λ v → Split.E₀ (v ⊕ [ ix 1 ])) ev₂)

  -- The `begin` a part's connect shows is the lane part's, past its
  -- frame's first piece.
  down-begin : ∀ k P {e₂ n} → enter (Sv k) P e₂ (out (instEmit (mark begin) n))
             → k ≡ lanePart × Σ Pos λ v₂ → (∀ {u} → Under (Bp P ⊕ [ ix 0 ]) u → u ≺ v₂) × v₂ ≺ e₂
  down-begin k P {e₂} svr =
    let (v₂ , yst , scr , inr , lt₁) = merge-out Inner (Sc k (H₁ P) (H₂ P k)) (Bp P) (sv-out k P svr)
        (w , c , ow , ll , _) = merge-out (λ b → Op.of (if b then proj₁ (proj₂ yst) else proj₂ (proj₂ yst))) (Op.of (true ∷ false ∷ [])) (v₂ ⊕ [ ix 1 ]) inr
        (st , a₀ , fa , eq) = scan-out laneStep z₀ (Fr k (H₁ P) (H₂ P k)) (Bp P) scr
        ea = pick-begin yst st a₀ eq (proj₁ ow) (proj₁ ll)
        (ek , vlt) = Frame.fr-begin k (H₁ P) (H₂ P k) (Bp P) (subst (λ a → enter (Fr k (H₁ P) (H₂ P k)) (Bp P) v₂ (out a)) ea fa)
                       (λ { refl r → sh-b (H₁ P) _ (proj₁ (proj₁ (proj₂ (hot-out r)))) })
    in ek , v₂ , vlt , ≺-trans {v₂} {v₂ ⊕ [ ix 1 ]} {e₂} (≺-ext v₂ []) lt₁

  h₂-no : ∀ P k → (∀ {y n} → enter (SH k (H₁ P)) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) y (out (instEmit (mark laneStart) n)) → ⊥)
        → ∀ {p y n} → enter (H₂ P k) p y (out (instEmit (mark laneStart) n)) → ⊥
  h₂-no P k hn r = hn (proj₁ (proj₁ (proj₂ (hot-out r))))

  -- Where a lane shows its `laneStart`.
  startAt : Pos → Pos
  startAt s = Split.E₀ (Frame.V₀ lanePart (H₁ (laneAt s)) (H₂ (laneAt s) lanePart) (Bp (laneAt s)) ⊕ [ ix 1 ])

  bl : burstPart ≡ lanePart → ⊥
  bl ()

  -- A LANE SHOWS `laneStart` AT ONE PLACE, when its lane part's share shows
  -- none.
  start-at : ∀ s → (∀ {y n} → enter (SH lanePart (H₁ (laneAt s))) ((laneAt s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) y (out (instEmit (mark laneStart) n)) → ⊥)
           → ∀ {y n} → enter LaneD s y (out (instEmit (mark laneStart) n)) → y ≡ startAt s
  start-at s hn (TakeWhile.pass r _ _ , _) = part (merge-out Sv (Op.of (lanePart ∷ burstPart ∷ [])) s r)
    where
      part : ∀ {y n} → (Σ Pos λ kq → Σ Part λ k → enter (Op.of (lanePart ∷ burstPart ∷ [])) s kq (out k)
               × enter (Sv k) (kq ⊕ [ ix 1 ]) y (out (instEmit (mark laneStart) n)) × (kq ⊕ [ ix 1 ]) ≺ y) → y ≡ startAt s
      part (_ , _ , (at-out , _) , svr , _) = proj₂ (down-start lanePart (laneAt s) svr (h₂-no (laneAt s) lanePart hn))
      part (_ , _ , (on-out at-out , _) , svr , _) = ⊥-elim (bl (proj₁ (down-start burstPart _ svr (h₂-no _ burstPart (sh-b _ _)))))
      part (_ , _ , (on-out (on-out ()) , _) , _ , _)
  start-at s hn (TakeWhile.fail _ () _ _ , _)


  -- The lane part's split of its first mark, a row of every layer of its
  -- connect: each layer's rows before it are few.
  module Up (P : Pos) where
    open Frame lanePart (H₁ P) (H₂ P lanePart) (Bp P) using (V₀; u-V₀; fr₀; fr-min; fr-few; fr-out-at; sc-val)
    open Split (V₀ ⊕ [ ix 1 ]) using (W₀; E₀; row; ks; all-in)

    Q : Pos
    Q = P ⊕ [ ix 0 ]

    FrE : EmissionSet (IE B)
    FrE = enter (Fr lanePart (H₁ P) (H₂ P lanePart)) (Bp P)

    ScE : EmissionSet (Routes × (List (IE B) × List (IE B)))
    ScE = enter (Sc lanePart (H₁ P) (H₂ P lanePart)) (Bp P)

    u-V₀E : Under V₀ E₀
    u-V₀E = under-⊕ (under-⊕ (under-⊕ (under-⊕ (under-refl V₀) (ix 1)) (ix 1)) (ix 1)) (ix 0)

    u-E₀ : Under (Bp P ⊕ [ ix 0 ]) E₀
    u-E₀ = under-trans u-V₀ u-V₀E

    u-Bp : Under (Bp P) E₀
    u-Bp = under-trans (under-⊕ (under-refl (Bp P)) (ix 0)) u-E₀

    u-P : Under (P ⊕ [ ix 0 ]) E₀
    u-P = under-trans (under-⊕ (under-refl Q) (ix 0)) u-Bp

    sc-few : ∀ {v} → Under V₀ v → Few (Scan.ScanT laneStep z₀ FrE) v
    sc-few uv = scan-few laneStep z₀ FrE (few-tr (fr-few uv))

    -- The split's lane is the only one below it.
    ct-few : Few (Merge.JoinT Inner ScE) E₀
    ct-few = join-few (few-tr (sc-few u-V₀E)) (ks , hl) ([] , λ ())
      where
        hl : ∀ {q y k e} → ScE q (out y) → LaneOf Inner q y k e → k ≺ E₀ → k ∈ ks
        hl {q} {y} {k} (Scan.sval a , _) (l , ql) lt with fr-out-at u-V₀E (proj₂ (acc-row a)) (≺-trans {q} {q ⊕ [ ix 1 ]} {E₀} (≺-ext q []) (≺-trans {q ⊕ [ ix 1 ]} {k} {E₀} ql lt))
        ... | refl with sc-val refl a
        ...   | refl = all-in (proj₁ l)

    -- The share lies past it, as does the empty source.
    in-few : Few (Connecting.ConnT Q (enter (SH lanePart (H₁ P)) (Q ⊕ [ ix 1 ])) (enter (Ct lanePart (H₁ P) (H₂ P lanePart)) (Bp P))) E₀
    in-few = conn-few Q (enter (SH lanePart (H₁ P)) (Q ⊕ [ ix 1 ])) (enter (Ct lanePart (H₁ P) (H₂ P lanePart)) (Bp P))
               (λ {y} x → ≺-trans {E₀} {Q ⊕ [ ix 1 ]} {y} (under-≺ Q (s≤s z≤n) u-Bp) (sh-past lanePart (H₁ P) (Q ⊕ [ ix 1 ]) x))
               (few-tr ct-few)

    sv-few : Few (Connecting.ConnT P (enter (Op.empty {⊤}) (P ⊕ [ ix 1 ])) (enter (Op.connect (SH lanePart (H₁ P)) (λ h′ → Ct lanePart (H₁ P) h′)) Q)) E₀
    sv-few = conn-few P (enter (Op.empty {⊤}) (P ⊕ [ ix 1 ])) (enter (Op.connect (SH lanePart (H₁ P)) (λ h′ → Ct lanePart (H₁ P) h′)) Q) past (few-tr in-few)
      where
        past : ∀ {y e} → enter Op.empty (P ⊕ [ ix 1 ]) y e → E₀ ≺ y
        past (at-end , _) = ≺-trans {E₀} {P ⊕ [ ix 1 ]} {(P ⊕ [ ix 1 ]) ⊕ [ last ]} (under-≺ P (s≤s z≤n) u-P) (≺-ext (P ⊕ [ ix 1 ]) [])

    sc-row : ScE V₀ (out (laneStep z₀ ls))
    sc-row = few-row (Scan.sval (Scan.acc₀ (few-row (fr₀ refl) (fr-few (under-refl V₀))) fr-min)) (sc-few (under-refl V₀))

    ct-row : enter (Ct lanePart (H₁ P) (H₂ P lanePart)) (Bp P) E₀ (out ls)
    ct-row = few-row (Joining.lane sc-row tt (row , under-ext (V₀ ⊕ [ ix 1 ]) (under-⊕ (under-⊕ (under-refl W₀) (ix 1)) (ix 0))) (λ ()) tt) ct-few

    sv-row : enter (Sv lanePart) P E₀ (out ls)
    sv-row = few-row (Connecting.body (few-row (Connecting.body ct-row) in-few)) sv-few

  -- A LANE SHOWS ITS `laneStart`, below its subscription's first child.
  start-row : ∀ s → enter LaneD s (startAt s) (out ls) × Under (s ⊕ [ ix 0 ]) (startAt s)
  start-row s = few-row (TakeWhile.pass mm-row tt nF) (take-few true undone (enter MM s) (few-tr mm-few)) , u-K
    where
      P : Pos
      P = laneAt s

      open Up P using (u-P; u-E₀; sv-few; sv-row)

      E₀ : Pos
      E₀ = startAt s

      K : Pos
      K = s ⊕ [ ix 0 ]

      u-K : Under K E₀
      u-K = under-trans (under-⊕ (under-⊕ (under-refl K) (ix 1)) (ix 0)) u-P

      OS : EmissionSet Part
      OS = enter (Op.of (lanePart ∷ burstPart ∷ [])) s

      o-few : Few OS E₀
      o-few = [ K ] , go
        where
          go : ∀ {k e} → OS k e → k ≺ E₀ → k ∈ [ K ]
          go (at-out , _) _                       = here refl
          go (on-out at-out , _) lt               = ⊥-elim (≺-absurd {E₀} {s ⊕ [ ix 1 ]} (under-≺ s (s≤s z≤n) u-K) lt)
          go (on-out (on-out at-end) , _) lt      = ⊥-elim (≺-absurd {E₀} {s ⊕ [ last ]} (under-last s u-K) lt)

      l-few : ∀ {q k y e} → OS q (out k) → LaneOf Sv q k y e → y ≺ E₀ → y ∈ proj₁ sv-few
      l-few (at-out , _) (l , _) lt = proj₂ sv-few (proj₁ l) lt
      l-few {y = y} (on-out at-out , _) (_ , ql) lt =
        ⊥-elim (≺-absurd {E₀} {s ⊕ [ ix 1 ]} (under-≺ s (s≤s z≤n) u-K)
          (≺-trans {s ⊕ [ ix 1 ]} {(s ⊕ [ ix 1 ]) ⊕ [ ix 1 ]} {E₀} (≺-ext (s ⊕ [ ix 1 ]) []) (≺-trans {(s ⊕ [ ix 1 ]) ⊕ [ ix 1 ]} {y} {E₀} ql lt)))
      l-few (on-out (on-out ()) , _) _ _

      mm-few : Few (Merge.JoinT Sv OS) E₀
      mm-few = join-few o-few (proj₁ sv-few , l-few) ([] , λ ())

      mm-row : enter MM s E₀ (out ls)
      mm-row = few-row (Joining.lane (at-out , of-reach s 0 (lanePart ∷ burstPart ∷ []) {K} {out lanePart}) tt
                 (sv-row , under-ext P u-P) (λ ()) tt) mm-few

      -- No `laneDone` comes before it.
      nF : ¬ TakeWhile.Failed true undone (enter MM s) E₀
      nF (q′ , a′ , x′ , nk′ , lt′) =
        let (n , ea) = done-of a′ nk′
        in late n (merge-out Sv (Op.of (lanePart ∷ burstPart ∷ [])) s (subst (λ a → enter MM s q′ (out a)) ea x′))
        where
          late : ∀ n → (Σ Pos λ kq → Σ Part λ k → OS kq (out k) × enter (Sv k) (kq ⊕ [ ix 1 ]) q′ (out (instEmit (mark laneDone) n)) × (kq ⊕ [ ix 1 ]) ≺ q′) → ⊥
          late n (_ , _ , (at-out , _) , svr , _) =
            let (_ , v₂ , _ , _ , _ , _ , vlt , v₂q) = down lanePart P svr
            in ≺-absurd {E₀} {q′} (≺-trans {E₀} {v₂} {q′} (vlt u-E₀) v₂q) lt′
          late n (_ , _ , (on-out at-out , _) , svr , _) = bl (proj₁ (down burstPart _ svr))
          late n (_ , _ , (on-out (on-out ()) , _) , _ , _)

  -- A LANE'S `begin` FOLLOWS ITS OWN `laneStart`, both past its
  -- subscription.
  core-begin : ∀ s {y n} → enter LaneD s y (out (instEmit (mark begin) n))
             → Σ Pos λ y₀ → enter LaneD s y₀ (out ls) × s ≺ y₀ × y₀ ≺ y
  core-begin s (TakeWhile.fail _ () _ _ , _)
  core-begin s {y} {n} x@(TakeWhile.pass r _ nF , _) = part (merge-out Sv (Op.of (lanePart ∷ burstPart ∷ [])) s r)
    where
    part : (Σ Pos λ kq → Σ Part λ k → enter (Op.of (lanePart ∷ burstPart ∷ [])) s kq (out k)
             × enter (Sv k) (kq ⊕ [ ix 1 ]) y (out (instEmit (mark begin) n)) × (kq ⊕ [ ix 1 ]) ≺ y)
         → Σ Pos λ y₀ → enter LaneD s y₀ (out ls) × s ≺ y₀ × y₀ ≺ y
    part (kq , k , okq , svr , _) with down-begin k (kq ⊕ [ ix 1 ]) svr
    ... | refl , v₂ , vlt , v₂y = E₀ , take₀ , s-E₀ , lt₀
     where
      P : Pos
      P = kq ⊕ [ ix 1 ]
      open Up P using (u-E₀; u-P; sv-row)
      open Split (Frame.V₀ lanePart (H₁ P) (H₂ P lanePart) (Bp P) ⊕ [ ix 1 ]) using (E₀)

      lt₀ : E₀ ≺ y
      lt₀ = ≺-trans {E₀} {v₂} {y} (vlt u-E₀) v₂y

      P-E₀ : P ≺ E₀
      P-E₀ = under-ext P u-P

      s-E₀ : s ≺ E₀
      s-E₀ = ≺-trans {s} {kq} {E₀} (of-after s (lanePart ∷ burstPart ∷ []) okq) (under-ext kq (under-trans (under-⊕ (under-refl P) (ix 0)) u-P))

      mm₀ : enter MM s E₀ (out ls)
      mm₀ = Joining.lane okq tt (sv-row , P-E₀) (λ ()) tt , reach-down {q = y} {w = E₀} {e = out (instEmit (mark begin) n)} {e₁ = out ls} (proj₂ r) lt₀ tt

      nF₀ : ¬ TakeWhile.Failed true undone (enter MM s) E₀
      nF₀ (q′ , a′ , x′ , nk′ , lt′) = nF (q′ , a′ , x′ , nk′ , ≺-trans {q′} {E₀} {y} lt′ lt₀)

      take₀ : enter LaneD s E₀ (out ls)
      take₀ = TakeWhile.pass mm₀ tt nF₀ , reach-down {q = y} {w = E₀} {e = out (instEmit (mark begin) n)} {e₁ = out ls} (proj₂ x) lt₀ tt

  -- A LANE'S `laneDone` FOLLOWS ITS OWN `laneStart`, both past its
  -- subscription.
  core : ∀ s {y n} → enter LaneD s y (out (instEmit (mark laneDone) n))
       → Σ Pos λ y₀ → enter LaneD s y₀ (out ls) × s ≺ y₀ × y₀ ≺ y
  core s (TakeWhile.pass _ () _ , _)
  core s x@(TakeWhile.fail r _ nF _ , _) = split₁ s x r nF (merge-out Sv (Op.of (lanePart ∷ burstPart ∷ [])) s r)
    where
    split₂ : ∀ s {q n} kq k → enter LaneD s (q ⊕ [ ix 0 ]) (out (instEmit (mark laneDone) n)) → enter MM s q (out (instEmit (mark laneDone) n))
           → ¬ TakeWhile.Failed true undone (enter MM s) q → enter (Op.of (lanePart ∷ burstPart ∷ [])) s kq (out k)
           → enter (Sv k) (kq ⊕ [ ix 1 ]) q (out (instEmit (mark laneDone) n))
           → (k ≡ lanePart × Σ Pos λ v₂ → Σ (Routes × (List (IE B) × List (IE B))) λ yst → Σ (IE B) λ a₂
               → enter (Sc k (H₁ (kq ⊕ [ ix 1 ])) (H₂ (kq ⊕ [ ix 1 ]) k)) (Bp (kq ⊕ [ ix 1 ])) v₂ (out yst)
               × enter (Fr k (H₁ (kq ⊕ [ ix 1 ])) (H₂ (kq ⊕ [ ix 1 ]) k)) (Bp (kq ⊕ [ ix 1 ])) v₂ (out a₂)
               × (∀ {u} → Under (Bp (kq ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) u → u ≺ v₂) × v₂ ≺ q)
           → Σ Pos λ y₀ → enter LaneD s y₀ (out ls) × s ≺ y₀ × y₀ ≺ (q ⊕ [ ix 0 ])

    split₁ : ∀ s {q n} → enter LaneD s (q ⊕ [ ix 0 ]) (out (instEmit (mark laneDone) n)) → enter MM s q (out (instEmit (mark laneDone) n))
           → ¬ TakeWhile.Failed true undone (enter MM s) q
           → (Σ Pos λ kq → Σ Part λ k → enter (Op.of (lanePart ∷ burstPart ∷ [])) s kq (out k)
               × enter (Sv k) (kq ⊕ [ ix 1 ]) q (out (instEmit (mark laneDone) n)) × (kq ⊕ [ ix 1 ]) ≺ q)
           → Σ Pos λ y₀ → enter LaneD s y₀ (out ls) × s ≺ y₀ × y₀ ≺ (q ⊕ [ ix 0 ])
    split₁ s x r nF (kq , k , okq , svr , _) = split₂ s kq k x r nF okq svr (down k (kq ⊕ [ ix 1 ]) svr)
    split₂ s {q} {n} kq k x r nF okq svr (refl , v₂ , yst , a₂ , scr , fa , vlt , v₂e₂) = E₀ , take₀ , s-E₀ , ≺-trans {E₀} {q} {q ⊕ [ ix 0 ]} lt₀ (≺-ext q [])
     where
      P : Pos
      P = kq ⊕ [ ix 1 ]
      open Up P using (u-E₀; u-P; sv-row)
      open Split (Frame.V₀ lanePart (H₁ P) (H₂ P lanePart) (Bp P) ⊕ [ ix 1 ]) using (E₀)

      lt₀ : E₀ ≺ q
      lt₀ = ≺-trans {E₀} {v₂} {q} (vlt u-E₀) v₂e₂

      sv₀ : enter (Sv lanePart) P E₀ (out ls)
      sv₀ = sv-row

      P-E₀ : P ≺ E₀
      P-E₀ = under-ext P u-P

      s-E₀ : s ≺ E₀
      s-E₀ = ≺-trans {s} {kq} {E₀} (of-after s (lanePart ∷ burstPart ∷ []) okq) (under-ext kq (under-trans (under-⊕ (under-refl P) (ix 0)) u-P))

      mm₀ : enter MM s E₀ (out ls)
      mm₀ = Joining.lane okq tt (sv₀ , P-E₀) (λ ()) tt , reach-down {q = q} {w = E₀} {e = out (instEmit (mark laneDone) n)} {e₁ = out ls} (proj₂ r) lt₀ tt

      nF₀ : ¬ TakeWhile.Failed true undone (enter MM s) E₀
      nF₀ (q′ , a′ , x′ , nk′ , lt′) = nF (q′ , a′ , x′ , nk′ , ≺-trans {q′} {E₀} {q} lt′ lt₀)

      take₀ : enter LaneD s E₀ (out ls)
      take₀ = TakeWhile.pass mm₀ tt nF₀ , reach-down {q = q ⊕ [ ix 0 ]} {w = E₀} {e = out (instEmit (mark laneDone) n)} {e₁ = out ls} (proj₂ x) (≺-trans {E₀} {q} {q ⊕ [ ix 0 ]} lt₀ (≺-ext q [])) tt

------------------------------------------------------------------------
-- The lane, read at either meaning

module _ {Θ B Γ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ′ → X ∈ ⊤ ∷ Θ) (o : Obs Timeline Γ′ B) (ρ : DenEnv Θ) where

  Sh : Part → Obs Timeline (⊤ ∷ Θ) (IE B)
  Sh k = flatMap (mergeᶠ (just 1)) (laneSrc ρ′ o k) (of (true ∷ false ∷ []))

  pc0 : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s → enter (ev m (piece {B = B} lanePart 0) (h′ ∷ h ∷ ρ)) s (s ⊕ [ ix 0 ]) (out (marked laneStart))
  pc0 nothing  h h′ s = at-out , of-reach s 0 (marked laneStart ∷ []) {s ⊕ [ ix 0 ]} {out (marked laneStart)}
  pc0 (just _) h h′ s = at-out , of-reach s 0 (marked laneStart ∷ []) {s ⊕ [ ix 0 ]} {out (marked laneStart)}

  pc0-at : ∀ m k (h : Den ⊤) (h′ : Den (IE B)) s {y a} → enter (ev m (piece {B = B} k 0) (h′ ∷ h ∷ ρ)) s y (out a) → y ≡ s ⊕ [ ix 0 ] × T (undone a)
  pc0-at nothing  lanePart  h h′ s (r , _) with of-one s _ r
  ... | refl , refl = refl , tt
  pc0-at nothing  burstPart h h′ s (r , _) with of-one s _ r
  ... | refl , refl = refl , tt
  pc0-at (just _) lanePart  h h′ s (r , _) with of-one s _ r
  ... | refl , refl = refl , tt
  pc0-at (just _) burstPart h h′ s (r , _) with of-one s _ r
  ... | refl , refl = refl , tt

  pc1 : ∀ m k (h : Den ⊤) (h′ : Den (IE B)) s {y a} → enter (ev m (piece {B = B} k 1) (h′ ∷ h ∷ ρ)) s y (out a) → enter h′ s y (out a)
  pc1 nothing  lanePart  h h′ s r = r
  pc1 nothing  burstPart h h′ s r = r
  pc1 (just _) lanePart  h h′ s r = r
  pc1 (just _) burstPart h h′ s r = r

  pc2 : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s {y a} → enter (ev m (piece {B = B} burstPart 2) (h′ ∷ h ∷ ρ)) s y (out a) → ⊥
  pc2 nothing  h h′ s (() , _)
  pc2 (just _) h h′ s (() , _)

  sh-b : ∀ m (h : Den ⊤) p {y a} → enter (ev m (Sh burstPart) (h ∷ ρ)) p y (out a) → ⊥
  sh-b m h p r with bounded-out 1 (λ c → ev m (laneSrc ρ′ o burstPart c) (h ∷ ρ)) (Op.of (true ∷ false ∷ [])) p (sh-at m r)
    where
      sh-at : ∀ m {y a} → enter (ev m (Sh burstPart) (h ∷ ρ)) p y (out a)
            → enter (Op.flatMap (mergeᶠ (just 1)) (λ c → ev m (laneSrc ρ′ o burstPart c) (h ∷ ρ)) (Op.of (true ∷ false ∷ []))) p y (out a)
      sh-at nothing  r = r
      sh-at (just _) r = r
  ... | _ , _ , _ , _ , (at-out , _) , _ , (l , _) = blk m l
    where
      blk : ∀ m {s y a} → enter (ev m (laneSrc ρ′ o burstPart true) (h ∷ ρ)) s y (out a) → ⊥
      blk nothing  {s} l with each-one (λ _ → []) h s l
      ... | _ , _ , _ , ()
      blk (just _) {s} l with each-one (λ _ → []) h s l
      ... | _ , _ , _ , ()
  ... | _ , _ , _ , _ , (on-out at-out , _) , _ , (l , _) = emp m l
    where
      emp : ∀ m {s y a} → enter (ev m (laneSrc ρ′ o burstPart false) (h ∷ ρ)) s y (out a) → ⊥
      emp nothing  (() , _)
      emp (just _) (() , _)
  ... | _ , _ , _ , _ , (on-out (on-out ()) , _) , _ , _

  pc0-b : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s {y n} → enter (ev m (piece {B = B} burstPart 0) (h′ ∷ h ∷ ρ)) s y (out (instEmit (mark laneStart) n)) → ⊥
  pc0-b nothing  h h′ s (r , _) with of-one s _ r
  ... | _ , ()
  pc0-b (just _) h h′ s (r , _) with of-one s _ r
  ... | _ , ()

  pc2-l : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s {y n} → enter (ev m (piece {B = B} lanePart 2) (h′ ∷ h ∷ ρ)) s y (out (instEmit (mark laneStart) n)) → ⊥
  pc2-l nothing  h h′ s (r , _) with of-one s _ r
  ... | _ , ()
  pc2-l (just _) h h′ s (r , _) with of-one s _ r
  ... | _ , ()

  pc0-rows : ∀ m k (h : Den ⊤) (h′ : Den (IE B)) s {y e} → enter (ev m (piece {B = B} k 0) (h′ ∷ h ∷ ρ)) s y e → y ≡ s ⊕ [ ix 0 ] ⊎ y ≡ s ⊕ [ last ]
  pc0-rows nothing  lanePart  h h′ s (r , _) = one-rows s _ r
  pc0-rows nothing  burstPart h h′ s (r , _) = one-rows s _ r
  pc0-rows (just _) lanePart  h h′ s (r , _) = one-rows s _ r
  pc0-rows (just _) burstPart h h′ s (r , _) = one-rows s _ r

  pc0-ls : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s {y a} → enter (ev m (piece {B = B} lanePart 0) (h′ ∷ h ∷ ρ)) s y (out a) → a ≡ marked laneStart
  pc0-ls nothing  h h′ s (r , _) = proj₂ (of-one s _ r)
  pc0-ls (just _) h h′ s (r , _) = proj₂ (of-one s _ r)

  pc0-be : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s {y a} → enter (ev m (piece {B = B} burstPart 0) (h′ ∷ h ∷ ρ)) s y (out a) → a ≡ marked burstEnd
  pc0-be nothing  h h′ s (r , _) = proj₂ (of-one s _ r)
  pc0-be (just _) h h′ s (r , _) = proj₂ (of-one s _ r)

  sh-past : ∀ m k (h : Den ⊤) p {y e} → enter (ev m (Sh k) (h ∷ ρ)) p y e → p ≺ y
  sh-past nothing  k h p (r , _) = join-past {p = p} (of-after p (true ∷ false ∷ [])) (λ _ → bd-lane-past) (λ ()) r
  sh-past (just _) k h p (r , _) = join-past {p = p} (of-after p (true ∷ false ∷ [])) (λ _ → bd-lane-past) (λ ()) r

  module C (m : Maybe ℕ) = Core (λ k (h : Den ⊤) → ev m (Sh k) (h ∷ ρ)) (λ k j (h : Den ⊤) (h′ : Den (IE B)) → ev m (piece k j) (h′ ∷ h ∷ ρ))
    (pc0 m) (pc0-at m) (pc1 m) (pc2 m) (sh-b m) (pc0-b m) (pc2-l m) (pc0-rows m) (pc0-ls m) (pc0-be m) (sh-past m)

  -- The elaborated lane IS the core's, paid once: each reading below
  -- moves along it, rather than re-converting its whole denotation.
  lane-eq : ∀ m → ev m (laneˢ (laneSrc ρ′ o)) ρ ≡ C.LaneD m
  lane-eq nothing  = refl
  lane-eq (just n) = refl

  -- A LANE'S `laneDone` FOLLOWS ITS OWN `laneStart`, both past its
  -- subscription.
  lane-starts : ∀ m s {y n} → enter (ev m (laneˢ (laneSrc ρ′ o)) ρ) s y (out (instEmit (mark laneDone) n))
              → Σ Pos λ y₀ → enter (ev m (laneˢ (laneSrc ρ′ o)) ρ) s y₀ (out (marked laneStart)) × s ≺ y₀ × y₀ ≺ y
  lane-starts m s {y} {n} r = subst (λ d → Σ Pos λ y₀ → enter d s y₀ (out (marked laneStart)) × s ≺ y₀ × y₀ ≺ y) (sym (lane-eq m))
    (C.core m s (subst (λ d → enter d s y (out (instEmit (mark laneDone) n))) (lane-eq m) r))

  -- A LANE'S `begin` FOLLOWS ITS OWN `laneStart`, both past its
  -- subscription.
  begin-starts : ∀ m s {y n} → enter (ev m (laneˢ (laneSrc ρ′ o)) ρ) s y (out (instEmit (mark begin) n))
              → Σ Pos λ y₀ → enter (ev m (laneˢ (laneSrc ρ′ o)) ρ) s y₀ (out (marked laneStart)) × s ≺ y₀ × y₀ ≺ y
  begin-starts m s {y} {n} r = subst (λ d → Σ Pos λ y₀ → enter d s y₀ (out (marked laneStart)) × s ≺ y₀ × y₀ ≺ y) (sym (lane-eq m))
    (C.core-begin m s (subst (λ d → enter d s y (out (instEmit (mark begin) n))) (lane-eq m) r))

  -- A LANE SHOWS `laneStart` AT ONE PLACE, when its lane part's share shows
  -- none.
  lane-start-at : ∀ m s → (∀ {y n} → enter (ev m (Sh lanePart) (hot (Proper (enter (ev m empty ρ) (laneAt s ⊕ [ ix 1 ]))) ∷ ρ)) ((laneAt s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) y (out (instEmit (mark laneStart) n)) → ⊥)
                → ∀ {y n} → enter (ev m (laneˢ (laneSrc ρ′ o)) ρ) s y (out (instEmit (mark laneStart) n)) → y ≡ C.startAt m s
  lane-start-at nothing  s hn {y} {n} r = C.start-at nothing s hn (subst (λ d → enter d s y (out (instEmit (mark laneStart) n))) (lane-eq nothing) r)
  lane-start-at (just k) s hn {y} {n} r = C.start-at (just k) s hn (subst (λ d → enter d s y (out (instEmit (mark laneStart) n))) (lane-eq (just k)) r)

  -- A LANE SHOWS ITS `laneStart`, below its subscription's first child.
  lane-start-row : ∀ m s → enter (ev m (laneˢ (laneSrc ρ′ o)) ρ) s (C.startAt m s) (out (marked laneStart)) × Under (s ⊕ [ ix 0 ]) (C.startAt m s)
  lane-start-row m s = subst (λ d → enter d s (C.startAt m s) (out (marked laneStart)) × Under (s ⊕ [ ix 0 ]) (C.startAt m s)) (sym (lane-eq m)) (C.start-row m s)
