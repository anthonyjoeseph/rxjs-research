{-# OPTIONS --guardedness #-}

-- A JOINING KEEPS THE TRUTH, over an outer and lanes each read against
-- the next.  The joining's cuts are its inputs' cuts it shows a reached
-- row past the first spin row of: the outer's, and those of a lane it
-- runs uncut there.  Under such a cut its rows are that input's rows, at
-- the same positions (no other lane, value or outer row lies there), so
-- the spin shows silent; and once a row under it is reached, every spin
-- row is, through the rows it reached and the input's own (`Spreading`).
--
-- Up to a clean bound, every input cut few in the joining is one of its
-- cuts, so no row at or before the bound lies past an input cut, and
-- the outer and the lanes read there each agree with the next
-- (`AtBound`); the policy carries that over.  A pin is read at its
-- connect and by hand at itself: its own input row, with the next's
-- shadow wherever its connect leads a cut.
--
-- A lane is wherever the policy subscribes it (`Slots`): past its value,
-- in the world of a value's second child no later than its own.  Which
-- rows a lane's cut excludes, and which lane of the next shows a pin
-- past it, the policy says.
module denotation.Laws.Truth.Joining where

open import Data.Bool using (T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
import Data.List.Relation.Unary.Any.Properties as AnyP
open import Data.Nat using (zero; suc; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Bool.Properties using (T-≡)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable.Core using (T?)

open import denotation.Position using (Pos; ix; sub; last; _⊕_; inside)
open import denotation.Events using (<ᵖ-part)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Den; enter; After; Ended; Few; Dep; Reach; Truncate; Silent;
  hush; held; Work; _≺_; _≼_; module Joining)
open import denotation.Read using (loud)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; ≺-trans; ≺→≼; ≼-refl; ≼-trans; ≼-or-≻; ≼-split; ≺-≼-≺; ≺-irrefl;
  ≺-ext; ticks; reach-few; entered-reach; trunc-to)
open import denotation.Laws.Count using (Cov; cov-down; cov-lift; cov-stable; em; pinned-after)
open import denotation.Laws.Shows using (cover; cov-∈; cov-few; lead-∈; few-down; few-reach)
open import denotation.Laws.Worlds using (W; W⁼; inW; Ok; InvAt; InvD; Shows; _⊑_; ⊑-refl; ⊑-trans; ⊑-snoc; ⊑-snoc⁺; ⊑-cmp; ⊑-≼;
  conv; leads; plain-ix; world-after; inside-⊑; ⊕-assoc; ⊕-identityʳ; ⊕-injˡ; ⊕-injʳ; w-up; nest; nest⁼; flat-under)
  renaming (step to wstep)
open import denotation.Laws.JoinInv using (ix10)
open import denotation.Laws.Truth using (Truth; Rel; Placed; placing; Spun; Lies; Lie; Clean; Before; lie-up; before-of; few-ag; truth-lies;
  where?; below-next; spin-few)

-- A pin reached: few before its connect.
reach-pin : ∀ {X} {t : EmissionSet X} {y r} → T (inside r y) → Reach t y (pin r) → Few t r
reach-pin {y = y} {r} ins (ks , h) = ks , λ {k} x kr → h x (≺-≼-≺ {k} {r} {y} kr (⊑-≼ (inside-⊑ r y ins))) (λ _ → inj₁ kr)

-- Under a position: at it, under one of its spin rows, or past them all.
under-c : ∀ c {k} → c ⊑ k → k ≡ c ⊎ Spun c k ⊎ (∀ i → (c ⊕ [ ix i ]) ≺ k)
under-c c ([] , refl)        = inj₁ (⊕-identityʳ c)
under-c c (ix j ∷ r , refl)  = inj₂ (inj₁ (j , r , sym (⊕-assoc c [ ix j ] r)))
under-c c (sub _ ∷ r , refl) = inj₂ (inj₂ λ _ → Equivalence.from T-≡ (<ᵖ-part c [] r refl))
under-c c (last ∷ r , refl)  = inj₂ (inj₂ λ _ → Equivalence.from T-≡ (<ᵖ-part c [] r refl))

lies-⊑ : ∀ {c y} → Lies c y → c ⊑ y
lies-⊑ {c} (_ , l) = ⊑-trans (⊑-snoc⁺ c) l

lies-≺ : ∀ {c y} → Lies c y → c ≺ y
lies-≺ {c} {y} (i , l) = ≺-≼-≺ {c} {c ⊕ [ ix (suc i) ]} {y} (≺-ext c []) (⊑-≼ l)

-- Under a row past a cut's first, a connect: past it too, or leading the cut.
lie-split : ∀ {c q r} → Lies c q → r ⊑ q → Lies c r ⊎ r ⊑ c
lie-split {c} (i , li) rq with ⊑-cmp _ (c ⊕ [ ix (suc i) ]) rq li
... | inj₂ cr = inj₁ (i , cr)
... | inj₁ rc with ⊑-snoc c rc
...   | inj₁ r⊑c = inj₂ r⊑c
...   | inj₂ refl = inj₁ (i , ⊑-refl _)

cov-++ˡ : ∀ {q ks ks′ k} → Cov q ks k → Cov q (ks ++ ks′) k
cov-++ˡ (inj₁ kq) = inj₁ kq
cov-++ˡ (inj₂ a)  = inj₂ (AnyP.++⁺ˡ a)

cov-++ʳ : ∀ {q ks ks′ k} → Cov q ks′ k → Cov q (ks ++ ks′) k
cov-++ʳ (inj₁ kq)          = inj₁ kq
cov-++ʳ {ks = ks} (inj₂ a) = inj₂ (AnyP.++⁺ʳ ks a)

-- An outer row under a spin, as a joining shows it.
data Same {A B : Set} : Ev A → Ev B → Set where
  s-skip : Same skip skip
  s-pin  : ∀ {r} → Same (pin r) (pin r)

same-silent : ∀ {A B} {e₀ : Ev A} {e : Ev B} → Same e₀ e → Silent e
same-silent s-skip = hush
same-silent s-pin  = held

same-dep : ∀ {A B} {z k} {e₀ e₀′ : Ev A} {e e′ : Ev B} → Same e₀ e → Same e₀′ e′ → Dep z e k e′ → Dep z e₀ k e₀′
same-dep s-skip _      _ = tt
same-dep s-pin  s-skip d i with d i
... | inj₁ kr = inj₁ kr
... | inj₂ ()
same-dep s-pin  s-pin  d i with d i
... | inj₁ kr   = inj₁ kr
... | inj₂ refl = inj₂ refl

work-silent : ∀ {B} {e : Ev B} → Silent e → Work e
work-silent hush = tt
work-silent held = tt

-- A JOINING'S LANES, on one side: each subscribed at a slot past its
-- value, in the world of the second child of a value no later; and a
-- lane pinning the connect another lane pins is that lane.
record Slots {A B : Set} (H : Pos → Set) (g : A → Den B) (u : EmissionSet A) (Ln : Pos → A → EmissionSet B) : Set₁ where
  field
    Sl   : Pos → A → Pos → Set
    slot : ∀ {q a k e} → Ln q a k e → Σ Pos λ s → Sl q a s × After (g a) s k e
    mk   : ∀ {q a s k e} → Sl q a s → After (g a) s k e → Ln q a k e
    okS  : ∀ {q a s} → u q (out a) → Sl q a s → Ok H s
    past : ∀ {q a s} → Sl q a s → q ≺ s
    seat : ∀ {q a s} → u q (out a) → Sl q a s → Σ Pos λ ρ → Σ A λ b → u ρ (out b) × ρ ≼ q × W⁼ H (ρ ⊕ [ ix 1 ]) s
    meet : ∀ {q₀ a₀ s₀ z q a k r} → u q₀ (out a₀) → Sl q₀ a₀ s₀ → enter (g a₀) s₀ z (pin r) → u q (out a) → Ln q a k (pin r)
         → enter (g a₀) s₀ k (pin r)

module Core {A B : Set} {H : Pos → Set} {f f′ : A → Den B} {s s′ : Den A}
            (Is : InvD H s) (Is′ : InvD H s′) (If : ∀ a → InvD H (f a)) (If′ : ∀ a → InvD H (f′ a))
            (R : Rel H s s′) (Rf : ∀ a → Rel H (f a) (f′ a)) (p : Pos) (ok : Ok H p)
            (Ln : (A → Den B) → EmissionSet A → Pos → A → EmissionSet B)
            (Runs : (A → Den B) → EmissionSet A → Pos → Set) (Cut : (A → Den B) → EmissionSet A → Pos → Pos → Set)
            (Hand : (A → Den B) → EmissionSet A → Pos → Set)
            (SL : Slots H f (enter s p) (Ln f (enter s p))) (SL′ : Slots H f′ (enter s′ p) (Ln f′ (enter s′ p))) where
  o o′ : EmissionSet A
  o  = enter s p
  o′ = enter s′ p

  open Slots SL
  module SL′ = Slots SL′

  Io : InvAt H p o
  Io = Is p ok

  Io′ : InvAt H p o′
  Io′ = Is′ p ok

  To : Truth o o′
  To = Placed.tr (R p ok)

  module TO = Truth To

  LI : ∀ {q a s₁} → o q (out a) → Sl q a s₁ → InvAt H s₁ (enter (f a) s₁)
  LI {a = a} {s₁} x sl = If a s₁ (okS x sl)

  LI′ : ∀ {q a s₁} → o′ q (out a) → SL′.Sl q a s₁ → InvAt H s₁ (enter (f′ a) s₁)
  LI′ {a = a} {s₁} x sl = If′ a s₁ (SL′.okS x sl)

  -- Each lane read against the next, where it is subscribed.
  PL : ∀ {q a s₁} → o q (out a) → Sl q a s₁ → Placed H s₁ (enter (f a) s₁) (enter (f′ a) s₁)
  PL {a = a} {s₁} x sl = Rf a s₁ (okS x sl)

  TL : ∀ {q a s₁} → o q (out a) → Sl q a s₁ → Truth (enter (f a) s₁) (enter (f′ a) s₁)
  TL x sl = Placed.tr (PL x sl)

  TC : ∀ {q a s₁} → o q (out a) → Sl q a s₁ → Pos → Set
  TC x sl = Truth.Cut (TL x sl)

  lc⁼ : ∀ {q a s₁ c} (x : o q (out a)) (sl : Sl q a s₁) → TC x sl c → W⁼ H s₁ c
  lc⁼ x sl = Placed.placed (PL x sl)

  after : ∀ {q a s₁ k e} (x : o q (out a)) (sl : Sl q a s₁) → enter (f a) s₁ k e → s₁ ≺ k
  after x sl l = world-after (InvAt.world (LI x sl) l) (InvAt.real (LI x sl) l)

  -- A lane pin's connect lies past its value.
  val-pin : ∀ {q a s₁ k r} (x : o q (out a)) (sl : Sl q a s₁) → enter (f a) s₁ k (pin r) → q ≼ r
  val-pin {q} {s₁ = s₁} {r = r} x sl l = ≺→≼ {q} {r} (≺-≼-≺ {q} {s₁} {r} (past sl) (pinned-after (LI x sl) l))

  val-pin′ : ∀ {q a s₁ k r} (x : o′ q (out a)) (sl : SL′.Sl q a s₁) → enter (f′ a) s₁ k (pin r) → q ≼ r
  val-pin′ {q} {s₁ = s₁} {r = r} x sl l = ≺→≼ {q} {r} (≺-≼-≺ {q} {s₁} {r} (SL′.past sl) (pinned-after (LI′ x sl) l))

  -- A lane's world lies in its seat's.
  seat-w : ∀ {q a s₁ w} (x : o q (out a)) → Sl q a s₁ → W⁼ H s₁ w → Σ Pos λ ρ → Σ A λ b → o ρ (out b) × W⁼ H (ρ ⊕ [ ix 1 ]) w
  seat-w x sl w⁼ = let (ρ , b , xρ , _ , ρW) = seat x sl in ρ , b , xρ , nest⁼ ρW w⁼

  s-w⁼ : ∀ {q a s₁} (x : o q (out a)) → Sl q a s₁ → W⁼ H p s₁
  s-w⁼ x sl = let (_ , _ , xρ , _ , ρW) = seat x sl in nest⁼ (inW (wstep (inW (InvAt.world Io xρ)) plain-ix)) ρW

  -- No outer row in a lane's world.
  no-o : ∀ {q a s₁ w y e} (x : o q (out a)) → Sl q a s₁ → W⁼ H s₁ w → o y e → w ⊑ y → ⊥
  no-o x sl w⁼ oy le = let (_ , _ , xρ , v) = seat-w x sl w⁼ in InvAt.under Io xρ oy plain-ix v le

  -- A lane row lies in the world of a value's second child.
  lane-root : ∀ {q a k e} → o q (out a) → Ln f o q a k e → Σ Pos λ ρ → Σ A λ b → o ρ (out b) × W H (ρ ⊕ [ ix 1 ]) k
  lane-root x l = let (_ , sl , (lk , _)) = slot l ; (ρ , b , xρ , _ , ρW) = seat x sl in ρ , b , xρ , nest ρW (InvAt.world (LI x sl) lk)

  -- No outer row under a lane row.
  lane-o : ∀ {q a k e z e′} → o q (out a) → Ln f o q a k e → o z e′ → k ⊑ z → ⊥
  lane-o x l oz kz = let (_ , _ , xρ , v) = lane-root x l in InvAt.under Io xρ oz plain-ix (inW v) kz

  -- No value under an outer cut's spin, and no outer row at the cut.
  o-val-spun : ∀ {c y a} → TO.Cut c → Spun c y → o y (out a) → ⊥
  o-val-spun cc sp x = loud tt (TO.silent cc sp x)

  o-at-cut : ∀ {c e} → TO.Cut c → o c e → ⊥
  o-at-cut cc x with TO.shows cc 0
  ... | _ , _ , cz , oz = flat-under Io x oz cz

  -- No lane reaches under an outer cut's spin.
  w1 : ∀ {c ρ b y m} → TO.Cut c → o ρ (out b) → W H (ρ ⊕ [ ix 1 ]) y → (c ⊕ [ ix m ]) ⊑ y → ⊥
  w1 {c} {ρ} {m = m} cc x yw le with TO.shows cc m
  ... | _ , _ , cz , oz =
    leads (proj₂ ok) (wstep (Placed.placed (R p ok) cc) plain-ix) (λ v → InvAt.under Io x oz plain-ix v cz) nb (inW yw) le
    where
      nb : (c ⊕ [ ix m ]) ⊑ (ρ ⊕ [ ix 1 ]) → ⊥
      nb l with ⊑-snoc ρ l
      ... | inj₁ cq = o-val-spun cc (m , cq) x
      ... | inj₂ eq = o-at-cut cc (subst (λ w → o w (out _)) (sym (⊕-injˡ c ρ eq)) x)

  lane-w1 : ∀ {c q a y e m} → TO.Cut c → o q (out a) → Ln f o q a y e → (c ⊕ [ ix m ]) ⊑ y → ⊥
  lane-w1 cc x l le = let (_ , _ , xρ , v) = lane-root x l in w1 cc xρ v le

  -- Either side's joining: its pins wait only on rows of their own input.
  module Side (g : A → Den B) (u : EmissionSet A) (Iu : InvAt H p u) (Ig : ∀ a → InvD H (g a)) (S : Slots H g u (Ln g u))
              (ur : ∀ {k e} → u k e → Reach u k e) where
    open Joining (Ln g u) u (λ _ _ → ⊥) (Ended u) (Runs g u) (Cut g u) (Hand g u) using (JoinT; opin; lane; left; run)
    module U = Slots S

    LIu : ∀ {q a s₁} → u q (out a) → U.Sl q a s₁ → InvAt H s₁ (enter (g a) s₁)
    LIu {a = a} {s₁} x sl = Ig a s₁ (U.okS x sl)

    -- No outer row under a lane's world.
    no-u : ∀ {q a s₁ w y e} → u q (out a) → U.Sl q a s₁ → W⁼ H s₁ w → u y e → w ⊑ y → ⊥
    no-u x sl w⁼ uy le = let (_ , _ , xρ , _ , ρW) = U.seat x sl in InvAt.under Iu xρ uy plain-ix (nest⁼ ρW w⁼) le

    -- A lane pin's connect, in its lane's world and before it.
    lpin : ∀ {q a k r} → u q (out a) → Ln g u q a k (pin r) → (∀ {y e} → u y e → r ⊑ y → ⊥) × T (inside r k)
    lpin x l = let (_ , sl , (lk , _)) = U.slot l in no-u x sl (proj₁ (InvAt.pinned (LIu x sl) lk)) , proj₂ (InvAt.pinned (LIu x sl) lk)

    ins-J : ∀ {y r} → JoinT y (pin r) → T (inside r y)
    ins-J (opin x)         = proj₂ (InvAt.pinned Iu x)
    ins-J (lane x _ l _ _) = proj₂ (lpin x l)
    ins-J (left _ _ _ _ i) = i
    ins-J (run () _)

    -- An outer pin waits on rows before its connect and outer pins of it.
    reach-opin : ∀ {z r} → Few JoinT r → u z (pin r) → Reach JoinT z (pin r)
    reach-opin {z} {r} (ks , h) oz with ur oz
    ... | ks′ , h′ = ks ++ ks′ , go
      where
        ins : T (inside r z)
        ins = proj₂ (InvAt.pinned Iu oz)

        pinned : ∀ {k} → JoinT k (pin r) → k ≺ z → k ∈ ks′
        pinned (opin ok′) kz       = h′ ok′ kz (λ _ → inj₂ refl)
        pinned (lane x _ l _ _) _  = ⊥-elim (proj₁ (lpin x l) oz (inside-⊑ r z ins))
        pinned (left x _ l _ _) _  = ⊥-elim (proj₁ (lpin x l) oz (inside-⊑ r z ins))
        pinned (run () _) _

        go : ∀ {k e′} → JoinT k e′ → k ≺ z → Dep z (pin r) k e′ → k ∈ ks ++ ks′
        go jk kz d with d ins
        ... | inj₁ kr   = ∈-++⁺ˡ (h jk kr)
        ... | inj₂ refl = ∈-++⁺ʳ ks (pinned jk kz)

    -- A lane pin waits on rows before its connect and its lane's pins of it.
    reach-lane : ∀ {q a s₁ z r} → Few JoinT r → u q (out a) → U.Sl q a s₁ → enter (g a) s₁ z (pin r) → Reach JoinT z (pin r)
    reach-lane {q} {a} {s₁} {z} {r} (ks , h) x sl lz with entered-reach (g a) s₁ lz
    ... | ks′ , h′ = ks ++ ks′ , go
      where
        r⁼ : W⁼ H s₁ r
        r⁼ = proj₁ (InvAt.pinned (LIu x sl) lz)

        ins : T (inside r z)
        ins = proj₂ (InvAt.pinned (LIu x sl) lz)

        pinned : ∀ {k} → JoinT k (pin r) → k ≺ z → k ∈ ks′
        pinned {k} (opin ok′) _     = ⊥-elim (no-u x sl r⁼ ok′ (inside-⊑ r k (proj₂ (InvAt.pinned Iu ok′))))
        pinned (lane x′ _ l _ _) kz = h′ (U.meet x sl lz x′ l) kz (λ _ → inj₂ refl)
        pinned (left x′ _ l _ _) kz = h′ (U.meet x sl lz x′ l) kz (λ _ → inj₂ refl)
        pinned (run () _) _

        go : ∀ {k e′} → JoinT k e′ → k ≺ z → Dep z (pin r) k e′ → k ∈ ks ++ ks′
        go jk kz d with d ins
        ... | inj₁ kr   = ∈-++⁺ˡ (h jk kr)
        ... | inj₂ refl = ∈-++⁺ʳ ks (pinned jk kz)

  -- A joining's policy: which values run, where a lane is cut, where an
  -- end hands off, how agreeing inputs make agreeing joinings, and which
  -- lane a row near a lane's cut is.
  module Policy (Lanes : Pos → Set)
                (mk-lanes : ∀ {b} → (∀ {q a s₁ k} → o q (out a) → Sl q a s₁ → Runs f o q → k ≼ b → ¬ Cut f o q k
                                      → AgreeTo k (enter (f a) s₁) (enter (f′ a) s₁))
                          → (∀ {q a s₁ k r} → o q (out a) → Sl q a s₁ → Runs f o q → k ≼ b → ¬ Cut f o q r → T (inside r k)
                             → (enter (f a) s₁ k (pin r) → enter (f′ a) s₁ k (pin r)) × (enter (f′ a) s₁ k (pin r) → enter (f a) s₁ k (pin r)))
                          → Lanes b)
                (sl-to   : ∀ Q → AgreeTo Q o o′ → Lanes Q → ∀ {q a s₁} → s₁ ≼ Q → Sl q a s₁ → SL′.Sl q a s₁)
                (sl-from : ∀ Q → AgreeTo Q o o′ → Lanes Q → ∀ {q a s₁} → s₁ ≼ Q → SL′.Sl q a s₁ → Sl q a s₁)
                (in-lane : ∀ {q₀ a₀ s₀ c y e q a} {X : EmissionSet B} → o q₀ (out a₀) → Sl q₀ a₀ s₀ → (tr : Truth (enter (f a₀) s₀) X)
                         → W⁼ H s₀ c → Truth.Cut tr c → Spun c y → o q (out a) → Ln f o q a y e → enter (f a₀) s₀ y e)
                (at-lane : ∀ {q₀ a₀ s₀ c e q a} {X : EmissionSet B} → o q₀ (out a₀) → Sl q₀ a₀ s₀ → (tr : Truth (enter (f a₀) s₀) X)
                         → W⁼ H s₀ c → Truth.Cut tr c → o q (out a) → Ln f o q a c e → ⊥)
                (at-hand : ∀ {q₀ a₀ s₀ c q a} {X : EmissionSet B} → o q₀ (out a₀) → Sl q₀ a₀ s₀ → (tr : Truth (enter (f a₀) s₀) X)
                         → W⁼ H s₀ (c ⊕ [ ix 0 ]) → Truth.Cut tr (c ⊕ [ ix 0 ]) → o q (out a) → Ln f o q a c end → Hand f o c → ⊥)
                (one-lane : ∀ {q₀ a₀ s₀ c w r q a} {X : EmissionSet B} → o q₀ (out a₀) → Sl q₀ a₀ s₀ → (tr : Truth (enter (f a₀) s₀) X)
                          → W⁼ H s₀ c → Truth.Cut tr c → Lies c w → r ⊑ c → AgreeTo q₀ o o′ → AgreeTo r o o′ → Lanes r
                          → (∀ {q₂ a₂ s₂ c₂} → o q₂ (out a₂) → Sl q₂ a₂ s₂ → Runs f o q₂ → After (f a₂) s₂ c₂ end → c₂ ≺ s₀ → ¬ Cut f o q₂ c₂
                             → enter (f′ a₂) s₂ c₂ end)
                          → o′ q (out a) → Ln f′ o′ q a w (pin r) → enter (f′ a₀) s₀ w (pin r))
                (shows-J : Shows (Joining.JoinT (Ln f o) o (λ _ _ → ⊥) (Ended o) (Runs f o) (Cut f o) (Hand f o)))
                (cut-up  : ∀ {q k y} → Cut f o q k → k ≼ y → Cut f o q y)
                (cut-up′ : ∀ {q k y} → Cut f′ o′ q k → k ≼ y → Cut f′ o′ q y)
                (cut-in  : ∀ {q z w} → Cut f o q z → w ⊑ z → (∀ {y e} → o y e → w ⊑ y → ⊥) → Cut f o q w)
                (agree   : ∀ Q → AgreeTo Q o o′ → Lanes Q
                         → AgreeTo Q (Joining.JoinT (Ln f o) o (λ _ _ → ⊥) (Ended o) (Runs f o) (Cut f o) (Hand f o))
                                     (Joining.JoinT (Ln f′ o′) o′ (λ _ _ → ⊥) (Ended o′) (Runs f′ o′) (Cut f′ o′) (Hand f′ o′)))
                (runs-to : ∀ Q → AgreeTo Q o o′ → Lanes Q → ∀ q → q ≼ Q → Runs f o q → Runs f′ o′ q)
                (runs-from : ∀ Q → AgreeTo Q o o′ → Lanes Q → ∀ q → q ≼ Q → Runs f′ o′ q → Runs f o q)
                (cut-to  : ∀ Q → AgreeTo Q o o′ → ∀ q k → k ≼ Q → Cut f o q k → Cut f′ o′ q k)
                (cut-from : ∀ Q → AgreeTo Q o o′ → ∀ q k → k ≼ Q → Cut f′ o′ q k → Cut f o q k) where
    open Joining (Ln f o) o (λ _ _ → ⊥) (Ended o) (Runs f o) (Cut f o) (Hand f o)
      using (JoinT; val; step; opin; oend; opass; lane; lend; lpass; hand; left; run; rend; rpass; rhand)
    module K′ = Joining (Ln f′ o′) o′ (λ _ _ → ⊥) (Ended o′) (Runs f′ o′) (Cut f′ o′) (Hand f′ o′)
    module S  = Side f o Io If SL (entered-reach s p)
    module S′ = Side f′ o′ Io′ If′ SL′ (entered-reach s′ p)

    Jt Jt′ : EmissionSet B
    Jt  = Truncate JoinT
    Jt′ = Truncate K′.JoinT

    -- A lane's cut, the lane running and uncut there.
    LCut : Pos → Set
    LCut c = Σ Pos λ q → Σ A λ a → Σ Pos λ s₁ → Σ (o q (out a)) λ x → Σ (Sl q a s₁) λ sl → Runs f o q × ¬ Cut f o q c × TC x sl c

    InCut : Pos → Set
    InCut c = TO.Cut c ⊎ LCut c

    -- An input's cut the joining shows a row past the first of.
    Cut′ : Pos → Set
    Cut′ c = InCut c × Σ Pos λ y → Σ (Ev B) λ e → Jt y e × Lies c y

    unc : ∀ {q k c} → ¬ Cut f o q k → c ≼ k → ¬ Cut f o q c
    unc nc ck ct = nc (cut-up ct ck)

    -- Uncut at a lane's pin's connect: uncut at whatever leads a row under it.
    uncut-under : ∀ {q a s₁ r c k} → o q (out a) → Sl q a s₁ → ¬ Cut f o q r → W⁼ H s₁ r → c ⊑ k → r ⊑ k → ¬ Cut f o q c
    uncut-under {c = c} {k} x sl nr r⁼ ck rk with ⊑-cmp c _ ck rk
    ... | inj₁ cr = unc nr (⊑-≼ cr)
    ... | inj₂ rc = λ ct → nr (cut-in ct rc (no-o x sl r⁼))

    -- Uncut at a lane's cut: uncut under it.
    unc-in : ∀ {q a s₁ c z} → o q (out a) → Sl q a s₁ → W⁼ H s₁ c → ¬ Cut f o q c → c ⊑ z → ¬ Cut f o q z
    unc-in x sl c⁼ nc cz ct = nc (cut-in ct cz (no-o x sl c⁼))

    il : ∀ {q₀ a₀ s₀ c y e q a} (x₀ : o q₀ (out a₀)) (sl₀ : Sl q₀ a₀ s₀) → TC x₀ sl₀ c → Spun c y → o q (out a) → Ln f o q a y e
       → enter (f a₀) s₀ y e
    il x₀ sl₀ cl = in-lane x₀ sl₀ (TL x₀ sl₀) (lc⁼ x₀ sl₀ cl) cl

    al : ∀ {q₀ a₀ s₀ c e q a} (x₀ : o q₀ (out a₀)) (sl₀ : Sl q₀ a₀ s₀) → TC x₀ sl₀ c → o q (out a) → Ln f o q a c e → ⊥
    al x₀ sl₀ cl = at-lane x₀ sl₀ (TL x₀ sl₀) (lc⁼ x₀ sl₀ cl) cl

    ------------------------------------------------------------------------
    -- Under a cut

    -- Under an outer cut's spin, the joining's rows are the outer's.
    in-o : ∀ {c y e} → TO.Cut c → Spun c y → JoinT y e → Σ (Ev A) λ e₀ → Same e₀ e × o y e₀
    in-o {c} cc (i , cy) (val {q} x) with ⊑-snoc q cy
    ... | inj₁ cq = ⊥-elim (o-val-spun cc (i , cq) x)
    ... | inj₂ eq = ⊥-elim (o-at-cut cc (subst (λ w → o w (out _)) (sym (⊕-injˡ c q eq)) x))
    in-o cc _  (step x)                = skip , s-skip , x
    in-o cc _  (opin x)                = pin _ , s-pin , x
    in-o cc sp (oend x _)              = ⊥-elim (loud tt (TO.silent cc sp x))
    in-o cc sp (opass x _)             = ⊥-elim (loud tt (TO.silent cc sp x))
    in-o cc (_ , cy) (lane x _ l _ _)    = ⊥-elim (lane-w1 cc x l cy)
    in-o cc (_ , cy) (lend x _ l _ _ _)  = ⊥-elim (lane-w1 cc x l cy)
    in-o cc (_ , cy) (lpass x _ l _ _ _) = ⊥-elim (lane-w1 cc x l cy)
    in-o {c} cc (_ , cy) (hand {c = ce} x _ l _ _) with ⊑-snoc ce cy
    ... | inj₁ cce = ⊥-elim (lane-w1 cc x l cce)
    ... | inj₂ eq with ⊕-injˡ c ce eq
    ...   | refl with TO.shows cc 0
    ...     | _ , _ , cz , oz = ⊥-elim (lane-o x l oz (⊑-trans (⊑-snoc⁺ c) cz))
    in-o cc (_ , cy) (left x _ l _ _)    = ⊥-elim (lane-w1 cc x l cy)
    in-o cc _  (run () _)
    in-o cc _  (rend () _ _)
    in-o cc _  (rpass () _ _)
    in-o cc _  (rhand () _)

    not-at-o : ∀ {c e} → TO.Cut c → JoinT c e → ⊥
    not-at-o cc (val {q} x) with TO.shows cc 0
    ... | _ , _ , cz , oz = flat-under Io x oz (⊑-trans (⊑-snoc⁺ (q ⊕ [ ix 0 ])) cz)
    not-at-o cc (step x)    = o-at-cut cc x
    not-at-o cc (opin x)    = o-at-cut cc x
    not-at-o cc (oend x _)  = o-at-cut cc x
    not-at-o cc (opass x _) = o-at-cut cc x
    not-at-o {c} cc (lane x _ l _ _) with TO.shows cc 0
    ... | _ , _ , cz , oz = lane-o x l oz (⊑-trans (⊑-snoc⁺ c) cz)
    not-at-o {c} cc (lend x _ l _ _ _) with TO.shows cc 0
    ... | _ , _ , cz , oz = lane-o x l oz (⊑-trans (⊑-snoc⁺ c) cz)
    not-at-o {c} cc (lpass x _ l _ _ _) with TO.shows cc 0
    ... | _ , _ , cz , oz = lane-o x l oz (⊑-trans (⊑-snoc⁺ c) cz)
    not-at-o cc (hand {c = ce} x _ l _ _) with TO.shows cc 0
    ... | _ , _ , cz , oz = lane-o x l oz (⊑-trans (⊑-snoc⁺ ce) (⊑-trans (⊑-snoc⁺ (ce ⊕ [ ix 0 ])) cz))
    not-at-o {c} cc (left x _ l _ _) with TO.shows cc 0
    ... | _ , _ , cz , oz = lane-o x l oz (⊑-trans (⊑-snoc⁺ c) cz)
    not-at-o cc (run () _)
    not-at-o cc (rend () _ _)
    not-at-o cc (rpass () _ _)
    not-at-o cc (rhand () _)

    -- Under a lane's cut's spin, the joining's rows are that lane's.
    in-L : ∀ {q₀ a₀ s₀ c y e} (x₀ : o q₀ (out a₀)) (sl₀ : Sl q₀ a₀ s₀) → TC x₀ sl₀ c → Spun c y → JoinT y e → enter (f a₀) s₀ y e
    in-L {c = c} x₀ sl₀ cl (i , cy) (val {q} x) with ⊑-snoc q cy
    ... | inj₁ cq = ⊥-elim (no-o x₀ sl₀ (lc⁼ x₀ sl₀ cl) x (⊑-trans (⊑-snoc⁺ c) cq))
    ... | inj₂ eq = ⊥-elim (no-o x₀ sl₀ (lc⁼ x₀ sl₀ cl) (subst (λ w → o w (out _)) (sym (⊕-injˡ c q eq)) x) (⊑-refl c))
    in-L {c = c} x₀ sl₀ cl (_ , cy) (step x)    = ⊥-elim (no-o x₀ sl₀ (lc⁼ x₀ sl₀ cl) x (⊑-trans (⊑-snoc⁺ c) cy))
    in-L {c = c} x₀ sl₀ cl (_ , cy) (opin x)    = ⊥-elim (no-o x₀ sl₀ (lc⁼ x₀ sl₀ cl) x (⊑-trans (⊑-snoc⁺ c) cy))
    in-L {c = c} x₀ sl₀ cl (_ , cy) (oend x _)  = ⊥-elim (no-o x₀ sl₀ (lc⁼ x₀ sl₀ cl) x (⊑-trans (⊑-snoc⁺ c) cy))
    in-L {c = c} x₀ sl₀ cl (_ , cy) (opass x _) = ⊥-elim (no-o x₀ sl₀ (lc⁼ x₀ sl₀ cl) x (⊑-trans (⊑-snoc⁺ c) cy))
    in-L x₀ sl₀ cl sp (lane x _ l _ _)    = il x₀ sl₀ cl sp x l
    in-L x₀ sl₀ cl sp (lend x _ l _ _ _)  = ⊥-elim (loud tt (Truth.silent (TL x₀ sl₀) cl sp (il x₀ sl₀ cl sp x l)))
    in-L x₀ sl₀ cl sp (lpass x _ l _ _ _) = ⊥-elim (loud tt (Truth.silent (TL x₀ sl₀) cl sp (il x₀ sl₀ cl sp x l)))
    in-L {c = c} x₀ sl₀ cl (i , cy) (hand {c = ce} x _ l _ _) with ⊑-snoc ce cy
    ... | inj₁ cce = ⊥-elim (loud tt (Truth.silent (TL x₀ sl₀) cl (i , cce) (il x₀ sl₀ cl (i , cce) x l)))
    ... | inj₂ eq with ⊕-injˡ c ce eq
    ...   | refl = ⊥-elim (al x₀ sl₀ cl x l)
    in-L x₀ sl₀ cl sp (left x _ l _ _) = il x₀ sl₀ cl sp x l
    in-L x₀ sl₀ cl _ (run () _)
    in-L x₀ sl₀ cl _ (rend () _ _)
    in-L x₀ sl₀ cl _ (rpass () _ _)
    in-L x₀ sl₀ cl _ (rhand () _)

    not-at-L : ∀ {q₀ a₀ s₀ c e} (x₀ : o q₀ (out a₀)) (sl₀ : Sl q₀ a₀ s₀) → TC x₀ sl₀ c → JoinT c e → ⊥
    not-at-L x₀ sl₀ cl (val {q} x) with seat-w x₀ sl₀ (lc⁼ x₀ sl₀ cl)
    ... | ρ , _ , xρ , v with w-up plain-ix v
    ...   | inj₁ eq = ix10 (⊕-injʳ ρ q eq)
    ...   | inj₂ v′ = InvAt.under Io xρ x plain-ix v′ (⊑-refl q)
    not-at-L x₀ sl₀ cl (step x)    = no-o x₀ sl₀ (lc⁼ x₀ sl₀ cl) x (⊑-refl _)
    not-at-L x₀ sl₀ cl (opin x)    = no-o x₀ sl₀ (lc⁼ x₀ sl₀ cl) x (⊑-refl _)
    not-at-L x₀ sl₀ cl (oend x _)  = no-o x₀ sl₀ (lc⁼ x₀ sl₀ cl) x (⊑-refl _)
    not-at-L x₀ sl₀ cl (opass x _) = no-o x₀ sl₀ (lc⁼ x₀ sl₀ cl) x (⊑-refl _)
    not-at-L x₀ sl₀ cl (lane x _ l _ _)    = al x₀ sl₀ cl x l
    not-at-L x₀ sl₀ cl (lend x _ l _ _ _)  = al x₀ sl₀ cl x l
    not-at-L x₀ sl₀ cl (lpass x _ l _ _ _) = al x₀ sl₀ cl x l
    not-at-L x₀ sl₀ cl (hand x _ l _ h)    = at-hand x₀ sl₀ (TL x₀ sl₀) (lc⁼ x₀ sl₀ cl) cl x l h
    not-at-L x₀ sl₀ cl (left x _ l _ _)    = al x₀ sl₀ cl x l
    not-at-L x₀ sl₀ cl (run () _)
    not-at-L x₀ sl₀ cl (rend () _ _)
    not-at-L x₀ sl₀ cl (rpass () _ _)
    not-at-L x₀ sl₀ cl (rhand () _)

    ------------------------------------------------------------------------
    -- A cut reached shows every spin row

    Spread : Pos → Set
    Spread c = ∀ i → Σ Pos λ z → Σ (Ev B) λ e → (c ⊕ [ ix i ]) ⊑ z × Jt z e

    -- An input `I` whose spin rows the joining shows where they lie, and
    -- whose rows are the joining's under the spin: past a bound under the
    -- cut few in the joining, every spin row is reached, through the rows
    -- before the bound and the input's own.
    module Spreading {X : Set} (I : EmissionSet X) (Rl : Ev X → Ev B → Set) {c : Pos}
                     (sh : ∀ i → Σ Pos λ z → Σ (Ev X) λ e₀ → (c ⊕ [ ix i ]) ⊑ z × I z e₀)
                     (img : ∀ {z e₀} → Spun c z → I z e₀ → Σ (Ev B) λ e → Rl e₀ e × JoinT z e)
                     (back : ∀ {k e} → Spun c k → JoinT k e → Σ (Ev X) λ e₀ → Rl e₀ e × I k e₀)
                     (dep : ∀ {z k e₀ e e₀′ e′} → Rl e₀ e → Rl e₀′ e′ → Dep z e k e′ → Dep z e₀ k e₀′)
                     (rch : ∀ {z e₀} → I z e₀ → Reach I z e₀)
                     (not-at : ∀ {e} → JoinT c e → ⊥) where
      spread : ∀ {b} → c ⊑ b → Few JoinT b → Spread c
      spread {b} cb (ks , h) i with sh i
      ... | z , e₀ , cz , iz with img (i , cz) iz | rch iz
      ...   | e , rl , jz | ks′ , h′ = z , e , cz , jz , (ks ++ ks′ , reach)
        where
          reach : ∀ {k e′} → JoinT k e′ → k ≺ z → Dep z e k e′ → k ∈ ks ++ ks′
          reach {k} jk kz d with ≼-or-≻ b k
          ... | inj₂ kb = ∈-++⁺ˡ (h jk kb)
          ... | inj₁ bk with under-c c (conv {c} {b} {k} {z} cb bk kz (⊑-trans (⊑-snoc⁺ c) cz))
          ...   | inj₁ refl = ⊥-elim (not-at jk)
          ...   | inj₂ (inj₂ far) =
            ⊥-elim (≺-irrefl {k} (≺-trans {k} {z} {k} kz (≺-trans {z} {c ⊕ [ ix (suc i) ]} {k} (below-next c cz ≤-refl) (far (suc i)))))
          ...   | inj₂ (inj₁ sp) with back sp jk
          ...     | _ , rl′ , ik = ∈-++⁺ʳ ks (h′ ik kz (dep {z} {k} rl rl′ d))

    img-spin-o : ∀ {c z e₀} → TO.Cut c → Spun c z → o z e₀ → Σ (Ev B) λ e → Same e₀ e × JoinT z e
    img-spin-o cc sp oz with TO.silent cc sp oz
    ... | hush = skip , s-skip , step oz
    ... | held = pin _ , s-pin , opin oz

    module SpO {c} (cc : TO.Cut c) =
      Spreading o Same {c} (TO.shows cc) (img-spin-o cc) (in-o cc)
        (λ {z} {k} {e₀} {e} {e₀′} {e′} → same-dep {z = z} {k = k} {e₀ = e₀} {e₀′ = e₀′} {e = e} {e′ = e′})
        (entered-reach s p) (not-at-o cc)

    module SpL {q₀ a₀ s₀ c} (x₀ : o q₀ (out a₀)) (sl₀ : Sl q₀ a₀ s₀) (rn : Runs f o q₀) (nc : ¬ Cut f o q₀ c) (cl : TC x₀ sl₀ c) =
      Spreading (enter (f a₀) s₀) _≡_ {c} (Truth.shows (TL x₀ sl₀) cl)
        (λ sp lz → _ , refl , lane x₀ rn (mk sl₀ (lz , after x₀ sl₀ lz)) (unc-in x₀ sl₀ (lc⁼ x₀ sl₀ cl) nc (⊑-trans (⊑-snoc⁺ c) (proj₂ sp)))
                                   (work-silent (Truth.silent (TL x₀ sl₀) cl sp lz)))
        (λ sp jk → _ , refl , in-L x₀ sl₀ cl sp jk)
        (λ { refl refl d → d })
        (entered-reach (f a₀) s₀) (not-at-L x₀ sl₀ cl)

    spread : ∀ {c b} → InCut c → c ⊑ b → Few JoinT b → Spread c
    spread (inj₁ cc)                                  = SpO.spread cc
    spread (inj₂ (_ , _ , _ , x₀ , sl₀ , rn , nc , cl)) = SpL.spread x₀ sl₀ rn nc cl

    -- A pin past a cut whose connect leads it recurs under every spin row.
    again′ : ∀ {c w r} → InCut c → Jt w (pin r) → Lies c w → r ⊑ c → ∀ i → Σ Pos λ z → (c ⊕ [ ix i ]) ⊑ z × Jt z (pin r)
    again′ {c} {w} {r} ic (jw , rw) li rc i = go ic
      where
        F : Few JoinT r
        F = reach-pin (S.ins-J jw) rw

        sp : Spun c w
        sp = suc (proj₁ li) , proj₂ li

        go : InCut c → Σ Pos λ z → (c ⊕ [ ix i ]) ⊑ z × Jt z (pin r)
        go (inj₁ cc) with in-o cc sp jw
        ... | _ , s-pin , ow with TO.again cc ow li rc i
        ...   | z , cz , oz = z , cz , opin oz , S.reach-opin F oz
        go (inj₂ (_ , _ , _ , x₀ , sl₀ , rn , nc , cl)) with Truth.again (TL x₀ sl₀) cl (in-L x₀ sl₀ cl sp jw) li rc i
        ... | z , cz , lz = z , cz , lane x₀ rn (mk sl₀ (lz , after x₀ sl₀ lz)) (unc-in x₀ sl₀ (lc⁼ x₀ sl₀ cl) nc (⊑-trans (⊑-snoc⁺ c) cz)) tt
                          , S.reach-lane F x₀ sl₀ lz

    shows′ : ∀ {c} → Cut′ c → Spread c
    shows′ {c} (ic , y , e , (jy , ry) , li) = by e jy ry
      where
        cy : c ⊑ y
        cy = lies-⊑ li

        by : ∀ e → JoinT y e → Reach JoinT y e → Spread c
        by (out a) _  ry = spread ic cy (reach-few {e = out a} (λ {_} {_} → tt) ry)
        by skip    _  ry = spread ic cy (reach-few {e = skip} (λ {_} {_} → tt) ry)
        by end     _  ry = spread ic cy (reach-few {e = end} (λ {_} {_} → tt) ry)
        by (pin r) jy ry with ⊑-cmp c r cy (inside-⊑ r y (S.ins-J jy))
        ... | inj₁ cr = spread ic cr (reach-pin (S.ins-J jy) ry)
        ... | inj₂ rc = λ i → let (z , cz , jz) = again′ ic (jy , ry) li rc i in z , pin r , cz , jz

    silent′ : ∀ {c y e} → Cut′ c → Spun c y → Jt y e → Silent e
    silent′ (inj₁ cc , _) sp (jy , _) = same-silent (proj₁ (proj₂ (in-o cc sp jy)))
    silent′ (inj₂ (_ , _ , _ , x₀ , sl₀ , _ , _ , cl) , _) sp (jy , _) = Truth.silent (TL x₀ sl₀) cl sp (in-L x₀ sl₀ cl sp jy)

    -- A lane's cut the joining shows past: few before its subscription.
    wit-few : ∀ {q₀ a₀ s₀ c} (x₀ : o q₀ (out a₀)) (sl₀ : Sl q₀ a₀ s₀) → TC x₀ sl₀ c → (Σ Pos λ y → Σ (Ev B) λ e → Jt y e × Lies c y)
            → Few JoinT s₀
    wit-few {q₀} {a₀} {s₀} x₀ sl₀ cl (y , e , (jy , ry) , i , l) = by e (in-L x₀ sl₀ cl (suc i , l) jy) ry
      where
        by : ∀ e → enter (f a₀) s₀ y e → Reach JoinT y e → Few JoinT s₀
        s₀y : ∀ {e} → enter (f a₀) s₀ y e → s₀ ≼ y
        s₀y ly = ≺→≼ {s₀} {y} (after x₀ sl₀ ly)
        by (out a) ly ry = few-down (reach-few {e = out a} (λ {_} {_} → tt) ry) (s₀y ly)
        by skip    ly ry = few-down (reach-few {e = skip} (λ {_} {_} → tt) ry) (s₀y ly)
        by end     ly ry = few-down (reach-few {e = end} (λ {_} {_} → tt) ry) (s₀y ly)
        by (pin r) ly ry = few-down (reach-pin (proj₂ (InvAt.pinned (LI x₀ sl₀) ly)) ry) (pinned-after (LI x₀ sl₀) ly)

    ------------------------------------------------------------------------
    -- Few in the joining

    module FewAt {b : Pos} (F : Few JoinT b) where
      K : List Pos
      K = proj₁ F

      -- A row at or under `k` in the joining covers `k`.
      cov-img : ∀ {k y e} → k ≺ b → JoinT y e → k ⊑ y → Cov b K k
      cov-img {k} {y} kb jy ky with ≼-or-≻ b y
      ... | inj₂ yb = inj₂ (lead-∈ ky (proj₂ F jy yb))
      ... | inj₁ by with ≼-split {b} {y} by
      ...   | inj₁ b≺y = inj₁ (conv {k} {k} {b} {y} (⊑-refl k) (≺→≼ {k} {b} kb) b≺y ky)
      ...   | inj₂ refl = inj₁ ky

      -- Each outer row shows at or under itself.
      img-o : ∀ {k e} → o k e → ¬ ¬ (Σ Pos λ y → Σ (Ev B) λ e′ → JoinT y e′ × k ⊑ y)
      img-o {k} {out _} x ¬i = ¬i (k ⊕ [ ix 0 ] , skip , val x , ⊑-snoc⁺ k)
      img-o {k} {skip}  x ¬i = ¬i (k , skip , step x , ⊑-refl k)
      img-o {k} {pin _} x ¬i = ¬i (k , _ , opin x , ⊑-refl k)
      img-o {k} {end}   x    = em (λ d ¬i → ¬i (k , end , oend x d , ⊑-refl k)) (λ nd ¬i → ¬i (k , skip , opass x nd , ⊑-refl k))

      cov-o : ∀ {k e} → o k e → k ≺ b → Cov b K k
      cov-o x kb = cov-stable (λ ¬c → img-o x (λ { (_ , _ , jy , ky) → ¬c (cov-img kb jy ky) }))

      few-o : Few o b
      few-o = cov-few {X = o} {v = b} {ks = K} cov-o

      -- Each running lane's row, uncut, shows at or under itself.
      img-l : ∀ {q a s₁ k e} (x : o q (out a)) (sl : Sl q a s₁) → Runs f o q → enter (f a) s₁ k e → ¬ Cut f o q k
            → ¬ ¬ (Σ Pos λ y → Σ (Ev B) λ e′ → JoinT y e′ × k ⊑ y)
      img-l {k = k} {out _} x sl rn l nc ¬i = ¬i (k , _ , lane x rn (mk sl (l , after x sl l)) nc tt , ⊑-refl k)
      img-l {k = k} {skip}  x sl rn l nc ¬i = ¬i (k , _ , lane x rn (mk sl (l , after x sl l)) nc tt , ⊑-refl k)
      img-l {k = k} {pin _} x sl rn l nc ¬i = ¬i (k , _ , lane x rn (mk sl (l , after x sl l)) nc tt , ⊑-refl k)
      img-l {q} {a} {k = k} {end} x sl rn l nc =
        em (λ h ¬i → ¬i (k ⊕ [ ix 0 ] , skip , hand x rn ly nc h , ⊑-snoc⁺ k))
           (λ nh → em (λ d ¬i → ¬i (k , end , lend x rn ly nc nh d , ⊑-refl k)) (λ nd ¬i → ¬i (k , skip , lpass x rn ly nc nh nd , ⊑-refl k)))
        where
          ly : Ln f o q a k end
          ly = mk sl (l , after x sl l)

      cov-l : ∀ {q a s₁ k e} (x : o q (out a)) (sl : Sl q a s₁) → Runs f o q → enter (f a) s₁ k e → ¬ Cut f o q k → k ≺ b → Cov b K k
      cov-l x sl rn l nc kb = cov-stable (λ ¬c → img-l x sl rn l nc (λ { (_ , _ , jy , ky) → ¬c (cov-img kb jy ky) }))

      cov-left : ∀ {q a s₁ k r} (x : o q (out a)) (sl : Sl q a s₁) → Runs f o q → enter (f a) s₁ k (pin r) → ¬ Cut f o q r → k ≺ b
               → Cov b K k
      cov-left x sl rn l nr kb = cov-img kb (left x rn (mk sl (l , after x sl l)) nr (proj₂ (InvAt.pinned (LI x sl) l))) (⊑-refl _)

    -- Few before a lane's subscription: an end of a lane before it is
    -- clean, so the next's.  A cut it lay past would spin endlessly many
    -- joining rows before it.
    ends-at : ∀ {s₀} → Few JoinT s₀ → ∀ {q₂ a₂ s₂ c₂} (x₂ : o q₂ (out a₂)) (sl₂ : Sl q₂ a₂ s₂) → Runs f o q₂ → After (f a₂) s₂ c₂ end
            → c₂ ≺ s₀ → ¬ Cut f o q₂ c₂ → enter (f′ a₂) s₂ c₂ end
    ends-at {s₀} F {q₂} {a₂} {s₂} {c₂} x₂ sl₂ rn₂ (l₂ , _) c₂s₀ nc₂ = proj₁ (Truth.agree (TL x₂ sl₂) c₂ end clean) l₂
      where
        open FewAt F using (K; cov-l)

        nl : ∀ {k} → k ≼ c₂ → ¬ Lie (TC x₂ sl₂) k
        nl {k} kc (c* , ct , i , l) with where? c* c₂
        ... | inj₁ c₂c = ≺-irrefl {c₂} (≺-trans {c₂} {c* ⊕ [ ix 0 ]} {c₂} c₂c
                           (≺-≼-≺ {c* ⊕ [ ix 0 ]} {k} {c₂} (≺-≼-≺ {c* ⊕ [ ix 0 ]} {c* ⊕ [ ix (suc i) ]} {k} (ticks c* i) (⊑-≼ l)) kc))
        ... | inj₂ (inj₁ sp) = loud tt (Truth.silent (TL x₂ sl₂) ct sp l₂)
        ... | inj₂ (inj₂ far) = spin-few {s = c*} row F
          where
            row : ∀ j → Σ Pos λ z → Σ (Ev B) λ e → (c* ⊕ [ ix j ]) ⊑ z × JoinT z e × z ≺ s₀
            row j with Truth.shows (TL x₂ sl₂) ct j
            ... | z , e , cz , lz =
              z , e , cz , lane x₂ rn₂ (mk sl₂ (lz , after x₂ sl₂ lz)) (unc nc₂ (≺→≼ {z} {c₂} zc)) (work-silent (Truth.silent (TL x₂ sl₂) ct (j , cz) lz))
              , ≺-trans {z} {c₂} {s₀} zc c₂s₀
              where
                zc : z ≺ c₂
                zc = ≺-trans {z} {c* ⊕ [ ix (suc j) ]} {c₂} (below-next c* cz ≤-refl) (far (suc j))

        clean : Clean (TC x₂ sl₂) (enter (f a₂) s₂) c₂ end
        clean = nl (≼-refl {c₂}) , K , λ {k} lk kc _ →
          cov-down (cov-l x₂ sl₂ rn₂ lk (unc nc₂ (≺→≼ {k} {c₂} kc)) (≺-trans {k} {c₂} {s₀} kc c₂s₀)) kc (≺→≼ {c₂} {s₀} c₂s₀) , nl (≺→≼ {k} {c₂} kc)

    ------------------------------------------------------------------------
    -- Up to a clean bound

    module AtBound {b : Pos} (bf : Before Cut′ Jt b) (nl : ¬ Lie Cut′ b) where
      -- Hangs show, so the rows before the bound are few.
      fewJ : Few JoinT b
      fewJ = cover b ks , λ {k} jk kb → cov-∈ (cov-stable λ ¬c → ¬F (λ Fb → ¬c (proj₁ (proj₂ bf (jk , few-reach (few-down Fb (≺→≼ {k} {b} kb))) kb))))
        where
          ks : List Pos
          ks = proj₁ bf

          ¬F : ¬ ¬ Few JoinT b
          ¬F = shows-J (cover b ks , λ jk F kb → cov-∈ (proj₁ (proj₂ bf (jk , few-reach F) kb)))

      open FewAt fewJ public

      -- No position at or before the bound lies past one of the joining's cuts.
      clearJ : ∀ {y} → y ≼ b → ¬ Lie Cut′ y
      clearJ {y} yb (c , cc , i , l) with where? c b
      ... | inj₁ bc = ≺-irrefl {b} (≺-trans {b} {c ⊕ [ ix 0 ]} {b} bc
                        (≺-≼-≺ {c ⊕ [ ix 0 ]} {y} {b} (≺-≼-≺ {c ⊕ [ ix 0 ]} {c ⊕ [ ix (suc i) ]} {y} (ticks c i) (⊑-≼ l)) yb))
      ... | inj₂ (inj₁ (zero , sb)) =
        ≺-irrefl {b} (≺-≼-≺ {b} {y} {b} (≺-≼-≺ {b} {c ⊕ [ ix (suc i) ]} {y} (below-next c sb (s≤s z≤n)) (⊑-≼ l)) yb)
      ... | inj₂ (inj₁ (suc j , sb)) = nl (c , cc , j , sb)
      ... | inj₂ (inj₂ far) with shows′ cc 1
      ...   | z , _ , cz , jz = proj₂ (proj₂ bf jz (≺-trans {z} {c ⊕ [ ix 2 ]} {b} (below-next c cz ≤-refl) (far 2))) (c , cc , 0 , cz)

      -- An input's cut before the bound is the joining's.
      cut-of : ∀ {c} → InCut c → c ≺ b → Cut′ c
      cut-of {c} ic cb with spread ic (⊑-refl c) (few-down fewJ (≺→≼ {c} {b} cb)) 1
      ... | z , e , cz , jz = ic , z , e , jz , 0 , cz

      clearO : ∀ {y} → y ≼ b → ¬ Lie TO.Cut y
      clearO {y} yb (c , cc , l) = clearJ yb (c , cut-of (inj₁ cc) (≺-≼-≺ {c} {y} {b} (lies-≺ l) yb) , l)

      clearL : ∀ {q a s₁ y} (x : o q (out a)) (sl : Sl q a s₁) → Runs f o q → y ≼ b → (∀ {c} → c ⊑ y → ¬ Cut f o q c) → ¬ Lie (TC x sl) y
      clearL {q} {a} {s₁} {y} x sl rn yb nc (c , cl , l) =
        clearJ yb (c , cut-of (inj₂ (q , a , s₁ , x , sl , rn , nc (lies-⊑ l) , cl)) (≺-≼-≺ {c} {y} {b} (lies-≺ l) yb) , l)

      cleanO : ∀ {y e} → y ≼ b → Clean TO.Cut o y e
      cleanO {y} yb = clearO yb , K , λ {k} ok ky _ →
        cov-down (cov-o ok (≺-≼-≺ {k} {y} {b} ky yb)) ky yb , clearO (≼-trans {k} {y} {b} (≺→≼ {k} {y} ky) yb)

      agO : AgreeTo b o o′
      agO = ⟨ (λ {y} {e} yb → TO.agree y e (cleanO yb)) ⟩

      beforeO : Before TO.Cut o b
      beforeO = K , λ {k} ok kb → cov-o ok kb , clearO (≺→≼ {k} {b} kb)

      -- A lane uncut at `r`: clean before it, and not past a cut at it.
      beforeL : ∀ {q a s₁ r} (x : o q (out a)) (sl : Sl q a s₁) → Runs f o q → r ≼ b → ¬ Cut f o q r → Before (TC x sl) (enter (f a) s₁) r
      beforeL {r = r} x sl rn rb nr = K , λ {k} lk kr →
        cov-down (cov-l x sl rn lk (unc nr (≺→≼ {k} {r} kr)) (≺-≼-≺ {k} {r} {b} kr rb)) kr rb
        , clearL x sl rn (≼-trans {k} {r} {b} (≺→≼ {k} {r} kr) rb) (λ {c} ck → unc nr (≼-trans {c} {k} {r} (⊑-≼ ck) (≺→≼ {k} {r} kr)))

      nlL : ∀ {q a s₁ r} (x : o q (out a)) (sl : Sl q a s₁) → Runs f o q → r ≼ b → ¬ Cut f o q r → ¬ Lie (TC x sl) r
      nlL x sl rn rb nr = clearL x sl rn rb (λ ck → unc nr (⊑-≼ ck))

      lanes-at : ∀ {q a s₁ k} → o q (out a) → Sl q a s₁ → Runs f o q → k ≼ b → ¬ Cut f o q k → AgreeTo k (enter (f a) s₁) (enter (f′ a) s₁)
      lanes-at {q} {a} {s₁} {k} x sl rn kb nc = ⟨ (λ {y} {e} yk → Truth.agree (TL x sl) y e (clean yk)) ⟩
        where
          clean : ∀ {y e} → y ≼ k → Clean (TC x sl) (enter (f a) s₁) y e
          clean {y} yk = clearL x sl rn yb (λ {c} cy → unc nc (≼-trans {c} {y} {k} (⊑-≼ cy) yk)) , K , λ {k′} lk k′y _ →
              cov-down (cov-l x sl rn lk (unc nc (≺→≼ {k′} {k} (≺-≼-≺ {k′} {y} {k} k′y yk))) (≺-≼-≺ {k′} {y} {b} k′y yb)) k′y yb
            , clearL x sl rn (≼-trans {k′} {y} {b} (≺→≼ {k′} {y} k′y) yb)
                (λ {c} ck′ → unc nc (≼-trans {c} {k′} {k} (⊑-≼ ck′) (≺→≼ {k′} {k} (≺-≼-≺ {k′} {y} {k} k′y yk))))
            where yb = ≼-trans {y} {k} {b} yk kb

      -- A lane pin whose connect is uncut, at or before the bound.
      clean-left : ∀ {q a s₁ k r} (x : o q (out a)) (sl : Sl q a s₁) → Runs f o q → k ≼ b → ¬ Cut f o q r → W⁼ H s₁ r → T (inside r k)
                 → Clean (TC x sl) (enter (f a) s₁) k (pin r)
      clean-left {q} {a} {s₁} {k} {r} x sl rn kb nr r⁼ ins = clearL x sl rn kb (λ ck → uncut-under x sl nr r⁼ ck (inside-⊑ r k ins)) , K , dep
        where
          dep : ∀ {k′ e′} → enter (f a) s₁ k′ e′ → k′ ≺ k → Dep k (pin r) k′ e′ → Cov k K k′ × ¬ Lie (TC x sl) k′
          dep {k′} lk k′k d with d ins
          ... | inj₁ k′r = cov-down (cov-l x sl rn lk (unc nr (≺→≼ {k′} {r} k′r)) k′b) k′k kb
                         , clearL x sl rn (≺→≼ {k′} {b} k′b) (λ {c} ck′ → unc nr (≼-trans {c} {k′} {r} (⊑-≼ ck′) (≺→≼ {k′} {r} k′r)))
            where k′b = ≺-≼-≺ {k′} {k} {b} k′k kb
          ... | inj₂ refl = cov-down (cov-left x sl rn lk nr k′b) k′k kb
                          , clearL x sl rn (≺→≼ {k′} {b} k′b) (λ ck′ → uncut-under x sl nr r⁼ ck′ (inside-⊑ r k′ (proj₂ (InvAt.pinned (LI x sl) lk))))
            where k′b = ≺-≼-≺ {k′} {k} {b} k′k kb

      lanes-left : ∀ {q a s₁ k r} → o q (out a) → Sl q a s₁ → Runs f o q → k ≼ b → ¬ Cut f o q r → T (inside r k)
                 → (enter (f a) s₁ k (pin r) → enter (f′ a) s₁ k (pin r)) × (enter (f′ a) s₁ k (pin r) → enter (f a) s₁ k (pin r))
      lanes-left {q} {a} {s₁} {k} {r} x sl rn kb nr ins =
          (λ l → proj₁ (Truth.agree (TL x sl) k (pin r) (clean-left x sl rn kb nr (proj₁ (InvAt.pinned (LI x sl) l)) ins)) l)
        , (λ l′ → proj₂ (Truth.agree (TL x sl) k (pin r) (clean-left x sl rn kb nr (proj₁ (InvAt.pinned (If′ a s₁ (okS x sl)) l′)) ins)) l′)

      lanes : Lanes b
      lanes = mk-lanes lanes-at lanes-left

      agJ : AgreeTo b JoinT K′.JoinT
      agJ = agree b agO lanes

      agJt : AgreeTo b Jt Jt′
      agJt = trunc-to agJ

      fewJ′ : Few K′.JoinT b
      fewJ′ = few-ag agJ (≼-refl {b}) fewJ

    ------------------------------------------------------------------------
    -- The rows agree where clean

    -- Clean before itself: read up to itself.
    by-all : ∀ {q e} → Clean Cut′ Jt q e → (∀ {k e₀} → k ≺ q → Dep q e k e₀) → (Jt q e → Jt′ q e) × (Jt′ q e → Jt q e)
    by-all {q} cl dp = upto (AtBound.agJt {q} (before-of cl (≼-refl {q}) dp) (proj₁ cl)) (≼-refl {q})

    -- A pin: read up to its connect, and by hand at itself.
    module Pinned {q r} (ins : T (inside r q)) (cl : Clean Cut′ Jt q (pin r)) where
      rq : r ⊑ q
      rq = inside-⊑ r q ins

      open AtBound {r} (before-of cl (⊑-≼ rq) (λ kr _ → inj₁ kr)) (λ l → proj₁ cl (lie-up l rq))

      cks : List Pos
      cks = proj₁ (proj₂ cl)

      ch : ∀ {k e′} → Jt k e′ → k ≺ q → Dep q (pin r) k e′ → Cov q cks k × ¬ Lie Cut′ k
      ch = proj₂ (proj₂ cl)

      wide : ∀ {k} → Cov r K k → Cov q (K ++ cks) k
      wide c = cov-++ˡ (cov-lift c rq)

      cleanO-pin : ¬ Lie TO.Cut q → Clean TO.Cut o q (pin r)
      cleanO-pin nq = nq , K ++ cks , dep
        where
          dep : ∀ {k e₀} → o k e₀ → k ≺ q → Dep q (pin r) k e₀ → Cov q (K ++ cks) k × ¬ Lie TO.Cut k
          dep {k} ok kq d with d ins
          ... | inj₁ kr   = wide (cov-o ok kr) , clearO (≺→≼ {k} {r} kr)
          ... | inj₂ refl = cov-++ʳ (proj₁ hit) , λ { (c , cc , l) → proj₂ hit (c , (inj₁ cc , k , pin r , jk , l) , l) }
            where
              jk : Jt k (pin r)
              jk = opin ok , S.reach-opin fewJ ok
              hit = ch jk kq (λ _ → inj₂ refl)

      cleanL-pin : ∀ {q₂ a s₂} (x : o q₂ (out a)) (sl : Sl q₂ a s₂) → Runs f o q₂ → ¬ Cut f o q₂ r → W⁼ H s₂ r
                 → ¬ Lie (TC x sl) q → Clean (TC x sl) (enter (f a) s₂) q (pin r)
      cleanL-pin {q₂} {a} {s₂} x sl rn nr r⁼ nq = nq , K ++ cks , dep
        where
          dep : ∀ {k e′} → enter (f a) s₂ k e′ → k ≺ q → Dep q (pin r) k e′ → Cov q (K ++ cks) k × ¬ Lie (TC x sl) k
          dep {k} lk kq d with d ins
          ... | inj₁ kr   = wide (cov-l x sl rn lk (unc nr (≺→≼ {k} {r} kr)) kr)
                          , clearL x sl rn (≺→≼ {k} {r} kr) (λ {c} ck → unc nr (≼-trans {c} {k} {r} (⊑-≼ ck) (≺→≼ {k} {r} kr)))
          ... | inj₂ refl = cov-++ʳ (proj₁ hit)
                          , λ { (c , ct , l) → proj₂ hit (c , (inj₂ (q₂ , a , s₂ , x , sl , rn , uncut-under x sl nr r⁼ (lies-⊑ l) rk , ct) , k , pin r , jk , l) , l) }
            where
              ink : T (inside r k)
              ink = proj₂ (InvAt.pinned (LI x sl) lk)
              rk : r ⊑ k
              rk = inside-⊑ r k ink
              jk : Jt k (pin r)
              jk = left x rn (mk sl (lk , after x sl lk)) nr ink , S.reach-lane fewJ x sl lk
              hit = ch jk kq (λ _ → inj₂ refl)

      toL : ∀ {q₂ a s₂} (x : o q₂ (out a)) (sl : Sl q₂ a s₂) → Runs f o q₂ → enter (f a) s₂ q (pin r) → s₂ ≺ q → ¬ Cut f o q₂ r
          → Jt q (pin r) → Jt′ q (pin r)
      toL {q₂} {a} {s₂} x sl rn l aq nr jq = K′.left x′ rn′ (SL′.mk sl′ (l′ , aq)) nr′ ins , S′.reach-lane fewJ′ x′ sl′ l′
        where
          r⁼ : W⁼ H s₂ r
          r⁼ = proj₁ (InvAt.pinned (LI x sl) l)
          q₂r : q₂ ≼ r
          q₂r = val-pin x sl l
          nq : ¬ Lie (TC x sl) q
          nq (c , ct , li) = proj₁ cl (c , (inj₂ (q₂ , a , s₂ , x , sl , rn , uncut-under x sl nr r⁼ (lies-⊑ li) rq , ct) , q , pin r , jq , li) , li)
          l′ : enter (f′ a) s₂ q (pin r)
          l′ = proj₁ (Truth.agree (TL x sl) q (pin r) (cleanL-pin x sl rn nr r⁼ nq)) l
          x′ : o′ q₂ (out a)
          x′ = proj₁ (upto agO {q₂} q₂r) x
          sl′ : SL′.Sl q₂ a s₂
          sl′ = sl-to r agO lanes (pinned-after (LI x sl) l) sl
          rn′ : Runs f′ o′ q₂
          rn′ = runs-to r agO lanes q₂ q₂r rn
          nr′ : ¬ Cut f′ o′ q₂ r
          nr′ ct = nr (cut-from r agO q₂ r (≼-refl {r}) ct)

      to : Jt q (pin r) → Jt′ q (pin r)
      to jq@(opin x , _) = K′.opin x′ , S′.reach-opin fewJ′ x′
        where
          x′ : o′ q (pin r)
          x′ = proj₁ (TO.agree q (pin r) (cleanO-pin λ { (c , cc , l) → proj₁ cl (c , (inj₁ cc , q , pin r , jq , l) , l) })) x
      to jq@(lane x rn l nc _ , _) = let (_ , sl , (lq , aq)) = slot l in toL x sl rn lq aq (unc nc (⊑-≼ rq)) jq
      to jq@(left x rn l nr _ , _) = let (_ , sl , (lq , aq)) = slot l in toL x sl rn lq aq nr jq
      to (run () _ , _)

      fromL : ∀ {q₂ a s₂} (x′ : o′ q₂ (out a)) (sl′ : SL′.Sl q₂ a s₂) → Runs f′ o′ q₂ → enter (f′ a) s₂ q (pin r) → s₂ ≺ q
            → ¬ Cut f′ o′ q₂ r → Jt q (pin r)
      fromL {q₂} {a} {s₂} x′ sl′ rn′ l′ aq nr′ = left x rn (mk sl (l , aq)) nr ins , S.reach-lane fewJ x sl l
        where
          q₂r : q₂ ≼ r
          q₂r = val-pin′ x′ sl′ l′
          x : o q₂ (out a)
          x = proj₂ (upto agO {q₂} q₂r) x′
          sl : Sl q₂ a s₂
          sl = sl-from r agO lanes (pinned-after (LI′ x′ sl′) l′) sl′
          rn : Runs f o q₂
          rn = runs-from r agO lanes q₂ q₂r rn′
          nr : ¬ Cut f o q₂ r
          nr ct = nr′ (cut-to r agO q₂ r (≼-refl {r}) ct)
          r⁼ : W⁼ H s₂ r
          r⁼ = proj₁ (InvAt.pinned (LI′ x′ sl′) l′)
          nq : ¬ Lie (TC x sl) q
          nq (c , ct , li) with lie-split li rq
          ... | inj₁ lr = nlL x sl rn (≼-refl {r}) nr (c , ct , lr)
          ... | inj₂ rc with Truth.shadow (TL x sl) ct l′ li rc (beforeL x sl rn (≼-refl {r}) nr) (nlL x sl rn (≼-refl {r}) nr)
          ...   | z , z1 , lz = proj₁ cl (c , (inj₂ (q₂ , a , s₂ , x , sl , rn , uncut-under x sl nr r⁼ (⊑-refl c) rc , ct)
                                              , z , pin r , (left x rn (mk sl (lz , after x sl lz)) nr (proj₂ (InvAt.pinned (LI x sl) lz))
                                                            , S.reach-lane fewJ x sl lz)
                                              , 0 , z1) , li)
          l : enter (f a) s₂ q (pin r)
          l = proj₂ (Truth.agree (TL x sl) q (pin r) (cleanL-pin x sl rn nr r⁼ nq)) l′

      from : Jt′ q (pin r) → Jt q (pin r)
      from (K′.opin x′ , _) = opin x , S.reach-opin fewJ x
        where
          nq : ¬ Lie TO.Cut q
          nq (c , cc , li) with lie-split li rq
          ... | inj₁ lr = clearO (≼-refl {r}) (c , cc , lr)
          ... | inj₂ rc with TO.shadow cc x′ li rc beforeO (clearO (≼-refl {r}))
          ...   | z , z1 , oz = proj₁ cl (c , (inj₁ cc , z , pin r , (opin oz , S.reach-opin fewJ oz) , 0 , z1) , li)
          x : o q (pin r)
          x = proj₂ (TO.agree q (pin r) (cleanO-pin nq)) x′
      from (K′.lane x′ rn′ l′ nc′ _ , _) = let (_ , sl′ , (lq , aq)) = SL′.slot l′ in fromL x′ sl′ rn′ lq aq (λ ct → nc′ (cut-up′ ct (⊑-≼ rq)))
      from (K′.left x′ rn′ l′ nr′ _ , _) = let (_ , sl′ , (lq , aq)) = SL′.slot l′ in fromL x′ sl′ rn′ lq aq nr′
      from (K′.run () _ , _)

    agree′ : ∀ q e → Clean Cut′ Jt q e → (Jt q e → Jt′ q e) × (Jt′ q e → Jt q e)
    agree′ q (out _) cl = by-all cl (λ _ → tt)
    agree′ q skip    cl = by-all cl (λ _ → tt)
    agree′ q end     cl = by-all cl (λ _ → tt)
    agree′ q (pin r) cl with T? (inside r q)
    ... | no ni   = by-all cl (λ _ i → ⊥-elim (ni i))
    ... | yes ins = Pinned.to {q} {r} ins cl , Pinned.from {q} {r} ins cl

    ------------------------------------------------------------------------
    -- The next's pin past a cut, under its second spin row

    shadow′ : ∀ {c w r} → Cut′ c → Jt′ w (pin r) → Lies c w → r ⊑ c → Before Cut′ Jt r → ¬ Lie Cut′ r
            → Σ Pos λ z → (c ⊕ [ ix 1 ]) ⊑ z × Jt z (pin r)
    shadow′ {c} {w} {r} (ic , wit) (jw′ , _) li rc bf nl = go ic jw′
      where
        open AtBound bf nl

        -- No lane of the next reaches under an outer cut's spin.
        w1′ : ∀ {q a y m} → TO.Cut c → o′ q (out a) → Ln f′ o′ q a y (pin r) → (c ⊕ [ ix m ]) ⊑ y → ⊥
        w1′ {q} cc x′ l′ le with SL′.slot l′
        ... | _ , sl′ , (ly , _) with SL′.seat x′ sl′
        ...   | ρ , _ , xρ′ , ρq , ρW =
          w1 cc (proj₂ (upto agO {ρ} (≼-trans {ρ} {q} {r} ρq (val-pin′ x′ sl′ ly))) xρ′) (nest ρW (InvAt.world (LI′ x′ sl′) ly)) le

        go : InCut c → K′.JoinT w (pin r) → Σ Pos λ z → (c ⊕ [ ix 1 ]) ⊑ z × Jt z (pin r)
        go (inj₁ cc) (K′.opin x′) with TO.shadow cc x′ li rc beforeO (clearO (≼-refl {r}))
        ... | z , z1 , oz = z , z1 , opin oz , S.reach-opin fewJ oz
        go (inj₁ cc) (K′.lane x′ _ l′ _ _) = ⊥-elim (w1′ cc x′ l′ (proj₂ li))
        go (inj₁ cc) (K′.left x′ _ l′ _ _) = ⊥-elim (w1′ cc x′ l′ (proj₂ li))
        go (inj₁ cc) (K′.run () _)
        go (inj₂ (q₀ , a₀ , s₀ , x₀ , sl₀ , rn , nc , cl)) jw′ = lane-case jw′
          where
            c⁼ : W⁼ H s₀ c
            c⁼ = lc⁼ x₀ sl₀ cl

            cw : c ⊑ w
            cw = lies-⊑ li

            F₀ : Few JoinT s₀
            F₀ = wit-few x₀ sl₀ cl wit

            -- The value transfers: the lane is reached.
            ag₀ : AgreeTo q₀ o o′
            ag₀ = truth-lies To (FewAt.few-o (few-down F₀ (≺→≼ {q₀} {s₀} (past sl₀)))) (inj₂ (out a₀ , x₀ , tt))

            nr₀ : ¬ Cut f o q₀ r
            nr₀ = unc nc (⊑-≼ rc)

            mine : ∀ {q₂ a} → o′ q₂ (out a) → Ln f′ o′ q₂ a w (pin r) → Σ Pos λ z → (c ⊕ [ ix 1 ]) ⊑ z × Jt z (pin r)
            mine x′ l′ with Truth.shadow (TL x₀ sl₀) cl (one-lane x₀ sl₀ (TL x₀ sl₀) c⁼ cl li rc ag₀ agO lanes (ends-at F₀) x′ l′) li rc
                              (beforeL x₀ sl₀ rn (≼-refl {r}) nr₀) (nlL x₀ sl₀ rn (≼-refl {r}) nr₀)
            ... | z , z1 , lz = z , z1 , lane x₀ rn (mk sl₀ (lz , after x₀ sl₀ lz)) (unc-in x₀ sl₀ c⁼ nc (⊑-trans (⊑-snoc⁺ c) z1)) tt
                              , S.reach-lane fewJ x₀ sl₀ lz

            lane-case : K′.JoinT w (pin r) → Σ Pos λ z → (c ⊕ [ ix 1 ]) ⊑ z × Jt z (pin r)
            lane-case (K′.opin y′) =
              let (ρ , _ , xρ , ρq₀ , ρW) = seat x₀ sl₀ in ⊥-elim (InvAt.under Io′ (proj₁ (upto ag₀ {ρ} ρq₀) xρ) y′ plain-ix (nest⁼ ρW c⁼) cw)
            lane-case (K′.lane x′ _ l′ _ _) = mine x′ l′
            lane-case (K′.left x′ _ l′ _ _) = mine x′ l′
            lane-case (K′.run () _)

    truth : Truth Jt Jt′
    truth = record
      { Cut    = Cut′
      ; silent = silent′
      ; shows  = shows′
      ; again  = λ c → again′ (proj₁ c)
      ; shadow = shadow′
      ; agree  = agree′
      }

    placed : Placed H p Jt Jt′
    placed = placing truth λ { (inj₁ cc , _) → Placed.placed (R p ok) cc
                             ; (inj₂ (_ , _ , _ , x , sl , _ , _ , cl) , _) → nest⁼ (s-w⁼ x sl) (lc⁼ x sl cl) }
