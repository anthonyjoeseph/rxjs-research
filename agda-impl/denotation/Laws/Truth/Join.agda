{-# OPTIONS --guardedness #-}

-- A JOINER KEEPS THE TRUTH, over an outer and lanes each read against the
-- next.  The joiner's cuts are its inputs' cuts it shows a reached row
-- past the first spin row of: the outer's, and those of a lane it runs
-- uncut there.  Under such a cut its rows are that input's rows, at the
-- same positions (no other lane, value or outer row lies there), so the
-- spin shows silent; and once a row under it is reached, every spin row
-- is, through the rows it reached and the input's own (`Spreading`).
--
-- Up to a clean bound, every input cut few in the joiner is one of its
-- cuts, so no row at or before the bound lies past an input cut, and
-- the outer and the lanes read there each agree with the next
-- (`AtBound`); the joiner's policy carries that over.  A pin is read at
-- its connect and by hand at itself: its own input row, with the next's
-- shadow wherever its connect leads a cut.
module denotation.Laws.Truth.Join where

open import Data.Bool using (T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
import Data.List.Relation.Unary.Any.Properties as AnyP
open import Data.Maybe using (nothing)
open import Data.Nat using (zero; suc; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool.Properties using (T-≡)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable.Core using (T?)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Position using (Pos; ix; sub; last; _⊕_; inside; _≟ᵖ_)
open import denotation.Events using (<ᵖ-part)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Den; enter; Few; Dep; Reach; Truncate; Silent; hush; held;
  Work; LaneOf; _≺_; _≼_; module Joiner; module Switch; module Exhaust; module Op)
open import denotation.Read using (loud)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; AgreeTo-sym; ≺-trans; ≺→≼; ≼-refl; ≼-trans; ≼-or-≻; ≼-split; ≺-≼-≺; ≺-irrefl;
  ≺-ext; ticks; reach-few; entered-reach; trunc-to)
open import denotation.Laws.Count using (Cov; cov-down; cov-lift; cov-stable; em; pinned-after)
open import denotation.Laws.Shows using (ShowsK; k-shows; cover; cov-∈; cov-few; lead-∈; few-down; few-reach)
open import denotation.Laws.Worlds using (W; W⁼; inW; Ok; InvAt; InvD; Shows; _⊑_; ⊑-refl; ⊑-trans; ⊑-snoc; ⊑-snoc⁺; ⊑-cmp; ⊑-≼;
  conv; leads; plain-ix; ok-step; ok-in; world-after; inside-⊑; ⊕-assoc; ⊕-identityʳ; ⊕-injˡ; ⊕-injʳ; w-up; nest⁼; flat-under)
  renaming (step to wstep)
open import denotation.Laws.Worlds.Leaves using (out-inj)
import denotation.Laws.JoinInv as JI
open import denotation.Laws.JoinInv using (switch-cut-up)
import denotation.Laws.Join as LJ
import denotation.Laws.ShowsJoin as SJ
open import denotation.Laws.Truth using (Truth; Rel; Placed; placing; Spun; Lies; Lie; Clean; Before; lie-up; before-of; few-ag; truth-lies;
  where?; below-next)

-- A switch's cut, past a subtree no value lies under, falls before it.
switch-cut-in : ∀ {A B : Set} (f : A → Den B) (o : EmissionSet A) {q z w} → Switch.Cut f o q z → w ⊑ z
              → (∀ {y e} → o y e → w ⊑ y → ⊥) → Switch.Cut f o q w
switch-cut-in f o {w = w} (q′ , a′ , x , qq′ , q′z) wz nv with ≼-or-≻ w q′
... | inj₂ q′w = q′ , a′ , x , qq′ , q′w
... | inj₁ wq′ = ⊥-elim (nv x (conv {w} {w} {q′} (⊑-refl w) wq′ q′z wz))

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

-- An outer row under a spin, as a joiner shows it.
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

module Core {A B : Set} {H : Pos → Set} {f f′ : A → Den B} {s s′ : Den A}
            (Is : InvD H s) (Is′ : InvD H s′) (If : ∀ a → InvD H (f a)) (If′ : ∀ a → InvD H (f′ a))
            (R : Rel H s s′) (Rf : ∀ a → Rel H (f a) (f′ a)) (p : Pos) (ok : Ok H p) where
  o o′ : EmissionSet A
  o  = enter s p
  o′ = enter s′ p

  Io : InvAt H p o
  Io = Is p ok

  Io′ : InvAt H p o′
  Io′ = Is′ p ok

  To : Truth o o′
  To = Placed.tr (R p ok)

  module TO = Truth To

  val-ok : ∀ {q a} → o q (out a) → Ok H (q ⊕ [ ix 1 ])
  val-ok {q} x = ok-step q (ok-in ok (InvAt.world Io x) (InvAt.real Io x))

  val-ok′ : ∀ {q a} → o′ q (out a) → Ok H (q ⊕ [ ix 1 ])
  val-ok′ {q} x = ok-step q (ok-in ok (InvAt.world Io′ x) (InvAt.real Io′ x))

  L L′ : A → Pos → EmissionSet B
  L  a q = enter (f a) (q ⊕ [ ix 1 ])
  L′ a q = enter (f′ a) (q ⊕ [ ix 1 ])

  IL : ∀ {q a} → o q (out a) → InvAt H (q ⊕ [ ix 1 ]) (L a q)
  IL {q} {a} x = If a (q ⊕ [ ix 1 ]) (val-ok x)

  IL′ : ∀ {q a} → o′ q (out a) → InvAt H (q ⊕ [ ix 1 ]) (L′ a q)
  IL′ {q} {a} x = If′ a (q ⊕ [ ix 1 ]) (val-ok′ x)

  -- Each lane read against the next, at the value it runs for.
  PL : ∀ {q a} → o q (out a) → Placed H (q ⊕ [ ix 1 ]) (L a q) (L′ a q)
  PL {q} {a} x = Rf a (q ⊕ [ ix 1 ]) (val-ok x)

  TL : ∀ {q a} → o q (out a) → Truth (L a q) (L′ a q)
  TL x = Placed.tr (PL x)

  lc⁼ : ∀ {q a c} (x : o q (out a)) → Truth.Cut (TL x) c → W⁼ H (q ⊕ [ ix 1 ]) c
  lc⁼ x = Placed.placed (PL x)

  module JO  = JI.Join ok f If Io
  module JO′ = JI.Join ok f′ If′ Io′

  after : ∀ {q a k e} (x : o q (out a)) → L a q k e → (q ⊕ [ ix 1 ]) ≺ k
  after x l = world-after (InvAt.world (IL x) l) (InvAt.real (IL x) l)

  -- A lane pin's connect lies past its value.
  val-pin : ∀ {q a k r} (x : o q (out a)) → L a q k (pin r) → q ≼ r
  val-pin {q} {r = r} x l = ≺→≼ {q} {r} (≺-≼-≺ {q} {q ⊕ [ ix 1 ]} {r} (≺-ext q []) (pinned-after (IL x) l))

  val-pin′ : ∀ {q a k r} (x : o′ q (out a)) → L′ a q k (pin r) → q ≼ r
  val-pin′ {q} {r = r} x l = ≺→≼ {q} {r} (≺-≼-≺ {q} {q ⊕ [ ix 1 ]} {r} (≺-ext q []) (pinned-after (IL′ x) l))

  -- No outer row in a lane's world.
  no-o : ∀ {q a w y e} → o q (out a) → W⁼ H (q ⊕ [ ix 1 ]) w → o y e → w ⊑ y → ⊥
  no-o x w⁼ oy le = InvAt.under Io x oy plain-ix w⁼ le

  -- No value under an outer cut's spin, and no outer row at the cut.
  o-val-spun : ∀ {c y a} → TO.Cut c → Spun c y → o y (out a) → ⊥
  o-val-spun cc sp x = loud tt (TO.silent cc sp x)

  o-at-cut : ∀ {c e} → TO.Cut c → o c e → ⊥
  o-at-cut cc x with TO.shows cc 0
  ... | _ , _ , cz , oz = flat-under Io x oz cz

  -- No lane reaches under an outer cut's spin.
  w1 : ∀ {c q a y m} → TO.Cut c → o q (out a) → W H (q ⊕ [ ix 1 ]) y → (c ⊕ [ ix m ]) ⊑ y → ⊥
  w1 {c} {q} {m = m} cc x yw le with TO.shows cc m
  ... | _ , _ , cz , oz =
    leads (proj₂ ok) (wstep (Placed.placed (R p ok) cc) plain-ix) (λ v → InvAt.under Io x oz plain-ix v cz) nb (inW yw) le
    where
      nb : (c ⊕ [ ix m ]) ⊑ (q ⊕ [ ix 1 ]) → ⊥
      nb l with ⊑-snoc q l
      ... | inj₁ cq = o-val-spun cc (m , cq) x
      ... | inj₂ eq = o-at-cut cc (subst (λ w → o w (out _)) (sym (⊕-injˡ c q eq)) x)

  -- Either side's joiner: its pins wait only on rows of their own input.
  module Side (g : A → Den B) (u : EmissionSet A) (Iu : InvAt H p u) (Ig : ∀ a → InvD H (g a))
              (ur : ∀ {k e} → u k e → Reach u k e) (Rn : Pos → Set) (Ct : Pos → Pos → Set) where
    open Joiner g u Rn Ct using (JoinT; opin; lane; left; run)
    module JU = JI.Join ok g Ig Iu

    lpin : ∀ {q a k r} → u q (out a) → LaneOf g q a k (pin r) → W⁼ H (q ⊕ [ ix 1 ]) r × T (inside r k)
    lpin x l = InvAt.pinned (JU.LI x) (proj₁ l)

    -- A lane row under a lane's world is that lane's.
    same : ∀ {q₀ a₀ q a w y e} → u q₀ (out a₀) → W⁼ H (q₀ ⊕ [ ix 1 ]) w → u q (out a) → LaneOf g q a y e → w ⊑ y
         → enter (g a₀) (q₀ ⊕ [ ix 1 ]) y e
    same {q₀} {q = q} x₀ w⁼ x l le with q ≟ᵖ q₀
    ... | no ne = ⊥-elim (JU.kid-lane x₀ plain-ix w⁼ x (JU.lw x l) (λ eq → ne (sym (⊕-injˡ q₀ q eq))) le)
    ... | yes refl with out-inj (InvAt.func Iu x x₀)
    ...   | refl = proj₁ l

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
        pinned (lane x _ l _ _) _  = ⊥-elim (InvAt.under Iu x oz plain-ix (proj₁ (lpin x l)) (inside-⊑ r z ins))
        pinned (left x _ l _ _) _  = ⊥-elim (InvAt.under Iu x oz plain-ix (proj₁ (lpin x l)) (inside-⊑ r z ins))
        pinned (run () _) _

        go : ∀ {k e′} → JoinT k e′ → k ≺ z → Dep z (pin r) k e′ → k ∈ ks ++ ks′
        go jk kz d with d ins
        ... | inj₁ kr   = ∈-++⁺ˡ (h jk kr)
        ... | inj₂ refl = ∈-++⁺ʳ ks (pinned jk kz)

    -- A lane pin waits on rows before its connect and its lane's pins of it.
    reach-lane : ∀ {q a z r} → Few JoinT r → u q (out a) → enter (g a) (q ⊕ [ ix 1 ]) z (pin r) → Reach JoinT z (pin r)
    reach-lane {q} {a} {z} {r} (ks , h) x lz with entered-reach (g a) (q ⊕ [ ix 1 ]) lz
    ... | ks′ , h′ = ks ++ ks′ , go
      where
        r⁼ : W⁼ H (q ⊕ [ ix 1 ]) r
        r⁼ = proj₁ (InvAt.pinned (JU.LI x) lz)

        ins : T (inside r z)
        ins = proj₂ (InvAt.pinned (JU.LI x) lz)

        pinned : ∀ {k} → JoinT k (pin r) → k ≺ z → k ∈ ks′
        pinned {k} (opin ok′) _     = ⊥-elim (InvAt.under Iu x ok′ plain-ix r⁼ (inside-⊑ r k (proj₂ (InvAt.pinned Iu ok′))))
        pinned {k} (lane x′ _ l _ _) kz = h′ (same x r⁼ x′ l (inside-⊑ r k (proj₂ (lpin x′ l)))) kz (λ _ → inj₂ refl)
        pinned {k} (left x′ _ l _ _) kz = h′ (same x r⁼ x′ l (inside-⊑ r k (proj₂ (lpin x′ l)))) kz (λ _ → inj₂ refl)
        pinned (run () _) _

        go : ∀ {k e′} → JoinT k e′ → k ≺ z → Dep z (pin r) k e′ → k ∈ ks ++ ks′
        go jk kz d with d ins
        ... | inj₁ kr   = ∈-++⁺ˡ (h jk kr)
        ... | inj₂ refl = ∈-++⁺ʳ ks (pinned jk kz)

  -- A joiner's policy: which values run, where a lane is cut, and how
  -- agreeing inputs make agreeing joiners.
  module Policy (Runs : (A → Den B) → EmissionSet A → Pos → Set) (Cut : (A → Den B) → EmissionSet A → Pos → Pos → Set)
                (shows-J : Shows (Joiner.JoinT f o (Runs f o) (Cut f o)))
                (cut-up  : ∀ {q k y} → Cut f o q k → k ≼ y → Cut f o q y)
                (cut-up′ : ∀ {q k y} → Cut f′ o′ q k → k ≼ y → Cut f′ o′ q y)
                (cut-in  : ∀ {q z w} → Cut f o q z → w ⊑ z → (∀ {y e} → o y e → w ⊑ y → ⊥) → Cut f o q w)
                (agree   : ∀ Q → AgreeTo Q o o′ → LJ.Join.JoinerJ.Lanes {A} {B} Q Runs Cut o f f′
                         → AgreeTo Q (Joiner.JoinT f o (Runs f o) (Cut f o)) (Joiner.JoinT f′ o′ (Runs f′ o′) (Cut f′ o′)))
                (runs-to : ∀ Q → AgreeTo Q o o′ → LJ.Join.JoinerJ.Lanes {A} {B} Q Runs Cut o f f′ → ∀ q → q ≼ Q → Runs f o q → Runs f′ o′ q)
                (runs-from : ∀ Q → AgreeTo Q o o′ → LJ.Join.JoinerJ.Lanes {A} {B} Q Runs Cut o f f′ → ∀ q → q ≼ Q → Runs f′ o′ q → Runs f o q)
                (cut-to  : ∀ Q → AgreeTo Q o o′ → ∀ q k → k ≼ Q → Cut f o q k → Cut f′ o′ q k)
                (cut-from : ∀ Q → AgreeTo Q o o′ → ∀ q k → k ≼ Q → Cut f′ o′ q k → Cut f o q k) where
    open Joiner f o (Runs f o) (Cut f o) using (JoinT; val; step; opin; oend; opass; lane; lend; lpass; hand; left; run; rend; rpass; rhand)
    module K′ = Joiner f′ o′ (Runs f′ o′) (Cut f′ o′)
    module S  = Side f o Io If (entered-reach s p) (Runs f o) (Cut f o)
    module S′ = Side f′ o′ Io′ If′ (entered-reach s′ p) (Runs f′ o′) (Cut f′ o′)

    Jt Jt′ : EmissionSet B
    Jt  = Truncate JoinT
    Jt′ = Truncate K′.JoinT

    -- A lane's cut, the lane running and uncut there.
    LCut : Pos → Set
    LCut c = Σ Pos λ q → Σ A λ a → Σ (o q (out a)) λ x → Runs f o q × ¬ Cut f o q c × Truth.Cut (TL x) c

    InCut : Pos → Set
    InCut c = TO.Cut c ⊎ LCut c

    -- An input's cut the joiner shows a row past the first of.
    Cut′ : Pos → Set
    Cut′ c = InCut c × Σ Pos λ y → Σ (Ev B) λ e → Jt y e × Lies c y

    unc : ∀ {q k c} → ¬ Cut f o q k → c ≼ k → ¬ Cut f o q c
    unc nc ck ct = nc (cut-up ct ck)

    -- Uncut at a lane's pin's connect: uncut at whatever leads a row under it.
    uncut-under : ∀ {q a r c k} → o q (out a) → ¬ Cut f o q r → W⁼ H (q ⊕ [ ix 1 ]) r → c ⊑ k → r ⊑ k → ¬ Cut f o q c
    uncut-under {c = c} {k} x nr r⁼ ck rk with ⊑-cmp c _ ck rk
    ... | inj₁ cr = unc nr (⊑-≼ cr)
    ... | inj₂ rc = λ ct → nr (cut-in ct rc (no-o x r⁼))

    -- Uncut at a lane's cut: uncut under it.
    unc-in : ∀ {q a c z} → o q (out a) → W⁼ H (q ⊕ [ ix 1 ]) c → ¬ Cut f o q c → c ⊑ z → ¬ Cut f o q z
    unc-in x c⁼ nc cz ct = nc (cut-in ct cz (no-o x c⁼))

    ------------------------------------------------------------------------
    -- Under a cut

    -- Under an outer cut's spin, the joiner's rows are the outer's.
    in-o : ∀ {c y e} → TO.Cut c → Spun c y → JoinT y e → Σ (Ev A) λ e₀ → Same e₀ e × o y e₀
    in-o {c} cc (i , cy) (val {q} x) with ⊑-snoc q cy
    ... | inj₁ cq = ⊥-elim (o-val-spun cc (i , cq) x)
    ... | inj₂ eq = ⊥-elim (o-at-cut cc (subst (λ w → o w (out _)) (sym (⊕-injˡ c q eq)) x))
    in-o cc _  (step x)                = skip , s-skip , x
    in-o cc _  (opin x)                = pin _ , s-pin , x
    in-o cc sp (oend x _)              = ⊥-elim (loud tt (TO.silent cc sp x))
    in-o cc sp (opass x _)             = ⊥-elim (loud tt (TO.silent cc sp x))
    in-o cc (_ , cy) (lane x _ l _ _)    = ⊥-elim (w1 cc x (JO.lw x l) cy)
    in-o cc (_ , cy) (lend x _ l _ _ _)  = ⊥-elim (w1 cc x (JO.lw x l) cy)
    in-o cc (_ , cy) (lpass x _ l _ _ _) = ⊥-elim (w1 cc x (JO.lw x l) cy)
    in-o cc _  (hand _ _ _ _ ())
    in-o cc (_ , cy) (left x _ l _ _)    = ⊥-elim (w1 cc x (JO.lw x l) cy)
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
    ... | _ , _ , cz , oz = InvAt.under Io x oz plain-ix (inW (JO.lw x l)) (⊑-trans (⊑-snoc⁺ c) cz)
    not-at-o {c} cc (lend x _ l _ _ _) with TO.shows cc 0
    ... | _ , _ , cz , oz = InvAt.under Io x oz plain-ix (inW (JO.lw x l)) (⊑-trans (⊑-snoc⁺ c) cz)
    not-at-o {c} cc (lpass x _ l _ _ _) with TO.shows cc 0
    ... | _ , _ , cz , oz = InvAt.under Io x oz plain-ix (inW (JO.lw x l)) (⊑-trans (⊑-snoc⁺ c) cz)
    not-at-o cc (hand _ _ _ _ ())
    not-at-o {c} cc (left x _ l _ _) with TO.shows cc 0
    ... | _ , _ , cz , oz = InvAt.under Io x oz plain-ix (inW (JO.lw x l)) (⊑-trans (⊑-snoc⁺ c) cz)
    not-at-o cc (run () _)
    not-at-o cc (rend () _ _)
    not-at-o cc (rpass () _ _)
    not-at-o cc (rhand () _)

    -- Under a lane's cut's spin, the joiner's rows are that lane's.
    in-L : ∀ {q₀ a₀ c y e} (x₀ : o q₀ (out a₀)) → Truth.Cut (TL x₀) c → Spun c y → JoinT y e → L a₀ q₀ y e
    in-L {c = c} x₀ cl (i , cy) (val {q} x) with ⊑-snoc q cy
    ... | inj₁ cq = ⊥-elim (no-o x₀ (lc⁼ x₀ cl) x (⊑-trans (⊑-snoc⁺ c) cq))
    ... | inj₂ eq = ⊥-elim (no-o x₀ (lc⁼ x₀ cl) (subst (λ w → o w (out _)) (sym (⊕-injˡ c q eq)) x) (⊑-refl c))
    in-L {c = c} x₀ cl (_ , cy) (step x)    = ⊥-elim (no-o x₀ (lc⁼ x₀ cl) x (⊑-trans (⊑-snoc⁺ c) cy))
    in-L {c = c} x₀ cl (_ , cy) (opin x)    = ⊥-elim (no-o x₀ (lc⁼ x₀ cl) x (⊑-trans (⊑-snoc⁺ c) cy))
    in-L {c = c} x₀ cl (_ , cy) (oend x _)  = ⊥-elim (no-o x₀ (lc⁼ x₀ cl) x (⊑-trans (⊑-snoc⁺ c) cy))
    in-L {c = c} x₀ cl (_ , cy) (opass x _) = ⊥-elim (no-o x₀ (lc⁼ x₀ cl) x (⊑-trans (⊑-snoc⁺ c) cy))
    in-L {c = c} x₀ cl (_ , cy) (lane x _ l _ _) = S.same x₀ (lc⁼ x₀ cl) x l (⊑-trans (⊑-snoc⁺ c) cy)
    in-L {c = c} x₀ cl sp@(_ , cy) (lend x _ l _ _ _) =
      ⊥-elim (loud tt (Truth.silent (TL x₀) cl sp (S.same x₀ (lc⁼ x₀ cl) x l (⊑-trans (⊑-snoc⁺ c) cy))))
    in-L {c = c} x₀ cl sp@(_ , cy) (lpass x _ l _ _ _) =
      ⊥-elim (loud tt (Truth.silent (TL x₀) cl sp (S.same x₀ (lc⁼ x₀ cl) x l (⊑-trans (⊑-snoc⁺ c) cy))))
    in-L x₀ cl _ (hand _ _ _ _ ())
    in-L {c = c} x₀ cl (_ , cy) (left x _ l _ _) = S.same x₀ (lc⁼ x₀ cl) x l (⊑-trans (⊑-snoc⁺ c) cy)
    in-L x₀ cl _ (run () _)
    in-L x₀ cl _ (rend () _ _)
    in-L x₀ cl _ (rpass () _ _)
    in-L x₀ cl _ (rhand () _)

    not-at-L : ∀ {q₀ a₀ c e} (x₀ : o q₀ (out a₀)) → Truth.Cut (TL x₀) c → JoinT c e → ⊥
    not-at-L {q₀} x₀ cl (val {q} x) with w-up plain-ix (lc⁼ x₀ cl)
    ... | inj₁ eq = JI.ix10 (⊕-injʳ q₀ q eq)
    ... | inj₂ v  = no-o x₀ v x (⊑-refl q)
    not-at-L x₀ cl (step x)    = no-o x₀ (lc⁼ x₀ cl) x (⊑-refl _)
    not-at-L x₀ cl (opin x)    = no-o x₀ (lc⁼ x₀ cl) x (⊑-refl _)
    not-at-L x₀ cl (oend x _)  = no-o x₀ (lc⁼ x₀ cl) x (⊑-refl _)
    not-at-L x₀ cl (opass x _) = no-o x₀ (lc⁼ x₀ cl) x (⊑-refl _)
    not-at-L x₀ cl (lane x _ l _ _) with Truth.shows (TL x₀) cl 0
    ... | _ , _ , cz , lz = flat-under (IL x₀) (S.same x₀ (lc⁼ x₀ cl) x l (⊑-refl _)) lz cz
    not-at-L x₀ cl (lend x _ l _ _ _) with Truth.shows (TL x₀) cl 0
    ... | _ , _ , cz , lz = flat-under (IL x₀) (S.same x₀ (lc⁼ x₀ cl) x l (⊑-refl _)) lz cz
    not-at-L x₀ cl (lpass x _ l _ _ _) with Truth.shows (TL x₀) cl 0
    ... | _ , _ , cz , lz = flat-under (IL x₀) (S.same x₀ (lc⁼ x₀ cl) x l (⊑-refl _)) lz cz
    not-at-L x₀ cl (hand _ _ _ _ ())
    not-at-L x₀ cl (left x _ l _ _) with Truth.shows (TL x₀) cl 0
    ... | _ , _ , cz , lz = flat-under (IL x₀) (S.same x₀ (lc⁼ x₀ cl) x l (⊑-refl _)) lz cz
    not-at-L x₀ cl (run () _)
    not-at-L x₀ cl (rend () _ _)
    not-at-L x₀ cl (rpass () _ _)
    not-at-L x₀ cl (rhand () _)

    ------------------------------------------------------------------------
    -- A cut reached shows every spin row

    Spread : Pos → Set
    Spread c = ∀ i → Σ Pos λ z → Σ (Ev B) λ e → (c ⊕ [ ix i ]) ⊑ z × Jt z e

    -- An input `I` whose spin rows the joiner shows where they lie, and
    -- whose rows are the joiner's under the spin: past a bound under the
    -- cut few in the joiner, every spin row is reached, through the rows
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

    module SpL {q₀ a₀ c} (x₀ : o q₀ (out a₀)) (rn : Runs f o q₀) (nc : ¬ Cut f o q₀ c) (cl : Truth.Cut (TL x₀) c) =
      Spreading (L a₀ q₀) _≡_ {c} (Truth.shows (TL x₀) cl)
        (λ sp lz → _ , refl , lane x₀ rn (lz , after x₀ lz) (unc-in x₀ (lc⁼ x₀ cl) nc (⊑-trans (⊑-snoc⁺ c) (proj₂ sp)))
                                   (work-silent (Truth.silent (TL x₀) cl sp lz)))
        (λ sp jk → _ , refl , in-L x₀ cl sp jk)
        (λ { refl refl d → d })
        (entered-reach (f a₀) (q₀ ⊕ [ ix 1 ])) (not-at-L x₀ cl)

    spread : ∀ {c b} → InCut c → c ⊑ b → Few JoinT b → Spread c
    spread (inj₁ cc)                         = SpO.spread cc
    spread (inj₂ (_ , _ , x₀ , rn , nc , cl)) = SpL.spread x₀ rn nc cl

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
        go (inj₂ (_ , _ , x₀ , rn , nc , cl)) with Truth.again (TL x₀) cl (in-L x₀ cl sp jw) li rc i
        ... | z , cz , lz = z , cz , lane x₀ rn (lz , after x₀ lz) (unc-in x₀ (lc⁼ x₀ cl) nc (⊑-trans (⊑-snoc⁺ c) cz)) tt
                          , S.reach-lane F x₀ lz

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
    silent′ (inj₂ (_ , _ , x₀ , _ , _ , cl) , _) sp (jy , _) = Truth.silent (TL x₀) cl sp (in-L x₀ cl sp jy)

    -- A lane's cut the joiner shows past: its value few before.
    wit-few : ∀ {q₀ a₀ c} (x₀ : o q₀ (out a₀)) → Truth.Cut (TL x₀) c → (Σ Pos λ y → Σ (Ev B) λ e → Jt y e × Lies c y) → Few JoinT q₀
    wit-few {q₀} {a₀} x₀ cl (y , e , (jy , ry) , i , l) = by e (in-L x₀ cl (suc i , l) jy) ry
      where
        by : ∀ e → L a₀ q₀ y e → Reach JoinT y e → Few JoinT q₀
        q₀y : ∀ {e} → L a₀ q₀ y e → q₀ ≼ y
        q₀y ly = ≺→≼ {q₀} {y} (≺-trans {q₀} {q₀ ⊕ [ ix 1 ]} {y} (≺-ext q₀ []) (after x₀ ly))
        by (out a) ly ry = few-down (reach-few {e = out a} (λ {_} {_} → tt) ry) (q₀y ly)
        by skip    ly ry = few-down (reach-few {e = skip} (λ {_} {_} → tt) ry) (q₀y ly)
        by end     ly ry = few-down (reach-few {e = end} (λ {_} {_} → tt) ry) (q₀y ly)
        by (pin r) ly ry = few-down (reach-pin (proj₂ (InvAt.pinned (IL x₀) ly)) ry) (val-pin x₀ ly)

    ------------------------------------------------------------------------
    -- Few in the joiner

    module FewAt {b : Pos} (F : Few JoinT b) where
      K : List Pos
      K = proj₁ F

      -- A row at or under `k` in the joiner covers `k`.
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

      -- Each running lane's row, uncut, shows at itself.
      img-l : ∀ {q a k e} (x : o q (out a)) → Runs f o q → L a q k e → ¬ Cut f o q k → ¬ ¬ (Σ (Ev B) λ e′ → JoinT k e′)
      img-l {e = out _} x rn l nc ¬i = ¬i (_ , lane x rn (l , after x l) nc tt)
      img-l {e = skip}  x rn l nc ¬i = ¬i (_ , lane x rn (l , after x l) nc tt)
      img-l {e = pin _} x rn l nc ¬i = ¬i (_ , lane x rn (l , after x l) nc tt)
      img-l {e = end}   x rn l nc    =
        em (λ d ¬i → ¬i (_ , lend x rn (l , after x l) nc (λ ()) d)) (λ nd ¬i → ¬i (_ , lpass x rn (l , after x l) nc (λ ()) nd))

      cov-l : ∀ {q a k e} (x : o q (out a)) → Runs f o q → L a q k e → ¬ Cut f o q k → k ≺ b → Cov b K k
      cov-l x rn l nc kb = cov-stable (λ ¬c → img-l x rn l nc (λ { (_ , jk) → ¬c (cov-img kb jk (⊑-refl _)) }))

      cov-left : ∀ {q a k r} (x : o q (out a)) → Runs f o q → L a q k (pin r) → ¬ Cut f o q r → k ≺ b → Cov b K k
      cov-left x rn l nr kb = cov-img kb (left x rn (l , after x l) nr (proj₂ (InvAt.pinned (IL x) l))) (⊑-refl _)

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

      -- No position at or before the bound lies past one of the joiner's cuts.
      clearJ : ∀ {y} → y ≼ b → ¬ Lie Cut′ y
      clearJ {y} yb (c , cc , i , l) with where? c b
      ... | inj₁ bc = ≺-irrefl {b} (≺-trans {b} {c ⊕ [ ix 0 ]} {b} bc
                        (≺-≼-≺ {c ⊕ [ ix 0 ]} {y} {b} (≺-≼-≺ {c ⊕ [ ix 0 ]} {c ⊕ [ ix (suc i) ]} {y} (ticks c i) (⊑-≼ l)) yb))
      ... | inj₂ (inj₁ (zero , sb)) =
        ≺-irrefl {b} (≺-≼-≺ {b} {y} {b} (≺-≼-≺ {b} {c ⊕ [ ix (suc i) ]} {y} (below-next c sb (s≤s z≤n)) (⊑-≼ l)) yb)
      ... | inj₂ (inj₁ (suc j , sb)) = nl (c , cc , j , sb)
      ... | inj₂ (inj₂ far) with shows′ cc 1
      ...   | z , _ , cz , jz = proj₂ (proj₂ bf jz (≺-trans {z} {c ⊕ [ ix 2 ]} {b} (below-next c cz ≤-refl) (far 2))) (c , cc , 0 , cz)

      -- An input's cut before the bound is the joiner's.
      cut-of : ∀ {c} → InCut c → c ≺ b → Cut′ c
      cut-of {c} ic cb with spread ic (⊑-refl c) (few-down fewJ (≺→≼ {c} {b} cb)) 1
      ... | z , e , cz , jz = ic , z , e , jz , 0 , cz

      clearO : ∀ {y} → y ≼ b → ¬ Lie TO.Cut y
      clearO {y} yb (c , cc , l) = clearJ yb (c , cut-of (inj₁ cc) (≺-≼-≺ {c} {y} {b} (lies-≺ l) yb) , l)

      clearL : ∀ {q a y} (x : o q (out a)) → Runs f o q → y ≼ b → (∀ {c} → c ⊑ y → ¬ Cut f o q c) → ¬ Lie (Truth.Cut (TL x)) y
      clearL {q} {a} {y} x rn yb nc (c , cl , l) =
        clearJ yb (c , cut-of (inj₂ (q , a , x , rn , nc (lies-⊑ l) , cl)) (≺-≼-≺ {c} {y} {b} (lies-≺ l) yb) , l)

      cleanO : ∀ {y e} → y ≼ b → Clean TO.Cut o y e
      cleanO {y} yb = clearO yb , K , λ {k} ok ky _ →
        cov-down (cov-o ok (≺-≼-≺ {k} {y} {b} ky yb)) ky yb , clearO (≼-trans {k} {y} {b} (≺→≼ {k} {y} ky) yb)

      agO : AgreeTo b o o′
      agO = ⟨ (λ {y} {e} yb → TO.agree y e (cleanO yb)) ⟩

      beforeO : Before TO.Cut o b
      beforeO = K , λ {k} ok kb → cov-o ok kb , clearO (≺→≼ {k} {b} kb)

      -- A lane uncut at `r`: clean before it, and not past a cut at it.
      beforeL : ∀ {q a r} (x : o q (out a)) → Runs f o q → r ≼ b → ¬ Cut f o q r → Before (Truth.Cut (TL x)) (L a q) r
      beforeL {r = r} x rn rb nr = K , λ {k} lk kr →
        cov-down (cov-l x rn lk (unc nr (≺→≼ {k} {r} kr)) (≺-≼-≺ {k} {r} {b} kr rb)) kr rb
        , clearL x rn (≼-trans {k} {r} {b} (≺→≼ {k} {r} kr) rb) (λ {c} ck → unc nr (≼-trans {c} {k} {r} (⊑-≼ ck) (≺→≼ {k} {r} kr)))

      nlL : ∀ {q a r} (x : o q (out a)) → Runs f o q → r ≼ b → ¬ Cut f o q r → ¬ Lie (Truth.Cut (TL x)) r
      nlL x rn rb nr = clearL x rn rb (λ ck → unc nr (⊑-≼ ck))

      lanes-at : ∀ {q a k} → o q (out a) → Runs f o q → q ≼ b → k ≼ b → ¬ Cut f o q k → AgreeTo k (L a q) (L′ a q)
      lanes-at {q} {a} {k} x rn _ kb nc = ⟨ (λ {y} {e} yk → Truth.agree (TL x) y e (clean yk)) ⟩
        where
          clean : ∀ {y e} → y ≼ k → Clean (Truth.Cut (TL x)) (L a q) y e
          clean {y} yk = clearL x rn yb (λ {c} cy → unc nc (≼-trans {c} {y} {k} (⊑-≼ cy) yk)) , K , λ {k′} lk k′y _ →
              cov-down (cov-l x rn lk (unc nc (≺→≼ {k′} {k} (≺-≼-≺ {k′} {y} {k} k′y yk))) (≺-≼-≺ {k′} {y} {b} k′y yb)) k′y yb
            , clearL x rn (≼-trans {k′} {y} {b} (≺→≼ {k′} {y} k′y) yb)
                (λ {c} ck′ → unc nc (≼-trans {c} {k′} {k} (⊑-≼ ck′) (≺→≼ {k′} {k} (≺-≼-≺ {k′} {y} {k} k′y yk))))
            where yb = ≼-trans {y} {k} {b} yk kb

      -- A lane pin whose connect is uncut, at or before the bound.
      clean-left : ∀ {q a k r} (x : o q (out a)) → Runs f o q → k ≼ b → ¬ Cut f o q r → W⁼ H (q ⊕ [ ix 1 ]) r → T (inside r k)
                 → Clean (Truth.Cut (TL x)) (L a q) k (pin r)
      clean-left {q} {a} {k} {r} x rn kb nr r⁼ ins = clearL x rn kb (λ ck → uncut-under x nr r⁼ ck (inside-⊑ r k ins)) , K , dep
        where
          dep : ∀ {k′ e′} → L a q k′ e′ → k′ ≺ k → Dep k (pin r) k′ e′ → Cov k K k′ × ¬ Lie (Truth.Cut (TL x)) k′
          dep {k′} lk k′k d with d ins
          ... | inj₁ k′r = cov-down (cov-l x rn lk (unc nr (≺→≼ {k′} {r} k′r)) k′b) k′k kb
                         , clearL x rn (≺→≼ {k′} {b} k′b) (λ {c} ck′ → unc nr (≼-trans {c} {k′} {r} (⊑-≼ ck′) (≺→≼ {k′} {r} k′r)))
            where k′b = ≺-≼-≺ {k′} {k} {b} k′k kb
          ... | inj₂ refl = cov-down (cov-left x rn lk nr k′b) k′k kb
                          , clearL x rn (≺→≼ {k′} {b} k′b) (λ ck′ → uncut-under x nr r⁼ ck′ (inside-⊑ r k′ (proj₂ (InvAt.pinned (IL x) lk))))
            where k′b = ≺-≼-≺ {k′} {k} {b} k′k kb

      lanes-left : ∀ {q a k r} → o q (out a) → Runs f o q → q ≼ b → k ≼ b → ¬ Cut f o q r → T (inside r k)
                 → (L a q k (pin r) → L′ a q k (pin r)) × (L′ a q k (pin r) → L a q k (pin r))
      lanes-left {q} {a} {k} {r} x rn _ kb nr ins =
          (λ l → proj₁ (Truth.agree (TL x) k (pin r) (clean-left x rn kb nr (proj₁ (InvAt.pinned (IL x) l)) ins)) l)
        , (λ l′ → proj₂ (Truth.agree (TL x) k (pin r) (clean-left x rn kb nr (proj₁ (InvAt.pinned (If′ a (q ⊕ [ ix 1 ]) (val-ok x)) l′)) ins)) l′)

      lanes : LJ.Join.JoinerJ.Lanes {A} {B} b Runs Cut o f f′
      lanes = LJ.Join.JoinerJ.lanes lanes-at lanes-left

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

      cleanL-pin : ∀ {q₂ a} (x : o q₂ (out a)) → Runs f o q₂ → ¬ Cut f o q₂ r → W⁼ H (q₂ ⊕ [ ix 1 ]) r
                 → ¬ Lie (Truth.Cut (TL x)) q → Clean (Truth.Cut (TL x)) (L a q₂) q (pin r)
      cleanL-pin {q₂} {a} x rn nr r⁼ nq = nq , K ++ cks , dep
        where
          dep : ∀ {k e′} → L a q₂ k e′ → k ≺ q → Dep q (pin r) k e′ → Cov q (K ++ cks) k × ¬ Lie (Truth.Cut (TL x)) k
          dep {k} lk kq d with d ins
          ... | inj₁ kr   = wide (cov-l x rn lk (unc nr (≺→≼ {k} {r} kr)) kr)
                          , clearL x rn (≺→≼ {k} {r} kr) (λ {c} ck → unc nr (≼-trans {c} {k} {r} (⊑-≼ ck) (≺→≼ {k} {r} kr)))
          ... | inj₂ refl = cov-++ʳ (proj₁ hit)
                          , λ { (c , ct , l) → proj₂ hit (c , (inj₂ (q₂ , a , x , rn , uncut-under x nr r⁼ (lies-⊑ l) rk , ct) , k , pin r , jk , l) , l) }
            where
              ink : T (inside r k)
              ink = proj₂ (InvAt.pinned (IL x) lk)
              rk : r ⊑ k
              rk = inside-⊑ r k ink
              jk : Jt k (pin r)
              jk = left x rn (lk , after x lk) nr ink , S.reach-lane fewJ x lk
              hit = ch jk kq (λ _ → inj₂ refl)

      toL : ∀ {q₂ a} (x : o q₂ (out a)) → Runs f o q₂ → L a q₂ q (pin r) → (q₂ ⊕ [ ix 1 ]) ≺ q → ¬ Cut f o q₂ r → Jt q (pin r)
          → Jt′ q (pin r)
      toL {q₂} {a} x rn l aq nr jq = K′.left x′ rn′ (l′ , aq) nr′ ins , S′.reach-lane fewJ′ x′ l′
        where
          r⁼ : W⁼ H (q₂ ⊕ [ ix 1 ]) r
          r⁼ = proj₁ (InvAt.pinned (IL x) l)
          q₂r : q₂ ≼ r
          q₂r = val-pin x l
          nq : ¬ Lie (Truth.Cut (TL x)) q
          nq (c , ct , li) = proj₁ cl (c , (inj₂ (q₂ , a , x , rn , uncut-under x nr r⁼ (lies-⊑ li) rq , ct) , q , pin r , jq , li) , li)
          l′ : L′ a q₂ q (pin r)
          l′ = proj₁ (Truth.agree (TL x) q (pin r) (cleanL-pin x rn nr r⁼ nq)) l
          x′ : o′ q₂ (out a)
          x′ = proj₁ (upto agO {q₂} q₂r) x
          rn′ : Runs f′ o′ q₂
          rn′ = runs-to r agO lanes q₂ q₂r rn
          nr′ : ¬ Cut f′ o′ q₂ r
          nr′ ct = nr (cut-from r agO q₂ r (≼-refl {r}) ct)

      to : Jt q (pin r) → Jt′ q (pin r)
      to jq@(opin x , _) = K′.opin x′ , S′.reach-opin fewJ′ x′
        where
          x′ : o′ q (pin r)
          x′ = proj₁ (TO.agree q (pin r) (cleanO-pin λ { (c , cc , l) → proj₁ cl (c , (inj₁ cc , q , pin r , jq , l) , l) })) x
      to jq@(lane x rn l nc _ , _) = toL x rn (proj₁ l) (proj₂ l) (unc nc (⊑-≼ rq)) jq
      to jq@(left x rn l nr _ , _) = toL x rn (proj₁ l) (proj₂ l) nr jq
      to (run () _ , _)

      fromL : ∀ {q₂ a} (x′ : o′ q₂ (out a)) → Runs f′ o′ q₂ → LaneOf f′ q₂ a q (pin r) → ¬ Cut f′ o′ q₂ r → Jt q (pin r)
      fromL {q₂} {a} x′ rn′ (l′ , aq) nr′ = left x rn (l , aq) nr ins , S.reach-lane fewJ x l
        where
          q₂r : q₂ ≼ r
          q₂r = val-pin′ x′ l′
          x : o q₂ (out a)
          x = proj₂ (upto agO {q₂} q₂r) x′
          rn : Runs f o q₂
          rn = runs-from r agO lanes q₂ q₂r rn′
          nr : ¬ Cut f o q₂ r
          nr ct = nr′ (cut-to r agO q₂ r (≼-refl {r}) ct)
          r⁼ : W⁼ H (q₂ ⊕ [ ix 1 ]) r
          r⁼ = proj₁ (InvAt.pinned (IL′ x′) l′)
          nq : ¬ Lie (Truth.Cut (TL x)) q
          nq (c , ct , li) with lie-split li rq
          ... | inj₁ lr = nlL x rn (≼-refl {r}) nr (c , ct , lr)
          ... | inj₂ rc with Truth.shadow (TL x) ct l′ li rc (beforeL x rn (≼-refl {r}) nr) (nlL x rn (≼-refl {r}) nr)
          ...   | z , z1 , lz = proj₁ cl (c , (inj₂ (q₂ , a , x , rn , uncut-under x nr r⁼ (⊑-refl c) rc , ct)
                                              , z , pin r , (left x rn (lz , after x lz) nr (proj₂ (InvAt.pinned (IL x) lz)) , S.reach-lane fewJ x lz)
                                              , 0 , z1) , li)
          l : L a q₂ q (pin r)
          l = proj₂ (Truth.agree (TL x) q (pin r) (cleanL-pin x rn nr r⁼ nq)) l′

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
      from (K′.lane x′ rn′ l′ nc′ _ , _) = fromL x′ rn′ l′ (λ ct → nc′ (cut-up′ ct (⊑-≼ rq)))
      from (K′.left x′ rn′ l′ nr′ _ , _) = fromL x′ rn′ l′ nr′
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

        go : InCut c → K′.JoinT w (pin r) → Σ Pos λ z → (c ⊕ [ ix 1 ]) ⊑ z × Jt z (pin r)
        go (inj₁ cc) (K′.opin x′) with TO.shadow cc x′ li rc beforeO (clearO (≼-refl {r}))
        ... | z , z1 , oz = z , z1 , opin oz , S.reach-opin fewJ oz
        go (inj₁ cc) (K′.lane x′ _ l′ _ _) = ⊥-elim (w1 cc (proj₂ (upto agO (val-pin′ x′ (proj₁ l′))) x′) (JO′.lw x′ l′) (proj₂ li))
        go (inj₁ cc) (K′.left x′ _ l′ _ _) = ⊥-elim (w1 cc (proj₂ (upto agO (val-pin′ x′ (proj₁ l′))) x′) (JO′.lw x′ l′) (proj₂ li))
        go (inj₁ cc) (K′.run () _)
        go (inj₂ (q₀ , a₀ , x₀ , rn , nc , cl)) jw′ = lane-case jw′
          where
            c⁼ : W⁼ H (q₀ ⊕ [ ix 1 ]) c
            c⁼ = lc⁼ x₀ cl

            cw : c ⊑ w
            cw = lies-⊑ li

            -- The value transfers: the lane is reached.
            x₀′ : o′ q₀ (out a₀)
            x₀′ = proj₁ (upto (truth-lies To (FewAt.few-o (wit-few x₀ cl wit)) (inj₂ (out a₀ , x₀ , tt))) (≼-refl {q₀})) x₀

            nr₀ : ¬ Cut f o q₀ r
            nr₀ = unc nc (⊑-≼ rc)

            mine : ∀ {q₂ a} → o′ q₂ (out a) → LaneOf f′ q₂ a w (pin r) → Σ Pos λ z → (c ⊕ [ ix 1 ]) ⊑ z × Jt z (pin r)
            mine x′ l′ with Truth.shadow (TL x₀) cl (S′.same x₀′ c⁼ x′ l′ cw) li rc (beforeL x₀ rn (≼-refl {r}) nr₀) (nlL x₀ rn (≼-refl {r}) nr₀)
            ... | z , z1 , lz = z , z1 , lane x₀ rn (lz , after x₀ lz) (unc-in x₀ c⁼ nc (⊑-trans (⊑-snoc⁺ c) z1)) tt , S.reach-lane fewJ x₀ lz

            lane-case : K′.JoinT w (pin r) → Σ Pos λ z → (c ⊕ [ ix 1 ]) ⊑ z × Jt z (pin r)
            lane-case (K′.opin y′)          = ⊥-elim (InvAt.under Io′ x₀′ y′ plain-ix c⁼ cw)
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
                             ; (inj₂ (_ , _ , x , _ , _ , cl) , _) → nest⁼ (inW (JO.sw x)) (lc⁼ x cl) }

------------------------------------------------------------------------
-- The joiners

merge-truth : ∀ {A B H} {f f′ : A → Den B} {s s′ : Den A}
            → InvD H s → InvD H s′ → (∀ a → InvD H (f a)) → (∀ a → InvD H (f′ a))
            → (∀ m q → Ok H q → ShowsK m (enter s q)) → (∀ m a q → Ok H q → ShowsK m (enter (f a) q))
            → Rel H s s′ → (∀ a → Rel H (f a) (f′ a)) → Rel H (Op.flatMap (mergeᶠ nothing) f s) (Op.flatMap (mergeᶠ nothing) f′ s′)
merge-truth {A} {B} {H} {f} {f′} {s} {s′} Is Is′ If If′ sk-o sk-f R Rf p ok =
  Core.Policy.placed {A} {B} {H} {f} {f′} {s} {s′} Is Is′ If If′ R Rf p ok (λ _ _ _ → ⊤) (λ _ _ _ _ → ⊥)
    (k-shows (λ n → SJ.Flat.sk-merge {A} {B} {H} {n} s f Is If p ok (sk-o n p ok) (λ a q okq → sk-f n a q okq)))
    (λ ()) (λ ()) (λ ())
    (λ Q → LJ.Join.MergeJ.agree {A} {B} Q) (λ _ _ _ _ _ _ → tt) (λ _ _ _ _ _ _ → tt) (λ _ _ _ _ _ ()) (λ _ _ _ _ _ ())

switch-truth : ∀ {A B H} {f f′ : A → Den B} {s s′ : Den A}
             → InvD H s → InvD H s′ → (∀ a → InvD H (f a)) → (∀ a → InvD H (f′ a))
             → (∀ m q → Ok H q → ShowsK m (enter s q)) → (∀ m a q → Ok H q → ShowsK m (enter (f a) q))
             → Rel H s s′ → (∀ a → Rel H (f a) (f′ a)) → Rel H (Op.flatMap switchᶠ f s) (Op.flatMap switchᶠ f′ s′)
switch-truth {A} {B} {H} {f} {f′} {s} {s′} Is Is′ If If′ sk-o sk-f R Rf p ok =
  Core.Policy.placed {A} {B} {H} {f} {f′} {s} {s′} Is Is′ If If′ R Rf p ok (λ _ _ _ → ⊤) (λ g u → Switch.Cut g u)
    (k-shows (λ n → SJ.Flat.sk-switch {A} {B} {H} {n} s f Is If p ok (sk-o n p ok) (λ a q okq → sk-f n a q okq)))
    (λ {q} {k} {y} → switch-cut-up f (enter s p) {q} {k} {y}) (λ {q} {k} {y} → switch-cut-up f′ (enter s′ p) {q} {k} {y})
    (λ {q} {z} {w} → switch-cut-in f (enter s p) {q} {z} {w})
    (λ Q → LJ.Join.SwitchJ.agree {A} {B} Q) (λ _ _ _ _ _ _ → tt) (λ _ _ _ _ _ _ → tt)
    (λ Q ao → LJ.Join.SwitchJ.cut-to {A} {B} Q {f} {f′} {enter s p} {enter s′ p} ao)
    (λ Q ao → LJ.Join.SwitchJ.cut-to {A} {B} Q {f′} {f} {enter s′ p} {enter s p} (AgreeTo-sym ao))

exhaust-truth : ∀ {A B H} {f f′ : A → Den B} {s s′ : Den A}
              → InvD H s → InvD H s′ → (∀ a → InvD H (f a)) → (∀ a → InvD H (f′ a))
              → (∀ m q → Ok H q → ShowsK m (enter s q)) → (∀ m a q → Ok H q → ShowsK m (enter (f a) q))
              → Rel H s s′ → (∀ a → Rel H (f a) (f′ a)) → Rel H (Op.flatMap exhaustᶠ f s) (Op.flatMap exhaustᶠ f′ s′)
exhaust-truth {A} {B} {H} {f} {f′} {s} {s′} Is Is′ If If′ sk-o sk-f R Rf p ok =
  Core.Policy.placed {A} {B} {H} {f} {f′} {s} {s′} Is Is′ If If′ R Rf p ok (λ g u → Exhaust.Run g u) (λ _ _ _ _ → ⊥)
    (k-shows (λ n → SJ.Flat.sk-exhaust {A} {B} {H} {n} s f Is If p ok (sk-o n p ok) (λ a q okq → sk-f n a q okq)))
    (λ ()) (λ ()) (λ ())
    (λ Q → LJ.Join.ExhaustJ.agree {A} {B} Q) (λ Q → LJ.Join.ExhaustJ.runs-to {A} {B} Q)
    (λ Q ao L q qQ → LJ.Join.ExhaustJ.cur-from {A} {B} Q ao L q q qQ)
    (λ _ _ _ _ _ ()) (λ _ _ _ _ _ ())
