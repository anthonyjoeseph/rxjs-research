{-# OPTIONS --guardedness #-}

-- A CONNECT SHOWS ITS BODY.  Every row a reader of a connect meets is its
-- body's, in the same order: the source's rows show only silent, at their
-- first effects, and a body row the connect drops has a source past every
-- bound before it, which the next row met would wait on too.  So a connect
-- holds what its body holds, its body's burst lying in its own.
module simultaneous.HeldConnect where

open import Data.Bool using (T; true; false; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import denotation.Events using (Pos; ix; sub; last; Timeline; root; fresh; _≟ᵖ_; inside)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; skip; pin; Den; hot; enter; Proper; _≺_; _≼_; module Op;
  module Connect; module Connecting)
open import denotation.Read using (Run; []; _∷_; Visible)
open import denotation.Laws.Modulus using (≺-trans; ≺-≼-≺; ≼-≺-≺; ≼-refl; ≺→≼; ≺-ext; entered-few; entered-reach)
open import denotation.Laws.Worlds using (Ok; InvD; InvAt; Lawful; Real; TimerRoot; _⊕_; ok-step; _⊑_; inside-⊑; ⊑-snoc⁺; ⊑-trans)
open import denotation.Laws.Connect using () renaming (lawful to src-lawful; ok₀ to body-ok)
open import adequacy.Up using (conn-reach)
open import simultaneous.InstEmit using (instEmit; value; mark)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Relations using (Met)
open import simultaneous.Routed using (Held; Sync; Ex)
open import simultaneous.Relabel using (Same; same-mark; same-value; Rows≈; []; _∷_; ev-out; ev-end; held-same)

open import simultaneous.SObs using (module Elaborate)
open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (IE)

------------------------------------------------------------------------
-- Positions

-- A subscription past a timer's root keeps its instant one label down.
inst-snoc : ∀ p l → Real p → (TimerRoot p → ⊥) → instantOf (p ++ [ l ]) ≡ instantOf p
inst-snoc (ix i ∷ [])                 (ix _)  _ _ = refl
inst-snoc (ix i ∷ [])                 (sub _) _ _ = refl
inst-snoc (ix i ∷ [])                 last    _ _ = refl
inst-snoc (ix i ∷ ix _ ∷ [])          l       _ _ = refl
inst-snoc (ix i ∷ last ∷ [])          l       _ _ = refl
inst-snoc (ix i ∷ sub _ ∷ [])         l       _ nt = ⊥-elim (nt tt)
inst-snoc (ix i ∷ ix _ ∷ _ ∷ _)       l       _ _ = refl
inst-snoc (ix i ∷ last ∷ _ ∷ _)       l       _ _ = refl
inst-snoc (ix i ∷ sub _ ∷ _ ∷ _)      l       _ _ = refl

⊑-≼ : ∀ {x y} → x ⊑ y → x ≼ y
⊑-≼ {x} ([] , refl) yx = ≼-refl {x} (subst (λ z → z ≺ x) (++-[] x) yx)
  where
    ++-[] : ∀ (x : Pos) → x ++ [] ≡ x
    ++-[] []      = refl
    ++-[] (a ∷ x) = cong (a ∷_) (++-[] x)
⊑-≼ {x} (l ∷ ys , refl) = ≺→≼ {x} (≺-ext x ys)

-- The body's burst lies in the connect's.
sync-body : ∀ {p y} → Real p → (TimerRoot p → ⊥) → Sync (p ++ [ ix 0 ]) y → Sync p y
sync-body {p} {y} rp nt (i , eq) =
  subst T (sym (inside⇒ (⊑-trans (⊑-snoc⁺ p) (inside-⊑ _ y i)))) tt , trans eq (inst-snoc p (ix 0) rp nt)
  where
    inside⇒ : ∀ {x z} → x ⊑ z → inside x z ≡ true
    inside⇒ {x} {z} le with inside x z in e
    ... | true  = refl
    ... | false = ⊥-elim (subst T e (denotation.Laws.Worlds.⊑-inside le))

-- Fewer bursts exempt, the same stream holds.
held-ex : ∀ {A} {t : EmissionSet (IE A)} {cs cs′} → (∀ {y} → Ex cs′ y → Ex cs y) → Held t cs′ → Held t cs
held-ex wd H = record
  { named   = Held.named H
  ; covered = λ m r₁ r₂ e c nx → Held.covered H m r₁ r₂ e c (λ x → nx (wd x))
  ; exact   = Held.exact H
  ; routing = Held.routing H
  ; shut    = Held.shut H }

------------------------------------------------------------------------
-- Runs

-- A position's parent, one label up.
up : Pos → Pos
up []          = []
up (_ ∷ [])    = []
up (a ∷ b ∷ x) = a ∷ up (b ∷ x)

up-snoc : ∀ (y : Pos) l → up (y ++ [ l ]) ≡ y
up-snoc []          l = refl
up-snoc (a ∷ [])    l = refl
up-snoc (a ∷ b ∷ y) l = cong (a ∷_) (up-snoc (b ∷ y) l)

-- A visible row waits on every row before it.
vis-dep : ∀ {A} {q} {e : Ev A} → Visible e → ∀ {k e′} → denotation.EmissionSet.Dep q e k e′
vis-dep {e = out _} _ = tt
vis-dep {e = end}   _ = tt

module ConnRun {A B : Set} {H : Pos → Set} (s : Den A) (F : Den A → Den B)
               (Is : InvD H s) (IF : ∀ {t} → Lawful t → InvD (H ⊕ t) (F (hot t))) (p : Pos) (ok : Ok H p) where
  open Connect s F p using (σ; β; r; ConnT; Alive; body; burst; echo; kept)

  C : EmissionSet B
  C = enter (Op.connect s F) p

  Iσ : InvAt H r σ
  Iσ = Is r (ok-step p ok)

  Iβ : InvAt (H ⊕ Proper σ) (p ++ [ ix 0 ]) β
  Iβ = IF (src-lawful {s = s} {F = F} Is IF p ok) (p ++ [ ix 0 ]) (body-ok {s = s} {F = F} Is IF p ok)

  -- A visible body row lies before the body's end.
  before-end : ∀ {q e c} → β q e → Visible e → β c end → q ≼ c
  before-end x v ce cq with InvAt.quiet Iβ ce x cq
  before-end {e = out _} x v ce cq | _ , () , _
  before-end {e = end}   x v ce cq | _ , () , _

  -- Before a visible body row, the body runs.
  alive′ : ∀ {q e} → β q e → Visible e → ∀ k → k ≺ q → Alive k
  alive′ x v k kq ce = ≺-≼-≺ {k} kq (before-end x v ce)

  -- Before a visible body row, every source row shows.
  shows : ∀ {q e} → β q e → Visible e → ∀ {y e′} → σ y e′ → (y ++ [ ix 0 ]) ≺ q → Σ (Ev B) (ConnT (y ++ [ ix 0 ]))
  shows {q} x v {y} {e′} sy lt with inside r y in ins
  ... | true  = _ , burst sy (subst T (sym ins) tt)
  ... | false with e′
  ...   | out _ = _ , echo sy (alive′ x v y (≺-trans {y} (≺-ext y []) lt)) tt (subst T (sym (cong not ins)) tt)
  ...   | skip  = _ , echo sy (alive′ x v y (≺-trans {y} (≺-ext y []) lt)) tt (subst T (sym (cong not ins)) tt)
  ...   | end   = _ , echo sy (alive′ x v y (≺-trans {y} (≺-ext y []) lt)) tt (subst T (sym (cong not ins)) tt)
  ...   | pin p′ = _ , kept sy (λ ce → ≼-≺-≺ {p′} {y} (⊑-≼ (inside-⊑ p′ y (proj₂ (InvAt.pinned Iσ sy))))
                                         (alive′ x v y (≺-trans {y} (≺-ext y []) lt) ce))
                       (subst T (sym (cong not ins)) tt) (proj₂ (InvAt.pinned Iσ sy))

  -- A body row before a visible connect row is the connect's.
  lift : ∀ {q e} → C q e → Visible e → ∀ {k e′} → β k e′ → k ≺ q → C k e′
  lift {q} (body x , ks , rc) v {k} xk kq =
    body xk , conn-reach {r = p} {σ = σ} {β = β} few (entered-reach (F (hot (Proper σ))) (p ++ [ ix 0 ]) xk)
    where
      few : Σ (List Pos) λ ys → ∀ {y e″} → σ y e″ → (y ++ [ ix 0 ]) ≺ k → y ∈ ys
      few = L.map up ks , λ {y} sy lt →
        let (_ , cy) = shows x v sy (≺-trans {y ++ [ ix 0 ]} lt kq)
        in subst (_∈ L.map up ks) (up-snoc y (ix 0)) (∈-map⁺ up (rc cy (≺-trans {y ++ [ ix 0 ]} lt kq) (vis-dep v)))
  lift (burst _ _ , _) () _ _
  lift (echo _ _ _ _ , _) () _ _
  lift (kept _ _ _ _ , _) () _ _

  -- Every run met of the connect is met of its body.
  back : ∀ {c rs} → Run C c rs → Run β c rs
  back [] = []
  back ((((x@(body y , _) , pr) , _) , vi , aft , lst) ∷ run) =
    (((y , λ ce → before-end y vi ce) , entered-few (F (hot (Proper σ))) (p ++ [ ix 0 ]) (vis-dep vi) y) , vi , aft ,
      λ {k} xk vk ak kq → lst (lift x vi xk kq) vk ak kq) ∷ back run
  back (((((burst _ _ , _) , _) , _) , () , _) ∷ _)
  back (((((echo _ _ _ _ , _) , _) , _) , () , _) ∷ _)
  back (((((kept _ _ _ _ , _) , _) , _) , () , _) ∷ _)

------------------------------------------------------------------------
-- Held through a connect

same-refl : ∀ {A} (x : IE A) → Same x x
same-refl (instEmit (value _) _) = same-value
same-refl (instEmit (mark _) _)  = same-mark

rows-refl : ∀ {A} {c} {t : EmissionSet (IE A)} {rs} → Run t c rs → Rows≈ rs rs
rows-refl []                                = []
rows-refl (_∷_ {e = out x} (_ , _ , _) run) = ev-out (same-refl x) ∷ rows-refl run
rows-refl (_∷_ {e = end}   (_ , _ , _) run) = ev-end ∷ rows-refl run
rows-refl (_∷_ {e = skip}  (_ , () , _) _)
rows-refl (_∷_ {e = pin _} (_ , () , _) _)

held-conn : ∀ {A B} {H : Pos → Set} (s : Den A) (F : Den A → Den (IE B))
            (Is : InvD H s) (IF : ∀ {t} → Lawful t → InvD (H ⊕ t) (F (hot t))) p (ok : Ok H p) (nt : TimerRoot p → ⊥) cs
          → Held (enter (F (hot (Proper (enter s (p ++ [ ix 1 ]))))) (p ++ [ ix 0 ])) ((p ++ [ ix 0 ]) ∷ p ∷ cs)
          → Held (enter (Op.connect s F) p) (p ∷ cs)
held-conn s F Is IF p ok nt cs h = held-same row back′ (held-ex ex h)
  where
    open ConnRun s F Is IF p ok

    ex : ∀ {y} → Ex ((p ++ [ ix 0 ]) ∷ p ∷ cs) y → Ex (p ∷ cs) y
    ex (here sy) = here (sync-body (proj₁ ok) nt sy)
    ex (there x) = x

    row : ∀ {y x′} → C y (out x′) → Σ _ λ x → Connect.β s F p y (out x) × Same x′ x
    row (Connecting.body y , _) = _ , y , same-refl _

    back′ : ∀ {rs′} → Met C rs′ → Σ _ λ rs → Met (Connect.β s F p) rs × Rows≈ rs′ rs
    back′ m = _ , back m , rows-refl m
