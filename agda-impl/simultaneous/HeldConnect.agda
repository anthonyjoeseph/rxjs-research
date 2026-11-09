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
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Relation.Nullary.Decidable using (decidable-stable)
open import Data.Sum using (inj₁; inj₂)
open import Data.List.Relation.Unary.Any using (here; there; any?)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import denotation.Position using (Pos; Path; ix; root; _≟ᵖ_; inside; _⊕_; _∙_; _<ᵖ_)
open import denotation.Events using (Timeline; fresh; finals)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; skip; pin; Den; hot; enter; Proper; _≺_; _≼_; module Op;
  module Connect; module Connecting; Few; Reach; Dep; PDep; Unpinned)
open import Relation.Nullary using (¬_)
open import denotation.Read using (Run; []; _∷_; Visible)
open import denotation.Laws.Modulus using (≺-absurd; ≺-trans; ≺-≼-≺; ≼-≺-≺; ≼-refl; ≺→≼; ≺-ext; entered-few; entered-reach)
open import denotation.Laws.Worlds using (Shows; full; Ok; InvD; InvAt; Lawful; _∪ʰ_; ok-step; _⊑_; inside-⊑; ⊑-snoc⁺; ⊑-trans; ⊑-inside; world-after; world-after⁼; in-world; ⊕-assoc; ⊕-identityʳ)
open import denotation.Laws.Connect using () renaming (lawful to src-lawful; ok₀ to body-ok)
open import adequacy.Up using (conn-reach)
open import simultaneous.InstEmit using (instEmit; value; mark)
open import simultaneous.Readings using (emission)
open import simultaneous.Relations using (Met)
open import simultaneous.Routed using (Held; Sync; Ex; Early; Before; Valued; opos)
open import denotation.Events using (<ᵖ-apart; <ᵖ-shift; <ᵖ-next)
open import Data.Bool.Properties using (T-≡)
open import Function.Bundles using (Equivalence)
open import simultaneous.Relabel using (Same; same-mark; same-value; Rows≈; []; _∷_; ev-out; ev-end; held-same)

open import simultaneous.SObs using (module Elaborate)
open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) finals using (IE)

------------------------------------------------------------------------
-- Positions

-- An effect keeps its cause's emission.
emission-ext : ∀ p zs → emission (p ⊕ zs) ≡ emission p
emission-ext (_ ∙ _) _ = refl

-- What lies before an over, all it causes does.
before-ext : ∀ {y o} zs → Before y o → Before (y ⊕ zs) o
before-ext {y} {o} zs (lt , ns) =
  Equivalence.from T-≡ (<ᵖ-apart y o zs (Equivalence.to T-≡ lt) λ ys e → ns (ys , e)) ,
  λ { (ws , e) → ns (zs ++ ws , trans e (⊕-assoc y zs ws)) }

-- What an early position causes is as early.
early-inst : ∀ {p} zs → Early p → Early (p ⊕ zs)
early-inst {p} zs ep v =
  subst (λ I → Before (p ⊕ zs) (opos I)) (sym eq) (before-ext zs (ep (subst Valued eq v)))
  where eq = emission-ext p zs

⊑-≼ : ∀ {x y} → x ⊑ y → x ≼ y
⊑-≼ {x} ([] , refl) yx = ≼-refl {x} (subst (λ z → z ≺ x) (⊕-identityʳ x) yx)
⊑-≼ {x} (l ∷ ys , refl) = ≺→≼ {x} (≺-ext x ys)

-- The body's burst lies in the connect's.
sync-body : ∀ {p y} → Sync (p ⊕ [ ix 0 ]) y → Sync p y
sync-body {p} {y} (i , eq) =
  subst T (sym (inside⇒ (⊑-trans (⊑-snoc⁺ p) (inside-⊑ _ y i)))) tt , trans eq (emission-ext p [ ix 0 ])
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
  ; shut    = Held.shut H
  ; early   = Held.early H
  ; ends    = Held.ends H
  ; late    = Held.late H
  ; idle    = Held.idle H }

------------------------------------------------------------------------
-- Runs

-- A position's parent, one label up.
upᵗ : Path → Path
upᵗ []          = []
upᵗ (_ ∷ [])    = []
upᵗ (a ∷ b ∷ x) = a ∷ upᵗ (b ∷ x)

up : Pos → Pos
up (i ∙ p) = i ∙ upᵗ p

upᵗ-snoc : ∀ (y : Path) l → upᵗ (y ++ [ l ]) ≡ y
upᵗ-snoc []          l = refl
upᵗ-snoc (a ∷ [])    l = refl
upᵗ-snoc (a ∷ b ∷ y) l = cong (a ∷_) (upᵗ-snoc (b ∷ y) l)

up-snoc : ∀ (y : Pos) l → up (y ⊕ [ l ]) ≡ y
up-snoc (i ∙ y) l = cong (i ∙_) (upᵗ-snoc y l)

-- A visible row waits on every row before it.
vis-dep : ∀ {A} {q} {e : Ev A} → Visible e → ∀ {k e′} → denotation.EmissionSet.Dep q e k e′
vis-dep {e = out _} _ = tt
vis-dep {e = end}   _ = tt

-- One step past each keeps the order.
shift : ∀ z′ z → (z′ ⊕ [ ix 0 ]) ≺ (z ⊕ [ ix 0 ]) → z′ ≺ z
shift z′ z lt with z′ <ᵖ z in e
... | true  = tt
... | false = ⊥-elim (subst T (<ᵖ-shift z′ z e) lt)

next : ∀ z′ z → z′ ≺ z → (z′ ⊕ [ ix 0 ]) ≺ (z ⊕ [ ix 0 ])
next z′ z lt = Equivalence.from T-≡ (<ᵖ-next z′ z (ix 0) (Equivalence.to T-≡ lt))

module ConnRun {A B : Set} {H : Pos → Set} (s : Den A) (F : Den A → Den B)
               (Is : InvD H s) (IF : ∀ {t} → Lawful t → InvD (H ∪ʰ t) (F (hot t))) (p : Pos) (ok : Ok H p)
               (sh : Shows (enter s (p ⊕ [ ix 1 ]))) where
  open Connect s F p using (σ; β; r; ConnT; Alive; body; burst; echo; kept)

  C : EmissionSet B
  C = enter (Op.connect s F) p

  Iσ : InvAt H r σ
  Iσ = Is r (ok-step p ok)

  Iβ : InvAt (H ∪ʰ Proper σ) (p ⊕ [ ix 0 ]) β
  Iβ = IF (src-lawful {s = s} {F = F} Is IF p ok) (p ⊕ [ ix 0 ]) (body-ok {s = s} {F = F} Is IF p ok)

  -- A visible body row lies before the body's end.
  before-end : ∀ {q e c} → β q e → Visible e → β c end → q ≼ c
  before-end x v ce cq with InvAt.quiet Iβ ce x cq
  before-end {e = out _} x v ce cq | _ , () , _
  before-end {e = end}   x v ce cq | _ , () , _

  -- Before a visible body row, the body runs.
  alive′ : ∀ {q e} → β q e → Visible e → ∀ k → k ≺ q → Alive k
  alive′ x v k kq ce = ≺-≼-≺ {k} kq (before-end x v ce)

  -- Before a visible body row, every source row shows.
  shows : ∀ {q e} → β q e → Visible e → ∀ {y e′} → σ y e′ → (y ⊕ [ ix 0 ]) ≺ q → Σ (Ev B) (ConnT (y ⊕ [ ix 0 ]))
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
    body xk , conn-reach {r = p} {σ = σ} {β = β} few (entered-reach (F (hot (Proper σ))) (p ⊕ [ ix 0 ]) xk)
    where
      few : Σ (List Pos) λ ys → ∀ {y e″} → σ y e″ → (y ⊕ [ ix 0 ]) ≺ k → y ∈ ys
      few = L.map up ks , λ {y} sy lt →
        let (_ , cy) = shows x v sy (≺-trans {y ⊕ [ ix 0 ]} lt kq)
        in subst (_∈ L.map up ks) (up-snoc y (ix 0)) (∈-map⁺ up (rc cy (≺-trans {y ⊕ [ ix 0 ]} lt kq) (vis-dep v)))
  lift (burst _ _ , _) () _ _
  lift (echo _ _ _ _ , _) () _ _
  lift (kept _ _ _ _ , _) () _ _

  -- Every row of the connect lies past it.
  σ-past : ∀ {k e} → σ k e → p ≺ k
  σ-past {k} x = ≺-trans {p} {r} {k} (≺-ext p []) (world-after (InvAt.world Iσ x) (InvAt.real Iσ x))

  past-p : ∀ {k e} → ConnT k e → p ≺ k
  past-p {k} (body x)         = ≺-trans {p} {p ⊕ [ ix 0 ]} {k} (≺-ext p []) (world-after (InvAt.world Iβ x) (InvAt.real Iβ x))
  past-p (burst {k} x _)      = ≺-trans {p} {k} {k ⊕ [ ix 0 ]} (σ-past x) (≺-ext k [])
  past-p (echo {k} x _ _ _)   = ≺-trans {p} {k} {k ⊕ [ ix 0 ]} (σ-past x) (≺-ext k [])
  past-p (kept {k} x _ _ _)   = ≺-trans {p} {k} {k ⊕ [ ix 0 ]} (σ-past x) (≺-ext k [])

  -- No pin of the source's or the body's is the connect's own.
  σ-pin : ∀ {k} → σ k (pin p) → ⊥
  σ-pin x = world-after⁼ (proj₁ (InvAt.pinned Iσ x)) (proj₁ ok) (≺-ext p [])

  β-pin : ∀ {k} → β k (pin p) → ⊥
  β-pin x = world-after⁼ (proj₁ (InvAt.pinned Iβ x)) (proj₁ ok) (≺-ext p [])

  -- The source's rows shown in the connect.
  SD : ∀ {k e} → ConnT k e → Set
  SD (body _) = ⊥
  SD _        = ⊤

  -- A body row waits on its body's rows, and on the source's it is told.
  body-reach : ∀ {b e} → β b e → (L : List Pos) → (∀ {k e′} (x : ConnT k e′) → SD x → k ≺ b → Dep b e k e′ → k ∈ L) → Reach ConnT b e
  body-reach y L h = proj₁ Rb ++ L , λ
    { (body x)         lt d → ∈-++⁺ˡ (proj₂ Rb x lt d)
    ; x@(burst _ _)    lt d → ∈-++⁺ʳ (proj₁ Rb) (h x tt lt d)
    ; x@(echo _ _ _ _) lt d → ∈-++⁺ʳ (proj₁ Rb) (h x tt lt d)
    ; x@(kept _ _ _ _) lt d → ∈-++⁺ʳ (proj₁ Rb) (h x tt lt d) }
    where Rb = entered-reach (F (hot (Proper σ))) (p ⊕ [ ix 0 ]) y

  -- A burst row waits on the bursts before it, which the source's rows
  -- before it give.
  burst-reach : ∀ {z e′} → σ z e′ → T (inside r z) → (L : List Pos) → (∀ {z′ e″} → σ z′ e″ → z′ ≺ z → z′ ∈ L)
              → Reach ConnT (z ⊕ [ ix 0 ]) (pin p)
  burst-reach {z} x i L h = L.map (_⊕ [ ix 0 ]) L , cov
    where
      ip : T (inside p (z ⊕ [ ix 0 ]))
      ip = ⊑-inside (⊑-trans (⊑-trans (⊑-snoc⁺ p) (inside-⊑ r z i)) (⊑-snoc⁺ z))

      below : ∀ {k e″} → ConnT k e″ → k ≺ p → ⊥
      below x′ kp = ≺-absurd {p} (past-p x′) kp

      cov : ∀ {k e″} → ConnT k e″ → k ≺ (z ⊕ [ ix 0 ]) → Dep (z ⊕ [ ix 0 ]) (pin p) k e″ → k ∈ L.map (_⊕ [ ix 0 ]) L
      cov x′@(body y) lt d with d ip
      ... | inj₁ kp   = ⊥-elim (below x′ kp)
      ... | inj₂ refl = ⊥-elim (β-pin y)
      cov (burst {k′} y _) lt _ = ∈-map⁺ (_⊕ [ ix 0 ]) (h y (shift k′ z lt))
      cov x′@(echo _ _ _ _) lt d with d ip
      ... | inj₁ kp = ⊥-elim (below x′ kp)
      ... | inj₂ ()
      cov x′@(kept y _ _ _) lt d with d ip
      ... | inj₁ kp   = ⊥-elim (below x′ kp)
      ... | inj₂ refl = ⊥-elim (σ-pin y)

  -- A HANG SHOWS IN A CONNECT: before a position few of its rows precede,
  -- every row of the connect is one of them.  A burst row waits only on
  -- the bursts before it, so the source's showing its hangs reaches it;
  -- every other row waits on few of the source's, and on body rows those
  -- reach.
  module Seen {w} (Fw : Few C w) where
    ks : List Pos
    ks = proj₁ Fw

    inC : ∀ {k e} → ConnT k e → Reach ConnT k e → k ≺ w → k ∈ ks
    inC x rc kw = proj₂ Fw (x , rc) kw

    burst-in : ∀ {z e′} → σ z e′ → (i : T (inside r z)) → (z ⊕ [ ix 0 ]) ≺ w → ¬ ¬ ((z ⊕ [ ix 0 ]) ∈ ks)
    burst-in {z} x i zw no = sh (L.map up ks , good) λ (Ls , hs) → no (inC (burst x i) (burst-reach x i Ls hs) zw)
      where
        good : ∀ {k e} → σ k e → Few σ k → k ≺ z → k ∈ L.map up ks
        good {k} y (Lk , hk) kz = subst (_∈ L.map up ks) (up-snoc k (ix 0))
          (∈-map⁺ up (inC (burst y (in-world Iσ y kz i)) (burst-reach y (in-world Iσ y kz i) Lk hk)
                          (≺-trans {k ⊕ [ ix 0 ]} {z ⊕ [ ix 0 ]} {w} (next k z kz) zw)))

    echo-in : ∀ {z e′} → σ z e′ → (a : Alive z) (u : Unpinned e′) (ni : T (not (inside r z))) → (z ⊕ [ ix 0 ]) ≺ w
            → (z ⊕ [ ix 0 ]) ∈ ks
    echo-in {z} x a u ni zw = inC (echo x a u ni) (Lσ ++ ks , cov) zw
      where
        Rz = entered-reach s r x
        Lσ = L.map (_⊕ [ ix 0 ]) (proj₁ Rz)

        inLz : ∀ {z′ e″} → σ z′ e″ → z′ ≺ z → (z′ ⊕ [ ix 0 ]) ∈ Lσ
        inLz {z′} y lt = ∈-map⁺ (_⊕ [ ix 0 ]) (proj₂ Rz y lt (full u))

        sd : ∀ {k e″} (x′ : ConnT k e″) → SD x′ → k ≺ (z ⊕ [ ix 0 ]) → k ∈ Lσ
        sd (burst {k′} y _)    _ lt = inLz y (shift k′ z lt)
        sd (echo {k′} y _ _ _) _ lt = inLz y (shift k′ z lt)
        sd (kept {k′} y _ _ _) _ lt = inLz y (shift k′ z lt)

        cov : ∀ {k e″} → ConnT k e″ → k ≺ (z ⊕ [ ix 0 ]) → Dep (z ⊕ [ ix 0 ]) skip k e″ → k ∈ (Lσ ++ ks)
        cov {k} (body y) lt _ =
          ∈-++⁺ʳ Lσ (inC (body y) (body-reach y Lσ λ {k′} x′ t lt′ _ → sd x′ t (≺-trans {k′} {k} {z ⊕ [ ix 0 ]} lt′ lt))
                        (≺-trans {k} {z ⊕ [ ix 0 ]} {w} lt zw))
        cov x′@(burst _ _)    lt _ = ∈-++⁺ˡ (sd x′ tt lt)
        cov x′@(echo _ _ _ _) lt _ = ∈-++⁺ˡ (sd x′ tt lt)
        cov x′@(kept _ _ _ _) lt _ = ∈-++⁺ˡ (sd x′ tt lt)

    kept-in : ∀ {z p′} → σ z (pin p′) → (a : Alive p′) (ni : T (not (inside r z))) (i : T (inside p′ z)) → (z ⊕ [ ix 0 ]) ≺ w
            → (z ⊕ [ ix 0 ]) ∈ ks
    kept-in {z} {p′} x a ni i zw = inC (kept x a ni i) (Lσ ++ ks , cov) zw
      where
        Rz = entered-reach s r x
        Lσ = L.map (_⊕ [ ix 0 ]) (proj₁ Rz)

        i′ : T (inside p′ (z ⊕ [ ix 0 ]))
        i′ = ⊑-inside (⊑-trans (inside-⊑ p′ z i) (⊑-snoc⁺ z))

        inLz : ∀ {z′ e″} → σ z′ e″ → z′ ≺ z → PDep p′ z′ e″ → (z′ ⊕ [ ix 0 ]) ∈ Lσ
        inLz y lt pd = ∈-map⁺ (_⊕ [ ix 0 ]) (proj₂ Rz y lt λ _ → pd)

        -- A source row shown before a point waiting on `p′`'s past is in it.
        sd : ∀ {k e″} (x′ : ConnT k e″) → SD x′ → k ≺ (z ⊕ [ ix 0 ]) → PDep p′ k e″ → k ∈ Lσ
        sd (burst {k′} y _) _ lt (inj₁ kp)  = inLz y (shift k′ z lt) (inj₁ (≺-trans {k′} {k′ ⊕ [ ix 0 ]} {p′} (≺-ext k′ []) kp))
        sd (burst _ _)      _ lt (inj₂ refl) = ⊥-elim (σ-pin x)
        sd (echo {k′} y _ _ _) _ lt (inj₁ kp) = inLz y (shift k′ z lt) (inj₁ (≺-trans {k′} {k′ ⊕ [ ix 0 ]} {p′} (≺-ext k′ []) kp))
        sd (echo _ _ _ _)   _ lt (inj₂ ())
        sd (kept {k′} y _ _ _) _ lt (inj₁ kp) = inLz y (shift k′ z lt) (inj₁ (≺-trans {k′} {k′ ⊕ [ ix 0 ]} {p′} (≺-ext k′ []) kp))
        sd (kept {k′} y _ _ _) _ lt (inj₂ refl) = inLz y (shift k′ z lt) (inj₂ refl)

        -- What a body row before the kept one waits on, it waits on in `p′`'s past.
        bdep : ∀ {b e} → β b e → b ≺ (z ⊕ [ ix 0 ]) → PDep p′ b e → ∀ {k e″} → k ≺ b → Dep b e k e″ → PDep p′ k e″
        bdep {b} y bz (inj₁ bp)  {k} kb _ = inj₁ (≺-trans {k} {b} {p′} kb bp)
        bdep y bz (inj₂ refl) kb d = d (proj₂ (InvAt.pinned Iβ y))

        cov : ∀ {k e″} → ConnT k e″ → k ≺ (z ⊕ [ ix 0 ]) → Dep (z ⊕ [ ix 0 ]) (pin p′) k e″ → k ∈ (Lσ ++ ks)
        cov {k} (body y) lt d =
          ∈-++⁺ʳ Lσ (inC (body y) (body-reach y Lσ λ {k′} x′ t lt′ d′ → sd x′ t (≺-trans {k′} {k} {z ⊕ [ ix 0 ]} lt′ lt) (bdep y lt (d i′) lt′ d′))
                        (≺-trans {k} {z ⊕ [ ix 0 ]} {w} lt zw))
        cov x′@(burst _ _)    lt d = ∈-++⁺ˡ (sd x′ tt lt (d i′))
        cov x′@(echo _ _ _ _) lt d = ∈-++⁺ˡ (sd x′ tt lt (d i′))
        cov x′@(kept _ _ _ _) lt d = ∈-++⁺ˡ (sd x′ tt lt (d i′))

    sd-in : ∀ {k e} (x : ConnT k e) → SD x → k ≺ w → k ∈ ks
    sd-in (burst {k} y i)  _ kw = decidable-stable (any? ((k ⊕ [ ix 0 ]) ≟ᵖ_) ks) (burst-in y i kw)
    sd-in (echo y a u ni)  _ kw = echo-in y a u ni kw
    sd-in (kept y a ni i)  _ kw = kept-in y a ni i kw

    all-in : ∀ {k e} → ConnT k e → k ≺ w → k ∈ ks
    all-in {k} (body y) kw = inC (body y) (body-reach y ks λ {k′} x′ t lt _ → sd-in x′ t (≺-trans {k′} {k} {w} lt kw)) kw
    all-in x@(burst _ _)    = sd-in x tt
    all-in x@(echo _ _ _ _) = sd-in x tt
    all-in x@(kept _ _ _ _) = sd-in x tt

  conn-seen : ∀ {w} → Few C w → ∀ {k e} → ConnT k e → k ≺ w → Reach ConnT k e
  conn-seen {w} Fw {k} x kw = ks , λ {k′} y lt _ → all-in y (≺-trans {k′} {k} {w} lt kw)
    where open Seen Fw

  -- Every run met of the connect is met of its body.
  back : ∀ {c rs} → Run C c rs → Run β c rs
  back [] = []
  back ((((x@(body y , _) , pr) , _) , vi , aft , lst) ∷ run) =
    (((y , λ ce → before-end y vi ce) , entered-few (F (hot (Proper σ))) (p ⊕ [ ix 0 ]) (vis-dep vi) y) , vi , aft ,
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
            (Is : InvD H s) (IF : ∀ {t} → Lawful t → InvD (H ∪ʰ t) (F (hot t))) p (ok : Ok H p) cs
          → Shows (enter s (p ⊕ [ ix 1 ]))
          → Held (enter (F (hot (Proper (enter s (p ⊕ [ ix 1 ]))))) (p ⊕ [ ix 0 ])) ((p ⊕ [ ix 0 ]) ∷ p ∷ cs)
          → Held (enter (Op.connect s F) p) (p ∷ cs)
held-conn s F Is IF p ok cs sh h = held-same row end-row back′ fwd (held-ex ex h)
  where
    open ConnRun s F Is IF p ok sh

    ex : ∀ {y} → Ex ((p ⊕ [ ix 0 ]) ∷ p ∷ cs) y → Ex (p ∷ cs) y
    ex {y} (here sy) = here (sync-body {p} {y} sy)
    ex (there x) = x

    row : ∀ {y x′} → C y (out x′) → Σ _ λ x → Connect.β s F p y (out x) × Same x′ x
    row (Connecting.body y , _) = _ , y , same-refl _

    end-row : ∀ {y} → C y end → Connect.β s F p y end
    end-row (Connecting.body y , _) = y

    back′ : ∀ {rs′} → Met C rs′ → Σ _ λ rs → Met (Connect.β s F p) rs × Rows≈ rs′ rs
    back′ m = _ , back m , rows-refl m

    fwd : ∀ {w} → Few C w → ∀ {k e} → Connect.β s F p k e → k ≺ w → ¬ ¬ Σ _ λ e′ → C k e′ × (Visible e → Visible e′)
    fwd F x kw no = no (_ , (Connecting.body x , conn-seen F (Connecting.body x) kw) , λ v → v)
