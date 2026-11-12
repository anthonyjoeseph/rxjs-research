{-# OPTIONS --guardedness #-}

-- A `connect` IS CARRIED when its source and its body are.  The body is
-- subscribed at `ix 0` on each side; the source at `ix 1` plainly and,
-- elaborated, past its annotate's own `ix 1`.  The body runs under its
-- environment grown by the source made hot, bound to the annotated
-- source made hot.
module simultaneous.CarryConnect where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (yes; no)
open import Data.Bool.Properties using (T?)

open import Tree using (Obs; connect; map)
open import denotation.Position using (Pos; Label; Path; ix; sub; _⊕_; root; _≟ᵖ_; inside)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; EmissionSet; Proper; Den; hot; enter; DenEnv; approx; _≺_; module Connect)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≺-trans; ≺-ext; ticks; ≺-≼-≺)
open import denotation.Laws.Worlds using (_⊑_; ⊑-refl; ⊑-trans; ⊑-snoc; ⊑-snoc⁺; ⊑-≼; ⊑-cmp; ⊑-inside; inside-⊑; ⊕-assoc; ⊕-identityʳ;
  ⊕-injˡ; ⊕-injʳ; ext≢; Hots; GoodEnv; Ok; ok-step; InvAt; Lawful; InvD; _∪ʰ_; W; here; inW;
  step; plain-ix; nest-in; not-up; sib; shrink⁼; narrow⁼)
open import denotation.Laws using (inv-approx; good-cons)
open import denotation.Laws.Connect using (σ-wp; lawful; ok₀; body-leads; source-leads; sw; bw)
open import simultaneous.SObs using (lone; ext; module Elaborate)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (Live)
open import simultaneous.CarryBase using (PMap; _∪ᴹ_; emb-pairs; emb-at; _⊆ᴹ_; Emb; Fresh; CarryAt; emb-under; instant-⊕)
open import simultaneous.Carry using (CarriesAt; Within; Bare; Carry; carry; EnvRel; Bound; BoundRow; HotsListed; NotHot; Grown; Joins; joins-grow; Apart; EnvPast; PBNest; Nests; Anchor; anchor-up; grown-past; env-past; annValues; bound-hot)
open import simultaneous.CarryDefer using (env-grow; nests-grow; past-shrink; nest-up; joins-up; joins-shrink)
open import simultaneous.CarryLeaves using (module OneAt; ix-sub)
open import simultaneous.CarryTold using (module Folded; module Mapped; told-carry; justValues)
open import simultaneous.ToldRows using (told)
open import simultaneous.CarryConn using (module ConnCarry)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; annotate; annStep)

------------------------------------------------------------------------
-- The two subscriptions

private
  -- A route fold keeps the emit, so what it shows.
  ann-law : ∀ {X} b (y : Maybe (IE X)) → annValues (proj₂ (annStep b y)) ≡ justValues y
  ann-law (_ , _) (just _) = refl
  ann-law (_ , _) nothing  = refl

  ix01 : ∀ q → q ⊕ [ ix 0 ] ≡ q ⊕ [ ix 1 ] → ⊥
  ix01 q e = ≺-irrefl {q ⊕ [ ix 0 ]} (subst ((q ⊕ [ ix 0 ]) ≺_) (sym e) (ticks q 0))

  below-two : ∀ q → (q ⊕ [ ix 0 ]) ≺ ((q ⊕ [ ix 1 ]) ⊕ [ ix 1 ])
  below-two q = ≺-trans {q ⊕ [ ix 0 ]} {q ⊕ [ ix 1 ]} {(q ⊕ [ ix 1 ]) ⊕ [ ix 1 ]} (ticks q 0) (≺-ext (q ⊕ [ ix 1 ]) [])

  over-two : ∀ q → q ≺ ((q ⊕ [ ix 1 ]) ⊕ [ ix 1 ])
  over-two q = ≺-trans {q} {q ⊕ [ ix 1 ]} {(q ⊕ [ ix 1 ]) ⊕ [ ix 1 ]} (≺-ext q []) (≺-ext (q ⊕ [ ix 1 ]) [])

  not-under-two : ∀ q → (q ⊕ [ ix 0 ]) ⊑ ((q ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) → ⊥
  not-under-two q h with ⊑-snoc (q ⊕ [ ix 1 ]) h
  ... | inj₂ e = ext≢ q [] (sym (⊕-injˡ q (q ⊕ [ ix 1 ]) e))
  ... | inj₁ h′ with ⊑-snoc q h′
  ...   | inj₁ h″ = ⊑-≼ h″ (≺-ext q [])
  ...   | inj₂ e  = ix01 q e

  two-not-under : ∀ q → ((q ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊑ (q ⊕ [ ix 0 ]) → ⊥
  two-not-under q h with ⊑-snoc q h
  ... | inj₁ h′ = ⊑-≼ h′ (over-two q)
  ... | inj₂ e  = ext≢ q [] (⊕-injˡ (q ⊕ [ ix 1 ]) q e)

  inst-two : ∀ q → instantOf ((q ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ≡ instantOf q
  inst-two q = trans (instant-⊕ (q ⊕ [ ix 1 ]) [ ix 1 ]) (instant-⊕ q [ ix 1 ])

  -- Two labels one under a position, both leading a third, are one.
  one-label : ∀ k {a b x} → (k ⊕ [ a ]) ⊑ x → (k ⊕ [ b ]) ⊑ x → a ≡ b
  one-label k {a} {b} ax bx with ⊑-cmp (k ⊕ [ a ]) (k ⊕ [ b ]) ax bx
  ... | inj₁ ab with ⊑-snoc k ab
  ...   | inj₁ ak = ⊥-elim (⊑-≼ ak (≺-ext k []))
  ...   | inj₂ e  = ⊕-injʳ k k e
  one-label k {a} {b} ax bx | inj₂ ba with ⊑-snoc k ba
  ...   | inj₁ bk = ⊥-elim (⊑-≼ bk (≺-ext k []))
  ...   | inj₂ e  = sym (⊕-injʳ k k e)

  -- A tick one label under a position leads nothing its readings do.
  tick-read : ∀ k {e x} → (k ⊕ [ sub e ]) ⊑ x → (k ⊕ [ ix 0 ]) ⊑ x → ⊥
  tick-read k sx tx with one-label k sx tx
  ... | ()

  one-sh : ∀ {k l x y} → OneAt.N k l x y → Σ Label λ a → Σ Path λ σ → Σ Label λ b → Σ Path λ σ′ → x ≡ k ⊕ (a ∷ σ) × y ≡ l ⊕ (b ∷ σ′)
  one-sh (a , _ , refl , refl) = a , [] , a , [] , refl , refl

  -- Two pairs.
  Two : Pos → Pos → Pos → Pos → PMap
  Two a b a′ b′ x y = (x ≡ a × y ≡ b) ⊎ (x ≡ a′ × y ≡ b′)

  -- Two pairs of an embedding embed.
  emb-two : ∀ {M a b a′ b′} → Emb M → M a b → M a′ b′ → Emb (Two a b a′ b′)
  emb-two {M} {a} {b} {a′} {b′} E m m′ = record
    { fun     = λ t t′ → Emb.fun E (back t) (back t′)
    ; mono    = λ t t′ → Emb.mono E (back t) (back t′)
    ; reflect = λ t t′ → Emb.reflect E (back t) (back t′)
    ; inst    = λ t t′ → Emb.inst E (back t) (back t′) }
    where
      back : ∀ {x y} → Two a b a′ b′ x y → M x y
      back (inj₁ (refl , refl)) = m
      back (inj₂ (refl , refl)) = m′

  -- Two distinct pairs embed when each relation between them carries.
  emb-two′ : ∀ {x y x′ y′} → (x ≡ x′ → ⊥) → (x ≺ x′ → y ≺ y′) → (x′ ≺ x → y′ ≺ y) → (y ⊑ y′ → x ⊑ x′) → (y′ ⊑ y → x′ ⊑ x)
           → (instantOf y ≡ instantOf y′ ⇔ instantOf x ≡ instantOf x′) → Emb (Two x y x′ y′)
  emb-two′ {x} {y} {x′} {y′} ne m₁ m₂ r₁ r₂ i = record
    { fun     = λ { (inj₁ (refl , refl)) (inj₁ (_ , refl)) → refl
                  ; (inj₂ (refl , refl)) (inj₂ (_ , refl)) → refl
                  ; (inj₁ (refl , refl)) (inj₂ (e , _))    → ⊥-elim (ne e)
                  ; (inj₂ (refl , refl)) (inj₁ (e , _))    → ⊥-elim (ne (sym e)) }
    ; mono    = λ { (inj₁ (refl , refl)) (inj₁ (refl , refl)) h → ⊥-elim (≺-irrefl {x} h)
                  ; (inj₂ (refl , refl)) (inj₂ (refl , refl)) h → ⊥-elim (≺-irrefl {x′} h)
                  ; (inj₁ (refl , refl)) (inj₂ (refl , refl)) h → m₁ h
                  ; (inj₂ (refl , refl)) (inj₁ (refl , refl)) h → m₂ h }
    ; reflect = λ { (inj₁ (refl , refl)) (inj₁ (refl , refl)) _ → ⊑-refl x
                  ; (inj₂ (refl , refl)) (inj₂ (refl , refl)) _ → ⊑-refl x′
                  ; (inj₁ (refl , refl)) (inj₂ (refl , refl)) h → r₁ h
                  ; (inj₂ (refl , refl)) (inj₁ (refl , refl)) h → r₂ h }
    ; inst    = λ { (inj₁ (refl , refl)) (inj₁ (refl , refl)) → mk⇔ (λ _ → refl) (λ _ → refl)
                  ; (inj₂ (refl , refl)) (inj₂ (refl , refl)) → mk⇔ (λ _ → refl) (λ _ → refl)
                  ; (inj₁ (refl , refl)) (inj₂ (refl , refl)) → i
                  ; (inj₂ (refl , refl)) (inj₁ (refl , refl)) →
                      mk⇔ (λ q → sym (Equivalence.to i (sym q))) (λ q → sym (Equivalence.from i (sym q))) } }

-- THE CONNECT'S TWO SUBSCRIPTIONS, paired: the body's at `ix 0` on each
-- side; the source's at `ix 1`, put past the elaborated annotate's own
-- `ix 1`.
module ConnAt (p p′ : Pos) where
  N : PMap
  N x y = (x ≡ p ⊕ [ ix 0 ] × y ≡ p′ ⊕ [ ix 0 ]) ⊎ (x ≡ p ⊕ [ ix 1 ] × y ≡ (p′ ⊕ [ ix 1 ]) ⊕ [ ix 1 ])

  iP : ∀ {x y} → N x y → instantOf x ≡ instantOf p
  iP (inj₁ (refl , _)) = instant-⊕ p [ ix 0 ]
  iP (inj₂ (refl , _)) = instant-⊕ p [ ix 1 ]

  iE : ∀ {x y} → N x y → instantOf y ≡ instantOf p′
  iE (inj₁ (_ , refl)) = instant-⊕ p′ [ ix 0 ]
  iE (inj₂ (_ , refl)) = inst-two p′

  embN : Emb N
  embN = record
    { fun     = λ { (inj₁ (refl , refl)) (inj₁ (_ , refl)) → refl
                  ; (inj₂ (refl , refl)) (inj₂ (_ , refl)) → refl
                  ; (inj₁ (refl , _))    (inj₂ (e , _))    → ⊥-elim (ix01 p e)
                  ; (inj₂ (refl , _))    (inj₁ (e , _))    → ⊥-elim (ix01 p (sym e)) }
    ; mono    = λ { (inj₁ (refl , refl)) (inj₁ (refl , refl)) h → ⊥-elim (≺-irrefl {p ⊕ [ ix 0 ]} h)
                  ; (inj₂ (refl , refl)) (inj₂ (refl , refl)) h → ⊥-elim (≺-irrefl {p ⊕ [ ix 1 ]} h)
                  ; (inj₁ (refl , refl)) (inj₂ (refl , refl)) _ → below-two p′
                  ; (inj₂ (refl , refl)) (inj₁ (refl , refl)) h → ⊥-elim (≺-absurd {p ⊕ [ ix 0 ]} {p ⊕ [ ix 1 ]} (ticks p 0) h) }
    ; reflect = λ { (inj₁ (refl , refl)) (inj₁ (refl , refl)) _ → ⊑-refl _
                  ; (inj₂ (refl , refl)) (inj₂ (refl , refl)) _ → ⊑-refl _
                  ; (inj₁ (refl , refl)) (inj₂ (refl , refl)) h → ⊥-elim (not-under-two p′ h)
                  ; (inj₂ (refl , refl)) (inj₁ (refl , refl)) h → ⊥-elim (two-not-under p′ h) }
    ; inst    = λ n n′ → mk⇔ (λ _ → trans (iP n) (sym (iP n′))) (λ _ → trans (iE n) (sym (iE n′)))
    }

-- A map held fresh grown by the two subscriptions.
module ConnUnder {H : Pos → Set} {M₀ : PMap} {p p′ : Pos} (E₀ : Emb M₀) (fr : Fresh H M₀ p) (m₀ : M₀ p p′) where
  open ConnAt p p′ public

  M : PMap
  M = M₀ ∪ᴹ N

  emb : Emb M
  emb = emb-under {N = N} E₀ fr m₀ (⊑-refl p′) embN sh
    where
      sh : ∀ {x y} → N x y → Σ Label λ a → Σ Path λ σ → Σ Label λ b → Σ Path λ σ′ → x ≡ p ⊕ (a ∷ σ) × y ≡ p′ ⊕ (b ∷ σ′)
      sh (inj₁ (refl , refl)) = ix 0 , [] , ix 0 , [] , refl , refl
      sh (inj₂ (refl , refl)) = ix 1 , [] , ix 1 , [ ix 1 ] , refl , ⊕-assoc p′ [ ix 1 ] [ ix 1 ]

  within : Within H M₀ M p
  within (inj₁ m)                 = inj₁ m
  within (inj₂ (inj₁ (refl , _))) = inj₂ (inW (step here plain-ix))
  within (inj₂ (inj₂ (refl , _))) = inj₂ (inW (step here plain-ix))

  grown : NotHot H p → ∀ {x y} → M x y → M₀ x y ⊎ Grown M₀ H x y
  grown _  (inj₁ m)                    = inj₁ m
  grown nh (inj₂ (inj₁ (refl , refl))) = inj₂ (p , p′ , ix 0 , m₀ , ⊑-snoc⁺ p′ , refl , nh)
  grown nh (inj₂ (inj₂ (refl , refl))) = inj₂ (p , p′ , ix 1 , m₀ , ⊑-trans (⊑-snoc⁺ p′) (⊑-snoc⁺ (p′ ⊕ [ ix 1 ])) , refl , nh)

  -- The source's subscription is held fresh.
  fresh-s : Ok H p → Fresh H M (p ⊕ [ ix 1 ])
  fresh-s ok (inj₁ m) (w , ww , wx) with fr m (w , inW (nest-in (step here plain-ix) ww) , wx)
  ... | refl = ⊥-elim (not-up (proj₁ ok) ww wx)
  fresh-s ok (inj₂ (inj₁ (refl , _))) (w , ww , wx) = ⊥-elim (sib (proj₁ ok) plain-ix (⊑-refl p) (ix01 p) ww wx)
  fresh-s ok (inj₂ (inj₂ (refl , _))) _ = refl

------------------------------------------------------------------------
-- The connect's parts

module Conn {Γ Δ A B} (n : ℕ) (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B)
            (envP : DenEnv Γ) (envE : DenEnv Δ) (gP : GoodEnv envP) (gE : GoodEnv envE)
            (p p′ : Pos) (okP : Ok (Hots envP) p) (okE : Ok (Hots envE) p′) where
  ρ′ : ∀ {X} → X ∈ L.map AIE (A ∷ Γ) → X ∈ AIE A ∷ Δ
  ρ′ = ext (λ {X} → ρ {X})

  sP : Den A
  sP = approx n s envP

  FP : Den A → Den B
  FP h = approx n b (h ∷ envP)

  sE : Den (AIE A)
  sE = approx n (annotate (elab ρ s)) envE

  FE : Den (AIE A) → Den (IE B)
  FE h = approx n (elab ρ′ b) (h ∷ envE)

  σP : EmissionSet A
  σP = enter sP (p ⊕ [ ix 1 ])

  σE : EmissionSet (AIE A)
  σE = enter sE (p′ ⊕ [ ix 1 ])

  envP′ : DenEnv (A ∷ Γ)
  envP′ = hot (Proper σP) ∷ envP

  envE′ : DenEnv (AIE A ∷ Δ)
  envE′ = hot (Proper σE) ∷ envE

  -- The elaborated source, past annotate's own subscription.
  s₀′ : Pos
  s₀′ = (p′ ⊕ [ ix 1 ]) ⊕ [ ix 1 ]

  uS : EmissionSet (IE A)
  uS = enter (approx n (elab ρ s) envE) s₀′

  IsP : InvD (Hots envP) sP
  IsP = inv-approx n s envP gP

  IFP : ∀ {t} → Lawful t → InvD (Hots envP ∪ʰ t) (FP (hot t))
  IFP {t} L = inv-approx n b (hot t ∷ envP) (good-cons L gP)

  IsE : InvD (Hots envE) sE
  IsE = inv-approx n (annotate (elab ρ s)) envE gE

  IFE : ∀ {t} → Lawful t → InvD (Hots envE ∪ʰ t) (FE (hot t))
  IFE {t} L = inv-approx n (elab ρ′ b) (hot t ∷ envE) (good-cons L gE)

  gP′ : GoodEnv envP′
  gP′ = good-cons (lawful {s = sP} {F = FP} IsP IFP p okP) gP

  gE′ : GoodEnv envE′
  gE′ = good-cons (lawful {s = sE} {F = FE} IsE IFE p′ okE) gE

  okP′ : Ok (Hots envP′) (p ⊕ [ ix 0 ])
  okP′ = ok₀ {s = sP} {F = FP} IsP IFP p okP

  okE′ : Ok (Hots envE′) (p′ ⊕ [ ix 0 ])
  okE′ = ok₀ {s = sE} {F = FE} IsE IFE p′ okE

  Iσ : InvAt (Hots envP) (p ⊕ [ ix 1 ]) σP
  Iσ = IsP (p ⊕ [ ix 1 ]) (ok-step p okP)

  σ-in : ∀ {h e} → Proper σP h e → W (Hots envP) p h
  σ-in = σ-wp {s = sP} {F = FP} IsP IFP p okP

  -- No source row lies under another's.
  σ-flat : ∀ {k h e e′} → σP k e → σP h e′ → k ⊑ h → k ≡ h
  σ-flat {k} x x′ ([] , refl) = sym (⊕-identityʳ k)
  σ-flat x x′ (_ ∷ _ , refl) = ⊥-elim (InvAt.flat Iσ x x′)

  -- The source made hot, bound to its annotation.
  bound : ∀ {M} → CarryAt annValues M (Hots envP) (Hots envE) (HotsListed envP) σP σE (p ⊕ [ ix 1 ]) (p′ ⊕ [ ix 1 ])
        → Bound M (HotsListed envP′) (hot (Proper σP)) (hot (Proper σE))
  bound c = record { m = n ; src = s ; σ = λ {Y} → ρ {Y} ; envP = envP ; envE = envE ; at = p ; at′ = p′ ; lists = proj₂ ; carried = c
                   ; invP = Iσ ; invE = IsE (p′ ⊕ [ ix 1 ]) (ok-step p′ okE) ; isP = refl ; isE = refl }

  -- The environment grown by it.
  bind : ∀ {M} → EnvRel M ρ envP envE → CarryAt annValues M (Hots envP) (Hots envE) (HotsListed envP) σP σE (p ⊕ [ ix 1 ]) (p′ ⊕ [ ix 1 ])
       → EnvRel M ρ′ envP′ envE′
  bind er c (here refl) = bound c
  bind er c (there i)   = record { m = B.m ; src = B.src ; σ = B.σ ; envP = B.envP ; envE = B.envE ; at = B.at ; at′ = B.at′
                                 ; lists = λ L → B.lists (proj₂ L) ; carried = B.carried ; invP = B.invP ; invE = B.invE ; isP = B.isP ; isE = B.isE }
    where module B = Bound (er i)

  -- What the grown environment's binders give, the original's do: bind
  -- copies each one.
  bind-past : ∀ {M N} (er : EnvRel M ρ envP envE) (c : CarryAt annValues M (Hots envP) (Hots envE) (HotsListed envP) σP σE (p ⊕ [ ix 1 ]) (p′ ⊕ [ ix 1 ]))
            → EnvPast (bind er c) N → EnvPast er N
  bind-past er c ep i = ep (there i)

  joins-unbind : ∀ {M N} (er : EnvRel M ρ envP envE) (c : CarryAt annValues M (Hots envP) (Hots envE) (HotsListed envP) σP σE (p ⊕ [ ix 1 ]) (p′ ⊕ [ ix 1 ]))
               → Joins ρ′ envP′ envE′ (bind er c) N → Joins ρ envP envE er N
  joins-unbind er c jn i = jn (there i)

  joins-bind : ∀ {M N} (er : EnvRel M ρ envP envE) (c : CarryAt annValues M (Hots envP) (Hots envE) (HotsListed envP) σP σE (p ⊕ [ ix 1 ]) (p′ ⊕ [ ix 1 ]))
             → Joins ρ envP envE er N → (∀ {x y q a σ} → N x y → BoundRow (bound c) q → x ≡ q ⊕ (a ∷ σ) → ⊥)
             → Joins ρ′ envP′ envE′ (bind er c) N
  joins-bind er c jn nu (here refl) m row e = ⊥-elim (nu m row e)
  joins-bind er c jn nu (there i)   m row e = jn i m row e

  -- A late carrier strictly under a row of the bound source, anchored.
  Under : ∀ {M} → CarryAt annValues M (Hots envP) (Hots envE) (HotsListed envP) σP σE (p ⊕ [ ix 1 ]) (p′ ⊕ [ ix 1 ]) → PMap
        → ∀ {A′ Y} {f : Y → List A′} {M₁ : PMap} {HP HE LP : Pos → Set} {t : EmissionSet A′} {u : EmissionSet Y} {s₁ s₁′ : Pos}
        → CarryAt f M₁ HP HE LP t u s₁ s₁′ → Set
  Under c N {t = t} c′ = ∀ {k l e₀ h L a σ} → CarryAt.PB c′ k l → t k e₀ → Live t k → BoundRow (bound c) h → CarryAt.Img c h L
                       → k ≡ h ⊕ (a ∷ σ) → Anchor N k l h a

  nests-bind : ∀ {M N} (er : EnvRel M ρ envP envE) (c : CarryAt annValues M (Hots envP) (Hots envE) (HotsListed envP) σP σE (p ⊕ [ ix 1 ]) (p′ ⊕ [ ix 1 ]))
             → Nests er N → PBNest er N c → Under c N c → (∀ {X} (j : X ∈ Γ) → Under c N (Bound.carried (er j)))
             → Nests (bind er c) N
  nests-bind er c ns ht hh th (here refl) (here refl) = hh
  nests-bind er c ns ht hh th (here refl) (there i)   = ht i
  nests-bind er c ns ht hh th (there j)   (here refl) = th j
  nests-bind er c ns ht hh th (there j)   (there i)   = ns j i

  -- THE ANNOTATED SOURCE CARRIES THE SOURCE where the elaborated source
  -- does, each late carrier under one of the elaborated source's: read
  -- as maybe-emits, told its end by `nothing`, and folded into routes,
  -- each row showing what it showed.
  annotate-carry : ∀ {M} → (c : CarryAt valuesOf M (Hots envP) (Hots envE) (HotsListed envP) σP uS (p ⊕ [ ix 1 ]) s₀′)
                 → Σ (CarryAt annValues M (Hots envP) (Hots envE) (HotsListed envP) σP σE (p ⊕ [ ix 1 ]) (p′ ⊕ [ ix 1 ]))
                     λ c′ → ∀ {k l e₀} → CarryAt.PB c′ k l → σP k e₀ → Live σP k → Σ Pos λ l₀ → CarryAt.PB c k l₀ × l₀ ⊑ l
  annotate-carry c = Folded.carried annStep ((root , 0) , ((root , 0) , nothing)) proj₂ ann-law (approx n told′ envE) (p′ ⊕ [ ix 1 ])
                       (inv-approx n told′ envE gE (p′ ⊕ [ ix 1 ]) (ok-step p′ okE)) (proj₁ tc) , proj₂ tc
    where
      told′ : Obs Timeline Δ (Maybe (IE A))
      told′ = told nothing (map just (elab ρ s))

      tc = told-carry n (map just (elab ρ s)) nothing refl envE gE (p′ ⊕ [ ix 1 ]) (ok-step p′ okE)
             (Mapped.carried {f₁ = valuesOf} {f₂ = justValues} just (λ _ → refl) (approx n (elab ρ s) envE) s₀′ c)

------------------------------------------------------------------------
-- The assembly

module Assembly {Γ Δ A B} (n : ℕ) (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B)
                (hs : Carry n ρ s) (hb : ∀ {Δ′} (ρ″ : ∀ {X} → X ∈ L.map AIE (A ∷ Γ) → X ∈ Δ′) → Carry n ρ″ b)
                (envP : DenEnv Γ) (envE : DenEnv Δ) (gP : GoodEnv envP) (gE : GoodEnv envE) (M₀ : PMap) (hm : Emb M₀)
                (er : EnvRel M₀ ρ envP envE) (jn : Joins ρ envP envE er M₀) (ns : Nests er M₀) (ap : Apart envP)
                (p p′ : Pos) (m₀ : M₀ p p′) (okP : Ok (Hots envP) p) (okE : Ok (Hots envE) p′) (nh : NotHot (Hots envP) p)
                (fr : Fresh (Hots envP) M₀ p) where
  open Conn n ρ s b envP envE gP gE p p′ okP okE
  module U = ConnUnder {H = Hots envP} hm fr m₀

  past₁ : EnvPast er U.M
  past₁ = grown-past {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} er (env-past er) (λ {x} {y} → U.grown nh {x} {y})

  er₁ : EnvRel U.M ρ envP envE
  er₁ = env-grow {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} inj₁ er past₁

  ns₁ : Nests er₁ U.M
  ns₁ = nests-grow {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} inj₁ er past₁ ns

  jn₁ : Joins ρ envP envE er₁ U.M
  jn₁ = joins-grow {ρ = ρ} {envP = envP} {envE = envE} {er = er₁} {M = M₀} {N = U.M} inj₁
          (joins-up {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} inj₁ er past₁ jn) (λ {x} {y} → U.grown nh {x} {y})

  -- Past the source.
  module AfterSource (M_s : PMap) (ms_s : U.M ⊆ᴹ M_s) (hm_s : Emb M_s) (wi_s : Within (Hots envP) U.M M_s (p ⊕ [ ix 1 ])) (br_s : Bare M_s σP)
                     (jn_s : Joins ρ envP envE er₁ M_s) (ep_s : EnvPast er₁ M_s)
                     (c_s : CarryAt valuesOf M_s (Hots envP) (Hots envE) (HotsListed envP) σP uS (p ⊕ [ ix 1 ]) s₀′) (nc_s : PBNest er₁ M_s c_s) where
    er₂ : EnvRel M_s ρ envP envE
    er₂ = env-grow {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} ms_s er₁ ep_s

    ns₂ : Nests er₂ M_s
    ns₂ = nests-grow {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} ms_s er₁ ep_s ns₁

    annotated = annotate-carry c_s

    c_a : CarryAt annValues M_s (Hots envP) (Hots envE) (HotsListed envP) σP σE (p ⊕ [ ix 1 ]) (p′ ⊕ [ ix 1 ])
    c_a = proj₁ annotated

    er′ : EnvRel M_s ρ′ envP′ envE′
    er′ = bind er₂ c_a

    -- Nothing the source's map pairs is strictly under one of its rows.
    joins′ : Joins ρ′ envP′ envE′ er′ M_s
    joins′ = joins-bind er₂ c_a (joins-up {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} ms_s er₁ ep_s jn_s)
               (λ { m (_ , x) refl → ext≢ _ _ (br_s (proj₁ x) m (_ ∷ _ , refl)) })

    -- An annotated late carrier lies under a source one.
    nest-a : PBNest er₁ M_s c_a
    nest-a i pb tk lv br ci e with proj₂ annotated pb tk lv
    ... | l₀ , pb₀ , ll = anchor-up (nc_s i pb₀ tk lv br ci e) ll

    -- No hot row lies strictly under a source row.
    nests′ : Nests er′ M_s
    nests′ = nests-bind er₂ c_a ns₂ (nest-up {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} {c = c_a} ms_s er₁ ep_s nest-a)
               (λ { pb tk lv (_ , x) ci refl → ⊥-elim (InvAt.flat Iσ (proj₁ x) tk) })
               (λ { j {h = h} {a = a} {σ = σ} pb tk lv (_ , x) ci refl →
                 ⊥-elim (proj₂ okP (bound-hot {ρ = λ {X} → ρ {X}} envP {envE = envE} er₂ j (_ , tk , λ {c} → lv {c})) (σ-in x)
                   (⊑-inside {h} {h ⊕ (a ∷ σ)} (a ∷ σ , refl))) })

    ap′ : Apart envP′
    ap′ = (λ {q} x hq → proj₂ okP hq (σ-in x) (⊑-inside {q} {q} (⊑-refl q))) , ap

    nh-b : NotHot (Hots envP′) (p ⊕ [ ix 0 ])
    nh-b (inj₂ hq)     kq = nh hq (⊑-trans (⊑-snoc⁺ p) kq)
    nh-b (inj₁ (_ , x)) kq = body-leads {s = sP} {F = FP} IsP IFP p okP here (sw {s = sP} {F = FP} IsP IFP p okP (proj₁ x)) kq

    fresh-b : Fresh (Hots envP′) M_s (p ⊕ [ ix 0 ])
    fresh-b m (w , ww , wx) with wi_s m
    ... | inj₂ sx = ⊥-elim (body-leads {s = sP} {F = FP} IsP IFP p okP ww sx wx)
    ... | inj₁ (inj₂ (inj₁ (refl , _))) = refl
    ... | inj₁ (inj₂ (inj₂ (refl , _))) = ⊥-elim (body-leads {s = sP} {F = FP} IsP IFP p okP ww here wx)
    ... | inj₁ (inj₁ m₁) with fr m₁ (w , inW (narrow⁼ σ-in ww) , wx)
    ...   | refl = ⊥-elim (not-up (proj₁ okP) ww wx)

    -- What a map joins under a row of the bound source.
    JoinsHere : PMap → Set
    JoinsHere N = ∀ {x y q a σ} → N x y → BoundRow (bound c_a) q → x ≡ q ⊕ (a ∷ σ)
      → Σ Pos λ e → a ≡ sub e × Σ Pos λ e′ → N e e′ × Σ Pos λ L → CarryAt.Img c_a q L × (L ⊕ [ sub e′ ]) ⊑ y

    -- Past the body.  Only what the body's map needs is a parameter here:
    -- each `with` below rechecks the parameters, and the body's carry
    -- holds the environment grown twice.
    module AfterBody (M_b : PMap) (jh : JoinsHere M_b) (ms_b : M_s ⊆ᴹ M_b) (hm_b : Emb M_b) (wi_b : Within (Hots envP′) M_s M_b (p ⊕ [ ix 0 ])) where
      within : Within (Hots envP) M₀ M_b p
      within m with wi_b m
      ... | inj₂ w = inj₂ (inW (narrow⁼ σ-in w))
      ... | inj₁ ms with wi_s ms
      ...   | inj₂ w = inj₂ (inW (shrink⁼ w))
      ...   | inj₁ u = U.within u

      -- Nothing is paired strictly under a source row's echo: the source's
      -- map pairs nothing under the row, and the body reaches under it
      -- only through a join.
      σ-bare : ∀ {k e x y} → σP k e → M_b x y → (k ⊕ [ ix 0 ]) ⊑ x → x ≡ k ⊕ [ ix 0 ]
      σ-bare {k} x m kx with wi_b m
      ... | inj₁ ms with br_s x ms (⊑-trans (⊑-snoc⁺ k) kx)
      ...   | refl = ⊥-elim (⊑-≼ kx (≺-ext k []))
      σ-bare {k} x m kx | inj₂ w with source-leads {s = sP} {F = FP} IsP IFP p okP (sw {s = sP} {F = FP} IsP IFP p okP x) w (⊑-trans (⊑-snoc⁺ k) kx)
      ... | h , e , (_ , x′) , kh , hx with σ-flat x (proj₁ x′) kh
      ...   | refl with one-label k kx hx
      ...     | ()

      -- EACH SOURCE ROW'S ECHO, paired one label under the row with its
      -- annotation's: the map the connect's rows are carried along.
      Echo : PMap
      Echo x y = Σ Pos λ k₀ → Σ Pos λ l₀ → Σ (Ev A) (σP k₀) × CarryAt.Img c_a k₀ l₀ × x ≡ k₀ ⊕ [ ix 0 ] × y ≡ l₀ ⊕ [ ix 0 ]

      M′ : PMap
      M′ = M_b ∪ᴹ Echo

      -- An annotation's carrier, paired in the body's map.
      at-a : ∀ {k₀ l₀} → CarryAt.Img c_a k₀ l₀ → Σ Pos λ y₀ → M_b k₀ y₀ × y₀ ⊑ l₀
      at-a i = let (y₀ , m , yl) = CarryAt.ext c_a i in y₀ , ms_b m , yl

      -- What the body pairs strictly under a source row is a reading of
      -- it, imaged under a reading of its annotation.
      read-under : ∀ {k₀ e₀ l₀ x y} → σP k₀ e₀ → CarryAt.Img c_a k₀ l₀ → M_b x y → k₀ ⊑ x → (x ≡ k₀ → ⊥)
                 → Σ Pos λ e → Σ Pos λ e′ → (k₀ ⊕ [ sub e ]) ⊑ x × (l₀ ⊕ [ sub e′ ]) ⊑ y
      read-under {k₀} tk i m ([] , refl) ne = ⊥-elim (ne (⊕-identityʳ k₀))
      read-under {k₀} tk i m (a ∷ σ₁ , refl) ne with wi_b m
      ... | inj₁ ms = ⊥-elim (ne (br_s tk ms (a ∷ σ₁ , refl)))
      ... | inj₂ w with source-leads {s = sP} {F = FP} IsP IFP p okP (sw {s = sP} {F = FP} IsP IFP p okP tk) w (a ∷ σ₁ , refl)
      ...   | h , e , (_ , x′) , kh , _ with σ-flat tk (proj₁ x′) kh
      ...     | refl with jh m (_ , x′) refl
      ...       | e₁ , refl , e′ , _ , L , iL , Ly with CarryAt.img-fun c_a iL i
      ...         | refl = e₁ , e′ , (σ₁ , sym (⊕-assoc _ [ sub e₁ ] σ₁)) , Ly

      -- Two echoes lie one label under their rows' carriers.
      echo-echo : ∀ {x y x′ y′} → Echo x y → Echo x′ y′ → Σ PMap λ K → Emb K × K x y × K x′ y′
      echo-echo (k₀ , l₀ , (_ , tk₀) , i₀ , refl , refl) (k₁ , l₁ , (_ , tk₁) , i₁ , refl , refl) with k₀ ≟ᵖ k₁
      ... | yes refl with CarryAt.img-fun c_a i₀ i₁
      ...   | refl = OneAt.N k₀ l₀ , OneAt.embN k₀ l₀ , (ix 0 , plain-ix , refl , refl) , (ix 0 , plain-ix , refl , refl)
      echo-echo (k₀ , l₀ , (_ , tk₀) , i₀ , refl , refl) (k₁ , l₁ , (_ , tk₁) , i₁ , refl , refl) | no ne with at-a i₀ | at-a i₁
      ... | y₀ , m₀ , p₀ | y₁ , m₁ , p₁ =
        (Two k₀ y₀ k₁ y₁ ∪ᴹ OneAt.N k₀ l₀) ∪ᴹ OneAt.N k₁ l₁ , E₁ , inj₁ (inj₂ (ix 0 , plain-ix , refl , refl)) , inj₂ (ix 0 , plain-ix , refl , refl)
        where
          at₀ : ∀ {x y} → Two k₀ y₀ k₁ y₁ x y → k₀ ⊑ x → x ≡ k₀
          at₀ (inj₁ (refl , _)) _  = refl
          at₀ (inj₂ (refl , _)) kx = ⊥-elim (ne (σ-flat tk₀ tk₁ kx))

          E₀ : Emb (Two k₀ y₀ k₁ y₁ ∪ᴹ OneAt.N k₀ l₀)
          E₀ = emb-at (emb-two hm_b m₀ m₁) at₀ (inj₁ (refl , refl)) p₀ (OneAt.embN k₀ l₀) (λ {x} {y} q → one-sh {k₀} {l₀} {x} {y} q)

          at₁ : ∀ {x y} → (Two k₀ y₀ k₁ y₁ ∪ᴹ OneAt.N k₀ l₀) x y → k₁ ⊑ x → x ≡ k₁
          at₁ (inj₁ (inj₁ (refl , _))) kx = ⊥-elim (ne (sym (σ-flat tk₁ tk₀ kx)))
          at₁ (inj₁ (inj₂ (refl , _))) _  = refl
          at₁ (inj₂ (a , _ , refl , _)) kx with ⊑-snoc k₀ kx
          ... | inj₁ kk = ⊥-elim (ne (sym (σ-flat tk₁ tk₀ kk)))
          ... | inj₂ e  = ⊥-elim (ne (σ-flat tk₀ tk₁ (subst (k₀ ⊑_) (sym e) (⊑-snoc⁺ k₀))))

          E₁ : Emb ((Two k₀ y₀ k₁ y₁ ∪ᴹ OneAt.N k₀ l₀) ∪ᴹ OneAt.N k₁ l₁)
          E₁ = emb-at E₀ at₁ (inj₁ (inj₂ (refl , refl))) p₁ (OneAt.embN k₁ l₁) (λ {x} {y} q → one-sh {k₁} {l₁} {x} {y} q)

      -- An echo and a pair of the body's map not strictly under its row.
      echo-under : ∀ {k₀ l₀ e₀ x′ y′} → σP k₀ e₀ → CarryAt.Img c_a k₀ l₀ → M_b x′ y′ → (k₀ ⊑ x′ → x′ ≡ k₀)
                 → Σ PMap λ K → Emb K × K (k₀ ⊕ [ ix 0 ]) (l₀ ⊕ [ ix 0 ]) × K x′ y′
      echo-under {k₀} {l₀} {x′ = x′} {y′} tk₀ i₀ m kx′ with at-a i₀
      ... | y₀ , m₀ , p₀ =
        Two k₀ y₀ x′ y′ ∪ᴹ OneAt.N k₀ l₀ , emb-at (emb-two hm_b m₀ m) at (inj₁ (refl , refl)) p₀ (OneAt.embN k₀ l₀) (λ {x} {y} q → one-sh {k₀} {l₀} {x} {y} q)
          , inj₂ (ix 0 , plain-ix , refl , refl) , inj₁ (inj₂ (refl , refl))
        where
          at : ∀ {x y} → Two k₀ y₀ x′ y′ x y → k₀ ⊑ x → x ≡ k₀
          at (inj₁ (refl , _)) _  = refl
          at (inj₂ (refl , _)) kx = kx′ kx

      -- An echo and a reading of its row: the tick leads the readings on
      -- both sides.
      echo-read : ∀ {k₀ l₀ e₀ x′ y′} → σP k₀ e₀ → CarryAt.Img c_a k₀ l₀ → M_b x′ y′ → k₀ ⊑ x′ → (x′ ≡ k₀ → ⊥)
                → Emb (Two (k₀ ⊕ [ ix 0 ]) (l₀ ⊕ [ ix 0 ]) x′ y′)
      echo-read {k₀} {l₀} tk₀ i₀ m kx ne with read-under tk₀ i₀ m kx ne
      ... | e , e′ , (zs , refl) , (ws , refl) =
        emb-two′ (λ q → tick-read k₀ (zs , refl) (subst ((k₀ ⊕ [ ix 0 ]) ⊑_) q (⊑-refl _)))
                 (λ _ → ≺-≼-≺ {l₀ ⊕ [ ix 0 ]} {l₀ ⊕ [ sub e′ ]} {(l₀ ⊕ [ sub e′ ]) ⊕ ws} (ix-sub l₀ e′) (⊑-≼ {l₀ ⊕ [ sub e′ ]} (ws , refl)))
                 (λ h → ⊥-elim (≺-absurd {(k₀ ⊕ [ sub e ]) ⊕ zs} {k₀ ⊕ [ ix 0 ]} h
                          (≺-≼-≺ {k₀ ⊕ [ ix 0 ]} {k₀ ⊕ [ sub e ]} {(k₀ ⊕ [ sub e ]) ⊕ zs} (ix-sub k₀ e) (⊑-≼ {k₀ ⊕ [ sub e ]} (zs , refl)))))
                 (λ h → ⊥-elim (tick-read l₀ (ws , refl) h))
                 (λ h → ⊥-elim (tick-read l₀ (⊑-trans (ws , refl) h) (⊑-refl _)))
                 (mk⇔ (λ _ → trans (instant-⊕ k₀ [ ix 0 ]) (sym (trans (instant-⊕ (k₀ ⊕ [ sub e ]) zs) (instant-⊕ k₀ [ sub e ]))))
                      (λ _ → trans (instant-⊕ l₀ [ ix 0 ]) (sym (trans (instant-⊕ (l₀ ⊕ [ sub e′ ]) ws) (instant-⊕ l₀ [ sub e′ ])))))

      echo-m : ∀ {x y x′ y′} → Echo x y → M_b x′ y′ → Σ PMap λ K → Emb K × K x y × K x′ y′
      echo-m {x′ = x′} (k₀ , l₀ , (_ , tk₀) , i₀ , refl , refl) m with x′ ≟ᵖ k₀
      ... | yes e = echo-under tk₀ i₀ m (λ _ → e)
      ... | no ne with T? (inside k₀ x′)
      ...   | no nk  = echo-under tk₀ i₀ m (λ kx → ⊥-elim (nk (⊑-inside kx)))
      ...   | yes ik = _ , echo-read tk₀ i₀ m (inside-⊑ k₀ x′ ik) ne , inj₁ (refl , refl) , inj₂ (refl , refl)

      emb′ : Emb M′
      emb′ = emb-pairs pair
        where
          swap : ∀ {x y x′ y′} → (Σ PMap λ K → Emb K × K x y × K x′ y′) → Σ PMap λ K → Emb K × K x′ y′ × K x y
          swap (K , E , k , k′) = K , E , k′ , k

          pair : ∀ {x y x′ y′} → M′ x y → M′ x′ y′ → Σ PMap λ K → Emb K × K x y × K x′ y′
          pair (inj₁ m) (inj₁ m′) = M_b , hm_b , m , m′
          pair (inj₂ e) (inj₂ e′) = echo-echo e e′
          pair (inj₂ e) (inj₁ m)  = echo-m e m
          pair (inj₁ m) (inj₂ e)  = swap (echo-m e m)

      -- An echo lies one label under its row's carrier, holding no hot row.
      grown′ : ∀ {x y} → M′ x y → M_b x y ⊎ Grown M_b (Hots envP) x y
      grown′ (inj₁ m) = inj₁ m
      grown′ (inj₂ (k₀ , l₀ , (_ , tk₀) , i₀ , refl , refl)) with at-a i₀
      ... | y₀ , m₀ , p₀ =
        inj₂ (k₀ , y₀ , ix 0 , m₀ , ⊑-trans p₀ (⊑-snoc⁺ l₀) , refl , λ hq kq → proj₂ (ok-step p okP) hq (InvAt.world Iσ tk₀) (⊑-inside kq))

      within′ : Within (Hots envP) M₀ M′ p
      within′ (inj₁ m) = within m
      within′ (inj₂ (_ , _ , (_ , tk₀) , _ , refl , refl)) = inj₂ (inW (shrink⁼ (inW (step (inW (InvAt.world Iσ tk₀)) plain-ix))))

      -- Nothing is paired strictly under an echo: the echoes are one label
      -- under source rows, which lie flat.
      echo-bare : ∀ {k e x y} → σP k e → Echo x y → (k ⊕ [ ix 0 ]) ⊑ x → x ≡ k ⊕ [ ix 0 ]
      echo-bare {k} tk (k₀ , _ , (_ , tk₀) , _ , refl , _) kx with ⊑-snoc k₀ kx
      ... | inj₂ e = sym e
      ... | inj₁ kk with σ-flat tk tk₀ (⊑-trans (⊑-snoc⁺ k) kk)
      ...   | refl = ⊥-elim (⊑-≼ kk (≺-ext k []))

      -- Nor under a body row: the body's rows lie past the source's.
      body-echo : ∀ {k e x y} → enter (approx n b envP′) (p ⊕ [ ix 0 ]) k e → Echo x y → k ⊑ x → x ≡ k
      body-echo x (k₀ , _ , (_ , tk₀) , _ , refl , _) kx with ⊑-snoc k₀ kx
      ... | inj₂ e  = sym e
      ... | inj₁ kk = ⊥-elim (body-leads {s = sP} {F = FP} IsP IFP p okP (bw {s = sP} {F = FP} IsP IFP p okP x)
                                (sw {s = sP} {F = FP} IsP IFP p okP tk₀) kk)

      -- What the body's run gives besides its map.
      module Body (br_b : Bare M_b (enter (approx n b envP′) (p ⊕ [ ix 0 ]))) (jn_b : Joins ρ′ envP′ envE′ er′ M_b) (ep_b : EnvPast er′ M_b)
                  (c_b : CarryAt valuesOf M_b (Hots envP′) (Hots envE′) (HotsListed envP′) (enter (approx n b envP′) (p ⊕ [ ix 0 ]))
                           (enter (approx n (elab ρ′ b) envE′) (p′ ⊕ [ ix 0 ])) (p ⊕ [ ix 0 ]) (p′ ⊕ [ ix 0 ]))
                  (nc_b : PBNest er′ M_b c_b) where
        bare : Bare M_b (enter (approx n (connect s b) envP) p)
        bare (Connect.body x , _)          m kx = br_b x m kx
        bare (Connect.burst x _ , _)       m kx = σ-bare x m kx
        bare (Connect.echo x _ _ _ , _)    m kx = σ-bare x m kx
        bare (Connect.kept x _ _ _ , _)    m kx = σ-bare x m kx

        bare′ : Bare M′ (enter (approx n (connect s b) envP) p)
        bare′ r (inj₁ m) kx = bare r m kx
        bare′ (Connect.body x , _)       (inj₂ e) kx = body-echo x e kx
        bare′ (Connect.burst x _ , _)    (inj₂ e) kx = echo-bare x e kx
        bare′ (Connect.echo x _ _ _ , _) (inj₂ e) kx = echo-bare x e kx
        bare′ (Connect.kept x _ _ _ , _) (inj₂ e) kx = echo-bare x e kx

        joins″ : Joins ρ envP envE er M′
        joins″ = joins-grow {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} {er = er} {M = M_b} {N = M′} inj₁
                   (joins-shrink {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} inj₁ er past₁
                     (joins-shrink {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} ms_s er₁ ep_s (joins-unbind er₂ c_a jn_b)))
                   (λ {x} {y} → grown′ {x} {y})

        -- Every binder's late carriers, past the body's map.
        past-b : EnvPast er M_b
        past-b = past-shrink {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} inj₁ er past₁
                   (past-shrink {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} ms_s er₁ ep_s (bind-past er₂ c_a ep_b))

        -- THE CONNECT CARRIES: the body's rows on the body's, each source
        -- row's echo on its annotation's, each burst and kept pin on the
        -- annotation's.
        carried : CarryAt valuesOf M′ (Hots envP) (Hots envE) (HotsListed envP) (enter (approx n (connect s b) envP) p)
                    (enter (approx n (elab ρ (connect s b)) envE) p′) p p′
        carried = ConnCarry.Body.carried {sP = sP} {FP = FP} {sE = sE} {FE = FE} IsP (λ {t} → IFP {t}) IsE (λ {t} → IFE {t}) p p′ okP okE M_s c_a M_b ms_b emb′ c_b

        postulate
          -- Its late carriers under a bound hot's row are anchored.
          conn-nest : PBNest er M′ carried

        conn-carry : Σ (CarryAt valuesOf M′ (Hots envP) (Hots envE) (HotsListed envP) (enter (approx n (connect s b) envP) p)
                               (enter (approx n (elab ρ (connect s b)) envE) p′) p p′)
                       (λ c → PBNest er M′ c)
        conn-carry = carried , conn-nest

        result : CarriesAt n ρ (connect s b) envP envE M₀ er p p′
        result = M′ , (λ m → inj₁ (ms_b (ms_s (inj₁ m)))) , emb′ , within′ , bare′ , joins″
               , grown-past {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} er past-b (λ {x} {y} → grown′ {x} {y})
               , conn-carry

    after : CarriesAt n ρ′ b envP′ envE′ M_s er′ (p ⊕ [ ix 0 ]) (p′ ⊕ [ ix 0 ]) → CarriesAt n ρ (connect s b) envP envE M₀ er p p′
    after (M_b , ms_b , hm_b , wi_b , br_b , jn_b , ep_b , c_b , nc_b) =
      AfterBody.Body.result M_b (λ {x} {y} {q} {a} {σ} → jn_b (here refl) {x} {y} {q} {a} {σ}) ms_b hm_b wi_b br_b jn_b ep_b c_b nc_b

    result : CarriesAt n ρ (connect s b) envP envE M₀ er p p′
    result = after (Carry.carries (hb ρ′) envP′ envE′ gP′ gE′ M_s hm_s er′ joins′ nests′ ap′ (p ⊕ [ ix 0 ]) (p′ ⊕ [ ix 0 ])
                      (ms_s (inj₂ (inj₁ (refl , refl)))) okP′ okE′ nh-b fresh-b)

  after : CarriesAt n ρ s envP envE U.M er₁ (p ⊕ [ ix 1 ]) s₀′ → CarriesAt n ρ (connect s b) envP envE M₀ er p p′
  after (M_s , ms_s , hm_s , wi_s , br_s , jn_s , ep_s , c_s , nc_s) = AfterSource.result M_s ms_s hm_s wi_s br_s jn_s ep_s c_s nc_s

  result : CarriesAt n ρ (connect s b) envP envE M₀ er p p′
  result = after (Carry.carries hs envP envE gP gE U.M U.emb er₁ jn₁ ns₁ ap (p ⊕ [ ix 1 ]) s₀′ (inj₂ (inj₂ (refl , refl)))
                    (ok-step p okP) (ok-step (p′ ⊕ [ ix 1 ]) (ok-step p′ okE)) (λ hq kq → nh hq (⊑-trans (⊑-snoc⁺ p) kq)) (U.fresh-s okP))

-- A `connect` carries when its source and its body do.
carry-connect : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B)
              → Carry m ρ s → (∀ {Δ′} (ρ″ : ∀ {X} → X ∈ L.map AIE (A ∷ Γ) → X ∈ Δ′) → Carry m ρ″ b) → Carry m ρ (connect s b)
carry-connect n ρ s b hs hb = carry λ envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr →
  Assembly.result n ρ s b hs hb envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr
