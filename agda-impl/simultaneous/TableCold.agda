{-# OPTIONS --guardedness #-}

-- A COLD'S RECORD (`cold-tab`).  The elaboration subscribes the cold
-- itself four steps under its own subscription, at `c₀`, so the plain
-- cold's rows are renamed onto the elaborated cold's (`ψ`): a step of
-- the subscribe burst moves under `c₀`, and a later frame's step keeps
-- its label and its tick past the subscription, its timer created where
-- the renamed one is.  Each renamed row is then imaged by its kind
-- (`σ`): a skip on itself, a value on its render's value (one lane down
-- in the subscribe burst, under the minted name's lane in a later
-- frame), the end on the elaboration's end.  Nothing is put late.
--
-- A cut lists more of the cold, never other rows of it, so a plain row
-- agrees between cuts up to itself, and the elaboration up to its image.
module simultaneous.TableCold where

open import Data.Bool using (Bool; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; length; drop; take)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ; _≤_; _+_; _∸_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_⇔_; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

open import denotation.Position using (Pos; root; _≟ᵖ_; _≟ⁱ_; ix; last; _∙_; _⊕_; frame; cascade; instant; path; tick)
open import denotation.Events using (Timeline; From; fixed; fresh; start)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; _≺_; _≼_)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; ≼-refl; ≼-trans; ≺→≼)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (Row; _⊣_)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (One; Shown; Live)
open import simultaneous.Listing using (walkN; listC; listC-ok; UncutEnv)
open import simultaneous.ColdRows using (Kind; kv; ks; ke; kind; module At)
open import simultaneous.ColdList using (module Cold)
open import simultaneous.ColdOrder using (walk-past; walk-nopin)
open import simultaneous.TableCorr using (TR; M; Cons; Got; Corr; Rel)
open import simultaneous.TakeCut using (inst-⊕)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; coldˢ)

------------------------------------------------------------------------
-- A row's kind, and the kind a table lists at a position

kindIn : ∀ {X : Set} → List (Row X) → Pos → Kind
kindIn []             k = ks
kindIn ((y , e) ∷ rs) k with y ≟ᵖ k
... | yes _ = kind e
... | no _  = kindIn rs k

------------------------------------------------------------------------
-- The record

module ColdTab {A : Set} (m : From A 0) (n : ℕ) {Δ : List Set} (ρ* : ℕ → All Tb.Listed Δ) (uρ* : ∀ N → UncutEnv (ρ* N)) (p p* : Pos) where

  open At {A} p* using (c₀; P≼c₀; sync; σ; im; CRow; crow-fwd; crow-bwd; crow-pin; crow-after)

  -- A plain row's position, renamed onto the elaborated cold's.
  ψ : Pos → Pos
  ψ (i ∙ ys) with i ≟ⁱ instant p
  ... | yes _ = c₀ ⊕ drop (length (path p)) ys
  ψ (frame ∙ ys)         | no _ = frame ∙ ys
  ψ (cascade u e l ∙ ys) | no _ = cascade (u ∸ tick p + tick p*) (ψ e) l ∙ ys

  -- And back.
  ψ⁻ : Pos → Pos
  ψ⁻ (i ∙ ys) with i ≟ⁱ instant c₀
  ... | yes _ = p ⊕ drop (length (path c₀)) ys
  ψ⁻ (frame ∙ ys)         | no _ = frame ∙ ys
  ψ⁻ (cascade u e l ∙ ys) | no _ = cascade (u ∸ tick p* + tick p) (ψ⁻ e) l ∙ ys

  -- In the subscribe burst.
  sync* : Pos → Bool
  sync* = sync

  -- The two cuts, and the elaborated cold's own.
  W : ℕ → List (Row A)
  W N = walkN (3 + N) (start p m)

  I : ℕ → List (Row A)
  I N = walkN (3 + N) (start c₀ m)

  P : ℕ → Maybe (Tb.Listed A)
  P N = just (W N ⊣ false)

  Q : ℕ → Maybe (Tb.Listed (IE A))
  Q N = listC (3 + N) n (coldˢ (fixed m)) (ρ* N) p*

  φ′ : ℕ → Pos → Pos
  φ′ N k = σ (kindIn (W N) k) (sync* (ψ k)) (ψ k)

  Put′ : ℕ → Pos → Pos → Set
  Put′ _ _ _ = ⊥

  -- The rows an image can be of.
  trim : ℕ → Pos → Pos
  trim j (i ∙ ys) = i ∙ take (length ys ∸ j) ys

  bk′ : Pos → List Pos
  bk′ l = ψ⁻ l ∷ ψ⁻ (trim 2 l) ∷ ψ⁻ (trim 4 l) ∷ (p ⊕ [ last ]) ∷ []

  walk-at : ∀ K s {k e} → (k , e) ∈ walkN K (start s m) → s ≼ k
  walk-at K s {k} x = ≺→≼ {s} {k} (walk-past K s m x)

  postulate
    -- THE COLD'S WALK: the plain cuts, and the renaming onto the
    -- elaborated cold's.
    walk-ren→  : ∀ {N k e} → (k , e) ∈ W N → (ψ k , e) ∈ I N
    walk-ren←  : ∀ {N y e} → (y , e) ∈ I N → Σ Pos λ k → (k , e) ∈ W N × ψ k ≡ y
    walk-kind  : ∀ {N k e} → (k , e) ∈ W N → kindIn (W N) k ≡ kind e
    walk-func  : ∀ {N k e e′} → (k , e) ∈ W N → (k , e′) ∈ W N → e ≡ e′
    walk-flat  : ∀ {N y e l ys e′} → (y , e) ∈ W N → (y ⊕ (l ∷ ys) , e′) ∈ W N → ⊥
    walk-agree : ∀ {N N′ k e} → N ≤ N′ → (k , e) ∈ W N → AgreeTo k (TR (P N′)) (TR (P N))
    walk-back  : ∀ {N N′ k e} → N ≤ N′ → (k , e) ∈ W N′ → AgreeTo (φ′ N′ k) (TR (Q N′)) (TR (Q N)) → AgreeTo k (TR (P N′)) (TR (P N))
    walk-cons  : ∀ {N N′} → Cons (TR (P N)) (TR (P N′))
    walk-all   : ∀ {N N′} → N ≤ N′ → (∀ q → AgreeTo q (TR (P N′)) (TR (P N))) → I N ≡ I N′
    walk-alone : ∀ {N k e k′ e′} → (k , e) ∈ W N → (k′ , e′) ∈ W N → instantOf k′ ≡ instantOf k → sync* (ψ k) ≡ false → k ≡ k′
    φ-mono     : ∀ {N k e k′ e′} → (k , e) ∈ W N → (k′ , e′) ∈ W N → k ≺ k′ → φ′ N k ≺ φ′ N k′
    φ-inst     : ∀ {N k e k′ e′} → (k , e) ∈ W N → (k′ , e′) ∈ W N → (instantOf (φ′ N k) ≡ instantOf (φ′ N k′) ⇔ instantOf k ≡ instantOf k′)
    φ-home     : ∀ {N k e} → (k , e) ∈ W N → (instantOf (φ′ N k) ≡ instantOf p* ⇔ instantOf k ≡ instantOf p)
    φ-after    : ∀ {N k e} → (k , e) ∈ W N → p* ≼ φ′ N k
    φ-back     : ∀ {N k e} → (k , e) ∈ W N → k ∈ bk′ (φ′ N k)

    -- THE COLD'S ROWS: the written-out rows hang together.
    rows-func   : ∀ {N l e e′} → CRow (I N) l e → CRow (I N) l e′ → e ≡ e′
    rows-flat   : ∀ {N y e l ys e′} → CRow (I N) y e → CRow (I N) (y ⊕ (l ∷ ys)) e′ → ⊥
    rows-causal : ∀ {N N′ y e} → N ≤ N′ → (y , e) ∈ I N → AgreeTo (im y e) (CRow (I N′)) (CRow (I N))
    rows-cons   : ∀ {N N′} → Cons (CRow (I N)) (CRow (I N′))

  -- The elaborated table is the rows written out.
  rows→ : ∀ {N l e′} → TR (Q N) l e′ → CRow (I N) l e′
  rows→ {N} = Equivalence.to (Cold.cold-rows N n (ρ* N) (uρ* N) m p*)

  rows← : ∀ {N l e′} → CRow (I N) l e′ → TR (Q N) l e′
  rows← {N} = Equivalence.from (Cold.cold-rows N n (ρ* N) (uρ* N) m p*)

  -- The elaborated cold's rows lie past its subscription.
  I-after : ∀ {N y e} → (y , e) ∈ I N → p* ≼ y
  I-after {N} {y} x = ≼-trans {p*} {c₀} {y} P≼c₀ (walk-at (3 + N) c₀ x)

  -- Agreement read across the written-out rows.
  ag→ : ∀ {N N′ q} → AgreeTo q (CRow (I N)) (CRow (I N′)) → AgreeTo q (TR (Q N)) (TR (Q N′))
  ag→ a = ⟨ (λ yq → (λ t → rows← (proj₁ (upto a yq) (rows→ t))) , (λ t → rows← (proj₂ (upto a yq) (rows→ t)))) ⟩

  ag← : ∀ {N N′ q} → AgreeTo q (TR (Q N)) (TR (Q N′)) → AgreeTo q (CRow (I N)) (CRow (I N′))
  ag← a = ⟨ (λ yq → (λ t → rows→ (proj₁ (upto a yq) (rows← t))) , (λ t → rows→ (proj₂ (upto a yq) (rows← t)))) ⟩

  -- THE COLD'S PLUMBING: the elaborated table, read off the elaborated
  -- cold's rows.
  cold-fwd : ∀ {N y e} → (y , e) ∈ I N → Σ (Ev (IE A)) λ e′ → TR (Q N) (im y e) e′ × M e e′
  cold-fwd {N} x with crow-fwd (walk-nopin (3 + N) _) x
  ... | e′ , c , mm = e′ , rows← c , mm

  cold-bwd : ∀ {N l e′} → TR (Q N) l e′
           → (Σ Pos λ y → Σ (Ev A) λ e → (y , e) ∈ I N × l ≡ im y e × M e e′)
           ⊎ ((Shown (One valuesOf) e′ → ⊥)
              × (instantOf l ≡ instantOf p* ⊎ Σ Pos λ y → Σ (Ev A) λ e → (y , e) ∈ I N × sync* y ≡ false × instantOf y ≡ instantOf l))
  cold-bwd t = crow-bwd (rows→ t)

  cold-causal : ∀ {N N′ y e} → N ≤ N′ → (y , e) ∈ I N → AgreeTo (im y e) (TR (Q N′)) (TR (Q N))
  cold-causal le x = ag→ (rows-causal le x)

  cold-cons : ∀ {N N′} → Cons (TR (Q N)) (TR (Q N′))
  cold-cons below t t′ yy = rows← (rows-cons (λ lt → ag← (below lt)) (rows→ t) (rows→ t′) yy)

  cold-same : ∀ {N N′} → I N ≡ I N′ → ∀ {l e′} → TR (Q N′) l e′ → TR (Q N) l e′
  cold-same eq t = rows← (subst (λ J → CRow J _ _) (sym eq) (rows→ t))

  cold-func* : ∀ {N l e e′} → TR (Q N) l e → TR (Q N) l e′ → e ≡ e′
  cold-func* t t′ = rows-func (rows→ t) (rows→ t′)

  cold-flat* : ∀ {N y e l ys e′} → TR (Q N) y e → TR (Q N) (y ⊕ (l ∷ ys)) e′ → ⊥
  cold-flat* t t′ = rows-flat (rows→ t) (rows→ t′)

  cold-pin* : ∀ {N l r} → TR (Q N) l (pin r) → ⊥
  cold-pin* t = crow-pin (rows→ t)

  cold-after* : ∀ {N l e} → TR (Q N) l e → p* ≼ l
  cold-after* {N} t = crow-after (I-after {N}) (rows→ t)

  cold-got* : ∀ N → Got (Q N)
  cold-got* N with listC-ok (3 + N) n (coldˢ (fixed m)) (uρ* N) p*
  ... | L , eq , _ = L , eq

  walk-pin : ∀ {N k r} → (k , pin r) ∈ W N → ⊥
  walk-pin {N} = walk-nopin (3 + N) _

  walk-after : ∀ {N k e} → (k , e) ∈ W N → p ≼ k
  walk-after {N} = walk-at (3 + N) p

  unp : ∀ {N k e} → (k , e) ∈ W N → Unpinned e
  unp {e = out _} _ = tt
  unp {e = skip}  _ = tt
  unp {e = end}   _ = tt
  unp {e = pin _} x = walk-pin x

  -- A row's image is its renamed row's.
  φ-im : ∀ {N k e} → (k , e) ∈ W N → φ′ N k ≡ im (ψ k) e
  φ-im {k = k} x = cong (λ kd → σ kd (sync* (ψ k)) (ψ k)) (walk-kind x)

  -- Past the subscribe burst, an image stays in its row's instant.
  σ-inst : ∀ kd y → instantOf (σ kd false y) ≡ instantOf y
  σ-inst kv y = trans (inst-⊕ (y ⊕ [ ix 1 ] ⊕ [ ix 0 ] ⊕ [ ix 1 ]) [ ix 1 ]) (trans (inst-⊕ (y ⊕ [ ix 1 ] ⊕ [ ix 0 ]) [ ix 1 ])
                  (trans (inst-⊕ (y ⊕ [ ix 1 ]) [ ix 0 ]) (inst-⊕ y [ ix 1 ])))
  σ-inst ks y = refl
  σ-inst ke y = trans (inst-⊕ (y ⊕ [ ix 1 ]) [ last ]) (inst-⊕ y [ ix 1 ])

  img : ∀ {N k e} → (k , e) ∈ W N → Σ (Ev (IE A)) λ e′ → TR (Q N) (φ′ N k) e′ × M e e′
  img x with cold-fwd (walk-ren→ x)
  ... | e′ , y , mm = e′ , subst (λ l → TR _ l e′) (sym (φ-im x)) y , mm

  causal : ∀ {N N′ k e} → N ≤ N′ → (k , e) ∈ W N → AgreeTo (φ′ N k) (TR (Q N′)) (TR (Q N))
  causal le x = subst (λ l → AgreeTo l _ _) (sym (φ-im x)) (cold-causal le (walk-ren→ x))

  agree-φ : ∀ {N N′ k e} → (k , e) ∈ W N → AgreeTo k (TR (P N)) (TR (P N′)) → φ′ N k ≡ φ′ N′ k
  agree-φ {N} {N′} {k} {e} x a with proj₁ (AgreeTo.upto a (≼-refl {k})) (_ , refl , x)
  ... | _ , refl , x′ = cong (λ kd → σ kd (sync* (ψ k)) (ψ k)) (trans (walk-kind x) (sym (walk-kind x′)))

  corr′ : ∀ N → Corr p p* (φ′ N) (Put′ N) (TR (P N)) (TR (Q N))
  corr′ N = record
    { row→ = λ { (_ , refl , x) _ → inj₁ (img x) }
    ; pin→ = λ { (_ , refl , x) _ → ⊥-elim (walk-pin x) }
    ; put-before = λ _ ()
    ; shown← = shown′
    ; place = place′
    ; mono = λ { (_ , refl , x) (_ , refl , x′) _ _ lt → φ-mono x x′ lt }
    ; inst = λ { (_ , refl , x) (_ , refl , x′) _ _ → φ-inst x x′ }
    ; home = λ { (_ , refl , x) _ → φ-home x } }
    where
      shown′ : ∀ {l e′} → TR (Q N) l e′ → Shown (One valuesOf) e′
             → Σ Pos λ k → Σ (Ev A) λ e → l ≡ φ′ N k × TR (P N) k e × Unpinned e × M e e′
      shown′ q sh with cold-bwd q
      ... | inj₂ (ns , _) = ⊥-elim (ns sh)
      ... | inj₁ (y , e , iy , eq , mm) with walk-ren← iy
      ...   | k , x , refl = k , e , trans eq (sym (φ-im x)) , (_ , refl , x) , unp x , mm

      place′ : ∀ {l e′} → TR (Q N) l e′ → Live (TR (Q N)) l
             → instantOf l ≡ instantOf p*
             ⊎ Σ Pos λ k → Σ (Ev A) λ e → TR (P N) k e × Unpinned e × (Σ (Ev (IE A)) λ e′ → TR (Q N) (φ′ N k) e′ × M e e′)
               × (φ′ N k ≼ l ⊎ (∀ {k′ e″} → TR (P N) k′ e″ → Unpinned e″ → instantOf k′ ≡ instantOf k → k ≼ k′))
               × instantOf (φ′ N k) ≡ instantOf l
      place′ {l} q _ with cold-bwd q
      ... | inj₂ (_ , inj₁ i) = inj₁ i
      ... | inj₁ (y , e , iy , eq , mm) with walk-ren← iy
      ...   | k , x , refl with trans eq (sym (φ-im x))
      ...     | refl = inj₂ (k , e , (_ , refl , x) , unp x , img x , inj₁ (≼-refl {l}) , refl)
      place′ {l} q _ | inj₂ (_ , inj₂ (y , e , iy , as , ieq)) with walk-ren← iy
      ... | k , x , refl = inj₂ (k , e , (_ , refl , x) , unp x , img x , inj₂ leads , trans (cong instantOf (φ-im x)) inst)
        where
          leads : ∀ {k′ e″} → TR (P N) k′ e″ → Unpinned e″ → instantOf k′ ≡ instantOf k → k ≼ k′
          leads (_ , refl , x′) _ eq′ with walk-alone x x′ eq′ as
          ... | refl = ≼-refl {k}

          inst : instantOf (im (ψ k) e) ≡ instantOf l
          inst rewrite as = trans (σ-inst (kind e) (ψ k)) ieq

  rel′ : Rel P Q p p*
  rel′ = record
    { φ = φ′ ; Put = Put′ ; corr = corr′
    ; φ-agree = λ { (_ , refl , x) _ a → agree-φ x a }
    ; bk = λ _ → bk′
    ; in-bk = λ { (_ , refl , x) _ → φ-back x }
    ; pb-few = λ _ _ → [] , λ ()
    ; back = λ { le (_ , refl , x) _ a → walk-back le x a }
    ; put-up = λ _ _ ()
    ; back-put = λ _ ()
    ; elab-causal = λ { le (_ , refl , x) _ _ → causal le x }
    ; stable← = λ { le (_ , refl , x) _ _ _ → walk-agree le x }
    ; stable-put = λ _ _ _ ()
    ; stable-lead = λ { le (_ , refl , x) _ _ _ _ _ _ → causal le x }
    ; elab-all = λ le a → cold-same (walk-all le a)
    ; func = λ { (_ , refl , x) (_ , refl , x′) → walk-func x x′ }
    ; func* = cold-func*
    ; flat = λ { (_ , refl , x) (_ , refl , x′) → walk-flat x x′ }
    ; flat* = cold-flat*
    ; pin-in = λ { (_ , refl , x) → ⊥-elim (walk-pin x) }
    ; pin-in* = λ y → ⊥-elim (cold-pin* y)
    ; cons = walk-cons
    ; cons* = cold-cons
    ; got = λ _ → _ , refl
    ; got* = cold-got*
    ; after = λ { (_ , refl , x) → walk-after x }
    ; after* = cold-after*
    ; after-φ = λ { (_ , refl , x) _ → φ-after x }
    ; pin-after* = λ y → ⊥-elim (cold-pin* y)
    ; pin-stable = λ _ _ _ _ _ _ y → ⊥-elim (cold-pin* y) }

cold-tab : ∀ {A} (m : From A 0) n {Δ} (ρ* : ℕ → All Tb.Listed Δ) (uρ* : ∀ N → UncutEnv (ρ* N)) p p* → Rel (ColdTab.P m n ρ* uρ* p p*) (ColdTab.Q m n ρ* uρ* p p*) p p*
cold-tab m n ρ* uρ* p p* = ColdTab.rel′ m n ρ* uρ* p p*
