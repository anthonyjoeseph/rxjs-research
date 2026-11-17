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

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; length; drop; take)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ; _≤_; _+_; _∸_)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_⇔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no; does)

open import denotation.Position using (Pos; root; _≟ᵖ_; _≟ⁱ_; ix; last; _∙_; _⊕_; frame; cascade; instant; path; tick)
open import denotation.Events using (Timeline; From; fixed; fresh; start)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; _≺_; _≼_)
open import denotation.Laws.Modulus using (AgreeTo; ≼-refl)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (Row; _⊣_)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (One; Shown; Live)
open import simultaneous.Listing using (walkN; listC)
open import simultaneous.TableCorr using (TR; M; Cons; Got; Corr; Rel)
open import simultaneous.TakeCut using (inst-⊕)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; coldˢ)

------------------------------------------------------------------------
-- A row's kind, and the kind a table lists at a position

data Kind : Set where
  kv ks ke : Kind

kind : ∀ {X : Set} → Ev X → Kind
kind (out _) = kv
kind skip    = ks
kind end     = ke
kind (pin _) = ks

kindIn : ∀ {X : Set} → List (Row X) → Pos → Kind
kindIn []             k = ks
kindIn ((y , e) ∷ rs) k with y ≟ᵖ k
... | yes _ = kind e
... | no _  = kindIn rs k

------------------------------------------------------------------------
-- The record

module ColdTab {A : Set} (m : From A 0) (n : ℕ) {Δ : List Set} (ρ* : ℕ → All Tb.Listed Δ) (p p* : Pos) where

  -- Where the elaboration subscribes the cold.
  c₀ : Pos
  c₀ = p* ⊕ (ix 0 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ [])

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
  sync* y = does (instantOf y ≟ⁱ instantOf p*)

  -- An elaborated cold's row of a kind, imaged.
  σ : Kind → Bool → Pos → Pos
  σ kv true  y = y ⊕ (ix 1 ∷ ix 0 ∷ [])
  σ kv false y = y ⊕ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ [])
  σ ks _     y = y
  σ ke true  y = p* ⊕ [ last ]
  σ ke false y = y ⊕ (ix 1 ∷ last ∷ [])

  im : ∀ {X : Set} → Pos → Ev X → Pos
  im y e = σ (kind e) (sync* y) y

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

  postulate
    -- THE COLD'S WALK: the plain cuts, and the renaming onto the
    -- elaborated cold's.
    walk-ren→  : ∀ {N k e} → (k , e) ∈ W N → (ψ k , e) ∈ I N
    walk-ren←  : ∀ {N y e} → (y , e) ∈ I N → Σ Pos λ k → (k , e) ∈ W N × ψ k ≡ y
    walk-kind  : ∀ {N k e} → (k , e) ∈ W N → kindIn (W N) k ≡ kind e
    walk-func  : ∀ {N k e e′} → (k , e) ∈ W N → (k , e′) ∈ W N → e ≡ e′
    walk-flat  : ∀ {N y e l ys e′} → (y , e) ∈ W N → (y ⊕ (l ∷ ys) , e′) ∈ W N → ⊥
    walk-pin   : ∀ {N k r} → (k , pin r) ∈ W N → ⊥
    walk-after : ∀ {N k e} → (k , e) ∈ W N → p ≼ k
    walk-agree : ∀ {N N′ k e} → N ≤ N′ → (k , e) ∈ W N → AgreeTo k (TR (P N′)) (TR (P N))
    walk-cons  : ∀ {N N′} → Cons (TR (P N)) (TR (P N′))
    walk-all   : ∀ {N N′} → N ≤ N′ → (∀ q → AgreeTo q (TR (P N′)) (TR (P N))) → I N ≡ I N′
    walk-alone : ∀ {N k e k′ e′} → (k , e) ∈ W N → (k′ , e′) ∈ W N → instantOf k′ ≡ instantOf k → sync* (ψ k) ≡ false → k ≡ k′
    φ-mono     : ∀ {N k e k′ e′} → (k , e) ∈ W N → (k′ , e′) ∈ W N → k ≺ k′ → φ′ N k ≺ φ′ N k′
    φ-inst     : ∀ {N k e k′ e′} → (k , e) ∈ W N → (k′ , e′) ∈ W N → (instantOf (φ′ N k) ≡ instantOf (φ′ N k′) ⇔ instantOf k ≡ instantOf k′)
    φ-home     : ∀ {N k e} → (k , e) ∈ W N → (instantOf (φ′ N k) ≡ instantOf p* ⇔ instantOf k ≡ instantOf p)
    φ-after    : ∀ {N k e} → (k , e) ∈ W N → p* ≼ φ′ N k
    φ-back     : ∀ {N k e} → (k , e) ∈ W N → k ∈ bk′ (φ′ N k)

    -- THE COLD'S PLUMBING: the elaborated table, read off the
    -- elaborated cold's rows.
    cold-fwd    : ∀ {N y e} → (y , e) ∈ I N → Σ (Ev (IE A)) λ e′ → TR (Q N) (im y e) e′ × M e e′
    cold-bwd    : ∀ {N l e′} → TR (Q N) l e′
                → (Σ Pos λ y → Σ (Ev A) λ e → (y , e) ∈ I N × l ≡ im y e × M e e′)
                ⊎ ((Shown (One valuesOf) e′ → ⊥)
                   × (instantOf l ≡ instantOf p* ⊎ Σ Pos λ y → Σ (Ev A) λ e → (y , e) ∈ I N × sync* y ≡ false × instantOf y ≡ instantOf l))
    cold-causal : ∀ {N N′ y e} → N ≤ N′ → (y , e) ∈ I N → AgreeTo (im y e) (TR (Q N′)) (TR (Q N))
    cold-cons   : ∀ {N N′} → Cons (TR (Q N)) (TR (Q N′))
    cold-same   : ∀ {N N′} → I N ≡ I N′ → ∀ {l e′} → TR (Q N′) l e′ → TR (Q N) l e′
    cold-func*  : ∀ {N l e e′} → TR (Q N) l e → TR (Q N) l e′ → e ≡ e′
    cold-flat*  : ∀ {N y e l ys e′} → TR (Q N) y e → TR (Q N) (y ⊕ (l ∷ ys)) e′ → ⊥
    cold-pin*   : ∀ {N l r} → TR (Q N) l (pin r) → ⊥
    cold-after* : ∀ {N l e} → TR (Q N) l e → p* ≼ l
    cold-got*   : ∀ N → Got (Q N)

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
  σ-inst kv y = inst-⊕ y (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ [])
  σ-inst ks y = refl
  σ-inst ke y = inst-⊕ y (ix 1 ∷ last ∷ [])

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
    ; bk = bk′
    ; in-bk = λ { (_ , refl , x) _ → φ-back x }
    ; pb-few = λ _ → [] , λ ()
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
    ; after-φ = λ { (_ , refl , x) _ → φ-after x } }

cold-tab : ∀ {A} (m : From A 0) n {Δ} (ρ* : ℕ → All Tb.Listed Δ) p p* → Rel (ColdTab.P m n ρ* p p*) (ColdTab.Q m n ρ* p p*) p p*
cold-tab m n ρ* p p* = ColdTab.rel′ m n ρ* p p*
