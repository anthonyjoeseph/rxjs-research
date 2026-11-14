{-# OPTIONS --guardedness #-}

-- TWO CHILDREN, ONE LABEL APART: a former subscribing children at its
-- plain `ix 0` and `ix 1` pairs each with the foot of the elaborated
-- child, which lies under the elaborated former's own `ix 0` and `ix 1`.
-- A connect's body and source, a defer's guard and body.
module simultaneous.CarryPair where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_]; _++_)
open import Data.List.Properties using (++-cancelˡ; ∷-injectiveˡ; ++-assoc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import denotation.Position using (Pos; Path; Label; ix; _∙_; _⊕_)
open import denotation.EmissionSet using (_≺_)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≺-ext; ticks)
open import denotation.Laws.Worlds using (_⊑_; ⊑-refl; ⊑-≼; ⊕-assoc; here; inW; step; plain-ix; not-up; sib; nest-in; Real)
open import simultaneous.Readings using (instantOf)
open import simultaneous.CarryBase using (PMap; _∪ᴹ_; Emb; Fresh; apart; emb-under; instant-⊕)
open import simultaneous.Carry using (Within; Grown; NotHot)

private
  path-of : Pos → Path
  path-of (_ ∙ ps) = ps

  -- Two positions one step apart under a common one lead nothing of each other.
  lab : ∀ q {a b} σ τ → (q ⊕ (a ∷ σ)) ⊑ (q ⊕ (b ∷ τ)) → b ≡ a
  lab (i ∙ ps) {a} {b} σ τ (zs , e) =
    ∷-injectiveˡ (++-cancelˡ ps (b ∷ τ) (a ∷ σ ++ zs) (trans (cong path-of e) (++-assoc ps (a ∷ σ) zs)))

  shape : ∀ q {a} σ → (q ⊕ [ a ]) ⊕ σ ≡ q ⊕ (a ∷ σ)
  shape q {a} σ = ⊕-assoc q [ a ] σ

module PairAt (p p′ : Pos) (σ₀ σ₁ : Path) where
  y₀ y₁ : Pos
  y₀ = (p′ ⊕ [ ix 0 ]) ⊕ σ₀
  y₁ = (p′ ⊕ [ ix 1 ]) ⊕ σ₁

  N : PMap
  N x y = (x ≡ p ⊕ [ ix 0 ] × y ≡ y₀) ⊎ (x ≡ p ⊕ [ ix 1 ] × y ≡ y₁)

  ix01 : p ⊕ [ ix 0 ] ≡ p ⊕ [ ix 1 ] → ⊥
  ix01 e with lab p [] [] (subst ((p ⊕ [ ix 0 ]) ⊑_) e (⊑-refl (p ⊕ [ ix 0 ])))
  ... | ()

  private
    sh₀₁ : y₀ ⊑ y₁ → (p′ ⊕ (ix 0 ∷ σ₀)) ⊑ (p′ ⊕ (ix 1 ∷ σ₁))
    sh₀₁ h = subst (_⊑ (p′ ⊕ (ix 1 ∷ σ₁))) (shape p′ σ₀) (subst (y₀ ⊑_) (shape p′ σ₁) h)

    sh₁₀ : y₁ ⊑ y₀ → (p′ ⊕ (ix 1 ∷ σ₁)) ⊑ (p′ ⊕ (ix 0 ∷ σ₀))
    sh₁₀ h = subst (_⊑ (p′ ⊕ (ix 0 ∷ σ₀))) (shape p′ σ₁) (subst (y₁ ⊑_) (shape p′ σ₀) h)

  y₀₁ : y₀ ⊑ y₁ → ⊥
  y₀₁ h with lab p′ σ₀ σ₁ (sh₀₁ h)
  ... | ()

  y₁₀ : y₁ ⊑ y₀ → ⊥
  y₁₀ h with lab p′ σ₁ σ₀ (sh₁₀ h)
  ... | ()

  y₀≺y₁ : y₀ ≺ y₁
  y₀≺y₁ = apart (ticks p′ 0) (λ h → y₀₁′ h) σ₀ σ₁
    where
      y₀₁′ : (p′ ⊕ [ ix 0 ]) ⊑ (p′ ⊕ [ ix 1 ]) → ⊥
      y₀₁′ h with lab p′ [] [] h
      ... | ()

  i₀ : instantOf y₀ ≡ instantOf p′
  i₀ = trans (instant-⊕ (p′ ⊕ [ ix 0 ]) σ₀) (instant-⊕ p′ [ ix 0 ])

  i₁ : instantOf y₁ ≡ instantOf p′
  i₁ = trans (instant-⊕ (p′ ⊕ [ ix 1 ]) σ₁) (instant-⊕ p′ [ ix 1 ])

  iP : ∀ {x y} → N x y → instantOf x ≡ instantOf p
  iP (inj₁ (refl , _)) = instant-⊕ p [ ix 0 ]
  iP (inj₂ (refl , _)) = instant-⊕ p [ ix 1 ]

  iE : ∀ {x y} → N x y → instantOf y ≡ instantOf p′
  iE (inj₁ (_ , refl)) = i₀
  iE (inj₂ (_ , refl)) = i₁

  embN : Emb N
  embN = record
    { fun     = λ { (inj₁ (refl , refl)) (inj₁ (_ , refl)) → refl
                  ; (inj₂ (refl , refl)) (inj₂ (_ , refl)) → refl
                  ; (inj₁ (refl , _))    (inj₂ (e , _))    → ⊥-elim (ix01 e)
                  ; (inj₂ (refl , _))    (inj₁ (e , _))    → ⊥-elim (ix01 (sym e)) }
    ; mono    = λ { (inj₁ (refl , refl)) (inj₁ (refl , refl)) h → ⊥-elim (≺-irrefl {p ⊕ [ ix 0 ]} h)
                  ; (inj₂ (refl , refl)) (inj₂ (refl , refl)) h → ⊥-elim (≺-irrefl {p ⊕ [ ix 1 ]} h)
                  ; (inj₁ (refl , refl)) (inj₂ (refl , refl)) _ → y₀≺y₁
                  ; (inj₂ (refl , refl)) (inj₁ (refl , refl)) h → ⊥-elim (≺-absurd {p ⊕ [ ix 0 ]} {p ⊕ [ ix 1 ]} (ticks p 0) h) }
    ; reflect = λ { (inj₁ (refl , refl)) (inj₁ (refl , refl)) _ → ⊑-refl _
                  ; (inj₂ (refl , refl)) (inj₂ (refl , refl)) _ → ⊑-refl _
                  ; (inj₁ (refl , refl)) (inj₂ (refl , refl)) h → ⊥-elim (y₀₁ h)
                  ; (inj₂ (refl , refl)) (inj₁ (refl , refl)) h → ⊥-elim (y₁₀ h) }
    ; inst    = λ n n′ → mk⇔ (λ _ → trans (iP n) (sym (iP n′))) (λ _ → trans (iE n) (sym (iE n′)))
    }

  sh : ∀ {x y} → N x y → Σ Label λ a → Σ Path λ σ → Σ Label λ b → Σ Path λ σ′ → x ≡ p ⊕ (a ∷ σ) × y ≡ p′ ⊕ (b ∷ σ′)
  sh (inj₁ (refl , refl)) = ix 0 , [] , ix 0 , σ₀ , refl , shape p′ σ₀
  sh (inj₂ (refl , refl)) = ix 1 , [] , ix 1 , σ₁ , refl , shape p′ σ₁

-- A map held fresh grown by the two subscriptions.
module PairUnder {H : Pos → Set} {M₀ : PMap} {p p₀ p′ : Pos} (E₀ : Emb M₀) (fr : Fresh H M₀ p) (m₀ : M₀ p p₀) (pp : p₀ ⊑ p′)
                 (σ₀ σ₁ : Path) where
  open PairAt p p′ σ₀ σ₁ public

  M : PMap
  M = M₀ ∪ᴹ N

  emb : Emb M
  emb = emb-under {N = N} E₀ fr m₀ pp embN sh

  within : Within H M₀ M p
  within (inj₁ m)                 = inj₁ m
  within (inj₂ (inj₁ (refl , _))) = inj₂ (λ n → n (inW (step here plain-ix)))
  within (inj₂ (inj₂ (refl , _))) = inj₂ (λ n → n (inW (step here plain-ix)))

  private
    under : ∀ {a} σ → p₀ ⊑ ((p′ ⊕ [ a ]) ⊕ σ)
    under {a} σ = let (zs , e) = pp in zs ++ (a ∷ σ) , trans (shape p′ σ) (trans (cong (_⊕ (a ∷ σ)) e) (⊕-assoc p₀ zs (a ∷ σ)))

  grown : ∀ {R} → NotHot R p → ∀ {x y} → M x y → M₀ x y ⊎ Grown M₀ R x y
  grown _  (inj₁ m)                    = inj₁ m
  grown nh (inj₂ (inj₁ (refl , refl))) = inj₂ (p , p₀ , ix 0 , m₀ , under σ₀ , refl , nh)
  grown nh (inj₂ (inj₂ (refl , refl))) = inj₂ (p , p₀ , ix 1 , m₀ , under σ₁ , refl , nh)

  -- Nothing it pairs lies strictly under `p ⊕ [ ix 0 ]`.
  bare₀ : ∀ {x y} → M x y → (p ⊕ [ ix 0 ]) ⊑ x → x ≡ p ⊕ [ ix 0 ]
  bare₀ (inj₁ m) gx with fr m (p ⊕ [ ix 0 ] , inW (step here plain-ix) , gx)
  ... | refl = ⊥-elim (⊑-≼ gx (≺-ext p []))
  bare₀ (inj₂ (inj₁ (refl , _))) _  = refl
  bare₀ (inj₂ (inj₂ (refl , _))) gx with lab p [] [] gx
  ... | ()

  -- The second subscription is held fresh.
  fresh₁ : Real p → Fresh H M (p ⊕ [ ix 1 ])
  fresh₁ ok (inj₁ m) (w , ww , wx) with fr m (w , inW (nest-in (step here plain-ix) ww) , wx)
  ... | refl = ⊥-elim (not-up ok ww wx)
  fresh₁ ok (inj₂ (inj₁ (refl , _))) (w , ww , wx) = ⊥-elim (sib ok plain-ix (⊑-refl p) ix01 ww wx)
  fresh₁ ok (inj₂ (inj₂ (refl , _))) _ = refl
