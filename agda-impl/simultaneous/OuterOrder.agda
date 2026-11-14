{-# OPTIONS --guardedness #-}

-- THE ELABORATED OUTER READ AGAINST THE PLAIN: a flatMap's elaborated
-- joiner reads its outer's values off a hot of the elaborated source, one
-- reading lane per emit, each value on its lane's first row.  So every
-- elaborated value is a source value read at `Q l`, which the source's
-- carry reads back to a plain value in the same order; and a value read
-- before a carrier on a map embedding the source's carriers came before
-- the row carried there, unless that row lies over the value.
module simultaneous.OuterOrder where

open import Data.Bool.Properties using (T?)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_; []; [_]; _++_)
open import Data.List.Properties using (∷-injectiveˡ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (decidable-stable)

open import denotation.Position using (Pos; ix; sub; _⊕_; _<ᵖ_)
open import denotation.Events using (ofᴱ)
open import denotation.EmissionSet using (out; end; skip; pin; EmissionSet; Truncate; Proper; Reach; hot; enter; _≺_; InE; at-out;
  on-out; Rejoin; module Merge; module Op)
open import denotation.Laws.Worlds using (InvAt; _⊑_; ⊕-assoc; ⊕-identityʳ; ⊕-injˡ)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≼-split)
open import denotation.Laws.Count using (⊑?)
open import simultaneous.InstEmit using (InstEmit; instEmit; value; mark; valuesOf)
open import simultaneous.CarryBase using (PMap; _⊆ᴹ_; Emb; CarryAt; apart; module Mono)
open import simultaneous.JoinCarry using (unpin-few)

module Read {N A : Set} {HP HE LP : Pos → Set} (q₁ : Pos) {p s′ : Pos} {o : EmissionSet A} (Io : InvAt HP p o)
            {σ : EmissionSet (InstEmit N A)} (Iσ : InvAt HE s′ σ) (reachσ : ∀ {l e} → σ l e → Reach σ l e)
            (M_s : PMap) (hm_s : Emb M_s) (c_s : CarryAt valuesOf M_s HP HE LP o σ p s′) where
  module S = CarryAt c_s

  -- Where the elaborated outer shows a value read at `l`.
  Q : Pos → Pos
  Q l = ((l ⊕ [ sub q₁ ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]

  Q-eq : ∀ l → Q l ≡ l ⊕ (sub q₁ ∷ ix 1 ∷ ix 0 ∷ [])
  Q-eq l = trans (⊕-assoc (l ⊕ [ sub q₁ ]) [ ix 1 ] [ ix 0 ]) (⊕-assoc l [ sub q₁ ] (ix 1 ∷ ix 0 ∷ []))

  Q-path : ∀ l zs → Q (l ⊕ zs) ≡ l ⊕ (zs ++ sub q₁ ∷ ix 1 ∷ ix 0 ∷ [])
  Q-path l zs = trans (Q-eq (l ⊕ zs)) (⊕-assoc l zs (sub q₁ ∷ ix 1 ∷ ix 0 ∷ []))

  Q-inj : ∀ {l l′} → Q l ≡ Q l′ → l ≡ l′
  Q-inj {l} {l′} e = ⊕-injˡ l l′ (⊕-injˡ (l ⊕ [ sub q₁ ]) (l′ ⊕ [ sub q₁ ]) (⊕-injˡ ((l ⊕ [ sub q₁ ]) ⊕ [ ix 1 ]) ((l′ ⊕ [ sub q₁ ]) ⊕ [ ix 1 ]) e))

  -- Two of the source's rows, one before the other, are read in order.
  Q-mono : ∀ {l l′ e e′} → σ l e → σ l′ e′ → l ≺ l′ → Q l ≺ Q l′
  Q-mono {l} {l′} y y′ lt = subst₂ _≺_ (sym (Q-eq l)) (sym (Q-eq l′)) (apart lt nu (sub q₁ ∷ ix 1 ∷ ix 0 ∷ []) (sub q₁ ∷ ix 1 ∷ ix 0 ∷ []))
    where
      nu : ¬ (l ⊑ l′)
      nu ([] , refl)    = ≺-irrefl {l} (subst (l ≺_) (⊕-identityʳ l) lt)
      nu (_ ∷ _ , refl) = InvAt.flat Iσ y y′

  -- THE ELABORATED OUTER'S VALUES are its source's, each read on its
  -- reading lane's first row.
  module MJ = Merge (λ (x : InstEmit N A) → Op.of (valuesOf x)) (enter (hot (Proper σ)) q₁)

  O* : EmissionSet A
  O* = Truncate MJ.JoinT

  of-one : ∀ {s k a} (x : InstEmit N A) → InE (ofᴱ s 0 (valuesOf x)) k (out a) → valuesOf x ≡ a ∷ [] × k ≡ s ⊕ [ ix 0 ]
  of-one (instEmit (value _) _) at-out      = refl , refl
  of-one (instEmit (value _) _) (on-out ())
  of-one (instEmit (mark _) _) ()

  star-read : ∀ {q* a} → O* q* (out a) → Σ Pos λ l → Σ (InstEmit N A) λ x → Proper σ l (out x) × valuesOf x ≡ a ∷ [] × q* ≡ Q l
  star-read ((MJ.lane {a = x} (Rejoin.shown y _ _ , _) _ ((r , _) , _) _ _) , _) with of-one x r
  ... | vx , refl = _ , x , y , vx , refl
  star-read ((MJ.run () _) , _)

  -- Read back through the source's carry: few of its rows lie before
  -- any.
  read-back : ∀ {l x a} → Proper σ l (out x) → valuesOf x ≡ a ∷ [] → Σ Pos λ q′ → S.Img q′ l × o q′ (out a)
  read-back {l} {x} {a} y vx with S.shown (proj₁ y) (a , vx) tt (proj₂ y) (unpin-few {e = out x} tt (reachσ (proj₁ y)))
  ... | q′ , i′ , out b , x′ , m with proj₁ m tt
  ...   | _ , refl , vb = q′ , i′ , subst (λ z → o q′ (out z)) (∷-injectiveˡ (trans (sym vb) vx)) x′
  read-back y vx | q′ , i′ , end , x′ , m with proj₁ m tt
  ... | ()
  read-back y vx | q′ , i′ , skip , x′ , m  = ⊥-elim (proj₂ m (λ ()) (_ , vx))
  read-back y vx | q′ , i′ , pin _ , x′ , m = ⊥-elim (proj₂ m (λ ()) (_ , vx))

  module MS = Mono hm_s (λ {y} {e} {l} {ys} {e′} → InvAt.flat Io {y} {e} {l} {ys} {e′}) c_s

  -- Two values read in order were the outer's in order.
  value-order : ∀ {q q′ l₀ l′ e₀ e′} → S.Img q l₀ → S.Img q′ l′ → σ l₀ e₀ → σ l′ e′ → Q l₀ ≺ Q l′ → q ≺ q′
  value-order {q} {q′} {l₀} {l′} i₀ i′ y₀ y′ qq = decidable-stable (T? (q <ᵖ q′)) λ nq → go (≼-split {q′} {q} nq)
    where
      go : q′ ≺ q ⊎ q′ ≡ q → ⊥
      go (inj₂ e)  = ≺-irrefl {Q l₀} (subst (λ z → Q l₀ ≺ Q z) (sym (S.img-fun i₀ (subst (λ z → S.Img z l′) e i′))) qq)
      go (inj₁ lt) = ≺-absurd {Q l′} {Q l₀} (Q-mono y′ y₀ (MS.img-mono i′ i₀ lt)) qq

  -- A VALUE READ BEFORE A CARRIER came before the row carried there: on a
  -- map embedding the source's carriers, unless the row lies over the
  -- value.
  past-row : ∀ {M : PMap} → Emb M → M_s ⊆ᴹ M → ∀ {k y l q′ l′} → M k y → y ⊑ l → (k ⊑ q′ → ⊥) → S.Img q′ l′ → Q l′ ≺ l → q′ ≺ k
  past-row {M} hm ms {k} {y} {l} {q′} {l′} my (σ₀ , eq) off i′ lt = decidable-stable (T? (q′ <ᵖ k)) λ nk → over (≼-split {k} {q′} nk)
    where
      over : k ≺ q′ ⊎ k ≡ q′ → ⊥
      over (inj₂ e) = off (subst (k ⊑_) e ([] , sym (⊕-identityʳ k)))
      over (inj₁ kq) with S.ext i′
      ... | y′ , my′ , σ′ , eq′ with ⊑? y y′
      ...   | yes yy = off (Emb.reflect hm my (ms my′) yy)
      ...   | no ny  = ≺-absurd {l} {Q l′}
                         (subst₂ _≺_ (sym eq) (trans (sym (Q-path y′ σ′)) (cong Q (sym eq′)))
                           (apart (Emb.mono hm my (ms my′) kq) ny σ₀ (σ′ ++ sub q₁ ∷ ix 1 ∷ ix 0 ∷ []))) lt

  -- A SWITCH'S LANE IS CUT WHERE ITS PARTNER IS, read back: the elaborated
  -- value cutting it reads a plain one, in order.
  switch-read : ∀ {q l₀ a k l} → S.Img q l₀ → O* (Q l₀) (out a)
              → (Σ Pos λ q*′ → Σ A λ a′ → O* q*′ (out a′) × Q l₀ ≺ q*′ × q*′ ≺ l)
              → (∀ {q′ a′ l′} → o q′ (out a′) → S.Img q′ l′ → Q l′ ≺ l → q′ ≺ k)
              → Σ Pos λ q′ → Σ A λ a′ → o q′ (out a′) × q ≺ q′ × q′ ≺ k
  switch-read i₀ x* (q*′ , a′ , x*′ , qq , ql) past with star-read x*′ | star-read x*
  ... | l′ , _ , y′ , vx , refl | l₁ , _ , y₁ , _ , e₁ with read-back y′ vx
  ...   | q′ , i′ , x′ = q′ , a′ , x′ , value-order i₀ i′ (subst (λ z → σ z _) (Q-inj (sym e₁)) (proj₁ y₁)) (proj₁ y′) qq , past x′ i′ ql
