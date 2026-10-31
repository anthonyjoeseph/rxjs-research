------------------------------------------------------------------------
-- A SCAN'S RISE.  A scan's rising value is the least of its source's
-- rows, every other row lying strictly past it, so its fold leads the
-- scanned rows and the rest fold from it; an end rises unfolded, adding
-- no value to any fold.
------------------------------------------------------------------------

module adequacy.RiseScan where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Product using (Σ; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import denotation.EmissionSet using (EmissionSet; out; end; module Scan; _≼_; _≺_)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≺→≼; ≼-refl)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; ⟨_,_,_,_⟩; rising; alive; nx; cp; scanS; inScan)
open import adequacy.Rows using (env; rows; Plus; old; new; _≃_; _⇄_; silent)
open import adequacy.Bound using (Empty)
open import adequacy.Up using (up-≃; vis-≃)
open import adequacy.Skip using (After)
open import adequacy.Inv using (Sim; inv; open-alive; anc-liv; node-f; tr)
open import adequacy.Above using (anc-≃; anc-swap)

open Scan using (Acc; acc₀; acc; ScanT; sval; sstep; spin; send)

-- A fold's position holds one of its source's values.
acc-row : ∀ {A B} {f : B → A → B} {z} {t : EmissionSet A} {q b} → Acc f z t q b → Σ A λ a → t q (out a)
acc-row (acc₀ r _)    = _ , r
acc-row (acc _ r _ _) = _ , r

plus-at : ∀ {A} {t : EmissionSet A} {p v q e} → After p t → Plus t p v q e → p ≼ q
plus-at {p = p} {q = q} af (old r) = ≺→≼ {p} {q} (af r)
plus-at {p = p}         af new     = ≼-refl {p}

after-scan : ∀ {A B} (f : B → A → B) z {t : EmissionSet A} {p} → After p t → After p (ScanT f z t)
after-scan f z af (sval x)  with acc-row x
... | _ , r = af r
after-scan f z af (sstep r) = af r
after-scan f z af (spin r)  = af r
after-scan f z af (send r)  = af r

empty-scan : ∀ {A B} (f : B → A → B) z {t : EmissionSet A} → Empty t → Empty (ScanT f z t)
empty-scan f z em (sval x)  with acc-row x
... | _ , r = em r
empty-scan f z em (sstep r) = em r
empty-scan f z em (spin r)  = em r
empty-scan f z em (send r)  = em r

-- A VALUE LEADING ITS SOURCE: the fold of it leads, the rest fold from it.
scan-plus-nx : ∀ {A B} (f : B → A → B) z (t : EmissionSet A) p a → After p t
             → ScanT f z (Plus t p (out a)) ≃ Plus (ScanT f (f z a) t) p (out (f z a))
scan-plus-nx f z t p a af = to′ ⇄ from′
  where
    P  = Plus t p (out a)
    z′ = f z a

    down : ∀ {q b} → Acc f z P q b → Plus (ScanT f z′ t) p (out z′) q (out b)
    down (acc₀ new _)        = new
    down (acc₀ (old r) l)    = ⊥-elim (l new (af r))
    down (acc x new qp _)    with acc-row x
    ... | _ , r = ⊥-elim (plus-at af r qp)
    down (acc x (old r) qq nt) with down x
    ... | new          = old (sval (acc₀ r (λ r′ → nt (old r′) (af r′))))
    ... | old (sval y) = old (sval (acc y r qq (λ r′ → nt (old r′))))

    to′ : ∀ {q e} → ScanT f z P q e → Plus (ScanT f z′ t) p (out z′) q e
    to′ (sval x)        = down x
    to′ (sstep (old r)) = old (sstep r)
    to′ (spin (old r))  = old (spin r)
    to′ (send (old r))  = old (send r)

    up : ∀ {q b} → Acc f z′ t q b → Acc f z P q b
    up (acc₀ {q = q} r l) = acc (acc₀ new (plus-at af)) (old r) (af r) first
      where
        first : ∀ {k b} → P k (out b) → p ≺ k → q ≼ k
        first new      pk = ⊥-elim (≺-irrefl {p} pk)
        first (old r′) _  = l r′
    up (acc {q = q₀} {q′ = q′} x r qq nt) = acc (up x) (old r) qq nt′
      where
        nt′ : ∀ {k b} → P k (out b) → q₀ ≺ k → q′ ≼ k
        nt′ new      qk with acc-row x
        ... | _ , r′ = ⊥-elim (≺-absurd {p} {q₀} (af r′) qk)
        nt′ (old r′) qk = nt r′ qk

    from′ : ∀ {q e} → Plus (ScanT f z′ t) p (out z′) q e → ScanT f z P q e
    from′ new              = sval (acc₀ new (plus-at af))
    from′ (old (sval y))   = sval (up y)
    from′ (old (sstep r))  = sstep (old r)
    from′ (old (spin r))   = spin (old r)
    from′ (old (send r))   = send (old r)

-- AN END RISEN UNDER A SCAN: it folds no value, so every fold stands.
scan-plus-cp : ∀ {A B} (f : B → A → B) z (t : EmissionSet A) p → ScanT f z (Plus t p end) ≃ Plus (ScanT f z t) p end
scan-plus-cp f z t p = to′ ⇄ from′
  where
    P = Plus t p end

    down : ∀ {q b} → Acc f z P q b → Acc f z t q b
    down (acc₀ (old r) l)      = acc₀ r (λ r′ → l (old r′))
    down (acc x (old r) qq nt) = acc (down x) r qq (λ r′ → nt (old r′))

    up : ∀ {q b} → Acc f z t q b → Acc f z P q b
    up (acc₀ r l)      = acc₀ (old r) (λ { (old r′) → l r′ })
    up (acc x r qq nt) = acc (up x) (old r) qq (λ { (old r′) → nt r′ })

    to′ : ∀ {q e} → ScanT f z P q e → Plus (ScanT f z t) p end q e
    to′ (sval x)        = old (sval (down x))
    to′ (sstep (old r)) = old (sstep r)
    to′ (spin (old r))  = old (spin r)
    to′ (send (old r))  = old (send r)
    to′ (send new)      = new

    from′ : ∀ {q e} → Plus (ScanT f z t) p end q e → ScanT f z P q e
    from′ new             = send new
    from′ (old (sval y))  = sval (up y)
    from′ (old (sstep r)) = sstep (old r)
    from′ (old (spin r))  = spin (old r)
    from′ (old (send r))  = send (old r)

rise-scan-nx : ∀ {R Γ A B} (f : B → A → B) z (c : Ctx R Γ B) s a p → Sim ⟨ inScan f z c , s , rising (nx a) , p ⟩ [] ⟨ c , scanS f (f z a) s , rising (nx (f z a)) , p ⟩
rise-scan-nx f z c s a p i with alive s in al
rise-scan-nx f z c s a p (inv g (_ , _ , op , _)) | false = ⊥-elim (open-alive s op al)
rise-scan-nx f z c s a p (inv (an , g) (uc , lc , _ , af , _)) | true =
  inv (an′ , node-f c (scanS f (f z a) s) an′ (tr s (anc-liv c an) g)) (uc , lc , tt , after-scan f (f z a) {p = p} af , tt)
  , silent (vis-≃ (up-≃ c eq))
  where
    eq  = scan-plus-nx f z (rows (env c) s) p a af
    an′ = anc-≃ c (scanS f (f z a) s) eq (anc-swap c (record { ln = λ () ; cut = λ () ; held = λ () ; live≡ = refl ; told = λ _ t → t }) an)

rise-scan-cp : ∀ {R Γ A B} (f : B → A → B) z (c : Ctx R Γ B) s p → Sim ⟨ inScan f z c , s , rising cp , p ⟩ [] ⟨ c , scanS f z s , rising cp , p ⟩
rise-scan-cp f z c s p i with alive s in al
rise-scan-cp f z c s p (inv g (_ , _ , op , _)) | false = ⊥-elim (open-alive s op al)
rise-scan-cp f z c s p (inv (an , g) (uc , lc , _ , af , en)) | true =
  inv (an′ , node-f c (scanS f z s) an′ (tr s (anc-liv c an) g)) (uc , lc , tt , after-scan f z {p = p} af , empty-scan f z en)
  , silent (vis-≃ (up-≃ c eq))
  where
    eq  = scan-plus-cp f z (rows (env c) s) p
    an′ = anc-≃ c (scanS f z s) eq an
