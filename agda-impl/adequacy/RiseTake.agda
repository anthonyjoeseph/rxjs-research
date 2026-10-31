------------------------------------------------------------------------
-- A TAKE'S RISE.  A passing value is the least of its source's rows, so
-- nothing fails before it and it leads the taken rows; an end rises
-- through a take whose source owes nothing more.
------------------------------------------------------------------------

module adequacy.RiseTake where

open import Data.Bool using (Bool; true; false; not; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; [_]; _++_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import denotation.EmissionSet using (EmissionSet; out; end; module TakeWhile; Truncate)
open import denotation.Events using (ix; last)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≺→≼; ≺-trans; ≺-ext)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; ⟨_,_,_,_⟩; rising; absorbed; alive; nx; cp; free; cpAt; cutAt; overAt; Owe; takeS; inTake) renaming (Ev to Evᴹ)
open import adequacy.Rows using (env; rows; toEv; TakeR; Kept; kept; Stops; Plus; old; new; _≃_; _⇄_; silent)
  renaming (stop to stopᴿ; left to leftᴿ)
open import adequacy.Bound using (Empty)
open import adequacy.Up using (up-≃; vis-≃; trunc-≃; ≃-trans)
open import adequacy.Skip using (After; since-takeT)
open import adequacy.Inv using (Sim; inv; open-alive; anc-liv; node-f; tr; anc-join)
open import adequacy.Above using (anc-≃)
open import adequacy.LaneCp using (trunc-plus)

open TakeWhile using (TakeT; Failed; pass; fail; stop; step; tend; left)

-- A failing value's mark, read off one known to keep.
kept-not : ∀ {A : Set} (w : A → Bool) {a} → w a ≡ true → T (not (w a)) → ⊥
kept-not w wa nk = subst (λ b → T (not b)) wa nk

-- A VALUE THAT PASSES: it leads the taken rows, failing nothing.
take-plus-nx : ∀ {A} i (w : A → Bool) (t : EmissionSet A) p a → w a ≡ true → After p t
             → TakeT i w (Plus t p (out a)) ≃ Plus (TakeT i w t) p (out a)
take-plus-nx i w t p a wa af = to′ ⇄ from′
  where
    P = Plus t p (out a)

    raise : ∀ {k} → Failed i w t k → Failed i w P k
    raise (k′ , a′ , y , nk , lt) = k′ , a′ , old y , nk , lt

    lower : ∀ {k} → Failed i w P k → Failed i w t k
    lower (k′ , a′ , old y , nk , lt) = k′ , a′ , y , nk , lt
    lower (_  , _  , new   , nk , _)  = ⊥-elim (kept-not w wa nk)

    to′ : ∀ {q e} → TakeT i w P q e → Plus (TakeT i w t) p (out a) q e
    to′ (pass new _ _)         = new
    to′ (pass (old r) kp nf)   = old (pass r kp (λ x → nf (raise x)))
    to′ (fail new nk _ _)      = ⊥-elim (kept-not w wa nk)
    to′ (fail (old r) nk nf ic) = old (fail r nk (λ x → nf (raise x)) ic)
    to′ (stop new nk _)        = ⊥-elim (kept-not w wa nk)
    to′ (stop (old r) nk nf)   = old (stop r nk (λ x → nf (raise x)))
    to′ (step (old r) nf)      = old (step r (λ x → nf (raise x)))
    to′ (tend (old r) nf)      = old (tend r (λ x → nf (raise x)))
    to′ (left (old r) nf ins)  = old (left r (λ x → nf (raise x)) ins)

    from′ : ∀ {q e} → Plus (TakeT i w t) p (out a) q e → TakeT i w P q e
    from′ new                     = pass new (subst T (sym wa) tt) none
      where
        none : Failed i w P p → ⊥
        none (_ , _ , new   , _ , lt) = ≺-irrefl {p} lt
        none (k′ , _ , old y , _ , lt) = ≺-absurd {p} {k′} (af y) lt
    from′ (old (pass r kp nf))     = pass (old r) kp (λ x → nf (lower x))
    from′ (old (fail r nk nf ic))  = fail (old r) nk (λ x → nf (lower x)) ic
    from′ (old (stop r nk nf))     = stop (old r) nk (λ x → nf (lower x))
    from′ (old (step r nf))        = step (old r) (λ x → nf (lower x))
    from′ (old (tend r nf))        = tend (old r) (λ x → nf (lower x))
    from′ (old (left r nf ins))    = left (old r) (λ x → nf (lower x)) ins

-- AN END UNDER A TAKE WHOSE SOURCE OWES NOTHING: the end alone.
take-plus-cp : ∀ {A} i (w : A → Bool) (t : EmissionSet A) p → Empty t → TakeT i w (Plus t p end) ≃ Plus (TakeT i w t) p end
take-plus-cp i w t p em = to′ ⇄ from′
  where
    P = Plus t p end

    to′ : ∀ {q e} → TakeT i w P q e → Plus (TakeT i w t) p end q e
    to′ (tend new _)          = new
    to′ (pass (old r) _ _)    = ⊥-elim (em r)
    to′ (fail (old r) _ _ _)  = ⊥-elim (em r)
    to′ (stop (old r) _ _)    = ⊥-elim (em r)
    to′ (step (old r) _)      = ⊥-elim (em r)
    to′ (tend (old r) _)      = ⊥-elim (em r)
    to′ (left (old r) _ _)    = ⊥-elim (em r)

    from′ : ∀ {q e} → Plus (TakeT i w t) p end q e → TakeT i w P q e
    from′ new = tend new λ { (_ , _ , old y , _ , _) → em y }
    from′ (old (pass r _ _))   = ⊥-elim (em r)
    from′ (old (fail r _ _ _)) = ⊥-elim (em r)
    from′ (old (stop r _ _))   = ⊥-elim (em r)
    from′ (old (step r _))     = ⊥-elim (em r)
    from′ (old (tend r _))     = ⊥-elim (em r)
    from′ (old (left r _ _))   = ⊥-elim (em r)

after-takeT : ∀ {A} i (w : A → Bool) {t : EmissionSet A} {p} → After p t → After p (Truncate (TakeT i w t))
after-takeT i w {p = p} af (pass x _ _ , _)           = af x
after-takeT i w {p = p} af (fail {k} x _ _ _ , _)     = ≺-trans {p} {k} {k ++ [ ix 0 ]} (af x) (≺-ext k [])
after-takeT i w {p = p} af (stop {k} x _ _ , _)       = ≺-trans {p} {k} {k ++ [ last ]} (af x) (≺-ext k [])
after-takeT i w {p = p} af (step x _ , _)             = af x
after-takeT i w {p = p} af (tend x _ , _)             = af x
after-takeT i w {p = p} af (left x _ _ , _)           = af x

empty-takeT : ∀ {A} i (w : A → Bool) {t : EmissionSet A} → Empty t → Empty (TakeT i w t)
empty-takeT i w em (pass x _ _)   = em x
empty-takeT i w em (fail x _ _ _) = em x
empty-takeT i w em (stop x _ _)   = em x
empty-takeT i w em (step x _)     = em x
empty-takeT i w em (tend x _)     = em x
empty-takeT i w em (left x _ _)   = em x

rise-take-nx : ∀ {R Γ A} i (w : A → Bool) (c : Ctx R Γ A) s a p → w a ≡ true
             → Sim ⟨ inTake i w free c , s , rising (nx a) , p ⟩ [] ⟨ c , takeS i w free s , rising (nx a) , p ⟩
rise-take-nx i w c s a p wa x with alive s in al
rise-take-nx i w c s a p wa (inv g (_ , _ , op , _)) | false = ⊥-elim (open-alive s op al)
rise-take-nx i w c s a p wa (inv (an , g) (uc , (_ , lc) , _ , af , _)) | true =
  inv (an′ , node-f c (takeS i w free s) an′ (tr s (anc-liv c an) g)) (uc , lc , tt , after-takeT i w {p = p} af , tt)
  , silent (vis-≃ (up-≃ c eq))
  where
    t   = rows (env c) s
    eq  = ≃-trans (trunc-≃ (take-plus-nx i w t p a wa af)) (trunc-plus (since-takeT i w {p = p} (λ r → ≺→≼ {p} (af r))))
    an′ = anc-≃ c (takeS i w free s) eq an

rise-take-cp : ∀ {R Γ A} i (w : A → Bool) (c : Ctx R Γ A) s p
             → Sim ⟨ inTake i w free c , s , rising cp , p ⟩ [] ⟨ c , takeS i w free s , rising cp , p ⟩
rise-take-cp i w c s p x with alive s in al
rise-take-cp i w c s p (inv g (_ , _ , op , _)) | false = ⊥-elim (open-alive s op al)
rise-take-cp i w c s p (inv (an , g) (uc , (_ , lc) , _ , af , en)) | true =
  inv (an′ , node-f c (takeS i w free s) an′ (tr s (anc-liv c an) g)) (uc , lc , tt , after-takeT i w {p = p} af , (λ (r , _) → empty-takeT i w en r))
  , silent (vis-≃ (up-≃ c eq))
  where
    t   = rows (env c) s
    eq  = ≃-trans (trunc-≃ (take-plus-cp i w t p en)) (trunc-plus (λ r → ⊥-elim (empty-takeT i w en r)))
    an′ = anc-≃ c (takeS i w free s) eq an

-- A TAKE ALREADY OWING ITS STOP keeps only pins and that stop, so a value
-- or an end risen into it reaches nothing.
kept-plus : ∀ {A} r (t : EmissionSet A) p (e : Evᴹ A) → Kept r (Plus t p (toEv e)) ≃ Kept r t
kept-plus r t p (nx a) = (λ { (kept (old x) np ins) → kept x np ins }) ⇄ (λ { (kept x np ins) → kept (old x) np ins })
kept-plus r t p cp     = (λ { (kept (old x) np ins) → kept x np ins }) ⇄ (λ { (kept x np ins) → kept (old x) np ins })

stops-plus : ∀ {A} r (t : EmissionSet A) p (e : Evᴹ A) → Stops r (Plus t p (toEv e)) ≃ Stops r t
stops-plus r t p e = (λ { stopᴿ → stopᴿ ; (leftᴿ x) → leftᴿ (_≃_.to (kept-plus r t p e) x) })
                   ⇄ (λ { stopᴿ → stopᴿ ; (leftᴿ x) → leftᴿ (_≃_.from (kept-plus r t p e) x) })

owed-plus : ∀ {A} i (w : A → Bool) o (t : EmissionSet A) p (e : Evᴹ A) → (o ≡ free → ⊥) → TakeR i w o (Plus t p (toEv e)) ≃ TakeR i w o t
owed-plus i w free       t p e nf = ⊥-elim (nf refl)
owed-plus i w (cpAt r)   t p e nf = stops-plus r t p e
owed-plus i w (cutAt r)  t p e nf = kept-plus r t p e
owed-plus i w (overAt r) t p e nf = kept-plus r t p e

rise-take-owed : ∀ {R Γ A} i (w : A → Bool) o (c : Ctx R Γ A) s e p → (o ≡ free → ⊥)
               → Sim ⟨ inTake i w o c , s , rising e , p ⟩ [] ⟨ c , takeS i w o s , absorbed , p ⟩
rise-take-owed i w o c s e p nf x with alive s in al
rise-take-owed i w o c s e p nf (inv g (_ , _ , op , _)) | false = ⊥-elim (open-alive s op al)
rise-take-owed i w o c s e p nf (inv (an , g) _) | true =
  inv (anc-join (inTake i w o c) s (anc-≃ c (takeS i w o s) eq an) g) tt
  , silent (vis-≃ (up-≃ c eq))
  where eq = owed-plus i w o (rows (env c) s) p e nf
