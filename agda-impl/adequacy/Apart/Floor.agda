{-# OPTIONS --guardedness #-}

-- THE FLOOR: mid-run at `p`, no mark is keyed before `p`'s whole subtree
-- is past.  Every conf a run reaches keeps its regions apart, the run's
-- own among them; every key is in a region, so every key is clear of the
-- run's.
module adequacy.Apart.Floor where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_; [_])
open import Data.List.Relation.Unary.All using ([]; lookup)
open import Data.Maybe using (just; nothing)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import operation.PureObservable using (PureObs; module Machine; module Driver)
open Machine using (Ctx; St; Mode; ⟨_,_,_,_⟩; plug; load; subscribing; absorbed; rising; search; top; found; ofS; cutS; takeS; joinS; connS; coldS)
open import operation.Key using (at; after; _<ᴷ_)
open import adequacy.Least using (Lo)
open import adequacy.Stamped using (StOK; NotPend; stamped; plug-ok; unplug; pend-focus)
open import adequacy.Path using (Path; []; tau; val; _▸_)
open import adequacy.Dispatch using (Marked; ofK; attK; conK; joinK; leafK; stopK; cutK; found-least; found-mark; found-plug)
open import adequacy.Apart.Region using (cn; tl; pt; bk; cl)
open import adequacy.Apart.Items using (items; Covers; cover; keyed)
open import adequacy.Apart.Kit using (W; Apart; Next)
open import adequacy.Apart.Rise using (rise-ap)
open import adequacy.Apart.Begin using (begin-ap)
open import adequacy.Apart.Run using (run-ap)

private
  marked-np : ∀ {Γ A} {s : St Γ A} {m} → Marked s m → NotPend s
  marked-np (ofK _ _ _)           = tt
  marked-np (attK _ _ _)          = tt
  marked-np (conK _ _ _ _ _)      = tt
  marked-np (joinK _ _ _ _ _ _)   = tt
  marked-np (leafK _ _)           = tt
  marked-np (stopK _ _ _ _)       = tt
  marked-np (cutK _ _ _ _)        = tt

module _ {R : Set} where
  open Driver R using (step)

  -- A STEP KEEPS APART.
  apart-step : ∀ (o : PureObs [] R) {rs k} → Path (load o) rs k → Apart k → Next (step k)
  apart-step o {k = ⟨ c , s , rising e , p ⟩} pth a with stamped o pth
  ... | _ , _ , hp , _ = rise-ap c s e p hp a
  apart-step o {k = ⟨ c , s , subscribing , p ⟩} pth a with stamped o pth | pend-focus o pth
  ... | _ , _ , hp , _ | o′ , refl = begin-ap c o′ p hp a
  apart-step o {k = ⟨ c , s , absorbed , p ⟩} pth a with stamped o pth | search top (plug c s) in fd
  ... | _ | nothing = tt
  ... | hc , hs , _ | just (found (_ , _ , c′ , s′) m κ) with found-least {t = plug c s} fd | found-plug c s fd | found-mark c s fd
  ...   | mi , lo | pe | mk =
    run-ap c′ p mk mi (proj₂ (unplug c′ (marked-np mk) ok′))
      (keyed (plug c′ s′) ok′ (subst (λ t → Lo t κ) (sym pe) lo)) (subst (λ t → W top t []) (sym pe) a)
    where
      ok′ = subst StOK (sym pe) (plug-ok c hc hs)

  apart-path : ∀ (o : PureObs [] R) {rs rs′ k k″} → Path (load o) rs k → Apart k → Path k rs′ k″ → Apart k″
  apart-path o pre a []          = a
  apart-path o pre a (tau e pth) = apart-path o (pre ▸ tau e []) (subst Next e (apart-step o pre a)) pth
  apart-path o pre a (val e pth) = apart-path o (pre ▸ val e []) (subst Next e (apart-step o pre a)) pth

-- Every key past a region clear of the run.
lo-of : ∀ {R Γ A} (c : Ctx R Γ A) s p → W c s [ cl p ] → Lo (plug c s) (after p)
lo-of c s p (hd ∷ _) {κ} hk = past κ (cover (plug c s) hk)
  where
    past : ∀ κ → Covers (items (plug c s)) κ → κ <ᴷ after p ≡ false
    past (at y)    (cn r , m , iy)   = proj₁ (proj₂ (lookup hd m) y iy)
    past (at y)    (tl u i , m , iy) = proj₁ (proj₂ (lookup hd m) y iy)
    past (at y)    (pt _ , _ , ())
    past (at y)    (bk _ , _ , ())
    past (at y)    (cl _ , _ , ())
    past (after y) m                 = proj₁ (proj₂ (lookup hd m))

-- Mid-run.
Busy : ∀ {A} → Mode A → Set
Busy absorbed    = ⊥
Busy subscribing = ⊤
Busy (rising _)  = ⊤

-- THE FLOOR, everywhere a run reaches.
floor : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s m p}
      → Path (load o) rs ⟨ c , s , m , p ⟩ → Busy m → Lo (plug c s) (after p)
floor o {c = c} {s} {subscribing} {p} pth _ = lo-of c s p (apart-path o [] ([] ∷ []) pth)
floor o {c = c} {s} {rising _}    {p} pth _ = lo-of c s p (apart-path o [] ([] ∷ []) pth)
floor o {m = absorbed} pth ()
