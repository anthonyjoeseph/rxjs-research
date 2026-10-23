{-# OPTIONS --guardedness #-}

-- PLUGGED: a node of the witness read through the machine's context.  A
-- path from the root rebuilds the context the machine holds at its node,
-- and a context is the only one with its directions plugging its tree:
-- `downs` finds the focus again from the root.
module adequacy.Plugged where

open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ; length-++; ∷-injectiveʳ)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import denotation.MonotonicList.Events using (Pos)

open import operation.PureObservable using (module Machine; module Driver)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Ghost.Paths using (module GhostingPaths)

open Machine using (St; Ctx; Focus; plug; dirs; down; downs; pickL; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody;
                    mapS; scanS; cutS; lnS; takeS; flatS; connS; ofS; ⟨_,_,_,_,_⟩; resuming; next)

------------------------------------------------------------------------
-- The machine finds a plugged focus by its directions

private
  pickL-at : ∀ {Γ B} (acc pre : List (St Γ B)) s post → pickL (length pre) acc (pre ++ s ∷ post) ≡ just (acc ++ pre , s , post)
  pickL-at acc []        s post = cong (λ a → just (a , s , post)) (sym (++-identityʳ acc))
  pickL-at acc (p ∷ pre) s post = trans (pickL-at (acc ++ [ p ]) pre s post) (cong (λ a → just (a , s , post)) (++-assoc acc [ p ] pre))

  down-pick : ∀ {R Γ A B} op f d n q (o : St Γ A) (c : Ctx R Γ B) i ls {pre s post}
            → pickL i [] ls ≡ just (pre , s , post)
            → down (suc i) c (flatS op f d n q o ls) ≡ just (_ , _ , inLanes op f d n q o pre post c , s)
  down-pick op f d n q o c zero    ls e rewrite e = refl
  down-pick op f d n q o c (suc i) ls e rewrite e = refl

  downs-cons : ∀ {R Γ A Γ′ A′} {i p} {c : Ctx R Γ A} {s} {c′ : Ctx R Γ′ A′} {s′}
             → down i c s ≡ just (Γ′ , A′ , c′ , s′) → downs (i ∷ p) c s ≡ downs p c′ s′
  downs-cons e rewrite e = refl

  downs-++ : ∀ {R Γ A Γ′ A′} p q {c : Ctx R Γ A} {s} {c′ : Ctx R Γ′ A′} {s′}
           → downs p c s ≡ just (Γ′ , A′ , c′ , s′) → downs (p ++ q) c s ≡ downs q c′ s′
  downs-++ []      q refl = refl
  downs-++ (i ∷ p) q {c = c} {s} with down i c s
  ... | just (_ , _ , c₁ , s₁) = downs-++ p q
  ... | nothing                = λ ()

  downs-plug : ∀ {R Γ A} (c : Ctx R Γ A) x → downs (dirs c) top (plug c x) ≡ just (_ , _ , c , x)
  downs-plug top                               x = refl
  downs-plug (inMap f c)                       x = downs-++ (dirs c) [ 0 ] (downs-plug c (mapS f x))
  downs-plug (inScan f z c)                    x = downs-++ (dirs c) [ 0 ] (downs-plug c (scanS f z x))
  downs-plug (inCut l a c)                     x = downs-++ (dirs c) [ 0 ] (downs-plug c (cutS l a x))
  downs-plug (inLn b c)                        x = downs-++ (dirs c) [ 0 ] (downs-plug c (lnS b x))
  downs-plug (inTake i p c)                    x = downs-++ (dirs c) [ 0 ] (downs-plug c (takeS i p x))
  downs-plug (inOuter op f d n q ls c)         x = downs-++ (dirs c) [ 0 ] (downs-plug c (flatS op f d n q x ls))
  downs-plug (inLanes op f d n q o pre post c) x =
    trans (downs-++ (dirs c) _ (downs-plug c (flatS op f d n q o (pre ++ x ∷ post))))
          (downs-cons {i = suc (length pre)} {p = []} (down-pick op f d n q o c (length pre) (pre ++ x ∷ post) (pickL-at [] pre x post)))
  downs-plug (inSrc k b c)                     x = downs-++ (dirs c) [ 0 ] (downs-plug c (connS k x b))
  downs-plug (inBody k o c)                    x = downs-++ (dirs c) [ 1 ] (downs-plug c (connS k o x))

  -- Two contexts with one direction list plugging one tree are one focus.
  focus-unique : ∀ {R Γ A Γ′ A′} (c : Ctx R Γ A) (c′ : Ctx R Γ′ A′) x x′ → dirs c ≡ dirs c′ → plug c x ≡ plug c′ x′
               → _≡_ {A = Focus R} (Γ , A , c , x) (Γ′ , A′ , c′ , x′)
  focus-unique c c′ x x′ d e =
    just-injective (trans (sym (downs-plug c x)) (trans (cong₂ (λ p s → downs p top s) d e) (downs-plug c′ x′)))

  focus-eq : ∀ {R Γ A} {c c′ : Ctx R Γ A} {x x′} → _≡_ {A = Focus R} (Γ , A , c , x) (Γ , A , c′ , x′) → c ≡ c′ × x ≡ x′
  focus-eq refl = refl , refl

module Plugging (R : Set) where
  open Strongly R using (Sub; Path; PathLanes; here; in-map; in-scan; in-cut; in-lane; in-take; in-outer; in-lanes; in-source; in-body;
                         this-lane; next-lane; forget; forgetᴸ; pendingˢ; coldˢ; ofˢ; doneˢ; mapˢ; scanˢ; cutˢ; laneˢ; takeWhileˢ;
                         flatMapˢ; connectˢ; joinˢ; Carried; Kernels)
  open Driver R using (Mach)
  open Moving R using (plant; plantᴸ)
  open GhostingPaths R using (_⊕_; _⊕ᴸ_)

  ----------------------------------------------------------------------
  -- The context a path rebuilds, from the context of its root

  mutual
    ctxAt : ∀ {Γ A Δ B π} {t : Sub Γ A} {u : Sub Δ B} → Ctx R Γ A → Path t u π → Ctx R Δ B
    ctxAt c here                                                          = c
    ctxAt c (in-map {f = f} ψ)                                            = ctxAt (inMap f c) ψ
    ctxAt c (in-scan {f = f} {z = z} ψ)                                   = ctxAt (inScan f z c) ψ
    ctxAt c (in-cut {l = l} {a = a} ψ)                                    = ctxAt (inCut l a c) ψ
    ctxAt c (in-lane {r = r} ψ)                                           = ctxAt (inLn r c) ψ
    ctxAt c (in-take {i = i} {q = q} ψ)                                   = ctxAt (inTake i q c) ψ
    ctxAt c (in-outer {op = op} {f = f} {d = d} {n = n} {qs = qs} {ls = ls} ψ) = ctxAt (inOuter op f d n qs (forgetᴸ ls) c) ψ
    ctxAt c (in-lanes {op = op} {f = f} {d = d} {n = n} {qs = qs} {o = o} ψ)   = ctxAtᴸ (λ pre post → inLanes op f d n qs (forget o) pre post c) [] ψ
    ctxAt c (in-source {k = k} {b = b} ψ)                                 = ctxAt (inSrc k (forget b) c) ψ
    ctxAt c (in-body {k = k} {s = s} ψ)                                   = ctxAt (inBody k (forget s) c) ψ

    -- The lanes before the path's, forgotten, carried as `pre`.
    ctxAtᴸ : ∀ {Γ B Δ C i π} {ls : List (Sub Γ B)} {u : Sub Δ C}
           → (List (St Γ B) → List (St Γ B) → Ctx R Γ B) → List (St Γ B) → PathLanes ls u i π → Ctx R Δ C
    ctxAtᴸ F pre (this-lane {ls = ls} ψ) = ctxAt (F pre (forgetᴸ ls)) ψ
    ctxAtᴸ F pre (next-lane {l = l} ψ)   = ctxAtᴸ F (pre ++ [ forget l ]) ψ

  -- Its directions are the path's.
  mutual
    dirs-at : ∀ {Γ A Δ B π} {t : Sub Γ A} {u : Sub Δ B} (c : Ctx R Γ A) (ψ : Path t u π) → dirs (ctxAt c ψ) ≡ dirs c ++ π
    dirs-at c here            = sym (++-identityʳ (dirs c))
    dirs-at c (in-map ψ)      = trans (dirs-at _ ψ) (++-assoc (dirs c) [ 0 ] _)
    dirs-at c (in-scan ψ)     = trans (dirs-at _ ψ) (++-assoc (dirs c) [ 0 ] _)
    dirs-at c (in-cut ψ)      = trans (dirs-at _ ψ) (++-assoc (dirs c) [ 0 ] _)
    dirs-at c (in-lane ψ)     = trans (dirs-at _ ψ) (++-assoc (dirs c) [ 0 ] _)
    dirs-at c (in-take ψ)     = trans (dirs-at _ ψ) (++-assoc (dirs c) [ 0 ] _)
    dirs-at c (in-outer ψ)    = trans (dirs-at _ ψ) (++-assoc (dirs c) [ 0 ] _)
    dirs-at c (in-lanes ψ)    = dirs-atᴸ c _ (λ _ _ → refl) [] ψ
    dirs-at c (in-source ψ)   = trans (dirs-at _ ψ) (++-assoc (dirs c) [ 0 ] _)
    dirs-at c (in-body ψ)     = trans (dirs-at _ ψ) (++-assoc (dirs c) [ 1 ] _)

    dirs-atᴸ : ∀ {Γ′ A′ Γ B Δ C i π} {ls : List (Sub Γ B)} {u : Sub Δ C} (c : Ctx R Γ′ A′) (F : List (St Γ B) → List (St Γ B) → Ctx R Γ B)
             → (∀ pre post → dirs (F pre post) ≡ dirs c ++ [ suc (length pre) ]) → ∀ pre (ψ : PathLanes ls u i π)
             → dirs (ctxAtᴸ F pre ψ) ≡ dirs c ++ suc (length pre + i) ∷ π
    dirs-atᴸ c F hd pre (this-lane {ls = ls} {π = π} ψ) =
      trans (dirs-at _ ψ) (trans (cong (_++ π) (hd pre (forgetᴸ ls)))
            (trans (++-assoc (dirs c) _ π) (cong (λ k → dirs c ++ suc k ∷ π) (sym (+-identityʳ (length pre))))))
    dirs-atᴸ c F hd pre (next-lane {l = l} {i = i} {π = π} ψ) =
      trans (dirs-atᴸ c F hd (pre ++ [ forget l ]) ψ)
            (cong (λ k → dirs c ++ suc k ∷ π) (trans (cong (_+ i) (length-++ pre)) (+-assoc (length pre) 1 i)))

  -- Planting under the path is plugging the rebuilt context.
  mutual
    plant-plug : ∀ {Γ A Δ B π} {t : Sub Γ A} {u : Sub Δ B} (c : Ctx R Γ A) (ψ : Path t u π) w
               → plug c (forget (plant ψ w)) ≡ plug (ctxAt c ψ) (forget w)
    plant-plug c here w          = refl
    plant-plug c (in-map ψ) w    = plant-plug _ ψ w
    plant-plug c (in-scan ψ) w   = plant-plug _ ψ w
    plant-plug c (in-cut ψ) w    = plant-plug _ ψ w
    plant-plug c (in-lane ψ) w   = plant-plug _ ψ w
    plant-plug c (in-take ψ) w   = plant-plug _ ψ w
    plant-plug c (in-outer ψ) w  = plant-plug _ ψ w
    plant-plug c (in-lanes {op = op} {f = f} {d = d} {n = n} {qs = qs} {o = o} ψ) w =
      plant-plugᴸ (λ ls → plug c (flatS op f d n qs (forget o) ls)) _ (λ _ _ _ → refl) [] ψ w
    plant-plug c (in-source ψ) w = plant-plug _ ψ w
    plant-plug c (in-body ψ) w   = plant-plug _ ψ w

    plant-plugᴸ : ∀ {Γ B Δ C i π} {ls : List (Sub Γ B)} {u : Sub Δ C} (G : List (St Γ B) → St [] R) (F : List (St Γ B) → List (St Γ B) → Ctx R Γ B)
                → (∀ pre post s → plug (F pre post) s ≡ G (pre ++ s ∷ post)) → ∀ pre (ψ : PathLanes ls u i π) w
                → G (pre ++ forgetᴸ (plantᴸ ψ w)) ≡ plug (ctxAtᴸ F pre ψ) (forget w)
    plant-plugᴸ G F hp pre (this-lane {ls = ls} ψ) w = trans (sym (hp pre (forgetᴸ ls) _)) (plant-plug _ ψ w)
    plant-plugᴸ G F hp pre (next-lane {l = l} ψ) w =
      trans (cong G (sym (++-assoc pre [ forget l ] _))) (plant-plugᴸ G F hp (pre ++ [ forget l ]) ψ w)

  -- Planting a node's own self changes nothing.
  mutual
    plant-self : ∀ {Γ A Δ B π} {t : Sub Γ A} {u : Sub Δ B} (ψ : Path t u π) → plant ψ u ≡ t
    plant-self here = refl
    plant-self (in-map {f = f} ψ) = cong (mapˢ f) (plant-self ψ)
    plant-self (in-scan {f = f} {z = z} ψ) = cong (scanˢ f z) (plant-self ψ)
    plant-self (in-cut {l = l} {a = a} ψ) = cong (cutˢ l a) (plant-self ψ)
    plant-self (in-lane {r = r} ψ) = cong (laneˢ r) (plant-self ψ)
    plant-self (in-take {i = i} {q = q} {tk = tk} ψ) = cong (takeWhileˢ i q tk) (plant-self ψ)
    plant-self (in-outer {op = op} {f = f} {d = d} {n = n} {qs = qs} {pl = pl} {ls = ls} ψ) =
      cong (λ o → flatMapˢ op f d n qs pl o ls) (plant-self ψ)
    plant-self (in-lanes {op = op} {f = f} {d = d} {n = n} {qs = qs} {pl = pl} {o = o} ψ) =
      cong (flatMapˢ op f d n qs pl o) (plant-selfᴸ ψ)
    plant-self (in-source {k = k} {r = r} {e = e} {rt = rt} {b = b} ψ) = cong (λ s → connectˢ k r e rt s b) (plant-self ψ)
    plant-self (in-body {k = k} {r = r} {e = e} {rt = rt} {s = s} ψ) = cong (connectˢ k r e rt s) (plant-self ψ)

    plant-selfᴸ : ∀ {Γ A Δ B i π} {ls : List (Sub Γ A)} {u : Sub Δ B} (ψ : PathLanes ls u i π) → plantᴸ ψ u ≡ ls
    plant-selfᴸ (this-lane {ls = ls} ψ) = cong (_∷ ls) (plant-self ψ)
    plant-selfᴸ (next-lane {l = l} ψ) = cong (l ∷_) (plant-selfᴸ ψ)

  -- Rebuilding along two paths is rebuilding along their join.
  mutual
    ctx-⊕ : ∀ {Γ A Δ B Ε C π τ} {t : Sub Γ A} {u : Sub Δ B} {v : Sub Ε C} (c : Ctx R Γ A) (ψ : Path t u π) (σ : Path u v τ)
          → ctxAt c (ψ ⊕ σ) ≡ ctxAt (ctxAt c ψ) σ
    ctx-⊕ c here σ          = refl
    ctx-⊕ c (in-map ψ) σ    = ctx-⊕ _ ψ σ
    ctx-⊕ c (in-scan ψ) σ   = ctx-⊕ _ ψ σ
    ctx-⊕ c (in-cut ψ) σ    = ctx-⊕ _ ψ σ
    ctx-⊕ c (in-lane ψ) σ   = ctx-⊕ _ ψ σ
    ctx-⊕ c (in-take ψ) σ   = ctx-⊕ _ ψ σ
    ctx-⊕ c (in-outer ψ) σ  = ctx-⊕ _ ψ σ
    ctx-⊕ c (in-lanes ψ) σ  = ctx-⊕ᴸ _ [] ψ σ
    ctx-⊕ c (in-source ψ) σ = ctx-⊕ _ ψ σ
    ctx-⊕ c (in-body ψ) σ   = ctx-⊕ _ ψ σ

    ctx-⊕ᴸ : ∀ {Γ B Δ C Ε D i π τ} {ls : List (Sub Γ B)} {u : Sub Δ C} {v : Sub Ε D}
             (F : List (St Γ B) → List (St Γ B) → Ctx R Γ B) pre (ψ : PathLanes ls u i π) (σ : Path u v τ)
           → ctxAtᴸ F pre (ψ ⊕ᴸ σ) ≡ ctxAt (ctxAtᴸ F pre ψ) σ
    ctx-⊕ᴸ F pre (this-lane ψ) σ = ctx-⊕ _ ψ σ
    ctx-⊕ᴸ F pre (next-lane ψ) σ = ctx-⊕ᴸ F _ ψ σ

  ----------------------------------------------------------------------
  -- The machine's context at a path is the rebuilt one

  -- A context with a path's directions plugging the witness's tree is
  -- the path's, its focus the node's.
  at-path : ∀ {Δ B π} {T : Sub [] R} {u : Sub Δ B} (ψ : Path T u π) {c : Ctx R Δ B} {x}
          → dirs c ≡ π → forget T ≡ plug c x → c ≡ ctxAt top ψ × x ≡ forget u
  at-path {T = T} {u} ψ {c} {x} d e =
    focus-eq (focus-unique c (ctxAt top ψ) x (forget u) (trans d (sym (dirs-at top ψ)))
                           (trans (sym e) (trans (cong forget (sym (plant-self ψ))) (plant-plug top ψ u))))

  ----------------------------------------------------------------------
  -- The witness's node at the machine's context

  -- A node of the witness, by the head its machine tree shows.
  data Shape {Γ A} : Sub Γ A → St Γ A → Set₁ where
    sh-pending : ∀ {o q} → Shape (pendingˢ o q) (forget (pendingˢ o q))
    sh-cold    : ∀ {b ph} → Shape (coldˢ b ph) (forget (coldˢ b ph))
    sh-of      : ∀ {p i xs} → Shape (ofˢ p i xs) (forget (ofˢ p i xs))
    sh-done    : Shape doneˢ (forget doneˢ)
    sh-map     : ∀ {X} {f : X → A} {s : Sub Γ X} → Shape (mapˢ f s) (mapS f (forget s))
    sh-scan    : ∀ {X} {f : A → X → A} {z} {s : Sub Γ X} → Shape (scanˢ f z s) (scanS f z (forget s))
    sh-cut     : ∀ {l a} {s : Sub Γ A} → Shape (cutˢ l a s) (cutS l a (forget s))
    sh-lane    : ∀ {r} {s : Sub Γ A} → Shape (laneˢ r s) (lnS r (forget s))
    sh-take    : ∀ {i q tk} {s : Sub Γ A} → Shape (takeWhileˢ i q tk s) (takeS i q (forget s))
    sh-flat    : ∀ {X op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
               → Shape (flatMapˢ op f d n qs pl o ls) (flatS op f d n qs (forget o) (forgetᴸ ls))
    sh-conn    : ∀ {X k r e rt} {s : Sub Γ X} {b : Sub (X ∷ Γ) A} → Shape (connectˢ k r e rt s b) (connS k (forget s) (forget b))
    sh-join    : ∀ {j g x st} → Shape (joinˢ j g x st) (forget (joinˢ j g x st))

  shape : ∀ {Γ A} (u : Sub Γ A) → Shape u (forget u)
  shape (pendingˢ o q)                 = sh-pending
  shape (coldˢ b ph)                   = sh-cold
  shape (ofˢ p i xs)                   = sh-of
  shape doneˢ                          = sh-done
  shape (mapˢ f s)                     = sh-map
  shape (scanˢ f z s)                  = sh-scan
  shape (cutˢ l a s)                   = sh-cut
  shape (laneˢ r s)                    = sh-lane
  shape (takeWhileˢ i q tk s)          = sh-take
  shape (flatMapˢ op f d n qs pl o ls) = sh-flat
  shape (connectˢ k r e rt s b)        = sh-conn
  shape (joinˢ j g x st)               = sh-join

  private
    -- The lane a list of lanes holds after `pre`.
    lane-at : ∀ {Γ B} (ls : List (Sub Γ B)) pre x post → forgetᴸ ls ≡ pre ++ x ∷ post
            → Σ (Sub Γ B) λ v → PathLanes ls v (length pre) [] × forget v ≡ x
    lane-at []       []        x post ()
    lane-at (l ∷ ls) []        x post refl = l , this-lane here , refl
    lane-at []       (p ∷ pre) x post ()
    lane-at (l ∷ ls) (p ∷ pre) x post e with lane-at ls pre x post (∷-injectiveʳ e)
    ... | v , ψ , h = v , next-lane ψ , h

    lanes-at : ∀ {Γ X B π} {T : Sub [] R} {u : Sub Γ B} {op f d n q} {o : St Γ X} {L} → Shape u (flatS op f d n q o L)
             → ∀ pre x post → L ≡ pre ++ x ∷ post → Path T u π
             → Σ (Sub Γ B) λ v → Path T v (π ++ [ suc (length pre) ]) × forget v ≡ x
    lanes-at (sh-flat {ls = ls}) pre x post e ψ with lane-at ls pre x post e
    ... | v , ψ′ , h = v , ψ ⊕ in-lanes ψ′ , h

  -- The machine's context plugging the witness's tree reaches a node of
  -- it, the focus that node's.
  path-at : ∀ {Γ A} {T : Sub [] R} (c : Ctx R Γ A) x → forget T ≡ plug c x → Σ (Sub Γ A) λ u → Path T u (dirs c) × forget u ≡ x
  path-at top x e = _ , here , e
  path-at (inMap f c) x e with path-at c (mapS f x) e
  ... | u , ψ , h with subst (Shape u) h (shape u)
  ...   | sh-map {s = s} = s , ψ ⊕ in-map here , refl
  path-at (inScan f z c) x e with path-at c (scanS f z x) e
  ... | u , ψ , h with subst (Shape u) h (shape u)
  ...   | sh-scan {s = s} = s , ψ ⊕ in-scan here , refl
  path-at (inCut l a c) x e with path-at c (cutS l a x) e
  ... | u , ψ , h with subst (Shape u) h (shape u)
  ...   | sh-cut {s = s} = s , ψ ⊕ in-cut here , refl
  path-at (inLn b c) x e with path-at c (lnS b x) e
  ... | u , ψ , h with subst (Shape u) h (shape u)
  ...   | sh-lane {s = s} = s , ψ ⊕ in-lane here , refl
  path-at (inTake i p c) x e with path-at c (takeS i p x) e
  ... | u , ψ , h with subst (Shape u) h (shape u)
  ...   | sh-take {s = s} = s , ψ ⊕ in-take here , refl
  path-at (inOuter op f d n q ls c) x e with path-at c (flatS op f d n q x ls) e
  ... | u , ψ , h with subst (Shape u) h (shape u)
  ...   | sh-flat {o = o} = o , ψ ⊕ in-outer here , refl
  path-at (inLanes op f d n q o pre post c) x e with path-at c (flatS op f d n q o (pre ++ x ∷ post)) e
  ... | u , ψ , h = lanes-at (subst (Shape u) h (shape u)) pre x post refl ψ
  path-at (inSrc k b c) x e with path-at c (connS k x b) e
  ... | u , ψ , h with subst (Shape u) h (shape u)
  ...   | sh-conn {s = s} = s , ψ ⊕ in-source here , refl
  path-at (inBody k o c) x e with path-at c (connS k o x) e
  ... | u , ψ , h with subst (Shape u) h (shape u)
  ...   | sh-conn {b = b} = b , ψ ⊕ in-body here , refl

  -- The `of` a job resumes is the witness's at the job's path.
  of-path : ∀ {g m Γ A} {c : Ctx R Γ A} {xs i p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , ofS xs , resuming (next i) , p , rs ⟩
          → Σ Pos λ p₀ → Σ ℕ λ j → Path (Carried.tree cr) (ofˢ {Γ} {A} p₀ j xs) (dirs c)
  of-path {c = c} {xs} cr e with path-at c (ofS xs) (subst (Kernels (Carried.tree cr)) e (Carried.kernels cr))
  ... | u , ψ , h with subst (Shape u) h (shape u)
  ...   | sh-of {p = p₀} {i = j} = p₀ , j , ψ

  -- The takeWhile a job resumes is the witness's at the job's path.
  take-path : ∀ {g m Γ A} {c : Ctx R Γ A} {i q s τ p rs} (cr : Carried g m) → Mach.conf m ≡ ⟨ c , takeS i q s , resuming τ , p , rs ⟩
            → Σ _ λ tk → Σ (Sub Γ A) λ u → Path (Carried.tree cr) (takeWhileˢ i q tk u) (dirs c)
  take-path {c = c} {i = i} {q} {s} cr e with path-at c (takeS i q s) (subst (Kernels (Carried.tree cr)) e (Carried.kernels cr))
  ... | u , ψ , h with subst (Shape u) h (shape u)
  ...   | sh-take {tk = tk} {s = v} = tk , v , ψ
