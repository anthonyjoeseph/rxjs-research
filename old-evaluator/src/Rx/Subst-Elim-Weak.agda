------------------------------------------------------------------
-- A VARIABLE THE TERM NEVER NAMES IS ELIMINATED FOR FREE.
------------------------------------------------------------------

-- WHAT THE TWO WALKS DO TO A TERM THAT CAME IN BY RENAMING.  Both
-- eliminators are the identity except at the one node that can name
-- the variable being removed, so the whole content is bookkeeping
-- about POSITIONS: what the comparison says at a renamed position,
-- and how that survives the deferred shuffle's two context
-- identities.  It is stated over an arbitrary renaming rather than
-- over the weakening it is wanted for, because the induction walks
-- under binders and a closed subterm stops being closed the moment
-- it does -- what survives is that the renaming's image AVOIDS the
-- position being eliminated.  The maps are compared POINTWISE, so
-- nothing here needs extensionality.
--
-- WHY THE DEFERRED FACE CARRIES AN EQUATION AND THE GUARDED ONE DOES
-- NOT.  Eliminating from the deferred context reindexes it, and the
-- shuffle under a `deferᵉ` re-splits the concatenation, so the walk's
-- result and the renamed term live at contexts that agree only up to
-- one of the two `⊟`/`++` identities.  Carrying that identity as a
-- PARAMETER and matching it `refl` in every clause is what keeps the
-- arms congruences: the caller instantiates it at the shuffle, and
-- the induction never sees a transport.
module Rx.Subst-Elim-Weak where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Rx.Exp
  using ( Ty; Ctx; Exp; Tm; Ren∈; ext∈; ++Ren; renExp; renTm; renTms
        ; _×ᵗ_
        ; _⊟_; ⊟-++ˡ; ⊟-++ʳ; compare∈
        ; elimGExp; elimGTm; elimGTms; elimDExp; elimDTm; elimDTms
        ; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ
        ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ
        ; varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ
        ; caseᵗ; ifᵗ; primᵗ; strmᵗ )
open import Rx.Subst-Transport using (cong₃)
open import Rx.Subst-Split using (isˡ; isʳ; split; ++Ren-l; ++Ren-r)

private
  variable
    n            : ℕ
    Γ            : Ctx n
    Δᵍ Δ Δ₀ᵍ Δ₀  : List Ty
    Θ Θ₀ Θsub Δd : List Ty
    s t u        : Ty

------------------------------------------------------------------
-- TRANSPORTING A POSITION ALONG A CONTEXT IDENTITY.  Each is the
-- one-constructor step of the two shuffle identities, which are both
-- `cong (g ∷_)` chains, so a clause that goes under a cons needs
-- exactly this to move its transport past the constructor.
------------------------------------------------------------------

private
  hereˢ : {A B : List Ty} (p : A ≡ B) (e : u ≡ s)
        → here e ≡ subst (u ∈_) (sym (cong (s ∷_) p)) (here e)
  hereˢ refl e = refl

  thereˢ : {A B : List Ty} (p : A ≡ B) (w : u ∈ B)
         → there {x = s} (subst (u ∈_) (sym p) w)
             ≡ subst (u ∈_) (sym (cong (s ∷_) p)) (there w)
  thereˢ refl w = refl

  -- THE SUM THE COMPARISON RETURNS, MAPPED TWICE AND MAPPED ONCE.
  -- Stated over bare functions because every use below is a different
  -- pair of position transports and only their composite matters.
  mapmap : {X A B C : Set} (f : A → B) (g : B → C) (h : A → C)
         → (∀ a → g (f a) ≡ h a) → (v : X ⊎ A) → map₂ g (map₂ f v) ≡ map₂ h v
  mapmap f g h hh (inj₁ _) = refl
  mapmap f g h hh (inj₂ a) = cong inj₂ (hh a)

  map₂-id : {X A : Set} (v : X ⊎ A) → map₂ (λ a → a) v ≡ v
  map₂-id (inj₁ _) = refl
  map₂-id (inj₂ _) = refl

------------------------------------------------------------------
-- THE COMPARISON UNDER A CONS, AND UNDER EACH HALF OF THE SHUFFLE.
-- `compare∈` takes its recursive step behind a `with`, so the step
-- is restated here as an equation between whole sums; every lemma
-- below that goes under a cons spends it rather than re-abstracting.
------------------------------------------------------------------

compare-there : ∀ {A : Set} {a b s : A} {xs} (x : a ∈ xs) (y : b ∈ xs)
              → compare∈ (there {x = s} x) (there y) ≡ map₂ there (compare∈ x y)
compare-there x y with compare∈ x y
... | inj₁ _ = refl
... | inj₂ _ = refl

-- THE ELIMINATED POSITION IS IN THE LEFT HALF, and so is the one
-- being compared: the comparison is the one the un-shuffled contexts
-- already made, read through the left injection.
cmpˡˡ : ∀ {t u : Ty} {Δᵍ : List Ty} (Δ : List Ty) (x : t ∈ Δᵍ) (z : u ∈ Δᵍ)
      → compare∈ (∈-++⁺ˡ {ys = Δ} x) (∈-++⁺ˡ z)
          ≡ map₂ (λ w → subst (u ∈_) (sym (⊟-++ˡ {Δ = Δ} x)) (∈-++⁺ˡ w))
                 (compare∈ x z)
cmpˡˡ Δ (here refl) (here refl) = refl
cmpˡˡ Δ (here refl) (there z)   = refl
cmpˡˡ Δ (there x)   (here refl) = cong inj₂ (hereˢ (⊟-++ˡ x) refl)
cmpˡˡ {u = u} {Δᵍ = g ∷ Δᵍ} Δ (there x) (there z) =
  trans (compare-there (∈-++⁺ˡ x) (∈-++⁺ˡ z))
    (trans (cong (map₂ there) (cmpˡˡ Δ x z))
      (trans (mapmap fx there h step (compare∈ x z))
             (sym (trans (cong (map₂ fg) (compare-there x z))
                         (mapmap there fg h (λ _ → refl) (compare∈ x z))))))
  where
    fx : u ∈ (Δᵍ ⊟ x) → u ∈ ((Δᵍ ++ Δ) ⊟ ∈-++⁺ˡ x)
    fx w = subst (u ∈_) (sym (⊟-++ˡ x)) (∈-++⁺ˡ w)
    fg : u ∈ (g ∷ (Δᵍ ⊟ x)) → u ∈ ((g ∷ (Δᵍ ++ Δ)) ⊟ ∈-++⁺ˡ (there x))
    fg w = subst (u ∈_) (sym (⊟-++ˡ (there x))) (∈-++⁺ˡ w)
    h : u ∈ (Δᵍ ⊟ x) → u ∈ ((g ∷ (Δᵍ ++ Δ)) ⊟ ∈-++⁺ˡ (there x))
    h w = fg (there w)
    step : (w : u ∈ (Δᵍ ⊟ x)) → there (fx w) ≡ h w
    step w = thereˢ (⊟-++ˡ x) (∈-++⁺ˡ w)

-- THE ELIMINATED POSITION IS IN THE LEFT HALF AND THE COMPARED ONE
-- IN THE RIGHT: they can never coincide, so the answer is the right
-- half's own position, shuffled.
cmpˡʳ : ∀ {t u : Ty} {Δᵍ : List Ty} (Δ : List Ty) (x : t ∈ Δᵍ) (z : u ∈ Δ)
      → compare∈ (∈-++⁺ˡ {ys = Δ} x) (∈-++⁺ʳ Δᵍ z)
          ≡ inj₂ (subst (u ∈_) (sym (⊟-++ˡ {Δ = Δ} x)) (∈-++⁺ʳ (Δᵍ ⊟ x) z))
cmpˡʳ Δ (here refl) z = refl
cmpˡʳ {Δᵍ = g ∷ Δᵍ} Δ (there x) z =
  trans (compare-there (∈-++⁺ˡ x) (∈-++⁺ʳ Δᵍ z))
    (trans (cong (map₂ there) (cmpˡʳ Δ x z))
           (cong inj₂ (thereˢ (⊟-++ˡ x) (∈-++⁺ʳ (Δᵍ ⊟ x) z))))

-- THE ELIMINATED POSITION IS IN THE RIGHT HALF AND THE COMPARED ONE
-- IN THE LEFT: the mirror of the previous, and the recursion is on
-- the left half rather than on the position.
cmpʳˡ : ∀ {t u : Ty} {Δ : List Ty} (Δᵍ : List Ty) (x : t ∈ Δ) (z : u ∈ Δᵍ)
      → compare∈ (∈-++⁺ʳ Δᵍ x) (∈-++⁺ˡ {ys = Δ} z)
          ≡ inj₂ (subst (u ∈_) (sym (⊟-++ʳ {Δᵍ = Δᵍ} x)) (∈-++⁺ˡ z))
cmpʳˡ [] x ()
cmpʳˡ (g ∷ Δᵍ) x (here refl) = cong inj₂ (hereˢ (⊟-++ʳ {Δᵍ = Δᵍ} x) refl)
cmpʳˡ (g ∷ Δᵍ) x (there z) =
  trans (compare-there (∈-++⁺ʳ Δᵍ x) (∈-++⁺ˡ z))
    (trans (cong (map₂ there) (cmpʳˡ Δᵍ x z))
           (cong inj₂ (thereˢ (⊟-++ʳ {Δᵍ = Δᵍ} x) (∈-++⁺ˡ z))))

-- BOTH POSITIONS ARE IN THE RIGHT HALF: the comparison the
-- un-shuffled contexts made, read through the right injection.
cmpʳʳ : ∀ {t u : Ty} {Δ : List Ty} (Δᵍ : List Ty) (x : t ∈ Δ) (z : u ∈ Δ)
      → compare∈ (∈-++⁺ʳ Δᵍ x) (∈-++⁺ʳ Δᵍ z)
          ≡ map₂ (λ w → subst (u ∈_) (sym (⊟-++ʳ {Δᵍ = Δᵍ} x)) (∈-++⁺ʳ Δᵍ w))
                 (compare∈ x z)
cmpʳʳ [] x z = sym (map₂-id (compare∈ x z))
cmpʳʳ {u = u} {Δ = Δ} (g ∷ Δᵍ) x z =
  trans (compare-there (∈-++⁺ʳ Δᵍ x) (∈-++⁺ʳ Δᵍ z))
    (trans (cong (map₂ there) (cmpʳʳ Δᵍ x z))
           (mapmap fx there h step (compare∈ x z)))
  where
    fx : u ∈ (Δ ⊟ x) → u ∈ ((Δᵍ ++ Δ) ⊟ ∈-++⁺ʳ Δᵍ x)
    fx w = subst (u ∈_) (sym (⊟-++ʳ {Δᵍ = Δᵍ} x)) (∈-++⁺ʳ Δᵍ w)
    h : u ∈ (Δ ⊟ x) → u ∈ ((g ∷ (Δᵍ ++ Δ)) ⊟ ∈-++⁺ʳ (g ∷ Δᵍ) x)
    h w = subst (u ∈_) (sym (⊟-++ʳ {Δᵍ = g ∷ Δᵍ} x)) (∈-++⁺ʳ (g ∷ Δᵍ) w)
    step : (w : u ∈ (Δ ⊟ x)) → there (fx w) ≡ h w
    step w = thereˢ (⊟-++ʳ {Δᵍ = Δᵍ} x) (∈-++⁺ʳ Δᵍ w)

------------------------------------------------------------------
-- WHAT A RENAMING OWES: ITS IMAGE MISSES THE POSITION BEING
-- ELIMINATED, and the witness of that is the position the walk will
-- emit.  The identity `p` is what the deferred shuffle re-splits;
-- at `refl` this is the plain claim and the transport disappears.
------------------------------------------------------------------

Avoids : (x : t ∈ Δᵍ) {Δd : List Ty} → (Δᵍ ⊟ x) ≡ Δd
       → Ren∈ Δ₀ᵍ Δᵍ → Ren∈ Δ₀ᵍ Δd → Set
Avoids {Δ₀ᵍ = Δ₀ᵍ} x p ρ⁺ ρ =
  ∀ {u} (y : u ∈ Δ₀ᵍ) → compare∈ x (ρ⁺ y) ≡ inj₂ (subst (u ∈_) (sym p) (ρ y))

avoids-ext : {x : t ∈ Δᵍ} {ρ⁺ : Ren∈ Δ₀ᵍ Δᵍ} {ρ : Ren∈ Δ₀ᵍ (Δᵍ ⊟ x)}
           → Avoids x refl ρ⁺ ρ
           → Avoids (there {x = s} x) refl (ext∈ ρ⁺) (ext∈ ρ)
avoids-ext av (here refl) = refl
avoids-ext {x = x} av (there y) =
  trans (compare-there x _) (cong (map₂ there) (av y))

-- THE GUARDED FACE'S SHUFFLE: the position moves into the left half
-- and the concatenated renaming still misses it.
avoids-++ˡ : {x : t ∈ Δᵍ} {ρ⁺ : Ren∈ Δ₀ᵍ Δᵍ} {ρ : Ren∈ Δ₀ᵍ (Δᵍ ⊟ x)}
             (ρd : Ren∈ Δ₀ Δ)
           → Avoids x refl ρ⁺ ρ
           → Avoids (∈-++⁺ˡ {ys = Δ} x) (⊟-++ˡ x)
                    (++Ren ρ⁺ ρd) (++Ren ρ ρd)
avoids-++ˡ {Δ₀ᵍ = Δ₀ᵍ} {Δ = Δ} {x = x} {ρ⁺ = ρ⁺} {ρ = ρ} ρd av y
  with split Δ₀ᵍ _ y
... | isˡ a eq =
  trans (cong (compare∈ (∈-++⁺ˡ x)) (++Ren-l ρ⁺ ρd y a eq))
    (trans (cmpˡˡ Δ x (ρ⁺ a))
      (trans (cong (map₂ _) (av a))
             (cong (λ z → inj₂ (subst (_ ∈_) (sym (⊟-++ˡ x)) z))
                   (sym (++Ren-l ρ ρd y a eq)))))
... | isʳ b eq =
  trans (cong (compare∈ (∈-++⁺ˡ x)) (++Ren-r ρ⁺ ρd y b eq))
    (trans (cmpˡʳ Δ x (ρd b))
           (cong (λ z → inj₂ (subst (_ ∈_) (sym (⊟-++ˡ x)) z))
                 (sym (++Ren-r ρ ρd y b eq))))

-- THE DEFERRED FACE'S SHUFFLE: the mirror, with the position in the
-- right half and the guarded renaming untouched.
avoids-++ʳ : {x : t ∈ Δ} {ρ⁺ : Ren∈ Δ₀ Δ} {ρ : Ren∈ Δ₀ (Δ ⊟ x)}
             (ρg : Ren∈ Δ₀ᵍ Δᵍ)
           → Avoids x refl ρ⁺ ρ
           → Avoids (∈-++⁺ʳ Δᵍ x) (⊟-++ʳ x)
                    (++Ren ρg ρ⁺) (++Ren ρg ρ)
avoids-++ʳ {Δ₀ᵍ = Δ₀ᵍ} {Δᵍ = Δᵍ} {x = x} {ρ⁺ = ρ⁺} {ρ = ρ} ρg av y
  with split Δ₀ᵍ _ y
... | isˡ a eq =
  trans (cong (compare∈ (∈-++⁺ʳ Δᵍ x)) (++Ren-l ρg ρ⁺ y a eq))
    (trans (cmpʳˡ Δᵍ x (ρg a))
           (cong (λ z → inj₂ (subst (_ ∈_) (sym (⊟-++ʳ {Δᵍ = Δᵍ} x)) z))
                 (sym (++Ren-l ρg ρ y a eq))))
... | isʳ b eq =
  trans (cong (compare∈ (∈-++⁺ʳ Δᵍ x)) (++Ren-r ρg ρ⁺ y b eq))
    (trans (cmpʳʳ Δᵍ x (ρ⁺ b))
      (trans (cong (map₂ _) (av b))
             (cong (λ z → inj₂ (subst (_ ∈_) (sym (⊟-++ʳ {Δᵍ = Δᵍ} x)) z))
                   (sym (++Ren-r ρg ρ y b eq)))))

private
  -- THE DEFERRED WALK'S ONLY DECIDING CLAUSE, taken apart outside its
  -- own `with` so the comparison can be supplied rather than redone.
  elimD-var : (Θl : List Ty) (x : t ∈ Δ) (cl : Exp Γ [] [] Θsub t)
              (y : u ∈ Δ) (z : u ∈ (Δ ⊟ x))
            → compare∈ x y ≡ inj₂ z
            → elimDExp {Δᵍ = Δᵍ} Θl x cl (varᵉ y) ≡ varᵉ z
  elimD-var Θl x cl y z eq with compare∈ x y | eq
  ... | inj₂ _ | refl = refl

------------------------------------------------------------------
-- THE TWO WALKS ARE THE IDENTITY ON AN AVOIDING RENAMING.
------------------------------------------------------------------

mutual
  elimG-avᵉ : (Θl : List Ty) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] Θsub t)
              {ρ⁺ : Ren∈ Δ₀ᵍ Δᵍ} {ρg : Ren∈ Δ₀ᵍ (Δᵍ ⊟ x)}
              {ρd : Ren∈ Δ₀ Δ} {ρt : Ren∈ Θ₀ (Θl ++ Θsub)}
            → Avoids x refl ρ⁺ ρg
            → (e : Exp Γ Δ₀ᵍ Δ₀ Θ₀ u)
            → elimGExp Θl x cl (renExp ρ⁺ ρd ρt e) ≡ renExp ρg ρd ρt e
  elimG-avᵉ Θl x cl av (input i)  = refl
  elimG-avᵉ Θl x cl av emptyᵉ     = refl
  elimG-avᵉ Θl x cl av (varᵉ y)   = refl
  elimG-avᵉ Θl x cl av (ofᵉ ts)   = cong ofᵉ (elimG-avˢ Θl x cl av ts)
  elimG-avᵉ Θl x cl av (mapᵉ {s = s} f e) =
    cong₂ mapᵉ (elimG-avᵗ (s ∷ Θl) x cl av f) (elimG-avᵉ Θl x cl av e)
  elimG-avᵉ Θl x cl av (takeᵉ m e) =
    cong₂ takeᵉ (elimG-avᵗ Θl x cl av m) (elimG-avᵉ Θl x cl av e)
  elimG-avᵉ Θl x cl av (scanᵉ {s = s} {t = w} f i e) =
    cong₃ scanᵉ (elimG-avᵗ ((w ×ᵗ s) ∷ Θl) x cl av f)
                (elimG-avᵗ Θl x cl av i) (elimG-avᵉ Θl x cl av e)
  elimG-avᵉ Θl x cl av (mergeAllᵉ lim e) =
    cong (mergeAllᵉ lim) (elimG-avᵉ Θl x cl av e)
  elimG-avᵉ Θl x cl av (switchAllᵉ e)  = cong switchAllᵉ (elimG-avᵉ Θl x cl av e)
  elimG-avᵉ Θl x cl av (exhaustAllᵉ e) = cong exhaustAllᵉ (elimG-avᵉ Θl x cl av e)
  elimG-avᵉ Θl x cl av (μᵉ e) =
    cong μᵉ (elimG-avᵉ Θl (there x) cl (avoids-ext av) e)
  elimG-avᵉ Θl x cl {ρ⁺ = ρ⁺} {ρg = ρg} {ρd = ρd} av (deferᵉ e) =
    cong deferᵉ (elimD-avᵉ Θl (∈-++⁺ˡ x) (⊟-++ˡ x) cl
                   (avoids-++ˡ {x = x} {ρ⁺ = ρ⁺} {ρ = ρg} ρd av) e)

  elimG-avᵗ : (Θl : List Ty) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] Θsub t)
              {ρ⁺ : Ren∈ Δ₀ᵍ Δᵍ} {ρg : Ren∈ Δ₀ᵍ (Δᵍ ⊟ x)}
              {ρd : Ren∈ Δ₀ Δ} {ρt : Ren∈ Θ₀ (Θl ++ Θsub)}
            → Avoids x refl ρ⁺ ρg
            → (m : Tm Γ Δ₀ᵍ Δ₀ Θ₀ u)
            → elimGTm Θl x cl (renTm ρ⁺ ρd ρt m) ≡ renTm ρg ρd ρt m
  elimG-avᵗ Θl x cl av (varᵗ y)    = refl
  elimG-avᵗ Θl x cl av unit̂        = refl
  elimG-avᵗ Θl x cl av (bool̂ b)    = refl
  elimG-avᵗ Θl x cl av (nat̂ m)     = refl
  elimG-avᵗ Θl x cl av (pairᵗ a b) =
    cong₂ pairᵗ (elimG-avᵗ Θl x cl av a) (elimG-avᵗ Θl x cl av b)
  elimG-avᵗ Θl x cl av (fstᵗ q) = cong fstᵗ (elimG-avᵗ Θl x cl av q)
  elimG-avᵗ Θl x cl av (sndᵗ q) = cong sndᵗ (elimG-avᵗ Θl x cl av q)
  elimG-avᵗ Θl x cl av (inlᵗ a) = cong inlᵗ (elimG-avᵗ Θl x cl av a)
  elimG-avᵗ Θl x cl av (inrᵗ a) = cong inrᵗ (elimG-avᵗ Θl x cl av a)
  elimG-avᵗ Θl x cl av (caseᵗ {s = s} {t = w} sc l r) =
    cong₃ caseᵗ (elimG-avᵗ Θl x cl av sc) (elimG-avᵗ (s ∷ Θl) x cl av l)
                (elimG-avᵗ (w ∷ Θl) x cl av r)
  elimG-avᵗ Θl x cl av (ifᵗ c a b) =
    cong₃ ifᵗ (elimG-avᵗ Θl x cl av c) (elimG-avᵗ Θl x cl av a)
              (elimG-avᵗ Θl x cl av b)
  elimG-avᵗ Θl x cl av (primᵗ op a) = cong (primᵗ op) (elimG-avᵗ Θl x cl av a)
  elimG-avᵗ Θl x cl av (strmᵗ e)    = cong strmᵗ (elimG-avᵉ Θl x cl av e)

  elimG-avˢ : (Θl : List Ty) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] Θsub t)
              {ρ⁺ : Ren∈ Δ₀ᵍ Δᵍ} {ρg : Ren∈ Δ₀ᵍ (Δᵍ ⊟ x)}
              {ρd : Ren∈ Δ₀ Δ} {ρt : Ren∈ Θ₀ (Θl ++ Θsub)}
            → Avoids x refl ρ⁺ ρg
            → (ts : List (Tm Γ Δ₀ᵍ Δ₀ Θ₀ u))
            → elimGTms Θl x cl (renTms ρ⁺ ρd ρt ts) ≡ renTms ρg ρd ρt ts
  elimG-avˢ Θl x cl av []       = refl
  elimG-avˢ Θl x cl av (y ∷ ys) =
    cong₂ _∷_ (elimG-avᵗ Θl x cl av y) (elimG-avˢ Θl x cl av ys)

  elimD-avᵉ : (Θl : List Ty) (x : t ∈ Δ) (p : (Δ ⊟ x) ≡ Δd)
              (cl : Exp Γ [] [] Θsub t)
              {ρg : Ren∈ Δ₀ᵍ Δᵍ} {ρ⁺ : Ren∈ Δ₀ Δ} {ρd : Ren∈ Δ₀ Δd}
              {ρt : Ren∈ Θ₀ (Θl ++ Θsub)}
            → Avoids x p ρ⁺ ρd
            → (e : Exp Γ Δ₀ᵍ Δ₀ Θ₀ u)
            → subst (λ ζ → Exp Γ Δᵍ ζ (Θl ++ Θsub) u) p
                    (elimDExp Θl x cl (renExp ρg ρ⁺ ρt e))
                ≡ renExp ρg ρd ρt e
  elimD-avᵉ Θl x refl cl av (input i)  = refl
  elimD-avᵉ Θl x refl cl av emptyᵉ     = refl
  elimD-avᵉ Θl x refl cl av (varᵉ y)   = elimD-var Θl x cl _ _ (av y)
  elimD-avᵉ Θl x refl cl av (ofᵉ ts)   = cong ofᵉ (elimD-avˢ Θl x refl cl av ts)
  elimD-avᵉ Θl x refl cl av (mapᵉ {s = s} f e) =
    cong₂ mapᵉ (elimD-avᵗ (s ∷ Θl) x refl cl av f) (elimD-avᵉ Θl x refl cl av e)
  elimD-avᵉ Θl x refl cl av (takeᵉ m e) =
    cong₂ takeᵉ (elimD-avᵗ Θl x refl cl av m) (elimD-avᵉ Θl x refl cl av e)
  elimD-avᵉ Θl x refl cl av (scanᵉ {s = s} {t = w} f i e) =
    cong₃ scanᵉ (elimD-avᵗ ((w ×ᵗ s) ∷ Θl) x refl cl av f)
                (elimD-avᵗ Θl x refl cl av i) (elimD-avᵉ Θl x refl cl av e)
  elimD-avᵉ Θl x refl cl av (mergeAllᵉ lim e) =
    cong (mergeAllᵉ lim) (elimD-avᵉ Θl x refl cl av e)
  elimD-avᵉ Θl x refl cl av (switchAllᵉ e) =
    cong switchAllᵉ (elimD-avᵉ Θl x refl cl av e)
  elimD-avᵉ Θl x refl cl av (exhaustAllᵉ e) =
    cong exhaustAllᵉ (elimD-avᵉ Θl x refl cl av e)
  elimD-avᵉ Θl x refl cl av (μᵉ e) = cong μᵉ (elimD-avᵉ Θl x refl cl av e)
  elimD-avᵉ Θl x refl cl {ρg = ρg} av (deferᵉ e) =
    cong deferᵉ (elimD-avᵉ Θl (∈-++⁺ʳ _ x) (⊟-++ʳ x) cl (avoids-++ʳ ρg av) e)

  elimD-avᵗ : (Θl : List Ty) (x : t ∈ Δ) (p : (Δ ⊟ x) ≡ Δd)
              (cl : Exp Γ [] [] Θsub t)
              {ρg : Ren∈ Δ₀ᵍ Δᵍ} {ρ⁺ : Ren∈ Δ₀ Δ} {ρd : Ren∈ Δ₀ Δd}
              {ρt : Ren∈ Θ₀ (Θl ++ Θsub)}
            → Avoids x p ρ⁺ ρd
            → (m : Tm Γ Δ₀ᵍ Δ₀ Θ₀ u)
            → subst (λ ζ → Tm Γ Δᵍ ζ (Θl ++ Θsub) u) p
                    (elimDTm Θl x cl (renTm ρg ρ⁺ ρt m))
                ≡ renTm ρg ρd ρt m
  elimD-avᵗ Θl x refl cl av (varᵗ y)    = refl
  elimD-avᵗ Θl x refl cl av unit̂        = refl
  elimD-avᵗ Θl x refl cl av (bool̂ b)    = refl
  elimD-avᵗ Θl x refl cl av (nat̂ m)     = refl
  elimD-avᵗ Θl x refl cl av (pairᵗ a b) =
    cong₂ pairᵗ (elimD-avᵗ Θl x refl cl av a) (elimD-avᵗ Θl x refl cl av b)
  elimD-avᵗ Θl x refl cl av (fstᵗ q) = cong fstᵗ (elimD-avᵗ Θl x refl cl av q)
  elimD-avᵗ Θl x refl cl av (sndᵗ q) = cong sndᵗ (elimD-avᵗ Θl x refl cl av q)
  elimD-avᵗ Θl x refl cl av (inlᵗ a) = cong inlᵗ (elimD-avᵗ Θl x refl cl av a)
  elimD-avᵗ Θl x refl cl av (inrᵗ a) = cong inrᵗ (elimD-avᵗ Θl x refl cl av a)
  elimD-avᵗ Θl x refl cl av (caseᵗ {s = s} {t = w} sc l r) =
    cong₃ caseᵗ (elimD-avᵗ Θl x refl cl av sc)
                (elimD-avᵗ (s ∷ Θl) x refl cl av l)
                (elimD-avᵗ (w ∷ Θl) x refl cl av r)
  elimD-avᵗ Θl x refl cl av (ifᵗ c a b) =
    cong₃ ifᵗ (elimD-avᵗ Θl x refl cl av c) (elimD-avᵗ Θl x refl cl av a)
              (elimD-avᵗ Θl x refl cl av b)
  elimD-avᵗ Θl x refl cl av (primᵗ op a) =
    cong (primᵗ op) (elimD-avᵗ Θl x refl cl av a)
  elimD-avᵗ Θl x refl cl av (strmᵗ e) = cong strmᵗ (elimD-avᵉ Θl x refl cl av e)

  elimD-avˢ : (Θl : List Ty) (x : t ∈ Δ) (p : (Δ ⊟ x) ≡ Δd)
              (cl : Exp Γ [] [] Θsub t)
              {ρg : Ren∈ Δ₀ᵍ Δᵍ} {ρ⁺ : Ren∈ Δ₀ Δ} {ρd : Ren∈ Δ₀ Δd}
              {ρt : Ren∈ Θ₀ (Θl ++ Θsub)}
            → Avoids x p ρ⁺ ρd
            → (ts : List (Tm Γ Δ₀ᵍ Δ₀ Θ₀ u))
            → subst (λ ζ → List (Tm Γ Δᵍ ζ (Θl ++ Θsub) u)) p
                    (elimDTms Θl x cl (renTms ρg ρ⁺ ρt ts))
                ≡ renTms ρg ρd ρt ts
  elimD-avˢ Θl x refl cl av []       = refl
  elimD-avˢ Θl x refl cl av (y ∷ ys) =
    cong₂ _∷_ (elimD-avᵗ Θl x refl cl av y) (elimD-avˢ Θl x refl cl av ys)
