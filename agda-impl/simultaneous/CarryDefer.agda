{-# OPTIONS --guardedness #-}

-- A `defer` IS CARRIED THROUGH ITS APPROXIMANTS.  The bottom one spins
-- skips one label under each subscription, each carried by its fellow;
-- each further one is the body under the guard; the meaning is their
-- limit.
module simultaneous.CarryDefer where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; applyUpTo; filter)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-applyUpTo⁺; ∈-applyUpTo⁻; ∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Nullary using (¬_; ¬?; yes; no)

open import Tree using (Later; defer)
open import denotation.Position using (Pos; ix; _⊕_; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; skip; pin; Unpinned; EmissionSet; Truncate; Reach; Few; Spin; spin; _≺_; _≼_; Den; enter;
  DenEnv; approx; DeferT; guard; body)
open import denotation.Laws.Modulus using (≺-irrefl; ≺→≼; ≺-≼-≺; ticks; entered-reach)
open import denotation.Laws.Cut using (ix-asc; ix-back)
open import denotation.Laws.Worlds using (plain-ix; _⊑_; ⊑-refl; Hots; GoodEnv; Ok; ok-step; here; inW; step; nest-in; not-up; sib)
open import denotation.Laws using (aft; inv-approx)
open import simultaneous.SObs using (module Elaborate)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.Attribution using (Live; Shown; Match; Every; One; Reads)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Listing using (Listed)
open import simultaneous.Carry using (PMap; _⊆ᴹ_; Emb; Fresh; Within; CarryAt; Carry; carry; Cause; row; env; both; subs; Owes; Home; Read;
  instant-⊕; EnvRel; Bound; module OneUnder)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) using (IE; AIE; elab)

------------------------------------------------------------------------
-- The bottom approximant

-- A SPIN'S ROWS before its `i`th: the first `i`, each a row with as few
-- before it.
module SpinRows (q : Pos) where
  rows : ℕ → List Pos
  rows i = applyUpTo (λ j → q ⊕ [ ix j ]) i

  before : ∀ {A : Set} i {k} {e : Ev A} → Spin q k e → k ≺ (q ⊕ [ ix i ]) → k ∈ rows i
  before i (spin j) kq = ∈-applyUpTo⁺ (λ j → q ⊕ [ ix j ]) (ix-back q kq)

  reach : ∀ {A : Set} i → Reach {A} (Spin q) (q ⊕ [ ix i ]) skip
  reach i = rows i , λ x kq _ → before i x kq

  listed : ∀ {A : Set} i → Listed {A} (Truncate (Spin q)) (q ⊕ [ ix i ])
  listed {A} i = rows i , (λ x kq → before i (proj₁ x) kq) , back
    where
      back : ∀ {k} → k ∈ rows i → k ≺ (q ⊕ [ ix i ]) × Σ (Ev A) (Truncate (Spin q) k)
      back m with ∈-applyUpTo⁻ (λ j → q ⊕ [ ix j ]) m
      ... | j , lt , refl = ix-asc q lt , skip , spin j , reach j

-- Each skip of the plain spin, carried by the elaborated spin's skip at
-- its label, owed to it.
module SpinCarry {A : Set} {HP HE : Pos → Set} {M₀ : PMap} {p p₀ p′ : Pos}
                 (E₀ : Emb M₀) (fr : Fresh HP M₀ p) (m₀ : M₀ p p₀) (pp : p₀ ⊑ p′) where
  open OneUnder E₀ fr m₀ pp using (N; embN; M; up; up-⊕; down; down-⊕)

  private
    module P = SpinRows p
    module P′ = SpinRows p′

  t : EmissionSet A
  t = Truncate (Spin p)

  u : EmissionSet (IE A)
  u = Truncate (Spin p′)

  Img : Pos → Pos → Set
  Img k l = N k l × Σ (Ev A) (t k)

  img : ∀ {k e} → t k e → Unpinned e → Live t k → Listed t k
      → Σ Pos λ l → Img k l × Σ (Ev (IE A)) λ e′ → u l e′ × Listed u l × Match Every (One valuesOf) (Reads valuesOf) e e′
  img (spin i , r) _ _ _ =
    p′ ⊕ [ ix i ] , ((ix i , plain-ix , refl , refl) , skip , spin i , r) , skip , (spin i , P′.reach i) , P′.listed i , (λ ()) , λ _ ()

  cause : ∀ {r e} → u r e → Cause
  cause (spin i , _) = row (p ⊕ [ ix i ])

  owes : ∀ {r e} (ur : u r e) → Owes M HE t p′ (cause ur) r
  owes (spin i , _) = (λ n → n (skip , spin i , P.reach i)) , p′ ⊕ [ ix i ] , inj₂ (ix i , plain-ix , refl , refl) , refl

  fib : Cause → List Pos
  fib (row k) = [ up k ]
  fib _       = []

  in-fib : ∀ {r e} (ur : u r e) → r ∈ fib (cause ur)
  in-fib (spin i , _) = here (sym (up-⊕ [ ix i ]))

  carried : CarryAt valuesOf M HP HE t u p p′
  carried = record
    { Img     = Img
    ; ext     = λ { (n , _) → _ , inj₂ n , ⊑-refl _ }
    ; img     = img
    ; shown   = λ { (spin _ , _) () }
    ; img-row = λ { (_ , _ , spin i , r) n → n (skip , (spin i , r) , tt) }
    ; img-fun = λ { (n , _) (n′ , _) → Emb.fun embN n n′ }
    ; place   = λ { (spin i , _) _ _ → inj₁ (instant-⊕ p′ [ ix i ]) }
    ; live    = λ _ _ → λ { (() , _) }
    ; few     = λ { (_ , _ , spin i , _) → P.rows i , λ x kq → P.before i (proj₁ x) kq }
    ; cause   = cause
    ; owes    = owes
    ; fib     = fib
    ; in-fib  = in-fib
    ; read    = λ { (spin _ , _) () }
    ; bk      = λ l → [ down l ]
    ; in-bk   = λ { ((a , _ , refl , refl) , _) → here (sym (down-⊕ [ a ])) }
    ; pbk     = λ _ → []
    ; pinned  = λ { (() , _) _ }
    }

-- THE BOTTOM APPROXIMANT shows only skips: the spin, on both sides.
carry-⊥ : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A) → Carry (just zero) ρ (defer l)
carry-⊥ {A = A} ρ l = carry λ _ _ _ _ _ e₀ _ p p′ (_ , m₀ , pp) _ _ fr → spun e₀ fr m₀ pp
  where
    spun : ∀ {HP HE M₀ p p₀ p′} → Emb M₀ → Fresh HP M₀ p → M₀ p p₀ → p₀ ⊑ p′
         → Σ PMap λ M → M₀ ⊆ᴹ M × Emb M × Within HP M₀ M p
           × CarryAt valuesOf M HP HE (Truncate (Spin {A} p)) (Truncate (Spin {IE A} p′)) p p′
    spun {HP} {HE} E₀ fr m₀ pp = O.M , inj₁ , O.emb , O.within , X.carried
      where module X = SpinCarry {A} {HP} {HE} E₀ fr m₀ pp
            module O = OneUnder E₀ fr m₀ pp

------------------------------------------------------------------------
-- A grown map

-- A CARRY STAYS ONE along a larger map: the map is read only where a row
-- is put under its image.
carry-grow : ∀ {A Y} {f : Y → List A} {M M′ : PMap} {HP HE : Pos → Set} {t : EmissionSet A} {u : EmissionSet Y} {s s′ : Pos}
           → M ⊆ᴹ M′ → CarryAt f M HP HE t u s s′ → CarryAt f M′ HP HE t u s s′
carry-grow {A} {M = M} {M′} {HE = HE} {t} {s′ = s′} sub c = record
  { Img = Img ; ext = λ i → let (y , m , yl) = ext i in y , sub m , yl ; img = img ; shown = shown ; img-row = img-row
  ; img-fun = img-fun ; place = place ; live = live ; few = few ; cause = cause ; owes = λ ur → grown (cause ur) (owes ur)
  ; fib = fib ; in-fib = in-fib ; read = read ; bk = bk ; in-bk = in-bk ; pbk = pbk ; pinned = pinned }
  where
    open CarryAt c
    grown : ∀ c₀ {r} → Owes M HE t s′ c₀ r → Owes M′ HE t s′ c₀ r
    grown (row _)    (h , y , m , e) = h , y , sub m , e
    grown (env _)    o = o
    grown (both _ _) o = o
    grown subs       o = o

env-grow : ∀ {Γ Δ} {M M′ : PMap} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {envP : DenEnv Γ} {envE : DenEnv Δ}
         → M ⊆ᴹ M′ → EnvRel M ρ envP envE → EnvRel M′ ρ envP envE
env-grow sub er i = record { m = m ; src = src ; σ = σ ; envP = envP ; envE = envE ; at = at ; at′ = at′
                            ; carried = carry-grow sub carried ; isP = isP ; isE = isE }
  where open Bound (er i)

------------------------------------------------------------------------
-- The further approximants

-- A `defer`'s run past its subscription: the guard, then the body's run
-- under the next label, every row of which lies past the guard.
module Side {X : Set} (d : Den X) (q : Pos)
            (a : ∀ {y e} → enter d (q ⊕ [ ix 1 ]) y e → (q ⊕ [ ix 1 ]) ≼ y × (∀ {r} → e ≡ pin r → (q ⊕ [ ix 1 ]) ≼ r)) where
  g : Pos
  g = q ⊕ [ ix 0 ]

  T B : EmissionSet X
  T = Truncate (DeferT d q)
  B = enter d (q ⊕ [ ix 1 ])

  gb : ∀ {y e} → B y e → g ≺ y
  gb {y} x = ≺-≼-≺ {g} {q ⊕ [ ix 1 ]} {y} (ticks q 0) (proj₁ (a x))

  ¬g : ∀ {e} → B g e → ⊥
  ¬g x = ≺-irrefl {g} (gb x)

  none : ∀ {y e} → T y e → y ≺ g → ⊥
  none (guard , _)          lt = ≺-irrefl {g} lt
  none (body {y} x , _)     lt = ≺→≼ {g} {y} (gb x) lt

  gT : T g skip
  gT = guard , [] , λ { guard lt _ → ⊥-elim (≺-irrefl {g} lt) ; (body {y} x) lt _ → ⊥-elim (≺→≼ {g} {y} (gb x) lt) }

  up : ∀ {y e} → B y e → T y e
  up {y} x = body x , g ∷ proj₁ R , λ { guard _ _ → here refl ; (body x′) kq dp → there (proj₂ R x′ kq dp) }
    where R = entered-reach d (q ⊕ [ ix 1 ]) x

  live← : ∀ {k} → Live T k → Live B k
  live← lv x = lv (up x)

  live→ : ∀ {k} → Live B k → Live T k
  live→ lv (body x , _) = lv x

  few→ : ∀ {k} → Few B k → Few T k
  few→ (ks , F) = g ∷ ks , λ { (guard , _) _ → here refl ; (body x , _) kq → there (F x kq) }

  few← : ∀ {k} → Few T k → Few B k
  few← (ks , F) = ks , λ x kq → F (up x) kq

  lst← : ∀ {k} → Listed T k → Listed B k
  lst← {k} (ks , F , Bk) = filter (λ y → ¬? (y ≟ᵖ g)) ks , (λ x kq → ∈-filter⁺ (λ y → ¬? (y ≟ᵖ g)) (F (up x) kq) (λ { refl → ¬g x })) , back
    where
      back : ∀ {k′} → k′ ∈ filter (λ y → ¬? (y ≟ᵖ g)) ks → k′ ≺ k × Σ (Ev X) (B k′)
      back m with ∈-filter⁻ (λ y → ¬? (y ≟ᵖ g)) m
      ... | n , ne with Bk n
      ...   | _  , _ , (guard , _)  = ⊥-elim (ne refl)
      ...   | kq , e , (body x , _) = kq , e , x

  lst→ : ∀ {k e} → B k e → Listed B k → Listed T k
  lst→ x (ks , F , Bk) = g ∷ ks , (λ { (guard , _) _ → here refl ; (body x′ , _) kq → there (F x′ kq) })
                       , λ { (here refl) → gb x , skip , gT ; (there m) → let (kq , e , x′) = Bk m in kq , e , up x′ }

-- THE GUARD CARRIES THE GUARD and the body carries the body: a carry of
-- the body under each guard is one of the whole.
module NextCarry {A : Set} {HP HE : Pos → Set} {M : PMap} (s : Den A) (s′ : Den (IE A)) (p p′ : Pos)
  (mg : M (p ⊕ [ ix 0 ]) (p′ ⊕ [ ix 0 ]))
  (aP : ∀ {y e} → enter s (p ⊕ [ ix 1 ]) y e → (p ⊕ [ ix 1 ]) ≼ y × (∀ {r} → e ≡ pin r → (p ⊕ [ ix 1 ]) ≼ r))
  (aE : ∀ {y e} → enter s′ (p′ ⊕ [ ix 1 ]) y e → (p′ ⊕ [ ix 1 ]) ≼ y × (∀ {r} → e ≡ pin r → (p′ ⊕ [ ix 1 ]) ≼ r))
  (c : CarryAt valuesOf M HP HE (enter s (p ⊕ [ ix 1 ])) (enter s′ (p′ ⊕ [ ix 1 ])) (p ⊕ [ ix 1 ]) (p′ ⊕ [ ix 1 ])) where
  private
    module P = Side s p aP
    module E = Side s′ p′ aE
    module C = CarryAt c

  Img : Pos → Pos → Set
  Img k l = (k ≡ P.g × l ≡ E.g) ⊎ C.Img k l

  ext : ∀ {k l} → Img k l → Σ Pos λ y → M k y × y ⊑ l
  ext (inj₁ (refl , refl)) = E.g , mg , ⊑-refl E.g
  ext (inj₂ i)             = C.ext i

  img : ∀ {k e} → P.T k e → Unpinned e → Live P.T k → Listed P.T k
      → Σ Pos λ l → Img k l × Σ (Ev (IE A)) λ e′ → E.T l e′ × Listed E.T l × Match Every (One valuesOf) (Reads valuesOf) e e′
  img (guard , _) _ _ _ = E.g , inj₁ (refl , refl) , skip , E.gT , ([] , (λ x lt → ⊥-elim (E.none x lt)) , λ ()) , (λ ()) , λ _ ()
  img (body x , _) un lv ls with C.img x un (P.live← lv) (P.lst← ls)
  ... | l , i , e′ , ul , lu , m = l , inj₂ i , e′ , E.up ul , E.lst→ ul lu , m

  shown : ∀ {l e} → E.T l e → Shown (One valuesOf) e → Live E.T l → Few E.T l
        → Σ Pos λ k → Img k l × Σ (Ev A) λ e₀ → P.T k e₀ × Match Every (One valuesOf) (Reads valuesOf) e₀ e
  shown (guard , _) ()
  shown (body y , _) sh lv fw with C.shown y sh (E.live← lv) (E.few← fw)
  ... | k , i , e₀ , tk , m = k , inj₂ i , e₀ , P.up tk , m

  img-row : ∀ {k l} → Img k l → ¬ ¬ Σ (Ev A) λ e → P.T k e × Unpinned e
  img-row (inj₁ (refl , refl)) n = n (skip , P.gT , tt)
  img-row (inj₂ i)             n = C.img-row i λ { (e , x , un) → n (e , P.up x , un) }

  img-fun : ∀ {k l l′} → Img k l → Img k l′ → l ≡ l′
  img-fun (inj₁ (refl , refl)) (inj₁ (refl , refl)) = refl
  img-fun (inj₂ i)             (inj₂ i′)            = C.img-fun i i′
  img-fun (inj₁ (refl , refl)) (inj₂ i)             = ⊥-elim (C.img-row i λ { (_ , x , _) → P.¬g x })
  img-fun (inj₂ i)             (inj₁ (refl , refl)) = ⊥-elim (C.img-row i λ { (_ , x , _) → P.¬g x })

  place : ∀ {m e} → E.T m e → Live E.T m → Few E.T m
        → instantOf m ≡ instantOf p′ ⊎ (Σ Pos λ k → Σ Pos λ l → Img k l × instantOf l ≡ instantOf m)
          ⊎ Σ Pos λ h → HE h × instantOf h ≡ instantOf m
  place (guard , _) _ _ = inj₁ (instant-⊕ p′ [ ix 0 ])
  place (body y , _) lv fw with C.place y (E.live← lv) (E.few← fw)
  ... | inj₁ e                     = inj₁ (trans e (instant-⊕ p′ [ ix 1 ]))
  ... | inj₂ (inj₁ (k , l , i , e)) = inj₂ (inj₁ (k , l , inj₂ i , e))
  ... | inj₂ (inj₂ h)               = inj₂ (inj₂ h)

  live : ∀ {k l} → Img k l → Live P.T k → Live E.T l
  live (inj₁ (refl , refl)) _  (body {y} x , _) = ≺→≼ {E.g} {y} (E.gb x)
  live (inj₂ i)             lv x                = E.live→ (C.live i (P.live← lv)) x

  few : ∀ {k l} → Img k l → Few P.T k
  few (inj₁ (refl , refl)) = [] , λ x lt → ⊥-elim (P.none x lt)
  few (inj₂ i)             = P.few→ (C.few i)

  cause : ∀ {r e} → E.T r e → Cause
  cause (guard , _)  = row P.g
  cause (body y , _) = C.cause y

  owes→ : ∀ c₀ {r} → Owes M HE P.B (p′ ⊕ [ ix 1 ]) c₀ r → Owes M HE P.T p′ c₀ r
  owes→ (row k)    (h , y , m , e) = (λ n → h λ { (e′ , x) → n (e′ , P.up x) }) , y , m , e
  owes→ (env h)    o               = o
  owes→ (both k h) (h₁ , o)        = (λ n → h₁ λ { (e′ , x) → n (e′ , P.up x) }) , o
  owes→ subs       e               = trans e (instant-⊕ p′ [ ix 1 ])

  owes : ∀ {r e} (ur : E.T r e) → Owes M HE P.T p′ (cause ur) r
  owes (guard , _)  = (λ n → n (skip , P.gT)) , E.g , mg , refl
  owes (body y , _) = owes→ (C.cause y) (C.owes y)

  fib : Cause → List Pos
  fib c₀ = E.g ∷ C.fib c₀

  in-fib : ∀ {r e} (ur : E.T r e) → r ∈ fib (cause ur)
  in-fib (guard , _)  = here refl
  in-fib (body y , _) = there (C.in-fib y)

  read : ∀ {r e} (ur : E.T r e) → Read (cause ur) → Live E.T r
  read (guard , _) ()
  read (body y , _) rd = E.live→ (C.read y rd)

  bk : Pos → List Pos
  bk l = P.g ∷ C.bk l

  in-bk : ∀ {k l} → Img k l → k ∈ bk l
  in-bk (inj₁ (refl , refl)) = here refl
  in-bk (inj₂ i)             = there (C.in-bk i)

  homed : ∀ {k q} → instantOf k ≡ instantOf (p ⊕ [ ix 1 ]) ⊎ (Σ Pos λ k₀ → k₀ ≺ q × Home P.B k₀ × instantOf k₀ ≡ instantOf k)
                    ⊎ Σ Pos (λ h → HP h × instantOf h ≡ instantOf k)
        → instantOf k ≡ instantOf p ⊎ (Σ Pos λ k₀ → k₀ ≺ q × Home P.T k₀ × instantOf k₀ ≡ instantOf k)
          ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k
  homed (inj₁ e)                       = inj₁ (trans e (instant-⊕ p [ ix 1 ]))
  homed (inj₂ (inj₁ (k₀ , kq , h , e))) = inj₂ (inj₁ (k₀ , kq , (λ n → h λ { (e′ , x , un) → n (e′ , P.up x , un) }) , e))
  homed (inj₂ (inj₂ h))                = inj₂ (inj₂ h)

  pinned : ∀ {k q} → P.T k (pin q) → Live P.T k
         → (Σ Pos λ l → Σ Pos λ q′ → E.T l (pin q′) × k ∈ C.pbk l)
           × (instantOf k ≡ instantOf p ⊎ (Σ Pos λ k₀ → k₀ ≺ q × Home P.T k₀ × instantOf k₀ ≡ instantOf k)
              ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)
  pinned {k} {q} (body x , _) lv with C.pinned x (P.live← lv)
  ... | (l , q′ , ul , m) , r = (l , q′ , E.up ul , m) , homed {k} {q} r

  carried : CarryAt valuesOf M HP HE P.T E.T p p′
  carried = record
    { Img = Img ; ext = ext ; img = img ; shown = shown ; img-row = img-row ; img-fun = img-fun ; place = place
    ; live = live ; few = few ; cause = cause ; owes = owes ; fib = fib ; in-fib = in-fib ; read = read
    ; bk = bk ; in-bk = in-bk ; pbk = C.pbk ; pinned = pinned }

-- EACH FURTHER APPROXIMANT is the body under the guard: the map grown by
-- the guard and the body's subscription, held fresh at the body's.
carry-next : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A)
           → Carry (just n) ρ (Later.force l) → Carry (just (suc n)) ρ (defer l)
carry-next n {Γ} {Δ} {A} ρ l (carry h) = carry λ envP envE gP gE M₀ hm er p p′ (_ , m₀ , pp) okP okE fr →
  nexted envP envE gP gE M₀ hm er p p′ m₀ pp okP okE fr
  where
    nexted : ∀ (envP : DenEnv Γ) (envE : DenEnv Δ) → GoodEnv envP → GoodEnv envE → ∀ M₀ → Emb M₀ → EnvRel M₀ ρ envP envE
           → ∀ p p′ {p₀} → M₀ p p₀ → p₀ ⊑ p′ → Ok (Hots envP) p → Ok (Hots envE) p′ → Fresh (Hots envP) M₀ p
           → Σ PMap λ M → M₀ ⊆ᴹ M × Emb M × Within (Hots envP) M₀ M p
             × CarryAt valuesOf M (Hots envP) (Hots envE) (Truncate (DeferT (approx n (Later.force l) envP) p))
                 (Truncate (DeferT (approx n (elab ρ (Later.force l)) envE) p′)) p p′
    nexted envP envE gP gE M₀ hm er p p′ m₀ pp okP okE fr
      with h envP envE gP gE O.M O.emb (env-grow {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} inj₁ er) (p ⊕ [ ix 1 ]) (p′ ⊕ [ ix 1 ])
             (p′ ⊕ [ ix 1 ] , inj₂ (ix 1 , plain-ix , refl , refl) , ⊑-refl (p′ ⊕ [ ix 1 ])) (ok-step p okP) (ok-step p′ okE) fresh₁
      where
        module O = OneUnder hm fr m₀ pp

        fresh₁ : Fresh (Hots envP) O.M (p ⊕ [ ix 1 ])
        fresh₁ (inj₁ m) (w , ww , wx) with fr m (w , inW (nest-in (step here plain-ix) ww) , wx)
        ... | refl = ⊥-elim (not-up (proj₁ okP) ww wx)
        fresh₁ (inj₂ (a , pl , refl , _)) (w , ww , wx) with (p ⊕ [ a ]) ≟ᵖ (p ⊕ [ ix 1 ])
        ... | yes e = e
        ... | no ne = ⊥-elim (sib (proj₁ okP) pl (⊑-refl p) ne ww wx)
    ... | M , ms , hm′ , wi , c =
      M , (λ m → ms (inj₁ m)) , hm′ , wi′
        , NextCarry.carried (approx n (Later.force l) envP) (approx n (elab ρ (Later.force l)) envE) p p′
            (ms (inj₂ (ix 0 , plain-ix , refl , refl)))
            (aft (approx n (Later.force l) envP) (inv-approx n (Later.force l) envP gP) p okP)
            (aft (approx n (elab ρ (Later.force l)) envE) (inv-approx n (elab ρ (Later.force l)) envE gE) p′ okE) c
      where
        module O = OneUnder hm fr m₀ pp

        wi′ : Within (Hots envP) M₀ M p
        wi′ m with wi m
        ... | inj₁ m₁ = O.within m₁
        ... | inj₂ w  = inj₂ (inW (nest-in (step here plain-ix) w))

------------------------------------------------------------------------
-- The limit

-- THE MEANING is the approximants' limit.
--
-- DEAD ROUTE: the limit from the approximants' carries alone.  Each
--   approximant's carry picks its own map and image, existentially; a row
--   of the meaning is a row of every approximant from some index on, but
--   nothing makes their images of it agree from one index to the next, so
--   no image is eventually constant, and the meaning's must be one
--   relation, functional and monotone across rows carried at different
--   indices.  Bounding instead each carry by depth fails at a scan, whose
--   row reads every row before it, at any depth.
-- DEAD ROUTE: images made coherent and nothing more.  An elaborated row is
--   a row of the meaning only where the elaborated approximants agree,
--   and an image's agreement is bounded by no hypothesis here: the
--   elaborated run adds rows (marks, readers' joins) a plain cover does
--   not count.  The bookkeeping (`fib`, `bk`, `pbk`) is one function per
--   approximant, and a cause is read off a row of the meaning at the
--   index its own limit names, so those must cohere across indices too.
--   An image is not fixed by the fields either: a plain skip may sit on
--   any unshown elaborated row of its instant.
postulate
  carry-lim : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A)
            → (∀ n → Carry (just n) ρ (defer l)) → Carry nothing ρ (defer l)
