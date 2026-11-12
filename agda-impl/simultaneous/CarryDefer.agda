{-# OPTIONS --guardedness #-}

-- A `defer` IS CARRIED THROUGH ITS APPROXIMANTS.  The bottom one spins
-- skips one label under each subscription, each carried by its fellow;
-- each further one is the body under the guard.  The meaning is never
-- carried: the erasure reaches it from the approximants' per-row facts.
module simultaneous.CarryDefer where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; applyUpTo; filter)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-applyUpTo⁺; ∈-applyUpTo⁻; ∈-filter⁺; ∈-filter⁻; ∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_; ¬?; yes; no)

open import Tree using (Later; defer)
open import denotation.Position using (Pos; ix; _⊕_; root; _≟ᵖ_; _<ᵖ_)
open import Data.Bool.Properties using (T?)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; skip; end; pin; Unpinned; EmissionSet; Truncate; Reach; Few; Spin; spin; _≺_; _≼_; Den; enter;
  DenEnv; approx; DeferT; guard; body)
open import denotation.Laws.Modulus using (≺-irrefl; ≺→≼; ≺-≼-≺; ticks; entered-reach; ≺-ext)
open import denotation.Laws.Cut using (ix-asc; ix-back)
open import denotation.Laws.Worlds using (plain-ix; _⊑_; ⊑-refl; Hots; GoodEnv; Ok; ok-step; here; inW; step; nest-in; not-up; sib; W⁼;
  leads; ⊑-snoc; ⊑-≼; shrink⁼)
open import denotation.Laws using (aft; inv-approx)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.Attribution using (Live; Shown; Match; Every; One; Reads)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Listing using (Listed)
open import simultaneous.CarryBase using (PMap; _⊆ᴹ_; Emb; Fresh; CarryAt; Targeted; Home; Near; Whole; From; instant-⊕; IntoAt; Ahead)
open import simultaneous.Carry using (Clear; clear-not; Rows; rows-map; Within; Bare; Carry; carry; EnvRel; Bound; HotsListed; NotHot; Grown; Joins; joins-grow; Apart; EnvPast; PBNest; Nests; anchor-grow; nest-via; grown-past; env-past; CarriesAt)
open import simultaneous.CarryLeaves using (module OneUnder)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; annotate)

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
module SpinCarry {A : Set} {HP HE LP : Pos → Set} {M₀ : PMap} {p p₀ p′ : Pos}
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

  img : ∀ {k e} → t k e → Σ Pos λ l → Img k l × Σ (Ev (IE A)) λ e′ → u l e′ × Listed u l × Match Every (One valuesOf) (Reads valuesOf) e e′
  img (spin i , r) =
    p′ ⊕ [ ix i ] , ((ix i , plain-ix , refl , refl) , skip , spin i , r) , skip , (spin i , P′.reach i) , P′.listed i , (λ ()) , λ _ ()

  -- An elaborated skip is the plain one's, put under.
  up-in : ∀ {ks j} → p ⊕ [ ix j ] ∈ ks → p′ ⊕ [ ix j ] ∈ L.map up ks
  up-in {j = j} m = subst (_∈ L.map up _) (up-⊕ [ ix j ]) (∈-map⁺ up m)

  -- Before a point its carriers follow, the elaborated skips are those
  -- of the plain ones before the point they follow.
  cover : ∀ {v w} → Listed t v → From Img (λ _ _ → ⊥) t u v w → Listed u w
  cover {v} {w} (ks , Fk , Bk) Fr = filter (λ l → T? (l <ᵖ w)) (L.map up ks) , cov , back
    where
      cov : ∀ {l e} → u l e → l ≺ w → l ∈ filter (λ l → T? (l <ᵖ w)) (L.map up ks)
      cov (spin j , r) lw with T? ((p ⊕ [ ix j ]) <ᵖ v)
      ... | yes jv = ∈-filter⁺ (λ l → T? (l <ᵖ w)) (up-in (Fk (spin j , P.reach j) jv)) lw
      ... | no nj  = ⊥-elim (Fr (spin j , P.reach j) (λ { (() , _) }) nj (inj₁ (proj₁ (proj₂ (img (spin j , P.reach j))))) (spin j , r) lw)

      back : ∀ {l} → l ∈ filter (λ l → T? (l <ᵖ w)) (L.map up ks) → l ≺ w × Σ (Ev (IE A)) (u l)
      back m with ∈-filter⁻ (λ l → T? (l <ᵖ w)) {xs = L.map up ks} m
      ... | m′ , lw with ∈-map⁻ up m′
      ...   | k , mk , refl with Bk mk
      ...     | _ , _ , (spin j , _) = lw , skip , subst (λ y → u y skip) (sym (up-⊕ [ ix j ])) (spin j , P′.reach j)

  whole : Whole t → Whole u
  whole (ks , F , Bk) = L.map up ks , (λ { (spin j , _) → up-in (F (spin j , P.reach j)) }) , back
    where
      back : ∀ {x} → x ∈ L.map up ks → Σ (Ev (IE A)) (u x)
      back m with ∈-map⁻ up m
      ... | k , mk , refl with Bk mk
      ...   | _ , (spin j , _) = skip , subst (λ y → u y skip) (sym (up-⊕ [ ix j ])) (spin j , P′.reach j)

  carried : CarryAt valuesOf M HP HE LP t u p p′
  carried = record
    { Img     = Img
    ; ext     = λ { (n , _) → _ , inj₂ n , ⊑-refl _ }
    ; img     = λ tk _ _ _ _ → inj₁ (img tk)
    ; img¬¬   = λ tk _ _ _ n → let (l , i , e′ , ul , _ , m) = img tk in n (inj₁ (l , i , e′ , ul , m))
    ; shown   = λ { (spin _ , _) () }
    ; img-row = λ { (_ , _ , spin i , r) n → n (skip , (spin i , r) , tt) }
    ; img-fun = λ { (n , _) (n′ , _) → Emb.fun embN n n′ }
    ; place   = λ { (spin i , _) _ _ → inj₁ (instant-⊕ p′ [ ix i ]) }
    ; live    = λ _ _ → λ { (() , _) }
    ; few     = λ { (_ , _ , spin i , _) → P.rows i , λ x kq → P.before i (proj₁ x) kq }
    ; whole   = λ wt _ _ → whole wt
    ; cover   = λ L _ _ F → cover L F
    ; bk      = λ l → [ down l ]
    ; in-bk   = λ { ((a , _ , refl , refl) , _) → here (sym (down-⊕ [ a ])) }
    ; PB      = λ _ _ → ⊥
    ; pb-few  = λ _ → [] , λ ()
    ; pb-img  = λ ()
    ; pb-past = λ ()
    ; pinned  = λ { (() , _) _ _ }
    }

-- THE BOTTOM APPROXIMANT shows only skips: the spin, on both sides.
carry-⊥ : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A) → Carry zero ρ (defer l)
carry-⊥ {A = A} ρ l = carry λ envP envE _ _ M₀ e₀ er jn _ _ p p′ m₀ _ _ nh fr →
  let (M , ms , hm , wi , br , gr , c) = spun e₀ fr m₀ (⊑-refl p′) (clear-not nh)
  in M , ms , hm , wi , br , joins-grow {ρ = ρ} {envP = envP} {envE = envE} {er = er} {M = M₀} {N = M} (λ {x} {y} → ms {x} {y}) jn (λ {x} {y} → gr {x} {y})
     , grown-past {ρ = ρ} {envP = envP} {envE = envE} er (env-past er) (λ {x} {y} → gr {x} {y}) , c , λ _ ()
  where
    spun : ∀ {HP HE LP R M₀ p p₀ p′} → Emb M₀ → Fresh HP M₀ p → M₀ p p₀ → p₀ ⊑ p′ → NotHot R p
         → Σ PMap λ M → M₀ ⊆ᴹ M × Emb M × Within HP M₀ M p × Bare M (Truncate (Spin {A} p))
           × (∀ {x y} → M x y → M₀ x y ⊎ Grown M₀ R x y) × CarryAt valuesOf M HP HE LP (Truncate (Spin {A} p)) (Truncate (Spin {IE A} p′)) p p′
    spun {HP} {HE} {LP} {p = p} E₀ fr m₀ pp nh =
      O.M , inj₁ , O.emb , O.within , O.bare {t = Truncate (Spin {A} p)} (λ { (spin i , _) → ix i , plain-ix , refl }) , O.grown nh , X.carried
      where module X = SpinCarry {A} {HP} {HE} {LP} E₀ fr m₀ pp
            module O = OneUnder E₀ fr m₀ pp

------------------------------------------------------------------------
-- A grown map

-- A CARRY STAYS ONE along a larger map: the map is read where a row is
-- put under its image, and where a row carried into its instant is put
-- past the image of what lies before it, which the larger map keeps.
carry-grow : ∀ {A Y} {f : Y → List A} {M M′ : PMap} {HP HE LP : Pos → Set} {t : EmissionSet A} {u : EmissionSet Y} {s s′ : Pos}
           → M ⊆ᴹ M′ → (c : CarryAt f M HP HE LP t u s s′)
           → (∀ {k l e₀ e x y} → CarryAt.PB c k l → t k e₀ → (Unpinned e₀ → Live t k) → u l e → M′ x y → x ≺ k → ¬ (x ⊑ k) → Ahead y l)
           → CarryAt f M′ HP HE LP t u s s′
carry-grow sub c past = record
  { Img = Img ; ext = λ i → let (y , m , yl) = ext i in y , sub m , yl ; img = img ; img¬¬ = img¬¬ ; shown = shown ; img-row = img-row
  ; img-fun = img-fun ; place = place ; live = live ; few = few ; whole = whole ; cover = cover
  ; bk = bk ; in-bk = in-bk ; PB = PB ; pb-few = pb-few ; pb-img = pb-img ; pb-past = past ; pinned = pinned′ }
  where
    open CarryAt c
    pinned′ = λ {k} {q} tk L lp → let ((l , q′ , ul , pb , (y , m , qy) , ls) , h) = pinned {k} {q} tk L lp in (l , q′ , ul , pb , (y , sub m , qy) , ls) , h

-- AN ENVIRONMENT STAYS ONE along a map grown past its binders' late
-- carriers.
env-grow : ∀ {Γ Δ} {M M′ : PMap} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {envP : DenEnv Γ} {envE : DenEnv Δ}
         → M ⊆ᴹ M′ → (er : EnvRel M ρ envP envE) → EnvPast er M′ → EnvRel M′ ρ envP envE
env-grow sub er past i = record { m = m ; src = src ; σ = σ ; envP = envP ; envE = envE ; at = at ; at′ = at′
                                ; lists = lists ; carried = carry-grow sub carried (past i) ; invP = invP ; invE = invE ; isP = isP ; isE = isE }
  where
    open Bound (er i)

-- The anchors kept, the map grown so.
nests-grow : ∀ {Γ Δ} {M M′ : PMap} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {envP : DenEnv Γ} {envE : DenEnv Δ}
           → (sub : M ⊆ᴹ M′) (er : EnvRel M ρ envP envE) (past : EnvPast er M′) → Nests er M
           → Nests (env-grow {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} sub er past) M′
nests-grow sub er past ns j i pb tk lv br ci e = anchor-grow sub (ns j i pb tk lv br ci e)

-- What holds of the grown environment's carriers holds of the original's:
-- growing keeps each carrier's rows and their pairing.
past-shrink : ∀ {Γ Δ} {M M′ N : PMap} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {envP : DenEnv Γ} {envE : DenEnv Δ}
            → (sub : M ⊆ᴹ M′) (er : EnvRel M ρ envP envE) (past : EnvPast er M′)
            → EnvPast (env-grow {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} sub er past) N → EnvPast er N
past-shrink sub er past ep i = ep i

nest-shrink : ∀ {Γ Δ} {M M′ N : PMap} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {envP : DenEnv Γ} {envE : DenEnv Δ}
              {A Y} {f : Y → List A} {M₁ : PMap} {HP HE LP : Pos → Set} {t : EmissionSet A} {u : EmissionSet Y} {s s′ : Pos}
              {c : CarryAt f M₁ HP HE LP t u s s′}
            → (sub : M ⊆ᴹ M′) (er : EnvRel M ρ envP envE) (past : EnvPast er M′)
            → PBNest (env-grow {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} sub er past) N c → PBNest er N c
nest-shrink sub er past nc i = nc i

nest-up : ∀ {Γ Δ} {M M′ N : PMap} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {envP : DenEnv Γ} {envE : DenEnv Δ}
          {A Y} {f : Y → List A} {M₁ : PMap} {HP HE LP : Pos → Set} {t : EmissionSet A} {u : EmissionSet Y} {s s′ : Pos}
          {c : CarryAt f M₁ HP HE LP t u s s′}
        → (sub : M ⊆ᴹ M′) (er : EnvRel M ρ envP envE) (past : EnvPast er M′)
        → PBNest er N c → PBNest (env-grow {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} sub er past) N c
nest-up sub er past nc i = nc i

joins-up : ∀ {Γ Δ} {M M′ N : PMap} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {envP : DenEnv Γ} {envE : DenEnv Δ}
         → (sub : M ⊆ᴹ M′) (er : EnvRel M ρ envP envE) (past : EnvPast er M′)
         → Joins (λ {X} → ρ {X}) envP envE er N → Joins (λ {X} → ρ {X}) envP envE (env-grow {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} sub er past) N
joins-up sub er past jn i = jn i

joins-shrink : ∀ {Γ Δ} {M M′ N : PMap} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {envP : DenEnv Γ} {envE : DenEnv Δ}
             → (sub : M ⊆ᴹ M′) (er : EnvRel M ρ envP envE) (past : EnvPast er M′)
             → Joins (λ {X} → ρ {X}) envP envE (env-grow {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} sub er past) N → Joins (λ {X} → ρ {X}) envP envE er N
joins-shrink sub er past jn i = jn i

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

  whole← : Whole T → Whole B
  whole← (ks , F , Bk) = filter (λ y → ¬? (y ≟ᵖ g)) ks , (λ x → ∈-filter⁺ (λ y → ¬? (y ≟ᵖ g)) (F (up x)) (λ { refl → ¬g x })) , back
    where
      back : ∀ {k′} → k′ ∈ filter (λ y → ¬? (y ≟ᵖ g)) ks → Σ (Ev X) (B k′)
      back m with ∈-filter⁻ (λ y → ¬? (y ≟ᵖ g)) m
      ... | n , ne with Bk n
      ...   | _ , (guard , _)  = ⊥-elim (ne refl)
      ...   | e , (body x , _) = e , x

  lst→ : ∀ {k e} → B k e → Listed B k → Listed T k
  lst→ x (ks , F , Bk) = g ∷ ks , (λ { (guard , _) _ → here refl ; (body x′ , _) kq → there (F x′ kq) })
                       , λ { (here refl) → gb x , skip , gT ; (there m) → let (kq , e , x′) = Bk m in kq , e , up x′ }

  -- Listed before any point: the guard, when before it, and the body.
  lstw : ∀ {w} → Listed B w → Listed T w
  lstw {w} (ks , F , Bk) with T? (g <ᵖ w)
  ... | yes gw = g ∷ ks , (λ { (guard , _) _ → here refl ; (body x , _) kq → there (F x kq) })
               , λ { (here refl) → gw , skip , gT ; (there m) → let (kq , e , x) = Bk m in kq , e , up x }
  ... | no ngw = ks , (λ { (guard , _) kq → ⊥-elim (ngw kq) ; (body x , _) kq → F x kq })
               , λ m → let (kq , e , x) = Bk m in kq , e , up x

  near→ : ∀ {m l} → Near B m l → Near T m l
  near→ (inj₁ lm)           = inj₁ lm
  near→ (inj₂ ((e , x) , L)) = inj₂ ((e , up x) , lst→ x L)

-- THE GUARD CARRIES THE GUARD and the body carries the body: a carry of
-- the body under each guard is one of the whole.
module NextCarry {A : Set} {HP HE LP : Pos → Set} {M : PMap} (s : Den A) (s′ : Den (IE A)) (p p′ : Pos)
  (mg : M (p ⊕ [ ix 0 ]) (p′ ⊕ [ ix 0 ]))
  (aP : ∀ {y e} → enter s (p ⊕ [ ix 1 ]) y e → (p ⊕ [ ix 1 ]) ≼ y × (∀ {r} → e ≡ pin r → (p ⊕ [ ix 1 ]) ≼ r))
  (aE : ∀ {y e} → enter s′ (p′ ⊕ [ ix 1 ]) y e → (p′ ⊕ [ ix 1 ]) ≼ y × (∀ {r} → e ≡ pin r → (p′ ⊕ [ ix 1 ]) ≼ r))
  (c : CarryAt valuesOf M HP HE LP (enter s (p ⊕ [ ix 1 ])) (enter s′ (p′ ⊕ [ ix 1 ])) (p ⊕ [ ix 1 ]) (p′ ⊕ [ ix 1 ])) where
  private
    module P = Side s p aP
    module E = Side s′ p′ aE
    module C = CarryAt c

  Img : Pos → Pos → Set
  Img k l = (k ≡ P.g × l ≡ E.g) ⊎ C.Img k l

  ext : ∀ {k l} → Img k l → Σ Pos λ y → M k y × y ⊑ l
  ext (inj₁ (refl , refl)) = E.g , mg , ⊑-refl E.g
  ext (inj₂ i)             = C.ext i

  -- What the body puts into its instant, of its rows on its own rows.
  PB : Pos → Pos → Set
  PB k l = Σ (Ev (IE A)) (E.B l) × Σ (Ev A) (P.B k) × C.PB k l

  pb-few : ∀ {l e} → E.T l e → Σ (List Pos) λ ks → ∀ {k} → PB k l → k ∈ ks
  pb-few (guard , _)  = [] , λ { ((_ , y) , _) → ⊥-elim (E.¬g y) }
  pb-few (body y , _) = proj₁ (C.pb-few y) , λ { (_ , _ , m) → proj₂ (C.pb-few y) m }

  pb-img : ∀ {k l l′} → PB k l → Img k l′ → ⊥
  pb-img (_ , (_ , x) , _) (inj₁ (refl , refl)) = P.¬g x
  pb-img (_ , _ , m)       (inj₂ i)             = C.pb-img m i

  pb-past : ∀ {k l e₀ e x y} → PB k l → P.T k e₀ → (Unpinned e₀ → Live P.T k) → E.T l e → M x y → x ≺ k → ¬ (x ⊑ k) → Ahead y l
  pb-past (_ , (_ , x) , _) (guard , _)    _  _ = ⊥-elim (P.¬g x)
  pb-past ((_ , y) , _ , m) (body x₀ , _) lv _ = C.pb-past m x₀ (λ un → P.live← (lv un)) y

  pb-down : ∀ {k l e₀} → PB k l → P.T k e₀ → (Unpinned e₀ → Live P.T k)
          → C.PB k l × Σ (Ev A) λ e → enter s (p ⊕ [ ix 1 ]) k e × (Unpinned e → Live (enter s (p ⊕ [ ix 1 ])) k)
  pb-down (_ , (_ , x) , _) (guard , _)    _  = ⊥-elim (P.¬g x)
  pb-down (_ , _ , m)       (body x₀ , _) lv = m , _ , x₀ , λ un → P.live← (lv un)

  into : ∀ {k e₀} → P.B k e₀ → IntoAt C.Img (enter s′ (p′ ⊕ [ ix 1 ])) C.PB HP (p ⊕ [ ix 1 ]) k → IntoAt Img E.T PB HP p k
  into x ((l , (e , ul) , L , m) , h) = (l , (e , E.up ul) , E.lst→ ul L , ((e , ul) , (_ , x) , m)) , at h
    where
      at : _ → _
      at (inj₁ e)                                             = inj₁ (trans e (instant-⊕ p [ ix 1 ]))
      at (inj₂ (inj₁ (k₀ , l₀ , i , kk , e , (e₀ , ul₀) , L))) = inj₂ (inj₁ (k₀ , l₀ , inj₂ i , kk , e , (e₀ , E.up ul₀) , E.lst→ ul₀ L))
      at (inj₂ (inj₂ h))                                      = inj₂ (inj₂ h)

  img : ∀ {k e} → P.T k e → Unpinned e → Live P.T k → Listed P.T k → LP k
      → (Σ Pos λ l → Img k l × Σ (Ev (IE A)) λ e′ → E.T l e′ × Listed E.T l × Match Every (One valuesOf) (Reads valuesOf) e e′)
        ⊎ (e ≡ skip × IntoAt Img E.T PB HP p k)
  img (guard , _) _ _ _ _ = inj₁ (E.g , inj₁ (refl , refl) , skip , E.gT , ([] , (λ x lt → ⊥-elim (E.none x lt)) , λ ()) , (λ ()) , λ _ ())
  img (body x , _) un lv ls lp with C.img x un (P.live← lv) (P.lst← ls) lp
  ... | inj₁ (l , i , e′ , ul , lu , m) = inj₁ (l , inj₂ i , e′ , E.up ul , E.lst→ ul lu , m)
  ... | inj₂ (es , h)                   = inj₂ (es , into x h)

  img¬¬ : ∀ {k e} → P.T k e → Unpinned e → Live P.T k → Few P.T k
        → ¬ ¬ ((Σ Pos λ l → Img k l × Σ (Ev (IE A)) λ e′ → E.T l e′ × Match Every (One valuesOf) (Reads valuesOf) e e′) ⊎ e ≡ skip)
  img¬¬ (guard , _) _ _ _ n = n (inj₁ (E.g , inj₁ (refl , refl) , skip , E.gT , (λ ()) , λ _ ()))
  img¬¬ (body x , _) un lv fw n =
    C.img¬¬ x un (P.live← lv) (P.few← fw) λ { (inj₁ (l , i , e′ , ul , m)) → n (inj₁ (l , inj₂ i , e′ , E.up ul , m))
                                             ; (inj₂ es) → n (inj₂ es) }

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

  place : ∀ {m e} → E.T m e → Live E.T m → Listed E.T m
        → instantOf m ≡ instantOf p′ ⊎ (Σ Pos λ k → Σ Pos λ l → Img k l × instantOf l ≡ instantOf m × Near E.T m l)
          ⊎ Σ Pos λ h → HE h × instantOf h ≡ instantOf m
  place (guard , _) _ _ = inj₁ (instant-⊕ p′ [ ix 0 ])
  place {m} (body y , _) lv lm with C.place y (E.live← lv) (E.lst← lm)
  ... | inj₁ e                             = inj₁ (trans e (instant-⊕ p′ [ ix 1 ]))
  ... | inj₂ (inj₁ (k , l , i , e , n)) = inj₂ (inj₁ (k , l , inj₂ i , e , E.near→ {m} {l} n))
  ... | inj₂ (inj₂ h)                       = inj₂ (inj₂ h)

  live : ∀ {k l} → Img k l → Live P.T k → Live E.T l
  live (inj₁ (refl , refl)) _  (body {y} x , _) = ≺→≼ {E.g} {y} (E.gb x)
  live (inj₂ i)             lv x                = E.live→ (C.live i (P.live← lv)) x

  few : ∀ {k l} → Img k l → Few P.T k
  few (inj₁ (refl , refl)) = [] , λ x lt → ⊥-elim (P.none x lt)
  few (inj₂ i)             = P.few→ (C.few i)

  whole : Whole P.T → (∀ {c} → P.T c end → ⊥) → (∀ {q} → LP q) → Whole E.T
  whole wt ne lp with C.whole (P.whole← wt) (λ x → ne (P.up x)) lp
  ... | ls , F , Bk = E.g ∷ ls , (λ { (guard , _) → here refl ; (body y , _) → there (F y) })
                    , λ { (here refl) → skip , E.gT ; (there m) → let (e , y) = Bk m in e , E.up y }

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

  pinned : ∀ {k q} → P.T k (pin q) → Listed P.T k → LP k
         → (Σ Pos λ l → Σ Pos λ q′ → E.T l (pin q′) × PB k l × Targeted M q q′ × Listed E.T l)
           × (instantOf k ≡ instantOf p ⊎ (Σ Pos λ k₀ → k₀ ≺ q × Home P.T k₀ × instantOf k₀ ≡ instantOf k)
              ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)
  pinned {k} {q} (body x , _) L lp with C.pinned x (P.lst← L) lp
  ... | (l , q′ , ul , m , b , ls) , r = (l , q′ , E.up ul , ((pin q′ , ul) , (_ , x) , m) , b , E.lst→ ul ls) , homed {k} {q} r

  cover : ∀ {v w} → Listed P.T v → LP v → Live P.T v → From Img PB P.T E.T v w → Listed E.T w
  cover L lp lv F = E.lstw (C.cover (P.lst← L) lp (P.live← lv) λ tk lk vk m ul → F (P.up tk) (P.live→ lk) vk (fwd m tk ul) (E.up ul))
    where
      fwd : ∀ {k l e e′} → C.Img k l ⊎ C.PB k l → P.B k e → E.B l e′ → Img k l ⊎ PB k l
      fwd (inj₁ i)  _  _  = inj₁ (inj₂ i)
      fwd (inj₂ pb) tk ul = inj₂ ((_ , ul) , (_ , tk) , pb)

  carried : CarryAt valuesOf M HP HE LP P.T E.T p p′
  carried = record
    { Img = Img ; ext = ext ; img = img ; img¬¬ = img¬¬ ; shown = shown ; img-row = img-row ; img-fun = img-fun ; place = place
    ; live = live ; few = few ; whole = whole ; cover = cover
    ; bk = bk ; in-bk = in-bk ; PB = PB ; pb-few = pb-few ; pb-img = pb-img ; pb-past = pb-past ; pinned = pinned }

-- EACH FURTHER APPROXIMANT is the body under the guard: the map grown by
-- the guard and the body's subscription, held fresh at the body's.
carry-next : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A)
           → Carry n ρ (Later.force l) → Carry (suc n) ρ (defer l)
carry-next n {Γ} {Δ} {A} ρ l (carry h) = carry λ envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr →
  nexted envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr
  where
    nexted : ∀ (envP : DenEnv Γ) (envE : DenEnv Δ) → GoodEnv envP → GoodEnv envE → ∀ M₀ → Emb M₀ → (er : EnvRel M₀ ρ envP envE)
           → Joins ρ envP envE er M₀ → Nests er M₀ → Apart envP → ∀ p p′ → M₀ p p′ → Ok (Hots envP) p → Ok (Hots envE) p′ → Clear (Rows er) (Hots envP) p
           → Fresh (Hots envP) M₀ p
           → Σ PMap λ M → M₀ ⊆ᴹ M × Emb M × Within (Hots envP) M₀ M p × Bare M (Truncate (DeferT (approx n (Later.force l) envP) p))
             × Joins ρ envP envE er M × EnvPast er M
             × Σ (CarryAt valuesOf M (Hots envP) (Hots envE) (HotsListed envP) (Truncate (DeferT (approx n (Later.force l) envP) p))
                   (Truncate (DeferT (approx n (elab ρ (Later.force l)) envE) p′)) p p′) (λ c → PBNest er M c)
    nexted envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr =
      finish (h envP envE gP gE O.M O.emb er₁ jn₁ ns₁ ap (p ⊕ [ ix 1 ]) (p′ ⊕ [ ix 1 ])
             (inj₂ (ix 1 , plain-ix , refl , refl)) (ok-step p okP) (ok-step p′ okE) (λ hq w i → nh (rows-map er er₁ (λ _ x → x) hq) (inW (shrink⁼ w)) i) fresh₁)
      where
        module O = OneUnder hm fr m₀ (⊑-refl p′)

        past₁ : EnvPast er O.M
        past₁ = grown-past {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} er (env-past er) (λ {x} {y} → O.grown (clear-not nh) {x} {y})

        er₁ : EnvRel O.M ρ envP envE
        er₁ = env-grow {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} inj₁ er past₁

        ns₁ : Nests er₁ O.M
        ns₁ = nests-grow {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} inj₁ er past₁ ns

        jn₁ : Joins ρ envP envE er₁ O.M
        jn₁ = joins-grow {ρ = ρ} {envP = envP} {envE = envE} {er = er₁} {M = M₀} {N = O.M} inj₁ (λ i → jn i) (λ {x} {y} → O.grown (λ hq → clear-not nh (rows-map er er₁ (λ _ x → x) hq)) {x} {y})

        fresh₁ : Fresh (Hots envP) O.M (p ⊕ [ ix 1 ])
        fresh₁ (inj₁ m) (w , ww , wx) with fr m (w , inW (nest-in (step here plain-ix) ww) , wx)
        ... | refl = ⊥-elim (not-up (proj₁ okP) ww wx)
        fresh₁ (inj₂ (a , pl , refl , _)) (w , ww , wx) with (p ⊕ [ a ]) ≟ᵖ (p ⊕ [ ix 1 ])
        ... | yes e = e
        ... | no ne = ⊥-elim (sib (proj₁ okP) pl (⊑-refl p) ne ww wx)

        finish : CarriesAt n ρ (Later.force l) envP envE O.M er₁ (p ⊕ [ ix 1 ]) (p′ ⊕ [ ix 1 ])
               → Σ PMap λ M → M₀ ⊆ᴹ M × Emb M × Within (Hots envP) M₀ M p × Bare M (Truncate (DeferT (approx n (Later.force l) envP) p))
                 × Joins ρ envP envE er M × EnvPast er M
                 × Σ (CarryAt valuesOf M (Hots envP) (Hots envE) (HotsListed envP) (Truncate (DeferT (approx n (Later.force l) envP) p))
                       (Truncate (DeferT (approx n (elab ρ (Later.force l)) envE) p′)) p p′) (λ c → PBNest er M c)
        finish (M , ms , hm′ , wi , br , jn′ , ep , c , nc) =
          M , (λ m → ms (inj₁ m)) , hm′ , wi′ , bare , (λ i → jn′ i) , past-shrink {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} inj₁ er past₁ ep
            , NC.carried
            , nest-via {er = er} {c = c} {c′ = NC.carried} (λ m → m) (λ {k} {l} {e₀} → NC.pb-down {k} {l} {e₀})
                (nest-shrink {ρ = λ {X} → ρ {X}} {envP = envP} {envE = envE} {c = c} inj₁ er past₁ nc)
          where
           module NC = NextCarry (approx n (Later.force l) envP) (approx n (elab ρ (Later.force l)) envE) p p′
               (ms (inj₂ (ix 0 , plain-ix , refl , refl)))
               (aft (approx n (Later.force l) envP) (inv-approx n (Later.force l) envP gP) p okP)
               (aft (approx n (elab ρ (Later.force l)) envE) (inv-approx n (elab ρ (Later.force l)) envE gE) p′ okE) c

           g : Pos
           g = p ⊕ [ ix 0 ]

           g≢ : g ≡ p ⊕ [ ix 1 ] → ⊥
           g≢ e = ≺-irrefl {g} (subst (g ≺_) (sym e) (ticks p 0))

           -- Nothing the body's map adds lies under the guard.
           g-bare : ∀ {x y} → M x y → g ⊑ x → x ≡ g
           g-bare m gx with wi m
           ... | inj₁ m₁ = O.bare {X = A} {t = λ k _ → k ≡ g} (λ { refl → ix 0 , plain-ix , refl }) {e = skip} refl m₁ gx
           ... | inj₂ w  = ⊥-elim (leads (proj₂ okP) (step here plain-ix) nb nr w gx)
             where
               nb : W⁼ (Hots envP) (p ⊕ [ ix 1 ]) g → ⊥
               nb ww = sib (proj₁ okP) plain-ix (⊑-refl p) g≢ ww (⊑-refl g)

               nr : g ⊑ (p ⊕ [ ix 1 ]) → ⊥
               nr r with ⊑-snoc p r
               ... | inj₁ gp = ⊑-≼ gp (≺-ext p [])
               ... | inj₂ e  = g≢ e

           bare : Bare M (Truncate (DeferT (approx n (Later.force l) envP) p))
           bare (guard , _)  m gx = g-bare m gx
           bare (body x , _) m kx = br x m kx

           wi′ : Within (Hots envP) M₀ M p
           wi′ m with wi m
           ... | inj₁ m₁ = O.within m₁
           ... | inj₂ w  = inj₂ (inW (nest-in (step here plain-ix) w))
