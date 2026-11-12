{-# OPTIONS --guardedness #-}

-- THE LEAVES CARRY: rows one label under each subscription (`of`, the
-- empty program).
module simultaneous.CarryLeaves where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; filter)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List.Properties using (++-assoc; ++-cancelˡ; ∷-injectiveˡ)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Bool.Properties using (T?)
open import denotation.Position using (_<ᵖ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Bool using (T)
open import Function using (mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Tree using (empty; of; map)
open import denotation.Position using (_≟ᵖ_; Pos; Path; Label; ix; sub; last; _∙_; _⊕_; root; cmpPath; cmpPos; isLt)
open import denotation.Simultaneity using (reflˡ; reflⁱ)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Few; _≺_; Truncate; Reach; InE; at-end;
  at-out; on-out)
import denotation.Events as Evs
open import denotation.Events using (Timeline; fresh)
open import simultaneous.HeldMap using (mapEv)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-ext)
open import denotation.Laws.Worlds using (here; inW; step; Plain; plain-ix; plain-last; _⊑_; ⊕-identityʳ; ⊑-refl; ⊑-≼; ⊑-trans; ⊑-snoc⁺)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.InstEmit using (valuesOf; instEmit; value)
open import simultaneous.Attribution using (Live; Shown; Match; Every; One; Reads)
open import simultaneous.Listing using (Listed)
open import denotation.Laws.Worlds.Leaves using (of-rows; of-in; of-row)
open import simultaneous.CarryBase using (CarryAt; Emb; Fresh; PMap; _∪ᴹ_; _⊆ᴹ_; emb-under; instant-⊕)
open import simultaneous.Carry using (Bare; Carry; Within; carry; NotHot; Grown; joins-grow; grown-past; env-past)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; annotate; mapIE; elaborate)

-- Positions one label under a common prefix.
private
  path-under : ∀ ps σ τ → cmpPath (ps ++ σ) (ps ++ τ) ≡ cmpPath σ τ
  path-under []       σ τ = refl
  path-under (a ∷ ps) σ τ rewrite reflˡ a = path-under ps σ τ

  cmp-under : ∀ q σ τ → cmpPos (q ⊕ σ) (q ⊕ τ) ≡ cmpPath σ τ
  cmp-under (i ∙ ps) σ τ rewrite reflⁱ i = path-under ps σ τ

  ≺-shift : ∀ q q′ σ τ → (q ⊕ σ) ≺ (q ⊕ τ) → (q′ ⊕ σ) ≺ (q′ ⊕ τ)
  ≺-shift q q′ σ τ h = subst (λ c → T (isLt c)) (trans (cmp-under q σ τ) (sym (cmp-under q′ σ τ))) h

  path-of : Pos → Path
  path-of (_ ∙ ps) = ps

  ⊑-one : ∀ q {a b} → (q ⊕ [ a ]) ⊑ (q ⊕ [ b ]) → b ≡ a
  ⊑-one (i ∙ ps) {a} {b} (zs , e) = ∷-injectiveˡ (++-cancelˡ ps [ b ] (a ∷ zs) (trans (cong path-of e) (++-assoc ps [ a ] zs)))

  drop-len : ∀ (ps σ : Path) → L.drop (L.length ps) (ps ++ σ) ≡ σ
  drop-len []       σ = refl
  drop-len (_ ∷ ps) σ = drop-len ps σ

  drop-under : ∀ q σ → L.drop (L.length (path-of q)) (path-of (q ⊕ σ)) ≡ σ
  drop-under (i ∙ ps) σ = drop-len ps σ

-- Each plain label under one position, put on the same label under another.
module OneAt (p p′ : Pos) where
  N : PMap
  N x y = Σ Label λ a → Plain a × x ≡ p ⊕ [ a ] × y ≡ p′ ⊕ [ a ]

  embN : Emb N
  embN = record
    { fun     = λ { (a , _ , refl , refl) (b , _ , e , refl) →
                    cong (λ c → p′ ⊕ [ c ]) (⊑-one p ([] , trans e (sym (⊕-identityʳ (p ⊕ [ b ]))))) }
    ; mono    = λ { (a , _ , refl , refl) (b , _ , refl , refl) h → ≺-shift p p′ [ a ] [ b ] h }
    ; reflect = λ { (a , _ , refl , refl) (b , _ , refl , refl) h → subst (λ c → (p ⊕ [ a ]) ⊑ (p ⊕ [ c ])) (sym (⊑-one p′ h)) (⊑-refl (p ⊕ [ a ])) }
    ; inst    = λ { (a , _ , refl , refl) (b , _ , refl , refl) →
                    mk⇔ (λ _ → trans (instant-⊕ p [ a ]) (sym (instant-⊕ p [ b ])))
                        (λ _ → trans (instant-⊕ p′ [ a ]) (sym (instant-⊕ p′ [ b ]))) } }

-- ONE LABEL UNDER EACH SUBSCRIPTION: a map held fresh grown by each
-- plain label under the plain subscription, put on the same label under
-- the elaborated one.
module OneUnder {HP : Pos → Set} {M₀ : PMap} {p p₀ p′ : Pos}
                (E₀ : Emb M₀) (fr : Fresh HP M₀ p) (m₀ : M₀ p p₀) (pp : p₀ ⊑ p′) where
  open OneAt p p′ public

  M : PMap
  M = M₀ ∪ᴹ N

  emb : Emb M
  emb = emb-under {N = N} E₀ fr m₀ pp embN λ { (a , _ , refl , refl) → a , [] , a , [] , refl , refl }

  within : Within HP M₀ M p
  within (inj₁ m)                  = inj₁ m
  within (inj₂ (_ , pl , refl , _)) = inj₂ (inW (step here pl))

  -- Its points lie one label under the subscription, holding no hot row.
  grown : NotHot HP p → ∀ {x y} → M x y → M₀ x y ⊎ Grown M₀ HP x y
  grown _  (inj₁ m)                  = inj₁ m
  grown nh (inj₂ (a , _ , refl , refl)) = inj₂ (p , p₀ , a , m₀ , ⊑-trans pp (⊑-snoc⁺ p′) , refl , nh)

  -- Rows one label under the subscription have nothing paired under them.
  bare : ∀ {X : Set} {t : EmissionSet X} → (∀ {k e} → t k e → Σ Label λ a → Plain a × k ≡ p ⊕ [ a ]) → Bare M t
  bare sh tk (inj₁ m) kx with sh tk
  ... | a , pl , refl = ⊥-elim (⊑-≼ (subst ((p ⊕ [ a ]) ⊑_) (fr m (p ⊕ [ a ] , inW (step here pl) , kx)) kx) (≺-ext p []))
  bare sh tk (inj₂ (b , _ , refl , _)) kx with sh tk
  ... | a , pl , refl = cong (λ c → p ⊕ [ c ]) (⊑-one p kx)

  -- A position's path past one subscription, put under the other.
  up : Pos → Pos
  up k = p′ ⊕ L.drop (L.length (path-of p)) (path-of k)

  up-⊕ : ∀ σ → up (p ⊕ σ) ≡ p′ ⊕ σ
  up-⊕ σ = cong (p′ ⊕_) (drop-under p σ)

  down : Pos → Pos
  down l = p ⊕ L.drop (L.length (path-of p′)) (path-of l)

  down-⊕ : ∀ σ → down (p′ ⊕ σ) ≡ p ⊕ σ
  down-⊕ σ = cong (p ⊕_) (drop-under p′ σ)

-- An end one label under `q` comes after every row so labelled.
last-max : ∀ q {a} → Plain a → (q ⊕ [ last ]) ≺ (q ⊕ [ a ]) → ⊥
last-max q (plain-ix {i}) h = subst (λ c → T (isLt c)) (cmp-under q [ last ] [ ix i ]) h
last-max q plain-last     h = subst (λ c → T (isLt c)) (cmp-under q [ last ] [ last ]) h

ix-last : ∀ q → (q ⊕ [ ix 0 ]) ≺ (q ⊕ [ last ])
ix-last q = subst (λ c → T (isLt c)) (sym (cmp-under q [ ix 0 ] [ last ])) tt

-- A tick one label under `q` comes before every reading so labelled.
ix-sub : ∀ q e → (q ⊕ [ ix 0 ]) ≺ (q ⊕ [ sub e ])
ix-sub q e = subst (λ c → T (isLt c)) (sym (cmp-under q [ ix 0 ] [ sub e ])) tt

private
  unp-pin : ∀ {X : Set} {r} → Unpinned {X} (pin r) → ⊥
  unp-pin ()

  -- What an elaborated `of` emits for a value.
  V : ∀ {A : Set} → A → IE A
  V x = instEmit (value x) root

  -- A run with a complete list of its rows, each a row, is listed
  -- before every position.
  fin-listed : ∀ {X : Set} {t : EmissionSet X} (ks : List Pos) → (∀ {k e} → t k e → k ∈ ks) → (∀ {k} → k ∈ ks → Σ (Ev X) (t k))
             → ∀ q → Listed t q
  fin-listed ks F B q =
    filter (λ k → T? (k <ᵖ q)) ks
    , (λ tk kq → ∈-filter⁺ (λ k → T? (k <ᵖ q)) (F tk) kq)
    , λ m → let (n , kq) = ∈-filter⁻ (λ k → T? (k <ᵖ q)) m in kq , B n

  -- The rows of an `of`: one label under its subscription, finitely
  -- many, none pinned, the end last.
  of-unp : ∀ {A : Set} p i (xs : List A) {k e} → InE (Evs.ofᴱ p i xs) k e → Unpinned e
  of-unp p i []       at-end     = tt
  of-unp p i (x ∷ xs) at-out     = tt
  of-unp p i (x ∷ xs) (on-out r) = of-unp p (suc i) xs r

  of-end : ∀ {A : Set} p i (xs : List A) {c} → InE (Evs.ofᴱ p i xs) c end → c ≡ p ⊕ [ last ]
  of-end p i []       at-end     = refl
  of-end p i (x ∷ xs) (on-out r) = of-end p (suc i) xs r

  -- Each row of the plain `of`, and of the elaborated, has its fellow
  -- under the other subscription.
  of-up : ∀ {A : Set} p p′ i (xs : List A) {k e} → InE (Evs.ofᴱ p i xs) k e
        → Σ Label λ a → Plain a × k ≡ p ⊕ [ a ] × InE (Evs.ofᴱ p′ i (L.map V xs)) (p′ ⊕ [ a ]) (mapEv V e)
  of-up p p′ i []       at-end     = last , plain-last , refl , at-end
  of-up p p′ i (x ∷ xs) at-out     = ix i , plain-ix , refl , at-out
  of-up p p′ i (x ∷ xs) (on-out r) with of-up p p′ (suc i) xs r
  ... | a , pl , e , r′ = a , pl , e , on-out r′

  of-down : ∀ {A : Set} p p′ i (xs : List A) {l e′} → InE (Evs.ofᴱ p′ i (L.map V xs)) l e′
          → Σ Label λ a → Plain a × l ≡ p′ ⊕ [ a ] × Σ (Ev A) λ e → InE (Evs.ofᴱ p i xs) (p ⊕ [ a ]) e × e′ ≡ mapEv V e
  of-down p p′ i []       at-end     = last , plain-last , refl , end , at-end , refl
  of-down p p′ i (x ∷ xs) at-out     = ix i , plain-ix , refl , out x , at-out , refl
  of-down p p′ i (x ∷ xs) (on-out r) with of-down p p′ (suc i) xs r
  ... | a , pl , e , e₀ , r₀ , ee = a , pl , e , e₀ , on-out r₀ , ee

  match-V : ∀ {A : Set} (e : Ev A) → Match Every (One valuesOf) (Reads valuesOf) e (mapEv V e)
  match-V (out x) = (λ _ → V x , refl , refl) , λ ns → ⊥-elim (ns tt)
  match-V end     = (λ _ → refl) , λ ns → ⊥-elim (ns tt)
  match-V skip    = (λ ()) , λ _ ()
  match-V (pin _) = (λ ()) , λ _ ()

  -- The values listed, carried row for row one label under each side.
  module OfRows {A : Set} {HP HE LP : Pos → Set} {M₀ : PMap} {p p₀ p′ : Pos} (xs : List A)
                (E₀ : Emb M₀) (fr : Fresh HP M₀ p) (m₀ : M₀ p p₀) (pp : p₀ ⊑ p′) where
    open OneUnder E₀ fr m₀ pp using (N; embN; M; emb; within)

    t : EmissionSet A
    t = Truncate (InE (Evs.ofᴱ p 0 xs))

    u : EmissionSet (IE A)
    u = Truncate (InE (Evs.ofᴱ p′ 0 (L.map V xs)))

    allT : Σ (List Pos) λ ks → ∀ {k e} → InE (Evs.ofᴱ p 0 xs) k e → k ∈ ks
    allT = of-rows p 0 xs , of-in p 0 xs

    allU : Σ (List Pos) λ ks → ∀ {k e} → InE (Evs.ofᴱ p′ 0 (L.map V xs)) k e → k ∈ ks
    allU = of-rows p′ 0 (L.map V xs) , of-in p′ 0 (L.map V xs)

    reachT : ∀ {q e} → Reach (InE (Evs.ofᴱ p 0 xs)) q e
    reachT = proj₁ allT , λ r _ _ → proj₂ allT r

    reachU : ∀ {q e} → Reach (InE (Evs.ofᴱ p′ 0 (L.map V xs))) q e
    reachU = proj₁ allU , λ r _ _ → proj₂ allU r

    fewT : ∀ {k} → Few t k
    fewT = proj₁ allT , λ r _ → proj₂ allT (proj₁ r)

    lstU : ∀ {l} → Listed u l
    lstU {l} = fin-listed (proj₁ allU) (λ r → proj₂ allU (proj₁ r)) (λ m → let (e , r) = of-row p′ 0 (L.map V xs) m in e , r , reachU) l

    Img : Pos → Pos → Set
    Img k l = N k l × Σ (Ev A) (t k)

    img : ∀ {k e} → t k e → Σ Pos λ l → Img k l × Σ (Ev (IE A)) λ e′ → u l e′ × Listed u l × Match Every (One valuesOf) (Reads valuesOf) e e′
    img {k} {e} tk with of-up p p′ 0 xs (proj₁ tk)
    ... | a , pl , refl , r′ = p′ ⊕ [ a ] , ((a , pl , refl , refl) , e , tk) , mapEv V e , (r′ , reachU) , lstU , match-V e

    shown : ∀ {l e′} → u l e′ → Shown (One valuesOf) e′ → Live u l → Few u l
          → Σ Pos λ k → Img k l × Σ (Ev A) λ e₀ → t k e₀ × Match Every (One valuesOf) (Reads valuesOf) e₀ e′
    shown ul _ _ _ with of-down p p′ 0 xs (proj₁ ul)
    ... | a , pl , refl , e , r₀ , refl = p ⊕ [ a ] , ((a , pl , refl , refl) , e , r₀ , reachT) , e , (r₀ , reachT) , match-V e

    place : ∀ {m e} → u m e → instantOf m ≡ instantOf p′
    place um with of-down p p′ 0 xs (proj₁ um)
    ... | a , _ , refl , _ = instant-⊕ p′ [ a ]

    live : ∀ {k l} → Img k l → ∀ {c} → u c end → c ≺ l → ⊥
    live ((a , pl , _ , refl) , _) uc with of-end p′ 0 (L.map V xs) (proj₁ uc)
    ... | refl = last-max p′ pl

    carried : CarryAt valuesOf M HP HE LP t u p p′
    carried = record
      { Img     = Img
      ; ext     = λ { (n , _) → _ , inj₂ n , ⊑-refl _ }
      ; img     = λ tk _ _ _ _ → inj₁ (img tk)
      ; img¬¬   = λ tk _ _ _ n → let (l , i , e′ , ul , _ , m) = img tk in n (inj₁ (l , i , e′ , ul , m))
      ; shown   = shown
      ; img-row = λ { (_ , e , tk) n → n (e , tk , of-unp p 0 xs (proj₁ tk)) }
      ; img-fun = λ { (n , _) (n′ , _) → Emb.fun embN n n′ }
      ; place   = λ um _ _ → inj₁ (place um)
      ; live    = λ i _ → live i
      ; few     = λ _ → fewT
      ; whole   = λ _ _ _ → proj₁ allU , (λ ur → proj₂ allU (proj₁ ur)) , λ m → let (e , r) = of-row p′ 0 (L.map V xs) m in e , r , reachU
      ; bk      = λ _ → proj₁ allT
      ; in-bk   = λ { (_ , _ , tk) → proj₂ allT (proj₁ tk) }
      ; PB      = λ _ _ → ⊥
      ; pb-few  = λ _ → [] , λ ()
      ; pb-img  = λ ()
      ; pb-past = λ ()
      ; pinned  = λ {_} {r} tk _ _ _ → ⊥-elim (unp-pin {A} {r} (of-unp p 0 xs (proj₁ tk)))
      }

  of-carried : ∀ {A HP HE LP M₀ p p₀ p′} (xs : List A) → Emb M₀ → Fresh HP M₀ p → M₀ p p₀ → p₀ ⊑ p′ → NotHot HP p
             → Σ PMap λ M → M₀ ⊆ᴹ M × Emb M × Within HP M₀ M p × Bare M (Truncate (InE (Evs.ofᴱ p 0 xs)))
               × (∀ {x y} → M x y → M₀ x y ⊎ Grown M₀ HP x y) × CarryAt valuesOf M HP HE LP (Truncate (InE (Evs.ofᴱ p 0 xs))) (Truncate (InE (Evs.ofᴱ p′ 0 (L.map V xs)))) p p′
  of-carried {A} {HP} {HE} {LP} {p = p} xs E₀ fr m₀ pp nh = O.M , inj₁ , O.emb , O.within , O.bare {t = Truncate (InE (Evs.ofᴱ p 0 xs))} (λ {k} {e} tk → of-shape {k} {e} (proj₁ tk)) , O.grown nh , X.carried
    where module X = OfRows {A} {HP} {HE} {LP} xs E₀ fr m₀ pp
          module O = OneUnder E₀ fr m₀ pp
          of-shape : ∀ {k e} → InE (Evs.ofᴱ p 0 xs) k e → Σ Label λ a → Plain a × k ≡ p ⊕ [ a ]
          of-shape r = let (a , pl , e , _) = of-up p p 0 xs r in a , pl , e

-- AN `of` lists its values one label under each subscription.
carry-of : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (xs : List A) → Carry m ρ (of xs)
carry-of n ρ xs = carry λ envP envE _ _ M₀ e₀ er jn _ _ p p′ m₀ _ _ nh fr →
  let (M , ms , hm , wi , br , gr , c) = of-carried xs e₀ fr m₀ (⊑-refl p′) nh
  in M , ms , hm , wi , br , joins-grow {ρ = ρ} {envP = envP} {envE = envE} {er = er} {M = M₀} {N = M} (λ {x} {y} → ms {x} {y}) jn (λ {x} {y} → gr {x} {y})
     , grown-past {ρ = ρ} {envP = envP} {envE = envE} er (env-past er) (λ {x} {y} → gr {x} {y}) , c , λ _ ()

-- THE EMPTY PROGRAM ends at once, on both sides: the empty listing.
carry-empty : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → Carry m ρ (empty {A = A})
carry-empty n ρ = carry λ envP envE _ _ M₀ e₀ er jn _ _ p p′ m₀ _ _ nh fr →
  let (M , ms , hm , wi , br , gr , c) = of-carried [] e₀ fr m₀ (⊑-refl p′) nh
  in M , ms , hm , wi , br , joins-grow {ρ = ρ} {envP = envP} {envE = envE} {er = er} {M = M₀} {N = M} (λ {x} {y} → ms {x} {y}) jn (λ {x} {y} → gr {x} {y})
     , grown-past {ρ = ρ} {envP = envP} {envE = envE} er (env-past er) (λ {x} {y} → gr {x} {y}) , c , λ _ ()

------------------------------------------------------------------------
-- The whole run

-- Where `elaborate` subscribes the elaborated program: past its restamp
-- and its takeWhile, the first lane of its merge, and that lane's
-- connect's source.
coreAt : Pos
coreAt = root ⊕ (ix 0 ∷ ix 1 ∷ ix 1 ∷ [])

-- The plain run's subscription paired with the core's: one pair, in
-- neither world.
At₀ : PMap
At₀ x y = x ≡ root × y ≡ coreAt

emb-At₀ : Emb At₀
emb-At₀ = record
  { fun     = λ { (refl , refl) (refl , refl) → refl }
  ; mono    = λ { (refl , refl) (refl , refl) rr → ⊥-elim (≺-irrefl {root} rr) }
  ; reflect = λ { (refl , refl) (refl , refl) _ → [] , refl }
  ; inst    = λ { (refl , refl) (refl , refl) → mk⇔ (λ _ → refl) (λ _ → refl) }
  }

fresh-At₀ : Fresh (λ _ → ⊥) At₀ root
fresh-At₀ (refl , refl) _ = refl
