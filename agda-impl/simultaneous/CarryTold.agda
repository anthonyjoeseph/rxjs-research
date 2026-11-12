{-# OPTIONS --guardedness #-}

-- A RUN TOLD ITS END CARRIES THE RUN.  `completing` and `annotate` each
-- read a run through its own subject by a concat queueing one more row,
-- which shows nothing, at the run's end: one connect, two uses.  Around
-- it, rows relabelled one for one: a map, and a scan projected, whose
-- rows show what the rows they relabel showed.
module simultaneous.CarryTold where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (any?)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; yes; no)

open import Tree using (Obs)
open import denotation.Position using (_≟ᵖ_; Pos; ix; sub; last; _⊕_; root)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Few; Reach; Den; DenEnv; enter; approx; _≺_; module Scan; module Op)
open import denotation.Laws.Modulus using (entered-reach; entered-few; reach-few; ≼-split; ≺→≼; ≺-≼-≺; ≼-≺-≺; ≺-trans)
open import denotation.Laws.Worlds using (InvAt; Ok; Hots; GoodEnv; full; _⊑_; ⊑-refl; ⊑-trans; ⊑-≼; ⊕-assoc; ok-step)
open import denotation.Laws using (inv-approx)
open import denotation.Laws.Worlds.Leaves using (module AccF)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.Readings using (instantOf)
open import simultaneous.HeldMap using (mapEv; module MapRun)
open import simultaneous.Attribution using (Shown; Match; Every; One; Reads; Carried; Live)
open import simultaneous.Listing using (Listed)
open import simultaneous.Folds using (reach-kin; few-¬¬listed; module ListedFold)
open import simultaneous.CarryBase using (CarryAt; Kin; k-out; k-skip; k-pin; k-end; kin-refl; module Relabel; IntoAt; Near; Home; instant-⊕;
  sub-listed; ahead-over)
open import simultaneous.ReadRows using (up; up-⊕)
open import simultaneous.ToldRows using (told; module Told)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

------------------------------------------------------------------------
-- Rows showing alike

-- Two events alike but for their labels, each label showing what the
-- other does.
data Same {X Y Z : Set} (f₁ : Y → List X) (f₂ : Z → List X) : Ev Y → Ev Z → Set where
  same-out  : ∀ {x y} → f₁ x ≡ f₂ y → Same f₁ f₂ (out x) (out y)
  same-skip : Same f₁ f₂ skip skip
  same-pin  : ∀ {r} → Same f₁ f₂ (pin r) (pin r)
  same-end  : Same f₁ f₂ end end

private
  module Alike {X Y Z : Set} {f₁ : Y → List X} {f₂ : Z → List X} where
    kin : ∀ {e e′} → Same f₁ f₂ e e′ → Kin e e′
    kin (same-out _) = k-out
    kin same-skip    = k-skip
    kin same-pin     = k-pin
    kin same-end     = k-end

    shown : ∀ {e e′} → Same f₁ f₂ e e′ → Shown (One f₂) e′ → Shown (One f₁) e
    shown (same-out eq) (a , r) = a , trans eq r
    shown same-end      _       = tt
    shown same-skip     ()
    shown same-pin      ()

    carried : ∀ {e₀ : Ev X} {e e′} → Carried (Reads f₁) e₀ e → Same f₁ f₂ e e′ → Carried (Reads f₂) e₀ e′
    carried {e₀ = out _} (_ , refl , r) (same-out eq) = _ , refl , trans (sym eq) r
    carried {e₀ = end}   refl           same-end      = refl
    carried {e₀ = skip}  ()             _
    carried {e₀ = pin _} ()             _

    match : ∀ {e₀ : Ev X} {e e′} → Same f₁ f₂ e e′
          → Match Every (One f₁) (Reads f₁) e₀ e → Match Every (One f₂) (Reads f₂) e₀ e′
    match sv (cr , ns) = (λ s₀ → carried (cr s₀) sv) , λ n sw → ns n (shown sv sw)

  -- A carry relabelled on the elaborated side alone, row for row.
  module OneSide {X Y Z : Set} {f₁ : Y → List X} {f₂ : Z → List X} {u : EmissionSet Y} {u′ : EmissionSet Z}
    (upL′ : ∀ {l e} → Listed u l → u l e → Σ (Ev Z) λ e′ → u′ l e′ × Same f₁ f₂ e e′)
    (up¬¬′ : ∀ {l e} → u l e → ¬ ¬ Σ (Ev Z) λ e′ → u′ l e′ × Same f₁ f₂ e e′)
    (up-end′ : ∀ {l} → u l end → u′ l end) (up-pin′ : ∀ {l r} → u l (pin r) → u′ l (pin r))
    (down′ : ∀ {l e′} → u′ l e′ → Σ (Ev Y) λ e → u l e × Same f₁ f₂ e e′) where

    carried : ∀ {M HP HE LP} {t : EmissionSet X} {s s′} → CarryAt f₁ M HP HE LP t u s s′ → CarryAt f₂ M HP HE LP t u′ s s′
    carried {t = t} c =
      Relabel.carried {t = t} {t′ = t} (λ _ e e′ → e′ ≡ e) (λ _ → Same f₁ f₂) (λ { {e = e} refl → kin-refl e })
        (λ {l} {e} {e′} → Alike.kin {e = e} {e′ = e′})
        (λ tk → _ , tk , refl) (λ tk → _ , tk , refl) (λ {l} {e} → upL′ {l} {e}) (λ {l} {e} → up¬¬′ {l} {e}) (λ {l} → up-end′ {l})
        (λ {l} {r} → up-pin′ {l} {r}) (λ {l} {e′} → down′ {l} {e′}) c
        (λ {l} {e} {e′} → Alike.shown {e = e} {e′ = e′}) (λ { _ refl sv m → Alike.match sv m })

------------------------------------------------------------------------
-- A map

-- A MAP RELABELS: each row keeps its place, its label mapped, showing
-- what it showed.
module Mapped {X Y Z : Set} {f₁ : Y → List X} {f₂ : Z → List X} (g : Y → Z) (law : ∀ y → f₁ y ≡ f₂ (g y)) (d : Den Y) (p′ : Pos) where
  private
    module E = MapRun g d p′

    same : ∀ (e : Ev Y) → Same f₁ f₂ e (mapEv g e)
    same (out y) = same-out (law y)
    same skip    = same-skip
    same (pin _) = same-pin
    same end     = same-end

    down : ∀ {l e′} → E.M l e′ → Σ (Ev Y) λ e → E.S l e × Same f₁ f₂ e e′
    down m with E.unmap m
    ... | e , x , refl = e , x , same e

  carried : ∀ {M HP HE LP} {t : EmissionSet X} {s} → CarryAt f₁ M HP HE LP t E.S s p′ → CarryAt f₂ M HP HE LP t E.M s p′
  carried = OneSide.carried (λ {_} {e} _ x → _ , E.lift x , same e) (λ {_} {e} x n → n (_ , E.lift x , same e)) E.lift E.lift
              (λ {l} {e′} → down {l} {e′})

------------------------------------------------------------------------
-- A scan projected

-- A SCAN PROJECTED RELABELS when each step's projection shows what its
-- row did: its state folds the rows before, so it is built only from a
-- listing, and refutably elsewhere.
module Folded {X Y Z B : Set} {f₁ : Y → List X} {f₂ : Z → List X} (g : B → Y → B) (z : B) (π : B → Z)
  (law : ∀ b y → f₂ (π (g b y)) ≡ f₁ y) (d : Den Y) (p′ : Pos) {H : Pos → Set} (Iu : InvAt H p′ (enter d p′)) where
  private
    u : EmissionSet Y
    u = enter d p′

    funcU : ∀ {y e e′} → u y e → u y e′ → e ≡ e′
    funcU {y} {e} {e′} = InvAt.func Iu {y} {e} {e′}

    module RS = Scan g z u
    module AF = AccF g z {t = u} (λ {y} {e} {e′} → funcU {y} {e} {e′})
    module RL = ListedFold g z {t = u} (λ {y} {e} {e′} → funcU {y} {e} {e′})
    module W = MapRun π (Op.scan g z d) p′

    down₀ : ∀ {l e′} → RS.ScanT l e′ → Σ (Ev Y) λ e → u l e × Kin e e′
    down₀ (RS.sval a)  = _ , proj₂ (AF.acc-val a) , k-out
    down₀ (RS.sstep x) = _ , x , k-skip
    down₀ (RS.spin x)  = _ , x , k-pin
    down₀ (RS.send x)  = _ , x , k-end

    vals-acc : ∀ {l st y} → RS.Acc l st → u l (out y) → f₂ (π st) ≡ f₁ y
    vals-acc (RS.acc₀ {a = a} x _) ux with funcU x ux
    ... | refl = law z a
    vals-acc (RS.acc {b = b} {a′ = a′} _ x _ _) ux with funcU x ux
    ... | refl = law b a′

    rch : ∀ {q e} → u q e → Reach u q e
    rch {q} {e} = entered-reach d p′ {q} {e}

    upL : ∀ {l e} → Listed u l → u l e → Σ (Ev Z) λ e′ → W.M l e′ × Same f₁ f₂ e e′
    upL {e = out y} L uy with RL.fold-listed L uy
    ... | st , ac = out (π st) , W.lift (RS.sval ac , reach-kin down₀ (k-out {a = y} {b = st}) (rch uy)) , same-out (sym (vals-acc ac uy))
    upL {e = skip}  _ x = skip , W.lift (RS.sstep x , reach-kin down₀ k-skip (rch x)) , same-skip
    upL {e = pin r} _ x = pin r , W.lift (RS.spin x , reach-kin down₀ k-pin (rch x)) , same-pin
    upL {e = end}   _ x = end , W.lift (RS.send x , reach-kin down₀ k-end (rch x)) , same-end

    up-pin : ∀ {l r} → u l (pin r) → W.M l (pin r)
    up-pin x = W.lift (RS.spin x , reach-kin down₀ k-pin (rch x))

    up-end : ∀ {l} → u l end → W.M l end
    up-end x = W.lift (RS.send x , reach-kin down₀ k-end (rch x))

    up¬¬ : ∀ {l e} → u l e → ¬ ¬ Σ (Ev Z) λ e′ → W.M l e′ × Same f₁ f₂ e e′
    up¬¬ {l} {e = out y} uy n = few-¬¬listed (reach-few {e = out y} (λ {k} {e′} → full {q = l} {e = out y} tt {k} {e′}) (rch uy)) λ L → n (upL L uy)
    up¬¬ {e = skip}  x  n = n (skip , W.lift (RS.sstep x , reach-kin down₀ k-skip (rch x)) , same-skip)
    up¬¬ {e = pin r} x  n = n (pin r , up-pin x , same-pin)
    up¬¬ {e = end}   x  n = n (end , up-end x , same-end)

    back : ∀ {l e₀} → RS.ScanT l e₀ → Σ (Ev Y) λ e → u l e × Same f₁ f₂ e (mapEv π e₀)
    back (RS.sval a)  = let (y , uy) = AF.acc-val a in out y , uy , same-out (sym (vals-acc a uy))
    back (RS.sstep x) = skip , x , same-skip
    back (RS.spin x)  = _ , x , same-pin
    back (RS.send x)  = end , x , same-end

    down : ∀ {l e′} → W.M l e′ → Σ (Ev Y) λ e → u l e × Same f₁ f₂ e e′
    down m with W.unmap m
    ... | _ , (sc , _) , refl = back sc

  carried : ∀ {M HP HE LP} {t : EmissionSet X} {s} → CarryAt f₁ M HP HE LP t u s p′ → CarryAt f₂ M HP HE LP t W.M s p′
  carried = OneSide.carried (λ {l} {e} → upL {l} {e}) (λ {l} {e} → up¬¬ {l} {e}) (λ {l} → up-end {l}) (λ {l} {r} → up-pin {l} {r})
              (λ {l} {e′} → down {l} {e′})

------------------------------------------------------------------------
-- The told run

-- THE TOLD RUN CARRIES THE RUN, where the queued row shows nothing: each
-- carrier moves to its row's image (`simultaneous.ToldRows`), and a
-- carrier that is no row stays put.  A pin is carried into the told
-- connect's copy of its carrier, which lies under it.
module _ {Γ X Y} {f : Y → List X} {M HP HE LP} {t : EmissionSet X} {s} n (S : Obs Timeline Γ Y) (x : Y) (fx : f x ≡ [])
         (env : DenEnv Γ) (genv : GoodEnv env) (q : Pos) (ok : Ok (Hots env) q)
         (c : CarryAt f M HP HE LP t (enter (approx n S env) (q ⊕ [ ix 1 ])) s (q ⊕ [ ix 1 ])) where
  private
    open Told n S x env genv q ok
    module C = CarryAt c

    few-of : ∀ {l} → Listed σ l → Few σ l
    few-of (ks , F , _) = ks , F

    inst-⊑ : ∀ {l m} → l ⊑ m → instantOf m ≡ instantOf l
    inst-⊑ {l} (zs , refl) = instant-⊕ l zs

    -- Where a carrier moves: to its row's image, or nowhere.
    Mv : Pos → Pos → Set
    Mv l l′ = (Σ (Ev Y) λ e → σ l e × l′ ≡ l ⊕ δ e) ⊎ ((∀ {e} → σ l e → ⊥) × l′ ≡ l)

    mv-⊑ : ∀ {l l′} → Mv l l′ → l ⊑ l′
    mv-⊑ (inj₁ (e , _ , eq)) = δ e , eq
    mv-⊑ {l} (inj₂ (_ , refl)) = ⊑-refl l

    mv-fun : ∀ {l a b} → Mv l a → Mv l b → a ≡ b
    mv-fun (inj₁ (_ , y , refl)) (inj₁ (_ , y′ , refl)) rewrite InvAt.func invσ y y′ = refl
    mv-fun (inj₁ (_ , y , _))    (inj₂ (n , _))         = ⊥-elim (n y)
    mv-fun (inj₂ (n , _))        (inj₁ (_ , y , _))     = ⊥-elim (n y)
    mv-fun (inj₂ (_ , refl))     (inj₂ (_ , refl))      = refl

    Img′ : Pos → Pos → Set
    Img′ k l′ = Σ Pos λ l → C.Img k l × Mv l l′

    PB′ : Pos → Pos → Set
    PB′ k l′ = Σ Pos λ l → C.PB k l × Σ (Ev Y) λ e → σ l e × l′ ≡ l ⊕ δ e

    shown-back : ∀ {e e′} → Told e e′ → Shown (One f) e′ → Shown (One f) e
    shown-back t-out  sh = sh
    shown-back t-end  sh = sh
    shown-back t-skip ()
    shown-back (t-pin _) ()

    match-told : ∀ {e₀ : Ev X} {e e′} → Match Every (One f) (Reads f) e₀ e → Told e e′ → Match Every (One f) (Reads f) e₀ e′
    match-told m t-out  = m
    match-told m t-skip = m
    match-told m t-end  = m
    match-told {e₀ = out _} (cr , _) (t-pin _) with cr tt
    ... | _ , () , _
    match-told {e₀ = end}   (cr , _) (t-pin _) with cr tt
    ... | ()
    match-told {e₀ = skip}  _ (t-pin _) = (λ ()) , λ _ ()
    match-told {e₀ = pin _} _ (t-pin _) = (λ ()) , λ _ ()

    -- A plain row carried by a pin is a skip.
    pin-skip : ∀ {e : Ev X} {r} → Match Every (One f) (Reads f) e (pin r) → Unpinned e → e ≡ skip
    pin-skip {e = out _} (cr , _) _ with cr tt
    ... | _ , () , _
    pin-skip {e = end}   (cr , _) _ with cr tt
    ... | ()
    pin-skip {e = skip}  _ _ = refl
    pin-skip {e = pin _} _ ()

    up³ : ∀ l a b d → up (up (up (l ⊕ (a ∷ b ∷ d ∷ [])))) ≡ l
    up³ l a b d = trans (cong (λ z → up (up (up z))) e) (trans (cong (λ z → up (up z)) (up-⊕ ((l ⊕ [ a ]) ⊕ [ b ]) d))
                    (trans (cong up (up-⊕ (l ⊕ [ a ]) b)) (up-⊕ l a)))
      where
        e : l ⊕ (a ∷ b ∷ d ∷ []) ≡ ((l ⊕ [ a ]) ⊕ [ b ]) ⊕ [ d ]
        e = sym (trans (⊕-assoc (l ⊕ [ a ]) [ b ] [ d ]) (⊕-assoc l [ a ] (b ∷ d ∷ [])))

    bk′ : Pos → List Pos
    bk′ l′ = C.bk l′ ++ C.bk (up l′) ++ C.bk (up (up (up l′)))

    in-up : ∀ {k l} a → k ∈ C.bk l → k ∈ bk′ (l ⊕ [ a ])
    in-up {k} {l} a m = ∈-++⁺ʳ (C.bk (l ⊕ [ a ])) (∈-++⁺ˡ (subst (λ z → k ∈ C.bk z) (sym (up-⊕ l a)) m))

    in-δ : ∀ {k l} (e : Ev Y) → k ∈ C.bk l → k ∈ bk′ (l ⊕ δ e)
    in-δ (out _) m = in-up (sub w) m
    in-δ skip    m = in-up (sub w) m
    in-δ (pin _) m = in-up (ix 0) m
    in-δ {k} {l} end m =
      ∈-++⁺ʳ (C.bk (l ⊕ δ end)) (∈-++⁺ʳ (C.bk (up (l ⊕ δ end))) (subst (λ z → k ∈ C.bk z) (sym (up³ l (sub w) (ix 1) last)) m))

    in-bk′ : ∀ {k l′} → Img′ k l′ → k ∈ bk′ l′
    in-bk′ (_ , i , inj₁ (e , _ , refl)) = in-δ e (C.in-bk i)
    in-bk′ (_ , i , inj₂ (_ , refl))     = ∈-++⁺ˡ (C.in-bk i)

    img-fun′ : ∀ {k a b} → Img′ k a → Img′ k b → a ≡ b
    img-fun′ (_ , i , m) (_ , i′ , m′) with C.img-fun i i′
    ... | refl = mv-fun m m′

    live′ : ∀ {k l′} → Img′ k l′ → Live t k → Live τ l′
    live′ (_ , i , inj₁ (_ , y , refl)) lv = told-live y (λ {c′} → C.live i (λ {c₀} → lv {c₀}) {c′})
    live′ (_ , i , inj₂ (_ , refl))     lv = told-live-at (λ {c′} → C.live i (λ {c₀} → lv {c₀}) {c′})

    -- The image of a row with few before it.
    imaged : ∀ {k l e} → C.Img k l → σ l e → Few σ l → Σ (Ev Y) λ e′ → Img′ k (l ⊕ δ e) × τ (l ⊕ δ e) e′ × Told e e′
    imaged {e = e} i y fw with told-row y fw
    ... | e′ , y′ , tr = e′ , (_ , i , inj₁ (e , y , refl)) , y′ , tr

    into′ : ∀ {k} → IntoAt C.Img σ C.PB HP s k → IntoAt Img′ τ PB′ HP s k
    into′ ((l , (e₀ , y) , L , pb) , h) = (l ⊕ δ e₀ , (proj₁ (told-row y (few-of L)) , proj₁ (proj₂ (told-row y (few-of L)))) , told-listed y L , (l , pb , e₀ , y , refl)) , home h
      where
        home : _ → _
        home (inj₁ e) = inj₁ e
        home (inj₂ (inj₁ (k₀ , l₀ , i , kk , ek , (e₁ , y₀) , L₀))) with imaged i y₀ (few-of L₀)
        ... | e′ , i′ , y′ , _ = inj₂ (inj₁ (k₀ , l₀ ⊕ δ e₁ , i′ , kk , ek , (e′ , y′) , told-listed y₀ L₀))
        home (inj₂ (inj₂ h)) = inj₂ (inj₂ h)

    img′ : ∀ {k e} → t k e → Unpinned e → Live t k → Listed t k → LP k
         → (Σ Pos λ l → Img′ k l × Σ (Ev Y) λ e′ → τ l e′ × Listed τ l × Match Every (One f) (Reads f) e e′)
           ⊎ (e ≡ skip × IntoAt Img′ τ PB′ HP s k)
    img′ tk un lv L lp with C.img tk un lv L lp
    ... | inj₂ (es , h) = inj₂ (es , into′ h)
    ... | inj₁ (l , i , e′ , y , Ll , mt) with imaged i y (few-of Ll)
    ...   | e″ , i′ , y′ , tr = inj₁ (_ , i′ , e″ , y′ , told-listed y Ll , match-told mt tr)

    img¬¬′ : ∀ {k e} → t k e → Unpinned e → Live t k → Few t k
           → ¬ ¬ ((Σ Pos λ l → Img′ k l × Σ (Ev Y) λ e′ → τ l e′ × Match Every (One f) (Reads f) e e′) ⊎ e ≡ skip)
    img¬¬′ {e = e} tk un lv fw n = C.img¬¬ tk un lv fw go
      where
        go : ((Σ Pos λ l → C.Img _ l × Σ (Ev Y) λ e′ → σ l e′ × Match Every (One f) (Reads f) e e′) ⊎ e ≡ skip) → ⊥
        go (inj₂ es) = n (inj₂ es)
        go (inj₁ (l , i , pin _ , y , mt)) = n (inj₂ (pin-skip mt un))
        go (inj₁ (l , i , out a , y , mt)) with imaged i y (few-unp y tt)
        ... | e″ , i′ , y′ , tr = n (inj₁ (_ , i′ , e″ , y′ , match-told mt tr))
        go (inj₁ (l , i , skip , y , mt)) with imaged i y (few-unp y tt)
        ... | e″ , i′ , y′ , tr = n (inj₁ (_ , i′ , e″ , y′ , match-told mt tr))
        go (inj₁ (l , i , end , y , mt)) with imaged i y (few-unp y tt)
        ... | e″ , i′ , y′ , tr = n (inj₁ (_ , i′ , e″ , y′ , match-told mt tr))

    shown-unp : ∀ {e e′} → Told e e′ → Shown (One f) e′ → Unpinned e
    shown-unp t-out _ = tt
    shown-unp t-end _ = tt
    shown-unp t-skip ()
    shown-unp (t-pin _) ()

    shown′ : ∀ {l e} → τ l e → Shown (One f) e → Live τ l → Few τ l
           → Σ Pos λ k → Img′ k l × Σ (Ev X) λ e₀ → t k e₀ × Match Every (One f) (Reads f) e₀ e
    shown′ y sh lv fw with told-shown fx y sh
    ... | l , e , yl , refl , tr with C.shown yl (shown-back tr sh) (told-live← y yl (δ e , refl) (λ {c′} → lv {c′})) (few-unp yl (shown-unp tr sh))
    ...   | k , i , e₀ , tk , mt = k , (l , i , inj₁ (e , yl , refl)) , e₀ , tk , match-told mt tr

    Placed : Pos → Set
    Placed m = instantOf m ≡ instantOf q ⊎ (Σ Pos λ k → Σ Pos λ l → Img′ k l × instantOf l ≡ instantOf m × Near τ m l)
               ⊎ Σ Pos λ h → HE h × instantOf h ≡ instantOf m

    -- A carrier near a row of `σ` at `l`, listed, is near its image's row.
    near′ : ∀ {k l l₂ e m} → C.Img k l₂ → σ l e → Listed σ l → l ⊑ m → instantOf l₂ ≡ instantOf l → Near σ l l₂ → Placed m
    near′ {k} {l} {l₂} {e} {m} i y L lm ie nr = inj₂ (inj₁ (go nr))
      where
        ie′ : instantOf l₂ ≡ instantOf m
        ie′ = trans ie (sym (inst-⊑ lm))

        at : ∀ {e₂} → σ l₂ e₂ → Listed σ l₂ → Σ Pos λ k′ → Σ Pos λ l′ → Img′ k′ l′ × instantOf l′ ≡ instantOf m × Near τ m l′
        at {e₂} y₂ L₂ with imaged i y₂ (few-of L₂)
        ... | e″ , i′ , y″ , _ = k , l₂ ⊕ δ e₂ , i′ , trans (instant-⊕ l₂ (δ e₂)) ie′ , inj₂ ((e″ , y″) , told-listed y₂ L₂)

        go : Near σ l l₂ → Σ Pos λ k′ → Σ Pos λ l′ → Img′ k′ l′ × instantOf l′ ≡ instantOf m × Near τ m l′
        go (inj₂ ((_ , y₂) , L₂)) = at y₂ L₂
        go (inj₁ l₂l) with ≼-split {l₂} {l} l₂l
        ... | inj₂ refl = at y L
        ... | inj₁ lt with any? (l₂ ≟ᵖ_) (proj₁ L)
        ...   | yes mem = at (proj₂ (proj₂ (proj₂ (proj₂ L) mem))) (sub-listed L lt)
        ...   | no nm   = k , l₂ , (l₂ , i , inj₂ ((λ y₂ → nm (proj₁ (proj₂ L) y₂ lt)) , refl)) , ie′
                          , inj₁ (≺→≼ {l₂} {m} (≺-≼-≺ {l₂} {l} {m} lt (⊑-≼ lm)))

    placed : ∀ {m l e} → σ l e → Listed σ l → l ⊑ m
           → instantOf l ≡ instantOf (q ⊕ [ ix 1 ]) ⊎ (Σ Pos λ k → Σ Pos λ l₂ → C.Img k l₂ × instantOf l₂ ≡ instantOf l × Near σ l l₂)
             ⊎ Σ Pos (λ h → HE h × instantOf h ≡ instantOf l)
           → Placed m
    placed {l = l} _ _ lm (inj₁ eq) = inj₁ (trans (inst-⊑ lm) (trans eq (instant-⊕ q [ ix 1 ])))
    placed y L lm (inj₂ (inj₁ (k , l₂ , i , ie , nr))) = near′ i y L lm ie nr
    placed _ _ lm (inj₂ (inj₂ (h , he , eq))) = inj₂ (inj₂ (h , he , trans eq (sym (inst-⊑ lm))))

    place′ : ∀ {m e} → τ m e → Live τ m → Listed τ m → Placed m
    place′ y lv L with told-from y
    ... | inj₁ eq = inj₁ eq
    ... | inj₂ (l , e , yl , lm) = placed yl (told-listed← y yl lm L) lm (C.place yl (told-live← y yl lm (λ {c′} → lv {c′})) (told-listed← y yl lm L))

    pb-few′ : ∀ {l′ e} → τ l′ e → Σ (List Pos) λ ks → ∀ {k} → PB′ k l′ → k ∈ ks
    pb-few′ y with told-source? y
    ... | inj₂ none = [] , λ { (_ , _ , _ , y₂ , eq) → ⊥-elim (none y₂ eq) }
    ... | inj₁ (l , _ , yl , refl) = proj₁ (C.pb-few yl) , λ { (l₂ , pb , _ , y₂ , eq) → proj₂ (C.pb-few yl) (subst (C.PB _) (sym (told-inj yl y₂ eq)) pb) }

    pinned′ : ∀ {k p} → t k (pin p) → Live t k → Listed t k → LP k
            → (Σ Pos λ l → Σ Pos λ p′ → τ l (pin p′) × PB′ k l × (∀ {k′ l′} → Img′ k′ l′ → l′ ≺ p′ → k′ ≺ p) × Listed τ l)
              × (instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → k₀ ≺ p × Home t k₀ × instantOf k₀ ≡ instantOf k)
                 ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)
    pinned′ tk lv L lp with C.pinned tk lv L lp
    ... | (l , p′ , y , pb , B , Ll) , h = carrier (told-row y (few-of Ll)) , h
      where
        carrier : (Σ (Ev Y) λ e′ → τ (l ⊕ [ ix 0 ]) e′ × Told (pin p′) e′)
                → Σ Pos λ l′ → Σ Pos λ r → τ l′ (pin r) × PB′ _ l′ × (∀ {k′ l″} → Img′ k′ l″ → l″ ≺ r → k′ ≺ _) × Listed τ l′
        carrier (pin r , y′ , t-pin rr) = l ⊕ [ ix 0 ] , r , y′ , (l , pb , pin p′ , y , refl) , B′ rr , told-listed y Ll
          where
            B′ : r ≡ p′ ⊎ r ≡ q → ∀ {k′ l″} → Img′ k′ l″ → l″ ≺ r → k′ ≺ _
            B′ (inj₁ refl) {l″ = l″} (l₁ , i , mv) lr = B i (≼-≺-≺ {l₁} {l″} {p′} (⊑-≼ {l₁} {l″} (mv-⊑ mv)) lr)
            B′ (inj₂ refl) {l″ = l″} (l₁ , i , mv) lr =
              B i (≺-trans {l₁} {q} {p′} (≼-≺-≺ {l₁} {l″} {q} (⊑-≼ {l₁} {l″} (mv-⊑ mv)) lr) (told-pin-past y))

  told-carry : Σ (CarryAt f M HP HE LP t (enter (approx n (told x S) env) q) s q)
                 λ c′ → ∀ {k l e₀} → CarryAt.PB c′ k l → t k e₀ → Live t k → Σ Pos λ l₀ → CarryAt.PB c k l₀ × l₀ ⊑ l
  told-carry = record
    { Img = Img′ ; ext = λ { (_ , i , mv) → let (y , m , yl) = C.ext i in y , m , ⊑-trans yl (mv-⊑ mv) }
    ; PB = PB′ ; pb-few = pb-few′ ; pb-img = λ { (_ , pb , _) (_ , i , _) → C.pb-img pb i }
    ; pb-past = λ { (l , pb , e , y , refl) tk lv _ m xk nx → ahead-over (C.pb-past pb tk lv y m xk nx) (δ e , refl) }
    ; img = img′ ; img¬¬ = img¬¬′ ; shown = shown′
    ; img-row = λ { (_ , i , _) → C.img-row i } ; img-fun = img-fun′
    ; place = place′ ; live = live′ ; few = λ { (_ , i , _) → C.few i }
    ; whole = λ wt ne lp → told-whole (C.whole wt ne lp)
    ; bk = bk′ ; in-bk = in-bk′ ; pinned = pinned′ }
    , λ { (l , pb , e , _ , refl) _ _ → l , pb , (δ e , refl) }

-- What a row of a run read as maybe-emits shows.
justValues : ∀ {X} → Maybe (IE X) → List X
justValues (just x) = valuesOf x
justValues nothing  = []
