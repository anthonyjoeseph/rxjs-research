{-# OPTIONS --guardedness #-}

-- THE ANNOTATED SOURCE IS A RUN OF WHAT ITS SOURCE RUNS: a run of a
-- plain program by a source gives a run of its proper rows by the
-- source annotated, each carried value and end at its carrier's
-- annotation (`at`).
--
-- A VALUE OR AN END PAST A RUN'S END WOULD BE A PIN (`carried-proper`),
-- so every carried row on either side is proper, and a proper row's
-- past is proper.
--
-- A CARRIED ROW IS CARRIED AT ITS OWN BOUND (`own`): cut there, its
-- carrier's past is under the image of the row, so listed.
--
-- THE PLAIN RUN IS CUT WHERE ITS PROPER ROWS ARE LISTED (`cut`): up to
-- the bound, unless a proper end lies there, and then at that end, past
-- which every proper annotated row lies before the end's annotation.
module simultaneous.AnnRun where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; filter)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (_⊎-dec_)
open import Relation.Nullary.Decidable.Core using (T?)

open import Tree using (Obs)
open import denotation.Position using (_≟ᵖ_; _<ᵖ_; Pos; ix; sub; last; _⊕_; root)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Proper; DenEnv; _≺_)
open import denotation.Laws.Modulus using (≺-trans; ≺→≼; ≺-≼-≺; ≼-split; ≺-ext)
open import denotation.Laws.Worlds using (Ok; Hots; GoodEnv; InvAt; PinBy; _⊑_; ⊑-refl; ⊑-trans; ⊑-snoc⁺; ⊕-identityʳ)
open import denotation.Laws.Count using (⊑?)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Listing using (Listed)
open import simultaneous.SimPos using (UpTo; upto-down; ⊑-split)
open import simultaneous.Sim using (PMap; Emb; _⊆ᴹ_; Sim; Run; Lates; Mt; m-out; m-end; Carried; c-out; c-end; Upto; Under; Mapped; ListedB;
                                    Shows; Shown; AShows; AShown; annValues)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.ReadMap using (upto-dn; under?; under-down; upto-row)
open import simultaneous.AnnRows using (module Ann)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE)

------------------------------------------------------------------------
-- Proper rows and bounds

private
  no-pin : ∀ {A c} {e : Ev A} → Carried e → PinBy c e → ⊥
  no-pin c-out (_ , () , _)
  no-pin c-end (_ , () , _)

  end-ev? : ∀ {A} (e : Ev A) → Dec (e ≡ end)
  end-ev? end     = yes refl
  end-ev? (out _) = no λ ()
  end-ev? skip    = no λ ()
  end-ev? (pin _) = no λ ()

-- A carried row is proper.
carried-proper : ∀ {A H p} {t : EmissionSet A} → InvAt H p t → ∀ {k e} → t k e → Carried e → Proper t k e
carried-proper I y ce = y , λ x ck → no-pin ce (InvAt.quiet I x y ck)

-- Up to a bound: decided.
upto? : ∀ y l → Dec (UpTo y l)
upto? y l = T? (l <ᵖ y) ⊎-dec ⊑? y l

Upto? : ∀ c l → Dec (Upto c l)
Upto? nothing  _ = yes tt
Upto? (just c) l = upto? c l

under-⊑ : ∀ {A′} c {k m} → k ⊑ m → Under A′ c m → Under A′ c k
under-⊑ c km u with ⊑-split km
... | inj₁ refl = u
... | inj₂ lt   = under-down c lt u

------------------------------------------------------------------------
-- The run

-- Over any source and annotation with the annotated rows' facts.
module Annotated {X : Set} (σₑ : EmissionSet (IE X)) (σ′ : EmissionSet (AIE X))
                 (func-ₑ : ∀ {y e e′} → σₑ y e → σₑ y e′ → e ≡ e′) {H′ p′} (Iσ′ : InvAt H′ p′ σ′) (w : Pos)
                 (val→ : ∀ {l b} → σₑ l (out b) → Listed σₑ l → Σ (AIE X) λ b′ → σ′ (l ⊕ [ sub w ]) (out b′) × annValues b′ ≡ valuesOf b)
                 (end→ : ∀ {l} → σₑ l end → Listed σₑ l → σ′ (((l ⊕ [ sub w ]) ⊕ [ ix 1 ]) ⊕ [ last ]) end)
                 (aval← : ∀ {m b′} → σ′ m (out b′) → ¬ (annValues b′ ≡ [])
                        → Σ Pos λ l → Σ (IE X) λ b → σₑ l (out b) × m ≡ l ⊕ [ sub w ] × annValues b′ ≡ valuesOf b)
                 (aend← : ∀ {m} → σ′ m end → Σ Pos λ l → σₑ l end × m ≡ ((l ⊕ [ sub w ]) ⊕ [ ix 1 ]) ⊕ [ last ])
                 (listing : ∀ (P : Pos → Set) → (∀ l → Dec (P l)) → (∀ {k k′} → k′ ≺ k → P k → P k′) → (ks : List Pos)
                          → (∀ {l e} → σₑ l e → P l → l ∈ ks) → (∀ {l} → l ∈ ks → P l × Σ (Ev (IE X)) (σₑ l))
                          → Σ (List Pos) λ ls → (∀ {m e′} → Proper σ′ m e′ → (∀ {k e} → σₑ k e → k ⊑ m → P k) → m ∈ ls)
                                              × (∀ {m} → m ∈ ls → Σ (Ev (AIE X)) (Proper σ′ m)))
                 {H p} {σ : EmissionSet X} (Iσ : InvAt H p σ) {M : PMap} {L : PMap → Maybe Pos → Set}
                 (R : Run Shows Shown M L σ σₑ)
                 (need-row : ∀ {A′ c k e} → Proper σ k e → Upto c k → L A′ c → L A′ (just k)) where

  private module R = Run R

  c₁ : Pos → Pos
  c₁ l = ((l ⊕ [ sub w ]) ⊕ [ ix 1 ]) ⊕ [ last ]

  -- Where a carried row's annotation lies.
  at : Pos → Ev (IE X) → Pos
  at l (out _) = l ⊕ [ sub w ]
  at l end     = c₁ l
  at l skip    = l
  at l (pin _) = l

  at-⊑ : ∀ l e → l ⊑ at l e
  at-⊑ l (out _) = ⊑-snoc⁺ l
  at-⊑ l end     = ⊑-trans (⊑-trans (⊑-snoc⁺ l) (⊑-snoc⁺ (l ⊕ [ sub w ]))) (⊑-snoc⁺ ((l ⊕ [ sub w ]) ⊕ [ ix 1 ]))
  at-⊑ l skip    = ⊑-refl l
  at-⊑ l (pin _) = ⊑-refl l

  c₁-≻ : ∀ l → l ≺ c₁ l
  c₁-≻ l = ≺-trans {l} {l ⊕ [ sub w ]} {c₁ l} (≺-ext l [])
             (≺-trans {l ⊕ [ sub w ]} {(l ⊕ [ sub w ]) ⊕ [ ix 1 ]} {c₁ l} (≺-ext (l ⊕ [ sub w ]) []) (≺-ext ((l ⊕ [ sub w ]) ⊕ [ ix 1 ]) []))

  -- The carriers: a carrier's annotation.
  Img′ : Pos → Pos → Set
  Img′ k m = Σ Pos λ l → R.Img k l × Σ (Ev (IE X)) λ e → σₑ l e × Carried e × m ≡ at l e

  img-fun′ : ∀ {k m m′} → Img′ k m → Img′ k m′ → m ≡ m′
  img-fun′ (l , i , e , y , _ , refl) (l′ , i′ , e′ , y′ , _ , refl) with R.img-fun i i′
  ... | refl with func-ₑ y y′
  ...   | refl = refl

  ext′ : ∀ {k m} → Img′ k m → Σ Pos λ y → M k y × y ⊑ m
  ext′ (l , i , e , _ , _ , refl) = proj₁ (R.ext i) , proj₁ (proj₂ (R.ext i)) , ⊑-trans (proj₂ (proj₂ (R.ext i))) (at-⊑ l e)

  ----------------------------------------------------------------------
  -- Plain rows

  -- Under a row, no other.
  σ-sub : ∀ {k e k′ e′} → σ k e → σ k′ e′ → k ⊑ k′ → k′ ≡ k
  σ-sub {k} _ _ ([] , refl)    = ⊕-identityʳ k
  σ-sub     x y (_ ∷ _ , refl) = ⊥-elim (InvAt.flat Iσ x y)

  proper-upto : ∀ {k e k′ e′} → Proper σ k e → σ k′ e′ → UpTo k k′ → Proper σ k′ e′
  proper-upto {k} {k′ = k′} (_ , pr) y (inj₁ lt) = y , λ {c} x → ≺→≼ {k′} {c} (≺-≼-≺ {k′} {k} {c} lt (pr x))
  proper-upto (x , pr) y (inj₂ kk) with σ-sub x y kk
  ... | refl = y , pr

  -- Listed up to a bound, the plain rows up to a proper row before it.
  lb-own : ∀ {c k e} → Proper σ k e → Upto c k → ListedB (Proper σ) c → ListedB σ (just k)
  lb-own {c} x uk (ks , cov , bk) = ks , (λ y u → cov (proper-upto x y u) (upto-row (λ {y} {e} {l} {ys} {e′} → InvAt.flat Iσ {y} {e} {l} {ys} {e′}) c (proj₁ x) uk y u)) , λ m → proj₁ (bk m) , proj₁ (proj₂ (bk m))

  ----------------------------------------------------------------------
  -- A carried row at its own bound

  own : ∀ A′ → M ⊆ᴹ A′ → Emb A′ → ∀ {k e} → Proper σ k e → Carried e → L A′ (just k) → ListedB σ (just k)
      → Σ Pos λ l → R.Img k l × Σ (Ev (IE X)) λ e′ → σₑ l e′ × Listed σₑ l × Mt Shows e e′
  own A′ inc em {k} x ce Lk lk = l , i , proj₁ r , proj₁ (proj₂ r) , lsₑ , proj₂ (proj₂ r)
    where
      a = R.anchor A′ inc em (proj₁ x) ce Lk lk
      Sk = R.sim A′ inc em (just k) (proj₁ a , inc (proj₂ a)) Lk lk
      fw = Sim.fwd Sk (proj₁ x) ce (inj₂ (⊑-refl k))
      l = proj₁ fw
      i = proj₁ (proj₂ fw)
      r = proj₂ (proj₂ fw)
      ex = R.ext i
      up = Sim.upto Sk

      und : ∀ {u} → u ≺ l → Under A′ (just k) u
      und lt = proj₁ ex , inc (proj₁ (proj₂ ex)) , upto-down lt (inj₂ (proj₂ (proj₂ ex)))

      lsₑ : Listed σₑ l
      lsₑ = filter (λ u → T? (u <ᵖ l)) (proj₁ up)
          , (λ y lt → ∈-filter⁺ (λ u → T? (u <ᵖ l)) (proj₁ (proj₂ up) y (und lt)) lt)
          , λ m → proj₂ (∈-filter⁻ (λ u → T? (u <ᵖ l)) {xs = proj₁ up} m) , proj₂ (proj₂ up) (proj₁ (∈-filter⁻ (λ u → T? (u <ᵖ l)) {xs = proj₁ up} m))

  -- Its annotation.
  ann : ∀ {k l e e′} → R.Img k l → σₑ l e′ → Listed σₑ l → Mt Shows e e′
      → Σ Pos λ m → Img′ k m × Σ (Ev (AIE X)) λ e″ → Proper σ′ m e″ × Mt AShows e e″
  ann {l = l} i y ls (m-out v) with val→ y ls
  ... | b′ , y′ , eq = l ⊕ [ sub w ] , (l , i , _ , y , c-out , refl) , out b′ , carried-proper Iσ′ y′ c-out , m-out (trans eq v)
  ann {l = l} i y ls m-end = c₁ l , (l , i , end , y , c-end , refl) , end , carried-proper Iσ′ (end→ y ls) c-end , m-end

  ----------------------------------------------------------------------
  -- The cut

  -- Where the plain run is simulated, for a bound its proper rows are
  -- listed to.
  record Cut (A′ : PMap) (c : Maybe Pos) : Set₁ where
    field
      c′  : Maybe Pos
      mp′ : Mapped A′ c′
      S′  : Sim Shows Shown A′ R.Img c′ σ σₑ
      row : ∀ {m e′} → Proper σ′ m e′ → Under A′ c m → Under A′ c′ m

  -- A proper end up to the bound among the listed, or none.
  end? : ∀ c (ks : List Pos) → (∀ {k} → k ∈ ks → Σ (Ev X) (Proper σ k))
       → (Σ Pos λ k → Proper σ k end × Upto c k) ⊎ (∀ {k} → k ∈ ks → Proper σ k end → Upto c k → ⊥)
  end? c []       bk = inj₂ λ ()
  end? c (k ∷ ks) bk with end? c ks (λ m → bk (there m))
  ... | inj₁ f  = inj₁ f
  ... | inj₂ nf with end-ev? (proj₁ (bk (here refl))) | Upto? c k
  ...   | yes eq | yes u = inj₁ (k , subst (Proper σ k) eq (proj₂ (bk (here refl))) , u)
  ...   | yes _  | no nu = inj₂ λ { (here refl) _ u → nu u ; (there m) → nf m }
  ...   | no ne  | _     = inj₂ λ { (here refl) y _ → ne (InvAt.func Iσ (proj₁ (proj₂ (bk (here refl)))) (proj₁ y)) ; (there m) → nf m }

  -- No proper end up to the bound: every plain row up to it is proper.
  cut-none : ∀ A′ → M ⊆ᴹ A′ → Emb A′ → ∀ c → Mapped A′ c → L A′ c → (lst : ListedB (Proper σ) c)
           → (∀ {k} → k ∈ proj₁ lst → Proper σ k end → Upto c k → ⊥) → Cut A′ c
  cut-none A′ inc em c mp Lc (ks , cov , bk) ne = record { c′ = c ; mp′ = mp ; S′ = R.sim A′ inc em c mp Lc lb ; row = λ _ u → u }
    where
      prop : ∀ {k e} → σ k e → Upto c k → Proper σ k e
      prop y u = y , λ x lt → ne (cov (carried-proper Iσ x c-end) (upto-dn c lt u)) (carried-proper Iσ x c-end) (upto-dn c lt u)

      lb : ListedB σ c
      lb = ks , (λ y u → cov (prop y u) u) , λ m → proj₁ (bk m) , proj₁ (proj₂ (bk m))

  -- A proper end up to the bound: cut at it, past which no proper
  -- annotated row lies.
  cut-end : ∀ A′ → M ⊆ᴹ A′ → Emb A′ → ∀ c → L A′ c → ListedB (Proper σ) c → ∀ {kₑ} → Proper σ kₑ end → Upto c kₑ → Cut A′ c
  cut-end A′ inc em c Lc lst {kₑ} x u = record { c′ = just kₑ ; mp′ = proj₁ a , inc (proj₂ a) ; S′ = R.sim A′ inc em (just kₑ) (proj₁ a , inc (proj₂ a)) Lₑ lₑ ; row = rowₑ }
    where
      Lₑ = need-row {A′} {c} {kₑ} {end} x u Lc
      lₑ = lb-own x u lst
      a = R.anchor A′ inc em (proj₁ x) c-end Lₑ lₑ
      o = own A′ inc em x c-end Lₑ lₑ
      an = ann (proj₁ (proj₂ o)) (proj₁ (proj₂ (proj₂ (proj₂ o)))) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ o))))) (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ o)))))
      mₑ = proj₁ an
      ex = ext′ (proj₁ (proj₂ an))

      end-of : ∀ {e″} → Mt AShows end e″ → e″ ≡ end
      end-of m-end = refl

      yₑ : σ′ mₑ end
      yₑ = subst (σ′ mₑ) (end-of (proj₂ (proj₂ (proj₂ (proj₂ an))))) (proj₁ (proj₁ (proj₂ (proj₂ (proj₂ an)))))

      before : ∀ {m} → m ≺ mₑ ⊎ m ≡ mₑ → UpTo (proj₁ ex) m
      before (inj₁ lt)   = upto-down lt (inj₂ (proj₂ (proj₂ ex)))
      before (inj₂ refl) = inj₂ (proj₂ (proj₂ ex))

      rowₑ : ∀ {m e′} → Proper σ′ m e′ → Under A′ c m → Under A′ (just kₑ) m
      rowₑ {m} (_ , pr) _ = proj₁ ex , inc (proj₁ (proj₂ ex)) , before (≼-split {m} {mₑ} (pr yₑ))

  cut : ∀ A′ → M ⊆ᴹ A′ → Emb A′ → ∀ c → Mapped A′ c → L A′ c → ListedB (Proper σ) c → Cut A′ c
  cut A′ inc em c mp Lc lst with end? c (proj₁ lst) (proj₂ (proj₂ lst))
  ... | inj₁ (kₑ , x , u) = cut-end A′ inc em c Lc lst x u
  ... | inj₂ ne           = cut-none A′ inc em c mp Lc lst ne

  ----------------------------------------------------------------------
  -- The simulation

  sim′ : ∀ A′ → M ⊆ᴹ A′ → Emb A′ → ∀ c → Mapped A′ c → L A′ c → ListedB (Proper σ) c → Sim AShows AShown A′ Img′ c (Proper σ) (Proper σ′)
  sim′ A′ inc em c mp Lc lst = record { fwd = fwd ; val← = val ; end← = en ; upto = upto }
    where
      C = cut A′ inc em c mp Lc lst
      open Cut C

      fwd : ∀ {k e} → Proper σ k e → Carried e → Upto c k → Σ Pos λ m → Img′ k m × Σ (Ev (AIE X)) λ e″ → Proper σ′ m e″ × Mt AShows e e″
      fwd x ce uk = ann (proj₁ (proj₂ o)) (proj₁ (proj₂ (proj₂ (proj₂ o)))) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ o))))) (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ o)))))
        where o = own A′ inc em x ce (need-row x uk Lc) (lb-own x uk lst)

      val : ∀ {m b′} → Proper σ′ m (out b′) → AShown b′ → Under A′ c m → Σ Pos λ k → Img′ k m × Σ X λ a → Proper σ k (out a) × AShows a b′
      val (y′ , pr) sh u with aval← y′ sh
      ... | l , b , yₑ , refl , eq with Sim.val← S′ yₑ (λ e → sh (trans eq e)) (under-down c′ (≺-ext l []) (row (y′ , pr) u))
      ...   | k , i , a , x , shw = k , (l , i , out b , yₑ , c-out , refl) , a , carried-proper Iσ x c-out , trans eq shw

      en : ∀ {m} → Proper σ′ m end → Under A′ c m → Σ Pos λ k → Img′ k m × Proper σ k end
      en (y′ , pr) u with aend← y′
      ... | l , yₑ , refl with Sim.end← S′ yₑ (under-down c′ (c₁-≻ l) (row (y′ , pr) u))
      ...   | k , i , x = k , (l , i , end , yₑ , c-end , refl) , carried-proper Iσ x c-end

      up = Sim.upto S′

      P? = under? (Emb.fun em) c′ mp′

      lst′ = listing (Under A′ c′) P? (λ lt → under-down c′ lt) (filter P? (proj₁ up))
                     (λ y pl → ∈-filter⁺ P? (proj₁ (proj₂ up) y pl) pl)
                     (λ m → proj₂ (∈-filter⁻ P? {xs = proj₁ up} m) , proj₂ (proj₂ up) (proj₁ (∈-filter⁻ P? {xs = proj₁ up} m)))

      upto : Σ (List Pos) λ ls → (∀ {m e′} → Proper σ′ m e′ → Under A′ c m → m ∈ ls) × (∀ {m} → m ∈ ls → Σ (Ev (AIE X)) (Proper σ′ m))
      upto = proj₁ lst′ , (λ x u → proj₁ (proj₂ lst′) x (λ _ km → under-⊑ c′ km (row x u))) , proj₂ (proj₂ lst′)

  -- THE RUN, given its late pins.
  run : Lates M L (Proper σ) (Proper σ′) → Run AShows AShown M L (Proper σ) (Proper σ′)
  run lt = record
    { Img     = Img′
    ; img-fun = img-fun′
    ; ext     = ext′
    ; sim     = sim′
    ; late    = lt
    ; anchor  = λ A′ inc em {k} x ce Lk lk → R.anchor A′ inc em (proj₁ x) ce Lk (lb-own x (inj₂ (⊑-refl k)) lk)
    }

------------------------------------------------------------------------
-- The annotated source

module AnnRun {Γ X} n (S : Obs Timeline Γ (IE X)) (env : DenEnv Γ) (genv : GoodEnv env) (q : Pos) (ok : Ok (Hots env) q)
              {H p} {σ : EmissionSet X} (Iσ : InvAt H p σ) {M : PMap} {L : PMap → Maybe Pos → Set}
              (R : Run Shows Shown M L σ (Ann.σₑ n S env genv q ok))
              (need-row : ∀ {A′ c k e} → Proper σ k e → Upto c k → L A′ c → L A′ (just k)) where

  open Ann n S env genv q ok using (σₑ; σ′; Iₑ; Iσ′; w; val→; end→; val←; end←; module Over)

  postulate
    -- THE ANNOTATED SOURCE'S LATE PINS, listed: each told pin is a source
    -- row's, so the source's late pins and its rows list them.
    ann-late : Lates M L (Proper σ) (Proper σ′)

  -- THE ANNOTATED SOURCE RUNS WHAT ITS SOURCE RUNS.
  run : Run AShows AShown M L (Proper σ) (Proper σ′)
  run = Annotated.run σₑ σ′ (InvAt.func Iₑ) Iσ′ w val→ end→ val← end←
          (λ P P? down ks cov bk → Over.listing P P? down ks cov bk) Iσ R (λ {A′} {c} {k} {e} → need-row {A′} {c} {k} {e}) ann-late
