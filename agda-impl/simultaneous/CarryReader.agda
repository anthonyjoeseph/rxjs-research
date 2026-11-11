{-# OPTIONS --guardedness #-}

-- A READER CARRIES ITS HOT.  The plain reader of a bound hot shows each
-- row of the hot past its subscription, joined under it; the elaborated
-- reader reads the annotated hot so, then folds `joinStep` over what it
-- reads and sends each fold's emits, a reader joining late sending the
-- routes the hot holds first.  Every emit the annotated hot shows, the
-- reader sends, so the reader carries what the hot's carry carries.
--
-- The map grows by the reader's joins: each row of the hot past the
-- subscription, joined under it, put on its carrier joined under the
-- elaborated subscription; and the late end on the late end.  A hot row
-- holds the joins of every reader of it in their subscriptions' order
-- (`simultaneous.Carry.Joins`), so the map stays an embedding.
module simultaneous.CarryReader where

open import Data.Bool using (true)
open import Data.Bool.Properties using (T?)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; filter)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-filter⁺; ∈-filter⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.All using (lookup; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Tree using (connected; mergeᶠ)
open import denotation.Position using (Pos; ix; sub; last; _⊕_; _<ᵖ_; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Den; hot; coldAt; enter; Proper; DenEnv; Few;
  Reach; Truncate; Rejoin; shown; heard; ended; late; _≺_; _≼_; approx; module Op)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-trans; ≺-≼-≺; ≺-ext; ≺→≼; ≼-refl; ≼-trans; ≼-split; entered-few)
open import denotation.Laws.Worlds using (Hots; Ok; InvAt; full; _⊑_; ⊑-refl; ⊑-≼; ⊑-snoc⁺; ⊕-identityʳ; ⊕-injˡ; ⊕-injʳ)
open import denotation.Laws.Count using (⊑?)
open import simultaneous.SObs using (module Elaborate)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.Readings using (instantOf; parent; parent-snoc)
open import simultaneous.Attribution using (Live; Shown; Match; Every; One; Reads)
open import simultaneous.Listing using (Listed)
open import simultaneous.Carry using (PMap; _∪ᴹ_; _⊆ᴹ_; Emb; Fresh; Within; Bare; CarryAt; Carry; carry; EnvRel; Bound; HotsListed;
  NotHot; BoundRow; Joins; Apart; annValues; Whole; Near; IntoAt; module Mono; apart; instant-⊕; listed↓; listed-≼; hots-at; bound-hot)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) using (IE; AIE; elab; annotate; joinStep)

-- The elaborated reader's run over a handle: the fold of `joinStep`,
-- each fold's emits sent.
Reading : ∀ {X} → Den (AIE X) → Den (IE X)
Reading d = Op.flatMap (mergeᶠ nothing) (λ x → Op.of (proj₂ x)) (Op.scan joinStep (true , []) d)

-- THE READER'S SENDING carries what its reading carries: a fold's emits
-- are the emit it folds in, past the routes a late reader joins.
postulate
  read-post : ∀ {X : Set} {M : PMap} {HP HE LP H : Pos → Set} {t : EmissionSet X} {d′ : Den (AIE X)} {s s′}
            → InvAt H s′ (enter d′ s′) → CarryAt annValues M HP HE LP t (enter d′ s′) s s′
            → CarryAt valuesOf M HP HE LP t (enter (Reading d′) s′) s s′

-- A binder's hot, plain and annotated.
HotOf : ∀ {M₀ LP X} {d : Den X} {d′ : Den (AIE X)} → Bound M₀ LP d d′ → EmissionSet X
HotOf b = enter (approx (Bound.m b) (Bound.src b) (Bound.envP b)) (Bound.at b ⊕ [ ix 1 ])

HotOf′ : ∀ {M₀ LP X} {d : Den X} {d′ : Den (AIE X)} → Bound M₀ LP d d′ → EmissionSet (AIE X)
HotOf′ b = enter (approx (Bound.m b) (annotate (elab (Bound.σ b) (Bound.src b))) (Bound.envE b)) (Bound.at′ b ⊕ [ ix 1 ])

------------------------------------------------------------------------
-- Rejoined rows

private
  -- No row of `S` lies strictly under another.
  Flat : ∀ {A} → EmissionSet A → Set
  Flat S = ∀ {y e l ys e′} → S y e → S (y ⊕ (l ∷ ys)) e′ → ⊥

  -- Two rows of a flat set, one before the other, are apart.
  nest : ∀ {A} {S : EmissionSet A} → Flat S → ∀ {x y e e′} → S x e → S y e′ → x ≺ y → ¬ (x ⊑ y)
  nest fl {x} sx sy xy ([] , refl) = ≺-irrefl {x} (subst (x ≺_) (⊕-identityʳ x) xy)
  nest fl sx sy xy (l ∷ ys , refl) = fl sx sy

  -- Joined at one label, the order read back.
  back : ∀ x y {a} → (x ⊕ [ a ]) ≺ (y ⊕ [ a ]) → (y ≺ x → ¬ (y ⊑ x)) → x ≺ y
  back x y {a} h ny with T? (x <ᵖ y)
  ... | yes xy = xy
  ... | no nxy with ≼-split {y} {x} nxy
  ...   | inj₂ refl = ⊥-elim (≺-irrefl {x ⊕ [ a ]} h)
  ...   | inj₁ yx = ⊥-elim (≺-irrefl {x ⊕ [ a ]} (≺-trans {x ⊕ [ a ]} {y ⊕ [ a ]} {x ⊕ [ a ]} h (apart yx (ny yx) [ a ] [ a ])))

  few-reach : ∀ {A} {S : EmissionSet A} {q e} → Few S q → Reach S q e
  few-reach (ks , F) = ks , λ r h _ → F r h

  -- What a joiner hears of a row: a pin as a skip.
  rjEv : ∀ {A} → Ev A → Ev A
  rjEv (out x) = out x
  rjEv skip    = skip
  rjEv end     = end
  rjEv (pin _) = skip

  rjUnp : ∀ {A} (e : Ev A) → Unpinned (rjEv e)
  rjUnp (out _) = tt
  rjUnp skip    = tt
  rjUnp end     = tt
  rjUnp (pin _) = tt

  rjRow : ∀ {A} {S : EmissionSet A} {j q e} → Proper S q e → j ≺ q → Rejoin j (Proper S) (q ⊕ [ sub j ]) (rjEv e)
  rjRow {e = out _} r h = shown r tt h
  rjRow {e = skip}  r h = shown r tt h
  rjRow {e = end}   r h = ended r h
  rjRow {e = pin _} r h = heard r h

  -- Before a joined row, the joined rows before its row, and the late end.
  rejoin-few : ∀ {A} {S : EmissionSet A} {j q e} → Flat S → S q e → Few S q → Few (Rejoin j (Proper S)) (q ⊕ [ sub j ])
  rejoin-few {S = S} {j} {q} fl sq (ks , F) = L.map (_⊕ [ sub j ]) ks ++ [ j ⊕ [ last ] ] , pick
    where
      pick : ∀ {k e′} → Rejoin j (Proper S) k e′ → k ≺ (q ⊕ [ sub j ]) → k ∈ L.map (_⊕ [ sub j ]) ks ++ [ j ⊕ [ last ] ]
      pick (shown {q′} r _ _) h = ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub j ]) (F (proj₁ r) (back q′ q h (nest {S = S} fl sq (proj₁ r)))))
      pick (heard {q′} r _)   h = ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub j ]) (F (proj₁ r) (back q′ q h (nest {S = S} fl sq (proj₁ r)))))
      pick (ended {q′} r _)   h = ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub j ]) (F (proj₁ r) (back q′ q h (nest {S = S} fl sq (proj₁ r)))))
      pick (late _ _)         _ = ∈-++⁺ʳ (L.map (_⊕ [ sub j ]) ks) (here refl)

  -- Past an end at or before the subscription, nothing before the late end.
  late-none : ∀ {A} {S : EmissionSet A} {j c r e} → Proper S c end → c ≼ j → Rejoin j (Proper S) r e → r ≺ (j ⊕ [ last ]) → ⊥
  late-none {j = j} {c} (sc , _) cj (shown {q} (_ , lv) _ jq) _ = cj (≺-≼-≺ {j} {q} {c} jq (lv sc))
  late-none {j = j} {c} (sc , _) cj (heard {q} (_ , lv) jq)   _ = cj (≺-≼-≺ {j} {q} {c} jq (lv sc))
  late-none {j = j} {c} (sc , _) cj (ended {q} (_ , lv) jq)   _ = cj (≺-≼-≺ {j} {q} {c} jq (lv sc))
  late-none {j = j} _ _ (late _ _) h = ≺-irrefl {j ⊕ [ last ]} h

  -- A proper row listed, joined past the subscription: its joined rows listed.
  rejoin-listed : ∀ {A} {S : EmissionSet A} {j l₀ e₀} → Flat S → Proper S l₀ e₀ → j ≺ l₀ → Listed S l₀
                → Listed (Truncate (Rejoin j (Proper S))) (l₀ ⊕ [ sub j ])
  rejoin-listed {S = S} {j} {l₀} fl (sl , lv) jl (ks , F , B) = cand , (λ r h → pick (proj₁ r) h) , out′
    where
      cand : List Pos
      cand = L.map (_⊕ [ sub j ]) (filter (λ k → T? (j <ᵖ k)) ks)

      at : ∀ {q e′} → S q e′ → j ≺ q → (q ⊕ [ sub j ]) ≺ (l₀ ⊕ [ sub j ]) → q ⊕ [ sub j ] ∈ cand
      at {q} sq jq h = ∈-map⁺ (_⊕ [ sub j ]) (∈-filter⁺ (λ k → T? (j <ᵖ k)) (F sq (back q l₀ h (nest {S = S} fl sl sq))) jq)

      pick : ∀ {k e′} → Rejoin j (Proper S) k e′ → k ≺ (l₀ ⊕ [ sub j ]) → k ∈ cand
      pick (shown r _ jq) h = at (proj₁ r) jq h
      pick (heard r jq)   h = at (proj₁ r) jq h
      pick (ended r jq)   h = at (proj₁ r) jq h
      pick (late {c} r cj) _ = ⊥-elim (cj (≺-≼-≺ {j} {l₀} {c} jl (lv (proj₁ r))))

      out′ : ∀ {x} → x ∈ cand → x ≺ (l₀ ⊕ [ sub j ]) × Σ _ (Truncate (Rejoin j (Proper S)) x)
      out′ m with ∈-map⁻ (_⊕ [ sub j ]) m
      ... | k , mk , refl with ∈-filter⁻ (λ k → T? (j <ᵖ k)) mk
      ...   | mk′ , jk with B mk′
      ...     | kl , e , sk =
        kx , rjEv e , rjRow (sk , λ {c} tc → ≺→≼ {k} {c} (≺-≼-≺ {k} {l₀} {c} kl (lv tc))) jk , cand , λ {y} r h _ → pick r (≺-trans {y} {k ⊕ [ sub j ]} {l₀ ⊕ [ sub j ]} h kx)
        where
          kx : (k ⊕ [ sub j ]) ≺ (l₀ ⊕ [ sub j ])
          kx = apart {k} {l₀} kl (nest {S = S} fl sk sl kl) [ sub j ] [ sub j ]

  -- Every hot of an environment listed: the one at a handle.
  listed-at : ∀ {Γ} (env : DenEnv Γ) {Y} (j : Y ∈ Γ) {t : EmissionSet Y} → lookup env j ≡ hot t → ∀ {q} → HotsListed env q → Listed t q
  listed-at (hot _ ∷ _)    (here refl) refl (L , _) = L
  listed-at (coldAt _ ∷ _) (here refl) ()   _
  listed-at (hot _ ∷ ρ)    (there j)   e    (_ , R) = listed-at ρ j e R
  listed-at (coldAt _ ∷ ρ) (there j)   e    R       = listed-at ρ j e R

  -- Listed proper up to a proper row: listed.
  proper-listed : ∀ {A} {S : EmissionSet A} {q} → Listed (Proper S) q → (∀ {c} → S c end → q ≼ c) → Listed S q
  proper-listed {q = q} (ks , F , B) lv =
    ks , (λ {k} r kq → F (r , λ {c} tc → ≺→≼ {k} {c} (≺-≼-≺ {k} {q} {c} kq (lv tc))) kq) , λ m → let (kq , e , r) = B m in kq , e , proj₁ r

  -- The rows of a reading, each named by its hot row.
  one : ∀ {A} {S : EmissionSet A} {j y e} → Rejoin j S y e → List Pos
  one (shown {q} _ _ _) = [ q ]
  one (heard {q} _ _)   = [ q ]
  one (ended {c} _ _)   = [ c ]
  one (late _ _)        = []

  last-sub : ∀ {x} → last ≡ sub x → ⊥
  last-sub ()

  one-in : ∀ {A} {S : EmissionSet A} {j y e q} (r : Rejoin j S y e) → y ≡ q ⊕ [ sub j ] → q ∈ one r
  one-in {q = q} (shown {q′} _ _ _) eq = here (⊕-injˡ q q′ (sym eq))
  one-in {q = q} (heard {q′} _ _)   eq = here (⊕-injˡ q q′ (sym eq))
  one-in {q = q} (ended {q′} _ _)   eq = here (⊕-injˡ q q′ (sym eq))
  one-in {j = j} {q = q} (late _ _) eq = ⊥-elim (last-sub (⊕-injʳ j q eq))

  one-out : ∀ {A} {S : EmissionSet A} {j y e q} (r : Rejoin j S y e) → q ∈ one r → Σ _ (S q)
  one-out (shown r _ _) (here refl) = _ , r
  one-out (heard r _)   (here refl) = _ , r
  one-out (ended r _)   (here refl) = _ , r
  one-out (late _ _)    ()

  djs : ∀ {A} {S : EmissionSet A} {j} (xs : List Pos) → (∀ {x} → x ∈ xs → Σ _ (Truncate (Rejoin j S) x)) → List Pos
  djs []       g = []
  djs (x ∷ xs) g = one (proj₁ (proj₂ (g (here refl)))) ++ djs xs (λ m → g (there m))

  djs-in : ∀ {A} {S : EmissionSet A} {j q} (xs : List Pos) (g : ∀ {x} → x ∈ xs → Σ _ (Truncate (Rejoin j S) x))
         → q ⊕ [ sub j ] ∈ xs → q ∈ djs xs g
  djs-in (x ∷ xs) g (here refl) = ∈-++⁺ˡ (one-in (proj₁ (proj₂ (g (here refl)))) refl)
  djs-in (x ∷ xs) g (there m)   = ∈-++⁺ʳ (one (proj₁ (proj₂ (g (here refl))))) (djs-in xs (λ m′ → g (there m′)) m)

  djs-out : ∀ {A} {S : EmissionSet A} {j q} (xs : List Pos) (g : ∀ {x} → x ∈ xs → Σ _ (Truncate (Rejoin j S) x))
          → q ∈ djs xs g → Σ _ (S q)
  djs-out (x ∷ xs) g m with ∈-++⁻ (one (proj₁ (proj₂ (g (here refl))))) m
  ... | inj₁ m′ = one-out (proj₁ (proj₂ (g (here refl)))) m′
  ... | inj₂ m′ = djs-out xs (λ m″ → g (there m″)) m′

  -- A shown row is shown on the other side; a skip is not.
  mt-rj : ∀ {X} {e : Ev X} {e′ : Ev (AIE X)} → Unpinned e → Match Every (One annValues) (Reads annValues) e e′
        → Match Every (One annValues) (Reads annValues) e (rjEv e′)
  mt-rj {e′ = out _} _ m = m
  mt-rj {e′ = skip}  _ m = m
  mt-rj {e′ = end}   _ m = m
  mt-rj {e = out _} {e′ = pin _} _ (c , _) with c tt
  ... | _ , () , _
  mt-rj {e = skip}  {e′ = pin _} _ _ = (λ ()) , λ _ ()
  mt-rj {e = end}   {e′ = pin _} _ (c , _) with c tt
  ... | ()
  mt-rj {e = pin _} {e′ = pin _} () _

  shown-unp : ∀ {X} {e : Ev X} {e′ : Ev (AIE X)} → Shown Every e → Match Every (One annValues) (Reads annValues) e e′ → Unpinned e′
  shown-unp {e = out _} _ (c , _) with c tt
  ... | _ , refl , _ = tt
  shown-unp {e = end}   _ (c , _) with c tt
  ... | refl = tt
  shown-unp {e = skip}  () _
  shown-unp {e = pin _} () _

  out-of : ∀ {X} {e₀ : Ev X} {x} → Match Every (One annValues) (Reads annValues) e₀ (out x) → One annValues x → Σ X λ a → e₀ ≡ out a
  out-of {e₀ = out a} _ _ = a , refl
  out-of {e₀ = skip}  (_ , n) sh = ⊥-elim (n (λ ()) sh)
  out-of {e₀ = pin _} (_ , n) sh = ⊥-elim (n (λ ()) sh)
  out-of {e₀ = end}   (c , _) _ with c tt
  ... | ()

  end-of : ∀ {X} {e₀ : Ev X} → Match Every (One annValues) (Reads annValues) e₀ (end {A = AIE X}) → e₀ ≡ end
  end-of {e₀ = out _} (c , _) with c tt
  ... | _ , () , _
  end-of {e₀ = end}   _ = refl
  end-of {e₀ = skip}  (_ , n) = ⊥-elim (n (λ ()) tt)
  end-of {e₀ = pin _} (_ , n) = ⊥-elim (n (λ ()) tt)


------------------------------------------------------------------------
-- One reader

-- One reader of the binder `i`, subscribed at `p` and at its image `p′`.
module Read {Γ Δ} {M₀ : PMap} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {envP : DenEnv Γ} {envE : DenEnv Δ}
            (hm : Emb M₀) (er : EnvRel M₀ ρ envP envE) (jn : Joins ρ envP envE er M₀) (ap : Apart envP)
            {X} (i : X ∈ Γ) {p p′} (m₀ : M₀ p p′) (okP : Ok (Hots envP) p) (okE : Ok (Hots envE) p′)
            (nh : NotHot (Hots envP) p) (fr : Fresh (Hots envP) M₀ p) where
  private
    module C = CarryAt (Bound.carried (er i))
    module VP = InvAt (Bound.invP (er i))
    module VE = InvAt (Bound.invE (er i))

  T₀ : EmissionSet X
  T₀ = HotOf (er i)

  T₀′ : EmissionSet (AIE X)
  T₀′ = HotOf′ (er i)

  t : EmissionSet X
  t = Truncate (Rejoin p (Proper T₀))

  u : EmissionSet (AIE X)
  u = Truncate (Rejoin p′ (Proper T₀′))

  -- The reader's joins: a hot row past the subscription, joined under it,
  -- on its carrier joined under the image; and the late end.
  R : PMap
  R x y = (Σ Pos λ q → Σ Pos λ l → BoundRow (er i) q × C.Img q l × p ≺ q × x ≡ q ⊕ [ sub p ] × y ≡ l ⊕ [ sub p′ ])
        ⊎ (x ≡ p ⊕ [ last ] × y ≡ p′ ⊕ [ last ])

  M : PMap
  M = M₀ ∪ᴹ R

  -- A joined row on its joined carrier, a row of the annotated hot; the
  -- late end on the late end, the hot ended by the subscription.
  Img : Pos → Pos → Set
  Img k l = (Σ Pos λ q → Σ Pos λ l₀ → BoundRow (er i) q × C.Img q l₀ × Σ (Ev (AIE X)) (Proper T₀′ l₀) × p ≺ q
              × k ≡ q ⊕ [ sub p ] × l ≡ l₀ ⊕ [ sub p′ ])
          ⊎ (k ≡ p ⊕ [ last ] × l ≡ p′ ⊕ [ last ] × Σ Pos λ c₀ → Proper T₀ c₀ end × c₀ ≼ p)

  -- A hot row carried into its instant, on the carrier's joined row.
  PB : Pos → Pos → Set
  PB k l = Σ Pos λ q → Σ Pos λ l₀ → C.PB q l₀ × p ≺ q × k ≡ q ⊕ [ sub p ] × l ≡ l₀ ⊕ [ sub p′ ]

  postulate
    reader-emb      : Emb M
    reader-within   : Within (Hots envP) M₀ M p
    reader-bare     : Bare M t
    reader-joins    : Joins ρ envP envE er M
    -- THE READER HEARS WHERE THE HOT IS CARRIED INTO ITS INSTANT: a row of
    -- the hot past the subscription that is carried into its instant, the
    -- reader showing it listed, has its carrier past the image and joined
    -- there by the annotated reader, listed.
    pb-heard        : ∀ {q l₀ e} → Proper T₀ q e → p ≺ q → C.PB q l₀ → Listed t (q ⊕ [ sub p ])
                    → Σ (Ev (AIE X)) (u (l₀ ⊕ [ sub p′ ])) × Listed u (l₀ ⊕ [ sub p′ ])

  private
    flatP : Flat T₀
    flatP = VP.flat

    flatE : Flat T₀′
    flatE = VE.flat

    endP : ∀ {c c′} → T₀ c end → T₀ c′ end → c ≼ c′
    endP tc tc′ c′c with VP.quiet tc′ tc c′c
    ... | _ , () , _

    endE : ∀ {c c′} → T₀′ c end → T₀′ c′ end → c ≼ c′
    endE tc tc′ c′c with VE.quiet tc′ tc c′c
    ... | _ , () , _

    fewP : ∀ {q e} → T₀ q e → Unpinned e → Few T₀ q
    fewP tq un = entered-few (approx (Bound.m (er i)) (Bound.src (er i)) (Bound.envP (er i))) (Bound.at (er i) ⊕ [ ix 1 ]) (full un) tq

    fewE : ∀ {l e} → T₀′ l e → Unpinned e → Few T₀′ l
    fewE tl un = entered-few (approx (Bound.m (er i)) (annotate (elab (Bound.σ (er i)) (Bound.src (er i)))) (Bound.envE (er i)))
                             (Bound.at′ (er i) ⊕ [ ix 1 ]) (full un) tl

    hotP : ∀ {q e} → Proper T₀ q e → Hots envP q
    hotP tq = bound-hot {ρ = ρ} envP {envE = envE} er i (_ , tq)

    hotE : ∀ {l e} → Proper T₀′ l e → Hots envE l
    hotE tl = hots-at envE (ρ (∈-map⁺ AIE i)) (Bound.isE (er i)) tl

    lstP : ∀ {q e k} → Proper T₀ q e → q ≼ k → HotsListed envP k → Listed T₀ q
    lstP (_ , lv) qk lp = proper-listed (listed-≼ (listed-at envP i (Bound.isP (er i)) lp) qk) lv

    lsts : ∀ {q k} → q ≼ k → HotsListed envP k → HotsListed (Bound.envP (er i)) q
    lsts qk lp = Bound.lists (er i) (listed↓ envP qk lp)

    liveE : ∀ {q l₀ e} → C.Img q l₀ → Proper T₀ q e → ∀ {c} → T₀′ c end → l₀ ≼ c
    liveE ci tq {c} = C.live ci (λ {c₁} → proj₂ tq {c₁}) {c}

    sub≼ : ∀ q {a} → q ≼ (q ⊕ [ a ])
    sub≼ q = ⊑-≼ (⊑-snoc⁺ q)

    module CM = Mono hm flatP (Bound.carried (er i))

    -- Carried past the subscription: past its image.
    after′ : ∀ {q l₀} → C.Img q l₀ → p ≺ q → p′ ≺ l₀
    after′ {q} {l₀} ci pq with C.ext ci
    ... | y , my , yl = ≺-≼-≺ {p′} {y} {l₀} (Emb.mono hm m₀ my pq) (⊑-≼ yl)

    -- Carried before the subscription: before its image.
    pre : ∀ {q l₀ e} → Proper T₀ q e → C.Img q l₀ → q ≺ p → l₀ ≺ p′
    pre {q} {l₀} tq ci qp with ⊑? q p
    ... | yes ([] , e) = ⊥-elim (≺-irrefl {q} (subst (q ≺_) (trans e (⊕-identityʳ q)) qp))
    ... | yes (a ∷ σ , e) with jn i m₀ (_ , tq) e
    ...   | _ , _ , e′ , _ , L , ci′ , Lp with C.img-fun ci ci′
    ...     | refl = ≺-≼-≺ {L} {L ⊕ [ sub e′ ]} {p′} (≺-ext L []) (⊑-≼ Lp)
    pre {q} {l₀} tq ci qp | no nq with C.ext ci
    ... | y , my , (zs , refl) =
      subst (λ z → (y ⊕ zs) ≺ z) (⊕-identityʳ p′) (apart (Emb.mono hm my m₀ qp) (λ yp → nq (Emb.reflect hm my m₀ yp)) zs [])

    before : ∀ {q l₀ e} → Proper T₀ q e → C.Img q l₀ → p′ ≺ l₀ → p ≺ q
    before {q} {l₀} tq ci pl with T? (p <ᵖ q)
    ... | yes pq = pq
    ... | no npq with ≼-split {q} {p} npq
    ...   | inj₂ refl = ⊥-elim (nh (hotP tq) (⊑-refl q))
    ...   | inj₁ qp = ⊥-elim (≺-irrefl {l₀} (≺-trans {l₀} {p′} {l₀} (pre tq ci qp) pl))

    late-at : ∀ {c c′ e} → Proper T₀ c e → C.Img c c′ → c ≼ p → c′ ≼ p′
    late-at {c} {c′} tc ci cp with ≼-split {c} {p} cp
    ... | inj₂ refl = ⊥-elim (nh (hotP tc) (⊑-refl c))
    ... | inj₁ cp′ = ≺→≼ {c′} {p′} (pre tc ci cp′)

    -- A plain row whose carrier lives lives.
    live-back : ∀ {q l₀ e} → C.Img q l₀ → T₀ q e → (∀ {c} → T₀′ c end → l₀ ≼ c) → ∀ {c} → T₀ c end → q ≼ c
    live-back ci tq lv tc cq = C.img¬¬ tc tt (endP tc) (fewP tc tt) λ where
      (inj₂ ())
      (inj₁ (c′ , ci′ , e′ , uc , mt)) → lv (subst (T₀′ c′) (proj₁ mt tt) uc) (CM.img-mono ci′ ci cq)

    -- A carried row and its joined carrier.
    joined : ∀ {q e l₀ e′} → Proper T₀ q e → p ≺ q → C.Img q l₀ → T₀′ l₀ e′ → Few T₀′ l₀
           → Img (q ⊕ [ sub p ]) (l₀ ⊕ [ sub p′ ]) × u (l₀ ⊕ [ sub p′ ]) (rjEv e′)
    joined {q} {l₀ = l₀} {e′} tq pq ci ue fw =
      inj₁ (q , l₀ , (_ , tq) , ci , (e′ , rp) , pq , refl , refl) , rjRow rp pl , few-reach {e = rjEv e′} (rejoin-few flatE ue fw)
      where
        rp : Proper T₀′ l₀ e′
        rp = ue , (λ {c₈} → liveE ci tq {c₈})
        pl : p′ ≺ l₀
        pl = after′ ci pq

    -- The late end, on the late end.
    late-row : ∀ {c c′} → Proper T₀ c end → c ≼ p → C.Img c c′ → T₀′ c′ end → Img (p ⊕ [ last ]) (p′ ⊕ [ last ]) × u (p′ ⊕ [ last ]) end
    late-row tc cp ci uc = inj₂ (refl , refl , _ , tc , cp) , late rc (late-at tc ci cp) , few-reach {e = end} ([] , λ r h → ⊥-elim (late-none rc (late-at tc ci cp) r h))
      where rc = uc , (λ {c₈} → liveE ci tc {c₈})

    late-listed : ∀ {c c′} → Proper T₀ c end → c ≼ p → C.Img c c′ → T₀′ c′ end → Listed u (p′ ⊕ [ last ])
    late-listed tc cp ci uc = [] , (λ r h → ⊥-elim (late-none (uc , (λ {c₈} → liveE ci tc {c₈})) (late-at tc ci cp) (proj₁ r) h)) , λ ()

    heard-into : ∀ {q l₀ e} → Proper T₀ q e → p ≺ q → C.PB q l₀ → Listed t (q ⊕ [ sub p ]) → IntoAt Img u PB (Hots envP) p (q ⊕ [ sub p ])
    heard-into {q} {l₀} tq pq pb L with pb-heard tq pq pb L
    ... | ul , Lu = (l₀ ⊕ [ sub p′ ] , ul , Lu , (q , l₀ , pb , pq , refl , refl)) , inj₂ (inj₂ (q , hotP tq , sym (instant-⊕ q [ sub p ])))

    MatchR : Ev X → Ev (AIE X) → Set
    MatchR = Match Every (One annValues) (Reads annValues)

    ext : ∀ {k l} → Img k l → Σ Pos λ y → M k y × y ⊑ l
    ext (inj₁ (q , l₀ , br , ci , _ , pq , refl , refl)) = _ , inj₂ (inj₁ (q , l₀ , br , ci , pq , refl , refl)) , ⊑-refl _
    ext (inj₂ (refl , refl , _))                         = _ , inj₂ (inj₂ (refl , refl)) , ⊑-refl _

    pb-fib : ∀ {l₀} → (Σ (List Pos) λ ks → ∀ {q} → C.PB q l₀ → q ∈ ks) → Σ (List Pos) λ ks → ∀ {k} → PB k (l₀ ⊕ [ sub p′ ]) → k ∈ ks
    pb-fib {l₀} (ks , F) = L.map (_⊕ [ sub p ]) ks , λ { (q , l₁ , pb , _ , refl , e) → ∈-map⁺ (_⊕ [ sub p ]) (F (subst (C.PB q) (⊕-injˡ l₁ l₀ (sym e)) pb)) }

    pb-few : ∀ {l e} → u l e → Σ (List Pos) λ ks → ∀ {k} → PB k l → k ∈ ks
    pb-few (shown r _ _ , _) = pb-fib (C.pb-few (proj₁ r))
    pb-few (heard r _ , _)   = pb-fib (C.pb-few (proj₁ r))
    pb-few (ended r _ , _)   = pb-fib (C.pb-few (proj₁ r))
    pb-few (late _ _ , _)    = [] , λ { (_ , l₁ , _ , _ , _ , e) → ⊥-elim (last-sub (⊕-injʳ p′ l₁ e)) }

    -- What the carry makes of a hot row, and what the reader makes of its joined row.
    Carried : Pos → Ev X → Set
    Carried q e = (Σ Pos λ l → C.Img q l × Σ (Ev (AIE X)) λ e′ → T₀′ l e′ × Listed T₀′ l × MatchR e e′)
                ⊎ (e ≡ skip × IntoAt C.Img T₀′ C.PB (Hots (Bound.envP (er i))) (Bound.at (er i) ⊕ [ ix 1 ]) q)

    Out : Pos → Ev X → Set
    Out k e = (Σ Pos λ l → Img k l × Σ (Ev (AIE X)) λ e′ → u l e′ × Listed u l × MatchR e e′)
            ⊎ (e ≡ skip × IntoAt Img u PB (Hots envP) p k)

    img-joined : ∀ {q e l₀ e′} → Proper T₀ q e → p ≺ q → C.Img q l₀ → T₀′ l₀ e′ → Listed T₀′ l₀ → MatchR e (rjEv e′)
               → Out (q ⊕ [ sub p ]) e
    img-joined tq pq ci ue L′ mt = inj₁ (_ , proj₁ J , _ , proj₂ J , rejoin-listed flatE (ue , (λ {c₈} → liveE ci tq {c₈})) (after′ ci pq) L′ , mt)
      where J = joined tq pq ci ue (proj₁ L′ , proj₁ (proj₂ L′))

    img-shown : ∀ {q e} → Proper T₀ q e → p ≺ q → Unpinned e → Listed t (q ⊕ [ sub p ]) → Carried q e → Out (q ⊕ [ sub p ]) e
    img-shown tq pq un L (inj₂ (es , (_ , _ , _ , pb) , _)) = inj₂ (es , heard-into tq pq pb L)
    img-shown tq pq un L (inj₁ (l₀ , ci , e′ , ue , L′ , mt)) = img-joined tq pq ci ue L′ (mt-rj un mt)

    img-ended : ∀ {c} → Proper T₀ c end → p ≺ c → Carried c end → Out (c ⊕ [ sub p ]) end
    img-ended tc pc (inj₂ (() , _))
    img-ended tc pc (inj₁ (l₀ , ci , e′ , ue , L′ , mt)) = img-joined tc pc ci ue L′ (mt-rj tt mt)

    img-late : ∀ {c} → Proper T₀ c end → c ≼ p → Carried c end → Out (p ⊕ [ last ]) end
    img-late tc cp (inj₂ (() , _))
    img-late {c} tc cp (inj₁ (c′ , ci , e′ , ue , L′ , mt)) =
      inj₁ (_ , proj₁ J , end , proj₂ J , late-listed tc cp ci ue′ , (λ _ → refl) , λ n′ → ⊥-elim (n′ tt))
      where
        ue′ = subst (T₀′ c′) (proj₁ mt tt) ue
        J = late-row tc cp ci ue′

    img : ∀ {k e} → t k e → Unpinned e → Live t k → Listed t k → HotsListed envP k → Out k e
    img (shown {q} tq _ pq , _) un _ L lp =
      img-shown tq pq un L (C.img (proj₁ tq) un (λ {c₉} → proj₂ tq {c₉}) (lstP tq (sub≼ q) lp) (lsts (sub≼ q) lp))
    img (heard tq pq , _) _ _ L _ =
      inj₂ (refl , heard-into tq pq (proj₁ (proj₂ (proj₂ (proj₂ (proj₁ (C.pinned (proj₁ tq) (λ {c₉} → proj₂ tq {c₉}))))))) L)
    img (ended {c} tc pc , _) _ _ _ lp =
      img-ended tc pc (C.img (proj₁ tc) tt (λ {c₉} → proj₂ tc {c₉}) (lstP tc (sub≼ c) lp) (lsts (sub≼ c) lp))
    img (late {c} tc cp , _) _ _ _ lp =
      img-late tc cp (C.img (proj₁ tc) tt (λ {c₉} → proj₂ tc {c₉}) (lstP tc cl lp) (lsts cl lp))
      where cl = ≼-trans {c} {p} {p ⊕ [ last ]} cp (sub≼ p)

    img¬¬ : ∀ {k e} → t k e → Unpinned e → Live t k → Few t k
          → ¬ ¬ ((Σ Pos λ l → Img k l × Σ (Ev (AIE X)) λ e′ → u l e′ × MatchR e e′) ⊎ e ≡ skip)
    img¬¬ (shown {e = skip} _ _ _ , _) _ _ _ n = n (inj₂ refl)
    img¬¬ (shown {e = out a} tq _ pq , _) un _ _ n = C.img¬¬ (proj₁ tq) un (λ {c₉} → proj₂ tq {c₉}) (fewP (proj₁ tq) un) λ where
      (inj₂ ())
      (inj₁ (l₀ , ci , e′ , ue , mt)) → let (im , ul) = joined tq pq ci ue (fewE ue (shown-unp tt mt)) in n (inj₁ (_ , im , _ , ul , mt-rj un mt))
    img¬¬ (shown {e = end} _ () _ , _)
    img¬¬ (shown {e = pin _} _ () _ , _)
    img¬¬ (heard _ _ , _) _ _ _ n = n (inj₂ refl)
    img¬¬ (ended tc pc , _) _ _ _ n = C.img¬¬ (proj₁ tc) tt (λ {c₉} → proj₂ tc {c₉}) (fewP (proj₁ tc) tt) λ where
      (inj₂ ())
      (inj₁ (l₀ , ci , e′ , ue , mt)) → let (im , ul) = joined tc pc ci ue (fewE ue (shown-unp tt mt)) in n (inj₁ (_ , im , _ , ul , mt-rj tt mt))
    img¬¬ (late tc cp , _) _ _ _ n = C.img¬¬ (proj₁ tc) tt (λ {c₉} → proj₂ tc {c₉}) (fewP (proj₁ tc) tt) λ where
      (inj₂ ())
      (inj₁ (c′ , ci , e′ , ue , mt)) → let (im , ul) = late-row tc cp ci (subst (T₀′ c′) (proj₁ mt tt) ue) in n (inj₁ (_ , im , end , ul , (λ _ → refl) , λ n′ → ⊥-elim (n′ tt)))

    -- What the carry shows a carrier carrying, and what the reader shows its joined row carrying.
    Shw : Pos → Ev (AIE X) → Set
    Shw l e = Σ Pos λ k → C.Img k l × Σ (Ev X) λ e₀ → T₀ k e₀ × MatchR e₀ e

    Back : Pos → Ev (AIE X) → Set
    Back l e = Σ Pos λ k → Img k l × Σ (Ev X) λ e₀ → t k e₀ × MatchR e₀ e

    shown-out′ : ∀ {l₀ x q e₀} → Proper T₀′ l₀ (out x) → p′ ≺ l₀ → C.Img q l₀ → T₀ q e₀ → MatchR e₀ (out x)
               → Σ X (λ a → e₀ ≡ out a) → Back (l₀ ⊕ [ sub p′ ]) (out x)
    shown-out′ {l₀} {q = q} r pl ci tq mt (a , refl) =
      q ⊕ [ sub p ] , inj₁ (q , l₀ , (_ , rq) , ci , (_ , r) , pq , refl , refl) , out a , (shown rq tt pq , few-reach {e = out a} (rejoin-few flatP tq (fewP tq tt))) , mt
      where
        rq : Proper T₀ q (out a)
        rq = tq , live-back ci tq (λ {c₉} → proj₂ r {c₉})
        pq : p ≺ q
        pq = before rq ci pl

    shown-out : ∀ {l₀ x} → Proper T₀′ l₀ (out x) → p′ ≺ l₀ → Shown (One annValues) (out x) → Shw l₀ (out x) → Back (l₀ ⊕ [ sub p′ ]) (out x)
    shown-out r pl sh (q , ci , e₀ , tq , mt) = shown-out′ r pl ci tq mt (out-of mt sh)

    shown-end′ : ∀ {c′ c e₀} → Proper T₀′ c′ end → p′ ≺ c′ → C.Img c c′ → T₀ c e₀ → MatchR e₀ end → e₀ ≡ end
               → Back (c′ ⊕ [ sub p′ ]) end
    shown-end′ {c′} {c} r pc′ ci tc mt refl =
      c ⊕ [ sub p ] , inj₁ (c , c′ , (end , rc) , ci , (end , r) , pc , refl , refl) , end , (ended rc pc , few-reach {e = end} (rejoin-few flatP tc (fewP tc tt))) , mt
      where
        rc : Proper T₀ c end
        rc = tc , endP tc
        pc : p ≺ c
        pc = before rc ci pc′

    shown-end : ∀ {c′} → Proper T₀′ c′ end → p′ ≺ c′ → Shw c′ end → Back (c′ ⊕ [ sub p′ ]) end
    shown-end r pc′ (c , ci , e₀ , tc , mt) = shown-end′ r pc′ ci tc mt (end-of mt)

    shown-late′ : ∀ {c′ c e₀} → Proper T₀′ c′ end → c′ ≼ p′ → C.Img c c′ → T₀ c e₀ → MatchR e₀ end → e₀ ≡ end
                → Back (p′ ⊕ [ last ]) end
    shown-late′ {c′} {c} r cp′ ci tc mt refl =
      p ⊕ [ last ] , inj₂ (refl , refl , c , rc , cp) , end , (late rc cp , few-reach {e = end} ([] , λ r′ h → ⊥-elim (late-none rc cp r′ h))) , mt
      where
        rc : Proper T₀ c end
        rc = tc , endP tc
        cp : c ≼ p
        cp h = cp′ (after′ ci h)

    shown-late : ∀ {c′} → Proper T₀′ c′ end → c′ ≼ p′ → Shw c′ end → Back (p′ ⊕ [ last ]) end
    shown-late r cp′ (c , ci , e₀ , tc , mt) = shown-late′ r cp′ ci tc mt (end-of mt)

    shown′ : ∀ {l e} → u l e → Shown (One annValues) e → Live u l → Few u l → Back l e
    shown′ (shown {e = skip} _ _ _ , _) ()
    shown′ (shown {e = out _} r _ pl , _) sh _ _ = shown-out r pl sh (C.shown (proj₁ r) sh (λ {c₉} → proj₂ r {c₉}) (fewE (proj₁ r) tt))
    shown′ (shown {e = end} _ () _ , _)
    shown′ (shown {e = pin _} _ () _ , _)
    shown′ (heard _ _ , _) ()
    shown′ (ended r pc′ , _) _ _ _ = shown-end r pc′ (C.shown (proj₁ r) tt (λ {c₉} → proj₂ r {c₉}) (fewE (proj₁ r) tt))
    shown′ (late r cp′ , _) _ _ _ = shown-late r cp′ (C.shown (proj₁ r) tt (λ {c₉} → proj₂ r {c₉}) (fewE (proj₁ r) tt))

    img-row : ∀ {k l} → Img k l → ¬ ¬ Σ (Ev X) λ e → t k e × Unpinned e
    img-row (inj₁ (q , l₀ , (e , tq) , ci , _ , pq , refl , refl)) n = n (rjEv e , (rjRow tq pq , few-reach {e = rjEv e} (rejoin-few flatP (proj₁ tq) (C.few ci))) , rjUnp e)
    img-row (inj₂ (refl , refl , c , tc , cp)) n = n (end , (late tc cp , few-reach {e = end} ([] , λ r h → ⊥-elim (late-none tc cp r h))) , tt)

    img-fun : ∀ {k l l′} → Img k l → Img k l′ → l ≡ l′
    img-fun (inj₁ (q , l₀ , _ , ci , _ , _ , refl , refl)) (inj₁ (q′ , l₁ , _ , ci′ , _ , _ , e , refl)) with ⊕-injˡ q q′ e
    ... | refl = cong (_⊕ [ sub p′ ]) (C.img-fun ci ci′)
    img-fun (inj₁ (q , _ , _ , _ , _ , _ , refl , _)) (inj₂ (e , _)) = ⊥-elim (last-sub (sym (⊕-injʳ q p e)))
    img-fun (inj₂ (refl , _)) (inj₁ (q , _ , _ , _ , _ , _ , e , _)) = ⊥-elim (last-sub (⊕-injʳ p q e))
    img-fun (inj₂ (_ , refl , _)) (inj₂ (_ , refl , _)) = refl

    place : ∀ {m e} → u m e → Live u m → Listed u m
          → instantOf m ≡ instantOf p′ ⊎ (Σ Pos λ k → Σ Pos λ l → Img k l × instantOf l ≡ instantOf m × Near u m l)
            ⊎ Σ Pos λ h → Hots envE h × instantOf h ≡ instantOf m
    place (shown {l₀} r _ _ , _) _ _ = inj₂ (inj₂ (l₀ , hotE r , sym (instant-⊕ l₀ [ sub p′ ])))
    place (heard {l₀} r _ , _)   _ _ = inj₂ (inj₂ (l₀ , hotE r , sym (instant-⊕ l₀ [ sub p′ ])))
    place (ended {l₀} r _ , _)   _ _ = inj₂ (inj₂ (l₀ , hotE r , sym (instant-⊕ l₀ [ sub p′ ])))
    place (late _ _ , _)         _ _ = inj₁ (instant-⊕ p′ [ last ])

    live : ∀ {k l} → Img k l → Live t k → Live u l
    live (inj₁ (_ , l₀ , _ , _ , (_ , rl) , _ , refl , refl)) _ (shown _ () _ , _)
    live (inj₁ (_ , l₀ , _ , _ , (_ , rl) , _ , refl , refl)) _ (ended {c′} r _ , _) with ≼-split {l₀} {c′} (proj₂ rl (proj₁ r))
    ... | inj₂ refl = ≼-refl {l₀ ⊕ [ sub p′ ]}
    ... | inj₁ lc = ≺→≼ {l₀ ⊕ [ sub p′ ]} {c′ ⊕ [ sub p′ ]} (apart {l₀} {c′} lc (nest {S = T₀′} flatE {l₀} {c′} (proj₁ rl) (proj₁ r) lc) [ sub p′ ] [ sub p′ ])
    live (inj₁ (_ , l₀ , _ , ci , (_ , rl) , pq , refl , refl)) _ (late {c′} r cp , _) _ =
      cp (≺-≼-≺ {p′} {l₀} {c′} (after′ ci pq) (proj₂ rl (proj₁ r)))
    live (inj₂ (refl , refl , _)) _ (shown _ () _ , _)
    live (inj₂ (refl , refl , _)) _ (late _ _ , _) = ≼-refl {p′ ⊕ [ last ]}
    live (inj₂ (refl , refl , c₀ , tc₀ , cp)) _ (ended {c′} r pc′ , _) _ =
      C.img¬¬ (proj₁ tc₀) tt (λ {c₉} → proj₂ tc₀ {c₉}) (fewP (proj₁ tc₀) tt) λ where
        (inj₂ ())
        (inj₁ (c₀′ , ci , e′ , uc , mt)) →
          late-at tc₀ ci cp (≺-≼-≺ {p′} {c′} {c₀′} pc′ (endE (proj₁ r) (subst (T₀′ c₀′) (proj₁ mt tt) uc)))

    few : ∀ {k l} → Img k l → Few t k
    few (inj₁ (_ , _ , (_ , tq) , ci , _ , _ , refl , refl)) with rejoin-few flatP (proj₁ tq) (C.few ci)
    ... | ks , F = ks , λ r h → F (proj₁ r) h
    few (inj₂ (refl , refl , _ , tc , cp)) = [] , λ r h → ⊥-elim (late-none tc cp (proj₁ r) h)

    -- No end plain: every row of the hot listed, before the subscription
    -- by the environment's listing, past it by the reader's.
    no-end : (∀ {c} → t c end → ⊥) → ∀ {c} → T₀ c end → ⊥
    no-end ne {c} tc with T? (p <ᵖ c)
    ... | yes pc = ne (ended (tc , endP tc) pc , few-reach {e = end} (rejoin-few flatP tc (fewP tc tt)))
    ... | no cp = ne (late (tc , endP tc) cp , few-reach {e = end} ([] , λ r h → ⊥-elim (late-none (tc , endP tc) cp r h)))

    whole-hot : Whole t → (∀ {c} → T₀ c end → ⊥) → (∀ {q} → HotsListed envP q) → Whole T₀
    whole-hot (ks , F , B) ne lp = proj₁ L₁ ++ djs ks B , pick , back′
      where
        L₁ : Listed (Proper T₀) p
        L₁ = listed-at envP i (Bound.isP (er i)) (lp {p})

        prop : ∀ {k e} → T₀ k e → Proper T₀ k e
        prop tk = tk , λ tc → ⊥-elim (ne tc)

        pick : ∀ {k e} → T₀ k e → k ∈ proj₁ L₁ ++ djs ks B
        pick {k} {e} tk with T? (k <ᵖ p)
        ... | yes kp = ∈-++⁺ˡ (proj₁ (proj₂ L₁) (prop tk) kp)
        ... | no pk with ≼-split {p} {k} pk
        ...   | inj₂ refl = ⊥-elim (nh (hotP (prop tk)) (⊑-refl p))
        ...   | inj₁ pk′ = ∈-++⁺ʳ (proj₁ L₁) (djs-in ks B (F (rjRow (prop tk) pk′ , few-reach {e = rjEv e} (rejoin-few flatP tk fk))))
          where
            fk : Few T₀ k
            fk with listed-at envP i (Bound.isP (er i)) (lp {k})
            ... | js , G , _ = js , λ r h → G (prop r) h

        back′ : ∀ {k} → k ∈ proj₁ L₁ ++ djs ks B → Σ _ (T₀ k)
        back′ m with ∈-++⁻ (proj₁ L₁) m
        ... | inj₁ m′ = let (_ , e , r) = proj₂ (proj₂ L₁) m′ in e , proj₁ r
        ... | inj₂ m′ = let (e , r) = djs-out ks B m′ in e , proj₁ r

    whole : Whole t → (∀ {c} → t c end → ⊥) → (∀ {q} → HotsListed envP q) → Σ (List Pos) λ ls → ∀ {r e} → u r e → r ∈ ls
    whole W ne lp = wh (C.whole (whole-hot W (no-end ne) lp) (no-end ne) (λ {q} → Bound.lists (er i) (lp {q})))
      where
        wh : (Σ (List Pos) λ ls → ∀ {r e} → T₀′ r e → r ∈ ls) → Σ (List Pos) λ ls → ∀ {r e} → u r e → r ∈ ls
        wh (ls , G) = L.map (_⊕ [ sub p′ ]) ls ++ [ p′ ⊕ [ last ] ] , λ where
          (shown r _ _ , _) → ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub p′ ]) (G (proj₁ r)))
          (heard r _ , _)   → ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub p′ ]) (G (proj₁ r)))
          (ended r _ , _)   → ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub p′ ]) (G (proj₁ r)))
          (late _ _ , _)    → ∈-++⁺ʳ (L.map (_⊕ [ sub p′ ]) ls) (here refl)

    bk : Pos → List Pos
    bk l = L.map (_⊕ [ sub p ]) (C.bk (parent l)) ++ [ p ⊕ [ last ] ]

    in-bk : ∀ {k l} → Img k l → k ∈ bk l
    in-bk (inj₁ (q , l₀ , _ , ci , _ , _ , refl , refl)) =
      ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub p ]) (subst (λ z → q ∈ C.bk z) (sym (parent-snoc l₀ (sub p′))) (C.in-bk ci)))
    in-bk (inj₂ (refl , refl , _)) = ∈-++⁺ʳ (L.map (_⊕ [ sub p ]) (C.bk (parent (p′ ⊕ [ last ])))) (here refl)

  -- THE READER CARRIES its hot's carry: a joined row on its joined
  -- carrier, a late end on a late end; a row the hot carries into its
  -- instant, into the instant of the hot's row.
  reader-rejoined : CarryAt annValues M (Hots envP) (Hots envE) (HotsListed envP) t u p p′
  reader-rejoined = record
    { Img = Img ; ext = ext ; PB = PB ; pb-few = pb-few ; img = img ; img¬¬ = img¬¬ ; shown = shown′ ; img-row = img-row
    ; img-fun = img-fun ; place = place ; live = live ; few = few ; whole = whole ; bk = bk ; in-bk = in-bk
    ; pinned = λ { (shown _ () _ , _) } }


------------------------------------------------------------------------
-- The former

private
  read-at : ∀ {Γ Δ} {M₀ : PMap} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {envP : DenEnv Γ} {envE : DenEnv Δ}
            (hm : Emb M₀) (er : EnvRel M₀ ρ envP envE) (jn : Joins ρ envP envE er M₀) (ap : Apart envP)
            {X} (i : X ∈ Γ) {p p′} (m₀ : M₀ p p′) (okP : Ok (Hots envP) p) (okE : Ok (Hots envE) p′)
            (nh : NotHot (Hots envP) p) (fr : Fresh (Hots envP) M₀ p) {dP : Den X} {dE : Den (AIE X)}
          → dP ≡ hot (Proper (HotOf (er i))) → dE ≡ hot (Proper (HotOf′ (er i))) → InvAt (Hots envE) p′ (enter dE p′)
          → Σ PMap λ M → M₀ ⊆ᴹ M × Emb M × Within (Hots envP) M₀ M p × Bare M (enter dP p) × Joins ρ envP envE er M
            × CarryAt valuesOf M (Hots envP) (Hots envE) (HotsListed envP) (enter dP p) (enter (Reading dE) p′) p p′
  read-at {M₀ = M₀} {ρ} {envP} {envE} hm er jn ap i m₀ okP okE nh fr refl refl Iu =
    R.M , inj₁ , R.reader-emb , R.reader-within , R.reader-bare , R.reader-joins , read-post {d′ = hot (Proper (HotOf′ (er i)))} Iu R.reader-rejoined
    where module R = Read {M₀ = M₀} {ρ = ρ} {envP = envP} {envE = envE} hm er jn ap i m₀ okP okE nh fr

-- A READER of a bound hot carries it.
carry-connected : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) → Carry m ρ (connected i)
carry-connected n ρ i = carry λ envP envE gP gE M₀ hm er jn ap p p′ m₀ okP okE nh fr →
  read-at {ρ = ρ} {envP = envP} {envE = envE} hm er jn ap i m₀ okP okE nh fr {dP = lookup envP i} {dE = lookup envE (ρ (∈-map⁺ AIE i))}
    (Bound.isP (er i)) (Bound.isE (er i)) (proj₁ (gE (ρ (∈-map⁺ AIE i))) p′ okE)
