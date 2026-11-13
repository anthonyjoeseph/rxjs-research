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

open import Data.Bool using (T; true)
open import Data.Bool.Properties using (T?; T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; filter)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-filter⁺; ∈-filter⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Function using (Equivalence; _⇔_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import denotation.Position using (Pos; Path; ix; sub; last; _⊕_; _<ᵖ_; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh; <ᵖ-part; <ᵖ-between)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Den; enter; Proper; DenEnv; Few; Truncate;
  Rejoin; shown; heard; ended; late; _≺_; _≼_; approx)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≼-or-≻; ≼-≺-≺; ≺-trans; ≺-≼-≺; ≺-ext; ≺→≼; ≼-refl; ≼-trans; ≼-split; entered-few)
open import denotation.Laws.Worlds using (Hots; Ok; InvAt; full; _⊑_; ⊑-refl; ⊑-≼; ⊑-cmp; ext≢; ⊑-snoc; ⊑-snoc⁺; ⊑-trans; ⊕-assoc; ⊕-identityʳ; ⊕-injˡ; ⊕-injʳ;
  W⁼; here; inW; join; step; plain-last; conv)
open import denotation.Laws.Count using (⊑?)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf; parent; parent-snoc)
open import simultaneous.Attribution using (Live; Shown; Match; Every; One; Reads)
open import simultaneous.Listing using (Listed)
open import simultaneous.CarryBase using (From; InOrder; PMap; _∪ᴹ_; Emb; Fresh; CarryAt; Whole; Near; IntoAt; module Mono; apart; instant-⊕; listed-≼; sub-listed; Ahead; ahead-over; ahead-under)
open import simultaneous.Carry using (Within; Bare; EnvRel; Bound; HotsListed; NotHot; BoundRow; Joins; Apart; annValues; listed↓; hots-at; bound-hot; BoundSrc; Rows; rows-at)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; annotate)

open import simultaneous.Rejoined using (Flat; split-at; same-hot; nest; joined-back; few-reach; rjEv; rjUnp; rjRow; rejoin-few;
  late-none; rejoin-listed; listed-at; proper-listed; last-sub; djs; djs-in; djs-out; mt-rj;
  shown-unp; out-of; end-of)

-- A binder's annotated hot.
HotOf′ : ∀ {M₀ LP X} {d : Den X} {d′ : Den (AIE X)} → Bound M₀ LP d d′ → EmissionSet (AIE X)
HotOf′ b = enter (approx (Bound.m b) (annotate (elab (Bound.σ b) (Bound.src b))) (Bound.envE b)) (Bound.at′ b ⊕ [ ix 1 ])

------------------------------------------------------------------------
-- Joining any hot

-- Not the head's end: the tail's.
end-rest : ∀ {A} {S : EmissionSet A} → (∀ {y e e′} → S y e → S y e′ → e ≡ e′)
         → ∀ {x js e c} → S x e → (e ≡ end → ⊥) → S c end → c ∈ x ∷ js → c ∈ js
end-rest fn tx ne tc (here refl) = ⊥-elim (ne (fn tx tc))
end-rest fn tx ne tc (there m)   = m

-- An end among the rows listed before a row, or none before it.
end-among : ∀ {A} {S : EmissionSet A} → (∀ {y e e′} → S y e → S y e′ → e ≡ e′) → ∀ {l₀} (js : List Pos)
          → (∀ {k} → k ∈ js → k ≺ l₀ × Σ _ (S k)) → (∀ {c} → S c end → c ≺ l₀ → c ∈ js)
          → (Σ Pos λ c′ → S c′ end × c′ ≺ l₀) ⊎ (∀ {c} → S c end → l₀ ≼ c)
end-among fn {l₀} [] _ F = inj₂ λ {c} tc → [ (λ lc → lc) , (λ cl → ⊥-elim (∉[] (F tc cl))) ]′ (≼-or-≻ l₀ c)
  where
    ∉[] : ∀ {c} → c ∈ [] → ⊥
    ∉[] ()
end-among fn (x ∷ js) B F with B (here refl)
... | xl , end , tx = inj₁ (x , tx , xl)
... | xl , out _ , tx = end-among fn js (λ m → B (there m)) (λ tc cl → end-rest fn tx (λ ()) tc (F tc cl))
... | xl , skip , tx = end-among fn js (λ m → B (there m)) (λ tc cl → end-rest fn tx (λ ()) tc (F tc cl))
... | xl , pin _ , tx = end-among fn js (λ m → B (there m)) (λ tc cl → end-rest fn tx (λ ()) tc (F tc cl))

-- A listed row past the join, joined; or, an end before it, that end.
rejoin-into : ∀ {A} {S : EmissionSet A} {j l₀ e₁} → Flat S → (∀ {y e e′} → S y e → S y e′ → e ≡ e′)
            → (∀ {c c′} → S c end → S c′ end → c ≼ c′) → (∀ {c} → S c end → Few S c)
            → S l₀ e₁ → j ≺ l₀ → (∀ {c} → S c end → j ≺ c) → Listed S l₀ → (P : Pos → Set)
            → (∀ {l} → l ≡ l₀ ⊕ [ sub j ] ⊎ (Σ Pos λ c′ → S c′ end × c′ ≺ l₀ × l ≡ c′ ⊕ [ sub j ]) → P l)
            → Σ Pos λ l → Σ (Ev A) (Truncate (Rejoin j (Proper S)) l) × Listed (Truncate (Rejoin j (Proper S))) l × P l
rejoin-into {A} {S} {j} {l₀} {e₁} fl fn ee fe ul jl jc L′@(ks , F , B) P w = choose (end-among fn ks (λ m → B m) (λ tc cl → F tc cl))
  where
    choose : (Σ Pos λ c′ → S c′ end × c′ ≺ l₀) ⊎ (∀ {c} → S c end → l₀ ≼ c)
           → Σ Pos λ l → Σ (Ev A) (Truncate (Rejoin j (Proper S)) l) × Listed (Truncate (Rejoin j (Proper S))) l × P l
    choose (inj₂ lv) =
      l₀ ⊕ [ sub j ] , (rjEv e₁ , rjRow (ul , (λ {c} → lv {c})) jl , few-reach {e = rjEv e₁} (rejoin-few fl ul (ks , F)))
      , rejoin-listed fl (ul , (λ {c} → lv {c})) jl L′ , w (inj₁ refl)
    choose (inj₁ (c′ , tc′ , cl)) =
      c′ ⊕ [ sub j ] , (end , ended (tc′ , (λ {c} → ee {_} {c} tc′)) (jc tc′) , few-reach {e = end} (rejoin-few fl tc′ (fe tc′)))
      , rejoin-listed fl (tc′ , (λ {c} → ee {_} {c} tc′)) (jc tc′) (sub-listed L′ cl) , w (inj₂ (c′ , tc′ , cl , refl))

-- A whole hot with no end, joined: whole.
rejoin-whole : ∀ {A} {S : EmissionSet A} {j} → Flat S → Whole S → (∀ {c} → S c end → ⊥) → Whole (Truncate (Rejoin j (Proper S)))
rejoin-whole {S = S} {j} fl (ls , G , Bk) ne = L.map (_⊕ [ sub j ]) ks , pick , back
  where
    ks : List Pos
    ks = filter (λ k → T? (j <ᵖ k)) ls

    at : ∀ {q e} → S q e → j ≺ q → q ⊕ [ sub j ] ∈ L.map (_⊕ [ sub j ]) ks
    at r jq = ∈-map⁺ (_⊕ [ sub j ]) (∈-filter⁺ (λ k → T? (j <ᵖ k)) (G r) jq)

    pick : ∀ {r e} → Truncate (Rejoin j (Proper S)) r e → r ∈ L.map (_⊕ [ sub j ]) ks
    pick (shown r _ jq , _) = at (proj₁ r) jq
    pick (heard r jq , _)   = at (proj₁ r) jq
    pick (ended r jq , _)   = at (proj₁ r) jq
    pick (late r _ , _)     = ⊥-elim (ne (proj₁ r))

    row : ∀ {k} → k ∈ ls → j ≺ k → Σ _ (Truncate (Rejoin j (Proper S)) (k ⊕ [ sub j ]))
    row mk jk = rjEv (proj₁ (Bk mk)) , rjRow (proj₂ (Bk mk) , λ tc → ⊥-elim (ne tc)) jk
              , few-reach {e = rjEv (proj₁ (Bk mk))} (rejoin-few fl (proj₂ (Bk mk)) (ls , λ r _ → G r))

    back : ∀ {x} → x ∈ L.map (_⊕ [ sub j ]) ks → Σ _ (Truncate (Rejoin j (Proper S)) x)
    back m with ∈-map⁻ (_⊕ [ sub j ]) m
    ... | k , mk , refl = row (proj₁ (∈-filter⁻ (λ k → T? (j <ᵖ k)) {xs = ls} mk)) (proj₂ (∈-filter⁻ (λ k → T? (j <ᵖ k)) {xs = ls} mk))

------------------------------------------------------------------------
-- One reader

-- One reader of the binder `i`, subscribed at `p` and at its image `p′`.
module Read {Γ Δ} {M₀ : PMap} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {envP : DenEnv Γ} {envE : DenEnv Δ}
            (hm : Emb M₀) (er : EnvRel M₀ ρ envP envE) (jn : Joins ρ envP envE er M₀) (ap : Apart envP)
            {X} (i : X ∈ Γ) {p p′} (m₀ : M₀ p p′) (okP : Ok (Hots envP) p) (okE : Ok (Hots envE) p′)
            (nh : NotHot (Rows er) p) (fr : Fresh (Hots envP) M₀ p) where
  module C = CarryAt (Bound.carried (er i))

  private
    module VP = InvAt (Bound.invP (er i))
    module VE = InvAt (Bound.invE (er i))

  T₀ : EmissionSet X
  T₀ = BoundSrc (er i)

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

  -- A hot row carried into its instant: on the carrier's joined row, or,
  -- the carrier trailing an annotated end, on that end joined.
  PB : Pos → Pos → Set
  PB k l = Σ Pos λ q → Σ Pos λ l₀ → C.PB q l₀ × Σ (Ev X) (Proper T₀ q) × Σ (Ev (AIE X)) (T₀′ l₀) × p ≺ q × k ≡ q ⊕ [ sub p ]
           × (l ≡ l₀ ⊕ [ sub p′ ] ⊎ Σ Pos λ c′ → T₀′ c′ end × c′ ≺ l₀ × l ≡ c′ ⊕ [ sub p′ ])

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

  private

    fewP : ∀ {q e} → T₀ q e → Unpinned e → Few T₀ q
    fewP tq un = entered-few (approx (Bound.m (er i)) (Bound.src (er i)) (Bound.envP (er i))) (Bound.at (er i) ⊕ [ ix 1 ]) (full un) tq

  fewE : ∀ {l e} → T₀′ l e → Unpinned e → Few T₀′ l
  fewE tl un = entered-few (approx (Bound.m (er i)) (annotate (elab (Bound.σ (er i)) (Bound.src (er i)))) (Bound.envE (er i)))
                           (Bound.at′ (er i) ⊕ [ ix 1 ]) (full un) tl

  private

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
    ...   | inj₂ refl = ⊥-elim (nh (rows-at er i (proj₁ tq)) (⊑-refl q))
    ...   | inj₁ qp = ⊥-elim (≺-irrefl {l₀} (≺-trans {l₀} {p′} {l₀} (pre tq ci qp) pl))

    late-at : ∀ {c c′ e} → Proper T₀ c e → C.Img c c′ → c ≼ p → c′ ≼ p′
    late-at {c} {c′} tc ci cp with ≼-split {c} {p} cp
    ... | inj₂ refl = ⊥-elim (nh (rows-at er i (proj₁ tc)) (⊑-refl c))
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
      inj₁ (q , l₀ , (_ , tq) , ci , (e′ , rp) , pq , refl , refl) , rjRow {S = T₀′} {j = p′} rp pl
      , few-reach {S = Rejoin p′ (Proper T₀′)} {e = rjEv e′} (rejoin-few {S = T₀′} {j = p′} flatE ue fw)
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

    -- An annotated end carries the plain end: every live plain row lies at
    -- or before it, few rows before.
    end-few : ∀ {c′} → T₀′ c′ end → Σ (List Pos) λ ks → ∀ {q e} → Proper T₀ q e → q ∈ ks
    end-few tc′ with C.shown tc′ tt (λ {c₉} → endE {_} {c₉} tc′) (fewE tc′ tt)
    ... | k , ci , e₀ , tk , mt with end-of mt
    ...   | refl = proj₁ (C.few ci) ++ [ k ] , pick
      where
        pick : ∀ {q e} → Proper T₀ q e → q ∈ proj₁ (C.few ci) ++ [ k ]
        pick {q} (tq , lv) with ≼-split {q} {k} (lv tk)
        ... | inj₁ qk   = ∈-++⁺ˡ (proj₂ (C.few ci) tq qk)
        ... | inj₂ refl = ∈-++⁺ʳ (proj₁ (C.few ci)) (here refl)

    -- An annotated end past a live plain row past the subscription: past the image.
    end-past : ∀ {q e c′} → Proper T₀ q e → p ≺ q → T₀′ c′ end → p′ ≺ c′
    end-past {q} tq pq tc′ with C.shown tc′ tt (λ {c₉} → endE {_} {c₉} tc′) (fewE tc′ tt)
    ... | k , ci , e₀ , tk , mt with end-of mt
    ...   | refl = after′ ci (≺-≼-≺ {p} {q} {k} pq (proj₂ tq tk))

    heard-into : ∀ {q l₀ e e₁} → Proper T₀ q e → p ≺ q → C.PB q l₀ → T₀′ l₀ e₁ → Listed T₀′ l₀ → Listed t (q ⊕ [ sub p ])
               → IntoAt Img u PB (Hots envP) p (q ⊕ [ sub p ])
    heard-into {q} {l₀} {e₁ = e₁} tq pq pb ul L′ L =
      rejoin-into {S = T₀′} {j = p′} {l₀ = l₀} {e₁ = e₁} flatE VE.func endE (λ tc → fewE tc tt) ul
        (proj₁ (C.pb-past pb (proj₁ tq) (λ _ {c₈} → proj₂ tq {c₈}) ul m₀ pq (nh (rows-at er i (proj₁ tq)))))
        (λ tc → end-past tq pq tc) L′ (PB (q ⊕ [ sub p ])) (λ w → q , l₀ , pb , (_ , tq) , (_ , ul) , pq , refl , w)
      , inj₂ (inj₂ (q , hotP tq , sym (instant-⊕ q [ sub p ])))

    MatchR : Ev X → Ev (AIE X) → Set
    MatchR = Match Every (One annValues) (Reads annValues)

    ext : ∀ {k l} → Img k l → Σ Pos λ y → M k y × y ⊑ l
    ext (inj₁ (q , l₀ , br , ci , _ , pq , refl , refl)) = _ , inj₂ (inj₁ (q , l₀ , br , ci , pq , refl , refl)) , ⊑-refl _
    ext (inj₂ (refl , refl , _))                         = _ , inj₂ (inj₂ (refl , refl)) , ⊑-refl _

    pb-fib : ∀ {l₀} → (Σ (List Pos) λ ks → ∀ {q} → C.PB q l₀ → q ∈ ks) → ∀ {e₀} → Proper T₀′ l₀ e₀ → (e₀ ≡ end → ⊥)
           → Σ (List Pos) λ ks → ∀ {k} → PB k (l₀ ⊕ [ sub p′ ]) → k ∈ ks
    pb-fib {l₀} (ks , F) r ne = L.map (_⊕ [ sub p ]) ks , mem
      where
        mem : ∀ {k} → PB k (l₀ ⊕ [ sub p′ ]) → k ∈ L.map (_⊕ [ sub p ]) ks
        mem (q , l₁ , pb , _ , _ , _ , refl , inj₁ e) = ∈-map⁺ (_⊕ [ sub p ]) (F (subst (C.PB q) (⊕-injˡ l₁ l₀ (sym e)) pb))
        mem (q , l₁ , pb , _ , _ , _ , refl , inj₂ (c′ , tc′ , _ , e)) =
          ⊥-elim (ne (VE.func (proj₁ r) (subst (λ c → T₀′ c end) (sym (⊕-injˡ l₀ c′ e)) tc′)))

    -- On an end: the rows carried on it, and those trailing it.
    pb-end : ∀ {c′} → Proper T₀′ c′ end → Σ (List Pos) λ ks → ∀ {k} → PB k (c′ ⊕ [ sub p′ ]) → k ∈ ks
    pb-end {c′} r with C.pb-few (proj₁ r) | end-few (proj₁ r)
    ... | ks , F | js , G = L.map (_⊕ [ sub p ]) (ks ++ js) , mem
      where
        mem : ∀ {k} → PB k (c′ ⊕ [ sub p′ ]) → k ∈ L.map (_⊕ [ sub p ]) (ks ++ js)
        mem (q , l₁ , pb , _ , _ , _ , refl , inj₁ e) = ∈-map⁺ (_⊕ [ sub p ]) (∈-++⁺ˡ (F (subst (C.PB q) (⊕-injˡ l₁ c′ (sym e)) pb)))
        mem (q , l₁ , pb , (_ , tq) , _ , _ , refl , inj₂ (c₁ , _ , _ , e)) = ∈-map⁺ (_⊕ [ sub p ]) (∈-++⁺ʳ ks (G tq))

    pb-few : ∀ {l e} → u l e → Σ (List Pos) λ ks → ∀ {k} → PB k l → k ∈ ks
    pb-few (shown {e = out _} r _ _ , _) = pb-fib (C.pb-few (proj₁ r)) r (λ ())
    pb-few (shown {e = skip} r _ _ , _)  = pb-fib (C.pb-few (proj₁ r)) r (λ ())
    pb-few (shown {e = end} _ () _ , _)
    pb-few (shown {e = pin _} _ () _ , _)
    pb-few (heard r _ , _)   = pb-fib (C.pb-few (proj₁ r)) r (λ ())
    pb-few (ended r _ , _)   = pb-end r
    pb-few (late _ _ , _)    = [] , λ { (_ , l₁ , _ , _ , _ , _ , _ , inj₁ e) → ⊥-elim (last-sub (⊕-injʳ p′ l₁ e))
                                      ; (_ , _ , _ , _ , _ , _ , _ , inj₂ (c₁ , _ , _ , e)) → ⊥-elim (last-sub (⊕-injʳ p′ c₁ e)) }

    -- What the carry makes of a hot row, and what the reader makes of its joined row.
    Carried : Pos → Ev X → Set
    Carried q e = (Σ Pos λ l → C.Img q l × Σ (Ev (AIE X)) λ e′ → T₀′ l e′ × Listed T₀′ l × MatchR e e′)
                ⊎ (e ≡ skip × IntoAt C.Img T₀′ C.PB (Hots (Bound.envP (er i))) (Bound.at (er i) ⊕ [ ix 1 ]) q)

    Out : Pos → Ev X → Set
    Out k e = (Σ Pos λ l → Img k l × Σ (Ev (AIE X)) λ e′ → u l e′ × Listed u l × MatchR e e′)
            ⊎ (e ≡ skip × IntoAt Img u PB (Hots envP) p k)

    img-joined : ∀ {q e l₀ e′} → Proper T₀ q e → p ≺ q → C.Img q l₀ → T₀′ l₀ e′ → Listed T₀′ l₀ → MatchR e (rjEv e′)
               → Out (q ⊕ [ sub p ]) e
    img-joined {q} {l₀ = l₀} {e′} tq pq ci ue L′ mt =
      inj₁ (l₀ ⊕ [ sub p′ ] , proj₁ J , rjEv e′ , proj₂ J , rejoin-listed {S = T₀′} {j = p′} flatE (ue , (λ {c₈} → liveE ci tq {c₈})) (after′ ci pq) L′ , mt)
      where J = joined tq pq ci ue (proj₁ L′ , proj₁ (proj₂ L′))

    img-shown : ∀ {q e} → Proper T₀ q e → p ≺ q → Unpinned e → Listed t (q ⊕ [ sub p ]) → Carried q e → Out (q ⊕ [ sub p ]) e
    img-shown tq pq un L (inj₂ (es , (_ , (_ , ul) , L′ , pb) , _)) = inj₂ (es , heard-into tq pq pb ul L′ L)
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
    heard-img : ∀ {q r} → Proper T₀ q (pin r) → p ≺ q → Listed t (q ⊕ [ sub p ]) → HotsListed envP (q ⊕ [ sub p ])
              → InOrder C.Img C.PB T₀ T₀′ q
              → Out (q ⊕ [ sub p ]) skip
    heard-img {q} {r} tq pq L lp (l , (e₁ , ul) , pb , ls , _) =
      inj₂ (refl , heard-into {q} {l} {pin r} {e₁} tq pq pb ul ls L)

    img (shown {q} {e} tq _ pq , _) un _ L lp =
      img-shown {q} {e} tq pq un L (C.img {q} {e} (proj₁ tq) un (λ {c₉} → proj₂ tq {c₉})
        (lstP {q} {e} {q ⊕ [ sub p ]} tq (sub≼ q) lp) (lsts {q} {q ⊕ [ sub p ]} (sub≼ q) lp))
    img (heard {q} {r} tq pq , _) _ _ L lp = heard-img {q} {r} tq pq L lp
      (proj₁ (C.pinned {q} {r} (proj₁ tq) (λ {c₉} → proj₂ tq {c₉}) (lstP {q} {pin r} {q ⊕ [ sub p ]} tq (sub≼ q) lp) (lsts {q} {q ⊕ [ sub p ]} (sub≼ q) lp)))
    img (ended {c} tc pc , _) _ _ _ lp =
      img-ended {c} tc pc (C.img {c} {end} (proj₁ tc) tt (λ {c₉} → proj₂ tc {c₉})
        (lstP {c} {end} {c ⊕ [ sub p ]} tc (sub≼ c) lp) (lsts {c} {c ⊕ [ sub p ]} (sub≼ c) lp))
    img (late {c} tc cp , _) _ _ _ lp =
      img-late {c} tc cp (C.img {c} {end} (proj₁ tc) tt (λ {c₉} → proj₂ tc {c₉})
        (lstP {c} {end} {p ⊕ [ last ]} tc cl lp) (lsts {c} {p ⊕ [ last ]} cl lp))
      where
        cl : c ≼ (p ⊕ [ last ])
        cl = ≼-trans {c} {p} {p ⊕ [ last ]} cp (sub≼ p)

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
        ...   | inj₂ refl = ⊥-elim (nh (rows-at er i (proj₁ (prop tk))) (⊑-refl p))
        ...   | inj₁ pk′ = ∈-++⁺ʳ (proj₁ L₁) (djs-in ks B (F (rjRow (prop tk) pk′ , few-reach {e = rjEv e} (rejoin-few flatP tk fk))))
          where
            fk : Few T₀ k
            fk with listed-at envP i (Bound.isP (er i)) (lp {k})
            ... | js , G , _ = js , λ r h → G (prop r) h

        back′ : ∀ {k} → k ∈ proj₁ L₁ ++ djs ks B → Σ _ (T₀ k)
        back′ m with ∈-++⁻ (proj₁ L₁) m
        ... | inj₁ m′ = let (_ , e , r) = proj₂ (proj₂ L₁) m′ in e , proj₁ r
        ... | inj₂ m′ = let (e , r) = djs-out ks B m′ in e , proj₁ r

    -- No end plain: none elaborated, an end being shown.
    endlessE : (∀ {c} → t c end → ⊥) → ∀ {c} → T₀′ c end → ⊥
    endlessE ne tc with C.shown tc tt (λ {c′} tc′ → endE tc tc′) (fewE tc tt)
    ... | _ , _ , _ , tk , mt with end-of mt
    ...   | refl = no-end ne tk

    whole : Whole t → (∀ {c} → t c end → ⊥) → (∀ {q} → HotsListed envP q) → Whole u
    whole W ne lp = rejoin-whole {S = T₀′} {j = p′} flatE (C.whole (whole-hot W (no-end ne) lp) (no-end ne) (λ {q} → Bound.lists (er i) (lp {q})))
                                 (λ tc → endlessE ne tc)

    bk : Pos → List Pos
    bk l = L.map (_⊕ [ sub p ]) (C.bk (parent l)) ++ [ p ⊕ [ last ] ]

    in-bk : ∀ {k l} → Img k l → k ∈ bk l
    in-bk (inj₁ (q , l₀ , _ , ci , _ , _ , refl , refl)) =
      ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub p ]) (subst (λ z → q ∈ C.bk z) (sym (parent-snoc l₀ (sub p′))) (C.in-bk ci)))
    in-bk (inj₂ (refl , refl , _)) = ∈-++⁺ʳ (L.map (_⊕ [ sub p ]) (C.bk (parent (p′ ⊕ [ last ])))) (here refl)

  private
    -- A hot row past the subscription, joined under it: in its world.
    joinW : ∀ {q e} → Proper T₀ q e → p ≺ q → W⁼ (Hots envP) p (q ⊕ [ sub p ]) × p ≺ (q ⊕ [ sub p ])
    joinW {q} tq pq = inW (join (inj₁ (hotP tq)) here pq) , ≺-≼-≺ {p} {q} {q ⊕ [ sub p ]} pq (sub≼ q)

    -- A row of the reading lies in the subscription's world, past it.
    rowW : ∀ {k e} → t k e → W⁼ (Hots envP) p k × p ≺ k
    rowW (shown tq _ pq , _) = joinW tq pq
    rowW (heard tq pq , _)   = joinW tq pq
    rowW (ended tq pq , _)   = joinW tq pq
    rowW (late _ _ , _)      = inW (step here plain-last) , ≺-ext p []

    -- No row of the reading leads the subscription.
    ahead : ∀ {k e} → t k e → k ⊑ p → ⊥
    ahead {k} tk kp = ≺-irrefl {p} (≺-≼-≺ {p} {k} {p} (proj₂ (rowW tk)) (⊑-≼ {k} {p} kp))

    under-row : ∀ {q′ e′ q} → Proper T₀ q′ e′ → BoundRow (er i) q → (q′ ⊕ [ sub p ]) ⊑ q → ⊥
    under-row {q′} tq (e₁ , tr , _) (zs , e) = flatP (proj₁ tq) (subst (λ z → T₀ z e₁) (trans e (⊕-assoc q′ [ sub p ] zs)) tr)

    -- No row of the reading leads a hot row.
    under : ∀ {k e q} → t k e → BoundRow (er i) q → k ⊑ q → ⊥
    under (shown {q′} tq _ _ , _) br kq = under-row {q′} tq br kq
    under (heard {q′} tq _ , _)   br kq = under-row {q′} tq br kq
    under (ended {q′} tq _ , _)   br kq = under-row {q′} tq br kq
    under (late _ _ , _)          br kq = nh (rows-at er i (proj₁ (proj₂ br))) (⊑-trans (⊑-snoc⁺ p) kq)

    -- A row of the reading leading a joined point is it.
    lead : ∀ {k e} q {a} → t k e → (k ⊑ q → ⊥) → k ⊑ (q ⊕ [ a ]) → (q ⊕ [ a ]) ≡ k
    lead q tk n kx with ⊑-snoc q kx
    ... | inj₂ e  = sym e
    ... | inj₁ kq = ⊥-elim (n kq)

  -- What the joins add lies in the subscription's world.
  reader-within : Within (Hots envP) M₀ M p
  reader-within (inj₁ m) = inj₁ m
  reader-within (inj₂ (inj₁ (q , _ , br , _ , pq , refl , _))) = inj₂ (inW (join (inj₁ (bound-hot {ρ = ρ} envP {envE = envE} er i br)) here pq))
  reader-within (inj₂ (inj₂ (refl , _))) = inj₂ (inW (step here plain-last))

  -- The map pairs nothing strictly under a row of the reading: the map
  -- so far is fresh in the world, and a join lies on a hot row's join.
  reader-bare : Bare M t
  reader-bare {k} tk (inj₁ m) kx = ⊥-elim (ahead tk (subst (k ⊑_) (fr m (k , proj₁ (rowW tk) , kx)) kx))
  reader-bare tk (inj₂ (inj₁ (q , _ , br , _ , _ , refl , _))) kx = lead q tk (under tk br) kx
  reader-bare tk (inj₂ (inj₂ (refl , _))) kx = lead p tk (ahead tk) kx

  -- A join lies on its hot row's join; a point under a hot row's step
  -- lies in the map so far, which joins it.
  reader-joins : Joins ρ envP envE er M
  reader-joins i′ (inj₁ m) br eq with jn i′ m br eq
  ... | e₀ , ae , e₀′ , me , L , ci , le = e₀ , ae , e₀′ , inj₁ me , L , ci , le
  reader-joins i′ (inj₂ (inj₁ (q₁ , l , br₁ , ci₁ , _ , refl , refl))) br eq with split-at _ q₁ eq
  ... | inj₁ (refl , refl) =
    p , refl , p′ , inj₁ m₀ , l
      , same-hot envP ap i i′ (Bound.isP (er i)) (Bound.isP (er i′)) (proj₂ br₁) (proj₂ br) (λ k → CarryAt.Img (Bound.carried (er k)) q₁ l) ci₁
      , ⊑-refl (l ⊕ [ sub p′ ])
  ... | inj₂ (zs , e) with C.ext ci₁
  ...   | y₁ , my₁ , yl with jn i′ my₁ br e
  ...     | e₀ , ae , e₀′ , me , L , ci , le = e₀ , ae , e₀′ , inj₁ me , L , ci , ⊑-trans le (⊑-trans yl (⊑-snoc⁺ l))
  reader-joins i′ (inj₂ (inj₂ (refl , refl))) br eq with split-at _ p eq
  ... | inj₁ (refl , _) = ⊥-elim (nh (rows-at er i′ (proj₁ (proj₂ br))) (⊑-refl p))
  ... | inj₂ (zs , e) with jn i′ m₀ br e
  ...   | e₀ , ae , e₀′ , me , L , ci , le = e₀ , ae , e₀′ , inj₁ me , L , ci , ⊑-trans le (⊑-snoc⁺ p′)

  private
    →T : ∀ {b} → b ≡ true → T b
    →T = Equivalence.from T-≡

  cmp3 : ∀ x y → x ≺ y ⊎ x ≡ y ⊎ y ≺ x
  cmp3 x y with ≼-or-≻ x y
  ... | inj₂ yx = inj₂ (inj₂ yx)
  ... | inj₁ xy with ≼-split {x} {y} xy
  ...   | inj₁ lt = inj₁ lt
  ...   | inj₂ eq = inj₂ (inj₁ eq)

  private

    -- Siblings keep their labels' order, whatever lies under them.
    sibs : ∀ q {e e′} ys zs → e ≺ e′ → (q ⊕ (sub e ∷ ys)) ≺ (q ⊕ (sub e′ ∷ zs))
    sibs q ys zs h = →T (<ᵖ-part q ys zs (Equivalence.to T-≡ h))

    sib-below : ∀ l {e e′ y} → e ≺ e′ → (l ⊕ [ sub e ]) ⊑ y → y ≺ (l ⊕ [ sub e′ ])
    sib-below l {e} {e′} h (τ , refl) = subst (_≺ (l ⊕ [ sub e′ ])) (sym (⊕-assoc l [ sub e ] τ)) (sibs l τ [] h)

    sib-above : ∀ l {e e′ y} → e ≺ e′ → (l ⊕ [ sub e′ ]) ⊑ y → (l ⊕ [ sub e ]) ≺ y
    sib-above l {e} {e′} h (τ , refl) = subst ((l ⊕ [ sub e ]) ≺_) (sym (⊕-assoc l [ sub e′ ] τ)) (sibs l [] τ h)

    -- Past a position and before a point under it: under it.
    between : ∀ {q x} ys → q ≺ x → x ≺ (q ⊕ ys) → q ⊑ x
    between {q} {x} ys qx xq = <ᵖ-between q x ys (Equivalence.to T-≡ qx) (Equivalence.to T-≡ xq)

    snoc-up : ∀ x {a} → (x ⊕ [ a ]) ⊑ x → ⊥
    snoc-up x {a} (zs , e) = ext≢ x zs (sym (trans e (⊕-assoc x [ a ] zs)))

  sib-eq : ∀ x {a b} → (x ⊕ [ a ]) ⊑ (x ⊕ [ b ]) → a ≡ b
  sib-eq x le with ⊑-snoc x le
  ... | inj₁ up = ⊥-elim (snoc-up x up)
  ... | inj₂ e  = ⊕-injʳ x x e

  private

    sib-sub : ∀ x {e e′} → (x ⊕ [ sub e ]) ⊑ (x ⊕ [ sub e′ ]) → e ≡ e′
    sib-sub x le with sib-eq x le
    ... | refl = refl

    -- Before an apart position: so is everything under it.

  past : ∀ {a b c} → a ≺ b → ¬ (a ⊑ b) → a ⊑ c → c ≺ b
  past {a} {b} ab nab (σ , refl) = subst ((a ⊕ σ) ≺_) (⊕-identityʳ b) (apart {a} {b} ab nab σ [])

  private

    -- The map so far holds no point at or under a point of the world past
    -- the subscription.
    stale : ∀ {x y w} → M₀ x y → W⁼ (Hots envP) p w × p ≺ w → w ⊑ x → ⊥
    stale {w = w} m (v , pw) wx with fr m (w , v , wx)
    ... | refl = ≺-irrefl {p} (≺-≼-≺ {p} {w} {p} pw (⊑-≼ wx))

    lateW : W⁼ (Hots envP) p (p ⊕ [ last ]) × p ≺ (p ⊕ [ last ])
    lateW = inW (step here plain-last) , ≺-ext p []

    fresh-R : ∀ {x y y′} → M₀ x y → R x y′ → ⊥
    fresh-R m (inj₁ (_ , _ , br , _ , pq , refl , _)) = stale m (joinW (proj₂ br) pq) (⊑-refl _)
    fresh-R m (inj₂ (refl , _))                      = stale m lateW (⊑-refl _)

    stale-sub : ∀ {q x y σ} → BoundRow (er i) q → p ≺ q → M₀ x y → x ≡ q ⊕ (sub p ∷ σ) → ⊥
    stale-sub {q} {σ = σ} br pq m e = stale m (joinW (proj₂ br) pq) (σ , trans e (sym (⊕-assoc q [ sub p ] σ)))

    hotB : ∀ {q} → BoundRow (er i) q → p ⊑ q → ⊥
    hotB br = nh (rows-at er i (proj₁ (proj₂ br)))

    -- A point paired with the subscription's image is the subscription.
    same-join : ∀ {e e′} → M₀ e e′ → e′ ≡ p′ → e ≡ p
    same-join {e} me refl with cmp3 e p
    ... | inj₁ ep        = ⊥-elim (≺-irrefl {p′} (Emb.mono hm me m₀ ep))
    ... | inj₂ (inj₁ eq) = eq
    ... | inj₂ (inj₂ pe) = ⊥-elim (≺-irrefl {p′} (Emb.mono hm m₀ me pe))

    -- A point of the map so far under a hot row's step: a reader's join,
    -- under the row's carrier joined at the reader's image.
    under-q : ∀ {q l x y a σ} → BoundRow (er i) q → C.Img q l → M₀ x y → x ≡ q ⊕ (a ∷ σ)
            → Σ Pos λ e → a ≡ sub e × Σ Pos λ e′ → M₀ e e′ × (l ⊕ [ sub e′ ]) ⊑ y
    under-q br ci m eq with jn i m br eq
    ... | e , ae , e′ , me , L , ci′ , le with C.img-fun ci ci′
    ...   | refl = e , ae , e′ , me , le

    q-lead : ∀ {q l x y} → BoundRow (er i) q → C.Img q l → M₀ x y → q ⊑ x
           → x ≡ q ⊎ Σ Pos λ e′ → (l ⊕ [ sub e′ ]) ⊑ y × Σ Pos λ e → M₀ e e′ × Σ Path λ σ → x ≡ q ⊕ (sub e ∷ σ)
    q-lead {q} br ci m ([] , e) = inj₁ (trans e (⊕-identityʳ q))
    q-lead br ci m (a ∷ σ , e) with under-q br ci m e
    ... | e₀ , refl , e₀′ , me , le = inj₂ (e₀′ , le , e₀ , me , σ , e)

    -- The map so far holds no other reader's join at this one's image.
    j-hit : ∀ {q x y e e′ σ} → BoundRow (er i) q → p ≺ q → M₀ x y → M₀ e e′ → x ≡ q ⊕ (sub e ∷ σ) → e′ ≡ p′ → ⊥
    j-hit br pq m me ex ep with same-join me ep
    ... | refl = stale-sub br pq m ex

  flat-lead : ∀ {q₁ q₂} → BoundRow (er i) q₁ → BoundRow (er i) q₂ → q₁ ≺ q₂ → ¬ (q₁ ⊑ q₂)
  flat-lead br₁ br₂ = nest {S = T₀} flatP (proj₁ (proj₂ br₁)) (proj₁ (proj₂ br₂))

  private

    -- Carriers of rows in order are apart.
    img-apart : ∀ {q₁ q₂ l₁ l₂} → BoundRow (er i) q₁ → BoundRow (er i) q₂ → C.Img q₁ l₁ → C.Img q₂ l₂ → q₁ ≺ q₂ → ¬ (l₁ ⊑ l₂)
    img-apart {q₁} {q₂} br₁ br₂ ci₁ ci₂ qq ll with C.ext ci₁ | C.ext ci₂
    ... | y₁ , my₁ , yl₁ | y₂ , my₂ , yl₂ with ⊑-cmp y₁ y₂ (⊑-trans yl₁ ll) yl₂
    ...   | inj₁ yy = flat-lead br₁ br₂ qq (Emb.reflect hm my₁ my₂ yy)
    ...   | inj₂ yy = ⊑-≼ {y₂} {y₁} yy (Emb.mono hm my₁ my₂ qq)

    img-eq : ∀ {q₁ q₂ l₁ l₂} → BoundRow (er i) q₁ → BoundRow (er i) q₂ → C.Img q₁ l₁ → C.Img q₂ l₂ → l₁ ⊑ l₂ → q₁ ≡ q₂
    img-eq {q₁} {q₂} {l₁} {l₂} br₁ br₂ ci₁ ci₂ ll with cmp3 q₁ q₂
    ... | inj₁ qq        = ⊥-elim (img-apart br₁ br₂ ci₁ ci₂ qq ll)
    ... | inj₂ (inj₁ e)  = e
    ... | inj₂ (inj₂ qq) = ⊥-elim (⊑-≼ {l₁} {l₂} ll (CM.img-mono ci₂ ci₁ qq))

    -- A carrier past the subscription is apart from its image.
    p′-l : ∀ {q l} → BoundRow (er i) q → C.Img q l → p ≺ q → ¬ (p′ ⊑ l)
    p′-l {q} br ci pq pl with C.ext ci
    ... | y , my , yl with ⊑-cmp y p′ yl pl
    ...   | inj₁ yp = ≺-irrefl {p} (≺-≼-≺ {p} {q} {p} pq (⊑-≼ (Emb.reflect hm my m₀ yp)))
    ...   | inj₂ py = hotB br (Emb.reflect hm m₀ my py)

    -- Order: two joins; a join and the late end; a point of the map so
    -- far and a join or the late end.
    j-j : ∀ {q₁ q₂ l₁ l₂} → BoundRow (er i) q₁ → C.Img q₁ l₁ → BoundRow (er i) q₂ → C.Img q₂ l₂
        → (q₁ ⊕ [ sub p ]) ≺ (q₂ ⊕ [ sub p ]) → (l₁ ⊕ [ sub p′ ]) ≺ (l₂ ⊕ [ sub p′ ])
    j-j {q₁} {q₂} {l₁} {l₂} br₁ ci₁ br₂ ci₂ h =
      apart {l₁} {l₂} (CM.img-mono ci₁ ci₂ qq) (img-apart br₁ br₂ ci₁ ci₂ qq) [ sub p′ ] [ sub p′ ]
      where qq = joined-back q₁ q₂ h (flat-lead br₂ br₁)

    l-j : ∀ {q} → BoundRow (er i) q → p ≺ q → (p ⊕ [ last ]) ≺ (q ⊕ [ sub p ])
    l-j {q} br pq = apart {p} {q} pq (hotB br) [ last ] [ sub p ]

    l-j′ : ∀ {q l} → BoundRow (er i) q → C.Img q l → p ≺ q → (p′ ⊕ [ last ]) ≺ (l ⊕ [ sub p′ ])
    l-j′ {q} {l} br ci pq = apart {p′} {l} (after′ ci pq) (p′-l br ci pq) [ last ] [ sub p′ ]

    m-j : ∀ {x y q l} → M₀ x y → BoundRow (er i) q → C.Img q l → p ≺ q → x ≺ (q ⊕ [ sub p ]) → y ≺ (l ⊕ [ sub p′ ])
    m-j {x} {y} {q} {l} m br ci pq h with C.ext ci
    ... | yq , myq , yl with cmp3 x q
    ...   | inj₁ xq = ≺-≼-≺ {y} {yq} {l ⊕ [ sub p′ ]} (Emb.mono hm m myq xq) (⊑-≼ (⊑-trans yl (⊑-snoc⁺ l)))
    ...   | inj₂ (inj₁ refl) = ≼-≺-≺ {y} {l} {l ⊕ [ sub p′ ]} (⊑-≼ (subst (_⊑ l) (Emb.fun hm myq m) yl)) (≺-ext l [])
    ...   | inj₂ (inj₂ qx) with between [ sub p ] qx h
    ...     | [] , e = ⊥-elim (≺-irrefl {q} (subst (q ≺_) (trans e (⊕-identityʳ q)) qx))
    ...     | a ∷ σ , e with under-q br ci m e
    ...       | e₀ , refl , e₀′ , me , le with cmp3 e₀ p
    ...         | inj₁ ep        = sib-below l (Emb.mono hm me m₀ ep) le
    ...         | inj₂ (inj₁ ep) = ⊥-elim (stale-sub br pq m (subst (λ z → x ≡ q ⊕ (sub z ∷ σ)) ep e))
    ...         | inj₂ (inj₂ pe) = ⊥-elim (≺-absurd {q ⊕ (sub e₀ ∷ σ)} {q ⊕ [ sub p ]} (subst (_≺ (q ⊕ [ sub p ])) e h) (sibs q [] σ pe))

    j-m : ∀ {x y q l} → M₀ x y → BoundRow (er i) q → C.Img q l → p ≺ q → (q ⊕ [ sub p ]) ≺ x → (l ⊕ [ sub p′ ]) ≺ y
    j-m {x} {y} {q} {l} m br ci pq h with C.ext ci
    ... | yq , myq , yl with cmp3 x q
    ...   | inj₁ xq = ⊥-elim (≺-irrefl {x} (≺-trans {x} {q} {x} xq (≺-trans {q} {q ⊕ [ sub p ]} {x} (≺-ext q []) h)))
    ...   | inj₂ (inj₁ refl) = ⊥-elim (≺-absurd {x ⊕ [ sub p ]} {x} h (≺-ext x {sub p} []))
    ...   | inj₂ (inj₂ qx) with ⊑? q x
    ...     | no nq = past {yq} {y} {l ⊕ [ sub p′ ]} (Emb.mono hm myq m qx) (λ yy → nq (Emb.reflect hm myq m yy)) (⊑-trans yl (⊑-snoc⁺ l))
    ...     | yes ([] , e) = ⊥-elim (≺-irrefl {q} (subst (q ≺_) (trans e (⊕-identityʳ q)) qx))
    ...     | yes (a ∷ σ , e) with under-q br ci m e
    ...       | e₀ , refl , e₀′ , me , le with cmp3 e₀ p
    ...         | inj₁ ep        = ⊥-elim (≺-absurd {q ⊕ [ sub p ]} {q ⊕ (sub e₀ ∷ σ)} (subst ((q ⊕ [ sub p ]) ≺_) e h) (sibs q σ [] ep))
    ...         | inj₂ (inj₁ ep) = ⊥-elim (stale-sub br pq m (subst (λ z → x ≡ q ⊕ (sub z ∷ σ)) ep e))
    ...         | inj₂ (inj₂ pe) = sib-above l (Emb.mono hm m₀ me pe) le

    m-l : ∀ {x y} → M₀ x y → x ≺ (p ⊕ [ last ]) → y ≺ (p′ ⊕ [ last ])
    m-l {x} {y} m h with cmp3 x p
    ... | inj₁ xp        = ≺-trans {y} {p′} {p′ ⊕ [ last ]} (Emb.mono hm m m₀ xp) (≺-ext p′ [])
    ... | inj₂ (inj₁ refl) = subst (_≺ (p′ ⊕ [ last ])) (Emb.fun hm m₀ m) (≺-ext p′ [])
    ... | inj₂ (inj₂ px) = ⊥-elim (≺-irrefl {p} (subst (p ≺_) (fr m (p , here , between [ last ] px h)) px))

    l-m : ∀ {x y} → M₀ x y → (p ⊕ [ last ]) ≺ x → (p′ ⊕ [ last ]) ≺ y
    l-m {x} {y} m h with cmp3 x p
    ... | inj₁ xp        = ⊥-elim (≺-absurd {p} {x} (≺-trans {p} {p ⊕ [ last ]} {x} (≺-ext p []) h) xp)
    ... | inj₂ (inj₁ refl) = ⊥-elim (≺-absurd {x ⊕ [ last ]} {x} h (≺-ext x {last} []))
    ... | inj₂ (inj₂ px) with ⊑? p x
    ...   | yes px′ = ⊥-elim (≺-irrefl {p} (subst (p ≺_) (fr m (p , here , px′)) px))
    ...   | no np   = past {p′} {y} {p′ ⊕ [ last ]} (Emb.mono hm m₀ m px) (λ yy → np (Emb.reflect hm m₀ m yy)) (⊑-snoc⁺ p′)

    -- Reflection, the same cases.
    j-jr : ∀ {q₁ q₂ l₁ l₂} → BoundRow (er i) q₁ → C.Img q₁ l₁ → BoundRow (er i) q₂ → C.Img q₂ l₂
         → (l₁ ⊕ [ sub p′ ]) ⊑ (l₂ ⊕ [ sub p′ ]) → (q₁ ⊕ [ sub p ]) ⊑ (q₂ ⊕ [ sub p ])
    j-jr {q₁} {q₂} {l₁} {l₂} br₁ ci₁ br₂ ci₂ h with ⊑-snoc l₂ h
    ... | inj₂ e with img-eq br₁ br₂ ci₁ ci₂ (subst (l₁ ⊑_) (⊕-injˡ l₁ l₂ e) (⊑-refl l₁))
    ...   | refl = ⊑-refl _
    j-jr {q₁} {q₂} {l₁} {l₂} br₁ ci₁ br₂ ci₂ h | inj₁ up with img-eq br₁ br₂ ci₁ ci₂ (⊑-trans (⊑-snoc⁺ l₁) up)
    ...   | refl = ⊥-elim (snoc-up l₁ (subst ((l₁ ⊕ [ sub p′ ]) ⊑_) (sym (C.img-fun ci₁ ci₂)) up))

    j-lr : ∀ {q l} → C.Img q l → p ≺ q → (l ⊕ [ sub p′ ]) ⊑ (p′ ⊕ [ last ]) → ⊥
    j-lr {q} {l} ci pq h with ⊑-snoc p′ h
    ... | inj₂ e  = last-sub (sym (⊕-injʳ l p′ e))
    ... | inj₁ up = ⊑-≼ {l} {p′} (⊑-trans (⊑-snoc⁺ l) up) (after′ ci pq)

    l-jr : ∀ {q l} → BoundRow (er i) q → C.Img q l → p ≺ q → (p′ ⊕ [ last ]) ⊑ (l ⊕ [ sub p′ ]) → ⊥
    l-jr {q} {l} br ci pq h with ⊑-snoc l h
    ... | inj₂ e  = last-sub (⊕-injʳ p′ l e)
    ... | inj₁ up = p′-l br ci pq (⊑-trans (⊑-snoc⁺ p′) up)

    m-jr : ∀ {x y q l} → M₀ x y → BoundRow (er i) q → C.Img q l → p ≺ q → y ⊑ (l ⊕ [ sub p′ ]) → x ⊑ (q ⊕ [ sub p ])
    m-jr {x} {y} {q} {l} m br ci pq h with C.ext ci
    ... | yq , myq , yl with ⊑-snoc l h
    ...   | inj₂ refl with q-lead br ci m (Emb.reflect hm myq m (⊑-trans yl (⊑-snoc⁺ l)))
    ...     | inj₁ refl = ⊑-snoc⁺ x
    ...     | inj₂ (e′ , le , e₀ , me , σ , ex) = ⊥-elim (j-hit br pq m me ex (sib-sub l le))
    m-jr {x} {y} {q} {l} m br ci pq h | yq , myq , yl | inj₁ yl′ with ⊑-cmp y yq yl′ yl
    ...     | inj₁ yy = ⊑-trans (Emb.reflect hm m myq yy) (⊑-snoc⁺ q)
    ...     | inj₂ yy with q-lead br ci m (Emb.reflect hm myq m yy)
    ...       | inj₁ refl = ⊑-snoc⁺ x
    ...       | inj₂ (_ , le , _) = ⊥-elim (snoc-up l (⊑-trans le yl′))

    j-mr : ∀ {x y q l} → M₀ x y → BoundRow (er i) q → C.Img q l → p ≺ q → (l ⊕ [ sub p′ ]) ⊑ y → ⊥
    j-mr {x} {y} {q} {l} m br ci pq h with C.ext ci
    ... | yq , myq , yl with q-lead br ci m (Emb.reflect hm myq m (⊑-trans yl (⊑-trans (⊑-snoc⁺ l) h)))
    ...   | inj₁ refl = snoc-up l (⊑-trans h (subst (_⊑ l) (Emb.fun hm myq m) yl))
    ...   | inj₂ (e′ , le , e₀ , me , σ , ex) with ⊑-cmp (l ⊕ [ sub e′ ]) (l ⊕ [ sub p′ ]) le h
    ...     | inj₁ ll = j-hit br pq m me ex (sib-sub l ll)
    ...     | inj₂ ll = j-hit br pq m me ex (sym (sib-sub l ll))

    m-lr : ∀ {x y} → M₀ x y → y ⊑ (p′ ⊕ [ last ]) → x ⊑ (p ⊕ [ last ])
    m-lr {x} {y} m h with ⊑-snoc p′ h
    ... | inj₁ yp   = ⊑-trans (Emb.reflect hm m m₀ yp) (⊑-snoc⁺ p)
    ... | inj₂ refl with fr m (p , here , Emb.reflect hm m₀ m (⊑-snoc⁺ p′))
    ...   | refl = ⊥-elim (ext≢ p′ [] (sym (Emb.fun hm m₀ m)))

    l-mr : ∀ {x y} → M₀ x y → (p′ ⊕ [ last ]) ⊑ y → ⊥
    l-mr {x} {y} m h with fr m (p , here , Emb.reflect hm m₀ m (⊑-trans (⊑-snoc⁺ p′) h))
    ... | refl = snoc-up p′ (subst ((p′ ⊕ [ last ]) ⊑_) (sym (Emb.fun hm m₀ m)) h)

    -- Each point's instants are those of a point of the map so far.
    base : ∀ {x y} → M x y → Σ Pos λ x₁ → Σ Pos λ y₁ → M₀ x₁ y₁ × instantOf x ≡ instantOf x₁ × instantOf y ≡ instantOf y₁
    base (inj₁ m) = _ , _ , m , refl , refl
    base (inj₂ (inj₁ (q , l , br , ci , pq , refl , refl))) with C.ext ci
    ... | yq , myq , (δ , refl) = q , yq , myq , instant-⊕ q [ sub p ] , trans (instant-⊕ (yq ⊕ δ) [ sub p′ ]) (instant-⊕ yq δ)
    base (inj₂ (inj₂ (refl , refl))) = p , p′ , m₀ , instant-⊕ p [ last ] , instant-⊕ p′ [ last ]

    fun′ : ∀ {x y y′} → M x y → M x y′ → y ≡ y′
    fun′ (inj₁ m) (inj₁ m′) = Emb.fun hm m m′
    fun′ (inj₁ m) (inj₂ r)  = ⊥-elim (fresh-R m r)
    fun′ (inj₂ r) (inj₁ m)  = ⊥-elim (fresh-R m r)
    fun′ (inj₂ (inj₁ (q₁ , _ , _ , ci₁ , _ , e₁ , refl))) (inj₂ (inj₁ (q₂ , _ , _ , ci₂ , _ , e₂ , refl))) with ⊕-injˡ q₁ q₂ (trans (sym e₁) e₂)
    ... | refl = cong (_⊕ [ sub p′ ]) (C.img-fun ci₁ ci₂)
    fun′ (inj₂ (inj₁ (q₁ , _ , _ , _ , _ , e₁ , _))) (inj₂ (inj₂ (e₂ , _))) = ⊥-elim (last-sub (⊕-injʳ p q₁ (trans (sym e₂) e₁)))
    fun′ (inj₂ (inj₂ (e₁ , _))) (inj₂ (inj₁ (q₂ , _ , _ , _ , _ , e₂ , _))) = ⊥-elim (last-sub (⊕-injʳ p q₂ (trans (sym e₁) e₂)))
    fun′ (inj₂ (inj₂ (_ , refl))) (inj₂ (inj₂ (_ , refl))) = refl

    mono′ : ∀ {x x′ y y′} → M x y → M x′ y′ → x ≺ x′ → y ≺ y′
    mono′ (inj₁ m) (inj₁ m′) h = Emb.mono hm m m′ h
    mono′ (inj₁ m) (inj₂ (inj₁ (_ , _ , br , ci , pq , refl , refl))) h = m-j m br ci pq h
    mono′ (inj₁ m) (inj₂ (inj₂ (refl , refl))) h = m-l m h
    mono′ (inj₂ (inj₁ (_ , _ , br , ci , pq , refl , refl))) (inj₁ m) h = j-m m br ci pq h
    mono′ (inj₂ (inj₂ (refl , refl))) (inj₁ m) h = l-m m h
    mono′ (inj₂ (inj₁ (_ , _ , br₁ , ci₁ , _ , refl , refl))) (inj₂ (inj₁ (_ , _ , br₂ , ci₂ , _ , refl , refl))) h = j-j br₁ ci₁ br₂ ci₂ h
    mono′ (inj₂ (inj₁ (q , _ , br , _ , pq , refl , refl))) (inj₂ (inj₂ (refl , refl))) h = ⊥-elim (≺-absurd {q ⊕ [ sub p ]} {p ⊕ [ last ]} h (l-j br pq))
    mono′ (inj₂ (inj₂ (refl , refl))) (inj₂ (inj₁ (_ , _ , br , ci , pq , refl , refl))) _ = l-j′ br ci pq
    mono′ (inj₂ (inj₂ (refl , refl))) (inj₂ (inj₂ (refl , refl))) h = ⊥-elim (≺-irrefl {p ⊕ [ last ]} h)

    reflect′ : ∀ {x x′ y y′} → M x y → M x′ y′ → y ⊑ y′ → x ⊑ x′
    reflect′ (inj₁ m) (inj₁ m′) h = Emb.reflect hm m m′ h
    reflect′ (inj₁ m) (inj₂ (inj₁ (_ , _ , br , ci , pq , refl , refl))) h = m-jr m br ci pq h
    reflect′ (inj₁ m) (inj₂ (inj₂ (refl , refl))) h = m-lr m h
    reflect′ (inj₂ (inj₁ (_ , _ , br , ci , pq , refl , refl))) (inj₁ m) h = ⊥-elim (j-mr m br ci pq h)
    reflect′ (inj₂ (inj₂ (refl , refl))) (inj₁ m) h = ⊥-elim (l-mr m h)
    reflect′ (inj₂ (inj₁ (_ , _ , br₁ , ci₁ , _ , refl , refl))) (inj₂ (inj₁ (_ , _ , br₂ , ci₂ , _ , refl , refl))) h = j-jr br₁ ci₁ br₂ ci₂ h
    reflect′ (inj₂ (inj₁ (_ , _ , _ , ci , pq , refl , refl))) (inj₂ (inj₂ (refl , refl))) h = ⊥-elim (j-lr ci pq h)
    reflect′ (inj₂ (inj₂ (refl , refl))) (inj₂ (inj₁ (_ , _ , br , ci , pq , refl , refl))) h = ⊥-elim (l-jr br ci pq h)
    reflect′ (inj₂ (inj₂ (refl , refl))) (inj₂ (inj₂ (refl , refl))) _ = ⊑-refl _

    inst′ : ∀ {x x′ y y′} → M x y → M x′ y′ → (instantOf y ≡ instantOf y′ ⇔ instantOf x ≡ instantOf x′)
    inst′ a b with base a | base b
    ... | _ , _ , m₁ , ex , ey | _ , _ , m₂ , ex′ , ey′ rewrite ex | ex′ | ey | ey′ = Emb.inst hm m₁ m₂

  -- THE JOINS KEEP THE EMBEDDING: the map so far holds nothing in the
  -- subscription's world, a hot row's joins lie in their subscriptions'
  -- order (`Joins`), and the hot's carriers are apart.
  reader-emb : Emb M
  reader-emb = record { fun = fun′ ; mono = mono′ ; reflect = reflect′ ; inst = inst′ }

  private
    -- A hot row carried into its instant, joined: past, and apart from,
    -- every point the map puts before the join.  Under the hot row only
    -- joins lie, which carried rows have, and it has none.
    -- No point of the map lies strictly under a carried hot row.
    hot-split : ∀ {q l₀ e x y} → C.PB q l₀ → Proper T₀ q e → M₀ x y → q ≺ x → (zs : Path) → x ≡ q ⊕ zs → ⊥
    hot-split {q} pb tq m qx [] e = ≺-irrefl {q} (subst (q ≺_) (trans e (⊕-identityʳ q)) qx)
    hot-split pb tq m qx (_ ∷ _) e = C.pb-img pb (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (jn i m (_ , tq) e)))))))

    hot-ahead : ∀ {q l₀ e e₁ x y} → C.PB q l₀ → Proper T₀ q e → T₀′ l₀ e₁ → p ≺ q → M x y
              → x ≺ (q ⊕ [ sub p ]) → ¬ (x ⊑ (q ⊕ [ sub p ])) → Ahead y (l₀ ⊕ [ sub p′ ])
    hot-ahead {q} {l₀} {x = x} {y} pb tq ul pq (inj₁ m) xk nxk = old (cmp3 x q)
      where
        old : x ≺ q ⊎ x ≡ q ⊎ q ≺ x → Ahead y (l₀ ⊕ [ sub p′ ])
        old (inj₁ xq) =
          ahead-over (C.pb-past pb (proj₁ tq) (λ _ {c} → proj₂ tq {c}) ul m xq (λ xq′ → nxk (⊑-trans xq′ (⊑-snoc⁺ q)))) (⊑-snoc⁺ l₀)
        old (inj₂ (inj₁ e)) = ⊥-elim (nxk (subst (λ z → x ⊑ (z ⊕ [ sub p ])) e (⊑-snoc⁺ x)))
        old (inj₂ (inj₂ qx)) = ⊥-elim (hot-split pb tq m qx (proj₁ (between {q} {x} [ sub p ] qx xk)) (proj₂ (between {q} {x} [ sub p ] qx xk)))
    hot-ahead {q} {l₀} pb tq ul pq (inj₂ (inj₁ (q′ , L , br′ , ci′ , _ , refl , refl))) xk _ =
      ahead-under (ahead-over (ahead-under (C.pb-past pb (proj₁ tq) (λ _ {c} → proj₂ tq {c}) ul (proj₁ (proj₂ (C.ext ci′))) qq
        (flat-lead br′ (_ , tq) qq)) (proj₂ (proj₂ (C.ext ci′)))) (⊑-snoc⁺ l₀)) (⊑-snoc⁺ L)
      where
        qq : q′ ≺ q
        qq = joined-back q′ q xk (flat-lead (_ , tq) br′)
    hot-ahead {q} {l₀} pb tq ul pq (inj₂ (inj₂ (refl , refl))) _ _ =
      ahead-under (ahead-over (C.pb-past pb (proj₁ tq) (λ _ {c} → proj₂ tq {c}) ul m₀ pq (hotB (_ , tq))) (⊑-snoc⁺ l₀)) (⊑-snoc⁺ p′)

    -- Trailing the annotated end: past, and apart from, the same points,
    -- the end's join carrying the plain end's.
    end-ahead : ∀ {q e c′ x y} → Proper T₀ q e → p ≺ q → T₀′ c′ end → M x y
              → x ≺ (q ⊕ [ sub p ]) → ¬ (x ⊑ (q ⊕ [ sub p ])) → Ahead y (c′ ⊕ [ sub p′ ])
    end-ahead {q} {c′ = c′} {x} tq pq tc′ m xk nxk with C.shown tc′ tt (λ {c₉} → endE {_} {c₉} tc′) (fewE tc′ tt)
    ... | k , ci , e₀ , tk , mt with end-of mt
    ...   | refl = Emb.mono reader-emb m rk (proj₁ shift) , λ yy → proj₂ shift (Emb.reflect reader-emb m rk yy)
      where
        br : BoundRow (er i) k
        br = end , tk , λ {c} tc → endP tk tc

        rk : M (k ⊕ [ sub p ]) (c′ ⊕ [ sub p′ ])
        rk = inj₂ (inj₁ (k , c′ , br , ci , ≺-≼-≺ {p} {q} {k} pq (proj₂ tq tk) , refl , refl))

        shift : x ≺ (k ⊕ [ sub p ]) × ¬ (x ⊑ (k ⊕ [ sub p ]))
        shift with ≼-split {q} {k} (proj₂ tq tk)
        ... | inj₂ e = subst (λ z → x ≺ (z ⊕ [ sub p ]) × ¬ (x ⊑ (z ⊕ [ sub p ]))) e (xk , nxk)
        ... | inj₁ qk = ≺-trans {x} {q ⊕ [ sub p ]} {k ⊕ [ sub p ]} xk qk′
                      , λ xk′ → nxk (conv (⊑-refl x) (≺→≼ {x} {q ⊕ [ sub p ]} xk) qk′ xk′)
          where
            qk′ : (q ⊕ [ sub p ]) ≺ (k ⊕ [ sub p ])
            qk′ = apart {q} {k} qk (flat-lead (_ , tq) br qk) [ sub p ] [ sub p ]

    pb-img′ : ∀ {k l l′} → PB k l → Img k l′ → ⊥
    pb-img′ (q , _ , pb , _ , _ , _ , refl , _) (inj₁ (q′ , _ , _ , ci , _ , _ , e , _)) =
      C.pb-img pb (subst (λ z → C.Img z _) (sym (⊕-injˡ q q′ e)) ci)
    pb-img′ (q , _ , _ , _ , _ , _ , refl , _) (inj₂ (e , _)) = last-sub (sym (⊕-injʳ q p e))

    pb-past′ : ∀ {k l e₀ e x y} → PB k l → t k e₀ → (Unpinned e₀ → Live t k) → u l e → M x y → x ≺ k → ¬ (x ⊑ k) → Ahead y l
    pb-past′ (_ , _ , pb , (_ , tq) , (_ , ul) , pq , refl , inj₁ refl) _ _ _ m xk nxk = hot-ahead pb tq ul pq m xk nxk
    pb-past′ (_ , _ , _ , (_ , tq) , _ , pq , refl , inj₂ (_ , tc′ , _ , refl)) _ _ _ m xk nxk = end-ahead tq pq tc′ m xk nxk

  -- THE READER CARRIES its hot's carry: a joined row on its joined
  -- carrier, a late end on a late end; a row the hot carries into its
  -- instant, into the instant of the hot's row.
  -- The reader listed before a point its carriers follow.
  postulate
    reader-cover : ∀ {v w} → Listed t v → HotsListed envP v → Live t v → From Img PB t u v w → Listed u w

  reader-rejoined : CarryAt annValues M (Hots envP) (Hots envE) (HotsListed envP) t u p p′
  reader-rejoined = record
    { Img = Img ; ext = ext ; PB = PB ; pb-few = pb-few ; img = img ; img¬¬ = img¬¬ ; shown = shown′ ; img-row = img-row
    ; img-fun = img-fun ; place = place ; live = live ; few = few ; whole = whole ; cover = reader-cover ; bk = bk ; in-bk = in-bk
    ; pb-img = pb-img′ ; pb-past = pb-past′ ; pinned = λ { (shown _ () _ , _) } }
