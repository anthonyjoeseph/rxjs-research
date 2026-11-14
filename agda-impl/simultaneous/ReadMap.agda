{-# OPTIONS --guardedness #-}

-- THE READER'S MAP: a reader at `p` of a simulated hot pairs each plain
-- joined value or end with its row's carrier joined at the
-- subscription's image `p′`, and the late end with the late end (`Mr`).
-- Within the pair's worlds the ambient map holds the pair alone, and an
-- ambient point under a hot row is a join, so the two maps together
-- embed the order; nothing `Mr` pairs lies under a plain joined row.
module simultaneous.ReadMap where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_; yes; no)

open import denotation.Position using (Pos; root; _≟ᵖ_; _⊕_; sub; last)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (end; Unpinned; Few; EmissionSet; Truncate; Rejoin; shown; heard; ended; late; _≺_; _≼_)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≺-trans; ≺→≼; ≼-refl; ≼-trans; ≼-antisym; ≺-≼-≺; ≼-≺-≺; ≼-split; ≼-or-≻; ≺-ext)
open import denotation.Laws.Worlds using (Lawful; _⊑_; plain-last; ⊕-assoc; ⊕-identityʳ; ⊕-injˡ; ⊕-injʳ; ⊑-refl; ⊑-trans;
  ⊑-≼; ⊑-snoc; ⊑-snoc⁺; ⊑-cmp) renaming (here to w-here; inW to w-in; step to w-step; join to w-join)
open import denotation.Laws.Count using (⊑?)
open import adequacy.SubJoin using (lower)
open import simultaneous.SimPos using (apart; apart₁; flat-apart; ⊑-split; upto-down; lie; above; below; left; right; join-lt; join-back;
  join-fwd; ⊕-cons)
open import simultaneous.Sim using (PMap; _∪ᴹ_; Emb; Sim; Carried; Local; Fresh; Below; NoneUnder; Joins; AShows; AShown; Upto; Under;
  Mapped; Within; BoundOk)
open import simultaneous.ReadRows using (module Rows)
open import simultaneous.SObs using (lone; module Elaborate)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (AIE)

-- Leading and after: never both.
⊑-≺ : ∀ {x y} → x ⊑ y → y ≺ x → ⊥
⊑-≺ {x} {y} h lt = ≺-irrefl {y} (≺-≼-≺ {y} {x} {y} lt (⊑-≼ {x} {y} h))

------------------------------------------------------------------------
-- Points of a subscription's world

below-join : ∀ {K : Pos → Set} {r h} → K h → r ≺ h → Below K r (h ⊕ [ sub r ])
below-join k rh = _ , w-in (w-join (inj₁ k) w-here rh) , ⊑-refl _

below-last : ∀ {K : Pos → Set} {r} → Below K r (r ⊕ [ last ])
below-last = _ , w-in (w-step w-here plain-last) , ⊑-refl _

below-up : ∀ {K : Pos → Set} {r x y} → Below K r x → x ⊑ y → Below K r y
below-up (w , ww , wx) xy = w , ww , ⊑-trans wx xy

below-at : ∀ {K : Pos → Set} {r x} → r ⊑ x → Below K r x
below-at h = _ , w-here , h

------------------------------------------------------------------------
-- The map

module Map {X : Set} (Amb : PMap) (H H′ : Pos → Set) (S : EmissionSet X) (G : EmissionSet (AIE X)) {c₀}
           (hs : Sim AShows AShown Amb c₀ S G) (joins : Joins Amb Amb S (Sim.Img hs))
           (lawS : Lawful S) (lawG : Lawful G) (fewG : ∀ {q e} → G q e → Unpinned e → Few G q)
           (hS : ∀ {q e} → S q e → H q) (hG : ∀ {q e} → G q e → H′ q)
           (em : Emb Amb) (p p′ : Pos) (pp : Amb p p′) (fr : Fresh H H′ Amb p p′) (nh : ¬ H p) where

  open Rows G p′ lawG fewG using (at-unique; at-apart)

  open Sim hs using () renaming (Img to Car; img-fun to car-fun; ext to car-ext)
  open Emb em using () renaming (fun to a-fun; mono to a-mono; reflect to a-refl)

  fresh₁ : ∀ {x y} → Amb x y → Below H p x → x ≡ p
  fresh₁ a = proj₁ (fr a)

  fresh₂ : ∀ {x y} → Amb x y → Below H′ p′ y → y ≡ p′
  fresh₂ a = proj₂ (fr a)

  -- An ambient point under the subscription is the subscription.
  at-p : ∀ {x y} → Amb x y → p ⊑ x → x ≡ p
  at-p a h = fresh₁ a (below-at h)

  -- No ambient image lies under a carrier joined, or the late end.
  amb-car : ∀ {x y L e′} → Amb x y → G L e′ → p′ ≺ L → (L ⊕ [ sub p′ ]) ⊑ y → ⊥
  amb-car {L = L} a g pL h with fresh₂ a (below-up (below-join (hG g) pL) h)
  ... | refl = ⊑-≺ h (≺-trans {p′} {L} {L ⊕ [ sub p′ ]} pL (≺-ext L {sub p′} []))

  amb-late : ∀ {x y} → Amb x y → (p′ ⊕ [ last ]) ⊑ y → ⊥
  amb-late a h with fresh₂ a (below-up below-last h)
  ... | refl = ⊑-≺ h (≺-ext p′ {last} [])

  -- No ambient point at a joined row, or the late end.
  amb-join : ∀ {x y q e} → Amb x y → S q e → p ≺ q → x ≡ q ⊕ [ sub p ] → ⊥
  amb-join {q = q} a s pk refl =
    ≺-irrefl {p} (subst (p ≺_) (fresh₁ a (below-join (hS s) pk)) (≺-trans {p} {q} {q ⊕ [ sub p ]} pk (≺-ext q {sub p} [])))

  amb-lt : ∀ {x y} → Amb x y → x ≡ p ⊕ [ last ] → ⊥
  amb-lt a refl = ≺-irrefl {p} (subst (p ≺_) (fresh₁ a below-last) (≺-ext p {last} []))

  -- No hot row lies past the hot's end.
  no-late : ∀ {c k e} → S c end → c ≼ p → S k e → p ≺ k → ⊥
  no-late {c} {k} sc cp s pk = ≺-irrefl {p} (≺-≼-≺ {p} {k} {p} pk (≼-trans {k} {c} {p} (Lawful.proper lawS sc s) cp))

  ----------------------------------------------------------------------
  -- Carriers

  -- A row past the subscription: its carrier past the image.
  past-sup : ∀ {k L} → p ≺ k → Car k L → p′ ≺ L
  past-sup {k} {L} pk car with car-ext car
  ... | y , a , yL = ≺-≼-≺ {p′} {y} {L} (a-mono pp a pk) (⊑-≼ {y} {L} yL)

  -- A row before an ambient point: its carrier before the point's image.
  car-before : ∀ {q e L x y} → S q e → Car q L → Amb x y → q ≺ x → L ≺ y
  car-before {q} {y = y} s car a′ lt with car-ext car
  ... | yq , a , (zs , refl) with ⊑? yq y
  ...   | no ny = apart₁ {yq} {y} (a-mono a a′ lt) ny zs
  ...   | yes yy with a-refl a a′ yy
  ...     | [] , e = ⊥-elim (≺-irrefl {q} (subst (q ≺_) (trans e (⊕-identityʳ q)) lt))
  ...     | (l ∷ σ) , e with joins a′ s e
  ...       | _ , refl , e′ , _ , L′ , car′ , h with car-fun car car′
  ...         | refl = ≺-≼-≺ {yq ⊕ zs} {(yq ⊕ zs) ⊕ [ sub e′ ]} {y} (≺-ext (yq ⊕ zs) {sub e′} []) (⊑-≼ {(yq ⊕ zs) ⊕ [ sub e′ ]} {y} h)

  -- A row at or before an ambient point: its carrier up to the point's image.
  car-under : ∀ {q e L x y} → S q e → Car q L → Amb x y → q ≼ x → L ≺ y ⊎ y ⊑ L
  car-under {q} {x = x} s car a′ qx with ≼-split {q} {x} qx
  ... | inj₁ lt = inj₁ (car-before s car a′ lt)
  ... | inj₂ refl with car-ext car
  ...   | yq , a , yL with a-fun a a′
  ...     | refl = inj₂ yL

  -- A carrier past the image: its row past the subscription.
  past-sub : ∀ {q L e} → S q e → Car q L → p′ ≺ L → p ≺ q
  past-sub {q} {L} s car pL with ≼-or-≻ q p
  ... | inj₂ pq = pq
  ... | inj₁ qp with ≼-split {q} {p} qp
  ...   | inj₂ refl = ⊥-elim (nh (hS s))
  ...   | inj₁ q<p  = ⊥-elim (≺-absurd {p′} {L} pL (car-before s car pp q<p))

  -- The hot ended by the subscription: its end's carrier before the image.
  late-car : ∀ {c L} → S c end → c ≼ p → Car c L → L ≺ p′
  late-car {c} sc cp car with ≼-split {c} {p} cp
  ... | inj₁ lt   = car-before sc car pp lt
  ... | inj₂ refl = ⊥-elim (nh (hS sc))

  -- Carriers keep the order of their rows.
  car-mono : ∀ {q q′ L L′ e e′} → S q e → S q′ e′ → Car q L → Car q′ L′ → q ≺ q′ → L ≺ L′
  car-mono {q} {q′} s s′ car car′ lt with car-ext car | car-ext car′
  ... | y , a , (zs , refl) | y′ , a′ , (zs′ , refl) with ⊑? y y′
  ...   | no ny  = apart {y} {y′} (a-mono a a′ lt) ny zs zs′
  ...   | yes yy = ⊥-elim (flat-apart lawS s s′ lt (a-refl a a′ yy))

  car-inj : ∀ {q q′ L e e′} → S q e → S q′ e′ → Car q L → Car q′ L → q ≡ q′
  car-inj {q} {q′} {L} s s′ car car′ with ≼-or-≻ q q′
  ... | inj₂ q′q = ⊥-elim (≺-irrefl {L} (car-mono s′ s car′ car q′q))
  ... | inj₁ qq′ with ≼-split {q} {q′} qq′
  ...   | inj₂ eq = eq
  ...   | inj₁ lt = ⊥-elim (≺-irrefl {L} (car-mono s s′ car car′ lt))

  -- Two ambient points apart: their images too, everything under the first.
  amb-apart : ∀ {x y x′ y′} → Amb x y → Amb x′ y′ → x ≺ x′ → ¬ (x ⊑ x′) → ∀ σ → (y ⊕ σ) ≺ y′
  amb-apart {x} {y} {x′} {y′} a a′ lt nx σ with ⊑? y y′
  ... | yes yy = ⊥-elim (nx (a-refl a a′ yy))
  ... | no ny  = apart₁ {y} {y′} (a-mono a a′ lt) ny σ

  car-apart : ∀ {k L x′ y′} → Car k L → Amb x′ y′ → k ≺ x′ → ¬ (k ⊑ x′) → (L ⊕ [ sub p′ ]) ≺ y′
  car-apart {L = L} {y′ = y′} car a′ lt nk with car-ext car
  ... | yk , ak , (zs , refl) = subst (_≺ y′) (sym (⊕-assoc yk zs [ sub p′ ])) (amb-apart ak a′ lt nk (zs ++ [ sub p′ ]))

  -- A point at or before a row: its image before the carrier joined.
  before-car : ∀ {x y k L} → Amb x y → Car k L → x ≡ k ⊎ x ≺ k → y ≺ (L ⊕ [ sub p′ ])
  before-car {x} {y} {k} {L} a car xk with car-ext car
  ... | yk , ak , yL with xk
  ...   | inj₂ lt = ≺-≼-≺ {y} {yk} {L ⊕ [ sub p′ ]} (a-mono a ak lt) (⊑-≼ {yk} {L ⊕ [ sub p′ ]} (⊑-trans yL (⊑-snoc⁺ L)))
  ...   | inj₁ refl with a-fun a ak
  ...     | refl = ≼-≺-≺ {y} {L} {L ⊕ [ sub p′ ]} (⊑-≼ {y} {L} yL) (≺-ext L {sub p′} [])

  -- A point at or before the subscription: its image before the late end.
  before-p : ∀ {x y} → Amb x y → x ≡ p ⊎ x ≺ p → y ≺ (p′ ⊕ [ last ])
  before-p {y = y} a (inj₂ lt) = ≺-trans {y} {p′} {p′ ⊕ [ last ]} (a-mono a pp lt) (≺-ext p′ {last} [])
  before-p a (inj₁ refl) with a-fun a pp
  ... | refl = ≺-ext p′ {last} []

  ----------------------------------------------------------------------
  -- THE MAP: each joined value or end at its carrier joined; the late end
  -- at the late end.

  data Mr (x y : Pos) : Set where
    mrow  : ∀ {k e L e′} → S k e → Carried e → p ≺ k → Car k L → G L e′ → x ≡ k ⊕ [ sub p ] → y ≡ L ⊕ [ sub p′ ] → Mr x y
    mlate : ∀ {c} → S c end → c ≼ p → x ≡ p ⊕ [ last ] → y ≡ p′ ⊕ [ last ] → Mr x y

  amb-mr : ∀ {x y y′} → Amb x y → Mr x y′ → ⊥
  amb-mr a (mrow s _ pk _ _ e _) = amb-join a s pk e
  amb-mr a (mlate _ _ e _)       = amb-lt a e

  -- No ambient point at a plain joined row.
  amb-t : ∀ {x y e} → Amb x y → Rejoin p S x e → ⊥
  amb-t a (shown s _ pk) = amb-join a s pk refl
  amb-t a (heard s pk)   = amb-join a s pk refl
  amb-t a (ended s pk)   = amb-join a s pk refl
  amb-t a (late _ _)     = amb-lt a refl

  mr-fun : ∀ {x y y′} → Mr x y → Mr x y′ → y ≡ y′
  mr-fun (mrow {k} _ _ _ car _ refl refl) (mrow {k′} _ _ _ car′ _ ex refl) with ⊕-injˡ k k′ ex
  ... | refl = cong (_⊕ [ sub p′ ]) (car-fun car car′)
  mr-fun (mrow {k} _ _ _ _ _ refl _) (mlate _ _ ex _) with ⊕-injʳ k p ex
  ... | ()
  mr-fun (mlate _ _ refl _) (mrow {k} _ _ _ _ _ ex _) with ⊕-injʳ p k ex
  ... | ()
  mr-fun (mlate _ _ refl refl) (mlate _ _ _ refl) = refl

  -- In order.
  mr-mono : ∀ {x x′ y y′} → Mr x y → Mr x′ y′ → x ≺ x′ → y ≺ y′
  mr-mono (mrow {k} {L = L} s _ _ car g refl refl) (mrow {k′} {L = L′} s′ _ _ car′ g′ refl refl) lt =
    let LL = car-mono s s′ car car′ (lower lawS {s = sub p} s′ s lt) in apart {L} {L′} LL (flat-apart lawG g g′ LL) [ sub p′ ] [ sub p′ ]
  mr-mono (mrow s _ pk _ _ refl refl) (mlate sc cp refl refl) _ = ⊥-elim (no-late sc cp s pk)
  mr-mono (mlate sc cp refl refl) (mrow s _ pk _ _ refl refl) _ = ⊥-elim (no-late sc cp s pk)
  mr-mono (mlate _ _ refl refl) (mlate _ _ refl refl) lt = ⊥-elim (≺-irrefl {p ⊕ [ last ]} lt)

  am-under : ∀ {x y k L e₀} → Amb x y → S k e₀ → Car k L → x ≺ (k ⊕ [ sub p ]) → ∀ σ → x ≡ k ⊕ σ → y ≺ (L ⊕ [ sub p′ ])
  am-under {k = k} a s car lt [] e = before-car a car (inj₁ (trans e (⊕-identityʳ k)))
  am-under {x} {k = k} {L} a s car lt (l ∷ σ) e with joins a s e
  ... | _ , refl , e′ , ae , L′ , car′ , (τ , refl) with car-fun car car′
  ...   | refl = subst (_≺ (L ⊕ [ sub p′ ])) (⊕-cons L (sub e′) τ)
                   (join-lt L τ [] (a-mono ae pp (join-back k σ (subst (_≺ (k ⊕ [ sub p ])) e lt))))

  am-mono : ∀ {x x′ y y′} → Amb x y → Mr x′ y′ → x ≺ x′ → y ≺ y′
  am-mono {x} a (mrow {k} s _ pk car g refl refl) lt with lie x k
  ... | above xk       = before-car a car (⊑-split xk)
  ... | left xk _ _    = before-car a car (inj₂ xk)
  ... | right kx _ nkx = ⊥-elim (≺-absurd {x} {k ⊕ [ sub p ]} lt (apart₁ {k} {x} kx nkx [ sub p ]))
  ... | below (σ , e)  = am-under a s car lt σ e
  am-mono {x} a (mlate sc cp refl refl) lt with lie x p
  ... | above xp       = before-p a (⊑-split xp)
  ... | left xp _ _    = before-p a (inj₂ xp)
  ... | below px       = before-p a (inj₁ (at-p a px))
  ... | right px _ npx = ⊥-elim (≺-absurd {x} {p ⊕ [ last ]} lt (apart₁ {p} {x} px npx [ last ]))

  ma-under : ∀ {x′ y′ k L e₀ e₁} → Amb x′ y′ → S k e₀ → p ≺ k → Car k L → G L e₁ → (k ⊕ [ sub p ]) ≺ x′
           → ∀ l σ → x′ ≡ k ⊕ (l ∷ σ) → (L ⊕ [ sub p′ ]) ≺ y′
  ma-under {k = k} {L} a′ s pk car g lt l σ e with joins a′ s e
  ... | e₂ , refl , e′ , ae , L′ , car′ , (τ , refl) with car-fun car car′
  ...   | refl with join-fwd k σ (subst ((k ⊕ [ sub p ]) ≺_) e lt)
  ...     | inj₂ pe = subst ((L ⊕ [ sub p′ ]) ≺_) (⊕-cons L (sub e′) τ) (join-lt L [] τ (a-mono pp ae pe))
  ...     | inj₁ refl with a-fun ae pp
  ...       | refl = ⊥-elim (amb-car a′ g (past-sup pk car) (τ , refl))

  ma-mono : ∀ {x x′ y y′} → Mr x y → Amb x′ y′ → x ≺ x′ → y ≺ y′
  ma-mono {x′ = x′} (mrow {k} s _ pk car g refl refl) a′ lt with lie k x′
  ... | below xk       = ⊥-elim (⊑-≺ xk (≺-trans {k} {k ⊕ [ sub p ]} {x′} (≺-ext k {sub p} []) lt))
  ... | right xk _ _   = ⊥-elim (≺-absurd {x′} {k} xk (≺-trans {k} {k ⊕ [ sub p ]} {x′} (≺-ext k {sub p} []) lt))
  ... | left kx nkx _  = car-apart car a′ kx nkx
  ... | above ([] , e) = ⊥-elim (≺-absurd {k} {k ⊕ [ sub p ]} (≺-ext k {sub p} [])
                           (subst ((k ⊕ [ sub p ]) ≺_) (trans e (⊕-identityʳ k)) lt))
  ... | above ((l ∷ σ) , e) = ma-under a′ s pk car g lt l σ e
  ma-mono {x′ = x′} (mlate sc cp refl refl) a′ lt with lie p x′
  ... | above px      = ⊥-elim (≺-absurd {p} {p ⊕ [ last ]} (≺-ext p {last} []) (subst ((p ⊕ [ last ]) ≺_) (at-p a′ px) lt))
  ... | below xp      = ⊥-elim (⊑-≺ xp (≺-trans {p} {p ⊕ [ last ]} {x′} (≺-ext p {last} []) lt))
  ... | right xp _ _  = ⊥-elim (≺-absurd {x′} {p} xp (≺-trans {p} {p ⊕ [ last ]} {x′} (≺-ext p {last} []) lt))
  ... | left px npx _ = amb-apart pp a′ px npx [ last ]

  -- Leading reflected.
  mr-refl : ∀ {x x′ y y′} → Mr x y → Mr x′ y′ → y ⊑ y′ → x ⊑ x′
  mr-refl (mrow {k} {L = L} s _ pk car g refl refl) (mrow {k′} {L = L′} {e₂} s′ _ _ car′ g′ refl refl) h with ⊑-snoc L′ h
  ... | inj₁ (zs , e) = ⊥-elim (Lawful.flat lawG g (subst (λ z → G z e₂) (trans e (⊕-assoc L [ sub p′ ] zs)) g′))
  ... | inj₂ e with ⊕-injˡ L L′ e
  ...   | refl with car-inj s s′ car car′
  ...     | refl = ⊑-refl _
  mr-refl (mrow {L = L} s _ pk car g refl refl) (mlate _ _ refl refl) h with ⊑-snoc p′ h
  ... | inj₁ h′ = ⊥-elim (⊑-≺ h′ (≺-trans {p′} {L} {L ⊕ [ sub p′ ]} (past-sup pk car) (≺-ext L {sub p′} [])))
  ... | inj₂ e with ⊕-injʳ L p′ e
  ...   | ()
  mr-refl (mlate sc cp refl refl) (mrow s _ pk _ _ refl refl) _ = ⊥-elim (no-late sc cp s pk)
  mr-refl (mlate _ _ refl refl) (mlate _ _ refl refl) _ = ⊑-refl _

  am-refl : ∀ {x x′ y y′} → Amb x y → Mr x′ y′ → y ⊑ y′ → x ⊑ x′
  am-refl {y = y} a (mrow {k} {L = L} s _ pk car g refl refl) h with ⊑-snoc L h
  ... | inj₂ e = ⊥-elim (amb-car a g (past-sup pk car) (subst ((L ⊕ [ sub p′ ]) ⊑_) (sym e) (⊑-refl _)))
  ... | inj₁ yL with car-ext car
  ...   | yk , ak , ykL with ⊑-cmp y yk yL ykL
  ...     | inj₁ yyk = ⊑-trans (a-refl a ak yyk) (⊑-snoc⁺ k)
  ...     | inj₂ yky with a-refl ak a yky
  ...       | [] , e = subst (_⊑ (k ⊕ [ sub p ])) (sym (trans e (⊕-identityʳ k))) (⊑-snoc⁺ k)
  ...       | (l ∷ σ) , e with joins a s e
  ...         | _ , refl , e′ , _ , L′ , car′ , h′ with car-fun car car′
  ...           | refl = ⊥-elim (⊑-≺ (⊑-trans h′ yL) (≺-ext L {sub e′} []))
  am-refl a (mlate _ _ refl refl) h with ⊑-snoc p′ h
  ... | inj₁ yp = ⊑-trans (a-refl a pp yp) (⊑-snoc⁺ p)
  ... | inj₂ e  = ⊥-elim (amb-late a (subst ((p′ ⊕ [ last ]) ⊑_) (sym e) (⊑-refl _)))

  ma-refl : ∀ {x x′ y y′} → Mr x y → Amb x′ y′ → y ⊑ y′ → x ⊑ x′
  ma-refl (mrow _ _ pk car g refl refl) a′ h = ⊥-elim (amb-car a′ g (past-sup pk car) h)
  ma-refl (mlate _ _ refl refl)         a′ h = ⊥-elim (amb-late a′ h)

  -- THE AMBIENT MAP WITH THE READER'S: an order embedding.
  emb : Emb (Amb ∪ᴹ Mr)
  emb = record { fun = fu ; mono = mo ; reflect = re }
    where
      fu : ∀ {x y y′} → (Amb ∪ᴹ Mr) x y → (Amb ∪ᴹ Mr) x y′ → y ≡ y′
      fu (inj₁ a) (inj₁ a′) = a-fun a a′
      fu (inj₁ a) (inj₂ m)  = ⊥-elim (amb-mr a m)
      fu (inj₂ m) (inj₁ a)  = ⊥-elim (amb-mr a m)
      fu (inj₂ m) (inj₂ m′) = mr-fun m m′

      mo : ∀ {x x′ y y′} → (Amb ∪ᴹ Mr) x y → (Amb ∪ᴹ Mr) x′ y′ → x ≺ x′ → y ≺ y′
      mo (inj₁ a) (inj₁ a′) = a-mono a a′
      mo (inj₁ a) (inj₂ m)  = am-mono a m
      mo (inj₂ m) (inj₁ a)  = ma-mono m a
      mo (inj₂ m) (inj₂ m′) = mr-mono m m′

      re : ∀ {x x′ y y′} → (Amb ∪ᴹ Mr) x y → (Amb ∪ᴹ Mr) x′ y′ → y ⊑ y′ → x ⊑ x′
      re (inj₁ a) (inj₁ a′) = a-refl a a′
      re (inj₁ a) (inj₂ m)  = am-refl a m
      re (inj₂ m) (inj₁ a)  = ma-refl m a
      re (inj₂ m) (inj₂ m′) = mr-refl m m′

  -- Within the pair's worlds.
  local : Local H H′ p p′ Mr
  local (mrow s _ pk car g refl refl) = below-join (hS s) pk , below-join (hG g) (past-sup pk car)
  local (mlate _ _ refl refl)         = below-last , below-last

  -- Nothing under a plain joined row.
  nu-row : ∀ {q e₀ x y} → S q e₀ → p ≺ q → Mr x y → (q ⊕ [ sub p ]) ⊑ x → x ≡ q ⊕ [ sub p ]
  nu-row {q} s pk (mrow {k} {e₂} s′ _ _ _ _ refl _) h with ⊑-snoc k h
  ... | inj₁ (zs , e) = ⊥-elim (Lawful.flat lawS s (subst (λ z → S z e₂) (trans e (⊕-assoc q [ sub p ] zs)) s′))
  ... | inj₂ e = sym e
  nu-row {q} s pk (mlate _ _ refl _) h with ⊑-snoc p h
  ... | inj₁ qp = ⊥-elim (⊑-≺ qp (≺-trans {p} {q} {q ⊕ [ sub p ]} pk (≺-ext q {sub p} [])))
  ... | inj₂ e with ⊕-injʳ q p e
  ...   | ()

  none-under : NoneUnder Mr (Truncate (Rejoin p S))
  none-under (shown s _ pk , _) m h = nu-row s pk m h
  none-under (heard s pk , _)   m h = nu-row s pk m h
  none-under (ended s pk , _)   m h = nu-row s pk m h
  none-under (late sc cp , _) (mrow s _ pk _ _ refl _) h = ⊥-elim (no-late sc cp s pk)
  none-under (late _ _ , _)   (mlate _ _ refl _)       h = refl

  ----------------------------------------------------------------------
  -- UNDER THE READER'S BOUND, the joined rows' carriers lie under the
  -- hot's.  The bound's image leads no elaborated hot row, or is a plain
  -- joined row's: a carrier joined, or the late end.

  amb-bound : ∀ {c₁ c₂ y y₀ z} → Amb c₁ y → Amb c₂ y₀ → c₁ ≼ c₂ → z ≺ y → z ≺ y₀
  amb-bound {c₁} {c₂} {y} {y₀} {z} a a₀ cc zy with ≼-split {c₁} {c₂} cc
  ... | inj₁ lt = ≺-trans {z} {y} {y₀} zy (a-mono a a₀ lt)
  ... | inj₂ refl with a-fun a a₀
  ...   | refl = zy

  -- An image leading no hot row: a joined row under or before it lies before it.
  row-bound : ∀ {l₀ e₀ m y} → G l₀ e₀ → (l₀ ⊕ [ sub p′ ]) ⊑ m → (∀ {h} → H′ h → y ⊑ h → ⊥) → (m ≺ y ⊎ y ⊑ m) → l₀ ≺ y
  row-bound {l₀} {m = m} {y} g am nl (inj₁ my) =
    ≺-trans {l₀} {m} {y} (≺-≼-≺ {l₀} {l₀ ⊕ [ sub p′ ]} {m} (≺-ext l₀ {sub p′} []) (⊑-≼ {l₀ ⊕ [ sub p′ ]} {m} am)) my
  row-bound {l₀} {m = m} {y} g am nl (inj₂ ym) with lie y l₀
  ... | above yl     = ⊥-elim (nl (hG g) yl)
  ... | right ly _ _ = ly
  ... | below ly with ⊑-split ly
  ...   | inj₁ refl = ⊥-elim (nl (hG g) (⊑-refl _))
  ...   | inj₂ lt   = lt
  row-bound {l₀} {m = m} {y} g am nl (inj₂ ym) | left _ nyl nly with ⊑-cmp y (l₀ ⊕ [ sub p′ ]) ym am
  ... | inj₂ ly = ⊥-elim (nly (⊑-trans (⊑-snoc⁺ l₀) ly))
  ... | inj₁ yl with ⊑-snoc l₀ yl
  ...   | inj₁ h    = ⊥-elim (nyl h)
  ...   | inj₂ refl = ⊥-elim (nly (⊑-snoc⁺ l₀))

  late-bound : ∀ {c₂ y} → G c₂ end → c₂ ≼ p′ → (∀ {h} → H′ h → y ⊑ h → ⊥) → ((p′ ⊕ [ last ]) ≺ y ⊎ y ⊑ (p′ ⊕ [ last ])) → c₂ ≺ y
  late-bound {c₂} {y} g cp nl (inj₁ ly) = ≼-≺-≺ {c₂} {p′} {y} cp (≺-trans {p′} {p′ ⊕ [ last ]} {y} (≺-ext p′ {last} []) ly)
  late-bound {c₂} {y} g cp nl (inj₂ yl) with ⊑-snoc p′ yl
  ... | inj₂ refl = ≼-≺-≺ {c₂} {p′} {p′ ⊕ [ last ]} cp (≺-ext p′ {last} [])
  ... | inj₁ (σ , refl) with lie c₂ y
  ...   | below yc       = ⊥-elim (nl (hG g) yc)
  ...   | left cy _ _    = cy
  ...   | right yc _ nyc = ⊥-elim (cp (apart₁ {y} {c₂} yc nyc σ))
  ...   | above cy with ⊑-split cy
  ...     | inj₂ lt   = lt
  ...     | inj₁ refl = ⊥-elim (nl (hG g) (⊑-refl _))

  -- The plain late end's carrier, where the bound reaches the late end.
  LateCar : Maybe Pos → Set
  LateCar c = ∀ {q} → S q end → q ≼ p → Upto c (p ⊕ [ last ]) → Σ Pos λ E → Car q E × G E end

  under-row : ∀ c c₀′ → Within c c₀′ → Mapped Amb c₀′ → BoundOk H′ Amb (Truncate (Rejoin p S)) c → LateCar c
            → ∀ {l₀ e₀ m} → G l₀ e₀ → p′ ≺ l₀ → (l₀ ⊕ [ sub p′ ]) ⊑ m → Under (Amb ∪ᴹ Mr) c m → Under Amb c₀′ l₀
  under-row nothing   nothing    _  _ _ _ _ _ _ _ = tt
  under-row nothing   (just _)   () _ _ _ _ _ _ _
  under-row (just _)  nothing    _  _ _ _ _ _ _ _ = tt
  under-row (just c₁) (just c₀₁) cc (y₀ , a₀) (inj₂ (_ , _ , r , _)) lc g pl am (y , inj₁ a , u) = ⊥-elim (amb-t a r)
  under-row (just c₁) (just c₀₁) cc (y₀ , a₀) (inj₁ (y′ , a′ , nl)) lc {l₀} g pl am (y , inj₁ a , u) with a-fun a a′
  ... | refl = y₀ , a₀ , inj₁ (amb-bound {z = l₀} a a₀ cc (row-bound g am nl u))
  under-row (just c₁) (just c₀₁) cc (y₀ , a₀) B lc {l₀} g pl (σ , refl) (y , inj₂ (mrow {q} {L = L} s _ pk car gL refl refl) , u) =
    y₀ , a₀ , pick u
    where
      cu : L ≺ y₀ ⊎ y₀ ⊑ L
      cu = car-under s car a₀ (≺→≼ {q} {c₀₁} (≺-≼-≺ {q} {q ⊕ [ sub p ]} {c₀₁} (≺-ext q {sub p} []) cc))

      at-L : l₀ ≡ L → l₀ ≺ y₀ ⊎ y₀ ⊑ l₀
      at-L refl = cu

      pick : ((l₀ ⊕ [ sub p′ ]) ⊕ σ) ≺ (L ⊕ [ sub p′ ]) ⊎ (L ⊕ [ sub p′ ]) ⊑ ((l₀ ⊕ [ sub p′ ]) ⊕ σ) → l₀ ≺ y₀ ⊎ y₀ ⊑ l₀
      pick (inj₂ h) = at-L (sym (at-unique gL g h (σ , refl)))
      pick (inj₁ ml) with ≼-or-≻ l₀ L
      ... | inj₂ Ll = ⊥-elim (≺-absurd {(l₀ ⊕ [ sub p′ ]) ⊕ σ} {L ⊕ [ sub p′ ]} ml
                        (subst (_≺ ((l₀ ⊕ [ sub p′ ]) ⊕ σ)) (⊕-identityʳ (L ⊕ [ sub p′ ])) (at-apart gL g Ll [] σ)))
      ... | inj₁ lL with ≼-split {l₀} {L} lL
      ...   | inj₁ lt = upto-down {y₀} {L} {l₀} lt cu
      ...   | inj₂ eq = at-L eq
  under-row (just c₁) (just c₀₁) cc (y₀ , a₀) B lc {l₀} g pl am (y , inj₂ (mlate sc cp refl refl) , u) with lc sc cp (≼-refl {p ⊕ [ last ]})
  ... | E , carE , gE = ⊥-elim (≺-irrefl {p′} (≺-≼-≺ {p′} {l₀} {p′} pl (≼-trans {l₀} {E} {p′} (Lawful.proper lawG gE g) (≺→≼ {E} {p′} (late-car sc cp carE)))))

  under-late : ∀ c c₀′ → Within c c₀′ → Mapped Amb c₀′ → BoundOk H′ Amb (Truncate (Rejoin p S)) c → LateCar c
             → ∀ {c₂} → G c₂ end → c₂ ≼ p′ → Under (Amb ∪ᴹ Mr) c (p′ ⊕ [ last ]) → Under Amb c₀′ c₂
  under-late nothing   nothing    _  _ _ _ _ _ _ = tt
  under-late nothing   (just _)   () _ _ _ _ _ _
  under-late (just _)  nothing    _  _ _ _ _ _ _ = tt
  under-late (just c₁) (just c₀₁) cc (y₀ , a₀) (inj₂ (_ , _ , r , _)) lc g cp (y , inj₁ a , u) = ⊥-elim (amb-t a r)
  under-late (just c₁) (just c₀₁) cc (y₀ , a₀) (inj₁ (y′ , a′ , nl)) lc {c₂} g cp (y , inj₁ a , u) with a-fun a a′
  ... | refl = y₀ , a₀ , inj₁ (amb-bound {z = c₂} a a₀ cc (late-bound g cp nl u))
  under-late (just c₁) (just c₀₁) cc (y₀ , a₀) B lc {c₂} g cp (y , inj₂ (mrow {L = L} s _ pk car gL refl refl) , u) =
    ⊥-elim (≺-irrefl {p′} (≺-≼-≺ {p′} {L} {p′} (past-sup pk car) (≼-trans {L} {c₂} {p′} (Lawful.proper lawG g gL) cp)))
  under-late (just c₁) (just c₀₁) cc (y₀ , a₀) B lc {c₂} g cp (y , inj₂ (mlate {q} sc qp refl refl) , u) with lc sc qp (≼-refl {p ⊕ [ last ]})
  ... | E , carE , gE with ≼-antisym {c₂} {E} (Lawful.proper lawG gE g) (Lawful.proper lawG g gE)
  ...   | refl = y₀ , a₀ , car-under sc carE a₀ (≺→≼ {q} {c₀₁} (≼-≺-≺ {q} {p} {c₀₁} qp (≺-≼-≺ {p} {p ⊕ [ last ]} {c₀₁} (≺-ext p {last} []) cc)))
