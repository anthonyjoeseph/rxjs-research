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
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_; yes; no)

open import denotation.Position using (Pos; root; _≟ᵖ_; _⊕_; sub; last)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (end; EmissionSet; Truncate; Rejoin; shown; heard; ended; late; _≺_; _≼_)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≺-trans; ≼-trans; ≺-≼-≺; ≼-≺-≺; ≼-split; ≼-or-≻; ≺-ext)
open import denotation.Laws.Worlds using (Lawful; _⊑_; plain-last; ⊕-assoc; ⊕-identityʳ; ⊕-injˡ; ⊕-injʳ; ⊑-refl; ⊑-trans;
  ⊑-≼; ⊑-snoc; ⊑-snoc⁺; ⊑-cmp) renaming (here to w-here; inW to w-in; step to w-step; join to w-join)
open import denotation.Laws.Count using (⊑?)
open import adequacy.SubJoin using (lower)
open import simultaneous.SimPos using (apart; apart₁; flat-apart; ⊑-split; lie; above; below; left; right; join-lt; join-back;
  join-fwd; ⊕-cons)
open import simultaneous.Sim using (PMap; _∪ᴹ_; Emb; Sim; Carried; Local; Fresh; Below; NoneUnder; Joins; AShows; AShown)
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
           (lawS : Lawful S) (lawG : Lawful G) (hS : ∀ {q e} → S q e → H q) (hG : ∀ {q e} → G q e → H′ q)
           (em : Emb Amb) (p p′ : Pos) (pp : Amb p p′) (fr : Fresh H H′ Amb p p′) (nh : ¬ H p) where

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

  -- No hot row lies past the hot's end.
  no-late : ∀ {c k e} → S c end → c ≼ p → S k e → p ≺ k → ⊥
  no-late {c} {k} sc cp s pk = ≺-irrefl {p} (≺-≼-≺ {p} {k} {p} pk (≼-trans {k} {c} {p} (Lawful.proper lawS sc s) cp))

  ----------------------------------------------------------------------
  -- Carriers

  -- A row past the subscription: its carrier past the image.
  past-sup : ∀ {k L} → p ≺ k → Car k L → p′ ≺ L
  past-sup {k} {L} pk car with car-ext car
  ... | y , a , yL = ≺-≼-≺ {p′} {y} {L} (a-mono pp a pk) (⊑-≼ {y} {L} yL)

  -- A carrier past the image: its row past the subscription.
  past-sub : ∀ {q L e} → S q e → Car q L → p′ ≺ L → p ≺ q
  past-sub {q} {L} s car pL with ≼-or-≻ q p
  ... | inj₂ pq = pq
  ... | inj₁ qp with ≼-split {q} {p} qp
  ...   | inj₂ refl = ⊥-elim (nh (hS s))
  ...   | inj₁ q<p with car-ext car
  ...     | y , a , (zs , refl) with ⊑? y p′
  ...       | no ny = ⊥-elim (≺-absurd {p′} {y ⊕ zs} pL (apart₁ {y} {p′} (a-mono a pp q<p) ny zs))
  ...       | yes yp with a-refl a pp yp
  ...         | [] , e = ⊥-elim (≺-irrefl {q} (subst (q ≺_) (trans e (⊕-identityʳ q)) q<p))
  ...         | (l ∷ σ) , e with joins pp s e
  ...           | _ , refl , e′ , _ , L′ , car′ , h with car-fun car car′
  ...             | refl = ⊥-elim (≺-absurd {p′} {y ⊕ zs} pL
                     (≺-≼-≺ {y ⊕ zs} {(y ⊕ zs) ⊕ [ sub e′ ]} {p′} (≺-ext (y ⊕ zs) {sub e′} []) (⊑-≼ {(y ⊕ zs) ⊕ [ sub e′ ]} {p′} h)))

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
  amb-mr a (mrow {k} s _ pk _ _ refl _) =
    ≺-irrefl {p} (subst (p ≺_) (fresh₁ a (below-join (hS s) pk)) (≺-trans {p} {k} {k ⊕ [ sub p ]} pk (≺-ext k {sub p} [])))
  amb-mr a (mlate _ _ refl _) = ≺-irrefl {p} (subst (p ≺_) (fresh₁ a below-last) (≺-ext p {last} []))

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
