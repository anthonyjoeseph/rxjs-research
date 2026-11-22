{-# OPTIONS --guardedness #-}

-- A READING COMPLETED BY A MARK HOLDS WHAT THE READING HOLDS.  Where the
-- reading ends at `c`, the concat hands its place on silently at
-- `c ⊕ [ ix 0 ]`, then shows the mark at `c ⊕ [ ix 1 ] ⊕ [ ix 0 ]` and
-- ends at `c ⊕ [ ix 1 ] ⊕ [ last ]`.  The mark counts nothing, so every
-- count the closed stream reaches the reading reached at its end.
module simultaneous.HeldClose where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Properties using (++-assoc; ++-identityʳ; ∷-injective)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)

open import Tree using (mergeᶠ)
open import Data.Nat using (ℕ; zero; suc; _≟_; s≤s; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (decidable-stable; _⊎-dec_)

open import denotation.Position using (Pos; root; _≟ᵖ_; ix; last; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; pin; end; Few; Seen; Den; enter; Reach; Ended; at-out; on-out; at-end; _≺_; _≼_; module Op; module Bounded)
open import denotation.Read using (Run; []; _∷_; Visible; After; Least; cursor)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≺-absurd; ≼-refl; ≺→≼; ≼-antisym; ≼-or-≻; ≼-split; ≺-ext; ≺-≼-≺; ≼-trans)
open import denotation.Laws.Worlds using (⊕-assoc; ⊕-injˡ)
open import denotation.Laws.Worlds.Leaves using (of-reach)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.InstEmit using (instEmit; mark; completed; begin; value)
open import simultaneous.Relations using (Met)
open import simultaneous.Readings using (rootOf)
open import simultaneous.Routed using (Held; Idle; Rest; Ex; cnt; nameOf; r-completed; c-end)
open import simultaneous.Shut using (Shut)
open import simultaneous.HeldConnect using (rootOf-ext; early-inst; same-refl; rows-refl)
open import simultaneous.HeldTake using (++-split′; ex-ext; name-ext; under-of; past-end)
open import simultaneous.HeldComb using (from-++)
open import simultaneous.HeldHot using (em)
open import simultaneous.HeldTrigger using (≺-part; start-0; module Two)
open import simultaneous.CombSent using (of-two)
open import simultaneous.Relabel using (held-same)
open import simultaneous.Layers using (after-≺; run-tail; cursor-snoc)
open import simultaneous.Project using (run-prefix)
open import simultaneous.TakeKit using (ix<last)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

-- Where a run stands, past a row in its middle.
cur-mid : ∀ {X : Set} c (xs : List (Pos × Ev X)) {q e} ys → cursor c (xs ++ (q , e) ∷ ys) ≡ cursor (just q) ys
cur-mid c []             ys = refl
cur-mid c ((q′ , _) ∷ xs) ys = cur-mid (just q′) xs ys

-- Two lists split one list where each ends.
split₂ : ∀ {B : Set} (xs ys r₁ : List B) {r₂} → xs ++ ys ≡ r₁ ++ r₂
       → (Σ (List B) λ m → r₁ ≡ xs ++ m × ys ≡ m ++ r₂) ⊎ (Σ (List B) λ m → xs ≡ r₁ ++ m × r₂ ≡ m ++ ys)
split₂ []       ys r₁       eq   = inj₁ (r₁ , refl , eq)
split₂ (x ∷ xs) ys []       refl = inj₂ (x ∷ xs , refl , refl)
split₂ (x ∷ xs) ys (w ∷ r₁) eq with ∷-injective eq
... | refl , eq′ with split₂ xs ys r₁ eq′
...   | inj₁ (m , e₁ , e₂) = inj₁ (m , cong (x ∷_) e₁ , e₂)
...   | inj₂ (m , e₁ , e₂) = inj₂ (m , cong (x ∷_) e₁ , e₂)

end? : ∀ {X : Set} (e : Ev X) → e ≡ end ⊎ (e ≡ end → ⊥)
end? (out _) = inj₂ λ ()
end? skip    = inj₂ λ ()
end? (pin _) = inj₂ λ ()
end? end     = inj₁ refl

-- A one-value `of`: its value, then its end.
of-row₁ : ∀ {X : Set} (x : X) {s y e} → enter (Op.of (x ∷ [])) s y e → (y ≡ s ⊕ [ ix 0 ] × e ≡ out x) ⊎ (y ≡ s ⊕ [ last ] × e ≡ end)
of-row₁ x (at-out , _)        = inj₁ (refl , refl)
of-row₁ x (on-out at-end , _) = inj₂ (refl , refl)

of-val₁ : ∀ {X : Set} (x : X) s → enter (Op.of (x ∷ [])) s (s ⊕ [ ix 0 ]) (out x)
of-val₁ x s = at-out , of-reach s 0 (x ∷ []) {s ⊕ [ ix 0 ]} {out x}

of-end₁ : ∀ {X : Set} (x : X) s → enter (Op.of (x ∷ [])) s (s ⊕ [ last ]) end
of-end₁ x s = on-out at-end , of-reach s 0 (x ∷ []) {s ⊕ [ last ]} {end}

-- A READING CLOSED BY ONE VALUE: its rows but its end, then where it ends,
-- the hand-off, the value and the end.
module CloseRuns {B : Set} (R : EmissionSet B) (mk₀ : B)
             (proper : ∀ {q e c} → R q e → R c end → q ≼ c)
             (func   : ∀ {q e e′} → R q e → R q e′ → e ≡ e′)
             (r-few  : ∀ {q e} → R q e → Few R q) where

  hpos mpos fpos : Pos → Pos
  hpos c = c ⊕ [ ix 0 ]
  mpos c = (c ⊕ [ ix 1 ]) ⊕ [ ix 0 ]
  fpos c = (c ⊕ [ ix 1 ]) ⊕ [ last ]

  -- The reading's rows but its end; where it ends, the hand-off, the mark
  -- and the end.
  data U : EmissionSet B where
    src : ∀ {q e} → R q e → (e ≡ end → ⊥) → U q e
    hnd : ∀ {c} → R c end → U (hpos c) skip
    mk  : ∀ {c} → R c end → U (mpos c) (out mk₀)
    fin : ∀ {c} → R c end → U (fpos c) end

  ----------------------------------------------------------------------
  -- Order

  c≺h : ∀ c → c ≺ hpos c
  c≺h c = ≺-ext c []

  h≺m : ∀ c → hpos c ≺ mpos c
  h≺m c = subst (hpos c ≺_) (sym (⊕-assoc c [ ix 1 ] [ ix 0 ])) (≺-part c [] [ ix 0 ] refl)

  m≺f : ∀ c → mpos c ≺ fpos c
  m≺f c = ix<last (c ⊕ [ ix 1 ])

  c≺m : ∀ c → c ≺ mpos c
  c≺m c = ≺-trans {c} {hpos c} {mpos c} (c≺h c) (h≺m c)

  f≺L : ∀ c → fpos c ≺ (c ⊕ [ last ])
  f≺L c = subst (_≺ (c ⊕ [ last ])) (sym (⊕-assoc c [ ix 1 ] [ last ])) (≺-part c [ last ] [] refl)

  c≺f : ∀ c → c ≺ fpos c
  c≺f c = ≺-trans {c} {mpos c} {fpos c} (c≺m c) (m≺f c)

  m≼L : ∀ c → mpos c ≼ (c ⊕ [ last ])
  m≼L c = ≺→≼ {mpos c} {c ⊕ [ last ]} (≺-trans {mpos c} {fpos c} {c ⊕ [ last ]} (m≺f c) (f≺L c))

  uniq : ∀ {c c′} → R c end → R c′ end → c ≡ c′
  uniq y y′ = ≼-antisym (proper y y′) (proper y′ y)

  -- A row of the reading but its end lies before its end.
  before : ∀ {q e} → R q e → (e ≡ end → ⊥) → ∀ {c} → R c end → q ≺ c
  before {q} y ne {c} yc with ≼-split {q} {c} (proper y yc)
  ... | inj₁ lt   = lt
  ... | inj₂ refl = ⊥-elim (ne (func y yc))

  end≼ : ∀ {c c′} → R c end → R c′ end → c ≼ c′
  end≼ {c} y y′ = subst (c ≼_) (uniq y y′) (≼-refl {c})

  root-h : ∀ c → rootOf (hpos c) ≡ rootOf c
  root-h c = rootOf-ext c [ ix 0 ]

  root-m : ∀ c → rootOf (mpos c) ≡ rootOf c
  root-m c = trans (rootOf-ext (c ⊕ [ ix 1 ]) [ ix 0 ]) (rootOf-ext c [ ix 1 ])

  root-f : ∀ c → rootOf (fpos c) ≡ rootOf c
  root-f c = trans (rootOf-ext (c ⊕ [ ix 1 ]) [ last ]) (rootOf-ext c [ ix 1 ])

  ----------------------------------------------------------------------
  -- Few

  few-RU : ∀ {q} → (∀ {c} → R c end → q ≺ c) → Few R q → Few U q
  few-RU {q} qc (ks , h) = ks , pick
    where
      pick : ∀ {k e} → U k e → k ≺ q → k ∈ ks
      pick (src y _)   lt = h y lt
      pick (hnd {c} y) lt = ⊥-elim (≺-absurd {q} {hpos c} (≺-trans {q} {c} {hpos c} (qc y) (c≺h c)) lt)
      pick (mk {c} y)  lt = ⊥-elim (≺-absurd {q} {mpos c} (≺-trans {q} {c} {mpos c} (qc y) (c≺m c)) lt)
      pick (fin {c} y) lt =
        ⊥-elim (≺-absurd {q} {fpos c} (≺-trans {q} {c} {fpos c} (qc y) (≺-trans {c} {mpos c} {fpos c} (c≺m c) (m≺f c))) lt)

  few-UR : ∀ {w} → (∀ {c} → R c end → w ≼ c) → Few U w → Few R w
  few-UR {w} wc (ks , h) = ks , pick
    where
      pick : ∀ {k e} → R k e → k ≺ w → k ∈ ks
      pick {e = e} y lt with end? e
      ... | inj₁ refl = ⊥-elim (wc y lt)
      ... | inj₂ ne   = h (src y ne) lt

  -- Before the end, through a position past it.
  few-end-UR : ∀ {cb} → R cb end → ∀ {w} → cb ≺ w → Few U w → Few R cb
  few-end-UR {cb} yc {w} cw (ks , h) = ks , pick
    where
      pick : ∀ {k e} → R k e → k ≺ cb → k ∈ ks
      pick {k} {e} y lt with end? e
      ... | inj₁ refl = ⊥-elim (≺-irrefl {k} (subst (k ≺_) (sym (uniq y yc)) lt))
      ... | inj₂ ne   = h (src y ne) (≺-trans {k} {cb} {w} lt cw)

  -- Up to the closing end, the reading's rows and the closing ones.
  few-end : ∀ {c} → R c end → ∀ {w} → w ≼ fpos c → Few U w
  few-end {c} yc {w} wf = mpos c ∷ hpos c ∷ proj₁ (r-few yc) , pick
    where
      pick : ∀ {k e} → U k e → k ≺ w → k ∈ (mpos c ∷ hpos c ∷ proj₁ (r-few yc))
      pick (src y ne) _ = there (there (proj₂ (r-few yc) y (before y ne yc)))
      pick (hnd y) _ with uniq y yc
      ... | refl = there (here refl)
      pick (mk y) _ with uniq y yc
      ... | refl = here refl
      pick (fin y) lt with uniq y yc
      ... | refl = ⊥-elim (wf lt)

  few-U : ∀ {k e} → U k e → Few U k
  few-U (src y ne)  = few-RU (before y ne) (r-few y)
  few-U (hnd {c} y) = few-end y (≺→≼ {hpos c} {fpos c} (≺-trans {hpos c} {mpos c} {fpos c} (h≺m c) (m≺f c)))
  few-U (mk {c} y)  = few-end y (≺→≼ {mpos c} {fpos c} (m≺f c))
  few-U (fin {c} y) = few-end y (≼-refl {fpos c})

  ----------------------------------------------------------------------
  -- Runs

  -- A cursor before every end.
  Pre : Maybe Pos → Set
  Pre c = ∀ {c′} → R c′ end → After c c′

  step-src : ∀ {c q e} → R q e → (e ≡ end → ⊥) → Seen U q e × Visible e × Least U c q → Seen R q e × Visible e × Least R c q
  step-src {c} y ne ((_ , fw) , vi , a , l) = ((y , proper y) , few-UR (proper y) fw) , vi , a , least
    where
      least : ∀ {k e′} → R k e′ → Visible e′ → After c k → _ ≼ k
      least {e′ = e′} y′ v ak with end? e′
      ... | inj₁ refl = proper y y′
      ... | inj₂ ne′  = l (src y′ ne′) v ak

  step-mk : ∀ {c cb} → Pre c → R cb end → Seen U (mpos cb) (out mk₀) × Visible (out mk₀) × Least U c (mpos cb)
          → Seen R cb end × Visible (end {B}) × Least R c cb
  step-mk {c} {cb} pc yc ((_ , fw) , _ , _ , l) = ((yc , end≼ yc) , few-end-UR yc (c≺m cb) fw) , tt , pc yc , least
    where
      least : ∀ {k e′} → R k e′ → Visible e′ → After c k → cb ≼ k
      least {k} {e′} y′ v ak with end? e′
      ... | inj₁ refl = end≼ yc y′
      ... | inj₂ ne′  = λ kc → l (src y′ ne′) v ak (≺-trans {k} {cb} {mpos cb} kc (c≺m cb))

  data Tail (cb : Pos) : List (Pos × Ev B) → Set where
    t-none : Tail cb []
    t-fin  : Tail cb [ (fpos cb , end) ]

  -- A run met of the closed stream: one of the reading's, or the
  -- reading's up to its end, then the mark, then perhaps the end.
  data Shape (c : Maybe Pos) : List (Pos × Ev B) → Set where
    open′ : ∀ {rs} → Run R c rs → Pre (cursor c rs) → Shape c rs
    shut  : ∀ {cb r t} → Run R c (r ++ [ (cb , end) ]) → R cb end → Tail cb t → Shape c (r ++ (mpos cb , out mk₀) ∷ t)

  tail : ∀ {cb t} → R cb end → Run U (just (mpos cb)) t → Tail cb t
  tail yc []                                   = t-none
  tail {cb} yc ((((u , _) , _) , _ , a , _) ∷ run) = go u a run
    where
      go : ∀ {q e rs} → U q e → mpos cb ≺ q → Run U (just q) rs → Tail cb ((q , e) ∷ rs)
      go (src {q} y ne) a _ = ⊥-elim (≺-absurd {mpos cb} {q} a (≺-trans {q} {cb} {mpos cb} (before y ne yc) (c≺m cb)))
      go (hnd y) a _ with uniq y yc
      ... | refl = ⊥-elim (≺-absurd {mpos cb} {hpos cb} a (h≺m cb))
      go (mk y) a _ with uniq y yc
      ... | refl = ⊥-elim (≺-irrefl {mpos cb} a)
      go (fin y) a run with uniq y yc
      ... | refl with past-end (fin y) run
      ...   | refl = t-fin

  shape : ∀ {c rs} → Pre c → Run U c rs → Shape c rs
  shape pc [] = open′ [] pc
  shape {c} pc (((((src {q} {e} y ne , pr) , fw) , vi , ls)) ∷ run) with shape (before y ne) run
  ... | open′ r p′  = open′ (step-src {c} y ne (((src y ne , pr) , fw) , vi , ls) ∷ r) p′
  ... | shut {r = r′} r yc t = shut {r = (q , e) ∷ r′} (step-src {c} y ne (((src y ne , pr) , fw) , vi , ls) ∷ r) yc t
  shape pc ((((hnd y , _) , _) , () , _) ∷ _)
  shape {c} pc (((((mk y , pr) , fw) , vi , ls)) ∷ run) = shut {r = []} (step-mk {c} pc y (((mk y , pr) , fw) , vi , ls) ∷ []) y (tail y run)
  shape {c} pc ((((fin {c′} y , _) , _) , _ , _ , l) ∷ _) = ⊥-elim (l (mk y) tt (after-≺ c (pc y) (c≺m c′)) (m≺f c′))

  shape₀ : ∀ {rs} → Met U rs → Shape nothing rs
  shape₀ = shape (λ _ → tt)

  in-tail : ∀ {cb} m {z r₂} → Tail cb (m ++ z ∷ r₂) → m ≡ [] × z ≡ (fpos cb , end) × r₂ ≡ []
  in-tail []          t-fin = refl , refl , refl
  in-tail (_ ∷ [])    ()
  in-tail (_ ∷ _ ∷ _) ()

  no-out : ∀ {cb t y x} → Tail cb t → (y , out x) ∈ t → ⊥
  no-out t-none ()
  no-out t-fin (here ())
  no-out t-fin (there ())

  past-mk : ∀ {cb t y} r → Tail cb t → After (cursor nothing (r ++ (mpos cb , out mk₀) ∷ t)) y → mpos cb ≺ y
  past-mk {y = y} r t-none a     = subst (λ c → After c y) (cur-mid nothing r []) a
  past-mk {cb} {y = y} r t-fin a = ≺-trans {mpos cb} {fpos cb} {y} (m≺f cb) (subst (λ c → After c y) (cur-mid nothing r _) a)

-- Closed by a completion mark.
module Close {A : Set} (R : EmissionSet (IE A)) (n₀ : Pos)
             (proper : ∀ {q e c} → R q e → R c end → q ≼ c)
             (func   : ∀ {q e e′} → R q e → R q e′ → e ≡ e′)
             (r-few  : ∀ {q e} → R q e → Few R q) where

  mk₀ : IE A
  mk₀ = instEmit (mark completed) n₀

  open CloseRuns R mk₀ proper func r-few public

  cnt-mk : ∀ r q → cnt (r ++ [ (q , out mk₀) ]) ≡ cnt r
  cnt-mk r q = from-++ _ r [ (q , out mk₀) ]

  ----------------------------------------------------------------------
  -- The closed stream holds

  module Holds {cs} (H : Held R cs) where

    nm-m : ∀ c → nameOf (mpos c) ≡ nameOf c
    nm-m c = trans (name-ext (c ⊕ [ ix 1 ]) [ ix 0 ]) (name-ext c [ ix 1 ])

    nm-f : ∀ c → nameOf (fpos c) ≡ nameOf c
    nm-f c = trans (name-ext (c ⊕ [ ix 1 ]) [ last ]) (name-ext c [ ix 1 ])

    nx-at : ∀ {c} zs → ¬ Ex cs (c ⊕ zs) → ¬ Ex cs c
    nx-at zs nx ex = nx (ex-ext zs ex)

    -- The end's count, unless its burst is exempt.
    at-close : ∀ {r cb} → Run R nothing (r ++ [ (cb , end) ]) → ¬ Ex cs cb → Σ ℕ λ k → cnt r ≡ (nameOf cb , suc k)
    at-close {r} run nx = Held.covered H run r [] refl c-end nx

    covered : ∀ {rs} → Met U rs → ∀ r₁ {y e} r₂ → rs ≡ r₁ ++ (y , e) ∷ r₂ → _ → ¬ Ex cs y → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
    covered m = cov (shape₀ m)
      where
        cov : ∀ {rs} → Shape nothing rs → ∀ r₁ {y e} r₂ → rs ≡ r₁ ++ (y , e) ∷ r₂ → _ → ¬ Ex cs y
            → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
        cov (open′ run _) r₁ r₂ eq ce nx = Held.covered H run r₁ r₂ eq ce nx
        cov (shut {cb} {r} {t} run yc tl) r₁ {y} {e} r₂ eq ce nx with ++-split′ r ((mpos cb , out mk₀) ∷ t) r₁ (y , e) r₂ eq
        ... | inj₂ (m , refl , refl) = Held.covered H run r₁ (m ++ [ (cb , end) ]) (++-assoc r₁ ((y , e) ∷ m) [ (cb , end) ]) ce nx
        ... | inj₁ ([] , refl , refl) with at-close run (nx-at (ix 1 ∷ ix 0 ∷ []) (subst (λ z → ¬ Ex cs z) (⊕-assoc cb [ ix 1 ] [ ix 0 ]) nx))
        ...   | k , h = k , trans (cong cnt (++-identityʳ r)) (trans h (cong (λ n → n , suc k) (sym (nm-m cb))))
        cov (shut {cb} {r} {t} run yc tl) r₁ {y} {e} r₂ eq ce nx | inj₁ (_ ∷ m , refl , refl) with in-tail m tl
        ... | refl , refl , refl with at-close run (nx-at (ix 1 ∷ last ∷ []) (subst (λ z → ¬ Ex cs z) (⊕-assoc cb [ ix 1 ] [ last ]) nx))
        ...   | k , h = k , trans (cnt-mk r (mpos cb)) (trans h (cong (λ n → n , suc k) (sym (nm-f cb))))

    exact : ∀ {rs} → Met U rs → ∀ r₁ {y n} r₂ → rs ≡ r₁ ++ (y , out (instEmit (mark _) n)) ∷ r₂ → Σ ℕ λ k → proj₂ (cnt r₁) ≡ suc k
    exact m = ext (shape₀ m)
      where
        ext : ∀ {rs} → Shape nothing rs → ∀ r₁ {y n} r₂ → rs ≡ r₁ ++ (y , out (instEmit (mark _) n)) ∷ r₂ → Σ ℕ λ k → proj₂ (cnt r₁) ≡ suc k
        ext (open′ run _) r₁ r₂ eq = Held.exact H run r₁ r₂ eq
        ext (shut {cb} {r} {t} run yc tl) r₁ {y} {n} r₂ eq with ++-split′ r ((mpos cb , out mk₀) ∷ t) r₁ _ r₂ eq
        ... | inj₂ (m , refl , refl) = Held.exact H run r₁ (m ++ [ (cb , end) ]) (++-assoc r₁ (_ ∷ m) [ (cb , end) ])
        ... | inj₁ ([] , refl , ())
        ... | inj₁ (_ ∷ m , refl , refl) with in-tail m tl
        ...   | refl , () , _

    shut′ : Shut U
    shut′ m = sht (shape₀ m)
      where
        sht : ∀ {rs} → Shape nothing rs → ∀ r₁ r₂ → rs ≡ r₁ ++ r₂ → proj₂ (cnt r₁) ≡ 0
            → ∀ {q} → (q , out (instEmit (mark begin) (proj₁ (cnt r₁)))) ∈ r₁
            → ∀ {y a j} → (y , out (instEmit (value a) j)) ∈ r₂ → rootOf y ≡ rootOf q → ⊥
        sht (open′ run _) r₁ r₂ eq z bq vy rt = Held.shut H run r₁ r₂ eq z bq vy rt
        sht (shut {cb} {r} {t} run yc tl) r₁ r₂ eq z bq vy rt with split₂ r ((mpos cb , out mk₀) ∷ t) r₁ eq
        ... | inj₁ (m , refl , e₂) = gone (subst (_ ∈_) (sym e₂) (∈-++⁺ʳ m vy))
          where
            gone : ∀ {y a j} → (y , out (instEmit (value a) j)) ∈ (mpos cb , out mk₀) ∷ t → ⊥
            gone (here ())
            gone (there x) = no-out tl x
        ... | inj₂ (m , refl , refl) with ∈-++⁻ m vy
        ...   | inj₁ x = Held.shut H run r₁ (m ++ [ (cb , end) ]) (++-assoc r₁ m [ (cb , end) ]) z bq (∈-++⁺ˡ x) rt
        ...   | inj₂ (here ())
        ...   | inj₂ (there x) = no-out tl x

    Goal : List (Pos × Ev (IE A)) → Pos → Set
    Goal rs w = proj₂ (cnt rs) ≡ 0 ⊎ proj₁ (cnt rs) ≡ nameOf w

    idle : Idle U
    idle m ne {w} F aw lw = idl (shape₀ m) ne aw lw
      where
        idl : ∀ {rs} → Shape nothing rs → (∀ {c} → (c , end) ∈ rs → ⊥) → After (cursor nothing rs) w
            → (∀ {y e} → U y e → Visible e → After (cursor nothing rs) y → w ≼ y) → Goal rs w
        idl {rs} (open′ run pr) ne aw lw =
          decidable-stable ((proj₂ (cnt rs) ≟ 0) ⊎-dec (proj₁ (cnt rs) ≟ᵖ nameOf w)) λ ng → em {Σ Pos λ c → R c end} λ
            { (inj₂ none) → ng (Held.idle H run ne (few-UR (λ y → ⊥-elim (none (_ , y))) F) aw (lw-none none))
            ; (inj₁ (cb , yc)) → ng (ended cb yc (≼-or-≻ w cb)) }
          where
            lw-none : ¬ Σ Pos (λ c → R c end) → ∀ {y e} → R y e → Visible e → After (cursor nothing rs) y → w ≼ y
            lw-none none {e = e} y v a with end? e
            ... | inj₁ refl = ⊥-elim (none (_ , y))
            ... | inj₂ ne′  = lw (src y ne′) v a

            ended : ∀ cb → R cb end → w ≼ cb ⊎ cb ≺ w → Goal rs w
            ended cb yc (inj₁ wc) = Held.idle H run ne (few-UR (λ y → subst (w ≼_) (uniq yc y) wc) F) aw lw-at
              where
                lw-at : ∀ {y e} → R y e → Visible e → After (cursor nothing rs) y → w ≼ y
                lw-at {e = e} y v a with end? e
                ... | inj₁ refl = subst (w ≼_) (uniq yc y) wc
                ... | inj₂ ne′  = lw (src y ne′) v a
            ended cb yc (inj₂ cw) with Held.idle H run ne (few-end-UR yc cw F) (pr yc) lw-cb
              where
                lw-cb : ∀ {y e} → R y e → Visible e → After (cursor nothing rs) y → cb ≼ y
                lw-cb {y} {e} y′ v a with end? e
                ... | inj₁ refl = end≼ yc y′
                ... | inj₂ ne′  = ≺→≼ {cb} {y} (≺-≼-≺ {cb} {w} {y} cw (lw (src y′ ne′) v a))
            ... | inj₁ z  = inj₁ z
            ... | inj₂ nq = inj₂ (trans nq (sym (under-of {cb} {w} cw
                                    (≼-trans {w} {mpos cb} {cb ⊕ [ last ]} (lw (mk yc) tt (after-≺ (cursor nothing rs) (pr yc) (c≺m cb))) (m≼L cb)))))
        idl (shut {cb} {r} {t} run yc tl) ne aw lw with tl
        ... | t-fin = ⊥-elim (ne (∈-++⁺ʳ r (there (here refl))))
        ... | t-none with run-tail r run
        ...   | ((_ , fcb) , _ , acb , lcb) ∷ [] with Held.idle H (run-prefix r run) (λ x → ne (∈-++⁺ˡ x)) fcb acb lcb
        ...     | inj₁ z  = inj₁ (trans (cong proj₂ (cnt-mk r (mpos cb))) z)
        ...     | inj₂ nq = inj₂ (trans (cong proj₁ (cnt-mk r (mpos cb))) (trans nq (sym (under-of {cb} {w} cw wL))))
          where
            aw′ : mpos cb ≺ w
            aw′ = subst (λ c → After c w) (cursor-snoc nothing r) aw

            cw : cb ≺ w
            cw = ≺-trans {cb} {mpos cb} {w} (c≺m cb) aw′

            wL : w ≼ (cb ⊕ [ last ])
            wL = ≼-trans {w} {fpos cb} {cb ⊕ [ last ]}
                   (lw (fin yc) tt (subst (λ c → After c (fpos cb)) (sym (cursor-snoc nothing r)) (m≺f cb)))
                   (≺→≼ {fpos cb} {cb ⊕ [ last ]} (f≺L cb))

    rest : Rest U
    rest m z bq = rst (shape₀ m) z bq
      where
        rst : ∀ {rs} → Shape nothing rs → proj₂ (cnt rs) ≡ 0 → ∀ {q} → (q , out (instEmit (mark begin) (proj₁ (cnt rs)))) ∈ rs
            → Σ (List Pos) λ ks → ∀ {y e} → U y e → After (cursor nothing rs) y → rootOf y ≡ rootOf q → y ∈ ks
        rst {rs} (open′ run pr) z {q} bq with Held.rest H run z bq
        ... | ks , h = ks ++ L.map hpos ks ++ L.map mpos ks ++ L.map fpos ks , pick
          where
            at : ∀ {c} → R c end → ∀ y → rootOf y ≡ rootOf c → rootOf y ≡ rootOf q → c ∈ ks
            at {c} yc y yr rt = h yc (pr yc) (trans (sym yr) rt)

            pick : ∀ {y e} → U y e → After (cursor nothing rs) y → rootOf y ≡ rootOf q → y ∈ _
            pick (src y _) a rt = ∈-++⁺ˡ (h y a rt)
            pick (hnd {c} y) _ rt = ∈-++⁺ʳ ks (∈-++⁺ˡ (∈-map⁺ hpos (at y (hpos c) (root-h c) rt)))
            pick (mk {c} y) _ rt = ∈-++⁺ʳ ks (∈-++⁺ʳ (L.map hpos ks) (∈-++⁺ˡ (∈-map⁺ mpos (at y (mpos c) (root-m c) rt))))
            pick (fin {c} y) _ rt =
              ∈-++⁺ʳ ks (∈-++⁺ʳ (L.map hpos ks) (∈-++⁺ʳ (L.map mpos ks) (∈-map⁺ fpos (at y (fpos c) (root-f c) rt))))
        rst (shut {cb} {r} {t} run yc tl) z bq = fpos cb ∷ [] , pick
          where
            past-m : ∀ {y} → After (cursor nothing (r ++ (mpos cb , out mk₀) ∷ t)) y → mpos cb ≺ y
            past-m = past-mk r tl

            pick : ∀ {y e} → U y e → After (cursor nothing (r ++ (mpos cb , out mk₀) ∷ t)) y → _ → y ∈ (fpos cb ∷ [])
            pick (src {y} y′ ne) a _ = ⊥-elim (≺-absurd {mpos cb} {y} (past-m a) (≺-trans {y} {cb} {mpos cb} (before y′ ne yc) (c≺m cb)))
            pick (hnd y) a _ with uniq y yc
            ... | refl = ⊥-elim (≺-absurd {mpos cb} {hpos cb} (past-m a) (h≺m cb))
            pick (mk y) a _ with uniq y yc
            ... | refl = ⊥-elim (≺-irrefl {mpos cb} (past-m a))
            pick (fin y) _ _ with uniq y yc
            ... | refl = here refl

    held : Held U cs
    held = record
      { named   = λ { (src y _) → Held.named H y }
      ; covered = covered
      ; exact   = exact
      ; routing = λ { (src y _) → Held.routing H y ; (mk _) → r-completed }
      ; shut    = shut′
      ; early   = λ { (src y _) → Held.early H y }
      ; ends    = λ { (src y ne) → ⊥-elim (ne refl) ; (fin {c} y) → early-inst [ last ] (early-inst [ ix 1 ] (Held.ends H y)) }
      ; done    = λ { (src y _) → Held.done H y ; (mk {c} y) → early-inst [ ix 0 ] (early-inst [ ix 1 ] (Held.ends H y)) }
      ; late    = λ { (src y _) → Held.late H y }
      ; idle    = idle
      ; rest    = rest
      }

------------------------------------------------------------------------
-- The concat

-- THE CLOSING CONCAT IS THE CLOSED STREAM: a concat of a reading whose
-- rows all lie past the outer's end, then a lane showing one mark.  The
-- outer's rows are silent, and each other row is one of the closed
-- stream's, where it is.
module CatRuns {B : Set} (G : Bool → Den B) (P : Pos) (mk₀ : B)
                (proper : ∀ {q e c} → enter (G true) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) q e → enter (G true) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) c end → q ≼ c)
                (func   : ∀ {q e e′} → enter (G true) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) q e → enter (G true) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) q e′ → e ≡ e′)
                (r-few  : ∀ {q e} → enter (G true) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) q e → Few (enter (G true) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ])) q)
                (r-late : ∀ {k e} → enter (G true) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) k e → (P ⊕ [ last ]) ≺ k)
                (r-nopin : ∀ {k r} → enter (G true) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) k (pin r) → ⊥)
                (of-row : ∀ {s y e} → enter (G false) s y e
                        → (y ≡ s ⊕ [ ix 0 ] × e ≡ out mk₀) ⊎ (y ≡ s ⊕ [ last ] × e ≡ end))
                (of-val : ∀ s → enter (G false) s (s ⊕ [ ix 0 ]) (out mk₀))
                (of-end : ∀ s → enter (G false) s (s ⊕ [ last ]) end) where


  sb : Pos
  sb = (P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]

  R : EmissionSet B
  R = enter (G true) sb

  open CloseRuns R mk₀ proper func r-few public
  open Two P
  module Bd = Bounded 1 G O

  C : EmissionSet B
  C = enter (Op.flatMap (mergeᶠ (just 1)) G (Op.of (true ∷ false ∷ []))) P

  In : Pos → EmissionSet B
  In c = enter (G false) (c ⊕ [ ix 1 ])

  sb≺e₁ : sb ≺ e₁
  sb≺e₁ = subst (_≺ e₁) (sym (⊕-assoc P [ ix 0 ] [ ix 1 ])) (≺-part P [ ix 1 ] [] refl)

  q₁≺e₁ : q₁ ≺ e₁
  q₁≺e₁ = ≺-part P [] [] refl

  r-after : ∀ {k e} → R k e → sb ≺ k
  r-after {k} y = ≺-trans {sb} {e₁} {k} sb≺e₁ (r-late y)

  q₁≺ : ∀ {k e} → R k e → q₁ ≺ k
  q₁≺ {k} y = ≺-trans {q₁} {e₁} {k} q₁≺e₁ (r-late y)

  in-after : ∀ {s y e} → enter (G false) s y e → s ≺ y
  in-after {s} x with of-row x
  ... | inj₁ (refl , _) = ≺-ext s []
  ... | inj₂ (refl , _) = ≺-ext s []

  -- The second lane starts where the first ends.

  ends-0 : ∀ {c} → Bd.Ends 0 [] c → R c end
  ends-0 (_ , _ , _ , N , St , (x , _)) with nth-0 N | start-0 St
  ... | refl , refl | refl = x

  start-1 : ∀ {s} → Bd.Starts 1 q₁ (Bd.Sched 1) s → Σ Pos λ c → R c end × s ≡ c ⊕ [ ix 1 ]
  start-1 (Bd.room (s≤s ()))
  start-1 (Bd.freed _ (inj₁ (c , E , lt))) = ⊥-elim (≺-absurd {q₁} {c} (q₁≺ (ends-0 E)) lt)
  start-1 (Bd.freed _ (inj₂ ()))
  start-1 (Bd.queued _ _ (inj₁ (c , E , refl)) _ _) = c , ends-0 E , refl
  start-1 (Bd.queued _ _ (inj₂ ()) _ _)

  lane-of : ∀ {q a k e} → Bd.Lane q a k e
          → (q ≡ q₀ × a ≡ true × R k e) ⊎ (q ≡ q₁ × a ≡ false × Σ Pos λ c → R c end × In c k e)
  lane-of (zero , _ , (N , St) , (x , _)) with nth-0 N | start-0 St
  ... | refl , refl | refl = inj₁ (refl , refl , x)
  lane-of (suc zero , _ , (N , St) , (x , _)) with nth-1 N
  ... | refl , refl with start-1 St
  ...   | c , yc , refl = inj₂ (refl , refl , c , yc , x)
  lane-of (suc (suc _) , _ , (N , _) , _) = ⊥-elim (nth-2 N)

  E₀ : ∀ {c} → R c end → Bd.Ends 0 [] c
  E₀ yc = q₀ , true , sb , nth₀ , Bd.room (s≤s z≤n) , (yc , r-after yc)

  st₁ : ∀ {c} → R c end → Bd.Starts 1 q₁ (Bd.Sched 1) (c ⊕ [ ix 1 ])
  st₁ {c} yc = Bd.queued (s≤s z≤n) (q₁≺ yc) (inj₁ (c , E₀ yc , refl)) (inj₁ (c , E₀ yc , ≼-refl {c})) none
    where
      none : Bd.Kth (_≺ c) (Bd.Sched 1) 0 → ⊥
      none (inj₁ (c′ , E , lt)) = ≺-irrefl {c} (subst (_≺ c) (uniq (ends-0 E) yc) lt)
      none (inj₂ ())

  lane₀ : ∀ {k e} → R k e → Bd.Lane q₀ true k e
  lane₀ y = 0 , sb , (nth₀ , Bd.room (s≤s z≤n)) , (y , r-after y)

  lane₁ : ∀ {c k e} → R c end → In c k e → Bd.Lane q₁ false k e
  lane₁ yc x = 1 , _ , (nth₁ , st₁ yc) , (x , in-after x)

  queued : ∀ {c} → R c end → Bd.Queued c
  queued yc = 1 , q₁ , false , nth₁ , st₁ yc

  -- The second lane hands on to nothing.
  no-hand : ∀ {c} → R c end → Bd.Queued (fpos c) → ⊥
  no-hand {c} yc (zero , _ , _ , (N , St)) with nth-0 N
  ... | refl , refl = ≺-irrefl {q₀} (subst (q₀ ≺_) (⊕-injˡ (fpos c) q₀ (start-0 St)) (≺-trans {q₀} {c} {fpos c} (≺-trans {q₀} {e₁} {c} q₀e₁ (r-late yc)) (c≺f c)))
  no-hand {c} yc (suc zero , _ , _ , (N , St)) with nth-1 N
  ... | refl , refl with start-1 St
  ...   | c′ , yc′ , eq with uniq yc′ yc
  ...     | refl = ≺-irrefl {c} (subst (c ≺_) (⊕-injˡ (fpos c) c eq) (c≺f c))
  no-hand yc (suc (suc _) , _ , _ , (N , _)) = nth-2 N

  -- Where the second lane ends, so has everything.
  done : ∀ {c} → R c end → Bd.Done (fpos c)
  done {c} yc = (e₁ , oe , ≺→≼ {e₁} {fpos c} (≺-trans {e₁} {c} {fpos c} (r-late yc) (c≺f c))) , lanes
    where
      lanes : ∀ {q a} → O q (out a) → Bd.Indexed q → q ≺ fpos c → (⊥ → ⊥) → Ended (Bd.Lane q a) (fpos c)
      lanes x _ _ _ with of-two P x
      ... | inj₁ (refl , refl) = c , lane₀ yc , ≺→≼ {c} {fpos c} (c≺f c)
      ... | inj₂ (refl , refl) = fpos c , lane₁ yc (of-end _) , ≼-refl {fpos c}

  base : List Pos
  base = (q₀ ⊕ [ ix 0 ]) ∷ (q₁ ⊕ [ ix 0 ]) ∷ e₁ ∷ []

  -- EVERY ROW OF THE CONCAT is the outer's, or one of the closed stream's.
  classify : ∀ {k e′} → Bd.JoinT k e′ → k ∈ base ⊎ Σ (Ev B) λ e₀ → U k e₀
  classify (Bd.val x) with of-two P x
  ... | inj₁ (refl , _) = inj₁ (here refl)
  ... | inj₂ (refl , _) = inj₁ (there (here refl))
  classify (Bd.step x)  = ⊥-elim (o-skip x)
  classify (Bd.opin x)  = ⊥-elim (o-pin x)
  classify (Bd.oend x _) with o-end x
  ... | refl = inj₁ (there (there (here refl)))
  classify (Bd.opass x _) with o-end x
  ... | refl = inj₁ (there (there (here refl)))
  classify (Bd.lane _ _ L _ w) with lane-of L
  ... | inj₁ (_ , _ , y) = inj₂ (_ , src y λ { refl → w })
  ... | inj₂ (_ , _ , c , yc , x) with of-row x
  ...   | inj₁ (refl , refl) = inj₂ (_ , mk yc)
  ...   | inj₂ (refl , refl) = ⊥-elim w
  classify (Bd.lend _ _ L _ nh _) with lane-of L
  ... | inj₁ (_ , _ , y) = ⊥-elim (nh (queued y))
  ... | inj₂ (_ , _ , c , yc , x) with of-row x
  ...   | inj₂ (refl , _) = inj₂ (_ , fin yc)
  classify (Bd.lpass _ _ L _ nh _) with lane-of L
  ... | inj₁ (_ , _ , y) = ⊥-elim (nh (queued y))
  ... | inj₂ (_ , _ , c , yc , x) with of-row x
  ...   | inj₂ (refl , _) = inj₂ (_ , fin yc)
  classify (Bd.hand _ _ L _ h) with lane-of L
  ... | inj₁ (_ , _ , y) = inj₂ (_ , hnd y)
  ... | inj₂ (_ , _ , c , yc , x) with of-row x
  ...   | inj₂ (refl , _) = ⊥-elim (no-hand yc h)
  classify (Bd.left _ _ L _ _) with lane-of L
  ... | inj₁ (_ , _ , y) = ⊥-elim (r-nopin y)
  ... | inj₂ (_ , _ , c , yc , x) with of-row x
  ...   | inj₁ (_ , ())
  ...   | inj₂ (_ , ())
  classify (Bd.run () _)
  classify (Bd.rend () _ _)
  classify (Bd.rpass () _ _)
  classify (Bd.rhand () _)

  reach-U : ∀ {k e} → U k e → Reach Bd.JoinT k e
  reach-U u = base ++ proj₁ (few-U u) , λ j lt _ → cover j lt
    where
      cover : ∀ {k′ e′} → Bd.JoinT k′ e′ → _ → k′ ∈ (base ++ proj₁ (few-U u))
      cover j lt with classify j
      ... | inj₁ m        = ∈-++⁺ˡ m
      ... | inj₂ (_ , u′) = ∈-++⁺ʳ base (proj₂ (few-U u) u′ lt)

  -- The closed stream's rows are the concat's.
  lift : ∀ {k e} → U k e → C k e
  lift (src {e = out _} y ne) = Bd.lane o₀ (0 , true , nth₀) (lane₀ y) (λ ()) tt , reach-U (src y ne)
  lift (src {e = skip} y ne)  = Bd.lane o₀ (0 , true , nth₀) (lane₀ y) (λ ()) tt , reach-U (src y ne)
  lift (src {e = pin _} y _)  = ⊥-elim (r-nopin y)
  lift (src {e = end} _ ne)   = ⊥-elim (ne refl)
  lift (hnd y) = Bd.hand o₀ (0 , true , nth₀) (lane₀ y) (λ ()) (queued y) , reach-U (hnd y)
  lift (mk y)  = Bd.lane o₁ (1 , false , nth₁) (lane₁ y (of-val _)) (λ ()) tt , reach-U (mk y)
  lift (fin y) = Bd.lend o₁ (1 , false , nth₁) (lane₁ y (of-end _)) (λ ()) (no-hand y) (done y) , reach-U (fin y)

  -- And the concat's visible rows are the closed stream's.
  row : ∀ {y x} → C y (out x) → U y (out x)
  row (Bd.lane _ _ L _ _ , _) with lane-of L
  ... | inj₁ (_ , _ , y) = src y λ ()
  ... | inj₂ (_ , _ , c , yc , x) with of-row x
  ...   | inj₁ (refl , refl) = mk yc
  row (Bd.run () _ , _)

  end-row : ∀ {c} → C c end → U c end
  end-row (Bd.oend o (_ , lanes) , _) with o-end o
  ... | refl with lanes o₀ (0 , true , nth₀) q₀e₁ (λ ())
  ...   | _ , L , c₀e with lane-of L
  ...     | inj₁ (_ , _ , y) = ⊥-elim (c₀e (r-late y))
  ...     | inj₂ (eq , _) = ⊥-elim (≺-irrefl {q₀} (subst (q₀ ≺_) (sym eq) q₀q₁))
  end-row (Bd.lane _ _ _ _ () , _)
  end-row (Bd.lend _ _ L _ nh _ , _) with lane-of L
  ... | inj₁ (_ , _ , y) = ⊥-elim (nh (queued y))
  ... | inj₂ (_ , _ , c , yc , x) with of-row x
  ...   | inj₂ (refl , _) = fin yc
  end-row (Bd.run () _ , _)
  end-row (Bd.rend () _ _ , _)

  vis : ∀ {q e} → C q e → Visible e → U q e
  vis {e = out _} y _ = row y
  vis {e = end}   y _ = end-row y
  vis {e = skip}  _ ()
  vis {e = pin _} _ ()

  back : ∀ {c rs} → Run C c rs → Run U c rs
  back [] = []
  back ((((y , pr) , fw) , vi , ac , lf) ∷ run) =
    (((vis y vi , λ ce → pr (lift ce)) , (proj₁ fw , λ y′ lt → proj₂ fw (lift y′) lt)) , vi , ac , λ y′ v a → lf (lift y′) v a) ∷ back run

  -- The concat ends only past its mark's first effect.
  closes : ∀ {c} → C c end → Σ Pos λ f → C f (out mk₀) × (f ⊕ [ ix 0 ]) ≺ c
  closes y with end-row y
  ... | src _ ne = ⊥-elim (ne refl)
  ... | fin {c₀} yc = mpos c₀ , lift (mk yc) ,
          subst (_≺ fpos c₀) (sym (⊕-assoc (c₀ ⊕ [ ix 1 ]) [ ix 0 ] [ ix 0 ])) (≺-part (c₀ ⊕ [ ix 1 ]) [ ix 0 ] [] refl)

-- Closed by a completion mark.
module CatClose {A : Set} (G : Bool → Den (IE A)) (P n₀ : Pos)
                (proper : ∀ {q e c} → enter (G true) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) q e → enter (G true) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) c end → q ≼ c)
                (func   : ∀ {q e e′} → enter (G true) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) q e → enter (G true) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) q e′ → e ≡ e′)
                (r-few  : ∀ {q e} → enter (G true) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) q e → Few (enter (G true) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ])) q)
                (r-late : ∀ {k e} → enter (G true) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) k e → (P ⊕ [ last ]) ≺ k)
                (r-nopin : ∀ {k r} → enter (G true) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) k (pin r) → ⊥)
                (of-row : ∀ {s y e} → enter (G false) s y e
                        → (y ≡ s ⊕ [ ix 0 ] × e ≡ out (instEmit (mark completed) n₀)) ⊎ (y ≡ s ⊕ [ last ] × e ≡ end))
                (of-val : ∀ s → enter (G false) s (s ⊕ [ ix 0 ]) (out (instEmit (mark completed) n₀)))
                (of-end : ∀ s → enter (G false) s (s ⊕ [ last ]) end) where
  open CatRuns G P (instEmit (mark completed) n₀) proper func r-few r-late r-nopin of-row of-val of-end public
  open Close R n₀ proper func r-few using (module Holds)

  rest : Rest U → Rest C
  rest R′ m z bq with R′ (back m) z bq
  ... | ks , h = base ++ ks , λ (j , _) ay ry → pick j ay ry
    where
      pick : ∀ {y e} → Bd.JoinT y e → _ → _ → y ∈ (base ++ ks)
      pick j ay ry with classify j
      ... | inj₁ m        = ∈-++⁺ˡ m
      ... | inj₂ (_ , u′) = ∈-++⁺ʳ base (h u′ ay ry)

  held : ∀ {cs} → Held R cs → Held C cs
  held H = held-same (λ r → _ , row r , same-refl _) end-row (λ m → _ , back m , rows-refl (back m))
             (λ _ y _ no → no (_ , lift y , λ v → v)) rest (Holds.held H)
