{-# OPTIONS --guardedness #-}

-- A LIMIT OF HELD READINGS IS HELD, wherever each of its rows is some
-- reading's and it agrees with some reading up to any position few of its
-- rows precede: every field reads one row, or a run met and the rows up to
-- one position, which a reading agreeing that far shares.  Only the rest
-- reads every row of an instant, so it is asked of the limit itself.
module simultaneous.HeldLim where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ; ∈-∃++)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)

open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import simultaneous.SObs using (lone; module Elaborate)
open import denotation.EmissionSet using (end; EmissionSet; Few; _≺_; _≼_)
open import denotation.Read using (Run; []; _∷_; cursor; After; Visible)
open import denotation.Laws.Modulus using (AgreeTo; upto; ≺→≼; ≼-refl; ≺-trans; ≺-≼-≺)
open import denotation.Laws.Truth using (few-ag)
open import simultaneous.Relations using (Met)
open import simultaneous.Project using (run-prefix)
open import simultaneous.Routed using (Held; Rest; Idle)
open import simultaneous.Shut using (Shut)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

module _ {X : Set} {t t′ : EmissionSet X} {Q : Pos} (ag : AgreeTo Q t t′) where

  -- A run whose rows lie no later than `Q` is met where `t` agrees.
  run-ag : ∀ {c rs} → Run t c rs → (∀ {k e} → (k , e) ∈ rs → k ≼ Q) → Run t′ c rs
  run-ag []                                                    _  = []
  run-ag {c} {(q , e) ∷ _} (((pr , fw) , vi , af , least) ∷ rn) le =
    (((to (proj₁ pr) , end′) , few-ag ag qQ fw) , vi , af , least′) ∷ run-ag rn (λ m → le (there m))
    where
      qQ : q ≼ Q
      qQ = le (here refl)
      under : ∀ {k} → k ≺ q → k ≼ Q
      under {k} kq = ≺→≼ {k} {Q} (≺-≼-≺ {k} {q} {Q} kq qQ)
      to : t q e → t′ q e
      to = proj₁ (upto ag {q} {e} qQ)
      end′ : ∀ {d} → t′ d end → q ≼ d
      end′ {d} x dq = proj₂ pr (proj₂ (upto ag {d} (under dq)) x) dq
      least′ : ∀ {k e′} → t′ k e′ → Visible e′ → After c k → q ≼ k
      least′ {k} x v a kq = least (proj₂ (upto ag {k} (under kq)) x) v a kq

module _ {X : Set} {t : EmissionSet X} where

  -- Each row met lies past the cursor it was met from.
  run-past : ∀ {q rs} → Run t (just q) rs → ∀ {k e} → (k , e) ∈ rs → q ≺ k
  run-past ((_ , _ , af , _) ∷ _)  (here refl) = af
  run-past {q} ((_ , _ , af , _) ∷ rn) {k} (there m) = ≺-trans {q} {_} {k} af (run-past rn m)

  -- What lies past where a run stands lies past each row it met.
  cursor-past : ∀ {q rs w} → Run t (just q) rs → After (cursor (just q) rs) w → q ≺ w
  cursor-past []                           a = a
  cursor-past {q} {w = w} ((_ , _ , af , _) ∷ rn) a = ≺-trans {q} {_} {w} af (cursor-past rn a)

  run-below : ∀ {c rs w} → Run t c rs → After (cursor c rs) w → ∀ {k e} → (k , e) ∈ rs → k ≺ w
  run-below (_ ∷ rn) a (here refl) = cursor-past rn a
  run-below (_ ∷ rn) a (there m)   = run-below rn a m

  -- A run ending at `y` lies no later than `y`.
  upto-last : ∀ {c} r₁ {y e} → Run t c (r₁ ++ [ (y , e) ]) → ∀ {k e′} → (k , e′) ∈ r₁ ++ [ (y , e) ] → k ≼ y
  upto-last []      {y} _  (here refl) = ≼-refl {y}
  upto-last []      _        (there ())
  upto-last (_ ∷ r₁) {y} (_ ∷ rn) (here refl) = ≺→≼ {_} {y} (run-past rn (∈-++⁺ʳ r₁ (here refl)))
  upto-last (_ ∷ r₁) (_ ∷ rn) (there m)   = upto-last r₁ rn m

  -- The run up to a row it meets.
  pre-at : ∀ {c} r₁ {y e} r₂ → Run t c (r₁ ++ (y , e) ∷ r₂) → Run t c (r₁ ++ [ (y , e) ])
  pre-at r₁ {y} {e} r₂ rn = run-prefix (r₁ ++ [ (y , e) ]) (subst (Run t _) (sym (++-assoc r₁ [ (y , e) ] r₂)) rn)

  last-few : ∀ {c} r₁ {y e} → Run t c (r₁ ++ [ (y , e) ]) → Few t y
  last-few []       ((sn , _) ∷ _) = proj₂ sn
  last-few (_ ∷ r₁) (_ ∷ rn)       = last-few r₁ rn

module LimHeld {A : Set} (t : EmissionSet (IE A)) (c : ℕ → EmissionSet (IE A)) (cs : List Pos)
               (row : ∀ {y e} → t y e → Σ ℕ λ N → c N y e)
               (agree : ∀ {q} → Few t q → Σ ℕ λ N → AgreeTo q t (c N))
               (H : ∀ n → Held (c n) cs) (rest : Rest t) where

  -- A run met up to a row is met by a reading.
  lift : ∀ r₁ {y e} → Met t (r₁ ++ [ (y , e) ]) → Σ ℕ λ N → Met (c N) (r₁ ++ [ (y , e) ])
  lift r₁ mt with agree (last-few r₁ mt)
  ... | N , ag = N , run-ag ag mt (upto-last r₁ mt)

  held : Held t cs
  held = record
    { named   = λ x → Held.named (H (proj₁ (row x))) (proj₂ (row x))
    ; covered = λ { mt r₁ r₂ refl cr ne → let (N , m′) = lift r₁ (pre-at r₁ r₂ mt) in Held.covered (H N) m′ r₁ [] refl cr ne }
    ; exact   = λ { mt r₁ r₂ refl → let (N , m′) = lift r₁ (pre-at r₁ r₂ mt) in Held.exact (H N) m′ r₁ [] refl }
    ; routing = λ x → Held.routing (H (proj₁ (row x))) (proj₂ (row x))
    ; shut    = shut
    ; early   = λ x → Held.early (H (proj₁ (row x))) (proj₂ (row x))
    ; ends    = λ x → Held.ends (H (proj₁ (row x))) (proj₂ (row x))
    ; done    = λ x → Held.done (H (proj₁ (row x))) (proj₂ (row x))
    ; late    = λ x → Held.late (H (proj₁ (row x))) (proj₂ (row x))
    ; idle    = idle
    ; rest    = rest }
    where
      shut : Shut t
      shut mt r₁ r₂ refl z bq yv ry with ∈-∃++ yv
      ... | a , b , refl with lift (r₁ ++ a) (pre-at (r₁ ++ a) b (subst (Met t) (sym (++-assoc r₁ a _)) mt))
      ...   | N , m′ = Held.shut (H N) (subst (Met (c N)) (++-assoc r₁ a _) m′) r₁ (a ++ [ _ ]) refl z bq (∈-++⁺ʳ a (here refl)) ry

      idle : Idle t
      idle mt ne {w} fw aw least with agree fw
      ... | N , ag = Held.idle (H N) (run-ag ag mt (λ {k} m → ≺→≼ {k} {w} (run-below mt aw m))) ne (few-ag ag (≼-refl {w}) fw) aw
        λ {y} x v a yw → least (proj₂ (upto ag {y} (≺→≼ {y} {w} yw)) x) v a yw
