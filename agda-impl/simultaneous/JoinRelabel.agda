-- A JOINER RESPECTS A RELABELLING: two outers carrying each other's rows
-- along `Φ`, and lanes doing the same at the matching subscriptions, give
-- two merges carrying each other's rows along `Φ`.  `Φ` keeps the order
-- of every two positions, and is a homomorphism at an outer value's two
-- effects: its value's skip and its lane's subscription.
module simultaneous.JoinRelabel where

open import Data.Bool using (T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.List using ([_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import denotation.Position using (Pos; inside; ix; _⊕_)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; _≺_; _≼_; Work; Den; enter; Ended; LaneOf; module Merge)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≼-or-≻; ≼-split)

-- Pins name positions: relabelled with them.
evΦ : ∀ {X : Set} → (Pos → Pos) → Ev X → Ev X
evΦ Φ (pin r) = pin (Φ r)
evΦ Φ e       = e

-- `u` carries `t` along `Φ`: every row on its image, matched by `M`, and
-- every row `Sh` shows back on one.
record Sim {X Y : Set} (Φ : Pos → Pos) (M : Ev X → Ev Y → Set) (Sh : Ev Y → Set) (t : EmissionSet X) (u : EmissionSet Y) : Set where
  field
    fwd  : ∀ {k e} → t k e → Σ (Ev Y) λ e′ → u (Φ k) e′ × M e e′
    back : ∀ {l e′} → u l e′ → Sh e′ → Σ Pos λ k → l ≡ Φ k × Σ (Ev X) λ e → t k e × M e e′

-- An outer's shown rows: its values and its end.
Vis : ∀ {X : Set} → Ev X → Set
Vis (out _) = ⊤
Vis end     = ⊤
Vis skip    = ⊥
Vis (pin _) = ⊥

module MergeRel {A B B′ : Set} (Φ : Pos → Pos)
  (mono : ∀ {k k′} → k ≺ k′ → Φ k ≺ Φ k′)
  (M : Ev B → Ev B′ → Set) (Sh : Ev B′ → Set)
  (m-skip : M skip skip) (m-end : M end end) (m-pin : ∀ {r} → M (pin r) (pin (Φ r)))
  (end→ : ∀ {e} → M end e → e ≡ end) (end← : ∀ {e} → M e end → e ≡ end) (pin→ : ∀ {r e} → M (pin r) e → e ≡ pin (Φ r))
  (sh-end : Sh end) (sh-skip : Sh skip → ⊥) (sh-pin : ∀ {r} → Sh (pin r) → ⊥)
  (ins : ∀ {r k} → T (inside r k) → T (inside (Φ r) (Φ k)))
  {f : A → Den B} {f′ : A → Den B′} {o o′ : EmissionSet A}
  (outer : Sim Φ (λ e e′ → e′ ≡ evΦ Φ e) Vis o o′)
  (h0 : ∀ {q a} → o q (out a) → Φ (q ⊕ [ ix 0 ]) ≡ Φ q ⊕ [ ix 0 ])
  (h1 : ∀ {q a} → o q (out a) → Φ (q ⊕ [ ix 1 ]) ≡ Φ q ⊕ [ ix 1 ])
  (lanes : ∀ {q a} → o q (out a) → Sim Φ M Sh (enter (f a) (q ⊕ [ ix 1 ])) (enter (f′ a) (Φ q ⊕ [ ix 1 ])))
  where

  module P = Merge f o
  module Q = Merge f′ o′
  open Sim

  -- `Φ` reflects the order it keeps.
  refl≺ : ∀ {k k′} → Φ k ≺ Φ k′ → k ≺ k′
  refl≺ {k} {k′} h with ≼-or-≻ k′ k
  ... | inj₂ lt = lt
  ... | inj₁ le with ≼-split {k′} {k} le
  ...   | inj₁ lt   = ⊥-elim (≺-absurd {Φ k} {Φ k′} h (mono lt))
  ...   | inj₂ refl = ⊥-elim (≺-irrefl {Φ k} h)

  mono≼ : ∀ {k k′} → k ≼ k′ → Φ k ≼ Φ k′
  mono≼ le h = le (refl≺ h)

  refl≼ : ∀ {k k′} → Φ k ≼ Φ k′ → k ≼ k′
  refl≼ le h = le (mono h)

  -- The outer's values, ends and other rows land as themselves.
  o-out : ∀ {q a} → o q (out a) → o′ (Φ q) (out a)
  o-out x with fwd outer x
  ... | _ , x′ , refl = x′

  o-end : ∀ {c} → o c end → o′ (Φ c) end
  o-end x with fwd outer x
  ... | _ , x′ , refl = x′

  o-skip : ∀ {q} → o q skip → o′ (Φ q) skip
  o-skip x with fwd outer x
  ... | _ , x′ , refl = x′

  o-pin : ∀ {q r} → o q (pin r) → o′ (Φ q) (pin (Φ r))
  o-pin x with fwd outer x
  ... | _ , x′ , refl = x′

  out-inv : ∀ {e : Ev A} {a} → out a ≡ evΦ Φ e → e ≡ out a
  out-inv {out _} refl = refl
  out-inv {skip}  ()
  out-inv {end}   ()
  out-inv {pin _} ()

  end-inv : ∀ {e : Ev A} → end ≡ evΦ Φ e → e ≡ end
  end-inv {out _} ()
  end-inv {skip}  ()
  end-inv {end}   refl = refl
  end-inv {pin _} ()

  o-out← : ∀ {l a} → o′ l (out a) → Σ Pos λ q → l ≡ Φ q × o q (out a)
  o-out← x′ with back outer x′ tt
  ... | q , eq , e , x , m with out-inv {e} m
  ...   | refl = q , eq , x

  o-end← : ∀ {l} → o′ l end → Σ Pos λ c → l ≡ Φ c × o c end
  o-end← x′ with back outer x′ tt
  ... | c , eq , e , x , m with end-inv {e} m
  ...   | refl = c , eq , x

  -- A lane row lands past its lane's subscription.
  sub→ : ∀ {q a k} → o q (out a) → (q ⊕ [ ix 1 ]) ≺ k → (Φ q ⊕ [ ix 1 ]) ≺ Φ k
  sub→ x lt = subst (_≺ _) (h1 x) (mono lt)

  sub← : ∀ {q a k} → o q (out a) → (Φ q ⊕ [ ix 1 ]) ≺ Φ k → (q ⊕ [ ix 1 ]) ≺ k
  sub← x lt = refl≺ (subst (_≺ _) (sym (h1 x)) lt)

  work→ : ∀ {e e′} → M e e′ → Work e → Work e′
  work→ {e′ = out _} m w = tt
  work→ {e′ = skip}  m w = tt
  work→ {e′ = pin _} m w = tt
  work→ {e = e} {e′ = end} m w with end← m
  ... | refl = w

  work← : ∀ {e e′} → M e e′ → Work e′ → Work e
  work← {e = out _} m w = tt
  work← {e = skip}  m w = tt
  work← {e = pin _} m w = tt
  work← {e = end}   m w with end→ m
  ... | refl = w

  -- Every part done by `c` is done by its image, and back.
  done→ : ∀ {c} → P.Done c → Q.Done (Φ c)
  done→ {c} ((c₀ , x , le) , ls) = (Φ c₀ , o-end x , mono≼ le) , lanes′
    where
      lanes′ : ∀ {q′ a} → o′ q′ (out a) → ⊤ → q′ ≺ Φ c → ¬ ⊥ → Ended (LaneOf f′ q′ a) (Φ c)
      lanes′ x′ _ lt _ with o-out← x′
      ... | q , refl , x with ls x tt (refl≺ lt) (λ ())
      ...   | c₁ , (y , s) , le₁ with fwd (lanes x) y
      ...     | e′ , y′ , m with end→ m
      ...       | refl = Φ c₁ , (y′ , sub→ x s) , mono≼ le₁

  done← : ∀ {c} → Q.Done (Φ c) → P.Done c
  done← {c} ((c₀′ , x′ , le) , ls) with o-end← x′
  ... | c₀ , refl , x = (c₀ , x , refl≼ le) , lanes′
    where
      lanes′ : ∀ {q a} → o q (out a) → ⊤ → q ≺ c → ¬ ⊥ → Ended (LaneOf f q a) c
      lanes′ x _ lt _ with ls (o-out x) tt (mono lt) (λ ())
      ... | c₁′ , (y′ , s) , le₁ with back (lanes x) y′ sh-end
      ...   | c₁ , refl , e , y , m with end← m
      ...     | refl = c₁ , (y , sub← x s) , refl≼ le₁

  -- THE MERGE CARRIES ITS RELABELLED SELF.
  merge-rel : Sim Φ M Sh P.JoinT Q.JoinT
  merge-rel = record { fwd = to ; back = from }
    where
      to : ∀ {k e} → P.JoinT k e → Σ (Ev B′) λ e′ → Q.JoinT (Φ k) e′ × M e e′
      to (P.val x)  = skip , subst (λ l → Q.JoinT l skip) (sym (h0 x)) (Q.val (o-out x)) , m-skip
      to (P.step x) = skip , Q.step (o-skip x) , m-skip
      to (P.opin x) = _ , Q.opin (o-pin x) , m-pin
      to (P.oend x d)  = end , Q.oend (o-end x) (done→ d) , m-end
      to (P.opass x n) = skip , Q.opass (o-end x) (λ d → n (done← d)) , m-skip
      to (P.lane x _ (y , s) _ w) with fwd (lanes x) y
      ... | e′ , y′ , m = e′ , Q.lane (o-out x) tt (y′ , sub→ x s) (λ ()) (work→ m w) , m
      to (P.lend x _ (y , s) _ _ d) with fwd (lanes x) y
      ... | e′ , y′ , m with end→ m
      ...   | refl = end , Q.lend (o-out x) tt (y′ , sub→ x s) (λ ()) (λ ()) (done→ d) , m-end
      to (P.lpass x _ (y , s) _ _ n) with fwd (lanes x) y
      ... | e′ , y′ , m with end→ m
      ...   | refl = skip , Q.lpass (o-out x) tt (y′ , sub→ x s) (λ ()) (λ ()) (λ d → n (done← d)) , m-skip
      to (P.hand _ _ _ _ ())
      to (P.left x _ (y , s) _ i) with fwd (lanes x) y
      ... | e′ , y′ , m with pin→ m
      ...   | refl = _ , Q.left (o-out x) tt (y′ , sub→ x s) (λ ()) (ins i) , m
      to (P.run () _)
      to (P.rend () _ _)
      to (P.rpass () _ _)
      to (P.rhand () _)

      from : ∀ {l e′} → Q.JoinT l e′ → Sh e′ → Σ Pos λ k → l ≡ Φ k × Σ (Ev B) λ e → P.JoinT k e × M e e′
      from (Q.val _)     sh = ⊥-elim (sh-skip sh)
      from (Q.step _)    sh = ⊥-elim (sh-skip sh)
      from (Q.opin _)    sh = ⊥-elim (sh-pin sh)
      from (Q.opass _ _) sh = ⊥-elim (sh-skip sh)
      from (Q.oend x′ d) sh with o-end← x′
      ... | c , refl , x = c , refl , end , P.oend x (done← d) , m-end
      from (Q.lane x′ _ (y′ , s) _ w) sh with o-out← x′
      ... | q , refl , x with back (lanes x) y′ sh
      ...   | k , refl , e , y , m = k , refl , e , P.lane x tt (y , sub← x s) (λ ()) (work← m w) , m
      from (Q.lend x′ _ (y′ , s) _ _ d) sh with o-out← x′
      ... | q , refl , x with back (lanes x) y′ sh
      ...   | c , refl , e , y , m with end← m
      ...     | refl = c , refl , end , P.lend x tt (y , sub← x s) (λ ()) (λ ()) (done← d) , m-end
      from (Q.lpass _ _ _ _ _ _) sh = ⊥-elim (sh-skip sh)
      from (Q.hand _ _ _ _ ())   sh
      from (Q.left _ _ _ _ _)    sh = ⊥-elim (sh-pin sh)
      from (Q.run () _)          sh
      from (Q.rend () _ _)       sh
      from (Q.rpass () _ _)      sh
      from (Q.rhand () _)        sh
