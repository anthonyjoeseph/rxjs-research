{-# OPTIONS --guardedness #-}

-- A SHARED OUTER HOLDS as the outer does.  The trigger is a concat of a
-- lane that waits on the share's empty source and shows nothing, then
-- the outer: every row a reader meets is the outer's, subscribed once,
-- where the waiting lane ends, inside the share's own burst.
module simultaneous.HeldTrigger where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (Equivalence)
open import Data.Bool.Properties using (T-≡)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import Tree using (Obs; mergeᶠ; empty; of; flatMap)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; sub; last; _⊕_; inside; _<ˡ_)
open import denotation.Events using (Timeline; fresh; <ᵖ-part)
open import denotation.EmissionSet using (EmissionSet; Den; hot; enter; Proper; DenEnv; Ev; out; skip; pin; end; _≺_; _≼_; Dep; Reach;
  Ended; at-out; at-end; on-out; Rejoin; shown; heard; ended; late; module Op; module Values;
  module Bounded; module Merge)
open import denotation.Read using (Run; []; _∷_; Visible)
open import denotation.Laws using (good-cons; inv-⟦⟧)
open import denotation.Laws.Connect using () renaming (lawful to src-lawful; ok₀ to body-ok)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≺-absurd; ≼-refl; ≺-ext; entered-reach)
open import denotation.Laws.Worlds using (Ok; InvAt; Hots; GoodEnv; ok-step; ok-in; world-after; ⊕-assoc; ⊕-injˡ)
open import denotation.Laws.Worlds.Leaves using (of-reach)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Routed using (Held; HeldD; Early; Ex; Sync; Rest)
open import simultaneous.Relabel using (held-same)
open import simultaneous.HeldConnect using (early-inst; held-ex; same-refl; rows-refl)
open import simultaneous.HeldDefer using (sync-up)
open import simultaneous.HeldComb using (ev)
open import simultaneous.CombSent using (assoc³)
open import simultaneous.LaneLocal using (inv-ev)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; srcLane)

≺-part : ∀ p {a b} ys zs → a <ˡ b ≡ true → (p ⊕ (a ∷ ys)) ≺ (p ⊕ (b ∷ zs))
≺-part p ys zs h = Equivalence.from T-≡ (<ᵖ-part p ys zs h)

≺⇒≼ : ∀ {x y} → x ≺ y → x ≼ y
≺⇒≼ {x} {y} xy yx = ≺-absurd {x} {y} xy yx

-- A pin waits on what any row waits on but a pin.
dep-end : ∀ {A} {q} {e : Ev A} {k} → Dep q e k skip → Dep q e k end
dep-end {e = pin _} d i with d i
... | inj₁ x = inj₁ x
... | inj₂ ()
dep-end {e = out _} _ = tt
dep-end {e = skip}  _ = tt
dep-end {e = end}   _ = tt

------------------------------------------------------------------------
-- The waiting lane

-- A lane subscribed at `sb` that shows nothing, ending once, at `cb`.
record Blocked {Y : Set} (d : Den Y) (sb cb : Pos) : Set where
  field
    bk-out  : ∀ {y x} → enter d sb y (out x) → ⊥
    bk-end  : ∀ {c} → enter d sb c end → c ≡ cb
    bk-has  : enter d sb cb end
    bk-rows : Σ (List Pos) λ ks → ∀ {y e} → enter d sb y e → y ∈ ks

-- An `each` over a hot that only ends shows only its end, joined.
module Blk {X Y : Set} (r sb : Pos) (lt : sb ≺ (r ⊕ [ last ])) where

  e₀ cb : Pos
  e₀ = r ⊕ [ last ]
  cb = e₀ ⊕ [ sub sb ]

  σ₀ : EmissionSet X
  σ₀ = Proper (enter Op.empty r)

  σ-row : ∀ {q e} → σ₀ q e → q ≡ e₀ × e ≡ end
  σ-row ((at-end , _) , _) = refl , refl

  σ-end : σ₀ e₀ end
  σ-end = (at-end , [] , λ { at-end l _ → ⊥-elim (≺-irrefl {e₀} l) }) , λ { (at-end , _) → ≼-refl {e₀} }

  rejoin-row : ∀ {q e} → Rejoin sb σ₀ q e → q ≡ cb × e ≡ end
  rejoin-row (shown y b _) with σ-row y
  ... | refl , refl = ⊥-elim b
  rejoin-row (heard y _) with σ-row y
  ... | _ , ()
  rejoin-row (ended y _) with σ-row y
  ... | refl , _ = refl , refl
  rejoin-row (late y c≼) with σ-row y
  ... | refl , _ = ⊥-elim (c≼ lt)

  Hot : EmissionSet X
  Hot = enter (hot σ₀) sb

  hot-end : Hot cb end
  hot-end = ended σ-end lt , cb ∷ [] , λ j _ _ → here (proj₁ (rejoin-row j))

  module K = Merge (λ (_ : X) → Op.of ([] {A = Y})) Hot

  k-pos : ∀ {y e} → K.JoinT y e → y ≡ cb
  k-pos (K.val o)       with () ← proj₂ (rejoin-row (proj₁ o))
  k-pos (K.step o)      with () ← proj₂ (rejoin-row (proj₁ o))
  k-pos (K.opin o)      with () ← proj₂ (rejoin-row (proj₁ o))
  k-pos (K.oend o _)    = proj₁ (rejoin-row (proj₁ o))
  k-pos (K.opass o _)   = proj₁ (rejoin-row (proj₁ o))
  k-pos (K.lane o _ _ _ _)    with () ← proj₂ (rejoin-row (proj₁ o))
  k-pos (K.lend o _ _ _ _ _)  with () ← proj₂ (rejoin-row (proj₁ o))
  k-pos (K.lpass o _ _ _ _ _) with () ← proj₂ (rejoin-row (proj₁ o))
  k-pos (K.hand o _ _ _ _)    with () ← proj₂ (rejoin-row (proj₁ o))
  k-pos (K.left o _ _ _ _)    with () ← proj₂ (rejoin-row (proj₁ o))
  k-pos (K.run () _)
  k-pos (K.rend () _ _)
  k-pos (K.rpass () _ _)
  k-pos (K.rhand () _)

  Bk : EmissionSet Y
  Bk = enter (Op.flatMap (mergeᶠ nothing) (λ (_ : X) → Op.of ([] {A = Y})) (hot σ₀)) sb

  bk-out : ∀ {y x} → Bk y (out x) → ⊥
  bk-out (K.lane o _ _ _ _ , _) with () ← proj₂ (rejoin-row (proj₁ o))
  bk-out (K.run () _ , _)

  bk-end : ∀ {c} → Bk c end → c ≡ cb
  bk-end (j , _) = k-pos j

  bk-has : Bk cb end
  bk-has = K.oend hot-end ((cb , hot-end , ≼-refl {cb}) , λ o _ _ _ → ⊥-elim (out≢ (proj₂ (rejoin-row (proj₁ o))))) ,
           cb ∷ [] , λ j _ _ → here (k-pos j)
    where
      out≢ : ∀ {x} → out x ≡ end → ⊥
      out≢ ()

  bk-rows : Σ (List Pos) λ ks → ∀ {y e} → Bk y e → y ∈ ks
  bk-rows = cb ∷ [] , λ (j , _) → here (k-pos j)

  blocked : Blocked (Op.flatMap (mergeᶠ nothing) (λ (_ : X) → Op.of ([] {A = Y})) (hot σ₀)) sb cb
  blocked = record { bk-out = bk-out ; bk-end = bk-end ; bk-has = bk-has ; bk-rows = bk-rows }

------------------------------------------------------------------------
-- The concat

-- The outer: two values and the end.
module Two (P : Pos) where

  q₀ q₁ e₁ : Pos
  q₀ = P ⊕ [ ix 0 ]
  q₁ = P ⊕ [ ix 1 ]
  e₁ = P ⊕ [ last ]

  O : EmissionSet Bool
  O = enter (Op.of (true ∷ false ∷ [])) P

  open Values O using (Nth; Next; first; next) public

  q₀q₁ : q₀ ≺ q₁
  q₀q₁ = ≺-part P [] [] refl

  q₀e₁ : q₀ ≺ e₁
  q₀e₁ = ≺-part P [] [] refl

  -- The outer's rows: two values and the end.
  o-out : ∀ {q a} → O q (out a) → (q ≡ q₀ × a ≡ true) ⊎ (q ≡ q₁ × a ≡ false)
  o-out (at-out , _)        = inj₁ (refl , refl)
  o-out (on-out at-out , _) = inj₂ (refl , refl)
  o-out (on-out (on-out ()) , _)

  o-end : ∀ {c} → O c end → c ≡ e₁
  o-end (on-out (on-out at-end) , _) = refl

  o-skip : ∀ {c} → O c skip → ⊥
  o-skip (on-out (on-out ()) , _)

  o-pin : ∀ {c r} → O c (pin r) → ⊥
  o-pin (on-out (on-out ()) , _)

  o₀ : O q₀ (out true)
  o₀ = at-out , of-reach P 0 (true ∷ false ∷ []) {q₀} {out true}

  o₁ : O q₁ (out false)
  o₁ = on-out at-out , of-reach P 0 (true ∷ false ∷ []) {q₁} {out false}

  oe : O e₁ end
  oe = on-out (on-out at-end) , of-reach P 0 (true ∷ false ∷ []) {e₁} {end}

  nth₀ : Nth 0 q₀ true
  nth₀ = first o₀ least
    where
      least : ∀ {k b} → O k (out b) → q₀ ≼ k
      least x with o-out x
      ... | inj₁ (refl , _) = ≼-refl {q₀}
      ... | inj₂ (refl , _) = ≺⇒≼ {q₀} {q₁} q₀q₁

  nth₁ : Nth 1 q₁ false
  nth₁ = next nth₀ o₁ q₀q₁ nx
    where
      nx : Next q₀ q₁
      nx x lt with o-out x
      ... | inj₁ (refl , _) = ⊥-elim (≺-irrefl {q₀} lt)
      ... | inj₂ (refl , _) = ≼-refl {q₁}

  nth-0 : ∀ {q a} → Nth 0 q a → q ≡ q₀ × a ≡ true
  nth-0 (first x least) with o-out x
  ... | inj₁ e = e
  ... | inj₂ (refl , _) = ⊥-elim (least o₀ q₀q₁)

  nth-1 : ∀ {q a} → Nth 1 q a → q ≡ q₁ × a ≡ false
  nth-1 (next N x lt _) with nth-0 N | o-out x
  ... | refl , _ | inj₁ (refl , _) = ⊥-elim (≺-irrefl {q₀} lt)
  ... | refl , _ | inj₂ e = e

  nth-2 : ∀ {i q a} → Nth (suc (suc i)) q a → ⊥
  nth-2 {suc i} (next N _ _ _) = nth-2 N
  nth-2 {zero} (next N x lt _) with nth-1 N | o-out x
  ... | refl , _ | inj₁ (refl , _) = ≺-absurd {q₀} {q₁} q₀q₁ lt
  ... | refl , _ | inj₂ (refl , _) = ≺-irrefl {q₁} lt


-- A CONCAT OF A LANE SHOWING ONLY ITS END AT `cb`, THEN A LANE: every
-- row a reader meets is the second lane's, subscribed at `cb ⊕ [ ix 1 ]`.
-- A bounded merge's first lane starts at its value.
start-0 : ∀ {A B : Set} {n f} {o : EmissionSet A} {q s} → Bounded.Starts {A} {B} (suc n) f o 0 q [] s → s ≡ q ⊕ [ ix 1 ]
start-0 (Bounded.room _) = refl
start-0 (Bounded.freed () _)
start-0 (Bounded.queued () _ _ _ _)

module Cat {A : Set} (G : Bool → Den (IE A)) (P cb : Pos) (B : Blocked (G true) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) cb)
           (sb≺cb : ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ≺ cb) (q₁≺cb : (P ⊕ [ ix 1 ]) ≺ cb) (e₁≺cb : (P ⊕ [ last ]) ≺ cb)
           (after  : ∀ {y e} → enter (G false) (cb ⊕ [ ix 1 ]) y e → (cb ⊕ [ ix 1 ]) ≺ y)
           (pinned : ∀ {y r} → enter (G false) (cb ⊕ [ ix 1 ]) y (pin r) → T (inside r y)) where

  open Two P
  open Blocked B
  module Bd = Bounded 1 G O

  sb s₁ : Pos
  sb = q₀ ⊕ [ ix 1 ]
  s₁ = cb ⊕ [ ix 1 ]

  C : EmissionSet (IE A)
  C = enter (Op.flatMap (mergeᶠ (just 1)) G (Op.of (true ∷ false ∷ []))) P

  In : EmissionSet (IE A)
  In = enter (G false) s₁

  cbs₁ : cb ≺ s₁
  cbs₁ = ≺-ext cb []

  -- The second lane starts where the first ends.

  ends-0 : ∀ {c} → Bd.Ends 0 [] c → c ≡ cb
  ends-0 (_ , _ , _ , N , St , (x , _)) with nth-0 N | start-0 St
  ... | refl , refl | refl = bk-end x

  start-1 : ∀ {s} → Bd.Starts 1 q₁ (Bd.Sched 1) s → s ≡ s₁
  start-1 (Bd.room (s≤s ()))
  start-1 (Bd.freed _ (inj₁ (_ , E , lt))) = ⊥-elim (≺-absurd {q₁} {cb} q₁≺cb (subst (_≺ q₁) (ends-0 E) lt))
  start-1 (Bd.freed _ (inj₂ ()))
  start-1 (Bd.queued _ _ (inj₁ (_ , E , refl)) _ _) = cong (_⊕ [ ix 1 ]) (ends-0 E)
  start-1 (Bd.queued _ _ (inj₂ ()) _ _)

  lane-of : ∀ {q a k e} → Bd.Lane q a k e
          → (q ≡ q₀ × a ≡ true × enter (G true) sb k e) ⊎ (q ≡ q₁ × a ≡ false × In k e)
  lane-of (zero , _ , (N , St) , (x , _)) with nth-0 N | start-0 St
  ... | refl , refl | refl = inj₁ (refl , refl , x)
  lane-of (suc zero , _ , (N , St) , (x , _)) with nth-1 N
  ... | refl , refl with start-1 St
  ...   | refl = inj₂ (refl , refl , x)
  lane-of (suc (suc _) , _ , (N , _) , _) = ⊥-elim (nth-2 N)

  E₀ : Bd.Ends 0 [] cb
  E₀ = q₀ , true , sb , nth₀ , Bd.room (s≤s z≤n) , (bk-has , sb≺cb)

  st₁ : Bd.Starts 1 q₁ (Bd.Sched 1) s₁
  st₁ = Bd.queued (s≤s z≤n) q₁≺cb (inj₁ (cb , E₀ , refl)) (inj₁ (cb , E₀ , ≼-refl {cb})) none
    where
      none : Bd.Kth (_≺ cb) (Bd.Sched 1) 0 → ⊥
      none (inj₁ (_ , E , lt)) = ≺-irrefl {cb} (subst (_≺ cb) (ends-0 E) lt)
      none (inj₂ ())

  lane₁ : ∀ {k e} → In k e → Bd.Lane q₁ false k e
  lane₁ y = 1 , s₁ , (nth₁ , st₁) , (y , after y)

  -- The second lane hands on to nothing.
  no-hand : ∀ {c} → In c end → Bd.Queued c → ⊥
  no-hand y (zero , _ , _ , (N , St)) with nth-0 N
  ... | refl , refl = ≺-absurd {s₁} {q₀} (subst (s₁ ≺_) (⊕-injˡ _ q₀ (start-0 St)) (after y))
                        (≺-trans {q₀} {q₁} {s₁} q₀q₁ (≺-trans {q₁} {cb} {s₁} q₁≺cb cbs₁))
  no-hand y (suc zero , _ , _ , (N , St)) with nth-1 N
  ... | refl , refl = ≺-absurd {s₁} {cb} (subst (s₁ ≺_) (⊕-injˡ _ cb (start-1 St)) (after y)) cbs₁
  no-hand y (suc (suc _) , _ , _ , (N , _)) = nth-2 N

  -- Where the second lane ends, so has everything.
  done : ∀ {c} → In c end → Bd.Done c
  done {c} y = (e₁ , oe , ≺⇒≼ {e₁} {c} (≺-trans {e₁} {s₁} {c} (≺-trans {e₁} {cb} {s₁} e₁≺cb cbs₁) (after y))) , lanes
    where
      lanes : ∀ {q a} → O q (out a) → Bd.Indexed q → q ≺ c → (⊥ → ⊥) → Ended (Bd.Lane q a) c
      lanes x _ _ _ with o-out x
      ... | inj₁ (refl , refl) = cb , (0 , sb , (nth₀ , Bd.room (s≤s z≤n)) , (bk-has , sb≺cb)) , ≺⇒≼ {cb} {c} (≺-trans {cb} {s₁} {c} cbs₁ (after y))
      ... | inj₂ (refl , refl) = c , lane₁ y , ≼-refl {c}

  base : List Pos
  base = (q₀ ⊕ [ ix 0 ]) ∷ (q₁ ⊕ [ ix 0 ]) ∷ e₁ ∷ (cb ⊕ [ ix 0 ]) ∷ proj₁ bk-rows

  bk-mem : ∀ {y e} → enter (G true) sb y e → y ∈ base
  bk-mem x = there (there (there (there (proj₂ bk-rows x))))

  -- EVERY ROW OF THE CONCAT is one of finitely many, or the second lane's.
  classify : ∀ {k e′} → Bd.JoinT k e′ → k ∈ base ⊎ Σ (Ev (IE A)) λ e₀ → In k e₀ × (∀ {q e} → Dep q e k e′ → Dep q e k e₀)
  classify (Bd.val x) with o-out x
  ... | inj₁ (refl , _) = inj₁ (here refl)
  ... | inj₂ (refl , _) = inj₁ (there (here refl))
  classify (Bd.step x)  = ⊥-elim (o-skip x)
  classify (Bd.opin x)  = ⊥-elim (o-pin x)
  classify (Bd.oend x _) with o-end x
  ... | refl = inj₁ (there (there (here refl)))
  classify (Bd.opass x _) with o-end x
  ... | refl = inj₁ (there (there (here refl)))
  classify (Bd.lane _ _ L _ _) with lane-of L
  ... | inj₁ (_ , _ , y) = inj₁ (bk-mem y)
  ... | inj₂ (_ , _ , y) = inj₂ (_ , y , λ d → d)
  classify (Bd.lend _ _ L _ _ _) with lane-of L
  ... | inj₁ (_ , _ , y) = inj₁ (bk-mem y)
  ... | inj₂ (_ , _ , y) = inj₂ (_ , y , λ d → d)
  classify (Bd.lpass _ _ L _ _ _) with lane-of L
  ... | inj₁ (_ , _ , y) = inj₁ (bk-mem y)
  ... | inj₂ (_ , _ , y) = inj₂ (_ , y , dep-end)
  classify (Bd.hand _ _ L _ h) with lane-of L
  ... | inj₁ (_ , _ , y) with bk-end y
  ...   | refl = inj₁ (there (there (there (here refl))))
  classify (Bd.hand _ _ L _ h) | inj₂ (_ , _ , y) = ⊥-elim (no-hand y h)
  classify (Bd.left _ _ L _ _) with lane-of L
  ... | inj₁ (_ , _ , y) = inj₁ (bk-mem y)
  ... | inj₂ (_ , _ , y) = inj₂ (_ , y , λ d → d)
  classify (Bd.run () _)
  classify (Bd.rend () _ _)
  classify (Bd.rpass () _ _)
  classify (Bd.rhand () _)

  reach₁ : ∀ {k e} → In k e → Reach Bd.JoinT k e
  reach₁ y with entered-reach (G false) s₁ y
  ... | ks , h = base ++ ks , λ j lt d → cover j lt d
    where
      cover : ∀ {k′ e′} → Bd.JoinT k′ e′ → _ → _ → k′ ∈ (base ++ ks)
      cover j lt d with classify j
      ... | inj₁ m = ∈-++⁺ˡ m
      ... | inj₂ (_ , y′ , dd) = ∈-++⁺ʳ base (h y′ lt (dd d))

  -- The second lane's rows are the concat's.
  lift : ∀ {k e} → In k e → C k e
  lift {e = out _} y = Bd.lane o₁ (1 , false , nth₁) (lane₁ y) (λ ()) tt , reach₁ y
  lift {e = skip}  y = Bd.lane o₁ (1 , false , nth₁) (lane₁ y) (λ ()) tt , reach₁ y
  lift {e = pin _} y = Bd.left o₁ (1 , false , nth₁) (lane₁ y) (λ ()) (pinned y) , reach₁ y
  lift {e = end}   y = Bd.lend o₁ (1 , false , nth₁) (lane₁ y) (λ ()) (no-hand y) (done y) , reach₁ y

  -- And the concat's visible rows are the second lane's.
  row : ∀ {y x} → C y (out x) → In y (out x)
  row (Bd.lane _ _ L _ _ , _) with lane-of L
  ... | inj₁ (_ , _ , x) = ⊥-elim (bk-out x)
  ... | inj₂ (_ , _ , x) = x
  row (Bd.run () _ , _)

  end-row : ∀ {c} → C c end → In c end
  end-row (Bd.oend o (_ , lanes) , _) with o-end o
  ... | refl with lanes o₀ (0 , true , nth₀) q₀e₁ (λ ())
  ...   | _ , L , c₀e with lane-of L
  ...     | inj₁ (_ , _ , x) = ⊥-elim (c₀e (subst (e₁ ≺_) (sym (bk-end x)) e₁≺cb))
  ...     | inj₂ (eq , _) = ⊥-elim (≺-irrefl {q₀} (subst (q₀ ≺_) (sym eq) q₀q₁))
  end-row (Bd.lane _ _ _ _ () , _)
  end-row (Bd.lend _ _ L _ nh _ , _) with lane-of L
  ... | inj₁ (refl , refl , x) with bk-end x
  ...   | refl = ⊥-elim (nh (1 , q₁ , false , nth₁ , st₁))
  end-row (Bd.lend _ _ L _ nh _ , _) | inj₂ (_ , _ , x) = x
  end-row (Bd.run () _ , _)
  end-row (Bd.rend () _ _ , _)

  vis : ∀ {q e} → C q e → Visible e → In q e
  vis {e = out _} y _ = row y
  vis {e = end}   y _ = end-row y
  vis {e = skip}  _ ()
  vis {e = pin _} _ ()

  back : ∀ {c rs} → Run C c rs → Run In c rs
  back [] = []
  back ((((y , pr) , fw) , vi , ac , lf) ∷ run) =
    (((vis y vi , λ ce → pr (lift ce)) , (proj₁ fw , λ y′ lt → proj₂ fw (lift y′) lt)) , vi , ac , λ y′ v a → lf (lift y′) v a) ∷ back run

  rest : Rest In → Rest C
  rest R m z bq with R (back m) z bq
  ... | ks , h = base ++ ks , λ (j , _) ay ry → pick j ay ry
    where
      pick : ∀ {y e} → Bd.JoinT y e → _ → _ → y ∈ (base ++ ks)
      pick j ay ry with classify j
      ... | inj₁ m = ∈-++⁺ˡ m
      ... | inj₂ (_ , y′ , _) = ∈-++⁺ʳ base (h y′ ay ry)

  held : ∀ {cs} → Held In cs → Held C cs
  held = held-same (λ r → _ , row r , same-refl _) end-row (λ m → _ , back m , rows-refl (back m))
           (λ _ y _ no → no (_ , lift y , λ v → v)) rest

------------------------------------------------------------------------
-- The trigger

pos-sb : ∀ p → (((p ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ] ≡ p ⊕ (ix 0 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ [])
pos-sb p = trans (cong (_⊕ [ ix 1 ]) (assoc³ p (ix 0) (ix 1) (ix 0))) (⊕-assoc p (ix 0 ∷ ix 1 ∷ ix 0 ∷ []) [ ix 1 ])

-- Either reading of the waiting lane.
blk : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (env : DenEnv Δ) (r sb : Pos) (lt : sb ≺ (r ⊕ [ last ]))
    → Blocked (ev m (srcLane ρ s true) (hot (Proper (enter (ev m empty env) r)) ∷ env)) sb ((r ⊕ [ last ]) ⊕ [ sub sb ])
blk nothing  ρ s env r sb lt = Blk.blocked r sb lt
blk (just n) ρ s env r sb lt = Blk.blocked r sb lt

module Trig (m : Maybe ℕ) {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (env : DenEnv Δ) cs p
            (g : GoodEnv env) (ok : Ok (Hots env) p) (ep : Early p) where

  σ₀ : EmissionSet ⊤
  σ₀ = Proper (enter (ev m empty env) (p ⊕ [ ix 1 ]))

  env′ : DenEnv (⊤ ∷ Δ)
  env′ = hot σ₀ ∷ env

  P sb cb s₁ : Pos
  P  = (p ⊕ [ ix 0 ]) ⊕ [ ix 1 ]
  sb = (P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]
  cb = ((p ⊕ [ ix 1 ]) ⊕ [ last ]) ⊕ [ sub sb ]
  s₁ = cb ⊕ [ ix 1 ]

  G : Bool → Den (IE A)
  G c = ev m (srcLane ρ s c) env′

  L₀ = src-lawful {A = ⊤} {B = ⊤} {s = ev m empty env} {F = λ h → ev m empty (h ∷ env)}
         (inv-ev m empty env g) (λ L → inv-ev m empty (hot _ ∷ env) (good-cons L g)) p ok

  g′ : GoodEnv env′
  g′ = good-cons L₀ g

  ok₀ : Ok (Hots env′) (p ⊕ [ ix 0 ])
  ok₀ = body-ok {A = ⊤} {B = ⊤} {s = ev m empty env} {F = λ h → ev m empty (h ∷ env)}
          (inv-ev m empty env g) (λ L → inv-ev m empty (hot _ ∷ env) (good-cons L g)) p ok

  eq-cb : cb ≡ p ⊕ (ix 1 ∷ last ∷ sub sb ∷ [])
  eq-cb = assoc³ p (ix 1) last (sub sb)

  eq-s₁ : s₁ ≡ p ⊕ (ix 1 ∷ last ∷ sub sb ∷ ix 1 ∷ [])
  eq-s₁ = trans (cong (_⊕ [ ix 1 ]) eq-cb) (⊕-assoc p (ix 1 ∷ last ∷ sub sb ∷ []) [ ix 1 ])

  sb≺e₀ : sb ≺ ((p ⊕ [ ix 1 ]) ⊕ [ last ])
  sb≺e₀ = subst₂ _≺_ (sym (pos-sb p)) (sym (⊕-assoc p [ ix 1 ] [ last ])) (≺-part p (ix 1 ∷ ix 0 ∷ ix 1 ∷ []) (last ∷ []) refl)

  sb≺cb : sb ≺ cb
  sb≺cb = subst₂ _≺_ (sym (pos-sb p)) (sym eq-cb) (≺-part p (ix 1 ∷ ix 0 ∷ ix 1 ∷ []) (last ∷ sub sb ∷ []) refl)

  q₁≺cb : (P ⊕ [ ix 1 ]) ≺ cb
  q₁≺cb = subst₂ _≺_ (sym (assoc³ p (ix 0) (ix 1) (ix 1))) (sym eq-cb) (≺-part p (ix 1 ∷ ix 1 ∷ []) (last ∷ sub sb ∷ []) refl)

  e₁≺cb : (P ⊕ [ last ]) ≺ cb
  e₁≺cb = subst₂ _≺_ (sym (assoc³ p (ix 0) (ix 1) last)) (sym eq-cb) (≺-part p (ix 1 ∷ last ∷ []) (last ∷ sub sb ∷ []) refl)

  Bk : Blocked (G true) sb cb
  Bk = blk m ρ s env (p ⊕ [ ix 1 ]) sb sb≺e₀

  -- Where the outer is subscribed: past the waiting lane's end.
  okP : Ok (Hots env′) P
  okP = ok-step (p ⊕ [ ix 0 ]) ok₀

  okb : Ok (Hots env′) sb
  okb = ok-step (P ⊕ [ ix 0 ]) (ok-in okP (InvAt.world Io (Two.o₀ P)) (InvAt.real Io (Two.o₀ P)))
    where Io = inv-⟦⟧ (of (true ∷ false ∷ [])) env′ g′ P okP

  okc : Ok (Hots env′) cb
  okc = ok-in okb (InvAt.world Ib (Blocked.bk-has Bk)) (InvAt.real Ib (Blocked.bk-has Bk))
    where Ib = inv-ev m (srcLane ρ s true) env′ g′ sb okb

  ok₁ : Ok (Hots env′) s₁
  ok₁ = ok-step cb okc

  ep₁ : Early s₁
  ep₁ = early-inst [ ix 1 ] (early-inst [ sub sb ] (early-inst [ last ] (early-inst [ ix 1 ] ep)))

  I₁ : InvAt (Hots env′) s₁ (enter (G false) s₁)
  I₁ = inv-ev m (elab (λ i → there (ρ i)) s) env′ g′ s₁ ok₁

  ex : ∀ {y} → Ex (s₁ ∷ cs) y → Ex (P ∷ p ∷ cs) y
  ex {y} (here sy) = there (here (sync-up {p} {y} (ix 1 ∷ last ∷ sub sb ∷ ix 1 ∷ []) (subst (λ z → Sync z y) eq-s₁ sy)))
  ex (there x) = there (there x)

  held : HeldD (Hots env′) (ev m (elab (λ i → there (ρ i)) s) env′) cs
       → Held (enter (Op.flatMap (mergeᶠ (just 1)) G (Op.of (true ∷ false ∷ []))) P) (P ∷ p ∷ cs)
  held hd = Cat.held G P cb Bk sb≺cb q₁≺cb e₁≺cb (λ y → world-after (InvAt.world I₁ y) (InvAt.real I₁ y))
    (λ y → proj₂ (InvAt.pinned I₁ y)) (held-ex ex (hd s₁ ok₁ ep₁))

-- A SHARED OUTER HOLDS as the outer does: the trigger's lane holds
-- nothing, and the outer is subscribed once, as the trigger ends, inside
-- the share's own burst, which the share's subscription exempts.
held-trigger : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (env : DenEnv Δ) cs p
             → GoodEnv env → Ok (Hots env) p → Early p
             → let σ₀ = Proper (enter (ev m empty env) (p ⊕ [ ix 1 ])) in
               HeldD (Hots (hot σ₀ ∷ env)) (ev m (elab (λ i → there (ρ i)) s) (hot σ₀ ∷ env)) cs
             → Held (enter (ev m (flatMap (mergeᶠ (just 1)) (λ c → srcLane ρ s c) (of (true ∷ false ∷ []))) (hot σ₀ ∷ env)) ((p ⊕ [ ix 0 ]) ⊕ [ ix 1 ]))
                    (((p ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ∷ p ∷ cs)
held-trigger nothing  ρ s env cs p g ok ep hd = Trig.held nothing ρ s env cs p g ok ep hd
held-trigger (just n) ρ s env cs p g ok ep hd = Trig.held (just n) ρ s env cs p g ok ep hd
