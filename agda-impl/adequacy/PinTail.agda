{-# OPTIONS --guardedness #-}

-- A PIN OF A BURST BEGUN BEFORE THE CURSOR lies in what the node's isles
-- still run, but for finitely many.  A pin is held by the connect that
-- subscribed it, so one whose connect the cursor has passed is held by a
-- burst begun before the cursor: an isle's, if its source is still in its
-- subscribe call; otherwise one of finitely many, its source attached.  A
-- lane's pin is of a connect at or past the lane's subscription, so a
-- lane still owed, begun or waiting, holds none such.
module adequacy.PinTail where

open import Data.Bool using (Bool; T; not; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (lookup)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; Timeline; ix; last)
open import denotation.EmissionSet using (EmissionSet; out; end; pin; _≺_; _≼_; enter; ⟦_⟧; shown; map-pin; module Scan;
  module TakeWhile; module Connecting)
open import denotation.Laws.Modulus using (≺→≼; ≺-ext; ≼-antisym)
open import denotation.Laws.Worlds using (InvAt; real-snoc; plain-ix)
open import denotation.Laws.Worlds.Leaves using (ine-pin)
open import denotation.Laws.JoinInv using (module Join)
open import denotation.Laws.BoundedInv using (module BoundedI)
open import operation.PureObservable using (module Machine)
open Machine using (St; Scope; unbound; binds; CS; takeS)
open import adequacy.Rows using (full; Frozen)
open import adequacy.Cursor using (takes; Cur; Behind; Flags; ConnE; bef; aft; Owes; Beneath; Pts; _∪ᵖ_; Burst; Held; held-dn; TailP;
  tailp; Sync; Src; Sound; NoFail; Pol; Lane; Runs; Start; Kept; polF; JoinF; JInv; Hole; Dom;
  Thru; Up; NoKill; h-live; h-end; h-kill; l-live; l-dead; Begun; none; more; Parts; joined;
  src-pend; src-on; src-shut; Torn; cov; s-cold; s-of; s-done; s-map; s-scan; s-cut; s-take;
  s-took; s-flat; s-conn; s-join; s-joinx)
open import adequacy.Cursor.Tear using (by; husk-of; src-husk; begun-husk)
open import adequacy.Cursor.Show using (flat-up-lane; pin-law)
open import adequacy.Bound using (owes?; owes-≼; starts-past; past)
open import adequacy.Few using (join-pin; kept-lane; ix0)

-- A lane's pin is of a connect at or past where the lane subscribed.
lane-pin : ∀ {Γ A B} {sc : Scope Γ} op {f : A → Obs Timeline Γ B} {O : EmissionSet A} → JInv sc f O
         → ∀ {q a k r} → O q (out a) → Lane (polF op (λ a → ⟦ f a ⟧ (full sc)) O) q a k (pin r)
         → Σ Pos λ s → Start (polF op (λ a → ⟦ f a ⟧ (full sc)) O) q a s × q ≺ s × s ≼ r
lane-pin {sc = sc} (mergeᶠ nothing) {f} ji {q} x (l , _) =
  q ++ [ ix 1 ] , refl , ≺-ext q [] , pin-law (real-snoc q plain-ix (InvAt.real (JInv.io ji) x)) (Join.LI (JInv.ok ji) (λ a → ⟦ f a ⟧ (full sc)) (JInv.fi ji) (JInv.io ji) x) l
lane-pin {sc = sc} switchᶠ {f} ji {q} x (l , _) =
  q ++ [ ix 1 ] , refl , ≺-ext q [] , pin-law (real-snoc q plain-ix (InvAt.real (JInv.io ji) x)) (Join.LI (JInv.ok ji) (λ a → ⟦ f a ⟧ (full sc)) (JInv.fi ji) (JInv.io ji) x) l
lane-pin {sc = sc} exhaustᶠ {f} ji {q} x (l , _) =
  q ++ [ ix 1 ] , refl , ≺-ext q [] , pin-law (real-snoc q plain-ix (InvAt.real (JInv.io ji) x)) (Join.LI (JInv.ok ji) (λ a → ⟦ f a ⟧ (full sc)) (JInv.fi ji) (JInv.io ji) x) l
lane-pin {sc = sc} (mergeᶠ (just m)) {f} {O} ji x (i , s , sb , l , _) =
  s , (i , sb) , starts-past m (λ a → ⟦ f a ⟧ (full sc)) O (proj₂ sb)
    , pin-law (proj₁ (BoundedI.okS (JInv.ok ji) m _ (JInv.fi ji) (JInv.io ji) sb)) (BoundedI.LI (JInv.ok ji) m _ (JInv.fi ji) (JInv.io ji) sb) l

------------------------------------------------------------------------
-- The pins

-- Every pin of `E` the cursor has not passed, of a connect it has, in
-- `P` but for finitely many.
record PinTail {A} (C : Cur) (E : EmissionSet A) (P : Pts) : Set where
  constructor ptl
  field
    pks : List Pos
    pf  : ∀ {y r} → E y (pin r) → Owes C y → ¬ Owes C r → P y ⊎ y ∈ pks

-- Each pin of `E′` a pin of `E` but for finitely many.
pt-bn : ∀ {A B} {C} {E : EmissionSet A} {X E′ : EmissionSet B} {P} → Beneath X E′ → (∀ {y r} → X y (pin r) → E y (pin r))
      → PinTail C E P → PinTail C E′ P
pt-bn (ls , g) back (ptl ks f) = ptl (ls ++ ks) λ x o no →
  [ (λ x′ → [ inj₁ , (λ i → inj₂ (∈-++⁺ʳ ls i)) ]′ (f (back x′) o no)) , (λ i → inj₂ (∈-++⁺ˡ i)) ]′ (g x)

-- Within what it still runs, but for finitely many: its pins too.
tailp-pt : ∀ {A} {C} {E : EmissionSet A} {P} → TailP C E P → PinTail C E P
tailp-pt (tailp ks f) = ptl ks λ x o _ → f x o

-- Read through a flag.
by-elim : ∀ {X : Set₁} (Q : X → Set) b (t : T b → X) (f : T (not b) → X) → (∀ x → Q (t x)) → (∀ x → Q (f x)) → Q (by b t f)
by-elim Q true  t f qt qf = qt tt
by-elim Q false t f qt qf = qf tt

-- A binder is hot: rejoined, it holds no pin.
hot-nopin : ∀ {Γ A} (sc : Scope Γ) (x : A ∈ Γ) {j y r} → enter (lookup (full sc) x) j y (pin r) → ⊥
hot-nopin unbound        ()
hot-nopin (binds o p sc) (here refl) (shown _ () _ , _)
hot-nopin (binds o p sc) (there x)   e = hot-nopin sc x e

-- In its burst.
in-burst : ∀ {Γ X} {C} {k : CS Γ X} {k′ e} → Frozen k k′ e → Held C k k′ e → Burst C k (ix0 k′)
in-burst x h = _ , (_ , x , h) , refl

SrcPT : ∀ {Γ X} → Cur → CS Γ X → Pts → Set
SrcPT C k P = Σ (List Pos) λ ks → ∀ {k′ e} → Frozen k k′ e → Held C k k′ e → Owes C (ix0 k′) → P (ix0 k′) ⊎ ix0 k′ ∈ ks

-- A dead lane's: what its hole's tail still runs.
dead-pt : ∀ {A B} {C} {P : Pol A B} {q a Ph E} → Hole C P q a Ph E false
        → Σ (List Pos) λ ks → ∀ {y r} → Kept P q a y (pin r) → Owes C y → Ph y ⊎ y ∈ ks
dead-pt (h-end _ _ (tailp ks f))  = ks , λ kp o → f kp o
dead-pt (h-kill _ _ (tailp ks f)) = ks , λ kp o → f kp o

mutual
  pin-tail : ∀ {Γ} {sc : Scope Γ} {Rg C A} {s : St Γ A} {E} (sy : Sync sc Rg C s E) → PinTail C E (proj₁ (husk-of sy))
  pin-tail (s-cold _ _ (ks , f) _) = ptl ks λ x o _ → [ (λ t → ⊥-elim (ine-pin t)) , inj₂ ]′ (f x o)
  pin-tail (s-of _ (ks , f))     = ptl ks λ x o _ → [ (λ t → ⊥-elim (ine-pin t)) , inj₂ ]′ (f x o)
  pin-tail (s-done _ (ks , f))   = ptl ks λ x o _ → inj₂ (f x o)
  pin-tail {C = C} (s-map sy m _)        = pt-bn {C = C} (cov m) (λ { (map-pin x) → x }) (pin-tail sy)
  pin-tail {C = C} (s-scan sy _ m _)     = pt-bn {C = C} (cov m) (λ { (Scan.spin x) → x }) (pin-tail sy)
  pin-tail (s-cut sy)            = pin-tail sy
  pin-tail {C = C} (s-take sy _ m _)     = pt-bn {C = C} (cov m) (λ { (TakeWhile.left x _ _) → x }) (pin-tail sy)
  pin-tail {C = C} (s-took _ _ _ _ tp _ _ _ m _) = pt-bn {C = C} (cov m) (λ x → x) (tailp-pt {C = C} tp)
  pin-tail {sc = sc} {C = C} (s-flat {op = op} {f = f} {ω = ω} {O = O} {E = E} ji sy (joined {vs} bg wa wh _ _ _ _ li _) je@(_ , m) _ bh)
    with pin-tail sy | begun-pt {O = O} {E = E} (λ {q} {a} {D} x rn dm nk → flat-up-lane {sc = sc} {C = C} {D = D} {op = op} {f = f} {ω = ω} {O = O} {E = E} {q = q} {a = a} ji je bh li x rn dm nk) bg
  ... | ptl ko fo | kl , fl = pt-bn {C = C} {E = JoinF op F O} (cov m) proj₁ (ptl (ko ++ kl) λ {y} {r} x o no → pick (join-pin op F O x) o no)
    where
      F = λ a → ⟦ f a ⟧ (full sc)
      pick : ∀ {y r} → O y (pin r) ⊎ (Σ Pos λ q → Σ _ λ a → O q (out a) × Runs (polF op F O) q × Kept (polF op F O) q a y (pin r))
           → Owes C y → ¬ Owes C r → (proj₁ (husk-of sy) ∪ᵖ proj₁ (begun-husk {O = O} {E = E} (λ {q} {a} {D} x rn dm nk → flat-up-lane {sc = sc} {C = C} {D = D} {op = op} {f = f} {ω = ω} {O = O} {E = E} {q = q} {a = a} ji je bh li x rn dm nk) bg)) y ⊎ y ∈ ko ++ kl
      pick (inj₁ x) o no = [ (λ h → inj₁ (inj₁ h)) , (λ i → inj₂ (∈-++⁺ˡ i)) ]′ (fo x o no)
      pick (inj₂ (q , a , x , ru , kp)) o no with lane-pin op ji x (kept-lane {P = polF op F O} kp)
      ... | s , st , qs , sr with owes? C q
      ...   | inj₁ oq = ⊥-elim (no (owes-≼ C (owes-≼ C oq (≺→≼ {q} {s} qs)) sr))
      ...   | inj₂ nq with wh x nq (takes (polF op F O) ru)
      ...     | inj₁ iv = [ (λ h → inj₁ (inj₂ h)) , (λ i → inj₂ (∈-++⁺ʳ ko i)) ]′ (fl iv kp o no)
      ...     | inj₂ iw = ⊥-elim (no (owes-≼ C (proj₂ (proj₂ (proj₂ (proj₁ (proj₂ (proj₂ wa)) iw))) st) sr))
  pin-tail {C = C} {E = E} (s-conn {k = k} refl pt bs bb ss tn fl ce@(m , _)) =
    by-elim (λ h → PinTail C E (proj₁ h)) (CS.srcLive k) _ _
      (λ l → pt-bn {C = C} (cov m) proj₁ (conn-pt {C = C} {k = k} (src-pt pt (ss l) (bb l) fl ce) (pin-tail (bs l))))
      (λ nl → pt-bn {C = C} (cov m) proj₁ (tailp-pt {C = C} (Torn.tl (tn nl))))
  pin-tail {sc = sc} (s-join {x = x} en _ _ _ _) =
    ptl (proj₁ (cov en)) λ e o _ → [ (λ t → ⊥-elim (hot-nopin sc x t)) , inj₂ ]′ (proj₂ (cov en) e)
  pin-tail (s-joinx _ (ks , f))  = ptl ks λ x o _ → inj₂ (f x o)

  -- A connect's pins: its body's, its burst's, and those of its source's
  -- it keeps.
  conn-pt : ∀ {Γ X B} {C} {k : CS Γ X} {β : EmissionSet B} {Ps Pb} → SrcPT C k Ps → PinTail C β Pb
          → PinTail C (Connecting.ConnT (CS.connAt k) (Frozen k) β) (Ps ∪ᵖ Pb)
  conn-pt (ks , fs) (ptl kb fb) = ptl (kb ++ ks) λ where
    (Connecting.body x) o no         → [ (λ h → inj₁ (inj₂ h)) , (λ i → inj₂ (∈-++⁺ˡ i)) ]′ (fb x o no)
    (Connecting.burst x ins) o _     → [ (λ h → inj₁ (inj₁ h)) , (λ i → inj₂ (∈-++⁺ʳ kb i)) ]′ (fs x (inj₁ ins) o)
    (Connecting.kept x _ _ _) o no   → [ (λ h → inj₁ (inj₁ h)) , (λ i → inj₂ (∈-++⁺ʳ kb i)) ]′ (fs x (inj₂ (_ , refl , no)) o)

  -- A source's: a burst begun before the cursor runs on in its isle; an
  -- attached one's is finitely many, and so are the rows the cursor passed.
  src-pt : ∀ {Γ X B} {Rg C} {k : CS Γ X} {o} {β E : EmissionSet B} (pt : Parts (CS.scope k) Rg k β) (sw : Src (CS.scope k) (Parts.Rs pt) C k o)
         (bb : Behind C β) (fl : Flags C k β) (ce : ConnE (CS.connAt k) (Frozen k) β E) → SrcPT C k (proj₁ (src-husk refl pt sw bb fl ce))
  src-pt {C = C} {k = k} _ (src-pend _ _ _ _ _ _ _ ow _) _ _ _ = [] , λ x h _ → inj₁ (in-burst {C = bef (CS.connAt k ++ [ ix 1 ])} {k = k} x (held-dn {C = C} {C′ = bef (CS.connAt k ++ [ ix 1 ])} {k = k} (λ {y} q → owes-≼ C ow q) h))
  src-pt {C = C} {k = k} _ (src-on nc sy bh sd af _ _ _) _ _ _ =
    by-elim (λ h → SrcPT C k (proj₁ h)) (CS.srcAtt k) _ _
      (λ t → let (ka , fa) = af t ; (ptl kp fp) = pin-tail sy ; (kh , fh) = bh in
             map ix0 (ka ++ (kp ++ kh)) , λ {k′} x h _ →
               [ (λ ok → [ (λ i → inj₂ (∈-map⁺ ix0 (∈-++⁺ˡ (fa x i))))
                         , (λ { (_ , refl , np) → [ (λ q → inj₁ (k′ , q , refl)) , (λ i → inj₂ (∈-map⁺ ix0 (∈-++⁺ʳ ka (∈-++⁺ˡ i)))) ]′ (fp x ok np) }) ]′ h)
               , (λ nk → inj₂ (∈-map⁺ ix0 (∈-++⁺ʳ ka (∈-++⁺ʳ kp (fh x nk))))) ]′ (owes? C k′))
      (λ _ → [] , λ x h _ → inj₁ (in-burst {C = C} {k = k} x h))
  src-pt {C = C} {k = k} _ (src-shut _ _ tp _ _ bh _ _ _ _) _ _ _ =
    by-elim (λ h → SrcPT C k (proj₁ h)) (CS.srcAtt k) _ _
      (λ _ → let (tailp kt ft) = tp ; (kh , fh) = bh in
             map ix0 (kt ++ kh) , λ {k′} x _ _ →
               [ (λ ok → [ (λ q → inj₁ (k′ , q , refl)) , (λ i → inj₂ (∈-map⁺ ix0 (∈-++⁺ˡ i))) ]′ (ft x ok))
               , (λ nk → inj₂ (∈-map⁺ ix0 (∈-++⁺ʳ kt (fh x nk)))) ]′ (owes? C k′))
      (λ _ → [] , λ x h _ → inj₁ (in-burst {C = C} {k = k} x h))

  -- A begun lane's pins.
  begun-pt : ∀ {Γ A B} {sc : Scope Γ} {Rl C} {P : Pol A B} {O E vs ls n}
             (lf : ∀ {q a D} → O q (out a) → Runs P q → Dom C D → (∀ {r} → Thru D r → NoKill P q r) → Up D (Lane P q a) C E)
             (bg : Begun sc Rl C P O vs ls n)
           → Σ (List Pos) λ ks → ∀ {q a y r} → (q , a) ∈ vs → Kept P q a y (pin r) → Owes C y → ¬ Owes C r → proj₁ (begun-husk lf bg) y ⊎ y ∈ ks
  begun-pt lf none = [] , λ ()
  begun-pt {C = C} {P = P} lf (more _ _ _ (l-live (h-live _ m _ _) sy _) bg) with pt-bn {C = C} (cov m) (λ x → x) (pin-tail sy) | begun-pt lf bg
  ... | ptl kl fl | kb , fb = kl ++ kb , λ where
    (here refl) kp o no → [ (λ h → inj₁ (inj₁ h)) , (λ i → inj₂ (∈-++⁺ˡ i)) ]′ (fl (kept-lane {P = P} kp) o no)
    (there i) kp o no   → [ (λ h → inj₁ (inj₂ h)) , (λ j → inj₂ (∈-++⁺ʳ kl j)) ]′ (fb i kp o no)
  begun-pt lf (more _ _ _ (l-dead hl _ _ _) bg) with dead-pt hl | begun-pt lf bg
  ... | kl , fl | kb , fb = kl ++ kb , λ where
    (here refl) kp o no → [ (λ h → inj₁ (inj₁ h)) , (λ i → inj₂ (∈-++⁺ˡ i)) ]′ (fl kp o)
    (there i) kp o no   → [ (λ h → inj₁ (inj₂ h)) , (λ j → inj₂ (∈-++⁺ʳ kl j)) ]′ (fb i kp o no)

------------------------------------------------------------------------
-- A NODE ENDED BEFORE THE CURSOR owes what its isles still run, but for
-- finitely many: past its end lie only pins of connects before it
-- (`Sound.past`), which the cursor has passed.
end-tail : ∀ {Γ} {sc : Scope Γ} {Rg C A} {s : St Γ A} {E} (sy : Sync sc Rg C s E) → Sound Rg E
         → ∀ {c} → E c end → ¬ Owes C c → TailP C E (proj₁ (husk-of sy))
end-tail {C = C} {E = E} sy sd {c} ce nc with pin-tail sy
... | ptl ks f = tailp ks row
  where
    row : ∀ {y e} → E y e → Owes C y → proj₁ (husk-of sy) y ⊎ y ∈ ks
    row {y} x o with Sound.past sd ce x (past C nc o)
    ... | r , refl , rc = f x o λ or → nc (owes-≼ C or (≺→≼ {r} {c} rc))

------------------------------------------------------------------------
-- A TAKEWHILE FAILING AT `p` owes what its source's isles still run.  A
-- row past the failure is at the failure itself, but for a pin it keeps
-- (`TakeWhile.left`), which is of a burst begun before the failure, so a
-- pin of its source's tail.
took-tail : ∀ {Γ} {sc : Scope Γ} {Rg} {A} {i} {keep : A → Bool} {s : St Γ A} {Es a p}
          → (sy : Sync sc Rg (aft p) s Es) → Es p (out a) → T (not (keep a)) → NoFail (bef p) keep Es
          → TailP (bef p) (TakeWhile.TakeT i keep Es) (proj₁ (husk-of sy))
took-tail {i = i} {keep = keep} {Es = Es} {p = p} sy row nk nf with pin-tail sy
... | ptl kp fp = tailp (p ∷ (p ++ [ ix 0 ]) ∷ (p ++ [ last ]) ∷ kp) λ where
    (TakeWhile.pass {q} _ _ nq) o → inj₂ (here (at q nq o))
    (TakeWhile.step {q} _ nq) o   → inj₂ (here (at q nq o))
    (TakeWhile.tend {q} _ nq) o   → inj₂ (here (at q nq o))
    (TakeWhile.fail {q} x nkq nq _) _ → inj₂ (there (here (cong (_++ [ ix 0 ]) (at q nq (nf x nkq)))))
    (TakeWhile.stop {q} x nkq nq) _   → inj₂ (there (there (here (cong (_++ [ last ]) (at q nq (nf x nkq))))))
    (TakeWhile.left {q} {r} x nr _) o → [ (λ pq → [ inj₁ , (λ j → inj₂ (there (there (there j)))) ]′ (fp x pq (λ pr → nr (_ , _ , row , nk , pr))))
                                        , (λ npq → inj₂ (here (≼-antisym {q} {p} npq o))) ]′ (owes? (aft p) q)
  where
    at : ∀ q → ¬ TakeWhile.Failed i keep Es q → p ≼ q → q ≡ p
    at q nq o = ≼-antisym {q} {p} (λ pq → nq (_ , _ , row , nk , pq)) o
