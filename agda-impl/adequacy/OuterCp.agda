{-# OPTIONS --guardedness #-}

-- AN OUTER'S END, SHOWN ONLY WITH NO LANE RUNNING OR WAITING: the outer
-- rises its end owing nothing else, and the joiner, marked done, rises its
-- own end exactly when no lane is live and none waits.  Every begun lane
-- lies strictly past the end, so the two readings of the joiner agree but
-- for a skip there, where the first owes its own end exactly when it is
-- done.  One step for every joiner, read by its policy.
module adequacy.OuterCp where

open import Data.Bool using (Bool; true; false; T; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Relation.Unary.All using ([])
open import Data.List using (List; []; _∷_; null; length)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; Timeline)
open import denotation.EmissionSet using (EmissionSet; Ended; out; end; module Joining; _≼_; DenEnv; Truncate)
open import denotation.Laws.Modulus using (≼-refl)
open import operation.Key using (at)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; ⟨_,_,_,_⟩; Mode; plug; absorbed; rising; cp; alive; settle; flatS; inOuter)
open import adequacy.Rows using (env; up; here; rows; rowsL; pendRows; Plus; old; new; Lanes; Each; AllEnd; EndsOf; module Flat; module SwitchF; module BoundedF;
  _≃_; ≃-sym; Moves; silent)
open import adequacy.Up using (up-≃; ≃-trans; vis-≃; plus-≃)
open import adequacy.Bound using (Empty; Good; G; From; ⊑-refl; MergeG; dead-empty)
open import adequacy.Skip using (After; Since; LeadC; _≈⟨_⟩_; _⇆_; Skip; after-since; since-lanes; since-join; up-vis; trunc-≈)
open import adequacy.Policy using (Policy; JoinP; DoneP; polOf; flatP; switchP; exhaustP; boundedP)
open import adequacy.Flags using (flat-flags; switch-flags; exhaust-flags; bounded-flags; queued-flags)
open import adequacy.LaneCp using (rows-flat; pol-empty; trunc-plus)
open import adequacy.Swap using (≡→≃)
open import adequacy.Inv using (Inv; inv; Sim; UpO; open-alive; node-good; upo-liv)

open Policy

------------------------------------------------------------------------
-- The frame

-- What two readings of a joiner past `p` share, the first's outer owing
-- only its end at `p` and the second's nothing.
record OuterAt {A B : Set} (PX PY : Policy A B) (p : Pos) : Set where
  field
    ox  : ∀ {q e} → outer PX q e → q ≡ p × e ≡ end
    oy  : ∀ {q e} → ¬ outer PY q e
    oat : outer PX p end
    sb  : Since p (begun PX)
    ha→ : ∀ {c} → p ≼ c → hand PX c → hand PY c
    ha← : ∀ {c} → p ≼ c → hand PY c → hand PX c
    dn→ : ∀ {c} → p ≼ c → DoneP PX c → DoneP PY c
    dn← : ∀ {c} → p ≼ c → DoneP PY c → DoneP PX c
    bg→ : ∀ {k e} → begun PX k e → begun PY k e
    bg← : ∀ {k e} → begun PY k e → begun PX k e

module OFrame {A B : Set} {PX PY : Policy A B} {p : Pos} (E : OuterAt PX PY p) where
  open OuterAt E

  nv : ∀ {q a} → ¬ outer PX q (out a)
  nv r with ox r
  ... | _ , ()

  -- THE FRAME: the joiner read as `Y′`, which owes `JoinP PY` and at most
  -- the joiner's own end at `p`.
  module _ (Y′ : EmissionSet B) (dp : DoneP PX p → Y′ p end) (y→ : ∀ {k e} → JoinP PY k e → Y′ k e)
           (y← : ∀ {k e} → Y′ k e → JoinP PY k e ⊎ (k ≡ p × e ≡ end × DoneP PX p)) where

    fwd′ : ∀ {k e} → JoinP PX k e → Y′ k e ⊎ Skip p k e
    fwd′ (Joining.val r)             = ⊥-elim (nv r)
    fwd′ (Joining.step r) with ox r
    ... | _ , ()
    fwd′ (Joining.opin r) with ox r
    ... | _ , ()
    fwd′ (Joining.oend r d) with ox r
    ... | refl , _ = inj₁ (dp d)
    fwd′ (Joining.opass r _) with ox r
    ... | refl , _ = inj₂ (refl , refl)
    fwd′ (Joining.lane r _ _ _ _)    = ⊥-elim (nv r)
    fwd′ (Joining.lend r _ _ _ _ _)  = ⊥-elim (nv r)
    fwd′ (Joining.lpass r _ _ _ _ _) = ⊥-elim (nv r)
    fwd′ (Joining.hand r _ _ _ _)    = ⊥-elim (nv r)
    fwd′ (Joining.left r _ _ _ _)    = ⊥-elim (nv r)
    fwd′ (Joining.run x w)           = inj₁ (y→ (Joining.run (bg→ x) w))
    fwd′ (Joining.rend x nh d)       = inj₁ (y→ (Joining.rend (bg→ x) (λ h → nh (ha← (sb x) h)) (dn→ (sb x) d)))
    fwd′ (Joining.rpass x nh nd)     = inj₁ (y→ (Joining.rpass (bg→ x) (λ h → nh (ha← (sb x) h)) λ d → nd (dn← (sb x) d)))
    fwd′ (Joining.rhand x h)         = inj₁ (y→ (Joining.rhand (bg→ x) (ha→ (sb x) h)))

    back : ∀ {k e} → JoinP PY k e → JoinP PX k e
    back (Joining.val r)             = ⊥-elim (oy r)
    back (Joining.step r)            = ⊥-elim (oy r)
    back (Joining.opin r)            = ⊥-elim (oy r)
    back (Joining.oend r _)          = ⊥-elim (oy r)
    back (Joining.opass r _)         = ⊥-elim (oy r)
    back (Joining.lane r _ _ _ _)    = ⊥-elim (oy r)
    back (Joining.lend r _ _ _ _ _)  = ⊥-elim (oy r)
    back (Joining.lpass r _ _ _ _ _) = ⊥-elim (oy r)
    back (Joining.hand r _ _ _ _)    = ⊥-elim (oy r)
    back (Joining.left r _ _ _ _)    = ⊥-elim (oy r)
    back (Joining.run x w)           = Joining.run (bg← x) w
    back (Joining.rend x nh d)       = Joining.rend (bg← x) (λ h → nh (ha→ (sb (bg← x)) h)) (dn← (sb (bg← x)) d)
    back (Joining.rpass x nh nd)     = Joining.rpass (bg← x) (λ h → nh (ha→ (sb (bg← x)) h)) λ d → nd (dn→ (sb (bg← x)) d)
    back (Joining.rhand x h)         = Joining.rhand (bg← x) (ha← (sb (bg← x)) h)

    bwd′ : ∀ {k e} → Y′ k e → JoinP PX k e ⊎ Skip p k e
    bwd′ r with y← r
    ... | inj₁ r′                = inj₁ (back r′)
    ... | inj₂ (refl , refl , d) = inj₁ (Joining.oend oat d)

    oframe-≈ : JoinP PX ≈⟨ p ⟩ Y′
    oframe-≈ = fwd′ ⇆ bwd′

  since-x : Since p (JoinP PX)
  since-x = since-join PX so sb (λ r _ → ⊥-elim (nv r))
    where
      so : Since p (outer PX)
      so r with ox r
      ... | refl , _ = ≼-refl {p}

  since-y : Since p (JoinP PY)
  since-y = since-join PY (λ r → ⊥-elim (oy r)) (λ x → sb (bg← x)) (λ r _ → ⊥-elim (oy r))

------------------------------------------------------------------------
-- Each joiner's two readings

postulate
  -- A BOUNDED MERGE'S TWO READINGS PAST ITS OUTER'S END: with no outer
  -- value left, each queued value's schedule, its start and its hand-off
  -- read alike whether or not the outer is marked done.
  bounded-outer-at : ∀ {A B} m (L : A → Pos → EmissionSet B) {p O d n} Qu (Ls : List (EmissionSet B))
                   → Empty O → Each (After p) Ls
                   → OuterAt (boundedP m L (Plus O p end) d n Qu Ls) (boundedP m L O true n Qu Ls) p

-- A bounded merge's live or waiting lanes end past `p`: not over there.
bounded-unover : ∀ {A B} m (L : A → Pos → EmissionSet B) O d n Qu (Ls : List (EmissionSet B)) {p k}
               → From (at p) O → Each (After p) Ls → n + length Qu ≡ suc k → ¬ BoundedF.Over m L O d n Qu Ls p
bounded-unover m L O d n []      Ls {p} fo al nk ov =
  subst (λ x → T (x ≡ᵇ 0)) (trans (sym (+-identityʳ n)) nk) (proj₂ (proj₂ (bounded-flags m L O d n Ls)) {p} fo al ov)
bounded-unover m L O d n (a ∷ q) Ls {p} fo al nk ov = queued-flags m L O d n a q Ls {p} fo al ov

module _ {A B : Set} (L : A → Pos → EmissionSet B) {p : Pos} {O : EmissionSet A} {d : Bool} {n : ℕ} (Qu : List A) (Ls : List (EmissionSet B))
         (eo : Empty O) (al : Each (After p) Ls) where

  OX = Plus O p end

  PX PY : FlatOp → Policy A B
  PX op = polOf op L OX d n Qu Ls
  PY op = polOf op L O true n Qu Ls

  ox : ∀ {q e} → OX q e → q ≡ p × e ≡ end
  ox (old r) = ⊥-elim (eo r)
  ox new     = refl , refl

  sb : Since p (Lanes Ls)
  sb = since-lanes Ls (after-since Ls al)

  fo : From (at p) OX
  fo (old r) = ⊥-elim (eo r)
  fo new     = ⊑-refl (at p)

  ended : ∀ {c} → p ≼ c → Ended OX c
  ended {c} pc = _ , new , pc

  merge-at : OuterAt (flatP L OX d n Ls) (flatP L O true n Ls) p
  merge-at = record
    { ox = ox ; oy = eo ; oat = new ; sb = sb ; ha→ = λ _ () ; ha← = λ _ () ; bg→ = λ x → x ; bg← = λ x → x
    ; dn→ = λ { _ (Flat.over-at _ ls , _) → Flat.over-at (inj₁ tt) ls , λ r → ⊥-elim (eo r) }
    ; dn← = λ { {c} pc (Flat.over-at _ ls , _) → Flat.over-at (inj₂ (ended {c} pc)) ls , λ { (old r) → ⊥-elim (eo r) } } }

  kx : ∀ {k} → ¬ SwitchF.Kill L OX d n Ls k
  kx (_ , _ , old r , _) = eo r

  ky : ∀ {k} → ¬ SwitchF.Kill L O true n Ls k
  ky (_ , _ , r , _) = eo r

  sw-bg→ : ∀ {k e} → SwitchF.Bg L OX d n Ls k e → SwitchF.Bg L O true n Ls k e
  sw-bg→ (SwitchF.bg x _)     = SwitchF.bg x ky
  sw-bg→ (SwitchF.bpin x _ i) = SwitchF.bpin x ky i

  sw-bg← : ∀ {k e} → SwitchF.Bg L O true n Ls k e → SwitchF.Bg L OX d n Ls k e
  sw-bg← (SwitchF.bg x _)     = SwitchF.bg x kx
  sw-bg← (SwitchF.bpin x _ i) = SwitchF.bpin x kx i

  sw-sb : Since p (SwitchF.Bg L OX d n Ls)
  sw-sb (SwitchF.bg x _)     = sb x
  sw-sb (SwitchF.bpin x _ _) = sb x

  switch-at : OuterAt (switchP L OX d n Ls) (switchP L O true n Ls) p
  switch-at = record
    { ox = ox ; oy = eo ; oat = new ; sb = sw-sb ; ha→ = λ _ () ; ha← = λ _ () ; bg→ = sw-bg→ ; bg← = sw-bg←
    ; dn→ = λ { _ ((_ , inj₁ ls) , _) → (inj₁ tt , inj₁ ls) , λ r → ⊥-elim (eo r)
              ; _ ((_ , inj₂ k) , _)  → ⊥-elim (kx k) }
    ; dn← = λ { {c} pc ((_ , inj₁ ls) , _) → (inj₂ (ended {c} pc) , inj₁ ls) , λ { (old r) → ⊥-elim (eo r) }
              ; _ ((_ , inj₂ k) , _)   → ⊥-elim (ky k) } }

  exhaust-at : OuterAt (exhaustP L OX d n Ls) (exhaustP L O true n Ls) p
  exhaust-at = record
    { ox = ox ; oy = eo ; oat = new ; sb = sb ; ha→ = λ _ () ; ha← = λ _ () ; bg→ = λ x → x ; bg← = λ x → x
    ; dn→ = λ { _ ((_ , ls) , _) → (inj₁ tt , ls) , λ r → ⊥-elim (eo r) }
    ; dn← = λ { {c} pc ((_ , ls) , _) → (inj₂ (ended {c} pc) , ls) , λ { (old r) → ⊥-elim (eo r) } } }

  -- The joiner's two readings past `p`, its outer's end at `p`.
  outer-at : ∀ op → OuterAt (PX op) (PY op) p
  outer-at (mergeᶠ nothing)  = merge-at
  outer-at (mergeᶠ (just m)) = bounded-outer-at m L Qu Ls eo al
  outer-at switchᶠ           = switch-at
  outer-at exhaustᶠ          = exhaust-at

  none : n ≡ 0 → AllEnd (_≼ p) n (EndsOf Ls)
  none nz = subst (λ k → AllEnd (_≼ p) k (EndsOf Ls)) (sym nz) tt

  -- No lane live and none waiting: the joiner done at `p`.
  done-at : ∀ op → n ≡ 0 → Qu ≡ [] → DoneP (PX op) p
  done-at (mergeᶠ nothing)  nz _  = Flat.over-at (inj₂ (ended {p} (≼-refl {p}))) (none nz) , λ { (old r) → ⊥-elim (eo r) }
  done-at (mergeᶠ (just m)) nz qz = (inj₂ (ended {p} (≼-refl {p})) , subst (λ k → AllEnd (_≼ p) k (BoundedF.Sched m L OX d n Qu Ls (length Qu))) (sym (cong₂ _+_ nz (cong length qz))) tt)
                                  , λ { (old r) → ⊥-elim (eo r) }
  done-at switchᶠ           nz _  = (inj₂ (ended {p} (≼-refl {p})) , inj₁ (none nz)) , λ { (old r) → ⊥-elim (eo r) }
  done-at exhaustᶠ          nz _  = (inj₂ (ended {p} (≼-refl {p})) , none nz) , λ { (old r) → ⊥-elim (eo r) }

  -- A lane live: not done at `p`, every lane ending past it.
  owes-n : ∀ op {k} → n ≡ suc k → ¬ DoneP (PX op) p
  owes-n (mergeᶠ nothing)  nk (ov , _) = subst (λ x → T (x ≡ᵇ 0)) nk (proj₂ (proj₂ (flat-flags L OX d n Ls)) {p} fo al ov)
  owes-n (mergeᶠ (just m)) nk (ov , _) = bounded-unover m L OX d n Qu Ls fo al (cong (_+ length Qu) nk) ov
  owes-n switchᶠ           nk (ov , _) = subst (λ x → T (x ≡ᵇ 0)) nk (proj₂ (proj₂ (switch-flags L OX d n Ls)) {p} fo al ov)
  owes-n exhaustᶠ          nk (ov , _) = subst (λ x → T (x ≡ᵇ 0)) nk (proj₂ (proj₂ (exhaust-flags L OX d n Ls)) {p} fo al ov)

  -- A value waiting: not done at `p`.
  owes-q : ∀ m {a q′} → Qu ≡ a ∷ q′ → ¬ DoneP (PX (mergeᶠ (just m))) p
  owes-q m {a} {q′} qz (ov , _) = subst (λ Q → ¬ BoundedF.Over m L OX d n Q Ls p) (sym qz) (queued-flags m L OX d n a q′ Ls {p} fo al) ov

------------------------------------------------------------------------
-- The step

postulate
  -- AN OUTER'S END, THE TREE STILL GOOD: the joiner marked done over an
  -- outer owing nothing, every node above stays good reading the
  -- joiner's rows, which may now end where its last lane does.  The
  -- joiner's own node is direct; open is each frame above, whose facts
  -- read those rows.
  good-outer-end : ∀ {R Γ A B} op (f : A → Obs Timeline Γ B) n q (o : St Γ A) ls (c : Ctx R Γ B)
                 → Empty (rows (env c) o)
                 → Good [] (plug c (flatS op f false n q o ls))
                 → Good [] (plug c (flatS op f true n q o ls))

  -- A DONE JOINER'S OUTER ENDING AGAIN: absorbed.  False against `Inv` as
  -- it stands: the joiner, marked done with no lane live and none
  -- waiting, is done at the end's position, so the rows before the step
  -- owe its end there and the rows after owe none.  Such a joiner has
  -- already risen its end, and the frame that took it is, as the machine
  -- runs, closed or above the program's end; `Inv` says neither of a done
  -- joiner, so nothing stops its outer rising.  Settled by an invariant
  -- tying a done joiner to its frame above, or a program whose done
  -- joiner's outer ends.
  rise-joiner-cp-spent : ∀ {R Γ A B} op (f : A → Obs Timeline Γ B) ls (c : Ctx R Γ B) (o : St Γ A) p
                       → Sim ⟨ inOuter op f true 0 [] ls c , o , rising cp , p ⟩ [] ⟨ c , flatS op f true 0 [] o ls , absorbed , p ⟩

-- The joiner marked done.
good-mark : ∀ {R Γ A B} op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls (c : Ctx R Γ B)
          → Empty (rows (env c) o) → Good [] (plug c (flatS op f d n q o ls)) → Good [] (plug c (flatS op f true n q o ls))
good-mark op f false n q o ls c eo g = good-outer-end op f n q o ls c eo g
good-mark op f true  n q o ls c eo g = g

-- A done joiner, no lane live and none waiting, apart.
by-spent : ∀ {A : Set} (P : Bool → ℕ → List A → Set₁) → P true 0 [] → (∀ d n q → (T d → n ≡ 0 → q ≡ [] → ⊥) → P d n q) → ∀ d n q → P d n q
by-spent P s k true  zero    []      = s
by-spent P s k false n       q       = k false n q λ ()
by-spent P s k true  (suc n) q       = k true (suc n) q λ _ ()
by-spent P s k true  zero    (a ∷ q) = k true zero (a ∷ q) λ _ _ ()

module Ocp {R Γ A B} (op : FlatOp) (f : A → Obs Timeline Γ B) (d : Bool) (n : ℕ) (q : List A) (o : St Γ A) (ls : List (St Γ B)) (c : Ctx R Γ B) (p : Pos)
           (g′ : Good [] (plug c (flatS op f true n q o ls)))
           (uc : UpO c) (al : Each (After p) (rowsL (env c) ls)) (lc : LeadC c p) (eo : Empty (rows (env c) o))
           (el : n ≡ 0 → Each Empty (rowsL (env c) ls))
           (nq : ∀ {a q′} → q ≡ a ∷ q′ → ¬ DoneP (polOf op (λ x → pendRows (env c) (f x)) (Plus (rows (env c) o) p end) d n q (rowsL (env c) ls)) p)
           (sp : T d → n ≡ 0 → q ≡ [] → ⊥) where

  ρ : DenEnv Γ
  ρ = env c

  L  = λ x → pendRows ρ (f x)
  O  = rows ρ o
  Ls = rowsL ρ ls
  PJ = polOf op L (Plus O p end) d n q Ls
  Y  = JoinP (polOf op L O true n q Ls)
  E  = outer-at L {p} {O} {d} {n} q Ls eo al op

  node : St Γ B
  node = flatS op f true n q o ls

  rowsY : rows ρ node ≃ Truncate Y
  rowsY = ≡→≃ (rows-flat ρ op f true n q o ls)

  sx = OFrame.since-x E
  sy = OFrame.since-y E

  Out : Mode B → Set₁
  Out m = Inv ⟨ c , node , m , p ⟩ × Moves (up c (Truncate (JoinP PJ))) [] (up c (here ρ node m p))

  pass : ¬ DoneP PJ p → Out absorbed
  pass nd = inv g′ tt
          , silent (≃-trans (up-vis c lc (λ (r , _) → sx r) (λ (r , _) → sy r) skip) (vis-≃ (up-≃ c (≃-sym rowsY))))
    where skip = trunc-≈ (OFrame.oframe-≈ E Y (λ dn → ⊥-elim (nd dn)) (λ r → r) inj₁)

  done : n ≡ 0 → q ≡ [] → Out (rising cp)
  done nz qz = inv g′ (uc , lc , tt , (λ r → ⊥-elim (empty-node r)) , empty-node)
             , silent (≃-trans (up-vis c lc (λ (r , _) → sx r) (λ (r , _) → since′ r) skip) (vis-≃ (up-≃ c to-node)))
    where
      D = done-at L {p} {O} {d} {n} q Ls eo al op nz qz
      empty-y : Empty Y
      empty-y = subst (λ Q → Empty (JoinP (polOf op L O true n Q Ls))) (sym qz) (pol-empty op L {O} true n Ls eo (el nz))
      empty-node : Empty (rows ρ node)
      empty-node r = empty-y (proj₁ (_≃_.to rowsY r))
      back : ∀ {k e} → Plus Y p end k e → Y k e ⊎ (k ≡ p × e ≡ end × DoneP PJ p)
      back (old r) = inj₁ r
      back new     = inj₂ (refl , refl , D)
      since′ : Since p (Plus Y p end)
      since′ (old r) = sy r
      since′ new     = ≼-refl {p}
      skip    = trunc-≈ (OFrame.oframe-≈ E (Plus Y p end) (λ _ → new) old back)
      to-node = ≃-trans (trunc-plus sy) (plus-≃ (≃-sym rowsY))

  pick : ∀ b → d ≡ b → ∀ k → n ≡ k → ∀ Q → q ≡ Q → Out (if b then absorbed else settle true k (null Q))
  pick true  db zero    nk []      qQ = ⊥-elim (sp (subst T (sym db) tt) nk qQ)
  pick true  db zero    nk (_ ∷ _) qQ = pass (nq qQ)
  pick true  db (suc k) nk _       qQ = pass (owes-n L {p} {O} {d} {n} q Ls eo al op nk)
  pick false db zero    nk []      qQ = done nk qQ
  pick false db zero    nk (_ ∷ _) qQ = pass (nq qQ)
  pick false db (suc k) nk _       qQ = pass (owes-n L {p} {O} {d} {n} q Ls eo al op nk)

  result : Out (if d then absorbed else settle true n (null q))
  result = pick d refl n refl q refl

nil≢ : ∀ {A : Set} {a : A} {q} → [] ≡ a ∷ q → ⊥
nil≢ ()

-- A MERGE'S OUTER END, SHOWN ONLY WITH NO LANE RUNNING.
merge-cp : ∀ {R Γ A B} f d n q ls (c : Ctx R Γ B) (o : St Γ A) p → (T d → n ≡ 0 → q ≡ [] → ⊥)
         → Sim ⟨ inOuter (mergeᶠ nothing) f d n q ls c , o , rising cp , p ⟩ [] ⟨ c , flatS (mergeᶠ nothing) f true n q o ls , (if d then absorbed else settle true n (null q)) , p ⟩
merge-cp f d n q ls c o p sp i with alive o in al
merge-cp f d n q ls c o p sp (inv g (_ , _ , op′ , _)) | false = ⊥-elim (open-alive o op′ al)
merge-cp f d n q ls c o p sp (inv g (u , (als , lc) , _ , _ , es)) | true
  with subst (λ v → G (env c) v (flatS (mergeᶠ nothing) f d n q o ls)) (upo-liv c u) (node-good c (flatS (mergeᶠ nothing) f d n q o ls) g (λ ()) (λ ()))
... | mg = Ocp.result (mergeᶠ nothing) f d n q o ls c p (good-mark (mergeᶠ nothing) f d n q o ls c es g) u als lc es
                      (λ z → dead-empty ls (MergeG.lanesG mg) (trans (sym (MergeG.count mg)) z))
                      (λ qz _ → nil≢ (trans (sym (MergeG.fresh mg)) qz)) sp

rise-outer-cp : ∀ {R Γ A B} f d n q ls (c : Ctx R Γ B) (o : St Γ A) p
              → Sim ⟨ inOuter (mergeᶠ nothing) f d n q ls c , o , rising cp , p ⟩ [] ⟨ c , flatS (mergeᶠ nothing) f true n q o ls , (if d then absorbed else settle true n (null q)) , p ⟩
rise-outer-cp f d n q ls c o p =
  by-spent (λ d n q → Sim ⟨ inOuter (mergeᶠ nothing) f d n q ls c , o , rising cp , p ⟩ [] ⟨ c , flatS (mergeᶠ nothing) f true n q o ls , (if d then absorbed else settle true n (null q)) , p ⟩)
           (rise-joiner-cp-spent (mergeᶠ nothing) f ls c o p) (λ d n q → merge-cp f d n q ls c o p) d n q

-- A BOUNDED MERGE'S OUTER END, SHOWN ONLY WITH NO LANE RUNNING OR WAITING.
bounded-cp : ∀ {R Γ A B} m f d n q ls (c : Ctx R Γ B) (o : St Γ A) p → (T d → n ≡ 0 → q ≡ [] → ⊥)
           → Sim ⟨ inOuter (mergeᶠ (just m)) f d n q ls c , o , rising cp , p ⟩ [] ⟨ c , flatS (mergeᶠ (just m)) f true n q o ls , (if d then absorbed else settle true n (null q)) , p ⟩
bounded-cp m f d n q ls c o p sp i with alive o in al
bounded-cp m f d n q ls c o p sp (inv g (_ , _ , op′ , _)) | false = ⊥-elim (open-alive o op′ al)
bounded-cp m f d n q ls c o p sp (inv g (u , (als , lc) , _ , _ , es)) | true
  with subst (λ v → G (env c) v (flatS (mergeᶠ (just m)) f d n q o ls)) (upo-liv c u) (node-good c (flatS (mergeᶠ (just m)) f d n q o ls) g (λ ()) (λ ()))
... | mg , _ = Ocp.result (mergeᶠ (just m)) f d n q o ls c p (good-mark (mergeᶠ (just m)) f d n q o ls c es g) u als lc es
                          (λ z → dead-empty ls (MergeG.lanesG mg) (trans (sym (MergeG.count mg)) z))
                          (owes-q (λ x → pendRows (env c) (f x)) {p} {rows (env c) o} {d} {n} q (rowsL (env c) ls) es als m) sp

rise-bounded-cp : ∀ {R Γ A B} m f d n q ls (c : Ctx R Γ B) (o : St Γ A) p
                → Sim ⟨ inOuter (mergeᶠ (just m)) f d n q ls c , o , rising cp , p ⟩ [] ⟨ c , flatS (mergeᶠ (just m)) f true n q o ls , (if d then absorbed else settle true n (null q)) , p ⟩
rise-bounded-cp m f d n q ls c o p =
  by-spent (λ d n q → Sim ⟨ inOuter (mergeᶠ (just m)) f d n q ls c , o , rising cp , p ⟩ [] ⟨ c , flatS (mergeᶠ (just m)) f true n q o ls , (if d then absorbed else settle true n (null q)) , p ⟩)
           (rise-joiner-cp-spent (mergeᶠ (just m)) f ls c o p) (λ d n q → bounded-cp m f d n q ls c o p) d n q

-- A SWITCH'S OUTER END, SHOWN ONLY WITH NO LANE RUNNING.
switch-cp : ∀ {R Γ A B} f d n q ls (c : Ctx R Γ B) (o : St Γ A) p → (T d → n ≡ 0 → q ≡ [] → ⊥)
          → Sim ⟨ inOuter switchᶠ f d n q ls c , o , rising cp , p ⟩ [] ⟨ c , flatS switchᶠ f true n q o ls , (if d then absorbed else settle true n (null q)) , p ⟩
switch-cp f d n q ls c o p sp i with alive o in al
switch-cp f d n q ls c o p sp (inv g (_ , _ , op′ , _)) | false = ⊥-elim (open-alive o op′ al)
switch-cp f d n q ls c o p sp (inv g (u , (als , lc) , _ , _ , es)) | true
  with subst (λ v → G (env c) v (flatS switchᶠ f d n q o ls)) (upo-liv c u) (node-good c (flatS switchᶠ f d n q o ls) g (λ ()) (λ ()))
... | mg = Ocp.result switchᶠ f d n q o ls c p (good-mark switchᶠ f d n q o ls c es g) u als lc es
                      (λ z → dead-empty ls (MergeG.lanesG mg) (trans (sym (MergeG.count mg)) z))
                      (λ qz _ → nil≢ (trans (sym (MergeG.fresh mg)) qz)) sp

rise-switch-cp : ∀ {R Γ A B} f d n q ls (c : Ctx R Γ B) (o : St Γ A) p
               → Sim ⟨ inOuter switchᶠ f d n q ls c , o , rising cp , p ⟩ [] ⟨ c , flatS switchᶠ f true n q o ls , (if d then absorbed else settle true n (null q)) , p ⟩
rise-switch-cp f d n q ls c o p =
  by-spent (λ d n q → Sim ⟨ inOuter switchᶠ f d n q ls c , o , rising cp , p ⟩ [] ⟨ c , flatS switchᶠ f true n q o ls , (if d then absorbed else settle true n (null q)) , p ⟩)
           (rise-joiner-cp-spent switchᶠ f ls c o p) (λ d n q → switch-cp f d n q ls c o p) d n q

-- AN EXHAUST'S OUTER END, SHOWN ONLY WITH NO LANE RUNNING.
exhaust-cp : ∀ {R Γ A B} f d n q ls (c : Ctx R Γ B) (o : St Γ A) p → (T d → n ≡ 0 → q ≡ [] → ⊥)
           → Sim ⟨ inOuter exhaustᶠ f d n q ls c , o , rising cp , p ⟩ [] ⟨ c , flatS exhaustᶠ f true n q o ls , (if d then absorbed else settle true n (null q)) , p ⟩
exhaust-cp f d n q ls c o p sp i with alive o in al
exhaust-cp f d n q ls c o p sp (inv g (_ , _ , op′ , _)) | false = ⊥-elim (open-alive o op′ al)
exhaust-cp f d n q ls c o p sp (inv g (u , (als , lc) , _ , _ , es)) | true
  with subst (λ v → G (env c) v (flatS exhaustᶠ f d n q o ls)) (upo-liv c u) (node-good c (flatS exhaustᶠ f d n q o ls) g (λ ()) (λ ()))
... | mg = Ocp.result exhaustᶠ f d n q o ls c p (good-mark exhaustᶠ f d n q o ls c es g) u als lc es
                      (λ z → dead-empty ls (MergeG.lanesG mg) (trans (sym (MergeG.count mg)) z))
                      (λ qz _ → nil≢ (trans (sym (MergeG.fresh mg)) qz)) sp

rise-exhaust-cp : ∀ {R Γ A B} f d n q ls (c : Ctx R Γ B) (o : St Γ A) p
                → Sim ⟨ inOuter exhaustᶠ f d n q ls c , o , rising cp , p ⟩ [] ⟨ c , flatS exhaustᶠ f true n q o ls , (if d then absorbed else settle true n (null q)) , p ⟩
rise-exhaust-cp f d n q ls c o p =
  by-spent (λ d n q → Sim ⟨ inOuter exhaustᶠ f d n q ls c , o , rising cp , p ⟩ [] ⟨ c , flatS exhaustᶠ f true n q o ls , (if d then absorbed else settle true n (null q)) , p ⟩)
           (rise-joiner-cp-spent exhaustᶠ f ls c o p) (λ d n q → exhaust-cp f d n q ls c o p) d n q
