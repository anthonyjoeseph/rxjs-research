{-# OPTIONS --guardedness #-}

-- A LANE SHOWS ITS BURST'S END OR ITS `laneDone` IN ITS START'S INSTANT
-- (`burst-next`).  The lane's take either fails before its burst part's
-- `burstEnd`, and its first failing value is its `laneDone`, past its
-- `laneStart` and below the `burstEnd`; or it fails nowhere before it,
-- and the parts' merge, which shows its hangs, has the `burstEnd` among
-- its rows, every row before it being a row of the lane, and so of the
-- lanes the scan's source reads.  Either row is a row of the real
-- flatMap: no end of it comes first, since an uncut running lane shows
-- its `laneDone` before that end, and a switch cuts no row under the
-- lane's subscription (`ro-nest`).
--
-- The lanes' rows before a source value's instant are few
-- (`sent-few`): the source shows each at most a step down before that
-- value, and the source's own rows before it are few.
module simultaneous.HeldBurst where

open import Data.Bool using (Bool; true; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
import Data.List as L
open import Data.List.Properties using (reverse-++; reverse-involutive)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-concat⁺′)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; s≤s; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; connected; of)
open import denotation.Position using (Pos; Label; ix; sub; last; root; _≟ᵖ_; _⊕_; _∙_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Den; DenEnv; Ev; hot; enter; out; end; skip; pin; Few; Work; Superseded;
  _≺_; _≼_; at-out; on-out; module Op; module Merge)
open import denotation.Laws.Modulus using (entered-few; ≺-trans; ≺-ext; ≺-≼-≺; ≼-≺-≺; ≺→≼; ≼-or-≻; ≼-split; ≺-irrefl; ≼-refl; ≺-absurd)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; Lawful; Shows; InvAt; InvD; ok-step; world-after)
open import denotation.Laws.Worlds.Leaves using (of-inv)
open import denotation.Laws.Shows using (Step; k-shows; shows-k; few-via; few-reach; ∈-stable)
open import denotation.Laws.ShowsOps using (sk-of)
import denotation.Laws.ShowsJoin as SJ
open import denotation.Laws.Lift using (few-lift)
open import adequacy.SubOne using (below-or-under)
open import simultaneous.SObs using (lone; module Elaborate; laneB; Part; lanePart; burstPart)
open import simultaneous.InstEmit using (instEmit; mark; laneStart; laneDone; burstEnd; valuesOf)
open import simultaneous.Routed using (Held; Early; Placed)
open import simultaneous.HeldBase using (EnvHeld; module FlatHots; IH; Fresh; shows-ev)
open import simultaneous.HeldComb using (ev)
open import simultaneous.LaneLocal using (inv-ev)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Instants using (_≺ⁱ_; instant-≺; irrⁱ; triⁱ; transⁱ)
open import simultaneous.TakeCut using (inst-⊕)
open import simultaneous.DenRows using (merge-out)
open import simultaneous.RealView using (module View; lane-at; lane-fwd; join-in; join-shows; cutat-up)
open import simultaneous.HeldTake using (module TakeBack)
open import simultaneous.HeldLanes using (module CombLanes; lane-once)
open import simultaneous.HeldLaneRoutes using (module LaneRoutes; cut-switch)
open import simultaneous.HeldSrc using (module CombSrc)
open import simultaneous.LaneLayers using (Under; done-of; under-⊕; under-refl; under-trans; under-ext; under-≺; under-last)
import simultaneous.LaneStart as LaneStart
open import simultaneous.LaneStart using (laneAt)
import simultaneous.BurstFew as BurstFew

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; laneSrc; laneˢ; shareˢ; counted; framed; undone; Input; each)

------------------------------------------------------------------------
-- Positions and instants

-- A position's parent.
up1 : Pos → Pos
up1 (i ∙ ls) = i ∙ L.reverse (L.drop 1 (L.reverse ls))

up1-⊕ : ∀ x l → up1 (x ⊕ [ l ]) ≡ x
up1-⊕ (i ∙ ls) l = cong (i ∙_) (trans (cong (λ zs → L.reverse (L.drop 1 zs)) (reverse-++ ls [ l ])) (reverse-involutive ls))

under-inst : ∀ {x y} → Under x y → instantOf y ≡ instantOf x
under-inst {x} (ys , refl) = inst-⊕ x ys

-- A position before one earlier than `q`'s instant is earlier too.
inst-le : ∀ {k v q} → k ≺ v → instantOf v ≺ⁱ instantOf q → instantOf k ≺ⁱ instantOf q
inst-le {k} {v} {q} kv vq with triⁱ (instantOf k) (instantOf v)
... | inj₁ lt        = transⁱ lt vq
... | inj₂ (inj₁ eq) = subst (_≺ⁱ instantOf q) (sym eq) vq
... | inj₂ (inj₂ gt) = ⊥-elim (≺-absurd {k} {v} kv (instant-≺ v k gt))

-- Between two positions of one instant lies that instant.
sandwich : ∀ {x f e} → x ≺ f → f ≺ e → instantOf e ≡ instantOf x → instantOf f ≡ instantOf x
sandwich {x} {f} {e} xf fe ex with triⁱ (instantOf x) (instantOf f)
... | inj₂ (inj₁ eq) = sym eq
... | inj₂ (inj₂ fx) = ⊥-elim (≺-absurd {x} {f} xf (instant-≺ f x fx))
... | inj₁ xf′ with triⁱ (instantOf f) (instantOf e)
...   | inj₁ fe′       = ⊥-elim (irrⁱ (subst (instantOf x ≺ⁱ_) ex (transⁱ xf′ fe′)))
...   | inj₂ (inj₁ eq) = ⊥-elim (irrⁱ (subst (instantOf x ≺ⁱ_) (trans eq ex) xf′))
...   | inj₂ (inj₂ ef) = ⊥-elim (≺-absurd {f} {e} fe (instant-≺ e f ef))

------------------------------------------------------------------------
-- The lane's parts' merge, elaborated, is the core's

module _ {Θ B Γ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ′ → X ∈ ⊤ ∷ Θ) (o : Obs Timeline Γ′ B) (ρ : DenEnv Θ) where
  open LaneStart using (module C)

  sv-eq : ∀ m → (λ k → ev m (shareˢ (laneSrc ρ′ o k) (counted (framed k))) ρ) ≡ C.Sv ρ′ o ρ m
  sv-eq nothing  = refl
  sv-eq (just _) = refl

  mm-eq : ∀ m → ev m (Tree.flatMap (mergeᶠ nothing) (λ k → shareˢ (laneSrc ρ′ o k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ []))) ρ ≡ C.MM ρ′ o ρ m
  mm-eq nothing  = refl
  mm-eq (just _) = refl

  -- A failing value of the parts' merge lies past everything under its
  -- lane part's frame's first value.
  fail-past : ∀ m s {f b} → enter (C.MM ρ′ o ρ m) s f (out b) → T (not (undone b))
            → ∀ {u} → Under (C.Bp ρ′ o ρ m (laneAt s) ⊕ [ ix 0 ]) u → u ≺ f
  fail-past m s {f} {b} x nk = part (merge-out (C.Sv ρ′ o ρ m) (Op.of (lanePart ∷ burstPart ∷ [])) s x)
    where
      bl : burstPart ≡ lanePart → ⊥
      bl ()

      part : (Σ Pos λ kq → Σ Part λ k → enter (Op.of (lanePart ∷ burstPart ∷ [])) s kq (out k)
               × enter (C.Sv ρ′ o ρ m k) (kq ⊕ [ ix 1 ]) f (out b) × (kq ⊕ [ ix 1 ]) ≺ f)
           → ∀ {u} → Under (C.Bp ρ′ o ρ m (laneAt s) ⊕ [ ix 0 ]) u → u ≺ f
      part (_ , _ , (at-out , _) , svr , _) = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (C.down ρ′ o ρ m lanePart (laneAt s) svr nk)))))
      part (_ , _ , (on-out at-out , _) , svr , _) = ⊥-elim (bl (proj₁ (C.down ρ′ o ρ m burstPart _ svr nk)))
      part (_ , _ , (on-out (on-out ()) , _) , _ , _)

-- A switch's lane runs at its value's second child.
switch-at : ∀ {A B H} op (d : Den A) (f : A → Den B) (Id : InvD H d) (If : ∀ a → InvD H (f a)) p (ok : Ok H p)
          → ∀ {q a k e} (x : enter d p q (out a)) (l : View.Lane f (enter d p) op q a k e) → op ≡ switchᶠ
          → proj₁ (lane-at op d f Id If p ok x l) ≡ q ⊕ [ ix 1 ]
switch-at switchᶠ d f Id If p ok x l refl = refl

module CombBurst (m : Maybe ℕ) {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (op : FlatOp) (f : A → Obs Timeline Γ B)
               (s : Obs Timeline Γ A) (env : DenEnv Δ) (cs : List Pos) (gd : GoodEnv env) (eh : EnvHeld ρ env cs)
               (hf : ∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ (f a))
               (p : Pos) (ok : Ok (Hots env) p) (fr : Fresh eh p) (ep : Early p)
               (H₁ : Held (enter (ev m (FlatHots.trig m ρ op f s env p) (FlatHots.env₀ m ρ op f s env p)) (FlatHots.c m ρ op f s env p ⊕ [ ix 1 ]))
                          ((FlatHots.c m ρ op f s env p ⊕ [ ix 1 ]) ∷ p ∷ cs))
               (tp : Placed (Fresh eh) (FlatHots.σ₁ m ρ op f s env p))
               (L₁ : Lawful (FlatHots.σ₁ m ρ op f s env p)) (L₂ : Lawful (FlatHots.σ₂ m ρ op f s env p))
               (L₃ : Lawful (FlatHots.σ₃ m ρ op f s env p))
               (ok₁ : Ok (Hots (hot (FlatHots.σ₁ m ρ op f s env p) ∷ FlatHots.env₀ m ρ op f s env p)) (FlatHots.p₀ m ρ op f s env p))
               (ok₂ : Ok (Hots (hot (FlatHots.σ₂ m ρ op f s env p) ∷ hot (FlatHots.σ₁ m ρ op f s env p) ∷ FlatHots.env₀ m ρ op f s env p))
                         (FlatHots.p₀₀ m ρ op f s env p))
               (ok₃ : Ok (Hots (FlatHots.env′ m ρ op f s env p)) (FlatHots.P m ρ op f s env p))
               (ep₃ : Early (FlatHots.P m ρ op f s env p)) where
  open FlatHots m ρ op f s env p
  open CombSrc m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃
  open CombLanes m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃
  open LaneRoutes m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃ using (inner; done-before; end-σ; lane-end-done)

  -- NO VALUE OF THE REAL FLATMAP'S OUTER LIES STRICTLY UNDER ANOTHER.
  postulate
    ro-nest : ∀ {q a l ls a′} → RO q (out a) → RO (q ⊕ (l ∷ ls)) (out a′) → ⊥

  E₄ : DenEnv (IE B ∷ IE A ∷ ⊤ ∷ Δ)
  E₄ = hot σ₂ ∷ hot σ₁ ∷ env₀

  ρ⁴ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ ⊤ ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ
  ρ⁴ i = there (there (there (there (ρ i))))

  module LC (a : A) = LaneStart.C ρ⁴ (f a) E₄ m
  module BA (a : A) (s′ : Pos) = BurstFew.BurstAt ρ⁴ (f a) E₄ m s′

  Q : Pos
  Q = p₀₀ ⊕ [ ix 1 ]

  okQ : Ok (Hots E₄) Q
  okQ = ok-step p₀₀ ok₂

  ROd : Den A
  ROd = ev m (each valuesOf (connected (there (here refl)))) E₄

  Id : InvD (Hots E₄) ROd
  Id = inv-ev m (each valuesOf (connected (there (here refl)))) E₄ g₂

  If : ∀ a → InvD (Hots E₄) (fL a)
  If a = inv-ev m (laneˢ (g a)) E₄ g₂

  -- Where the scan's source reads a lane's row.
  Lr : IE B → Maybe (Input B)
  Lr x = just (inj₁ (laneB , x))

  -- The next lane row a lane started at `y` shows in its start's instant.
  Next : Pos → Set
  Next y = Σ Pos λ b → Σ Pos λ n′ → (M b (out (Lr (instEmit (mark burstEnd) n′))) ⊎ Σ ℕ λ kd → M b (out (Lr (instEmit (mark (laneDone kd)) n′))))
         × y ≺ b × instantOf b ≡ instantOf y

  -- THE LANES' ROWS BEFORE A SOURCE VALUE'S INSTANT ARE FEW.
  sent-few : ∀ {q a} → M q (out a) → ∀ {v} → instantOf v ≺ⁱ instantOf q → Few σ₃ v
  sent-few {q} {a} mq {v} vq = L.concatMap cands (q ∷ proj₁ FM) , λ {k} {e} σk kv → ∈-stable λ ¬i →
      lane-shown σk (mq′ mq)
        (≺→≼ {k ⊕ [ sub LS.J ]} {q} (instant-≺ (k ⊕ [ sub LS.J ]) q (subst (_≺ⁱ instantOf q) (sym (inst-⊕ k [ sub LS.J ])) (inst-le {k} {v} {q} kv vq))))
        λ (z , e″ , mz , st , zq , _) → ¬i (cand-in st (z-in zq mz))
    where
      FM : Few M q
      FM = entered-few (ev m src env′) P {q} {out a} (λ {_} {_} → tt) mq

      cands : Pos → List Pos
      cands z = up1 z ∷ up1 (up1 z) ∷ []

      z-in : ∀ {z e″} → z ≼ q → LS.M′ z e″ → z ∈ (q ∷ proj₁ FM)
      z-in {z} zq mz with ≼-split {z} {q} zq
      ... | inj₁ lt   = there (proj₂ FM (toM mz) lt)
      ... | inj₂ refl = here refl

      cand-in : ∀ {k z zs} → Step (k ⊕ [ sub LS.J ]) z → z ∈ zs → k ∈ L.concatMap cands zs
      cand-in {k} (inj₁ refl) i = ∈-concat⁺′ (here (up1-⊕ k (sub LS.J))) (∈-map⁺ cands i)
      cand-in {k} (inj₂ refl) i =
        ∈-concat⁺′ (there (here (trans (cong up1 (up1-⊕ (k ⊕ [ sub LS.J ]) (ix 0))) (up1-⊕ k (sub LS.J))))) (∈-map⁺ cands i)

  -- An uncut running lane's row, past no end of the real flatMap before
  -- a position the lanes' rows before are few, is one of theirs.
  lane-σ₃ : ∀ {q₀ a₀ k e v} → RO q₀ (out a₀) → RV.Runs op q₀ → RV.Lane op q₀ a₀ k e → Work e → ¬ RV.CutAt op q₀ k
          → k ≼ v → (∀ {d} → R d end → d ≺ v → ⊥) → Few σ₃ v → ¬ ¬ σ₃ k e
  lane-σ₃ {k = k} {e} {v} xo rn l wk nc kv ne Fv κ =
    join-shows op ROd fL Id If Q okQ
      (shows-ev m (each valuesOf (connected (there (here refl)))) E₄ g₂ Q okQ)
      (λ a s′ oks → shows-ev m (laneˢ (g a)) E₄ g₂ s′ oks)
      (proj₁ Fv , λ x fx lt → proj₂ Fv (prop (R-from (x , few-reach fx)) (≺→≼ lt)) lt) λ fJ →
      κ (prop (R-from (join-in op fL RO xo rn l nc wk , proj₁ fJ , λ {k′} x lt _ → proj₂ fJ x (≺-≼-≺ {k′} {k} {v} lt kv))) kv)
    where
      prop : ∀ {k′ e′} → R k′ e′ → k′ ≼ v → σ₃ k′ e′
      prop {k′} rk kv′ = rk , λ {c′} rc → [ (λ le → le) , (λ lt → ⊥-elim (ne rc (≺-≼-≺ {c′} {k′} {v} lt kv′))) ]′ (≼-or-≻ k′ c′)

  -- No end of the real flatMap comes before a position an uncut running
  -- lane shows no `laneDone` before.
  no-end-before : ∀ {q₀ a₀ v} → RO q₀ (out a₀) → RV.Runs op q₀ → ¬ RV.CutAt op q₀ v
         → (∀ {yd kd n} → RV.Lane op q₀ a₀ yd (out (instEmit (mark (laneDone kd)) n)) → yd ≺ v → ⊥)
         → ∀ {d} → R d end → d ≺ v → ⊥
  no-end-before xo rn nc nd {d} rd dv =
    let (yd , kd , n , ld , ydd) = done-before xo rn (λ ct → nc (cutat-up op fL RO dv ct)) (end-σ rd)
    in nd ld (≺-trans {yd} {d} {_} ydd dv)

  -- A switch cuts no row under its lane's subscription.
  module Run {q₀ a₀ c x} (xo : RO q₀ (out a₀)) (rn : RV.Runs op q₀) (l : RV.Lane op q₀ a₀ c (out x)) where
    LAt = lane-at op ROd fL Id If Q okQ xo l

    sL : Pos
    sL = proj₁ LAt

    oks : Ok (Hots E₄) sL
    oks = proj₁ (proj₂ LAt)

    back : ∀ {k e} → enter (fL a₀) sL k e → sL ≺ k → RV.Lane op q₀ a₀ k e
    back = proj₂ (proj₂ (proj₂ (proj₂ LAt)))

    fwd : ∀ {k e} → RV.Lane op q₀ a₀ k e → enter (fL a₀) sL k e
    fwd = lane-fwd op ROd fL Id If Q okQ xo l

    after : ∀ {k e} → enter (fL a₀) sL k e → sL ≺ k
    after r = world-after (InvAt.world (If a₀ sL oks) r) (InvAt.real (If a₀ sL oks) r)

    toL : ∀ {k e} → enter (LC.LaneD a₀) sL k e → enter (fL a₀) sL k e
    toL {k} {e} = subst (λ d → enter d sL k e) (sym (LaneStart.lane-eq ρ⁴ (f a₀) E₄ m))

    fromL : ∀ {k e} → enter (fL a₀) sL k e → enter (LC.LaneD a₀) sL k e
    fromL {k} {e} = subst (λ d → enter d sL k e) (LaneStart.lane-eq ρ⁴ (f a₀) E₄ m)

    ivMM : InvAt (Hots E₄) sL (enter (LC.MM a₀) sL)
    ivMM = subst (λ d → InvAt (Hots E₄) sL (enter d sL)) (mm-eq ρ⁴ (f a₀) E₄ m) (inv-ev m (inner a₀) E₄ g₂ sL oks)

    module TB = TakeBack true undone (LC.MM a₀) sL ivMM

    uncut : ∀ {k} → Under sL k → ¬ RV.CutAt op q₀ k
    uncut {k} uk ct =
      let op≡ = cut-switch op fL RO ct
          (q′ , a′ , xo′ , qq′ , q′k) = subst (λ o₀ → RV.CutAt o₀ q₀ k → Superseded RO q₀ k) (sym op≡) (λ z → z) ct
          uk′ = subst (λ z → Under z k) (switch-at op ROd fL Id If Q okQ xo l op≡) uk
      in [ (λ le → ≺-irrefl {q₀} (≺-≼-≺ {q₀} {q′} {q₀} qq′ le))
         , (λ (l′ , ls , e) → ro-nest xo (subst (λ z → RO z (out a′)) e xo′)) ]′
         (below-or-under q′ q₀ last (≺-trans {q′} {k} {q₀ ⊕ [ last ]} q′k (under-last q₀ uk′)))

    -- A `laneDone` of the lane is its take's failing value.
    dn-failed : ∀ {yd kd n v} → RV.Lane op q₀ a₀ yd (out (instEmit (mark (laneDone kd)) n)) → yd ≺ v → TB.Failed v
    dn-failed {yd} {kd} {n} {v} ld ydv = go (fromL (fwd ld)) ydv
      where
        go : ∀ {y} → enter (LC.LaneD a₀) sL y (out (instEmit (mark (laneDone kd)) n)) → y ≺ v → TB.Failed v
        go (TB.pass _ () _ , _) _
        go (TB.fail {q = w} xw nk _ _ , _) yv = w , _ , xw , nk , ≺-trans {w} {w ⊕ [ ix 0 ]} {v} (≺-ext w {ix 0} []) yv

  -- A LANE STARTED AT `y` SHOWS ITS BURST'S END, OR ITS `laneDone`, IN
  -- `y`'s INSTANT, before any later instant's source value.
  module Start {q₀ a₀ c n} (xo : RO q₀ (out a₀)) (rn : RV.Runs op q₀) (l : RV.Lane op q₀ a₀ c (out (instEmit (mark laneStart) n))) where
    open Run xo rn l

    LSR = LaneStart.lane-start-row ρ⁴ (f a₀) E₄ m sL

    c≡ : c ≡ LC.startAt a₀ sL
    c≡ = start-once xo l (back (proj₁ LSR) (under-ext sL (proj₂ LSR)))

    uc : Under (sL ⊕ [ ix 0 ]) c
    uc = subst (Under (sL ⊕ [ ix 0 ])) (sym c≡) (proj₂ LSR)

    -- The start lies under the lane part's frame's first value.
    uc-fr : Under (LC.Bp a₀ (laneAt sL) ⊕ [ ix 0 ]) c
    uc-fr = subst (Under (LC.Bp a₀ (laneAt sL) ⊕ [ ix 0 ])) (sym c≡)
              (under-⊕ (under-⊕ (under-refl (LC.Bp a₀ (laneAt sL) ⊕ [ ix 0 ])) (ix 1)) (ix 0))

    c-inst : instantOf c ≡ instantOf sL
    c-inst = trans (under-inst uc) (inst-⊕ sL [ ix 0 ])

    open BA a₀ sL using (Eb; mm-row; u-s; u-R)

    eb-c : instantOf Eb ≡ instantOf c
    eb-c = trans (trans (under-inst u-s) (inst-⊕ sL [ ix 1 ])) (sym c-inst)

    u-Eb : Under sL Eb
    u-Eb = under-trans (under-⊕ (under-refl sL) (ix 1)) u-s

    -- The merge's rows of the lane part's subscription and the burst's
    -- end lie under the lane's subscription.
    start-below : ∀ w → (c ⊕ [ sub w ]) ≺ Eb
    start-below w = ≺-trans {c ⊕ [ sub w ]} {sL ⊕ [ ix 1 ]} {Eb} (under-≺ sL (s≤s z≤n) (under-⊕ uc (sub w))) (under-ext (sL ⊕ [ ix 1 ]) u-R)

    mm-shows : Shows (Merge.JoinT (LC.Sv a₀) (enter (Op.of (lanePart ∷ burstPart ∷ [])) sL))
    mm-shows = subst (λ F → Shows (Merge.JoinT F (enter (Op.of (lanePart ∷ burstPart ∷ [])) sL))) (sv-eq ρ⁴ (f a₀) E₄ m)
      (k-shows λ n′ → SJ.Flat.sk-merge {n = n′} (Op.of (lanePart ∷ burstPart ∷ [])) (λ k → ev m (shareˢ (g a₀ k) (counted (framed k))) E₄) (of-inv _)
        (λ k → inv-ev m (shareˢ (g a₀ k) (counted (framed k))) E₄ g₂) sL oks (sk-of _ sL)
        (λ k s′ ok′ → shows-k (shows-ev m (shareˢ (g a₀ k) (counted (framed k))) E₄ g₂ s′ ok′)))

    module Shown {q a} (mq : M q (out a)) (cq : instantOf c ≺ⁱ instantOf q) where
      -- Its rows in its start's instant lie before the source value.
      at-c : ∀ {v} → instantOf v ≡ instantOf c → instantOf v ≺ⁱ instantOf q
      at-c vc = subst (_≺ⁱ instantOf q) (sym vc) cq

      shown-M : ∀ {k e} → σ₃ k e → instantOf k ≡ instantOf c → ∀ {b} → e ≡ out b → ¬ ¬ M (k ⊕ [ sub LS.J ]) (out (Lr b))
      shown-M {k} σk kc {b} refl κ =
        lane-shown σk (mq′ mq) (≺→≼ {k ⊕ [ sub LS.J ]} {q} (instant-≺ (k ⊕ [ sub LS.J ]) q (at-c (trans (inst-⊕ k [ sub LS.J ]) kc))))
          λ (z′ , e″ , m′ , _ , _ , pr) → κ (subst₂ M (proj₁ (pr refl)) (proj₂ (pr refl)) (toM m′))

      next-at : ∀ {w k b} → σ₃ k (out b) → instantOf k ≡ instantOf c → (c ⊕ [ sub w ]) ≺ k
              → (M (k ⊕ [ sub LS.J ]) (out (Lr b)) → Σ Pos λ n′ → M (k ⊕ [ sub LS.J ]) (out (Lr (instEmit (mark burstEnd) n′))) ⊎ Σ ℕ λ kd → M (k ⊕ [ sub LS.J ]) (out (Lr (instEmit (mark (laneDone kd)) n′))))
              → ¬ ¬ Next (c ⊕ [ sub w ])
      next-at {w} {k} σk kc ck sel κ = shown-M σk kc refl λ mk →
        let (n′ , mb) = sel mk
        in κ (k ⊕ [ sub LS.J ] , n′ , mb , ≺-trans {c ⊕ [ sub w ]} {k} {k ⊕ [ sub LS.J ]} ck (≺-ext k [])
             , trans (inst-⊕ k [ sub LS.J ]) (trans kc (sym (inst-⊕ c [ sub w ]))))

      -- No failure before the burst's end: the merge shows it, the lane
      -- with it.
      burst : ∀ w → ¬ TB.Failed Eb → ¬ ¬ Next (c ⊕ [ sub w ])
      burst w nF κ = mm-row′ λ xr →
        let r′ = toL (TB.up (TB.pass xr tt nF))
        in lane-σ₃ xo rn (back r′ (after r′)) tt (uncut u-Eb) (≼-refl {Eb}) noend Fσ λ σEb →
             next-at σEb eb-c (start-below w) (λ mb → _ , inj₁ mb) κ
        where
          Fσ : Few σ₃ Eb
          Fσ = sent-few mq (at-c eb-c)

          noend : ∀ {d} → R d end → d ≺ Eb → ⊥
          noend = no-end-before xo rn (uncut u-Eb) (λ ld ydEb → nF (dn-failed ld ydEb))

          lane-σ : ∀ {k} (e : Ev (IE B)) → RV.Lane op q₀ a₀ k e → k ≺ Eb → ¬ ¬ Σ (Ev (IE B)) (σ₃ k)
          lane-σ {k} end lk kEb _ =
            let (yd , kd , n′ , ld , ydk) = lane-end-done xo lk in nF (dn-failed ld (≺-trans {yd} {k} {Eb} ydk kEb))
          lane-σ {k} (out b) lk kEb κ′ =
            lane-σ₃ xo rn lk tt (λ ct → uncut u-Eb (cutat-up op fL RO kEb ct)) (≺→≼ {k} {Eb} kEb) noend Fσ λ σk → κ′ (_ , σk)
          lane-σ {k} skip lk kEb κ′ =
            lane-σ₃ xo rn lk tt (λ ct → uncut u-Eb (cutat-up op fL RO kEb ct)) (≺→≼ {k} {Eb} kEb) noend Fσ λ σk → κ′ (_ , σk)
          lane-σ {k} (pin r) lk kEb κ′ =
            lane-σ₃ xo rn lk tt (λ ct → uncut u-Eb (cutat-up op fL RO kEb ct)) (≺→≼ {k} {Eb} kEb) noend Fσ λ σk → κ′ (_ , σk)

          mm-σ : ∀ {k e} → enter (LC.MM a₀) sL k e → k ≺ Eb → ¬ ¬ Σ (Ev (IE B)) (σ₃ k)
          mm-σ {k} {e} x kEb = let r = toL (TB.below nF x kEb) in lane-σ e (back r (after r)) kEb

          mm-row′ : ¬ ¬ enter (LC.MM a₀) sL Eb (out (BA.be a₀ sL))
          mm-row′ = few-lift mm-shows (few-via mm-σ Fσ) mm-row (≼-refl {Eb})

      -- A failure before it: the first is the lane's `laneDone`.
      failed : ∀ w → TB.Failed Eb → ¬ ¬ Next (c ⊕ [ sub w ])
      failed w (f₀ , _ , x₀ , nk₀ , f₀Eb) κ = TB.min-fail x₀ nk₀ λ (fv , b , xf , nkf , nFf , ff₀) →
        let r′ = toL (TB.up (TB.fail xf nkf nFf tt))
            (kd , nd , b≡) = done-of b nkf
            cf : (c ⊕ [ sub w ]) ≺ fv
            cf = fail-past ρ⁴ (f a₀) E₄ m sL xf nkf (under-⊕ uc-fr (sub w))
            fEb = ≼-≺-≺ {fv} {f₀} {Eb} ff₀ f₀Eb
            f-inst : instantOf fv ≡ instantOf (c ⊕ [ sub w ])
            f-inst = sandwich {c ⊕ [ sub w ]} {fv} {Eb} cf fEb (trans eb-c (sym (inst-⊕ c [ sub w ])))
            fc : instantOf (fv ⊕ [ ix 0 ]) ≡ instantOf c
            fc = trans (inst-⊕ fv [ ix 0 ]) (trans f-inst (inst-⊕ c [ sub w ]))
            uf : Under sL fv
            uf = [ (λ le → ⊥-elim (≺-irrefl {sL} (≺-≼-≺ {sL} {fv} {sL} (≺-trans {sL} {c ⊕ [ sub w ]} {fv} (under-ext sL (under-⊕ uc (sub w))) cf) le)))
                 , (λ (l′ , ls , e) → l′ ∷ ls , e) ]′
                 (below-or-under fv sL last (≺-trans {fv} {Eb} {sL ⊕ [ last ]} fEb (under-last sL u-s)))
            uf₀ = under-⊕ uf (ix 0)
            noend : ∀ {d} → R d end → d ≺ fv ⊕ [ ix 0 ] → ⊥
            noend = no-end-before xo rn (uncut uf₀) λ ld ydv →
              ≺-irrefl {fv ⊕ [ ix 0 ]} (subst (_≺ fv ⊕ [ ix 0 ]) (lane-once m undone (inner a₀) E₄ g₂ sL oks (fwd ld) tt r′ nkf) ydv)
        in lane-σ₃ xo rn (back r′ (after r′)) tt (uncut uf₀) (≼-refl {fv ⊕ [ ix 0 ]}) noend (sent-few mq (at-c fc)) λ σf →
             next-at σf fc (≺-trans {c ⊕ [ sub w ]} {fv} {fv ⊕ [ ix 0 ]} cf (≺-ext fv {ix 0} []))
               (λ mb → nd , inj₂ (kd , subst (λ b′ → M (fv ⊕ [ ix 0 ] ⊕ [ sub LS.J ]) (out (Lr b′))) b≡ mb)) κ

      shown : ∀ w → ¬ ¬ Next (c ⊕ [ sub w ])
      shown w κ = TB.em λ where
        (inj₁ F)  → failed w F κ
        (inj₂ nF) → burst w nF κ

  burst-next : ∀ {y n q a} → M y (out (Lr (instEmit (mark laneStart) n))) → M q (out a) → instantOf y ≺ⁱ instantOf q → ¬ ¬ Next y
  burst-next {y} {n} {q} {a} my mq yq =
    let (c , w , σc , y≡) = lane-sent my
        (q₀ , a₀ , xo , rn , l , _) = σ₃-lane σc
        cq = subst (_≺ⁱ instantOf q) (trans (cong instantOf y≡) (inst-⊕ c [ sub w ])) yq
    in subst (λ y′ → ¬ ¬ Next y′) (sym y≡) (Start.Shown.shown xo rn l mq cq w)
