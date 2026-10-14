------------------------------------------------------------------
-- THE FLOOR ARGUMENT: A RUN THAT CONNECTS NOTHING WRITES A WATCHED
-- NODE ONLY WHERE ITS OWN FRAMES STAND.  Watch one node below the
-- counter whose rows all end at one terminus.  Every write a run makes
-- is to a frame's own node on the path being walked, or to the node the
-- counter hands out; and every path walked is either built on the one
-- the run started from, which ends where it did, or a row a share's
-- fan-out admitted, which sits at floor `suc i` above the sink `i` it
-- was admitted at and so ends strictly above every sink the watched
-- node's rows end at.  A connect is the one step that leaves both: it
-- walks from a share's own sink, and that share's readers are only the
-- rows the run itself registered, which is the rule's `linked`.
------------------------------------------------------------------

module Rx.Evaluator.Reducible.Floor where

open import Data.Bool using (Bool; true; false; T; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≤_; _<_; z≤n; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; n≤1+n; <-≤-trans; <-irrefl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function.Base using (_|>′_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)
open import Relation.Nullary using (yes; no)

open import Decide using (≡ᵇ-refl; ≡ᵇ→≡)
open import Rx.Prim using (Source)
open import Rx.Exp using (Ctx; Closed; Val; obs; _+ᵗ_; _≟ᵗ_)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; share-sink; _↠[_]_; Frame; map-f; scan-f; take-f; batchSync-f;
  from-inner; thru-outer; echoᵗ; NodeState; NodeId; RegId; RegSrc; RegRow; regFloor; lookupNode;
  setNode; frameNodes; pathHasNode; installNode; lowerFloor; AllOp; mergeAllᵒ; switch-st;
  exhaust-st; mergeAll-st; shareAdmit; shareDying; shareFinish; switchKill; thruWrap; drainSt;
  regSource; sameSource; dropSource; spentOn; memberSource; atSlot; atDyn)
open import Rx.Evaluator.Freshness using (nodeCt; lookup-set; set-above; <→≢ᵇ)
open import Rx.Evaluator.Unconn-Arith using (KeepsC; keeps-refl; keeps-trans; keeps-cons)
open import Rx.Evaluator.Keeps using (thruWrap-keeps; scanDispatch-keeps; takeDispatch-keeps; batchDispatch-keeps)
open import Rx.Evaluator.Domain using (subscribeE⇓; subscribeInner⇓; thruConsume⇓; thruWalk⇓; mergeAllDrain⇓;
  innerFinish⇓; innerReact⇓; stepFrame⇓; subscribeAll⇓; subscribeSharedSlot⇓; foldPath⇓; dispatchShare⇓;
  shareWalk⇓; shareGo⇓;
  subs-floor; subs-shared; subs-hot-done; subs-hot-live; subs-cold-sync; subs-cold-async; subs-of; subs-empty;
  subs-takeWhile; subs-batchSync; subs-map; subs-scan;
  subs-flatten; subs-μ; subs-defer; subs-mint; inner; consume-all-sub; consume-all-enqueue; consume-all-nil;
  consume-switch-sub; consume-switch-nil; consume-exhaust-sub; consume-exhaust-nil; walk-nil; walk-echo; walk-cons;
  drain-spent; drain-nil; drain-no-room; drain-room; finish-all-drain; finish-switch-clear; finish-exhaust-clear;
  finish-nil; react-false; react-alive; react-dead; step-map; step-scan; step-take; step-batchSync;
  step-from-inner; step-thru-outer; sub-all; connect; slot-spent; slot-join; slot-connect; disp; walk-end;
  walk-more; go-nil; go-cut; go-live; fold-root; fold-sink; fold-step)
open import Rx.Evaluator.Reducible.Support using (EndsAt; Sound; NodeOn; Kept; standing; Linked; SlotLinked; linked; ruled;
  endOf; waiting; drain-waiting; bumpNode; admit-row; lower-nodes; lower-end; ∨-T; ∨-Tˡ; ∨-Tʳ; node-cases;
  self-node; kill-sub; wrap-facts; wrapped; wrap-reg; scanOff; scanCt; scanReg; takeOff; takeCt; takeReg;
  batchOff; batchCt; batchReg; ends; fresh-path; distinct; at-end; node-below; off-path)

-- the end of a cascade drops rows and moves nothing else the rule reads
drop-sub : ∀ {n} {Γ : Ctx n} {t} (src : Source) (reg : List (RegRow Γ t)) {r}
         → r ∈ dropSource src reg → r ∈ reg
drop-sub src [] ()
drop-sub src ((rid , s , c) ∷ reg) r∈ with sameSource src (regSource s)
... | true  = there (drop-sub src reg r∈)
... | false with r∈
...   | here refl = here refl
...   | there r∈′ = there (drop-sub src reg r∈′)

-- a path's sinks sit at or above its floor
end-floor : ∀ {n} {Γ : Ctx n} {lo s t} (p : Path Γ lo s t) {i : Fin n} → endOf p ≡ just i → lo ≤ toℕ i
end-floor root             ()
end-floor (share-sink i le) refl = le
end-floor (f ↠[ le ] p)    eq   = ≤-trans le (end-floor p eq)

-- A SINK AT OR ABOVE THE WATCHED TERMINUS: never when the terminus is
-- the root, whose rows reach no sink at all.
Clr : ∀ {n} → Maybe (Fin n) → Fin n → Set
Clr nothing  i = ⊥
Clr (just j) i = toℕ j ≤ toℕ i

clear-self : ∀ {n} (y : Maybe (Fin n)) (i : Fin n) → y ≡ just i → Clr y i
clear-self .(just i) i refl = ≤-refl

-- a row a sink at or above the terminus admitted ends above that sink,
-- so it does not end at the terminus
floor-miss : ∀ {n} {Γ : Ctx n} {s t} (y : Maybe (Fin n)) (i : Fin n) (p : Path Γ (suc (toℕ i)) s t)
           → Clr y i → endOf p ≡ y → ⊥
floor-miss (just j) i p c eq = <-irrefl refl (≤-trans (end-floor p eq) c)

-- and every sink it reaches is above the terminus too
floor-clear : ∀ {n} {Γ : Ctx n} {s t} (y : Maybe (Fin n)) (i : Fin n) (p : Path Γ (suc (toℕ i)) s t)
            → Clr y i → ∀ i′ → endOf p ≡ just i′ → Clr y i′
floor-clear (just j) i p c i′ eq = ≤-trans c (≤-trans (n≤1+n _) (end-floor p eq))

-- a node read off and put back through a frame's node list
notIn₁ : ∀ {a k : ℕ} → (T (any (_≡ᵇ k) (a ∷ [])) → ⊥) → (a ≡ᵇ k) ≡ false
notIn₁ {a} {k} ni with a ≡ᵇ k
... | true  = ⊥-elim (ni tt)
... | false = refl

notIn₂ : ∀ {a j k : ℕ} → (T (any (_≡ᵇ k) (a ∷ j ∷ [])) → ⊥) → (a ≡ᵇ k) ≡ false
notIn₂ {a} {j} {k} ni with a ≡ᵇ k
... | true  = ⊥-elim (ni tt)
... | false = refl

off₁ : ∀ {a k : ℕ} → (a ≡ᵇ k) ≡ false → T (any (_≡ᵇ k) (a ∷ [])) → ⊥
off₁ na h rewrite na = h

off₂ : ∀ {a j k : ℕ} → (a ≡ᵇ k) ≡ false → (j ≡ᵇ k) ≡ false → T (any (_≡ᵇ k) (a ∷ j ∷ [])) → ⊥
off₂ na nj h rewrite na | nj = h

hit₂ : ∀ {a j k : ℕ} → a ≡ k → T (any (_≡ᵇ k) (a ∷ j ∷ []))
hit₂ {j = j} {k} refl = self-node k (j ∷ [])

≢ᵇ : ∀ {a k : ℕ} → (a ≡ᵇ k) ≡ false → a ≡ k → ⊥
≢ᵇ {k = k} ne refl with trans (sym ne) (≡ᵇ-refl k)
... | ()
------------------------------------------------------------------
-- THE INDUCTION, AT ONE WATCHED NODE.  `fed` says whether the
-- node's own inners may finish into it -- the merge whose queue a
-- refill would grow -- or whether it is written by nothing at all; `W`
-- bounds its queue and `h₀` is what it holds.  `sl₀` and `cs₀` are the
-- table and the connected set the run started from, so a share outside
-- `cs₀` is one the run itself connects.
------------------------------------------------------------------

module Watch {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             (fed : Bool) (nid : NodeId) (x : Maybe (Fin n)) (W : ℕ)
             (h₀ : Maybe (NodeState Γ)) (sl₀ : Slots Γ) (cs₀ : List Source) where

  NotIn : ∀ {s u} → Frame Γ s u → Set
  NotIn f = T (any (_≡ᵇ nid) (frameNodes f)) → ⊥

  -- the frames a walked path may stand on: none at the watched node,
  -- save its own inners' exits where they are allowed to finish into it
  FrameOK : ∀ {s u} → Frame Γ s u → Set
  FrameOK f@(map-f fn)         = NotIn f
  FrameOK f@(scan-f fn k)      = NotIn f
  FrameOK f@(take-f _ k)       = NotIn f
  FrameOK f@(batchSync-f k)    = NotIn f
  FrameOK f@(from-inner _ _ _) = fed ≡ false → NotIn f
  FrameOK f@(thru-outer _ k) = NotIn f

  PathOK : ∀ {lo u} → Path Γ lo u t → Set
  PathOK root             = ⊤
  PathOK (share-sink _ _) = ⊤
  PathOK (f ↠[ _ ] κ)     = FrameOK f × PathOK κ

  -- A SHARE THE RUN CONNECTS: shared in the table, and outside the set
  -- the run started from.  Its readers are only rows the run itself
  -- registered, since a reader of an unconnected share is the rule's
  -- `linked` broken.
  Fresh : Fin n → Set
  Fresh i = Σ _ λ d → Σ _ λ ok → sl₀ i ≡ shared d {ok = ok} × memberSource (toℕ i) cs₀ ≡ false

  -- A SINK A WALKED PATH MAY END AT: at or above the terminus, or a
  -- share the run connects
  Sink : Fin n → Set
  Sink i = Clr x i ⊎ Fresh i

  -- A WALKED PATH: its frames are allowed, a row it registers through
  -- the watched node ends at the terminus, and every sink it ends at is
  -- one it may.
  record PI {lo u} (κ : Path Γ lo u t) : Set where
    constructor pᵢ
    field
      pok : PathOK κ
      pon : T (pathHasNode nid κ) → endOf κ ≡ x
      pcl : ∀ i → endOf κ ≡ just i → Sink i

  PF : ∀ {lo s u} → Frame Γ s u → Path Γ lo u t → Set
  PF f κ = FrameOK f × (T (any (_≡ᵇ nid) (frameNodes f)) → endOf κ ≡ x) × PI κ

  PA : ∀ {lo u} → NodeId → Path Γ lo u t → Set
  PA a κ = PI κ × (a ≡ nid → endOf κ ≡ x) × (fed ≡ false → (a ≡ᵇ nid) ≡ false)

  pf-of : ∀ {lo ℓ s u} {f : Frame Γ s u} {le : lo ≤ ℓ} {κ : Path Γ ℓ u t} → PI (f ↠[ le ] κ) → PF f κ
  pf-of (pᵢ (fo , ok) oe ce) = fo , (λ h → oe (∨-Tˡ h)) , pᵢ ok (λ h → oe (∨-Tʳ h)) ce

  pa-of : ∀ {lo s op a j} {κ : Path Γ lo s t} → PF (from-inner op a j) κ → PA a κ
  pa-of {a = a} {j} (fo , fe , pi) = pi , (λ eq → fe (hit₂ {a} {j} {nid} eq)) , (λ f → notIn₂ {a} {j} {nid} (fo f))

  pa-inl : ∀ {lo s a} {κ : Path Γ lo s t} → PA a κ → a ≡ nid → fed ≡ false → ⊥
  pa-inl {a = a} (_ , _ , ne) eq f = ≢ᵇ {a} {nid} (ne f) eq

  fi-inl : ∀ {lo s op a j} {κ : Path Γ lo s t} → PF (from-inner op a j) κ → a ≡ nid → fed ≡ false → ⊥
  fi-inl {a = a} {j} (fo , _ , _) eq f = fo f (hit₂ {a} {j} {nid} eq)

  -- a frame off the watched node, pushed
  push : ∀ {lo ℓ s u} {f : Frame Γ s u} {le : lo ≤ ℓ} {κ : Path Γ ℓ u t}
       → FrameOK f → NotIn f → PI κ → PI (f ↠[ le ] κ)
  push fo ni (pᵢ ok oe ce) = pᵢ (fo , ok) (λ h → [ (λ fn → ⊥-elim (ni fn)) , oe ]′ (∨-T h)) ce

  -- an inner's exit pushed at the counter
  fresh-PI : ∀ {lo u op a c} {le : lo ≤ lo} {κ : Path Γ lo u t}
           → nid < c → PA a κ → PI (from-inner op a c ↠[ le ] κ)
  fresh-PI {a = a} {c} lt (pᵢ ok oe ce , ae , ne) =
    pᵢ ((λ f → off₂ {a} {c} {nid} (ne f) (<→≢ᵇ lt)) , ok)
       (λ h → [ (λ fn → node-cases {x = a} {y = c} fn ae (λ eq → ⊥-elim (<-irrefl (sym eq) lt))) , oe ]′ (∨-T h))
       ce

  fresh-off : ∀ {c} → nid < c → T (any (_≡ᵇ nid) (c ∷ [])) → ⊥
  fresh-off {c} lt = off₁ {c} {nid} (<→≢ᵇ lt)

  thru-PA : ∀ {lo u a} {κ : Path Γ lo u t} → (a ≡ᵇ nid) ≡ false → PI κ → PA a κ
  thru-PA {a = a} ne pi = pi , (λ eq → ⊥-elim (≢ᵇ {a} {nid} ne eq)) , (λ _ → ne)

  frame-ok : ∀ {s u} (f : Frame Γ s u) → NotIn f → FrameOK f
  frame-ok (map-f _)          ni = ni
  frame-ok (scan-f _ _)       ni = ni
  frame-ok (take-f _ _)       ni = ni
  frame-ok (batchSync-f _)    ni = ni
  frame-ok (from-inner _ _ _) ni = λ _ → ni
  frame-ok (thru-outer _ _) ni = ni

  -- a path off the watched node stands on allowed frames
  off-ok : ∀ {lo u} (κ : Path Γ lo u t) → (T (pathHasNode nid κ) → ⊥) → PathOK κ
  off-ok root             off = tt
  off-ok (share-sink _ _) off = tt
  off-ok (f ↠[ _ ] κ)     off = frame-ok f (λ h → off (∨-Tˡ h)) , off-ok κ (λ h → off (∨-Tʳ h))

  -- a walked path keeps being one under a lowered floor
  lower-ok : ∀ {lo lo′ u} (le : lo′ ≤ lo) (κ : Path Γ lo u t) → PathOK κ → PathOK (lowerFloor le κ)
  lower-ok le root             ok = ok
  lower-ok le (share-sink i p) ok = ok
  lower-ok le (f ↠[ h ] p)     ok = ok

  lower-PI : ∀ {lo lo′ u} (le : lo′ ≤ lo) (κ : Path Γ lo u t) → PI κ → PI (lowerFloor le κ)
  lower-PI le κ (pᵢ ok oe ce) =
    pᵢ (lower-ok le κ ok) (λ th → trans (lower-end le κ) (oe (subst T (lower-nodes le κ nid) th)))
       (λ i eq → ce i (trans (sym (lower-end le κ)) eq))

  record NI (ts : List (NodeId × NodeState Γ)) : Set where
    constructor nᵢ
    field
      nw : waiting (lookupNode nid ts) ≤ W
      nh : fed ≡ false → lookupNode nid ts ≡ h₀

  -- A ROW THE WATCH CAN READ: through the watched node only where it
  -- ends at the terminus, and walkable where its share is one the run
  -- connects.
  FreshPI : (rs : RegSrc Γ) {u : _} → Path Γ (regFloor rs) u t → Set
  FreshPI (atSlot j)  p = Fresh j → PI p
  FreshPI (atDyn _ _) p = ⊤

  RowOK : RegRow Γ t → Set
  RowOK (_ , rs , (_ , p)) = (T (pathHasNode nid p) → endOf p ≡ x) × FreshPI rs p

  EA : List (RegRow Γ t) → Set
  EA R = ∀ {r} → r ∈ R → RowOK r

  -- THE WATCHED STATE: the node within bounds, its rows readable, below
  -- the counter, and the table and the connected set kept since the
  -- start.
  record SI (sched : Sched Γ) (st : EvalSt e) : Set where
    constructor si
    field
      ni : NI (EvalSt.nodes st)
      ea : EA (EvalSt.registry st)
      lt : nid < nodeCt sched
      rm : KeepsC sl₀ cs₀ (Sched.slots sched) (EvalSt.connectedShares st)
  open SI public

  -- a drain's queue, bounded where it is the watched node's
  DQ : NodeId → ℕ → Sched Γ → EvalSt e → Set
  DQ a len sched st = SI sched st × (a ≡ nid → len ≤ W)

  NI-eq : ∀ {ts ts′ : List (NodeId × NodeState Γ)} → lookupNode nid ts′ ≡ lookupNode nid ts → NI ts → NI ts′
  NI-eq eq (nᵢ w f) = nᵢ (subst (λ h → waiting h ≤ W) (sym eq) w) (λ z → trans eq (f z))

  NI-off : ∀ {a : NodeId} {s : NodeState Γ} {ts} → (a ≡ᵇ nid) ≡ false → NI ts → NI (setNode a s ts)
  NI-off {a} {s} {ts} ne = NI-eq (set-above a nid s ts ne)

  NI-fresh : ∀ {c : NodeId} {s : NodeState Γ} {ts} → nid < c → NI ts → NI (setNode c s ts)
  NI-fresh {c} lt = NI-off {c} (<→≢ᵇ lt)

  NI-set : ∀ (a : NodeId) (s : NodeState Γ) (ts : List (NodeId × NodeState Γ))
         → NI ts → (a ≡ nid → (fed ≡ false → ⊥) × waiting (just s) ≤ W) → NI (setNode a s ts)
  NI-set a s ts ni′ ok with a ≡ᵇ nid in eq
  ... | false = NI-eq (set-above a nid s ts eq) ni′
  ... | true with ≡ᵇ→≡ a nid eq
  ...   | refl = nᵢ (subst (λ h → waiting h ≤ W) (sym (lookup-set nid s ts)) (proj₂ (ok refl)))
                     (λ f → ⊥-elim (proj₁ (ok refl) f))

  ea-sub : ∀ {R R′ : List (RegRow Γ t)} → (∀ {r} → r ∈ R′ → r ∈ R) → EA R → EA R′
  ea-sub sb ea′ r∈ = ea′ (sb r∈)

  row-ok : ∀ {rs : RegSrc Γ} {u rid} {p : Path Γ (regFloor rs) u t} → PI p → RowOK (rid , rs , u , p)
  row-ok {atSlot _}  pi = PI.pon pi , λ _ → pi
  row-ok {atDyn _ _} pi = PI.pon pi , tt

  ea-reg : ∀ {R : List (RegRow Γ t)} {ns : List (NodeId × NodeState Γ)} {u rid} {rs : RegSrc Γ}
             {p : Path Γ (regFloor rs) u t}
         → EA R → PI p
         → EA (if spentOn p ns then R else R ++ (rid , rs , u , p) ∷ [])
  ea-reg {R} {ns} {rid = rid} {rs = rs} {p = p} ea′ pi r∈ with spentOn p ns
  ... | true  = ea′ r∈
  ... | false with ∈-++⁻ R r∈
  ...   | inj₁ a           = ea′ a
  ...   | inj₂ (here refl) = row-ok {rs = rs} {rid = rid} pi

  -- AT THE START NO ROW READS A SHARE THE RUN WILL CONNECT, which is
  -- the rule's `linked` read at the table and set the run started from
  fresh-none : ∀ {sched : Sched Γ} {st : EvalSt e} → Sched.slots sched ≡ sl₀ → EvalSt.connectedShares st ≡ cs₀
             → (rs : RegSrc Γ) {u : _} (p : Path Γ (regFloor rs) u t) → SlotLinked sched st rs → FreshPI rs p
  fresh-none tb cm (atSlot j)  p lk (d , ok , eqd , nm) =
    ⊥-elim (subst T (trans (sym (lk (trans (cong (λ f → f j) tb) eqd))) (trans (cong (memberSource (toℕ j)) cm) nm)) tt)
  fresh-none tb cm (atDyn _ _) p lk = tt

  ea-start : ∀ {sched : Sched Γ} {st : EvalSt e} → Sched.slots sched ≡ sl₀ → EvalSt.connectedShares st ≡ cs₀
           → EndsAt nid x st → Linked sched st → EA (EvalSt.registry st)
  ea-start tb cm eak lk {r} r∈ = eak r∈ , fresh-none tb cm (proj₁ (proj₂ r)) (proj₂ (proj₂ (proj₂ r))) (lk r∈)

  -- the set the run started from is inside the one it holds, so a share
  -- unconnected now was unconnected then
  still-out : ∀ {cs : List Source} k → (∀ s → memberSource s cs₀ ≡ true → memberSource s cs ≡ true)
            → memberSource k cs ≡ false → memberSource k cs₀ ≡ false
  still-out k mono nm with memberSource k cs₀ in m
  ... | false = refl
  ... | true  = ⊥-elim (subst T (trans (sym (mono k m)) nm) tt)

  fresh-SI : ∀ {sched st} (ns : NodeState Γ) → SI sched st
           → SI (bumpNode sched) (installNode (nodeCt sched) ns st)
  fresh-SI ns s = si (NI-fresh (lt s) (ni s)) (ea s) (<-≤-trans (lt s) (n≤1+n _)) (rm s)

  kill-SI : ∀ (cur : Maybe NodeId) {sched st} → SI sched st
          → SI (proj₁ (switchKill {e = e} cur sched st)) (proj₂ (switchKill cur sched st))
  kill-SI nothing          s = s
  kill-SI (just v) {sched} {st} s = si (ni s) (ea-sub (kill-sub (just v) sched st) (ea s)) (lt s) (rm s)

  dying-SI : ∀ (i : Fin n) (fin : Bool) {sched st} → SI sched st → SI sched (shareDying i fin st)
  dying-SI i false s = s
  dying-SI i true  s = si (ni s) (ea s) (lt s) (rm s)

  finish-SI : ∀ (i : Fin n) (fin : Bool) r
            → SI (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
            → SI (proj₁ (proj₂ (shareFinish {e = e} i fin r))) (proj₂ (proj₂ (shareFinish i fin r)))
  finish-SI i false r                 s = s
  finish-SI i true  (emits , sc , st) s =
    si (ni s) (ea-sub (drop-sub (toℕ i) (EvalSt.registry st)) (ea s)) (lt s) (rm s)

  wrap-SI : ∀ (op : AllOp) (c : NodeId) (fin : Bool) {sched st} → (c ≡ᵇ nid) ≡ false → SI sched st
          → SI (proj₁ (proj₂ (thruWrap {e = e} op c fin (sched , st)))) (proj₂ (proj₂ (thruWrap op c fin (sched , st))))
  wrap-SI op c fin {sched} {st} ne s =
    let wrapped _ o sc = wrap-facts op c fin sched st
    in si (NI-eq (o nid ne) (ni s)) (ea-sub (wrap-reg op c fin sched st) (ea s))
          (subst (λ z → nid < nodeCt z) (sym sc) (lt s)) (keeps-trans (rm s) (thruWrap-keeps op c fin sched st))

  -- the finish's write at its flattener's node
  write-SI : ∀ {sched st} (a : NodeId) (ns : NodeState Γ) → (a ≡ nid → fed ≡ false → ⊥)
           → DQ a (waiting (just ns)) sched st
           → SI sched (record st { nodes = setNode a ns (EvalSt.nodes st) })
  write-SI a ns nf (s , w) = si (NI-set a ns _ (ni s) (λ eq → nf eq , w eq)) (ea s) (lt s) (rm s)

  -- the drain re-reads the node it spends, so its queue is the node's
  reread : ∀ {s : _} {a : NodeId} {sched st} {lim₂ act₂} {q₂ : List (Val Γ (obs s))} {od₂}
         → drainSt s (lookupNode a (EvalSt.nodes st)) ≡ (lim₂ , act₂ , q₂ , od₂)
         → SI sched st → DQ a (length q₂) sched st
  reread {s} {a} {st = st} eq w =
    w , λ e′ → ≤-trans (subst (λ p → length (proj₁ (proj₂ (proj₂ p))) ≤ waiting (lookupNode a (EvalSt.nodes st)))
                               eq (drain-waiting s (lookupNode a (EvalSt.nodes st))))
                       (subst (λ k → waiting (lookupNode k (EvalSt.nodes st)) ≤ W) (sym e′) (NI.nw (ni w)))

  -- a row a share admits at a sink at or above the terminus is off the
  -- watched node and ends above every sink the node's rows end at
  admit-PI : ∀ (i : Fin n) {R : List (RegRow Γ t)} → Clr x i → EA R
           → ∀ {a} → a ∈ shareAdmit i R → PI (proj₂ a)
  admit-PI i {R} c eak {a} a∈ =
    admit-row i R a∈ |>′ λ (r₀ , m , ek , ee) →
    let off = λ h → floor-miss x i (proj₂ a) c (trans (sym ee) (proj₁ (eak m) (subst T (sym (ek nid)) h))) in
    pᵢ (off-ok (proj₂ a) off) (λ h → ⊥-elim (off h)) (λ i′ eq → inj₁ (floor-clear x i (proj₂ a) c i′ eq))

  -- and a row a share the run connects admits is one the run registered
  admit-fresh : ∀ (i : Fin n) (R : List (RegRow Γ t)) → Fresh i → EA R
              → ∀ {a} → a ∈ shareAdmit i R → PI (proj₂ a)
  admit-fresh i [] f ea′ ()
  admit-fresh i ((rid , atDyn _ _ , _) ∷ R) f ea′ a∈ = admit-fresh i R f (λ m → ea′ (there m)) a∈
  admit-fresh i ((rid , atSlot j , (u , p)) ∷ R) f ea′ a∈ with i ≟ᶠ j | u ≟ᵗ lookup Γ i
  ... | no _     | _        = admit-fresh i R f (λ m → ea′ (there m)) a∈
  ... | yes _    | no _     = admit-fresh i R f (λ m → ea′ (there m)) a∈
  ... | yes refl | yes refl with a∈
  ...   | here refl = proj₂ (ea′ (here refl)) f
  ...   | there a∈′ = admit-fresh i R f (λ m → ea′ (there m)) a∈′

  admit : ∀ (i : Fin n) {R : List (RegRow Γ t)} → Sink i → EA R
        → ∀ {a} → a ∈ shareAdmit i R → PI (proj₂ a)
  admit i (inj₁ c) ea′ = admit-PI i c ea′
  admit i (inj₂ f) ea′ = admit-fresh i _ f ea′

  -- THE FOURTEEN-MEMBER INDUCTION.  Every clause matches a constructor
  -- and recurses on its sub-derivations, so the block descends
  -- structurally.
  -- STRUCTURAL SCC: subscribeE-floor subscribeSharedSlot-floor subscribeAll-floor subscribeInner-floor stepFrame-floor thruWalk-floor thruConsume-floor innerReact-floor innerFinish-floor mergeAllDrain-floor foldPath-floor dispatchShare-floor shareWalk-floor shareGo-floor
  subscribeE-floor : ∀ {u lo} {b : Val Γ (obs u)} {κ : Path Γ lo u t} {now}
                       {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out}
                   → subscribeE⇓ {e = e} b κ now sched st (out , sched′ , st′)
                   → PI κ → SI sched st → SI sched′ st′

  subscribeSharedSlot-floor : ∀ {lo} {i : Fin n} {d} {ok} {κ : Path Γ lo (lookup Γ i) t} {below} {now}
                                {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out}
                            → Sched.slots sched i ≡ shared d {ok = ok}
                            → subscribeSharedSlot⇓ {e = e} i d κ below now sched st (out , sched′ , st′)
                            → PI κ → SI sched st → SI sched′ st′

  subscribeAll-floor : ∀ {u lo} {op} {ns : NodeState Γ} {b : Val Γ (obs (echoᵗ u))} {κ : Path Γ lo u t} {now}
                         {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out}
                     → subscribeAll⇓ {e = e} op ns b κ now sched st (out , sched′ , st′)
                     → PI κ → SI sched st → SI sched′ st′

  subscribeInner-floor : ∀ {u lo} {op a} {κ : Path Γ lo u t} {now} {o : Val Γ (obs u)}
                           {sched sched′ : Sched Γ} {st st′ : EvalSt e} {inst out}
                       → subscribeInner⇓ {e = e} op a κ now o sched st (inst , out , sched′ , st′)
                       → PA a κ → SI sched st → SI sched′ st′

  stepFrame-floor : ∀ {s u lo} {f : Frame Γ s u} {κ : Path Γ lo u t} {now vals fin}
                      {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out vals′ fin′}
                  → stepFrame⇓ {e = e} now f κ vals fin sched st (out , vals′ , fin′ , sched′ , st′)
                  → PF f κ → SI sched st → SI sched′ st′

  thruWalk-floor : ∀ {u lo} {op a} {κ : Path Γ lo u t} {now} {vals : List (Val Γ (u +ᵗ obs u))}
                     {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out}
                 → thruWalk⇓ {e = e} op a κ now vals sched st (out , sched′ , st′)
                 → (a ≡ᵇ nid) ≡ false → PI κ → SI sched st → SI sched′ st′

  thruConsume-floor : ∀ {u lo} {op a} {κ : Path Γ lo u t} {now} {o : Val Γ (obs u)}
                        {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out}
                    → thruConsume⇓ {e = e} op a κ now o sched st (out , sched′ , st′)
                    → (a ≡ᵇ nid) ≡ false → PI κ → SI sched st → SI sched′ st′

  innerReact-floor : ∀ {s lo} {op a inst} {κ : Path Γ lo s t} {now} {vals : List (Val Γ s)}
                       {sched sched′ : Sched Γ} {st st′ : EvalSt e} {alive} {out vals′ fin}
                   → innerReact⇓ {e = e} op a inst κ now vals sched st alive (out , vals′ , fin , sched′ , st′)
                   → PF (from-inner op a inst) κ → SI sched st → SI sched′ st′

  innerFinish-floor : ∀ {s lo} {op a inst} {κ : Path Γ lo s t} {now} {vals : List (Val Γ s)}
                        {sched sched′ : Sched Γ} {st st′ : EvalSt e} {m} {out vals′ fin}
                    → innerFinish⇓ {e = e} op a inst κ now vals sched st m (out , vals′ , fin , sched′ , st′)
                    → PF (from-inner op a inst) κ → (a ≡ nid → waiting m ≤ W) → SI sched st → SI sched′ st′

  mergeAllDrain-floor : ∀ {s lo} {a} {κ : Path Γ lo s t} {now} {fuel lim act od} {q : List (Val Γ (obs s))}
                          {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out act′} {q′ : List (Val Γ (obs s))}
                      → mergeAllDrain⇓ {e = e} a κ now fuel lim act od q sched st (out , act′ , q′ , sched′ , st′)
                      → PA a κ → DQ a (length q) sched st → DQ a (length q′) sched′ st′

  foldPath-floor : ∀ {u lo} {κ : Path Γ lo u t} {now vals fin}
                     {sched sched′ : Sched Γ} {st st′ : EvalSt e} {emits}
                 → foldPath⇓ {e = e} now κ vals fin sched st (emits , sched′ , st′)
                 → PI κ → SI sched st → SI sched′ st′

  dispatchShare-floor : ∀ {lo} {i : Fin n} {below} {now vals fin} {sched : Sched Γ} {st : EvalSt e} {r}
                      → dispatchShare⇓ {e = e} {lo = lo} now i below vals fin sched st r
                      → Sink i → SI sched st → SI (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

  shareWalk-floor : ∀ {i : Fin n} {now vals fin} {sched : Sched Γ} {st : EvalSt e} {r}
                  → shareWalk⇓ {e = e} now i vals fin sched st r
                  → Sink i → SI sched st → SI (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

  shareGo-floor : ∀ {lo} {i : Fin n} {now vals fin} {ps : List (RegId × Path Γ lo (lookup Γ i) t)}
                    {sched : Sched Γ} {st : EvalSt e} {r}
                → shareGo⇓ {e = e} {lo = lo} now i vals fin ps sched st r
                → (∀ {a} → a ∈ ps → PI (proj₂ a)) → SI sched st → SI (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

  subscribeE-floor (subs-floor _ f)        ph s = foldPath-floor f ph s
  subscribeE-floor (subs-shared eq slot)   ph s = subscribeSharedSlot-floor eq slot ph s
  subscribeE-floor (subs-hot-done _ _ _ f) ph s = foldPath-floor f ph s
  subscribeE-floor {κ = κ} (subs-hot-live below _ _ refl) ph s =
    si (ni s) (ea-reg (ea s) (lower-PI below κ ph)) (lt s) (rm s)
  subscribeE-floor (subs-cold-sync _ _ f)  ph s = foldPath-floor f ph s
  subscribeE-floor (subs-cold-async _ _ refl refl refl f) ph s =
    foldPath-floor f ph (si (ni s) (ea-reg (ea s) ph) (lt s) (rm s))
  subscribeE-floor (subs-of f)             ph s = foldPath-floor f ph s
  subscribeE-floor (subs-empty f)          ph s = foldPath-floor f ph s
  subscribeE-floor (subs-takeWhile refl sub) ph s =
    subscribeE-floor sub (push (fresh-off (lt s)) (fresh-off (lt s)) ph) (fresh-SI _ s)
  subscribeE-floor (subs-batchSync refl sub f) ph s =
    let ph′ = push (fresh-off (lt s)) (fresh-off (lt s)) ph
        s₁  = subscribeE-floor sub ph′ (fresh-SI _ s)
    in foldPath-floor f ph′ (si (NI-fresh (lt s) (ni s₁)) (ea s₁) (lt s₁) (rm s₁))
  subscribeE-floor (subs-map sub)          ph s = subscribeE-floor sub (push (λ ()) (λ ()) ph) s
  subscribeE-floor (subs-scan refl sub)    ph s =
    subscribeE-floor sub (push (fresh-off (lt s)) (fresh-off (lt s)) ph) (fresh-SI _ s)
  subscribeE-floor (subs-flatten sa)       ph s = subscribeAll-floor sa ph s
  subscribeE-floor (subs-μ sub)            ph s = subscribeE-floor sub ph s
  subscribeE-floor {sched = sched} (subs-defer refl refl refl refl) ph s =
    let ph′ = push {f = thru-outer mergeAllᵒ (nodeCt sched)} {le = ≤-refl} (fresh-off (lt s)) (fresh-off (lt s)) ph
    in si (NI-fresh (lt s) (ni s)) (ea-reg (ea s) ph′) (<-≤-trans (lt s) (n≤1+n _)) (rm s)
  subscribeE-floor (subs-mint refl sub)    ph s = subscribeE-floor sub ph (si (ni s) (ea s) (lt s) (rm s))

  subscribeSharedSlot-floor eq (slot-spent _ f) ph s = foldPath-floor f ph s
  subscribeSharedSlot-floor {κ = κ} {below = below} eq (slot-join _ _ refl) ph s =
    si (ni s) (ea-reg (ea s) (lower-PI below κ ph)) (lt s) (rm s)
  subscribeSharedSlot-floor {i = i} {d = d} {ok = ok} {κ = κ} {below = below} {st = st} eq (slot-connect _ nm (connect refl sub)) ph s =
    subscribeE-floor sub (pᵢ tt (λ ()) λ { _ refl → inj₂ fr })
      (si (ni s) (ea-reg (ea s) (lower-PI below κ ph)) (lt s) (keeps-trans (rm s) (keeps-cons _ _ _)))
    where
    fr : Fresh i
    fr = d , ok , trans (cong (λ f → f i) (sym (KeepsC.table (rm s)))) eq , still-out {cs = EvalSt.connectedShares st} (toℕ i) (KeepsC.mem (rm s)) nm

  subscribeAll-floor (sub-all refl sub) ph s =
    subscribeE-floor sub (push (fresh-off (lt s)) (fresh-off (lt s)) ph) (fresh-SI _ s)

  subscribeInner-floor (inner refl sub) pa s =
    subscribeE-floor sub (fresh-PI (lt s) pa) (si (ni s) (ea s) (<-≤-trans (lt s) (n≤1+n _)) (rm s))

  stepFrame-floor step-map pf s = s
  stepFrame-floor (step-scan {fn = fn} {nid = c} {vals = vals} {fin} {sched} {st}) pf s =
    si (NI-eq (scanOff fn c vals fin sched st (lookupNode c (EvalSt.nodes st)) nid (notIn₁ {c} {nid} (proj₁ pf))) (ni s))
       (ea-sub (λ r∈ → subst (_ ∈_) (scanReg fn c vals fin sched st (lookupNode c (EvalSt.nodes st))) r∈) (ea s))
       (subst (nid <_) (sym (scanCt fn c vals fin sched st (lookupNode c (EvalSt.nodes st)))) (lt s))
       (keeps-trans (rm s) (scanDispatch-keeps fn c vals fin sched st (lookupNode c (EvalSt.nodes st))))
  stepFrame-floor (step-take {w = w} {nid = c} {vals = vals} {fin} {sched} {st}) pf s =
    si (NI-eq (takeOff w c (lookupNode c (EvalSt.nodes st)) vals fin sched st nid (notIn₁ {c} {nid} (proj₁ pf))) (ni s))
       (ea-sub (takeReg w c (lookupNode c (EvalSt.nodes st)) vals fin sched st) (ea s))
       (subst (nid <_) (sym (takeCt w c (lookupNode c (EvalSt.nodes st)) vals fin sched st)) (lt s))
       (keeps-trans (rm s) (takeDispatch-keeps w c vals fin sched st (lookupNode c (EvalSt.nodes st))))
  stepFrame-floor (step-batchSync {nid = c} {vals = vals} {fin} {sched} {st}) pf s =
    si (NI-eq (batchOff c vals fin sched st (lookupNode c (EvalSt.nodes st)) nid (notIn₁ {c} {nid} (proj₁ pf))) (ni s))
       (ea-sub (λ r∈ → subst (_ ∈_) (batchReg c vals fin sched st (lookupNode c (EvalSt.nodes st))) r∈) (ea s))
       (subst (nid <_) (sym (batchCt c vals fin sched st (lookupNode c (EvalSt.nodes st)))) (lt s))
       (keeps-trans (rm s) (batchDispatch-keeps c vals fin sched st (lookupNode c (EvalSt.nodes st))))
  stepFrame-floor (step-from-inner r) pf s = innerReact-floor r pf s
  stepFrame-floor (step-thru-outer {op = op} {nid = c} {fin = fin} w) pf s =
    wrap-SI op c fin (notIn₁ {c} {nid} (proj₁ pf)) (thruWalk-floor w (notIn₁ {c} {nid} (proj₁ pf)) (proj₂ (proj₂ pf)) s)

  thruWalk-floor walk-nil        ne ph s = s
  thruWalk-floor (walk-echo f w) ne ph s = thruWalk-floor w ne ph (foldPath-floor f ph s)
  thruWalk-floor (walk-cons c w) ne ph s = thruWalk-floor w ne ph (thruConsume-floor c ne ph s)

  thruConsume-floor {a = a} (consume-all-sub _ _ c) ne ph s =
    subscribeInner-floor c (thru-PA ne ph) (si (NI-off {a} ne (ni s)) (ea s) (lt s) (rm s))
  thruConsume-floor {a = a} (consume-all-enqueue _ _) ne ph s = si (NI-off {a} ne (ni s)) (ea s) (lt s) (rm s)
  thruConsume-floor (consume-all-nil _)       ne ph s = s
  thruConsume-floor {a = a} (consume-switch-sub {cur = cur} _ kl _ c) ne ph s =
    let s₁ = subst (λ p → SI (proj₁ p) (proj₂ p)) kl (kill-SI cur s)
    in subscribeInner-floor c (thru-PA ne ph) (si (NI-off {a} ne (ni s₁)) (ea s₁) (lt s₁) (rm s₁))
  thruConsume-floor (consume-switch-nil _)    ne ph s = s
  thruConsume-floor {a = a} (consume-exhaust-sub _ c) ne ph s =
    subscribeInner-floor c (thru-PA ne ph) (si (NI-off {a} ne (ni s)) (ea s) (lt s) (rm s))
  thruConsume-floor (consume-exhaust-nil _)   ne ph s = s

  innerReact-floor react-false     pf s = s
  innerReact-floor (react-alive _) pf s = s
  innerReact-floor {st = st} (react-dead _ f) pf s =
    innerFinish-floor f pf (λ eq → subst (λ k → waiting (lookupNode k (EvalSt.nodes st)) ≤ W) (sym eq) (NI.nw (ni s))) s

  innerFinish-floor {op = op} {a} {inst} (finish-all-drain {lim = lim} {od = od} {act′ = act′} {q′ = q′} fp dr) pf wm s =
    write-SI a (mergeAll-st lim act′ q′ od) (fi-inl {op = op} {j = inst} pf)
      (mergeAllDrain-floor dr (pa-of {op = op} {j = inst} pf) (foldPath-floor fp (proj₂ (proj₂ pf)) s , wm))
  innerFinish-floor {op = op} {a} {inst} (finish-switch-clear {od = od} _) pf wm s = write-SI a (switch-st nothing od) (fi-inl {op = op} {j = inst} pf) (s , λ _ → z≤n)
  innerFinish-floor {op = op} {a} {inst} (finish-exhaust-clear {od = od}) pf wm s = write-SI a (exhaust-st false od) (fi-inl {op = op} {j = inst} pf) (s , λ _ → z≤n)
  innerFinish-floor (finish-nil _) pf wm s = s

  mergeAllDrain-floor drain-spent       pa sw      = sw
  mergeAllDrain-floor drain-nil         pa (s , _) = s , λ _ → z≤n
  mergeAllDrain-floor (drain-no-room _) pa sw      = sw
  mergeAllDrain-floor {a = a} (drain-room _ c eq dr) pa (s , w) =
    mergeAllDrain-floor dr pa
      (reread eq (subscribeInner-floor c pa
        (si (NI-set a _ _ (ni s) (λ e′ → pa-inl pa e′ , ≤-trans (n≤1+n _) (w e′))) (ea s) (lt s) (rm s))))

  foldPath-floor fold-root                ph s = s
  foldPath-floor (fold-sink {i = i} d)    ph s = dispatchShare-floor d (PI.pcl ph i refl) s
  foldPath-floor (fold-step sf r)         ph s =
    foldPath-floor r (proj₂ (proj₂ (pf-of ph))) (stepFrame-floor sf (pf-of ph) s)

  dispatchShare-floor (disp {i = i} {fin = fin} w) c s =
    finish-SI i fin _ (shareWalk-floor w c (dying-SI i fin s))

  shareWalk-floor walk-nil c s = s
  shareWalk-floor {i = i} (walk-end g) c s =
    shareGo-floor g (admit i c (ea s)) (si (ni s) (ea s) (lt s) (rm s))
  shareWalk-floor {i = i} (walk-more g w) c s =
    shareWalk-floor w c (shareGo-floor g (admit i c (ea s)) s)

  shareGo-floor go-nil       h s = s
  shareGo-floor (go-cut _ g) h s = shareGo-floor g (λ m → h (there m)) s
  shareGo-floor (go-live _ f g) h s =
    shareGo-floor g (λ m → h (there m)) (foldPath-floor f (h (here refl)) (si (ni s) (ea s) (lt s) (rm s)))

------------------------------------------------------------------
-- AND THE COUNTER NEVER FALLS, which is the half of `Kept` no node
-- watch can give: a run's writes to the mint are its own bumps.
------------------------------------------------------------------

-- the share's retirement sweeps rows and the live set, and no counter
finish-ct : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (i : Fin n) (fin : Bool) r
          → nodeCt (proj₁ (proj₂ r)) ≤ nodeCt (proj₁ (proj₂ (shareFinish {e = e} i fin r)))
finish-ct i false r                 = ≤-refl
finish-ct i true  (emits , sc , st) = ≤-refl

-- STRUCTURAL SCC: subscribeE-ct subscribeSharedSlot-ct subscribeAll-ct subscribeInner-ct stepFrame-ct thruWalk-ct thruConsume-ct innerReact-ct innerFinish-ct mergeAllDrain-ct foldPath-ct dispatchShare-ct shareWalk-ct shareGo-ct
subscribeE-ct : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {b : Val Γ (obs u)} {κ : Path Γ lo u t} {now}
                  {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out}
              → subscribeE⇓ {e = e} b κ now sched st (out , sched′ , st′) → nodeCt sched ≤ nodeCt sched′

subscribeSharedSlot-ct : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
                           {below} {now} {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out}
                       → subscribeSharedSlot⇓ {e = e} i d κ below now sched st (out , sched′ , st′)
                       → nodeCt sched ≤ nodeCt sched′

subscribeAll-ct : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {op} {ns : NodeState Γ} {b : Val Γ (obs (echoᵗ u))}
                    {κ : Path Γ lo u t} {now} {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out}
                → subscribeAll⇓ {e = e} op ns b κ now sched st (out , sched′ , st′) → nodeCt sched ≤ nodeCt sched′

subscribeInner-ct : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {op a} {κ : Path Γ lo u t} {now}
                      {o : Val Γ (obs u)} {sched sched′ : Sched Γ} {st st′ : EvalSt e} {inst out}
                  → subscribeInner⇓ {e = e} op a κ now o sched st (inst , out , sched′ , st′)
                  → nodeCt sched ≤ nodeCt sched′

stepFrame-ct : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo} {f : Frame Γ s u} {κ : Path Γ lo u t} {now vals fin}
                 {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out vals′ fin′}
             → stepFrame⇓ {e = e} now f κ vals fin sched st (out , vals′ , fin′ , sched′ , st′)
             → nodeCt sched ≤ nodeCt sched′

thruWalk-ct : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {op a} {κ : Path Γ lo u t} {now}
                {vals : List (Val Γ (u +ᵗ obs u))} {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out}
            → thruWalk⇓ {e = e} op a κ now vals sched st (out , sched′ , st′) → nodeCt sched ≤ nodeCt sched′

thruConsume-ct : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {op a} {κ : Path Γ lo u t} {now}
                   {o : Val Γ (obs u)} {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out}
               → thruConsume⇓ {e = e} op a κ now o sched st (out , sched′ , st′) → nodeCt sched ≤ nodeCt sched′

innerReact-ct : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo} {op a inst} {κ : Path Γ lo s t} {now}
                  {vals : List (Val Γ s)} {sched sched′ : Sched Γ} {st st′ : EvalSt e} {alive} {out vals′ fin}
              → innerReact⇓ {e = e} op a inst κ now vals sched st alive (out , vals′ , fin , sched′ , st′)
              → nodeCt sched ≤ nodeCt sched′

innerFinish-ct : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo} {op a inst} {κ : Path Γ lo s t} {now}
                   {vals : List (Val Γ s)} {sched sched′ : Sched Γ} {st st′ : EvalSt e} {m} {out vals′ fin}
               → innerFinish⇓ {e = e} op a inst κ now vals sched st m (out , vals′ , fin , sched′ , st′)
               → nodeCt sched ≤ nodeCt sched′

mergeAllDrain-ct : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo} {a} {κ : Path Γ lo s t} {now} {fuel lim act od q}
                     {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out act′ q′}
                 → mergeAllDrain⇓ {e = e} {s = s} a κ now fuel lim act od q sched st (out , act′ , q′ , sched′ , st′)
                 → nodeCt sched ≤ nodeCt sched′

foldPath-ct : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {κ : Path Γ lo u t} {now vals fin}
                {sched sched′ : Sched Γ} {st st′ : EvalSt e} {emits}
            → foldPath⇓ {e = e} now κ vals fin sched st (emits , sched′ , st′) → nodeCt sched ≤ nodeCt sched′

dispatchShare-ct : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo} {i : Fin n} {below} {now vals fin}
                     {sched : Sched Γ} {st : EvalSt e} {r}
                 → dispatchShare⇓ {e = e} {lo = lo} now i below vals fin sched st r
                 → nodeCt sched ≤ nodeCt (proj₁ (proj₂ r))

shareWalk-ct : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {i : Fin n} {now vals fin} {sched : Sched Γ} {st : EvalSt e} {r}
             → shareWalk⇓ {e = e} now i vals fin sched st r → nodeCt sched ≤ nodeCt (proj₁ (proj₂ r))

shareGo-ct : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo} {i : Fin n} {now vals fin}
               {ps : List (RegId × Path Γ lo (lookup Γ i) t)} {sched : Sched Γ} {st : EvalSt e} {r}
           → shareGo⇓ {e = e} {lo = lo} now i vals fin ps sched st r → nodeCt sched ≤ nodeCt (proj₁ (proj₂ r))

subscribeE-ct (subs-floor _ f)                   = foldPath-ct f
subscribeE-ct (subs-shared _ slot)               = subscribeSharedSlot-ct slot
subscribeE-ct (subs-hot-done _ _ _ f)            = foldPath-ct f
subscribeE-ct (subs-hot-live _ _ _ refl)         = ≤-refl
subscribeE-ct (subs-cold-sync _ _ f)             = foldPath-ct f
subscribeE-ct (subs-cold-async _ _ refl refl refl f) = foldPath-ct f
subscribeE-ct (subs-of f)                        = foldPath-ct f
subscribeE-ct (subs-empty f)                     = foldPath-ct f
subscribeE-ct (subs-takeWhile refl sub)          = ≤-trans (n≤1+n _) (subscribeE-ct sub)
subscribeE-ct (subs-batchSync refl sub f)        = ≤-trans (n≤1+n _) (≤-trans (subscribeE-ct sub) (foldPath-ct f))
subscribeE-ct (subs-map sub)                     = subscribeE-ct sub
subscribeE-ct (subs-scan refl sub)               = ≤-trans (n≤1+n _) (subscribeE-ct sub)
subscribeE-ct (subs-flatten sa)                  = subscribeAll-ct sa
subscribeE-ct (subs-μ sub)                       = subscribeE-ct sub
subscribeE-ct (subs-defer refl refl refl refl)   = n≤1+n _
subscribeE-ct (subs-mint refl sub)               = subscribeE-ct sub

subscribeSharedSlot-ct (slot-spent _ f)                  = foldPath-ct f
subscribeSharedSlot-ct (slot-join _ _ refl)              = ≤-refl
subscribeSharedSlot-ct (slot-connect _ _ (connect refl sub)) = subscribeE-ct sub

subscribeAll-ct (sub-all refl sub) = ≤-trans (n≤1+n _) (subscribeE-ct sub)

subscribeInner-ct (inner refl sub) = ≤-trans (n≤1+n _) (subscribeE-ct sub)

stepFrame-ct step-map = ≤-refl
stepFrame-ct (step-scan {fn = fn} {nid = c} {vals = vals} {fin} {sched} {st}) =
  ≤-reflexive (sym (scanCt fn c vals fin sched st (lookupNode c (EvalSt.nodes st))))
stepFrame-ct (step-take {w = w} {nid = c} {vals = vals} {fin} {sched} {st}) = ≤-reflexive (sym (takeCt w c (lookupNode c (EvalSt.nodes st)) vals fin sched st))
stepFrame-ct (step-batchSync {nid = c} {vals = vals} {fin} {sched} {st}) =
  ≤-reflexive (sym (batchCt c vals fin sched st (lookupNode c (EvalSt.nodes st))))
stepFrame-ct (step-from-inner r) = innerReact-ct r
stepFrame-ct (step-thru-outer {op = op} {nid = c} {fin = fin} {sched′ = sched′} {st′ = st′} w) =
  let wrapped _ _ sc = wrap-facts op c fin sched′ st′
  in ≤-trans (thruWalk-ct w) (≤-reflexive (cong nodeCt (sym sc)))

thruWalk-ct walk-nil        = ≤-refl
thruWalk-ct (walk-echo f w) = ≤-trans (foldPath-ct f) (thruWalk-ct w)
thruWalk-ct (walk-cons c w) = ≤-trans (thruConsume-ct c) (thruWalk-ct w)

thruConsume-ct (consume-all-sub _ _ c)   = subscribeInner-ct c
thruConsume-ct (consume-all-enqueue _ _) = ≤-refl
thruConsume-ct (consume-all-nil _)       = ≤-refl
thruConsume-ct (consume-switch-sub {cur = nothing} _ refl _ c) = subscribeInner-ct c
thruConsume-ct (consume-switch-sub {cur = just _}  _ refl _ c) = subscribeInner-ct c
thruConsume-ct (consume-switch-nil _)    = ≤-refl
thruConsume-ct (consume-exhaust-sub _ c) = subscribeInner-ct c
thruConsume-ct (consume-exhaust-nil _)   = ≤-refl

innerReact-ct react-false      = ≤-refl
innerReact-ct (react-alive _)  = ≤-refl
innerReact-ct (react-dead _ f) = innerFinish-ct f

innerFinish-ct (finish-all-drain fp dr) = ≤-trans (foldPath-ct fp) (mergeAllDrain-ct dr)
innerFinish-ct (finish-switch-clear _)  = ≤-refl
innerFinish-ct finish-exhaust-clear     = ≤-refl
innerFinish-ct (finish-nil _)           = ≤-refl

mergeAllDrain-ct drain-spent            = ≤-refl
mergeAllDrain-ct drain-nil              = ≤-refl
mergeAllDrain-ct (drain-no-room _)      = ≤-refl
mergeAllDrain-ct (drain-room _ c _ dr)  = ≤-trans (subscribeInner-ct c) (mergeAllDrain-ct dr)

foldPath-ct fold-root        = ≤-refl
foldPath-ct (fold-sink d)    = dispatchShare-ct d
foldPath-ct (fold-step sf r) = ≤-trans (stepFrame-ct sf) (foldPath-ct r)

dispatchShare-ct (disp {i = i} {fin = fin} w) = ≤-trans (shareWalk-ct w) (finish-ct i fin _)

shareWalk-ct walk-nil        = ≤-refl
shareWalk-ct (walk-end g)    = shareGo-ct g
shareWalk-ct (walk-more g w) = ≤-trans (shareGo-ct g) (shareWalk-ct w)

shareGo-ct go-nil          = ≤-refl
shareGo-ct (go-cut _ g)    = shareGo-ct g
shareGo-ct (go-live _ f g) = ≤-trans (foldPath-ct f) (shareGo-ct g)

------------------------------------------------------------------
-- THE THREE FACTS THE RAW FOLD'S BASE STANDS ON.
------------------------------------------------------------------

-- A RAW FOLD KEEPS THE TERMINUS: a node off the path whose rows end
-- where the path does is written by nothing, and its rows still end
-- there.
raw-at : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {κ : Path Γ lo u t}
           {now vals fin sched st out sched′ st′}
       → foldPath⇓ {e = e} now κ vals fin sched st (out , sched′ , st′)
       → Linked sched st
       → ∀ k → k < nodeCt sched → (T (pathHasNode k κ) → ⊥) → EndsAt k (endOf κ) st
       → lookupNode k (EvalSt.nodes st′) ≡ lookupNode k (EvalSt.nodes st) × EndsAt k (endOf κ) st′
raw-at {e = e} {κ = κ} {sched = sched} {st = st} d lk k k< off eak =
  NI.nh (ni s′) refl , (λ r∈ th → proj₁ (ea s′ r∈) th)
  where
  open Watch {e = e} false k (endOf κ) (waiting (lookupNode k (EvalSt.nodes st)))
             (lookupNode k (EvalSt.nodes st)) (Sched.slots sched) (EvalSt.connectedShares st)
  s′ = foldPath-floor d (pᵢ (off-ok κ off) (λ h → ⊥-elim (off h)) (λ i eq → inj₁ (clear-self (endOf κ) i eq)))
         (si (nᵢ ≤-refl (λ _ → refl)) (ea-start refl refl eak lk) k< (keeps-refl _ _))

raw-kept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {κ : Path Γ lo u t}
             {now vals fin sched st out sched′ st′}
         → foldPath⇓ {e = e} now κ vals fin sched st (out , sched′ , st′)
         → Linked sched st
         → ∀ {pfs} → Kept κ (standing pfs) sched st sched′ st′
raw-kept d lk =
    foldPath-ct d
  , (λ k k< off eak → proj₁ (raw-at d lk k k< off eak))
  , (λ k k< off eak → proj₂ (raw-at d lk k k< off eak))

-- A MERGE'S QUEUE DOES NOT REFILL WHILE ONE OF ITS INNERS RUNS: its
-- node is written only by its own inners' finishes, each of which
-- drains the queue it read and writes back no more than it left.
refill-bounded : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u ℓ} (op : AllOp) (nid : NodeId)
                   (κ : Path Γ ℓ u t) {o : Val Γ (obs u)} {now} {sched : Sched Γ} {st : EvalSt e} {r}
               → subscribeE⇓ {e = e} o (from-inner op nid (nodeCt sched) ↠[ ≤-refl ] κ) now (bumpNode sched) st r
               → NodeOn nid κ sched st → Linked sched st
               → ∀ {h} → lookupNode nid (EvalSt.nodes st) ≡ h
               → waiting (lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r)))) ≤ waiting h
refill-bounded {e = e} op nid κ {sched = sched} {st} d nd lk {h} eq =
  NI.nw (ni (subscribeE-floor d (pᵢ ((λ ()) , off-ok κ (off-path nd)) (λ _ → refl) (λ i eq′ → inj₁ (clear-self (endOf κ) i eq′)))
              (si (nᵢ (subst (λ z → waiting z ≤ waiting h) (sym eq) ≤-refl) (λ ()))
                  (ea-start refl refl (at-end nd) lk) (<-≤-trans (node-below nd) (n≤1+n _)) (keeps-refl _ _))))
  where open Watch {e = e} true nid (endOf κ) (waiting h) h (Sched.slots sched) (EvalSt.connectedShares st)

-- AND A RAW FOLD FROM AN INNER'S EXIT FRAME DOES NOT REFILL ITS MERGE'S
-- QUEUE, for the same reason.
fold-refill-bounded : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u ℓ} (op : AllOp) (nid inst : NodeId)
                        (κ : Path Γ ℓ u t) {now vals fin} {sched : Sched Γ} {st : EvalSt e} {r}
                    → foldPath⇓ {e = e} now (from-inner {s = u} op nid inst ↠[ ≤-refl ] κ) vals fin sched st r
                    → Sound (from-inner op nid inst ↠[ ≤-refl ] κ) sched st
                    → waiting (lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r)))) ≤ waiting (lookupNode nid (EvalSt.nodes st))
fold-refill-bounded {e = e} op nid inst κ {sched = sched} {st} d so =
  NI.nw (ni (foldPath-floor d (pᵢ ((λ ()) , off-ok κ (proj₁ (distinct so) nid (self-node nid (inst ∷ []))))
                                  (λ _ → refl) (λ i eq → inj₁ (clear-self (endOf κ) i eq)))
              (si (nᵢ ≤-refl (λ ())) (ea-start refl refl (ends so nid on) (linked (ruled so)))
                  (fresh-path so nid on) (keeps-refl _ _))))
  where
  on = ∨-Tˡ {b = pathHasNode nid κ} (self-node nid (inst ∷ []))
  open Watch {e = e} true nid (endOf κ) (waiting (lookupNode nid (EvalSt.nodes st)))
             (lookupNode nid (EvalSt.nodes st)) (Sched.slots sched) (EvalSt.connectedShares st)
