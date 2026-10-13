-- WHAT A WALK DOES TO THE REGISTRY, THE DYING LIST AND THE COMPLETED
-- LIST, STATED SO THAT TWO WALKS IN A ROW COMPOSE.  The fact a consumer
-- wants is `quiet` alone -- no row of a source dying at the end that
-- was not dying at the start -- but `quiet` does not compose: a row
-- registered by the second walk can name a source the first one
-- killed.  The other four conjuncts are exactly what closes that:
-- a source newly dying is a slot the walk completed, a completed
-- source stays completed, and a new row is either minted at or above
-- the counter or sits on a slot not yet completed.
--
-- IT IS STATED OVER THE FIELDS RATHER THAN OVER THE STATES, as
-- `Rx.Evaluator.Keeps` is and for its reason: a step rebuilds its state
-- by record update, and only the projections out of one reduce.
--
-- WHILE THE SOURCE COUNTER STANDS ABOVE EVERY SLOT.  A share dies under
-- its slot's number and a minted source takes the counter's, so only
-- the counter keeps a row minted after a share's end from naming it.
--
-- REFUTED: `Refuted.Walk-Quiet-Mint` -- `quiet` without the counter:
--   the counter lowered to the share's slot, and a `defer` subscribed
--   after the share's end.
module Rx.Evaluator.Quiet where

open import Data.Bool using (Bool; true; false; T)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_; _<_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-≤-trans; <-irrefl; n≤1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Decide using (≡ᵇ→≡; ≡ᵇ-refl)
open import Rx.Exp using (Ctx; Closed; Val; FnClo; obs; _×ᵗ_; _+ᵗ_; boolᵗ; _≟ᵗ_)
open import Rx.Mint using (counter; sourceᵏ)
open import Rx.Evaluator using (Sched; EvalSt; NodeId; NodeState; AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ;
  RegId; RegRow; RegSrc; atSlot; atDyn; lowerFloor; regFloor; Path; Frame; echoᵗ; regSource; sameSource; memberSource; register; cutThrough; dropSource;
  installNode; switchKill; scanDispatch; takeDispatch; batchDispatch; thruWrap;
  cell-st; take-st; batchSync-st; mergeAll-st; switch-st; exhaust-st; lookupNode; takeVals)
open import Rx.Evaluator.Domain using (subscribeE⇓; subscribeInner⇓; thruConsume⇓;
  thruWalk⇓; mergeAllDrain⇓; innerFinish⇓; innerReact⇓; stepFrame⇓;
  subscribeAll⇓; sharedConnect⇓; subscribeSharedSlot⇓;
  foldPath⇓; dispatchShare⇓; shareWalk⇓; shareGo⇓; chainStep⇓; cascadeGo⇓;
  subs-floor; subs-shared; subs-hot-done; subs-hot-live; subs-cold-sync;
  subs-cold-async; subs-of; subs-empty; subs-map; subs-takeWhile;
  subs-batchSync; subs-scan; subs-flatten;
  subs-μ; subs-defer; subs-mint;
  inner; consume-all-sub; consume-all-enqueue; consume-all-nil; consume-switch-sub;
  consume-switch-nil; consume-exhaust-sub; consume-exhaust-nil;
  walk-nil; walk-echo; walk-cons; drain-spent; drain-nil; drain-no-room; drain-room;
  finish-all-drain; finish-switch-clear; finish-exhaust-clear; finish-nil;
  react-false; react-alive; react-dead;
  step-map; step-scan; step-take; step-batchSync; step-from-inner; step-thru-outer;
  sub-all; connect;
  slot-spent; slot-join; slot-connect;
  disp; walk-end; walk-more; go-nil; go-cut; go-live;
  fold-root; fold-sink; fold-step; chain-step; casc-nil; casc-cut; casc-live)
open import Rx.Evaluator.Reducible.Support using (∈-register; cut-sub)

-- a row's source
srcOf : ∀ {m} {Δ : Ctx m} {u} → RegRow Δ u → ℕ
srcOf x = regSource (proj₁ (proj₂ x))

record QuietC {m} {Δ : Ctx m} {u} (c c′ : ℕ) (done done′ dy dy′ : List ℕ)
              (reg reg′ : List (RegRow Δ u)) : Set where
  field
    mint-up : c ≤ c′
    done-up : ∀ s → memberSource s done ≡ true → memberSource s done′ ≡ true
    dies    : ∀ s → memberSource s dy′ ≡ true
            → memberSource s dy ≡ true ⊎ (s < m × memberSource s done′ ≡ true)
    rows    : ∀ {x} → x ∈ reg′
            → x ∈ reg ⊎ c ≤ srcOf x ⊎ (srcOf x < m × memberSource (srcOf x) done ≡ false)
    quiet   : ∀ {x} → x ∈ reg′ → memberSource (srcOf x) dy′ ≡ true → memberSource (srcOf x) dy ≡ true

-- THE FIELDS, NAMED ONCE
Quiet : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} → Sched Δ → EvalSt e → Sched Δ → EvalSt e → Set
Quiet sched st sched′ st′ =
  QuietC (counter (Sched.mint sched) sourceᵏ) (counter (Sched.mint sched′) sourceᵏ)
         (EvalSt.completedSources st) (EvalSt.completedSources st′)
         (EvalSt.dying st) (EvalSt.dying st′)
         (EvalSt.registry st) (EvalSt.registry st′)

-- a member of a cons is its head or a member of its tail
mem-∷ : ∀ s y L → memberSource s (y ∷ L) ≡ true → s ≡ y ⊎ memberSource s L ≡ true
mem-∷ s y L h with s ≡ᵇ y in eq
... | true  = inj₁ (≡ᵇ→≡ s y eq)
... | false = inj₂ h

mem-there : ∀ s y L → memberSource s L ≡ true → memberSource s (y ∷ L) ≡ true
mem-there s y L h with s ≡ᵇ y
... | true  = refl
... | false = h

mem-here : ∀ s L → memberSource s (s ∷ L) ≡ true
mem-here s L rewrite ≡ᵇ-refl s = refl

-- what the later list keeps, the earlier one lacked only if the later lacks it
lacks : ∀ {b b′} → (b ≡ true → b′ ≡ true) → b′ ≡ false → b ≡ false
lacks {false} _ _ = refl
lacks {true}  f e = trans (sym (f refl)) e

-- a row the drop keeps is not the dropped source's
drop-off : ∀ {m} {Δ : Ctx m} {u} s (K : List (RegRow Δ u)) {x} → x ∈ dropSource s K
         → sameSource s (srcOf x) ≡ false × x ∈ K
drop-off s [] ()
drop-off s ((rid , c , y) ∷ K) x∈ with sameSource s (regSource c) in eq
... | true  = let d , m = drop-off s K x∈ in d , there m
drop-off s ((rid , c , y) ∷ K) (here refl) | false = eq , here refl
drop-off s ((rid , c , y) ∷ K) (there x∈)  | false = let d , m = drop-off s K x∈ in d , there m

-- a step that moves only the counter, upward
quiet-mint : ∀ {m} {Δ : Ctx m} {u} {c c′ done dy} {reg : List (RegRow Δ u)}
           → c ≤ c′ → QuietC c c′ done done dy dy reg reg
quiet-mint le = record { mint-up = le ; done-up = λ _ h → h ; dies = λ _ h → inj₁ h
                       ; rows = inj₁ ; quiet = λ _ h → h }

quiet-refl : ∀ {m} {Δ : Ctx m} {u} {c done dy} {reg : List (RegRow Δ u)}
           → QuietC c c done done dy dy reg reg
quiet-refl = quiet-mint ≤-refl

-- the spend completes a source and touches nothing else
quiet-spend : ∀ {m} {Δ : Ctx m} {u} {c s done dy} {reg : List (RegRow Δ u)}
            → QuietC c c done (s ∷ done) dy dy reg reg
quiet-spend {s = s} {done} = record { mint-up = ≤-refl ; done-up = λ x h → mem-there x s done h
                                    ; dies = λ _ h → inj₁ h ; rows = inj₁ ; quiet = λ _ h → h }

-- a cut keeps a sublist
quiet-cut : ∀ {m} {Δ : Ctx m} {u} {c done dy} (v : NodeId) (reg : List (RegRow Δ u))
          → QuietC c c done done dy dy reg (proj₁ (cutThrough v reg))
quiet-cut v reg = record { mint-up = ≤-refl ; done-up = λ _ h → h ; dies = λ _ h → inj₁ h
                         ; rows = λ {x} x∈ → inj₁ (cut-sub v reg x x∈) ; quiet = λ _ h → h }

-- A REGISTRATION ADDS ONE ROW, fresh or on a slot not yet completed
quiet-register : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {w} {st : EvalSt e} {c c′}
                   (rid : RegId) (rs : RegSrc Δ) (p : Path Δ (regFloor rs) w u)
               → c ≤ c′
               → c ≤ regSource rs ⊎ (regSource rs < m × memberSource (regSource rs) (EvalSt.completedSources st) ≡ false)
               → QuietC c c′ (EvalSt.completedSources st) (EvalSt.completedSources st)
                        (EvalSt.dying st) (EvalSt.dying st)
                        (EvalSt.registry st) (EvalSt.registry (register rid rs p st))
quiet-register {m} {w = w} {st = st} {c} rid rs p le new = record
  { mint-up = le ; done-up = λ _ h → h ; dies = λ _ h → inj₁ h
  ; rows = λ x∈ → row (∈-register {st = st} rid rs p x∈)
  ; quiet = λ _ h → h }
  where
    row : ∀ {x} → x ∈ EvalSt.registry st ⊎ x ≡ (rid , rs , w , p)
        → x ∈ EvalSt.registry st ⊎ c ≤ srcOf x ⊎ (srcOf x < m × memberSource (srcOf x) (EvalSt.completedSources st) ≡ false)
    row (inj₁ x∈)  = inj₁ x∈
    row (inj₂ refl) = inj₂ new

-- TWO STEPS IN A ROW, the second taken at the counter the first left
then : ∀ {m} {Δ : Ctx m} {u} {c c₁ c₂ d d₁ d₂ y y₁ y₂} {r r₁ r₂ : List (RegRow Δ u)}
     → m ≤ c → QuietC c c₁ d d₁ y y₁ r r₁ → (m ≤ c₁ → QuietC c₁ c₂ d₁ d₂ y₁ y₂ r₁ r₂)
     → QuietC c c₂ d d₂ y y₂ r r₂
QuietC.mint-up (then h q k) = ≤-trans (QuietC.mint-up q) (QuietC.mint-up (k (≤-trans h (QuietC.mint-up q))))
QuietC.done-up (then h q k) s x =
  QuietC.done-up (k (≤-trans h (QuietC.mint-up q))) s (QuietC.done-up q s x)
QuietC.dies (then h q k) s x with QuietC.dies (k (≤-trans h (QuietC.mint-up q))) s x
... | inj₂ z = inj₂ z
... | inj₁ x₁ with QuietC.dies q s x₁
...   | inj₁ x₀       = inj₁ x₀
...   | inj₂ (lt , d) = inj₂ (lt , QuietC.done-up (k (≤-trans h (QuietC.mint-up q))) s d)
QuietC.rows (then h q k) {x} x∈ with QuietC.rows (k (≤-trans h (QuietC.mint-up q))) x∈
... | inj₁ x∈₁                = QuietC.rows q x∈₁
... | inj₂ (inj₁ le)          = inj₂ (inj₁ (≤-trans (QuietC.mint-up q) le))
... | inj₂ (inj₂ (lt , nd))   = inj₂ (inj₂ (lt , lacks (QuietC.done-up q (srcOf x)) nd))
QuietC.quiet (then h q k) {x} x∈ w with QuietC.rows (k (≤-trans h (QuietC.mint-up q))) x∈
                                   | QuietC.quiet (k (≤-trans h (QuietC.mint-up q))) x∈ w
... | inj₁ x∈₁              | w₁ = QuietC.quiet q x∈₁ w₁
... | inj₂ (inj₁ le)        | w₁ with QuietC.dies q (srcOf x) w₁
...   | inj₁ w₀       = w₀
...   | inj₂ (lt , _) = ⊥-elim (<-irrefl refl (<-≤-trans lt (≤-trans h (≤-trans (QuietC.mint-up q) le))))
QuietC.quiet (then h q k) {x} x∈ w | inj₂ (inj₂ (lt , nd)) | w₁ with QuietC.dies q (srcOf x) w₁
...   | inj₁ w₀      = w₀
...   | inj₂ (_ , d) = ⊥-elim (subst T (trans (sym d) nd) tt)

-- A SHARE'S END: its slot joins the dying list, the walk spent it, and
-- the finish drops its rows
quiet-end : ∀ {m} {Δ : Ctx m} {u} {c c′ d d′ y y′} {r r′ : List (RegRow Δ u)} (i : Fin m)
          → QuietC c c′ d d′ (toℕ i ∷ y) y′ r r′ → memberSource (toℕ i) d′ ≡ true
          → QuietC c c′ d d′ y y′ r (dropSource (toℕ i) r′)
QuietC.mint-up (quiet-end i q sp) = QuietC.mint-up q
QuietC.done-up (quiet-end i q sp) = QuietC.done-up q
QuietC.dies (quiet-end {y = y} i q sp) s w with QuietC.dies q s w
... | inj₂ z = inj₂ z
... | inj₁ w₀ with mem-∷ s (toℕ i) y w₀
...   | inj₁ refl = inj₂ (toℕ<n i , sp)
...   | inj₂ w₁   = inj₁ w₁
QuietC.rows (quiet-end {r′ = r′} i q sp) {x} x∈ = QuietC.rows q (proj₂ (drop-off (toℕ i) r′ x∈))
QuietC.quiet (quiet-end {y = y} {r′ = r′} i q sp) {x} x∈ w
  with mem-∷ (srcOf x) (toℕ i) y (QuietC.quiet q (proj₂ (drop-off (toℕ i) r′ x∈)) w)
... | inj₂ w₁ = w₁
... | inj₁ eq = ⊥-elim (subst T (trans (sym (≡ᵇ-refl (toℕ i)))
                   (subst (λ z → sameSource (toℕ i) z ≡ false) eq (proj₁ (drop-off (toℕ i) r′ x∈)))) tt)

-- the switch's cut keeps a sublist
switchKill-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                     (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e)
                     {sched₁ st₁}
                 → switchKill {e = e} cur sched st ≡ (sched₁ , st₁)
                 → Quiet {e = e} sched st sched₁ st₁
switchKill-quiet nothing  sched st refl = quiet-refl
switchKill-quiet (just v) sched st refl = quiet-cut v (EvalSt.registry st)

-- the fold's dispatch rewrites its own node
scanDispatch-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
                       (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId)
                       (vals : List (Val Γ s)) (fin : Bool)
                       (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
                   → Quiet {e = e} sched st
                       (proj₁ (proj₂ (proj₂
                         (scanDispatch {e = e} fn nid vals fin sched st m))))
                       (proj₂ (proj₂ (proj₂
                         (scanDispatch {e = e} fn nid vals fin sched st m))))
scanDispatch-quiet {u = u} fn nid vals fin sched st (just (cell-st {w} a))
  with w ≟ᵗ u
... | no  _    = quiet-refl
... | yes refl = quiet-refl
scanDispatch-quiet fn nid vals fin sched st nothing                      = quiet-refl
scanDispatch-quiet fn nid vals fin sched st (just (take-st _))           = quiet-refl
scanDispatch-quiet fn nid vals fin sched st (just (batchSync-st _ _ _))      = quiet-refl
scanDispatch-quiet fn nid vals fin sched st (just (mergeAll-st _ _ _ _)) = quiet-refl
scanDispatch-quiet fn nid vals fin sched st (just (switch-st _ _))       = quiet-refl
scanDispatch-quiet fn nid vals fin sched st (just (exhaust-st _ _))      = quiet-refl

-- the truncation's cut keeps a sublist of the registry
takeDispatch-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
                       (w : Maybe (FnClo Γ s boolᵗ)) (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
                       (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
                   → Quiet {e = e} sched st
                       (proj₁ (proj₂ (proj₂
                         (takeDispatch {e = e} w nid vals fin sched st m))))
                       (proj₂ (proj₂ (proj₂
                         (takeDispatch {e = e} w nid vals fin sched st m))))
takeDispatch-quiet w nid vals fin sched st (just (take-st k))
  with proj₂ (proj₂ (takeVals w k vals))
... | true  = quiet-cut nid (EvalSt.registry st)
... | false = quiet-refl
takeDispatch-quiet w nid vals fin sched st nothing                      = quiet-refl
takeDispatch-quiet w nid vals fin sched st (just (cell-st _))           = quiet-refl
takeDispatch-quiet w nid vals fin sched st (just (batchSync-st _ _ _))      = quiet-refl
takeDispatch-quiet w nid vals fin sched st (just (mergeAll-st _ _ _ _)) = quiet-refl
takeDispatch-quiet w nid vals fin sched st (just (switch-st _ _))       = quiet-refl
takeDispatch-quiet w nid vals fin sched st (just (exhaust-st _ _))      = quiet-refl

-- the bracket writes its buffer while the bit is up and empties it
-- once after; only the node table moves either way
batchDispatch-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
                        (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
                        (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
                    → Quiet {e = e} sched st
                        (proj₁ (proj₂ (proj₂
                          (batchDispatch {e = e} nid vals fin sched st m))))
                        (proj₂ (proj₂ (proj₂
                          (batchDispatch {e = e} nid vals fin sched st m))))
batchDispatch-quiet {s = s} nid vals fin sched st (just (batchSync-st {w} true bur done))
  with w ≟ᵗ s
... | no  _    = quiet-refl
... | yes refl = quiet-refl
batchDispatch-quiet {s = s} nid vals fin sched st (just (batchSync-st {w} false bur done))
  with w ≟ᵗ s
... | no  _    = quiet-refl
... | yes refl = quiet-refl
batchDispatch-quiet nid vals fin sched st nothing                        = quiet-refl
batchDispatch-quiet nid vals fin sched st (just (cell-st _))             = quiet-refl
batchDispatch-quiet nid vals fin sched st (just (take-st _))             = quiet-refl
batchDispatch-quiet nid vals fin sched st (just (mergeAll-st _ _ _ _))   = quiet-refl
batchDispatch-quiet nid vals fin sched st (just (switch-st _ _))         = quiet-refl
batchDispatch-quiet nid vals fin sched st (just (exhaust-st _ _))        = quiet-refl

-- the flattener's wrap marks its own node done
thruWrap-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                   (op : AllOp) (nid : NodeId) (fin : Bool)
                   (sched′ : Sched Γ) (st′ : EvalSt e)
               → Quiet {e = e} sched′ st′
                   (proj₁ (proj₂ (thruWrap {e = e} op nid fin (sched′ , st′))))
                   (proj₂ (proj₂ (thruWrap {e = e} op nid fin (sched′ , st′))))
thruWrap-quiet op nid false sched′ st′ = quiet-refl
thruWrap-quiet mergeAllᵒ nid true sched′ st′
  with lookupNode nid (EvalSt.nodes st′)
... | just (mergeAll-st _ _ _ _) = quiet-refl
... | just (cell-st _)           = quiet-refl
... | just (take-st _)           = quiet-refl
... | just (batchSync-st _ _ _)  = quiet-refl
... | just (switch-st _ _)       = quiet-refl
... | just (exhaust-st _ _)      = quiet-refl
... | nothing                    = quiet-refl
thruWrap-quiet switchᵒ nid true sched′ st′
  with lookupNode nid (EvalSt.nodes st′)
... | just (switch-st _ _)       = quiet-refl
... | just (cell-st _)           = quiet-refl
... | just (take-st _)           = quiet-refl
... | just (batchSync-st _ _ _)  = quiet-refl
... | just (mergeAll-st _ _ _ _) = quiet-refl
... | just (exhaust-st _ _)      = quiet-refl
... | nothing                    = quiet-refl
thruWrap-quiet exhaustᵒ nid true sched′ st′
  with lookupNode nid (EvalSt.nodes st′)
... | just (exhaust-st _ _)      = quiet-refl
... | just (cell-st _)           = quiet-refl
... | just (take-st _)           = quiet-refl
... | just (batchSync-st _ _ _)  = quiet-refl
... | just (mergeAll-st _ _ _ _) = quiet-refl
... | just (switch-st _ _)       = quiet-refl
... | nothing                    = quiet-refl

-- THE FIFTEEN-MEMBER INDUCTION, `Rx.Evaluator.Keeps`'s, at a counter.
-- Every clause matches a constructor and recurses on its own
-- sub-derivations; the counter bound travels by `then`.
-- STRUCTURAL SCC: subscribeE-quiet subscribeSharedSlot-quiet subscribeInner-quiet subscribeAll-quiet stepFrame-quiet thruWalk-quiet thruConsume-quiet innerReact-quiet innerFinish-quiet mergeAllDrain-quiet sharedConnect-quiet foldPath-quiet dispatchShare-quiet shareWalk-quiet shareGo-quiet
subscribeE-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                     {b : Val Γ (obs u)} {κ : Path Γ lo u t} {now}
                     {sched sched₂ : Sched Γ} {st st₁ : EvalSt e} {out}
                 → n ≤ counter (Sched.mint sched) sourceᵏ
                 → subscribeE⇓ {e = e} b κ now sched st (out , sched₂ , st₁)
                 → Quiet {e = e} sched st sched₂ st₁

stepFrame-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
                    {fr : Frame Γ s u} {κ : Path Γ lo u t} {now} {vals fin}
                    {sched sched₁ : Sched Γ} {st st₁ : EvalSt e} {out vals′ fin′}
                → n ≤ counter (Sched.mint sched) sourceᵏ
                → stepFrame⇓ {e = e} now fr κ vals fin sched st
                    (out , vals′ , fin′ , sched₁ , st₁)
                → Quiet {e = e} sched st sched₁ st₁

subscribeAll-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                       {op} {ns : NodeState Γ} {b : Val Γ (obs (echoᵗ u))}
                       {κ : Path Γ lo u t} {now}
                       {sched sched₂ : Sched Γ} {st st₁ : EvalSt e} {out}
                   → n ≤ counter (Sched.mint sched) sourceᵏ
                   → subscribeAll⇓ {e = e} op ns b κ now sched st
                       (out , sched₂ , st₁)
                   → Quiet {e = e} sched st sched₂ st₁

subscribeInner-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                         {op} {allNid} {κ : Path Γ lo u t} {now}
                         {o : Val Γ (obs u)} {sched sched′ : Sched Γ}
                         {st st′ : EvalSt e} {inst out}
                     → n ≤ counter (Sched.mint sched) sourceᵏ
                     → subscribeInner⇓ {e = e} op allNid κ now o sched st
                         (inst , out , sched′ , st′)
                     → Quiet {e = e} sched st sched′ st′

thruWalk-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                   {op} {nid} {κ : Path Γ lo u t} {now}
                   {vals : List (Val Γ (u +ᵗ obs u))} {sched sched′ : Sched Γ}
                   {st st′ : EvalSt e} {out}
               → n ≤ counter (Sched.mint sched) sourceᵏ
               → thruWalk⇓ {e = e} op nid κ now vals sched st (out , sched′ , st′)
               → Quiet {e = e} sched st sched′ st′

thruConsume-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                      {op} {nid} {κ : Path Γ lo u t} {now}
                      {o : Val Γ (obs u)} {sched sched′ : Sched Γ}
                      {st st′ : EvalSt e} {out}
                  → n ≤ counter (Sched.mint sched) sourceᵏ
                  → thruConsume⇓ {e = e} op nid κ now o sched st (out , sched′ , st′)
                  → Quiet {e = e} sched st sched′ st′

mergeAllDrain-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
                        {allNid} {κ : Path Γ lo s t} {now} {fuel lim act od q}
                        {sched sched′ : Sched Γ} {st st′ : EvalSt e}
                        {out act′ q′}
                    → n ≤ counter (Sched.mint sched) sourceᵏ
                    → mergeAllDrain⇓ {e = e} allNid κ now fuel lim act od q sched st
                        (out , act′ , q′ , sched′ , st′)
                    → Quiet {e = e} sched st sched′ st′

innerFinish-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
                      {op} {allNid inst} {κ : Path Γ lo s t} {now}
                      {vals : List (Val Γ s)} {sched sched′ : Sched Γ}
                      {st st′ : EvalSt e} {m} {out vals′ fin}
                  → n ≤ counter (Sched.mint sched) sourceᵏ
                  → innerFinish⇓ {e = e} op allNid inst κ now vals sched st m
                      (out , vals′ , fin , sched′ , st′)
                  → Quiet {e = e} sched st sched′ st′

innerReact-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
                     {op} {allNid inst} {κ : Path Γ lo s t} {now}
                     {vals : List (Val Γ s)} {sched sched′ : Sched Γ}
                     {st st′ : EvalSt e} {alive} {out vals′ fin}
                 → n ≤ counter (Sched.mint sched) sourceᵏ
                 → innerReact⇓ {e = e} op allNid inst κ now vals sched st alive
                     (out , vals′ , fin , sched′ , st′)
                 → Quiet {e = e} sched st sched′ st′

-- the connect is reached only from a slot not yet completed
sharedConnect-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                        {i} {d} {κ : Path Γ lo _ t} {below} {now}
                        {sched sched₁ : Sched Γ} {st st₂ : EvalSt e} {out}
                    → memberSource (toℕ i) (EvalSt.completedSources st) ≡ false
                    → n ≤ counter (Sched.mint sched) sourceᵏ
                    → sharedConnect⇓ {e = e} i d κ below now sched st
                        (out , sched₁ , st₂)
                    → Quiet {e = e} sched st sched₁ st₂

subscribeSharedSlot-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                              {i} {d} {κ : Path Γ lo _ t} {below} {now}
                              {sched sched₁ : Sched Γ} {st st₂ : EvalSt e} {out}
                          → n ≤ counter (Sched.mint sched) sourceᵏ
                          → subscribeSharedSlot⇓ {e = e} i d κ below now sched st
                              (out , sched₁ , st₂)
                          → Quiet {e = e} sched st sched₁ st₂

foldPath-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                   {κ : Path Γ lo u t} {now} {vals} {fin}
                   {sched sched₁ : Sched Γ} {st st₁ : EvalSt e} {emits}
               → n ≤ counter (Sched.mint sched) sourceᵏ
               → foldPath⇓ {e = e} now κ vals fin sched st (emits , sched₁ , st₁)
               → Quiet {e = e} sched st sched₁ st₁

dispatchShare-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                        {i} {below} {now} {vals} {fin}
                        {sched sched₁ : Sched Γ} {st st₁ : EvalSt e} {emits}
                    → n ≤ counter (Sched.mint sched) sourceᵏ
                    → dispatchShare⇓ {e = e} {lo = lo} now i below vals fin sched st
                        (emits , sched₁ , st₁)
                    → Quiet {e = e} sched st sched₁ st₁

-- and a walk carrying the end has spent its share
shareWalk-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                    {i} {now} {vals} {fin}
                    {sched sched₁ : Sched Γ} {st st₁ : EvalSt e} {emits}
                → n ≤ counter (Sched.mint sched) sourceᵏ
                → shareWalk⇓ {e = e} now i vals fin sched st (emits , sched₁ , st₁)
                → Quiet {e = e} sched st sched₁ st₁
                  × (fin ≡ true → memberSource (toℕ i) (EvalSt.completedSources st₁) ≡ true)

shareGo-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                  {i} {now} {v} {fin} {ps}
                  {sched sched₁ : Sched Γ} {st st₁ : EvalSt e} {emits}
              → n ≤ counter (Sched.mint sched) sourceᵏ
              → shareGo⇓ {e = e} {lo = lo} now i v fin ps sched st
                  (emits , sched₁ , st₁)
              → Quiet {e = e} sched st sched₁ st₁

subscribeE-quiet h (subs-floor _ f)              = foldPath-quiet h f
subscribeE-quiet h (subs-shared _ slot)          = subscribeSharedSlot-quiet h slot
subscribeE-quiet h (subs-hot-done _ _ _ f)       = foldPath-quiet h f
subscribeE-quiet h (subs-hot-live {i = i} {κ = κ} {st = st} below _ nd _) =
  quiet-register {st = st} _ (atSlot i) (lowerFloor below κ) ≤-refl (inj₂ (toℕ<n i , nd))
subscribeE-quiet h (subs-cold-sync _ _ f)        = foldPath-quiet h f
subscribeE-quiet h (subs-cold-async {κ = κ} {st = st} _ _ refl _ _ f) =
  then h (quiet-register {st = st} _ (atDyn _ _) κ (n≤1+n _) (inj₁ ≤-refl)) (λ h′ → foldPath-quiet h′ f)
subscribeE-quiet h (subs-of f)                   = foldPath-quiet h f
subscribeE-quiet h (subs-empty f)                = foldPath-quiet h f
subscribeE-quiet h (subs-map sub)                = subscribeE-quiet h sub
subscribeE-quiet h (subs-takeWhile refl sub)     = subscribeE-quiet h sub
subscribeE-quiet h (subs-batchSync refl sub f)   =
  then h (subscribeE-quiet h sub) (λ h′ → foldPath-quiet h′ f)
subscribeE-quiet h (subs-scan refl sub)          = subscribeE-quiet h sub
subscribeE-quiet h (subs-flatten sa)             = subscribeAll-quiet h sa
subscribeE-quiet h (subs-μ sub)                  = subscribeE-quiet h sub
subscribeE-quiet h (subs-defer {u = u} {st = st} {nid = nid} _ refl _ _) =
  quiet-register {st = installNode nid (mergeAll-st {t = u} nothing 0 [] false) st} _ (atDyn _ _) _ (n≤1+n _) (inj₁ ≤-refl)
subscribeE-quiet h (subs-mint refl sub)          =
  then h (quiet-mint (n≤1+n _)) (λ h′ → subscribeE-quiet h′ sub)

stepFrame-quiet h step-map       = quiet-refl
stepFrame-quiet h (step-batchSync {nid = nid} {vals = vals} {fin} {sched} {st}) =
  batchDispatch-quiet nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
stepFrame-quiet h (step-scan {fn = fn} {nid} {vals = vals} {fin} {sched} {st}) =
  scanDispatch-quiet fn nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
stepFrame-quiet h (step-take {w = w} {nid = nid} {vals = vals} {fin} {sched} {st}) =
  takeDispatch-quiet w nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
stepFrame-quiet h (step-from-inner r) = innerReact-quiet h r
stepFrame-quiet h (step-thru-outer {op = op} {nid} {fin = fin} w) =
  then h (thruWalk-quiet h w) (λ _ → thruWrap-quiet op nid fin _ _)

subscribeAll-quiet h (sub-all refl sub) = subscribeE-quiet h sub

subscribeInner-quiet h (inner refl sub) = subscribeE-quiet h sub

thruWalk-quiet h walk-nil        = quiet-refl
thruWalk-quiet h (walk-echo f w) =
  then h (foldPath-quiet h f) (λ h′ → thruWalk-quiet h′ w)
thruWalk-quiet h (walk-cons c w) =
  then h (thruConsume-quiet h c) (λ h′ → thruWalk-quiet h′ w)

thruConsume-quiet h (consume-all-sub _ _ si)  = subscribeInner-quiet h si
thruConsume-quiet h (consume-all-enqueue _ _) = quiet-refl
thruConsume-quiet h (consume-all-nil _)       = quiet-refl
thruConsume-quiet h
  (consume-switch-sub {sched₀ = sched₀} {st₀ = st₀} {cur = cur} _ kl _ si) =
  then h (switchKill-quiet cur sched₀ st₀ kl) (λ h′ → subscribeInner-quiet h′ si)
thruConsume-quiet h (consume-switch-nil _)     = quiet-refl
thruConsume-quiet h (consume-exhaust-sub _ si) = subscribeInner-quiet h si
thruConsume-quiet h (consume-exhaust-nil _)    = quiet-refl

mergeAllDrain-quiet h drain-spent          = quiet-refl
mergeAllDrain-quiet h drain-nil            = quiet-refl
mergeAllDrain-quiet h (drain-no-room _)    = quiet-refl
mergeAllDrain-quiet h (drain-room _ si _ dr) =
  then h (subscribeInner-quiet h si) (λ h′ → mergeAllDrain-quiet h′ dr)

innerReact-quiet h react-false      = quiet-refl
innerReact-quiet h (react-alive _)  = quiet-refl
innerReact-quiet h (react-dead _ f) = innerFinish-quiet h f

innerFinish-quiet h (finish-all-drain fp dr) =
  then h (foldPath-quiet h fp) (λ h′ → mergeAllDrain-quiet h′ dr)
innerFinish-quiet h (finish-switch-clear _) = quiet-refl
innerFinish-quiet h finish-exhaust-clear    = quiet-refl
innerFinish-quiet h (finish-nil _)          = quiet-refl

sharedConnect-quiet nd h (connect {i = i} {κ = κ} {below = below} {st = st} refl sub) =
  then h (quiet-register {st = record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }} _ (atSlot i) (lowerFloor below κ) ≤-refl (inj₂ (toℕ<n i , nd)))
         (λ h′ → subscribeE-quiet h′ sub)

subscribeSharedSlot-quiet h (slot-spent _ f)      = foldPath-quiet h f
subscribeSharedSlot-quiet h (slot-join {i = i} {κ = κ} {below = below} {st = st} nd _ _) =
  quiet-register {st = st} _ (atSlot i) (lowerFloor below κ) ≤-refl (inj₂ (toℕ<n i , nd))
subscribeSharedSlot-quiet h (slot-connect nd _ sc) = sharedConnect-quiet nd h sc

foldPath-quiet h fold-root        = quiet-refl
foldPath-quiet h (fold-sink d)    = dispatchShare-quiet h d
foldPath-quiet h (fold-step sf r) =
  then h (stepFrame-quiet h sf) (λ h′ → foldPath-quiet h′ r)

dispatchShare-quiet h (disp {fin = false} w) = proj₁ (shareWalk-quiet h w)
dispatchShare-quiet h (disp {i = i} {fin = true} w) =
  quiet-end i (proj₁ (shareWalk-quiet h w)) (proj₂ (shareWalk-quiet h w) refl)

shareWalk-quiet h walk-nil        = quiet-refl , λ ()
shareWalk-quiet h (walk-end {i = i} {st = st} g) =
  then h (quiet-spend {s = toℕ i} {done = EvalSt.completedSources st}) (λ h′ → shareGo-quiet h′ g) ,
  λ _ → QuietC.done-up (shareGo-quiet h g) (toℕ i) (mem-here (toℕ i) (EvalSt.completedSources st))
shareWalk-quiet h (walk-more g w) =
  then h (shareGo-quiet h g) (λ h′ → proj₁ (shareWalk-quiet h′ w)) ,
  proj₂ (shareWalk-quiet (≤-trans h (QuietC.mint-up (shareGo-quiet h g))) w)

shareGo-quiet h go-nil          = quiet-refl
shareGo-quiet h (go-cut _ g)    = shareGo-quiet h g
shareGo-quiet h (go-live _ f g) =
  then h (foldPath-quiet h f) (λ h′ → shareGo-quiet h′ g)

chainStep-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {a vs fin c sched st r}
                → n ≤ counter (Sched.mint sched) sourceᵏ
                → chainStep⇓ {e = e} a vs fin c sched st r
                → Quiet {e = e} sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
chainStep-quiet h (chain-step f) = foldPath-quiet h f

-- A WALK IS QUIET WHILE THE SOURCE COUNTER STANDS ABOVE EVERY SLOT.
go-quiet : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {a vs fin cs sched} {st : EvalSt e} {r}
         → m ≤ counter (Sched.mint sched) sourceᵏ → cascadeGo⇓ a vs fin cs sched st r
         → Quiet sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
go-quiet h casc-nil         = quiet-refl
go-quiet h (casc-cut _ g)   = go-quiet h g
go-quiet h (casc-live _ c g) =
  then h (chainStep-quiet h c) (λ h′ → go-quiet h′ g)
