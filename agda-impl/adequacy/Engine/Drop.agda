{-# OPTIONS --guardedness #-}

-- A SKIP DROPPED AT A HOLE IS DROPPED AT THE ROOT, when every frame on
-- the way up shows it next (`Pass`): a run past leading skips at the hole,
-- the rest with skips erased (`Dropsˢ`), is one at the root (`lift-drops`).
--
-- A frame with one child passes a skip as it is.  A switched-off cut, a
-- takeWhile past its decision, a connect that is over or whose source is
-- closed, and a lane in the pool read only the hole's tail: there a skip
-- is not shown at all, and `Pass` is empty.  A frame with siblings passes
-- the skip when it comes first among them.  A connect's source passes it
-- with what its joiners saw of it, each under the skip's position
-- (`Under`): the body fed the run drops its own skips to the body fed
-- the rest, or erases them (`Fed`).

-- ERASURE IS WHAT A JOINER JOINED LATE SEES.  A lane a source's value
-- opens reads the source's run from where it joins, a skip before that
-- shown as one of its own (`denotation.Unfold`'s `rejoin`); past a
-- source's skip, the lanes not yet joined no longer see it, wherever
-- their own skips stand among the body's.  So the run past leading skips
-- is not the rest alike but the rest with skips erased (`_⊒_`), each
-- tail erased alike, its next the same.
--
-- REFUTED: c4f9b49e the rest alike, by `quickcheck.KeptDepth`'s lane joined
--   after its source's skip: the step drops the source's skip and erases
--   a later lane's, a kept body skip between them.
module adequacy.Engine.Drop where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_; [_]; reverse)
import Data.List as L
import denotation.MonotonicList as M′
open import Data.List.Relation.Unary.All using (All) renaming (_∷_ to _∷ᴬ_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import denotation.MonotonicList.Events using (Events; Events∞; Tail; Tail∞; pin; Pos; out; skip; end; hush; idle; _∪_; ix; last; _<ᵖ_; <ᵖ-split; <ᵖ-asym; <ᵖ-trans; <ᵖ-below)
open import denotation.MonotonicList using (head; mapᴱ; scanᴱ; takeWhileᴱ; taking; Agree; Agreeᵀ; stop; stopᵀ; pin⁼; idle⁼; out⁼; skip⁼; end⁼; hush⁼; agree-refl; agree-trans;
  agree-sym; agreeᵀ-refl; agreeᵀ-sym; agreeᵀ-trans; agreeᵀ-pred; agree-pred)
open import denotation.NonExpansive using (_,ˢ_; mapᴱ-ne; scanᴱ-ne; takeWhileᴱ-ne; ∪-ne; beside-ne; burstOn-ne; Outerᴿ; liveᴼ; whole-ne; go-ne; mapᴱ-neᴹ; Lanes)
open import denotation.Unfold using (Node; NEnv; stateᴺ; states; outerᴺ; meaning; cutᴺ; outer∞)
open import denotation.Denote using (flatOp)
open import operation.PureObservable using (module Machine)
open Machine using (nx; cp; Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; cs; free; cpAt; cutAt; overAt; closed)
open import adequacy.Engine.Meaning using (_≋_; ≋-by; same; up; mapped; scanned; took; outerFrame; lanesFrame; connSrc; bodyConn;
  srcState; srcG; envAt; gh; lane; lanesL; deadL; outerG; outerT; poolRuns; poolT; laneᴹ;
  lanesFrame-ne; outerFrame-ne; outerOf; lanes-refl; queue-refl; outer-refl; ≈-refl; risen)
open import adequacy.Engine.Race using (First; After; NotBefore; TailNotBefore; go-rise; go-outer)
open import adequacy.Engine.Ahead using (Under; shown)
open Events∞
open Tail∞
open import denotation.NonExpansive using (Agreeˢ)
open Agreeˢ

------------------------------------------------------------------------
-- Runs with skips erased

-- A tail with none or more of its pins erased.
data Eraseᵀ : ℕ → Tail → Tail → Set where
  stopᵉ : ∀ {x y} → Eraseᵀ zero x y
  pinᵉ  : ∀ {k p l r} → Eraseᵀ k (later l) (later r) → Eraseᵀ (suc k) (pin p l) (pin p r)
  unpin : ∀ {k p l r} → Eraseᵀ k (later l) r → Eraseᵀ (suc k) (pin p l) r
  idleᵉ : ∀ {k} → Eraseᵀ (suc k) idle idle

-- A run with none or more of its skips erased, `t` what the other leaves
-- running where it stands: each event kept alike, each tail beside one
-- erased alike, the tail past an erased skip beside the other's.  An
-- erased skip comes no later than what follows it: a merge reads its
-- parts by their next, so a skip erased out of order moves a sibling
-- across the outer's next.
--
-- REFUTED: 01726160 any skip erased, by an outer's `skip [5]` erased
--   before its `skip [1]`: a lane at `[3]` merges before the outer's next
--   on the one side, after it on the other.
data Erase {A : Set} : ℕ → Events A → Tail → Events A → Set where
  stopᵉ  : ∀ {x t y} → Erase zero x t y
  outᵉ   : ∀ {k p a l r t} → Eraseᵀ k (cut l) (cut r) → Erase k (force l) (cut r) (force r) → Erase (suc k) (out p a l) t (out p a r)
  skipᵉ  : ∀ {k p l r t} → Eraseᵀ k (cut l) (cut r) → Erase k (force l) (cut r) (force r) → Erase (suc k) (skip p l) t (skip p r)
  erased : ∀ {k p l t e} → NotBefore p (head (force l)) → Eraseᵀ k (cut l) t → Erase k (force l) t e → Erase (suc k) (skip p l) t e
  endᵉ   : ∀ {k p t} → Erase (suc k) (end p) t (end p)
  hushᵉ  : ∀ {k t} → Erase (suc k) hush t hush

-- The same with no tails, at the root.
data Eraseᴱ {A : Set} : ℕ → Events A → Events A → Set where
  stopᴱ   : ∀ {x y} → Eraseᴱ zero x y
  outᴱ    : ∀ {k p a l r} → Eraseᴱ k (force l) (force r) → Eraseᴱ (suc k) (out p a l) (out p a r)
  skipᴱ   : ∀ {k p l r} → Eraseᴱ k (force l) (force r) → Eraseᴱ (suc k) (skip p l) (skip p r)
  erasedᴱ : ∀ {k p l e} → Eraseᴱ k (force l) e → Eraseᴱ (suc k) (skip p l) e
  endᴱ    : ∀ {k p} → Eraseᴱ (suc k) (end p) (end p)
  hushᴱ   : ∀ {k} → Eraseᴱ (suc k) hush hush

-- Two runs with the same next.
data Lead⁼ {A : Set} : Events A → Events A → Set where
  outᴸ  : ∀ {p a l r} → Lead⁼ (out p a l) (out p a r)
  skipᴸ : ∀ {p l r} → Lead⁼ (skip p l) (skip p r)
  endᴸ  : ∀ {p} → Lead⁼ (end p) (end p)
  hushᴸ : Lead⁼ hush hush

record Eraseˢ {A : Set} (m : ℕ) (l l′ : Events∞ A) : Set where
  constructor _,ᵉ_
  field
    cutᵉ : Eraseᵀ m (cut l) (cut l′)
    nowᵉ : Erase m (force l) (cut l′) (force l′)
open Eraseˢ

-- THE REST, ERASED: `h′` is `h` with skips erased, its next kept, and,
-- hushed, leaving the same running.
_⊒_ : ∀ {A} → Events∞ A → Events∞ A → Set
h ⊒ h′ = Lead⁼ (force h) (force h′) × (force h ≡ hush → ∀ d → Agreeᵀ d (cut h) (cut h′)) × (∀ n → Eraseˢ n h h′)

private
  eraseᵀ-agree : ∀ {k} {x y : Tail} → Agreeᵀ k x y → Eraseᵀ k x y
  eraseᵀ-agree stopᵀ    = stopᵉ
  eraseᵀ-agree (pin⁼ a) = pinᵉ (eraseᵀ-agree a)
  eraseᵀ-agree idle⁼    = idleᵉ

  erase-agree : ∀ {A k} {x y : Events A} {t} → Agree k x y → Erase k x t y
  erase-agree stop        = stopᵉ
  erase-agree (out⁼ t a)  = outᵉ (eraseᵀ-agree t) (erase-agree a)
  erase-agree (skip⁼ t a) = skipᵉ (eraseᵀ-agree t) (erase-agree a)
  erase-agree end⁼        = endᵉ
  erase-agree hush⁼       = hushᵉ

  lead-agree : ∀ {A} {x y : Events A} → Agree 1 x y → Lead⁼ x y
  lead-agree (out⁼ _ _)  = outᴸ
  lead-agree (skip⁼ _ _) = skipᴸ
  lead-agree end⁼        = endᴸ
  lead-agree hush⁼       = hushᴸ

  eraseᵀ-then : ∀ {k} {x y z : Tail} → Eraseᵀ k x y → Agreeᵀ k y z → Eraseᵀ k x z
  eraseᵀ-then stopᵉ     a        = stopᵉ
  eraseᵀ-then (pinᵉ e)  (pin⁼ a) = pinᵉ (eraseᵀ-then e a)
  eraseᵀ-then (unpin e) a        = unpin (eraseᵀ-then e (agreeᵀ-pred a))
  eraseᵀ-then idleᵉ     idle⁼    = idleᵉ

  erase-then : ∀ {A k} {x y z : Events A} {t t′} → Erase k x t y → Agreeᵀ k t t′ → Agree k y z → Erase k x t′ z
  erase-then stopᵉ        u a           = stopᵉ
  erase-then (outᵉ e x)   u (out⁼ t a)  = outᵉ (eraseᵀ-then e t) (erase-then x t a)
  erase-then (skipᵉ e x)  u (skip⁼ t a) = skipᵉ (eraseᵀ-then e t) (erase-then x t a)
  erase-then (erased o e x) u a         = erased o (eraseᵀ-then e (agreeᵀ-pred u)) (erase-then x (agreeᵀ-pred u) (agree-pred a))
  erase-then endᵉ         u end⁼        = endᵉ
  erase-then hushᵉ        u hush⁼       = hushᵉ

  lead-then : ∀ {A} {x y z : Events A} → Lead⁼ x y → Agree 1 y z → Lead⁼ x z
  lead-then outᴸ  (out⁼ _ _)  = outᴸ
  lead-then skipᴸ (skip⁼ _ _) = skipᴸ
  lead-then endᴸ  end⁼        = endᴸ
  lead-then hushᴸ hush⁼       = hushᴸ

-- Runs alike, one the other erased of nothing.
≋-⊒ : ∀ {A} {h h′ : Events∞ A} → h ≋ h′ → h ⊒ h′
≋-⊒ x = lead-agree (nowˢ (x 1)) , (λ _ d → cutˢ (x d)) , λ n → eraseᵀ-agree (cutˢ (x n)) ,ᵉ erase-agree (nowˢ (x n))

-- Erased, then alike.
⊒-≋ : ∀ {A} {h h₀ h′ : Events∞ A} → h ⊒ h₀ → h₀ ≋ h′ → h ⊒ h′
⊒-≋ (l , u , e) x =
  lead-then l (nowˢ (x 1)) , (λ eq d → agreeᵀ-trans (u eq d) (cutˢ (x d))) ,
  λ n → eraseᵀ-then (cutᵉ (e n)) (cutˢ (x n)) ,ᵉ erase-then (nowᵉ (e n)) (cutˢ (x n)) (nowˢ (x n))

-- The next of a run erased is the next of the run.
lead-head : ∀ {A} {x y : Events A} → Lead⁼ x y → head x ≡ head y
lead-head outᴸ  = refl
lead-head skipᴸ = refl
lead-head endᴸ  = refl
lead-head hushᴸ = refl

lead-shown : ∀ {A} {x y : Events A} → Lead⁼ x y → shown x ≡ shown y
lead-shown outᴸ  = refl
lead-shown skipᴸ = refl
lead-shown endᴸ  = refl
lead-shown hushᴸ = refl

-- Hushed erased, hushed alike: what it leaves running is the other's.
lead-hush : ∀ {A} {h h′ : Events∞ A} → h ⊒ h′ → (force h′ ≡ hush → ∀ d → Agreeᵀ d (cut h′) idle) → force h ≡ hush → ∀ d → Agreeᵀ d (cut h) idle
lead-hush {h = h} (l , u , e) hc eq d = agreeᵀ-trans (u eq d) (hc (hushed (subst (λ x → Lead⁼ x _) eq l)) d)
  where hushed : ∀ {A} {y : Events A} → Lead⁼ hush y → y ≡ hush
        hushed hushᴸ = refl

-- No tails.
erase-events : ∀ {A k} {x y : Events A} {t} → Erase k x t y → Eraseᴱ k x y
erase-events stopᵉ        = stopᴱ
erase-events (outᵉ _ e)   = outᴱ (erase-events e)
erase-events (skipᵉ _ e)  = skipᴱ (erase-events e)
erase-events (erased _ _ e) = erasedᴱ (erase-events e)
erase-events endᵉ         = endᴱ
erase-events hushᵉ        = hushᴱ

------------------------------------------------------------------------
-- Runs past their leading skips

-- A run past one or more of its leading skips, the rest with skips erased.
data Drops {A : Set} (e e′ : Events A) : Set where
  drop  : ∀ {k r} → (∀ n → Agree n e (skip k r)) → (∀ n → Eraseᴱ n (force r) e′) → Drops e e′
  drops : ∀ {k r} → (∀ n → Agree n e (skip k r)) → Drops (force r) e′ → Drops e e′

-- And with its tail: each skip at a position `P` holds of.
data Dropsˢ {A : Set} (P : Pos → Set) (h h′ : Events∞ A) : Set where
  dropˢ  : ∀ {k r} → P k → (∀ n → Agree n (force h) (skip k r)) → r ⊒ h′ → Dropsˢ P h h′
  dropsˢ : ∀ {k r} → P k → (∀ n → Agree n (force h) (skip k r)) → Dropsˢ P r h′ → Dropsˢ P h h′

-- A skip alike past it.
skip-≋ : ∀ {A k} {r r′ : Events∞ A} → r ≋ r′ → ∀ n → Agree n (skip k r) (skip k r′)
skip-≋ x zero    = stop
skip-≋ x (suc n) = skip⁼ (cutˢ (x n)) (nowˢ (x n))

------------------------------------------------------------------------
-- What each frame asks of the skips it passes

-- The body fed the run and the body fed the rest: the one the other with
-- skips erased, or past its leading skips first, each under one of the
-- source's.
Fed : ∀ {B} → (Pos → Set) → Events∞ B → Events∞ B → Set
Fed P β β′ = β ⊒ β′ ⊎ Dropsˢ (Under P) β β′

mutual
  Pass : ∀ {R Γ A} → (Pos → Set) → Ctx R Γ A → Bool → Events∞ A → Events∞ A → Set
  Pass P top                               f h h′ = ⊤
  Pass P (inMap g c)                       f h h′ = Pass P c true (mapped g h) (mapped g h′)
  Pass P (inScan g z c)                    f h h′ = Pass P c true (scanned g z h) (scanned g z h′)
  Pass P (inCut true a c)                  f h h′ = Pass P c true h h′
  Pass P (inCut false a c)                 f h h′ = ⊥
  Pass P (inLn b c)                        f h h′ = Pass P c b h h′
  Pass P (inTake i q free c)               f h h′ = Pass P c true (took i q h) (took i q h′)
  Pass P (inTake i q (cpAt _) c)           f h h′ = ⊥
  Pass P (inTake i q (cutAt _) c)          f h h′ = ⊥
  Pass P (inTake i q (overAt _) c)         f h h′ = ⊥
  Pass P (inOuter op g true n q ls c)      f h h′ = ⊥
  Pass P (inOuter op g false n q ls c)     f h h′ =
    (∀ k → P k → All (λ l → After k (head (force l))) (states (lanesL ls) (envAt c)) × TailNotBefore k (poolT (deadL ls) (envAt c)))
    × Pass P c true (outerFrame op (lane g) false q (lanesL ls) (deadL ls) (envAt c) h) (outerFrame op (lane g) false q (lanesL ls) (deadL ls) (envAt c) h′)
  Pass P (inLanes op g d n q o pre post c) false h h′ = ⊥
  Pass P (inLanes op g d n q o pre post c) true  h h′ =
    (∀ k → P k → First k (outerᴺ (lane g) (outerG d (gh o)) (envAt c)) (states (lanesL post) (envAt c)) (states (lanesL (reverse pre)) (envAt c))
                     (outerT d (gh o) (envAt c) (poolRuns (reverse pre) post true (envAt c) h)))
    × Pass P c true (lanesFrame op (lane g) d q (gh o) (reverse pre) post true (envAt c) h)
                    (lanesFrame op (lane g) d q (gh o) (reverse pre) post true (envAt c) h′)
  Pass P (inSrc (cs false true sa ba as nothing r en) b c) f h h′ =
    SrcPass P (stateᴺ (gh b) (force h ∷ᴬ envAt c)) (stateᴺ (gh b) (force h′ ∷ᴬ envAt c)) h′
    × Pass (Under P) c true (connSrc false r en (gh b) (envAt c) h) (connSrc false r en (gh b) (envAt c) h′)
  Pass P (inSrc (cs false true sa ba as (just _) r en) b c) f h h′ = ⊥
  Pass P (inSrc (cs false false sa ba as ow r en) b c)      f h h′ = ⊥
  Pass P (inSrc (cs true sl sa ba as ow r en) b c)          f h h′ = ⊥
  Pass P (inBody (cs cl true sa ba as nothing r en) o c)    f h h′ =
    (force (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)) ≡ hush
       → ∀ d → Agreeᵀ d (cut (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c))) idle)
    × (∀ k → P k → NotBefore k (shown (force (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)))))
    × Pass P c true (bodyConn r (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)) h)
                    (bodyConn r (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)) h′)
  Pass P (inBody (cs cl true sa ba as (just _) r en) o c)   f h h′ = ⊥
  Pass P (inBody (cs cl false sa ba as ow r en) o c)        f h h′ = ⊥

  -- A source's skips pass its connect: the body drops what its joiners
  -- saw of them; the source's next shows no earlier than any of those,
  -- and, hushed, leaves nothing running; the body's next comes after
  -- each source skip shows.
  record SrcPass {X B} (P : Pos → Set) (β β′ : Events∞ B) (h′ : Events∞ X) : Set where
    inductive
    field
      fed     : Fed P β β′
      srcOn   : ∀ k → Under P k → NotBefore k (shown (force h′))
      srcHush : force h′ ≡ hush → ∀ d → Agreeᵀ d (cut h′) idle
      bodyOn  : ∀ k → P k → After (k ++ [ ix 0 ]) (head (force β′))

------------------------------------------------------------------------
-- Each frame keeps an erasure

-- A frame with one child maps each event alone, its tail the child's.
private
  map-on : ∀ {A B} (g : A → B) {p} x → NotBefore p (head x) → NotBefore p (head (mapᴱ g x))
  map-on g (out _ _ _) o = o
  map-on g (skip _ _)  o = o
  map-on g (end _)     o = o
  map-on g hush        o = o

  map-erase : ∀ {A B} (g : A → B) {k x t y} → Erase k x t y → Erase k (mapᴱ g x) t (mapᴱ g y)
  map-erase g stopᵉ        = stopᵉ
  map-erase g (outᵉ e x)   = outᵉ e (map-erase g x)
  map-erase g (skipᵉ e x)  = skipᵉ e (map-erase g x)
  map-erase g (erased o e x) = erased (map-on g _ o) e (map-erase g x)
  map-erase g endᵉ         = endᵉ
  map-erase g hushᵉ        = hushᵉ

  map-lead : ∀ {A B} (g : A → B) {x y} → Lead⁼ x y → Lead⁼ (mapᴱ g x) (mapᴱ g y)
  map-lead g outᴸ  = outᴸ
  map-lead g skipᴸ = skipᴸ
  map-lead g endᴸ  = endᴸ
  map-lead g hushᴸ = hushᴸ

  map-hush : ∀ {A B} (g : A → B) x → mapᴱ g x ≡ hush → x ≡ hush
  map-hush g hush eq = refl

  scan-on : ∀ {A B} (g : B → A → B) z {p} x → NotBefore p (head x) → NotBefore p (head (scanᴱ g z x))
  scan-on g z (out _ _ _) o = o
  scan-on g z (skip _ _)  o = o
  scan-on g z (end _)     o = o
  scan-on g z hush        o = o

  scan-erase : ∀ {A B} (g : B → A → B) z {k x t y} → Erase k x t y → Erase k (scanᴱ g z x) t (scanᴱ g z y)
  scan-erase g z stopᵉ                = stopᵉ
  scan-erase g z (outᵉ {a = a} e x)   = outᵉ e (scan-erase g (g z a) x)
  scan-erase g z (skipᵉ e x)          = skipᵉ e (scan-erase g z x)
  scan-erase g z (erased o e x)       = erased (scan-on g z _ o) e (scan-erase g z x)
  scan-erase g z endᵉ                 = endᵉ
  scan-erase g z hushᵉ                = hushᵉ

  scan-lead : ∀ {A B} (g : B → A → B) z {x y} → Lead⁼ x y → Lead⁼ (scanᴱ g z x) (scanᴱ g z y)
  scan-lead g z outᴸ  = outᴸ
  scan-lead g z skipᴸ = skipᴸ
  scan-lead g z endᴸ  = endᴸ
  scan-lead g z hushᴸ = hushᴸ

  scan-hush : ∀ {A B} (g : B → A → B) z x → scanᴱ g z x ≡ hush → x ≡ hush
  scan-hush g z hush eq = refl

  end-erase : ∀ {A} k {p t} → Erase {A} k (end p) t (end p)
  end-erase zero    = stopᵉ
  end-erase (suc k) = endᵉ

  -- Past a position, its subtree too.
  below-on : ∀ {p} k x → NotBefore p (just k) → NotBefore p (just (k ++ [ x ]))
  below-on {p} k x o with <ᵖ-split p k o
  ... | inj₁ lt   = <ᵖ-asym p (k ++ [ x ]) (<ᵖ-trans p k (k ++ [ x ]) lt (<ᵖ-below k []))
  ... | inj₂ refl = <ᵖ-asym k (k ++ [ x ]) (<ᵖ-below k [])

  took-on : ∀ {A} i (q : A → Bool) {p} x → NotBefore p (head x) → NotBefore p (head (takeWhileᴱ i q x))
  took-on i q (out k a r) o = taking-on i (q a) o
    where taking-on : ∀ i b → NotBefore _ (just k) → NotBefore _ (head (taking i q k a b r))
          taking-on i     true  o = o
          taking-on true  false o = below-on k (ix 0) o
          taking-on false false o = below-on k last o
  took-on i q (skip _ _)  o = o
  took-on i q (end _)     o = o
  took-on i q hush        o = o

  mutual
    took-erase : ∀ {A} i (q : A → Bool) {k x t y} → Erase k x t y → Erase k (takeWhileᴱ i q x) t (takeWhileᴱ i q y)
    took-erase i q stopᵉ                = stopᵉ
    took-erase i q (outᵉ {a = a} e x)   = taking-erase i q (q a) e x
    took-erase i q (skipᵉ e x)          = skipᵉ e (took-erase i q x)
    took-erase i q (erased o e x)       = erased (took-on i q _ o) e (took-erase i q x)
    took-erase i q endᵉ                 = endᵉ
    took-erase i q hushᵉ                = hushᵉ

    taking-erase : ∀ {A} i (q : A → Bool) b {k p a t} {l r : Events∞ A} → Eraseᵀ k (cut l) (cut r) → Erase k (force l) (cut r) (force r)
                 → Erase (suc k) (taking i q p a b l) t (taking i q p a b r)
    taking-erase i     q true  e x = outᵉ e (took-erase i q x)
    taking-erase true  q false {k} e x = outᵉ e (end-erase k)
    taking-erase false q false e x = endᵉ

  took-lead : ∀ {A} i (q : A → Bool) {x y} → Lead⁼ x y → Lead⁼ (takeWhileᴱ i q x) (takeWhileᴱ i q y)
  took-lead i q (outᴸ {a = a}) = taking-lead i (q a)
    where taking-lead : ∀ i b {p l r} → Lead⁼ (taking i q p a b l) (taking i q p a b r)
          taking-lead i     true  = outᴸ
          taking-lead true  false = outᴸ
          taking-lead false false = endᴸ
  took-lead i q skipᴸ = skipᴸ
  took-lead i q endᴸ  = endᴸ
  took-lead i q hushᴸ = hushᴸ

  took-hush : ∀ {A} i (q : A → Bool) x → takeWhileᴱ i q x ≡ hush → x ≡ hush
  took-hush i q (out p a l) eq = ⊥-elim (taking-hush i (q a) eq)
    where taking-hush : ∀ i b → taking i q p a b l ≡ hush → ⊥
          taking-hush i     true  ()
          taking-hush true  false ()
          taking-hush false false ()
  took-hush i q hush eq = refl

mapped-⊒ : ∀ {A B} (g : A → B) {h h′ : Events∞ A} → h ⊒ h′ → mapped g h ⊒ mapped g h′
mapped-⊒ g {h} (l , u , e) = map-lead g l , (λ eq → u (map-hush g (force h) eq)) , λ n → cutᵉ (e n) ,ᵉ map-erase g (nowᵉ (e n))

scanned-⊒ : ∀ {A B} (g : B → A → B) z {h h′ : Events∞ A} → h ⊒ h′ → scanned g z h ⊒ scanned g z h′
scanned-⊒ g z {h} (l , u , e) = scan-lead g z l , (λ eq → u (scan-hush g z (force h) eq)) , λ n → cutᵉ (e n) ,ᵉ scan-erase g z (nowᵉ (e n))

took-⊒ : ∀ {A} i (q : A → Bool) {h h′ : Events∞ A} → h ⊒ h′ → took i q h ⊒ took i q h′
took-⊒ i q {h} (l , u , e) = took-lead i q l , (λ eq → u (took-hush i q (force h) eq)) , λ n → cutᵉ (e n) ,ᵉ took-erase i q (nowᵉ (e n))

-- THE ERASURE, FRAME BY FRAME: a merge fed a run with skips erased runs
-- with skips erased, its next kept: it keeps its parts' order, and what
-- the parts leave running is the merge's tail.
postulate
  lanes-⊒   : ∀ {Γ A B} op (g : A → Pos → Node Γ B) d q (o : Node Γ A) pre post (ρ : NEnv Γ) {h h′ : Events∞ B}
            → h ⊒ h′ → lanesFrame op g d q o pre post true ρ h ⊒ lanesFrame op g d q o pre post true ρ h′
  outer-⊒   : ∀ {Γ A B} op (g : A → Pos → Node Γ B) q ls ds (ρ : NEnv Γ) {h h′ : Events∞ A}
            → h ⊒ h′ → outerFrame op g false q ls ds ρ h ⊒ outerFrame op g false q ls ds ρ h′
  body-⊒    : ∀ {X B} r {σ σ′ : Events∞ X} {β β′ : Events∞ B} → σ ⊒ σ′ → β ⊒ β′ → bodyConn r σ β ⊒ bodyConn r σ′ β′

------------------------------------------------------------------------
-- Each frame passes the skips

private
  -- A run as its next skip, its tail kept.
  skipped : ∀ {A} → Pos → Events∞ A → Events∞ A → Events∞ A
  skipped k r h .force = skip k r
  skipped k r h .cut   = cut h

  skipped-≋ : ∀ {A k} {r h : Events∞ A} → (∀ n → Agree n (force h) (skip k r)) → h ≋ skipped k r h
  skipped-≋ {h = h} ag n = agreeᵀ-refl n (cut h) ,ˢ ag n

mapped-drops : ∀ {A B P} (g : A → B) {h h′ : Events∞ A} → Dropsˢ P h h′ → Dropsˢ P (mapped g h) (mapped g h′)
mapped-drops g (dropˢ {r = r} pk ag x) =
  dropˢ {r = (mapped g r)} pk (λ n → agree-trans {y = M′.mapᴱ g (skip _ r)} (mapᴱ-ne g (ag n)) (skip-≋ (≋-by refl refl) n)) (mapped-⊒ g x)
mapped-drops g (dropsˢ {r = r} pk ag d) =
  dropsˢ {r = (mapped g r)} pk (λ n → agree-trans {y = M′.mapᴱ g (skip _ r)} (mapᴱ-ne g (ag n)) (skip-≋ (≋-by refl refl) n)) (mapped-drops g d)

scanned-drops : ∀ {A B P} (g : B → A → B) z {h h′ : Events∞ A} → Dropsˢ P h h′ → Dropsˢ P (scanned g z h) (scanned g z h′)
scanned-drops g z (dropˢ {r = r} pk ag x) =
  dropˢ {r = (scanned g z r)} pk (λ n → agree-trans {y = M′.scanᴱ g z (skip _ r)} (scanᴱ-ne g z (ag n)) (skip-≋ (≋-by refl refl) n)) (scanned-⊒ g z x)
scanned-drops g z (dropsˢ {r = r} pk ag d) =
  dropsˢ {r = (scanned g z r)} pk (λ n → agree-trans {y = M′.scanᴱ g z (skip _ r)} (scanᴱ-ne g z (ag n)) (skip-≋ (≋-by refl refl) n)) (scanned-drops g z d)

took-drops : ∀ {A P} i (q : A → Bool) {h h′ : Events∞ A} → Dropsˢ P h h′ → Dropsˢ P (took i q h) (took i q h′)
took-drops i q (dropˢ {r = r} pk ag x) =
  dropˢ {r = (took i q r)} pk (λ n → agree-trans {y = M′.takeWhileᴱ i q (skip _ r)} (takeWhileᴱ-ne i q (ag n)) (skip-≋ (≋-by refl refl) n)) (took-⊒ i q x)
took-drops i q (dropsˢ {r = r} pk ag d) =
  dropsˢ {r = (took i q r)} pk (λ n → agree-trans {y = M′.takeWhileᴱ i q (skip _ r)} (takeWhileᴱ-ne i q (ag n)) (skip-≋ (≋-by refl refl) n)) (took-drops i q d)

-- The lane's skip, first: the merge's next, the lane's rest in its place.
at-skip : ∀ {Γ A B} op (g : A → Pos → Node Γ B) d q (o : Node Γ A) pre post (ρ : NEnv Γ) {h r : Events∞ B} {k}
        → First k (outerᴺ g (outerG d o) ρ) (states (lanesL post) ρ) (states (lanesL pre) ρ) (outerT d o ρ (poolRuns pre post true ρ h))
        → (∀ n → Agree n (force h) (skip k r))
        → ∀ n → Agree n (force (lanesFrame op g d q o pre post true ρ h)) (skip k (lanesFrame op g d q o pre post true ρ r))
at-skip op g d q o pre post ρ {h} {r} {k} fi ag n =
  agree-trans (nowˢ (lanesFrame-ne op g d q o pre post true ρ (skipped-≋ {r = r} {h = h} ag n)))
    (subst (λ x → Agree n x (skip k (lanesFrame op g d q o pre post true ρ r)))
      (sym (go-rise (flatOp op) (outerᴺ g (outerG d o) ρ) (states (lanesL post) ρ) (skipped k r h) (states (lanesL pre) ρ) (L.map (laneᴹ g ρ) q)
             (outerT d o ρ (poolRuns pre post true ρ h)) refl fi))
      (skip-≋ (≋-by refl refl) n))

-- A lane first among its flatMap's parts passes its skips.
lanes-drops : ∀ {Γ A B P} op (g : A → Pos → Node Γ B) d q (o : Node Γ A) pre post (ρ : NEnv Γ) {h h′ : Events∞ B}
            → (∀ k → P k → First k (outerᴺ g (outerG d o) ρ) (states (lanesL post) ρ) (states (lanesL pre) ρ) (outerT d o ρ (poolRuns pre post true ρ h)))
            → Dropsˢ P h h′ → Dropsˢ P (lanesFrame op g d q o pre post true ρ h) (lanesFrame op g d q o pre post true ρ h′)
lanes-drops op g d q o pre post ρ {h} fi (dropˢ {k} {r} pk ag x) =
  dropˢ pk (at-skip op g d q o pre post ρ (fi k pk) ag) (lanes-⊒ op g d q o pre post ρ x)
lanes-drops op g d q o pre post ρ {h} fi (dropsˢ {k} {r} pk ag e) =
  dropsˢ pk (at-skip op g d q o pre post ρ (fi k pk) ag) (lanes-drops op g d q o pre post ρ fi e)

private
  -- The outer's skip, the outer's rest alike past it.
  outer-skip : ∀ {B} op (x : Events∞ (M′.MonotonicList B)) ls qs t k (e e′ : Events∞ (M′.MonotonicList B))
             → (∀ m → Outerᴿ m (just e) (just e′)) → ∀ n → Agree n (M′.outer op x ls qs t (skip k e)) (M′.outer op x ls qs t (skip k e′))
  outer-skip op x ls qs t k e e′ o zero    = stop
  outer-skip op x ls qs t k e e′ o (suc n) =
    skip⁼ (whole-ne (o n) (lanes-refl n ls) (agreeᵀ-refl n t)) (go-ne op (o n) (lanes-refl n ls) (queue-refl n qs) (agreeᵀ-refl n t))

  -- The outer's skip, first: the merge's next, the outer's rest in its place.
  at-outer : ∀ {Γ A B} op (g : A → Pos → Node Γ B) q ls ds (ρ : NEnv Γ) {h r : Events∞ A} {k}
           → All (λ l → After k (head (force l))) (states ls ρ) → TailNotBefore k (poolT ds ρ)
           → (∀ n → Agree n (force h) (skip k r))
           → ∀ n → Agree n (force (outerFrame op g false q ls ds ρ h)) (skip k (outerFrame op g false q ls ds ρ r))
  at-outer op g q ls ds ρ {h} {r} {k} al tn ag n =
    agree-trans (nowˢ (outerFrame-ne op g false q ls ds ρ (skipped-≋ {r = r} {h = h} ag n)))
      (subst (λ x → Agree n x (skip k (outerFrame op g false q ls ds ρ r)))
        (sym (go-outer (flatOp op) (outerOf g ρ (skipped k r h)) (states ls ρ) (L.map (laneᴹ g ρ) q) (poolT ds ρ) refl al tn))
        (agree-trans (outer-skip (flatOp op) (outerOf g ρ (skipped k r h)) (states ls ρ) (L.map (laneᴹ g ρ) q) (poolT ds ρ) k _ (outerOf g ρ r)
                        (λ m → liveᴼ (agreeᵀ-refl m (cut r)) (mapᴱ-neᴹ (λ x → ≈-refl (laneᴹ g ρ x)) (agree-refl m (force r)))) n)
                     (skip-≋ (≋-by refl refl) n)))

-- THE OUTER FIRST: an outer whose skips come before every lane's next
-- and every tail its ended parts left passes them.
outer-drops : ∀ {Γ A B P} op (g : A → Pos → Node Γ B) q ls ds (ρ : NEnv Γ) {h h′ : Events∞ A}
            → (∀ k → P k → All (λ l → After k (head (force l))) (states ls ρ) × TailNotBefore k (poolT ds ρ))
            → Dropsˢ P h h′ → Dropsˢ P (outerFrame op g false q ls ds ρ h) (outerFrame op g false q ls ds ρ h′)
outer-drops op g q ls ds ρ fi (dropˢ {k} pk ag x) =
  dropˢ pk (at-outer op g q ls ds ρ (proj₁ (fi k pk)) (proj₂ (fi k pk)) ag) (outer-⊒ op g q ls ds ρ x)
outer-drops op g q ls ds ρ fi (dropsˢ {k} pk ag d) =
  dropsˢ pk (at-outer op g q ls ds ρ (proj₁ (fi k pk)) (proj₂ (fi k pk)) ag) (outer-drops op g q ls ds ρ fi d)


-- THE OUTER ADMITTED: an outer's value first among its flatMap's parts
-- is a skip, and past it the merge running what `admit` leaves.
outer-admits : ∀ {Γ A B} op (g : A → Pos → Node Γ B) q ls ds (ρ : NEnv Γ) (o : Node Γ A) a p {Ls Qs t′ Ls′ T} (Y : Events∞ B)
             → M′.admit (flatOp op) (p ++ [ ix 1 ]) (laneᴹ g ρ a) (states ls ρ) (L.map (laneᴹ g ρ) q) ≡ (Ls , Qs , t′)
             → force Y ≡ M′.go (flatOp op) (just (outer∞ g o ρ)) Ls′ Qs T → cut Y ≡ M′.whole (just (outer∞ g o ρ)) Ls′ T
             → (∀ n → Lanes n Ls Ls′) → (∀ n → Agreeᵀ n (poolT ds ρ ∪ t′) T)
             → All (λ l → After p (head (force l))) (states ls ρ) → TailNotBefore p (poolT ds ρ)
             → Dropsˢ (_≡ p ++ [ ix 0 ]) (outerFrame op g false q ls ds ρ (risen o ρ (nx a) p)) Y
outer-admits op g q ls ds ρ o a p {Qs = Qs} Y ad ef ec la ta al tn =
  dropˢ refl
    (λ n → subst (λ x → Agree n x (skip (p ++ [ ix 0 ]) Y))
             (sym (go-outer (flatOp op) (outerOf g ρ (risen o ρ (nx a) p)) (states ls ρ) (L.map (laneᴹ g ρ) q) (poolT ds ρ) refl al tn)) (held n))
    (≋-⊒ (≋-by refl refl))
  where
    held : ∀ n → Agree n (M′.outer (flatOp op) (outerOf g ρ (risen o ρ (nx a) p)) (states ls ρ) (L.map (laneᴹ g ρ) q) (poolT ds ρ)
                            (force (outerOf g ρ (risen o ρ (nx a) p))))
                         (skip (p ++ [ ix 0 ]) Y)
    held zero = stop
    held (suc n) rewrite ad =
      skip⁼ (subst (Agreeᵀ n _) (sym ec) (whole-ne r (la n) (ta n)))
            (subst (Agree n _) (sym ef) (go-ne (flatOp op) r (la n) (queue-refl n Qs) (ta n)))
      where r = liveᴼ (agreeᵀ-refl n (cutᴺ o ρ)) (mapᴱ-neᴹ (λ x → ≈-refl (laneᴹ g ρ x)) (agree-refl n (meaning o ρ)))

-- THE LANE ENDED: a lane's end first among its flatMap's parts, a lane
-- waiting, is a skip, and past it the merge running the waiting lane
-- begun ahead of the rest, the ended lane's tail behind the pool.
lane-admits : ∀ {Γ A B} op (g : A → Pos → Node Γ B) d a q (o : Node Γ A) pre post (ρ : NEnv Γ) (s : Node Γ B) p {Ls T} (Y : Events∞ B)
            → First p (outerᴺ g (outerG d o) ρ) (states (lanesL post) ρ) (states (lanesL pre) ρ) (outerT d o ρ (poolRuns pre post true ρ (risen s ρ cp p)))
            → force Y ≡ M′.go (flatOp op) (outerᴺ g (outerG d o) ρ) Ls (L.map (laneᴹ g ρ) q) T → cut Y ≡ M′.whole (outerᴺ g (outerG d o) ρ) Ls T
            → (∀ n → Lanes n (M′.enter (laneᴹ g ρ a) (p ++ [ ix 1 ]) ∷ states (lanesL post) ρ ++ states (lanesL pre) ρ) Ls)
            → (∀ n → Agreeᵀ n (outerT d o ρ (poolRuns pre post true ρ (risen s ρ cp p)) ∪ cutᴺ s ρ) T)
            → Dropsˢ (_≡ p ++ [ ix 0 ]) (lanesFrame op g d (a ∷ q) o pre post true ρ (risen s ρ cp p)) Y
lane-admits op g d a q o pre post ρ s p Y fi ef ec la ta =
  dropˢ refl
    (λ n → subst (λ x → Agree n x (skip (p ++ [ ix 0 ]) Y))
             (sym (go-rise (flatOp op) (outerᴺ g (outerG d o) ρ) (states (lanesL post) ρ) (risen s ρ cp p) (states (lanesL pre) ρ)
                     (L.map (laneᴹ g ρ) (a ∷ q)) (outerT d o ρ (poolRuns pre post true ρ (risen s ρ cp p))) refl fi))
             (held n))
    (≋-⊒ (≋-by refl refl))
  where
    held : ∀ n → Agree n (M′.lane (flatOp op) (outerᴺ g (outerG d o) ρ) (states (lanesL post) ρ) (risen s ρ cp p) (states (lanesL pre) ρ)
                            (L.map (laneᴹ g ρ) (a ∷ q)) (outerT d o ρ (poolRuns pre post true ρ (risen s ρ cp p))) (end p))
                         (skip (p ++ [ ix 0 ]) Y)
    held zero    = stop
    held (suc n) =
      skip⁼ (subst (Agreeᵀ n _) (sym ec) (whole-ne (outer-refl n g (outerG d o) ρ) (la n) (ta n)))
            (subst (Agree n _) (sym ef) (go-ne (flatOp op) (outer-refl n g (outerG d o) ρ) (la n) (queue-refl n (L.map (laneᴹ g ρ) q)) (ta n)))

private
  -- The body past its skip, the source beside it as it stands.
  sideC : ∀ {X B} → Pos → Events∞ X → Events X → Events∞ B → Events∞ B
  sideC r σ e r₁ .force = M′.side r r₁ σ e
  sideC r σ e r₁ .cut   = M′.burstOn r σ ∪ cut r₁

  -- The body's skip, the source's next no earlier, comes first.  A
  -- source hushed is the body alone, so what it leaves running must be
  -- nothing, or the connect's tail would lose it past the skip.
  side-skip : ∀ {X B} r (σ : Events∞ X) (e : Events X) {k} (r₁ h : Events∞ B) → force σ ≡ e
            → (force σ ≡ hush → ∀ d → Agreeᵀ d (cut σ) idle) → NotBefore k (shown e)
            → ∀ n → Agree n (M′.side r (skipped k r₁ h) σ e) (skip k (sideC r σ e r₁))
  side-skip r σ e r₁ h eq hc nb zero = stop
  side-skip r σ hush r₁ h eq hc nb (suc n) =
    skip⁼ (subst (λ x → Agreeᵀ n (cut r₁) (M′.runOn r x (cut σ) ∪ cut r₁)) (sym eq) (agreeᵀ-sym (∪-ne (hc eq n) (agreeᵀ-refl n (cut r₁)))))
      (agree-refl n (force r₁))
  side-skip r σ (out q a s) r₁ h eq hc nb (suc n) rewrite nb = skip⁼ (agreeᵀ-refl n _) (agree-refl n _)
  side-skip r σ (skip q s)  r₁ h eq hc nb (suc n) rewrite nb = skip⁼ (agreeᵀ-refl n _) (agree-refl n _)
  side-skip r σ (end q)     r₁ h eq hc nb (suc n) rewrite nb = skip⁼ (agreeᵀ-refl n _) (agree-refl n _)

  body-skip : ∀ {X B k} r (σ : Events∞ X) {h r₁ : Events∞ B}
            → (force σ ≡ hush → ∀ d → Agreeᵀ d (cut σ) idle) → NotBefore k (shown (force σ))
            → (∀ n → Agree n (force h) (skip k r₁)) → ∀ n → Agree n (force (bodyConn r σ h)) (skip k (bodyConn r σ r₁))
  body-skip {k = k} r σ {h} {r₁} hc nb ag n =
    agree-trans (beside-ne r (skipped-≋ ag n) (same n σ))
      (agree-trans (side-skip r σ (force σ) r₁ h refl hc nb n) (skip-≋ {r = sideC r σ (force σ) r₁} {r′ = bodyConn r σ r₁} (≋-by refl refl) n))

-- A BODY'S SKIPS, THE SOURCE'S NEXT NO EARLIER, pass its connect, the
-- source beside it erased alike.
body-drops : ∀ {X B P} r {σ σ′ : Events∞ X} {h h′ : Events∞ B}
           → (force σ ≡ hush → ∀ d → Agreeᵀ d (cut σ) idle) → (∀ k → P k → NotBefore k (shown (force σ)))
           → σ ⊒ σ′ → Dropsˢ P h h′ → Dropsˢ P (bodyConn r σ h) (bodyConn r σ′ h′)
body-drops r {σ} hc nb y (dropˢ {k} {r₁} pk ag x) = dropˢ pk (body-skip r σ hc (nb k pk) ag) (body-⊒ r y x)
body-drops r {σ} hc nb y (dropsˢ {k} {r₁} pk ag d) = dropsˢ pk (body-skip r σ hc (nb k pk) ag) (body-drops r hc nb y d)

private
  ≋-sym : ∀ {A} {h h′ : Events∞ A} → h ≋ h′ → h′ ≋ h
  ≋-sym x n = agreeᵀ-sym (cutˢ (x n)) ,ˢ agree-sym (nowˢ (x n))

  bc-≋ : ∀ {X B} r {σ σ′ : Events∞ X} {β β′ : Events∞ B} → σ ≋ σ′ → β ≋ β′ → bodyConn r σ β ≋ bodyConn r σ′ β′
  bc-≋ r y x n = ∪-ne (burstOn-ne r (y n)) (cutˢ (x n)) ,ˢ beside-ne r (x n) (y n)

  -- A run alike a run's start drops what it drops; and to a run alike its end.
  drops-from : ∀ {A P} {h h₀ h′ : Events∞ A} → h ≋ h₀ → Dropsˢ P h₀ h′ → Dropsˢ P h h′
  drops-from e (dropˢ pk ag x)  = dropˢ pk (λ n → agree-trans (nowˢ (e n)) (ag n)) x
  drops-from e (dropsˢ pk ag d) = dropsˢ pk (λ n → agree-trans (nowˢ (e n)) (ag n)) d

  drops-to : ∀ {A P} {h h₀ h′ : Events∞ A} → Dropsˢ P h h₀ → h₀ ≋ h′ → Dropsˢ P h h′
  drops-to (dropˢ pk ag x)  e = dropˢ pk ag (⊒-≋ x e)
  drops-to (dropsˢ pk ag d) e = dropsˢ pk ag (drops-to d e)

  on-head : ∀ {B q} {β β′ : Events∞ B} → β ⊒ β′ → After q (head (force β′)) → After q (head (force β))
  on-head {q = q} x a = subst (After q) (sym (lead-head (proj₁ x))) a

  after-before : ∀ {B} q (e : Events B) → After q (head e) → M′.before q e ≡ true
  after-before q (out k a r) a′ = a′
  after-before q (skip k r)  a′ = a′
  after-before q (end k)     a′ = a′
  after-before q hush        a′ = refl

  -- The source's skip shows first.
  src-ahead : ∀ {X B} r (β : Events∞ B) (σ : Events∞ X) k σ₁ b → b ≡ true
            → ∀ n → Agree n (M′.ahead r β (skipped k σ₁ σ) (k ++ [ ix 0 ]) b) (skip (k ++ [ ix 0 ]) (bodyConn r σ₁ β))
  src-ahead r β σ k σ₁ .true refl n = skip-≋ (≋-by refl refl) n

  -- The body's skip goes first.
  body-ahead : ∀ {X B} r (β : Events∞ B) (σ : Events∞ X) k σ₁ k′ β₁ b → b ≡ false
             → ∀ n → Agree n (M′.ahead r (skipped k′ β₁ β) (skipped k σ₁ σ) (k ++ [ ix 0 ]) b) (skip k′ (bodyConn r (skipped k σ₁ σ) β₁))
  body-ahead r β σ k σ₁ k′ β₁ .false refl n = skip-≋ (≋-by refl refl) n

  src-first : ∀ {X B} r (β : Events∞ B) {σ σ₁ : Events∞ X} {k} → (∀ n → Agree n (force σ) (skip k σ₁))
            → M′.before (k ++ [ ix 0 ]) (force β) ≡ true
            → ∀ n → Agree n (force (bodyConn r σ β)) (skip (k ++ [ ix 0 ]) (bodyConn r σ₁ β))
  src-first r β {σ} {σ₁} {k} ag bt n =
    agree-trans (beside-ne r (same n β) (skipped-≋ ag n)) (src-ahead r β σ k σ₁ (M′.before (k ++ [ ix 0 ]) (force β)) bt n)

  choose : ∀ {C : Set} (b : Bool) → (b ≡ true → C) → (b ≡ false → C) → C
  choose true  t f = t refl
  choose false t f = f refl

  under-shown : ∀ {P : Pos → Set} {k} → P k → Under P (k ++ [ ix 0 ])
  under-shown {k = k} pk = k , pk , [ ix 0 ] , refl

  -- The body done dropping: each source skip shows ahead of its next,
  -- the body's next that of the body it erases to.
  src-alone : ∀ {X B P} r {β β′ : Events∞ B} {σ σ′ : Events∞ X} → β ⊒ β′ → (∀ k → P k → After (k ++ [ ix 0 ]) (head (force β′)))
            → Dropsˢ P σ σ′ → Dropsˢ (Under P) (bodyConn r σ β) (bodyConn r σ′ β′)
  src-alone r {β} {σ = σ} e bo (dropˢ {k} pk ag x) =
    dropˢ (under-shown pk) (src-first r β {σ} ag (after-before (k ++ [ ix 0 ]) (force β) (on-head e (bo k pk)))) (body-⊒ r x e)
  src-alone r {β} {σ = σ} e bo (dropsˢ {k} pk ag d) =
    dropsˢ (under-shown pk) (src-first r β {σ} ag (after-before (k ++ [ ix 0 ]) (force β) (on-head e (bo k pk)))) (src-alone r e bo d)

  -- The source done dropping: its connect is the body beside it, the
  -- source's next that of the source it erases to.
  body-alone : ∀ {X B P} r {σ σ′ : Events∞ X} {β β′ : Events∞ B}
             → (force σ′ ≡ hush → ∀ d → Agreeᵀ d (cut σ′) idle) → (∀ k → Under P k → NotBefore k (shown (force σ′)))
             → σ ⊒ σ′ → Dropsˢ (Under P) β β′ → Dropsˢ (Under P) (bodyConn r σ β) (bodyConn r σ′ β′)
  body-alone r {σ} hc nb x d =
    body-drops r (lead-hush x hc) (λ k u → subst (NotBefore k) (sym (lead-shown (proj₁ x))) (nb k u)) x d

  first-src : ∀ {X B} r {σ : Events∞ X} {β : Events∞ B} k σ₁ k′ β₁
            → (∀ n → Agree n (force σ) (skip k σ₁)) → (∀ n → Agree n (force β) (skip k′ β₁)) → (k ++ [ ix 0 ]) <ᵖ k′ ≡ true
            → ∀ n → Agree n (force (bodyConn r σ β)) (skip (k ++ [ ix 0 ]) (bodyConn r σ₁ β))
  first-src r {σ} {β} k σ₁ k′ β₁ ag ag′ eq n =
    agree-trans (beside-ne r (skipped-≋ ag′ n) (skipped-≋ ag n))
      (agree-trans (src-ahead r (skipped k′ β₁ β) σ k σ₁ ((k ++ [ ix 0 ]) <ᵖ k′) eq n)
        (skip-≋ (bc-≋ r (λ m → same m σ₁) (≋-sym (skipped-≋ ag′))) n))

  first-body : ∀ {X B} r {σ : Events∞ X} {β : Events∞ B} k σ₁ k′ β₁
             → (∀ n → Agree n (force σ) (skip k σ₁)) → (∀ n → Agree n (force β) (skip k′ β₁)) → (k ++ [ ix 0 ]) <ᵖ k′ ≡ false
             → ∀ n → Agree n (force (bodyConn r σ β)) (skip k′ (bodyConn r σ β₁))
  first-body r {σ} {β} k σ₁ k′ β₁ ag ag′ eq n =
    agree-trans (beside-ne r (skipped-≋ ag′ n) (skipped-≋ ag n))
      (agree-trans (body-ahead r β σ k σ₁ k′ β₁ ((k ++ [ ix 0 ]) <ᵖ k′) eq n)
        (skip-≋ (bc-≋ r (≋-sym (skipped-≋ ag)) (λ m → same m β₁)) n))

  -- Both dropping: whichever shows first goes.
  both : ∀ {X B P} r {σ σ′ : Events∞ X} {β β′ : Events∞ B}
       → (force σ′ ≡ hush → ∀ d → Agreeᵀ d (cut σ′) idle) → (∀ k → Under P k → NotBefore k (shown (force σ′)))
       → (∀ k → P k → After (k ++ [ ix 0 ]) (head (force β′)))
       → Dropsˢ P σ σ′ → Dropsˢ (Under P) β β′ → Dropsˢ (Under P) (bodyConn r σ β) (bodyConn r σ′ β′)
  both r {σ} {β = β} {β′ = β′} hc nb bo dσ@(dropˢ {k} {σ₁} pk ag x) dβ@(dropˢ {k′} {β₁} pk′ ag′ x′) =
    choose ((k ++ [ ix 0 ]) <ᵖ k′)
      (λ eq → dropsˢ (under-shown pk) (first-src r {σ} {β} k σ₁ k′ β₁ ag ag′ eq) (body-alone r hc nb x dβ))
      (λ eq → dropsˢ pk′ (first-body r {σ} {β} k σ₁ k′ β₁ ag ag′ eq) (src-alone r x′ bo dσ))
  both r {σ} {β = β} {β′ = β′} hc nb bo dσ@(dropˢ {k} {σ₁} pk ag x) dβ@(dropsˢ {k′} {β₁} pk′ ag′ d′) =
    choose ((k ++ [ ix 0 ]) <ᵖ k′)
      (λ eq → dropsˢ (under-shown pk) (first-src r {σ} {β} k σ₁ k′ β₁ ag ag′ eq) (body-alone r hc nb x dβ))
      (λ eq → dropsˢ pk′ (first-body r {σ} {β} k σ₁ k′ β₁ ag ag′ eq) (both r hc nb bo dσ d′))
  both r {σ} {β = β} {β′ = β′} hc nb bo dσ@(dropsˢ {k} {σ₁} pk ag d) dβ@(dropˢ {k′} {β₁} pk′ ag′ x′) =
    choose ((k ++ [ ix 0 ]) <ᵖ k′)
      (λ eq → dropsˢ (under-shown pk) (first-src r {σ} {β} k σ₁ k′ β₁ ag ag′ eq) (both r hc nb bo d dβ))
      (λ eq → dropsˢ pk′ (first-body r {σ} {β} k σ₁ k′ β₁ ag ag′ eq) (src-alone r x′ bo dσ))
  both r {σ} {β = β} {β′ = β′} hc nb bo dσ@(dropsˢ {k} {σ₁} pk ag d) dβ@(dropsˢ {k′} {β₁} pk′ ag′ d′) =
    choose ((k ++ [ ix 0 ]) <ᵖ k′)
      (λ eq → dropsˢ (under-shown pk) (first-src r {σ} {β} k σ₁ k′ β₁ ag ag′ eq) (both r hc nb bo d dβ))
      (λ eq → dropsˢ pk′ (first-body r {σ} {β} k σ₁ k′ β₁ ag ag′ eq) (both r hc nb bo dσ d′))

-- A SOURCE'S SKIPS AND ITS JOINERS': each source skip shows just past
-- itself, each joiner's image of it under it, and what follows is later;
-- so the connect drops them all, leading.
src-drops : ∀ {Γ X B P} r en (b : Node (X ∷ Γ) B) (ρ : NEnv Γ) {h h′ : Events∞ X}
          → SrcPass P (stateᴺ b (force h ∷ᴬ ρ)) (stateᴺ b (force h′ ∷ᴬ ρ)) h′
          → Dropsˢ P h h′ → Dropsˢ (Under P) (connSrc false r en b ρ h) (connSrc false r en b ρ h′)
src-drops r en b ρ {h} {h′} sp d with SrcPass.fed sp
... | inj₁ x  = drops-from (≋-by refl refl) (drops-to (src-alone r x (SrcPass.bodyOn sp) d) (≋-by refl refl))
... | inj₂ dβ = drops-from (≋-by refl refl) (drops-to (both r (SrcPass.srcHush sp) (SrcPass.srcOn sp) (SrcPass.bodyOn sp) d dβ) (≋-by refl refl))

------------------------------------------------------------------------
-- Up to the root

top-drops : ∀ {A P} {h h′ : Events∞ A} → Dropsˢ P h h′ → Drops (force h) (force h′)
top-drops (dropˢ pk ag x)  = drop ag (λ n → erase-events (nowᵉ (proj₂ (proj₂ x) n)))
top-drops (dropsˢ pk ag d) = drops ag (top-drops d)

-- THE LIFT: skips dropped at the hole, each passed by every frame above,
-- are dropped at the root.
lift-drops : ∀ {R Γ A} P (c : Ctx R Γ A) f {h h′ : Events∞ A} → Dropsˢ P h h′ → Pass P c f h h′ → Drops (up c f h) (up c f h′)
lift-drops P top                               f d ps       = top-drops d
lift-drops P (inMap g c)                       f d ps       = lift-drops P c true (mapped-drops g d) ps
lift-drops P (inScan g z c)                    f d ps       = lift-drops P c true (scanned-drops g z d) ps
lift-drops P (inCut true a c)                  f d ps       = lift-drops P c true d ps
lift-drops P (inLn b c)                        f d ps       = lift-drops P c b d ps
lift-drops P (inTake i q free c)               f d ps       = lift-drops P c true (took-drops i q d) ps
lift-drops P (inOuter op g false n q ls c)     f d (o , ps) =
  lift-drops P c true (outer-drops op (lane g) q (lanesL ls) (deadL ls) (envAt c) o d) ps
lift-drops P (inLanes op g d′ n q o pre post c) true d (fi , ps) =
  lift-drops P c true (lanes-drops op (lane g) d′ q (gh o) (reverse pre) post (envAt c) fi d) ps
lift-drops P (inSrc (cs false true sa ba as nothing r en) b c) f d (sp , ps) =
  lift-drops (Under P) c true (src-drops r en (gh b) (envAt c) sp d) ps
lift-drops P (inBody (cs cl true sa ba as nothing r en) o c) f d (hc , bp , ps) =
  lift-drops P c true (body-drops r hc bp (≋-⊒ (λ n → same n (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)))) d) ps
