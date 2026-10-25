{-# OPTIONS --guardedness #-}

-- THE KEPT DEPTH, TESTED: every silent step of the engine drops the
-- leading skip of what its configuration means (`adequacy.Engine.Meaning.M`)
-- and erases none or more of the skips past it, or means the same, event for event, skips, positions and tails included
-- (`adequacy.Content.silent-exact`), with less work left
-- (`adequacy.Engine.Spent.Spending.silent-spent`), and never the same
-- when the step is one whose work may grow (`adequacy.Content`'s drops).
-- Also the longest run of silent steps meaning the same, and that what
-- the search finds still leads every race above it past each live
-- source's skips (`adequacy.Engine.Pick.Beat`).  And that each stall,
-- close and defer where it is shown links past every live source above
-- it (`adequacy.Engine.Shown.Links`): the body fed the rest erased of the
-- body fed the run, or past skips under the source's
-- (`adequacy.Engine.FedWalk.src-fed`), and so every node of it, owing the source nothing, its
-- source's run nesting nothing, and after each source skip shows
-- (`adequacy.Engine.Shown.src-body-on`).
module quickcheck.KeptDepth where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; upTo; null) renaming (map to mapL; _++_ to _++L_; _ʳ++_ to _ʳ++L_; reverse to reverseL)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _<ᵇ_; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (just; nothing)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String using (String; _++_)

open import denotation.MonotonicList.Events using (Events; Events∞; Tail; Tail∞; pin; idle; out; skip; end; hush; Pos; _<ᵖ_; inside; ix)
open import Tree using (defer; mergeᶠ; Later)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (refl)
open import quickcheck.Tm using (nat; bool; var)
open import quickcheck.Code using (Code; Prog; of; takeWhile; flatMap; connect; connected; cold; script) renaming (defer to deferᶜ)
open import denotation.MonotonicList.Events using (stall; close)
open import operation.PureObservable using (play; module Driver; module Machine)
open import adequacy.Engine.Meaning using (M)
open import quickcheck.Code using (toObs; timeline; showCode)
open import quickcheck.Ty using (natᵗ)
open import quickcheck.Quickcheck using (program)
open import adequacy.Ghost using (module Ghosting)
open import quickcheck.Spin using (showP)
open import quickcheck.Placing using (trailsᵇ; flatsᵇ)

open Driver ℕ using (Step; step; silent; value; complete; drained)
open Ghosting ℕ using (work; Measure)
open Machine using (Conf; ⟨_,_,_,_⟩; load; spot; subscribing; absorbed; rising; nx; cp; pend; coldS; top; inOuter; inLanes;
  plug; closed; alive; search; found; leafM; St; Ctx; Out; mapS; scanS; cutS; lnS; takeS; flatS; connS; inMap; inScan; inCut; inLn;
  inTake; inSrc; inBody; over; own; Mark; outOf; still; shows; cs; CS; free; cpAt; cutAt; overAt; _⊕_)
open import Data.Maybe using (Maybe)
open import operation.Key using (Key; _<ᴷ_)
open import Tree using (Obs; FlatOp)
open import denotation.MonotonicList.Events using (Timeline)
open import adequacy.Engine.Head using (cand)
open import adequacy.Engine.Pick using (past)
open import adequacy.Engine.Meaning using (mapped; scanned; took; outerFrame; lanesFrame; connSrc; bodyConn; srcState; srcG; srcRun; gh; lane; lanesL; deadL; envAt)
open import adequacy.Engine.Ahead using (shown) renaming (shows to showsᵃ)
open import denotation.MonotonicList using (head)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import operation.PureObservable using () renaming (rest to restᵀ)
open import denotation.MonotonicList.Events using (Frame∞; From∞; last)
import denotation.Unfold as U
open import Data.List.Membership.Propositional using (_∈_)

private
  -- A run's verdict, carrying its longest run of steps meaning the same
  -- and how many live sources' links it checked.
  data Verdict : Set where
    yes : ℕ → ℕ → Verdict
    no  : ℕ → String → Verdict

  -- The first `k` events of a run, printed.
  showE : ℕ → Events ℕ → String
  showE zero    _           = "…"
  showE (suc k) (out p a r) = "o(" ++ showP p ++ "," ++ showℕ a ++ ") " ++ showE k (Events∞.force r)
  showE (suc k) (skip p r)  = "k(" ++ showP p ++ ") " ++ showE k (Events∞.force r)
  showE (suc k) (end p)     = "e(" ++ showP p ++ ")"
  showE (suc k) hush        = "h"

  showMode : Conf ℕ → String
  showMode m with Conf.mode m
  ... | subscribing = "subscribing"
  ... | absorbed    = "absorbed"
  ... | rising _    = "rising"

  showSpot : List ℕ → String
  showSpot []      = ""
  showSpot (i ∷ π) = showℕ i ++ "." ++ showSpot π

  -- `work`'s order, decided.
  lowerᵇ : Measure → Measure → Bool
  lowerᵇ ((a , b , c , d , e) , f) ((a′ , b′ , c′ , d′ , e′) , f′) =
    lex₆ a a′ (lex₆ b b′ (lex₆ c c′ (lex₆ d d′ (lex₆ e e′ (f <ᵇ f′)))))
    where lex₆ : ℕ → ℕ → Bool → Bool
          lex₆ x y r = (x <ᵇ y) ∨ ((x ≡ᵇ y) ∧ r)

  showW : Measure → String
  showW ((a , b , c , d , e) , f) = showℕ a ++ "," ++ showℕ b ++ "," ++ showℕ c ++ "," ++ showℕ d ++ "," ++ showℕ e ++ ";" ++ showℕ f

  -- The steps whose work may grow (`adequacy.Engine.Spent.Spending.Skipped`).
  skippedᵇ : Conf ℕ → Bool
  skippedᵇ ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩         = true
  skippedᵇ ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩ = alive s
  skippedᵇ ⟨ c , pend (defer l) , subscribing , p ⟩                     = true
  skippedᵇ ⟨ c , s , absorbed , p ⟩ with search top (plug c s)
  ... | just (found (Γ′ , A′ , c′ , coldS true (play τ u i t (stall k))) leafM key) = not (closed c′)
  ... | just (found (Γ′ , A′ , c′ , coldS true (play τ u i t (close k))) leafM key) = not (closed c′)
  ... | _ = false
  skippedᵇ _ = false

  -- `adequacy.Engine.Pick.Beat`, decided.
  kafterᵇ knotᵇ : ∀ {A} → Key → Maybe (Key × Out A) → Bool
  kafterᵇ k nothing        = true
  kafterᵇ k (just (h , _)) = k <ᴷ h
  knotᵇ k nothing        = true
  knotᵇ k (just (h , _)) = not (h <ᴷ k)

  beforeᵇ : Key → List (Mark × Key) → Bool
  beforeᵇ k []             = true
  beforeᵇ k ((_ , h) ∷ ms) = (k <ᴷ h) ∧ beforeᵇ k ms

  raceᵇ : ∀ {R Γ A B} → (Key → Maybe (Key × Out B) → Bool) → Key → Ctx R Γ B → FlatOp → (A → Obs Timeline Γ B) → Bool → ℕ
        → List A → St Γ A → List (St Γ B) → List (St Γ B) → List (St Γ B) → Bool
  raceᵇ P k c op f d n q o acc []       tl = true
  raceᵇ P k c op f d n q o acc (x ∷ xs) tl = P k (cand (inLanes op f d n q o acc (xs ++L tl) c) x) ∧ raceᵇ P k c op f d n q o (x ∷ acc) xs tl

  beatᵇ : ∀ {R Γ A} → Key → Ctx R Γ A → St Γ A → Bool
  beatᵇ k top                               s = true
  beatᵇ k (inMap f c)                       s = beatᵇ k c (mapS f s)
  beatᵇ k (inScan f z c)                    s = beatᵇ k c (scanS f z s)
  beatᵇ k (inCut l a c)                     s = beatᵇ k c (cutS l a s)
  beatᵇ k (inLn b c)                        s = beatᵇ k c (lnS b s)
  beatᵇ k (inTake i q w c)                  s = beatᵇ k c (takeS i q w s)
  beatᵇ k (inOuter op f d n q ls c)         s = raceᵇ kafterᵇ k c op f d n q s [] ls [] ∧ beatᵇ k c (flatS op f d n q s ls)
  beatᵇ k (inLanes op f d n q o pre post c) s =
    knotᵇ k (cand (inOuter op f d n q (pre ʳ++L s ∷ post) c) o) ∧ raceᵇ kafterᵇ k c op f d n q o [] (reverseL pre) (s ∷ post)
    ∧ raceᵇ knotᵇ k c op f d n q o (s ∷ pre) post [] ∧ beatᵇ k c (flatS op f d n q o (pre ʳ++L s ∷ post))
  beatᵇ k (inSrc kk b c)                    s =
    kafterᵇ (past (over kk) k) (cand (inBody kk s c) b) ∧ beforeᵇ (past (over kk) k) (own (connS kk s b))
    ∧ beatᵇ (past (over kk) k) c (connS kk s b)
  beatᵇ k (inBody kk o c)                   s = knotᵇ k (cand (inSrc kk s c) o) ∧ beforeᵇ k (own (connS kk o s)) ∧ beatᵇ k c (connS kk o s)

  -- `adequacy.Engine.Pick.Beats`, decided.
  searchedᵇ : Conf ℕ → Bool
  searchedᵇ ⟨ c , s , absorbed , p ⟩ with search top (plug c s)
  ... | nothing = true
  ... | just (found (Γ′ , A′ , c′ , s′) m key) with outOf c′ s′ m
  ...   | still   = beatᵇ key c′ s′
  ...   | shows _ = true
  searchedᵇ _ = true

  -- What a silent step neither dropping nor keeping its meaning did.
  why : Conf ℕ → Conf ℕ → String
  why m m′ = "\n  from " ++ showMode m ++ " at " ++ showSpot (spot m) ++ " to " ++ showMode m′ ++ " at " ++ showSpot (spot m′)
             ++ (if skippedᵇ m then " (skipped)" else "") ++ "\n  work " ++ showW (work m) ++ " to " ++ showW (work m′)
             ++ "\n  before " ++ showE 10 (M m) ++ "\n  after  " ++ showE 10 (M m′)

  depth : ℕ
  depth = 60

  samePos : Pos → Pos → Bool
  samePos p q = not (p <ᵖ q) ∧ not (q <ᵖ p)

  -- Whether what follows comes no earlier than `p`.
  tailOnᵇ : Pos → Tail → Bool
  tailOnᵇ p idle      = true
  tailOnᵇ p (pin k _) = not (k <ᵖ p)

  onᵇ : ∀ {A} → Pos → Events A → Bool
  onᵇ p (out k _ _) = not (k <ᵖ p)
  onᵇ p (skip k _)  = not (k <ᵖ p)
  onᵇ p (end k)     = not (k <ᵖ p)
  onᵇ p hush        = true

  -- Whether `u` is `t`, to `k` pins of `t`, with none or more of its pins
  -- erased, each no later than the other's next
  -- (`adequacy.Engine.Erase.Eraseᵀ`).
  unpinnedᵇ : ℕ → Tail → Tail → Bool
  unpinnedᵇ zero    _         _          = true
  unpinnedᵇ (suc k) (pin p l) (pin q r)  =
    if samePos p q then unpinnedᵇ k (Tail∞.later l) (Tail∞.later r) else tailOnᵇ p (pin q r) ∧ unpinnedᵇ k (Tail∞.later l) (pin q r)
  unpinnedᵇ (suc k) (pin p l) idle       = unpinnedᵇ k (Tail∞.later l) idle
  unpinnedᵇ (suc k) idle      idle       = true
  unpinnedᵇ (suc k) idle      (pin _ _)  = false

  -- Past an erased skip, its tail erased to what the other leaves running.
  pastᵇ : ℕ → Tail → Maybe Tail → Bool
  pastᵇ k u nothing  = true
  pastᵇ k u (just t) = unpinnedᵇ k u t

  -- Whether `e′` is `e`, to `k` events of `e`, with none or more of its
  -- skips erased, each no later than the other's next
  -- (`adequacy.Engine.Drop.Erase`): each tail beside a kept
  -- event erased to the other's, the tail past an erased skip to what the
  -- other leaves running there, `t` (unknown at the root).  Positions
  -- strictly rise, so a skip at the other's position is never one to
  -- erase.  Values compared by `eq`.
  erasedᵇ : ∀ {A} → (A → A → Bool) → ℕ → Maybe Tail → Events A → Events A → Bool
  erasedᵇ eq zero    t _           _            = true
  erasedᵇ eq (suc k) t (out p a r) (out q b r′) =
    samePos p q ∧ eq a b ∧ unpinnedᵇ k (Events∞.cut r) (Events∞.cut r′) ∧ erasedᵇ eq k (just (Events∞.cut r′)) (Events∞.force r) (Events∞.force r′)
  erasedᵇ eq (suc k) t (skip p r)  (skip q r′)  =
    if samePos p q then unpinnedᵇ k (Events∞.cut r) (Events∞.cut r′) ∧ erasedᵇ eq k (just (Events∞.cut r′)) (Events∞.force r) (Events∞.force r′)
    else onᵇ p (skip q r′) ∧ pastᵇ k (Events∞.cut r) t ∧ erasedᵇ eq k t (Events∞.force r) (skip q r′)
  erasedᵇ eq (suc k) t (skip p r)  e′           = onᵇ p e′ ∧ pastᵇ k (Events∞.cut r) t ∧ erasedᵇ eq k t (Events∞.force r) e′
  erasedᵇ eq (suc k) t (end p)     (end q)      = samePos p q
  erasedᵇ eq (suc k) t hush        hush         = true
  erasedᵇ eq (suc k) t _           _            = false

  sameᵀ : ℕ → Tail → Tail → Bool
  sameᵀ zero    _         _         = true
  sameᵀ (suc k) (pin p l) (pin q r) = samePos p q ∧ sameᵀ k (Tail∞.later l) (Tail∞.later r)
  sameᵀ (suc k) idle      idle      = true
  sameᵀ (suc k) _         _         = false

  -- Whether `e′` is `e`, to `k` events, tails included.
  exactᵗ : ℕ → Events ℕ → Events ℕ → Bool
  exactᵗ zero    _           _            = true
  exactᵗ (suc k) (out p a r) (out q b r′) = samePos p q ∧ (a ≡ᵇ b) ∧ sameᵀ k (Events∞.cut r) (Events∞.cut r′) ∧ exactᵗ k (Events∞.force r) (Events∞.force r′)
  exactᵗ (suc k) (skip p r)  (skip q r′)  = samePos p q ∧ sameᵀ k (Events∞.cut r) (Events∞.cut r′) ∧ exactᵗ k (Events∞.force r) (Events∞.force r′)
  exactᵗ (suc k) (end p)     (end q)      = samePos p q
  exactᵗ (suc k) hush        hush         = true
  exactᵗ (suc k) _           _            = false

  -- Whether `e′` is `e` past its leading skip, the rest with skips erased.
  dropped : Events ℕ → Events ℕ → Bool
  dropped (skip p r) e′ = erasedᵇ _≡ᵇ_ depth nothing (Events∞.force r) e′
  dropped _          e′ = false

  -- A silent step from `m` to `m′`: 2 dropped leading skips, 1 meant the
  -- same with less work left and not skipped, 0 neither.
  kind : Conf ℕ → Conf ℕ → ℕ
  kind m m′ = if exactᵗ depth (M m) (M m′) then (if lowerᵇ (work m′) (work m) ∧ not (skippedᵇ m) then 1 else 0)
              else (if dropped (M m) (M m′) then 2 else 0)

  -- `adequacy.Engine.Erase._⊒_`, decided, values unread.
  leadᵇ : ∀ {A} → Events A → Events A → Bool
  leadᵇ (out p _ _) (out q _ _) = samePos p q
  leadᵇ (skip p _)  (skip q _)  = samePos p q
  leadᵇ (end p)     (end q)     = samePos p q
  leadᵇ hush        hush        = true
  leadᵇ _           _           = false

  hushedᵇ : ∀ {A} → Events A → Tail → Tail → Bool
  hushedᵇ hush t t′ = sameᵀ depth t t′
  hushedᵇ _    t t′ = true

  restᵇ : ∀ {A} → Events∞ A → Events∞ A → Bool
  restᵇ h h′ = leadᵇ (Events∞.force h) (Events∞.force h′) ∧ hushedᵇ (Events∞.force h) (Events∞.cut h) (Events∞.cut h′)
               ∧ unpinnedᵇ depth (Events∞.cut h) (Events∞.cut h′) ∧ erasedᵇ (λ _ _ → true) depth (just (Events∞.cut h′)) (Events∞.force h) (Events∞.force h′)

  -- `adequacy.Engine.Drop.Dropsˢ` and `Fed`, decided: past leading skips
  -- under `q`, the rest erased of the other.
  fedᵇ : ∀ {A} → ℕ → Pos → Events∞ A → Events∞ A → Bool
  fedᵇ k q β β′ = restᵇ β β′ ∨ dropsᵇ k q (Events∞.force β) β′
    where dropsᵇ : ∀ {A} → ℕ → Pos → Events A → Events∞ A → Bool
          dropsᵇ (suc k) q (skip p r) β′ = inside q p ∧ (restᵇ r β′ ∨ dropsᵇ k q (Events∞.force r) β′)
          dropsᵇ _       q _          β′ = false

  -- Every position a pass is asked of (`adequacy.Engine.FedWalk.Sought`:
  -- `q`'s own, or any under it) comes before `x`, one deeper.
  afterAllᵇ : Bool → Pos → Maybe Pos → Bool
  afterAllᵇ v     q nothing  = true
  afterAllᵇ false q (just x) = (q ++L (ix 0 ∷ [])) <ᵖ x
  afterAllᵇ true  q (just x) = (q <ᵖ x) ∧ not (inside q x)

  -- `x` before no position under `q`.
  notUnderᵇ : Pos → Maybe Pos → Bool
  notUnderᵇ q nothing  = true
  notUnderᵇ q (just x) = not (x <ᵖ q) ∧ not (inside q x)

  -- `adequacy.Engine.Drop.SrcPass`, decided, but for its trail.
  srcPassᵇ : ∀ {X B} → Bool → Pos → Events∞ B → Events∞ B → Events∞ X → Bool
  srcPassᵇ v q β β′ h′ =
    fedᵇ depth q β β′ ∧ afterAllᵇ v q (head (Events∞.force β′)) ∧ notUnderᵇ q (shown (Events∞.force h′))
    ∧ hushedᵇ (Events∞.force h′) (Events∞.cut h′) idle

  -- Where connect `i` sits in scope, innermost first.
  atᵇ : ∀ {Γ : List Set} {A : Set} → A ∈ Γ → ℕ
  atᵇ (here _)  = 0
  atᵇ (there j) = suc (atᵇ j)

  -- Nothing owed a source: each joiner of connect `i` not yet told its
  -- end joined before `q` and holds nothing fed, no defer holds a step of
  -- it, nothing is held under `q`; `i` counted as `atᵇ` counts.
  mutual
    caughtᵇ : ∀ {Γ B} → ℕ → Pos → U.Node Γ B → Bool
    caughtᵇ i q (U.mapᶜ f n)                 = caughtᵇ i q n
    caughtᵇ i q (U.scanᶜ f z n)              = caughtᵇ i q n
    caughtᵇ i q (U.takeWhileᶜ w t n)         = caughtᵇ i q n
    caughtᵇ i q (U.flatMapᶜ op g o ls qs pl) = caughtᴹᵇ i q o ∧ caughtᴸᵇ i q ls ∧ caughtᵇ i q pl
    caughtᵇ i q (U.joinᶜ j p xs nothing)     = (not (atᵇ j ≡ᵇ i) ∨ null xs) ∧ (p <ᵖ q)
    caughtᵇ i q (U.framesᶜ τ e m)            = not (inside q e)
    caughtᵇ i q (U.burstᶜ τ r k m)           = not (inside q r)
    caughtᵇ i q (U.ofᶜ p k xs)               = not (inside q p)
    caughtᵇ i q (U.connectᶜ r b s)           = not (inside q r) ∧ caughtᵇ (suc i) q b ∧ caughtˢᵇ i q s
    caughtᵇ i q (U.deferᶜ l p ns)            = not (inside q p) ∧ unnoticedᵇ i ns
    caughtᵇ i q (U.endingᶜ p n)              = not (inside q p) ∧ caughtᵇ i q n
    caughtᵇ i q (U.restᶜ n)                  = caughtᵇ i q n
    caughtᵇ i q (U.unionᶜ x y)               = caughtᵇ i q x ∧ caughtᵇ i q y
    caughtᵇ i q (U.burstingᶜ r t)            = not (inside q r) ∧ caughtᵇ i q t
    caughtᵇ i q (U.underᶜ s b)               = caughtˢᵇ i q s ∧ caughtᵇ (suc i) q b
    caughtᵇ i q _                            = true

    caughtᴹᵇ : ∀ {Γ B} → ℕ → Pos → Maybe (U.Node Γ B) → Bool
    caughtᴹᵇ i q nothing  = true
    caughtᴹᵇ i q (just n) = caughtᵇ i q n

    caughtᴸᵇ : ∀ {Γ B} → ℕ → Pos → List (U.Node Γ B) → Bool
    caughtᴸᵇ i q []       = true
    caughtᴸᵇ i q (n ∷ ns) = caughtᵇ i q n ∧ caughtᴸᵇ i q ns

    caughtˢᵇ : ∀ {Γ B} → ℕ → Pos → U.Source Γ B → Bool
    caughtˢᵇ i q (U.live s)    = caughtᵇ i q s
    caughtˢᵇ i q (U.ended c t) = caughtᵇ i q t

    unnoticedᵇ : ∀ {Γ} → ℕ → List (U.Notice Γ) → Bool
    unnoticedᵇ i []                   = true
    unnoticedᵇ i (U.notice j q a ∷ ns) = not (atᵇ j ≡ᵇ i) ∧ unnoticedᵇ i ns

  -- A run nothing nests in: no event under the skip just before it.
  flatᵇ : ∀ {A} → ℕ → Events A → Bool
  flatᵇ (suc k) (out p a r) = flatᵇ k (Events∞.force r)
  flatᵇ (suc k) (skip p r)  = unnested (head (Events∞.force r)) ∧ flatᵇ k (Events∞.force r)
    where unnested : Maybe Pos → Bool
          unnested nothing  = true
          unnested (just y) = not (inside p y)
  flatᵇ _       _           = true

  -- Every node of a body fed, not only the body: each inner source fed
  -- by the sources above it, each inner body by its source as well.
  mutual
    fedWalkᵇ : ∀ {Δ A} → Pos → St Δ A → U.NEnv Δ → U.NEnv Δ → Bool
    fedWalkᵇ q s ρ ρ′ = fedᵇ depth q (U.stateᴺ (gh s) ρ) (U.stateᴺ (gh s) ρ′) ∧ fedKidsᵇ q s ρ ρ′

    fedKidsᵇ : ∀ {Δ A} → Pos → St Δ A → U.NEnv Δ → U.NEnv Δ → Bool
    fedKidsᵇ q (mapS f s)              ρ ρ′ = fedWalkᵇ q s ρ ρ′
    fedKidsᵇ q (scanS f z s)           ρ ρ′ = fedWalkᵇ q s ρ ρ′
    fedKidsᵇ q (cutS l a s)            ρ ρ′ = fedWalkᵇ q s ρ ρ′
    fedKidsᵇ q (lnS b s)               ρ ρ′ = fedWalkᵇ q s ρ ρ′
    fedKidsᵇ q (takeS i w x s)         ρ ρ′ = fedWalkᵇ q s ρ ρ′
    fedKidsᵇ q (flatS op f d n p o ls) ρ ρ′ = fedWalkᵇ q o ρ ρ′ ∧ fedLanesᵇ q ls ρ ρ′
    fedKidsᵇ q (connS k o b)           ρ ρ′ =
      fedWalkᵇ q o ρ ρ′ ∧ fedWalkᵇ q b (srcRun (srcG k o) ρ ∷ᴬ ρ) (srcRun (srcG k o) ρ′ ∷ᴬ ρ′)
    fedKidsᵇ q _                       ρ ρ′ = true

    fedLanesᵇ : ∀ {Δ A} → Pos → List (St Δ A) → U.NEnv Δ → U.NEnv Δ → Bool
    fedLanesᵇ q []       ρ ρ′ = true
    fedLanesᵇ q (l ∷ ls) ρ ρ′ = fedWalkᵇ q l ρ ρ′ ∧ fedLanesᵇ q ls ρ ρ′

  -- Every live inner connect's source leaves running what trails it
  -- (`adequacy.Engine.FedWalk.fed-trail`): in the run's environment, and
  -- in the rest's wherever the run's does.
  liveTrailᵇ : ∀ {X} → CS → Events∞ X → Bool
  liveTrailᵇ (cs cl true sa ba as nothing r en) σ = trailsᵇ 30 σ ∧ flatsᵇ 30 σ
  liveTrailᵇ _                                  σ = true

  mutual
    innerᵇ : ∀ {Δ A} → St Δ A → U.NEnv Δ → Bool
    innerᵇ (mapS f s)              ρ = innerᵇ s ρ
    innerᵇ (scanS f z s)           ρ = innerᵇ s ρ
    innerᵇ (cutS l a s)            ρ = innerᵇ s ρ
    innerᵇ (lnS b s)               ρ = innerᵇ s ρ
    innerᵇ (takeS i w x s)         ρ = innerᵇ s ρ
    innerᵇ (flatS op f d n p o ls) ρ = innerᵇ o ρ ∧ innerLᵇ ls ρ
    innerᵇ (connS k o b)           ρ = liveTrailᵇ k (srcState (srcG k o) ρ) ∧ innerᵇ o ρ ∧ innerᵇ b (srcRun (srcG k o) ρ ∷ᴬ ρ)
    innerᵇ _                       ρ = true

    innerLᵇ : ∀ {Δ A} → List (St Δ A) → U.NEnv Δ → Bool
    innerLᵇ []       ρ = true
    innerLᵇ (l ∷ ls) ρ = innerᵇ l ρ ∧ innerLᵇ ls ρ

  -- Every live inner connect's source shows no earlier than any position
  -- asked of and, hushed, leaves nothing running; its body comes after
  -- each (`adequacy.Engine.FedWalk.fed-src-next`, `.fed-body-on`).
  livePosᵇ : ∀ {X B} → Bool → Pos → CS → Events∞ X → Events∞ B → Bool
  livePosᵇ v q (cs cl true sa ba as nothing r en) σ β =
    notUnderᵇ q (shown (Events∞.force σ)) ∧ hushedᵇ (Events∞.force σ) (Events∞.cut σ) idle ∧ afterAllᵇ v q (head (Events∞.force β))
  livePosᵇ v q _ σ β = true

  mutual
    placedᵇ : ∀ {Δ A} → Bool → Pos → St Δ A → U.NEnv Δ → Bool
    placedᵇ v q (mapS f s)              ρ = placedᵇ v q s ρ
    placedᵇ v q (scanS f z s)           ρ = placedᵇ v q s ρ
    placedᵇ v q (cutS l a s)            ρ = placedᵇ v q s ρ
    placedᵇ v q (lnS b s)               ρ = placedᵇ v q s ρ
    placedᵇ v q (takeS i w x s)         ρ = placedᵇ v q s ρ
    placedᵇ v q (flatS op f d n p o ls) ρ = placedᵇ v q o ρ ∧ placedLᵇ v q ls ρ
    placedᵇ v q (connS k o b)           ρ =
      livePosᵇ v q k (srcState (srcG k o) ρ) (U.stateᴺ (gh b) (srcRun (srcG k o) ρ ∷ᴬ ρ))
      ∧ placedᵇ v q o ρ ∧ placedᵇ v q b (srcRun (srcG k o) ρ ∷ᴬ ρ)
    placedᵇ v q _                       ρ = true

    placedLᵇ : ∀ {Δ A} → Bool → Pos → List (St Δ A) → U.NEnv Δ → Bool
    placedLᵇ v q []       ρ = true
    placedLᵇ v q (l ∷ ls) ρ = placedᵇ v q l ρ ∧ placedLᵇ v q ls ρ

  -- Unchecked; trails in the run's environment; in the rest's where the
  -- run's holds; placed in the rest's, as the facts are stated.
  trailedᵇ : ∀ {Δ A} → ℕ → Bool → Pos → St Δ A → U.NEnv Δ → U.NEnv Δ → Bool
  trailedᵇ zero               v q b ρ ρ′ = true
  trailedᵇ (suc zero)         v q b ρ ρ′ = innerᵇ b ρ
  trailedᵇ (suc (suc zero))   v q b ρ ρ′ = not (innerᵇ b ρ) ∨ innerᵇ b ρ′
  trailedᵇ (suc (suc (suc _))) v q b ρ ρ′ = placedᵇ v q b ρ′

  -- `adequacy.Engine.Shown.Links`, decided.
  linksᵇ : ∀ {R Γ A} → ℕ → Bool → Pos → Ctx R Γ A → Bool → Events∞ A → Events∞ A → Bool
  linksᵇ t v q top                          f h h′ = true
  linksᵇ t v q (inMap g c)                  f h h′ = linksᵇ t v q c true (mapped g h) (mapped g h′)
  linksᵇ t v q (inScan g z c)               f h h′ = linksᵇ t v q c true (scanned g z h) (scanned g z h′)
  linksᵇ t v q (inCut l a c)                f h h′ = linksᵇ t v q c true h h′
  linksᵇ t v q (inLn b c)                   f h h′ = linksᵇ t v q c b h h′
  linksᵇ t v q (inTake i w free c)          f h h′ = linksᵇ t v q c true (took i w h) (took i w h′)
  linksᵇ t v q (inTake i w (cpAt _) c)      f h h′ = true
  linksᵇ t v q (inTake i w (cutAt _) c)     f h h′ = true
  linksᵇ t v q (inTake i w (overAt _) c)    f h h′ = true
  linksᵇ t v q (inOuter op g d n w ls c)    f h h′ =
    linksᵇ t v q c true (outerFrame op (lane g) d w (lanesL ls) (deadL ls) (envAt c) h) (outerFrame op (lane g) d w (lanesL ls) (deadL ls) (envAt c) h′)
  linksᵇ t v q (inLanes op g d n w o pre post c) f h h′ =
    linksᵇ t v q c true (lanesFrame op (lane g) d w (gh o) (reverseL pre) post f (envAt c) h) (lanesFrame op (lane g) d w (gh o) (reverseL pre) post f (envAt c) h′)
  linksᵇ t v q (inSrc (cs false true sa ba as nothing r en) b c) f h h′ =
    srcPassᵇ v q (U.stateᴺ (gh b) (Events∞.force h ∷ᴬ envAt c)) (U.stateᴺ (gh b) (Events∞.force h′ ∷ᴬ envAt c)) h′
    ∧ caughtᵇ 0 q (gh b) ∧ flatᵇ depth (Events∞.force h) ∧ fedWalkᵇ q b (Events∞.force h ∷ᴬ envAt c) (Events∞.force h′ ∷ᴬ envAt c)
    ∧ trailedᵇ t v q b (Events∞.force h ∷ᴬ envAt c) (Events∞.force h′ ∷ᴬ envAt c)
    ∧ linksᵇ t true q c true (connSrc false r en (gh b) (envAt c) h) (connSrc false r en (gh b) (envAt c) h′)
  linksᵇ t v q (inSrc (cs false true sa ba as (just _) r en) b c) f h h′ = true
  linksᵇ t v q (inSrc (cs false false sa ba as ow r en) b c)      f h h′ = true
  linksᵇ t v q (inSrc (cs true sl sa ba as ow r en) b c)          f h h′ = true
  linksᵇ t v q (inBody (cs cl true sa ba as nothing r en) o c)    f h h′ =
    linksᵇ t v q c true (bodyConn r (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)) h)
                      (bodyConn r (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)) h′)
  linksᵇ t v q (inBody (cs cl true sa ba as (just _) r en) o c)   f h h′ = true
  linksᵇ t v q (inBody (cs cl false sa ba as ow r en) o c)        f h h′ = true

  -- The live sources a pass links past.
  liveᵇ : ∀ {R Γ A} → Ctx R Γ A → ℕ
  liveᵇ top                                                = 0
  liveᵇ (inMap g c)                                        = liveᵇ c
  liveᵇ (inScan g z c)                                     = liveᵇ c
  liveᵇ (inCut l a c)                                      = liveᵇ c
  liveᵇ (inLn b c)                                         = liveᵇ c
  liveᵇ (inTake i w x c)                                   = liveᵇ c
  liveᵇ (inOuter op g d n w ls c)                          = liveᵇ c
  liveᵇ (inLanes op g d n w o pre post c)                  = liveᵇ c
  liveᵇ (inSrc (cs false true sa ba as nothing r en) b c)  = suc (liveᵇ c)
  liveᵇ (inSrc k b c)                                      = liveᵇ c
  liveᵇ (inBody k o c)                                     = liveᵇ c

  -- How many a step links past, where it is shown.
  linkCount : Conf ℕ → ℕ
  linkCount ⟨ c , pend (defer l) , subscribing , p ⟩ = if showsᵃ c true then liveᵇ c else 0
  linkCount ⟨ c , s , absorbed , p ⟩ with search top (plug c s)
  ... | just (found (Γ′ , A′ , c′ , coldS true (play τ u i t (stall k))) leafM key) = if closed c′ ∨ not (showsᵃ c′ true) then 0 else liveᵇ c′
  ... | just (found (Γ′ , A′ , c′ , coldS true (play τ u i t (close k))) leafM key) = if closed c′ ∨ not (showsᵃ c′ true) then 0 else liveᵇ c′
  ... | _ = 0
  linkCount _ = 0

  -- Each step `adequacy.Content` passes, linked where it is shown: an
  -- absorbed stall or close (`stall-pass`, `close-pass`), and a defer
  -- (`defer-links`).
  linkedᵇ : ℕ → Conf ℕ → Bool
  linkedᵇ t ⟨ c , pend (defer l) , subscribing , p ⟩ =
    if showsᵃ c true
    then linksᵇ t false (p ⊕ (ix 0 ∷ [])) c true (U.stateᴺ (U.deferᶜ l p []) (envAt c)) (U.stateᴺ (U.subscribe (Later.force l) (p ⊕ (ix 1 ∷ []))) (envAt c))
    else true
  linkedᵇ t ⟨ c , s , absorbed , p ⟩ with search top (plug c s)
  ... | just (found (Γ′ , A′ , c′ , coldS true (play τ u i t (stall k))) leafM key) =
    closed c′ ∨ not (showsᵃ c′ true)
    ∨ linksᵇ t false (u ++L (ix i ∷ [])) c′ true (U.stateᴺ (gh (coldS true (play τ u i t (stall k)))) (envAt c′))
                                               (U.stateᴺ (gh (coldS true (play τ u (suc i) t (Frame∞.force k)))) (envAt c′))
  ... | just (found (Γ′ , A′ , c′ , coldS true (play τ u i t (close k))) leafM key) =
    closed c′ ∨ not (showsᵃ c′ true)
    ∨ linksᵇ t false (u ++L (ix i ∷ [])) c′ true (U.stateᴺ (gh (coldS true (play τ u i t (close k)))) (envAt c′))
                                               (U.stateᴺ (gh (coldS true (restᵀ τ (u ++L (last ∷ [])) (From∞.force k)))) (envAt c′))
  ... | _ = true
  linkedᵇ t _ = true

  -- Whether every silent step keeps its meaning so, and the longest run
  -- meaning the same.
  mutual
    walk : ℕ → ℕ → ℕ → ℕ → Conf ℕ → Verdict
    walk zero    run best ls m = yes (best ⊔ run) ls
    walk (suc n) run best ls m =
      if not (searchedᵇ m) then no (best ⊔ run) ("\n  beaten: a still find not first past a live source's skips, " ++ showMode m ++ " at " ++ showSpot (spot m))
      else if not (linkedᵇ 0 m) then no (best ⊔ run) ("\n  unlinked: a pass not fed past a live source's skips, " ++ showMode m ++ " at " ++ showSpot (spot m))
      else if not (linkedᵇ 1 m) then no (best ⊔ run) ("\n  untrailed: an inner source fed the run not trailing, " ++ showMode m ++ " at " ++ showSpot (spot m))
      else if not (linkedᵇ 2 m) then no (best ⊔ run) ("\n  untrailed: an inner source fed the rest not trailing, " ++ showMode m ++ " at " ++ showSpot (spot m))
      else if not (linkedᵇ 3 m) then no (best ⊔ run) ("\n  unplaced: an inner source fed the rest before a position asked of, " ++ showMode m ++ " at " ++ showSpot (spot m))
      else next n run best (ls + linkCount m) m (step m)

    next : ℕ → ℕ → ℕ → ℕ → Conf ℕ → Step → Verdict
    next n run best ls m (silent t m′)     = after n run best ls m m′ (kind m m′)
    next n run best ls m (value t p a m′)  = walk n 0 (best ⊔ run) ls m′
    next n run best ls m (complete p)      = yes (best ⊔ run) ls
    next n run best ls m drained           = yes (best ⊔ run) ls

    after : ℕ → ℕ → ℕ → ℕ → Conf ℕ → Conf ℕ → ℕ → Verdict
    after n run best ls m m′ zero          = no (best ⊔ run) (why m m′)
    after n run best ls m m′ (suc zero)    = walk n (suc run) best ls m′
    after n run best ls m m′ (suc (suc _)) = walk n 0 (best ⊔ run) ls m′

-- One program's verdict, under a label.
keptLine : String → Prog natᵗ → String
keptLine n p with walk 400 0 0 0 (load (toObs timeline 3 p []ᴬ []ᴬ []ᴬ))
... | yes l ls = "kept-depth: ok   " ++ n ++ " longest " ++ showℕ l ++ " links " ++ showℕ ls
... | no l w = "kept-depth: FAIL " ++ n ++ " longest " ++ showℕ l ++ "\n  program " ++ showCode natᵗ p ++ w

private
  -- A connect whose body's first value ends the takeWhile above it while
  -- the connect is still being subscribed, so its source is begun under
  -- a closed cut; a lane of a merge, so the run goes on past it.
  closedSrc : ∀ {Γ Δᵍ Δ Θ} → Bool → Code Γ Δᵍ Δ Θ natᵗ → Code Γ Δᵍ Δ Θ natᵗ
  closedSrc i s = takeWhile i (bool false) (connect s (of (nat 0 ∷ nat 1 ∷ [])))

  inLane : Code [] [] [] (natᵗ ∷ []) natᵗ → Prog natᵗ
  inLane l = flatMap (mergeᶠ nothing) l (of (nat 0 ∷ nat 1 ∷ []))

  -- Steps drawn programs rarely take: a step begun under a closed cut, and
  -- a source's skips shown to several joiners and defers at once.
  hands : List (String × Prog natᵗ)
  hands =
      ("a deferred source begun under a closed cut" , inLane (closedSrc false (deferᶜ (of (nat 5 ∷ [])))))
    ∷ ("a deferred source begun under a closed cut, inclusive" , inLane (closedSrc true (deferᶜ (of (nat 5 ∷ [])))))
    ∷ ("a deferred connect begun under a closed cut"
      , inLane (closedSrc false (deferᶜ (connect (of (nat 5 ∷ [])) (connected (here refl))))))
    ∷ ("a deferred merge begun under a closed cut"
      , inLane (closedSrc false (deferᶜ (flatMap (mergeᶠ nothing) (deferᶜ (of (var (here refl) ∷ []))) (of (nat 5 ∷ nat 6 ∷ []))))))
    ∷ ("a lane joined after its source's skip" , connect (cold (script ((1 , 1 ∷ []) ∷ []) false false)) rejoins)
    ∷ ("a lane joined after its source's skips" , connect (cold (script ((2 , 1 ∷ []) ∷ (1 , 2 ∷ []) ∷ []) false false)) rejoins)
    ∷ ("two joiners at once" , connect skipping (flatMap (mergeᶠ nothing) (connected (here refl)) (of (nat 0 ∷ nat 1 ∷ []))))
    ∷ ("a defer joining a live source" , connect skipping (deferᶜ (connected (here refl))))
    ∷ ("two defers joining at once" , connect skipping (flatMap (mergeᶠ nothing) (deferᶜ (connected (here refl))) (of (nat 0 ∷ nat 1 ∷ []))))
    ∷ ("a defer beside a joiner" , connect skipping (flatMap (mergeᶠ nothing) (deferᶜ (connected (here refl))) (connected (here refl))))
    ∷ ("a defer begun past a merged source's skip"
      , connect merged (flatMap (mergeᶠ nothing) (deferᶜ (connected (here refl))) (connected (here refl))))
    ∷ ("a lane joined past a merged source's skips" , connect merged rejoins)
    ∷ ("a connect in the body over its source, its lanes joining it"
      , connect skipping (connect (connected (here refl)) (flatMap (mergeᶠ nothing) (connected (here refl)) (connected (here refl)))))
    ∷ ("a connect in the body over a merged source, its lanes joining it"
      , connect merged (connect (connected (here refl)) (flatMap (mergeᶠ nothing) (connected (here refl)) (connected (here refl)))))
    ∷ ("a source running out a closed connect's nested burst past a stall, two joiners on it"
      , connect burstOut (flatMap (mergeᶠ nothing) (connected (here refl)) (of (nat 0 ∷ nat 1 ∷ []))))
    ∷ ("a source running out a closed connect's nested burst past a stall, its lanes joining it" , connect burstOut rejoins)
    ∷ []
    where
    -- A source skipping before each of its values.
    skipping : Code [] [] [] [] natᵗ
    skipping = cold (script ((2 , 1 ∷ []) ∷ (1 , 2 ∷ []) ∷ (2 , 3 ∷ []) ∷ []) false false)

    -- Two skipping lanes merged, so a source whose steps nest under the
    -- values that began them.
    merged : Code [] [] [] [] natᵗ
    merged = flatMap (mergeᶠ nothing) (cold (script ((2 , 1 ∷ []) ∷ (1 , 2 ∷ []) ∷ []) false false)) (of (nat 0 ∷ nat 1 ∷ []))

    -- A merge whose lanes, opened by a timed cold so past a stall, are each
    -- a connect its body ends at once: its source's subscribe burst, each
    -- value with a lane under it, runs out as skips.
    burstOut : Code [] [] [] [] natᵗ
    burstOut = flatMap (mergeᶠ nothing) (connect nests (of [])) (cold (script ((2 , 1 ∷ []) ∷ (1 , 2 ∷ []) ∷ []) false false))
      where nests : Code [] [] [] (natᵗ ∷ []) natᵗ
            nests = flatMap (mergeᶠ nothing) (of (var (here refl) ∷ var (here refl) ∷ [])) (of (nat 0 ∷ nat 1 ∷ []))

    -- Every value of the source opens a lane joining it again.
    rejoins : Code (natᵗ ∷ []) [] [] [] natᵗ
    rejoins = flatMap (mergeᶠ nothing) (connected (here refl)) (connected (here refl))

-- The verdicts on seeds from f, then on the hand programs.
keptLines : ℕ → ℕ → List String
keptLines f c = mapL (λ s → keptLine ("seed " ++ showℕ (f + s)) (program (f + s))) (upTo c) ++L mapL (λ (n , p) → keptLine n p) hands
