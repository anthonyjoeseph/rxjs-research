{-# OPTIONS --guardedness #-}

-- SPIKE 6, THE ORDER HALF: NOTHING THE GHOST STILL HOLDS COMES BEFORE
-- WHAT WAS SHOWN.  At every quiet configuration of a run, every value
-- and end the ghost's meaning holds lies at or after every position the
-- root was already shown (`least`).  Together with spike 5's `Kept`, a
-- set, this is what makes the residual the denotation's tail.
--
-- It is STATIC: a property of one configuration, never a simulation of a
-- step.  Spike 4's chain bounds every job from the last event
-- (`chain-ready`); the ghost's meaning holds nothing below its jobs'
-- bounds (`floor`), read operator by operator off the stream functions
-- (`above-of`, `above-take`, `above-go`, `beside-has`, `above-rejoin`):
-- every value or end a stream function emits sits at or after one its
-- inputs emit, a job's saved position, or where it was subscribed.
--
-- The walk is generic in a flatMap's operator, so switch, exhaust and a
-- bounded merge cost nothing beyond merge: a dropped lane is a cut
-- ghosted idle, and `above-go` reads every arm of `go` at once.
--
-- One fact the walk needs is not spike 4's: each joiner a feed still
-- owes is the joiner at that path, joined where the node says, and an
-- end owed to it is the binder's one end, made after it joined
-- (`Named`).  `Valid` reads only the tree's shape, so it cannot carry
-- this; it is the leaf `named`.
module spike.StateTree3Least where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; T)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (_<ᵇ_)
open import Data.List using (length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong₂; subst)

open import denotation.MonotonicList.Events using (Pos; ix; last; root; Events; Events∞; out; skip; end; hush; Tail; idle; pin; _∪_;
  module Tail∞; _<ᵖ_; <ᵖ-trans; <ᵖ-below; <ᵖ-split; <ᵖ-sub; <ᵖ-ix) renaming (sub to subᴾ)
open import denotation.MonotonicList using (MonotonicList; mapᴱ; scanᴱ; takeWhileᴱ; ofᴱ; rejoin)
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import denotation.Denote using (flatOp)
open import adequacy.Sorted using (_≤ᵖ_; ≤ᵖ-trans; ≤ᵖ-child; settled-refl)
open import Tree using (Obs; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer; Later)
open import denotation.MonotonicList.Events using (Timeline)
open import spike.StateTree3 using (PObs; Ev; nx; cp; CS; St; pend; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
  Tag; go; att; attBody; owed; next; owedCp; owedCut; feeding; Job; subscribing; absorbed; resuming; rising; Conf; ⟨_,_,_,_,_⟩; Shown; step)
open import spike.StateTree3Valid using (Valid; step-ok; load-ok)
open import spike.StateTree3Order using (Ready; Feed; Asc; Chain; stop; link; Fwd; step-fwd; sib)
import spike.StateTree3Order as O
open import spike.StateTree3Ghost using (_≟ᴸ_; jobsAt; ofAt; Owing; free; endsAt; over; takeAt; owedAt; feedingsAt; attached; pendAt;
  Level; Bind; bind; zipF; member; owedTo; endOwed; endedAt; Book; book; flatᶜ; joinᶜ; gh; lanes; focusing; residual; quiet;
  Has; atOut; atEnd; pastOut; pastSkip; From; loaded; stepped)

------------------------------------------------------------------------
-- Nothing before `lo`

Above : ∀ {A : Set} → Pos → Events A → Set
Above lo e = ∀ {q b} → Has e q b → lo ≤ᵖ q

above-≤ : ∀ {A} {lo lo′} {e : Events A} → lo ≤ᵖ lo′ → Above lo′ e → Above lo e
above-≤ le a h = ≤ᵖ-trans le (a h)

------------------------------------------------------------------------
-- Each stream function emits nothing before what it reads

above-of : ∀ {A lo} p i (xs : List A) → lo ≤ᵖ (p ++ [ ix i ]) → Above lo (ofᴱ p i xs)
above-of p i []       le atEnd       = sib p refl le
above-of p i (x ∷ xs) le atOut       = le
above-of p i (x ∷ xs) le (pastOut h) = above-of p (suc i) xs (sib p (<ᵖ-ix i) le) h

above-map : ∀ {A B lo} (f : A → B) (e : Events A) → Above lo e → Above lo (mapᴱ f e)
above-map f (out k a r) he atOut       = he atOut
above-map f (out k a r) he (pastOut h) = above-map f (Events∞.force r) (λ h′ → he (pastOut h′)) h
above-map f (skip k r)  he (pastSkip h) = above-map f (Events∞.force r) (λ h′ → he (pastSkip h′)) h
above-map f (end k)     he atEnd       = he atEnd

above-scan : ∀ {A B lo} (f : B → A → B) z (e : Events A) → Above lo e → Above lo (scanᴱ f z e)
above-scan f z (out k a r) he atOut       = he atOut
above-scan f z (out k a r) he (pastOut h) = above-scan f (f z a) (Events∞.force r) (λ h′ → he (pastOut h′)) h
above-scan f z (skip k r)  he (pastSkip h) = above-scan f z (Events∞.force r) (λ h′ → he (pastSkip h′)) h
above-scan f z (end k)     he atEnd       = he atEnd

above-take : ∀ {A lo} i (q : A → Bool) (e : Events A) → Above lo e → Above lo (takeWhileᴱ i q e)
above-take i q (out k a r) he h with q a
above-take i     q (out k a r) he atOut           | true  = he atOut
above-take i     q (out k a r) he (pastOut h)     | true  = above-take i q (Events∞.force r) (λ h′ → he (pastOut h′)) h
above-take true  q (out k a r) he atOut           | false = ≤ᵖ-child k (he atOut)
above-take true  q (out k a r) he (pastOut atEnd) | false = ≤ᵖ-child k (he atOut)
above-take false q (out k a r) he atEnd           | false = ≤ᵖ-child k (he atOut)
above-take i q (skip k r)  he (pastSkip h) = above-take i q (Events∞.force r) (λ h′ → he (pastSkip h′)) h
above-take i q (end k)     he atEnd        = he atEnd

-- A joiner's events sit under the source's, or past where it joined.
≤-split : ∀ {c j} → c <ᵖ j ≡ true ⊎ c ≡ j → c ≤ᵖ j
≤-split (inj₁ h)    = inj₂ h
≤-split (inj₂ refl) = inj₁ refl

above-rejoin : ∀ {A lo} j (e : Events A) → Above lo e → Above lo (rejoin j e)
above-rejoin j (out q a k) he h with j <ᵖ q
above-rejoin j (out q a k) he atOut         | true  = ≤ᵖ-child q (he atOut)
above-rejoin j (out q a k) he (pastOut h)   | true  = above-rejoin j (Events∞.force k) (λ h′ → he (pastOut h′)) h
above-rejoin j (out q a k) he (pastSkip h)  | false = above-rejoin j (Events∞.force k) (λ h′ → he (pastOut h′)) h
above-rejoin j (skip q k)  he h with j <ᵖ q
above-rejoin j (skip q k)  he (pastSkip h)  | true  = above-rejoin j (Events∞.force k) (λ h′ → he (pastSkip h′)) h
above-rejoin j (skip q k)  he (pastSkip h)  | false = above-rejoin j (Events∞.force k) (λ h′ → he (pastSkip h′)) h
above-rejoin j (end c)     he h with j <ᵖ c in e
above-rejoin j (end c)     he atEnd         | true  = ≤ᵖ-child c (he atEnd)
above-rejoin j (end c)     he atEnd         | false = ≤ᵖ-child j (≤ᵖ-trans (he atEnd) (≤-split (<ᵖ-split c j e)))

-- Wherever the source stands, a joiner shows nothing before it joined.
above-rejoin-at : ∀ {A} p (e : Events A) → Above p (rejoin p e)
above-rejoin-at p (out q a k) h with p <ᵖ q in e
above-rejoin-at p (out q a k) atOut        | true  = inj₂ (<ᵖ-trans p q _ e (<ᵖ-below q []))
above-rejoin-at p (out q a k) (pastOut h)  | true  = above-rejoin-at p (Events∞.force k) h
above-rejoin-at p (out q a k) (pastSkip h) | false = above-rejoin-at p (Events∞.force k) h
above-rejoin-at p (skip q k)  h with p <ᵖ q
above-rejoin-at p (skip q k)  (pastSkip h) | true  = above-rejoin-at p (Events∞.force k) h
above-rejoin-at p (skip q k)  (pastSkip h) | false = above-rejoin-at p (Events∞.force k) h
above-rejoin-at p (end c)     h with p <ᵖ c in e
above-rejoin-at p (end c)     atEnd        | true  = inj₂ (<ᵖ-trans p c _ e (<ᵖ-below c []))
above-rejoin-at p (end c)     atEnd        | false = ≤ᵖ-child p (inj₁ refl)

-- What a joiner was fed, then the rest.
above-fed : ∀ {A lo} (xs : List (Pos × Maybe A)) (e : Events A) → All (λ x → lo ≤ᵖ proj₁ x) xs → Above lo e → Above lo (U.fedᴺ xs e)
above-fed []                   e hx        he h            = he h
above-fed ((q , just a) ∷ xs)  e (l ∷ᴬ hx) he atOut        = l
above-fed ((q , just a) ∷ xs)  e (l ∷ᴬ hx) he (pastOut h)  = above-fed xs e hx he h
above-fed ((q , nothing) ∷ xs) e (l ∷ᴬ hx) he (pastSkip h) = above-fed xs e hx he h

-- A connect shows its body's values and end, nothing of its source's.
mutual
  beside-has : ∀ {A B} r (β : Events∞ B) (σ : Events∞ A) {q b} → Has (M′.beside r β σ) q b → Has (Events∞.force β) q b
  beside-has r β σ h = side-has r β σ (Events∞.force σ) h

  side-has : ∀ {A B} r (β : Events∞ B) (σ : Events∞ A) e {q b} → Has (M′.side r β σ e) q b → Has (Events∞.force β) q b
  side-has r β σ e@(out _ _ _) h = ahead-has r β σ (M′.shownAt e) (M′.before (M′.shownAt e) (Events∞.force β)) h
  side-has r β σ e@(skip _ _)  h = ahead-has r β σ (M′.shownAt e) (M′.before (M′.shownAt e) (Events∞.force β)) h
  side-has r β σ e@(end _)     h = ahead-has r β σ (M′.shownAt e) (M′.before (M′.shownAt e) (Events∞.force β)) h
  side-has r β σ hush        h = h

  ahead-has : ∀ {A B} r (β : Events∞ B) (σ : Events∞ A) x c {q b} → Has (M′.ahead r β σ x c) q b → Has (Events∞.force β) q b
  ahead-has r β σ x true  (pastSkip h) = beside-has r β (M′.onward∞ σ (Events∞.force σ)) h
  ahead-has r β σ x false h            = body-has r σ x (Events∞.force β) h

  body-has : ∀ {A B} r (σ : Events∞ A) x (e : Events B) {q b} → Has (M′.body r σ x e) q b → Has e q b
  body-has r σ x (out k a β) atOut        = atOut
  body-has r σ x (out k a β) (pastOut h)  = pastOut (ahead-has r β σ x (M′.before x (Events∞.force β)) h)
  body-has r σ x (skip k β)  (pastSkip h) = pastSkip (ahead-has r β σ x (M′.before x (Events∞.force β)) h)
  body-has r σ x (end c)     atEnd        = atEnd

------------------------------------------------------------------------
-- FLATMAP: every arm of `go` at once

-- A lane, wherever it is subscribed no earlier than `lo`.
Good : ∀ {B} → Pos → MonotonicList B → Set
Good lo m = ∀ p → lo ≤ᵖ p → Above lo (M′.observe m p)

GoodM : ∀ {B} → Pos → Maybe (MonotonicList B) → Set
GoodM lo nothing  = ⊤
GoodM lo (just m) = Good lo m

-- The outer: its events no earlier than `lo`, each lane it opens good.
OAbove : ∀ {B} → Pos → Events (MonotonicList B) → Set
OAbove lo e = ∀ {q b} → Has e q b → lo ≤ᵖ q × GoodM lo b

OAboveM : ∀ {B} → Pos → Maybe (Events∞ (MonotonicList B)) → Set
OAboveM lo nothing  = ⊤
OAboveM lo (just e) = OAbove lo (Events∞.force e)

AboveL : ∀ {B} → Pos → List (Events∞ B) → Set
AboveL lo ls = All (λ l → Above lo (Events∞.force l)) ls

above-mapO : ∀ {A B lo} (F : A → MonotonicList B) (e : Events A) → Above lo e → (∀ a → Good lo (F a)) → OAbove lo (mapᴱ F e)
above-mapO F (out k a r) he hg atOut        = he atOut , hg a
above-mapO F (out k a r) he hg (pastOut h)  = above-mapO F (Events∞.force r) (λ h′ → he (pastOut h′)) hg h
above-mapO F (skip k r)  he hg (pastSkip h) = above-mapO F (Events∞.force r) (λ h′ → he (pastSkip h′)) hg h
above-mapO F (end k)     he hg atEnd        = he atEnd , tt

data EAbove {B} (lo : Pos) : M′.Earliest B → Set where
  none  : EAbove lo M′.none
  found : ∀ {k bs l as} → AboveL lo bs → Above lo (Events∞.force l) → AboveL lo as → EAbove lo (M′.found k bs l as)

earliest-above : ∀ {B lo} (ls : List (Events∞ B)) → AboveL lo ls → EAbove lo (M′.earliest ls)
earliest-above []       []ᴬ        = none
earliest-above (l ∷ ls) (hl ∷ᴬ hs) with M′.head (Events∞.force l) | M′.earliest ls | earliest-above ls hs
... | nothing | M′.none            | none            = none
... | nothing | M′.found k bs c as | found hb hc ha  = found (hl ∷ᴬ hb) hc ha
... | just k  | M′.none            | none            = found []ᴬ hl hs
... | just k  | M′.found k′ bs c as | found hb hc ha with k <ᵖ k′
...   | true  = found []ᴬ hl hs
...   | false = found (hl ∷ᴬ hb) hc ha

admit-ok : ∀ {B lo} op q (m : MonotonicList B) ls qs → Good lo m → lo ≤ᵖ q → AboveL lo ls → All (Good lo) qs
         → AboveL lo (proj₁ (M′.admit op q m ls qs)) × All (Good lo) (proj₁ (proj₂ (M′.admit op q m ls qs)))
admit-ok (M′.mergeᶠ nothing)  q m ls       qs g le hl hq = (g q le ∷ᴬ hl) , hq
admit-ok (M′.mergeᶠ (just n)) q m ls       qs g le hl hq with length ls <ᵇ n
... | true  = (g q le ∷ᴬ hl) , hq
... | false = hl , ++⁺ hq (g ∷ᴬ []ᴬ)
admit-ok M′.switchᶠ           q m ls       qs g le hl hq = (g q le ∷ᴬ []ᴬ) , hq
admit-ok M′.exhaustᶠ          q m []       qs g le hl hq = (g q le ∷ᴬ []ᴬ) , hq
admit-ok M′.exhaustᶠ          q m (l ∷ ls) qs g le hl hq = hl , hq

mutual
  above-go : ∀ {B lo} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t
           → OAboveM lo o → AboveL lo ls → All (Good lo) qs → Above lo (M′.go op o ls qs t)
  above-go op o ls qs idle      ho hl hq h = above-parts op o ls qs idle ho hl hq h
  above-go op o ls qs (pin k u) ho hl hq h = above-left op o ls qs k u (M′.ahead-of k o ls) ho hl hq h

  above-left : ∀ {B lo} op (o : Maybe (Events∞ (MonotonicList B))) ls qs k u c
             → OAboveM lo o → AboveL lo ls → All (Good lo) qs → Above lo (M′.left op o ls qs k u c)
  above-left op o ls qs k u true  ho hl hq (pastSkip h) = above-go op o ls qs (Tail∞.later u) ho hl hq h
  above-left op o ls qs k u false ho hl hq h            = above-parts op o ls qs (pin k u) ho hl hq h

  above-parts : ∀ {B lo} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t
              → OAboveM lo o → AboveL lo ls → All (Good lo) qs → Above lo (M′.parts op o ls qs t)
  above-parts op o ls qs t ho hl hq h with M′.earliest ls | earliest-above ls hl
  ... | M′.none            | none           = above-via op o ls qs t ho hl hq h
  ... | M′.found k bs l as | found hb hc ha = above-race op o k bs l as qs t ho hb hc ha hq h

  above-via : ∀ {B lo} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t
            → OAboveM lo o → AboveL lo ls → All (Good lo) qs → Above lo (M′.viaOuter op o ls qs t)
  above-via op (just e) ls qs t ho hl hq h = above-outer op e ls qs t (Events∞.force e) ho hl hq h

  above-race : ∀ {B lo} op (o : Maybe (Events∞ (MonotonicList B))) k bs l as qs t
             → OAboveM lo o → AboveL lo bs → Above lo (Events∞.force l) → AboveL lo as → All (Good lo) qs
             → Above lo (M′.race op o k bs l as qs t)
  above-race op nothing  k bs l as qs t ho hb hc ha hq h = above-lane op nothing bs l as qs t (Events∞.force l) ho hb hc ha hq h
  above-race op (just e) k bs l as qs t ho hb hc ha hq h with M′.head (Events∞.force e)
  ... | nothing = above-lane op (just e) bs l as qs t (Events∞.force l) ho hb hc ha hq h
  ... | just k′ with k′ <ᵖ k
  ...   | true  = above-outer op e (bs ++ l ∷ as) qs t (Events∞.force e) ho (++⁺ hb (hc ∷ᴬ ha)) hq h
  ...   | false = above-lane op (just e) bs l as qs t (Events∞.force l) ho hb hc ha hq h

  above-outer : ∀ {B lo} op (e : Events∞ (MonotonicList B)) ls qs t x
              → OAbove lo x → AboveL lo ls → All (Good lo) qs → Above lo (M′.outer op e ls qs t x)
  above-outer op e ls qs t (out q m r) hx hl hq h with M′.admit op (q ++ [ ix 1 ]) m ls qs
                                                      | admit-ok op (q ++ [ ix 1 ]) m ls qs (proj₂ (hx atOut)) (≤ᵖ-child q (proj₁ (hx atOut))) hl hq
  above-outer op e ls qs t (out q m r) hx hl hq (pastSkip h) | ls′ , qs′ , d | hl′ , hq′ =
    above-go op (just r) ls′ qs′ (t ∪ d) (λ h′ → hx (pastOut h′)) hl′ hq′ h
  above-outer op e ls       qs       t (skip q r) hx hl hq (pastSkip h) =
    above-go op (just r) ls qs t (λ h′ → hx (pastSkip h′)) hl hq h
  above-outer op e []       []       t (end c) hx hl hq atEnd        = proj₁ (hx atEnd)
  above-outer op e []       (m ∷ qs) t (end c) hx hl hq (pastSkip h) = above-go op nothing [] (m ∷ qs) (t ∪ Events∞.cut e) tt hl hq h
  above-outer op e (l ∷ ls) qs       t (end c) hx hl hq (pastSkip h) = above-go op nothing (l ∷ ls) qs (t ∪ Events∞.cut e) tt hl hq h

  above-lane : ∀ {B lo} op (o : Maybe (Events∞ (MonotonicList B))) bs l as qs t x
             → OAboveM lo o → AboveL lo bs → Above lo x → AboveL lo as → All (Good lo) qs
             → Above lo (M′.lane op o bs l as qs t x)
  above-lane op o bs l as qs t (out k b r) ho hb hx ha hq atOut        = hx atOut
  above-lane op o bs l as qs t (out k b r) ho hb hx ha hq (pastOut h)  =
    above-go op o (bs ++ r ∷ as) qs t ho (++⁺ hb ((λ h′ → hx (pastOut h′)) ∷ᴬ ha)) hq h
  above-lane op o bs l as qs t (skip k r)  ho hb hx ha hq (pastSkip h) =
    above-go op o (bs ++ r ∷ as) qs t ho (++⁺ hb ((λ h′ → hx (pastSkip h′)) ∷ᴬ ha)) hq h
  above-lane op o bs l as (m ∷ qs) t (end c) ho hb hx ha (g ∷ᴬ hq) (pastSkip h) =
    above-go op o (M′.enter m (c ++ [ ix 1 ]) ∷ bs ++ as) qs (t ∪ Events∞.cut l) ho (g (c ++ [ ix 1 ]) (≤ᵖ-child c (hx atEnd)) ∷ᴬ ++⁺ hb ha) hq h
  above-lane op nothing  []      l []      [] t (end c) ho hb hx ha hq atEnd        = hx atEnd
  above-lane op nothing  []      l (a ∷ as) [] t (end c) ho hb hx ha hq (pastSkip h) = above-go op nothing (a ∷ as) [] (t ∪ Events∞.cut l) ho ha hq h
  above-lane op nothing  (b ∷ bs) l as     [] t (end c) ho hb hx ha hq (pastSkip h) = above-go op nothing ((b ∷ bs) ++ as) [] (t ∪ Events∞.cut l) ho (++⁺ hb ha) hq h
  above-lane op (just e) bs      l as      [] t (end c) ho hb hx ha hq (pastSkip h) = above-go op (just e) (bs ++ as) [] (t ∪ Events∞.cut l) ho (++⁺ hb ha) hq h

------------------------------------------------------------------------
-- A subscription shows nothing before where it was made

-- Outside the fragment: a timeline's frames and a defer's fold.
postulate
  above-cold  : ∀ {Γ A} c p (ρ : U.NEnv Γ) → Above p (U.meaning (U.subscribe {Γ} {A} (cold c) p) ρ)
  above-defer : ∀ {Γ A} (l : Later Timeline Γ A) p (ρ : U.NEnv Γ) → Above p (U.meaning (U.subscribe (defer l) p) ρ)

above-sub : ∀ {Γ A} (o : PObs Γ A) p (ρ : U.NEnv Γ) → Above p (U.meaning (U.subscribe o p) ρ)
above-sub (cold c)          p ρ = above-cold c p ρ
above-sub empty             p ρ = above-of p 0 [] (≤ᵖ-child p (inj₁ refl))
above-sub (of xs)           p ρ = above-of p 0 xs (≤ᵖ-child p (inj₁ refl))
above-sub (map f s)         p ρ = above-map f _ (above-sub s p ρ)
above-sub (scan f z s)      p ρ = above-scan f z _ (above-sub s p ρ)
above-sub (takeWhile i q s) p ρ = above-take i q _ (above-sub s p ρ)
above-sub (flatMap op f s)  p ρ =
  above-go (flatOp op) (just (U.outer∞ (λ a q → U.subscribe (f a) q) (U.subscribe s p) ρ)) [] [] idle
    (λ h → above-mapO _ _ (above-sub s p ρ) (λ a q le → above-≤ le (above-sub (f a) q ρ)) h) []ᴬ []ᴬ
above-sub (connect s b)     p ρ h =
  above-≤ (≤ᵖ-child p (inj₁ refl)) (above-sub b (p ++ [ ix 0 ]) (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ ∷ᴬ ρ)) (beside-has (p ++ [ ix 1 ]) (U.stateᴺ (U.subscribe b (p ++ [ ix 0 ])) (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ ∷ᴬ ρ)) (U.stateᴺ (U.subscribe s (p ++ [ ix 1 ])) ρ) h)
above-sub (connected i)     p ρ = above-rejoin-at p (lookup ρ i)
above-sub (defer l)         p ρ = above-defer l p ρ

------------------------------------------------------------------------
-- What the jobs bound

ReadyJ : Pos → Job → Set
ReadyJ lo (π , t , p) = Ready t p lo

ReadyT : Pos → Tag × Pos → Set
ReadyT lo (t , p) = Ready t p lo

jobsAt-ok : ∀ {lo} π rs → All (ReadyJ lo) rs → All (ReadyT lo) (jobsAt π rs)
jobsAt-ok π []               []ᴬ        = []ᴬ
jobsAt-ok π ((q , t , p) ∷ rs) (h ∷ᴬ hs) with π ≟ᴸ q
... | true  = h ∷ᴬ jobsAt-ok π rs hs
... | false = jobsAt-ok π rs hs

OfOK : Pos → Maybe (ℕ × Pos) → Set
OfOK lo nothing        = ⊤
OfOK lo (just (i , p)) = lo ≤ᵖ (p ++ [ ix i ])

ofAt-ok : ∀ {lo} ts → All (ReadyT lo) ts → OfOK lo (ofAt ts)
ofAt-ok []                   []ᴬ        = tt
ofAt-ok ((next i , p) ∷ ts)  (h ∷ᴬ hs) = h
ofAt-ok ((go , p) ∷ ts)      (h ∷ᴬ hs) = ofAt-ok ts hs
ofAt-ok ((att , p) ∷ ts)     (h ∷ᴬ hs) = ofAt-ok ts hs
ofAt-ok ((attBody , p) ∷ ts) (h ∷ᴬ hs) = ofAt-ok ts hs
ofAt-ok ((owed , p) ∷ ts)    (h ∷ᴬ hs) = ofAt-ok ts hs
ofAt-ok ((owedCp , p) ∷ ts)  (h ∷ᴬ hs) = ofAt-ok ts hs
ofAt-ok ((owedCut , p) ∷ ts) (h ∷ᴬ hs) = ofAt-ok ts hs
ofAt-ok ((feeding js , p) ∷ ts) (h ∷ᴬ hs) = ofAt-ok ts hs

TakeOK : Pos → Owing → Set
TakeOK lo (endsAt k) = lo ≤ᵖ (k ++ [ last ])
TakeOK lo _          = ⊤

takeAt-ok : ∀ {lo} ts → All (ReadyT lo) ts → TakeOK lo (takeAt ts)
takeAt-ok []                   []ᴬ        = tt
takeAt-ok ((owedCp , k) ∷ ts)  (h ∷ᴬ hs) = h
takeAt-ok ((owedCut , k) ∷ ts) (h ∷ᴬ hs) = tt
takeAt-ok ((next i , p) ∷ ts)  (h ∷ᴬ hs) = takeAt-ok ts hs
takeAt-ok ((go , p) ∷ ts)      (h ∷ᴬ hs) = takeAt-ok ts hs
takeAt-ok ((att , p) ∷ ts)     (h ∷ᴬ hs) = takeAt-ok ts hs
takeAt-ok ((attBody , p) ∷ ts) (h ∷ᴬ hs) = takeAt-ok ts hs
takeAt-ok ((owed , p) ∷ ts)    (h ∷ᴬ hs) = takeAt-ok ts hs
takeAt-ok ((feeding js , p) ∷ ts) (h ∷ᴬ hs) = takeAt-ok ts hs

PendOK : Pos → Maybe Pos → Set
PendOK lo nothing  = ⊤
PendOK lo (just p) = lo ≤ᵖ p

pendAt-ok : ∀ {lo} π (ps : List (List ℕ × Pos)) → All (λ x → lo ≤ᵖ proj₂ x) ps → PendOK lo (pendAt π ps)
pendAt-ok π []             []ᴬ        = tt
pendAt-ok π ((q , p) ∷ ps) (h ∷ᴬ hs) with π ≟ᴸ q
... | true  = h
... | false = pendAt-ok π ps hs

attached-ok : ∀ {lo} rs → All (ReadyJ lo) rs → All (λ x → lo ≤ᵖ proj₂ x) (attached rs)
attached-ok []                        []ᴬ        = []ᴬ
attached-ok ((π , attBody , p) ∷ rs)  (h ∷ᴬ hs) = inj₂ h ∷ᴬ attached-ok rs hs
attached-ok ((π , go , p) ∷ rs)       (h ∷ᴬ hs) = attached-ok rs hs
attached-ok ((π , att , p) ∷ rs)      (h ∷ᴬ hs) = attached-ok rs hs
attached-ok ((π , owed , p) ∷ rs)     (h ∷ᴬ hs) = attached-ok rs hs
attached-ok ((π , next i , p) ∷ rs)   (h ∷ᴬ hs) = attached-ok rs hs
attached-ok ((π , owedCp , p) ∷ rs)   (h ∷ᴬ hs) = attached-ok rs hs
attached-ok ((π , owedCut , p) ∷ rs)  (h ∷ᴬ hs) = attached-ok rs hs
attached-ok ((π , feeding js , p) ∷ rs) (h ∷ᴬ hs) = attached-ok rs hs

-- At the last event, every job on the stack is ready.
chain-ready : ∀ {lo S} rs → Chain lo S rs → All (ReadyJ lo) rs
chain-ready []               stop       = []ᴬ
chain-ready ((π , t , p) ∷ rs) (link u f) = proj₁ (f _ settled-refl) ∷ᴬ chain-ready rs (proj₂ (f _ settled-refl))

------------------------------------------------------------------------
-- What a binder's joiners are owed

-- Every joiner a feed still owes is fed no earlier than `lo`.
LevelOK : ∀ {X} → Pos → Level X → Set
LevelOK lo (e , p , js) = All (λ x → lo ≤ᵖ (p ++ [ subᴾ (proj₂ x) ])) js

FeedJ : Pos → List (List ℕ × Pos) × Pos → Set
FeedJ lo (js , p) = Feed p js lo

asc-all : ∀ j js → Asc j js → All (λ x → j <ᵖ proj₂ x ≡ true) js
asc-all j []               a       = []ᴬ
asc-all j ((q , j′) ∷ js) (h , a) = h ∷ᴬ mapᴬ (λ {x} h′ → <ᵖ-trans j j′ (proj₂ x) h h′) (asc-all j′ js a)

feed-all : ∀ {lo} p js → Feed p js lo → All (λ x → lo ≤ᵖ (p ++ [ subᴾ (proj₂ x) ])) js
feed-all p []              _        = []ᴬ
feed-all p ((q , j) ∷ js) (le , a) = le ∷ᴬ mapᴬ (λ {x} h → sib p (<ᵖ-sub j (proj₂ x) h) le) (asc-all j js a)

feedingsAt-ok : ∀ {lo} ts → All (ReadyT lo) ts → All (FeedJ lo) (feedingsAt ts)
feedingsAt-ok []                      []ᴬ        = []ᴬ
feedingsAt-ok ((feeding js , p) ∷ ts) (h ∷ᴬ hs) = h ∷ᴬ feedingsAt-ok ts hs
feedingsAt-ok ((go , p) ∷ ts)         (h ∷ᴬ hs) = feedingsAt-ok ts hs
feedingsAt-ok ((att , p) ∷ ts)        (h ∷ᴬ hs) = feedingsAt-ok ts hs
feedingsAt-ok ((attBody , p) ∷ ts)    (h ∷ᴬ hs) = feedingsAt-ok ts hs
feedingsAt-ok ((owed , p) ∷ ts)       (h ∷ᴬ hs) = feedingsAt-ok ts hs
feedingsAt-ok ((next i , p) ∷ ts)     (h ∷ᴬ hs) = feedingsAt-ok ts hs
feedingsAt-ok ((owedCp , p) ∷ ts)     (h ∷ᴬ hs) = feedingsAt-ok ts hs
feedingsAt-ok ((owedCut , p) ∷ ts)    (h ∷ᴬ hs) = feedingsAt-ok ts hs

zipF-ok : ∀ {X lo} (es : List (Ev X)) fs → All (FeedJ lo) fs → All (LevelOK lo) (zipF es fs)
zipF-ok []       fs               hf         = []ᴬ
zipF-ok (e ∷ es) []               hf         = []ᴬ
zipF-ok (e ∷ es) ((js , p) ∷ fs) (h ∷ᴬ hf) = feed-all p js h ∷ᴬ zipF-ok es fs hf

-- THE NAMING FACT: the entries a feed owes at path `π` name the joiner
-- there, joined at `j`; an owed end was made after it joined, and is the
-- binder's one end `c`.
Ends : ∀ {X} → Ev X → Pos → Pos → Pos → Set
Ends (nx _) j c p = ⊤
Ends cp     j c p = j <ᵖ p ≡ true × c ≡ p

NamedL : ∀ {X} → List ℕ → Pos → Pos → Level X → Set
NamedL π j c (e , p , js) = All (λ x → π ≡ proj₁ x → proj₂ x ≡ j × Ends e j c p) js

Named : ∀ {X} → List ℕ → Pos → Bind X → Set
Named π j (bind c ls) = All (NamedL π j (endedAt ls)) ls

≟ᴸ-sound : ∀ a b → a ≟ᴸ b ≡ true → a ≡ b
≟ᴸ-sound []       []       e = refl
≟ᴸ-sound (a ∷ as) (b ∷ bs) e with a ≡ᵇ b in h
≟ᴸ-sound (a ∷ as) (b ∷ bs) e  | true = cong₂ _∷_ (≡ᵇ⇒≡ a b (subst T (sym h) tt)) (≟ᴸ-sound as bs e)
≟ᴸ-sound (a ∷ as) (b ∷ bs) () | false
≟ᴸ-sound []       (b ∷ bs) ()
≟ᴸ-sound (a ∷ as) []       ()

mem-ok : ∀ π {j} {E : Set} {P : Pos → Set} js → member π js ≡ true
       → All (λ x → π ≡ proj₁ x → proj₂ x ≡ j × E) js → All (λ x → P (proj₂ x)) js → P j × E
mem-ok π ((q , j′) ∷ js) m (n ∷ᴬ ns) (h ∷ᴬ hs) with π ≟ᴸ q in e
... | true with n (≟ᴸ-sound π q e)
...   | refl , x = h , x
mem-ok π ((q , j′) ∷ js) m (n ∷ᴬ ns) (h ∷ᴬ hs) | false = mem-ok π js m ns hs

owed-ok : ∀ {X lo} π j c (ls : List (Level X)) → All (NamedL π j c) ls → All (LevelOK lo) ls → All (λ x → lo ≤ᵖ proj₁ x) (owedTo π j ls)
owed-ok π j c []                   []ᴬ        []ᴬ        = []ᴬ
owed-ok π j c ((nx v , p , js) ∷ ls) (n ∷ᴬ ns) (h ∷ᴬ hs) with member π js in m
... | true  = ++⁺ (owed-ok π j c ls ns hs) (proj₁ (mem-ok π js m n h) ∷ᴬ []ᴬ)
... | false = ++⁺ (owed-ok π j c ls ns hs) []ᴬ
owed-ok π j c ((cp , p , js) ∷ ls)   (n ∷ᴬ ns) (h ∷ᴬ hs) = owed-ok π j c ls ns hs

end-ok : ∀ {X lo} π j c (ls : List (Level X)) → endOwed π ls ≡ true → All (NamedL π j c) ls → All (LevelOK lo) ls
       → j <ᵖ c ≡ true × lo ≤ᵖ (c ++ [ subᴾ j ])
end-ok π j c ((nx v , p , js) ∷ ls) eo (n ∷ᴬ ns) (h ∷ᴬ hs) = end-ok π j c ls eo ns hs
end-ok π j c ((cp , p , js) ∷ ls)   eo (n ∷ᴬ ns) (h ∷ᴬ hs) with member π js in m
... | true with mem-ok π js m n h
...   | le , lt , refl = lt , le
end-ok π j c ((cp , p , js) ∷ ls)   eo (n ∷ᴬ ns) (h ∷ᴬ hs) | false = end-ok π j c ls eo ns hs

------------------------------------------------------------------------
-- THE FLOOR: the ghost holds nothing before its jobs' bounds

BookOK : Pos → Book → Set
BookOK lo b = All (ReadyJ lo) (Book.rets b) × All (λ x → lo ≤ᵖ proj₂ x) (Book.pends b)

-- A binder's subject as its joiners read it: a live source's run, no
-- earlier than `lo`; a closed one's end.
BindOK : ∀ {X} → Pos → Bind X → Events X → Set
BindOK lo (bind false ls) e = All (LevelOK lo) ls × Above lo e
BindOK lo (bind true ls)  e = All (LevelOK lo) ls × e ≡ end (endedAt ls)

EnvOK : ∀ {Γ} → Pos → All Bind Γ → U.NEnv Γ → Set
EnvOK lo []ᴬ        []ᴬ        = ⊤
EnvOK lo (b ∷ᴬ β)   (e ∷ᴬ ρ)   = BindOK lo b e × EnvOK lo β ρ

env-lookup : ∀ {Γ X lo} {β : All Bind Γ} {ρ : U.NEnv Γ} (x : X ∈ Γ) → EnvOK lo β ρ → BindOK lo (lookup β x) (lookup ρ x)
env-lookup {β = b ∷ᴬ β} {e ∷ᴬ ρ} (here refl) (h , _) = h
env-lookup {β = b ∷ᴬ β} {e ∷ᴬ ρ} (there x)   (_ , hs) = env-lookup x hs

-- The naming fact at every joiner, through the binders the ghost builds.
mutual
  Nm : ∀ {Γ A} → Book → List ℕ → All Bind Γ → St Γ A → Set
  Nm b π β (joinS j true x)      = Named π j (lookup β x)
  Nm b π β (mapS f s)            = Nm b (π ++ [ 0 ]) β s
  Nm b π β (scanS f z s)         = Nm b (π ++ [ 0 ]) β s
  Nm b π β (cutS l a s)          = Nm b (π ++ [ 0 ]) β s
  Nm b π β (lnS l s)             = Nm b (π ++ [ 0 ]) β s
  Nm b π β (takeS i q s)         = Nm b (π ++ [ 0 ]) β s
  Nm b π β (flatS op f d n o ls) = Nm b (π ++ [ 0 ]) β o × NmL b π 0 β ls
  Nm b π β (connS k o bd)        =
    Nm b (π ++ [ 0 ]) β o × Nm b (π ++ [ 1 ]) (bind (CS.closed k) (zipF (CS.feeds k) (feedingsAt (jobsAt π (Book.rets b)))) ∷ᴬ β) bd
  Nm b π β _                     = ⊤

  NmL : ∀ {Γ B} → Book → List ℕ → ℕ → All Bind Γ → List (St Γ B) → Set
  NmL b π i β []                           = ⊤
  NmL b π i β (lnS l (cutS true a s) ∷ ls) = Nm b (π ++ [ suc i ] ++ [ 0 ] ++ [ 0 ]) β s × NmL b π (suc i) β ls
  NmL b π i β (_ ∷ ls)                     = NmL b π (suc i) β ls

above-joinᶜ : ∀ {Γ X lo} π j (x : X ∈ Γ) (bd : Bind X) (ρ : U.NEnv Γ) → Named π j bd → BindOK lo bd (lookup ρ x)
            → Above lo (U.meaning (joinᶜ π j x bd) ρ)
above-joinᶜ π j x (bind false ls) ρ nm (lv , he) =
  above-fed (owedTo π j ls) _ (owed-ok π j (endedAt ls) ls nm lv) (above-rejoin j (lookup ρ x) he)
above-joinᶜ π j x (bind true ls)  ρ nm (lv , he) with endOwed π ls in eo
... | false = λ ()
... | true  = above-fed (owedTo π j ls) _ (owed-ok π j (endedAt ls) ls nm lv) (subst (λ e → Above _ (rejoin j e)) (sym he) ended)
  where
    ended : Above _ (rejoin j (end (endedAt ls)))
    ended with end-ok π j (endedAt ls) ls eo nm lv
    ... | lt , le rewrite lt = λ { atEnd → le }

AboveN : ∀ {Γ A} → Pos → U.NEnv Γ → U.Node Γ A → Set
AboveN lo ρ n = Above lo (U.meaning n ρ)

states-ok : ∀ {Γ A lo} (ρ : U.NEnv Γ) (ns : List (U.Node Γ A)) → All (AboveN lo ρ) ns → AboveL lo (U.states ns ρ)
states-ok ρ []       []ᴬ        = []ᴬ
states-ok ρ (n ∷ ns) (h ∷ᴬ hs) = h ∷ᴬ states-ok ρ ns hs

MAbove : ∀ {Γ A} → Pos → U.NEnv Γ → Maybe (U.Node Γ A) → Set
MAbove lo ρ nothing  = ⊤
MAbove lo ρ (just n) = AboveN lo ρ n

above-flatᶜ : ∀ {Γ A B lo} op (f : A → PObs Γ B) (o : Maybe (U.Node Γ A)) ns (ρ : U.NEnv Γ)
            → MAbove lo ρ o → All (AboveN lo ρ) ns → Above lo (U.meaning (flatᶜ op f o ns) ρ)
above-flatᶜ op f nothing  []       ρ ho hn = λ ()
above-flatᶜ op f nothing  (n ∷ ns) ρ ho hn = above-go (flatOp op) nothing (U.states (n ∷ ns) ρ) [] idle tt (states-ok ρ (n ∷ ns) hn) []ᴬ
above-flatᶜ op f (just o) ns       ρ ho hn =
  above-go (flatOp op) (just (U.outer∞ (λ a q → U.subscribe (f a) q) o ρ)) (U.states ns ρ) [] idle
    (λ h → above-mapO _ _ ho (λ a q le → above-≤ le (above-sub (f a) q ρ)) h) (states-ok ρ ns hn) []ᴬ

-- A closed source's node, typed by the source it was.
idleOf : ∀ {Γ X} → St Γ X → U.Node Γ X
idleOf _ = U.idleᶜ

mutual
  floor-gh : ∀ {Γ A lo} b π (β : All Bind Γ) (s : St Γ A) (ρ : U.NEnv Γ) → BookOK lo b → EnvOK lo β ρ → Nm b π β s
           → Above lo (U.meaning (gh b π β s) ρ)
  floor-gh b π β (pend o) ρ bk ev nm with pendAt π (Book.pends b) | pendAt-ok π (Book.pends b) (proj₂ bk)
  ... | just p  | le = above-≤ le (above-sub o p ρ)
  ... | nothing | _  = λ ()
  floor-gh b π β (ofS xs) ρ bk ev nm with ofAt (jobsAt π (Book.rets b)) | ofAt-ok (jobsAt π (Book.rets b)) (jobsAt-ok π (Book.rets b) (proj₁ bk))
  ... | just (i , p) | le = above-of p i xs le
  ... | nothing      | _  = λ ()
  floor-gh b π β doneS              ρ bk ev nm = λ ()
  floor-gh b π β (mapS f s)         ρ bk ev nm = above-map f _ (floor-gh b (π ++ [ 0 ]) β s ρ bk ev nm)
  floor-gh b π β (scanS f z s)      ρ bk ev nm = above-scan f z _ (floor-gh b (π ++ [ 0 ]) β s ρ bk ev nm)
  floor-gh b π β (cutS true a s)    ρ bk ev nm = floor-gh b (π ++ [ 0 ]) β s ρ bk ev nm
  floor-gh b π β (cutS false a s)   ρ bk ev nm = λ ()
  floor-gh b π β (lnS l s)          ρ bk ev nm = floor-gh b (π ++ [ 0 ]) β s ρ bk ev nm
  floor-gh b π β (takeS i q s)      ρ bk ev nm with takeAt (jobsAt π (Book.rets b)) | takeAt-ok (jobsAt π (Book.rets b)) (jobsAt-ok π (Book.rets b) (proj₁ bk))
  ... | free     | _  = above-take i q _ (floor-gh b (π ++ [ 0 ]) β s ρ bk ev nm)
  ... | endsAt k | le = λ { atEnd → le }
  ... | over     | _  = λ ()
  floor-gh b π β (flatS op f true n o ls)  ρ bk ev (no , nl) =
    above-flatᶜ op f nothing (lanes b π 0 β ls) ρ tt (floor-lanes b π 0 β ls ρ bk ev nl)
  floor-gh b π β (flatS op f false n o ls) ρ bk ev (no , nl) =
    above-flatᶜ op f (just (gh b (π ++ [ 0 ]) β o)) (lanes b π 0 β ls) ρ (floor-gh b (π ++ [ 0 ]) β o ρ bk ev no) (floor-lanes b π 0 β ls ρ bk ev nl)
  floor-gh b π β (connS k o bd) ρ bk ev (no , nb)
    with jobsAt π (Book.rets b) | jobsAt-ok π (Book.rets b) (proj₁ bk)
  ... | ts | hts with owedAt ts ∨ not (CS.srcLive k)
  ...   | true  = λ ()
  ...   | false with CS.closed k
  ...     | true  = λ h →
    floor-gh b (π ++ [ 1 ]) (bind true (zipF (CS.feeds k) (feedingsAt ts)) ∷ᴬ β) bd (end (endedAt (zipF (CS.feeds k) (feedingsAt ts))) ∷ᴬ ρ) bk
      ((zipF-ok (CS.feeds k) (feedingsAt ts) (feedingsAt-ok ts hts) , refl) , ev) nb
      (beside-has root (U.stateᴺ (gh b (π ++ [ 1 ]) (bind true (zipF (CS.feeds k) (feedingsAt ts)) ∷ᴬ β) bd) (end (endedAt (zipF (CS.feeds k) (feedingsAt ts))) ∷ᴬ ρ)) (U.stateᴺ (idleOf o) ρ) h)
  ...     | false = λ h →
    floor-gh b (π ++ [ 1 ]) (bind false (zipF (CS.feeds k) (feedingsAt ts)) ∷ᴬ β) bd (U.meaning (gh b (π ++ [ 0 ]) β o) ρ ∷ᴬ ρ) bk
      ((zipF-ok (CS.feeds k) (feedingsAt ts) (feedingsAt-ok ts hts) , (λ h′ → floor-gh b (π ++ [ 0 ]) β o ρ bk ev no h′)) , ev) nb
      (beside-has root (U.stateᴺ (gh b (π ++ [ 1 ]) (bind false (zipF (CS.feeds k) (feedingsAt ts)) ∷ᴬ β) bd) (U.meaning (gh b (π ++ [ 0 ]) β o) ρ ∷ᴬ ρ)) (U.stateᴺ (gh b (π ++ [ 0 ]) β o) ρ) h)
  floor-gh b π β (joinS j true x)  ρ bk ev nm = above-joinᶜ π j x (lookup β x) ρ nm (env-lookup x ev)
  floor-gh b π β (joinS j false x) ρ bk ev nm = λ ()

  floor-lanes : ∀ {Γ B lo} b π i (β : All Bind Γ) (ls : List (St Γ B)) (ρ : U.NEnv Γ) → BookOK lo b → EnvOK lo β ρ → NmL b π i β ls
              → All (AboveN lo ρ) (lanes b π i β ls)
  floor-lanes b π i β []                               ρ bk ev nl        = []ᴬ
  floor-lanes b π i β (lnS l (cutS true a s) ∷ ls)     ρ bk ev (nm , nl) =
    floor-gh b (π ++ [ suc i ] ++ [ 0 ] ++ [ 0 ]) β s ρ bk ev nm ∷ᴬ floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (lnS l (cutS false a s) ∷ ls)    ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (lnS l (pend o) ∷ ls)            ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (lnS l (ofS xs) ∷ ls)            ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (lnS l doneS ∷ ls)               ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (lnS l (joinS j g x) ∷ ls)       ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (lnS l (mapS f s) ∷ ls)          ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (lnS l (scanS f z s) ∷ ls)       ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (lnS l (lnS l′ s) ∷ ls)          ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (lnS l (takeS i′ q s) ∷ ls)      ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (lnS l (flatS op f d n o l′) ∷ ls) ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (lnS l (connS k o bd) ∷ ls)      ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (pend o ∷ ls)                    ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (ofS xs ∷ ls)                    ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (doneS ∷ ls)                     ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (joinS j g x ∷ ls)               ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (mapS f s ∷ ls)                  ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (scanS f z s ∷ ls)               ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (cutS l a s ∷ ls)                ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (takeS i′ q s ∷ ls)              ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (flatS op f d n o l′ ∷ ls)       ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl
  floor-lanes b π i β (connS k o bd ∷ ls)              ρ bk ev nl = floor-lanes b π (suc i) β ls ρ bk ev nl

------------------------------------------------------------------------
-- THE LEAST EVENT

-- The naming fact, at the root of a configuration's tree.
NmTop : ∀ {R} → Conf R → Set
NmTop ⟨ c , s , m , p , rs ⟩ = Nm (book rs (focusing c m p ++ attached rs)) [] []ᴬ (spike.StateTree3.plug c s)

-- `Valid` reads only shape, so it does not carry this: a new invariant
-- over the tree and the feeding jobs, kept by every step that joins,
-- feeds or ends a source.
postulate
  named : ∀ {R} {o : PObs [] R} {k sh} → From o k sh → quiet k ≡ true → NmTop k

floor : ∀ {R} (k : Conf R) {lo} → quiet k ≡ true → Fwd lo k → NmTop k → Above lo (residual k)
floor ⟨ c , s , absorbed , p , rs ⟩ refl (_ , ch , _) nm =
  floor-gh (book rs (attached rs)) [] []ᴬ (spike.StateTree3.plug c s) []ᴬ (chain-ready rs ch , attached-ok rs (chain-ready rs ch)) tt nm
floor ⟨ c , s , subscribing , p , rs ⟩ () f nm
floor ⟨ c , s , resuming t , p , rs ⟩  () f nm
floor ⟨ c , s , rising e , p , rs ⟩    () f nm

-- Along a run, spike 4's invariant, at a watermark no earlier than
-- anything shown.
fwd-from : ∀ {R} {o : PObs [] R} {k sh} → From o k sh → Σ Pos λ lo → Valid k × Fwd lo k × All (λ x → proj₁ x ≤ᵖ lo) sh
fwd-from {o = o} loaded = [] , load-ok o , (refl , stop , tt) , []ᴬ
fwd-from (stepped {k = k} fr e) with fwd-from fr
... | lo , v , f , al with step k | step-ok k v | step-fwd k v f | e
...   | _ | v′ | lo′ , O.quiet le , O.⟪ f′ ⟫ | refl = lo′ , v′ , f′ , ++⁺ (mapᴬ (λ h → ≤ᵖ-trans h le) al) []ᴬ
...   | _ | v′ | lo′ , O.shown le , O.⟪ f′ ⟫ | refl = lo′ , v′ , f′ , ++⁺ (mapᴬ (λ h → ≤ᵖ-trans h le) al) (inj₁ refl ∷ᴬ []ᴬ)

-- THE LEAST EVENT: at every quiet configuration, nothing the ghost
-- still holds comes before anything the root was shown.
least : ∀ {R} {o : PObs [] R} {k sh} → From o k sh → quiet k ≡ true → All (λ x → Above (proj₁ x) (residual k)) sh
least {k = k} fr qk with fwd-from fr
... | lo , v , f , al = mapᴬ (λ le {q} {b} h → above-≤ le (floor k qk f (named fr qk)) h) al
