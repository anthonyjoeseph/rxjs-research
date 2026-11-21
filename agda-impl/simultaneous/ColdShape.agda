{-# OPTIONS --guardedness #-}

-- WHAT EACH ROW OF THE ELABORATED COLD IS (`cold-rows`).  A row under the
-- subscription is a value the scan read before the tick, or an end.  A
-- value read past the tick lies where the cold's step fires it
-- (`val-row`); a completion read past it, where the cold's end hands its
-- lane on (`cd-row`); each renders its step under that instant.  The
-- whole ends under the subscription or past the cold's end (`mg-end`); a
-- step's render ends before that, so its end never ends the whole.  An
-- end under the subscription leaves no row of a later tick behind it
-- (`early-mg`).
module simultaneous.ColdShape where

open import Data.Bool using (Bool; true; false; T; _∨_; if_then_else_)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; _+_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; +-monoʳ-≤; +-monoʳ-<; n<1+n; m<m+n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)

open import Tree using (mergeᶠ; cold; of; map)
open import denotation.Position using (Pos; ix; last; root; cascade; _∙_; _⊕_; _≟ᵖ_; instant; nested; fired; Root; _▸_; tickᴿ; _<ˡ_)
  renaming (tick to tickᵖ)
open import denotation.Events using (Timeline; Events; fresh; From; done; quiet; at; Frame; emit; stall; close; Frame∞; From∞;
  frames; burst; start; timelineAt; ofᴱ; <ᵖ-part; ix-<)
open import denotation.EmissionSet using (EmissionSet; Den; DenEnv; enter; Ev; out; skip; end; pin; InE; at-out; at-skip; at-end;
  on-out; on-skip; _≺_; _≼_; map-out; map-skip; map-pin; map-end; module Op; module Joining; module Bounded; module Merge; module Scan)
open import denotation.Read using (Visible)
open import denotation.Laws.Modulus using (≺-trans; ≼-refl; ≺→≼; ≺-≼-≺; ≼-≺-≺; ≼-antisym; ≼-or-≻; ≺-ext; ≺-absurd)
open import denotation.Laws.Worlds using (_⊑_; ⊑-trans; ⊑-refl; ⊕-assoc)
open import denotation.Laws.Worlds.Leaves using (of-reach; of-end; ine-pin)
open import denotation.Laws.Cut using (ix-asc)
open import denotation.Laws.Nth using (module Nths)
open import denotation.Laws.Truth using (instant-⊑)
open import denotation.Simultaneity using (same-timer)
open import simultaneous.HeldComb using (ev)
open import simultaneous.SObs using (lone; Tag; val; cdone; tick; module Elaborate)
open import simultaneous.InstEmit using (instEmit; mark; value; begin; over)
open import simultaneous.Routed using (nm)
open import simultaneous.Instants using (below; ≺-instant; instant-≺; past-tick)
open import simultaneous.CombSent using (assoc³)
open import simultaneous.ColdFew using (Fresh; fresh-⊑; fresh-self; fresh-past; tick-⊑; ⊑₂; sep; Fired; f-out; f-skip; f-end; Leaf;
  start-lf; last-tick; O; o-row; o-under; module Pair; Ticks; Tickless; Rendered; Mint; module Core)
import simultaneous.ColdFew as CF

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; coldˢ; render; concatˢ)

-- THE COLD'S ROWS, subscribed at `p`: its synchronous values and end lie
-- in the subscribe burst, named `root`.  Each async step at `I` renders
-- under its lane at `I ∙ [ ix 1 ]`: a value step's `of` sends begin,
-- value and over beneath `nm I ⊕ [ ix 0 ]`, the over at `opos I`.  A
-- completion is an instant of its own, even straight after a value: its
-- begin lies where a value step's does, under the name one queued lane
-- further down, and the cold's end carries that route
-- (`simultaneous.Routed.Carried`) from where the step's lane completes.
data ColdRow {A : Set} (p : Pos) : Pos → Ev (IE A) → Set where
  now-value  : ∀ zs {a} → ColdRow p (p ⊕ zs) (out (instEmit (value a) root))
  now-end    : ∀ zs → ColdRow p (p ⊕ zs) end
  step-begin : ∀ {t e l} → ColdRow p (cascade t e l ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ []))
                                     (out (instEmit (mark begin) (nm (cascade t e l ∙ []))))
  step-value : ∀ {t e i a} → ColdRow p (cascade t e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ []))
                                       (out (instEmit (value a) (nm (cascade t e (ix i) ∙ []))))
  step-over  : ∀ {t e i} → ColdRow p (cascade t e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ []))
                                     (out (instEmit (mark over) (nm (cascade t e (ix i) ∙ []))))
  step-end   : ∀ {t e} → ColdRow p (cascade t e last ∙ (ix 1 ∷ last ∷ [])) end

------------------------------------------------------------------------
-- A cold leaf's stream: one end, after every other row

ine-end : ∀ {A} {es : Events A} {c c′} → InE es c end → InE es c′ end → c ≡ c′
ine-end at-end      at-end       = refl
ine-end (on-out x)  (on-out x′)  = ine-end x x′
ine-end (on-skip x) (on-skip x′) = ine-end x x′

▸-tick : ∀ r l → tickᵖ (r ▸ l) ≡ tickᴿ r
▸-tick (nested s)  l = tick-⊑ {s} ([ l ] , refl)
▸-tick (fired t e) l = refl

lab-≺ : ∀ t e {a b} ys zs → T (a <ˡ b) → (cascade t e a ∙ ys) ≺ (cascade t e b ∙ zs)
lab-≺ t e {a} {b} ys zs h = instant-≺ (cascade t e a ∙ ys) (cascade t e b ∙ zs) (below (subst T (sym (same-timer t e a b)) h))

ix-step : ∀ r i → (r ▸ ix i) ≺ (r ▸ ix (suc i))
ix-step (nested s)  i = ix-asc s (n<1+n i)
ix-step (fired t e) i = lab-≺ t e {ix i} {ix (suc i)} [] [] (Equivalence.from T-≡ (ix-< (n<1+n i)))

ix-last : ∀ r i → (r ▸ ix i) ≺ (r ▸ last)
ix-last (nested s)  i = Equivalence.from T-≡ (<ᵖ-part s [] [] refl)
ix-last (fired t e) i = lab-≺ t e {ix i} {last} [] [] tt

≺≼ : ∀ x y q → x ≺ y → y ≼ q → x ≼ q
≺≼ x y q a b = ≺→≼ {x} {q} (≺-≼-≺ {x} {y} {q} a b)

lt-last : ∀ {τ t} r → tickᴿ r < τ + suc t → tickᵖ (r ▸ last) < τ + suc t
lt-last r h = subst (_< _) (sym (▸-tick r last)) h

mutual
  frames-aft : ∀ {A t} τ e (m : From A t) {y v} → tickᵖ e < τ + t → InE (frames τ e m) y v → e ≼ y
  frames-aft τ e done         h at-end = ≼-refl {e}
  frames-aft τ e quiet        h ()
  frames-aft τ e (at t′ le b) {y} h x =
    ≺≼ e (cascade (τ + t′) e (ix 0) ∙ []) y (past-tick e {τ + t′} {e} {ix 0} {[]} (≤-trans h (+-monoʳ-≤ τ le)))
       (burst-aft τ (fired (τ + t′) e) 0 b (+-monoʳ-< τ (n<1+n t′)) x)

  burst-aft : ∀ {A t} τ r i (b : Frame A t) {y v} → tickᴿ r < τ + suc t → InE (burst τ r i b) y v → (r ▸ ix i) ≼ y
  burst-aft τ r i (emit _ k) h at-out      = ≼-refl {r ▸ ix i}
  burst-aft τ r i (emit _ k) {y} h (on-out x)  = ≺≼ (r ▸ ix i) (r ▸ ix (suc i)) y (ix-step r i) (burst-aft τ r (suc i) k h x)
  burst-aft τ r i (stall k)  h at-skip     = ≼-refl {r ▸ ix i}
  burst-aft τ r i (stall k)  {y} h (on-skip x) = ≺≼ (r ▸ ix i) (r ▸ ix (suc i)) y (ix-step r i) (burst-aft τ r (suc i) (Frame∞.force k) h x)
  burst-aft τ r i (close k)  h at-skip     = ≼-refl {r ▸ ix i}
  burst-aft τ r i (close k)  {y} h (on-skip x) = ≺≼ (r ▸ ix i) (r ▸ last) y (ix-last r i) (frames-aft τ (r ▸ last) (From∞.force k) (lt-last r h) x)

mutual
  frames-be : ∀ {A t} τ e (m : From A t) {y v c} → tickᵖ e < τ + t → InE (frames τ e m) y v → InE (frames τ e m) c end → y ≼ c
  frames-be τ e done         h at-end at-end = ≼-refl {e}
  frames-be τ e quiet        h () _
  frames-be τ e (at t′ le b) h x      x′     = burst-be τ (fired (τ + t′) e) 0 b (+-monoʳ-< τ (n<1+n t′)) x x′

  burst-be : ∀ {A t} τ r i (b : Frame A t) {y v c} → tickᴿ r < τ + suc t → InE (burst τ r i b) y v → InE (burst τ r i b) c end → y ≼ c
  burst-be τ r i (emit _ k) {c = c} h at-out (on-out x′) = ≺≼ (r ▸ ix i) (r ▸ ix (suc i)) c (ix-step r i) (burst-aft τ r (suc i) k h x′)
  burst-be τ r i (emit _ k) h (on-out x)  (on-out x′)  = burst-be τ r (suc i) k h x x′
  burst-be τ r i (stall k)  {c = c} h at-skip (on-skip x′) = ≺≼ (r ▸ ix i) (r ▸ ix (suc i)) c (ix-step r i) (burst-aft τ r (suc i) (Frame∞.force k) h x′)
  burst-be τ r i (stall k)  h (on-skip x) (on-skip x′) = burst-be τ r (suc i) (Frame∞.force k) h x x′
  burst-be τ r i (close k)  {c = c} h at-skip (on-skip x′) = ≺≼ (r ▸ ix i) (r ▸ last) c (ix-last r i) (frames-aft τ (r ▸ last) (From∞.force k) (lt-last r h) x′)
  burst-be τ r i (close k)  h (on-skip x) (on-skip x′) = frames-be τ (r ▸ last) (From∞.force k) (lt-last r h) x x′

start-be : ∀ {A} s (m : From A 0) {y v c} → InE (start s m) y v → InE (start s m) c end → y ≼ c
start-be s done              at-end at-end = ≼-refl {s ⊕ [ last ]}
start-be s quiet             () _
start-be s (at zero _ b)     x      x′     = burst-be (tickᵖ s) (nested s) 0 b (m<m+n (tickᵖ s) (s≤s z≤n)) x x′
start-be s (at (suc t) le b) x      x′     = frames-be {t = 1} (tickᵖ s) (s ⊕ [ last ]) (at (suc t) (s≤s z≤n) b) (last-tick s) x x′

------------------------------------------------------------------------
-- What a render shows

data VRow {A : Set} (a : A) (s : Pos) : Pos → IE A → Set where
  v-begin : VRow a s (s ⊕ (ix 0 ∷ ix 1 ∷ ix 0 ∷ [])) (instEmit (mark begin) s)
  v-value : VRow a s (s ⊕ (ix 0 ∷ ix 1 ∷ ix 1 ∷ [])) (instEmit (value a) s)
  v-over  : VRow a s (s ⊕ (ix 0 ∷ ix 1 ∷ ix 2 ∷ [])) (instEmit (mark over) s)

ROut : ∀ {A} → Bool × Tag A → Pos → Pos → IE A → Set
ROut (false , val a) s y v = y ≡ s ⊕ [ ix 0 ] × v ≡ instEmit (value a) root
ROut (true  , val a) s y v = VRow a s y v
ROut (true  , cdone) s y v = y ≡ s ⊕ [ ix 0 ] × v ≡ instEmit (mark begin) s
ROut _               s y v = ⊥

IsVal : ∀ {A} → Tag A → Set
IsVal (val _) = ⊤
IsVal _       = ⊥

T∨l : ∀ x y → T x → T (x ∨ y)
T∨l true _ _ = tt

T∨r : ∀ x → T (x ∨ true)
T∨r true  = tt
T∨r false = tt

tk-tl : ∀ {A} {v : Tag A} → Ticks (out v) → Tickless (out v) → ⊥
tk-tl {v = tick} _ ()

------------------------------------------------------------------------
-- The elaborated cold, row by row

module Shape {A : Set} (Fc Fm : Bool → Den (Tag A)) (R : Bool × Tag A → Den (IE A))
  (fc-true  : ∀ s {y e} → enter (Fc true) s y e → CF.Place CF.One s y × Tickless e)
  (fc-false : ∀ s {y e} → enter (Fc false) s y e → (y ≡ s ⊕ [ ix 0 ] ⊎ y ≡ s ⊕ [ last ]) × Tickless e)
  (fm-true  : ∀ s {y e} → enter (Fm true) s y e → enter (Op.flatMap (mergeᶠ (just 1)) Fc (Op.of (true ∷ false ∷ []))) s y e)
  (fm-false : ∀ s {y e} → enter (Fm false) s y e → s ⊑ y × Ticks e)
  (r-in     : ∀ x s {y e} → enter (R x) s y e → Rendered s y)
  (r-begin  : ∀ x s {y n} → enter (R x) s y (out (instEmit (mark begin) n)) → CF.Late x)
  (lf-row   : ∀ s {y e} → enter (Fc true) s y e → Leaf s y e)
  (lf-val   : ∀ s {y v} → enter (Fc true) s y (out v) → IsVal v)
  (lf-uniq  : ∀ s {c c′} → enter (Fc true) s c end → enter (Fc true) s c′ end → c ≡ c′)
  (lf-be    : ∀ s {y e c} → enter (Fc true) s y e → enter (Fc true) s c end → y ≼ c)
  (fc-out   : ∀ s {y v} → enter (Fc false) s y (out v) → y ≡ s ⊕ [ ix 0 ] × v ≡ cdone)
  (fc-end   : ∀ s {y} → enter (Fc false) s y end → y ≡ s ⊕ [ last ])
  (fm-tick  : ∀ s → enter (Fm false) s (s ⊕ [ ix 0 ]) (out tick))
  (r-out    : ∀ x s {y v} → enter (R x) s y (out v) → ROut x s y v) where

  open Core Fc Fm R fc-true fc-false fm-true fm-false r-in r-begin

  -- The cold's stream, run by the concat at `s`.
  L1 : Pos → EmissionSet (Tag A)
  L1 s = enter (Fc true) (S₁ s)

  module Cat′ (s : Pos) where
    open Bounded 1 Fc (O s) using (Lane; Starts; room; freed; queued; Kth; Sched; JoinT; Done)
    open Pair s using (nth₀; nth₁)
    open Nths (O s) using (nth-val; nth-inj)
    open Cat s using (end-t; first-end)

    kth0 : ∀ {P : Pos → Set} → Kth P (Sched 1) 0 → Σ Pos λ c → L1 s c end × P c
    kth0 (inj₁ (c , (q , a , s′ , nq , st , (r , _)) , pc)) = c , end-t (o-row s (nth-val nq)) nq st r , pc
    kth0 (inj₂ ())

    l0-go : ∀ {s′ k e} → Starts 0 (s ⊕ [ ix 0 ]) [] s′ → enter (Fc true) s′ k e → L1 s k e
    l0-go (room _)            r = r
    l0-go (freed () _)        r
    l0-go (queued () _ _ _ _) r

    -- The first lane runs the cold.
    lane₀ : ∀ {k e} → Lane (s ⊕ [ ix 0 ]) true k e → L1 s k e
    lane₀ (i , s′ , (nd , st) , (r , _)) with nth-inj nd nth₀
    ... | refl = l0-go st r

    -- The second, freed by the cold's end before it, or queued at it.
    data Ran₁ (k : Pos) (e : Ev (Tag A)) : Set where
      freed₁ : (Σ Pos λ c → L1 s c end × c ≺ (s ⊕ [ ix 1 ])) → enter (Fc false) (S₂ s) k e → Ran₁ k e
      queue₁ : ∀ {c} → L1 s c end → enter (Fc false) (c ⊕ [ ix 1 ]) k e → Ran₁ k e

    l1-go : ∀ {s′ k e} → Starts 1 (s ⊕ [ ix 1 ]) (Sched 1) s′ → enter (Fc false) s′ k e → Ran₁ k e
    l1-go (room (s≤s ()))     r
    l1-go (freed _ kt)        r = freed₁ (kth0 kt) r
    l1-go (queued _ _ kc _ _) r = queue₁ (first-end kc) r

    lane₁ : ∀ {k e} → Lane (s ⊕ [ ix 1 ]) false k e → Ran₁ k e
    lane₁ (i , s′ , (nd , st) , (r , _)) with nth-inj nd nth₁
    ... | refl = l1-go st r

    data Row (k : Pos) (e : Ev (Tag A)) : Set where
      on₀ : L1 s k e → Row k e
      on₁ : Ran₁ k e → Row k e

    lanes : ∀ {q a k e} → O s q (out a) → Lane q a k e → Row k e
    lanes x l with o-row s x
    ... | inj₁ (refl , refl) = on₀ (lane₀ l)
    ... | inj₂ (refl , refl) = on₁ (lane₁ l)

    cat-out : ∀ {y v} → JoinT y (out v) → Row y (out v)
    cat-out (Joining.lane x _ l _ _) = lanes x l
    cat-out (Joining.run () _)

    -- The cold's end at a later tick hands its place on, so the concat
    -- has not ended there.
    handed : ∀ {c c₂} → L1 s c end → (s ⊕ [ ix 1 ]) ≺ c → Ran₁ c₂ end → c₂ ≼ c → ⊥
    handed {c} rc lt (freed₁ (c′ , rc′ , lt′) r) le with lf-uniq (S₁ s) rc rc′
    ... | refl = ≺-absurd {c} {s ⊕ [ ix 1 ]} lt′ lt
    handed {c} rc lt (queue₁ rc′ r) le with lf-uniq (S₁ s) rc rc′ | fc-end _ r
    ... | refl | refl = le (subst (c ≺_) (sym (⊕-assoc c [ ix 1 ] [ last ])) (≺-ext c {ix 1} (last ∷ [])))

    hands : ∀ {c} → L1 s c end → Fresh s (instant c) → Done c → ⊥
    hands {c} rc f (_ , all) with all (nth-val nth₁) (1 , false , nth₁) (fresh-past {y = c} ([ ix 1 ] , refl) f) (λ ())
    ... | c₂ , l₂ , le = handed rc (fresh-past {y = c} ([ ix 1 ] , refl) f) (lane₁ l₂) le

    -- Where the concat ends: under it, or a lane past the cold's end.
    CatEnd : Pos → Set
    CatEnd c = s ⊑ c ⊎ Σ Pos λ c′ → L1 s c′ end × Fired {Tag A} (S₁ s) c′ end × c ≡ (c′ ⊕ [ ix 1 ]) ⊕ [ last ]

    up₁ : ∀ {k} → S₁ s ⊑ k → s ⊑ k
    up₁ u = ⊑-trans (⊑₂ s (ix 0) (ix 1)) u

    up₂ : ∀ {k} → S₂ s ⊑ k → s ⊑ k
    up₂ u = ⊑-trans (⊑₂ s (ix 1) (ix 1)) u

    lend-end : ∀ {c} → Row c end → Done c → CatEnd c
    lend-end (on₀ r) dn with lf-row (S₁ s) r
    ... | inj₁ u         = inj₁ (up₁ u)
    ... | inj₂ (f-end f) = ⊥-elim (hands r (fresh-⊑ (⊑₂ s (ix 0) (ix 1)) f) dn)
    lend-end (on₁ (freed₁ _ r)) dn with fc-end (S₂ s) r
    ... | refl = inj₁ (up₂ ([ last ] , refl))
    lend-end (on₁ (queue₁ {c′} rc r)) dn with fc-end _ r | lf-row (S₁ s) rc
    ... | refl | inj₁ u         = inj₁ (up₁ (⊑-trans u ((ix 1 ∷ last ∷ []) , ⊕-assoc c′ [ ix 1 ] [ last ])))
    ... | refl | inj₂ (f-end f) = inj₂ (_ , rc , f-end f , refl)

    cat-end : ∀ {c} → JoinT c end → CatEnd c
    cat-end (Joining.oend x _)          = inj₁ (o-under s x)
    cat-end (Joining.lend x _ l _ _ dn) = lend-end (lanes x l) dn
    cat-end (Joining.rend () _ _)

    -- No end of the concat precedes a row of the cold at a later tick.
    past-end : ∀ {p y e c x} → L1 s y e → Fresh p (instant y) → p ⊑ x → (Σ Pos λ c″ → L1 s c″ end × c″ ≼ c) → c ≼ x → ⊥
    past-end {p} {y} {e} {c} {x} ry f px (c″ , rc , le) cx =
      lf-be (S₁ s) ry rc (≼-≺-≺ {c″} {c} {y} le (≼-≺-≺ {c} {x} {y} cx (fresh-past {p} {x} {y} px f)))

    l0-ended : ∀ {c} → Done c → (s ⊕ [ ix 0 ]) ≺ c → Σ Pos λ c″ → L1 s c″ end × c″ ≼ c
    l0-ended (_ , all) lt with all (nth-val nth₀) (0 , true , nth₀) lt (λ ())
    ... | c″ , l , le = c″ , lane₀ l , le

    early-lane : ∀ {p y e c x} → L1 s y e → Fresh p (instant y) → p ⊑ x → Row c end → Done c → c ≼ x → ⊥
    early-lane {c = c} ry f px (on₀ rc) dn cx = past-end ry f px (c , rc , ≼-refl {c}) cx
    early-lane ry f px (on₁ (freed₁ _ r)) dn cx with fc-end (S₂ s) r
    ... | refl = past-end ry f px (l0-ended dn (sep s (⊑-refl (s ⊕ [ ix 0 ])) ((ix 1 ∷ last ∷ []) , ⊕-assoc (s ⊕ [ ix 1 ]) [ ix 1 ] [ last ]))) cx
    early-lane ry f px (on₁ (queue₁ {c′} rc r)) dn cx with fc-end _ r
    ... | refl = past-end ry f px (c′ , rc , ≺→≼ {c′} {(c′ ⊕ [ ix 1 ]) ⊕ [ last ]} (subst (c′ ≺_) (sym (⊕-assoc c′ [ ix 1 ] [ last ])) (≺-ext c′ {ix 1} (last ∷ [])))) cx

    early-cat : ∀ {p y e c x} → L1 s y e → Fresh p (instant y) → p ⊑ x → JoinT c end → c ≼ x → ⊥
    early-cat ry f px (Joining.oend o dn) cx with of-end s 0 (true ∷ false ∷ []) (proj₁ o)
    ... | refl = past-end ry f px (l0-ended dn (Equivalence.from T-≡ (<ᵖ-part s [] [] refl))) cx
    early-cat ry f px (Joining.lend o _ l _ _ dn) cx = early-lane ry f px (lanes o l) dn cx
    early-cat ry f px (Joining.rend () _ _) cx

  module Mgs (p : Pos) where
    open Merge Fm (O p) using (JoinT; Done)
    open Pair p using (nth₀; nth₁)
    open Nths (O p) using (nth-val)
    open Cat′ (S₁ p) using (CatEnd; cat-end; cat-out; early-cat; Row; on₀; on₁; freed₁; queue₁)

    pS : p ⊑ S₁ (S₁ p)
    pS = ⊑-trans (⊑₂ p (ix 0) (ix 1)) (⊑₂ (S₁ p) (ix 0) (ix 1))

    not-under : ∀ {y} → p ⊑ y → Fresh p (instant y) → ⊥
    not-under u f = fresh-self {p} (subst (Fresh p) (instant-⊑ u) f)

    -- Where the merge ends: under it, or past the cold's end.
    MgEnd : Pos → Set
    MgEnd c = p ⊑ c ⊎ Σ Pos λ c′ → L1 (S₁ p) c′ end × Fired {Tag A} (S₁ (S₁ p)) c′ end × c ≡ (c′ ⊕ [ ix 1 ]) ⊕ [ last ]

    cat-up : ∀ {c} → CatEnd c → MgEnd c
    cat-up (inj₁ u) = inj₁ (⊑-trans (⊑₂ p (ix 0) (ix 1)) u)
    cat-up (inj₂ z) = inj₂ z

    mg-lend : ∀ {q a c} → (q ≡ p ⊕ [ ix 0 ] × a ≡ true) ⊎ (q ≡ p ⊕ [ ix 1 ] × a ≡ false) → enter (Fm a) (q ⊕ [ ix 1 ]) c end → MgEnd c
    mg-lend (inj₁ (refl , refl)) l = cat-up (cat-end (proj₁ (fm-true _ l)))
    mg-lend (inj₂ (refl , refl)) l = inj₁ (⊑-trans (⊑₂ p (ix 1) (ix 1)) (proj₁ (fm-false _ l)))

    mg-end : ∀ {c} → JoinT c end → MgEnd c
    mg-end (Joining.oend x _)                = inj₁ (o-under p x)
    mg-end (Joining.lend x _ (l , _) _ _ _)  = mg-lend (o-row p x) l
    mg-end (Joining.rend () _ _)

    -- A value of the merge: the concat's, or a tick under it.
    mg-lrow : ∀ {q a y v} → (q ≡ p ⊕ [ ix 0 ] × a ≡ true) ⊎ (q ≡ p ⊕ [ ix 1 ] × a ≡ false) → enter (Fm a) (q ⊕ [ ix 1 ]) y (out v)
            → Bounded.JoinT 1 Fc (O (S₁ p)) y (out v) ⊎ (Ticks (out v) × p ⊑ y)
    mg-lrow (inj₁ (refl , refl)) l = inj₁ (proj₁ (fm-true _ l))
    mg-lrow (inj₂ (refl , refl)) l with fm-false _ l
    ... | u , t = inj₂ (t , ⊑-trans (⊑₂ p (ix 1) (ix 1)) u)

    mg-row : ∀ {y v} → JoinT y (out v) → Bounded.JoinT 1 Fc (O (S₁ p)) y (out v) ⊎ (Ticks (out v) × p ⊑ y)
    mg-row (Joining.lane x _ (l , _) _ _) = mg-lrow (o-row p x) l
    mg-row (Joining.run () _)

    -- An end under the subscription leaves no row of the cold at a later
    -- tick behind it.
    via-cat : ∀ {y e c} → L1 (S₁ p) y e → Fresh p (instant y) → p ⊑ c → Done c → (p ⊕ [ ix 0 ]) ≺ c → ⊥
    via-cat ry f pc (_ , all) lt with all (nth-val nth₀) tt lt (λ ())
    ... | c₁ , (l₁ , _) , le = early-cat ry f pc (proj₁ (fm-true _ l₁)) le

    early-ml : ∀ {y e q a c} → L1 (S₁ p) y e → Fresh p (instant y) → p ⊑ c
             → (q ≡ p ⊕ [ ix 0 ] × a ≡ true) ⊎ (q ≡ p ⊕ [ ix 1 ] × a ≡ false) → enter (Fm a) (q ⊕ [ ix 1 ]) c end → Done c → ⊥
    early-ml {c = c} ry f pc (inj₁ (refl , refl)) l dn = early-cat ry f pc (proj₁ (fm-true _ l)) (≼-refl {c})
    early-ml ry f pc (inj₂ (refl , refl)) l dn =
      via-cat ry f pc dn (sep p (⊑-refl (p ⊕ [ ix 0 ])) (⊑-trans ([ ix 1 ] , refl) (proj₁ (fm-false _ l))))

    early-mg : ∀ {y e c} → L1 (S₁ p) y e → Fresh p (instant y) → JoinT c end → p ⊑ c → ⊥
    early-mg ry f (Joining.oend o dn) pc with of-end p 0 (true ∷ false ∷ []) (proj₁ o)
    ... | refl = via-cat ry f pc dn (Equivalence.from T-≡ (<ᵖ-part p [] [] refl))
    early-mg ry f (Joining.lend x _ (l , _) _ _ dn) pc = early-ml ry f pc (o-row p x) l dn
    early-mg ry f (Joining.rend () _ _) pc

    ------------------------------------------------------------------------
    -- The scan

    T₀ : Pos
    T₀ = ((p ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]

    T₀-under : p ⊑ T₀
    T₀-under = (ix 1 ∷ ix 1 ∷ ix 0 ∷ []) , assoc³ p (ix 1) (ix 1) (ix 0)

    -- The tick, shown wherever a later row is.
    tick-at : ∀ {q v} → Mg p q (out v) → T₀ ≺ q → Mg p T₀ (out tick)
    tick-at {q} (_ , (ks , h)) lt =
      Joining.lane (nth-val nth₁) tt (fm-tick ((p ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) , ≺-ext ((p ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) {ix 0} []) (λ ()) tt
      , (ks , λ {k} r kl _ → h r (≺-trans {k} {T₀} {q} kl lt) tt)

    tick-under : ∀ {k} → Mg p k (out tick) → p ⊑ k
    tick-under kx with mg-out p (proj₁ kx)
    ... | inj₁ (_ , u)  = ⊑-trans ([ ix 1 ] , refl) u
    ... | inj₂ (() , _)

    acc-self : ∀ {q b} → Acc p q b → Ticks (out (proj₂ b)) → T (proj₁ b)
    acc-self (Scan.acc₀ {a = tick} _ _)            _  = tt
    acc-self (Scan.acc₀ {a = val _} _ _)           ()
    acc-self (Scan.acc₀ {a = cdone} _ _)           ()
    acc-self (Scan.acc {b = b} {a′ = tick} _ _ _ _) _ = T∨r (proj₁ b)
    acc-self (Scan.acc {a′ = val _} _ _ _ _)       ()
    acc-self (Scan.acc {a′ = cdone} _ _ _ _)       ()

    -- Past a tick, the scan reads late.
    late-past : ∀ {q b k} → Acc p q b → Mg p k (out tick) → k ≺ q → T (proj₁ b)
    late-past (Scan.acc₀ _ first) kx lt = ⊥-elim (first kx lt)
    late-past {k = k} (Scan.acc {q = q′} {b = b} r x lt′ nx) kx lt with mg-out p (proj₁ (acc-tag r))
    ... | inj₁ (tk , _)      = T∨l (proj₁ b) _ (acc-self r tk)
    ... | inj₂ (_ , inj₂ f)  = T∨l (proj₁ b) _ (late-past r kx (fresh-past {p} {k} {q′} (tick-under kx) f))
    ... | inj₂ (_ , inj₁ u₀) with mg-out p (proj₁ kx)
    ...   | inj₁ (_ , u₁) = ⊥-elim (nx kx (sep p {q′} {k} u₀ u₁) lt)
    ...   | inj₂ (() , _)

    -- A value read before the tick lies under the concat.
    read-early : ∀ {q₀ x₀} → Acc p q₀ x₀ → ¬ T (proj₁ x₀) → Tickless (out (proj₂ x₀)) → (p ⊕ [ ix 0 ]) ⊑ q₀
    read-early {q₀} ac nl tl with mg-out p (proj₁ (acc-tag ac))
    ... | inj₁ (tk , _)     = ⊥-elim (tk-tl tk tl)
    ... | inj₂ (_ , inj₁ u) = u
    ... | inj₂ (_ , inj₂ f) = let lt = fresh-past {p} {T₀} {q₀} T₀-under f in ⊥-elim (nl (late-past ac (tick-at (acc-tag ac) lt) lt))

    -- A value read past it: where the cold's step fires it.
    ValAt : Pos → A → Set
    ValAt q₀ a = Σ ℕ λ T → Σ Pos λ e → Σ ℕ λ i → q₀ ≡ (cascade T e (ix i) ∙ []) × L1 (S₁ p) q₀ (out (val a)) × Fresh p (instant q₀)

    val-leaf : ∀ {q₀ a} → Fresh p (instant q₀) → L1 (S₁ p) q₀ (out (val a)) → Leaf (S₁ (S₁ p)) q₀ (out (val a)) → ValAt q₀ a
    val-leaf f r (inj₁ u)          = ⊥-elim (not-under (⊑-trans pS u) f)
    val-leaf f r (inj₂ (f-out _)) = _ , _ , _ , refl , r , f

    val-cat : ∀ {q₀ a} → Fresh p (instant q₀) → Row q₀ (out (val a)) → ValAt q₀ a
    val-cat f (on₀ r)             = val-leaf f r (lf-row _ r)
    val-cat f (on₁ (freed₁ _ r)) with () ← proj₂ (fc-out _ r)
    val-cat f (on₁ (queue₁ _ r)) with () ← proj₂ (fc-out _ r)

    val-mg : ∀ {q₀ a} → Fresh p (instant q₀) → Bounded.JoinT 1 Fc (O (S₁ p)) q₀ (out (val a)) ⊎ (Ticks (out (val a)) × p ⊑ q₀) → ValAt q₀ a
    val-mg f (inj₁ cr)      = val-cat f (cat-out cr)
    val-mg f (inj₂ (() , _))

    val-row : ∀ {q₀ a} → Acc p q₀ (true , val a) → ValAt q₀ a
    val-row ac = val-mg (read-late p ac tt) (mg-row (proj₁ (acc-tag ac)))

    -- A completion read past it: where the cold's end hands its lane on.
    CdAt : Pos → Set
    CdAt q₀ = Σ Pos λ c′ → L1 (S₁ p) c′ end × Fired {Tag A} (S₁ (S₁ p)) c′ end × q₀ ≡ (c′ ⊕ [ ix 1 ]) ⊕ [ ix 0 ]

    cd-cat : ∀ {q₀} → Fresh p (instant q₀) → Row q₀ (out cdone) → CdAt q₀
    cd-cat f (on₀ r) with () ← lf-val _ r
    cd-cat f (on₁ (freed₁ _ r)) with fc-out _ r
    ... | refl , _ = ⊥-elim (not-under (⊑-trans (⊑₂ p (ix 0) (ix 1)) (⊑-trans (⊑₂ (S₁ p) (ix 1) (ix 1)) ([ ix 0 ] , refl))) f)
    cd-cat f (on₁ (queue₁ {c′} rc r)) with fc-out _ r | lf-row _ rc
    ... | refl , _ | inj₁ u          = ⊥-elim (not-under (⊑-trans pS (⊑-trans u ((ix 1 ∷ ix 0 ∷ []) , ⊕-assoc c′ [ ix 1 ] [ ix 0 ]))) f)
    ... | refl , _ | inj₂ (f-end f′) = _ , rc , f-end f′ , refl

    cd-mg : ∀ {q₀} → Fresh p (instant q₀) → Bounded.JoinT 1 Fc (O (S₁ p)) q₀ (out cdone) ⊎ (Ticks (out (cdone {A})) × p ⊑ q₀) → CdAt q₀
    cd-mg f (inj₁ cr)      = cd-cat f (cat-out cr)
    cd-mg f (inj₂ (() , _))

    cd-row : ∀ {q₀} → Acc p q₀ (true , cdone) → CdAt q₀
    cd-row ac = cd-mg (read-late p ac tt) (mg-row (proj₁ (acc-tag ac)))

    ------------------------------------------------------------------------
    -- The renders

    now-v : ∀ {y} {a : A} → p ⊑ y → ColdRow p y (out (instEmit (value a) root))
    now-v (zs , refl) = now-value zs

    now-e : ∀ {y} → p ⊑ y → ColdRow {A} p y end
    now-e (zs , refl) = now-end zs

    lo-v : ∀ {q₀ a k v} → ValAt q₀ a → VRow a (q₀ ⊕ [ ix 1 ]) k v → ColdRow p k (out v)
    lo-v (_ , _ , _ , refl , _ , _) v-begin = step-begin
    lo-v (_ , _ , _ , refl , _ , _) v-value = step-value
    lo-v (_ , _ , _ , refl , _ , _) v-over  = step-over

    lo-c : ∀ {q₀} → CdAt q₀ → ColdRow {A} p ((q₀ ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) (out (instEmit (mark begin) (q₀ ⊕ [ ix 1 ])))
    lo-c (_ , _ , f-end _ , refl) = step-begin

    lo : ∀ x₀ {q₀ k v} → Acc p q₀ x₀ → ROut x₀ (q₀ ⊕ [ ix 1 ]) k v → ColdRow p k (out v)
    lo (false , val a) {q₀} ac (refl , refl) =
      now-v (⊑-trans (⊑-trans ([ ix 0 ] , refl) (read-early ac (λ ()) tt)) ((ix 1 ∷ ix 0 ∷ []) , ⊕-assoc q₀ [ ix 1 ] [ ix 0 ]))
    lo (true , val a)  ac vr            = lo-v (val-row ac) vr
    lo (true , cdone)  ac (refl , refl) = lo-c (cd-row ac)
    lo (false , cdone) ac ()
    lo (false , tick)  ac ()
    lo (true , tick)   ac ()

    -- Where the whole ends: its outer's end.
    over-end : ∀ {c} → Merge.Done R (Sc p) c → Σ Pos λ c₀ → JoinT c₀ end × c₀ ≼ c
    over-end ((c₀ , (Scan.send x , _) , le) , _) = c₀ , proj₁ x , le

    step-before : ∀ {T e i T′ e′ a} → L1 (S₁ p) (cascade T e (ix i) ∙ []) (out (val a)) → L1 (S₁ p) (cascade T′ e′ last ∙ []) end
                → (cascade T e (ix i) ∙ []) ≺ (cascade T′ e′ last ∙ [])
    step-before {T} {e} {i} {T′} {e′} r rc with ≼-or-≻ (cascade T′ e′ last ∙ []) (cascade T e (ix i) ∙ [])
    ... | inj₂ lt = lt
    ... | inj₁ le with ≼-antisym {cascade T e (ix i) ∙ []} {cascade T′ e′ last ∙ []} (lf-be (S₁ (S₁ p)) r rc) le
    ...   | ()

    val-end : ∀ {q₀ a w} → ValAt q₀ a → (Σ Pos λ c₀ → JoinT c₀ end × c₀ ≼ ((q₀ ⊕ [ ix 1 ]) ⊕ w)) → ⊥
    val-end {w = w} (T , e , i , refl , r₁ , f) (c₀ , x , le) = ve (mg-end x) le
      where
        ve : MgEnd c₀ → c₀ ≼ (((cascade T e (ix i) ∙ []) ⊕ [ ix 1 ]) ⊕ w) → ⊥
        ve (inj₁ u)                           _  = early-mg r₁ f x u
        ve (inj₂ (c′ , rc , f-end _ , refl)) le′ =
          le′ (instant-≺ (((cascade T e (ix i) ∙ []) ⊕ [ ix 1 ]) ⊕ w) ((c′ ⊕ [ ix 1 ]) ⊕ [ last ])
                 (≺-instant (cascade T e (ix i) ∙ []) c′ (step-before r₁ rc) (λ ())))

    cd-end : ∀ {q₀ w} → CdAt q₀ → (Σ Pos λ c₀ → JoinT c₀ end × c₀ ≼ ((q₀ ⊕ [ ix 1 ]) ⊕ w)) → ⊥
    cd-end {w = w} (c′ , rc , f-end f , refl) (c₀ , x , le) = ce (mg-end x) le
      where
        ce : MgEnd c₀ → c₀ ≼ ((((c′ ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ w) → ⊥
        ce (inj₁ u)                            _   = early-mg rc (fresh-⊑ pS f) x u
        ce (inj₂ (c″ , rc″ , f-end _ , refl)) le′ with lf-uniq _ rc rc″
        ... | refl = le′ (Equivalence.from T-≡ (<ᵖ-part (c′ ⊕ [ ix 1 ]) {ix 0} {last} (ix 1 ∷ w) [] refl))

    tick-r : ∀ {q₀ b w} → Acc p q₀ (b , tick) → p ⊑ ((q₀ ⊕ [ ix 1 ]) ⊕ w)
    tick-r {q₀} {w = w} ac with mg-out p (proj₁ (acc-tag ac))
    ... | inj₁ (_ , u)  = ⊑-trans (⊑-trans ([ ix 1 ] , refl) u) ((ix 1 ∷ w) , ⊕-assoc q₀ [ ix 1 ] w)
    ... | inj₂ (() , _)

    early-r : ∀ {q₀ w} → (p ⊕ [ ix 0 ]) ⊑ q₀ → p ⊑ ((q₀ ⊕ [ ix 1 ]) ⊕ w)
    early-r {q₀} {w} u = ⊑-trans (⊑-trans ([ ix 0 ] , refl) u) ((ix 1 ∷ w) , ⊕-assoc q₀ [ ix 1 ] w)

    le-x : ∀ x₀ {q₀ w} → Acc p q₀ x₀ → Merge.Done R (Sc p) ((q₀ ⊕ [ ix 1 ]) ⊕ w) → ColdRow {A} p ((q₀ ⊕ [ ix 1 ]) ⊕ w) end
    le-x (false , val a) {q₀} {w} ac dn = now-e (early-r {q₀} {w} (read-early ac (λ ()) tt))
    le-x (false , cdone) {q₀} {w} ac dn = now-e (early-r {q₀} {w} (read-early ac (λ ()) tt))
    le-x (false , tick)  {q₀} {w} ac dn = now-e (tick-r {q₀} {false} {w} ac)
    le-x (true , tick)   {q₀} {w} ac dn = now-e (tick-r {q₀} {true} {w} ac)
    le-x (true , val a)  ac dn = ⊥-elim (val-end (val-row ac) (over-end dn))
    le-x (true , cdone)  ac dn = ⊥-elim (cd-end (cd-row ac) (over-end dn))

    lane-end : ∀ {q₀ x₀ c} → Acc p q₀ x₀ → enter (R x₀) (q₀ ⊕ [ ix 1 ]) c end → Merge.Done R (Sc p) c → ColdRow {A} p c end
    lane-end {q₀} {x₀} ac l dn with r-in x₀ (q₀ ⊕ [ ix 1 ]) l
    ... | w , _ , refl = le-x x₀ {q₀} {w} ac dn

    top-end : ∀ {c} → MgEnd c → ColdRow {A} p c end
    top-end (inj₁ u)                        = now-e u
    top-end (inj₂ (_ , _ , f-end _ , refl)) = step-end

    -- EACH ROW SHOWN.
    top-row : ∀ {y e} → Merge.JoinT R (Sc p) y e → Visible e → ColdRow p y e
    top-row (Joining.lane {e = out v} (Scan.sval ac , _) _ (l , _) _ _) _ = lo _ ac (r-out _ _ l)
    top-row (Joining.lane {e = skip} _ _ _ _ _)  ()
    top-row (Joining.lane {e = pin _} _ _ _ _ _) ()
    top-row (Joining.lane {e = end} _ _ _ _ ())  _
    top-row (Joining.oend (Scan.send x , _) _) _ = top-end (mg-end (proj₁ x))
    top-row (Joining.lend (Scan.sval ac , _) _ (l , _) _ _ dn) _ = lane-end ac l dn
    top-row (Joining.val _)              ()
    top-row (Joining.step _)             ()
    top-row (Joining.opin _)             ()
    top-row (Joining.opass _ _)          ()
    top-row (Joining.lpass _ _ _ _ _ _)  ()
    top-row (Joining.hand _ _ _ _ ())    _
    top-row (Joining.left _ _ _ _ _)     ()
    top-row (Joining.run () _)           _
    top-row (Joining.rend () _ _)        _
    top-row (Joining.rpass () _ _)       _
    top-row (Joining.rhand () _)         _

------------------------------------------------------------------------
-- The elaborated cold's parts

lf-o : ∀ {X Y : Set} {s y} {a : X} {b : Y} → Leaf s y (out a) → Leaf s y (out b)
lf-o (inj₁ u)         = inj₁ u
lf-o (inj₂ (f-out f)) = inj₂ (f-out f)

lf-s : ∀ {X Y : Set} {s y} → Leaf {X} s y skip → Leaf {Y} s y skip
lf-s (inj₁ u)          = inj₁ u
lf-s (inj₂ (f-skip f)) = inj₂ (f-skip f)

lf-e : ∀ {X Y : Set} {s y} → Leaf {X} s y end → Leaf {Y} s y end
lf-e (inj₁ u)         = inj₁ u
lf-e (inj₂ (f-end f)) = inj₂ (f-end f)

lf-map : ∀ {A} (c : Timeline A) s {y e} → enter (Op.map val (Op.cold c)) s y e → Leaf s y e
lf-map c s (map-out (x , _) , _)  = lf-o (start-lf s (timelineAt c s) x)
lf-map c s (map-skip (x , _) , _) = lf-s (start-lf s (timelineAt c s) x)
lf-map c s (map-pin (x , _) , _)  = ⊥-elim (ine-pin x)
lf-map c s (map-end (x , _) , _)  = lf-e (start-lf s (timelineAt c s) x)

be-map : ∀ {A} (c : Timeline A) s {y e c′} → enter (Op.map val (Op.cold c)) s y e → enter (Op.map val (Op.cold c)) s c′ end → y ≼ c′
be-map c s (map-out (x , _) , _)  (map-end (x′ , _) , _) = start-be s (timelineAt c s) x x′
be-map c s (map-skip (x , _) , _) (map-end (x′ , _) , _) = start-be s (timelineAt c s) x x′
be-map c s (map-pin (x , _) , _)  _                       = ⊥-elim (ine-pin x)
be-map c s (map-end (x , _) , _)  (map-end (x′ , _) , _) = start-be s (timelineAt c s) x x′

three-out : ∀ {X : Set} s (a : X) {y v} → InE (ofᴱ ((s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) 0 (instEmit (mark begin) s ∷ instEmit (value a) s ∷ instEmit (mark over) s ∷ [])) y (out v)
          → VRow a s y v
three-out s a at-out                   = subst (λ y → VRow a s y (instEmit (mark begin) s)) (sym (assoc³ s (ix 0) (ix 1) (ix 0))) v-begin
three-out s a (on-out at-out)          = subst (λ y → VRow a s y (instEmit (value a) s)) (sym (assoc³ s (ix 0) (ix 1) (ix 1))) v-value
three-out s a (on-out (on-out at-out)) = subst (λ y → VRow a s y (instEmit (mark over) s)) (sym (assoc³ s (ix 0) (ix 1) (ix 2))) v-over
three-out s a (on-out (on-out (on-out ())))

rv-out : ∀ {X : Set} (a : X) s {y v}
       → enter (Op.flatMap (mergeᶠ nothing) (λ n → Op.of (instEmit (mark begin) n ∷ instEmit (value a) n ∷ instEmit (mark over) n ∷ [])) (Op.cold Mint)) s y (out v)
       → VRow a s y v
rv-out a s (Joining.lane (at-out , _) _ ((l , _) , _) _ _ , _) = three-out s a l
rv-out a s (Joining.lane (on-out (on-skip ()) , _) _ _ _ _ , _)
rv-out a s (Joining.run () _ , _)

cd-out : ∀ {X : Set} s {y v} → enter (Op.map (λ n → instEmit {A = X} (mark begin) n) (Op.cold Mint)) s y (out v)
       → y ≡ s ⊕ [ ix 0 ] × v ≡ instEmit (mark begin) s
cd-out s (map-out (at-out , _) , _)              = refl , refl
cd-out s (map-out (on-out (on-skip ()) , _) , _)

module _ {Δ : List Set} (env : DenEnv Δ) where

  lf-rows : ∀ m {A} (c : Timeline A) s {y e} → enter (ev m (map val (cold c)) env) s y e → Leaf s y e
  lf-rows nothing  c s r = lf-map c s r
  lf-rows (just _) c s r = lf-map c s r

  lf-vals : ∀ m {A} (c : Timeline A) s {y v} → enter (ev m (map val (cold c)) env) s y (out v) → IsVal v
  lf-vals nothing  c s (map-out _ , _) = tt
  lf-vals (just _) c s (map-out _ , _) = tt

  lf-uniqs : ∀ m {A} (c : Timeline A) s {c₁ c₂} → enter (ev m (map val (cold c)) env) s c₁ end → enter (ev m (map val (cold c)) env) s c₂ end → c₁ ≡ c₂
  lf-uniqs nothing  c s (map-end (x , _) , _) (map-end (x′ , _) , _) = ine-end x x′
  lf-uniqs (just _) c s (map-end (x , _) , _) (map-end (x′ , _) , _) = ine-end x x′

  lf-bes : ∀ m {A} (c : Timeline A) s {y e c′} → enter (ev m (map val (cold c)) env) s y e → enter (ev m (map val (cold c)) env) s c′ end → y ≼ c′
  lf-bes nothing  c s r r′ = be-map c s r r′
  lf-bes (just _) c s r r′ = be-map c s r r′

  fc-outs : ∀ m {A} s {y v} → enter (ev m (of (cdone {A} ∷ [])) env) s y (out v) → y ≡ s ⊕ [ ix 0 ] × v ≡ cdone
  fc-outs nothing  s (at-out , _)      = refl , refl
  fc-outs nothing  s (on-out () , _)
  fc-outs (just _) s (at-out , _)      = refl , refl
  fc-outs (just _) s (on-out () , _)

  fc-ends : ∀ m {A} s {y} → enter (ev m (of (cdone {A} ∷ [])) env) s y end → y ≡ s ⊕ [ last ]
  fc-ends nothing  s (on-out at-end , _) = refl
  fc-ends (just _) s (on-out at-end , _) = refl

  fm-ticks : ∀ m {A} s → enter (ev m (of (tick {A} ∷ [])) env) s (s ⊕ [ ix 0 ]) (out tick)
  fm-ticks nothing  s = at-out , of-reach s 0 (tick ∷ []) {s ⊕ [ ix 0 ]} {out tick}
  fm-ticks (just _) s = at-out , of-reach s 0 (tick ∷ []) {s ⊕ [ ix 0 ]} {out tick}

  r-outs : ∀ m {A} (x : Bool × Tag A) s {y v} → enter (ev m (render x) env) s y (out v) → ROut x s y v
  r-outs nothing  (false , val a) s (at-out , _)    = refl , refl
  r-outs nothing  (false , val a) s (on-out () , _)
  r-outs nothing  (true , val a)  s r               = rv-out a s r
  r-outs nothing  (true , cdone)  s r               = cd-out s r
  r-outs nothing  (false , cdone) s (() , _)
  r-outs nothing  (false , tick)  s (() , _)
  r-outs nothing  (true , tick)   s (() , _)
  r-outs (just _) (false , val a) s (at-out , _)    = refl , refl
  r-outs (just _) (false , val a) s (on-out () , _)
  r-outs (just _) (true , val a)  s r               = rv-out a s r
  r-outs (just _) (true , cdone)  s r               = cd-out s r
  r-outs (just _) (false , cdone) s (() , _)
  r-outs (just _) (false , tick)  s (() , _)
  r-outs (just _) (true , tick)   s (() , _)

  module ShapeOf (m : Maybe ℕ) {A : Set} (c : Timeline A) =
    Shape (λ b → ev m (if b then map val (cold c) else of (cdone ∷ [])) env)
          (λ b → ev m (if b then concatˢ (map val (cold c)) (of (cdone ∷ [])) else of (tick ∷ [])) env)
          (λ x → ev m (render x) env)
          (CF.fc-true env m c) (CF.fc-false env m) (CF.fm-true env m c) (CF.fm-false env m) (CF.render-in env m) (CF.render-begin env m)
          (lf-rows m c) (lf-vals m c) (lf-uniqs m c) (lf-bes m c) (fc-outs m) (fc-ends m) (fm-ticks m) (r-outs m)

-- EVERY ROW OF THE COLD SHOWN IS ONE OF ITS SHAPES.
cold-rows : ∀ m {Δ A} (c : Timeline A) (env : DenEnv Δ) p {y e} → enter (ev m (coldˢ c) env) p y e → Visible e → ColdRow p y e
cold-rows nothing  c env p (r , _) = ShapeOf.Mgs.top-row env nothing c p r
cold-rows (just n) c env p (r , _) = ShapeOf.Mgs.top-row env (just n) c p r
