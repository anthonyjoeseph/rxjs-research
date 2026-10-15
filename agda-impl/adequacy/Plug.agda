-- ONE NODE IN ITS CONTEXT.  A configuration with a hole, the operators
-- from the hole up to the root, and the stepper read through it: when
-- the hole's next event comes before every sibling's, the root's step
-- is the hole's, lifted frame by frame.  `Wins` is that condition, one
-- conjunct per frame, written as the stepper's own comparisons.
module adequacy.Plug where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as AllP
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

import Tree as T
open import denotation.MonotonicList using (Pos; ix; last; _<ᵖ_; <ᵖ-asym; <ᵖ-++ʳ)
open import denotation.Unfold using (Node; mapᶜ; scanᶜ; takeWhileᶜ; flatMapᶜ; connectᶜ; live; ended; feed; shut
                                    ; Step; outˢ; skipˢ; endˢ; hushˢ; headˢ; step; mapˢ; scanˢ; takeWhileˢ; outerˢ; laneˢ
                                    ; bodyˢ; shutˢᵗ; sourceˢ; beforeˢ; raceˢ; goˢ; Earliest; none; found; pick; earliest; taking; admit
                                    ; shutᴹ; shutᴸ)

data Nope : Set₁ where

------------------------------------------------------------------------
-- Frames and contexts

-- One operator over the hole: the hole's scope and type, then the
-- operator's.  A flatMap's outer or one of its lanes; a connect's body,
-- beside its source running or ended, or its source beside its body.
data Frame : List Set → Set → List Set → Set → Set₁ where
  mapF   : ∀ {Γ A B} → (A → B) → Frame Γ A Γ B
  scanF  : ∀ {Γ A B} → (B → A → B) → B → Frame Γ A Γ B
  takeF  : ∀ {Γ A} → Bool → (A → Bool) → Frame Γ A Γ A
  outerF : ∀ {Γ A B} → T.FlatOp → (A → Pos → Node Γ B) → List (Node Γ B) → List A → Frame Γ A Γ B
  laneF  : ∀ {Γ A B} → T.FlatOp → (A → Pos → Node Γ B) → Maybe (Node Γ A) → List (Node Γ B) → List (Node Γ B) → List A → Frame Γ B Γ B
  bodyF  : ∀ {Γ A B} → Node Γ A → Frame (A ∷ Γ) B Γ B
  endedF : ∀ {Γ A B} → Pos → Frame (A ∷ Γ) B Γ B
  srcF   : ∀ {Γ A B} → Node (A ∷ Γ) B → Frame Γ A Γ B

-- The frames from the hole up, innermost first.
infixr 5 _∷_
data Ctx : List Set → Set → List Set → Set → Set₁ where
  []  : ∀ {Γ A} → Ctx Γ A Γ A
  _∷_ : ∀ {Γ A Γ₁ A₁ Δ B} → Frame Γ A Γ₁ A₁ → Ctx Γ₁ A₁ Δ B → Ctx Γ A Δ B

plugF : ∀ {Γ A Δ B} → Frame Γ A Δ B → Node Γ A → Node Δ B
plugF (mapF f)                n = mapᶜ f n
plugF (scanF f z)             n = scanᶜ f z n
plugF (takeF i p)             n = takeWhileᶜ i p n
plugF (outerF op g ls qs)     n = flatMapᶜ op g (just n) ls qs
plugF (laneF op g o bs as qs) n = flatMapᶜ op g o (bs ++ n ∷ as) qs
plugF (bodyF s)               n = connectᶜ n (live s)
plugF (endedF c)              n = connectᶜ n (ended c)
plugF (srcF b)                n = connectᶜ b (live n)

plug : ∀ {Γ A Δ B} → Ctx Γ A Δ B → Node Γ A → Node Δ B
plug []      n = n
plug (F ∷ C) n = plug C (plugF F n)

------------------------------------------------------------------------
-- The hole's step, lifted

-- A connect's source stepping before its body.
srcWin : ∀ {Γ A B} → Node (A ∷ Γ) B → Step Γ A → Step Γ B
srcWin b (outˢ q a s′) = skipˢ (q ++ [ ix 0 ]) (connectᶜ (feed (here refl) q a b) (live s′))
srcWin b (skipˢ q s′)  = skipˢ (q ++ [ ix 0 ]) (connectᶜ b (live s′))
srcWin b (endˢ c)      = skipˢ (c ++ [ ix 0 ]) (connectᶜ (shut (here refl) c b) (ended c))
srcWin b hushˢ         = hushˢ

liftF : ∀ {Γ A Δ B} → Frame Γ A Δ B → Step Γ A → Step Δ B
liftF (mapF f)                = mapˢ f
liftF (scanF f z)             = scanˢ f z
liftF (takeF i p)             = takeWhileˢ i p
liftF (outerF op g ls qs)   s = outerˢ op g s ls qs
liftF (laneF op g o bs as qs) s = laneˢ op g o bs s as qs
liftF (bodyF src)             = bodyˢ (live src)
liftF (endedF c)              = shutˢᵗ c
liftF (srcF b)                = srcWin b

lift : ∀ {Γ A Δ B} → Ctx Γ A Δ B → Step Γ A → Step Δ B
lift []      s = s
lift (F ∷ C) s = lift C (liftF F s)

------------------------------------------------------------------------
-- The hole first

-- A sibling's next event strictly after `k`, or none.
Later : Pos → Maybe Pos → Set
Later k nothing   = ⊤
Later k (just k′) = k <ᵖ k′ ≡ true

-- A sibling's next event not before `k`, or none.
NotBefore : Pos → Maybe Pos → Set
NotBefore k nothing   = ⊤
NotBefore k (just k′) = k′ <ᵖ k ≡ false

HeadIs : Maybe Pos → (Pos → Set₁) → Set₁
HeadIs nothing  P = Nope
HeadIs (just k) P = P k

OuterNB : ∀ {Γ A} → Pos → Maybe (Node Γ A) → Set
OuterNB k nothing  = ⊤
OuterNB k (just o) = NotBefore k (headˢ (step o))

-- The source's next feed not before the body's next event.
SrcAfter : ∀ {Γ A B} → Step Γ A → Step (A ∷ Γ) B → Set
SrcAfter (outˢ q _ _) sb = beforeˢ (q ++ [ ix 0 ]) sb ≡ false
SrcAfter (skipˢ q _)  sb = beforeˢ (q ++ [ ix 0 ]) sb ≡ false
SrcAfter (endˢ c)     sb = beforeˢ (c ++ [ ix 0 ]) sb ≡ false
SrcAfter hushˢ        sb = ⊤

-- The source's next feed before the body's next event.
SrcFirst : ∀ {Γ A B} → Step (A ∷ Γ) B → Step Γ A → Set₁
SrcFirst sb (outˢ q _ _) = beforeˢ (q ++ [ ix 0 ]) sb ≡ true × ⊤
SrcFirst sb (skipˢ q _)  = beforeˢ (q ++ [ ix 0 ]) sb ≡ true × ⊤
SrcFirst sb (endˢ c)     = beforeˢ (c ++ [ ix 0 ]) sb ≡ true × ⊤
SrcFirst sb hushˢ        = Nope

WinsF : ∀ {Γ A Δ B} → Frame Γ A Δ B → Step Γ A → Set₁
WinsF (outerF op g ls qs)     s = HeadIs (headˢ s) λ k → All (λ l → Later k (headˢ (step l))) ls
WinsF (laneF op g o bs as qs) s = HeadIs (headˢ s) λ k → OuterNB k o × All (λ l → NotBefore k (headˢ (step l))) bs
                                                         × All (λ l → Later k (headˢ (step l))) as
WinsF (bodyF src)             s = SrcAfter (step src) s × ⊤
WinsF (srcF b)                s = SrcFirst (step b) s
WinsF _                       s = ⊤

Wins : ∀ {Γ A Δ B} → Ctx Γ A Δ B → Step Γ A → Set₁
Wins []      s = ⊤
Wins (F ∷ C) s = WinsF F s × Wins C (liftF F s)

------------------------------------------------------------------------
-- The earliest lane

private
  if-elim : ∀ {X : Set₁} (P : X → Set₁) b {x y} → P x → P y → P (if b then x else y)
  if-elim P true  px py = px
  if-elim P false px py = py

  ELater : ∀ {Γ B} → Pos → List (Node Γ B) → Earliest Γ B → Set₁
  ELater k ls none                  = ⊤
  ELater k ls (found k′ bs l sl as) = k <ᵖ k′ ≡ true × bs ++ l ∷ as ≡ ls

  pick-later : ∀ {Γ B} k (l : Node Γ B) s ls h E → Later k h → ELater k ls E → ELater k (l ∷ ls) (pick l s ls h E)
  pick-later k l s ls nothing   none                   p e          = _
  pick-later k l s ls nothing   (found k′ bs c sc as)  p (lt , eq)  = lt , cong (l ∷_) eq
  pick-later k l s ls (just k₁) none                   p e          = p , refl
  pick-later k l s ls (just k₁) (found k′ bs c sc as)  p (lt , eq)  =
    if-elim (ELater k (l ∷ ls)) (k₁ <ᵖ k′) (p , refl) (lt , cong (l ∷_) eq)

  earliest-later : ∀ {Γ B} k (ls : List (Node Γ B)) → All (λ l → Later k (headˢ (step l))) ls → ELater k ls (earliest ls)
  earliest-later k []       []       = _
  earliest-later k (l ∷ ls) (p ∷ ps) = pick-later k l (step l) ls (headˢ (step l)) (earliest ls) p (earliest-later k ls ps)

  pick-here : ∀ {Γ B} k (n : Node Γ B) s as h E → h ≡ just k → ELater k as E → pick n s as h E ≡ found k [] n s as
  pick-here k n s as _ none                   refl e        = refl
  pick-here k n s as _ (found k′ bs c sc as′) refl (lt , _) rewrite lt = refl

  pick-behind : ∀ {Γ B} k (b : Node Γ B) sb rest h bs n sn as → NotBefore k h
              → pick b sb rest h (found k bs n sn as) ≡ found k (b ∷ bs) n sn as
  pick-behind k b sb rest nothing   bs n sn as nb = refl
  pick-behind k b sb rest (just kb) bs n sn as nb rewrite nb = refl

  earliest-at : ∀ {Γ B} k (n : Node Γ B) bs as → headˢ (step n) ≡ just k
              → All (λ l → NotBefore k (headˢ (step l))) bs → All (λ l → Later k (headˢ (step l))) as
              → earliest (bs ++ n ∷ as) ≡ found k bs n (step n) as
  earliest-at k n []       as hk []         las = pick-here k n (step n) as (headˢ (step n)) (earliest as) hk (earliest-later k as las)
  earliest-at k n (b ∷ bs) as hk (nb ∷ nbs) las =
    trans (cong (pick b (step b) (bs ++ n ∷ as) (headˢ (step b))) (earliest-at k n bs as hk nbs las))
          (pick-behind k b (step b) (bs ++ n ∷ as) (headˢ (step b)) bs n (step n) as nb)

  head-of : ∀ {P : Pos → Set₁} (m : Maybe Pos) → HeadIs m P → Σ Pos λ k → m ≡ just k × P k
  head-of nothing  ()
  head-of (just k) p = k , refl , p

------------------------------------------------------------------------
-- The root steps as the hole

private
  body-wins : ∀ {Γ A B} (b : Node (A ∷ Γ) B) sb (s : Node Γ A) ss → SrcAfter ss sb → sourceˢ b sb s ss ≡ bodyˢ (live s) sb
  body-wins b sb s (outˢ q a s′) w rewrite w = refl
  body-wins b sb s (skipˢ q s′)  w rewrite w = refl
  body-wins b sb s (endˢ c)      w rewrite w = refl
  body-wins b sb s hushˢ         w = refl

  src-wins : ∀ {Γ A B} (b : Node (A ∷ Γ) B) sb (s : Node Γ A) ss → SrcFirst sb ss → sourceˢ b sb s ss ≡ srcWin b ss
  src-wins b sb s (outˢ q a s′) (w , _) rewrite w = refl
  src-wins b sb s (skipˢ q s′)  (w , _) rewrite w = refl
  src-wins b sb s (endˢ c)      (w , _) rewrite w = refl
  src-wins b sb s hushˢ         ()

  outer-go : ∀ {Γ A B} op (g : A → Pos → Node Γ B) (n : Node Γ A) ls qs k → headˢ (step n) ≡ just k → (E : Earliest Γ B) → ELater k ls E
           → goˢ op g (just n) ls qs E ≡ outerˢ op g (step n) ls qs
  outer-go op g n ls               qs k hk none                  e           = refl
  outer-go op g n .(bs ++ l ∷ as) qs k hk (found k′ bs l sl as) (lt , refl) rewrite hk | lt = refl

  race-lane : ∀ {Γ A B} op (g : A → Pos → Node Γ B) (o : Node Γ A) so h k bs n sn as qs → NotBefore k h
            → raceˢ op g o so h k bs n sn as qs ≡ laneˢ op g (just o) bs sn as qs
  race-lane op g o so nothing   k bs n sn as qs nb = refl
  race-lane op g o so (just k′) k bs n sn as qs nb rewrite nb = refl

  lane-go : ∀ {Γ A B} op (g : A → Pos → Node Γ B) (o : Maybe (Node Γ A)) bs (n : Node Γ B) as qs k → OuterNB k o
          → goˢ op g o (bs ++ n ∷ as) qs (found k bs n (step n) as) ≡ laneˢ op g o bs (step n) as qs
  lane-go op g nothing   bs n as qs k nb = refl
  lane-go op g (just o) bs n as qs k nb = race-lane op g o (step o) (headˢ (step o)) k bs n (step n) as qs nb

plugF-step : ∀ {Γ A Δ B} (F : Frame Γ A Δ B) (n : Node Γ A) → WinsF F (step n) → step (plugF F n) ≡ liftF F (step n)
plugF-step (mapF f)                n w = refl
plugF-step (scanF f z)             n w = refl
plugF-step (takeF i p)             n w = refl
plugF-step (outerF op g ls qs)     n w with head-of (headˢ (step n)) w
... | k , hk , las = outer-go op g n ls qs k hk (earliest ls) (earliest-later k ls las)
plugF-step (laneF op g o bs as qs) n w with head-of (headˢ (step n)) w
... | k , hk , onb , nbs , las =
  trans (cong (goˢ op g o (bs ++ n ∷ as) qs) (earliest-at k n bs as hk nbs las)) (lane-go op g o bs n as qs k onb)
plugF-step (bodyF src)             n (w , _) = body-wins n (step n) src (step src) w
plugF-step (endedF c)              n w = refl
plugF-step (srcF b)                n w = src-wins b (step b) n (step n) w

-- THE HOLE FIRST, THE ROOT STEPS AS IT.
plug-step : ∀ {Γ A Δ B} (C : Ctx Γ A Δ B) (n : Node Γ A) → Wins C (step n) → step (plug C n) ≡ lift C (step n)
plug-step []      n w        = refl
plug-step (F ∷ C) n (wf , wc) = trans (plug-step C (plugF F n) (subst (Wins C) (sym e) wc)) (cong (lift C) e)
  where e = plugF-step F n wf

------------------------------------------------------------------------
-- A skip stays a skip

skip-liftsF : ∀ {Γ A Δ B} (F : Frame Γ A Δ B) k (n : Node Γ A) → Σ Pos λ k′ → Σ (Node Δ B) λ c → liftF F (skipˢ k n) ≡ skipˢ k′ c
skip-liftsF (mapF f)                k n = _ , _ , refl
skip-liftsF (scanF f z)             k n = _ , _ , refl
skip-liftsF (takeF i p)             k n = _ , _ , refl
skip-liftsF (outerF op g ls qs)     k n = _ , _ , refl
skip-liftsF (laneF op g o bs as qs) k n = _ , _ , refl
skip-liftsF (bodyF src)             k n = _ , _ , refl
skip-liftsF (endedF c)              k n = _ , _ , refl
skip-liftsF (srcF b)                k n = _ , _ , refl

skip-lifts : ∀ {Γ A Δ B} (C : Ctx Γ A Δ B) k (n : Node Γ A) → Σ Pos λ k′ → Σ (Node Δ B) λ c → lift C (skipˢ k n) ≡ skipˢ k′ c
skip-lifts []      k n = k , n , refl
skip-lifts (F ∷ C) k n with skip-liftsF F k n
... | k₁ , n₁ , e with skip-lifts C k₁ n₁
...   | k′ , c , e′ = k′ , c , trans (cong (lift C) e) e′

------------------------------------------------------------------------
-- Every sibling beyond the hole's root

-- Strictly after everything at or under `r`.
Beyond : Pos → Maybe Pos → Set
Beyond r nothing   = ⊤
Beyond r (just k′) = ∀ x → (r ++ x) <ᵖ k′ ≡ true

Beyondᴺ : ∀ {Γ A} → Pos → Node Γ A → Set
Beyondᴺ r n = Beyond r (headˢ (step n))

OuterB : ∀ {Γ A} → Pos → Maybe (Node Γ A) → Set
OuterB r nothing  = ⊤
OuterB r (just o) = Beyondᴺ r o

-- Every sibling a frame holds waits beyond `r`.
ClearF : ∀ {Γ A Δ B} → Pos → Frame Γ A Δ B → Set₁
ClearF r (outerF op g ls qs)     = All (Beyondᴺ r) ls
ClearF r (laneF op g o bs as qs) = OuterB r o × All (Beyondᴺ r) bs × All (Beyondᴺ r) as
ClearF r (bodyF src)             = Beyondᴺ r src × ⊤
ClearF r (srcF b)                = Beyondᴺ r b × ⊤
ClearF r _                       = ⊤

Clear : ∀ {Γ A Δ B} → Pos → Ctx Γ A Δ B → Set₁
Clear r []      = ⊤
Clear r (F ∷ C) = ClearF r F × Clear r C

-- A lift keeps a step's head or moves it under it.
Ext : Pos → Maybe Pos → Set
Ext k m = Σ Pos λ y → m ≡ just (k ++ y)

private
  kept-at : ∀ k → Ext k (just k)
  kept-at k = [] , cong just (sym (++-identityʳ k))

  under : ∀ k y → Ext k (just (k ++ y))
  under k y = y , refl

  taking-head : ∀ {Γ A} i (p : A → Bool) k a (c : Node Γ A) t → Ext k (headˢ (taking i p k a c t))
  taking-head i     p k a c true  = kept-at k
  taking-head true  p k a c false = kept-at k
  taking-head false p k a c false = under k [ last ]

  outer-head : ∀ {Γ A B} op (g : A → Pos → Node Γ B) (s : Step Γ A) ls qs {k} → headˢ s ≡ just k
             → Ext k (headˢ (outerˢ op g s ls qs))
  outer-head op g (outˢ q a o) ls qs refl with admit op g (q ++ [ ix 1 ]) a ls qs
  ... | _ , _ = under q [ ix 0 ]
  outer-head op g (skipˢ q o) ls       qs      refl = kept-at q
  outer-head op g (endˢ c)    []       []      refl = kept-at c
  outer-head op g (endˢ c)    []       (_ ∷ _) refl = kept-at c
  outer-head op g (endˢ c)    (_ ∷ _)  qs      refl = kept-at c
  outer-head op g hushˢ       ls       qs      ()

  lane-head : ∀ {Γ A B} op (g : A → Pos → Node Γ B) o bs (s : Step Γ B) as qs {k} → headˢ s ≡ just k
            → Ext k (headˢ (laneˢ op g o bs s as qs))
  lane-head op g o        bs      (outˢ k b c)  as      qs       refl = kept-at k
  lane-head op g o        bs      (skipˢ k c)   as      qs       refl = kept-at k
  lane-head op g o        bs      (endˢ c)      as      (_ ∷ _)  refl = under c [ ix 0 ]
  lane-head op g nothing  []      (endˢ c)      []      []       refl = kept-at c
  lane-head op g nothing  []      (endˢ c)      (_ ∷ _) []       refl = kept-at c
  lane-head op g nothing  (_ ∷ _) (endˢ c)      as      []       refl = kept-at c
  lane-head op g (just o) bs      (endˢ c)      as      []       refl = kept-at c
  lane-head op g o        bs      hushˢ         as      qs       ()

  src-head : ∀ {Γ A B} (b : Node (A ∷ Γ) B) (s : Step Γ A) {k} → headˢ s ≡ just k → Ext k (headˢ (srcWin b s))
  src-head b (outˢ q a s′) refl = under q [ ix 0 ]
  src-head b (skipˢ q s′)  refl = under q [ ix 0 ]
  src-head b (endˢ c)      refl = under c [ ix 0 ]
  src-head b hushˢ         ()

liftF-head : ∀ {Γ A Δ B} (F : Frame Γ A Δ B) (s : Step Γ A) {k} → headˢ s ≡ just k → Ext k (headˢ (liftF F s))
liftF-head (mapF f)                (outˢ k a c) refl = kept-at k
liftF-head (mapF f)                (skipˢ k c)  refl = kept-at k
liftF-head (mapF f)                (endˢ k)     refl = kept-at k
liftF-head (scanF f z)             (outˢ k a c) refl = kept-at k
liftF-head (scanF f z)             (skipˢ k c)  refl = kept-at k
liftF-head (scanF f z)             (endˢ k)     refl = kept-at k
liftF-head (takeF i p)             (outˢ k a c) refl = taking-head i p k a c (p a)
liftF-head (takeF i p)             (skipˢ k c)  refl = kept-at k
liftF-head (takeF i p)             (endˢ k)     refl = kept-at k
liftF-head (outerF op g ls qs)     s            h    = outer-head op g s ls qs h
liftF-head (laneF op g o bs as qs) s            h    = lane-head op g o bs s as qs h
liftF-head (bodyF src)             (outˢ k a c) refl = kept-at k
liftF-head (bodyF src)             (skipˢ k c)  refl = kept-at k
liftF-head (bodyF src)             (endˢ k)     refl = kept-at k
liftF-head (endedF e)              (outˢ k a c) refl = kept-at k
liftF-head (endedF e)              (skipˢ k c)  refl = kept-at k
liftF-head (endedF e)              (endˢ k)     refl = kept-at k
liftF-head (srcF b)                s            h    = src-head b s h
liftF-head _                       hushˢ        ()

private
  later-of : ∀ r x m → Beyond r m → Later (r ++ x) m
  later-of r x nothing   _ = tt
  later-of r x (just k′) b = b x

  nb-of : ∀ r x m → Beyond r m → NotBefore (r ++ x) m
  nb-of r x nothing   _ = tt
  nb-of r x (just k′) b = <ᵖ-asym (r ++ x) k′ (b x)

  outer-nb : ∀ {Γ A} r x (o : Maybe (Node Γ A)) → OuterB r o → OuterNB (r ++ x) o
  outer-nb r x nothing  _ = tt
  outer-nb r x (just o) b = nb-of r x (headˢ (step o)) b

  before-head : ∀ {Γ B} q (s : Step Γ B) {k} → headˢ s ≡ just k → beforeˢ q s ≡ q <ᵖ k
  before-head q (outˢ k _ _) refl = refl
  before-head q (skipˢ k _)  refl = refl
  before-head q (endˢ k)     refl = refl
  before-head q hushˢ        ()

  past : ∀ {Γ B} r x q (s : Step Γ B) → (∀ y → (r ++ y) <ᵖ q ≡ true) → headˢ s ≡ just (r ++ x) → beforeˢ (q ++ [ ix 0 ]) s ≡ false
  past r x q s b h = trans (before-head (q ++ [ ix 0 ]) s h) (<ᵖ-asym (r ++ x) (q ++ [ ix 0 ]) (<ᵖ-++ʳ (r ++ x) q [ ix 0 ] (b x)))

  src-after : ∀ {Γ A B} r x (ss : Step Γ A) (s : Step (A ∷ Γ) B) → Beyond r (headˢ ss) → headˢ s ≡ just (r ++ x) → SrcAfter ss s
  src-after r x (outˢ q _ _) s b h = past r x q s b h
  src-after r x (skipˢ q _)  s b h = past r x q s b h
  src-after r x (endˢ c)     s b h = past r x c s b h
  src-after r x hushˢ        s b h = tt

  first-of : ∀ {Γ B} r x (sb : Step Γ B) → Beyond r (headˢ sb) → beforeˢ ((r ++ x) ++ [ ix 0 ]) sb ≡ true
  first-of r x (outˢ k _ _) b rewrite ++-assoc r x [ ix 0 ] = b (x ++ [ ix 0 ])
  first-of r x (skipˢ k _)  b rewrite ++-assoc r x [ ix 0 ] = b (x ++ [ ix 0 ])
  first-of r x (endˢ k)     b rewrite ++-assoc r x [ ix 0 ] = b (x ++ [ ix 0 ])
  first-of r x hushˢ        b = refl

  src-first : ∀ {Γ A B} r x (sb : Step (A ∷ Γ) B) (s : Step Γ A) → Beyond r (headˢ sb) → headˢ s ≡ just (r ++ x) → SrcFirst sb s
  src-first r x sb (outˢ q _ _) b refl = first-of r x sb b , tt
  src-first r x sb (skipˢ q _)  b refl = first-of r x sb b , tt
  src-first r x sb (endˢ c)     b refl = first-of r x sb b , tt
  src-first r x sb hushˢ        b ()

  clear-winsF : ∀ {Γ A Δ B} r x (F : Frame Γ A Δ B) (s : Step Γ A) → ClearF r F → headˢ s ≡ just (r ++ x) → WinsF F s
  clear-winsF r x (outerF op g ls qs) s cf h =
    subst (λ m → HeadIs m λ k → All (λ l → Later k (headˢ (step l))) ls) (sym h)
      (AllP.map (λ {l} → later-of r x (headˢ (step l))) cf)
  clear-winsF r x (laneF op g o bs as qs) s (ob , cbs , cas) h =
    subst (λ m → HeadIs m λ k → OuterNB k o × All (λ l → NotBefore k (headˢ (step l))) bs × All (λ l → Later k (headˢ (step l))) as) (sym h)
      (outer-nb r x o ob , AllP.map (λ {l} → nb-of r x (headˢ (step l))) cbs , AllP.map (λ {l} → later-of r x (headˢ (step l))) cas)
  clear-winsF r x (bodyF src)  s (b , _) h = src-after r x (step src) s b h , tt
  clear-winsF r x (srcF b)     s (cb , _) h = src-first r x (step b) s cb h
  clear-winsF r x (mapF f)     s _ _ = tt
  clear-winsF r x (scanF f z)  s _ _ = tt
  clear-winsF r x (takeF i p)  s _ _ = tt
  clear-winsF r x (endedF c)   s _ _ = tt

-- EVERY SIBLING BEYOND THE ROOT, THE HOLE WINS: whatever it steps at
-- under `r`, each lift keeps under `r`.
clear-wins : ∀ {Γ A Δ B} r x (C : Ctx Γ A Δ B) (s : Step Γ A) → Clear r C → headˢ s ≡ just (r ++ x) → Wins C s
clear-wins r x []      s _         _ = tt
clear-wins r x (F ∷ C) s (cf , cc) h with liftF-head F s h
... | y , e = clear-winsF r x F s cf h , clear-wins r (x ++ y) C (liftF F s) cc (trans e (cong just (++-assoc r x y)))

------------------------------------------------------------------------
-- Contexts built from the root down

-- One more operator, outermost.
_∷ʳᶜ_ : ∀ {Γ A Γ₁ A₁ Δ B} → Ctx Γ A Γ₁ A₁ → Frame Γ₁ A₁ Δ B → Ctx Γ A Δ B
[]      ∷ʳᶜ G = G ∷ []
(F ∷ C) ∷ʳᶜ G = F ∷ (C ∷ʳᶜ G)

plug-∷ʳᶜ : ∀ {Γ A Γ₁ A₁ Δ B} (C : Ctx Γ A Γ₁ A₁) (G : Frame Γ₁ A₁ Δ B) n → plug (C ∷ʳᶜ G) n ≡ plugF G (plug C n)
plug-∷ʳᶜ []      G n = refl
plug-∷ʳᶜ (F ∷ C) G n = plug-∷ʳᶜ C G (plugF F n)

------------------------------------------------------------------------
-- A connect's end told through a context

-- The connect a frame's operator sees, from the hole's scope.
innerF : ∀ {X Γ A Δ B} → Frame Γ A Δ B → X ∈ Δ → X ∈ Γ
innerF (bodyF s)  i = there i
innerF (endedF c) i = there i
innerF (mapF f)                i = i
innerF (scanF f z)             i = i
innerF (takeF b p)             i = i
innerF (outerF op g ls qs)     i = i
innerF (laneF op g o bs as qs) i = i
innerF (srcF b)                i = i

innerC : ∀ {X Γ A Δ B} → Ctx Γ A Δ B → X ∈ Δ → X ∈ Γ
innerC []      i = i
innerC (F ∷ C) i = innerF F (innerC C i)

shutF : ∀ {X Γ A Δ B} → X ∈ Δ → Pos → Frame Γ A Δ B → Frame Γ A Δ B
shutF i c (mapF f)                = mapF f
shutF i c (scanF f z)             = scanF f z
shutF i c (takeF b p)             = takeF b p
shutF i c (outerF op g ls qs)     = outerF op g (shutᴸ i c ls) qs
shutF i c (laneF op g o bs as qs) = laneF op g (shutᴹ i c o) (shutᴸ i c bs) (shutᴸ i c as) qs
shutF i c (bodyF s)               = bodyF (shut i c s)
shutF i c (endedF e)              = endedF e
shutF i c (srcF b)                = srcF (shut (there i) c b)

shutC : ∀ {X Γ A Δ B} → X ∈ Δ → Pos → Ctx Γ A Δ B → Ctx Γ A Δ B
shutC i c []      = []
shutC i c (F ∷ C) = shutF (innerC C i) c F ∷ shutC i c C

private
  shutᴸ-++ : ∀ {X Γ B} (i : X ∈ Γ) c (bs : List (Node Γ B)) n as → shutᴸ i c (bs ++ n ∷ as) ≡ shutᴸ i c bs ++ shut i c n ∷ shutᴸ i c as
  shutᴸ-++ i c []       n as = refl
  shutᴸ-++ i c (b ∷ bs) n as = cong (shut i c b ∷_) (shutᴸ-++ i c bs n as)

shut-plugF : ∀ {X Γ A Δ B} (i : X ∈ Δ) c (F : Frame Γ A Δ B) n → shut i c (plugF F n) ≡ plugF (shutF i c F) (shut (innerF F i) c n)
shut-plugF i c (mapF f)                n = refl
shut-plugF i c (scanF f z)             n = refl
shut-plugF i c (takeF b p)             n = refl
shut-plugF i c (outerF op g ls qs)     n = refl
shut-plugF i c (laneF op g o bs as qs) n = cong (λ l → flatMapᶜ op g (shutᴹ i c o) l qs) (shutᴸ-++ i c bs n as)
shut-plugF i c (bodyF s)               n = refl
shut-plugF i c (endedF e)              n = refl
shut-plugF i c (srcF b)                n = refl

-- TOLD AT THE ROOT, TOLD FRAME BY FRAME.
shut-plug : ∀ {X Γ A Δ B} (i : X ∈ Δ) c (C : Ctx Γ A Δ B) n → shut i c (plug C n) ≡ plug (shutC i c C) (shut (innerC C i) c n)
shut-plug i c []      n = refl
shut-plug i c (F ∷ C) n = trans (shut-plug i c C (plugF F n)) (cong (plug (shutC i c C)) (shut-plugF (innerC C i) c F n))
