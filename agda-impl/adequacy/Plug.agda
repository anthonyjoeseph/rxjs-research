-- ONE NODE IN ITS CONTEXT.  A configuration with a hole, the operators
-- from the hole up to the root, and the stepper read through it: when
-- the hole's next event comes before every sibling's, the root's step
-- is the hole's, lifted frame by frame.  `Wins` is that condition, one
-- conjunct per frame, written as the stepper's own comparisons.
module adequacy.Plug where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Unit.Polymorphic using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

import Tree as T
open import denotation.MonotonicList using (Pos; ix; _<ᵖ_)
open import denotation.Unfold using (Node; mapᶜ; scanᶜ; takeWhileᶜ; flatMapᶜ; connectᶜ; live; ended; feed; shut
                                    ; Step; outˢ; skipˢ; endˢ; hushˢ; headˢ; step; mapˢ; scanˢ; takeWhileˢ; outerˢ; laneˢ
                                    ; bodyˢ; shutˢᵗ; sourceˢ; beforeˢ; raceˢ; goˢ; Earliest; none; found; pick; earliest)

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
