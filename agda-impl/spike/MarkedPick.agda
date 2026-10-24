{-# OPTIONS --guardedness #-}

-- SPIKE: A LANE FIRST, FROM THE PICK.  The order a rising lane needs
-- (`spike.MarkedRace.First`, per flatMap frame: `Sides`) is read off the
-- search that picked it, frame by frame (`won-clear`), not off a
-- predicate on every key the tree owns.  At each frame the engine's race
-- puts every sibling's candidate no earlier than the winner's key, older
-- lanes strictly later (`Won`, as `search` computes it); each sibling's
-- step heads no earlier than its candidate (`spike.MarkedHead.Agrees`,
-- by `head-agrees` at the sibling); and the stepper's head is the
-- meaning's (`sides-link`).
--
-- So a configuration carries only the fragment's shape (`Frag` of its
-- whole tree) and, while a value rises, what that pick established about
-- the frames above it (`Clear`).  Nothing relates two nodes' keys.
module spike.MarkedPick where

open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Pos; Timeline; idle; _∪_)
open import denotation.Unfold using (Step; NEnv; states; outerᴺ; step; headˢ; hushˢ; outˢ; skipˢ; endˢ)
open import operation.Key using (Key; at; _<ᴷ_)
open import operation.MarkedPure using (module Machine)
open Machine using (St; mapS; scanS; cutS; lnS; takeS; flatS; connS; Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes;
  inSrc; inBody; plug; closed; Out; still; seek; search; found; Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising)
open import spike.MarkedGhost using (gh; lane; outerG; poolG; lanesL; deadL; poolT; tailsOn; outerT; envAt)
open import spike.MarkedRace using (First; NotBefore; After)
open import spike.MarkedHead using (Frag; Lanes; Lane; Agrees; exact; early; HeadAt; cand; pool-step; at-<ᵖ; <≮ᴷ; ≮ᴷ-trans)
open import spike.MarkedHead.Agrees using (head-agrees)

------------------------------------------------------------------------
-- What a rising lane leads

-- A flatMap's other parts, as a lane rising at `p` leads them.
Sides : ∀ {Γ A B} → Pos → (A → Obs Timeline Γ B) → Bool → St Γ A → List (St Γ B) → List (St Γ B) → NEnv Γ → Set
Sides p f d o pre post ρ =
  First p (outerᴺ (lane f) (outerG d (gh o)) ρ) (states (lanesL post) ρ) (states (lanesL pre) ρ)
    (outerT d (gh o) ρ (tailsOn (deadL pre) ρ (idle ∪ poolT (deadL post) ρ)))

-- Every flatMap frame above a value rising at `p`, while its observer is open.
Clear : ∀ {R Γ A} → Pos → Ctx R Γ A → Set
Clear p top                               = ⊤
Clear p (inMap f c)                       = Clear p c
Clear p (inScan f z c)                    = Clear p c
Clear p (inCut l a c)                     = Clear p c
Clear p (inLn b c)                        = Clear p c
Clear p (inTake i q w c)                  = Clear p c
Clear p (inOuter op f d n q ls c)         = Clear p c
Clear p (inLanes op f d n q o pre post c) = (closed c ≡ false → Sides p f d o pre post (envAt c)) × Clear p c
Clear p (inSrc k b c)                     = Clear p c
Clear p (inBody k o c)                    = Clear p c

-- The configuration's order: the whole tree's shape, and a rise's lead.
Lead : ∀ {R} → Conf R → Set
Lead ⟨ c , s , rising e , p ⟩  = Clear p c
Lead ⟨ c , s , subscribing , p ⟩ = ⊤
Lead ⟨ c , s , absorbed , p ⟩    = ⊤

whole : ∀ {R} → Conf R → St [] R
whole ⟨ c , s , m , p ⟩ = plug c s

record Order {R} (k : Conf R) : Set where
  constructor order
  field
    shape : Frag (whole k)
    lead  : Lead k

------------------------------------------------------------------------
-- The engine's race, as the winner's frames saw it

-- Strictly after a key; not before it.
KAfter KNotBefore : ∀ {A} → Key → Maybe (Key × Out A) → Set
KAfter     k nothing        = ⊤
KAfter     k (just (h , _)) = k <ᴷ h ≡ true
KNotBefore k nothing        = ⊤
KNotBefore k (just (h , _)) = h <ᴷ k ≡ false

-- Each lane of `ls`, sought as the engine's fold seeks it, `P` of `k`;
-- `acc` the lanes before, `tl` the lanes after the list.
Race : ∀ {R Γ A B} → (Key → Maybe (Key × Out B) → Set) → Key → Ctx R Γ B → FlatOp → (A → Obs Timeline Γ B) → Bool → ℕ → List A → St Γ A
     → List (St Γ B) → List (St Γ B) → List (St Γ B) → Set
Race P k c op f d n q o acc []       tl = ⊤
Race P k c op f d n q o acc (x ∷ xs) tl = P k (cand (inLanes op f d n q o acc (xs ++ tl) c) x) × Race P k c op f d n q o (acc ++ [ x ]) xs tl

-- The lane `s` won its flatMap's race: the outer and the newer lanes no
-- earlier, the older lanes strictly later.
record LaneWon {R Γ A B} (k : Key) (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) (pre post : List (St Γ B)) (s : St Γ B) : Set where
  constructor lane-won
  field
    outerW : KNotBefore k (cand (inOuter op f d n q (pre ++ s ∷ post) c) o)
    olderW : Race KAfter k c op f d n q o [] pre (s ∷ post)
    newerW : Race KNotBefore k c op f d n q o (pre ++ [ s ]) post []

-- Every flatMap above the found node raced it in.
Won : ∀ {R Γ A} → Key → Ctx R Γ A → St Γ A → Set
Won k top s                               = ⊤
Won k (inMap f c) s                       = Won k c (mapS f s)
Won k (inScan f z c) s                    = Won k c (scanS f z s)
Won k (inCut l a c) s                     = Won k c (cutS l a s)
Won k (inLn b c) s                        = Won k c (lnS b s)
Won k (inTake i q w c) s                  = Won k c (takeS i q w s)
Won k (inOuter op f d n q ls c) s         = Won k c (flatS op f d n q s ls)
Won k (inLanes op f d n q o pre post c) s = LaneWon k c op f d n q o pre post s × Won k c (flatS op f d n q o (pre ++ s ∷ post))
Won k (inSrc kk b c) s                    = Won k c (connS kk s b)
Won k (inBody kk o c) s                   = Won k c (connS kk o s)

postulate
  -- The engine's search: the found node's key leads every race above it.
  search-won : ∀ {R} (t : St [] R) {Γ A} {c : Ctx R Γ A} {s m key} → search top t ≡ just (found (Γ , A , c , s) m key) → Won key c s
  -- A flatMap of a fragment tree is of the fragment.
  frag-flat : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls
            → Frag (plug c (flatS op f d n q o ls)) → Frag (flatS op f d n q o ls)

------------------------------------------------------------------------
-- From the race to the stepper's heads

after-step : ∀ {Γ A} q (x : Maybe (Key × Out A)) (st : Step Γ A) → KAfter (at q) x → Agrees x st → After q (headˢ st)
after-step q _ (outˢ h a n) w (exact refl) = subst (λ b → b ≡ true) (at-<ᵖ q h) w
after-step q _ (skipˢ h n)  w (exact refl) = subst (λ b → b ≡ true) (at-<ᵖ q h) w
after-step q _ (endˢ h)     w (exact refl) = subst (λ b → b ≡ true) (at-<ᵖ q h) w
after-step q _ hushˢ        w (exact refl) = tt
after-step q (just (k , still)) st w (early u) with headˢ st
... | nothing = tt
... | just h  = subst (λ b → b ≡ true) (at-<ᵖ q h) (<≮ᴷ (at q) k (at h) w u)

not-before-step : ∀ {Γ A} q (x : Maybe (Key × Out A)) (st : Step Γ A) → KNotBefore (at q) x → Agrees x st → NotBefore q (headˢ st)
not-before-step q _ (outˢ h a n) w (exact refl) = subst (λ b → b ≡ false) (at-<ᵖ h q) w
not-before-step q _ (skipˢ h n)  w (exact refl) = subst (λ b → b ≡ false) (at-<ᵖ h q) w
not-before-step q _ (endˢ h)     w (exact refl) = subst (λ b → b ≡ false) (at-<ᵖ h q) w
not-before-step q _ hushˢ        w (exact refl) = tt
not-before-step q (just (k , still)) st w (early u) with headˢ st
... | nothing = tt
... | just h  = subst (λ b → b ≡ false) (at-<ᵖ h q) (≮ᴷ-trans (at h) k (at q) u w)

-- A node's head, read at an open observer.
open-agrees : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → closed c ≡ false → Frag s → Agrees (cand c s) (step (gh s))
open-agrees c s cl fs = subst (λ b → HeadAt b (cand c s) s) cl (head-agrees c s fs)

-- Each live lane of a race, its step's head related as its candidate.
race-steps : ∀ {R Γ A B} (P : Key → Maybe (Key × Out B) → Set) (Q : Maybe Pos → Set) (k : Key)
           → (∀ {Γ′} (x : Maybe (Key × Out B)) (st : Step Γ′ B) → P k x → Agrees x st → Q (headˢ st))
           → ∀ (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) acc ls tl → closed c ≡ false → Lanes ls
           → Race P k c op f d n q o acc ls tl → All (λ m → Q (headˢ (step m))) (lanesL ls)
race-steps P Q k h c op f d n q o acc [] tl cl _ _ = []
race-steps P Q k h c op f d n q o acc (lnS true (cutS true a y) ∷ xs) tl cl (fy , fl) (r , rs) =
  all-++⁺ (race-steps P Q k h c op f d n q o (acc ++ [ lnS true (cutS true a y) ]) xs tl cl fl rs)
          (h _ (step (gh y)) r (open-agrees (inLn true (inLanes op f d n q o acc (xs ++ tl) c)) (cutS true a y) cl fy) ∷ [])
race-steps P Q k h c op f d n q o acc (lnS false (cutS false a y) ∷ xs) tl cl (fy , fl) (r , rs) =
  all-++⁺ (race-steps P Q k h c op f d n q o (acc ++ [ lnS false (cutS false a y) ]) xs tl cl fl rs) []

lanes-split : ∀ {Γ A} (pre : List (St Γ A)) {s post} → Lanes (pre ++ s ∷ post) → Lanes pre × Lane s × Lanes post
lanes-split []        (l , ls) = tt , l , ls
lanes-split (x ∷ pre) (l , ls) with lanes-split pre ls
... | u , v , w = (l , u) , v , w

------------------------------------------------------------------------
-- From the stepper's heads to the meaning's

-- What the stepper shows of a flatMap's other parts, a lane rising at `p`.
record StepSides {Γ A B} (p : Pos) d (o : St Γ A) (pre post : List (St Γ B)) (s : St Γ B) : Set₁ where
  constructor step-sides
  field
    newerS : All (λ m → NotBefore p (headˢ (step m))) (lanesL post)
    olderS : All (λ m → After p (headˢ (step m))) (lanesL pre)
    outerS : d ≡ false → NotBefore p (headˢ (step (gh o)))
    poolS  : step (poolG d (gh o) (deadL (pre ++ s ∷ post))) ≡ hushˢ

postulate
  -- The meaning's heads are the stepper's; a pool the stepper hushes
  -- leaves nothing running.
  sides-link : ∀ {R Γ A B} (c : Ctx R Γ B) p (f : A → Obs Timeline Γ B) d n (o : St Γ A) pre post (s : St Γ B)
             → Frag (plug c (flatS (mergeᶠ nothing) f d n [] o (pre ++ s ∷ post))) → StepSides p d o pre post s
             → Sides p f d o pre post (envAt c)

  -- A bounded, switching or exhausting flatMap's lane that won: its
  -- queue and its one-lane rule sit outside the stepper's race, so the
  -- merge clause's route does not apply as written.
  limited-sides : ∀ {R Γ A B} p (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B)
                → (op ≡ mergeᶠ nothing → ⊥) → closed c ≡ false → LaneWon (at p) c op f d n q o pre post s
                → Frag (plug c (flatS op f d n q o (pre ++ s ∷ post))) → Sides p f d o pre post (envAt c)

-- The frame a lane won: what the pick establishes of its siblings.
lane-sides : ∀ {R Γ A B} p (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B)
           → closed c ≡ false → LaneWon (at p) c op f d n q o pre post s → Frag (plug c (flatS op f d n q o (pre ++ s ∷ post)))
           → Frag (flatS op f d n q o (pre ++ s ∷ post)) → Sides p f d o pre post (envAt c)
lane-sides p c (mergeᶠ nothing) f d n [] o pre post s cl (lane-won wo wold wnew) ft (fo , fl , en , dd) =
  sides-link c p f d n o pre post s ft
    (step-sides (race-steps KNotBefore (NotBefore p) (at p) (not-before-step p) c (mergeᶠ nothing) f d n [] o (pre ++ [ s ]) post [] cl
                  (proj₂ (proj₂ (lanes-split pre fl))) wnew)
                (race-steps KAfter (After p) (at p) (after-step p) c (mergeᶠ nothing) f d n [] o [] pre (s ∷ post) cl
                  (proj₁ (lanes-split pre fl)) wold)
                (λ { refl → not-before-step p _ (step (gh o)) wo (open-agrees (inOuter (mergeᶠ nothing) f false n [] (pre ++ s ∷ post) c) o cl fo) })
                (pool-step d o (pre ++ s ∷ post) fo fl (λ e → proj₂ (dd e))))
lane-sides p c (mergeᶠ (just m)) f d n q o pre post s cl w ft _ = limited-sides p c (mergeᶠ (just m)) f d n q o pre post s (λ ()) cl w ft
lane-sides p c switchᶠ f d n q o pre post s cl w ft _ = limited-sides p c switchᶠ f d n q o pre post s (λ ()) cl w ft
lane-sides p c exhaustᶠ f d n q o pre post s cl w ft _ = limited-sides p c exhaustᶠ f d n q o pre post s (λ ()) cl w ft

-- Up the found node's frames: each flatMap it won is clear.
won-clear : ∀ {R Γ A} p (c : Ctx R Γ A) (s : St Γ A) → Won (at p) c s → Frag (plug c s) → Clear p c
won-clear p top                               s w       ft = tt
won-clear p (inMap f c)                       s w       ft = won-clear p c (mapS f s) w ft
won-clear p (inScan f z c)                    s w       ft = won-clear p c (scanS f z s) w ft
won-clear p (inCut l a c)                     s w       ft = won-clear p c (cutS l a s) w ft
won-clear p (inLn b c)                        s w       ft = won-clear p c (lnS b s) w ft
won-clear p (inTake i q w′ c)                 s w       ft = won-clear p c (takeS i q w′ s) w ft
won-clear p (inOuter op f d n q ls c)         s w       ft = won-clear p c (flatS op f d n q s ls) w ft
won-clear p (inLanes op f d n q o pre post c) s (l , w) ft =
  (λ cl → lane-sides p c op f d n q o pre post s cl l ft (frag-flat c op f d n q o (pre ++ s ∷ post) ft))
  , won-clear p c (flatS op f d n q o (pre ++ s ∷ post)) w ft
won-clear p (inSrc kk b c)                    s w       ft = won-clear p c (connS kk s b) w ft
won-clear p (inBody kk o c)                   s w       ft = won-clear p c (connS kk o s) w ft
