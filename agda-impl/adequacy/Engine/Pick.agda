{-# OPTIONS --guardedness #-}

-- A LANE FIRST, FROM THE PICK.  The order a rising lane needs
-- (`adequacy.Engine.Race.First`, per flatMap frame: `Sides`) is read off the
-- search that picked it, frame by frame (`won-clear`), not off a
-- predicate on every key the tree owns.  At each frame the engine's race
-- puts every sibling's candidate no earlier than the winner's key, older
-- lanes strictly later (`Won`, as `search` computes it); each sibling's
-- step heads no earlier than its candidate (`adequacy.Engine.Head.Agrees`,
-- by `head-agrees` at the sibling); and the stepper's head is the
-- meaning's (`sides-link`).
--
-- So a configuration carries the fragment's shape (`Frag` of its whole
-- tree), while a value rises what that pick established about the frames
-- above it (`Clear`), and where the search runs, that a still find leads
-- every race above it past each live source's skips (`Apart`): the
-- engine's race reads a source's skip at one key, while the frames above
-- are asked of every position under it.
--
-- `Clear` follows the value up as `rise` carries it, each frame at the
-- position the value has there: an inclusive takeWhile's failing value
-- reaches the frames above at `p ⊕ [ ix 0 ]`.  `Won` follows the
-- winner's candidate up as `seek` retags it, which moves the key at the
-- same frames by the same `shift`, so each frame's race is read at the
-- position the value will rise to.

-- DEAD ROUTE: one position for every frame (`Clear p c`, the winner's own
--   key throughout).  Above an inclusive takeWhile failing at `p` the value
--   rises at `p ⊕ [ ix 0 ]`; an older lane headed exactly there is after
--   `p` but not after where the value arrives, so no step from the lead at
--   `p` reaches the lead the frame above needs.  The engine's race there
--   is already at the shifted key.
module adequacy.Engine.Pick where

open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; _ʳ++_; [_]; reverse)
open import Data.List.Properties using (ʳ++-defn)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Pos; Timeline; idle; _∪_; ix)
open import denotation.Unfold using (Step; NEnv; states; outerᴺ; step; headˢ; hushˢ; outˢ; skipˢ; endˢ)
open import operation.Key using (Key; at; after; _<ᴷ_)
open import operation.PureObservable using (module Machine)
open Machine using (St; mapS; scanS; cutS; lnS; takeS; flatS; connS; Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes;
  inSrc; inBody; plug; closed; Out; still; shows; seek; search; found; Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising;
  Mark; own; Found; nx; cp; alive; free; cpAt; cutAt; overAt; _⊕_; mapT; scanT; cutT; takeT; laneT; shift; over; outOf)
  renaming (outerT to outerK)
open import adequacy.Engine.Meaning using (gh; lane; outerG; poolG; lanesL; deadL; poolT; tailsOn; outerT; envAt)
open import adequacy.Engine.Race using (First; NotBefore; After)
open import adequacy.Engine.Head using (Frag; Lanes; Lane; Agrees; exact; early; HeadAt; cand; pool-step; at-<ᵖ; <≮ᴷ; ≮ᴷ-trans)
open import adequacy.Engine.Head.Agrees using (head-agrees)

------------------------------------------------------------------------
-- What a rising lane leads

-- A flatMap's other parts, as a lane rising at `p` leads them.
Sides : ∀ {Γ A B} → Pos → (A → Obs Timeline Γ B) → Bool → St Γ A → List (St Γ B) → List (St Γ B) → NEnv Γ → Set
Sides p f d o pre post ρ =
  First p (outerᴺ (lane f) (outerG d (gh o)) ρ) (states (lanesL post) ρ) (states (lanesL pre) ρ)
    (outerT d (gh o) ρ (tailsOn (deadL pre) ρ (idle ∪ poolT (deadL post) ρ)))

-- Every frame a value `a` rising at `p` passes, at the position it has
-- there and the node `rise` leaves below; each flatMap frame while its
-- observer is open.
Clear : ∀ {R Γ A} → Pos → A → Ctx R Γ A → St Γ A → Set
Clear p a top                               s = ⊤
Clear p a (inMap f c)                       s = Clear p (f a) c (mapS f s)
Clear p a (inScan f z c)                    s = Clear p (f z a) c (scanS f (f z a) s)
Clear p a (inCut l x c)                     s = l ≡ true → Clear p a c (cutS l x s)
Clear p a (inLn b c)                        s = Clear p a c (lnS b s)
Clear p a (inTake i q free c)               s = (q a ≡ true → Clear p a c (takeS i q free s))
                                              × (q a ≡ false → i ≡ true → Clear (p ⊕ [ ix 0 ]) a c (takeS i q (cpAt p) s))
Clear p a (inTake i q (cpAt r) c)           s = ⊤
Clear p a (inTake i q (cutAt r) c)          s = ⊤
Clear p a (inTake i q (overAt r) c)         s = ⊤
Clear p a (inOuter op f d n q ls c)         s = ⊤
Clear p a (inLanes op f d n q o pre post c) s =
  alive s ≡ true → (closed c ≡ false → Sides p f d o (reverse pre) post (envAt c)) × Clear p a c (flatS op f d n q o (pre ʳ++ s ∷ post))
Clear p a (inSrc k b c)                     s = over k ≡ false → closed c ≡ false → After (p ⊕ [ ix 0 ]) (headˢ (step (gh b)))
Clear p a (inBody k o c)                    s = Clear p a c (connS k o s)

-- A rise's lead.
Lead : ∀ {R} → Conf R → Set
Lead ⟨ c , s , rising (nx a) , p ⟩ = Clear p a c s
Lead ⟨ c , s , rising cp , p ⟩     = ⊤
Lead ⟨ c , s , subscribing , p ⟩   = ⊤
Lead ⟨ c , s , absorbed , p ⟩      = ⊤

whole : ∀ {R} → Conf R → St [] R
whole ⟨ c , s , m , p ⟩ = plug c s

------------------------------------------------------------------------
-- The engine's race, as the winner's frames saw it

-- Strictly after a key; not before it.
KAfter KNotBefore : ∀ {A} → Key → Maybe (Key × Out A) → Set
KAfter     k nothing        = ⊤
KAfter     k (just (h , _)) = k <ᴷ h ≡ true
KNotBefore k nothing        = ⊤
KNotBefore k (just (h , _)) = h <ᴷ k ≡ false

-- Strictly before each of a node's own marks.
Before : Key → List (Mark × Key) → Set
Before k = All (λ mk → k <ᴷ proj₂ mk ≡ true)

-- Each lane of `ls`, sought as the engine's fold seeks it, `P` of `k`;
-- `acc` the lanes before, nearest first, `tl` the lanes after the list.
Race : ∀ {R Γ A B} → (Key → Maybe (Key × Out B) → Set) → Key → Ctx R Γ B → FlatOp → (A → Obs Timeline Γ B) → Bool → ℕ → List A → St Γ A
     → List (St Γ B) → List (St Γ B) → List (St Γ B) → Set
Race P k c op f d n q o acc []       tl = ⊤
Race P k c op f d n q o acc (x ∷ xs) tl = P k (cand (inLanes op f d n q o acc (xs ++ tl) c) x) × Race P k c op f d n q o (x ∷ acc) xs tl

-- The lane `s` won its flatMap's race: the outer and the newer lanes no
-- earlier, the older lanes strictly later.
record LaneWon {R Γ A B} (k : Key) (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) (pre post : List (St Γ B)) (s : St Γ B) : Set where
  constructor lane-won
  field
    outerW : KNotBefore k (cand (inOuter op f d n q (pre ʳ++ s ∷ post) c) o)
    olderW : Race KAfter k c op f d n q o [] (reverse pre) (s ∷ post)
    newerW : Race KNotBefore k c op f d n q o (s ∷ pre) post []

-- Every flatMap above the found node raced it in, each at the key and
-- event its candidate has there; every connect's body lost to its source.
Won : ∀ {R Γ A} → Key × Out A → Ctx R Γ A → St Γ A → Set
Won h       top                                s = ⊤
Won (k , o) (inMap f c)                        s = Won (mapT f k o) c (mapS f s)
Won (k , o) (inScan f z c)                     s = Won (scanT f z k o) c (scanS f z s)
Won (k , o) (inCut l a c)                      s = Won (cutT l k o) c (cutS l a s)
Won h       (inLn b c)                         s = Won h c (lnS b s)
Won (k , o) (inTake i q w c)                   s = Won (takeT i q w k o) c (takeS i q w s)
Won (k , o) (inOuter op f d n q ls c)          s = Won (outerK n q k o) c (flatS op f d n q s ls)
Won (k , o) (inLanes op f d n q o′ pre post c) s =
  LaneWon k c op f d n q o′ pre post s × Won (uncurry (laneT d n q) (cutT (alive s) k o)) c (flatS op f d n q o′ (pre ʳ++ s ∷ post))
Won (k , o) (inSrc kk b c)                     s =
  KAfter (if over kk then k else shift k) (cand (inBody kk s c) b) × Won ((if over kk then k else shift k) , still) c (connS kk s b)
Won h       (inBody kk o c)                    s = Won h c (connS kk o s)

-- A key past a live source's skips: after every position under it.
past : Bool → Key → Key
past true  k         = k
past false (at p)    = after p
past false (after p) = after p

-- Every race above a still found node, at its key read past each live
-- source's skips: every flatMap's as `Won` reads it; at a connect's
-- source, its body and its own marks after; at its body, its source no
-- earlier and its own marks after.
Beat : ∀ {R Γ A} → Key → Ctx R Γ A → St Γ A → Set
Beat k top                                s = ⊤
Beat k (inMap f c)                        s = Beat k c (mapS f s)
Beat k (inScan f z c)                     s = Beat k c (scanS f z s)
Beat k (inCut l a c)                      s = Beat k c (cutS l a s)
Beat k (inLn b c)                         s = Beat k c (lnS b s)
Beat k (inTake i q w c)                   s = Beat k c (takeS i q w s)
Beat k (inOuter op f d n q ls c)          s = Race KAfter k c op f d n q s [] ls [] × Beat k c (flatS op f d n q s ls)
Beat k (inLanes op f d n q o pre post c)  s = LaneWon k c op f d n q o pre post s × Beat k c (flatS op f d n q o (pre ʳ++ s ∷ post))
Beat k (inSrc kk b c)                     s =
  KAfter (past (over kk) k) (cand (inBody kk s c) b) × Before (past (over kk) k) (own (connS kk s b)) × Beat (past (over kk) k) c (connS kk s b)
Beat k (inBody kk o c)                    s = KNotBefore k (cand (inSrc kk s c) o) × Before k (own (connS kk o s)) × Beat k c (connS kk o s)

-- What the search finds still beats every race above it.
Beats : ∀ {R} → Maybe (Found R) → Set
Beats nothing                                  = ⊤
Beats (just (found (Γ , A , c , s) m key)) = outOf c s m ≡ still → Beat key c s

Apart : ∀ {R} → St [] R → Set
Apart t = Beats (search top t)

-- Where the search runs, the tree is apart.
Searched : ∀ {R} → Conf R → Set
Searched ⟨ c , s , subscribing , p ⟩ = ⊤
Searched ⟨ c , s , absorbed , p ⟩    = Apart (plug c s)
Searched ⟨ c , s , rising e , p ⟩    = ⊤

record Order {R} (k : Conf R) : Set where
  constructor order
  field
    shape : Frag (whole k)
    lead  : Lead k
    apart : Searched k

postulate
  -- The engine's search: the found node's key leads every race above it.
  search-won : ∀ {R} (t : St [] R) {Γ A} {c : Ctx R Γ A} {s m key} → search top t ≡ just (found (Γ , A , c , s) m key)
             → Won (key , outOf c s m) c s
  -- A flatMap of a fragment tree is of the fragment.
  frag-flat : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls
            → Frag (plug c (flatS op f d n q o ls)) → Frag (flatS op f d n q o ls)
  -- A connect's body in a fragment tree is of the fragment.
  frag-body : ∀ {R Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → Frag (plug c (connS k o b)) → Frag b

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
  all-++⁺ (race-steps P Q k h c op f d n q o (lnS true (cutS true a y) ∷ acc) xs tl cl fl rs)
          (h _ (step (gh y)) r (open-agrees (inLn true (inLanes op f d n q o acc (xs ++ tl) c)) (cutS true a y) cl fy) ∷ [])
race-steps P Q k h c op f d n q o acc (lnS false (cutS false a y) ∷ xs) tl cl (fy , fl) (r , rs) =
  all-++⁺ (race-steps P Q k h c op f d n q o (lnS false (cutS false a y) ∷ acc) xs tl cl fl rs) []

lanes-split : ∀ {Γ A} (pre : List (St Γ A)) {s post} → Lanes (pre ++ s ∷ post) → Lanes pre × Lane s × Lanes post
lanes-split []        (l , ls) = tt , l , ls
lanes-split (x ∷ pre) (l , ls) with lanes-split pre ls
... | u , v , w = (l , u) , v , w

-- A lane's context keeps the lanes before it nearest first.
lanes-ʳsplit : ∀ {Γ A} (pre : List (St Γ A)) {s post} → Lanes (pre ʳ++ s ∷ post) → Lanes (reverse pre) × Lane s × Lanes post
lanes-ʳsplit pre l = lanes-split (reverse pre) (subst Lanes (ʳ++-defn pre) l)

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
             → Frag (plug c (flatS (mergeᶠ nothing) f d n [] o (pre ʳ++ s ∷ post))) → StepSides p d o (reverse pre) post s
             → Sides p f d o (reverse pre) post (envAt c)

  -- A bounded, switching or exhausting flatMap's lane that won: its
  -- queue and its one-lane rule sit outside the stepper's race, so the
  -- merge clause's route does not apply as written.
  limited-sides : ∀ {R Γ A B} p (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B)
                → (op ≡ mergeᶠ nothing → ⊥) → closed c ≡ false → LaneWon (at p) c op f d n q o pre post s
                → Frag (plug c (flatS op f d n q o (pre ʳ++ s ∷ post))) → Sides p f d o (reverse pre) post (envAt c)

-- The frame a lane won: what the pick establishes of its siblings.
lane-sides : ∀ {R Γ A B} p (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B)
           → closed c ≡ false → LaneWon (at p) c op f d n q o pre post s → Frag (plug c (flatS op f d n q o (pre ʳ++ s ∷ post)))
           → Frag (flatS op f d n q o (pre ʳ++ s ∷ post)) → Sides p f d o (reverse pre) post (envAt c)
lane-sides p c (mergeᶠ nothing) f d n [] o pre post s cl (lane-won wo wold wnew) ft (fo , fl , en , dd) =
  sides-link c p f d n o pre post s ft
    (step-sides (race-steps KNotBefore (NotBefore p) (at p) (not-before-step p) c (mergeᶠ nothing) f d n [] o (s ∷ pre) post [] cl
                  (proj₂ (proj₂ (lanes-ʳsplit pre fl))) wnew)
                (race-steps KAfter (After p) (at p) (after-step p) c (mergeᶠ nothing) f d n [] o [] (reverse pre) (s ∷ post) cl
                  (proj₁ (lanes-ʳsplit pre fl)) wold)
                (λ { refl → not-before-step p _ (step (gh o)) wo (open-agrees (inOuter (mergeᶠ nothing) f false n [] (pre ʳ++ s ∷ post) c) o cl fo) })
                (subst (λ ls → step (poolG d (gh o) (deadL ls)) ≡ hushˢ) (ʳ++-defn pre) (pool-step d o (pre ʳ++ s ∷ post) fo fl (λ e → proj₂ (dd e)))))
lane-sides p c (mergeᶠ (just m)) f d n q o pre post s cl w ft _ = limited-sides p c (mergeᶠ (just m)) f d n q o pre post s (λ ()) cl w ft
lane-sides p c switchᶠ f d n q o pre post s cl w ft _ = limited-sides p c switchᶠ f d n q o pre post s (λ ()) cl w ft
lane-sides p c exhaustᶠ f d n q o pre post s cl w ft _ = limited-sides p c exhaustᶠ f d n q o pre post s (λ ()) cl w ft

-- A live lane's value passes its flatMap's retag unchanged.
lane-on : ∀ {R Γ A B} d n (q : List A) {b} {k} (a : B) {c : Ctx R Γ B} {t} → b ≡ true
        → Won (uncurry (laneT d n q) (cutT b k (shows (nx a)))) c t → Won (k , shows (nx a)) c t
lane-on d n []      a refl w = w
lane-on d n (_ ∷ _) a refl w = w

-- Up the found node's frames: each one the value reaches is clear there.
-- `s` is the node the search saw, `s′` the one the rise leaves.
won-clear : ∀ {R Γ A} p (a : A) (c : Ctx R Γ A) (s s′ : St Γ A) → alive s ≡ alive s′
          → Won (at p , shows (nx a)) c s → Frag (plug c s) → Clear p a c s′
won-clear p a top                               s s′ al w ft = tt
won-clear p a (inMap f c)                       s s′ al w ft = won-clear p (f a) c (mapS f s) (mapS f s′) refl w ft
won-clear p a (inScan f z c)                    s s′ al w ft = won-clear p (f z a) c (scanS f z s) (scanS f (f z a) s′) refl w ft
won-clear p a (inCut true x c)                  s s′ al w ft = λ _ → won-clear p a c (cutS true x s) (cutS true x s′) refl w ft
won-clear p a (inCut false x c)                 s s′ al w ft = λ ()
won-clear p a (inLn b c)                        s s′ al w ft = won-clear p a c (lnS b s) (lnS b s′) refl w ft
won-clear p a (inTake i q free c)               s s′ al w ft with q a | i
... | true  | _     = (λ _ → won-clear p a c (takeS _ q free s) (takeS _ q free s′) refl w ft) , (λ ())
... | false | true  = (λ ()) , (λ _ _ → won-clear (p ⊕ [ ix 0 ]) a c (takeS true q free s) (takeS true q (cpAt p) s′) refl w ft)
... | false | false = (λ ()) , (λ _ ())
won-clear p a (inTake i q (cpAt r) c)           s s′ al w ft = tt
won-clear p a (inTake i q (cutAt r) c)          s s′ al w ft = tt
won-clear p a (inTake i q (overAt r) c)         s s′ al w ft = tt
won-clear p a (inOuter op f d n q ls c)         s s′ al w ft = tt
won-clear p a (inLanes op f d n q o pre post c) s s′ al (l , w) ft lv =
  (λ cl → lane-sides p c op f d n q o pre post s cl l ft (frag-flat c op f d n q o (pre ʳ++ s ∷ post) ft))
  , won-clear p a c (flatS op f d n q o (pre ʳ++ s ∷ post)) (flatS op f d n q o (pre ʳ++ s′ ∷ post)) refl
      (lane-on d n q {alive s} {at p} a {c} {flatS op f d n q o (pre ʳ++ s ∷ post)} (trans al lv) w) ft
won-clear p a (inSrc kk b c)                    s s′ al (w , _) ft with over kk
... | true  = λ ()
... | false = λ _ cl → after-step (p ⊕ [ ix 0 ]) (cand (inBody kk s c) b) (step (gh b)) w (open-agrees (inBody kk s c) b cl (frag-body c kk s b ft))
won-clear p a (inBody kk o c)                   s s′ al w ft = won-clear p a c (connS kk o s) (connS kk o s′) refl w ft
