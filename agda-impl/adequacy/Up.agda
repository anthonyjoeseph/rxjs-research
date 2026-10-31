{-# OPTIONS --guardedness #-}

-- WHAT THE ROOT OWES RESPECTS THE ROWS: the same rows in the hole, the
-- same rows at the root, frame by frame.  A merge's lanes are matched
-- index by index, so a lane's rows replaced in its list is the same merge.
module adequacy.Up where

open import Data.Bool using (Bool; T; true; false)
open import Data.List using (List; []; _∷_; _ʳ++_; length)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos)
open import denotation.EmissionSet using (EmissionSet; out; end; Ended; module Values; module Joining; Truncate; Reach; MapT; map-out;
  map-skip; map-pin; map-end; module Connecting; module Scan; module TakeWhile)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; St; CS; free; cpAt; cutAt; overAt; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Causal using (rows-hot)
open import adequacy.Policy using (Policy; JoinP; DoneP; flatP; switchP; exhaustP; boundedP)
open import adequacy.Rows using (Echoing; TakeR; kept; Stops; stop; left; up; env; pendRows; Vis; Plus; old; new; rowsL; From; Lanes;
  Each; Kth; AllEnd; EndsOf; module Flat; module BoundedF; module SwitchF; module ExhaustF;
  _≃_; _⇄_; ≃-sym)

open _≃_

≃-refl : ∀ {A} {t : EmissionSet A} → t ≃ t
≃-refl = (λ x → x) ⇄ (λ x → x)

≃-trans : ∀ {A} {t u v : EmissionSet A} → t ≃ u → u ≃ v → t ≃ v
≃-trans a b = (λ r → to b (to a r)) ⇄ (λ r → from a (from b r))

vis-≃ : ∀ {A} {t u : EmissionSet A} → t ≃ u → Vis t ≃ Vis u
vis-≃ eq = (λ { (r , v) → to eq r , v }) ⇄ (λ { (r , v) → from eq r , v })

plus-≃ : ∀ {A} {t u : EmissionSet A} {p e} → t ≃ u → Plus t p e ≃ Plus u p e
plus-≃ eq = (λ { (old r) → old (to eq r) ; new → new }) ⇄ (λ { (old r) → old (from eq r) ; new → new })

-- Two lists of lanes, lane by lane the same rows.
data _≈ᴸ_ {B : Set} : List (EmissionSet B) → List (EmissionSet B) → Set₁ where
  []  : [] ≈ᴸ []
  _∷_ : ∀ {t u Ls Ls′} → t ≃ u → Ls ≈ᴸ Ls′ → (t ∷ Ls) ≈ᴸ (u ∷ Ls′)

≈ᴸ-sym : ∀ {B} {Ls Ls′ : List (EmissionSet B)} → Ls ≈ᴸ Ls′ → Ls′ ≈ᴸ Ls
≈ᴸ-sym []       = []
≈ᴸ-sym (e ∷ es) = ≃-sym e ∷ ≈ᴸ-sym es

≈ᴸ-refl : ∀ {B} (Ls : List (EmissionSet B)) → Ls ≈ᴸ Ls
≈ᴸ-refl []       = []
≈ᴸ-refl (_ ∷ Ls) = ≃-refl ∷ ≈ᴸ-refl Ls

ʳ++-≈ : ∀ {B} (xs : List (EmissionSet B)) {ys ys′} → ys ≈ᴸ ys′ → (xs ʳ++ ys) ≈ᴸ (xs ʳ++ ys′)
ʳ++-≈ []       h = h
ʳ++-≈ (x ∷ xs) h = ʳ++-≈ xs (≃-refl ∷ h)

any-≈ : ∀ {B} {Ls Ls′ : List (EmissionSet B)} → Ls ≈ᴸ Ls′ → ∀ {k e} → Lanes Ls k e → Lanes Ls′ k e
any-≈ (e ∷ _)  (inj₁ r) = inj₁ (to e r)
any-≈ (_ ∷ es) (inj₂ x) = inj₂ (any-≈ es x)

------------------------------------------------------------------------
-- A list with a hole: the lanes before it, nearest first, and after.

module _ {B : Set} where

  any-ʳ++ʳ : ∀ (xs : List (EmissionSet B)) {ys k e} → Lanes ys k e → Lanes (xs ʳ++ ys) k e
  any-ʳ++ʳ []       b = b
  any-ʳ++ʳ (z ∷ xs) b = any-ʳ++ʳ xs (inj₂ b)

  any-ʳ++ˡ : ∀ (xs : List (EmissionSet B)) {ys k e} → Lanes xs k e → Lanes (xs ʳ++ ys) k e
  any-ʳ++ˡ (z ∷ xs) (inj₁ r) = any-ʳ++ʳ xs (inj₁ r)
  any-ʳ++ˡ (z ∷ xs) (inj₂ a) = any-ʳ++ˡ xs a

  any-ʳ++ : ∀ (xs : List (EmissionSet B)) {ys k e} → Lanes (xs ʳ++ ys) k e → Lanes xs k e ⊎ Lanes ys k e
  any-ʳ++ []       x = inj₂ x
  any-ʳ++ (z ∷ xs) x with any-ʳ++ xs x
  ... | inj₁ a        = inj₁ (inj₂ a)
  ... | inj₂ (inj₁ r) = inj₁ (inj₁ r)
  ... | inj₂ (inj₂ b) = inj₂ b

  all-ʳ++ : ∀ {P : EmissionSet B → Set} (xs : List (EmissionSet B)) {ys} → Each P xs → Each P ys → Each P (xs ʳ++ ys)
  all-ʳ++ []       _        b = b
  all-ʳ++ (z ∷ xs) (a , as) b = all-ʳ++ xs as (a , b)

-- Fewer rows: no more before any position.
reach-⊆ : ∀ {A} {t u : EmissionSet A} → (∀ {k e} → u k e → t k e) → ∀ {q e} → Reach t q e → Reach u q e
reach-⊆ h (ks , f) = ks , λ x lt d → f (h x) lt d

trunc-≃ : ∀ {A} {t u : EmissionSet A} → t ≃ u → Truncate t ≃ Truncate u
trunc-≃ eq = (λ (r , fw) → to eq r , reach-⊆ (from eq) fw) ⇄ (λ (r , fw) → from eq r , reach-⊆ (to eq) fw)

-- Lanes given by their ends, end for end the same.
data _⇔ᴾ_ : List (Pos → Set) → List (Pos → Set) → Set₁ where
  []  : [] ⇔ᴾ []
  _∷_ : ∀ {l l′ ls ls′} → (∀ {c} → l c → l′ c) × (∀ {c} → l′ c → l c) → ls ⇔ᴾ ls′ → (l ∷ ls) ⇔ᴾ (l′ ∷ ls′)

⇔ᴾ-sym : ∀ {ls ls′} → ls ⇔ᴾ ls′ → ls′ ⇔ᴾ ls
⇔ᴾ-sym []             = []
⇔ᴾ-sym ((f , g) ∷ es) = (g , f) ∷ ⇔ᴾ-sym es

-- The same ends: the same ends, counted.
kth-⇔ : ∀ {ls ls′} {P : Pos → Set} → ls ⇔ᴾ ls′ → ∀ {k} → Kth P ls k → Kth P ls′ k
kth-⇔ []             ()
kth-⇔ ((f , _) ∷ es) {zero}  (inj₁ (c , r , pc))       = inj₁ (c , f r , pc)
kth-⇔ (_ ∷ es)       {zero}  (inj₂ K)                  = inj₂ (kth-⇔ es K)
kth-⇔ ((f , _) ∷ es) {suc k} (inj₁ ((c , r , pc) , K)) = inj₁ ((c , f r , pc) , kth-⇔ es K)
kth-⇔ (_ ∷ es)       {suc k} (inj₂ K)                  = inj₂ (kth-⇔ es K)

allEnd-⇔ : ∀ {ls ls′} {P : Pos → Set} n → ls ⇔ᴾ ls′ → AllEnd P n ls → AllEnd P n ls′
allEnd-⇔ zero    es _ = _
allEnd-⇔ (suc k) es K = kth-⇔ es K

ends-≃ : ∀ {B} {Ls Ls′ : List (EmissionSet B)} → Ls ≈ᴸ Ls′ → EndsOf Ls ⇔ᴾ EndsOf Ls′
ends-≃ []       = []
ends-≃ (e ∷ es) = (to e , from e) ∷ ends-≃ es

-- The same values and ends: all a policy reads of an outer.
record Like {A : Set} (t u : EmissionSet A) : Set where
  constructor like
  field
    outs : ∀ {q a} → t q (out a) → u q (out a)
    ends : ∀ {q} → t q end → u q end
open Like

like-≃ : ∀ {A} {t u : EmissionSet A} → t ≃ u → Like t u
like-≃ eq = like (to eq) (to eq)

ended-like : ∀ {A} {t u : EmissionSet A} {c} → Like t u → Ended t c → Ended u c
ended-like lk (c₀ , r , le) = c₀ , ends lk r , le

over-like : ∀ {A} {t u : EmissionSet A} {d c} → Like t u → T d ⊎ Ended t c → T d ⊎ Ended u c
over-like         lk (inj₁ td) = inj₁ td
over-like {c = c} lk (inj₂ x)  = inj₂ (ended-like {c = c} lk x)

nth-like : ∀ {A} {t u : EmissionSet A} {i q a} → Like t u → Like u t → Values.Nth t i q a → Values.Nth u i q a
nth-like l l⁻ (Values.first r mn)     = Values.first (outs l r) (λ y → mn (outs l⁻ y))
nth-like l l⁻ (Values.next x r lt nx) = Values.next (nth-like l l⁻ x) (outs l r) lt (λ y → nx (outs l⁻ y))

------------------------------------------------------------------------
-- A joiner's policy

-- Two policies reading their lanes, ends, runs, cuts and hand-offs alike.
record Reads {A B} (P P′ : Policy A B) : Set where
  open Policy
  field
    lane≃ : ∀ {q a} → lanes P q a ≃ lanes P′ q a
    ov→   : ∀ {c} → over P c → over P′ c
    ov←   : ∀ {c} → over P′ c → over P c
    ru→   : ∀ {q} → runs P q → runs P′ q
    ru←   : ∀ {q} → runs P′ q → runs P q
    cu→   : ∀ {q k} → cut P q k → cut P′ q k
    cu←   : ∀ {q k} → cut P′ q k → cut P q k
    ha→   : ∀ {c} → hand P c → hand P′ c
    ha←   : ∀ {c} → hand P′ c → hand P c

reads-sym : ∀ {A B} {P P′ : Policy A B} → Reads P P′ → Reads P′ P
reads-sym R = record { lane≃ = ≃-sym (lane≃ R) ; ov→ = ov← R ; ov← = ov→ R ; ru→ = ru← R ; ru← = ru→ R
                     ; cu→ = cu← R ; cu← = cu→ R ; ha→ = ha← R ; ha← = ha→ R }
  where open Reads

-- A joiner done reads only its outer's values and what its policy reads.
done-reads : ∀ {A B} {P P′ : Policy A B} → Reads P P′ → (∀ {q a} → Policy.outer P′ q (out a) → Policy.outer P q (out a))
           → ∀ {c} → DoneP P c → DoneP P′ c
done-reads R back (v , h) = ov→ R v , λ r u lt nc → let (c₀ , x , le) = h (back r) (ru← R u) lt (λ y → nc (cu→ R y)) in c₀ , to (lane≃ R) x , le
  where open Reads

-- TWO JOINERS, PART FOR PART THE SAME: the same rows.
join-→ : ∀ {A B} (P P′ : Policy A B) → Reads P P′ → Policy.outer P ≃ Policy.outer P′ → Policy.begun P ≃ Policy.begun P′
       → ∀ {k e} → JoinP P k e → JoinP P′ k e
join-→ P P′ R eo eb (Joining.val r)              = Joining.val (to eo r)
join-→ P P′ R eo eb (Joining.step r)             = Joining.step (to eo r)
join-→ P P′ R eo eb (Joining.opin r)             = Joining.opin (to eo r)
join-→ P P′ R eo eb (Joining.oend r d)           = Joining.oend (to eo r) (done-reads R (from eo) d)
join-→ P P′ R eo eb (Joining.opass r nd)         = Joining.opass (to eo r) λ d → nd (done-reads (reads-sym R) (to eo) d)
join-→ P P′ R eo eb (Joining.lane r u l nc w)    = Joining.lane (to eo r) (Reads.ru→ R u) (to (Reads.lane≃ R) l) (λ y → nc (Reads.cu← R y)) w
join-→ P P′ R eo eb (Joining.lend r u l nc nh d) = Joining.lend (to eo r) (Reads.ru→ R u) (to (Reads.lane≃ R) l) (λ y → nc (Reads.cu← R y)) (λ y → nh (Reads.ha← R y)) (done-reads R (from eo) d)
join-→ P P′ R eo eb (Joining.lpass r u l nc nh nd) = Joining.lpass (to eo r) (Reads.ru→ R u) (to (Reads.lane≃ R) l) (λ y → nc (Reads.cu← R y)) (λ y → nh (Reads.ha← R y)) λ d → nd (done-reads (reads-sym R) (to eo) d)
join-→ P P′ R eo eb (Joining.hand r u l nc h)    = Joining.hand (to eo r) (Reads.ru→ R u) (to (Reads.lane≃ R) l) (λ y → nc (Reads.cu← R y)) (Reads.ha→ R h)
join-→ P P′ R eo eb (Joining.left r u l nc i)    = Joining.left (to eo r) (Reads.ru→ R u) (to (Reads.lane≃ R) l) (λ y → nc (Reads.cu← R y)) i
join-→ P P′ R eo eb (Joining.run x w)            = Joining.run (to eb x) w
join-→ P P′ R eo eb (Joining.rend x nh d)        = Joining.rend (to eb x) (λ y → nh (Reads.ha← R y)) (done-reads R (from eo) d)
join-→ P P′ R eo eb (Joining.rpass x nh nd)      = Joining.rpass (to eb x) (λ y → nh (Reads.ha← R y)) λ d → nd (done-reads (reads-sym R) (to eo) d)
join-→ P P′ R eo eb (Joining.rhand x h)          = Joining.rhand (to eb x) (Reads.ha→ R h)

join-≃ : ∀ {A B} (P P′ : Policy A B) → Reads P P′ → Policy.outer P ≃ Policy.outer P′ → Policy.begun P ≃ Policy.begun P′ → JoinP P ≃ JoinP P′
join-≃ P P′ R eo eb = join-→ P P′ R eo eb ⇄ join-→ P′ P (reads-sym R) (≃-sym eo) (≃-sym eb)

------------------------------------------------------------------------
-- The four policies, read alike

-- Each policy, read alike from an outer with the same values and ends
-- and lanes with the same ends.
module _ {A B : Set} (L : A → Pos → EmissionSet B) (d : Bool) (n : ℕ) {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)}
         (l : Like O O′) (l⁻ : Like O′ O) (es : EndsOf Ls ⇔ᴾ EndsOf Ls′) where

  flat-over : ∀ {c} → Flat.Over L O d n Ls c → Flat.Over L O′ d n Ls′ c
  flat-over {c} (Flat.over-at g ls) = Flat.over-at (over-like {c = c} l g) (allEnd-⇔ n es ls)

  kill-like : ∀ {k} → SwitchF.Kill L O d n Ls k → SwitchF.Kill L O′ d n Ls′ k
  kill-like (q′ , a′ , r , lt) = q′ , a′ , outs l r , lt

  cut-like : ∀ {q k} → SwitchF.Cut L O d n Ls q k → SwitchF.Cut L O′ d n Ls′ q k
  cut-like (q′ , a′ , r , lt , lt′) = q′ , a′ , outs l r , lt , lt′

  switch-over : ∀ {c} → SwitchF.Over L O d n Ls c → SwitchF.Over L O′ d n Ls′ c
  switch-over {c} (g , inj₁ ls) = over-like {c = c} l g , inj₁ (allEnd-⇔ n es ls)
  switch-over {c} (g , inj₂ k)  = over-like {c = c} l g , inj₂ (kill-like k)

  exhaust-over : ∀ {c} → ExhaustF.Over L O d n Ls c → ExhaustF.Over L O′ d n Ls′ c
  exhaust-over {c} (g , ls) = over-like {c = c} l g , allEnd-⇔ n es ls

  -- Which value runs, read off values and ends alone.
  cur-like : ∀ {q w} → ExhaustF.Cur L O d n Ls q w → ExhaustF.Cur L O′ d n Ls′ q w
  cur-like (ExhaustF.cur₀ r mn fr)              = ExhaustF.cur₀ (outs l r) (λ y → mn (outs l⁻ y)) (allEnd-⇔ n es fr)
  cur-like (ExhaustF.bg₀ r mn nf)               = ExhaustF.bg₀ (outs l r) (λ y → mn (outs l⁻ y)) (λ fr → nf (allEnd-⇔ n (⇔ᴾ-sym es) fr))
  cur-like (ExhaustF.run c r ln lt r₂ lt′ nx)   = ExhaustF.run (cur-like c) (outs l r) ln lt (outs l r₂) lt′ (λ y → nx (outs l⁻ y))
  cur-like (ExhaustF.drop c r h r₂ lt nx)       = ExhaustF.drop (cur-like c) (outs l r) h (outs l r₂) lt (λ y → nx (outs l⁻ y))
  cur-like (ExhaustF.brun c fr r₂ lt nx)        = ExhaustF.brun (cur-like c) (allEnd-⇔ n es fr) (outs l r₂) lt (λ y → nx (outs l⁻ y))
  cur-like (ExhaustF.bdrop c nf r₂ lt nx)       = ExhaustF.bdrop (cur-like c) (λ fr → nf (allEnd-⇔ n (⇔ᴾ-sym es) fr)) (outs l r₂) lt (λ y → nx (outs l⁻ y))

flat-reads : ∀ {A B : Set} (L : A → Pos → EmissionSet B) d n {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → Like O O′ → Like O′ O → EndsOf Ls ⇔ᴾ EndsOf Ls′
           → Reads (flatP L O d n Ls) (flatP L O′ d n Ls′)
flat-reads L d n l l⁻ es = record { lane≃ = ≃-refl ; ov→ = λ {c} → flat-over L d n l l⁻ es {c} ; ov← = λ {c} → flat-over L d n l⁻ l (⇔ᴾ-sym es) {c}
                                  ; ru→ = λ u → u ; ru← = λ u → u ; cu→ = λ () ; cu← = λ () ; ha→ = λ () ; ha← = λ () }

switch-reads : ∀ {A B : Set} (L : A → Pos → EmissionSet B) d n {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → Like O O′ → Like O′ O → EndsOf Ls ⇔ᴾ EndsOf Ls′
             → Reads (switchP L O d n Ls) (switchP L O′ d n Ls′)
switch-reads L d n l l⁻ es = record { lane≃ = ≃-refl ; ov→ = λ {c} → switch-over L d n l l⁻ es {c} ; ov← = λ {c} → switch-over L d n l⁻ l (⇔ᴾ-sym es) {c}
                                    ; ru→ = λ u → u ; ru← = λ u → u ; cu→ = λ {q} {k} → cut-like L d n l l⁻ es {q} {k} ; cu← = λ {q} {k} → cut-like L d n l⁻ l (⇔ᴾ-sym es) {q} {k} ; ha→ = λ () ; ha← = λ () }

exhaust-reads : ∀ {A B : Set} (L : A → Pos → EmissionSet B) d n {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → Like O O′ → Like O′ O → EndsOf Ls ⇔ᴾ EndsOf Ls′
              → Reads (exhaustP L O d n Ls) (exhaustP L O′ d n Ls′)
exhaust-reads L d n l l⁻ es = record { lane≃ = ≃-refl ; ov→ = λ {c} → exhaust-over L d n l l⁻ es {c} ; ov← = λ {c} → exhaust-over L d n l⁻ l (⇔ᴾ-sym es) {c}
                                     ; ru→ = λ {q} → cur-like L d n l l⁻ es {q} ; ru← = λ {q} → cur-like L d n l⁻ l (⇔ᴾ-sym es) {q} ; cu→ = λ () ; cu← = λ () ; ha→ = λ () ; ha← = λ () }

-- A bounded merge's schedule, read off values and ends alone.
module _ {A B : Set} (m : ℕ) (L : A → Pos → EmissionSet B) (d : Bool) (n : ℕ) (Qu : List A) {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)}
         (l : Like O O′) (l⁻ : Like O′ O) where
  private
    module X = BoundedF m L O d n Qu Ls
    module Y = BoundedF m L O′ d n Qu Ls′

  item-like : ∀ {i w a} → X.Item i w a → Y.Item i w a
  item-like (X.queued x) = Y.queued x
  item-like (X.outer x)  = Y.outer (nth-like l l⁻ x)

  starts-like : ∀ {i ls ls′ w s} → ls ⇔ᴾ ls′ → X.Starts i ls w s → Y.Starts i ls′ w s
  starts-like es (X.room lt)               = Y.room lt
  starts-like es (X.freed le K)            = Y.freed le (kth-⇔ es K)
  starts-like es (X.queued le ar K₀ K₁ nK) = Y.queued le ar (kth-⇔ es K₀) (kth-⇔ es K₁) (λ K → nK (kth-⇔ (⇔ᴾ-sym es) K))

  ends-like : ∀ {i ls ls′ c} → ls ⇔ᴾ ls′ → X.Ends i ls c → Y.Ends i ls′ c
  ends-like es (w , a , s , it , st , fr) = w , a , s , item-like it , starts-like es st , fr

module _ {A B : Set} (m : ℕ) (L : A → Pos → EmissionSet B) (d : Bool) (n : ℕ) (Qu : List A) {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)}
         (l : Like O O′) (l⁻ : Like O′ O) (es : EndsOf Ls ⇔ᴾ EndsOf Ls′) where
  private
    module X = BoundedF m L O d n Qu Ls
    module Y = BoundedF m L O′ d n Qu Ls′

  sched-like : ∀ i → X.Sched i ⇔ᴾ Y.Sched i
  sched-like zero    = es
  sched-like (suc i) = ((λ x → ends-like m L d n Qu l l⁻ (sched-like i) x) , (λ y → ends-like m L d n Qu l⁻ l (⇔ᴾ-sym (sched-like i)) y)) ∷ sched-like i

  sub-like : ∀ {i w s a} → X.Sub i w s a → Y.Sub i w s a
  sub-like {i} (it , st) = item-like m L d n Qu l l⁻ it , starts-like m L d n Qu l l⁻ (sched-like i) st

  lane-like : ∀ {q a k e} → X.LaneB q a k e → Y.LaneB q a k e
  lane-like (i , s , sb , fr) = i , s , sub-like sb , fr

  queued-like : ∀ {c} → X.Queued c → Y.Queued c
  queued-like (i , w , a , sb) = i , w , a , sub-like sb

  indexed-like : ∀ {q} → X.Indexed q → Y.Indexed q
  indexed-like (i , a , it) = i , a , item-like m L d n Qu l l⁻ it

  bounded-over : ∀ {c} → X.Over c → Y.Over c
  bounded-over {c} (g , ls) = over-like {c = c} l g , allEnd-⇔ (n + length Qu) (sched-like (length Qu)) ls

  -- A queued value's lane, begun or not, read alike.
  waits-like : ∀ {i a s k e} → X.Sub i nothing s a → From L a s k e → Y.Bg k e
  waits-like sb fr = Y.waits (sub-like sb) fr

bounded-reads : ∀ {A B : Set} m (L : A → Pos → EmissionSet B) d n Qu {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → Like O O′ → Like O′ O → EndsOf Ls ⇔ᴾ EndsOf Ls′
              → Reads (boundedP m L O d n Qu Ls) (boundedP m L O′ d n Qu Ls′)
bounded-reads m L d n Qu l l⁻ es = record
  { lane≃ = λ {q} {a} → (λ {k} {e} → lane-like m L d n Qu l l⁻ es {q} {a} {k} {e}) ⇄ (λ {k} {e} → lane-like m L d n Qu l⁻ l (⇔ᴾ-sym es) {q} {a} {k} {e})
  ; ov→ = λ {c} → bounded-over m L d n Qu l l⁻ es {c} ; ov← = λ {c} → bounded-over m L d n Qu l⁻ l (⇔ᴾ-sym es) {c}
  ; ru→ = λ {q} → indexed-like m L d n Qu l l⁻ es {q} ; ru← = λ {q} → indexed-like m L d n Qu l⁻ l (⇔ᴾ-sym es) {q}
  ; cu→ = λ () ; cu← = λ ()
  ; ha→ = λ {c} → queued-like m L d n Qu l l⁻ es {c} ; ha← = λ {c} → queued-like m L d n Qu l⁻ l (⇔ᴾ-sym es) {c} }

------------------------------------------------------------------------
-- The same outer and the same lanes: the same joiner part way through.

module _ {A B : Set} (L : A → Pos → EmissionSet B) {d : Bool} {n : ℕ} where

  flat-≃ : ∀ {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′ → Flat.JoinT L O d n Ls ≃ Flat.JoinT L O′ d n Ls′
  flat-≃ {O} {O′} {Ls} {Ls′} eo es =
    join-≃ (flatP L O d n Ls) (flatP L O′ d n Ls′) (flat-reads L d n (like-≃ eo) (like-≃ (≃-sym eo)) (ends-≃ es)) eo (any-≈ es ⇄ any-≈ (≈ᴸ-sym es))

  switch-bg : ∀ {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′ → ∀ {k e} → SwitchF.Bg L O d n Ls k e → SwitchF.Bg L O′ d n Ls′ k e
  switch-bg eo es (SwitchF.bg x nk)     = SwitchF.bg (any-≈ es x) λ k → nk (kill-like L d n (like-≃ (≃-sym eo)) (like-≃ eo) (ends-≃ (≈ᴸ-sym es)) k)
  switch-bg eo es (SwitchF.bpin x nk i) = SwitchF.bpin (any-≈ es x) (λ k → nk (kill-like L d n (like-≃ (≃-sym eo)) (like-≃ eo) (ends-≃ (≈ᴸ-sym es)) k)) i

  switch-≃ : ∀ {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′ → SwitchF.RowT L O d n Ls ≃ SwitchF.RowT L O′ d n Ls′
  switch-≃ {O} {O′} {Ls} {Ls′} eo es =
    trunc-≃ (join-≃ (switchP L O d n Ls) (switchP L O′ d n Ls′) (switch-reads L d n (like-≃ eo) (like-≃ (≃-sym eo)) (ends-≃ es)) eo
                    (switch-bg eo es ⇄ switch-bg (≃-sym eo) (≈ᴸ-sym es)))

  exhaust-≃ : ∀ {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′ → ExhaustF.RowT L O d n Ls ≃ ExhaustF.RowT L O′ d n Ls′
  exhaust-≃ {O} {O′} {Ls} {Ls′} eo es =
    trunc-≃ (join-≃ (exhaustP L O d n Ls) (exhaustP L O′ d n Ls′) (exhaust-reads L d n (like-≃ eo) (like-≃ (≃-sym eo)) (ends-≃ es)) eo
                    (any-≈ es ⇄ any-≈ (≈ᴸ-sym es)))

module _ {A B : Set} (m : ℕ) (L : A → Pos → EmissionSet B) {d : Bool} {n : ℕ} {Qu : List A} where

  bounded-bg : ∀ {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′ → ∀ {k e} → BoundedF.Bg m L O d n Qu Ls k e → BoundedF.Bg m L O′ d n Qu Ls′ k e
  bounded-bg eo es (BoundedF.begun x)     = BoundedF.begun (any-≈ es x)
  bounded-bg eo es (BoundedF.waits sb fr) = waits-like m L d n Qu (like-≃ eo) (like-≃ (≃-sym eo)) (ends-≃ es) sb fr

  bounded-≃ : ∀ {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′ → BoundedF.RowT m L O d n Qu Ls ≃ BoundedF.RowT m L O′ d n Qu Ls′
  bounded-≃ {O} {O′} {Ls} {Ls′} eo es =
    trunc-≃ (join-≃ (boundedP m L O d n Qu Ls) (boundedP m L O′ d n Qu Ls′) (bounded-reads m L d n Qu (like-≃ eo) (like-≃ (≃-sym eo)) (ends-≃ es)) eo
                    (bounded-bg eo es ⇄ bounded-bg (≃-sym eo) (≈ᴸ-sym es)))

-- The same outer and the same lanes: the same merge, as entered.
row-≃ : ∀ {A B : Set} (L : A → Pos → EmissionSet B) {O O′ : EmissionSet A} {d} n {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′
      → Flat.RowT L O d n Ls ≃ Flat.RowT L O′ d n Ls′
row-≃ L n eo es = trunc-≃ (flat-≃ L {n = n} eo es)

map-≃ : ∀ {A B} (f : A → B) {t u : EmissionSet A} → t ≃ u → MapT f t ≃ MapT f u
map-≃ f eq = go (to eq) ⇄ go (from eq)
  where
    go : ∀ {t u} → (∀ {q e} → t q e → u q e) → ∀ {q e} → MapT f t q e → MapT f u q e
    go h (map-out r)  = map-out (h r)
    go h (map-skip r) = map-skip (h r)
    go h (map-pin r)  = map-pin (h r)
    go h (map-end r)  = map-end (h r)

-- The same rows taken: the same rows kept.
take-≃ : ∀ {A} i (q : A → Bool) w {t u : EmissionSet A} → t ≃ u → TakeR i q w t ≃ TakeR i q w u
take-≃ {A} i q free     eq = trunc-≃ (go (to eq) (from eq) ⇄ go (from eq) (to eq))
  where
    go : ∀ {t u : EmissionSet A} → (∀ {k e} → t k e → u k e) → (∀ {k e} → u k e → t k e) → ∀ {k e} → TakeWhile.TakeT i q t k e → TakeWhile.TakeT i q u k e
    go h h⁻ (TakeWhile.pass r k nf)   = TakeWhile.pass (h r) k λ (k′ , a , x , y , z) → nf (k′ , a , h⁻ x , y , z)
    go h h⁻ (TakeWhile.fail r k nf j) = TakeWhile.fail (h r) k (λ (k′ , a , x , y , z) → nf (k′ , a , h⁻ x , y , z)) j
    go h h⁻ (TakeWhile.stop r k nf)   = TakeWhile.stop (h r) k λ (k′ , a , x , y , z) → nf (k′ , a , h⁻ x , y , z)
    go h h⁻ (TakeWhile.step r nf)     = TakeWhile.step (h r) λ (k′ , a , x , y , z) → nf (k′ , a , h⁻ x , y , z)
    go h h⁻ (TakeWhile.tend r nf)     = TakeWhile.tend (h r) λ (k′ , a , x , y , z) → nf (k′ , a , h⁻ x , y , z)
    go h h⁻ (TakeWhile.left r nf j)   = TakeWhile.left (h r) (λ (k′ , a , x , y , z) → nf (k′ , a , h⁻ x , y , z)) j
take-≃ i q (cpAt p)   eq = go (to eq) ⇄ go (from eq)
  where
    go : ∀ {A} {t u : EmissionSet A} → (∀ {k e} → t k e → u k e) → ∀ {k e} → Stops p t k e → Stops p u k e
    go h stop                = stop
    go h (left (kept r n j)) = left (kept (h r) n j)
take-≃ i q (cutAt p)  eq = (λ { (kept r n j) → kept (to eq r) n j }) ⇄ λ { (kept r n j) → kept (from eq r) n j }
take-≃ i q (overAt p) eq = (λ { (kept r n j) → kept (to eq r) n j }) ⇄ λ { (kept r n j) → kept (from eq r) n j }

-- The same rows scanned: the same folds.
scan-≃ : ∀ {A B} (f : B → A → B) z {t u : EmissionSet A} → t ≃ u → Scan.ScanT f z t ≃ Scan.ScanT f z u
scan-≃ {A} {B} f z eq = go (to eq) (from eq) ⇄ go (from eq) (to eq)
  where
    acc : ∀ {t u : EmissionSet A} → (∀ {q e} → t q e → u q e) → (∀ {q e} → u q e → t q e) → ∀ {q b} → Scan.Acc f z t q b → Scan.Acc f z u q b
    acc h h⁻ (Scan.acc₀ r mn)     = Scan.acc₀ (h r) (λ y → mn (h⁻ y))
    acc h h⁻ (Scan.acc a r lt nx) = Scan.acc (acc h h⁻ a) (h r) lt (λ y → nx (h⁻ y))
    go : ∀ {t u : EmissionSet A} → (∀ {q e} → t q e → u q e) → (∀ {q e} → u q e → t q e) → ∀ {q e} → Scan.ScanT f z t q e → Scan.ScanT f z u q e
    go h h⁻ (Scan.sval a)  = Scan.sval (acc h h⁻ a)
    go h h⁻ (Scan.sstep r) = Scan.sstep (h r)
    go h h⁻ (Scan.spin r)  = Scan.spin (h r)
    go h h⁻ (Scan.send r)  = Scan.send (h r)

-- The same source and the same body: the same connect.
conn-≃ : ∀ {A B : Set} r {σ σ′ : EmissionSet A} {β β′ : EmissionSet B} → σ ≃ σ′ → β ≃ β′ → Connecting.ConnT r σ β ≃ Connecting.ConnT r σ′ β′
conn-≃ {A} {B} r es eb = go es eb ⇄ go (≃-sym es) (≃-sym eb)
  where
    go : ∀ {σ σ′ : EmissionSet A} {β β′ : EmissionSet B} → σ ≃ σ′ → β ≃ β′ → ∀ {q e} → Connecting.ConnT r σ β q e → Connecting.ConnT r σ′ β′ q e
    go es eb (Connecting.body x)           = Connecting.body (to eb x)
    go es eb (Connecting.burst x i)        = Connecting.burst (to es x) i
    go es eb (Connecting.echo x al u ni)   = Connecting.echo (to es x) (λ y → al (from eb y)) u ni
    go es eb (Connecting.kept x al ni i)   = Connecting.kept (to es x) (λ y → al (from eb y)) ni i

-- The same source: the same echoes.
echo-≃ : ∀ {Γ A} (k : CS Γ A) {t u : EmissionSet A} → t ≃ u → Echoing k t ≃ Echoing k u
echo-≃ k eq = (λ { (x , g) → to eq x , g }) ⇄ (λ { (x , g) → from eq x , g })

-- THE CONGRUENCE.
up-≃ : ∀ {R Γ A} (c : Ctx R Γ A) {t u : EmissionSet A} → t ≃ u → up c t ≃ up c u
up-≃ top                                              eq = eq
up-≃ (inMap f c)                                      eq = up-≃ c (map-≃ f eq)
up-≃ (inScan f z c)                                   eq = up-≃ c (scan-≃ f z eq)
up-≃ (inCut true a c)                                 eq = up-≃ c eq
up-≃ (inCut false a c)                                eq = ≃-refl
up-≃ (inLn true c)                                    eq = up-≃ c eq
up-≃ (inLn false c)                                   eq = ≃-refl
up-≃ (inTake i q w c)                                 eq = up-≃ c (take-≃ i q w eq)
up-≃ (inOuter (mergeᶠ nothing) f d n q ls c)          eq = up-≃ c (row-≃ (λ a → pendRows (env c) (f a)) n eq (≈ᴸ-refl (rowsL (env c) ls)))
up-≃ (inOuter (mergeᶠ (just m)) f d n q ls c)         eq = up-≃ c (bounded-≃ m (λ a → pendRows (env c) (f a)) eq (≈ᴸ-refl (rowsL (env c) ls)))
up-≃ (inOuter switchᶠ f d n q ls c)                   eq = up-≃ c (switch-≃ (λ a → pendRows (env c) (f a)) eq (≈ᴸ-refl (rowsL (env c) ls)))
up-≃ (inOuter exhaustᶠ f d n q ls c)                  eq = up-≃ c (exhaust-≃ (λ a → pendRows (env c) (f a)) eq (≈ᴸ-refl (rowsL (env c) ls)))
up-≃ (inLanes (mergeᶠ nothing) f d n q o pre post c)  eq = up-≃ c (row-≃ (λ a → pendRows (env c) (f a)) n ≃-refl (ʳ++-≈ (rowsL (env c) pre) (eq ∷ ≈ᴸ-refl (rowsL (env c) post))))
up-≃ (inLanes (mergeᶠ (just m)) f d n q o pre post c) eq = up-≃ c (bounded-≃ m (λ a → pendRows (env c) (f a)) ≃-refl (ʳ++-≈ (rowsL (env c) pre) (eq ∷ ≈ᴸ-refl (rowsL (env c) post))))
up-≃ (inLanes switchᶠ f d n q o pre post c)           eq = up-≃ c (switch-≃ (λ a → pendRows (env c) (f a)) ≃-refl (ʳ++-≈ (rowsL (env c) pre) (eq ∷ ≈ᴸ-refl (rowsL (env c) post))))
up-≃ (inLanes exhaustᶠ f d n q o pre post c)          eq = up-≃ c (exhaust-≃ (λ a → pendRows (env c) (f a)) ≃-refl (ʳ++-≈ (rowsL (env c) pre) (eq ∷ ≈ᴸ-refl (rowsL (env c) post))))
up-≃ (inSrc k b c)                                    eq = up-≃ c (conn-≃ _ (echo-≃ k eq) (rows-hot k (env c) b eq))
up-≃ (inBody k o c)                                   eq = up-≃ c (conn-≃ _ ≃-refl eq)
