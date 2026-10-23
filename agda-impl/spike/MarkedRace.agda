{-# OPTIONS --guardedness #-}

-- SPIKE: A LANE FIRST.  When the lane a value rises from comes first
-- among a merge's parts, the merge shows that value next and runs on
-- with the lane's rest in its place (`go-rise`).  First means: no lane
-- before it in the list earlier, none after it as early (`M′.earliest`
-- breaks a tie toward the later lane), the outer no earlier, and what
-- ended parts left no earlier.
module spike.MarkedRace where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Bool.Properties using (∧-zeroʳ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Tree using (FlatOp)
open import denotation.MonotonicList.Events using (Events; Events∞; Pos; Tail; idle; pin; out; _∪_; _<ᵖ_)
open import denotation.MonotonicList using (MonotonicList; head; headᴼ; Earliest; none; found; earliest; clear; clears; cuts; go; parts; race; lane)

open Events∞

-- Nothing at `h` comes before `p`.
NotBefore : Pos → Maybe Pos → Set
NotBefore p nothing  = ⊤
NotBefore p (just h) = h <ᵖ p ≡ false

-- Whatever is at `h` comes after `p`.
After : Pos → Maybe Pos → Set
After p nothing  = ⊤
After p (just h) = p <ᵖ h ≡ true

TailNotBefore : Pos → Tail → Set
TailNotBefore p idle      = ⊤
TailNotBefore p (pin k u) = k <ᵖ p ≡ false

-- A lane at `p` first among the parts around it.
record First {B} (p : Pos) (o : Maybe (Events∞ (MonotonicList B))) (ls rs : List (Events∞ B)) (t : Tail) : Set where
  constructor first
  field
    before : All (λ l → NotBefore p (head (force l))) ls
    after  : All (λ l → After p (head (force l))) rs
    outerN : NotBefore p (headᴼ o)
    tailN  : TailNotBefore p t

private
  EarliestAfter : ∀ {B} → Pos → Earliest B → Set
  EarliestAfter p none              = ⊤
  EarliestAfter p (found k bs c as) = p <ᵖ k ≡ true

  earliest-after : ∀ {B} p (ls : List (Events∞ B)) → All (λ l → After p (head (force l))) ls → EarliestAfter p (earliest ls)
  earliest-after p []       []       = tt
  earliest-after p (l ∷ ls) (a ∷ as) with head (force l) | a | earliest ls | earliest-after p ls as
  ... | nothing | _  | none              | _ = tt
  ... | nothing | _  | found k bs c as′  | e = e
  ... | just k  | a′ | none              | _ = a′
  ... | just k  | a′ | found k′ bs c as′ | e with k <ᵖ k′
  ...   | true  = a′
  ...   | false = e

  earliest-hole : ∀ {B} p (ls : List (Events∞ B)) (h : Events∞ B) rs {b r} → force h ≡ out p b r
                → All (λ l → NotBefore p (head (force l))) ls → All (λ l → After p (head (force l))) rs
                → earliest (ls ++ h ∷ rs) ≡ found p ls h rs
  earliest-hole p [] h rs e [] as rewrite e with earliest rs | earliest-after p rs as
  ... | none             | _  = refl
  ... | found k bs c as′ | a rewrite a = refl
  earliest-hole p (l ∷ ls) h rs e (n ∷ ns) as rewrite earliest-hole p ls h rs e ns as with head (force l) | n
  ... | nothing | _  = refl
  ... | just k  | n′ rewrite n′ = refl

  clears-hole : ∀ {B} k p (ls : List (Events∞ B)) (h : Events∞ B) rs {b r} → force h ≡ out p b r → k <ᵖ p ≡ false
              → clears k (ls ++ h ∷ rs) ≡ false
  clears-hole k p []       h rs e n rewrite e | n = refl
  clears-hole k p (l ∷ ls) h rs e n rewrite clears-hole k p ls h rs e n = ∧-zeroʳ (clear k (head (force l)))

  race-rise : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) p ls (h : Events∞ B) rs qs t → NotBefore p (headᴼ o)
            → race op o p ls h rs qs t ≡ lane op o ls h rs qs t (force h)
  race-rise op nothing  p ls h rs qs t on = refl
  race-rise op (just e) p ls h rs qs t on with head (force e) | on
  ... | nothing | _ = refl
  ... | just k′ | n rewrite n = refl

  parts-rise : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls (h : Events∞ B) rs qs t {p b r} → force h ≡ out p b r
             → All (λ l → NotBefore p (head (force l))) ls → All (λ l → After p (head (force l))) rs → NotBefore p (headᴼ o)
             → parts op o (ls ++ h ∷ rs) qs t ≡ lane op o ls h rs qs t (force h)
  parts-rise op o ls h rs qs t {p} e ns as on rewrite earliest-hole p ls h rs e ns as = race-rise op o p ls h rs qs t on

-- THE LANE FIRST: the merge's next is the lane's value.
go-rise : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls (h : Events∞ B) rs qs t {p b r} → force h ≡ out p b r
        → First p o ls rs t → go op o (ls ++ h ∷ rs) qs t ≡ lane op o ls h rs qs t (force h)
go-rise op o ls h rs qs idle      e (first ns as on tn) = parts-rise op o ls h rs qs idle e ns as on
go-rise op o ls h rs qs (pin k u) {p} e (first ns as on tn)
  rewrite clears-hole k p ls h rs e tn | ∧-zeroʳ (clear k (headᴼ o)) = parts-rise op o ls h rs qs (pin k u) e ns as on

-- A lane's tail is all a merge's tail reads of it.
cuts-swap : ∀ {B} (ls : List (Events∞ B)) (h h′ : Events∞ B) rs → cut h ≡ cut h′ → cuts (ls ++ h ∷ rs) ≡ cuts (ls ++ h′ ∷ rs)
cuts-swap []       h h′ rs e = cong (_∪ cuts rs) e
cuts-swap (l ∷ ls) h h′ rs e = cong (cut l ∪_) (cuts-swap ls h h′ rs e)
