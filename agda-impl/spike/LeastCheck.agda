{-# OPTIONS --guardedness --large-indices #-}

-- SPIKE 6's EVIDENCE for its one new leaf, `named`: at every quiet
-- configuration of spike 5's programs, every entry a feed still owes at a
-- joiner's path names that joiner's join position, and an owed end is
-- the binder's one end, made after it joined.  Checked by `refl`; `owes`
-- marks the programs where some entry was checked, so the pass is not
-- vacuous there.
module spike.LeastCheck where

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Pos; _≟ᵖ_; _<ᵖ_)
open import spike.StateTree3 using (PObs; Ev; nx; cp; CS; St; joinS; mapS; scanS; cutS; lnS; takeS; flatS; connS;
  Conf; ⟨_,_,_,_,_⟩; Shown; load; plug)
open import spike.StateTree3Ghost using (_≟ᴸ_; jobsAt; feedingsAt; attached; focusing; Level; Bind; bind; zipF; endedAt; Book; book; quiets)
open import spike.GhostCheck using (p1; p2; lanes; p6; p7; p8; p9; p10; p11; p12; p13)

endsᵇ : ∀ {X} → Ev X → Pos → Pos → Pos → Bool
endsᵇ (nx _) j c p = true
endsᵇ cp     j c p = (j <ᵖ p) ∧ does (c ≟ᵖ p)

-- Each entry at `π`: its join position is `j`, its end after it; and how
-- many entries were checked.
both : Bool × ℕ → Bool × ℕ → Bool × ℕ
both (a , m) (b , n) = a ∧ b , m + n

one : Bool → Bool × ℕ
one b = b , 1

namedL : ∀ {X} → List ℕ → Pos → Pos → Level X → Bool × ℕ
namedL π j c (e , p , [])              = true , 0
namedL π j c (e , p , ((q , j′) ∷ js)) =
  both (if π ≟ᴸ q then one (does (j′ ≟ᵖ j) ∧ endsᵇ e j c p) else (true , 0)) (namedL π j c (e , p , js))

namedLs : ∀ {X} → List ℕ → Pos → Pos → List (Level X) → Bool × ℕ
namedLs π j c []       = true , 0
namedLs π j c (l ∷ ls) = both (namedL π j c l) (namedLs π j c ls)

named : ∀ {X} → List ℕ → Pos → Bind X → Bool × ℕ
named π j (bind c ls) = namedLs π j (endedAt ls) ls

mutual
  nm : ∀ {Γ A} → Book → List ℕ → All Bind Γ → St Γ A → Bool × ℕ
  nm b π β (joinS j true x)      = named π j (lookup β x)
  nm b π β (mapS f s)            = nm b (π ++ [ 0 ]) β s
  nm b π β (scanS f z s)         = nm b (π ++ [ 0 ]) β s
  nm b π β (cutS l a s)          = nm b (π ++ [ 0 ]) β s
  nm b π β (lnS l s)             = nm b (π ++ [ 0 ]) β s
  nm b π β (takeS i q s)         = nm b (π ++ [ 0 ]) β s
  nm b π β (flatS op f d n o ls) = both (nm b (π ++ [ 0 ]) β o) (nmL b π 0 β ls)
  nm b π β (connS k o bd)        =
    both (nm b (π ++ [ 0 ]) β o) (nm b (π ++ [ 1 ]) (bind (CS.closed k) (zipF (CS.feeds k) (feedingsAt (jobsAt π (Book.rets b)))) ∷ᴬ β) bd)
  nm b π β _                     = true , 0

  nmL : ∀ {Γ B} → Book → List ℕ → ℕ → All Bind Γ → List (St Γ B) → Bool × ℕ
  nmL b π i β []                           = true , 0
  nmL b π i β (lnS l (cutS true a s) ∷ ls) = both (nm b (π ++ [ suc i ] ++ [ 0 ] ++ [ 0 ]) β s) (nmL b π (suc i) β ls)
  nmL b π i β (_ ∷ ls)                     = nmL b π (suc i) β ls

nmTop : ∀ {R} → Conf R → Bool × ℕ
nmTop ⟨ c , s , m , p , rs ⟩ = nm (book rs (focusing c m p ++ attached rs)) [] []ᴬ (plug c s)

-- Over every quiet configuration of a run: the configurations that fail,
-- and the entries checked.
tally : Bool × ℕ → ℕ × ℕ → ℕ × ℕ
tally (true  , n) (f , m) = f , n + m
tally (false , n) (f , m) = suc f , n + m

run : PObs [] ℕ → ℕ × ℕ
run o = go (quiets 3000 (load o) [])
  where
    go : List (Shown ℕ × Conf ℕ) → ℕ × ℕ
    go []             = 0 , 0
    go ((_ , k) ∷ ks) = tally (nmTop k) (go ks)

-- No configuration fails; `owes` also asks that some entry was checked.
cleanᵗ : ℕ × ℕ → Bool
cleanᵗ (0 , _) = true
cleanᵗ _       = false

owesᵗ : ℕ × ℕ → Bool
owesᵗ (0 , suc _) = true
owesᵗ _           = false

clean : PObs [] ℕ → Bool
clean o = cleanᵗ (run o)

owes : PObs [] ℕ → Bool
owes o = owesᵗ (run o)

c1 : clean p1 ≡ true
c1 = refl
c2 : clean p2 ≡ true
c2 = refl
c3 : owes (lanes (mergeᶠ nothing)) ≡ true
c3 = refl
c4 : clean (lanes switchᶠ) ≡ true
c4 = refl
c5 : clean (lanes exhaustᶠ) ≡ true
c5 = refl
c6 : clean p6 ≡ true
c6 = refl
c7 : owes p7 ≡ true
c7 = refl
c8 : clean p8 ≡ true
c8 = refl
c9 : owes p9 ≡ true
c9 = refl
c10 : clean p10 ≡ true
c10 = refl
c11 : owes p11 ≡ true
c11 = refl
c12 : owes p12 ≡ true
c12 = refl
c13 : owes p13 ≡ true
c13 = refl
