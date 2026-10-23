{-# OPTIONS --guardedness #-}

-- SPIKE: THE ORDER, TESTED.  At every configuration the pointer-free
-- engine (`operation.MarkedPure`) reaches on a seed's program:
--
--   fresh   every key in the tree beyond `p`'s whole subtree while a
--           subscribe or a rise is at `p`; after `r`, no two alike,
--           once absorbed at `r`
--   first   a lane's value rising in its flatMap's list, its observer
--           open, is first among the flatMap's parts
--           (`spike.MarkedKept.lanes-first`, decided)
--   strict  and every other part's next event, and every tail the pool
--           holds, strictly after `p`
--   hidden  `first` again, its observer closed
--   live    every joiner still live whose source has ended holds that
--           completion in its inbox
--
-- `fresh`, `first` and `live` are claims; `strict` and `hidden` are
-- probes of how far the order reaches, and fail no run.
module quickcheck.MarkedOrder where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.List using (List; []; _∷_; _++_; filterᵇ; upTo) renaming (map to mapL)
open import Data.List.Relation.Unary.All using (lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_; proj₂)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Events; Events∞; Pos; Tail; Timeline; idle; pin; end; _<ᵖ_)
open import denotation.MonotonicList using (head; headᴼ)
open import denotation.Unfold using (NEnv; stateᴺ; states; outerᴺ)
open import operation.Key using (Key; at; after; _<ᴷ_)
open import operation.MarkedPure using (module Machine; module Driver)
open Machine using (St; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; Ctx; inLanes; Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising; nx;
  own; plug; closed; alive; load)
open import spike.MarkedGhost using (gh; envAt; lane; outerG; lanesL; outerT; poolRuns; srcRun; srcG; endOf)
open import quickcheck.Code using (Prog; toObs; timeline)
open import quickcheck.Ty using (natᵗ)
open import quickcheck.Quickcheck using (program)

record Verdict : Set where
  constructor verdict
  field
    fresh first strict hidden live : Bool

private
  mutual
    keys : ∀ {Γ A} → St Γ A → List Key
    keys s = mapL proj₂ (own s) ++ kidKeys s

    kidKeys : ∀ {Γ A} → St Γ A → List Key
    kidKeys (mapS f s)              = keys s
    kidKeys (scanS f z s)           = keys s
    kidKeys (cutS l a s)            = keys s
    kidKeys (lnS b s)               = keys s
    kidKeys (takeS i q w s)         = keys s
    kidKeys (flatS op f d n q o ls) = keys o ++ keysL ls
    kidKeys (connS k o b)           = keys o ++ keys b
    kidKeys _                       = []

    keysL : ∀ {Γ A} → List (St Γ A) → List Key
    keysL []       = []
    keysL (s ∷ ls) = keys s ++ keysL ls

  all : ∀ {X : Set} → (X → Bool) → List X → Bool
  all g []       = true
  all g (x ∷ xs) = g x ∧ all g xs

  isEnd : ∀ {X} → Events X → Bool
  isEnd (end _) = true
  isEnd _       = false

  told : Maybe Pos → Bool
  told (just _) = true
  told nothing  = false

  mutual
    live? : ∀ {Γ A} → NEnv Γ → St Γ A → Bool
    live? ρ (mapS f s)              = live? ρ s
    live? ρ (scanS f z s)           = live? ρ s
    live? ρ (cutS l a s)            = live? ρ s
    live? ρ (lnS b s)               = live? ρ s
    live? ρ (takeS i q w s)         = live? ρ s
    live? ρ (flatS op f d n q o ls) = live? ρ o ∧ livesL ρ ls
    live? ρ (connS k o b)           = live? ρ o ∧ live? (srcRun (srcG k o) ρ ∷ᴬ ρ) b
    live? ρ (joinS j true x ib)     = not (isEnd (lookup ρ x)) ∨ told (endOf ib)
    live? ρ _                       = true

    livesL : ∀ {Γ A} → NEnv Γ → List (St Γ A) → Bool
    livesL ρ []       = true
    livesL ρ (s ∷ ls) = live? ρ s ∧ livesL ρ ls

  notBefore later : Pos → Maybe Pos → Bool
  notBefore p nothing  = true
  notBefore p (just h) = not (h <ᵖ p)
  later p nothing  = true
  later p (just h) = p <ᵖ h

  tailNotBefore tailAfter : Pos → Tail → Bool
  tailNotBefore p idle      = true
  tailNotBefore p (pin k u) = not (k <ᵖ p)
  tailAfter p idle      = true
  tailAfter p (pin k u) = p <ᵖ k

  hd : ∀ {B} → Events∞ B → Maybe Pos
  hd h = head (Events∞.force h)

  ok : Verdict
  ok = verdict true true true true true

  both : Verdict → Verdict → Verdict
  both (verdict a b c d e) (verdict a′ b′ c′ d′ e′) = verdict (a ∧ a′) (b ∧ b′) (c ∧ c′) (d ∧ d′) (e ∧ e′)

  -- The flatMap's parts around a lane rising at `p`.
  parts : ∀ {R Γ A B} (f : A → Obs Timeline Γ B) → Bool → St Γ A → (pre post : List (St Γ B)) → Ctx R Γ B → St Γ B → Pos → Bool × Bool
  parts f d o pre post c s p =
      (all (λ l → notBefore p (hd l)) Ls ∧ all (λ l → later p (hd l)) Rs ∧ notBefore p (headᴼ O) ∧ tailNotBefore p T)
    , (all (λ l → later p (hd l)) Ls ∧ all (λ l → later p (hd l)) Rs ∧ later p (headᴼ O) ∧ tailAfter p T)
    where
      ρ  = envAt c
      O  = outerᴺ (lane f) (outerG d (gh o)) ρ
      Ls = states (lanesL post) ρ
      Rs = states (lanesL pre) ρ
      T  = outerT d (gh o) ρ (poolRuns pre post true ρ (stateᴺ (gh s) ρ))

  -- A lane out of the list is absorbed; one under a closed observer is
  -- only probed.
  lanesAt : Bool → Bool → Bool × Bool → Verdict
  lanesAt false _     _        = ok
  lanesAt true  false (fi , st) = verdict true fi st true true
  lanesAt true  true  (fi , _)  = verdict true true true fi true

  laneCheck : ∀ {R} → Conf R → Verdict
  laneCheck ⟨ inLanes op f d n q o pre post c , s , rising (nx b) , p ⟩ = lanesAt (alive s) (closed c) (parts f d o pre post c s p)
  laneCheck x = ok

  distinct : List Key → Bool
  distinct []       = true
  distinct (k ∷ ks) = all (λ k′ → (k <ᴷ k′) ∨ (k′ <ᴷ k)) ks ∧ distinct ks

  beyond : Pos → List Key → Bool
  beyond p = all (λ k → not (k <ᴷ after p))

  freshCheck : ∀ {R} → Conf R → Bool
  freshCheck ⟨ c , s , subscribing , p ⟩ = beyond p (keys (plug c s)) ∧ distinct (keys (plug c s))
  freshCheck ⟨ c , s , rising e , p ⟩    = beyond p (keys (plug c s)) ∧ distinct (keys (plug c s))
  freshCheck ⟨ c , s , absorbed , r ⟩    = all (λ k → at r <ᴷ k) (keys (plug c s)) ∧ distinct (keys (plug c s))

  check : ∀ {R} → Conf R → Verdict
  liveCheck : ∀ {R} → Conf R → Bool
  liveCheck ⟨ c , s , m , p ⟩ = live? []ᴬ (plug c s)

  check x = both (verdict (freshCheck x) true true true (liveCheck x)) (laneCheck x)

  open Driver ℕ using (step; silent; value; complete; drained)

  walk : ℕ → Conf ℕ → Verdict
  walk zero    x = check x
  walk (suc n) x with step x
  ... | silent t x′    = both (check x) (walk n x′)
  ... | value t p a x′ = both (check x) (walk n x′)
  ... | complete p     = check x
  ... | drained        = check x

budget : ℕ
budget = 4000

order : Prog natᵗ → Verdict
order p = walk budget (load (toObs timeline 3 p []ᴬ []ᴬ []ᴬ))

-- The seeds from f on which each check fails: fresh, first, live, strict,
-- hidden.
orderFails : ℕ → ℕ → List ℕ × List ℕ × List ℕ × List ℕ × List ℕ
orderFails f c = fails Verdict.fresh , fails Verdict.first , fails Verdict.live , fails Verdict.strict , fails Verdict.hidden
  where
    seeds = mapL (f +_) (upTo c)
    fails : (Verdict → Bool) → List ℕ
    fails g = filterᵇ (λ s → not (g (order (program s)))) seeds
