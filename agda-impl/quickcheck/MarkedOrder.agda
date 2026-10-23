{-# OPTIONS --guardedness #-}

-- SPIKE: THE ORDER, TESTED.  At every configuration the pointer-free
-- engine (`operation.MarkedPure`) reaches on a seed's program:
--
--   beyond    every key in the tree beyond `p`'s whole subtree while a
--             subscribe or a rise is at `p`
--   past      every key after `r` once absorbed at `r`
--   live      every joiner still live and untold whose source's run is an
--             end has that end after the position
--   first     a lane's value rising in its flatMap's list, its observer
--             open, is first among the flatMap's parts
--             (`spike.MarkedKept.lanes-first`, decided)
--   strict    and every other part's next event, and every tail the pool
--             holds, strictly after `p`
--   hidden    `first` again, its observer closed
--   distinct  no two keys alike
--   apart     once absorbed, no key at or under another's `at q`, short
--             of `after q`: the strengthening an inductive `beyond` needs
--
-- `beyond`, `past`, `live` and `first` are claims; the rest are probes of
-- how far the order reaches, and fail no run.  Each seed reports, per
-- check, the first configuration failing it: the mode and position, the
-- focus and its frames, and the keys at fault.
module quickcheck.MarkedOrder where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; filterᵇ; upTo; take) renaming (map to mapL)
open import Data.List.Relation.Unary.All using (lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.String using (String; intersperse) renaming (_++_ to _++ˢ_)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Events; Events∞; Pos; Label; ix; sub; last; Tail; Timeline; idle; pin; end; _<ᵖ_)
open import denotation.MonotonicList using (head; headᴼ)
open import denotation.Unfold using (NEnv; stateᴺ; states; outerᴺ)
open import operation.Key using (Key; at; after; _<ᴷ_)
open import operation.MarkedPure using (module Machine; module Driver)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
  Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody;
  Conf; ⟨_,_,_,_⟩; Mode; subscribing; absorbed; rising; nx; cp;
  Mark; ofM; attM; bodyM; srcAttM; owedM; cpM; cutM; joinM; leafM;
  own; plug; closed; alive; load)
open import spike.MarkedGhost using (gh; envAt; lane; outerG; lanesL; outerT; poolRuns; srcRun; srcG; endOf)
open import quickcheck.Code using (Prog; toObs; timeline)
open import quickcheck.Ty using (natᵗ)
open import quickcheck.Quickcheck using (program)

-- Per check, the first configuration failing it.
record Verdict : Set where
  constructor verdict
  field
    beyond past live first strict hidden distinct apart : Maybe String

private
  mutual
    keyed : ∀ {Γ A} → St Γ A → List (Mark × Key)
    keyed s = own s ++ kidKeyed s

    kidKeyed : ∀ {Γ A} → St Γ A → List (Mark × Key)
    kidKeyed (mapS f s)              = keyed s
    kidKeyed (scanS f z s)           = keyed s
    kidKeyed (cutS l a s)            = keyed s
    kidKeyed (lnS b s)               = keyed s
    kidKeyed (takeS i q w s)         = keyed s
    kidKeyed (flatS op f d n q o ls) = keyed o ++ keyedL ls
    kidKeyed (connS k o b)           = keyed o ++ keyed b
    kidKeyed _                       = []

    keyedL : ∀ {Γ A} → List (St Γ A) → List (Mark × Key)
    keyedL []       = []
    keyedL (s ∷ ls) = keyed s ++ keyedL ls

  ------------------------------------------------------------------------
  -- Showing what is at fault

  mutual
    showPos : Pos → String
    showPos ls = "[" ++ˢ intersperse "." (showLabels ls) ++ˢ "]"

    showLabels : Pos → List String
    showLabels []       = []
    showLabels (l ∷ ls) = showLabel l ∷ showLabels ls

    showLabel : Label → String
    showLabel (ix n)  = showℕ n
    showLabel (sub q) = "s" ++ˢ showPos q
    showLabel last    = "L"

  showKey : Key → String
  showKey (at p)    = "at" ++ˢ showPos p
  showKey (after p) = "after" ++ˢ showPos p

  showMark : Mark → String
  showMark ofM     = "of"
  showMark attM    = "att"
  showMark bodyM   = "body"
  showMark srcAttM = "srcAtt"
  showMark owedM   = "owed"
  showMark cpM     = "cp"
  showMark cutM    = "cut"
  showMark joinM   = "join"
  showMark leafM   = "leaf"

  showKeyed : List (Mark × Key) → String
  showKeyed mks = intersperse " " (mapL (λ { (m , k) → showMark m ++ˢ ":" ++ˢ showKey k }) (take 4 mks))

  stName : ∀ {Γ A} → St Γ A → String
  stName (pend o)          = "pend"
  stName (coldS b l)       = "cold"
  stName (ofS i p xs)      = "of"
  stName doneS             = "done"
  stName (mapS f s)        = "map"
  stName (scanS f z s)     = "scan"
  stName (cutS l a s)      = "cut"
  stName (lnS b s)         = "ln"
  stName (takeS i q w s)   = "take"
  stName (flatS _ _ _ _ _ _ _) = "flat"
  stName (connS k o b)     = "conn"
  stName (joinS j g x ib)  = "join"

  frames : ∀ {R Γ A} → Ctx R Γ A → List String
  frames top                             = []
  frames (inMap f c)                     = "map" ∷ frames c
  frames (inScan f z c)                  = "scan" ∷ frames c
  frames (inCut l a c)                   = "cut" ∷ frames c
  frames (inLn b c)                      = "ln" ∷ frames c
  frames (inTake i q w c)                = "take" ∷ frames c
  frames (inOuter _ _ _ _ _ _ c)         = "outer" ∷ frames c
  frames (inLanes _ _ _ _ _ _ _ _ c)     = "lanes" ∷ frames c
  frames (inSrc k b c)                   = "src" ∷ frames c
  frames (inBody k o c)                  = "body" ∷ frames c

  showMode : ∀ {A} → Mode A → String
  showMode subscribing  = "subscribing"
  showMode absorbed     = "absorbed"
  showMode (rising (nx a)) = "rising-nx"
  showMode (rising cp)  = "rising-cp"

  where′ : ∀ {R} → Conf R → String
  where′ ⟨ c , s , m , p ⟩ = showMode m ++ˢ " " ++ˢ showPos p ++ˢ " focus " ++ˢ stName s ++ˢ " frames " ++ˢ intersperse "<" (frames c)

  blame : ∀ {R} → Conf R → String → Maybe String
  blame x why = just (where′ x ++ˢ " :: " ++ˢ why)

  ------------------------------------------------------------------------
  -- The checks

  all : ∀ {X : Set} → (X → Bool) → List X → Bool
  all g []       = true
  all g (x ∷ xs) = g x ∧ all g xs

  told : Maybe Pos → Bool
  told (just _) = true
  told nothing  = false

  -- The untold joiners whose source's run is an end not after `p`.
  mutual
    stale : ∀ {Γ A} → Pos → NEnv Γ → St Γ A → List String
    stale p ρ (mapS f s)              = stale p ρ s
    stale p ρ (scanS f z s)           = stale p ρ s
    stale p ρ (cutS l a s)            = stale p ρ s
    stale p ρ (lnS b s)               = stale p ρ s
    stale p ρ (takeS i q w s)         = stale p ρ s
    stale p ρ (flatS op f d n q o ls) = stale p ρ o ++ staleL p ρ ls
    stale p ρ (connS k o b)           = stale p ρ o ++ stale p (srcRun (srcG k o) ρ ∷ᴬ ρ) b
    stale p ρ (joinS j true x ib)     = staleAt (lookup ρ x) (told (endOf ib))
      where
        staleAt : ∀ {X} → Events X → Bool → List String
        staleAt (end e) false = if p <ᵖ e then [] else ("joiner" ++ˢ showPos j ++ˢ " source-end" ++ˢ showPos e) ∷ []
        staleAt _       _     = []
    stale p ρ _                       = []

    staleL : ∀ {Γ A} → Pos → NEnv Γ → List (St Γ A) → List String
    staleL p ρ []       = []
    staleL p ρ (s ∷ ls) = stale p ρ s ++ staleL p ρ ls

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
  ok = verdict nothing nothing nothing nothing nothing nothing nothing nothing

  orM : Maybe String → Maybe String → Maybe String
  orM (just a) _ = just a
  orM nothing  b = b

  both : Verdict → Verdict → Verdict
  both (verdict a b c d e f g h) (verdict a′ b′ c′ d′ e′ f′ g′ h′) =
    verdict (orM a a′) (orM b b′) (orM c c′) (orM d d′) (orM e e′) (orM f f′) (orM g g′) (orM h h′)

  when : ∀ {R} → Bool → Conf R → String → Maybe String
  when true  x why = nothing
  when false x why = blame x why

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
  lanesAt : ∀ {R} → Conf R → Bool → Bool → Bool × Bool → Verdict
  lanesAt x false _     _         = ok
  lanesAt x true  false (fi , st) = verdict nothing nothing nothing (when fi x "lane not first") (when st x "a part not strictly after") nothing nothing nothing
  lanesAt x true  true  (fi , _)  = verdict nothing nothing nothing nothing nothing (when fi x "closed lane not first") nothing nothing

  laneCheck : ∀ {R} → Conf R → Verdict
  laneCheck x@(⟨ inLanes op f d n q o pre post c , s , rising (nx b) , p ⟩) = lanesAt x (alive s) (closed c) (parts f d o pre post c s p)
  laneCheck x = ok

  alike : List (Mark × Key) → List (Mark × Key)
  alike []             = []
  alike ((m , k) ∷ ks) with filterᵇ (λ { (_ , k′) → not ((k <ᴷ k′) ∨ (k′ <ᴷ k)) }) ks
  ... | []    = alike ks
  ... | hits  = (m , k) ∷ hits

  -- The keys at or under `at q`, short of `after q`.
  under : Pos → List (Mark × Key) → List (Mark × Key)
  under q = filterᵇ (λ { (_ , k′) → not (k′ <ᴷ at q) ∧ (k′ <ᴷ after q) })

  crowd : List (Mark × Key) → List (Mark × Key) → List (Mark × Key)
  crowd ks []                   = []
  crowd ks ((m , after q) ∷ ms) = crowd ks ms
  crowd ks ((m , at q) ∷ ms) with under q ks
  ... | _ ∷ _ ∷ _ = under q ks
  ... | _         = crowd ks ms

  faulty : ∀ {R} → Conf R → Maybe String → Maybe String
  faulty x nothing  = nothing
  faulty x (just w) = blame x w

  some : List (Mark × Key) → Maybe String
  some []  = nothing
  some mks = just (showKeyed mks)

  someS : List String → Maybe String
  someS [] = nothing
  someS ws = just (intersperse " " (take 3 ws))

  isAbsorbed : ∀ {A} → Mode A → Bool
  isAbsorbed absorbed = true
  isAbsorbed _        = false

  keyCheck : ∀ {R} → Conf R → Verdict
  keyCheck x@(⟨ c , s , m , p ⟩) =
    verdict (faulty x (if isAbsorbed m then nothing else some (filterᵇ (λ { (_ , k) → k <ᴷ after p }) ks)))
            (faulty x (if isAbsorbed m then some (filterᵇ (λ { (_ , k) → not (at p <ᴷ k) }) ks) else nothing))
            (faulty x (someS (stale p []ᴬ (plug c s)))) nothing nothing nothing (faulty x (some (alike ks)))
            (faulty x (if isAbsorbed m then some (crowd ks ks) else nothing))
    where
      ks = keyed (plug c s)

  check : ∀ {R} → Conf R → Verdict
  check x = both (keyCheck x) (laneCheck x)

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

-- One line per seed and failing check, claims as FAIL, probes as INFO.
orderReport : ℕ → ℕ → List String
orderReport f c = go (mapL (f +_) (upTo c))
  where
    line : String → String → ℕ → Maybe String → List String
    line tag name s nothing  = []
    line tag name s (just w) = ("order: " ++ˢ tag ++ˢ " " ++ˢ name ++ˢ " seed " ++ˢ showℕ s ++ˢ " " ++ˢ w) ∷ []

    one : ℕ → List String
    one s with order (program s)
    ... | verdict a b l fi st hi di ap =
      line "FAIL" "beyond" s a ++ line "FAIL" "past" s b ++ line "FAIL" "live" s l ++ line "FAIL" "first" s fi
        ++ line "INFO" "strict" s st ++ line "INFO" "hidden" s hi ++ line "INFO" "distinct" s di ++ line "INFO" "apart" s ap

    go : List ℕ → List String
    go []       = []
    go (s ∷ ss) = one s ++ go ss
