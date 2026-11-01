{-# OPTIONS --guardedness #-}

-- THE FROZEN ENTRY AND THE CURSOR, PROBED: does every live node owe
-- exactly its entry past one global cursor?  The pure semantics runs each
-- generated program.  A node's ENTRY is its own program listed where it is
-- subscribed, its binders read whole; only its visible rows (values and
-- its end) are kept.  A node DELIVERS a row when it rises to its parent.
-- The CURSOR is the latest position any node has delivered.
--
-- Checked at every step:
--   * a delivered row is one of its node's entry rows, past every row the
--     node delivered before;
--   * no delivery lies before the cursor: the cursor never runs back;
--   * at every settled step (absorbed or subscribing), every live node has
--     delivered each entry row at or before the cursor;
--   * once the run drains, every live node has delivered its whole entry.
-- A node is live while nothing on its path is switched off, a lane
-- finished, a cold stopped, a joiner done, or a connect's source torn down.
--
-- Also reported, never failed: a silent step whose clock (the least mark
-- due once absorbed, else the run's position; `adequacy.Complete.Clock`)
-- is earlier than the step before's, the shape `clock-mono` denies.  A
-- fall is reported only when the root shows a row after it, as
-- `clock-mono`'s premise asks; one with no row after is only counted.
--
-- A node is named by its path of child indices, as `quickcheck.Entry-Check`
-- names it.  An entry cut short by a budget is skipped.  A probe for
-- `make cursor-check`: no proof reads it.
module quickcheck.Cursor-Check where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (tt) renaming (⊤ to Unit)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; upTo; null; length; take) renaming (map to mapL)
open import Data.List.Relation.Unary.All using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_; _<ᵇ_; _≤ᵇ_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String) renaming (_++_ to _+++_)
open import Data.String.Properties using (_==_)
open import IO.Primitive.Core using (_>>=_; pure)
open import IO.Primitive.Finite using (putStrLn)
open import Relation.Nullary using (does)

open import Tree using (Obs; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Events using (Pos; Timeline; ix; last; _<ᵖ_; _≟ᵖ_)
open import operation.Key using (Key; at; after; _<ᴷ_)
open import operation.PureObservable using (module Machine; module Driver)
open Machine using (St; Ev; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; pend; CS; Scope;
                    Conf; ⟨_,_,_,_⟩; plug; dirs; scopeOf; subscribing; absorbed; rising; load; nx; cp;
                    Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody;
                    attAt; attached; free; cpAt; cutAt; overAt; search; found; Found; own;
                    Mark; ofM; attM; bodyM; srcAttM; owedM; cpM; cutM; joinM; leafM)
open import adequacy.Weight using (W; prefixes)
open import quickcheck.Code using (toObs; timeline; showCode)
open import quickcheck.Trace using (depth)
open import quickcheck.Quickcheck using (program)
open import quickcheck.Ty using (showPos; natᵗ)
open import quickcheck.Tabled using (rows; short; concatMap; when; anyᵇ; listT)
open import quickcheck.Entry-Check using (Kind; kout; kend; erase; sameRow; showRows; fullL; samePath; showPath)

------------------------------------------------------------------------
-- Each node's entry, and what it has delivered

record Seen : Set where
  constructor seen
  field
    path   : List ℕ
    former : String
    entry  : Maybe (List (Pos × Kind))
    got    : List (Pos × Kind)

private
  visible : List (Pos × Kind) → List (Pos × Kind)
  visible = concatMap λ { (q , kout) → [ q , kout ] ; (q , kend) → [ q , kend ] ; _ → [] }

  formerOf : ∀ {Γ A} → Obs Timeline Γ A → String
  formerOf (cold _)          = "cold"
  formerOf empty             = "empty"
  formerOf (of _)            = "of"
  formerOf (map _ _)         = "map"
  formerOf (scan _ _ _)      = "scan"
  formerOf (takeWhile _ _ _) = "take"
  formerOf (flatMap _ _ _)   = "flatMap"
  formerOf (connect _ _)     = "connect"
  formerOf (connected _)     = "join"
  formerOf (defer _)         = "defer"

  -- A node's entry: its program listed where it is subscribed, its
  -- binders read whole, visible rows only; nothing when cut short.
  entryOf : ∀ {Γ A} → ℕ → Scope Γ → Obs Timeline Γ A → Pos → Maybe (List (Pos × Kind))
  entryOf u sc o q with fullL u sc
  ... | nothing = nothing
  ... | just φ with listT u o φ q
  ...   | nothing = nothing
  ...   | just l  = if short l then nothing else just (visible (mapL erase (rows l)))

  known : List ℕ → List Seen → Maybe Seen
  known π []       = nothing
  known π (s ∷ ss) = if samePath π (Seen.path s) then just s else known π ss

  deliver : List ℕ → Pos × Kind → List Seen → List Seen
  deliver π r []       = []
  deliver π r (s ∷ ss) = if samePath π (Seen.path s) then record s { got = r ∷ Seen.got s } ∷ ss else s ∷ deliver π r ss

  kindOf : ∀ {A} → Ev A → Kind
  kindOf (nx _) = kout
  kindOf cp     = kend

  prefix : List ℕ → List ℕ → Bool
  prefix []       _        = true
  prefix (i ∷ is) (j ∷ js) = (i ≡ᵇ j) ∧ prefix is js
  prefix _        []       = false

  -- The roots of every subtree the run has torn down or finished.
  mutual
    deadS : ∀ {Γ A} → List ℕ → St Γ A → List (List ℕ)
    deadS π (coldS false _)        = [ π ]
    deadS π (cutS false _ _)       = [ π ]
    deadS π (lnS false _)          = [ π ]
    deadS π (joinS _ false _ _)    = [ π ]
    deadS π (mapS _ s)             = deadS (π ++ [ 0 ]) s
    deadS π (scanS _ _ s)          = deadS (π ++ [ 0 ]) s
    deadS π (cutS true _ s)        = deadS (π ++ [ 0 ]) s
    deadS π (lnS true s)           = deadS (π ++ [ 0 ]) s
    deadS π (takeS _ _ _ s)        = deadS (π ++ [ 0 ]) s
    deadS π (flatS _ _ _ _ _ o ls) = deadS (π ++ [ 0 ]) o ++ deadLs π 1 ls
    deadS π (connS k o b)          = (if CS.srcLive k then deadS (π ++ [ 0 ]) o else [ π ++ [ 0 ] ]) ++ deadS (π ++ [ 1 ]) b
    deadS π _                      = []

    deadLs : ∀ {Γ A} → List ℕ → ℕ → List (St Γ A) → List (List ℕ)
    deadLs π i []       = []
    deadLs π i (s ∷ ls) = deadS (π ++ [ i ]) s ++ deadLs π (suc i) ls

  live : List (List ℕ) → List ℕ → Bool
  live ds π = not (anyᵇ (λ d → prefix d π) ds)

  -- A node's entry rows the cursor has reached that it has not delivered.
  owed : (Pos → Bool) → Seen → List (Pos × Kind)
  owed reached s with Seen.entry s
  ... | nothing = []
  ... | just es = concatMap (λ { (q , k) → when (reached q ∧ not (anyᵇ (sameRow (q , k)) (Seen.got s))) (q , k) }) es

  arrears : ℕ → String → (Pos → Bool) → List (List ℕ) → List Seen → List String
  arrears t why reached ds = concatMap λ s → arrear s (owed reached s)
    where
      arrear : Seen → List (Pos × Kind) → List String
      arrear s []       = []
      arrear s (r ∷ rs) =
        when (live ds (Seen.path s))
             ("step " +++ showℕ t +++ " node " +++ showPath (Seen.path s) +++ " " +++ Seen.former s +++ " owes " +++ showRows (r ∷ rs)
              +++ why +++ "; delivered " +++ showRows (Seen.got s))

  showKey : Key → String
  showKey (at p)    = "at " +++ showPos p
  showKey (after p) = "after " +++ showPos p

  showCursor : Maybe Pos → String
  showCursor nothing  = "none"
  showCursor (just c) = showPos c

------------------------------------------------------------------------
-- The run, checked

record Probe : Set where
  constructor probing
  field
    book   : List Seen
    cursor : Maybe Pos
    falls  : Maybe String
    backs  : List String

private
  open module D = Driver ℕ using (step; silent; value; complete; drained)

  -- A node subscribed: its entry, the first time its path is seen (a
  -- defer's body keeps the defer's).
  enter : ℕ → Conf ℕ → List Seen → List Seen
  enter u ⟨ c , pend o q , subscribing , _ ⟩ bk with known (dirs c) bk
  ... | just _  = bk
  ... | nothing = seen (dirs c) (formerOf o) (entryOf u (scopeOf c) o q) [] ∷ bk
  enter u _ bk = bk

  -- A node rising: its delivery, against its entry and the cursor.
  delivered : ℕ → Conf ℕ → Probe → Probe × List String
  delivered t ⟨ c , _ , rising e , p ⟩ (probing bk cur fl bs) =
    probing (deliver π r bk) (ahead cur) fl bs , back cur ++ stray (known π bk)
    where
      π = dirs c
      r = p , kindOf e

      back : Maybe Pos → List String
      back nothing  = []
      back (just C) = when (p <ᵖ C) ("step " +++ showℕ t +++ " node " +++ showPath π +++ " delivered " +++ showRows [ r ] +++ "before the cursor " +++ showPos C)

      ahead : Maybe Pos → Maybe Pos
      ahead nothing  = just p
      ahead (just C) = if p <ᵖ C then just C else just p

      stray : Maybe Seen → List String
      stray nothing  = []
      stray (just s) with Seen.entry s
      ... | nothing = []
      ... | just es =
        when (not (anyᵇ (sameRow r) es))
             ("step " +++ showℕ t +++ " node " +++ showPath π +++ " " +++ Seen.former s +++ " delivered " +++ showRows [ r ] +++ "outside its entry " +++ showRows es)
        ++ when (anyᵇ (λ { (q , _) → not (q <ᵖ p) }) (Seen.got s))
             ("step " +++ showℕ t +++ " node " +++ showPath π +++ " " +++ Seen.former s +++ " delivered " +++ showRows [ r ] +++ "not past its own " +++ showRows (Seen.got s))
  delivered t _ pr = pr , []

  settled : Conf ℕ → Bool
  settled ⟨ _ , _ , rising _ , _ ⟩ = false
  settled _                       = true

  reachedBy : Maybe Pos → Pos → Bool
  reachedBy nothing  q = false
  reachedBy (just C) q = not (C <ᵖ q)

  look : ℕ → ℕ → Conf ℕ → Probe → Probe × List String
  look u t k pr with delivered t k (record pr { book = enter u k (Probe.book pr) })
  ... | pr′ , fs = pr′ , fs ++ (if settled k then arrears t (" at or before the cursor " +++ showCursor (Probe.cursor pr′)) (reachedBy (Probe.cursor pr′))
                                                             (deadS [] (plug (Conf.ctx k) (Conf.foc k))) (Probe.book pr′)
                                               else [])

  markName : Mark → String
  markName ofM     = "ofM"
  markName attM    = "attM"
  markName bodyM   = "bodyM"
  markName srcAttM = "srcAttM"
  markName owedM   = "owedM"
  markName cpM     = "cpM"
  markName cutM    = "cutM"
  markName joinM   = "joinM"
  markName leafM   = "leafM"

  ctxName : ∀ {R Γ A} → Ctx R Γ A → String
  ctxName top                     = "top"
  ctxName (inMap _ _)             = "map"
  ctxName (inScan _ _ _)          = "scan"
  ctxName (inCut _ _ _)           = "cut"
  ctxName (inLn _ _)              = "lane"
  ctxName (inTake _ _ _ _)        = "take"
  ctxName (inOuter _ _ _ _ _ _ _) = "outer"
  ctxName (inLanes _ _ _ _ _ _ _ _ _) = "lanes"
  ctxName (inSrc _ _ _)           = "source"
  ctxName (inBody _ _ _)          = "body"

  stepKind : Conf ℕ → String
  stepKind ⟨ c , pend o q , subscribing , _ ⟩ = "sub " +++ formerOf o
  stepKind ⟨ c , s , subscribing , _ ⟩        = "sub stuck"
  stepKind ⟨ c , s , rising _ , _ ⟩          = "rise " +++ ctxName c
  stepKind ⟨ c , s , absorbed , _ ⟩ with search top (plug c s)
  ... | just f  = "run " +++ markName (Found.mark f)
  ... | nothing = "quiet"

  clockOf : Conf ℕ → Key
  clockOf k with Conf.mode k | Machine.next k
  ... | absorbed | just κ = κ
  ... | _        | _      = at (Conf.pos k)

  -- A silent step's clock against the step before's; the first fall noted.
  ticked : ℕ → Conf ℕ → Conf ℕ → Probe → Probe
  ticked t k k′ pr with Probe.falls pr | clockOf k′ <ᴷ clockOf k
  ... | nothing | true = record pr { falls = just ("step " +++ showℕ t +++ " " +++ stepKind k +++ " clock " +++ showKey (clockOf k) +++ " then " +++ showKey (clockOf k′)) }
  ... | _       | _    = pr

  -- The root shows a row: a fall since the last one is met.
  shown : Probe → Probe
  shown (probing bk cur (just f) []) = probing bk cur nothing [ f ]
  shown (probing bk cur _ bs)        = probing bk cur nothing bs

  -- The run's result: its failures, its first met fall, and a fall no
  -- row followed.
  Result : Set
  Result = List String × List String × Maybe String

  ended : List String → Probe → Result
  ended fs pr = fs , Probe.backs pr , Probe.falls pr

  -- The run for `n` more steps: its first failures, and its clock's fall.
  go : ℕ → ℕ → ℕ → Probe → Conf ℕ → Result
  go u zero    t pr k = ended [] pr
  go u (suc n) t pr k with look u t k pr
  ... | pr′ , f ∷ fs = ended (f ∷ fs) pr′
  ... | pr′ , []     with step k
  ...   | silent _ k′    = go u n (suc t) (ticked t k k′ pr′) k′
  ...   | value _ _ _ k′ = go u n (suc t) (shown pr′) k′
  ...   | complete _     = ended [] (shown pr′)
  ...   | drained        = ended (arrears t " though the run drained" (λ _ → true) (deadS [] (plug (Conf.ctx k) (Conf.foc k))) (Probe.book pr′)) pr′

-- A seed's program, its run read for `n` steps.
probe : ℕ → ℕ → List String × List String × Maybe String
probe n seed = let p = program seed in go (depth 3 p) n 0 (probing [] nothing nothing []) (load (toObs timeline 3 p [] [] []))

------------------------------------------------------------------------
-- THE SILENT RUN, MEASURED: `adequacy.Complete`'s fuel, read off a run.
--
-- P is the next row the root shows.  KS is the root's rows at or before P
-- and every ancestor of each.  A counts KS strictly past the clock; a
-- silent step leaving A where it was is STILL.  W is a candidate
-- potential every still step must lower: each pending subscription's
-- syntax (a defer is one), weighted by depth; each admin mark, pending or
-- owed, and each mark keyed outside KS and before P, at depth + 2; the
-- depth of a rise; and, once absorbed with a KS mark next, that mark's
-- depth + 2.  A mark at or past P runs only as the clock passes P, so
-- never on a still step.
--
-- Reported, never failed: a step whose A rose; a still step whose W did
-- not fall, with its kind; a settled-free step (subscribing or rising)
-- with a mark keyed before its position; a fall no row followed.  A
-- seed whose root listing a budget cut short is not measured.

private
  shownL : ℕ → Conf ℕ → List Pos
  shownL zero    k = []
  shownL (suc n) k with step k
  ... | silent _ k′    = shownL n k′
  ... | value _ p _ k′ = p ∷ shownL n k′
  ... | complete p     = [ p ]
  ... | drained        = []

  ksOf : List Pos → Pos → List Pos
  ksOf rws P = concatMap prefixes (concatMap (λ q → when ((q <ᵖ P) ∨ does (q ≟ᵖ P)) q) rws) ++ prefixes P

  aheadN : Key → List Pos → ℕ
  aheadN κ []       = 0
  aheadN κ (q ∷ qs) = if κ <ᴷ at q then suc (aheadN κ qs) else aheadN κ qs

  -- Every mark key in a tree, a joiner's whole inbox included.
  mutual
    keysS : ∀ {Γ A} → St Γ A → List Key
    keysS (joinS j g x ib)        = mapL (λ e → at (proj₁ e)) ib
    keysS s                       = mapL proj₂ (own s) ++ kidsK s

    kidsK : ∀ {Γ A} → St Γ A → List Key
    kidsK (mapS _ s)               = keysS s
    kidsK (scanS _ _ s)            = keysS s
    kidsK (cutS _ _ s)             = keysS s
    kidsK (lnS _ s)                = keysS s
    kidsK (takeS _ _ _ s)          = keysS s
    kidsK (flatS _ _ _ _ _ o ls)   = keysS o ++ keysL ls
    kidsK (connS _ o b)            = keysS o ++ keysS b
    kidsK _                        = []

    keysL : ∀ {Γ A} → List (St Γ A) → List Key
    keysL []       = []
    keysL (s ∷ ls) = keysS s ++ keysL ls

  -- A settled-free step: a mark keyed at or before the run's position.
  early : Conf ℕ → Maybe Key
  early ⟨ c , s , absorbed , p ⟩ = nothing
  early ⟨ c , s , _ , p ⟩ = firstL (keysS (plug c s))
    where
      firstL : List Key → Maybe Key
      firstL []       = nothing
      firstL (κ ∷ κs) = if not (at p <ᴷ κ) then just κ else firstL κs

  record Meas : Set where
    constructor meas
    field
      lines  : List String
      stills : ℕ
      tags   : List String

  note : Bool → String → Meas → Meas
  note true  l (meas fs n st) = meas (fs ++ [ l ]) n st
  note false l m              = m

  -- `tg` names the listing: the rows at or before P (exact), or every row
  -- listed (wide), as `adequacy.Complete` lets any cover stand.
  judge : Bool → String → ℕ → List Pos → Pos → Conf ℕ → Conf ℕ → Meas → Meas
  judge main tg t ks P k k′ m = still (aheadN (clockOf k) ks) (aheadN (clockOf k′) ks) (tagIf (main ∧ bad (early k)) "KEY" (note (main ∧ bad (early k)) keyLine m))
    where
      tick : Bool → ℕ → ℕ
      tick b n = if b then suc n else n
      tagIf : Bool → String → Meas → Meas
      tagIf true  x m′ = record m′ { tags = x ∷ Meas.tags m′ }
      tagIf false x m′ = m′
      bad : Maybe Key → Bool
      bad nothing  = false
      bad (just _) = true
      showE : Maybe Key → String
      showE nothing  = ""
      showE (just κ) = showKey κ
      keyLine = "KEY step " +++ showℕ t +++ " " +++ stepKind k +++ " at " +++ showPos (Conf.pos k) +++ " has a mark " +++ showE (early k)
      still : ℕ → ℕ → Meas → Meas
      still a₀ a₁ m′ with a₀ <ᵇ a₁ | a₁ ≡ᵇ a₀
      ... | true | _     = tagIf true (tg +++ "AROSE") (note true (tg +++ "AROSE step " +++ showℕ t +++ " " +++ stepKind k +++ " A " +++ showℕ a₀ +++ " then " +++ showℕ a₁) m′)
      ... | _    | false = m′
      ... | _    | true  with W ks P k ≤ᵇ W ks P k′
      ...   | false = tagIf main ("still " +++ stepKind k) (record m′ { stills = tick main (Meas.stills m′) })
      ...   | true  = record (note true (tg +++ "STUCK step " +++ showℕ t +++ " " +++ stepKind k +++ " clock " +++ showKey (clockOf k)
                                        +++ " then " +++ stepKind k′ +++ " clock " +++ showKey (clockOf k′)
                                        +++ " W " +++ showℕ (W ks P k) +++ " then " +++ showℕ (W ks P k′)) m′)
                             { stills = tick main (Meas.stills m′) ; tags = (tg +++ "STUCK " +++ stepKind k) ∷ (if main then ("still " +++ stepKind k) ∷ Meas.tags m′ else Meas.tags m′) }

  walkM : List Pos → ℕ → ℕ → List Pos → Conf ℕ → Meas → Meas
  walkM rws zero    t sh       k m = m
  walkM rws (suc n) t []       k m = m
  walkM rws (suc n) t (P ∷ sh) k m with step k
  ... | silent _ k′    = walkM rws n (suc t) (P ∷ sh) k′ (judge true "" t (ksOf rws P) P k k′ (judge false "WIDE " t (ksOf rws P ++ concatMap prefixes rws) P k k′ m))
  ... | value _ _ _ k′ = walkM rws n (suc t) sh k′ m
  ... | complete _     = m
  ... | drained        = m

-- A seed's silent run measured for `n` steps; nothing when its root
-- listing is cut short.
measure : ℕ → ℕ → Maybe Meas
measure n seed with program seed
... | p with listT (depth 3 p) (toObs timeline 3 p [] [] []) [] (ix 0 ∷ [])
...   | nothing = nothing
...   | just l  =
  if short l then nothing
  else just (walkM (mapL proj₁ (rows l)) n 0 (shownL n (load (toObs timeline 3 p [] [] []))) (load (toObs timeline 3 p [] [] [])) (meas [] 0 []))

------------------------------------------------------------------------
-- The report

private
  each : String → List String → IO Unit
  each tag []       = putStrLn ""
  each tag (x ∷ xs) = putStrLn (tag +++ x) >>= λ _ → each tag xs

  count : Bool → ℕ → ℕ
  count b n = if b then suc n else n

  some : Maybe String → Bool
  some nothing  = false
  some (just _) = true

  late : Bool → ℕ → Maybe String → IO Unit
  late false seed _        = pure tt
  late true  seed nothing  = pure tt
  late true  seed (just f) = putStrLn ("cursor-check: LATEFALL seed " +++ showℕ seed +++ " " +++ f +++ " in " +++ showCode natᵗ (program seed))

  report : List ℕ → ℕ → ℕ → ℕ → IO Unit
  report []          bad bk tl = putStrLn ("cursor-check: done " +++ showℕ bad +++ " failing seeds, " +++ showℕ bk +++ " seeds whose clock ran back before a row, "
                                           +++ showℕ tl +++ " more whose clock ran back only after the last row")
  report (seed ∷ ss) bad bk tl with probe 400 seed
  ... | [] , [] , u = late (tl <ᵇ 8) seed u >>= λ _ → report ss bad bk (count (some u) tl)
  ... | fs , cs , u =
    putStrLn ("cursor-check: program " +++ showℕ seed +++ " " +++ showCode natᵗ (program seed)) >>= λ _ →
    each ("cursor-check: FAIL seed " +++ showℕ seed +++ " ") fs >>= λ _ →
    each ("cursor-check: CLOCK seed " +++ showℕ seed +++ " ") cs >>= λ _ →
    report ss (count (not (null fs)) bad) (count (not (null cs)) bk) (count (some u ∧ null cs) tl)

  -- The still steps' kinds, tallied.
  tally : List String → List (String × ℕ) → List (String × ℕ)
  tally []       ts = ts
  tally (x ∷ xs) ts = tally xs (bump ts)
    where
      bump : List (String × ℕ) → List (String × ℕ)
      bump []              = [ (x , 1) ]
      bump ((y , n) ∷ ys) = if x == y then (y , suc n) ∷ ys else (y , n) ∷ bump ys

  showTally : List (String × ℕ) → String
  showTally []             = ""
  showTally ((x , n) ∷ ts) = x +++ " " +++ showℕ n +++ "; " +++ showTally ts

  stillReport : List ℕ → ℕ → ℕ → ℕ → List (String × ℕ) → IO Unit
  stillReport []          cutN sts bad ts =
    putStrLn ("cursor-check: still " +++ showℕ sts +++ " still steps, " +++ showℕ bad +++ " seeds with a finding, "
              +++ showℕ cutN +++ " seeds unmeasured; steps and findings by kind: " +++ showTally ts)
  stillReport (seed ∷ ss) cutN sts bad ts with measure 400 seed
  ... | nothing = stillReport ss (suc cutN) sts bad ts
  ... | just (meas [] n st) = stillReport ss cutN (sts + n) bad (tally st ts)
  ... | just (meas fs n st) with bad <ᵇ 25
  ...   | false = stillReport ss cutN (sts + n) (suc bad) (tally st ts)
  ...   | true  =
    putStrLn ("cursor-check: program " +++ showℕ seed +++ " " +++ showCode natᵗ (program seed)) >>= λ _ →
    each ("cursor-check: STILL seed " +++ showℕ seed +++ " ") (take 4 fs) >>= λ _ →
    stillReport ss cutN (sts + n) (suc bad) (tally st ts)

main : IO Unit
main = report (upTo 300) 0 0 0 >>= λ _ → stillReport (upTo 300) 0 0 0 []
