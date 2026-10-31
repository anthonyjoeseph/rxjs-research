{-# OPTIONS --guardedness #-}

-- THE SETTLED ENTRY, PROBED: does a node's reading only ever shrink?  The
-- pure semantics runs each generated program, and at every settled step
-- (absorbed or subscribing) every node of the tree is listed as
-- `adequacy.Rows.rows` reads it, under the environment `adequacy.Rows.env`
-- gives it.  A node is named by its path of child indices, which the
-- machine never renumbers: a flatMap's lanes are only ever appended.  The
-- first listing of a path is its ENTRY; every later one must lie inside
-- it.  A row outside is printed with the node's former, whether it sits
-- under a connect's body (where the reading hangs on the source's current
-- rows), and the row's kind; a connect's former carries its source's and
-- its body's rows, now and at its entry.
--
-- Values are erased to their kind, since a node's type is not one the
-- harness can compare.  A listing cut short by a budget is skipped as an
-- entry, never as a later reading.  Each clause of `listS` mirrors one of
-- `adequacy.Rows.rows`; each joiner's, one of its `Rows` module over
-- `denotation.EmissionSet.Joining`.  A probe for `make entry-check`: no
-- proof reads it.
module quickcheck.Entry-Check where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using () renaming (⊤ to Unit)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; length; upTo; reverse) renaming (map to mapL)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤ᵇ_; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.String using (String) renaming (_++_ to _+++_)
open import IO.Primitive.Core using (_>>=_)
open import IO.Primitive.Finite using (putStrLn)
open import Relation.Nullary using (does)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; Timeline; ix; last; inside; _<ᵖ_; _≟ᵖ_; ofᴱ)
open import denotation.EmissionSet using (Ev; out; skip; pin; end)
open import operation.PureObservable using (module Machine; module Driver)
open Machine using (St; pend; coldS; ofS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; CS; Owe; free; cpAt; cutAt; overAt;
                    Conf; plug; subscribing; absorbed; rising; load; nx; cp)
open import adequacy.Rows using (tapeE)
open import quickcheck.Ty using (showPos)
open import quickcheck.Code using (toObs; timeline)
open import quickcheck.Trace using (depth)
open import quickcheck.Quickcheck using (program)
open import quickcheck.Tabled using (Row; Listed; _⊣_; rows; short; bind; concatMap; mapM; when; anyᵇ; allᵇ; _≼ᵇ_; endBy; endBefore;
                                     ends; properᵇ; values; count; fuel; walk; mapRows; rejoin; past; afterL; lanes; listT;
                                     module Order; scanRows; takeRows; connRows)

------------------------------------------------------------------------
-- Rows, their values erased

data Kind : Set where
  kout kskip kend : Kind
  kpin            : Pos → Kind

erase : ∀ {A} → Row A → Pos × Kind
erase (q , out _) = q , kout
erase (q , skip)  = q , kskip
erase (q , pin r) = q , kpin r
erase (q , end)   = q , kend

sameKind : Kind → Kind → Bool
sameKind kout     kout     = true
sameKind kskip    kskip    = true
sameKind kend     kend     = true
sameKind (kpin r) (kpin s) = does (r ≟ᵖ s)
sameKind _        _        = false

sameRow : Pos × Kind → Pos × Kind → Bool
sameRow (q , k) (q′ , k′) = does (q ≟ᵖ q′) ∧ sameKind k k′

showKind : Kind → String
showKind kout     = "out"
showKind kskip    = "skip"
showKind kend     = "end"
showKind (kpin r) = "pin " +++ showPos r

showRows : List (Pos × Kind) → String
showRows []             = ""
showRows ((q , k) ∷ rs) = "(" +++ showPos q +++ " " +++ showKind k +++ ") " +++ showRows rs

------------------------------------------------------------------------
-- A joiner part way through, listed: `Joining`'s rows, given its outer's
-- rows, each running value's lane (by position), the begun lanes' rows,
-- and its policy's `Over`, `Runs`, `Cut` and `Hand`.

module JoinL {A B : Set} (o : List (Row A)) (ls : List (Pos × List (Row B))) (bg : List (Row B))
             (overᵇ runsᵇ : Pos → Bool) (cutᵇ : Pos → Pos → Bool) (handᵇ : Pos → Bool) where
  doneᵇ : Pos → Bool
  doneᵇ c = overᵇ c ∧ allᵇ (λ { (q , l) → not (runsᵇ q ∧ (q <ᵖ c) ∧ not (cutᵇ q c)) ∨ endBy l c }) ls

  endRow : Pos → Row B
  endRow c = if handᵇ c then (c ++ [ ix 0 ] , skip) else (c , (if doneᵇ c then end else skip))

  outerR : Row A → List (Row B)
  outerR (q , out _) = [ q ++ [ ix 0 ] , skip ]
  outerR (q , skip)  = [ q , skip ]
  outerR (q , pin r) = [ q , pin r ]
  outerR (c , end)   = [ c , (if doneᵇ c then end else skip) ]

  laneR : Pos → Row B → List (Row B)
  laneR q (k , end)   = when (not (cutᵇ q k)) (endRow k)
  laneR q (k , pin r) = when (not (cutᵇ q k)) (k , pin r) ++ when (not (cutᵇ q r) ∧ inside r k) (k , pin r)
  laneR q (k , e)     = when (not (cutᵇ q k)) (k , e)

  bgR : Row B → List (Row B)
  bgR (k , end) = [ endRow k ]
  bgR r         = [ r ]

  joined : List (Row B)
  joined = concatMap outerR o
        ++ concatMap (λ { (q , l) → if runsᵇ q then concatMap (laneR q) l else [] }) ls
        ++ concatMap bgR bg

-- Begun lanes by their ends.
endsL : ∀ {B} → List (Listed B) → List (List Pos)
endsL = mapL (λ l → ends (rows l))

rowsL : ∀ {B} → List (Listed B) → List (Row B)
rowsL = concatMap rows

shortL : ∀ {B} → List (Listed B) → Bool
shortL = anyᵇ short

-- Each running value's lane, by its position.
byPos : ∀ {A B : Set} → List (Pos × A × Listed B) → List (Pos × List (Row B))
byPos = mapL (λ { (q , _ , l) → q , rows l })

shortLanes : ∀ {A B : Set} → List (Pos × A × Listed B) → Bool
shortLanes = anyᵇ (λ { (_ , _ , l) → short l })

outerOver : ∀ {A} → Bool → List (Row A) → Pos → Bool
outerOver d o c = d ∨ endBy o c

-- `Rows.Flat`.
flatL : ∀ {A B : Set} → (A → Pos → Maybe (Listed B)) → Listed A → Bool → ℕ → List (Listed B) → Maybe (Listed B)
flatL ln o d n Ls =
  bind (lanes ln (values (rows o))) λ ls →
  just (JoinL.joined (rows o) (byPos ls) (rowsL Ls)
          (λ c → outerOver d (rows o) c ∧ (n ≤ᵇ count (λ k → k ≼ᵇ c) (endsL Ls))) (λ _ → true) (λ _ _ → false) (λ _ → false)
        ⊣ (short o ∨ shortLanes ls ∨ shortL Ls))

-- `Rows.SwitchF`.
switchL : ∀ {A B : Set} → (A → Pos → Maybe (Listed B)) → Listed A → Bool → ℕ → List (Listed B) → Maybe (Listed B)
switchL ln o d n Ls =
  bind (lanes ln vs) λ ls →
  just (JoinL.joined (rows o) (byPos ls) (concatMap bgR (rowsL Ls))
          (λ c → outerOver d (rows o) c ∧ ((n ≤ᵇ count (λ k → k ≼ᵇ c) (endsL Ls)) ∨ kill c)) (λ _ → true) cutᵇ (λ _ → false)
        ⊣ (short o ∨ shortLanes ls ∨ shortL Ls))
  where
    vs = values (rows o)

    kill : Pos → Bool
    kill k = anyᵇ (λ { (q′ , _) → q′ <ᵖ k }) vs

    cutᵇ : Pos → Pos → Bool
    cutᵇ q k = anyᵇ (λ { (q′ , _) → (q <ᵖ q′) ∧ (q′ <ᵖ k) }) vs

    bgR : ∀ {B} → Row B → List (Row B)
    bgR (k , pin r) = when (not (kill k)) (k , pin r) ++ when (not (kill r) ∧ inside r k) (k , pin r)
    bgR (k , e)     = when (not (kill k)) (k , e)

-- `Rows.ExhaustF`: the last run at each value, `nothing` for a begun lane.
module ExhaustM {A B : Set} (o : Listed A) (ls : List (Pos × List (Row B))) (n : ℕ) (Les : List (List Pos)) where
  vs : List (Pos × A)
  vs = values (rows o)
  open Order vs using (minᵇ; nextᵇ)

  freeᵇ : Pos → Bool
  freeᵇ q = n ≤ᵇ count (λ k → k <ᵖ q) Les

  laneAt : Pos → List (Row B)
  laneAt q = concatMap (λ { (q′ , l) → if does (q′ ≟ᵖ q) then l else [] }) ls

  opening : Pos → Maybe Pos
  opening q₂ = if freeᵇ q₂ then just q₂ else nothing

  moves : Pos → Maybe Pos → List (Maybe Pos)
  moves q₂ (just q) = when (endBefore (laneAt q) q₂) (just q₂) ++ when (properᵇ (laneAt q) q₂) (just q)
  moves q₂ nothing  = [ opening q₂ ]

  mutual
    curs : ℕ → Pos → List (Maybe Pos)
    curs zero    q₂ = []
    curs (suc k) q₂ = when (minᵇ q₂) (opening q₂) ++ concatMap (prior k q₂) vs

    prior : ℕ → Pos → Pos × A → List (Maybe Pos)
    prior k q₂ (q₁ , _) = if nextᵇ q₁ q₂ then concatMap (moves q₂) (curs k q₁) else []

  isJust : Pos → Maybe Pos → Bool
  isJust q (just q′) = does (q′ ≟ᵖ q)
  isJust q nothing   = false

  runᵇ : Pos → Bool
  runᵇ q = anyᵇ (isJust q) (curs (suc (length vs)) q)

exhaustL : ∀ {A B : Set} → (A → Pos → Maybe (Listed B)) → Listed A → Bool → ℕ → List (Listed B) → Maybe (Listed B)
exhaustL ln o d n Ls =
  bind (lanes ln (values (rows o))) λ ls →
  just (JoinL.joined (rows o) (byPos ls) (rowsL Ls)
          (λ c → outerOver d (rows o) c ∧ (n ≤ᵇ count (λ k → k ≼ᵇ c) (endsL Ls))) (ExhaustM.runᵇ o (byPos ls) n (endsL Ls))
          (λ _ _ → false) (λ _ → false)
        ⊣ (short o ∨ shortLanes ls ∨ shortL Ls))

-- `Rows.BoundedF`: level by level from the begun lanes' ends, the queued
-- values first, each item's lane at every start `Starts` allows.
module BoundedM {A B : Set} (m : ℕ) (ln : A → Pos → Maybe (Listed B)) (o : Listed A) (n : ℕ) (Qu : List A) where
  vs : List (Pos × A)
  vs = values (rows o)
  open Order vs using (nths)

  -- the i-th item: queued (no position), or the outer's
  items : ℕ → List (Maybe Pos × A)
  items i = if i <ᵇ length Qu then nthQ i Qu else mapL (λ { (q , a) → just q , a }) (nths (i ∸ length Qu))
    where
      nthQ : ℕ → List A → List (Maybe Pos × A)
      nthQ _       []       = []
      nthQ zero    (a ∷ _)  = [ nothing , a ]
      nthQ (suc k) (_ ∷ as) = nthQ k as

  arr : Maybe Pos → Pos → Bool
  arr nothing  c = true
  arr (just q) c = q <ᵖ c

  queuedAt : ℕ → Maybe Pos → List (List Pos) → Pos → List Pos
  queuedAt i w ess c =
    let k = n + i ∸ m in
    when (arr w c ∧ (suc k ≤ᵇ count (λ k′ → k′ ≼ᵇ c) ess) ∧ not (suc k ≤ᵇ count (λ k′ → k′ <ᵖ c) ess)) (c ++ [ ix 1 ])

  starts : ℕ → Maybe Pos → List (List Pos) → List Pos
  starts i w ess = if n + i <ᵇ m then room w else freed w
    where
      room : Maybe Pos → List Pos
      room (just q) = [ q ++ [ ix 1 ] ]
      room nothing  = []

      queued : List Pos
      queued = concatMap (concatMap (queuedAt i w ess)) ess

      freed : Maybe Pos → List Pos
      freed (just q) = if suc (n + i ∸ m) ≤ᵇ count (λ k → k <ᵖ q) ess then [ q ++ [ ix 1 ] ] else queued
      freed nothing  = queued

  -- An item, and its lane at each start.
  Item : Set
  Item = Maybe Pos × List (Pos × Listed B)

  item : ℕ → List (List Pos) → Maybe Pos × A → Maybe Item
  item i ess (w , a) = bind (mapM (λ s → bind (ln a s) λ l → just (s , past s l)) (starts i w ess)) λ ss → just (w , ss)

  itemEnds : Item → List Pos
  itemEnds (_ , ss) = concatMap (λ { (_ , l) → ends (rows l) }) ss

  -- `k` levels from level `i`, the lanes before it `ess`: every item, and
  -- the lanes before the level past them.
  levels : ℕ → ℕ → List (List Pos) → Maybe (List Item × List (List Pos))
  levels zero    i ess = just ([] , ess)
  levels (suc k) i ess =
    bind (mapM (item i ess) (items i)) λ gs →
    bind (levels k (suc i) (concatMap itemEnds gs ∷ ess)) λ { (rest , ess′) → just (gs ++ rest , ess′) }

  boundedL : Bool → List (Listed B) → Maybe (Listed B)
  boundedL d Ls =
    bind (levels (length Qu) 0 (endsL Ls)) λ { (gq , essQ) →
    bind (levels (length vs) (length Qu) essQ) λ { (go , _) →
    just (rowsOf (gq ++ go) essQ) } }
    where
      lanesOf : Item → List (Row B)
      lanesOf (_ , ss) = concatMap (λ { (_ , l) → rows l }) ss

      outerLanes : List Item → List (Pos × List (Row B))
      outerLanes = concatMap λ { (just q , ss) → [ q , lanesOf (just q , ss) ] ; (nothing , _) → [] }

      waiting : List Item → List (Row B)
      waiting = concatMap λ { (nothing , ss) → lanesOf (nothing , ss) ; (just _ , _) → [] }

      shortItems : List Item → Bool
      shortItems = anyᵇ (λ { (_ , ss) → anyᵇ (λ { (_ , l) → short l }) ss })

      rowsOf : List Item → List (List Pos) → Listed B
      rowsOf gs essQ =
        JoinL.joined (rows o) (outerLanes gs) (rowsL Ls ++ waiting gs)
          (λ c → outerOver d (rows o) c ∧ (n + length Qu ≤ᵇ count (λ k → k ≼ᵇ c) essQ))
          (λ q → anyᵇ (λ { (q′ , _) → does (q′ ≟ᵖ q) }) (outerLanes gs))
          (λ _ _ → false)
          (λ c → anyᵇ (λ { (_ , ss) → anyᵇ (λ { (s , _) → does (s ≟ᵖ (c ++ [ ix 1 ])) }) ss }) gs)
        ⊣ (short o ∨ shortL Ls ∨ shortItems gs)

------------------------------------------------------------------------
-- Every node, listed

record Node : Set where
  constructor node
  field
    path   : List ℕ
    former : String
    body   : Bool
    seen   : Maybe (List (Pos × Kind) × Bool)

private
  noted : ∀ {A} → List ℕ → String → Bool → Maybe (Listed A) → Node
  noted π f b nothing  = node π f b nothing
  noted π f b (just l) = node π f b (just (mapL erase (rows l) , short l))

  closedRows : ∀ {Γ A} → CS Γ A → List (Row A)
  closedRows k = when (CS.closed k) (CS.endAt k , end)

  -- A binder's rows: what its source still owes, and its end once closed,
  -- each a row of the source's frozen entry `F` before that entry's end.
  frozenHot : ∀ {Γ A} → CS Γ A → Listed A → Listed A → Listed A
  frozenHot k F σ = concatMap (λ { (q , e) → when (properᵇ (rows F) q ∧ anyᵇ (λ { (q′ , _) → does (q′ ≟ᵖ q) }) (rows F)) (q , e) })
                              (rows σ ++ closedRows k)
                  ⊣ (short σ ∨ short F)

  -- A connect's source rows as its echoes read them: its subscribe burst
  -- always, any other row only while the source lives and before the
  -- body's end the connect still owes.
  gated : ∀ {Γ A} → CS Γ A → Listed A → Listed A
  gated k σ = concatMap (λ { (q , e) → when (inside (CS.connAt k ++ [ ix 1 ]) q ∨ (CS.srcLive k ∧ before (CS.owedAt k) q)) (q , e) }) (rows σ)
            ⊣ short σ
    where
      before : Maybe Pos → Pos → Bool
      before nothing  q = true
      before (just c) q = q <ᵖ c

  inbox : ∀ {A} → List (Pos × Machine.Ev A) → List (Row A)
  inbox []                  = []
  inbox ((q , nx a) ∷ ib)   = (q , out a) ∷ inbox ib
  inbox ((q , cp) ∷ ib)     = (q , end) ∷ inbox ib

  kept : ∀ {A} → Pos → List (Row A) → List (Row A)
  kept p = concatMap λ { (k , pin r) → when (not (p <ᵖ r) ∧ inside r k) (k , pin r) ; _ → [] }

  takeR : ∀ {A} → Bool → (A → Bool) → Owe → Listed A → Listed A
  takeR i q free      l = takeRows i q l
  takeR i q (cpAt p)  l = (((p ++ [ last ]) , end) ∷ kept p (rows l)) ⊣ short l
  takeR i q (cutAt p) l = kept p (rows l) ⊣ short l
  takeR i q (overAt p) l = kept p (rows l) ⊣ short l

  lift₁ : ∀ {A B} → (Listed A → Listed B) → Maybe (Listed A) → Maybe (Listed B)
  lift₁ f m = bind m λ l → just (f l)

  allJust : ∀ {B} → List (Maybe (Listed B)) → Maybe (List (Listed B))
  allJust = mapM (λ m → m)

  opName : FlatOp → String
  opName (mergeᶠ nothing)  = "merge"
  opName (mergeᶠ (just _)) = "bounded"
  opName switchᶠ           = "switch"
  opName exhaustᶠ          = "exhaust"

  -- A joiner by its policy, each value's lane listed at its subscription.
  joiner : ∀ {Γ A B} → ℕ → All Listed Γ → FlatOp → (A → Obs Timeline Γ B) → Bool → ℕ → List A → Listed A → List (Listed B)
         → Maybe (Listed B)
  joiner u ρ (mergeᶠ nothing)  f d n q o Ls = flatL (afterL (λ a → listT u (f a) ρ)) o d n Ls
  joiner u ρ (mergeᶠ (just m)) f d n q o Ls = BoundedM.boundedL m (afterL (λ a → listT u (f a) ρ)) o n q d Ls
  joiner u ρ switchᶠ           f d n q o Ls = switchL (afterL (λ a → listT u (f a) ρ)) o d n Ls
  joiner u ρ exhaustᶠ          f d n q o Ls = exhaustL (afterL (λ a → listT u (f a) ρ)) o d n Ls

-- The node at `π`, under the environment `ρ`, `b` whether under a body:
-- its listing, and every node of its subtree, its own first.
mutual
  listS : ∀ {Γ A} → ℕ → All Listed Γ → List ℕ → Bool → St Γ A → Maybe (Listed A) × List Node
  listS u ρ π b s with listN u ρ π b s
  ... | f , l , ns = l , noted π f b l ∷ ns

  listN : ∀ {Γ A} → ℕ → All Listed Γ → List ℕ → Bool → St Γ A → String × Maybe (Listed A) × List Node
  listN u ρ π b (pend o p)      = "pend" , listT u o ρ p , []
  listN u ρ π b (coldS true l)  = "cold" , just (walk fuel (tapeE l)) , []
  listN u ρ π b (coldS false l) = "cold" , just ([] ⊣ false) , []
  listN u ρ π b (ofS i p xs)    = "of" , just (walk fuel (ofᴱ p i xs)) , []
  listN u ρ π b (mapS f s) with listS u ρ (π ++ [ 0 ]) b s
  ... | l , ns = "map" , lift₁ (mapRows f) l , ns
  listN u ρ π b (scanS f z s) with listS u ρ (π ++ [ 0 ]) b s
  ... | l , ns = "scan" , lift₁ (scanRows f z) l , ns
  listN u ρ π b (cutS true a s) with listS u ρ (π ++ [ 0 ]) b s
  ... | l , ns = "cut" , l , ns
  listN u ρ π b (cutS false a s) with listS u ρ (π ++ [ 0 ]) b s
  ... | _ , ns = "cut" , just ([] ⊣ false) , ns
  listN u ρ π b (lnS true s) with listS u ρ (π ++ [ 0 ]) b s
  ... | l , ns = "lane" , l , ns
  listN u ρ π b (lnS false s) with listS u ρ (π ++ [ 0 ]) b s
  ... | _ , ns = "lane" , just ([] ⊣ false) , ns
  listN u ρ π b (takeS i q w s) with listS u ρ (π ++ [ 0 ]) b s
  ... | l , ns = "take" , lift₁ (takeR i q w) l , ns
  listN u ρ π b (flatS op f d n q o ls) with listS u ρ (π ++ [ 0 ]) b o | listLs u ρ π b 1 ls
  ... | lo , no | lls , nls = opName op , bind lo (λ o′ → bind (allJust lls) λ Ls → joiner u ρ op f d n q o′ Ls) , no ++ nls
  listN u ρ π b (connS k o s) with listS u ρ (π ++ [ 0 ]) b o
  ... | nothing , no = "connect" , nothing , no
  ... | just σ , no with listT u (CS.src k) ρ (CS.connAt k ++ [ ix 1 ])
  ...   | nothing = "connect" , nothing , no
  ...   | just F with listS u (frozenHot k F σ ∷ ρ) (π ++ [ 1 ]) true s
  ...     | lb , nb = "connect" +++ parts lb , lift₁ (connRows (CS.connAt k) (gated k σ)) lb , no ++ nb
    where
      parts : ∀ {B} → Maybe (Listed B) → String
      parts nothing   = ""
      parts (just β) = " [source " +++ showRows (mapL erase (rows σ)) +++ "| body " +++ showRows (mapL erase (rows β)) +++ "]"
  listN u ρ π b (joinS j true x ib)  = "join" , just (let h = rejoin j (lookup ρ x) in (inbox ib ++ rows h) ⊣ short h) , []
  listN u ρ π b (joinS j false x ib) = "join" , just (inbox ib ⊣ false) , []
  listN u ρ π b _                    = "done" , just ([] ⊣ false) , []

  listLs : ∀ {Γ A} → ℕ → All Listed Γ → List ℕ → Bool → ℕ → List (St Γ A) → List (Maybe (Listed A)) × List Node
  listLs u ρ π b i []       = [] , []
  listLs u ρ π b i (s ∷ ls) with listS u ρ (π ++ [ i ]) b s | listLs u ρ π b (suc i) ls
  ... | l , ns | lls , nls = l ∷ lls , ns ++ nls

------------------------------------------------------------------------
-- The run, checked

-- A finding: the step, the node, its former as read at its entry, and
-- its rows outside that entry.
record Finding : Set where
  constructor finding
  field
    at    : ℕ
    nd    : Node
    was   : String
    extra : List (Pos × Kind)

private
  samePath : List ℕ → List ℕ → Bool
  samePath []       []       = true
  samePath (i ∷ is) (j ∷ js) = (i ≡ᵇ j) ∧ samePath is js
  samePath _        _        = false

  Entries : Set
  Entries = List (List ℕ × String × List (Pos × Kind) × Bool)

  entryOf : List ℕ → Entries → Maybe (String × List (Pos × Kind) × Bool)
  entryOf π []                  = nothing
  entryOf π ((π′ , e) ∷ es) = if samePath π π′ then just e else entryOf π es

  outside : List (Pos × Kind) → List (Pos × Kind) → List (Pos × Kind)
  outside e = concatMap λ r → when (not (anyᵇ (sameRow r) e)) r

  -- One settled tree's nodes against the entries, recording new ones.
  visit : ℕ → List Node → Entries → Entries × List Finding
  visit t []        es = es , []
  visit t (nd ∷ ns) es with Node.seen nd
  ... | nothing = visit t ns es
  ... | just (rs , sh) with entryOf (Node.path nd) es
  ...   | nothing = visit t ns ((Node.path nd , Node.former nd , rs , sh) ∷ es)
  ...   | just (_ , e , true) = visit t ns es
  ...   | just (w , e , false) with outside e rs | visit t ns es
  ...     | []    | es′ , fs = es′ , fs
  ...     | x ∷ xs | es′ , fs = es′ , finding t nd w (x ∷ xs) ∷ fs

  settled : ∀ {R} → Conf R → Bool
  settled c with Conf.mode c
  ... | rising _ = false
  ... | _        = true

  open module D = Driver ℕ using (step; silent; value; complete; drained)

  check : ℕ → ℕ → ℕ → Entries → Conf ℕ → List Finding
  check u zero    t es c = []
  check u (suc k) t es c = here (if settled c then visit t (proj₂ (listS u [] [] false (plug (Conf.ctx c) (Conf.foc c)))) es else es , [])
    where
      next : Entries → D.Step → List Finding
      next es′ (silent _ c′)    = check u k (suc t) es′ c′
      next es′ (value _ _ _ c′) = check u k (suc t) es′ c′
      next es′ _                = []

      here : Entries × List Finding → List Finding
      here (es′ , [])     = next es′ (step c)
      here (es′ , f ∷ fs) = f ∷ fs

-- The first findings of a seed's program, the run read for `k` steps.
probe : ℕ → ℕ → List Finding
probe k seed = let p = program seed in check (depth 3 p) k 0 [] (load (toObs timeline 3 p [] [] []))

------------------------------------------------------------------------
-- The report

private
  showPath : List ℕ → String
  showPath []       = ""
  showPath (i ∷ is) = showℕ i +++ "/" +++ showPath is

  showFinding : ℕ → Finding → String
  showFinding seed (finding t nd w xs) =
    "entry-check: FAIL seed " +++ showℕ seed +++ " step " +++ showℕ t +++ " node " +++ showPath (Node.path nd)
    +++ " " +++ Node.former nd +++ (if Node.body nd then " under-body" else " outside-body") +++ " rows " +++ showRows xs
    +++ "\n    at entry: " +++ w
  report : List ℕ → ℕ → IO Unit
  report []          bad = putStrLn ("entry-check: done " +++ showℕ bad +++ " failing seeds")
  report (seed ∷ ss) bad with probe 400 seed
  ... | []     = report ss bad
  ... | f ∷ fs = each (f ∷ fs) >>= λ _ → report ss (suc bad)
    where
      each : List Finding → IO Unit
      each []       = putStrLn ""
      each (x ∷ xs) = putStrLn (showFinding seed x) >>= λ _ → each xs

main : IO Unit
main = report (upTo 300) 0
