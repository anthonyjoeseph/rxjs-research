{-# OPTIONS --guardedness #-}

-- A RUN THE READER MEETS IS ITS SOURCE'S, JOINED LATE.  The reader is a
-- merge of its scan's lanes, so a run met of it is a prefix of the lanes
-- of a scan run reaching the anchor of its last row (`FlatLayer.found`).
-- That scan run is read off a run of the hot reaching the anchor, which
-- is the annotation's run past the reader's subscribe moved below it;
-- and the annotation's run is the source's, row by row (`ARows`).  The
-- scan's first state sends the joins before the first row it reads, each
-- later state the emit it read, so the lanes are the joins and then the
-- source's rows past the cut, each below its source row.
--
-- Where the hot ended past the subscribe, that the annotation's nothing
-- lies past it too (the reader is not in the last gap) is not refuted,
-- and the hot's end follows it: the lanes end below the source's end.
-- Where it ended at or before the subscribe, every row met is the late end.
module simultaneous.HeldBack where

open import Data.Bool using (true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Properties using (++-assoc; map-++; ∷ʳ-injective)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import Relation.Nullary as Nl

open import denotation.Position using (Pos; Label; ix; last; sub; _⊕_; _<ᵖ_; _≟ᵖ_; root)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Den; Ev; out; end; skip; pin; enter; hot; Proper; module Op; module Scan; _≺_; _≼_)
  renaming (ended to r-ended; late to r-late; shown to r-shown; heard to r-heard)
open import denotation.EmissionSet using (Rejoin)
open import denotation.Read using (Run; []; _∷_; Visible; After; cursor)
open import denotation.Laws.Rejoined using (lower; row-reach)
open import denotation.Events using (<ᵖ-down)
open import Data.Bool.Properties using (T-≡)
open import Function using (Equivalence)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import denotation.Laws.Worlds using (InvAt; Hots; Lawful; ok-step)
open import denotation.Laws.Modulus using (≺-irrefl; ≼-trans; ≺-trans; entered-few)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Relations using (Met; values)
open import simultaneous.Shut using (r₀)
open import simultaneous.Relabel using (RowsAt; []ᵃ; _∷ᵃ_)
open import simultaneous.HeldBase using (Bound; Ann; Gap)
open import simultaneous.HeldComb using (ev)
open import simultaneous.HeldRead using (Rl; Src; AnnEv; ann-just; ann-none)
open import simultaneous.LiveRuns using (pre-noend)
open import simultaneous.HeldRead using (ev-ann; cn-inv; z₀; CnO; Cn; ev-cn; Fm; module AnnConn; mv; last-mv; end-back; ev-g₀)
open import simultaneous.CombSent using (assoc³)
open import denotation.EmissionSet using (Few; module Connecting)
open import denotation.Laws.Fold using (fold)
open import denotation.Laws.Worlds using (conv; ⊑-snoc⁺; ⊑-≼; _⊑_; ⊑-refl; ⊕-identityʳ)
open import adequacy.Up using (conn-reach)
open import denotation.Laws.Modulus using (≼-or-≻; ≺→≼; ≼-≺-≺; ≼-split; ≺-ext; entered-reach)
open import simultaneous.DenRows using (map-out′)
open import simultaneous.ScanAcc using (module AccRun)
open import simultaneous.HeldConnect using (vis-dep)
open import simultaneous.HeldMap using (module MapRun; mapRows; mapRow)
open import simultaneous.LaneLocal using (inv-ev)
open import simultaneous.Layers using (module ScanLayer; scanRows; snoc-view; run-row; run-tail; run-after; run-past-end; to≺;
  snoc≢[])
open import simultaneous.Project using (run-prefix)
open import simultaneous.FlatLayer using (ofVals)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; count; annotate; annStep; joinStep)

------------------------------------------------------------------------
-- Runs and lists

-- A row moved below a reader subscribed at `p`.
mvh : ∀ {A : Set} → Pos → Pos × Ev A → Pos × Ev A
mvh p (y , e) = y ⊕ [ sub p ] , e

NoEnd : ∀ {A : Set} → List (Pos × Ev A) → Set
NoEnd rs = ∀ {w} → (w , end) ∈ rs → ⊥

-- Nothing follows an end.
EndLast : ∀ {A : Set} → List (Pos × Ev A) → Set
EndLast []                 = ⊤
EndLast ((_ , out _) ∷ rs) = EndLast rs
EndLast ((_ , end) ∷ rs)   = rs ≡ []
EndLast ((_ , skip) ∷ rs)  = EndLast rs
EndLast ((_ , pin _) ∷ rs) = EndLast rs

end-last : ∀ {A} {t : EmissionSet A} {c rs} → Run t c rs → EndLast rs
end-last []                                        = tt
end-last (_∷_ {e = out _} _ run)                   = end-last run
end-last (_∷_ {e = end} (((x , _) , _) , _) run)   = run-past-end x run
end-last (_∷_ {e = skip}  (_ , () , _) _)
end-last (_∷_ {e = pin _} (_ , () , _) _)

-- What is left of a source run past the rows a reader shows: nothing, or its end.
data Tl {A : Set} : List (Pos × Ev A) → Set where
  t-nil : Tl []
  t-end : ∀ {w} → Tl ((w , end) ∷ [])

tl-end : ∀ {A : Set} {sc′ rest : List (Pos × Ev A)} {w} → Tl rest → NoEnd sc′ → (w , end) ∈ sc′ ++ rest → rest ≡ (w , end) ∷ []
tl-end {sc′ = sc′} tl ne i with ∈-++⁻ sc′ i
... | inj₁ i′ = ⊥-elim (ne i′)
tl-end t-end ne i | inj₂ (here refl) = refl
tl-end t-end ne i | inj₂ (there ())

-- A scan of a run with no end is its prefix's scan, then the rest's.
scan-++ : ∀ {A B : Set} (f : B → A → B) b (rx ys : List (Pos × Ev A)) → NoEnd rx
        → Σ B λ b′ → scanRows f b (rx ++ ys) ≡ scanRows f b rx ++ scanRows f b′ ys
scan-++ f b []                 ys _  = b , refl
scan-++ f b ((q , out a) ∷ rx) ys ne with scan-++ f (f b a) rx ys (λ i → ne (there i))
... | b′ , eq = b′ , cong ((q , out (f b a)) ∷_) eq
scan-++ f b ((q , end) ∷ rx)   ys ne = ⊥-elim (ne (here refl))
scan-++ f b ((q , skip) ∷ rx)  ys ne = scan-++ f b rx ys (λ i → ne (there i))
scan-++ f b ((q , pin _) ∷ rx) ys ne = scan-++ f b rx ys (λ i → ne (there i))

scan-noend : ∀ {A B : Set} (f : B → A → B) b (rx : List (Pos × Ev A)) → NoEnd rx → NoEnd (scanRows f b rx)
scan-noend f b []                 ne ()
scan-noend f b ((q , out a) ∷ rx) ne (here ())
scan-noend f b ((q , out a) ∷ rx) ne (there i) = scan-noend f (f b a) rx (λ j → ne (there j)) i
scan-noend f b ((q , end) ∷ rx)   ne _         = ne (here refl)
scan-noend f b ((q , skip) ∷ rx)  ne i         = scan-noend f b rx (λ j → ne (there j)) i
scan-noend f b ((q , pin _) ∷ rx) ne i         = scan-noend f b rx (λ j → ne (there j)) i

ofVals-vals : ∀ {A : Set} q i (xs : List A) → L.map proj₂ (ofVals q i xs) ≡ L.map out xs
ofVals-vals q i []       = refl
ofVals-vals q i (x ∷ xs) = cong (out x ∷_) (ofVals-vals q (suc i) xs)

-- Each row one label below.
ofVals-at : ∀ {A : Set} q i (xs : List A) {y e} → (y , e) ∈ ofVals q i xs → Σ Label λ x → y ≡ q ⊕ [ x ]
ofVals-at q i []       ()
ofVals-at q i (x ∷ xs) (here refl) = ix i , refl
ofVals-at q i (x ∷ xs) (there m)   = ofVals-at q (suc i) xs m

-- A run met, cut where it passes `p`.
cut : ∀ {A} {t : EmissionSet A} p (ra : List (Pos × Ev A)) {c} → Run t c ra
    → Σ _ λ ra₁ → Σ _ λ ra₂ → ra ≡ ra₁ ++ ra₂ × (∀ {y e} → (y , e) ∈ ra₁ → y ≼ p) × (∀ {y e} → (y , e) ∈ ra₂ → p ≺ y)
cut p []             []         = [] , [] , refl , (λ ()) , (λ ())
cut p ((y , e) ∷ ra) (_ ∷ run) with p <ᵖ y in eq
... | true = [] , (y , e) ∷ ra , refl , (λ ()) , past
  where
    past : ∀ {y′ e′} → (y′ , e′) ∈ (y , e) ∷ ra → p ≺ y′
    past (here refl) = to≺ p y eq
    past (there i)   = ≺-trans {p} {y} (to≺ p y eq) (run-after run i)
... | false with cut p ra run
...   | ra₁ , ra₂ , refl , b₁ , b₂ = (y , e) ∷ ra₁ , ra₂ , refl , before , b₂
  where
    before : ∀ {y′ e′} → (y′ , e′) ∈ (y , e) ∷ ra₁ → y′ ≼ p
    before (here refl) py = subst T eq py
    before (there i)   = b₁ i

-- Prefixes.
pre-split : ∀ {B : Set} {rs′ : List B} js {M} → Prefix _≡_ rs′ (js ++ M)
          → Prefix _≡_ rs′ js ⊎ Σ B λ m → Σ (List B) λ M′ → rs′ ≡ js ++ m ∷ M′ × Prefix _≡_ (m ∷ M′) M
pre-split []       []         = inj₁ []
pre-split []       (eq ∷ pr)  = inj₂ (_ , _ , refl , eq ∷ pr)
pre-split (j ∷ js) []         = inj₁ []
pre-split (j ∷ js) (refl ∷ pr) with pre-split js pr
... | inj₁ pr′                = inj₁ (refl ∷ pr′)
... | inj₂ (m , M′ , refl , pr′) = inj₂ (m , M′ , refl , pr′)

nil-eq : ∀ {B : Set} {xs : List B} → Prefix _≡_ xs [] → xs ≡ []
nil-eq [] = refl

-- A prefix of rows paired is paired with a prefix.
at-pre : ∀ {A B : Set} {R : Pos → Pos → Set} {M₁ M : List (Pos × Ev (IE B))} {S : List (Pos × Ev (IE A))}
       → Prefix _≡_ M₁ M → RowsAt R M S → Σ _ λ S₁ → Σ _ λ ex → S ≡ S₁ ++ ex × RowsAt R M₁ S₁
at-pre {S = S} []         _          = [] , S , refl , []ᵃ
at-pre         (refl ∷ pr) (h ∷ᵃ at) with at-pre pr at
... | S₁ , ex , refl , at₁ = _ ∷ S₁ , ex , refl , h ∷ᵃ at₁

at-++ : ∀ {A B : Set} {R : Pos → Pos → Set} {M M′ : List (Pos × Ev (IE B))} {S S′ : List (Pos × Ev (IE A))}
      → RowsAt R M S → RowsAt R M′ S′ → RowsAt R (M ++ M′) (S ++ S′)
at-++ []ᵃ       a′ = a′
at-++ (h ∷ᵃ a) a′ = h ∷ᵃ at-++ a a′

------------------------------------------------------------------------
-- The annotation beside its source

-- AN ANNOTATED RUN BESIDE THE SOURCE RUN IT WRAPS: each annotated row
-- below its source row, carrying the routes counted before it.
data ARows {X : Set} : Routes → List (Pos × Ev (AIE X)) → List (Pos × Ev (IE X)) → Set where
  []ᴬ  : ∀ {c} → ARows c [] []
  _∷ᴬ_ : ∀ {c y w me e ra sc} → Rl y w × AnnEv me e → ARows (L.foldl count c (values ((w , e) ∷ []))) ra sc
       → ARows c ((y , out (c , me)) ∷ ra) ((w , e) ∷ sc)

ar-split : ∀ {X} {c} ra₁ {ra₂} {sc : List (Pos × Ev (IE X))} → ARows c (ra₁ ++ ra₂) sc
         → Σ _ λ sc₁ → Σ _ λ sc₂ → sc ≡ sc₁ ++ sc₂ × ARows (L.foldl count c (values sc₁)) ra₂ sc₂
ar-split []         ar                 = [] , _ , refl , ar
ar-split (_ ∷ ra₁) ((r , ann-just) ∷ᴬ ar) with ar-split ra₁ ar
... | sc₁ , sc₂ , refl , ar₂ = _ ∷ sc₁ , sc₂ , refl , ar₂
ar-split (_ ∷ ra₁) ((r , ann-none) ∷ᴬ ar) with ar-split ra₁ ar
... | sc₁ , sc₂ , refl , ar₂ = _ ∷ sc₁ , sc₂ , refl , ar₂

-- An annotated nothing stands beside the source's end.
ar-none : ∀ {X} {c ra} {sc : List (Pos × Ev (IE X))} {y r} → ARows c ra sc → (y , out (r , nothing)) ∈ ra → Σ Pos λ w → (w , end) ∈ sc
ar-none ((_ , ann-none) ∷ᴬ _)  (here refl) = _ , here refl
ar-none ((_ , ann-just) ∷ᴬ _)  (here ())
ar-none (_ ∷ᴬ ar)              (there i) with ar-none ar i
... | w , j = w , there j

-- PAST A READER'S SUBSCRIBE, A HOT SHOWS ITS SOURCE'S RUN, MOVED BELOW:
-- rows moved a label down keep their order, both ways (`raise`, `lower`),
-- and no end lies at or before the subscribe once a row lies past it.
module LateIn {A} {t : EmissionSet A} (L : Lawful (Proper t)) (p : Pos) where
  H : EmissionSet A
  H = enter (hot (Proper t)) p

  s : Pos → Pos
  s k = k ⊕ [ sub p ]

  raise : ∀ {k q e e′} → Proper t k e → Proper t q e′ → k ≺ q → s k ≺ s q
  raise {k} {q} {e} {e′} y x kq =
    Equivalence.from T-≡ (<ᵖ-down k q (sub p) (sub p) (Equivalence.to T-≡ kq) (λ l ls eq → Lawful.flat L y (subst (λ z → Proper t z e′) eq x)))

  -- Where the source's reader and the hot's stand, against the rows past `p`.
  Cur : Maybe Pos → Maybe Pos → Set
  Cur c c′ = (∀ {k e} → Proper t k e → p ≺ k → After c k → After c′ (s k))
           × (∀ {k e} → Proper t k e → p ≺ k → After c′ (s k) → After c k)

  go : ∀ {c c′ ra} → Run t c ra → Cur c c′ → (∀ {y e} → (y , e) ∈ ra → p ≺ y) → Run H c′ (L.map (mvh p) ra)
  go [] _ _ = []
  go {c} {c′} (_∷_ {q = q} {e = e} ((xp , few) , vi , aft , lst) run) (fw , bw) past =
    ((((rjv xp vi , row-reach L xp fewP pq) , prop) , fewH) , vi , fw xp pq aft , least) ∷ go run (fw′ , bw′) (λ i → past (there i))
    where
      pq : p ≺ q
      pq = past (here refl)

      no-late : ∀ {c₀} → Proper t c₀ end → c₀ ≼ p → ⊥
      no-late {c₀} y cp = ≼-trans {q} {c₀} {p} (Lawful.proper L y xp) cp pq

      fewP : Few (Proper t) q
      fewP = proj₁ few , λ z lt → proj₂ few (proj₁ z) lt

      rjv : ∀ {e₁} → Proper t q e₁ → Visible e₁ → Rejoin p (Proper t) (s q) e₁
      rjv {out _} x _ = r-shown x tt pq
      rjv {end}   x _ = r-ended x pq
      rjv {skip}  _ ()
      rjv {pin _} _ ()

      prop : ∀ {c₀} → H c₀ end → s q ≼ c₀
      prop (r-shown _ () _ , _)
      prop (r-ended y _ , _) lt = Lawful.proper L y xp (lower L xp y lt)
      prop (r-late y cp , _) _  = no-late y cp

      fewH : Few H (s q)
      fewH = L.map s (proj₁ few) , pick
        where
          pick : ∀ {k e′} → H k e′ → k ≺ s q → k ∈ L.map s (proj₁ few)
          pick (r-shown y _ _ , _) lt = ∈-map⁺ s (proj₂ few (proj₁ y) (lower L xp y lt))
          pick (r-heard y _ , _)   lt = ∈-map⁺ s (proj₂ few (proj₁ y) (lower L xp y lt))
          pick (r-ended y _ , _)   lt = ∈-map⁺ s (proj₂ few (proj₁ y) (lower L xp y lt))
          pick (r-late y cp , _)   _  = ⊥-elim (no-late y cp)

      least : ∀ {k e′} → H k e′ → Visible e′ → After c′ k → s q ≼ k
      least (r-shown y _ pk , _) v ak lt = lst (proj₁ y) v (bw y pk ak) (lower L xp y lt)
      least (r-heard _ _ , _)    () _
      least (r-ended y pk , _)   v ak lt = lst (proj₁ y) v (bw y pk ak) (lower L xp y lt)
      least (r-late y cp , _)    _ _ _ = no-late y cp

      fw′ : ∀ {k e₁} → Proper t k e₁ → p ≺ k → After (just q) k → After (just (s q)) (s k)
      fw′ y _ qk = raise xp y qk

      bw′ : ∀ {k e₁} → Proper t k e₁ → p ≺ k → After (just (s q)) (s k) → After (just q) k
      bw′ y _ lt = lower L y xp lt

  -- A reader past the run before the subscribe stands before every row past it.
  cur : ∀ c (ra₁ : List (Pos × Ev A)) → (∀ {k} → p ≺ k → After c k) → (∀ {y e} → (y , e) ∈ ra₁ → y ≼ p) → ∀ {k} → p ≺ k → After (cursor c ra₁) k
  cur c []             h _ pk = h pk
  cur c ((y , _) ∷ ra) h b pk = cur (just y) ra (λ {k} pk′ → ≼-≺-≺ {y} {p} {k} (b (here refl)) pk′) (λ i → b (there i)) pk

opaque
  late-in : ∀ {A} {t : EmissionSet A} → Lawful (Proper t) → ∀ p {ra₁ ra₂} → Met t (ra₁ ++ ra₂)
          → (∀ {y e} → (y , e) ∈ ra₁ → y ≼ p) → (∀ {y e} → (y , e) ∈ ra₂ → p ≺ y)
          → Met (enter (hot (Proper t)) p) (L.map (mvh p) ra₂)
  late-in L p {ra₁} m b₁ b₂ =
    LateIn.go L p (run-tail ra₁ m) ((λ _ _ _ → tt) , (λ _ pk _ → LateIn.cur L p nothing ra₁ (λ _ → tt) b₁ pk)) b₂

-- A RUN'S LAST ROW IS THE ROW AT ITS POSITION.
last-fix : ∀ {A} {t : EmissionSet A} → (∀ {y e e′} → t y e → t y e′ → e ≡ e′) → ∀ {ra q e e′}
         → Met t (ra ++ [ (q , e′) ]) → t q e → Met t (ra ++ [ (q , e) ])
last-fix {t = t} fu {ra} {q} m x with fu (proj₁ (run-row m (∈-++⁺ʳ ra (here refl)))) x
... | refl = m

-- EVERY ANNOTATED VALUE IS THE LAST ROW OF A RUN MET OF THE ANNOTATION:
-- its fold names a run met of the connect up to it (`AccRun`), scanned
-- and mapped row for row.
module AnnRun {X} {d : Den (AIE X)} {cs} (b : Bound d cs) where
  a₁ : Pos
  a₁ = Bound.at b ⊕ [ ix 1 ]

  C : Den (Maybe (IE X))
  C = ev (Bound.m b) (CnO (Bound.src b)) (Bound.env b)

  Sa : Den (Routes × AIE X)
  Sa = Op.scan annStep z₀ C

  eqA : ev (Bound.m b) (annotate (Bound.src b)) (Bound.env b) ≡ Op.map proj₂ Sa
  eqA = ev-ann (Bound.m b) (Bound.src b) (Bound.env b)

  IA : InvAt (Hots (Bound.env b)) a₁ (Ann b)
  IA = inv-ev (Bound.m b) (annotate (Bound.src b)) (Bound.env b) (Bound.good b) a₁ (ok-step (Bound.at b) (Bound.ok b))

  module MR = MapRun proj₂ Sa a₁

  run : ∀ {q x} → Ann b q (out x) → Σ _ λ ra → Met (Ann b) (ra ++ [ (q , out x) ])
  run {q} {x} aq with map-out′ proj₂ Sa a₁ (subst (λ D′ → enter D′ a₁ q (out x)) eqA aq)
  ... | _ , (Scan.sval ac , _) , _
    with AccRun.acc-run annStep z₀ (cn-inv b) (λ y v → entered-few C a₁ (vis-dep v) y) ac
  ...   | rx , a , _ , runC , _
    with ScanLayer.in-go annStep z₀ C a₁ (InvAt.func (cn-inv b)) ScanLayer.none runC
       | scan-++ annStep z₀ rx [ (q , out a) ] (pre-noend rx runC)
  ...     | _ , mSa , _ , _ , refl | b′ , eqs =
    mapRows proj₂ (scanRows annStep z₀ rx) ,
    last-fix (InvAt.func IA)
      (subst (λ D′ → Met (enter D′ a₁) (mapRows proj₂ (scanRows annStep z₀ rx) ++ mapRows proj₂ (scanRows annStep b′ [ (q , out a) ]))) (sym eqA)
        (subst (Met (enter (Op.map proj₂ Sa) a₁)) (map-++ (mapRow proj₂) (scanRows annStep z₀ rx) (scanRows annStep b′ [ (q , out a) ]))
          (MR.fwd (subst (Met (enter Sa a₁)) eqs mSa))))
      aq

ann-run : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) {q x} → Ann b q (out x) → Σ _ λ ra → Met (Ann b) (ra ++ [ (q , out x) ])
ann-run b = AnnRun.run b

-- THE ANNOTATION'S VALUES ARE ITS CONNECT'S, each with its fold: the
-- source's values, then the nothing that closes it (`CatRuns`).  A fold
-- is not refuted where few rows precede (`denotation.Laws.Fold.fold`),
-- and no more: which rows precede may hang on an older hot's synchronous
-- loop no row of this one shows.  So the nothing is the last value, and
-- lies where the end's last gap opens.
module AnnVals {X} {d : Den (AIE X)} {cs} (b : Bound d cs) where
  open AnnRun b using (a₁; C; Sa; eqA)
  module AC = AnnConn b
  module MS = MapRun proj₂ Sa a₁
  module SL = ScanLayer annStep z₀ C a₁ (InvAt.func (cn-inv b))
  open Scan annStep z₀ (Cn b) using (Acc; acc₀; acc; sval; send)

  evc : ev (Bound.m b) (CnO (Bound.src b)) (Bound.env b) ≡ Op.connect (Op.map just (ev (Bound.m b) (Bound.src b) (Bound.env b))) (Fm (Bound.m b) (Bound.env b))
  evc = ev-cn (Bound.m b) (Bound.src b) (Bound.env b)

  to-ann : ∀ {k st} → Acc k st → Ann b k (out (proj₂ st))
  to-ann {k} {st} ac = subst (λ D′ → enter D′ a₁ k (out (proj₂ st))) (sym eqA) (MS.lift (SL.toSc (sval ac)))

  from-ann : ∀ {k x} → Ann b k (out x) → Σ _ λ st → Acc k st × x ≡ proj₂ st
  from-ann {k} {x} aq with MS.unmap (subst (λ D′ → enter D′ a₁ k (out x)) eqA aq)
  ... | out st , (sval ac , _) , refl = st , ac , refl
  ... | skip , _ , ()
  ... | pin _ , _ , ()
  ... | end , _ , ()

  cn-of : ∀ {k st} → Acc k st → Σ _ λ st₀ → Σ _ λ a → Cn b k (out a) × st ≡ annStep st₀ a
  cn-of (acc₀ x _)              = z₀ , _ , x , refl
  cn-of (acc {b = st₀} _ x _ _) = st₀ , _ , x , refl

  ann-in : ∀ {st₀ : Routes × AIE X} {a r me} → (r , me) ≡ proj₂ (annStep st₀ a) → a ≡ me
  ann-in {a = just _}  refl = refl
  ann-in {a = nothing} refl = refl

  -- An annotated value is the connect's value it read.
  ann-cn : ∀ {k r me} → Ann b k (out (r , me)) → Cn b k (out me)
  ann-cn {k} aq with from-ann aq
  ... | st , ac , eq with cn-of ac
  ...   | st₀ , a , x , refl = subst (λ a′ → Cn b k (out a′)) (ann-in {st₀} {a} eq) x

  -- A value of the connect is its closed body's.
  cn-u : ∀ {y x} → Cn b y (out x) → AC.CT.U y (out x)
  cn-u {y} {x} cx with subst (λ D′ → enter D′ a₁ y (out x)) evc cx
  ... | (Connecting.body z , _) = AC.CT.row z

  -- The source shows only values wrapped.
  src-just : ∀ {y} → AC.CT.R y (out nothing) → ⊥
  src-just y with AC.HR.src-vis (proj₁ (AC.to y)) tt
  ... | _ , _ , sk with AC.MR.unmap (proj₁ sk)
  ...   | out _ , _ , ()
  ...   | skip , _ , ()
  ...   | pin _ , _ , ()
  ...   | end , _ , ()

  none-last : ∀ {m r j a} → Ann b m (out (r , nothing)) → Ann b j (out a) → m ≺ j → ⊥
  none-last am ak mj = go mj (cn-u (ann-cn am)) (cn-u (ann-cn ak))
    where
      go : ∀ {m′ j′ x} → m′ ≺ j′ → AC.CT.U m′ (out nothing) → AC.CT.U j′ (out x) → ⊥
      go _ (AC.CT.src y _) _ = src-just y
      go {j′ = j′} mj′ (AC.CT.mk {cb} yc) (AC.CT.src y′ ne) =
        ≺-irrefl {cb} (≺-trans {cb} {j′} {cb} (≺-trans {cb} {AC.CT.mpos cb} {j′} (AC.CT.c≺m cb) mj′) (AC.CT.before y′ ne yc))
      go mj′ (AC.CT.mk {cb} yc) (AC.CT.mk yc′) with AC.CT.uniq yc yc′
      ... | refl = ≺-irrefl {AC.CT.mpos cb} mj′

  -- The annotation's end is the closed body's, past its mark.
  cn-end : ∀ {c} → Ann b c end → Σ Pos λ cb → AC.CT.R cb end × Cn b c end × c ≡ AC.CT.fpos cb
  cn-end {c} ce with MS.unmap (subst (λ D′ → enter D′ a₁ c end) eqA ce)
  ... | out _ , _ , ()
  ... | skip , _ , ()
  ... | pin _ , _ , ()
  ... | end , (Scan.send t , _) , refl with subst (λ D′ → enter D′ a₁ c end) evc t
  ...   | (Connecting.body z , _) with AC.CT.end-row z
  ...     | AC.CT.src _ ne = ⊥-elim (ne refl)
  ...     | AC.CT.fin yc   = _ , yc , t , refl

  mark : ∀ {cb} → AC.CT.R cb end → Cn b (AC.CT.fpos cb) end → Cn b (AC.CT.mpos cb) (out nothing)
  mark {cb} yc ce = subst (λ D′ → enter D′ a₁ (AC.CT.mpos cb) (out nothing)) (sym evc)
    (AC.CR.lift (subst (λ D′ → enter D′ a₁ (AC.CT.fpos cb) end) evc ce) tt (AC.CT.lift (AC.CT.mk yc)) (AC.CT.m≺f cb))

  -- A value of the connect has its fold, not refuted.
  fold-ann : ∀ {w a} → Cn b w (out a) → Nl.¬ Nl.¬ (Σ _ λ st₀ → Acc w (annStep st₀ a))
  fold-ann x = fold annStep z₀ (Cn b) (entered-few C a₁ tt x) x

  gap : ∀ p → Nl.¬ Gap b p → ∀ {c} → Ann b c end → p ≺ c
      → Nl.¬ Nl.¬ (Σ Pos λ m → Σ Routes λ r → Ann b m (out (r , nothing)) × p ≺ m)
  gap p ng {c} ce pc k with cn-end ce
  ... | cb , yc , ce′ , refl = fold-ann (mark yc ce′) at
    where
      at : Nl.¬ (Σ _ λ st₀ → Acc (AC.CT.mpos cb) (annStep st₀ nothing))
      at (st₀ , ac) with ≼-or-≻ (AC.CT.mpos cb) p
      ... | inj₂ pm = k (AC.CT.mpos cb , proj₁ (annStep st₀ nothing) , to-ann ac , pm)
      ... | inj₁ mp = ng (cb , proj₁ (annStep st₀ nothing) , to-ann ac ,
                        conv {cb ⊕ [ ix 1 ]} {AC.CT.mpos cb} {p} {AC.CT.fpos cb} (⊑-snoc⁺ (cb ⊕ [ ix 1 ])) mp pc (⊑-snoc⁺ (cb ⊕ [ ix 1 ])) ,
                        λ fp → ⊑-≼ fp pc)

  -- THE SOURCE ROWS BEFORE ANYTHING UNDER A ROW of it are its rows up to
  -- that row: none lies under it.
  few-under : ∀ {k e} → AC.σ k e → Few AC.σ k → ∀ {F} → k ⊑ F
            → Σ (List Pos) λ ys → ∀ {y e′} → AC.σ y e′ → (y ⊕ [ ix 0 ]) ≺ F → y ∈ ys
  few-under {k} σk ks {F} kF = k ∷ proj₁ ks , pick
    where
      pick : ∀ {y e′} → AC.σ y e′ → (y ⊕ [ ix 0 ]) ≺ F → y ∈ (k ∷ proj₁ ks)
      pick {y} sy lt with ≼-or-≻ y k
      ... | inj₁ yk with ≼-split {y} {k} yk
      ...   | inj₁ y<k = there (proj₂ ks sy y<k)
      ...   | inj₂ refl = here refl
      pick {y} sy lt | inj₂ ky with conv {k} {k} {y} {F} (⊑-refl k) (≺→≼ {k} {y} ky) (≺-trans {y} {y ⊕ [ ix 0 ]} {F} (≺-ext y []) lt) kF
      ... | [] , eq = ⊥-elim (≺-irrefl {k} (subst (k ≺_) (trans eq (⊕-identityʳ k)) ky))
      ... | (_ ∷ _) , eq = ⊥-elim (InvAt.flat AC.Iσ σk (subst (λ z → AC.σ z _) eq sy))

  -- A row of the closed body under a source row is the connect's.
  body-cnᶠ : ∀ {k e F e′} → AC.σ k e → Few AC.σ k → k ⊑ F → AC.CT.C F e′ → Cn b F e′
  body-cnᶠ {k} {e} {F} {e′} σk fk kF xk = subst (λ D′ → enter D′ a₁ F e′) (sym evc)
    (Connecting.body xk , conn-reach {r = a₁} {e = e′} (few-under σk fk kF)
      (entered-reach (Fm (Bound.m b) {X = X} (Bound.env b) (hot (Proper AC.σ))) (a₁ ⊕ [ ix 0 ]) xk))

  body-cn : ∀ {k e F e′} → AC.σ k e → Visible e → k ⊑ F → AC.CT.C F e′ → Cn b F e′
  body-cn σk v = body-cnᶠ σk (AC.few-vis σk v)

  -- The source's reading, as the closed body reads it.
  rd-r : ∀ {y e} → AC.HR.Rd y e → AC.CT.R y e
  rd-r {y} {e} = subst (λ D′ → enter D′ AC.sb y e) (sym (ev-g₀ (Bound.m b) (Bound.env b) (hot (Proper AC.σ))))

  -- THE BODY'S END PAST THE MARK IS THE CONNECT'S.
  fin-at : ∀ {cb} → AC.CT.R cb end → ∀ k → cb ≡ AC.HR.shift k → AC.σ k end → Ann b (AC.CT.fpos cb) end
  fin-at {cb} yc k refl σk =
    subst (λ D′ → enter D′ a₁ (AC.CT.fpos cb) end) (sym eqA)
      (MS.lift (SL.toSc (send (body-cn σk tt (_ , assoc³ k (sub AC.sb) (ix 1) last) (AC.CT.lift (AC.CT.fin yc))))))

  -- A SOURCE VALUE IS ANNOTATED where the closed body reads it.
  show-val : ∀ {k x} → Src b k (out x) → Nl.¬ Nl.¬ (Σ Routes λ r → Ann b (k ⊕ [ sub AC.sb ]) (out (r , just x)))
  show-val {k} {x} sk h = fold-ann cw λ sa → h (_ , to-ann (proj₂ sa))
    where
      σk : AC.σ k (out (just x))
      σk = AC.MR.lift sk

      cw : Cn b (k ⊕ [ sub AC.sb ]) (out (just x))
      cw = body-cn σk tt ([ sub AC.sb ] , refl) (AC.CT.lift (AC.CT.src (rd-r (AC.HR.lift-vis σk tt)) (λ ())))

  -- THE SOURCE'S END IS ANNOTATED by the nothing past it, then the end.
  show-end : ∀ {k} → Src b k end
           → Nl.¬ Nl.¬ (Σ Routes λ r → Ann b (AC.CT.mpos (AC.HR.shift k)) (out (r , nothing)) × Ann b (AC.CT.fpos (AC.HR.shift k)) end)
  show-end {k} sk h = fold-ann (mark yc ce) λ sa → h (_ , to-ann (proj₂ sa) , ae)
    where
      σk : AC.σ k end
      σk = AC.MR.lift sk

      yc : AC.CT.R (AC.HR.shift k) end
      yc = rd-r (AC.HR.lift-vis σk tt)

      ae : Ann b (AC.CT.fpos (AC.HR.shift k)) end
      ae = fin-at yc k refl σk

      ce : Cn b (AC.CT.fpos (AC.HR.shift k)) end
      ce = proj₁ (proj₂ (proj₂ (cn-end ae)))

  fin : ∀ {m r} → Ann b m (out (r , nothing)) → Σ Pos λ c → Ann b c end × m ≺ c
  fin am with cn-u (ann-cn am)
  ... | AC.CT.src y _ = ⊥-elim (src-just y)
  ... | AC.CT.mk {cb} yc with AC.HR.src-vis (proj₁ (AC.to yc)) tt
  ...   | k , eq , σk = AC.CT.fpos cb , fin-at yc k eq (proj₁ σk) , AC.CT.m≺f cb

-- Out of the last gap, the annotation's nothing lies past a reader its end
-- does: not refuted, since its fold is no more.
ann-gap : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p → Nl.¬ Gap b p → ∀ {c} → Ann b c end → p ≺ c
        → Nl.¬ Nl.¬ (Σ Pos λ m → Σ Routes λ r → Ann b m (out (r , nothing)) × p ≺ m)
ann-gap b = AnnVals.gap b

-- The annotation's nothing is its last value.
ann-last : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) {m r j a} → Ann b m (out (r , nothing)) → Ann b j (out a) → m ≺ j → ⊥
ann-last b = AnnVals.none-last b

-- A source value is annotated below it, not refuted.
src-ann : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) {k x} → Src b k (out x)
        → Nl.¬ Nl.¬ (Σ Routes λ r → Ann b (k ⊕ [ sub (AnnConn.sb b) ]) (out (r , just x)))
src-ann b = AnnVals.show-val b

-- The source's end is annotated below it, not refuted: the nothing, then
-- the end.
src-ann-end : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) {k} → Src b k end
            → Nl.¬ Nl.¬ (Σ Routes λ r → Ann b (((k ⊕ [ sub (AnnConn.sb b) ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) (out (r , nothing))
                                     × Ann b (((k ⊕ [ sub (AnnConn.sb b) ]) ⊕ [ ix 1 ]) ⊕ [ last ]) end)
src-ann-end b = AnnVals.show-end b

-- The annotation's nothing is followed by its end.
ann-fin : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) {m r} → Ann b m (out (r , nothing))
        → Σ Pos λ c → Ann b c end × m ≺ c
ann-fin b = AnnVals.fin b

------------------------------------------------------------------------
-- The annotation's run, read back

-- A RUN MET OF THE CONNECT BESIDE THE SOURCE RUN IT SHOWS: each value a
-- source row wrapped, or the nothing beside its end.
data CRows {X : Set} : List (Pos × Ev (Maybe (IE X))) → List (Pos × Ev (IE X)) → Set where
  []ᶜ  : CRows [] []
  _∷ᶜ_ : ∀ {y w me e rc sc} → Rl y w × AnnEv me e → CRows rc sc → CRows ((y , out me) ∷ rc) ((w , e) ∷ sc)

crows-++ : ∀ {X} {rc rc′} {sc sc′ : List (Pos × Ev (IE X))} → CRows rc sc → CRows rc′ sc′ → CRows (rc ++ rc′) (sc ++ sc′)
crows-++ []ᶜ        c′ = c′
crows-++ (h ∷ᶜ c) c′ = h ∷ᶜ crows-++ c c′

-- A source run with no end, moved, is the connect's beside it.
crows-mv : ∀ {X} {t : EmissionSet (IE X)} {c} s (sc : List (Pos × Ev (IE X))) → Run t c sc → NoEnd sc → CRows (L.map (mv s) sc) sc
crows-mv s []                      []                        _  = []ᶜ
crows-mv s ((_ , out _) ∷ sc)      (_ ∷ run)                 ne = (([ sub s ] , refl) , ann-just) ∷ᶜ crows-mv s sc run (λ i → ne (there i))
crows-mv s ((_ , end) ∷ sc)        (_ ∷ run)                 ne = ⊥-elim (ne (here refl))
crows-mv s ((_ , skip) ∷ sc)       ((_ , () , _) ∷ _)        _
crows-mv s ((_ , pin _) ∷ sc)      ((_ , () , _) ∷ _)        _

-- Before a run's last row, no end.
endlast-snoc : ∀ {A : Set} (pre : List (Pos × Ev A)) {x} → EndLast (pre ++ [ x ]) → NoEnd pre
endlast-snoc [] _ ()
endlast-snoc ((_ , out _) ∷ pre) el (there i) = endlast-snoc pre el i
endlast-snoc ((_ , skip) ∷ pre)  el (there i) = endlast-snoc pre el i
endlast-snoc ((_ , pin _) ∷ pre) el (there i) = endlast-snoc pre el i
endlast-snoc ((_ , end) ∷ pre) el _ = snoc≢[] pre _ el

-- Each annotated row of a connect run beside its source's.
ar-of : ∀ {X} {c a rc} {sc : List (Pos × Ev (IE X))} → CRows rc sc → ARows c (mapRows proj₂ (scanRows annStep (c , a) rc)) sc
ar-of []ᶜ                    = []ᴬ
ar-of ((r , ann-just) ∷ᶜ cr) = (r , ann-just) ∷ᴬ ar-of cr
ar-of ((r , ann-none) ∷ᶜ cr) = (r , ann-none) ∷ᴬ ar-of cr

module AnnSrc {X} {d : Den (AIE X)} {cs} (b : Bound d cs) where
  open AnnRun b using (a₁; C; Sa; eqA)
  module AC = AnnConn b
  module MS = MapRun proj₂ Sa a₁
  module SL = ScanLayer annStep z₀ C a₁ (InvAt.func (cn-inv b))

  -- THE CONNECT'S RUN, ENDING ON A VALUE, beside its source's: the source
  -- read whole, or read to its end and closed by the nothing.
  shape-rows : ∀ {rs} → AC.CT.Shape nothing rs → ∀ {rx q me} → rs ≡ rx ++ [ (q , out me) ] → Σ _ λ sc → Met (Src b) sc × CRows rs sc
  shape-rows (AC.CT.open′ run _) eq with AC.src-run run
  ... | sc , srun , refl with last-mv AC.sb sc (sym eq)
  ...   | pre , w , out a , refl , _ , _ , _ = pre ++ [ (w , out a) ] , srun , crows-mv AC.sb (pre ++ [ (w , out a) ]) srun ne
    where
      ne : NoEnd (pre ++ [ (w , out a) ])
      ne i with ∈-++⁻ pre i
      ... | inj₁ i′         = endlast-snoc pre (end-last srun) i′
      ... | inj₂ (here ())
      ... | inj₂ (there ())
  ...   | pre , w , end , refl , _ , _ , ()
  ...   | pre , w , skip , refl , _ , _ , ()
  ...   | pre , w , pin _ , refl , _ , _ , ()
  shape-rows (AC.CT.shut {cb} {r} run yc AC.CT.t-none) _ with AC.src-run run
  ... | sc , srun , eq₂ with last-mv AC.sb sc eq₂
  ...   | pre , w , e₀ , refl , refl , refl , ee with end-back e₀ ee
  ...     | refl = pre ++ [ (w , end) ] , srun ,
                   crows-++ (crows-mv AC.sb pre (run-prefix pre srun) (endlast-snoc pre (end-last srun)))
                     (((_ , assoc³ w (sub AC.sb) (ix 1) (ix 0)) , ann-none) ∷ᶜ []ᶜ)
  shape-rows (AC.CT.shut {cb} {r} run yc AC.CT.t-fin) {rx} eq
    with ∷ʳ-injective (r ++ [ (AC.CT.mpos cb , out nothing) ]) rx (trans (++-assoc r [ (AC.CT.mpos cb , out nothing) ] [ (AC.CT.fpos cb , end) ]) eq)
  ... | _ , ()

  -- The last row of a connect run whose annotation ends on a value is one.
  last-val : ∀ {ra rx b′ y q x} e₁ → Met (enter C a₁) (rx ++ [ (y , e₁) ])
           → ra ++ [ (q , out x) ] ≡ mapRows proj₂ (scanRows annStep z₀ rx) ++ mapRows proj₂ (scanRows annStep b′ [ (y , e₁) ])
           → Σ (Maybe (IE X)) λ me → e₁ ≡ out me × y ≡ q
  last-val {ra} (out me) _ eq with ∷ʳ-injective ra _ eq
  ... | _ , refl = me , refl , refl
  last-val {ra} end _ eq with ∷ʳ-injective ra _ eq
  ... | _ , ()
  last-val {rx = rx} skip r′ _ with proj₂ (run-row r′ (∈-++⁺ʳ rx (here refl)))
  ... | ()
  last-val {rx = rx} (pin _) r′ _ with proj₂ (run-row r′ (∈-++⁺ʳ rx (here refl)))
  ... | ()

  -- A run met of the annotation, ending on a value, is the connect's
  -- scanned and mapped, so its source's row by row.
  src : ∀ {ra q x} → Met (Ann b) (ra ++ [ (q , out x) ]) → Σ _ λ sc → Met (Src b) sc × ARows r₀ (ra ++ [ (q , out x) ]) sc
  src {ra} {q} {x} m with MS.back (subst (λ D′ → Met (enter D′ a₁) (ra ++ [ (q , out x) ])) eqA m)
  ... | sa , runSa , eqa with SL.out-go SL.none runSa
  ...   | rc , runC , _ , _ , refl with snoc-view rc
  ...     | inj₁ refl = ⊥-elim (snoc≢[] ra _ eqa)
  ...     | inj₂ (rx , (y , e) , refl) with scan-++ annStep z₀ rx [ (y , e) ] (pre-noend rx runC)
  ...       | b′ , eqs with last-val {ra} {rx} {b′} e runC (trans eqa (trans (cong (mapRows proj₂) eqs) (map-++ (mapRow proj₂) (scanRows annStep z₀ rx) (scanRows annStep b′ [ (y , e) ]))))
  ...         | me , refl , refl with shape-rows (AC.CT.shape₀ (AC.CT.back (AC.CR.back (AC.cn runC)))) refl
  ...           | sc , srun , cr = sc , srun , subst (λ R → ARows r₀ R sc) (sym eqa) (ar-of cr)

-- A run met of the annotation is its source's, row by row.
opaque
  ann-src : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) {ra q x} → Met (Ann b) (ra ++ [ (q , out x) ])
          → Σ _ λ sc → Met (Src b) sc × ARows r₀ (ra ++ [ (q , out x) ]) sc
  ann-src b = AnnSrc.src b

------------------------------------------------------------------------
-- The reader, read back
