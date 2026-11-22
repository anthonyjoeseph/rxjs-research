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
-- Where the hot ended past the subscribe, the annotation's nothing lies
-- past it too (the reader is not in the last gap), and the hot's end
-- follows it: the lanes end below the source's end.  Where it ended at or
-- before the subscribe, every row met is the late end.
module simultaneous.HeldBack where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Properties using (++-assoc; ++-identityʳ; map-++; ∷ʳ-injective)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import Relation.Nullary as Nl

open import denotation.Position using (Pos; ix; last; sub; _⊕_; _<ᵖ_; _≟ᵖ_; root)
open import denotation.Events using (Timeline; fresh; inside-self)
open import denotation.EmissionSet using (EmissionSet; Den; Ev; out; end; skip; pin; enter; hot; Proper; module Op; module Scan; _≺_; _≼_)
  renaming (ended to r-ended; late to r-late; shown to r-shown; heard to r-heard)
open import denotation.EmissionSet using (Rejoin)
open import denotation.Read using (Run; []; _∷_; Visible; After; cursor)
open import denotation.Laws.Rejoined using (lower; row-reach)
open import denotation.Events using (<ᵖ-down)
open import Data.Bool.Properties using (T-≡)
open import Function using (Equivalence)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import denotation.Laws.Worlds using (InvAt; Hots; Lawful; PinBy; ok-step)
open import denotation.Laws.Modulus using (≼-split; ≼-antisym; ≺-irrefl; ≺-≼-≺; ≼-trans; ≺-trans; entered-few)
open import denotation.Laws.HotInv using (hot-func; hot-flat; hot-quiet)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Relations using (Met; values)
open import simultaneous.Routed using (cnt; Ex)
open import simultaneous.Shut using (r₀)
open import simultaneous.Relabel using (RowsAt; []ᵃ; _∷ᵃ_; ev-out; ev-end)
open import simultaneous.HeldConnect using (same-refl)
open import simultaneous.HeldTake using (ex-ext)
open import simultaneous.HeldBase using (Bound; Ann; Gap)
open import simultaneous.HeldComb using (ev)
open import simultaneous.HeldJoin using (Joined; j-late; j-part; j-read; jl; js-begins; Begins)
open import simultaneous.HeldRead using (RD; Rl; Src; s₀; Rl-trans; AnnEv; ann-just; ann-none; ann-end; pre-noend; JS)
open import simultaneous.HeldRead using (ev-ann; cn-inv; z₀; CnO; Cn; ev-cn; Fm; module AnnConn; mv; last-mv; end-back; snoc≢[])
open import simultaneous.CombSent using (assoc³)
open import denotation.EmissionSet using (Few; module Connecting)
open import denotation.Laws.Fold using (fold)
open import denotation.Laws.Worlds using (conv; ⊑-snoc⁺; ⊑-≼)
open import denotation.Laws.Modulus using (≼-or-≻; ≼-refl; ≺→≼; ≼-≺-≺)
open import Relation.Nullary using (Dec; yes; no)
open import simultaneous.DenRows using (map-out′)
open import simultaneous.ScanAcc using (module AccRun)
open import simultaneous.HeldConnect using (vis-dep)
open import simultaneous.HeldMap using (module MapRun; mapRows; mapRow)
open import simultaneous.DenRows using (scan-out; hot-out)
open import simultaneous.LaneLocal using (inv-ev)
open import simultaneous.Layers using (module ScanLayer; scanRows; snoc-view; run-row; run-tail; run-after; run-++; run-past-end;
  cursor-snoc; to≺; pinby-vis)
open import simultaneous.Project using (run-prefix)
open import simultaneous.FlatLayer using (module ScanOrder; module Each₂; ofVals)

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

pre-∈ : ∀ {B : Set} {xs ys : List B} {x} → Prefix _≡_ xs ys → x ∈ xs → x ∈ ys
pre-∈ (refl ∷ _) (here refl) = here refl
pre-∈ (_ ∷ pr)   (there i)   = there (pre-∈ pr i)

nil-pre : ∀ {B : Set} {xs : List B} {x} → Prefix _≡_ xs [] → x ∈ xs → ⊥
nil-pre [] ()

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

-- A PREFIX OF THE JOINS, THEN A PREFIX OF THE SOURCE'S ROWS PAST THE CUT,
-- is a join: the source's run met up to the last row shown is met.
assemble : ∀ {X} {t : EmissionSet (IE X)} {cs′ sc₁ w₁ e₁ S₀ js M S′ rest rs′}
         → Met t (sc₁ ++ (w₁ , e₁) ∷ S₀) → Prefix _≡_ rs′ (js ++ M) → L.map proj₂ js ≡ L.map out (jl (cnt sc₁) e₁)
         → RowsAt Rl M S′ → (w₁ , e₁) ∷ S₀ ≡ S′ ++ rest → Joined t Rl cs′ rs′
assemble {t = t} {sc₁ = sc₁} {e₁ = e₁} {js = js} {rest = rest} mS pr jeq at eq with pre-split js pr
... | inj₁ pj = j-part (λ i → js-begins {r = cnt sc₁} {e = e₁} jeq (pre-∈ pj i))
... | inj₂ (m , M′ , refl , pm) with at-pre pm at
...   | (y , e) ∷ rs , ex , refl , at₁ with eq
...     | refl = j-read (run-prefix (sc₁ ++ (y , e) ∷ rs) (subst (Met t) shift mS)) jeq at₁
  where
    shift : sc₁ ++ (y , e) ∷ ((rs ++ ex) ++ rest) ≡ (sc₁ ++ (y , e) ∷ rs) ++ (ex ++ rest)
    shift = trans (cong (λ Z → sc₁ ++ (y , e) ∷ Z) (++-assoc rs ex rest)) (sym (++-assoc sc₁ ((y , e) ∷ rs) (ex ++ rest)))

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

-- THE LATEST VALUE AMONG LISTED ROWS, or none: each listed row's event is
-- in hand, so which of them is a value is decided.
module LatestVal {A : Set} (t : EmissionSet A) (fu : ∀ {y e e′} → t y e → t y e′ → e ≡ e′) where
  Val : Pos → Set
  Val k = Σ A λ a → t k (out a)

  Latest : List Pos → Set
  Latest ks = (∀ {k} → k ∈ ks → Val k → ⊥) ⊎ Σ Pos λ v → Val v × v ∈ ks × (∀ {k} → k ∈ ks → Val k → k ≼ v)

  not-val : ∀ {k e} → t k e → (∀ {a} → out a ≡ e → ⊥) → Val k → ⊥
  not-val x nv (_ , y) = nv (fu y x)

  val? : ∀ {k} e → t k e → Dec (Val k)
  val? (out a) x = yes (a , x)
  val? skip    x = no (not-val x λ ())
  val? (pin _) x = no (not-val x λ ())
  val? end     x = no (not-val x λ ())

  latest : ∀ ks → (∀ {k} → k ∈ ks → Σ _ (t k)) → Latest ks
  latest []       _ = inj₁ λ ()
  latest (k ∷ ks) s = add (val? _ (proj₂ (s (here refl)))) (latest ks (λ i → s (there i)))
    where
      add : Dec (Val k) → Latest ks → Latest (k ∷ ks)
      add (no nv)  (inj₁ none)              = inj₁ λ { (here refl) vk → nv vk ; (there i) → none i }
      add (no nv)  (inj₂ (v , vv , i , mx)) = inj₂ (v , vv , there i , λ { (here refl) vk → ⊥-elim (nv vk) ; (there i′) → mx i′ })
      add (yes vk) (inj₁ none)              = inj₂ (k , vk , here refl , λ { (here refl) _ → ≼-refl {k} ; (there i) vk′ → ⊥-elim (none i vk′) })
      add (yes vk) (inj₂ (v , vv , i , mx)) with ≼-or-≻ v k
      ... | inj₁ vk≼ = inj₂ (k , vk , here refl , λ { (here refl) _ → ≼-refl {k} ; {k′} (there i′) vk′ → ≼-trans {k′} {v} {k} (mx i′ vk′) vk≼ })
      ... | inj₂ kv  = inj₂ (v , vv , there i , λ { (here refl) _ → ≺→≼ {k} {v} kv ; (there i′) → mx i′ })

-- THE ANNOTATION'S VALUES ARE ITS CONNECT'S, each with its fold: the
-- source's values, then the nothing that closes it (`CatRuns`), whose
-- fold runs from the latest annotated value before it, the annotation
-- being listed (`Bound.lists`).  So the nothing is the last value, and
-- lies where the end's last gap opens.
module AnnVals {X} {d : Den (AIE X)} {cs} (b : Bound d cs) where
  open AnnRun b using (a₁; C; Sa; eqA)
  module AC = AnnConn b
  module MS = MapRun proj₂ Sa a₁
  module SL = ScanLayer annStep z₀ C a₁ (InvAt.func (cn-inv b))
  open Scan annStep z₀ (Cn b) using (Acc; acc₀; acc; sval)
  module LV = LatestVal (Ann b) (InvAt.func (AnnRun.IA b))

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

  few-ann : ∀ {cb} → Ann b (AC.CT.fpos cb) end → Few (Ann b) (AC.CT.mpos cb)
  few-ann {cb} ce with entered-few (ev (Bound.m b) (annotate (Bound.src b)) (Bound.env b)) a₁ (λ {k′} {e′} → tt) ce
  ... | ks , h = ks , λ {k} y lt → h y (≺-trans {k} {AC.CT.mpos cb} {AC.CT.fpos cb} lt (AC.CT.m≺f cb))

  -- A value with few annotated rows before it has its fold: the latest
  -- annotated value before it, or none.  A value of the connect between
  -- would have its own (`fold`), and be listed.
  fold-ann : ∀ {w a} → Cn b w (out a) → Few (Ann b) w → Σ _ λ st₀ → Acc w (annStep st₀ a)
  fold-ann {w} {a} x F with Bound.lists b F
  ... | ks , cover , sound with LV.latest ks (λ i → proj₂ (sound i))
  ...   | inj₁ none = z₀ , acc₀ x λ {k} y kw →
            fold annStep z₀ (Cn b) (entered-few C a₁ tt y) y λ { (_ , ac) → none (cover (to-ann ac) kw) (_ , to-ann ac) }
  ...   | inj₂ (v , (_ , av) , i , mx) with from-ann av
  ...     | st , ac , refl = st , acc ac x (proj₁ (sound i)) λ {k} y vk kw →
            fold annStep z₀ (Cn b) (entered-few C a₁ tt y) y λ { (_ , ack) → mx (cover (to-ann ack) kw) (_ , to-ann ack) vk }

  gap : ∀ p → Nl.¬ Gap b p → ∀ {c} → Ann b c end → p ≺ c → Σ Pos λ m → Σ Routes λ r → Ann b m (out (r , nothing)) × p ≺ m
  gap p ng {c} ce pc with cn-end ce
  ... | cb , yc , ce′ , refl with fold-ann (mark yc ce′) (few-ann ce)
  ...   | st , ac with ≼-or-≻ (AC.CT.mpos cb) p
  ...     | inj₂ pm = AC.CT.mpos cb , proj₁ st , to-ann ac , pm
  ...     | inj₁ mp = ⊥-elim (ng (cb , proj₁ st , to-ann ac ,
                        conv {cb ⊕ [ ix 1 ]} {AC.CT.mpos cb} {p} {AC.CT.fpos cb} (⊑-snoc⁺ (cb ⊕ [ ix 1 ])) mp pc (⊑-snoc⁺ (cb ⊕ [ ix 1 ])) ,
                        λ fp → ⊑-≼ fp pc))

-- Out of the last gap, the annotation's nothing lies past a reader its end does.
ann-gap : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p → Nl.¬ Gap b p → ∀ {c} → Ann b c end → p ≺ c
        → Σ Pos λ m → Σ Routes λ r → Ann b m (out (r , nothing)) × p ≺ m
ann-gap b = AnnVals.gap b

-- The annotation's nothing is its last value.
ann-last : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) {m r j a} → Ann b m (out (r , nothing)) → Ann b j (out a) → m ≺ j → ⊥
ann-last b = AnnVals.none-last b

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

module Back {X} {d : Den (AIE X)} {cs} (b : Bound d cs) (p : Pos) (ng : Nl.¬ Gap b p) where
  A : EmissionSet (AIE X)
  A = Ann b

  D : Den (AIE X)
  D = hot (Proper A)

  z : JS X
  z = true , ([] , [])

  Sc : Den (JS X)
  Sc = Op.scan joinStep z D

  IA : InvAt (Hots (Bound.env b)) (Bound.at b ⊕ [ ix 1 ]) A
  IA = inv-ev (Bound.m b) (annotate (Bound.src b)) (Bound.env b) (Bound.good b) (Bound.at b ⊕ [ ix 1 ]) (ok-step (Bound.at b) (Bound.ok b))

  IS : InvAt (Hots (Bound.env b)) (s₀ b) (Src b)
  IS = inv-ev (Bound.m b) (Bound.src b) (Bound.env b) (Bound.good b) (s₀ b)
         (ok-step (Bound.at b ⊕ [ ix 1 ]) (ok-step (Bound.at b) (Bound.ok b)))

  LA : Lawful (Proper A)
  LA = record
    { real   = λ x → InvAt.real IA (proj₁ x)
    ; func   = λ x x′ → InvAt.func IA (proj₁ x) (proj₁ x′)
    ; flat   = λ x x′ → InvAt.flat IA (proj₁ x) (proj₁ x′)
    ; proper = λ c y → proj₂ y (proj₁ c)
    }

  fuD : ∀ {y e e′} → enter D p y e → enter D p y e′ → e ≡ e′
  fuD = hot-func LA p

  flD : ∀ {y e l ys e′} → enter D p y e → enter D p (y ⊕ (l ∷ ys)) e′ → ⊥
  flD = hot-flat LA p

  quD : ∀ {c y e} → enter D p c end → enter D p y e → c ≺ y → PinBy c e
  quD c y cy = ⊥-elim (hot-quiet LA p c y cy)

  module SO = ScanOrder joinStep z D p fuD flD quD

  f₂ g₂ : JS X → List (IE X)
  f₂ st = proj₁ (proj₂ st)
  g₂ st = proj₂ (proj₂ st)

  module O = Each₂.Outer f₂ g₂ Sc p SO.sc-fu SO.sc-flat SO.sc-quiet

  -- The reader's visible rows are a function of their position.
  fuE : ∀ {y e e′} → O.E y e → Visible e → O.E y e′ → Visible e′ → e ≡ e′
  fuE = O.e-fu (Each₂.inner-fu f₂ g₂)

  lr : JS X → Pos → List (Pos × Ev (IE X))
  lr = Each₂.lrows₂ f₂ g₂

  -- An emit's lane row lies below the source row it shows.
  rl-lane : ∀ {y w} → Rl y w → Rl (((((y ⊕ [ sub p ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) w
  rl-lane r = Rl-trans ([ ix 0 ] , refl) (Rl-trans ([ ix 1 ] , refl) (Rl-trans ([ ix 1 ] , refl) (Rl-trans ([ ix 1 ] , refl) (Rl-trans ([ sub p ] , refl) r))))

  Img : List (Pos × Ev (IE X)) → List (Pos × Ev (IE X)) → Set
  Img F sc = Σ _ λ M → Σ _ λ sc′ → Σ _ λ rest → F ≡ M × RowsAt Rl M sc′ × sc ≡ sc′ ++ rest × Tl rest × NoEnd sc′

  -- One emit's lane row before the image of the rest.
  tstep : ∀ {y w x F sc} → Rl y w → Img F sc
        → Img ((((((y ⊕ [ sub p ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ] , out x) ∷ F) ((w , out x) ∷ sc)
  tstep {w = w} {x} r (M , sc′ , rest , refl , at , refl , tl , ne) =
    _ ∷ M , (w , out x) ∷ sc′ , rest , refl , (rl-lane r , ev-out (same-refl x)) ∷ᵃ at , refl , tl , ne′
    where
      ne′ : NoEnd ((w , out x) ∷ sc′)
      ne′ (here ())
      ne′ (there i) = ne i

  -- PAST THE FIRST ROW, each annotated emit is a lane row below its source row.
  timg : ∀ {c s ra sc} → ARows c ra sc → EndLast sc
       → Img (O.flatRows (scanRows joinStep (false , s) (L.map (mvh p) ra))) sc
  timg []ᴬ _ = [] , [] , [] , refl , []ᵃ , refl , t-nil , (λ ())
  timg (_∷ᴬ_ (r , ann-just {x}) ar) el = tstep r (timg {s = ([] , x ∷ [])} ar el)
  timg (_∷ᴬ_ (r , ann-none) []ᴬ) refl = [] , [] , _ , refl , []ᵃ , refl , t-end , (λ ())
  timg (_∷ᴬ_ (r , ann-none) (_ ∷ᴬ _)) ()

  -- The joins, then one emit's lane row, before the image of the rest.
  hstep : ∀ {c y w x F sc} → Rl y w → Img F sc
        → Σ _ λ js → Σ _ λ M → Σ _ λ sc′ → Σ _ λ rest
          → (ofVals (((((y ⊕ [ sub p ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ])) 0 (jl c (out x))
              ++ ((((((y ⊕ [ sub p ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ] , out x) ∷ [])) ++ F ≡ js ++ M
          × L.map proj₂ js ≡ L.map out (jl c (out x)) × RowsAt Rl M sc′ × (w , out x) ∷ sc ≡ sc′ ++ rest × Tl rest × NoEnd sc′
  hstep {c} {y} {w} {x} r (M , sc′ , rest , refl , at , refl , tl , ne) =
    js , _ ∷ M , (w , out x) ∷ sc′ , rest , ++-assoc js _ M , ofVals-vals _ 0 (jl c (out x)) ,
    (rl-lane r , ev-out (same-refl x)) ∷ᵃ at , refl , tl , ne′
    where
      js = ofVals (((((y ⊕ [ sub p ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ])) 0 (jl c (out x))
      ne′ : NoEnd ((w , out x) ∷ sc′)
      ne′ (here ())
      ne′ (there i) = ne i

  -- THE FIRST ROW sends the joins, then its emit.
  himg : ∀ {c y w me e ra sc} → Rl y w × AnnEv me e → ARows (L.foldl count c (values ((w , e) ∷ []))) ra sc → EndLast ((w , e) ∷ sc)
       → Σ _ λ js → Σ _ λ M → Σ _ λ sc′ → Σ _ λ rest
         → O.flatRows (scanRows joinStep z (L.map (mvh p) ((y , out (c , me)) ∷ ra))) ≡ js ++ M
         × L.map proj₂ js ≡ L.map out (jl c e) × RowsAt Rl M sc′ × (w , e) ∷ sc ≡ sc′ ++ rest × Tl rest × NoEnd sc′
  himg {c} (r , ann-just {x}) ar el = hstep {c} r (timg {s = (jl c (out x) , x ∷ [])} ar el)
  himg {c} {y} {w} (r , ann-none) []ᴬ refl =
    js , [] , [] , (w , end) ∷ [] , ++-identityʳ (js ++ []) , ofVals-vals _ 0 (jl c end) , []ᵃ , refl , t-end , (λ ())
    where
      js = ofVals (((((y ⊕ [ sub p ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ])) 0 (jl c end)
  himg (r , ann-none) (_ ∷ᴬ _) ()

  -- What the first row's image leaves: the joins, then lane rows below source rows.
  Head : Routes → Ev (IE X) → List (Pos × Ev (IE X)) → List (Pos × Ev (IE X)) → Set
  Head c e F S = Σ _ λ js → Σ _ λ M → Σ _ λ sc′ → Σ _ λ rest → F ≡ js ++ M
               × L.map proj₂ js ≡ L.map out (jl c e) × RowsAt Rl M sc′ × S ≡ sc′ ++ rest × Tl rest × NoEnd sc′

  joined-at : ∀ {sc₁ w₁ e₁ S₀ rs′ F} → Met (Src b) (sc₁ ++ (w₁ , e₁) ∷ S₀) → Prefix _≡_ rs′ F
            → Head (cnt sc₁) e₁ F ((w₁ , e₁) ∷ S₀) → Joined (Src b) Rl (p ∷ cs) rs′
  joined-at mS pr (js , M , sc′ , rest , refl , jeq , at , eqs , _ , _) = assemble mS pr jeq at eqs

  ended-fin : ∀ {sc₁ w₁ e₁ S₀ rs′ js M sc′ q w} → Met (Src b) (sc₁ ++ (w₁ , e₁) ∷ S₀) → (∀ {w′} → Src b w′ end → Rl q w′)
            → Prefix _≡_ rs′ ((js ++ M) ++ (q , end) ∷ []) → (w , end) ∈ (w₁ , e₁) ∷ S₀ → L.map proj₂ js ≡ L.map out (jl (cnt sc₁) e₁)
            → RowsAt Rl M sc′ → (w₁ , e₁) ∷ S₀ ≡ sc′ ++ (w , end) ∷ [] → Joined (Src b) Rl (p ∷ cs) rs′
  ended-fin {sc₁} {js = js} {M} {q = q} mS rq pr wi jeq at eqs =
    assemble mS (subst (Prefix _≡_ _) (++-assoc js M ((q , end) ∷ [])) pr) jeq
      (at-++ at ((rq (proj₁ (run-row mS (∈-++⁺ʳ sc₁ wi))) , ev-end) ∷ᵃ []ᵃ)) (trans eqs (sym (++-identityʳ _)))

  ended-at : ∀ {sc₁ w₁ e₁ S₀ rs′ F q} → Met (Src b) (sc₁ ++ (w₁ , e₁) ∷ S₀) → (∀ {w′} → Src b w′ end → Rl q w′)
           → Prefix _≡_ rs′ (F ++ (q , end) ∷ []) → Σ Pos (λ w → (w , end) ∈ (w₁ , e₁) ∷ S₀)
           → Head (cnt sc₁) e₁ F ((w₁ , e₁) ∷ S₀) → Joined (Src b) Rl (p ∷ cs) rs′
  ended-at mS rq pr (w , wi) (js , M , sc′ , rest , refl , jeq , at , eqs , tl , ne) =
    ended-fin mS rq pr wi jeq at (trans eqs (cong (sc′ ++_) (tl-end tl ne (subst ((w , end) ∈_) eqs wi))))

  -- Lanes of the source rows past the cut, read whole.
  joined-of : ∀ {sc₁ ra₂ sc₂ rs′} → Met (Src b) (sc₁ ++ sc₂) → ARows (cnt sc₁) ra₂ sc₂
            → Prefix _≡_ rs′ (O.flatRows (scanRows joinStep z (L.map (mvh p) ra₂))) → Joined (Src b) Rl (p ∷ cs) rs′
  joined-of _ []ᴬ pr = j-part (λ i → ⊥-elim (nil-pre pr i))
  joined-of {sc₁} mS (h ∷ᴬ ar) pr = joined-at mS pr (himg h ar (end-last (run-tail sc₁ mS)))

  flat-end : ∀ (xs : List (Pos × Ev (JS X))) {q} → NoEnd xs → O.flatRows (xs ++ (q , end) ∷ []) ≡ O.flatRows xs ++ (q , end) ∷ []
  flat-end []                  _  = refl
  flat-end ((y , out st) ∷ xs) {q} ne =
    trans (cong (lr st (y ⊕ [ ix 1 ]) ++_) (flat-end xs (λ i → ne (there i)))) (sym (++-assoc (lr st (y ⊕ [ ix 1 ])) (O.flatRows xs) ((q , end) ∷ [])))
  flat-end ((y , end) ∷ xs)    ne = ⊥-elim (ne (here refl))
  flat-end ((y , skip) ∷ xs)   ne = flat-end xs (λ i → ne (there i))
  flat-end ((y , pin _) ∷ xs)  ne = flat-end xs (λ i → ne (there i))

  -- …then the end, below the source's end.
  ended-of : ∀ {sc₁ ra₂ sc₂ rs′ q m₀ r} → Met (Src b) (sc₁ ++ sc₂) → ARows (cnt sc₁) ra₂ sc₂ → (m₀ , out (r , nothing)) ∈ ra₂
           → (∀ {w} → Src b w end → Rl q w)
           → Prefix _≡_ rs′ (O.flatRows (scanRows joinStep z (L.map (mvh p) ra₂)) ++ (q , end) ∷ []) → Joined (Src b) Rl (p ∷ cs) rs′
  ended-of _ []ᴬ () _ _
  ended-of {sc₁} mS ar@(h ∷ᴬ ar′) mi rq pr = ended-at mS rq pr (ar-none ar mi) (himg h ar′ (end-last (run-tail sc₁ mS)))

  -- Two ends of the source are one.
  src-end : ∀ {w w′} → Src b w end → Src b w′ end → w ≡ w′
  src-end sw sw′ = ≼-antisym {_} {_} (λ lt → pinby-vis tt (InvAt.quiet IS sw′ sw lt)) (λ lt → pinby-vis tt (InvAt.quiet IS sw sw′ lt))

  -- A run met of the hot, read through the scan to the anchor, and found.
  found-in : ∀ {ys k e H y} e₀ → Visible e₀ → Met O.E (ys ++ [ (k , e) ]) → O.Vis k y e → Met (enter D p) (H ++ [ (y , e₀) ])
           → Prefix _≡_ (ys ++ [ (k , e) ]) (O.flatRows (scanRows joinStep z (H ++ [ (y , e₀) ])))
  found-in {ys} {k} {e} {H} {y} e₀ vi m v mD =
    fin (subst (Met (enter Sc p)) (proj₂ (proj₂ (proj₂ (proj₂ ig)))) (proj₁ (proj₂ ig))) (scan-++ joinStep z H [ (y , e₀) ] (pre-noend H mD))
    where
      ig = ScanLayer.in-go joinStep z D p fuD ScanLayer.none mD

      fin : Met (enter Sc p) (scanRows joinStep z (H ++ [ (y , e₀) ]))
          → Σ _ (λ b′ → scanRows joinStep z (H ++ [ (y , e₀) ]) ≡ scanRows joinStep z H ++ scanRows joinStep b′ [ (y , e₀) ])
          → Prefix _≡_ (ys ++ [ (k , e) ]) (O.flatRows (scanRows joinStep z (H ++ [ (y , e₀) ])))
      fin mSc (b′ , eqs) = subst (Prefix _≡_ (ys ++ [ (k , e) ])) (cong O.flatRows (sym eqs)) (go e₀ vi eqs mSc)
        where
         go : ∀ e₀′ → Visible e₀′ → scanRows joinStep z (H ++ [ (y , e₀′) ]) ≡ scanRows joinStep z H ++ scanRows joinStep b′ [ (y , e₀′) ]
            → Met (enter Sc p) (scanRows joinStep z (H ++ [ (y , e₀′) ]))
            → Prefix _≡_ (ys ++ [ (k , e) ]) (O.flatRows (scanRows joinStep z H ++ scanRows joinStep b′ [ (y , e₀′) ]))
         go (out _) _ eq mSc′ = O.found fuE m v (scanRows joinStep z H) (subst (Met (enter Sc p)) eq mSc′)
         go end     _ eq mSc′ = O.found fuE m v (scanRows joinStep z H) (subst (Met (enter Sc p)) eq mSc′)
         go skip    () _ _
         go (pin _) () _ _

  -- A RUN OF THE ANNOTATION REACHING THE ANCHOR'S ROW, cut where the
  -- reader subscribes, is read back past the cut.
  from-ann : ∀ {ys k e ra q₁ a} → Met O.E (ys ++ [ (k , e) ]) → O.Vis k (q₁ ⊕ [ sub p ]) e → p ≺ q₁
           → Met A (ra ++ [ (q₁ , out a) ]) → Joined (Src b) Rl (p ∷ cs) (ys ++ [ (k , e) ])
  from-ann {ys} {k} {e} {ra} {q₁} {a} m v pq mA = at-cut (ann-src b mA) (cut p ra (run-prefix ra mA)) mA
    where
      last-q : ∀ {y e′} → (y , e′) ∈ [ (q₁ , out a) ] → p ≺ y
      last-q (here refl) = pq
      last-q (there ())

      at-split : ∀ {ra₁ ra₂ sc} → Met (Src b) sc → (∀ {y e′} → (y , e′) ∈ ra₁ → y ≼ p) → (∀ {y e′} → (y , e′) ∈ ra₂ → p ≺ y)
               → Met A ((ra₁ ++ ra₂) ++ [ (q₁ , out a) ])
               → Σ _ (λ sc₁ → Σ _ λ sc₂ → sc ≡ sc₁ ++ sc₂ × ARows (L.foldl count r₀ (values sc₁)) (ra₂ ++ [ (q₁ , out a) ]) sc₂)
               → Joined (Src b) Rl (p ∷ cs) (ys ++ [ (k , e) ])
      at-split {ra₁} {ra₂} mS b₁ b₂ mA′ (sc₁ , sc₂ , refl , ar₂) =
        joined-of mS ar₂ (subst (λ R → Prefix _≡_ (ys ++ [ (k , e) ]) (O.flatRows (scanRows joinStep z R))) (sym (map-++ (mvh p) ra₂ [ (q₁ , out a) ]))
          (found-in (out a) tt m v (subst (Met (enter D p)) (map-++ (mvh p) ra₂ [ (q₁ , out a) ])
            (late-in LA p (subst (Met A) (++-assoc ra₁ ra₂ [ (q₁ , out a) ]) mA′) b₁ (λ i → [ b₂ , last-q ]′ (∈-++⁻ ra₂ i))))))

      at-cut : ∀ {ra′} → (Σ _ λ sc → Met (Src b) sc × ARows r₀ (ra′ ++ [ (q₁ , out a) ]) sc)
             → (Σ _ λ ra₁ → Σ _ λ ra₂ → ra′ ≡ ra₁ ++ ra₂ × (∀ {y e′} → (y , e′) ∈ ra₁ → y ≼ p) × (∀ {y e′} → (y , e′) ∈ ra₂ → p ≺ y))
             → Met A (ra′ ++ [ (q₁ , out a) ]) → Joined (Src b) Rl (p ∷ cs) (ys ++ [ (k , e) ])
      at-cut (sc , mS , ar) (ra₁ , ra₂ , refl , b₁ , b₂) mA′ =
        at-split mS b₁ b₂ mA′ (ar-split ra₁ (subst (λ R → ARows r₀ R sc) (++-assoc ra₁ ra₂ [ (q₁ , out a) ]) ar))

  -- THE ANCHOR A VALUE: the annotation's run to its row.
  shown : ∀ {ys k e q st} → Met O.E (ys ++ [ (k , e) ]) → O.Vis k q e → enter Sc p q (out st) → Joined (Src b) Rl (p ∷ cs) (ys ++ [ (k , e) ])
  shown {ys} {k} {e} {q} m v sq = sh (hot-out (proj₁ (proj₂ (proj₂ (scan-out joinStep z D p sq)))))
    where
      sh : ∀ {x} → Σ Pos (λ q₁ → Proper A q₁ (out x) × p ≺ q₁ × q ≡ q₁ ⊕ [ sub p ]) → Joined (Src b) Rl (p ∷ cs) (ys ++ [ (k , e) ])
      sh (q₁ , aq , pq , eq) = from-ann m (subst (λ y → O.Vis k y e) eq v) pq (proj₂ (ann-run b (proj₁ aq)))

  -- THE ANCHOR THE HOT'S END, PAST THE SUBSCRIBE: the annotation's run to
  -- its nothing, then its end.
  ended : ∀ {ys k e c} → Met O.E (ys ++ [ (k , e) ]) → O.Vis k (c ⊕ [ sub p ]) e → Proper A c end → p ≺ c
        → Joined (Src b) Rl (p ∷ cs) (ys ++ [ (k , e) ])
  ended {ys} {k} {e} {c} m v (ce , pc′) pc = e₁ (ann-gap b p ng ce pc)
    where
      absurd-oe : ∀ {x : AIE X} → out x ≡ end → ⊥
      absurd-oe ()

      e₄ : ∀ {m₀ r ra₁ ra₂ sc} → A m₀ (out (r , nothing)) → p ≺ m₀ → Met (Src b) sc
         → (∀ {y e′} → (y , e′) ∈ ra₁ → y ≼ p) → (∀ {y e′} → (y , e′) ∈ ra₂ → p ≺ y)
         → Met A ((ra₁ ++ ra₂) ++ [ (m₀ , out (r , nothing)) ])
         → Σ _ (λ sc₁ → Σ _ λ sc₂ → sc ≡ sc₁ ++ sc₂ × ARows (L.foldl count r₀ (values sc₁)) (ra₂ ++ [ (m₀ , out (r , nothing)) ]) sc₂)
         → Joined (Src b) Rl (p ∷ cs) (ys ++ [ (k , e) ])
      e₄ {m₀} {r} {ra₁} {ra₂} am pm mS b₁ b₂ mA (sc₁ , sc₂ , refl , ar₂) =
        ended-of mS ar₂ (∈-++⁺ʳ ra₂ (here refl)) rq′
          (subst (Prefix _≡_ (ys ++ [ (k , e) ])) flat-eq (found-in end tt m v mD))
        where
          xm = (m₀ , out (r , nothing))
          H = L.map (mvh p) (ra₂ ++ [ xm ])

          m₀c : m₀ ≺ c
          m₀c = [ (λ lt → lt) , (λ eq → ⊥-elim (absurd-oe (InvAt.func IA (subst (λ z → A z (out (r , nothing))) eq am) ce))) ]′
                  (≼-split {m₀} {c} (λ cm → pinby-vis tt (InvAt.quiet IA ce am cm)))

          least : ∀ {k′ e′} → A k′ e′ → Visible e′ → m₀ ≺ k′ → c ≼ k′
          least {e′ = out _} ak _ mk = ⊥-elim (ann-last b am ak mk)
          least {e′ = end}   ak _ _  = pc′ ak
          least {e′ = skip}  _ () _
          least {e′ = pin _} _ () _

          endrow : Run A (just m₀) ((c , end) ∷ [])
          endrow = (((ce , pc′) , entered-few (ev (Bound.m b) (annotate (Bound.src b)) (Bound.env b)) (Bound.at b ⊕ [ ix 1 ]) (λ {k′} {e′} → tt) ce) , tt , m₀c , least) ∷ []

          mA⁺ : Met A (ra₁ ++ ((ra₂ ++ [ xm ]) ++ [ (c , end) ]))
          mA⁺ = subst (Met A) (trans (cong (_++ [ (c , end) ]) (++-assoc ra₁ ra₂ [ xm ])) (++-assoc ra₁ (ra₂ ++ [ xm ]) [ (c , end) ]))
                  (run-++ mA (subst (λ c′ → Run A c′ ((c , end) ∷ [])) (sym (cursor-snoc nothing (ra₁ ++ ra₂))) endrow))

          one : ∀ {q′} → p ≺ q′ → ∀ {y e′} {x : Ev (AIE X)} → (y , e′) ∈ [ (q′ , x) ] → p ≺ y
          one pq (here refl) = pq
          one pq (there ())

          past : ∀ {y e′} → (y , e′) ∈ (ra₂ ++ [ xm ]) ++ [ (c , end) ] → p ≺ y
          past i = [ (λ j → [ b₂ , one pm ]′ (∈-++⁻ ra₂ j)) , one pc ]′ (∈-++⁻ (ra₂ ++ [ xm ]) i)

          mD : Met (enter D p) (H ++ [ (c ⊕ [ sub p ] , end) ])
          mD = subst (Met (enter D p)) (map-++ (mvh p) (ra₂ ++ [ xm ]) [ (c , end) ]) (late-in LA p mA⁺ b₁ past)

          flat-eq : O.flatRows (scanRows joinStep z (H ++ [ (c ⊕ [ sub p ] , end) ]))
                  ≡ O.flatRows (scanRows joinStep z H) ++ (c ⊕ [ sub p ] , end) ∷ []
          flat-eq = trans (cong O.flatRows (proj₂ (scan-++ joinStep z H [ (c ⊕ [ sub p ] , end) ] (pre-noend H mD))))
                          (flat-end (scanRows joinStep z H) (scan-noend joinStep z H (pre-noend H mD)))

          rq′ : ∀ {w} → Src b w end → Rl (c ⊕ [ sub p ]) w
          rq′ sw = Rl-trans ([ sub p ] , refl) (subst (Rl c) (sym (src-end sw (proj₂ (proj₂ (ann-end b ce))))) (proj₁ (proj₂ (ann-end b ce))))

      e₃ : ∀ {m₀ r ra′} → A m₀ (out (r , nothing)) → p ≺ m₀
         → (Σ _ λ sc → Met (Src b) sc × ARows r₀ (ra′ ++ [ (m₀ , out (r , nothing)) ]) sc)
         → (Σ _ λ ra₁ → Σ _ λ ra₂ → ra′ ≡ ra₁ ++ ra₂ × (∀ {y e′} → (y , e′) ∈ ra₁ → y ≼ p) × (∀ {y e′} → (y , e′) ∈ ra₂ → p ≺ y))
         → Met A (ra′ ++ [ (m₀ , out (r , nothing)) ]) → Joined (Src b) Rl (p ∷ cs) (ys ++ [ (k , e) ])
      e₃ {m₀} {r} am pm (sc , mS , ar) (ra₁ , ra₂ , refl , b₁ , b₂) mA =
        e₄ am pm mS b₁ b₂ mA (ar-split ra₁ (subst (λ R → ARows r₀ R sc) (++-assoc ra₁ ra₂ [ (m₀ , out (r , nothing)) ]) ar))

      e₂ : ∀ {m₀ r} → A m₀ (out (r , nothing)) → p ≺ m₀ → Σ _ (λ ra → Met A (ra ++ [ (m₀ , out (r , nothing)) ]))
         → Joined (Src b) Rl (p ∷ cs) (ys ++ [ (k , e) ])
      e₂ am pm (ra , mA) = e₃ am pm (ann-src b mA) (cut p ra (run-prefix ra mA)) mA

      e₁ : (Σ Pos λ m₀ → Σ Routes λ r → A m₀ (out (r , nothing)) × p ≺ m₀) → Joined (Src b) Rl (p ∷ cs) (ys ++ [ (k , e) ])
      e₁ (m₀ , r , am , pm) = e₂ am pm (ann-run b am)

  -- THE ANCHOR THE LATE END: every row met is that end.
  late : ∀ {rs′} → Met O.E rs′ → ∀ {c} → Proper A c end → c ≼ p → Joined (Src b) Rl (p ∷ cs) rs′
  late {rs′} m {c} (ce , _) cp = j-late row
    where
      nv : ∀ {q x} → Σ Pos (λ q₁ → Proper A q₁ (out x) × p ≺ q₁ × q ≡ q₁ ⊕ [ sub p ]) → ⊥
      nv (q₁ , (_ , prop) , pq , _) = ≺-irrefl {p} (≺-≼-≺ {p} {q₁} {p} pq (≼-trans {q₁} {c} {p} (prop ce) cp))

      no-val : ∀ {q a} → enter Sc p q (out a) → ⊥
      no-val sq = nv (hot-out (proj₁ (proj₂ (proj₂ (scan-out joinStep z D p sq)))))

      late-ex : ∀ {q} → enter Sc p q end → Ex (p ∷ cs) q
      late-ex (Scan.send (r-ended {c′} (_ , prop′) pc′ , _) , _) =
        ⊥-elim (≺-irrefl {p} (≺-≼-≺ {p} {c′} {p} pc′ (≼-trans {c′} {c} {p} (prop′ ce) cp)))
      late-ex (Scan.send (r-late _ _ , _) , _) = ex-ext [ last ] (here (subst T (sym (inside-self p)) tt , refl))
      late-ex (Scan.send (r-shown _ () _ , _) , _)

      at-late : ∀ {y q e} → O.Vis y q e → e ≡ end × Ex (p ∷ cs) y
      at-late (O.vlane sx _) = ⊥-elim (no-val sx)
      at-late (O.vend sx)    = refl , late-ex sx

      row : ∀ {y e} → (y , e) ∈ rs′ → e ≡ end × Ex (p ∷ cs) y
      row i = at-late (proj₂ (O.vis (proj₁ (run-row m i)) (proj₂ (run-row m i))))

  -- The anchor of the last row met: a value, the hot's end past the
  -- subscribe, or its late end.
  anchored : ∀ {ys k e q} → Met O.E (ys ++ [ (k , e) ]) → O.Vis k q e → Σ (Ev (JS X)) (λ e₀ → enter Sc p q e₀ × Visible e₀)
           → Joined (Src b) Rl (p ∷ cs) (ys ++ [ (k , e) ])
  anchored m v (out _ , sq , _)                                 = shown m v sq
  anchored m v (end , (Scan.send (r-ended ce pc , _) , _) , _) = ended m v ce pc
  anchored m v (end , (Scan.send (r-late ce cp , _) , _) , _)  = late m ce cp
  anchored m v (end , (Scan.send (r-shown _ () _ , _) , _) , _)
  anchored m v (skip , _ , ())
  anchored m v (pin _ , _ , ())

  back-at : ∀ {rs′} → (rs′ ≡ [] ⊎ Σ _ λ ys → Σ _ λ y → rs′ ≡ ys ++ [ y ]) → Met O.E rs′ → Joined (Src b) Rl (p ∷ cs) rs′
  back-at (inj₁ refl) _ = j-part (λ ())
  back-at (inj₂ (ys , (k , e) , refl)) m = at-vis (O.vis (proj₁ rr) (proj₂ rr))
    where
      rr = run-row m (∈-++⁺ʳ ys (here refl))
      at-vis : Σ Pos (λ q → O.Vis k q e) → Joined (Src b) Rl (p ∷ cs) (ys ++ [ (k , e) ])
      at-vis (q , v) = anchored m v (O.vis-anc v)

  back : ∀ {rs′} → Met O.E rs′ → Joined (Src b) Rl (p ∷ cs) rs′
  back {rs′} m = back-at (snoc-view rs′) m

-- A RUN THE READER MEETS IS ONE OF THE SOURCE'S, JOINED LATE.
read-back : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p → Nl.¬ Gap b p → ∀ {rs′} → Met (enter (RD d) p) rs′
          → Joined (Src b) Rl (p ∷ cs) rs′
read-back b p ng {rs′} m = Back.back b p ng (subst (λ D → Met (enter (RD D) p) rs′) (Bound.is b) m)

-- A RUN THE READER MEETS OF BEGINS ALONE is a prefix of the joins the
-- first source row past the subscription sends, all below that row, with
-- the reader's next row, visible, below it too: the joins left, the row's
-- emit, or the end the source's end shows.  Or it runs past the joins,
-- into that row's emit and on: a begin the source sends is the reader's.
Part : ∀ {X} {d : Den (AIE X)} {cs} → Bound d cs → Pos → List (Pos × Ev (IE X)) → Set
Part {X} {d} b p rs′ =
  Σ _ λ sc₁ → Σ Pos λ w₁ → Σ _ λ e₁ → Σ _ λ S₀ → Σ _ λ js → Met (Src b) (sc₁ ++ (w₁ , e₁) ∷ S₀)
  × L.map proj₂ js ≡ L.map out (jl (cnt sc₁) e₁) × Prefix _≡_ rs′ js × (∀ {y e′} → (y , e′) ∈ rs′ → Rl y w₁)
  × Σ Pos λ u → Σ (Ev (IE X)) λ e′ → enter (RD d) p u e′ × Visible e′ × After (cursor nothing rs′) u × Rl u w₁

data Further {X} {d : Den (AIE X)} {cs} (b : Bound d cs) (rs′ : List (Pos × Ev (IE X))) : Set where
  further : ∀ {pre y e rs js rs₁′} → rs′ ≡ js ++ rs₁′ → Met (Src b) (pre ++ (y , e) ∷ rs)
          → L.map proj₂ js ≡ L.map out (jl (cnt pre) e) → RowsAt Rl rs₁′ ((y , e) ∷ rs) → Further b rs′

postulate
  read-part : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p → Nl.¬ Gap b p → ∀ {rs′ q e} → Met (enter (RD d) p) rs′
            → Begins rs′ → (q , e) ∈ rs′ → Part b p rs′ ⊎ Further b rs′
