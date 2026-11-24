{-# OPTIONS --guardedness #-}

module simultaneous.HeldReadBack where

open import Data.Bool using (true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ; ∈-++⁺ˡ; ∈-++⁻)
open import Data.List.Properties using (++-assoc; ++-identityʳ; map-++)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import Relation.Nullary as Nl

open import denotation.Position using (Pos; Label; ix; last; sub; _⊕_; _≟ᵖ_; root)
open import denotation.Events using (Timeline; fresh; inside-self)
open import denotation.EmissionSet using (EmissionSet; Den; Ev; out; end; skip; pin; enter; hot; Proper; module Op; module Scan; _≺_; _≼_)
  renaming (ended to r-ended; late to r-late; shown to r-shown; heard to r-heard)
open import denotation.Read using (Run; []; _∷_; Visible; After; cursor)
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
open import simultaneous.HeldRead using (RD; Rl; Src; s₀; Rl-trans; AnnEv; ann-just; ann-none; ann-end; JS)
open import simultaneous.LiveRuns using (pre-noend)
open import simultaneous.DenRows using (scan-out; hot-out)
open import simultaneous.LaneLocal using (inv-ev)
open import simultaneous.Layers using (module ScanLayer; scanRows; snoc-view; run-row; run-tail; run-++; cursor-snoc; pinby-vis;
  pre-∈; pre-++; before-last; prefix-split)
open import simultaneous.Project using (run-prefix)
open import simultaneous.FlatLayer using (module ScanOrder; module Each₂; ofVals)
open import simultaneous.HeldBack using (ARows; EndLast; NoEnd; Tl; []ᴬ; _∷ᴬ_; ann-fin; ann-gap; ann-last; ann-run; ar-none; ar-split;
  at-++; at-pre; cut; end-last; mvh; nil-eq; ofVals-at; ofVals-vals; pre-split; scan-++;
  scan-noend; t-end; t-nil; tl-end; late-in; ann-src)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; count; annotate; annStep; joinStep)

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

  -- Where the joins of a row stand.
  jp : Pos → Pos
  jp y = (((y ⊕ [ sub p ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]

  JsRl : List (Pos × Ev (IE X)) → Pos → Set
  JsRl js w = ∀ {y e} → (y , e) ∈ js → Rl y w

  -- Each join lies below the source row it joins.
  rl-join : ∀ {y w} → Rl y w → ∀ c e → JsRl (ofVals (jp y) 0 (jl c e)) w
  rl-join {y} {w} r c e {y′} i = jat (ofVals-at (jp y) 0 (jl c e) i)
    where
      jat : Σ Label (λ x → y′ ≡ jp y ⊕ [ x ]) → Rl y′ w
      jat (x , eq) = Rl-trans ([ x ] , eq) (Rl-trans ([ ix 1 ] , refl) (Rl-trans ([ ix 0 ] , refl) (Rl-trans ([ ix 1 ] , refl) (Rl-trans ([ sub p ] , refl) r))))

  -- Past the joins, the image's next row lies below the source row, or
  -- there is none and that row is the source's end.
  Aft : List (Pos × Ev (IE X)) → Ev (IE X) → Pos → Set
  Aft M e w = (Σ Pos λ u → Σ (Ev (IE X)) λ e′ → Σ _ λ M′ → M ≡ (u , e′) ∷ M′ × Rl u w) ⊎ (M ≡ [] × e ≡ end)

  -- What a row's image leaves: the joins, then lane rows below source rows.
  Head : Routes → Pos → Ev (IE X) → List (Pos × Ev (IE X)) → List (Pos × Ev (IE X)) → Set
  Head c w e F S₀ = Σ _ λ js → Σ _ λ M → Σ _ λ sc′ → Σ _ λ rest → F ≡ js ++ M
                  × L.map proj₂ js ≡ L.map out (jl c e) × RowsAt Rl M sc′ × (w , e) ∷ S₀ ≡ sc′ ++ rest × Tl rest × NoEnd sc′
                  × JsRl js w × Aft M e w

  -- The joins, then one emit's lane row, before the image of the rest.
  hstep : ∀ {c y w x F sc} → Rl y w → Img F sc
        → Head c w (out x) ((ofVals (jp y) 0 (jl c (out x))
              ++ ((((((y ⊕ [ sub p ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ] , out x) ∷ [])) ++ F) sc
  hstep {c} {y} {w} {x} r (M , sc′ , rest , refl , at , refl , tl , ne) =
    js , _ ∷ M , (w , out x) ∷ sc′ , rest , ++-assoc js _ M , ofVals-vals _ 0 (jl c (out x)) ,
    (rl-lane r , ev-out (same-refl x)) ∷ᵃ at , refl , tl , ne′ , rl-join r c (out x) , inj₁ (_ , _ , M , refl , rl-lane r)
    where
      js = ofVals (jp y) 0 (jl c (out x))
      ne′ : NoEnd ((w , out x) ∷ sc′)
      ne′ (here ())
      ne′ (there i) = ne i

  -- THE FIRST ROW sends the joins, then its emit.
  himg : ∀ {c y w me e ra sc} → Rl y w × AnnEv me e → ARows (L.foldl count c (values ((w , e) ∷ []))) ra sc → EndLast ((w , e) ∷ sc)
       → Head c w e (O.flatRows (scanRows joinStep z (L.map (mvh p) ((y , out (c , me)) ∷ ra)))) sc
  himg {c} (r , ann-just {x}) ar el = hstep {c} r (timg {s = (jl c (out x) , x ∷ [])} ar el)
  himg {c} {y} {w} (r , ann-none) []ᴬ refl =
    js , [] , [] , (w , end) ∷ [] , ++-identityʳ (js ++ []) , ofVals-vals _ 0 (jl c end) , []ᵃ , refl , t-end , (λ ()) ,
    rl-join r c end , inj₂ (refl , refl)
    where
      js = ofVals (jp y) 0 (jl c end)
  himg (r , ann-none) (_ ∷ᴬ _) ()

  -- A row of the reader past a run, visible, below a source row.
  Nx : List (Pos × Ev (IE X)) → Pos → Set
  Nx rs′ w = Σ Pos λ u → Σ (Ev (IE X)) λ e′ → O.E u e′ × Visible e′ × After (cursor nothing rs′) u × Rl u w

  nx-run : ∀ {c u e′ T w} → Run O.E c ((u , e′) ∷ T) → Rl u w
         → Σ Pos λ u′ → Σ (Ev (IE X)) λ e″ → O.E u′ e″ × Visible e″ × After c u′ × Rl u′ w
  nx-run ((((x , _) , _) , vi , au , _) ∷ _) r = _ , _ , x , vi , au , r

  nx-head : ∀ rs′ {u e′ T w} → Met O.E (rs′ ++ (u , e′) ∷ T) → Rl u w → Nx rs′ w
  nx-head rs′ m r = nx-run (run-tail rs′ m) r

  nx-end : ∀ {rs′ js u e′ T w} → rs′ ≡ js → Met O.E (js ++ (u , e′) ∷ T) → Rl u w → Nx rs′ w
  nx-end {rs′} refl m ru = nx-head rs′ m ru

  nx-mid : ∀ {rs′ js u e′ T w} → (Σ (Pos × Ev (IE X)) λ z′ → Σ _ λ zs → js ≡ rs′ ++ z′ ∷ zs)
         → Met O.E (js ++ (u , e′) ∷ T) → JsRl js w → Nx rs′ w
  nx-mid {rs′} {u = u} {e′} {T} ((y₂ , e₂) , zs , refl) m jr =
    nx-head rs′ (subst (Met O.E) (++-assoc rs′ ((y₂ , e₂) ∷ zs) ((u , e′) ∷ T)) m) (jr (∈-++⁺ʳ rs′ (here refl)))

  -- The reader's row past a prefix of the joins: the next join, or the
  -- row past them all.
  nx-pre : ∀ {rs′ js u e′ T w} → Prefix _≡_ rs′ js → Met O.E (js ++ (u , e′) ∷ T) → JsRl js w → Rl u w → Nx rs′ w
  nx-pre pj m jr ru = [ (λ eq → nx-end eq m ru) , (λ sp → nx-mid sp m jr) ]′ (prefix-split pj)

  -- The row of the reader's run past the joins.
  Past : List (Pos × Ev (IE X)) → Pos → Set
  Past js w = Σ Pos λ u → Σ (Ev (IE X)) λ e′ → Σ _ λ T → Met O.E (js ++ (u , e′) ∷ T) × Rl u w

  EndAfter : List (Pos × Ev (IE X)) → Ev (IE X) → Pos → Set
  EndAfter X e w = e ≡ end → Σ Pos λ q → Σ _ λ X′ → X ≡ (q , end) ∷ X′ × Rl q w

  past-nil : ∀ {js X w} → Met O.E ((js ++ []) ++ X) → (Σ Pos λ q → Σ _ λ X′ → X ≡ (q , end) ∷ X′ × Rl q w) → Past js w
  past-nil {js} m (q , X′ , refl , rq) = q , end , X′ , subst (Met O.E) (cong (_++ ((q , end) ∷ X′)) (++-identityʳ js)) m , rq

  after-js : ∀ {js M X w e} → Met O.E ((js ++ M) ++ X) → Aft M e w → EndAfter X e w → Past js w
  after-js {js} {X = X} m (inj₁ (u , e′ , M′ , refl , ru)) _ = u , e′ , M′ ++ X , subst (Met O.E) (++-assoc js ((u , e′) ∷ M′) X) m , ru
  after-js m (inj₂ (refl , refl)) tl = past-nil m (tl refl)

  -- WHAT THE READER'S RUN IS, READ BACK: rows of the late end; nothing; a
  -- prefix of the joins of the first source row past the subscription,
  -- with the reader's next row below that row; or past those joins, on
  -- the source's rows.
  data BackR (rs′ : List (Pos × Ev (IE X))) : Set where
    b-late : (∀ {y e} → (y , e) ∈ rs′ → e ≡ end × Ex (p ∷ cs) y) → BackR rs′
    b-nil  : rs′ ≡ [] → BackR rs′
    b-part : ∀ {sc₁ w₁ e₁ S₀ js} → Met (Src b) (sc₁ ++ (w₁ , e₁) ∷ S₀) → L.map proj₂ js ≡ L.map out (jl (cnt sc₁) e₁)
           → Prefix _≡_ rs′ js → JsRl rs′ w₁ → Nx rs′ w₁ → BackR rs′
    b-read : Further b rs′ → BackR rs′

  part-of : ∀ {sc₁ w₁ e₁ S₀ js rs′} → Met (Src b) (sc₁ ++ (w₁ , e₁) ∷ S₀) → L.map proj₂ js ≡ L.map out (jl (cnt sc₁) e₁)
          → Prefix _≡_ rs′ js → JsRl js w₁ → Past js w₁ → BackR rs′
  part-of mS jeq pj jr (u , e′ , T , mO , ru) = b-part mS jeq pj (λ i → jr (pre-∈ pj i)) (nx-pre pj mO jr ru)

  -- A PREFIX OF THE JOINS, THEN A PREFIX OF THE SOURCE'S ROWS PAST THE CUT:
  -- the source's run met up to the last row shown is met.
  assemble : ∀ {sc₁ w₁ e₁ S₀ js M S′ rest rs′}
           → Met (Src b) (sc₁ ++ (w₁ , e₁) ∷ S₀) → Prefix _≡_ rs′ (js ++ M) → L.map proj₂ js ≡ L.map out (jl (cnt sc₁) e₁)
           → RowsAt Rl M S′ → (w₁ , e₁) ∷ S₀ ≡ S′ ++ rest → JsRl js w₁ → Past js w₁ → BackR rs′
  assemble {sc₁ = sc₁} {js = js} {rest = rest} mS pr jeq at eq jr pa with pre-split js pr
  ... | inj₁ pj = part-of mS jeq pj jr pa
  ... | inj₂ (m , M′ , refl , pm) with at-pre pm at
  ...   | (y , e) ∷ rs , ex , refl , at₁ with eq
  ...     | refl = b-read (further refl (run-prefix (sc₁ ++ (y , e) ∷ rs) (subst (Met (Src b)) shift mS)) jeq at₁)
    where
      shift : sc₁ ++ (y , e) ∷ ((rs ++ ex) ++ rest) ≡ (sc₁ ++ (y , e) ∷ rs) ++ (ex ++ rest)
      shift = trans (cong (λ Z → sc₁ ++ (y , e) ∷ Z) (++-assoc rs ex rest)) (sym (++-assoc sc₁ ((y , e) ∷ rs) (ex ++ rest)))

  joined-at : ∀ {sc₁ w₁ e₁ S₀ rs′ F X} → Met (Src b) (sc₁ ++ (w₁ , e₁) ∷ S₀) → Met O.E (F ++ X) → Prefix _≡_ rs′ F
            → EndAfter X e₁ w₁ → Head (cnt sc₁) w₁ e₁ F S₀ → BackR rs′
  joined-at mS mO pr tl (js , M , sc′ , rest , refl , jeq , at , eqs , _ , _ , jr , af) = assemble mS pr jeq at eqs jr (after-js mO af tl)

  ended-fin : ∀ {sc₁ w₁ e₁ S₀ rs′ js M sc′ q w} → Met (Src b) (sc₁ ++ (w₁ , e₁) ∷ S₀) → Met O.E ((js ++ M) ++ (q , end) ∷ [])
            → (∀ {w′} → Src b w′ end → Rl q w′)
            → Prefix _≡_ rs′ ((js ++ M) ++ (q , end) ∷ []) → (w , end) ∈ (w₁ , e₁) ∷ S₀ → L.map proj₂ js ≡ L.map out (jl (cnt sc₁) e₁)
            → RowsAt Rl M sc′ → (w₁ , e₁) ∷ S₀ ≡ sc′ ++ (w , end) ∷ [] → JsRl js w₁ → Aft M e₁ w₁ → BackR rs′
  ended-fin {sc₁} {w₁} {js = js} {M} {q = q} mS mO rq pr wi jeq at eqs jr af =
    assemble mS (subst (Prefix _≡_ _) (++-assoc js M ((q , end) ∷ [])) pr) jeq
      (at-++ at ((rq (proj₁ (run-row mS (∈-++⁺ʳ sc₁ wi))) , ev-end) ∷ᵃ []ᵃ)) (trans eqs (sym (++-identityʳ _))) jr
      (after-js mO af (λ e≡ → q , [] , refl , rq (subst (Src b w₁) e≡ (proj₁ (run-row mS (∈-++⁺ʳ sc₁ (here refl)))))))

  ended-at : ∀ {sc₁ w₁ e₁ S₀ rs′ F q} → Met (Src b) (sc₁ ++ (w₁ , e₁) ∷ S₀) → Met O.E (F ++ (q , end) ∷ [])
           → (∀ {w′} → Src b w′ end → Rl q w′)
           → Prefix _≡_ rs′ (F ++ (q , end) ∷ []) → Σ Pos (λ w → (w , end) ∈ (w₁ , e₁) ∷ S₀)
           → Head (cnt sc₁) w₁ e₁ F S₀ → BackR rs′
  ended-at mS mO rq pr (w , wi) (js , M , sc′ , rest , refl , jeq , at , eqs , tl , ne , jr , af) =
    ended-fin mS mO rq pr wi jeq at (trans eqs (cong (sc′ ++_) (tl-end tl ne (subst ((w , end) ∈_) eqs wi)))) jr af

  -- Lanes of the source rows past the cut, read whole, the first a value.
  joined-of : ∀ {sc₁ ra₂ sc₂ rs′ X} → Met (Src b) (sc₁ ++ sc₂) → ARows (cnt sc₁) ra₂ sc₂ → (∀ {y r} → (y , out (r , nothing)) ∈ ra₂ → ⊥)
            → Met O.E (O.flatRows (scanRows joinStep z (L.map (mvh p) ra₂)) ++ X)
            → Prefix _≡_ rs′ (O.flatRows (scanRows joinStep z (L.map (mvh p) ra₂))) → BackR rs′
  joined-of _ []ᴬ _ _ pr = b-nil (nil-eq pr)
  joined-of {sc₁} mS (h@(_ , ann-just) ∷ᴬ ar) _ mO pr = joined-at mS mO pr (λ ()) (himg h ar (end-last (run-tail sc₁ mS)))
  joined-of mS ((_ , ann-none) ∷ᴬ _) nn _ _ = ⊥-elim (nn (here refl))

  flat-end : ∀ (xs : List (Pos × Ev (JS X))) {q} → NoEnd xs → O.flatRows (xs ++ (q , end) ∷ []) ≡ O.flatRows xs ++ (q , end) ∷ []
  flat-end []                  _  = refl
  flat-end ((y , out st) ∷ xs) {q} ne =
    trans (cong (lr st (y ⊕ [ ix 1 ]) ++_) (flat-end xs (λ i → ne (there i)))) (sym (++-assoc (lr st (y ⊕ [ ix 1 ])) (O.flatRows xs) ((q , end) ∷ [])))
  flat-end ((y , end) ∷ xs)    ne = ⊥-elim (ne (here refl))
  flat-end ((y , skip) ∷ xs)   ne = flat-end xs (λ i → ne (there i))
  flat-end ((y , pin _) ∷ xs)  ne = flat-end xs (λ i → ne (there i))

  flat-snoc : ∀ H {c′} → Met (enter D p) (H ++ [ (c′ , end) ])
            → O.flatRows (scanRows joinStep z (H ++ [ (c′ , end) ])) ≡ O.flatRows (scanRows joinStep z H) ++ (c′ , end) ∷ []
  flat-snoc H {c′} mD = trans (cong O.flatRows (proj₂ (scan-++ joinStep z H [ (c′ , end) ] (pre-noend H mD))))
                              (flat-end (scanRows joinStep z H) (scan-noend joinStep z H (pre-noend H mD)))

  -- …then the end, below the source's end.
  ended-of : ∀ {sc₁ ra₂ sc₂ rs′ q m₀ r} → Met (Src b) (sc₁ ++ sc₂) → ARows (cnt sc₁) ra₂ sc₂ → (m₀ , out (r , nothing)) ∈ ra₂
           → (∀ {w} → Src b w end → Rl q w)
           → Met O.E (O.flatRows (scanRows joinStep z (L.map (mvh p) ra₂)) ++ (q , end) ∷ [])
           → Prefix _≡_ rs′ (O.flatRows (scanRows joinStep z (L.map (mvh p) ra₂)) ++ (q , end) ∷ []) → BackR rs′
  ended-of _ []ᴬ () _ _ _
  ended-of {sc₁} mS ar@(h ∷ᴬ ar′) mi rq mO pr = ended-at mS mO rq pr (ar-none ar mi) (himg h ar′ (end-last (run-tail sc₁ mS)))

  -- Two ends of the source are one.
  src-end : ∀ {w w′} → Src b w end → Src b w′ end → w ≡ w′
  src-end sw sw′ = ≼-antisym {_} {_} (λ lt → pinby-vis tt (InvAt.quiet IS sw′ sw lt)) (λ lt → pinby-vis tt (InvAt.quiet IS sw sw′ lt))

  -- An end of the annotation is its only one.
  proper-end : ∀ {c} → A c end → Proper A c end
  proper-end ce = ce , λ ce′ lt → pinby-vis tt (InvAt.quiet IA ce′ ce lt)

  -- A run met of the hot, read through the scan to the anchor, and found.
  found-in : ∀ {ys k e H y} e₀ → Visible e₀ → Met O.E (ys ++ [ (k , e) ]) → O.Vis k y e → Met (enter D p) (H ++ [ (y , e₀) ])
           → Prefix _≡_ (ys ++ [ (k , e) ]) (O.flatRows (scanRows joinStep z (H ++ [ (y , e₀) ])))
             × Met O.E (O.flatRows (scanRows joinStep z (H ++ [ (y , e₀) ])))
  found-in {ys} {k} {e} {H} {y} e₀ vi m v mD =
    fin (subst (Met (enter Sc p)) (proj₂ (proj₂ (proj₂ (proj₂ ig)))) (proj₁ (proj₂ ig))) (scan-++ joinStep z H [ (y , e₀) ] (pre-noend H mD))
    where
      ig = ScanLayer.in-go joinStep z D p fuD ScanLayer.none mD

      fin : Met (enter Sc p) (scanRows joinStep z (H ++ [ (y , e₀) ]))
          → Σ _ (λ b′ → scanRows joinStep z (H ++ [ (y , e₀) ]) ≡ scanRows joinStep z H ++ scanRows joinStep b′ [ (y , e₀) ])
          → Prefix _≡_ (ys ++ [ (k , e) ]) (O.flatRows (scanRows joinStep z (H ++ [ (y , e₀) ])))
            × Met O.E (O.flatRows (scanRows joinStep z (H ++ [ (y , e₀) ])))
      fin mSc (b′ , eqs) = subst (Prefix _≡_ (ys ++ [ (k , e) ])) (cong O.flatRows (sym eqs)) (go e₀ vi eqs mSc) , O.flat-in mSc
        where
         go : ∀ e₀′ → Visible e₀′ → scanRows joinStep z (H ++ [ (y , e₀′) ]) ≡ scanRows joinStep z H ++ scanRows joinStep b′ [ (y , e₀′) ]
            → Met (enter Sc p) (scanRows joinStep z (H ++ [ (y , e₀′) ]))
            → Prefix _≡_ (ys ++ [ (k , e) ]) (O.flatRows (scanRows joinStep z H ++ scanRows joinStep b′ [ (y , e₀′) ]))
         go (out _) _ eq mSc′ = O.found fuE m v (scanRows joinStep z H) (subst (Met (enter Sc p)) eq mSc′)
         go end     _ eq mSc′ = O.found fuE m v (scanRows joinStep z H) (subst (Met (enter Sc p)) eq mSc′)
         go skip    () _ _
         go (pin _) () _ _

  -- THE ANNOTATION'S NOTHING, THEN ITS END, PAST THE SUBSCRIBE: the
  -- annotation's run to its end, the hot's to the end moved below.
  nothing-end : ∀ {rs′ m₀ r c ra₁ ra₂ sc} → A m₀ (out (r , nothing)) → p ≺ m₀ → Proper A c end → p ≺ c → Met (Src b) sc
              → (∀ {y e′} → (y , e′) ∈ ra₁ → y ≼ p) → (∀ {y e′} → (y , e′) ∈ ra₂ → p ≺ y)
              → Met A ((ra₁ ++ ra₂) ++ [ (m₀ , out (r , nothing)) ])
              → Σ _ (λ sc₁ → Σ _ λ sc₂ → sc ≡ sc₁ ++ sc₂ × ARows (L.foldl count r₀ (values sc₁)) (ra₂ ++ [ (m₀ , out (r , nothing)) ]) sc₂)
              → (Met (enter D p) (L.map (mvh p) (ra₂ ++ [ (m₀ , out (r , nothing)) ]) ++ [ (c ⊕ [ sub p ] , end) ])
                 → Prefix _≡_ rs′ (O.flatRows (scanRows joinStep z (L.map (mvh p) (ra₂ ++ [ (m₀ , out (r , nothing)) ]) ++ [ (c ⊕ [ sub p ] , end) ]))))
              → BackR rs′
  nothing-end {rs′} {m₀} {r} {c} {ra₁} {ra₂} am pm (ce , pc′) pc mS b₁ b₂ mA (sc₁ , sc₂ , refl , ar₂) pre =
    ended-of mS ar₂ (∈-++⁺ʳ ra₂ (here refl)) rq′ (subst (Met O.E) fe (O.flat-in mSc)) (subst (Prefix _≡_ rs′) fe (pre mD))
    where
      absurd-oe : ∀ {x : AIE X} → out x ≡ end → ⊥
      absurd-oe ()

      xm = (m₀ , out (r , nothing))
      H = L.map (mvh p) (ra₂ ++ [ xm ])

      m₀c : m₀ ≺ c
      m₀c = [ (λ lt → lt) , (λ eq → ⊥-elim (absurd-oe (InvAt.func IA (subst (λ z′ → A z′ (out (r , nothing))) eq am) ce))) ]′
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

      ig = ScanLayer.in-go joinStep z D p fuD ScanLayer.none mD

      mSc : Met (enter Sc p) (scanRows joinStep z (H ++ [ (c ⊕ [ sub p ] , end) ]))
      mSc = subst (Met (enter Sc p)) (proj₂ (proj₂ (proj₂ (proj₂ ig)))) (proj₁ (proj₂ ig))

      fe : O.flatRows (scanRows joinStep z (H ++ [ (c ⊕ [ sub p ] , end) ])) ≡ O.flatRows (scanRows joinStep z H) ++ (c ⊕ [ sub p ] , end) ∷ []
      fe = flat-snoc H mD

      rq′ : ∀ {w} → Src b w end → Rl (c ⊕ [ sub p ]) w
      rq′ sw = Rl-trans ([ sub p ] , refl) (subst (Rl c) (sym (src-end sw (proj₂ (proj₂ (ann-end b ce))))) (proj₁ (proj₂ (ann-end b ce))))

  -- A RUN OF THE ANNOTATION REACHING THE ANCHOR'S ROW, cut where the
  -- reader subscribes, is read back past the cut: a value's joins and
  -- lanes, or a nothing's joins and then the annotation's end.
  from-ann : ∀ {ys k e ra q₁ a} → Met O.E (ys ++ [ (k , e) ]) → O.Vis k (q₁ ⊕ [ sub p ]) e → p ≺ q₁
           → Met A (ra ++ [ (q₁ , out a) ]) → BackR (ys ++ [ (k , e) ])
  from-ann {ys} {k} {e} {ra} {q₁} m v pq mA = at-cut (ann-src b mA) (cut p ra (run-prefix ra mA)) mA
    where
      last-q : ∀ {a′ : AIE X} {y e′} → (y , e′) ∈ [ (q₁ , out a′) ] → p ≺ y
      last-q (here refl) = pq
      last-q (there ())

      fi : ∀ {ra₁ ra₂ a′} → (∀ {y e′} → (y , e′) ∈ ra₁ → y ≼ p) → (∀ {y e′} → (y , e′) ∈ ra₂ → p ≺ y)
         → Met A ((ra₁ ++ ra₂) ++ [ (q₁ , out a′) ])
         → Prefix _≡_ (ys ++ [ (k , e) ]) (O.flatRows (scanRows joinStep z (L.map (mvh p) (ra₂ ++ [ (q₁ , out a′) ]))))
           × Met O.E (O.flatRows (scanRows joinStep z (L.map (mvh p) (ra₂ ++ [ (q₁ , out a′) ]))))
      fi {ra₁} {ra₂} {a′} b₁ b₂ mA′ =
        subst (λ R → Prefix _≡_ (ys ++ [ (k , e) ]) (O.flatRows (scanRows joinStep z R)) × Met O.E (O.flatRows (scanRows joinStep z R)))
          (sym (map-++ (mvh p) ra₂ [ (q₁ , out a′) ]))
          (found-in (out a′) tt m v (subst (Met (enter D p)) (map-++ (mvh p) ra₂ [ (q₁ , out a′) ])
            (late-in LA p (subst (Met A) (++-assoc ra₁ ra₂ [ (q₁ , out a′) ]) mA′) b₁ (λ i → [ b₂ , last-q {a′} ]′ (∈-++⁻ ra₂ i)))))

      at-split : ∀ {ra₁ ra₂ sc a′} → Met (Src b) sc → (∀ {y e′} → (y , e′) ∈ ra₁ → y ≼ p) → (∀ {y e′} → (y , e′) ∈ ra₂ → p ≺ y)
               → Met A ((ra₁ ++ ra₂) ++ [ (q₁ , out a′) ])
               → Σ _ (λ sc₁ → Σ _ λ sc₂ → sc ≡ sc₁ ++ sc₂ × ARows (L.foldl count r₀ (values sc₁)) (ra₂ ++ [ (q₁ , out a′) ]) sc₂)
               → BackR (ys ++ [ (k , e) ])
      at-split {ra₁} {ra₂} {a′ = r′ , just x} mS b₁ b₂ mA′ (sc₁ , sc₂ , refl , ar₂) =
        joined-of mS ar₂ nn (subst (Met O.E) (sym (++-identityʳ _)) (proj₂ (fi b₁ b₂ mA′))) (proj₁ (fi b₁ b₂ mA′))
        where
          aq : A q₁ (out (r′ , just x))
          aq = proj₁ (run-row mA′ (∈-++⁺ʳ (ra₁ ++ ra₂) (here refl)))

          before : ∀ {y r} → (y , out (r , nothing)) ∈ ra₂ → ⊥
          before j = ann-last b (proj₁ (run-row mA′ (∈-++⁺ˡ (∈-++⁺ʳ ra₁ j)))) aq (before-last (ra₁ ++ ra₂) mA′ (∈-++⁺ʳ ra₁ j))

          lst : ∀ {y r} → (y , out (r , nothing)) ∈ [ (q₁ , out (r′ , just x)) ] → ⊥
          lst (here ())
          lst (there ())

          nn : ∀ {y r} → (y , out (r , nothing)) ∈ ra₂ ++ [ (q₁ , out (r′ , just x)) ] → ⊥
          nn i = [ before , lst ]′ (∈-++⁻ ra₂ i)
      at-split {ra₁} {ra₂} {a′ = r′ , nothing} mS b₁ b₂ mA′ ars = fin-of (ann-fin b am)
        where
          am : A q₁ (out (r′ , nothing))
          am = proj₁ (run-row mA′ (∈-++⁺ʳ (ra₁ ++ ra₂) (here refl)))

          P : Prefix _≡_ (ys ++ [ (k , e) ]) (O.flatRows (scanRows joinStep z (L.map (mvh p) (ra₂ ++ [ (q₁ , out (r′ , nothing)) ]))))
          P = proj₁ (fi b₁ b₂ mA′)

          fin-of : (Σ Pos λ c → A c end × q₁ ≺ c) → BackR (ys ++ [ (k , e) ])
          fin-of (c , ce , qc) = nothing-end am pq (proper-end ce) (≺-trans {p} {q₁} {c} pq qc) mS b₁ b₂ mA′ ars
            (λ mD → subst (Prefix _≡_ (ys ++ [ (k , e) ])) (sym (flat-snoc (L.map (mvh p) (ra₂ ++ [ (q₁ , out (r′ , nothing)) ])) mD)) (pre-++ P))

      at-cut : ∀ {ra′ a′} → (Σ _ λ sc → Met (Src b) sc × ARows r₀ (ra′ ++ [ (q₁ , out a′) ]) sc)
             → (Σ _ λ ra₁ → Σ _ λ ra₂ → ra′ ≡ ra₁ ++ ra₂ × (∀ {y e′} → (y , e′) ∈ ra₁ → y ≼ p) × (∀ {y e′} → (y , e′) ∈ ra₂ → p ≺ y))
             → Met A (ra′ ++ [ (q₁ , out a′) ]) → BackR (ys ++ [ (k , e) ])
      at-cut {a′ = a′} (sc , mS , ar) (ra₁ , ra₂ , refl , b₁ , b₂) mA′ =
        at-split mS b₁ b₂ mA′ (ar-split ra₁ (subst (λ R → ARows r₀ R sc) (++-assoc ra₁ ra₂ [ (q₁ , out a′) ]) ar))

  -- THE ANCHOR A VALUE: the annotation's run to its row.
  shown : ∀ {ys k e q st} → Met O.E (ys ++ [ (k , e) ]) → O.Vis k q e → enter Sc p q (out st) → BackR (ys ++ [ (k , e) ])
  shown {ys} {k} {e} {q} m v sq = sh (hot-out (proj₁ (proj₂ (proj₂ (scan-out joinStep z D p sq)))))
    where
      sh : ∀ {x} → Σ Pos (λ q₁ → Proper A q₁ (out x) × p ≺ q₁ × q ≡ q₁ ⊕ [ sub p ]) → BackR (ys ++ [ (k , e) ])
      sh (q₁ , aq , pq , eq) = from-ann m (subst (λ y → O.Vis k y e) eq v) pq (proj₂ (ann-run b (proj₁ aq)))

  -- THE ANCHOR THE HOT'S END, PAST THE SUBSCRIBE: the annotation's run to
  -- its nothing, then its end, not refuted, as the nothing's fold is not.
  ended : ∀ {ys k e c} → Met O.E (ys ++ [ (k , e) ]) → O.Vis k (c ⊕ [ sub p ]) e → Proper A c end → p ≺ c
        → Nl.¬ Nl.¬ (BackR (ys ++ [ (k , e) ]))
  ended {ys} {k} {e} {c} m v cp pc h = ann-gap b p ng (proj₁ cp) pc λ g → h (e₁ g)
    where
      e₃ : ∀ {m₀ r ra′} → A m₀ (out (r , nothing)) → p ≺ m₀
         → (Σ _ λ sc → Met (Src b) sc × ARows r₀ (ra′ ++ [ (m₀ , out (r , nothing)) ]) sc)
         → (Σ _ λ ra₁ → Σ _ λ ra₂ → ra′ ≡ ra₁ ++ ra₂ × (∀ {y e′} → (y , e′) ∈ ra₁ → y ≼ p) × (∀ {y e′} → (y , e′) ∈ ra₂ → p ≺ y))
         → Met A (ra′ ++ [ (m₀ , out (r , nothing)) ]) → BackR (ys ++ [ (k , e) ])
      e₃ {m₀} {r} am pm (sc , mS , ar) (ra₁ , ra₂ , refl , b₁ , b₂) mA =
        nothing-end am pm cp pc mS b₁ b₂ mA (ar-split ra₁ (subst (λ R → ARows r₀ R sc) (++-assoc ra₁ ra₂ [ (m₀ , out (r , nothing)) ]) ar))
          (λ mD → proj₁ (found-in end tt m v mD))

      e₂ : ∀ {m₀ r} → A m₀ (out (r , nothing)) → p ≺ m₀ → Σ _ (λ ra → Met A (ra ++ [ (m₀ , out (r , nothing)) ]))
         → BackR (ys ++ [ (k , e) ])
      e₂ am pm (ra , mA) = e₃ am pm (ann-src b mA) (cut p ra (run-prefix ra mA)) mA

      e₁ : (Σ Pos λ m₀ → Σ Routes λ r → A m₀ (out (r , nothing)) × p ≺ m₀) → BackR (ys ++ [ (k , e) ])
      e₁ (m₀ , r , am , pm) = e₂ am pm (ann-run b am)

  -- THE ANCHOR THE LATE END: every row met is that end.
  late : ∀ {rs′} → Met O.E rs′ → ∀ {c} → Proper A c end → c ≼ p → BackR rs′
  late {rs′} m {c} (ce , _) cp = b-late row
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

  -- READ BACK POSITIVELY, or, where the last row met is the reader's end
  -- read off the hot's end past the subscribe, not refuted.
  Back⁺ : List (Pos × Ev (IE X)) → Set
  Back⁺ rs′ = BackR rs′ ⊎ (Σ Pos (λ q → (q , end) ∈ rs′) × Nl.¬ Nl.¬ (BackR rs′))

  -- A row anchored at the scan's end is the reader's end.
  end-of : ∀ {ys k e q} → O.Vis k q e → enter Sc p q end → Σ Pos (λ q′ → (q′ , end) ∈ ys ++ [ (k , e) ])
  end-of {ys} (O.vend _) _ = _ , ∈-++⁺ʳ ys (here refl)
  end-of (O.vlane x _) sq with SO.sc-fu x sq
  ... | ()

  -- The anchor of the last row met: a value, the hot's end past the
  -- subscribe, or its late end.
  anchored : ∀ {ys k e q} → Met O.E (ys ++ [ (k , e) ]) → O.Vis k q e → Σ (Ev (JS X)) (λ e₀ → enter Sc p q e₀ × Visible e₀)
           → Back⁺ (ys ++ [ (k , e) ])
  anchored m v (out _ , sq , _)                                    = inj₁ (shown m v sq)
  anchored m v (end , sq@(Scan.send (r-ended ce pc , _) , _) , _) = inj₂ (end-of v sq , ended m v ce pc)
  anchored m v (end , (Scan.send (r-late ce cp , _) , _) , _)     = inj₁ (late m ce cp)
  anchored m v (end , (Scan.send (r-shown _ () _ , _) , _) , _)
  anchored m v (skip , _ , ())
  anchored m v (pin _ , _ , ())

  back-at : ∀ {rs′} → (rs′ ≡ [] ⊎ Σ _ λ ys → Σ _ λ y → rs′ ≡ ys ++ [ y ]) → Met O.E rs′ → Back⁺ rs′
  back-at (inj₁ refl) _ = inj₁ (b-nil refl)
  back-at (inj₂ (ys , (k , e) , refl)) m = at-vis (O.vis (proj₁ rr) (proj₂ rr))
    where
      rr = run-row m (∈-++⁺ʳ ys (here refl))
      at-vis : Σ Pos (λ q → O.Vis k q e) → Back⁺ (ys ++ [ (k , e) ])
      at-vis (q , v) = anchored m v (O.vis-anc v)

  back : ∀ {rs′} → Met O.E rs′ → Back⁺ rs′
  back {rs′} m = back-at (snoc-view rs′) m

  to-joined : ∀ {rs′} → BackR rs′ → Joined (Src b) Rl (p ∷ cs) rs′
  to-joined (b-late h)                                          = j-late h
  to-joined (b-nil refl)                                        = j-part (λ ())
  to-joined (b-part {sc₁ = sc₁} {e₁ = e₁} _ jeq pj _ _)         = j-part (λ i → js-begins {r = cnt sc₁} {e = e₁} jeq (pre-∈ pj i))
  to-joined (b-read (further refl mS jeq at))                   = j-read mS jeq at

  to-joined⁺ : ∀ {rs′} → Back⁺ rs′
             → Joined (Src b) Rl (p ∷ cs) rs′ ⊎ (Σ Pos (λ q → (q , end) ∈ rs′) × Nl.¬ Nl.¬ (Joined (Src b) Rl (p ∷ cs) rs′))
  to-joined⁺ (inj₁ br)       = inj₁ (to-joined br)
  to-joined⁺ (inj₂ (ei , nb)) = inj₂ (ei , λ h → nb λ br → h (to-joined br))

  end-out : ∀ {x : IE X} → end ≡ out x → ⊥
  end-out ()

  no-row : ∀ {y : Pos × Ev (IE X)} {rs′} → rs′ ≡ [] → y ∈ rs′ → ⊥
  no-row refl ()

  to-part : ∀ {rs′ q e} → Begins rs′ → (q , e) ∈ rs′ → BackR rs′ → Part b p rs′ ⊎ Further b rs′
  to-part bs qi (b-late h) = ⊥-elim (end-out (trans (sym (proj₁ (h qi))) (proj₂ (bs qi))))
  to-part _  qi (b-nil eq) = ⊥-elim (no-row eq qi)
  to-part _  _  (b-part {sc₁} {w₁} {e₁} {S₀} {js} mS jeq pj rl (u , e′ , x , vi , au , ru)) =
    inj₁ (sc₁ , w₁ , e₁ , S₀ , js , mS , jeq , pj , rl , u , e′ , subst (λ D′ → enter (RD D′) p u e′) (sym (Bound.is b)) x , vi , au , ru)
  to-part _  _  (b-read f) = inj₂ f

  to-part⁺ : ∀ {rs′ q e} → Begins rs′ → (q , e) ∈ rs′ → Back⁺ rs′ → Part b p rs′ ⊎ Further b rs′
  to-part⁺ bs qi (inj₁ br)            = to-part bs qi br
  to-part⁺ bs _  (inj₂ ((_ , ei) , _)) = ⊥-elim (end-out (proj₂ (bs ei)))

-- A RUN THE READER MEETS IS ONE OF THE SOURCE'S, JOINED LATE: positively,
-- or, ending in the reader's end read off the hot's, not refuted.  Which
-- rows of the annotation precede its nothing may hang on an older hot's
-- synchronous loop the annotation never shows, so its fold is no more.
read-back : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p → Nl.¬ Gap b p → ∀ {rs′} → Met (enter (RD d) p) rs′
          → Joined (Src b) Rl (p ∷ cs) rs′ ⊎ (Σ Pos (λ q → (q , end) ∈ rs′) × Nl.¬ Nl.¬ (Joined (Src b) Rl (p ∷ cs) rs′))
read-back b p ng {rs′} m = Back.to-joined⁺ b p ng (Back.back b p ng (subst (λ D → Met (enter (RD D) p) rs′) (Bound.is b) m))

-- The same, not refuted either way.
read-joined : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p → Nl.¬ Gap b p → ∀ {rs′} → Met (enter (RD d) p) rs′
            → Nl.¬ Nl.¬ (Joined (Src b) Rl (p ∷ cs) rs′)
read-joined b p ng m with read-back b p ng m
... | inj₁ j       = λ h → h j
... | inj₂ (_ , nj) = nj

read-part : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p → Nl.¬ Gap b p → ∀ {rs′ q e} → Met (enter (RD d) p) rs′
          → Begins rs′ → (q , e) ∈ rs′ → Part b p rs′ ⊎ Further b rs′
read-part b p ng {rs′} m bs qi = Back.to-part⁺ b p ng bs qi (Back.back b p ng (subst (λ D → Met (enter (RD D) p) rs′) (Bound.is b) m))
