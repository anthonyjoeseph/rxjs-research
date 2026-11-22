{-# OPTIONS --guardedness #-}

-- A BOUND BINDER'S READER HOLDS.  A `connected` elaborates to a reader
-- of the binder's annotated source, read hot past the connect.  Each row
-- the reader shows is a row of the source moved below where the source
-- showed it, or a begin it sends joining the source's routes; so its
-- marks route, its values and ends are early, and its counts are the
-- source's (`HeldJoin`).
module simultaneous.HeldRead where

open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.List.Membership.Propositional.Properties using (∈-∃++; ∈-++⁺ʳ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)
open import Tree using (mergeᶠ)
open import denotation.Position using (sub)
open import denotation.Events using (ofᴱ)
open import denotation.EmissionSet using (Ev; hot; Proper; module Op; InE; at-out; on-out)
open import denotation.Laws.Worlds using (⊕-assoc)
open import denotation.Read using (Run; _∷_; [])
open import simultaneous.Routed using (cnt)
open import simultaneous.DenRows using (merge-out; hot-out; of-mem; scan-out)
open import simultaneous.Layers using (run-row; run-tail; run-past-end)
open import simultaneous.Project using (run-prefix)
open import simultaneous.HeldJoin using (jl; jl-in; zero-suc)
open import Tree using (Obs; connect; map; of)
open import denotation.EmissionSet using (map-end)
open import denotation.Laws.Modulus using (entered-few)
open import simultaneous.DenRows using (map-out′)
open import simultaneous.HeldConnect using (vis-dep; same-refl)
open import simultaneous.ScanAcc using (module AccRun)
open import simultaneous.Relations using (values)
open import denotation.Position using (last)
open import denotation.Events using (<ᵖ-between)
open import denotation.EmissionSet using (module Merge; module Scan; Ended; _≺_; _≼_) renaming (ended to r-ended; late to r-late; shown to r-shown)
open import denotation.Laws.Worlds using (InvAt; Hots; ⊕-identityʳ)
open import denotation.Laws.Worlds.Leaves using (of-end)
open import denotation.Laws.Modulus using (≼-split; ≺-irrefl; ≺-≼-≺; ≼-trans; ≺-ext)
open import simultaneous.Layers using (from≺)
open import simultaneous.LaneLocal using (inv-ev)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (lookup) renaming ([] to []ᵉ; _∷_ to _∷ᵉ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Tree using (connected)
open import denotation.Position using (Pos; Path; root; _≟ᵖ_; ix; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Den; enter; ⟦_⟧; out; end)
open import denotation.Laws.Worlds using (ok-step; ⊑-inside; inside-⊑; ⊑-trans; _⊑_)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; over; completed)
open import simultaneous.Relations using (Met)
open import simultaneous.Routed using (Held; Early; Ex; Sync; Idle; Rest; nameOf; r-begin; Routing; Valued; opos)
open import simultaneous.Readings using (rootOf)
open import simultaneous.Relabel using (Same; same-mark; same-value)
open import simultaneous.HeldConnect using (rootOf-ext; early-inst)
open import simultaneous.HeldTake using (name-ext; ex-ext)
open import simultaneous.HeldComb using (ev)
open import simultaneous.HeldBase using (Bound; IH; ih)
open import simultaneous.HeldJoin using (Joined; module Join)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; count; reader; annotate; annStep; joinStep; concatˢ)

-- The reader of a binder's meaning.
RD : ∀ {X} → Den (AIE X) → Den (IE X)
RD d = ⟦ reader (connected (here refl)) ⟧ (d ∷ᵉ []ᵉ)

-- Where the binder's source is subscribed: under the connect's source,
-- under the annotation's own connect.
s₀ : ∀ {X} {d : Den (AIE X)} {cs} → Bound d cs → Pos
s₀ b = (Bound.at b ⊕ [ ix 1 ]) ⊕ [ ix 1 ]

-- The binder's source, subscribed there.
Src : ∀ {X} {d : Den (AIE X)} {cs} → Bound d cs → EmissionSet (IE X)
Src b = enter (ev (Bound.m b) (Bound.src b) (Bound.env b)) (s₀ b)

-- A reader row lies below the source row it shows.
Rl : Pos → Pos → Set
Rl y′ y = Σ Path λ zs → y′ ≡ y ⊕ zs

postulate
  -- A run the reader meets is one of the source's, joined late.
  read-back : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p {rs′} → Met (enter (RD d) p) rs′
            → Joined (Src b) Rl (p ∷ cs) rs′
  read-idle : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p → Idle (enter (RD d) p)
  read-rest : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p → Rest (enter (RD d) p)

-- The source holds where the binder subscribes it.
held-src : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) → Held (Src b) (s₀ b ∷ Bound.outer b)
held-src b = Bound.held b (s₀ b) (ok-step (Bound.at b ⊕ [ ix 1 ]) (ok-step (Bound.at b) (Bound.ok b)))
               (early-inst [ ix 1 ] (early-inst [ ix 1 ] (Bound.ep b)))

-- The binder's annotated source, as the connect's source shows it.
Ann : ∀ {X} {d : Den (AIE X)} {cs} → Bound d cs → EmissionSet (AIE X)
Ann b = enter (ev (Bound.m b) (annotate (Bound.src b)) (Bound.env b)) (Bound.at b ⊕ [ ix 1 ])

-- What an annotated row carries: a source emit, or the source's end.
data AnnEv {X : Set} : Maybe (IE X) → Ev (IE X) → Set where
  ann-just : ∀ {e} → AnnEv (just e) (out e)
  ann-none : AnnEv nothing end

-- The annotation's connect: the source wrapped, read through its own subject, then nothing.
CnO : ∀ {Θ X} → Obs Timeline Θ (IE X) → Obs Timeline Θ (Maybe (IE X))
CnO s = connect (map just s) (concatˢ (connected (here refl)) (of (nothing ∷ [])))

Cn : ∀ {X} {d : Den (AIE X)} {cs} → Bound d cs → EmissionSet (Maybe (IE X))
Cn b = enter (ev (Bound.m b) (CnO (Bound.src b)) (Bound.env b)) (Bound.at b ⊕ [ ix 1 ])

postulate
  -- THE ANNOTATION'S CONNECT SHOWS ITS SOURCE'S RUN: each emit wrapped,
  -- then nothing at the source's end.
  conn-src : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) {rx q x} → Met (Cn b) (rx ++ [ (q , out x) ])
           → Σ (List (Pos × Ev (IE X))) λ pre → Σ Pos λ w → Σ (Ev (IE X)) λ e
             → Met (Src b) (pre ++ [ (w , e) ]) × values rx ≡ L.map just (values pre) × Rl q w × AnnEv x e
  -- It ends below the source's end.
  conn-end : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) {c} → Cn b c end → Σ Pos λ w → Rl c w × Src b w end

cn-inv : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) → InvAt (Hots (Bound.env b)) (Bound.at b ⊕ [ ix 1 ]) (Cn b)
cn-inv b = inv-ev (Bound.m b) (CnO (Bound.src b)) (Bound.env b) (Bound.good b) (Bound.at b ⊕ [ ix 1 ]) (ok-step (Bound.at b) (Bound.ok b))

-- The annotation's first state.
z₀ : ∀ {X} → Routes × AIE X
z₀ = (root , 0) , ((root , 0) , nothing)

ev-ann : ∀ m {Θ X} (s : Obs Timeline Θ (IE X)) env → ev m (annotate s) env ≡ Op.map proj₂ (Op.scan annStep z₀ (ev m (CnO s) env))
ev-ann nothing  s env = refl
ev-ann (just _) s env = refl

ann-snd : ∀ {X} (st : Routes × AIE X) x → proj₂ (annStep st x) ≡ (proj₁ st , x)
ann-snd st (just _) = refl
ann-snd st nothing  = refl

-- The routes an annotation carries count the emits it wrapped.
ann-fold : ∀ {X} (st : Routes × AIE X) (vs : List (IE X)) → proj₁ (L.foldl annStep st (L.map just vs)) ≡ L.foldl count (proj₁ st) vs
ann-fold st []       = refl
ann-fold st (v ∷ vs) = ann-fold (annStep st (just v)) vs

-- AN ANNOTATED ROW IS A SOURCE ROW MET, beside the routes the source
-- held before it.
ann-row : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) {q r me} → Ann b q (out (r , me))
        → Σ (List (Pos × Ev (IE X))) λ pre → Σ Pos λ w → Σ (Ev (IE X)) λ e
          → Met (Src b) (pre ++ [ (w , e) ]) × r ≡ cnt pre × Rl q w × AnnEv me e
ann-row {X} b {q} {r} {me} aq
  with map-out′ proj₂ (Op.scan annStep z₀ (ev (Bound.m b) (CnO (Bound.src b)) (Bound.env b))) (Bound.at b ⊕ [ ix 1 ])
         (subst (λ D → enter D (Bound.at b ⊕ [ ix 1 ]) q (out (r , me))) (ev-ann (Bound.m b) (Bound.src b) (Bound.env b)) aq)
... | st , (Scan.sval ac , _) , eq₁
  with AccRun.acc-run annStep z₀ (cn-inv b) (λ x v → entered-few (ev (Bound.m b) (CnO (Bound.src b)) (Bound.env b)) (Bound.at b ⊕ [ ix 1 ]) (vis-dep v) x) ac
...   | rx , x , _ , run , eq₂ with conn-src b run
...     | pre , w , e , srun , vq , qw , ann =
  pre , w , e , srun ,
  trans (cong proj₁ pair) (trans (cong (λ vs → proj₁ (L.foldl annStep z₀ vs)) vq) (ann-fold z₀ (values pre))) ,
  qw , subst (λ m′ → AnnEv m′ e) (sym (cong proj₂ pair)) ann
  where
    pair : (r , me) ≡ (proj₁ (L.foldl annStep z₀ (values rx)) , x)
    pair = trans eq₁ (trans (cong proj₂ eq₂) (ann-snd _ x))

-- An annotation ends below its source's end.
ann-end : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) {c} → Ann b c end → Σ Pos λ w → Rl c w × Src b w end
ann-end b {c} ce with subst (λ D → enter D (Bound.at b ⊕ [ ix 1 ]) c end) (ev-ann (Bound.m b) (Bound.src b) (Bound.env b)) ce
... | (map-end (Scan.send x , _) , _) = conn-end b x

Rl-trans : ∀ {x y z} → Rl x y → Rl y z → Rl x z
Rl-trans {z = z} (zs , refl) (ws , refl) = ws ++ zs , ⊕-assoc z ws zs

nameOf-rl : ∀ {y w} → Rl y w → nameOf y ≡ nameOf w
nameOf-rl {w = w} (zs , refl) = name-ext w zs

------------------------------------------------------------------------
-- A reader row

-- A reader's scan state: whether it has met a row, its joins, its emit.
JS : Set → Set
JS X = Bool × (List (IE X) × List (IE X))

of-pos : ∀ {A} p i (xs : List A) {y v} → InE (ofᴱ p i xs) y (out v) → Σ ℕ λ j → y ≡ p ⊕ [ ix j ]
of-pos p i (x ∷ xs) at-out     = i , refl
of-pos p i (x ∷ xs) (on-out r) = of-pos p (suc i) xs r

pick : ∀ {A : Set} (c : Bool) {f g : List A} {x} → x ∈ (if c then f else g) → x ∈ f ⊎ x ∈ g
pick true  i = inj₁ i
pick false i = inj₂ i

-- A reader row is one of its scan state's lists, below the state's row.
row-each : ∀ {X} (D : Den (AIE X)) p {y x} → enter (RD D) p y (out x)
         → Σ Pos λ q → Σ (JS X) λ st → enter (Op.scan joinStep (true , ([] , [])) D) p q (out st)
           × (x ∈ proj₁ (proj₂ st) ⊎ x ∈ proj₂ (proj₂ st)) × Rl y q
row-each {X} D p r
  with merge-out (λ (st : JS X) → Op.flatMap (mergeᶠ nothing) (λ c → Op.of (if c then proj₁ (proj₂ st) else proj₂ (proj₂ st)))
                                   (Op.of (true ∷ false ∷ []))) (Op.scan joinStep (true , ([] , [])) D) p r
... | q , st , sq , lane , _
  with merge-out (λ c → Op.of (if c then proj₁ (proj₂ st) else proj₂ (proj₂ st))) (Op.of (true ∷ false ∷ [])) (q ⊕ [ ix 1 ]) lane
...   | q′ , c , cq , inner , _ with of-pos _ 0 _ (proj₁ cq) | of-pos _ 0 _ (proj₁ inner)
...     | j′ , refl | j , refl =
  q , st , sq , pick c (of-mem _ 0 _ (proj₁ inner)) ,
  Rl-trans ([ ix j ] , refl) (Rl-trans ([ ix 1 ] , refl) (Rl-trans ([ ix j′ ] , refl) ([ ix 1 ] , refl)))

-- What a scan step sends: joins, or the emit it read.
js-mem : ∀ {X} (st : JS X) r me {x e} → AnnEv me e
       → x ∈ proj₁ (proj₂ (joinStep st (r , me))) ⊎ x ∈ proj₂ (proj₂ (joinStep st (r , me)))
       → x ∈ jl r e ⊎ me ≡ just x
js-mem (true , _)  r (just _) ann-just (inj₁ i)          = inj₁ i
js-mem (true , _)  r (just _) ann-just (inj₂ (here refl)) = inj₂ refl
js-mem (true , _)  r (just _) ann-just (inj₂ (there ()))
js-mem (true , _)  r nothing  ann-none (inj₁ i)          = inj₁ i
js-mem (true , _)  r nothing  ann-none (inj₂ ())
js-mem (false , _) r (just _) ann-just (inj₁ ())
js-mem (false , _) r (just _) ann-just (inj₂ (here refl)) = inj₂ refl
js-mem (false , _) r (just _) ann-just (inj₂ (there ()))
js-mem (false , _) r nothing  ann-none (inj₁ ())
js-mem (false , _) r nothing  ann-none (inj₂ ())

-- No end is met before a run's last row.
pre-noend : ∀ {A} {t : EmissionSet A} pre {w e c} → Run t nothing (pre ++ [ (w , e) ]) → (c , end) ∈ pre → ⊥
pre-noend {t = t} pre {w} {e} {c} run i with ∈-∃++ i
... | as , bs , refl with run-tail as (subst (Run t nothing) (++-assoc as ((c , end) ∷ bs) [ (w , e) ]) run)
...   | (((ce , _) , _) , _) ∷ rest = nonempty bs (run-past-end ce rest)
  where nonempty : ∀ (zs : List (Pos × Ev _)) → zs ++ [ (w , e) ] ≡ [] → ⊥
        nonempty []      ()
        nonempty (_ ∷ _) ()

-- A join names the instant of the row it is sent before: the source
-- idles there.
join-name : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) pre {w e r} → Met (Src b) (pre ++ [ (w , e) ]) → r ≡ cnt pre
          → ∀ {x} → x ∈ jl r e → x ≡ instEmit (mark begin) (proj₁ r) × proj₁ r ≡ nameOf w
join-name b pre {e = e} run refl {x} ji with jl-in (cnt pre) e ji | run-tail pre run
... | xb , j , pk | ((_ , few) , _ , aft , lst) ∷ [] with Held.idle (held-src b) (run-prefix pre run) (pre-noend pre run) few aft lst
...   | inj₁ z  = ⊥-elim (zero-suc (trans (sym z) pk))
...   | inj₂ nw = xb , nw

-- A ROW THE READER SHOWS: a source row moved below, or a join.
read-row : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p {y} {x : IE X} → enter (RD d) p y (out x)
         → (Σ Pos λ y₀ → Σ (IE X) λ x₀ → Rl y y₀ × Src b y₀ (out x₀) × Same x x₀)
           ⊎ x ≡ instEmit (mark begin) (nameOf y)
read-row {X} b p {y} {x} r = row-hot (subst (λ D → enter (RD D) p y (out x)) (Bound.is b) r)
  where
    row-hot : enter (RD (hot (Proper (Ann b)))) p y (out x)
            → (Σ Pos λ y₀ → Σ (IE X) λ x₀ → Rl y y₀ × Src b y₀ (out x₀) × Same x x₀)
              ⊎ x ≡ instEmit (mark begin) (nameOf y)
    row-hot r′ with row-each (hot (Proper (Ann b))) p r′
    ... | q , st , sq , xi , yq with scan-out joinStep (true , ([] , [])) (hot (Proper (Ann b))) p sq
    ...   | st₀ , (rt , me) , hq , refl with hot-out hq
    ...     | q₁ , (aq , _) , _ , refl with ann-row b aq
    ...       | pre , w , e , run , rc , qw , ann with js-mem st₀ rt me ann xi
    ...         | inj₂ refl = inj₁ (w , x , yw , moved ann , same-refl x)
      where
        yw = Rl-trans yq (Rl-trans ([ sub p ] , refl) qw)
        moved : AnnEv (just x) e → Src b w (out x)
        moved ann-just = proj₁ (run-row run (∈-++⁺ʳ pre (here refl)))
    ...         | inj₁ ji with join-name b pre run rc ji
    ...           | xb , nw =
      inj₂ (trans xb (cong (λ n → instEmit (mark begin) n) (trans nw (sym (nameOf-rl (Rl-trans yq (Rl-trans ([ sub p ] , refl) qw)))))))

------------------------------------------------------------------------
-- A reader end

module _ {A B : Set} (f : A → Den B) (d : Den A) (p : Pos) where
  private module Mg = Merge f (enter d p)

  -- A merge ends where its source does, or where a lane does, past the source's end.
  merge-end : ∀ {k} → enter (Op.flatMap (mergeᶠ nothing) f d) p k end
            → enter d p k end ⊎ Σ Pos λ q → Σ A λ a → enter d p q (out a) × enter (f a) (q ⊕ [ ix 1 ]) k end × Ended (enter d p) k
  merge-end (Mg.oend x _ , _)                        = inj₁ x
  merge-end (Mg.lend x _ (l , _) _ _ (ov , _) , _) = inj₂ (_ , _ , x , l , ov)
  merge-end (Mg.rend () _ _ , _)

-- A scan state's lanes end below its row.
lane-end : ∀ {X} (st : JS X) q {k}
         → enter (Op.flatMap (mergeᶠ nothing) (λ c → Op.of (if c then proj₁ (proj₂ st) else proj₂ (proj₂ st))) (Op.of (true ∷ false ∷ []))) (q ⊕ [ ix 1 ]) k end
         → Rl k q
lane-end st q l with merge-end (λ c → Op.of (if c then proj₁ (proj₂ st) else proj₂ (proj₂ st))) (Op.of (true ∷ false ∷ [])) (q ⊕ [ ix 1 ]) l
... | inj₁ (x , _) with of-end _ 0 _ x
...   | refl = Rl-trans ([ last ] , refl) ([ ix 1 ] , refl)
lane-end st q l | inj₂ (q′ , c , (cq , _) , (le , _) , _) with of-pos _ 0 _ cq | of-end _ 0 _ le
... | j , refl | refl = Rl-trans ([ last ] , refl) (Rl-trans ([ ix 1 ] , refl) (Rl-trans ([ ix j ] , refl) ([ ix 1 ] , refl)))

-- No end of a lawful stream lies past a value and before what lies below it.
val-end-under : ∀ {A H P} {t : EmissionSet A} → InvAt H P t → ∀ {q a c} → t q (out a) → t c end → q ≼ c
              → ∀ ys → c ≺ (q ⊕ ys) → ⊥
val-end-under IA {q} {a} {c} aq ce qc ys cy with ≼-split {q} {c} qc
... | inj₂ refl = out-end (InvAt.func IA aq ce)
  where out-end : out a ≡ end → ⊥
        out-end ()
... | inj₁ lt with <ᵖ-between q c ys (from≺ q c lt) (from≺ c (q ⊕ ys) cy)
...   | [] , eq      = ≺-irrefl {q} (subst (q ≺_) (trans eq (⊕-identityʳ q)) lt)
...   | (_ ∷ _) , refl = InvAt.flat IA aq ce

-- THE READER ENDS below the source's end, or in its own subscribe.
read-end : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p {y} → enter (RD d) p y end
         → (Σ Pos λ y₀ → Rl y y₀ × Src b y₀ end) ⊎ (Σ Path λ zs → y ≡ p ⊕ zs)
read-end {X} b p {y} r = end-hot (subst (λ D → enter (RD D) p y end) (Bound.is b) r)
  where
    IA : InvAt (Hots (Bound.env b)) (Bound.at b ⊕ [ ix 1 ]) (Ann b)
    IA = inv-ev (Bound.m b) (annotate (Bound.src b)) (Bound.env b) (Bound.good b) (Bound.at b ⊕ [ ix 1 ]) (ok-step (Bound.at b) (Bound.ok b))

    D : Den (AIE X)
    D = hot (Proper (Ann b))

    Sc : Den (JS X)
    Sc = Op.scan joinStep (true , ([] , [])) D

    end-hot : ∀ {y} → enter (RD D) p y end → (Σ Pos λ y₀ → Rl y y₀ × Src b y₀ end) ⊎ (Σ Path λ zs → y ≡ p ⊕ zs)
    end-hot r′ with merge-end (λ (st : JS X) → Op.flatMap (mergeᶠ nothing) (λ c → Op.of (if c then proj₁ (proj₂ st) else proj₂ (proj₂ st)))
                                                (Op.of (true ∷ false ∷ []))) Sc p r′
    ... | inj₁ (Scan.send h , _) with h
    ...   | (r-ended (ce , _) _ , _) with ann-end b ce
    ...     | w , cw , sw = inj₁ (w , Rl-trans ([ sub p ] , refl) cw , sw)
    end-hot r′ | inj₁ (Scan.send h , _) | (r-late _ _ , _) = inj₂ ([ last ] , refl)
    end-hot r′ | inj₁ (Scan.send h , _) | (r-shown _ () _ , _)
    end-hot r′ | inj₂ (q , st , sq , l , c₀ , (Scan.send h₀ , _) , c₀y) with scan-out joinStep (true , ([] , [])) D p sq | lane-end st q l
    ... | _ , _ , hq , _ | zs , refl with hot-out hq | h₀
    ...   | q₁ , (aq , prop) , pq , refl | (r-late (ce , _) cp , _) = ⊥-elim (≺-irrefl {p} (≺-≼-≺ {p} {q₁} {p} pq (≼-trans {q₁} {_} {p} (prop ce) cp)))
    ...   | q₁ , (aq , prop) , pq , refl | (r-ended {c} (ce , _) _ , _) =
      ⊥-elim (val-end-under IA aq ce (prop ce) ([ sub p ] ++ zs)
        (subst (c ≺_) (⊕-assoc q₁ [ sub p ] zs) (≺-≼-≺ {c} {c ⊕ [ sub p ]} (≺-ext c []) c₀y)))
    ...   | _ | (r-shown _ () _ , _)

sync-up : ∀ {c y} zs → Sync (c ⊕ zs) y → Sync c y
sync-up {c} {y} zs (ins , rt) =
  ⊑-inside {c} {y} (⊑-trans {c} {c ⊕ zs} {y} (zs , refl) (inside-⊑ (c ⊕ zs) y ins)) , trans rt (rootOf-ext c zs)

∈-ex : ∀ {cs c y} → c ∈ cs → Sync c y → Ex cs y
∈-ex (here refl) s = here s
∈-ex (there i)   s = there (∈-ex i s)

sub-ex : ∀ {os cs y} → (∀ {c} → c ∈ os → c ∈ cs) → Ex os y → Ex cs y
sub-ex f (here s)  = ∈-ex (f (here refl)) s
sub-ex f (there e) = sub-ex (λ i → f (there i)) e

module Reader {X} {d : Den (AIE X)} {cs} (b : Bound d cs) (p : Pos) (ep : Early p) where

  HS : Held (Src b) (s₀ b ∷ Bound.outer b)
  HS = held-src b

  T′ : EmissionSet (IE X)
  T′ = enter (RD d) p

  rt : ∀ {y′ y} → Rl y′ y → rootOf y′ ≡ rootOf y
  rt {y = y} (zs , refl) = rootOf-ext y zs

  lift : ∀ {y} → Ex (s₀ b ∷ Bound.outer b) y → Ex (p ∷ cs) y
  lift {y} (here s) = there (∈-ex (Bound.under b (here refl))
    (sync-up {Bound.at b} {y} [ ix 1 ] (sync-up {Bound.at b ⊕ [ ix 1 ]} {y} [ ix 1 ] s)))
  lift (there e) = there (sub-ex (λ i → Bound.under b (there i)) e)

  exR : ∀ {y′ y} → Rl y′ y → Ex (s₀ b ∷ Bound.outer b) y → Ex (p ∷ cs) y′
  exR (zs , refl) e = lift (ex-ext zs e)

  named : ∀ {y n} → T′ y (out (instEmit (mark begin) n)) → n ≡ nameOf y
  named x with read-row b p x
  ... | inj₁ (y₀ , _ , (zs , refl) , s , same-mark e) = trans (e refl) (trans (Held.named HS s) (sym (name-ext y₀ zs)))
  ... | inj₂ refl = refl

  ends : ∀ {y} → T′ y end → Early y
  ends x with read-end b p x
  ... | inj₁ (_ , (zs , refl) , s) = early-inst zs (Held.ends HS s)
  ... | inj₂ (zs , refl)           = early-inst zs ep

  module J = Join Rl rt exR named (read-back b p) HS

  held : Held T′ (p ∷ cs)
  held = record
    { named   = named
    ; covered = J.covered′
    ; exact   = J.exact′
    ; routing = routing
    ; shut    = J.shut′
    ; early   = early
    ; ends    = ends
    ; done    = done
    ; late    = late
    ; idle    = read-idle b p
    ; rest    = read-rest b p }
    where
      routing : ∀ {y m n} → T′ y (out (instEmit (mark m) n)) → Routing m
      routing x with read-row b p x
      ... | inj₁ (_ , _ , _ , s , same-mark _) = Held.routing HS s
      ... | inj₂ refl = r-begin
      early : ∀ {y a n} → T′ y (out (instEmit (value a) n)) → Early y
      early x with read-row b p x
      ... | inj₁ (_ , _ , (zs , refl) , s , same-value) = early-inst zs (Held.early HS s)
      ... | inj₂ ()
      done : ∀ {y n} → T′ y (out (instEmit (mark completed) n)) → Early y
      done x with read-row b p x
      ... | inj₁ (_ , _ , (zs , refl) , s , same-mark _) = early-inst zs (Held.done HS s)
      ... | inj₂ ()
      late : ∀ {y n} → T′ y (out (instEmit (mark over) n)) → Valued (rootOf y) × opos (rootOf y) ⊑ y
      late x with read-row b p x
      ... | inj₁ (y₀ , _ , (zs , refl) , s , same-mark _) =
        let (v , o) = Held.late HS s
        in subst (λ r → Valued r × opos r ⊑ (y₀ ⊕ zs)) (sym (rootOf-ext y₀ zs)) (v , ⊑-trans o (zs , refl))
      ... | inj₂ ()

held-connected : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) → IH m ρ (connected i)
held-connected nothing  ρ i = ih λ env cs g eh p ok ep → Reader.held (eh i) p ep
held-connected (just n) ρ i = ih λ env cs g eh p ok ep → Reader.held (eh i) p ep
