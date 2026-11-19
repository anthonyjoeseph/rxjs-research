{-# OPTIONS --guardedness #-}

-- THE JOINERS' MAP ACROSS ENVIRONMENTS (`joiners-coh`): two
-- environments whose hots map alike give each joiner's lanes' flatMap
-- one map.  The lane lists are read off the plain tables, so the two
-- list the same lanes in order; a lane's map is read off its value, its
-- two subscriptions and its record, each alike by the source's and the
-- lanes' coherence.
module simultaneous.TableCoh where

open import Level using (Level)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; [_])
open import Data.List.Relation.Unary.All using (All)
import Data.List as L
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_) renaming (++⁺ to pw-++)
open import Data.Maybe using (Maybe; just; nothing; maybe)
import Data.Maybe.Relation.Binary.Pointwise as MP
open MP using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (does; ¬_)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Position using (Pos; _≟ᵖ_; ix; sub; last; _⊕_)
open import denotation.Events using (Timeline)
open import denotation.EmissionSet using (end)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (anyᵇ)
open import simultaneous.Listing using (UncutEnv)
open import simultaneous.TableCorr using (Same; module Same; same; Rel)
open import simultaneous.TableKit using (TR)
open import simultaneous.TableEnv using (Ren; Tab; up; _⊕ˡ_; Aligned; Linked; EnvR; maps; lw; lw*; Admits; Out; HotD; den-cons)
open import simultaneous.LaneEndSched using (laneX; laneL; trigXs; readerR; emitAt; later)
open import simultaneous.TableFlat using (module Flat; module Vals; module TabRows; if-≡)
open import simultaneous.TableJoin using (module Joiners; module Runs)

open TabRows using (endAt; rowAt; endsAt)

----------------------------------------------------------------------
-- Lists related element by element

module _ {a b r : Level} {X : Set a} {Y : Set b} {R : X → Y → Set r} where
  if-pw : ∀ c {xs ys xs′ ys′} → (c ≡ true → Pointwise R xs xs′) → (c ≡ false → Pointwise R ys ys′)
        → Pointwise R (if c then xs else ys) (if c then xs′ else ys′)
  if-pw true  t _ = t refl
  if-pw false _ f = f refl

  maybe-pw : ∀ {w q : Level} {W W′ : Set w} {Q : W → W′ → Set q} {m m′} {g : W → List X} {g′ : W′ → List Y}
           → MP.Pointwise Q m m′ → (∀ {v v′} → Q v v′ → Pointwise R (g v) (g′ v′)) → Pointwise R (maybe g [] m) (maybe g′ [] m′)
  maybe-pw (just q) k = k q
  maybe-pw nothing  _ = []

  maybe-same : ∀ {w : Level} {W : Set w} {g : W → List X} {g′ : W → List Y} m → (∀ v → Pointwise R (g v) (g′ v))
             → Pointwise R (maybe g [] m) (maybe g′ [] m)
  maybe-same (just v) k = k v
  maybe-same nothing  _ = []

  cm-pw : ∀ {i : Level} {I : Set i} {g : I → List X} {g′ : I → List Y} → (∀ x → Pointwise R (g x) (g′ x))
        → ∀ xs → Pointwise R (L.concatMap g xs) (L.concatMap g′ xs)
  cm-pw k []       = []
  cm-pw k (x ∷ xs) = pw-++ (k x) (cm-pw k xs)

-- One table's ends, read twice.
endsAt-≡ : ∀ {X : Set} {m m′ : Maybe (Tb.Listed X)} → m ≡ m′ → ∀ c → MP.Pointwise (λ _ _ → ⊤) (endsAt m c) (endsAt m′ c)
endsAt-≡ {m = m} refl c with endsAt m c
... | just _  = just tt
... | nothing = nothing

----------------------------------------------------------------------
-- Two environments

module Two {Γ A B} n (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
  (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) (uρ* : ∀ N → UncutEnv (ρ* N))
  (E E′ : EnvR ρ ρι ρ*) (p p* : Pos) (a : Admits (lw E) p) (a′ : Admits (lw E′) p) (a* : Admits (lw* E) p*) (a*′ : Admits (lw* E′) p*) where

  module X  = Flat n f s ρ uρ ρι ρ* uρ* E  p p* a  a*
  module X′ = Flat n f s ρ uρ ρι ρ* uρ* E′ p p* a′ a*′
  open Vals n s ρ p using (S; ValAt; valAt; valsAt; valAtPos; isMarker)

  -- Two environments' lanes, mapping alike however their hots are
  -- recorded and their subscriptions admitted.
  LanesX : X.Lanes → X′.Lanes → Set₁
  LanesX Ls Ls′ = ∀ b t₁ t₂ t₃ t₄ u (h₁ h₁′ : HotD t₁) (h₂ h₂′ : HotD t₂) (h₃ h₃′ : HotD t₃) (h₄ h₄′ : HotD t₄) q q*
                    (ad : Admits (lw E) q) (ad′ : Admits (lw E′) q)
                    (ad* : Admits (den-cons h₁ (den-cons h₂ (den-cons h₃ (den-cons h₄ (lw* E))))) q*)
                    (ad*′ : Admits (den-cons h₁′ (den-cons h₂′ (den-cons h₃′ (den-cons h₄′ (lw* E′))))) q*)
                    (al : Aligned (maps E) ρ q q*) (al′ : Aligned (maps E′) ρ q q*) (lk lk′ : Linked q q*) N y
                → Same (Out.rel (Ls b t₁ t₂ t₃ t₄ u h₁ h₂ h₃ h₄ q q* ad ad* al lk)) (Out.rel (Ls′ b t₁ t₂ t₃ t₄ u h₁′ h₂′ h₃′ h₄′ q q* ad′ ad*′ al′ lk′)) N y

  module _ (Os : X.Src) (Os′ : X′.Src) (Ls : X.Lanes) (Ls′ : X′.Lanes) (Lc : X.LanesCoh Ls) (Lc′ : X′.LanesCoh Ls′)
           (os≡ : ∀ N y → Same (Out.rel Os) (Out.rel Os′) N y) (ls≡ : LanesX Ls Ls′) where
    module P  = X.Parts Os Ls Lc
    module P′ = X′.Parts Os′ Ls′ Lc′

    -- TWO ENVIRONMENTS' RECORDS OF ONE LANE: one value, one pair of
    -- subscriptions, one map, late alike.
    record LaneX {N} (R : P.LaneRec N) (R′ : P′.LaneRec N) : Set where
      field
        a≡   : P.LaneRec.a R ≡ P′.LaneRec.a R′
        st≡  : P.LaneRec.st R ≡ P′.LaneRec.st R′
        stE≡ : P.LaneRec.stE R ≡ P′.LaneRec.stE R′
        φ≡   : ∀ y → Rel.φ (Out.rel (P.LaneRec.lane R)) N y ≡ Rel.φ (Out.rel (P′.LaneRec.lane R′)) N y
        late→ : ∀ y → ¬ Rel.Late (Out.rel (P.LaneRec.lane R)) N y → ¬ Rel.Late (Out.rel (P′.LaneRec.lane R′)) N y

    tab-x : ∀ {N} {R : P.LaneRec N} {R′ : P′.LaneRec N} → LaneX R R′ → P.LaneRec.tab R ≡ P′.LaneRec.tab R′
    tab-x {N} x = cong₂ (λ b q → Tab n (f b) ρ q N) (LaneX.a≡ x) (LaneX.st≡ x)

    out-x : ∀ {N} {R : P.LaneRec N} {R′ : P′.LaneRec N} → LaneX R R′ → ∀ y → P.LaneRec.outImage R y ≡ P′.LaneRec.outImage R′ y
    out-x x y = cong₂ (λ u v → emitAt (u ⊕ [ sub (readerR v) ])) (LaneX.φ≡ x y) (LaneX.stE≡ x)

    end-x : ∀ {N} {R : P.LaneRec N} {R′ : P′.LaneRec N} → LaneX R R′ → ∀ y → P.LaneRec.endImage R y ≡ P′.LaneRec.endImage R′ y
    end-x x y = cong₂ (λ u v → emitAt (later u (laneL v ⊕ˡ trigXs v) ⊕ˡ (sub (readerR v) ∷ ix 1 ∷ ix 0 ∷ [])) ⊕ [ last ])
                      (LaneX.φ≡ x y) (LaneX.stE≡ x)

    -- A lane at alike subscriptions maps alike and is late alike in the
    -- two environments.
    lane-x : ∀ {b q st st′} → st ≡ st′ → (ad* : Admits X.Dc st) (ad*′ : Admits X′.Dc st′)
           → (ad : Admits (lw E) q) (ad′ : Admits (lw E′) q)
           → (al : Aligned (maps E) ρ q (laneX st)) (al′ : Aligned (maps E′) ρ q (laneX st′))
           → (lk : Linked q (laneX st)) (lk′ : Linked q (laneX st′)) → ∀ N y
           → Same (Out.rel (Ls b (P.trig st) X.cl-tab X.sh-tab X.tt-tab (P.utrig st) (P.trigD st ad*) X.clD X.shD X.ttD
                                q (laneX st) ad (P.laneAdm st ad*) al lk))
                  (Out.rel (Ls′ b (P′.trig st′) X′.cl-tab X′.sh-tab X′.tt-tab (P′.utrig st′) (P′.trigD st′ ad*′) X′.clD X′.shD X′.ttD
                                q (laneX st′) ad′ (P′.laneAdm st′ ad*′) al′ lk′)) N y
    lane-x {b} {q} {st} refl ad* ad*′ ad ad′ al al′ lk lk′ =
      ls≡ b (P.trig st) X.cl-tab X.sh-tab X.tt-tab (P.utrig st) (P.trigD st ad*) (P′.trigD st ad*′) X.clD X′.clD X.shD X′.shD X.ttD X′.ttD
          q (laneX st) ad ad′ (P.laneAdm st ad*) (P′.laneAdm st ad*′) al al′ lk lk′

    -- A value's two lanes.
    valRec-x : ∀ {N} v → LaneX (P.valRec N v) (P′.valRec N v)
    valRec-x {N} v@(valAt q b x) = record { a≡ = refl ; st≡ = refl ; stE≡ = st≡ ; φ≡ = λ y → Same.φ≡ (lx y) ; late→ = λ y → Same.nl→ (lx y) }
      where
        st≡ : P.LaneRec.stE (P.valRec N v) ≡ P′.LaneRec.stE (P′.valRec N v)
        st≡ = cong (λ u → (u ⊕ˡ (sub X.c₁ ∷ ix 1 ∷ ix 0 ∷ [])) ⊕ [ ix 1 ]) (Same.φ≡ (os≡ N q))
        lx : ∀ y → Same (Out.rel (P.LaneRec.lane (P.valRec N v))) (Out.rel (P′.LaneRec.lane (P′.valRec N v))) N y
        lx = lane-x st≡ (P.LaneRec.adm* (P.valRec N v)) (P′.LaneRec.adm* (P′.valRec N v)) (P.LaneRec.adm (P.valRec N v)) (P′.LaneRec.adm (P′.valRec N v)) _ _ _ _ N

    -- A queued value's two lanes, after two records of the lane it
    -- waited on.
    queuedRec-x : ∀ {N} {R : P.LaneRec N} {R′ : P′.LaneRec N} {c} → LaneX R R′ → (cx : TR (P.LaneRec.tab R) c end) (cx′ : TR (P′.LaneRec.tab R′) c end)
                → ∀ b → LaneX (P.queuedRec N R cx b) (P′.queuedRec N R′ cx′ b)
    queuedRec-x {N} {R} {R′} {c} x cx cx′ b = record { a≡ = refl ; st≡ = refl ; stE≡ = st≡ ; φ≡ = λ y → Same.φ≡ (lx y) ; late→ = λ y → Same.nl→ (lx y) }
      where
        st≡ : P.LaneRec.stE (P.queuedRec N R cx b) ≡ P′.LaneRec.stE (P′.queuedRec N R′ cx′ b)
        st≡ = cong (_⊕ [ ix 1 ]) (end-x x c)
        lx : ∀ y → Same (Out.rel (P.LaneRec.lane (P.queuedRec N R cx b))) (Out.rel (P′.LaneRec.lane (P′.queuedRec N R′ cx′ b))) N y
        lx = lane-x st≡ (P.LaneRec.adm* (P.queuedRec N R cx b)) (P′.LaneRec.adm* (P′.queuedRec N R′ cx′ b))
                        (P.LaneRec.adm (P.queuedRec N R cx b)) (P′.LaneRec.adm (P′.queuedRec N R′ cx′ b)) _ _ _ _ N

    LanesX′ : ∀ {N} → List (P.LaneRec N) → List (P′.LaneRec N) → Set₁
    LanesX′ = Pointwise LaneX

    PickX : ∀ {N} → Maybe (P.LaneRec N) → Maybe (P′.LaneRec N) → Set₁
    PickX = MP.Pointwise LaneX

    -- Alike lanes, picked alike, give alike picks.
    lastWith-x : ∀ {N} (h : P.LaneRec N → Bool) (h′ : P′.LaneRec N → Bool) → (∀ {R R′} → LaneX R R′ → h R ≡ h′ R′)
               → ∀ {Rs Rs′} → LanesX′ Rs Rs′ → PickX (P.lastWith h Rs) (P′.lastWith h′ Rs′)
    lastWith-x h h′ hh [] = nothing
    lastWith-x {N} h h′ hh (_∷_ {R} {R′} {Rs} {Rs′} x xs) with P.lastWith h Rs | P′.lastWith h′ Rs′ | lastWith-x h h′ hh xs
    ... | just _  | just _  | m       = m
    ... | nothing | nothing | nothing with h R | hh x
    ...   | true  | e = subst′ e (just x)
      where subst′ : ∀ {c} → true ≡ c → PickX {N} (just R) (just R′) → PickX {N} (just R) (if c then just R′ else nothing)
            subst′ refl m = m
    ...   | false | e = subst′ e nothing
      where subst′ : ∀ {c} → false ≡ c → PickX {N} nothing nothing → PickX {N} nothing (if c then just R′ else nothing)
            subst′ refl m = m

    -- The lane each list ends at a row on, alike.
    waitedOn-x : ∀ {N} {Rs : List (P.LaneRec N)} {Rs′ : List (P′.LaneRec N)} → LanesX′ Rs Rs′ → ∀ c
               → MP.Pointwise (λ w w′ → LaneX (proj₁ w) (proj₁ w′)) (P.waitedOn Rs c) (P′.waitedOn Rs′ c)
    waitedOn-x [] c = nothing
    waitedOn-x (_∷_ {R} {R′} x xs) c with endsAt (P.LaneRec.tab R) c | endsAt (P′.LaneRec.tab R′) c | endsAt-≡ (tab-x x) c
    ... | just _  | just _  | just _  = just x
    ... | nothing | nothing | nothing = waitedOn-x xs c

    -- THE MAP, ALIKE: alike picks of the holder and the lane ending above
    -- give one image, the source read through its alike map.
    module _ (op : FlatOp) (lanes : ∀ N → List (P.LaneRec N)) (lanes′ : ∀ N → List (P′.LaneRec N)) where
      rowφ-x : ∀ {N y m m′ e e′} → PickX m m′ → PickX e e′ → P.Tabs.rowφ op lanes N y m e ≡ P′.Tabs.rowφ op lanes′ N y m′ e′
      rowφ-x {N} {y} (just x) _ = if-≡ (cong (λ t → endAt t y) (tab-x x)) (λ _ → end-x x y) (λ _ → out-x x y)
      rowφ-x {N} {y} nothing (just x) = cong (_⊕ [ ix 0 ]) (end-x x (up y))
      rowφ-x {N} {y} nothing nothing =
        if-≡ {b = isMarker N y} {b′ = isMarker N y} refl (λ _ → cong (λ u → (u ⊕ˡ (sub X.c₁ ∷ ix 1 ∷ ix 0 ∷ [])) ⊕ [ ix 0 ]) (Same.φ≡ (os≡ N (up y))))
                  (λ _ → if-≡ {b = endAt (S N) y} {b′ = endAt (S N) y} refl (λ _ → cong (λ u → later u P.ttEnd ⊕ [ sub X.c₁ ]) (Same.φ≡ (os≡ N y)))
                                   (λ _ → cong (_⊕ [ sub X.c₁ ]) (Same.φ≡ (os≡ N y))))

      -- The holder late alike, or a source row late alike in the source.
      late-x : ∀ {N y m m′} → PickX m m′ → ¬ P.Tabs.lateAt op lanes N y m → ¬ P′.Tabs.lateAt op lanes′ N y m′
      late-x {y = y} (just x) nl = LaneX.late→ x y nl
      late-x {N} {y} nothing nl (r , lt) = Same.nl→ (os≡ N y) (λ lt₀ → nl (r , lt₀)) lt

      hold-x : ∀ {N} → LanesX′ (lanes N) (lanes′ N) → ∀ y → PickX (P.holder (lanes N) y) (P′.holder (lanes′ N) y)
      hold-x pw y = lastWith-x (λ R → rowAt (P.LaneRec.tab R) y) (λ R → rowAt (P′.LaneRec.tab R) y) (λ x → cong (λ t → rowAt t y) (tab-x x)) pw

      tabs-x : ∀ {N} → LanesX′ (lanes N) (lanes′ N) → ∀ y → P.Tabs.φ′ op lanes N y ≡ P′.Tabs.φ′ op lanes′ N y
      tabs-x pw y =
        rowφ-x (hold-x pw y)
               (lastWith-x (λ R → endAt (P.LaneRec.tab R) (up y)) (λ R → endAt (P′.LaneRec.tab R) (up y)) (λ x → cong (λ t → endAt t (up y)) (tab-x x)) pw)

      tabs-late-x : ∀ {N} → LanesX′ (lanes N) (lanes′ N) → ∀ y → ¬ P.Tabs.Late′ op lanes N y → ¬ P′.Tabs.Late′ op lanes′ N y
      tabs-late-x pw y = late-x (hold-x pw y)

    -- Each value's lane, alike.
    map-x : ∀ N vs → LanesX′ (L.map (P.valRec N) vs) (L.map (P′.valRec N) vs)
    map-x N []       = []
    map-x N (v ∷ vs) = valRec-x v ∷ map-x N vs

    module _ (k : ℕ) (al : Aligned (maps E) ρ p p*) (al′ : Aligned (maps E′) ρ p p*) (lk lk′ : Linked p p*) where
      module CT  = Joiners.Joins.ConcatTab n f s ρ uρ ρι ρ* uρ* E  p p* a  a*  Os  Ls  Lc  k al  lk
      module CT′ = Joiners.Joins.ConcatTab n f s ρ uρ ρι ρ* uρ* E′ p p* a′ a*′ Os′ Ls′ Lc′ k al′ lk′

      -- The bounded merge's lanes, level by level, alike.
      recs-x : ∀ N es {acc acc′} → LanesX′ acc acc′ → LanesX′ (CT.recs N es acc) (CT′.recs N es acc′)
      recs-x N [] pw = pw
      recs-x N ((_ , q , b , ss) ∷ es) {acc} {acc′} pw = recs-x N es (pw-++ pw (cm-pw one-x ss))
        where
          one-x : ∀ x → LanesX′ (CT.one N q b acc x) (CT′.one N q b acc′ x)
          one-x (st , _) = if-pw (does (st ≟ᵖ (q ⊕ [ ix 1 ])))
            (λ _ → maybe-same (valAtPos N q) (λ v → valRec-x v ∷ []))
            (λ _ → maybe-pw (waitedOn-x pw (up st)) (λ { {R , cx} {R′ , cx′} x → queuedRec-x x cx cx′ b ∷ [] }))

      concat-x : ∀ N y → Same CT.rel′ CT′.rel′ N y
      concat-x N y = same (tabs-x (mergeᶠ (just k)) lanes lanes′ pw y) (tabs-late-x (mergeᶠ (just k)) lanes lanes′ pw y)
        where
          lanes  = λ N → CT.recs N (CT.entriesAt N) []
          lanes′ = λ N → CT′.recs N (CT′.entriesAt N) []
          pw = recs-x N (Runs.entriesAt n f s ρ p k N) []

    -- The exhaust's lanes, alike.
    ranLanes : ∀ N → List (P.LaneRec N)
    ranLanes N = L.concatMap (λ v → if anyᵇ (λ q → does (q ≟ᵖ ValAt.q v)) (Runs.ranAt n f s ρ p N) then [ P.valRec N v ] else []) (valsAt N)

    ranLanes′ : ∀ N → List (P′.LaneRec N)
    ranLanes′ N = L.concatMap (λ v → if anyᵇ (λ q → does (q ≟ᵖ ValAt.q v)) (Runs.ranAt n f s ρ p N) then [ P′.valRec N v ] else []) (valsAt N)

    ran-x : ∀ N → LanesX′ (ranLanes N) (ranLanes′ N)
    ran-x N = cm-pw (λ v → if-pw (anyᵇ (λ q → does (q ≟ᵖ ValAt.q v)) (Runs.ranAt n f s ρ p N)) (λ _ → valRec-x v ∷ []) (λ _ → [])) (valsAt N)

    -- THE JOINERS' MAP AND LATE ROWS ARE THE SUBSCRIPTIONS'.
    joiners-coh : ∀ op (al : Aligned (maps E) ρ p p*) (al′ : Aligned (maps E′) ρ p p*) (lk lk′ : Linked p p*) N y
                → Same (Joiners.flat-core n f s ρ uρ ρι ρ* uρ* E  p p* a  a*  op Os  Ls  Lc  al  lk)
                       (Joiners.flat-core n f s ρ uρ ρι ρ* uρ* E′ p p* a′ a*′ op Os′ Ls′ Lc′ al′ lk′) N y
    joiners-coh (mergeᶠ nothing) al al′ lk lk′ N y =
      same (tabs-x (mergeᶠ nothing) vl vl′ (map-x N (valsAt N)) y) (tabs-late-x (mergeᶠ nothing) vl vl′ (map-x N (valsAt N)) y)
      where vl  = λ N → L.map (P.valRec N) (valsAt N)
            vl′ = λ N → L.map (P′.valRec N) (valsAt N)
    joiners-coh (mergeᶠ (just k)) al al′ lk lk′ = concat-x k al al′ lk lk′
    joiners-coh switchᶠ al al′ lk lk′ N y =
      same (tabs-x switchᶠ vl vl′ (map-x N (valsAt N)) y) (tabs-late-x switchᶠ vl vl′ (map-x N (valsAt N)) y)
      where vl  = λ N → L.map (P.valRec N) (valsAt N)
            vl′ = λ N → L.map (P′.valRec N) (valsAt N)
    joiners-coh exhaustᶠ al al′ lk lk′ N y =
      same (tabs-x exhaustᶠ ranLanes ranLanes′ (ran-x N) y) (tabs-late-x exhaustᶠ ranLanes ranLanes′ (ran-x N) y)
