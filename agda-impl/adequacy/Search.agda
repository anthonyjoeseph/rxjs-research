{-# OPTIONS --guardedness #-}

-- THE LEAST MARK LEADS THE ROWS: whatever `seek` finds under a node is
-- keyed no later than every row the node still owes, and an event it
-- shows sits at that key, as a row.  Finding nothing, the node owes
-- nothing.  A joiner's race is the only real case: the outer wins only
-- strictly before every lane, and a value it shows is a skip just past it.
module adequacy.Search where

open import Data.Bool using (Bool; true; false; T; _∧_; if_then_else_; not)
open import Data.Bool.Properties using (T-≡)
open import Function.Bundles using (Equivalence)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; pred; _≡ᵇ_; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.List.Relation.Unary.All using (lookup) renaming (_∷_ to _∷ᴬ_)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Relation.Nullary using (¬_)
open import Data.List.Properties using (∷ʳ-injectiveˡ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; Timeline; ix; last; <ᵖ-split; <ᵖ-part)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; pin; end; _≺_; _≼_; Truncate; module TakeWhile; DenEnv;
  module Joining; module Values)
open import denotation.Laws.Modulus using (≼-refl)
open import denotation.Laws.Worlds using (InvAt; Hots; W; inW; plain-ix; apart-w) renaming (⊑-refl to ⊑ᵖ-refl)
open import operation.Key using (at; after; _<ᴷ_; at-<ᵖ)
open import operation.PureObservable using (module Machine)

open Machine using (St; Ctx; CS; Cand; Found; found; Focus; Mark; Out; still; shows; seek; kids; lanes; own; ownBest; raceT; outerT; laneT; sourceT; retag; first; mapT; scanT; takeT; cutT; shift; alive; outOf; ofM; closed;
                    free; cpAt; cutAt; overAt; inScan; inTake; inSrc; inBody;
                    ofS; doneS; mapS; cutS; cpM; cutM; lnS; flatS; coldS; scanS; takeS; connS; joinS; inMap; inCut; inLn; inOuter; inLanes; nx; cp; attached; attAt; attM; pend) renaming (Ev to Evᴹ; over to overᶜ)
open import adequacy.Rows using (acc-val; rows; rowsL; pendRows; toEv; Lanes; Each; Kth; AllEnd; EndsOf; Lane; reads; module Flat; module SwitchF; module ExhaustF; module BoundedF; ∅; Hot; Inbox; _∪_; Kept; Stops) renaming (kept to keptᴿ; stop to stopᴿ; left to leftᴿ; sub to subᴿ)
open import adequacy.Bound using (Apart; <→⊑; Bd; Empty; From; Good; GoodL; GoodLn; MergeG; OK; OKL; Single; _⊑_; empty-any; ext-⊑; from-any; from-empty; from-weak; ix01; kept; lane-ok; lane-v; lanes-first; mapped; of-from; of-shows; off; on; one-end; own-first; past-⊑; rooted-single; scanned; seek-mark; shift-<; shift-≮; shift-⊑; silenced; ≺→⊑; ⊑-refl; ⊑-trans; ⊑i; ⊑→≼)

open _⊑_
open Bd

-- A joiner with nothing queued, by its policy: where its lanes start,
-- what it has begun, when it is over and when a lane's end hands off.
module Race {A B : Set} (Ln : Pos → A → EmissionSet B) (O : EmissionSet A) (Bg : EmissionSet B) (Over Runs : Pos → Set)
            (Cut : Pos → Pos → Set) (Hand : Pos → Set) (Ls : List (EmissionSet B)) (d : Bool) (n : ℕ)
            (sO : Single O) (over : T d → Empty O)
            (lane-after : ∀ {q a k e} → Ln q a k e → at (q ++ [ ix 0 ]) ⊑ at k)
            (bg-from : ∀ {K} → Each (From K) Ls → From K Bg)
            (bg-empty : Each Empty Ls → Empty Bg)
            (bg-at : ∀ {c e} → From (at c) O → Lanes Ls c e → Bg c e)
            (over-outer : ∀ {c} → O c end → n ≡ 0 → Over c)
            (over-lane : ∀ {c} → Lanes Ls c end → T d → pred n ≡ 0 → Over c)
            (no-hand : ∀ {c} → T d → ¬ Hand c) where
  open Joining Ln O Bg Over Runs Cut Hand

  -- A lane's row no earlier than its value's.
  lane-from : ∀ {K q a k e} → K ⊑ at q → Ln q a k e → K ⊑ at k
  lane-from u l = ⊑-trans u (⊑-trans (ext-⊑ _ [ ix 0 ]) (lane-after l))

  -- Every row of the joiner sits no earlier than some row of a part:
  -- `K` bounding the outer's and the lanes', it bounds the joiner's.
  rows-from : ∀ K → From K O → Each (From K) Ls → From K JoinT
  rows-from K fo fl (val r)             = ⊑-trans (fo r) (ext-⊑ _ [ ix 0 ])
  rows-from K fo fl (step r)            = fo r
  rows-from K fo fl (opin r)            = fo r
  rows-from K fo fl (oend r _)          = fo r
  rows-from K fo fl (opass r _)         = fo r
  rows-from K fo fl (lane r _ l _ _)    = lane-from (fo r) l
  rows-from K fo fl (lend r _ l _ _ _)  = lane-from (fo r) l
  rows-from K fo fl (lpass r _ l _ _ _) = lane-from (fo r) l
  rows-from K fo fl (hand r _ l _ _)    = ⊑-trans (lane-from (fo r) l) (ext-⊑ _ [ ix 0 ])
  rows-from K fo fl (left r _ l _ _)    = lane-from (fo r) l
  rows-from K fo fl (run x _)           = bg-from fl x
  rows-from K fo fl (rend x _ _)        = bg-from fl x
  rows-from K fo fl (rpass x _ _)       = bg-from fl x
  rows-from K fo fl (rhand x _)         = ⊑-trans (bg-from fl x) (ext-⊑ _ [ ix 0 ])

  -- A lane's row past its value, the value no earlier than `q₀`.
  lane-past : ∀ {q₀ q a k e} → at q₀ ⊑ at q → Ln q a k e → at (q₀ ++ [ ix 0 ]) ⊑ at k
  lane-past u l = ⊑-trans (shift-≮ _ (at _) u) (lane-after l)

  -- The outer showing a value at `q₀`: every row sits just past it or later.
  past-val : ∀ {q₀ a} → O q₀ (out a) → From (at q₀) O → Each (From (at (q₀ ++ [ ix 0 ]))) Ls → From (at (q₀ ++ [ ix 0 ])) JoinT
  past-val v fo fl (val r)             = shift-≮ _ (at _) (fo r)
  past-val v fo fl (step r)            = past-⊑ (fo r) λ { refl → skip≢ (sO v r) }
    where skip≢ : ∀ {a} → out a ≡ skip → ⊥
          skip≢ ()
  past-val v fo fl (opin r)            = past-⊑ (fo r) λ { refl → pin≢ (sO v r) }
    where pin≢ : ∀ {a r′} → out a ≡ pin r′ → ⊥
          pin≢ ()
  past-val v fo fl (oend r _)          = past-⊑ (fo r) λ { refl → end≢ (sO v r) }
    where end≢ : ∀ {a} → out a ≡ end → ⊥
          end≢ ()
  past-val v fo fl (opass r _)         = past-⊑ (fo r) λ { refl → end≢ (sO v r) }
    where end≢ : ∀ {a} → out a ≡ end → ⊥
          end≢ ()
  past-val v fo fl (lane r _ l _ _)    = lane-past (fo r) l
  past-val v fo fl (lend r _ l _ _ _)  = lane-past (fo r) l
  past-val v fo fl (lpass r _ l _ _ _) = lane-past (fo r) l
  past-val v fo fl (hand r _ l _ _)    = ⊑-trans (lane-past (fo r) l) (ext-⊑ _ [ ix 0 ])
  past-val v fo fl (left r _ l _ _)    = lane-past (fo r) l
  past-val v fo fl (run x _)           = bg-from fl x
  past-val v fo fl (rend x _ _)        = bg-from fl x
  past-val v fo fl (rpass x _ _)       = bg-from fl x
  past-val v fo fl (rhand x _)         = ⊑-trans (bg-from fl x) (ext-⊑ _ [ ix 0 ])

  -- The outer's end at `q₀` with no lane running ends the joiner.
  outer-done : ∀ {q₀} → O q₀ end → From (at q₀) O → n ≡ 0 → Done q₀
  outer-done r fo z = over-outer r z , (λ v _ lt _ → ⊥-elim (⊑→≼ (fo v) lt))

  -- A lane's end at `q`, the outer done and no other lane running, ends it.
  lane-done : ∀ {q} → Lanes Ls q end → T d → pred n ≡ 0 → Done q
  lane-done x td pn = over-lane x td pn , (λ v _ _ _ → ⊥-elim (over td v))

  empty-flat : Empty O → Each Empty Ls → Empty JoinT
  empty-flat eo el (val r)             = eo r
  empty-flat eo el (step r)            = eo r
  empty-flat eo el (opin r)            = eo r
  empty-flat eo el (oend r _)          = eo r
  empty-flat eo el (opass r _)         = eo r
  empty-flat eo el (lane r _ _ _ _)    = eo r
  empty-flat eo el (lend r _ _ _ _ _)  = eo r
  empty-flat eo el (lpass r _ _ _ _ _) = eo r
  empty-flat eo el (hand r _ _ _ _)    = eo r
  empty-flat eo el (left r _ _ _ _)    = eo r
  empty-flat eo el (run x _)           = bg-empty el x
  empty-flat eo el (rend x _ _)        = bg-empty el x
  empty-flat eo el (rpass x _ _)       = bg-empty el x
  empty-flat eo el (rhand x _)         = bg-empty el x

  -- A lane winning, the outer no earlier.
  lane-wins : ∀ {R} (g : Found R) K (o′ : Out B) → From K O → OKL Ls (just (g , K , o′)) → OK JoinT (just (g , laneT {A = A} d n [] K o′))
  lane-wins g K still fo (fl , ml , sl) =
    record { from = rows-from K fo fl ; mark = ml ; shown = λ () }
  lane-wins g K (shows (nx b)) fo (fl , ml , sl) =
    record { from = rows-from K fo fl ; mark = ml
           ; shown = λ { refl → let (q , k , x) = sl refl in q , k , run (bg-at (subst (λ K′ → From K′ O) k fo) x) tt } }
  lane-wins g K (shows cp) fo (fl , ml , sl) = ends d refl (pred n ≡ᵇ 0) refl
    where
      ends : ∀ b → d ≡ b → ∀ c → (pred n ≡ᵇ 0) ≡ c → OK JoinT (just (g , K , (if b ∧ c then shows cp else still)))
      ends true  de true  pn = record { from = rows-from K fo fl ; mark = ml
                                      ; shown = λ { refl → let (q , k , x) = sl refl ; td = subst T (sym de) tt in
                                                    q , k , rend (bg-at (subst (λ K′ → From K′ O) k fo) x) (no-hand td) (lane-done x td (≡ᵇ⇒≡ (pred n) 0 (subst T (sym pn) tt))) } }
      ends true  de false pn = record { from = rows-from K fo fl ; mark = ml ; shown = λ () }
      ends false de c     pn = record { from = rows-from K fo fl ; mark = ml ; shown = λ () }

  -- The outer winning, the lanes no earlier than just past its key.
  outer-wins : ∀ {R} (f : Found R) h (o : Out A) → Bd O (Found.key f) h o → Each (From (shift h)) Ls → OK JoinT (just (f , outerT n [] h o))
  outer-wins f h still b fl =
    record { from = rows-from h (from b) (from-weak Ls (shift-⊑ h) fl) ; mark = mark b ; shown = λ () }
  outer-wins f h (shows (nx a)) b fl with shown b refl
  ... | q₀ , refl , v = record { from = past-val v (from b) fl ; mark = ⊑-trans (mark b) (shift-⊑ (at q₀)) ; shown = λ () }
  outer-wins f h (shows cp) b fl = ends (n ≡ᵇ 0) refl
    where
      ends : ∀ z → (n ≡ᵇ 0) ≡ z → OK JoinT (just (f , h , (if z ∧ true then shows cp else still)))
      ends false nz = record { from = rows-from h (from b) (from-weak Ls (shift-⊑ h) fl) ; mark = mark b ; shown = λ () }
      ends true  nz with shown b refl
      ... | q₀ , refl , r = record { from = rows-from (at q₀) (from b) (from-weak Ls (shift-⊑ (at q₀)) fl) ; mark = mark b
                                   ; shown = λ { refl → q₀ , refl , oend r (outer-done r (from b) (≡ᵇ⇒≡ n 0 (subst T (sym nz) tt))) } }

  race-ok : ∀ {R} (x : Maybe (Cand R A)) (y : Maybe (Cand R B)) → OK O x → OKL Ls y → OK JoinT (raceT d n [] x y)
  race-ok nothing            nothing             eo el = empty-flat eo el
  race-ok nothing            (just (g , k , o′)) eo bl = lane-wins g k o′ (λ r → ⊥-elim (eo r)) bl
  race-ok (just (f , h , o)) nothing             b  el = outer-wins f h o b (from-empty Ls el)
  race-ok (just (f , h , o)) (just (g , k , o′)) b  bl with h <ᴷ k in lt
  ... | true  = outer-wins f h o b (from-weak Ls (shift-< h k lt) (proj₁ bl))
  ... | false = lane-wins g k o′ (λ r → ⊑-trans (⊑i lt) (from b r)) bl

-- No lane running, by its count.
none-run : ∀ {B} {c} n (Ls : List (EmissionSet B)) → n ≡ 0 → AllEnd (_≼ c) n (EndsOf Ls)
none-run {c = c} n Ls z = subst (λ k → AllEnd (_≼ c) k (EndsOf Ls)) (sym z) tt

-- A lane begun at its value's second child, past it.
read-after : ∀ {A B} {L : A → Pos → EmissionSet B} {q a k e} → Lane L q a k e → at (q ++ [ ix 0 ]) ⊑ at k
read-after (reads _ s) = ⊑-trans (ix01 _) (≺→⊑ s)

-- A begun lane's row at or before every outer row: no value has cut it.
switch-at : ∀ {A B} (L : A → Pos → EmissionSet B) O Ls d n {c e} → From (at c) O → Lanes Ls c e → SwitchF.Bg L O d n Ls c e
switch-at L O Ls d n fo x = SwitchF.bg x (λ (_ , _ , v , lt) → ⊑→≼ (fo v) lt)

-- Nothing queued, a lane's end hands off to none: no value is at it, and
-- none arrived before it.
bounded-unqueued : ∀ {A B} m (L : A → Pos → EmissionSet B) O Ls d n {c} → Apart O (Lanes Ls) → From (at c) O → Lanes Ls c end
                 → ¬ BoundedF.Queued m L O d n [] Ls c
bounded-unqueued m L O Ls d n {c} ap fo x (_ , _ , _ , BoundedF.Item.queued () , _)
bounded-unqueued m L O Ls d n {c} ap fo x (_ , _ , a , BoundedF.Item.outer {q = q} v , st) =
  starts st (λ eq → ap (subst (λ q′ → O q′ (out a)) (∷ʳ-injectiveˡ q c eq) (valued v)) x) (λ {c′} eq qc → ⊑→≼ (fo (valued v)) (subst (q ≺_) (∷ʳ-injectiveˡ c′ c eq) qc))
  where
    open Values O using (Nth) renaming (first to first₀; next to next₀)
    valued : ∀ {i q a} → Nth i q a → O q (out a)
    valued (first₀ x _)    = x
    valued (next₀ _ x _ _) = x
    starts : ∀ {i ls q s} → BoundedF.Starts m L O d n [] Ls i ls (just q) s → (q ++ [ ix 1 ] ≡ s → ⊥) → (∀ {c′} → c′ ++ [ ix 1 ] ≡ s → q ≺ c′ → ⊥) → ⊥
    starts (BoundedF.Starts.room _)            h₁ _  = h₁ refl
    starts (BoundedF.Starts.freed _ _)         h₁ _  = h₁ refl
    starts {q = q} (BoundedF.Starts.queued {c = c₁} _ qc _ _ _) _ h₂ = h₂ {c₁} refl qc

-- Each policy's race, from its outer's and its lanes' finds.
Races : ∀ {A B} → (R : Set) → EmissionSet A → List (EmissionSet B) → Bool → ℕ → EmissionSet B → Set₁
Races R O Ls d n J = ∀ (x : Maybe (Cand R _)) (y : Maybe (Cand R _)) → OK O x → OKL Ls y → OK J (raceT d n [] x y)

flat-race : ∀ {R A B} (L : A → Pos → EmissionSet B) O Ls d n → Single O → (T d → Empty O) → Races R O Ls d n (Flat.JoinT L O d n Ls)
flat-race L O Ls d n sO sp =
  Race.race-ok (Lane L) O (Lanes Ls) Over (λ _ → ⊤) (λ _ _ → ⊥) (λ _ → ⊥) Ls d n sO sp read-after (from-any Ls) (empty-any Ls) (λ _ x → x)
    (λ {c} r z → over-at (inj₂ (c , r , ≼-refl {c})) (none-run {c = c} n Ls z)) (λ {c} x td pn → over-at (inj₁ td) (one-end n Ls pn {c} x)) (λ _ ())
  where open Flat L O d n Ls using (Over; over-at)

switch-race : ∀ {R A B} (L : A → Pos → EmissionSet B) O Ls d n → Single O → (T d → Empty O) → Races R O Ls d n (SwitchF.JoinT L O d n Ls)
switch-race L O Ls d n sO sp =
  Race.race-ok (Lane L) O Bg Over (λ _ → ⊤) Cut (λ _ → ⊥) Ls d n sO sp read-after bg-from bg-empty
    (switch-at L O Ls d n)
    (λ {c} r z → inj₂ (c , r , ≼-refl {c}) , inj₁ (none-run {c = c} n Ls z)) (λ {c} x td pn → inj₁ td , inj₁ (one-end n Ls pn {c} x)) (λ _ ())
  where
    open SwitchF L O d n Ls using (Bg; bg; bpin; Over; Cut)
    bg-from : ∀ {K} → Each (From K) Ls → From K Bg
    bg-from fl (bg x _)     = from-any Ls fl x
    bg-from fl (bpin x _ _) = from-any Ls fl x
    bg-empty : Each Empty Ls → Empty Bg
    bg-empty el (bg x _)     = empty-any Ls el x
    bg-empty el (bpin x _ _) = empty-any Ls el x

exhaust-race : ∀ {R A B} (L : A → Pos → EmissionSet B) O Ls d n → Single O → (T d → Empty O) → Races R O Ls d n (ExhaustF.JoinT L O d n Ls)
exhaust-race L O Ls d n sO sp =
  Race.race-ok (Lane L) O (Lanes Ls) Over Run (λ _ _ → ⊥) (λ _ → ⊥) Ls d n sO sp read-after (from-any Ls) (empty-any Ls) (λ _ x → x)
    (λ {c} r z → inj₂ (c , r , ≼-refl {c}) , none-run {c = c} n Ls z) (λ {c} x td pn → inj₁ td , one-end n Ls pn {c} x) (λ _ ())
  where open ExhaustF L O d n Ls using (Over; Run)

-- Nothing queued: no lane waits, and with the outer done none starts.
bounded-race : ∀ {R A B} m (L : A → Pos → EmissionSet B) O Ls d n → Single O → (T d → Empty O) → Races R O Ls d n (BoundedF.JoinT m L O d n [] Ls)
bounded-race m L O Ls d n sO sp =
  Race.race-ok LaneB O Bg Over Indexed (λ _ _ → ⊥) Queued Ls d n sO sp lane-after bg-from bg-empty (λ _ x → begun x)
    (λ {c} r z → inj₂ (c , r , ≼-refl {c}) , counted {c} (none-run {c = c} n Ls z))
    (λ {c} x td pn → inj₁ td , counted {c} (one-end n Ls pn {c} x)) no-hand
  where
    open BoundedF m L O d n [] Ls using (LaneB; Bg; begun; waits; Over; Indexed; Queued; Item; Starts)
    open Values O using (Nth) renaming (first to first₀; next to next₀)
    counted : ∀ {c} → AllEnd (_≼ c) n (EndsOf Ls) → AllEnd (_≼ c) (n + 0) (EndsOf Ls)
    counted {c} = subst (λ k → AllEnd (_≼ c) k (EndsOf Ls)) (sym (+-identityʳ n))
    lane-after : ∀ {q a k e} → LaneB q a k e → at (q ++ [ ix 0 ]) ⊑ at k
    lane-after (_ , _ , (_ , Starts.room _) , subᴿ _ s)     = ⊑-trans (ix01 _) (≺→⊑ s)
    lane-after (_ , _ , (_ , Starts.freed _ _) , subᴿ _ s)  = ⊑-trans (ix01 _) (≺→⊑ s)
    lane-after (_ , _ , (_ , Starts.queued {c = c} _ qc _ _ _) , subᴿ _ s) =
      ⊑-trans (past-⊑ (≺→⊑ qc) λ eq → ⊑→≼ {c} {c} (⊑-refl (at c)) (subst (_≺ c) eq qc)) (⊑-trans (ext-⊑ c [ ix 1 ]) (≺→⊑ s))
    bg-from : ∀ {K} → Each (From K) Ls → From K Bg
    bg-from fl (begun x)                  = from-any Ls fl x
    bg-from fl (waits (Item.queued () , _) _)
    bg-empty : Each Empty Ls → Empty Bg
    bg-empty el (begun x)                  = empty-any Ls el x
    bg-empty el (waits (Item.queued () , _) _)
    valued : ∀ {i q a} → Nth i q a → O q (out a)
    valued (first₀ x _)     = x
    valued (next₀ _ x _ _)  = x
    no-hand : ∀ {c} → T d → ¬ Queued c
    no-hand td (_ , _ , _ , Item.queued () , _)
    no-hand td (_ , _ , _ , Item.outer v , _) = sp td (valued v)

-- As entered: nothing lies before where a mark is keyed, so what it
-- shows has nothing before it.
ok-trunc : ∀ {R A} {t : EmissionSet A} (x : Maybe (Cand R A)) → OK t x → OK (Truncate t) x
ok-trunc nothing            e (r , _) = e r
ok-trunc (just (f , K , o)) b =
  record { from = λ (r , _) → from b r ; mark = mark b
         ; shown = λ eq → let (q , k , r) = shown b eq in q , k , r , ([] , λ {k′} y lt → ⊥-elim (⊑→≼ (subst (_⊑ at k′) k (from b y)) lt)) }

------------------------------------------------------------------------
-- A take

postulate
  -- A GOOD NODE'S ROWS HOLD ONE EVENT A POSITION.
  rows-single : ∀ {A} {ρ : DenEnv []} (s : St [] A) → Good ρ s → Single (rows ρ s)

-- At or past where it was decided, one of `p` and `q` before the other.
⊑-split : ∀ {p q} → at p ⊑ at q → p ≺ q ⊎ p ≡ q
⊑-split {p} {q} pq with <ᵖ-split p q (trans (sym (at-<ᵖ q p)) (un pq))
... | inj₁ lt = inj₁ (Equivalence.from T-≡ lt)
... | inj₂ eq = inj₂ eq

-- A take's row lies at or just past its source's.
take-src : ∀ {A} {i} {w : A → Bool} {t : EmissionSet A} {k e} → TakeWhile.TakeT i w t k e → Σ Pos λ q → Σ (Ev A) λ e′ → t q e′ × at q ⊑ at k
take-src (TakeWhile.pass r _ _)   = _ , _ , r , ⊑-refl _
take-src (TakeWhile.fail r _ _ _) = _ , _ , r , ext-⊑ _ [ ix 0 ]
take-src (TakeWhile.stop r _ _)   = _ , _ , r , ext-⊑ _ [ last ]
take-src (TakeWhile.step r _)     = _ , _ , r , ⊑-refl _
take-src (TakeWhile.tend r _)     = _ , _ , r , ⊑-refl _
take-src (TakeWhile.left r _ _)   = _ , _ , r , ⊑-refl _

take-from : ∀ {A} {i} {w : A → Bool} {t : EmissionSet A} K → From K t → From K (TakeWhile.TakeT i w t)
take-from K fr x = let (_ , _ , r , le) = take-src x in ⊑-trans (fr r) le

-- Nothing fails before the least row.
unfailed : ∀ {A} {i} {w : A → Bool} {t : EmissionSet A} {q₀} → From (at q₀) t → ¬ TakeWhile.Failed i w t q₀
unfailed fr (_ , _ , r , _ , lt) = ⊑→≼ (fr r) lt

noPin : ∀ {A} {a : A} {r} → out a ≡ pin r → ⊥
noPin ()

-- Past a failing value at the least row, every row of the take lies just
-- past it.
past-fail : ∀ {A} {i} {w : A → Bool} {t : EmissionSet A} {q₀ a} → Single t → t q₀ (out a) → w a ≡ false → From (at q₀) t
          → From (at (q₀ ++ [ ix 0 ])) (TakeWhile.TakeT i w t)
past-fail {w = w} {a = a} sg r wa fr (TakeWhile.pass r′ kp nf) with ⊑-split (fr r′)
... | inj₁ lt   = ⊥-elim (nf (_ , _ , r , subst (λ b → T (not b)) (sym wa) tt , lt))
... | inj₂ refl with sg r r′
... | refl = ⊥-elim (subst T wa kp)
past-fail sg r wa fr (TakeWhile.fail r′ _ _ _) = shift-≮ _ (at _) (fr r′)
past-fail {q₀ = q₀} sg r wa fr (TakeWhile.stop r′ _ nf) with ⊑-split (fr r′)
... | inj₁ lt   = ⊥-elim (nf (_ , _ , r , subst (λ b → T (not b)) (sym wa) tt , lt))
... | inj₂ refl = ≺→⊑ (subst T (sym (<ᵖ-part q₀ {ix 0} {last} [] [] refl)) tt)
past-fail sg r wa fr (TakeWhile.step r′ nf) with ⊑-split (fr r′)
... | inj₁ lt   = ⊥-elim (nf (_ , _ , r , subst (λ b → T (not b)) (sym wa) tt , lt))
... | inj₂ refl with sg r r′
... | ()
past-fail sg r wa fr (TakeWhile.tend r′ nf) with ⊑-split (fr r′)
... | inj₁ lt   = ⊥-elim (nf (_ , _ , r , subst (λ b → T (not b)) (sym wa) tt , lt))
... | inj₂ refl with sg r r′
... | ()
past-fail sg r wa fr (TakeWhile.left r′ _ _) = past-⊑ (fr r′) λ { refl → noPin (sg r r′) }

-- An unfailed take's search: its child's find, a failing value shown
-- just past it if inclusive, else dropped.
take-free : ∀ {R A} i (w : A → Bool) {t : EmissionSet A} (y : Maybe (Cand R A)) → Single t → OK t y → OK (TakeWhile.TakeT i w t) (retag (takeT i w free) y)
take-free i w nothing sg e x = let (_ , _ , r , _) = take-src x in e r
take-free i w (just (f , K , still)) sg b = record { from = take-from K (from b) ; mark = mark b ; shown = λ () }
take-free i w {t} (just (f , K , shows cp)) sg b =
  record { from = take-from K (from b) ; mark = mark b
         ; shown = λ { refl → let (q₀ , k , r) = shown b refl in q₀ , k , TakeWhile.tend r (unfailed {i = i} {w = w} {t = t} (λ r′ → subst (_⊑ at _) k (from b r′))) } }
take-free i w {t} (just (f , K , shows (nx a))) sg b with w a in wa | shown b refl
... | true  | q₀ , refl , r =
  record { from = take-from (at q₀) (from b) ; mark = mark b
         ; shown = λ { refl → q₀ , refl , TakeWhile.pass r (subst T (sym wa) tt) (unfailed {i = i} {w = w} {t = t} (from b)) } }
... | false | q₀ , refl , r with i
...   | true  = record { from = past-fail sg r wa (from b) ; mark = ⊑-trans (mark b) (shift-⊑ (at q₀))
                       ; shown = λ { refl → q₀ ++ [ ix 0 ] , refl , TakeWhile.fail r (subst (λ b → T (not b)) (sym wa) tt) (unfailed {i = i} {w = w} {t = t} (from b)) tt } }
...   | false = record { from = take-from (at q₀) (from b) ; mark = mark b ; shown = λ () }

-- A failed take's completion, shown at its stop unless closed above.
stop-shown : ∀ {R Γ A} (c : Ctx R Γ A) r {t : EmissionSet A} {e} → (if not (closed c) then shows cp else still) ≡ shows e
           → Σ Pos λ q → at (r ++ [ last ]) ≡ at q × Stops r t q (toEv e)
stop-shown c r eq with closed c
stop-shown c r ()   | true
stop-shown c r refl | false = _ , refl , stopᴿ

take-stop : ∀ {R Γ A} (c : Ctx R Γ A) i (w : A → Bool) r (s : St Γ A) {t : EmissionSet A} (y : Maybe (Cand R A)) → OK t y
          → OK (Stops r t) (first (just (found (_ , _ , c , takeS i w (cpAt r) s) cpM (at (r ++ [ last ])) , at (r ++ [ last ]) , outOf c (takeS i w (cpAt r) s) cpM))
                                  (retag (takeT i w (cpAt r)) y))
take-stop c i w r s nothing e =
  record { from = λ { stopᴿ → ⊑-refl _ ; (leftᴿ (keptᴿ x _ _)) → ⊥-elim (e x) } ; mark = ⊑-refl _ ; shown = stop-shown c r }
take-stop c i w r s (just (g , h , o)) b with h <ᴷ at (r ++ [ last ]) in lt
... | true  = record { from = λ { stopᴿ → <→⊑ h _ lt ; (leftᴿ (keptᴿ x _ _)) → from b x } ; mark = mark b ; shown = λ () }
... | false = record { from = λ { stopᴿ → ⊑-refl _ ; (leftᴿ (keptᴿ x _ _)) → ⊑-trans (⊑i lt) (from b x) } ; mark = ⊑-refl _ ; shown = stop-shown c r }

-- Past its stop, a take keeps only its source's surviving pins, shown
-- by no find.
kept-ok : ∀ {R A} i (w : A → Bool) o {r} {t : EmissionSet A} → (o ≡ free → ⊥) → (y : Maybe (Cand R A)) → OK t y → OK (Kept r t) (retag (takeT i w o) y)
kept-ok i w free       nf y b = ⊥-elim (nf refl)
kept-ok i w (cpAt _)   nf nothing e (keptᴿ x _ _) = e x
kept-ok i w (cutAt _)  nf nothing e (keptᴿ x _ _) = e x
kept-ok i w (overAt _) nf nothing e (keptᴿ x _ _) = e x
kept-ok i w (cpAt _)   nf (just (f , K , o)) b = record { from = λ { (keptᴿ x _ _) → from b x } ; mark = mark b ; shown = λ () }
kept-ok i w (cutAt _)  nf (just (f , K , o)) b = record { from = λ { (keptᴿ x _ _) → from b x } ; mark = mark b ; shown = λ () }
kept-ok i w (overAt _) nf (just (f , K , o)) b = record { from = λ { (keptᴿ x _ _) → from b x } ; mark = mark b ; shown = λ () }

------------------------------------------------------------------------
-- Every node

-- Under a cut switched off: silent whatever it holds.
seek-off : ∀ {R Γ A} {ρ : DenEnv Γ} (c : Ctx R Γ A) a (s : St Γ A) → OK (rows ρ (cutS false a s)) (seek c (cutS false a s))
seek-off c attached s = silenced (seek (inCut false attached c) s) (seek-mark (inCut false attached c) s)
seek-off c (attAt p) s =
  own-first (_ , _ , c , cutS false (attAt p) s) attM (after p) _ (silenced (seek (inCut false (attAt p) c) s) (seek-mark (inCut false (attAt p) c) s))

postulate
  -- A CONNECT'S SEEK LEADS ITS ROWS: whatever its source and body find,
  -- the source winning only strictly before the body, keys every row the
  -- connect still owes, its body's joiners' unfed rows included.
  --
  -- DEAD ROUTE: recursing into the body as `seek-ok` does into every
  --   other node: `seek-ok` is stated at an empty environment, and a
  --   joiner's rows read its binder, so no joiner's OK holds apart from
  --   the source it reads.
  -- DEAD ROUTE: reading the body under a quiet binder to reuse `seek-ok`:
  --   `G` and `rows` read the environment, so a body good under its real
  --   binder says nothing under a quiet one.
  conn-ok : ∀ {R A X} {ρ : DenEnv []} (c : Ctx R [] A) k (o : St [] X) (b : St (X ∷ []) A) → Good ρ (connS k o b) → OK (rows ρ (connS k o b)) (seek c (connS k o b))

  -- A COLD'S DUE MARK KEYS ITS ROWS: the next step of its tape, a frame's
  -- value, stall or close, or its completion owed; a dead cold owes none.
  cold-ok : ∀ {R A} {ρ : DenEnv []} (c : Ctx R [] A) b l → OK (rows ρ (coldS b l)) (seek c (coldS b l))

  -- A BOUNDED MERGE'S SEARCH WITH VALUES WAITING KEYS ITS ROWS: a lane's
  -- end hands off to the queue's first just past it, the merge's end
  -- owed by none.
  bounded-wait-ok : ∀ {R A B} {ρ : DenEnv []} (c : Ctx R [] B) m (f : A → Obs Timeline [] B) d n a q (o : St [] A) ls
                  → Good ρ (flatS (mergeᶠ (just m)) f d n (a ∷ q) o ls) → OK (rows ρ (flatS (mergeᶠ (just m)) f d n (a ∷ q) o ls)) (seek c (flatS (mergeᶠ (just m)) f d n (a ∷ q) o ls))

mutual
  seek-ok : ∀ {R A} {ρ : DenEnv []} (c : Ctx R [] A) (s : St [] A) → Good ρ s → OK (rows ρ s) (seek c s)
  seek-ok c (ofS i p [])       _ = record { from = of-from p i [] ; mark = ⊑-refl _ ; shown = λ eq → _ , refl , of-shows c i p [] eq }
  seek-ok c (ofS i p (x ∷ xs)) _ = record { from = of-from p i (x ∷ xs) ; mark = ⊑-refl _ ; shown = λ eq → _ , refl , of-shows c i p (x ∷ xs) eq }
  seek-ok c doneS              _ = λ ()
  seek-ok c (connS k o b)      g = conn-ok c k o b g
  seek-ok c (coldS b l)        _ = cold-ok c b l
  seek-ok c (mapS f s)         g = mapped f (seek (inMap f c) s) (seek-ok (inMap f c) s g)
  seek-ok c (scanS f z s)      g = scanned f z (seek (inScan f z c) s) (seek-ok (inScan f z c) s g)
  seek-ok c (takeS i q w s)    g = take-ok c i q w s g
  seek-ok c (cutS true attached s)   g = kept (seek (inCut true attached c) s) (seek-ok (inCut true attached c) s g)
  seek-ok {ρ = ρ} c (cutS false a s) _ = seek-off {ρ = ρ} c a s
  seek-ok c (cutS true (attAt p) s)  g =
    own-first (_ , _ , c , cutS true (attAt p) s) attM (after p) _ (kept (seek (inCut true (attAt p) c) s) (seek-ok (inCut true (attAt p) c) s g))
  seek-ok {ρ = ρ} c (flatS (mergeᶠ nothing) f d n q o ls) g with MergeG.fresh g
  ... | refl = ok-trunc _ (join-ok c (mergeᶠ nothing) f d n o ls (flat-race (λ a → pendRows ρ (f a)) (rows ρ o) (rowsL ρ ls) d n (rooted-single rooted) spent) outer lanesG)
    where open MergeG g
  seek-ok {ρ = ρ} c (flatS (mergeᶠ (just m)) f d n [] o ls) (g , _) =
    ok-trunc _ (join-ok c (mergeᶠ (just m)) f d n o ls (bounded-race m (λ a → pendRows ρ (f a)) (rows ρ o) (rowsL ρ ls) d n (rooted-single rooted) spent) outer lanesG)
    where open MergeG g
  seek-ok c (flatS (mergeᶠ (just m)) f d n (a ∷ q) o ls) g = bounded-wait-ok c m f d n a q o ls g
  seek-ok {ρ = ρ} c (flatS switchᶠ f d n q o ls) g with MergeG.fresh g
  ... | refl = ok-trunc _ (join-ok c switchᶠ f d n o ls (switch-race (λ a → pendRows ρ (f a)) (rows ρ o) (rowsL ρ ls) d n (rooted-single rooted) spent) outer lanesG)
    where open MergeG g
  seek-ok {ρ = ρ} c (flatS exhaustᶠ f d n q o ls) g with MergeG.fresh g
  ... | refl = ok-trunc _ (join-ok c exhaustᶠ f d n o ls (exhaust-race (λ a → pendRows ρ (f a)) (rows ρ o) (rowsL ρ ls) d n (rooted-single rooted) spent) outer lanesG)
    where open MergeG g

  -- A TAKE'S SEARCH KEYS ITS ROWS: unfailed, its child's find retagged; a
  -- failing value's completion owed at its stop; its kept pins after.
  take-ok : ∀ {R A} {ρ : DenEnv []} (c : Ctx R [] A) i q w (s : St [] A) → Good ρ (takeS i q w s) → OK (rows ρ (takeS i q w s)) (seek c (takeS i q w s))
  take-ok {ρ = ρ} c i q free s g =
    ok-trunc (retag (takeT i q free) (seek (inTake i q free c) s))
      (take-free i q (seek (inTake i q free c) s) (rows-single {ρ = ρ} s g) (seek-ok (inTake i q free c) s g))
  take-ok c i q (cpAt r) s g = take-stop c i q r s (seek (inTake i q (cpAt r) c) s) (seek-ok (inTake i q (cpAt r) c) s g)
  take-ok c i q (cutAt r) s g =
    own-first (_ , _ , c , takeS i q (cutAt r) s) cutM (after r) _ (kept-ok i q (cutAt r) (λ ()) (seek (inTake i q (cutAt r) c) s) (seek-ok (inTake i q (cutAt r) c) s g))
  take-ok c i q (overAt r) s g = kept-ok i q (overAt r) (λ ()) (seek (inTake i q (overAt r) c) s) (seek-ok (inTake i q (overAt r) c) s g)

  -- A joiner with nothing queued: its policy's race over its parts' finds.
  join-ok : ∀ {R A B} {ρ : DenEnv []} (c : Ctx R [] B) op (f : A → Obs Timeline [] B) d n (o : St [] A) ls {J : EmissionSet B}
          → (∀ (x : Maybe (Cand R A)) (y : Maybe (Cand R B)) → OK (rows ρ o) x → OKL (rowsL ρ ls) y → OK J (raceT d n [] x y))
          → Good ρ o → GoodL ρ ls → OK J (raceT d n [] (seek (inOuter op f d n [] ls c) o) (lanes c op f d n [] o [] ls))
  join-ok c op f d n o ls rc go gl =
    rc (seek (inOuter op f d n [] ls c) o) (lanes c op f d n [] o [] ls) (seek-ok (inOuter op f d n [] ls c) o go) (lanes-ok c op f d n [] o [] ls gl)

  seek-ln : ∀ {R A} {ρ : DenEnv []} (c : Ctx R [] A) (s : St [] A) → GoodLn ρ s → OK (rows ρ s) (seek c s)
  seek-ln {ρ = ρ} c s g with lane-v s g
  ... | on a s₀ g₀ _ = seek-ok (inLn true c) (cutS true a s₀) g₀
  ... | off a s₀     = seek-off {ρ = ρ} (inLn false c) a s₀

  lanes-ok : ∀ {R A B} {ρ : DenEnv []} (c : Ctx R [] B) op f d n q (o : St [] A) pre (ls : List (St [] B)) → GoodL ρ ls
           → OKL (rowsL ρ ls) (lanes c op f d n q o pre ls)
  lanes-ok c op f d n q o pre []         _          = tt
  lanes-ok c op f d n q o pre (s ∷ post) (gs , gp) =
    lanes-first (retag (cutT (alive s)) (seek (inLanes op f d n q o pre post c) s)) (lanes c op f d n q o (s ∷ pre) post)
      (lane-ok s _ (seek-ln (inLanes op f d n q o pre post c) s gs)) (lanes-ok c op f d n q o (s ∷ pre) post gp)
