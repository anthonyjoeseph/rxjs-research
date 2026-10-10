------------------------------------------------------------------
-- A READ JOINING A CONNECTED SHARE, on both sides: each run registers
-- one row at the slot, the impl's at the stamped slot behind the share,
-- and the pair relates as `read~`.  Only the id counter moves, so every
-- field that names a source, a node or an ordinal stands as it was.
--
-- NEITHER ROW IS DYING: a hot slot is marked dying only once latched
-- (`Store.dying-done`), and both latches are unset.  The share's census
-- keeps its one raw row, since a connected share with no raw row has a
-- latched raw slot.
--
-- THE IMPL'S ROW IS THE READ'S PATH under the restamp, whose map frame
-- has no node: the row threads the nodes the path threads, ends where it
-- ends, and is spent where it is, so both registrations agree.
------------------------------------------------------------------
module Simulation.Slot-Join where

open import Data.Bool    using (Bool; true; false; T; if_then_else_; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Fin     using (Fin; zero; suc; toℕ; _↑ʳ_; _↑ˡ_)
open import Data.Fin.Properties using (toℕ<n; toℕ-injective; ↑ʳ-injective)
open import Data.Vec     using (lookup)
open import Data.List    using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using () renaming ([] to []ᵖ; map to mapᵖ)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᵃ; lookup to lookupᵃ; tabulate to tabulateᵃ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to ++⁺ᵃ)
open import Data.List.Relation.Unary.AllPairs using () renaming ([] to []ᴾ; _∷_ to _∷ᴾ_)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (++⁺ to ++⁺ᴾ)
open import Data.Nat     using (suc; _+_; _≤_; _<_; _<ᵇ_; _≟_)
open import Data.Nat.Properties using (≤-refl; m<n⇒m<1+n; <⇒≢; <-trans; <⇒<ᵇ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Exp       using (Ty; Ctx; Closed; Tm; uniqᵗ; varᵗ)
open import Data.List.Relation.Unary.Any using (here)
open import Rx.Mint      using (counter; setAt; regᵏ; freshId)
open import Rx.Evaluator using (Sched; EvalSt; pathHasNode; LiveSource; RegRow; regSource; sameSource; memberSource; Path; root; share-sink; _↠[_]_;
                                map-f; scan-f; take-f; batchSync-f; from-inner; thru-outer; atSlot; register; spentOn; lowerFloor; memoᶠ)
open import Rx.Evaluator.Reducible.Support using (Rule; Sound; Distinct; endOf; register-sound; row-sound; lower-nodes; lower-end; lower-distinct;
  scripted≢shared)
open import Rx.Evaluator.Unconn-Arith using (keeps-refl)
open import Rx.Prim      using (hot)
open import Rx.Slots     using (scripted)
open import SExp.Simul-Slots using (SimulSlots; hotˢ; plainSlots)
open import SExp.Syntax  using (Kinds; hotᵏ; plainᵏ; emitᵗ)
open import SExp.Elaborate using (restampᵛ; subscribeᵛ)
open import Simulation.Stores using (inv-snoc; Store; Arr; PathRel; Named; Census; Unpaired; RowRel; ArrRows; _∷_; []; read~; root~; sink~;
  map~; scan~; takeWhile~; spentWhile~; outerElem~; outerExplode~; inner~; deferInner~; LiveOn; LiveIf; module LiveIf; thruNodes; live-thru)
open import Simulation.Sweep using (sameSource-no; t≢f; raw≢stamped; stamped<)
open import Simulation.Cut   using (nodesOf; has-node; node-has)
open import Simulation.Hop   using (none-below; guard-snoc; count-snoc; reg-snoc; part-snoc; spent-snoc; arr-snoc; reg-unp; path-spent; rel-vals)
open import Simulation.After using (module Kept)

-- a table read at a slot is the slot
memoᶠ-at : ∀ {m} {P : Fin m → Set} (f : ∀ j → P j) j → memoᶠ f j ≡ f j
memoᶠ-at f zero    = refl
memoᶠ-at f (suc j) = memoᶠ-at (λ j → f (suc j)) j

-- A HOT SLOT READ PLAIN IS ITS SCRIPT, READ IMPL AT ITS STAMPED SLOT A
-- SHARE: neither run's read of it takes the other kinds' rules
plain-hot-slot : ∀ {m} {Δ : Ctx m} {κ : Kinds m} (ins : SimulSlots Δ κ) (j : Fin m) → lookup κ j ≡ hotᵏ
               → Σ _ λ ok → Σ _ λ as → plainSlots ins j ≡ scripted {ok = ok} (hot as)
plain-hot-slot {κ = κ} ins j ek with lookup κ j | ins j
plain-hot-slot ins j refl | hotᵏ | hotˢ _ = _ , _ , refl

-- the id counter moved past the id it handed out, and one row more
-- stands at a source below the slots' bound
named-row : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {f} {sched : Sched Δ} {st : EvalSt e} {r}
          → Named f sched st → regSource (proj₁ (proj₂ r)) < counter (Sched.mint sched) _
          → Named f (record sched { mint = setAt regᵏ (suc (counter (Sched.mint sched) regᵏ)) (Sched.mint sched) })
                    (record st { registry = EvalSt.registry st ++ r ∷ [] })
named-row N lt = record
  { slots-below = Named.slots-below N ; ords-below = Named.ords-below N
  ; srcs-below = ++⁺ᵃ (Named.srcs-below N) (lt ∷ᵃ []ᵃ)
  ; cut-below = mapᵃ m<n⇒m<1+n (Named.cut-below N) ; dlv-below = mapᵃ m<n⇒m<1+n (Named.dlv-below N)
  ; dying-below = Named.dying-below N }

named-reg : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {f} {sched : Sched Δ} {st : EvalSt e}
          → Named f sched st → Named f (record sched { mint = setAt regᵏ (suc (counter (Sched.mint sched) regᵏ)) (Sched.mint sched) }) st
named-reg N = record
  { slots-below = Named.slots-below N ; ords-below = Named.ords-below N ; srcs-below = Named.srcs-below N
  ; cut-below = mapᵃ m<n⇒m<1+n (Named.cut-below N) ; dlv-below = mapᵃ m<n⇒m<1+n (Named.dlv-below N)
  ; dying-below = Named.dying-below N }

-- a row at a slot leaves every live source's guard alone: a live source
-- below the slots is guarded anyway, and one above them is not the slot
guard-slot : ∀ {m} {Δ : Ctx m} {u} (K : List (RegRow Δ u)) r (l : LiveSource Δ) → regSource (proj₁ (proj₂ r)) < m
           → (LiveSource.source l <ᵇ m) ∨ any (λ p → sameSource (LiveSource.source l) (regSource (proj₁ (proj₂ p)))) (K ++ r ∷ [])
           ≡ (LiveSource.source l <ᵇ m) ∨ any (λ p → sameSource (LiveSource.source l) (regSource (proj₁ (proj₂ p)))) K
guard-slot {m} K r l lt with LiveSource.source l <ᵇ m in e
... | true  = refl
... | false = subst (λ b → b ∨ any (λ p → sameSource (LiveSource.source l) (regSource (proj₁ (proj₂ p)))) (K ++ r ∷ [])
                           ≡ b ∨ any (λ p → sameSource (LiveSource.source l) (regSource (proj₁ (proj₂ p)))) K) e
                  (guard-snoc K r l (sameSource-no (λ x → subst T (trans (cong (_<ᵇ m) (sym x)) e) (<⇒<ᵇ lt))))

-- a lowered floor reads the same tests
lower-spent : ∀ {m} {Δ : Ctx m} {s u lo lo′} (le : lo′ ≤ lo) (p : Path Δ lo s u) ns → spentOn (lowerFloor le p) ns ≡ spentOn p ns
lower-spent le root                      ns = refl
lower-spent le (share-sink _ _)          ns = refl
lower-spent le (map-f _ ↠[ _ ] _)        ns = refl
lower-spent le (scan-f _ _ ↠[ _ ] _)     ns = refl
lower-spent le (take-f _ _ ↠[ _ ] _)     ns = refl
lower-spent le (batchSync-f _ ↠[ _ ] _)  ns = refl
lower-spent le (from-inner _ _ _ ↠[ _ ] _) ns = refl
lower-spent le (thru-outer _ _ ↠[ _ ] _) ns = refl

-- and walks the outers it did
lower-thru : ∀ {m} {Δ : Ctx m} {s u lo lo′} (le : lo′ ≤ lo) (p : Path Δ lo s u) → thruNodes (lowerFloor le p) ≡ thruNodes p
lower-thru le root                      = refl
lower-thru le (share-sink _ _)          = refl
lower-thru le (map-f _ ↠[ _ ] _)        = refl
lower-thru le (scan-f _ _ ↠[ _ ] _)     = refl
lower-thru le (take-f _ _ ↠[ _ ] _)     = refl
lower-thru le (batchSync-f _ ↠[ _ ] _)  = refl
lower-thru le (from-inner _ _ _ ↠[ _ ] _) = refl
lower-thru le (thru-outer _ _ ↠[ _ ] _) = refl

module _ {n} {Γ : Ctx n} (κ : Kinds n) {t} where

  -- and relates as it did, since the relation reads no floor
  lower-rel : ∀ {π NP NI lo lo′ ℓ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)} (le : ℓ ≤ lo)
            → PathRel {Γ = Γ} κ π {t} NP NI p q → PathRel {Γ = Γ} κ π {t} NP NI (lowerFloor le p) q
  lower-rel le root~                         = root~
  lower-rel le (sink~ sh)                    = sink~ sh
  lower-rel le (map~ l r)                    = map~ l r
  lower-rel le (scan~ a b c d e r)           = scan~ a b c d e r
  lower-rel le (takeWhile~ a b c d e r)      = takeWhile~ a b c d e r
  lower-rel le (spentWhile~ a b c r)         = spentWhile~ a b c r
  lower-rel le (outerElem~ a r)              = outerElem~ a r
  lower-rel le (outerExplode~ a x r)         = outerExplode~ a x r
  lower-rel le (inner~ a b c r)              = inner~ a b c r
  lower-rel le (deferInner~ a b c d e f g r) = deferInner~ a b c d e f g r

module _ {n} {Γ : Ctx n} (κ : Kinds n) {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

  open Kept {Γ = Γ} κ {t} {ep} {ei}

  module Join {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
              (S : St sP stP sI stI) (i : Fin n) (hk : lookup κ i ≡ hotᵏ)
              (cP : memberSource (toℕ i) (EvalSt.completedSources stP) ≡ false)
              (conn : memberSource (toℕ (n ↑ʳ i)) (EvalSt.connectedShares stI) ≡ true)
              {p : Path Γ (suc (toℕ i)) (lookup Γ i) t} {u′} {p′ : Path (plainᵏ Γ κ) (suc (toℕ (n ↑ʳ i))) u′ (emitᵗ t)}
              (new-row : RowRel {Γ = Γ} κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI)
                           (freshId regᵏ (Sched.mint sP) , atSlot i , _ , p) (freshId regᵏ (Sched.mint sI) , atSlot (n ↑ʳ i) , u′ , p′))
              (arr : ∀ {s s′ w w′} → ArrRows {Γ = Γ} κ (Store.π S) _ _ _ _ (new-row ∷ []) s s′ w w′)
              (off : ∀ {j} → Unpaired {Γ = Γ} κ (Store.π S) j → j ∈ nodesOf p′ → ⊥)
              {lo lo′ s} {p₀ : Path Γ lo s t} {q₀ : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
              (pr₀ : PathRel {Γ = Γ} κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) p₀ q₀) where

    open Store S

    rid = freshId regᵏ (Sched.mint sP) ; rid′ = freshId regᵏ (Sched.mint sI)
    rowP : RegRow Γ t
    rowP = (rid , atSlot i , lookup Γ i , p)
    rowI : RegRow (plainᵏ Γ κ) (emitᵗ t)
    rowI = (rid′ , atSlot (n ↑ʳ i) , u′ , p′)
    KP = EvalSt.registry stP ; KI = EvalSt.registry stI
    sP₂ = record sP { mint = setAt regᵏ (suc rid) (Sched.mint sP) }
    sI₂ = record sI { mint = setAt regᵏ (suc rid′) (Sched.mint sI) }

    -- the raw slot is live: its latch is the plain slot's
    rawI : memberSource (toℕ (i ↑ˡ n)) (EvalSt.completedSources stI) ≡ false
    rawI = trans (sym (proj₁ (proj₁ (latches i) hk))) cP

    deadP : memberSource (toℕ i) (EvalSt.dying stP) ≡ false
    deadP with memberSource (toℕ i) (EvalSt.dying stP) in e
    ... | false = refl
    ... | true  = ⊥-elim (t≢f (trans (sym (proj₁ (dying-done i hk) e)) cP))

    deadI : memberSource (toℕ (n ↑ʳ i)) (EvalSt.dying stI) ≡ false
    deadI with memberSource (toℕ (n ↑ʳ i)) (EvalSt.dying stI) in e
    ... | false = refl
    ... | true  = ⊥-elim (t≢f (trans (sym (proj₂ (dying-done i hk) e)) rawI))

    -- each hot slot's census, with a reader of slot i behind its share
    cen : ∀ j → lookup κ j ≡ hotᵏ → Census (toℕ (j ↑ˡ n)) (toℕ (n ↑ʳ j)) (KI ++ rowI ∷ [])
                                           (memberSource (toℕ (n ↑ʳ j)) (EvalSt.connectedShares stI))
                                           (memberSource (toℕ (j ↑ˡ n)) (EvalSt.completedSources stI))
    cen j h with census j h
    ... | inj₁ (o , cn) = inj₁ (trans (count-snoc _ KI rowI (sameSource-no (raw≢stamped j i))) o , cn)
    ... | inj₂ (z , z′ , f) with toℕ j ≟ toℕ i
    ...   | no ne = inj₂ ( trans (count-snoc _ KI rowI (sameSource-no (raw≢stamped j i))) z
                         , trans (count-snoc _ KI rowI (sameSource-no (λ x → ne (cong toℕ (↑ʳ-injective n j i (toℕ-injective x)))))) z′
                         , f )
    ...   | yes e with toℕ-injective e
    ...     | refl = ⊥-elim (t≢f (trans (sym (f conn)) rawI))

    -- REGISTERED: both rows join their registries last, paired as `read~`,
    -- the impl's on a path its walk found live
    registered : LiveOn p′ (EvalSt.nodes stI) → Rule sP₂ (record stP { registry = KP ++ rowP ∷ [] }) → Rule sI₂ (record stI { registry = KI ++ rowI ∷ [] })
               → Σ (After S ([] , sP₂ , record stP { registry = KP ++ rowP ∷ [] }) ([] , sI₂ , record stI { registry = KI ++ rowI ∷ [] })) λ B
                   → PathRel {Γ = Γ} κ (Store.π (After.store B)) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) p₀ q₀
    registered join-live rP rI =
      after S₂ (λ { (inj₁ c) → inj₁ c ; (inj₂ (a , b , pp)) → inj₂ (a , b , part-snoc {Γ = Γ} κ rows new-row pp) })
               (λ ar → record { boundP = Arr.boundP ar ; boundI = Arr.boundI ar ; rows = arr-snoc {Γ = Γ} κ rows new-row (Arr.rows ar) arr
                              ; lists = Arr.lists ar })
               []ᵖ (λ m → m)
      , pr₀
      where
      S₂ : Store κ sP₂ (record stP { registry = KP ++ rowP ∷ [] }) sI₂ (record stI { registry = KI ++ rowI ∷ [] })
      S₂ = record
        { π = π ; π-keys = π-keys ; π-vals = π-vals ; pairs-below = pairs-below
        ; sources = sources ; numbers = numbers ; distinct = distinct ; sync = sync
        ; rows     = reg-snoc {Γ = Γ} κ rows new-row
        ; dlv-alike = spent-snoc {Γ = Γ} κ rows new-row dlv-alike
                        (trans (none-below (Named.dlv-below (proj₁ named))) (sym (none-below (Named.dlv-below (proj₂ named)))))
        ; dying-alike = spent-snoc {Γ = Γ} κ rows new-row dying-alike (trans deadP (sym deadI))
        ; latches  = latches ; dying-done = dying-done
        ; bounded  = bounded
        ; swept    = mapᵖ (λ {l} {l′} g → trans (guard-slot KP rowP l (toℕ<n i)) (trans g (sym (guard-slot KI rowI l′ (toℕ<n (n ↑ʳ i)))))) swept
        ; uncut    = ++⁺ᵃ (proj₁ uncut) (none-below (Named.cut-below (proj₁ named)) ∷ᵃ []ᵃ)
                   , ++⁺ᵃ (proj₂ uncut) (none-below (Named.cut-below (proj₂ named)) ∷ᵃ []ᵃ)
        ; named    = named-row (proj₁ named) (<-trans (toℕ<n i) (Named.slots-below (proj₁ named)))
                   , named-row (proj₂ named) (<-trans (stamped< i) (Named.slots-below (proj₂ named)))
        ; rids     = ++⁺ᴾ (proj₁ rids) ([]ᵃ ∷ᴾ []ᴾ) (mapᵃ (λ lt → <⇒≢ lt ∷ᵃ []ᵃ) (proj₁ fresh-ids))
                   , ++⁺ᴾ (proj₂ rids) ([]ᵃ ∷ᴾ []ᴾ) (mapᵃ (λ lt → <⇒≢ lt ∷ᵃ []ᵃ) (proj₂ fresh-ids))
        ; fresh-ids = ++⁺ᵃ (mapᵃ m<n⇒m<1+n (proj₁ fresh-ids)) (≤-refl ∷ᵃ []ᵃ)
                    , ++⁺ᵃ (mapᵃ m<n⇒m<1+n (proj₂ fresh-ids)) (≤-refl ∷ᵃ []ᵃ)
        ; above    = ++⁺ᵃ (proj₁ above) (refl ∷ᵃ []ᵃ) , ++⁺ᵃ (proj₂ above) (refl ∷ᵃ []ᵃ)
        ; census   = cen
        ; owned    = ++⁺ᵃ (tabulateᵃ (λ {r} r∈ ns {j} b → ++⁺ᵃ (lookupᵃ owned r∈ ns b)
                                        ((λ h → ⊥-elim (off (reg-unp {Γ = Γ} κ rows {r′ = r} r∈ ns b) (has-node {k = j} p′ (subst T (sym h) tt)))) ∷ᵃ []ᵃ)))
                          ((λ ns {_} _ → ⊥-elim (ns i refl)) ∷ᵃ []ᵃ)
        ; ruleP    = rP ; ruleI = rI ; scripts = scripts ; inv = inv-snoc rowI join-live inv
        }

    -- SPENT: the read's path already cut, so neither run registers it
    spent : Rule sP₂ (record stP { registry = KP }) → Rule sI₂ (record stI { registry = KI })
          → Σ (After S ([] , sP₂ , record stP { registry = KP }) ([] , sI₂ , record stI { registry = KI })) λ B
              → PathRel {Γ = Γ} κ (Store.π (After.store B)) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) p₀ q₀
    spent rP rI = after S₂ (λ x → x) (λ ar → record { boundP = Arr.boundP ar ; boundI = Arr.boundI ar ; rows = Arr.rows ar ; lists = Arr.lists ar })
                         []ᵖ (λ m → m)
                , pr₀
      where
      S₂ : Store κ sP₂ (record stP { registry = KP }) sI₂ (record stI { registry = KI })
      S₂ = record
        { π = π ; π-keys = π-keys ; π-vals = π-vals ; pairs-below = pairs-below
        ; sources = sources ; numbers = numbers ; distinct = distinct ; sync = sync
        ; rows = rows ; dlv-alike = dlv-alike ; dying-alike = dying-alike ; latches = latches ; dying-done = dying-done
        ; bounded = bounded ; swept = swept ; uncut = uncut
        ; named = named-reg (proj₁ named) , named-reg (proj₂ named)
        ; rids = rids ; fresh-ids = mapᵃ m<n⇒m<1+n (proj₁ fresh-ids) , mapᵃ m<n⇒m<1+n (proj₂ fresh-ids)
        ; above = above ; census = census ; owned = owned
        ; ruleP = rP ; ruleI = rI ; scripts = scripts ; inv = inv
        }

    -- the two registrations agree on whether they are spent
    join-at : (bP bI : Bool) → bP ≡ bI → (bI ≡ false → LiveOn p′ (EvalSt.nodes stI))
            → Rule sP₂ (record stP { registry = if bP then KP else KP ++ rowP ∷ [] })
            → Rule sI₂ (record stI { registry = if bI then KI else KI ++ rowI ∷ [] })
            → Σ (After S ([] , sP₂ , record stP { registry = if bP then KP else KP ++ rowP ∷ [] })
                         ([] , sI₂ , record stI { registry = if bI then KI else KI ++ rowI ∷ [] })) λ B
                → PathRel {Γ = Γ} κ (Store.π (After.store B)) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) p₀ q₀
    join-at true  true  refl _  = spent
    join-at false false refl lq = registered (lq refl)

  -- a path retyped along an equation is the same pair of type and path
  sub-pair : ∀ {lo u A B} (e : A ≡ B) (y : Path (plainᵏ Γ κ) lo B u)
           → _≡_ {A = Σ Ty λ v → Path (plainᵏ Γ κ) lo v u} (A , subst (λ v → Path (plainᵏ Γ κ) lo v u) (sym e) y) (B , y)
  sub-pair refl y = refl

  -- A HOT READ JOINING ITS CONNECTED SHARE: each run registers its row
  -- at the slot, the impl's down the restamp, and the stores stay related
  join-read : ∀ {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
                (S : St sP stP sI stI) (i : Fin n) (hk : lookup κ i ≡ hotᵏ)
              → memberSource (toℕ i) (EvalSt.completedSources stP) ≡ false
              → memberSource (toℕ (n ↑ʳ i)) (EvalSt.connectedShares stI) ≡ true
              → ∀ {lo} {p : Path Γ lo (lookup Γ i) t} {q : Path (plainᵏ Γ κ) (n + lo) (emitᵗ (lookup Γ i)) (emitᵗ t)}
                  (below : toℕ i < lo) (below′ : toℕ (n ↑ʳ i) < n + lo)
                  (eq : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (lookup Γ i)) {Θ₀ ρ₀} {X : Tm (plainᵏ Γ κ) [] [] (emitᵗ (lookup Γ i) ∷ Θ₀) uniqᵗ}
              → PathRel {Γ = Γ} κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) p q
              → Sound p sP stP → Sound q sI stI → LiveIf q (EvalSt.nodes stI)
              → let q′ = lowerFloor below′ (subst (λ v → Path (plainᵏ Γ κ) (n + lo) v (emitᵗ t)) (sym eq)
                                           (map-f (Θ₀ , restampᵛ X subscribeᵛ (varᵗ (here refl)) , ρ₀) ↠[ ≤-refl ] q))
                    rid = freshId regᵏ (Sched.mint sP) ; rid′ = freshId regᵏ (Sched.mint sI)
                in Σ (After S ([] , record sP { mint = setAt regᵏ (suc rid) (Sched.mint sP) } , register rid (atSlot i) (lowerFloor below p) stP)
                              ([] , record sI { mint = setAt regᵏ (suc rid′) (Sched.mint sI) } , register rid′ (atSlot (n ↑ʳ i)) q′ stI)) λ B
                     → PathRel {Γ = Γ} κ (Store.π (After.store B)) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) p q
  join-read {sP} {stP} {sI} {stI} S i hk cP conn {lo} {p} {q} below below′ eq {Θ₀} {ρ₀} {X} pr soP soI lv =
    J.join-at (spentOn (lowerFloor below p) (EvalSt.nodes stP)) (spentOn q′ (EvalSt.nodes stI)) same
              (λ s → live-thru q q′ {EvalSt.nodes stI} (sym thru′) (LiveIf.run lv (trans (sym spent′) s)))
              (Sound.ruled soP₂) (Sound.ruled soI₂)
    where
    y  = map-f (Θ₀ , restampᵛ X subscribeᵛ (varᵗ (here refl)) , ρ₀) ↠[ ≤-refl ] q
    y₀ = subst (λ v → Path (plainᵏ Γ κ) (n + lo) v (emitᵗ t)) (sym eq) y
    q′ = lowerFloor below′ y₀
    sp = sub-pair eq y

    -- the row threads, ends and is spent where the read's path is
    nodes′ : ∀ k → pathHasNode k q′ ≡ pathHasNode k q
    nodes′ k = trans (lower-nodes below′ y₀ k) (cong (λ c → pathHasNode k (proj₂ c)) sp)

    off : ∀ {j} → Unpaired {Γ = Γ} κ (Store.π S) j → j ∈ nodesOf q′ → ⊥
    off u m = u (rel-vals {Γ = Γ} κ pr (has-node q (subst T (nodes′ _) (node-has q′ m))))

    spent′ : spentOn q′ (EvalSt.nodes stI) ≡ spentOn q (EvalSt.nodes stI)
    spent′ = trans (lower-spent below′ y₀ (EvalSt.nodes stI)) (cong (λ c → spentOn (proj₂ c) (EvalSt.nodes stI)) sp)

    thru′ : thruNodes q′ ≡ thruNodes q
    thru′ = trans (lower-thru below′ y₀) (cong (λ c → thruNodes (proj₂ c)) sp)

    same : spentOn (lowerFloor below p) (EvalSt.nodes stP) ≡ spentOn q′ (EvalSt.nodes stI)
    same = trans (lower-spent below p (EvalSt.nodes stP)) (trans (path-spent {Γ = Γ} κ pr) (sym spent′))

    module J = Join S i hk cP conn {p = lowerFloor below p} {p′ = q′}
                 (read~ (inj₁ hk) (lower-rel κ below pr) (cong (λ c → proj₁ c , lowerFloor below′ (proj₂ c)) sp))
                 (λ {_} {_} {_} {_} → tt) off pr

    soP₂ = row-sound i below p sP stP
             (λ eq′ → ⊥-elim (scripted≢shared (trans (sym (proj₂ (proj₂ (plain-hot-slot ins i hk))))
                        (trans (sym (memoᶠ-at (plainSlots ins) i)) (trans (sym (cong (λ f → f i) eP)) eq′)))))
             soP
      where
      ins = proj₁ (Store.scripts S)
      eP  = proj₁ (proj₂ (Store.scripts S))
    soI₂ : Sound q (record sI { mint = setAt regᵏ (suc (freshId regᵏ (Sched.mint sI))) (Sched.mint sI) }) (register (freshId regᵏ (Sched.mint sI)) (atSlot (n ↑ʳ i)) q′ stI)
    soI₂ = register-sound {sched = sI} (freshId regᵏ (Sched.mint sI)) (atSlot (n ↑ʳ i)) q′ ≤-refl (keeps-refl _ _)
             (trans (lower-end below′ y₀) (cong (λ c → endOf (proj₂ c)) sp))
             (λ k h → inj₁ (subst T (nodes′ k) h))
             (λ so → lower-distinct below′ y₀ (subst (λ c → Distinct (proj₂ c)) (sym sp) ((λ _ ()) , Sound.distinct so)))
             (λ _ → conn) soI
