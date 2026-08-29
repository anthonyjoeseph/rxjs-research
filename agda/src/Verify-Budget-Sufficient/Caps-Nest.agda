------------------------------------------------------------------
-- THE NESTING MEASURE `nest`, and the frame row that supplies it.
--
-- The budget `k` the subscribe clique descends on counts nesting, and
-- Mu-Nest-Probe pinned which nesting: `syncSizeᵉ`, the measure that
-- stops at `deferᵉ` — the sole gate moving Δᵍ into Δ — and therefore
-- drops by exactly one across the μ edge, matching k's single descent
-- at `sLvlD S W d (suc k) J ↦ opIterD S W d k …`.
--
-- The term's own syncSize is NOT enough, and the reason is the share
-- edge.  `sharedConnect` subscribes the slot's STORED def, which is
-- structurally unrelated to the `input i` the caller was looking at —
-- a term-only hypothesis has one unit to offer a callee that needs the
-- def's whole nesting (Mu-Nest-Probe's `plain-share-absurd`).  So the
-- measure carries a RESIDUE: the nesting still owed by every share that
-- has not been connected yet.
--
--     nest e sl cs = syncSizeᵉ e + resid sl cs
--
-- `resid` is .Measures' `unconn` reweighted — the same
-- `memberSource … connectedShares` mask the evaluator already keeps,
-- summed by the same `sum-tab-mono`, with an unconnected shared slot
-- contributing its def's syncSize instead of 1.  That is what makes it
-- sound: a share connects at most once ever (`sharedConnect` writes
-- `toℕ i` into `connectedShares` BEFORE walking the def, and
-- `subscribeSharedSlot` short-circuits on an already-connected one), so
-- the residue only ever falls, and the edge that spends it pays for
-- itself.
--
-- Note the residue does NOT reset per instant — `connectedShares` is
-- initialised `[]` once and is append-only — and does not need to:
-- `resid≤slots` holds for EVERY cs, so the frame row below is uniform
-- in whatever the connected set happens to be at frame entry.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Caps-Nest where

open import Data.Bool using (T; true; false; if_then_else_; _∨_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Nat  using (ℕ; suc; _+_; _*_; _≤_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; +-mono-≤; +-monoʳ-≤; *-mono-≤;
         *-identityˡ; *-identityʳ; +-identityʳ; +-assoc; *-distribˡ-+;
         +-comm; m≤m+n; m≤n+m; +-monoˡ-≤; *-monoʳ-≤; n≤1+n; ≡⇒≡ᵇ)
open import Data.Fin  using (Fin; toℕ)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_; tabulate)
open import Data.Maybe using (Maybe)
open import Data.Product using (_×_; _,_)
open import Data.Nat.ListAction  using (sum)
open import Data.Vec  using (lookup)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Prim  using (Source)
open import Rx.Exp
  using (Ctx; Exp; Tm; Fn; Closed; obs; input; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; syncSizeᵉ; syncSizeᵗ; sizeᵉ; unfoldμ; inputsBelowᵉ)
open import Rx.Slots using (Slots; scripted; shared; slotSize; slotsSize)
open import Rx.Evaluator using (sizeAt; memberSource; sameSource)
open import Verify-Budget-Sufficient.Caps
  using (Caps; iterSize-suc)
open import Verify-Budget-Sufficient.Caps-Chain using (2≤sizeAt)
open import Verify-Budget-Sufficient.Measures using
  (sum-tab-mono; syncSize-unfoldμ;
                                                      syncSize≤sizeᵉ)
open import Decide using (T⇒≡true; f≡t-absurd)

------------------------------------------------------------------
-- § 1.  THE RESIDUE — `unconn`, reweighted.
------------------------------------------------------------------

residAt : ∀ {n} {Γ : Ctx n} → Slots Γ → List Source → Fin n → ℕ
residAt sl cs i with sl i
... | shared d   = if memberSource (toℕ i) cs then 0 else syncSizeᵉ d
... | scripted _ = 0

resid : ∀ {n} {Γ : Ctx n} → Slots Γ → List Source → ℕ
resid sl cs = sum (tabulate (residAt sl cs))

-- the residue is syntactically owned, uniformly in cs: every entry is
-- either masked out or a def's syncSize, and syncSize sits under size
residAt≤slot : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) (i : Fin n) →
  residAt sl cs i ≤ slotSize (sl i)
residAt≤slot sl cs i with sl i
... | scripted s = z≤n
... | shared d with memberSource (toℕ i) cs
...   | true  = z≤n
...   | false = syncSize≤sizeᵉ d

resid≤slots : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) →
  resid sl cs ≤ slotsSize sl
resid≤slots sl cs = sum-tab-mono _ _ (residAt≤slot sl cs)

-- connecting anything never raises the residue …
residAt-cons-≤ : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
  (s : Source) (i : Fin n) → residAt sl (s ∷ cs) i ≤ residAt sl cs i
residAt-cons-≤ sl cs s i with sl i
... | scripted _ = z≤n
... | shared d with memberSource (toℕ i) cs
...   | true  rewrite ∨-zeroʳ (sameSource (toℕ i) s) = z≤n
...   | false with sameSource (toℕ i) s ∨ false
...     | true  = z≤n
...     | false = ≤-refl

resid-cons-≤ : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) (s : Source) →
  resid sl (s ∷ cs) ≤ resid sl cs
resid-cons-≤ sl cs s = sum-tab-mono _ _ (residAt-cons-≤ sl cs s)

-- ANTITONE IN THE CONNECTED SET, which is the general form the walks
-- need: an evaluator step may connect any number of shares, not one, and
-- what `KeepsC` hands back about a step is exactly this hypothesis —
-- every source connected before is connected after.  Same proof as
-- .Measures' `unconn-antitone`, with the weight on it
residAt-antitone : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs cs′ : List Source)
  (i : Fin n) →
  (memberSource (toℕ i) cs ≡ true → memberSource (toℕ i) cs′ ≡ true) →
  residAt sl cs′ i ≤ residAt sl cs i
residAt-antitone sl cs cs′ i h with sl i
... | scripted _ = z≤n
... | shared d with memberSource (toℕ i) cs′ | memberSource (toℕ i) cs | h
...   | true  | _     | _  = z≤n
...   | false | false | _  = ≤-refl
...   | false | true  | h′ = f≡t-absurd (h′ refl)

resid-antitone : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs cs′ : List Source) →
  (∀ s → memberSource s cs ≡ true → memberSource s cs′ ≡ true) →
  resid sl cs′ ≤ resid sl cs
resid-antitone sl cs cs′ mono =
  sum-tab-mono (residAt sl cs′) (residAt sl cs)
    (λ i → residAt-antitone sl cs cs′ i (mono (toℕ i)))


------------------------------------------------------------------
-- § 2.  nest, and the ONE inequality the frame refresh spends.
------------------------------------------------------------------

nest : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → Slots Γ → List Source → ℕ
nest e sl cs = syncSizeᵉ e + resid sl cs

nest≤ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t)
  (sl : Slots Γ) (cs : List Source) → nest e sl cs ≤ sizeᵉ e + slotsSize sl
nest≤ e sl cs = +-mono-≤ (syncSize≤sizeᵉ e) (resid≤slots sl cs)

-- THE DRAIN'S TWO HEADROOM CONJUNCTS ARE ONE CURRENCY, and the row
-- above is why.  A parked inner is charged twice at the drain door --
-- once as a nesting the connect walk has to fit under the cap, once as
-- a size the level ceiling has to clear -- and the two read as separate
-- obligations only because one of them is stated in `nest`.  It is
-- not: nesting is a SIZE plus the slots the state has not connected
-- yet, both bounded above by the pair the caller already carries.  So a
-- single premise -- the parked term's size, the slots, and three, all
-- under the cap at the walk's own level -- supplies both, and whatever
-- states the store bound has ONE inequality to establish rather than a
-- measure it has no access to.
drain-head-supply : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (c : Caps) (Lv : ℕ)
  (o : Exp Γ Δᵍ Δ Θ t) (sl : Slots Γ) (cs : List Source) →
  Lv + (3 + (sizeᵉ o + slotsSize sl)) ≤ Caps.cSize c →
  (3 + nest o sl cs ≤ Caps.cSize c)
  × (Lv + suc (suc (sizeᵉ o)) ≤ Caps.cSize c)
drain-head-supply c Lv o sl cs h =
  ≤-trans (s≤s (s≤s (s≤s (nest≤ o sl cs))))
          (≤-trans (m≤n+m (3 + (sizeᵉ o + slotsSize sl)) Lv) h)
  , ≤-trans (+-monoʳ-≤ Lv
              (s≤s (s≤s (≤-trans (m≤m+n (sizeᵉ o) (slotsSize sl))
                                 (n≤1+n (sizeᵉ o + slotsSize sl))))))
            h

-- THE SHARE EDGE'S STEP, which is the row the residue exists for.
-- `sharedConnect` recurses on the slot's stored def with `toℕ i`
-- ALREADY consed onto `connectedShares`, so the callee's measure is
-- `syncSizeᵉ d + resid sl (toℕ i ∷ cs)` while the caller holds
-- `nest (input i) sl cs ≤ suc k` — and `input i` has syncSize 1, so that
-- premise IS `resid sl cs ≤ k`.  The two differ by exactly slot i's own
-- weight, which leaves the residue precisely when the slot is connected

swap₃ : ∀ (a b c : ℕ) → a + (b + c) ≡ b + (a + c)
swap₃ a b c =
  trans (sym (+-assoc a b c))
        (trans (cong (_+ c) (+-comm a b)) (+-assoc b a c))

sum-tab-slack : ∀ {m} (f g : Fin m → ℕ) (w : ℕ) → (∀ j → f j ≤ g j) →
  (i : Fin m) → w + f i ≤ g i → w + sum (tabulate f) ≤ sum (tabulate g)
sum-tab-slack {suc m} f g w h Fin.zero hi =
  ≤-trans (≤-reflexive
            (sym (+-assoc w (f Fin.zero) (sum (tabulate (λ j → f (Fin.suc j)))))))
          (+-mono-≤ hi (sum-tab-mono _ _ (λ j → h (Fin.suc j))))
sum-tab-slack {suc m} f g w h (Fin.suc i) hi =
  ≤-trans (≤-reflexive
            (swap₃ w (f Fin.zero) (sum (tabulate (λ j → f (Fin.suc j))))))
          (+-mono-≤ (h Fin.zero)
                    (sum-tab-slack (λ j → f (Fin.suc j)) (λ j → g (Fin.suc j)) w
                                   (λ j → h (Fin.suc j)) i hi))

resid-connect : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) (i : Fin n)
  {d : Closed Γ (lookup Γ i)} {ok : T (inputsBelowᵉ (toℕ i) d)} →
  sl i ≡ shared d {ok = ok} →
  memberSource (toℕ i) cs ≡ false →
  syncSizeᵉ d + resid sl (toℕ i ∷ cs) ≤ resid sl cs
resid-connect sl cs i {d} eqi fresh =
  sum-tab-slack _ _ (syncSizeᵉ d) (residAt-cons-≤ sl cs (toℕ i)) i slack
  where
  slack : syncSizeᵉ d + residAt sl (toℕ i ∷ cs) i ≤ residAt sl cs i
  slack rewrite eqi | fresh
              | T⇒≡true (toℕ i ≡ᵇ toℕ i) (≡⇒≡ᵇ (toℕ i) (toℕ i) refl)
              = ≤-reflexive (+-identityʳ (syncSizeᵉ d))

share-step : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) (i : Fin n)
  {d : Closed Γ (lookup Γ i)} {ok : T (inputsBelowᵉ (toℕ i) d)} (k : ℕ) →
  sl i ≡ shared d {ok = ok} →
  memberSource (toℕ i) cs ≡ false →
  nest (input {Γ = Γ} {Δᵍ = []} {Δ = []} {Θ = []} i) sl cs ≤ suc k →
  nest d sl (toℕ i ∷ cs) ≤ k
share-step sl cs i k eqi fresh (s≤s h) =
  ≤-trans (resid-connect sl cs i eqi fresh) h


------------------------------------------------------------------
-- § 4.  THE REMAINING EDGES.  `subscribeE` walks an operator chain and
-- re-enters itself at a μ; every chain edge descends to a strict subterm
-- at the SAME k, and the μ edge SPENDS a unit of it.  Together with § 2's
-- share step and § 3's frame row, that is every way the clique reaches a
-- deeper subscribe, so the hypothesis is maintainable at every call site.
--
-- THE μ EDGE IS NOT THE ONLY SPENDER, which is what this block used to
-- claim.  It is the only one among the edges enumerated HERE — a walk
-- reaches a payload through a FRAME, and the frame refreshes, so the
-- payload edge spends a unit of the REFRESHED budget instead.  § 3's
-- strict row is what pays for it: `frameBud c j` is
-- `suc (sizeAt S (suc j))` by construction, and the payload's nest is
-- bounded by its predecessor.
--
-- (`1 ≤ k` on its own is NOT maintainable — nothing hands a bare side
-- condition to the μ call.  Mu-Nest-Probe refutes it.  This is why the
-- hypothesis is a measure and not a bound.)
------------------------------------------------------------------

mu-step : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t)
  (sl : Slots Γ) (cs : List Source) (k : ℕ) →
  nest (μᵉ body) sl cs ≤ suc k → nest (unfoldμ body) sl cs ≤ k
mu-step body sl cs k (s≤s h) =
  subst (λ x → x + resid sl cs ≤ k) (sym (syncSize-unfoldμ body)) h


-- ONE CHAIN EDGE.  Every operator's head is a strict subterm whose
-- syncSize the constructor's own `suc` dominates, so one lemma with the
-- head's syncSize abstracted covers map / take / scan and all four *All
chain-step : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
  (h b k : ℕ) → suc (h + b) + resid sl cs ≤ k → b + resid sl cs ≤ k
chain-step sl cs h b k =
  ≤-trans (+-monoˡ-≤ (resid sl cs)
            (≤-trans (m≤n+m b h) (n≤1+n (h + b))))

map-step : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (f : Fn Γ Δᵍ Δ Θ s t)
  (b : Exp Γ Δᵍ Δ Θ s) (sl : Slots Γ) (cs : List Source) (k : ℕ) →
  nest (mapᵉ f b) sl cs ≤ k → nest b sl cs ≤ k
map-step f b sl cs k = chain-step sl cs (syncSizeᵗ f) (syncSizeᵉ b) k

take-step : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (c : Tm Γ Δᵍ Δ Θ _)
  (b : Exp Γ Δᵍ Δ Θ t) (sl : Slots Γ) (cs : List Source) (k : ℕ) →
  nest (takeᵉ c b) sl cs ≤ k → nest b sl cs ≤ k
take-step c b sl cs k = chain-step sl cs (syncSizeᵗ c) (syncSizeᵉ b) k

scan-step : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (f : Fn Γ Δᵍ Δ Θ _ t)
  (z : Tm Γ Δᵍ Δ Θ t) (b : Exp Γ Δᵍ Δ Θ s) (sl : Slots Γ) (cs : List Source)
  (k : ℕ) → nest (scanᵉ f z b) sl cs ≤ k → nest b sl cs ≤ k
scan-step f z b sl cs k =
  chain-step sl cs (syncSizeᵗ f + syncSizeᵗ z) (syncSizeᵉ b) k

-- the four *All heads carry no term, so their `h` is 0
all-step : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) (b k : ℕ) →
  suc b + resid sl cs ≤ k → b + resid sl cs ≤ k
all-step sl cs b k =
  ≤-trans (+-monoˡ-≤ (resid sl cs) (n≤1+n b))

mergeAll-step : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (lim : Maybe ℕ) (b : Exp Γ Δᵍ Δ Θ (obs t))
  (sl : Slots Γ) (cs : List Source) (k : ℕ) →
  nest (mergeAllᵉ lim b) sl cs ≤ k → nest b sl cs ≤ k
mergeAll-step lim b sl cs k = all-step sl cs (syncSizeᵉ b) k

switch-step : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (b : Exp Γ Δᵍ Δ Θ (obs t))
  (sl : Slots Γ) (cs : List Source) (k : ℕ) →
  nest (switchAllᵉ b) sl cs ≤ k → nest b sl cs ≤ k
switch-step b sl cs k = all-step sl cs (syncSizeᵉ b) k

exhaust-step : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (b : Exp Γ Δᵍ Δ Θ (obs t))
  (sl : Slots Γ) (cs : List Source) (k : ℕ) →
  nest (exhaustAllᵉ b) sl cs ≤ k → nest b sl cs ≤ k
exhaust-step b sl cs k = all-step sl cs (syncSizeᵉ b) k

-- AND THE STATE EDGE.  `sharedConnect` is the only writer of
-- `connectedShares`, and it only ever conses, so every OTHER call that
-- carries the hypothesis across a state step reads a residue that has
-- not risen
nest-cons : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t)
  (sl : Slots Γ) (cs : List Source) (s : Source) (k : ℕ) →
  nest e sl cs ≤ k → nest e sl (s ∷ cs) ≤ k
nest-cons e sl cs s k = ≤-trans (+-monoʳ-≤ (syncSizeᵉ e) (resid-cons-≤ sl cs s))

-- and the same across a whole evaluator step, which is what a walk
-- crosses between two payloads
nest-keeps : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t)
  (sl : Slots Γ) (cs cs′ : List Source) (k : ℕ) →
  (∀ s → memberSource s cs ≡ true → memberSource s cs′ ≡ true) →
  nest e sl cs ≤ k → nest e sl cs′ ≤ k
nest-keeps e sl cs cs′ k mono =
  ≤-trans (+-monoʳ-≤ (syncSizeᵉ e) (resid-antitone sl cs cs′ mono))

------------------------------------------------------------------
-- § 3.  THE FRAME ROW.  A frame holds `sizeᵉ o ≤ sizeAt S j` for its
-- payload and `slotsSize sl ≤ S` for the telescope, so nest is bounded by
-- `sizeAt S j + S` — one summand MORE than the entry level.  The entry
-- level cannot pay for it: `sizeAt S j + S ≤ suc (sizeAt S j)` wants
-- `S ≤ 1`, against the clique's own `2 ≤ S` (Share-Residue-Probe § 1
-- refutes it at S = 2, j = 0).  ONE MORE SIZE LEVEL pays for it with
-- room to spare, because `sizeAt S (suc j)` unfolds to
-- `S * suc (2 * sizeAt S j)` — the `+ S` is already there and the rest
-- needs only `1 ≤ 2 * S`.  Levels are the cheap currency, and reading k
-- one level up is a RAISE, so every consumer already landed moves with
-- it under `sizeAt-mono` and nothing is re-derived.
------------------------------------------------------------------

sizeAt-suc : ∀ (S J : ℕ) → sizeAt S (suc J) ≡ S * suc (2 * sizeAt S J)
sizeAt-suc S J = iterSize-suc S J S

-- the arithmetic core, with no measure in it
core : ∀ (S x : ℕ) → 1 ≤ S → x + S ≤ S * suc (2 * x)
core S x 1≤S =
  ≤-trans (≤-trans (≤-reflexive (+-comm x S)) (+-monoʳ-≤ S x≤S2x))
          (≤-reflexive step)
  where
  x≤2x : x ≤ 2 * x
  x≤2x = ≤-trans (m≤m+n x x) (≤-reflexive (sym (cong (x +_) (+-identityʳ x))))

  x≤S2x : x ≤ S * (2 * x)
  x≤S2x = ≤-trans (≤-reflexive (sym (*-identityˡ x))) (*-mono-≤ 1≤S x≤2x)

  step : S + S * (2 * x) ≡ S * suc (2 * x)
  step = trans (cong (_+ S * (2 * x)) (sym (*-identityʳ S)))
               (sym (*-distribˡ-+ S 1 (2 * x)))

-- THE CHAIN REACHES THE PREDECESSOR ON THE NOSE, and that is the whole
-- content of the payload edge's budget split: `core` lands exactly on
-- `sizeAt S (suc j)`, and only the weak row below gives the last step
-- away.  The refreshed budget a frame reads is `suc (sizeAt S (suc j))` —
-- a SUCCESSOR by construction — so the payload it hands a subscribe is
-- bounded by that budget's PREDECESSOR, and the subscribe can spend the
-- unit a fresh entry costs
one-level-supply-strict : ∀ (S j x y : ℕ) →
  1 ≤ S → x ≤ sizeAt S j → y ≤ S → x + y ≤ sizeAt S (suc j)
one-level-supply-strict S j x y 1≤S hx hy =
  ≤-trans (≤-trans (+-mono-≤ hx hy) (core S (sizeAt S j) 1≤S))
          (≤-reflexive (sym (sizeAt-suc S j)))

-- AND THE ROW WITH THE PARKED TERM'S HEADROOM IN IT.  A drain's
-- ceiling wants three units above the pair a queued inner is charged
-- for, and the level below has room for them without being asked: the
-- refreshed budget is a MULTIPLE of the one it refreshes, so the slack
-- is a factor rather than a constant and three is bought by the size
-- cap being at least two.  That is what lets a store predicate carry
-- the drain's demand at the level it parks at.
core3 : ∀ (S X : ℕ) → 2 ≤ S → 2 ≤ X → 3 + (X + S) ≤ S * suc (2 * X)
core3 S X 2≤S 2≤X =
  ≤-trans (≤-reflexive (sym (+-assoc 3 X S)))
          (≤-trans (+-monoˡ-≤ S 3+X≤2SX)
                   (≤-trans (≤-reflexive (+-comm (S * (2 * X)) S))
                            (≤-reflexive step)))
  where
  3≤2X : 3 ≤ 2 * X
  3≤2X = ≤-trans (s≤s (s≤s (s≤s z≤n))) (*-monoʳ-≤ 2 2≤X)

  X≤2X : X ≤ 2 * X
  X≤2X = m≤m+n X (X + 0)

  3+X≤twice : 3 + X ≤ 2 * X + 2 * X
  3+X≤twice = +-mono-≤ 3≤2X X≤2X

  twice≤2SX : 2 * X + 2 * X ≤ S * (2 * X)
  twice≤2SX =
    ≤-trans (≤-reflexive (cong (2 * X +_) (sym (+-identityʳ (2 * X)))))
            (*-mono-≤ 2≤S (≤-refl {2 * X}))

  3+X≤2SX : 3 + X ≤ S * (2 * X)
  3+X≤2SX = ≤-trans 3+X≤twice twice≤2SX

  step : S + S * (2 * X) ≡ S * suc (2 * X)
  step = trans (cong (_+ S * (2 * X)) (sym (*-identityʳ S)))
               (sym (*-distribˡ-+ S 1 (2 * X)))

three-level-supply : ∀ (S j x y : ℕ) →
  2 ≤ S → x ≤ sizeAt S j → y ≤ S → 3 + (x + y) ≤ sizeAt S (suc j)
three-level-supply S j x y 2≤S hx hy =
  ≤-trans (s≤s (s≤s (s≤s (+-mono-≤ hx hy))))
          (≤-trans (core3 S (sizeAt S j) 2≤S
                     (2≤sizeAt S j 2≤S))
                   (≤-reflexive (sym (sizeAt-suc S j))))

one-level-supply : ∀ (S j x y : ℕ) →
  1 ≤ S → x ≤ sizeAt S j → y ≤ S → x + y ≤ suc (sizeAt S (suc j))
one-level-supply S j x y 1≤S hx hy =
  ≤-trans (one-level-supply-strict S j x y 1≤S hx hy) (n≤1+n (sizeAt S (suc j)))

-- the row in the shape the frame clause states it
refresh-supplies-nest : ∀ {n} {Γ : Ctx n} (S j : ℕ) {Δᵍ Δ Θ t}
  (o : Exp Γ Δᵍ Δ Θ t) (sl : Slots Γ) (cs : List Source) →
  1 ≤ S → sizeᵉ o ≤ sizeAt S j → slotsSize sl ≤ S →
  nest o sl cs ≤ suc (sizeAt S (suc j))
refresh-supplies-nest S j o sl cs 1≤S hsz hsl =
  one-level-supply S j (syncSizeᵉ o) (resid sl cs) 1≤S
    (≤-trans (syncSize≤sizeᵉ o) hsz)
    (≤-trans (resid≤slots sl cs) hsl)

-- and the strict row in the same shape: what a payload's subscribe is
-- handed once the frame's refresh has paid for the nesting level
refresh-supplies-nest-strict : ∀ {n} {Γ : Ctx n} (S j : ℕ) {Δᵍ Δ Θ t}
  (o : Exp Γ Δᵍ Δ Θ t) (sl : Slots Γ) (cs : List Source) →
  1 ≤ S → sizeᵉ o ≤ sizeAt S j → slotsSize sl ≤ S →
  nest o sl cs ≤ sizeAt S (suc j)
refresh-supplies-nest-strict S j o sl cs 1≤S hsz hsl =
  one-level-supply-strict S j (syncSizeᵉ o) (resid sl cs) 1≤S
    (≤-trans (syncSize≤sizeᵉ o) hsz)
    (≤-trans (resid≤slots sl cs) hsl)
