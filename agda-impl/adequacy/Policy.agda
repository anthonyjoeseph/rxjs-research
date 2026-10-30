{-# OPTIONS --guardedness #-}

-- A JOINER'S POLICY: what `Joining` takes, the four joiners part way
-- through as policies, and a joiner reading its policy causally.  Two
-- policies reading their outers, begun lanes, lanes, ends, runs, cuts and
-- hand-offs alike at and below `Q` give joiners agreeing there: every row
-- a joiner shows reads its policy no later than the row, a lane only past
-- its value and a pin no later than its connect.
--
-- Each joiner part way through reads its policy off its outer, its begun
-- lanes and the lanes it would begin, each at and below the row, so
-- agreeing inputs give agreeing joiners.  A bounded merge's schedule is
-- read lane by lane below the bound, as the denotation's is
-- (`denotation.Laws.Join`).
module adequacy.Policy where

open import Data.Bool using (Bool; T)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; ix)
open import denotation.EmissionSet using (EmissionSet; out; end; Ended; module Joining; _≺_; _≼_)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; AgreeTo-sym; ≺-trans; ≺→≼; ≼-refl; ≼-≺-≺; ≼-or-≻; ≺-ext)
open import denotation.Laws.Join using (module Join)
open import adequacy.Rows using (Lane; reads; From; sub; Lanes; Kth; AllEnd; EndsOf; module Flat; module SwitchF; module ExhaustF; module BoundedF)

------------------------------------------------------------------------
-- A joiner's policy

-- What `Joining` takes.
record Policy (A B : Set) : Set₁ where
  field
    lanes : Pos → A → EmissionSet B
    outer : EmissionSet A
    begun : EmissionSet B
    over  : Pos → Set
    runs  : Pos → Set
    cut   : Pos → Pos → Set
    hand  : Pos → Set

JoinP : ∀ {A B} → Policy A B → EmissionSet B
JoinP P = Joining.JoinT (lanes P) (outer P) (begun P) (over P) (runs P) (cut P) (hand P)
  where open Policy

DoneP : ∀ {A B} → Policy A B → Pos → Set
DoneP P = Joining.Done (lanes P) (outer P) (begun P) (over P) (runs P) (cut P) (hand P)
  where open Policy

------------------------------------------------------------------------
-- The four policies

flatP : ∀ {A B : Set} (L : A → Pos → EmissionSet B) (O : EmissionSet A) (d : Bool) (n : ℕ) (Ls : List (EmissionSet B)) → Policy A B
flatP L O d n Ls = record { lanes = Lane L ; outer = O ; begun = Lanes Ls ; over = Flat.Over L O d n Ls ; runs = λ _ → ⊤ ; cut = λ _ _ → ⊥ ; hand = λ _ → ⊥ }

switchP : ∀ {A B : Set} (L : A → Pos → EmissionSet B) (O : EmissionSet A) (d : Bool) (n : ℕ) (Ls : List (EmissionSet B)) → Policy A B
switchP L O d n Ls = record { lanes = Lane L ; outer = O ; begun = SwitchF.Bg L O d n Ls ; over = SwitchF.Over L O d n Ls ; runs = λ _ → ⊤ ; cut = SwitchF.Cut L O d n Ls ; hand = λ _ → ⊥ }

exhaustP : ∀ {A B : Set} (L : A → Pos → EmissionSet B) (O : EmissionSet A) (d : Bool) (n : ℕ) (Ls : List (EmissionSet B)) → Policy A B
exhaustP L O d n Ls = record { lanes = Lane L ; outer = O ; begun = Lanes Ls ; over = ExhaustF.Over L O d n Ls ; runs = ExhaustF.Run L O d n Ls ; cut = λ _ _ → ⊥ ; hand = λ _ → ⊥ }

boundedP : ∀ {A B : Set} (m : ℕ) (L : A → Pos → EmissionSet B) (O : EmissionSet A) (d : Bool) (n : ℕ) (Qu : List A) (Ls : List (EmissionSet B)) → Policy A B
boundedP m L O d n Qu Ls = record { lanes = BoundedF.LaneB m L O d n Qu Ls ; outer = O ; begun = BoundedF.Bg m L O d n Qu Ls ; over = BoundedF.Over m L O d n Qu Ls
                                  ; runs = BoundedF.Indexed m L O d n Qu Ls ; cut = λ _ _ → ⊥ ; hand = BoundedF.Queued m L O d n Qu Ls }

-- Each joiner's policy, none waiting.
polOf : ∀ {A B : Set} → FlatOp → (A → Pos → EmissionSet B) → EmissionSet A → Bool → ℕ → List (EmissionSet B) → Policy A B
polOf (mergeᶠ nothing)  L O d n = flatP L O d n
polOf (mergeᶠ (just m)) L O d n = boundedP m L O d n []
polOf switchᶠ           L O d n = switchP L O d n
polOf exhaustᶠ          L O d n = exhaustP L O d n

------------------------------------------------------------------------
-- Read alike at and below a bound

module _ {A B : Set} (Q : Pos) where
  open Join {A} {B} Q using (below; trans≼; beyond; fwd; conn≼; least-to; next-to; module BoundedJ)
  open BoundedJ 0 using (Stem; stem-≼; stem-at; LAg; none; _&_; lag-sym; nth-to)

  -- One policy read as another at and below `Q`: each of its parts, where
  -- the joiner reads it.
  record ReadsTo (P P′ : Policy A B) : Set where
    open Policy
    field
      out→  : ∀ {y e} → y ≼ Q → outer P y e → outer P′ y e
      bg→   : ∀ {y e} → y ≼ Q → begun P y e → begun P′ y e
      lane→ : ∀ {q a k e} → k ≼ Q → outer P q (out a) → runs P q → lanes P q a k e → lanes P′ q a k e
      past  : ∀ {q a k e} → lanes P q a k e → q ≺ k
      ov→   : ∀ {c} → c ≼ Q → over P c → over P′ c
      ru→   : ∀ {q a} → q ≼ Q → outer P q (out a) → runs P q → runs P′ q
      cu→   : ∀ {q k} → k ≼ Q → cut P q k → cut P′ q k
      ha→   : ∀ {c} → c ≼ Q → hand P c → hand P′ c

  module _ {P P′ : Policy A B} (R : ReadsTo P P′) (R⁻ : ReadsTo P′ P) where
    open ReadsTo

    done-to : ∀ {c} → c ≼ Q → DoneP P c → DoneP P′ c
    done-to {c} cQ (v , h) = ov→ R cQ v , λ {q} r′ u′ lt nc′ →
      let qQ = below q c lt cQ
          r  = out→ R⁻ qQ r′
          u  = ru→ R⁻ qQ r′ u′
          (c₀ , x , le) = h r u lt (λ y → nc′ (cu→ R cQ y))
      in c₀ , lane→ R (trans≼ c₀ c le cQ) r u x , le

  join-to : ∀ {P P′ : Policy A B} (R : ReadsTo P P′) (R⁻ : ReadsTo P′ P) → ∀ {y e} → y ≼ Q → JoinP P y e → JoinP P′ y e
  join-to R R⁻ yQ (Joining.val {q} r)  = Joining.val (out→ R (below q (q ++ [ ix 0 ]) (≺-ext q []) yQ) r)
    where open ReadsTo
  join-to R R⁻ yQ (Joining.step r)     = Joining.step (ReadsTo.out→ R yQ r)
  join-to R R⁻ yQ (Joining.opin r)     = Joining.opin (ReadsTo.out→ R yQ r)
  join-to R R⁻ yQ (Joining.oend r d)   = Joining.oend (ReadsTo.out→ R yQ r) (done-to R R⁻ yQ d)
  join-to R R⁻ yQ (Joining.opass r nd) = Joining.opass (ReadsTo.out→ R yQ r) (λ d → nd (done-to R⁻ R yQ d))
  join-to R R⁻ {y} yQ (Joining.lane {q} r u l nc w) =
    Joining.lane (out→ R qQ r) (ru→ R qQ r u) (lane→ R yQ r u l) (λ c → nc (cu→ R⁻ yQ c)) w
    where
      open ReadsTo
      qQ = below q y (past R l) yQ
  join-to R R⁻ {y} yQ (Joining.lend {q} r u l nc nh d) =
    Joining.lend (out→ R qQ r) (ru→ R qQ r u) (lane→ R yQ r u l) (λ c → nc (cu→ R⁻ yQ c)) (λ h → nh (ha→ R⁻ yQ h)) (done-to R R⁻ yQ d)
    where
      open ReadsTo
      qQ = below q y (past R l) yQ
  join-to R R⁻ {y} yQ (Joining.lpass {q} r u l nc nh nd) =
    Joining.lpass (out→ R qQ r) (ru→ R qQ r u) (lane→ R yQ r u l) (λ c → nc (cu→ R⁻ yQ c)) (λ h → nh (ha→ R⁻ yQ h)) (λ d → nd (done-to R⁻ R yQ d))
    where
      open ReadsTo
      qQ = below q y (past R l) yQ
  join-to R R⁻ yQ (Joining.hand {q} {c = c} r u l nc h) =
    Joining.hand (out→ R qQ r) (ru→ R qQ r u) (lane→ R cQ r u l) (λ ct → nc (cu→ R⁻ cQ ct)) (ha→ R cQ h)
    where
      open ReadsTo
      cQ = below c (c ++ [ ix 0 ]) (≺-ext c []) yQ
      qQ = below q c (past R l) cQ
  join-to R R⁻ {y} yQ (Joining.left {q} {r = r₀} r u l nc i) =
    Joining.left (out→ R qQ r) (ru→ R qQ r u) (lane→ R yQ r u l) (λ c → nc (cu→ R⁻ (conn≼ r₀ y i yQ) c)) i
    where
      open ReadsTo
      qQ = below q y (past R l) yQ
  join-to R R⁻ yQ (Joining.run x w)      = Joining.run (ReadsTo.bg→ R yQ x) w
  join-to R R⁻ yQ (Joining.rend x nh d)  = Joining.rend (ReadsTo.bg→ R yQ x) (λ h → nh (ReadsTo.ha→ R⁻ yQ h)) (done-to R R⁻ yQ d)
  join-to R R⁻ yQ (Joining.rpass x nh nd) = Joining.rpass (ReadsTo.bg→ R yQ x) (λ h → nh (ReadsTo.ha→ R⁻ yQ h)) (λ d → nd (done-to R⁻ R yQ d))
  join-to R R⁻ yQ (Joining.rhand {c} x h) = Joining.rhand (ReadsTo.bg→ R cQ x) (ReadsTo.ha→ R cQ h)
    where cQ = below c (c ++ [ ix 0 ]) (≺-ext c []) yQ

  -- TWO POLICIES READ ALIKE BELOW THE BOUND: joiners agreeing there.
  join-ag : ∀ {P P′ : Policy A B} → ReadsTo P P′ → ReadsTo P′ P → AgreeTo Q (JoinP P) (JoinP P′)
  join-ag R R⁻ = ⟨ (λ yQ → join-to R R⁻ yQ , join-to R⁻ R yQ) ⟩

  ----------------------------------------------------------------------
  -- The parts each policy reads

  lanes-to : ∀ {Ms Ms′ : List (EmissionSet B)} → Pointwise (AgreeTo Q) Ms Ms′ → ∀ {y e} → y ≼ Q → Lanes Ms y e → Lanes Ms′ y e
  lanes-to (g ∷ gs) {y} yQ (inj₁ x) = inj₁ (fwd g y yQ x)
  lanes-to (g ∷ gs) yQ (inj₂ x)     = inj₂ (lanes-to gs yQ x)

  -- Lanes by their ends, agreeing below the bound.
  ends-lag : ∀ {Ms Ms′ : List (EmissionSet B)} → Pointwise (AgreeTo Q) Ms Ms′ → LAg (EndsOf Ms) (EndsOf Ms′)
  ends-lag []       = none
  ends-lag (g ∷ gs) = (λ c cQ → upto g {c} {end} cQ) & ends-lag gs

  kth-to : ∀ {P ls ls′} → LAg ls ls′ → (∀ c → P c → c ≼ Q) → ∀ k → Kth P ls k → Kth P ls′ k
  kth-to none    bP k ()
  kth-to (g & G) bP zero    (inj₁ (c , y , pc))       = inj₁ (c , proj₁ (g c (bP c pc)) y , pc)
  kth-to (g & G) bP zero    (inj₂ r)                  = inj₂ (kth-to G bP zero r)
  kth-to (g & G) bP (suc k) (inj₁ ((c , y , pc) , r)) = inj₁ ((c , proj₁ (g c (bP c pc)) y , pc) , kth-to G bP k r)
  kth-to (g & G) bP (suc k) (inj₂ r)                  = inj₂ (kth-to G bP (suc k) r)

  all-to : ∀ {P ls ls′} → LAg ls ls′ → (∀ c → P c → c ≼ Q) → ∀ k → AllEnd P k ls → AllEnd P k ls′
  all-to G bP zero    h = tt
  all-to G bP (suc k) h = kth-to G bP k h

  at-or-before : ∀ c → c ≼ Q → ∀ c′ → c′ ≼ c → c′ ≼ Q
  at-or-before c cQ c′ le = trans≼ c′ c le cQ

  before : ∀ c → c ≼ Q → ∀ c′ → c′ ≺ c → c′ ≼ Q
  before c cQ c′ lt = below c′ c lt cQ

  module _ {L L′ : A → Pos → EmissionSet B} (la : ∀ a p → AgreeTo Q (L a p) (L′ a p)) where
    lane-to : ∀ {q a k e} → k ≼ Q → Lane L q a k e → Lane L′ q a k e
    lane-to {q} {a} {k} kQ (reads l p) = reads (fwd (la a (q ++ [ ix 1 ])) k kQ l) p

    from-to : ∀ {a s k e} → k ≼ Q → From L a s k e → From L′ a s k e
    from-to {a} {s} {k} kQ (sub r p) = sub (fwd (la a s) k kQ r) p

  lane-past : ∀ {L : A → Pos → EmissionSet B} {q a k e} → Lane L q a k e → q ≺ k
  lane-past {q = q} {k = k} (reads _ p) = ≺-trans {q} {q ++ [ ix 1 ]} {k} (≺-ext q []) p

  module _ {O O′ : EmissionSet A} (ao : AgreeTo Q O O′) where
    ended-to : ∀ {c} → c ≼ Q → Ended O c → Ended O′ c
    ended-to {c} cQ (c₀ , x , le) = c₀ , fwd ao c₀ (trans≼ c₀ c le cQ) x , le

    over-d : ∀ {d c} → c ≼ Q → T d ⊎ Ended O c → T d ⊎ Ended O′ c
    over-d cQ (inj₁ t) = inj₁ t
    over-d cQ (inj₂ e) = inj₂ (ended-to cQ e)

  ----------------------------------------------------------------------
  -- Merge

  module _ {L L′ : A → Pos → EmissionSet B} {O O′ : EmissionSet A} (d : Bool) (n : ℕ) {Ls Ls′ : List (EmissionSet B)}
           (ao : AgreeTo Q O O′) (ls : Pointwise (AgreeTo Q) Ls Ls′) where
    flat-ov : ∀ {c} → c ≼ Q → Flat.Over L O d n Ls c → Flat.Over L′ O′ d n Ls′ c
    flat-ov {c} cQ (Flat.over-at o l) = Flat.over-at (over-d ao cQ o) (all-to (ends-lag ls) (at-or-before c cQ) n l)

  flat-to : ∀ {L L′ : A → Pos → EmissionSet B} {O O′ : EmissionSet A} d n {Ls Ls′ : List (EmissionSet B)}
          → (∀ a p → AgreeTo Q (L a p) (L′ a p)) → AgreeTo Q O O′ → Pointwise (AgreeTo Q) Ls Ls′
          → ReadsTo (flatP L O d n Ls) (flatP L′ O′ d n Ls′)
  flat-to {L} {L′} d n la ao ls = record
    { out→  = λ {y} yQ → fwd ao y yQ
    ; bg→   = lanes-to ls
    ; lane→ = λ kQ _ _ → lane-to la kQ
    ; past  = lane-past {L}
    ; ov→   = flat-ov {L} {L′} d n ao ls
    ; ru→   = λ _ _ _ → tt
    ; cu→   = λ _ ()
    ; ha→   = λ _ ()
    }

  ----------------------------------------------------------------------
  -- Switch

  module _ {L L′ : A → Pos → EmissionSet B} {O O′ : EmissionSet A} (d : Bool) (n : ℕ) {Ls Ls′ : List (EmissionSet B)}
           (ao : AgreeTo Q O O′) where
    kill-to : ∀ {k} → k ≼ Q → SwitchF.Kill L O d n Ls k → SwitchF.Kill L′ O′ d n Ls′ k
    kill-to {k} kQ (q′ , a′ , x , lt) = q′ , a′ , fwd ao q′ (below q′ k lt kQ) x , lt

    swcut-to : ∀ {q k} → k ≼ Q → SwitchF.Cut L O d n Ls q k → SwitchF.Cut L′ O′ d n Ls′ q k
    swcut-to {k = k} kQ (q′ , a′ , x , lt , lt′) = q′ , a′ , fwd ao q′ (below q′ k lt′ kQ) x , lt , lt′

  module _ {L L′ : A → Pos → EmissionSet B} {O O′ : EmissionSet A} (d : Bool) (n : ℕ) {Ls Ls′ : List (EmissionSet B)}
           (ao : AgreeTo Q O O′) (ls : Pointwise (AgreeTo Q) Ls Ls′) where
    sw-bg : ∀ {y e} → y ≼ Q → SwitchF.Bg L O d n Ls y e → SwitchF.Bg L′ O′ d n Ls′ y e
    sw-bg yQ (SwitchF.bg x nk) = SwitchF.bg (lanes-to ls yQ x) (λ k → nk (kill-to {L′} {L} d n {Ls′} {Ls} (AgreeTo-sym ao) yQ k))
    sw-bg {y} yQ (SwitchF.bpin {r = r} x nk i) =
      SwitchF.bpin (lanes-to ls yQ x) (λ k → nk (kill-to {L′} {L} d n {Ls′} {Ls} (AgreeTo-sym ao) (conn≼ r y i yQ) k)) i

    sw-ov : ∀ {c} → c ≼ Q → SwitchF.Over L O d n Ls c → SwitchF.Over L′ O′ d n Ls′ c
    sw-ov {c} cQ (o , inj₁ l) = over-d ao cQ o , inj₁ (all-to (ends-lag ls) (at-or-before c cQ) n l)
    sw-ov cQ (o , inj₂ k)     = over-d ao cQ o , inj₂ (kill-to {L} {L′} d n {Ls} {Ls′} ao cQ k)

  switch-to : ∀ {L L′ : A → Pos → EmissionSet B} {O O′ : EmissionSet A} d n {Ls Ls′ : List (EmissionSet B)}
            → (∀ a p → AgreeTo Q (L a p) (L′ a p)) → AgreeTo Q O O′ → Pointwise (AgreeTo Q) Ls Ls′
            → ReadsTo (switchP L O d n Ls) (switchP L′ O′ d n Ls′)
  switch-to {L} {L′} {O} {O′} d n {Ls} {Ls′} la ao ls = record
    { out→  = λ {y} yQ → fwd ao y yQ
    ; bg→   = sw-bg {L} {L′} d n ao ls
    ; lane→ = λ kQ _ _ → lane-to la kQ
    ; past  = lane-past {L}
    ; ov→   = sw-ov {L} {L′} d n ao ls
    ; ru→   = λ _ _ _ → tt
    ; cu→   = λ {q} {k} → swcut-to {L} {L′} {O} {O′} d n {Ls} {Ls′} ao {q} {k}
    ; ha→   = λ _ ()
    }

  ----------------------------------------------------------------------
  -- Exhaust

  module _ {L L′ : A → Pos → EmissionSet B} {O O′ : EmissionSet A} (d : Bool) (n : ℕ) {Ls Ls′ : List (EmissionSet B)}
           (la : ∀ a p → AgreeTo Q (L a p) (L′ a p)) (ao : AgreeTo Q O O′) (ls : Pointwise (AgreeTo Q) Ls Ls′)
           (la⁻ : ∀ a p → AgreeTo Q (L′ a p) (L a p)) (ls⁻ : Pointwise (AgreeTo Q) Ls′ Ls) where
    open ExhaustF using (Cur; cur₀; bg₀; run; drop; brun; bdrop)

    -- The last lane run lies at or before the value now.
    cur-le : ∀ {q₁ q} → Cur L O d n Ls q₁ (just q) → q ≼ q₁
    cur-le {q₁} (cur₀ _ _ _)                        = ≼-refl {q₁}
    cur-le {q₂} (run _ _ _ _ _ _ _)                 = ≼-refl {q₂}
    cur-le (drop {q₁} {q} {q₂ = q₂} cu _ _ _ lt _)  = ≺→≼ {q} {q₂} (≼-≺-≺ {q} {q₁} {q₂} (cur-le cu) lt)
    cur-le {q₂} (brun _ _ _ _ _)                    = ≼-refl {q₂}

    cur-to : ∀ {q₁ w} → q₁ ≼ Q → Cur L O d n Ls q₁ w → Cur L′ O′ d n Ls′ q₁ w
    cur-to {q₁} q₁Q (cur₀ x mn f) = cur₀ (fwd ao q₁ q₁Q x) (least-to ao q₁ q₁Q mn) (all-to (ends-lag ls) (before q₁ q₁Q) n f)
    cur-to {q₁} q₁Q (bg₀ x mn nf) = bg₀ (fwd ao q₁ q₁Q x) (least-to ao q₁ q₁Q mn) (λ f → nf (all-to (ends-lag ls⁻) (before q₁ q₁Q) n f))
    cur-to {q₂} q₂Q (run {q₁} {q} {c = c} cu x l cq₂ x₂ lt nx) =
      run (cur-to (below q₁ q₂ lt q₂Q) cu) (fwd ao q qQ x) (lane-to la cQ l) cq₂ (fwd ao q₂ q₂Q x₂) lt (next-to ao q₁ q₂ q₂Q nx)
      where
        cQ = below c q₂ cq₂ q₂Q
        qQ = below q c (lane-past {L} l) cQ
    cur-to {q₂} q₂Q (drop {q₁} {q} {a} cu x nl x₂ lt nx) =
      drop (cur-to q₁Q cu) (fwd ao q qQ x) nl′ (fwd ao q₂ q₂Q x₂) lt (next-to ao q₁ q₂ q₂Q nx)
      where
        q₁Q = below q₁ q₂ lt q₂Q
        qQ  = trans≼ q q₁ (cur-le cu) q₁Q
        nl′ : ∀ {c} → Lane L′ q a c end → q₂ ≼ c
        nl′ {c} l′ with ≼-or-≻ c Q
        ... | inj₁ cQ = nl (lane-to la⁻ cQ l′)
        ... | inj₂ Qc = beyond q₂ c q₂Q Qc
    cur-to {q₂} q₂Q (brun {q₁} cu f x₂ lt nx) =
      brun (cur-to (below q₁ q₂ lt q₂Q) cu) (all-to (ends-lag ls) (before q₂ q₂Q) n f) (fwd ao q₂ q₂Q x₂) lt (next-to ao q₁ q₂ q₂Q nx)
    cur-to {q₂} q₂Q (bdrop {q₁} cu nf x₂ lt nx) =
      bdrop (cur-to (below q₁ q₂ lt q₂Q) cu) (λ f → nf (all-to (ends-lag ls⁻) (before q₂ q₂Q) n f)) (fwd ao q₂ q₂Q x₂) lt (next-to ao q₁ q₂ q₂Q nx)

    ex-ov : ∀ {c} → c ≼ Q → ExhaustF.Over L O d n Ls c → ExhaustF.Over L′ O′ d n Ls′ c
    ex-ov {c} cQ (o , l) = over-d ao cQ o , all-to (ends-lag ls) (at-or-before c cQ) n l

  exhaust-to : ∀ {L L′ : A → Pos → EmissionSet B} {O O′ : EmissionSet A} d n {Ls Ls′ : List (EmissionSet B)}
             → (∀ a p → AgreeTo Q (L a p) (L′ a p)) → AgreeTo Q O O′ → Pointwise (AgreeTo Q) Ls Ls′
             → (∀ a p → AgreeTo Q (L′ a p) (L a p)) → Pointwise (AgreeTo Q) Ls′ Ls
             → ReadsTo (exhaustP L O d n Ls) (exhaustP L′ O′ d n Ls′)
  exhaust-to {L} d n la ao ls la⁻ ls⁻ = record
    { out→  = λ {y} yQ → fwd ao y yQ
    ; bg→   = lanes-to ls
    ; lane→ = λ kQ _ _ → lane-to la kQ
    ; past  = lane-past {L}
    ; ov→   = ex-ov d n la ao ls la⁻ ls⁻
    ; ru→   = λ qQ _ u → cur-to d n la ao ls la⁻ ls⁻ qQ u
    ; cu→   = λ _ ()
    ; ha→   = λ _ ()
    }

  ----------------------------------------------------------------------
  -- Bounded merge

  -- Where a value at `w` arrived, at or before the bound.
  WQ : Maybe Pos → Set
  WQ nothing  = ⊤
  WQ (just q) = q ≼ Q

  -- One side's schedule pieces read as the other's, given the lanes before.
  module _ (m : ℕ) {L L′ : A → Pos → EmissionSet B} {O O′ : EmissionSet A} (d : Bool) (n : ℕ) (Qu : List A) {Ls Ls′ : List (EmissionSet B)}
           (ao : AgreeTo Q O O′) where
    private
      module B  = BoundedF m L O d n Qu Ls
      module B′ = BoundedF m L′ O′ d n Qu Ls′

    starts-w : ∀ {i ls w s} → Stem s → B.Starts i ls w s → WQ w
    starts-w {w = just q} st (B.room _)                    = st q refl
    starts-w {w = just q} st (B.freed _ _)                 = st q refl
    starts-w {w = nothing} st (B.queued _ _ _ _ _)          = tt
    starts-w {w = just q} st (B.queued {c = c} _ qc _ _ _) = below q c qc (st c refl)

    item-to : ∀ {i w a} → WQ w → B.Item i w a → B′.Item i w a
    item-to _  (B.queued x) = B′.queued x
    item-to qQ (B.outer N)  = B′.outer (nth-to ao qQ N)

    arr-to : ∀ {w c} → B.Arr w c → B′.Arr w c
    arr-to {nothing} a = a
    arr-to {just q}  a = a

    starts-to : ∀ {i ls ls′ w s} → LAg ls ls′ → Stem s → B.Starts i ls w s → B′.Starts i ls′ w s
    starts-to G st (B.room lt)                          = B′.room lt
    starts-to G st (B.freed {q} le h)                   = B′.freed le (kth-to G (λ c cq → below c q cq (st q refl)) _ h)
    starts-to G st (B.queued {w} {c} le ar one h nh)    =
      B′.queued le (arr-to {w} ar) (kth-to G (λ { c′ refl → cQ }) 0 one) (kth-to G (at-or-before c cQ) _ h)
                (λ h′ → nh (kth-to (lag-sym G) (before c cQ) _ h′))
      where cQ = st c refl

  -- A lane subscribed at `s` starts past its value.
  starts-past : ∀ m {L : A → Pos → EmissionSet B} {O : EmissionSet A} d n Qu {Ls : List (EmissionSet B)} {i ls q s}
              → BoundedF.Starts m L O d n Qu Ls i ls (just q) s → q ≺ s
  starts-past m d n Qu {q = q} (BoundedF.room _)    = ≺-ext q []
  starts-past m d n Qu {q = q} (BoundedF.freed _ _) = ≺-ext q []
  starts-past m d n Qu {q = q} (BoundedF.queued {c = c} _ qc _ _ _) = ≺-trans {q} {c} {c ++ [ ix 1 ]} qc (≺-ext c [])

  module _ (m : ℕ) {L L′ : A → Pos → EmissionSet B} {O O′ : EmissionSet A} (d : Bool) (n : ℕ) (Qu : List A) {Ls Ls′ : List (EmissionSet B)}
           (la : ∀ a p → AgreeTo Q (L a p) (L′ a p)) (ao : AgreeTo Q O O′) (ls : Pointwise (AgreeTo Q) Ls Ls′)
           (la⁻ : ∀ a p → AgreeTo Q (L′ a p) (L a p)) (ls⁻ : Pointwise (AgreeTo Q) Ls′ Ls) where
    private
      module B  = BoundedF m L O d n Qu Ls
      module B′ = BoundedF m L′ O′ d n Qu Ls′
      ao⁻ = AgreeTo-sym ao

    -- The schedules agree lane by lane, each read where it is subscribed.
    sched-ag : ∀ i → LAg (B.Sched i) (B′.Sched i)
    sched-ag zero    = ends-lag ls
    sched-ag (suc i) = (λ c cQ → there c cQ , back c cQ) & G
      where
        G = sched-ag i

        there : ∀ c → c ≼ Q → B.Ends i (B.Sched i) c → B′.Ends i (B′.Sched i) c
        there c cQ (w , a , s , I , St , fr@(sub _ sc)) =
          w , a , s , item-to m {L} {L′} d n Qu {Ls} {Ls′} ao (starts-w m {L} {L′} d n Qu {Ls} {Ls′} ao st St) I
            , starts-to m {L} {L′} d n Qu {Ls} {Ls′} ao G st St , from-to la cQ fr
          where st = stem-≼ s (below s c sc cQ)

        back : ∀ c → c ≼ Q → B′.Ends i (B′.Sched i) c → B.Ends i (B.Sched i) c
        back c cQ (w , a , s , I , St , fr@(sub _ sc)) =
          w , a , s , item-to m {L′} {L} d n Qu {Ls′} {Ls} ao⁻ (starts-w m {L′} {L} d n Qu {Ls′} {Ls} ao⁻ st St) I
            , starts-to m {L′} {L} d n Qu {Ls′} {Ls} ao⁻ (lag-sym G) st St , from-to la⁻ cQ fr
          where st = stem-≼ s (below s c sc cQ)

    sub-to : ∀ {i w s a} → Stem s → B.Sub i w s a → B′.Sub i w s a
    sub-to {i} st (I , St) = item-to m {L} {L′} d n Qu {Ls} {Ls′} ao (starts-w m {L} {L′} d n Qu {Ls} {Ls′} ao st St) I
                           , starts-to m {L} {L′} d n Qu {Ls} {Ls′} ao (sched-ag i) st St

    laneB-to : ∀ {q a k e} → k ≼ Q → B.LaneB q a k e → B′.LaneB q a k e
    laneB-to {k = k} kQ (i , s , sb , fr@(sub _ sk)) = i , s , sub-to (stem-≼ s (below s k sk kQ)) sb , from-to la kQ fr

    laneB-past : ∀ {q a k e} → B.LaneB q a k e → q ≺ k
    laneB-past {q} {k = k} (i , s , (_ , St) , sub _ sk) = ≺-trans {q} {s} {k} (starts-past m d n Qu St) sk

    bd-bg : ∀ {y e} → y ≼ Q → B.Bg y e → B′.Bg y e
    bd-bg yQ (B.begun x)                       = B′.begun (lanes-to ls yQ x)
    bd-bg {y} yQ (B.waits {s = s} sb fr@(sub _ sk)) = B′.waits (sub-to (stem-≼ s (below s y sk yQ)) sb) (from-to la yQ fr)

    bd-ov : ∀ {c} → c ≼ Q → B.Over c → B′.Over c
    bd-ov {c} cQ (o , l) = over-d ao cQ o , all-to (sched-ag (length Qu)) (at-or-before c cQ) (n + length Qu) l

    bd-ru : ∀ {q} → q ≼ Q → B.Indexed q → B′.Indexed q
    bd-ru qQ (i , a , I) = i , a , item-to m {L} {L′} d n Qu {Ls} {Ls′} ao qQ I

    bd-ha : ∀ {c} → c ≼ Q → B.Queued c → B′.Queued c
    bd-ha {c} cQ (i , w , a , sb) = i , w , a , sub-to (stem-at c cQ) sb

  bounded-to : ∀ m {L L′ : A → Pos → EmissionSet B} {O O′ : EmissionSet A} d n Qu {Ls Ls′ : List (EmissionSet B)}
             → (∀ a p → AgreeTo Q (L a p) (L′ a p)) → AgreeTo Q O O′ → Pointwise (AgreeTo Q) Ls Ls′
             → (∀ a p → AgreeTo Q (L′ a p) (L a p)) → Pointwise (AgreeTo Q) Ls′ Ls
             → ReadsTo (boundedP m L O d n Qu Ls) (boundedP m L′ O′ d n Qu Ls′)
  bounded-to m d n Qu la ao ls la⁻ ls⁻ = record
    { out→  = λ {y} yQ → fwd ao y yQ
    ; bg→   = bd-bg m d n Qu la ao ls la⁻ ls⁻
    ; lane→ = λ kQ _ _ → laneB-to m d n Qu la ao ls la⁻ ls⁻ kQ
    ; past  = laneB-past m d n Qu la ao ls la⁻ ls⁻
    ; ov→   = bd-ov m d n Qu la ao ls la⁻ ls⁻
    ; ru→   = λ qQ _ u → bd-ru m d n Qu la ao ls la⁻ ls⁻ qQ u
    ; cu→   = λ _ ()
    ; ha→   = bd-ha m d n Qu la ao ls la⁻ ls⁻
    }
