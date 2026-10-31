{-# OPTIONS --guardedness #-}

-- AN OUTER'S VALUE BEGINS ITS LANE: the outer rises a value at `p`, and
-- the joiner subscribes the value's lane at `p`'s second child.  The two
-- readings of the joiner agree but for the value's own row, a skip at
-- `p`'s first child: before, the value is the outer's and its lane is
-- read off it; after, the outer owes it no longer and the lane is begun.
-- Every other part lies past `p`, so the skip is unseen above.  One step
-- for every joiner, read by its policy.
module adequacy.OuterNx where

open import Data.Bool using (Bool; true; false; T; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Relation.Unary.All using ([])
open import Data.List using (List; []; _∷_; _++_; [_]; _ʳ++_; reverse)
open import Data.List.Properties using (ʳ++-defn; reverse-involutive)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Properties using (<ᵇ⇒<; <-irrefl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to either)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)

open import Tree using (Obs; FlatOp; mergeᶠ; exhaustᶠ)
open import denotation.Events using (Pos; Timeline; ix; inside)
open import denotation.EmissionSet using (EmissionSet; out; pin; end; _≺_; _≼_; Ended; DenEnv; Truncate; module Joining)
open import denotation.Laws.Modulus using (≺-trans; ≺→≼; ≼-refl; ≺-ext)
open import denotation.Laws.Worlds using (Ok; Hots; InvAt; ok-step; world-after)
open import denotation.Laws using (inv-⟦⟧)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; ⟨_,_,_,_⟩; plug; absorbed; rising; subscribing; nx; alive; closed; start; attAt; pend; doneS; cutS; lnS; flatS;
                    inOuter; inCut; inLn; inLanes)
open import adequacy.Rows using (env; up; rows; rowsL; pendRows; Plus; old; new; Lane; reads; Lanes; Each; Kth; AllEnd; EndsOf; module Flat; Moves; silent)
open import adequacy.Up using (up-≃; ≃-trans; vis-≃)
open import adequacy.Bound using (Good; GoodL; G; MergeG; live; lane-v; on; off)
open import adequacy.Skip using (After; Since; LeadC; Skip; _≈⟨_⟩_; _⇆_; since-join; since-trunc; up-vis-at; trunc-≈)
open import adequacy.Policy using (Policy; JoinP; DoneP; polOf; flatP; boundedP; exhaustP)
open import adequacy.LaneEnd using (Has; kth-skip; kth-less)
open import adequacy.Swap using (rowsL-ʳ++; ≡→≃)
open import adequacy.Env using (env-good)
open import adequacy.Inv using (Inv; inv; good; lead; Sim; UpO; Shut; open-alive; node-good; upo-liv; closed-dead)

open Policy

------------------------------------------------------------------------
-- One lane more, last

lanes-snoc : ∀ {B} (Ls : List (EmissionSet B)) {T₁ : EmissionSet B} {k e} → Lanes (Ls ++ [ T₁ ]) k e → Lanes Ls k e ⊎ T₁ k e
lanes-snoc []       (inj₁ r) = inj₂ r
lanes-snoc []       (inj₂ ())
lanes-snoc (_ ∷ Ls) (inj₁ r) = inj₁ (inj₁ r)
lanes-snoc (_ ∷ Ls) (inj₂ x) with lanes-snoc Ls x
... | inj₁ y = inj₁ (inj₂ y)
... | inj₂ r = inj₂ r

snoc-lanes : ∀ {B} (Ls : List (EmissionSet B)) {T₁ : EmissionSet B} {k e} → Lanes Ls k e ⊎ T₁ k e → Lanes (Ls ++ [ T₁ ]) k e
snoc-lanes []       (inj₁ ())
snoc-lanes []       (inj₂ r)        = inj₁ r
snoc-lanes (_ ∷ Ls) (inj₁ (inj₁ r)) = inj₁ r
snoc-lanes (_ ∷ Ls) (inj₁ (inj₂ x)) = inj₂ (snoc-lanes Ls (inj₁ x))
snoc-lanes (_ ∷ Ls) (inj₂ r)        = inj₂ (snoc-lanes Ls (inj₂ r))

lanes-after : ∀ {B} {p} (Ls : List (EmissionSet B)) → Each (After p) Ls → After p (Lanes Ls)
lanes-after          (_ ∷ _)  (a , _)  (inj₁ r) = a r
lanes-after {p = p} (_ ∷ Ls) (_ , as) (inj₂ x) = lanes-after {p = p} Ls as x

cons-all : ∀ {P x} ls k → Has P x → AllEnd P k ls → Kth P (x ∷ ls) k
cons-all ls zero    h _ = inj₁ h
cons-all ls (suc k) h a = inj₁ (h , a)

-- The begun lanes' ends, the new lane's last.
snoc-end : ∀ {B P} (Ls : List (EmissionSet B)) {T₁ : EmissionSet B} k → AllEnd P k (EndsOf Ls) → Has P (λ c → T₁ c end) → Kth P (EndsOf (Ls ++ [ T₁ ])) k
snoc-end []       zero          _               h = inj₁ h
snoc-end (_ ∷ Ls) zero          _               h = inj₂ (snoc-end Ls zero tt h)
snoc-end []       (suc k)       ()              h
snoc-end (_ ∷ Ls) (suc zero)    (inj₁ hx)       h = inj₁ (hx , snoc-end Ls zero tt h)
snoc-end (_ ∷ Ls) (suc zero)    (inj₂ r)        h = inj₂ (snoc-end Ls (suc zero) r h)
snoc-end (_ ∷ Ls) (suc (suc j)) (inj₁ (hx , r)) h = inj₁ (hx , snoc-end Ls (suc j) r h)
snoc-end (_ ∷ Ls) (suc (suc j)) (inj₂ r)        h = inj₂ (snoc-end Ls (suc (suc j)) r h)

unsnoc : ∀ {B P} (Ls : List (EmissionSet B)) {T₁ : EmissionSet B} k → Kth P (EndsOf (Ls ++ [ T₁ ])) k
       → Kth P (EndsOf Ls) k ⊎ (AllEnd P k (EndsOf Ls) × Has P (λ c → T₁ c end))
unsnoc []       zero    (inj₁ h)        = inj₂ (tt , h)
unsnoc []       zero    (inj₂ ())
unsnoc []       (suc k) (inj₁ (_ , ()))
unsnoc []       (suc k) (inj₂ ())
unsnoc (_ ∷ Ls) zero    (inj₁ hx)       = inj₁ (inj₁ hx)
unsnoc (_ ∷ Ls) zero    (inj₂ r) with unsnoc Ls zero r
... | inj₁ r′      = inj₁ (inj₂ r′)
... | inj₂ (_ , h) = inj₂ (tt , h)
unsnoc (_ ∷ Ls) (suc k) (inj₁ (hx , r)) with unsnoc Ls k r
... | inj₁ r′      = inj₁ (inj₁ (hx , r′))
... | inj₂ (a , h) = inj₂ (cons-all (EndsOf Ls) k hx a , h)
unsnoc (_ ∷ Ls) (suc k) (inj₂ r) with unsnoc Ls (suc k) r
... | inj₁ r′      = inj₁ (inj₂ r′)
... | inj₂ (a , h) = inj₂ (kth-skip (EndsOf Ls) k a , h)

kth-none : ∀ {P} (ls : List (Pos → Set)) k → Kth P ((λ _ → ⊥) ∷ ls) k → Kth P ls k
kth-none ls zero    (inj₁ (_ , () , _))
kth-none ls zero    (inj₂ x) = x
kth-none ls (suc k) (inj₁ ((_ , () , _) , _))
kth-none ls (suc k) (inj₂ x) = x

-- No more ends among a merge's lanes than it has live.
live-cap : ∀ {Γ B} {ρ : DenEnv Γ} {P} (ls : List (St Γ B)) → GoodL ρ ls → Kth P (EndsOf (rowsL ρ ls)) (live ls) → ⊥
live-cap []       _         ()
live-cap (s ∷ ls) (gs , gl) x with lane-v s gs
live-cap (_ ∷ ls) (gs , gl) (inj₁ (_ , y)) | on _ _ _ _ = live-cap ls gl y
live-cap (_ ∷ ls) (gs , gl) (inj₂ y)       | on _ _ _ _ = live-cap ls gl (kth-less _ (live ls) y)
live-cap {ρ = ρ} (_ ∷ ls) (gs , gl) x      | off _ _    = live-cap ls gl (kth-none (EndsOf (rowsL ρ ls)) (live ls) x)

cap-of : ∀ {Γ B} {ρ : DenEnv Γ} {n} (ls : List (St Γ B)) → GoodL ρ ls → n ≡ live ls → ∀ {P} → Kth P (EndsOf (rowsL ρ ls)) n → ⊥
cap-of ls gl refl = live-cap ls gl

------------------------------------------------------------------------
-- The frame

-- What two readings of a joiner share, the first's outer owing a value
-- at `p` whose lane the second has begun.
record BeginAt {A B : Set} (PX PY : Policy A B) (p : Pos) (a : A) : Set where
  field
    ox   : ∀ {q e} → outer PX q e → (q ≡ p × e ≡ out a) ⊎ outer PY q e
    oy   : ∀ {q e} → outer PY q e → outer PX q e
    oat  : outer PX p (out a)
    ao   : After p (outer PY)
    rp   : runs PX p
    ru→  : ∀ {q b} → outer PY q (out b) → runs PX q → runs PY q
    ru←  : ∀ {q b} → outer PY q (out b) → runs PY q → runs PX q
    la→  : ∀ {q b k e} → outer PY q (out b) → lanes PX q b k e → lanes PY q b k e
    la←  : ∀ {q b k e} → outer PY q (out b) → lanes PY q b k e → lanes PX q b k e
    al   : ∀ {q b k e} → outer PX q (out b) → lanes PX q b k e → p ≺ k
    cu→  : ∀ {q b k} → outer PY q (out b) → cut PX q k → cut PY q k
    cu←  : ∀ {q b k} → outer PY q (out b) → cut PY q k → cut PX q k
    bgn  : ∀ {k e} → lanes PX p a k e → ¬ cut PX p k → begun PY k e
    bgp  : ∀ {k r} → lanes PX p a k (pin r) → ¬ cut PX p r → T (inside r k) → begun PY k (pin r)
    bg→  : ∀ {k e} → begun PX k e → begun PY k e
    bg←  : ∀ {k e} → begun PY k e
         → begun PX k e ⊎ (lanes PX p a k e × (¬ cut PX p k ⊎ Σ Pos λ r → e ≡ pin r × ¬ cut PX p r × T (inside r k)))
    ab   : After p (begun PY)
    ha→  : ∀ {c} → p ≺ c → hand PX c → hand PY c
    ha←  : ∀ {c} → p ≺ c → hand PY c → hand PX c
    dn→  : ∀ {c} → p ≺ c → DoneP PX c → DoneP PY c
    dn←  : ∀ {c} → p ≺ c → DoneP PY c → DoneP PX c

module BFrame {A B : Set} {PX PY : Policy A B} {p : Pos} {a : A} (E : BeginAt PX PY p a) where
  open BeginAt E

  fwd : ∀ {k e} → JoinP PX k e → JoinP PY k e ⊎ Skip (p ++ [ ix 0 ]) k e
  fwd (Joining.val r) with ox r
  ... | inj₁ (refl , refl) = inj₂ (refl , refl)
  ... | inj₂ r′            = inj₁ (Joining.val r′)
  fwd (Joining.step r) with ox r
  ... | inj₁ (_ , ())
  ... | inj₂ r′ = inj₁ (Joining.step r′)
  fwd (Joining.opin r) with ox r
  ... | inj₁ (_ , ())
  ... | inj₂ r′ = inj₁ (Joining.opin r′)
  fwd (Joining.oend r d) with ox r
  ... | inj₁ (_ , ())
  ... | inj₂ r′ = inj₁ (Joining.oend r′ (dn→ (ao r′) d))
  fwd (Joining.opass r nd) with ox r
  ... | inj₁ (_ , ())
  ... | inj₂ r′ = inj₁ (Joining.opass r′ (λ d → nd (dn← (ao r′) d)))
  fwd (Joining.lane r u l nc w) with ox r
  ... | inj₁ (refl , refl) = inj₁ (Joining.run (bgn l nc) w)
  ... | inj₂ r′            = inj₁ (Joining.lane r′ (ru→ r′ u) (la→ r′ l) (λ ct → nc (cu← r′ ct)) w)
  fwd (Joining.lend r u l nc nh d) with ox r
  ... | inj₁ (refl , refl) = inj₁ (Joining.rend (bgn l nc) (λ h → nh (ha← (al r l) h)) (dn→ (al r l) d))
  ... | inj₂ r′            = inj₁ (Joining.lend r′ (ru→ r′ u) (la→ r′ l) (λ ct → nc (cu← r′ ct)) (λ h → nh (ha← (al r l) h)) (dn→ (al r l) d))
  fwd (Joining.lpass r u l nc nh nd) with ox r
  ... | inj₁ (refl , refl) = inj₁ (Joining.rpass (bgn l nc) (λ h → nh (ha← (al r l) h)) (λ d → nd (dn← (al r l) d)))
  ... | inj₂ r′            = inj₁ (Joining.lpass r′ (ru→ r′ u) (la→ r′ l) (λ ct → nc (cu← r′ ct)) (λ h → nh (ha← (al r l) h)) (λ d → nd (dn← (al r l) d)))
  fwd (Joining.hand r u l nc h) with ox r
  ... | inj₁ (refl , refl) = inj₁ (Joining.rhand (bgn l nc) (ha→ (al r l) h))
  ... | inj₂ r′            = inj₁ (Joining.hand r′ (ru→ r′ u) (la→ r′ l) (λ ct → nc (cu← r′ ct)) (ha→ (al r l) h))
  fwd (Joining.left r u l nc i) with ox r
  ... | inj₁ (refl , refl) = inj₁ (Joining.run (bgp l nc i) tt)
  ... | inj₂ r′            = inj₁ (Joining.left r′ (ru→ r′ u) (la→ r′ l) (λ ct → nc (cu← r′ ct)) i)
  fwd (Joining.run x w)       = inj₁ (Joining.run (bg→ x) w)
  fwd (Joining.rend x nh d)   = inj₁ (Joining.rend (bg→ x) (λ h → nh (ha← (ab (bg→ x)) h)) (dn→ (ab (bg→ x)) d))
  fwd (Joining.rpass x nh nd) = inj₁ (Joining.rpass (bg→ x) (λ h → nh (ha← (ab (bg→ x)) h)) (λ d → nd (dn← (ab (bg→ x)) d)))
  fwd (Joining.rhand x h)     = inj₁ (Joining.rhand (bg→ x) (ha→ (ab (bg→ x)) h))

  bwd : ∀ {k e} → JoinP PY k e → JoinP PX k e ⊎ Skip (p ++ [ ix 0 ]) k e
  bwd (Joining.val r)                = inj₁ (Joining.val (oy r))
  bwd (Joining.step r)               = inj₁ (Joining.step (oy r))
  bwd (Joining.opin r)               = inj₁ (Joining.opin (oy r))
  bwd (Joining.oend r d)             = inj₁ (Joining.oend (oy r) (dn← (ao r) d))
  bwd (Joining.opass r nd)           = inj₁ (Joining.opass (oy r) (λ d → nd (dn→ (ao r) d)))
  bwd (Joining.lane r u l nc w)      = inj₁ (Joining.lane (oy r) (ru← r u) (la← r l) (λ ct → nc (cu→ r ct)) w)
  bwd (Joining.lend r u l nc nh d)   =
    inj₁ (Joining.lend (oy r) (ru← r u) (la← r l) (λ ct → nc (cu→ r ct)) (λ h → nh (ha→ (al (oy r) (la← r l)) h)) (dn← (al (oy r) (la← r l)) d))
  bwd (Joining.lpass r u l nc nh nd) =
    inj₁ (Joining.lpass (oy r) (ru← r u) (la← r l) (λ ct → nc (cu→ r ct)) (λ h → nh (ha→ (al (oy r) (la← r l)) h)) (λ d → nd (dn→ (al (oy r) (la← r l)) d)))
  bwd (Joining.hand r u l nc h)      = inj₁ (Joining.hand (oy r) (ru← r u) (la← r l) (λ ct → nc (cu→ r ct)) (ha← (al (oy r) (la← r l)) h))
  bwd (Joining.left r u l nc i)      = inj₁ (Joining.left (oy r) (ru← r u) (la← r l) (λ ct → nc (cu→ r ct)) i)
  bwd (Joining.run x w) with bg← x
  ... | inj₁ x′                             = inj₁ (Joining.run x′ w)
  ... | inj₂ (l , inj₁ nc)                  = inj₁ (Joining.lane oat rp l nc w)
  ... | inj₂ (l , inj₂ (_ , refl , nc , i)) = inj₁ (Joining.left oat rp l nc i)
  bwd (Joining.rend x nh d) with bg← x
  ... | inj₁ x′                     = inj₁ (Joining.rend x′ (λ h → nh (ha→ (ab x) h)) (dn← (ab x) d))
  ... | inj₂ (l , inj₁ nc)          = inj₁ (Joining.lend oat rp l nc (λ h → nh (ha→ (ab x) h)) (dn← (ab x) d))
  ... | inj₂ (_ , inj₂ (_ , () , _))
  bwd (Joining.rpass x nh nd) with bg← x
  ... | inj₁ x′                     = inj₁ (Joining.rpass x′ (λ h → nh (ha→ (ab x) h)) (λ d → nd (dn→ (ab x) d)))
  ... | inj₂ (l , inj₁ nc)          = inj₁ (Joining.lpass oat rp l nc (λ h → nh (ha→ (ab x) h)) (λ d → nd (dn→ (ab x) d)))
  ... | inj₂ (_ , inj₂ (_ , () , _))
  bwd (Joining.rhand x h) with bg← x
  ... | inj₁ x′                     = inj₁ (Joining.rhand x′ (ha← (ab x) h))
  ... | inj₂ (l , inj₁ nc)          = inj₁ (Joining.hand oat rp l nc (ha← (ab x) h))
  ... | inj₂ (_ , inj₂ (_ , () , _))

  -- THE FRAME: the two readings agree but for the value's skip.
  frame : JoinP PX ≈⟨ p ++ [ ix 0 ] ⟩ JoinP PY
  frame = fwd ⇆ bwd

  since-x : Since p (JoinP PX)
  since-x = since-join PX so (λ {k} x → ≺→≼ {p} {k} (ab (bg→ x))) (λ {_} {_} {k} r l → ≺→≼ {p} {k} (al r l))
    where
      so : Since p (outer PX)
      so {q} r with ox r
      ... | inj₁ (refl , _) = ≼-refl {p}
      ... | inj₂ r′         = ≺→≼ {p} {q} (ao r′)

  since-y : Since p (JoinP PY)
  since-y = since-join PY (λ {q} r → ≺→≼ {p} {q} (ao r)) (λ {k} x → ≺→≼ {p} {k} (ab x)) (λ {_} {_} {k} r l → ≺→≼ {p} {k} (al (oy r) (la← r l)))

------------------------------------------------------------------------
-- Merge

module _ {A B : Set} (L : A → Pos → EmissionSet B) {p : Pos} {O : EmissionSet A} {d : Bool} {n : ℕ} (Ls : List (EmissionSet B)) {a : A}
         (ao : After p O) (als : Each (After p) Ls) (tp : ∀ {k e} → L a (p ++ [ ix 1 ]) k e → (p ++ [ ix 1 ]) ≺ k)
         (cap : ∀ {P} → Kth P (EndsOf Ls) n → ⊥) where

  private
    Tn = L a (p ++ [ ix 1 ])
    OX = Plus O p (out a)
    PX = flatP L OX d n Ls
    PY = flatP L O d (suc n) (Ls ++ [ Tn ])

    lane-past : ∀ {q b k e} → Lane L q b k e → q ≺ k
    lane-past {q} {k = k} (reads _ pk) = ≺-trans {q} {q ++ [ ix 1 ]} {k} (≺-ext q []) pk

    al′ : ∀ {q b k e} → OX q (out b) → Lane L q b k e → p ≺ k
    al′ {q} {k = k} (old r) l = ≺-trans {p} {q} {k} (ao r) (lane-past l)
    al′ new l = lane-past l

    o-old : ∀ {c} → T d ⊎ Ended OX c → T d ⊎ Ended O c
    o-old (inj₁ t)                = inj₁ t
    o-old (inj₂ (c₀ , old r , le)) = inj₂ (c₀ , r , le)

    o-new : ∀ {c} → T d ⊎ Ended O c → T d ⊎ Ended OX c
    o-new (inj₁ t)            = inj₁ t
    o-new (inj₂ (c₀ , r , le)) = inj₂ (c₀ , old r , le)

    dn→′ : ∀ {c} → p ≺ c → DoneP PX c → DoneP PY c
    dn→′ {c} pc (Flat.over-at o lo , h) with h {p} new tt pc (λ ())
    ... | c₀ , l , le = Flat.over-at (o-old {c} o) (snoc-end Ls n lo (c₀ , Lane.lane l , le)) , λ r u lt nc → h (old r) u lt nc

    dn←′ : ∀ {c} → p ≺ c → DoneP PY c → DoneP PX c
    dn←′ {c} pc (Flat.over-at o lo , h) with unsnoc Ls n lo
    ... | inj₁ k                      = ⊥-elim (cap k)
    ... | inj₂ (lo′ , (c₀ , lc , le)) = Flat.over-at (o-new {c} o) lo′ , hx
      where
        hx : ∀ {q b} → OX q (out b) → ⊤ → q ≺ c → ¬ ⊥ → Σ Pos λ c₁ → Lane L q b c₁ end × c₁ ≼ c
        hx (old r) u lt nc = h r u lt nc
        hx new     u lt nc = c₀ , reads lc (tp lc) , le

  -- A MERGE'S TWO READINGS, A VALUE'S LANE BEGUN.
  merge-begin : BeginAt PX PY p a
  merge-begin = record
    { ox   = λ { (old r) → inj₂ r ; new → inj₁ (refl , refl) }
    ; oy   = old
    ; oat  = new
    ; ao   = ao
    ; rp   = tt
    ; ru→  = λ _ _ → tt
    ; ru←  = λ _ _ → tt
    ; la→  = λ _ l → l
    ; la←  = λ _ l → l
    ; al   = al′
    ; cu→  = λ _ ()
    ; cu←  = λ _ ()
    ; bgn  = λ l _ → snoc-lanes Ls (inj₂ (Lane.lane l))
    ; bgp  = λ l _ _ → snoc-lanes Ls (inj₂ (Lane.lane l))
    ; bg→  = λ x → snoc-lanes Ls (inj₁ x)
    ; bg←  = λ x → either inj₁ (λ t → inj₂ (reads t (tp t) , inj₁ (λ ()))) (lanes-snoc Ls x)
    ; ab   = λ {k} x → either (lanes-after {p = p} Ls als) (λ t → ≺-trans {p} {p ++ [ ix 1 ]} {k} (≺-ext p []) (tp t)) (lanes-snoc Ls x)
    ; ha→  = λ _ ()
    ; ha←  = λ _ ()
    ; dn→  = dn→′
    ; dn←  = dn←′
    }

------------------------------------------------------------------------
-- The step

-- One joiner's step: the lane subscribed, its value's row a skip.
module Begin {R Γ A B} (op : FlatOp) (f : A → Obs Timeline Γ B) (d : Bool) (n : ℕ) (q : List A) (o : St Γ A) (ls : List (St Γ B)) (c : Ctx R Γ B) (a : A) (p : Pos)
             (g′ : Good [] (plug c (flatS op f d (suc n) q o (reverse ls ʳ++ lnS true (cutS true (attAt (p ++ [ ix 1 ])) doneS) ∷ []))))
             (uc : UpO c) (lc : LeadC c p) (ok : Ok (Hots (env c)) p)
             (E : (∀ {k e} → pendRows (env c) (f a) (p ++ [ ix 1 ]) k e → (p ++ [ ix 1 ]) ≺ k)
                → BeginAt (polOf op (λ x → pendRows (env c) (f x)) (Plus (rows (env c) o) p (out a)) d n q (rowsL (env c) ls))
                          (polOf op (λ x → pendRows (env c) (f x)) (rows (env c) o) d (suc n) q (rowsL (env c) ls ++ [ pendRows (env c) (f a) (p ++ [ ix 1 ]) ]))
                          p a) where

  ρ : DenEnv Γ
  ρ = env c

  L  = λ x → pendRows ρ (f x)
  O  = rows ρ o
  Ls = rowsL ρ ls
  p₁ = p ++ [ ix 1 ]
  Tn = pendRows ρ (f a) p₁
  PX = polOf op L (Plus O p (out a)) d n q Ls
  PY = polOf op L O d (suc n) q (rowsL ρ (reverse ls) ʳ++ (Tn ∷ []))

  ok₁ : Ok (Hots ρ) p₁
  ok₁ = ok-step p ok

  -- The new lane's rows lie past where it subscribes: Tier −1's invariant.
  tp : ∀ {k e} → Tn k e → p₁ ≺ k
  tp r = world-after (InvAt.world I r) (InvAt.real I r)
    where I = inv-⟦⟧ (f a) ρ (env-good c g′) p₁ ok₁

  open BFrame (E tp)

  eq : rowsL ρ (reverse ls) ʳ++ (Tn ∷ []) ≡ Ls ++ [ Tn ]
  eq = trans (cong (_ʳ++ [ Tn ]) (rowsL-ʳ++ {ρ = ρ} ls)) (trans (ʳ++-defn (rowsL ρ ls ʳ++ [])) (cong (_++ [ Tn ]) (reverse-involutive Ls)))

  result : Inv ⟨ inCut true (attAt p₁) (inLn true (inLanes op f d (suc n) q o (reverse ls) [] c)) , pend (f a) p₁ , subscribing , p₁ ⟩
         × Moves (up c (Truncate (JoinP PX))) [] (up c (Truncate (JoinP PY)))
  result = inv g′ (uc , ok₁)
         , silent (≃-trans (up-vis-at c lc (≺→≼ {p} {p ++ [ ix 0 ]} (≺-ext p [])) (since-trunc since-x) (since-trunc since-y) (trunc-≈ frame))
                           (vis-≃ (up-≃ c (≡→≃ (cong (λ Ms → Truncate (JoinP (polOf op L O d (suc n) q Ms))) (sym eq))))))

postulate
  -- THE BEGUN LANE'S TREE GOOD: the lane subscribed at the value's second
  -- child, out of its list but owed, the tree stays good with one more
  -- live.  The lane is rooted at the value, which must lie in its outer's
  -- entry; `Inv` says the outer's rows lie there, but not the value it
  -- has just risen.  Every frame above reads the joiner's rows, now with
  -- the lane's for the value's.
  --
  -- DEAD ROUTE: every live node's rows inside an entry frozen when it
  --   subscribed, `Rooted`'s `sub` at each node of `Good`.  `Good` reads a
  --   rising focus's ancestors with the risen row already gone, and a
  --   joiner is not monotone in its parts: a lane's end gone leaves the
  --   joiner not done, so its outer's end reads as a pass where the entry
  --   holds the end.  Only a reading through the risen row, frame by frame
  --   up the context as `LeadC` reads `After`, stays inside the entry.
  begin-good : ∀ {R Γ A B} op (f : A → Obs Timeline Γ B) d n q ls (c : Ctx R Γ B) (o : St Γ A) a p
             → Inv ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩ → closed c ≡ false → q ≡ []
             → Good [] (plug c (flatS op f d (suc n) q o (reverse ls ʳ++ lnS true (cutS true (attAt (p ++ [ ix 1 ])) doneS) ∷ [])))

  -- THE RISEN VALUE IN ITS WORLD: an outer's rising value lies where its
  -- binders are hot, so the lane it begins subscribes there.  `Inv` says
  -- nothing of where the value lies but past the joiner's other parts.
  begin-ok : ∀ {R Γ A B} op (f : A → Obs Timeline Γ B) d n q ls (c : Ctx R Γ B) (o : St Γ A) a p
           → Inv ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩ → closed c ≡ false → Ok (Hots (env c)) p

  -- AN OUTER'S VALUE IN A COMPLETED SOURCE IS ABSORBED: the source owes
  -- nothing once its connect has seen it complete, so the value's row
  -- reaches no row above it.
  shut-begin : ∀ {R Γ A B} op (f : A → Obs Timeline Γ B) d n q ls (c : Ctx R Γ B) (o : St Γ A) a p → Shut c
             → Sim ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩ [] ⟨ c , flatS op f d n q o ls , absorbed , p ⟩

  -- A BOUNDED MERGE'S TWO READINGS, A VALUE'S LANE BEGUN WITH ROOM: none
  -- waiting, each later value's schedule reads one more lane begun.
  bounded-begin-at : ∀ {A B} m (L : A → Pos → EmissionSet B) {p O d n} Qu (Ls : List (EmissionSet B)) {a : A}
                   → (n <ᵇ m) ≡ true → Qu ≡ [] → After p O → Each (After p) Ls
                   → (∀ {k e} → L a (p ++ [ ix 1 ]) k e → (p ++ [ ix 1 ]) ≺ k) → (∀ {P} → Kth P (EndsOf Ls) n → ⊥)
                   → BeginAt (boundedP m L (Plus O p (out a)) d n Qu Ls) (boundedP m L O d (suc n) Qu (Ls ++ [ L a (p ++ [ ix 1 ]) ])) p a

  -- AN EXHAUST'S TWO READINGS, A VALUE'S LANE BEGUN WITH NONE RUNNING: the
  -- value runs, and each later value's run reads its lane begun.
  exhaust-begin-at : ∀ {A B} (L : A → Pos → EmissionSet B) {p O d n} (Ls : List (EmissionSet B)) {a : A}
                   → (n ≡ᵇ 0) ≡ true → After p O → Each (After p) Ls
                   → (∀ {k e} → L a (p ++ [ ix 1 ]) k e → (p ++ [ ix 1 ]) ≺ k) → (∀ {P} → Kth P (EndsOf Ls) n → ⊥)
                   → BeginAt (exhaustP L (Plus O p (out a)) d n Ls) (exhaustP L O d (suc n) (Ls ++ [ L a (p ++ [ ix 1 ]) ])) p a

  -- A BOUNDED MERGE'S OUTER VALUE, NO ROOM, WAITS.
  rise-bounded-wait : ∀ {R Γ A B} m f d n q ls (c : Ctx R Γ B) (o : St Γ A) a p → (n <ᵇ m) ≡ false
                    → Sim ⟨ inOuter (mergeᶠ (just m)) f d n q ls c , o , rising (nx a) , p ⟩ [] ⟨ c , flatS (mergeᶠ (just m)) f d n (q ++ [ a ]) o ls , absorbed , p ⟩

------------------------------------------------------------------------
-- Each joiner

t≢f : true ≡ false → ⊥
t≢f ()

shut : ∀ {R Γ A} (c : Ctx R Γ A) → UpO c → closed c ≡ true → Shut c
shut c u cl with closed-dead c cl
... | inj₁ dd = ⊥-elim (t≢f (trans (sym (upo-liv c u)) dd))
... | inj₂ sh = sh

no-room : ∀ {n m} → (n <ᵇ m) ≡ true → n ≡ m → ⊥
no-room {n} lt refl = <-irrefl refl (<ᵇ⇒< n n (subst T (sym lt) tt))

-- What a rising outer value's invariant gives the joiner.
module At {R Γ A B} (op : FlatOp) (f : A → Obs Timeline Γ B) (d : Bool) (n : ℕ) (q : List A) (ls : List (St Γ B)) (c : Ctx R Γ B) (o : St Γ A) (a : A) (p : Pos)
          (i : Inv ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩) where
  uc : UpO c
  uc = proj₁ (lead i)

  als : Each (After p) (rowsL (env c) ls)
  als = proj₁ (proj₁ (proj₂ (lead i)))

  lc : LeadC c p
  lc = proj₂ (proj₁ (proj₂ (lead i)))

  oo = proj₁ (proj₂ (proj₂ (lead i)))

  ao : After p (rows (env c) o)
  ao = proj₁ (proj₂ (proj₂ (proj₂ (lead i))))

  node : G (env c) true (flatS op f d n q o ls)
  node = subst (λ v → G (env c) v (flatS op f d n q o ls)) (upo-liv c uc) (node-good c (flatS op f d n q o ls) (good i) (λ ()) (λ ()))

-- A MERGE'S OUTER VALUE BEGINS ITS LANE.
rise-outer-nx : ∀ {R Γ A B} f d n q ls (c : Ctx R Γ B) (o : St Γ A) a p
              → Sim ⟨ inOuter (mergeᶠ nothing) f d n q ls c , o , rising (nx a) , p ⟩ [] (start c (mergeᶠ nothing) f d n q o ls a p)
rise-outer-nx f d n q ls c o a p i with closed c in cl
... | true  = shut-begin (mergeᶠ nothing) f d n q ls c o a p (shut c (At.uc (mergeᶠ nothing) f d n q ls c o a p i) cl) i
... | false with alive o in al
...   | false = ⊥-elim (open-alive o (At.oo (mergeᶠ nothing) f d n q ls c o a p i) al)
...   | true  =
  Begin.result (mergeᶠ nothing) f d n q o ls c a p (begin-good (mergeᶠ nothing) f d n q ls c o a p i cl (MergeG.fresh node)) uc lc
               (begin-ok (mergeᶠ nothing) f d n q ls c o a p i cl)
               (λ tp → merge-begin (λ x → pendRows (env c) (f x)) (rowsL (env c) ls) ao als tp (cap-of ls (MergeG.lanesG node) (MergeG.count node)))
  where open At (mergeᶠ nothing) f d n q ls c o a p i

-- A BOUNDED MERGE'S OUTER VALUE BEGINS ITS LANE WITH ROOM, ELSE WAITS.
rise-bounded-nx : ∀ {R Γ A B} m f d n q ls (c : Ctx R Γ B) (o : St Γ A) a p
                → Sim ⟨ inOuter (mergeᶠ (just m)) f d n q ls c , o , rising (nx a) , p ⟩ []
                      (if n <ᵇ m then start c (mergeᶠ (just m)) f d n q o ls a p
                                 else ⟨ c , flatS (mergeᶠ (just m)) f d n (q ++ [ a ]) o ls , absorbed , p ⟩)
rise-bounded-nx m f d n q ls c o a p i with n <ᵇ m in lt
... | false = rise-bounded-wait m f d n q ls c o a p lt i
... | true with closed c in cl
...   | true  = shut-begin (mergeᶠ (just m)) f d n q ls c o a p (shut c (At.uc (mergeᶠ (just m)) f d n q ls c o a p i) cl) i
...   | false with alive o in al
...     | false = ⊥-elim (open-alive o (At.oo (mergeᶠ (just m)) f d n q ls c o a p i) al)
...     | true  =
  Begin.result (mergeᶠ (just m)) f d n q o ls c a p (begin-good (mergeᶠ (just m)) f d n q ls c o a p i cl qz) uc lc
               (begin-ok (mergeᶠ (just m)) f d n q ls c o a p i cl)
               (λ tp → bounded-begin-at m (λ x → pendRows (env c) (f x)) q (rowsL (env c) ls) lt qz ao als tp
                                        (cap-of ls (MergeG.lanesG (proj₁ node)) (MergeG.count (proj₁ node))))
  where
    open At (mergeᶠ (just m)) f d n q ls c o a p i
    qz : q ≡ []
    qz = either (λ e → e) (λ e → ⊥-elim (no-room lt e)) (proj₂ node)

-- AN EXHAUST'S OUTER VALUE BEGINS ITS LANE WITH NONE RUNNING.
rise-exhaust-run : ∀ {R Γ A B} f d n q ls (c : Ctx R Γ B) (o : St Γ A) a p → (n ≡ᵇ 0) ≡ true
                 → Sim ⟨ inOuter exhaustᶠ f d n q ls c , o , rising (nx a) , p ⟩ [] (start c exhaustᶠ f d n q o ls a p)
rise-exhaust-run f d n q ls c o a p z i with closed c in cl
... | true  = shut-begin exhaustᶠ f d n q ls c o a p (shut c (At.uc exhaustᶠ f d n q ls c o a p i) cl) i
... | false with alive o in al
...   | false = ⊥-elim (open-alive o (At.oo exhaustᶠ f d n q ls c o a p i) al)
...   | true  =
  Begin.result exhaustᶠ f d n q o ls c a p (begin-good exhaustᶠ f d n q ls c o a p i cl (MergeG.fresh node)) uc lc
               (begin-ok exhaustᶠ f d n q ls c o a p i cl)
               (λ tp → exhaust-begin-at (λ x → pendRows (env c) (f x)) (rowsL (env c) ls) z ao als tp (cap-of ls (MergeG.lanesG node) (MergeG.count node)))
  where open At exhaustᶠ f d n q ls c o a p i
