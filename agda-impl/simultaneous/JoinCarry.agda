{-# OPTIONS --guardedness #-}

-- A JOINER CARRIES A JOINER when its outer's running values are paired
-- with the other's, value for value, and each lane is carried into its
-- partner's.  A lane row rides its lane's carrier; a lane's end, carried
-- end for end, is joined where its partner's is; a hand-off rides its
-- lane end's carrier one child down; the outer's end, paired end for end,
-- is joined where its partner's is.
module simultaneous.JoinCarry where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary using (¬_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

open import denotation.Position using (Pos; _≟ᵖ_; root; _⊕_; ix)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; Work; EmissionSet; Truncate; Few; Reach; Ended; _≺_; _≼_; module Joining)
open import denotation.Laws.Modulus using (≺-trans; ≺→≼; ≺-ext; reach-few)
open import denotation.Laws.Worlds using (_⊑_; _∪ʰ_; ⊕-injˡ; full)
open import denotation.Laws.Shows using (few-reach)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (Live; Shown; Match; Every; One; Reads)
open import simultaneous.Listing using (Listed)
open import simultaneous.ConnLists using (trunc-few)
open import denotation.Events using (Timeline; fresh)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.CarryBase using (PMap; _⊆ᴹ_; CarryAt; IntoAt; Near; Whole; From; InOrder; Home; Ahead; listed-≼)
open import simultaneous.SObs using (lone; module Elaborate)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

-- A row with no pin waits on every row before it.
unpin-few : ∀ {X : Set} {t : EmissionSet X} {k e} → Unpinned e → Reach t k e → Few t k
unpin-few {e = e} un r = reach-few {e = e} (full un) r

-- A position at or before its first child.
c≼ : ∀ c → c ≼ (c ⊕ [ ix 0 ])
c≼ c = ≺→≼ {c} {c ⊕ [ ix 0 ]} (≺-ext c [])

few-≺ : ∀ {X : Set} {t : EmissionSet X} {k k′} → Few t k → k′ ≺ k → Few t k′
few-≺ {k = k} {k′} (ks , h) kk = ks , λ {j} y jk → h y (≺-trans {j} {k′} {k} jk kk)

-- A row shown by nothing is no completion.
unshown-work : ∀ {Y : Set} {Sh : Y → Set} {e′ : Ev Y} → ¬ Shown Sh e′ → Work e′
unshown-work {e′ = out _} _ = tt
unshown-work {e′ = skip}  _ = tt
unshown-work {e′ = end}   n = n tt
unshown-work {e′ = pin _} _ = tt

-- A carrier of work is work.
match-work : ∀ {X Y : Set} {Sh : Y → Set} {Vl : X → Y → Set} {e : Ev X} {e′ : Ev Y} → Work e → Match Every Sh Vl e e′ → Work e′
match-work {e = out _} _ m with proj₁ m tt
... | _ , refl , _ = tt
match-work {e = skip}  _ (_ , n) = unshown-work (n (λ ()))
match-work {e = end}   () _
match-work {e = pin _} _ (_ , n) = unshown-work (n (λ ()))

-- A shown carrier's row is work, never a pin; one carried to an end, an end.
shown-unpin : ∀ {Y : Set} {Sh : Y → Set} {e : Ev Y} → Shown Sh e → Unpinned e
shown-unpin {e = out _} _ = tt
shown-unpin {e = skip}  ()
shown-unpin {e = end}   _ = tt
shown-unpin {e = pin _} ()

match-work⁻ : ∀ {X Y : Set} {Sh : Y → Set} {Vl : X → Y → Set} {e₀ : Ev X} {e : Ev Y} → Work e → Match Every Sh Vl e₀ e → Work e₀
match-work⁻ {e₀ = end}   w m = subst Work (proj₁ m tt) w
match-work⁻ {e₀ = out _} _ _ = tt
match-work⁻ {e₀ = skip}  _ _ = tt
match-work⁻ {e₀ = pin _} _ _ = tt

match-unpin⁻ : ∀ {X Y : Set} {Sh : Y → Set} {Vl : X → Y → Set} {e₀ : Ev X} {e : Ev Y} → Shown Sh e → Match Every Sh Vl e₀ e → Unpinned e₀
match-unpin⁻ {e₀ = pin _} sh (_ , n) = n (λ ()) sh
match-unpin⁻ {e₀ = out _} _ _ = tt
match-unpin⁻ {e₀ = skip}  _ _ = tt
match-unpin⁻ {e₀ = end}   _ _ = tt

end-match : ∀ {Y A : Set} {f : Y → List A} → Match {A} {Y} Every (One f) (Reads f) end end
end-match = (λ _ → refl) , λ n _ → n tt

skip-match : ∀ {Y A : Set} {f : Y → List A} → Match {A} {Y} Every (One f) (Reads f) skip skip
skip-match = (λ ()) , λ _ ()

-- A JOINER'S LANE ROWS, not its outer's.
module Lanes {A B : Set} (Ln : Pos → A → EmissionSet B) (o : EmissionSet A) (Runs : Pos → Set) (Cut : Pos → Pos → Set) (Hand : Pos → Set) where
  module J = Joining Ln o (λ _ _ → ⊥) (Ended o) Runs Cut Hand

  t : EmissionSet B
  t = Truncate J.JoinT

  Bod : ∀ {k e} → J.JoinT k e → Set
  Bod (J.val _)     = ⊥
  Bod (J.step _)    = ⊥
  Bod (J.opin _)    = ⊥
  Bod (J.opass _ _) = ⊥
  Bod _             = ⊤

  tB : EmissionSet B
  tB k e = Σ (t k e) λ x → Bod (proj₁ x)

-- The plain joiner over `Ln`, the elaborated over `Ln*`; `V q a q*`
-- pairs the plain running value `a` at `q` with the elaborated at `q*`,
-- whose lane carries the plain one's along its own map, part of `N`;
-- `E c c*` pairs the outer's end with the other's.
module Joined {A B : Set} {HP HE LP : Pos → Set} (p p′ : Pos)
              (o : EmissionSet A) (Ln : Pos → A → EmissionSet B) (Runs : Pos → Set) (Cut : Pos → Pos → Set) (Hand : Pos → Set)
              (o* : EmissionSet A) (Ln* : Pos → A → EmissionSet (IE B)) (Runs* : Pos → Set) (Cut* : Pos → Pos → Set) (Hand* : Pos → Set)
              (V : Pos → A → Pos → Set)
              (v-at : ∀ {q a q*} → V q a q* → o q (out a) × Runs q × o* q* (out a) × Runs* q*)
              (N : PMap) (LM : ∀ {q a q*} → V q a q* → PMap) (lm-sub : ∀ {q a q*} (v : V q a q*) → LM v ⊆ᴹ N)
              (lc : ∀ {q a q*} (v : V q a q*) → Σ Pos λ s → Σ Pos λ s* → CarryAt valuesOf (LM v) HP HE LP (Ln q a) (Ln* q* a) s s*)
              (E : Pos → Pos → Set)
              -- THE PLAIN JOINER'S PARTS: a lane runs past its value, cut
              -- for good once cut; its rows precede its end and, under the
              -- environment's listing, are listed wherever few precede; the
              -- environment's listing is closed downward.
              (lane-after : ∀ {q a k e} → Ln q a k e → q ≺ k)
              (cut↑ : ∀ {q k k′} → Cut q k′ → k′ ≺ k → Cut q k)
              (lane-live : ∀ {q a k e} → o q (out a) → Runs q → Ln q a k e → Unpinned e → Live (Ln q a) k)
              (lane-listing : ∀ {q a k} → o q (out a) → Runs q → Few (Ln q a) k → LP k → Listed (Ln q a) k)
              (lp↓ : ∀ {x y} → x ≼ y → LP y → LP x)
              (lane-live* : ∀ {q a l e} → o* q (out a) → Runs* q → Ln* q a l e → Unpinned e → Live (Ln* q a) l)
              (cut↑* : ∀ {q l l′} → Cut* q l′ → l′ ≺ l → Cut* q l)
              -- Two lanes' rows lie apart: one row is one lane's, imaged
              -- once; nor is a hand-off or the outer's end a lane's row.
              (img-apart : ∀ {q a q* q′ a′ q*′} (v : V q a q*) (v′ : V q′ a′ q*′) {k l l′}
                         → CarryAt.Img (proj₂ (proj₂ (lc v))) k l → CarryAt.Img (proj₂ (proj₂ (lc v′))) k l′ → l ≡ l′)
              (pb-apart : ∀ {q a q* q′ a′ q*′} (v : V q a q*) (v′ : V q′ a′ q*′) {k l l′}
                        → CarryAt.PB (proj₂ (proj₂ (lc v))) k l → CarryAt.Img (proj₂ (proj₂ (lc v′))) k l′ → ⊥)
              (hand-apart : ∀ {q a q* q′ a′ q*′} (v : V q a q*) (v′ : V q′ a′ q*′) {c c* l}
                          → CarryAt.Img (proj₂ (proj₂ (lc v))) c c* → Ln q a c end → Hand c
                          → CarryAt.Img (proj₂ (proj₂ (lc v′))) (c ⊕ [ ix 0 ]) l ⊎ CarryAt.PB (proj₂ (proj₂ (lc v′))) (c ⊕ [ ix 0 ]) l ⊎ E (c ⊕ [ ix 0 ]) l → ⊥)
              (end-apart : ∀ {q a q*} (v : V q a q*) {c l l′} → E c l → CarryAt.Img (proj₂ (proj₂ (lc v))) c l′ ⊎ CarryAt.PB (proj₂ (proj₂ (lc v))) c l′ → ⊥)
              -- THE PAIRED JOINERS AGREE: every running value is paired, a
              -- lane is cut where its partner is, and its end is joined, and
              -- handed off, where its partner's is; so is the outer's end.
              -- Read forward, a decision needs the plain run listed; read
              -- back, a plain decision is held classically, since it reads
              -- every plain value's partner.
              (paired : ∀ {q a} → o q (out a) → Runs q → Listed o q → LP q → Σ Pos (V q a))
              (paired⁻ : ∀ {q* a l e} → o* q* (out a) → Runs* q* → Ln* q* a l e
                       → Live (Truncate (Joining.JoinT Ln* o* (λ _ _ → ⊥) (Ended o*) Runs* Cut* Hand*)) l
                       → Few (Truncate (Joining.JoinT Ln* o* (λ _ _ → ⊥) (Ended o*) Runs* Cut* Hand*)) l → Σ Pos λ q → V q a q*)
              (cut-from : ∀ {q a q*} (v : V q a q*) {k l} → CarryAt.Img (proj₂ (proj₂ (lc v))) k l → Cut* q* l → Cut q k)
              (cut-to¬¬ : ∀ {q a q*} (v : V q a q*) {k l} → CarryAt.Img (proj₂ (proj₂ (lc v))) k l → Cut q k → ¬ ¬ Cut* q* l)
              (done-to : ∀ {q a q*} (v : V q a q*) {c c*} → CarryAt.Img (proj₂ (proj₂ (lc v))) c c* → Ln q a c end → Listed o c × LP c
                       → Joining.Done Ln o (λ _ _ → ⊥) (Ended o) Runs Cut Hand c → Joining.Done Ln* o* (λ _ _ → ⊥) (Ended o*) Runs* Cut* Hand* c*)
              (done-from¬¬ : ∀ {q a q*} (v : V q a q*) {c c*} → CarryAt.Img (proj₂ (proj₂ (lc v))) c c* → Ln q a c end
                           → Joining.Done Ln* o* (λ _ _ → ⊥) (Ended o*) Runs* Cut* Hand* c* → ¬ ¬ Joining.Done Ln o (λ _ _ → ⊥) (Ended o) Runs Cut Hand c)
              (hand-from : ∀ {q a q*} (v : V q a q*) {c c*} → CarryAt.Img (proj₂ (proj₂ (lc v))) c c* → Ln q a c end → Hand* c* → Hand c)
              (hand-to : ∀ {q a q*} (v : V q a q*) {c c*} → CarryAt.Img (proj₂ (proj₂ (lc v))) c c* → Ln q a c end → Listed o c × LP c → Hand c → Hand* c*)
              (hand-to¬¬ : ∀ {q a q*} (v : V q a q*) {c c*} → CarryAt.Img (proj₂ (proj₂ (lc v))) c c* → Ln q a c end → Hand c → ¬ ¬ Hand* c*)
              (hand-ext : ∀ {q a q*} (v : V q a q*) {c c*} → CarryAt.Img (proj₂ (proj₂ (lc v))) c c* → Ln q a c end → Hand c
                        → Σ Pos λ y → N (c ⊕ [ ix 0 ]) y × y ⊑ (c* ⊕ [ ix 0 ]))
              (ends : ∀ {c} → o c end → Listed o c → LP c → Σ Pos (E c))
              (ends⁻ : ∀ {c*} → o* c* end → Few (Truncate (Joining.JoinT Ln* o* (λ _ _ → ⊥) (Ended o*) Runs* Cut* Hand*)) c* → Σ Pos λ c → E c c*)
              (e-at : ∀ {c c*} → E c c* → o c end × o* c* end)
              (e-fun : ∀ {c c* c*′} → E c c* → E c c*′ → c* ≡ c*′)
              (end-to : ∀ {c c*} → E c c* → Listed o c × LP c
                      → Joining.Done Ln o (λ _ _ → ⊥) (Ended o) Runs Cut Hand c → Joining.Done Ln* o* (λ _ _ → ⊥) (Ended o*) Runs* Cut* Hand* c*)
              (end-from¬¬ : ∀ {c c*} → E c c* → Joining.Done Ln* o* (λ _ _ → ⊥) (Ended o*) Runs* Cut* Hand* c* → ¬ ¬ Joining.Done Ln o (λ _ _ → ⊥) (Ended o) Runs Cut Hand c)
              (e-ext : ∀ {c c*} → E c c* → Σ Pos λ y → N c y × y ⊑ c*) where
  open Lanes Ln o Runs Cut Hand public
  module J* = Joining Ln* o* (λ _ _ → ⊥) (Ended o*) Runs* Cut* Hand*

  u : EmissionSet (IE B)
  u = Truncate J*.JoinT

  -- Each value's lane carry.
  module L {q a q*} (v : V q a q*) = CarryAt (proj₂ (proj₂ (lc v)))

  -- A JOINED ROW AND ITS CARRIER: a lane row on its lane's carrier; a
  -- hand-off one child under its lane end's; a lane's end read back on
  -- its lane's carrier, and the outer's on its partner, each joined end
  -- held classically.
  data LaneImg (k l : Pos) : Set where
    row : ∀ {q a q* e₀} (v : V q a q*) → L.Img v k l → tB k e₀ → Unpinned e₀ → ¬ Cut q k → LaneImg k l
    hnd : ∀ {q a q* c c*} (v : V q a q*) → L.Img v c c* → Ln q a c end → ¬ Cut q c → Hand c
        → k ≡ c ⊕ [ ix 0 ] → l ≡ c* ⊕ [ ix 0 ] → tB k skip → LaneImg k l
    lnd : ∀ {q a q*} (v : V q a q*) → L.Img v k l → Few J.JoinT k → ¬ ¬ tB k end → LaneImg k l
    fin : E k l → Few J.JoinT k → ¬ ¬ tB k end → LaneImg k l

  -- A lane row carried into its instant, by its lane.
  LanePB : Pos → Pos → Set
  LanePB k l = Σ Pos λ q → Σ A λ a → Σ Pos λ q* → Σ (V q a q*) λ v → L.PB v k l × Σ (Ev B) (tB k) × Σ (Ev (IE B)) (u l)

  LP′ : Pos → Set
  LP′ q = Listed o q × LP q

  img-few : ∀ {k l} → LaneImg k l → Few J.JoinT k
  img-few (row {e₀ = e₀} _ _ ((_ , rc) , _) un _) = unpin-few {e = e₀} un rc
  img-few (hnd _ _ _ _ _ _ _ ((_ , rc) , _))     = unpin-few {e = skip} tt rc
  img-few (lnd _ _ F _)                          = F
  img-few (fin _ F _)                            = F

  lane-ext : ∀ {q a q* k l} (v : V q a q*) → L.Img v k l → Σ Pos λ y → N k y × y ⊑ l
  lane-ext v i with L.ext v i
  ... | y , m , yl = y , lm-sub v m , yl

  ext : ∀ {k l} → LaneImg k l → Σ Pos λ y → N k y × y ⊑ l
  ext (row v i _ _ _) = lane-ext v i
  ext (hnd v i y _ h refl refl _) = hand-ext v i y h
  ext (lnd v i _ _) = lane-ext v i
  ext (fin ε _ _) = e-ext ε

  few : ∀ {k l} → LaneImg k l → Few tB k
  few i = let (ks , h) = trunc-few (img-few i) in ks , λ y kq → h (proj₁ y) kq

  -- THE JOINED LANES' FIELDS: each a lane's own, the lanes lying apart,
  -- a lane's end joined as its partner's is.
  postulate
    join-pb-few  : ∀ {l e} → u l e → Σ (List Pos) λ ks → ∀ {k} → LanePB k l → k ∈ ks
    join-pb-past : ∀ {k l e₀ e x y} → LanePB k l → tB k e₀ → (Unpinned e₀ → Live tB k) → u l e → N x y → x ≺ k → ¬ (x ⊑ k) → Ahead y l
    join-img¬¬   : ∀ {k e} → tB k e → Unpinned e → Live tB k → Few tB k
                 → ¬ ¬ ((Σ Pos λ l → LaneImg k l × Σ (Ev (IE B)) λ e′ → u l e′ × Match Every (One valuesOf) (Reads valuesOf) e e′) ⊎ e ≡ skip)
    join-place   : ∀ {m e} → u m e → Live u m → Listed u m
                 → instantOf m ≡ instantOf p′ ⊎ (Σ Pos λ k → Σ Pos λ l → LaneImg k l × instantOf l ≡ instantOf m × Near u m l)
                   ⊎ Σ Pos λ h → HE h × instantOf h ≡ instantOf m
    join-live    : ∀ {k l} → LaneImg k l → Live tB k → Live u l
    join-whole   : Whole tB → (∀ {c} → tB c end → ⊥) → (∀ {q} → LP′ q) → Whole u
    join-cover   : ∀ {v w} → Listed tB v → LP′ v → Live tB v → From LaneImg LanePB tB u v w → Listed u w
    join-bk      : Σ (Pos → List Pos) λ bk → ∀ {k l} → LaneImg k l → k ∈ bk l
    join-pinned  : ∀ {k r} → tB k (pin r) → Live tB k → Listed tB k → LP′ k
                 → InOrder LaneImg LanePB tB u k
                   × (instantOf k ≡ instantOf p ⊎ (Σ Pos λ k₀ → k₀ ≺ r × Home tB k₀ × instantOf k₀ ≡ instantOf k)
                      ⊎ Σ Pos λ h → (HP ∪ʰ o) h × instantOf h ≡ instantOf k)
    -- A joined row's carrier has few joined rows before it, and comes no
    -- later than the carrier of any later row.
    img-reach    : ∀ {k l} → LaneImg k l → Few J*.JoinT l
    -- and back: a carried row has few plain rows before it.
    back-reach   : ∀ {q a q* k l} (v : V q a q*) → L.Img v k l → Few J*.JoinT l → Few J.JoinT k
    end-reach⁻   : ∀ {c c*} → E c c* → Few J*.JoinT c* → Few J.JoinT c
    join-from    : ∀ {k l} → LaneImg k l → From LaneImg LanePB tB u k l
    -- A lane row carried into its lane's instant is carried into the
    -- joiner's.
    into-lift    : ∀ {q a q* k} (v : V q a q*) → o q (out a) → Runs q → tB k skip → ¬ Cut q k → Listed tB k → LP′ k
                 → IntoAt (L.Img v) (Ln* q* a) (L.PB v) HP (proj₁ (lc v)) k → IntoAt LaneImg u LanePB (HP ∪ʰ o) p k

  img-row : ∀ {k l} → LaneImg k l → ¬ ¬ Σ (Ev B) λ e → tB k e × Unpinned e
  img-row (row _ _ x un _) n = n (_ , x , un)
  img-row (hnd _ _ _ _ _ _ _ x) n = n (_ , x , tt)
  img-row (lnd _ _ _ nn) n = nn λ x → n (end , x , tt)
  img-row (fin _ _ nn) n = nn λ x → n (end , x , tt)

  -- A lane's carrier, whether its row is read forward or its end back.
  LaneOn : Pos → Pos → Set
  LaneOn k l = Σ Pos λ q → Σ A λ a → Σ Pos λ q* → Σ (V q a q*) λ v → L.Img v k l

  on-lane : ∀ {k l} → LaneImg k l → LaneOn k l ⊎ ((Σ Pos λ q → Σ A λ a → Σ Pos λ q* → Σ (V q a q*) λ v → Σ Pos λ c → Σ Pos λ c*
                                                   → L.Img v c c* × Ln q a c end × Hand c × k ≡ c ⊕ [ ix 0 ] × l ≡ c* ⊕ [ ix 0 ]) ⊎ E k l)
  on-lane (row v i _ _ _) = inj₁ (_ , _ , _ , v , i)
  on-lane (lnd v i _ _) = inj₁ (_ , _ , _ , v , i)
  on-lane (hnd v i y _ h kc lc′ _) = inj₂ (inj₁ (_ , _ , _ , v , _ , _ , i , y , h , kc , lc′))
  on-lane (fin ε _ _) = inj₂ (inj₂ ε)

  img-fun : ∀ {k l l′} → LaneImg k l → LaneImg k l′ → l ≡ l′
  img-fun i i′ with on-lane i | on-lane i′
  ... | inj₁ (_ , _ , _ , v , j) | inj₁ (_ , _ , _ , v′ , j′) = img-apart v v′ j j′
  ... | inj₁ (_ , _ , _ , v , j) | inj₂ (inj₁ (_ , _ , _ , v′ , _ , _ , j′ , y′ , h′ , refl , _)) = ⊥-elim (hand-apart v′ v j′ y′ h′ (inj₁ j))
  ... | inj₁ (_ , _ , _ , v , j) | inj₂ (inj₂ ε) = ⊥-elim (end-apart v ε (inj₁ j))
  ... | inj₂ (inj₁ (_ , _ , _ , v , _ , _ , j , y , h , refl , _)) | inj₁ (_ , _ , _ , v′ , j′) = ⊥-elim (hand-apart v v′ j y h (inj₁ j′))
  ... | inj₂ (inj₁ (_ , _ , _ , v , c , _ , j , _ , _ , refl , refl)) | inj₂ (inj₁ (_ , _ , _ , v′ , c′ , _ , j′ , _ , _ , cc , refl)) with ⊕-injˡ c c′ cc
  ...   | refl = cong (_⊕ [ ix 0 ]) (img-apart v v′ j j′)
  img-fun i i′ | inj₂ (inj₁ (_ , _ , _ , v , _ , _ , j , y , h , refl , _)) | inj₂ (inj₂ ε) = ⊥-elim (hand-apart v v j y h (inj₂ (inj₂ ε)))
  img-fun i i′ | inj₂ (inj₂ ε) | inj₁ (_ , _ , _ , v′ , j′) = ⊥-elim (end-apart v′ ε (inj₁ j′))
  img-fun i i′ | inj₂ (inj₂ ε) | inj₂ (inj₁ (_ , _ , _ , v′ , _ , _ , j′ , y′ , h′ , refl , _)) = ⊥-elim (hand-apart v′ v′ j′ y′ h′ (inj₂ (inj₂ ε)))
  img-fun i i′ | inj₂ (inj₂ ε) | inj₂ (inj₂ ε′) = e-fun ε ε′

  pb-img : ∀ {k l l′} → LanePB k l → LaneImg k l′ → ⊥
  pb-img (_ , _ , _ , v , pb , _) i with on-lane i
  ... | inj₁ (_ , _ , _ , v′ , j) = pb-apart v v′ pb j
  ... | inj₂ (inj₁ (_ , _ , _ , v′ , _ , _ , j′ , y′ , h′ , refl , _)) = hand-apart v′ v j′ y′ h′ (inj₂ (inj₁ pb))
  ... | inj₂ (inj₂ ε) = end-apart v ε (inj₂ pb)

  -- A LANE ROW READ BY ITS LANE: its value paired through the outer's
  -- listing, its own rows listed as the joiner's are, the lane's carry
  -- placing it.
  lane-few : ∀ {q a k e} → o q (out a) → Runs q → Ln q a k e → Unpinned e → ¬ Cut q k → Few J.JoinT k → Few tB k → Few (Ln q a) k
  lane-few {q} {a} {k} x r y un nc F (ks , h) = ks , at
    where
      at : ∀ {k′ e′} → Ln q a k′ e′ → k′ ≺ k → k′ ∈ ks
      at {e′ = end}   y′ kk = ⊥-elim (lane-live x r y un y′ kk)
      at {k′} {out b} y′ kk = h {k′} {out b} ((J.lane x r y′ (λ c → nc (cut↑ c kk)) tt , few-reach {e = out b} (few-≺ F kk)) , tt) kk
      at {k′} {skip}  y′ kk = h {k′} {skip} ((J.lane x r y′ (λ c → nc (cut↑ c kk)) tt , few-reach {e = skip} (few-≺ F kk)) , tt) kk
      at {k′} {pin w} y′ kk = h {k′} {pin w} ((J.lane x r y′ (λ c → nc (cut↑ c kk)) tt , few-reach {e = pin w} (few-≺ F kk)) , tt) kk

  LaneRead : ∀ {q a} → Pos → Pos → Ev B → Set
  LaneRead {q} {a} k q* e = Σ (V q a q*) λ v →
      (Σ Pos λ l → L.Img v k l × Σ (Ev (IE B)) λ e′ → Ln* q* a l e′ × Listed (Ln* q* a) l × Match Every (One valuesOf) (Reads valuesOf) e e′)
    ⊎ (e ≡ skip × IntoAt (L.Img v) (Ln* q* a) (L.PB v) HP (proj₁ (lc v)) k)

  lane-read : ∀ {q a k e} → o q (out a) → Runs q → Ln q a k e → Unpinned e → ¬ Cut q k → Few J.JoinT k → Listed tB k → LP′ k
            → Σ Pos λ q* → LaneRead {q} {a} k q* e
  lane-read {q} {a} {k} x r y un nc F ls (lo , lp) =
    let qk = ≺→≼ {q} {k} (lane-after y)
        (q* , v) = paired x r (listed-≼ lo qk) (lp↓ qk lp)
    in q* , v , L.img v y un (lane-live x r y un) (lane-listing x r (lane-few x r y un nc F (proj₁ ls , proj₁ (proj₂ ls))) lp) lp

  -- The joined row on the carrier, listed from the carrier on.
  JoinedAt : Pos → Ev B → Set
  JoinedAt k e = (Σ Pos λ l → LaneImg k l × Σ (Ev (IE B)) λ e′ → u l e′ × Listed u l × Match Every (One valuesOf) (Reads valuesOf) e e′)
                 ⊎ (e ≡ skip × IntoAt LaneImg u LanePB (HP ∪ʰ o) p k)

  joined : ∀ {k l e e′} → Live tB k → Listed tB k → LP′ k → LaneImg k l → J*.JoinT l e′ → Match Every (One valuesOf) (Reads valuesOf) e e′ → JoinedAt k e
  joined lv ls lp i y m = inj₁ (_ , i , _ , (y , few-reach (img-reach i)) , join-cover ls lp lv (join-from i) , m)

  join-img : ∀ {k e} → tB k e → Unpinned e → Live tB k → Listed tB k → LP′ k → JoinedAt k e
  join-img ((J.val _ , _) , ())
  join-img ((J.step _ , _) , ())
  join-img ((J.opin _ , _) , ())
  join-img ((J.opass _ _ , _) , ())
  join-img ((J.run () _ , _) , _)
  join-img ((J.rend () _ _ , _) , _)
  join-img ((J.rpass () _ _ , _) , _)
  join-img ((J.rhand () _ , _) , _)
  join-img ((J.left _ _ _ _ _ , _) , _) ()
  join-img {e = e} b@((J.lane x r y nc w , rc) , _) un lv ls lp with lane-read x r y un nc (unpin-few {e = e} un rc) ls lp
  ... | q* , v , inj₁ (l , i , e′ , y* , _ , m) =
    let (_ , _ , x* , r*) = v-at v
    in joined lv ls lp (row v i b un nc) (J*.lane x* r* y* (λ c* → nc (cut-from v i c*)) (match-work w m)) m
  ... | q* , v , inj₂ (refl , into) = inj₂ (refl , into-lift v x r b nc ls lp into)
  join-img b@((J.lend x r y nc nh d , rc) , _) un lv ls lp with lane-read x r y tt nc (unpin-few {e = end} un rc) ls lp
  ... | q* , v , inj₁ (l , i , e′ , y* , _ , m) with proj₁ m tt
  ...   | refl =
    let (_ , _ , x* , r*) = v-at v
    in joined lv ls lp (row v i b tt nc)
         (J*.lend x* r* y* (λ c* → nc (cut-from v i c*)) (λ h* → nh (hand-from v i y h*)) (done-to v i y lp d)) (end-match {f = valuesOf})
  join-img ((J.lend x r y nc nh d , rc) , _) un lv ls lp | q* , v , inj₂ (() , _)
  join-img b@((J.lpass x r y nc nh nd , rc) , _) un lv ls lp with lane-read x r y tt nc (unpin-few {e = skip} un rc) ls lp
  ... | q* , v , inj₁ (l , i , e′ , y* , _ , m) with proj₁ m tt
  ...   | refl =
    let (_ , _ , x* , r*) = v-at v
    in joined lv ls lp (row v i b tt nc)
         (J*.lpass x* r* y* (λ c* → nc (cut-from v i c*)) (λ h* → nh (hand-from v i y h*)) (λ d* → done-from¬¬ v i y d* nd))
         (skip-match {IE B} {B} {valuesOf})
  join-img ((J.lpass x r y nc nh nd , rc) , _) un lv ls lp | q* , v , inj₂ (() , _)
  join-img b@((J.hand {c = c} x r y nc h , rc) , _) un lv ls (lo , lp)
    with lane-read x r y tt nc (few-≺ (unpin-few {e = skip} un rc) (≺-ext c [])) (listed-≼ ls (c≼ c)) (listed-≼ lo (c≼ c) , lp↓ (c≼ c) lp)
  ... | q* , v , inj₁ (l , i , e′ , y* , _ , m) with proj₁ m tt
  ...   | refl =
    let (_ , _ , x* , r*) = v-at v
    in joined lv ls (lo , lp) (hnd v i y nc h refl refl b)
         (J*.hand x* r* y* (λ c* → nc (cut-from v i c*)) (hand-to v i y (listed-≼ lo (c≼ c) , lp↓ (c≼ c) lp) h)) (skip-match {IE B} {B} {valuesOf})
  join-img ((J.hand x r y nc h , rc) , _) un lv ls (lo , lp) | q* , v , inj₂ (() , _)
  join-img b@((J.oend xc d , rc) , _) un lv ls (lo , lp) with ends xc lo lp
  ... | c* , ε = joined lv ls (lo , lp) (fin ε (unpin-few {e = end} tt rc) (λ n → n b)) (J*.oend (proj₂ (e-at ε)) (end-to ε (lo , lp) d)) (end-match {f = valuesOf})

  -- A SHOWN ROW READ BACK: its lane's value paired back, the lane's own
  -- carry finding the plain row; the outer's end paired back.
  lane-few* : ∀ {q* a l e} → o* q* (out a) → Runs* q* → Ln* q* a l e → Unpinned e → ¬ Cut* q* l → Few J*.JoinT l → Few u l → Few (Ln* q* a) l
  lane-few* {q*} {a} {l} x r y un nc F (ks , h) = ks , at
    where
      at : ∀ {l′ e′} → Ln* q* a l′ e′ → l′ ≺ l → l′ ∈ ks
      at {e′ = end}   y′ ll = ⊥-elim (lane-live* x r y un y′ ll)
      at {l′} {out b} y′ ll = h {l′} {out b} (J*.lane x r y′ (λ c → nc (cut↑* c ll)) tt , few-reach {e = out b} (few-≺ F ll)) ll
      at {l′} {skip}  y′ ll = h {l′} {skip} (J*.lane x r y′ (λ c → nc (cut↑* c ll)) tt , few-reach {e = skip} (few-≺ F ll)) ll
      at {l′} {pin w} y′ ll = h {l′} {pin w} (J*.lane x r y′ (λ c → nc (cut↑* c ll)) tt , few-reach {e = pin w} (few-≺ F ll)) ll

  ShownAt : Pos → Ev (IE B) → Set
  ShownAt l e = Σ Pos λ k → LaneImg k l × Σ (Ev B) λ e₀ → tB k e₀ × Match Every (One valuesOf) (Reads valuesOf) e₀ e

  join-shown : ∀ {l e} → u l e → Shown (One valuesOf) e → Work e → Live u l → Few u l → ShownAt l e
  join-shown (J*.val _ , _) ()
  join-shown (J*.step _ , _) ()
  join-shown (J*.opin _ , _) ()
  join-shown (J*.opass _ _ , _) ()
  join-shown (J*.lpass _ _ _ _ _ _ , _) ()
  join-shown (J*.hand _ _ _ _ _ , _) ()
  join-shown (J*.left _ _ _ _ _ , _) ()
  join-shown (J*.run () _ , _) _
  join-shown (J*.rend () _ _ , _) _
  join-shown (J*.rpass () _ _ , _) _
  join-shown (J*.rhand () _ , _) _
  join-shown (J*.lend _ _ _ _ _ _ , _) _ ()
  join-shown (J*.oend _ _ , _) _ ()
  join-shown {e = e} (J*.lane x* r* y* nc* w , rc) sh _ lv F =
    let un = shown-unpin sh
        F* = unpin-few {e = e} un rc
        (q , v) = paired⁻ x* r* y* lv F
        (x , r , _ , _) = v-at v
        (k , i , e₀ , y₀ , m) = L.shown v y* sh w (lane-live* x* r* y* un) (lane-few* x* r* y* un nc* F* F)
        nc = λ c → cut-to¬¬ v i c nc*
        b = (J.lane x r y₀ nc (match-work⁻ w m) , few-reach {e = e₀} (back-reach v i F*)) , tt
    in k , row v i b (match-unpin⁻ sh m) nc , e₀ , b , m

  -- AN END READ BACK, its plain end held classically: a lane's through
  -- its lane's carry, its decisions read back; the outer's paired back.
  join-shown-end : ∀ {l} → u l end → Live u l → Few u l → Σ Pos λ k → LaneImg k l × ¬ ¬ tB k end
  join-shown-end (J*.lane _ _ _ _ () , _) _ _
  join-shown-end (J*.run () _ , _) _ _
  join-shown-end (J*.rend () _ _ , _) _ _
  join-shown-end (J*.lend x* r* y* nc* nh* d* , rc) lv F =
    let F* = unpin-few {e = end} tt rc
        (q , v) = paired⁻ x* r* y* lv F
        (x , r , _ , _) = v-at v
        (k , i , nn) = L.shown-end v y* (lane-live* x* r* y* tt) (lane-few* x* r* y* tt nc* F* F)
        Fk = back-reach v i F*
        held : ¬ ¬ tB k end
        held n = nn λ y₀ → done-from¬¬ v i y₀ d* λ d →
                   n ((J.lend x r y₀ (λ c → cut-to¬¬ v i c nc*) (λ h → hand-to¬¬ v i y₀ h nh*) d , few-reach {e = end} Fk) , tt)
    in k , lnd v i Fk held , held
  join-shown-end (J*.oend x* d* , rc) lv F =
    let (c , ε) = ends⁻ x* F
        Fc = end-reach⁻ ε (unpin-few {e = end} tt rc)
        held : ¬ ¬ tB c end
        held n = end-from¬¬ ε d* λ d → n ((J.oend (proj₁ (e-at ε)) d , few-reach {e = end} Fc) , tt)
    in c , fin ε Fc held , held

  -- A lane row carried into its instant may lie in its value's: the
  -- outer's rows stand with the environment's hots, its echo carrying
  -- them once the joiner sits under its outer's connect.
  carried : CarryAt valuesOf N (HP ∪ʰ o) HE LP′ tB u p p′
  carried = record
    { Img = LaneImg ; ext = ext ; PB = LanePB ; pb-few = join-pb-few ; pb-img = pb-img ; pb-past = join-pb-past
    ; img = join-img ; img¬¬ = join-img¬¬ ; shown = join-shown ; shown-end = join-shown-end ; img-row = img-row ; img-fun = img-fun
    ; place = join-place ; live = join-live ; few = few ; whole = join-whole ; cover = join-cover ; bk = proj₁ join-bk
    ; in-bk = proj₂ join-bk ; pinned = join-pinned }
