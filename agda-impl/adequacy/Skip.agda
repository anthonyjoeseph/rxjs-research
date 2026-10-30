{-# OPTIONS --guardedness #-}

-- THE ROWS BUT FOR A SKIP AT THE FOCUS: two holes owing the same rows
-- but for skips at `p`, read up a context whose other parts lie past
-- `p`, owe the same rows at the root but for skips at `p`.  A merge's end
-- waits on every part's rows, and a row at `p` lies by any end at or past
-- `p`, so where the two disagree no end reads them differently.
module adequacy.Skip where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _ʳ++_; _++_; [_])
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (¬_)
open import adequacy.Up using (all-ʳ++; _⇔ᴾ_; Like; like; Policy; JoinP; Reads; reads-sym; done-reads; flatP; switchP; exhaustP; boundedP;
  flat-reads; switch-reads; exhaust-reads; bounded-reads; kill-like; waits-like)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; ix; last)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; end; _≺_; _≼_; Truncate; Reach; Dep; MapT; map-out; map-skip;
  map-pin; map-end; module Joining; module Values; module Connecting; module Scan;
  module TakeWhile)
open import denotation.Laws.Modulus using (≺-trans; ≺→≼; ≼-≺-≺; ≺-ext)
open import operation.PureObservable using (module Machine)
open Machine using (Owe; free; cpAt; cutAt; overAt; Ctx; St; CS; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (TakeR; Kept; kept; Stops; stop; left; acc-val; up; env; rows; rowsL; pendRows; Lane; reads;
  From; Lanes; Each; Kth; EndsOf; module Flat; module BoundedF; module SwitchF;
  module ExhaustF; _≃_; _⇄_; Vis; Hot; ∅)

------------------------------------------------------------------------
-- Rows past a position

-- Every row strictly past `p`.
After : ∀ {A} → Pos → EmissionSet A → Set
After p t = ∀ {q e} → t q e → p ≺ q

-- Every row at or past `p`.
Since : ∀ {A} → Pos → EmissionSet A → Set
Since p t = ∀ {q e} → t q e → p ≼ q

-- A take that has failed ends where the failing value stops it.
LeadT : Owe → Pos → Set
LeadT (cpAt p₀) p = p ≼ (p₀ ++ [ last ])
LeadT _         p = ⊤

-- What a rising event at `p` is owed past: frame by frame, every other
-- part of a merge or a connect it rises through.  Up a source, the
-- body's own rows: those it is not yet fed of the source's.
LeadC : ∀ {R Γ A} → Ctx R Γ A → Pos → Set
LeadC (inMap f c)                                    p = LeadC c p
LeadC (inScan f z c)                                 p = LeadC c p
LeadC (inCut l a c)                                  p = LeadC c p
LeadC (inLn b c)                                     p = LeadC c p
LeadC (inTake i q w c)                               p = LeadT w p × LeadC c p
LeadC (inOuter op f d n q ls c)                      p = Each (After p) (rowsL (env c) ls) × LeadC c p
LeadC (inLanes op f d n q o pre post c)              p =
  After p (rows (env c) o) × Each (After p) (rowsL (env c) pre) × Each (After p) (rowsL (env c) post) × LeadC c p
LeadC (inSrc k b c)                                  p = After p (rows (Hot ∅ k ∷ᴬ env c) b) × LeadC c p
LeadC (inBody k o c)                                 p = After p (rows (env c) o) × LeadC c p
LeadC _                                              p = ⊤

after-since : ∀ {B} {p} (Ls : List (EmissionSet B)) → Each (After p) Ls → Each (Since p) Ls
after-since []       _        = _
after-since {p = p} (_ ∷ Ls) (a , as) = (λ {q} {e} r → ≺→≼ {p} {q} (a {q} {e} r)) , after-since Ls as

since-lanes : ∀ {B} {p} (Ls : List (EmissionSet B)) → Each (Since p) Ls → Since p (Lanes Ls)
since-lanes (_ ∷ _)  (s , _)  {q} {e} (inj₁ r) = s {q} {e} r
since-lanes (_ ∷ Ls) (_ , ss) {q} {e} (inj₂ x) = since-lanes Ls ss {q} {e} x

------------------------------------------------------------------------
-- The relation

Skip : ∀ {A} → Pos → Pos → Ev A → Set
Skip p q e = q ≡ p × e ≡ skip

record _≈⟨_⟩_ {A : Set} (t : EmissionSet A) (p : Pos) (u : EmissionSet A) : Set where
  constructor _⇆_
  field
    fwd : ∀ {q e} → t q e → u q e ⊎ Skip p q e
    bwd : ∀ {q e} → u q e → t q e ⊎ Skip p q e
open _≈⟨_⟩_

≈-sym : ∀ {A} {t u : EmissionSet A} {p} → t ≈⟨ p ⟩ u → u ≈⟨ p ⟩ t
≈-sym (f ⇆ b) = b ⇆ f

≈-refl : ∀ {A} {t : EmissionSet A} {p} → t ≈⟨ p ⟩ t
≈-refl = inj₁ ⇆ inj₁

-- A skip is never seen.
≈-vis : ∀ {A} {t u : EmissionSet A} {p} → t ≈⟨ p ⟩ u → Vis t ≃ Vis u
≈-vis eq = go (fwd eq) ⇄ go (bwd eq)
  where
    go : ∀ {A} {t u : EmissionSet A} {p} → (∀ {q e} → t q e → u q e ⊎ Skip p q e) → ∀ {q e} → Vis t q e → Vis u q e
    go h (r , v) with h r
    ... | inj₁ r′          = r′ , v
    ... | inj₂ (refl , refl) = ⊥-elim v

end-≈ : ∀ {A} {t u : EmissionSet A} {p c} → t ≈⟨ p ⟩ u → t c end → u c end
end-≈ eq r with fwd eq r
... | inj₁ r′      = r′
... | inj₂ (_ , ())

data _≈ᴸ⟨_⟩_ {B : Set} : List (EmissionSet B) → Pos → List (EmissionSet B) → Set₁ where
  []  : ∀ {p} → [] ≈ᴸ⟨ p ⟩ []
  _∷_ : ∀ {p t u Ls Ls′} → t ≈⟨ p ⟩ u → Ls ≈ᴸ⟨ p ⟩ Ls′ → (t ∷ Ls) ≈ᴸ⟨ p ⟩ (u ∷ Ls′)

≈ᴸ-sym : ∀ {B} {Ls Ls′ : List (EmissionSet B)} {p} → Ls ≈ᴸ⟨ p ⟩ Ls′ → Ls′ ≈ᴸ⟨ p ⟩ Ls
≈ᴸ-sym []       = []
≈ᴸ-sym (e ∷ es) = ≈-sym e ∷ ≈ᴸ-sym es

≈ᴸ-refl : ∀ {B} (Ls : List (EmissionSet B)) {p} → Ls ≈ᴸ⟨ p ⟩ Ls
≈ᴸ-refl []       = []
≈ᴸ-refl (_ ∷ Ls) = ≈-refl ∷ ≈ᴸ-refl Ls

-- One lane changed, the rest kept.
≈ᴸ-hole : ∀ {B} (xs : List (EmissionSet B)) {ys ys′ p} → ys ≈ᴸ⟨ p ⟩ ys′ → (xs ʳ++ ys) ≈ᴸ⟨ p ⟩ (xs ʳ++ ys′)
≈ᴸ-hole []       h = h
≈ᴸ-hole (x ∷ xs) h = ≈ᴸ-hole xs (≈-refl ∷ h)

lanes-≈ : ∀ {B} {Ls Ls′ : List (EmissionSet B)} {p} → Ls ≈ᴸ⟨ p ⟩ Ls′ → ∀ {k e} → Lanes Ls k e → Lanes Ls′ k e ⊎ Skip p k e
lanes-≈ (e ∷ _)  (inj₁ r) with fwd e r
... | inj₁ r′ = inj₁ (inj₁ r′)
... | inj₂ sk = inj₂ sk
lanes-≈ (_ ∷ es) (inj₂ x) with lanes-≈ es x
... | inj₁ x′ = inj₁ (inj₂ x′)
... | inj₂ sk = inj₂ sk

------------------------------------------------------------------------
-- Up a map, up a merge

map-≈ : ∀ {A B} (f : A → B) {t u : EmissionSet A} {p} → t ≈⟨ p ⟩ u → MapT f t ≈⟨ p ⟩ MapT f u
map-≈ f eq = go (fwd eq) ⇆ go (bwd eq)
  where
    go : ∀ {t u : EmissionSet _} {p} → (∀ {q e} → t q e → u q e ⊎ Skip p q e) → ∀ {q e} → MapT f t q e → MapT f u q e ⊎ Skip p q e
    go h (map-out r) with h r
    ... | inj₁ r′     = inj₁ (map-out r′)
    ... | inj₂ (_ , ())
    go h (map-skip r) with h r
    ... | inj₁ r′            = inj₁ (map-skip r′)
    ... | inj₂ (refl , refl) = inj₂ (refl , refl)
    go h (map-pin r) with h r
    ... | inj₁ r′     = inj₁ (map-pin r′)
    ... | inj₂ (_ , ())
    go h (map-end r) with h r
    ... | inj₁ r′     = inj₁ (map-end r′)
    ... | inj₂ (_ , ())

since-map : ∀ {A B} (f : A → B) {t : EmissionSet A} {p} → Since p t → Since p (MapT f t)
since-map f s (map-out r)  = s r
since-map f s (map-skip r) = s r
since-map f s (map-pin r)  = s r
since-map f s (map-end r)  = s r

-- Skips apart, folded alike: a fold reads values only.
scan-≈ : ∀ {A B} (f : B → A → B) z {t u : EmissionSet A} {p} → t ≈⟨ p ⟩ u → Scan.ScanT f z t ≈⟨ p ⟩ Scan.ScanT f z u
scan-≈ {A} {B} f z {p = p} eq = go (fwd eq) (bwd eq) ⇆ go (bwd eq) (fwd eq)
  where
    val : ∀ {t u : EmissionSet A} → (∀ {q e} → t q e → u q e ⊎ Skip p q e) → ∀ {q a} → t q (out a) → u q (out a)
    val h r with h r
    ... | inj₁ r′       = r′
    ... | inj₂ (_ , ())
    acc : ∀ {t u : EmissionSet A} → (∀ {q e} → t q e → u q e ⊎ Skip p q e) → (∀ {q e} → u q e → t q e ⊎ Skip p q e)
        → ∀ {q b} → Scan.Acc f z t q b → Scan.Acc f z u q b
    acc h h⁻ (Scan.acc₀ r mn)     = Scan.acc₀ (val h r) (λ y → mn (val h⁻ y))
    acc h h⁻ (Scan.acc a r lt nx) = Scan.acc (acc h h⁻ a) (val h r) lt (λ y → nx (val h⁻ y))
    go : ∀ {t u : EmissionSet A} → (∀ {q e} → t q e → u q e ⊎ Skip p q e) → (∀ {q e} → u q e → t q e ⊎ Skip p q e)
       → ∀ {q e} → Scan.ScanT f z t q e → Scan.ScanT f z u q e ⊎ Skip p q e
    go h h⁻ (Scan.sval a) = inj₁ (Scan.sval (acc h h⁻ a))
    go h h⁻ (Scan.sstep r) with h r
    ... | inj₁ r′            = inj₁ (Scan.sstep r′)
    ... | inj₂ (refl , refl) = inj₂ (refl , refl)
    go h h⁻ (Scan.spin r) with h r
    ... | inj₁ r′       = inj₁ (Scan.spin r′)
    ... | inj₂ (_ , ())
    go h h⁻ (Scan.send r) with h r
    ... | inj₁ r′       = inj₁ (Scan.send r′)
    ... | inj₂ (_ , ())

-- A fold sits at a value.
since-scan : ∀ {A B} (f : B → A → B) z {t : EmissionSet A} {p} → Since p t → Since p (Scan.ScanT f z t)
since-scan f z s (Scan.sval a)  = s (proj₂ (acc-val a))
since-scan f z s (Scan.sstep r) = s r
since-scan f z s (Scan.spin r)  = s r
since-scan f z s (Scan.send r)  = s r

-- A skip more or less: one more row before any position.
reach-≈ : ∀ {A} {t u : EmissionSet A} {p} → (∀ {q e} → u q e → t q e ⊎ Skip p q e) → ∀ {q e} → Reach t q e → Reach u q e
reach-≈ {t = t} {p = p} h {q} {e} (ks , f) = p ∷ ks , λ x lt → go (h x) lt
  where
    go : ∀ {k e′} → t k e′ ⊎ Skip p k e′ → k ≺ q → Dep q e k e′ → k ∈ (p ∷ ks)
    go (inj₁ y)           lt d = there (f y lt d)
    go (inj₂ (refl , _))  lt _ = here refl

trunc-≈ : ∀ {A} {t u : EmissionSet A} {p} → t ≈⟨ p ⟩ u → Truncate t ≈⟨ p ⟩ Truncate u
trunc-≈ eq = go (fwd eq) (bwd eq) ⇆ go (bwd eq) (fwd eq)
  where
    go : ∀ {t u : EmissionSet _} {p} → (∀ {q e} → t q e → u q e ⊎ Skip p q e) → (∀ {q e} → u q e → t q e ⊎ Skip p q e)
       → ∀ {q e} → Truncate t q e → Truncate u q e ⊎ Skip p q e
    go h k (r , fw) with h r
    ... | inj₁ r′ = inj₁ (r′ , reach-≈ k fw)
    ... | inj₂ sk = inj₂ sk

------------------------------------------------------------------------
-- A joiner, generically

-- A row past `p`'s position lies past `p`.
≼-ext : ∀ {p q} x → p ≼ q → p ≼ (q ++ [ x ])
≼-ext {p} {q} x h = ≺→≼ {p} {q ++ [ x ]} (≼-≺-≺ {p} {q} {q ++ [ x ]} h (≺-ext q []))

≼-≺-≼ : ∀ {p} s {k} → p ≼ s → s ≺ k → p ≼ k
≼-≺-≼ {p} s {k} h lt = ≺→≼ {p} {k} (≼-≺-≺ {p} {s} {k} h lt)

like-≈ : ∀ {A} {t u : EmissionSet A} {p} → t ≈⟨ p ⟩ u → Like t u
like-≈ eq = like (val eq) (end-≈ eq)
  where
    val : ∀ {t u : EmissionSet _} {p} → t ≈⟨ p ⟩ u → ∀ {q a} → t q (out a) → u q (out a)
    val eq r with fwd eq r
    ... | inj₁ r′       = r′
    ... | inj₂ (_ , ())

ends-≈ : ∀ {B} {Ls Ls′ : List (EmissionSet B)} {p} → Ls ≈ᴸ⟨ p ⟩ Ls′ → EndsOf Ls ⇔ᴾ EndsOf Ls′
ends-≈ []       = _⇔ᴾ_.[]
ends-≈ (e ∷ es) = (end-≈ e , end-≈ (≈-sym e)) _⇔ᴾ_.∷ ends-≈ es

-- TWO JOINERS, PART FOR PART THE SAME BUT FOR SKIPS AT `p`: the same rows
-- but for skips at `p`.  A skip is no value, no end and no pin.
join-≈→ : ∀ {A B} {p} (P P′ : Policy A B) → Reads P P′ → Policy.outer P ≈⟨ p ⟩ Policy.outer P′ → Policy.begun P ≈⟨ p ⟩ Policy.begun P′
        → ∀ {k e} → JoinP P k e → JoinP P′ k e ⊎ Skip p k e
join-≈→ {p = p} P P′ R eo eb = go
  where
    open Reads R
    val : ∀ {q a} → Policy.outer P q (out a) → Policy.outer P′ q (out a)
    val = Like.outs (like-≈ eo)
    val⁻ : ∀ {q a} → Policy.outer P′ q (out a) → Policy.outer P q (out a)
    val⁻ = Like.outs (like-≈ (≈-sym eo))
    go : ∀ {k e} → JoinP P k e → JoinP P′ k e ⊎ Skip p k e
    go (Joining.val r)                = inj₁ (Joining.val (val r))
    go (Joining.step r) with fwd eo r
    ... | inj₁ r′       = inj₁ (Joining.step r′)
    ... | inj₂ (eq , _) = inj₂ (eq , refl)
    go (Joining.opin r) with fwd eo r
    ... | inj₁ r′       = inj₁ (Joining.opin r′)
    ... | inj₂ (_ , ())
    go (Joining.oend r d)             = inj₁ (Joining.oend (end-≈ eo r) (done-reads R val⁻ d))
    go (Joining.opass r nd)           = inj₁ (Joining.opass (end-≈ eo r) λ d → nd (done-reads (reads-sym R) val d))
    go (Joining.lane r u l nc w)      = inj₁ (Joining.lane (val r) (ru→ u) (_≃_.to lane≃ l) (λ y → nc (cu← y)) w)
    go (Joining.lend r u l nc nh d)   = inj₁ (Joining.lend (val r) (ru→ u) (_≃_.to lane≃ l) (λ y → nc (cu← y)) (λ y → nh (ha← y)) (done-reads R val⁻ d))
    go (Joining.lpass r u l nc nh nd) = inj₁ (Joining.lpass (val r) (ru→ u) (_≃_.to lane≃ l) (λ y → nc (cu← y)) (λ y → nh (ha← y)) λ d → nd (done-reads (reads-sym R) val d))
    go (Joining.hand r u l nc h)      = inj₁ (Joining.hand (val r) (ru→ u) (_≃_.to lane≃ l) (λ y → nc (cu← y)) (ha→ h))
    go (Joining.left r u l nc i)      = inj₁ (Joining.left (val r) (ru→ u) (_≃_.to lane≃ l) (λ y → nc (cu← y)) i)
    go (Joining.run x w) with fwd eb x
    ... | inj₁ x′ = inj₁ (Joining.run x′ w)
    ... | inj₂ sk = inj₂ sk
    go (Joining.rend x nh d)          = inj₁ (Joining.rend (end-≈ eb x) (λ y → nh (ha← y)) (done-reads R val⁻ d))
    go (Joining.rpass x nh nd)        = inj₁ (Joining.rpass (end-≈ eb x) (λ y → nh (ha← y)) λ d → nd (done-reads (reads-sym R) val d))
    go (Joining.rhand x h)            = inj₁ (Joining.rhand (end-≈ eb x) (ha→ h))

join-≈ : ∀ {A B} {p} (P P′ : Policy A B) → Reads P P′ → Policy.outer P ≈⟨ p ⟩ Policy.outer P′ → Policy.begun P ≈⟨ p ⟩ Policy.begun P′
       → JoinP P ≈⟨ p ⟩ JoinP P′
join-≈ P P′ R eo eb = join-≈→ P P′ R eo eb ⇆ join-≈→ P′ P (reads-sym R) (≈-sym eo) (≈-sym eb)

-- A joiner's rows lie past `p` where its outer's, its begun lanes' and
-- each value's lane's do.
since-join : ∀ {A B} {p} (P : Policy A B) → Since p (Policy.outer P) → Since p (Policy.begun P)
           → (∀ {q a k e} → Policy.outer P q (out a) → Policy.lanes P q a k e → p ≼ k) → Since p (JoinP P)
since-join {p = p} P so sb sl (Joining.val {q} {a} r)   = ≼-ext {p} {q} (ix 0) (so {q} {out a} r)
since-join P so sb sl (Joining.step r)                   = so r
since-join P so sb sl (Joining.opin r)                   = so r
since-join P so sb sl (Joining.oend r _)                 = so r
since-join P so sb sl (Joining.opass r _)                = so r
since-join P so sb sl (Joining.lane r _ l _ _)           = sl r l
since-join P so sb sl (Joining.lend r _ l _ _ _)         = sl r l
since-join P so sb sl (Joining.lpass r _ l _ _ _)        = sl r l
since-join {p = p} P so sb sl (Joining.hand {c = c} r _ l _ _) = ≼-ext {p} {c} (ix 0) (sl r l)
since-join P so sb sl (Joining.left r _ l _ _)           = sl r l
since-join P so sb sl (Joining.run x _)                  = sb x
since-join P so sb sl (Joining.rend x _ _)               = sb x
since-join P so sb sl (Joining.rpass x _ _)              = sb x
since-join {p = p} P so sb sl (Joining.rhand {c} x _)   = ≼-ext {p} {c} (ix 0) (sb {c} {end} x)

since-trunc : ∀ {A} {t : EmissionSet A} {p} → Since p t → Since p (Truncate t)
since-trunc s (r , _) = s r

------------------------------------------------------------------------
-- The four joiners

module _ {A B : Set} (L : A → Pos → EmissionSet B) {d : Bool} {n : ℕ} {p : Pos} where

  -- A lane begun past an outer value lies past what the value lies past.
  lane-since : ∀ {O : EmissionSet A} {q a k e} → Since p O → O q (out a) → Lane L q a k e → p ≼ k
  lane-since {q = q} {a = a} {k = k} so r (reads _ s) =
    ≺→≼ {p} {k} (≺-trans {p} {q ++ [ ix 1 ]} {k} (≼-≺-≺ {p} {q} {q ++ [ ix 1 ]} (so {q} {out a} r) (≺-ext q [])) s)

  since-flat : ∀ (O : EmissionSet A) (Ls : List (EmissionSet B)) → Since p O → Each (Since p) Ls → Since p (Flat.JoinT L O d n Ls)
  since-flat O Ls so sl = since-join (flatP L O d n Ls) so (since-lanes Ls sl) (λ {q} {a} r l → lane-since {O = O} {q = q} {a = a} so r l)

  since-row : ∀ (O : EmissionSet A) (Ls : List (EmissionSet B)) → Since p O → Each (Since p) Ls → Since p (Flat.RowT L O d n Ls)
  since-row O Ls so sl = since-trunc (since-flat O Ls so sl)

  flat-≈ : ∀ {O O′ : EmissionSet A} (Ls Ls′ : List (EmissionSet B)) → O ≈⟨ p ⟩ O′ → Ls ≈ᴸ⟨ p ⟩ Ls′
         → Flat.JoinT L O d n Ls ≈⟨ p ⟩ Flat.JoinT L O′ d n Ls′
  flat-≈ {O} {O′} Ls Ls′ eo es = join-≈ (flatP L O d n Ls) (flatP L O′ d n Ls′) (flat-reads L d n (like-≈ eo) (like-≈ (≈-sym eo)) (ends-≈ es)) eo
                                        (lanes-≈ es ⇆ lanes-≈ (≈ᴸ-sym es))

  since-switch : ∀ (O : EmissionSet A) (Ls : List (EmissionSet B)) → Since p O → Each (Since p) Ls → Since p (SwitchF.RowT L O d n Ls)
  since-switch O Ls so sl = since-trunc (since-join (switchP L O d n Ls) so bg (λ {q} {a} r l → lane-since {O = O} {q = q} {a = a} so r l))
    where
      bg : Since p (SwitchF.Bg L O d n Ls)
      bg (SwitchF.bg x _)     = since-lanes Ls sl x
      bg (SwitchF.bpin x _ _) = since-lanes Ls sl x

  switch-bg-≈ : ∀ {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → O ≈⟨ p ⟩ O′ → Ls ≈ᴸ⟨ p ⟩ Ls′
              → ∀ {k e} → SwitchF.Bg L O d n Ls k e → SwitchF.Bg L O′ d n Ls′ k e ⊎ Skip p k e
  switch-bg-≈ eo es (SwitchF.bg x nk) with lanes-≈ es x
  ... | inj₁ x′ = inj₁ (SwitchF.bg x′ λ k → nk (kill-like L d n (like-≈ (≈-sym eo)) (like-≈ eo) (ends-≈ (≈ᴸ-sym es)) k))
  ... | inj₂ sk = inj₂ sk
  switch-bg-≈ eo es (SwitchF.bpin x nk i) with lanes-≈ es x
  ... | inj₁ x′       = inj₁ (SwitchF.bpin x′ (λ k → nk (kill-like L d n (like-≈ (≈-sym eo)) (like-≈ eo) (ends-≈ (≈ᴸ-sym es)) k)) i)
  ... | inj₂ (_ , ())

  switch-≈ : ∀ {O O′ : EmissionSet A} (Ls Ls′ : List (EmissionSet B)) → O ≈⟨ p ⟩ O′ → Ls ≈ᴸ⟨ p ⟩ Ls′ → SwitchF.RowT L O d n Ls ≈⟨ p ⟩ SwitchF.RowT L O′ d n Ls′
  switch-≈ {O} {O′} Ls Ls′ eo es =
    trunc-≈ (join-≈ (switchP L O d n Ls) (switchP L O′ d n Ls′) (switch-reads L d n (like-≈ eo) (like-≈ (≈-sym eo)) (ends-≈ es)) eo
                    (switch-bg-≈ eo es ⇆ switch-bg-≈ (≈-sym eo) (≈ᴸ-sym es)))

  since-exhaust : ∀ (O : EmissionSet A) (Ls : List (EmissionSet B)) → Since p O → Each (Since p) Ls → Since p (ExhaustF.RowT L O d n Ls)
  since-exhaust O Ls so sl = since-trunc (since-join (exhaustP L O d n Ls) so (since-lanes Ls sl) (λ {q} {a} r l → lane-since {O = O} {q = q} {a = a} so r l))

  exhaust-≈ : ∀ {O O′ : EmissionSet A} (Ls Ls′ : List (EmissionSet B)) → O ≈⟨ p ⟩ O′ → Ls ≈ᴸ⟨ p ⟩ Ls′ → ExhaustF.RowT L O d n Ls ≈⟨ p ⟩ ExhaustF.RowT L O′ d n Ls′
  exhaust-≈ {O} {O′} Ls Ls′ eo es =
    trunc-≈ (join-≈ (exhaustP L O d n Ls) (exhaustP L O′ d n Ls′) (exhaust-reads L d n (like-≈ eo) (like-≈ (≈-sym eo)) (ends-≈ es)) eo
                    (lanes-≈ es ⇆ lanes-≈ (≈ᴸ-sym es)))

-- Ends, each lying past `p`.
EndsSince : Pos → List (Pos → Set) → Set
EndsSince p []       = ⊤
EndsSince p (l ∷ ls) = (∀ {c} → l c → p ≼ c) × EndsSince p ls

kth-since : ∀ {p ls c} → EndsSince p ls → Kth (_≡ c) ls 0 → p ≼ c
kth-since {ls = _ ∷ _} (h , _)  (inj₁ (_ , x , refl)) = h x
kth-since {ls = _ ∷ _} (_ , hs) (inj₂ K)              = kth-since hs K

ends-since : ∀ {B} {p} (Ls : List (EmissionSet B)) → Each (Since p) Ls → EndsSince p (EndsOf Ls)
ends-since []       _        = _
ends-since (_ ∷ Ls) (s , ss) = s , ends-since Ls ss

module _ {A B : Set} (m : ℕ) (L : A → Pos → EmissionSet B) {d : Bool} {n : ℕ} {Qu : List A} {p : Pos} where

  module _ (O : EmissionSet A) (Ls : List (EmissionSet B)) (so : Since p O) (sl : Each (Since p) Ls) where
    private
      module X = BoundedF m L O d n Qu Ls

    -- Each lane starts past `p`: at its value, or at an end that frees it.
    starts-since : ∀ {i ls w s a} → EndsSince p ls → X.Item i w a → X.Starts i ls w s → p ≼ s
    starts-since hs (X.outer (Values.first {q} r _))          (X.room _)                 = ≼-ext {p} {q} (ix 1) (so r)
    starts-since hs (X.outer (Values.next {q′ = q} _ r _ _))  (X.room _)                 = ≼-ext {p} {q} (ix 1) (so r)
    starts-since hs (X.outer (Values.first {q} r _))          (X.freed _ _)              = ≼-ext {p} {q} (ix 1) (so r)
    starts-since hs (X.outer (Values.next {q′ = q} _ r _ _))  (X.freed _ _)              = ≼-ext {p} {q} (ix 1) (so r)
    starts-since hs _                                         (X.queued {c = c} _ _ K _ _) = ≼-ext {p} {c} (ix 1) (kth-since hs K)

    sched-since : ∀ i → EndsSince p (X.Sched i)
    sched-since zero    = ends-since Ls sl
    sched-since (suc i) = (λ { {c} (w , a , s , it , st , fr) → ≼-≺-≼ s {c} (starts-since (sched-since i) it st) (From.past fr) }) , sched-since i

    since-bounded : Since p (BoundedF.RowT m L O d n Qu Ls)
    since-bounded = since-trunc (since-join (boundedP m L O d n Qu Ls) so bg ln)
      where
        bg : Since p X.Bg
        bg (X.begun x)            = since-lanes Ls sl x
        bg (X.waits {i} {_} {s} {k} (it , st) fr) = ≼-≺-≼ s {k} (starts-since (sched-since i) it st) (From.past fr)
        ln : ∀ {q a k e} → O q (out a) → X.LaneB q a k e → p ≼ k
        ln {k = k} _ (i , s , (it , st) , fr) = ≼-≺-≼ s {k} (starts-since (sched-since i) it st) (From.past fr)

  bounded-bg-≈ : ∀ {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → O ≈⟨ p ⟩ O′ → Ls ≈ᴸ⟨ p ⟩ Ls′
               → ∀ {k e} → BoundedF.Bg m L O d n Qu Ls k e → BoundedF.Bg m L O′ d n Qu Ls′ k e ⊎ Skip p k e
  bounded-bg-≈ eo es (BoundedF.begun x) with lanes-≈ es x
  ... | inj₁ x′ = inj₁ (BoundedF.begun x′)
  ... | inj₂ sk = inj₂ sk
  bounded-bg-≈ eo es (BoundedF.waits sb fr) = inj₁ (waits-like m L d n Qu (like-≈ eo) (like-≈ (≈-sym eo)) (ends-≈ es) sb fr)

  bounded-≈ : ∀ {O O′ : EmissionSet A} (Ls Ls′ : List (EmissionSet B)) → O ≈⟨ p ⟩ O′ → Ls ≈ᴸ⟨ p ⟩ Ls′
            → BoundedF.RowT m L O d n Qu Ls ≈⟨ p ⟩ BoundedF.RowT m L O′ d n Qu Ls′
  bounded-≈ {O} {O′} Ls Ls′ eo es =
    trunc-≈ (join-≈ (boundedP m L O d n Qu Ls) (boundedP m L O′ d n Qu Ls′) (bounded-reads m L d n Qu (like-≈ eo) (like-≈ (≈-sym eo)) (ends-≈ es)) eo
                    (bounded-bg-≈ eo es ⇆ bounded-bg-≈ (≈-sym eo) (≈ᴸ-sym es)))

------------------------------------------------------------------------
-- Up a take

kept-≈ : ∀ {A} p₀ {t u : EmissionSet A} {p} → t ≈⟨ p ⟩ u → Kept p₀ t ≈⟨ p ⟩ Kept p₀ u
kept-≈ {A} p₀ {p = p} eq = go (fwd eq) ⇆ go (bwd eq)
  where
    go : ∀ {t u : EmissionSet A} → (∀ {k e} → t k e → u k e ⊎ Skip p k e) → ∀ {k e} → Kept p₀ t k e → Kept p₀ u k e ⊎ Skip p k e
    go h (kept x np ins) with h x
    ... | inj₁ x′       = inj₁ (kept x′ np ins)
    ... | inj₂ (_ , ())

since-take : ∀ {A} i (q : A → Bool) w {t : EmissionSet A} {p} → LeadT w p → Since p t → Since p (TakeR i q w t)
since-take i q free {t} {p} _ s (r , _) = go r
  where
    go : ∀ {k e} → TakeWhile.TakeT i q t k e → p ≼ k
    go (TakeWhile.pass x _ _)             = s x
    go (TakeWhile.fail {k} {a} x _ _ _)   = ≺→≼ {p} {k ++ [ ix 0 ]} (≼-≺-≺ {p} {k} {k ++ [ ix 0 ]} (s {k} {out a} x) (≺-ext k []))
    go (TakeWhile.stop {k} {a} x _ _)     = ≺→≼ {p} {k ++ [ last ]} (≼-≺-≺ {p} {k} {k ++ [ last ]} (s {k} {out a} x) (≺-ext k []))
    go (TakeWhile.step x _)               = s x
    go (TakeWhile.tend x _)               = s x
    go (TakeWhile.left x _ _)             = s x
since-take i q (cpAt p₀)  lt s stop                 = lt
since-take i q (cpAt p₀)  lt s (left (kept x _ _))  = s x
since-take i q (cutAt p₀) lt s (kept x _ _)         = s x
since-take i q (overAt p₀) lt s (kept x _ _)        = s x

take-≈ : ∀ {A} i (q : A → Bool) w {t u : EmissionSet A} {p} → t ≈⟨ p ⟩ u → TakeR i q w t ≈⟨ p ⟩ TakeR i q w u
take-≈ {A} i q free {p = p} eq = trunc-≈ (go (fwd eq) (bwd eq) ⇆ go (bwd eq) (fwd eq))
  where
    nf : ∀ {t u : EmissionSet A} → (∀ {k e} → u k e → t k e ⊎ Skip p k e) → ∀ {k} → ¬ TakeWhile.Failed i q t k → ¬ TakeWhile.Failed i q u k
    nf h⁻ n (k′ , a , y , nk , lt) with h⁻ y
    ... | inj₁ y′       = n (k′ , a , y′ , nk , lt)
    ... | inj₂ (_ , ())
    go : ∀ {t u : EmissionSet A} → (∀ {k e} → t k e → u k e ⊎ Skip p k e) → (∀ {k e} → u k e → t k e ⊎ Skip p k e)
       → ∀ {k e} → TakeWhile.TakeT i q t k e → TakeWhile.TakeT i q u k e ⊎ Skip p k e
    go h h⁻ (TakeWhile.pass x kp n) with h x
    ... | inj₁ x′       = inj₁ (TakeWhile.pass x′ kp (nf h⁻ n))
    ... | inj₂ (_ , ())
    go h h⁻ (TakeWhile.fail x kp n ic) with h x
    ... | inj₁ x′       = inj₁ (TakeWhile.fail x′ kp (nf h⁻ n) ic)
    ... | inj₂ (_ , ())
    go h h⁻ (TakeWhile.stop x kp n) with h x
    ... | inj₁ x′       = inj₁ (TakeWhile.stop x′ kp (nf h⁻ n))
    ... | inj₂ (_ , ())
    go h h⁻ (TakeWhile.step x n) with h x
    ... | inj₁ x′            = inj₁ (TakeWhile.step x′ (nf h⁻ n))
    ... | inj₂ (refl , refl) = inj₂ (refl , refl)
    go h h⁻ (TakeWhile.tend x n) with h x
    ... | inj₁ x′       = inj₁ (TakeWhile.tend x′ (nf h⁻ n))
    ... | inj₂ (_ , ())
    go h h⁻ (TakeWhile.left x n ins) with h x
    ... | inj₁ x′       = inj₁ (TakeWhile.left x′ (nf h⁻ n) ins)
    ... | inj₂ (_ , ())
take-≈ {A} i q (cpAt p₀) {p = p} eq = go (fwd eq) ⇆ go (bwd eq)
  where
    go : ∀ {t u : EmissionSet A} → (∀ {k e} → t k e → u k e ⊎ Skip p k e) → ∀ {k e} → Stops p₀ t k e → Stops p₀ u k e ⊎ Skip p k e
    go h stop = inj₁ stop
    go h (left (kept x np ins)) with h x
    ... | inj₁ x′       = inj₁ (left (kept x′ np ins))
    ... | inj₂ (_ , ())
take-≈ {A} i q (cutAt p₀) {p = p} eq = kept-≈ p₀ eq
take-≈ {A} i q (overAt p₀) {p = p} eq = kept-≈ p₀ eq

------------------------------------------------------------------------
-- Up a connect

-- A body a skip apart: its connect too, the source's rows read alike
-- while the body has not ended, an end being no skip.
conn-≈ : ∀ {A B} (r : Pos) (σ : EmissionSet A) {t u : EmissionSet B} {p} → t ≈⟨ p ⟩ u → Connecting.ConnT r σ t ≈⟨ p ⟩ Connecting.ConnT r σ u
conn-≈ {A} {B} r σ {p = p} eq = go (fwd eq) (bwd eq) ⇆ go (bwd eq) (fwd eq)
  where
    alive : ∀ {t u : EmissionSet B} → (∀ {q e} → u q e → t q e ⊎ Skip p q e) → ∀ {k} → Connecting.Alive r σ t k → Connecting.Alive r σ u k
    alive h′ al y with h′ y
    ... | inj₁ y′      = al y′
    ... | inj₂ (_ , ())
    go : ∀ {t u : EmissionSet B} → (∀ {q e} → t q e → u q e ⊎ Skip p q e) → (∀ {q e} → u q e → t q e ⊎ Skip p q e)
       → ∀ {q e} → Connecting.ConnT r σ t q e → Connecting.ConnT r σ u q e ⊎ Skip p q e
    go h h′ (Connecting.body x) with h x
    ... | inj₁ x′ = inj₁ (Connecting.body x′)
    ... | inj₂ sk = inj₂ sk
    go h h′ (Connecting.burst x i)      = inj₁ (Connecting.burst x i)
    go h h′ (Connecting.echo {k} x al un ni) = inj₁ (Connecting.echo x (alive h′ {k} al) un ni)
    go h h′ (Connecting.kept {p′ = p′} x al ni i)  = inj₁ (Connecting.kept x (alive h′ {p′} al) ni i)

-- A source past `p` shows past `p`.
since-conn : ∀ {A B} (r : Pos) (σ : EmissionSet A) (t : EmissionSet B) {p} → After p σ → Since p t → Since p (Connecting.ConnT r σ t)
since-conn r σ t {p} ao st (Connecting.body x)          = st x
since-conn r σ t {p} ao st (Connecting.burst {k} x _)   = ≺→≼ {p} {k ++ [ ix 0 ]} (≺-trans {p} {k} {k ++ [ ix 0 ]} (ao x) (≺-ext k []))
since-conn r σ t {p} ao st (Connecting.echo {k} x _ _ _) = ≺→≼ {p} {k ++ [ ix 0 ]} (≺-trans {p} {k} {k ++ [ ix 0 ]} (ao x) (≺-ext k []))
since-conn r σ t {p} ao st (Connecting.kept {k} x _ _ _) = ≺→≼ {p} {k ++ [ ix 0 ]} (≺-trans {p} {k} {k ++ [ ix 0 ]} (ao x) (≺-ext k []))

postulate
  -- A SKIP AT A SOURCE IS UNSEEN ABOVE ITS CONNECT: the connect shows it
  -- as a skip or a pin under it, and every joiner fed it as a skip under
  -- where it joined, so what differs above is skips past `p` alone, and
  -- the frames above, every other part past `p`, end alike.
  src-vis : ∀ {R Γ X B} (k : CS) (b : St (X ∷ Γ) B) (c : Ctx R Γ B) {t u : EmissionSet X} {p}
          → After p (rows (Hot ∅ k ∷ᴬ env c) b) → LeadC c p → Since p t → Since p u → t ≈⟨ p ⟩ u
          → Vis (up (inSrc k b c) t) ≃ Vis (up (inSrc k b c) u)

------------------------------------------------------------------------
-- THE LIFT

-- The same rows, seen alike.
≃-id : ∀ {A} {t : EmissionSet A} → t ≃ t
≃-id = (λ x → x) ⇄ (λ x → x)

up-vis : ∀ {R Γ A} (c : Ctx R Γ A) {t u : EmissionSet A} {p} → LeadC c p → Since p t → Since p u → t ≈⟨ p ⟩ u → Vis (up c t) ≃ Vis (up c u)
up-vis top                                   ld st su eq = ≈-vis eq
up-vis (inMap f c)                             ld st su eq = up-vis c ld (since-map f st) (since-map f su) (map-≈ f eq)
up-vis (inScan f z c)                          ld st su eq = up-vis c ld (since-scan f z st) (since-scan f z su) (scan-≈ f z eq)
up-vis (inCut true a c)                        ld st su eq = up-vis c ld st su eq
up-vis (inCut false a c)                       ld st su eq = ≃-id
up-vis (inLn true c)                           ld st su eq = up-vis c ld st su eq
up-vis (inLn false c)                          ld st su eq = ≃-id
up-vis (inTake i q w c)                        (lt , ld) st su eq = up-vis c ld (since-take i q w lt st) (since-take i q w lt su) (take-≈ i q w eq)
up-vis (inOuter (mergeᶠ nothing) f d n q ls c) {t} {u} (al , ld) st su eq =
  up-vis c ld (since-row L t Ls st sl) (since-row L u Ls su sl) (trunc-≈ (flat-≈ L Ls Ls eq (≈ᴸ-refl Ls)))
  where
    L  = λ a → pendRows (env c) (f a)
    Ls = rowsL (env c) ls
    sl = after-since Ls al
up-vis (inOuter (mergeᶠ (just m)) f d n q ls c) {t} {u} (al , ld) st su eq =
  up-vis c ld (since-bounded m L t Ls st sl) (since-bounded m L u Ls su sl) (bounded-≈ m L Ls Ls eq (≈ᴸ-refl Ls))
  where
    L  = λ a → pendRows (env c) (f a)
    Ls = rowsL (env c) ls
    sl = after-since Ls al
up-vis (inOuter switchᶠ f d n q ls c) {t} {u} (al , ld) st su eq =
  up-vis c ld (since-switch L t Ls st sl) (since-switch L u Ls su sl) (switch-≈ L Ls Ls eq (≈ᴸ-refl Ls))
  where
    L  = λ a → pendRows (env c) (f a)
    Ls = rowsL (env c) ls
    sl = after-since Ls al
up-vis (inOuter exhaustᶠ f d n q ls c) {t} {u} (al , ld) st su eq =
  up-vis c ld (since-exhaust L t Ls st sl) (since-exhaust L u Ls su sl) (exhaust-≈ L Ls Ls eq (≈ᴸ-refl Ls))
  where
    L  = λ a → pendRows (env c) (f a)
    Ls = rowsL (env c) ls
    sl = after-since Ls al
up-vis (inLanes (mergeᶠ nothing) f d n q o pre post c) {t} {u} (ao , apre , apost , ld) st su eq =
  up-vis c ld (since-row L O Lt so slt) (since-row L O Lu so slu)
       (trunc-≈ (flat-≈ L Lt Lu ≈-refl (≈ᴸ-hole (rowsL ρ pre) (eq ∷ ≈ᴸ-refl (rowsL ρ post)))))
  where
    ρ   = env c
    L   = λ a → pendRows ρ (f a)
    O   = rows ρ o
    Lt  = rowsL ρ pre ʳ++ (t ∷ rowsL ρ post)
    Lu  = rowsL ρ pre ʳ++ (u ∷ rowsL ρ post)
    so  = λ {q} {e} r → ≺→≼ {_} {q} (ao {q} {e} r)
    slt = all-ʳ++ (rowsL ρ pre) (after-since (rowsL ρ pre) apre) (st , after-since (rowsL ρ post) apost)
    slu = all-ʳ++ (rowsL ρ pre) (after-since (rowsL ρ pre) apre) (su , after-since (rowsL ρ post) apost)
up-vis (inLanes (mergeᶠ (just m)) f d n q o pre post c) {t} {u} (ao , apre , apost , ld) st su eq =
  up-vis c ld (since-bounded m L O Lt so slt) (since-bounded m L O Lu so slu)
       (bounded-≈ m L Lt Lu ≈-refl (≈ᴸ-hole (rowsL ρ pre) (eq ∷ ≈ᴸ-refl (rowsL ρ post))))
  where
    ρ   = env c
    L   = λ a → pendRows ρ (f a)
    O   = rows ρ o
    Lt  = rowsL ρ pre ʳ++ (t ∷ rowsL ρ post)
    Lu  = rowsL ρ pre ʳ++ (u ∷ rowsL ρ post)
    so  = λ {q} {e} r → ≺→≼ {_} {q} (ao {q} {e} r)
    slt = all-ʳ++ (rowsL ρ pre) (after-since (rowsL ρ pre) apre) (st , after-since (rowsL ρ post) apost)
    slu = all-ʳ++ (rowsL ρ pre) (after-since (rowsL ρ pre) apre) (su , after-since (rowsL ρ post) apost)
up-vis (inLanes switchᶠ f d n q o pre post c) {t} {u} (ao , apre , apost , ld) st su eq =
  up-vis c ld (since-switch L O Lt so slt) (since-switch L O Lu so slu)
       (switch-≈ L Lt Lu ≈-refl (≈ᴸ-hole (rowsL ρ pre) (eq ∷ ≈ᴸ-refl (rowsL ρ post))))
  where
    ρ   = env c
    L   = λ a → pendRows ρ (f a)
    O   = rows ρ o
    Lt  = rowsL ρ pre ʳ++ (t ∷ rowsL ρ post)
    Lu  = rowsL ρ pre ʳ++ (u ∷ rowsL ρ post)
    so  = λ {q} {e} r → ≺→≼ {_} {q} (ao {q} {e} r)
    slt = all-ʳ++ (rowsL ρ pre) (after-since (rowsL ρ pre) apre) (st , after-since (rowsL ρ post) apost)
    slu = all-ʳ++ (rowsL ρ pre) (after-since (rowsL ρ pre) apre) (su , after-since (rowsL ρ post) apost)
up-vis (inLanes exhaustᶠ f d n q o pre post c) {t} {u} (ao , apre , apost , ld) st su eq =
  up-vis c ld (since-exhaust L O Lt so slt) (since-exhaust L O Lu so slu)
       (exhaust-≈ L Lt Lu ≈-refl (≈ᴸ-hole (rowsL ρ pre) (eq ∷ ≈ᴸ-refl (rowsL ρ post))))
  where
    ρ   = env c
    L   = λ a → pendRows ρ (f a)
    O   = rows ρ o
    Lt  = rowsL ρ pre ʳ++ (t ∷ rowsL ρ post)
    Lu  = rowsL ρ pre ʳ++ (u ∷ rowsL ρ post)
    so  = λ {q} {e} r → ≺→≼ {_} {q} (ao {q} {e} r)
    slt = all-ʳ++ (rowsL ρ pre) (after-since (rowsL ρ pre) apre) (st , after-since (rowsL ρ post) apost)
    slu = all-ʳ++ (rowsL ρ pre) (after-since (rowsL ρ pre) apre) (su , after-since (rowsL ρ post) apost)
up-vis (inSrc k b c)                            (ab , ld) st su eq = src-vis k b c ab ld st su eq
up-vis (inBody k o c) {t} {u}                   (ao , ld) st su eq =
  up-vis c ld (since-conn (CS.connAt k) _ t ao st) (since-conn (CS.connAt k) _ u ao su) (conn-≈ (CS.connAt k) _ eq)
