{-# OPTIONS --guardedness #-}

-- WHAT A TREE STILL OWES, REGION BY REGION: every mark's region, and
-- every region a node will key once its marks run — an of's values, a
-- take's end after its cut, a connect's source and teardown, a joiner's
-- inbox and, while live, its subscription.  A tree's list is its
-- context's around its hole's, so a step that moves one subtree keeps
-- the rest, and what holds pairwise of the old holds of the new once the
-- moved regions sit inside what they replace.
module adequacy.Apart.Items where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; [_]; _++_; _ʳ++_; reverse)
open import Data.List.Properties using (++-assoc; ++-identityʳ; ʳ++-defn)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to all-map; head to all-head; tail to all-tail)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++; ++⁻ to all-++⁻; ++⁻ʳ to all-++⁻ʳ)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (++⁺ to ap-++)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; refl; prep; swap; trans; ↭-sym; ↭-reflexive)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (All-resp-↭; shifts) renaming (++⁺ˡ to ↭-++ˡ; ++⁺ʳ to ↭-++ʳ)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_; ⊆-refl)
open import Data.List.Relation.Binary.Sublist.Heterogeneous using (_∷ʳ_) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import Data.List.Relation.Binary.Sublist.Propositional.Properties using (All-resp-⊆) renaming (++⁺ to ⊆-++; ++⁺ˡ to ⊆-++ˡ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m<n∨m≡n)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst) renaming (trans to ≡-trans)

open import denotation.Events using (Pos; ix; last; _<ᵖ_; <ᵖ-part; <ᵖ-trans; <ᵖ-asym; ix-<)
open import operation.PureObservable using (module Machine; Tape; play; ending) renaming (over to overT)
open Machine using (Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    CS; cs; Att; attAt; attached; Owe; free; cpAt; cutAt; overAt; Ev; plug; own; unsub; cut; killAll; unsubIf; ended)
open import operation.Key using (Key; at; after; _<ᴷ_; at-<ᴷ; ≮ᴷ-trans)
open import adequacy.Least using (KeyIn; k-own; k-kid; k-map; k-scan; k-cut; k-ln; k-take; k-outer; k-lane; k-src; k-body; Lo)
open import adequacy.Stamped using (Ix; ix-⊕; StOK; LOK; QOK; MOK)
open import adequacy.Floor.Keys using (asym; at-after; OwnOf; ob; os; oo; own-cls; own-bld)
open import adequacy.Apart.Cone using (cone-ge)
open import adequacy.Apart.Region using (Rg; cn; tl; pt; bk; In; Sep; sep-sym; NoCl; Keyed; self)

------------------------------------------------------------------------
-- A node's regions

tapeI : ∀ {A} → Tape A → List Rg
tapeI (play τ u i t fr) = [ tl u i ]
tapeI (ending e)        = [ cn e ]
tapeI overT             = []

attI : Att → List Rg
attI attached  = []
attI (attAt p) = [ pt p ]

oweI : Owe → List Rg
oweI free       = []
oweI (cpAt p)   = cn (p ++ [ last ]) ∷ pt p ∷ []
oweI (cutAt p)  = [ pt p ]
oweI (overAt p) = []

mI : (Pos → Rg) → Maybe Pos → List Rg
mI f (just p) = [ f p ]
mI f nothing  = []

bodyR : Pos → Rg
bodyR p = cn (p ++ [ ix 1 ])

csI : ∀ {Γ X} → CS Γ X → List Rg
csI k = mI bodyR (CS.bodyAt k) ++ mI pt (CS.attSrc k) ++ mI pt (CS.owedAt k)

ibI : ∀ {A} → List (Pos × Ev A) → List Rg
ibI []             = []
ibI ((q , _) ∷ ib) = cn q ∷ ibI ib

gI : Bool → Pos → List Rg
gI true  j = [ bk j ]
gI false j = []

mutual
  items : ∀ {Γ A} → St Γ A → List Rg
  items (pend o q)              = []
  items (coldS b l)             = tapeI l
  items (ofS i p [])            = [ cn (p ++ [ last ]) ]
  items (ofS i p (_ ∷ _))       = [ tl p i ]
  items doneS                   = []
  items (mapS f s)              = items s
  items (scanS f z s)           = items s
  items (cutS l a s)            = attI a ++ items s
  items (lnS b s)               = items s
  items (takeS i q w s)         = oweI w ++ items s
  items (flatS op f d n q o ls) = items o ++ itemsL ls
  items (connS k o b)           = csI k ++ items o ++ items b
  items (joinS j g x ib)        = ibI ib ++ gI g j

  itemsL : ∀ {Γ A} → List (St Γ A) → List Rg
  itemsL []       = []
  itemsL (s ∷ ls) = items s ++ itemsL ls

------------------------------------------------------------------------
-- Around a hole

lhs : ∀ {R Γ A} → Ctx R Γ A → List Rg
lhs top                               = []
lhs (inMap f c)                       = lhs c
lhs (inScan f z c)                    = lhs c
lhs (inCut l a c)                     = lhs c ++ attI a
lhs (inLn b c)                        = lhs c
lhs (inTake i q w c)                  = lhs c ++ oweI w
lhs (inOuter op f d n q ls c)         = lhs c
lhs (inLanes op f d n q o pre post c) = lhs c ++ items o ++ itemsL (reverse pre)
lhs (inSrc k b c)                     = lhs c ++ csI k
lhs (inBody k o c)                    = lhs c ++ csI k ++ items o

rhs : ∀ {R Γ A} → Ctx R Γ A → List Rg
rhs top                               = []
rhs (inMap f c)                       = rhs c
rhs (inScan f z c)                    = rhs c
rhs (inCut l a c)                     = rhs c
rhs (inLn b c)                        = rhs c
rhs (inTake i q w c)                  = rhs c
rhs (inOuter op f d n q ls c)         = itemsL ls ++ rhs c
rhs (inLanes op f d n q o pre post c) = itemsL post ++ rhs c
rhs (inSrc k b c)                     = items b ++ rhs c
rhs (inBody k o c)                    = rhs c

itemsL-++ : ∀ {Γ A} (xs : List (St Γ A)) {ys} → itemsL (xs ++ ys) ≡ itemsL xs ++ itemsL ys
itemsL-++ []       = refl
itemsL-++ (s ∷ xs) {ys} = ≡-trans (cong (items s ++_) (itemsL-++ xs)) (sym (++-assoc (items s) (itemsL xs) (itemsL ys)))

private
  -- `a ++ (b ++ m) ++ r` as `(a ++ b) ++ m ++ r`.
  left : ∀ (a b m r : List Rg) → a ++ (b ++ m) ++ r ≡ (a ++ b) ++ m ++ r
  left a b m r = ≡-trans (cong (a ++_) (++-assoc b m r)) (sym (++-assoc a b (m ++ r)))

  -- `a ++ (m ++ b) ++ r` as `a ++ m ++ b ++ r`.
  right : ∀ (a m b r : List Rg) → a ++ (m ++ b) ++ r ≡ a ++ m ++ b ++ r
  right a m b r = cong (a ++_) (++-assoc m b r)

plug-items : ∀ {R Γ A} (c : Ctx R Γ A) (t : St Γ A) → items (plug c t) ≡ lhs c ++ items t ++ rhs c
plug-items top                               t = sym (++-identityʳ (items t))
plug-items (inMap f c)                       t = plug-items c (mapS f t)
plug-items (inScan f z c)                    t = plug-items c (scanS f z t)
plug-items (inCut l a c)                     t = ≡-trans (plug-items c (cutS l a t)) (left (lhs c) (attI a) (items t) (rhs c))
plug-items (inLn b c)                        t = plug-items c (lnS b t)
plug-items (inTake i q w c)                  t = ≡-trans (plug-items c (takeS i q w t)) (left (lhs c) (oweI w) (items t) (rhs c))
plug-items (inOuter op f d n q ls c)         t = ≡-trans (plug-items c (flatS op f d n q t ls)) (right (lhs c) (items t) (itemsL ls) (rhs c))
plug-items (inLanes op f d n q o pre post c) t =
  ≡-trans (plug-items c (flatS op f d n q o (pre ʳ++ t ∷ post)))
  (cong (λ z → lhs c ++ (items o ++ z) ++ rhs c) (≡-trans (cong itemsL (ʳ++-defn pre)) (itemsL-++ (reverse pre)))
  ⟨≡⟩ reshape (lhs c) (items o) (itemsL (reverse pre)) (items t) (itemsL post) (rhs c))
  where
    _⟨≡⟩_ : ∀ {x y z : List Rg} → x ≡ y → y ≡ z → x ≡ z
    _⟨≡⟩_ = ≡-trans
    infixr 5 _⟨≡⟩_
    reshape : ∀ (a o r m p z : List Rg) → a ++ (o ++ r ++ m ++ p) ++ z ≡ (a ++ o ++ r) ++ m ++ p ++ z
    reshape a o r m p z rewrite ++-assoc a (o ++ r) (m ++ p ++ z) | ++-assoc o r (m ++ p ++ z)
                              | ++-assoc o (r ++ m ++ p) z | ++-assoc r (m ++ p) z | ++-assoc m p z = refl
plug-items (inSrc k b c)                     t =
  ≡-trans (plug-items c (connS k t b)) (reshape (lhs c) (csI k) (items t) (items b) (rhs c))
  where
    reshape : ∀ (a s m b r : List Rg) → a ++ (s ++ m ++ b) ++ r ≡ (a ++ s) ++ m ++ b ++ r
    reshape a s m b r rewrite ++-assoc a s (m ++ b ++ r) | ++-assoc s (m ++ b) r | ++-assoc m b r = refl
plug-items (inBody k o c)                    t =
  ≡-trans (plug-items c (connS k o t)) (reshape (lhs c) (csI k) (items o) (items t) (rhs c))
  where
    reshape : ∀ (a s o m r : List Rg) → a ++ (s ++ o ++ m) ++ r ≡ (a ++ s ++ o) ++ m ++ r
    reshape a s o m r rewrite ++-assoc a (s ++ o) (m ++ r) | ++-assoc s o (m ++ r) | ++-assoc s (o ++ m) r | ++-assoc o m r = refl

------------------------------------------------------------------------
-- Pairwise, under a symmetric relation

private
  variable
    xs ys : List Rg

ap-↭ : xs ↭ ys → AllPairs Sep xs → AllPairs Sep ys
ap-↭ refl                h                          = h
ap-↭ (prep x p)          (a ∷ h)                    = All-resp-↭ p a ∷ ap-↭ p h
ap-↭ (swap x y p)        ((rxy ∷ ax) ∷ (ay ∷ h))    = (sep-sym {x} {y} rxy ∷ All-resp-↭ p ay) ∷ (All-resp-↭ p ax ∷ ap-↭ p h)
ap-↭ (trans p q)         h                          = ap-↭ q (ap-↭ p h)

ap-⊆ : xs ⊆ ys → AllPairs Sep ys → AllPairs Sep xs
ap-⊆ []ˢ _ = []
ap-⊆ (y ∷ʳ p)                 (_ ∷ h) = ap-⊆ p h
ap-⊆ (refl ∷ˢ p) (a ∷ h) = All-resp-⊆ p a ∷ ap-⊆ p h

ap-++⁻ : ∀ as {bs} → AllPairs Sep (as ++ bs) → AllPairs Sep as × AllPairs Sep bs × All (λ x → All (Sep x) bs) as
ap-++⁻ []       h       = [] , h , []
ap-++⁻ (x ∷ as) (a ∷ h) with ap-++⁻ as h | all-++⁻ as a
... | h₁ , h₂ , h₃ | a₁ , a₂ = (a₁ ∷ h₁) , h₂ , (a₂ ∷ h₃)

-- Rows as columns.
flipA : ∀ {R : Rg → Rg → Set} as bs → All (λ x → All (R x) bs) as → All (λ y → All (λ x → R x y) as) bs
flipA as []       h = []
flipA as (b ∷ bs) h = all-map all-head h ∷ flipA as bs (all-map all-tail h)

private
  -- The moved part to the front.
  front : ∀ (L O X Rr : List Rg) → L ++ (O ++ X) ++ Rr ↭ O ++ L ++ X ++ Rr
  front L O X Rr = trans (↭-reflexive (cong (L ++_) (++-assoc O X Rr))) (shifts L O)

  -- `B ++ L ++ T ++ Rr` with `T` split into `O ++ X`.
  split : ∀ (B L O X Rr : List Rg) {T} → T ↭ O ++ X → B ++ L ++ T ++ Rr ↭ (B ++ O) ++ L ++ X ++ Rr
  split B L O X Rr {T} pT =
    trans (↭-++ˡ B (↭-++ˡ L (↭-++ʳ Rr pT)))
    (trans (↭-++ˡ B (front L O X Rr)) (↭-reflexive (sym (++-assoc B O (L ++ X ++ Rr)))))

-- A HOLE REFILLED: the subtree's regions `O ++ X` become `Nn ++ X`, the
-- run's `B` becomes `B′`; what the new regions owe each other is
-- given, and what they owe the rest follows from what the old owed it.
hole : ∀ {P : Rg → Set} (B B′ O Nn X L Rr : List Rg) {T T′}
     → T ↭ O ++ X → T′ ↭ Nn ++ X
     → All P (L ++ T ++ Rr)
     → (∀ k → All (λ z → Sep z k) (B ++ O) → P k → All (λ n → Sep n k) (B′ ++ Nn))
     → AllPairs Sep (B′ ++ Nn)
     → AllPairs Sep (B ++ L ++ T ++ Rr) → AllPairs Sep (B′ ++ L ++ T′ ++ Rr)
hole {P} B B′ O Nn X L Rr pT pT′ hp step hn h with ap-++⁻ (B ++ O) (ap-↭ (split B L O X Rr pT) h)
... | _ , hk , cross = ap-↭ (↭-sym (split B′ L Nn X Rr pT′)) (ap-++ hn hk (flipA K (B′ ++ Nn) cols))
  where
    K = L ++ X ++ Rr
    pk : All P K
    pk = all-++⁻ʳ O (All-resp-↭ (trans (↭-++ˡ L (↭-++ʳ Rr pT)) (front L O X Rr)) hp)
    cols : All (λ k → All (λ n → Sep n k) (B′ ++ Nn)) K
    cols = go K (flipA (B ++ O) K cross) pk
      where
        go : ∀ ks → All (λ k → All (λ z → Sep z k) (B ++ O)) ks → All P ks → All (λ k → All (λ n → Sep n k) (B′ ++ Nn)) ks
        go []       []       []       = []
        go (k ∷ ks) (c ∷ cz) (p ∷ ps) = step k c p ∷ go ks cz ps

-- A HOLE THINNED: fewer regions, nothing new.
thin : ∀ {R Γ A} (c : Ctx R Γ A) {B B′ t t′} → B′ ⊆ B → items t′ ⊆ items t
     → AllPairs Sep (B ++ items (plug c t)) → AllPairs Sep (B′ ++ items (plug c t′))
thin c {B} {B′} {t} {t′} hb ht h rewrite plug-items c t | plug-items c t′ =
  ap-⊆ (⊆-++ hb (⊆-++ (⊆-refl {x = lhs c}) (⊆-++ ht ⊆-refl))) h

------------------------------------------------------------------------
-- No region a node owes is the run

mutual
  no-cl : ∀ {Γ A} (s : St Γ A) → All NoCl (items s)
  no-cl (pend o q)              = []
  no-cl (coldS b (play τ u i t fr)) = tt ∷ []
  no-cl (coldS b (ending e))    = tt ∷ []
  no-cl (coldS b overT)         = []
  no-cl (ofS i p [])            = tt ∷ []
  no-cl (ofS i p (_ ∷ _))       = tt ∷ []
  no-cl doneS                   = []
  no-cl (mapS f s)              = no-cl s
  no-cl (scanS f z s)           = no-cl s
  no-cl (cutS l a s)            = all-++ (att a) (no-cl s)
    where
      att : ∀ a → All NoCl (attI a)
      att attached  = []
      att (attAt p) = tt ∷ []
  no-cl (lnS b s)               = no-cl s
  no-cl (takeS i q w s)         = all-++ (owe w) (no-cl s)
    where
      owe : ∀ w → All NoCl (oweI w)
      owe free       = []
      owe (cpAt p)   = tt ∷ tt ∷ []
      owe (cutAt p)  = tt ∷ []
      owe (overAt p) = []
  no-cl (flatS op f d n q o ls) = all-++ (no-cl o) (no-clL ls)
  no-cl (connS k o b)           = all-++ (cs-cl k) (all-++ (no-cl o) (no-cl b))
  no-cl (joinS j g x ib)        = all-++ (ib-cl ib) (g-cl g)
    where
      ib-cl : ∀ {A} (ib : List (Pos × Ev A)) → All NoCl (ibI ib)
      ib-cl []             = []
      ib-cl ((q , _) ∷ ib) = tt ∷ ib-cl ib
      g-cl : ∀ g → All NoCl (gI g j)
      g-cl true  = tt ∷ []
      g-cl false = []

  no-clL : ∀ {Γ A} (ls : List (St Γ A)) → All NoCl (itemsL ls)
  no-clL []       = []
  no-clL (s ∷ ls) = all-++ (no-cl s) (no-clL ls)

  cs-cl : ∀ {Γ X} (k : CS Γ X) → All NoCl (csI k)
  cs-cl k = all-++ (m (CS.bodyAt k)) (all-++ (m′ (CS.attSrc k)) (m′ (CS.owedAt k)))
    where
      m : ∀ mp → All NoCl (mI bodyR mp)
      m (just p) = tt ∷ []
      m nothing  = []
      m′ : ∀ mp → All NoCl (mI pt mp)
      m′ (just p) = tt ∷ []
      m′ nothing  = []

------------------------------------------------------------------------
-- Every key a tree carries is in a region it owes

Covers : List Rg → Key → Set
Covers L (at y)    = Σ Rg λ R → R ∈ L × In R y
Covers L (after y) = pt y ∈ L

covers-l : ∀ L {M} κ → Covers L κ → Covers (L ++ M) κ
covers-l L (at y)    (R , m , i) = R , ∈-++⁺ˡ m , i
covers-l L (after y) m           = ∈-++⁺ˡ m

covers-r : ∀ L {M} κ → Covers M κ → Covers (L ++ M) κ
covers-r L (at y)    (R , m , i) = R , ∈-++⁺ʳ L m , i
covers-r L (after y) m           = ∈-++⁺ʳ L m

private
  cs-cover : ∀ {Γ X} (k : CS Γ X) {m κ} → OwnOf k m κ → Covers (csI k) κ
  cs-cover (cs _ _ _ (just p) _ _ _ _ _ _) (ob refl) = bodyR p , here refl , self _
  cs-cover (cs _ _ _ ba (just p) _ _ _ _ _) (os refl) = ∈-++⁺ʳ (mI bodyR ba) (here refl)
  cs-cover (cs _ _ _ ba as (just p) _ _ _ _) (oo refl) = ∈-++⁺ʳ (mI bodyR ba) (∈-++⁺ʳ (mI pt as) (here refl))

  ib-cover : ∀ {A} q (e : Ev A) ib {L} → Covers (ibI ((q , e) ∷ ib) ++ L) (at q)
  ib-cover q e ib = cn q , here refl , self q

mutual
  cover : ∀ {Γ A} (s : St Γ A) {κ} → KeyIn s κ → Covers (items s) κ
  cover (coldS b (play τ u i t fr)) (k-own (here refl)) = tl u i , here refl , inj₁ (i , ≤-refl , self _)
  cover (coldS b (play τ u i t fr)) (k-own (there ()))
  cover (coldS b (ending e))    (k-own (here refl)) = cn e , here refl , self e
  cover (coldS b (ending e))    (k-own (there ()))
  cover (coldS b overT)         (k-own ())
  cover (ofS i p [])            (k-own (here refl)) = cn (p ++ [ last ]) , here refl , self _
  cover (ofS i p (_ ∷ _))       (k-own (here refl)) = tl p i , here refl , inj₁ (i , ≤-refl , self _)
  cover (ofS i p [])            (k-own (there ()))
  cover (ofS i p (_ ∷ _))       (k-own (there ()))
  cover (cutS l (attAt p) s)    (k-own (here refl)) = here refl
  cover (cutS l (attAt p) s)    (k-own (there ()))
  cover (cutS l attached s)     (k-own ())
  cover (takeS i q (cpAt p) s)  (k-own (here refl)) = cn (p ++ [ last ]) , here refl , self _
  cover (takeS i q (cpAt p) s)  (k-own (there ()))
  cover (takeS i q (cutAt p) s) (k-own (here refl)) = here refl
  cover (takeS i q (cutAt p) s) (k-own (there ()))
  cover (takeS i q free s)      (k-own ())
  cover (takeS i q (overAt p) s) (k-own ())
  cover (connS k o b)           (k-own m) = covers-l (csI k) _ (cs-cover k (own-cls k {o} {b} m))
  cover (joinS j g x ((q , e) ∷ ib)) (k-own (here refl)) = ib-cover q e ib
  cover (joinS j g x ((q , e) ∷ ib)) (k-own (there ()))
  cover (joinS j g x [])        (k-own ())
  cover (pend o q)              (k-own ())
  cover doneS                   (k-own ())
  cover (mapS f s)              (k-own ())
  cover (scanS f z s)           (k-own ())
  cover (lnS b s)               (k-own ())
  cover (flatS op f d n q o ls) (k-own ())
  cover (mapS f s)              (k-kid (k-map h))   = cover s h
  cover (scanS f z s)           (k-kid (k-scan h))  = cover s h
  cover (cutS l a s)            (k-kid (k-cut h))   = covers-r (attI a) _ (cover s h)
  cover (lnS b s)               (k-kid (k-ln h))    = cover s h
  cover (takeS i q w s)         (k-kid (k-take h))  = covers-r (oweI w) _ (cover s h)
  cover (flatS op f d n q o ls) (k-kid (k-outer h)) = covers-l (items o) _ (cover o h)
  cover (flatS op f d n q o ls) (k-kid (k-lane m h)) = covers-r (items o) _ (coverL ls m h)
  cover (connS k o b)           (k-kid (k-src h))   = covers-r (csI k) _ (covers-l (items o) _ (cover o h))
  cover (connS k o b)           (k-kid (k-body h))  = covers-r (csI k) _ (covers-r (items o) _ (cover b h))

  coverL : ∀ {Γ A} (ls : List (St Γ A)) {s κ} → s ∈ ls → KeyIn s κ → Covers (itemsL ls) κ
  coverL (s ∷ ls) (here refl) h = covers-l (items s) _ (cover s h)
  coverL (s ∷ ls) (there m)   h = covers-r (items s) _ (coverL ls m h)

------------------------------------------------------------------------
-- Every region keys no earlier than its own mark's key

_≼_ : Pos → Pos → Set
a ≼ b = a <ᵖ b ≡ true ⊎ a ≡ b

≼-trans : ∀ {a b c} → a ≼ b → b ≼ c → a ≼ c
≼-trans {a} {b} {c} (inj₁ ab) (inj₁ bc) = inj₁ (<ᵖ-trans a b c ab bc)
≼-trans (inj₁ ab) (inj₂ refl) = inj₁ ab
≼-trans (inj₂ refl) bc = bc

-- No earlier than a key no earlier than `h`.
past-of : ∀ {a y} h → a ≼ y → at a <ᴷ h ≡ false → at y <ᴷ h ≡ false
past-of {a} {y} h (inj₁ ay)   k = ≮ᴷ-trans (at y) (at a) h (≡-trans (at-<ᴷ y a) (<ᵖ-asym a y ay)) k
past-of         h (inj₂ refl) k = k

cn-keyed : ∀ {r} h → Ix r → at r <ᴷ h ≡ false → Keyed h (cn r)
cn-keyed h hr k y c = past-of h (cone-ge hr c) k

tl-keyed : ∀ {u i} h → Ix u → at (u ++ [ ix i ]) <ᴷ h ≡ false → Keyed h (tl u i)
tl-keyed {u} {i} h hu k y (inj₁ (j , le , c)) = past-of {u ++ [ ix i ]} h (≼-trans step (cone-ge (ix-⊕ u _ hu) c)) k
  where
    step : (u ++ [ ix i ]) ≼ (u ++ [ ix j ])
    step with m≤n⇒m<n∨m≡n le
    ... | inj₁ lt   = inj₁ (<ᵖ-part u [] [] (ix-< lt))
    ... | inj₂ refl = inj₂ refl
tl-keyed {u} {i} h hu k y (inj₂ c) = past-of {u ++ [ ix i ]} h (≼-trans (inj₁ (<ᵖ-part u {ix i} {last} [] [] refl)) (cone-ge (ix-⊕ u _ hu) c)) k

-- A take's teardown after the end it owes.
pt-under : ∀ p y h → at (p ++ y) <ᴷ h ≡ false → Keyed h (pt p)
pt-under p y h k = ≮ᴷ-trans (after p) (at (p ++ y)) h (asym (at (p ++ y)) (after p) (at-after p y)) k

private
  ib-keyed : ∀ {A h} q (e : Ev A) ib → QOK ((q , e) ∷ ib) → at q <ᴷ h ≡ false → All (Keyed h) (ibI ((q , e) ∷ ib))
  ib-keyed {h = h} q e []               (hq , _ , _)  k = cn-keyed h hq k ∷ []
  ib-keyed {h = h} q e ((r , e′) ∷ ib) (hq , b , hs) k =
    cn-keyed h hq k ∷ ib-keyed r e′ ib hs (≮ᴷ-trans (at r) (at q) h (≡-trans (at-<ᴷ r q) b) k)

  g-keyed : ∀ {h} g j → All (Keyed h) (gI g j)
  g-keyed true  j = tt ∷ []
  g-keyed false j = []

  body-keyed : ∀ {h} mp → MOK mp → (∀ {p} → mp ≡ just p → at (p ++ [ ix 1 ]) <ᴷ h ≡ false) → All (Keyed h) (mI bodyR mp)
  body-keyed {h} (just p) hp k = cn-keyed h (ix-⊕ p _ hp) (k refl) ∷ []
  body-keyed nothing  _  k = []

  pt-keyed : ∀ {h} mp → (∀ {p} → mp ≡ just p → after p <ᴷ h ≡ false) → All (Keyed h) (mI pt mp)
  pt-keyed (just p) k = k refl ∷ []
  pt-keyed nothing  k = []

mutual
  keyed : ∀ {Γ A h} (s : St Γ A) → StOK s → Lo s h → All (Keyed h) (items s)
  keyed (pend o q)                  _ lo = []
  keyed {h = h} (coldS b (play τ u i t fr)) (hu , _) lo = tl-keyed h hu (lo (k-own (here refl))) ∷ []
  keyed {h = h} (coldS b (ending e))        he lo = cn-keyed h he (lo (k-own (here refl))) ∷ []
  keyed (coldS b overT)             _ lo = []
  keyed {h = h} (ofS i p [])                hp lo = cn-keyed h (ix-⊕ p _ hp) (lo (k-own (here refl))) ∷ []
  keyed {h = h} (ofS i p (_ ∷ _))           hp lo = tl-keyed h hp (lo (k-own (here refl))) ∷ []
  keyed doneS                       _ lo = []
  keyed (mapS f s)                  hs lo = keyed s hs (λ h → lo (k-kid (k-map h)))
  keyed (scanS f z s)               hs lo = keyed s hs (λ h → lo (k-kid (k-scan h)))
  keyed (cutS l attached s)         (_ , hs) lo = keyed s hs (λ h → lo (k-kid (k-cut h)))
  keyed (cutS l (attAt p) s)        (_ , hs) lo = lo (k-own (here refl)) ∷ keyed s hs (λ h → lo (k-kid (k-cut h)))
  keyed (lnS b s)                   hs lo = keyed s hs (λ h → lo (k-kid (k-ln h)))
  keyed (takeS i q free s)          (_ , hs) lo = keyed s hs (λ h → lo (k-kid (k-take h)))
  keyed {h = h} (takeS i q (cpAt p) s)      (hp , hs) lo =
    cn-keyed h (ix-⊕ p _ hp) (lo (k-own (here refl))) ∷ pt-under p [ last ] h (lo (k-own (here refl))) ∷ keyed s hs (λ h → lo (k-kid (k-take h)))
  keyed (takeS i q (cutAt p) s)     (_ , hs) lo = lo (k-own (here refl)) ∷ keyed s hs (λ h → lo (k-kid (k-take h)))
  keyed (takeS i q (overAt p) s)    (_ , hs) lo = keyed s hs (λ h → lo (k-kid (k-take h)))
  keyed (flatS op f d n q o ls)     (ho , hl) lo = all-++ (keyed o ho (λ h → lo (k-kid (k-outer h)))) (keyedL ls hl (λ m h → lo (k-kid (k-lane m h))))
  keyed (connS k o b)               ((hb , _ , _) , ho , hb′ , _) lo =
    all-++ (all-++ (body-keyed (CS.bodyAt k) hb (λ e → lo (k-own (own-bld k {o} {b} (ob e)))))
                   (all-++ (pt-keyed (CS.attSrc k) (λ e → lo (k-own (own-bld k {o} {b} (os e)))))
                           (pt-keyed (CS.owedAt k) (λ e → lo (k-own (own-bld k {o} {b} (oo e)))))))
           (all-++ (keyed o ho (λ h → lo (k-kid (k-src h)))) (keyed b hb′ (λ h → lo (k-kid (k-body h)))))
  keyed (joinS j g x [])            _ lo = g-keyed g j
  keyed (joinS j g x ((q , e) ∷ ib)) (_ , hq) lo = all-++ (ib-keyed q e ib hq (lo (k-own (here refl)))) (g-keyed g j)

  keyedL : ∀ {Γ A h} (ls : List (St Γ A)) → LOK ls → (∀ {s κ} → s ∈ ls → KeyIn s κ → κ <ᴷ h ≡ false) → All (Keyed h) (itemsL ls)
  keyedL []       _        lo = []
  keyedL (s ∷ ls) (hs , hl) lo = all-++ (keyed s hs (lo (here refl))) (keyedL ls hl (λ m → lo (there m)))

------------------------------------------------------------------------
-- Teardown only drops regions

mutual
  unsub-⊆ : ∀ {Γ A} (s : St Γ A) → items (proj₁ (unsub s)) ⊆ items s
  unsub-⊆ (coldS true l)          = ⊆-refl
  unsub-⊆ (coldS false l)         = ⊆-refl
  unsub-⊆ (mapS f s)              = unsub-⊆ s
  unsub-⊆ (scanS f z s)           = unsub-⊆ s
  unsub-⊆ (takeS i p w s)         = ⊆-++ ⊆-refl (cut-⊆ s)
  unsub-⊆ (flatS op f d n q o ls) = ⊆-++ (cut-⊆ o) (killAll-⊆ ls)
  unsub-⊆ (connS k o b)           = ⊆-++ (⊆-refl {x = csI k}) (⊆-++ (unsub-⊆ o) (unsub-⊆ b))
  unsub-⊆ (joinS j g x ib)        = none (ibI ib ++ gI g j)
    where
      none : ∀ (L : List Rg) → [] ⊆ L
      none []      = []ˢ
      none (y ∷ L) = y ∷ʳ none L
  unsub-⊆ (pend o q)              = ⊆-refl
  unsub-⊆ (ofS i p xs)            = ⊆-refl
  unsub-⊆ doneS                   = ⊆-refl
  unsub-⊆ (cutS l a s)            = ⊆-refl
  unsub-⊆ (lnS b s)               = ⊆-refl

  cut-⊆ : ∀ {Γ A} (s : St Γ A) → items (proj₁ (cut s)) ⊆ items s
  cut-⊆ (cutS l attached s)     = unsub-⊆ s
  cut-⊆ (cutS l (attAt p) s)    = ⊆-refl
  cut-⊆ (pend o q)              = ⊆-refl
  cut-⊆ (coldS b l)             = ⊆-refl
  cut-⊆ (ofS i p xs)            = ⊆-refl
  cut-⊆ doneS                   = ⊆-refl
  cut-⊆ (mapS f s)              = ⊆-refl
  cut-⊆ (scanS f z s)           = ⊆-refl
  cut-⊆ (lnS b s)               = ⊆-refl
  cut-⊆ (takeS i q w s)         = ⊆-refl
  cut-⊆ (flatS op f d n q o ls) = ⊆-refl
  cut-⊆ (connS k o b)           = ⊆-refl
  cut-⊆ (joinS j g x ib)        = ⊆-refl

  killAll-⊆ : ∀ {Γ B} (ls : List (St Γ B)) → itemsL (proj₁ (killAll ls)) ⊆ itemsL ls
  killAll-⊆ []                          = ⊆-refl
  killAll-⊆ (lnS true s ∷ ls)           = ⊆-++ (cut-⊆ s) (killAll-⊆ ls)
  killAll-⊆ (lnS false s ∷ ls)          = ⊆-++ ⊆-refl (killAll-⊆ ls)
  killAll-⊆ (pend o q ∷ ls)             = ⊆-++ ⊆-refl (killAll-⊆ ls)
  killAll-⊆ (coldS b l ∷ ls)            = ⊆-++ ⊆-refl (killAll-⊆ ls)
  killAll-⊆ (ofS i p xs ∷ ls)           = ⊆-++ ⊆-refl (killAll-⊆ ls)
  killAll-⊆ (doneS ∷ ls)                = ⊆-++ ⊆-refl (killAll-⊆ ls)
  killAll-⊆ (mapS f s ∷ ls)             = ⊆-++ ⊆-refl (killAll-⊆ ls)
  killAll-⊆ (scanS f z s ∷ ls)          = ⊆-++ ⊆-refl (killAll-⊆ ls)
  killAll-⊆ (cutS l a s ∷ ls)           = ⊆-++ ⊆-refl (killAll-⊆ ls)
  killAll-⊆ (takeS i q w s ∷ ls)        = ⊆-++ ⊆-refl (killAll-⊆ ls)
  killAll-⊆ (flatS op f d n q o l ∷ ls) = ⊆-++ ⊆-refl (killAll-⊆ ls)
  killAll-⊆ (connS k o b ∷ ls)          = ⊆-++ ⊆-refl (killAll-⊆ ls)
  killAll-⊆ (joinS j g x ib ∷ ls)       = ⊆-++ ⊆-refl (killAll-⊆ ls)

unsubIf-⊆ : ∀ {Γ A} b (s : St Γ A) → items (proj₁ (unsubIf b s)) ⊆ items s
unsubIf-⊆ true  s = unsub-⊆ s
unsubIf-⊆ false s = ⊆-refl

-- A lane ended keeps what it owes.
ended-items : ∀ {Γ B} (s : St Γ B) → items (ended s) ≡ items s
ended-items (lnS b (cutS l a s))    = refl
ended-items (lnS b (pend o q))      = refl
ended-items (lnS b (coldS x l))     = refl
ended-items (lnS b (ofS i p xs))    = refl
ended-items (lnS b doneS)           = refl
ended-items (lnS b (mapS f s))      = refl
ended-items (lnS b (scanS f z s))   = refl
ended-items (lnS b (lnS x s))       = refl
ended-items (lnS b (takeS i q w s)) = refl
ended-items (lnS b (flatS op f d n q o ls)) = refl
ended-items (lnS b (connS k o x))   = refl
ended-items (lnS b (joinS j g x ib)) = refl
ended-items (pend o q)              = refl
ended-items (coldS b l)             = refl
ended-items (ofS i p xs)            = refl
ended-items doneS                   = refl
ended-items (mapS f s)              = refl
ended-items (scanS f z s)           = refl
ended-items (cutS l a s)            = refl
ended-items (takeS i q w s)         = refl
ended-items (flatS op f d n q o ls) = refl
ended-items (connS k o b)           = refl
ended-items (joinS j g x ib)        = refl
