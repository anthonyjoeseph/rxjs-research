{-# OPTIONS --guardedness #-}

-- THE TREE ABOVE A RISING EVENT, READ THROUGH IT: each frame's node facts
-- over the rows its hole owes as the run reads them, the event among
-- them.  A joiner is not monotone in its parts, so the settled tree's
-- facts can fail where these hold: each ancestor is judged against the
-- rows it is read with.  The hole's own facts are its frame's.
module adequacy.Above where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; Timeline)
open import denotation.EmissionSet using (EmissionSet; DenEnv; MapT; module Scan; module Connecting)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; CS; alive; lnS; cutS; mapS; scanS; takeS; flatS; connS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (env; rows; rowsL; pendRows; TakeR; Hot; _≃_; module Flat; module BoundedF; module SwitchF; module ExhaustF)
open import adequacy.Up using (_≈ᴸ_; []; _∷_; ≈ᴸ-refl; ʳ++-≈; row-≃; bounded-≃; switch-≃; exhaust-≃; map-≃; scan-≃; take-≃; conn-≃; ≃-refl)
open import adequacy.Causal using (rows-hot)
open import adequacy.Bound using (Empty; EndLast; Rooted; Roots; G; GL; SrcG; Held; Told; live; ⊥₁)
open import adequacy.Skip using (Since; LeadC; _≈⟨_⟩_)
open import adequacy.Swap using (rooted-≃; empty-≃; endlast-≃; good-hot; live-swap; toldL-swap)

------------------------------------------------------------------------
-- A joiner's rows and facts

-- A joiner's rows over its outer and lanes, by operator.
JR : ∀ {A B} → FlatOp → (A → Pos → EmissionSet B) → EmissionSet A → Bool → ℕ → List A → List (EmissionSet B) → EmissionSet B
JR (mergeᶠ nothing)  L O d n q Ls = Flat.RowT L O d n Ls
JR (mergeᶠ (just m)) L O d n q Ls = BoundedF.RowT m L O d n q Ls
JR switchᶠ           L O d n q Ls = SwitchF.RowT L O d n Ls
JR exhaustᶠ          L O d n q Ls = ExhaustF.RowT L O d n Ls

jr-≃ : ∀ {A B} op (L : A → Pos → EmissionSet B) {O O′ : EmissionSet A} d n q {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′
     → JR op L O d n q Ls ≃ JR op L O′ d n q Ls′
jr-≃ (mergeᶠ nothing)  L d n q eo es = row-≃ L n eo es
jr-≃ (mergeᶠ (just m)) L d n q eo es = bounded-≃ m L eo es
jr-≃ switchᶠ           L d n q eo es = switch-≃ L eo es
jr-≃ exhaustᶠ          L d n q eo es = exhaust-≃ L eo es

-- A joiner's node reads its operator's rows.
rows-jr : ∀ {Γ A B} (ρ : DenEnv Γ) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls
        → rows ρ (flatS op f d n q o ls) ≡ JR op (λ a → pendRows ρ (f a)) (rows ρ o) d n q (rowsL ρ ls)
rows-jr ρ (mergeᶠ nothing)  f d n q o ls = refl
rows-jr ρ (mergeᶠ (just m)) f d n q o ls = refl
rows-jr ρ switchᶠ           f d n q o ls = refl
rows-jr ρ exhaustᶠ          f d n q o ls = refl

-- Nothing queued, or a bounded merge full.
Fresh : ∀ {A : Set} → FlatOp → ℕ → List A → Set
Fresh (mergeᶠ nothing)  n q = q ≡ []
Fresh (mergeᶠ (just m)) n q = (q ≡ []) ⊎ (n ≡ m)
Fresh switchᶠ           n q = q ≡ []
Fresh exhaustᶠ          n q = q ≡ []

fresh-nil : ∀ {A : Set} op n → Fresh {A} op n []
fresh-nil (mergeᶠ nothing)  n = refl
fresh-nil (mergeᶠ (just m)) n = inj₁ refl
fresh-nil switchᶠ           n = refl
fresh-nil exhaustᶠ          n = refl

-- A joiner's facts over its parts' rows: nothing queued past its room,
-- its count, its done outer owing nothing, its parts rooted.
record Join {A B : Set} (op : FlatOp) (d : Bool) (n : ℕ) (q : List A) (nl : ℕ) (O : EmissionSet A) (Ls : List (EmissionSet B)) : Set₁ where
  field
    fresh  : Fresh op n q
    count  : n ≡ nl
    spent  : T d → Empty O
    rooted : Rooted O Ls

join-≃ : ∀ {A B : Set} {op d n q nl} {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′ → Join op d n q nl O Ls → Join op d n q nl O′ Ls′
join-≃ eo es j = record { fresh = fresh ; count = count ; spent = λ t → empty-≃ eo (spent t) ; rooted = rooted-≃ eo es rooted }
  where open Join j

------------------------------------------------------------------------
-- Where a hole sits

IsLn : ∀ {Γ A} → St Γ A → Set
IsLn (lnS _ _) = ⊤
IsLn _         = ⊥

IsCutT : ∀ {Γ A} → St Γ A → Set
IsCutT (cutS true _ _) = ⊤
IsCutT _               = ⊥

LnParent : ∀ {R Γ A} → Ctx R Γ A → Set
LnParent (inLanes _ _ _ _ _ _ _ _ _) = ⊤
LnParent _                           = ⊥

-- A source held while its body subscribes.
HeldIf : ∀ {Γ A} → Maybe Pos → St Γ A → Set₁
HeldIf nothing  s = ⊤₁
HeldIf (just _) s = Held s

------------------------------------------------------------------------
-- The frames above, read through the hole's rows `H`

Anc : ∀ {R Γ A} → Ctx R Γ A → St Γ A → EmissionSet A → Set₁
Anc top                   s H = ⊤₁
Anc (inMap f c)           s H = Anc c (mapS f s) (MapT f H)
Anc (inScan f z c)        s H = Anc c (scanS f z s) (Scan.ScanT f z H)
Anc (inCut true a c)      s H = Anc c (cutS true a s) H
Anc (inCut false a c)     s H = ⊥₁
Anc (inLn true c)         s H = IsCutT s × EndLast H × LnParent c × Anc c (lnS true s) H
Anc (inLn false c)        s H = ⊥₁
Anc (inTake i q w c)      s H = Anc c (takeS i q w s) (TakeR i q w H)
Anc (inOuter op f d n q ls c) s H =
  GL (env c) true ls × Join op d n q (live ls) H (rowsL (env c) ls)
  × Anc c (flatS op f d n q s ls) (JR op (λ a → pendRows (env c) (f a)) H d n q (rowsL (env c) ls))
Anc (inLanes op f d n q o pre post c) s H =
  IsLn s × G (env c) true o × GL (env c) true pre × GL (env c) true post
  × Join op d n q (live (pre ʳ++ s ∷ post)) (rows (env c) o) (rowsL (env c) pre ʳ++ H ∷ rowsL (env c) post)
  × Anc c (flatS op f d n q o (pre ʳ++ s ∷ post)) (JR op (λ a → pendRows (env c) (f a)) (rows (env c) o) d n q (rowsL (env c) pre ʳ++ H ∷ rowsL (env c) post))
Anc (inSrc k b c)         s H =
  HeldIf (CS.bodyAt k) s × G (Hot (env c) H k ∷ᴬ env c) true b × (T (CS.closed k) → Empty H) × (T (CS.closed k) → Told (here refl) b)
  × Anc c (connS k s b) (Connecting.ConnT (CS.connAt k) H (rows (Hot (env c) H k ∷ᴬ env c) b))
Anc (inBody k o c)        s H =
  SrcG (env c) true (CS.bodyAt k) o × (T (CS.closed k) → Empty (rows (env c) o)) × (T (CS.closed k) → Told (here refl) s)
  × Anc c (connS k o s) (Connecting.ConnT (CS.connAt k) (rows (env c) o) H)

-- THE SAME ROWS, THE SAME FRAMES: every frame reads its hole only
-- through its rows.
anc-≃ : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) {H H′ : EmissionSet A} → H ≃ H′ → Anc c s H → Anc c s H′
anc-≃ top                s eq a = a
anc-≃ (inMap f c)        s eq a = anc-≃ c (mapS f s) (map-≃ f eq) a
anc-≃ (inScan f z c)     s eq a = anc-≃ c (scanS f z s) (scan-≃ f z eq) a
anc-≃ (inCut true a′ c)  s eq a = anc-≃ c (cutS true a′ s) eq a
anc-≃ (inCut false a′ c) s eq ()
anc-≃ (inLn true c)      s eq (ct , el , lp , a) = ct , endlast-≃ eq el , lp , anc-≃ c (lnS true s) eq a
anc-≃ (inLn false c)     s eq ()
anc-≃ (inTake i q w c)   s eq a = anc-≃ c (takeS i q w s) (take-≃ i q w eq) a
anc-≃ (inOuter op f d n q ls c) s eq (gl , j , a) =
  gl , join-≃ eq (≈ᴸ-refl (rowsL (env c) ls)) j
  , anc-≃ c (flatS op f d n q s ls) (jr-≃ op (λ x → pendRows (env c) (f x)) d n q eq (≈ᴸ-refl (rowsL (env c) ls))) a
anc-≃ (inLanes op f d n q o pre post c) s eq (il , go , gp , gq , j , a) =
  il , go , gp , gq , join-≃ ≃-refl es j , anc-≃ c (flatS op f d n q o (pre ʳ++ s ∷ post)) (jr-≃ op (λ x → pendRows (env c) (f x)) d n q ≃-refl es) a
  where es = ʳ++-≈ (rowsL (env c) pre) (eq ∷ ≈ᴸ-refl (rowsL (env c) post))
anc-≃ (inSrc k b c)      s eq (h , gb , sp , tl , a) =
  h , good-hot k (env c) b eq true gb , (λ cl → empty-≃ eq (sp cl)) , tl
  , anc-≃ c (connS k s b) (conn-≃ (CS.connAt k) eq (rows-hot k (env c) b eq)) a
anc-≃ (inBody k o c)     s eq (gs , sp , tl , a) = gs , sp , tl , anc-≃ c (connS k o s) (conn-≃ (CS.connAt k) ≃-refl eq) a

------------------------------------------------------------------------
-- A hole swapped for one of the same shape

-- The same place in its parent, the same joiners told: nothing above
-- reads more of a hole.
record Same {Γ A} (s s′ : St Γ A) : Set₁ where
  field
    ln    : IsLn s → IsLn s′
    cut   : IsCutT s → IsCutT s′
    held  : Held s → Held s′
    live≡ : alive s ≡ alive s′
    told  : ∀ {X} (x : X ∈ Γ) → Told x s → Told x s′
open Same

heldIf : ∀ {Γ A} {s s′ : St Γ A} → Same s s′ → ∀ m → HeldIf m s → HeldIf m s′
heldIf sw nothing  h = tt₁
heldIf sw (just _) h = held sw h

anc-swap : ∀ {R Γ A} (c : Ctx R Γ A) {s s′ : St Γ A} {H} → Same s s′ → Anc c s H → Anc c s′ H
anc-swap top                sw a = a
anc-swap (inMap f c)        sw a = anc-swap c (record { ln = λ () ; cut = λ () ; held = λ () ; live≡ = refl ; told = told sw }) a
anc-swap (inScan f z c)     sw a = anc-swap c (record { ln = λ () ; cut = λ () ; held = λ () ; live≡ = refl ; told = told sw }) a
anc-swap (inCut true a′ c)  sw a = anc-swap c (record { ln = λ () ; cut = λ _ → tt ; held = λ () ; live≡ = refl ; told = told sw }) a
anc-swap (inCut false a′ c) sw ()
anc-swap (inLn true c)      sw (ct , el , lp , a) = cut sw ct , el , lp , anc-swap c (record { ln = λ _ → tt ; cut = λ () ; held = λ () ; live≡ = refl ; told = told sw }) a
anc-swap (inLn false c)     sw ()
anc-swap (inTake i q w c)   sw a = anc-swap c (record { ln = λ () ; cut = λ () ; held = λ () ; live≡ = refl ; told = told sw }) a
anc-swap (inOuter op f d n q ls c) sw (gl , j , a) =
  gl , j , anc-swap c (record { ln = λ () ; cut = λ () ; held = λ () ; live≡ = refl ; told = λ x (t , ts) → told sw x t , ts }) a
anc-swap (inLanes op f d n q o pre post c) sw (il , go , gp , gq , j , a) =
  ln sw il , go , gp , gq , record { fresh = Join.fresh j ; count = trans (Join.count j) (live-swap pre (live≡ sw)) ; spent = Join.spent j ; rooted = Join.rooted j }
  , anc-swap c (record { ln = λ () ; cut = λ () ; held = λ () ; live≡ = refl ; told = λ x (t , ts) → t , toldL-swap pre (told sw x) ts }) a
anc-swap (inSrc k b c)      sw (h , gb , sp , tl , a) =
  heldIf sw (CS.bodyAt k) h , gb , sp , tl , anc-swap c (record { ln = λ () ; cut = λ () ; held = λ () ; live≡ = refl ; told = λ x (t , tb) → told sw x t , tb }) a
anc-swap (inBody k o c)     sw (gs , sp , tl , a) =
  gs , sp , (λ cl → told sw (here refl) (tl cl))
  , anc-swap c (record { ln = λ () ; cut = λ () ; held = λ () ; live≡ = refl ; told = λ x (t , tb) → t , told sw (there x) tb }) a

------------------------------------------------------------------------
-- A lane read with fewer rows

-- Lane by lane, each read with no more rows than before.
data _⊒ᴸ_ {B} : List (EmissionSet B) → List (EmissionSet B) → Set₁ where
  []  : [] ⊒ᴸ []
  _∷_ : ∀ {t u Ls Ls′} → (∀ {y e} → u y e → t y e) → Ls ⊒ᴸ Ls′ → (t ∷ Ls) ⊒ᴸ (u ∷ Ls′)

⊒-refl : ∀ {B} (Ls : List (EmissionSet B)) → Ls ⊒ᴸ Ls
⊒-refl []       = []
⊒-refl (_ ∷ Ls) = (λ r → r) ∷ ⊒-refl Ls

⊒-ʳ++ : ∀ {B} (xs : List (EmissionSet B)) {ys ys′} → ys ⊒ᴸ ys′ → (xs ʳ++ ys) ⊒ᴸ (xs ʳ++ ys′)
⊒-ʳ++ []       h = h
⊒-ʳ++ (_ ∷ xs) h = ⊒-ʳ++ xs ((λ r → r) ∷ h)

-- A lane's root roots any fewer of its rows.
roots-⊒ : ∀ {A B} {H : Pos → Set} {X : EmissionSet A} qs {Ls Ls′ : List (EmissionSet B)} → Ls ⊒ᴸ Ls′ → Roots H X qs Ls → Roots H X qs Ls′
roots-⊒ []       []      r = r
roots-⊒ (q ∷ qs) (s ∷ h) ((a , x , w) , nq , rs) = (a , x , λ r → w (s r)) , nq , roots-⊒ qs h rs
roots-⊒ []       (_ ∷ _) ()
roots-⊒ (_ ∷ _)  []      ()

rooted-⊒ : ∀ {A B} {O : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → Ls ⊒ᴸ Ls′ → Rooted O Ls → Rooted O Ls′
rooted-⊒ h r = record { H = Rooted.H r ; X = Rooted.X r ; p₀ = Rooted.p₀ r ; inv = Rooted.inv r ; sub = Rooted.sub r
                      ; qs = Rooted.qs r ; roots = roots-⊒ (Rooted.qs r) h (Rooted.roots r) }

-- An outer read with fewer rows stays inside its entry.
rooted-sub : ∀ {A B} {O O′ : EmissionSet A} {Ls : List (EmissionSet B)} → (∀ {q e} → O′ q e → O q e) → Rooted O Ls → Rooted O′ Ls
rooted-sub h r = record { H = Rooted.H r ; X = Rooted.X r ; p₀ = Rooted.p₀ r ; inv = Rooted.inv r ; sub = λ x → Rooted.sub r (h x)
                        ; qs = Rooted.qs r ; roots = Rooted.roots r }

------------------------------------------------------------------------
-- A skip at the lead, read above

postulate
  -- A HOLE'S SKIP AT THE LEAD, READ ABOVE: frames read through a hole's
  -- rows read through any rows agreeing with them but for a skip at the
  -- lead, every row of both at or past it.  Every frame's map is causal,
  -- so the two readings above agree but for rows at or past the lead.
  -- Open is a joiner frame's `Rooted` entry, frozen before the lead: a
  -- skip one reading gains at the lead must already be among the entry's
  -- rows, which the settled-entry check finds failing where a joiner
  -- re-reads a live connect binder.
  anc-≈ : ∀ {R Γ A} (c : Ctx R Γ A) {s : St Γ A} {t u : EmissionSet A} {p} → LeadC c p → Since p t → Since p u → t ≈⟨ p ⟩ u → Anc c s t → Anc c s u
