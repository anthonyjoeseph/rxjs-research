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
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; Timeline)
open import denotation.EmissionSet using (EmissionSet; DenEnv; MapT; module Scan; module Connecting)
open import denotation.Laws.Modulus using (≺→≼)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; CS; alive; lnS; cutS; mapS; scanS; takeS; flatS; connS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (Admits; env; rows; rowsL; pendRows; TakeR; Hot; Echoing; Each; _≃_; module Flat; module BoundedF; module SwitchF; module ExhaustF)
open import adequacy.Up using (_≈ᴸ_; []; _∷_; ≈ᴸ-refl; ʳ++-≈; all-ʳ++; row-≃; bounded-≃; switch-≃; exhaust-≃; map-≃; scan-≃; take-≃; conn-≃; echo-≃; ≃-refl)
open import adequacy.Causal using (rows-hot)
open import adequacy.Bound using (Empty; EndLast; Rooted; Roots; G; GL; SrcG; Held; Told; live; ⊥₁)
open import adequacy.Skip using (Since; LeadC; After; _≈⟨_⟩_; ≈-sym; ≈-refl; end-≈; _≈ᴸ⟨_⟩_; ≈ᴸ-hole; after-since; trunc-≈;
                                  since-map; map-≈; since-scan; scan-≈; since-take; take-≈; since-conn; conn-≈;
                                  since-row; flat-≈; since-bounded; bounded-≈; since-switch; switch-≈; since-exhaust; exhaust-≈)
  renaming (≈ᴸ-refl to ≈ᴸ-refl⟨⟩; _∷_ to _∷≈_)
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
  HeldIf (CS.bodyAt k) s × G (Hot H k ∷ᴬ env c) true b × (T (CS.closed k) → Empty H) × (T (CS.closed k) → Told (here refl) b)
  × Admits k × Anc c (connS k s b) (Connecting.ConnT (CS.connAt k) (Echoing k H) (rows (Hot H k ∷ᴬ env c) b))
Anc (inBody k o c)        s H =
  SrcG (env c) true (CS.bodyAt k) o × (T (CS.closed k) → Empty (rows (env c) o)) × (T (CS.closed k) → Told (here refl) s)
  × Admits k × Anc c (connS k o s) (Connecting.ConnT (CS.connAt k) (Echoing k (rows (env c) o)) H)

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
anc-≃ (inSrc k b c)      s eq (h , gb , sp , tl , ok , a) =
  h , good-hot k (env c) b eq true gb , (λ cl → empty-≃ eq (sp cl)) , tl , ok
  , anc-≃ c (connS k s b) (conn-≃ (CS.connAt k) (echo-≃ k eq) (rows-hot k (env c) b eq)) a
anc-≃ (inBody k o c)     s eq (gs , sp , tl , ok , a) = gs , sp , tl , ok , anc-≃ c (connS k o s) (conn-≃ (CS.connAt k) ≃-refl eq) a

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
anc-swap (inSrc k b c)      sw (h , gb , sp , tl , ok , a) =
  heldIf sw (CS.bodyAt k) h , gb , sp , tl , ok , anc-swap c (record { ln = λ () ; cut = λ () ; held = λ () ; live≡ = refl ; told = λ x (t , tb) → told sw x t , tb }) a
anc-swap (inBody k o c)     sw (gs , sp , tl , ok , a) =
  gs , sp , (λ cl → told sw (here refl) (tl cl)) , ok
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

-- An end lies past the lead, so a skip at the lead keeps it last.
endlast-≈ : ∀ {A} {t u : EmissionSet A} {p} → Since p t → t ≈⟨ p ⟩ u → EndLast t → EndLast u
endlast-≈ st eq el ce y with _≈⟨_⟩_.bwd eq y
... | inj₁ x          = el (end-≈ (≈-sym eq) ce) x
... | inj₂ (refl , _) = st (end-≈ (≈-sym eq) ce)

-- A joiner's rows over parts agreeing but for a skip at the lead, each
-- part at or past it.
jr-≈ : ∀ {A B} op (L : A → Pos → EmissionSet B) {O O′ : EmissionSet A} d n q {Ls Ls′ : List (EmissionSet B)} {p}
     → Since p O → Since p O′ → Each (Since p) Ls → Each (Since p) Ls′ → O ≈⟨ p ⟩ O′ → Ls ≈ᴸ⟨ p ⟩ Ls′
     → Since p (JR op L O d n q Ls) × Since p (JR op L O′ d n q Ls′) × JR op L O d n q Ls ≈⟨ p ⟩ JR op L O′ d n q Ls′
jr-≈ (mergeᶠ nothing) L {O} {O′} d n q {Ls} {Ls′} so so′ sl sl′ eo es =
  since-row L {d = d} {n = n} O Ls so sl , since-row L {d = d} {n = n} O′ Ls′ so′ sl′ , trunc-≈ (flat-≈ L {d = d} {n = n} Ls Ls′ eo es)
jr-≈ (mergeᶠ (just m)) L {O} {O′} d n q {Ls} {Ls′} so so′ sl sl′ eo es =
  since-bounded m L {d = d} {n = n} {Qu = q} O Ls so sl , since-bounded m L {d = d} {n = n} {Qu = q} O′ Ls′ so′ sl′
  , bounded-≈ m L {d = d} {n = n} {Qu = q} Ls Ls′ eo es
jr-≈ switchᶠ L {O} {O′} d n q {Ls} {Ls′} so so′ sl sl′ eo es =
  since-switch L {d = d} {n = n} O Ls so sl , since-switch L {d = d} {n = n} O′ Ls′ so′ sl′ , switch-≈ L {d = d} {n = n} Ls Ls′ eo es
jr-≈ exhaustᶠ L {O} {O′} d n q {Ls} {Ls′} so so′ sl sl′ eo es =
  since-exhaust L {d = d} {n = n} O Ls so sl , since-exhaust L {d = d} {n = n} O′ Ls′ so′ sl′ , exhaust-≈ L {d = d} {n = n} Ls Ls′ eo es

postulate
  -- AN OUTER'S SKIP AT THE LEAD KEEPS ITS JOINER'S FACTS: a done outer
  -- still owes nothing, and the skip lies inside the outer's frozen entry.
  -- Open is that entry: the settled-entry check finds a joiner's outer
  -- growing past it where a `sub` re-reads a live connect binder.
  join-≈-outer : ∀ {A B : Set} {op d n q nl} {t u : EmissionSet A} {Ls : List (EmissionSet B)} {p}
               → Each (After p) Ls → Since p t → Since p u → t ≈⟨ p ⟩ u → Join op d n q nl t Ls → Join op d n q nl u Ls

  -- A LANE'S SKIP AT THE LEAD KEEPS ITS JOINER'S FACTS: the skip lies
  -- under the lane's root.
  join-≈-lane : ∀ {A B : Set} {op d n q nl} {O : EmissionSet A} (pre : List (EmissionSet B)) {post} {t u : EmissionSet B} {p}
              → After p O → Each (After p) pre → Each (After p) post → Since p t → Since p u → t ≈⟨ p ⟩ u
              → Join op d n q nl O (pre ʳ++ t ∷ post) → Join op d n q nl O (pre ʳ++ u ∷ post)

  -- A SOURCE'S SKIP AT THE LEAD, READ ABOVE ITS CONNECT: its body's facts
  -- hold over the binder with the skip, and the frames above read the
  -- connect with it as without, the connect showing it a skip or a pin
  -- and each joiner a skip where it joined (`adequacy.Skip.src-vis`).
  anc-≈-src : ∀ {R Γ X B} (k : CS Γ X) (b : St (X ∷ Γ) B) (c : Ctx R Γ B) {s : St Γ X} {t u : EmissionSet X} {p}
            → LeadC (inSrc k b c) p → Since p t → Since p u → t ≈⟨ p ⟩ u → Anc (inSrc k b c) s t → Anc (inSrc k b c) s u

-- A HOLE'S SKIP AT THE LEAD, READ ABOVE: frames read through a hole's
-- rows read through any rows agreeing with them but for a skip at the
-- lead, every row of both at or past it.  Every frame's map is causal,
-- so the readings above agree but for that skip; a joiner's entry and a
-- connect's binder are the frames that must hold it.
anc-≈ : ∀ {R Γ A} (c : Ctx R Γ A) {s : St Γ A} {t u : EmissionSet A} {p} → LeadC c p → Since p t → Since p u → t ≈⟨ p ⟩ u → Anc c s t → Anc c s u
anc-≈ top                 ld st su eq a = a
anc-≈ (inMap f c)         ld st su eq a = anc-≈ c ld (since-map f st) (since-map f su) (map-≈ f eq) a
anc-≈ (inScan f z c)      ld st su eq a = anc-≈ c ld (since-scan f z st) (since-scan f z su) (scan-≈ f z eq) a
anc-≈ (inCut true a′ c)   ld st su eq a = anc-≈ c ld st su eq a
anc-≈ (inCut false a′ c)  ld st su eq ()
anc-≈ (inLn true c)       ld st su eq (ct , el , lp , a) = ct , endlast-≈ st eq el , lp , anc-≈ c ld st su eq a
anc-≈ (inLn false c)      ld st su eq ()
anc-≈ (inTake i q w c)    (lt , ld) st su eq a = anc-≈ c ld (since-take i q w lt st) (since-take i q w lt su) (take-≈ i q w eq) a
anc-≈ (inOuter op f d n q ls c) {t = t} {u} (al , ld) st su eq (gl , j , a) =
  gl , join-≈-outer al st su eq j , anc-≈ c ld (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) a
  where
    Ls = rowsL (env c) ls
    sl = after-since Ls al
    r  = jr-≈ op (λ x → pendRows (env c) (f x)) d n q st su sl sl eq (≈ᴸ-refl⟨⟩ Ls)
anc-≈ (inLanes op f d n q o pre post c) {t = t} {u} (ao , apre , apost , ld) st su eq (il , go , gp , gq , j , a) =
  il , go , gp , gq , join-≈-lane (rowsL ρ pre) ao apre apost st su eq j
  , anc-≈ c ld (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) a
  where
    ρ   = env c
    so  = λ {q} {e} r → ≺→≼ {_} {q} (ao {q} {e} r)
    slt = all-ʳ++ (rowsL ρ pre) (after-since (rowsL ρ pre) apre) (st , after-since (rowsL ρ post) apost)
    slu = all-ʳ++ (rowsL ρ pre) (after-since (rowsL ρ pre) apre) (su , after-since (rowsL ρ post) apost)
    r   = jr-≈ op (λ x → pendRows ρ (f x)) d n q so so slt slu ≈-refl (≈ᴸ-hole (rowsL ρ pre) (eq ∷≈ ≈ᴸ-refl⟨⟩ (rowsL ρ post)))
anc-≈ (inSrc k b c)       ld st su eq a = anc-≈-src k b c ld st su eq a
anc-≈ (inBody k o c) {t = t} {u} (ao , ld) st su eq (gs , sp , tl , ok , a) =
  gs , sp , tl , ok , anc-≈ c ld (since-conn (CS.connAt k) _ t ae st) (since-conn (CS.connAt k) _ u ae su) (conn-≈ (CS.connAt k) _ eq) a
  where
    ae = λ {q} {e} r → ao {q} {e} (proj₁ r)
