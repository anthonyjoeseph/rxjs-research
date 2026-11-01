{-# OPTIONS --guardedness #-}

-- A SOURCE'S FEED KEEPS APART: what a source's step at `p` queues for
-- its subject's live joiners sits under `p`, one subtree per joiner.
-- Each joiner joined before `p` — the run was past its subscription —
-- and no two joined at one position, so the subtrees are apart and all
-- inside the run.
module adequacy.Apart.Feed where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; [_]; _++_; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ; map-++)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-refl; ↭-trans; ↭-reflexive; prep; swap)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using () renaming (++⁺ to ↭-++; ++⁺ˡ to ↭-++ˡ; ++⁺ʳ to ↭-++ʳ)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_; ⊆-refl)
open import Data.List.Relation.Binary.Sublist.Propositional.Properties using (All-resp-⊆) renaming (++⁺ to ⊆-++; ++⁺ˡ to ⊆-++ˡ; ++⁺ʳ to ⊆-++ʳ)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import denotation.Events using (Pos; last; _<ᵖ_) renaming (sub to subᴾ)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; CS; Ev; nx; cp; plug; feed; feedL; inbox; queued; same?)
open import adequacy.Stamped using (Ix)
open import adequacy.Apart.Cone using (cone-apart)
open import adequacy.Apart.Region using (Rg; cn; bk; cl; Sep; Sub)
open import adequacy.Apart.Items using (items; itemsL; ibI; attI; oweI; csI; lhs; plug-items; ap-⊆)
open import adequacy.Apart.Kit using (W; grow; pull; sub-child; none)

------------------------------------------------------------------------
-- What a feed queues

-- What a joiner joined at `j` is newly owed for a step at `p`.
newR : ∀ {A} → Pos → Pos → Ev A → List Rg
newR j p (nx a) = if j <ᵖ p then [ cn (p ++ [ subᴾ j ]) ] else []
newR j p cp     = [ cn (if j <ᵖ p then p ++ [ subᴾ j ] else j ++ [ last ]) ]

nw : ∀ {A} → Pos → Ev A → List Pos → List Rg
nw p e []       = []
nw p e (j ∷ js) = newR j p e ++ nw p e js

nw-++ : ∀ {A} p (e : Ev A) xs {ys} → nw p e (xs ++ ys) ≡ nw p e xs ++ nw p e ys
nw-++ p e []       = refl
nw-++ p e (j ∷ xs) {ys} = trans (cong (newR j p e ++_) (nw-++ p e xs)) (sym (++-assoc (newR j p e) (nw p e xs) (nw p e ys)))

-- The live joiners a binder's step reaches.
mutual
  joiners : ∀ {Γ X A} → X ∈ Γ → St Γ A → List Pos
  joiners i (joinS j true x ib) with same? i x
  ... | just refl = [ j ]
  ... | nothing   = []
  joiners i (mapS f s)              = joiners i s
  joiners i (scanS f z s)           = joiners i s
  joiners i (cutS l a s)            = joiners i s
  joiners i (lnS b s)               = joiners i s
  joiners i (takeS v q w s)         = joiners i s
  joiners i (flatS op f d n q o ls) = joiners i o ++ joinersL i ls
  joiners i (connS k o b)           = joiners i o ++ joiners (there i) b
  joiners i s                       = []

  joinersL : ∀ {Γ X A} → X ∈ Γ → List (St Γ A) → List Pos
  joinersL i []       = []
  joinersL i (s ∷ ls) = joiners i s ++ joinersL i ls

------------------------------------------------------------------------
-- A feed adds only what it queues

private
  inbox-items : ∀ {A} q (e : Ev A) ib → ibI (inbox (q , e) ib) ↭ cn q ∷ ibI ib
  inbox-items q e []              = ↭-refl
  inbox-items q e ((r , e′) ∷ ib) with r <ᵖ q
  ... | true  = ↭-trans (prep (cn r) (inbox-items q e ib)) (swap (cn r) (cn q) ↭-refl)
  ... | false = ↭-refl

  queued-items : ∀ {A} j p (e : Ev A) ib → ibI (queued j p e ib) ↭ newR j p e ++ ibI ib
  queued-items j p (nx a) ib with j <ᵖ p
  ... | true  = inbox-items _ (nx a) ib
  ... | false = ↭-refl
  queued-items j p cp ib = inbox-items _ cp ib

  -- Two parts' additions, gathered.
  inter : ∀ (A B C D : List Rg) → (A ++ B) ++ (C ++ D) ↭ (A ++ C) ++ (B ++ D)
  inter A B C D =
    ↭-trans (↭-reflexive (++-assoc A B (C ++ D)))
      (↭-trans (↭-++ˡ A (pull B C D)) (↭-reflexive (sym (++-assoc A C (B ++ D)))))

mutual
  feed-items : ∀ {Γ X A} (i : X ∈ Γ) p (e : Ev X) (s : St Γ A) → items (feed i p e s) ↭ nw p e (joiners i s) ++ items s
  feed-items i p e (joinS j true x ib) with same? i x
  ... | just refl = ↭-trans (↭-++ʳ [ bk j ] (queued-items j p e ib))
                      (↭-reflexive (trans (++-assoc (newR j p e) (ibI ib) [ bk j ])
                                          (cong (_++ (ibI ib ++ [ bk j ])) (sym (++-identityʳ (newR j p e))))))
  ... | nothing   = ↭-refl
  feed-items i p e (joinS j false x ib)    = ↭-refl
  feed-items i p e (pend o q)              = ↭-refl
  feed-items i p e (coldS b l)             = ↭-refl
  feed-items i p e (ofS n q xs)            = ↭-refl
  feed-items i p e doneS                   = ↭-refl
  feed-items i p e (mapS f s)              = feed-items i p e s
  feed-items i p e (scanS f z s)           = feed-items i p e s
  feed-items i p e (cutS l a s)            = ↭-trans (↭-++ˡ (attI a) (feed-items i p e s)) (pull (attI a) _ (items s))
  feed-items i p e (lnS b s)               = feed-items i p e s
  feed-items i p e (takeS v q w s)         = ↭-trans (↭-++ˡ (oweI w) (feed-items i p e s)) (pull (oweI w) _ (items s))
  feed-items i p e (flatS op f d n q o ls) rewrite nw-++ p e (joiners i o) {joinersL i ls} =
    ↭-trans (↭-++ (feed-items i p e o) (feedL-items i p e ls)) (inter (nw p e (joiners i o)) (items o) (nw p e (joinersL i ls)) (itemsL ls))
  feed-items i p e (connS k o b) rewrite nw-++ p e (joiners i o) {joiners (there i) b} =
    ↭-trans (↭-++ˡ (csI k) (↭-trans (↭-++ (feed-items i p e o) (feed-items (there i) p e b))
                             (inter (nw p e (joiners i o)) (items o) (nw p e (joiners (there i) b)) (items b))))
      (pull (csI k) (nw p e (joiners i o) ++ nw p e (joiners (there i) b)) (items o ++ items b))

  feedL-items : ∀ {Γ X A} (i : X ∈ Γ) p (e : Ev X) (ls : List (St Γ A)) → itemsL (feedL i p e ls) ↭ nw p e (joinersL i ls) ++ itemsL ls
  feedL-items i p e []       = ↭-refl
  feedL-items i p e (s ∷ ls) rewrite nw-++ p e (joiners i s) {joinersL i ls} =
    ↭-trans (↭-++ (feed-items i p e s) (feedL-items i p e ls)) (inter (nw p e (joiners i s)) (items s) (nw p e (joinersL i ls)) (itemsL ls))

-- Every joiner fed is owed in the tree, live.
mutual
  joiners-⊆ : ∀ {Γ X A} (i : X ∈ Γ) (s : St Γ A) → map bk (joiners i s) ⊆ items s
  joiners-⊆ i (joinS j true x ib) with same? i x
  ... | just refl = ⊆-++ˡ (ibI ib) ⊆-refl
  ... | nothing   = none (ibI ib ++ [ bk j ])
  joiners-⊆ i (joinS j false x ib)    = none _
  joiners-⊆ i (pend o q)              = none _
  joiners-⊆ i (coldS b l)             = none _
  joiners-⊆ i (ofS n q xs)            = none _
  joiners-⊆ i doneS                   = none _
  joiners-⊆ i (mapS f s)              = joiners-⊆ i s
  joiners-⊆ i (scanS f z s)           = joiners-⊆ i s
  joiners-⊆ i (cutS l a s)            = ⊆-++ˡ (attI a) (joiners-⊆ i s)
  joiners-⊆ i (lnS b s)               = joiners-⊆ i s
  joiners-⊆ i (takeS v q w s)         = ⊆-++ˡ (oweI w) (joiners-⊆ i s)
  joiners-⊆ i (flatS op f d n q o ls) =
    subst (_⊆ items o ++ itemsL ls) (sym (map-++ bk (joiners i o) (joinersL i ls))) (⊆-++ (joiners-⊆ i o) (joinersL-⊆ i ls))
  joiners-⊆ i (connS k o b)           =
    ⊆-++ˡ (csI k) (subst (_⊆ items o ++ items b) (sym (map-++ bk (joiners i o) (joiners (there i) b))) (⊆-++ (joiners-⊆ i o) (joiners-⊆ (there i) b)))

  joinersL-⊆ : ∀ {Γ X A} (i : X ∈ Γ) (ls : List (St Γ A)) → map bk (joinersL i ls) ⊆ itemsL ls
  joinersL-⊆ i []       = ⊆-refl
  joinersL-⊆ i (s ∷ ls) =
    subst (_⊆ items s ++ itemsL ls) (sym (map-++ bk (joiners i s) (joinersL i ls))) (⊆-++ (joiners-⊆ i s) (joinersL-⊆ i ls))

------------------------------------------------------------------------
-- Every joiner fed joined before the run

module _ (p : Pos) where
  private
    under : Pos → Rg
    under j = cn (p ++ [ subᴾ j ])

  nw-low : ∀ {A} (e : Ev A) js → All (λ j → j <ᵖ p ≡ true) js → nw p e js ≡ map under js
  nw-low e      []       []         = refl
  nw-low (nx a) (j ∷ js) (lt ∷ lts) rewrite lt = cong (under j ∷_) (nw-low (nx a) js lts)
  nw-low cp     (j ∷ js) (lt ∷ lts) rewrite lt = cong (under j ∷_) (nw-low cp js lts)

  -- Joiners at distinct positions, owed apart.
  apart : Ix p → ∀ js → AllPairs Sep (map bk js) → AllPairs Sep (map under js)
  apart hp []       []         = []
  apart hp (j ∷ js) (hj ∷ hjs) = row js hj ∷ apart hp js hjs
    where
      row : ∀ js → All (Sep (bk j)) (map bk js) → All (Sep (under j)) (map under js)
      row []        []          = []
      row (j′ ∷ js) (h ∷ hs) = ((λ y c c′ → cone-apart hp ne c c′) , (λ y c c′ → cone-apart hp (λ e → ne (sym e)) c c′)) ∷ row js hs
        where
          ne : subᴾ j ≡ subᴾ j′ → ⊥
          ne refl = proj₁ h refl

  inside : Ix p → ∀ js → All (λ n → Sub n (cl p)) (map under js)
  inside hp []       = []
  inside hp (j ∷ js) = sub-child (subᴾ j) hp ∷ inside hp js

  lows : ∀ js → All (Sep (cl p)) (map bk js) → All (λ j → j <ᵖ p ≡ true) js
  lows []       []       = []
  lows (j ∷ js) (h ∷ hs) = proj₁ h ∷ lows js hs

------------------------------------------------------------------------
-- The feed

feed-ap : ∀ {R Γ X B} (c : Ctx R Γ B) (k k′ : CS Γ X) (s : St Γ X) (b : St (X ∷ Γ) B) {p} (e : Ev X) → Ix p
        → csI k′ ≡ csI k → W c (connS k s b) [ cl p ] → W c (connS k′ s (feed (here refl) p e b)) []
feed-ap c k k′ s b {p} e hp ek h@(hcl ∷ hL) =
  grow c {t = connS k s b} {t′ = connS k′ s (feed (here refl) p e b)} p [] fresh [] (items (connS k s b)) ↭-refl perm
    (inside p hp js) (apart p hp js (ap-⊆ sub hL)) h
  where
    js = joiners (here refl) b
    fresh = map (λ j → cn (p ++ [ subᴾ j ])) js
    L = items (plug c (connS k s b))

    sub : map bk js ⊆ L
    sub = subst (map bk js ⊆_) (sym (plug-items c (connS k s b)))
            (⊆-++ˡ (lhs c) (⊆-++ʳ _ (⊆-++ˡ (csI k) (⊆-++ˡ (items s) (joiners-⊆ (here refl) b)))))

    low : nw p e js ≡ fresh
    low = nw-low p e js (lows p js (All-resp-⊆ sub hcl))

    perm : csI k′ ++ items s ++ items (feed (here refl) p e b) ↭ fresh ++ csI k ++ items s ++ items b
    perm rewrite ek =
      ↭-trans (↭-++ˡ (csI k) (↭-++ˡ (items s) (subst (λ z → items (feed (here refl) p e b) ↭ z ++ items b) low (feed-items (here refl) p e b))))
        (↭-trans (↭-reflexive (sym (++-assoc (csI k) (items s) (fresh ++ items b))))
          (↭-trans (pull (csI k ++ items s) fresh (items b)) (↭-reflexive (cong (fresh ++_) (++-assoc (csI k) (items s) (items b))))))
