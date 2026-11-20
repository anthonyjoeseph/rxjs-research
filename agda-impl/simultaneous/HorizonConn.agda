{-# OPTIONS --guardedness #-}

-- A CONNECT OVER CORRESPONDING PARTS CORRESPONDS.  The plain connect's
-- source and body each correspond to the elaborated connect's, the body
-- seeing the source's rows as its environment; then the two connects'
-- boundaries correspond (`ConnPair.corr`).
--
-- A connect's own rows are its body's, at their places, and its echoes,
-- each a source row's first child; its pins are no row.  So against any
-- pair the body's rows and the source's cut alike, a connect row orders
-- as its part's (`ConnPair.lift`): an echo as its source row, since
-- nothing lies between a position and its first child but what is under
-- that child.
--
-- A body boundary has the body's partner.  A source boundary has the
-- source's, kept alike: in the burst on both sides together, held by the
-- connect itself, whose position orders against the connect's rows and
-- the environment alike; past it, echoed while the body is alive on both
-- sides together, since the body's ends are each other's images and the
-- body's rows cut the pair alike (`ConnPair.al→`, `ConnPair.al←`).
--
-- WHAT THE PARTS OWE, as parameters: their correspondences, the body's
-- partners cutting its source alike along the source's map (`SrcCut`);
-- the body's rows cut each source boundary pair alike (`body-src`); the burst holds partners together (`home→`,
-- `home←`); the body's ends correspond; rows lie past the connect, and
-- the environment cuts the two connects alike (`env-p`); and the gaps
-- every former's boundaries keep from its rows.
module simultaneous.HorizonConn where

open import Data.Bool using (T; not)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; [_])
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_)

open import denotation.Position using (Pos; inside; ix; _⊕_)
open import denotation.EmissionSet using (Ev; end; EmissionSet; _≺_; _≼_; module Connecting)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans; ≺-absurd; ≺→≼; ≼-or-≻; ≼-split)
open import denotation.Laws.Worlds using (_⊑_; ⊑-refl)
open import simultaneous.Horizon using (Tag; free; held; module Cuts; module ConnB; not-T; T-not)
open import simultaneous.HorizonCorr using (Btw; PB; Own; OwnPut; _∪_; _∪²_; module Inter; first-child; ix0-first)

-- A boundary, or the connect a held one waits on.
Mark : (Pos → Tag → Set) → Pos → Set
Mark Bd z = Σ Pos λ b → Σ Tag λ g → Bd b g × (z ≡ b ⊎ g ≡ held z)

mark : ∀ {Bd : Pos → Tag → Set} {b g} → Bd b g → Mark Bd b
mark {b = b} {g} bd = b , g , bd , inj₁ refl

mark-q : ∀ {Bd : Pos → Tag → Set} {b q} → Bd b (held q) → Mark Bd q
mark-q {b = b} {q} bd = b , held q , bd , inj₂ refl

retarget : ∀ {k z z* w w′} → w′ ≡ w → (k ≺ z → w ≺ z*) × (w ≺ z* → k ≺ z) → (k ≺ z → w′ ≺ z*) × (w′ ≺ z* → k ≺ z)
retarget refl x = x

module ConnPair {A B X Y : Set} (N : ℕ) (p p* : Pos)
  (σ : ℕ → EmissionSet A) (β : ℕ → EmissionSet B) (Bdσ Bdβ : ℕ → Pos → Tag → Set)
  (Bσ : Cuts.Bounded σ Bdσ) (Bβ : Cuts.Bounded β Bdβ)
  (σ-out : ∀ {N b g} → Bdσ N b g → b ≺ p ⊎ (p ⊕ [ ix 1 ]) ≺ b)
  (σ-held : ∀ {N b q} → Bdσ N b (held q) → T (inside (p ⊕ [ ix 1 ]) b) → (p ⊕ [ ix 1 ]) ≼ q)
  (β-after : ∀ {N c} → β N c end → p ≺ c)
  (σ* : ℕ → EmissionSet X) (β* : ℕ → EmissionSet Y) (Bdσ* Bdβ* : ℕ → Pos → Tag → Set)
  (Bσ* : Cuts.Bounded σ* Bdσ*) (Bβ* : Cuts.Bounded β* Bdβ*)
  (σ-out* : ∀ {N b g} → Bdσ* N b g → b ≺ p* ⊎ (p* ⊕ [ ix 1 ]) ≺ b)
  (σ-held* : ∀ {N b q} → Bdσ* N b (held q) → T (inside (p* ⊕ [ ix 1 ]) b) → (p* ⊕ [ ix 1 ]) ≼ q)
  (β-after* : ∀ {N c} → β* N c end → p* ≺ c)
  -- the environment, and each part's map, late rows and placements
  (Env : Pos → Set) (EnvPut : Pos → Pos → Set)
  (φσ φβ φc : Pos → Pos) (Lσ Lβ Lc : Pos → Set) (Pσ Pβ Pc : Pos → Pos → Set)
  where
  module P = ConnB p σ β Bdσ Bdβ Bσ Bβ σ-out σ-held β-after
  module E = ConnB p* σ* β* Bdσ* Bdβ* Bσ* Bβ* σ-out* σ-held* β-after*

  SrcRow : Pos → Set
  SrcRow = Own (σ N) Lσ ∪ Env

  SrcPut : Pos → Pos → Set
  SrcPut = OwnPut (σ N) Pσ ∪² EnvPut

  -- The body's environment: its source, as its hot, and the connect's,
  -- each read along the source's map.
  SrcCut : Pos → Pos → Set
  SrcCut z z* = Btw SrcRow φσ z z* × PB SrcPut z z*

  ConnRow : Pos → Set
  ConnRow = Own (P.Cc N) Lc ∪ Env

  ConnPut : Pos → Pos → Set
  ConnPut = OwnPut (P.Cc N) Pc ∪² EnvPut

  module IS = Inter SrcRow φσ SrcPut (Bdσ N) (Bdσ* N)
  module IB = Inter (Own (β N) Lβ) φβ (OwnPut (β N) Pβ) (Bdβ N) (Bdβ* N)
  module IC = Inter ConnRow φc ConnPut (P.CBd N) (E.CBd N)

  r r* : Pos
  r  = p ⊕ [ ix 1 ]
  r* = p* ⊕ [ ix 1 ]

  module Pair
    (Cσ : IS.BCorr) (Cβ : IB.BCorrX SrcCut)
    -- one map: the connect reads its body's rows and environment as they
    -- do, an echo under its row's
    (φc-body : ∀ {k e} → β N k e → φc k ≡ φβ k)
    (φc-echo : ∀ {k e} → σ N k e → φc (k ⊕ [ ix 0 ]) ≡ φσ k ⊕ [ ix 0 ])
    (φc-env : ∀ {k} → Env k → φc k ≡ φσ k)
    (late-body : ∀ {k} → Lβ k → Lc k)
    (late-echo : ∀ {k} → Lσ k → Lc (k ⊕ [ ix 0 ]))
    (put-split : ∀ {k e l} → P.Cc N k e → Pc k l
               → (Σ (Ev B) λ e′ → β N k e′ × Pβ k l)
               ⊎ (Σ Pos λ j → Σ (Ev A) λ e′ → Σ Pos λ l₀ → σ N j e′ × k ≡ j ⊕ [ ix 0 ] × Pσ j l₀ × l ≡ l₀ ⊕ [ ix 0 ]))
    -- a row's image and a late row's placement are elaborated rows
    (img : ∀ {k} → Own (P.Cc N) Lc k → Σ (Ev Y) (E.Cc N (φc k)))
    (put-row : ∀ {k e l} → P.Cc N k e → Pc k l → Σ (Ev Y) (E.Cc N l))
    -- no connect row lies over a source boundary, or a connect a boundary waits on
    (gap-src  : ∀ {b g y e} → Bdσ N b g → P.Cc N y e → ¬ y ⊑ b)
    (gap-src* : ∀ {b g y e} → Bdσ* N b g → E.Cc N y e → ¬ y ⊑ b)
    (held-src  : ∀ {b q y e} → Bdσ N b (held q) → P.Cc N y e → ¬ y ⊑ q)
    (held-src* : ∀ {b q y e} → Bdσ* N b (held q) → E.Cc N y e → ¬ y ⊑ q)
    (held-body  : ∀ {b q y e} → Bdβ N b (held q) → P.Cc N y e → ¬ y ⊑ q)
    (held-body* : ∀ {b q y e} → Bdβ* N b (held q) → E.Cc N y e → ¬ y ⊑ q)
    -- the body's rows cut each source mark pair alike
    (body-src : ∀ {z z*} → Mark (Bdσ N) z → Mark (Bdσ* N) z* → IS.Between z z* → Btw (Own (β N) Lβ) φβ z z*)
    (body-src-put : ∀ {z z*} → Mark (Bdσ N) z → Mark (Bdσ* N) z* → IS.PutBefore z z* → PB (OwnPut (β N) Pβ) z z*)
    -- the burst holds partners together
    (home→ : ∀ {b b* g g*} → Bdσ N b g → Bdσ* N b* g* → IS.Between b b* → T (inside r b) → T (inside r* b*))
    (home← : ∀ {b b* g g*} → Bdσ N b g → Bdσ* N b* g* → IS.Between b b* → T (inside r* b*) → T (inside r b))
    -- the body's ends are each other's images
    (end→ : ∀ {c} → β N c end → ¬ Lβ c × β* N (φβ c) end)
    (end← : ∀ {c*} → β* N c* end → Σ Pos λ c → β N c end × ¬ Lβ c × c* ≡ φβ c)
    -- the connect's rows lie past it; the environment cuts the two alike
    (rows-after  : ∀ {k e} → P.Cc N k e → p ≺ k)
    (rows-after* : ∀ {k e} → E.Cc N k e → p* ≺ k)
    (env-p : Btw Env φc p p*)
    where
    open Inter.BCorr Cσ renaming (to to toσ; from to fromσ)
    open Inter.BCorrX Cβ renaming (to to toβ; from to fromβ)

    gapc : ∀ {b g y e} → P.CBd N b g → P.Cc N y e → ¬ y ⊑ b
    gapc cb y = proj₂ (P.gap-c cb y)

    gapc* : ∀ {b g y e} → E.CBd N b g → E.Cc N y e → ¬ y ⊑ b
    gapc* cb y = proj₂ (E.gap-c cb y)

    -- A CONNECT ROW ORDERS AS ITS PART'S ROW.
    lift : ∀ {z z*} → Btw (Own (β N) Lβ) φβ z z* → Btw SrcRow φσ z z*
         → (∀ {y e} → P.Cc N y e → ¬ y ⊑ z) → (∀ {y e} → E.Cc N y e → ¬ y ⊑ z*)
         → Btw ConnRow φc z z*
    lift {z} {z*} bb bs ng ng* {k} (inj₂ en) = retarget {k} {z} {z*} (φc-env en) (bs (inj₂ en))
    lift {z} {z*} bb bs ng ng* {k} (inj₁ (e , Connecting.body x , un , nl)) = retarget {k} {z} {z*} (φc-body x) (bb (e , x , un , λ l → nl (late-body l)))
    lift bb bs ng ng* (inj₁ (_ , Connecting.burst _ _ , () , _))
    lift bb bs ng ng* (inj₁ (_ , Connecting.kept _ _ _ _ , () , _))
    lift {z} {z*} bb bs ng ng* (inj₁ (_ , y@(Connecting.echo {j} {e} x al un nin) , un′ , nl)) =
      retarget {j ⊕ [ ix 0 ]} {z} {z*} (φc-echo x)
        (first-child {j} {φσ j} {z} {z*} (bs (inj₁ (e , x , un , λ l → nl (late-echo l)))) (ng y)
          (subst (λ w → ¬ w ⊑ z*) (φc-echo x) (ng* (proj₂ (img (_ , y , un′ , nl))))))

    liftβ : ∀ {z z*} → IB.Between z z* → SrcCut z z* → (∀ {y e} → P.Cc N y e → ¬ y ⊑ z) → (∀ {y e} → E.Cc N y e → ¬ y ⊑ z*) → IC.Between z z*
    liftβ btw (bs , _) = lift btw bs

    liftσ : ∀ {z z*} → Mark (Bdσ N) z → Mark (Bdσ* N) z* → IS.Between z z*
          → (∀ {y e} → P.Cc N y e → ¬ y ⊑ z) → (∀ {y e} → E.Cc N y e → ¬ y ⊑ z*) → IC.Between z z*
    liftσ m m* btw = lift (body-src m m* btw) btw

    -- A late connect row is a body row or an echo, placed as there.
    putC : ∀ {z z*} → PB (OwnPut (β N) Pβ) z z* → PB SrcPut z z* → (∀ {y e} → E.Cc N y e → ¬ y ⊑ z*) → PB ConnPut z z*
    putC pbb pbs ng* (inj₂ x) kz = pbs (inj₂ x) kz
    putC {z} pbb pbs ng* (inj₁ ((e , y) , pl)) kz with put-split y pl
    ... | inj₁ (e′ , x , pl′) = pbb ((e′ , x) , pl′) kz
    ... | inj₂ (j , e′ , l₀ , x , refl , pl′ , refl) =
      ix0-first (pbs (inj₁ ((e′ , x) , pl′)) (≺-trans {j} {j ⊕ [ ix 0 ]} {z} (≺-ext j []) kz)) (ng* (proj₂ (put-row y pl)))

    -- The connect's own position, against its rows and the environment.
    at-p : Btw ConnRow φc p p*
    at-p (inj₂ en) = env-p en
    at-p {k} (inj₁ o@(_ , y , _ , _)) =
      (λ lt → ⊥-elim (≺-absurd {k} {p} lt (rows-after y)))
      , (λ lt → ⊥-elim (≺-absurd {φc k} {p*} lt (rows-after* (proj₂ (img o)))))

    -- ALIVE TOGETHER: the body's ends are images, cutting the pair alike.
    al→ : ∀ {z z*} → Btw (Own (β N) Lβ) φβ z z* → (∀ {y e} → E.Cc N y e → ¬ y ⊑ z*) → P.Al N z → E.Al N z*
    al→ {z} {z*} bb ng* al {c*} x* with end← x*
    ... | c , x , nl , refl with ≼-or-≻ z* (φβ c)
    ...   | inj₂ lt = ⊥-elim (≺-absurd {z} {c} (al x) (proj₂ (bb (end , x , _ , nl)) lt))
    ...   | inj₁ le with ≼-split {z*} {φβ c} le
    ...     | inj₁ lt   = lt
    ...     | inj₂ refl = ⊥-elim (ng* (Connecting.body x*) (⊑-refl z*))

    al← : ∀ {z z*} → Btw (Own (β N) Lβ) φβ z z* → (∀ {y e} → P.Cc N y e → ¬ y ⊑ z) → E.Al N z* → P.Al N z
    al← {z} {z*} bb ng al* {c} x with end→ x
    ... | nl , x* with ≼-or-≻ z c
    ...   | inj₂ lt = ⊥-elim (≺-absurd {z*} {φβ c} (al* x*) (proj₁ (bb (end , x , _ , nl)) lt))
    ...   | inj₁ le with ≼-split {z} {c} le
    ...     | inj₁ lt   = lt
    ...     | inj₂ refl = ⊥-elim (ng (Connecting.body x) (⊑-refl z))

    tagβ→ : ∀ {b b* g g*} → Bdβ N b g → Bdβ* N b* g* → IB.TagToX SrcCut g g* → IC.TagTo g g*
    tagβ→ _  _   IB.plain-free         = IC.plain-free
    tagβ→ bd bd* (IB.both-held btw sc) = IC.both-held (liftβ btw sc (held-body bd) (held-body* bd*))

    tagβ← : ∀ {b b* g g*} → Bdβ N b g → Bdβ* N b* g* → IB.TagFromX SrcCut g g* → IC.TagFrom g g*
    tagβ← _  _   IB.elab-free          = IC.elab-free
    tagβ← bd bd* (IB.both-held btw sc) = IC.both-held (liftβ btw sc (held-body bd) (held-body* bd*))

    nin→ : ∀ {b b* g g*} → Bdσ N b g → Bdσ* N b* g* → IS.Between b b* → T (not (inside r b)) → T (not (inside r* b*))
    nin→ bd bd* btw nin = not-T (λ i → T-not nin (home← bd bd* btw i))

    nin← : ∀ {b b* g g*} → Bdσ N b g → Bdσ* N b* g* → IS.Between b b* → T (not (inside r* b*)) → T (not (inside r b))
    nin← bd bd* btw nin* = not-T (λ i → T-not nin* (home→ bd bd* btw i))

    to : ∀ {b g} → P.CBd N b g → Σ Pos λ b* → Σ Tag λ g* → E.CBd N b* g* × IC.Between b b* × IC.TagTo g g*
    to (P.bodyB bd) with toβ bd
    ... | b* , g* , bd* , btw , sc , tt = b* , g* , E.bodyB bd* , liftβ btw sc (gapc (P.bodyB bd)) (gapc* (E.bodyB bd*)) , tagβ→ bd bd* tt
    to (P.burstB bd ins) with toσ bd
    ... | b* , g* , bd* , btw , _ =
      b* , held p* , E.burstB bd* (home→ bd bd* btw ins) , liftσ (mark bd) (mark bd*) btw (gap-src bd) (gap-src* bd*) , IC.both-held at-p
    to (P.echoB bd nin al) with toσ bd
    ... | b* , free , bd* , btw , _ =
      b* , free , E.echoB bd* (nin→ bd bd* btw nin) (al→ (body-src (mark bd) (mark bd*) btw) (gap-src* bd*) al)
      , liftσ (mark bd) (mark bd*) btw (gap-src bd) (gap-src* bd*) , IC.plain-free
    ... | b* , held q* , bd* , btw , _ =
      b* , held q* , E.keptB bd* (nin→ bd bd* btw nin)
        (E.alive-down {N} {b*} {q*} (≺→≼ {q*} {b*} (E.BS.held-in {N} {b*} {q*} bd*)) (al→ (body-src (mark bd) (mark bd*) btw) (gap-src* bd*) al))
      , liftσ (mark bd) (mark bd*) btw (gap-src bd) (gap-src* bd*) , IC.plain-free
    to (P.keptB bd nin alq) with toσ bd
    ... | b* , _ , bd* , btw , IS.both-held btwq =
      b* , _ , E.keptB bd* (nin→ bd bd* btw nin) (al→ (body-src (mark-q bd) (mark-q bd*) btwq) (held-src* bd*) alq)
      , liftσ (mark bd) (mark bd*) btw (gap-src bd) (gap-src* bd*)
      , IC.both-held (liftσ (mark-q bd) (mark-q bd*) btwq (held-src bd) (held-src* bd*))

    from : ∀ {b* g*} → E.CBd N b* g* → Σ Pos λ b → Σ Tag λ g → P.CBd N b g × IC.Between b b* × IC.PutBefore b b* × IC.TagFrom g g*
    from (E.bodyB bd*) with fromβ bd*
    ... | b , g , bd , btw , pb , (bs , spb) , tf =
      b , g , P.bodyB bd , liftβ btw (bs , spb) (gapc (P.bodyB bd)) (gapc* (E.bodyB bd*))
      , putC pb spb (gapc* (E.bodyB bd*)) , tagβ← bd bd* tf
    from (E.burstB bd* ins*) with fromσ bd*
    ... | b , g , bd , btw , pb , _ =
      b , held p , P.burstB bd (home← bd bd* btw ins*) , liftσ (mark bd) (mark bd*) btw (gap-src bd) (gap-src* bd*)
      , putC (body-src-put (mark bd) (mark bd*) pb) pb (gap-src* bd*) , IC.both-held at-p
    from (E.echoB bd* nin* al*) with fromσ bd*
    ... | b , free , bd , btw , pb , _ =
      b , free , P.echoB bd (nin← bd bd* btw nin*) (al← (body-src (mark bd) (mark bd*) btw) (gap-src bd) al*)
      , liftσ (mark bd) (mark bd*) btw (gap-src bd) (gap-src* bd*)
      , putC (body-src-put (mark bd) (mark bd*) pb) pb (gap-src* bd*) , IC.elab-free
    ... | b , held q , bd , btw , pb , _ =
      b , held q , P.keptB bd (nin← bd bd* btw nin*)
        (P.alive-down {N} {b} {q} (≺→≼ {q} {b} (P.BS.held-in {N} {b} {q} bd)) (al← (body-src (mark bd) (mark bd*) btw) (gap-src bd) al*))
      , liftσ (mark bd) (mark bd*) btw (gap-src bd) (gap-src* bd*)
      , putC (body-src-put (mark bd) (mark bd*) pb) pb (gap-src* bd*) , IC.elab-free
    from (E.keptB bd* nin* alq*) with fromσ bd*
    ... | b , _ , bd , btw , pb , IS.both-held btwq =
      b , _ , P.keptB bd (nin← bd bd* btw nin*) (al← (body-src (mark-q bd) (mark-q bd*) btwq) (held-src bd) alq*)
      , liftσ (mark bd) (mark bd*) btw (gap-src bd) (gap-src* bd*)
      , putC (body-src-put (mark bd) (mark bd*) pb) pb (gap-src* bd*)
      , IC.both-held (liftσ (mark-q bd) (mark-q bd*) btwq (held-src bd) (held-src* bd*))

    corr : IC.BCorr
    corr = record { to = to ; from = from }
