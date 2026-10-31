{-# OPTIONS --guardedness #-}

-- ROWS AND RUNS: the visible rows of an emission set, those past a
-- cursor, two sets' visible rows agreeing; the entries a node is read
-- by (a pending program's meaning entered where it subscribes, a
-- binder's source frozen at its connect, a joiner's inbox, a cold's
-- tape); the pure semantics' runs, and a reader shown each least row in
-- turn.
module adequacy.Rows where

open import Data.Bool using (T)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Tree using (Obs)
open import denotation.Events using (ofᴱ; Events; burst; hush) renaming (end to endᴱ)
open import denotation.Events using (Pos; Timeline; ix)
open import denotation.Read using (Visible)
import denotation.Read as Read
open import denotation.Laws.Modulus using (≺-trans)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; _≺_; _≼_; enter; ⟦_⟧; hot; Proper; DenEnv)
open import operation.PureObservable using (module Machine; module Driver; Tape; play; ending; over)
open Machine using (St; Ctx; CS; Scope; unbound; binds; Owe; free; cpAt; cutAt; overAt; takeS; connS; joinS; coldS; scanS; Conf; ⟨_,_,_,_⟩; Mode; subscribing; absorbed; rising; load; moved; quiet; pend; ofS; mapS; cutS; lnS; flatS; alive; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; nx; cp) renaming (Ev to Evᴹ; Shown to Shownᴹ; step to stepᴹ)

------------------------------------------------------------------------
-- Rows

toEv : ∀ {A} → Evᴹ A → Ev A
toEv (nx a) = out a
toEv cp     = end

Vis : ∀ {A} → EmissionSet A → EmissionSet A
Vis t q e = t q e × Visible e

Past : ∀ {A} → Pos → EmissionSet A → EmissionSet A
Past p t q e = t q e × p ≺ q

-- The rows past a cursor.
Beyond : ∀ {A} → EmissionSet A → Maybe Pos → EmissionSet A
Beyond t nothing  = t
Beyond t (just c) = Past c t

module _ {A : Set} {t : EmissionSet A} where
  into : ∀ c {k e} → Beyond t c k e → t k e × Read.After c k
  into nothing  x        = x , tt
  into (just c) (x , ck) = x , ck

  back : ∀ c {k e} → t k e → Read.After c k → Beyond t c k e
  back nothing  x _  = x
  back (just c) x ck = x , ck

record _≃_ {A : Set} (t u : EmissionSet A) : Set where
  constructor _⇄_
  field
    to   : ∀ {q e} → t q e → u q e
    from : ∀ {q e} → u q e → t q e
open _≃_

-- Past a row past the cursor: past the row.
narrow : ∀ {A} {t : EmissionSet A} c {p} → Read.After c p → Vis (Past p (Beyond t c)) ≃ Vis (Beyond t (just p))
narrow c ap = (λ { ((y , pq) , vk) → (proj₁ (into c y) , pq) , vk })
            ⇄ (λ { ((y , pq) , vk) → (back c y (on c ap pq) , pq) , vk })
  where
    on : ∀ c {p q} → Read.After c p → p ≺ q → Read.After c q
    on nothing  _  _  = tt
    on (just c) {p} {q} ap pq = ≺-trans {c} {p} {q} ap pq

-- What a subscription pending at `p` owes: its meaning under `ρ`,
-- entered there.
pendRows : ∀ {Γ A} → DenEnv Γ → Obs Timeline Γ A → Pos → EmissionSet A
pendRows ρ o p = enter (⟦ o ⟧ ρ) p

-- THE BINDERS IN SCOPE AS THE DENOTATION READS THEM: each its source's
-- whole meaning, entered where its connect subscribed it, up to that
-- entry's end.  Not what they still owe: a source subscribed in the past
-- read the rows its binders have delivered since.
full : ∀ {Γ} → Scope Γ → DenEnv Γ
full unbound         = []
full (binds o p sc) = hot (Proper (pendRows (full sc) o (p ++ [ ix 1 ]))) ∷ full sc

-- A connect's source as it was subscribed: its whole meaning, entered
-- where the connect subscribes it.
Frozen : ∀ {Γ A} → CS Γ A → EmissionSet A
Frozen k = pendRows (full (CS.scope k)) (CS.src k) (CS.connAt k ++ [ ix 1 ])

-- What a joiner has been fed and not shown.
data Inbox {A : Set} : List (Pos × Evᴹ A) → EmissionSet A where
  this : ∀ {q e ib} → Inbox ((q , e) ∷ ib) q (toEv e)
  that : ∀ {x ib q e} → Inbox ib q e → Inbox (x ∷ ib) q e

-- A started cold's events: the frame it plays from its next index, its
-- completion owed, or nothing more.
tapeE : ∀ {A} → Tape A → Events A
tapeE (play τ u i t fr) = burst τ u i fr
tapeE (ending e)        = endᴱ e
tapeE over              = hush

------------------------------------------------------------------------
-- Runs

-- The pure semantics run from `k`, showing `rs`: the driver's steps, so
-- a cold begun and a cold's turn are steps too.
data Steps {R : Set} : Conf R → Shownᴹ R → Set₁ where
  []   : ∀ {k} → Steps k []
  tau  : ∀ {k k′ t rs} → Driver.step R k ≡ Driver.silent t k′ → Steps k′ rs → Steps k rs
  val  : ∀ {k k′ t p a rs} → Driver.step R k ≡ Driver.value t p a k′ → Steps k′ rs → Steps k ((p , nx a) ∷ rs)
  fin  : ∀ {k p} → Driver.step R k ≡ Driver.complete p → Steps k [ (p , cp) ]

conv : ∀ {R} → Shownᴹ R → List (Pos × Ev R)
conv []             = []
conv ((p , e) ∷ rs) = (p , toEv e) ∷ conv rs

-- The least visible row.
Lowest : ∀ {A} → EmissionSet A → Pos → Ev A → Set
Lowest t p e = Vis t p e × (∀ {q e′} → Vis t q e′ → p ≼ q)

-- A reader shown `rs` of `t`: each the least visible row left.
data Shows* {A : Set} (t : EmissionSet A) : List (Pos × Ev A) → Set₁ where
  []  : Shows* t []
  _∷_ : ∀ {p e rs} → Lowest t p e → Shows* (Past p t) rs → Shows* t ((p , e) ∷ rs)

-- One step: the visible rows kept, or the least shown and dropped.
data Moves {R : Set} (T : EmissionSet R) : Shownᴹ R → EmissionSet R → Set₁ where
  silent : ∀ {T′} → Vis T ≃ Vis T′ → Moves T [] T′
  shown  : ∀ {T′ p e} → Vis T p (toEv e) → (∀ {q e′} → Vis T q e′ → p ≼ q) → Vis (Past p T) ≃ Vis T′ → Moves T [ (p , e) ] T′

≃-sym : ∀ {A} {t u : EmissionSet A} → t ≃ u → u ≃ t
≃-sym eq = from eq ⇄ to eq

≃-refl : ∀ {A} {t : EmissionSet A} → t ≃ t
≃-refl = (λ x → x) ⇄ (λ x → x)

≃-trans : ∀ {A} {t u v : EmissionSet A} → t ≃ u → u ≃ v → t ≃ v
≃-trans p q = (λ x → to q (to p x)) ⇄ (λ x → from p (from q x))

past-≃ : ∀ {A} {t u : EmissionSet A} {p} → Vis t ≃ Vis u → Vis (Past p t) ≃ Vis (Past p u)
past-≃ eq = (λ { ((x , pq) , vi) → let (y , vj) = to eq (x , vi) in (y , pq) , vj })
          ⇄ (λ { ((x , pq) , vi) → let (y , vj) = from eq (x , vi) in (y , pq) , vj })

Shows*-≃ : ∀ {A} {t u : EmissionSet A} {rs} → Vis t ≃ Vis u → Shows* t rs → Shows* u rs
Shows*-≃ eq [] = []
Shows*-≃ eq (_∷_ {p = p} (v , lt) rest) = (to eq v , λ w → lt (from eq w)) ∷ Shows*-≃ (past-≃ {p = p} eq) rest
