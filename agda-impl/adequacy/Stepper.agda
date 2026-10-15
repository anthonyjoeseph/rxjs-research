{-# OPTIONS --guardedness #-}

-- THE STEPPER IS THE MEANING, skips included, node by node.  A node inside
-- a connect's body reads its connects' sources as their runs from where
-- they stand (`ρᴱ`), and its step is the run's next event only if it
-- comes before each running source's (`First`), as a connect's step
-- decides.  Then its meaning is what its step shows, then the meaning of
-- the node it leaves (`os`).
module adequacy.Stepper where

open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; [_]; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.Properties using (++-assoc)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

import Tree as T
open import Tree using (Later)
open import denotation.MonotonicList using (Events; Events∞; Pos; From; Frame; Timeline; out; skip; end; hush; ix; _<ᵖ_; Agree; stop; out⁼; skip⁼; end⁼; hush⁼; agree-refl; agree-sym; agree-trans; <ᵖ-trans; <ᵖ-below; <ᵖ-irrefl; <ᵖ-shift; <ᵖ-part; ≮-trans; last; agrees; agree; ≈ₖ-pred)
  renaming (sub to subᴾ)
import denotation.MonotonicList as M
import denotation.Unfold as U
open import denotation.NonExpansive using (mapᴱ-ne; scanᴱ-ne; takeWhileᴱ-ne; rejoin-ne; beside-ne; hot-ne; go-ne; Lanes; []ᴸ; _∷ᴸ_; Queue; []ᑫ; _∷ᑫ_; doneᴼ; liveᴼ)
open import denotation.Compositional using (EnvAgree; deferᴰ-contractive) renaming ([]ᵉ to []ᵈ; _∷ᵉ_ to _∷ᵈ_)
open import denotation.Unfold using (NEnv; ⟦⟧-ne)
open import denotation.Denote using (flatOp)
open import adequacy.Sane using (Sane; Saneᴹ; Saneᴸ; Told; allLive)
open import adequacy.Placed using (Atop; Placed; Placedᴹ; Placedᴸ)

open Events∞

------------------------------------------------------------------------
-- Alike: the same events at the same positions, skips included, to any
-- depth.

record _≃_ {A : Set} (x y : Events A) : Set where
  constructor alike
  field agreeing : ∀ n → Agree n x y

open _≃_

≃-refl : ∀ {A} (x : Events A) → x ≃ x
≃-refl x = alike λ n → agree-refl n x

≃-sym : ∀ {A} {x y : Events A} → x ≃ y → y ≃ x
≃-sym p = alike λ n → agree-sym (agreeing p n)

≃-trans : ∀ {A} {x y z : Events A} → x ≃ y → y ≃ z → x ≃ z
≃-trans p q = alike λ n → agree-trans (agreeing p n) (agreeing q n)

-- One event, then tails alike.
out-cong : ∀ {A k a} {l r : Events∞ A} → force l ≃ force r → out k a l ≃ out k a r
out-cong p = alike λ where
  zero    → stop
  (suc n) → out⁼ (agreeing p n)

skip-cong : ∀ {A k} {l r : Events∞ A} → force l ≃ force r → skip k l ≃ skip k r
skip-cong p = alike λ where
  zero    → stop
  (suc n) → skip⁼ (agreeing p n)

out-same : ∀ {A k a} {l r : Events∞ A} → force l ≡ force r → out k a l ≃ out k a r
out-same {l = l} e = out-cong (subst (force l ≃_) e (≃-refl (force l)))

skip-same : ∀ {A k} {l r : Events∞ A} → force l ≡ force r → skip k l ≃ skip k r
skip-same {l = l} e = skip-cong (subst (force l ≃_) e (≃-refl (force l)))

------------------------------------------------------------------------
-- The stream functions respect it

mapᴱ-≃ : ∀ {A B} (f : A → B) {x y : Events A} → x ≃ y → M.mapᴱ f x ≃ M.mapᴱ f y
mapᴱ-≃ f p = alike λ n → mapᴱ-ne f (agreeing p n)

scanᴱ-≃ : ∀ {A B} (f : B → A → B) z {x y : Events A} → x ≃ y → M.scanᴱ f z x ≃ M.scanᴱ f z y
scanᴱ-≃ f z p = alike λ n → scanᴱ-ne f z (agreeing p n)

takeWhileᴱ-≃ : ∀ {A} i (p : A → Bool) {x y : Events A} → x ≃ y → M.takeWhileᴱ i p x ≃ M.takeWhileᴱ i p y
takeWhileᴱ-≃ i p e = alike λ n → takeWhileᴱ-ne i p (agreeing e n)

beside-≃ : ∀ {A B} {x x′ : Events B} {y y′ : Events A} → x ≃ x′ → y ≃ y′ → M.beside x y ≃ M.beside x′ y′
beside-≃ p q = alike λ n → beside-ne (agreeing p n) (agreeing q n)

rejoin-≃ : ∀ {A} p {x y : Events A} → x ≃ y → M.rejoin p x ≃ M.rejoin p y
rejoin-≃ p e = alike λ n → rejoin-ne p (agreeing e n)

------------------------------------------------------------------------
-- The connects in scope

-- Each connect's source: running, or ended where.
data Env : List Set → Set₁ where
  []  : Env []
  _∷_ : ∀ {Γ A} → U.Source Γ A → Env Γ → Env (A ∷ Γ)

-- Each source's run from where it stands, as the meaning reads it.
ρᴱ : ∀ {Γ} → Env Γ → NEnv Γ
ρᴱ []              = []ᴬ
ρᴱ (U.live s  ∷ δ) = U.meaning s (ρᴱ δ) ∷ᴬ ρᴱ δ
ρᴱ (U.ended c ∷ δ) = end c ∷ᴬ ρᴱ δ

flags : ∀ {Γ} → Env Γ → All (λ _ → Bool) Γ
flags []              = []ᴬ
flags (U.live _  ∷ δ) = true ∷ᴬ flags δ
flags (U.ended _ ∷ δ) = false ∷ᴬ flags δ

-- What a step shows, then the meaning of the node it leaves.
afterᴱ : ∀ {Γ A} → NEnv Γ → U.Step Γ A → Events A
afterᴱ ρ (U.outˢ k a c′) = out k a λ where .force → U.meaning c′ ρ
afterᴱ ρ (U.skipˢ k c′)  = skip k λ where .force → U.meaning c′ ρ
afterᴱ ρ (U.endˢ k)      = end k
afterᴱ ρ U.hushˢ         = hush

-- A step at `k` is taken before a source's next at `q`, as `U.sourceˢ`
-- decides: a silent source never comes first, a silent body never does.
Wins : Maybe Pos → Maybe Pos → Bool
Wins k        nothing  = true
Wins nothing  (just q) = false
Wins (just k) (just q) = not ((q ++ [ ix 0 ]) <ᵖ k)

First : ∀ {Γ} → Maybe Pos → Env Γ → Set
First k []              = ⊤
First k (U.live s  ∷ δ) = Wins k (U.headˢ (U.step s)) ≡ true × First k δ
First k (U.ended _ ∷ δ) = First k δ

-- The node, its meaning read in `δ`, is what its step shows whenever
-- that step comes first.
Shows : ∀ {Γ A} → U.Node Γ A → Env Γ → Set
Shows c δ = First (U.headˢ (U.step c)) δ → U.meaning c (ρᴱ δ) ≃ afterᴱ (ρᴱ δ) (U.step c)

-- A position's step past a head: a silent head shifts to nothing.
shift : Maybe Pos → Maybe Pos
shift nothing  = nothing
shift (just h) = just (h ++ [ ix 0 ])

-- Each running source's next, a step past it, is taken after `k`: what
-- a joiner is fed of it lands past its step.
Under : ∀ {Γ} → Pos → Env Γ → Set
Under k []              = ⊤
Under k (U.live s  ∷ δ) = Wins (just k) (shift (U.headˢ (U.step s))) ≡ true × Under k δ
Under k (U.ended _ ∷ δ) = Under k δ

-- The events' first is taken after a body's event at `k`.
Lags : ∀ {A} → Pos → Events A → Set
Lags k (out h _ _) = (h ++ [ ix 0 ]) <ᵖ k ≡ false
Lags k (skip h _)  = (h ++ [ ix 0 ]) <ᵖ k ≡ false
Lags k (end c)     = (c ++ [ ix 0 ]) <ᵖ k ≡ false
Lags k hush        = ⊤

-- The events' first, a step past it, is taken after `k`.
Lags₂ : ∀ {A} → Pos → Events A → Set
Lags₂ k (out h _ _) = ((h ++ [ ix 0 ]) ++ [ ix 0 ]) <ᵖ k ≡ false
Lags₂ k (skip h _)  = ((h ++ [ ix 0 ]) ++ [ ix 0 ]) <ᵖ k ≡ false
Lags₂ k (end c)     = ((c ++ [ ix 0 ]) ++ [ ix 0 ]) <ᵖ k ≡ false
Lags₂ k hush        = ⊤

-- A source's meaning, a step past it, is taken after any `k` its step
-- and its own sources are.
Lagging : ∀ {Γ A} → U.Node Γ A → Env Γ → Set
Lagging s δ = ∀ k → Wins (just k) (shift (U.headˢ (U.step s))) ≡ true → Under k δ → Lags₂ k (U.meaning s (ρᴱ δ))

-- Every running source shows its step, is placed, and lags.
Settled : ∀ {Γ} → Env Γ → Set
Settled []              = ⊤
Settled (U.live s  ∷ δ) = Shows s δ × Placed s (ρᴱ δ) × Lagging s δ × Settled δ
Settled (U.ended _ ∷ δ) = Settled δ

------------------------------------------------------------------------
-- Node by node

frames-after : ∀ {Γ A t} τ e (m : From A t) {ρ : NEnv Γ} → M.frames τ e m ≃ afterᴱ ρ (U.framesˢ τ e m)
burst-after : ∀ {Γ A t} τ r i (b : Frame A t) {ρ : NEnv Γ} → M.burst τ r i b ≃ afterᴱ ρ (U.burstˢ τ r i b)
frames-after τ e M.done       = ≃-refl (end e)
frames-after τ e M.quiet      = ≃-refl hush
frames-after τ e (M.at t _ b) = burst-after τ _ 0 b
burst-after τ r i (M.emit a k) = out-same refl
burst-after τ r i (M.stall k)  = skip-same refl
burst-after τ r i (M.close k)  = skip-same refl

of-after : ∀ {Γ A} p i (xs : List A) {ρ : NEnv Γ} → M.ofᴱ p i xs ≃ afterᴱ ρ (U.ofˢ p i xs)
of-after p i []       = ≃-refl (end _)
of-after p i (x ∷ xs) = out-same refl

map-head : ∀ {Γ A B} (f : A → B) (s : U.Step Γ A) → U.headˢ (U.mapˢ f s) ≡ U.headˢ s
map-head f (U.outˢ k a c) = refl
map-head f (U.skipˢ k c)  = refl
map-head f (U.endˢ k)     = refl
map-head f U.hushˢ        = refl

map-after : ∀ {Γ A B} (f : A → B) {ρ : NEnv Γ} (s : U.Step Γ A) → M.mapᴱ f (afterᴱ ρ s) ≃ afterᴱ ρ (U.mapˢ f s)
map-after f (U.outˢ k a c) = out-same refl
map-after f (U.skipˢ k c)  = skip-same refl
map-after f (U.endˢ k)     = ≃-refl (end k)
map-after f U.hushˢ        = ≃-refl hush

scan-head : ∀ {Γ A B} (f : B → A → B) z (s : U.Step Γ A) → U.headˢ (U.scanˢ f z s) ≡ U.headˢ s
scan-head f z (U.outˢ k a c) = refl
scan-head f z (U.skipˢ k c)  = refl
scan-head f z (U.endˢ k)     = refl
scan-head f z U.hushˢ        = refl

scan-after : ∀ {Γ A B} (f : B → A → B) z {ρ : NEnv Γ} (s : U.Step Γ A) → M.scanᴱ f z (afterᴱ ρ s) ≃ afterᴱ ρ (U.scanˢ f z s)
scan-after f z (U.outˢ k a c) = out-same refl
scan-after f z (U.skipˢ k c)  = skip-same refl
scan-after f z (U.endˢ k)     = ≃-refl (end k)
scan-after f z U.hushˢ        = ≃-refl hush

-- A cut value's step sits at or past it, so a step that comes first
-- before the cut still does.
postulate
  take-first : ∀ {Γ A} i (p : A → Bool) (s : U.Step Γ A) (δ : Env Γ) → First (U.headˢ (U.takeWhileˢ i p s)) δ → First (U.headˢ s) δ

take-after : ∀ {Γ A} i (p : A → Bool) {ρ : NEnv Γ} (s : U.Step Γ A) → M.takeWhileᴱ i p (afterᴱ ρ s) ≃ afterᴱ ρ (U.takeWhileˢ i p s)
take-after i p (U.outˢ k a c) with p a
take-after i     p (U.outˢ k a c) | true  = out-same refl
take-after true  p (U.outˢ k a c) | false = out-same refl
take-after false p (U.outˢ k a c) | false = ≃-refl (end _)
take-after i p (U.skipˢ k c) = skip-same refl
take-after i p (U.endˢ k)    = ≃-refl (end k)
take-after i p U.hushˢ       = ≃-refl hush

-- An untold joiner's step is silent only when its source's is.
postulate
  -- A joiner untold and fed nothing, every running source silent: it
  -- shows nothing.
  join-quiet : ∀ {Γ A} (i : A ∈ Γ) p (δ : Env Γ) → Settled δ → Told (lookup (flags δ) i) nothing → First nothing δ
             → M.rejoin p (lookup (ρᴱ δ) i) ≃ hush

join-after : ∀ {Γ A} (i : A ∈ Γ) p xs e (δ : Env Γ) → Settled δ → Told (lookup (flags δ) i) e → First (U.headˢ (U.joinˢ i p xs e)) δ
           → U.meaning (U.joinᶜ i p xs e) (ρᴱ δ) ≃ afterᴱ (ρᴱ δ) (U.joinˢ i p xs e)
join-after i p ((q , just a) ∷ xs) e   δ st t fi = out-same refl
join-after i p ((q , nothing) ∷ xs) e  δ st t fi = skip-same refl
join-after i p []             (just c) δ st t fi = ≃-refl (end c)
join-after i p []             nothing  δ st t fi = join-quiet i p δ st t fi

-- Each lane in flight, or the outer, shows its step.
Showsᴹ : ∀ {Γ A} → Maybe (U.Node Γ A) → Env Γ → Set
Showsᴹ nothing  δ = ⊤
Showsᴹ (just c) δ = Shows c δ

Showsᴸ : ∀ {Γ A} → List (U.Node Γ A) → Env Γ → Set
Showsᴸ []       δ = ⊤
Showsᴸ (c ∷ cs) δ = Shows c δ × Showsᴸ cs δ

postulate
  -- THE MERGE STEPS AS THE MERGE MEANS: the outer and each lane in flight
  -- showing its step whenever it comes first, a flatMap's meaning is what
  -- its step shows.
  go-skips : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) o ls qs (δ : Env Γ) → Settled δ
           → Sane (flags δ) (U.flatMapᶜ op g o ls qs) → Placed (U.flatMapᶜ op g o ls qs) (ρᴱ δ)
           → Showsᴹ o δ → Showsᴸ ls δ → Shows (U.flatMapᶜ op g o ls qs) δ

  -- A FLATMAP'S MEANING LAGS: whatever it shows is taken after a body's
  -- event at `k` that comes before its step, and its sources' a step
  -- past.
  lags-flat : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) o ls qs (δ : Env Γ) → Settled δ
            → Sane (flags δ) (U.flatMapᶜ op g o ls qs) → Placed (U.flatMapᶜ op g o ls qs) (ρᴱ δ) → ∀ k
            → Wins (just k) (U.headˢ (U.step (U.flatMapᶜ op g o ls qs))) ≡ true → Under k δ → Lags k (U.meaning (U.flatMapᶜ op g o ls qs) (ρᴱ δ))

  -- A DEFER STEPS AS IT MEANS: one skip, then the program it defers
  -- subscribed, as the fold's meaning of it.
  defer-after : ∀ {Γ A} (l : Later Timeline Γ A) p ns (ρ : NEnv Γ) → U.meaning (U.deferᶜ l p ns) ρ ≃ afterᴱ ρ (U.step (U.deferᶜ l p ns))

-- `same?` answers yes only for one index.
same-≡ : ∀ {Γ : List Set} {A : Set} (i j : A ∈ Γ) → U.same? i j ≡ just refl → i ≡ j
same-≡ (here refl) (here refl) e = refl
same-≡ (there i)   (there j)   e = cong there (same-≡ i j e)
same-≡ (here refl) (there j)   ()
same-≡ (there i)   (here refl) ()

-- Telling a joiner its source's end changes nothing it means once the
-- source has ended there.
shut-join : ∀ {Γ A B} {ρ : NEnv Γ} (i : A ∈ Γ) c (j : B ∈ Γ) p e → lookup ρ i ≡ end c
          → U.joined j p (U.told i c j p e (U.same? i j)) ρ ≡ U.joined j p e ρ
shut-join i c j p (just e) l with U.same? i j
... | just refl = refl
... | nothing   = refl
shut-join {ρ = ρ} i c j p nothing l with U.same? i j in eq
... | nothing   = refl
... | just refl with same-≡ i j eq
... | refl rewrite l with p <ᵖ c
... | true  = refl
... | false = refl

mutual
  shut-meaning : ∀ {Γ A B} (i : A ∈ Γ) c (n : U.Node Γ B) (ρ : NEnv Γ) → lookup ρ i ≡ end c → U.meaning (U.shut i c n) ρ ≡ U.meaning n ρ
  shut-meaning i c (U.framesᶜ τ e m)         ρ l = refl
  shut-meaning i c (U.burstᶜ τ r k b)        ρ l = refl
  shut-meaning i c (U.endᶜ p)                ρ l = refl
  shut-meaning i c (U.ofᶜ p k xs)            ρ l = refl
  shut-meaning i c (U.mapᶜ f n)              ρ l = cong (M.mapᴱ f) (shut-meaning i c n ρ l)
  shut-meaning i c (U.scanᶜ f z n)           ρ l = cong (M.scanᴱ f z) (shut-meaning i c n ρ l)
  shut-meaning i c (U.takeWhileᶜ k p n)      ρ l = cong (M.takeWhileᴱ k p) (shut-meaning i c n ρ l)
  shut-meaning i c (U.flatMapᶜ op g o ls qs) ρ l
    rewrite shut-meaningᴹ i c o ρ l | shut-meanings i c ls ρ l = refl
  shut-meaning i c (U.joinᶜ j p xs e)        ρ l = cong (U.fedᴺ xs) (shut-join i c j p e l)
  shut-meaning i c (U.connectᶜ b (U.live s)) ρ l
    rewrite shut-meaning i c s ρ l | shut-meaning (there i) c b (U.meaning s ρ ∷ᴬ ρ) l = refl
  shut-meaning i c (U.connectᶜ b (U.ended e)) ρ l = shut-meaning (there i) c b (end e ∷ᴬ ρ) l
  shut-meaning i c (U.deferᶜ k p ns)         ρ l = refl

  shut-meaningᴹ : ∀ {Γ A B} (i : A ∈ Γ) c (o : Maybe (U.Node Γ B)) (ρ : NEnv Γ) → lookup ρ i ≡ end c → U.meaningᴹ (U.shutᴹ i c o) ρ ≡ U.meaningᴹ o ρ
  shut-meaningᴹ i c nothing  ρ l = refl
  shut-meaningᴹ i c (just n) ρ l = cong just (shut-meaning i c n ρ l)

  shut-meanings : ∀ {Γ A B} (i : A ∈ Γ) c (ns : List (U.Node Γ B)) (ρ : NEnv Γ) → lookup ρ i ≡ end c → U.meanings (U.shutᴸ i c ns) ρ ≡ U.meanings ns ρ
  shut-meanings i c []       ρ l = refl
  shut-meanings i c (n ∷ ns) ρ l = cong₂ _∷_ (shut-meaning i c n ρ l) (shut-meanings i c ns ρ l)

shut-head : ∀ {Γ A B} c (s : U.Step (A ∷ Γ) B) → U.headˢ (U.shutˢᵗ c s) ≡ U.headˢ s
shut-head c (U.outˢ k a b) = refl
shut-head c (U.skipˢ k b)  = refl
shut-head c (U.endˢ e)     = refl
shut-head c U.hushˢ        = refl

shut-after : ∀ {Γ A B} c {ρ : NEnv Γ} (s : U.Step (A ∷ Γ) B) → afterᴱ (end c ∷ᴬ ρ) s ≃ afterᴱ ρ (U.shutˢᵗ c s)
shut-after c {ρ} (U.outˢ k a b) = out-same (sym (shut-meaning (here refl) c b (end c ∷ᴬ ρ) refl))
shut-after c {ρ} (U.skipˢ k b)  = skip-same (sym (shut-meaning (here refl) c b (end c ∷ᴬ ρ) refl))
shut-after c (U.endˢ e)         = ≃-refl (end e)
shut-after c U.hushˢ            = ≃-refl hush

------------------------------------------------------------------------
-- A running connect

-- A BODY TIED WITH A POSITION SHOWS ONLY SKIPS THERE: each event it
-- shows not past `Q` is a skip at `Q`.
mutual
  data Tie {B : Set} (Q : Pos) : Events B → Set where
    past : ∀ {x} → M.before Q x ≡ true → Tie Q x
    tied : ∀ {r} → Tied Q (force r) → Tie Q (skip Q r)

  record Tied {B : Set} (Q : Pos) (x : Events B) : Set where
    coinductive
    field tie : Tie Q x

open Tied

-- The source's next taken after the body's, or before it.
ahead-out : ∀ {A B} k (a : B) (r : Events∞ B) q (t : Events∞ A) b (r′ : Events∞ B) → b ≡ false
          → force r′ ≡ M.ahead (force r) q t (M.before q (force r)) → M.ahead (out k a r) q t b ≃ out k a r′
ahead-out k a r q t .false r′ refl e = out-same (sym e)

ahead-skip : ∀ {A B} k (r : Events∞ B) q (t : Events∞ A) b (r′ : Events∞ B) → b ≡ false
           → force r′ ≡ M.ahead (force r) q t (M.before q (force r)) → M.ahead (skip k r) q t b ≃ skip k r′
ahead-skip k r q t .false r′ refl e = skip-same (sym e)

ahead-end : ∀ {A B} k q (t : Events∞ A) b → b ≡ false → M.ahead {B = B} (end k) q t b ≃ end k
ahead-end k q t .false refl = ≃-refl (end k)

beside-out : ∀ {A B} k (a : B) (r : Events∞ B) (e : Events A) (r′ : Events∞ B) → Lags k e
           → force r′ ≡ M.beside (force r) e → M.beside (out k a r) e ≃ out k a r′
beside-out k a r (out h x t) r′ lag f = ahead-out k a r (h ++ [ ix 0 ]) t _ r′ lag f
beside-out k a r (skip h t)  r′ lag f = ahead-out k a r (h ++ [ ix 0 ]) t _ r′ lag f
beside-out k a r (end c)     r′ lag f = ahead-out k a r (c ++ [ ix 0 ]) M.hushed _ r′ lag f
beside-out k a r hush        r′ lag f = out-same (sym f)

beside-skip : ∀ {A B} k (r : Events∞ B) (e : Events A) (r′ : Events∞ B) → Lags k e
            → force r′ ≡ M.beside (force r) e → M.beside (skip k r) e ≃ skip k r′
beside-skip k r (out h x t) r′ lag f = ahead-skip k r (h ++ [ ix 0 ]) t _ r′ lag f
beside-skip k r (skip h t)  r′ lag f = ahead-skip k r (h ++ [ ix 0 ]) t _ r′ lag f
beside-skip k r (end c)     r′ lag f = ahead-skip k r (c ++ [ ix 0 ]) M.hushed _ r′ lag f
beside-skip k r hush        r′ lag f = skip-same (sym f)

beside-end : ∀ {A B} k (e : Events A) → Lags k e → M.beside {B = B} (end k) e ≃ end k
beside-end k (out h x t) lag = ahead-end k (h ++ [ ix 0 ]) t _ lag
beside-end k (skip h t)  lag = ahead-end k (h ++ [ ix 0 ]) t _ lag
beside-end k (end c)     lag = ahead-end k (c ++ [ ix 0 ]) M.hushed _ lag
beside-end k hush        lag = ≃-refl (end k)

-- What a step shows sits atop the stepped node's meaning, and that node
-- is placed.
Placedˢ : ∀ {Γ A} → NEnv Γ → U.Step Γ A → Set
Placedˢ ρ (U.outˢ k a c) = Atop k (U.meaning c ρ) × Placed c ρ
Placedˢ ρ (U.skipˢ k c)  = Atop k (U.meaning c ρ) × Placed c ρ
Placedˢ ρ (U.endˢ k)     = ⊤
Placedˢ ρ U.hushˢ        = ⊤

-- A step that comes first just past `q` comes first at `q`.
not-past : ∀ x y z → y <ᵖ z ≡ true → not (x <ᵖ z) ≡ true → not (x <ᵖ y) ≡ true
not-past x y z yz w with x <ᵖ y in e
... | false = refl
... | true  = subst (λ b → not b ≡ true) (<ᵖ-trans x y z e yz) w

first-sub : ∀ {Γ} q (δ : Env Γ) → First (just (q ++ [ ix 0 ])) δ → First (just q) δ
first-sub q []              tt       = tt
first-sub q (U.ended _ ∷ δ) f        = first-sub q δ f
first-sub q (U.live s  ∷ δ) (w , f) = wins (U.headˢ (U.step s)) w , first-sub q δ f
  where wins : ∀ h → Wins (just (q ++ [ ix 0 ])) h ≡ true → Wins (just q) h ≡ true
        wins nothing  w = refl
        wins (just r) w = not-past (r ++ [ ix 0 ]) q (q ++ [ ix 0 ]) (<ᵖ-below q []) w

-- A source's step taken just past itself comes first.
wins-self : ∀ q → Wins (just (q ++ [ ix 0 ])) (just q) ≡ true
wins-self q = cong not (<ᵖ-irrefl (q ++ [ ix 0 ]))

-- What a joiner was fed, ahead of alike runs.
put-cong : ∀ {A} q (a : Maybe A) {l r : Events∞ A} → force l ≃ force r → U.put q a l ≃ U.put q a r
put-cong q (just a) e = out-cong e
put-cong q nothing  e = skip-cong e

fedᴺ-≃ : ∀ {A} (xs : List (Pos × Maybe A)) {x y : Events A} → x ≃ y → U.fedᴺ xs x ≃ U.fedᴺ xs y
fedᴺ-≃ []             e = e
fedᴺ-≃ ((q , a) ∷ xs) e = put-cong q a (fedᴺ-≃ xs e)

-- Environments alike entry by entry.
data _≈ᴱ_ : ∀ {Γ} → NEnv Γ → NEnv Γ → Set₁ where
  []ᵉ  : []ᴬ ≈ᴱ []ᴬ
  _∷ᵉ_ : ∀ {A Γ} {x y : Events A} {ρ σ : NEnv Γ} → x ≃ y → ρ ≈ᴱ σ → (x ∷ᴬ ρ) ≈ᴱ (y ∷ᴬ σ)

≈ᴱ-refl : ∀ {Γ} (ρ : NEnv Γ) → ρ ≈ᴱ ρ
≈ᴱ-refl []ᴬ      = []ᵉ
≈ᴱ-refl (x ∷ᴬ ρ) = ≃-refl x ∷ᵉ ≈ᴱ-refl ρ

lookup-≈ : ∀ {Γ A} {ρ σ : NEnv Γ} → ρ ≈ᴱ σ → (i : A ∈ Γ) → lookup ρ i ≃ lookup σ i
lookup-≈ (a ∷ᵉ e) (here refl) = a
lookup-≈ (a ∷ᵉ e) (there i)   = lookup-≈ e i

module _ {A : Set} (p : Pos) where
  -- the rest of a source, rejoined
  rejoined : Events∞ A → Events∞ A
  force (rejoined l) = M.rejoin p (force l)

  module _ {q : Pos} {l : Events∞ A} where
    -- a source's step after the join, shown
    rejoin-in : ∀ a → p <ᵖ q ≡ true → M.rejoin p (U.put q a l) ≃ U.put (q ++ [ subᴾ p ]) a (rejoined l)
    rejoin-in (just a) h with p <ᵖ q | h
    ... | true | refl = out-same refl
    rejoin-in nothing  h with p <ᵖ q | h
    ... | true | refl = skip-same refl

    -- a source's step before the join, a skip just past it
    rejoin-pre : ∀ a → p <ᵖ q ≡ false → M.rejoin p (U.put q a l) ≃ skip (p ++ [ ix 0 ]) (rejoined l)
    rejoin-pre (just a) h with p <ᵖ q | h
    ... | false | refl = skip-same refl
    rejoin-pre nothing  h with p <ᵖ q | h
    ... | false | refl = skip-same refl

private
  fedᴺ-snoc : ∀ {A} xs k (a : Maybe A) (l : Events∞ A) → U.fedᴺ (xs ++ [ (k , a) ]) (force l) ≃ U.fedᴺ xs (U.put k a l)
  fedᴺ-snoc []       k (just a) l = out-same refl
  fedᴺ-snoc []       k nothing  l = skip-same refl
  fedᴺ-snoc ((q , b) ∷ xs) k a l = put-cong q b (fedᴺ-snoc xs k a l)

-- An environment fed its source's step at `i`: alike the reading one
-- elsewhere, and at `i` the step, then the run it feeds.
data Fedᴱ {A : Set} (q : Pos) (a : Maybe A) : ∀ {Γ} → A ∈ Γ → NEnv Γ → NEnv Γ → Set₁ where
  here′  : ∀ {Γ x} {l : Events∞ A} {ρ σ : NEnv Γ} → x ≃ U.put q a l → ρ ≈ᴱ σ → Fedᴱ q a (here refl) (x ∷ᴬ ρ) (force l ∷ᴬ σ)
  there′ : ∀ {B Γ} {i : A ∈ Γ} {x y : Events B} {ρ σ : NEnv Γ} → x ≃ y → Fedᴱ q a i ρ σ → Fedᴱ q a (there i) (x ∷ᴬ ρ) (y ∷ᴬ σ)

-- A node fed its source's step, and the node reading it.
Fed : ∀ {Γ B} → U.Node Γ B → Set₁
Fed {Γ} b = ∀ {A} (i : A ∈ Γ) q (a : Maybe A) {ρ σ : NEnv Γ} → Fedᴱ q a i ρ σ
  → ∀ {ν} → Sane ν b → lookup ν i ≡ true → U.meaning b ρ ≃ U.meaning (U.feed i q a b) σ

private
  fed-indep : ∀ {Γ Δ A B} (i : A ∈ Γ) (i′ : A ∈ Δ) q (a : Maybe A) (j : B ∈ Γ) (j′ : B ∈ Δ) p xs m
            → U.fed i q a j p xs m ≡ U.fed i′ q a j′ p xs m
  fed-indep i i′ q a j j′ p xs (just refl) = refl
  fed-indep i i′ q a j j′ p xs nothing     = refl

  -- the joiner of the fed source itself
  fed-here : ∀ {A} p xs q (a : Maybe A) (l : Events∞ A) {x : Events A} → x ≃ U.put q a l
           → U.fedᴺ xs (M.rejoin p x) ≃ U.fedᴺ (U.fed (here refl) q a (here {xs = []} refl) p xs (just refl)) (M.rejoin p (force l))
  fed-here p xs q a l e with p <ᵖ q in pq
  ... | true  = ≃-trans (fedᴺ-≃ xs (≃-trans (rejoin-≃ p e) (rejoin-in p {q} {l} a pq))) (≃-sym (fedᴺ-snoc xs _ a (rejoined p l)))
  ... | false = ≃-trans (fedᴺ-≃ xs (≃-trans (rejoin-≃ p e) (rejoin-pre p {q} {l} a pq))) (≃-sym (fedᴺ-snoc xs _ nothing (rejoined p l)))

-- A JOINER FED ITS SOURCE'S STEP IS THE JOINER READING IT: fed the step
-- under its own position if it joined before it, else as its pre-join
-- skip; a joiner of another source is not fed at all.
fed-joiner : ∀ {Γ A B} {q} {a : Maybe A} {i : A ∈ Γ} {ρ σ : NEnv Γ} → Fedᴱ q a i ρ σ → ∀ {ν} → lookup ν i ≡ true
           → (j : B ∈ Γ) → ∀ p xs e → Told (lookup ν j) e
           → U.fedᴺ xs (U.joined j p e ρ) ≃ U.fedᴺ (U.fed i q a j p xs (U.same? i j)) (U.joined j p e σ)
fed-joiner {q = q} {a} (here′ {l = l} e r) lv (here refl) p xs nothing  t = fed-here p xs q a l e
fed-joiner (here′ e r) {true ∷ᴬ _} refl (here refl) p xs (just c) ()
fed-joiner (here′ e r)  lv (there j)   p xs nothing  t = fedᴺ-≃ xs (rejoin-≃ p (lookup-≈ r j))
fed-joiner (here′ e r)  lv (there j)   p xs (just c) t = ≃-refl _
fed-joiner (there′ e f) lv (here refl) p xs nothing  t = fedᴺ-≃ xs (rejoin-≃ p e)
fed-joiner (there′ e f) lv (here refl) p xs (just c) t = ≃-refl _
fed-joiner {q = q} {a} {there i} {_ ∷ᴬ ρ} {_ ∷ᴬ σ} (there′ {B = C} e f) {_ ∷ᴬ ν} lv (there j) p xs nothing t =
  subst (λ ys → U.fedᴺ xs (U.joined j p nothing ρ) ≃ U.fedᴺ ys (U.joined j p nothing σ)) (fed-indep {Δ = C ∷ _} i (there i) q a j (there j) p xs (U.same? i j)) (fed-joiner f {ν} lv j p xs nothing t)
fed-joiner {q = q} {a} {there i} {_ ∷ᴬ ρ} {_ ∷ᴬ σ} (there′ {B = C} e f) {_ ∷ᴬ ν} lv (there j) p xs (just c) t =
  subst (λ ys → U.fedᴺ xs (U.joined j p (just c) ρ) ≃ U.fedᴺ ys (U.joined j p (just c) σ)) (fed-indep {Δ = C ∷ _} i (there i) q a j (there j) p xs (U.same? i j)) (fed-joiner f {ν} lv j p xs (just c) t)

-- A defer's notices: the last put back on the environment first.
replay-snoc : ∀ {Γ} ns (n : U.Notice Γ) (σ : NEnv Γ) → U.replay (ns ++ [ n ]) σ ≡ U.replay ns (U.replay [ n ] σ)
replay-snoc []       n σ = refl
replay-snoc (U.notice j r b ∷ ns) n σ = cong (U.replay [ U.notice j r b ]) (replay-snoc ns n σ)

-- A fed environment, its step put back, is the reading one.
fedᴱ-≈ : ∀ {Γ A} {q} {a : Maybe A} {i : A ∈ Γ} {ρ σ : NEnv Γ} → Fedᴱ q a i ρ σ → ρ ≈ᴱ U.replay [ U.notice i q a ] σ
fedᴱ-≈ {q = q} {a} (here′ {l = l} e r) = ≃-trans e (put-cong q a (≃-refl (force l))) ∷ᵉ r
fedᴱ-≈ (there′ e f) = e ∷ᵉ fedᴱ-≈ f

-- A lane maker: each value's lanes, read in `ρ` wherever subscribed.
lanesᴺ : ∀ {Γ} {A B : Set} → (A → Pos → U.Node Γ B) → NEnv Γ → A → M.MonotonicList B
lanesᴺ g ρ x = M.cold λ r → U.meaning (g x r) ρ

-- A defer's notices put back on environments alike.
private
  notice-≈ : ∀ {Γ} (n : U.Notice Γ) {ρ σ : NEnv Γ} → ρ ≈ᴱ σ → U.replay [ n ] ρ ≈ᴱ U.replay [ n ] σ
  notice-≈ (U.notice (here refl) q a) (e ∷ᵉ r) = put-cong q a e ∷ᵉ r
  notice-≈ (U.notice (there i) q a)   (e ∷ᵉ r) = e ∷ᵉ notice-≈ (U.notice i q a) r

  replay-≈ : ∀ {Γ} ns {ρ σ : NEnv Γ} → ρ ≈ᴱ σ → U.replay ns ρ ≈ᴱ U.replay ns σ
  replay-≈ []                   e = e
  replay-≈ (U.notice i q a ∷ ns) e = notice-≈ (U.notice i q a) (replay-≈ ns e)

  hots-agree : ∀ {Γ} {ρ σ : NEnv Γ} → ρ ≈ᴱ σ → ∀ n → EnvAgree n (U.hots ρ) (U.hots σ)
  hots-agree []ᵉ      n = []ᵈ
  hots-agree (e ∷ᵉ r) n = hot-ne (agreeing e n) ∷ᵈ hots-agree r n

  live-true : ∀ Γ {A} (i : A ∈ Γ) → lookup (allLive Γ) i ≡ true
  live-true (_ ∷ Γ) (here refl) = refl
  live-true (_ ∷ Γ) (there i)   = live-true Γ i

  queue-≃ : ∀ {A B : Set} {n} {F G : A → M.MonotonicList B} → (∀ x → F x M.≈[ n ] G x) → ∀ qs → Queue n (map F qs) (map G qs)
  queue-≃ FG []       = []ᑫ
  queue-≃ FG (x ∷ qs) = FG x ∷ᑫ queue-≃ FG qs

-- A DEFER READS ALIKE ENVIRONMENTS ALIKE: the fold's meaning of the
-- program it defers, over the environment's runs made hot.
defer-≃ : ∀ {Γ A} (l : Later Timeline Γ A) p ns {ρ σ : NEnv Γ} → ρ ≈ᴱ σ → U.meaning (U.deferᶜ l p ns) ρ ≃ U.meaning (U.deferᶜ l p ns) σ
defer-≃ l p ns e = alike λ n → agree (≈ₖ-pred (deferᴰ-contractive (⟦⟧-ne (Later.force l) (hots-agree (replay-≈ ns e) n)))) p

-- A NODE READS ALIKE ENVIRONMENTS ALIKE: a flatMap's outer, its lanes in
-- flight and the lanes it has yet to subscribe each reading them from
-- where it joins.
mutual
  envs-≃ : ∀ {Γ A} (c : U.Node Γ A) {ρ σ : NEnv Γ} → ρ ≈ᴱ σ → U.meaning c ρ ≃ U.meaning c σ
  envs-≃ (U.framesᶜ τ r m)            e = ≃-refl _
  envs-≃ (U.burstᶜ τ r i b)           e = ≃-refl _
  envs-≃ (U.endᶜ r)                   e = ≃-refl _
  envs-≃ (U.ofᶜ r i xs)               e = ≃-refl _
  envs-≃ (U.mapᶜ f c)                 e = mapᴱ-≃ f (envs-≃ c e)
  envs-≃ (U.scanᶜ f z c)              e = scanᴱ-≃ f z (envs-≃ c e)
  envs-≃ (U.takeWhileᶜ i p c)         e = takeWhileᴱ-≃ i p (envs-≃ c e)
  envs-≃ (U.flatMapᶜ op g nothing ls qs) {ρ} {σ} e = alike λ n →
    go-ne (flatOp op) (lanesᴺ g ρ) (lanesᴺ g σ) (λ x → agrees λ r → agreeing (envs-≃ (g x r) e) n) doneᴼ (envsᴸ ls e n) (queue-≃ (λ x → agrees λ r → agreeing (envs-≃ (g x r) e) n) qs)
  envs-≃ (U.flatMapᶜ op g (just o) ls qs) {ρ} {σ} e = alike λ n →
    go-ne (flatOp op) (lanesᴺ g ρ) (lanesᴺ g σ) (λ x → agrees λ r → agreeing (envs-≃ (g x r) e) n) (liveᴼ (agreeing (envs-≃ o e) n)) (envsᴸ ls e n) (queue-≃ (λ x → agrees λ r → agreeing (envs-≃ (g x r) e) n) qs)
  envs-≃ (U.joinᶜ i p xs (just c))    e = ≃-refl _
  envs-≃ (U.joinᶜ i p xs nothing)     e = fedᴺ-≃ xs (rejoin-≃ p (lookup-≈ e i))
  envs-≃ (U.connectᶜ b (U.live s))    e = beside-≃ (envs-≃ b (s≃ ∷ᵉ e)) s≃
    where s≃ = envs-≃ s e
  envs-≃ (U.connectᶜ b (U.ended c))   e = envs-≃ b (≃-refl _ ∷ᵉ e)
  envs-≃ (U.deferᶜ l p ns)            e = defer-≃ l p ns e

  envsᴸ : ∀ {Γ A} (ls : List (U.Node Γ A)) {ρ σ : NEnv Γ} → ρ ≈ᴱ σ → ∀ n → Lanes n (U.meanings ls ρ) (U.meanings ls σ)
  envsᴸ []       e n = []ᴸ
  envsᴸ (c ∷ cs) e n = agreeing (envs-≃ c e) n ∷ᴸ envsᴸ cs e n

-- A body reads alike sources alike.
env-≃ : ∀ {Γ A B} (b : U.Node (A ∷ Γ) B) (ρ : NEnv Γ) {x y : Events A} → x ≃ y → U.meaning b (x ∷ᴬ ρ) ≃ U.meaning b (y ∷ᴬ ρ)
env-≃ b ρ e = envs-≃ b (e ∷ᵉ ≈ᴱ-refl ρ)

-- A DEFER FED ITS SOURCE'S STEP IS THE DEFER READING IT: its notices
-- put the step back on the environment it reads.
fed-defer : ∀ {Γ B} (l : Later Timeline Γ B) p ns → Fed (U.deferᶜ l p ns)
fed-defer l p ns i q a {ρ} {σ} f sn lv =
  subst (U.meaning (U.deferᶜ l p ns) ρ ≃_) (sym m) (defer-≃ l p ns (fedᴱ-≈ f))
  where m = cong (U.meaning (U.deferᶜ l p [])) (replay-snoc ns (U.notice i q a) σ)

-- Positions no earlier, and the events' first lagging.
≮-up : ∀ p q r → q <ᵖ r ≡ true → q <ᵖ p ≡ false → r <ᵖ p ≡ false
≮-up p q r qr qp with r <ᵖ p in e
... | false = refl
... | true  = trans (sym (<ᵖ-trans q r p qr e)) qp

<ᵖ-asym : ∀ p q → p <ᵖ q ≡ true → q <ᵖ p ≡ false
<ᵖ-asym p q h with q <ᵖ p in e
... | false = refl
... | true  = trans (sym (<ᵖ-trans p q p h e)) (<ᵖ-irrefl p)

not-true : ∀ {b} → not b ≡ true → b ≡ false
not-true {false} refl = refl

true-not : ∀ {b} → b ≡ false → not b ≡ true
true-not refl = refl

-- Two labels in order, a step past each.
part₂ : ∀ q {a b} → (a ∷ []) <ᵖ (b ∷ []) ≡ true → ((q ++ [ a ]) ++ [ ix 0 ]) <ᵖ ((q ++ [ b ]) ++ [ ix 0 ]) ≡ true
part₂ q {a} {b} h rewrite ++-assoc q [ a ] [ ix 0 ] | ++-assoc q [ b ] [ ix 0 ] = <ᵖ-part q (ix 0 ∷ []) (ix 0 ∷ []) h

-- No earlier, a step past each.
shift₂ : ∀ p q → p <ᵖ q ≡ false → ((p ++ [ ix 0 ]) ++ [ ix 0 ]) <ᵖ ((q ++ [ ix 0 ]) ++ [ ix 0 ]) ≡ false
shift₂ p q h = <ᵖ-shift (p ++ [ ix 0 ]) (q ++ [ ix 0 ]) (<ᵖ-shift p q h)

lags-agree : ∀ {A k} {x y : Events A} → Agree 1 x y → Lags k y → Lags k x
lags-agree (out⁼ _)  l = l
lags-agree (skip⁼ _) l = l
lags-agree end⁼      l = l
lags-agree hush⁼     l = l

lags₂-agree : ∀ {A k} {x y : Events A} → Agree 1 x y → Lags₂ k y → Lags₂ k x
lags₂-agree (out⁼ _)  l = l
lags₂-agree (skip⁼ _) l = l
lags₂-agree end⁼      l = l
lags₂-agree hush⁼     l = l

lags-up : ∀ {A} k (e : Events A) → Lags k e → Lags₂ k e
lags-up k (out h _ _) l = ≮-up k (h ++ [ ix 0 ]) _ (<ᵖ-below (h ++ [ ix 0 ]) []) l
lags-up k (skip h _)  l = ≮-up k (h ++ [ ix 0 ]) _ (<ᵖ-below (h ++ [ ix 0 ]) []) l
lags-up k (end c)     l = ≮-up k (c ++ [ ix 0 ]) _ (<ᵖ-below (c ++ [ ix 0 ]) []) l
lags-up k hush        l = tt

-- What a step shows lags whatever its head does.
wins-lags : ∀ {Γ A k} (ρ : NEnv Γ) (s : U.Step Γ A) → Wins (just k) (U.headˢ s) ≡ true → Lags k (afterᴱ ρ s)
wins-lags ρ (U.outˢ h _ _) w = not-true w
wins-lags ρ (U.skipˢ h _)  w = not-true w
wins-lags ρ (U.endˢ h)     w = not-true w
wins-lags ρ U.hushˢ        w = tt

wins-lags₂ : ∀ {Γ A k} (ρ : NEnv Γ) (s : U.Step Γ A) → Wins (just k) (shift (U.headˢ s)) ≡ true → Lags₂ k (afterᴱ ρ s)
wins-lags₂ ρ (U.outˢ h _ _) w = not-true w
wins-lags₂ ρ (U.skipˢ h _)  w = not-true w
wins-lags₂ ρ (U.endˢ h)     w = not-true w
wins-lags₂ ρ U.hushˢ        w = tt

-- The stream functions keep a lag: a value stays where it is, a cut
-- moves it later.
lags-map : ∀ {A B k} (f : A → B) (e : Events A) → Lags k e → Lags k (M.mapᴱ f e)
lags-map f (out _ _ _) l = l
lags-map f (skip _ _)  l = l
lags-map f (end _)     l = l
lags-map f hush        l = l

lags-scan : ∀ {A B k} (f : B → A → B) z (e : Events A) → Lags k e → Lags k (M.scanᴱ f z e)
lags-scan f z (out _ _ _) l = l
lags-scan f z (skip _ _)  l = l
lags-scan f z (end _)     l = l
lags-scan f z hush        l = l

lags-take : ∀ {A} k i (p : A → Bool) (e : Events A) → Lags k e → Lags k (M.takeWhileᴱ i p e)
lags-take k i p (out h a r) l with p a
lags-take k i     p (out h a r) l | true  = l
lags-take k true  p (out h a r) l | false = ≮-up k (h ++ [ ix 0 ]) _ (<ᵖ-below (h ++ [ ix 0 ]) []) l
lags-take k false p (out h a r) l | false = ≮-up k (h ++ [ ix 0 ]) _ cut l
  where cut : (h ++ [ ix 0 ]) <ᵖ ((h ++ [ last ]) ++ [ ix 0 ]) ≡ true
        cut rewrite ++-assoc h [ last ] [ ix 0 ] = <ᵖ-part h [] (ix 0 ∷ []) refl
lags-take k i p (skip _ _) l = l
lags-take k i p (end _)    l = l
lags-take k i p hush       l = tt

-- A joiner's rejoined run lags what it was fed of a run lagging a step
-- past: whatever it shows lands under its source's position, or past
-- its own subscription.
lags-rejoin : ∀ {A} k p (e : Events A) → Lags₂ k e → Lags k (M.rejoin p e)
lags-rejoin k p (out q a r) l with p <ᵖ q in e
... | true  = ≮-up k ((q ++ [ ix 0 ]) ++ [ ix 0 ]) _ (part₂ q refl) l
... | false = ≮-trans k ((q ++ [ ix 0 ]) ++ [ ix 0 ]) ((p ++ [ ix 0 ]) ++ [ ix 0 ]) l (shift₂ p q e)
lags-rejoin k p (skip q r) l with p <ᵖ q in e
... | true  = ≮-up k ((q ++ [ ix 0 ]) ++ [ ix 0 ]) _ (part₂ q refl) l
... | false = ≮-trans k ((q ++ [ ix 0 ]) ++ [ ix 0 ]) ((p ++ [ ix 0 ]) ++ [ ix 0 ]) l (shift₂ p q e)
lags-rejoin k p (end c) l with p <ᵖ c in e
... | true  = ≮-up k ((c ++ [ ix 0 ]) ++ [ ix 0 ]) _ (part₂ c refl) l
... | false = ≮-up k ((p ++ [ ix 0 ]) ++ [ ix 0 ]) _ (part₂ p refl) (≮-trans k ((c ++ [ ix 0 ]) ++ [ ix 0 ]) ((p ++ [ ix 0 ]) ++ [ ix 0 ]) l (shift₂ p c e))
lags-rejoin k p hush l = tt

-- A connect's meaning lags as its body does and its source a step past.
lags-ahead : ∀ {A B} k (x : Events B) q (r : Events∞ A) b → Lags k x → (q ++ [ ix 0 ]) <ᵖ k ≡ false → Lags k (M.ahead x q r b)
lags-ahead k x           q r true  lx lq = lq
lags-ahead k (out _ _ _) q r false lx lq = lx
lags-ahead k (skip _ _)  q r false lx lq = lx
lags-ahead k (end _)     q r false lx lq = lx
lags-ahead k hush        q r false lx lq = tt

lags-beside : ∀ {A B} k (x : Events B) (y : Events A) → Lags k x → Lags₂ k y → Lags k (M.beside x y)
lags-beside k x (out q _ r) lx ly = lags-ahead k x (q ++ [ ix 0 ]) r _ lx ly
lags-beside k x (skip q r)  lx ly = lags-ahead k x (q ++ [ ix 0 ]) r _ lx ly
lags-beside k x (end c)     lx ly = lags-ahead k x (c ++ [ ix 0 ]) M.hushed _ lx ly
lags-beside k x hush        lx ly = lx

-- Under `k`, a position comes first, or lags `k` itself: a source
-- coming before it a step past lags `k` two steps past.
pass : ∀ {Γ} h (δ : Env Γ) k → Under k δ → First (just h) δ ⊎ (h ++ [ ix 0 ]) <ᵖ k ≡ false
pass h []              k u        = inj₁ tt
pass h (U.ended _ ∷ δ) k u        = pass h δ k u
pass h (U.live s  ∷ δ) k (u₁ , u) = go (U.headˢ (U.step s)) u₁ (pass h δ k u)
  where go : ∀ m → Wins (just k) (shift m) ≡ true → First (just h) δ ⊎ (h ++ [ ix 0 ]) <ᵖ k ≡ false
           → (Wins (just h) m ≡ true × First (just h) δ) ⊎ (h ++ [ ix 0 ]) <ᵖ k ≡ false
        go m        u₁ (inj₂ l) = inj₂ l
        go nothing  u₁ (inj₁ f) = inj₁ (refl , f)
        go (just r) u₁ (inj₁ f) with (r ++ [ ix 0 ]) <ᵖ h in e
        ... | false = inj₁ (refl , f)
        ... | true  = inj₂ (≮-trans k ((r ++ [ ix 0 ]) ++ [ ix 0 ]) (h ++ [ ix 0 ]) (not-true u₁) (<ᵖ-shift h (r ++ [ ix 0 ]) (<ᵖ-asym _ h e)))

-- Coming first is under.
first-under : ∀ {Γ} k (δ : Env Γ) → First (just k) δ → Under k δ
first-under k []              tt      = tt
first-under k (U.ended _ ∷ δ) f       = first-under k δ f
first-under k (U.live s  ∷ δ) (w , f) = up (U.headˢ (U.step s)) w , first-under k δ f
  where up : ∀ m → Wins (just k) m ≡ true → Wins (just k) (shift m) ≡ true
        up nothing  w = refl
        up (just r) w = true-not (≮-up k (r ++ [ ix 0 ]) _ (<ᵖ-below (r ++ [ ix 0 ]) []) (not-true w))

-- A joiner's source lags a step past.
lags-env : ∀ {Γ A} (δ : Env Γ) → Settled δ → ∀ k → Under k δ → (i : A ∈ Γ) → lookup (flags δ) i ≡ true → Lags₂ k (lookup (ρᴱ δ) i)
lags-env (U.live s  ∷ δ) (_ , _ , lg , st) k (u₁ , u) (here refl) l = lg k u₁ u
lags-env (U.live s  ∷ δ) (_ , _ , _ , st)  k (_ , u)  (there i)   l = lags-env δ st k u i l
lags-env (U.ended c ∷ δ) st                k u        (here refl) ()
lags-env (U.ended c ∷ δ) st                k u        (there i)   l = lags-env δ st k u i l

-- An untold joiner's connect runs.
told-live : ∀ {b} → Told b nothing → b ≡ true
told-live {true} t = refl

-- A connect's step taken after `k`: its body's is, and its source's a
-- step past.
body-head : ∀ {Γ A B} (s : U.Source Γ A) (sb : U.Step (A ∷ Γ) B) → U.headˢ (U.bodyˢ s sb) ≡ U.headˢ sb
body-head s (U.outˢ _ _ _) = refl
body-head s (U.skipˢ _ _)  = refl
body-head s (U.endˢ _)     = refl
body-head s U.hushˢ        = refl

tie-wins : ∀ {Γ B} k q (sb : U.Step Γ B) → U.beforeˢ (q ++ [ ix 0 ]) sb ≡ true → Wins (just k) (just (q ++ [ ix 0 ])) ≡ true → Wins (just k) (U.headˢ sb) ≡ true
tie-wins k q (U.outˢ h _ _) e w = true-not (≮-trans k ((q ++ [ ix 0 ]) ++ [ ix 0 ]) (h ++ [ ix 0 ]) (not-true w) (<ᵖ-shift h (q ++ [ ix 0 ]) (<ᵖ-asym _ h e)))
tie-wins k q (U.skipˢ h _)  e w = true-not (≮-trans k ((q ++ [ ix 0 ]) ++ [ ix 0 ]) (h ++ [ ix 0 ]) (not-true w) (<ᵖ-shift h (q ++ [ ix 0 ]) (<ᵖ-asym _ h e)))
tie-wins k q (U.endˢ h)     e w = true-not (≮-trans k ((q ++ [ ix 0 ]) ++ [ ix 0 ]) (h ++ [ ix 0 ]) (not-true w) (<ᵖ-shift h (q ++ [ ix 0 ]) (<ᵖ-asym _ h e)))
tie-wins k q U.hushˢ        e w = refl

untie-wins : ∀ {Γ B} k q (sb : U.Step Γ B) → U.beforeˢ (q ++ [ ix 0 ]) sb ≡ false → Wins (just k) (U.headˢ sb) ≡ true → Wins (just k) (just (q ++ [ ix 0 ])) ≡ true
untie-wins k q (U.outˢ h _ _) e w = true-not (≮-trans k (h ++ [ ix 0 ]) ((q ++ [ ix 0 ]) ++ [ ix 0 ]) (not-true w) (<ᵖ-shift (q ++ [ ix 0 ]) h e))
untie-wins k q (U.skipˢ h _)  e w = true-not (≮-trans k (h ++ [ ix 0 ]) ((q ++ [ ix 0 ]) ++ [ ix 0 ]) (not-true w) (<ᵖ-shift (q ++ [ ix 0 ]) h e))
untie-wins k q (U.endˢ h)     e w = true-not (≮-trans k (h ++ [ ix 0 ]) ((q ++ [ ix 0 ]) ++ [ ix 0 ]) (not-true w) (<ᵖ-shift (q ++ [ ix 0 ]) h e))
untie-wins k q U.hushˢ        () w

pick-wins : ∀ {Γ Δ B} k q (sb : U.Step Δ B) (t : U.Node Γ B) (bs : U.Step Γ B) d → U.beforeˢ (q ++ [ ix 0 ]) sb ≡ d → U.headˢ bs ≡ U.headˢ sb
          → Wins (just k) (U.headˢ (if d then U.skipˢ (q ++ [ ix 0 ]) t else bs)) ≡ true
          → Wins (just k) (U.headˢ sb) ≡ true × Wins (just k) (just (q ++ [ ix 0 ])) ≡ true
pick-wins k q sb t bs true  e hb w = tie-wins k q sb e w , w
pick-wins k q sb t bs false e hb w = wb , untie-wins k q sb e wb
  where wb = subst (λ m → Wins (just k) m ≡ true) hb w

source-wins : ∀ {Γ A B} k (b : U.Node (A ∷ Γ) B) (sb : U.Step (A ∷ Γ) B) (s : U.Node Γ A) (ss : U.Step Γ A)
            → Wins (just k) (U.headˢ (U.sourceˢ b sb s ss)) ≡ true → Wins (just k) (U.headˢ sb) ≡ true × Wins (just k) (shift (U.headˢ ss)) ≡ true
source-wins k b sb s (U.outˢ q a s′) w = pick-wins k q sb _ (U.bodyˢ (U.live s) sb) _ refl (body-head (U.live s) sb) w
source-wins k b sb s (U.skipˢ q s′)  w = pick-wins k q sb _ (U.bodyˢ (U.live s) sb) _ refl (body-head (U.live s) sb) w
source-wins k b sb s (U.endˢ c)      w = pick-wins k c sb _ (U.bodyˢ (U.live s) sb) _ refl (body-head (U.live s) sb) w
source-wins k b sb s U.hushˢ         w = subst (λ m → Wins (just k) m ≡ true) (body-head (U.live s) sb) w , refl

postulate

  -- A NODE'S MEANING LEADS NOTHING: whatever it shows at `j`, which comes
  -- before its step and its sources', is a skip, and the rest comes
  -- strictly after.  A joiner placed at its source's next step shows a
  -- pre-join skip there, and nothing in the placing says positions never
  -- meet; an event there would come ahead of the source's tied step.
  --
  -- REFUTED: 07140662 strictly after `j`, by a joiner placed at its source's next step
  -- REFUTED: 7d5d0332 stated without the node sane, by a joiner untold of an ended source
  leads : ∀ {Γ A} (c : U.Node Γ A) (δ : Env Γ) → Settled δ → Sane (flags δ) c → Placed c (ρᴱ δ) → ∀ j
        → U.beforeˢ j (U.step c) ≡ true → First (just j) δ → Tied j (U.meaning c (ρᴱ δ))

  -- A STEP KEEPS THE GHOST PLACED: a step coming first leaves the stepped
  -- node placed, atop what the step shows.
  --
  -- REFUTED: d2d13661 without the step coming first, by a merge whose joiner lane shows its source's earlier event
  -- REFUTED: c8c55884 over a placing with each live joiner joined before its source, by a lane admitted past its source's next event
  placed-after : ∀ {Γ A} (c : U.Node Γ A) (δ : Env Γ) → Settled δ → Sane (flags δ) c → Placed c (ρᴱ δ)
               → First (U.headˢ (U.step c)) δ → Placedˢ (ρᴱ δ) (U.step c)

-- A NODE FED ITS SOURCE'S STEP IS ALIKE THE NODE READING IT, at
-- whichever connect's index it reads that source: a joiner fed the step
-- its source shows at `q`, a value or a skip, reading the source past
-- it.  Every joiner is fed, those the node has yet to make included (a
-- lane's `g`, a defer's notices, which put the step back on what the
-- defer reads), so the node may show anything before the step; and a
-- joiner told its end is fed all the same, so none may be told while
-- the source runs.  A cut and a connect are congruences, a connect's
-- body fed one index further out.
--
-- REFUTED: 082ad778 stated without the body sane, by a joiner told its end
-- DEAD ROUTE: exact agreement with a ghost anchored in its sources'
--   step history.  The ghost is the witness's open part (`part`), which
--   keeps no count of a source's steps, and a silent run is matched by
--   the residual as a set alone (`Ahead`), so no field of the witness
--   can keep the count a lane's pre-join skips need.
-- RECOVERY: git show 950a4208 restores step-alike over step-agrees
mutual
  fed-≃ : ∀ {Γ B} (b : U.Node Γ B) → Fed b
  fed-≃ (U.framesᶜ _ _ _)         i q a f sn lv = ≃-refl _
  fed-≃ (U.burstᶜ _ _ _ _)        i q a f sn lv = ≃-refl _
  fed-≃ (U.endᶜ _)                i q a f sn lv = ≃-refl _
  fed-≃ (U.ofᶜ _ _ _)             i q a f sn lv = ≃-refl _
  fed-≃ (U.mapᶜ g c)              i q a f sn lv = mapᴱ-≃ g (fed-≃ c i q a f sn lv)
  fed-≃ (U.scanᶜ g z c)           i q a f sn lv = scanᴱ-≃ g z (fed-≃ c i q a f sn lv)
  fed-≃ (U.takeWhileᶜ j p c)      i q a f sn lv = takeWhileᴱ-≃ j p (fed-≃ c i q a f sn lv)
  fed-≃ {Γ} (U.flatMapᶜ op g nothing ls qs) i q a {ρ} {σ} f (_ , sl , sg) lv = alike λ n →
    go-ne (flatOp op) (lanesᴺ g ρ) (lanesᴺ (λ x r → U.feed i q a (g x r)) σ) (G n) doneᴼ (fedᴸ ls i q a f sl lv n) (queue-≃ (G n) qs)
    where G : ∀ n x → lanesᴺ g ρ x M.≈[ n ] lanesᴺ (λ x r → U.feed i q a (g x r)) σ x
          G n x = agrees λ r → agreeing (fed-≃ (g x r) i q a f (sg x r) (live-true Γ i)) n
  fed-≃ {Γ} (U.flatMapᶜ op g (just o) ls qs) i q a {ρ} {σ} f (so , sl , sg) lv = alike λ n →
    go-ne (flatOp op) (lanesᴺ g ρ) (lanesᴺ (λ x r → U.feed i q a (g x r)) σ) (G n) (liveᴼ (agreeing (fed-≃ o i q a f so lv) n)) (fedᴸ ls i q a f sl lv n) (queue-≃ (G n) qs)
    where G : ∀ n x → lanesᴺ g ρ x M.≈[ n ] lanesᴺ (λ x r → U.feed i q a (g x r)) σ x
          G n x = agrees λ r → agreeing (fed-≃ (g x r) i q a f (sg x r) (live-true Γ i)) n
  fed-≃ (U.joinᶜ j p xs e)        i q a f {ν} sn lv = fed-joiner f {ν} lv j p xs e sn
  fed-≃ (U.connectᶜ b (U.live s)) i q a f {ν} (sb , ss) lv =
    beside-≃ (fed-≃ b (there i) q a (there′ s≃ f) {true ∷ᴬ ν} sb lv) s≃
    where s≃ = fed-≃ s i q a f {ν} ss lv
  fed-≃ (U.connectᶜ b (U.ended c)) i q a f {ν} sn lv =
    fed-≃ b (there i) q a (there′ (≃-refl (end c)) f) {false ∷ᴬ ν} sn lv
  fed-≃ (U.deferᶜ l p ns)         i q a f {ν} sn lv = fed-defer l p ns i q a f {ν} sn lv

  fedᴸ : ∀ {Γ A B} (ls : List (U.Node Γ B)) (i : A ∈ Γ) q (a : Maybe A) {ρ σ : NEnv Γ} → Fedᴱ q a i ρ σ
       → ∀ {ν} → Saneᴸ ν ls → lookup ν i ≡ true → ∀ n → Lanes n (U.meanings ls ρ) (U.meanings (U.feedᴸ i q a ls) σ)
  fedᴸ []       i q a f sn       lv n = []ᴸ
  fedᴸ (c ∷ cs) i q a f (sc , sl) lv n = agreeing (fed-≃ c i q a f sc lv) n ∷ᴸ fedᴸ cs i q a f sl lv n

-- The source's rest, each event no earlier than `Q` once shown.
Behind : ∀ {A} → Pos → Events A → Set
Behind Q (out q′ _ _) = (q′ ++ [ ix 0 ]) <ᵖ Q ≡ false
Behind Q (skip q′ _)  = (q′ ++ [ ix 0 ]) <ᵖ Q ≡ false
Behind Q (end q′)     = (q′ ++ [ ix 0 ]) <ᵖ Q ≡ false
Behind Q hush         = ⊤

behind : ∀ {A} q (e : Events A) → Atop q e → Behind (q ++ [ ix 0 ]) e
behind q (out q′ _ _) at = <ᵖ-shift q′ q at
behind q (skip q′ _)  at = <ᵖ-shift q′ q at
behind q (end q′)     at = <ᵖ-shift q′ q at
behind q hush         at = tt

-- A body's skip at `Q` goes ahead of a source's rest behind it.
tie-tail : ∀ {A B} Q (r : Events∞ B) (e : Events A) (l : Events∞ B) → force l ≡ M.beside (force r) e → Behind Q e
         → ∀ n → Agree n (M.beside (skip Q r) e) (skip Q l)
tie-tail Q r e            l f b zero    = stop
tie-tail Q r (out q′ _ _) l f b (suc n) rewrite b = skip⁼ (subst (Agree n _) (sym f) (agree-refl n _))
tie-tail Q r (skip q′ _)  l f b (suc n) rewrite b = skip⁼ (subst (Agree n _) (sym f) (agree-refl n _))
tie-tail Q r (end q′)     l f b (suc n) rewrite b = skip⁼ (subst (Agree n _) (sym f) (agree-refl n _))
tie-tail Q r hush         l f b (suc n) = skip⁼ (subst (Agree n _) (sym f) (agree-refl n _))

-- EVENTS AT ONE POSITION COMMUTE: a source's step taken ahead of the
-- body's skips at its own position.
module _ {A} (q : Pos) (t : Events∞ A) (at : Atop q (force t)) where
  private
    Q : Pos
    Q = q ++ [ ix 0 ]

    -- the rest of the connect, the body read beside the source's rest
    rest : ∀ {B} → Events B → Events∞ B
    force (rest x) = M.beside x (force t)

    tie-run : ∀ {B} (x : Events B) n → Tied Q x → Agree n (M.ahead x Q t (M.before Q x)) (skip Q (rest x))
    tie-run x zero td = stop
    tie-run x (suc n) td with tie td
    tie-run x (suc n) td | past b rewrite b = skip⁼ (agree-refl n _)
    tie-run (skip Q r) (suc n) td | tied td′ rewrite <ᵖ-irrefl Q =
      skip⁼ (agree-trans (tie-run (force r) n td′) (agree-sym (tie-tail Q r (force t) (rest (force r)) refl (behind q (force t) at) n)))

  -- The source's next taken first, ahead of the body's skips at the same
  -- position.
  tie-lead : ∀ {B} (x : Events B) → Tied Q x → M.ahead x Q t (M.before Q x) ≃ skip Q (rest x)
  tie-lead x td = alike λ n → tie-run x n td

-- The source's next taken after the body's step.
LagsHead : ∀ {Γ A B} → U.Step Γ B → Events A → Set
LagsHead (U.outˢ k _ _) e = Lags k e
LagsHead (U.skipˢ k _)  e = Lags k e
LagsHead (U.endˢ k)     e = Lags k e
LagsHead U.hushˢ        e = ⊥

beside-head : ∀ {Γ A B} (s : U.Node Γ A) (ρ : NEnv Γ) (sb : U.Step (A ∷ Γ) B) → LagsHead sb (U.meaning s ρ)
            → M.beside (afterᴱ (U.meaning s ρ ∷ᴬ ρ) sb) (U.meaning s ρ) ≃ afterᴱ ρ (U.bodyˢ (U.live s) sb)
beside-head s ρ (U.outˢ k a b) lag = beside-out k a _ (U.meaning s ρ) _ lag refl
beside-head s ρ (U.skipˢ k b)  lag = beside-skip k _ (U.meaning s ρ) _ lag refl
beside-head s ρ (U.endˢ k)     lag = beside-end k (U.meaning s ρ) lag

-- The connect, its body's step and its source's named.
conn : ∀ {Γ A B} (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (δ : Env Γ) (st : Settled δ)
     → Sane (flags δ) (U.connectᶜ b (U.live s)) → Placed (U.connectᶜ b (U.live s)) (ρᴱ δ)
     → (sb : U.Step (A ∷ Γ) B) (ss : U.Step Γ A)
     → (Wins (U.headˢ sb) (U.headˢ ss) ≡ true → First (U.headˢ sb) δ → U.meaning b (U.meaning s (ρᴱ δ) ∷ᴬ ρᴱ δ) ≃ afterᴱ (U.meaning s (ρᴱ δ) ∷ᴬ ρᴱ δ) sb)
     → (First (U.headˢ ss) δ → U.meaning s (ρᴱ δ) ≃ afterᴱ (ρᴱ δ) ss)
     → (∀ k → Wins (just k) (U.headˢ ss) ≡ true → First (just k) δ → Lags k (U.meaning s (ρᴱ δ)))
     → (∀ j → U.beforeˢ j sb ≡ true → Wins (just j) (U.headˢ ss) ≡ true → First (just j) δ → Tied j (U.meaning b (U.meaning s (ρᴱ δ) ∷ᴬ ρᴱ δ)))
     → (First (U.headˢ ss) δ → Placedˢ (ρᴱ δ) ss)
     → First (U.headˢ (U.sourceˢ b sb s ss)) δ
     → U.meaning (U.connectᶜ b (U.live s)) (ρᴱ δ) ≃ afterᴱ (ρᴱ δ) (U.sourceˢ b sb s ss)
conn b s δ st sn _ sb ss hb hs lg ld pas fi = go sb ss hb hs lg ld pas fi
  where
  ρ  = ρᴱ δ
  ms = U.meaning s ρ
  MB = U.meaning b (ms ∷ᴬ ρ)

  -- The body's step taken first.
  body : ∀ sb → MB ≃ afterᴱ (ms ∷ᴬ ρ) sb → LagsHead sb ms → M.beside MB ms ≃ afterᴱ ρ (U.bodyˢ (U.live s) sb)
  body sb e lag = ≃-trans (beside-≃ e (≃-refl ms)) (beside-head s ρ sb lag)

  go : ∀ sb ss
     → (Wins (U.headˢ sb) (U.headˢ ss) ≡ true → First (U.headˢ sb) δ → MB ≃ afterᴱ (ms ∷ᴬ ρ) sb)
     → (First (U.headˢ ss) δ → ms ≃ afterᴱ ρ ss)
     → (∀ k → Wins (just k) (U.headˢ ss) ≡ true → First (just k) δ → Lags k ms)
     → (∀ j → U.beforeˢ j sb ≡ true → Wins (just j) (U.headˢ ss) ≡ true → First (just j) δ → Tied j MB)
     → (First (U.headˢ ss) δ → Placedˢ ρ ss)
     → First (U.headˢ (U.sourceˢ b sb s ss)) δ → M.beside MB ms ≃ afterᴱ ρ (U.sourceˢ b sb s ss)
  go U.hushˢ          U.hushˢ hb hs lg ld pas fi =
    beside-≃ (hb refl fi) (hs fi)
  go sb@(U.outˢ k _ _) U.hushˢ hb hs lg ld pas fi = body sb (hb refl fi) (lg k refl fi)
  go sb@(U.skipˢ k _)  U.hushˢ hb hs lg ld pas fi = body sb (hb refl fi) (lg k refl fi)
  go sb@(U.endˢ k)     U.hushˢ hb hs lg ld pas fi = body sb (hb refl fi) (lg k refl fi)
  go sb (U.outˢ q x s′) hb hs lg ld pas fi with U.beforeˢ (q ++ [ ix 0 ]) sb in eq
  go U.hushˢ           (U.outˢ q x s′) hb hs lg ld pas fi | false with () ← eq
  go sb@(U.outˢ k _ _) (U.outˢ q x s′) hb hs lg ld pas fi | false = body sb (hb (cong not eq) fi) (lg k (cong not eq) fi)
  go sb@(U.skipˢ k _)  (U.outˢ q x s′) hb hs lg ld pas fi | false = body sb (hb (cong not eq) fi) (lg k (cong not eq) fi)
  go sb@(U.endˢ k)     (U.outˢ q x s′) hb hs lg ld pas fi | false = body sb (hb (cong not eq) fi) (lg k (cong not eq) fi)
  go sb (U.outˢ q x s′) hb hs lg ld pas fi | true =
    ≃-trans (beside-≃ (≃-refl MB) e₁)
   (≃-trans (tie-lead q _ atq MB td)
            (skip-cong (beside-≃ (fed-≃ b (here refl) q (just x) (here′ e₁ (≈ᴱ-refl ρ)) (proj₁ sn) refl) (≃-refl (U.meaning s′ (ρᴱ δ))))))
    where e₁ = hs (first-sub q δ fi)
          atq = proj₁ (pas (first-sub q δ fi))
          td = ld (q ++ [ ix 0 ]) eq (wins-self q) fi
  go sb (U.skipˢ q s′) hb hs lg ld pas fi with U.beforeˢ (q ++ [ ix 0 ]) sb in eq
  go U.hushˢ           (U.skipˢ q s′) hb hs lg ld pas fi | false with () ← eq
  go sb@(U.outˢ k _ _) (U.skipˢ q s′) hb hs lg ld pas fi | false = body sb (hb (cong not eq) fi) (lg k (cong not eq) fi)
  go sb@(U.skipˢ k _)  (U.skipˢ q s′) hb hs lg ld pas fi | false = body sb (hb (cong not eq) fi) (lg k (cong not eq) fi)
  go sb@(U.endˢ k)     (U.skipˢ q s′) hb hs lg ld pas fi | false = body sb (hb (cong not eq) fi) (lg k (cong not eq) fi)
  go sb (U.skipˢ q s′) hb hs lg ld pas fi | true =
    ≃-trans (beside-≃ (≃-refl MB) e₁)
   (≃-trans (tie-lead q _ atq MB td)
            (skip-cong (beside-≃ (fed-≃ b (here refl) q nothing (here′ e₁ (≈ᴱ-refl ρ)) (proj₁ sn) refl) (≃-refl (U.meaning s′ (ρᴱ δ))))))
    where e₁ = hs (first-sub q δ fi)
          atq = proj₁ (pas (first-sub q δ fi))
          td = ld (q ++ [ ix 0 ]) eq (wins-self q) fi
  go sb (U.endˢ c) hb hs lg ld pas fi with U.beforeˢ (c ++ [ ix 0 ]) sb in eq
  go U.hushˢ           (U.endˢ c) hb hs lg ld pas fi | false with () ← eq
  go sb@(U.outˢ k _ _) (U.endˢ c) hb hs lg ld pas fi | false = body sb (hb (cong not eq) fi) (lg k (cong not eq) fi)
  go sb@(U.skipˢ k _)  (U.endˢ c) hb hs lg ld pas fi | false = body sb (hb (cong not eq) fi) (lg k (cong not eq) fi)
  go sb@(U.endˢ k)     (U.endˢ c) hb hs lg ld pas fi | false = body sb (hb (cong not eq) fi) (lg k (cong not eq) fi)
  go sb (U.endˢ c) hb hs lg ld pas fi | true =
    ≃-trans (beside-≃ (≃-refl MB) e₁)
   (≃-trans (tie-lead c M.hushed tt MB (ld (c ++ [ ix 0 ]) eq (wins-self c) fi))
            (skip-cong (subst (MB ≃_) (sym (shut-meaning (here refl) c b (end c ∷ᴬ ρ) refl))
                              (env-≃ b ρ e₁))))
    where e₁ = hs (first-sub c δ fi)

-- A RUNNING CONNECT STEPS AS IT MEANS: its body, reading its source, and
-- its source, each showing its step whenever it comes first, the
-- connect's meaning is what its step shows: its body's step or its
-- source's, a value fed to the body's joiners.
------------------------------------------------------------------------
-- Every node

mutual
  -- A NODE'S MEANING LAGS: whatever it shows is taken after a body's
  -- event at `k` that comes before its step, and before its sources' a
  -- step past, since what a joiner is fed lands past its source's
  -- position.  A cut's step may come later than its node's, so a cut
  -- whose node comes first reads its meaning off its step.
  --
  -- REFUTED: 3cab1ca8 stated without the node sane, by a joiner untold of an ended source
  lags : ∀ {Γ A} (c : U.Node Γ A) (δ : Env Γ) → Settled δ → Sane (flags δ) c → Placed c (ρᴱ δ) → ∀ k
       → Wins (just k) (U.headˢ (U.step c)) ≡ true → Under k δ → Lags k (U.meaning c (ρᴱ δ))
  lags (U.framesᶜ τ e m)  δ st sn pl k w u = lags-agree (agreeing (frames-after τ e m) 1) (wins-lags (ρᴱ δ) (U.framesˢ τ e m) w)
  lags (U.burstᶜ τ r i b) δ st sn pl k w u = lags-agree (agreeing (burst-after τ r i b) 1) (wins-lags (ρᴱ δ) (U.burstˢ τ r i b) w)
  lags (U.endᶜ p)         δ st sn pl k w u = not-true w
  lags (U.ofᶜ p i xs)     δ st sn pl k w u = lags-agree (agreeing (of-after p i xs) 1) (wins-lags (ρᴱ δ) (U.ofˢ p i xs) w)
  lags (U.mapᶜ f c)       δ st sn (_ , pc) k w u =
    lags-map f _ (lags c δ st sn pc k (subst (λ m → Wins (just k) m ≡ true) (map-head f (U.step c)) w) u)
  lags (U.scanᶜ f z c)    δ st sn (_ , pc) k w u =
    lags-scan f z _ (lags c δ st sn pc k (subst (λ m → Wins (just k) m ≡ true) (scan-head f z (U.step c)) w) u)
  lags (U.takeWhileᶜ i p c) δ st sn (_ , pc) k w u with U.headˢ (U.step c) in eh
  ... | nothing = lags-take k i p _ (lags c δ st sn pc k (subst (λ m → Wins (just k) m ≡ true) (sym eh) refl) u)
  ... | just h with pass h δ k u
  ...   | inj₂ l = lags-take k i p _ (lags c δ st sn pc k (subst (λ m → Wins (just k) m ≡ true) (sym eh) (true-not l)) u)
  ...   | inj₁ f = lags-agree (agreeing (≃-trans (takeWhileᴱ-≃ i p (os c δ st sn pc (subst (λ m → First m δ) (sym eh) f))) (take-after i p (U.step c))) 1)
                              (wins-lags (ρᴱ δ) (U.takeWhileˢ i p (U.step c)) w)
  lags (U.flatMapᶜ op g o ls qs) δ st sn pl k w u = lags-flat op g o ls qs δ st sn pl k w u
  lags (U.joinᶜ i p ((q , just a) ∷ xs) e) δ st sn pl k w u = not-true w
  lags (U.joinᶜ i p ((q , nothing) ∷ xs) e) δ st sn pl k w u = not-true w
  lags (U.joinᶜ i p [] (just c)) δ st sn pl k w u = not-true w
  lags (U.joinᶜ i p [] nothing)  δ st sn pl k w u = lags-rejoin k p _ (lags-env δ st k u i (told-live sn))
  lags (U.connectᶜ b (U.live s)) δ st (sb , ss) (_ , pb , ps) k w u =
    lags-beside k _ _ (lags b (U.live s ∷ δ) (hs , ps , lg , st) sb pb k (proj₁ sw) (proj₂ sw , u)) (lg k (proj₂ sw) u)
    where hs = os s δ st ss ps
          lg : Lagging s δ
          lg k w u = lags₂ s δ st hs ss ps k w u
          sw = source-wins k b (U.step b) s (U.step s) w
  lags (U.connectᶜ b (U.ended c)) δ st sn (_ , pb) k w u =
    lags b (U.ended c ∷ δ) st sn pb k (subst (λ m → Wins (just k) m ≡ true) (shut-head c (U.step b)) w) u
  lags (U.deferᶜ l p ns)  δ st sn pl k w u =
    lags-agree (agreeing (defer-after l p ns (ρᴱ δ)) 1) (wins-lags (ρᴱ δ) (U.step (U.deferᶜ l p ns)) w)

  -- A SOURCE'S MEANING LAGS A STEP PAST: its step comes first, and shows,
  -- or lags `k` itself.
  lags₂ : ∀ {Γ A} (s : U.Node Γ A) (δ : Env Γ) → Settled δ → Shows s δ → Sane (flags δ) s → Placed s (ρᴱ δ) → Lagging s δ
  lags₂ s δ st hs sn pl k w u with U.headˢ (U.step s) in eh
  ... | nothing = lags-up k _ (lags s δ st sn pl k (subst (λ m → Wins (just k) m ≡ true) (sym eh) refl) u)
  ... | just h with pass h δ k u
  ...   | inj₂ l = lags-up k _ (lags s δ st sn pl k (subst (λ m → Wins (just k) m ≡ true) (sym eh) (true-not l)) u)
  ...   | inj₁ f = lags₂-agree (agreeing (hs f) 1)
                               (wins-lags₂ (ρᴱ δ) (U.step s) (subst (λ m → Wins (just k) (shift m) ≡ true) (sym eh) w))

  live-skips : ∀ {Γ A B} (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (δ : Env Γ) → Settled δ
             → Sane (flags δ) (U.connectᶜ b (U.live s)) → Placed (U.connectᶜ b (U.live s)) (ρᴱ δ)
             → Shows b (U.live s ∷ δ) → Shows s δ → Shows (U.connectᶜ b (U.live s)) δ
  live-skips b s δ st sn@(sbn , sns) pl@(_ , pb , ps) hb hs =
    conn b s δ st sn pl (U.step b) (U.step s) (λ w f → hb (w , f)) hs
         (λ k w f → lags s δ st sns ps k w (first-under k δ f))
         (λ j bj w f → leads b (U.live s ∷ δ) (hs , ps , lags₂ s δ st hs sns ps , st) sbn pb j bj (w , f))
         (placed-after s δ st sns ps)

  os : ∀ {Γ A} (c : U.Node Γ A) (δ : Env Γ) → Settled δ → Sane (flags δ) c → Placed c (ρᴱ δ) → Shows c δ
  os (U.framesᶜ τ e m)    δ st sn pl fi = frames-after τ e m
  os (U.burstᶜ τ r i b)   δ st sn pl fi = burst-after τ r i b
  os (U.endᶜ p)           δ st sn pl fi = ≃-refl (end p)
  os (U.ofᶜ p i xs)       δ st sn pl fi = of-after p i xs
  os (U.mapᶜ f c)         δ st sn (_ , pl) fi =
    ≃-trans (mapᴱ-≃ f (os c δ st sn pl (subst (λ k → First k δ) (map-head f (U.step c)) fi))) (map-after f (U.step c))
  os (U.scanᶜ f z c)      δ st sn (_ , pl) fi =
    ≃-trans (scanᴱ-≃ f z (os c δ st sn pl (subst (λ k → First k δ) (scan-head f z (U.step c)) fi))) (scan-after f z (U.step c))
  os (U.takeWhileᶜ i p c) δ st sn (_ , pl) fi =
    ≃-trans (takeWhileᴱ-≃ i p (os c δ st sn pl (take-first i p (U.step c) δ fi))) (take-after i p (U.step c))
  os (U.flatMapᶜ op g o ls qs) δ st sn pl@(_ , po , pls) =
    go-skips op g o ls qs δ st sn pl (osᴹ o δ st (proj₁ sn) po) (osᴸ ls δ st (proj₁ (proj₂ sn)) pls)
  os (U.joinᶜ i p xs e)   δ st sn pl fi = join-after i p xs e δ st sn fi
  os (U.connectᶜ b (U.live s)) δ st sn@(sb , ss) pl@(_ , pb , ps) =
    live-skips b s δ st sn pl (os b (U.live s ∷ δ) (hs , ps , lags₂ s δ st hs ss ps , st) sb pb) hs
    where hs = os s δ st ss ps
  os (U.connectᶜ b (U.ended c)) δ st sn (_ , pb) fi =
    ≃-trans (os b (U.ended c ∷ δ) st sn pb (subst (λ k → First k δ) (shut-head c (U.step b)) fi)) (shut-after c (U.step b))
  os (U.deferᶜ l p ns)    δ st sn pl fi = defer-after l p ns (ρᴱ δ)

  osᴹ : ∀ {Γ A} (o : Maybe (U.Node Γ A)) (δ : Env Γ) → Settled δ → Saneᴹ (flags δ) o → Placedᴹ o (ρᴱ δ) → Showsᴹ o δ
  osᴹ nothing  δ st sn pl = tt
  osᴹ (just c) δ st sn pl = os c δ st sn pl

  osᴸ : ∀ {Γ A} (ls : List (U.Node Γ A)) (δ : Env Γ) → Settled δ → Saneᴸ (flags δ) ls → Placedᴸ ls (ρᴱ δ) → Showsᴸ ls δ
  osᴸ []       δ st sn        pl        = tt
  osᴸ (c ∷ cs) δ st (sc , sl) (pc , pl) = os c δ st sc pc , osᴸ cs δ st sl pl
