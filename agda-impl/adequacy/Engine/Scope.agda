{-# OPTIONS --guardedness #-}

-- A node read where its frame sits: per connect in scope, whether its
-- source runs (`modes`), and every running one showing at or past a
-- position (`Scope`).  A node's meaning starts with its step's event, or
-- past a running source's shown event (`adequacy.Stepper.first`); so a
-- node whose step heads after `q` heads after `q` in the meaning
-- (`first-after`), and one whose step shows at or past `q` shows there
-- too (`first-floor`).  A connect's source is such a node, read in the
-- scope above it (`scope-src`).
module adequacy.Engine.Scope where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; [_]; _++_; _ʳ++_; reverse; map)
open import Data.List.Properties using (ʳ++-defn; reverse-involutive)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

open import denotation.MonotonicList using (Agree; out⁼; skip⁼; end⁼; hush⁼; agree-refl)
open import denotation.NonExpansive using (Agreeˢ)
open import denotation.MonotonicList.Events using (Pos; Timeline; Events; Events∞; out; skip; end; hush; ix; _<ᵖ_; <ᵖ-trans; <ᵖ-asym; <ᵖ-below)
import denotation.MonotonicList as M′
open import denotation.Unfold using (NEnv; Node; Source; live; ended; Step; outˢ; skipˢ; endˢ; hushˢ; states; step; headˢ; meaning; subscribe)
open import Tree using (Obs; FlatOp)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; St; CS; cs; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; plug)
open import adequacy.Sane using (Mode; runs; over; loose; Sane; Saneᴸ)
open import adequacy.Placed.Order using (Placed; Placedᴸ)
open import adequacy.Stepper.Past using (Floor; Floorᴱ; floorᴱ-agree; First; Firstᴸ; afterᴱ; above; _≃_; alike)
open import adequacy.Stepper.Parts using (shut-alikeⁱ)
open import adequacy.Env using (nagree-refl)
open import adequacy.Stepper.Flat using (agree-head)
open import adequacy.Engine.Meaning using (gh; lanesL; envAt; srcG; srcRun; endOf)
open import adequacy.Engine.Race using (After)
open import adequacy.Engine.Shuts using (Shuts; none; shutAt; upˢ; shutAll; Told)

modeᴳ : ∀ {Γ X} → Source Γ X → Mode
modeᴳ (live s)    = runs
modeᴳ (ended e t) = over

modes : ∀ {R Γ A} → Ctx R Γ A → All (λ _ → Mode) Γ
modes top                               = []ᴬ
modes (inMap f c)                       = modes c
modes (inScan f z c)                    = modes c
modes (inCut l a c)                     = modes c
modes (inLn b c)                        = modes c
modes (inTake i q w c)                  = modes c
modes (inOuter op f d n q ls c)         = modes c
modes (inLanes op f d n q o pre post c) = modes c
modes (inSrc k b c)                     = modes c
modes (inBody k o c)                    = modeᴳ (srcG k o) ∷ᴬ modes c

Scope : ∀ {R Γ A} → Pos → Ctx R Γ A → Set
Scope q c = Floor (modes c) q (envAt c)

-- At or past a later position, at or past an earlier one.
≮-lower : ∀ s k k′ → k <ᵖ k′ ≡ true → s <ᵖ k′ ≡ false → s <ᵖ k ≡ false
≮-lower s k k′ lt f with s <ᵖ k in e
... | false = refl
... | true  = trans (sym (<ᵖ-trans s k k′ e lt)) f

floorᴱ-lower : ∀ {A} k k′ (e : Events A) → k <ᵖ k′ ≡ true → Floorᴱ k′ e → Floorᴱ k e
floorᴱ-lower k k′ hush        lt f = f
floorᴱ-lower k k′ (out q a σ) lt f = ≮-lower (q ++ [ ix 0 ]) k k′ lt f
floorᴱ-lower k k′ (skip q σ)  lt f = ≮-lower (q ++ [ ix 0 ]) k k′ lt f
floorᴱ-lower k k′ (end c)     lt f = ≮-lower (c ++ [ ix 0 ]) k k′ lt f

floor-lower : ∀ {Γ} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) k k′ → k <ᵖ k′ ≡ true → Floor ν k′ ρ → Floor ν k ρ
floor-lower []ᴬ          []ᴬ      k k′ lt f        = f
floor-lower (runs ∷ᴬ ν)  (e ∷ᴬ ρ) k k′ lt (fe , f) = floorᴱ-lower k k′ e lt fe , floor-lower ν ρ k k′ lt f
floor-lower (over ∷ᴬ ν)  (e ∷ᴬ ρ) k k′ lt f        = floor-lower ν ρ k k′ lt f
floor-lower (loose ∷ᴬ ν) (e ∷ᴬ ρ) k k′ lt (fe , f) = floorᴱ-lower k k′ e lt fe , floor-lower ν ρ k k′ lt f

first-after : ∀ {Γ A} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) q (t : Step Γ A) (x : Events A)
            → Floor ν q ρ → First ν ρ t x → After q (headˢ t) → After q (M′.head x)
first-after ν ρ q t x           fl (inj₁ ag) a = subst (After q) (agree-head ρ t x ag) a
first-after ν ρ q t (out h _ _) fl (inj₂ pa) a = above ν ρ q h (headˢ t) fl pa
first-after ν ρ q t (skip h _)  fl (inj₂ pa) a = above ν ρ q h (headˢ t) fl pa
first-after ν ρ q t (end h)     fl (inj₂ pa) a = above ν ρ q h (headˢ t) fl pa
first-after ν ρ q t hush        fl (inj₂ ()) a

firsts-after : ∀ {Γ A} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) q (ms : List (Node Γ A))
             → Floor ν q ρ → Firstᴸ ν ms ρ → All (λ m → After q (headˢ (step m))) ms
             → All (λ l → After q (M′.head (Events∞.force l))) (states ms ρ)
firsts-after ν ρ q []       fl _        []ᴬ       = []ᴬ
firsts-after ν ρ q (m ∷ ms) fl (f , fs) (a ∷ᴬ as) = first-after ν ρ q (step m) (meaning m ρ) fl f a ∷ᴬ firsts-after ν ρ q ms fl fs as

-- Whatever is at `h` shows at or past `q`.
FloorAt : Pos → Maybe Pos → Set
FloorAt q nothing  = ⊤
FloorAt q (just h) = (h ++ [ ix 0 ]) <ᵖ q ≡ false

-- A node whose step shows at or past `q`, every running source in scope
-- at or past it, shows there in the meaning.
agree-floor : ∀ {Γ A} (ρ : NEnv Γ) q (t : Step Γ A) (x : Events A) → Agree 1 x (afterᴱ ρ t) → FloorAt q (headˢ t) → Floorᴱ q x
agree-floor ρ q (outˢ h a n) _ (out⁼ _ _)  fa = fa
agree-floor ρ q (skipˢ h n)  _ (skip⁼ _ _) fa = fa
agree-floor ρ q (endˢ h)     _ end⁼        fa = fa
agree-floor ρ q hushˢ        _ hush⁼       fa = tt

past-floor : ∀ q h → q <ᵖ h ≡ true → (h ++ [ ix 0 ]) <ᵖ q ≡ false
past-floor q h lt = <ᵖ-asym q (h ++ [ ix 0 ]) (<ᵖ-trans q h (h ++ [ ix 0 ]) lt (<ᵖ-below h []))

first-floor : ∀ {Γ A} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) q (t : Step Γ A) (x : Events A)
            → Floor ν q ρ → First ν ρ t x → FloorAt q (headˢ t) → Floorᴱ q x
first-floor ν ρ q t x           fl (inj₁ ag) fa = agree-floor ρ q t x ag fa
first-floor ν ρ q t (out h _ _) fl (inj₂ pa) fa = past-floor q h (above ν ρ q h (headˢ t) fl pa)
first-floor ν ρ q t (skip h _)  fl (inj₂ pa) fa = past-floor q h (above ν ρ q h (headˢ t) fl pa)
first-floor ν ρ q t (end h)     fl (inj₂ pa) fa = past-floor q h (above ν ρ q h (headˢ t) fl pa)
first-floor ν ρ q t hush        fl (inj₂ ()) fa

-- A connect's source at or past `q`, if it runs.
FloorSrc : ∀ {Γ X} → Pos → Source Γ X → NEnv Γ → Set
FloorSrc q (live s)    ρ = Floorᴱ q (meaning s ρ)
FloorSrc q (ended e t) ρ = ⊤

scope-src : ∀ {Γ X} (ν : All (λ _ → Mode) Γ) q (g : Source Γ X) (ρ : NEnv Γ) → FloorSrc q g ρ → Floor ν q ρ
          → Floor (modeᴳ g ∷ᴬ ν) q (srcRun g ρ ∷ᴬ ρ)
scope-src ν q (live s)    ρ fs f = fs , f
scope-src ν q (ended e t) ρ fs f = f

-- THE CONNECTS IN SCOPE THAT HAVE ENDED, each with where: `Unfold` shuts
-- an ended connect's body (`Unfold.shutˢᵗ`), telling every joiner of it,
-- one a later subscription made too.  A node read through them is the
-- one `Unfold` would hold there, alike in meaning (`shut-floor`).
closeOf : ∀ {Γ X} → Source Γ X → Shuts (X ∷ Γ) → Shuts (X ∷ Γ)
closeOf (live s)    ss = ss
closeOf (ended e t) ss = shutAt (here refl) e ss

closures : ∀ {R Γ A} → Ctx R Γ A → Shuts Γ
closures top                               = none
closures (inMap f c)                       = closures c
closures (inScan f z c)                    = closures c
closures (inCut l a c)                     = closures c
closures (inLn b c)                        = closures c
closures (inTake i q w c)                  = closures c
closures (inOuter op f d n q ls c)         = closures c
closures (inLanes op f d n q o pre post c) = closures c
closures (inSrc k b c)                     = closures c
closures (inBody k o c)                    = closeOf (srcG k o) (upˢ (closures c))

-- Each shut connect ended where it says.
Ended : ∀ {Γ} → Shuts Γ → NEnv Γ → Set
Ended none           ρ = ⊤
Ended (shutAt i c s) ρ = lookup ρ i ≃ end c × Ended s ρ

ended-up : ∀ {Γ X} (s : Shuts Γ) (e : Events X) (ρ : NEnv Γ) → Ended s ρ → Ended (upˢ s) (e ∷ᴬ ρ)
ended-up none           e ρ t        = tt
ended-up (shutAt i c s) e ρ (a , t) = a , ended-up s e ρ t

ended-close : ∀ {Γ X} (g : Source Γ X) (ρ : NEnv Γ) (s : Shuts (X ∷ Γ)) → Ended s (srcRun g ρ ∷ᴬ ρ) → Ended (closeOf g s) (srcRun g ρ ∷ᴬ ρ)
ended-close (live x)    ρ s t = t
ended-close (ended e x) ρ s t = alike (λ n → agree-refl n (end e)) , t

ended-at : ∀ {R Γ A} (c : Ctx R Γ A) → Ended (closures c) (envAt c)
ended-at top                               = tt
ended-at (inMap f c)                       = ended-at c
ended-at (inScan f z c)                    = ended-at c
ended-at (inCut l a c)                     = ended-at c
ended-at (inLn b c)                        = ended-at c
ended-at (inTake i q w c)                  = ended-at c
ended-at (inOuter op f d n q ls c)         = ended-at c
ended-at (inLanes op f d n q o pre post c) = ended-at c
ended-at (inSrc k b c)                     = ended-at c
ended-at (inBody k o c)                    =
  ended-close (srcG k o) (envAt c) (upˢ (closures c)) (ended-up (closures c) (srcRun (srcG k o) (envAt c)) (envAt c) (ended-at c))

shut-floor : ∀ {Γ B} q (s : Shuts Γ) (n : Node Γ B) (ρ : NEnv Γ) → Ended s ρ → Floorᴱ q (meaning (shutAll s n) ρ) → Floorᴱ q (meaning n ρ)
shut-floor q none           n ρ t       f = f
shut-floor q (shutAt i c s) n ρ (a , t) f =
  shut-floor q s n ρ t (floorᴱ-agree
    (Agreeˢ.nowˢ (shut-alikeⁱ i c (shutAll s n) {ρ} {ρ} a (λ m → nagree-refl m ρ) 1)) f)

after-agree : ∀ {A} q {e e′ : Events A} → Agree 1 e e′ → After q (M′.head e′) → After q (M′.head e)
after-agree q (out⁼ _ _)  a = a
after-agree q (skip⁼ _ _) a = a
after-agree q end⁼        a = a
after-agree q hush⁼       a = a

shut-after : ∀ {Γ B} q (s : Shuts Γ) (n : Node Γ B) (ρ : NEnv Γ) → Ended s ρ → After q (M′.head (meaning (shutAll s n) ρ)) → After q (M′.head (meaning n ρ))
shut-after q none           n ρ t       a = a
shut-after q (shutAt i c s) n ρ (e , t) a =
  shut-after q s n ρ t (after-agree q
    (Agreeˢ.nowˢ (shut-alikeⁱ i c (shutAll s n) {ρ} {ρ} e (λ m → nagree-refl m ρ) 1)) a)

shut-states : ∀ {Γ B} q (s : Shuts Γ) (ms : List (Node Γ B)) (ρ : NEnv Γ) → Ended s ρ
            → All (λ l → After q (M′.head (Events∞.force l))) (states (map (shutAll s) ms) ρ)
            → All (λ l → After q (M′.head (Events∞.force l))) (states ms ρ)
shut-states q s []       ρ t []ᴬ       = []ᴬ
shut-states q s (m ∷ ms) ρ t (a ∷ᴬ as) = shut-after q s m ρ t a ∷ᴬ shut-states q s ms ρ t as

-- WHAT THE INVARIANT KEEPS OF EACH SUBSCRIBED CONNECT'S SOURCE, at the
-- frame it sits in: its ghost read through the ended connects in scope
-- is a run's configuration there, placed in the environment the frame
-- reads, and so of each flatMap's lanes (`Lns`); of each live joiner,
-- that a shut connect told it its end (`Told`).  A lane at its place in
-- its list (`Ghᴸ`, the lanes before it reversed, as `inLanes` holds them).
--
-- DEAD ROUTE: the plain ghost: a source subscribing inside an ended
--   connect's body, its own body emitting before its source subscribes,
--   shows past the pick while ghosting that pending source untold.
Src : ∀ {R Γ X B} → Ctx R Γ B → CS → St Γ X → Set
Src c (cs false sl sa nothing as ow r en) o = Sane (modes c) (shutAll (closures c) (gh o)) × Placed (shutAll (closures c) (gh o)) (envAt c)
Src c k                                   o = ⊤

Lns : ∀ {R Γ B} → Ctx R Γ B → List (Node Γ B) → Set
Lns c ms = Saneᴸ (modes c) (map (shutAll (closures c)) ms) × Placedᴸ (map (shutAll (closures c)) ms) (envAt c)

mutual
  Gh : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Set
  Gh c (mapS f s)              = Gh (inMap f c) s
  Gh c (scanS f z s)           = Gh (inScan f z c) s
  Gh c (cutS l a s)            = Gh (inCut l a c) s
  Gh c (lnS b s)               = Gh (inLn b c) s
  Gh c (takeS i q w s)         = Gh (inTake i q w c) s
  Gh c (flatS op f d n q o ls) = Lns c (lanesL ls) × Gh (inOuter op f d n q ls c) o × Ghᴸ c op f d n q o [] ls
  Gh c (connS k o b)           = Src c k o × Gh (inSrc k b c) o × Gh (inBody k o c) b
  Gh c (joinS j true x ib)     = Told (closures c) x (endOf ib)
  Gh c _                       = ⊤

  Ghᴸ : ∀ {R Γ A B} → Ctx R Γ B → FlatOp → (A → Obs Timeline Γ B) → Bool → ℕ → List A → St Γ A → List (St Γ B) → List (St Γ B) → Set
  Ghᴸ c op f d n q o pre []         = ⊤
  Ghᴸ c op f d n q o pre (s ∷ post) = Gh (inLanes op f d n q o pre post c) s × Ghᴸ c op f d n q o (s ∷ pre) post

ghᴸ-at : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q o xs acc (s : St Γ B) post
       → Ghᴸ c op f d n q o acc (xs ++ s ∷ post) → Gh (inLanes op f d n q o (xs ʳ++ acc) post c) s
ghᴸ-at c op f d n q o []       acc s post (g , _)  = g
ghᴸ-at c op f d n q o (x ∷ xs) acc s post (_ , gs) = ghᴸ-at c op f d n q o xs (x ∷ acc) s post gs

-- Kept of the whole tree, kept at every frame.
gh-at : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Gh top (plug c s) → Gh c s
gh-at top                               s g = g
gh-at (inMap f c)                       s g = gh-at c (mapS f s) g
gh-at (inScan f z c)                    s g = gh-at c (scanS f z s) g
gh-at (inCut l a c)                     s g = gh-at c (cutS l a s) g
gh-at (inLn b c)                        s g = gh-at c (lnS b s) g
gh-at (inTake i q w c)                  s g = gh-at c (takeS i q w s) g
gh-at (inOuter op f d n q ls c)         s g = proj₁ (proj₂ (gh-at c (flatS op f d n q s ls) g))
gh-at (inLanes op f d n q o pre post c) s g =
  subst (λ xs → Gh (inLanes op f d n q o xs post c) s) (reverse-involutive pre)
    (ghᴸ-at c op f d n q o (reverse pre) [] s post
      (subst (Ghᴸ c op f d n q o []) (ʳ++-defn pre) (proj₂ (proj₂ (gh-at c (flatS op f d n q o (pre ʳ++ s ∷ post)) g)))))
gh-at (inSrc k b c)                     s g = proj₁ (proj₂ (gh-at c (connS k s b) g))
gh-at (inBody k o c)                    s g = proj₂ (proj₂ (gh-at c (connS k o s) g))

postulate
  -- A subscription at `r` shows at or past anything before `r`: each
  -- former's first event lies under `r`, and a joiner rejoins its
  -- source past `r`.
  sub-meaning : ∀ {Γ A} (o : Obs Timeline Γ A) r (ρ : NEnv Γ) q → q <ᵖ r ≡ true → Floorᴱ q (meaning (subscribe o r) ρ)
