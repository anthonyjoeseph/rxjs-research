{-# OPTIONS --guardedness #-}

-- THE REPLANT FRAME'S WALK: a node `u` replanted to `v` under a write at
-- `u`'s own names, walked from the node up to the root.  Every node
-- above reads its path child only through the child's part, its heads
-- and its leftover; every node beside the path reads alike.
module adequacy.Shift where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ; ++⁻)
open import Data.List.Relation.Unary.All using (All) renaming (lookup to lookupᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; _∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (lower)
open import Data.Maybe using (Maybe; just; nothing; is-just; is-nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Data.Sum using ([_,_]′)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥; ⊥-elim)

open import denotation.MonotonicList.Events using (Timeline; Pos)
import denotation.Unfold as U
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (maybe; quiet; module Heap; module Run) renaming (module Machine to Shared)
open import adequacy.Strong using (module Strongly)
open import adequacy.Strong.Against using (module StrongAgainst)
open import adequacy.Strong.Held using (module StrongHeld)
open import adequacy.Torn using (module Tearing)
open import adequacy.Moves using (module Moving)
open import adequacy.Local using (module Locality)
open import adequacy.Ghost.Paths using (module GhostingPaths)
open import adequacy.Frame using (module Framing)
open import adequacy.Frame.Repool using (module FramingRepool)
open import adequacy.Kept using (module Keeping)
open import adequacy.Retag using (Retag; module Retagging) renaming (keep to keepᴿ)


module Shifting (R : Set) where
  open Heap using (Sink; Quiet; slot; cell)
  open Run (Pureᴾ R) using (Ref; Subject; module Kit; module FlatKit)
  open FlatKit using (Flat)
  open Shared Timeline (Out R) using (Heapᴹ; look)
  open Strongly R using (Sub; Path; PathLanes; here; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; this-lane; next-lane; _⊕_; _⊕ᴸ_; pendingˢ; coldˢ; ofˢ; doneˢ; joinˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ; deferˢ; Lane; lane; Taking; taking; ending; taken; names; laneNames; cutNames; quietName; subjectNames; flatNames; module At; Name; outers; outersL; Feed)
  open StrongAgainst R using (isTaking; seen; seenL; seen-join; seen-up; Each; Leaves; Twin; tw-refl; tw-if; tw-union; tw-under; lv-tie; tw-tie; Restful; Lingers; Pinned; unpinned; rest-pinned; bursts-pinned; bursts-moved; under-moved; union-pinned; pinned-trans; pinned-sym; restful-pinned; ∧-split; ∧-join; false≢)
  open StrongHeld R using (DoneBy; Flagged; Heads)
  open Tearing R using (Alike; Off; part-alike; partLanes-alike; seen-alike; seenL-alike; names-path; lanes-path; apart-r; apart-l; narrow; each-same)
  open Moving R using (plant; plantᴸ; planted; plantedᴸ; pairs-r; pairs-split)
  open Locality R using (module Heaps)
  open GhostingPaths R using (each-sub; each-lanes)
  open Framing R using (Tells; untold; untoldᴹ; untoldᴸ; heads-map; heads-scan; heads-take; heads-source; shut-heads; just-of; untold-shut; merged-eq; heads-flat)
  open FramingRepool R using (Untold; Ended; ended-head)
  open Keeping R using (leftover-restful)
  open Retagging R using (retag; retagᴸ)

  ----------------------------------------------------------------------
  -- Lists, booleans, pins

  _⊆ᴾ_ : List Pos → List Pos → Set
  xs ⊆ᴾ ys = ∀ {x} → x ∈ᴸ xs → x ∈ᴸ ys

  ≡-⊆ : ∀ {xs ys} → xs ≡ ys → xs ⊆ᴾ ys
  ≡-⊆ refl m = m

  ++-mono : ∀ xs xs′ {ys ys′} → xs′ ⊆ᴾ xs → ys′ ⊆ᴾ ys → (xs′ ++ ys′) ⊆ᴾ (xs ++ ys)
  ++-mono xs xs′ {ys} sx sy m = [ (λ a → ++⁺ˡ {xs = xs} {ys = ys} (sx a)) , (λ b → ++⁺ʳ xs (sy b)) ]′ (++⁻ xs′ m)

  via-≡ : ∀ {a} {X : Set a} (f : X → Bool) {x x′ : X} → x′ ≡ x → f x′ ≡ true → f x ≡ true
  via-≡ f refl p = p

  filled : ∀ {a} {X : Set a} → List X → Bool
  filled []      = false
  filled (_ ∷ _) = true

  ∨-l : ∀ {x y} → x ≡ true → x ∨ y ≡ true
  ∨-l refl = refl

  ∨-r : ∀ x {y} → y ≡ true → x ∨ y ≡ true
  ∨-r true  _ = refl
  ∨-r false p = p

  ∨-mono : ∀ {a a′} b → (a′ ≡ true → a ≡ true) → a′ ∨ b ≡ true → a ∨ b ≡ true
  ∨-mono {a′ = true}  b f _ = ∨-l (f refl)
  ∨-mono {a′ = false} b f p = ∨-r _ p

  thru : ∀ {ℓ} {X : Set ℓ} x {y} → x ∧ y ≡ true → (x ≡ true → y ≡ true → X) → X
  thru x p k = k (proj₁ (∧-split x p)) (proj₂ (∧-split x p))

  thru₂ : ∀ {ℓ} {X : Set ℓ} x y {z} → x ∧ y ∧ z ≡ true → (x ∧ y ≡ true → z ≡ true → X) → X
  thru₂ x y p k = thru x p (λ a q → thru y q (λ b c → k (∧-join a b) c))

  seen-take : ∀ x {y} → x ∧ y ≡ true → x ∧ y ∧ true ≡ true
  seen-take x p = thru x p (λ a b → ∧-join a (∧-join b refl))

  just≢ : ∀ {a b} {X : Set a} {Y : Set b} {x : X} → just x ≡ nothing → Y
  just≢ ()

  pairs-tl : ∀ {a r} {X : Set a} {Rl : X → X → Set r} {x xs} → AllPairs Rl (x ∷ xs) → AllPairs Rl xs
  pairs-tl (_ ∷ p) = p

  if-moved : ∀ {Γ A} {b b′ : Bool} {x x′ y y′ : U.Node Γ A} → b′ ≡ b
           → Pinned (U.restˢ {B = ⊤} x) (U.restˢ {B = ⊤} x′) → Pinned (U.restˢ {B = ⊤} y) (U.restˢ {B = ⊤} y′)
           → Pinned (U.restˢ {B = ⊤} (if b then x else y)) (U.restˢ {B = ⊤} (if b′ then x′ else y′))
  if-moved {b = true}  refl p _ = p
  if-moved {b = false} refl _ q = q

  pin-alike : ∀ {Γ A} {x x′ : U.Node Γ A} → x′ ≡ x → Pinned (U.restˢ {B = ⊤} x) (U.restˢ {B = ⊤} x′)
  pin-alike {x = x} refl = rest-pinned x

  tw-alike : ∀ {Γ A} {x x′ : U.Node Γ A} → x′ ≡ x → Twin x x′
  tw-alike {x = x} refl = tw-refl x

  tw-if-moved : ∀ {Γ A} {b b′ : Bool} {x x′ y y′ : U.Node Γ A} → b′ ≡ b → Twin x x′ → Twin y y′ → Twin (if b then x else y) (if b′ then x′ else y′)
  tw-if-moved {b = b} refl = tw-if b

  -- A connect's leftover over a source run alike and a body pinned alike.
  conn-pin : ∀ {Γ A B} rp (N N′ : U.Node Γ A) {x x′ : U.Node (A ∷ Γ) ⊤} → N′ ≡ N → Pinned (U.restˢ {B = ⊤} x) (U.restˢ {B = ⊤} x′)
           → Pinned (U.restˢ {B = ⊤} (U.unionᶜ {B = B} (U.burstingᶜ rp N) (U.underᶜ (U.live N) x)))
                    (U.restˢ {B = ⊤} (U.unionᶜ {B = B} (U.burstingᶜ rp N′) (U.underᶜ (U.live N′) x′)))
  conn-pin rp N N′ refl lp = union-pinned (bursts-pinned rp N (U.step N)) (under-moved (U.live N) (U.live N) lp)

  conn-tw : ∀ {Γ A B} rp (N N′ : U.Node Γ A) {x x′ : U.Node (A ∷ Γ) ⊤} → N′ ≡ N → Twin x x′
          → Twin (U.unionᶜ {B = B} (U.burstingᶜ rp N) (U.underᶜ (U.live N) x)) (U.unionᶜ {B = B} (U.burstingᶜ rp N′) (U.underᶜ (U.live N′) x′))
  conn-tw rp N N′ refl t = tw-union (tw-refl (U.burstingᶜ rp N)) (tw-under (U.live N) t)

  conn-left : ∀ {Γ A B} rp {n n′ : U.Node Γ A} {x x′ : U.Node (A ∷ Γ) ⊤} → n′ ≡ n → x′ ≡ x
            → U.unionᶜ {B = B} (U.burstingᶜ rp n′) (U.underᶜ (U.live n′) x′) ≡ U.unionᶜ (U.burstingᶜ rp n) (U.underᶜ (U.live n) x)
  conn-left rp refl refl = refl

  ----------------------------------------------------------------------
  -- What a node's part reads, at either heap

  sourced-heap : ∀ {h} (G G′ : Heapᴹ h) {Δ A} (m : Maybe (U.Node Δ A)) (t : U.Node Δ A) → At.sourced G′ m t ≡ At.sourced G m t
  sourced-heap G G′ (just _) t = refl
  sourced-heap G G′ nothing  t = refl

  map-fwd : ∀ {h} (G : Heapᴹ h) {X Y : Set₁} (g : X → Y) (m : Maybe X) → is-just m ≡ true → is-just (At.mapᴹ G g m) ≡ true
  map-fwd G g (just _) _ = refl
  map-fwd G g nothing  ()

  map-back : ∀ {h} (G : Heapᴹ h) {X Y : Set₁} (g : X → Y) (m : Maybe X) → is-just (At.mapᴹ G g m) ≡ true → is-just m ≡ true
  map-back G g (just _) _ = refl
  map-back G g nothing  ()

  cons-untold : ∀ {h} (G : Heapᴹ h) {Γ A B} (i : A ∈ᴸ Γ) (m : Maybe (U.Node Γ B)) L → untoldᴸ i (At.consᴹ G m L) ≡ untoldᴹ i m ++ untoldᴸ i L
  cons-untold G i nothing  L = refl
  cons-untold G i (just _) L = refl

  untold-at : ∀ {h} {G : Heapᴹ h} {q Δ A} {t : Sub h Δ A} → Untold G q t
            → ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
            → (ψ : Path t (connectˢ S c b kb k fd rp e rt src bd)) → seen G ψ ≡ true → ∀ {c₀} → e ≡ just c₀ → At.part G src ≡ nothing
            → ∀ {b₀} → At.part G bd ≡ just b₀ → Tells q c₀ (untold (here refl) b₀)
  untold-at ut ψ sn refl pn pb = ut ψ sn pn pb

  ----------------------------------------------------------------------
  -- THE LEAVES


  ----------------------------------------------------------------------
  -- Every node below a run of lanes

  record EachL {h} (G : Heapᴹ h) (P : ∀ {Γ A} → U.Node Γ A → Set) {Δ B} (ls : List (Lane h Δ B)) : Set₁ where
    field
      partsL : ∀ {Δ′ A′} {u : Sub h Δ′ A′} (ψ : PathLanes ls u) → seenL G ψ ≡ true → ∀ {c} → At.part G u ≡ just c → P c
      poolsL : ∀ {Δ′ A′ B′} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls′ : List (Lane h Δ′ B′)}
             → (ψ : PathLanes ls (flatMapˢ op f fl oc k r pl so ls′)) → seenL G ψ ≡ true
             → ∀ {c} → At.part G (flatMapˢ op f fl oc k r pl so ls′) ≡ just c → P pl
      restsL : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
             → (ψ : PathLanes ls (connectˢ S c b kb k fd rp e rt src bd)) → seenL G ψ ≡ true
             → ∀ {n} → At.part G (connectˢ S c b kb k fd rp e rt src bd) ≡ just n
             → At.part G src ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt

  record LingersL {h} (G : Heapᴹ h) {Δ B} (ls : List (Lane h Δ B)) : Set₁ where
    field
      poolsL : ∀ {Δ′ A′ B′} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls′ : List (Lane h Δ′ B′)}
             → (ψ : PathLanes ls (flatMapˢ op f fl oc k r pl so ls′)) → seenL G ψ ≡ true
             → ∀ {c} → At.part G (flatMapˢ op f fl oc k r pl so ls′) ≡ just c → Leaves pl (At.pooled G fl so ls′) × Restful pl
      restsL : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
             → (ψ : PathLanes ls (connectˢ S c b kb k fd rp e rt src bd)) → seenL G ψ ≡ true
             → ∀ {n} → At.part G (connectˢ S c b kb k fd rp e rt src bd) ≡ just n
             → At.part G src ≡ nothing → ∀ {c₀} → e ≡ just c₀ → Twin rt (At.leftover G {B = ⊤} src) × Restful rt

  UntoldL : ∀ {h} (G : Heapᴹ h) (q : Pos) {Δ B} (ls : List (Lane h Δ B)) → Set₁
  UntoldL {h} G q ls = ∀ {Δ′ A′ B′} {S c b kb k fd rp c₀ rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
                     → (ψ : PathLanes ls (connectˢ S c b kb k fd rp (just c₀) rt src bd)) → seenL G ψ ≡ true → At.part G src ≡ nothing
                     → ∀ {b₀} → At.part G bd ≡ just b₀ → Tells q c₀ (untold (here refl) b₀)

  EndedL : ∀ {h} (G : Heapᴹ h) {Δ B} (ls : List (Lane h Δ B)) → Set₁
  EndedL {h} G ls = ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
                  → (ψ : PathLanes ls (connectˢ S c b kb k fd rp e rt src bd)) → seenL G ψ ≡ true
                  → ∀ {n} → At.part G (connectˢ S c b kb k fd rp e rt src bd) ≡ just n → ∀ {c₀} → e ≡ just c₀ → At.part G src ≡ nothing

  ----------------------------------------------------------------------
  -- Down a seen path: what holds of a node holds below it

  module _ {h} (G : Heapᴹ h) where
    ut-sub : ∀ {q Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Untold G q t → (ρ : Path t u) → seen G ρ ≡ true → Untold G q u
    ut-sub ut ρ sρ ψ sn = ut (ρ ⊕ ψ) (seen-join G ρ ψ sρ sn)

    en-sub : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Ended G t → (ρ : Path t u) → seen G ρ ≡ true → Ended G u
    en-sub en ρ sρ ψ sn = en (ρ ⊕ ψ) (seen-join G ρ ψ sρ sn)

    lingers-sub : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Lingers G t → (ρ : Path t u) → seen G ρ ≡ true → Lingers G u
    lingers-sub lg ρ sρ = record
      { pools = λ ψ sψ → Lingers.pools lg (ρ ⊕ ψ) (seen-join G ρ ψ sρ sψ)
      ; rests = λ ψ sψ → Lingers.rests lg (ρ ⊕ ψ) (seen-join G ρ ψ sρ sψ) }

    module _ {P : ∀ {Γ A} → U.Node Γ A → Set} where
      eachL-of : ∀ {Δ A B op f fl oc k r pl} {so : Sub h Δ A} {ls : List (Lane h Δ B)} → Each G P (flatMapˢ op f fl oc k r pl so ls) → EachL G P ls
      eachL-of ev = record
        { partsL = λ πL → Each.parts ev (in-lanes πL) ; poolsL = λ πL → Each.pools ev (in-lanes πL) ; restsL = λ πL → Each.rests ev (in-lanes πL) }

      eachL-head : ∀ {Δ B} {c : Kit.Cut h} {k} {s : Sub h Δ B} {ls} → EachL G P (lane c k s ∷ ls) → At.val G (Kit.live c) ≡ true → Each G P s
      eachL-head eL lv = record
        { parts = λ ψ sn → EachL.partsL eL (this-lane ψ) (∧-join lv sn)
        ; pools = λ ψ sn → EachL.poolsL eL (this-lane ψ) (∧-join lv sn)
        ; rests = λ ψ sn → EachL.restsL eL (this-lane ψ) (∧-join lv sn) }

      eachL-tail : ∀ {Δ B} {l : Lane h Δ B} {ls} → EachL G P (l ∷ ls) → EachL G P ls
      eachL-tail eL = record
        { partsL = λ πL → EachL.partsL eL (next-lane πL) ; poolsL = λ πL → EachL.poolsL eL (next-lane πL) ; restsL = λ πL → EachL.restsL eL (next-lane πL) }

    lingersL-of : ∀ {Δ A B op f fl oc k r pl} {so : Sub h Δ A} {ls : List (Lane h Δ B)} → Lingers G (flatMapˢ op f fl oc k r pl so ls) → LingersL G ls
    lingersL-of lg = record { poolsL = λ πL → Lingers.pools lg (in-lanes πL) ; restsL = λ πL → Lingers.rests lg (in-lanes πL) }

    lingersL-head : ∀ {Δ B} {c : Kit.Cut h} {k} {s : Sub h Δ B} {ls} → LingersL G (lane c k s ∷ ls) → At.val G (Kit.live c) ≡ true → Lingers G s
    lingersL-head lL lv = record
      { pools = λ ψ sn → LingersL.poolsL lL (this-lane ψ) (∧-join lv sn)
      ; rests = λ ψ sn → LingersL.restsL lL (this-lane ψ) (∧-join lv sn) }

    lingersL-tail : ∀ {Δ B} {l : Lane h Δ B} {ls} → LingersL G (l ∷ ls) → LingersL G ls
    lingersL-tail lL = record { poolsL = λ πL → LingersL.poolsL lL (next-lane πL) ; restsL = λ πL → LingersL.restsL lL (next-lane πL) }

    utL-of : ∀ {q Δ A B op f fl oc k r pl} {so : Sub h Δ A} {ls : List (Lane h Δ B)} → Untold G q (flatMapˢ op f fl oc k r pl so ls) → UntoldL G q ls
    utL-of ut πL = ut (in-lanes πL)

    utL-head : ∀ {q Δ B} {c : Kit.Cut h} {k} {s : Sub h Δ B} {ls} → UntoldL G q (lane c k s ∷ ls) → At.val G (Kit.live c) ≡ true → Untold G q s
    utL-head ut lv ψ sn = ut (this-lane ψ) (∧-join lv sn)

    utL-tail : ∀ {q Δ B} {l : Lane h Δ B} {ls} → UntoldL G q (l ∷ ls) → UntoldL G q ls
    utL-tail ut πL = ut (next-lane πL)

    enL-of : ∀ {Δ A B op f fl oc k r pl} {so : Sub h Δ A} {ls : List (Lane h Δ B)} → Ended G (flatMapˢ op f fl oc k r pl so ls) → EndedL G ls
    enL-of en πL = en (in-lanes πL)

    enL-head : ∀ {Δ B} {c : Kit.Cut h} {k} {s : Sub h Δ B} {ls} → EndedL G (lane c k s ∷ ls) → At.val G (Kit.live c) ≡ true → Ended G s
    enL-head en lv ψ sn = en (this-lane ψ) (∧-join lv sn)

    enL-tail : ∀ {Δ B} {l : Lane h Δ B} {ls} → EndedL G (l ∷ ls) → EndedL G ls
    enL-tail en πL = en (next-lane πL)

  ----------------------------------------------------------------------
  -- Two heaps alike at a node's names: its part, its leftover, its pool,
  -- and everything held below it, alike

  module _ {h} (H H′ : Heapᴹ h) where
    part-from : ∀ {ns Δ′ A′} {x : Sub h Δ′ A′} → (∀ {n} → n ∈ᴸ names x → n ∈ᴸ ns) → Alike H H′ ns → At.part H′ x ≡ At.part H x
    part-from {x = x} sub al = part-alike H H′ x (λ j m → al j (sub m))

    part-at : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {x : Sub h Δ′ A′} (ψ : Path t x) → Alike H H′ (names t) → At.part H′ x ≡ At.part H x
    part-at {x = x} ψ = part-from {x = x} (λ m → names-path ψ m)

    partL-at : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {x : Sub h Δ′ A′} (πL : PathLanes ls x) → Alike H H′ (laneNames ls) → At.part H′ x ≡ At.part H x
    partL-at {x = x} πL = part-from {x = x} (λ m → lanes-path πL m)

    mutual
      leftover-alike : ∀ {Δ A B} (s : Sub h Δ A) → Alike H H′ (names s) → At.leftover H′ {B = B} s ≡ At.leftover H {B = B} s
      leftover-alike (pendingˢ s q) al = refl
      leftover-alike (coldˢ s hd ph) al = refl
      leftover-alike (ofˢ p i xs) al = refl
      leftover-alike doneˢ al = refl
      leftover-alike (mapˢ f s) al = leftover-alike s al
      leftover-alike (scanˢ f r s) al = leftover-alike s (λ j m → al j (there m))
      leftover-alike (takeWhileˢ i p c k tk s) al = leftover-alike s (λ j m → al j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) m)))
      leftover-alike (flatMapˢ op f fl oc k r pl so ls) al = cong₂ U.unionᶜ (leftover-alike so a₁) (leftoverL-alike ls a₂)
        where
          a₁ : Alike H H′ (names so)
          a₁ j m = al j (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ m)))))
          a₂ : Alike H H′ (laneNames ls)
          a₂ j m = al j (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m)))))
      leftover-alike (connectˢ S c b kb k fd rp e rt src bd) al =
        conn-left rp (trans (sourced-heap H H′ (At.part H′ src) (At.leftover H′ src)) (cong₂ (At.sourced H) (part-alike H H′ src a₁) (leftover-alike src a₁)))
          (leftover-alike bd a₂)
        where
          a₁ : Alike H H′ (names src)
          a₁ j m = al j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m))))))
          a₂ : Alike H H′ (names bd)
          a₂ j m = al j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) m))))))
      leftover-alike (joinˢ j sk l x st) al = refl
      leftover-alike (deferˢ k s) al = leftover-alike s (λ j m → al j (++⁺ʳ (quietName k) m))

      leftoverL-alike : ∀ {Δ A B} (ls : List (Lane h Δ A)) → Alike H H′ (laneNames ls) → At.leftoverL H′ {B = B} ls ≡ At.leftoverL H {B = B} ls
      leftoverL-alike []                al = refl
      leftoverL-alike (lane c k s ∷ ls) al =
        cong₂ U.unionᶜ (leftover-alike s (λ j m → al j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ˡ m)))))
                       (leftoverL-alike ls (λ j m → al j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s) m)))))

    leftover-from : ∀ {ns Δ′ A′ B} {x : Sub h Δ′ A′} → (∀ {n} → n ∈ᴸ names x → n ∈ᴸ ns) → Alike H H′ ns → At.leftover H′ {B = B} x ≡ At.leftover H x
    leftover-from {x = x} sub al = leftover-alike x (λ j m → al j (sub m))

    pooledL-alike : ∀ {Δ A B} (ls : List (Lane h Δ A)) → Alike H H′ (laneNames ls) → At.pooledL H′ {B = B} ls ≡ At.pooledL H {B = B} ls
    pooledL-alike [] al = refl
    pooledL-alike {B = B} (lane c k s ∷ ls) al
      rewrite al (Kit.live c) (here refl)
            | leftover-alike {B = B} s (λ j m → al j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ˡ m))))
            | pooledL-alike {B = B} ls (λ j m → al j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s) m)))) = refl

    pooled-alike : ∀ {Δ A B} (fl : Flat A h) (so : Sub h Δ A) (ls : List (Lane h Δ B)) → look H′ (Flat.outerDone fl) ≡ look H (Flat.outerDone fl)
                 → Alike H H′ (names so) → Alike H H′ (laneNames ls) → At.pooled H′ fl so ls ≡ At.pooled H fl so ls
    pooled-alike {B = B} fl so ls d aso als rewrite d | leftover-alike {B = B} so aso | pooledL-alike {B = B} ls als = refl

    pooled-from : ∀ {ns Δ′ A′ B′ op f fl oc k r pl} {so : Sub h Δ′ A′} {ls : List (Lane h Δ′ B′)}
                → (∀ {n} → n ∈ᴸ names (flatMapˢ op f fl oc k r pl so ls) → n ∈ᴸ ns) → Alike H H′ ns → At.pooled H′ fl so ls ≡ At.pooled H fl so ls
    pooled-from {fl = fl} {oc} {k} {so = so} {ls} sub al =
      pooled-alike fl so ls (al (Flat.outerDone fl) (sub (there (here refl))))
        (λ j m → al j (sub (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ m)))))))
        (λ j m → al j (sub (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m)))))))

    each-alike : ∀ {P : ∀ {Γ A} → U.Node Γ A → Set} {Δ A} {t : Sub h Δ A} → Alike H H′ (names t) → Each H P t → Each H′ P t
    each-alike al ev = each-same H H′ (λ ψ → seen-alike H H′ ψ al) (λ ψ → part-at ψ al) ev

    eachL-alike : ∀ {P : ∀ {Γ A} → U.Node Γ A → Set} {Δ B} {ls : List (Lane h Δ B)} → Alike H H′ (laneNames ls) → EachL H P ls → EachL H′ P ls
    eachL-alike {ls = ls} al eL = record
      { partsL = λ πL sn e → EachL.partsL eL πL (se πL sn) (trans (sym (partL-at πL al)) e)
      ; poolsL = λ πL sn e → EachL.poolsL eL πL (se πL sn) (trans (sym (partL-at πL al)) e)
      ; restsL = λ πL sn e pn pe → EachL.restsL eL πL (se πL sn) (trans (sym (partL-at πL al)) e) (trans (sym (partL-at (πL ⊕ᴸ in-source here) al)) pn) pe }
      where
        se : ∀ {Δ′ A′} {x : Sub h Δ′ A′} (πL : PathLanes ls x) → seenL H′ πL ≡ true → seenL H πL ≡ true
        se πL sn = trans (sym (seenL-alike H H′ πL al)) sn

    lingers-alike : ∀ {Δ A} {t : Sub h Δ A} → Alike H H′ (names t) → Lingers H t → Lingers H′ t
    lingers-alike {t = t} al lg = record
      { pools = λ {op = op₀} {f = f₀} {fl = fl₀} {oc = oc₀} {k = k₀} {r = r₀} {pl = pl₀} {so = so₀} {ls = ls₀} ψ sn e → lv-tie (Lingers.pools lg ψ (se ψ sn) (trans (sym (part-at ψ al)) e)) (proj₁ (tw-alike (pooled-from {op = op₀} {f = f₀} {fl = fl₀} {oc = oc₀} {k = k₀} {r = r₀} {pl = pl₀} {so = so₀} {ls = ls₀} (λ m → names-path ψ m) al)))
      ; rests = λ {src = src₀} ψ sn e pn pe → tw-tie (Lingers.rests lg ψ (se ψ sn) (trans (sym (part-at ψ al)) e) (trans (sym (part-at (ψ ⊕ in-source here) al)) pn) pe)
                                              (tw-alike (leftover-from {B = ⊤} {x = src₀} (λ m → names-path (ψ ⊕ in-source here) m) al)) }
      where
        se : ∀ {Δ′ A′} {x : Sub h Δ′ A′} (ψ : Path t x) → seen H′ ψ ≡ true → seen H ψ ≡ true
        se ψ sn = trans (sym (seen-alike H H′ ψ al)) sn

    lingersL-alike : ∀ {Δ B} {ls : List (Lane h Δ B)} → Alike H H′ (laneNames ls) → LingersL H ls → LingersL H′ ls
    lingersL-alike {ls = ls} al lL = record
      { poolsL = λ {op = op₀} {f = f₀} {fl = fl₀} {oc = oc₀} {k = k₀} {r = r₀} {pl = pl₀} {so = so₀} {ls′ = ls₀} πL sn e → lv-tie (LingersL.poolsL lL πL (se πL sn) (trans (sym (partL-at πL al)) e)) (proj₁ (tw-alike (pooled-from {op = op₀} {f = f₀} {fl = fl₀} {oc = oc₀} {k = k₀} {r = r₀} {pl = pl₀} {so = so₀} {ls = ls₀} (λ m → lanes-path πL m) al)))
      ; restsL = λ {src = src₀} πL sn e pn pe → tw-tie (LingersL.restsL lL πL (se πL sn) (trans (sym (partL-at πL al)) e) (trans (sym (partL-at (πL ⊕ᴸ in-source here) al)) pn) pe)
                                               (tw-alike (leftover-from {B = ⊤} {x = src₀} (λ m → lanes-path (πL ⊕ᴸ in-source here) m) al)) }
      where
        se : ∀ {Δ′ A′} {x : Sub h Δ′ A′} (πL : PathLanes ls x) → seenL H′ πL ≡ true → seenL H πL ≡ true
        se πL sn = trans (sym (seenL-alike H H′ πL al)) sn

  ----------------------------------------------------------------------
  -- A node's relation from its own clause and its children's

  module Build {h} (G : Heapᴹ h) (P : ∀ {Γ A} → U.Node Γ A → Set) where
    Root : ∀ {Δ A} → Sub h Δ A → Set₁
    Root t = ∀ {c} → At.part G t ≡ just c → P c

    each-map : ∀ {Δ A B} {f : A → B} {s : Sub h Δ A} → Root (mapˢ f s) → Each G P s → Each G P (mapˢ f s)
    each-map root es = record
      { parts = λ { here _ x → root x ; (in-map ψ) sn x → Each.parts es ψ sn x }
      ; pools = λ { (in-map ψ) sn x → Each.pools es ψ sn x }
      ; rests = λ { (in-map ψ) sn x pn pe → Each.rests es ψ sn x pn pe } }

    each-scan : ∀ {Δ A B} {f : B → A → B} {r} {s : Sub h Δ A} → Root (scanˢ f r s) → Each G P s → Each G P (scanˢ f r s)
    each-scan root es = record
      { parts = λ { here _ x → root x ; (in-scan ψ) sn x → Each.parts es ψ sn x }
      ; pools = λ { (in-scan ψ) sn x → Each.pools es ψ sn x }
      ; rests = λ { (in-scan ψ) sn x pn pe → Each.rests es ψ sn x pn pe } }

    each-defer : ∀ {Δ A k} {s : Sub h Δ A} → Root (deferˢ k s) → Each G P s → Each G P (deferˢ k s)
    each-defer root es = record
      { parts = λ { here _ x → root x ; (in-defer ψ) sn x → Each.parts es ψ sn x }
      ; pools = λ { (in-defer ψ) sn x → Each.pools es ψ sn x }
      ; rests = λ { (in-defer ψ) sn x pn pe → Each.rests es ψ sn x pn pe } }

    each-take : ∀ {Δ A i p c k tk} {s : Sub h Δ A} → Root (takeWhileˢ i p c k tk s) → (At.val G (Kit.live c) ∧ isTaking tk ≡ true → Each G P s)
              → Each G P (takeWhileˢ i p c k tk s)
    each-take {c = c} {tk = tk} root es = record
      { parts = λ { here _ x → root x
                  ; (in-take ψ) sn x → thru₂ (At.val G (Kit.live c)) (isTaking tk) sn (λ ok sψ → Each.parts (es ok) ψ sψ x) }
      ; pools = λ { (in-take ψ) sn x → thru₂ (At.val G (Kit.live c)) (isTaking tk) sn (λ ok sψ → Each.pools (es ok) ψ sψ x) }
      ; rests = λ { (in-take ψ) sn x pn pe → thru₂ (At.val G (Kit.live c)) (isTaking tk) sn (λ ok sψ → Each.rests (es ok) ψ sψ x pn pe) } }

    each-flat : ∀ {Δ A B op f fl oc k r pl} {so : Sub h Δ A} {ls : List (Lane h Δ B)}
              → Root (flatMapˢ op f fl oc k r pl so ls) → (∀ {c} → At.part G (flatMapˢ op f fl oc k r pl so ls) ≡ just c → P pl)
              → Each G P so → EachL G P ls → Each G P (flatMapˢ op f fl oc k r pl so ls)
    each-flat root pool eo eL = record
      { parts = λ { here _ x → root x ; (in-outer ψ) sn x → Each.parts eo ψ sn x ; (in-lanes πL) sn x → EachL.partsL eL πL sn x }
      ; pools = λ { here _ x → pool x ; (in-outer ψ) sn x → Each.pools eo ψ sn x ; (in-lanes πL) sn x → EachL.poolsL eL πL sn x }
      ; rests = λ { (in-outer ψ) sn x pn pe → Each.rests eo ψ sn x pn pe ; (in-lanes πL) sn x pn pe → EachL.restsL eL πL sn x pn pe } }

    each-connect : ∀ {Δ A B S c b kb k fd rp e rt} {src : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
                 → Root (connectˢ S c b kb k fd rp e rt src bd)
                 → (∀ {n} → At.part G (connectˢ S c b kb k fd rp e rt src bd) ≡ just n → At.part G src ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt)
                 → (is-just (At.part G bd) ≡ true → Each G P src) → ((is-just (At.part G src) ∨ is-just e) ≡ true → Each G P bd)
                 → Each G P (connectˢ S c b kb k fd rp e rt src bd)
    each-connect {e = e} {src = src} {bd} root rest es eb = record
      { parts = λ { here _ x → root x
                  ; (in-source ψ) sn x → thru (is-just (At.part G bd)) sn (λ jb sψ → Each.parts (es jb) ψ sψ x)
                  ; (in-body ψ) sn x → thru (is-just (At.part G src) ∨ is-just e) sn (λ js sψ → Each.parts (eb js) ψ sψ x) }
      ; pools = λ { (in-source ψ) sn x → thru (is-just (At.part G bd)) sn (λ jb sψ → Each.pools (es jb) ψ sψ x)
                  ; (in-body ψ) sn x → thru (is-just (At.part G src) ∨ is-just e) sn (λ js sψ → Each.pools (eb js) ψ sψ x) }
      ; rests = λ { here _ x pn pe → rest x pn pe
                  ; (in-source ψ) sn x pn pe → thru (is-just (At.part G bd)) sn (λ jb sψ → Each.rests (es jb) ψ sψ x pn pe)
                  ; (in-body ψ) sn x pn pe → thru (is-just (At.part G src) ∨ is-just e) sn (λ js sψ → Each.rests (eb js) ψ sψ x pn pe) } }

    eachL-cons : ∀ {Δ B} {c : Kit.Cut h} {k} {s : Sub h Δ B} {ls} → (At.val G (Kit.live c) ≡ true → Each G P s) → EachL G P ls → EachL G P (lane c k s ∷ ls)
    eachL-cons {c = c} es eL = record
      { partsL = λ { (this-lane ψ) sn x → thru (At.val G (Kit.live c)) sn (λ lv sψ → Each.parts (es lv) ψ sψ x)
                   ; (next-lane πL) sn x → EachL.partsL eL πL sn x }
      ; poolsL = λ { (this-lane ψ) sn x → thru (At.val G (Kit.live c)) sn (λ lv sψ → Each.pools (es lv) ψ sψ x)
                   ; (next-lane πL) sn x → EachL.poolsL eL πL sn x }
      ; restsL = λ { (this-lane ψ) sn x pn pe → thru (At.val G (Kit.live c)) sn (λ lv sψ → Each.rests (es lv) ψ sψ x pn pe)
                   ; (next-lane πL) sn x pn pe → EachL.restsL eL πL sn x pn pe } }

  module Linger {h} (G : Heapᴹ h) where
    lg-map : ∀ {Δ A B} {f : A → B} {s : Sub h Δ A} → Lingers G s → Lingers G (mapˢ f s)
    lg-map ls = record
      { pools = λ { (in-map ψ) sn x → Lingers.pools ls ψ sn x }
      ; rests = λ { (in-map ψ) sn x pn pe → Lingers.rests ls ψ sn x pn pe } }

    lg-scan : ∀ {Δ A B} {f : B → A → B} {r} {s : Sub h Δ A} → Lingers G s → Lingers G (scanˢ f r s)
    lg-scan ls = record
      { pools = λ { (in-scan ψ) sn x → Lingers.pools ls ψ sn x }
      ; rests = λ { (in-scan ψ) sn x pn pe → Lingers.rests ls ψ sn x pn pe } }

    lg-defer : ∀ {Δ A k} {s : Sub h Δ A} → Lingers G s → Lingers G (deferˢ k s)
    lg-defer ls = record
      { pools = λ { (in-defer ψ) sn x → Lingers.pools ls ψ sn x }
      ; rests = λ { (in-defer ψ) sn x pn pe → Lingers.rests ls ψ sn x pn pe } }

    lg-take : ∀ {Δ A i p c k tk} {s : Sub h Δ A} → (At.val G (Kit.live c) ∧ isTaking tk ≡ true → Lingers G s) → Lingers G (takeWhileˢ i p c k tk s)
    lg-take {c = c} {tk = tk} ls = record
      { pools = λ { (in-take ψ) sn x → thru₂ (At.val G (Kit.live c)) (isTaking tk) sn (λ ok sψ → Lingers.pools (ls ok) ψ sψ x) }
      ; rests = λ { (in-take ψ) sn x pn pe → thru₂ (At.val G (Kit.live c)) (isTaking tk) sn (λ ok sψ → Lingers.rests (ls ok) ψ sψ x pn pe) } }

    lg-flat : ∀ {Δ A B op f fl oc k r pl} {so : Sub h Δ A} {ls : List (Lane h Δ B)}
            → (∀ {c} → At.part G (flatMapˢ op f fl oc k r pl so ls) ≡ just c → Leaves pl (At.pooled G fl so ls) × Restful pl)
            → Lingers G so → LingersL G ls → Lingers G (flatMapˢ op f fl oc k r pl so ls)
    lg-flat pool lo lL = record
      { pools = λ { here _ x → pool x ; (in-outer ψ) sn x → Lingers.pools lo ψ sn x ; (in-lanes πL) sn x → LingersL.poolsL lL πL sn x }
      ; rests = λ { (in-outer ψ) sn x pn pe → Lingers.rests lo ψ sn x pn pe ; (in-lanes πL) sn x pn pe → LingersL.restsL lL πL sn x pn pe } }

    lg-connect : ∀ {Δ A B S c b kb k fd rp e rt} {src : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
               → (∀ {n} → At.part G (connectˢ S c b kb k fd rp e rt src bd) ≡ just n → At.part G src ≡ nothing → ∀ {c₀} → e ≡ just c₀
                  → Twin rt (At.leftover G {B = ⊤} src) × Restful rt)
               → (is-just (At.part G bd) ≡ true → Lingers G src) → ((is-just (At.part G src) ∨ is-just e) ≡ true → Lingers G bd)
               → Lingers G (connectˢ S c b kb k fd rp e rt src bd)
    lg-connect {e = e} {src = src} {bd} rest ls lb = record
      { pools = λ { (in-source ψ) sn x → thru (is-just (At.part G bd)) sn (λ jb sψ → Lingers.pools (ls jb) ψ sψ x)
                  ; (in-body ψ) sn x → thru (is-just (At.part G src) ∨ is-just e) sn (λ js sψ → Lingers.pools (lb js) ψ sψ x) }
      ; rests = λ { here _ x pn pe → rest x pn pe
                  ; (in-source ψ) sn x pn pe → thru (is-just (At.part G bd)) sn (λ jb sψ → Lingers.rests (ls jb) ψ sψ x pn pe)
                  ; (in-body ψ) sn x pn pe → thru (is-just (At.part G src) ∨ is-just e) sn (λ js sψ → Lingers.rests (lb js) ψ sψ x pn pe) } }

    lgL-cons : ∀ {Δ B} {c : Kit.Cut h} {k} {s : Sub h Δ B} {ls} → (At.val G (Kit.live c) ≡ true → Lingers G s) → LingersL G ls → LingersL G (lane c k s ∷ ls)
    lgL-cons {c = c} l lL = record
      { poolsL = λ { (this-lane ψ) sn x → thru (At.val G (Kit.live c)) sn (λ lv sψ → Lingers.pools (l lv) ψ sψ x)
                   ; (next-lane πL) sn x → LingersL.poolsL lL πL sn x }
      ; restsL = λ { (this-lane ψ) sn x pn pe → thru (At.val G (Kit.live c)) sn (λ lv sψ → Lingers.rests (l lv) ψ sψ x pn pe)
                   ; (next-lane πL) sn x pn pe → LingersL.restsL lL πL sn x pn pe } }

  ----------------------------------------------------------------------
  -- Done flags: below a node, beside it, and across heaps alike

  DoneByL : ∀ {h} (G : Heapᴹ h) {Δ B} (ls : List (Lane h Δ B)) → List (Name h) → Set₁
  DoneByL {h} G ls ns = ∀ {Δ′ A′ B′} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls′ : List (Lane h Δ′ B′)}
                      → (ψ : PathLanes ls (flatMapˢ op f fl oc k r pl so ls′)) → seenL G ψ ≡ true → Flagged G ns fl so

  -- A flatMap's done flag is among the names above it.
  flag-in : ∀ {h Δ A Δ′ A′ B′} {t : Sub h Δ A} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls : List (Lane h Δ′ B′)}
          → Path t (flatMapˢ op f fl oc k r pl so ls) → (cell _ , Flat.outerDone fl) ∈ᴸ names t
  flag-in {fl = fl} ψ = names-path ψ (++⁺ˡ {xs = flatNames fl} (there (here refl)))

  flag-inL : ∀ {h Δ B Δ′ A′ B′} {ls : List (Lane h Δ B)} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls′ : List (Lane h Δ′ B′)}
           → PathLanes ls (flatMapˢ op f fl oc k r pl so ls′) → (cell _ , Flat.outerDone fl) ∈ᴸ laneNames ls
  flag-inL {fl = fl} πL = lanes-path πL (++⁺ˡ {xs = flatNames fl} (there (here refl)))

  -- Replanting keeps the outers a path enters.
  mutual
    outers-planted : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′) → outers (planted π v) ≡ outers π
    outers-planted here         v = refl
    outers-planted (in-map π)    v = outers-planted π v
    outers-planted (in-scan π)   v = outers-planted π v
    outers-planted (in-take π)   v = outers-planted π v
    outers-planted (in-outer π)  v = cong (_ ∷_) (outers-planted π v)
    outers-planted (in-lanes π)  v = outersL-planted π v
    outers-planted (in-source π) v = outers-planted π v
    outers-planted (in-body π)   v = outers-planted π v
    outers-planted (in-defer π)  v = outers-planted π v

    outersL-planted : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′) → outersL (plantedᴸ π v) ≡ outersL π
    outersL-planted (this-lane π) v = outers-planted π v
    outersL-planted (next-lane π) v = outersL-planted π v

  module Flag {h} (G : Heapᴹ h) {ns : List (Name h)} where
    db-map : ∀ {Δ A B} {f : A → B} {s : Sub h Δ A} → DoneBy G s ns → DoneBy G (mapˢ f s) ns
    db-map d (in-map ψ) sn = d ψ sn

    db-scan : ∀ {Δ A B} {f : B → A → B} {r} {s : Sub h Δ A} → DoneBy G s ns → DoneBy G (scanˢ f r s) ns
    db-scan d (in-scan ψ) sn = d ψ sn

    db-defer : ∀ {Δ A k} {s : Sub h Δ A} → DoneBy G s ns → DoneBy G (deferˢ k s) ns
    db-defer d (in-defer ψ) sn = d ψ sn

    db-take : ∀ {Δ A i p c k tk} {s : Sub h Δ A} → (At.val G (Kit.live c) ∧ isTaking tk ≡ true → DoneBy G s ns) → DoneBy G (takeWhileˢ i p c k tk s) ns
    db-take {c = c} {tk = tk} d (in-take ψ) sn = thru₂ (At.val G (Kit.live c)) (isTaking tk) sn (λ ok sψ → d ok ψ sψ)

    db-flat : ∀ {Δ A B op f fl oc k r pl} {so : Sub h Δ A} {ls : List (Lane h Δ B)}
            → Flagged G ns fl so → DoneBy G so ns → DoneByL G ls ns → DoneBy G (flatMapˢ op f fl oc k r pl so ls) ns
    db-flat fg d dL here          _  = fg
    db-flat fg d dL (in-outer ψ)  sn = d ψ sn
    db-flat fg d dL (in-lanes πL) sn = dL πL sn

    db-connect : ∀ {Δ A B S c b kb k fd rp e rt} {src : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
               → (is-just (At.part G bd) ≡ true → DoneBy G src ns) → ((is-just (At.part G src) ∨ is-just e) ≡ true → DoneBy G bd ns)
               → DoneBy G (connectˢ S c b kb k fd rp e rt src bd) ns
    db-connect {src = src} {bd} ds db (in-source ψ) sn = thru (is-just (At.part G bd)) sn (λ jb sψ → ds jb ψ sψ)
    db-connect {e = e} {src = src} ds db (in-body ψ) sn = thru (is-just (At.part G src) ∨ is-just e) sn (λ js sψ → db js ψ sψ)

    dbL-cons : ∀ {Δ B} {c : Kit.Cut h} {k} {s : Sub h Δ B} {ls} → (At.val G (Kit.live c) ≡ true → DoneBy G s ns) → DoneByL G ls ns → DoneByL G (lane c k s ∷ ls) ns
    dbL-cons {c = c} d dL (this-lane ψ) sn = thru (At.val G (Kit.live c)) sn (λ lv sψ → d lv ψ sψ)
    dbL-cons d dL (next-lane πL) sn = dL πL sn

    db-sub : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {x : Sub h Δ′ A′} → DoneBy G t ns → (ρ : Path t x) → seen G ρ ≡ true → DoneBy G x ns
    db-sub d ρ sρ ψ sψ = d (ρ ⊕ ψ) (seen-join G ρ ψ sρ sψ)

    dbL-of : ∀ {Δ A B op f fl oc k r pl} {so : Sub h Δ A} {ls : List (Lane h Δ B)} → DoneBy G (flatMapˢ op f fl oc k r pl so ls) ns → DoneByL G ls ns
    dbL-of d πL = d (in-lanes πL)

    dbL-head : ∀ {Δ B} {c : Kit.Cut h} {k} {s : Sub h Δ B} {ls} → DoneByL G (lane c k s ∷ ls) ns → At.val G (Kit.live c) ≡ true → DoneBy G s ns
    dbL-head dL lv ψ sn = dL (this-lane ψ) (∧-join lv sn)

    dbL-tail : ∀ {Δ B} {l : Lane h Δ B} {ls} → DoneByL G (l ∷ ls) ns → DoneByL G ls ns
    dbL-tail dL πL = dL (next-lane πL)

    -- The names listed changed only where no flag below reads them.
    relist : ∀ {ns′ Δ A} {t : Sub h Δ A} → (∀ {n} → n ∈ᴸ names t → n ∈ᴸ ns′ → n ∈ᴸ ns) → (∀ {n} → n ∈ᴸ names t → n ∈ᴸ ns → n ∈ᴸ ns′)
           → DoneBy G t ns → DoneBy G t ns′
    relist to fro d ψ sn = (λ m → proj₁ (d ψ sn) (to (flag-in ψ) m)) , (λ m̸ → proj₂ (d ψ sn) (λ m → m̸ (fro (flag-in ψ) m)))

    relistL : ∀ {ns′ Δ B} {ls : List (Lane h Δ B)} → (∀ {n} → n ∈ᴸ laneNames ls → n ∈ᴸ ns′ → n ∈ᴸ ns) → (∀ {n} → n ∈ᴸ laneNames ls → n ∈ᴸ ns → n ∈ᴸ ns′)
            → DoneByL G ls ns → DoneByL G ls ns′
    relistL to fro dL πL sn = (λ m → proj₁ (dL πL sn) (to (flag-inL πL) m)) , (λ m̸ → proj₂ (dL πL sn) (λ m → m̸ (fro (flag-inL πL) m)))

  module _ {h} (H H′ : Heapᴹ h) where
    flagged-moved : ∀ {ns Δ A} {fl : Flat A h} {so : Sub h Δ A} → At.val H′ (Flat.outerDone fl) ≡ At.val H (Flat.outerDone fl) → At.part H′ so ≡ At.part H so
                  → Flagged H ns fl so → Flagged H′ ns fl so
    flagged-moved vd pd (f₁ , f₂) = (λ m → trans vd (f₁ m)) , (λ m̸ → trans vd (trans (f₂ m̸) (cong is-nothing (sym pd))))

    flags-alike : ∀ {ns Δ A} {t : Sub h Δ A} → Alike H H′ (names t) → DoneBy H t ns → DoneBy H′ t ns
    flags-alike al d {fl = fl} {so = so} ψ sn =
      flagged-moved {fl = fl} {so = so} (cong lower (al (Flat.outerDone fl) (flag-in ψ))) (part-at H H′ (ψ ⊕ in-outer {t = so} here) al) (d ψ (trans (sym (seen-alike H H′ ψ al)) sn))

    flagsL-alike : ∀ {ns Δ B} {ls : List (Lane h Δ B)} → Alike H H′ (laneNames ls) → DoneByL H ls ns → DoneByL H′ ls ns
    flagsL-alike al dL {fl = fl} {so = so} πL sn =
      flagged-moved {fl = fl} {so = so} (cong lower (al (Flat.outerDone fl) (flag-inL πL))) (partL-at H H′ (πL ⊕ᴸ in-outer {t = so} here) al) (dL πL (trans (sym (seenL-alike H H′ πL al)) sn))

  -- A RETAG KEEPS EVERY FLAG: it rewrites only what joiners hold, and
  -- a flag reads parts only for whether they are open, so a retag whose
  -- joiners stay open exactly where they were moves no flag.
  module _ {h} (G : Heapᴹ h) where
    open At G using (part; partLanes; Fed; FedLanes; Now; told; mapᴹ; consᴹ; merged; connected)

    -- Each connect's feed, read down the path.
    mutual
      nowAt : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → Now Δ → Now Δ′
      nowAt here          ν = ν
      nowAt (in-map p)    ν = nowAt p ν
      nowAt (in-scan p)   ν = nowAt p ν
      nowAt (in-take p)   ν = nowAt p ν
      nowAt (in-outer p)  ν = nowAt p ν
      nowAt (in-lanes p)  ν = nowAtL p ν
      nowAt (in-source p) ν = nowAt p ν
      nowAt (in-body {S = S} {fd = fd} {e = e} p) ν = nowAt p ((fd , told S e) ∷ᴬ ν)
      nowAt (in-defer p)  ν = nowAt p ν

      nowAtL : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → PathLanes ls u → Now Δ → Now Δ′
      nowAtL (this-lane p) ν = nowAt p ν
      nowAtL (next-lane p) ν = nowAtL p ν

    mutual
      fed-at : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) {ν} → Fed t ν → Fed u (nowAt π ν)
      fed-at here          f        = f
      fed-at (in-map p)    f        = fed-at p f
      fed-at (in-scan p)   f        = fed-at p f
      fed-at (in-take p)   f        = fed-at p f
      fed-at (in-outer p)  (f , _)  = fed-at p f
      fed-at (in-lanes p)  (_ , fl) = fed-atL p fl
      fed-at (in-source p) (f , _)  = fed-at p f
      fed-at (in-body p)   (_ , fb) = fed-at p fb
      fed-at (in-defer p)  f        = fed-at p f

      fed-atL : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) {ν} → FedLanes ls ν → Fed u (nowAtL π ν)
      fed-atL (this-lane p) (f , _)  = fed-at p f
      fed-atL (next-lane p) (_ , fl) = fed-atL p fl

    -- Every joiner fed as `ν` says stays open exactly where it was.
    Steady : ∀ {Δ} → Retag Δ → Now Δ → Set₁
    Steady {Δ} g ν = ∀ {B} (x : B ∈ᴸ Δ) {j sk l st} → Fed (joinˢ j sk l x st) ν
                  → At.val G l ≡ true → is-just (g x j st) ≡ is-just st

    keeps-keep : ∀ {Δ A} {g : Retag Δ} {ν} {fe : Feed A h × Maybe Pos} → Steady g ν → Steady (keepᴿ g) (fe ∷ᴬ ν)
    keeps-keep hy (here refl) f lv = refl
    keeps-keep hy (there x)   f lv = hy x f lv

    just-map : ∀ {X Y : Set₁} (F : X → Y) {m m′ : Maybe X} → is-just m ≡ is-just m′ → is-just (mapᴹ F m) ≡ is-just (mapᴹ F m′)
    just-map F {just _}  {just _}  _ = refl
    just-map F {nothing} {nothing} _ = refl
    just-map F {just _}  {nothing} ()
    just-map F {nothing} {just _}  ()

    just-nothing : ∀ {X : Set₁} {m m′ : Maybe X} → is-just m ≡ is-just m′ → is-nothing m ≡ is-nothing m′
    just-nothing {m = just _}  {just _}  _ = refl
    just-nothing {m = nothing} {nothing} _ = refl
    just-nothing {m = just _}  {nothing} ()
    just-nothing {m = nothing} {just _}  ()

    just-cons : ∀ {X : Set₁} {m m′ : Maybe X} {xs ys : List X} → is-just m ≡ is-just m′ → filled xs ≡ filled ys → filled (consᴹ m xs) ≡ filled (consᴹ m′ ys)
    just-cons {m = just _}  {just _}  _ _ = refl
    just-cons {m = nothing} {nothing} _ p = p
    just-cons {m = just _}  {nothing} ()
    just-cons {m = nothing} {just _}  ()

    just-merged : ∀ {Δ A B} op (F : A → Pos → U.Node Δ B) (o : Maybe (U.Node Δ A)) ls qs pl
                → is-just (merged op F o ls qs pl) ≡ (is-just o ∨ filled ls ∨ filled qs)
    just-merged op F nothing  []      []      pl = refl
    just-merged op F nothing  []      (_ ∷ _) pl = refl
    just-merged op F nothing  (_ ∷ _) qs      pl = refl
    just-merged op F (just _) ls      qs      pl = refl

    just-connected : ∀ {Δ A B} r e (t : U.Node Δ A) {s s′ : Maybe (U.Node Δ A)} {b b′ : Maybe (U.Node (A ∷ Δ) B)}
                   → is-just s ≡ is-just s′ → is-just b ≡ is-just b′ → is-just (connected r e t s b) ≡ is-just (connected r e t s′ b′)
    just-connected r e t {b = nothing} {nothing} _ _ = refl
    just-connected r e t {just _} {just _} {just _} {just _} _ _ = refl
    just-connected r (just _) t {nothing} {nothing} {just _} {just _} _ _ = refl
    just-connected r nothing  t {nothing} {nothing} {just _} {just _} _ _ = refl
    just-connected r e t {just _} {nothing} {just _} {just _} () _
    just-connected r e t {nothing} {just _} {just _} {just _} () _
    just-connected r e t {b = just _} {nothing} _ ()
    just-connected r e t {b = nothing} {just _} _ ()

    mutual
      part-retag : ∀ {Δ A} (g : Retag Δ) (s : Sub h Δ A) {ν} → Steady g ν → Fed s ν → is-just (part (retag g s)) ≡ is-just (part s)
      part-retag g (pendingˢ s q)                          hy f = refl
      part-retag g (coldˢ s hd ph)                         hy f = refl
      part-retag g (ofˢ p i xs)                            hy f = refl
      part-retag g doneˢ                                   hy f = refl
      part-retag g (mapˢ f₀ s)                             hy f = just-map _ (part-retag g s hy f)
      part-retag g (scanˢ f₀ r s)                          hy f = just-map _ (part-retag g s hy f)
      part-retag g (takeWhileˢ i p c k tk s)               hy f with At.val G (Kit.live c)
      ... | false = refl
      ... | true  = taking-retag tk (part-retag g s hy f)
        where
          taking-retag : ∀ tk′ {m m′} → is-just m ≡ is-just m′ → is-just (At.taking? G i p tk′ m) ≡ is-just (At.taking? G i p tk′ m′)
          taking-retag taking       e = just-map _ e
          taking-retag (ending _ _) e = refl
          taking-retag taken        e = refl
      part-retag g (flatMapˢ op f₀ fl oc k r pl so ls)     hy (fs , fl′) =
        trans (just-merged op _ _ _ _ pl)
              (trans (cong₂ (λ x y → x ∨ y ∨ filled (At.val G (Flat.queue fl))) (part-retag g so hy fs) (lanes-retag g ls hy fl′))
                     (sym (just-merged op _ _ _ _ pl)))
      part-retag g (connectˢ S c b kb k fd rp e rt src bd) hy (fs , fb) =
        just-connected rp e rt (part-retag g src hy fs) (part-retag (keepᴿ g) bd (keeps-keep hy) fb)
      part-retag g (joinˢ j sk l x st)                     hy f = pj (At.val G l) refl
        where
          just-joined : ∀ m m′ → is-just m ≡ is-just m′ → is-just (At.joinedᶜ G x j m) ≡ is-just (At.joinedᶜ G x j m′)
          just-joined (just _) (just _) _ = refl
          just-joined nothing  nothing  _ = refl
          pj : ∀ b → At.val G l ≡ b → is-just (if b then At.joinedᶜ G x j (g x j st) else nothing) ≡ is-just (if b then At.joinedᶜ G x j st else nothing)
          pj false _  = refl
          pj true  lv = just-joined (g x j st) st (hy x f lv)
      part-retag g (deferˢ k s)                            hy f = part-retag g s hy f

      lanes-retag : ∀ {Δ B} (g : Retag Δ) (ls : List (Lane h Δ B)) {ν} → Steady g ν → FedLanes ls ν → filled (partLanes (retagᴸ g ls)) ≡ filled (partLanes ls)
      lanes-retag g []                hy _          = refl
      lanes-retag g (lane c k s ∷ ls) hy (fs , fl′) with At.val G (Kit.live c)
      ... | true  = just-cons (part-retag g s hy fs) (lanes-retag g ls hy fl′)
      ... | false = lanes-retag g ls hy fl′

    mutual
      flags-retag : ∀ {ns Δ A} (g : Retag Δ) (s : Sub h Δ A) {ν} → Steady g ν → Fed s ν → DoneBy G s ns → DoneBy G (retag g s) ns
      flags-retag g (pendingˢ s q)                          hy f d = d
      flags-retag g (coldˢ s hd ph)                         hy f d = d
      flags-retag g (ofˢ p i xs)                            hy f d = d
      flags-retag g doneˢ                                   hy f d = d
      flags-retag g (mapˢ f₀ s)                             hy f d = Flag.db-map G (flags-retag g s hy f (λ ψ sn → d (in-map ψ) sn))
      flags-retag g (scanˢ f₀ r s)                          hy f d = Flag.db-scan G (flags-retag g s hy f (λ ψ sn → d (in-scan ψ) sn))
      flags-retag g (takeWhileˢ i p c k tk s)               hy f d =
        Flag.db-take G (λ ok → flags-retag g s hy f (λ ψ sn → d (in-take ψ) (thru (At.val G (Kit.live c)) ok (λ a b′ → ∧-join a (∧-join b′ sn)))))
      flags-retag g (flatMapˢ op f₀ fl oc k r pl so ls)     hy (fs , fl′) d =
        Flag.db-flat G (proj₁ (d here refl) , λ m̸ → trans (proj₂ (d here refl) m̸) (just-nothing (sym (part-retag g so hy fs))))
          (flags-retag g so hy fs (λ ψ sn → d (in-outer ψ) sn)) (flagsL-retag g ls hy fl′ (λ πL sn → d (in-lanes πL) sn))
      flags-retag g (connectˢ S c b kb k fd rp e rt src bd) hy (fs , fb) d =
        Flag.db-connect G (λ jb → flags-retag g src hy fs (λ ψ sn → d (in-source ψ) (∧-join (trans (sym (part-retag (keepᴿ g) bd (keeps-keep hy) fb)) jb) sn)))
          (λ js → flags-retag (keepᴿ g) bd (keeps-keep hy) fb (λ ψ sn → d (in-body ψ) (∧-join (trans (cong (λ z → z ∨ is-just e) (sym (part-retag g src hy fs))) js) sn)))
      flags-retag g (joinˢ j sk l x st)                     hy f d ()
      flags-retag g (deferˢ k s)                            hy f d = Flag.db-defer G (flags-retag g s hy f (λ ψ sn → d (in-defer ψ) sn))

      flagsL-retag : ∀ {ns Δ B} (g : Retag Δ) (ls : List (Lane h Δ B)) {ν} → Steady g ν → FedLanes ls ν → DoneByL G ls ns → DoneByL G (retagᴸ g ls) ns
      flagsL-retag g []                hy _          dL ()
      flagsL-retag g (lane c k s ∷ ls) hy (fs , fl′) dL =
        Flag.dbL-cons G (λ lv → flags-retag g s hy fs (λ ψ sn → dL (this-lane ψ) (∧-join lv sn))) (flagsL-retag g ls hy fl′ (λ πL sn → dL (next-lane πL) sn))

  -- Every flag named on the way down lies in the tree.
  mutual
    outers-in : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) → ∀ {n} → n ∈ᴸ outers π → n ∈ᴸ names t
    outers-in here ()
    outers-in (in-map π) m = outers-in π m
    outers-in (in-scan π) m = there (outers-in π m)
    outers-in (in-take {c = c} {k} π) m = ++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (outers-in π m))
    outers-in (in-outer {fl = fl} π) (here refl) = ++⁺ˡ {xs = flatNames fl} (there (here refl))
    outers-in (in-outer {fl = fl} {oc} {k} π) (there m) = ++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ (outers-in π m)))))
    outers-in (in-lanes {fl = fl} {oc} {k} {t = so} πL) m =
      ++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) (outersL-in πL m)))))
    outers-in (in-source {S = S} {c} {kb = kb} {k} π) m =
      ++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ (outers-in π m))))))
    outers-in (in-body {S = S} {c} {kb = kb} {k} {t = src} π) m =
      ++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) (outers-in π m))))))
    outers-in (in-defer {k = k} π) m = ++⁺ʳ (quietName k) (outers-in π m)

    outersL-in : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (πL : PathLanes ls u) → ∀ {n} → n ∈ᴸ outersL πL → n ∈ᴸ laneNames ls
    outersL-in (this-lane {c = c} {k} π) m = ++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ˡ (outers-in π m)))
    outersL-in (next-lane {l = lane c k s} πL) m = ++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s) (outersL-in πL m)))

  -- No flag named on the way down lies below.
  mutual
    outers-apart : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) → AllPairs _≢_ (names t) → ∀ {n} → n ∈ᴸ outers π → n ∈ᴸ names u → ⊥
    outers-apart here ps () mu
    outers-apart (in-map π) ps o mu = outers-apart π ps o mu
    outers-apart (in-scan π) ps o mu = outers-apart π (pairs-tl ps) o mu
    outers-apart (in-take {c = c} {k} π) ps o mu = outers-apart π (pairs-r (quietName k) (pairs-r (cutNames c) ps)) o mu
    outers-apart (in-outer {fl = fl} {oc} {k} π) ps (here refl) mu =
      lookupᴬ (apart-r (flatNames fl) ps (there (here refl))) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ (names-path π mu))))) refl
    outers-apart (in-outer {fl = fl} {oc} {k} {t = so} π) ps (there o) mu =
      outers-apart π (proj₁ (pairs-split (names so) (pairs-tl (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))))) o mu
    outers-apart (in-lanes {fl = fl} {oc} {k} {t = so} πL) ps o mu =
      outersL-apart πL (pairs-r (names so) (pairs-tl (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps))))) o mu
    outers-apart (in-source {S = S} {c} {kb = kb} {k} {t = src} π) ps o mu =
      outers-apart π (proj₁ (pairs-split (names src) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-tl (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))))) o mu
    outers-apart (in-body {S = S} {c} {kb = kb} {k} {t = src} π) ps o mu =
      outers-apart π (pairs-r (names src) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-tl (pairs-r (cutNames c) (pairs-r (subjectNames S) ps)))))) o mu
    outers-apart (in-defer {k = k} π) ps o mu = outers-apart π (pairs-r (quietName k) ps) o mu

    outersL-apart : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (πL : PathLanes ls u) → AllPairs _≢_ (laneNames ls)
                  → ∀ {n} → n ∈ᴸ outersL πL → n ∈ᴸ names u → ⊥
    outersL-apart (this-lane {c = c} {k} {t = s} π) ps o mu = outers-apart π (proj₁ (pairs-split (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps)))) o mu
    outersL-apart (next-lane {l = lane c k s} πL) ps o mu = outersL-apart πL (pairs-r (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps))) o mu

  -- THE FLAGS LET GO: below a live node, every outer on the way down
  -- live too, so its flag, still unset, reads its outer as the rest do.
  module Alive {h} (H : Heapᴹ h) {Δ₀ A₀} {u : Sub h Δ₀ A₀} (ju : is-just (At.part H u) ≡ true) {ns : List (Name h)} where
    module FG = Flag H {ns}

    private
      unlist : ∀ {xs ys Δ A} {t : Sub h Δ A} → (∀ {n} → n ∈ᴸ names t → n ∈ᴸ xs → ⊥) → DoneBy H t (xs ++ ys) → DoneBy H t ys
      unlist {xs} {ys} {t = t} D = Flag.relist H {ns = xs ++ ys} {t = t} (λ _ m → ++⁺ʳ xs m) (λ mt m → [ (λ o → ⊥-elim (D mt o)) , (λ b → b) ]′ (++⁻ xs m))

      unlistL : ∀ {xs ys Δ B} {ls : List (Lane h Δ B)} → (∀ {n} → n ∈ᴸ laneNames ls → n ∈ᴸ xs → ⊥) → DoneByL H ls (xs ++ ys) → DoneByL H ls ys
      unlistL {xs} {ys} {ls = ls} D = Flag.relistL H {ns = xs ++ ys} {ls = ls} (λ _ m → ++⁺ʳ xs m) (λ ml m → [ (λ o → ⊥-elim (D ml o)) , (λ b → b) ]′ (++⁻ xs m))

      enlist : ∀ {xs ys Δ A} {t : Sub h Δ A} → (∀ {n} → n ∈ᴸ names t → n ∈ᴸ xs → ⊥) → DoneBy H t ys → DoneBy H t (xs ++ ys)
      enlist {xs} {ys} {t = t} D = Flag.relist H {ns = ys} {ns′ = xs ++ ys} {t = t} (λ mt m → [ (λ o → ⊥-elim (D mt o)) , (λ b → b) ]′ (++⁻ xs m)) (λ _ m → ++⁺ʳ xs m)

      enlistL : ∀ {xs ys Δ B} {ls : List (Lane h Δ B)} → (∀ {n} → n ∈ᴸ laneNames ls → n ∈ᴸ xs → ⊥) → DoneByL H ls ys → DoneByL H ls (xs ++ ys)
      enlistL {xs} {ys} {ls = ls} D = Flag.relistL H {ns = ys} {ns′ = xs ++ ys} {ls = ls} (λ ml m → [ (λ o → ⊥-elim (D ml o)) , (λ b → b) ]′ (++⁻ xs m)) (λ _ m → ++⁺ʳ xs m)

      both-false : ∀ {a} {P : Set a} (b : Bool) → (P → b ≡ false) → ((P → ⊥) → b ≡ false) → b ≡ false
      both-false false _ _ = refl
      both-false true  y n = n (λ p → absurd (y p))
        where absurd : true ≡ false → ⊥
              absurd ()

    mutual
      release : ∀ {Δ A} {t : Sub h Δ A} (π : Path t u) → AllPairs _≢_ (names t) → seen H π ≡ true → DoneBy H t (outers π ++ ns) → DoneBy H t ns
      release here ps sπ d = d
      release (in-map π) ps sπ d = FG.db-map (release π ps sπ (Flag.db-sub H d (in-map here) refl))
      release (in-scan π) ps sπ d = FG.db-scan (release π (pairs-tl ps) sπ (Flag.db-sub H d (in-scan here) refl))
      release (in-take {c = c} {k} {tk} π) ps sπ d =
        thru₂ (At.val H (Kit.live c)) (isTaking tk) sπ (λ ok s′ →
          FG.db-take (λ _ → release π (pairs-r (quietName k) (pairs-r (cutNames c) ps)) s′ (Flag.db-sub H d (in-take here) (seen-take (At.val H (Kit.live c)) ok))))
      release (in-outer {fl = fl} {oc} {k} {t = so} {ls} π) ps sπ d =
        FG.db-flat ((λ _ → off₀) , (λ _ → trans off₀ (sym (cong not (seen-up H π sπ ju)))))
                   (release π (proj₁ (pairs-split (names so) P′)) sπ (unlist {xs = F ∷ []} {ys = outers π ++ ns} (λ { m (here refl) → doneS m }) (Flag.db-sub H d (in-outer here) refl)))
                   (unlistL {xs = F ∷ outers π} {ys = ns} (λ { ml (here refl) → doneL ml ; ml (there o) → lookupᴬ (apart-l (names so) P′ ml) (outers-in π o) refl }) (Flag.dbL-of H d))
        where
          F = (cell _ , Flat.outerDone fl)
          P′ = pairs-tl (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
          off₀ = proj₁ (d here refl) (here refl)
          doneS : F ∈ᴸ names so → ⊥
          doneS m = lookupᴬ (apart-r (flatNames fl) ps (there (here refl))) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ m)))) refl
          doneL : F ∈ᴸ laneNames ls → ⊥
          doneL m = lookupᴬ (apart-r (flatNames fl) ps (there (here refl))) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m)))) refl
      release (in-lanes {fl = fl} {oc} {k} {t = so} {ls} πL) ps sπ d =
        FG.db-flat ((λ m → proj₁ (d here refl) (++⁺ʳ (outersL πL) m))
                   , (λ m̸ → proj₂ (d here refl) (λ m → [ (λ o → doneL (outersL-in πL o)) , m̸ ]′ (++⁻ (outersL πL) m))))
                   (unlist {xs = outersL πL} {ys = ns} (λ ms o → lookupᴬ (apart-r (names so) P′ ms) (outersL-in πL o) refl) (Flag.db-sub H d (in-outer here) refl))
                   (releaseL πL (pairs-r (names so) P′) sπ (Flag.dbL-of H d))
        where
          F = (cell _ , Flat.outerDone fl)
          P′ = pairs-tl (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
          doneL : F ∈ᴸ laneNames ls → ⊥
          doneL m = lookupᴬ (apart-r (flatNames fl) ps (there (here refl))) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m)))) refl
      release (in-source {S = S} {c} {kb = kb} {k} {t = src} {bd} π) ps sπ d =
        thru (is-just (At.part H bd)) sπ (λ _ s′ →
          FG.db-connect (λ jb′ → release π (proj₁ (pairs-split (names src) Q)) s′ (Flag.db-sub H d (in-source here) (∧-join jb′ refl)))
                        (λ js → unlist {xs = outers π} {ys = ns} (λ mb o → lookupᴬ (apart-l (names src) Q mb) (outers-in π o) refl) (Flag.db-sub H d (in-body here) (∧-join js refl))))
        where
          Q = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-tl (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))
      release (in-body {S = S} {c} {kb = kb} {k} {e = e} {t = src} π) ps sπ d =
        thru (is-just (At.part H src) ∨ is-just e) sπ (λ _ s′ →
          FG.db-connect (λ jb → unlist {xs = outers π} {ys = ns} (λ ms o → lookupᴬ (apart-r (names src) Q ms) (outers-in π o) refl) (Flag.db-sub H d (in-source here) (∧-join jb refl)))
                        (λ js′ → release π (pairs-r (names src) Q) s′ (Flag.db-sub H d (in-body here) (∧-join js′ refl))))
        where
          Q = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-tl (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))
      release (in-defer {k = k} π) ps sπ d = FG.db-defer (release π (pairs-r (quietName k) ps) sπ (Flag.db-sub H d (in-defer here) refl))

      releaseL : ∀ {Δ B} {ls : List (Lane h Δ B)} (πL : PathLanes ls u) → AllPairs _≢_ (laneNames ls) → seenL H πL ≡ true
               → DoneByL H ls (outersL πL ++ ns) → DoneByL H ls ns
      releaseL (this-lane {c = c} {k} {t = s} {ls} π) ps sπ dL =
        thru (At.val H (Kit.live c)) sπ (λ _ s′ →
          FG.dbL-cons (λ lv → release π (proj₁ (pairs-split (names s) Q)) s′ (Flag.dbL-head H dL lv))
                      (unlistL {xs = outers π} {ys = ns} (λ ml o → lookupᴬ (apart-l (names s) Q ml) (outers-in π o) refl) (Flag.dbL-tail H dL)))
        where
          Q = pairs-r (quietName k) (pairs-r (cutNames c) ps)
      releaseL (next-lane {l = lane c k s} {ls} πL) ps sπ dL =
        FG.dbL-cons (λ lv → unlist {xs = outersL πL} {ys = ns} (λ ms o → lookupᴬ (apart-r (names s) Q ms) (outersL-in πL o) refl) (Flag.dbL-head H dL lv))
                    (releaseL πL (pairs-r (names s) Q) sπ (Flag.dbL-tail H dL))
        where
          Q = pairs-r (quietName k) (pairs-r (cutNames c) ps)

    -- The other way: every outer on the way down live, its flag unset.
    mutual
      hold : ∀ {Δ A} {t : Sub h Δ A} (π : Path t u) → AllPairs _≢_ (names t) → seen H π ≡ true → DoneBy H t ns → DoneBy H t (outers π ++ ns)
      hold here ps sπ d = d
      hold (in-map π) ps sπ d = Flag.db-map H (hold π ps sπ (Flag.db-sub H d (in-map here) refl))
      hold (in-scan π) ps sπ d = Flag.db-scan H (hold π (pairs-tl ps) sπ (Flag.db-sub H d (in-scan here) refl))
      hold (in-take {c = c} {k} {tk} π) ps sπ d =
        thru₂ (At.val H (Kit.live c)) (isTaking tk) sπ (λ ok s′ →
          Flag.db-take H (λ _ → hold π (pairs-r (quietName k) (pairs-r (cutNames c) ps)) s′ (Flag.db-sub H d (in-take here) (seen-take (At.val H (Kit.live c)) ok))))
      hold (in-outer {fl = fl} {oc} {k} {t = so} {ls} π) ps sπ d =
        Flag.db-flat H {ns = F ∷ outers π ++ ns} ((λ _ → off₀) , (λ m̸ → ⊥-elim (m̸ (here refl))))
          (enlist {xs = F ∷ []} {ys = outers π ++ ns} (λ { m (here refl) → doneS m }) (hold π (proj₁ (pairs-split (names so) P′)) sπ (Flag.db-sub H d (in-outer here) refl)))
          (enlistL {xs = F ∷ outers π} {ys = ns} (λ { ml (here refl) → doneL ml ; ml (there o) → lookupᴬ (apart-l (names so) P′ ml) (outers-in π o) refl }) (Flag.dbL-of H d))
        where
          F = (cell _ , Flat.outerDone fl)
          P′ = pairs-tl (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
          off₀ = both-false (At.val H (Flat.outerDone fl)) (proj₁ (d here refl)) (λ m̸ → trans (proj₂ (d here refl) m̸) (cong not (seen-up H π sπ ju)))
          doneS : F ∈ᴸ names so → ⊥
          doneS m = lookupᴬ (apart-r (flatNames fl) ps (there (here refl))) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ m)))) refl
          doneL : F ∈ᴸ laneNames ls → ⊥
          doneL m = lookupᴬ (apart-r (flatNames fl) ps (there (here refl))) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m)))) refl
      hold (in-lanes {fl = fl} {oc} {k} {t = so} {ls} πL) ps sπ d =
        Flag.db-flat H {ns = outersL πL ++ ns}
                   ((λ m → [ (λ o → ⊥-elim (doneL (outersL-in πL o))) , proj₁ (d here refl) ]′ (++⁻ (outersL πL) m))
                   , (λ m̸ → proj₂ (d here refl) (λ m → m̸ (++⁺ʳ (outersL πL) m))))
                   (enlist {xs = outersL πL} {ys = ns} (λ ms o → lookupᴬ (apart-r (names so) P′ ms) (outersL-in πL o) refl) (Flag.db-sub H d (in-outer here) refl))
                   (holdL πL (pairs-r (names so) P′) sπ (Flag.dbL-of H d))
        where
          F = (cell _ , Flat.outerDone fl)
          P′ = pairs-tl (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
          doneL : F ∈ᴸ laneNames ls → ⊥
          doneL m = lookupᴬ (apart-r (flatNames fl) ps (there (here refl))) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m)))) refl
      hold (in-source {S = S} {c} {kb = kb} {k} {t = src} {bd} π) ps sπ d =
        thru (is-just (At.part H bd)) sπ (λ _ s′ →
          Flag.db-connect H (λ jb′ → hold π (proj₁ (pairs-split (names src) Q)) s′ (Flag.db-sub H d (in-source here) (∧-join jb′ refl)))
                            (λ js → enlist {xs = outers π} {ys = ns} (λ mb o → lookupᴬ (apart-l (names src) Q mb) (outers-in π o) refl) (Flag.db-sub H d (in-body here) (∧-join js refl))))
        where
          Q = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-tl (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))
      hold (in-body {S = S} {c} {kb = kb} {k} {e = e} {t = src} π) ps sπ d =
        thru (is-just (At.part H src) ∨ is-just e) sπ (λ _ s′ →
          Flag.db-connect H (λ jb → enlist {xs = outers π} {ys = ns} (λ ms o → lookupᴬ (apart-r (names src) Q ms) (outers-in π o) refl) (Flag.db-sub H d (in-source here) (∧-join jb refl)))
                            (λ js′ → hold π (pairs-r (names src) Q) s′ (Flag.db-sub H d (in-body here) (∧-join js′ refl))))
        where
          Q = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-tl (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))
      hold (in-defer {k = k} π) ps sπ d = Flag.db-defer H (hold π (pairs-r (quietName k) ps) sπ (Flag.db-sub H d (in-defer here) refl))

      holdL : ∀ {Δ B} {ls : List (Lane h Δ B)} (πL : PathLanes ls u) → AllPairs _≢_ (laneNames ls) → seenL H πL ≡ true
            → DoneByL H ls ns → DoneByL H ls (outersL πL ++ ns)
      holdL (this-lane {c = c} {k} {t = s} {ls} π) ps sπ dL =
        thru (At.val H (Kit.live c)) sπ (λ _ s′ →
          Flag.dbL-cons H (λ lv → hold π (proj₁ (pairs-split (names s) Q)) s′ (Flag.dbL-head H dL lv))
                          (enlistL {xs = outers π} {ys = ns} (λ ml o → lookupᴬ (apart-l (names s) Q ml) (outers-in π o) refl) (Flag.dbL-tail H dL)))
        where
          Q = pairs-r (quietName k) (pairs-r (cutNames c) ps)
      holdL (next-lane {l = lane c k s} {ls} πL) ps sπ dL =
        Flag.dbL-cons H (λ lv → enlist {xs = outersL πL} {ys = ns} (λ ms o → lookupᴬ (apart-r (names s) Q ms) (outersL-in πL o) refl) (Flag.dbL-head H dL lv))
                        (holdL πL (pairs-r (names s) Q) sπ (Flag.dbL-tail H dL))
        where
          Q = pairs-r (quietName k) (pairs-r (cutNames c) ps)
