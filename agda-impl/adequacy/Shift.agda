{-# OPTIONS --guardedness #-}

-- THE REPLANT FRAME'S WALK: a node `u` replanted to `v` under a write at
-- `u`'s own names, walked from the node up to the root.  Every node
-- above reads its path child only through the child's part, its heads
-- and its leftover; every node beside the path reads alike.
module adequacy.Shift where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ; ++⁻)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; _∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (lower)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Data.Sum using ([_,_]′)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.Unit using (⊤)

open import denotation.MonotonicList using (Timeline; Pos)
import denotation.Unfold as U
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (maybe; quiet; module Heap; module Run) renaming (module Machine to Shared)
open import adequacy.Strong using (module Strongly)
open import adequacy.Torn using (module Tearing)
open import adequacy.Moves using (module Moving)
open import adequacy.Local using (module Locality)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Frame using (module Framing)
open import adequacy.Restage using (module Restaging)

module Shifting (R : Set) where
  open Heap using (Sink; Quiet; slot; cell)
  open Run (Pureᴾ R) using (Ref; Subject; module Kit; module FlatKit)
  open FlatKit using (Flat)
  open Shared Timeline (Out R) using (Heapᴹ; look)
  open Strongly R using (Sub; Path; PathLanes; here; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; this-lane; next-lane; _⊕_; _⊕ᴸ_;
                         pendingˢ; coldˢ; ofˢ; doneˢ; joinˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ; deferˢ; Lane; lane; Taking; taking; ending; taken; isTaking;
                         names; laneNames; cutNames; quietName; subjectNames; flatNames; module At; seen; seenL; seen-join;
                         Each; Lingers; Heads; Pinned; Tied; rest-pinned; bursts-pinned; bursts-moved; under-moved; union-pinned;
                         pinned-trans; pinned-sym; restful-pinned; ∧-split; ∧-join; false≢)
  open Tearing R using (Alike; Off; part-alike; partLanes-alike; seen-alike; seenL-alike; names-path; lanes-path; apart-r; apart-l; narrow; each-same)
  open Moving R using (plant; plantᴸ; pairs-r; pairs-split)
  open Locality R using (module Heaps)
  open Ghosting R using (each-sub; each-lanes)
  open Framing R using (Untold; Ended; Tells; untold; untoldᴹ; untoldᴸ; heads-map; heads-scan; heads-take; heads-source; ended-head; shut-heads; just-of)
  open Restaging R using (leftover-restful)

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

  -- A connect's leftover over a source run alike and a body pinned alike.
  conn-pin : ∀ {Γ A B} rp (N N′ : U.Node Γ A) {x x′ : U.Node (A ∷ Γ) ⊤} → N′ ≡ N → Pinned (U.restˢ {B = ⊤} x) (U.restˢ {B = ⊤} x′)
           → Pinned (U.restˢ {B = ⊤} (U.unionᶜ {B = B} (U.burstingᶜ rp N) (U.underᶜ (U.live N) x)))
                    (U.restˢ {B = ⊤} (U.unionᶜ {B = B} (U.burstingᶜ rp N′) (U.underᶜ (U.live N′) x′)))
  conn-pin rp N N′ refl lp = union-pinned (bursts-pinned rp N (U.step N)) (under-moved (U.live N) (U.live N) lp)

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

  merged-eq : ∀ {h} (G : Heapᴹ h) {Δ A B} op (g : A → Pos → U.Node Δ B) o L Q pl {b} → At.merged G op g o L Q pl ≡ just b → U.flatMapᶜ op g o L Q pl ≡ b
  merged-eq G op g (just _) L       Q       pl refl = refl
  merged-eq G op g nothing  (_ ∷ _) Q       pl refl = refl
  merged-eq G op g nothing  []      (_ ∷ _) pl refl = refl
  merged-eq G op g nothing  []      []      pl ()

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

  postulate
    -- A flatMap's head moved by its outer and lanes alone, each heading
    -- no sooner than `q`.
    heads-flat : ∀ {Δ A B q} op (g : A → Pos → U.Node Δ B) (o o′ : Maybe (U.Node Δ A)) (L L′ : List (U.Node Δ B)) Q pl
               → Heads q (U.flatMapᶜ op g o L Q pl) → (∀ {c} → o′ ≡ just c → Heads q c) → All (Heads q) L′
               → Heads q (U.flatMapᶜ op g o′ L′ Q pl)

    -- A shut tells only the joiners of the connect it ends.
    untold-shut : ∀ {Γ A B C} (i : C ∈ᴸ Γ) c (b : U.Node (A ∷ Γ) B) → untold (there i) (U.shut (here refl) c b) ≡ untold (there i) b

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
             → ∀ {c} → At.part G (flatMapˢ op f fl oc k r pl so ls′) ≡ just c → Tied pl (At.pooled G fl so ls′)
      restsL : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
             → (ψ : PathLanes ls (connectˢ S c b kb k fd rp e rt src bd)) → seenL G ψ ≡ true
             → ∀ {n} → At.part G (connectˢ S c b kb k fd rp e rt src bd) ≡ just n
             → At.part G src ≡ nothing → ∀ {c₀} → e ≡ just c₀ → Tied rt (At.leftover G {B = ⊤} src)

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
      { pools = λ {op = op₀} {f = f₀} {fl = fl₀} {oc = oc₀} {k = k₀} {r = r₀} {pl = pl₀} {so = so₀} {ls = ls₀} ψ sn e → pinned-trans (Lingers.pools lg ψ (se ψ sn) (trans (sym (part-at ψ al)) e)) (pin-alike (pooled-from {op = op₀} {f = f₀} {fl = fl₀} {oc = oc₀} {k = k₀} {r = r₀} {pl = pl₀} {so = so₀} {ls = ls₀} (λ m → names-path ψ m) al))
      ; rests = λ {src = src₀} ψ sn e pn pe → pinned-trans (Lingers.rests lg ψ (se ψ sn) (trans (sym (part-at ψ al)) e) (trans (sym (part-at (ψ ⊕ in-source here) al)) pn) pe)
                                              (pin-alike (leftover-from {B = ⊤} {x = src₀} (λ m → names-path (ψ ⊕ in-source here) m) al)) }
      where
        se : ∀ {Δ′ A′} {x : Sub h Δ′ A′} (ψ : Path t x) → seen H′ ψ ≡ true → seen H ψ ≡ true
        se ψ sn = trans (sym (seen-alike H H′ ψ al)) sn

    lingersL-alike : ∀ {Δ B} {ls : List (Lane h Δ B)} → Alike H H′ (laneNames ls) → LingersL H ls → LingersL H′ ls
    lingersL-alike {ls = ls} al lL = record
      { poolsL = λ {op = op₀} {f = f₀} {fl = fl₀} {oc = oc₀} {k = k₀} {r = r₀} {pl = pl₀} {so = so₀} {ls′ = ls₀} πL sn e → pinned-trans (LingersL.poolsL lL πL (se πL sn) (trans (sym (partL-at πL al)) e)) (pin-alike (pooled-from {op = op₀} {f = f₀} {fl = fl₀} {oc = oc₀} {k = k₀} {r = r₀} {pl = pl₀} {so = so₀} {ls = ls₀} (λ m → lanes-path πL m) al))
      ; restsL = λ {src = src₀} πL sn e pn pe → pinned-trans (LingersL.restsL lL πL (se πL sn) (trans (sym (partL-at πL al)) e) (trans (sym (partL-at (πL ⊕ᴸ in-source here) al)) pn) pe)
                                               (pin-alike (leftover-from {B = ⊤} {x = src₀} (λ m → lanes-path (πL ⊕ᴸ in-source here) m) al)) }
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
            → (∀ {c} → At.part G (flatMapˢ op f fl oc k r pl so ls) ≡ just c → Tied pl (At.pooled G fl so ls))
            → Lingers G so → LingersL G ls → Lingers G (flatMapˢ op f fl oc k r pl so ls)
    lg-flat pool lo lL = record
      { pools = λ { here _ x → pool x ; (in-outer ψ) sn x → Lingers.pools lo ψ sn x ; (in-lanes πL) sn x → LingersL.poolsL lL πL sn x }
      ; rests = λ { (in-outer ψ) sn x pn pe → Lingers.rests lo ψ sn x pn pe ; (in-lanes πL) sn x pn pe → LingersL.restsL lL πL sn x pn pe } }

    lg-connect : ∀ {Δ A B S c b kb k fd rp e rt} {src : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
               → (∀ {n} → At.part G (connectˢ S c b kb k fd rp e rt src bd) ≡ just n → At.part G src ≡ nothing → ∀ {c₀} → e ≡ just c₀
                  → Tied rt (At.leftover G {B = ⊤} src))
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
  -- THE WALK: `u` replanted to `v`, the heaps moved only at `u`'s names.
  -- Every node above `u` on the path: its own cells, and every child
  -- beside the path, read alike.

  module Walk {h} (H H′ : Heapᴹ h) {Δ₀ A₀} {u : Sub h Δ₀ A₀} (v : Sub h Δ₀ A₀) (off : Off H H′ (names u))
              (rv₀ : is-just (At.part H′ v) ≡ true → is-just (At.part H u) ≡ true) where
    open Heaps H H′ using (keep; keeps)

    -- What a node on the path keeps: its own cells and its other
    -- children, apart from `u`'s names.
    module Take {Δ A} (c : Kit.Cut h) (k : Maybe (Quiet h)) {s : Sub h Δ A} (π : Path s u) (ps : AllPairs _≢_ (cutNames c ++ quietName k ++ names s)) where
      fresh : AllPairs _≢_ (names s)
      fresh = pairs-r (quietName k) (pairs-r (cutNames c) ps)

      live′ : At.val H′ (Kit.live c) ≡ At.val H (Kit.live c)
      live′ = cong lower (keep off (λ m → ++⁺ʳ (quietName k) (names-path π m)) (Kit.live c) (apart-r (cutNames c) ps (here refl)))

    module Outer {Δ A B} (fl : Flat A h) (oc : Kit.Cut h) (k : Maybe (Quiet h)) (r : Sink h ⊤) {so : Sub h Δ A} (ls : List (Lane h Δ B)) (π : Path so u)
                 (ps : AllPairs _≢_ (flatNames fl ++ cutNames oc ++ quietName k ++ (slot _ , r) ∷ names so ++ laneNames ls)) where
      private
        P′ : AllPairs _≢_ (names so ++ laneNames ls)
        P′ = pairs-tl (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))

        rest : ∀ {n} → n ∈ᴸ names u → n ∈ᴸ (cutNames oc ++ quietName k ++ (slot _ , r) ∷ names so ++ laneNames ls)
        rest m = ++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ (names-path π m))))

      fresh : AllPairs _≢_ (names so)
      fresh = proj₁ (pairs-split (names so) P′)

      lanesA : Alike H H′ (laneNames ls)
      lanesA = keeps off (λ m → names-path π m) (λ m → apart-l (names so) P′ m)

      lanes : At.partLanes H′ ls ≡ At.partLanes H ls
      lanes = partLanes-alike H H′ ls lanesA

      queue : look H′ (Flat.queue fl) ≡ look H (Flat.queue fl)
      queue = keep off rest (Flat.queue fl) (apart-r (flatNames fl) ps (there (there (here refl))))

      done : look H′ (Flat.outerDone fl) ≡ look H (Flat.outerDone fl)
      done = keep off rest (Flat.outerDone fl) (apart-r (flatNames fl) ps (there (here refl)))

    module Lanes {Δ A B} (fl : Flat A h) (oc : Kit.Cut h) (k : Maybe (Quiet h)) (r : Sink h ⊤) (so : Sub h Δ A) {ls : List (Lane h Δ B)} (πL : PathLanes ls u)
                 (ps : AllPairs _≢_ (flatNames fl ++ cutNames oc ++ quietName k ++ (slot _ , r) ∷ names so ++ laneNames ls)) where
      private
        P′ : AllPairs _≢_ (names so ++ laneNames ls)
        P′ = pairs-tl (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))

        rest : ∀ {n} → n ∈ᴸ names u → n ∈ᴸ (cutNames oc ++ quietName k ++ (slot _ , r) ∷ names so ++ laneNames ls)
        rest m = ++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) (lanes-path πL m))))

      fresh : AllPairs _≢_ (laneNames ls)
      fresh = pairs-r (names so) P′

      soA : Alike H H′ (names so)
      soA = keeps off (λ m → lanes-path πL m) (λ m → apart-r (names so) P′ m)

      outer : At.part H′ so ≡ At.part H so
      outer = part-alike H H′ so soA

      queue : look H′ (Flat.queue fl) ≡ look H (Flat.queue fl)
      queue = keep off rest (Flat.queue fl) (apart-r (flatNames fl) ps (there (there (here refl))))

      done : look H′ (Flat.outerDone fl) ≡ look H (Flat.outerDone fl)
      done = keep off rest (Flat.outerDone fl) (apart-r (flatNames fl) ps (there (here refl)))

    module Source {Δ A B} (S : Subject A h) (c : Kit.Cut h) (b : Ref h (maybe quiet)) (kb k : Maybe (Quiet h)) {src : Sub h Δ A} (bd : Sub h (A ∷ Δ) B)
                  (π : Path src u) (ps : AllPairs _≢_ (subjectNames S ++ cutNames c ++ (cell _ , b) ∷ quietName kb ++ quietName k ++ names src ++ names bd)) where
      private
        Q : AllPairs _≢_ (names src ++ names bd)
        Q = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-tl (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))

      fresh : AllPairs _≢_ (names src)
      fresh = proj₁ (pairs-split (names src) Q)

      bdA : Alike H H′ (names bd)
      bdA = keeps off (λ m → names-path π m) (λ m → apart-l (names src) Q m)

      body : At.part H′ bd ≡ At.part H bd
      body = part-alike H H′ bd bdA

    module Body {Δ A B} (S : Subject A h) (c : Kit.Cut h) (b : Ref h (maybe quiet)) (kb k : Maybe (Quiet h)) (src : Sub h Δ A) {bd : Sub h (A ∷ Δ) B}
                (π : Path bd u) (ps : AllPairs _≢_ (subjectNames S ++ cutNames c ++ (cell _ , b) ∷ quietName kb ++ quietName k ++ names src ++ names bd)) where
      private
        Q : AllPairs _≢_ (names src ++ names bd)
        Q = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-tl (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))

      fresh : AllPairs _≢_ (names bd)
      fresh = pairs-r (names src) Q

      srcA : Alike H H′ (names src)
      srcA = keeps off (λ m → names-path π m) (λ m → apart-r (names src) Q m)

      source : At.part H′ src ≡ At.part H src
      source = part-alike H H′ src srcA

    module This {Δ B} (c : Kit.Cut h) (k : Maybe (Quiet h)) {s : Sub h Δ B} (ls : List (Lane h Δ B)) (π : Path s u)
                (ps : AllPairs _≢_ (cutNames c ++ quietName k ++ names s ++ laneNames ls)) where
      private
        Q : AllPairs _≢_ (names s ++ laneNames ls)
        Q = pairs-r (quietName k) (pairs-r (cutNames c) ps)

      fresh : AllPairs _≢_ (names s)
      fresh = proj₁ (pairs-split (names s) Q)

      restA : Alike H H′ (laneNames ls)
      restA = keeps off (λ m → names-path π m) (λ m → apart-l (names s) Q m)

      rest : At.partLanes H′ ls ≡ At.partLanes H ls
      rest = partLanes-alike H H′ ls restA

      live′ : At.val H′ (Kit.live c) ≡ At.val H (Kit.live c)
      live′ = cong lower (keep off (λ m → ++⁺ʳ (quietName k) (++⁺ˡ (names-path π m))) (Kit.live c) (apart-r (cutNames c) ps (here refl)))

      on : At.val H′ (Kit.live c) ≡ true → At.val H (Kit.live c) ≡ true
      on lv = trans (sym live′) lv

    module Next {Δ B} (c : Kit.Cut h) (k : Maybe (Quiet h)) (s : Sub h Δ B) {ls : List (Lane h Δ B)} (πL : PathLanes ls u)
                (ps : AllPairs _≢_ (cutNames c ++ quietName k ++ names s ++ laneNames ls)) where
      private
        Q : AllPairs _≢_ (names s ++ laneNames ls)
        Q = pairs-r (quietName k) (pairs-r (cutNames c) ps)

      fresh : AllPairs _≢_ (laneNames ls)
      fresh = pairs-r (names s) Q

      headA : Alike H H′ (names s)
      headA = keeps off (λ m → lanes-path πL m) (λ m → apart-r (names s) Q m)

      head : At.part H′ s ≡ At.part H s
      head = part-alike H H′ s headA

      live′ : At.val H′ (Kit.live c) ≡ At.val H (Kit.live c)
      live′ = cong lower (keep off (λ m → ++⁺ʳ (quietName k) (++⁺ʳ (names s) (lanes-path πL m))) (Kit.live c) (apart-r (cutNames c) ps (here refl)))

      on : At.val H′ (Kit.live c) ≡ true → At.val H (Kit.live c) ≡ true
      on lv = trans (sym live′) lv

    --------------------------------------------------------------------
    -- NO PART REVIVED: a node the write leaves held was held before.

    take-rev : ∀ {Δ A} ib (p : A → Bool) (tk : Taking Δ A) (m m′ : Maybe (U.Node Δ A)) {b b′} → b′ ≡ b → (is-just m′ ≡ true → is-just m ≡ true)
             → is-just (if b′ then At.taking? H′ ib p tk m′ else nothing) ≡ true → is-just (if b then At.taking? H ib p tk m else nothing) ≡ true
    take-rev ib p tk           m        m′       {false} refl rm ()
    take-rev ib p taking       (just _) m′       {true}  refl rm j = refl
    take-rev ib p taking       nothing  (just _) {true}  refl rm j = false≢ (rm refl)
    take-rev ib p taking       nothing  nothing  {true}  refl rm ()
    take-rev ib p (ending _ _) m        m′       {true}  refl rm j = refl
    take-rev ib p taken        m        m′       {true}  refl rm ()

    lane-rev : ∀ {Δ B} {b b′} → b′ ≡ b → (m m′ : Maybe (U.Node Δ B)) (L L′ : List (U.Node Δ B))
             → (is-just m′ ≡ true → is-just m ≡ true) → (filled L′ ≡ true → filled L ≡ true)
             → filled (if b′ then At.consᴹ H′ m′ L′ else L′) ≡ true → filled (if b then At.consᴹ H m L else L) ≡ true
    lane-rev {b = false} refl m        m′       L L′ rm rL j = rL j
    lane-rev {b = true}  refl (just _) m′       L L′ rm rL j = refl
    lane-rev {b = true}  refl nothing  (just _) L L′ rm rL j = false≢ (rm refl)
    lane-rev {b = true}  refl nothing  nothing  L L′ rm rL j = rL j

    merged-rev : ∀ {Δ A B} op (g : A → Pos → U.Node Δ B) (o o′ : Maybe (U.Node Δ A)) (L L′ : List (U.Node Δ B)) (Q Q′ : List A) pl
               → (is-just o′ ≡ true → is-just o ≡ true) → (filled L′ ≡ true → filled L ≡ true) → (filled Q′ ≡ true → filled Q ≡ true)
               → is-just (At.merged H′ op g o′ L′ Q′ pl) ≡ true → is-just (At.merged H op g o L Q pl) ≡ true
    merged-rev op g (just _) o′       L       L′      Q       Q′      pl ro rL rQ j = refl
    merged-rev op g nothing  o′       (_ ∷ _) L′      Q       Q′      pl ro rL rQ j = refl
    merged-rev op g nothing  o′       []      L′      (_ ∷ _) Q′      pl ro rL rQ j = refl
    merged-rev op g nothing  (just _) []      L′      []      Q′      pl ro rL rQ j = false≢ (ro refl)
    merged-rev op g nothing  nothing  []      (_ ∷ _) []      Q′      pl ro rL rQ j = false≢ (rL refl)
    merged-rev op g nothing  nothing  []      []      []      (_ ∷ _) pl ro rL rQ j = false≢ (rQ refl)
    merged-rev op g nothing  nothing  []      []      []      []      pl ro rL rQ ()

    conn-rev : ∀ {Δ A B} rp (e : Maybe Pos) (rt : U.Node Δ A) (s s′ : Maybe (U.Node Δ A)) (mb mb′ : Maybe (U.Node (A ∷ Δ) B))
             → (is-just s′ ≡ true → is-just s ≡ true) → (is-just mb′ ≡ true → is-just mb ≡ true)
             → is-just (At.connected H′ rp e rt s′ mb′) ≡ true → is-just (At.connected H rp e rt s mb) ≡ true
    conn-rev rp e        rt s        s′       nothing  (just _) rs rb j = false≢ (rb refl)
    conn-rev rp e        rt s        s′       nothing  nothing  rs rb ()
    conn-rev rp e        rt (just _) s′       (just _) mb′      rs rb j = refl
    conn-rev rp (just _) rt nothing  s′       (just _) mb′      rs rb j = refl
    conn-rev rp nothing  rt nothing  (just _) (just _) mb′      rs rb j = false≢ (rs refl)
    conn-rev rp nothing  rt nothing  nothing  (just _) (just _) rs rb ()
    conn-rev rp nothing  rt nothing  nothing  (just _) nothing  rs rb ()

    mutual
      revive : ∀ {Δ A} {t : Sub h Δ A} (π : Path t u) → AllPairs _≢_ (names t) → is-just (At.part H′ (plant π v)) ≡ true → is-just (At.part H t) ≡ true
      revive here ps = rv₀
      revive (in-map {f = f} {t = s} π) ps j =
        map-fwd H (U.mapᶜ f) (At.part H s) (revive π ps (map-back H′ (U.mapᶜ f) (At.part H′ (plant π v)) j))
      revive (in-scan {f = f} {r} {t = s} π) ps j =
        map-fwd H (U.scanᶜ f (At.val H r)) (At.part H s) (revive π (pairs-tl ps) (map-back H′ (U.scanᶜ f (At.val H′ r)) (At.part H′ (plant π v)) j))
      revive (in-take {i = ib} {p} {c} {k} {tk} {t = s} π) ps =
        take-rev ib p tk (At.part H s) (At.part H′ (plant π v)) Tk.live′ (revive π Tk.fresh)
        where module Tk = Take c k π ps
      revive (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} {ls} π) ps =
        merged-rev op (λ a q → U.subscribe (f a) q) (At.part H so) (At.part H′ (plant π v)) (At.partLanes H ls) (At.partLanes H′ ls)
          (At.val H (Flat.queue fl)) (At.val H′ (Flat.queue fl)) pl (revive π O.fresh) (via-≡ filled O.lanes) (via-≡ filled (cong lower O.queue))
        where module O = Outer fl oc k r ls π ps
      revive (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} {ls} πL) ps =
        merged-rev op (λ a q → U.subscribe (f a) q) (At.part H so) (At.part H′ so) (At.partLanes H ls) (At.partLanes H′ (plantᴸ πL v))
          (At.val H (Flat.queue fl)) (At.val H′ (Flat.queue fl)) pl (via-≡ is-just Ln.outer) (reviveL πL Ln.fresh) (via-≡ filled (cong lower Ln.queue))
        where module Ln = Lanes fl oc k r so πL ps
      revive (in-source {S = S} {c} {b} {kb} {k} {e = e} {rp} {rt} {t = src} {bd} π) ps =
        conn-rev rp e rt (At.part H src) (At.part H′ (plant π v)) (At.part H bd) (At.part H′ bd) (revive π Sr.fresh) (via-≡ is-just Sr.body)
        where module Sr = Source S c b kb k bd π ps
      revive (in-body {S = S} {c} {b} {kb} {k} {e = e} {rp} {rt} {t = src} {bd} π) ps =
        conn-rev rp e rt (At.part H src) (At.part H′ src) (At.part H bd) (At.part H′ (plant π v)) (via-≡ is-just Bd.source) (revive π Bd.fresh)
        where module Bd = Body S c b kb k src π ps
      revive (in-defer {k = k} π) ps = revive π (pairs-r (quietName k) ps)

      reviveL : ∀ {Δ B} {ls : List (Lane h Δ B)} (πL : PathLanes ls u) → AllPairs _≢_ (laneNames ls)
              → filled (At.partLanes H′ (plantᴸ πL v)) ≡ true → filled (At.partLanes H ls) ≡ true
      reviveL (this-lane {c = c} {k} {t = s} {ls} π) ps =
        lane-rev Th.live′ (At.part H s) (At.part H′ (plant π v)) (At.partLanes H ls) (At.partLanes H′ ls) (revive π Th.fresh) (via-≡ filled Th.rest)
        where module Th = This c k ls π ps
      reviveL (next-lane {l = lane c k s} {ls} πL) ps =
        lane-rev Nx.live′ (At.part H s) (At.part H′ s) (At.partLanes H ls) (At.partLanes H′ (plantᴸ πL v)) (via-≡ is-just Nx.head) (reviveL πL Nx.fresh)
        where module Nx = Next c k s πL ps

    -- A node held after the write, read where it was held before.
    held : ∀ {ℓ} {X : Set ℓ} {Δ A} {t : Sub h Δ A} (π : Path t u) → AllPairs _≢_ (names t)
         → ∀ {n} → At.part H′ (plant π v) ≡ just n → (∀ {n₀} → At.part H t ≡ just n₀ → X) → X
    held π ps x k = k (proj₂ (just-of (revive π ps (cong is-just x))))

    --------------------------------------------------------------------
    -- NO JOINER NEWLY UNTOLD: what a node above leaves untold its
    -- joiners after the write, it left untold before.

    module Telling (tl₀ : ∀ {C} (i : C ∈ᴸ Δ₀) {b₀ b′} → At.part H u ≡ just b₀ → At.part H′ v ≡ just b′ → untold i b′ ⊆ᴾ untold i b₀) where
      untold-≡ : ∀ {Γ B C} (i : C ∈ᴸ Γ) {x x′ y y′ : U.Node Γ B} → x ≡ y → x′ ≡ y′ → untold i x′ ⊆ᴾ untold i x → untold i y′ ⊆ᴾ untold i y
      untold-≡ i refl refl s = s

      told-ᴹ : ∀ {Δ A B C} (i : C ∈ᴸ Δ) (g g′ : U.Node Δ A → U.Node Δ B) → (∀ c → untold i (g c) ≡ untold i c) → (∀ c → untold i (g′ c) ≡ untold i c)
             → (m m′ : Maybe (U.Node Δ A)) → ∀ {b₀ b′} → At.mapᴹ H g m ≡ just b₀ → At.mapᴹ H′ g′ m′ ≡ just b′
             → (∀ {c c′} → m ≡ just c → m′ ≡ just c′ → untold i c′ ⊆ᴾ untold i c) → untold i b′ ⊆ᴾ untold i b₀
      told-ᴹ i g g′ up up′ (just c) (just c′) refl refl sub = λ m → ≡-⊆ (sym (up c)) (sub refl refl (≡-⊆ (up′ c′) m))
      told-ᴹ i g g′ up up′ nothing  m′        ()   e′   sub
      told-ᴹ i g g′ up up′ (just c) nothing   e₀   ()   sub

      told-take : ∀ {Δ A C} (i : C ∈ᴸ Δ) ib (p : A → Bool) (tk : Taking Δ A) (m m′ : Maybe (U.Node Δ A)) {b b′} → b′ ≡ b
                → ∀ {b₀ b₁} → (if b then At.taking? H ib p tk m else nothing) ≡ just b₀ → (if b′ then At.taking? H′ ib p tk m′ else nothing) ≡ just b₁
                → (b ∧ isTaking tk ≡ true → ∀ {c c′} → m ≡ just c → m′ ≡ just c′ → untold i c′ ⊆ᴾ untold i c) → untold i b₁ ⊆ᴾ untold i b₀
      told-take i ib p tk           m m′ {b = false} refl ()   e′   sub
      told-take i ib p taking       m m′ {b = true}  refl e₀   e′   sub =
        told-ᴹ i (U.takeWhileᶜ ib p) (U.takeWhileᶜ ib p) (λ _ → refl) (λ _ → refl) m m′ e₀ e′ (sub refl)
      told-take i ib p (ending _ _) m m′ {b = true}  refl refl refl sub = λ x → x
      told-take i ib p taken        m m′ {b = true}  refl ()   e′   sub

      toldᴹ : ∀ {Δ B C} (i : C ∈ᴸ Δ) (m m′ : Maybe (U.Node Δ B)) → (∀ {c c′} → m ≡ just c → m′ ≡ just c′ → untold i c′ ⊆ᴾ untold i c)
            → (is-just m′ ≡ true → is-just m ≡ true) → untoldᴹ i m′ ⊆ᴾ untoldᴹ i m
      toldᴹ i m        nothing   sub rv = λ ()
      toldᴹ i (just c) (just c′) sub rv = sub refl refl
      toldᴹ i nothing  (just c′) sub rv = false≢ (rv refl)

      flat-told : ∀ {Δ A B C} (i : C ∈ᴸ Δ) op (g : A → Pos → U.Node Δ B) (o o′ : Maybe (U.Node Δ A)) (L L′ : List (U.Node Δ B)) (Q Q′ : List A) pl
                → untoldᴹ i o′ ⊆ᴾ untoldᴹ i o → untoldᴸ i L′ ⊆ᴾ untoldᴸ i L → Q′ ≡ Q
                → ∀ {b₀ b′} → At.merged H op g o L Q pl ≡ just b₀ → At.merged H′ op g o′ L′ Q′ pl ≡ just b′ → untold i b′ ⊆ᴾ untold i b₀
      flat-told i op g o o′ L L′ Q _ pl so sL refl e₀ e′ =
        untold-≡ i (merged-eq H op g o L Q pl e₀) (merged-eq H′ op g o′ L′ Q pl e′)
          (++-mono (untoldᴹ i o) (untoldᴹ i o′) so (++-mono (untoldᴸ i L) (untoldᴸ i L′) sL (λ m → m)))

      lane-told : ∀ {Δ B C} (i : C ∈ᴸ Δ) {b b′} → b′ ≡ b → (m m′ : Maybe (U.Node Δ B)) (L L′ : List (U.Node Δ B))
                → (b ≡ true → untoldᴹ i m′ ⊆ᴾ untoldᴹ i m) → untoldᴸ i L′ ⊆ᴾ untoldᴸ i L
                → untoldᴸ i (if b′ then At.consᴹ H′ m′ L′ else L′) ⊆ᴾ untoldᴸ i (if b then At.consᴹ H m L else L)
      lane-told i {b = false} refl m m′ L L′ fm fL = fL
      lane-told i {b = true}  refl m m′ L L′ fm fL =
        λ x → ≡-⊆ (sym (cons-untold H i m L)) (++-mono (untoldᴹ i m) (untoldᴹ i m′) (fm refl) fL (≡-⊆ (cons-untold H′ i m′ L′) x))

      -- The source replanted: a source still running past an end is
      -- refuted by the end, and one gone on both sides tells alike.
      src-told : ∀ {Δ A B C} (i : C ∈ᴸ Δ) rp (e : Maybe Pos) (rt : U.Node Δ A) (s s′ : Maybe (U.Node Δ A)) (mb : Maybe (U.Node (A ∷ Δ) B))
               → (is-just s′ ≡ true → is-just s ≡ true)
               → (is-just mb ≡ true → ∀ {c c′} → s ≡ just c → s′ ≡ just c′ → untold i c′ ⊆ᴾ untold i c)
               → (∀ {n} → At.connected H rp e rt s mb ≡ just n → ∀ {c₀} → e ≡ just c₀ → s ≡ nothing)
               → ∀ {b₀ b′} → At.connected H rp e rt s mb ≡ just b₀ → At.connected H′ rp e rt s′ mb ≡ just b′ → untold i b′ ⊆ᴾ untold i b₀
      src-told i rp e        rt s        s′        nothing  rv sub en ()   e′
      src-told i rp e        rt (just c) (just c′) (just b) rv sub en refl refl = ++-mono (untold (there i) b) (untold (there i) b) (λ m → m) (sub refl refl refl)
      src-told i rp (just x) rt (just c) nothing   (just b) rv sub en e₀   e′   = just≢ (en e₀ refl)
      src-told i rp nothing  rt (just c) nothing   (just b) rv sub en e₀   ()
      src-told i rp e        rt nothing  (just c′) (just b) rv sub en e₀   e′   = false≢ (rv refl)
      src-told i rp (just x) rt nothing  nothing   (just b) rv sub en refl refl = λ m → m
      src-told i rp nothing  rt nothing  nothing   (just b) rv sub en ()   e′

      -- The body replanted: its joiners read one frame down, through a
      -- shut when the source has ended.
      body-told : ∀ {Δ A B C} (i : C ∈ᴸ Δ) rp (e : Maybe Pos) (rt : U.Node Δ A) (s : Maybe (U.Node Δ A)) (mb mb′ : Maybe (U.Node (A ∷ Δ) B))
                → (is-just mb′ ≡ true → is-just mb ≡ true)
                → ((is-just s ∨ is-just e) ≡ true → ∀ {c c′} → mb ≡ just c → mb′ ≡ just c′ → untold (there i) c′ ⊆ᴾ untold (there i) c)
                → ∀ {b₀ b′} → At.connected H rp e rt s mb ≡ just b₀ → At.connected H′ rp e rt s mb′ ≡ just b′ → untold i b′ ⊆ᴾ untold i b₀
      body-told i rp e        rt s        mb       nothing   rv sub e₀   ()
      body-told i rp e        rt s        nothing  (just b′) rv sub e₀   e′   = false≢ (rv refl)
      body-told i rp e        rt (just c) (just b) (just b′) rv sub refl refl = ++-mono (untold (there i) b) (untold (there i) b′) (sub refl refl refl) (λ m → m)
      body-told i rp (just x) rt nothing  (just b) (just b′) rv sub refl refl =
        ++-mono (untold (there i) (U.shut (here refl) x b)) (untold (there i) (U.shut (here refl) x b′))
          (λ m → ≡-⊆ (sym (untold-shut i x b)) (sub refl refl refl (≡-⊆ (untold-shut i x b′) m))) (λ m → m)
      body-told i rp nothing  rt nothing  (just b) (just b′) rv sub ()   e′

      mutual
        told : ∀ {Δ A} {t : Sub h Δ A} (π : Path t u) → AllPairs _≢_ (names t) → Ended H t
             → ∀ {C} (i : C ∈ᴸ Δ) {b₀ b′} → At.part H t ≡ just b₀ → At.part H′ (plant π v) ≡ just b′ → untold i b′ ⊆ᴾ untold i b₀
        told here ps en i e₀ e′ = tl₀ i e₀ e′
        told (in-map {f = f} {t = s} π) ps en i e₀ e′ =
          told-ᴹ i (U.mapᶜ f) (U.mapᶜ f) (λ _ → refl) (λ _ → refl) (At.part H s) (At.part H′ (plant π v)) e₀ e′
            (told π ps (en-sub H en (in-map here) refl) i)
        told (in-scan {f = f} {r} {t = s} π) ps en i e₀ e′ =
          told-ᴹ i (U.scanᶜ f (At.val H r)) (U.scanᶜ f (At.val H′ r)) (λ _ → refl) (λ _ → refl) (At.part H s) (At.part H′ (plant π v)) e₀ e′
            (told π (pairs-tl ps) (en-sub H en (in-scan here) refl) i)
        told (in-take {i = ib} {p} {c} {k} {tk} {t = s} π) ps en i e₀ e′ =
          told-take i ib p tk (At.part H s) (At.part H′ (plant π v)) Tk.live′ e₀ e′
            (λ ok → told π Tk.fresh (en-sub H en (in-take here) (seen-take (At.val H (Kit.live c)) ok)) i)
          where module Tk = Take c k π ps
        told (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} {ls} π) ps en i e₀ e′ =
          flat-told i op (λ a q → U.subscribe (f a) q) (At.part H so) (At.part H′ (plant π v)) (At.partLanes H ls) (At.partLanes H′ ls)
            (At.val H (Flat.queue fl)) (At.val H′ (Flat.queue fl)) pl
            (toldᴹ i (At.part H so) (At.part H′ (plant π v)) (told π O.fresh (en-sub H en (in-outer here) refl) i) (revive π O.fresh))
            (≡-⊆ (cong (untoldᴸ i) O.lanes)) (cong lower O.queue) e₀ e′
          where module O = Outer fl oc k r ls π ps
        told (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} {ls} πL) ps en i e₀ e′ =
          flat-told i op (λ a q → U.subscribe (f a) q) (At.part H so) (At.part H′ so) (At.partLanes H ls) (At.partLanes H′ (plantᴸ πL v))
            (At.val H (Flat.queue fl)) (At.val H′ (Flat.queue fl)) pl
            (≡-⊆ (cong (untoldᴹ i) Ln.outer)) (toldL πL Ln.fresh (enL-of H en) i) (cong lower Ln.queue) e₀ e′
          where module Ln = Lanes fl oc k r so πL ps
        told (in-source {S = S} {c} {b} {kb} {k} {e = e} {rp} {rt} {t = src} {bd} π) ps en i {b′ = b′} e₀ e′ =
          src-told i rp e rt (At.part H src) (At.part H′ (plant π v)) (At.part H bd) (revive π Sr.fresh)
            (λ jb → told π Sr.fresh (en-sub H en (in-source here) (∧-join jb refl)) i) (en here refl) e₀
            (subst (λ z → At.connected H′ rp e rt (At.part H′ (plant π v)) z ≡ just b′) Sr.body e′)
          where module Sr = Source S c b kb k bd π ps
        told (in-body {S = S} {c} {b} {kb} {k} {e = e} {rp} {rt} {t = src} {bd} π) ps en i {b′ = b′} e₀ e′ =
          body-told i rp e rt (At.part H src) (At.part H bd) (At.part H′ (plant π v)) (revive π Bd.fresh)
            (λ js → told π Bd.fresh (en-sub H en (in-body here) (∧-join js refl)) (there i)) e₀
            (subst (λ z → At.connected H′ rp e rt z (At.part H′ (plant π v)) ≡ just b′) Bd.source e′)
          where module Bd = Body S c b kb k src π ps
        told (in-defer {k = k} π) ps en i e₀ e′ = told π (pairs-r (quietName k) ps) (en-sub H en (in-defer here) refl) i e₀ e′

        toldL : ∀ {Δ B} {ls : List (Lane h Δ B)} (πL : PathLanes ls u) → AllPairs _≢_ (laneNames ls) → EndedL H ls
              → ∀ {C} (i : C ∈ᴸ Δ) → untoldᴸ i (At.partLanes H′ (plantᴸ πL v)) ⊆ᴾ untoldᴸ i (At.partLanes H ls)
        toldL (this-lane {c = c} {k} {t = s} {ls} π) ps en i =
          lane-told i Th.live′ (At.part H s) (At.part H′ (plant π v)) (At.partLanes H ls) (At.partLanes H′ ls)
            (λ lv → toldᴹ i (At.part H s) (At.part H′ (plant π v)) (told π Th.fresh (enL-head H en lv) i) (revive π Th.fresh))
            (≡-⊆ (cong (untoldᴸ i) Th.rest))
          where module Th = This c k ls π ps
        toldL (next-lane {l = lane c k s} {ls} πL) ps en i =
          lane-told i Nx.live′ (At.part H s) (At.part H′ s) (At.partLanes H ls) (At.partLanes H′ (plantᴸ πL v))
            (λ _ → ≡-⊆ (cong (untoldᴹ i) Nx.head)) (toldL πL Nx.fresh (enL-tail H en) i)
          where module Nx = Next c k s πL ps

    --------------------------------------------------------------------
    -- NO HEAD BEFORE `q`: every node above heads no sooner after the
    -- write than before.

    module Behind (tl₀ : ∀ {C} (i : C ∈ᴸ Δ₀) {b₀ b′} → At.part H u ≡ just b₀ → At.part H′ v ≡ just b′ → untold i b′ ⊆ᴾ untold i b₀)
                  (q : Pos) (bl₀ : Each H (Heads q) u → Each H′ (Heads q) v) where
      open Telling tl₀

      P : ∀ {Γ A} → U.Node Γ A → Set
      P c = Heads q c

      module BH = Build H′ P

      lift-ᴹ : ∀ {Δ A B} (G : Heapᴹ h) (g : U.Node Δ A → U.Node Δ B) (m : Maybe (U.Node Δ A)) → (∀ c → P c → P (g c))
             → (∀ {c} → m ≡ just c → P c) → ∀ {c} → At.mapᴹ G g m ≡ just c → P c
      lift-ᴹ G g (just c) up hm refl = up c (hm refl)
      lift-ᴹ G g nothing  up hm ()

      take-up : ∀ {Δ A} ib (p : A → Bool) (tk : Taking Δ A) (m m′ : Maybe (U.Node Δ A)) {b b′} → b′ ≡ b
              → (∀ {c} → (if b then At.taking? H ib p tk m else nothing) ≡ just c → P c)
              → (b ∧ isTaking tk ≡ true → ∀ {c} → m′ ≡ just c → P c)
              → ∀ {c} → (if b′ then At.taking? H′ ib p tk m′ else nothing) ≡ just c → P c
      take-up ib p tk           m m′        {b = false} refl old up ()
      take-up ib p taking       m (just c′) {b = true}  refl old up refl = heads-take ib p {c′} (up refl refl)
      take-up ib p taking       m nothing   {b = true}  refl old up ()
      take-up ib p (ending _ _) m m′        {b = true}  refl old up refl = old refl
      take-up ib p taken        m m′        {b = true}  refl old up ()

      root-flat : ∀ {Δ A B} op (g : A → Pos → U.Node Δ B) (o o′ : Maybe (U.Node Δ A)) (L L′ : List (U.Node Δ B)) (Q Q′ : List A) pl → Q′ ≡ Q
                → (∀ {c} → At.merged H op g o L Q pl ≡ just c → P c)
                → (is-just (At.merged H′ op g o′ L′ Q′ pl) ≡ true → is-just (At.merged H op g o L Q pl) ≡ true)
                → (∀ {c} → o′ ≡ just c → P c) → All P L′
                → ∀ {c} → At.merged H′ op g o′ L′ Q′ pl ≡ just c → P c
      root-flat op g o o′ L L′ Q _ pl refl old rv ho hL {c} x = go (proj₂ (just-of (rv (cong is-just x))))
        where
          go : ∀ {b₀} → At.merged H op g o L Q pl ≡ just b₀ → P c
          go x₀ = subst P (merged-eq H′ op g o′ L′ Q pl x) (heads-flat op g o o′ L L′ Q pl (subst P (sym (merged-eq H op g o L Q pl x₀)) (old x₀)) ho hL)

      -- The source replanted: a source running on either side heads
      -- the connect beside its body; past the end, nothing moved.
      src-up : ∀ {Δ A B} rp (e : Maybe Pos) (rt : U.Node Δ A) (s s′ : Maybe (U.Node Δ A)) (mb : Maybe (U.Node (A ∷ Δ) B))
             → (∀ {c} → At.connected H rp e rt s mb ≡ just c → P c)
             → (∀ {n} → At.connected H rp e rt s mb ≡ just n → ∀ {c₀} → e ≡ just c₀ → s ≡ nothing)
             → (is-just s′ ≡ true → is-just s ≡ true)
             → (is-just mb ≡ true → ∀ {c} → s′ ≡ just c → P c)
             → ((is-just s ∨ is-just e) ≡ true → ∀ {c} → mb ≡ just c → P c)
             → ∀ {c} → At.connected H′ rp e rt s′ mb ≡ just c → P c
      src-up rp e        rt s        s′        nothing  old en rv hs hb ()
      src-up rp e        rt s        (just c′) (just b) old en rv hs hb refl = heads-source rp {b} {c′} (hs refl refl) (hb (∨-l (rv refl)) refl)
      src-up rp (just x) rt (just c) nothing   (just b) old en rv hs hb _    = just≢ (en refl refl)
      src-up rp (just x) rt nothing  nothing   (just b) old en rv hs hb refl = old refl
      src-up rp nothing  rt s        nothing   (just b) old en rv hs hb ()

      -- The body replanted: past the source's end the new body heads
      -- through a shut, telling only what the old body left untold.
      body-up : ∀ {Δ A B} rp (e : Maybe Pos) (rt : U.Node Δ A) (s : Maybe (U.Node Δ A)) (mb mb′ : Maybe (U.Node (A ∷ Δ) B))
              → (is-just mb′ ≡ true → is-just mb ≡ true)
              → (is-just mb ≡ true → ∀ {c} → s ≡ just c → P c)
              → ((is-just s ∨ is-just e) ≡ true → ∀ {c} → mb′ ≡ just c → P c)
              → ((is-just s ∨ is-just e) ≡ true → ∀ {b₀ b′} → mb ≡ just b₀ → mb′ ≡ just b′ → untold (here refl) b′ ⊆ᴾ untold (here refl) b₀)
              → (∀ {c₀} → e ≡ just c₀ → s ≡ nothing → ∀ {b₀} → mb ≡ just b₀ → Tells q c₀ (untold (here refl) b₀))
              → (∀ {n} → At.connected H rp e rt s mb ≡ just n → s ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt)
              → ∀ {c} → At.connected H′ rp e rt s mb′ ≡ just c → P c
      body-up rp e         rt s        mb        nothing   rv hs hb tl ut hr ()
      body-up rp e         rt (just c) mb        (just b′) rv hs hb tl ut hr refl = heads-source rp {b′} {c} (hs (rv refl) refl) (hb refl refl)
      body-up rp (just c₀) rt nothing  nothing   (just b′) rv hs hb tl ut hr _    = false≢ (rv refl)
      body-up rp (just c₀) rt nothing  (just b₀) (just b′) rv hs hb tl ut hr refl =
        ended-head rp c₀ (U.shut (here refl) c₀ b′) rt (U.step rt)
          (shut-heads (here refl) c₀ b′ (hb refl refl) (narrow (tl refl refl refl) (ut refl refl refl))) (hr refl refl refl)
      body-up rp nothing   rt nothing  mb        (just b′) rv hs hb tl ut hr ()

      mutual
        shiftE : ∀ {Δ A} {t : Sub h Δ A} (π : Path t u) → AllPairs _≢_ (names t) → Each H P t → Untold H q t → Ended H t → Each H′ P (plant π v)
        shiftE here ps ev ut en = bl₀ ev
        shiftE (in-map {f = f} {t = s} π) ps ev ut en =
          BH.each-map (lift-ᴹ H′ (U.mapᶜ f) (At.part H′ (plant π v)) (λ c → heads-map f {c}) (Each.parts es here refl)) es
          where
            es : Each H′ P (plant π v)
            es = shiftE π ps (each-sub ev (in-map here) refl) (ut-sub H ut (in-map here) refl) (en-sub H en (in-map here) refl)
        shiftE (in-scan {f = f} {r} {t = s} π) ps ev ut en =
          BH.each-scan (lift-ᴹ H′ (U.scanᶜ f (At.val H′ r)) (At.part H′ (plant π v)) (λ c → heads-scan f (At.val H′ r) {c}) (Each.parts es here refl)) es
          where
            es : Each H′ P (plant π v)
            es = shiftE π (pairs-tl ps) (each-sub ev (in-scan here) refl) (ut-sub H ut (in-scan here) refl) (en-sub H en (in-scan here) refl)
        shiftE (in-take {i = ib} {p} {c} {k} {tk} {t = s} π) ps ev ut en =
          BH.each-take root (λ ok → sh (via-≡ (λ z → z ∧ isTaking tk) Tk.live′ ok))
          where
            module Tk = Take c k π ps
            sh : At.val H (Kit.live c) ∧ isTaking tk ≡ true → Each H′ P (plant π v)
            sh ok = shiftE π Tk.fresh (each-sub ev (in-take here) sk) (ut-sub H ut (in-take here) sk) (en-sub H en (in-take here) sk)
              where
                sk : At.val H (Kit.live c) ∧ isTaking tk ∧ true ≡ true
                sk = seen-take (At.val H (Kit.live c)) ok
            root : ∀ {n} → At.part H′ (takeWhileˢ ib p c k tk (plant π v)) ≡ just n → P n
            root = take-up ib p tk (At.part H s) (At.part H′ (plant π v)) Tk.live′ (Each.parts ev here refl) (λ ok → Each.parts (sh ok) here refl)
        shiftE (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} {ls} π) ps ev ut en =
          BH.each-flat root pool eo eL
          where
            module O = Outer fl oc k r ls π ps
            eo : Each H′ P (plant π v)
            eo = shiftE π O.fresh (each-sub ev (in-outer here) refl) (ut-sub H ut (in-outer here) refl) (en-sub H en (in-outer here) refl)
            eL : EachL H′ P ls
            eL = eachL-alike H H′ O.lanesA (eachL-of H ev)
            pool : ∀ {n} → At.part H′ (flatMapˢ op f fl oc k r pl (plant π v) ls) ≡ just n → P pl
            pool x = held (in-outer {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {ls = ls} π) ps x (Each.pools ev here refl)
            root : ∀ {n} → At.part H′ (flatMapˢ op f fl oc k r pl (plant π v) ls) ≡ just n → P n
            root = root-flat op (λ a q′ → U.subscribe (f a) q′) (At.part H so) (At.part H′ (plant π v)) (At.partLanes H ls) (At.partLanes H′ ls)
                     (At.val H (Flat.queue fl)) (At.val H′ (Flat.queue fl)) pl (cong lower O.queue) (Each.parts ev here refl) (revive (in-outer {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {ls = ls} π) ps)
                     (Each.parts eo here refl) (each-lanes {H = H′} {P = P} ls (λ πL sn e → EachL.partsL eL πL sn e))
        shiftE (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} {ls} πL) ps ev ut en =
          BH.each-flat root pool eo eL
          where
            module Ln = Lanes fl oc k r so πL ps
            eo : Each H′ P so
            eo = each-alike H H′ Ln.soA (each-sub ev (in-outer here) refl)
            eL : EachL H′ P (plantᴸ πL v)
            eL = shiftL πL Ln.fresh (eachL-of H ev) (utL-of H ut) (enL-of H en)
            pool : ∀ {n} → At.part H′ (flatMapˢ op f fl oc k r pl so (plantᴸ πL v)) ≡ just n → P pl
            pool x = held (in-lanes {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {t = so} πL) ps x (Each.pools ev here refl)
            root : ∀ {n} → At.part H′ (flatMapˢ op f fl oc k r pl so (plantᴸ πL v)) ≡ just n → P n
            root = root-flat op (λ a q′ → U.subscribe (f a) q′) (At.part H so) (At.part H′ so) (At.partLanes H ls) (At.partLanes H′ (plantᴸ πL v))
                     (At.val H (Flat.queue fl)) (At.val H′ (Flat.queue fl)) pl (cong lower Ln.queue) (Each.parts ev here refl) (revive (in-lanes {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {t = so} πL) ps)
                     (Each.parts eo here refl) (each-lanes {H = H′} {P = P} (plantᴸ πL v) (λ πL′ sn e → EachL.partsL eL πL′ sn e))
        shiftE (in-source {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = src} {bd} π) ps ev ut en =
          BH.each-connect root rest es eb
          where
            module Sr = Source S c b kb k bd π ps
            es : is-just (At.part H′ bd) ≡ true → Each H′ P (plant π v)
            es jb = shiftE π Sr.fresh (each-sub ev (in-source here) s₁) (ut-sub H ut (in-source here) s₁) (en-sub H en (in-source here) s₁)
              where
                s₁ : is-just (At.part H bd) ∧ true ≡ true
                s₁ = ∧-join (via-≡ is-just Sr.body jb) refl
            eb : (is-just (At.part H′ (plant π v)) ∨ is-just e) ≡ true → Each H′ P bd
            eb js = each-alike H H′ Sr.bdA (each-sub ev (in-body here) (∧-join (∨-mono (is-just e) (revive π Sr.fresh) js) refl))
            rest : ∀ {n} → At.part H′ (connectˢ S c b kb k fd rp e rt (plant π v) bd) ≡ just n → At.part H′ (plant π v) ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt
            rest x _ pe = held (in-source {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {e = e} {rp = rp} {rt = rt} {bd = bd} π) ps x (λ x₀ → Each.rests ev here refl x₀ (en here refl x₀ pe) pe)
            root : ∀ {n} → At.part H′ (connectˢ S c b kb k fd rp e rt (plant π v) bd) ≡ just n → P n
            root {n} x =
              src-up rp e rt (At.part H src) (At.part H′ (plant π v)) (At.part H bd) (Each.parts ev here refl) (en here refl) (revive π Sr.fresh)
                (λ jb → Each.parts (es (via-≡ is-just (sym Sr.body) jb)) here refl) (λ j → Each.parts ev (in-body here) (∧-join j refl))
                (subst (λ z → At.connected H′ rp e rt (At.part H′ (plant π v)) z ≡ just n) Sr.body x)
        shiftE (in-body {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = src} {bd} π) ps ev ut en =
          BH.each-connect root rest es eb
          where
            module Bd = Body S c b kb k src π ps
            sb : (is-just (At.part H src) ∨ is-just e) ≡ true → (is-just (At.part H src) ∨ is-just e) ∧ true ≡ true
            sb js = ∧-join js refl
            eb : (is-just (At.part H′ src) ∨ is-just e) ≡ true → Each H′ P (plant π v)
            eb js = shiftE π Bd.fresh (each-sub ev (in-body here) (sb js′)) (ut-sub H ut (in-body here) (sb js′)) (en-sub H en (in-body here) (sb js′))
              where
                js′ : (is-just (At.part H src) ∨ is-just e) ≡ true
                js′ = ∨-mono (is-just e) (via-≡ is-just Bd.source) js
            es : is-just (At.part H′ (plant π v)) ≡ true → Each H′ P src
            es jb = each-alike H H′ Bd.srcA (each-sub ev (in-source here) (∧-join (revive π Bd.fresh jb) refl))
            rest : ∀ {n} → At.part H′ (connectˢ S c b kb k fd rp e rt src (plant π v)) ≡ just n → At.part H′ src ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt
            rest x pn pe = held (in-body {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {e = e} {rp = rp} {rt = rt} {t = src} π) ps x (λ x₀ → Each.rests ev here refl x₀ (trans (sym Bd.source) pn) pe)
            root : ∀ {n} → At.part H′ (connectˢ S c b kb k fd rp e rt src (plant π v)) ≡ just n → P n
            root {n} x =
              body-up rp e rt (At.part H src) (At.part H bd) (At.part H′ (plant π v)) (revive π Bd.fresh)
                (λ jb → Each.parts ev (in-source here) (∧-join jb refl))
                (λ js → Each.parts (eb (∨-mono (is-just e) (via-≡ is-just (sym Bd.source)) js)) here refl)
                (λ js → told π Bd.fresh (en-sub H en (in-body here) (sb js)) (here refl))
                (untold-at ut here refl) (Each.rests ev here refl)
                (subst (λ z → At.connected H′ rp e rt z (At.part H′ (plant π v)) ≡ just n) Bd.source x)
        shiftE (in-defer {k = k} π) ps ev ut en =
          BH.each-defer (Each.parts es here refl) es
          where
            es : Each H′ P (plant π v)
            es = shiftE π (pairs-r (quietName k) ps) (each-sub ev (in-defer here) refl) (ut-sub H ut (in-defer here) refl) (en-sub H en (in-defer here) refl)

        shiftL : ∀ {Δ B} {ls : List (Lane h Δ B)} (πL : PathLanes ls u) → AllPairs _≢_ (laneNames ls) → EachL H P ls → UntoldL H q ls → EndedL H ls
               → EachL H′ P (plantᴸ πL v)
        shiftL (this-lane {c = c} {k} {t = s} {ls} π) ps eL ut en =
          BH.eachL-cons (λ lv → shiftE π Th.fresh (eachL-head H eL (Th.on lv)) (utL-head H ut (Th.on lv)) (enL-head H en (Th.on lv)))
                        (eachL-alike H H′ Th.restA (eachL-tail H eL))
          where module Th = This c k ls π ps
        shiftL (next-lane {l = lane c k s} {ls} πL) ps eL ut en =
          BH.eachL-cons (λ lv → each-alike H H′ Nx.headA (eachL-head H eL (Nx.on lv)))
                        (shiftL πL Nx.fresh (eachL-tail H eL) (utL-tail H ut) (enL-tail H en))
          where module Nx = Next c k s πL ps

    --------------------------------------------------------------------
    -- WHAT LINGERS, TIED: every pool and every ended source's rest above
    -- the write is tied after it as before.

    module Ties (rs₀ : ∀ {C} → Pinned (U.restˢ {B = ⊤} (At.leftover H {B = C} u)) (U.restˢ {B = ⊤} (At.leftover H′ {B = C} v)))
                (lb₀ : Lingers H u → Lingers H′ v) where
      module LG = Linger H′

      -- A connect's leftover over a source running on either side: the
      -- source's own leftover pinned alike, the body's leftover alike.
      postulate
        rest-sourced : ∀ {Δ A B} {src : Sub h Δ A} (π : Path src u) rp {x x′ : U.Node (A ∷ Δ) ⊤}
                     → (is-just (At.part H src) ∨ is-just (At.part H′ (plant π v))) ≡ true
                     → Pinned (U.restˢ {B = ⊤} (At.leftover H {B = A} src)) (U.restˢ {B = ⊤} (At.leftover H′ {B = A} (plant π v)))
                     → x′ ≡ x
                     → Pinned (U.restˢ {B = ⊤} (U.unionᶜ {B = B} (U.burstingᶜ rp (At.sourced H (At.part H src) (At.leftover H src)))
                                                                (U.underᶜ (U.live (At.sourced H (At.part H src) (At.leftover H src))) x)))
                              (U.restˢ {B = ⊤} (U.unionᶜ {B = B} (U.burstingᶜ rp (At.sourced H′ (At.part H′ (plant π v)) (At.leftover H′ (plant π v))))
                                                                (U.underᶜ (U.live (At.sourced H′ (At.part H′ (plant π v)) (At.leftover H′ (plant π v)))) x′)))

      src-rested : ∀ {Δ A B} {src : Sub h Δ A} (π : Path src u) rp {x x′ : U.Node (A ∷ Δ) ⊤}
                 → Pinned (U.restˢ {B = ⊤} (At.leftover H {B = A} src)) (U.restˢ {B = ⊤} (At.leftover H′ {B = A} (plant π v)))
                 → x′ ≡ x → (s s′ : Maybe (U.Node Δ A)) → At.part H src ≡ s → At.part H′ (plant π v) ≡ s′
                 → Pinned (U.restˢ {B = ⊤} (U.unionᶜ {B = B} (U.burstingᶜ rp (At.sourced H (At.part H src) (At.leftover H src)))
                                                            (U.underᶜ (U.live (At.sourced H (At.part H src) (At.leftover H src))) x)))
                          (U.restˢ {B = ⊤} (U.unionᶜ {B = B} (U.burstingᶜ rp (At.sourced H′ (At.part H′ (plant π v)) (At.leftover H′ (plant π v))))
                                                            (U.underᶜ (U.live (At.sourced H′ (At.part H′ (plant π v)) (At.leftover H′ (plant π v)))) x′)))
      src-rested {src = src} π rp up lb nothing nothing p p′ rewrite p | p′ =
        union-pinned (bursts-moved rp stepped up) (under-moved (U.live (At.leftover H src)) (U.live (At.leftover H′ (plant π v))) (pin-alike lb))
        where
          stepped : Pinned (U.step (At.leftover H src)) (U.step (At.leftover H′ (plant π v)))
          stepped = pinned-trans (restful-pinned (leftover-restful H src))
                      (pinned-trans (rest-pinned (At.leftover H src))
                        (pinned-trans up
                          (pinned-trans (rest-pinned (At.leftover H′ (plant π v)))
                            (pinned-sym (restful-pinned (leftover-restful H′ (plant π v)))))))
      src-rested π rp up lb (just _) s′       p p′ = rest-sourced π rp (∨-l (cong is-just p)) up lb
      src-rested {src = src} π rp up lb nothing (just _) p p′ = rest-sourced π rp (∨-r (is-just (At.part H src)) (cong is-just p′)) up lb

      mutual
        restedUp : ∀ {Δ A} {t : Sub h Δ A} (π : Path t u) → AllPairs _≢_ (names t)
                 → ∀ {C} → Pinned (U.restˢ {B = ⊤} (At.leftover H {B = C} t)) (U.restˢ {B = ⊤} (At.leftover H′ {B = C} (plant π v)))
        restedUp here ps = rs₀
        restedUp (in-map π) ps = restedUp π ps
        restedUp (in-scan π) ps = restedUp π (pairs-tl ps)
        restedUp (in-take {c = c} {k} π) ps = restedUp π (Take.fresh c k π ps)
        restedUp (in-outer {fl = fl} {oc} {k} {r} {ls = ls} π) ps =
          union-pinned (restedUp π O.fresh) (pin-alike (leftoverL-alike H H′ ls O.lanesA))
          where module O = Outer fl oc k r ls π ps
        restedUp (in-lanes {fl = fl} {oc} {k} {r} {t = so} πL) ps =
          union-pinned (pin-alike (leftover-alike H H′ so Ln.soA)) (restedUpL πL Ln.fresh)
          where module Ln = Lanes fl oc k r so πL ps
        restedUp (in-source {S = S} {c} {b} {kb} {k} {rp = rp} {t = src} {bd} π) ps =
          src-rested π rp (restedUp π Sr.fresh) (leftover-alike H H′ bd Sr.bdA) (At.part H src) (At.part H′ (plant π v)) refl refl
          where module Sr = Source S c b kb k bd π ps
        restedUp (in-body {S = S} {c} {b} {kb} {k} {rp = rp} {t = src} {bd} π) ps =
          conn-pin rp (At.sourced H (At.part H src) (At.leftover H src)) (At.sourced H′ (At.part H′ src) (At.leftover H′ src))
            (trans (sourced-heap H H′ (At.part H′ src) (At.leftover H′ src)) (cong₂ (At.sourced H) Bd.source (leftover-alike H H′ src Bd.srcA)))
            (restedUp π Bd.fresh)
          where module Bd = Body S c b kb k src π ps
        restedUp (in-defer {k = k} π) ps = restedUp π (pairs-r (quietName k) ps)

        restedUpL : ∀ {Δ B} {ls : List (Lane h Δ B)} (πL : PathLanes ls u) → AllPairs _≢_ (laneNames ls)
                  → ∀ {C} → Pinned (U.restˢ {B = ⊤} (At.leftoverL H {B = C} ls)) (U.restˢ {B = ⊤} (At.leftoverL H′ {B = C} (plantᴸ πL v)))
        restedUpL (this-lane {c = c} {k} {t = s} {ls} π) ps =
          union-pinned (restedUp π Th.fresh) (pin-alike (leftoverL-alike H H′ ls Th.restA))
          where module Th = This c k ls π ps
        restedUpL (next-lane {l = lane c k s} {ls} πL) ps =
          union-pinned (pin-alike (leftover-alike H H′ s Nx.headA)) (restedUpL πL Nx.fresh)
          where module Nx = Next c k s πL ps

      pooledUpL : ∀ {Δ B} {ls : List (Lane h Δ B)} (πL : PathLanes ls u) → AllPairs _≢_ (laneNames ls)
                → ∀ {C} → Pinned (U.restˢ {B = ⊤} (At.pooledL H {B = C} ls)) (U.restˢ {B = ⊤} (At.pooledL H′ {B = C} (plantᴸ πL v)))
      pooledUpL (this-lane {c = c} {k} {t = s} {ls} π) ps =
        if-moved Th.live′ (pin-alike (pooledL-alike H H′ ls Th.restA)) (union-pinned (restedUp π Th.fresh) (pin-alike (pooledL-alike H H′ ls Th.restA)))
        where module Th = This c k ls π ps
      pooledUpL (next-lane {l = lane c k s} {ls} πL) ps =
        if-moved Nx.live′ (pooledUpL πL Nx.fresh) (union-pinned (pin-alike (leftover-alike H H′ s Nx.headA)) (pooledUpL πL Nx.fresh))
        where module Nx = Next c k s πL ps

      mutual
        shiftLg : ∀ {Δ A} {t : Sub h Δ A} (π : Path t u) → AllPairs _≢_ (names t) → Lingers H t → Ended H t → Lingers H′ (plant π v)
        shiftLg here ps lg en = lb₀ lg
        shiftLg (in-map π) ps lg en = LG.lg-map (shiftLg π ps (lingers-sub H lg (in-map here) refl) (en-sub H en (in-map here) refl))
        shiftLg (in-scan π) ps lg en = LG.lg-scan (shiftLg π (pairs-tl ps) (lingers-sub H lg (in-scan here) refl) (en-sub H en (in-scan here) refl))
        shiftLg (in-take {c = c} {k} {tk} π) ps lg en =
          LG.lg-take (λ ok → sh (via-≡ (λ z → z ∧ isTaking tk) Tk.live′ ok))
          where
            module Tk = Take c k π ps
            sh : At.val H (Kit.live c) ∧ isTaking tk ≡ true → Lingers H′ (plant π v)
            sh ok = shiftLg π Tk.fresh (lingers-sub H lg (in-take here) sk) (en-sub H en (in-take here) sk)
              where
                sk : At.val H (Kit.live c) ∧ isTaking tk ∧ true ≡ true
                sk = seen-take (At.val H (Kit.live c)) ok
        shiftLg (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} {ls} π) ps lg en =
          LG.lg-flat pool (shiftLg π O.fresh (lingers-sub H lg (in-outer here) refl) (en-sub H en (in-outer here) refl))
            (lingersL-alike H H′ O.lanesA (lingersL-of H lg))
          where
            module O = Outer fl oc k r ls π ps
            pool : ∀ {n} → At.part H′ (flatMapˢ op f fl oc k r pl (plant π v) ls) ≡ just n → Tied pl (At.pooled H′ fl (plant π v) ls)
            pool x = held (in-outer {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {ls = ls} π) ps x (λ x₀ → pinned-trans (Lingers.pools lg here refl x₀)
                       (union-pinned (if-moved {y = U.idleᶜ} {y′ = U.idleᶜ} (cong lower O.done) (restedUp π O.fresh) (pin-alike refl)) (pin-alike (pooledL-alike H H′ ls O.lanesA))))
        shiftLg (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} {ls} πL) ps lg en =
          LG.lg-flat pool (lingers-alike H H′ Ln.soA (lingers-sub H lg (in-outer here) refl)) (shiftLgL πL Ln.fresh (lingersL-of H lg) (enL-of H en))
          where
            module Ln = Lanes fl oc k r so πL ps
            pool : ∀ {n} → At.part H′ (flatMapˢ op f fl oc k r pl so (plantᴸ πL v)) ≡ just n → Tied pl (At.pooled H′ fl so (plantᴸ πL v))
            pool x = held (in-lanes {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {t = so} πL) ps x (λ x₀ → pinned-trans (Lingers.pools lg here refl x₀)
                       (union-pinned (if-moved {y = U.idleᶜ} {y′ = U.idleᶜ} (cong lower Ln.done) (pin-alike (leftover-alike H H′ so Ln.soA)) (pin-alike refl)) (pooledUpL πL Ln.fresh)))
        shiftLg (in-source {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = src} {bd} π) ps lg en =
          LG.lg-connect rest ls lb
          where
            module Sr = Source S c b kb k bd π ps
            ls : is-just (At.part H′ bd) ≡ true → Lingers H′ (plant π v)
            ls jb = shiftLg π Sr.fresh (lingers-sub H lg (in-source here) s₁) (en-sub H en (in-source here) s₁)
              where
                s₁ : is-just (At.part H bd) ∧ true ≡ true
                s₁ = ∧-join (via-≡ is-just Sr.body jb) refl
            lb : (is-just (At.part H′ (plant π v)) ∨ is-just e) ≡ true → Lingers H′ bd
            lb js = lingers-alike H H′ Sr.bdA (lingers-sub H lg (in-body here) (∧-join (∨-mono (is-just e) (revive π Sr.fresh) js) refl))
            rest : ∀ {n} → At.part H′ (connectˢ S c b kb k fd rp e rt (plant π v) bd) ≡ just n → At.part H′ (plant π v) ≡ nothing
                 → ∀ {c₀} → e ≡ just c₀ → Tied rt (At.leftover H′ {B = ⊤} (plant π v))
            rest x _ pe = held (in-source {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {e = e} {rp = rp} {rt = rt} {bd = bd} π) ps x (λ x₀ → pinned-trans (Lingers.rests lg here refl x₀ (en here refl x₀ pe) pe) (restedUp π Sr.fresh))
        shiftLg (in-body {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = src} {bd} π) ps lg en =
          LG.lg-connect rest ls lb
          where
            module Bd = Body S c b kb k src π ps
            ls : is-just (At.part H′ (plant π v)) ≡ true → Lingers H′ src
            ls jb = lingers-alike H H′ Bd.srcA (lingers-sub H lg (in-source here) (∧-join (revive π Bd.fresh jb) refl))
            lb : (is-just (At.part H′ src) ∨ is-just e) ≡ true → Lingers H′ (plant π v)
            lb js = shiftLg π Bd.fresh (lingers-sub H lg (in-body here) sb) (en-sub H en (in-body here) sb)
              where
                sb : (is-just (At.part H src) ∨ is-just e) ∧ true ≡ true
                sb = ∧-join (∨-mono (is-just e) (via-≡ is-just Bd.source) js) refl
            rest : ∀ {n} → At.part H′ (connectˢ S c b kb k fd rp e rt src (plant π v)) ≡ just n → At.part H′ src ≡ nothing
                 → ∀ {c₀} → e ≡ just c₀ → Tied rt (At.leftover H′ {B = ⊤} src)
            rest x pn pe = held (in-body {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {e = e} {rp = rp} {rt = rt} {t = src} π) ps x (λ x₀ → pinned-trans (Lingers.rests lg here refl x₀ (trans (sym Bd.source) pn) pe)
                             (pin-alike (leftover-alike H H′ src Bd.srcA)))
        shiftLg (in-defer {k = k} π) ps lg en =
          LG.lg-defer (shiftLg π (pairs-r (quietName k) ps) (lingers-sub H lg (in-defer here) refl) (en-sub H en (in-defer here) refl))

        shiftLgL : ∀ {Δ B} {ls : List (Lane h Δ B)} (πL : PathLanes ls u) → AllPairs _≢_ (laneNames ls) → LingersL H ls → EndedL H ls
                 → LingersL H′ (plantᴸ πL v)
        shiftLgL (this-lane {c = c} {k} {t = s} {ls} π) ps lL en =
          LG.lgL-cons (λ lv → shiftLg π Th.fresh (lingersL-head H lL (Th.on lv)) (enL-head H en (Th.on lv)))
                      (lingersL-alike H H′ Th.restA (lingersL-tail H lL))
          where module Th = This c k ls π ps
        shiftLgL (next-lane {l = lane c k s} {ls} πL) ps lL en =
          LG.lgL-cons (λ lv → lingers-alike H H′ Nx.headA (lingersL-head H lL (Nx.on lv))) (shiftLgL πL Nx.fresh (lingersL-tail H lL) (enL-tail H en))
          where module Nx = Next c k s πL ps
