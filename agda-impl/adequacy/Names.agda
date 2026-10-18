{-# OPTIONS --guardedness #-}

-- Names weakened and planted, the fresh frame, and observers read alike
-- part for part.
module adequacy.Names where

open import Data.List using (List; []; _∷_; _++_; [_]; length; null) renaming (map to mapᴸ)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (tabulate to tabulateᴬ; lookup to lookupᴬ; map to all-map)
open import Data.List.Relation.Unary.Any using () renaming (here to hereᴬ; there to thereᴬ)
open import Data.List.Relation.Unary.Any.Properties using () renaming (++⁻ to any-++⁻; ++⁺ˡ to any-++⁺ˡ; ++⁺ʳ to any-++⁺ʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁻ to all-++⁻)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_) renaming (map to pairs-map)
open import Data.List.Relation.Unary.Linked using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (map⁺ to pairs-map⁺; ++⁺ to pairs-++⁺)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-sym; ↭-trans; ↭-reflexive) renaming (refl to ↭-refl′; prep to ↭-prep′; swap to ↭-swap′; trans to ↭-trans′)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (All-resp-↭; shifts) renaming (++⁺ˡ to ↭-++⁺ˡ; ++⁺ʳ to ↭-++⁺ʳ)
open import Data.List.Properties using (map-++; ++-assoc) renaming (++-identityʳ to ++-idʳ)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.Maybe using (Maybe; just; nothing; is-just) renaming (map to mapMaybe)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Data.Bool using (if_then_else_)
open import Level using (lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import denotation.MonotonicList using (Timeline; Frame; From; Pos; ix; last; tick; at; _<ᵖ_; <ᵖ-below) renaming (done to doneᶠᵐ; quiet to quietᶠᵐ)
open import denotation.MonotonicList using () renaming (sub to subᴾ)
import Tree as T
import denotation.Unfold as U
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (module Heap; module Run; Prims) renaming (module Machine to Shared)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Grow using (module Growing)
open import adequacy.Seq using (module Sequencing)
open import adequacy.Weaken using (module Weakening)
open import adequacy.Alike using (module Aliking)

module Naming (R : Set) where
  open Unsubbing R using (then; ≗-trans; wk≗; bind≗)
  open Growing R using (wkTree; wkLanes)
  open Sequencing R using (wk-wk; wk∋-wk; wkEl-wk; wkEnv-wk)
  open Shared Timeline (Out R) using (Heapᴹ; ⟨_,_,_⟩; Val; extend; look; cbs; wkVal; Callbacks; Stored; stored; get; wkAll)
  open Heap using (_⊑_; _⨾_; _∋_; there; new; grow; wk∋; cell; slot; Quiet) renaming (here to hereʳ; same to same⊑)
  open Run (Pureᴾ R) using (Act; done; compile; Env; wkEnv; wkAct; module Kit; module FlatKit; Ref; Observer; Kont; wkObs; Subscription; Subscribe; emitAll; Subject; wkSubject; wkR; wkSubn; writeRef; _>>ᴬ_)
  open Strongly R using (Sub; pendingˢ; ofˢ; mapˢ; takeWhileˢ; connectˢ; Lane; Path; PathLanes; here; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; this-lane; next-lane; Here; walk; top; coldˢ; _≗_; names; laneNames; Phase; Name; quietName; cutNames; flatNames; subjectNames; flatMapˢ; killAllᶜ; scanˢ; joinˢ; doneˢ; deferˢ; lane; CbRel; ≗-refl; newRef≗; done≗; register≗; send≗; finish≗; startCold≗; stop≗; stash≗; cancel≗; eff≗; here≗; under≗; diverge≗; unfold≗; readRef≗; writeRef≗; module Canon)
  open Moving R using (plant; plantᴸ)
  open Weakening R using (Grows)
  open Aliking R using (≗-sym)

  postulate
    -- A walk's continuation reads its subscription's unsubscribe only.
    walk-kont-sub : ∀ {h Δ A} {t : Sub h [] R} {x : Sub h Δ A} (π : Path t x) {v} (τ : h ⊑ v) {U U′ : Subscription v}
                  → Subscription.unsubscribe U ≗ Subscription.unsubscribe U′ → Here.kont (walk π top) τ U ≗ Here.kont (walk π top) τ U′

  ----------------------------------------------------------------------
  -- Names, weakened and planted

  -- A name carried along a growth.
  wkN : ∀ {h v} → h ⊑ v → Name h → Name v
  wkN τ (k , i) = k , wk∋ τ i

  -- A name some growth made: what the old world named, carried along.
  Img : ∀ {h₀ h} → h₀ ⊑ h → Name h → Set
  Img {h₀} ν (k , j) = Σ (h₀ ∋ k) λ i → wk∋ ν i ≡ j

  to-img : ∀ {h₀ h} (ν : h₀ ⊑ h) {x m} → wkN ν x ≡ m → Img ν m
  to-img ν {_ , i} refl = i , refl

  there-inj : ∀ {w j k k′} {i : w ∋ k} {i′ : w ∋ k′} → _≡_ {A = Name (j ∷ w)} (k , there i) (k′ , there i′) → _≡_ {A = Name w} (k , i) (k′ , i′)
  there-inj refl = refl

  wkN-inj : ∀ {h v} (τ : h ⊑ v) {x y : Name h} → wkN τ x ≡ wkN τ y → x ≡ y
  wkN-inj same⊑    e = e
  wkN-inj (grow τ) e = wkN-inj τ (there-inj e)

  quiet-wk : ∀ {h v} (τ : h ⊑ v) (k : Maybe (Quiet h)) → quietName (mapMaybe (wk∋ τ) k) ≡ mapᴸ (wkN τ) (quietName k)
  quiet-wk τ nothing  = refl
  quiet-wk τ (just _) = refl

  wk++ : ∀ {h v} (τ : h ⊑ v) xs ys {xs′ ys′ : List (Name v)} → xs′ ≡ mapᴸ (wkN τ) xs → ys′ ≡ mapᴸ (wkN τ) ys → xs′ ++ ys′ ≡ mapᴸ (wkN τ) (xs ++ ys)
  wk++ τ xs ys e₁ e₂ = trans (cong₂ _++_ e₁ e₂) (sym (map-++ (wkN τ) xs ys))

  -- A weakened tree names what the tree named, each weakened.
  mutual
    names-wkTree : ∀ {h v Δ A} (τ : h ⊑ v) (t : Sub h Δ A) → names (wkTree τ t) ≡ mapᴸ (wkN τ) (names t)
    names-wkTree τ (pendingˢ s q)                      = refl
    names-wkTree τ (coldˢ s hd ph)                     = refl
    names-wkTree τ (ofˢ p i xs)                        = refl
    names-wkTree τ doneˢ                               = refl
    names-wkTree τ (mapˢ f t)                          = names-wkTree τ t
    names-wkTree τ (scanˢ f r t)                       = cong (_ ∷_) (names-wkTree τ t)
    names-wkTree τ (takeWhileˢ i p c k tk t)           =
      wk++ τ (cutNames c) (quietName k ++ names t) refl (wk++ τ (quietName k) (names t) (quiet-wk τ k) (names-wkTree τ t))
    names-wkTree τ (flatMapˢ op f fl oc k r pl t ls)   =
      wk++ τ (flatNames fl) (cutNames oc ++ quietName k ++ (slot _ , r) ∷ names t ++ laneNames ls) refl
        (wk++ τ (cutNames oc) (quietName k ++ (slot _ , r) ∷ names t ++ laneNames ls) refl
          (wk++ τ (quietName k) ((slot _ , r) ∷ names t ++ laneNames ls) (quiet-wk τ k)
            (cong (_ ∷_) (wk++ τ (names t) (laneNames ls) (names-wkTree τ t) (names-wkLanes τ ls)))))
    names-wkTree τ (connectˢ S c b kb k fd q e rt s bd) =
      wk++ τ (subjectNames S) (cutNames c ++ (cell _ , b) ∷ quietName kb ++ quietName k ++ names s ++ names bd) refl
        (wk++ τ (cutNames c) ((cell _ , b) ∷ quietName kb ++ quietName k ++ names s ++ names bd) refl
          (cong (_ ∷_) (wk++ τ (quietName kb) (quietName k ++ names s ++ names bd) (quiet-wk τ kb)
            (wk++ τ (quietName k) (names s ++ names bd) (quiet-wk τ k) (wk++ τ (names s) (names bd) (names-wkTree τ s) (names-wkTree τ bd))))))
    names-wkTree τ (joinˢ j s fl x m)                  = refl
    names-wkTree τ (deferˢ k t)                        = wk++ τ (quietName k) (names t) (quiet-wk τ k) (names-wkTree τ t)

    names-wkLanes : ∀ {h v Δ B} (τ : h ⊑ v) (ls : List (Lane h Δ B)) → laneNames (wkLanes τ ls) ≡ mapᴸ (wkN τ) (laneNames ls)
    names-wkLanes τ []                = refl
    names-wkLanes τ (lane c k t ∷ ls) =
      wk++ τ (cutNames c) (quietName k ++ names t ++ laneNames ls) refl
        (wk++ τ (quietName k) (names t ++ laneNames ls) (quiet-wk τ k) (wk++ τ (names t) (laneNames ls) (names-wkTree τ t) (names-wkLanes τ ls)))

  -- A weakened tree's names are apart where the tree's were.
  wk-pairs : ∀ {h v Δ A} (τ : h ⊑ v) (t : Sub h Δ A) → AllPairs _≢_ (names t) → AllPairs _≢_ (names (wkTree τ t))
  wk-pairs τ t ap = subst (AllPairs _≢_) (sym (names-wkTree τ t)) (pairs-map⁺ (pairs-map (λ ne e → ne (wkN-inj τ e)) ap))

  -- Each name of a weakened tree a name of the tree, weakened.
  wk-img : ∀ {h v Δ A} (τ : h ⊑ v) (t : Sub h Δ A) {m} → m ∈ names (wkTree τ t) → Σ (Name h) λ x → x ∈ names t × wkN τ x ≡ m
  wk-img τ t {m} m∈ with ∈-map⁻ (wkN τ) (subst (m ∈_) (names-wkTree τ t) m∈)
  ... | x , x∈ , e = x , x∈ , sym e

  names-wk : ∀ {h v Δ A} (τ : h ⊑ v) (t : Sub h Δ A) {k} (j : v ∋ k) → (k , j) ∈ names (wkTree τ t)
           → Σ (h ∋ k) λ i → wk∋ τ i ≡ j × (k , i) ∈ names t
  names-wk τ t j m with wk-img τ t m
  ... | (_ , i) , m′ , refl = i , refl , m′

  -- A permutation keeps names apart.
  pairs-↭ : ∀ {h} {xs ys : List (Name h)} → xs ↭ ys → AllPairs _≢_ xs → AllPairs _≢_ ys
  pairs-↭ ↭-refl′           ap                      = ap
  pairs-↭ (↭-prep′ x p)     (a ∷ ap)                = All-resp-↭ p a ∷ pairs-↭ p ap
  pairs-↭ (↭-swap′ x y p)   ((xy ∷ ax) ∷ ay ∷ ap)   = ((λ e → xy (sym e)) ∷ All-resp-↭ p ay) ∷ All-resp-↭ p ax ∷ pairs-↭ p ap
  pairs-↭ (↭-trans′ p q)    ap                      = pairs-↭ q (pairs-↭ p ap)

  -- Names put in front of a stretch, or behind it.
  pre : ∀ {h} (X : List (Name h)) {ys s s′ : List (Name h)} → s′ ↭ ys ++ s → X ++ s′ ↭ ys ++ X ++ s
  pre X {ys} p = ↭-trans (↭-++⁺ˡ X p) (shifts X ys)

  post : ∀ {h} (Q : List (Name h)) {ys s s′ : List (Name h)} → s′ ↭ ys ++ s → s′ ++ Q ↭ ys ++ s ++ Q
  post Q {ys} {s} p = ↭-trans (↭-++⁺ʳ Q p) (↭-reflexive (++-assoc ys s Q))

  -- A node replanted naming `X` more than the one it replaced: the tree
  -- names `X` more.
  mutual
    names-plant-↭ : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′) {X}
                  → names v ↭ X ++ names u → names (plant π v) ↭ X ++ names t
    names-plant-↭ here v e = e
    names-plant-↭ (in-map π) v {X} e = names-plant-↭ π v {X} e
    names-plant-↭ (in-scan π) v {X} e = pre (_ ∷ []) {X} (names-plant-↭ π v {X} e)
    names-plant-↭ (in-take {c = c} {k} π) v {X} e = pre (cutNames c) {X} (pre (quietName k) {X} (names-plant-↭ π v {X} e))
    names-plant-↭ (in-outer {fl = fl} {oc} {k} {ls = ls} π) v {X} e =
      pre (flatNames fl) {X} (pre (cutNames oc) {X} (pre (quietName k) {X} (pre (_ ∷ []) {X} (post (laneNames ls) {X} (names-plant-↭ π v {X} e)))))
    names-plant-↭ (in-lanes {fl = fl} {oc} {k} {t = so} π) v {X} e =
      pre (flatNames fl) {X} (pre (cutNames oc) {X} (pre (quietName k) {X} (pre (_ ∷ []) {X} (pre (names so) {X} (names-plant-↭ᴸ π v {X} e)))))
    names-plant-↭ (in-source {S = S} {c} {kb = kb} {k} {bd = bd} π) v {X} e =
      pre (subjectNames S) {X} (pre (cutNames c) {X} (pre (_ ∷ []) {X} (pre (quietName kb) {X} (pre (quietName k) {X} (post (names bd) {X} (names-plant-↭ π v {X} e))))))
    names-plant-↭ (in-body {S = S} {c} {kb = kb} {k} {t = src} π) v {X} e =
      pre (subjectNames S) {X} (pre (cutNames c) {X} (pre (_ ∷ []) {X} (pre (quietName kb) {X} (pre (quietName k) {X} (pre (names src) {X} (names-plant-↭ π v {X} e))))))
    names-plant-↭ (in-defer {k = k} π) v {X} e = pre (quietName k) {X} (names-plant-↭ π v {X} e)

    names-plant-↭ᴸ : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′) {X}
                   → names v ↭ X ++ names u → laneNames (plantᴸ π v) ↭ X ++ laneNames ls
    names-plant-↭ᴸ (this-lane {c = c} {k} {ls = ls} π) v {X} e = pre (cutNames c) {X} (pre (quietName k) {X} (post (laneNames ls) {X} (names-plant-↭ π v {X} e)))
    names-plant-↭ᴸ (next-lane {l = lane c k s} π) v {X} e = pre (cutNames c) {X} (pre (quietName k) {X} (pre (names s) {X} (names-plant-↭ᴸ π v {X} e)))

  -- THE FRESH FRAME: a node replanted naming `X` more, `X` apart from
  -- itself and from every name the tree held, leaves the tree's names
  -- apart.
  fresh-plant : ∀ {h Δ A} {t : Sub h [] R} {u : Sub h Δ A} (π : Path t u) (v : Sub h Δ A) {X}
              → names v ↭ X ++ names u → AllPairs _≢_ X → AllPairs _≢_ (names t) → All (λ n → All (n ≢_) (names t)) X
              → AllPairs _≢_ (names (plant π v))
  fresh-plant π v e px pt dj = pairs-↭ (↭-sym (names-plant-↭ π v e)) (pairs-++⁺ px pt dj)

  -- A pending node replaced: every name the new node holds is more.
  pending-↭ : ∀ {h Δ A} (v : Sub h Δ A) → names v ↭ names v ++ []
  pending-↭ v = ↭-reflexive (sym (++-idʳ (names v)))

  -- Names no growth made, apart from every name one did.
  fresh-new : ∀ {h₀ h} (ν : h₀ ⊑ h) {ns ms : List (Name h)} → (∀ {m} → m ∈ ms → Img ν m)
            → All (λ n → ∀ {m} → Img ν m → n ≢ m) ns → All (λ n → All (n ≢_) ms) ns
  fresh-new ν im = all-map (λ f → tabulateᴬ λ m∈ → f (im m∈))

  -- An entry of a weakened heap: the entry, its inclusion carried on.
  get-wk : ∀ {h v w k} (ρ : h ⊑ v) (xs : All (Stored h) w) (i : w ∋ k) → get (wkAll ρ xs) i ≡ stored (Stored.val (get xs i)) (Stored.into (get xs i) ⨾ ρ)
  get-wk ρ (stored x σ ∷ xs) hereʳ     = refl
  get-wk ρ (stored x σ ∷ xs) (there i) = get-wk ρ xs i

  look-ext : ∀ {h j k} (H : Heapᴹ h) (x : Val (j ∷ h) j) (i : h ∋ k)
           → look (extend H x) (there i) ≡ wkVal k (Stored.into (get H i) ⨾ new) (Stored.val (get H i))
  look-ext {k = k} H x i = cong (λ e → wkVal k (Stored.into e) (Stored.val e)) (get-wk new H i)

  -- An allocation grows the world and moves nothing.
  grows-extend : ∀ {h k} (H : Heapᴹ h) (x : Val (k ∷ h) k) → Grows new H (extend H x)
  grows-extend H x = record
    { cells   = λ {t} r → trans (cong lower (look-ext H x r)) (sym (wkEl-wk t (Stored.into (get H r)) new (lower (Stored.val (get H r)))))
    ; slots   = λ {X} s → subst (λ c → CbRel c (wkVal (slot X) new (cbs H s))) (sym (look-ext H x s))
                  ( (λ a → ≗-sym (wk-wk (Stored.into (get H s)) new (Callbacks.onNext (Stored.val (get H s)) a)))
                  , ≗-sym (wk-wk (Stored.into (get H s)) new (Callbacks.onComplete (Stored.val (get H s))))
                  , ≗-sym (wk-wk (Stored.into (get H s)) new (Callbacks.isClosed (Stored.val (get H s)))) )
    ; stashes = λ u → subst (λ m → m ≗ wkAct new (look H u)) (sym (look-ext H x u)) (≗-sym (wk-wk (Stored.into (get H u)) new (Stored.val (get H u))))
    ; handles = λ hd → cong lower (look-ext H x hd) }
