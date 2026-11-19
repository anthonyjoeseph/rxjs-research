-- WHERE `laneˢ` PUTS A LANE'S PARTS, subscribed at `st`: its trigger,
-- its share and its gate, the frame's schedule, and what each part's
-- lane can end the take with (`Peel`).  `LaneEnd` reads the lane's end
-- off them.
module simultaneous.LaneEndSched where

open import Data.Bool using (Bool; true; false; T; not; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; _+_; s≤s; z≤n)
open import Data.Maybe using (nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Tree using (Obs; mergeᶠ; of; flatMap; takeWhile; scan; connect; connected)
open import denotation.Position using (Pos; Label; ix; sub; last; root; _≟ᵖ_; _⊕_; _<ᵖ_)
open import denotation.Events using (Timeline; fresh; ofᴱ)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; end; pin; Den; DenEnv; enter; Proper; Rejoin; shown; ended;
  at-out; at-end; on-out; _≺_; _≼_; module Op; module Bounded; module Scan; module TakeWhile;
  module Values)
import denotation.EmissionSet as ES
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≺-absurd; ≼-refl; ≺→≼; ≺-ext)
open import denotation.Laws.Worlds using (notT)
open import denotation.Laws.Cut using (capprox; inv-capprox; ix-asc)
open import denotation.Laws.BoundedInv using (module BoundedI)
open import denotation.Laws.Nth using (module Nths)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (hotOf)
open import quickcheck.Tabled.Exact using (EnvRel; rejoin-exact; proper-exact)
open import quickcheck.Tabled.Exact.Base using (sound)
open import simultaneous.SObs using (lone; Part; lanePart; burstPart; isLane; module Elaborate)
open import simultaneous.Listing using (listC; listC-ok; listC-exact; raw-exact; in-raw; Raw; Own; UncutEnv)
open import simultaneous.TableKit using (TR)
open import simultaneous.TableEnv using (_⊕ˡ_; DenOf; den; den-ex; den-ok; den-cons; Admits; admits-ix; admits-at)
open import simultaneous.TreeBounded using (listHot; admits-body)
open import simultaneous.TableRows using (⊕ˡ-⊕; part-≺)
open import simultaneous.DenRows using (conn-out; merge-out; hot-out; scan-out; bounded-out; of-mem)
open import simultaneous.ElabUndone using (Undone; Sends; sd-[]; sd-rep)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; over; stop; outerOpen; outerClose; laneStart; carry;
  laneDone; burstEnd; outerDone; subscribed; completed)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Routes; laneˢ; shareˢ; counted; framed; piece; laneStep; undone; marked)

------------------------------------------------------------------------
-- Where `laneˢ` puts things, subscribed at `st`

-- Its trigger's lane, the elaborated lane under it, and the trigger's
-- end rejoined by the share.
laneXt trigXs : Pos → List Label
laneXt st = ix 1 ∷ ix 0 ∷ sub (st ⊕ˡ (ix 0 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ [])) ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ []
trigXs st = ix 1 ∷ last ∷ sub (st ⊕ˡ (ix 0 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ [])) ∷ []

-- The lane part's connect, the elaborated lane, the share's reader.
laneL laneX readerR : Pos → Pos
laneL st = st ⊕ˡ (ix 0 ∷ ix 1 ∷ [])
laneX st = laneL st ⊕ˡ laneXt st
readerR st = laneL st ⊕ˡ (ix 0 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ [])

-- Where `counted` sends what its scan reads at `r`.
emitAt : Pos → Pos
emitAt r = r ⊕ˡ (ix 1 ∷ ix 1 ∷ ix 1 ∷ ix 0 ∷ [])

-- The later of two positions.
pick : Bool → Pos → Pos → Pos
pick true  e t = t
pick false e t = e

later : Pos → Pos → Pos
later e t = pick (e <ᵖ t) e t

later-cases : ∀ e t → (later e t ≡ e × t ≼ e) ⊎ (later e t ≡ t × e ≺ t)
later-cases e t = go (e <ᵖ t) refl
  where
    go : ∀ b → (e <ᵖ t) ≡ b → (pick b e t ≡ e × t ≼ e) ⊎ (pick b e t ≡ t × e ≺ t)
    go true  eq = inj₂ (refl , subst T (sym eq) tt)
    go false eq = inj₁ (refl , λ h → subst T eq h)

≺-ˡ : ∀ x l ls → x ≺ (x ⊕ˡ (l ∷ ls))
≺-ˡ x l ls = subst (x ≺_) (sym (⊕ˡ-⊕ x (l ∷ ls))) (≺-ext x ls)

------------------------------------------------------------------------
-- Rows read off listings

-- An operator's row before truncation is a row.
raw-in : ∀ {Γ X} K n (o : Obs Timeline Γ X) → Own o → {ρL : All Tb.Listed Γ} {ρD : DenEnv Γ} → EnvRel ρL ρD → UncutEnv ρL
       → ∀ p {q e} → Raw (capprox K n o ρD) p q e → enter (capprox K n o ρD) p q e
raw-in K n o ow ex u p x with listC-ok K n o u p
... | l , eq , ul = in-raw (capprox K n o _) p (raw-exact K n o ow ex p eq) ul x

-- A connect's hot, read before truncation.
hot-in : ∀ {Γ X} n (o : Obs Timeline Γ X) {ρ : ℕ → All Tb.Listed Γ} (u : ∀ N → UncutEnv (ρ N)) (D : DenOf ρ) c N p {q e}
       → Rejoin p (Proper (enter (capprox (3 + N) n o (den D N)) (c ⊕ [ ix 1 ]))) q e
       → enter (ES.hot (Proper (enter (capprox (3 + N) n o (den D N)) (c ⊕ [ ix 1 ])))) p q e
hot-in n o u D c N p x with listC-ok (3 + N) n o (u N) (c ⊕ [ ix 1 ])
... | l , eq , ul = in-raw (ES.hot _) p (rejoin-exact (proper-exact (listC-exact (3 + N) n o (den-ex D N) (c ⊕ [ ix 1 ]) eq)) p) ul x

-- A listed row is a row.
tr-in : ∀ {Γ X} K n (o : Obs Timeline Γ X) {ρL : All Tb.Listed Γ} {ρD : DenEnv Γ} → EnvRel ρL ρD → UncutEnv ρL
      → ∀ p {k e} → TR (listC K n o ρL p) k e → enter (capprox K n o ρD) p k e
tr-in K n o ex u p (l , eq , r) with listC-ok K n o u p
... | l′ , eq′ , ul with trans (sym eq) eq′
...   | refl = sound (listC-exact K n o ex p eq ul) r

-- Whether a list holds an end at `k`.
isEnd : ∀ {X : Set} (e : Ev X) → Dec (e ≡ end)
isEnd (out _) = no λ ()
isEnd skip    = no λ ()
isEnd end     = yes refl
isEnd (pin _) = no λ ()

dec-end : ∀ {X : Set} (rs : List (Tb.Row X)) k → Dec ((k , end) ∈ rs)
dec-end []              k = no λ ()
dec-end ((k′ , e) ∷ rs) k with k ≟ᵖ k′ | isEnd e | dec-end rs k
... | yes refl | yes refl | _     = yes (here refl)
... | _        | _        | yes m = yes (there m)
... | no ne    | _        | no ¬m = no λ { (here refl) → ne refl ; (there m) → ¬m m }
... | yes refl | no ne    | no ¬m = no λ { (here refl) → ne refl ; (there m) → ¬m m }

-- A scan's state at a row folds the one value there.
acc-last : ∀ {X Y : Set} {f : Y → X → Y} {z : Y} {t : ES.EmissionSet X} {v a₀}
         → (∀ {a} → t v (out a) → a ≡ a₀) → ∀ {y} → Scan.Acc f z t v y → Σ Y λ b → y ≡ f b a₀
acc-last one (Scan.acc₀ r _) with one r
... | refl = _ , refl
acc-last one (Scan.acc _ r _ _) with one r
... | refl = _ , refl

------------------------------------------------------------------------
-- What `counted`'s scan sends

-- The scan's second list is what it read.
ls-one : ∀ {X} (s : Routes × (List (IE X) × List (IE X))) e → proj₂ (proj₂ (laneStep s e)) ≡ e ∷ []
ls-one s (instEmit (value _) _)      = refl
ls-one s (instEmit (mark begin) _)      = refl
ls-one s (instEmit (mark over) _)       = refl
ls-one s (instEmit (mark stop) _)       = refl
ls-one s (instEmit (mark outerOpen) _)  = refl
ls-one s (instEmit (mark outerClose) _) = refl
ls-one s (instEmit (mark laneStart) _)  = refl
ls-one s (instEmit (mark carry) _)      = refl
ls-one s (instEmit (mark laneDone) _)   = refl
ls-one s (instEmit (mark burstEnd) _)   = refl
ls-one s (instEmit (mark outerDone) _)  = refl
ls-one s (instEmit (mark subscribed) _) = refl
ls-one s (instEmit (mark completed) _)  = refl

-- Its first list ends no lane.
ls-true : ∀ {X} (s : Routes × (List (IE X) × List (IE X))) e → Sends (proj₁ (proj₂ (laneStep s e)))
ls-true s (instEmit (value _) _)      = sd-[]
ls-true s (instEmit (mark begin) _)      = sd-[]
ls-true s (instEmit (mark over) _)       = sd-[]
ls-true s (instEmit (mark stop) _)       = sd-[]
ls-true s (instEmit (mark outerOpen) _)  = sd-[]
ls-true s (instEmit (mark outerClose) _) = sd-[]
ls-true s (instEmit (mark laneStart) _)  = sd-[]
ls-true s (instEmit (mark carry) _)      = sd-[]
ls-true s (instEmit (mark laneDone) _)   = sd-rep (proj₂ (proj₁ s)) carry root tt
ls-true s (instEmit (mark burstEnd) _)   = sd-[]
ls-true s (instEmit (mark outerDone) _)  = sd-[]
ls-true s (instEmit (mark subscribed) _) = sd-[]
ls-true s (instEmit (mark completed) _)  = sd-[]

-- An `of` of one value shows it at its first child.
of-one : ∀ {X : Set} p (x : X) {q y} → ES.InE (ofᴱ p 0 (x ∷ [])) q (out y) → q ≡ p ⊕ [ ix 0 ] × y ≡ x
of-one p x at-out      = refl , refl
of-one p x (on-out ())

------------------------------------------------------------------------
-- The lane

module Ending {Θ : List Set} {B : Set} n (x : Obs Timeline (⊤ ∷ Θ) (IE B)) {ρ : ℕ → All Tb.Listed Θ} (u : ∀ N → UncutEnv (ρ N))
              (D : DenOf ρ) (st : Pos) (ad : Admits D st) (N : ℕ) (ux : ∀ h → Undone (capprox (3 + N) n x (h ∷ den D N))) where

  K : ℕ
  K = 3 + N

  -- The two parts' children.
  G : Part → Obs Timeline (⊤ ∷ Θ) (IE B)
  G k = flatMap (mergeᶠ nothing) (λ _ → x) (takeWhile false isLane (of (k ∷ [])))

  Sh : Part → Obs Timeline (⊤ ∷ Θ) (IE B)
  Sh k = flatMap (mergeᶠ nothing) (λ _ → G k) (connected (here refl))

  M : Obs Timeline Θ (IE B)
  M = flatMap (mergeᶠ nothing) (λ k → shareˢ (G k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ []))

  inner : Routes × (List (IE B) × List (IE B)) → Obs Timeline (IE B ∷ ⊤ ∷ Θ) (IE B)
  inner y = flatMap (mergeᶠ nothing) (λ c → of (if c then proj₁ (proj₂ y) else proj₂ (proj₂ y))) (of (true ∷ false ∷ []))

  z₀ : Routes × (List (IE B) × List (IE B))
  z₀ = (root , 0) , ([] , [])

  ld : IE B
  ld = marked laneDone

  ρ₀ : DenEnv Θ
  ρ₀ = den D N

  ----------------------------------------------------------------------
  -- Every lane, wherever subscribed: what ends the take

  module Peel (k : Part) (P : Pos) where
    σ₁P : EmissionSet ⊤
    σ₁P = enter (Op.of (tt ∷ [])) (P ⊕ [ ix 1 ])

    ρ₁P : DenEnv (⊤ ∷ Θ)
    ρ₁P = ES.hot (Proper σ₁P) ∷ ρ₀

    σ₂P : EmissionSet (IE B)
    σ₂P = enter (capprox K n (Sh k) ρ₁P) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ])

    ρ₂P : DenEnv (IE B ∷ ⊤ ∷ Θ)
    ρ₂P = ES.hot (Proper σ₂P) ∷ ρ₁P

    BP : Pos
    BP = (P ⊕ [ ix 0 ]) ⊕ [ ix 0 ]

    FrP : EmissionSet (IE B)
    FrP = enter (capprox K n (framed k) ρ₂P) BP

    -- The lane's of, picking its scan's second list.
    pick-lane : ∀ v y s₀ a₀ → FrP v (out a₀) → y ≡ laneStep s₀ a₀ → ∀ {w c q a}
              → enter (Op.of (true ∷ false ∷ [])) (v ⊕ [ ix 1 ]) w (out c)
              → ES.InE (ofᴱ (w ⊕ [ ix 1 ]) 0 (if c then proj₁ (proj₂ y) else proj₂ (proj₂ y))) q (out a)
              → T (not (undone a)) → Σ Pos λ v′ → Σ (IE B) λ a₁ → q ≡ emitAt v′ × FrP v′ (out a₁) × T (not (undone a₁))
    pick-lane v _ s₀ a₀ fa refl (at-out , _) l nu = ⊥-elim (notT _ nu (ls-true s₀ a₀ (of-mem _ 0 _ l)))
    pick-lane v _ s₀ a₀ fa refl (on-out at-out , _) l nu with of-one _ a₀ (subst (λ xs → ES.InE (ofᴱ _ 0 xs) _ (out _)) (ls-one s₀ a₀) l)
    ... | refl , refl = v , a₀ , refl , fa , nu
    pick-lane v _ s₀ a₀ fa refl (on-out (on-out ()) , _) _ _

    -- What the lane ends the take with is what its scan read.
    peel : ∀ {q a} → enter (capprox K n (shareˢ (G k) (counted (framed k))) ρ₀) P q (out a) → T (not (undone a))
         → Σ Pos λ v → Σ (IE B) λ a₀ → q ≡ emitAt v × FrP v (out a₀) × T (not (undone a₀))
    peel r nu =
      let r₁ = conn-out (capprox K n (of (tt ∷ [])) ρ₀) (λ h → capprox K n (connect (Sh k) (counted (framed k))) (h ∷ ρ₀)) P r
          r₂ = conn-out (capprox K n (Sh k) ρ₁P) (λ h → capprox K n (counted (framed k)) (h ∷ ρ₁P)) (P ⊕ [ ix 0 ]) r₁
          (v , y , sv , il , _) = merge-out (λ y → capprox K n (inner y) ρ₂P) (Op.scan laneStep z₀ (capprox K n (framed k) ρ₂P)) BP r₂
          (w , c , ow , (ll , _) , _) = merge-out (λ c → Op.of (if c then proj₁ (proj₂ y) else proj₂ (proj₂ y))) (Op.of (true ∷ false ∷ [])) (v ⊕ [ ix 1 ]) il
          (s₀ , a₀ , fa , eq) = scan-out laneStep z₀ (capprox K n (framed k) ρ₂P) BP sv
      in pick-lane v y s₀ a₀ fa eq ow ll nu

    -- The second part reads the share, whose rows are the elaborated
    -- lane's.
    h₂-u : ∀ {s v a} → enter (ES.hot (Proper σ₂P)) s v (out a) → T (undone a)
    h₂-u r =
      let (_ , (σq , _) , _ , _) = hot-out r
          (q₁ , _ , _ , lg , _) = merge-out (λ _ → capprox K n (G k) ρ₁P) (ES.hot (Proper σ₁P)) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) σq
          (_ , _ , _ , lx , _) = merge-out (λ _ → capprox K n x ρ₁P) (capprox K n (takeWhile false isLane (of (k ∷ []))) ρ₁P) (q₁ ⊕ [ ix 1 ]) lg
      in ux (ES.hot (Proper σ₁P)) _ lx

    module Bp = Bounded 1 (λ j → capprox K n (piece k j) ρ₂P) (enter (Op.of (0 ∷ 1 ∷ 2 ∷ [])) BP)

    -- The first part sends a start mark.
    piece0 : ∀ k′ {s v a} → enter (capprox K n (piece k′ 0) ρ₂P) s v (out a) → T (not (undone a)) → ⊥
    piece0 lanePart  (at-out , _) ()
    piece0 lanePart  (on-out () , _) _
    piece0 burstPart (at-out , _) ()
    piece0 burstPart (on-out () , _) _

    -- The second part reads the share.
    piece1 : ∀ k′ {s v a} → enter (capprox K n (piece k′ 1) ρ₂P) s v (out a) → T (undone a)
    piece1 lanePart  l = h₂-u l
    piece1 burstPart l = h₂-u l

    -- The third part ends the lane, in the lane part only.
    piece2 : ∀ k′ {i s v a} → Bounded.Sub 1 (λ j → capprox K n (piece k′ j) ρ₂P) (enter (Op.of (0 ∷ 1 ∷ 2 ∷ [])) BP) i (BP ⊕ [ ix 2 ]) s 2
           → enter (capprox K n (piece k′ 2) ρ₂P) s v (out a)
           → k′ ≡ lanePart × Σ ℕ λ i′ → Σ Pos λ s′ → Bounded.Sub 1 (λ j → capprox K n (piece k′ j) ρ₂P) (enter (Op.of (0 ∷ 1 ∷ 2 ∷ [])) BP) i′ (BP ⊕ [ ix 2 ]) s′ 2 × v ≡ s′ ⊕ [ ix 0 ]
    piece2 lanePart  sb (at-out , _)    = refl , _ , _ , sb , refl
    piece2 lanePart  sb (on-out () , _)
    piece2 burstPart sb (() , _)

    fr-j : ∀ {q j i s v a} → enter (Op.of (0 ∷ 1 ∷ 2 ∷ [])) BP q (out j) → Bp.Sub i q s j → enter (capprox K n (piece k j) ρ₂P) s v (out a)
         → T (not (undone a)) → k ≡ lanePart × Σ ℕ λ i′ → Σ Pos λ s′ → Bp.Sub i′ (BP ⊕ [ ix 2 ]) s′ 2 × v ≡ s′ ⊕ [ ix 0 ]
    fr-j (at-out , _)                     sb l nu = ⊥-elim (piece0 k l nu)
    fr-j (on-out at-out , _)              sb l nu = ⊥-elim (notT _ nu (piece1 k l))
    fr-j (on-out (on-out at-out) , _)     sb l nu = piece2 k sb l
    fr-j (on-out (on-out (on-out ())) , _) _ _ _

    -- What the scan reads that ends a lane: the third part's mark.
    fr-back : ∀ {v a₀} → FrP v (out a₀) → T (not (undone a₀))
            → k ≡ lanePart × Σ ℕ λ i → Σ Pos λ s → Bp.Sub i (BP ⊕ [ ix 2 ]) s 2 × v ≡ s ⊕ [ ix 0 ]
    fr-back r nu =
      let (_ , _ , _ , _ , oq , sb , (l , _)) = bounded-out 1 (λ j → capprox K n (piece k j) ρ₂P) (Op.of (0 ∷ 1 ∷ 2 ∷ [])) BP r
      in fr-j oq sb l nu

  ----------------------------------------------------------------------
  -- The lane part, at `L`

  L L₁ B₀ S Bc R : Pos
  L = laneL st
  L₁ = L ⊕ [ ix 1 ]
  B₀ = L ⊕ [ ix 0 ]
  S = B₀ ⊕ [ ix 1 ]
  Bc = B₀ ⊕ [ ix 0 ]
  R = readerR st

  qt sp T′ : Pos
  qt = (L₁ ⊕ [ ix 0 ]) ⊕ [ sub S ]
  sp = qt ⊕ [ ix 1 ]
  T′ = laneL st ⊕ˡ trigXs st

  -- The hots and their admissible subscriptions.
  aL : Admits D L
  aL = admits-ix D 1 (admits-ix D 0 ad)

  h₁ = listHot n (of (tt ∷ [])) u D L aL
  D₁ = den-cons h₁ D

  a₁ : Admits D₁ B₀
  a₁ = admits-body n (of (tt ∷ [])) u D L aL

  trig : ℕ → Tb.Listed ⊤
  trig N′ = hotOf (proj₁ (listC-ok (3 + N′) n (of (tt ∷ [])) (u N′) L₁))

  ℓ₁ : ℕ → All Tb.Listed (⊤ ∷ Θ)
  ℓ₁ N′ = trig N′ ∷ ρ N′

  u₁ : ∀ N′ → UncutEnv (ℓ₁ N′)
  u₁ N′ = proj₂ (proj₂ (listC-ok (3 + N′) n (of (tt ∷ [])) (u N′) L₁)) , u N′

  h₂ = listHot n (Sh lanePart) {ℓ₁} u₁ D₁ B₀ a₁
  D₂ = den-cons h₂ D₁

  a₂ : Admits D₂ Bc
  a₂ = admits-body n (Sh lanePart) {ℓ₁} u₁ D₁ B₀ a₁

  ℓ₂ : ℕ → All Tb.Listed (IE B ∷ ⊤ ∷ Θ)
  ℓ₂ N′ = hotOf (proj₁ (listC-ok (3 + N′) n (Sh lanePart) {ℓ₁ N′} (u₁ N′) S)) ∷ ℓ₁ N′

  u₂ : ∀ N′ → UncutEnv (ℓ₂ N′)
  u₂ N′ = proj₂ (proj₂ (listC-ok (3 + N′) n (Sh lanePart) {ℓ₁ N′} (u₁ N′) S)) , u₁ N′

  ρ₁ = den D₁ N
  ρ₂ = den D₂ N

  σ₁ : EmissionSet ⊤
  σ₁ = enter (capprox K n (of (tt ∷ [])) ρ₀) L₁

  σ₂ : EmissionSet (IE B)
  σ₂ = enter (capprox K n (Sh lanePart) ρ₁) S

  -- The trigger: one value, then its end.
  σ₁-val : σ₁ (L₁ ⊕ [ ix 0 ]) (out tt)
  σ₁-val = raw-in K n (of (tt ∷ [])) tt (den-ex D N) (u N) L₁ at-out

  σ₁-end : σ₁ (L₁ ⊕ [ last ]) end
  σ₁-end = raw-in K n (of (tt ∷ [])) tt (den-ex D N) (u N) L₁ (on-out at-end)

  σ₁-end⁻ : ∀ {c} → σ₁ c end → c ≡ L₁ ⊕ [ last ]
  σ₁-end⁻ (on-out at-end , _) = refl

  σ₁-out⁻ : ∀ {k y} → σ₁ k (out y) → k ≡ L₁ ⊕ [ ix 0 ]
  σ₁-out⁻ (at-out , _)    = refl
  σ₁-out⁻ (on-out () , _)

  L₁0-last : (L₁ ⊕ [ ix 0 ]) ≺ (L₁ ⊕ [ last ])
  L₁0-last = part-≺ L₁ [] [] refl

  H₁-val : Proper σ₁ (L₁ ⊕ [ ix 0 ]) (out tt)
  H₁-val = σ₁-val , λ c → subst (λ c′ → (L₁ ⊕ [ ix 0 ]) ≼ c′) (sym (σ₁-end⁻ c)) (≺→≼ {L₁ ⊕ [ ix 0 ]} {L₁ ⊕ [ last ]} L₁0-last)

  H₁-end : Proper σ₁ (L₁ ⊕ [ last ]) end
  H₁-end = σ₁-end , λ c → subst (λ c′ → (L₁ ⊕ [ last ]) ≼ c′) (sym (σ₁-end⁻ c)) (≼-refl {L₁ ⊕ [ last ]})

  -- The share reads it: one value, then the trigger's end.
  r₁-val : enter (ES.hot (Proper σ₁)) S qt (out tt)
  r₁-val = hot-in n (of (tt ∷ [])) u D L N S (shown H₁-val tt (part-≺ L (ix 1 ∷ []) (ix 0 ∷ []) refl))

  r₁-end : enter (ES.hot (Proper σ₁)) S T′ end
  r₁-end = hot-in n (of (tt ∷ [])) u D L N S (ended H₁-end (part-≺ L (ix 1 ∷ []) (last ∷ []) refl))

  r₁-out⁻ : ∀ {k y} → enter (ES.hot (Proper σ₁)) S k (out y) → k ≡ qt
  r₁-out⁻ r with hot-out r
  ... | _ , (σq , _) , _ , refl = cong (λ q′ → q′ ⊕ [ sub S ]) (σ₁-out⁻ σq)

  -- The gate passes the lane part's one value, then ends.
  TW : Obs Timeline (⊤ ∷ Θ) Part
  TW = takeWhile false isLane (of (lanePart ∷ []))

  tw : EmissionSet Part
  tw = enter (capprox K n TW ρ₁) sp

  og-val : enter (Op.of (lanePart ∷ [])) sp (sp ⊕ [ ix 0 ]) (out lanePart)
  og-val = raw-in K n (of (lanePart ∷ [])) tt {ℓ₁ N} (den-ex D₁ N) (u₁ N) sp at-out

  og-end : enter (Op.of (lanePart ∷ [])) sp (sp ⊕ [ last ]) end
  og-end = raw-in K n (of (lanePart ∷ [])) tt {ℓ₁ N} (den-ex D₁ N) (u₁ N) sp (on-out at-end)

  tg-nf : ∀ {k} → ¬ TakeWhile.Failed false isLane (enter (Op.of (lanePart ∷ [])) sp) k
  tg-nf (_ , _ , (at-out , _) , () , _)
  tg-nf (_ , _ , (on-out () , _) , _ , _)

  tg-val : tw (sp ⊕ [ ix 0 ]) (out lanePart)
  tg-val = raw-in K n TW tt {ℓ₁ N} (den-ex D₁ N) (u₁ N) sp (TakeWhile.pass og-val tt tg-nf)

  tg-end : tw (sp ⊕ [ last ]) end
  tg-end = raw-in K n TW tt {ℓ₁ N} (den-ex D₁ N) (u₁ N) sp (TakeWhile.tend og-end tg-nf)

  tg-out⁻ : ∀ {k y} → tw k (out y) → k ≡ sp ⊕ [ ix 0 ]
  tg-out⁻ (TakeWhile.pass (at-out , _) _ _ , _)    = refl
  tg-out⁻ (TakeWhile.pass (on-out () , _) _ _ , _)
  tg-out⁻ (TakeWhile.fail _ _ _ () , _)

  Gd : Den (IE B)
  Gd = capprox K n (G lanePart) ρ₁

  -- Orders.
  sl-T : (sp ⊕ [ last ]) ≺ T′
  sl-T = part-≺ L₁ (sub S ∷ ix 1 ∷ last ∷ []) (sub S ∷ []) refl

  R-T : R ≺ T′
  R-T = part-≺ L (ix 0 ∷ ix 1 ∷ ix 1 ∷ []) (last ∷ sub S ∷ []) refl

  L-T : L ≺ T′
  L-T = ≺-ˡ L (ix 1) (last ∷ sub S ∷ [])

  c₀ : Pos
  c₀ = ((Bc ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ last ]

  c₀-B1 : c₀ ≺ (Bc ⊕ [ ix 1 ])
  c₀-B1 = part-≺ Bc (ix 1 ∷ last ∷ []) [] refl

  c₀-T : c₀ ≺ T′
  c₀-T = part-≺ L (ix 0 ∷ ix 0 ∷ ix 1 ∷ last ∷ []) (last ∷ sub S ∷ []) refl

  B2-T : (Bc ⊕ [ ix 2 ]) ≺ T′
  B2-T = part-≺ L (ix 0 ∷ ix 2 ∷ []) (last ∷ sub S ∷ []) refl

  -- The framed parts and their schedule.
  Fj : ℕ → Den (IE B)
  Fj j = capprox K n (piece lanePart j) ρ₂

  Ob : EmissionSet ℕ
  Ob = enter (Op.of (0 ∷ 1 ∷ 2 ∷ [])) Bc

  module Bd = Bounded 1 Fj Ob
  open Values Ob using (Nth; Next)
  open Nths Ob using (nth-inj)

  okB = admits-at D₂ a₂ N
  module BI = BoundedI okB 1 Fj (λ j → inv-capprox K n (piece lanePart j) ρ₂ (den-ok D₂ N)) (inv-capprox K n (of (0 ∷ 1 ∷ 2 ∷ [])) ρ₂ (den-ok D₂ N) Bc okB)

  ob₀ : Ob (Bc ⊕ [ ix 0 ]) (out 0)
  ob₀ = raw-in K n (of (0 ∷ 1 ∷ 2 ∷ [])) tt {ℓ₂ N} (den-ex D₂ N) (u₂ N) Bc at-out

  ob₁ : Ob (Bc ⊕ [ ix 1 ]) (out 1)
  ob₁ = raw-in K n (of (0 ∷ 1 ∷ 2 ∷ [])) tt {ℓ₂ N} (den-ex D₂ N) (u₂ N) Bc (on-out at-out)

  ob₂ : Ob (Bc ⊕ [ ix 2 ]) (out 2)
  ob₂ = raw-in K n (of (0 ∷ 1 ∷ 2 ∷ [])) tt {ℓ₂ N} (den-ex D₂ N) (u₂ N) Bc (on-out (on-out at-out))

  B01 : (Bc ⊕ [ ix 0 ]) ≺ (Bc ⊕ [ ix 1 ])
  B01 = ix-asc Bc (s≤s z≤n)

  B12 : (Bc ⊕ [ ix 1 ]) ≺ (Bc ⊕ [ ix 2 ])
  B12 = ix-asc Bc (s≤s (s≤s z≤n))

  ob-min : ∀ {k b} → Ob k (out b) → (Bc ⊕ [ ix 0 ]) ≼ k
  ob-min (at-out , _)                       = ≼-refl {Bc ⊕ [ ix 0 ]}
  ob-min (on-out at-out , _)                = ≺→≼ {Bc ⊕ [ ix 0 ]} {Bc ⊕ [ ix 1 ]} B01
  ob-min (on-out (on-out at-out) , _)       = ≺→≼ {Bc ⊕ [ ix 0 ]} {Bc ⊕ [ ix 2 ]} (≺-trans {Bc ⊕ [ ix 0 ]} {Bc ⊕ [ ix 1 ]} {Bc ⊕ [ ix 2 ]} B01 B12)
  ob-min (on-out (on-out (on-out ())) , _)

  nx₁ : Next (Bc ⊕ [ ix 0 ]) (Bc ⊕ [ ix 1 ])
  nx₁ (at-out , _)                 lt = ⊥-elim (≺-irrefl {Bc ⊕ [ ix 0 ]} lt)
  nx₁ (on-out at-out , _)          _  = ≼-refl {Bc ⊕ [ ix 1 ]}
  nx₁ (on-out (on-out at-out) , _) _  = ≺→≼ {Bc ⊕ [ ix 1 ]} {Bc ⊕ [ ix 2 ]} B12
  nx₁ (on-out (on-out (on-out ())) , _) _

  nx₂ : Next (Bc ⊕ [ ix 1 ]) (Bc ⊕ [ ix 2 ])
  nx₂ (at-out , _)                 lt = ⊥-elim (≺-absurd {Bc ⊕ [ ix 1 ]} {Bc ⊕ [ ix 0 ]} lt B01)
  nx₂ (on-out at-out , _)          lt = ⊥-elim (≺-irrefl {Bc ⊕ [ ix 1 ]} lt)
  nx₂ (on-out (on-out at-out) , _) _  = ≼-refl {Bc ⊕ [ ix 2 ]}
  nx₂ (on-out (on-out (on-out ())) , _) _

  nth₀ : Nth 0 (Bc ⊕ [ ix 0 ]) 0
  nth₀ = Values.first ob₀ ob-min

  nth₁ : Nth 1 (Bc ⊕ [ ix 1 ]) 1
  nth₁ = Values.next nth₀ ob₁ B01 nx₁

  nth₂ : Nth 2 (Bc ⊕ [ ix 2 ]) 2
  nth₂ = Values.next nth₁ ob₂ B12 nx₂

  -- The first part: a mark, then its end, before the second part's value.
  s₀ : Pos
  s₀ = (Bc ⊕ [ ix 0 ]) ⊕ [ ix 1 ]

  l₀-end : Bd.Ends 0 [] c₀
  l₀-end = Bc ⊕ [ ix 0 ] , 0 , s₀ , nth₀ , Bd.room (s≤s z≤n)
         , (raw-in K n (of (marked laneStart ∷ [])) tt {ℓ₂ N} (den-ex D₂ N) (u₂ N) s₀ (on-out at-end) , ≺-ext s₀ [])

  fr₁ : Bd.Starts 1 (Bc ⊕ [ ix 1 ]) (Bd.Sched 1) R
  fr₁ = Bd.freed (s≤s z≤n) (inj₁ (c₀ , l₀-end , c₀-B1))

  sb₁ : Bd.Sub 1 (Bc ⊕ [ ix 1 ]) R 1
  sb₁ = nth₁ , fr₁
