{-# OPTIONS --guardedness #-}

-- A FLATMAP'S SCAN SOURCE HOLDS (`CombSrc`): the three branches it reads,
-- the scan's counters against them row by row, and the source's end.
module simultaneous.HeldSrc where

open import Data.List using (List; []; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (lookup; _∷_) renaming ([] to []ᵉ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

open import Tree using (Obs; FlatOp; empty; of; map; flatMap; mergeᶠ)
open import denotation.Position using (Pos; root; _≟ᵖ_; _≟ⁱ_; ix; sub; last; _⊕_; Path)
open import denotation.Events using (Timeline; <ᵖ-between; fresh; <ᵖ-part)
open import denotation.EmissionSet using (hot; enter; ⟦_⟧; DenEnv; module Op; Ev; out; end; Few; _≼_; EmissionSet; Proper; _≺_)
open import simultaneous.SObs using (lone; module Elaborate; Flat; outerB; laneB; closeB)
open import simultaneous.Relations using (Met)
open import simultaneous.Shut using (r₀)
open import simultaneous.Routed using (Held; Early; Idle; Rest; Ex; nameOf; nm; Valued; opos; cnt)
open import simultaneous.HeldIn using (IdleIn)
open import denotation.Laws.Worlds using (Hots; GoodEnv; ⊕-assoc; Ok; Lawful; Shows; ⊑-snoc; ⊕-identityʳ; ⊑-inside; ok-step; ok-in;
  _⊑_; InvAt; world-after; W; ⊑-≼; pinby-silent)
open import simultaneous.LaneLocal using (inv-ev; Fit; proper-fit; held-fit; module LaneReal)
open import simultaneous.CombSent using (src-op; own-op; cat-op; tag-op; no-track; no-close; tag-branch; Cat-of; Tag; sent-branch; Closing; closing-mark; closing-value; closer-marks; closer-good; src-where; Where) renaming (under to w-under; past to w-past)
open import denotation.EmissionSet using (map-end) renaming (ended to r-ended; late to r-late; shown to r-shown)
open import simultaneous.DenRows using (map-out′; hot-out)
open import simultaneous.HeldConnect using (early-inst; rootOf-ext)
open import denotation.Laws using (good-cons)
open import denotation.Laws.Connect using () renaming (lawful to src-lawful; ok₀ to body-ok)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Relation.Unary.Any using (there)
open import simultaneous.InstEmit using (begin; completed; instEmit; value; mark; over; outerOpen; outerDone)
open import Data.Product using (_×_; _,_; proj₁; Σ; proj₂)
open import Data.Unit using (⊤; tt)
open import simultaneous.BranchSplit using (SrcOf; bview)
open import simultaneous.LaneSplit using (Ln; module HotSplit)
open import simultaneous.TakeCut using (inst-⊕)
open import simultaneous.CloseDone using (module CloseDone)
open import simultaneous.CombSent using (Clo)
open import simultaneous.FlatLanes using (Tg)
import denotation.Laws.ShowsJoin as SJ
open import denotation.Laws.ShowsOps using (sk-of; module Take)
open import denotation.Laws.Shows using (Step; k-shows; shows-k; sk-down; sk-trunc)
open import denotation.Laws.Worlds.Leaves using (of-inv)
open import denotation.Laws.Modulus using (≺→≼; ≺-≼-≺; ≺-irrefl; ≺-ext; ≺-trans; ≺-absurd; ≼-refl; ≼-or-≻; ≼-split; entered-few)
open import simultaneous.CombSent using (fed-op; Fed; sent-track; trackers-out; hots-at; tag-outer)
open import simultaneous.HeldBase using (Bound; shows-ev; EnvHeld; module FlatHots; IH; ev-none; Fresh; fresh-adm)
open import simultaneous.Routed using (Placed; Adm; adm-∪)
open import denotation.Laws.Worlds using (plain-ix)
open import simultaneous.FlatLanes using (end-last; BProj; past-within; within-of; within₀; co)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; count; elab; srcLane; laneSrc; annotate; marked; trackers; closer; combined; laneˢ; each; coldˢ;
  Input; react; going; fed; opening; anyHolds; branch; restamp; wrapped; Out; cut; left)
open import simultaneous.HeldComb using (ev; ShutRun; outRows; init; from; past)
open import simultaneous.HeldComb using (ShutRun; ev)
open import Data.Bool.Properties using (T-≡)
open import Relation.Nullary using (¬_)
import Relation.Nullary as Nl
open import Data.Sum using (_⊎_; [_,_]′; inj₁; inj₂)
open import simultaneous.Layers using (run-tail; run-after) renaming (run-row to run-row∈)
open import simultaneous.Readings using (rootOf; instantOf)
open import simultaneous.Instants using (_≺ⁱ_; ≺-instant; instant-≺)
open import simultaneous.OwnEnds using (module OwnEnds)
open import denotation.Read using (Visible; After; cursor; Run; loud) renaming (_∷_ to _∷ᴿ_)
open import Function using (Equivalence)
open import Data.Bool using (true; false)
open import simultaneous.Project using (run-prefix)
import denotation.Read as Run
import Data.Nat as ℕ
import Data.Nat.Properties as ℕP
import denotation.EmissionSet as ES
open import denotation.Laws.HotBelow using (under-hot)
open import simultaneous.OuterSplit using (count-open; module OuterSplit)
open import simultaneous.ProperIdle using (proper-idle)

open import Tree using (Obs; FlatOp; empty; of; map; flatMap)


-- A row between two of one instant is of it.
between-inst : ∀ {y q z} → y ≺ q → q ≼ z → instantOf z ≡ instantOf y → instantOf y ≡ instantOf q
between-inst {y} {q} {z} yq qz zy with instantOf y ≟ⁱ instantOf q
... | Nl.yes e = e
... | Nl.no ne = ⊥-elim (qz (instant-≺ z q (subst (_≺ⁱ instantOf q) (sym zy) (≺-instant y q yq ne))))

-- An opened outer row is a mark it was, unless it opens.
open-mark : ∀ {A B} {x : IE A} {m n} → opening {B = B} x ≡ instEmit (mark m) n → (m ≡ outerOpen → ⊥) → x ≡ instEmit (mark m) n
open-mark {x = instEmit (value _) _} refl no = ⊥-elim (no refl)
open-mark {x = instEmit (mark _) _}  refl _  = refl

open-value : ∀ {A B} {x : IE A} {a n} → opening {B = B} x ≡ instEmit (value a) n → ⊥
open-value {x = instEmit (value _) _} ()
open-value {x = instEmit (mark _) _}  ()

-- A stream's proper rows show their hangs as it does.
proper-shows : ∀ {A} {t : EmissionSet A} → Shows t → Shows (Proper t)
proper-shows {t = t} sh = k-shows λ n → sk-down (λ x ¬e → ¬e (_ , proj₁ x)) dn (shows-k sh)
  where
    dn : ∀ {q e k e′} → Proper t q e → t k e′ → k ≺ q → ¬ ¬ Σ _ (Proper t k)
    dn {q} {k = k} (_ , pr) x kq ¬s = ¬s (_ , x , λ {c} xc → ≺→≼ {k} {c} (≺-≼-≺ {k} {q} {c} kq (pr xc)))

-- A branch's next row is of the source's next row's instant,
named-at : ∀ J {w q} → (w ≡ q ⊎ q ≡ w ⊕ [ sub J ]) → nameOf w ≡ nameOf q
named-at J     (inj₁ refl) = refl
named-at J {w} (inj₂ refl) = cong nm (sym (rootOf-ext w [ sub J ]))

-- and no later than it.
next-≼ : ∀ J {w q} → (w ≡ q ⊎ q ≡ w ⊕ [ sub J ]) → w ≼ q
next-≼ J {w} (inj₁ refl) = ≼-refl {w}
next-≼ J {w} (inj₂ refl) = ≺→≼ {w} {w ⊕ [ sub J ]} (≺-ext w [])

-- What a branch's row opens past the scan unchanged: a value, or a completion.
data Opens {A : Set} : IE A → Set where
  o-value : ∀ {a n} → Opens (instEmit (value a) n)
  o-done  : ∀ {n} → Opens (instEmit (mark completed) n)

-- WHAT THE SCAN'S SOURCE MEETS, read past the three connects: a
-- tracker's report, a branch's row re-keyed where the branch's reader
-- subscribed it, or the end, under the scan's own subscription.
module CombSrc (m : Maybe ℕ) {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (op : FlatOp) (f : A → Obs Timeline Γ B)
               (s : Obs Timeline Γ A) (env : DenEnv Δ) (cs : List Pos) (gd : GoodEnv env) (eh : EnvHeld ρ env cs)
               (hf : ∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ (f a))
               (p : Pos) (ok : Ok (Hots env) p) (fr : Fresh eh p) (ep : Early p)
               (H₁ : Held (enter (ev m (FlatHots.trig m ρ op f s env p) (FlatHots.env₀ m ρ op f s env p)) (FlatHots.c m ρ op f s env p ⊕ [ ix 1 ]))
                          ((FlatHots.c m ρ op f s env p ⊕ [ ix 1 ]) ∷ p ∷ cs))
               (tp : Placed (Fresh eh) (FlatHots.σ₁ m ρ op f s env p))
               (L₁ : Lawful (FlatHots.σ₁ m ρ op f s env p)) (L₂ : Lawful (FlatHots.σ₂ m ρ op f s env p))
               (L₃ : Lawful (FlatHots.σ₃ m ρ op f s env p))
               (ok₁ : Ok (Hots (hot (FlatHots.σ₁ m ρ op f s env p) ∷ FlatHots.env₀ m ρ op f s env p)) (FlatHots.p₀ m ρ op f s env p))
               (ok₂ : Ok (Hots (hot (FlatHots.σ₂ m ρ op f s env p) ∷ hot (FlatHots.σ₁ m ρ op f s env p) ∷ FlatHots.env₀ m ρ op f s env p))
                         (FlatHots.p₀₀ m ρ op f s env p))
               (ok₃ : Ok (Hots (FlatHots.env′ m ρ op f s env p)) (FlatHots.P m ρ op f s env p))
               (ep₃ : Early (FlatHots.P m ρ op f s env p)) where
  open FlatHots m ρ op f s env p

  L₀ : Lawful σ₀
  L₀ = src-lawful {A = ⊤} {B = ⊤} {s = ev m empty env} {F = λ h → ev m empty (h ∷ env)} (inv-ev m empty env gd) (λ L → inv-ev m empty (hot _ ∷ env) (good-cons L gd)) p ok

  g₂ : GoodEnv (hot σ₂ ∷ hot σ₁ ∷ env₀)
  g₂ = good-cons L₂ (good-cons L₁ (good-cons L₀ gd))

  -- Admissible under the binders, past the flatMap's three connects.
  ad₂ : Adm (Hots (hot σ₂ ∷ hot σ₁ ∷ env₀)) (Fresh eh)
  ad₂ = adm-∪ {t = σ₂} (adm-∪ {t = σ₁} (adm-∪ {t = σ₀} (fresh-adm eh)))

  fr₀₀ : Fresh eh p₀₀
  fr₀₀ = Adm.bare (fresh-adm eh) (Adm.bare (fresh-adm eh) (Adm.bare (fresh-adm eh) fr λ ()) λ ()) λ ()

  fr₁ : Fresh eh (p₀₀ ⊕ [ ix 1 ])
  fr₁ = Adm.step ad₂ ok₂ fr₀₀ plain-ix

  -- The binders, read under a lane's hot.
  eh₄ : ∀ {t : EmissionSet ⊤} → EnvHeld (λ i → there (there (there (there (ρ i))))) (hot t ∷ hot σ₂ ∷ hot σ₁ ∷ env₀) cs
  eh₄ = record { bound = λ {X} i → EnvHeld.bound eh {X} i ; apart = λ {X} {Y} i j → EnvHeld.apart eh {X} {Y} i j }

  g₃ : GoodEnv env′
  g₃ = good-cons L₃ g₂

  I-M : InvAt (Hots env′) P M
  I-M = inv-ev m src env′ g₃ P ok₃

  -- Where a branch's reader ends: past its source's end.
  data BEnd : Pos → Set where
    b-outer : ∀ {c w} → σ₁ c end → BEnd (c ⊕ [ sub w ])
    b-lane  : ∀ {c w} → σ₃ c end → BEnd (c ⊕ [ sub w ])
    b-close : ∀ {c w} → σ₂ c end → BEnd (c ⊕ [ sub w ])

  data MRow : Pos → Ev (Maybe (Input B)) → Set where
    tracker : ∀ {q x} → MRow q (out (just (inj₂ x)))
    outer   : ∀ {q w x y} → σ₁ q (out x) → opening x ≡ y → MRow (q ⊕ [ sub w ]) (out (just (inj₁ (outerB , y))))
    lane    : ∀ {q w x} → σ₃ q (out x) → MRow (q ⊕ [ sub w ]) (out (just (inj₁ (laneB , x))))
    close   : ∀ {q w x} → σ₂ q (out x) → MRow (q ⊕ [ sub w ]) (out (just (inj₁ (closeB , x))))
    under   : ∀ {zs} → MRow (P ⊕ zs) end
    done    : ∀ {c zs} → BEnd c → MRow (c ⊕ zs) end

  -- WHAT EACH BRANCH SENT, row by row: a row of the outer, the closer or
  -- the lanes, one `sub` below where that branch shows it.
  outer-sent : ∀ {q y} → M q (out (just (inj₁ (outerB , y))))
             → Σ Pos λ c → Σ Pos λ w → Σ (IE A) λ x → σ₁ c (out x) × opening x ≡ y × q ≡ c ⊕ [ sub w ]
  outer-sent r with sent-branch tk env′ m P r
  ... | w , l with map-out′ opening (hot σ₁) w l
  ...   | x , l′ , refl with hot-out l′
  ...     | c′ , σc , _ , refl = c′ , w , x , σc , refl , refl

  lane-sent : ∀ {q x} → M q (out (just (inj₁ (laneB , x)))) → Σ Pos λ c → Σ Pos λ w → σ₃ c (out x) × q ≡ c ⊕ [ sub w ]
  lane-sent r with sent-branch tk env′ m P r
  ... | w , l with hot-out l
  ...   | c′ , σc , _ , refl = c′ , w , σc , refl

  close-sent : ∀ {q x} → M q (out (just (inj₁ (closeB , x)))) → Σ Pos λ c → Σ Pos λ w → σ₂ c (out x) × q ≡ c ⊕ [ sub w ]
  close-sent r with sent-branch tk env′ m P r
  ... | w , l with hot-out l
  ...   | c′ , σc , _ , refl = c′ , w , σc , refl

  track-sent : ∀ {q x} → M q (out (just (inj₂ x))) → Σ Pos λ c → Σ Pos λ w → Hots env c × q ≡ c ⊕ [ sub w ]
  track-sent r with sent-track tk env′ m P r
  ... | _ , l = trackers-out m Γ 0 (λ i → there (there (there (there (ρ i))))) env′ (Hots env)
    (λ j → _ , Bound.is (EnvHeld.bound eh j) , λ {_} {_} t → hots-at env (ρ (∈-map⁺ AIE j)) (Bound.is (EnvHeld.bound eh j)) t) l

  -- The source ends under its own subscription, or past a branch's end.
  MEnd : Pos → Set
  MEnd q = (Σ _ λ zs → q ≡ P ⊕ zs) ⊎ (Σ Pos λ c → Σ _ λ zs → BEnd c × q ≡ c ⊕ zs)

  mend-ext : ∀ {q} → MEnd q → ∀ ys → MEnd (q ⊕ ys)
  mend-ext (inj₁ (zs , refl))         ys = inj₁ (zs ++ ys , ⊕-assoc P zs ys)
  mend-ext (inj₂ (c′ , zs , b , refl)) ys = inj₂ (c′ , zs ++ ys , b , ⊕-assoc c′ zs ys)

  mend : ∀ {q} → Where P (λ b → ⟦ branch {A = A} {B} b ⟧ env′) q → MEnd q
  mend (w-under zs) = inj₁ (zs , refl)
  mend (w-past {b = outerB} zs _ (map-end (r-ended y _ , _) , _)) = inj₂ (_ , zs , b-outer y , refl)
  mend (w-past {b = outerB} zs _ (map-end (r-shown _ () _ , _) , _))
  mend (w-past {b = outerB} zs w (map-end (r-late _ _ , _) , _))  = mend-ext (mend-ext (mend w) [ last ]) zs
  mend (w-past {b = laneB} zs _ (r-ended y _ , _))                = inj₂ (_ , zs , b-lane y , refl)
  mend (w-past {b = laneB} zs _ (r-shown _ () _ , _))
  mend (w-past {b = laneB} zs w (r-late _ _ , _))                 = mend-ext (mend-ext (mend w) [ last ]) zs
  mend (w-past {b = closeB} zs _ (r-ended y _ , _))               = inj₂ (_ , zs , b-close y , refl)
  mend (w-past {b = closeB} zs _ (r-shown _ () _ , _))
  mend (w-past {b = closeB} zs w (r-late _ _ , _))                = mend-ext (mend-ext (mend w) [ last ]) zs

  m-ends : ∀ {q} → M q end → MEnd q
  m-ends x = mend (src-where tk env′ m P x)

  -- Every row the scan's source meets is one of these.
  m-rows : ∀ {q e} → M q e → Visible e → MRow q e
  m-rows {e = out (just (inj₂ _))} _ _ = tracker
  m-rows {e = out (just (inj₁ (outerB , _)))} x _ with outer-sent x
  ... | _ , _ , _ , y , o , refl = outer y o
  m-rows {e = out (just (inj₁ (laneB , _)))} x _ with lane-sent x
  ... | _ , _ , y , refl = lane y
  m-rows {e = out (just (inj₁ (closeB , _)))} x _ with close-sent x
  ... | _ , _ , y , refl = close y
  m-rows {e = out nothing} x _ = ⊥-elim (ev-none m _ env′ P x)
  m-rows {e = end} x _ with m-ends x
  ... | inj₁ (_ , refl)     = under
  ... | inj₂ (_ , _ , b , refl) = done b

  -- The lanes' rows, each as it claims, over the programs they share.
  lane-fit : Fit (Fresh eh) σ₃
  lane-fit = proper-fit (LaneReal.realE m {Fr = Fresh eh} op f (λ i → there (there (there (there (ρ i))))) σ₂ σ₁ env₀ g₂ L₁
               (λ r → Held.early H₁ (proj₁ r)) (λ r → Held.ends H₁ (proj₁ r)) tp ad₂
               (λ a {t} L q okq fq eq → held-fit (IH.holds (hf a (λ i → there (there (there (there (ρ i)))))) (hot t ∷ hot σ₂ ∷ hot σ₁ ∷ env₀) cs
                                   (good-cons L g₂) (eh₄ {t}) q okq fq eq)
                                   (IH.placed (hf a (λ i → there (there (there (there (ρ i)))))) (hot t ∷ hot σ₂ ∷ hot σ₁ ∷ env₀) cs
                                   (good-cons L g₂) (eh₄ {t}) q okq fq eq))
               (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) fr₁ (early-inst [ ix 1 ] (early-inst [ ix 0 ] (early-inst [ ix 0 ] (early-inst [ ix 0 ] ep)))))

  lane-named  : ∀ {q n} → σ₃ q (out (instEmit (mark begin) n)) → n ≡ nameOf q
  lane-named = Fit.fine lane-fit

  lane-early  : ∀ {q a n} → σ₃ q (out (instEmit (value a) n)) → Early q
  lane-early = Fit.fine lane-fit

  lane-late   : ∀ {q n} → σ₃ q (out (instEmit (mark over) n)) → Valued (rootOf q) × opos (rootOf q) ⊑ q
  lane-late = Fit.fine lane-fit

  lane-done   : ∀ {q n} → σ₃ q (out (instEmit (mark completed) n)) → Early q
  lane-done = Fit.fine lane-fit

  -- A lane's end lies before its step's over.
  lane-ends   : ∀ {q} → σ₃ q end → Early q
  lane-ends = Fit.ends lane-fit

  -- The closer ends where it is subscribed or where the outer ends.
  close-ends : ∀ {q} → σ₂ q end → Early q
  close-ends (r , _) =
    closer-good m σ₁ env₀ L₁ Early (λ e zs → early-inst zs e) (λ y → Held.ends H₁ (proj₁ y))
      (p₀ ⊕ [ ix 1 ]) (early-inst [ ix 1 ] (early-inst [ ix 0 ] (early-inst [ ix 0 ] ep))) r

  close-marks : ∀ {q x} → σ₂ q (out x) → Closing x
  close-marks (r , _) = closer-marks m (hot σ₁ ∷ env₀) _ r

  cs′ : List Pos
  cs′ = P ∷ p₀₀ ∷ p₀ ∷ c ∷ p ∷ cs

  -- THE SCAN'S COUNTERS TRACK THE BRANCHES, row by row of a run met:
  -- the routes open at a row are of its instant; a value read, a live
  -- over read, and the end find one open unless exempt; and a dead
  -- instant stays dead.
  postulate
    -- THE SCAN'S COUNTERS ARE OF THE ROW'S INSTANT, OR NONE: those an ended
    -- lane hands a queued lane's burst.
    held-current   : ∀ rx₁ {q e rx₂} → Met M (rx₁ ++ (q , e) ∷ rx₂) → Visible e
                   → Flat.held (proj₁ (past op init rx₁)) ≡ 0 ⊎ Flat.at (proj₁ (past op init rx₁)) ≡ nameOf q
    value-open    : ∀ rx₁ {q b x rx₂} → Met M (rx₁ ++ (q , out (just (inj₁ (b , x)))) ∷ rx₂) → Opens x → ¬ Ex cs′ q
                  → Σ ℕ λ k → proj₂ (from r₀ (outRows op init rx₁)) ≡ suc k
    over-open     : ∀ rx₁ {q b n rx₂} → Met M (rx₁ ++ (q , out (just (inj₁ (b , instEmit (mark over) n)))) ∷ rx₂)
                  → Flat.spent (proj₁ (past op init rx₁)) ≡ false → ¬ Ex cs′ q
                  → Σ ℕ λ k → proj₂ (from r₀ (outRows op init rx₁)) ≡ suc k
    end-open      : ∀ rx₁ {q rx₂} → Met M (rx₁ ++ (q , end) ∷ rx₂) → ¬ Ex cs′ q
                  → Σ ℕ λ k → from r₀ (outRows op init rx₁) ≡ (nameOf q , suc k)
    comb-shut     : ∀ {rx} → Met M rx → ShutRun (outRows op init rx)
    -- IDLE BETWEEN ROWS: where a reader of the scan waits on nothing before
    -- a position few rows precede, the routes it counts are of that
    -- position's instant, or none, wherever the real flatMap has few rows
    -- before.
    --
    -- REFUTED: 9e244736 `scan-idle` unrestricted, by a switch whose cut lane loops: the real flatMap never gets past the loop, while the scan reads on in the clairvoyant hot outer to the closer's `outerDone`, which keeps the outer completion's route as the counts empty, and waits in a later instant still holding it
    scan-idle     : IdleIn (Few R) scanned
    -- PAST A ZERO COUNT THE SCAN FINISHES THE INSTANT: once its count holds
    -- no route of the instant last begun, finitely many rows of it follow,
    -- outer, branches and trackers together.
    scan-rest     : Rest scanned

  -- THE READINGS UNDER THE SCAN'S SOURCE: the outer at its subscription,
  -- the closer over it, the lanes over both.
  ok₀′ : Ok (Hots env₀) c
  ok₀′ = body-ok {A = ⊤} {B = ⊤} {s = ev m empty env} {F = λ h → ev m empty (h ∷ env)} (inv-ev m empty env gd) (λ L → inv-ev m empty (hot _ ∷ env) (good-cons L gd)) p ok

  I₁ : InvAt (Hots env₀) (c ⊕ [ ix 1 ]) (enter (ev m trig env₀) (c ⊕ [ ix 1 ]))
  I₁ = inv-ev m trig env₀ (good-cons L₀ gd) (c ⊕ [ ix 1 ]) (ok-step c ok₀′)

  I₂ : InvAt (Hots (hot σ₁ ∷ env₀)) (p₀ ⊕ [ ix 1 ]) (enter (ev m (closer {B = B}) (hot σ₁ ∷ env₀)) (p₀ ⊕ [ ix 1 ]))
  I₂ = inv-ev m (closer {B = B}) (hot σ₁ ∷ env₀) (good-cons L₁ (good-cons L₀ gd)) (p₀ ⊕ [ ix 1 ]) (ok-step p₀ ok₁)

  I₃ : InvAt (Hots (hot σ₂ ∷ hot σ₁ ∷ env₀)) (p₀₀ ⊕ [ ix 1 ]) (enter (ev m real (hot σ₂ ∷ hot σ₁ ∷ env₀)) (p₀₀ ⊕ [ ix 1 ]))
  I₃ = inv-ev m real (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂)

  -- Where they subscribe: the source first, then the lanes, the closer,
  -- the outer.
  P≺q₀ : ∀ zs → (P ⊕ zs) ≺ (p₀₀ ⊕ [ ix 1 ])
  P≺q₀ zs = subst (_≺ (p₀₀ ⊕ [ ix 1 ])) (sym (⊕-assoc p₀₀ [ ix 0 ] zs)) (Equivalence.from T-≡ (<ᵖ-part p₀₀ {ix 0} {ix 1} zs [] refl))

  q₀≺s₂ : (p₀₀ ⊕ [ ix 1 ]) ≺ (p₀ ⊕ [ ix 1 ])
  q₀≺s₂ = subst (_≺ (p₀ ⊕ [ ix 1 ])) (sym (⊕-assoc p₀ [ ix 0 ] [ ix 1 ])) (Equivalence.from T-≡ (<ᵖ-part p₀ {ix 0} {ix 1} [ ix 1 ] [] refl))

  s₂≺c₁ : (p₀ ⊕ [ ix 1 ]) ≺ (c ⊕ [ ix 1 ])
  s₂≺c₁ = subst (_≺ (c ⊕ [ ix 1 ])) (sym (⊕-assoc c [ ix 0 ] [ ix 1 ])) (Equivalence.from T-≡ (<ᵖ-part c {ix 0} {ix 1} [ ix 1 ] [] refl))

  σ₁-after : ∀ {y e} → σ₁ y e → (c ⊕ [ ix 1 ]) ≺ y
  σ₁-after (r , _) = world-after (InvAt.world I₁ r) (InvAt.real I₁ r)

  -- The lanes' hot lies wholly past the source's subscription,
  lanes-past : ∀ zs {k e} → σ₃ k e → (P ⊕ zs) ≺ k
  lanes-past zs {k} (r , _) = ≺-trans {P ⊕ zs} {p₀₀ ⊕ [ ix 1 ]} {k} (P≺q₀ zs) (world-after (InvAt.world I₃ r) (InvAt.real I₃ r))

  -- and so does the outer's.
  outer-past : ∀ zs {k e} → σ₁ k e → (P ⊕ zs) ≺ k
  outer-past zs {k} r = ≺-trans {P ⊕ zs} {c ⊕ [ ix 1 ]} {k}
    (subst (_≺ (c ⊕ [ ix 1 ])) (sym (trans (⊕-assoc p₀₀ [ ix 0 ] zs) (trans (⊕-assoc p₀ [ ix 0 ] (ix 0 ∷ zs)) (⊕-assoc c [ ix 0 ] (ix 0 ∷ ix 0 ∷ zs)))))
      (Equivalence.from T-≡ (<ᵖ-part c {ix 0} {ix 1} (ix 0 ∷ ix 0 ∷ zs) [] refl)))
    (σ₁-after r)

  -- and so does the closer's.
  closer-past : ∀ zs {k e} → σ₂ k e → (P ⊕ zs) ≺ k
  closer-past zs {k} (r , _) = ≺-trans {P ⊕ zs} {p₀₀ ⊕ [ ix 1 ]} {k} (P≺q₀ zs)
    (≺-trans {p₀₀ ⊕ [ ix 1 ]} {p₀ ⊕ [ ix 1 ]} {k} q₀≺s₂ (world-after (InvAt.world I₂ r) (InvAt.real I₂ r)))

  -- The outer lies past the closer's subscription.
  outer-past₂ : ∀ zs {k e} → σ₁ k e → ((p₀ ⊕ [ ix 1 ]) ⊕ zs) ≺ k
  outer-past₂ zs {k} r = ≺-trans {(p₀ ⊕ [ ix 1 ]) ⊕ zs} {c ⊕ [ ix 1 ]} {k}
    (subst (_≺ (c ⊕ [ ix 1 ])) (sym (trans (⊕-assoc p₀ [ ix 1 ] zs) (⊕-assoc c [ ix 0 ] (ix 1 ∷ zs))))
      (Equivalence.from T-≡ (<ᵖ-part c {ix 0} {ix 1} (ix 1 ∷ zs) [] refl)))
    (σ₁-after r)

  tag-close : ∀ m′ → ev m′ (Tag tk env′ closeB) env′ ≡ Op.map (Tg closeB) (hot σ₂)
  tag-close nothing  = refl
  tag-close (just _) = refl

  cat-nothing : ∀ m′ → ev m′ (Cat-of tk env′ false) env′ ≡ Op.of (nothing ∷ [])
  cat-nothing nothing  = refl
  cat-nothing (just _) = refl

  -- A row of the source's reading is one the scan's source meets.
  toM : ∀ {q′ e′} → SrcOf (λ b → ev m (fed tk b) env′) P q′ e′ → M q′ e′
  toM {q′} {e′} = subst (λ d → enter d P q′ e′) (sym (src-op tk env′ m))

  src-func : ∀ {y e e′} → SrcOf (λ b → ev m (fed tk b) env′) P y e → SrcOf (λ b → ev m (fed tk b) env′) P y e′ → e ≡ e′
  src-func {y} {e} {e′} a b = InvAt.func (inv-ev m src env′ g₃ P ok₃)
    (subst (λ d → enter d P y e) (sym (src-op tk env′ m)) a) (subst (λ d → enter d P y e′) (sym (src-op tk env′ m)) b)

  module LS = HotSplit laneB σ₃ L₃ P (λ b → ev m (fed tk b) env′) (λ c → ev m (Cat-of tk env′ c) env′) (λ b → ev m (Tag tk env′ b) env′)
    (own-op tk env′ m) (cat-op tk env′ m) (tag-op tk env′ m) (no-track tk env′ m) (no-close tk env′ m) (λ {b} → tag-branch tk env′ m b)
    src-func lanes-past
  module OS = OuterSplit σ₁ L₁ P (λ b → ev m (fed tk b) env′) (λ c′ → ev m (Cat-of tk env′ c′) env′) (λ b → ev m (Tag tk env′ b) env′)
    (own-op tk env′ m) (cat-op tk env′ m) (tag-outer tk env′ m) (no-track tk env′ m) (no-close tk env′ m) (λ {b} → tag-branch tk env′ m b)
    src-func outer-past
  module OE = OwnEnds (λ b → ev m (fed tk b) env′) (λ c′ → ev m (Cat-of tk env′ c′) env′) (λ b → ev m (Tag tk env′ b) env′) P
    (own-op tk env′ m) (cat-op tk env′ m) (cat-nothing m)
  module CS = HotSplit closeB σ₂ L₂ P (λ b → ev m (fed tk b) env′) (λ c′ → ev m (Cat-of tk env′ c′) env′) (λ b → ev m (Tag tk env′ b) env′)
    (own-op tk env′ m) (cat-op tk env′ m) (tag-close m) (no-track tk env′ m) (no-close tk env′ m) (λ {b} → tag-branch tk env′ m b)
    src-func closer-past

  -- The lanes' rows a run of the source met are a run of the lanes.
  lane-run : ∀ {rx} → Met M rx → LS.Runs nothing nothing rx
  lane-run {rx} mt = LS.run′ (subst (λ d → Run (enter d P) nothing rx) (src-op tk env′ m) mt)

  -- Each level the source's reader of the lanes passes through shows its hangs.
  S₂ s₃ : Pos
  S₂ = LS.S₂
  s₃ = LS.s₃

  module FM2 (n : ℕ) = SJ.Flat {n = n} (Op.of (true ∷ false ∷ [])) (λ b → ev m (fed tk b) env′) (of-inv _)
    (λ b → inv-ev m (fed tk b) env′ g₃) P ok₃ (sk-of _ P) (λ b s oks → shows-k (shows-ev m (fed tk b) env′ g₃ s oks))
  module FB3 (n : ℕ) = SJ.Flat {n = n} (Op.of (true ∷ false ∷ [])) (λ c → ev m (Cat-of tk env′ c) env′) (of-inv _)
    (λ c → inv-ev m (Cat-of tk env′ c) env′ g₃) S₂ (FM2.val-ok 0 LS.o₁) (sk-of _ S₂)
    (λ c s oks → shows-k (shows-ev m (Cat-of tk env′ c) env′ g₃ s oks))
  module FM4 (n : ℕ) = SJ.Flat {n = n} (Op.of (outerB ∷ laneB ∷ closeB ∷ [])) (λ b → ev m (Tag tk env′ b) env′) (of-inv _)
    (λ b → inv-ev m (Tag tk env′ b) env′ g₃) s₃ (FB3.val-ok 0 LS.o₂) (sk-of _ s₃)
    (λ b s oks → shows-k (shows-ev m (Tag tk env′ b) env′ g₃ s oks))

  I-fed : InvAt (Hots env′) P (enter (Op.flatMap (mergeᶠ nothing) (λ b → ev m (fed tk b) env′) (Op.of (true ∷ false ∷ []))) P)
  I-fed = subst (λ d → InvAt (Hots env′) P (enter d P)) (fed-op tk env′ m) (inv-ev m (Fed tk env′) env′ g₃ P ok₃)

  sh-σ₃ : Shows σ₃
  sh-σ₃ = proper-shows {t = enter (ev m real (hot σ₂ ∷ hot σ₁ ∷ env₀)) (p₀₀ ⊕ [ ix 1 ])} (shows-ev m real (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂))

  sh-σ₂ : Shows σ₂
  sh-σ₂ = proper-shows {t = enter (ev m (closer {B = B}) (hot σ₁ ∷ env₀)) (p₀ ⊕ [ ix 1 ])} (shows-ev m (closer {B = B}) (hot σ₁ ∷ env₀) (good-cons L₁ (good-cons L₀ gd)) (p₀ ⊕ [ ix 1 ]) (ok-step p₀ ok₁))

  sh-σ₁ : Shows σ₁
  sh-σ₁ = proper-shows {t = enter (ev m trig env₀) (c ⊕ [ ix 1 ])} (shows-ev m trig env₀ (good-cons L₀ gd) (c ⊕ [ ix 1 ]) (ok-step c ok₀′))

  -- A LANE ROW BEFORE A SOURCE VALUE IS SHOWN, at most a step down.
  lane-shown : ∀ {y e q a} → σ₃ y e → LS.M′ q (out a) → (y ⊕ [ sub LS.J ]) ≼ q
             → ¬ ¬ Σ Pos λ z → Σ (Ev (Maybe (Input B))) λ e″ → LS.M′ z e″ × Step (y ⊕ [ sub LS.J ]) z × z ≼ q
               × (∀ {x} → e ≡ out x → z ≡ y ⊕ [ sub LS.J ] × e″ ≡ out (Ln x))
  lane-shown ry mq = LS.Rows.Shown.shown′ LS.dpast (k-shows λ n → FM4.sk-merge n) (k-shows λ n → FB3.Bnd.sk-bounded n 1) (k-shows λ n → FM2.sk-merge n)
    (k-shows λ n → Take.sk-takeT false going (Op.flatMap (mergeᶠ nothing) (λ b → ev m (fed tk b) env′) (Op.of (true ∷ false ∷ []))) P I-fed (sk-trunc (FM2.sk-merge n))) (λ r → proj₂ (InvAt.pinned I-fed r)) mq (LS.dshow sh-σ₃) ry

  -- NO SOURCE VALUE LIES UNDER A LANE'S ROW before where the source's
  -- reader joins it: a lane's value lies one `sub J` below its own row,
  -- and the rest one `sub` below a hot no lane row lies over.
  lane-under : ∀ {y e q a} → σ₃ y e → LS.M′ q (out a) → y ≺ q → (y ⊕ [ sub LS.J ]) ≼ q
  lane-under {y} {e} {q} {a} ry mq yq qJ = go a mq yq qJ
    where
      J = LS.J
      ⊑q : ∀ {q′} → y ≺ q′ → q′ ≺ (y ⊕ [ sub J ]) → y ⊑ q′
      ⊑q {q′} lt lt′ = <ᵖ-between y q′ [ sub J ] (Equivalence.to T-≡ lt) (Equivalence.to T-≡ lt′)
      apart : ∀ {q′ c w} → Hots (hot σ₂ ∷ hot σ₁ ∷ env₀) c → q′ ≡ c ⊕ [ sub w ] → y ≺ q′ → q′ ≺ (y ⊕ [ sub J ]) → ⊥
      apart {c = c} hc refl lt lt′ with ⊑-snoc c (⊑q lt lt′)
      ... | inj₁ yc = proj₂ (ok-step p₀₀ ok₂) hc (InvAt.world I₃ (proj₁ ry)) (⊑-inside yc)
      ... | inj₂ eq = ≺-irrefl {y} (subst (y ≺_) (sym eq) lt)
      go : ∀ {q′} a′ → LS.M′ q′ (out a′) → y ≺ q′ → q′ ≺ (y ⊕ [ sub J ]) → ⊥
      go nothing r _ _ = ev-none m _ env′ P (toM r)
      go (just (inj₂ x)) r lt lt′ with track-sent (toM r)
      ... | _ , _ , hc , eq = apart (inj₂ (inj₂ (inj₂ hc))) eq lt lt′
      go (just (inj₁ (outerB , x))) r lt lt′ with outer-sent (toM r)
      ... | _ , _ , _ , σc , _ , eq = apart (inj₂ (inj₁ (_ , σc))) eq lt lt′
      go (just (inj₁ (closeB , x))) r lt lt′ with close-sent (toM r)
      ... | _ , _ , σc , eq = apart (inj₁ (_ , σc)) eq lt lt′
      go (just (inj₁ (laneB , x))) r lt lt′ with LS.split r
      ... | _ , refl , y′ , refl , ry′ , _ with ⊑-snoc y′ (⊑q lt lt′)
      ...   | inj₂ eq = ≺-irrefl {y} (subst (y ≺_) (sym eq) lt)
      ...   | inj₁ ([] , refl) = ≺-irrefl {(y ⊕ []) ⊕ [ sub J ]} (subst (λ z → ((y ⊕ []) ⊕ [ sub J ]) ≺ (z ⊕ [ sub J ])) (sym (⊕-identityʳ y)) lt′)
      ...   | inj₁ (l ∷ ws , refl) = Lawful.flat L₃ ry ry′

  -- THE HOT ROWS UNDER AN OUTER ROW: itself, or the closer's, under one of
  -- its `sub`s naming a position at or past any `Q` at or before the
  -- closer's subscription; the environment's, never.
  module OuterRow {y e} (ry : σ₁ y e) where
    Below : Pos → Pos → Set
    Below Q z = Σ Pos λ e′ → Σ Path λ zs → z ≡ y ⊕ (sub e′ ∷ zs) × Q ≼ e′

    env-apart : ∀ {h} → Hots env₀ h → y ⊑ h → ⊥
    env-apart hc yh = proj₂ (ok-step c ok₀′) hc (InvAt.world I₁ (proj₁ ry)) (⊑-inside yh)

    σ₁-lead : ∀ {h e′} → σ₁ h e′ → y ⊑ h → h ≡ y
    σ₁-lead rh ([] , eq)      = trans eq (⊕-identityʳ y)
    σ₁-lead rh (_ ∷ _ , refl) = ⊥-elim (Lawful.flat L₁ ry rh)

    private
      hy₂ : ∀ {Q h} → Hots (hot σ₁ ∷ env₀) h → y ⊑ h → h ≡ y ⊎ Below Q h
      hy₂ (inj₁ (_ , rh)) yh = inj₁ (σ₁-lead rh yh)
      hy₂ (inj₂ hc)       yh = ⊥-elim (env-apart hc yh)

      dj₂ : ∀ {w} → W (Hots (hot σ₁ ∷ env₀)) (p₀ ⊕ [ ix 1 ]) w → w ≡ y → ⊥
      dj₂ ww refl = proj₂ (ok-step p₀ ok₁) (inj₁ (_ , ry)) ww (⊑-inside ([] , sym (⊕-identityʳ y)))

      sy₂ : y ⊑ (p₀ ⊕ [ ix 1 ]) → ⊥
      sy₂ ys = ⊑-≼ {y} {p₀ ⊕ [ ix 1 ]} ys (≺-trans {p₀ ⊕ [ ix 1 ]} {c ⊕ [ ix 1 ]} {y} s₂≺c₁ (σ₁-after ry))

    in-σ₂ : ∀ Q → Q ≼ (p₀ ⊕ [ ix 1 ]) → ∀ {h e′} → σ₂ h e′ → y ⊑ h → Below Q h
    in-σ₂ Q qs (r , _) = under-hot {H = Hots (hot σ₁ ∷ env₀)} {s = p₀ ⊕ [ ix 1 ]} {q = Q} {y = y} qs (λ {h} → hy₂ {Q} {h}) dj₂ sy₂
                           (InvAt.world I₂ r) (InvAt.real I₂ r)

    hots-under : ∀ Q → Q ≼ (p₀ ⊕ [ ix 1 ]) → ∀ {h} → Hots (hot σ₂ ∷ hot σ₁ ∷ env₀) h → y ⊑ h → h ≡ y ⊎ Below Q h
    hots-under Q qs (inj₁ (_ , r₂))        yh = inj₂ (in-σ₂ Q qs r₂ yh)
    hots-under Q qs (inj₂ (inj₁ (_ , rh))) yh = inj₁ (σ₁-lead rh yh)
    hots-under Q qs (inj₂ (inj₂ hc))       yh = ⊥-elim (env-apart hc yh)

  -- NO SOURCE VALUE LIES UNDER AN OUTER ROW before where the source's
  -- reader joins it: the outer's value lies one `sub J` below its own row;
  -- the closer and the lanes reach inside an outer row only by joining it
  -- past their own subscriptions, so past `J`; a tracker, never.
  outer-under : ∀ {y e q a} → σ₁ y e → OS.M′ q (out a) → y ≺ q → (y ⊕ [ sub OS.J ]) ≼ q
  outer-under {y} {e} {q} {a} ry mq yq qJ = go a mq yq qJ
    where
      J q₀ Y : Pos
      J  = OS.J
      q₀ = p₀₀ ⊕ [ ix 1 ]
      Y  = y ⊕ [ sub J ]

      open OuterRow ry

      U : Pos → Set
      U = Below q₀

      ⊑q : ∀ {q′} → y ≺ q′ → q′ ≺ Y → y ⊑ q′
      ⊑q {q′} lt lt′ = <ᵖ-between y q′ [ sub J ] (Equivalence.to T-≡ lt) (Equivalence.to T-≡ lt′)

      lead : ∀ {c′ w} → y ≺ (c′ ⊕ [ sub w ]) → (c′ ⊕ [ sub w ]) ≺ Y → y ⊑ c′
      lead {c′} {w} lt lt′ with ⊑-snoc c′ (⊑q {c′ ⊕ [ sub w ]} lt lt′)
      ... | inj₁ yc = yc
      ... | inj₂ eq = ⊥-elim (≺-irrefl {y} (subst (y ≺_) (sym eq) lt))

      dj₃ : ∀ {w} → W (Hots (hot σ₂ ∷ hot σ₁ ∷ env₀)) q₀ w → w ≡ y → ⊥
      dj₃ ww refl = proj₂ (ok-step p₀₀ ok₂) (inj₂ (inj₁ (_ , ry))) ww (⊑-inside ([] , sym (⊕-identityʳ y)))

      sy₃ : y ⊑ q₀ → ⊥
      sy₃ ys = ⊑-≼ {y} {q₀} ys (≺-trans {q₀} {p₀ ⊕ [ ix 1 ]} {y} q₀≺s₂ (≺-trans {p₀ ⊕ [ ix 1 ]} {c ⊕ [ ix 1 ]} {y} s₂≺c₁ (σ₁-after ry)))

      q₀≼s₂ : q₀ ≼ (p₀ ⊕ [ ix 1 ])
      q₀≼s₂ = ≺→≼ {q₀} {p₀ ⊕ [ ix 1 ]} q₀≺s₂

      hy₃ : ∀ {h} → Hots (hot σ₂ ∷ hot σ₁ ∷ env₀) h → y ⊑ h → h ≡ y ⊎ U h
      hy₃ = hots-under q₀ q₀≼s₂

      -- and the lanes'.
      in-σ₃ : ∀ {h e′} → σ₃ h e′ → y ⊑ h → U h
      in-σ₃ (r , _) = under-hot {H = Hots (hot σ₂ ∷ hot σ₁ ∷ env₀)} {s = q₀} {q = q₀} {y = y} (≼-refl {q₀}) hy₃ dj₃ sy₃
                        (InvAt.world I₃ r) (InvAt.real I₃ r)

      J≺q₀ : J ≺ q₀
      J≺q₀ = subst (_≺ q₀) (sym (proj₂ OS.J-under)) (P≺q₀ (proj₁ OS.J-under))

      past-Y : ∀ {c′ w} → U c′ → Y ≺ (c′ ⊕ [ sub w ])
      past-Y {w = w} (e′ , zs , refl , qe) =
        subst (Y ≺_) (sym (⊕-assoc y (sub e′ ∷ zs) [ sub w ]))
          (Equivalence.from T-≡ (<ᵖ-part y {sub J} {sub e′} [] (zs ++ [ sub w ]) (Equivalence.to T-≡ (≺-≼-≺ {J} {q₀} {e′} J≺q₀ qe))))

      sent : ∀ {q′ c′ w} → q′ ≡ c′ ⊕ [ sub w ] → (y ⊑ c′ → U c′) → y ≺ q′ → q′ ≺ Y → ⊥
      sent {c′ = c′} {w} refl un lt lt′ = ≺-absurd {c′ ⊕ [ sub w ]} {Y} lt′ (past-Y {c′} {w} (un (lead {c′} {w} lt lt′)))

      apart : ∀ {q′ c′ w} → Hots env₀ c′ → q′ ≡ c′ ⊕ [ sub w ] → y ≺ q′ → q′ ≺ Y → ⊥
      apart {c′ = c′} {w} hc refl lt lt′ = env-apart hc (lead {c′} {w} lt lt′)

      go : ∀ {q′} a′ → OS.M′ q′ (out a′) → y ≺ q′ → q′ ≺ Y → ⊥
      go nothing r _ _ = ev-none m _ env′ P (toM r)
      go (just (inj₂ x)) r lt lt′ with track-sent (toM r)
      ... | _ , _ , hc , eq = apart (inj₂ hc) eq lt lt′
      go (just (inj₁ (laneB , x))) r lt lt′ with lane-sent (toM r)
      ... | _ , _ , σc , eq = sent eq (in-σ₃ σc) lt lt′
      go (just (inj₁ (closeB , x))) r lt lt′ with close-sent (toM r)
      ... | _ , _ , σc , eq = sent eq (in-σ₂ q₀ q₀≼s₂ σc) lt lt′
      go (just (inj₁ (outerB , x))) r lt lt′ with OS.split r
      ... | _ , refl , y′ , refl , ry′ , _ with ⊑-snoc y′ (⊑q lt lt′)
      ...   | inj₂ eq = ≺-irrefl {y} (subst (y ≺_) (sym eq) lt)
      ...   | inj₁ ([] , refl) = ≺-irrefl {(y ⊕ []) ⊕ [ sub J ]} (subst (λ z → ((y ⊕ []) ⊕ [ sub J ]) ≺ (z ⊕ [ sub J ])) (sym (⊕-identityʳ y)) lt′)
      ...   | inj₁ (l ∷ ws , refl) = Lawful.flat L₁ ry ry′

  -- AN OUTER ROW BEFORE A SOURCE VALUE IS SHOWN, at most a step down.
  outer-shown : ∀ {y e q a} → σ₁ y e → OS.M′ q (out a) → (y ⊕ [ sub OS.J ]) ≼ q
              → ¬ ¬ Σ Pos λ z → Σ (Ev (Maybe (Input B))) λ e″ → OS.M′ z e″ × Step (y ⊕ [ sub OS.J ]) z × z ≼ q
                × (∀ {x} → e ≡ out x → z ≡ y ⊕ [ sub OS.J ] × e″ ≡ out (OS.g x))
  outer-shown ry mq = OS.Rows.Shown.shown′ OS.dpast (k-shows λ n → FM4.sk-merge n) (k-shows λ n → FB3.Bnd.sk-bounded n 1) (k-shows λ n → FM2.sk-merge n)
    (k-shows λ n → Take.sk-takeT false going (Op.flatMap (mergeᶠ nothing) (λ b → ev m (fed tk b) env′) (Op.of (true ∷ false ∷ []))) P I-fed (sk-trunc (FM2.sk-merge n))) (λ r → proj₂ (InvAt.pinned I-fed r)) mq (OS.dshow sh-σ₁) ry

  module LN = LS.Next lane-shown lane-under
  module ON = OS.Next outer-shown outer-under

  opaque
    lane-next : ∀ rx₁ {q a rx₂} → Met M (rx₁ ++ (q , out a) ∷ rx₂)
              → Σ _ λ rs → BProj laneB (λ x → x) LS.J rx₁ rs × Met σ₃ rs × Σ Pos λ w → (w ≡ q ⊎ q ≡ w ⊕ [ sub LS.J ]) × LN.NextAt (cursor nothing rs) w
    lane-next rx₁ {q} {a} {rx₂} mt = LN.next-at {rx₁} {q} {a} {rx₂} (lane-run (run-prefix rx₁ mt))
      (run-tail rx₁ (subst (λ d → Run (enter d P) nothing (rx₁ ++ (q , out a) ∷ rx₂)) (src-op tk env′ m) mt)) (bview laneB (out a))

  -- The outer's next row past what the source met.
  opaque
    outer-next : ∀ rx₁ {q a rx₂} → Met M (rx₁ ++ (q , out a) ∷ rx₂)
               → Σ _ λ rs → BProj outerB (opening {A} {B}) OS.J rx₁ rs × Met σ₁ rs
                 × Σ Pos λ w → (w ≡ q ⊎ q ≡ w ⊕ [ sub OS.J ]) × ON.NextAt (cursor nothing rs) w
    outer-next rx₁ {q} {a} {rx₂} mt = ON.next-at {rx₁} {q} {a} {rx₂} (OS.run′ (subst (λ d → Run (enter d P) nothing rx₁) (src-op tk env′ m) (run-prefix rx₁ mt)))
      (run-tail rx₁ (subst (λ d → Run (enter d P) nothing (rx₁ ++ (q , out a) ∷ rx₂)) (src-op tk env′ m) mt)) (bview outerB (out a))

  -- The outer's counter is none, or of the name the outer last began,
  -- with a route of it open.
  outer-count : ∀ {rx rs} → Met M rx → BProj outerB (opening {A} {B}) OS.J rx rs
              → Flat.outer (proj₁ (past op init rx)) ≡ 0
              ⊎ Flat.at (proj₁ (past op init rx)) ≡ proj₁ (cnt rs) × Σ ℕ λ k → proj₂ (cnt rs) ≡ suc k
  outer-count {rx} {rs} mt pr =
    within-of (past-within {A} {B} co (opening {A} {B}) count-open OS.J op init r₀ rx rs
      (λ r₁ r₂ eq → end-last (inv-ev m src env′ g₃ P ok₃) r₁ (subst (Met M) eq mt)) pr (within₀ {B} outerB r₀))

  -- The outer's proper rows are idle where the outer is.
  outer-idle : Idle σ₁
  outer-idle = proper-idle {S = enter (ev m trig env₀) (c ⊕ [ ix 1 ])} (λ sc sy cy → pinby-silent (InvAt.quiet I₁ sc sy cy)) (InvAt.func I₁) (Held.idle H₁)

  -- THE CLOSER TELLS THE OUTER'S END IN ITS INSTANT (`simultaneous.CloseDone`):
  -- its `outerDone` lies there, before each of its ends; the source shows
  -- it wherever it shows a later row.
  module CD = CloseDone m {B = B} σ₁ env₀ L₁ (p₀ ⊕ [ ix 1 ]) outer-past₂

  Io₂ : InvAt (Hots (hot σ₁ ∷ env₀)) (p₀ ⊕ [ ix 1 ]) (enter (Op.of (true ∷ false ∷ [])) (p₀ ⊕ [ ix 1 ]))
  Io₂ = of-inv (true ∷ false ∷ []) (p₀ ⊕ [ ix 1 ]) (ok-step p₀ ok₁)

  I-D₀ : InvAt (Hots (hot σ₁ ∷ env₀)) CD.s₁ (enter CD.D₀ CD.s₁)
  I-D₀ = subst (λ d → InvAt (Hots (hot σ₁ ∷ env₀)) CD.s₁ (enter d CD.s₁)) CD.first-op
    (inv-ev m (Clo true) (hot σ₁ ∷ env₀) (good-cons L₁ (good-cons L₀ gd)) CD.s₁
      (ok-step CD.q₀ (ok-in (ok-step p₀ ok₁) (InvAt.world Io₂ CD.o₀) (InvAt.real Io₂ CD.o₀))))

  few-σ₁ : ∀ {y} → σ₁ y end → Few σ₁ y
  few-σ₁ (r , _) with entered-few (ev m trig env₀) (c ⊕ [ ix 1 ]) {e = end} (λ {_} {_} → tt) r
  ... | ks , h = ks , λ x lt → h (proj₁ x) lt

  mq′ : ∀ {q a} → M q (out a) → CS.M′ q (out a)
  mq′ {q} {a} = subst (λ d → enter d P q (out a)) (src-op tk env′ m)

  close-done : ∀ {y q a} → σ₁ y end → M q (out a) → y ≺ q
             → ¬ ¬ Σ Pos λ z → instantOf z ≡ instantOf y
               × (q ≼ z ⊎ Σ Pos λ n → M z (out (just (inj₁ (closeB , instEmit (mark outerDone) n)))) × z ≺ q)
  close-done {y} {q} ry mq _ ¬g = go (CD.FirstEnd.closer-row ry (few-σ₁ ry) (InvAt.flat I-D₀))
    where
      go : Σ Pos (λ z₁ → instantOf z₁ ≡ instantOf y × enter (ev m (closer {B = B}) (hot σ₁ ∷ env₀)) (p₀ ⊕ [ ix 1 ]) z₁ (out (marked {B} outerDone))
             × (∀ {c} → enter (ev m (closer {B = B}) (hot σ₁ ∷ env₀)) (p₀ ⊕ [ ix 1 ]) c end → z₁ ≺ c)) → ⊥
      go (z₁ , zy , r₁ , aft) = [ shown , later ]′ (≼-or-≻ (z₁ ⊕ [ sub CS.J ]) q)
        where
          zy′ : instantOf (z₁ ⊕ [ sub CS.J ]) ≡ instantOf y
          zy′ = trans (inst-⊕ z₁ [ sub CS.J ]) zy

          later : q ≺ (z₁ ⊕ [ sub CS.J ]) → ⊥
          later qz = ¬g (z₁ ⊕ [ sub CS.J ] , zy′ , inj₁ (≺→≼ {q} {z₁ ⊕ [ sub CS.J ]} qz))

          case : ∀ {z e″} → z ≡ z₁ ⊕ [ sub CS.J ] × e″ ≡ out (CS.g (marked {B} outerDone)) → z ≼ q → CS.M′ z e″ → ⊥
          case (refl , refl) z≼q m′ with ≼-split {z₁ ⊕ [ sub CS.J ]} {q} z≼q
          ... | inj₁ lt = ¬g (z₁ ⊕ [ sub CS.J ] , zy′ , inj₂ (_ , toM m′ , lt))
          ... | inj₂ eq = ¬g (z₁ ⊕ [ sub CS.J ] , zy′ , inj₁ (subst (q ≼_) (sym eq) (≼-refl {q})))

          shown : (z₁ ⊕ [ sub CS.J ]) ≼ q → ⊥
          shown zq = CS.Rows.Shown.shown′ CS.dpast (k-shows λ n → FM4.sk-merge n) (k-shows λ n → FB3.Bnd.sk-bounded n 1) (k-shows λ n → FM2.sk-merge n)
            (k-shows λ n → Take.sk-takeT false going (Op.flatMap (mergeᶠ nothing) (λ b → ev m (fed tk b) env′) (Op.of (true ∷ false ∷ []))) P I-fed (sk-trunc (FM2.sk-merge n)))
            (λ r → proj₂ (InvAt.pinned I-fed r)) (mq′ mq) (CS.dshow sh-σ₂) (r₁ , λ sc → ≺→≼ {z₁} {_} (aft sc)) zq
            λ (z , e″ , m′ , _ , z≼q , pr) → case (pr refl) z≼q m′
