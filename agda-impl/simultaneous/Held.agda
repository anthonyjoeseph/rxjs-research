{-# OPTIONS --guardedness #-}

-- EVERY ELABORATED STREAM HOLDS (`simultaneous.Routed.Held`), former by
-- former, and so the batcher's source keeps its dead instants dead.
--
-- A `defer` is reached through its approximants: each is a finite tree,
-- so the formers' leaves hold of it by induction on the bound, and the
-- meaning is their limit.
module simultaneous.Held where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (lookup; _∷_) renaming ([] to []ᵉ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Obs; Later; FlatOp; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected;
  defer; mergeᶠ)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; sub; last; _⊕_; _∙_; frame; cascade)
open import denotation.Events using (Timeline)
open import denotation.EmissionSet using (hot; enter; ⟦_⟧; DenEnv; approx; module Op)
open import simultaneous.SObs using (SObs; plain; ext)
open import simultaneous.Relations using (elaborated)
open import simultaneous.Shut using (Shut)
open import simultaneous.Routed using (Held; Early)
open import denotation.Laws.Worlds using (Hots; GoodEnv)
open import simultaneous.Relabel using (same-mark; same-value)
open import simultaneous.HeldWrap using (held-wrapped)
open import simultaneous.HeldScan using (held-scan-at; Relabels)
open import simultaneous.HeldDefer using (held-defer)
open import simultaneous.LaneLocal using (inv-ev; late-ext; Fit; proper-fit; held-fit; module LaneReal)
open import simultaneous.HeldTrigger using (held-trigger)
open import simultaneous.CombRun using (comb-run)
open import simultaneous.CombSent using (src-op; own-op; cat-op; tag-op; no-track; no-close; tag-branch; Cat-of; Tag; sent-branch; Closing; closing-mark; closing-value; closer-marks; closer-good; src-where; Where) renaming (under to w-under; past to w-past)
open import denotation.EmissionSet using (map-end) renaming (ended to r-ended; late to r-late; shown to r-shown)
open import denotation.Laws.Worlds using (⊕-assoc)
open import simultaneous.DenRows using (map-out′; hot-out)
open import simultaneous.HeldConnect using (early-inst; tracks-fin)
open import denotation.Laws using (good-cons)
open import denotation.Laws.Worlds using (Ok; Lawful)
open import denotation.Laws.Connect using () renaming (lawful to src-lawful; ok₀ to body-ok)
open import Data.Empty using (⊥)
open import Data.List.Relation.Unary.Any using (here; there)
open import simultaneous.InstEmit using (begin)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import simultaneous.FlatPark using (past-park)
open import simultaneous.BranchSplit using (SrcOf; BView; isB; notB; bview)
open import simultaneous.LaneSplit using (Ln; lane-proj; module LaneSplit)
import denotation.Laws.ShowsJoin as SJ
open import denotation.Laws.ShowsOps using (sk-of; module Take)
open import denotation.Laws.Shows using (Step; k-shows; shows-k; sk-down; sk-trunc)
open import denotation.Laws.Worlds.Leaves using (of-inv)
open import denotation.Laws.Worlds using (Shows; Hots)
open import denotation.Laws.Modulus using (≺→≼; ≺-≼-≺)
open import simultaneous.CombSent using (fed-op; Fed; sent-track; trackers-out; hots-at)
open import simultaneous.HeldBase using (Bound)
open import denotation.Laws.Worlds using (⊑-snoc; ⊕-identityʳ)
open import denotation.Events using (<ᵖ-between)
open import denotation.Laws.Modulus using (≺-irrefl)
open import simultaneous.FlatLanes using (laneTag; end-last; BProj; past-within; within-of; within₀; cl)
open import denotation.Up using (up; up-⊕)
open import denotation.Laws.Shows using (∈-stable)
open import denotation.Laws.Modulus using (≺-ext)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import denotation.Position using (_<ᵖ_)
open import denotation.Laws.Modulus using (≼-split)
open import simultaneous.HeldBase using (shows-ev; EnvHeld; module FlatHots; IH; module Quiet; conn-ev; empty-few; ev-none; held-cold; held-connect; held-connected; held-empty; held-map; held-of; held-scan; held-takeWhile; ih)
open import denotation.Events using (Timeline; fresh)
open import simultaneous.SObs using (SObs; plain; lone; ext; module Elaborate)
open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; count; elab; srcLane; laneSrc; annotate; marked; trackers; closer; combined; laneˢ; each; coldˢ;
  Input; react; going; fed; opening; anyHolds; branch; restamp; wrapped)
open import simultaneous.HeldComb using (ev; CombIn; RunHeld; ShutRun; outRows; init; from; past; lay; Local; Locals;
  locals-runs; local-end; run-row; walk; inv-past; step-local; Laid; laid; ended; laid-in; runs-prefix; held-runs)
open import simultaneous.FlatSim using (react-sent; passed; routed; minted; NoCB; tot)
open import simultaneous.HeldComb using (exact-past; inv-at)
open import simultaneous.Reach using (module Reached)
open import simultaneous.Routed using (valued; Idle; Rest; Routing; r-begin; r-stop; r-over; r-subscribed; r-completed)
open import Relation.Nullary.Decidable using (decidable-stable)
open import Data.Bool.Properties using (T?)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import denotation.Laws.Worlds using (inside-⊑; ⊑-inside)
open import simultaneous.InstEmit using (stop; subscribed; completed; laneStart; carry; laneDone; burstEnd)
open import simultaneous.Shut using (r₀)
open import simultaneous.SObs using (Flat)
open import simultaneous.Routed using (Ex)
open import Relation.Nullary using (¬_)
import Relation.Nullary as Nl
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; proj₂)
open import simultaneous.SObs using (outerB; laneB; closeB)
open import simultaneous.InstEmit using (instEmit; value; mark; over; outerOpen; outerClose; outerDone)
open import simultaneous.Routed using (nameOf; nm; Valued; opos)
open import simultaneous.Layers using (run-tail) renaming (run-row to run-row∈)
open import simultaneous.Readings using (rootOf)
open import simultaneous.Relations using (Met)
open import simultaneous.HeldConnect using (rootOf-ext)
open import denotation.Read using (Visible)
open import denotation.EmissionSet using (Ev; out; end)
open import denotation.Laws.Worlds using (ok-step; _⊑_; InvAt; world-after)
open import denotation.Laws.Modulus using (≺-trans)
open import denotation.Events using (<ᵖ-part)
open import Data.Bool.Properties using (T-≡)
open import Function using (Equivalence)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (trans; sym; cong; subst)
open import Data.Bool using (true; false)
open import simultaneous.Project using (Proj; run-prefix)
open import denotation.EmissionSet using (Few; _≼_)
open import denotation.Read using (After; cursor; Run)
import denotation.Read as Run
import Data.Nat as ℕ
import Data.Nat.Properties as ℕP
import denotation.EmissionSet as ES
open import denotation.Laws.Truthful using (reached)
open import denotation.EmissionSet using (EmissionSet; Proper)
open import denotation.Laws.Modulus using (≺-absurd; ≼-refl)
open import denotation.Laws.Worlds using (W; ⊑-≼; pinby-silent)
open import denotation.Position using (Path)
open import denotation.Laws.HotBelow using (under-hot)
open import simultaneous.OuterSplit using (count-open; module OuterSplit)
open import simultaneous.ProperIdle using (proper-idle)
open import simultaneous.FlatLanes using (co; bproj-end)
open import simultaneous.CombSent using (tag-outer)
open import simultaneous.HeldLim using (module LimHeld)
open import denotation.EmissionSet using (_≺_)
open import simultaneous.Routed using (cnt)
open import simultaneous.HeldComb using (ShutRun)
open import denotation.EmissionSet using (spin)
open import simultaneous.HeldComb using (RunHeld)
open import Data.Nat using (ℕ; suc)

open import Tree using (Obs; FlatOp; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; last; _⊕_; _∙_; cascade)
open import simultaneous.SObs using (lone; ext; module Elaborate)
open import simultaneous.HeldConnect using (early-inst)

open import simultaneous.HeldComb using (ev; RunHeld; ShutRun; run-row; held-runs)
open import simultaneous.Routed using (valued; Idle; Rest; Routing; r-begin; r-over)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ)
open import denotation.Laws.Worlds using (⊑-inside)
open import simultaneous.InstEmit using (stop; completed)
open import simultaneous.InstEmit using (instEmit; value; mark; over)
open import denotation.Laws.Worlds using (ok-step; _⊑_)
open import Relation.Binary.PropositionalEquality using (sym; cong; subst)
open import denotation.Read using (Run)

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
               (p : Pos) (ok : Ok (Hots env) p) (ep : Early p)
               (H₁ : Held (enter (ev m (FlatHots.trig m ρ op f s env p) (FlatHots.env₀ m ρ op f s env p)) (FlatHots.c m ρ op f s env p ⊕ [ ix 1 ]))
                          ((FlatHots.c m ρ op f s env p ⊕ [ ix 1 ]) ∷ p ∷ cs))
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

  g₃ : GoodEnv env′
  g₃ = good-cons L₃ g₂

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
    (λ j → _ , Bound.is (eh j) , λ {_} {_} t → hots-at env (ρ (∈-map⁺ AIE j)) (Bound.is (eh j)) t) l

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
  lane-fit : Fit σ₃
  lane-fit = proper-fit (LaneReal.realE m op f (λ i → there (there (there (there (ρ i))))) σ₂ σ₁ env₀ g₂ L₁
               (λ r → Held.early H₁ (proj₁ r)) (λ r → Held.ends H₁ (proj₁ r))
               (λ a L q okq eq → held-fit (IH.holds (hf a (λ i → there (there (there (there (ρ i)))))) (hot _ ∷ hot σ₂ ∷ hot σ₁ ∷ env₀) cs
                                   (good-cons L g₂) eh q okq eq))
               (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) (early-inst [ ix 1 ] (early-inst [ ix 0 ] (early-inst [ ix 0 ] (early-inst [ ix 0 ] ep)))))

  lane-named  : ∀ {q n} → σ₃ q (out (instEmit (mark begin) n)) → n ≡ nameOf q
  lane-named = Fit.fine lane-fit

  lane-early  : ∀ {q a n} → σ₃ q (out (instEmit (value a) n)) → Early q
  lane-early = Fit.fine lane-fit

  lane-late   : ∀ {q n} → σ₃ q (out (instEmit (mark over) n)) → Valued (rootOf q) × opos (rootOf q) ⊑ q
  lane-late = Fit.fine lane-fit

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
    -- position's instant, or none.
    scan-idle     : Idle scanned
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

  -- A row of the source's reading is one the scan's source meets.
  toM : ∀ {q′ e′} → SrcOf (λ b → ev m (fed tk b) env′) P q′ e′ → M q′ e′
  toM {q′} {e′} = subst (λ d → enter d P q′ e′) (sym (src-op tk env′ m))

  src-func : ∀ {y e e′} → SrcOf (λ b → ev m (fed tk b) env′) P y e → SrcOf (λ b → ev m (fed tk b) env′) P y e′ → e ≡ e′
  src-func {y} {e} {e′} a b = InvAt.func (inv-ev m src env′ g₃ P ok₃)
    (subst (λ d → enter d P y e) (sym (src-op tk env′ m)) a) (subst (λ d → enter d P y e′) (sym (src-op tk env′ m)) b)

  private
    module LS = LaneSplit σ₃ L₃ P (λ b → ev m (fed tk b) env′) (λ c → ev m (Cat-of tk env′ c) env′) (λ b → ev m (Tag tk env′ b) env′)
      (own-op tk env′ m) (cat-op tk env′ m) (tag-op tk env′ m) (no-track tk env′ m) (no-close tk env′ m) (λ {b} → tag-branch tk env′ m b)
      src-func lanes-past
    module OS = OuterSplit σ₁ L₁ P (λ b → ev m (fed tk b) env′) (λ c′ → ev m (Cat-of tk env′ c′) env′) (λ b → ev m (Tag tk env′ b) env′)
      (own-op tk env′ m) (cat-op tk env′ m) (tag-outer tk env′ m) (no-track tk env′ m) (no-close tk env′ m) (λ {b} → tag-branch tk env′ m b)
      src-func outer-past

  -- The lanes' rows a run of the source met are a run of the lanes.
  lane-run : ∀ {rx} → Met M rx → LS.Runs nothing nothing rx
  lane-run {rx} mt = LS.run′ (subst (λ d → Run (enter d P) nothing rx) (src-op tk env′ m) mt)

  -- Each level the source's reader of the lanes passes through shows its hangs.
  private
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
    sh-σ₃ = proper-shows (shows-ev m real (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂))

    sh-σ₁ : Shows σ₁
    sh-σ₁ = proper-shows (shows-ev m trig env₀ (good-cons L₀ gd) (c ⊕ [ ix 1 ]) (ok-step c ok₀′))

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

  postulate
    -- THE LANES END WITH THE SCAN HOLDING NONE OF THEIR ROUTES: where the
    -- lanes' next row past what the source met is their end, every lane has
    -- sent its `laneDone`, its routes stopped, ended or handed on.
    --
    -- REFUTED: cf901010 lane-end-shut over the lanes' own count, by a lane whose inner completes asynchronously: its completion's begin is carried, never stopped
    lane-end-shut : ∀ rx₁ {q a rx₂ rs y} → Met M (rx₁ ++ (q , out a) ∷ rx₂) → Proj laneTag rx₁ rs → σ₃ y end → After (cursor nothing rs) y
                  → (∀ {k x} → σ₃ k (out x) → After (cursor nothing rs) k → y ≼ k) → Flat.lanes (proj₁ (past op init rx₁)) ≡ 0

    -- WHILE THE SCAN STILL COUNTS A LANE ROUTE, THE LANES' NEXT ROW IS OF
    -- THEIR INSTANT: the instant the lanes' own count names, past a run of
    -- them, is that of any position before every lane row still to come.
    --
    -- REFUTED: 1e9665c7 lane-idle as the lanes' own `Idle`, by a merge whose first lane completes asynchronously while a second is pending: the completion's begin is carried, so the lanes' count keeps its instant as the second lane begins another
    lane-idle : ∀ rx₁ {q a rx₂ rs} → Met M (rx₁ ++ (q , out a) ∷ rx₂) → Proj laneTag rx₁ rs → ¬ Flat.lanes (proj₁ (past op init rx₁)) ≡ 0
              → ∀ {w} → Few σ₃ w → After (cursor nothing rs) w → (∀ {y e} → σ₃ y e → Visible e → After (cursor nothing rs) y → w ≼ y)
              → proj₁ (cnt rs) ≡ nameOf w

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

      U : Pos → Set
      U z = Σ Pos λ e′ → Σ Path λ zs → z ≡ y ⊕ (sub e′ ∷ zs) × q₀ ≼ e′

      ⊑q : ∀ {q′} → y ≺ q′ → q′ ≺ Y → y ⊑ q′
      ⊑q {q′} lt lt′ = <ᵖ-between y q′ [ sub J ] (Equivalence.to T-≡ lt) (Equivalence.to T-≡ lt′)

      lead : ∀ {c′ w} → y ≺ (c′ ⊕ [ sub w ]) → (c′ ⊕ [ sub w ]) ≺ Y → y ⊑ c′
      lead {c′} {w} lt lt′ with ⊑-snoc c′ (⊑q {c′ ⊕ [ sub w ]} lt lt′)
      ... | inj₁ yc = yc
      ... | inj₂ eq = ⊥-elim (≺-irrefl {y} (subst (y ≺_) (sym eq) lt))

      env-apart : ∀ {h} → Hots env₀ h → y ⊑ h → ⊥
      env-apart hc yh = proj₂ (ok-step c ok₀′) hc (InvAt.world I₁ (proj₁ ry)) (⊑-inside yh)

      σ₁-lead : ∀ {h e′} → σ₁ h e′ → y ⊑ h → h ≡ y
      σ₁-lead rh ([] , eq)      = trans eq (⊕-identityʳ y)
      σ₁-lead rh (_ ∷ _ , refl) = ⊥-elim (Lawful.flat L₁ ry rh)

      self : y ⊑ y
      self = [] , sym (⊕-identityʳ y)

      dj₂ : ∀ {w} → W (Hots (hot σ₁ ∷ env₀)) (p₀ ⊕ [ ix 1 ]) w → w ≡ y → ⊥
      dj₂ ww refl = proj₂ (ok-step p₀ ok₁) (inj₁ (_ , ry)) ww (⊑-inside self)

      dj₃ : ∀ {w} → W (Hots (hot σ₂ ∷ hot σ₁ ∷ env₀)) q₀ w → w ≡ y → ⊥
      dj₃ ww refl = proj₂ (ok-step p₀₀ ok₂) (inj₂ (inj₁ (_ , ry))) ww (⊑-inside self)

      sy₂ : y ⊑ (p₀ ⊕ [ ix 1 ]) → ⊥
      sy₂ ys = ⊑-≼ {y} {p₀ ⊕ [ ix 1 ]} ys (≺-trans {p₀ ⊕ [ ix 1 ]} {c ⊕ [ ix 1 ]} {y} s₂≺c₁ (σ₁-after ry))

      sy₃ : y ⊑ q₀ → ⊥
      sy₃ ys = ⊑-≼ {y} {q₀} ys (≺-trans {q₀} {p₀ ⊕ [ ix 1 ]} {y} q₀≺s₂ (≺-trans {p₀ ⊕ [ ix 1 ]} {c ⊕ [ ix 1 ]} {y} s₂≺c₁ (σ₁-after ry)))

      hy₂ : ∀ {h} → Hots (hot σ₁ ∷ env₀) h → y ⊑ h → h ≡ y ⊎ U h
      hy₂ (inj₁ (_ , rh)) yh = inj₁ (σ₁-lead rh yh)
      hy₂ (inj₂ hc)       yh = ⊥-elim (env-apart hc yh)

      -- The closer's rows under `y`,
      in-σ₂ : ∀ {h e′} → σ₂ h e′ → y ⊑ h → U h
      in-σ₂ (r , _) = under-hot {H = Hots (hot σ₁ ∷ env₀)} {s = p₀ ⊕ [ ix 1 ]} {q = q₀} {y = y} (≺→≼ {q₀} {p₀ ⊕ [ ix 1 ]} q₀≺s₂) hy₂ dj₂ sy₂
                        (InvAt.world I₂ r) (InvAt.real I₂ r)

      hy₃ : ∀ {h} → Hots (hot σ₂ ∷ hot σ₁ ∷ env₀) h → y ⊑ h → h ≡ y ⊎ U h
      hy₃ (inj₁ (_ , r₂))        yh = inj₂ (in-σ₂ r₂ yh)
      hy₃ (inj₂ (inj₁ (_ , rh))) yh = inj₁ (σ₁-lead rh yh)
      hy₃ (inj₂ (inj₂ hc))       yh = ⊥-elim (env-apart hc yh)

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
      ... | _ , _ , σc , eq = sent eq (in-σ₂ σc) lt lt′
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

  private
    module LN = LS.Next lane-shown lane-under
    module ON = OS.Next outer-shown outer-under

  lane-next : ∀ rx₁ {q a rx₂} → Met M (rx₁ ++ (q , out a) ∷ rx₂)
            → Σ _ λ rs → BProj laneB (λ x → x) LS.J rx₁ rs × Met σ₃ rs × Σ Pos λ w → (w ≡ q ⊎ q ≡ w ⊕ [ sub LS.J ]) × LN.NextAt (cursor nothing rs) w
  lane-next rx₁ {q} {a} {rx₂} mt = LN.next-at (lane-run (run-prefix rx₁ mt))
    (run-tail rx₁ (subst (λ d → Run (enter d P) nothing (rx₁ ++ (q , out a) ∷ rx₂)) (src-op tk env′ m) mt)) (bview laneB (out a))

  -- The lanes' counter is none, or of the name the lanes last began,
  -- with a route of it open.
  lanes-count : ∀ {rx rs} → Met M rx → BProj laneB (λ x → x) LS.J rx rs
              → Flat.lanes (proj₁ (past op init rx)) ≡ 0
              ⊎ Flat.at (proj₁ (past op init rx)) ≡ proj₁ (cnt rs) × Σ ℕ λ k → proj₂ (cnt rs) ≡ suc k
  lanes-count {rx} {rs} mt pr =
    within-of (past-within {B} {B} cl (λ x → x) (λ _ _ → refl) LS.J op init r₀ rx rs
      (λ r₁ r₂ eq → end-last (inv-ev m src env′ g₃ P ok₃) r₁ (subst (Met M) eq mt)) pr (within₀ {B} laneB r₀))

  -- Where the lanes still count a route, no lane end is next.
  lane-shut : ∀ rx₁ {q a rx₂ rs} → Met M (rx₁ ++ (q , out a) ∷ rx₂) → BProj laneB (λ x → x) LS.J rx₁ rs → ¬ Flat.lanes (proj₁ (past op init rx₁)) ≡ 0
            → ∀ {y} → σ₃ y end → After (cursor nothing rs) y → (∀ {k x} → σ₃ k (out x) → After (cursor nothing rs) k → y ≼ k) → ⊥
  lane-shut rx₁ mt pr nz ry ay all = nz (lane-end-shut rx₁ mt (lane-proj pr) ry ay all)

  lanes-current : ∀ rx₁ {q a rx₂} → Met M (rx₁ ++ (q , out a) ∷ rx₂)
                → Flat.lanes (proj₁ (past op init rx₁)) ≡ 0 ⊎ Flat.at (proj₁ (past op init rx₁)) ≡ nameOf q
  lanes-current rx₁ mt with lane-next rx₁ mt
  ... | rs , pr , _ , w , wq , fw , af , outl , endl with lanes-count (run-prefix rx₁ mt) pr
  ...   | inj₁ z = inj₁ z
  ...   | inj₂ (at≡ , _) with Flat.lanes (proj₁ (past op init rx₁)) ℕ.≟ 0
  ...     | Nl.yes z = inj₁ z
  ...     | Nl.no nz =
    inj₂ (trans at≡ (trans (lane-idle rx₁ mt (lane-proj pr) nz fw af (LN.idle-least (lane-shut rx₁ {rs = rs} mt pr nz) outl endl)) (named-at LS.J wq)))

  -- The outer's next row past what the source met.
  outer-next : ∀ rx₁ {q a rx₂} → Met M (rx₁ ++ (q , out a) ∷ rx₂)
             → Σ _ λ rs → BProj outerB (opening {A} {B}) OS.J rx₁ rs × Met σ₁ rs
               × Σ Pos λ w → (w ≡ q ⊎ q ≡ w ⊕ [ sub OS.J ]) × ON.NextAt (cursor nothing rs) w
  outer-next rx₁ {q} {a} {rx₂} mt = ON.next-at (OS.run′ (subst (λ d → Run (enter d P) nothing rx₁) (src-op tk env′ m) (run-prefix rx₁ mt)))
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
  outer-idle = proper-idle (λ sc sy cy → pinby-silent (InvAt.quiet I₁ sc sy cy)) (InvAt.func I₁) (Held.idle H₁)

  postulate
    -- WHILE THE SCAN STILL COUNTS AN OUTER ROUTE, AN OUTER END BEFORE THE
    -- SOURCE'S NEXT ROW IS OF THAT ROW'S INSTANT: past the outer's cursor,
    -- its end lies in the instant the source meets next.
    outer-end-at : ∀ rx₁ {q a rx₂ rs y} → Met M (rx₁ ++ (q , out a) ∷ rx₂) → BProj outerB (opening {A} {B}) OS.J rx₁ rs
                 → σ₁ y end → After (cursor nothing rs) y → y ≺ q → ¬ Flat.outer (proj₁ (past op init rx₁)) ≡ 0
                 → nameOf y ≡ nameOf q

  -- THE SCAN'S OUTER COUNTER IS OF THE SOURCE'S NEXT ROW'S INSTANT, OR
  -- NONE: it is of the instant the outer last began, which the outer,
  -- idle, keeps up to its next row, or up to its end.
  outer-current : ∀ rx₁ {q a rx₂} → Met M (rx₁ ++ (q , out a) ∷ rx₂)
                → Flat.outer (proj₁ (past op init rx₁)) ≡ 0 ⊎ Flat.at (proj₁ (past op init rx₁)) ≡ nameOf q
  outer-current rx₁ {q} mt with outer-next rx₁ mt
  ... | rs , pr , mr , w , wq , fw , af , outl , _ with outer-count (run-prefix rx₁ mt) pr
  ...   | inj₁ z = inj₁ z
  ...   | inj₂ (at≡ , k , ck) with Flat.outer (proj₁ (past op init rx₁)) ℕ.≟ 0
  ...     | Nl.yes z = inj₁ z
  ...     | Nl.no nz = inj₂ (trans at≡ (decidable-stable (proj₁ (cnt rs) ≟ᵖ nameOf q) λ ¬g → ¬g (idle-w λ e → ¬g (idle-y e))))
    where
      Cr : Maybe Pos
      Cr = cursor nothing rs

      at-idle : ∀ {v} → Few σ₁ v → After Cr v → (∀ {y e} → σ₁ y e → Visible e → After Cr y → v ≼ y) → proj₁ (cnt rs) ≡ nameOf v
      at-idle fv av lv with outer-idle mr (λ i → bproj-end pr i) fv av lv
      ... | inj₁ z = ⊥-elim (ℕP.0≢1+n (trans (sym z) ck))
      ... | inj₂ n = n

      -- No outer end before `w`: the outer is idle at `w`.
      idle-w : (Σ Pos (λ y → σ₁ y end × After Cr y × y ≺ w) → ⊥) → proj₁ (cnt rs) ≡ nameOf q
      idle-w ne = trans (at-idle fw af lw) (named-at OS.J wq)
        where
          lw : ∀ {y e} → σ₁ y e → Visible e → After Cr y → w ≼ y
          lw {e = out _} ry _ ay    = outl ry ay
          lw {e = end}   ry _ ay yw = ne (_ , ry , ay , yw)
          lw {e = skip}  _  () _
          lw {e = pin _} _  () _

      -- An outer end before it: the outer is idle at that end.
      idle-y : Σ Pos (λ y → σ₁ y end × After Cr y × y ≺ w) → proj₁ (cnt rs) ≡ nameOf q
      idle-y (y , ry , ay , yw) =
        trans (at-idle (proj₁ fw , λ {k} rk ky → proj₂ fw rk (≺-trans {k} {y} {w} ky yw)) ay ly)
              (outer-end-at rx₁ mt pr ry ay (≺-≼-≺ {y} {w} {q} yw (next-≼ OS.J wq)) nz)
        where
          ly : ∀ {y′ e} → σ₁ y′ e → Visible e → After Cr y′ → y ≼ y′
          ly {y′} {out _} ry′ _ ay′ = ≺→≼ {y} {y′} (≺-≼-≺ {y} {w} {y′} yw (outl ry′ ay′))
          ly {e = end}    ry′ _ _   = Lawful.proper L₁ ry′ ry
          ly {e = skip}   _   () _
          ly {e = pin _}  _   () _

  postulate
    -- A CONNECT IN SCOPE KEEPS NO ROUTE PAST ITS INSTANT, read at the
    -- scan's rows.  Owed: the run split onto that connect's tracker, and
    -- the binder's own `idle` (`Bound.held`) read through `annotate`.
    live-current : ∀ rx₁ {q e rx₂} → Met M (rx₁ ++ (q , e) ∷ rx₂) → Visible e
                 → anyHolds (Flat.at (proj₁ (past op init rx₁))) (Flat.live (proj₁ (past op init rx₁))) ≡ true
                 → Flat.at (proj₁ (past op init rx₁)) ≡ nameOf q

  parked-current : ∀ rx₁ {q e rx₂} → Met M (rx₁ ++ (q , e) ∷ rx₂) → Visible e
                 → Flat.parked (proj₁ (past op init rx₁)) ≡ 0 ⊎ Flat.at (proj₁ (past op init rx₁)) ≡ nameOf q
  parked-current rx₁ mt v with past-park op init rx₁ (inj₁ refl)
  ... | inj₁ z = inj₁ z
  ... | inj₂ h = inj₂ (live-current rx₁ mt v h)

  -- No closer's row begins a route.
  no-cb : ∀ {q n} → MRow q (out (just (inj₁ (closeB , instEmit (mark begin) n)))) → ⊥
  no-cb (close y) = closing-mark (close-marks y) (λ ()) (λ ())

  nocb : ∀ rx₁ {q e rx₂} → Met M (rx₁ ++ (q , e) ∷ rx₂) → ∀ r₁ {q′ x} r₂ → rx₁ ≡ r₁ ++ (q′ , out x) ∷ r₂ → NoCB x
  nocb rx₁ {q} {e} {rx₂} mt r₁ {q′} r₂ refl refl =
    no-cb (m-rows (proj₁ (run-row r₁ (subst (Met M) (++-assoc r₁ ((q′ , _) ∷ r₂) ((q , e) ∷ rx₂)) mt))) tt)

  -- Four counters each of the instant or none: their sum is.
  sum-current : ∀ {X : Set} (a b c d : ℕ) → (a ≡ 0 ⊎ X) → (b ≡ 0 ⊎ X) → (c ≡ 0 ⊎ X) → (d ≡ 0 ⊎ X) → a + b + c + d ≡ 0 ⊎ X
  sum-current .0 .0 .0 .0 (inj₁ refl) (inj₁ refl) (inj₁ refl) (inj₁ refl) = inj₁ refl
  sum-current _ _ _ _ (inj₂ x) _ _ _ = inj₂ x
  sum-current _ _ _ _ (inj₁ _) (inj₂ x) _ _ = inj₂ x
  sum-current _ _ _ _ (inj₁ _) (inj₁ _) (inj₂ x) _ = inj₂ x
  sum-current _ _ _ _ (inj₁ _) (inj₁ _) (inj₁ _) (inj₂ x) = inj₂ x

  flat-current : ∀ rx₁ {q a rx₂} → Met M (rx₁ ++ (q , out a) ∷ rx₂)
               → tot (proj₁ (past op init rx₁)) ≡ 0 ⊎ Flat.at (proj₁ (past op init rx₁)) ≡ nameOf q
  flat-current rx₁ mt = sum-current (Flat.outer st) (Flat.lanes st) (Flat.held st) (Flat.parked st)
    (outer-current rx₁ mt) (lanes-current rx₁ mt) (held-current rx₁ mt tt) (parked-current rx₁ mt tt)
    where st = proj₁ (past op init rx₁)

  start-current : ∀ rx₁ {q a rx₂} → Met M (rx₁ ++ (q , out a) ∷ rx₂)
                → proj₂ (from r₀ (outRows op init rx₁)) ≡ 0 ⊎ proj₁ (from r₀ (outRows op init rx₁)) ≡ nameOf q
  start-current rx₁ mt with flat-current rx₁ mt
  ... | inj₁ z = inj₁ (trans (exact-past op rx₁ (nocb rx₁ mt)) z)
  ... | inj₂ a = inj₂ (trans (inv-at (inv-past op rx₁)) a)

  named : ∀ {q b n} → M q (out (just (inj₁ (b , instEmit (mark begin) n)))) → n ≡ nameOf q
  named x with m-rows x tt
  ... | outer {q = c} {w = w} y eq with refl ← open-mark eq (λ ()) =
    trans (Held.named H₁ (proj₁ y)) (cong nm (sym (rootOf-ext c [ sub w ])))
  ... | lane {q = c} {w = w} y  = trans (lane-named y) (cong nm (sym (rootOf-ext c [ sub w ])))
  ... | close y = ⊥-elim (closing-mark (close-marks y) (λ ()) (λ ()))

  early : ∀ {q b a n} → M q (out (just (inj₁ (b , instEmit (value a) n)))) → Early q
  early x with m-rows x tt
  ... | outer y eq = ⊥-elim (open-value eq)
  ... | lane {w = w} y = early-inst [ sub w ] (lane-early y)
  ... | close y = ⊥-elim (closing-value (close-marks y))

  ends : ∀ {q} → M q end → Early q
  ends x with m-rows x tt
  ... | under {zs} = early-inst zs ep₃
  ... | done {zs = zs} b = early-inst zs (bend b)
    where
      bend : ∀ {c} → BEnd c → Early c
      bend (b-outer {w = w} y) = early-inst [ sub w ] (Held.ends H₁ (proj₁ y))
      bend (b-lane {w = w} y)  = early-inst [ sub w ] (lane-ends y)
      bend (b-close {w = w} y) = early-inst [ sub w ] (close-ends y)

  late : ∀ {q b n} → M q (out (just (inj₁ (b , instEmit (mark over) n)))) → Valued (rootOf q) × opos (rootOf q) ⊑ q
  late x with m-rows x tt
  ... | outer {w = w} y eq with refl ← open-mark eq (λ ()) = late-ext [ sub w ] (Held.late H₁ (proj₁ y))
  ... | lane {w = w} y = late-ext [ sub w ] (lane-late y)
  ... | close y = ⊥-elim (closing-mark (close-marks y) (λ ()) (λ ()))

  mdone : ∀ {q b n} → M q (out (just (inj₁ (b , instEmit (mark completed) n)))) → Early q
  mdone x with m-rows x tt
  ... | outer {w = w} y eq with refl ← open-mark eq (λ ()) = early-inst [ sub w ] (Held.done H₁ (proj₁ y))
  ... | lane {w = w} y = early-inst [ sub w ] (Fit.fine lane-fit y)
  ... | close y = ⊥-elim (closing-mark (close-marks y) (λ ()) (λ ()))

  comb-runs : ∀ {rx} → Met M rx → RunHeld cs′ (outRows op init rx)
  comb-runs {rx} mt = locals-runs (walk op cs′ init r₀ rx step fin) (comb-shut mt)
    where
      step : ∀ rx₁ {q x} rx₂ → rx ≡ rx₁ ++ (q , out x) ∷ rx₂
           → Locals cs′ (from r₀ (outRows op init rx₁)) (lay q 0 (proj₂ (react op (past op init rx₁) x)))
      step rx₁ {q} {x} rx₂ refl =
        step-local op cs′ (past op init rx₁) (from r₀ (outRows op init rx₁)) q x (inv-past op rx₁) (start-current rx₁ mt)
          (λ { refl → named (proj₁ (run-row rx₁ mt)) })
          (λ { refl ne → value-open rx₁ mt o-value ne })
          (λ { refl sp ne → over-open rx₁ mt sp ne })
          (λ { refl ne → value-open rx₁ mt o-done ne })
          (λ j → rootOf-ext q (ix 1 ∷ ix j ∷ []))

      fin : ∀ rx₁ {q} rx₂ → rx ≡ rx₁ ++ (q , end) ∷ rx₂ → Local cs′ (from r₀ (outRows op init rx₁)) q end
      fin rx₁ rx₂ refl = local-end (end-open rx₁ mt)

  comb : CombIn op M cs′
  comb = record { named = named ; early = early ; ends = ends ; late = late ; done = mdone ; runs = comb-runs }

------------------------------------------------------------------------
-- The scanned stream

-- A run's facts, each decidable from the run, hold if not refuted.
runheld-stable : ∀ {A cs} {rs : List (Pos × Ev (IE A))} → ¬ ¬ RunHeld cs rs → RunHeld cs rs
runheld-stable h = record
  { covered = λ r₁ r₂ eq c ne → routes-stable (cnt r₁) _ λ k → h λ R → k (RunHeld.covered R r₁ r₂ eq c ne)
  ; exact   = λ r₁ r₂ eq → suc-stable _ λ k → h λ R → k (RunHeld.exact R r₁ r₂ eq)
  ; shut    = λ r₁ r₂ eq z bq vy iq → h λ R → RunHeld.shut R r₁ r₂ eq z bq vy iq }
  where
    suc-stable : ∀ n → ¬ ¬ (Σ ℕ λ k → n ≡ suc k) → Σ ℕ λ k → n ≡ suc k
    suc-stable zero    h′ = ⊥-elim (h′ λ { (_ , ()) })
    suc-stable (suc k) _  = k , refl
    routes-stable : ∀ (r : Pos × ℕ) y → ¬ ¬ (Σ ℕ λ k → r ≡ (y , suc k)) → Σ ℕ λ k → r ≡ (y , suc k)
    routes-stable (x , zero)  y h′ = ⊥-elim (h′ λ { (_ , ()) })
    routes-stable (x , suc k) y h′ with x ≟ᵖ y
    ... | Nl.yes refl = k , refl
    ... | Nl.no ne    = ⊥-elim (h′ λ { (_ , refl) → ne refl })

-- What a row shows, it shows whether or not a run is found to meet it.
early-stable : ∀ {y} → ¬ ¬ Early y → Early y
early-stable h v = decidable-stable (T? _) (λ k → h λ e → k (proj₁ (e v))) , λ s → h λ e → proj₂ (e v) s

valued-stable : ∀ {I} → ¬ ¬ Valued I → Valued I
valued-stable {cascade _ _ (ix _) ∙ []}      h = valued
valued-stable {frame ∙ _}                    h = ⊥-elim (h λ ())
valued-stable {cascade _ _ (ix _) ∙ (_ ∷ _)} h = ⊥-elim (h λ ())
valued-stable {cascade _ _ (sub _) ∙ _}      h = ⊥-elim (h λ ())
valued-stable {cascade _ _ last ∙ _}         h = ⊥-elim (h λ ())

late-stable : ∀ {y} → ¬ ¬ (Valued (rootOf y) × opos (rootOf y) ⊑ y) → Valued (rootOf y) × opos (rootOf y) ⊑ y
late-stable {y} h =
  valued-stable (λ k → h λ l → k (proj₁ l)) , inside-⊑ _ y (decidable-stable (T? _) λ k → h λ l → k (⊑-inside (proj₂ l)))

routing-stable : ∀ {m} → ¬ ¬ Routing m → Routing m
routing-stable {begin}      _ = r-begin
routing-stable {stop}       _ = r-stop
routing-stable {over}       _ = r-over
routing-stable {subscribed} _ = r-subscribed
routing-stable {completed}  _ = r-completed
routing-stable {outerOpen}  h = ⊥-elim (h λ ())
routing-stable {outerClose} h = ⊥-elim (h λ ())
routing-stable {laneStart}  h = ⊥-elim (h λ ())
routing-stable {carry}      h = ⊥-elim (h λ ())
routing-stable {laneDone}   h = ⊥-elim (h λ ())
routing-stable {burstEnd}   h = ⊥-elim (h λ ())
routing-stable {outerDone}  h = ⊥-elim (h λ ())

-- THE SCANNED STREAM HOLDS WHAT ITS SOURCE PROMISES: a row it shows is
-- one a run met of the source lays out, a step's output, which is what
-- the step read or a stop, or the source's end.
module Scanned (m : Maybe ℕ) {Γ B} op (s : Obs Timeline Γ (Maybe (Input B))) (ρ : DenEnv Γ) P cs (g : GoodEnv ρ) (ok : Ok (Hots ρ) P)
               (ci : CombIn op (enter (ev m s ρ) P) cs) where
  M = enter (ev m s ρ) P
  S = enter (ev m (each proj₂ (scan (react op) init s)) ρ) P

  open Reached (ev m (each proj₂ (scan (react op) init s)) ρ) P (inv-ev m (each proj₂ (scan (react op) init s)) ρ g P ok) using (reach)

  -- A row shown is laid out by a run met of the source, classically.
  met-laid : ∀ {y e} → S y e → Visible e → ¬ ¬ Σ _ λ rx → Met M rx × Laid op init rx y e
  met-laid {y} {e} x vi k = reach x vi λ (rs , mt) → comb-run m op s ρ P g ok mt λ (rx , mx , ext , eq) →
    k (rx , mx , laid-in op init rx (subst ((y , e) ∈_) eq (∈-++⁺ˡ (∈-++⁺ʳ rs (here refl)))))

  named-laid : ∀ {rx y n} → Met M rx → Laid op init rx y (out (instEmit (mark begin) n)) → n ≡ nameOf y
  named-laid mx (laid rx₁ {q = c} {x = x} rx₂ {j = j} refl vi) with react-sent op (past op init rx₁) x vi
  ... | routed _ refl = trans (CombIn.named ci mq) (cong nm (sym (rootOf-ext c (ix 1 ∷ ix j ∷ []))))
    where mq = proj₁ (run-row rx₁ mx)

  routing-laid : ∀ {rx y m n} → Met M rx → Laid op init rx y (out (instEmit (mark m) n)) → Routing m
  routing-laid mx (laid rx₁ {x = x} rx₂ refl vi) with react-sent op (past op init rx₁) x vi
  ... | routed r refl = r
  ... | minted        = r-stop

  early-laid : ∀ {rx y a n} → Met M rx → Laid op init rx y (out (instEmit (value a) n)) → Early y
  early-laid mx (laid rx₁ {x = x} rx₂ {j = j} refl vi) with react-sent op (past op init rx₁) x vi
  ... | passed refl = early-inst (ix 1 ∷ ix j ∷ []) (CombIn.early ci mq)
    where mq = proj₁ (run-row rx₁ mx)

  ends-laid : ∀ {rx y} → Met M rx → Laid op init rx y end → Early y
  ends-laid mx (ended rx₁ rx₂ refl) = CombIn.ends ci (proj₁ (run-row rx₁ mx))

  late-laid : ∀ {rx y n} → Met M rx → Laid op init rx y (out (instEmit (mark over) n)) → Valued (rootOf y) × opos (rootOf y) ⊑ y
  late-laid mx (laid rx₁ {x = x} rx₂ {j = j} refl vi) with react-sent op (past op init rx₁) x vi
  ... | routed _ refl = late-ext (ix 1 ∷ ix j ∷ []) (CombIn.late ci mq)
    where mq = proj₁ (run-row rx₁ mx)

  done-laid : ∀ {rx y n} → Met M rx → Laid op init rx y (out (instEmit (mark completed) n)) → Early y
  done-laid mx (laid rx₁ {x = x} rx₂ {j = j} refl vi) with react-sent op (past op init rx₁) x vi
  ... | routed _ refl = early-inst (ix 1 ∷ ix j ∷ []) (CombIn.done ci mq)
    where mq = proj₁ (run-row rx₁ mx)

  named : ∀ {y n} → S y (out (instEmit (mark begin) n)) → n ≡ nameOf y
  named x = decidable-stable (_ ≟ᵖ _) λ ng → met-laid x tt λ (_ , mx , l) → ng (named-laid mx l)

  routing : ∀ {y m n} → S y (out (instEmit (mark m) n)) → Routing m
  routing x = routing-stable λ ng → met-laid x tt λ (_ , mx , l) → ng (routing-laid mx l)

  early : ∀ {y a n} → S y (out (instEmit (value a) n)) → Early y
  early x = early-stable λ ng → met-laid x tt λ (_ , mx , l) → ng (early-laid mx l)

  ends : ∀ {y} → S y end → Early y
  ends x = early-stable λ ng → met-laid x tt λ (_ , mx , l) → ng (ends-laid mx l)

  late : ∀ {y n} → S y (out (instEmit (mark over) n)) → Valued (rootOf y) × opos (rootOf y) ⊑ y
  late x = late-stable λ ng → met-laid x tt λ (_ , mx , l) → ng (late-laid mx l)

  done : ∀ {y n} → S y (out (instEmit (mark completed) n)) → Early y
  done x = early-stable λ ng → met-laid x tt λ (_ , mx , l) → ng (done-laid mx l)

  runs : ∀ {rs} → Met S rs → RunHeld cs rs
  runs mt = runheld-stable λ k → comb-run m op s ρ P g ok mt λ (rx , mx , ext , eq) →
    k (runs-prefix ext (subst (RunHeld cs) (sym eq) (CombIn.runs ci mx)))

comb-held : ∀ m {Γ B} op (s : Obs Timeline Γ (Maybe (Input B))) (ρ : DenEnv Γ) P cs → GoodEnv ρ → Ok (Hots ρ) P
          → CombIn op (enter (ev m s ρ) P) cs → Idle (enter (ev m (each proj₂ (scan (react op) init s)) ρ) P)
          → Rest (enter (ev m (each proj₂ (scan (react op) init s)) ρ) P)
          → Held (enter (ev m (each proj₂ (scan (react op) init s)) ρ) P) cs
comb-held m op s ρ P cs g ok ci id re = held-runs named routing early ends done late id re runs
  where open Scanned m op s ρ P cs g ok ci

held-comb : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) s
            (env : DenEnv Δ) cs → GoodEnv env → EnvHeld ρ env cs
          → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ (f a))
          → ∀ p → Ok (Hots env) p → Early p
          → let open FlatHots m ρ op f s env p in
            Held (enter (ev m trig env₀) (c ⊕ [ ix 1 ])) ((c ⊕ [ ix 1 ]) ∷ p ∷ cs)
          → Lawful σ₁ → Lawful σ₂ → Lawful σ₃ → Ok (Hots (hot σ₁ ∷ env₀)) p₀ → Ok (Hots (hot σ₂ ∷ hot σ₁ ∷ env₀)) p₀₀
          → Ok (Hots env′) P → Early P
          → Held scanned (P ∷ p₀₀ ∷ p₀ ∷ c ∷ p ∷ cs)
held-comb m ρ op f s env cs gd eh hf p ok ep H₁ L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃ =
  comb-held m op src env′ P _ (good-cons L₃ (good-cons L₂ (good-cons L₁ (good-cons L₀ gd)))) ok₃
    (CombSrc.comb m ρ op f s env cs gd eh hf p ok ep H₁ L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃)
    (CombSrc.scan-idle m ρ op f s env cs gd eh hf p ok ep H₁ L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃)
    (CombSrc.scan-rest m ρ op f s env cs gd eh hf p ok ep H₁ L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃)
  where
    open FlatHots m ρ op f s env p using (src; env′; P)
    L₀ = src-lawful {A = ⊤} {B = ⊤} {s = ev m empty env} {F = λ h → ev m empty (h ∷ env)} (inv-ev m empty env gd) (λ L → inv-ev m empty (hot _ ∷ env) (good-cons L gd)) p ok

held-flatMap : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) s
             → (∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ s)
             → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ (f a)) → IH m ρ (flatMap op f s)
held-flatMap m ρ op f s hs hf = ih λ env cs g eh p ok ep →
  let open FlatHots m ρ op f s env p using (trig; real; c; p₀; p₀₀; tracks-trig; tracks-closer; tracks-real) in
  conn-ev m empty _ env cs g p ok ep (tracks-fin (empty-few m env (p ⊕ [ ix 1 ]))) λ L₀ ok₀ ep₀ →
    conn-ev m trig _ _ (p ∷ cs) (good-cons L₀ g) c ok₀ ep₀ tracks-trig λ L₁ ok₁ ep₁ →
      conn-ev m closer _ _ (c ∷ p ∷ cs) (good-cons L₁ (good-cons L₀ g)) p₀ ok₁ ep₁ tracks-closer λ L₂ ok₂ ep₂ →
        conn-ev m real _ _ (p₀ ∷ c ∷ p ∷ cs) (good-cons L₂ (good-cons L₁ (good-cons L₀ g))) p₀₀ ok₂ ep₂ tracks-real λ L₃ ok₃ ep₃ →
          held-comb m ρ op f s env cs g eh hf p ok ep
            (held-trigger m ρ s env cs p g ok ep (IH.holds (hs (λ i → there (ρ i))) _ cs (good-cons L₀ g) eh))
            L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃

-- A DEFER'S LIMIT KEEPS ITS INSTANTS FINITE: past a zero count, finitely
-- many rows of the instant last begun.  Each approximant's rest bounds only
-- its own rows, and the limit's rows of an instant are those of every
-- approximant together, which no one approximant's list bounds.
postulate
  lim-rest : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A)
           → (∀ n → IH (just n) ρ (defer l))
           → ∀ env cs → GoodEnv env → EnvHeld ρ env cs → ∀ p → Ok (Hots env) p → Early p
           → Rest (enter (⟦ elab ρ (defer l) ⟧ env) p)

-- THE BOTTOM APPROXIMANT shows only skips; each further one is the body
-- under a `defer`'s guard; the meaning is the approximants' limit, held
-- wherever the approximants agree with it.
held-lim : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A)
         → (∀ n → IH (just n) ρ (defer l)) → IH nothing ρ (defer l)
held-lim ρ l hs = ih λ env cs g eh p ok ep →
  LimHeld.held (enter (⟦ elab ρ (defer l) ⟧ env) p) (λ n → enter (approx n (elab ρ (defer l)) env) p) (p ∷ cs)
    (λ { (ES.from N h , _) → N , h N ℕP.≤-refl })
    (λ fw → let (N , ag) = reached (elab ρ (defer l)) env g p ok fw in N , ag N ℕP.≤-refl)
    (λ n → IH.holds (hs n) env cs g eh p ok ep) (lim-rest ρ l hs env cs g eh p ok ep)

held-⊥ : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A) → IH (just zero) ρ (defer l)
held-⊥ ρ l = ih λ env cs g eh p ok ep → Quiet.held _ p cs ep (λ { (spin _ , _) () }) λ { (() , _) }

held-next : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A)
          → IH (just n) ρ (Later.force l) → IH (just (suc n)) ρ (defer l)
held-next n ρ l (ih h) = ih λ env cs g eh p ok ep →
  held-defer (approx n (elab ρ (Later.force l)) env) p cs (h env cs g eh (p ⊕ [ ix 1 ]) (ok-step p ok) (early-inst [ ix 1 ] ep))

held-approx : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) → IH (just n) ρ o
held-approx n       ρ (cold c)          = held-cold (just n) ρ c
held-approx n       ρ empty             = held-empty (just n) ρ
held-approx n       ρ (of xs)           = held-of (just n) ρ xs
held-approx n       ρ (map f s)         = held-map (just n) ρ f s (held-approx n ρ s)
held-approx n       ρ (scan f z s)      = held-scan (just n) ρ f z s (held-approx n ρ s)
held-approx n       ρ (takeWhile i p s) = held-takeWhile (just n) ρ i p s (held-approx n ρ s)
held-approx n       ρ (flatMap op f s)  = held-flatMap (just n) ρ op f s (λ ρ′ → held-approx n ρ′ s) λ a ρ′ → held-approx n ρ′ (f a)
held-approx n       ρ (connect s b)     = held-connect (just n) ρ s b (held-approx n ρ s) λ ρ′ → held-approx n ρ′ b
held-approx n       ρ (connected i)     = held-connected (just n) ρ i
held-approx zero    ρ (defer l)         = held-⊥ ρ l
held-approx (suc n) ρ (defer l)         = held-next n ρ l (held-approx n ρ (Later.force l))

held-⟦⟧ : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) → IH nothing ρ o
held-⟦⟧ ρ (cold c)          = held-cold nothing ρ c
held-⟦⟧ ρ empty             = held-empty nothing ρ
held-⟦⟧ ρ (of xs)           = held-of nothing ρ xs
held-⟦⟧ ρ (map f s)         = held-map nothing ρ f s (held-⟦⟧ ρ s)
held-⟦⟧ ρ (scan f z s)      = held-scan nothing ρ f z s (held-⟦⟧ ρ s)
held-⟦⟧ ρ (takeWhile i p s) = held-takeWhile nothing ρ i p s (held-⟦⟧ ρ s)
held-⟦⟧ ρ (flatMap op f s)  = held-flatMap nothing ρ op f s (λ ρ′ → held-⟦⟧ ρ′ s) λ a ρ′ → held-⟦⟧ ρ′ (f a)
held-⟦⟧ ρ (connect s b)     = held-connect nothing ρ s b (held-⟦⟧ ρ s) λ ρ′ → held-⟦⟧ ρ′ b
held-⟦⟧ ρ (connected i)     = held-connected nothing ρ i
held-⟦⟧ ρ (defer l)         = held-lim ρ l λ n → held-approx n ρ (defer l)

------------------------------------------------------------------------
-- The top

-- The restamp renames only what no count reads: a begin keeps its own.
same-restamp : ∀ {A} → Relabels (restamp {A})
same-restamp st (instEmit (value _) _)        = same-value
same-restamp st (instEmit (mark begin) _)      = same-mark (λ _ → refl)
same-restamp st (instEmit (mark stop) _)       = same-mark λ ()
same-restamp st (instEmit (mark over) _)       = same-mark λ ()
same-restamp st (instEmit (mark outerOpen) _)  = same-mark λ ()
same-restamp st (instEmit (mark outerClose) _) = same-mark λ ()
same-restamp st (instEmit (mark laneStart) _)  = same-mark λ ()
same-restamp st (instEmit (mark carry) _)      = same-mark λ ()
same-restamp st (instEmit (mark laneDone) _)   = same-mark λ ()
same-restamp st (instEmit (mark burstEnd) _)   = same-mark λ ()
same-restamp st (instEmit (mark outerDone) _)  = same-mark λ ()
same-restamp st (instEmit (mark subscribed) _) = same-mark λ ()
same-restamp st (instEmit (mark completed) _)  = same-mark λ ()

-- THE BATCHER'S SOURCE HOLDS: the wrapped program, restamped.
held-top : ∀ {A} (o : SObs [] A) → IH nothing (λ i → i) (plain o) → Held (elaborated o) (root ∷ [])
held-top o hy = held-scan-at restamp same-restamp (root , marked begin) (⟦ wrapped s ⟧ []ᵉ) root
  (held-wrapped s (IH.holds hy []ᵉ [] (λ ()) (λ ())))
  where
    s = elab (λ i → i) (plain o)

-- Opaque: a consumer projects its fields, and a `with` on one would
-- otherwise unfold the whole induction.
opaque
  held : ∀ {A} (o : SObs [] A) → Held (elaborated o) (root ∷ [])
  held o = held-top o (held-⟦⟧ (λ i → i) (plain o))

-- The elaborated program's instants stay dead.
shut : ∀ {A : Set} (o : SObs [] A) → Shut (elaborated o)
shut o = Held.shut (held o)
