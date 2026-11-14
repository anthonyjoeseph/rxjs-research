{-# OPTIONS --guardedness #-}

-- THE TAKE CARRIES THE CORE.  `elaborate` subscribes the core as the
-- source of a connect telling its completion (the told run, carried by
-- `simultaneous.CarryTold`), that connect as the first lane of a merge
-- beside the subscribe mark's lane, and takes the merge to the
-- completion mark.  The merge relabels nothing: its rows are the told
-- run's, the told end shown as a skip (the mark's lane never ends), and
-- five rows of its own, in the subscribe frame.  The completion mark is
-- the merge's one failing value, so the take keeps every row before it
-- and ends one label under it.  Each carrier stays where the told carry
-- put it, but the end's, which moves from the told end up to the take's.
module simultaneous.WrapTake where

open import Data.Bool using (Bool; true; false; T; not; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; filter)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-filter⁺; ∈-filter⁻)
open import Data.Bool.Properties using (T?)
open import Data.List.Relation.Unary.All using ([])
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_; yes; no; ¬?)
open import Relation.Nullary.Decidable using (decidable-stable)
open import Data.List.Relation.Unary.Any using (any?)

open import Tree using (Obs; cold)
open import denotation.Position using (Pos; Label; frame; ix; sub; last; _⊕_; root; _≟ᵖ_; _<ᵖ_)
open import denotation.Events using (Timeline; fresh; timelineAt)
import denotation.Events as Evs
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; Work; EmissionSet; Den; enter; approx; Reach; Few; at-out;
  at-skip; at-end; on-out; on-skip; _≺_; _≼_; module Op; module Merge)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≺-absurd; ≺-≼-≺; ≺→≼; ≼-refl; ≼-trans; ≼-split; ≺-ext; entered-reach;
  T-not)
open import denotation.Laws.Worlds using (InvAt; Ok; Hots; W; W⁼; here; inW; step; timer; join; _⊑_; ⊑-refl; ⊑-trans; ⊑-≼; ⊑-snoc⁺;
  ⊑-snoc; ⊕-injʳ; ⊕-identityʳ; ⊕-assoc; world-after; conv)
open import denotation.Laws.Worlds.Leaves using (of-end; of-reach)
open import denotation.Laws.BoundedInv using (end-uniq)
open import denotation.Laws.Shows using (∈-stable)
open import denotation.Laws.ColdInv using (cold-reach)
open import denotation.Laws using (inv-approx)
open import adequacy.SubOne using (Lifted; reach-lift)
open import simultaneous.SObs using (SObs; plain; lone; module Elaborate)
open import simultaneous.InstEmit using (valuesOf; completed; subscribed)
open import simultaneous.Readings using (instantOf; parent; parent-snoc)
open import simultaneous.Relations using (sourced)
open import simultaneous.Attribution using (Live; Shown; Match; Every; One; Reads)
open import simultaneous.Listing using (Listed)
open import simultaneous.CarryBase using (PMap; Emb; CarryAt; instant-⊕; sub-listed; listed-≼; apart; module Mono; IntoAt; From;
  InOrder; Near; Home; Whole; Ahead; ahead-over)
open import simultaneous.CarryLeaves using (coreAt; ix-last)
open import simultaneous.CarryTold using (told-carry)
open import simultaneous.ToldRows using (module Told)
open import simultaneous.TakeSide using (module Side; between)
open import simultaneous.CoreOuts using (core-unfinished)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; elab; completing; unfinished; marked)

-- Where the merge subscribes its first lane, the connect telling the
-- core's completion: the second child of the merge's first outer value.
cAt : Pos
cAt = root ⊕ (ix 0 ∷ ix 1 ∷ [])

------------------------------------------------------------------------
-- A world with no hot rows, in the subscribe frame, lies under its
-- subscription.

mutual
  frame-under : ∀ {p y} → W (λ _ → ⊥) p y → instantOf y ≡ frame → p ⊑ y
  frame-under (step {x} {l} w _) e = ⊑-trans (frame-under⁼ w (trans (sym (instant-⊕ x [ l ])) e)) (⊑-snoc⁺ x)
  frame-under (timer _ _ _ _) ()
  frame-under (join (inj₁ ()) _ _)
  frame-under (join {h} {e₀} (inj₂ w) _ _) e = ⊑-trans (frame-under w (trans (sym (instant-⊕ h [ sub e₀ ])) e)) (⊑-snoc⁺ h)

  frame-under⁼ : ∀ {p y} → W⁼ (λ _ → ⊥) p y → instantOf y ≡ frame → p ⊑ y
  frame-under⁼ {p} here _ = ⊑-refl p
  frame-under⁼ (inW w) e  = frame-under w e

module Wrap n {A} (o : SObs [] A) {M : PMap} (hm : Emb M)
  (cc : CarryAt valuesOf M (λ _ → ⊥) (λ _ → ⊥) (λ _ → ⊤) (enter (approx n (plain o) []) root)
          (enter (approx n (elab (λ i → i) (plain o)) []) coreAt) root coreAt) where

  core : Obs Timeline [] (IE A)
  core = elab (λ i → i) (plain o)

  t : EmissionSet A
  t = enter (approx n (plain o) []) root

  okc : Ok (Hots []) cAt
  okc = tt , λ ()

  module T = Told n core (marked completed) [] (λ ()) cAt okc
  open T using (σ; δ; w; c₁; invσ; flatσ)

  C : EmissionSet (IE A)
  C = T.τ

  c : CarryAt valuesOf M (λ _ → ⊥) (λ _ → ⊥) (λ _ → ⊤) t C root cAt
  c = proj₁ (told-carry n core (marked completed) refl [] (λ ()) cAt okc cc)

  module CC = CarryAt cc
  module Cc = CarryAt c

  It : InvAt (Hots []) root t
  It = inv-approx n (plain o) [] (λ ()) root (tt , λ ())

  IC : InvAt (Hots []) cAt C
  IC = inv-approx n (completing core) [] (λ ()) cAt okc

  m : EmissionSet (IE A)
  m = enter (approx n (sourced o) []) root

  Im : InvAt (Hots []) root m
  Im = inv-approx n (sourced o) [] (λ ()) root (tt , λ ())

  module MS = Side true unfinished m (λ {y} {e} → entered-reach (approx n (sourced o) []) root {y} {e}) Im

  u : EmissionSet (IE A)
  u = MS.T′

  ----------------------------------------------------------------------
  -- The merge, unfolded

  bs : List Bool
  bs = true ∷ false ∷ []

  Om : EmissionSet Bool
  Om = enter (Op.of bs) root

  F : Bool → Den (IE A)
  F b = approx n (if b then completing core else cold (lone (marked subscribed))) []

  module Mg = Merge F Om

  -- The merge's own rows: its two values, the mark's lane, the pass.
  data Fix : Pos → Ev (IE A) → Set where
    fx-v0   : Fix ((root ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) skip
    fx-v1   : Fix ((root ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) skip
    fx-sub  : Fix (((root ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) (out (marked subscribed))
    fx-sk   : Fix (((root ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) skip
    fx-pass : Fix (root ⊕ [ last ]) skip

  fixL : List Pos
  fixL = ((root ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ∷ ((root ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ∷ (((root ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ])
       ∷ (((root ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ∷ (root ⊕ [ last ]) ∷ []

  fix-in : ∀ {k e} → Fix k e → k ∈ fixL
  fix-in fx-v0   = here refl
  fix-in fx-v1   = there (here refl)
  fix-in fx-sub  = there (there (here refl))
  fix-in fx-sk   = there (there (there (here refl)))
  fix-in fx-pass = there (there (there (there (here refl))))

  fix-row : ∀ {k} → k ∈ fixL → Σ (Ev (IE A)) (Fix k)
  fix-row (here refl)                                 = _ , fx-v0
  fix-row (there (here refl))                         = _ , fx-v1
  fix-row (there (there (here refl)))                 = _ , fx-sub
  fix-row (there (there (there (here refl))))         = _ , fx-sk
  fix-row (there (there (there (there (here refl))))) = _ , fx-pass

  fix-frame : ∀ {k} → k ∈ fixL → instantOf k ≡ frame
  fix-frame (here refl)                                 = refl
  fix-frame (there (here refl))                         = refl
  fix-frame (there (there (here refl)))                 = refl
  fix-frame (there (there (there (here refl))))         = refl
  fix-frame (there (there (there (there (here refl))))) = refl

  -- No fixed row lies under the told run's subscription.
  cAt-fix : ∀ {k} → cAt ⊑ k → k ∈ fixL → ⊥
  cAt-fix (_ , refl) (here ())
  cAt-fix (_ , refl) (there (here ()))
  cAt-fix (_ , refl) (there (there (here ())))
  cAt-fix (_ , refl) (there (there (there (here ()))))
  cAt-fix (_ , refl) (there (there (there (there (here ())))))
  cAt-fix (_ , refl) (there (there (there (there (there ())))))

  lone-endless : ∀ {p c₀} → enter (F false) p c₀ end → ⊥
  lone-endless (on-out (on-skip ()) , _)

  lone-row : ∀ {k e} → enter (F false) ((root ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) k e → Fix k e
  lone-row (at-out , _)              = fx-sub
  lone-row (on-out at-skip , _)      = fx-sk
  lone-row (on-out (on-skip ()) , _)

  -- The merge never ends: the mark's lane never does.
  undone : ∀ {c₀} → Mg.Done c₀ → ⊥
  undone {c₀} ((c′ , xo , c′c) , lanes) with of-end root 0 bs (proj₁ xo)
  ... | refl with lanes (on-out at-out , of-reach root 0 bs {root ⊕ [ ix 1 ]} {out false}) tt (≺-≼-≺ {root ⊕ [ ix 1 ]} {root ⊕ [ last ]} {c₀} tt c′c) (λ ())
  ...   | _ , (yL , _) , _ = lone-endless yL

  -- Every row of the merge: a told row, the told end passed, or its own.
  data MR : Pos → Ev (IE A) → Set where
    mr-c   : ∀ {k e} → C k e → Work e → MR k e
    mr-end : ∀ {k} → C k end → MR k skip
    mr-fix : ∀ {k e} → Fix k e → MR k e

  jrow : ∀ {k e} → Mg.JoinT k e → MR k e
  jrow (Mg.val (at-out , _))                             = mr-fix fx-v0
  jrow (Mg.val (on-out at-out , _))                      = mr-fix fx-v1
  jrow (Mg.val (on-out (on-out ()) , _))
  jrow (Mg.step (on-out (on-out ()) , _))
  jrow (Mg.opin (on-out (on-out ()) , _))
  jrow (Mg.oend _ d)                                     = ⊥-elim (undone d)
  jrow (Mg.opass (on-out (on-out at-end) , _) _)         = mr-fix fx-pass
  jrow (Mg.lane (at-out , _) _ (y , _) _ wk)             = mr-c y wk
  jrow (Mg.lane (on-out at-out , _) _ (y , _) _ _)       = mr-fix (lone-row y)
  jrow (Mg.lane (on-out (on-out ()) , _) _ _ _ _)
  jrow (Mg.lend _ _ _ _ _ d)                             = ⊥-elim (undone d)
  jrow (Mg.lpass (at-out , _) _ (y , _) _ _ _)           = mr-end y
  jrow (Mg.lpass (on-out at-out , _) _ (y , _) _ _ _)    = ⊥-elim (lone-endless y)
  jrow (Mg.lpass (on-out (on-out ()) , _) _ _ _ _ _)
  jrow (Mg.hand _ _ _ _ ())
  jrow (Mg.left (at-out , _) _ (y , _) _ _)              = mr-c y tt
  jrow (Mg.left (on-out at-out , _) _ (y , _) _ _) with lone-row y
  ... | ()
  jrow (Mg.left (on-out (on-out ()) , _) _ _ _ _)
  jrow (Mg.run () _)
  jrow (Mg.rend () _ _)
  jrow (Mg.rpass () _ _)
  jrow (Mg.rhand () _)

  mrow : ∀ {k e} → m k e → MR k e
  mrow x = jrow (proj₁ x)

  ----------------------------------------------------------------------
  -- The merge's rows made

  -- The told rows and the merge's own, the rows every merge row is read off.
  E₀ : EmissionSet (IE A)
  E₀ k e = C k e ⊎ Fix k e

  lifted : Lifted [_] E₀ Mg.JoinT
  lifted x with jrow x
  ... | mr-c {k} y _ = k , _ , inj₁ y , ≼-refl {k} , here refl , λ eq → eq
  ... | mr-end {k} y = k , end , inj₁ y , ≼-refl {k} , here refl , λ ()
  ... | mr-fix {k} f = k , _ , inj₂ f , ≼-refl {k} , here refl , λ eq → eq

  reachE : ∀ {y e} → C y e → Reach E₀ y e
  reachE x with entered-reach (approx n (completing core) []) cAt x
  ... | ks , h = ks ++ fixL , λ { (inj₁ x′) lt d → ∈-++⁺ˡ (h x′ lt d) ; (inj₂ f) _ _ → ∈-++⁺ʳ ks (fix-in f) }

  fewE : ∀ {y} → Few C y → Few E₀ y
  fewE (ks , h) = ks ++ fixL , λ { (inj₁ x′) lt → ∈-++⁺ˡ (h x′ lt) ; (inj₂ f) _ → ∈-++⁺ʳ ks (fix-in f) }

  cAt≺ : ∀ {k e} → C k e → cAt ≺ k
  cAt≺ y = world-after (InvAt.world IC y) (InvAt.real IC y)

  o-true : Om (root ⊕ [ ix 0 ]) (out true)
  o-true = at-out , of-reach root 0 bs {root ⊕ [ ix 0 ]} {out true}

  o-false : Om (root ⊕ [ ix 1 ]) (out false)
  o-false = on-out at-out , of-reach root 0 bs {root ⊕ [ ix 1 ]} {out false}

  m-c : ∀ {k e} → C k e → Work e → m k e
  m-c {e = e} y wk = Mg.lane o-true tt (y , cAt≺ y) (λ ()) wk , reach-lift [_] lifted {e = e} {e₀ = e} (λ eq → eq) (λ un → un) (reachE y)

  m-end : ∀ {k} → C k end → m k skip
  m-end y = Mg.lpass o-true tt (y , cAt≺ y) (λ ()) (λ ()) undone , reach-lift [_] lifted {e = skip} {e₀ = end} (λ ()) (λ _ → tt) (reachE y)

  m-of : ∀ {k e} → C k e → Σ (Ev (IE A)) (m k)
  m-of {e = out _}  y = _ , m-c y tt
  m-of {e = skip}   y = _ , m-c y tt
  m-of {e = pin _}  y = _ , m-c y tt
  m-of {e = end}    y = _ , m-end y

  fix-unp : ∀ {k e} → Fix k e → Unpinned e
  fix-unp fx-v0   = tt
  fix-unp fx-v1   = tt
  fix-unp fx-sub  = tt
  fix-unp fx-sk   = tt
  fix-unp fx-pass = tt

  lp : Pos
  lp = (root ⊕ [ ix 1 ]) ⊕ [ ix 1 ]

  lm : Evs.From (IE A) 0
  lm = timelineAt (lone (marked subscribed)) lp

  m-fix : ∀ {k e} → Fix k e → Few C k → m k e
  m-fix {k} {e} f fw = row f , reach-lift [_] lifted {e = e} {e₀ = e} (λ eq → eq) (λ un → un) (fr (fix-unp f))
    where
      fr : Unpinned e → Reach E₀ k e
      fr un with fewE fw
      ... | ks , h = ks , λ x lt _ → h x lt

      row : ∀ {k e} → Fix k e → Mg.JoinT k e
      row fx-v0   = Mg.val o-true
      row fx-v1   = Mg.val o-false
      row fx-sub  = Mg.lane o-false tt ((at-out , cold-reach lp lm tt at-out) , tt) (λ ()) tt
      row fx-sk   = Mg.lane o-false tt ((on-out at-skip , cold-reach lp lm tt (on-out at-skip)) , tt) (λ ()) tt
      row fx-pass = Mg.opass (on-out (on-out at-end) , of-reach root 0 bs {root ⊕ [ last ]} {end}) undone

  ----------------------------------------------------------------------
  -- Where the told end and the take's end lie

  Pk : Pos → Pos
  Pk K = (K ⊕ [ sub w ]) ⊕ [ ix 1 ]

  -- The completion mark, the merge's one failing value.
  qc : Pos → Pos
  qc K = Pk K ⊕ [ ix 0 ]

  -- The take's end, under it.
  Xs : Pos → Pos
  Xs K = qc K ⊕ [ last ]

  qc-path : ∀ K → K ⊕ (sub w ∷ ix 1 ∷ ix 0 ∷ []) ≡ qc K
  qc-path K = sym (trans (⊕-assoc (K ⊕ [ sub w ]) [ ix 1 ] [ ix 0 ]) (⊕-assoc K [ sub w ] (ix 1 ∷ ix 0 ∷ [])))

  under-qc : ∀ K → K ⊑ qc K
  under-qc K = sub w ∷ ix 1 ∷ ix 0 ∷ [] , sym (qc-path K)

  under-Xs : ∀ K → K ⊑ Xs K
  under-Xs K = ⊑-trans {K} (under-qc K) (⊑-snoc⁺ (qc K))

  K≺qc : ∀ K → K ≺ qc K
  K≺qc K = subst (K ≺_) (qc-path K) (≺-ext K (ix 1 ∷ ix 0 ∷ []))

  snoc-apart : ∀ q {a b : Label} → (a ≡ b → ⊥) → (q ⊕ [ a ]) ⊑ (q ⊕ [ b ]) → ⊥
  snoc-apart q {a} n le with ⊑-snoc q le
  ... | inj₂ eq  = n (⊕-injʳ q q eq)
  ... | inj₁ le′ = ≺-irrefl {q} (≺-≼-≺ {q} {q ⊕ [ a ]} {q} (≺-ext q []) (⊑-≼ le′))

  Xs≺c₁ : ∀ K → Xs K ≺ c₁ K
  Xs≺c₁ K = subst (Xs K ≺_) (⊕-identityʳ (c₁ K))
              (apart {Pk K ⊕ [ ix 0 ]} {Pk K ⊕ [ last ]} (ix-last (Pk K)) (snoc-apart (Pk K) λ ()) [ last ] [])

  ----------------------------------------------------------------------
  -- The told end, the failing mark, the stop

  xrow : ∀ {K} → σ K end → C (qc K) (out (marked completed))
  xrow {K} y = T.τ-under y (T.few-unp y tt) (under-qc K) (T.j-x y)

  endrow : ∀ {K} → σ K end → C (c₁ K) end
  endrow {K} y = T.τ-under y (T.few-unp y tt) (T.under-c₁ K) (T.j-end y)

  mx : ∀ {K} → σ K end → m (qc K) (out (marked completed))
  mx y = m-c (xrow y) tt

  -- Only the completion mark fails.
  fails-at : ∀ {q a} → m q (out a) → T (not (unfinished a)) → Σ Pos λ K → σ K end × q ≡ qc K
  fails-at x nf with mrow x
  ... | mr-fix fx-sub = ⊥-elim nf
  ... | mr-c y _ with T.raw y
  ...   | T.r-shown p _ = ⊥-elim (T-not (core-unfinished n o (proj₁ p)) nf)
  ...   | T.r-x yK = _ , yK , refl

  failed-at : ∀ {l} → MS.Failed l → Σ Pos λ K → σ K end × qc K ≺ l
  failed-at (_ , _ , x , nf , cl) with fails-at x nf
  ... | K , yK , refl = K , yK , cl

  never-before : ∀ {K} → σ K end → ¬ MS.Failed (qc K)
  never-before {K} yK fl with failed-at fl
  ... | K′ , yK′ , lt with end-uniq T.invσ yK yK′
  ...   | refl = ≺-irrefl {qc K} lt

  first-qc : ∀ {K} → σ K end → MS.First (qc K)
  first-qc yK = (_ , mx yK , tt) , never-before yK

  stop : ∀ {K} → σ K end → u (Xs K) end
  stop yK = MS.cut-row (mx yK) tt (never-before yK) (inj₂ refl)

  -- The plain end the told end carries.
  L2 : ∀ {K} → σ K end → Σ Pos λ c₀ → ¬ ¬ t c₀ end × CC.Img c₀ K
  L2 {K} yK with CC.shown-end yK (λ yc → subst (K ≼_) (end-uniq T.invσ yK yc) (≼-refl {K})) (T.few-unp yK tt)
  ... | c₀ , i , ntc = c₀ , ntc , i

  module Mn = Mono hm (λ {y} {e} {l} {ys} {e′} → InvAt.flat It {y} {e} {l} {ys} {e′}) cc

  ----------------------------------------------------------------------
  -- Where a carrier moves

  -- A carrier with a row moves to its told image, but the told end's;
  -- one with none stays, off the merge's own rows.
  data Sv (l : Pos) : Pos → Set where
    w-row  : ∀ {e} → σ l e → Work e → Sv l (l ⊕ δ e)
    w-bare : (∀ {e} → σ l e → ⊥) → ¬ (l ∈ fixL) → Sv l l

  -- The told end's carrier moves to the take's end.
  Wv : Pos → Pos → Set
  Wv l l″ = Sv l l″ ⊎ (σ l end × l″ ≡ Xs l)

  -- A live carrier that stays lies before every failure.
  stay-at : ∀ {k l l′ K c₀} → CC.Img k l → Sv l l′ → Live t k → σ K end → t c₀ end → CC.Img c₀ K → l′ ≺ qc K
  stay-at {k} {l} {K = K} {c₀} i sv lv yK tc₀ i₀ with ≼-split {k} {c₀} (lv tc₀)
  ... | inj₂ refl with CC.img-fun i i₀
  ...   | refl with sv
  ...     | w-row y wk with InvAt.func T.invσ y yK
  ...       | refl = ⊥-elim wk
  stay-at {k} {l} {K = K} i sv lv yK tc₀ i₀ | inj₂ refl | refl | w-bare nr _ = ⊥-elim (nr yK)
  stay-at {k} {l} {K = K} i sv lv yK tc₀ i₀ | inj₁ kc with sv
  ... | w-row {e} y _ = subst ((l ⊕ δ e) ≺_) (qc-path K) (T.img-≺ y yK (Mn.img-mono i i₀ kc) (δ e) (sub w ∷ ix 1 ∷ ix 0 ∷ []))
  ... | w-bare _ _    = ≺-trans {l} {K} {qc K} (Mn.img-mono i i₀ kc) (K≺qc K)

  stay-≺ : ∀ {k l l′ K} → CC.Img k l → Sv l l′ → Live t k → σ K end → l′ ≺ qc K
  stay-≺ {l′ = l′} {K} i sv lv yK with L2 yK
  ... | c₀ , ntc₀ , i₀ = decidable-stable (T? (l′ <ᵖ qc K)) λ n → ntc₀ λ tc₀ → n (stay-at i sv lv yK tc₀ i₀)

  stay-unf : ∀ {k l l′} → CC.Img k l → Sv l l′ → Live t k → ¬ MS.Failed l′
  stay-unf {l′ = l′} i sv lv fl with failed-at fl
  ... | K , yK , lt = ≺-absurd {qc K} {l′} lt (stay-≺ i sv lv yK)

  stay-unfs : ∀ {k l l′} → CC.Img k l → Sv l l′ → Live t k → ¬ MS.Fails l′
  stay-unfs {l′ = l′} i sv lv (_ , x , nf) with fails-at x nf
  ... | K , yK , refl = ≺-irrefl {qc K} (stay-≺ i sv lv yK)

  ----------------------------------------------------------------------
  -- The merge's rows kept

  keep : ∀ {l e} → C l e → Work e → ¬ MS.Failed l → ¬ MS.Fails l → u l e
  keep y wk nf nfs = MS.up (m-c y wk) nf (MS.pass-of nfs (m-c y wk))

  -- The told rows listed, the merge's are.
  L12 : ∀ {w} → Listed C w → Listed m w
  L12 {w} (ks , F , B) = ks ++ fw , F′ , B′
    where
      fw : List Pos
      fw = filter (λ k → T? (k <ᵖ w)) fixL

      F′ : ∀ {k e} → m k e → k ≺ w → k ∈ ks ++ fw
      F′ x kw with mrow x
      ... | mr-c y _  = ∈-++⁺ˡ (F y kw)
      ... | mr-end y  = ∈-++⁺ˡ (F y kw)
      ... | mr-fix f  = ∈-++⁺ʳ ks (∈-filter⁺ (λ k → T? (k <ᵖ w)) (fix-in f) kw)

      B′ : ∀ {k} → k ∈ ks ++ fw → k ≺ w × Σ _ (m k)
      B′ {k} mm with ∈-++⁻ ks mm
      ... | inj₁ m′ = let (kw , _ , y) = B m′ in kw , m-of y
      ... | inj₂ m′ with ∈-filter⁻ (λ k → T? (k <ᵖ w)) {xs = fixL} m′
      ...   | mem , kw with fix-row mem
      ...     | _ , f = kw , _ , m-fix f (ks , λ {k′} y lt → F y (≺-trans {k′} {k} {w} lt kw))

  qc≺Xs : ∀ K → qc K ≺ Xs K
  qc≺Xs K = ≺-ext (qc K) []

  c₁≡ : ∀ K → c₁ K ≡ K ⊕ δ end
  c₁≡ K = proj₂ (T.under-c₁ K)

  -- The told end lies past the failure.
  end-failed : ∀ {c} → C c end → MS.Failed c
  end-failed y with T.ends-raw (T.raw y)
  ... | K , yK , refl = qc K , _ , mx yK , tt , ≺-trans {qc K} {Xs K} {c₁ K} (qc≺Xs K) (Xs≺c₁ K)

  work-or : ∀ (e : Ev (IE A)) → Work e ⊎ e ≡ end
  work-or (out _) = inj₁ tt
  work-or skip    = inj₁ tt
  work-or (pin _) = inj₁ tt
  work-or end     = inj₂ refl

  ----------------------------------------------------------------------
  -- Off the merge's own rows

  c-unfixed : ∀ {l e} → C l e → l ∈ fixL → ⊥
  c-unfixed y mem = cAt-fix (frame-under (InvAt.world IC y) (fix-frame mem)) mem

  σ-unfixed : ∀ {K e x} → σ K e → K ⊑ x → x ∈ fixL → ⊥
  σ-unfixed {K} {x = x} y (zs , refl) mem =
    cAt-fix (⊑-trans {cAt} (⊑-trans {cAt} (⊑-snoc⁺ cAt) (frame-under (InvAt.world invσ y) (trans (sym (instant-⊕ K zs)) (fix-frame mem))))
                     (zs , refl)) mem

  sv-unfixed : ∀ {l l′} → Sv l l′ → l′ ∈ fixL → ⊥
  sv-unfixed (w-row {e} y _) mem = σ-unfixed y (δ e , refl) mem
  sv-unfixed (w-bare _ nf) mem   = nf mem

  ----------------------------------------------------------------------
  -- The take's rows

  data UR : Pos → Ev (IE A) → Set where
    u-c   : ∀ {l e} → C l e → Work e → ¬ MS.Failed l → ¬ MS.Fails l → UR l e
    u-fix : ∀ {l e} → Fix l e → ¬ MS.Failed l → UR l e
    u-pin : ∀ {l r} → C l (pin r) → UR l (pin r)
    u-x   : ∀ {K} → σ K end → UR (qc K ⊕ [ ix 0 ]) (out (marked completed))
    u-end : ∀ {K} → σ K end → UR (Xs K) end

  kept : ∀ {l e} → m l e → ¬ MS.Failed l → ¬ MS.Fails l → UR l e
  kept x nf nfs with mrow x
  ... | mr-c y wk = u-c y wk nf nfs
  ... | mr-end y  = ⊥-elim (nf (end-failed y))
  ... | mr-fix f  = u-fix f nf

  uview : ∀ {l e} → u l e → UR l e
  uview (MS.pass x p nf , _) = kept x nf (MS.pass-fails x p)
  uview (MS.step x nf , _)   = kept x nf (MS.pass-fails x tt)
  uview (MS.tend x nf , _)   = kept x nf (MS.pass-fails x tt)
  uview (MS.left x _ _ , _) with mrow x
  ... | mr-c y _ = u-pin y
  ... | mr-fix ()
  uview (MS.fail x nk _ _ , _) with fails-at x nk
  ... | K , yK , refl with InvAt.func Im x (mx yK)
  ...   | refl = u-x yK
  uview (MS.stop x nk _ , _) with fails-at x nk
  ... | K , yK , refl = u-end yK

  live-C : ∀ {l} → ¬ MS.Failed l → Live C l
  live-C {l} nf yc cl with end-failed yc
  ... | (q , a , x , nk , qc′) = nf (q , a , x , nk , ≺-trans {q} {_} {l} qc′ cl)

  few-C : ∀ {l} → ¬ MS.Failed l → Few u l → Few C l
  few-C nf fw with MS.few← nf fw
  ... | ks , F = ks , λ y lt → F (proj₂ (m-of y)) lt

  lst-C : ∀ {w} → Listed m w → Listed C w
  lst-C (ks , F , B) = filter (λ k → ¬? (any? (k ≟ᵖ_) fixL)) ks , F′ , B′
    where
      F′ : ∀ {k e} → C k e → _ → k ∈ filter (λ k → ¬? (any? (k ≟ᵖ_) fixL)) ks
      F′ y kw = ∈-filter⁺ (λ k → ¬? (any? (k ≟ᵖ_) fixL)) (F (proj₂ (m-of y)) kw) (c-unfixed y)

      B′ : ∀ {k} → k ∈ filter (λ k → ¬? (any? (k ≟ᵖ_) fixL)) ks → _ × Σ _ (C k)
      B′ mm with ∈-filter⁻ (λ k → ¬? (any? (k ≟ᵖ_) fixL)) {xs = ks} mm
      ... | m′ , nfx with B m′
      ...   | kw , _ , x with mrow x
      ...     | mr-c y _ = kw , _ , y
      ...     | mr-end y = kw , _ , y
      ...     | mr-fix f = ⊥-elim (nfx (fix-in f))

  -- A carrier staying put, with a told row there: the take's row.
  stayed : ∀ {k l l′ e′} → CC.Img k l → Sv l l′ → C l′ e′ → Live t k → u l′ e′ × (Listed C l′ → Listed u l′)
  stayed {e′ = e′} i sv y lv with work-or e′
  ... | inj₂ refl = ⊥-elim (stay-unf i sv lv (end-failed y))
  ... | inj₁ wk   = keep y wk (stay-unf i sv lv) (stay-unfs i sv lv) , λ L → MS.lst→ (stay-unf i sv lv) (L12 L)

  -- The take's end listed, from the told run listed past the mark.
  lst-Xs : ∀ {K w} → σ K end → Listed C w → qc K ≼ w → Listed u (Xs K)
  lst-Xs {K} yK L le = MS.lst-cut (first-qc yK) (listed-≼ (L12 L) le) (inj₂ refl)

  ----------------------------------------------------------------------
  -- The carriers

  Img″ : Pos → Pos → Set
  Img″ k l″ = Σ Pos λ l → CC.Img k l × Wv l l″

  -- What a row carried before failing is cut at.
  Cut : Pos → Pos → Set
  Cut k l = Σ Pos λ K → Σ Pos λ c₀ → σ K end × l ≡ Xs K × ¬ ¬ t c₀ end × CC.Img c₀ K × k ≺ c₀ × Σ _ (t k) × Σ Pos (CC.PB k)

  PB″ : Pos → Pos → Set
  PB″ k l = (Cc.PB k l × Σ _ (C l)) ⊎ Cut k l

  sv-c : ∀ {k l l′} → CC.Img k l → Sv l l′ → Cc.Img k l′
  sv-c i (w-row y _)  = _ , i , inj₁ (_ , y , refl)
  sv-c i (w-bare n _) = _ , i , inj₂ ((λ {e} → n {e}) , refl)

  -- A told carrier with a told row: the take's.
  carry-row : ∀ {k l′ e′} → Cc.Img k l′ → C l′ e′ → Live t k
            → Σ Pos λ l″ → Img″ k l″ × u l″ e′ × (Listed C l′ → Listed u l″) × l″ ≼ l′
  carry-row {e′ = e′} (l , i , inj₁ (end , y , refl)) z lv with InvAt.func IC z (subst (λ q → C q end) (c₁≡ l) (endrow y))
  ... | refl = Xs l , (l , i , inj₂ (y , refl)) , stop y
             , (λ L → lst-Xs y L (≺→≼ {qc l} {l ⊕ δ end} (subst (qc l ≺_) (c₁≡ l) (≺-trans {qc l} {Xs l} {c₁ l} (qc≺Xs l) (Xs≺c₁ l)))))
             , ≺→≼ {Xs l} {l ⊕ δ end} (subst (Xs l ≺_) (c₁≡ l) (Xs≺c₁ l))
  carry-row {l′ = l′} (l , i , inj₁ (out _ , y , refl)) z lv = let (uy , L) = stayed i (w-row y tt) z lv in l′ , (l , i , inj₁ (w-row y tt)) , uy , L , ≼-refl {l′}
  carry-row {l′ = l′} (l , i , inj₁ (skip , y , refl)) z lv  = let (uy , L) = stayed i (w-row y tt) z lv in l′ , (l , i , inj₁ (w-row y tt)) , uy , L , ≼-refl {l′}
  carry-row {l′ = l′} (l , i , inj₁ (pin _ , y , refl)) z lv = let (uy , L) = stayed i (w-row y tt) z lv in l′ , (l , i , inj₁ (w-row y tt)) , uy , L , ≼-refl {l′}
  carry-row {l′ = l′} (l , i , inj₂ (nr , refl)) z lv =
    let sv = w-bare (λ {e} → nr {e}) (c-unfixed z) ; (uy , L) = stayed i sv z lv in l′ , (l , i , inj₁ sv) , uy , L , ≼-refl {l′}

  -- A told row the take keeps, carried as the told carry had it.
  c-img : ∀ {k l e} → Cc.Img k l → C l e → Work e → Img″ k l
  c-img (l₀ , i , inj₁ (end , y , refl)) z wk with InvAt.func IC z (subst (λ q → C q end) (c₁≡ l₀) (endrow y))
  ... | refl = ⊥-elim wk
  c-img (l₀ , i , inj₁ (out _ , y , refl)) _ _ = l₀ , i , inj₁ (w-row y tt)
  c-img (l₀ , i , inj₁ (skip , y , refl)) _ _  = l₀ , i , inj₁ (w-row y tt)
  c-img (l₀ , i , inj₁ (pin _ , y , refl)) _ _ = l₀ , i , inj₁ (w-row y tt)
  c-img (l₀ , i , inj₂ (nr , refl)) z _        = l₀ , i , inj₁ (w-bare (λ {e} → nr {e}) (c-unfixed z))

  -- A pin's told carrier is never the failing mark.
  pb-not-x : ∀ {k l} → Cc.PB k l → ¬ MS.Fails l
  pb-not-x (l₁ , _ , e₂ , y₂ , refl) (_ , x , nk) with fails-at x nk
  ... | K , yK , eq with T.at-ix0 yK y₂ (sym eq)
  ...   | refl , _ = T.flatσ yK (subst (λ q → σ q _) (⊕-assoc K [ sub w ] [ ix 1 ]) y₂)

  -- With a carrier stays a told row, at the told run's row.
  sv-row : ∀ {k l l₁ e} → CC.Img k l → Sv l l₁ → Live t k → u l₁ e → Σ _ (C l₁)
  sv-row i sv lv uy with uview uy
  ... | u-c y _ _ _ = _ , y
  ... | u-pin y     = _ , y
  ... | u-fix f _   = ⊥-elim (sv-unfixed sv (fix-in f))
  ... | u-x {K} yK  = ⊥-elim (≺-absurd {qc K} {qc K ⊕ [ ix 0 ]} (≺-ext (qc K) []) (stay-≺ i sv lv yK))
  ... | u-end {K} yK = ⊥-elim (≺-absurd {qc K} {Xs K} (qc≺Xs K) (stay-≺ i sv lv yK))

  unf-≼Xs : ∀ {l K} → ¬ MS.Failed l → σ K end → l ≼ Xs K
  unf-≼Xs {l} {K} nf yK Xl = nf (qc K , _ , mx yK , tt , ≺-trans {qc K} {Xs K} {l} (qc≺Xs K) Xl)

  -- The told row at a cut is none.
  no-C-x : ∀ {K e} → σ K end → C (qc K ⊕ [ ix 0 ]) e → ⊥
  no-C-x yK y = InvAt.flat IC (xrow yK) y

  no-C-Xs : ∀ {K e} → σ K end → C (Xs K) e → ⊥
  no-C-Xs yK y = InvAt.flat IC (xrow yK) y

  live-t : ∀ {k k₀} → k₀ ≼ k → Live t k → Live t k₀
  live-t {k} {k₀} le lv {c} tc = ≼-trans {k₀} {k} {c} le (lv tc)

  live-end : ∀ {c₀} → t c₀ end → Live t c₀
  live-end {c₀} tc tc′ = subst (c₀ ≼_) (end-uniq It tc tc′) (≼-refl {c₀})

  -- A live row with a told pin before the end lies before the end.
  before-end : ∀ {k c₀ l K} → Live t k → ¬ ¬ t c₀ end → CC.Img c₀ K → CC.PB k l → k ≺ c₀
  before-end {k} {c₀} lv ntc₀ i₀ pb = decidable-stable (T? (k <ᵖ c₀)) λ n → ntc₀ λ tc₀ → n (go tc₀)
    where
      go : t c₀ end → k ≺ c₀
      go tc₀ with ≼-split {k} {c₀} (lv tc₀)
      ... | inj₁ lt   = lt
      ... | inj₂ refl = ⊥-elim (CC.pb-img pb i₀)

  ----------------------------------------------------------------------
  -- The fields

  wv-⊑ : ∀ {l l″} → Wv l l″ → l ⊑ l″
  wv-⊑ (inj₁ (w-row {e} _ _))  = δ e , refl
  wv-⊑ {l} (inj₁ (w-bare _ _)) = ⊑-refl l
  wv-⊑ {l} (inj₂ (_ , refl))   = under-Xs l

  ext″ : ∀ {k l″} → Img″ k l″ → Σ Pos λ y → M k y × y ⊑ l″
  ext″ (l , i , wv) with CC.ext i
  ... | y , my , yl = y , my , ⊑-trans {y} yl (wv-⊑ wv)

  wv-fun : ∀ {l a b} → Wv l a → Wv l b → a ≡ b
  wv-fun (inj₁ (w-row y _)) (inj₁ (w-row y′ _)) with InvAt.func invσ y y′
  ... | refl = refl
  wv-fun (inj₁ (w-row y _)) (inj₁ (w-bare n _))   = ⊥-elim (n y)
  wv-fun (inj₁ (w-row y wk)) (inj₂ (y′ , _)) with InvAt.func invσ y y′
  ... | refl = ⊥-elim wk
  wv-fun (inj₁ (w-bare n _)) (inj₁ (w-row y _))   = ⊥-elim (n y)
  wv-fun (inj₁ (w-bare _ _)) (inj₁ (w-bare _ _))  = refl
  wv-fun (inj₁ (w-bare n _)) (inj₂ (y′ , _))      = ⊥-elim (n y′)
  wv-fun (inj₂ (y , _)) (inj₁ (w-row y′ wk)) with InvAt.func invσ y y′
  ... | refl = ⊥-elim wk
  wv-fun (inj₂ (y , _)) (inj₁ (w-bare n _))       = ⊥-elim (n y)
  wv-fun (inj₂ (_ , refl)) (inj₂ (_ , refl))      = refl

  img-fun″ : ∀ {k a b} → Img″ k a → Img″ k b → a ≡ b
  img-fun″ (_ , i , wv) (_ , i′ , wv′) with CC.img-fun i i′
  ... | refl = wv-fun wv wv′

  live″ : ∀ {k l″} → Img″ k l″ → Live t k → Live u l″
  live″ {l″ = l″} (l , i , wv) lv uc with uview uc
  ... | u-c _ () _ _
  ... | u-fix () _
  live″ {l″ = l″} (l , i , inj₁ sv) lv uc | u-end {K} yK =
    ≺→≼ {l″} {Xs K} (≺-trans {l″} {qc K} {Xs K} (stay-≺ i sv lv yK) (qc≺Xs K))
  live″ (l , i , inj₂ (yl , refl)) lv uc | u-end {K} yK with end-uniq invσ yl yK
  ... | refl = ≼-refl {Xs K}

  shown″ : ∀ {l e} → u l e → Shown (One valuesOf) e → Work e → Live u l → Few u l
         → Σ Pos λ k → Img″ k l × Σ (Ev A) λ e₀ → t k e₀ × Match Every (One valuesOf) (Reads valuesOf) e₀ e
  shown″ uy sh wk′ lv fw with uview uy
  ... | u-c y wk nf _ with Cc.shown y sh wk′ (live-C nf) (few-C nf fw)
  ...   | k , ci , e₀ , tk , mt = k , c-img ci y wk , e₀ , tk , mt
  shown″ uy () wk′ lv fw | u-pin _
  shown″ uy () wk′ lv fw | u-fix fx-v0 _
  shown″ uy () wk′ lv fw | u-fix fx-v1 _
  shown″ uy (_ , ()) wk′ lv fw | u-fix fx-sub _
  shown″ uy () wk′ lv fw | u-fix fx-sk _
  shown″ uy () wk′ lv fw | u-fix fx-pass _
  shown″ uy (_ , ()) wk′ lv fw | u-x _
  shown″ uy sh () lv fw | u-end _

  shown-end″ : ∀ {l} → u l end → Live u l → Few u l → Σ Pos λ k → Img″ k l × ¬ ¬ t k end
  shown-end″ uy lv fw with uview uy
  ... | u-c _ () _ _
  ... | u-fix () _
  ... | u-end {K} yK with L2 yK
  ...   | c₀ , ntc₀ , i₀ = c₀ , (K , i₀ , inj₂ (yK , refl)) , ntc₀

  Into″ : Pos → Set
  Into″ = IntoAt Img″ u PB″ (λ _ → ⊥) root

  into″ : ∀ {k e} → t k e → Live t k → IntoAt Cc.Img C Cc.PB (λ _ → ⊥) root k → Into″ k
  into″ {k} tk lv ((l , (e₁ , y) , Ll , pb@(l₁ , pb₁ , _)) , h) = row (MS.search (L12 Ll)) , home h
    where
      row : ¬ MS.Failed l ⊎ Σ Pos (λ f → MS.First f × f ≺ l) → Σ Pos λ l″ → Σ _ (u l″) × Listed u l″ × PB″ k l″
      row (inj₁ nf) with work-or e₁
      ... | inj₂ refl = ⊥-elim (nf (end-failed y))
      ... | inj₁ wk   = l , (e₁ , keep y wk nf (pb-not-x pb)) , MS.lst→ nf (L12 Ll) , inj₁ (pb , e₁ , y)
      row (inj₂ (f , ((_ , x , nk) , _) , fl)) with fails-at x nk
      ... | K , yK , refl with L2 yK
      ...   | c₀ , tc₀ , i₀ =
        Xs K , (end , stop yK) , lst-Xs yK Ll (≺→≼ {qc K} {l} fl)
        , inj₂ (K , c₀ , yK , refl , tc₀ , i₀ , before-end lv tc₀ i₀ pb₁ , (_ , tk) , l₁ , pb₁)

      home : _ → _
      home (inj₁ e) = inj₁ e
      home (inj₂ (inj₁ (k₀ , l₀ , ci₀ , k₀k , ek , (e₀ , y₀) , L₀))) with carry-row ci₀ y₀ (live-t (≺→≼ {k₀} {k} k₀k) lv)
      ... | l″ , i″ , uy , lst , _ = inj₂ (inj₁ (k₀ , l″ , i″ , k₀k , ek , (e₀ , uy) , lst L₀))
      home (inj₂ (inj₂ (_ , () , _)))

  img″ : ∀ {k e} → t k e → Unpinned e → Live t k → Listed t k → ⊤
       → (Σ Pos λ l → Img″ k l × Σ (Ev (IE A)) λ e′ → u l e′ × Listed u l × Match Every (One valuesOf) (Reads valuesOf) e e′)
         ⊎ (e ≡ skip × Into″ k)
  img″ tk un lv L lp with Cc.img tk un lv L lp
  ... | inj₂ (es , h) = inj₂ (es , into″ tk lv h)
  ... | inj₁ (l′ , ci , e′ , y , Ll , mt) with carry-row ci y lv
  ...   | l″ , i″ , uy , lst , _ = inj₁ (l″ , i″ , e′ , uy , lst Ll , mt)

  img¬¬″ : ∀ {k e} → t k e → Unpinned e → Live t k → Few t k
         → ¬ ¬ ((Σ Pos λ l → Img″ k l × Σ (Ev (IE A)) λ e′ → u l e′ × Match Every (One valuesOf) (Reads valuesOf) e e′) ⊎ e ≡ skip)
  img¬¬″ tk un lv fw n = Cc.img¬¬ tk un lv fw λ
    { (inj₂ es) → n (inj₂ es)
    ; (inj₁ (l′ , ci , e′ , y , mt)) → let (l″ , i″ , uy , _ , _) = carry-row ci y lv in n (inj₁ (l″ , i″ , e′ , uy , mt)) }

  ----------------------------------------------------------------------
  -- Placing

  Placed″ : Pos → Set
  Placed″ z = instantOf z ≡ instantOf root ⊎ (Σ Pos λ k → Σ Pos λ l → Img″ k l × instantOf l ≡ instantOf z × Near u z l)
              ⊎ Σ Pos λ h → ⊥ × instantOf h ≡ instantOf z

  inst-qc : ∀ K → instantOf (qc K) ≡ instantOf K
  inst-qc K = trans (cong instantOf (sym (qc-path K))) (instant-⊕ K (sub w ∷ ix 1 ∷ ix 0 ∷ []))

  -- Placed by the take's end, listed past a row of its instant.
  placed-cut : ∀ {K z} → σ K end → Listed m (qc K) → instantOf (qc K) ≡ instantOf z → Placed″ z
  placed-cut {K} yK Lq ie with L2 yK
  ... | c₀ , _ , i₀ = inj₂ (inj₁ (c₀ , Xs K , (K , i₀ , inj₂ (yK , refl)) , trans (instant-⊕ (qc K) [ last ]) ie
                     , inj₂ ((end , stop yK) , MS.lst-cut (first-qc yK) Lq (inj₂ refl))))

  before-x : ∀ {z K} → ¬ MS.Failed z → ¬ MS.Fails z → σ K end → z ≺ qc K
  before-x {z} {K} nf nfs yK with ≼-split {z} {qc K} (λ lt → nf (qc K , _ , mx yK , tt , lt))
  ... | inj₁ lt   = lt
  ... | inj₂ refl = ⊥-elim (nfs (_ , mx yK , tt))

  -- A kept row near a staying carrier: near its row, or, that row cut,
  -- near the take's end.
  near-stay : ∀ {k l′ z} → Img″ k l′ → instantOf l′ ≡ instantOf z → Near C z l′ → ¬ MS.Failed z → ¬ MS.Fails z → Placed″ z
  near-stay i″ ie (inj₁ le) _ _ = inj₂ (inj₁ (_ , _ , i″ , ie , inj₁ le))
  near-stay {l′ = l′} {z} i″ ie (inj₂ ((e₂ , y₂) , L₂)) nfz nfsz with MS.search (L12 L₂)
  ... | inj₂ (f , ((_ , x , nk) , _) , fl) with fails-at x nk
  ...   | K , yK , refl = placed-cut {K} {z} yK (sub-listed (L12 L₂) fl) (between {z} {qc K} {l′} (before-x nfz nfsz yK) fl ie)
  near-stay {l′ = l′} {z} i″ ie (inj₂ ((e₂ , y₂) , L₂)) nfz nfsz | inj₁ nf with MS.fails? (proj₂ (m-of y₂))
  ... | inj₁ (_ , x , nk) with fails-at x nk
  ...   | K , yK , refl = placed-cut {K} {z} yK (L12 L₂) ie
  near-stay {l′ = l′} {z} i″ ie (inj₂ ((e₂ , y₂) , L₂)) nfz nfsz | inj₁ nf | inj₂ nfs with work-or e₂
  ... | inj₁ wk   = inj₂ (inj₁ (_ , _ , i″ , ie , inj₂ ((e₂ , keep y₂ wk nf nfs) , MS.lst→ nf (L12 L₂))))
  ... | inj₂ refl = ⊥-elim (nf (end-failed y₂))

  -- A kept told row, placed as the told carry placed it.
  from-c : ∀ {z e} → C z e → ¬ MS.Failed z → ¬ MS.Fails z
         → instantOf z ≡ instantOf cAt ⊎ (Σ Pos λ k → Σ Pos λ l → Cc.Img k l × instantOf l ≡ instantOf z × Near C z l)
           ⊎ Σ Pos (λ h → ⊥ × instantOf h ≡ instantOf z)
         → Placed″ z
  from-c y nf nfs (inj₁ eq) = inj₁ eq
  from-c y nf nfs (inj₂ (inj₂ (_ , () , _)))
  from-c {z} y nf nfs (inj₂ (inj₁ (k , _ , (l₀ , i , inj₁ (end , y₁ , refl)) , ie , nr))) with nr
  ... | inj₁ le = ⊥-elim (nf (MS.failed-up (end-failed (subst (λ q → C q end) (c₁≡ l₀) (endrow y₁))) le))
  ... | inj₂ (_ , L₂) =
    placed-cut {l₀} {z} y₁ (listed-≼ (L12 L₂) (≺→≼ {qc l₀} {l₀ ⊕ δ end} (subst (qc l₀ ≺_) (c₁≡ l₀) (≺-trans {qc l₀} {Xs l₀} {c₁ l₀} (qc≺Xs l₀) (Xs≺c₁ l₀)))))
      (trans (inst-qc l₀) (trans (sym (instant-⊕ l₀ (δ end))) ie))
  from-c y nf nfs (inj₂ (inj₁ (k , _ , (l₀ , i , inj₁ (out _ , y₁ , refl)) , ie , nr))) = near-stay (l₀ , i , inj₁ (w-row y₁ tt)) ie nr nf nfs
  from-c y nf nfs (inj₂ (inj₁ (k , _ , (l₀ , i , inj₁ (skip , y₁ , refl)) , ie , nr))) = near-stay (l₀ , i , inj₁ (w-row y₁ tt)) ie nr nf nfs
  from-c y nf nfs (inj₂ (inj₁ (k , _ , (l₀ , i , inj₁ (pin _ , y₁ , refl)) , ie , nr))) = near-stay (l₀ , i , inj₁ (w-row y₁ tt)) ie nr nf nfs
  from-c y nf nfs (inj₂ (inj₁ (k , _ , (l₀ , i , inj₂ (nr′ , refl)) , ie , nr))) with any? (l₀ ≟ᵖ_) fixL
  ... | yes mem = inj₁ (trans (sym ie) (fix-frame mem))
  ... | no nm   = near-stay (l₀ , i , inj₁ (w-bare (λ {e} → nr′ {e}) nm)) ie nr nf nfs

  place″ : ∀ {z e} → u z e → Live u z → Listed u z → Placed″ z
  place″ uy lv Lu with uview uy
  ... | u-fix f _ = inj₁ (fix-frame (fix-in f))
  ... | u-end {K} yK with L2 yK
  ...   | c₀ , _ , i₀ = inj₂ (inj₁ (c₀ , Xs K , (K , i₀ , inj₂ (yK , refl)) , refl , inj₁ (≼-refl {Xs K})))
  place″ {z} uy lv Lu | u-x {K} yK =
    placed-cut {K} {z} yK (MS.lst← (never-before yK) (sub-listed Lu (≺-ext (qc K) []))) (sym (instant-⊕ (qc K) [ ix 0 ]))
  place″ uy lv Lu | u-c y wk nf nfs = from-c y nf nfs (Cc.place y (live-C nf) (lst-C (MS.lst← nf Lu)))
  place″ uy lv Lu | u-pin y with MS.live-unfailed lv (proj₂ (m-of y))
  ... | nf = from-c y nf (MS.pass-fails (proj₂ (m-of y)) tt) (Cc.place y (live-C nf) (lst-C (MS.lst← nf Lu)))

  ----------------------------------------------------------------------
  -- Whole and covered

  whole″ : Whole t → (∀ {c} → t c end → ⊥) → (∀ {q : Pos} → ⊤) → Whole u
  whole″ wt ne lp with Cc.whole wt ne (λ {q : Pos} → tt)
  ... | ks , F , B = ks ++ fixL , F′ , B′
    where
      noend : ∀ {K} → σ K end → ⊥
      noend yK = proj₁ (proj₂ (L2 yK)) ne

      nofail : ∀ {l} → ¬ MS.Failed l
      nofail fl = noend (proj₁ (proj₂ (failed-at fl)))

      nofails : ∀ {l} → ¬ MS.Fails l
      nofails (_ , x , nk) = noend (proj₁ (proj₂ (fails-at x nk)))

      F′ : ∀ {k e} → u k e → k ∈ ks ++ fixL
      F′ uy with uview uy
      ... | u-c y _ _ _ = ∈-++⁺ˡ (F y)
      ... | u-pin y     = ∈-++⁺ˡ (F y)
      ... | u-fix f _   = ∈-++⁺ʳ ks (fix-in f)
      ... | u-x yK      = ⊥-elim (noend yK)
      ... | u-end yK    = ⊥-elim (noend yK)

      B′ : ∀ {k} → k ∈ ks ++ fixL → Σ _ (u k)
      B′ mm with ∈-++⁻ ks mm
      ... | inj₁ m′ with B m′
      ...   | e , y with work-or e
      ...     | inj₁ wk   = e , keep y wk nofail nofails
      ...     | inj₂ refl = ⊥-elim (nofail (end-failed y))
      B′ mm | inj₂ m′ with fix-row m′
      ... | e , f = e , MS.up (m-fix f (ks , λ y _ → F y)) nofail (MS.pass-of nofails (m-fix f (ks , λ y _ → F y)))

  xm : ∀ {P : Set} → ((P ⊎ ¬ P) → ⊥) → ⊥
  xm h = h (inj₂ λ p → h (inj₁ p))

  cover″ : ∀ {v w} → Listed t v → ⊤ → Live t v → From Img″ PB″ t u v w → Listed u w
  cover″ {v} {w} L lp lv F″ = go (Cc.cover L lp lv Fc)
    where
      Fc : From Cc.Img Cc.PB t C v w
      Fc {l = l} tk lvk vk (inj₁ ci) y with carry-row ci y lvk
      ... | l″ , i″ , uy , _ , le = ≼-trans {w} {l″} {l} (F″ tk lvk vk (inj₁ i″) uy) le
      Fc {k} {e} {l} {e′} tk lvk vk (inj₂ pb@(l₁ , pb₁ , _)) y lw = xm go′
        where
          go′ : MS.Failed l ⊎ ¬ MS.Failed l → ⊥
          go′ (inj₂ nf) with work-or e′
          ... | inj₂ refl = nf (end-failed y)
          ... | inj₁ wk   = F″ tk lvk vk (inj₂ (inj₁ (pb , e′ , y))) (keep y wk nf (pb-not-x pb)) lw
          go′ (inj₁ fl) with failed-at fl
          ... | K , yK , ql with L2 yK
          ...   | c₀ , tc₀ , i₀ =
            F″ tk lvk vk (inj₂ (inj₂ (K , c₀ , yK , refl , tc₀ , i₀ , before-end lvk tc₀ i₀ pb₁ , (_ , tk) , l₁ , pb₁))) (stop yK)
              (≺-trans {Xs K} {l} {w} (MS.cut-before (mx yK) (proj₂ (m-of y)) ql last) lw)

      go : Listed C w → Listed u w
      go LC with MS.search (L12 LC)
      ... | inj₁ nf = MS.lst→ nf (L12 LC)
      ... | inj₂ (f , ((_ , x , nk) , _) , fw) with fails-at x nk
      ...   | K , yK , refl with L2 yK
      ...     | c₀ , tc₀ , i₀ =
        listed-≼ (lst-Xs yK LC (≺→≼ {qc K} {w} fw)) λ lt → tc₀ λ tc → F″ tc (live-end tc) (lv tc) (inj₁ (K , i₀ , inj₂ (yK , refl))) (stop yK) lt

  ----------------------------------------------------------------------
  -- Pins and their carriers

  bk″ : Pos → List Pos
  bk″ l″ = Cc.bk l″ ++ Cc.bk (parent (parent l″) ⊕ [ last ])

  in-bk″ : ∀ {k l″} → Img″ k l″ → k ∈ bk″ l″
  in-bk″ (l , i , inj₁ sv) = ∈-++⁺ˡ (Cc.in-bk (sv-c i sv))
  in-bk″ {k} (l , i , inj₂ (y , refl)) = ∈-++⁺ʳ (Cc.bk (Xs l)) (subst (λ z → k ∈ Cc.bk z) eq (Cc.in-bk {k} {l ⊕ δ end} (l , i , inj₁ (end , y , refl))))
    where
      eq : l ⊕ δ end ≡ parent (parent (Xs l)) ⊕ [ last ]
      eq = trans (sym (c₁≡ l)) (cong (_⊕ [ last ]) (sym (trans (cong parent (parent-snoc (qc l) last)) (parent-snoc (Pk l) (ix 0)))))

  pb-few″ : ∀ {l e} → u l e → Σ (List Pos) λ ks → ∀ {k} → PB″ k l → k ∈ ks
  pb-few″ uy with uview uy
  ... | u-c y _ _ _ = proj₁ (Cc.pb-few y) , λ { (inj₁ (pb , _)) → proj₂ (Cc.pb-few y) pb ; (inj₂ (K , _ , yK , eq , _)) → ⊥-elim (no-C-Xs yK (subst (λ q → C q _) eq y)) }
  ... | u-pin y     = proj₁ (Cc.pb-few y) , λ { (inj₁ (pb , _)) → proj₂ (Cc.pb-few y) pb ; (inj₂ (K , _ , yK , eq , _)) → ⊥-elim (no-C-Xs yK (subst (λ q → C q _) eq y)) }
  ... | u-fix f _   = [] , λ { (inj₁ (_ , _ , y)) → ⊥-elim (c-unfixed y (fix-in f))
                             ; (inj₂ (K , _ , yK , eq , _)) → ⊥-elim (σ-unfixed yK (under-Xs K) (subst (_∈ fixL) eq (fix-in f))) }
  ... | u-x {K} yK  = [] , λ { (inj₁ (_ , _ , y)) → ⊥-elim (no-C-x yK y) ; (inj₂ (K′ , _ , _ , eq , _)) → ⊥-elim (ix≢last (⊕-injʳ (qc K) (qc K′) eq)) }
    where
      ix≢last : ix 0 ≡ last → ⊥
      ix≢last ()
  ... | u-end yK with L2 yK
  ...   | c₀ , tc₀ , i₀ = proj₁ (CC.few i₀) , λ { (inj₁ (_ , _ , y)) → ⊥-elim (no-C-Xs yK y)
                                                ; {k} (inj₂ (_ , _ , _ , _ , tc₀′ , _ , kc , (_ , tk) , _)) → ∈-stable λ n → tc₀′ λ tc′ → tc₀ λ tc → n (proj₂ (CC.few i₀) tk (subst (k ≺_) (end-uniq It tc′ tc) kc)) }

  pb-img″ : ∀ {k l l′} → PB″ k l → Img″ k l′ → ⊥
  pb-img″ (inj₁ ((_ , pb , _) , _)) (_ , i , _)                  = CC.pb-img pb i
  pb-img″ (inj₂ (_ , _ , _ , _ , _ , _ , _ , _ , _ , pb)) (_ , i , _) = CC.pb-img pb i

  pb-past″ : ∀ {k l e₀ e x y} → PB″ k l → t k e₀ → (Unpinned e₀ → Live t k) → u l e → M x y → x ≺ k → ¬ (x ⊑ k) → Ahead y l
  pb-past″ (inj₁ (pb , _ , z)) tk lv _ mxy xk nx = Cc.pb-past pb tk lv z mxy xk nx
  pb-past″ {k} {x = x} (inj₂ (K , c₀ , yK , refl , tc₀ , i₀ , kc , _)) _ _ _ mxy xk nx with CC.ext i₀
  ... | y₀ , m₀ , y₀K =
    ahead-over (Emb.mono hm mxy m₀ (≺-trans {x} {k} {c₀} xk kc) , λ yy → nx (conv (⊑-refl x) (≺→≼ {x} {k} xk) kc (Emb.reflect hm mxy m₀ yy)))
      (⊑-trans {y₀} y₀K (under-Xs K))

  Homed : Pos → Pos → Set
  Homed k p = instantOf k ≡ instantOf root ⊎ (Σ Pos λ k₀ → k₀ ≺ p × Home t k₀ × instantOf k₀ ≡ instantOf k) ⊎ Σ Pos λ h → ⊥ × instantOf h ≡ instantOf k

  pinned″ : ∀ {k p} → t k (pin p) → Live t k → Listed t k → ⊤ → InOrder Img″ PB″ t u k × Homed k p
  pinned″ {k} tk lv L lp with Cc.pinned tk lv L lp
  ... | (l , (e , y) , pb@(l₁ , pb₁ , _) , LC , Fc) , h = io (MS.search (L12 LC)) , h
    where
      io : ¬ MS.Failed l ⊎ Σ Pos (λ f → MS.First f × f ≺ l) → InOrder Img″ PB″ t u k
      io (inj₁ nf) with work-or e
      ... | inj₂ refl = ⊥-elim (nf (end-failed y))
      ... | inj₁ wk   = l , (e , keep y wk nf (pb-not-x pb)) , inj₁ (pb , e , y) , MS.lst→ nf (L12 LC) , fr
        where
          fr : From Img″ PB″ t u k l
          fr tk₁ lv₁ kk (inj₁ (l₀ , i , inj₁ sv)) uy          = Fc tk₁ lv₁ kk (inj₁ (sv-c i sv)) (proj₂ (sv-row i sv lv₁ uy))
          fr tk₁ lv₁ kk (inj₁ (l₀ , i , inj₂ (yl₀ , refl))) _ = unf-≼Xs nf yl₀
          fr tk₁ lv₁ kk (inj₂ (inj₁ (pb′ , _ , z))) _          = Fc tk₁ lv₁ kk (inj₂ pb′) z
          fr tk₁ lv₁ kk (inj₂ (inj₂ (K , _ , yK , refl , _))) _ = unf-≼Xs nf yK
      io (inj₂ (f , ((_ , x , nk) , _) , fl)) with fails-at x nk
      ... | K , yK , refl with L2 yK
      ...   | c₀ , tc₀ , i₀ =
        Xs K , (end , stop yK) , inj₂ (K , c₀ , yK , refl , tc₀ , i₀ , before-end lv tc₀ i₀ pb₁ , (_ , tk) , l₁ , pb₁)
        , lst-Xs yK LC (≺→≼ {qc K} {l} fl) , fr
        where
          fr : From Img″ PB″ t u k (Xs K)
          fr {l = l₂} tk₁ lv₁ kk (inj₁ (l₀ , i , inj₁ sv)) uy =
            ⊥-elim (Fc tk₁ lv₁ kk (inj₁ (sv-c i sv)) (proj₂ (sv-row i sv lv₁ uy)) (≺-trans {l₂} {qc K} {l} (stay-≺ i sv lv₁ yK) fl))
          fr tk₁ lv₁ kk (inj₁ (l₀ , i , inj₂ (yl₀ , refl))) _ with end-uniq invσ yl₀ yK
          ... | refl = ≼-refl {Xs K}
          fr {l = l₂} tk₁ lv₁ kk (inj₂ (inj₁ (pb′ , _ , z))) uy with Fc tk₁ lv₁ kk (inj₂ pb′) z | uview uy
          ... | le | u-c _ _ nf₁ _ = ⊥-elim (nf₁ (qc K , _ , mx yK , tt , ≺-≼-≺ {qc K} {l} {l₂} fl le))
          ... | le | u-fix _ nf₁   = ⊥-elim (nf₁ (qc K , _ , mx yK , tt , ≺-≼-≺ {qc K} {l} {l₂} fl le))
          ... | le | u-pin z′      = ≺→≼ {Xs K} {l₂} (MS.cut-before (mx yK) (proj₂ (m-of z′)) (≺-≼-≺ {qc K} {l} {l₂} fl le) last)
          ... | le | u-x yK′       = ⊥-elim (no-C-x yK′ z)
          ... | le | u-end yK′     = ⊥-elim (no-C-Xs yK′ z)
          fr tk₁ lv₁ kk (inj₂ (inj₂ (K′ , _ , yK′ , refl , _))) _ with end-uniq invσ yK′ yK
          ... | refl = ≼-refl {Xs K}

  ----------------------------------------------------------------------
  -- The take's carry

  carried : CarryAt valuesOf M (λ _ → ⊥) (λ _ → ⊥) (λ _ → ⊤) t u root root
  carried = record
    { Img = Img″ ; ext = ext″ ; PB = PB″ ; pb-few = pb-few″ ; pb-img = pb-img″ ; pb-past = pb-past″
    ; img = img″ ; img¬¬ = img¬¬″ ; shown = shown″ ; shown-end = shown-end″
    ; img-row = λ { (_ , i , _) → CC.img-row i } ; img-fun = img-fun″
    ; place = place″ ; live = live″ ; few = λ { (_ , i , _) → CC.few i }
    ; whole = whole″ ; cover = cover″ ; bk = bk″ ; in-bk = in-bk″ ; pinned = pinned″ }
