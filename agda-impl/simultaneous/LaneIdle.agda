{-# OPTIONS --guardedness #-}

-- A LANE OF THE REAL FLATMAP IS IDLE ON ITS OWN (`lane-idle`).  A lane is
-- its value's elaboration at one admissible, early subscription
-- (`lane-sub`), and there it is a take of its two parts' merge, cut at
-- its own `laneDone`, which moves no route: so the take is idle wherever
-- the merge is idle up to that cut (`TakeIdle`).
module simultaneous.LaneIdle where

open import Data.Bool using (true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_; yes; no)
open import simultaneous.Instants using (_≺ⁱ_; ≺-instant; instant-≺)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; of; flatMap; takeWhile)
open import denotation.Position using (Pos; root; _≟ᵖ_; _≟ⁱ_; ix; instant; _∙_; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Ev; DenEnv; hot; enter; out; end; pin; Few; _≺_; After; shown; module Op; module Bounded; module Merge)
open import denotation.Laws.Modulus using (≼-or-≻; ≼-split; ≼-refl; ≺→≼)
open import denotation.Laws.Worlds.Leaves using (ine-pin)
open import denotation.Read using (Run; []; _∷_)
open import denotation.Laws.Worlds using (Ok; InvAt; InvD; Lawful; Hots; GoodEnv; ok-step; plain-ix; world-after)
open import denotation.Laws.BoundedInv using (module BoundedI)
open import simultaneous.SObs using (lone; lanePart; burstPart; module Elaborate)
open import simultaneous.InstEmit using (instEmit; value)
open import simultaneous.Routed using (Held; Early; Idle; HeldD; Placed; PlacedD; Adm)
open import simultaneous.HeldComb using (ev)
open import simultaneous.HeldConnect using (early-inst)
open import simultaneous.HeldTake using (module TakeIdle)
open import simultaneous.HeldTo using (IdleTo; Unfailed)
open import simultaneous.LaneLocal using (inv-ev; EndsEarly; held-fit; module FlatFit; module LaneReal; undone-done; done; of-outer)
open import simultaneous.LaneOnce using (module LaneOnce)
open import simultaneous.RealView using (module View)
open import simultaneous.IdleThin using (module Thin)
open import simultaneous.ConcatTwo using (module Two)
open import simultaneous.EnterFew using (enter-few)
open import simultaneous.ColdIdle using (mid)
open import simultaneous.LaneDoneRow using (done-row)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; laneˢ; undone; counted; framed; shareˢ; count)

-- A take of the meaning or of an approximant is the take of its source's.
ev-take : ∀ m {Γ X} (k : X → _) (o : Obs Timeline Γ X) (ρ : DenEnv Γ) → ev m (takeWhile true k o) ρ ≡ Op.takeWhile true k (ev m o ρ)
ev-take nothing  k o ρ = refl
ev-take (just _) k o ρ = refl

-- An `of`, read as the meaning's or an approximant's, is the `of`'s.
of-to : ∀ m {Γ X} (xs : List X) (ρ : DenEnv Γ) p {y e} → enter (ev m (of xs) ρ) p y e → enter (Op.of xs) p y e
of-to nothing  xs ρ p r = r
of-to (just _) xs ρ p r = r

of-from : ∀ m {Γ X} (xs : List X) (ρ : DenEnv Γ) p {y e} → enter (Op.of xs) p y e → enter (ev m (of xs) ρ) p y e
of-from nothing  xs ρ p r = r
of-from (just _) xs ρ p r = r

-- A flatMap read through its parts is the flatMap's.
flat-from : ∀ m {Γ X Y} op (g : X → Obs Timeline Γ Y) (o : Obs Timeline Γ X) (ρ : DenEnv Γ) p {y e}
          → enter (Op.flatMap op (λ c → ev m (g c) ρ) (ev m o ρ)) p y e → enter (ev m (flatMap op g o) ρ) p y e
flat-from nothing  op g o ρ p r = r
flat-from (just _) op g o ρ p r = r

-- An `each` of nothing over a hot pins nothing: the hot's pins are heard
-- as skips, and its lanes are empty `of`s.
hot-each-nopin : ∀ {X Y} (t : EmissionSet X) s {k r} → enter (Op.flatMap (mergeᶠ nothing) (λ _ → Op.of {Y} []) (hot t)) s k (pin r) → ⊥
hot-each-nopin t s (Merge.opin (shown _ () _ , _) , _)
hot-each-nopin t s (Merge.left _ _ ((l , _) , _) _ _ , _) = ine-pin l
hot-each-nopin t s (Merge.run () _ , _)

-- IDLENESS IS A PROPERTY OF THE ROWS: two sets holding the same rows are
-- idle together.
module Same {X : Set} {t u : EmissionSet (IE X)} (to : ∀ {y e} → t y e → u y e) (from : ∀ {y e} → u y e → t y e) where

  few : ∀ {w} → Few t w → Few u w
  few (ks , h) = ks , λ x lt → h (from x) lt

  run : ∀ {c rs} → Run t c rs → Run u c rs
  run [] = []
  run ((((x , pe) , fw) , v , ac , lst) ∷ r) = (((to x , λ ce → pe (from ce)) , few fw) , v , ac , λ k v′ a → lst (from k) v′ a) ∷ run r

  idle : Idle u → Idle t
  idle iu mt ne fw aw lw = iu (run mt) ne (few fw) aw λ x v a → lw (from x) v a

module LaneIdle (m : Maybe ℕ) {Γ Θ A B} {Fr : Pos → Set} (op : FlatOp) (f : A → Obs Timeline Γ B)
                (ρ₄ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ ⊤ ∷ IE B ∷ IE A ∷ Θ)
                (t₂ : EmissionSet (IE B)) (t₁ : EmissionSet (IE A)) (env₀ : DenEnv Θ)
                (g₂ : GoodEnv (hot t₂ ∷ hot t₁ ∷ env₀)) (L₁ : Lawful t₁)
                (tv : ∀ {r b n} → t₁ r (out (instEmit (value b) n)) → Early r) (te : EndsEarly t₁) (tp : Placed Fr t₁)
                (ad : Adm (Hots (hot t₂ ∷ hot t₁ ∷ env₀)) Fr) (cs : List Pos)
                (held : ∀ a {t} → Lawful t → HeldD (Hots (hot t ∷ hot t₂ ∷ hot t₁ ∷ env₀)) Fr (ev m (elab ρ₄ (f a)) (hot t ∷ hot t₂ ∷ hot t₁ ∷ env₀)) cs)
                (placed : ∀ a {t} → Lawful t → PlacedD (Hots (hot t ∷ hot t₂ ∷ hot t₁ ∷ env₀)) Fr (ev m (elab ρ₄ (f a)) (hot t ∷ hot t₂ ∷ hot t₁ ∷ env₀))) where

  open LaneReal m op f ρ₄ t₂ t₁ env₀ g₂ L₁ tv te tp ad (λ a L p ok fp ep → held-fit (held a L p ok fp ep) (placed a L p ok fp ep)) using (env₂; x; srcE; laneE)
  open LaneOnce m op f ρ₄ t₂ t₁ env₀ g₂ L₁ tv te tp ad cs held placed using (dR; fL; Id; Il; ok-o; vals; module Share)

  -- A lane's two parts, merged, ahead of its take.
  merged : A → Obs Timeline (IE B ∷ IE A ∷ Θ) (IE B)
  merged a = flatMap (mergeᶠ nothing) (λ k → shareˢ (x a k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ []))

  -- THE MERGE'S ROWS ARE ITS PROGRAM'S, where the lane part's share runs
  -- it past its blocker, framed by marks that move no route.
  module Rows (a : A) (s : Pos) (ok : Ok (Hots env₂) s) (fs : Fr s) (es : Early s) where
    open Share a s ok fs es using (tS; Lt; tee; env′; g′; Q; okQ; fQ; eQ; fc; dQ; ad′)

    Mg : EmissionSet (IE B)
    Mg = enter (ev m (merged a) env₂) s

    -- The lane part's share, at its subscription.
    Sh : EmissionSet (IE B)
    Sh = enter (ev m (flatMap (mergeᶠ (just 1)) (x a lanePart) (of (true ∷ false ∷ []))) env′) Q

    Prog : Pos → EmissionSet (IE B)
    Prog s′ = enter (ev m (elab ρ₄ (f a)) env′) s′

    -- Where the share's bounded merge runs the program: its second lane.
    Runs : Pos → Set
    Runs s′ = Σ ℕ λ i → Σ Pos λ q → Bounded.Sub 1 fc (enter dQ Q) i q s′ false

    runs-at : ∀ {s′} → Runs s′ → Early s′ × Ok (Hots env′) s′ × Fr s′
    runs-at (i , _ , N , St) =
      FlatFit.Bd.start-at fc dQ ad′ (inv-ev m (of (true ∷ false ∷ [])) env′ g′) (λ c → inv-ev m (x a lanePart c) env′ g′)
        (srcE a lanePart tS Lt tee) Q okQ (proj₁ O) (proj₁ (proj₂ O)) (proj₂ (proj₂ O)) 1 i N St
      where O = of-outer m _ env′ ad′ Q okQ fQ eQ

    postulate
      -- The blocker ends, so the program runs.
      prog-runs : Σ Pos Runs

      -- A value of the merge is the program's, or a frame mark at a place
      -- the program holds nothing.
      rows-vis : ∀ {s′} → Runs s′ → ∀ {q v} → Mg q (out v) → Prog s′ q (out v) ⊎ ((∀ r → count r v ≡ r) × (∀ {e′} → Prog s′ q e′ → ⊥))

      -- Each row of the program lies at a row of the merge,
      rows-lift : ∀ {s′} → Runs s′ → ∀ {q e} → Prog s′ q e → Σ (Ev (IE B)) (Mg q)

      -- its values shown as they are.
      rows-shown : ∀ {s′} → Runs s′ → ∀ {q v} → Prog s′ q (out v) → Mg q (out v)

    -- THE SHARE'S END RUNS THE `laneDone`, IN ITS INSTANT.
    share-done : ∀ {e} → Sh e end → ¬ ¬ (Σ Pos λ f′ → Σ (IE B) λ v → Mg f′ (out v) × T (not (undone v)) × instant f′ ≡ instant e)
    share-done se = done-row ρ₄ (f a) env₂ m s se

    -- The share's bounded merge: its outer `of [ true , false ]`, its first
    -- lane the blocker, its second the program.
    module T2 = Two fc (enter dQ Q) Q true false (λ {y} {e} r → of-to m (true ∷ false ∷ []) env′ Q {y} {e} r)
                                                  (λ {y} {e} r → of-from m (true ∷ false ∷ []) env′ Q {y} {e} r)

    fi : ∀ c → InvD (Hots env′) (fc c)
    fi c = inv-ev m (x a lanePart c) env′ g′

    Io : InvAt (Hots env′) Q (enter dQ Q)
    Io = inv-ev m (of (true ∷ false ∷ [])) env′ g′ Q okQ

    -- The blocker pins nothing.
    blk-np : ∀ m′ {s′ k r} → enter (ev m′ (x a lanePart true) env′) s′ k (pin r) → ⊥
    blk-np nothing  {s′} = hot-each-nopin tS s′
    blk-np (just _) {s′} = hot-each-nopin tS s′

    -- THE END'S INSTANT HOLDING FEW ROWS OF THE MERGE, THE SHARE'S MERGE
    -- ENDS THERE: at the program's end, or, the program ending in the
    -- subscribing instant, at its outer's.  Its rows before that are the
    -- blocker's, which are few before its end and none past it, and the
    -- program's, few before its end and past it in its instant.
    share-ends : ∀ {s′} → Runs s′ → ∀ {c} → Prog s′ c end → (ks : List Pos) → (∀ {y e} → Mg y e → instant y ≡ instant c → y ∈ ks)
               → ¬ ¬ (Σ Pos λ e → Sh e end × instant e ≡ instant c)
    share-ends {s′} rn@(i , q , N , St₀) {c} uc ks h k =
      k (E , flat-from m (mergeᶠ (just 1)) (x a lanePart) (of (true ∷ false ∷ [])) env′ Q (R.row ea) , E2.end-inst ea)
      where
        St : Bounded.Starts 1 fc (enter dQ Q) 1 T2.q₁ (Bounded.Sched 1 fc (enter dQ Q) 1) s′
        St = T2.second (λ ()) refl (N , St₀)

        Ip : InvAt (Hots env′) s′ (Prog s′)
        Ip = inv-ev m (elab ρ₄ (f a)) env′ g′ s′ (proj₁ (proj₂ (runs-at rn)))

        c₀ = proj₁ (T2.first-end St)
        e₀ = proj₂ (T2.first-end St)

        u₀ : ∀ {c′} → After (fc true) (T2.q₀ ⊕ [ ix 1 ]) c′ end → c′ ≡ c₀
        u₀ e′ = BoundedI.lane-end okQ 1 fc fi Io T2.sub₀ e′ e₀

        module E2 = T2.End {c₀} {c} {s′} e₀ u₀ St (uc , world-after (InvAt.world Ip uc) (InvAt.real Ip uc))

        E = proj₁ E2.end-at
        ea = proj₂ E2.end-at

        Ib : InvAt (Hots env′) (T2.q₀ ⊕ [ ix 1 ]) (enter (fc true) (T2.q₀ ⊕ [ ix 1 ]))
        Ib = BoundedI.LI okQ 1 fc fi Io T2.sub₀

        rb = enter-few (fc true) (T2.q₀ ⊕ [ ix 1 ]) (proj₁ e₀) tt
        rc = enter-few (ev m (elab ρ₄ (f a)) env′) s′ uc tt

        KS : List Pos
        KS = c₀ ∷ c ∷ (proj₁ rb ++ proj₁ rc ++ ks)

        -- The blocker's rows: up to its end, it pinning nothing.
        blk-in : ∀ {y e} → After (fc true) (T2.q₀ ⊕ [ ix 1 ]) y e → y ≺ E → y ∈ KS
        blk-in {y} {e} (r , _) _ =
          [ (λ le → [ (λ lt → there (there (∈-++⁺ˡ (proj₂ rb r lt)))) , here ]′ (≼-split {y} {c₀} le))
          , (λ c₀y → let (_ , eq , _) = InvAt.quiet Ib (proj₁ e₀) r c₀y in ⊥-elim (blk-np m (subst (enter (fc true) (T2.q₀ ⊕ [ ix 1 ]) y) eq r))) ]′
          (≼-or-≻ y c₀)

        -- The program's: up to its end, and past it in its instant.
        prog-in : ∀ {y e} → After (fc false) s′ y e → y ≺ E → y ∈ KS
        prog-in {y} (r , _) yE =
          [ (λ le → [ (λ lt → there (there (∈-++⁺ʳ (proj₁ rb) (∈-++⁺ˡ (proj₂ rc r lt))))) , (λ eq → there (here eq)) ]′ (≼-split {y} {c} le))
          , (λ cy → there (there (∈-++⁺ʳ (proj₁ rb) (∈-++⁺ʳ (proj₁ rc)
                      (h (proj₂ (rows-lift rn r)) (mid c c y E (≼-refl {c}) cy (≺→≼ {y} {E} yE) (sym (E2.end-inst ea)))))))) ]′
          (≼-or-≻ y c)

        module R = E2.Row E KS blk-in prog-in

    -- THE END'S INSTANT HOLDING FEW ROWS OF THE MERGE, ITS `laneDone`
    -- FALLS THERE.
    done-in : ∀ {s′} → Runs s′ → ∀ {c} → Prog s′ c end → (ks : List Pos) → (∀ {y e} → Mg y e → instant y ≡ instant c → y ∈ ks)
            → ¬ ¬ (Σ Pos λ f′ → Σ (IE B) λ v → Mg f′ (out v) × T (not (undone v)) × instant f′ ≡ instant c)
    done-in rn uc ks h k = share-ends rn uc ks h λ (e , se , ie) → share-done se λ (f′ , v , x , nk , if) → k (f′ , v , x , nk , trans if ie)

    -- A READER PAST THE PROGRAM'S END, BEFORE ANY CUT AND WITH FEW ROWS
    -- BEFORE IT, IS IN THE END'S INSTANT: were it later, the end's instant
    -- would hold few rows, so a cut before the reader.
    rows-late : ∀ {s′} → Runs s′ → ∀ {c} → Prog s′ c end → ∀ {w} → c ≺ w → Few Mg w → Unfailed undone Mg w → ¬ ¬ (instant w ≡ instant c)
    rows-late rn {c} uc {w} cw (ks , fw) unf k with instant w ≟ⁱ instant c
    ... | yes eq = k eq
    ... | no ne  = done-in rn uc ks (λ {y} x iy → fw x (before {y} iy)) λ (f′ , v , x , nk , if) → unf x nk (before {f′ ⊕ [ ix 0 ]} (ext f′ if))
      where
        before : ∀ {y} → instant y ≡ instant c → y ≺ w
        before {y} iy = instant-≺ y w (subst (_≺ⁱ instant w) (sym iy) (≺-instant c w cw λ e → ne (sym e)))
        ext : ∀ f′ → instant f′ ≡ instant c → instant (f′ ⊕ [ ix 0 ]) ≡ instant c
        ext (_ ∙ _) e = e

    -- THE MERGE IS IDLE UP TO ITS `laneDone`.
    merged-idle : IdleTo undone Mg
    merged-idle =
      let (s′ , rn) = prog-runs
          (es′ , oks′ , fs′) = runs-at rn
      in Thin.idle undone Mg (Prog s′) (inv-ev m (elab ρ₄ (f a)) env′ g′ s′ oks′) (Held.idle (held a Lt s′ oks′ fs′ es′))
           (rows-vis rn) (rows-lift rn) (rows-shown rn) (rows-late rn)

  -- A `laneDone` moves no route.
  silent : ∀ {y : IE B} → T (not (undone y)) → ∀ r → count r y ≡ r
  silent nk r with undone-done nk
  ... | done = refl

  -- A LANE IS IDLE at an admissible, fresh, early subscription.
  idle-at : ∀ a s → Ok (Hots env₂) s → Fr s → Early s → Idle (enter (fL a) s)
  idle-at a s ok fs es = subst (λ d → Idle (enter d s)) (sym (ev-take m undone (merged a) env₂)) TI.idle
    where
      module TI = TakeIdle true undone (ev m (merged a) env₂) s (inv-ev m (merged a) env₂ g₂ s ok) (Rows.merged-idle a s ok fs es) silent

  -- A LANE'S ROWS ARE ITS VALUE'S PAST ONE ADMISSIBLE, FRESH, EARLY
  -- SUBSCRIPTION, and those are all the lane's.
  lane-sub : ∀ op′ p → Ok (Hots env₂) p → Fr p → Early p → ∀ {q a k e} → enter dR p q (out a) → View.Lane fL (enter dR p) op′ q a k e
           → Σ Pos λ s → Ok (Hots env₂) s × Fr s × Early s
             × (∀ {c e′} → View.Lane fL (enter dR p) op′ q a c e′ → enter (fL a) s c e′)
             × (∀ {c e′} → enter (fL a) s c e′ → View.Lane fL (enter dR p) op′ q a c e′)
  lane-sub (mergeᶠ nothing) p ok fp ep {q} {a} xo _ =
    _ , oks , Adm.step ad (ok-o p ok xo) (proj₂ (proj₂ (vals p ok fp ep)) xo tt) plain-ix , early-inst [ ix 1 ] (proj₁ (vals p ok fp ep) xo)
      , proj₁ , λ r → r , world-after (InvAt.world (Il a _ oks) r) (InvAt.real (Il a _ oks) r)
    where oks = ok-step q (ok-o p ok xo)
  lane-sub switchᶠ p ok fp ep {q} {a} xo _ =
    _ , oks , Adm.step ad (ok-o p ok xo) (proj₂ (proj₂ (vals p ok fp ep)) xo tt) plain-ix , early-inst [ ix 1 ] (proj₁ (vals p ok fp ep) xo)
      , proj₁ , λ r → r , world-after (InvAt.world (Il a _ oks) r) (InvAt.real (Il a _ oks) r)
    where oks = ok-step q (ok-o p ok xo)
  lane-sub exhaustᶠ p ok fp ep {q} {a} xo _ =
    _ , oks , Adm.step ad (ok-o p ok xo) (proj₂ (proj₂ (vals p ok fp ep)) xo tt) plain-ix , early-inst [ ix 1 ] (proj₁ (vals p ok fp ep) xo)
      , proj₁ , λ r → r , world-after (InvAt.world (Il a _ oks) r) (InvAt.real (Il a _ oks) r)
    where oks = ok-step q (ok-o p ok xo)
  lane-sub (mergeᶠ (just n)) p ok fp ep {q} {a} xo (i , s , sb , _ , _) =
    let (es , oks , fs) = FlatFit.Bd.start-at fL dR ad Id Il laneE p ok (proj₁ V) (proj₁ (proj₂ V)) (proj₂ (proj₂ V)) n i (proj₁ sb) (proj₂ sb)
    in s , oks , fs , es , fwd , λ r → i , s , sb , r , world-after (InvAt.world (Il a s oks) r) (InvAt.real (Il a s oks) r)
    where
      V = vals p ok fp ep
      fwd : ∀ {c e′} → View.Lane fL (enter dR p) (mergeᶠ (just n)) q a c e′ → enter (fL a) s c e′
      fwd (_ , _ , sb′ , r′ , _) with BoundedI.sub-same ok n fL Il (Id p ok) sb sb′
      ... | refl = r′

  -- A LANE IS IDLE ON ITS OWN.
  lane-idle : ∀ op′ p → Ok (Hots env₂) p → Fr p → Early p → ∀ {q a} → enter dR p q (out a) → Idle (View.Lane fL (enter dR p) op′ q a)
  lane-idle op′ p ok fp ep xo {[]} _ _ _ _ _ = inj₁ refl
  lane-idle op′ p ok fp ep xo {_ ∷ _} mt@((((r , _) , _) , _) ∷ _) =
    let (s , oks , fs , es , to , from) = lane-sub op′ p ok fp ep xo r
    in Same.idle to from (idle-at _ s oks fs es) mt
