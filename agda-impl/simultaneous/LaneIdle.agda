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
open import Data.Sum using (_⊎_; inj₁; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_; yes; no)
open import simultaneous.Instants using (_≺ⁱ_; ≺-instant; instant-≺)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; of; flatMap; takeWhile)
open import denotation.Position using (Pos; root; _≟ᵖ_; _≟ⁱ_; ix; instant; _⊕_)
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
open import simultaneous.HeldHot using (module HotRead)
open import simultaneous.HeldBase using (shows-ev)
open import simultaneous.ElabUndone using (Undone)
open import simultaneous.CombSent using (assoc³)
open import simultaneous.HeldTrigger using (≺-part)
open import simultaneous.Layers using (pinby-vis)
open import denotation.Read using (Visible)
open import denotation.Laws.Worlds using (full; notT)
open import denotation.Laws.Truth using (instant-⊕)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-≼-≺; ≺-trans; entered-few)
open import denotation.Position using (sub)
open import denotation.EmissionSet using (shown; ended; late; _≼_; skip)

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
                (placed : ∀ a {t} → Lawful t → PlacedD (Hots (hot t ∷ hot t₂ ∷ hot t₁ ∷ env₀)) Fr (ev m (elab ρ₄ (f a)) (hot t ∷ hot t₂ ∷ hot t₁ ∷ env₀)))
                (pu : ∀ a {t} → Undone (ev m (elab ρ₄ (f a)) (hot t ∷ hot t₂ ∷ hot t₁ ∷ env₀))) where

  open LaneReal m op f ρ₄ t₂ t₁ env₀ g₂ L₁ tv te tp ad (λ a L p ok fp ep → held-fit (held a L p ok fp ep) (placed a L p ok fp ep)) using (env₂; x; srcE; laneE)
  open LaneOnce m op f ρ₄ t₂ t₁ env₀ g₂ L₁ tv te tp ad cs held placed using (dR; fL; Id; Il; ok-o; vals; module Share)

  -- A lane's two parts, merged, ahead of its take.
  merged : A → Obs Timeline (IE B ∷ IE A ∷ Θ) (IE B)
  merged a = flatMap (mergeᶠ nothing) (λ k → shareˢ (x a k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ []))

  -- THE MERGE'S ROWS ARE ITS PROGRAM'S, where the lane part's share runs
  -- it past its blocker, framed by marks that move no route.
  module Rows (a : A) (s : Pos) (ok : Ok (Hots env₂) s) (fs : Fr s) (es : Early s) where
    open Share a s ok fs es using (P; tS; Lt; tee; env′; g′; Q; okQ; fQ; eQ; fc; dQ; ad′)

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

    -- The share's rows.
    Ish : InvAt (Hots env′) Q Sh
    Ish = inv-ev m (flatMap (mergeᶠ (just 1)) (x a lanePart) (of (true ∷ false ∷ []))) env′ g′ Q okQ

    -- THE FRAME READS THE SHARE at its second piece's subscription, from
    -- before every row of the share: each row moved under its own `sub z`.
    Bd z : Pos
    Bd = (P ⊕ [ ix 0 ]) ⊕ [ ix 0 ]
    z = (Bd ⊕ [ ix 1 ]) ⊕ [ ix 1 ]

    z≺Q : z ≺ Q
    z≺Q = subst (_≺ Q) (sym (assoc³ (P ⊕ [ ix 0 ]) (ix 0) (ix 1) (ix 1))) (≺-part (P ⊕ [ ix 0 ]) (ix 1 ∷ ix 1 ∷ []) [] refl)

    sh-aft : ∀ {y e} → Sh y e → Q ≺ y
    sh-aft y = world-after (InvAt.world Ish y) (InvAt.real Ish y)

    sh-few : ∀ {y e} → Sh y e → Visible e → Few Sh y
    sh-few {q} {out v} y _ = entered-few (ev m (flatMap (mergeᶠ (just 1)) (x a lanePart) (of (true ∷ false ∷ []))) env′) Q (λ {k} {e′} → full {IE B} {q} {out v} tt {k} {e′}) y
    sh-few {q} {end}   y _ = entered-few (ev m (flatMap (mergeᶠ (just 1)) (x a lanePart) (of (true ∷ false ∷ []))) env′) Q (λ {k} {e′} → full {IE B} {q} {end} tt {k} {e′}) y
    sh-few {e = skip}  _ ()
    sh-few {e = pin _} _ ()

    sh-proper : ∀ {c y e} → Sh c end → Sh y e → Visible e → y ≼ c
    sh-proper sc sy v cy with InvAt.quiet Ish sc sy cy
    ... | _ , refl , _ = v

    module HR = HotRead Sh z (InvAt.flat Ish) (InvAt.func Ish) (λ {y} y′ → ≺-trans {z} {Q} {y} z≺Q (sh-aft y′)) sh-few sh-proper
                  (shows-ev m (flatMap (mergeᶠ (just 1)) (x a lanePart) (of (true ∷ false ∷ []))) env′ g′ Q okQ)

    postulate
      -- The blocker ends, so the program runs.
      prog-runs : Σ Pos Runs

      -- A value of the share is the program's,
      sh-vis : ∀ {s′} → Runs s′ → ∀ {q v} → Sh q (out v) → Prog s′ q (out v)

      -- each row of the program lies at a row of the share,
      sh-lift : ∀ {s′} → Runs s′ → ∀ {q e} → Prog s′ q e → Σ (Ev (IE B)) (Sh q)

      -- its values shown as they are.
      sh-shown : ∀ {s′} → Runs s′ → ∀ {q v} → Prog s′ q (out v) → Sh q (out v)

      -- A value of the merge is the frame's reading of the share's, or a
      -- frame mark at a place the reading holds nothing.
      rows-vis : ∀ {q v} → Mg q (out v) → HR.Rd q (out v) ⊎ ((∀ r → count r v ≡ r) × (∀ {e′} → HR.Rd q e′ → ⊥))

      -- Each row of the reading lies at a row of the merge,
      rows-lift : ∀ {q e} → HR.Rd q e → Σ (Ev (IE B)) (Mg q)

      -- its values shown as they are.
      rows-shown : ∀ {q v} → HR.Rd q (out v) → Mg q (out v)

    -- THE SHARE'S END RUNS THE `laneDone`, IN ITS INSTANT.
    share-done : ∀ {e} → Sh e end → ¬ ¬ (Σ Pos λ f′ → Σ (IE B) λ v → Mg f′ (out v) × T (not (undone v)) × instant f′ ≡ instant e)
    share-done se = done-row ρ₄ (f a) env₂ m s (inv-ev m (flatMap (mergeᶠ (just 1)) (x a lanePart) (of (true ∷ false ∷ []))) env′ g′ Q okQ) se

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
    share-ends : ∀ {s′} → Runs s′ → ∀ {c} → Prog s′ c end → (ks : List Pos) → (∀ {y e} → Sh y e → instant y ≡ instant c → y ∈ ks)
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
                      (h (proj₂ (sh-lift rn r)) (mid c c y E (≼-refl {c}) cy (≺→≼ {y} {E} yE) (sym (E2.end-inst ea)))))))) ]′
          (≼-or-≻ y c)

        module R = E2.Row E KS blk-in prog-in

    -- PAST THE PROGRAM'S END, SHORT OF THE SHARE'S, A READER WITH FEW ROWS
    -- BEFORE IT IS IN THE END'S INSTANT: were it later, the share's rows of
    -- that instant would be few, so the share would end there, before it.
    sh-late : ∀ {s′} → Runs s′ → ∀ {c} → Prog s′ c end → ∀ {w} → c ≺ w → Few Sh w → Unfailed undone Sh w
            → (∀ {c′} → Sh c′ end → w ≼ c′) → ¬ ¬ (instant w ≡ instant c)
    sh-late rn {c} uc {w} cw (ks , fw) _ wE k with instant w ≟ⁱ instant c
    ... | yes eq = k eq
    ... | no ne  = share-ends rn uc ks (λ {y} x iy → fw x (before {y} iy)) λ (E , se , ie) → k (mid c c w E (≼-refl {c}) cw (wE se) (sym ie))
      where
        before : ∀ {y} → instant y ≡ instant c → y ≺ w
        before {y} iy = instant-≺ y w (subst (_≺ⁱ instant w) (sym iy) (≺-instant c w cw λ e → ne (sym e)))

    -- The share's values end no lane.
    sh-unf : ∀ {s′} → Runs s′ → ∀ {w} → Unfailed undone Sh w
    sh-unf {s′} rn x nk _ = notT _ nk (pu a s′ (sh-vis rn x))

    -- THE SHARE IS IDLE, where its program runs.
    sh-idle : Idle Sh
    sh-idle mt ne fw aw lw =
      let (s′ , rn) = prog-runs
          (es′ , oks′ , fs′) = runs-at rn
          Ip = inv-ev m (elab ρ₄ (f a)) env′ g′ s′ oks′
      in Thin.idle undone Sh (Prog s′) Ish (λ uc uy v cy → pinby-vis v (InvAt.quiet Ip uc uy cy)) (Held.idle (held a Lt s′ oks′ fs′ es′))
           (λ x → inj₁ (sh-vis rn x)) (sh-lift rn) (sh-shown rn) (sh-late rn) mt ne (sh-unf rn) fw aw lw

    -- The reading's end is the share's, moved.
    rd-end : ∀ {c} → HR.Rd c end → Σ Pos λ E → Sh E end × instant c ≡ instant E
    rd-end (shown _ b _ , _)    = ⊥-elim (HR.bare-end b refl)
    rd-end (ended {c} tc _ , _) = c , proj₁ tc , instant-⊕ c [ sub z ]
    rd-end (late {c} tc cz , _) = ⊥-elim (≺-irrefl {z} (≺-≼-≺ {z} {c} {z} (≺-trans {z} {Q} {c} z≺Q (sh-aft (proj₁ tc))) cz))

    -- A READER PAST THE READING'S END, BEFORE ANY CUT, IS IN THE END'S
    -- INSTANT: the share's end runs the `laneDone` there.
    rows-late : ∀ {c} → HR.Rd c end → ∀ {w} → c ≺ w → Few Mg w → Unfailed undone Mg w → (∀ {c′} → Mg c′ end → w ≼ c′)
              → ¬ ¬ (instant w ≡ instant c)
    rows-late {c} rc {w} cw _ unf _ k with rd-end rc | instant w ≟ⁱ instant c
    ... | _ | yes eq = k eq
    ... | E , se , ic | no ne = share-done se λ (f′ , v , x , nk , if) →
      unf x nk (before {f′ ⊕ [ ix 0 ]} (trans (instant-⊕ f′ [ ix 0 ]) (trans if (sym ic))))
      where
        before : ∀ {y} → instant y ≡ instant c → y ≺ w
        before {y} iy = instant-≺ y w (subst (_≺ⁱ instant w) (sym iy) (≺-instant c w cw λ e → ne (sym e)))

    -- THE MERGE IS IDLE UP TO ITS `laneDone`.
    merged-idle : IdleTo undone Mg
    merged-idle = Thin.idle undone Mg HR.Rd (inv-ev m (merged a) env₂ g₂ s ok) (λ rc ry _ → HR.rd-proper ry rc)
                    (HR.idle-hot sh-idle) (rows-vis) (rows-lift) (rows-shown) rows-late

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
