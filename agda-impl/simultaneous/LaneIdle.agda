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
open import Data.List.Properties using (∷ʳ-injective; ++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there; any?)
open import Relation.Nullary.Decidable using (decidable-stable)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Relation.Nullary using (¬_; yes; no)
open import simultaneous.Instants using (_≺ⁱ_; ≺-instant; instant-≺)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; of; flatMap; takeWhile)
open import denotation.Position using (Pos; root; _≟ᵖ_; _≟ⁱ_; ix; instant; _⊕_)
open import denotation.Events using (Timeline; fresh; inside-self)
open import denotation.EmissionSet using (EmissionSet; Den; Ev; DenEnv; hot; enter; out; end; pin; Few; _≺_; _≼_; After; shown; module Op; module Bounded; module Merge; Ended)
open import denotation.Laws.Modulus using (≼-or-≻; ≼-split; ≼-refl; ≺→≼; ≼-antisym)
open import denotation.Laws.Worlds.Leaves using (ine-pin)
open import denotation.Read using ([]; _∷_; Run)
open import denotation.Laws.Worlds using (Ok; InvAt; InvD; Lawful; Hots; GoodEnv; ok-step; plain-ix; world-after; ⊕-identityʳ; ⊕-assoc)
open import denotation.Laws.BoundedInv using (module BoundedI)
open import simultaneous.SObs using (lone; lanePart; burstPart; module Elaborate)
open import simultaneous.InstEmit using (instEmit; value; mark; laneDone; burstEnd)
open import simultaneous.Relations using (Met)
open import simultaneous.Routed using (Held; Early; Idle; HeldD; Placed; PlacedD; Adm; Sync; Ex; Carried; c-end; cnt; nameOf)
open import simultaneous.Counts using (idle-row; Counts; module Alike; counts-held; counts-at; module TakeCounts)
open import simultaneous.HeldTake using (name-ext; sync-ext; ex-ext)
open import simultaneous.HeldDefer using (sync-up)
open import simultaneous.RealView using (lane-at)
open import simultaneous.HeldComb using (ev)
open import simultaneous.HeldConnect using (early-inst)
open import simultaneous.HeldTake using (module TakeIdle; module TakeBack)
open import simultaneous.HeldTo using (IdleTo; Unfailed)
open import simultaneous.LaneLocal using (inv-ev; EndsEarly; held-fit; module FlatFit; module LaneReal; undone-done; done; of-outer)
open import simultaneous.LaneOnce using (module LaneOnce)
open import simultaneous.RealView using (module View)
open import simultaneous.IdleThin using (module Thin)
open import simultaneous.ConcatTwo using (module Two; starts₀)
open import simultaneous.EnterFew using (enter-few)
open import simultaneous.ColdIdle using (mid)
open import simultaneous.LaneDoneRow using (done-row)
open import simultaneous.LaneVis using (lane-vis; lane-ld; hot-lab; sh-u)
open import simultaneous.LaneUp using (module Lift)
open import simultaneous.LaneSite using (between-under)
open import simultaneous.LaneLayers using (under-⊕; under-refl)
open import denotation.Up using (up; up-⊕)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import simultaneous.HeldHot using (module HotRead; em)
open import simultaneous.HeldBase using (shows-ev)
open import simultaneous.ElabUndone using (Undone; tell-back; tell-undone)
open import simultaneous.CombSent using (assoc³)
open import simultaneous.HeldTrigger using (≺-part; Blocked; blk; module Spots; module Cat₀; module Cat)
open import simultaneous.Layers using (pinby-vis; run-row; run-tail; run-++; last-met)
open import simultaneous.Project using (run-prefix)
open import simultaneous.LiveRuns using (pre-noend)
open import denotation.Read using (Visible; cursor)
import denotation.Read as Rd
import simultaneous.Layers as Layers
open import simultaneous.Relabel using (RowsAt; cntAt)
open import simultaneous.Shut using (r₀)
open import denotation.Position using (Label)
open import denotation.Laws.Worlds using (full; notT; _⊑_; inside-⊑)
open import simultaneous.LaneChain using (module Chains)
import simultaneous.LaneBurst as LaneBurst
open import denotation.Laws.Truth using (instant-⊕; past)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-≼-≺; ≺-trans; entered-few; ≺-ext)
open import denotation.Position using (sub; last)
open import denotation.EmissionSet using (shown; ended; late; _≼_; skip; Dep)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; laneˢ; undone; counted; framed; shareˢ; count; laneStep)

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

flat-to : ∀ m {Γ X Y} op (g : X → Obs Timeline Γ Y) (o : Obs Timeline Γ X) (ρ : DenEnv Γ) p {y e}
        → enter (ev m (flatMap op g o) ρ) p y e → enter (Op.flatMap op (λ c → ev m (g c) ρ) (ev m o ρ)) p y e
flat-to nothing  op g o ρ p r = r
flat-to (just _) op g o ρ p r = r

-- A flatMap over an `of`, read as the meaning's or an approximant's, is
-- the operator's over the `of`.
flat-of-to : ∀ m {Γ X Y} op (g : X → Obs Timeline Γ Y) (xs : List X) (ρ : DenEnv Γ) p {y e}
           → enter (ev m (flatMap op g (of xs)) ρ) p y e → enter (Op.flatMap op (λ c → ev m (g c) ρ) (Op.of xs)) p y e
flat-of-to nothing  op g xs ρ p r = r
flat-of-to (just _) op g xs ρ p r = r

flat-of-from : ∀ m {Γ X Y} op (g : X → Obs Timeline Γ Y) (xs : List X) (ρ : DenEnv Γ) p {y e}
             → enter (Op.flatMap op (λ c → ev m (g c) ρ) (Op.of xs)) p y e → enter (ev m (flatMap op g (of xs)) ρ) p y e
flat-of-from nothing  op g xs ρ p r = r
flat-of-from (just _) op g xs ρ p r = r

-- A bounded merge's lane over an `of` is the same lane read either way.
sub-of-to : ∀ m {Γ X Y} n (G : X → Den Y) (xs : List X) (ρ : DenEnv Γ) p {i q s a}
          → Bounded.Sub n G (enter (ev m (of xs) ρ) p) i q s a → Bounded.Sub n G (enter (Op.of xs) p) i q s a
sub-of-to nothing  n G xs ρ p r = r
sub-of-to (just _) n G xs ρ p r = r

sub-of-from : ∀ m {Γ X Y} n (G : X → Den Y) (xs : List X) (ρ : DenEnv Γ) p {i q s a}
            → Bounded.Sub n G (enter (Op.of xs) p) i q s a → Bounded.Sub n G (enter (ev m (of xs) ρ) p) i q s a
sub-of-from nothing  n G xs ρ p r = r
sub-of-from (just _) n G xs ρ p r = r

-- An `each` of nothing over a hot pins nothing: the hot's pins are heard
-- as skips, and its lanes are empty `of`s.
hot-each-nopin : ∀ {X Y} (t : EmissionSet X) s {k r} → enter (Op.flatMap (mergeᶠ nothing) (λ _ → Op.of {Y} []) (hot t)) s k (pin r) → ⊥
hot-each-nopin t s (Merge.opin (shown _ () _ , _) , _)
hot-each-nopin t s (Merge.left _ _ ((l , _) , _) _ _ , _) = ine-pin l
hot-each-nopin t s (Merge.run () _ , _)

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

    open Lift ρ₄ (f a) env₂ using (up-val; up-skip)

    -- The read's rows lie past its subscription, past the frame's.
    rd-z : ∀ {y e} → HR.Rd y e → z ≺ y
    rd-z = HR.rd-past {z} (λ {y} y′ → ≺-trans {z} {Q} {y} z≺Q (sh-aft y′))

    Bz : Bd ≺ z
    Bz = ≺-trans {Bd} {Bd ⊕ [ ix 1 ]} {z} (≺-ext Bd []) (≺-ext (Bd ⊕ [ ix 1 ]) [])

    -- THE SHARE HAS FEW ROWS BEFORE A ROW OF THE READ WAITING ON ALL BEFORE
    -- IT: those before its source row are proper, so read before it, and
    -- none lies under it.
    sh-few-rd : ∀ {y e} → HR.Rd y e → (∀ {k e′} → Dep y e k e′) → Few Sh y
    sh-few-rd (rj , ks , c) d with HR.rj-σ rj
    ... | k₀ , refl , _ , (sk₀ , pk₀) = k₀ ∷ L.map up ks , pick
      where
        pick : ∀ {j e′} → Sh j e′ → j ≺ HR.shift k₀ → j ∈ (k₀ ∷ L.map up ks)
        pick {j} sj jy with ≼-split {j} {k₀} (λ k₀j → let (ys , eq) = between-under (under-⊕ (under-refl k₀) (sub z)) k₀j jy in HR.apart sk₀ sj k₀j ys eq)
        ... | inj₂ refl = here refl
        ... | inj₁ jk₀  = there (subst (_∈ L.map up ks) (up-⊕ j (sub z))
                                  (∈-map⁺ up (c (proj₂ (HR.rj (sj , λ {c′} sc cj → pk₀ sc (≺-trans {c′} {j} {k₀} cj jk₀)))) (HR.down sj sk₀ jk₀) d)))

    -- A VALUE OF THE READING IS THE MERGE'S, classically: the frame's scan
    -- shows it once it has folded the frame's values before it, and tells
    -- it as it is, ending no lane.
    rows-shown : ∀ {q v} → HR.Rd q (out v) → ¬ ¬ Mg q (out v)
    rows-shown {q} {v} r k =
      up-val m s HR.rd-proper HR.rd-few r (rd-z r) (sh-few-rd r (λ {_} {_} → tt)) (≺-trans {Bd} {z} {q} Bz (rd-z r))
        λ (b , x′) → k (subst (λ c → Mg q (out c)) (told b) x′)
      where
        uv : T (undone v)
        uv = sh-u ρ₄ (f a) env₂ m (λ {t} → pu a {t}) (proj₁ (proj₂ (proj₂ (HR.src-vis (proj₁ r) tt))))

        told : ∀ (b : _ × IE B) → proj₂ (laneStep b v) ≡ v
        told b = sym (tell-back (proj₁ b) v refl (subst T (sym (tell-undone (proj₁ b) v)) uv))

    -- A skip of the reading is the merge's.
    rows-skip : ∀ {q} → HR.Rd q skip → Mg q skip
    rows-skip {q} r = up-skip m s HR.rd-proper HR.rd-few r (rd-z r) (sh-few-rd r (λ {_} {_} → tt)) (≺-trans {Bd} {z} {q} Bz (rd-z r))

    -- THE SHARE IS A CONCAT of its blocker, which ends where the empty
    -- source does, then the program, subscribed past that end.
    module SP = Spots P

    Bk : Blocked (fc true) SP.sb SP.cb
    Bk = blk m env₂ (P ⊕ [ ix 1 ]) SP.sb SP.sb≺e₀

    module C0 = Cat₀ fc Q SP.cb Bk SP.sb≺cb SP.q₁≺cb

    -- The blocker ends, so the program runs.
    prog-runs : Σ Pos Runs
    prog-runs = C0.s₁ , 1 , Q ⊕ [ ix 1 ] , sub-of-from m 1 fc (true ∷ false ∷ []) env′ Q C0.sub₁

    runs-s₁ : ∀ {s′} → Runs s′ → s′ ≡ C0.s₁
    runs-s₁ (_ , _ , sb) = C0.sub-s₁ (sub-of-to m 1 fc (true ∷ false ∷ []) env′ Q sb)

    I₁ : InvAt (Hots env′) C0.s₁ (Prog C0.s₁)
    I₁ = inv-ev m (elab ρ₄ (f a)) env′ g′ C0.s₁ (proj₁ (proj₂ (runs-at (proj₂ prog-runs))))

    module CC = Cat fc Q SP.cb Bk SP.sb≺cb SP.q₁≺cb SP.e₁≺cb
                  (λ y → world-after (InvAt.world I₁ y) (InvAt.real I₁ y)) (λ y → proj₂ (InvAt.pinned I₁ y))

    to-s₁ : ∀ {s′} → Runs s′ → ∀ {q e} → Prog s′ q e → Prog C0.s₁ q e
    to-s₁ rn {q} {e} r = subst (λ c → Prog c q e) (runs-s₁ rn) r

    -- A value of the share is the program's,
    sh-vis : ∀ {s′} → Runs s′ → ∀ {q v} → Sh q (out v) → Prog s′ q (out v)
    sh-vis rn {q} {v} r = subst (λ c → Prog c q (out v)) (sym (runs-s₁ rn))
                            (CC.row (flat-of-to m (mergeᶠ (just 1)) (x a lanePart) (true ∷ false ∷ []) env′ Q r))

    -- each row of the program lies at a row of the share,
    sh-lift : ∀ {s′} → Runs s′ → ∀ {q e} → Prog s′ q e → Σ (Ev (IE B)) (Sh q)
    sh-lift rn r = _ , flat-of-from m (mergeᶠ (just 1)) (x a lanePart) (true ∷ false ∷ []) env′ Q (CC.lift (to-s₁ rn r))

    -- its values shown as they are.
    sh-shown : ∀ {s′} → Runs s′ → ∀ {q v} → Prog s′ q (out v) → Sh q (out v)
    sh-shown rn r = flat-of-from m (mergeᶠ (just 1)) (x a lanePart) (true ∷ false ∷ []) env′ Q (CC.lift (to-s₁ rn r))

    -- EACH ROW OF THE READING BUT ITS END LIES AT A ROW OF THE MERGE.  The
    -- end, the frame's connected piece's, hands the frame to its queued
    -- `laneDone`, a skip just past it.
    rows-lift : ∀ {q e} → HR.Rd q e → ¬ ¬ (Σ (Ev (IE B)) (Mg q) ⊎ e ≡ end)
    rows-lift {e = out _} r k = rows-shown r λ y → k (inj₁ (_ , y))
    rows-lift {e = skip}  r k = k (inj₁ (skip , rows-skip r))
    rows-lift {e = end}   _ k = k (inj₂ refl)
    rows-lift {e = pin _} (shown _ () _ , _)

    -- A VALUE OF THE MERGE IS THE FRAME'S READING OF THE SHARE'S, or a
    -- frame mark at a place the reading holds nothing.
    rows-vis : ∀ {q v} → Mg q (out v) → HR.Rd q (out v) ⊎ ((∀ r → count r v ≡ r) × (∀ {e′} → HR.Rd q e′ → ⊥))
    rows-vis r with lane-vis ρ₄ (f a) env₂ m (λ {t} → pu a {t}) s r
    ... | inj₁ h          = inj₁ h
    ... | inj₂ (ly , sv) = inj₂ (proj₁ sv , λ rd → hot-lab rd ly)

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

    -- THE SHARE IS ITS PROGRAM'S ROWS, the blocker's dropped, where the
    -- program runs.
    module ST (s′ : Pos) (rn : Runs s′) where
      Ip : InvAt (Hots env′) s′ (Prog s′)
      Ip = inv-ev m (elab ρ₄ (f a)) env′ g′ s′ (proj₁ (proj₂ (runs-at rn)))

      Hp : Held (Prog s′) (s′ ∷ cs)
      Hp = held a Lt s′ (proj₁ (proj₂ (runs-at rn))) (proj₂ (proj₂ (runs-at rn))) (proj₁ (runs-at rn))

      open Thin undone Sh (Prog s′) Ish (λ uc uy v cy → pinby-vis v (InvAt.quiet Ip uc uy cy)) (Held.idle Hp)
             (λ x → inj₁ (sh-vis rn x)) (λ fw k → k (proj₁ fw , λ x lt → proj₂ fw (proj₂ (sh-lift rn x)) lt))
             (λ { {e = out _} x _ → enter-few (ev m (elab ρ₄ (f a)) env′) s′ x tt ; {e = end} x _ → enter-few (ev m (elab ρ₄ (f a)) env′) s′ x tt })
             (λ x k → k (sh-shown rn x)) (sh-late rn) public

    -- THE SHARE IS IDLE, where its program runs.
    sh-idle : Idle Sh
    sh-idle mt ne fw aw lw = ST.idle (proj₁ prog-runs) (proj₂ prog-runs) mt ne (sh-unf (proj₂ prog-runs)) fw aw lw

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

    -- FEW ROWS OF THE MERGE BEFORE A PLACE, FEW OF THE READING: its end
    -- the one row more.
    rows-few : ∀ {w} → Few Mg w → ¬ ¬ Few HR.Rd w
    rows-few {w} (ks , h) k = em {Σ Pos λ c → HR.Rd c end} λ
      { (inj₁ (c , rc)) → k (c ∷ ks , λ {y′} x lt → decidable-stable (any? (y′ ≟ᵖ_) (c ∷ ks)) λ ni → rows-lift x λ
          { (inj₁ (_ , y)) → ni (there (h y lt)) ; (inj₂ refl) → ni (here (≼-antisym {y′} {c} (HR.rd-proper x rc) (HR.rd-proper rc x))) })
      ; (inj₂ ne) → k (ks , λ {y′} x lt → decidable-stable (any? (y′ ≟ᵖ_) ks) λ ni → rows-lift x λ
          { (inj₁ (_ , y)) → ni (h y lt) ; (inj₂ refl) → ne (_ , x) }) }

    -- THE MERGE IS IDLE UP TO ITS `laneDone`.
    merged-idle : IdleTo undone Mg
    merged-idle = Thin.idle undone Mg HR.Rd (inv-ev m (merged a) env₂ g₂ s ok) (λ rc ry _ → HR.rd-proper ry rc)
                    (HR.idle-hot sh-idle) (rows-vis) (rows-few) (λ x _ → HR.rd-few x) (rows-shown) rows-late

    -- A carried value of the merge is the reading's: the frame's marks
    -- are carried by nothing.
    rows-carried : ∀ {q v} → Mg q (out v) → Carried (out v) → HR.Rd q (out v)
    rows-carried r c with lane-vis ρ₄ (f a) env₂ m (λ {t} → pu a {t}) s r
    ... | inj₁ h       = h
    ... | inj₂ (_ , sv) = ⊥-elim (proj₂ sv c)

    -- THE PROGRAM'S BURST LIES IN THE LANE'S, read where the frame reads it.
    sync-s₁ : ∀ {y} → Sync C0.s₁ y → Sync s y
    sync-s₁ {y} sy =
      sync-up {s} {y} [ ix 0 ] (sync-up {s ⊕ [ ix 0 ]} {y} [ ix 1 ] (sync-up {P} {y} [ ix 1 ] (sync-up {P ⊕ [ ix 1 ]} {y} [ last ]
        (sync-up {(P ⊕ [ ix 1 ]) ⊕ [ last ]} {y} [ sub SP.sb ] (sync-up {SP.cb} {y} [ ix 1 ] sy)))))

    ex-move : ∀ {y} → Ex (C0.s₁ ∷ cs) y → Sync s (HR.shift y) ⊎ Ex cs (HR.shift y)
    ex-move {y} (here sy)  = inj₁ (sync-ext {s} {y} [ sub z ] (sync-s₁ sy))
    ex-move {y} (there ex) = inj₂ (ex-ext {cs} {y} [ sub z ] ex)

    -- THE MERGE COUNTS WHAT ITS PROGRAM COUNTS, exempt for the lane's burst.
    mg-counts : Counts Mg (λ y → Sync s y ⊎ Ex cs y)
    mg-counts =
      Thin.counts undone Mg HR.Rd (inv-ev m (merged a) env₂ g₂ s ok) (λ rc ry _ → HR.rd-proper ry rc)
        (HR.idle-hot sh-idle) rows-vis rows-few (λ x _ → HR.rd-few x) rows-shown rows-late rows-carried
        (counts-at HR.Sh (λ { {y = y} refl → name-ext y [ sub z ] }) (λ { refl ex → ex-move ex }) HR.back
          (ST.counts C0.s₁ (proj₂ prog-runs) (λ x _ → sh-vis (proj₂ prog-runs) x) (counts-held (ST.Hp C0.s₁ (proj₂ prog-runs)))))

    ----------------------------------------------------------------
    -- THE `laneDone`'S COUNT IS THE PROGRAM'S AT ITS END.  A run met up
    -- to the `laneDone` is the merge's up to its frame row, which lies
    -- under the share's end; thinned, it is the frame's reading of the
    -- share, so the share's run, which meets its end next; thinned again,
    -- the program's run, which meets the program's end next.

    module TB = TakeBack true undone (ev m (merged a) env₂) s (inv-ev m (merged a) env₂ g₂ s ok)

    snoc-cut : ∀ r₁ {rs₀ y f e a′} → r₁ ++ [ (y , e) ] ≡ rs₀ ++ [ (f ⊕ [ ix 0 ] , out a′) ] → Met Mg (rs₀ ++ [ (f , out a′) ])
             → Met Mg (r₁ ++ [ (f , e) ]) × y ≡ f ⊕ [ ix 0 ]
    snoc-cut r₁ {rs₀} eq r with ∷ʳ-injective r₁ rs₀ eq
    ... | refl , refl = r , refl

    snoc-end : ∀ (r₁ rs : List (Pos × Ev (IE B))) {y q : Pos} {v : IE B} → r₁ ++ [ (y , out v) ] ≡ rs ++ [ (q , end) ] → ⊥
    snoc-end r₁ rs eq with ∷ʳ-injective r₁ rs eq
    ... | _ , ()

    -- The take's `laneDone` is its source's failing row, or under it.
    take-ld : ∀ r₁ {y kd n} → Met (enter (fL a) s) (r₁ ++ [ (y , out (instEmit (mark (laneDone kd)) n)) ])
            → Σ Pos λ v₂ → Met Mg (r₁ ++ [ (v₂ , out (instEmit (mark (laneDone kd)) n)) ]) × Σ (List Label) λ zs → y ≡ v₂ ⊕ zs
    take-ld r₁ {y} {kd} {n} mt = go (TB.back TB.c-none (subst (λ d → Met (enter d s) rows) (ev-take m undone (merged a) env₂) mt))
      where
        rows : List (Pos × Ev (IE B))
        rows = r₁ ++ [ (y , out (instEmit (mark (laneDone kd)) n)) ]
        go : TB.Back nothing rows → Σ Pos λ v₂ → Met Mg (r₁ ++ [ (v₂ , out (instEmit (mark (laneDone kd)) n)) ]) × Σ (List Label) λ zs → y ≡ v₂ ⊕ zs
        go (inj₁ (rn , _)) = y , rn , [] , sym (⊕-identityʳ y)
        go (inj₂ (TB.cut {rs₀} {f = f} sp r _ _ _ (TB.tl-v _) _)) =
          f , proj₁ (snoc-cut r₁ sp r) , [ ix 0 ] , proj₂ (snoc-cut r₁ sp r)
        go (inj₂ (TB.cut {rs₀} {f = f} {a′} sp _ _ _ _ (TB.tl-ve _) _)) =
          ⊥-elim (snoc-end r₁ (rs₀ ++ [ (f ⊕ [ ix 0 ] , out a′) ]) (trans sp (sym (++-assoc rs₀ [ (f ⊕ [ ix 0 ] , out a′) ] [ (f ⊕ [ last ] , end) ]))))
        go (inj₂ (TB.cut {rs₀} sp _ _ _ _ TB.tl-e _)) = ⊥-elim (snoc-end r₁ rs₀ sp)

    -- The merge's `laneDone` lies under the frame's reading of the share's end.
    ld-past : ∀ {v₂ kd n} → Mg v₂ (out (instEmit (mark (laneDone kd)) n))
            → ¬ ¬ (Σ Pos λ E → Sh E end × Σ Label λ l → Σ (List Label) λ zs → v₂ ≡ HR.shift E ⊕ (l ∷ zs))
    ld-past r κ with lane-ld ρ₄ (f a) env₂ m (λ {t} → pu a {t}) s r tt
    ... | E , se , eq = κ (E , se , ix 1 , [ ix 0 ] , trans eq (⊕-assoc (HR.shift E) [ ix 1 ] [ ix 0 ]))

    pv : ∀ {c y e} → Prog C0.s₁ c end → Prog C0.s₁ y e → Visible e → y ≼ c
    pv uc uy v cy = pinby-vis v (InvAt.quiet I₁ uc uy cy)

    -- The share subscribes in the lane's burst.
    sQ : Sync s Q
    sQ = sync-up {s} {Q} [ ix 0 ] (sync-up {s ⊕ [ ix 0 ]} {Q} [ ix 1 ] (sync-up {P} {Q} [ ix 0 ]
           (sync-up {P ⊕ [ ix 0 ]} {Q} [ ix 1 ] (subst T (sym (inside-self Q)) tt , refl))))

    module BQ = Bounded 1 fc (enter dQ Q)

    end-done : ∀ {E} → BQ.JoinT E end → BQ.Done E
    end-done (BQ.oend _ d)         = d
    end-done (BQ.lend _ _ _ _ _ d) = d
    end-done (BQ.rend () _ _)

    -- THE SHARE ENDS AT ITS PROGRAM'S END, OR AT ITS OUTER'S, in the
    -- subscribing burst: never at its blocker's, which the program starts
    -- past.
    sh-prog-end : ∀ {E} → Sh E end → Σ Pos λ c → Prog C0.s₁ c end × c ≼ E × (E ≡ c ⊎ Sync s E)
    sh-prog-end {E} se = c , pc , cE , at jt cE
      where
        jt : BQ.JoinT E end
        jt = proj₁ (flat-to m (mergeᶠ (just 1)) (x a lanePart) (of (true ∷ false ∷ [])) env′ Q se)

        over : ∀ {c′} → enter dQ Q c′ end → c′ ≼ E → T2.qL ≼ E
        over x′ le with T2.o-row x′
        ... | T2.rL = le

        Lp : Ended (BQ.Lane T2.q₁ false) E
        Lp = proj₂ (end-done jt) T2.ob₁ (1 , false , T2.nth₁)
               (≺-≼-≺ {T2.q₁} {T2.qL} {E} (past Q 1) (over (proj₁ (proj₂ (proj₁ (end-done jt)))) (proj₂ (proj₂ (proj₁ (end-done jt)))))) (λ ())

        c : Pos
        c = proj₁ Lp

        ln : BQ.Lane T2.q₁ false c end
        ln = proj₁ (proj₂ Lp)

        cE : c ≼ E
        cE = proj₂ (proj₂ Lp)

        s′ : Pos
        s′ = proj₁ (proj₂ ln)

        sb : BQ.Sub (proj₁ ln) T2.q₁ s′ false
        sb = proj₁ (proj₂ (proj₂ ln))

        pc : Prog C0.s₁ c end
        pc = to-s₁ (proj₁ ln , T2.q₁ , sb) (proj₁ (proj₂ (proj₂ (proj₂ ln))))

        St : BQ.Starts 1 T2.q₁ (BQ.Sched 1) s′
        St = T2.second (λ ()) refl sb

        blk-past : ∀ {i q s″ E′} → BQ.Sub i q s″ true → After (fc true) s″ E′ end → c ≼ E′ → ⊥
        blk-past {E′ = E′} (n , st) aft cE′ with T2.nth-c n
        ... | T2.n₀ with starts₀ st
        ...   | refl = ≺-irrefl {E′} (≺-≼-≺ {E′} {c} {E′}
                  (T2.End.c₀c₁ {E′} {c} {s′} aft (λ e′ → BoundedI.lane-end okQ 1 fc fi Io T2.sub₀ e′ aft) St (proj₂ (proj₂ (proj₂ ln)))) cE′)

        at : ∀ {E′} → BQ.JoinT E′ end → c ≼ E′ → E′ ≡ c ⊎ Sync s E′
        at (BQ.oend x′ _) _ with T2.o-row x′
        ... | T2.rL = inj₂ (sync-ext {s} {Q} [ last ] sQ)
        at {E′} (BQ.lend {a = false} _ _ (i , _ , sb′ , aft) _ _ _) cE′ =
          inj₁ (≼-antisym {E′} {c} (pv pc (to-s₁ (i , _ , sb′) (proj₁ aft)) tt) cE′)
        at (BQ.lend {a = true} _ _ (_ , _ , sb′ , aft) _ _ _) cE′ = ⊥-elim (blk-past sb′ aft cE′)
        at (BQ.rend () _ _)

    module MT = Thin undone Mg HR.Rd (inv-ev m (merged a) env₂ g₂ s ok) (λ rc ry _ → HR.rd-proper ry rc)
                  (HR.idle-hot sh-idle) rows-vis rows-few (λ x _ → HR.rd-few x) rows-shown rows-late
    module PT = ST C0.s₁ (proj₂ prog-runs)

    -- The program's rows lie at or before its end.

    -- A RUN OF THE MERGE MET UP TO A ROW PAST THE READING OF THE SHARE'S
    -- END COUNTS WHAT THE PROGRAM'S RUN UP TO ITS END DOES.
    count-at : ∀ r₁ {v₂ e₂ E} → Met Mg (r₁ ++ [ (v₂ , e₂) ]) → Sh E end → HR.shift E ≺ v₂
             → (∀ {c} → E ≡ c ⊎ Sync s E → ¬ Ex (C0.s₁ ∷ cs) c)
             → Σ ℕ λ k → proj₂ (cnt r₁) ≡ suc k
    count-at r₁ {v₂} {e₂} {E} mg se Ev₂ nxc = proj₁ H , trans (cong proj₂ (trans cnt₁ (trans cnt₂ cnt₃))) (cong proj₂ (proj₂ H))
      where
        mg₁ : Met Mg r₁
        mg₁ = run-prefix r₁ mg

        ne : ∀ {k} → (k , end) ∈ r₁ → ⊥
        ne = pre-noend r₁ mg

        lst₂ : ∀ {k e} → Mg k e → Visible e → Rd.After (cursor nothing r₁) k → v₂ ≼ k
        lst₂ = go (run-tail r₁ mg)
          where go : Run Mg (cursor nothing r₁) [ (v₂ , e₂) ] → ∀ {k e} → Mg k e → Visible e → Rd.After (cursor nothing r₁) k → v₂ ≼ k
                go ((_ , _ , _ , l) ∷ []) = l

        -- The merge's run, thinned: the frame's reading of the share.
        r₁′ : List (Pos × Ev (IE B))
        r₁′ = proj₁ (MT.thin mg₁ ne)

        th : MT.Thin r₁ r₁′
        th = proj₂ (MT.thin mg₁ ne)

        mr : Met HR.Rd r₁′
        mr = proj₁ (MT.run mg₁ th (λ x → x) (λ _ x → x))

        i1 : ∀ {k v} → HR.Rd k (out v) → Rd.After (cursor nothing r₁′) k → Rd.After (cursor nothing r₁) k
        i1 = proj₂ (proj₂ (MT.run mg₁ th (λ x → x) (λ _ x → x)))

        cnt₁ : cnt r₁ ≡ cnt r₁′
        cnt₁ = MT.fold th r₀

        -- The reading's run, moved back: the share's.
        rs₀ : List (Pos × Ev (IE B))
        rs₀ = proj₁ (HR.run-back HR.none mr)

        ms : Met Sh rs₀
        ms = proj₁ (proj₂ (HR.run-back HR.none mr))

        eqB : r₁′ ≡ L.map HR.shR rs₀
        eqB = proj₂ (proj₂ (HR.run-back HR.none mr))

        cnt₂ : cnt r₁′ ≡ cnt rs₀
        cnt₂ = cntAt (subst (λ z → RowsAt HR.Sh z rs₀) (sym eqB) (HR.rows-at ms))

        neS : ∀ {k} → (k , end) ∈ rs₀ → ⊥
        neS {k} i = ne (MT.ends th (subst ((HR.shift k , end) ∈_) (sym eqB) (∈-map⁺ HR.shR i)))

        curS : cursor nothing r₁′ ≡ HR.shiftM (cursor nothing rs₀)
        curS = trans (cong (cursor nothing) eqB) (HR.cursor-at (HR.rows-at ms) nothing)

        lastS : Layers.Last Sh (cursor nothing rs₀) rs₀
        lastS = last-met ms

        -- No row of the share between its run and its end.
        lstE : ∀ {k e} → Sh k e → Visible e → Rd.After (cursor nothing rs₀) k → E ≼ k
        lstE {e = end}   sk _ _ = sh-proper sk se tt
        lstE {k} {e = out v} sk _ ak kE =
          rows-shown (HR.lift-vis sk tt) λ mk → lst₂ mk tt (i1 (HR.lift-vis sk tt) aR)
            (≺-trans {HR.shift k} {HR.shift E} {v₂} (HR.down sk se kE) Ev₂)
          where
            aR : Rd.After (cursor nothing r₁′) (HR.shift k)
            aR = subst (λ c → Rd.After c (HR.shift k)) (sym curS) (HR.aft-fwd (HR.last-cur lastS) sk ak)
        lstE {e = skip}  _ () _
        lstE {e = pin _} _ () _

        aftE : ∀ c → Layers.Last Sh c rs₀ → Rd.After c E
        aftE nothing  _ = tt
        aftE (just q) (e , iq , sq , vq) = [ (λ lt → lt) , (λ eq → ⊥-elim (neS (subst (λ e′ → (q , e′) ∈ rs₀) (InvAt.func Ish sq (subst (λ z → Sh z end) (sym eq) se)) iq))) ]′
                                             (≼-split {q} {E} (sh-proper se sq vq))

        msE : Met Sh (rs₀ ++ [ (E , end) ])
        msE = run-++ ms ((((se , λ ce → sh-proper ce se tt) , sh-few se tt) , tt , aftE (cursor nothing rs₀) lastS , lstE) ∷ [])

        -- The share's run, thinned: the program's.
        rp : List (Pos × Ev (IE B))
        rp = proj₁ (PT.thin ms neS)

        thp : PT.Thin rs₀ rp
        thp = proj₂ (PT.thin ms neS)

        mp : Met (Prog C0.s₁) rp
        mp = proj₁ (PT.run ms thp (λ x → x) (λ _ x → x))

        ip1 : ∀ {k v} → Prog C0.s₁ k (out v) → Rd.After (cursor nothing rp) k → Rd.After (cursor nothing rs₀) k
        ip1 = proj₂ (proj₂ (PT.run ms thp (λ x → x) (λ _ x → x)))

        cnt₃ : cnt rs₀ ≡ cnt rp
        cnt₃ = PT.fold thp r₀

        c : Pos
        c = proj₁ (sh-prog-end se)

        pc : Prog C0.s₁ c end
        pc = proj₁ (proj₂ (sh-prog-end se))

        cE : c ≼ E
        cE = proj₁ (proj₂ (proj₂ (sh-prog-end se)))

        lstE′ : ∀ {k e} → Sh k e → Visible e → Rd.After (cursor nothing rs₀) k → E ≼ k
        lstE′ = go (run-tail rs₀ msE)
          where go : Run Sh (cursor nothing rs₀) [ (E , end) ] → ∀ {k e} → Sh k e → Visible e → Rd.After (cursor nothing rs₀) k → E ≼ k
                go ((_ , _ , _ , l) ∷ []) = l

        lstC : ∀ {k e} → Prog C0.s₁ k e → Visible e → Rd.After (cursor nothing rp) k → c ≼ k
        lstC {e = end}   pk _ _ = pv pk pc tt
        lstC {k} {e = out v} pk _ ak kc =
          lstE′ (sh-shown (proj₂ prog-runs) pk) tt (ip1 pk ak) (≺-≼-≺ {k} {c} {E} kc cE)
        lstC {e = skip}  _ () _
        lstC {e = pin _} _ () _

        aftC : ∀ q′ → Layers.Last (Prog C0.s₁) q′ rp → Rd.After q′ c
        aftC nothing  _ = tt
        aftC (just q) (e , iq , pq , vq) = [ (λ lt → lt) , (λ eq → ⊥-elim (neS (PT.ends thp (subst (λ e′ → (q , e′) ∈ rp) (InvAt.func I₁ pq (subst (λ z → Prog C0.s₁ z end) (sym eq) pc)) iq)))) ]′
                                             (≼-split {q} {c} (pv pc pq vq))

        mpE : Met (Prog C0.s₁) (rp ++ [ (c , end) ])
        mpE = run-++ mp ((((pc , λ ce → pv ce pc tt) , enter-few (ev m (elab ρ₄ (f a)) env′) C0.s₁ pc tt) , tt
                , aftC (cursor nothing rp) (last-met mp) , lstC) ∷ [])

        H : Σ ℕ λ k → cnt rp ≡ (nameOf c , suc k)
        H = Held.covered PT.Hp mpE rp [] refl c-end (nxc (proj₂ (proj₂ (proj₂ (sh-prog-end se)))))

    -- THE RUN MET UP TO A `laneDone` HOLDS A ROUTE, outside the lane's burst
    -- and every exemption.
    ld-count : ∀ r₁ {y kd n} → Met (enter (fL a) s) (r₁ ++ [ (y , out (instEmit (mark (laneDone kd)) n)) ]) → ¬ Sync s y → ¬ Ex cs y
             → ¬ ¬ (Σ ℕ λ k → proj₂ (cnt r₁) ≡ suc k)
    ld-count r₁ mt ns nx κ with take-ld r₁ mt
    ... | v₂ , mg , zs , refl =
      ld-past (proj₁ (run-row mg (∈-++⁺ʳ r₁ (here refl)))) λ { (E , se , l , zs′ , ev) →
        κ (count-at r₁ mg se (subst (HR.shift E ≺_) (sym ev) (≺-ext (HR.shift E) {l} zs′)) (nxc E l zs′ ev)) }
      where
        sy-up : ∀ {E} l zs′ zs → Sync s E → Sync s (((HR.shift E) ⊕ (l ∷ zs′)) ⊕ zs)
        sy-up {E} l zs′ zs sy = sync-ext {s} {(HR.shift E) ⊕ (l ∷ zs′)} zs (sync-ext {s} {HR.shift E} (l ∷ zs′) (sync-ext {s} {E} [ sub z ] sy))

        ex-up : ∀ {E} l zs′ zs → Ex cs E → Ex cs (((HR.shift E) ⊕ (l ∷ zs′)) ⊕ zs)
        ex-up {E} l zs′ zs ex = ex-ext {cs} {(HR.shift E) ⊕ (l ∷ zs′)} zs (ex-ext {cs} {HR.shift E} (l ∷ zs′) (ex-ext {cs} {E} [ sub z ] ex))

        nxc : ∀ E l zs′ → v₂ ≡ HR.shift E ⊕ (l ∷ zs′) → ∀ {c} → E ≡ c ⊎ Sync s E → ¬ Ex (C0.s₁ ∷ cs) c
        nxc E l zs′ ev (inj₂ sE)   _          = ns (subst (λ w → Sync s (w ⊕ zs)) (sym ev) (sy-up l zs′ zs sE))
        nxc E l zs′ ev (inj₁ refl) (here sy)  = ns (subst (λ w → Sync s (w ⊕ zs)) (sym ev) (sy-up l zs′ zs (sync-s₁ sy)))
        nxc E l zs′ ev (inj₁ refl) (there ex) = nx (subst (λ w → Ex cs (w ⊕ zs)) (sym ev) (ex-up l zs′ zs ex))

  -- No route carries a `laneDone`.
  done-free : ∀ {v : IE B} → T (not (undone v)) → Carried (out v) → ⊥
  done-free nk c with undone-done nk | c
  ... | done | ()

  -- A LANE COUNTS WHAT ITS PROGRAM COUNTS at an admissible, fresh, early
  -- subscription: its take cuts only at its `laneDone`.
  counts-sub : ∀ a s → Ok (Hots env₂) s → Fr s → Early s → Counts (enter (fL a) s) (λ y → Sync s y ⊎ Ex cs y)
  counts-sub a s ok fs es = subst (λ d → Counts (enter d s) (λ y → Sync s y ⊎ Ex cs y)) (sym (ev-take m undone (merged a) env₂))
    (TakeCounts.counts true undone (ev m (merged a) env₂) s (inv-ev m (merged a) env₂ g₂ s ok) done-free (Rows.mg-counts a s ok fs es))

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
    in Alike.idle to from (idle-at _ s oks fs es) mt

  -- A lane's subscription read off its row is the one its rows lie past.
  sub-is : ∀ op′ p (ok : Ok (Hots env₂) p) (fp : Fr p) (ep : Early p) {q a k e} (xo : enter dR p q (out a)) (l : View.Lane fL (enter dR p) op′ q a k e)
         → proj₁ (lane-sub op′ p ok fp ep xo l) ≡ proj₁ (lane-at op′ dR fL Id Il p ok xo l)
  sub-is (mergeᶠ nothing)  p ok fp ep xo l                 = refl
  sub-is switchᶠ           p ok fp ep xo l                 = refl
  sub-is exhaustᶠ          p ok fp ep xo l                 = refl
  sub-is (mergeᶠ (just n)) p ok fp ep xo (i , s , sb , _ , _) = refl

  -- A LANE'S `laneDone` HOLDS A ROUTE: the run met up to it holds one,
  -- and an idle run names the row's instant.
  done-sub : ∀ a s → Ok (Hots env₂) s → Fr s → Early s → ∀ r₁ {y kd n}
           → Met (enter (fL a) s) (r₁ ++ [ (y , out (instEmit (mark (laneDone kd)) n)) ]) → ¬ Sync s y → ¬ Ex cs y
           → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
  done-sub a s ok fs es r₁ {y} mt ns nx = proj₁ P , cong₂ _,_ name (proj₂ P)
    where
      stable : ∀ {j} → ¬ ¬ (Σ ℕ λ k → j ≡ suc k) → Σ ℕ λ k → j ≡ suc k
      stable {zero}  h = ⊥-elim (h λ { (_ , ()) })
      stable {suc j} _ = j , refl

      P : Σ ℕ λ k → proj₂ (cnt r₁) ≡ suc k
      P = stable (Rows.ld-count a s ok fs es r₁ mt ns nx)

      name : proj₁ (cnt r₁) ≡ nameOf y
      name = [ (λ z → ⊥-elim (zero≢suc (trans (sym z) (proj₂ P)))) , (λ eq → eq) ]′ (idle-row (idle-at a s ok fs es) r₁ mt)
        where zero≢suc : ∀ {j} → 0 ≡ suc j → ⊥
              zero≢suc ()

  lane-done : ∀ op′ p (ok : Ok (Hots env₂) p) → Fr p → Early p → ∀ {q a k e} (xo : enter dR p q (out a)) (l : View.Lane fL (enter dR p) op′ q a k e)
            → ∀ r₁ {y kd n} → Met (View.Lane fL (enter dR p) op′ q a) (r₁ ++ [ (y , out (instEmit (mark (laneDone kd)) n)) ])
            → ¬ Sync (proj₁ (lane-at op′ dR fL Id Il p ok xo l)) y → ¬ Ex cs y → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
  lane-done op′ p ok fp ep {q} {a} xo l r₁ mt ns nx =
    let (s , oks , fs , es , to , from) = lane-sub op′ p ok fp ep xo l
    in done-sub a s oks fs es r₁ (Alike.run to from mt) (subst (λ c → ¬ Sync c _) (sym (sub-is op′ p ok fp ep xo l)) ns) nx

  -- A LANE'S SUBSCRIPTION IS ADMISSIBLE.
  lane-fresh : ∀ op′ p (ok : Ok (Hots env₂) p) → Fr p → Early p → ∀ {q a k e} (xo : enter dR p q (out a)) (l : View.Lane fL (enter dR p) op′ q a k e)
             → Fr (proj₁ (lane-at op′ dR fL Id Il p ok xo l))
  lane-fresh op′ p ok fp ep xo l = subst Fr (sub-is op′ p ok fp ep xo l) (proj₁ (proj₂ (proj₂ (lane-sub op′ p ok fp ep xo l))))

  -- A LANE'S `burstEnd` CLOSES ITS SUBSCRIBE BURST: it lies by what the
  -- lane shows or ends with in its subscription's instant.
  lane-burst : ∀ op′ p (ok : Ok (Hots env₂) p) → Fr p → Early p → ∀ {q a y e yb n} (xo : enter dR p q (out a)) (l : View.Lane fL (enter dR p) op′ q a y e)
             → Visible e → Sync (proj₁ (lane-at op′ dR fL Id Il p ok xo l)) y
             → View.Lane fL (enter dR p) op′ q a yb (out (instEmit (mark burstEnd) n)) → y ≼ yb
  lane-burst op′ p ok fp ep {q} {a} {y} xo l v sy lb =
    let (s , oks , fs , es , to , from) = lane-sub op′ p ok fp ep xo l
        eq = sub-is op′ p ok fp ep xo l
    in LaneBurst.lane-burst (λ i → ρ₄ i) (f a) env₂ g₂ m s oks (Share.share-mark a s oks fs es (λ ()))
         (λ hh le → Chains.sub-cold dR fL Id Il p ok op′ xo l hh (subst (_⊑ _) eq le))
         (to l) v (subst (_⊑ y) (sym eq) (inside-⊑ _ _ (proj₁ sy))) (to lb)

  -- A LANE COUNTS WHAT ITS PROGRAM COUNTS, exempt for its own burst.
  lane-counts : ∀ op′ p (ok : Ok (Hots env₂) p) → Fr p → Early p → ∀ {q a k e} (xo : enter dR p q (out a)) (l : View.Lane fL (enter dR p) op′ q a k e)
              → Counts (View.Lane fL (enter dR p) op′ q a) (λ y → Sync (proj₁ (lane-at op′ dR fL Id Il p ok xo l)) y ⊎ Ex cs y)
  lane-counts op′ p ok fp ep {q} {a} xo l =
    let (s , oks , fs , es , to , from) = lane-sub op′ p ok fp ep xo l
    in subst (λ c → Counts (View.Lane fL (enter dR p) op′ q a) (λ y → Sync c y ⊎ Ex cs y)) (sub-is op′ p ok fp ep xo l)
         (Alike.counts to from (counts-sub a s oks fs es))
