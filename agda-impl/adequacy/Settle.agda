{-# OPTIONS --guardedness #-}

-- A JOINER SETTLES: an end reaching a joiner shows the joiner's own end
-- where its meaning is done (`JDone`), every part it runs ended, and is
-- absorbed otherwise.  The engine reads done off its live count and its
-- queue: none running and none waiting.
module adequacy.Settle where

open import Data.Bool using (Bool; T; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Nat using (zero; suc)
open import Data.List using (List; []; _∷_; [_]; _++_; null)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Properties using (ʳ++-defn)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; ix; Timeline)
open import denotation.EmissionSet using (EmissionSet; Den; Work; Ended; Reach; _≺_; _≼_; out; end; ⟦_⟧; module Merge; module Bounded; module Switch; module Exhaust)
open import denotation.Laws.Modulus using (≺-irrefl; ≼-refl; ≺→≼; ≼-trans; ≼-antisym)
open import denotation.Laws.Worlds using (InvAt; PinBy; ⊑-inside; W; step; inW; plain-ix; nest-in; Hots) renaming (⊑-refl to ⊑ʷ-refl)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; Scope; ⟨_,_,_,_⟩; scopeOf; rise; moved; rising; absorbed; flatS; cp; nx; inOuter; inLanes; settle)
open import adequacy.Rows using (full; ≃-refl; silent; _≃_)
open _≃_ using (to; from)
open import adequacy.Cursor using (Pol; Kill; kill-out; takes; bef; aft; Owes; Sound; JInv; Joined; joined; Begun; more; JoinE; JRl; Behind; Sync; s-flat;
                                   polF; JoinF; Lane; Runs; Start; JRo; voc; h-live; l-live; Whole; OuterDone; Ahead; Waiting; Slots; Ends; Asc; Unkilled; Unended; NoKill; alike; slots-mv)
open import adequacy.Cursor.Frame using (owes; Fr; f-outer; d-outer; f-lanes; d-lanes)
open import adequacy.Cursor.Rise using (SimC; settled; flying; adrift)
open import adequacy.Cursor.Tear using (c-abs)
open import adequacy.Enter using (module Lanes)
open import adequacy.Walk using (dead-closed; begun-join)
open import adequacy.Regions using (lane-sole)
open import denotation.Laws.BoundedInv using (module BoundedI)
open import adequacy.Up using (module Past; VHot; vhot-hots; begun-out; NoRow; nr-≈; nr-tr; fr-up; After; asc-pre; asc-post)
open import adequacy.Bound using (JDone; join-row-d)
open import adequacy.Admit using (before; begun-nq; dead-ends; live-of)

------------------------------------------------------------------------
-- DONE, by operator: built from the outer's end and every lane running,
-- uncut, ended; read for a lane no later value has cut.

done-mk : ∀ op {A B} {F : A → Den B} {O : EmissionSet A} {c} → Ended O c
        → (∀ {q a} → O q (out a) → Runs (polF op F O) q → q ≺ c → (∀ {q′} → Kill (polF op F O) q q′ → q′ ≺ c → ⊥) → Ended (Lane (polF op F O) q a) c)
        → JDone op F O c
done-mk (mergeᶠ nothing)  ov g = ov , λ x r qc _ → g x r qc λ ()
done-mk (mergeᶠ (just m)) ov g = ov , λ x r qc _ → g x r qc λ ()
done-mk switchᶠ           ov g = ov , λ x r qc nc → g x r qc λ { {q′} (a′ , x′ , qq′) q′c → nc (q′ , a′ , x′ , qq′ , q′c) }
done-mk exhaustᶠ          ov g = ov , λ x r qc _ → g x r qc λ ()

done-use : ∀ op {A B} {F : A → Den B} {O : EmissionSet A} {c} → JDone op F O c
         → ∀ {q a} → O q (out a) → Runs (polF op F O) q → q ≺ c → (∀ {q′} → Kill (polF op F O) q q′ → c ≼ q′) → Ended (Lane (polF op F O) q a) c
done-use (mergeᶠ nothing)  (_ , g) x r qc _  = g x r qc λ ()
done-use (mergeᶠ (just m)) (_ , g) x r qc _  = g x r qc λ ()
done-use switchᶠ           (_ , g) x r qc nk = g x r qc λ (q′ , a′ , x′ , qq′ , q′c) → nk (a′ , x′ , qq′) q′c
done-use exhaustᶠ          (_ , g) x r qc _  = g x r qc λ ()

oend-row : ∀ op {A B} {F : A → Den B} {O : EmissionSet A} {c} → O c end → JDone op F O c → JoinF op F O c end
oend-row (mergeᶠ nothing)  {F = F} {O} x dn = Merge.oend {f = F} {o = O} x dn
oend-row (mergeᶠ (just m)) {F = F} {O} x dn = Bounded.oend {n = m} {f = F} {o = O} x dn
oend-row switchᶠ           {F = F} {O} x dn = Switch.oend {f = F} {o = O} x dn
oend-row exhaustᶠ          {F = F} {O} x dn = Exhaust.oend {f = F} {o = O} x dn

-- A begun lane's value runs.
begun-ru : ∀ {Γ} {sc : Scope Γ} {Rl C A B} {P : Pol A B} {O : EmissionSet A} {vs ls n q a}
         → Begun sc Rl C P O vs ls n → (q , a) ∈ vs → Runs P q
begun-ru (more _ _ r _ _) (here refl) = r
begun-ru (more _ _ _ _ bg) (there i) = begun-ru bg i

∉[] : ∀ {X : Set} {x : X} {xs} → xs ≡ [] → x ∈ xs → ⊥
∉[] refl ()

-- A LANE RUNNING, at `p`, unended: not done there.
live-undone : ∀ op {Γ} {sc : Scope Γ} {Rl p A B} {F : A → Den B} {O : EmissionSet A} {vs ls n}
            → Begun sc Rl (bef p) (polF op F O) O vs ls n → ¬ n ≡ 0
            → (∀ {q a} → (q , a) ∈ vs → Lane (polF op F O) q a p end → ⊥) → ¬ JDone op F O p
live-undone op {p = p} bg nz nl dn with live-of bg nz
... | q , a , i , uk , ue with done-use op dn (begun-out bg i) (begun-ru bg i) (before p {q} (begun-nq bg i)) (λ kq → uk kq)
...   | c₀ , lc , c₀p with ≼-antisym {c₀} {p} c₀p (ue lc (λ {q′} kq → ≼-trans {c₀} {p} {q′} c₀p (uk kq)))
...     | refl = nl i lc

-- A VALUE WAITING for a slot: its lane starts past an owed end, so it
-- has not ended, and the joiner is not done.
wait-undone : ∀ op {Γ} {sc : Scope Γ} {Rl p A B} {F : A → Den B} {O : EmissionSet A} {vs ls ws qu q a}
            → Begun sc Rl (bef p) (polF op F O) O vs ls 0 → Waiting (bef p) (polF op F O) O vs ws qu
            → Ahead (bef p) (polF op F O) vs ws → Ends (polF op F O) O → (q , a) ∈ ws → ¬ JDone op F O p
wait-undone (mergeᶠ nothing) _ wt _ _ iw _ = ∉[] (proj₁ (proj₂ (proj₂ (proj₂ wt))) tt) iw
wait-undone switchᶠ          _ wt _ _ iw _ = ∉[] (proj₁ (proj₂ (proj₂ (proj₂ wt))) tt) iw
wait-undone exhaustᶠ         _ wt _ _ iw _ = ∉[] (proj₁ (proj₂ (proj₂ (proj₂ wt))) tt) iw
wait-undone (mergeᶠ (just m)) {p = p} {q = q} bg wt ah en iw dn with proj₁ (proj₂ (proj₂ wt)) iw
... | y , nq , r , _ with done-use (mergeᶠ (just m)) dn y r (before p {q} nq) (λ ())
...   | _ , (i , s , sub , _) , _ with ah iw (i , sub)
...     | _ , _ , c , iv , lc′ , _ , oc , _ with dead-ends bg refl iv
...       | inj₁ (c′ , lc″ , nc′) = nc′ (≼-trans {p} {c} {c′} oc (en (begun-out bg iv) lc″ lc′ tt))
...       | inj₂ (_ , () , _)

-- A lane's row, uncut, as its joiner's.
jlane : ∀ op {A B} {F : A → Den B} {O q a k e} → O q (out a) → Runs (polF op F O) q → Lane (polF op F O) q a k e
      → (∀ {q′} → Kill (polF op F O) q q′ → q′ ≺ k → ⊥) → Work e → JoinF op F O k e
jlane (mergeᶠ nothing) {F = F} {O} x rn l nk w = Merge.lane {f = F} {o = O} x rn l (λ ()) w
jlane (mergeᶠ (just m)) {F = F} {O} x rn l nk w = Bounded.lane {n = m} {f = F} {o = O} x rn l (λ ()) w
jlane switchᶠ {F = F} {O} x rn l nk w = Switch.lane {f = F} {o = O} x rn l (λ { (_ , a′ , x′ , lt , lt′) → nk (a′ , x′ , lt) lt′ }) w
jlane exhaustᶠ {F = F} {O} x rn l nk w = Exhaust.lane {f = F} {o = O} x rn l (λ ()) w

-- A lane's start, and so its every row, lies in its joiner's world.
start-w : ∀ {Γ A B} {sc : Scope Γ} {f : A → Obs Timeline Γ B} {O : EmissionSet A} (ji : JInv sc f O) op {q a s}
        → O q (out a) → Start (polF op (λ a → ⟦ f a ⟧ (full sc)) O) q a s → W (Hots (full sc)) (JInv.at ji) s
start-w ji (mergeᶠ nothing)  x refl = step (inW (InvAt.world (JInv.io ji) x)) plain-ix
start-w {sc = sc} {f} ji (mergeᶠ (just m)) _ (_ , sb) = BoundedI.s-w (JInv.ok ji) m (λ a → ⟦ f a ⟧ (full sc)) (JInv.fi ji) (JInv.io ji) sb
start-w ji switchᶠ           x refl = step (inW (InvAt.world (JInv.io ji) x)) plain-ix
start-w ji exhaustᶠ          x refl = step (inW (InvAt.world (JInv.io ji) x)) plain-ix

lane-w : ∀ {Γ A B} {sc : Scope Γ} {f : A → Obs Timeline Γ B} {O : EmissionSet A} (ji : JInv sc f O) op {q a k e}
       → O q (out a) → Lane (polF op (λ a → ⟦ f a ⟧ (full sc)) O) q a k e → W (Hots (full sc)) (JInv.at ji) k
lane-w {sc = sc} {f} ji op x l with Lanes.lane-row sc f ji op x l
... | _ , st , w , _ = nest-in (start-w ji op x st) w

module _ {R : Set} (Rt : EmissionSet R) where

  ----------------------------------------------------------------------
  -- AN OUTER'S END at `p`.  Already ended, it cannot end again: past an
  -- end only pins follow.  Else the joiner's outer is over; with no lane
  -- running and none waiting every lane begun ended before `p`, and the
  -- joiner's end flies; otherwise its meaning is not done at `p`, nothing
  -- shows there, and the frames above move past it.
  rise-outer-cp : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {ω} {d n q ls} {c : Ctx R Γ B} {o p k′ sh t}
                → rise (inOuter op f ω d n q ls c) o cp p ≡ moved k′ sh t → SimC Rt ⟨ inOuter op f ω d n q ls c , o , rising cp , p ⟩ sh k′
  rise-outer-cp {d = true} {p = p} refl (flying (f-outer _ ji (joined _ _ _ od _ _ _ _ _) _ _ _) _ (_ , row)) =
    let (c₀ , y , nc) = proj₁ od tt in ⊥-elim (end-pin (InvAt.quiet (JInv.io ji) y row (before p {c₀} nc)))
    where
      end-pin : ∀ {X : Set} {c₀} → PinBy {X} c₀ end → ⊥
      end-pin (_ , () , _)
  rise-outer-cp {op = op} {f = f} {ω = ω} {d = false} {c = c} {o = o} {p = p} refl {Cr = Cr}
    (flying (f-outer {Rg = Rg} {E = E} {E′ = E′} fr ji (joined bg wt wh od ah ao en li sl) jm so bh) cl (sy , row)) = go bg wt wh ah ao sl
    where
      sc = scopeOf c
      F = λ a → ⟦ f a ⟧ (full sc)
      P = polF op F E
      io = JInv.io ji
      open Past p using (owes-up; dn; behind-up; begun-up; module Book)
      open Book {P = P} {O = E} using (ahead-up; wait-up)

      out-end : ∀ {b} → out b ≡ end → ⊥
      out-end ()

      -- the outer's row at `p` is in what no lane's region holds
      here-o = Sound.rg so row tt
      nl : ∀ {q′} → ¬ JRl sc Rg op f E q′ p
      nl r = proj₂ here-o (proj₂ r)
      rl = Lanes.lane-rows sc f ji op li
      nh : ¬ VHot (full sc) p
      nh = λ hv → proj₂ (JInv.ok ji) (vhot-hots (full sc) hv) (InvAt.world io row) (⊑-inside (⊑ʷ-refl p))

      -- no value of the outer at `p`
      nv : ∀ {k b} → E k (out b) → Owes (bef p) k → Owes (aft p) k
      nv y o = owes-up (λ { refl → out-end (InvAt.func io y row) }) o

      le : ∀ {vs ls n q a c′} → Begun sc (JRl sc Rg op f E) (bef p) P E vs ls n → (q , a) ∈ vs → Lane P q a c′ end → p ≡ c′ → ⊥
      le bg iv lc refl = nl (rl (begun-out bg iv) lc)

      -- the joiner's bookkeeping past `p`, its outer over
      book : ∀ {n qu ls vs ws} → Begun sc (JRl sc Rg op f E) (bef p) P E vs ls n → Waiting (bef p) P E vs ws qu → Whole (bef p) P E vs ws
           → Ahead (bef p) P vs ws → Asc vs → Slots P (bef p) vs ws n
           → Sync sc Rg (aft p) (flatS op f ω true n qu o ls) E′
      book bg wt wh ah ao sl =
        s-flat ji sy (joined (begun-up (λ k o → nv (proj₁ (proj₂ (kill-out op k))) o) (λ _ → nl) nh bg)
                             (wait-up (le bg) (ahead-up (le bg) ah) wt) (λ y nq r → wh y (λ o → nq (nv y o)) r)
                             ((λ _ → p , row , ≺-irrefl {p}) , (λ _ _ → tt)) (ahead-up (le bg) ah) ao en li
                             (slots-mv op (λ {y} → dn {y}) nv sl))
               jm so (behind-up bh)

      absorb : ∀ {n qu ls vs ws} → ¬ JDone op F E p → Begun sc (JRl sc Rg op f E) (bef p) P E vs ls n → Waiting (bef p) P E vs ws qu
             → Whole (bef p) P E vs ws → Ahead (bef p) P vs ws → Asc vs → Slots P (bef p) vs ws n
             → After Rt Cr ⟨ c , flatS op f ω true n qu o ls , absorbed , p ⟩
      absorb nd bg wt wh ah ao sl = proj₁ lifted , aft p , settled c-abs (proj₁ (proj₂ lifted)) (book bg wt wh ah ao sl) , proj₂ (proj₂ lifted)
        where
          nr : NoRow (JoinF op F E) p
          nr r v with join-row-d op F E r v
          ... | inj₁ (_ , dn′)                  = nd dn′
          ... | inj₂ (_ , _ , y , _ , ln , _) = nl (rl y ln)
          lifted = fr-up Rt fr tt (proj₁ here-o) (nr-≈ (proj₂ jm) (nr-tr nr)) nh

      go : ∀ {n qu ls vs ws} → Begun sc (JRl sc Rg op f E) (bef p) P E vs ls n → Waiting (bef p) P E vs ws qu
         → Whole (bef p) P E vs ws → Ahead (bef p) P vs ws → Asc vs → Slots P (bef p) vs ws n
         → After Rt Cr ⟨ c , flatS op f ω true n qu o ls , settle true n (null qu) , p ⟩
      go {suc k} bg wt wh ah ao sl = absorb (live-undone op bg (λ ()) (λ i lc → le bg i lc refl)) bg wt wh ah ao sl
      go {zero} {_ ∷ _} {ws = []}    _ (() , _) _ _ _ _
      go {zero} {_ ∷ _} {ws = _ ∷ _} bg wt wh ah ao sl = absorb (wait-undone op bg wt ah en (here refl)) bg wt wh ah ao sl
      go {zero} {[]}    {ws = _ ∷ _} _ (() , _) _ _ _ _
      go {zero} {[]}    {ws = []}    bg wt wh ah ao sl = Cr , bef p , flying fr cl (book bg wt wh ah ao sl , shown) , silent ≃-refl
        where
          -- every lane begun ended before `p`
          g : ∀ {q a} → E q (out a) → Runs P q → q ≺ p → (∀ {q′} → Kill P q q′ → q′ ≺ p → ⊥) → Ended (Lane P q a) p
          g y r qp nk with wh y (λ pq → pq qp) (takes P r)
          ... | inj₂ ()
          ... | inj₁ iv with dead-ends bg refl iv
          ...   | inj₁ (c′ , lc , nc) = c′ , lc , ≺→≼ {c′} {p} (before p {c′} nc)
          ...   | inj₂ (q′ , kq , nq) = ⊥-elim (nk kq (before p {q′} nq))
          done : JDone op F E p
          done = done-mk op (p , row , ≼-refl {p}) g
          shown = proj₁ (to (alike (proj₂ jm)) ((oend-row op row done , proj₁ bh , λ tk kp _ → proj₂ bh tk (λ pk → pk kp)) , tt))
  rise-outer-cp _ (flying (d-outer _ _ _ _) _ ())
  rise-outer-cp _ (adrift fr cl _) = ⊥-elim (subst T cl (dead-closed Rt fr refl))
  rise-outer-cp _ (settled () _ _)

  ----------------------------------------------------------------------
  -- A LANE'S VALUE at `p`: the lane runs, so its row is the joiner's.
  -- Nothing else of the joiner is at `p`: not its outer, whose region
  -- holds no lane's, nor another lane, whose region is its own; so the
  -- joiner's bookkeeping moves past it.
  rise-lane-nx : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {ω} {d n q o pre post} {c : Ctx R Γ B} {s b p k′ sh t}
               → rise (inLanes op f ω d n q o pre post c) s (nx b) p ≡ moved k′ sh t
               → SimC Rt ⟨ inLanes op f ω d n q o pre post c , s , rising (nx b) , p ⟩ sh k′
  rise-lane-nx {op = op} {f = f} {pre = pre} {c = c} {p = p} eq {Cr = Cr}
    (flying (f-lanes {Rg = Rg} {E = E} {O = O} {vs₁ = vs₁} {vs₂ = vs₂} {q = q₀} {a = a₀} {b = true}
              fr ji sy lf y₀ nq ru (h-live st le uk ue) rt cnt wt wh od ah ao en li jm so sd bh _ sl) cl (_ , _ , refl , _ , sy′ , row)) with eq
  ... | refl = Cr , bef p , flying fr cl (s-flat ji (up sy so no nh) (joined bg′ (wait-up le-all ah′ wt) (whole-up oo wh) (od-up oo od) ah′ ao en li sl′) jm so (behind-up bh) , shown) , silent ≃-refl
    where
      sc = scopeOf c
      F = λ a → ⟦ f a ⟧ (full sc)
      P = polF op F O
      open Past p using (up; begun-up; nm; owes-up; off-rg; in-off; behind-up; kill-up; module Book)
      open Book {P = P} {O = O}

      out-end : ∀ {v} → out v ≡ end → ⊥
      out-end ()

      ly = voc le row
      hr : JRl sc Rg op f O q₀ p
      hr = Lanes.lane-rows sc f ji op li y₀ ly
      rl = Lanes.lane-rows sc f ji op li
      -- the outer's region holds no lane's row
      no : ¬ JRo sc Rg op f O p
      no r = proj₂ r (proj₂ hr)
      oo = off-rg so no
      ku = kill-up op oo
      nh : ¬ VHot (full sc) p
      nh hv = proj₂ (JInv.ok ji) (vhot-hots (full sc) hv) (lane-w ji op y₀ ly) (⊑-inside (⊑ʷ-refl p))

      sole : ∀ {q q′} → JRl sc Rg op f O q p → JRl sc Rg op f O q′ p → q ≡ q′
      sole r r′ = lane-sole (JInv.ok ji) F (JInv.fi ji) (JInv.io ji) op (proj₂ r) (proj₂ r′)
      nb₁ : ∀ {q a} → (q , a) ∈ vs₁ → ¬ JRl sc Rg op f O q p
      nb₁ i r = ≺-irrefl {q₀} (subst (λ x → x ≺ q₀) (sole r hr) (asc-pre vs₁ ao i))
      nb₂ : ∀ {q a} → (q , a) ∈ vs₂ → ¬ JRl sc Rg op f O q p
      nb₂ i r = ≺-irrefl {q₀} (subst (λ x → q₀ ≺ x) (sole r hr) (asc-post vs₁ ao i))
      val : ∀ {q a} → (q , a) ∈ vs₁ ++ (q₀ , a₀) ∷ vs₂ → O q (out a)
      val i with ∈-++⁻ vs₁ i
      ... | inj₁ i′          = begun-out lf i′
      ... | inj₂ (here refl) = y₀
      ... | inj₂ (there i′)  = begun-out rt i′

      -- the lane's row at `p` is a value: it ends elsewhere
      endne : ∀ {c′} → Lane P q₀ a₀ c′ end → p ≡ c′ → ⊥
      endne lc refl = out-end (Sound.fn (sd tt) row (proj₁ (from (alike le) (lc , tt))) tt tt)
      le-all : ∀ {q a c′} → (q , a) ∈ vs₁ ++ (q₀ , a₀) ∷ vs₂ → Lane P q a c′ end → p ≡ c′ → ⊥
      le-all i lc refl with sole (rl (val i) lc) hr
      ... | refl with Sound.fn so (val i) y₀ tt tt
      ...   | refl = endne lc refl
      ah′ = ahead-up le-all ah

      hole = l-live (h-live st le (λ k → ku k (uk k)) (λ lc nk → owes-up (endne lc) (ue lc nk))) sy′ (sd tt)
      bg′ = subst (Begun _ _ _ _ _ _ _) (sym cnt)
              (subst (λ ls → Begun _ _ _ _ _ _ ls _) (sym (ʳ++-defn pre)) (begun-join (begun-up ku nb₁ nh lf) y₀ (nm nq) ru hole (begun-up ku nb₂ nh rt)))
      sl′ = slots-mv op (λ {y} t → ≺→≼ {p} {y} t) (λ x o → in-off oo x tt o) sl
      shown = proj₁ (to (alike (proj₂ jm)) ((jlane op y₀ ru ly (λ k lt → uk k lt) tt , proj₁ bh , λ tk kp _ → proj₂ bh tk (λ pk → pk kp)) , tt))
  rise-lane-nx _ (flying (f-lanes {b = false} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (_ , _ , _ , () , _))
  rise-lane-nx _ (flying (d-lanes _ _ _ _ _ _ _) _ ())
  rise-lane-nx _ (adrift fr cl _) = ⊥-elim (subst T cl (dead-closed Rt fr refl))
  rise-lane-nx _ (settled () _ _)
