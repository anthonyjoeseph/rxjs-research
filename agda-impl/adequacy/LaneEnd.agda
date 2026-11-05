{-# OPTIONS --guardedness #-}

-- A LANE'S END at `p`: the lane runs, so its end is the joiner's row
-- there, and the lane is listed ended, its husk what it still runs.  A
-- slot freed goes to the queue's head, which starts at `p ⊕ [ ix 1 ]`:
-- `p` is the first owed end of a begun lane.  With none waiting, the
-- joiner's end flies where its outer is over and no lane runs, and is
-- absorbed otherwise.
module adequacy.LaneEnd where

open import Data.Bool using (T; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _≤_)
open import Data.Nat.Properties using (+-suc; +-comm; ≤-trans; ≤-reflexive; pred[n]≤n)
open import Data.List using (List; []; _∷_; [_]; _++_; _ʳ++_; reverse; length; map)
open import Data.List.Properties using (ʳ++-defn; reverse-involutive; ++-assoc; length-++; ∷ʳ-injectiveˡ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (tabulate) renaming (_∷_ to _∷ᴬ_; [] to []ᴬ)
open import Data.List.Relation.Unary.AllPairs using () renaming (_∷_ to _∷ᴾ_; [] to []ᴾ)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (++⁺ to pairs-++⁺)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; ix; Timeline)
open import denotation.EmissionSet using (EmissionSet; Den; Ended; Work; LaneOf; _≺_; _≼_; out; end; ⟦_⟧; module Joining; module Merge; module Bounded; module Switch; module Exhaust; module Values)
open import denotation.Laws.Modulus using (≺-ext; ≺-irrefl; ≺-trans; ≺-absurd; ≼-refl; ≺→≼; ≼-trans; ≼-or-≻)
open import denotation.Laws.Nth using (module Nths)
open import denotation.Laws.BoundedInv using (module BoundedI)
open import denotation.Laws.Worlds using (⊑-inside; Hots) renaming (⊑-refl to ⊑ʷ-refl)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; St; ⟨_,_,_,_⟩; scopeOf; closed; rise; moved; start; dequeue; rising; absorbed; flatS; cp; inLanes; lnS; cutS; settle)
open import adequacy.Rows using (full; pendRows; ≃-refl; silent; _≃_; Moves; ≼-≢)
open _≃_ using (to; from)
open import adequacy.Cursor using (Cur; Pol; Kill; kill-out; takes; bef; aft; Owes; Sound; JInv; joined; Begun; none; JoinE; JRl; JRo; Behind; Sync; s-flat;
                                   polF; JoinF; Lane; Runs; Start; Whole; OuterDone; Waiting; Slots; Ends; Asc; LanesIn; NoKill; OwedEnd; Unended; Kept;
                                   h-live; h-end; l-dead; TailP; tailp; Beneath; alike; cov; voc; slots-mv; ≈-refl)
  renaming (Nths to Listed)
open import adequacy.Cursor.Frame using (owes; Fr; f-lanes; f-lane; f-lnct; d-lanes)
open import adequacy.Cursor.Rise using (RT; SimC; settled; pending; flying; adrift)
open import adequacy.Cursor.Tear using (c-abs; husk-of)
open import adequacy.Enter using (module Lanes; within-sound)
open import adequacy.Walk using (dead-closed; begun-join; husk-≈)
open import adequacy.Regions using (lane-sole)
open import adequacy.Few using (kept-lane)
open import adequacy.PinTail using (end-tail)
open import adequacy.Census using (module Count; lt-le; eq-le)
open import adequacy.Up using (module Past; VHot; vhot-hots; begun-out; NoRow; nr-≈; nr-tr; fr-up; After; asc-pre; asc-post)
open import adequacy.Bound using (JDone; join-row-d)
open import adequacy.Admit using (before; begun-nq; dead-ends; live-of; start-open)
open import adequacy.Settle using (done-mk; done-use; begun-ru; lane-w)

------------------------------------------------------------------------
-- A tail read through finitely many rows more.

tailp-bn : ∀ {A} {C} {E E′ X : EmissionSet A} {P} → Beneath E E′ → (∀ {y e} → X y e → E′ y e) → TailP C E P → TailP C X P
tailp-bn (ls , g) back (tailp ks f) = tailp (ls ++ ks) λ x o → go (g (back x)) o
  where
    go : ∀ {y e} → _ → _ → _
    go (inj₁ x′) o with f x′ o
    ... | inj₁ py = inj₁ py
    ... | inj₂ i  = inj₂ (∈-++⁺ʳ ls i)
    go (inj₂ i) _ = inj₂ (∈-++⁺ˡ i)

------------------------------------------------------------------------
-- A joiner's end row: done there.

module _ {A B : Set} (L : Pos → A → EmissionSet B) (O : EmissionSet A) (Over : Pos → Set) (R : Pos → Set)
         (Cut : Pos → Pos → Set) (Hand : Pos → Set) where
  open Joining L O (λ _ _ → ⊥) Over R Cut Hand

  jend : ∀ {k} → JoinT k end → Done k
  jend (oend _ dn)         = dn
  jend (lane _ _ _ _ ())
  jend (lend _ _ _ _ _ dn) = dn
  jend (run () _)
  jend (rend () _ _)

join-end : ∀ op {A B} (F : A → Den B) (O : EmissionSet A) {k} → JoinF op F O k end → JDone op F O k
join-end (mergeᶠ nothing)  F O = jend (LaneOf F) O (Ended O) (λ _ → ⊤) (λ _ _ → ⊥) (λ _ → ⊥)
join-end (mergeᶠ (just m)) F O = jend (Bounded.Lane m F O) O (Ended O) (Bounded.Indexed m F O) (λ _ _ → ⊥) (Bounded.Queued m F O)
join-end switchᶠ           F O = jend (LaneOf F) O (Ended O) (λ _ → ⊤) (Switch.Cut F O) (λ _ → ⊥)
join-end exhaustᶠ          F O = jend (LaneOf F) O (Ended O) (Exhaust.Run F O) (λ _ _ → ⊥) (λ _ → ⊥)

-- Done, the outer over.
done-over : ∀ op {A B} {F : A → Den B} {O : EmissionSet A} {c} → JDone op F O c → Ended O c
done-over (mergeᶠ nothing)  = proj₁
done-over (mergeᶠ (just m)) = proj₁
done-over switchᶠ           = proj₁
done-over exhaustᶠ          = proj₁

-- No queued lane handed a slot at `c`: only a bounded merge queues.
NoHand : ∀ {A B} → FlatOp → (A → Den B) → EmissionSet A → Pos → Set
NoHand (mergeᶠ nothing)  F O c = ⊤
NoHand (mergeᶠ (just m)) F O c = ¬ Bounded.Queued m F O c
NoHand switchᶠ           F O c = ⊤
NoHand exhaustᶠ          F O c = ⊤

-- A bounded lane started past `r` is for a value at or before it.
start-at : ∀ m {A B} (F : A → Den B) (O : EmissionSet A) {i q ls s r} → Bounded.Starts m F O i q ls s → s ≡ r ++ [ ix 1 ] → q ≼ r
start-at m F O {q = q} {r = r} (Bounded.room _)    e = eq-le {q} {r} (∷ʳ-injectiveˡ q r e)
start-at m F O {q = q} {r = r} (Bounded.freed _ _) e = eq-le {q} {r} (∷ʳ-injectiveˡ q r e)
start-at m F O {q = q} {r = r} (Bounded.queued {c} _ qc _ _ _) e = lt-le {q} {r} (subst (q ≺_) (∷ʳ-injectiveˡ c r e) qc)

-- No lane, for a value at or before `p`, starts at `p ⊕ [ ix 1 ]`: none
-- handed a slot there.
nohand : ∀ op {A B} {F : A → Den B} {O : EmissionSet A} {p}
       → (∀ {q a} → O q (out a) → Runs (polF op F O) q → q ≼ p → Start (polF op F O) q a (p ++ [ ix 1 ]) → ⊥) → NoHand op F O p
nohand (mergeᶠ nothing)  _ = tt
nohand (mergeᶠ (just m)) {F = F} {O} g (i , q , a , sb) = g (Nths.nth-val O (proj₁ sb)) (i , a , proj₁ sb) (start-at m F O (proj₂ sb) refl) (i , sb)
nohand switchᶠ           _ = tt
nohand exhaustᶠ          _ = tt

-- A lane's end, uncut and handing no slot, as its joiner's.
jlend : ∀ op {A B} {F : A → Den B} {O q a c} → O q (out a) → Runs (polF op F O) q → Lane (polF op F O) q a c end
      → (∀ {q′} → Kill (polF op F O) q q′ → q′ ≺ c → ⊥) → NoHand op F O c → JDone op F O c → JoinF op F O c end
jlend (mergeᶠ nothing)  {F = F} {O} x rn l _  _  dn = Merge.lend {f = F} {o = O} x rn l (λ ()) (λ ()) dn
jlend (mergeᶠ (just m)) {F = F} {O} x rn l _  nh dn = Bounded.lend {n = m} {f = F} {o = O} x rn l (λ ()) nh dn
jlend switchᶠ           {F = F} {O} x rn l nk _  dn = Switch.lend {f = F} {o = O} x rn l (λ { (_ , a′ , x′ , lt , lt′) → nk (a′ , x′ , lt) lt′ }) (λ ()) dn
jlend exhaustᶠ          {F = F} {O} x rn l _  _  dn = Exhaust.lend {f = F} {o = O} x rn l (λ ()) (λ ()) dn

-- With none waiting, one fewer lane running: the slots hold.
slots-pred : ∀ op {A B} {F : A → Den B} {O : EmissionSet A} {C vs n} → Slots (polF op F O) C vs [] n → Slots (polF op F O) C vs [] (pred n)
slots-pred (mergeᶠ nothing)  s            = s
slots-pred (mergeᶠ (just m)) (L , le , _) = L , ≤-trans pred[n]≤n le , inj₁ refl
slots-pred switchᶠ           s            = s
slots-pred exhaustᶠ          s            = s

-- A killed lane started under its own value.
ks : ∀ op {A B} {F : A → Den B} {O : EmissionSet A} {q q″ a s} → Kill (polF op F O) q q″ → Start (polF op F O) q a s → s ≡ q ++ [ ix 1 ]
ks (mergeᶠ nothing)  ()
ks (mergeᶠ (just m)) ()
ks switchᶠ           _  st = st
ks exhaustᶠ          ()

unq : ∀ {X Y : Set} {ws : List (X × Y)} {a qu} → ws ≡ [] → map proj₂ ws ≡ a ∷ qu → ⊥
unq refl ()

module _ {R : Set} (Rt : EmissionSet R) where

  ----------------------------------------------------------------------
  -- THE HAND-OFF: a lane ended at `p` with a value waiting.  Only a
  -- bounded merge queues; there every slot is taken, the head starts at
  -- `p ⊕ [ ix 1 ]`, and the rest wait counted past the census taken
  -- there.  The head's lane ends past `p`, so the joiner is not done.
  handoff : ∀ {Γ A B} op {f : A → Obs Timeline Γ B} {ω d n qu a₁} {o : St Γ A} {ls} {c : Ctx R Γ B} {Cr Rg E′ O vs ws p}
          → closed c ≡ false
          → (¬ JDone op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O p → Σ Cur λ Cr′ → Fr Rt Cr′ (aft p) Rg c owes E′ × Moves (RT Rt Cr) [] (RT Rt Cr′))
          → (ji : JInv (scopeOf c) f O) → Sync (scopeOf c) (JRo (scopeOf c) Rg op f O) (aft p) o O
          → Begun (scopeOf c) (JRl (scopeOf c) Rg op f O) (aft p) (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) O vs ls (pred n)
          → suc (pred n) ≡ n
          → OwedEnd (bef p) (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) vs p
          → Waiting (bef p) (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) O vs ws (a₁ ∷ qu)
          → Whole (aft p) (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) O vs ws → OuterDone (aft p) O d
          → Asc vs → Ends (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) O
          → LanesIn (Hots (full (scopeOf c))) (JRl (scopeOf c) Rg op f O) (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) O
          → JoinE (scopeOf c) op f ω O E′ → Sound (JRo (scopeOf c) Rg op f O) O
          → Behind (aft p) (JoinF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O)
          → Slots (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) (bef p) vs ws n
          → After Rt Cr (start c op f ω d (pred n) qu o ls a₁ p)
  handoff (mergeᶠ nothing) _ _ _ _ _ _ _ wt _ _ _ _ _ _ _ _ _ = ⊥-elim (unq (proj₁ (proj₂ (proj₂ (proj₂ wt))) tt) (proj₁ wt))
  handoff switchᶠ          _ _ _ _ _ _ _ wt _ _ _ _ _ _ _ _ _ = ⊥-elim (unq (proj₁ (proj₂ (proj₂ (proj₂ wt))) tt) (proj₁ wt))
  handoff exhaustᶠ         _ _ _ _ _ _ _ wt _ _ _ _ _ _ _ _ _ = ⊥-elim (unq (proj₁ (proj₂ (proj₂ (proj₂ wt))) tt) (proj₁ wt))
  handoff (mergeᶠ (just m)) {ws = []} _ _ _ _ _ _ _ (() , _) _ _ _ _ _ _ _ _ _
  handoff (mergeᶠ (just m)) {ws = _ ∷ _} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_ , _ , inj₁ ())
  handoff (mergeᶠ (just m)) {f = f} {ω = ω} {d = d} {n = n} {o = o} {ls = ls} {c = c} {Cr = Cr} {Rg = Rg} {O = O} {vs = vs} {ws = (q₁ , a₁) ∷ ws′} {p = p}
    cl lift ji sy bg sp oe₀ (refl , (_ ∷ᴾ ap) , wf , _ , hd) wh od ao en li jm so bh (L₀ , le , inj₂ nm′) =
    subst (After Rt Cr) (sym (start-open {c = c} {op = mergeᶠ (just m)} {f = f} {a = a₁} {p = p} cl))
      ( proj₁ lifted , aft p
      , pending (f-lnct (f-lane (f-lanes {D = aft p} (proj₁ (proj₂ lifted)) ji sy lf′ y₁ (nm nqb₁) ru₁ (h-live st₁ ln₁ (λ ()) ue₁) none cnt′
                                          wt′ wh′ od ah′ ao′ en li jm so (λ _ → within-sound (JInv.fi ji a₁ s₁ ok₁) wi) bh (λ ()) sl′)))
                (≺-ext p {ix 1} [] , ok₁ , JInv.adm ji , ≈-refl , wi)
      , proj₂ (proj₂ lifted) )
    where
      sc = scopeOf c
      F = λ a → ⟦ f a ⟧ (full sc)
      P = polF (mergeᶠ (just m)) F O
      s₁ = p ++ [ ix 1 ]
      w = (q₁ , a₁)
      open Count (JInv.ok ji) m F (JInv.fi ji) (JInv.io ji) hiding (P)
      open Values O using (Nth)
      open Nths O using (nth-lt)
      open BoundedI (JInv.ok ji) m F (JInv.fi ji) (JInv.io ji) using (okS)
      open Past p using (nm)

      -- the head: passed, and started at the first owed end, `p`
      y₁ = proj₁ (wf (here refl))
      nqb₁ = proj₁ (proj₂ (wf (here refl)))
      ru₁ = proj₁ (proj₂ (proj₂ (wf (here refl))))
      st₁ : Start P q₁ a₁ s₁
      st₁ = hd oe₀ λ { (_ , _ , _ , _ , _ , oc) → oc }
      ln₁ = sub-ln (proj₂ st₁)
      ok₁ = okS (proj₂ st₁)
      wi = Lanes.lane-within sc f ji (mergeᶠ (just m)) li y₁ st₁
      ue₁ : Unended (aft p) P q₁ a₁
      ue₁ lc _ = ≺-trans {p} {s₁} (≺-ext p []) (proj₂ (Lanes.past sc f ji (mergeᶠ (just m)) st₁ lc))

      -- its lane ends past `p`: the joiner is not done there
      nd : ¬ JDone (mergeᶠ (just m)) F O p
      nd dn with done-use (mergeᶠ (just m)) dn y₁ ru₁ (before p {q₁} nqb₁) (λ ())
      ... | _ , lc , c₀p = c₀p (ue₁ lc (λ ()))
      lifted = lift nd

      -- the values listed: the begun, the head, the rest waiting
      L₀′ : Listed O 0 ((vs ++ [ w ]) ++ ws′)
      L₀′ = subst (Listed O 0) (sym (++-assoc vs [ w ] ws′)) L₀
      Lv′ = proj₁ (nths-split (vs ++ [ w ]) L₀′)
      Lw′ = proj₂ (nths-split (vs ++ [ w ]) L₀′)
      Lv = proj₁ (nths-split vs Lv′)
      nth₁ : Nth (length vs) q₁ a₁
      nth₁ = proj₁ (proj₂ (nths-split vs Lv′))

      -- the census at `aft p`: the begun lanes, then the head's, on
      cv = cen-begun Lv bg (λ i → ∈-++⁺ˡ i) c-nil
      d′ = proj₁ cv
      on₁ : ∀ {c} → Bounded.Ends m F O (length vs) (Bounded.Sched m F O (length vs)) c → Σ Pos λ c′ → OwedEnd (aft p) P (vs ++ [ w ]) c′ × c′ ≼ c
      on₁ {c} e = c , (q₁ , a₁ , ∈-++⁺ʳ vs (here refl) , ends-at nth₁ e , (λ ()) , ue₁ (ends-at nth₁ e) (λ ())) , ≼-refl {c}
      eqL : suc (length vs) ≡ length (vs ++ [ w ])
      eqL = sym (trans (length-++ vs) (+-comm (length vs) 1))
      cs′ : Census (aft p) (vs ++ [ w ]) (length (vs ++ [ w ])) d′
      cs′ = subst (λ k → Census (aft p) (vs ++ [ w ]) k d′) eqL (c-on (proj₁ (proj₂ cv)) on₁)
      dm′ : d′ + m ≡ length (vs ++ [ w ])
      dm′ = trans (cong (d′ +_) (trans (sym nm′) (sym sp))) (trans (+-suc d′ (pred n)) (trans (cong suc (proj₂ (proj₂ cv))) eqL))

      nq′ : ∀ {q a} → (q , a) ∈ ws′ → ¬ Owes (aft p) q
      nq′ i = nm (proj₁ (proj₂ (wf (there i))))

      ah′ = ahead-from ws′ Lw′ nq′ cs′ (≤-reflexive dm′)

      hd′ : ∀ ws″ → Listed O (length (vs ++ [ w ])) ws″ → (∀ {q a} → (q , a) ∈ ws″ → ¬ Owes (aft p) q) → Head (aft p) P (vs ++ [ w ]) ws″
      hd′ []               _         _  = tt
      hd′ ((q₂ , a₂) ∷ ws″) (nth₂ , _) nq = head-at Lv′ cs′ dm′ (nq (here refl)) nth₂ {ws = ws″}

      wt′ : Waiting (aft p) P O (vs ++ [ w ]) ws′ (map proj₂ ws′)
      wt′ = refl , ap
          , (λ i → let (y , nq , r , _) = wf (there i) in
                   y , nm nq , r , λ {s} st → let (_ , _ , c , _ , _ , _ , oc , cz) = ah′ i st in ≺-trans {p} {c} {s} oc cz)
          , (λ ()) , hd′ ws′ Lw′ nq′

      wh′ : Whole (aft p) P O (vs ++ [ w ]) ws′
      wh′ y nq r with wh y nq r
      ... | inj₁ i           = inj₁ (∈-++⁺ˡ i)
      ... | inj₂ (here refl) = inj₁ (∈-++⁺ʳ vs (here refl))
      ... | inj₂ (there i)   = inj₂ i

      ao′ : Asc (vs ++ [ w ])
      ao′ = pairs-++⁺ ao ([]ᴬ ∷ᴾ []ᴾ) (tabulate λ {x} i → let (j , nj , lt) = nths-∈ Lv i in nth-lt lt nj nth₁ ∷ᴬ []ᴬ)

      sl′ : Slots P (aft p) (vs ++ [ w ]) ws′ (suc (pred n))
      sl′ = L₀′ , subst (_≤ m) (sym sp) le , inj₂ (trans sp nm′)

      lf′ = subst (λ l → Begun sc (JRl sc Rg (mergeᶠ (just m)) f O) (aft p) P O vs l (pred n)) (sym (reverse-involutive ls)) bg
      cnt′ : suc (pred n) ≡ pred n + 1
      cnt′ = sym (+-comm (pred n) 1)

  ----------------------------------------------------------------------
  -- A LANE'S END at `p`: the lane's row there the joiner's, the frames
  -- above past it unless the joiner's own end flies there.
  rise-lane-cp : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {ω} {d n q o pre post} {c : Ctx R Γ B} {s p k′ sh t}
               → rise (inLanes op f ω d n q o pre post c) s cp p ≡ moved k′ sh t
               → SimC Rt ⟨ inLanes op f ω d n q o pre post c , s , rising cp , p ⟩ sh k′
  rise-lane-cp {op = op} {f = f} {ω = ω} {d = d} {n = n} {o = o} {pre = pre} {post = post} {c = c} {p = p} eq {Cr = Cr}
    (flying (f-lanes {Rg = Rg} {E = E} {E′ = E′} {O = O} {vs₁ = vs₁} {vs₂ = vs₂} {n₁ = n₁} {n₂ = n₂} {q = q₀} {a = a₀} {b = true}
              fr ji sy lf y₀ nq ru (h-live st le uk ue) rt cnt wt wh od _ ao en li jm so sd bh _ sl) cl (at , l , refl , _ , sy′ , row)) with eq
  ... | refl = go wt wh sl
    where
      sc = scopeOf c
      F = λ a → ⟦ f a ⟧ (full sc)
      P = polF op F O
      vs = vs₁ ++ (q₀ , a₀) ∷ vs₂
      ls′ = pre ʳ++ lnS false (cutS false at l) ∷ post
      open Past p using (up; begun-up; nm; owes-up; off-rg; in-off; behind-up; kill-up; module Book)
      open Book {P = P} {O = O} using (whole-up; od-up)

      lc : Lane P q₀ a₀ p end
      lc = voc le row
      hr : JRl sc Rg op f O q₀ p
      hr = Lanes.lane-rows sc f ji op li y₀ lc
      rl = Lanes.lane-rows sc f ji op li
      -- the outer's region holds no lane's row
      no : ¬ JRo sc Rg op f O p
      no r = proj₂ r (proj₂ hr)
      oo = off-rg so no
      ku = kill-up op oo
      nh : ¬ VHot (full sc) p
      nh hv = proj₂ (JInv.ok ji) (vhot-hots (full sc) hv) (lane-w ji op y₀ lc) (⊑-inside (⊑ʷ-refl p))

      sole : ∀ {q q′} → JRl sc Rg op f O q p → JRl sc Rg op f O q′ p → q ≡ q′
      sole r r′ = lane-sole (JInv.ok ji) F (JInv.fi ji) (JInv.io ji) op (proj₂ r) (proj₂ r′)
      nb₁ : ∀ {q a} → (q , a) ∈ vs₁ → ¬ JRl sc Rg op f O q p
      nb₁ i r = ≺-irrefl {q₀} (subst (λ x → x ≺ q₀) (sole r hr) (asc-pre vs₁ ao i))
      nb₂ : ∀ {q a} → (q , a) ∈ vs₂ → ¬ JRl sc Rg op f O q p
      nb₂ i r = ≺-irrefl {q₀} (subst (λ x → q₀ ≺ x) (sole r hr) (asc-post vs₁ ao i))

      -- the outer past `p`
      sy↑ = up sy so no nh

      -- the lane listed ended: its husk what it still runs
      dead = l-dead {E = E} (h-end lc (≺-irrefl {p}) (tailp-bn (cov le) kept-lane (end-tail sy′ (sd tt) row (≺-irrefl {p}))))
                    (husk-≈ le (proj₂ (husk-of sy′))) (λ t → t) (λ {r} t {q′} k → ≼-trans {r} {p} {q′} t (uk k))

      pn : n ≡ suc (n₁ + n₂)
      pn = trans cnt (+-suc n₁ n₂)
      sp : suc (pred n) ≡ n
      sp = trans (cong (λ k → suc (pred k)) pn) (sym pn)

      bg″ : Begun sc (JRl sc Rg op f O) (aft p) P O vs ls′ (pred n)
      bg″ = subst (Begun _ _ _ _ _ _ _) (sym (cong pred pn))
              (subst (λ ls → Begun _ _ _ _ _ _ ls _) (sym (ʳ++-defn pre)) (begun-join (begun-up ku nb₁ nh lf) y₀ (nm nq) ru dead (begun-up ku nb₂ nh rt)))

      -- the joiner's only row at `p` is the lane's end
      nr : ¬ JDone op F O p → NoRow (JoinF op F O) p
      nr nd r v with join-row-d op F O r v
      ... | inj₁ (_ , dn) = nd dn
      ... | inj₂ (_ , _ , y , _ , ln , _) with sole (rl y ln) hr
      ...   | refl with Sound.fn so y y₀ tt tt
      ...     | refl with Sound.fn (sd tt) row (proj₁ (from (alike le) (ln , v))) tt v
      ...       | refl = nd (join-end op F O r)

      lift : ¬ JDone op F O p → Σ Cur λ Cr′ → Fr Rt Cr′ (aft p) Rg c owes E′ × Moves (RT Rt Cr) [] (RT Rt Cr′)
      lift nd = fr-up Rt fr tt (proj₁ hr) (nr-≈ (proj₂ jm) (nr-tr (nr nd))) nh

      absorb : ∀ {d k} → ¬ JDone op F O p → Sync sc Rg (aft p) (flatS op f ω d k [] o ls′) E′
             → After Rt Cr ⟨ c , flatS op f ω d k [] o ls′ , absorbed , p ⟩
      absorb nd hold = let (Cr′ , fr′ , mv) = lift nd in Cr′ , aft p , settled c-abs fr′ hold , mv

      -- passed, not at `p`: before it
      pst : ∀ {q b} → O q (out b) → ¬ Owes (aft p) q → q ≺ p
      pst {q} y nq′ with ≼-or-≻ q p
      ... | inj₁ qp = ≼-≢ {q} {p} qp (λ e′ → oo y tt (sym e′))
      ... | inj₂ pq = ⊥-elim (nq′ pq)

      bg-at : ∀ {k} → pred n ≡ k → Begun sc (JRl sc Rg op f O) (aft p) P O vs ls′ k
      bg-at e = subst (Begun sc (JRl sc Rg op f O) (aft p) P O vs ls′) e bg″

      hold-of : ∀ {d} k → pred n ≡ k → OuterDone (bef p) O d → Whole (bef p) P O vs [] → Slots P (bef p) vs [] n
              → Sync sc Rg (aft p) (flatS op f ω d k [] o ls′) E′
      hold-of k e od′ wh′ sl′ =
        s-flat ji sy↑ (joined (bg-at e) (refl , []ᴾ , (λ ()) , (λ _ → refl) , tt) (whole-up oo wh′) (od-up oo od′) (λ ()) ao en li
                               (subst (Slots P (aft p) vs []) e (slots-pred op (slots-mv op (λ {y} t → ≺→≼ {p} {y} t) (λ x o′ → in-off oo x tt o′) sl′))))
               jm so (behind-up bh)

      -- none waiting: the joiner's end flies where it is done
      quiet : ∀ {d} k → pred n ≡ k → OuterDone (bef p) O d → Whole (bef p) P O vs [] → Slots P (bef p) vs [] n
            → After Rt Cr ⟨ c , flatS op f ω d k [] o ls′ , settle d k true , p ⟩
      -- the outer runs past `p`: not done
      quiet {false} k e od′ wh′ sl′ = absorb nd (hold-of k e od′ wh′ sl′)
        where
          nd : ¬ JDone op F O p
          nd dn with done-over op dn
          ... | c₀ , x , c₀p = proj₂ od′ x (λ pc → pc (≼-≢ {c₀} {p} c₀p (λ e′ → oo x tt (sym e′))))
      -- a lane runs past `p`: not done
      quiet {true} (suc k) e od′ wh′ sl′ = absorb nd (hold-of (suc k) e od′ wh′ sl′)
        where
          bg-k = bg-at e
          nd : ¬ JDone op F O p
          nd dn with live-of bg-k (λ ())
          ... | q , a , i , uk′ , ue′
            with done-use op dn (begun-out bg-k i) (begun-ru bg-k i) (pst (begun-out bg-k i) (begun-nq bg-k i)) (λ kq → ≺→≼ {p} (uk′ kq))
          ...   | c₀ , lc′ , c₀p = c₀p (ue′ lc′ (λ {q′} kq → ≼-trans {c₀} {p} {q′} c₀p (≺→≼ {p} {q′} (uk′ kq))))
      -- the outer over, no lane running, none waiting: the joiner's end
      quiet {true} zero e od′ wh′ sl′ = Cr , bef p , flying fr cl (hold-of zero e od′ wh′ sl′ , shown) , silent ≃-refl
        where
          bg-0 = bg-at e
          wh↑ = whole-up oo wh′

          ov : Σ Pos λ c₀ → O c₀ end × c₀ ≼ p
          ov with proj₁ od′ tt
          ... | c₀ , x , nc = c₀ , x , ≺→≼ {c₀} {p} (before p {c₀} nc)

          gone : ∀ {q a} → O q (out a) → Runs P q → q ≺ p → (∀ {q′} → Kill P q q′ → q′ ≺ p → ⊥) → Σ Pos λ c′ → Lane P q a c′ end × c′ ≼ p
          gone {q} y r qp nk with wh↑ y (λ pq → ≺-absurd {q} {p} qp pq) (Pol.takes P r)
          ... | inj₂ ()
          ... | inj₁ iv with dead-ends bg-0 refl iv
          ...   | inj₁ (c′ , lc′ , nc′) = c′ , lc′ , nc′
          ...   | inj₂ (q′ , kq , nq′) = ⊥-elim (nk kq (≼-≢ {q′} {p} nq′ (λ e′ → oo (proj₁ (proj₂ (kill-out op kq))) tt (sym e′))))

          -- no lane takes the slot this end frees
          free : ∀ {q a} → O q (out a) → Runs P q → q ≼ p → Start P q a (p ++ [ ix 1 ]) → ⊥
          free {q} y r le′ st′ with wh↑ y le′ (Pol.takes P r)
          ... | inj₂ ()
          ... | inj₁ iv with dead-ends bg-0 refl iv
          ...   | inj₁ (c′ , lc′ , nc′) = nc′ (≺-trans {p} {p ++ [ ix 1 ]} {c′} (≺-ext p []) (proj₂ (Lanes.past sc f ji op st′ lc′)))
          ...   | inj₂ (q′ , kq , _) = oo y tt (∷ʳ-injectiveˡ p q (ks op kq st′))

          shown = proj₁ (to (alike (proj₂ jm)) ((jlend op y₀ ru lc (λ k lt → uk k lt) (nohand op free) (done-mk op ov gone)
                                                , proj₁ bh , λ tk kp _ → proj₂ bh tk (λ pk → pk kp)) , tt))

      go : ∀ {qu ws} → Waiting (bef p) P O vs ws qu → Whole (bef p) P O vs ws → Slots P (bef p) vs ws n
         → After Rt Cr (dequeue c op f ω d (pred n) qu o ls′ p)
      go {[]}    {_ ∷ _} (() , _) _ _
      go {[]}    {[]}    _ wh′ sl′ = quiet (pred n) refl od wh′ sl′
      go {_ ∷ _}         wt′ wh′ sl′ =
        handoff op cl lift ji sy↑ bg″ sp (q₀ , a₀ , ∈-++⁺ʳ vs₁ (here refl) , lc , (λ k → uk k) , ≼-refl {p})
                wt′ (whole-up oo wh′) (od-up oo od) ao en li jm so (behind-up bh) sl′
  rise-lane-cp _ (flying (f-lanes {b = false} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (_ , _ , _ , () , _))
  rise-lane-cp _ (flying (d-lanes _ _ _ _ _ _ _) _ ())
  rise-lane-cp _ (adrift fr cl _) = ⊥-elim (subst T cl (dead-closed Rt fr refl))
  rise-lane-cp _ (settled () _ _)
