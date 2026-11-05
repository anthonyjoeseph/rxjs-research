{-# OPTIONS --guardedness #-}

-- AN OUTER'S VALUE ADMITTED: a joiner's outer rises at `p`, and the
-- joiner subscribes the value's lane at `p ⊕ [ ix 1 ]`.  The frames above
-- the joiner show nothing at `p` (its row there is its outer's, in what
-- no lane's region holds), so they move past `p`; the lane, owed where
-- the cursor has not passed, is pending within its own region.
module adequacy.Admit where

open import Data.Bool using (T; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Nat using (zero; suc; _<ᵇ_; _<?_; _+_; _∸_; _≤_; _<_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; <ᵇ⇒<; <⇒<ᵇ; ≮⇒≥; <-irrefl; ≤-antisym; <-≤-trans; ≤-trans;
                                      m≤n+m; m≤m+n; m+n≤o⇒m≤o∸n; m+n∸n≡m)
open import Data.List using ([]; _∷_; [_]; _++_; reverse; length)
open import Data.List.Properties using (reverse-involutive; ++-identityʳ; ++-assoc; map-++; length-++)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (tabulate) renaming (_∷_ to _∷ᴬ_; [] to []ᴬ)
open import Data.List.Relation.Unary.AllPairs using () renaming (_∷_ to _∷ᴾ_; [] to []ᴾ)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (++⁺ to pairs-++⁺)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; yes; no)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; ix; Timeline; _≟ᵖ_)
open import denotation.EmissionSet using (EmissionSet; Den; _≺_; _≼_; out; end; ⟦_⟧; enter; LaneOf; module Bounded; module Values; module Exhaust)
open import denotation.Laws.Modulus using (≺-ext; ≺-irrefl; ≼-or-≻; ≺-trans; ≺-absurd; ≼-≺-≺; ≼-trans; ≼-antisym)
open import denotation.Laws.Join using (module Join)
open import denotation.Laws.Nth using (module Nths)
open import denotation.Laws.BoundedInv using (module BoundedI)
open import denotation.Laws.Worlds using (InvAt; ok-step; ok-in; world-after; ⊑-inside)
  renaming (⊑-refl to ⊑ʷ-refl)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; Scope; lnS; cutS; cut; killAll; attached; ⟨_,_,_,_⟩; scopeOf; closed; rise; moved; start; subscribing; rising; absorbed; flatS; nx; attAt; pend;
                    inOuter; inLanes; inLn; inCut)
open import adequacy.Rows using (full; pendRows; Moves; _⇄_; _≃_)
open _≃_ using (from)
open import adequacy.Cursor using (Cur; Pol; Kill; kill-out; bef; aft; Owes; _≈_; ≈-refl; Sound; JInv; Joined; joined; Begun; none; more; JoinE; JRl; JRo; Behind; Sync; polF; JoinF; Lane; Start; Runs; Whole; OuterDone; Ahead; Asc; h-live; wait-[]; Waiting; Slots; Unended; alike; Head; Hole; Unkilled; h-end; h-kill; LaneSt; l-live; l-dead; Kept; NoKill; Thru; TailP; tailp; tailp-⊑; ∅ᵖ; cov)
  renaming (Nths to Listed)
open import adequacy.Cursor.Frame using (owes; Fr; f-outer; f-lanes; f-lane; f-lnct; d-outer)
open import adequacy.Cursor.Rise using (Inv; RT; SimC; settled; pending; flying; adrift)
open import adequacy.Cursor.Tear using (c-abs; husk-of; unsub-husk; off-husk)
open import adequacy.PinTail using (ptl; pt-bn; pin-tail)
open import adequacy.Census using (module Count)
open import adequacy.Enter using (module Lanes; within-sound)
open import adequacy.Walk using (dead-closed; husk-≈)
open import adequacy.Up using (module Past; VHot; vhot-hots; begun-out; nr-≈; nr-tr; join-nr; fr-up; After)
open import adequacy.Cursor using (s-flat)

-- A begun lane's value, passed.
begun-nq : ∀ {Γ} {sc} {Rl C A B} {P : Pol A B} {O : EmissionSet A} {vs ls n q a}
         → Begun {Γ} sc Rl C P O vs ls n → (q , a) ∈ vs → ¬ Owes C q
begun-nq (more _ nq _ _ _) (here refl) = nq
begun-nq (more _ _ _ _ bg) (there i)   = begun-nq bg i

-- Not owed at `p`: passed before it.
before : ∀ p {q} → ¬ Owes (bef p) q → q ≺ p
before p {q} nq with ≼-or-≻ p q
... | inj₁ pq = ⊥-elim (nq pq)
... | inj₂ qp = qp

-- No lane running: every begun lane ended, or was killed, where passed.
dead-ends : ∀ {Γ} {sc : Scope Γ} {Rl C A B} {P : Pol A B} {O : EmissionSet A} {vs ls n q a}
          → Begun sc Rl C P O vs ls n → n ≡ 0 → (q , a) ∈ vs
          → (Σ Pos λ c → Lane P q a c end × ¬ Owes C c) ⊎ (Σ Pos λ q′ → Kill P q q′ × ¬ Owes C q′)
dead-ends (more {b = true} _ _ _ _ _) () _
dead-ends (more {b = false} _ _ _ (l-dead (h-end lc nc _) _ _ _) _) _ (here refl) = inj₁ (_ , lc , nc)
dead-ends (more {b = false} _ _ _ (l-dead (h-kill kq nq _) _ _ _) _) _ (here refl) = inj₂ (_ , kq , nq)
dead-ends (more {b = false} _ _ _ _ bg) z (there i) = dead-ends bg z i

-- A lane running: a begun lane unkilled and unended.
live-of : ∀ {Γ} {sc : Scope Γ} {Rl C A B} {P : Pol A B} {O : EmissionSet A} {vs ls n}
        → Begun sc Rl C P O vs ls n → ¬ n ≡ 0 → Σ Pos λ q → Σ A λ a → (q , a) ∈ vs × Unkilled C P q × Unended C P q a
live-of none nz = ⊥-elim (nz refl)
live-of (more {q = q} {a = a} {b = true} _ _ _ (l-live (h-live _ _ uk ue) _ _) _) _ = q , a , here refl , uk , ue
live-of (more {b = false} _ _ _ _ bg) nz with live-of bg nz
... | q , a , i , uk , ue = q , a , there i , uk , ue

-- An exhaust's cursor: at a value, the lane last run is one.
module ExCur {A B : Set} (F : A → Den B) (O : EmissionSet A) (fn : ∀ {k e e′} → O k e → O k e′ → e ≡ e′) where
  open Exhaust F O using (cur₀; run; drop) renaming (Cur to XCur)
  open Values O using (Next)

  cur-val : ∀ {x q} → XCur x q → Σ A λ b → O x (out b)
  cur-val (cur₀ {a = a} y _)             = a , y
  cur-val (run {a₂ = a₂} _ _ _ _ y _ _)  = a₂ , y
  cur-val (drop {a₂ = a₂} _ _ _ y _ _)   = a₂ , y

  -- The value before `x` is one.
  next-fun : ∀ {q q′ x b b′} → O q (out b) → O q′ (out b′) → q ≺ x → q′ ≺ x → Next q x → Next q′ x → q ≡ q′
  next-fun {q} {q′} y y′ lt lt′ n n′ = ≼-antisym {q} {q′} (λ q′q → n′ y q′q lt) (λ qq′ → n y′ qq′ lt′)

  cur-fun : ∀ {x q q′} → XCur x q → XCur x q′ → q ≡ q′
  cur-fun (cur₀ _ _)            (cur₀ _ _)            = refl
  cur-fun (cur₀ _ _)            (run _ _ _ _ _ _ _)   = refl
  cur-fun (run _ _ _ _ _ _ _)   (cur₀ _ _)            = refl
  cur-fun (run _ _ _ _ _ _ _)   (run _ _ _ _ _ _ _)   = refl
  cur-fun (cur₀ _ least)        (drop cu _ _ _ lt _)  = ⊥-elim (least (proj₂ (cur-val cu)) lt)
  cur-fun (drop cu _ _ _ lt _)  (cur₀ _ least)        = ⊥-elim (least (proj₂ (cur-val cu)) lt)
  cur-fun (run cu y l cx _ lt n) (drop cu′ y′ ul _ lt′ n′) with next-fun (proj₂ (cur-val cu)) (proj₂ (cur-val cu′)) lt lt′ n n′
  ... | refl with cur-fun cu cu′
  ...   | refl with fn y y′
  ...     | refl = ⊥-elim (ul l cx)
  cur-fun (drop cu′ y′ ul _ lt′ n′) (run cu y l cx _ lt n) with next-fun (proj₂ (cur-val cu)) (proj₂ (cur-val cu′)) lt lt′ n n′
  ... | refl with cur-fun cu cu′
  ...   | refl with fn y y′
  ...     | refl = ⊥-elim (ul l cx)
  cur-fun (drop cu _ _ _ lt n)  (drop cu′ _ _ _ lt′ n′) with next-fun (proj₂ (cur-val cu)) (proj₂ (cur-val cu′)) lt lt′ n n′
  ... | refl = cur-fun cu cu′

-- A SWITCH'S KILL at `p`: the value there kills every begun lane.  A
-- live lane is cut, its husk what its rows show past `p`; it runs
-- nothing that is not its, and its kept pins are those `p` reaches.
module Kills (p : Pos) where
  open Past p using (up; nm; tailp-up)

  kill-live : ∀ {Γ} {sc : Scope Γ} {Rg} {A B} {F : A → Den B} {O : EmissionSet A} {q a a′ at l E}
            → O p (out a′) → ¬ Owes (bef p) q → ¬ Rg p → ¬ VHot (full sc) p
            → Hole (bef p) (polF switchᶠ F O) q a ∅ᵖ E true → Sync sc Rg (bef p) l E → Sound Rg E
            → LaneSt sc Rg (aft p) (polF switchᶠ F O) q a (lnS false (proj₁ (cut (cutS true at l)))) false
  kill-live {sc = sc} {Rg = Rg} {F = F} {O = O} {q = q} {a = a} {a′ = a′} {at = at} {E = E} y nq nr nh (h-live st e uk ue) sy sd = cutting at
    where
      P = polF switchᶠ F O
      kp : Pol.Kill P q p
      kp = a′ , y , [ (λ le → ⊥-elim (nq le)) , (λ lt → lt) ]′ (≼-or-≻ p q)
      sy′ = up sy sd nr nh
      hk = husk-≈ e (proj₂ (husk-of sy′))
      tp : TailP (aft p) (Kept P q a) (proj₁ (husk-of sy′))
      tp with pt-bn (cov e) (λ x → x) (pin-tail sy′)
      ... | ptl ks pf = tailp ks row
        where
          row : ∀ {y e} → Kept P q a y e → Owes (aft p) y → _
          row (inj₁ (_ , nk)) o                  = ⊥-elim (nk kp o)
          row (inj₂ (r , refl , ln , nkr , _)) o = pf ln o (nkr kp)
      nk : ∀ {r} → Thru (aft p) r → NoKill P q r
      nk {r} t {q′} k = ≼-trans {r} {p} {q′} t (uk k)
      cutting : ∀ at′ → LaneSt sc Rg (aft p) P q a (lnS false (proj₁ (cut (cutS true at′ _)))) false
      cutting attached  = let (_ , hk′ , le) = unsub-husk hk in l-dead {E = E} (h-kill kp (≺-irrefl {p}) (tailp-⊑ tp le)) hk′ (λ t → t) nk
      cutting (attAt r) = l-dead {E = E} (h-kill kp (≺-irrefl {p}) tp) (off-husk hk) (λ t → t) nk

  kill-begun : ∀ {Γ} {sc : Scope Γ} {Rl} {A B} {F : A → Den B} {O : EmissionSet A} {vs ls n a′}
             → O p (out a′) → (∀ {q a} → (q , a) ∈ vs → ¬ Rl q p) → ¬ VHot (full sc) p
             → Begun sc Rl (bef p) (polF switchᶠ F O) O vs ls n → Begun sc Rl (aft p) (polF switchᶠ F O) O vs (proj₁ (killAll ls)) 0
  kill-begun y nl nh none = none
  kill-begun {F = F} {O = O} y nl nh (more {q = q} x nq r (l-live {at = at} h sy sd) bg) =
    more x (nm {q} nq) r (kill-live {F = F} {O = O} {at = at} y nq (nl (here refl)) nh h sy sd) (kill-begun {F = F} y (λ i → nl (there i)) nh bg)
  kill-begun {F = F} y nl nh (more {q = q} x nq r (l-dead {E = E} (h-end {c = c} lc nc tp) hk dm nk) bg) =
    more x (nm {q} nq) r (l-dead {E = E} (h-end lc (nm {c} nc) (tailp-up tp)) hk dm nk) (kill-begun {F = F} y (λ i → nl (there i)) nh bg)
  kill-begun {F = F} y nl nh (more {q = q} x nq r (l-dead {E = E} (h-kill {q′ = q′} kq nq′ tp) hk dm nk) bg) =
    more x (nm {q} nq) r (l-dead {E = E} (h-kill kq (nm {q′} nq′) (tailp-up tp)) hk dm nk) (kill-begun {F = F} y (λ i → nl (there i)) nh bg)

-- The lane subscribed where its joiner's observer is open.
start-open : ∀ {R Γ A B} {c : Ctx R Γ B} {op} {f : A → Obs Timeline Γ B} {ω d n q o ls a p} → closed c ≡ false
           → start c op f ω d n q o ls a p
             ≡ ⟨ inCut true (attAt (p ++ [ ix 1 ])) (inLn true (inLanes op f ω d (suc n) q o (reverse ls) [] c)) , pend (f a) (p ++ [ ix 1 ]) , subscribing , p ++ [ ix 1 ] ⟩
start-open cl rewrite cl = refl

module _ {R : Set} (Rt : EmissionSet R) where

  -- A value's lane, as its policy opens it at `p`: subscribed under
  -- `p`, its rows the value's entered there, no queue, its slot taken.
  record Opening {A B} (P : Pol A B) vs ws n p a (L : EmissionSet B) : Set where
    field
      st  : Start P p a (p ++ [ ix 1 ])
      ln  : L ≈ Lane P p a
      ru  : Runs P p
      w[] : ws ≡ []
      sl′ : Slots P (aft p) (vs ++ (p , a) ∷ []) ws (suc n)

  -- THE LANE OPENED: the frames above lifted past `p`, the joiner's
  -- bookkeeping with the value begun, its lane pending in its region.
  opens : ∀ {Cr Γ A B} op {f : A → Obs Timeline Γ B} {ω d n q ls n′ ls′} {c : Ctx R Γ B} {o a p Rg E E′}
        → Fr Rt Cr (bef p) Rg c owes E′ → (ji : JInv (scopeOf c) f E)
        → Joined (scopeOf c) (JRl (scopeOf c) Rg op f E) (bef p) (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E) E d n q ls
        → JoinE (scopeOf c) op f ω E E′ → Sound (JRo (scopeOf c) Rg op f E) E → Behind (bef p) (JoinF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E)
        → Sync (scopeOf c) (JRo (scopeOf c) Rg op f E) (aft p) o E → E p (out a)
        → (∀ {vs} → (∀ {q′} → ¬ JRl (scopeOf c) Rg op f E q′ p) → ¬ VHot (full (scopeOf c)) p
           → Begun (scopeOf c) (JRl (scopeOf c) Rg op f E) (bef p) (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E) E vs ls n
           → Begun (scopeOf c) (JRl (scopeOf c) Rg op f E) (aft p) (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E) E vs ls′ n′)
        → (∀ {vs ws} → Begun (scopeOf c) (JRl (scopeOf c) Rg op f E) (bef p) (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E) E vs ls n → Waiting (bef p) (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E) E vs ws q
           → Whole (bef p) (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E) E vs ws → Slots (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E) (bef p) vs ws n → Opening (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E) vs ws n′ p a (pendRows (full (scopeOf c)) (f a) (p ++ [ ix 1 ])))
        → Σ Cur λ Cr′ → Inv Rt Cr′ (aft p) ⟨ inCut true (attAt (p ++ [ ix 1 ])) (inLn true (inLanes op f ω d (suc n′) q o (reverse ls′) [] c))
                                            , pend (f a) (p ++ [ ix 1 ]) , subscribing , p ++ [ ix 1 ] ⟩
                        × Moves (RT Rt Cr) [] (RT Rt Cr′)
  opens op {f = f} {d = d} {n = n} {ls = ls} {n′ = n′} {ls′ = ls′} {c = c} {a = a} {p = p} {Rg = Rg} {E = E} fr ji jn@(joined {vs = vs} {ws = ws} bg wt wh od ah ao en li sl) m so bh sy row lb opn =
    Cr↑ , pending (f-lnct (f-lane (f-lanes {D = aft p} fr↑ ji sy lf row (≺-irrefl {p}) ru (h-live st ln (λ k → proj₂ (proj₂ (kill-out op k))) ue) none (sym (+-comm n′ 1))
                                           (wait-[] {O = E} w[] (wait-up (λ iv lc → λ { refl → nl (rl (begun-out bg iv) lc) }) ah′ wt)) wh′ od′ ah″ ao′ en li m so (λ _ → within-sound {sc = sc} (JInv.fi ji a s ok) wi) (behind-up bh) (λ ()) sl′)))
                  (≺-ext p {ix 1} [] , ok , JInv.adm ji , ≈-refl , wi)
        , moves
    where
      open Past p using (nm; owes-up; behind-up; begun-up; module Book)
      open Book {P = polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E} {O = E} using (ahead-up; wait-up)
      sc = scopeOf c
      P = polF op (λ a → ⟦ f a ⟧ (full sc)) E
      s = p ++ [ ix 1 ]
      io = JInv.io ji
      st = Opening.st (opn bg wt wh sl)
      ln = Opening.ln (opn bg wt wh sl)
      ru = Opening.ru (opn bg wt wh sl)
      w[] = Opening.w[] (opn bg wt wh sl)
      sl′ = Opening.sl′ (opn bg wt wh sl)

      -- the outer's row at `p` is in what no lane's region holds
      here-o = Sound.rg so row _
      nl : ∀ {q′} → ¬ JRl sc Rg op f E q′ p
      nl r = proj₂ here-o (proj₂ r)

      rl = Lanes.lane-rows sc f ji op li

      nh : ¬ VHot (full sc) p
      nh = λ hv → proj₂ (JInv.ok ji) (vhot-hots (full sc) hv) (InvAt.world io row) (⊑-inside (⊑ʷ-refl p))

      lifted = fr-up Rt fr tt (proj₁ here-o)
                 (nr-≈ (proj₂ m) (nr-tr (join-nr op (λ a → ⟦ f a ⟧ (full sc)) rl (λ y → end-at (InvAt.func io row y)) (λ _ _ _ r → nl r)))) nh
        where
          end-at : ∀ {b} → out b ≡ end → _
          end-at ()
      Cr↑ = proj₁ lifted
      fr↑ = proj₁ (proj₂ lifted)
      moves = proj₂ (proj₂ lifted)

      ok = ok-step p (ok-in (JInv.ok ji) (InvAt.world io row) (InvAt.real io row))
      wi = Lanes.lane-within sc f ji op li row st

      I = JInv.fi ji a s ok

      -- the lane's end lies past its subscription, past `p`
      ue : Unended (aft p) P p a
      ue l _ = let x = proj₁ (from (alike ln) (l , tt)) in ≺-trans {p} {s} (≺-ext p []) (world-after (InvAt.world I x) (InvAt.real I x))

      lf = subst (λ l → Begun sc (JRl sc Rg op f E) (aft p) P E vs l n′) (sym (reverse-involutive ls′)) (lb nl nh bg)

      -- no begun lane ends at `p`
      ah′ : Ahead (aft p) P vs ws
      ah′ = ahead-up (λ iv lc → λ { refl → nl (rl (begun-out bg iv) lc) }) ah
      ah″ : Ahead (aft p) P (vs ++ (p , a) ∷ []) ws
      ah″ iw st′ with ah′ iw st′
      ... | q′ , a′ , c′ , iv , rest = q′ , a′ , c′ , ∈-++⁺ˡ iv , rest

      ao′ : Asc (vs ++ (p , a) ∷ [])
      ao′ = pairs-++⁺ ao ([]ᴬ ∷ᴾ []ᴾ) (tabulate λ {x} i → before p {proj₁ x} (begun-nq bg i) ∷ᴬ []ᴬ)

      wh′ : Whole (aft p) P E (vs ++ (p , a) ∷ []) ws
      wh′ {q′} y nq r with p ≟ᵖ q′
      ... | yes refl with InvAt.func io row y
      ...   | refl = inj₁ (∈-++⁺ʳ vs (here refl))
      wh′ {q′} y nq r | no ne = [ (λ i → inj₁ (∈-++⁺ˡ i)) , inj₂ ]′ (wh y (λ o → nq (owes-up ne o)) r)

      od′ : OuterDone (aft p) E d
      od′ = (λ t → let (c′ , y , n′) = proj₁ od t in c′ , y , nm n′)
          , (λ y n′ → proj₂ od y (λ o → n′ (owes-up (λ { refl → end-out (InvAt.func io row y) }) o)))
        where
          end-out : ∀ {b} → out b ≡ end → _
          end-out ()

  -- An unbounded lane's rows: the value's, entered under `p`.
  lane-entered : ∀ {Γ A B} {sc : Scope Γ} {f : A → Obs Timeline Γ B} {E : EmissionSet A} {a p}
               → JInv sc f E → E p (out a) → pendRows (full sc) (f a) (p ++ [ ix 1 ]) ≈ LaneOf (λ a → ⟦ f a ⟧ (full sc)) p a
  lane-entered {sc = sc} {f = f} {a = a} {p = p} ji row =
    record { alike = (λ (x , v) → (x , g x) , v) ⇄ (λ ((x , _) , v) → x , v)
           ; cov = [] , λ x → inj₁ (proj₁ x)
           ; voc = λ x → x , g x }
    where
      I = JInv.fi ji a (p ++ [ ix 1 ]) (ok-step p (ok-in (JInv.ok ji) (InvAt.world (JInv.io ji) row) (InvAt.real (JInv.io ji) row)))
      g : ∀ {y e} → enter (⟦ f a ⟧ (full sc)) (p ++ [ ix 1 ]) y e → _
      g x = world-after (InvAt.world I x) (InvAt.real I x)

  -- A MERGE'S VALUE begins its lane at once.  In a part no live node
  -- reads, the lane is subscribed by none: it settles there, running
  -- nothing.
  merge-start : ∀ {Γ A B} {f : A → Obs Timeline Γ B} {ω d n q ls} {c : Ctx R Γ B} {o a p}
              → SimC Rt ⟨ inOuter (mergeᶠ nothing) f ω d n q ls c , o , rising (nx a) , p ⟩ [] (start c (mergeᶠ nothing) f ω d n q o ls a p)
  merge-start {f = f} {c = c} {a = a} {p = p} {Cr = Cr} (flying (f-outer fr ji jn m so bh) cl (sy , row)) =
    let (Cr′ , i , mv) = opens (mergeᶠ nothing) fr ji jn m so bh sy row (λ nl nh → Past.begun-up p (λ ()) (λ _ → nl) nh)
                           (λ _ wt _ _ → record { st = refl ; ln = lane-entered ji row ; ru = tt ; w[] = proj₁ (proj₂ (proj₂ (proj₂ wt))) tt ; sl′ = tt })
    in subst (After Rt Cr) (sym (start-open {c = c} {op = mergeᶠ nothing} {f = f} {a = a} {p = p} cl)) (Cr′ , aft p , i , mv)
  merge-start (flying (d-outer _ _ _ _) _ ())
  merge-start (adrift fr cl _) = ⊥-elim (subst T cl (dead-closed Rt fr refl))
  merge-start (settled () _ _)

  -- A BOUNDED MERGE'S VALUE: its lane begun while a slot is free, else
  -- queued, absorbed.  Counted (`Census`), the dead lanes are the slots
  -- the live count leaves free: with one free, the lane is freed or has
  -- room; with none, the queue's new head starts at the first owed end.
  rise-outer-bounded : ∀ {Γ A B} {m} {f : A → Obs Timeline Γ B} {ω} {d n q ls} {c : Ctx R Γ B} {o a p k′ sh t}
                     → rise (inOuter (mergeᶠ (just m)) f ω d n q ls c) o (nx a) p ≡ moved k′ sh t
                     → SimC Rt ⟨ inOuter (mergeᶠ (just m)) f ω d n q ls c , o , rising (nx a) , p ⟩ sh k′
  rise-outer-bounded {m = m} {f = f} {ω = ω} {d = d} {n = n} {q = qu} {ls = ls} {c = c} {o = o} {a = a} {p = p} refl {Cr = Cr}
    (flying (f-outer {Rg = Rg} {E = E} fr ji jn@(joined {vs = vs} {ws = ws} bg wt wh od ah ao en li sl) jm so bh) cl (sy , row)) = go (n <ᵇ m) refl
    where
      sc = scopeOf c
      F = λ a → ⟦ f a ⟧ (full sc)
      P = polF (mergeᶠ (just m)) F E
      s = p ++ [ ix 1 ]
      io = JInv.io ji
      open Count (JInv.ok ji) m F (JInv.fi ji) io hiding (P)
      open Bounded m F E using (Sched; Kth; Starts; Sub; room; freed; queued)
      open Values E using (Nth)
      open Nths E using (nth-inj)
      open BoundedI (JInv.ok ji) m F (JInv.fi ji) io using (sub-fun)
      open Past p using (nm; owes-up; behind-up; begun-up; module Book)
      open Book {P = P} {O = E} using (ahead-up; wait-up)

      -- the outer's row at `p` is in what no lane's region holds
      here-o = Sound.rg so row _
      nl : ∀ {q′} → ¬ JRl sc Rg (mergeᶠ (just m)) f E q′ p
      nl r = proj₂ here-o (proj₂ r)

      rl = Lanes.lane-rows sc f ji (mergeᶠ (just m)) li

      nh : ¬ VHot (full sc) p
      nh = λ hv → proj₂ (JInv.ok ji) (vhot-hots (full sc) hv) (InvAt.world io row) (⊑-inside (⊑ʷ-refl p))

      -- the value at `p` is the next after every value begun or waiting
      nth-at : ∀ {vs ws} → Begun sc (JRl sc Rg (mergeᶠ (just m)) f E) (bef p) P E vs ls n → Waiting (bef p) P E vs ws qu
             → Whole (bef p) P E vs ws → Listed E 0 (vs ++ ws) → Nth (length (vs ++ ws)) p a
      nth-at {vs} {ws} bg′ wt′ wh′ L = nth-new L bf wi row
        where
          bf : ∀ {x} → x ∈ vs ++ ws → proj₁ x ≺ p
          bf {x} i = [ (λ j → before p {proj₁ x} (begun-nq bg′ j)) , (λ j → before p {proj₁ x} (proj₁ (proj₂ (proj₁ (proj₂ (proj₂ wt′)) j)))) ]′ (∈-++⁻ vs i)
          wi : ∀ {q′ b} → E q′ (out b) → q′ ≺ p → (q′ , b) ∈ vs ++ ws
          wi y lt = [ ∈-++⁺ˡ , ∈-++⁺ʳ vs ]′ (wh′ y (λ o → o lt) tt)

      okp = ok-step p (ok-in (JInv.ok ji) (InvAt.world io row) (InvAt.real io row))
      I = JInv.fi ji a s okp
      g : ∀ {y e} → enter (F a) s y e → s ≺ y
      g x = world-after (InvAt.world I x) (InvAt.real I x)

      -- A SLOT FREE: the lane opened, with room or freed.
      opening : n < m → ∀ {vs ws} → Begun sc (JRl sc Rg (mergeᶠ (just m)) f E) (bef p) P E vs ls n → Waiting (bef p) P E vs ws qu
              → Whole (bef p) P E vs ws → Slots P (bef p) vs ws n → Opening P vs ws n p a (pendRows (full sc) (f a) s)
      opening lt _ _ _ (_ , _ , inj₂ eq) = ⊥-elim (<-irrefl eq lt)
      opening lt {vs} bg′ wt′ wh′ (L₀ , _ , inj₁ refl) = record { st = N , nth , starts ; ln = ln ; ru = N , a , nth ; w[] = refl ; sl′ = sl′ }
        where
          N = length vs
          L : Listed E 0 vs
          L = subst (Listed E 0) (++-identityʳ vs) L₀
          nth : Nth N p a
          nth = subst (λ k → Nth k p a) (cong length (++-identityʳ vs)) (nth-at bg′ wt′ wh′ L₀)
          census = cen-begun L bg′ (λ x → x) c-nil
          starts : Starts N p (Sched N) s
          starts with N <? m
          ... | yes lt′ = room lt′
          ... | no ge   = freed (≮⇒≥ ge) (freed-k N (proj₂ (proj₂ census)) lt (≮⇒≥ ge) (cen-lo (λ {c′} → before p {c′}) (proj₁ (proj₂ census))))
          back : ∀ {i s′ y e} → Sub i p s′ a → enter (F a) s′ y e → enter (F a) s y e
          back (nj , st′) x with nth-inj nj nth
          ... | refl with sub-fun (nj , st′) (nth , starts)
          ...   | refl , refl , refl = x
          ln : pendRows (full sc) (f a) s ≈ Lane P p a
          ln = record { alike = (λ (x , v) → (N , s , (nth , starts) , x , g x) , v) ⇄ (λ ((_ , _ , sb , x , _) , v) → back sb x , v)
                      ; cov = [] , λ (_ , _ , sb , x , _) → inj₁ (back sb x)
                      ; voc = λ x → N , s , (nth , starts) , x , g x }
          sl′ : Slots P (aft p) (vs ++ (p , a) ∷ []) [] (suc n)
          sl′ = subst (Listed E 0) (sym (++-identityʳ (vs ++ (p , a) ∷ []))) (nths-snoc vs L nth) , lt , inj₁ refl

      go : ∀ b → (n <ᵇ m) ≡ b
         → After Rt Cr (if b then start c (mergeᶠ (just m)) f ω d n qu o ls a p
                        else ⟨ c , flatS (mergeᶠ (just m)) f ω d n (qu ++ [ a ]) o ls , absorbed , p ⟩)
      go true e =
        let (Cr′ , i , mv) = opens (mergeᶠ (just m)) fr ji jn jm so bh sy row (λ nl nh → Past.begun-up p (λ ()) (λ _ → nl) nh) (opening (<ᵇ⇒< n m (subst T (sym e) tt)))
        in subst (After Rt Cr) (sym (start-open {c = c} {op = mergeᶠ (just m)} {f = f} {a = a} {p = p} cl)) (Cr′ , aft p , i , mv)
      go false e = proj₁ lifted , aft p , settled c-abs (proj₁ (proj₂ lifted)) (s-flat ji sy (joined bg↑ wt′ wh↑ od↑ ah′ ao en li sl↑) jm so (behind-up bh))
                 , proj₂ (proj₂ lifted)
        where
          -- NO SLOT FREE: every slot taken, the value queued.
          taken : n ≡ m
          taken = ≤-antisym (proj₁ (proj₂ sl)) (≮⇒≥ (λ lt → subst T e (<⇒<ᵇ lt)))

          lifted = fr-up Rt fr tt (proj₁ here-o)
                     (nr-≈ (proj₂ jm) (nr-tr (join-nr (mergeᶠ (just m)) F rl (λ y → end-at (InvAt.func io row y)) (λ _ _ _ r → nl r)))) nh
            where
              end-at : ∀ {b} → out b ≡ end → _
              end-at ()

          -- no begun lane ends at `p`
          le : ∀ {q′ a′ c′} → (q′ , a′) ∈ vs → Lane P q′ a′ c′ end → p ≡ c′ → ⊥
          le iv lc refl = nl (rl (begun-out bg iv) lc)

          bg↑ = begun-up (λ ()) (λ _ → nl) nh bg
          ah↑ = ahead-up le ah
          wt↑ = wait-up le ah↑ wt

          L₀ = proj₁ sl
          Lv = proj₁ (nths-split vs L₀)
          Lw = proj₂ (nths-split vs L₀)
          nth₀ = nth-at bg wt wh L₀
          N′ = length vs + length ws
          nth′ : Nth N′ p a
          nth′ = subst (λ k → Nth k p a) (length-++ vs) nth₀

          -- the lanes counted at `aft p`: the begun, then the waiting
          cv = cen-begun Lv bg↑ (λ x → x) c-nil
          d′ = proj₁ cv
          cs-v = proj₁ (proj₂ cv)
          dm : d′ + m ≡ length vs
          dm = subst (λ k → d′ + k ≡ length vs) taken (proj₂ (proj₂ cv))
          cs-a : Census (aft p) vs N′ d′
          cs-a = cen-wait Lw (λ x → x) ah↑ cs-v
          m≤v : m ≤ length vs
          m≤v = subst (m ≤_) dm (m≤n+m m d′)
          d≤ : d′ ≤ N′ ∸ m
          d≤ = m+n≤o⇒m≤o∸n d′ (subst (_≤ N′) (sym dm) (m≤m+n (length vs) (length ws)))

          -- a queued lane starts past `p`
          owe-start : ∀ {s′} → Start P p a s′ → p ≺ s′
          owe-start (_ , _ , room _)                  = ≺-ext p []
          owe-start (_ , _ , freed _ _)               = ≺-ext p []
          owe-start (_ , _ , queued {c₀} _ pc _ _ _) = ≺-trans {p} {c₀} pc (≺-ext c₀ [])

          wf′ : ∀ {q′ a′} → (q′ , a′) ∈ ws ++ (p , a) ∷ [] → E q′ (out a′) × ¬ Owes (aft p) q′ × Runs P q′ × (∀ {s′} → Start P q′ a′ s′ → Owes (aft p) s′)
          wf′ iw with ∈-++⁻ ws iw
          ... | inj₁ i           = proj₁ (proj₂ (proj₂ wt↑)) i
          ... | inj₂ (here refl) = row , ≺-irrefl {p} , (N′ , a , nth′) , owe-start

          -- the new head, alone: it starts at the first owed end
          new-head : Nth (length vs) p a → Head (aft p) P vs ((p , a) ∷ [])
          new-head nv {c₀} (q′ , a′ , iv , lc , _ , oc) least = length vs , nv , queued m≤v oc kin kle nkl
            where
              kin = let (j , nj , jlt) = nths-∈ Lv iv in kth-in (length vs) jlt (lane-ends nj lc)
              dv : length vs ∸ m ≡ d′
              dv = trans (cong (_∸ m) (sym dm)) (m+n∸n≡m d′ m)
              kle = subst (Kth (_≼ c₀) (Sched (length vs))) (sym dv)
                      (kth-add′ (length vs) kin (cen-lo (λ {c″} nc → ≼-≺-≺ {c″} {p} {c₀} nc oc) cs-v))
              nkl = subst (λ k → ¬ Kth (_≺ c₀) (Sched (length vs)) k) (sym dv)
                      (cen-hi (λ {c′} {c″} oe′ le′ lt′ → ≼-trans {c₀} {c′} {c″} (least oe′) le′ lt′) cs-v)

          head-snoc : ∀ ws′ → Nth (length vs + length ws′) p a → Head (aft p) P vs ws′ → Head (aft p) P vs (ws′ ++ (p , a) ∷ [])
          head-snoc []      nv _ = new-head (subst (λ k → Nth k p a) (+-identityʳ (length vs)) nv)
          head-snoc (_ ∷ _) _  h = h

          wt′ : Waiting (aft p) P E vs (ws ++ (p , a) ∷ []) (qu ++ [ a ])
          wt′ = trans (map-++ proj₂ ws ((p , a) ∷ [])) (cong (_++ [ a ]) (proj₁ wt↑))
              , pairs-++⁺ (proj₁ (proj₂ wt↑)) ([]ᴬ ∷ᴾ []ᴾ) (tabulate λ {x} i → before p {proj₁ x} (proj₁ (proj₂ (proj₁ (proj₂ (proj₂ wt)) i))) ∷ᴬ []ᴬ)
              , wf′ , (λ ()) , head-snoc ws nth′ (proj₂ (proj₂ (proj₂ (proj₂ wt↑))))

          wh↑ : Whole (aft p) P E vs (ws ++ (p , a) ∷ [])
          wh↑ {q′} y nq r with p ≟ᵖ q′
          ... | yes refl with InvAt.func io row y
          ...   | refl = inj₂ (∈-++⁺ʳ ws (here refl))
          wh↑ {q′} y nq r | no ne = [ inj₁ , (λ i → inj₂ (∈-++⁺ˡ i)) ]′ (wh y (λ o → nq (owes-up ne o)) r)

          od↑ : OuterDone (aft p) E d
          od↑ = (λ t → let (c′ , y , n′) = proj₁ od t in c′ , y , nm n′)
              , (λ y n′ → proj₂ od y (λ o → n′ (owes-up (λ { refl → end-out (InvAt.func io row y) }) o)))
            where
              end-out : ∀ {b} → out b ≡ end → _
              end-out ()

          -- the new value's lane starts past an owed end: not with room,
          -- not freed, so queued past one
          from-start : ∀ {s′} → Starts N′ p (Sched N′) s′
                     → Σ Pos λ q′ → Σ _ λ a′ → Σ Pos λ c′ → (q′ , a′) ∈ vs × Lane P q′ a′ c′ end × (∀ {q″} → Kill P q′ q″ → c′ ≼ q″) × Owes (aft p) c′ × c′ ≺ s′
          from-start (room lt)  = ⊥-elim (<-irrefl refl (<-≤-trans lt (≤-trans m≤v (m≤m+n (length vs) (length ws)))))
          from-start (freed _ K) =
            ⊥-elim (cen-hi (λ {c′} {c″} (_ , _ , _ , _ , _ , oc) le′ lt′ → ≺-absurd {p} {c′} oc (≼-≺-≺ {c′} {c″} {p} le′ lt′)) cs-a (kth-le (Sched N′) d≤ K))
          from-start (queued {c₀} _ _ _ K _) =
            let (c″ , c′ , (q′ , a′ , iv , lc , kc , oc) , le′ , le₀) = cen-find {Q = _≼ c₀} cs-a (kth-le (Sched N′) d≤ K)
            in q′ , a′ , c′ , iv , lc , (λ {q″} → kc {q″}) , oc , ≼-≺-≺ {c′} {c₀} {c₀ ++ [ ix 1 ]} (≼-trans {c′} {c″} {c₀} le′ le₀) (≺-ext c₀ [])

          ah′ : Ahead (aft p) P vs (ws ++ (p , a) ∷ [])
          ah′ iw st′ with ∈-++⁻ ws iw
          ... | inj₁ i = ah↑ i st′
          ah′ _ (j , nj , st′) | inj₂ (here refl) with nth-inj nj nth′
          ...   | refl = from-start st′

          sl↑ : Slots P (aft p) vs (ws ++ (p , a) ∷ []) n
          sl↑ = subst (Listed E 0) (++-assoc vs ws ((p , a) ∷ [])) (nths-snoc (vs ++ ws) L₀ nth₀) , proj₁ (proj₂ sl) , inj₂ taken
  rise-outer-bounded refl (adrift fr cl _) = ⊥-elim (subst T cl (dead-closed Rt fr refl))

  -- A SWITCH'S VALUE: every begun lane killed by it, the value's begun.
  rise-outer-switch : ∀ {Γ A B} {f : A → Obs Timeline Γ B} {ω} {d n q ls} {c : Ctx R Γ B} {o a p k′ sh t}
                    → rise (inOuter switchᶠ f ω d n q ls c) o (nx a) p ≡ moved k′ sh t
                    → SimC Rt ⟨ inOuter switchᶠ f ω d n q ls c , o , rising (nx a) , p ⟩ sh k′
  rise-outer-switch {f = f} {c = c} {a = a} {p = p} refl {Cr = Cr} (flying (f-outer fr ji jn m so bh) cl (sy , row)) =
    let (Cr′ , i , mv) = opens switchᶠ fr ji jn m so bh sy row (λ nl nh → Kills.kill-begun p {F = λ a → ⟦ f a ⟧ (full (scopeOf c))} row (λ _ → nl) nh)
                           (λ _ wt _ _ → record { st = refl ; ln = lane-entered ji row ; ru = tt ; w[] = proj₁ (proj₂ (proj₂ (proj₂ wt))) tt ; sl′ = tt })
    in subst (After Rt Cr) (sym (start-open {c = c} {op = switchᶠ} {f = f} {a = a} {p = p} cl)) (Cr′ , aft p , i , mv)
  rise-outer-switch refl (flying (d-outer _ _ _ _) _ ())
  rise-outer-switch refl (adrift fr cl _) = ⊥-elim (subst T cl (dead-closed Rt fr refl))
  rise-outer-switch refl (settled () _ _)

  -- AN EXHAUST'S LANE OPENED, none running: the value at `p` runs its
  -- own lane, next after the last value passed, every lane begun ended
  -- before it.
  module ExOpen {Γ A B} {sc : Scope Γ} {f : A → Obs Timeline Γ B} {E : EmissionSet A} (ji : JInv sc f E) {p a} (row : E p (out a)) where
    F = λ a → ⟦ f a ⟧ (full sc)
    P = polF exhaustᶠ F E
    open Exhaust F E using (cur₀; run) renaming (Cur to XCur)

    opening : ∀ {Rl vs ws ls qu} → Begun sc Rl (bef p) P E vs ls 0 → Waiting (bef p) P E vs ws qu → Whole (bef p) P E vs ws → Slots P (bef p) vs ws 0
            → Opening P vs ws 0 p a (pendRows (full sc) (f a) (p ++ [ ix 1 ]))
    opening {vs = vs} {ws = ws} bg wt _ sl = record { st = refl ; ln = lane-entered ji row ; ru = ru sl ; w[] = proj₁ (proj₂ (proj₂ (proj₂ wt))) tt
                                          ; sl′ = inj₂ (p , vs , p , a , refl , (a , row) , ≺-irrefl {p} , (λ _ nk → nk) , ru sl , ended) }
      where
        ended : ∀ {q′ a′} → (q′ , a′) ∈ vs → Σ Pos λ c → LaneOf F q′ a′ c end × c ≺ p
        ended i with dead-ends bg refl i
        ... | inj₁ (c , lc , nc) = c , lc , before p {c} nc
        ... | inj₂ (_ , () , _)
        ru : Slots P (bef p) vs ws 0 → XCur p p
        ru (inj₁ (_ , allo)) = cur₀ row allo
        ru (inj₂ (x , us , q , aq , refl , (_ , xv) , nx′ , lt , cu , _)) =
          let (c , lc , cp) = ended (∈-++⁺ʳ us (here refl))
          in run cu (begun-out bg (∈-++⁺ʳ us (here refl))) lc cp row (before p {x} nx′)
                 (λ {k} y xk → [ (λ pk → pk) , (λ kp → ⊥-elim (lt y (λ pk → pk kp) xk)) ]′ (≼-or-≻ p k))

  -- AN EXHAUST'S VALUE: its lane begun while none runs, else dropped.
  -- The slots hold the last value passed and the lane it last ran: with
  -- none running the value runs its own; with one running, that lane
  -- the last begun, the value is dropped, that lane unended at it.
  rise-outer-exhaust : ∀ {Γ A B} {f : A → Obs Timeline Γ B} {ω} {d n q ls} {c : Ctx R Γ B} {o a p k′ sh t}
                     → rise (inOuter exhaustᶠ f ω d n q ls c) o (nx a) p ≡ moved k′ sh t
                     → SimC Rt ⟨ inOuter exhaustᶠ f ω d n q ls c , o , rising (nx a) , p ⟩ sh k′
  rise-outer-exhaust {f = f} {n = zero} {c = c} {a = a} {p = p} refl {Cr = Cr} (flying (f-outer fr ji jn m so bh) cl (sy , row)) =
    let (Cr′ , i , mv) = opens exhaustᶠ fr ji jn m so bh sy row (λ nl nh → Past.begun-up p (λ ()) (λ _ → nl) nh) (ExOpen.opening ji row)
    in subst (After Rt Cr) (sym (start-open {c = c} {op = exhaustᶠ} {f = f} {a = a} {p = p} cl)) (Cr′ , aft p , i , mv)
  rise-outer-exhaust {n = suc k} refl (flying (f-outer fr ji (joined () _ _ _ _ _ _ _ (inj₁ (refl , _))) _ _ _) _ _)
  rise-outer-exhaust {f = f} {ω = ω} {d = d} {n = suc k} {q = qu} {ls = ls} {c = c} {o = o} {a = a} {p = p} refl {Cr = Cr}
    (flying (f-outer {Rg = Rg} {E = E} fr ji (joined {ws = ws} bg wt wh od ah ao en li (inj₂ (x , us , q , aq , refl , (_ , xv) , nx′ , lt , cu , ue)))
                     jm so bh) cl (sy , row)) =
    proj₁ lifted , aft p , settled c-abs (proj₁ (proj₂ lifted)) (s-flat ji sy (joined bg↑ wt↑ wh↑ od↑ ah↑ ao en li sl↑) jm so (behind-up bh)) , proj₂ (proj₂ lifted)
    where
      sc = scopeOf c
      F = λ a → ⟦ f a ⟧ (full sc)
      P = polF exhaustᶠ F E
      vs = us ++ (q , aq) ∷ []
      io = JInv.io ji
      open Exhaust F E using (cur₀; run; drop) renaming (Cur to XCur)
      open Values E using (Next)
      open ExCur F E (InvAt.func io) using (cur-val; next-fun; cur-fun)
      open Past p using (nm; owes-up; behind-up; begun-up; module Book)
      open Book {P = P} {O = E} using (ahead-up; wait-up)

      here-o = Sound.rg so row _
      nl : ∀ {q′} → ¬ JRl sc Rg exhaustᶠ f E q′ p
      nl r = proj₂ here-o (proj₂ r)
      rl = Lanes.lane-rows sc f ji exhaustᶠ li
      nh : ¬ VHot (full sc) p
      nh = λ hv → proj₂ (JInv.ok ji) (vhot-hots (full sc) hv) (InvAt.world io row) (⊑-inside (⊑ʷ-refl p))

      lifted = fr-up Rt fr tt (proj₁ here-o)
                 (nr-≈ (proj₂ jm) (nr-tr (join-nr exhaustᶠ F rl (λ y → end-at (InvAt.func io row y)) (λ _ _ _ r → nl r)))) nh
        where
          end-at : ∀ {b} → out b ≡ end → _
          end-at ()

      -- the lane last begun runs, unended at `p`: every one before it
      -- ended before it
      iq = ∈-++⁺ʳ us (here refl)
      oq = begun-out bg iq
      q≺p = before p {q} (begun-nq bg iq)
      live : Unended (bef p) P q aq
      live with live-of bg (λ ())
      ... | q₀ , a₀ , i , _ , u with ∈-++⁻ us i
      ...   | inj₂ (here refl) = u
      ...   | inj₁ j = let (c₀ , lc , cq) = ue j in ⊥-elim (u lc (λ {q′} ()) (≺-trans {c₀} {q} {p} cq q≺p))

      x≺p = before p {x} nx′
      nxt : Next x p
      nxt {k} y xk = [ (λ pk → pk) , (λ kp → ⊥-elim (lt y (λ pk → pk kp) xk)) ]′ (≼-or-≻ p k)

      -- the value at `p` does not run: the last value passed, `x`, is
      -- next before it, and its lane is the one still running
      no-run : ¬ XCur p p
      no-run (cur₀ _ least) = least xv x≺p
      no-run (drop cu′ _ _ _ lt′ _) = Join.ExhaustJ.cur-le [] cu′ lt′
      no-run (run cu′ oq′ lc cp _ lt′ n′) with next-fun (proj₂ (cur-val cu′)) xv lt′ x≺p n′ nxt
      ... | refl with cur-fun cu′ cu
      ...   | refl with InvAt.func io oq′ oq
      ...     | refl = live lc (λ {q′} ()) cp

      le : ∀ {q′ a′ c′} → (q′ , a′) ∈ vs → Lane P q′ a′ c′ end → p ≡ c′ → ⊥
      le iv lc refl = nl (rl (begun-out bg iv) lc)

      bg↑ = begun-up (λ ()) (λ _ → nl) nh bg
      ah↑ = ahead-up le ah
      wt↑ = wait-up le ah↑ wt

      wh↑ : Whole (aft p) P E vs ws
      wh↑ {q′} y nq r with p ≟ᵖ q′
      ... | yes refl = ⊥-elim (no-run r)
      ... | no ne = wh y (λ o → nq (owes-up ne o)) r

      od↑ : OuterDone (aft p) E d
      od↑ = (λ t → let (c′ , y , n′) = proj₁ od t in c′ , y , nm n′)
          , (λ y n′ → proj₂ od y (λ o → n′ (owes-up (λ { refl → end-out (InvAt.func io row y) }) o)))
        where
          end-out : ∀ {b} → out b ≡ end → _
          end-out ()

      sl↑ : Slots P (aft p) vs ws (suc k)
      sl↑ = inj₂ (p , us , q , aq , refl , (a , row) , ≺-irrefl {p} , (λ _ nk → nk) , drop cu oq (λ lc → live lc (λ {q′} ())) row x≺p nxt , ue)
  rise-outer-exhaust _ (flying (d-outer _ _ _ _) _ ())
  rise-outer-exhaust _ (adrift fr cl _) = ⊥-elim (subst T cl (dead-closed Rt fr refl))
  rise-outer-exhaust _ (settled () _ _)

  rise-outer-nx : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {ω} {d n q ls} {c : Ctx R Γ B} {o a p k′ sh t}
                → rise (inOuter op f ω d n q ls c) o (nx a) p ≡ moved k′ sh t → SimC Rt ⟨ inOuter op f ω d n q ls c , o , rising (nx a) , p ⟩ sh k′
  rise-outer-nx {op = mergeᶠ nothing}  refl = merge-start
  rise-outer-nx {op = mergeᶠ (just m)} eq   = rise-outer-bounded eq
  rise-outer-nx {op = switchᶠ}         eq   = rise-outer-switch eq
  rise-outer-nx {op = exhaustᶠ}        eq   = rise-outer-exhaust eq
