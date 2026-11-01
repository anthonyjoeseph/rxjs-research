{-# OPTIONS --guardedness #-}

-- STILL STEPS LIGHTEN: a still step weighed, both confs at the clock it
-- starts from, by the step's mode — a climb, a subscribe, a mark run.
module adequacy.Lighten where

open import Data.Bool using (true; false; not; if_then_else_; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; length; _ʳ++_; null)
open import Data.List.Properties using (length-++)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc; pred; _+_; _*_; _≤_; _<_; _<ᵇ_; _≡ᵇ_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤; +-monoˡ-<; +-monoʳ-<; +-mono-<-≤; <-≤-trans; n≤1+n; m≤m+n; m≤n+m; +-identityʳ; +-assoc; +-comm)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Events using (Pos; root; ix; last; <ᵖ-part; <ᵖ-ix; _≟ᵖ_; emit; stall; close; From∞; Frame)
open import denotation.EmissionSet using (enter; ⟦_⟧; _≼_)
open import denotation.Read using (Meets) renaming (cursor to cursorᴿ)
open import operation.PureObservable using (PureObs; module Machine; module Driver; opening; due; Tape; rest; play; ending) renaming (over to overT)
open Machine using (Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    CS; cs; Mode; Conf; ⟨_,_,_,_⟩; plug; load; subscribing; absorbed; rising; nx; cp; closedUp; closed; alive; dirs; unsub; cut; killAll; ended; settle;
                    attAt; attached; free; cpAt; cutAt; overAt; search; found; own; run; unsubIf; ofM; attM; cpM; cutM; bodyM; srcAttM; owedM; joinM; leafM)
open import operation.Key using (Key; at; _<ᴷ_; at-<ᴷ; <ᴷ-trans; <ᴷ-irrefl; clash)
open import adequacy.Rows using (conv; back; module _≃_)
open import adequacy.Weight using (Clock; W; Wᶜ; anc; prefixes; listed; depth; syn; one; isNone; climb; module Weigh)
open import adequacy.Dispatch using (Marked; ofK; attK; conK; joinK; leafK; stopK; cutK; found-mark; found-least; found-plug; cursor)
open import adequacy.Path using (Path; Still; _⇜_)
open import adequacy.Stamped using (frame-ahead; opening-ahead; pend-focus)
open import adequacy.Floor.Keys using (below)
open import adequacy.Floor using (fed-ahead)
open import adequacy.Simulation using (Simulation; module Along)
open import adequacy.Cursor using (settled)
import adequacy.Walk as Walk
open import adequacy.Walk using (due-≈)
open import adequacy.Bound using (bound)
open _≃_ using (from)
open import denotation.Laws.Modulus using (≼-false)

-- A position's first child keyed before its second.
part : ∀ q → at (q ++ [ ix 0 ]) <ᴷ at (q ++ [ ix 1 ]) ≡ true
part q = trans (at-<ᴷ (q ++ [ ix 0 ]) (q ++ [ ix 1 ])) (<ᵖ-part q {ix 0} {ix 1} [] [] refl)

-- A clock a level down at the second child is not before the first.
over : ∀ q → at (q ++ [ ix 1 ]) <ᴷ at (q ++ [ ix 0 ]) ≡ true → ⊥
over q h = clash (<ᴷ-trans (at (q ++ [ ix 1 ])) (at (q ++ [ ix 0 ])) (at (q ++ [ ix 1 ])) h (part q)) (<ᴷ-irrefl (at (q ++ [ ix 1 ])))

postulate
  -- A DEFER'S GUARD IS MET: short of a row a reader meets next, a defer a
  -- run subscribes has its guard row, at or before the row met next.
  defer-guard : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {l q p e}
              → Path (load o) rs ⟨ c , pend (defer l) q , subscribing , q ⟩
              → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
              → Σ _ λ e′ → enter (⟦ o ⟧ []ᴬ) root (q ++ [ ix 0 ]) e′ × (q ++ [ ix 0 ]) ≼ p

  -- A LANE START PASSES ITS GUARD: a rise that subscribes begins a lane a
  -- level down, past the row its outer value, or its freed slot, leaves,
  -- at or before the row met next.
  lane-guard : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s ε q k′ p e}
             → Path (load o) rs ⟨ c , s , rising ε , q ⟩ → k′ ⇜ ⟨ c , s , rising ε , q ⟩ → Conf.mode k′ ≡ subscribing
             → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
             → Σ _ λ e′ → enter (⟦ o ⟧ []ᴬ) root (q ++ [ ix 0 ]) e′ × (q ++ [ ix 0 ]) ≼ p

  -- A SOURCE'S STEP IS ECHOED: a source rising under its connect leaves the
  -- connect's row a level down, at or before the row met next.
  echo-guard : ∀ {R} (o : PureObs [] R) {rs Γ X B} {k : CS Γ X} {b : St (X ∷ Γ) B} {c : Ctx R Γ B} {s ε q p e}
             → Path (load o) rs ⟨ inSrc k b c , s , rising ε , q ⟩
             → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
             → Σ _ λ e′ → enter (⟦ o ⟧ []ᴬ) root (q ++ [ ix 0 ]) e′ × (q ++ [ ix 0 ]) ≼ p

  -- A COLD'S TICK IS A ROW: short of a row a reader meets next, a cold an
  -- open observer hears plays its due at a row at or before it, or at an
  -- ancestor of one.
  tick-row : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s q p e Γ′ A′} {c′ : Ctx R Γ′ A′} {b τ u i t} {fr : Frame A′ t}
           → Path (load o) rs ⟨ c , s , absorbed , q ⟩
           → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
           → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , coldS b (play τ u i t fr)) leafM (at (u ++ [ ix i ])))
           → closed c′ ≡ false
           → Σ Pos λ r → Σ _ λ e′ → enter (⟦ o ⟧ []ᴬ) root r e′ × r ≼ p × (u ++ [ ix i ]) ∈ prefixes r


-- THE LEAST MARK IS NOT PAST THE ROW: short of a row a reader meets
-- next, the least mark a run finds, keyed at a position, is keyed at or
-- before it.
mark-short : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s q p e Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ mk u}
           → Path (load o) rs ⟨ c , s , absorbed , q ⟩
           → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
           → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , s′) mk (at u)) → at p <ᴷ at u ≡ false
mark-short {R} o {rs} {c = c} {s} {p = p} {u = u} pth m fd
  with Along.along (cursor o) nothing pth (Simulation.i₀ (cursor o)) (Simulation.t₀ (cursor o))
     | Along.met-next (cursor o) {c = nothing} (conv rs) m
... | (C , settled _ fr h) , r | ((tp , _) , _) , vi , ap , _ with Walk.climb (enter (⟦ o ⟧ []ᴬ) root) fr h
...   | _ , _ , eq , sy =
  trans (at-<ᴷ p u)
    (≼-false {u} {p} (bound sy (λ ()) (proj₂ (found-least {t = plug c s} fd))
      (from (due-≈ {C = C} eq) (proj₁ (from r (back (cursorᴿ nothing (conv rs)) tp ap , vi))))))

private
  conn-arith : ∀ w e x y → w ≤ e → suc ((((w + suc e) + 0) + 0 + e) + x + y) ≤ 2 + 3 * e + y + x
  conn-arith w e x y h =
    ≤-trans (s≤s (+-monoˡ-≤ y (+-monoˡ-≤ x (+-monoˡ-≤ e (+-monoˡ-≤ 0 (+-monoˡ-≤ 0 (+-monoˡ-≤ (suc e) h)))))))
            (≤-reflexive (eq e x y))
    where eq : ∀ e x y → suc ((((e + suc e) + 0) + 0 + e) + x + y) ≡ 2 + 3 * e + y + x
          eq = solve-∀

  take-arith : ∀ a b y → suc (a + (b + y)) ≤ 1 + a + b + y
  take-arith a b y = ≤-reflexive (eq a b y)
    where eq : ∀ a b y → suc (a + (b + y)) ≡ 1 + a + b + y
          eq = solve-∀

  flat-arith : ∀ b y → suc ((b + y) + 0) ≤ 1 + b + y
  flat-arith b y = ≤-reflexive (eq b y)
    where eq : ∀ b y → suc ((b + y) + 0) ≡ 1 + b + y
          eq = solve-∀


module Begun {R} (o : PureObs [] R) {rs p e} (m : Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ]))
             (ks : List Pos) (cov : ∀ {q′ e′} → enter (⟦ o ⟧ []ᴬ) root q′ e′ → q′ ≼ p → q′ ∈ ks)
             {Γ A} (c : Ctx R Γ A) (q : Pos) where
  private
    L = ks ++ anc ks
    open Weigh L p (at q)
    D = depth c

    -- An of's marks, each strictly past where it was subscribed.
    ofW-ahead : ∀ {X : Set} i (xs : List X) → ofW D i q xs ≤ length xs * (2 + D) + (2 + D)
    ofW-ahead i []       = wt-ahead D (at (q ++ [ last ])) (below q)
    ofW-ahead i (_ ∷ xs) =
      ≤-trans (+-mono-≤ (wt-ahead D (at (q ++ [ ix i ])) (below q)) (ofW-ahead (suc i) xs)) (≤-reflexive (asc (2 + D) (length xs * (2 + D)) (2 + D)))
      where asc : ∀ a b c → a + (b + c) ≡ (a + b) + c
            asc = solve-∀

    of-lt : ∀ {X : Set} (xs : List X) → ofW D 0 q xs < 3 + D + length xs * (2 + D)
    of-lt xs = ≤-trans (s≤s (ofW-ahead 0 xs)) (≤-reflexive (eq (length xs * (2 + D)) D))
      where eq : ∀ n d → suc (n + (2 + d)) ≡ 3 + d + n
            eq = solve-∀

    lt0 : ∀ {a b} → a < b → a + 0 < b + 0
    lt0 lt = +-monoˡ-< 0 lt

    cold-lt : ∀ {X : Set} (l : Tape X) → (∀ {κ} → due l ≡ just κ → at q <ᴷ κ ≡ true) → pot {Γ} D (coldS true l) < 3 + D
    cold-lt l h with due l
    ... | just κ  = s≤s (wt-ahead D κ (h refl))
    ... | nothing = s≤s z≤n

  begun : ∀ (o′ : PureObs Γ A) {τ k′} → Path (load o) rs ⟨ c , pend o′ q , subscribing , q ⟩
        → Driver.step R ⟨ c , pend o′ q , subscribing , q ⟩ ≡ Driver.silent τ k′
        → (∀ {q′} → q′ ∈ L → at q <ᴷ at q′ ≡ true → Clock k′ <ᴷ at q′ ≡ true)
        → Wᶜ L p (at q) k′ < Wᶜ L p (at q) ⟨ c , pend o′ q , subscribing , q ⟩
  begun (map f s′)         pth refl _ = lt0 (lighter-at c ≤-refl)
  begun (scan f z s′)      pth refl _ = lt0 (lighter-at c ≤-refl)
  begun (takeWhile i f s′) pth refl _ = lt0 (lighter-at c (take-arith (2 * (2 + D)) (3 + D) (syn (2 + D) s′)))
  begun (flatMap op f s′)  pth refl _ = lt0 (lighter-at c (flat-arith (3 + D) (syn (2 + D) s′)))
  begun (connect s′ b)     pth refl _ =
    lt0 (lighter-at c (conn-arith _ (2 + D) (syn (suc D) s′) (syn (suc D) b) (wt-ahead D (at (q ++ [ ix 1 ])) (below q))))
  begun (defer l)          pth refl kept =
    let (_ , tq , le) = defer-guard o pth m
    in ⊥-elim (over q (kept (∈-++⁺ˡ (cov tq le)) (below q)))
  begun (cold x)           pth refl _ = lt0 (lighter-at c (cold-lt _ (opening-ahead o pth)))
  begun empty              pth refl _ = lt0 (lighter-at c (s≤s (wt-ahead D (at (q ++ [ last ])) (below q))))
  begun (of xs)            pth refl _ = lt0 (lighter-at c (of-lt xs))
  begun (connected x)      pth eq   _ with closedUp c x
  begun (connected x)      pth refl _ | true  = lt0 (lighter-at c (s≤s (wt-ahead D (at (q ++ [ last ])) (below q))))
  begun (connected x)      pth refl _ | false = lt0 (lighter-at c (s≤s z≤n))

-- A STILL SUBSCRIBE LIGHTENS: a subscribe trades its syntax for what it
-- leaves — its source pending a level down, or the marks it owes, each
-- strictly past where it was made; a defer passes its guard row, so is
-- never still.
lightens-begin : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s q k′ p e}
               → Path (load o) rs ⟨ c , s , subscribing , q ⟩
               → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
               → ∀ ks → (∀ {q′ e′} → enter (⟦ o ⟧ []ᴬ) root q′ e′ → q′ ≼ p → q′ ∈ ks)
               → Still (ks ++ anc ks) k′ ⟨ c , s , subscribing , q ⟩
               → Wᶜ (ks ++ anc ks) p (at q) k′ < Wᶜ (ks ++ anc ks) p (at q) ⟨ c , s , subscribing , q ⟩
lightens-begin o {c = c} {q = q} pth m ks cov ((τ , eq) , kept) with pend-focus o pth
... | o′ , refl = Begun.begun o m ks cov c q o′ pth eq kept

-- AN UNSUBSCRIBE SHEDS: tearing a tree down leaves it no heavier.
module Shed (ks : List Pos) (P : Pos) (C : Key) where
  open Weigh ks P C

  take-le : ∀ {Γ A} d {i q} w {s s′ : St Γ A} → pot (suc d) s′ ≤ pot (suc d) s → pot d (takeS i q w s′) ≤ pot d (takeS i q w s)
  take-le d free       h = +-monoʳ-≤ (2 * (2 + d)) h
  take-le d (cpAt r)   h = +-monoʳ-≤ (wt d (at (r ++ [ last ])) + (2 + d)) h
  take-le d (cutAt r)  h = +-monoʳ-≤ (2 + d) h
  take-le d (overAt r) h = h

  mutual
    unsub-le : ∀ {Γ A} d (s : St Γ A) → pot d (proj₁ (unsub s)) ≤ pot d s
    unsub-le d (pend o q)              = ≤-refl
    unsub-le d (coldS true l) with due l
    ... | just _                       = ≤-refl
    ... | nothing                      = ≤-refl
    unsub-le d (coldS false l)         = ≤-refl
    unsub-le d (ofS i q xs)            = ≤-refl
    unsub-le d doneS                   = ≤-refl
    unsub-le d (mapS f s)              = unsub-le (suc d) s
    unsub-le d (scanS f z s)           = unsub-le (suc d) s
    unsub-le d (cutS l a s)            = ≤-refl
    unsub-le d (lnS b s)               = ≤-refl
    unsub-le d (takeS i q w s)         = take-le d w (cut-le (suc d) s)
    unsub-le d (flatS op f b n q o ls) = +-mono-≤ (cut-le (suc d) o) (kill-le (suc d) ls)
    unsub-le d (connS k o b)           = +-mono-≤ (+-monoʳ-≤ (connW d k) (unsub-le (suc d) o)) (unsub-le (suc d) b)
    unsub-le d (joinS j g x ib)        = z≤n

    cut-le : ∀ {Γ A} d (s : St Γ A) → pot d (proj₁ (cut s)) ≤ pot d s
    cut-le d (cutS l attached s)  = unsub-le (suc d) s
    cut-le d (cutS l (attAt q) s) = ≤-refl
    cut-le d (pend o q)           = ≤-refl
    cut-le d (coldS b l)          = ≤-refl
    cut-le d (ofS i q xs)         = ≤-refl
    cut-le d doneS                = ≤-refl
    cut-le d (mapS f s)           = ≤-refl
    cut-le d (scanS f z s)        = ≤-refl
    cut-le d (lnS b s)            = ≤-refl
    cut-le d (takeS i q w s)      = ≤-refl
    cut-le d (flatS op f b n q o ls) = ≤-refl
    cut-le d (connS k o b)        = ≤-refl
    cut-le d (joinS j g x ib)     = ≤-refl

    kill-le : ∀ {Γ A} d (ls : List (St Γ A)) → potL d (proj₁ (killAll ls)) ≤ potL d ls
    kill-le d []                         = z≤n
    kill-le d (lnS true s ∷ ls)          = +-mono-≤ (cut-le (suc d) s) (kill-le d ls)
    kill-le d (lnS false s ∷ ls)         = keep d (lnS false s) ls
    kill-le d (pend o q ∷ ls)            = keep d (pend o q) ls
    kill-le d (coldS b l ∷ ls)           = keep d (coldS b l) ls
    kill-le d (ofS i q xs ∷ ls)          = keep d (ofS i q xs) ls
    kill-le d (doneS ∷ ls)               = keep d (doneS) ls
    kill-le d (mapS f s ∷ ls)            = keep d (mapS f s) ls
    kill-le d (scanS f z s ∷ ls)         = keep d (scanS f z s) ls
    kill-le d (cutS l a s ∷ ls)          = keep d (cutS l a s) ls
    kill-le d (takeS i q w s ∷ ls)       = keep d (takeS i q w s) ls
    kill-le d (flatS op f b n q o ms ∷ ls) = keep d (flatS op f b n q o ms) ls
    kill-le d (connS k o b ∷ ls)         = keep d (connS k o b) ls
    kill-le d (joinS j g x ib ∷ ls)      = keep d (joinS j g x ib) ls

    keep : ∀ {Γ A} d (l : St Γ A) (ls : List (St Γ A)) → pot d l + potL d (proj₁ (killAll ls)) ≤ pot d l + potL d ls
    keep d l ls = +-monoʳ-≤ (pot d l) (kill-le d ls)

  -- A lane ended weighs as it did.
  ended-le : ∀ {Γ A} d (s : St Γ A) → pot d (ended s) ≤ pot d s
  ended-le d (lnS b (cutS l (attAt r) s)) = ≤-refl
  ended-le d (lnS b (cutS l attached s))  = ≤-refl
  ended-le d (lnS b (pend o q))           = ≤-refl
  ended-le d (lnS b (coldS b′ l))         = ≤-refl
  ended-le d (lnS b (ofS i q xs))         = ≤-refl
  ended-le d (lnS b doneS)                = ≤-refl
  ended-le d (lnS b (mapS f s))           = ≤-refl
  ended-le d (lnS b (scanS f z s))        = ≤-refl
  ended-le d (lnS b (lnS b′ s))           = ≤-refl
  ended-le d (lnS b (takeS i q w s))      = ≤-refl
  ended-le d (lnS b (flatS op f b′ n q o ls)) = ≤-refl
  ended-le d (lnS b (connS k o s))        = ≤-refl
  ended-le d (lnS b (joinS j g x ib))     = ≤-refl
  ended-le d (pend o q)                   = ≤-refl
  ended-le d (coldS b l)                  = ≤-refl
  ended-le d (ofS i q xs)                 = ≤-refl
  ended-le d doneS                        = ≤-refl
  ended-le d (mapS f s)                   = ≤-refl
  ended-le d (scanS f z s)                = ≤-refl
  ended-le d (cutS l a s)                 = ≤-refl
  ended-le d (takeS i q w s)              = ≤-refl
  ended-le d (flatS op f b n q o ls)      = ≤-refl
  ended-le d (connS k o s)                = ≤-refl
  ended-le d (joinS j g x ib)             = ≤-refl

  -- A lane ended among its siblings.
  lanes-le : ∀ {Γ A B} d (o : St Γ A) (pre post : List (St Γ B)) s
           → pot (suc d) o + potL (suc d) (pre ʳ++ ended s ∷ post) ≤ pot (suc d) o + potL (suc d) (pre ʳ++ s ∷ post)
  lanes-le d o pre post s rewrite potL-ʳ++ (suc d) pre (ended s ∷ post) | potL-ʳ++ (suc d) pre (s ∷ post) =
    +-monoʳ-≤ (pot (suc d) o) (+-monoʳ-≤ (potL (suc d) pre) (+-monoˡ-≤ (potL (suc d) post) (ended-le (suc d) s)))

  -- A live connect's body ending: its end owed in place of its teardown.
  owe-le : ∀ {Γ X} d cl sa ba as ow ca ea sr sc r
         → connW d (cs {Γ} {X} cl true sa ba as (just r) ca ea sr sc) ≤ connW d (cs cl true sa ba as ow ca ea sr sc)
  owe-le d cl sa ba as (just _) ca ea sr sc r = ≤-refl
  owe-le d cl sa ba as nothing  ca ea sr sc r = ≤-reflexive (sw (bodyP d ba + one d (not (isNone as))) (2 + d))
    where sw : ∀ a b → a + b + 0 ≡ a + 0 + b
          sw = solve-∀

-- What a conf still climbs is at most its context's height.
climb-le : ∀ {R Γ A} {c : Ctx R Γ A} {s} (md : Mode A) {q} → climb ⟨ c , s , md , q ⟩ ≤ length (dirs c)
climb-le (rising _)  = ≤-refl
climb-le subscribing = z≤n
climb-le absorbed    = z≤n

module Rose {R} (o : PureObs [] R) {rs p e} (m : Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ]))
            (ks : List Pos) (cov : ∀ {q′ e′} → enter (⟦ o ⟧ []ᴬ) root q′ e′ → q′ ≼ p → q′ ∈ ks)
            (q : Pos) where
  private
    L = ks ++ anc ks
    open Weigh L p (at q)
    open Shed L p (at q)

    Guard : Set
    Guard = Σ _ λ e′ → enter (⟦ o ⟧ []ᴬ) root (q ++ [ ix 0 ]) e′ × (q ++ [ ix 0 ]) ≼ p

    Kept : Conf R → Set
    Kept k′ = ∀ {q′} → q′ ∈ L → at q <ᴷ at q′ ≡ true → Clock k′ <ᴷ at q′ ≡ true

    -- One level up, the hole no heavier: lighter by the climb.
    up : ∀ {Γ A} (c : Ctx R Γ A) x {t t′ : St Γ A} {n}
       → pot (depth c) t′ ≤ pot (depth c) t → n ≤ length (dirs c) → pot 0 (plug c t′) + n < pot 0 (plug c t) + length (dirs c ++ [ x ])
    up c x {t} {t′} h b rewrite pot-plug c t | pot-plug c t′ | length-++ (dirs c) {[ x ]} =
      ≤-trans (s≤s (+-mono-≤ (+-monoʳ-≤ (potC c) h) b)) (≤-reflexive (sh (potC c + pot (depth c) t) (length (dirs c))))
      where sh : ∀ a b → suc (a + b) ≡ a + (b + 1)
            sh = solve-∀

    -- A lane begun has passed its guard.
    begun : (∀ {q′} → q′ ∈ L → at q <ᴷ at q′ ≡ true → at (q ++ [ ix 1 ]) <ᴷ at q′ ≡ true) → Guard → ⊥
    begun kept (_ , tq , le) = over q (kept (∈-++⁺ˡ (cov tq le)) (below q))

    -- A takeWhile's failing value: its end owed past where it fell.
    failed : ∀ {Γ A} {i f} (s : St Γ A) d → pot d (takeS i f (cpAt q) s) ≤ pot d (takeS i f free s)
    failed s d = +-monoˡ-≤ (pot (suc d) s) (≤-trans (+-monoˡ-≤ (2 + d) (wt-ahead d (at (q ++ [ last ])) (below q))) (≤-reflexive (dbl (2 + d))))
      where dbl : ∀ a → a + a ≡ 2 * a
            dbl = solve-∀

  rose : ∀ {Γ A} (c : Ctx R Γ A) s ε {τ k′}
       → Path (load o) rs ⟨ c , s , rising ε , q ⟩ → (Conf.mode k′ ≡ subscribing → Guard)
       → Driver.step R ⟨ c , s , rising ε , q ⟩ ≡ Driver.silent τ k′ → Kept k′
       → Wᶜ L p (at q) k′ < Wᶜ L p (at q) ⟨ c , s , rising ε , q ⟩
  rose top s (nx a) pth g () kept
  rose top s cp     pth g () kept
  rose (inMap f c) s ε pth g refl _ = up c _ ≤-refl ≤-refl
  rose (inScan f z c) s (nx a) pth g refl _ = up c _ ≤-refl ≤-refl
  rose (inScan f z c) s cp     pth g refl _ = up c _ ≤-refl ≤-refl
  rose (inCut true a c) s ε pth g refl _ = up c _ ≤-refl ≤-refl
  rose (inCut false a c) s ε pth g refl _ = up c _ ≤-refl z≤n
  rose (inLn b c) s ε pth g refl _ = up c _ ≤-refl ≤-refl
  rose (inTake i f free c) s (nx a) pth g eq kept with f a | i
  rose (inTake i f free c) s (nx a) pth g refl kept | true  | _     = up c _ ≤-refl ≤-refl
  rose (inTake i f free c) s (nx a) pth g refl kept | false | true  = up c _ (failed {i = i} {f = f} s (depth c)) ≤-refl
  rose (inTake i f free c) s (nx a) pth g refl kept | false | false = up c _ (failed {i = i} {f = f} s (depth c)) z≤n
  rose (inTake i f free c) s cp pth g refl _ = up c _ ≤-refl ≤-refl
  rose (inTake i f (cpAt r) c)  s ε pth g refl _ = up c _ ≤-refl z≤n
  rose (inTake i f (cutAt r) c) s ε pth g refl _ = up c _ ≤-refl z≤n
  rose (inTake i f (overAt r) c) s ε pth g refl _ = up c _ ≤-refl z≤n
  rose (inOuter (mergeᶠ nothing) f d n qs ls c) s (nx a) pth g eq kept with closed c
  rose (inOuter (mergeᶠ nothing) f d n qs ls c) s (nx a) pth g refl kept | true  = up c _ ≤-refl z≤n
  rose (inOuter (mergeᶠ nothing) f d n qs ls c) s (nx a) pth g refl kept | false = ⊥-elim (begun kept (g refl))
  rose (inOuter (mergeᶠ (just mx)) f d n qs ls c) s (nx a) pth g eq kept with n <ᵇ mx
  rose (inOuter (mergeᶠ (just mx)) f d n qs ls c) s (nx a) pth g refl kept | false = up c _ ≤-refl z≤n
  rose (inOuter (mergeᶠ (just mx)) f d n qs ls c) s (nx a) pth g eq kept | true with closed c
  rose (inOuter (mergeᶠ (just mx)) f d n qs ls c) s (nx a) pth g refl kept | true | true  = up c _ ≤-refl z≤n
  rose (inOuter (mergeᶠ (just mx)) f d n qs ls c) s (nx a) pth g refl kept | true | false = ⊥-elim (begun kept (g refl))
  rose (inOuter switchᶠ f d n qs ls c) s (nx a) pth g eq kept with killAll ls | kill-le (suc (depth c)) ls
  rose (inOuter switchᶠ f d n qs ls c) s (nx a) pth g eq kept | ls′ , t | h with closed c
  rose (inOuter switchᶠ f d n qs ls c) s (nx a) pth g refl kept | ls′ , t | h | true  = up c _ (+-monoʳ-≤ (pot (suc (depth c)) s) h) z≤n
  rose (inOuter switchᶠ f d n qs ls c) s (nx a) pth g refl kept | ls′ , t | h | false = ⊥-elim (begun kept (g refl))
  rose (inOuter exhaustᶠ f d n qs ls c) s (nx a) pth g eq kept with n ≡ᵇ 0
  rose (inOuter exhaustᶠ f d n qs ls c) s (nx a) pth g refl kept | false = up c _ ≤-refl z≤n
  rose (inOuter exhaustᶠ f d n qs ls c) s (nx a) pth g eq kept | true with closed c
  rose (inOuter exhaustᶠ f d n qs ls c) s (nx a) pth g refl kept | true | true  = up c _ ≤-refl z≤n
  rose (inOuter exhaustᶠ f d n qs ls c) s (nx a) pth g refl kept | true | false = ⊥-elim (begun kept (g refl))
  rose (inOuter op f d n qs ls c) s cp pth g refl _ = up c _ ≤-refl (climb-le (if d then absorbed else settle true n (null qs)))
  rose (inLanes op f d n qs o′ pre post c) s (nx b) pth g eq kept with alive s
  rose (inLanes op f d n qs o′ pre post c) s (nx b) pth g refl kept | true  = up c _ ≤-refl ≤-refl
  rose (inLanes op f d n qs o′ pre post c) s (nx b) pth g refl kept | false = up c _ ≤-refl z≤n
  rose (inLanes op f d n qs o′ pre post c) s cp pth g eq kept with alive s
  rose (inLanes op f d n qs o′ pre post c) s cp pth g refl kept | false = up c _ ≤-refl z≤n
  rose (inLanes op f d n [] o′ pre post c) s cp pth g refl kept | true = up c _ (lanes-le (depth c) o′ pre post s) (climb-le (settle d (pred n) true))
  rose (inLanes op f d n (a ∷ qs) o′ pre post c) s cp pth g eq kept | true with closed c
  rose (inLanes op f d n (a ∷ qs) o′ pre post c) s cp pth g refl kept | true | true  = up c _ (lanes-le (depth c) o′ pre post s) z≤n
  rose (inLanes op f d n (a ∷ qs) o′ pre post c) s cp pth g refl kept | true | false = ⊥-elim (begun kept (g refl))
  rose (inSrc k b c) s ε pth g eq kept =
    let (_ , tq , le) = echo-guard o pth m
    in ⊥-elim (clash (kept (∈-++⁺ˡ (cov tq le)) (below q)) (fed-ahead o pth (_ , eq)))
  rose (inBody k o′ c) s (nx b) pth g eq kept with CS.srcLive k
  rose (inBody k o′ c) s (nx b) pth g refl kept | true  = up c _ ≤-refl ≤-refl
  rose (inBody k o′ c) s (nx b) pth g refl kept | false = up c _ ≤-refl z≤n
  rose (inBody (cs cl true sa ba as ow ca ea sr sc) o′ c) s cp pth g refl kept =
    up c _ (+-monoˡ-≤ (pot (suc (depth c)) s) (+-monoˡ-≤ (pot (suc (depth c)) o′) (owe-le (depth c) cl sa ba as ow ca ea sr sc q))) ≤-refl
  rose (inBody (cs cl false sa ba as ow ca ea sr sc) o′ c) s cp pth g refl kept = up c _ ≤-refl z≤n

-- A position listed, at its key.
∈-listed : ∀ ks q → q ∈ ks → listed ks (at q) ≡ true
∈-listed (r ∷ ks) q m with q ≟ᵖ r
... | yes _ = refl
... | no ¬e with m
...   | here e   = ⊥-elim (¬e e)
...   | there m′ = ∈-listed ks q m′

-- An ancestor of a listed position, among the ancestors listed.
anc-∈ : ∀ {y r} ks → r ∈ ks → y ∈ prefixes r → y ∈ anc ks
anc-∈ (r ∷ ks) (here refl) my = ∈-++⁺ˡ my
anc-∈ (x ∷ ks) (there mr) my = ∈-++⁺ʳ (prefixes x) (anc-∈ ks mr my)

-- A context's directions, one per level.
snoc-len : ∀ {n} (xs : List ℕ) {x} → length xs ≡ n → length (xs ++ [ x ]) ≡ suc n
snoc-len xs h = trans (length-++ xs) (trans (+-comm _ 1) (cong suc h))

dirs-depth : ∀ {R Γ A} (c : Ctx R Γ A) → length (dirs c) ≡ depth c
dirs-depth top                               = refl
dirs-depth (inMap f c)                       = snoc-len (dirs c) (dirs-depth c)
dirs-depth (inScan f z c)                    = snoc-len (dirs c) (dirs-depth c)
dirs-depth (inCut l a c)                     = snoc-len (dirs c) (dirs-depth c)
dirs-depth (inLn b c)                        = snoc-len (dirs c) (dirs-depth c)
dirs-depth (inTake i f w c)                  = snoc-len (dirs c) (dirs-depth c)
dirs-depth (inOuter op f d n q ls c)         = snoc-len (dirs c) (dirs-depth c)
dirs-depth (inLanes op f d n q o pre post c) = snoc-len (dirs c) (dirs-depth c)
dirs-depth (inSrc k b c)                     = snoc-len (dirs c) (dirs-depth c)
dirs-depth (inBody k o c)                    = snoc-len (dirs c) (dirs-depth c)

-- A connect's own marks, by kind.
own-body : ∀ {Γ X B} (k : CS Γ X) (o : St Γ X) (b : St (X ∷ Γ) B) {κ} → (bodyM , κ) ∈ own (connS k o b) → Σ Pos λ p₀ → CS.bodyAt k ≡ just p₀
own-body (cs _ _ _ (just p₀) _ _ _ _ _ _) o b _ = p₀ , refl
own-body (cs _ _ _ nothing nothing  nothing  _ _ _ _) o b ()
own-body (cs _ _ _ nothing (just _) nothing  _ _ _ _) o b (here ())
own-body (cs _ _ _ nothing (just _) nothing  _ _ _ _) o b (there ())
own-body (cs _ _ _ nothing nothing  (just _) _ _ _ _) o b (here ())
own-body (cs _ _ _ nothing nothing  (just _) _ _ _ _) o b (there ())
own-body (cs _ _ _ nothing (just _) (just _) _ _ _ _) o b (here ())
own-body (cs _ _ _ nothing (just _) (just _) _ _ _ _) o b (there (here ()))
own-body (cs _ _ _ nothing (just _) (just _) _ _ _ _) o b (there (there ()))

own-src : ∀ {Γ X B} (k : CS Γ X) (o : St Γ X) (b : St (X ∷ Γ) B) {κ} → (srcAttM , κ) ∈ own (connS k o b) → Σ Pos λ p₀ → CS.attSrc k ≡ just p₀
own-src (cs _ _ _ _ (just p₀) _ _ _ _ _) o b _ = p₀ , refl
own-src (cs _ _ _ nothing  nothing nothing  _ _ _ _) o b ()
own-src (cs _ _ _ (just _) nothing nothing  _ _ _ _) o b (here ())
own-src (cs _ _ _ (just _) nothing nothing  _ _ _ _) o b (there ())
own-src (cs _ _ _ nothing  nothing (just _) _ _ _ _) o b (here ())
own-src (cs _ _ _ nothing  nothing (just _) _ _ _ _) o b (there ())
own-src (cs _ _ _ (just _) nothing (just _) _ _ _ _) o b (here ())
own-src (cs _ _ _ (just _) nothing (just _) _ _ _ _) o b (there (here ()))
own-src (cs _ _ _ (just _) nothing (just _) _ _ _ _) o b (there (there ()))

own-owed : ∀ {Γ X B} (k : CS Γ X) (o : St Γ X) (b : St (X ∷ Γ) B) {κ} → (owedM , κ) ∈ own (connS k o b) → Σ Pos λ p₀ → CS.owedAt k ≡ just p₀
own-owed (cs _ _ _ _ _ (just p₀) _ _ _ _) o b _ = p₀ , refl
own-owed (cs _ _ _ nothing  nothing  nothing _ _ _ _) o b ()
own-owed (cs _ _ _ (just _) nothing  nothing _ _ _ _) o b (here ())
own-owed (cs _ _ _ (just _) nothing  nothing _ _ _ _) o b (there ())
own-owed (cs _ _ _ nothing  (just _) nothing _ _ _ _) o b (here ())
own-owed (cs _ _ _ nothing  (just _) nothing _ _ _ _) o b (there ())
own-owed (cs _ _ _ (just _) (just _) nothing _ _ _ _) o b (here ())
own-owed (cs _ _ _ (just _) (just _) nothing _ _ _ _) o b (there (here ()))
own-owed (cs _ _ _ (just _) (just _) nothing _ _ _ _) o b (there (there ()))

-- A MARK RUN, WEIGHED AT ITS KEY: the least mark run spends its own
-- weight, and what it leaves weighs less, its climb included.
module Run {R} (o : PureObs [] R) {rs p e} (m : Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ]))
           (ks : List Pos) (cov : ∀ {q′ e′} → enter (⟦ o ⟧ []ᴬ) root q′ e′ → q′ ≼ p → q′ ∈ ks)
           (q : Pos) where
  private
    L = ks ++ anc ks

  module At (κ : Key) where
    open Weigh L p κ
    open Shed L p κ

    -- A mark reached, not past the row: at least an unlisted one's weight.
    reached : ∀ d → at p <ᴷ κ ≡ false → 2 + d ≤ wt d κ
    reached d np with at p <ᴷ κ | np
    ... | true  | ()
    ... | false | _ with listed L κ
    ...   | true rewrite <ᴷ-irrefl κ = ≤-trans (m≤m+n (2 + d) (2 + d)) (≤-reflexive (dbl d))
      where dbl : ∀ d → (2 + d) + (2 + d) ≡ 4 + 2 * d
            dbl = solve-∀
    ...   | false = ≤-refl

    -- A listed mark reached weighs its run.
    full : ∀ d → at p <ᴷ κ ≡ false → listed L κ ≡ true → wt d κ ≡ 4 + 2 * d
    full d np ls with at p <ᴷ κ | np
    ... | true  | ()
    ... | false | _ rewrite ls | <ᴷ-irrefl κ = refl

    -- The mark spent, a climb at most its depth left.
    spend : ∀ d {κ₀ n r} → κ ≡ κ₀ → n ≤ d → at p <ᴷ κ ≡ false → n + r < wt d κ₀ + r
    spend d {r = r} refl h np = +-monoˡ-< r (<-≤-trans (s≤s (≤-trans h (n≤1+n d))) (reached d np))

    spend₀ : ∀ d {κ₀ n} → κ ≡ κ₀ → n ≤ d → at p <ᴷ κ ≡ false → n + 0 < wt d κ₀
    spend₀ d e h np = <-≤-trans (spend d e h np) (≤-reflexive (+-identityʳ _))

    -- A listed tick spent, the cold's next due ahead of it.
    tick : ∀ d {κ₀ n w} → κ ≡ κ₀ → at p <ᴷ κ ≡ false → listed L κ ≡ true → w ≤ 2 + d → n ≤ d → n + w < wt d κ₀
    tick d {n = n} {w} refl np ls hw hn rewrite full d np ls =
      ≤-trans (s≤s (+-mono-≤ hn hw)) (≤-trans (n≤1+n _) (≤-reflexive (eq d)))
      where eq : ∀ d → suc (suc (d + (2 + d))) ≡ 4 + 2 * d
            eq = solve-∀

    -- An admin mark spent.
    admin : ∀ d {a b} → a ≤ b → 0 + a < (2 + d) + b
    admin d {b = b} h = s≤s (≤-trans h (m≤n+m b (suc d)))

    unsubIf-le : ∀ {Γ A} t d (s : St Γ A) → pot d (proj₁ (unsubIf t s)) ≤ pot d s
    unsubIf-le true  d s = unsub-le d s
    unsubIf-le false d s = ≤-refl

    -- A cold whose next due is ahead weighs no more than an unlisted mark.
    cold-ahead : ∀ {Γ A} d b (l : Tape A) → (∀ {κ′} → due l ≡ just κ′ → κ <ᴷ κ′ ≡ true) → pot {Γ} d (coldS b l) ≤ 2 + d
    cold-ahead d b l ah with due l | ah
    ... | just κ′ | ah′ = wt-ahead d κ′ (ah′ refl)
    ... | nothing | _ = z≤n

    -- A run in the hole: lighter there, lighter whole.
    hole : ∀ {Γ A} (c : Ctx R Γ A) {t t′ : St Γ A} {n} → n + pot (depth c) t′ < pot (depth c) t → pot 0 (plug c t′) + n < pot 0 (plug c t) + 0
    hole c {t} {t′} {n} h rewrite pot-plug c t | pot-plug c t′ | +-identityʳ (potC c + pot (depth c) t) =
      ≤-trans (≤-reflexive (cong suc (sw (potC c) (pot (depth c) t′) n))) (+-monoʳ-< (potC c) h)
      where sw : ∀ a b n → a + b + n ≡ a + (n + b)
            sw = solve-∀

    -- A climb left by a run: at most its depth.
    lift : ∀ {Γ A} {c : Ctx R Γ A} {s} (md : Mode A) {r} → climb ⟨ c , s , md , r ⟩ ≤ depth c
    lift {c = c} md = ≤-trans (climb-le md) (≤-reflexive (dirs-depth c))

    Np = ∀ {u} → κ ≡ at u → at p <ᴷ κ ≡ false

    -- A cold's turn.
    leafs : ∀ {Γ A} (c : Ctx R Γ A) b (l : Tape A) → (leafM , κ) ∈ own {Γ} (coldS b l) → Np
          → (closed c ≡ false → ∀ {τ u i t} {fr : Frame A t} → l ≡ play τ u i t fr → κ ≡ at (u ++ [ ix i ]) → listed L κ ≡ true)
          → (∀ {τ u i t f κ′} → l ≡ play τ u i t (close f) → due (rest τ (u ++ [ last ]) (From∞.force f)) ≡ just κ′ → κ <ᴷ κ′ ≡ true)
          → ∀ {τ k′} → Driver.took R (run c (coldS b l) leafM q) ≡ Driver.silent τ k′ → Wᶜ L p κ k′ < pot 0 (plug c (coldS b l)) + 0
    leafs c b     overT              () np row ah eq
    leafs c false (ending e₀)        (here k) np row ah refl = hole c (spend₀ (depth c) (cong proj₂ k) z≤n (np (cong proj₂ k)))
    leafs c false (play τ u i t fr)  (here k) np row ah refl = hole c (spend₀ (depth c) (cong proj₂ k) z≤n (np (cong proj₂ k)))
    leafs c true  (ending e₀)        (here k) np row ah refl =
      hole c (spend₀ (depth c) (cong proj₂ k) (lift {c = c} (if not (closed c) then rising cp else absorbed)) (np (cong proj₂ k)))
    leafs c true  (play τ u i t fr)  (here k) np row ah eq with closed c
    leafs c true  (play τ u i t fr)  (here k) np row ah refl | true =
      hole c (spend₀ (depth c) (cong proj₂ k) z≤n (np (cong proj₂ k)))
    leafs c true  (play τ u i t (emit a f))  (here k) np row ah refl | false =
      hole c (tick (depth c) (cong proj₂ k) (np (cong proj₂ k)) (row refl refl (cong proj₂ k))
                   (wt-ahead (depth c) (at (u ++ [ ix (suc i) ])) (subst (λ z → z <ᴷ at (u ++ [ ix (suc i) ]) ≡ true) (sym (cong proj₂ k))
                                            (trans (at-<ᴷ (u ++ [ ix i ]) (u ++ [ ix (suc i) ])) (<ᵖ-part u [] [] (<ᵖ-ix i)))))
                   (≤-reflexive (dirs-depth c)))
    leafs c true  (play τ u i t (stall f))  (here k) np row ah refl | false =
      hole c (tick (depth c) (cong proj₂ k) (np (cong proj₂ k)) (row refl refl (cong proj₂ k))
                   (wt-ahead (depth c) (at (u ++ [ ix (suc i) ])) (subst (λ z → z <ᴷ at (u ++ [ ix (suc i) ]) ≡ true) (sym (cong proj₂ k))
                                            (trans (at-<ᴷ (u ++ [ ix i ]) (u ++ [ ix (suc i) ])) (<ᵖ-part u [] [] (<ᵖ-ix i)))))
                   z≤n)
    leafs {Γ} c true  (play τ u i t (close f))  (here k) np row ah refl | false =
      hole c (tick (depth c) (cong proj₂ k) (np (cong proj₂ k)) (row refl refl (cong proj₂ k))
                   (cold-ahead {Γ} (depth c) true (rest τ (u ++ [ last ]) (From∞.force f)) (ah refl)) z≤n)

    -- A connect's admin mark.
    conns : ∀ {Γ A X} (c : Ctx R Γ A) (k : CS Γ X) (o′ : St Γ X) b mk → mk ≡ bodyM ⊎ (mk ≡ srcAttM ⊎ mk ≡ owedM) → (mk , κ) ∈ own (connS k o′ b)
          → ∀ {τ k′} → Driver.took R (run c (connS k o′ b) mk q) ≡ Driver.silent τ k′ → Wᶜ L p κ k′ < pot 0 (plug c (connS k o′ b)) + 0
    conns c k@(cs cl sl sa (just p₀) as ow ca ea sr sc) o′ b .bodyM (inj₁ refl) mi refl =
      hole c (+-monoˡ-< (pot (suc (depth c)) b) (+-monoˡ-< (pot (suc (depth c)) o′) (+-monoˡ-< _ (+-monoˡ-< _
        (≤-trans (m≤n+m (3 + depth c) (wt (depth c) (at (p₀ ++ [ ix 1 ])))) (m≤m+n _ _))))))
    conns c k@(cs cl sl sa nothing as ow ca ea sr sc) o′ b .bodyM (inj₁ refl) mi eq with own-body k o′ b mi
    ... | _ , ()
    conns c k@(cs cl sl sa ba (just p₀) ow ca ea sr sc) o′ b .srcAttM (inj₂ (inj₁ refl)) mi refl =
      hole c (+-monoˡ-< (pot (suc (depth c)) b)
               (+-mono-<-≤ (+-monoˡ-< _ (+-monoˡ-< _ (+-monoʳ-< (bodyP (depth c) ba) (s≤s z≤n))))
                           (unsubIf-le (not sl) (suc (depth c)) o′)))
    conns c k@(cs cl sl sa ba nothing ow ca ea sr sc) o′ b .srcAttM (inj₂ (inj₁ refl)) mi eq with own-src k o′ b mi
    ... | _ , ()
    conns c k@(cs cl sl sa ba as (just p₀) ca ea sr sc) o′ b .owedM (inj₂ (inj₂ refl)) mi refl =
      hole c (+-monoˡ-< (pot (suc (depth c)) b)
               (+-mono-<-≤ (+-mono-<-≤ (+-monoʳ-< (bodyP (depth c) ba + one (depth c) (not (isNone as))) (s≤s z≤n)) z≤n)
                           (unsubIf-le sa (suc (depth c)) o′)))
    conns c k@(cs cl sl sa ba as nothing ca ea sr sc) o′ b .owedM (inj₂ (inj₂ refl)) mi eq with own-owed k o′ b mi
    ... | _ , ()

    -- The least mark run, by its kind.
    runs : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} {mk} → Marked s mk → (mk , κ) ∈ own s → Np
         → (closed c ≡ false → ∀ {b τ u i t} {fr : Frame A t} → s ≡ coldS b (play τ u i t fr) → mk ≡ leafM → κ ≡ at (u ++ [ ix i ]) → listed L κ ≡ true)
         → (∀ {b τ u i t f κ′} → s ≡ coldS b (play τ u i t (close f)) → mk ≡ leafM → due (rest τ (u ++ [ last ]) (From∞.force f)) ≡ just κ′ → κ <ᴷ κ′ ≡ true)
         → ∀ {τ k′} → Driver.took R (run c s mk q) ≡ Driver.silent τ k′ → Wᶜ L p κ k′ < pot 0 (plug c s) + 0
    runs c (ofK i p₀ []) (here k) np row ah eq with closed c
    runs c (ofK i p₀ []) (here k) np row ah refl | true  = hole c (spend₀ (depth c) (cong proj₂ k) z≤n (np (cong proj₂ k)))
    runs c (ofK i p₀ []) (here k) np row ah refl | false = hole c (spend₀ (depth c) (cong proj₂ k) (≤-reflexive (dirs-depth c)) (np (cong proj₂ k)))
    runs c (ofK i p₀ (x ∷ xs)) (here k) np row ah eq with closed c
    runs c (ofK i p₀ (x ∷ xs)) (here k) np row ah refl | true  = hole c (<-≤-trans (spend₀ (depth c) (cong proj₂ k) z≤n (np (cong proj₂ k))) (m≤m+n _ _))
    runs c (ofK i p₀ (x ∷ xs)) (here k) np row ah refl | false = hole c (spend (depth c) (cong proj₂ k) (≤-reflexive (dirs-depth c)) (np (cong proj₂ k)))
    runs c (attK l p₀ s₀) mi np row ah refl = hole c (admin (depth c) (unsubIf-le (not l) (suc (depth c)) s₀))
    runs c (conK k o′ b mk w) mi np row ah eq = conns c k o′ b mk w mi eq
    runs c (joinK j g x q₀ (nx a) ib) (here k) np row ah refl =
      hole c (spend (depth c) (cong proj₂ k) (lift {c = c} (if g ∧ not (closed c) then rising (nx a) else absorbed)) (np (cong proj₂ k)))
    runs c (joinK j g x q₀ cp ib) (here k) np row ah refl =
      hole c (spend (depth c) (cong proj₂ k) (lift {c = c} (if g ∧ not (closed c) then rising cp else absorbed)) (np (cong proj₂ k)))
    runs c (leafK b l) mi np row ah eq = leafs c b l mi np (λ cl {τ} {u} {i} {t} {fr} e → row cl {b} (cong (coldS b) e) refl) (λ e → ah (cong (coldS b) e) refl) eq
    runs c (stopK i f r s₀) (here k) np row ah refl =
      hole c (sp (depth c) (cong proj₂ k) (lift {c = c} (if not (closed c) then rising cp else absorbed)) (np (cong proj₂ k)))
      where
        sp : ∀ d {κ₀ n P} → κ ≡ κ₀ → n ≤ d → at p <ᴷ κ ≡ false → n + ((2 + d) + P) < (wt d κ₀ + (2 + d)) + P
        sp d {n = n} {P} e h np′ = ≤-trans (≤-reflexive (cong suc (sym (+-assoc n (2 + d) P)))) (+-monoˡ-< P (spend d e h np′))
    runs c (cutK i f r s₀) mi np row ah refl = hole c (admin (depth c) (cut-le (suc (depth c)) s₀))

  -- A STILL MARK RUN LIGHTENS: the least mark found and run, weighed at
  -- its key, the run's clock.
  go : ∀ {Γ A} (c : Ctx R Γ A) s → Path (load o) rs ⟨ c , s , absorbed , q ⟩
     → ∀ {τ k′} → Driver.step R ⟨ c , s , absorbed , q ⟩ ≡ Driver.silent τ k′
     → Wᶜ L p (Clock ⟨ c , s , absorbed , q ⟩) k′ < W L p ⟨ c , s , absorbed , q ⟩
  go c s pth {τ} {k′} with search top (plug c s) in fd
  ... | nothing = λ ()
  ... | just (found (_ , _ , c′ , s′) mk κ) = λ eq →
    subst (λ t → Wᶜ L p κ k′ < Weigh.pot L p κ 0 t + 0) (found-plug c s fd)
      (At.runs κ c′ (found-mark c s fd) (proj₁ (found-least {t = plug c s} fd))
        (λ { refl → mark-short o pth m fd })
        (λ { cl refl refl refl → let (r , _ , tr , le , mr) = tick-row o pth m fd cl in ∈-listed L _ (∈-++⁺ʳ ks (anc-∈ ks (cov tr le) mr)) })
        (λ { refl refl dr → frame-ahead o pth fd dr })
        eq)

-- STILL STEPS LIGHTEN, WEIGHED AT THE CLOCK THEY START FROM.
still-lightens : ∀ {R} (o : PureObs [] R) {rs k k′ p e} → Path (load o) rs k
               → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
               → ∀ ks → (∀ {q e′} → enter (⟦ o ⟧ []ᴬ) root q e′ → q ≼ p → q ∈ ks)
               → Still (ks ++ anc ks) k′ k → Wᶜ (ks ++ anc ks) p (Clock k) k′ < W (ks ++ anc ks) p k
still-lightens o {k = ⟨ c , s , rising ε , q ⟩} pth m ks cov (st@(_ , eq) , kept) =
  Rose.rose o m ks cov q c s ε pth (λ md → lane-guard o pth st md m) eq kept
still-lightens o {k = ⟨ c , s , subscribing , q ⟩} pth m ks cov st = lightens-begin o pth m ks cov st
still-lightens o {k = ⟨ c , s , absorbed , q ⟩} pth m ks cov ((_ , eq) , _) = Run.go o m ks cov q c s pth eq
