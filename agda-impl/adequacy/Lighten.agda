{-# OPTIONS --guardedness #-}

-- STILL STEPS LIGHTEN: a still step weighed, both confs at the clock it
-- starts from, by the step's mode — a climb, a subscribe, a mark run.
module adequacy.Lighten where

open import Data.Bool using (true; false; not; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; length; _ʳ++_; null)
open import Data.List.Properties using (length-++)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (suc; pred; _+_; _*_; _≤_; _<_; _<ᵇ_; _≡ᵇ_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤; +-monoˡ-<)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Events using (Pos; root; ix; last; <ᵖ-below; <ᵖ-part)
open import denotation.EmissionSet using (enter; ⟦_⟧; _≼_)
open import denotation.Read using (Meets)
open import operation.PureObservable using (PureObs; module Machine; module Driver; opening; due; Tape)
open import denotation.Events using (timelineAt)
open Machine using (Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    CS; cs; Mode; Conf; ⟨_,_,_,_⟩; plug; load; subscribing; absorbed; rising; nx; cp; closedUp; closed; alive; dirs; unsub; cut; killAll; ended; settle;
                    attAt; attached; free; cpAt; cutAt; overAt)
open import operation.Key using (Key; at; _<ᴷ_; at-<ᴷ; <ᴷ-trans; <ᴷ-irrefl; clash)
open import adequacy.Rows using (conv)
open import adequacy.Weight using (Clock; W; Wᶜ; anc; depth; syn; one; isNone; climb; module Weigh)
open import adequacy.Path using (Path; Still; _⇜_)

-- A position's child keyed strictly after it.
below : ∀ q {l} → at q <ᴷ at (q ++ [ l ]) ≡ true
below q = trans (at-<ᴷ q _) (<ᵖ-below q [])

-- A position's first child keyed before its second.
part : ∀ q → at (q ++ [ ix 0 ]) <ᴷ at (q ++ [ ix 1 ]) ≡ true
part q = trans (at-<ᴷ (q ++ [ ix 0 ]) (q ++ [ ix 1 ])) (<ᵖ-part q {ix 0} {ix 1} [] [] refl)

-- A clock a level down at the second child is not before the first.
over : ∀ q → at (q ++ [ ix 1 ]) <ᴷ at (q ++ [ ix 0 ]) ≡ true → ⊥
over q h = clash (<ᴷ-trans (at (q ++ [ ix 1 ])) (at (q ++ [ ix 0 ])) (at (q ++ [ ix 1 ])) h (part q)) (<ᴷ-irrefl (at (q ++ [ ix 1 ])))

postulate
  -- A SUBSCRIBING RUN IS AT ITS SUBSCRIPTION: every conf a run reaches
  -- subscribing has a pending subscription in focus, owed where the run is.
  pend-focus : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s q}
             → Path (load o) rs ⟨ c , s , subscribing , q ⟩ → Σ (PureObs Γ A) λ o′ → s ≡ pend o′ q

  -- A COLD OPENS AHEAD: a cold a run subscribes first comes due strictly
  -- after where it was subscribed.
  opening-ahead : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {x q κ}
                → Path (load o) rs ⟨ c , pend (cold x) q , subscribing , q ⟩
                → due (opening q (timelineAt x q)) ≡ just κ → at q <ᴷ κ ≡ true

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

  -- A SOURCE'S FEED COMES DUE NO SOONER: once a source has risen, every
  -- mark is due no earlier than the row a level down.
  fed-ahead : ∀ {R} (o : PureObs [] R) {rs Γ X B} {k : CS Γ X} {b : St (X ∷ Γ) B} {c : Ctx R Γ B} {s ε q k′}
            → Path (load o) rs ⟨ inSrc k b c , s , rising ε , q ⟩ → k′ ⇜ ⟨ inSrc k b c , s , rising ε , q ⟩
            → Clock k′ <ᴷ at (q ++ [ ix 0 ]) ≡ false

  -- A STILL MARK RUN LIGHTENS: the least mark run, passing no listed row,
  -- lowers the weight at its clock.
  lightens-run : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s q k′ p e}
               → Path (load o) rs ⟨ c , s , absorbed , q ⟩
               → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
               → ∀ ks → (∀ {q′ e′} → enter (⟦ o ⟧ []ᴬ) root q′ e′ → q′ ≼ p → q′ ∈ ks)
               → Still (ks ++ anc ks) k′ ⟨ c , s , absorbed , q ⟩
               → Wᶜ (ks ++ anc ks) p (Clock ⟨ c , s , absorbed , q ⟩) k′ < W (ks ++ anc ks) p ⟨ c , s , absorbed , q ⟩

private
  conn-arith : ∀ w e x y → w ≤ e → suc ((((w + e) + 0) + 0 + e) + x + y) ≤ 1 + 3 * e + y + x
  conn-arith w e x y h =
    ≤-trans (s≤s (+-monoˡ-≤ y (+-monoˡ-≤ x (+-monoˡ-≤ e (+-monoˡ-≤ 0 (+-monoˡ-≤ 0 (+-monoˡ-≤ e h)))))))
            (≤-reflexive (eq e x y))
    where eq : ∀ e x y → suc ((((e + e) + 0) + 0 + e) + x + y) ≡ 1 + 3 * e + y + x
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

-- STILL STEPS LIGHTEN, WEIGHED AT THE CLOCK THEY START FROM.
still-lightens : ∀ {R} (o : PureObs [] R) {rs k k′ p e} → Path (load o) rs k
               → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
               → ∀ ks → (∀ {q e′} → enter (⟦ o ⟧ []ᴬ) root q e′ → q ≼ p → q ∈ ks)
               → Still (ks ++ anc ks) k′ k → Wᶜ (ks ++ anc ks) p (Clock k) k′ < W (ks ++ anc ks) p k
still-lightens o {k = ⟨ c , s , rising ε , q ⟩} pth m ks cov (st@(_ , eq) , kept) =
  Rose.rose o m ks cov q c s ε pth (λ md → lane-guard o pth st md m) eq kept
still-lightens o {k = ⟨ c , s , subscribing , q ⟩} pth m ks cov st = lightens-begin o pth m ks cov st
still-lightens o {k = ⟨ c , s , absorbed , q ⟩} pth m ks cov st = lightens-run o pth m ks cov st
