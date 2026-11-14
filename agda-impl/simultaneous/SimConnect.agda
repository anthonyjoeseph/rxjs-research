{-# OPTIONS --guardedness #-}

-- A CONNECT SIMULATES ITS CONNECT.  The source is simulated at its own
-- pair, `r` against the annotated source's source two steps under `p′`;
-- annotated, that simulation is the hot the body reads, and the body is
-- simulated at its pair over it.  Every value and end of the connect is
-- the body's, the source's rows showing silent, so the body's carriers
-- are the connect's.
--
-- The connect's map is the two pairs, the source's map, the source's
-- burst bound paired, and the body's map: the body's ambient map with
-- the body's map, reassociated.
module simultaneous.SimConnect where

import Data.List as L
open import Data.List using ([]; _∷_; [_]; _++_; filter)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁺; ∈-filter⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?)
import Data.List.Relation.Unary.Any as AnyP
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (T?; ¬?)

open import Tree using (Obs; connect)
open import denotation.Position using (Pos; root; _≟ᵖ_; _⊕_; _<ᵖ_; inside; ix; last)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Den; hot; DenEnv; Proper; enter; approx; Few; _≺_; _≼_; module Connect)
open import denotation.Laws using (inv-approx; good-cons)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext; ≺→≼; ≺-irrefl; ≼-≺-≺; ≼-or-≻; ≼-split)
open import denotation.Laws.Shows using (k-shows; ∈-stable; few-down; few-reach)
open import denotation.Laws.ShowsEv using (sk-approx)
open import denotation.Laws.ShowsOps using () renaming (module Conn to SC)
open import denotation.Laws.Truth.Connect.Cuts using (step≼; module Side)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; Lawful; InvD; InvAt; _∪ʰ_; ok-step; here; _⊑_; ⊑-refl; ⊑-cmp; ⊑-snoc⁺; ⊑-trans; ⊑-≼; ⊑-inside; inside-⊑; ⊕-injˡ)
import denotation.Laws.Connect as LC
open import simultaneous.SObs using (lone; module Elaborate; ext)
open import simultaneous.Sim using (PMap; _∪ᴹ_; _⊆ᴹ_; Emb; Below; Fresh; Local; NoneUnder; Sim; Run; Lates; Mt; Carried; c-end; Upto;
  Under; Mapped; ListedB; ListedL; Live; Allᴱ; EndsAfter; env-live; Joins; Shows; Shown; AShows;
  AShown; HotSim; EnvSim; EnvListed; EnvNeeds; EnvJoins; Apart; SimIH; sih)
open import simultaneous.ReadMap using (under?; under-down; upto-dn; listed-up)
open import simultaneous.SimReader using (hots-at)
open import simultaneous.SimPos using (UpTo)
open import simultaneous.AnnRun using (Upto?; module AnnRun)
open import simultaneous.ToldRows using (T-or)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; annotate)

------------------------------------------------------------------------
-- Maps

-- One pair.
Pair : Pos → Pos → PMap
Pair a a′ x y = x ≡ a × y ≡ a′

-- Within an order embedding, an order embedding.
emb-sub : ∀ {M M′} → M ⊆ᴹ M′ → Emb M′ → Emb M
emb-sub inc e = record
  { fun     = λ a a′ → Emb.fun e (inc a) (inc a′)
  ; mono    = λ a a′ → Emb.mono e (inc a) (inc a′)
  ; reflect = λ a a′ → Emb.reflect e (inc a) (inc a′)
  }

-- A run anchored in a map is anchored in any holding it.
run-up : ∀ {A B} {V : A → B → Set} {Sh M M′ L} {T : EmissionSet A} {U : EmissionSet B} → M ⊆ᴹ M′ → Run V Sh M L T U → Run V Sh M′ L T U
run-up inc R = record
  { Img     = Img
  ; img-fun = img-fun
  ; ext     = λ i → proj₁ (ext′ i) , inc (proj₁ (proj₂ (ext′ i))) , proj₂ (proj₂ (ext′ i))
  ; sim     = λ A′ inc′ → sim A′ (λ a → inc′ (inc a))
  ; late    = λ A′ inc′ → late A′ (λ a → inc′ (inc a))
  ; anchor  = λ A′ inc′ em x ce L lst → proj₁ (anchor A′ (λ a → inc′ (inc a)) em x ce L lst)
                                      , inc (proj₂ (anchor A′ (λ a → inc′ (inc a)) em x ce L lst))
  }
  where open Run R renaming (ext to ext′)

-- Joins at one subscription map are joins at any holding it.
joins-S : ∀ {X} {S S′ P : PMap} {t : EmissionSet X} {Img} → S ⊆ᴹ S′ → Joins S P t Img → Joins S′ P t Img
joins-S inc j {e₀ = e₀} a q e with j {e₀ = e₀} a q e
... | e₁ , eq , e₁′ , s₁ , rest = e₁ , eq , e₁′ , inc s₁ , rest

-- Live in a run: live in one each of whose ends passes one of its proper
-- ends.
live-after : ∀ {A B′} {t : EmissionSet A} {T′ : EmissionSet B′} → EndsAfter (Proper t) T′ → ∀ {j} → Live t j → Live T′ j
live-after ea {j} l {k} x = ≺-trans {j} {proj₁ (ea x)} {k} (l (proj₁ (proj₁ (proj₂ (ea x))))) (proj₂ (proj₂ (ea x)))

-- At or under a position: below it.
below-at : ∀ {H q x} → q ⊑ x → Below H q x
below-at {q = q} h = q , here , h

-- A simulated hot under a larger ambient map keeping its joins.
hot-up : ∀ {Amb Amb′ X} {d : Den X} {d′} → Amb ⊆ᴹ Amb′ → (h : HotSim Amb d d′)
       → Joins Amb′ Amb′ (HotSim.rows h) (HotSim.car h) → HotSim Amb′ d d′
hot-up inc h j = record
  { Δ₀ = Δ₀ ; src = src ; at = at ; m = m ; core = core ; env₀ = env₀ ; at′ = at′ ; need = need ; need-row = need-row
  ; isP = isP ; isE = isE ; law = law ; law′ = law′ ; run = run-up inc run ; joins = j }
  where open HotSim h

-- WHAT A RUN READS, listed up to a bound, is listed up to a row up to it
-- where no hot row lies at or under the row.
env-row : ∀ {Γ Δ} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {Amb env env′} (es : EnvSim ρ Amb env env′) {B} {T : EmissionSet B} {c k}
        → Upto c k → (∀ {X} (i : X ∈ Γ) {h e} → HotSim.rows (es i) h e → k ⊑ h → ⊥)
        → ∀ {A′} → EnvListed ρ env env′ es T A′ c → EnvListed ρ env env′ es T A′ (just k)
env-row {Γ} es {T = T} {c} {k} uk nh = go Γ (λ i → HotSim.rows (es i)) (λ i → nh i)
  where
    go : ∀ Γ′ (r : ∀ {X} → X ∈ Γ′ → EmissionSet X) → (∀ {X} (i : X ∈ Γ′) {h e} → r i h e → k ⊑ h → ⊥)
       → Allᴱ Γ′ (λ i → ListedL (r i) T c) → Allᴱ Γ′ (λ i → ListedL (r i) T (just k))
    go []       _ _  _                      = tt
    go (_ ∷ Γ′) r nr ((ks , cov , bk) , ls) = (ks , (λ y u l → cov y (fix y u) l) , bk) , go Γ′ (λ i → r (there i)) (λ i → nr (there i)) ls
      where
        fix : ∀ {h e} → r (here refl) h e → UpTo k h → Upto c h
        fix _ (inj₁ lt) = upto-dn c lt uk
        fix y (inj₂ kh) = ⊥-elim (nr (here refl) y kh)

-- A carrier whose image lies under a bound's image is up to the bound:
-- the embedding reflects both the order and leading.
img-upto : ∀ {A′} → Emb A′ → ∀ {c y k y′ l} → A′ c y → A′ k y′ → y′ ⊑ l → UpTo y l → UpTo c k
img-upto em {c} {y} {k} {y′} {l} ac ak yl (inj₁ ly) with ≼-or-≻ c k
... | inj₂ kc = inj₁ kc
... | inj₁ ck with ≼-split {c} {k} ck
...   | inj₁ c≺k = ⊥-elim (≺-irrefl {y} (≺-trans {y} {y′} {y} (Emb.mono em ac ak c≺k) (≼-≺-≺ {y′} {l} {y} (⊑-≼ {y′} {l} yl) ly)))
...   | inj₂ refl = ⊥-elim (≺-irrefl {y′} (subst (y′ ≺_) (Emb.fun em ac ak) (≼-≺-≺ {y′} {l} {y} (⊑-≼ {y′} {l} yl) ly)))
img-upto em {c} {y} {k} {y′} ac ak yl (inj₂ yl′) with ⊑-cmp y y′ yl′ yl
... | inj₁ yy′ = inj₂ (Emb.reflect em ac ak yy′)
... | inj₂ y′y with ≼-split {k} {c} (⊑-≼ {k} {c} (Emb.reflect em ak ac y′y))
...   | inj₁ k≺c = inj₁ k≺c
...   | inj₂ refl = inj₂ (⊑-refl k)

-- Up to a bound, so is the first child: nothing lies between a position
-- and it.
upto-next : ∀ c {j} → Upto c j → Upto c (j ⊕ [ ix 0 ])
upto-next nothing  _ = tt
upto-next (just c) {j} (inj₁ jc) with ≼-split {j ⊕ [ ix 0 ]} {c} (step≼ {j} {c} jc)
... | inj₁ lt = inj₁ lt
... | inj₂ eq = inj₂ (subst (_⊑ (j ⊕ [ ix 0 ])) eq (⊑-refl _))
upto-next (just c) {j} (inj₂ cj) = inj₂ (⊑-trans cj (⊑-snoc⁺ j))

------------------------------------------------------------------------
-- The rows of a listing a choice keeps

module Keep {X Y} {t : EmissionSet X} {u : EmissionSet Y} (pick : ∀ {k e} → t k e → Maybe (Σ Pos λ j → Σ (Ev Y) (u j))) where

  Back : L.List Pos → Set
  Back ks = ∀ {k} → k ∈ ks → Σ (Ev X) (t k)

  cons : Maybe (Σ Pos λ j → Σ (Ev Y) (u j)) → L.List Pos → L.List Pos
  cons (just (j , _)) ls = j ∷ ls
  cons nothing        ls = ls

  keep : (ks : L.List Pos) → Back ks → L.List Pos
  keep []       _  = []
  keep (k ∷ ks) bk = cons (pick (proj₂ (bk (here refl)))) (keep ks (λ m → bk (there m)))

  kept-row : (ks : L.List Pos) (bk : Back ks) {v : Pos} → v ∈ keep ks bk → Σ (Ev Y) (u v)
  kept-row (k ∷ ks) bk {v} m = go (pick (proj₂ (bk (here refl)))) m
    where
      go : (mb : Maybe (Σ Pos λ j → Σ (Ev Y) (u j))) → v ∈ cons mb (keep ks (λ m → bk (there m))) → Σ (Ev Y) (u v)
      go (just (_ , w)) (here refl) = w
      go (just _)       (there m′)  = kept-row ks (λ m → bk (there m)) m′
      go nothing        m′          = kept-row ks (λ m → bk (there m)) m′

  -- A listed position every row at which is picked keeps what it picks.
  kept : (ks : L.List Pos) (bk : Back ks) {v j : Pos} → v ∈ ks
       → (∀ {e} (x : t v e) → Σ (Σ (Ev Y) (u j)) λ w → pick x ≡ just (j , w)) → j ∈ keep ks bk
  kept (k ∷ ks) bk {j = j} (here refl) all = go _ (all (proj₂ (bk (here refl))))
    where
      go : ∀ mb → (Σ (Σ (Ev Y) (u j)) λ w → mb ≡ just (j , w)) → j ∈ cons mb (keep ks (λ m → bk (there m)))
      go _ (_ , refl) = here refl
  kept (k ∷ ks) bk {j = j} (there m) all = go (pick (proj₂ (bk (here refl))))
    where
      go : ∀ mb → j ∈ cons mb (keep ks (λ m → bk (there m)))
      go (just _) = there (kept ks (λ m → bk (there m)) m all)
      go nothing  = kept ks (λ m → bk (there m)) m all

------------------------------------------------------------------------
-- The connect at a pair

module Conn (n : ℕ) {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B)
            (ihs : SimIH n ρ s) (ihb : ∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE (A ∷ Γ) → X ∈ Δ′) → SimIH n ρ′ b)
            (env : DenEnv Γ) (env′ : DenEnv Δ) (Amb : PMap) (ge : GoodEnv env) (ge′ : GoodEnv env′) (ap : Apart env)
            (es : EnvSim ρ Amb env env′) (en : EnvNeeds ρ env env′ es) (em : Emb Amb)
            (p p′ : Pos) (pp : Amb p p′) (fr : Fresh (Hots env) (Hots env′) Amb p p′)
            (ok : Ok (Hots env) p) (ok′ : Ok (Hots env′) p′) (nh : ¬ Hots env p) where

  ds : Den A
  ds = approx n s env

  F : Den A → Den B
  F h = approx n b (h ∷ᴬ env)

  ds′ : Den (AIE A)
  ds′ = approx n (annotate (elab ρ s)) env′

  F′ : Den (AIE A) → Den (IE B)
  F′ h = approx n (elab (ext ρ) b) (h ∷ᴬ env′)

  open Connect ds F p using (σ; β; ConnT; r; body; burst; echo; kept)
  open Connect ds′ F′ p′ using (body; burst; echo; kept) renaming (σ to σ′; β to β′; ConnT to ConnT′; r to r′)
  module CP = Connect ds F p
  module CE = Connect ds′ F′ p′

  Is : InvD (Hots env) ds
  Is = inv-approx n s env ge

  IF : ∀ {t} → Lawful t → InvD (Hots env ∪ʰ t) (F (hot t))
  IF {t} law = inv-approx n b (hot t ∷ᴬ env) (good-cons law ge)

  Is′ : InvD (Hots env′) ds′
  Is′ = inv-approx n (annotate (elab ρ s)) env′ ge′

  IF′ : ∀ {t} → Lawful t → InvD (Hots env′ ∪ʰ t) (F′ (hot t))
  IF′ {t} law = inv-approx n (elab (ext ρ) b) (hot t ∷ᴬ env′) (good-cons law ge′)

  lawσ : Lawful (Proper σ)
  lawσ = LC.lawful {s = ds} {F = F} Is IF p ok

  lawσ′ : Lawful (Proper σ′)
  lawσ′ = LC.lawful {s = ds′} {F = F′} Is′ IF′ p′ ok′

  -- The body's subscriptions, and the annotated source's source.
  p₀ p₀′ r″ : Pos
  p₀  = p ⊕ [ ix 0 ]
  p₀′ = p′ ⊕ [ ix 0 ]
  r″  = r′ ⊕ [ ix 1 ]

  -- The source's burst bound.
  rl rl″ : Pos
  rl  = r ⊕ [ last ]
  rl″ = r″ ⊕ [ last ]

  p⊑r : p ⊑ r
  p⊑r = ⊑-snoc⁺ p

  p′⊑r″ : p′ ⊑ r″
  p′⊑r″ = ⊑-trans (⊑-snoc⁺ p′) (⊑-snoc⁺ r′)

  p⊑rl : p ⊑ rl
  p⊑rl = ⊑-trans p⊑r (⊑-snoc⁺ r)

  p′⊑rl″ : p′ ⊑ rl″
  p′⊑rl″ = ⊑-trans p′⊑r″ (⊑-snoc⁺ r″)

  T : EmissionSet B
  T = enter (approx n (connect s b) env) p

  U : EmissionSet (IE B)
  U = enter (approx n (elab ρ (connect s b)) env′) p′

  ----------------------------------------------------------------------
  -- The source at its pair

  Amb-s : PMap
  Amb-s = Amb ∪ᴹ Pair r r″

  postulate
    -- A point under the subscription is a join wherever a hot row lies
    -- strictly above it.
    joins-sub : ∀ {X} (i : X ∈ Γ) {x y} → p ⊑ x → p′ ⊑ y → Joins Amb (Pair x y) (HotSim.rows (es i)) (HotSim.car (es i))
    emb-s   : Emb Amb-s
    fresh-s : Fresh (Hots env) (Hots env′) Amb-s r r″
    nh-s    : ¬ Hots env r

  joins-s : ∀ {X} (i : X ∈ Γ) → Joins Amb-s Amb-s (HotSim.rows (es i)) (HotSim.car (es i))
  joins-s i {e₀ = e₀} (inj₁ a)  q e = joins-S {t = HotSim.rows (es i)} {Img = HotSim.car (es i)} inj₁ (HotSim.joins (es i)) {e₀ = e₀} a q e
  joins-s i {e₀ = e₀} (inj₂ pr) q e = joins-S {t = HotSim.rows (es i)} {Img = HotSim.car (es i)} inj₁ (joins-sub i p⊑r p′⊑r″) {e₀ = e₀} pr q e

  es-s : EnvSim ρ Amb-s env env′
  es-s i = hot-up inj₁ (es i) (joins-s i)

  en-s : EnvNeeds ρ env env′ es-s
  en-s i = en i

  at-s : Amb-s r r″
  at-s = inj₂ (refl , refl)

  srcIH = SimIH.sims ihs env env′ Amb-s ge ge′ ap es-s en-s (emb-s) r r″ at-s (fresh-s) (ok-step p ok) (ok-step r′ (ok-step p′ ok′)) nh-s

  Ms : PMap
  Ms = proj₁ srcIH

  lc-s : Local (Hots env) (Hots env′) r r″ Ms
  lc-s = proj₁ (proj₂ srcIH)

  nu-s : NoneUnder Ms σ
  nu-s = proj₁ (proj₂ (proj₂ (proj₂ srcIH)))

  ej-s : EnvJoins ρ env env′ es-s Ms
  ej-s = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ srcIH))))

  ----------------------------------------------------------------------
  -- The hot the body reads

  Amb-b : PMap
  Amb-b = (((Amb-s ∪ᴹ Ms) ∪ᴹ Pair rl rl″) ∪ᴹ Pair p₀ p₀′)

  s⊆b : (Amb-s ∪ᴹ Ms) ⊆ᴹ Amb-b
  s⊆b a = inj₁ (inj₁ a)

  -- No hot row lies at or under a source row: the row is in the source's
  -- world, which holds none.
  under-σ : ∀ {X} (i : X ∈ Γ) {h e k e′} → HotSim.rows (es i) h e → σ k e′ → k ⊑ h → ⊥
  under-σ i y x kh = proj₂ (ok-step p ok) (hots-at env i (HotSim.isP (es i)) y) (InvAt.world (Is r (ok-step p ok)) x) (⊑-inside kh)

  -- What the source reads, listed up to a bound: listed up to a source
  -- row up to it.
  need-row : ∀ {A′ c k e} → Proper σ k e → Upto c k → EnvListed ρ env env′ es-s σ A′ c → EnvListed ρ env env′ es-s σ A′ (just k)
  need-row {A′} x uk = env-row {Γ} {Δ} {λ {X} → ρ {X}} {Amb-s} {env} {env′} es-s {T = σ} uk (λ i y kh → under-σ i y (proj₁ x) kh) {A′}

  -- THE ANNOTATED SOURCE IS A RUN OF THE SOURCE.
  annotate-run : Run AShows AShown (Amb-s ∪ᴹ Ms) (EnvListed ρ env env′ es-s σ) (Proper σ) (Proper σ′)
  annotate-run = AnnRun.run n (elab ρ s) env′ ge′ r′ (ok-step p′ ok′) (Is r (ok-step p ok)) (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ srcIH)))))
                   (λ {A′} {c} {k} {e} → need-row {A′} {c} {k} {e})

  postulate
    -- No point of the body's ambient map lies strictly under a source row.
    joins-σ : Joins Amb-b Amb-b (Proper σ) (Run.Img annotate-run)

  hotσ : HotSim Amb-b (hot (Proper σ)) (hot (Proper σ′))
  hotσ = record
    { Δ₀ = Δ ; src = ds ; at = r ; m = n ; core = elab ρ s ; env₀ = env′ ; at′ = r′
    ; need = EnvListed ρ env env′ es-s σ
    ; need-row = λ {A′} {c} {k} {e} → need-row {A′} {c} {k} {e}
    ; isP = refl ; isE = refl ; law = lawσ ; law′ = lawσ′
    ; run = run-up s⊆b annotate-run
    ; joins = joins-σ
    }

  ----------------------------------------------------------------------
  -- The body at its pair

  env-b : DenEnv (A ∷ Γ)
  env-b = hot (Proper σ) ∷ᴬ env

  env′-b : DenEnv (AIE A ∷ Δ)
  env′-b = hot (Proper σ′) ∷ᴬ env′

  postulate
    joins-b : ∀ {X} (i : X ∈ Γ) → Joins Amb-b Amb-b (HotSim.rows (es i)) (HotSim.car (es i))
    emb-b   : Emb Amb-b
    fresh-b : Fresh (Hots env-b) (Hots env′-b) Amb-b p₀ p₀′
    apart-b : ∀ {q e} → Proper σ q e → Hots env q → ⊥
    nh-b    : ¬ Hots env-b p₀

  es-b : EnvSim (ext ρ) Amb-b env-b env′-b
  es-b (here refl) = hotσ
  es-b (there i)   = hot-up (λ a → inj₁ (inj₁ (inj₁ (inj₁ a)))) (es i) (joins-b i)

  en-b : EnvNeeds (ext ρ) env-b env′-b es-b
  en-b (here refl) T′ ea A′ c (_ , Le) = env-live {ρ = ρ} {Amb = Amb-s} {env = env} {env′ = env′} es-s {T = T′} {T′ = σ} (λ {j} → live-after {t = σ} {T′ = T′} ea {j}) {A′} {c} Le
  en-b (there i)   T′ ea A′ c (_ , Le) = en i T′ ea A′ c Le

  at-b : Amb-b p₀ p₀′
  at-b = inj₂ (refl , refl)

  bodyIH = SimIH.sims (ihb {AIE A ∷ Δ} (λ {X} → ext ρ {X})) env-b env′-b Amb-b (good-cons lawσ ge) (good-cons lawσ′ ge′) (apart-b , ap) es-b en-b (emb-b)
           p₀ p₀′ at-b (fresh-b) (LC.ok₀ {s = ds} {F = F} Is IF p ok) (LC.ok₀ {s = ds′} {F = F′} Is′ IF′ p′ ok′) nh-b

  Mb : PMap
  Mb = proj₁ bodyIH

  lc-b : Local (Hots env-b) (Hots env′-b) p₀ p₀′ Mb
  lc-b = proj₁ (proj₂ bodyIH)

  emb-bM : Emb (Amb-b ∪ᴹ Mb)
  emb-bM = proj₁ (proj₂ (proj₂ bodyIH))

  nu-b : NoneUnder Mb β
  nu-b = proj₁ (proj₂ (proj₂ (proj₂ bodyIH)))

  ej-b : EnvJoins (ext ρ) env-b env′-b es-b Mb
  ej-b = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ bodyIH))))

  Rb : Run Shows Shown (Amb-b ∪ᴹ Mb) (EnvListed (ext ρ) env-b env′-b es-b β) β β′
  Rb = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ bodyIH))))

  ----------------------------------------------------------------------
  -- The connect's map

  M : PMap
  M = (((Pair r r″ ∪ᴹ Ms) ∪ᴹ Pair rl rl″) ∪ᴹ Pair p₀ p₀′) ∪ᴹ Mb

  b⊆M : (Amb-b ∪ᴹ Mb) ⊆ᴹ (Amb ∪ᴹ M)
  b⊆M (inj₂ a)                               = inj₂ (inj₂ a)
  b⊆M (inj₁ (inj₂ a))                        = inj₂ (inj₁ (inj₂ a))
  b⊆M (inj₁ (inj₁ (inj₂ a)))                 = inj₂ (inj₁ (inj₁ (inj₂ a)))
  b⊆M (inj₁ (inj₁ (inj₁ (inj₂ a))))          = inj₂ (inj₁ (inj₁ (inj₁ (inj₂ a))))
  b⊆M (inj₁ (inj₁ (inj₁ (inj₁ (inj₁ a)))))   = inj₁ a
  b⊆M (inj₁ (inj₁ (inj₁ (inj₁ (inj₂ a)))))   = inj₂ (inj₁ (inj₁ (inj₁ (inj₁ a))))

  M⊆b : (Amb ∪ᴹ M) ⊆ᴹ (Amb-b ∪ᴹ Mb)
  M⊆b (inj₁ a)                               = inj₁ (inj₁ (inj₁ (inj₁ (inj₁ a))))
  M⊆b (inj₂ (inj₂ a))                        = inj₂ a
  M⊆b (inj₂ (inj₁ (inj₂ a)))                 = inj₁ (inj₂ a)
  M⊆b (inj₂ (inj₁ (inj₁ (inj₂ a))))          = inj₁ (inj₁ (inj₂ a))
  M⊆b (inj₂ (inj₁ (inj₁ (inj₁ (inj₂ a)))))   = inj₁ (inj₁ (inj₁ (inj₂ a)))
  M⊆b (inj₂ (inj₁ (inj₁ (inj₁ (inj₁ a)))))   = inj₁ (inj₁ (inj₁ (inj₁ (inj₂ a))))

  s⊆M : (Amb-s ∪ᴹ Ms) ⊆ᴹ (Amb ∪ᴹ M)
  s⊆M a = b⊆M (inj₁ (s⊆b a))

  emb : Emb (Amb ∪ᴹ M)
  emb = emb-sub M⊆b emb-bM

  postulate
    below-b  : ∀ {x} → Below (Hots env-b) p₀ x → Below (Hots env) p x
    below-b′ : ∀ {y} → Below (Hots env′-b) p₀′ y → Below (Hots env′) p′ y
    below-s  : ∀ {x} → Below (Hots env) r x → Below (Hots env) p x
    below-s′ : ∀ {y} → Below (Hots env′) r″ y → Below (Hots env′) p′ y

  local : Local (Hots env) (Hots env′) p p′ M
  local (inj₂ a)                                       = below-b (proj₁ (lc-b a)) , below-b′ (proj₂ (lc-b a))
  local (inj₁ (inj₂ (refl , refl)))                    = below-at (⊑-snoc⁺ p) , below-at (⊑-snoc⁺ p′)
  local (inj₁ (inj₁ (inj₂ (refl , refl))))             = below-at p⊑rl , below-at p′⊑rl″
  local (inj₁ (inj₁ (inj₁ (inj₂ a))))                  = below-s (proj₁ (lc-s a)) , below-s′ (proj₂ (lc-s a))
  local (inj₁ (inj₁ (inj₁ (inj₁ (refl , refl)))))      = below-at p⊑r , below-at p′⊑r″

  env-joins : EnvJoins ρ env env′ es M
  env-joins i {e₀ = e₀} (inj₂ a)                      q e = joins-S {t = HotSim.rows (es i)} {Img = HotSim.car (es i)} b⊆M (ej-b (there i)) {e₀ = e₀} a q e
  env-joins i {e₀ = e₀} (inj₁ (inj₂ a))               q e = joins-S {t = HotSim.rows (es i)} {Img = HotSim.car (es i)} inj₁ (joins-sub i (⊑-snoc⁺ p) (⊑-snoc⁺ p′)) {e₀ = e₀} a q e
  env-joins i {e₀ = e₀} (inj₁ (inj₁ (inj₂ a)))        q e = joins-S {t = HotSim.rows (es i)} {Img = HotSim.car (es i)} inj₁ (joins-sub i p⊑rl p′⊑rl″) {e₀ = e₀} a q e
  env-joins i {e₀ = e₀} (inj₁ (inj₁ (inj₁ (inj₂ a)))) q e = joins-S {t = HotSim.rows (es i)} {Img = HotSim.car (es i)} s⊆M (ej-s i) {e₀ = e₀} a q e
  env-joins i {e₀ = e₀} (inj₁ (inj₁ (inj₁ (inj₁ a)))) q e = joins-S {t = HotSim.rows (es i)} {Img = HotSim.car (es i)} inj₁ (joins-sub i p⊑r p′⊑r″) {e₀ = e₀} a q e

  postulate
    -- No source-map point lies under a body row, and no body-map point
    -- under a source row's echo.
    body-s : ∀ {k e x y} → β k e → Ms x y → k ⊑ x → ⊥
    src-b  : ∀ {k e x y} → σ k e → Mb x y → (k ⊕ [ ix 0 ]) ⊑ x → ⊥
    -- The three pairs lie under no row but their own.
    pairs-none : ∀ {k e x} → T k e → (x ≡ r ⊎ x ≡ rl ⊎ x ≡ p₀) → k ⊑ x → x ≡ k

  -- No source-map point lies under a source row's first child: the
  -- source's map pairs nothing strictly under its rows.
  src-under : ∀ {k e x y} → σ k e → Ms x y → (k ⊕ [ ix 0 ]) ⊑ x → ⊥
  src-under {k} sk a kx = ⊑-≼ {k ⊕ [ ix 0 ]} {k} (subst ((k ⊕ [ ix 0 ]) ⊑_) (nu-s sk a (⊑-trans (⊑-snoc⁺ k) kx)) kx) (≺-ext k [])

  none : NoneUnder M T
  none (body x , _)  (inj₂ a)                                 kx = nu-b x a kx
  none (burst x _ , _)  (inj₂ a)                              kx = ⊥-elim (src-b x a kx)
  none (echo x _ _ _ , _)  (inj₂ a)                           kx = ⊥-elim (src-b x a kx)
  none (kept x _ _ _ , _)  (inj₂ a)                           kx = ⊥-elim (src-b x a kx)
  none (body x , _)  (inj₁ (inj₁ (inj₁ (inj₂ a))))            kx = ⊥-elim (body-s x a kx)
  none (burst x _ , _)  (inj₁ (inj₁ (inj₁ (inj₂ a))))         kx = ⊥-elim (src-under x a kx)
  none (echo x _ _ _ , _)  (inj₁ (inj₁ (inj₁ (inj₂ a))))      kx = ⊥-elim (src-under x a kx)
  none (kept x _ _ _ , _)  (inj₁ (inj₁ (inj₁ (inj₂ a))))      kx = ⊥-elim (src-under x a kx)
  none t (inj₁ (inj₂ (refl , _)))                             kx = pairs-none t (inj₂ (inj₂ refl)) kx
  none t (inj₁ (inj₁ (inj₂ (refl , _))))                      kx = pairs-none t (inj₂ (inj₁ refl)) kx
  none t (inj₁ (inj₁ (inj₁ (inj₁ (refl , _)))))               kx = pairs-none t (inj₁ refl) kx

  ----------------------------------------------------------------------
  -- The connect's rows through the body's

  -- A carried row of the connect: the body's; the source shows silent.
  t-body : ∀ {k e} → T k e → Carried e → β k e
  t-body (body x , _) _ = x
  t-body (burst _ _ , _) ()
  t-body (echo _ _ _ _ , _) ()
  t-body (kept _ _ _ _ , _) ()

  t-end : ∀ {k} → T k end → β k end
  t-end x = t-body x c-end

  u-out : ∀ {l b} → U l (out b) → β′ l (out b)
  u-out (body y , _) = y

  u-end : ∀ {l} → U l end → β′ l end
  u-end (body y , _) = y

  -- An elaborated row of the source's.
  FromSrc : ∀ {l e} → U l e → Set
  FromSrc (body _ , _) = ⊥
  FromSrc _            = ⊤

  -- Live in the body: live in the connect, which ends where it does.
  live-β : ∀ {j} → Live β j → Live T j
  live-β l x = l (t-end x)

  IT : InvAt (Hots env) p T
  IT = inv-approx n (connect s b) env ge p ok

  -- What the connect reads, listed up to a bound: listed up to a row up
  -- to it, no hot row lying in its world.
  env-up : ∀ {A′ c k e} → T k e → Upto c k → EnvListed ρ env env′ es T A′ c → EnvListed ρ env env′ es T A′ (just k)
  env-up {A′} x uk = env-row {Γ} {Δ} {λ {X} → ρ {X}} {Amb} {env} {env′} es {T = T} uk (λ i y kh → proj₂ ok (hots-at env i (HotSim.isP (es i)) y) (InvAt.world IT x) (⊑-inside kh)) {A′}

  lst-up : ∀ {c k e} → T k e → Upto c k → ListedB T c → ListedB T (just k)
  lst-up {c} = listed-up (λ {y} {e} {l} {ys} {e′} → InvAt.flat IT {y} {e} {l} {ys} {e′}) c

  -- A BODY ROW UP TO A LISTED BOUND IS THE CONNECT'S: every connect row
  -- before it with few before it is listed, so, the connect showing its
  -- hangs, few connect rows lie before it.
  conn-T : ∀ {c k e} → ListedB T c → ConnT k e → Upto c k → T k e
  conn-T {c} {k} (ks , cov , _) y uk = y , few-reach {t = ConnT} {k} Fk
    where
      led : ∀ {j e′} → ConnT j e′ → Few ConnT j → j ≺ k → j ∈ ks
      led {j} x f lt = cov (x , few-reach {t = ConnT} {j} f) (upto-dn c lt uk)
      nF : ¬ ¬ Few ConnT k
      nF = k-shows (λ m → SC.sk-connT ds F Is p ok (sk-approx m n s env ge r (ok-step p ok))
                     (sk-approx m n b (hot (Proper σ) ∷ᴬ env) (good-cons lawσ ge) p₀ (LC.ok₀ {s = ds} {F = F} Is IF p ok))) (ks , led)
      Fk : Few ConnT k
      Fk = ks , λ {j} x lt → ∈-stable λ ¬m → nF λ F′k → ¬m (led x (few-down F′k (≺→≼ {j} {k} lt)) lt)

  t-mem : ∀ {c k e} → ListedB T c → β k e → Upto c k → T k e
  t-mem lst y uk = conn-T lst (CP.body y) uk

  -- The body's rows up to a listed bound: the listed connect rows that
  -- are the body's, no source row's echo lying at a body row.
  listed-β : ∀ {c} → ListedB T c → ListedB β c
  listed-β {c} lst@(ks , cov , bk) = K.keep ks bk , (λ y uk → K.kept ks bk (cov (t-mem lst y uk) uk) (only y)) , K.kept-row ks bk
    where
      pick : ∀ {k e} → T k e → Maybe (Σ Pos λ j → Σ (Ev B) (β j))
      pick {k} (body y , _) = just (k , _ , y)
      pick _            = nothing
      module K = Keep {t = T} {u = β} pick
      module SS = Side {s = ds} {F = F} Is IF p ok
      only : ∀ {k e} → β k e → ∀ {e′} (x : T k e′) → Σ (Σ (Ev B) (β k)) λ w → pick x ≡ just (k , w)
      only _ (body y , _)          = (_ , y) , refl
      only y (burst x _ , _)       = ⊥-elim (SS.img-body x y (⊑-refl _))
      only y (echo x _ _ _ , _)    = ⊥-elim (SS.img-body x y (⊑-refl _))
      only y (kept x _ _ _ , _)    = ⊥-elim (SS.img-body x y (⊑-refl _))

  -- A carrier under a bound's image is up to the bound.
  under-upto : ∀ {A′} → (Amb ∪ᴹ M) ⊆ᴹ A′ → Emb A′ → ∀ {c} → Mapped A′ c → ∀ {k l} → Run.Img Rb k l → Under A′ c l → Upto c k
  under-upto inc emA {nothing} _ _ _             = tt
  under-upto inc emA {just c}  _ i (_ , ac , u) =
    img-upto emA ac (inc (b⊆M (proj₁ (proj₂ (Run.ext Rb i))))) (proj₂ (proj₂ (Run.ext Rb i))) u

  Iσ : InvAt (Hots env) r σ
  Iσ = Is r (ok-step p ok)

  -- A source row live in the body shows a connect row at its first
  -- child: its burst copy, its echo, or its kept pin, whose connect
  -- leads it and so is live too.
  src-row : ∀ {j e} → σ j e → Live β j → Σ (Ev B) (ConnT (j ⊕ [ ix 0 ]))
  src-row {j} {e} x lv with T-or (inside r j)
  ... | inj₁ i  = pin p , CP.burst x i
  ... | inj₂ ni = quiet e x
    where
      quiet : ∀ e → σ j e → Σ (Ev B) (ConnT (j ⊕ [ ix 0 ]))
      quiet (out _)  x = skip , CP.echo x lv tt ni
      quiet skip     x = skip , CP.echo x lv tt ni
      quiet end      x = skip , CP.echo x lv tt ni
      quiet (pin p″) x = pin p″ , CP.kept x (λ yb → ≼-≺-≺ {p″} {j} (⊑-≼ (inside-⊑ p″ j ins)) (lv yb)) ni ins
        where ins = proj₂ (InvAt.pinned Iσ x)

  -- THE SOURCE'S LISTING THROUGH THE CONNECT: its proper rows up to a
  -- listed bound and live in the body.  Each shows a connect row up to
  -- the bound, so listed; whether a listed source row is live, and
  -- proper, is decided by the listed ends before it.
  listed-σ : ∀ {c} → ListedB T c → ListedL (Proper σ) β c
  listed-σ {c} lst@(ks , cov , bk) = KP.keep cands (KS.kept-row ks bk) , cover , KP.kept-row cands (KS.kept-row ks bk)
    where
      module SS = Side {s = ds} {F = F} Is IF p ok

      -- The source rows behind the listed connect rows.
      pickS : ∀ {q e′} → T q e′ → Maybe (Σ Pos λ j → Σ (Ev A) (σ j))
      pickS (body _ , _)                  = nothing
      pickS (burst {j} {e} x _ , _)       = just (j , e , x)
      pickS (echo {j} {e} x _ _ _ , _)    = just (j , e , x)
      pickS (kept {j} {p″} x _ _ _ , _)   = just (j , pin p″ , x)
      module KS = Keep {t = T} {u = σ} pickS
      cands : L.List Pos
      cands = KS.keep ks bk

      -- The listed ends of the connect, and of the source.
      pickE : ∀ {q e′} → T q e′ → Maybe (Σ Pos λ j → Σ (Ev B) λ _ → T j end)
      pickE {q} {end} x = just (q , end , x)
      pickE {e′ = out _} _ = nothing
      pickE {e′ = skip}  _ = nothing
      pickE {e′ = pin _} _ = nothing
      module KE = Keep {t = T} {u = λ j _ → T j end} pickE
      endsT : L.List Pos
      endsT = KE.keep ks bk

      pickσ : ∀ {q e′} → σ q e′ → Maybe (Σ Pos λ j → Σ (Ev A) λ _ → σ j end)
      pickσ {q} {end} x = just (q , end , x)
      pickσ {e′ = out _} _ = nothing
      pickσ {e′ = skip}  _ = nothing
      pickσ {e′ = pin _} _ = nothing
      module Kσ = Keep {t = σ} {u = λ j _ → σ j end} pickσ
      endsσ : L.List Pos
      endsσ = Kσ.keep cands (KS.kept-row ks bk)

      -- A source row up to the bound and live: listed behind its row.
      in-cands : ∀ {j e} → σ j e → Upto c j → Live β j → j ∈ cands
      in-cands {j} x uj lv = KS.kept ks bk (cov (conn-T lst (proj₂ (src-row x lv)) uj′) uj′) (λ y → only y refl)
        where
          uj′ = upto-next c uj
          only : ∀ {q e′} (y : T q e′) → q ≡ j ⊕ [ ix 0 ] → Σ (Σ (Ev A) (σ j)) λ w → pickS y ≡ just (j , w)
          only (body b′ , _) eq = ⊥-elim (SS.img-body x b′ (subst ((j ⊕ [ ix 0 ]) ⊑_) (sym eq) (⊑-refl _)))
          only (burst {j′} x′ _ , _) eq with ⊕-injˡ j′ j eq
          ... | refl = (_ , x′) , refl
          only (echo {j′} x′ _ _ _ , _) eq with ⊕-injˡ j′ j eq
          ... | refl = (_ , x′) , refl
          only (kept {j′} x′ _ _ _ , _) eq with ⊕-injˡ j′ j eq
          ... | refl = (_ , x′) , refl

      end-T : ∀ {k} → T k end → k ∈ ks → k ∈ endsT
      end-T y m = KE.kept ks bk m (λ x → only x (InvAt.func IT y x))
        where
          only : ∀ {k e} (x : T k e) → end ≡ e → Σ (Σ (Ev B) λ _ → T k end) λ w → pickE x ≡ just (k , w)
          only x refl = (_ , x) , refl

      end-σ : ∀ {k} → σ k end → k ∈ cands → k ∈ endsσ
      end-σ y m = Kσ.kept cands (KS.kept-row ks bk) m (λ x → only x (InvAt.func Iσ y x))
        where
          only : ∀ {k e} (x : σ k e) → end ≡ e → Σ (Σ (Ev A) λ _ → σ k end) λ w → pickσ x ≡ just (k , w)
          only x refl = (_ , x) , refl

      upto-≼ : ∀ {j k} → k ≼ j → Upto c j → Upto c k
      upto-≼ {j} {k} kj uj with ≼-split {k} {j} kj
      ... | inj₁ lt   = upto-dn c lt uj
      ... | inj₂ refl = uj

      -- Live, when no listed connect end lies at or before it.
      live : ∀ {j} → Upto c j → ¬ Any (_≼ j) endsT → Live β j
      live {j} uj nT {k} yb with ≼-or-≻ k j
      ... | inj₂ jk = jk
      ... | inj₁ kj = ⊥-elim (nT (AnyP.map (λ eq → subst (_≼ j) eq kj) (end-T yk (cov yk (upto-≼ kj uj)))))
        where yk = t-mem lst yb (upto-≼ kj uj)

      -- Proper, when no listed source end lies before it.
      proper : ∀ {j e} → σ j e → Upto c j → ¬ Any (_≼ j) endsT → ¬ Any (_≺ j) endsσ → Proper σ j e
      proper {j} x uj nT nσ = x , λ {c′} y′ c′j →
        nσ (AnyP.map (λ eq → subst (_≺ j) eq c′j) (end-σ y′ (in-cands y′ (upto-dn c c′j uj) (λ yb → ≺-trans {c′} {j} c′j (live uj nT yb)))))

      decide : ∀ {j e} → σ j e → Dec (Upto c j) → Dec (Any (_≼ j) endsT) → Dec (Any (_≺ j) endsσ) → Maybe (Σ Pos λ j′ → Σ (Ev A) (Proper σ j′))
      decide {j} {e} x (yes uj) (no nT) (no nσ) = just (j , e , proper x uj nT nσ)
      decide _ (yes _) (yes _) _       = nothing
      decide _ (yes _) (no _)  (yes _) = nothing
      decide _ (no _)  _       _       = nothing

      decide-ok : ∀ {j e} (x : σ j e) d₁ d₂ d₃ → Upto c j → ¬ Any (_≼ j) endsT → ¬ Any (_≺ j) endsσ
                → Σ (Σ (Ev A) (Proper σ j)) λ w → decide x d₁ d₂ d₃ ≡ just (j , w)
      decide-ok x (yes _)  (no _)  (no _)  _  _  _  = _ , refl
      decide-ok x (yes _)  (yes a) _       _  nT _  = ⊥-elim (nT a)
      decide-ok x (yes _)  (no _)  (yes a) _  _  nσ = ⊥-elim (nσ a)
      decide-ok x (no ¬u)  _       _       uj _  _  = ⊥-elim (¬u uj)

      pickP : ∀ {j e} → σ j e → Maybe (Σ Pos λ j′ → Σ (Ev A) (Proper σ j′))
      pickP {j} x = decide x (Upto? c j) (any? (λ k → ¬? (T? (j <ᵖ k))) endsT) (any? (λ k → T? (k <ᵖ j)) endsσ)
      module KP = Keep {t = σ} {u = Proper σ} pickP

      cover : ∀ {j e} → Proper σ j e → Upto c j → Live β j → j ∈ KP.keep cands (KS.kept-row ks bk)
      cover {j} (x , pr) uj lv = KP.kept cands (KS.kept-row ks bk) (in-cands x uj lv) (λ x′ → decide-ok x′ _ _ _ uj nT nσ)
        where
          nT : ¬ Any (_≼ j) endsT
          nT a with find a
          ... | k , m , kj = kj (lv (t-end (proj₂ (KE.kept-row ks bk m))))
          nσ : ¬ Any (_≺ j) endsσ
          nσ a with find a
          ... | k , m , kj = pr (proj₂ (Kσ.kept-row cands (KS.kept-row ks bk) m)) kj

  postulate
    -- THE CONNECT'S LATE PINS, listed: the body's by its run's, the
    -- burst's and the kept's by the source's late pins and its rows.
    conn-late : Lates (Amb ∪ᴹ M) (EnvListed ρ env env′ es T) T U

  postulate
    -- THE ELABORATED CONNECT'S SOURCE ROWS UNDER A BOUND'S IMAGE, listed.
    --
    -- DEAD ROUTE: the source's simulation at a bound the connect's listing
    --   covers.  A kept pin past the body's end waits only on its
    --   subscription's past, so it may follow infinitely many source rows
    --   the connect hides, and no bound reaching it has the source listed;
    --   such pins come from the source's `Run.late` instead.
    src-listed : ∀ A′ → (Amb ∪ᴹ M) ⊆ᴹ A′ → Emb A′ → ∀ c → Mapped A′ c → EnvListed ρ env env′ es T A′ c → ListedB T c
               → Σ (L.List Pos) λ ls → (∀ {l e} (u : U l e) → FromSrc u → Under A′ c l → l ∈ ls) × (∀ {l} → l ∈ ls → Σ (Ev (IE B)) (U l))

  -- What the body reads, from what the connect reads.
  Lb : ∀ {A′ c} → EnvListed ρ env env′ es T A′ c → ListedB T c → EnvListed (ext ρ) env-b env′-b es-b β A′ c
  Lb {A′} {c} L lst = listed-σ lst , env-live {ρ = ρ} {Amb = Amb} {env = env} {env′ = env′} es {T = T} {T′ = β} (λ {j} → live-β {j}) {A′} {c} L

  -- AN ELABORATED BODY ROW UNDER A BOUND'S IMAGE IS THE CONNECT'S: every
  -- elaborated connect row before it is under the image too, so listed —
  -- the body's by the body's simulation, the source's by `src-listed` —
  -- and the elaborated connect shows its hangs.
  u-under : ∀ A′ → (Amb ∪ᴹ M) ⊆ᴹ A′ → Emb A′ → ∀ c → Mapped A′ c → EnvListed ρ env env′ es T A′ c → ListedB T c
          → ∀ {l e} → β′ l e → Under A′ c l → U l e
  u-under A′ inc emA c mp Lr lst {l} y un = CE.body y , few-reach {t = ConnT′} {l} Fl
    where
      hb = Run.sim Rb A′ (λ a → inc (b⊆M a)) emA c mp (Lb {A′} {c} Lr lst) (listed-β lst)
      srcL = src-listed A′ inc emA c mp Lr lst
      ls : L.List Pos
      ls = proj₁ (Sim.upto hb) L.++ proj₁ srcL
      in-ls : ∀ {j e′} → U j e′ → Under A′ c j → j ∈ ls
      in-ls (body y′ , _) uj          = ∈-++⁺ˡ (proj₁ (proj₂ (Sim.upto hb)) y′ uj)
      in-ls u@(burst _ _ , _) uj      = ∈-++⁺ʳ _ (proj₁ (proj₂ srcL) u _ uj)
      in-ls u@(echo _ _ _ _ , _) uj   = ∈-++⁺ʳ _ (proj₁ (proj₂ srcL) u _ uj)
      in-ls u@(kept _ _ _ _ , _) uj   = ∈-++⁺ʳ _ (proj₁ (proj₂ srcL) u _ uj)
      led : ∀ {j e′} → ConnT′ j e′ → Few ConnT′ j → j ≺ l → j ∈ ls
      led {j} x f lt = in-ls (x , few-reach {t = ConnT′} {j} f) (under-down c lt un)
      nF : ¬ ¬ Few ConnT′ l
      nF = k-shows (λ m → SC.sk-connT ds′ F′ Is′ p′ ok′ (sk-approx m n (annotate (elab ρ s)) env′ ge′ r′ (ok-step p′ ok′))
                     (sk-approx m n (elab (ext ρ) b) (hot (Proper σ′) ∷ᴬ env′) (good-cons lawσ′ ge′) p₀′ (LC.ok₀ {s = ds′} {F = F′} Is′ IF′ p′ ok′)))
                   (ls , led)
      Fl : Few ConnT′ l
      Fl = ls , λ {j} x lt → ∈-stable λ ¬m → nF λ F′l → ¬m (led x (few-down F′l (≺→≼ {j} {l} lt)) lt)

  module CSim (A′ : PMap) (inc : (Amb ∪ᴹ M) ⊆ᴹ A′) (emA : Emb A′) (c : Maybe Pos) (mp : Mapped A′ c)
              (Lr : EnvListed ρ env env′ es T A′ c) (lst : ListedB T c) where

    incb : (Amb-b ∪ᴹ Mb) ⊆ᴹ A′
    incb a = inc (b⊆M a)

    hb : Sim Shows Shown A′ (Run.Img Rb) c β β′
    hb = Run.sim Rb A′ incb emA c mp (Lb {A′} {c} Lr lst) (listed-β lst)

    open Sim hb renaming (fwd to fwdb; val← to valb; end← to endb; upto to uptob)

    -- A carried row's image, the connect's: the connect cut at the row.
    fwd : ∀ {k e} → T k e → Carried e → Upto c k → Σ Pos λ l → Run.Img Rb k l × Σ (Ev (IE B)) λ e′ → U l e′ × Mt Shows e e′
    fwd {k} {e} x ce uk = l , i , e′ , u-under A′ inc emA (just k) mk (env-up {A′} {c} x uk Lr) (lst-up x uk lst) y (proj₁ mk , proj₂ mk , inj₂ yl) , mt
      where
        f = fwdb (t-body x ce) ce uk
        l = proj₁ f
        i = proj₁ (proj₂ f)
        e′ = proj₁ (proj₂ (proj₂ f))
        y = proj₁ (proj₂ (proj₂ (proj₂ f)))
        mt = proj₂ (proj₂ (proj₂ (proj₂ f)))
        anc = Run.ext Rb i
        yl = proj₂ (proj₂ anc)
        mk : Mapped A′ (just k)
        mk = proj₁ anc , incb (proj₁ (proj₂ anc))

    val← : ∀ {l b} → U l (out b) → Shown b → Under A′ c l → Σ Pos λ k → Run.Img Rb k l × Σ B λ a → T k (out a) × Shows a b
    val← y sh un = proj₁ v , proj₁ (proj₂ v) , proj₁ (proj₂ (proj₂ v))
                 , t-mem lst (proj₁ (proj₂ (proj₂ (proj₂ v)))) (under-upto inc emA mp (proj₁ (proj₂ v)) un) , proj₂ (proj₂ (proj₂ (proj₂ v)))
      where v = valb (u-out y) sh un

    end← : ∀ {l} → U l end → Under A′ c l → Σ Pos λ k → Run.Img Rb k l × T k end
    end← y un = proj₁ v , proj₁ (proj₂ v) , t-mem lst (proj₂ (proj₂ v)) (under-upto inc emA mp (proj₁ (proj₂ v)) un)
      where v = endb (u-end y) un

    under-dec = under? {A′} (λ {x} {y} {y′} → Emb.fun emA {x} {y} {y′}) c mp

    srcL = src-listed A′ inc emA c mp Lr lst

    upto : Σ (L.List Pos) λ ls → (∀ {l e′} → U l e′ → Under A′ c l → l ∈ ls) × (∀ {l} → l ∈ ls → Σ (Ev (IE B)) (U l))
    upto = filter under-dec (proj₁ uptob) L.++ proj₁ srcL , cov , back
      where
        cov : ∀ {l e′} → U l e′ → Under A′ c l → l ∈ (filter under-dec (proj₁ uptob) L.++ proj₁ srcL)
        cov (body y , rc) un            = ∈-++⁺ˡ (∈-filter⁺ under-dec (proj₁ (proj₂ uptob) y un) un)
        cov u@(burst _ _ , _) un        = ∈-++⁺ʳ _ (proj₁ (proj₂ srcL) u _ un)
        cov u@(echo _ _ _ _ , _) un     = ∈-++⁺ʳ _ (proj₁ (proj₂ srcL) u _ un)
        cov u@(kept _ _ _ _ , _) un     = ∈-++⁺ʳ _ (proj₁ (proj₂ srcL) u _ un)

        fromB : ∀ {l} → l ∈ filter under-dec (proj₁ uptob) → Σ (Ev (IE B)) (U l)
        fromB m′ = let (m″ , un) = ∈-filter⁻ under-dec m′ in
                   proj₁ (proj₂ (proj₂ uptob) m″) , u-under A′ inc emA c mp Lr lst (proj₂ (proj₂ (proj₂ uptob) m″)) un

        back : ∀ {l} → l ∈ (filter under-dec (proj₁ uptob) L.++ proj₁ srcL) → Σ (Ev (IE B)) (U l)
        back m = [ fromB , proj₂ (proj₂ srcL) ]′ (∈-++⁻ (filter under-dec (proj₁ uptob)) m)

    sim : Sim Shows Shown A′ (Run.Img Rb) c T U
    sim = record { fwd = fwd ; val← = val← ; end← = end← ; upto = upto }

  anchor : ∀ A′ → (Amb ∪ᴹ M) ⊆ᴹ A′ → Emb A′ → ∀ {k e} → T k e → Carried e → EnvListed ρ env env′ es T A′ (just k)
         → ListedB T (just k) → Σ Pos ((Amb ∪ᴹ M) k)
  anchor A′ inc emA {k} x ce L lst = proj₁ a , b⊆M (proj₂ a)
    where a = Run.anchor Rb A′ (λ a → inc (b⊆M a)) emA (t-body x ce) ce (Lb {A′} {just k} L lst) (listed-β lst)

  run : Run Shows Shown (Amb ∪ᴹ M) (EnvListed ρ env env′ es T) T U
  run = record
    { Img     = Run.Img Rb
    ; img-fun = Run.img-fun Rb
    ; ext     = λ i → proj₁ (Run.ext Rb i) , b⊆M (proj₁ (proj₂ (Run.ext Rb i))) , proj₂ (proj₂ (Run.ext Rb i))
    ; sim     = λ A′ inc emA c mp L lst → CSim.sim A′ inc emA c mp L lst
    ; late    = conn-late
    ; anchor  = anchor
    }

  result : Σ PMap λ M′ → Local (Hots env) (Hots env′) p p′ M′ × Emb (Amb ∪ᴹ M′) × NoneUnder M′ T
           × EnvJoins ρ env env′ es M′ × Run Shows Shown (Amb ∪ᴹ M′) (EnvListed ρ env env′ es T) T U
  result = M , local , emb , none , env-joins , run

-- THE FORMER.
sim-connect : ∀ n {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B)
            → SimIH n ρ s → (∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE (A ∷ Γ) → X ∈ Δ′) → SimIH n ρ′ b) → SimIH n ρ (connect s b)
sim-connect n ρ s b ihs ihb = sih λ env env′ Amb ge ge′ ap es en em p p′ pp fr ok ok′ nh →
  Conn.result n ρ s b ihs ihb env env′ Amb ge ge′ ap es en em p p′ pp fr ok ok′ nh
