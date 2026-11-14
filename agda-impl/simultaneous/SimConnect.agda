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
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁺; ∈-filter⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; connect)
open import denotation.Position using (Pos; root; _≟ᵖ_; _⊕_; ix; last)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; end; EmissionSet; Den; hot; DenEnv; Proper; enter; approx; module Connect)
open import denotation.Laws using (inv-approx; good-cons)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; Lawful; InvD; InvAt; _∪ʰ_; ok-step; here; _⊑_; ⊑-snoc⁺; ⊑-trans; ⊑-≼; ⊑-inside)
import denotation.Laws.Connect as LC
open import simultaneous.SObs using (lone; module Elaborate; ext)
open import simultaneous.Sim using (PMap; _∪ᴹ_; _⊆ᴹ_; Emb; Below; Fresh; Local; NoneUnder; Sim; Run; Mt; Carried; c-end; Upto;
  Under; Mapped; ListedB; ListedL; Live; Allᴱ; EndsAfter; env-live; Joins; Shows; Shown; AShows;
  AShown; HotSim; EnvSim; EnvListed; EnvNeeds; EnvJoins; Apart; SimIH; sih)
open import simultaneous.ReadMap using (under?; upto-dn; listed-up)
open import simultaneous.SimReader using (hots-at)
open import simultaneous.SimPos using (UpTo)
open import simultaneous.AnnRun using (module AnnRun)

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

  postulate
    -- THE LISTINGS THROUGH THE CONNECT: its rows up to a bound listed, the
    -- body's are, and the source's still live in the body.
    listed-β : ∀ {c} → ListedB T c → ListedB β c
    listed-σ : ∀ {c} → ListedB T c → ListedL (Proper σ) β c
    -- A body row up to a listed bound is the connect's.
    t-mem : ∀ {c k e} → ListedB T c → β k e → Upto c k → T k e
    -- A carrier under a bound's image is up to the bound.
    under-upto : ∀ {A′} → (Amb ∪ᴹ M) ⊆ᴹ A′ → Emb A′ → ∀ {c} → Mapped A′ c → ∀ {k l} → Run.Img Rb k l → Under A′ c l → Upto c k
    -- THE ELABORATED CONNECT'S ROWS UNDER A BOUND'S IMAGE: a body row is
    -- the connect's, and the source's are listed.
    u-under : ∀ A′ → (Amb ∪ᴹ M) ⊆ᴹ A′ → Emb A′ → ∀ c → Mapped A′ c → EnvListed ρ env env′ es T A′ c → ListedB T c
            → ∀ {l e} → β′ l e → Under A′ c l → U l e
    src-listed : ∀ A′ → (Amb ∪ᴹ M) ⊆ᴹ A′ → Emb A′ → ∀ c → Mapped A′ c → EnvListed ρ env env′ es T A′ c → ListedB T c
               → Σ (L.List Pos) λ ls → (∀ {l e} (u : U l e) → FromSrc u → Under A′ c l → l ∈ ls) × (∀ {l} → l ∈ ls → Σ (Ev (IE B)) (U l))
    -- RECOVERY: git show a0945587^:agda-impl/simultaneous/ToldRows.agda
    --   restores told-listed←, for listed-σ: the source listed under a told
    --   row's listing.

  -- What the body reads, from what the connect reads.
  Lb : ∀ {A′ c} → EnvListed ρ env env′ es T A′ c → ListedB T c → EnvListed (ext ρ) env-b env′-b es-b β A′ c
  Lb {A′} {c} L lst = listed-σ lst , env-live {ρ = ρ} {Amb = Amb} {env = env} {env′ = env′} es {T = T} {T′ = β} (λ {j} → live-β {j}) {A′} {c} L

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
