{-# OPTIONS --guardedness #-}

-- THE ERASURE'S ROW FACTS, CARRIED FROM THE APPROXIMANTS TO THE MEANING.
-- At each approximant the elaborated run carries the plain one
-- (`erasingₙ`), so there the i-th value is the i-th, at one rank, its
-- instant over exactly when the other's is, and either side ends exactly
-- when the other does.  Each fact reaches the meaning by the
-- approximants' truth (`denotation.Laws.Truthful`): a row of the meaning
-- with finitely many before it is a row of every deep enough approximant,
-- its past too, and a row an approximant shows is the meaning's.
--
-- An instant's being over looks past its row, so it carries by its exit:
-- a reached row of a later instant, read off that instant's first row;
-- the end, a row shown; or a finite run, which is all of the meaning.
module simultaneous.Approximants where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.Any as Any
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _≤_; _⊔_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable.Core using (T?)

open import Tree using (Obs)
open import denotation.Position using (Pos; root; ix; instant; _≟ᵖ_; _≟ⁱ_; _<ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; end; pin; Unpinned; EmissionSet; Few; Seen; Proper; _≺_; _≼_; module Values; enter; approx; ⟦_⟧)
open import denotation.Read using (Visible)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; AgreeTo-sym; ≼-refl; ≺→≼; ≼-trans; ≼-split; ≼-or-≻; ≺-≼-≺; ≼-≺-≺; entered-reach)
open import denotation.Laws.Worlds using (Ok; Hots; InvAt; ⊑-refl; ⊑-≼; inside-⊑)
open import denotation.Laws.ConnectNe using (proper-ag)
open import denotation.Laws.Join using (module Join)
open import denotation.Laws.Nth using (module Nths)
open import denotation.Laws using (inv-approx; inv-⟦⟧) renaming (from to within)
open import denotation.Laws.Truthful using (Opens; Finite; few-ag; reached; never-lies; finite-true)
open import simultaneous.InstEmit using (instEmit; value; mark; valuesOf)
open import simultaneous.SObs using (SObs; plain; module Elaborate)
open import simultaneous.Instants using (_≺ⁱ_; ≺-instant; instant-≺)
open import simultaneous.Relations using (Rank; Before; Over; Left; elaborated; events)
open import simultaneous.Ranks using (enter-few; visible-unpinned)
open import simultaneous.Listing using (Listing; listedₙ)
open import simultaneous.Reach using (module Reached)
open import simultaneous.Attribution using (Live; Single; V; vrow; Attribution; Every; One; Reads; module Attributed)
open import simultaneous.Carry using (Carry; At₀; emb-At₀; fresh-At₀; coreAt; attributed; carry-wrap)
open import simultaneous.Carried using (carry-approx)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) using (IE; elaborate)
open Values using (Nth)
open Equivalence using (to; from)

private
  ok₀ : Ok (Hots []) root
  ok₀ = tt , λ ()

------------------------------------------------------------------------
-- What an agreement carries

module _ {X : Set} {Q : Pos} {t t′ : EmissionSet X} (ag : AgreeTo Q t t′) where
  private
    fwd : ∀ {y e} → y ≼ Q → t y e → t′ y e
    fwd {y} yQ = proj₁ (upto ag {y} yQ)

    bwd : ∀ {y e} → y ≼ Q → t′ y e → t y e
    bwd {y} yQ = proj₂ (upto ag {y} yQ)

    under : ∀ {y k} → y ≺ k → k ≼ Q → y ≼ Q
    under {y} {k} yk kQ = ≺→≼ {y} {Q} (≺-≼-≺ {y} {k} {Q} yk kQ)

    before-to : ∀ {u u′ : EmissionSet X} {k i} → (∀ {y e} → y ≺ k → u y e → u′ y e) → Before u k i → Before u′ k i
    before-to tr (ne , inj₁ fr)                  = ne , inj₁ fr
    before-to tr (ne , inj₂ (k′ , e , x , lt , eq)) = ne , inj₂ (k′ , e , tr lt x , lt , eq)

  v-ag : ∀ {A : Set} (f : X → List A) → AgreeTo Q (V f t) (V f t′)
  v-ag f = ⟨ (λ yQ → (λ { (vrow r fx) → vrow (fwd yQ r) fx }) , (λ { (vrow r fx) → vrow (bwd yQ r) fx })) ⟩

  nth-ag : ∀ {A : Set} (f : X → List A) {i k a} → k ≼ Q → Nth (V f t) i k a → Nth (V f t′) i k a
  nth-ag {A} f kQ n = Join.BoundedJ.nth-to {A} {A} Q 0 (v-ag f) kQ n

  live-ag : ∀ {k} → k ≼ Q → Live t k → Live t′ k
  live-ag {k} kQ lk {c} x with ≼-or-≻ c Q
  ... | inj₁ cQ = lk (bwd cQ x)
  ... | inj₂ Qc = ≺→≼ {k} {c} (≼-≺-≺ {k} {Q} {c} kQ Qc)

  rank-ag : ∀ {k n} → k ≼ Q → Rank t k n → Rank t′ k n
  rank-ag {k} kQ (is , ap , len , h) =
    is , ap , len , mk⇔ (λ m → before-to (λ {y} yk → fwd (under {y} {k} yk kQ)) (to h m))
                        (λ b → from h (before-to (λ {y} yk → bwd (under {y} {k} yk kQ)) b))

  seen-ag : ∀ {k e} → k ≼ Q → Seen t k e → Seen t′ k e
  seen-ag {k} kQ (pr , F) = proj₁ (upto (proper-ag ag) {k} kQ) pr , few-ag ag kQ F

------------------------------------------------------------------------
-- Finitely many rows, and an instant's first

-- Few before a row, finitely many after: finitely many in all.
finite-of : ∀ {X} {u : EmissionSet X} {q ks} → Few u q → (∀ {k e} → u k e → q ≺ k → k ∈ ks) → Finite u
finite-of {u = u} {q} {ks} (ps , h) h′ = ps ++ q ∷ ks , place
  where
    place : ∀ {k e} → u k e → k ∈ ps ++ q ∷ ks
    place {k} x with ≼-or-≻ k q
    ... | inj₂ qk = ∈-++⁺ʳ ps (there (h′ x qk))
    ... | inj₁ kq with ≼-split {k} {q} kq
    ...   | inj₁ lt   = ∈-++⁺ˡ (h x lt)
    ...   | inj₂ refl = ∈-++⁺ʳ ps (here refl)

module _ {X : Set} {u : EmissionSet X} where
  private
    Least : Pos → List Pos → Set
    Least w ks = Σ Pos λ f₁ → Σ (Ev X) (u f₁) × instant f₁ ≡ instant w × f₁ ≼ w × (∀ {m} → m ∈ ks → instant m ≡ instant w → f₁ ≼ m)

    least : ∀ {w ew} → u w ew → (ks : List Pos) → (∀ {m} → m ∈ ks → m ≺ w × Σ (Ev X) (u m)) → Least w ks
    least {w} {ew} uw [] _ = w , (ew , uw) , refl , ≼-refl {w} , λ ()
    least {w} uw (m ∷ ks) s with least uw ks (λ i → s (there i)) | instant m ≟ⁱ instant w
    ... | f₁ , xf , if , fw , all | no ne = f₁ , xf , if , fw , λ { (here refl) im → ⊥-elim (ne im) ; (there i) im → all i im }
    ... | f₁ , xf , if , fw , all | yes im with T? (m <ᵖ f₁)
    ...   | yes mf = m , proj₂ (s (here refl)) , im , ≺→≼ {m} {w} (proj₁ (s (here refl))) ,
      λ { (here refl) _ → ≼-refl {m} ; {m′} (there i) im′ → ≼-trans {m} {f₁} {m′} (≺→≼ {m} {f₁} mf) (all i im′) }
    ...   | no nf = f₁ , xf , if , fw , λ { (here refl) _ → nf ; (there i) im′ → all i im′ }

  -- Where finitely many rows precede and they are listed, a row's instant
  -- has a first row.
  opening : Listing u → ∀ {w ew} → u w ew → Few u w
          → Σ Pos λ f₁ → Σ (Ev X) (u f₁) × instant f₁ ≡ instant w × f₁ ≼ w × Opens u f₁
  opening lst {w} uw F with lst F
  ... | ks , cover , sound with least uw ks sound
  ...   | f₁ , xf , if , fw , all = f₁ , xf , if , fw , op
    where
      op : Opens u f₁
      op {k} x ik with ≼-or-≻ w k
      ... | inj₁ wk = ≼-trans {f₁} {w} {k} fw wk
      ... | inj₂ kw = all (cover x kw) (trans ik if)

------------------------------------------------------------------------
-- A closed program's approximants and its meaning

module Toward {A : Set} (s : Obs Timeline [] A) where
  t : EmissionSet A
  t = enter (⟦ s ⟧ []) root

  tₙ : ℕ → EmissionSet A
  tₙ n = enter (approx n s []) root

  -- Up to a row with finitely many before it: every deep enough approximant.
  reach : ∀ {q} → Few t q → Σ ℕ λ N → ∀ m → N ≤ m → AgreeTo q t (tₙ m)
  reach = reached s [] (λ ()) root ok₀

  down : ∀ {q e} → t q e → Visible e → Σ ℕ λ N → ∀ m → N ≤ m → AgreeTo q t (tₙ m)
  down x v = reach (enter-few (⟦ s ⟧ []) root x (visible-unpinned v))

  -- A row an approximant shows: the meaning's, its past too.
  up : ∀ n {q e} → tₙ n q e → Visible e → AgreeTo q (tₙ n) t
  up n x v = never-lies n s [] (λ ()) root ok₀ (enter-few (approx n s []) root x (visible-unpinned v)) (inj₂ (_ , x , v))

  private
    left-down : ∀ {B : Set} (f : A → List B) {q} → Left f t q → ∀ m → Left f (tₙ m) q
    left-down f lf m {k} x qk ik = lf (proj₁ (upto (up m x tt) {k} (≼-refl {k})) x) qk ik

  -- AN INSTANT OVER IN THE MEANING is over in every deep enough approximant.
  over-down : ∀ {B : Set} (f : A → List B) {q x} → t q (out x) → Over f t (just q)
            → Σ ℕ λ N → ∀ m → N ≤ m → Over f (tₙ m) (just q)
  over-down f tq (lf , inj₁ (k , e , sn , qk , d)) with reach (proj₂ sn)
  ... | N , ag = N , λ m le → left-down f lf m , inj₁ (k , e , seen-ag (ag m le) (≼-refl {k}) sn , qk , d)
  over-down f {q} tq (lf , inj₂ (ks , h)) = length L , λ m le → left-down f lf m , inj₂ (ks , spent m le)
    where
      fin : Finite t
      fin = finite-of (enter-few (⟦ s ⟧ []) root tq tt) (λ x qk → proj₁ (h x qk))

      L : List Pos
      L = proj₁ fin

      same : ∀ m → length L ≤ m → ∀ {y e} → (t y e → tₙ m y e) × (tₙ m y e → t y e)
      same m le {y} {e} = within m s [] (λ ()) root ok₀ y e (inj₁ (L , le , λ x _ _ → inj₂ (Any.map (λ { refl → ⊑-refl _ }) (proj₂ fin x))))

      spent : ∀ m → length L ≤ m → ∀ {k e} → tₙ m k e → q ≺ k → k ∈ ks × Proper (tₙ m) k e
      spent m le {k} x qk with h (proj₂ (same m le) x) qk
      ... | mk , pr = mk , proj₁ (upto (proper-ag ⟨ (λ _ → same m le) ⟩) {k} (≼-refl {k})) pr

  -- AN INSTANT OVER IN AN APPROXIMANT is over in the meaning.
  over-up : ∀ {B : Set} (f : A → List B) n {q x} → tₙ n q (out x) → Over f (tₙ n) (just q) → Over f t (just q)
  over-up f n {q} tq (lf , inj₁ (k₁ , e₁ , sn@((tk₁ , pr₁) , F₁) , qk₁ , inj₂ refl)) =
    left , inj₁ (k₁ , end , seen-ag ag₁ (≼-refl {k₁}) sn , qk₁ , inj₂ refl)
    where
      ag₁ : AgreeTo k₁ (tₙ n) t
      ag₁ = up n tk₁ tt

      left : Left f t q
      left {k} x qk ik with ≼-or-≻ k k₁
      ... | inj₁ kk₁ = lf (proj₂ (upto ag₁ {k} kk₁) x) qk ik
      ... | inj₂ k₁k with InvAt.quiet (inv-⟦⟧ s [] (λ ()) root ok₀) (proj₁ (upto ag₁ {k₁} (≼-refl {k₁})) tk₁) x k₁k
      ...   | _ , () , _
  over-up f n {q} tq (lf , inj₁ (k₁ , e₁ , ((tk₁ , pr₁) , F₁) , qk₁ , inj₁ ne)) = at-first (opening (listedₙ n s) tk₁ F₁)
    where
      later₁ : instant q ≺ⁱ instant k₁
      later₁ = ≺-instant q k₁ qk₁ (λ eq → ne (sym eq))

      at-first : (Σ Pos λ f₁ → Σ (Ev A) (tₙ n f₁) × instant f₁ ≡ instant k₁ × f₁ ≼ k₁ × Opens (tₙ n) f₁) → Over f t (just q)
      at-first (f₁ , (e′ , xf) , if , fk₁ , opens) = left , inj₁ (f₁ , e′ , seen-ag ag₁ (≼-refl {f₁}) sn₁ , instant-≺ q f₁ later , inj₁ nf₁)
        where
          F₁′ : Few (tₙ n) f₁
          F₁′ = proj₁ F₁ , λ {k} x kf → proj₂ F₁ x (≺-≼-≺ {k} {f₁} {k₁} kf fk₁)

          ag₁ : AgreeTo f₁ (tₙ n) t
          ag₁ = never-lies n s [] (λ ()) root ok₀ F₁′ (inj₁ opens)

          sn₁ : Seen (tₙ n) f₁ e′
          sn₁ = (xf , λ {c} xc → ≼-trans {f₁} {k₁} {c} fk₁ (pr₁ xc)) , F₁′

          later : instant q ≺ⁱ instant f₁
          later = subst (instant q ≺ⁱ_) (sym if) later₁

          nf₁ : instant f₁ ≢ instant q
          nf₁ eq = ne (trans (sym if) eq)

          left : Left f t q
          left {k} x qk ik = lf (proj₂ (upto ag₁ {k} (≺→≼ {k} {f₁} (instant-≺ k f₁ (subst (_≺ⁱ instant f₁) (sym ik) later)))) x) qk ik
  over-up f n {q} tq (lf , inj₂ (ks , h)) =
    (λ x qk ik → lf (proj₂ eq x) qk ik) ,
    inj₂ (ks , λ {k} x qk → proj₁ (h (proj₂ eq x) qk) , proj₁ (upto (proper-ag ⟨ (λ _ → eq) ⟩) {k} (≼-refl {k})) (proj₂ (h (proj₂ eq x) qk)))
    where
      eq : ∀ {y e} → (tₙ n y e → t y e) × (t y e → tₙ n y e)
      eq = finite-true n s [] (λ ()) root ok₀ (finite-of (enter-few (approx n s []) root tq tt) (λ x qk → proj₁ (h x qk)))

------------------------------------------------------------------------
-- The erasure at each approximant

-- One value or none off each elaborated emit.
single-values : ∀ {A} → Single {IE A} valuesOf
single-values (instEmit (value a) _) = inj₂ (a , refl)
single-values (instEmit (mark _) _)  = inj₁ refl

-- A pin waits on every row before its connect.
pin-fewₙ : ∀ n {A} (o : SObs [] A) {k p} → enter (approx n (plain o) []) root k (pin p) → Few (enter (approx n (plain o) []) root) p
pin-fewₙ n o {k} {p} tk with entered-reach (approx n (plain o) []) root tk | proj₂ (InvAt.pinned (inv-approx n (plain o) [] (λ ()) root ok₀) tk)
... | ks , F | i = ks , λ {x} tx xp → F tx (≺-≼-≺ {x} {p} {k} xp (⊑-≼ (inside-⊑ p k i))) (λ _ → inj₁ xp)

-- A plain row that is not a pin is at or before every end.
unpinned-liveₙ : ∀ n {A} (o : SObs [] A) {k e} → enter (approx n (plain o) []) root k e → Unpinned e → Live (enter (approx n (plain o) []) root) k
unpinned-liveₙ n o tk up {c} tc ck with InvAt.quiet (inv-approx n (plain o) [] (λ ()) root ok₀) tc tk ck
... | r , refl , _ = up

-- THE ELABORATION CARRIES THE PLAIN RUN, at each approximant: each
-- unpinned plain row at or before the end is carried by the elaborated
-- row elaborating it, a value by its value and the end by the end, in
-- order, instant for instant.  The elaboration adds no instant and holds
-- no value; switch, exhaust and the bounded queue are the real cases.
--
-- REFUTED: e10449e the ranks agreeing, with a rank counting only instants
--   holding rows: a run with no row in the subscribe frame ranks its
--   values one below its elaboration, whose subscribed mark lies there.
-- DEAD ROUTE: carrying every row, past the ends too.  A connect whose
--   body ends at once puts its source's burst pins past its end in the
--   subscribe frame, and the elaboration's end is that frame's last row:
--   no elaborated row lies past it to carry them in order.
-- DEAD ROUTE: carrying the pins in order.  Concat's elaboration
--   subscribes a queued lane under its own readers, so a pin of a later
--   lane's subscribe can fall past a value the plain run puts after it:
--   no elaborated row carries it in order.  A pin is carried only into
--   its instant, which is all a rank or an exit reads of it.
-- DEAD ROUTE: carrying the meaning directly, as the approximants' limit.
--   Each approximant's carry picks its own map and image; nothing makes
--   them agree from one index to the next, and an image is not fixed by
--   the fields (a plain skip may sit on any unshown elaborated row of its
--   instant), so no limit carry is assembled from them.
-- REFUTED: 711567f3 finitely many elaborated rows past every plain row's
--   carrier, outright: a connect whose source is an endless synchronous
--   burst under a silent body leaves endlessly many elaborated rows past
--   each; finitely many follow only a plain row past which finitely many
--   do.
-- REFUTED: 711567f3 every elaborated row put on a plain row or ahead of
--   all: under `connect (of [1]) (λ _ → ones)` a pin lies past endlessly
--   many carriers, so no reader reaches it to put it anywhere; only rows
--   a reader reaches are placed, each in the instant of a carrier.
erasingₙ : ∀ n {A} (o : SObs [] A)
         → Attribution Every (One valuesOf) (Reads valuesOf) (enter (approx n (plain o) []) root) (enter (approx n (elaborate (plain o)) []) root) root root
erasingₙ n o with Carry.carries (carry-approx n (λ i → i) (plain o)) [] [] (λ ()) (λ ()) At₀ emb-At₀ (λ ())
                    root coreAt (coreAt , (refl , refl) , ([] , refl)) ok₀ (tt , λ ()) fresh-At₀
... | M , ms , hm , _ , c =
  attributed hm (InvAt.flat (inv-approx n (plain o) [] (λ ()) root ok₀)) (InvAt.func (inv-approx n (plain o) [] (λ ()) root ok₀))
    (listedₙ n (plain o)) (pin-fewₙ n o) (ix 0 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ []) (ms (refl , refl))
    (carry-wrap n o hm (ms (refl , refl)) c)

private
  module Erₙ (n : ℕ) {A : Set} (o : SObs [] A) =
    Attributed {A} {IE A} {valuesOf} single-values {enter (approx n (plain o) []) root} {enter (approx n (elaborate (plain o)) []) root}
      (λ {y} {e} {e′} → InvAt.func (inv-approx n (plain o) [] (λ ()) root ok₀) {y} {e} {e′})
      (λ {y} {e} {e′} → InvAt.func (inv-approx n (elaborate (plain o)) [] (λ ()) root ok₀) {y} {e} {e′})
      (λ {k} {e} → Reached.seen (approx n (plain o) []) root (inv-approx n (plain o) [] (λ ()) root ok₀) {k} {e})
      (λ {k} {e} → Reached.seen (approx n (elaborate (plain o)) []) root (inv-approx n (elaborate (plain o)) [] (λ ()) root ok₀) {k} {e})
      (λ {k} {e} → enter-few (approx n (plain o) []) root {k} {e}) (λ {k} {e} → unpinned-liveₙ n o {k} {e})
      (λ {q} → listedₙ n (plain o) {q}) (λ {q} → listedₙ n (elaborate (plain o)) {q})
      (erasingₙ n o)

------------------------------------------------------------------------
-- The erasure in the meaning

-- An elaborated program's values, and its plain program's.
VX : ∀ {A} → SObs [] A → EmissionSet A
VX o = V valuesOf (elaborated o)

VE : ∀ {A} → SObs [] A → EmissionSet A
VE o = V [_] (events o)

-- THE I-TH VALUE IS THE I-TH: before each side's end, the elaborated
-- program's i-th value is its plain program's, at the same rank, its
-- instant over exactly when the other's is; and each side reaches an end
-- exactly when the other does.
module _ {A : Set} (o : SObs [] A) where
  private
    module TE = Toward (plain o)
    module TX = Toward (elaborate (plain o))

    -- A common depth past two.
    past₂ : ∀ N₁ N₂ → N₁ ≤ N₁ ⊔ N₂ × N₂ ≤ N₁ ⊔ N₂
    past₂ N₁ N₂ = m≤m⊔n N₁ N₂ , m≤n⊔m N₁ N₂

  erase-x : ∀ {i k a} → Nth (VX o) i k a → Live (elaborated o) k → Σ Pos λ k′ → Nth (VE o) i k′ a × Live (events o) k′
  erase-x {k = k} nx lx with Nths.nth-val (VX o) nx
  ... | vrow r _ with TX.down r tt
  ...   | N , ag with Erₙ.values-ut N o (nth-ag (ag N ≤-refl) valuesOf (≼-refl {k}) nx) (live-ag (ag N ≤-refl) (≼-refl {k}) lx)
  ...     | k′ , ne , le with Nths.nth-val (V [_] (TE.tₙ N)) ne
  ...       | vrow r′ refl = k′ , nth-ag (TE.up N r′ tt) [_] (≼-refl {k′}) ne , live-ag (TE.up N r′ tt) (≼-refl {k′}) le

  erase-e : ∀ {i k′ a} → Nth (VE o) i k′ a → Live (events o) k′ → Σ Pos λ k → Nth (VX o) i k a × Live (elaborated o) k
  erase-e {k′ = k′} ne le with Nths.nth-val (VE o) ne
  ... | vrow r refl with TE.down r tt
  ...   | N , ag with Erₙ.values-tu N o (nth-ag (ag N ≤-refl) [_] (≼-refl {k′}) ne) (live-ag (ag N ≤-refl) (≼-refl {k′}) le)
  ...     | k , nx , lx with Nths.nth-val (V valuesOf (TX.tₙ N)) nx
  ...       | vrow r′ _ = k , nth-ag (TX.up N r′ tt) valuesOf (≼-refl {k}) nx , live-ag (TX.up N r′ tt) (≼-refl {k}) lx

  erase-rank : ∀ {i k k′ a b n} → Nth (VX o) i k a → Live (elaborated o) k → Nth (VE o) i k′ b → Live (events o) k′
             → Rank (elaborated o) k n → Rank (events o) k′ n
  erase-rank {k = k} {k′} {n = n} nx _ ne _ r with Nths.nth-val (VX o) nx | Nths.nth-val (VE o) ne
  ... | vrow rx _ | vrow re refl with TX.down rx tt | TE.down re tt
  ...   | N₁ , agX | N₂ , agE = at (agX (N₁ ⊔ N₂) (proj₁ (past₂ N₁ N₂))) (agE (N₁ ⊔ N₂) (proj₂ (past₂ N₁ N₂)))
    where
      at : ∀ {m} → AgreeTo k (elaborated o) (TX.tₙ m) → AgreeTo k′ (events o) (TE.tₙ m) → Rank (events o) k′ n
      at {m} aX aE with Erₙ.nth-ut m o (nth-ag aX valuesOf (≼-refl {k}) nx)
      ... | k₀ , ak , nk with Nths.nth-fun (V [_] (TE.tₙ m)) nk (nth-ag aE [_] (≼-refl {k′}) ne)
      ...   | refl = rank-ag (AgreeTo-sym aE) (≼-refl {k′}) (Erₙ.rank-v m o (nth-ag aX valuesOf (≼-refl {k}) nx) ak (rank-ag aX (≼-refl {k}) r))

  erase-over : ∀ {i k k′ a b} → Nth (VX o) i k a → Live (elaborated o) k → Nth (VE o) i k′ b → Live (events o) k′
             → Over valuesOf (elaborated o) (just k) ⇔ Over [_] (events o) (just k′)
  erase-over {k = k} {k′} nx _ ne _ with Nths.nth-val (VX o) nx | Nths.nth-val (VE o) ne
  ... | vrow {x = x} rx fx | vrow re refl with TX.down rx tt | TE.down re tt
  ...   | N₁ , agX | N₂ , agE = mk⇔ to′ from′
    where
      at : ∀ {m} → AgreeTo k (elaborated o) (TX.tₙ m) → AgreeTo k′ (events o) (TE.tₙ m)
         → Over valuesOf (TX.tₙ m) (just k) ⇔ Over [_] (TE.tₙ m) (just k′)
      at {m} aX aE with Erₙ.nth-ut m o (nth-ag aX valuesOf (≼-refl {k}) nx)
      ... | k₀ , ak , nk with Nths.nth-fun (V [_] (TE.tₙ m)) nk (nth-ag aE [_] (≼-refl {k′}) ne)
      ...   | refl = Erₙ.over-ut m o ak (proj₁ (upto aX {k} (≼-refl {k})) rx) (_ , fx) (proj₁ (upto aE {k′} (≼-refl {k′})) re)

      -- Past both values' depths and a third.
      deep : ∀ N₃ → let m = (N₁ ⊔ N₂) ⊔ N₃ in N₁ ≤ m × N₂ ≤ m × N₃ ≤ m
      deep N₃ = ≤-trans (proj₁ (past₂ N₁ N₂)) (m≤m⊔n (N₁ ⊔ N₂) N₃) , ≤-trans (proj₂ (past₂ N₁ N₂)) (m≤m⊔n (N₁ ⊔ N₂) N₃) , m≤n⊔m (N₁ ⊔ N₂) N₃

      to′ : Over valuesOf (elaborated o) (just k) → Over [_] (events o) (just k′)
      to′ ov with TX.over-down valuesOf rx ov
      ... | N₃ , od with deep N₃
      ...   | l₁ , l₂ , l₃ =
        TE.over-up [_] ((N₁ ⊔ N₂) ⊔ N₃) (proj₁ (upto (agE _ l₂) {k′} (≼-refl {k′})) re) (to (at (agX _ l₁) (agE _ l₂)) (od _ l₃))

      from′ : Over [_] (events o) (just k′) → Over valuesOf (elaborated o) (just k)
      from′ ov with TE.over-down [_] re ov
      ... | N₃ , od with deep N₃
      ...   | l₁ , l₂ , l₃ =
        TX.over-up valuesOf ((N₁ ⊔ N₂) ⊔ N₃) (proj₁ (upto (agX _ l₁) {k} (≼-refl {k})) rx) (from (at (agX _ l₁) (agE _ l₂)) (od _ l₃))

  erase-end : (Σ Pos λ c → elaborated o c end × Live (elaborated o) c) ⇔ (Σ Pos λ c′ → events o c′ end × Live (events o) c′)
  erase-end = mk⇔ to′ from′
    where
      to′ : (Σ Pos λ c → elaborated o c end × Live (elaborated o) c) → Σ Pos λ c′ → events o c′ end × Live (events o) c′
      to′ (c , xc , lc) with TX.down xc tt
      ... | N , ag with to (Erₙ.ends N o) (c , proj₁ (upto (ag N ≤-refl) {c} (≼-refl {c})) xc , live-ag (ag N ≤-refl) (≼-refl {c}) lc)
      ...   | c′ , ec′ , lc′ = c′ , proj₁ (upto (TE.up N ec′ tt) {c′} (≼-refl {c′})) ec′ , live-ag (TE.up N ec′ tt) (≼-refl {c′}) lc′

      from′ : (Σ Pos λ c′ → events o c′ end × Live (events o) c′) → Σ Pos λ c → elaborated o c end × Live (elaborated o) c
      from′ (c′ , ec′ , lc′) with TE.down ec′ tt
      ... | N , ag with from (Erₙ.ends N o) (c′ , proj₁ (upto (ag N ≤-refl) {c′} (≼-refl {c′})) ec′ , live-ag (ag N ≤-refl) (≼-refl {c′}) lc′)
      ...   | c , xc , lc = c , proj₁ (upto (TX.up N xc tt) {c} (≼-refl {c})) xc , live-ag (TX.up N xc tt) (≼-refl {c}) lc
