{-# OPTIONS --guardedness #-}

-- THE COMPLETED PROGRAM BESIDE THE SUBSCRIBE MARK holds what the program
-- holds, up to its completion.  The merge's outer rows are silent, and
-- its lone lane shows only the mark, which counts nothing; every other
-- row is the program's, where it is, but its end, shown silent.  A run
-- met of the merge is one of the program's with the mark's row dropped.
--
-- IDLE ONLY BEFORE THE COMPLETION: past the program's end the merge never
-- ends, so a reader there waits on nothing the program shows.  Before the
-- completion's first effect the program has not ended (`closed`), so every
-- row of the program a reader waits on is one the merge shows.
module simultaneous.HeldBeside where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵉ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; yes; no)

open import Tree using (Obs; merge; cold)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; pin; end; Few; Reach; Dep; Work; Den; enter; ⟦_⟧; _≺_; _≼_;
  at-out; on-out; at-skip; on-skip; module Merge)
open import denotation.Read using (Run; []; _∷_; Visible; After; cursor)
open import denotation.Laws.Modulus using (≼-split; ≼-or-≻)
open import denotation.Laws using (inv-⟦⟧)
open import denotation.Laws.Worlds using (Hots; InvAt; inW; plain-ix; w-up; not-up; world-after)
open import simultaneous.InstEmit using (instEmit; mark; value; begin; stop; over; subscribed; completed)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Relations using (Met; values)
open import simultaneous.Routed using (Held; Ex; Carried; Routing; Early; Valued; opos; Rest; cnt; nameOf; r-subscribed)
open import simultaneous.Shut using (Shut)
open import simultaneous.Readings using (rootOf)
open import denotation.Laws.Worlds using (_⊑_)
open import simultaneous.HeldTo using (HeldTo; IdleTo)
open import simultaneous.HeldDefer using (sync-up)
open import simultaneous.HeldClose using (end?)
open import simultaneous.HeldTrigger using (module Two)
open import simultaneous.Layers using (module LoneLayer; after-≺; run-row)
open import simultaneous.Project using (run-prefix)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Routes; marked; unfinished; completing; count)

-- Where the merge subscribes the completed program.
sb₀ : Pos
sb₀ = (root ⊕ [ ix 0 ]) ⊕ [ ix 1 ]

-- The completed program beside the subscribe mark.
beside : ∀ {A} → Obs Timeline [] (IE A) → Den (IE A)
beside s = ⟦ merge (completing s) (cold (lone (marked subscribed))) ⟧ []ᵉ

module Beside {A : Set} (s : Obs Timeline [] (IE A))
              (closed : ∀ {w c} → Few (enter (⟦ completing s ⟧ []ᵉ) sb₀) w → enter (⟦ completing s ⟧ []ᵉ) sb₀ c end → c ≺ w
                      → Σ Pos λ f → Σ Pos λ n → enter (⟦ completing s ⟧ []ᵉ) sb₀ f (out (instEmit (mark completed) n)) × (f ⊕ [ ix 0 ]) ≺ w) where

  mkS : IE A
  mkS = marked subscribed

  open LoneLayer (completing s) mkS using (F; undone; lone-endless)
  open Two root using (q₀; q₁; e₁; O; o-out; o-end; o-skip; o-pin; o₀)
  open Merge F O

  C R : EmissionSet (IE A)
  C = enter (beside s) root
  R = enter (F true) sb₀

  IS : InvAt (Hots []ᵉ) sb₀ R
  IS = inv-⟦⟧ (completing s) []ᵉ (λ ()) sb₀ (tt , λ ())

  s₁ m₁ m₂ : Pos
  s₁ = q₁ ⊕ [ ix 1 ]
  m₁ = s₁ ⊕ [ ix 0 ]
  m₂ = s₁ ⊕ [ ix 1 ]

  base : List Pos
  base = (q₀ ⊕ [ ix 0 ]) ∷ (q₁ ⊕ [ ix 0 ]) ∷ e₁ ∷ []

  ----------------------------------------------------------------------
  -- Where the rows lie

  aft : ∀ {y e} → R y e → sb₀ ≺ y
  aft y = world-after (InvAt.world IS y) (InvAt.real IS y)

  -- The program's world holds nothing of the lone lane's.
  no-m₁ : ∀ {e} → R m₁ e → ⊥
  no-m₁ y with w-up {x = s₁} plain-ix (inW (InvAt.world IS y))
  ... | inj₁ ()
  ... | inj₂ v₁ with w-up {x = q₁} plain-ix v₁
  ...   | inj₁ ()
  ...   | inj₂ v₂ with w-up {x = root} plain-ix v₂
  ...     | inj₁ ()
  ...     | inj₂ v₃ = not-up {q = q₀} {l = ix 1} tt v₃ ([ ix 0 ] , refl)

  proper-vis : ∀ {c y e} → R c end → R y e → Visible e → y ≼ c
  proper-vis sc sy v cy with InvAt.quiet IS sc sy cy
  ... | _ , refl , _ = v

  -- The lone lane: the mark, then a skip.
  lone-row : ∀ {p k e} → enter (F false) p k e → (k ≡ p ⊕ [ ix 0 ] × e ≡ out mkS) ⊎ (k ≡ p ⊕ [ ix 1 ] × e ≡ skip)
  lone-row (at-out , _)              = inj₁ (refl , refl)
  lone-row (on-out at-skip , _)      = inj₂ (refl , refl)
  lone-row (on-out (on-skip ()) , _)

  ----------------------------------------------------------------------
  -- Every row of the merge

  data Row (k : Pos) : Ev (IE A) → Set where
    outer : k ∈ base → Row k skip
    src   : ∀ {e} → R k e → (e ≡ end → ⊥) → Row k e
    fin   : R k end → Row k skip
    mk    : k ≡ m₁ → Row k (out mkS)
    sk    : k ≡ m₂ → Row k skip

  classify : ∀ {k e} → JoinT k e → Row k e
  classify (val x) with o-out x
  ... | inj₁ (refl , _) = outer (here refl)
  ... | inj₂ (refl , _) = outer (there (here refl))
  classify (step x)   = ⊥-elim (o-skip x)
  classify (opin x)   = ⊥-elim (o-pin x)
  classify (oend _ d) = ⊥-elim (undone d)
  classify (opass x _) with o-end x
  ... | refl = outer (there (there (here refl)))
  classify (lane x _ L _ w) with o-out x
  ... | inj₁ (refl , refl) = src (proj₁ L) λ { refl → w }
  ... | inj₂ (refl , refl) with lone-row (proj₁ L)
  ...   | inj₁ (refl , refl) = mk refl
  ...   | inj₂ (refl , refl) = sk refl
  classify (lend _ _ _ _ _ d) = ⊥-elim (undone d)
  classify (lpass x _ L _ _ _) with o-out x
  ... | inj₁ (refl , refl) = fin (proj₁ L)
  ... | inj₂ (refl , refl) = ⊥-elim (lone-endless (proj₁ L))
  classify (hand _ _ _ _ ())
  classify (left x _ L _ _) with o-out x
  ... | inj₁ (refl , refl) = src (proj₁ L) λ ()
  ... | inj₂ (refl , refl) with lone-row (proj₁ L)
  ...   | inj₁ (_ , ())
  ...   | inj₂ (_ , ())
  classify (run () _)
  classify (rend () _ _)
  classify (rpass () _ _)
  classify (rhand () _)

  ----------------------------------------------------------------------
  -- The program's rows are the merge's

  dep-fin : ∀ {q} (e : Ev (IE A)) {k′} → Dep q e k′ skip → Dep q e k′ end
  dep-fin (out _) _ = tt
  dep-fin skip    _ = tt
  dep-fin end     _ = tt
  dep-fin (pin r) d i = [ inj₁ , (λ ()) ]′ (d i)

  lift-reach : ∀ {X : EmissionSet (IE A)} → (∀ {k e} → R k e → X k e)
             → ∀ {k e e₀} → Reach X k e₀ → (∀ {k′ e′} → Dep k e k′ e′ → Dep k e₀ k′ e′) → Reach JoinT k e
  lift-reach raw {k} {e} (ks , h) dm = ks ++ (base ++ m₁ ∷ m₂ ∷ []) , λ j lt d → pick (classify j) lt d
    where
      pick : ∀ {k′ e′} → Row k′ e′ → k′ ≺ k → Dep k e k′ e′ → k′ ∈ (ks ++ (base ++ m₁ ∷ m₂ ∷ []))
      pick (outer mb) _  _ = ∈-++⁺ʳ ks (∈-++⁺ˡ mb)
      pick {k′} {e′} (src y _) lt d = ∈-++⁺ˡ (h (raw {k′} {e′} y) lt (dm d))
      pick {k′} (fin y) lt d = ∈-++⁺ˡ (h (raw {k′} {end} y) lt (dm (dep-fin {k} e {k′} d)))
      pick (mk refl)  _  _ = ∈-++⁺ʳ ks (∈-++⁺ʳ base (here refl))
      pick (sk refl)  _  _ = ∈-++⁺ʳ ks (∈-++⁺ʳ base (there (here refl)))

  lane-row : ∀ {k e} → R k e → Work e → C k e
  lane-row {k} {e} y w = lane o₀ tt (y , aft y) (λ ()) w , lift-reach (λ {k′} {e′} z → proj₁ z) {k} {e} {e} (proj₂ y) (λ d → d)

  liftR : ∀ {k e} → R k e → (e ≡ end → ⊥) → C k e
  liftR {e = out _} y _  = lane-row y tt
  liftR {e = skip}  y _  = lane-row y tt
  liftR {e = pin _} y _  = lane-row y tt
  liftR {e = end}   _ ne = ⊥-elim (ne refl)

  -- The program's end, shown silent.
  liftE : ∀ {c} → R c end → C c skip
  liftE {c} y = lpass o₀ tt (y , aft y) (λ ()) (λ ()) undone , lift-reach (λ {k′} {e′} z → proj₁ z) {c} {skip} {end} (proj₂ y) (λ _ → tt)

  lift-any : ∀ {k e} → R k e → Σ (Ev (IE A)) (C k)
  lift-any {e = e} y with end? e
  ... | inj₁ refl = skip , liftE y
  ... | inj₂ ne   = e , liftR y ne

  few-CR : ∀ {w} → Few C w → Few R w
  few-CR (ks , h) = ks , λ y lt → h (proj₂ (lift-any y)) lt

  -- A row a reader meets is the program's, or the mark.
  vis-row : ∀ {q e} → C q e → Visible e → (q ≡ m₁ → ⊥) → R q e
  vis-row (j , _) v nm with classify j
  ... | outer _  = ⊥-elim v
  ... | src y _  = y
  ... | fin _    = ⊥-elim v
  ... | mk eq    = ⊥-elim (nm eq)
  ... | sk _     = ⊥-elim v

  at-m₁ : ∀ {e} → C m₁ e → Visible e → e ≡ out mkS
  at-m₁ (j , _) v with classify j
  ... | outer _ = ⊥-elim v
  ... | src y _ = ⊥-elim (no-m₁ y)
  ... | fin _   = ⊥-elim v
  ... | mk _    = refl
  ... | sk _    = ⊥-elim v

  off-m₁ : ∀ {q e} → C q e → Visible e → (e ≡ out mkS → ⊥) → q ≡ m₁ → ⊥
  off-m₁ y v ne refl = ne (at-m₁ y v)

  ----------------------------------------------------------------------
  -- A run met, the mark dropped

  thin : List (Pos × Ev (IE A)) → List (Pos × Ev (IE A))
  thin [] = []
  thin ((q , e) ∷ rs) with q ≟ᵖ m₁
  ... | yes _ = thin rs
  ... | no _  = (q , e) ∷ thin rs

  thin-++ : ∀ xs ys → thin (xs ++ ys) ≡ thin xs ++ thin ys
  thin-++ [] ys = refl
  thin-++ ((q , e) ∷ xs) ys with q ≟ᵖ m₁
  ... | yes _ = thin-++ xs ys
  ... | no _  = cong ((q , e) ∷_) (thin-++ xs ys)

  thin-no : ∀ {q e} xs → (q ≡ m₁ → ⊥) → thin ((q , e) ∷ xs) ≡ (q , e) ∷ thin xs
  thin-no {q} xs nm with q ≟ᵖ m₁
  ... | yes eq = ⊥-elim (nm eq)
  ... | no _   = refl

  thin-∈ : ∀ {q e xs} → (q , e) ∈ xs → (q ≡ m₁ → ⊥) → (q , e) ∈ thin xs
  thin-∈ {xs = _ ∷ xs} (here refl) nm = subst (_ ∈_) (sym (thin-no xs nm)) (here refl)
  thin-∈ {xs = (q′ , _) ∷ xs} (there m) nm with q′ ≟ᵖ m₁
  ... | yes _ = thin-∈ m nm
  ... | no _  = there (thin-∈ m nm)

  thin-⊆ : ∀ {x xs} → x ∈ thin xs → x ∈ xs
  thin-⊆ {xs = (q , _) ∷ xs} m with q ≟ᵖ m₁
  ... | yes _ = there (thin-⊆ m)
  ... | no _ with m
  ...   | here eq  = here eq
  ...   | there m′ = there (thin-⊆ m′)

  -- The cursor dropping the mark stands no later, and no program row a
  -- reader would meet lies between.
  Below Gap : Maybe Pos → Maybe Pos → Set
  Below c′ c = ∀ {x} → After c x → After c′ x
  Gap c′ c = ∀ {k x} → R k (out x) → After c′ k → After c k

  back : ∀ {c c′ rs} → Run C c rs → Below c′ c → Gap c′ c
       → Run R c′ (thin rs) × Below (cursor c′ (thin rs)) (cursor c rs) × Gap (cursor c′ (thin rs)) (cursor c rs)
  back [] B G = [] , B , G
  back {c} {c′} {(q , e) ∷ rs} ((((y , _) , fw) , vi , ac , lf) ∷ rn) B G with q ≟ᵖ m₁
  ... | yes refl = back rn B′ G′
    where
      B′ : Below c′ (just m₁)
      B′ lt = after-≺ c′ (B ac) lt

      G′ : Gap c′ (just m₁)
      G′ {k} yk a with ≼-split {m₁} {k} (lf (liftR yk (λ ())) tt (G yk a))
      ... | inj₁ lt   = lt
      ... | inj₂ refl = ⊥-elim (no-m₁ yk)
  ... | no nm = go (back rn (λ a → a) (λ _ a → a))
    where
      yR : R q e
      yR = vis-row y vi nm

      least : ∀ {k e₁} → R k e₁ → Visible e₁ → After c′ k → q ≼ k
      least {e₁ = out _} yk _ a = lf (liftR yk (λ ())) tt (G yk a)
      least {e₁ = end}   yk _ _ = proper-vis yk yR vi
      least {e₁ = skip}  _ () _
      least {e₁ = pin _} _ () _

      go : Run R (just q) (thin rs) × Below (cursor (just q) (thin rs)) (cursor (just q) rs) × Gap (cursor (just q) (thin rs)) (cursor (just q) rs)
         → Run R c′ ((q , e) ∷ thin rs) × Below (cursor (just q) (thin rs)) (cursor (just q) rs) × Gap (cursor (just q) (thin rs)) (cursor (just q) rs)
      go (run′ , B″ , G″) = (((yR , λ yc → proper-vis yc yR vi) , few-CR fw) , vi , B ac , least) ∷ run′ , B″ , G″

  met-back : ∀ {rs} → Met C rs → Met R (thin rs)
  met-back m = proj₁ (back m (λ a → a) (λ _ a → a))

  ----------------------------------------------------------------------
  -- The mark counts nothing

  step′ : Routes → Ev (IE A) → Routes
  step′ r (out x) = count r x
  step′ r _       = r

  fold-cons : ∀ r q e xs → L.foldl count r (values ((q , e) ∷ xs)) ≡ L.foldl count (step′ r e) (values xs)
  fold-cons r q (out _) xs = refl
  fold-cons r q skip    xs = refl
  fold-cons r q (pin _) xs = refl
  fold-cons r q end     xs = refl

  cnt-thin : ∀ {c rs} r → Run C c rs → L.foldl count r (values (thin rs)) ≡ L.foldl count r (values rs)
  cnt-thin r [] = refl
  cnt-thin {rs = (q , e) ∷ rs} r ((((y , _) , _) , vi , _) ∷ rn) with q ≟ᵖ m₁
  ... | yes refl with at-m₁ y vi
  ...   | refl = cnt-thin r rn
  cnt-thin {rs = (q , e) ∷ rs} r (_ ∷ rn) | no _ =
    trans (fold-cons r q e (thin rs)) (trans (cnt-thin (step′ r e) rn) (sym (fold-cons r q e rs)))

  cnt≡ : ∀ {c rs} → Run C c rs → cnt (thin rs) ≡ cnt rs
  cnt≡ = cnt-thin _

  ----------------------------------------------------------------------
  -- Held, up to the completion

  ex-up : ∀ {y} → Ex (sb₀ ∷ []) y → Ex (root ∷ []) y
  ex-up {y} (here sy) = here (sync-up {root} {y} (ix 0 ∷ ix 1 ∷ []) sy)
  ex-up (there ())

  no-carry : Carried (out mkS) → ⊥
  no-carry ()

  held : Held R (sb₀ ∷ []) → HeldTo unfinished C (root ∷ [])
  held H = record
    { named   = named
    ; covered = covered
    ; exact   = exact
    ; routing = routing
    ; shut    = shut
    ; early   = early
    ; ends    = ends
    ; done    = done
    ; late    = late
    ; idle    = idle
    ; rest    = rest
    }
    where
      module H = Held H

      named : ∀ {y n} → C y (out (instEmit (mark begin) n)) → n ≡ nameOf y
      named x with classify (proj₁ x)
      ... | src y _ = H.named y

      routing : ∀ {y m n} → C y (out (instEmit (mark m) n)) → Routing m
      routing x with classify (proj₁ x)
      ... | src y _ = H.routing y
      ... | mk _    = r-subscribed

      early : ∀ {y a n} → C y (out (instEmit (value a) n)) → Early y
      early x with classify (proj₁ x)
      ... | src y _ = H.early y

      ends : ∀ {y} → C y end → Early y
      ends x with classify (proj₁ x)
      ... | src _ ne = ⊥-elim (ne refl)

      done : ∀ {y n} → C y (out (instEmit (mark completed) n)) → Early y
      done x with classify (proj₁ x)
      ... | src y _ = H.done y

      late : ∀ {y n} → C y (out (instEmit (mark over) n)) → Valued (rootOf y) × opos (rootOf y) ⊑ y
      late x with classify (proj₁ x)
      ... | src y _ = H.late y

      -- The row at a split, off the mark.
      split : ∀ {rs} → Met C rs → ∀ r₁ {y e} r₂ → rs ≡ r₁ ++ (y , e) ∷ r₂ → (e ≡ out mkS → ⊥)
            → thin rs ≡ thin r₁ ++ (y , e) ∷ thin r₂
      split m r₁ {y} {e} r₂ eq ne =
        trans (cong thin eq) (trans (thin-++ r₁ _) (cong (thin r₁ ++_) (thin-no r₂ (off-m₁ (proj₁ ye) (proj₂ ye) ne))))
        where
          ye = run-row m (subst ((y , e) ∈_) (sym eq) (∈-++⁺ʳ r₁ (here refl)))

      pre : ∀ {rs} → Met C rs → ∀ r₁ {r₂} → rs ≡ r₁ ++ r₂ → cnt (thin r₁) ≡ cnt r₁
      pre m r₁ eq = cnt≡ (run-prefix r₁ (subst (Met C) eq m))

      covered : ∀ {rs} → Met C rs → ∀ r₁ {y e} r₂ → rs ≡ r₁ ++ (y , e) ∷ r₂ → Carried e → ¬ Ex (root ∷ []) y → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
      covered m r₁ r₂ eq c nx with H.covered (met-back m) (thin r₁) (thin r₂) (split m r₁ r₂ eq λ { refl → no-carry c }) c (λ ex → nx (ex-up ex))
      ... | k , ce = k , trans (sym (pre m r₁ eq)) ce

      exact : ∀ {rs} → Met C rs → ∀ r₁ {y n} r₂ → rs ≡ r₁ ++ (y , out (instEmit (mark stop) n)) ∷ r₂ → Σ ℕ λ k → proj₂ (cnt r₁) ≡ suc k
      exact m r₁ r₂ eq with H.exact (met-back m) (thin r₁) (thin r₂) (split m r₁ r₂ eq λ ())
      ... | k , ce = k , trans (sym (cong proj₂ (pre m r₁ eq))) ce

      shut : Shut C
      shut m r₁ r₂ eq z {q} bq {y} vy iq =
        H.shut (met-back m) (thin r₁) (thin r₂) (trans (cong thin eq) (thin-++ r₁ r₂)) (trans (cong proj₂ ct) z)
          (subst (λ n → (q , out (instEmit (mark begin) n)) ∈ thin r₁) (sym (cong proj₁ ct)) (thin-∈ bq nq)) (thin-∈ vy ny) iq
        where
          ct = pre m r₁ eq
          rq = run-row m (subst (_ ∈_) (sym eq) (∈-++⁺ˡ bq))
          ry = run-row m (subst (_ ∈_) (sym eq) (∈-++⁺ʳ r₁ vy))
          nq = off-m₁ (proj₁ rq) (proj₂ rq) λ ()
          ny = off-m₁ (proj₁ ry) (proj₂ ry) λ ()

      idle : IdleTo unfinished C
      idle {rs} m ne {w} unf Fw aw later with back m (λ a → a) (λ _ a → a)
      ... | run′ , B , G =
        subst (λ r → proj₂ r ≡ 0 ⊎ proj₁ r ≡ nameOf w) (cnt≡ m) (H.idle run′ (λ ce → ne (thin-⊆ ce)) (few-CR Fw) (B aw) later′)
        where
          later′ : ∀ {y e} → R y e → Visible e → After (cursor nothing (thin rs)) y → w ≼ y
          later′ {e = out _} y _ a = later (liftR y (λ ())) tt (G y a)
          later′ {y} {e = end} yc _ _ with ≼-or-≻ w y
          ... | inj₁ le = le
          ... | inj₂ yw with closed (few-CR Fw) yc yw
          ...   | f , n , x , fw = ⊥-elim (unf (liftR x (λ ())) tt fw)
          later′ {e = skip}  _ () _
          later′ {e = pin _} _ () _

      rest : Rest C
      rest {rs} m z {q} bq with back m (λ a → a) (λ _ a → a)
      ... | _ , B , _ with H.rest (met-back m) (trans (cong proj₂ (cnt≡ m)) z)
                             (subst (λ n → (q , out (instEmit (mark begin) n)) ∈ thin rs) (sym (cong proj₁ (cnt≡ m))) (thin-∈ bq nq))
        where
          rq = run-row m bq
          nq = off-m₁ (proj₁ rq) (proj₂ rq) λ ()
      ...   | ks , h = ks ++ (base ++ m₁ ∷ m₂ ∷ []) , pick
        where
          pick : ∀ {y e} → C y e → After (cursor nothing rs) y → rootOf y ≡ rootOf q → y ∈ (ks ++ (base ++ m₁ ∷ m₂ ∷ []))
          pick (j , _) a rt with classify j
          ... | outer mb = ∈-++⁺ʳ ks (∈-++⁺ˡ mb)
          ... | src y _  = ∈-++⁺ˡ (h y (B a) rt)
          ... | fin y    = ∈-++⁺ˡ (h y (B a) rt)
          ... | mk refl  = ∈-++⁺ʳ ks (∈-++⁺ʳ base (here refl))
          ... | sk refl  = ∈-++⁺ʳ ks (∈-++⁺ʳ base (there (here refl)))
