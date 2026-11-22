{-# OPTIONS --guardedness #-}

-- THE WRAPPED PROGRAM HOLDS.  The program, completed by a mark where it
-- ends, merged beside the subscribe mark and cut after the completion:
-- each layer holds what the one below it holds, and the completion mark
-- carries its end's route down to the cut, where the take ends.
module simultaneous.HeldWrap where

open import Data.Bool using (Bool; true; T; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Properties using (++-identityʳ; foldl-++)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁻)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (nothing; just)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵉ; _∷_ to _∷ᵉ_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Tree using (Obs; cold; merge; of; connected)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst; trans; cong)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; last; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; pin; end; Den; hot; enter; Proper; Few; _≺_; _≼_; ⟦_⟧; module Op;
  module Connect; module Connecting)
open import denotation.Read using (Visible; After; cursor)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext; entered-few)
open import denotation.Laws using (inv-⟦⟧; good-cons)
open import denotation.Laws.Shows using (k-shows)
open import denotation.Laws.ShowsEv using (sk-⟦⟧)
open import denotation.Laws.Worlds using (Hots; InvAt; InvD; Ok; Lawful; Shows; _∪ʰ_; ok-step; world-after; full; ⊕-assoc)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; stop; over; outerOpen; outerClose; laneStart; carry; laneDone;
  burstEnd; outerDone; subscribed; completed)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Relations using (Met; values; values-++)
open import simultaneous.Shut using (r₀)
open import simultaneous.Readings using (rootOf)
open import simultaneous.Layers using (cursor-++)
open import simultaneous.Relabel using (memAt; cntAt; same-mark)
open import simultaneous.Routed using (Held; HeldD; Early; Ex; cnt; nameOf; c-done)
open import simultaneous.HeldTake using (module Holds; Inert; i-done)
open import simultaneous.HeldTo using (HeldTo)
open import simultaneous.HeldIn using (held-in)
open import simultaneous.HeldBeside using (sb₀; beside; module Beside)
open import simultaneous.HeldConnect using (held-conn; held-ex; module ConnRun; Tracks; rootOf-ext)
open import simultaneous.HeldDefer using (sync-up)
open import simultaneous.HeldHot using (module HotRead)
open import simultaneous.HeldClose using (module CatClose; module Close; of-row₁; of-val₁; of-end₁)
open import simultaneous.HeldTrigger using (≺-part)
open import simultaneous.CombSent using (assoc³)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; marked; unfinished; completing; wrapped; concatˢ; count)

-- A TAKE CUT AFTER THE COMPLETION holds what its source holds.
held-until : ∀ {X} (d : Den (IE X)) {H} p cs → InvAt H p (enter d p) → HeldTo unfinished (enter d p) cs
           → Held (enter (Op.takeWhile true unfinished d) p) cs
held-until {X} d p cs iv h = Holds.holds true unfinished d cs p iv h fails fcov fearly
  where
    fails : ∀ {x : IE X} → T (not (unfinished x)) → Inert x
    fails {instEmit (mark completed) _}  _ = i-done
    fails {instEmit (value _) _}         ()
    fails {instEmit (mark begin) _}      ()
    fails {instEmit (mark stop) _}       ()
    fails {instEmit (mark over) _}       ()
    fails {instEmit (mark outerOpen) _}  ()
    fails {instEmit (mark outerClose) _} ()
    fails {instEmit (mark laneStart) _}  ()
    fails {instEmit (mark carry) _}      ()
    fails {instEmit (mark laneDone) _}   ()
    fails {instEmit (mark burstEnd) _}   ()
    fails {instEmit (mark outerDone) _}  ()
    fails {instEmit (mark subscribed) _} ()

    fcov : ∀ {rs} → Met (enter d p) rs → ∀ r₁ {y x} r₂ → rs ≡ r₁ ++ (y , out x) ∷ r₂ → T (not (unfinished x)) → ¬ Ex cs y
         → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
    fcov m r₁ r₂ eq nk nx with fails nk
    ... | i-done = HeldTo.covered h m r₁ r₂ eq c-done nx

    fearly : ∀ {y x} → enter d p y (out x) → T (not (unfinished x)) → Early y
    fearly x nk with fails nk
    ... | i-done = HeldTo.done h x

-- What completes a source read hot: its rows, then the completion mark.
closing : ∀ {A} → Den (IE A) → Den (IE A)
closing h = ⟦ concatˢ (connected (here refl)) (of (marked completed ∷ [])) ⟧ (h ∷ᵉ []ᵉ)

-- A source read hot from before its first row, completed by a mark: the
-- reading holds as the source does (`HotRead`), and the concat shows the
-- reading closed by the mark (`CatClose`).
module Closing {A : Set} (D : Den (IE A)) {H : Pos → Set} (p : Pos) (I : InvD H D) (ok : Ok H p)
               (sh : Shows (enter D (p ⊕ [ ix 1 ]))) where
  P r sb e₁ : Pos
  P  = p ⊕ [ ix 0 ]
  r  = p ⊕ [ ix 1 ]
  sb = (P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]
  e₁ = P ⊕ [ last ]

  S : EmissionSet (IE A)
  S = enter D r

  G : Bool → Den (IE A)
  G b = ⟦ if b then connected (here refl) else of (marked completed ∷ []) ⟧ (hot (Proper S) ∷ᵉ []ᵉ)

  IS = I r (ok-step p ok)

  aft : ∀ {y e} → S y e → r ≺ y
  aft y = world-after (InvAt.world IS y) (InvAt.real IS y)

  sb≺r : sb ≺ r
  sb≺r = subst (_≺ r) (sym (assoc³ p (ix 0) (ix 0) (ix 1))) (≺-part p (ix 0 ∷ ix 1 ∷ []) [] refl)

  e₁≺r : e₁ ≺ r
  e₁≺r = subst (_≺ r) (sym (⊕-assoc p [ ix 0 ] [ last ])) (≺-part p [ last ] [] refl)

  few-vis : ∀ {y e} → S y e → Visible e → Few S y
  few-vis {q} {out x} y _ = entered-few D r (λ {k} {e′} → full {IE A} {q} {out x} tt {k} {e′}) y
  few-vis {q} {end}   y _ = entered-few D r (λ {k} {e′} → full {IE A} {q} {end} tt {k} {e′}) y
  few-vis {e = skip}  _ ()
  few-vis {e = pin _} _ ()

  proper-vis : ∀ {c y e} → S c end → S y e → Visible e → y ≼ c
  proper-vis sc sy v cy with InvAt.quiet IS sc sy cy
  ... | _ , refl , _ = v

  module HR = HotRead S sb (InvAt.flat IS) (InvAt.func IS) (λ {y} y′ → ≺-trans {sb} {r} {y} sb≺r (aft y′)) few-vis proper-vis sh

  module CC = CatClose G P root HR.rd-proper HR.rd-func HR.rd-few (HR.rd-past {e₁} λ y → ≺-trans {e₁} {r} {_} e₁≺r (aft y)) HR.rd-nopin
                (of-row₁ _) (of-val₁ _) (of-end₁ _)

  module CL = Close (enter (G true) sb) root HR.rd-proper HR.rd-func HR.rd-few

  -- THE READING EMPTIES WHERE THE SOURCE DOES: a run of the reading is
  -- the source's moved, its count the same, so past it the source's own
  -- rest bounds the instant.
  via : ∀ {cs} → Held S cs → ∀ {rs′} → Met HR.Rd rs′ → proj₂ (cnt rs′) ≡ 0
      → ∀ {q} → (q , out (instEmit (mark begin) (proj₁ (cnt rs′)))) ∈ rs′
      → Σ (List Pos) λ ks → ∀ {k e} → S k e → After (cursor nothing rs′) k → rootOf k ≡ rootOf q → k ∈ ks
  via H {rs′} m z bq with HR.back m
  ... | rs , run , eq with memAt eq bq
  ...   | q₀ , _ , bq′ , refl , same-mark e
    with Held.rest H run (subst (λ r → proj₂ r ≡ 0) (cntAt eq) z)
           (subst (λ n → (q₀ , out (instEmit (mark begin) n)) ∈ rs) (trans (sym (e refl)) (cong proj₁ (cntAt eq))) bq′)
  ...     | ks , h = ks , λ {k} sk a r → h sk (unshift k (cursor nothing rs) (subst (λ c → After c k) (HR.cursor-at eq nothing) a))
                                              (trans r (rootOf-ext q₀ _))
    where
      unshift : ∀ k c → After (HR.shiftM c) k → After c k
      unshift k nothing  _  = tt
      unshift k (just c) lt = ≺-trans {c} {HR.shift c} {k} (≺-ext c _) lt

  -- A count past the reading's end and the mark is the reading's.
  cnt-mark : ∀ {cb t} (r : List (Pos × Ev (IE A))) → CL.Tail cb t
           → cnt (r ++ (CL.mpos cb , out CL.mk₀) ∷ t) ≡ cnt (r ++ [ (cb , end) ])
  cnt-mark {cb} r tl =
    trans (cong (L.foldl count r₀) (trans (values-++ r _) (cong (values r ++_) (cong (CL.mk₀ ∷_) (no-vals tl)))))
      (trans (foldl-++ count r₀ (values r) [ CL.mk₀ ])
        (sym (trans (cong (L.foldl count r₀) (trans (values-++ r [ (cb , end) ]) (++-identityʳ (values r)))) refl)))
    where
      no-vals : ∀ {t} → CL.Tail cb t → values t ≡ []
      no-vals CL.t-none = refl
      no-vals CL.t-fin  = refl

  -- A begin past the reading is the reading's.
  mem-mark : ∀ {cb t q n} (r : List (Pos × Ev (IE A))) → CL.Tail cb t
           → (q , out (instEmit (mark begin) n)) ∈ r ++ (CL.mpos cb , out CL.mk₀) ∷ t → (q , out (instEmit (mark begin) n)) ∈ r ++ [ (cb , end) ]
  mem-mark r tl x with ∈-++⁻ r x
  ... | inj₁ xr = ∈-++⁺ˡ xr
  mem-mark r CL.t-none x | inj₂ (here ())
  mem-mark r CL.t-fin  x | inj₂ (here ())
  mem-mark r CL.t-fin  x | inj₂ (there (here ()))

  -- The cursor past the mark is past the reading's end.
  cur-mark : ∀ {cb t} (r : List (Pos × Ev (IE A))) → CL.Tail cb t → ∀ {k}
           → After (cursor nothing (r ++ (CL.mpos cb , out CL.mk₀) ∷ t)) k → After (cursor nothing (r ++ [ (cb , end) ])) k
  cur-mark {cb} r tl {k} a =
    subst (λ c → After c k) (sym (cursor-++ nothing r [ (cb , end) ]))
      (past tl (subst (λ c → After c k) (cursor-++ nothing r _) a))
    where
      past : ∀ {t} → CL.Tail cb t → After (cursor (just (CL.mpos cb)) t) k → cb ≺ k
      past CL.t-none lt = ≺-trans {cb} {CL.mpos cb} {k} (CL.c≺m cb) lt
      past CL.t-fin  lt = ≺-trans {cb} {CL.fpos cb} {k} (CL.c≺f cb) lt

  -- WHERE THE CLOSED READING EMPTIES, THE SOURCE FINISHES THE INSTANT.
  tracks : ∀ {cs} {W : Pos → Set} → Held S cs → Tracks W S CC.C
  tracks H m _ z bq = go (CL.shape₀ (CC.back m)) z bq
    where
      go : ∀ {rs} → CL.Shape nothing rs → proj₂ (cnt rs) ≡ 0 → ∀ {q} → (q , out (instEmit (mark begin) (proj₁ (cnt rs)))) ∈ rs
         → Σ (List Pos) λ ks → ∀ {k e} → S k e → After (cursor nothing rs) k → rootOf k ≡ rootOf q → k ∈ ks
      go (CL.open′ run _) z bq = via H run z bq
      go (CL.shut {cb} {r} {t} run _ tl) z {q} bq =
        let E = cnt-mark r tl
            ks , h = via H run (trans (cong proj₂ (sym E)) z)
                       (mem-mark r tl (subst (λ n → (q , out (instEmit (mark begin) n)) ∈ r ++ (CL.mpos cb , out CL.mk₀) ∷ t) (cong proj₁ E) bq))
        in ks , λ sk a r′ → h sk (cur-mark r tl a) r′

-- READ HOT FROM BEFORE ITS FIRST ROW, A SOURCE COMPLETED BY A MARK holds
-- what the source holds, and its mark lies where its end did.
held-closing : ∀ {A} (D : Den (IE A)) {H} p cs → InvD H D → Ok H p → Shows (enter D (p ⊕ [ ix 1 ]))
             → Held (enter D (p ⊕ [ ix 1 ])) ((p ⊕ [ ix 1 ]) ∷ cs)
             → Held (Connect.β D closing p) ((p ⊕ [ ix 0 ]) ∷ p ∷ cs)
held-closing D p cs I ok sh h = CC.held (HR.held-hot (held-ex ex h))
  where
    open Closing D p I ok sh

    ex : ∀ {y} → Ex (r ∷ cs) y → Ex (P ∷ p ∷ cs) y
    ex {y} (here sy) = there (here (sync-up {p} {y} [ ix 1 ] sy))
    ex (there x)     = there (there x)

-- A PROGRAM COMPLETED BY A MARK holds what it holds, and its mark lies
-- where its end did.
held-completing : ∀ {A} (s : Obs Timeline [] (IE A)) p cs → Ok (Hots []ᵉ) p
                → Held (enter (⟦ s ⟧ []ᵉ) (p ⊕ [ ix 1 ])) ((p ⊕ [ ix 1 ]) ∷ cs)
                → Held (enter (⟦ completing s ⟧ []ᵉ) p) (p ∷ cs)
held-completing s p cs ok h = held-conn D closing Is IF p ok cs sh (held-in (held-closing D p cs Is ok sh h)) (Closing.tracks D p Is ok sh h)
  where
    D = ⟦ s ⟧ []ᵉ
    Is = inv-⟦⟧ s []ᵉ (λ ())

    IF : ∀ {t} → Lawful t → InvD (Hots []ᵉ ∪ʰ t) (closing (hot t))
    IF L = inv-⟦⟧ (concatˢ (connected (here refl)) (of (marked completed ∷ []))) (hot _ ∷ᵉ []ᵉ) (good-cons L (λ ()))

    sh = k-shows λ n → sk-⟦⟧ n s []ᵉ (λ ()) (p ⊕ [ ix 1 ]) (ok-step p ok)

-- A COMPLETED PROGRAM ENDS ONLY PAST ITS MARK: where it has ended by `w`,
-- its completion's first effect lies before `w` too.
completing-closed : ∀ {A} (s : Obs Timeline [] (IE A)) p → Ok (Hots []ᵉ) p → ∀ {w c}
                  → Few (enter (⟦ completing s ⟧ []ᵉ) p) w → enter (⟦ completing s ⟧ []ᵉ) p c end → c ≺ w
                  → Σ Pos λ f → Σ Pos λ n → enter (⟦ completing s ⟧ []ᵉ) p f (out (instEmit (mark completed) n)) × (f ⊕ [ ix 0 ]) ≺ w
completing-closed s p ok {w} {c} Fw (Connecting.body y , _) cw =
  let (f , x , fc) = CC.closes y
      fw = ≺-trans {f} {f ⊕ [ ix 0 ]} {w} (≺-ext f {ix 0} []) (≺-trans {f ⊕ [ ix 0 ]} {c} {w} fc cw)
  in f , root , (Connecting.body x , CR.conn-seen Fw (Connecting.body x) fw) , ≺-trans {f ⊕ [ ix 0 ]} {c} {w} fc cw
  where
    D = ⟦ s ⟧ []ᵉ
    Is = inv-⟦⟧ s []ᵉ (λ ())
    sh = k-shows λ n → sk-⟦⟧ n s []ᵉ (λ ()) (p ⊕ [ ix 1 ]) (ok-step p ok)

    IF : ∀ {t} → Lawful t → InvD (Hots []ᵉ ∪ʰ t) (closing (hot t))
    IF L = inv-⟦⟧ (concatˢ (connected (here refl)) (of (marked completed ∷ []))) (hot _ ∷ᵉ []ᵉ) (good-cons L (λ ()))

    open Closing D p Is ok sh using (module CC)
    module CR = ConnRun D closing Is IF p ok sh

-- BESIDE THE SUBSCRIBE MARK, the completed program holds as it did, up
-- to its completion.  Past it the merge never ends, its end turned a
-- skip, so idleness past the completion is not claimed.
--
-- DEAD ROUTE: unrestricted `Held` of the merge is false.  A program
--   ending in a later instant holds a route of that instant at its end
--   (`covered`), and the merge, never ending, idles past it later.
held-merged : ∀ {A} (s : Obs Timeline [] (IE A))
            → Held (enter (⟦ completing s ⟧ []ᵉ) sb₀) (sb₀ ∷ [])
            → HeldTo unfinished (enter (beside s) root) (root ∷ [])
held-merged s = Beside.held s (λ {w} {c} → completing-closed s sb₀ (tt , λ ()) {w} {c})

held-wrapped : ∀ {A} {F : Pos → Set} (s : Obs Timeline [] (IE A)) → (∀ {y} → F y) → HeldD (Hots []ᵉ) F (⟦ s ⟧ []ᵉ) [] → Held (enter (⟦ wrapped s ⟧ []ᵉ) root) (root ∷ [])
held-wrapped s fr hs =
  held-until (beside s) root (root ∷ []) (inv-⟦⟧ (merge (completing s) (cold (lone (marked subscribed)))) []ᵉ (λ ()) root (tt , λ ()))
    (held-merged s (held-completing s sb₀ [] (tt , λ ()) (hs (sb₀ ⊕ [ ix 1 ]) (tt , λ ()) fr λ ())))
