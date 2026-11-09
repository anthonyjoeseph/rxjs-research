{-# OPTIONS --guardedness #-}

-- THE RUN, STEP BY STEP, OVER THE CURSOR: every step of the engine is
-- one of the cursor invariant's moves, dispatched by mode and frame; a
-- mark run is a search, moving the focus to the mark and the cursor to
-- just before what it delivers, then the node's own run.  Together they
-- are a `Simulation` of every program's run.
module adequacy.Dispatch where

open import Data.Bool using (Bool; true; false; if_then_else_; not; _∨_; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (_≡ᵇ_; suc)
open import Data.List using (List; []; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᴹ)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to tt₁)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; cong)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Position using (Pos; ix; last; _⊕_; nested; _▸_)
open import denotation.Events using (Timeline; timelineAt; Frame; emit; stall; close; module From∞)
open import denotation.EmissionSet using (EmissionSet; out; skip; module TakeWhile; ⟦_⟧; InE; at-out; at-end; _≺_; _≼_)
open import denotation.Laws.Modulus using (≺-ext; ≺→≼; ≺-trans; ≺-irrefl; ≺-≼-≺; ≼-antisym; ≼-trans; ≼-refl; entered-reach; ticks)
open import denotation.Laws.Worlds using (Ok; Hots; ok-step)
open import operation.Key using (at; after; at-after)
open import operation.PureObservable using (PureObs; module Machine; module Driver; Tape; play; ending; over; opening)
open Machine using (St; Ctx; Conf; Scope; binds; scopeOf; ⟨_,_,_,_⟩; subscribing; absorbed; rising; load; moved; plug; search; found; Mark; ofM; attM;
                    rise; run; alive; nx; cp; attAt; attached; Torn; Stepped; quiet; admit; closed; killAll; unsubIf; unsub; free; cpAt; cutAt; overAt;
                    cut; cpM; cutM; CS; cs; closedUp; unbound; seek; kids; lanes; own; ownBest; first; retag; raceT; sourceT; Cand; Out; bodyM; srcAttM; owedM; joinM; leafM; leaf; starting; turn;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
                    renaming (Shown to Shownᴹ; step to stepᴹ)
open import adequacy.Rows using (pendRows; full; ≃-refl; Vis; _≃_; silent; Moves; this; tapeE)
open _≃_
open import adequacy.Cursor using (Cur; aft; NoFail; Sound; tailp-dn; ≈-refl; ≈-trans; fd-none; Rgn; JoinE; Flags; src-pend; Within; Adm; bef; Spent; Sync; _≈_; Owes; Due; cov; alike; Pts; h-blank; h-take; Quiet; Sealed; notT; s-of; s-join; s-joinx; s-took; s-cold; s-coldx; Ticked; subd; o-cp)
open import adequacy.Cursor.Tear using (husk-of; c-abs; c-sub; Clear; Pending; pend-shape; sync-pend)
open import adequacy.Cursor.Frame using (Fr; Hold; owes; dead; lane; lanecut; pnd; Rest; f-top; f-map; f-scan; f-cut; f-take; f-took; f-outer; f-lanes; f-lane; f-lnct; f-src; f-srcc; f-srcp; f-body; d-map; d-scan; d-cut; d-ln; d-take; d-outer; d-lanes; d-src; d-body; f-isle; f-islec; f-islep)
open import adequacy.Cursor.Rise using (Inv; settled; pending; flying; adrift; RT; SimC; keeps; rise-top; rise-map; rise-scan-nx; rise-scan-cp; rise-take-pass; rise-take-cp; rise-cut; rise-cutx; rise-ln; rise-took; rise-take-fail; rise-bodyx; run-stop; run-cut; run-att)
open import adequacy.Path using (Path)
open import adequacy.Isle.Step using (found-clear; found-con)
open import adequacy.RunCon using (vis-≃; body-noisle; Ran; con-body; con-att; con-owed; Off; closed-off)
open import adequacy.Stamped using (StOK; pend-of; pend-focus)
open import adequacy.Isle using (G)
open import adequacy.Floor.Keys using (own-cls; ob; os; oo; plug-in; lo-weaken)
open import adequacy.Found using (Marked; ofK; attK; conK; joinK; leafK; stopK; cutK; found-least; found-mark; found-plug)
open import adequacy.Walk using (due-≈; climb; descend; refocus)
open import adequacy.Least using (Lo; seek-none; k-kid; k-src)
open import adequacy.Bound using (bound; owes-≼; behind-past; behind-pend; join-past; pend-past)
open import adequacy.FrShift using (fr-shift; rc; hr; HR)
open import adequacy.Few using (lag; owes-call)
open import adequacy.Apart.Floor using (floor)
open import denotation.Laws.BoundedInv using (first-child)
open import adequacy.Up using (NoRow; rise-body-nx; rise-body-cp)
open import adequacy.PinTail using (took-tail)
open import denotation.Laws.ColdInv using (slot-last)
open import adequacy.FeedUp using (rise-src-nx; rise-src-cp)
open import adequacy.Admit using (rise-outer-nx)
open import adequacy.Settle using (rise-outer-cp; rise-lane-nx)
open import adequacy.LaneEnd using (rise-lane-cp)
open import adequacy.SubJoin using (join-pend; joined-pend; ended-up; settle-of; of-reach; of-owes)
open import adequacy.Ended using (endUp; ends-behind)
open import adequacy.SubOne using (module Entry; module DeferEntry)
open import adequacy.RunOf using (of-nx; of-cp; join-nx; join-cp)
open import adequacy.Cold using (cold-sync; cold-nx; emit-hit; cold-cp; cold-drop; rest-ticked; stall-into; stall-back; close-into; close-back)
open import adequacy.Enter using (conn₀; conn-parts; conn-ok; flat-sound; flat-within; flat-joined; flat-jinv)

------------------------------------------------------------------------
-- Within what is grown, every step moves or finds nothing to do

Mv : ∀ {R} → Stepped R → Set
Mv (moved _ _ _) = ⊤
Mv _             = ⊥

admit-mv : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) ω d n q o ls a p → Mv (admit c op f ω d n q o ls a p)
admit-mv c (Tree.mergeᶠ nothing)  f ω d n q o ls a p = tt
admit-mv c (Tree.mergeᶠ (just m)) f ω d n q o ls a p = tt
admit-mv c Tree.switchᶠ           f ω d n q o ls a p with killAll ls
... | _ = tt
admit-mv c Tree.exhaustᶠ          f ω d n q o ls a p with n ≡ᵇ 0
... | true  = tt
... | false = tt

rise-mv : ∀ {R Γ A} (c : Ctx R Γ A) s e p → Mv (rise c s e p)
rise-mv top                       s e      p = tt
rise-mv (inMap f c)               s e      p = tt
rise-mv (inScan f z c)            s (nx a) p = tt
rise-mv (inScan f z c)            s cp     p = tt
rise-mv (inCut l a c)             s e      p = tt
rise-mv (inLn b c)                s e      p = tt
rise-mv (inTake i q free c)       s (nx a) p with q a | i
... | true  | _     = tt
... | false | true  = tt
... | false | false = tt
rise-mv (inTake i q free c)       s cp     p = tt
rise-mv (inTake i q (cpAt r) c)   s e      p = tt
rise-mv (inTake i q (cutAt r) c)  s e      p = tt
rise-mv (inTake i q (overAt r) c) s e      p = tt
rise-mv (inOuter op f ω d n q ls c) o (nx a) p = admit-mv c op f ω d n q o ls a p
rise-mv (inOuter op f ω d n q ls c) o cp     p = tt
rise-mv (inLanes op f ω d n q o pre post c) s (nx b) p = tt
rise-mv (inLanes op f ω d n q o pre post c) s cp     p = tt
rise-mv (inSrc k b c)             s (nx a) p = tt
rise-mv (inSrc k b c)             s cp     p = tt
rise-mv (inBody k o c)            s (nx b) p with CS.srcLive k
... | true  = tt
... | false = tt
rise-mv (inBody k o c)            s cp     p with CS.srcLive k
... | true  = tt
... | false = tt

run-of-mv : ∀ {R Γ A} (c : Ctx R Γ A) i q (xs : List A) p → Mv (run c (ofS i q xs) ofM p)
run-of-mv c i q xs p with closed c | xs
... | true  | _     = tt
... | false | []    = tt
... | false | _ ∷ _ = tt

run-att-mv : ∀ {R Γ A} (c : Ctx R Γ A) l q (s : St Γ A) p → Mv (run c (cutS l (attAt q) s) attM p)
run-att-mv c l q s p with unsubIf (not l) s
... | _ = tt

run-con-mv : ∀ {R Γ A X} (c : Ctx R Γ A) k (o : St Γ X) b m p → m ≡ bodyM ⊎ (m ≡ srcAttM ⊎ m ≡ owedM) → Mv (run c (connS k o b) m p)
run-con-mv c k o b .bodyM p (inj₁ refl) with CS.bodyAt k
... | just _  = tt
... | nothing = tt
run-con-mv c k o b .srcAttM p (inj₂ (inj₁ refl)) with CS.attSrc k | unsubIf (not (CS.srcLive k) ∨ closed c) o
... | just _  | _ = tt
... | nothing | _ = tt
run-con-mv c k o b .owedM p (inj₂ (inj₂ refl)) with CS.owedAt k | unsubIf (CS.srcAtt k) o
... | just _  | _ = tt
... | nothing | _ = tt

run-cut-mv : ∀ {R Γ A} (c : Ctx R Γ A) i (q : A → Bool) r (s : St Γ A) p → Mv (run c (takeS i q (cutAt r) s) cutM p)
run-cut-mv c i q r s p with cut s
... | _ = tt

run-join-mv : ∀ {R Γ A} (c : Ctx R Γ A) j g (x : A ∈ Γ) q e ib p → Mv (run c (joinS j g x ((q , e) ∷ ib)) joinM p)
run-join-mv c j g x q (nx a) ib p = tt
run-join-mv c j g x q cp     ib p = tt

-- The driver's steps read back as the engine's.
module _ {R : Set} where
  open Driver R using (took; value; complete; drained) renaming (silent to τ)

  τ-moved : (x : Stepped R) → Mv x → ∀ {t k′} → took x ≡ τ t k′ → Σ Torn λ tr → x ≡ moved k′ [] tr
  τ-moved (moved k [] tr) _ refl = tr , refl
  τ-moved (moved k ((_ , nx _) ∷ _) tr) _ ()
  τ-moved (moved k ((_ , cp) ∷ _) tr)   _ ()
  τ-moved quiet _ ()

  val-moved : (x : Stepped R) → Mv x → ∀ {t p a k′} → took x ≡ value t p a k′ → Σ (Shownᴹ R) λ rest → Σ Torn λ tr → x ≡ moved k′ ((p , nx a) ∷ rest) tr
  val-moved (moved k [] tr) _ ()
  val-moved (moved k ((_ , nx _) ∷ rest) tr) _ refl = rest , tr , refl
  val-moved (moved k ((_ , cp) ∷ _) tr)      _ ()
  val-moved quiet _ ()

  fin-moved : (x : Stepped R) → Mv x → ∀ {p} → took x ≡ complete p → Σ (Conf R) λ k′ → Σ (Shownᴹ R) λ rest → Σ Torn λ tr → x ≡ moved k′ ((p , cp) ∷ rest) tr
  fin-moved (moved k [] tr) _ ()
  fin-moved (moved k ((_ , nx _) ∷ _) tr)    _ ()
  fin-moved (moved k ((_ , cp) ∷ rest) tr)   _ refl = k , rest , tr , refl
  fin-moved quiet _ ()

  mv-drained : (x : Stepped R) → Mv x → took x ≢ drained
  mv-drained (moved k [] tr)                _ ()
  mv-drained (moved k ((_ , nx _) ∷ _) tr) _ ()
  mv-drained (moved k ((_ , cp) ∷ _) tr)   _ ()
  mv-drained quiet                          () _
  mv-drained (starting _ _ _)               () _
  mv-drained (turn _)                       () _

  quiet-τ : ∀ {x t k′} → x ≡ quiet → took x ≢ τ t k′
  quiet-τ refl ()

  quiet-val : ∀ {x t p a k′} → x ≡ quiet → took x ≢ value t p a k′
  quiet-val refl ()

  quiet-fin : ∀ {x p} → x ≡ quiet → took x ≢ complete p
  quiet-fin refl ()

-- A driver step that shows nothing: a cold's subscription or turn.
module _ {R : Set} where
  open Driver R using (Step; played; value; complete; drained) renaming (silent to τ)

  Hush : Step → Set
  Hush (τ _ _) = ⊤
  Hush _       = ⊥

  played-hush : ∀ {A} b l cl dv st → Hush (played (leaf {A = A} b l cl dv st))
  played-hush true (ending e) cl dv st              = tt
  played-hush false l cl dv st                      = tt
  played-hush true (play τ′ u i t fr) true dv st    = tt
  played-hush true over true dv st                  = tt
  played-hush true (play τ′ u i t (emit a k)) false dv st = tt
  played-hush true (play τ′ u i t (stall k)) false dv st  = tt
  played-hush true (play τ′ u i t (close k)) false dv st  = tt
  played-hush true over false dv st                 = tt

  hush-val : ∀ {x t p a k′} → Hush x → x ≡ value t p a k′ → ⊥
  hush-val h refl = h

  hush-fin : ∀ {x p} → Hush x → x ≡ complete p → ⊥
  hush-fin h refl = h

  hush-drained : ∀ {x} → Hush x → x ≢ drained
  hush-drained h refl = h

------------------------------------------------------------------------
-- What a search finds


-- Where a mark run delivers, if it does.
data Delivers {Γ A} : St Γ A → Mark → Pos → Set₁ where
  d-of   : ∀ {i q x xs} → Delivers (ofS i q (x ∷ xs)) ofM (q ⊕ [ ix i ])
  d-ofx  : ∀ {i q} → Delivers (ofS i q []) ofM (q ⊕ [ last ])
  d-join : ∀ {j x q e ib} → Delivers (joinS j true x ((q , e) ∷ ib)) joinM q
  d-stop : ∀ {i keep r s} → Delivers (takeS i keep (cpAt r) s) cpM (r ⊕ [ last ])
  d-play : ∀ {τ u i t a k} → Delivers (coldS true (play τ u i t (emit a k))) leafM (u ▸ ix i)
  d-ending : ∀ {e} → Delivers (coldS true (ending e)) leafM e


-- A delivering mark's key is where it delivers.
delivers-key : ∀ {Γ A} {s : St Γ A} {m p κ} → Delivers s m p → (m , κ) ∈ own s → κ ≡ at p
delivers-key d-of   (here refl) = refl
delivers-key d-of   (there ())
delivers-key d-ofx  (here refl) = refl
delivers-key d-ofx  (there ())
delivers-key d-join (here refl) = refl
delivers-key d-join (there ())
delivers-key d-stop (here refl) = refl
delivers-key d-stop (there ())
delivers-key d-play (here refl) = refl
delivers-key d-play (there ())
delivers-key d-ending (here refl) = refl
delivers-key d-ending (there ())

-- What a node in step delivers, it owes.
delivers-owed : ∀ {Γ} {sc : Scope Γ} {Rg C A} {s : St Γ A} {E m p} → Sync sc Rg C s E → Delivers s m p → Owes C p
delivers-owed (s-of d _)                 d-of   = proj₂ (proj₂ (from d (at-out , tt , tt)))
delivers-owed (s-of d _)                 d-ofx  = proj₂ (proj₂ (from d (at-end , tt , tt)))
delivers-owed (s-join _ d _ _ _)         d-join = proj₂ (proj₂ (from d (inj₁ this)))
delivers-owed (s-took _ _ _ (o-cp ow) _ _ _ _ _ _) d-stop = ow
delivers-owed (s-cold _ d _ _)           d-play   = proj₂ (proj₂ (from d (emit-hit , tt , tt)))
delivers-owed (s-cold _ d _ _)           d-ending = proj₂ (proj₂ (from d (at-end , tt , tt)))

-- No list entry, switch or pending program delivers.
ln-none : ∀ {Γ A} {b} {l : St Γ A} {m p} → Delivers (lnS b l) m p → ⊥
ln-none ()
cut-none : ∀ {Γ A} {b a} {l : St Γ A} {m p} → Delivers (cutS b a l) m p → ⊥
cut-none ()
pend-none : ∀ {Γ A} {o : Obs Timeline Γ A} {q m p} → Delivers (pend o q) m p → ⊥
pend-none ()

-- The found mark's key, and none keyed before it, at its own focus.
found-lo : ∀ {R Γ′ A′} (c : Ctx R Γ′ A′) s {Γ A c′ s′ m κ}
         → search top (plug c s) ≡ just (found (Γ , A , c′ , s′) m κ) → (m , κ) ∈ own s′ × Lo (plug c′ s′) κ
found-lo c s {κ = κ} fd with found-least {t = plug c s} fd
... | mi , lo = mi , subst (λ t → Lo t κ) (sym (found-plug c s fd)) lo

-- A delivering mark found: nothing keyed before where it delivers.
lo-at : ∀ {R Γ′ A′} (c : Ctx R Γ′ A′) s {Γ A c′ s′ m κ p}
      → search top (plug c s) ≡ just (found (Γ , A , c′ , s′) m κ) → Delivers s′ m p → Lo (plug c′ s′) (at p)
lo-at c s {c′ = c′} {s′ = s′} fd dl with found-lo c s fd
... | mi , lo = subst (Lo (plug c′ s′)) (delivers-key dl mi) lo

-- No pending subscription owns a mark.
marked-pend : ∀ {Γ A} {s : St Γ A} {m} → Pending s → Marked s m → ⊥
marked-pend {s = s} p mk with pend-shape s p
... | _ , _ , refl with mk
...   | ()


-- What a part no live node reads still runs, kept by a mark's run.
rest-of : ∀ {Γ} {sc : Scope Γ} {D} {A} {i q} {xs : List A} {s″ : St Γ A} {E P} → Quiet s″ → Sealed sc s″ → Rest sc D (ofS i q xs) E P → Rest sc D s″ E P
rest-of q z (_ , h-blank _ _ , le) = _ , h-blank q z , le

rest-join : ∀ {Γ} {sc : Scope Γ} {D} {A} {j g} {x : A ∈ Γ} {ib} {s″ : St Γ A} {E P} → Quiet s″ → Sealed sc s″ → Rest sc D (joinS j g x ib) E P → Rest sc D s″ E P
rest-join q z (_ , h-blank _ _ , le) = _ , h-blank q z , le

rest-cold : ∀ {Γ} {sc : Scope Γ} {D} {A} {b b′} {l l′ : Tape A} {E P} → Rest sc D (coldS b l) E P → Rest sc D (coldS b′ l′) E P
rest-cold (_ , h-blank _ _ , le) = _ , h-blank tt tt₁ , le

rest-take : ∀ {Γ} {sc : Scope Γ} {D} {A} {i} {keep : A → Bool} {w w′ s₀ E P} → Rest sc D (takeS i keep w s₀) E P → Rest sc D (takeS i keep w′ s₀) E P
rest-take (_ , h-blank q z , le) = _ , h-blank q z , le
rest-take (_ , h-take hk u , le) = _ , h-take hk u , le

-- NO MARK, NOTHING OWED.
none-spent : ∀ {R} {t : St [] R} {Rg C E} → Sync unbound Rg C t E → search top t ≡ nothing → Spent C E
none-spent {t = t} sy fd {q} r with seek top t in sk
none-spent {t = t} sy fd {q} r | nothing =
  bound {p = q ⊕ [ ix 0 ]} sy (λ ()) (λ ki → ⊥-elim (seek-none top t sk ki)) r (≺-ext q [])
none-spent sy () r | just _

------------------------------------------------------------------------
-- The steps over a root's entry

-- A takeWhile failing at `p`, inclusive: nothing of it at `p`, its
-- failing value leaving under `p`'s first effect.
fail-nr : ∀ {A} {keep : A → Bool} {Rg Es p a} → Sound Rg Es → Es p (out a) → keep a ≡ false → NoFail (bef p) keep Es
        → NoRow (TakeWhile.TakeT true keep Es) p
fail-nr sd row kf nf (TakeWhile.pass y kt _) v with Sound.fn sd y row v tt
... | refl = subst T kf kt
fail-nr sd row kf nf (TakeWhile.fail {q} y nk _ _) _ = nf y nk (≺-ext q [])
fail-nr sd row kf nf (TakeWhile.stop {q} y nk _) _ = nf y nk (≺-ext q [])
fail-nr sd row kf nf (TakeWhile.step _ _) ()
fail-nr sd row kf nf (TakeWhile.tend y _) v with Sound.fn sd y row v tt
... | ()
fail-nr sd row kf nf (TakeWhile.left _ _ _) ()

module Over {R : Set} (Rt : EmissionSet R) where

  ----------------------------------------------------------------------
  -- A TAKEWHILE'S FIRST FAILURE, INCLUSIVE: the row leaves under `ix 0`,
  -- its first effect, and the frames above move onto it past `p`, where
  -- the take shows nothing; no position lies between.  The frames are
  -- re-cursored under the whole tree's floor, the run's.
  rise-take-failᵢ : ∀ {Γ A} {w : A → Bool} {c : Ctx R Γ A} {s a p} → w a ≡ false → Lo (plug c (takeS true w free s)) (after p)
                  → SimC Rt ⟨ inTake true w free c , s , rising (nx a) , p ⟩ [] ⟨ c , takeS true w (cpAt p) s , rising (nx a) , p ⊕ [ ix 0 ] ⟩
  rise-take-failᵢ {w = w} {c = c} {s = s} {a = a} {p = p} wa fl (flying (f-take {E = Es} {E′ = E′} fr nf eq sd) cl (sy , row)) =
    let (Cr′ , fr′ , _ , _ , d) = rc Rt {s = takeS true w free s} fr (hr λ _ _ → lag [ p ] (λ _ o yp → here (at-p o yp)) , bnd) (≺→≼ {p} {p ⊕ [ ix 0 ]} p0)
                                    (lo-weaken (at (p ⊕ [ ix 0 ])) (after p) fl (at-after p [ ix 0 ]))
    in Cr′ , bef (p ⊕ [ ix 0 ]) ,
       flying fr′ cl (s-took (a , row , nk , λ (_ , _ , y , nk′ , qp) → nf y nk′ qp) gone (λ _ → ≺-irrefl {p ⊕ [ ix 0 ]}) (o-cp (slot-last (nested p) 0))
                             (tailp-dn {C = bef p} {C′ = aft (p ⊕ [ ix 0 ])} (λ {y} t → gone {y} t) (took-tail sy row nk nf)) (proj₂ (husk-of sy))
                             (λ {r} t → ≼-trans {r} {p} {p ⊕ [ ix 0 ]} t (≺→≼ {p} {p ⊕ [ ix 0 ]} p0))
                             (λ {r′} t (q , _ , y , nk′ , qr) → nf y nk′ (≺-≼-≺ {q} {r′} {p} qr t)) eq sd
                    , proj₁ (to (alike eq) (TakeWhile.fail row nk (λ (_ , _ , y , nk′ , qp) → nf y nk′ qp) tt , _))) ,
       silent (vis-≃ d)
    where
      p0 : p ≺ (p ⊕ [ ix 0 ])
      p0 = ≺-ext p []
      nk : T (not (w a))
      nk = subst (λ b → T (not b)) (sym wa) tt
      at-p : ∀ {y} → p ≼ y → y ≺ (p ⊕ [ ix 0 ]) → y ≡ p
      at-p {y} o yp = ≼-antisym {y} {p} (λ py → first-child p py yp) o
      gone : ∀ {q} → (p ⊕ [ ix 0 ]) ≺ q → p ≼ q
      gone {q} t = ≺→≼ {p} {q} (≺-trans {p} {p ⊕ [ ix 0 ]} {q} p0 t)
      bnd : ∀ {q e} → Due (bef p) E′ q e → (p ⊕ [ ix 0 ]) ≼ q
      bnd {q} (y , v , o) yp with at-p {q} o yp
      ... | refl = let (y′ , v′) = from (alike eq) (y , v) in fail-nr sd row wa nf y′ v′
  rise-take-failᵢ wa fl (flying (f-took _ _ _ _ _ _ _ _ _ _) _ ())
  rise-take-failᵢ wa fl (flying (d-take _ _) _ ())
  rise-take-failᵢ wa fl (adrift (f-took _ _ _ _ () _ _ _ _ _) _ _)
  rise-take-failᵢ wa fl {Cr} {C} (adrift (d-take fr u) cl (Q , hk , le)) = Cr , C , adrift fr cl (Q , h-take hk u , le) , silent ≃-refl
  rise-take-failᵢ wa fl (settled () _ _)

  ----------------------------------------------------------------------
  -- A SUBSCRIPTION OWED, whichever way the invariant holds it: pending,
  -- or a connect's source not yet subscribed.  No part no live node
  -- reads holds one.
  PendV : ∀ {Γ A} → Cur → Cur → Ctx R Γ A → Obs Timeline Γ A → Pos → Set₁
  PendV {A = A} Cr C c o q =
      Σ Rgn λ Rg → Σ (EmissionSet A) λ E → Fr Rt Cr C Rg c owes E
         × Owes C q × Ok (Hots (full (scopeOf c))) q × Adm (scopeOf c) × pendRows (full (scopeOf c)) o q ≈ E × Within Rg (scopeOf c) q (pendRows (full (scopeOf c)) o q)

  -- A pending source, read as subscribing.
  srcp : ∀ {Cr C Γ A} {c : Ctx R Γ A} {o q Rg N E} → Fr Rt Cr C Rg c N E → N ≡ pnd q
       → pendRows (full (scopeOf c)) o q ≈ E → Within Rg (scopeOf c) q (pendRows (full (scopeOf c)) o q) → PendV Cr C c o q
  srcp {C = C} (f-srcp {k = k} fr sc pt lv nc na ba an (ok , adm) bs bb fl fe eq ow sd nb) refl pe wn =
    (_ , _ , f-src fr sc pt lv nc bs bb fl fe eq (behind-pend {C = C} {k = k} sc (ok , adm) ow) sd (λ t → ⊥-elim (notT _ na t)) (λ _ → inj₂ (ba , an)) (λ _ → owes-call {k = k} C ow) nb , ow , ok-step (CS.connAt k) ok , adm , pe , wn)
  srcp (f-islep {k = k} u hb ub le na nc ba an sc (ok , adm) ss bu nr nb oz iz) refl pe wn =
    (_ , _ , f-isle u hb ub le na nc (behind-pend {C = bef (CS.connAt k ⊕ [ ix 1 ])} {k = k} sc (ok , adm) (≼-refl {CS.connAt k ⊕ [ ix 1 ]}))
                         (subd (λ o → o) ok) ss (inj₂ (ba , an)) (owes-call {k = k} (bef (CS.connAt k ⊕ [ ix 1 ])) (≼-refl {CS.connAt k ⊕ [ ix 1 ]})) bu nr nb oz iz
         , ≼-refl {CS.connAt k ⊕ [ ix 1 ]} , ok-step (CS.connAt k) ok , adm , pe , wn)
  srcp (f-top _)                                                ()   _ _
  srcp (f-map _ _ _)                                            ()   _ _
  srcp (f-scan _ _ _ _)                                         ()   _ _
  srcp (f-cut _)                                                ()   _ _
  srcp (f-take _ _ _ _)                                         ()   _ _
  srcp (f-took _ _ _ _ _ _ _ _ _ _)                                 ()   _ _
  srcp (f-outer _ _ _ _ _ _)                                    ()   _ _
  srcp (f-lanes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)    ()   _ _
  srcp (f-lane _)                                               ()   _ _
  srcp (f-lnct {b = true} _)                                    ()   _ _
  srcp (f-lnct {b = false} _)                                   ()   _ _
  srcp (f-src _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)                  ()   _ _
  srcp (f-srcc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)                   ()   _ _
  srcp (f-body _ _ _ _ _ _ _ _)                                 ()   _ _
  srcp (d-map _ _)                                                ()   _ _
  srcp (d-scan _ _)                                               ()   _ _
  srcp (d-cut _ _)                                                ()   _ _
  srcp (d-ln _ _)                                                 ()   _ _
  srcp (d-take _ _)                                               ()   _ _
  srcp (d-outer _ _ _ _)                                          ()   _ _
  srcp (d-lanes _ _ _ _ _ _ _)                                      ()   _ _
  srcp (d-src _ _ _ _ _ _ _ pz oz iz)                                        ()   _ _
  srcp (d-body _ _ _ _ oz iz)                                           ()   _ _
  srcp (f-isle _ _ _ _ _ _ _ _ _ _ _ _ _ _ oz iz)                     ()   _ _
  srcp (f-islec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ oz iz)                  ()   _ _

  pend-view : ∀ {Cr C Γ A} {c : Ctx R Γ A} {o q p} → Inv Rt Cr C ⟨ c , pend o q , subscribing , p ⟩ → PendV Cr C c o q
  pend-view (pending fr h)                                     = _ , _ , fr , h
  pend-view {o = o} {q} (settled {N = owes} c-sub fr h)       = ⊥-elim (sync-pend {s = pend o q} tt h)
  pend-view (settled {N = dead _ _} c-sub fr (_ , h-blank () _ , _))
  pend-view (settled {N = lane _ _ _} c-sub fr (_ , _ , () , _))
  pend-view (settled {N = lanecut _ _ _} c-sub fr (_ , _ , () , _))
  pend-view {o = o} (settled {N = pnd _} c-sub fr (_ , refl , pe , wn)) = srcp {o = o} fr refl pe wn

  -- A joiner of a live subject: joined where it subscribed.
  sub-join : ∀ {Cr C Γ A} {c : Ctx R Γ A} {x : A ∈ Γ} {q p} → closedUp c x ≡ false
           → Inv Rt Cr C ⟨ c , pend (connected x) q , subscribing , p ⟩ → Inv Rt Cr C ⟨ c , joinS q true x [] , absorbed , q ⟩
  sub-join cu i with pend-view i
  ... | _ , _ , fr , h = join-pend Rt cu fr h

  -- A joiner of a completed subject, ended at or before it subscribed:
  -- its end owed, under `last`.
  sub-joined : ∀ {Cr C Γ A} {c : Ctx R Γ A} {x : A ∈ Γ} {q p} → closedUp c x ≡ true → endUp c x ≼ q
             → Inv Rt Cr C ⟨ c , pend (connected x) q , subscribing , p ⟩ → Inv Rt Cr C ⟨ c , ofS 0 q [] , absorbed , q ⟩
  sub-joined {x = x} cu eb i with pend-view i
  ... | _ , _ , fr , h = joined-pend Rt fr (ended-up Rt fr x cu) eb h

  -- SUBSCRIPTIONS keep the cursors: what the pending program owed is
  -- what the subscribed nodes owe.  An of owes every row it has.
  sub-of : ∀ {Cr C Γ A} {c : Ctx R Γ A} {xs : List A} {q p}
         → Inv Rt Cr C ⟨ c , pend (of xs) q , subscribing , p ⟩ → Inv Rt Cr C ⟨ c , ofS 0 q xs , absorbed , q ⟩
  sub-of {C = C} {xs = xs} {q} i with pend-view i
  ... | _ , _ , fr , (ow , _ , _ , eq , _) = settled c-abs fr (settle-of eq proj₁ (λ r → r , of-reach q 0 xs) (of-owes C q 0 xs ow))

  -- A cold subscribed: its tape owes its timeline's stream from there.
  sub-cold : ∀ {Cr C Γ A} {c : Ctx R Γ A} {x : Timeline A} {q p}
           → Inv Rt Cr C ⟨ c , pend (cold x) q , subscribing , p ⟩ → Inv Rt Cr C ⟨ c , coldS true (opening q (timelineAt x q)) , absorbed , q ⟩
  sub-cold {x = x} {q} i with pend-view i
  ... | _ , _ , fr , (ow , ok , ad , eq , wi) = settled c-abs fr (cold-sync x q ok ad ow eq wi)

  sub-empty : ∀ {Cr C Γ A} {c : Ctx R Γ A} {q p}
            → Inv Rt Cr C ⟨ c , pend empty q , subscribing , p ⟩ → Inv Rt Cr C ⟨ c , ofS 0 q [] , absorbed , q ⟩
  sub-empty {C = C} {A = A} {q = q} i with pend-view i
  ... | _ , _ , fr , (ow , _ , _ , eq , _) = settled c-abs fr (settle-of eq proj₁ (λ r → r , of-reach {A} q 0 []) (of-owes C {A} q 0 [] ow))

  -- A joiner's entry, its outer's entered where it subscribed.
  flat-entry : ∀ {Γ A B} (sc : Scope Γ) op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) q {E}
             → pendRows (full sc) (flatMap op f s) q ≈ E → JoinE sc op f (s , q) (pendRows (full sc) s q) E
  flat-entry sc (mergeᶠ nothing)  f s q eq = refl , eq
  flat-entry sc (mergeᶠ (just m)) f s q eq = refl , eq
  flat-entry sc switchᶠ           f s q eq = refl , eq
  flat-entry sc exhaustᶠ          f s q eq = refl , eq

  -- A connect pending at `q`: none of its rows before its first child.
  conn-hr : ∀ {Γ A B} {sc : Scope Γ} {s : Obs Timeline Γ A} {b : Obs Timeline (A ∷ Γ) B} {q C E} → Adm sc → Ok (Hots (full sc)) q
          → pendRows (full sc) (connect s b) q ≈ E → HR C (q ⊕ [ ix 0 ]) sc E
  conn-hr {sc = sc} {s = s} {b} {q} {C} {E} ad ok pe = hr λ _ _ → lag (proj₁ (cov pe)) has , bd
    where
      past : ∀ {y e} → pendRows (full sc) (connect s b) q y e → (q ⊕ [ ix 0 ]) ≼ y
      past r = first-child q (pend-past sc (connect s b) ad ok r)
      has : ∀ {y e} → E y e → Owes C y → y ≺ (q ⊕ [ ix 0 ]) → y ∈ proj₁ (cov pe)
      has x _ yq with proj₂ (cov pe) x
      ... | inj₁ r = ⊥-elim (past r yq)
      ... | inj₂ i = i
      bd : ∀ {y e} → Due C E y e → (q ⊕ [ ix 0 ]) ≼ y
      bd (x , v , _) = past (proj₁ (from (alike pe) (x , v)))

  -- A CONNECT SUBSCRIBED: the cursor moves to its body's subscription,
  -- the connect behind it, nothing owed passed.
  sub-conn : ∀ {Γ A B} {c : Ctx R Γ B} {s : Obs Timeline Γ A} {b q p}
           → Lo (plug c (pend (connect s b) q)) (at (q ⊕ [ ix 0 ]))
           → SimC Rt ⟨ c , pend (connect s b) q , subscribing , p ⟩ []
                     ⟨ inBody (conn₀ s q (scopeOf c)) (pend s (q ⊕ [ ix 1 ])) c , pend b (q ⊕ [ ix 0 ]) , subscribing , q ⊕ [ ix 0 ] ⟩
  sub-conn {c = c} {s = s} {b = b} {q = q} lo {C = C} i with pend-view i
  ... | Rg , _ , fr , ow , ok , ad , eq , wi
    with rc Rt {s = pend (connect s b) q} fr (conn-hr {s = s} {b = b} ad ok eq) (owes-≼ C {q} {q ⊕ [ ix 0 ]} ow (≺→≼ {q} {q ⊕ [ ix 0 ]} (≺-ext q []))) lo
  ...   | Cr′ , fr′ , _ , _ , d =
    let (pt , wb , ws) = conn-parts {s = s} {b = b} ok ad wi
        ow₁ = ≺→≼ {q ⊕ [ ix 0 ]} {q ⊕ [ ix 1 ]} (ticks q 0)
        -- fresh: its source's rows and its body's all still owed
        fl : Flags (bef (q ⊕ [ ix 0 ])) (conn₀ s q (scopeOf c)) (pendRows (full (binds s q (scopeOf c))) b (q ⊕ [ ix 0 ]))
        fl = record { shut = λ () ; torn = λ () ; owed = λ () ; owing = λ ()
                    ; unshut = λ _ {c′} y n → ⊥-elim (n (owes-≼ (bef (q ⊕ [ ix 0 ])) {q ⊕ [ ix 1 ]} {c′} ow₁ (≺→≼ {q ⊕ [ ix 1 ]} {c′} (pend-past (scopeOf c) s ad (ok-step q ok) y))))
                    ; ended = λ _ {c′} y n → ⊥-elim (n (≺→≼ {q ⊕ [ ix 0 ]} {c′} (pend-past (binds s q (scopeOf c)) b (ok , ad) (conn-ok {s = s} ok ad) y))) }
    in Cr′ , bef (q ⊕ [ ix 0 ]) ,
       pending (f-body fr′ refl pt tt (src-pend tt tt refl refl (ok , ad) ≈-refl ws ow₁ (≼-refl {q ⊕ [ ix 0 ]}))
                 (behind-past (bef (q ⊕ [ ix 0 ])) {q ⊕ [ ix 0 ]} (≼-refl {q ⊕ [ ix 0 ]}) (pend-past (binds s q (scopeOf c)) b (ok , ad) (conn-ok {s = s} ok ad))) fl
                 (eq , entered-reach (⟦ b ⟧ (full (binds s q (scopeOf c)))) (q ⊕ [ ix 0 ])))
         (≼-refl {q ⊕ [ ix 0 ]} , conn-ok {s = s} ok ad , (ok , ad) , ≈-refl , wb) ,
       silent (vis-≃ d)

  sub-flat : ∀ {Cr C Γ A B} {c : Ctx R Γ B} {op} {f : A → Obs Timeline Γ B} {s q p}
           → Inv Rt Cr C ⟨ c , pend (flatMap op f s) q , subscribing , p ⟩
           → Inv Rt Cr C ⟨ inCut true (attAt q) (inOuter op f (s , q) false 0 [] [] c) , pend s q , subscribing , q ⟩
  sub-flat {C = C} {c = c} {op = op} {f = f} {s = s} {q = q} i with pend-view i
  ... | Rg , _ , fr , ow , ok , ad , eq , wi =
    pending (f-cut (f-outer fr (flat-jinv {f = f} {s = s} ok ad) (flat-joined {op = op} {f = f} {s = s} ow ok ad wi)
              (flat-entry (scopeOf c) op f s q eq) (flat-sound {op = op} {f = f} {s = s} ok ad wi)
              (behind-past C ow (join-past (scopeOf c) op f s ad ok))))
            (ow , ok , ad , ≈-refl , flat-within {op = op} {f = f} {s = s} ok ad wi)

  -- An of's next row, delivered from where the cursor stands before it.
  run-of-nx : ∀ {Cr Γ A} {c : Ctx R Γ A} {i q x xs r} → closed c ≡ false
            → Inv Rt Cr (bef (q ⊕ [ ix i ])) ⟨ c , ofS i q (x ∷ xs) , absorbed , r ⟩
            → Inv Rt Cr (bef (q ⊕ [ ix i ])) ⟨ c , ofS (suc i) q xs , rising (nx x) , q ⊕ [ ix i ] ⟩
  run-of-nx cl (settled {N = owes}           _ fr h)              = flying fr cl (of-nx h)
  run-of-nx cl (settled {N = dead _ _}       _ fr h)              = adrift fr cl (rest-of tt tt₁ h)
  run-of-nx cl (settled {N = lane _ _ _}     _ fr (_ , _ , () , _))
  run-of-nx cl (settled {N = lanecut _ _ _}  _ fr (_ , _ , () , _))
  run-of-nx cl (settled {N = pnd _}          _ fr (_ , () , _))

  run-of-end : ∀ {Cr Γ A} {c : Ctx R Γ A} {i q r} → closed c ≡ false
             → Inv Rt Cr (bef (q ⊕ [ last ])) ⟨ c , ofS i q [] , absorbed , r ⟩
             → Inv Rt Cr (bef (q ⊕ [ last ])) ⟨ c , doneS , rising cp , q ⊕ [ last ] ⟩
  run-of-end cl (settled {N = owes}          _ fr h)              = flying fr cl (of-cp h)
  run-of-end cl (settled {N = dead _ _}      _ fr h)              = adrift fr cl (rest-of tt tt₁ h)
  run-of-end cl (settled {N = lane _ _ _}    _ fr (_ , _ , () , _))
  run-of-end cl (settled {N = lanecut _ _ _} _ fr (_ , _ , () , _))
  run-of-end cl (settled {N = pnd _}         _ fr (_ , () , _))

  run-join-nx : ∀ {Cr Γ A} {c : Ctx R Γ A} {j} {x : A ∈ Γ} {q a ib r} → closed c ≡ false
              → Inv Rt Cr (bef q) ⟨ c , joinS j true x ((q , nx a) ∷ ib) , absorbed , r ⟩
              → Inv Rt Cr (bef q) ⟨ c , joinS j true x ib , rising (nx a) , q ⟩
  run-join-nx cl (settled {N = owes}          _ fr h)              = flying fr cl (join-nx h)
  run-join-nx cl (settled {N = dead _ _}      _ fr h)              = adrift fr cl (rest-join tt tt₁ h)
  run-join-nx cl (settled {N = lane _ _ _}    _ fr (_ , _ , () , _))
  run-join-nx cl (settled {N = lanecut _ _ _} _ fr (_ , _ , () , _))
  run-join-nx cl (settled {N = pnd _}         _ fr (_ , () , _))

  run-join-cp : ∀ {Cr Γ A} {c : Ctx R Γ A} {j} {x : A ∈ Γ} {q ib r} → closed c ≡ false
              → Inv Rt Cr (bef q) ⟨ c , joinS j true x ((q , cp) ∷ ib) , absorbed , r ⟩
              → Inv Rt Cr (bef q) ⟨ c , joinS j false x ib , rising cp , q ⟩
  run-join-cp cl (settled {N = owes}          _ fr h)              = flying fr cl (join-cp h)
  run-join-cp cl (settled {N = dead _ _}      _ fr h)              = adrift fr cl (rest-join tt tt₁ h)
  run-join-cp cl (settled {N = lane _ _ _}    _ fr (_ , _ , () , _))
  run-join-cp cl (settled {N = lanecut _ _ _} _ fr (_ , _ , () , _))
  run-join-cp cl (settled {N = pnd _}         _ fr (_ , () , _))

  -- A cold's next value, or its end, delivered.
  run-cold-nx : ∀ {Cr Γ A} {c : Ctx R Γ A} {τ u i t a} {k : Frame A t} {r} → closed c ≡ false
              → Inv Rt Cr (bef (u ▸ ix i)) ⟨ c , coldS true (play τ u i t (emit a k)) , absorbed , r ⟩
              → Inv Rt Cr (bef (u ▸ ix i)) ⟨ c , coldS true (play τ u (suc i) t k) , rising (nx a) , u ▸ ix i ⟩
  run-cold-nx cl (settled {N = owes}          _ fr h)              = flying fr cl (cold-nx h)
  run-cold-nx cl (settled {N = dead _ _}      _ fr h)              = adrift fr cl (rest-cold h)
  run-cold-nx cl (settled {N = lane _ _ _}    _ fr (_ , _ , () , _))
  run-cold-nx cl (settled {N = lanecut _ _ _} _ fr (_ , _ , () , _))
  run-cold-nx cl (settled {N = pnd _}         _ fr (_ , () , _))

  run-cold-cp : ∀ {Cr Γ A} {c : Ctx R Γ A} {e r} → closed c ≡ false
              → Inv Rt Cr (bef e) ⟨ c , coldS {A = A} true (ending e) , absorbed , r ⟩
              → Inv Rt Cr (bef e) ⟨ c , coldS false over , rising cp , e ⟩
  run-cold-cp cl (settled {N = owes}          _ fr h)              = flying fr cl (cold-cp h)
  run-cold-cp cl (settled {N = dead _ _}      _ fr h)              = adrift fr cl (rest-cold h)
  run-cold-cp cl (settled {N = lane _ _ _}    _ fr (_ , _ , () , _))
  run-cold-cp cl (settled {N = lanecut _ _ _} _ fr (_ , _ , () , _))
  run-cold-cp cl (settled {N = pnd _}         _ fr (_ , () , _))

  -- A skip dropped from a cold's tape: nothing owed moves.
  cold-skip : ∀ {Cr C Γ A} {c : Ctx R Γ A} {l l′ : Tape A} {r} (y₀ : Pos) → (Ticked l → Ticked l′)
            → (∀ {y e} → InE (tapeE l′) y e → InE (tapeE l) y e)
            → (∀ {y e} → InE (tapeE l) y e → InE (tapeE l′) y e ⊎ (y ≡ y₀ × e ≡ skip))
            → Inv Rt Cr C ⟨ c , coldS true l , absorbed , r ⟩ → Inv Rt Cr C ⟨ c , coldS true l′ , absorbed , r ⟩
  cold-skip y₀ tk into back (settled {N = owes}          _ fr h)              = settled c-abs fr (cold-drop y₀ tk into back h)
  cold-skip y₀ tk into back (settled {N = dead _ _}      _ fr h)              = settled c-abs fr (rest-cold h)
  cold-skip y₀ tk into back (settled {N = lane _ _ _}    _ fr (_ , _ , () , _))
  cold-skip y₀ tk into back (settled {N = lanecut _ _ _} _ fr (_ , _ , () , _))
  cold-skip y₀ tk into back (settled {N = pnd _}         _ fr (_ , () , _))

  -- A completed cold's tape dropped.
  coldx-hold : ∀ {Γ A} {sc : Scope Γ} {Rg C N} {l l′ : Tape A} {E}
             → Hold sc Rg C N (coldS false l) E → Hold sc Rg C N (coldS false l′) E
  coldx-hold {N = owes}          (s-coldx sp fn)        = s-coldx sp fn
  coldx-hold {N = dead _ _}      (_ , h-blank _ _ , le) = _ , h-blank tt tt₁ , le
  coldx-hold {N = lane _ _ _}    (_ , _ , () , _)
  coldx-hold {N = lanecut _ _ _} (_ , _ , () , _)
  coldx-hold {N = pnd _}         (_ , () , _)

  coldx-off : ∀ {Cr C Γ A} {c : Ctx R Γ A} {l l′ : Tape A} {r}
            → Inv Rt Cr C ⟨ c , coldS false l , absorbed , r ⟩ → Inv Rt Cr C ⟨ c , coldS false l′ , absorbed , r ⟩
  coldx-off (settled _ fr h) = settled c-abs fr (coldx-hold h)

  -- A defer subscribed: its body at its second child, owing what the
  -- defer owed but its guard.
  sub-defer : ∀ {Cr C Γ A} {c : Ctx R Γ A} {l q p}
            → Inv Rt Cr C ⟨ c , pend (defer l) q , subscribing , p ⟩
            → Inv Rt Cr C ⟨ c , pend (Later.force l) (q ⊕ [ ix 1 ]) , subscribing , q ⊕ [ ix 1 ] ⟩
  sub-defer {C = C} {c = c} {l = l} {q = q} i with pend-view i
  ... | _ , _ , fr , ow , ok , ad , eq , wi with DeferEntry.entry (scopeOf c) l q ok ad wi
  ...   | m , wi′ = pending fr (owes-≼ C {q} {q ⊕ [ ix 1 ]} ow (≺→≼ {q} {q ⊕ [ ix 1 ]} (≺-ext q [])) , ok-step q ok , ad , ≈-trans m eq , wi′)

  -- A node over one source: the source subscribed under it at the same
  -- place, owing what the node owed.
  sub-map : ∀ {Cr C Γ A B} {c : Ctx R Γ B} {f : A → B} {s q p}
          → Inv Rt Cr C ⟨ c , pend (map f s) q , subscribing , p ⟩ → Inv Rt Cr C ⟨ inMap f c , pend s q , subscribing , q ⟩
  sub-map {c = c} {s = s} {q} i with pend-view i
  ... | _ , _ , fr , ow , ok , ad , eq , wi with Entry.map-entry (scopeOf c) s q ok ad wi
  ...   | m , sd , wi′ = pending (f-map fr (≈-trans m eq) sd) (ow , ok , ad , ≈-refl , wi′)

  sub-scan : ∀ {Cr C Γ A B} {c : Ctx R Γ B} {f : B → A → B} {z s q p}
           → Inv Rt Cr C ⟨ c , pend (scan f z s) q , subscribing , p ⟩ → Inv Rt Cr C ⟨ inScan f z c , pend s q , subscribing , q ⟩
  sub-scan {C = C} {c = c} {s = s} {q} i with pend-view i
  ... | _ , _ , fr , ow , ok , ad , eq , wi with Entry.scan-entry (scopeOf c) s q ok ad wi
  ...   | m , sd , wi′ = pending (f-scan fr (fd-none (Entry.owed (scopeOf c) s q ok ad {C = C} ow)) (≈-trans m eq) sd) (ow , ok , ad , ≈-refl , wi′)

  sub-take : ∀ {Cr C Γ A} {c : Ctx R Γ A} {i} {w : A → Bool} {s q p}
           → Inv Rt Cr C ⟨ c , pend (takeWhile i w s) q , subscribing , p ⟩
           → Inv Rt Cr C ⟨ inCut true (attAt q) (inTake i w free c) , pend s q , subscribing , q ⟩
  sub-take {C = C} {c = c} {s = s} {q} iv with pend-view iv
  ... | _ , _ , fr , ow , ok , ad , eq , wi with Entry.take-entry (scopeOf c) s q ok ad wi
  ...   | m , sd , wi′ = pending (f-cut (f-take fr (λ x _ → Entry.owed (scopeOf c) s q ok ad {C = C} ow x) (≈-trans m eq) sd)) (ow , ok , ad , ≈-refl , wi′)

  ----------------------------------------------------------------------
  -- THE SEARCH: the tree zipped up at the root's cursor, and unzipped
  -- down to the mark found, along a clear path.

  search-none : ∀ {Cr C Γ A} {c : Ctx R Γ A} {s p}
              → Inv Rt Cr C ⟨ c , s , absorbed , p ⟩ → search top (plug c s) ≡ nothing → Spent Cr Rt
  search-none {Cr} (settled _ fr h) fd with climb Rt fr h
  ... | _ , _ , e , sy = λ d → none-spent sy fd (from (due-≈ {C = Cr} e) d)

  -- A search's outcome: the hole's cursor just before what the mark
  -- delivers, the root's moved over nothing it owes; or the mark in a
  -- part no live node reads.
  Next : ∀ {Γ A} → Cur → Ctx R Γ A → St Γ A → Pos → Pos → Set₁
  Next {A = A} Cr c s r p =
      (Σ Cur λ Cr′ → Inv Rt Cr′ (bef p) ⟨ c , s , absorbed , r ⟩ × Vis (RT Rt Cr) ≃ Vis (RT Rt Cr′))
    ⊎ (Σ Cur λ C → Σ Rgn λ Rg → Σ Pts λ P → Σ (EmissionSet A) λ E → Σ Cur λ D → Fr Rt Cr C Rg c (dead D P) E × Rest (scopeOf c) D s E P)

  search-least : ∀ {Cr C Γ A} {c : Ctx R Γ A} {s r Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ p}
               → Inv Rt Cr C ⟨ c , s , absorbed , r ⟩ → Clear c′
               → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , s′) m κ) → Delivers s′ m p → Next Cr c′ s′ r p
  search-least {c = c} {s = s} {c′ = c′} {s′ = s′} (settled _ fr h) cl fd dl with climb Rt fr h
  ... | _ , _ , e , sy with descend Rt c′ s′ (λ x → marked-pend x (found-mark c s fd)) cl (subst (λ t → Sync unbound _ _ t _) (sym (found-plug c s fd)) sy) e
  ...   | C′ , dead D P , Rg , E , fr′ , h′                  = inj₂ (C′ , Rg , P , E , D , fr′ , h′)
  ...   | _ , lane _ _ _ , _ , _ , _ , (_ , _ , refl , _)   = ⊥-elim (ln-none dl)
  ...   | _ , lanecut _ _ _ , _ , _ , _ , (_ , _ , refl , _) = ⊥-elim (cut-none dl)
  ...   | _ , pnd _ , _ , _ , _ , (_ , refl , _)            = ⊥-elim (pend-none dl)
  ...   | _ , owes , _ , _ , fr′ , h′ with fr-shift Rt fr′ h′ (delivers-owed h′ dl) (lo-at c s fd dl)
  ...     | Cr′ , fr″ , h″ , d = inj₁ (Cr′ , settled c-abs fr″ h″ , vis-≃ d)

  -- A search's outcome, run: the node's run at the shifted cursor, or
  -- adrift in what it still runs.
  stepped : ∀ {Cr Γ A} {c′ : Ctx R Γ A} {s′ r p s″ e″ p″} → closed c′ ≡ false → Next Cr c′ s′ r p
          → (∀ {Cr′} → Inv Rt Cr′ (bef p) ⟨ c′ , s′ , absorbed , r ⟩ → Inv Rt Cr′ (bef p) ⟨ c′ , s″ , rising e″ , p″ ⟩)
          → (∀ {D E P} → Rest (scopeOf c′) D s′ E P → Rest (scopeOf c′) D s″ E P)
          → Σ Cur λ Cr′ → Σ Cur λ C′ → Inv Rt Cr′ C′ ⟨ c′ , s″ , rising e″ , p″ ⟩ × Moves (RT Rt Cr) [] (RT Rt Cr′)
  stepped      _  (inj₁ (Cr′ , i , d))              g _  = Cr′ , _ , g i , silent d
  stepped {Cr} cl (inj₂ (C′ , _ , _ , _ , _ , fr , h)) _ tr = Cr , C′ , adrift fr cl (tr h) , silent ≃-refl

  -- A torn joiner's row dropped: nothing owed before, nothing after.
  joinx-hold : ∀ {Γ A} {sc : Scope Γ} {Rg C N j} {x : A ∈ Γ} {u ib E}
             → Hold sc Rg C N (joinS j false x (u ∷ ib)) E → Hold sc Rg C N (joinS j false x ib) E
  joinx-hold {N = owes}        (s-joinx sp fn)     = s-joinx sp fn
  joinx-hold {N = dead _ _}      (_ , h-blank _ _ , le) = _ , h-blank tt tt₁ , le
  joinx-hold {N = lane _ _ _}    (_ , _ , () , _)
  joinx-hold {N = lanecut _ _ _} (_ , _ , () , _)
  joinx-hold {N = pnd _}       (_ , () , _)

  join-off : ∀ {Cr C Γ A} {c : Ctx R Γ A} {j} {x : A ∈ Γ} {u ib r p}
           → Inv Rt Cr C ⟨ c , joinS j false x (u ∷ ib) , absorbed , r ⟩ → Inv Rt Cr C ⟨ c , joinS j false x ib , absorbed , p ⟩
  join-off (settled _ fr h) = settled c-abs fr (joinx-hold h)

  off-keep : ∀ {Cr C Γ A} {c : Ctx R Γ A} {Rg N E} {s s′ : St Γ A} {p} → (Pending s → ⊥) → (∀ {D E P} → Rest (scopeOf c) D s E P → Rest (scopeOf c) D s′ E P)
           → Fr Rt Cr C Rg c N E → Hold (scopeOf c) Rg C N s E → Off N → Inv Rt Cr C ⟨ c , s′ , absorbed , p ⟩
  off-keep {N = owes}        _  _  _  _           ()
  off-keep {N = dead _ _}      _  tr fr h           _ = settled c-abs fr (tr h)
  off-keep {N = lane _ _ _}    _  _  _  _           ()
  off-keep {N = lanecut _ _ _} _  _  _  _           ()
  off-keep {N = pnd _}       np _  _  (_ , e , _) _ = ⊥-elim (np (subst Pending (sym e) tt))

  -- A run under a closed context delivers nothing and owes nothing.
  closed-keep : ∀ {Cr C Γ A} {c : Ctx R Γ A} {s s′ : St Γ A} {r p} → closed c ≡ true → (Pending s → ⊥)
              → (∀ {D E P} → Rest (scopeOf c) D s E P → Rest (scopeOf c) D s′ E P)
              → Inv Rt Cr C ⟨ c , s , absorbed , r ⟩ → Inv Rt Cr C ⟨ c , s′ , absorbed , p ⟩
  closed-keep cl np tr (settled _ fr h) = off-keep np tr fr h (closed-off Rt fr (subst T (sym cl) tt))

  -- A mark delivering nothing keeps the root's cursor: the focus moved
  -- to it, along a clear path.
  search-quiet : ∀ {Cr C Γ A} {c : Ctx R Γ A} {s r Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ}
               → Inv Rt Cr C ⟨ c , s , absorbed , r ⟩ → Clear c′
               → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , s′) m κ)
               → Σ Cur λ C′ → Inv Rt Cr C′ ⟨ c′ , s′ , absorbed , r ⟩
  search-quiet {c = c} {s = s} i cl fd = refocus Rt i (found-plug c s fd) (λ x → marked-pend x (found-mark c s fd)) cl

  refocused : ∀ {k k′ Γ A} {c′ : Ctx R Γ A} {s′ r}
            → (∀ {Cr C} → Inv Rt Cr C k → Σ Cur λ C′ → Inv Rt Cr C′ ⟨ c′ , s′ , absorbed , r ⟩)
            → (∀ {Cr C} → Inv Rt Cr C ⟨ c′ , s′ , absorbed , r ⟩ → Inv Rt Cr C k′) → SimC Rt k [] k′
  refocused q g {Cr} i with q i
  ... | C′ , i′ = Cr , C′ , g i′ , silent ≃-refl

  ----------------------------------------------------------------------
  -- A CONNECT'S OWN MARKS: its source subscribed, attached or torn
  -- down, nothing shown.  Subscribing moves the cursors: the source's
  -- frame reads `Subd`, so the hole's cursor stands at the connect's
  -- `ix 1`, and only the mark's being least over the whole tree keeps
  -- what the root owes.
  run-con : ∀ {Cr C Γ A X} {c : Ctx R Γ A} {k} {o : St Γ X} {b m κ r k′ sh t}
          → m ≡ bodyM ⊎ (m ≡ srcAttM ⊎ m ≡ owedM) → run c (connS k o b) m r ≡ moved k′ sh t
          → (m , κ) ∈ own (connS k o b) → Lo (plug c (connS k o b)) κ → StOK (connS k o b) → G (connS k o b)
          → Inv Rt Cr C ⟨ c , connS k o b , absorbed , r ⟩
          → sh ≡ [] × Ran Rt Cr k′
  run-con {c = c} {k = cs cl sl sa (just p) as ow cx ea sr sc} {o} {b} (inj₁ refl) refl mi lo st g i
    with own-cls (cs cl sl sa (just p) as ow cx ea sr sc) {o} {b} mi | pend-of o (proj₂ (proj₂ st))
  ... | ob refl | o₀ , refl = refl , con-body Rt (body-noisle c st g refl lo) lo i
  run-con {Cr} {C} {k = cs cl sl sa nothing as ow cx ea sr sc} (inj₁ refl) refl mi lo st g i = refl , Cr , C , i , silent ≃-refl
  run-con {c = c} {k = cs cl sl sa bd (just y) ow cx ea sr sc} {o} {b} (inj₂ (inj₁ refl)) refl mi lo st g i
    with own-cls (cs cl sl sa bd (just y) ow cx ea sr sc) {o} {b} mi
  ... | os refl = refl , con-att Rt (λ ki → lo (plug-in c (k-kid (k-src ki)))) i
  run-con {k = cs cl sl sa bd nothing ow cx ea sr sc} {o} {b} (inj₂ (inj₁ refl)) _ mi lo st g i
    with own-cls (cs cl sl sa bd nothing ow cx ea sr sc) {o} {b} mi
  ... | os ()
  run-con {k = cs cl sl sa bd as (just q) cx ea sr sc} (inj₂ (inj₂ refl)) refl mi lo st g i = refl , con-owed Rt i
  run-con {k = cs cl sl sa bd as nothing cx ea sr sc} {o} {b} (inj₂ (inj₂ refl)) _ mi lo st g i
    with own-cls (cs cl sl sa bd as nothing cx ea sr sc) {o} {b} mi
  ... | oo ()

  ----------------------------------------------------------------------
  -- Mark runs, assembled: the search, then the node's run.

  module _ {Γ′ A′} {c : Ctx R Γ′ A′} {s : St Γ′ A′} {p : Pos} {o : PureObs [] R} {rs} (pth : Path (load o) rs ⟨ c , s , absorbed , p ⟩) where

    focus : ∀ {Γ A} {c′ : Ctx R Γ A} {s′ m κ} → search top (plug c s) ≡ just (found (Γ , A , c′ , s′) m κ)
          → ∀ {Cr C} → Inv Rt Cr C ⟨ c , s , absorbed , p ⟩ → Σ Cur λ C′ → Inv Rt Cr C′ ⟨ c′ , s′ , absorbed , p ⟩
    focus fd i = search-quiet i (found-clear pth fd) fd

    least : ∀ {Γ A} {c′ : Ctx R Γ A} {s′ m κ q} → search top (plug c s) ≡ just (found (Γ , A , c′ , s′) m κ) → Delivers s′ m q
          → ∀ {Cr C} → Inv Rt Cr C ⟨ c , s , absorbed , p ⟩ → Next Cr c′ s′ p q
    least fd dl i = search-least i (found-clear pth fd) fd dl

    abs-of : ∀ {Γ A} {c′ : Ctx R Γ A} {i q} {xs : List A} {κ k′ sh t}
           → search top (plug c s) ≡ just (found (Γ , A , c′ , ofS i q xs) ofM κ) → run c′ (ofS i q xs) ofM p ≡ moved k′ sh t
           → SimC Rt ⟨ c , s , absorbed , p ⟩ sh k′
    abs-of {c′ = c′} {xs = xs} fd eq with closed c′ in cl | xs | eq
    ... | true  | []     | refl = refocused (focus fd) (closed-keep cl (λ ()) (rest-of tt tt₁))
    ... | true  | _ ∷ _  | refl = refocused (focus fd) (closed-keep cl (λ ()) (rest-of tt tt₁))
    ... | false | []     | refl = λ i → stepped cl (least fd d-ofx i) (run-of-end cl) (rest-of tt tt₁)
    ... | false | _ ∷ _  | refl = λ i → stepped cl (least fd d-of i) (run-of-nx cl) (rest-of tt tt₁)

    abs-att : ∀ {Γ A} {c′ : Ctx R Γ A} {l q s₀ κ k′ sh t}
            → search top (plug c s) ≡ just (found (Γ , A , c′ , cutS l (attAt q) s₀) attM κ) → run c′ (cutS l (attAt q) s₀) attM p ≡ moved k′ sh t
            → SimC Rt ⟨ c , s , absorbed , p ⟩ sh k′
    abs-att {l = true}              fd refl = refocused (focus fd) (run-att Rt refl)
    abs-att {l = false} {s₀ = s₀}   fd eq with unsub s₀ in us | eq
    ... | s′ , _ | refl = refocused (focus fd) (run-att Rt (cong proj₁ (sym us)))

    abs-con : ∀ {Γ A X} {c′ : Ctx R Γ A} {k} {o : St Γ X} {b m κ k′ sh t} → m ≡ bodyM ⊎ (m ≡ srcAttM ⊎ m ≡ owedM)
            → search top (plug c s) ≡ just (found (Γ , A , c′ , connS k o b) m κ) → run c′ (connS k o b) m p ≡ moved k′ sh t
            → SimC Rt ⟨ c , s , absorbed , p ⟩ sh k′
    abs-con w fd eq i with focus fd i | found-lo c s fd | found-con pth fd
    ... | _ , i′ | mi , lo | st , g with run-con w eq mi lo st g i′
    ...   | refl , nx′ = nx′

    abs-join : ∀ {Γ A} {c′ : Ctx R Γ A} {j g} {x : A ∈ Γ} {q e ib κ k′ sh t}
             → search top (plug c s) ≡ just (found (Γ , A , c′ , joinS j g x ((q , e) ∷ ib)) joinM κ)
             → run c′ (joinS j g x ((q , e) ∷ ib)) joinM p ≡ moved k′ sh t
             → SimC Rt ⟨ c , s , absorbed , p ⟩ sh k′
    abs-join {c′ = c′} {g = true} {e = nx a} fd eq with closed c′ in cl | eq
    ... | false | refl = λ i → stepped cl (least fd d-join i) (run-join-nx cl) (rest-join tt tt₁)
    ... | true  | refl = refocused (focus fd) (closed-keep cl (λ ()) (rest-join tt tt₁))
    abs-join {c′ = c′} {g = true} {e = cp}   fd eq with closed c′ in cl | eq
    ... | false | refl = λ i → stepped cl (least fd d-join i) (run-join-cp cl) (rest-join tt tt₁)
    ... | true  | refl = refocused (focus fd) (closed-keep cl (λ ()) (rest-join tt tt₁))
    abs-join {g = false} {e = nx a} fd refl   = refocused (focus fd) join-off
    abs-join {g = false} {e = cp}   fd refl   = refocused (focus fd) join-off

    abs-stop : ∀ {Γ A} {c′ : Ctx R Γ A} {j} {w : A → Bool} {r s₀ κ k′ sh t}
             → search top (plug c s) ≡ just (found (Γ , A , c′ , takeS j w (cpAt r) s₀) cpM κ)
             → run c′ (takeS j w (cpAt r) s₀) cpM p ≡ moved k′ sh t
             → SimC Rt ⟨ c , s , absorbed , p ⟩ sh k′
    abs-stop {c′ = c′} fd eq with closed c′ in cl | eq
    ... | false | refl = λ i → stepped cl (least fd d-stop i) (run-stop Rt cl) rest-take
    ... | true  | refl = refocused (focus fd) (closed-keep cl (λ ()) rest-take)

    -- A COLD'S TURN: its tape played one step, a value or its end rising,
    -- a stall or a frame's close moving nothing owed.
    abs-leaf : ∀ {Γ A} {c′ : Ctx R Γ A} {b} {l : Tape A} {κ t k′}
             → search top (plug c s) ≡ just (found (Γ , A , c′ , coldS b l) leafM κ)
             → Driver.took R (run c′ (coldS b l) leafM p) ≡ Driver.silent t k′
             → SimC Rt ⟨ c , s , absorbed , p ⟩ [] k′
    abs-leaf {b = false} fd refl = refocused (focus fd) coldx-off
    abs-leaf {c′ = c′} {b = true} {ending e} fd eq with closed c′ in cl | eq
    ... | true  | refl = refocused (focus fd) (closed-keep cl (λ ()) rest-cold)
    ... | false | refl = λ i → stepped cl (least fd d-ending i) (run-cold-cp cl) rest-cold
    abs-leaf {c′ = c′} {b = true} {over} fd eq with closed c′ in cl | eq
    ... | true  | refl = refocused (focus fd) (λ i → i)
    ... | false | refl = refocused (focus fd) (λ i → i)
    abs-leaf {c′ = c′} {b = true} {play τ u i t (emit a k)} fd eq with closed c′ in cl | eq
    ... | true  | refl = refocused (focus fd) (closed-keep cl (λ ()) rest-cold)
    ... | false | refl = λ iv → stepped cl (least fd d-play iv) (run-cold-nx cl) rest-cold
    abs-leaf {c′ = c′} {b = true} {play τ u i t (stall k)} fd eq with closed c′ in cl | eq
    ... | true  | refl = refocused (focus fd) (closed-keep cl (λ ()) rest-cold)
    ... | false | refl = refocused (focus fd) (cold-skip (u ▸ ix i) (λ tk → tk) stall-into stall-back)
    abs-leaf {c′ = c′} {b = true} {play τ u i t (close k)} fd eq with closed c′ in cl | eq
    ... | true  | refl = refocused (focus fd) (closed-keep cl (λ ()) rest-cold)
    ... | false | refl = refocused (focus fd) (cold-skip (u ▸ ix i) (λ (ru , le) → rest-ticked τ u ru le (From∞.force k)) close-into close-back)

    abs-cut : ∀ {Γ A} {c′ : Ctx R Γ A} {j} {w : A → Bool} {r s₀ κ k′ sh t}
            → search top (plug c s) ≡ just (found (Γ , A , c′ , takeS j w (cutAt r) s₀) cutM κ)
            → run c′ (takeS j w (cutAt r) s₀) cutM p ≡ moved k′ sh t
            → SimC Rt ⟨ c , s , absorbed , p ⟩ sh k′
    abs-cut {c′ = c′} {j = j} {w = w} {r = r} {s₀ = s₀} fd eq with cut s₀ in ct | eq
    ... | s′ , _ | refl = refocused (focus fd)
      (λ {Cr} {C} i → subst (λ x → Inv Rt Cr C ⟨ c′ , takeS j w (overAt r) x , absorbed , r ⟩) (cong proj₁ ct) (run-cut Rt i))

  ----------------------------------------------------------------------
  -- Where a step goes: on, linked a step at a time, engine or driver.

  data Reach (k : Conf R) : Set₁ where
    within : Mv (stepᴹ k) → (∀ {k′ sh t} → stepᴹ k ≡ moved k′ sh t → SimC Rt k sh k′) → Reach k
    driven : Hush (Driver.step R k) → (∀ {t k′} → Driver.step R k ≡ Driver.silent t k′ → SimC Rt k [] k′) → Reach k
    stills : stepᴹ k ≡ quiet → (∀ {Cr C} → Inv Rt Cr C k → Spent Cr Rt) → Reach k

  -- A step linked, read off the step itself, so a search's outcome can be
  -- abstracted in it.
  data Link (k : Conf R) : Stepped R → Set₁ where
    mvL    : ∀ {x} → Mv x → (∀ {k′ sh t} → x ≡ moved k′ sh t → SimC Rt k sh k′) → Link k x
    hushL  : ∀ {x} → Hush (Driver.took R x) → (∀ {t k′} → Driver.took R x ≡ Driver.silent t k′ → SimC Rt k [] k′) → Link k x
    stillL : (∀ {Cr C} → Inv Rt Cr C k → Spent Cr Rt) → Link k quiet

  linked : ∀ {k : Conf R} → Link k (stepᴹ k) → Reach k
  linked {k = k} = go refl
    where
      go : ∀ {x} → stepᴹ k ≡ x → Link k x → Reach k
      go eq   (stillL v)    = stills eq v
      go refl (mvL mv sim)  = within mv sim
      go refl (hushL h sim) = driven h sim

  -- A mark run, by what the search found.
  abs-link : ∀ {Γ A} (c : Ctx R Γ A) s p {o rs} → Path (load o) rs ⟨ c , s , absorbed , p ⟩ → Link ⟨ c , s , absorbed , p ⟩ (stepᴹ ⟨ c , s , absorbed , p ⟩)
  abs-link c s p pth with search top (plug c s) in fd
  ... | nothing = stillL λ i → search-none i fd
  ... | just (found (_ , _ , c′ , s′) m κ) with found-mark c s fd
  ...   | ofK j q xs         = mvL (run-of-mv c′ j q xs p) (abs-of pth fd)
  ...   | attK l q s₀        = mvL (run-att-mv c′ l q s₀ p) (abs-att pth fd)
  ...   | conK k o b m w     = mvL (run-con-mv c′ k o b m p w) (abs-con pth w fd)
  ...   | joinK j g x q e ib = mvL (run-join-mv c′ j g x q e ib p) (abs-join pth fd)
  ...   | stopK j q r s₀     = mvL tt (abs-stop pth fd)
  ...   | cutK j q r s₀      = mvL (run-cut-mv c′ j q r s₀ p) (abs-cut pth fd)
  ...   | leafK b l          = hushL (played-hush b l (closed c′) (λ e l′ b′ p′ → ⟨ c′ , coldS b′ l′ , (if not (closed c′) then rising e else absorbed) , p′ ⟩)
                                                      (λ l′ → ⟨ c′ , coldS b l′ , absorbed , p ⟩))
                                     (abs-leaf pth fd)

  -- The record update holds `srcLive` too, so the test is generalised alone.
  body-cp : ∀ {Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} {s p k′ sh t} b → CS.srcLive k ≡ b
          → moved (if b then ⟨ c , connS (record k { owedAt = just p }) o s , rising cp , p ⟩ else ⟨ c , connS k o s , absorbed , p ⟩) [] [] ≡ moved k′ sh t
          → SimC Rt ⟨ inBody k o c , s , rising cp , p ⟩ sh k′
  body-cp true  lv refl = rise-body-cp Rt lv
  body-cp false lv refl = rise-bodyx Rt lv

  -- A rise, by its frame.
  rise-sim : ∀ {Γ A} {k′ : Conf R} {sh t} (c : Ctx R Γ A) (s : St Γ A) e p → Lo (plug c s) (after p) → rise c s e p ≡ moved k′ sh t
           → SimC Rt ⟨ c , s , rising e , p ⟩ sh k′
  rise-sim top                       s e      p fl refl = rise-top Rt
  rise-sim (inMap f c)               s e      p fl refl = rise-map Rt
  rise-sim (inScan f z c)            s (nx a) p fl refl = rise-scan-nx Rt
  rise-sim (inScan f z c)            s cp     p fl refl = rise-scan-cp Rt
  rise-sim (inCut true a c)          s e      p fl refl = rise-cut Rt
  rise-sim (inCut false a c)         s e      p fl refl = rise-cutx Rt
  rise-sim (inLn b c)                s e      p fl refl = rise-ln Rt
  rise-sim (inTake i w free c)       s (nx a) p fl eq with w a in wa | i | eq
  ... | true  | _     | refl = rise-take-pass Rt wa
  ... | false | true  | refl = rise-take-failᵢ wa fl
  ... | false | false | refl = rise-take-fail Rt wa
  rise-sim (inTake i w free c)       s cp     p fl refl = rise-take-cp Rt
  rise-sim (inTake i w (cpAt r) c)   s e      p fl refl = rise-took Rt (λ ())
  rise-sim (inTake i w (cutAt r) c)  s e      p fl refl = rise-took Rt (λ ())
  rise-sim (inTake i w (overAt r) c) s e      p fl refl = rise-took Rt (λ ())
  rise-sim (inOuter op f ω d n q ls c) o (nx a) p fl eq   = rise-outer-nx Rt eq
  rise-sim (inOuter op f ω d n q ls c) o cp     p fl eq   = rise-outer-cp Rt eq
  rise-sim (inLanes op f ω d n q o pre post c) s (nx b) p fl eq = rise-lane-nx Rt eq
  rise-sim (inLanes op f ω d n q o pre post c) s cp     p fl eq = rise-lane-cp Rt eq
  rise-sim (inSrc k b c)             s (nx a) p fl eq   = rise-src-nx Rt eq
  rise-sim (inSrc k b c)             s cp     p fl eq   = rise-src-cp Rt eq
  rise-sim (inBody k o c)            s (nx b) p fl eq with CS.srcLive k in lv | eq
  ... | true  | refl = rise-body-nx Rt lv
  ... | false | refl = rise-bodyx Rt lv
  rise-sim (inBody k o c)            s cp     p fl eq   = body-cp (CS.srcLive k) refl eq

  -- A joiner subscribed, by its subject's end.
  join-mv : ∀ {Γ A} (c : Ctx R Γ A) (x : A ∈ Γ) q {p} → Mv (stepᴹ ⟨ c , pend (connected x) q , subscribing , p ⟩)
  join-mv c x q with closedUp c x
  ... | true  = tt
  ... | false = tt

  join-sim : ∀ {Γ A} {k′ : Conf R} {sh t} (c : Ctx R Γ A) (x : A ∈ Γ) q p → (closedUp c x ≡ true → endUp c x ≼ q)
           → stepᴹ ⟨ c , pend (connected x) q , subscribing , p ⟩ ≡ moved k′ sh t → SimC Rt ⟨ c , pend (connected x) q , subscribing , p ⟩ sh k′
  join-sim c x q p eb eq with closedUp c x in cu | eq
  ... | true  | refl = keeps Rt (sub-joined cu (eb refl))
  ... | false | refl = keeps Rt (sub-join cu)

  reach-pend : ∀ {Γ A} (c : Ctx R Γ A) (o : Obs Timeline Γ A) q p → Lo (plug c (pend o q)) (at (q ⊕ [ ix 0 ]))
             → (∀ {X} (x : X ∈ Γ) → closedUp c x ≡ true → endUp c x ≼ q) → Reach ⟨ c , pend o q , subscribing , p ⟩
  reach-pend c empty             q p _   _  = within tt λ { refl → keeps Rt sub-empty }
  reach-pend c (of xs)           q p _   _  = within tt λ { refl → keeps Rt sub-of }
  reach-pend c (map f s)         q p _   _  = within tt λ { refl → keeps Rt sub-map }
  reach-pend c (flatMap op f s)  q p _   _  = within tt λ { refl → keeps Rt sub-flat }
  reach-pend c (connected x)     q p _  eb = within (join-mv c x q {p}) (join-sim c x q p (eb x))
  reach-pend c (cold x)          q p _   _  = driven tt λ { refl → keeps Rt sub-cold }
  reach-pend c (scan f z s)      q p _   _  = within tt λ { refl → keeps Rt sub-scan }
  reach-pend c (takeWhile b w s) q p _   _  = within tt λ { refl → keeps Rt sub-take }
  reach-pend c (connect s b)     q p lo  _  = within tt λ { refl → sub-conn lo }
  reach-pend c (defer l)         q p _   _  = within tt λ { refl → keeps Rt sub-defer }

  -- Subscribing to a node already running: nothing to do.  A mark run
  -- reads the run's path.
  reach : ∀ {o₀ : PureObs [] R} {rs} (k : Conf R) → Path (load o₀) rs k → Reach k
  reach {o₀ = o₀} ⟨ c , s , rising e , p ⟩              pth = within (rise-mv c s e p) (rise-sim c s e p (floor o₀ pth tt))
  reach {o₀ = o₀} ⟨ c , pend o q , subscribing , p ⟩ pth with pend-focus o₀ pth
  ... | _ , refl = reach-pend c o q q (lo-weaken (at (q ⊕ [ ix 0 ])) (after q) (floor o₀ pth tt) (at-after q [ ix 0 ])) (ends-behind o₀ pth)
  reach ⟨ c , coldS b l , subscribing , p ⟩             _   = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , ofS j q xs , subscribing , p ⟩            _   = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , doneS , subscribing , p ⟩                 _   = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , mapS f s , subscribing , p ⟩              _   = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , scanS f z s , subscribing , p ⟩           _   = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , cutS l a s , subscribing , p ⟩            _   = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , lnS b s , subscribing , p ⟩               _   = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , takeS j q w s , subscribing , p ⟩         _   = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , flatS op f ω d n q o ls , subscribing , p ⟩ _ = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , connS k o b , subscribing , p ⟩           _   = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , joinS j g x ib , subscribing , p ⟩        _   = within tt λ { refl → keeps Rt λ i → i }
  reach ⟨ c , s , absorbed , p ⟩                        pth = linked (abs-link c s p pth)
