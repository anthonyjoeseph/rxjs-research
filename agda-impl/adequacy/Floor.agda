{-# OPTIONS --guardedness #-}

-- THE CLOCK NEVER RUNS BACK: a silent step's clock is no earlier than the
-- one it starts from.  Mid-run the clock is where the run is, and no mark
-- is keyed before that position's whole subtree is past; once everything
-- is absorbed it is the least mark due.  A step either moves the run to
-- where it was or below, or absorbs it, keeping every mark it had but
-- those it spends, and owing new ones only at or past its clock.
module adequacy.Floor where

open import Data.Bool using (true; false; not; if_then_else_; _∧_; _∨_)
open import Data.List using (List; []; _∷_; [_]; _++_; _ʳ++_; null)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (suc; pred; _<ᵇ_; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Events using (Pos; ix; last; _≟ˡ_; <ᵖ-below; <ᵖ-part; <ᵖ-ix; <ᵖ-irrefl; <ᵖ-asym; <ᵖ-split; <ᵖ-next; From∞; Frame; Frame∞; emit; stall; close; timelineAt)
  renaming (sub to subᴾ)
open import operation.PureObservable using (PureObs; module Machine; module Driver; Tape; play; ending; rest; due; opening) renaming (over to overT)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open Machine using (Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    CS; cs; Mode; Conf; ⟨_,_,_,_⟩; plug; load; subscribing; absorbed; rising; nx; cp; closed; closedUp; alive; unsub; cut; killAll; ended; settle; shutAt;
                    attAt; attached; free; cpAt; cutAt; overAt; search; found; own; run; unsubIf; feed; feedL; queued; inbox; Mark; ofM; attM; cpM; cutM; bodyM; srcAttM; owedM; joinM; leafM; Ev)
open import operation.Key using (at; after; _<ᴷ_; at-<ᴷ)
open import adequacy.Least using (KeyIn; k-own; k-kid; k-cut; k-take; k-src; k-body; Lo)
open import adequacy.Dispatch using (Marked; ofK; attK; conK; joinK; leafK; stopK; cutK; found-mark; found-least; found-plug)
open import adequacy.Stamped using (frame-ahead; opening-ahead; pend-focus; inbox-asc)
open import adequacy.Weight using (Clock)
open import adequacy.Path using (_⊑_; ⊑i; ⊑-trans; Path; _⇜_)

open import adequacy.Apart.Floor using (floor)
open import adequacy.Floor.Keys using (Fewer; Into; asym; at-after; at-after₀; cold-key; cut-in; ended-in; ext-le; ext-⊑; feed-key; fewer-same; flat-in; kill-in; lanes-in; lo-weaken; own-fewer; plug-in; same-l; shut-fewer; sub-at; top-max; unsubIf-in; ⊑-refl)

-- Once absorbed, the clock is no earlier than a bound on every key.
clock-abs : ∀ {R Γ A} (c : Ctx R Γ A) s r {X} → Lo (plug c s) X → X ⊑ Clock ⟨ c , s , absorbed , r ⟩
clock-abs c s r {X} lo with search top (plug c s) in fd
... | nothing = ⊑i (top-max X)
... | just (found (_ , _ , c′ , s′) m κ) =
  ⊑i (lo (subst (λ t → KeyIn t κ) (found-plug c s fd) (plug-in c′ (k-own (proj₁ (found-least {t = plug c s} fd))))))

-- Where the run is, in any mode, its keys none before it.
here-ok : ∀ {R Γ A} (md : Mode A) (c : Ctx R Γ A) s r → Lo (plug c s) (at r) → at r ⊑ Clock ⟨ c , s , md , r ⟩
here-ok absorbed    c s r lo = clock-abs c s r lo
here-ok subscribing c s r lo = ⊑-refl
here-ok (rising e)  c s r lo = ⊑-refl

------------------------------------------------------------------------
-- A step, by mode

-- Absorbed over new keys none before `X`, at any position.
absorb : ∀ {R Γ A} (c : Ctx R Γ A) (t t′ : St Γ A) r {X} → Into X t t′ → Lo (plug c t) X → X ⊑ Clock ⟨ c , t′ , absorbed , r ⟩
absorb c t t′ r {X} h lo = clock-abs c t′ r {X} (sub-at c {t} {t′} {X} h lo)

-- At `r`, in any mode, over new keys none before it.
md-at : ∀ {R Γ A} (md : Mode A) (c : Ctx R Γ A) (t t′ : St Γ A) r → Into (at r) t t′ → Lo (plug c t) (at r) → at r ⊑ Clock ⟨ c , t′ , md , r ⟩
md-at md c t t′ r h lo = here-ok md c t′ r (sub-at c {t} {t′} {at r} h lo)

-- An of's marks lie below where it was subscribed.
of-key : ∀ {Γ A} i p (xs : List A) {κ} → KeyIn {Γ} (ofS i p xs) κ → κ <ᴷ at p ≡ false
of-key i p []       (k-own (here refl)) = ext-le p [ last ]
of-key i p []       (k-own (there ()))
of-key i p (x ∷ xs) (k-own (here refl)) = ext-le p [ ix i ]
of-key i p (x ∷ xs) (k-own (there ()))
of-key i p xs       (k-kid ())

-- A source's feed: every new key past the row a level down.
fed-lo : ∀ {R Γ X B} (c : Ctx R Γ B) (k k′ : CS Γ X) (s : St Γ X) (b : St (X ∷ Γ) B) q (e : Ev X) → Fewer k′ k
       → Lo (plug c (connS k s b)) (after q) → Lo (plug c (connS k′ s (feed (here refl) q e b))) (at (q ++ [ ix 0 ]))
fed-lo c k k′ s b q e fw fl = sub-at c {connS k s b} {connS k′ s (feed (here refl) q e b)} {at (q ++ [ ix 0 ])} into (lo-weaken (at (q ++ [ ix 0 ])) (after q) fl (at-after q [ ix 0 ]))
  where
    into : Into (at (q ++ [ ix 0 ])) (connS k s b) (connS k′ s (feed (here refl) q e b))
    into (k-own m) = inj₁ (k-own (own-fewer k k′ {s} {s} {b} {feed (here refl) q e b} fw m))
    into (k-kid (k-src h)) = inj₁ (k-kid (k-src h))
    into {κ} (k-kid (k-body h)) with feed-key (here refl) q e b h
    ... | inj₁ h′ = inj₁ (k-kid (k-body h′))
    ... | inj₂ lt = inj₂ (asym (at (q ++ [ ix 0 ])) κ lt)

-- A takeWhile's failing value: its end owed below where it fell.
take-owe : ∀ {Γ A} {i f} (s : St Γ A) q → Into (at q) (takeS i f free s) (takeS i f (cpAt q) s)
take-owe s q (k-own (here refl)) = inj₂ (ext-le q [ last ])
take-owe s q (k-own (there ()))
take-owe s q (k-kid (k-take h)) = inj₁ (k-kid (k-take h))

module _ {R : Set} where
  -- A RISE: on where it was, a level down, or absorbed keeping its keys,
  -- a feed's or a failed take's only past it.
  rises : ∀ {Γ A} (c : Ctx R Γ A) s ε q {τ k′} → Lo (plug c s) (after q)
        → Driver.step R ⟨ c , s , rising ε , q ⟩ ≡ Driver.silent τ k′ → at q ⊑ Clock k′
  rises top s (nx a) q fl ()
  rises top s cp     q fl ()
  rises (inMap f c) s ε q fl refl = ⊑-refl
  rises (inScan f z c) s (nx a) q fl refl = ⊑-refl
  rises (inScan f z c) s cp     q fl refl = ⊑-refl
  rises (inCut l a c) s ε q fl refl = here-ok (if l then rising ε else absorbed) c (cutS l a s) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inLn b c) s ε q fl refl = ⊑-refl
  rises (inTake i f free c) s (nx a) q fl eq with f a | i
  rises (inTake i f free c) s (nx a) q fl refl | true  | _     = ⊑-refl
  rises (inTake i f free c) s (nx a) q fl refl | false | true  = ext-⊑ q [ ix 0 ]
  rises (inTake i f free c) s (nx a) q fl refl | false | false =
    absorb c (takeS false f free s) (takeS false f (cpAt q) s) q (take-owe {i = false} {f} s q) (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inTake i f free c) s cp q fl refl = ⊑-refl
  rises (inTake i f (cpAt r) c)  s ε q fl refl = clock-abs c (takeS i f (cpAt r) s) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inTake i f (cutAt r) c) s ε q fl refl = clock-abs c (takeS i f (cutAt r) s) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inTake i f (overAt r) c) s ε q fl refl = clock-abs c (takeS i f (overAt r) s) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inOuter (mergeᶠ nothing) f ω d n qs ls c) s (nx a) q fl eq with closed c
  rises (inOuter (mergeᶠ nothing) f ω d n qs ls c) s (nx a) q fl refl | true  =
    clock-abs c (flatS (mergeᶠ nothing) f ω d n qs s ls) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inOuter (mergeᶠ nothing) f ω d n qs ls c) s (nx a) q fl refl | false = ext-⊑ q [ ix 1 ]
  rises (inOuter (mergeᶠ (just mx)) f ω d n qs ls c) s (nx a) q fl eq with n <ᵇ mx
  rises (inOuter (mergeᶠ (just mx)) f ω d n qs ls c) s (nx a) q fl refl | false =
    absorb c (flatS (mergeᶠ (just mx)) f ω d n qs s ls) (flatS (mergeᶠ (just mx)) f ω d n (qs ++ [ a ]) s ls) q
           (λ ki → inj₁ (flat-in (λ h → h) same-l ki)) (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inOuter (mergeᶠ (just mx)) f ω d n qs ls c) s (nx a) q fl eq | true with closed c
  rises (inOuter (mergeᶠ (just mx)) f ω d n qs ls c) s (nx a) q fl refl | true | true  =
    clock-abs c (flatS (mergeᶠ (just mx)) f ω d n qs s ls) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inOuter (mergeᶠ (just mx)) f ω d n qs ls c) s (nx a) q fl refl | true | false = ext-⊑ q [ ix 1 ]
  rises (inOuter switchᶠ f ω d n qs ls c) s (nx a) q fl eq with killAll ls | (λ {x} {κ} → kill-in ls {x} {κ})
  rises (inOuter switchᶠ f ω d n qs ls c) s (nx a) q fl eq | ls′ , t | kl with closed c
  rises (inOuter switchᶠ f ω d n qs ls c) s (nx a) q fl refl | ls′ , t | kl | true  =
    absorb c (flatS switchᶠ f ω d n qs s ls) (flatS switchᶠ f ω d 0 qs s ls′) q (λ ki → inj₁ (flat-in (λ h → h) kl ki)) (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inOuter switchᶠ f ω d n qs ls c) s (nx a) q fl refl | ls′ , t | kl | false = ext-⊑ q [ ix 1 ]
  rises (inOuter exhaustᶠ f ω d n qs ls c) s (nx a) q fl eq with n ≡ᵇ 0
  rises (inOuter exhaustᶠ f ω d n qs ls c) s (nx a) q fl refl | false =
    clock-abs c (flatS exhaustᶠ f ω d n qs s ls) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inOuter exhaustᶠ f ω d n qs ls c) s (nx a) q fl eq | true with closed c
  rises (inOuter exhaustᶠ f ω d n qs ls c) s (nx a) q fl refl | true | true  =
    clock-abs c (flatS exhaustᶠ f ω d n qs s ls) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inOuter exhaustᶠ f ω d n qs ls c) s (nx a) q fl refl | true | false = ext-⊑ q [ ix 1 ]
  rises (inOuter op f ω d n qs ls c) s cp q fl refl =
    md-at (if d then absorbed else settle true n (null qs)) c (flatS op f ω d n qs s ls) (flatS op f ω true n qs s ls) q
          (λ ki → inj₁ (flat-in (λ h → h) same-l ki)) (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inLanes op f ω d n qs o′ pre post c) s (nx b) q fl eq with alive s
  rises (inLanes op f ω d n qs o′ pre post c) s (nx b) q fl refl | true  = ⊑-refl
  rises (inLanes op f ω d n qs o′ pre post c) s (nx b) q fl refl | false =
    clock-abs c (flatS op f ω d n qs o′ (pre ʳ++ s ∷ post)) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inLanes op f ω d n qs o′ pre post c) s cp q fl eq with alive s
  rises (inLanes op f ω d n qs o′ pre post c) s cp q fl refl | false =
    clock-abs c (flatS op f ω d n qs o′ (pre ʳ++ s ∷ post)) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inLanes op f ω d n [] o′ pre post c) s cp q fl refl | true =
    md-at (settle d (pred n) true) c (flatS op f ω d n [] o′ (pre ʳ++ s ∷ post)) (flatS op f ω d (pred n) [] o′ (pre ʳ++ ended s ∷ post)) q
          (λ ki → inj₁ (flat-in (λ h → h) (lanes-in pre post (ended-in s)) ki)) (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inLanes op f ω d n (a ∷ qs) o′ pre post c) s cp q fl eq | true with closed c
  rises (inLanes op f ω d n (a ∷ qs) o′ pre post c) s cp q fl refl | true | true  =
    absorb c (flatS op f ω d n (a ∷ qs) o′ (pre ʳ++ s ∷ post)) (flatS op f ω d (pred n) qs o′ (pre ʳ++ ended s ∷ post)) q
           (λ ki → inj₁ (flat-in (λ h → h) (lanes-in pre post (ended-in s)) ki)) (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inLanes op f ω d n (a ∷ qs) o′ pre post c) s cp q fl refl | true | false = ext-⊑ q [ ix 1 ]
  rises (inSrc k b c) s (nx a) q fl refl =
    ⊑-trans (ext-⊑ q [ ix 0 ]) (clock-abs c (connS k s (feed (here refl) q (nx a) b)) q {at (q ++ [ ix 0 ])} (fed-lo c k k s b q (nx a) (fewer-same {k = k}) fl))
  rises (inSrc k b c) s cp q fl refl =
    ⊑-trans (ext-⊑ q [ ix 0 ]) (clock-abs c (connS (shutAt q k) s (feed (here refl) q cp b)) q {at (q ++ [ ix 0 ])} (fed-lo c k (shutAt q k) s b q cp (shut-fewer q k) fl))
  rises (inBody k o′ c) s (nx b) q fl eq with CS.srcLive k
  rises (inBody k o′ c) s (nx b) q fl refl | true  = ⊑-refl
  rises (inBody k o′ c) s (nx b) q fl refl | false = clock-abs c (connS k o′ s) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inBody k o′ c) s cp q fl eq with CS.srcLive k
  rises (inBody k o′ c) s cp q fl refl | true  = ⊑-refl
  rises (inBody k o′ c) s cp q fl refl | false = clock-abs c (connS k o′ s) q (lo-weaken (at q) (after q) fl (at-after₀ q))

  -- A SUBSCRIBE: on where it was or a level down, or absorbed over marks
  -- owed below where it was made.
  begins : ∀ (o : PureObs [] R) {rs Γ A} (c : Ctx R Γ A) (o′ : PureObs Γ A) q {τ k′}
         → Path (load o) rs ⟨ c , pend o′ q , subscribing , q ⟩ → Lo (plug c (pend o′ q)) (at q)
         → Driver.step R ⟨ c , pend o′ q , subscribing , q ⟩ ≡ Driver.silent τ k′ → at q ⊑ Clock k′
  begins o c (map f s′)         q pth lo refl = ⊑-refl
  begins o c (scan f z s′)      q pth lo refl = ⊑-refl
  begins o c (takeWhile i f s′) q pth lo refl = ⊑-refl
  begins o c (flatMap op f s′)  q pth lo refl = ⊑-refl
  begins o c (connect s′ b)     q pth lo refl = ext-⊑ q [ ix 0 ]
  begins o c (defer l)          q pth lo refl = ext-⊑ q [ ix 1 ]
  begins o c (cold x)           q pth lo refl =
    absorb c (pend (cold x) q) (coldS true (opening q (timelineAt x q))) q (λ {κ} h → inj₂ (asym (at q) κ (opening-ahead o pth (cold-key h)))) lo
  begins o c empty              q pth lo refl = absorb c (pend empty q) (ofS 0 q []) q (λ h → inj₂ (of-key 0 q [] h)) lo
  begins o c (of xs)            q pth lo refl = absorb c (pend (of xs) q) (ofS 0 q xs) q (λ h → inj₂ (of-key 0 q xs h)) lo
  begins o c (connected x)      q pth lo eq with closedUp c x
  begins o c (connected x)      q pth lo refl | true  = absorb c (pend (connected x) q) (ofS 0 q []) q (λ h → inj₂ (of-key 0 q [] h)) lo
  begins o c (connected x)      q pth lo refl | false = absorb c (pend (connected x) q) (joinS q true x []) q (λ { (k-own ()) ; (k-kid ()) }) lo

  -- A joiner's next entry: none before the one it ran.
  inbox-into : ∀ {Γ A} {t : St Γ A} {j g x} q₀ (ib : List (Pos × Ev A))
             → (∀ {q₁ e₁ ib′} → ib ≡ (q₁ , e₁) ∷ ib′ → at q₁ <ᴷ at q₀ ≡ false) → Into (at q₀) t (joinS j g x ib)
  inbox-into q₀ []              h (k-own ())
  inbox-into q₀ []              h (k-kid ())
  inbox-into q₀ ((q₁ , e₁) ∷ ib) h (k-own (here refl)) = inj₂ (h refl)
  inbox-into q₀ ((q₁ , e₁) ∷ ib) h (k-own (there ()))
  inbox-into q₀ ((q₁ , e₁) ∷ ib) h (k-kid ())

  -- A cold's turn: on at its tick, or absorbed with its next due past it.
  leafs : ∀ {Γ A} (c : Ctx R Γ A) q b (l : Tape A) {κ} → (leafM , κ) ∈ own {Γ} (coldS b l) → Lo (plug c (coldS b l)) κ
        → (∀ {τ u i t f κ′} → l ≡ play τ u i t (close f) → due (rest τ (u ++ [ last ]) (From∞.force f)) ≡ just κ′ → κ <ᴷ κ′ ≡ true)
        → ∀ {τ k′} → Driver.took R (run c (coldS b l) leafM q) ≡ Driver.silent τ k′ → κ ⊑ Clock k′
  leafs c q b     overT              () lo ah eq
  leafs c q false (ending e₀)        (here refl) lo ah refl = absorb c (coldS false (ending e₀)) (coldS false overT) q (λ { (k-own ()) ; (k-kid ()) }) lo
  leafs c q false (play τ u i t fr)  (here refl) lo ah refl = absorb c (coldS false (play τ u i t fr)) (coldS false overT) q (λ { (k-own ()) ; (k-kid ()) }) lo
  leafs c q true  (ending e₀)        (here refl) lo ah refl =
    md-at (if not (closed c) then rising cp else absorbed) c (coldS true (ending e₀)) (coldS false overT) e₀ (λ { (k-own ()) ; (k-kid ()) }) lo
  leafs c q true  (play τ u i t fr)  (here refl) lo ah eq with closed c
  leafs c q true  (play τ u i t fr)  (here refl) lo ah refl | true =
    absorb c (coldS true (play τ u i t fr)) (coldS true overT) q (λ { (k-own ()) ; (k-kid ()) }) lo
  leafs c q true  (play τ u i t (emit a f))  (here refl) lo ah refl | false = ⊑-refl
  leafs c q true  (play τ u i t (stall f)) {κ} (here refl) lo ah refl | false =
    absorb c (coldS true (play τ u i t (stall f))) (coldS true (play τ u (suc i) t (Frame∞.force f))) q
      (λ { (k-own (here refl)) → inj₂ (asym κ (at (u ++ [ ix (suc i) ])) (trans (at-<ᴷ (u ++ [ ix i ]) (u ++ [ ix (suc i) ])) (<ᵖ-part u [] [] (<ᵖ-ix i))))
         ; (k-own (there ())) ; (k-kid ()) }) lo
  leafs c q true  (play τ u i t (close f)) {κ} (here refl) lo ah refl | false =
    absorb c (coldS true (play τ u i t (close f))) (coldS true (rest τ (u ++ [ last ]) (From∞.force f))) q
      (λ {κ′} h → inj₂ (asym κ κ′ (ah refl (cold-key h)))) lo

  -- A connect's admin mark: its body subscribed where it was keyed, or
  -- absorbed keeping fewer keys.
  conns : ∀ {Γ A X} (c : Ctx R Γ A) q (k : CS Γ X) (o′ : St Γ X) b mk → mk ≡ bodyM ⊎ (mk ≡ srcAttM ⊎ mk ≡ owedM)
        → ∀ {κ} → (mk , κ) ∈ own (connS k o′ b) → Lo (plug c (connS k o′ b)) κ
        → ∀ {τ k′} → Driver.took R (run c (connS k o′ b) mk q) ≡ Driver.silent τ k′ → κ ⊑ Clock k′
  conns c q k@(cs cl sl sa (just p₀) as ow ca ea sr sc) o′ b .bodyM (inj₁ refl) mi lo refl = ⊑i (lo (plug-in c (k-own (here refl))))
  conns c q k@(cs cl sl sa nothing as ow ca ea sr sc) o′ b .bodyM (inj₁ refl) mi lo refl = clock-abs c (connS k o′ b) q lo
  conns c q k@(cs cl sl sa ba (just p₀) ow ca ea sr sc) o′ b .srcAttM (inj₂ (inj₁ refl)) {κ} mi lo refl =
    absorb c (connS k o′ b) (connS (cs cl sl true ba nothing ow ca ea sr sc) (proj₁ (unsubIf (not sl ∨ closed c) o′)) b) p₀ into lo
    where
      into : Into κ (connS k o′ b) (connS (cs cl sl true ba nothing ow ca ea sr sc) (proj₁ (unsubIf (not sl ∨ closed c) o′)) b)
      into (k-own m) = inj₁ (k-own (own-fewer k (cs cl sl true ba nothing ow ca ea sr sc) {o′} {proj₁ (unsubIf (not sl ∨ closed c) o′)} {b} {b}
                                       ((λ e → e) , (λ ()) , (λ e → e)) m))
      into (k-kid (k-src h))  = inj₁ (k-kid (k-src (unsubIf-in (not sl ∨ closed c) o′ h)))
      into (k-kid (k-body h)) = inj₁ (k-kid (k-body h))
  conns c q k@(cs cl sl sa ba nothing ow ca ea sr sc) o′ b .srcAttM (inj₂ (inj₁ refl)) mi lo refl = clock-abs c (connS k o′ b) q lo
  conns c q k@(cs cl sl sa ba as (just p₀) ca ea sr sc) o′ b .owedM (inj₂ (inj₂ refl)) {κ} mi lo refl =
    absorb c (connS k o′ b) (connS (cs cl false sa ba as nothing ca ea sr sc) (proj₁ (unsubIf sa o′)) b) p₀ into lo
    where
      into : Into κ (connS k o′ b) (connS (cs cl false sa ba as nothing ca ea sr sc) (proj₁ (unsubIf sa o′)) b)
      into (k-own m) = inj₁ (k-own (own-fewer k (cs cl false sa ba as nothing ca ea sr sc) {o′} {proj₁ (unsubIf sa o′)} {b} {b}
                                       ((λ e → e) , (λ e → e) , (λ ())) m))
      into (k-kid (k-src h))  = inj₁ (k-kid (k-src (unsubIf-in sa o′ h)))
      into (k-kid (k-body h)) = inj₁ (k-kid (k-body h))
  conns c q k@(cs cl sl sa ba as nothing ca ea sr sc) o′ b .owedM (inj₂ (inj₂ refl)) mi lo refl = clock-abs c (connS k o′ b) q lo

  -- A MARK RUN: on at the mark's own key, or absorbed with what it owes
  -- next no earlier.
  runs : ∀ {Γ A} (c : Ctx R Γ A) q {s : St Γ A} {mk κ} → Marked s mk → (mk , κ) ∈ own s → Lo (plug c s) κ
       → (∀ {b τ u i t f κ′} → s ≡ coldS b (play τ u i t (close f)) → mk ≡ leafM → due (rest τ (u ++ [ last ]) (From∞.force f)) ≡ just κ′ → κ <ᴷ κ′ ≡ true)
       → (∀ {j g x q₀ e q₁ e₁ ib} → s ≡ joinS j g x ((q₀ , e) ∷ (q₁ , e₁) ∷ ib) → mk ≡ joinM → at q₁ <ᴷ at q₀ ≡ false)
       → ∀ {τ k′} → Driver.took R (run c s mk q) ≡ Driver.silent τ k′ → κ ⊑ Clock k′
  runs c q (ofK i p₀ []) (here refl) lo ah asc eq with closed c
  runs c q (ofK i p₀ []) (here refl) lo ah asc refl | true  = absorb c (ofS i p₀ []) doneS p₀ (λ { (k-own ()) ; (k-kid ()) }) lo
  runs c q (ofK i p₀ []) (here refl) lo ah asc refl | false = ⊑-refl
  runs c q (ofK i p₀ []) (there ()) lo ah asc eq
  runs c q (ofK i p₀ (x ∷ xs)) (here refl) lo ah asc eq with closed c
  runs c q (ofK i p₀ (x ∷ xs)) (here refl) lo ah asc refl | true  = absorb c (ofS i p₀ (x ∷ xs)) doneS p₀ (λ { (k-own ()) ; (k-kid ()) }) lo
  runs c q (ofK i p₀ (x ∷ xs)) (here refl) lo ah asc refl | false = ⊑-refl
  runs c q (ofK i p₀ (x ∷ xs)) (there ()) lo ah asc eq
  runs c q (attK l p₀ s₀) mi lo ah asc refl =
    absorb c (cutS l (attAt p₀) s₀) (cutS l attached (proj₁ (unsubIf (not l) s₀))) p₀
      (λ { (k-own ()) ; (k-kid (k-cut h)) → inj₁ (k-kid (k-cut (unsubIf-in (not l) s₀ h))) }) lo
  runs c q (conK k o′ b mk w) mi lo ah asc eq = conns c q k o′ b mk w mi lo eq
  runs c q (joinK j g x q₀ (nx a) ib) (here refl) lo ah asc refl =
    md-at (if g ∧ not (closed c) then rising (nx a) else absorbed) c (joinS j g x ((q₀ , nx a) ∷ ib)) (joinS j g x ib) q₀
      (inbox-into q₀ ib (λ { refl → asc refl refl })) lo
  runs c q (joinK j g x q₀ cp ib) (here refl) lo ah asc refl =
    md-at (if g ∧ not (closed c) then rising cp else absorbed) c (joinS j g x ((q₀ , cp) ∷ ib)) (joinS j false x ib) q₀
      (inbox-into q₀ ib (λ { refl → asc refl refl })) lo
  runs c q (joinK j g x q₀ e ib) (there ()) lo ah asc eq
  runs c q (leafK b l) mi lo ah asc eq = leafs c q b l mi lo (λ e → ah (cong (coldS b) e) refl) eq
  runs c q (stopK i f r s₀) (here refl) lo ah asc refl =
    md-at (if not (closed c) then rising cp else absorbed) c (takeS i f (cpAt r) s₀) (takeS i f (cutAt r) s₀) (r ++ [ last ])
      (λ { (k-own (here refl)) → inj₂ (asym (at (r ++ [ last ])) (after r) (at-after r [ last ])) ; (k-own (there ())) ; (k-kid (k-take h)) → inj₁ (k-kid (k-take h)) }) lo
  runs c q (stopK i f r s₀) (there ()) lo ah asc eq
  runs c q (cutK i f r s₀) mi lo ah asc refl =
    absorb c (takeS i f (cutAt r) s₀) (takeS i f (overAt r) (proj₁ (cut s₀))) r
      (λ { (k-own ()) ; (k-kid (k-take h)) → inj₁ (k-kid (k-take (cut-in s₀ h))) }) lo

  absorbs : ∀ (o : PureObs [] R) {rs Γ A} (c : Ctx R Γ A) s q → Path (load o) rs ⟨ c , s , absorbed , q ⟩
          → ∀ {τ k′} → Driver.step R ⟨ c , s , absorbed , q ⟩ ≡ Driver.silent τ k′ → Clock ⟨ c , s , absorbed , q ⟩ ⊑ Clock k′
  absorbs o c s q pth with search top (plug c s) in fd
  ... | nothing = λ ()
  ... | just (found (_ , _ , c′ , s′) mk κ) = λ eq →
    runs c′ q (found-mark c s fd) (proj₁ (found-least {t = plug c s} fd))
      (subst (λ t → Lo t κ) (sym (found-plug c s fd)) (proj₂ (found-least {t = plug c s} fd)))
      (λ { refl refl dr → frame-ahead o pth fd dr })
      (λ { refl refl → inbox-asc o pth fd })
      eq

------------------------------------------------------------------------
-- The clock ahead

-- THE CLOCK NEVER RUNS BACK: a silent step's clock is no earlier.
-- DEAD ROUTE: the least mark due as the clock throughout.  A lane begun
--   by an outer's value makes marks under that value, before the outer's
--   next mark, so mid-run the least key falls.
clock-mono : ∀ {R} (o : PureObs [] R) {rs k k′} → Path (load o) rs k → k′ ⇜ k → Clock k ⊑ Clock k′
clock-mono o {k = ⟨ c , s , rising ε , q ⟩}  pth (_ , eq) = rises c s ε q (floor o pth tt) eq
clock-mono o {k = ⟨ c , s , subscribing , q ⟩} pth (_ , eq) with pend-focus o pth
... | o′ , refl = begins o c o′ q pth (lo-weaken (at q) (after q) (floor o pth tt) (at-after₀ q)) eq
clock-mono o {k = ⟨ c , s , absorbed , q ⟩}  pth (_ , eq) = absorbs o c s q pth eq

-- A SOURCE'S FEED COMES DUE NO SOONER: once a source has risen, every
-- mark is due no earlier than the row a level down.
fed-ahead : ∀ {R} (o : PureObs [] R) {rs Γ X B} {k : CS Γ X} {b : St (X ∷ Γ) B} {c : Ctx R Γ B} {s ε q k′}
          → Path (load o) rs ⟨ inSrc k b c , s , rising ε , q ⟩ → k′ ⇜ ⟨ inSrc k b c , s , rising ε , q ⟩
          → Clock k′ <ᴷ at (q ++ [ ix 0 ]) ≡ false
fed-ahead o {k = k} {b} {c} {s} {nx a} {q} pth (_ , refl) =
  _⊑_.un (clock-abs c (connS k s (feed (here refl) q (nx a) b)) q {at (q ++ [ ix 0 ])} (fed-lo c k k s b q (nx a) (fewer-same {k = k}) (floor o pth tt)))
fed-ahead o {k = k} {b} {c} {s} {cp} {q} pth (_ , refl) =
  _⊑_.un (clock-abs c (connS (shutAt q k) s (feed (here refl) q cp b)) q {at (q ++ [ ix 0 ])} (fed-lo c k (shutAt q k) s b q cp (shut-fewer q k) (floor o pth tt)))
