{-# OPTIONS --guardedness --large-indices #-}

-- THE FOCUS: a firing cold's step, lifted through the subscriptions
-- around it to the meaning's next step.  At each level the cold's step
-- comes first when every sibling's next event comes later (`Clear`): a
-- flatMap's other lanes and its outer, a connect's body beside its
-- source, its source beside its body.  A connect shows its source's
-- step below the source's own position, at `ix 0`.
module Focus where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.All using (All; []; _∷_; head)
open import Data.List.Relation.Unary.All.Properties using (++⁺; ++⁻ʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; Σ; _,_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; lower; suc; zero) renaming (lift to up)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst)

open import denotation.MonotonicList using (Pos; Frame; ix; _<ᵖ_; <ᵖ-asym; <ᵖ-ext)
import denotation.Unfold as U
open import denotation.Unfold using (Srcs)
open import operation.AbstractObservable using (module Run)
open import operation.PureObservable using (Pureᴾ; World; Sink; module Pure)
open import Realize using (module Realizing)

-- A next event, if any, after `q`.
After : Pos → Maybe Pos → Set
After q nothing  = ⊤
After q (just k) = q <ᵖ k ≡ true

Later : ∀ {A} → Pos → U.Node A → Set
Later q n = After q (U.headˢ (U.step n))

Up : Set → Set₁
Up = Lift (suc zero)

Open : ∀ {A} → Pos → Maybe (U.Node A) → Set
Open q nothing  = ⊤
Open q (just n) = Later q n

private
  -- The lane `earliest` finds, with the lanes around it.
  FoundIn : ∀ {B} → List (U.Node B) → U.Earliest B → Set₁
  FoundIn ls U.none                = Up ⊤
  FoundIn ls (U.found k bs l s as) = bs ++ l ∷ as ≡ ls × s ≡ U.step l × U.headˢ s ≡ just k

  pick-in : ∀ {B} (l : U.Node B) ls mk → U.headˢ (U.step l) ≡ mk → (e : U.Earliest B) → FoundIn ls e
          → FoundIn (l ∷ ls) (U.pick l (U.step l) ls mk e)
  pick-in l ls nothing  h U.none                  _            = up tt
  pick-in l ls nothing  h (U.found k bs c sc as)  (e , s , hk) = cong (l ∷_) e , s , hk
  pick-in l ls (just k) h U.none                  _            = refl , refl , h
  pick-in l ls (just k) h (U.found k′ bs c sc as) (e , s , hk) with k <ᵖ k′
  ... | true  = refl , refl , h
  ... | false = cong (l ∷_) e , s , hk

  found-in : ∀ {B} (ls : List (U.Node B)) → FoundIn ls (U.earliest ls)
  found-in []       = up tt
  found-in (l ∷ ls) = pick-in l ls (U.headˢ (U.step l)) refl (U.earliest ls) (found-in ls)

  later-found : ∀ {B L} {ls : List (U.Node B)} {k bs l s as} → All (Later L) ls → FoundIn ls (U.found k bs l s as) → L <ᵖ k ≡ true
  later-found {L = L} {bs = bs} a (refl , refl , hk) = subst (After L) hk (head (++⁻ʳ bs a))

  -- The outer's step first, every lane's next event later.
  go-outer : ∀ {A B} op (g : A → Pos → U.Node B) {n n₁ L} ls qs → U.step n ≡ U.skipˢ L n₁ → All (Later L) ls
           → (e : U.Earliest B) → FoundIn ls e
           → U.goˢ op g (just n) ls qs e ≡ U.skipˢ L (U.flatMapᶜ op g (just n₁) ls qs)
  go-outer op g ls qs sn a U.none _ = cong (λ z → U.outerˢ op g z ls qs) sn
  go-outer op g {n} {n₁} {L} _ qs sn a (U.found k bs l s as) fi@(refl , refl , _) =
    trans (cong (λ z → U.raceˢ op g n z (U.headˢ z) k bs l s as qs) sn)
          (cong (λ z → if z then U.outerˢ op g (U.skipˢ L n₁) (bs ++ l ∷ as) qs else U.laneˢ op g (just n) bs s as qs)
                (later-found a fi))

  -- The focused lane's step first, every other lane's next event later.
  pick-first : ∀ {B} (l : U.Node B) s as L (e : U.Earliest B) → FoundIn as e → All (Later L) as
             → U.pick l s as (just L) e ≡ U.found L [] l s as
  pick-first l s as L U.none                   _  _ = refl
  pick-first l s as L (U.found k′ bs c sc as′) fi a =
    cong (λ z → if z then U.found L [] l s as else U.found k′ (l ∷ bs) c sc as′) (later-found a fi)

  pick-after : ∀ {B} (b : U.Node B) s ls mk {L bs l sl as} → After L mk → U.pick b s ls mk (U.found L bs l sl as) ≡ U.found L (b ∷ bs) l sl as
  pick-after b s ls nothing  _ = refl
  pick-after b s ls (just k) {L} {bs} {l} {sl} {as} h = cong (λ z → if z then U.found k [] b s ls else U.found L (b ∷ bs) l sl as) (<ᵖ-asym L k h)

  earliest-at : ∀ {B} (bs : List (U.Node B)) n as {L n₁} → U.step n ≡ U.skipˢ L n₁ → All (Later L) bs → All (Later L) as
              → U.earliest (bs ++ n ∷ as) ≡ U.found L bs n (U.step n) as
  earliest-at []       n as sn _          a =
    trans (cong (λ z → U.pick n (U.step n) as z (U.earliest as)) (cong U.headˢ sn)) (pick-first n (U.step n) as _ (U.earliest as) (found-in as) a)
  earliest-at (b ∷ bs) n as sn (hb ∷ abs) a =
    trans (cong (U.pick b (U.step b) (bs ++ n ∷ as) (U.headˢ (U.step b))) (earliest-at bs n as sn abs a))
          (pick-after b (U.step b) (bs ++ n ∷ as) (U.headˢ (U.step b)) hb)

  race-lane : ∀ {A B} op (g : A → Pos → U.Node B) o so mk {L bs l s as qs} → After L mk
            → U.raceˢ op g o so mk L bs l s as qs ≡ U.laneˢ op g (just o) bs s as qs
  race-lane op g o so nothing  _ = refl
  race-lane op g o so (just k) {L} {bs} {l} {s} {as} {qs} h =
    cong (λ z → if z then U.outerˢ op g so (bs ++ l ∷ as) qs else U.laneˢ op g (just o) bs s as qs) (<ᵖ-asym L k h)

  go-lane : ∀ {A B} op (g : A → Pos → U.Node B) (o : Maybe (U.Node A)) bs n as qs {L n₁} → U.step n ≡ U.skipˢ L n₁ → Open L o
          → U.goˢ op g o (bs ++ n ∷ as) qs (U.found L bs n (U.step n) as) ≡ U.skipˢ L (U.flatMapᶜ op g o (bs ++ n₁ ∷ as) qs)
  go-lane op g nothing  bs n as qs sn _ = cong (λ z → U.laneˢ op g nothing bs z as qs) sn
  go-lane op g (just o) bs n as qs sn h =
    trans (race-lane op g o (U.step o) (U.headˢ (U.step o)) h) (cong (λ z → U.laneˢ op g (just o) bs z as qs) sn)

  -- A connect's source steps first, its body's next event later.
  before-after : ∀ {B} Q (sb : U.Step B) → After Q (U.headˢ sb) → U.beforeˢ Q sb ≡ true
  before-after Q (U.outˢ k _ _) h = h
  before-after Q (U.skipˢ k _)  h = h
  before-after Q (U.endˢ k)     h = h
  before-after Q U.hushˢ        _ = refl

  ahead-src : ∀ {A B} (b : U.Node B) sb (s : U.Node A) Q s₁ → After Q (U.headˢ sb)
            → U.aheadˢ b sb s Q s₁ (U.beforeˢ Q sb) ≡ U.skipˢ Q (U.connectᶜ b s₁)
  ahead-src b sb s Q s₁ h = cong (U.aheadˢ b sb s Q s₁) (before-after Q sb h)

module Focusing (R : Set) where
  open Run (Pureᴾ R) using (Env; module Kit; module FlatKit)
  open FlatKit using (Flat)
  open Realizing R using (Sub; Lane; lane; Phase; nodeOf; Holding; firing; Spot; SpotLanes; cold-here; in-map; in-scan; in-take; in-outer
                         ; in-lanes; in-source; in-body; in-defer; this-lane; next-lane; spot-of; phaseAt; phaseAtLanes; over; module At)
  open Pure R using (State; get)

  -- Where the cold's step at `q` is shown at the root.
  mutual
    lift : ∀ {h Δ A B} {t : Sub h Δ A} {s : Sink h B} {hd} → Spot t s hd → Pos → Pos
    lift cold-here     q = q
    lift (in-map p)    q = lift p q
    lift (in-scan p)   q = lift p q
    lift (in-take p)   q = lift p q
    lift (in-outer p)  q = lift p q
    lift (in-lanes p)  q = liftLanes p q
    lift (in-source p) q = lift p q ++ [ ix 0 ]
    lift (in-body p)   q = lift p q
    lift (in-defer p)  q = lift p q

    liftLanes : ∀ {h Δ B C} {ls : List (Lane h Δ B)} {s : Sink h C} {hd} → SpotLanes ls s hd → Pos → Pos
    liftLanes (this-lane p) q = lift p q
    liftLanes (next-lane p) q = liftLanes p q

  module On {h : World} (H : All (Pure.Val R h) h) where
    open At H

    -- Every sibling on the way up next steps after the cold's step there.
    mutual
      Clear : ∀ {Δ A B} {t : Sub h Δ A} {s : Sink h B} {hd} → Spot t s hd → Env Δ h → Srcs Δ → Pos → Set₁
      Clear cold-here                                  E ρ q = Up ⊤
      Clear (in-map p)                                 E ρ q = Clear p E ρ q
      Clear (in-scan p)                                E ρ q = Clear p E ρ q
      Clear (in-take p)                                E ρ q = Clear p E ρ q
      Clear (in-outer {ls = ls} p)                     E ρ q = Clear p E ρ q × All (Later (lift p q)) (partLanes ls E ρ)
      Clear (in-lanes {t = so} p)                      E ρ q = ClearLanes p E ρ q × Up (Open (liftLanes p q) (part so E ρ))
      Clear (in-source {S = S} {s₀ = s₀} {u = u} p)    E ρ q =
        Clear p E ρ q × Up (Open (lift p q ++ [ ix 0 ]) (part u (S ∷ E) (s₀ ∷ ρ)))
      Clear (in-body {S = S} {s₀ = s₀} {m = m} p)      E ρ q = Clear p (S ∷ E) (s₀ ∷ ρ) q × Up (Open (lift p q) m)
      Clear (in-defer p)                               E ρ q = Clear p E ρ q

      ClearLanes : ∀ {Δ B C} {ls : List (Lane h Δ B)} {s : Sink h C} {hd} → SpotLanes ls s hd → Env Δ h → Srcs Δ → Pos → Set₁
      ClearLanes (this-lane {ls = ls} p) E ρ q = Clear p E ρ q × All (Later (lift p q)) (partLanes ls E ρ)
      ClearLanes (next-lane {l = l} p)   E ρ q = ClearLanes p E ρ q × All (Later (liftLanes p q)) (partLanes (l ∷ []) E ρ)

    private
      -- A gate above a live cold is open (`Gated`).
      live : ∀ {x : Bool} {hd} → (x ≡ false → spentʰ hd ≡ true) → spentʰ hd ≡ false → x ≡ true
      live {true}  d lv = refl
      live {false} d lv with trans (sym (d refl)) lv
      ... | ()

      opened : ∀ {X : Set₁} (mb : Maybe X) {hd} → (mb ≡ nothing → spentʰ hd ≡ true) → spentʰ hd ≡ false → Σ X λ b → mb ≡ just b
      opened (just b) d lv = b , refl
      opened nothing  d lv with trans (sym (d refl)) lv
      ... | ()

      -- A source stepping silently has something left to show, so the
      -- meaning holds it.
      held : ∀ {A} (m : Maybe (U.Node A)) {s′ : U.Node A} {L s₁} → Kept m (just s′) → U.step s′ ≡ U.skipˢ L s₁ → m ≡ just s′
      held (just x) k _ = cong just k
      held nothing  k e with trans (sym (cong over e)) (lower k)
      ... | ()

      lanes-split : ∀ {Δ B} (l : Lane h Δ B) ls (E : Env Δ h) ρ → partLanes (l ∷ ls) E ρ ≡ partLanes (l ∷ []) E ρ ++ partLanes ls E ρ
      lanes-split (lane c k s) ls E ρ with val (Kit.live c) | part s E ρ
      ... | true  | just x  = refl
      ... | true  | nothing = refl
      ... | false | _       = refl

      merged-lanes : ∀ {A B} op (g : A → Pos → U.Node B) o bs (n : U.Node B) as qs
                   → merged op g o (bs ++ n ∷ as) qs ≡ just (U.flatMapᶜ op g o (bs ++ n ∷ as) qs)
      merged-lanes op g (just _) bs      n as qs = refl
      merged-lanes op g nothing  []      n as qs = refl
      merged-lanes op g nothing  (_ ∷ _) n as qs = refl

      -- A connect's body steps first, the source it holds next stepping later.
      beside-body : ∀ {A B} (b : U.Node B) {L b₁} (x : U.Node A) sx → U.step b ≡ U.skipˢ L b₁ → After L (U.headˢ sx)
                  → Σ (U.Node B) λ n₁ → U.besideˢ b (U.step b) x sx ≡ U.skipˢ L n₁
                                      × connected (if over sx then nothing else just x) (just b₁) ≡ just n₁
      beside-body b {L} {b₁} x (U.outˢ k _ x′) sb h =
        U.connectᶜ b₁ x
        , trans (cong (λ z → U.aheadˢ b z x (k ++ [ ix 0 ]) x′ (U.beforeˢ (k ++ [ ix 0 ]) z)) sb)
                (cong (U.aheadˢ b (U.skipˢ L b₁) x (k ++ [ ix 0 ]) x′) (<ᵖ-asym L (k ++ [ ix 0 ]) (<ᵖ-ext L k [ ix 0 ] h)))
        , refl
      beside-body b {L} {b₁} x (U.skipˢ k x′) sb h =
        U.connectᶜ b₁ x
        , trans (cong (λ z → U.aheadˢ b z x (k ++ [ ix 0 ]) x′ (U.beforeˢ (k ++ [ ix 0 ]) z)) sb)
                (cong (U.aheadˢ b (U.skipˢ L b₁) x (k ++ [ ix 0 ]) x′) (<ᵖ-asym L (k ++ [ ix 0 ]) (<ᵖ-ext L k [ ix 0 ] h)))
        , refl
      beside-body b {b₁ = b₁} x (U.endˢ _) sb _ = b₁ , sb , refl
      beside-body b {b₁ = b₁} x U.hushˢ    sb _ = b₁ , sb , refl

    -- A live cold's silent step, every sibling above it clear, is the
    -- step of what is open around it, lifted, to the witness with its
    -- phase moved.
    mutual
      lift-skip : ∀ {Δ A B} {t : Sub h Δ A} {s : Sink h B} {hd} (sp : Spot t s hd) {E ρ q} {ph : Phase B}
                → spentʰ hd ≡ false → Gated t E ρ → Clear sp E ρ q
                → U.step (nodeOf (phaseAt sp)) ≡ U.skipˢ q (nodeOf ph)
                → Σ (U.Node A) λ n → Σ (U.Node A) λ n₁ → part t E ρ ≡ just n × U.step n ≡ U.skipˢ (lift sp q) n₁
                                                       × part (stepAt sp ph E ρ) E ρ ≡ just n₁
      lift-skip (cold-here {ph = ph₀}) {ph = ph} lv g c e =
        nodeOf ph₀ , nodeOf ph , cong (λ z → if z then nothing else just (nodeOf ph₀)) lv , e , cong (λ z → if z then nothing else just (nodeOf ph)) lv
      lift-skip (in-map {f = f} p) {E} {ρ} {q} {ph} lv g c e with lift-skip p {E} {ρ} {q} {ph} lv g c e
      ... | n , n₁ , o , sn , o₁ = U.mapᶜ f n , U.mapᶜ f n₁ , cong (mapᴹ (U.mapᶜ f)) o , cong (U.mapˢ f) sn , cong (mapᴹ (U.mapᶜ f)) o₁
      lift-skip (in-scan {f = f} {r} p) {E} {ρ} {q} {ph} lv g c e with lift-skip p {E} {ρ} {q} {ph} lv g c e
      ... | n , n₁ , o , sn , o₁ =
        U.scanᶜ f (val r) n , U.scanᶜ f (val r) n₁ , cong (mapᴹ (U.scanᶜ f (val r))) o , cong (U.scanˢ f (val r)) sn , cong (mapᴹ (U.scanᶜ f (val r))) o₁
      lift-skip (in-take {i = i} {p = pr} {c = c} {t = t} p) {E} {ρ} {q} {ph} lv (d , g) c′ e with lift-skip p {E} {ρ} {q} {ph} lv g c′ e
      ... | n , n₁ , o , sn , o₁ = U.takeWhileᶜ i pr n , U.takeWhileᶜ i pr n₁ , taken t o , cong (U.takeWhileˢ i pr) sn , taken (stepAt p ph E ρ) o₁
        where taken : ∀ t′ {n′} → part t′ E ρ ≡ just n′
                    → (if val (Kit.live c) then mapᴹ (U.takeWhileᶜ i pr) (part t′ E ρ) else nothing) ≡ just (U.takeWhileᶜ i pr n′)
              taken t′ o′ = trans (cong (λ z → if z then mapᴹ (U.takeWhileᶜ i pr) (part t′ E ρ) else nothing) (live (λ x → d x p) lv))
                                  (cong (mapᴹ (U.takeWhileᶜ i pr)) o′)
      lift-skip (in-outer {op = op} {f} {fl} {ls = ls} p) {E} {ρ} {q} {ph} lv (g , _) (c , al) e with lift-skip p {E} {ρ} {q} {ph} lv g c e
      ... | n , n₁ , o , sn , o₁ =
        U.flatMapᶜ op G (just n) PL Q , U.flatMapᶜ op G (just n₁) PL Q , cong (λ mo → merged op G mo PL Q) o
        , go-outer op G PL Q sn al (U.earliest PL) (found-in PL) , cong (λ mo → merged op G mo PL Q) o₁
        where G = λ a q → U.subscribe (f a) ρ q
              PL = partLanes ls E ρ
              Q = val (Flat.queue fl)
      lift-skip (in-lanes {op = op} {f} {fl} {t = so} p) {E} {ρ} {q} {ph} lv (_ , g) (c , oo) e with lift-skip-lanes p {E} {ρ} {q} {ph} lv g c e
      ... | bs , n , n₁ , as , pl , pl₁ , sn , abs , aas =
        U.flatMapᶜ op G O (bs ++ n ∷ as) Q , U.flatMapᶜ op G O (bs ++ n₁ ∷ as) Q
        , trans (cong (λ z → merged op G O z Q) pl) (merged-lanes op G O bs n as Q)
        , trans (cong (U.goˢ op G O (bs ++ n ∷ as) Q) (earliest-at bs n as sn abs aas)) (go-lane op G O bs n as Q sn (lower oo))
        , trans (cong (λ z → merged op G O z Q) pl₁) (merged-lanes op G O bs n₁ as Q)
        where G = λ a q → U.subscribe (f a) ρ q
              O = part so E ρ
              Q = val (Flat.queue fl)
      lift-skip (in-source {S = S} {s₀ = s₀} {m = m} {u = u} p) {E} {ρ} {q} {ph} lv (km , dead , gs , _) (c , ob) e
        with lift-skip p {E} {ρ} {q} {ph} lv gs c e | opened (part u (S ∷ E) (s₀ ∷ ρ)) (λ x → dead x p) lv
      ... | s′ , s₁ , o , sn , o₁ | b , eb =
        U.connectᶜ b s′ , U.connectᶜ b s₁ , cong₂ connected (held m (subst (Kept m) o km) sn) eb
        , trans (cong (U.besideˢ b (U.step b) s′) sn)
                (ahead-src b (U.step b) s′ (lift p q ++ [ ix 0 ]) s₁ (subst (Open (lift p q ++ [ ix 0 ])) eb (lower ob)))
        , cong₂ connected o₁ eb
      lift-skip (in-body {S = S} {s₀ = s₀} {m = nothing} p) {E} {ρ} {q} {ph} lv (_ , _ , _ , g) (c , _) e
        with lift-skip p {S ∷ E} {s₀ ∷ ρ} {q} {ph} lv g c e
      ... | b , b₁ , o , sn , o₁ = b , b₁ , cong (connected nothing) o , sn , cong (connected nothing) o₁
      lift-skip (in-body {S = S} {s₀ = s₀} {m = just x} p) {E} {ρ} {q} {ph} lv (_ , _ , _ , g) (c , ox) e
        with lift-skip p {S ∷ E} {s₀ ∷ ρ} {q} {ph} lv g c e
      ... | b , b₁ , o , sn , o₁ with beside-body b x (U.step x) sn (lower ox)
      ... | n₁ , st , pr = U.connectᶜ b x , n₁ , cong (connected (just x)) o , st , trans (cong (connected (pruned (just x))) o₁) pr
      lift-skip (in-defer p) {E} {ρ} {q} {ph} lv g c e = lift-skip p {E} {ρ} {q} {ph} lv g c e

      lift-skip-lanes : ∀ {Δ B C} {ls : List (Lane h Δ B)} {s : Sink h C} {hd} (sp : SpotLanes ls s hd) {E ρ q} {ph : Phase C}
                      → spentʰ hd ≡ false → GatedLanes ls E ρ → ClearLanes sp E ρ q
                      → U.step (nodeOf (phaseAtLanes sp)) ≡ U.skipˢ q (nodeOf ph)
                      → Σ (List (U.Node B)) λ bs → Σ (U.Node B) λ n → Σ (U.Node B) λ n₁ → Σ (List (U.Node B)) λ as
                        → partLanes ls E ρ ≡ bs ++ n ∷ as × partLanes (stepAtLanes sp ph E ρ) E ρ ≡ bs ++ n₁ ∷ as
                        × U.step n ≡ U.skipˢ (liftLanes sp q) n₁ × All (Later (liftLanes sp q)) bs × All (Later (liftLanes sp q)) as
      lift-skip-lanes (this-lane {c = c} {t = t} {ls = ls} p) {E} {ρ} {q} {ph} lv (d , g , _) (c′ , al) e
        with lift-skip p {E} {ρ} {q} {ph} lv g c′ e
      ... | n , n₁ , o , sn , o₁ = [] , n , n₁ , partLanes ls E ρ , spread t o , spread (stepAt p ph E ρ) o₁ , sn , [] , al
        where spread : ∀ t′ {n′} → part t′ E ρ ≡ just n′
                     → (if val (Kit.live c) then consᴹ (part t′ E ρ) (partLanes ls E ρ) else partLanes ls E ρ) ≡ n′ ∷ partLanes ls E ρ
              spread t′ o′ = trans (cong (λ z → if z then consᴹ (part t′ E ρ) (partLanes ls E ρ) else partLanes ls E ρ) (live (λ x → d x p) lv))
                                   (cong (λ z → consᴹ z (partLanes ls E ρ)) o′)
      lift-skip-lanes (next-lane {l = lane c k t} {ls = ls} p) {E} {ρ} {q} {ph} lv (_ , _ , g) (c′ , al) e
        with lift-skip-lanes p {E} {ρ} {q} {ph} lv g c′ e
      ... | bs , n , n₁ , as , pl , pl₁ , sn , abs , aas =
        L₀ ++ bs , n , n₁ , as , spread ls n pl , spread (stepAtLanes p ph E ρ) n₁ pl₁ , sn , ++⁺ al abs , aas
        where L₀ = partLanes (lane c k t ∷ []) E ρ
              spread : ∀ ls′ x → partLanes ls′ E ρ ≡ bs ++ x ∷ as → partLanes (lane c k t ∷ ls′) E ρ ≡ (L₀ ++ bs) ++ x ∷ as
              spread ls′ x pl′ = trans (lanes-split (lane c k t) ls′ E ρ) (trans (cong (L₀ ++_) pl′) (sym (++-assoc L₀ bs (x ∷ as))))

  postulate
    -- At a burst boundary every other node's next event comes after the
    -- firing cold's step: another cold's is a queued timer's, past the
    -- run's position (`Ordered`, `Timed`) and so past every step of a
    -- frame the run is short of (`behind`); a joiner's copy is its
    -- source's (`caught`), shown below its own join point (`past`).
    clear : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {b : Frame A u}
          → (H : Holding (firing s hd τ r i b ∷ []) c st) → lower (get (State.heap st) hd) ≡ false
          → ∀ {q} {ph : Phase A} → U.burstˢ τ r i b ≡ U.skipˢ q (nodeOf ph)
          → On.Clear (State.heap st) (spot-of (Holding.tree H) (Holding.firing≡ H)) [] [] q
