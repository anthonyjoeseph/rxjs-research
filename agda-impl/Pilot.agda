{-# OPTIONS --guardedness #-}

module Pilot where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import operation.AbstractObservable using (module Run)
open import operation.PureObservable using (Pureᴾ; same; note; fin)
open import denotation.MonotonicList using (Pos; tick; Events; Events∞; out; skip; end; hush; Time)
open import operation.PureObservable using (module Pure)
open import operation.Placed using (Placed; cut; ends; quiets; sends; skips)

open Events∞

module Prefix (A : Set) where
  open Pure A using (End; finished; dry; cutOff)

  -- Through skips only.
  data _↝_ : Events A → Events A → Set where
    stay : ∀ {e} → e ↝ e
    past : ∀ {p k e} → force k ↝ e → skip p k ↝ e

  -- The record so far, each value at its own event of `E`, with `r` left.
  data Pre : List Pos → List (Time × A) → Events A → Events A → Set where
    pnil  : ∀ {e} → Pre [] [] e e
    pskip : ∀ {qs xs p k r} → Pre qs xs (force k) r → Pre qs xs (skip p k) r
    pout  : ∀ {qs xs p a k r} → Pre qs xs (force k) r → Pre (p ∷ qs) ((tick p , a) ∷ xs) (out p a k) r

  -- One more value, at its event past some skips.
  pre-snoc : ∀ {qs xs E r q a k} → Pre qs xs E r → r ↝ out q a k → Pre (qs ++ [ q ]) (xs ++ [ (tick q , a) ]) E (force k)
  pre-snoc pnil      stay     = pout pnil
  pre-snoc pnil      (past s) = pskip (pre-snoc pnil s)
  pre-snoc (pskip p) s        = pskip (pre-snoc p s)
  pre-snoc (pout p)  s        = pout (pre-snoc p s)

  -- Read off, however the run ended.
  pre-cut : ∀ {qs xs E r} c → Pre qs xs E r → Placed (cutOff c) qs xs E
  pre-cut c pnil      = cut
  pre-cut c (pskip p) = skips (pre-cut c p)
  pre-cut c (pout p)  = sends (pre-cut c p)

  pre-end : ∀ {qs xs E r q} → Pre qs xs E r → r ↝ end q → Placed finished (qs ++ [ q ]) xs E
  pre-end pnil      stay     = ends
  pre-end pnil      (past s) = skips (pre-end pnil s)
  pre-end (pskip p) s        = skips (pre-end p s)
  pre-end (pout p)  s        = sends (pre-end p s)

  pre-dry : ∀ {qs xs E r} → Pre qs xs E r → r ↝ hush → Placed dry qs xs E
  pre-dry pnil      stay     = quiets
  pre-dry pnil      (past s) = skips (pre-dry pnil s)
  pre-dry (pskip p) s        = skips (pre-dry p s)
  pre-dry (pout p)  s        = sends (pre-dry p s)

module Root (A : Set) (E₀ : Events A) where
  open Prefix A
  open Pure A using (State; outcome; Res; res; finished)

  -- The root's record so far, against `E₀`, with `r` left; or complete.
  data Root {h} (r : Events A) (st : State h) : Set where
    live : State.ended st ≡ false → Pre (State.marks st) (State.log st) E₀ r → Root r st
    over : State.ended st ≡ true → Placed finished (State.marks st) (State.log st) E₀ → Root r st

  note-ok : ∀ {h} {st : State h} {r q a k} → Root r st → r ↝ out q a k → State.pos st ≡ q → State.clock st ≡ tick q
          → Root (force k) (Res.state (outcome (note a) st))
  note-ok {st = st} (live e p) s refl c rewrite e | c = live refl (pre-snoc p s)
  note-ok {st = st} (over e p) s refl c rewrite e = over refl p

  fin-ok : ∀ {h} {st : State h} {r q} r′ → Root r st → r ↝ end q → State.pos st ≡ q → Root r′ (Res.state (outcome fin st))
  fin-ok {st = st} r′ (live e p) s refl rewrite e = over refl (pre-end p s)
  fin-ok {st = st} r′ (over e p) s refl rewrite e = over refl p

  ↝-skip : ∀ {r p k} → r ↝ skip p k → r ↝ force k
  ↝-skip stay     = past stay
  ↝-skip (past s) = past (↝-skip s)

module Eng (R : Set) (E₀ : Events R) (N : ℕ) where
  open import Data.Maybe using (Maybe)
  open import Level using (lower; lift)
  open import Data.List.Relation.Unary.All using (All; _∷_)
  open import Data.Nat using (_≤_; _∸_)
  open import Data.Nat.Properties using (n≤1+n; m+[n∸m]≡n; ≤-trans)
  open import Data.Nat using (z≤n)
  open import Relation.Binary.PropositionalEquality using (trans)
  open import denotation.MonotonicList using (last)
  open import operation.PureObservable using (Kind; play; slot; _⊑_; _⨾_; _∋_; here; there; wk∋; Sink; Handle)
  open import denotation.MonotonicList using (Burst; Burst∞; ML∞; ix; sub; ML; done; quiet; at; emit; stall; close; burst; frames; start; root)
  open import Adequacy using (Rises; Rise; inside; ahead)
  open Prefix R
  open Root R E₀
  open Run (Pureᴾ R) using (Act; eff; done)
  open Pure R using (State; Res; res; Callbacks; get; put; Timer; module Play; runᴺ; outcome; finished)

  cbAt : ∀ {h} → Callbacks R h
  cbAt = record { onNext = λ a → eff (note a) (λ _ → done tt) ; onComplete = eff fin (λ _ → done tt) ; isClosed = done false }

  mkTimer : ∀ {h} → ℕ → Sink h R → Handle h → Time → Pos → Burst R → Timer h
  mkTimer d s hd t e b = record { due = d ; sink = s ; handle = hd ; at′ = t ; from = e ; frame = b }

  data Cfg {h} (st : State h) : Set₁ where
    pending : ∀ {r₀ d t e b} (s : Sink h R) (hd : Handle h) → State.ended st ≡ false → State.timers st ≡ mkTimer d s hd t e b ∷ []
            → get (State.heap st) s ≡ cbAt → lower (get (State.heap st) hd) ≡ false → d ≡ t
            → Pre (State.marks st) (State.log st) E₀ r₀ → r₀ ↝ burst 0 (ix t ∷ sub e ∷ []) 0 b → Rises (suc t) (inside b) → Cfg st
    silent  : ∀ {r₀} → State.ended st ≡ false → State.timers st ≡ [] → Pre (State.marks st) (State.log st) E₀ r₀ → r₀ ↝ hush → Cfg st
    over    : State.ended st ≡ true → State.timers st ≡ [] → Placed finished (State.marks st) (State.log st) E₀ → Cfg st

  data CutOk {h} (st : State h) : Set₁ where
    cutok : ∀ {r} → Root r st → CutOk st

  PostV : ∀ {h} → State h → Maybe ⊤ → Set₁
  PostV st nothing  = CutOk st
  PostV st (just _) = Cfg st

  Post : ∀ {h} → Res h ⊤ → Set₁
  Post x = PostV (Res.state x) (Res.value x)

  note-live : ∀ {h} {st : State h} {r₀ q a k} → State.ended st ≡ false → Pre (State.marks st) (State.log st) E₀ r₀
            → r₀ ↝ out q a k → State.pos st ≡ q → State.clock st ≡ tick q
            → Pre (State.marks (Res.state (outcome (note a) st))) (State.log (Res.state (outcome (note a) st))) E₀ (force k)
  note-live {st = st} e p s refl c rewrite e | c = pre-snoc p s

  fin-live : ∀ {h} {st : State h} {r₀ q} → State.ended st ≡ false → Pre (State.marks st) (State.log st) E₀ r₀
           → r₀ ↝ end q → State.pos st ≡ q
           → Placed finished (State.marks (Res.state (outcome fin st))) (State.log (Res.state (outcome fin st))) E₀
  fin-live {st = st} e p s refl rewrite e = pre-end p s

  finish-ok : ∀ k {w h} (s : Sink w R) (σ : w ⊑ h) (st : State h) {r₀ q}
            → get (State.heap st) (wk∋ σ s) ≡ cbAt → State.ended st ≡ false → State.timers st ≡ []
            → Pre (State.marks st) (State.log st) E₀ r₀ → r₀ ↝ end q → State.pos st ≡ q
            → Post (Play.finishᴾ N (runᴺ N k) s σ st)
  finish-ok zero    s σ st hs en ht p r q = cutok (live en p)
  finish-ok (suc k) s σ st hs en ht p r q rewrite hs = over refl ht (fin-live {st = st} en p r q)

  get-put : ∀ {h w} (xs : All (Pure.Val R h) w) (i : w ∋ play) (y : Pure.Val R h play) (j : w ∋ slot R) → get (put xs i y) j ≡ get xs j
  get-put (x ∷ xs) here      y (there j) = refl
  get-put (x ∷ xs) (there i) y here      = refl
  get-put (x ∷ xs) (there i) y (there j) = get-put xs i y j

  unless-ok : ∀ {w h} {hd : Handle w} {m : Pure.M R w ⊤} {σ : w ⊑ h} {st : State h}
            → lower (get (State.heap st) (wk∋ σ hd)) ≡ false → Post (m σ st) → Post (Pure.unlessSpent R hd m σ st)
  unless-ok {hd = hd} {σ = σ} {st = st} hh q rewrite hh = q

  mutual
    burst-ok : ∀ k f {w h} (s : Sink w R) (hd : Handle w) (σ : w ⊑ h) (st : State h) {c rest i b r₀}
             → get (State.heap st) (wk∋ σ s) ≡ cbAt → lower (get (State.heap st) (wk∋ σ hd)) ≡ false
             → State.ended st ≡ false → State.timers st ≡ [] → State.clock st ≡ c
             → Pre (State.marks st) (State.log st) E₀ r₀ → r₀ ↝ burst 0 (ix c ∷ rest) i b → Rises (suc c) (inside b)
             → Post (Play.burst N (runᴺ N k) f s hd c (ix c ∷ rest) i b σ st)
    burst-ok k       zero    s hd σ st hs hh e ht hc p r u = cutok (live e p)
    burst-ok zero    (suc f) s hd σ st hs hh e ht hc p r u rewrite hh = cutok (live e p)
    burst-ok (suc k) (suc f) s hd σ st hs hh e ht hc p r u rewrite hh | hs = step-ok k f s hd σ st hs hh e ht hc p r u

    step-ok : ∀ k f {w h} (s : Sink w R) (hd : Handle w) (σ : w ⊑ h) (st : State h) {c rest i b r₀}
            → get (State.heap st) (wk∋ σ s) ≡ cbAt → lower (get (State.heap st) (wk∋ σ hd)) ≡ false
            → State.ended st ≡ false → State.timers st ≡ [] → State.clock st ≡ c
            → Pre (State.marks st) (State.log st) E₀ r₀ → r₀ ↝ burst 0 (ix c ∷ rest) i b → Rises (suc c) (inside b)
            → Post (Play.stepᴾ N (runᴺ N (suc k)) f s hd c (ix c ∷ rest) i b σ st)
    step-ok k f s hd σ st {c} {rest} {i} {b = emit a k′} hs hh e ht hc p r u rewrite hh | hs =
      unless-ok {m = Play.burst N (runᴺ N (suc k)) f s hd c (ix c ∷ rest) (suc i) (Burst∞.force k′)} {st = st₂} hh
        (burst-ok (suc k) f s hd σ st₂ hs hh e ht hc (note-live {st = st₁} e p r refl hc) stay (Rises.rises u))
      where st₁ = record st { pos = (ix c ∷ rest) ++ [ ix i ] }
            st₂ = Res.state (outcome (note a) st₁)
    step-ok k f s hd σ st {b = stall k′} hs hh e ht hc p r u = burst-ok (suc k) f s hd σ st hs hh e ht hc p (↝-skip r) (Rises.rises u)
    step-ok k f s hd σ st {c} {rest} {b = close k′} hs hh e ht hc p r u =
      schedule-ok (suc k) s hd σ st (ML∞.force k′) hs hh e ht hc (n≤1+n c) p (↝-skip r) (Rises.rises (Rises.rises u))

    schedule-ok : ∀ k {w h} (s : Sink w R) (hd : Handle w) (σ : w ⊑ h) (st : State h) {c t₀ e r₀} (m : ML R)
                → get (State.heap st) (wk∋ σ s) ≡ cbAt → lower (get (State.heap st) (wk∋ σ hd)) ≡ false
                → State.ended st ≡ false → State.timers st ≡ [] → State.clock st ≡ c → c ≤ t₀
                → Pre (State.marks st) (State.log st) E₀ r₀ → r₀ ↝ frames 0 e m → Rise t₀ (ahead m)
                → Post (Play.schedule N (runᴺ N k) s hd c e m σ st)
    schedule-ok k s hd σ st {e = e} done hs hh en ht hc l p r u =
      unless-ok {m = Pure.bind R (Pure.spend R hd) λ _ → Pure.bind R (Pure.gotoᴾ R e) λ _ → Play.finishᴾ N (runᴺ N k) s} hh
        (finish-ok k s σ st₂ (trans (get-put (State.heap st) (wk∋ σ hd) (lift true) (wk∋ σ s)) hs) en ht p r refl)
      where st₂ = record st { heap = put (State.heap st) (wk∋ σ hd) (lift true) ; pos = e }
    schedule-ok k s hd σ st quiet    hs hh en ht hc l p r u = silent en ht p r
    schedule-ok k s hd σ st {c} {e = e} (at t b) hs hh en ht hc l p r (t₀≤t , u) =
      pending (wk∋ σ s) (wk∋ σ hd) en (cong (Pure.insert R (mkTimer (State.clock st + (t ∸ c)) (wk∋ σ s) (wk∋ σ hd) t e b)) ht) hs hh
        (trans (cong (_+ (t ∸ c)) hc) (m+[n∸m]≡n (≤-trans l t₀≤t))) p r u


  data Done {h} (st : State h) : Set₁ where
    silent′ : ∀ {r₀} → State.ended st ≡ false → Pre (State.marks st) (State.log st) E₀ r₀ → r₀ ↝ hush → Done st
    over′   : State.ended st ≡ true → Placed finished (State.marks st) (State.log st) E₀ → Done st

  PostDV : ∀ {h} → State h → Maybe ⊤ → Set₁
  PostDV st nothing  = CutOk st
  PostDV st (just _) = Done st

  PostD : ∀ {h} → Res h ⊤ → Set₁
  PostD x = PostDV (Res.state x) (Res.value x)

  cfg-cut : ∀ {h} {st : State h} → Cfg st → CutOk st
  cfg-cut (pending s hd e ht hs hh d p r u) = cutok (live e p)
  cfg-cut (silent e ht p r)                 = cutok (live e p)
  cfg-cut (over e ht p)                     = cutok {r = hush} (over e p)

  again : ℕ → Bool → Pure.M R [] ⊤
  again m a = if_then_else_ {A = Pure.M R [] ⊤} a (Pure.loopᴺ R N m) (Pure.ret R tt)

  mutual
    loop-ok : ∀ m {h} (σ : [] ⊑ h) (st : State h) → Cfg st → PostD (Pure.loopᴺ R N m σ st)
    loop-ok zero    σ st q = cfg-cut q
    loop-ok (suc m) σ st (pending s hd e ht hs hh refl p r u) rewrite ht =
      loop-tail m σ _ (unless-ok {hd = hd} {m = Play.burst N (runᴺ N (suc m)) N s hd _ _ 0 _} {σ = same} {st = st₁} hh
                        (burst-ok (suc m) N s hd same st₁ hs hh e refl refl p r u))
      where st₁ = record st { clock = _ ; timers = [] ; pos = _ }
    loop-ok (suc m) σ st (silent e ht p r) rewrite ht = silent′ e p r
    loop-ok (suc m) σ st (over e ht p) rewrite ht = over′ e p

    loop-tail : ∀ m {h} (σ : [] ⊑ h) (Y : Res h ⊤) → Post Y
              → PostD (Pure.then R (λ a τ → again m a (σ ⨾ τ))
                                   (Pure.then R (λ _ _ st′ → res same st′ (just true)) Y))
    loop-tail m σ (res g st nothing)   q = q
    loop-tail m σ (res g st (just tt)) q = loop-ok m (σ ⨾ g) st q

  then-ok : ∀ {h} (K : ⊤ → Pure.M R h ⊤) (Y : Res h ⊤) → Post Y
          → (∀ {v} (g : h ⊑ v) (st : State v) → Cfg st → Post (K tt g st)) → Post (Pure.then R K Y)
  then-ok K (res g st nothing)   q f = q
  then-ok K (res g st (just tt)) q f = f g st q

  then-okD : ∀ {h} (K : ⊤ → Pure.M R h ⊤) (Y : Res h ⊤) → Post Y
           → (∀ {v} (g : h ⊑ v) (st : State v) → Cfg st → PostD (K tt g st)) → PostD (Pure.then R K Y)
  then-okD K (res g st nothing)   q f = q
  then-okD K (res g st (just tt)) q f = f g st q

  sched : ∀ k {w h} (s : Sink w R) (hd : Handle w) (σ : w ⊑ h) (st : State h) {r₀} (m : ML R)
        → get (State.heap st) (wk∋ σ s) ≡ cbAt → lower (get (State.heap st) (wk∋ σ hd)) ≡ false
        → State.ended st ≡ false → State.timers st ≡ [] → State.clock st ≡ 0 → State.pos st ≡ root
        → Pre (State.marks st) (State.log st) E₀ r₀ → r₀ ↝ frames 0 (root ++ [ last ]) m → Rise 0 (ahead m)
        → Post (Play.schedule N (runᴺ N k) s hd 0 (State.pos st ++ [ last ]) m σ st)
  sched k s hd σ st m hs hh e ht hc hp p r u =
    subst (λ q → Post (Play.schedule N (runᴺ N k) s hd 0 (q ++ [ last ]) m σ st)) (sym hp) (schedule-ok k s hd σ st m hs hh e ht hc z≤n p r u)

  first-ok : ∀ k {w h} (s : Sink w R) (hd : Handle w) (σ : w ⊑ h) (st : State h) {r₀} (m : ML R)
           → get (State.heap st) (wk∋ σ s) ≡ cbAt → lower (get (State.heap st) (wk∋ σ hd)) ≡ false
           → State.ended st ≡ false → State.timers st ≡ [] → State.clock st ≡ 0 → State.pos st ≡ root
           → Pre (State.marks st) (State.log st) E₀ r₀ → r₀ ↝ start root m → Rises 0 (ahead m)
           → Post (Play.first N (runᴺ N k) s hd m σ st)
  first-ok k {w} s hd σ st (at zero b) hs hh e ht hc hp p r u with Rises.rises u
  ... | _ , v = subst (λ q → Post (Play.burst N (runᴺ N k) N s hd 0 q 0 b σ st)) (sym hp) (burst-ok k N s hd σ st hs hh e ht hc p r v)
  first-ok k s hd σ st done        hs hh e ht hc hp p r u = sched k s hd σ st done hs hh e ht hc hp p r (Rises.rises u)
  first-ok k s hd σ st quiet       hs hh e ht hc hp p r u = sched k s hd σ st quiet hs hh e ht hc hp p r (Rises.rises u)
  first-ok k s hd σ st (at (suc t) b) hs hh e ht hc hp p r u = sched k s hd σ st (at (suc t) b) hs hh e ht hc hp p r (Rises.rises u)

module Top (R : Set) where
  open import Data.Maybe using (Maybe)
  open import Level using (lower; lift)
  open import operation.PureObservable using (here; there; same; new)
  open import denotation.MonotonicList using (root; start; coldᴰ; observe; Timeline)
  open import Adequacy using (Rises; ahead)
  open Run (Pureᴾ R) using (via; startCold)
  open Pure R using (State; Res; res; cutOff; finished; dry; endOf)
  open import operation.Placed using (module Ran)
  open Ran R using (ran; Recorded)

  root-ok : ∀ N (c : Timeline R) → Rises 0 (ahead (lower c)) → Recorded (ran N (via (startCold c))) (observe (coldᴰ (lower c)) root)
  root-ok zero    c u = cut
  root-ok (suc n) c u = rec-of (ran (suc n) (via (startCold c))) (then-okD _ _ (then-ok _ _ (first-ok n (there here) here same _ (lower c) refl refl refl refl refl refl pnil stay u)
                                                 (λ g st q → q))
                                   (λ g st q → loop-ok (suc n) _ st q))
    where
      E₀ = observe (coldᴰ (lower c)) root
      open Prefix R
      open Root R E₀
      open Eng R E₀ (suc n)
      rec-of : (x : Res [] ⊤) → PostD x → Recorded x E₀
      rec-of (res σ st nothing)   (cutok (live e p)) rewrite e = pre-cut _ p
      rec-of (res σ st nothing)   (cutok (over e p)) rewrite e = p
      rec-of (res σ st (just tt)) (silent′ e p r)    rewrite e = pre-dry p r
      rec-of (res σ st (just tt)) (over′ e p)        rewrite e = p
