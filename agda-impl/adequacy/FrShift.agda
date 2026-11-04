{-# OPTIONS --guardedness #-}

-- THE CURSOR SHIFTED UNDER A FOCUS: `shift` frame by frame, from the
-- hole up to its world's top.  In the root's world the root's cursor
-- moves with it, what the root owes unchanged below the least key; in
-- an isle's only the isle's cursor moves, and the root's stays.  Each
-- frame's fields shift as the node's do in `Shifted`, read off what the
-- hole's rows give (`HF`): finitely many owed before `p`, none owed
-- before it visible.  A frame passes its parent the same of its own
-- entry, as `fb` passes a bound; its siblings shift by `shift` under the
-- whole tree's least key, an isle's binders by `subd-env`.
module adequacy.FrShift where

open import Data.Bool using (true; false)
open import Data.List using (List; _∷_; _++_; reverse; _ʳ++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.Events using (Pos)
open import denotation.EmissionSet using (EmissionSet; ⟦_⟧; _≺_)
open import operation.Key using (at)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; Scope; scopeOf; plug; binds; CS; connS; flatS; takeS)
open import adequacy.Rows using (full; Frozen; _≃_; _⇄_; ≃-refl)
open _≃_
open import adequacy.Cursor using (Cur; bef; Owes; Due; Pol; Kill; kill-out; Kept; Hole; h-live; polF; JoinF; joined; Behind;
  Src; Sync; burst-dn; alike; Rgn)
open import adequacy.Cursor.Frame using (Need; owes; dead; lane; lanecut; pnd; ⊥₁; Fr;
  f-top; f-map; f-scan; f-cut; f-take; f-took; f-outer; f-lanes; f-lane; f-lnct; f-src; f-srcc; f-srcp; f-body;
  d-map; d-scan; d-cut; d-ln; d-take; d-outer; d-lanes; d-src; d-body; f-isle; f-islec; f-islep)
open import adequacy.Floor.Keys using (plug-in; own-bld; os; oo)
open import adequacy.Least using (k-own; k-kid; k-outer; k-lane; k-body; Lo)
open import adequacy.Bound using (Bnd; LoP; Env; env-bind; owes-≼; lo-p; map-b; scan-b; take-b; flat-b; begun-b; bound; src-b; body-key; ≮-after)
open import adequacy.FrameBound using (conn-fb; lanes-b; pre-in; post-in)
open import adequacy.Few using (call-sh; Lag; EnvL; KLag; LBnd; lag-≈; lag-at; map-row; scan-row; take-lag; behind-bef; conn-lag; flat-lag; hole-kl;
  begun-f; few; envl-bind; src-f; subd-env; att-slot; shift; module Shifted)

------------------------------------------------------------------------
-- What a hole's rows give the frames above it, read under its scope:
-- finitely many owed before `p`, and none visible owed before it.  A
-- part no live node reads, or one not yet subscribed, gives nothing.

record HR {Γ A} (C : Cur) (p : Pos) (sc : Scope Γ) (E : EmissionSet A) : Set₁ where
  constructor hr
  field run : Env (full sc) C p → EnvL (full sc) C p → Lag C p E × Bnd C p E
open HR

HF : ∀ {Γ A} → Cur → Pos → Scope Γ → Need → EmissionSet A → Set₁
HF C p sc owes              E = HR C p sc E
HF C p sc (dead _ _)          E = ⊥₁
HF C p sc (lane true _ _)     E = HR C p sc E
HF C p sc (lane false _ _)    E = ⊥₁
HF C p sc (lanecut true _ _)  E = HR C p sc E
HF C p sc (lanecut false _ _) E = ⊥₁
HF C p sc (pnd _)           E = ⊥₁

-- A frame's entry read off its hole's.
hr-map : ∀ {Γ A B} {C p} {sc : Scope Γ} {E : EmissionSet A} {E′ : EmissionSet B}
       → (Lag C p E → Lag C p E′) → (Bnd C p E → Bnd C p E′) → HR C p sc E → HR C p sc E′
hr-map f g h = hr λ env ef → f (proj₁ (run h env ef)) , g (proj₂ (run h env ef))

-- A connect's body's binders: its source's rows, read past `p`.
bind-env : ∀ {Γ X} {sc : Scope Γ} {k : CS Γ X} {C p} → CS.scope k ≡ sc → Bnd C p (Frozen k) → Behind (bef p) (Frozen k)
         → Env (full sc) C p → EnvL (full sc) C p
         → Env (full (binds (CS.src k) (CS.connAt k) sc)) C p × EnvL (full (binds (CS.src k) (CS.connAt k) sc)) C p
bind-env {k = k} refl sb bf env ef = env-bind {o = CS.src k} {r = CS.connAt k} sb env , envl-bind {o = CS.src k} {r = CS.connAt k} bf ef

-- Likewise off the source's own state.
body-env : ∀ {Γ X B} {sc : Scope Γ} {Rg C} {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) B} {p}
         → CS.scope k ≡ sc → Src sc Rg C k o → Env (full sc) C p → EnvL (full sc) C p → LoP (connS k o b) p
         → Env (full (binds (CS.src k) (CS.connAt k) (CS.scope k))) C p × EnvL (full (binds (CS.src k) (CS.connAt k) (CS.scope k))) C p
         × Bnd C p (Frozen k) × Behind (bef p) (Frozen k)
body-env {k = k} refl sr env ef lo =
  env-bind {o = CS.src k} {r = CS.connAt k} (src-b sr env lo) env , envl-bind {o = CS.src k} {r = CS.connAt k} (src-f sr env ef lo) ef ,
  src-b sr env lo , src-f sr env ef lo

src-sh′ : ∀ {Γ X B} {sc : Scope Γ} {Rg C} {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) B} {p} → Owes C p
        → CS.scope k ≡ sc → Src sc Rg C k o → Env (full sc) C p → EnvL (full sc) C p → Lo (connS k o b) (at p) → Src sc Rg (bef p) k o
src-sh′ {C = C} {b = b} {p} w refl sr env ef lo = Shifted.src-sh {C} {p} w {b = b} sr env ef lo

-- A live lane's kept rows, among its siblings'.
live-kl : ∀ {A B} {C p} {P : Pol A B} {q a Ph} {E : EmissionSet B} → Hole C P q a Ph E true → Lag C p E
        → Σ (List Pos) λ ks → ∀ {k e} → Kept P q a k e → Owes C k → k ≺ p → k ∈ ks
live-kl {P = P} (h-live _ eq _) lg = hole-kl {P = P} eq lg

klag-mid : ∀ {A B} {C p} {P : Pol A B} {vs₁ vs₂ : List (Pos × A)} {q a}
         → KLag C p P vs₁ → (Σ (List Pos) λ ks → ∀ {k e} → Kept P q a k e → Owes C k → k ≺ p → k ∈ ks) → KLag C p P vs₂
         → KLag C p P (vs₁ ++ (q , a) ∷ vs₂)
klag-mid {C = C} {p} {P} {vs₁} {vs₂} {q} {a} (k₁ , f₁) (k₀ , f₀) (k₂ , f₂) = k₁ ++ (k₀ ++ k₂) , pick
  where
    pick : ∀ {q′ a′ k e} → (q′ , a′) ∈ vs₁ ++ (q , a) ∷ vs₂ → Kept P q′ a′ k e → Owes C k → k ≺ p → k ∈ k₁ ++ (k₀ ++ k₂)
    pick iv kp o kp′ with ∈-++⁻ vs₁ iv
    ... | inj₁ i           = ∈-++⁺ˡ (f₁ i kp o kp′)
    ... | inj₂ (here refl) = ∈-++⁺ʳ k₁ (∈-++⁺ˡ (f₀ kp o kp′))
    ... | inj₂ (there i)   = ∈-++⁺ʳ k₁ (∈-++⁺ʳ k₀ (f₂ i kp o kp′))

------------------------------------------------------------------------
-- THE FRAMES RE-CURSORED: from `C` to `bef p`, `p` the whole tree's
-- least key, with the hole's binders read at `C`.

module _ {R : Set} (Rt : EmissionSet R) where

  Out : Cur → Cur → ∀ {Γ A} → Rgn → Ctx R Γ A → Need → EmissionSet A → Pos → Set₁
  Out Cr C Rg c N E p = Σ Cur λ Cr′ → Fr Rt Cr′ (bef p) Rg c N E × Env (full (scopeOf c)) C p × EnvL (full (scopeOf c)) C p
                                    × Due Cr Rt ≃ Due Cr′ Rt

  rc : ∀ {Cr C Γ A Rg} {c : Ctx R Γ A} {N E} {s : St Γ A} {p}
     → Fr Rt Cr C Rg c N E → HF C p (scopeOf c) N E → Owes C p → Lo (plug c s) (at p) → Out Cr C Rg c N E p
  rc {C = C} {p = p} (f-top eq) hf w lo = bef p , f-top eq , (λ ()) , (λ ()) , due
    where
      due : Due C Rt ≃ Due (bef p) Rt
      due = (λ (x , v , o) → let (y , v′) = from (alike eq) (x , v) in x , v , proj₂ (run hf (λ ()) (λ ())) (y , v′ , o))
          ⇄ (λ (x , v , pq) → x , v , owes-≼ C w pq)
  rc {C = C} {s = s} (f-map fr m sd) hf w lo =
    let (Cr′ , fr′ , rs) = rc {s = Machine.mapS _ s} fr
                             (hr-map (λ lg → lag-≈ m (lag-at map-row lg)) (λ bd (x , v , ow) → map-b {C = C} bd (from (alike m) (x , v)) ow) hf) w lo
    in Cr′ , f-map fr′ m sd , rs
  rc {C = C} {s = s} {p} (f-scan fr fo m sd) hf w lo =
    let (Cr′ , fr′ , env , ef , d) = rc {s = Machine.scanS _ _ s} fr
                                       (hr-map (λ lg → lag-≈ m (lag-at scan-row lg)) (λ bd (x , v , ow) → scan-b {C = C} bd (from (alike m) (x , v)) ow) hf) w lo
    in Cr′ , f-scan fr′ (Shifted.fold-sh {C} {p} w (proj₂ (run hf env ef)) fo) m sd , env , ef , d
  rc {s = s} (f-cut fr) hf w lo = let (Cr′ , fr′ , rs) = rc {s = Machine.cutS true _ s} fr hf w lo in Cr′ , f-cut fr′ , rs
  rc {C = C} {s = s} (f-take fr nf m sd) hf w lo =
    let (Cr′ , fr′ , env , ef , d) = rc {s = takeS _ _ _ s} fr
                                       (hr-map (λ lg → lag-≈ m (take-lag nf lg)) (λ bd (x , v , ow) → take-b {C = C} bd nf (from (alike m) (x , v)) ow) hf) w lo
    in Cr′ , f-take fr′ (λ y nk → proj₂ (run hf env ef) (y , _ , nf y nk)) m sd , env , ef , d
  rc {C = C} {c = Machine.inOuter op f _ _ _ _ ls c} {E = O} {s = s} {p}
     (f-outer {E′ = E′} fr ji jn@(joined bg _ wh _ ah _ en _) je sd bh) hf w lo =
    let (Cr′ , fr′ , env , ef , d) = rc {s = flatS _ _ _ _ _ _ s ls} fr hf′ w lo
    in Cr′ , f-outer fr′ ji (Shifted.joined-sh {C} {p} w (proj₂ (run hf env ef)) (kill-out op) jn env ef lol) je sd (behind-bef bh (jl env ef)) , env , ef , d
    where
      F = λ a → ⟦ f a ⟧ (full (scopeOf c))
      lol : ∀ {l} → l ∈ ls → Lo l (at p)
      lol i ki = lo (plug-in c (k-kid (k-lane i ki)))
      lolp : ∀ {l} → l ∈ ls → LoP l p
      lolp i = lo-p (lol i)
      lb : Env (full (scopeOf c)) C p → LBnd C p (polF op F O) _
      lb env iv kl ln v ow = begun-b {O = O} bg iv kl ln v ow en env lolp
      jl : Env (full (scopeOf c)) C p → EnvL (full (scopeOf c)) C p → Lag C p (JoinF op F O)
      jl env ef = flat-lag {op = op} {F = F} {O = O} (proj₁ (run hf env ef)) (proj₂ (run hf env ef)) (begun-f bg env ef lolp) (lb env) wh ah
      hf′ : HR C p (scopeOf c) E′
      hf′ = hr λ env ef → lag-≈ (proj₂ je) (lag-at (λ r → _ , proj₁ r) (jl env ef)) ,
        λ (x , v , ow) → flat-b {op = op} {F = F} {C = C} (proj₂ (run hf env ef)) (lb env) wh ah (proj₁ (proj₁ (from (alike (proj₂ je)) (x , v)))) v ow
  rc {C = C} {c = Machine.inLanes op f _ _ _ qu o pre post c} {E = E} {s = s} {p}
     (f-lanes {E′ = E′} {O = O} {vs₁ = vs₁} {vs₂ = vs₂} {ws = ws} {q = q} {a = a} {b = true} fr ji sy bg₁ y nq ru hl bg₂ eqn wt wh od ah as en li je sd sdl bh _) hf w lo =
    let (Cr′ , fr′ , env , ef , d) = rc {s = flatS _ _ _ _ _ _ o (pre ʳ++ s ∷ post)} fr hf′ w lo
        ob = bound sy env loop
    in Cr′ , f-lanes fr′ ji (shift sy w env ef loo) (Shifted.begun-sh {C} {p} w (ku ob) bg₁ env ef lpre) y (Shifted.nm {C} {p} w nq) ru (Shifted.hole-sh {C} {p} w (ku ob) hl)
                 (Shifted.begun-sh {C} {p} w (ku ob) bg₂ env ef lpost) eqn (Shifted.waiting-sh {C} {p} w {P = P} {O = O} {vs = vs} {ws = ws} {qu = qu} (lb env ef) ah wt)
                 (Shifted.whole-sh {C} {p} w {P = P} {O = O} {vs = vs} {ws = ws} ob wh) (Shifted.od-sh {C} {p} w {O = O} ob od)
                 (Shifted.ahead-sh {C} {p} w {P = P} {vs = vs} {ws = ws} (lb env ef) ah) as en li je sd sdl (behind-bef bh (jl env ef)) (λ ())
       , env , ef , d
    where
      F = λ a → ⟦ f a ⟧ (full (scopeOf c))
      P = polF op F O
      vs = vs₁ ++ (q , a) ∷ vs₂
      loo : Lo o (at p)
      loo ki = lo (plug-in c (k-kid (k-outer ki)))
      loop : LoP o p
      loop = lo-p loo
      lol : ∀ {l} → l ∈ pre ʳ++ s ∷ post → LoP l p
      lol i = lo-p (λ ki → lo (plug-in c (k-kid (k-lane i ki))))
      lpre : ∀ {l} → l ∈ reverse pre → Lo l (at p)
      lpre i ki = lo (plug-in c (k-kid (k-lane (pre-in pre i) ki)))
      lpost : ∀ {l} → l ∈ post → Lo l (at p)
      lpost i ki = lo (plug-in c (k-kid (k-lane (post-in pre i) ki)))
      ku : Bnd C p O → ∀ {q₁ q′} → Kill (polF op F O) q₁ q′ → Owes C q′ → Owes (bef p) q′
      ku ob k ow = ob (proj₁ (proj₂ (kill-out op k)) , _ , ow)
      lb : Env (full (scopeOf c)) C p → EnvL (full (scopeOf c)) C p → LBnd C p (polF op F O) (vs₁ ++ (q , a) ∷ vs₂)
      lb env ef iv kl ln v ow = lanes-b {pre = pre} {post = post} {s = s} bg₁ hl bg₂ y en env (λ _ → proj₂ (run hf env ef)) lol iv kl ln v ow
      jl : Env (full (scopeOf c)) C p → EnvL (full (scopeOf c)) C p → Lag C p (JoinF op F O)
      jl env ef = flat-lag {op = op} {F = F} {O = O} (few sy env ef loop) (bound sy env loop)
                    (klag-mid {C = C} {p = p} {P = P} {vs₁ = vs₁} {vs₂ = vs₂} {q = q} {a = a} (begun-f bg₁ env ef (λ i → lo-p (lpre i))) (live-kl hl (proj₁ (run hf env ef))) (begun-f bg₂ env ef (λ i → lo-p (lpost i)))) (lb env ef) wh ah
      hf′ : HR C p (scopeOf c) E′
      hf′ = hr λ env ef → lag-≈ (proj₂ je) (lag-at (λ r → _ , proj₁ r) (jl env ef)) ,
        λ (x , v , ow) → flat-b {op = op} {F = F} {C = C} (bound sy env loop) (lb env ef) wh ah (proj₁ (proj₁ (from (alike (proj₂ je)) (x , v)))) v ow
  rc (f-lanes {b = false} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) () w lo
  rc {s = s} (f-lane {b = true} fr) hf w lo = let (Cr′ , fr′ , rs) = rc {s = Machine.lnS true s} fr hf w lo in Cr′ , f-lane fr′ , rs
  rc (f-lane {b = false} _) () w lo
  rc {s = s} (f-lnct {b = true} fr) hf w lo = let (Cr′ , fr′ , rs) = rc {s = Machine.cutS true _ s} fr hf w lo in Cr′ , f-lnct fr′ , rs
  rc (f-lnct {b = false} _) () w lo
  rc {C = C} {c = Machine.inSrc k b c} {E = E} {s = s} {p} (f-src {E′ = E′} fr sc pt sl nc bs bhβ fl fe ce bhk sd af ao _ ni) hf w lo =
    let (Cr′ , fr′ , env , ef , d) = rc {s = connS k s b} fr hf′ w lo
        (envb , efb) = benv env ef
    in Cr′ , f-src fr′ sc pt sl nc (shift bs w envb efb lob) (behind-bef bhβ (few bs envb efb (lo-p lob)))
                 (Shifted.flags-sh {C} {p} w (λ _ → fbd (proj₂ (run hf env ef))) (λ _ → bound bs envb (lo-p lob))
                   (λ {q} e → ≮-after q p (lo (plug-in c (k-own (own-bld k {o = s} {b = b} (oo e)))))) fl)
                 fe ce (bfr (proj₁ (run hf env ef))) (Shifted.subd′ {C} {p} w sd) af ao (λ na → call-sh {k = k} {o = s} {b = b} (ao na) loc) ni
       , env , ef , d
    where
      loc : LoP (connS k s b) p
      loc = lo-p (λ ki → lo (plug-in c ki))
      lob : Lo b (at p)
      lob ki = lo (plug-in c (k-kid (k-body ki)))
      fbd : Bnd C p E → Bnd C p (Frozen k)
      fbd bd (x , v , ow) = let (y , v′) = from (alike fe) (x , v) in bd (y , v′ , ow)
      bfr : Lag C p E → Behind (bef p) (Frozen k)
      bfr lg = behind-bef bhk (lag-≈ fe lg)
      benv : Env (full (scopeOf c)) C p → EnvL (full (scopeOf c)) C p → _
      benv env ef = bind-env {k = k} sc (fbd (proj₂ (run hf env ef))) (bfr (proj₁ (run hf env ef))) env ef
      hf′ : HR C p (scopeOf c) E′
      hf′ = hr λ env ef →
        lag-≈ (proj₁ ce) (lag-at (λ r → _ , proj₁ r) (conn-lag {k = k} (few bs (proj₁ (benv env ef)) (proj₂ (benv env ef)) (lo-p lob)) (bfr (proj₁ (run hf env ef))))) ,
        conn-fb {C = C} sc (λ _ _ → bound bs (proj₁ (benv env ef)) (lo-p lob)) (λ _ → fbd (proj₂ (run hf env ef))) fl env ce
  rc {C = C} {c = Machine.inBody k o c} {s = s} {p} (f-body {E′ = E′} fr sc pt sl sr bhE fl ce) hf w lo =
    let (Cr′ , fr′ , env , ef , d) = rc {s = connS k o s} fr hf′ w lo
        (envb , efb , sb , bf) = body-env {b = s} sc sr env ef (lo-p loc)
    in Cr′ , f-body fr′ sc pt sl (src-sh′ {b = s} w sc sr env ef loc) (behind-bef bhE (proj₁ (run hf envb efb)))
                 (Shifted.flags-sh {C} {p} w (λ _ → sb) (λ _ → proj₂ (run hf envb efb))
                   (λ {q} e → ≮-after q p (lo (plug-in c (k-own (own-bld k {o = o} {b = s} (oo e)))))) fl) ce
       , envb , efb , d
    where
      loc : Lo (connS k o s) (at p)
      loc ki = lo (plug-in c ki)
      hf′ : HR C p (scopeOf c) E′
      hf′ = hr λ env ef →
        let (envb , efb , sb , bf) = body-env {b = s} sc sr env ef (lo-p loc)
        in lag-≈ (proj₁ ce) (lag-at (λ r → _ , proj₁ r) (conn-lag {k = k} (proj₁ (run hf envb efb)) bf)) ,
           conn-fb {C = C} sc (λ _ _ → proj₂ (run hf envb efb)) (λ _ → sb) fl env ce
  rc {Cr = Cr} {C = Ci} {c = Machine.inSrc k b c} {s = s} {p} (f-isle u hk ub le na nc bh sd ss ao _ bu nr ni) hf w lo =
    Cr , f-isle u hk ub (burst-dn {C = Ci} {C′ = bef p} {k = k} (λ o → owes-≼ Ci w o) le) na nc (behind-bef bh (proj₁ (run hf env ef)))
                (Shifted.subd′ {Ci} {p} w sd) ss ao (call-sh {k = k} {o = s} {b = b} ao loc) bu nr ni
       , env , ef , ≃-refl
    where
      loc : LoP (connS k s b) p
      loc = lo-p (λ ki → lo (plug-in c ki))
      ie = subd-env {k = k} sd (att-slot {k = k} {p = p} ao (λ be → loc (k-own (body-key k {o = s} {b = b} be)))
                                                           (λ ae → loc (k-own (own-bld k {o = s} {b = b} (os ae)))))
      env = proj₁ ie
      ef  = proj₂ ie
  rc (f-took _ _ _ _ _ _ _ _ _ _) () w lo
  rc (f-srcc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) () w lo
  rc (f-srcp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) () w lo
  rc (d-map _ _) () w lo
  rc (d-scan _ _) () w lo
  rc (d-cut _ _) () w lo
  rc (d-ln _ _) () w lo
  rc (d-take _ _) () w lo
  rc (d-outer _ _ _ _) () w lo
  rc (d-lanes _ _ _ _ _ _ _) () w lo
  rc (d-src _ _ _ _ _ _ _) () w lo
  rc (d-body _ _ _ _) () w lo
  rc (f-islec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) () w lo
  rc (f-islep _ _ _ _ _ _ _ _ _ _ _ _ _ _) () w lo

  -- The frames, and the hole itself by `shift`, its keys being the tree's.
  fr-shift : ∀ {Cr C Γ A} {c : Ctx R Γ A} {s : St Γ A} {Rg E p}
           → Fr Rt Cr C Rg c owes E → Sync (scopeOf c) Rg C s E → Owes C p → Lo (plug c s) (at p)
           → Σ Cur λ Cr′ → Fr Rt Cr′ (bef p) Rg c owes E × Sync (scopeOf c) Rg (bef p) s E × Due Cr Rt ≃ Due Cr′ Rt
  fr-shift {c = c} {s = s} fr sy w lo =
    let (Cr′ , fr′ , env , ef , d) = rc {s = s} fr (hr λ env ef → few sy env ef (lo-p los) , bound sy env (lo-p los)) w lo
    in Cr′ , fr′ , shift sy w env ef los , d
    where
      los : Lo s (at _)
      los ki = lo (plug-in c ki)
