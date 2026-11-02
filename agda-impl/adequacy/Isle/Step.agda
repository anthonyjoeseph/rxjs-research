{-# OPTIONS --guardedness #-}

-- THE INVARIANT ALONG A RUN: every step keeps `Ig`, so every conf a run
-- reaches has its search's path clear.  The only step that owes a new
-- attach is a body's run, and the floor keys that attach below every
-- mark of the tree.
module adequacy.Isle.Step where

open import Data.Bool using (true; false; not; _∨_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; _ʳ++_; reverse)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (_<ᵇ_; _≡ᵇ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Events using (Pos; ix; emit; stall; close)
open import operation.PureObservable using (PureObs; module Machine; module Driver; play; ending) renaming (over to overT)
open Machine using (Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    CS; cs; attAt; free; cpAt; cutAt; overAt; Ev; nx; cp; Conf; ⟨_,_,_,_⟩; plug; load; subscribing; absorbed; rising;
                    cut; killAll; unsubIf; ended; closed; closedUp; alive; own; rise; run; begin; start; dequeue; admit;
                    search; found; Stepped; moved; starting; turn; quiet; gone; leaf)
open import operation.Key using (at; after; at-after-≮)
open import adequacy.Least using (k-kid; k-body; Lo)
open import adequacy.Floor.Keys using (plug-in; own-cls; ob; mem-self; mem-swap; unsubIf-in)
open import adequacy.Stamped using (stamped; plug-ok; pend-focus)
open import adequacy.Found using (Marked; ofK; attK; conK; joinK; leafK; stopK; cutK; found-least; found-mark; found-plug)
open import adequacy.Path using (Path; []; tau; val; _▸_)
open import adequacy.Apart.Floor using (floor)
open import adequacy.Cursor using (Clear)
open import adequacy.Isle using (⊤₁; tt₁; AttK; a-here; a-src; a-body; a-map; a-scan; a-cut; a-ln; a-take; a-outer; a-lane; NoAttB; att-key;
                                 AttL; Late; G; GL; ClearA; gl-mem; gl-of; gl-ʳ++; ʳ++-mem; LSub; g-hole; Swap; gd-swap; gd-sub;
                                 Keep; kp-unsubIf; kp-cut; kp-kill; kp-ended; kp-feed; found-clr)

-- The invariant at a conf.
Ig : ∀ {R} → Conf R → Set₁
Ig k = ClearA (Conf.ctx k) × G (plug (Conf.ctx k) (Conf.foc k))

-- Every conf a step can hand back keeps it.
IOK : ∀ {R} → Stepped R → Set₁
IOK (moved k _ _)              = Ig k
IOK (starting x p f)           = ∀ l → Ig (f l)
IOK (turn gone)                = ⊤₁
IOK (turn (leaf b l cl dv st)) = (∀ e l′ b′ p′ → Ig (dv e l′ b′ p′)) × (∀ l′ → Ig (st l′))
IOK quiet                      = ⊤₁

------------------------------------------------------------------------
-- A joiner's lanes

flat-ig : ∀ {R Γ A B} (c : Ctx R Γ B) {op} {f : A → PureObs Γ B} {ω d n q d′ n′ q′} {o : St Γ A} {ls ls′}
        → ClearA c → G (plug c (flatS op f ω d n q o ls)) → GL ls′ → LSub ls′ ls → G (plug c (flatS op f ω d′ n′ q′ o ls′))
flat-ig c ca g gl sub = gd-sub c ca g (proj₁ (g-hole c g) , gl)
  λ { (a-outer a) → a-outer a ; (a-lane m a) → let (w , m′ , a′) = sub m a in a-lane m′ a′ }

-- The joiner fine whatever its counters.
FG : ∀ {R Γ A B} → Ctx R Γ B → FlatOp → (A → PureObs Γ B) → PureObs Γ A × Pos → St Γ A → List (St Γ B) → Set₁
FG c op f ω o ls = ∀ {d n q} → G (plug c (flatS op f ω d n q o ls))

lsub-rev : ∀ {Γ B} (ls : List (St Γ B)) {z y} → z ∈ reverse ls → AttK z y → Σ _ λ w → w ∈ ls × AttK w y
lsub-rev ls m a with ʳ++-mem ls m
... | inj₁ m′ = _ , m′ , a
... | inj₂ ()

new-lsub : ∀ {Γ B} (ls : List (St Γ B)) {z} → NoAttB z → LSub (reverse ls ʳ++ z ∷ []) ls
new-lsub ls nz m a with ʳ++-mem (reverse ls) m
... | inj₁ m′          = lsub-rev ls m′ a
... | inj₂ (here refl) = ⊥-elim (nz a)
... | inj₂ (there ())

start-ig : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → PureObs Γ B) ω d n q o ls a p → ClearA c → FG c op f ω o ls → GL ls
         → Ig (start c op f ω d n q o ls a p)
start-ig c op f ω d n q o ls a p ca fg gl with closed c
... | true  = ca , fg
... | false = ca , flat-ig c ca (fg {d} {n} {q}) (gl-ʳ++ (reverse ls) (gl-ʳ++ ls gl tt₁) (tt₁ , tt₁))
                     (new-lsub ls λ { (a-ln (a-cut ())) })

dequeue-ig : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → PureObs Γ B) ω d n q o ls p → ClearA c → FG c op f ω o ls → GL ls
           → Ig (dequeue c op f ω d n q o ls p)
dequeue-ig c op f ω d n []      o ls p ca fg gl = ca , fg
dequeue-ig c op f ω d n (a ∷ q) o ls p ca fg gl = start-ig c op f ω d n q o ls a p ca fg gl

admit-ig : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → PureObs Γ B) ω d n q o ls a p → ClearA c → FG c op f ω o ls → GL ls
         → IOK (admit c op f ω d n q o ls a p)
admit-ig c (mergeᶠ nothing)  f ω d n q o ls a p ca fg gl = start-ig c _ f ω d n q o ls a p ca fg gl
admit-ig c (mergeᶠ (just m)) f ω d n q o ls a p ca fg gl with n <ᵇ m
... | true  = start-ig c _ f ω d n q o ls a p ca fg gl
... | false = ca , fg
admit-ig c switchᶠ           f ω d n q o ls a p ca fg gl with killAll ls | kp-kill ls gl
... | ls′ , t | gl′ , sub = start-ig c switchᶠ f ω d 0 q o ls′ a p ca (λ {d′ n′ q′} → flat-ig c ca (fg {d′} {n′} {q′}) gl′ sub) gl′
admit-ig c exhaustᶠ          f ω d n q o ls a p ca fg gl with n ≡ᵇ 0
... | true  = start-ig c _ f ω d n q o ls a p ca fg gl
... | false = ca , fg

------------------------------------------------------------------------
-- A rise

take-ig : ∀ {R Γ A} (c : Ctx R Γ A) {i q w w′} {s : St Γ A} → ClearA c → G (plug c (takeS i q w s)) → G (plug c (takeS i q w′ s))
take-ig c ca g = gd-sub c ca g (g-hole c g) λ { (a-take a) → a-take a }

-- A source's value fed to its body, which owes no attach.
src-ig : ∀ {R Γ X B} (c : Ctx R Γ B) (k k′ : CS Γ X) {s : St Γ X} {b b′ : St (X ∷ Γ) B} → ClearA c → G (plug c (connS k s b))
       → (AttL k → AttL k′) → (∀ {y} → CS.attSrc k′ ≡ just y → CS.attSrc k ≡ just y) → G b′ × NoAttB b′ → G (plug c (connS k′ s b′))
src-ig c k k′ {s} {b} {b′} ca g fa fe (gb′ , nb′) = gd-sub c ca g gx sub
  where
    gh = g-hole c g
    gx : G (connS k′ s b′)
    gx = fa (proj₁ gh) , (λ {_} a → ⊥-elim (nb′ a)) , proj₁ (proj₂ (proj₂ gh)) , gb′
    sub : ∀ {y} → AttK (connS k′ s b′) y → AttK (connS k s b) y
    sub (a-here e) = a-here (fe e)
    sub (a-src a)  = a-src a
    sub (a-body a) = ⊥-elim (nb′ a)

rise-ig : ∀ {R Γ A} (c : Ctx R Γ A) s (e : Ev A) p → ClearA c → G (plug c s) → IOK (rise c s e p)
rise-ig top            s e      p ca g = tt₁ , g
rise-ig (inMap f c)    s e      p ca g = ca , g
rise-ig (inScan f z c) s (nx a) p ca g = ca , gd-sub c ca g (g-hole c g) λ { (a-scan a′) → a-scan a′ }
rise-ig (inScan f z c) s cp     p ca g = ca , g
rise-ig (inCut l a c)  s e      p ca g = ca , g
rise-ig (inLn b c)     s e      p ca g = ca , g
rise-ig (inTake i q free c) s (nx a) p ca g with q a | i
... | true  | _     = ca , g
... | false | true  = ca , take-ig c ca g
... | false | false = ca , take-ig c ca g
rise-ig (inTake i q free c)       s cp p ca g = ca , g
rise-ig (inTake i q (cpAt r) c)   s e  p ca g = ca , g
rise-ig (inTake i q (cutAt r) c)  s e  p ca g = ca , g
rise-ig (inTake i q (overAt r) c) s e  p ca g = ca , g
rise-ig (inOuter op f ω d n q ls c) o (nx a) p ca g =
  admit-ig c op f ω d n q o ls a p ca (λ {d′ n′ q′} → flat-ig c ca g (proj₂ (g-hole c g)) (λ m a′ → _ , m , a′)) (proj₂ (g-hole c g))
rise-ig (inOuter op f ω d n q ls c) o cp     p ca g = ca , flat-ig c ca g (proj₂ (g-hole c g)) (λ m a′ → _ , m , a′)
rise-ig (inLanes op f ω d n q o pre post c) s (nx b) p ca g with alive s
... | true  = ca , g
... | false = ca , g
rise-ig (inLanes op f ω d n q o pre post c) s cp     p ca g with alive s
... | false = ca , g
... | true  = dequeue-ig c op f ω d _ q o (pre ʳ++ ended s ∷ post) p ca (λ {d′ n′ q′} → flat-ig c ca g gl sub) gl
  where
    gh = g-hole c g
    ke = kp-ended s (g-hole (inLanes op f ω d n q o pre post c) g)
    gl : GL (pre ʳ++ ended s ∷ post)
    gl = gl-of _ λ m → lane m
      where
        lane : ∀ {z} → z ∈ pre ʳ++ ended s ∷ post → G z
        lane m with mem-swap pre {s = s} m
        ... | inj₁ refl = proj₁ ke
        ... | inj₂ m′   = gl-mem (proj₂ gh) m′
    sub : LSub (pre ʳ++ ended s ∷ post) (pre ʳ++ s ∷ post)
    sub m a with mem-swap pre {s = s} m
    ... | inj₁ refl = s , mem-self pre , proj₂ ke a
    ... | inj₂ m′   = _ , m′ , a
rise-ig (inSrc k b c) s (nx a) p (nb , ca) g =
  ca , src-ig c k k ca g (λ al → al) (λ e → e) (kp-feed (here refl) p (nx a) b nb (proj₂ (proj₂ (proj₂ (g-hole c g)))))
rise-ig (inSrc (cs cl true sa ba as ow cx ea sr sc) b c) s cp p (nb , ca) g =
  ca , src-ig c _ _ ca g (λ al → al) (λ e → e) (kp-feed (here refl) p cp b nb (proj₂ (proj₂ (proj₂ (g-hole c g)))))
rise-ig (inSrc (cs cl false sa ba as ow cx ea sr sc) b c) s cp p (nb , ca) g =
  ca , src-ig c _ _ ca g (λ al → al) (λ e → e) (kp-feed (here refl) p cp b nb (proj₂ (proj₂ (proj₂ (g-hole c g)))))
rise-ig (inBody (cs cl true sa ba as ow cx ea sr sc) o c)  s (nx b) p ca g = ca , g
rise-ig (inBody (cs cl false sa ba as ow cx ea sr sc) o c) s (nx b) p ca g = ca , g
rise-ig (inBody (cs cl true sa ba as ow cx ea sr sc) o c)  s cp p ca g =
  ca , gd-sub c ca g (g-hole c g) λ { (a-here e) → a-here e ; (a-src a) → a-src a ; (a-body a) → a-body a }
rise-ig (inBody (cs cl false sa ba as ow cx ea sr sc) o c) s cp p ca g = ca , g

------------------------------------------------------------------------
-- A subscription begun

begin-ig : ∀ {R Γ A} (c : Ctx R Γ A) (o : PureObs Γ A) p {q} → ClearA c → G (plug c (pend o q)) → IOK (begin c o p)
begin-ig c (cold x)          p ca g = λ l → ca , gd-sub c ca g tt₁ (λ ())
begin-ig c empty             p ca g = ca , gd-sub c ca g tt₁ (λ ())
begin-ig c (of xs)           p ca g = ca , gd-sub c ca g tt₁ (λ ())
begin-ig c (map f s)         p ca g = ca , gd-sub c ca g tt₁ λ { (a-map ()) }
begin-ig c (scan f z s)      p ca g = ca , gd-sub c ca g tt₁ λ { (a-scan ()) }
begin-ig c (takeWhile i q s) p ca g = ca , gd-sub c ca g tt₁ λ { (a-take (a-cut ())) }
begin-ig c (flatMap op f s)  p ca g = ca , gd-sub c ca g (tt₁ , tt₁) λ { (a-outer (a-cut ())) ; (a-lane () _) }
begin-ig c (connect s b)     p ca g =
  ca , gd-sub c ca g (inj₂ (inj₁ (p , refl)) , (λ {_} ()) , tt₁ , tt₁) λ { (a-here ()) ; (a-src ()) ; (a-body ()) }
begin-ig c (connected x)     p ca g with closedUp c x
... | true  = ca , gd-sub c ca g tt₁ (λ ())
... | false = ca , gd-sub c ca g tt₁ (λ ())
begin-ig c (defer l)         p ca g = ca , gd-sub c ca g tt₁ (λ ())

------------------------------------------------------------------------
-- A mark run

-- A connect's source torn down, or attached.
kc : ∀ {Γ X B} x (k k′ : CS Γ X) (o : St Γ X) (b : St (X ∷ Γ) B) → (AttL k → AttL k′) → (∀ {κ} → Late k κ → Late k′ κ)
   → (∀ {y} → CS.attSrc k′ ≡ just y → CS.attSrc k ≡ just y) → G (connS k o b) → Keep (connS k o b) (connS k′ (proj₁ (unsubIf x o)) b)
kc x k k′ o b fa fl fe (al , up , go , gb) =
  (fa al , (λ {y} a → (λ {_} ki → proj₁ (up a) (unsubIf-in x o ki)) , fl {after y} (proj₂ (up a))) , proj₁ (kp-unsubIf x o go) , gb) ,
  λ { (a-here e) → a-here (fe e) ; (a-src a) → a-src (proj₂ (kp-unsubIf x o go) a) ; (a-body a) → a-body a }

-- A body run: its source subscribed, owing its attach.  The body owes
-- none, every one keyed after the body's run and no later than it.
body-ig : ∀ {R Γ X B} (c : Ctx R Γ B) {cl sl sa p as ow cx ea sr sc} {o : St Γ X} {b : St (X ∷ Γ) B}
        → Lo (plug c (connS (cs cl sl sa (just p) as ow cx ea sr sc) o b)) (at (p ++ [ ix 1 ])) → ClearA c
        → G (plug c (connS (cs cl sl sa (just p) as ow cx ea sr sc) o b))
        → Lo (plug c (connS (cs cl sl sa nothing (just (p ++ [ ix 1 ])) ow cx ea sr sc) o b)) (after (p ++ [ ix 1 ]))
        → Ig ⟨ inSrc (cs cl sl sa nothing (just (p ++ [ ix 1 ])) ow cx ea sr sc) b c , o , subscribing , p ++ [ ix 1 ] ⟩
body-ig c {p = p} {o = o} {b} lo ca g fl = (nb , ca) , gd-swap c ca g gx sw
  where
    gh = g-hole c g
    up = proj₁ (proj₂ gh)
    nb : NoAttB b
    nb a = at-after-≮ (p ++ [ ix 1 ]) _ (proj₂ (up a) refl) (lo (plug-in c (k-kid (k-body (att-key a)))))
    gx = inj₂ (inj₂ (_ , refl)) , (λ {_} a → (λ {_} ki → proj₁ (up a) ki) , λ ()) , proj₁ (proj₂ (proj₂ gh)) , proj₂ (proj₂ (proj₂ gh))
    sw : Swap c _ _
    sw (a-here refl) = inj₂ fl
    sw (a-src a)     = inj₁ (a-src a)
    sw (a-body a)    = inj₁ (a-body a)

module _ {R} (ρ : PureObs [] R) where
  open Driver R using (took; Step; silent; value; complete; drained)

  PI : Conf R → Set₁
  PI k = ∀ {rs} → Path (load ρ) rs k → Ig k

  ISOK : Stepped R → Set₁
  ISOK (moved k _ _)              = PI k
  ISOK (starting x p f)           = ∀ l → PI (f l)
  ISOK (turn gone)                = ⊤₁
  ISOK (turn (leaf b l cl dv st)) = (∀ e l′ b′ p′ → PI (dv e l′ b′ p′)) × (∀ l′ → PI (st l′))
  ISOK quiet                      = ⊤₁

  lift-ok : (x : Stepped R) → IOK x → ISOK x
  lift-ok (moved k _ _)              h       = λ _ → h
  lift-ok (starting x p f)           h       = λ l _ → h l
  lift-ok (turn gone)                _       = tt₁
  lift-ok (turn (leaf b l cl dv st)) (d , s) = (λ e l′ b′ p′ _ → d e l′ b′ p′) , (λ l′ _ → s l′)
  lift-ok quiet                      _       = tt₁

  run-ig : ∀ {Γ A} (c : Ctx R Γ A) {s m κ} → Marked s m → (m , κ) ∈ own s → Lo (plug c s) κ → ∀ r → ClearA c → G (plug c s)
         → ISOK (run c s m r)
  run-ig c (ofK i p xs) mi lo r ca g with closed c | xs
  ... | true  | _       = λ _ → ca , gd-sub c ca g tt₁ (λ ())
  ... | false | []      = λ _ → ca , gd-sub c ca g tt₁ (λ ())
  ... | false | x ∷ xs′ = λ _ → ca , gd-sub c ca g tt₁ (λ ())
  run-ig c (attK l p s) mi lo r ca g with unsubIf (not l) s | kp-unsubIf (not l) s (g-hole c g)
  ... | s′ , t | gs′ , sub = λ _ → ca , gd-sub c ca g gs′ λ { (a-cut a) → a-cut (sub a) }
  run-ig c (conK (cs cl sl sa (just p) as ow cx ea sr sc) o b _ (inj₁ refl)) mi lo r ca g
    with own-cls (cs cl sl sa (just p) as ow cx ea sr sc) {o} {b} mi
  ... | ob refl = λ pth → body-ig c lo ca g (floor ρ pth tt)
  run-ig c (conK (cs cl sl sa nothing as ow cx ea sr sc) o b _ (inj₁ refl)) mi lo r ca g = λ _ → ca , g
  run-ig c (conK (cs cl sl sa ba (just y) ow cx ea sr sc) o b _ (inj₂ (inj₁ refl))) mi lo r ca g
    with unsubIf (not sl ∨ closed c) o
       | kc (not sl ∨ closed c) (cs cl sl sa ba (just y) ow cx ea sr sc) (cs cl sl true ba nothing ow cx ea sr sc) o b
            (λ _ → inj₁ tt) (λ h → h) (λ ()) (g-hole c g)
  ... | o′ , t | gx , sub = λ _ → ca , gd-sub c ca g gx sub
  run-ig c (conK (cs cl sl sa ba nothing ow cx ea sr sc) o b _ (inj₂ (inj₁ refl))) mi lo r ca g = λ _ → ca , g
  run-ig c (conK (cs cl sl sa ba as (just q) cx ea sr sc) o b _ (inj₂ (inj₂ refl))) mi lo r ca g
    with unsubIf sa o
       | kc sa (cs cl sl sa ba as (just q) cx ea sr sc) (cs cl false sa ba as nothing cx ea sr sc) o b
            (λ al → al) (λ h → h) (λ e → e) (g-hole c g)
  ... | o′ , t | gx , sub = λ _ → ca , gd-sub c ca g gx sub
  run-ig c (conK (cs cl sl sa ba as nothing cx ea sr sc) o b _ (inj₂ (inj₂ refl))) mi lo r ca g = λ _ → ca , g
  run-ig c (joinK j gg x q (nx a) ib) mi lo r ca g = λ _ → ca , gd-sub c ca g tt₁ (λ ())
  run-ig c (joinK j gg x q cp ib)     mi lo r ca g = λ _ → ca , gd-sub c ca g tt₁ (λ ())
  run-ig c (leafK b l) mi lo r ca g =
    (λ e l′ b′ p′ _ → ca , gd-sub c ca g tt₁ (λ ())) , (λ l′ _ → ca , gd-sub c ca g tt₁ (λ ()))
  run-ig c (stopK i q p s) mi lo r ca g = λ _ → ca , take-ig c ca g
  run-ig c (cutK i q p s) mi lo r ca g with cut s | kp-cut s (g-hole c g)
  ... | s′ , t | gs′ , sub = λ _ → ca , gd-sub c ca g gs′ λ { (a-take a) → a-take (sub a) }

  INext : Step → Set₁
  INext (silent t k)    = PI k
  INext (value t p a k) = PI k
  INext (complete p)    = ⊤₁
  INext drained         = ⊤₁

  took-ok : ∀ x → ISOK x → INext (took x)
  took-ok (moved k [] _)               h = h
  took-ok (moved k ((p , nx a) ∷ _) _) h = h
  took-ok (moved k ((p , cp) ∷ _) _)   _ = tt₁
  took-ok (starting x p f)             h = h _
  took-ok (turn gone)                  _ = tt₁
  took-ok (turn (leaf true (ending e) cl dv st))                       (d , s) = d cp overT false e
  took-ok (turn (leaf false l cl dv st))                               (d , s) = s overT
  took-ok (turn (leaf true (play τ u i t fr) true dv st))              (d , s) = s overT
  took-ok (turn (leaf true overT true dv st))                          (d , s) = s overT
  took-ok (turn (leaf true (play τ u i t (emit a k)) false dv st))     (d , s) = d (nx a) _ true _
  took-ok (turn (leaf true (play τ u i t (stall k)) false dv st))      (d , s) = s _
  took-ok (turn (leaf true (play τ u i t (close k)) false dv st))      (d , s) = s _
  took-ok (turn (leaf true overT false dv st))                         (d , s) = s overT
  took-ok quiet                        _ = tt₁

  -- A STEP KEEPS THE INVARIANT.
  isle-step : ∀ {rs k} → Path (load ρ) rs k → Ig k → INext (Driver.step R k)
  isle-step {k = ⟨ c , s , rising e , p ⟩} pth (ca , g) = took-ok (rise c s e p) (lift-ok (rise c s e p) (rise-ig c s e p ca g))
  isle-step {k = ⟨ c , s , subscribing , p ⟩} pth (ca , g) with pend-focus ρ pth
  ... | o′ , refl = took-ok (begin c o′ p) (lift-ok (begin c o′ p) (begin-ig c o′ p ca g))
  isle-step {k = ⟨ c , s , absorbed , p ⟩} pth (ca , g) with stamped ρ pth | search top (plug c s) in fd
  ... | _ | nothing = tt₁
  ... | hc , hs , _ | just (found (_ , _ , c′ , s′) m κ) =
        took-ok (run c′ s′ m p)
          (run-ig c′ (found-mark c s fd) (proj₁ (found-least {t = plug c s} fd))
            (subst (λ t → Lo t κ) (sym (found-plug c s fd)) (proj₂ (found-least {t = plug c s} fd))) p
            (proj₂ (found-clr {t = plug c s} g (plug-ok c hc hs) fd)) (subst G (sym (found-plug c s fd)) g))

  isle-path : ∀ {rs rs′ k k″} → Path (load ρ) rs k → Ig k → Path k rs′ k″ → Ig k″
  isle-path pre ig []          = ig
  isle-path pre ig (tau e pth) = isle-path (pre ▸ tau e []) (subst INext e (isle-step pre ig) (pre ▸ tau e [])) pth
  isle-path pre ig (val e pth) = isle-path (pre ▸ val e []) (subst INext e (isle-step pre ig) (pre ▸ val e [])) pth

-- THE CLEAR PATH: no search a run reaches enters a source whose body
-- holds an isle.
found-clear : ∀ {R} {o : PureObs [] R} {rs Γ′ A′} {c : Ctx R Γ′ A′} {s r Γ A} {c′ : Ctx R Γ A} {s′ m κ}
  → Path (load o) rs ⟨ c , s , absorbed , r ⟩ → search top (plug c s) ≡ just (found (Γ , A , c′ , s′) m κ) → Clear c′
found-clear {o = o} {c = c} {s} pth fd with stamped o pth
... | hc , hs , _ = proj₁ (found-clr {t = plug c s} (proj₂ (isle-path o [] (tt₁ , tt₁) pth)) (plug-ok c hc hs) fd)
