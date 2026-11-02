{-# OPTIONS --guardedness #-}

-- THE PATH TO A FOUND MARK IS CLEAR, BY THE TREE: a connect's source owes
-- its attach only once its subscribe has returned, and a body's own
-- attach owed is keyed before every mark of its connect's source.  So no
-- search reaches into a source whose body still owes an attach, and with
-- every connect attached, pending or owing one, no such source holds an
-- isle.
module adequacy.Isle where

open import Data.Bool using (T; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; _ʳ++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₁)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import denotation.Events using (Pos; ix)
open import operation.Key using (Key; at; after; _<ᴷ_; clash; ≮ᴷ-trans)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; CS; Cand; Out; search; Found; found; plug; seek; kids; lanes; own; ownBest; first; retag; raceT; sourceT; cutT; alive;
                    unsub; cut; killAll; unsubIf; feed; feedL; ended; same?; Ev; attached; attAt;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Least using (KeyIn; k-own; k-kid; k-map; k-scan; k-cut; k-ln; k-take; k-outer; k-lane; k-src; k-body; Lo;
                                   Keeps; mapKp; scanKp; cutKp; takeKp; outerKp; laneKp; Below; keyOf; seek-b)
open import adequacy.Floor.Keys using (ob; os; own-bld; plug-in; mem-self; mem-swap; unsubIf-in)
open import adequacy.Stamped using (StOK; LOK; BodyOK; IsPend; is-pend)
open import adequacy.Cursor using (Settles; NoIsle; NoIsleL; Clear; Pending)

record ⊤₁ : Set₁ where
  constructor tt₁

------------------------------------------------------------------------
-- The attaches a tree owes

-- `y` is where a connect of `s` attaches its source.
data AttK : ∀ {Γ A} → St Γ A → Pos → Set₁ where
  a-here  : ∀ {Γ X B} {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) B} {y} → CS.attSrc k ≡ just y → AttK (connS k o b) y
  a-src   : ∀ {Γ X B} {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) B} {y} → AttK o y → AttK (connS k o b) y
  a-body  : ∀ {Γ X B} {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) B} {y} → AttK b y → AttK (connS k o b) y
  a-map   : ∀ {Γ A B} {f : A → B} {s : St Γ A} {y} → AttK s y → AttK (mapS f s) y
  a-scan  : ∀ {Γ A B} {f : B → A → B} {z} {s : St Γ A} {y} → AttK s y → AttK (scanS f z s) y
  a-cut   : ∀ {Γ A} {l a} {s : St Γ A} {y} → AttK s y → AttK (cutS l a s) y
  a-ln    : ∀ {Γ A} {b} {s : St Γ A} {y} → AttK s y → AttK (lnS b s) y
  a-take  : ∀ {Γ A} {i q w} {s : St Γ A} {y} → AttK s y → AttK (takeS i q w s) y
  a-outer : ∀ {Γ A B} {op f ω d n q} {o : St Γ A} {ls : List (St Γ B)} {y} → AttK o y → AttK (flatS op f ω d n q o ls) y
  a-lane  : ∀ {Γ A B} {op f ω d n q} {o : St Γ A} {ls : List (St Γ B)} {s y} → s ∈ ls → AttK s y → AttK (flatS op f ω d n q o ls) y

NoAttB : ∀ {Γ A} → St Γ A → Set₁
NoAttB s = ∀ {y} → AttK s y → ⊥

-- An attach owed is a mark.
att-key : ∀ {Γ A} {s : St Γ A} {y} → AttK s y → KeyIn s (after y)
att-key (a-here {k = k} {o = o} {b = b} e) = k-own (own-bld k {o} {b} (os e))
att-key (a-src a)          = k-kid (k-src (att-key a))
att-key (a-body a)         = k-kid (k-body (att-key a))
att-key (a-map a)          = k-kid (k-map (att-key a))
att-key (a-scan a)         = k-kid (k-scan (att-key a))
att-key (a-cut a)          = k-kid (k-cut (att-key a))
att-key (a-ln a)           = k-kid (k-ln (att-key a))
att-key (a-take a)         = k-kid (k-take (att-key a))
att-key (a-outer a)        = k-kid (k-outer (att-key a))
att-key (a-lane m a)       = k-kid (k-lane m (att-key a))

------------------------------------------------------------------------
-- THE INVARIANT

-- A connect's source attached, pending its body's run, or owing its
-- attach.
AttL : ∀ {Γ X} → CS Γ X → Set
AttL k = T (CS.srcAtt k) ⊎ Σ Pos (λ p → CS.bodyAt k ≡ just p) ⊎ Σ Pos (λ y → CS.attSrc k ≡ just y)

-- A body yet to run is keyed no earlier than `κ`.
Late : ∀ {Γ X} → CS Γ X → Key → Set
Late k κ = ∀ {p} → CS.bodyAt k ≡ just p → at (p ++ [ ix 1 ]) <ᴷ κ ≡ false

-- Every attach the body owes keyed no later than any mark of the source,
-- or than the body's own run.
Up : ∀ {Γ X B} → CS Γ X → St Γ X → St (X ∷ Γ) B → Set₁
Up k o b = ∀ {y} → AttK b y → Lo o (after y) × Late k (after y)

mutual
  G : ∀ {Γ A} → St Γ A → Set₁
  G (mapS _ s)                = G s
  G (scanS _ _ s)             = G s
  G (cutS _ _ s)              = G s
  G (lnS _ s)                 = G s
  G (takeS _ _ _ s)           = G s
  G (flatS _ _ _ _ _ _ o ls)  = G o × GL ls
  G (connS k o b)             = AttL k × Up k o b × G o × G b
  G _                         = ⊤₁

  GL : ∀ {Γ A} → List (St Γ A) → Set₁
  GL []       = ⊤₁
  GL (s ∷ ls) = G s × GL ls

-- The path enters no source whose body owes an attach.
ClearA : ∀ {R Γ A} → Ctx R Γ A → Set₁
ClearA top                           = ⊤₁
ClearA (inMap _ c)                   = ClearA c
ClearA (inScan _ _ c)                = ClearA c
ClearA (inCut _ _ c)                 = ClearA c
ClearA (inLn _ c)                    = ClearA c
ClearA (inTake _ _ _ c)              = ClearA c
ClearA (inOuter _ _ _ _ _ _ _ c)     = ClearA c
ClearA (inLanes _ _ _ _ _ _ _ _ _ c) = ClearA c
ClearA (inSrc _ b c)                 = NoAttB b × ClearA c
ClearA (inBody _ _ c)                = ClearA c

Clr : ∀ {R Γ A} → Ctx R Γ A → Set₁
Clr c = Clear c × ClearA c

------------------------------------------------------------------------
-- Lanes

gl-mem : ∀ {Γ A} {ls : List (St Γ A)} {z} → GL ls → z ∈ ls → G z
gl-mem (g , _)  (here refl) = g
gl-mem (_ , gs) (there m)   = gl-mem gs m

gl-of : ∀ {Γ A} (ls : List (St Γ A)) → (∀ {z} → z ∈ ls → G z) → GL ls
gl-of []       h = tt₁
gl-of (s ∷ ls) h = h (here refl) , gl-of ls (λ m → h (there m))

gl-ʳ++ : ∀ {Γ A} (pre : List (St Γ A)) {post} → GL pre → GL post → GL (pre ʳ++ post)
gl-ʳ++ []        _        hp = hp
gl-ʳ++ (s ∷ pre) (g , gs) hp = gl-ʳ++ pre gs (g , hp)

ʳ++-mem : ∀ {a} {S : Set a} (pre : List S) {post z} → z ∈ pre ʳ++ post → z ∈ pre ⊎ z ∈ post
ʳ++-mem []        m = inj₂ m
ʳ++-mem (s ∷ pre) m with ʳ++-mem pre m
... | inj₁ m′         = inj₁ (there m′)
... | inj₂ (here e)   = inj₁ (here e)
... | inj₂ (there m′) = inj₂ m′

-- Lanes owing no attach the old ones did not.
LSub : ∀ {Γ A} → List (St Γ A) → List (St Γ A) → Set₁
LSub ls′ ls = ∀ {z y} → z ∈ ls′ → AttK z y → Σ _ λ w → w ∈ ls × AttK w y

------------------------------------------------------------------------
-- A subtree swapped

g-hole : ∀ {R Γ A} (c : Ctx R Γ A) {s} → G (plug c s) → G s
g-hole top                               g = g
g-hole (inMap f c)                       g = g-hole c g
g-hole (inScan f z c)                    g = g-hole c g
g-hole (inCut l a c)                     g = g-hole c g
g-hole (inLn b c)                        g = g-hole c g
g-hole (inTake i q w c)                  g = g-hole c g
g-hole (inOuter op f ω d n q ls c)       g = proj₁ (g-hole c g)
g-hole (inLanes op f ω d n q o pre post c) g = gl-mem (proj₂ (g-hole c g)) (mem-self pre)
g-hole (inSrc k b c)                     g = proj₁ (proj₂ (proj₂ (g-hole c g)))
g-hole (inBody k o c)                    g = proj₂ (proj₂ (proj₂ (g-hole c g)))

-- Each new attach under the hole an old one, or keyed no later than any
-- mark of the tree.
Swap : ∀ {R Γ A} → Ctx R Γ A → St Γ A → St Γ A → Set₁
Swap c x x′ = ∀ {y} → AttK x′ y → AttK x y ⊎ Lo (plug c x′) (after y)

gd-swap : ∀ {R Γ A} (c : Ctx R Γ A) {x x′ : St Γ A} → ClearA c → G (plug c x) → G x′ → Swap c x x′ → G (plug c x′)
gd-swap top                ca g gx sw = gx
gd-swap (inMap f c)        ca g gx sw = gd-swap c ca g gx λ { (a-map a) → map₁ a-map (sw a) }
gd-swap (inScan f z c)     ca g gx sw = gd-swap c ca g gx λ { (a-scan a) → map₁ a-scan (sw a) }
gd-swap (inCut l a c)      ca g gx sw = gd-swap c ca g gx λ { (a-cut a′) → map₁ a-cut (sw a′) }
gd-swap (inLn b c)         ca g gx sw = gd-swap c ca g gx λ { (a-ln a) → map₁ a-ln (sw a) }
gd-swap (inTake i q w c)   ca g gx sw = gd-swap c ca g gx λ { (a-take a) → map₁ a-take (sw a) }
gd-swap (inOuter op f ω d n q ls c) ca g gx sw =
  gd-swap c ca g (gx , proj₂ (g-hole c g)) λ { (a-outer a) → map₁ a-outer (sw a) ; (a-lane m a) → inj₁ (a-lane m a) }
gd-swap (inLanes op f ω d n q o pre post c) {x} {x′} ca g gx sw = gd-swap c ca g (proj₁ gh , gl-of _ gl′) sw′
  where
    gh = g-hole c g
    gl′ : ∀ {z} → z ∈ pre ʳ++ x′ ∷ post → G z
    gl′ m with mem-swap pre {s = x} m
    ... | inj₁ refl = gx
    ... | inj₂ m′   = gl-mem (proj₂ gh) m′
    sw′ : Swap c (flatS op f ω d n q o (pre ʳ++ x ∷ post)) (flatS op f ω d n q o (pre ʳ++ x′ ∷ post))
    sw′ (a-outer a) = inj₁ (a-outer a)
    sw′ (a-lane m a) with mem-swap pre {s = x} m
    ... | inj₁ refl = map₁ (a-lane (mem-self pre)) (sw a)
    ... | inj₂ m′   = inj₁ (a-lane m′ a)
gd-swap (inSrc k b c) {x} {x′} (nb , ca) g gx sw = gd-swap c ca g (proj₁ gh , (λ {_} a → ⊥-elim (nb a)) , gx , proj₂ (proj₂ (proj₂ gh))) sw′
  where
    gh = g-hole c g
    sw′ : Swap c (connS k x b) (connS k x′ b)
    sw′ (a-here e) = inj₁ (a-here e)
    sw′ (a-src a)  = map₁ a-src (sw a)
    sw′ (a-body a) = inj₁ (a-body a)
gd-swap (inBody k o c) {x} {x′} ca g gx sw = gd-swap c ca g (proj₁ gh , (λ {y} → up′ {y}) , proj₁ (proj₂ (proj₂ gh)) , gx) sw′
  where
    gh = g-hole c g
    up′ : Up k o x′
    up′ a with sw a
    ... | inj₁ a′ = proj₁ (proj₂ gh) a′
    ... | inj₂ lo = (λ ki → lo (plug-in c (k-kid (k-src ki)))) , (λ e → lo (plug-in c (k-own (own-bld k {o} {x′} (ob e)))))
    sw′ : Swap c (connS k o x) (connS k o x′)
    sw′ (a-here e) = inj₁ (a-here e)
    sw′ (a-src a)  = inj₁ (a-src a)
    sw′ (a-body a) = map₁ a-body (sw a)

gd-sub : ∀ {R Γ A} (c : Ctx R Γ A) {x x′ : St Γ A} → ClearA c → G (plug c x) → G x′ → (∀ {y} → AttK x′ y → AttK x y) → G (plug c x′)
gd-sub c ca g gx sub = gd-swap c ca g gx (λ a → inj₁ (sub a))

------------------------------------------------------------------------
-- Teardown, feed and end keep the invariant

-- A node replaced, its invariant kept, owing no attach the old did not.
Keep : ∀ {Γ A} → St Γ A → St Γ A → Set₁
Keep s s′ = G s′ × (∀ {y} → AttK s′ y → AttK s y)

kk : ∀ {Γ A} {l : St Γ A} {ls ls′} → G l → GL ls′ × LSub ls′ ls → GL (l ∷ ls′) × LSub (l ∷ ls′) (l ∷ ls)
kk g (gl , sub) = (g , gl) , λ { (here refl) a → _ , here refl , a ; (there m) a → let (w , m′ , a′) = sub m a in w , there m′ , a′ }

mutual
  kp-unsub : ∀ {Γ A} (s : St Γ A) → G s → Keep s (proj₁ (unsub s))
  kp-unsub (coldS true l)  g = tt₁ , λ ()
  kp-unsub (coldS false l) g = tt₁ , λ ()
  kp-unsub (mapS f s)      g = proj₁ (kp-unsub s g) , λ { (a-map a) → a-map (proj₂ (kp-unsub s g) a) }
  kp-unsub (scanS f z s)   g = proj₁ (kp-unsub s g) , λ { (a-scan a) → a-scan (proj₂ (kp-unsub s g) a) }
  kp-unsub (takeS i p w s) g = proj₁ (kp-cut s g) , λ { (a-take a) → a-take (proj₂ (kp-cut s g) a) }
  kp-unsub (flatS op f ω d n q o ls) (go , gl) =
    (proj₁ (kp-cut o go) , proj₁ (kp-kill ls gl)) ,
    λ { (a-outer a) → a-outer (proj₂ (kp-cut o go) a) ; (a-lane m a) → let (w , m′ , a′) = proj₂ (kp-kill ls gl) m a in a-lane m′ a′ }
  kp-unsub (connS k o b) (al , up , go , gb) =
    (al , (λ {y} → up′ {y}) , proj₁ (kp-unsubIf (CS.srcAtt k) o go) , proj₁ (kp-unsub b gb)) ,
    λ { (a-here e) → a-here e ; (a-src a) → a-src (proj₂ (kp-unsubIf (CS.srcAtt k) o go) a) ; (a-body a) → a-body (proj₂ (kp-unsub b gb) a) }
    where
      up′ : Up k (proj₁ (unsubIf (CS.srcAtt k) o)) (proj₁ (unsub b))
      up′ a = (λ ki → proj₁ (up (proj₂ (kp-unsub b gb) a)) (unsubIf-in (CS.srcAtt k) o ki)) , proj₂ (up (proj₂ (kp-unsub b gb) a))
  kp-unsub (joinS j g x ib) _ = tt₁ , λ ()
  kp-unsub (pend o q)       g = g , λ a → a
  kp-unsub (ofS i p xs)     g = g , λ a → a
  kp-unsub doneS            g = g , λ a → a
  kp-unsub (cutS l a s)     g = g , λ a → a
  kp-unsub (lnS b s)        g = g , λ a → a

  kp-cut : ∀ {Γ A} (s : St Γ A) → G s → Keep s (proj₁ (cut s))
  kp-cut (cutS l attached s)  g = proj₁ (kp-unsub s g) , λ { (a-cut a) → a-cut (proj₂ (kp-unsub s g) a) }
  kp-cut (cutS l (attAt p) s) g = g , λ { (a-cut a) → a-cut a }
  kp-cut (pend o q)              g = g , λ a → a
  kp-cut (coldS b l)             g = g , λ a → a
  kp-cut (ofS i p xs)            g = g , λ a → a
  kp-cut doneS                   g = g , λ a → a
  kp-cut (mapS f s)              g = g , λ a → a
  kp-cut (scanS f z s)           g = g , λ a → a
  kp-cut (lnS b s)               g = g , λ a → a
  kp-cut (takeS i q w s)         g = g , λ a → a
  kp-cut (flatS op f ω d n q o ls) g = g , λ a → a
  kp-cut (connS k o b)           g = g , λ a → a
  kp-cut (joinS j g′ x ib)       g = g , λ a → a

  kp-kill : ∀ {Γ B} (ls : List (St Γ B)) → GL ls → GL (proj₁ (killAll ls)) × LSub (proj₁ (killAll ls)) ls
  kp-kill []                (_) = tt₁ , λ ()
  kp-kill (lnS true s ∷ ls) (g , gs) = (proj₁ (kp-cut s g) , proj₁ (kp-kill ls gs)) , sub
    where
      sub : LSub (lnS false (proj₁ (cut s)) ∷ proj₁ (killAll ls)) (lnS true s ∷ ls)
      sub (here refl) (a-ln a) = _ , here refl , a-ln (proj₂ (kp-cut s g) a)
      sub (there m)   a        = let (w , m′ , a′) = proj₂ (kp-kill ls gs) m a in w , there m′ , a′
  kp-kill (lnS false s ∷ ls)             (g , gs) = kk g (kp-kill ls gs)
  kp-kill (pend o q ∷ ls)                (g , gs) = kk g (kp-kill ls gs)
  kp-kill (coldS b l ∷ ls)               (g , gs) = kk g (kp-kill ls gs)
  kp-kill (ofS i p xs ∷ ls)              (g , gs) = kk g (kp-kill ls gs)
  kp-kill (doneS ∷ ls)                   (g , gs) = kk g (kp-kill ls gs)
  kp-kill (mapS f s ∷ ls)                (g , gs) = kk g (kp-kill ls gs)
  kp-kill (scanS f z s ∷ ls)             (g , gs) = kk g (kp-kill ls gs)
  kp-kill (cutS l a s ∷ ls)              (g , gs) = kk g (kp-kill ls gs)
  kp-kill (takeS i q w s ∷ ls)           (g , gs) = kk g (kp-kill ls gs)
  kp-kill (flatS op f ω d n q o ms ∷ ls) (g , gs) = kk g (kp-kill ls gs)
  kp-kill (connS k o b ∷ ls)             (g , gs) = kk g (kp-kill ls gs)
  kp-kill (joinS j g′ x ib ∷ ls)         (g , gs) = kk g (kp-kill ls gs)

  kp-unsubIf : ∀ {Γ A} b (s : St Γ A) → G s → Keep s (proj₁ (unsubIf b s))
  kp-unsubIf true  s g = kp-unsub s g
  kp-unsubIf false s g = g , λ a → a

kp-ended : ∀ {Γ B} (s : St Γ B) → G s → Keep s (ended s)
kp-ended (lnS b (cutS l a s))    g = g , λ { (a-ln (a-cut a′)) → a-ln (a-cut a′) }
kp-ended (lnS b (pend o q))      g = g , λ a → a
kp-ended (lnS b (coldS x l))     g = g , λ a → a
kp-ended (lnS b (ofS i p xs))    g = g , λ a → a
kp-ended (lnS b doneS)           g = g , λ a → a
kp-ended (lnS b (mapS f s))      g = g , λ a → a
kp-ended (lnS b (scanS f z s))   g = g , λ a → a
kp-ended (lnS b (lnS x s))       g = g , λ a → a
kp-ended (lnS b (takeS i q w s)) g = g , λ a → a
kp-ended (lnS b (flatS op f ω d n q o ls)) g = g , λ a → a
kp-ended (lnS b (connS k o x))   g = g , λ a → a
kp-ended (lnS b (joinS j g′ x ib)) g = g , λ a → a
kp-ended (pend o q)              g = g , λ a → a
kp-ended (coldS b l)             g = g , λ a → a
kp-ended (ofS i p xs)            g = g , λ a → a
kp-ended doneS                   g = g , λ a → a
kp-ended (mapS f s)              g = g , λ a → a
kp-ended (scanS f z s)           g = g , λ a → a
kp-ended (cutS l a s)            g = g , λ a′ → a′
kp-ended (takeS i q w s)         g = g , λ a → a
kp-ended (flatS op f ω d n q o ls) g = g , λ a → a
kp-ended (connS k o b)           g = g , λ a → a
kp-ended (joinS j g′ x ib)       g = g , λ a → a

-- A feed into a part owing no attach.
mutual
  kp-feed : ∀ {Γ X A} (i : X ∈ Γ) p (e : Ev X) (s : St Γ A) → NoAttB s → G s → G (feed i p e s) × NoAttB (feed i p e s)
  kp-feed i p e (joinS j true x ib) na g with same? i x
  ... | just refl = tt₁ , λ ()
  ... | nothing   = tt₁ , λ ()
  kp-feed i p e (joinS j false x ib) na g = tt₁ , λ ()
  kp-feed i p e (mapS f s)      na g = proj₁ r , λ { (a-map a) → proj₂ r a }
    where r = kp-feed i p e s (λ a → na (a-map a)) g
  kp-feed i p e (scanS f z s)   na g = proj₁ r , λ { (a-scan a) → proj₂ r a }
    where r = kp-feed i p e s (λ a → na (a-scan a)) g
  kp-feed i p e (cutS l a s)    na g = proj₁ r , λ { (a-cut a′) → proj₂ r a′ }
    where r = kp-feed i p e s (λ a′ → na (a-cut a′)) g
  kp-feed i p e (lnS b s)       na g = proj₁ r , λ { (a-ln a) → proj₂ r a }
    where r = kp-feed i p e s (λ a → na (a-ln a)) g
  kp-feed i p e (takeS v q w s) na g = proj₁ r , λ { (a-take a) → proj₂ r a }
    where r = kp-feed i p e s (λ a → na (a-take a)) g
  kp-feed i p e (flatS op f ω d n q o ls) na (go , gl) = (proj₁ ro , proj₁ rl) , λ { (a-outer a) → proj₂ ro a ; (a-lane m a) → proj₂ rl m a }
    where
      ro = kp-feed i p e o (λ a → na (a-outer a)) go
      rl = kp-feedL i p e ls (λ m a → na (a-lane m a)) gl
  kp-feed i p e (connS k o b) na (al , _ , go , gb) =
    (al , (λ {_} a → ⊥-elim (proj₂ rb a)) , proj₁ ro , proj₁ rb) , λ { (a-here x) → na (a-here x) ; (a-src a) → proj₂ ro a ; (a-body a) → proj₂ rb a }
    where
      ro = kp-feed i p e o (λ a → na (a-src a)) go
      rb = kp-feed (there i) p e b (λ a → na (a-body a)) gb
  kp-feed i p e (pend o q)   na g = g , na
  kp-feed i p e (coldS b l)  na g = g , na
  kp-feed i p e (ofS j q xs) na g = g , na
  kp-feed i p e doneS        na g = g , na

  kp-feedL : ∀ {Γ X A} (i : X ∈ Γ) p (e : Ev X) (ls : List (St Γ A)) → (∀ {z y} → z ∈ ls → AttK z y → ⊥) → GL ls
          → GL (feedL i p e ls) × (∀ {z y} → z ∈ feedL i p e ls → AttK z y → ⊥)
  kp-feedL i p e []       na _        = tt₁ , λ ()
  kp-feedL i p e (s ∷ ls) na (g , gs) = (proj₁ r , proj₁ rs) , λ { (here refl) a → proj₂ r a ; (there m) a → proj₂ rs m a }
    where
      r  = kp-feed i p e s (na (here refl)) g
      rs = kp-feedL i p e ls (λ m → na (there m)) gs

------------------------------------------------------------------------
-- No attach owed, no isle

pending : ∀ {Γ A} (o : St Γ A) {r} → IsPend o r → Pending o
pending o h = is-pend o h Pending (λ _ → tt)

settles : ∀ {Γ X} (k : CS Γ X) (o : St Γ X) → BodyOK (CS.bodyAt k) o → AttL k → (∀ {y} → CS.attSrc k ≡ just y → ⊥) → Settles k o
settles k o hbo (inj₁ t)               _  = inj₁ t
settles k o hbo (inj₂ (inj₁ (p , e))) _  = inj₂ (inj₂ (pending o (subst (λ m → BodyOK m o) e hbo)))
settles k o hbo (inj₂ (inj₂ (y , e))) na = ⊥-elim (na e)

mutual
  noatt-noisle : ∀ {Γ A} (s : St Γ A) → StOK s → G s → NoAttB s → NoIsle s
  noatt-noisle (mapS f s)      ok       g na = noatt-noisle s ok g (λ a → na (a-map a))
  noatt-noisle (scanS f z s)   ok       g na = noatt-noisle s ok g (λ a → na (a-scan a))
  noatt-noisle (cutS l a s)    (_ , ok) g na = noatt-noisle s ok g (λ a′ → na (a-cut a′))
  noatt-noisle (lnS b s)       ok       g na = noatt-noisle s ok g (λ a → na (a-ln a))
  noatt-noisle (takeS i q w s) (_ , ok) g na = noatt-noisle s ok g (λ a → na (a-take a))
  noatt-noisle (flatS op f ω d n q o ls) (oko , okl) (go , gl) na =
    noatt-noisle o oko go (λ a → na (a-outer a)) , noatt-noisleL ls okl gl (λ m a → na (a-lane m a))
  noatt-noisle (connS k o b) (_ , ho , hb , hbo) (al , _ , go , gb) na =
    settles k o hbo al (λ e → na (a-here e)) , noatt-noisle o ho go (λ a → na (a-src a)) , noatt-noisle b hb gb (λ a → na (a-body a))
  noatt-noisle (pend o q)       _ _ _ = tt
  noatt-noisle (coldS b l)      _ _ _ = tt
  noatt-noisle (ofS i p xs)     _ _ _ = tt
  noatt-noisle doneS            _ _ _ = tt
  noatt-noisle (joinS j g x ib) _ _ _ = tt

  noatt-noisleL : ∀ {Γ A} (ls : List (St Γ A)) → LOK ls → GL ls → (∀ {z y} → z ∈ ls → AttK z y → ⊥) → NoIsleL ls
  noatt-noisleL []       _          _        _  = tt
  noatt-noisleL (s ∷ ls) (ok , oks) (g , gs) na = noatt-noisle s ok g (na (here refl)) , noatt-noisleL ls oks gs (λ m → na (there m))

------------------------------------------------------------------------
-- THE SEARCH KEEPS TO A CLEAR PATH

ClrF : ∀ {R} → Found R → Set₁
ClrF (found (_ , _ , c , _) _ _) = Clr c

-- A candidate keyed by a mark `K` holds, its path clear if the frames
-- above are.
CLP : ∀ {R A} → (Key → Set₁) → Set₁ → Maybe (Cand R A) → Set₁
CLP K C nothing            = ⊤₁
CLP K C (just (f , h , _)) = K h × (C → ClrF f)

cl-map : ∀ {R A} {K K′ : Key → Set₁} {C C′ : Set₁} (x : Maybe (Cand R A)) → (∀ {h} → K h → K′ h) → (C′ → C) → CLP K C x → CLP K′ C′ x
cl-map nothing  kf cf _        = tt₁
cl-map (just _) kf cf (kh , f) = kf kh , λ c → f (cf c)

cl-first : ∀ {R A} {K : Key → Set₁} {C : Set₁} (x y : Maybe (Cand R A)) → CLP K C x → CLP K C y → CLP K C (first x y)
cl-first nothing            y                     _  cy = cy
cl-first (just _)           nothing               cx _  = cx
cl-first (just (f , h , o)) (just (g , h′ , o′)) cx cy with h′ <ᴷ h
... | true  = cy
... | false = cx

cl-retag : ∀ {R A B} {K : Key → Set₁} {C : Set₁} {t : Key → Out A → Key × Out B} → Keeps t → (x : Maybe (Cand R A))
         → CLP K C x → CLP K C (retag t x)
cl-retag kp nothing            _        = tt₁
cl-retag {K = K} kp (just (f , h , o)) (kh , cf) = subst K (sym (kp h o)) kh , cf

cl-race : ∀ {R A B} {K : Key → Set₁} {C : Set₁} d n (q : List A) (x : Maybe (Cand R A)) (y : Maybe (Cand R B))
        → CLP K C x → CLP K C y → CLP K C (raceT d n q x y)
cl-race d n q nothing            nothing              _         _         = tt₁
cl-race {K = K} d n q nothing (just (g , k , o′)) _ (kh , cf) = subst K (sym (laneKp d n q k o′)) kh , cf
cl-race {K = K} d n q (just (f , h , o)) nothing (kh , cf) _ = subst K (sym (outerKp n q h o)) kh , cf
cl-race {K = K} d n q (just (f , h , o)) (just (g , k , o′)) (kh , cf) (kh′ , cf′) with h <ᴷ k
... | true  = subst K (sym (outerKp n q h o)) kh , cf
... | false = subst K (sym (laneKp d n q k o′)) kh′ , cf′

-- The source only strictly before every mark of the body: then the body
-- owes no attach.
cl-source : ∀ {R Γ X B} (c : Ctx R Γ B) (k : CS Γ X) (o : St Γ X) (b : St (X ∷ Γ) B) (x : Maybe (Cand R X)) (y : Maybe (Cand R B))
          → CLP (KeyIn o) (Clr (inSrc k b c)) x → CLP (KeyIn b) (Clr c) y → (∀ {κ} → KeyIn b κ → Below (keyOf y) κ)
          → (∀ {h} → KeyIn o h → (∀ {κ} → KeyIn b κ → h <ᴷ κ ≡ false → ⊥) → Clr c → Clr (inSrc k b c))
          → CLP (KeyIn (connS k o b)) (Clr c) (sourceT x y)
cl-source c k o b nothing y _ cy _ _ = cl-map y (λ ki → k-kid (k-body ki)) (λ cc → cc) cy
cl-source c k o b (just (f , h , _)) nothing (kh , cf) _ bel W = k-kid (k-src kh) , λ cc → cf (W kh (λ kb _ → bel kb) cc)
cl-source c k o b (just (f , h , _)) (just (g , k′ , _)) (kh , cf) cy bel W with h <ᴷ k′ in e
... | true  = k-kid (k-src kh) , λ cc → cf (W kh (λ {κ} kb hk → clash e (≮ᴷ-trans h κ k′ hk (bel kb))) cc)
... | false = k-kid (k-body (proj₁ cy)) , proj₂ cy

own-clear : ∀ {R Γ A} (c : Ctx R Γ A) s ms → (∀ {mk} → mk ∈ ms → mk ∈ own s) → CLP (KeyIn s) (Clr c) (ownBest c s ms)
own-clear c s []             _   = tt₁
own-clear c s ((m , k) ∷ ms) sub =
  cl-first (just _) (ownBest c s ms) (k-own (sub (here refl)) , λ cc → cc) (own-clear c s ms (λ mm → sub (there mm)))

mutual
  seek-clear : ∀ {R Γ A} (c : Ctx R Γ A) s → G s → StOK s → CLP (KeyIn s) (Clr c) (seek c s)
  seek-clear c s g ok = cl-first (ownBest c s (own s)) (kids c s) (own-clear c s (own s) (λ m → m)) (kids-clear c s g ok)

  kids-clear : ∀ {R Γ A} (c : Ctx R Γ A) s → G s → StOK s → CLP (KeyIn s) (Clr c) (kids c s)
  kids-clear c (mapS f s) g ok =
    cl-retag (mapKp f) (seek (inMap f c) s) (cl-map (seek (inMap f c) s) (λ ki → k-kid (k-map ki)) (λ cc → cc) (seek-clear (inMap f c) s g ok))
  kids-clear c (scanS f z s) g ok =
    cl-retag (scanKp f z) (seek (inScan f z c) s) (cl-map (seek (inScan f z c) s) (λ ki → k-kid (k-scan ki)) (λ cc → cc) (seek-clear (inScan f z c) s g ok))
  kids-clear c (cutS l a s) g (_ , ok) =
    cl-retag (cutKp l) (seek (inCut l a c) s) (cl-map (seek (inCut l a c) s) (λ ki → k-kid (k-cut ki)) (λ cc → cc) (seek-clear (inCut l a c) s g ok))
  kids-clear c (lnS b s) g ok =
    cl-map (seek (inLn b c) s) (λ ki → k-kid (k-ln ki)) (λ cc → cc) (seek-clear (inLn b c) s g ok)
  kids-clear c (takeS i q w s) g (_ , ok) =
    cl-retag (takeKp i q w) (seek (inTake i q w c) s) (cl-map (seek (inTake i q w c) s) (λ ki → k-kid (k-take ki)) (λ cc → cc) (seek-clear (inTake i q w c) s g ok))
  kids-clear c (flatS op f ω d n q o ls) (go , gl) (oko , okl) =
    cl-race d n q (seek (inOuter op f ω d n q ls c) o) (lanes c op f ω d n q o [] ls)
      (cl-map (seek (inOuter op f ω d n q ls c) o) (λ ki → k-kid (k-outer ki)) (λ cc → cc) (seek-clear (inOuter op f ω d n q ls c) o go oko))
      (lanes-clear c op f ω d n q o [] ls (λ m → m) gl okl)
  kids-clear c (connS k o b) (al , up , go , gb) (_ , ho , hb , _) =
    cl-source c k o b (seek (inSrc k b c) o) (seek (inBody k o c) b) (seek-clear (inSrc k b c) o go ho) (seek-clear (inBody k o c) b gb hb)
      (seek-b (inBody k o c) b) W
    where
      W : ∀ {h} → KeyIn o h → (∀ {κ} → KeyIn b κ → h <ᴷ κ ≡ false → ⊥) → Clr c → Clr (inSrc k b c)
      W hin far (cl , ca) = (noatt-noisle b hb gb na , cl) , (na , ca)
        where
          na : NoAttB b
          na a = far (att-key a) (proj₁ (up a) hin)
  kids-clear c (pend o q)       _ _ = tt₁
  kids-clear c (coldS b l)      _ _ = tt₁
  kids-clear c (ofS i p xs)     _ _ = tt₁
  kids-clear c doneS            _ _ = tt₁
  kids-clear c (joinS j g x ib) _ _ = tt₁

  lanes-clear : ∀ {R Γ A B} (c : Ctx R Γ B) op f ω d n (q : List A) (o : St Γ A) pre (ls : List (St Γ B)) {L}
              → (∀ {z} → z ∈ ls → z ∈ L) → GL ls → LOK ls → CLP (KeyIn (flatS op f ω d n q o L)) (Clr c) (lanes c op f ω d n q o pre ls)
  lanes-clear c op f ω d n q o pre []         sub _        _          = tt₁
  lanes-clear c op f ω d n q o pre (s ∷ post) sub (g , gs) (ok , oks) =
    cl-first (retag (cutT (alive s)) (seek (inLanes op f ω d n q o pre post c) s)) (lanes c op f ω d n q o (s ∷ pre) post)
      (cl-retag (cutKp (alive s)) (seek (inLanes op f ω d n q o pre post c) s)
        (cl-map (seek (inLanes op f ω d n q o pre post c) s) (λ ki → k-kid (k-lane (sub (here refl)) ki)) (λ cc → cc)
          (seek-clear (inLanes op f ω d n q o pre post c) s g ok)))
      (lanes-clear c op f ω d n q o (s ∷ pre) post (λ m → sub (there m)) gs oks)

-- THE PATH TO A FOUND MARK IS CLEAR.
found-clr : ∀ {R} {t : St [] R} {Γ A} {c′ : Ctx R Γ A} {s′ m κ} → G t → StOK t
          → search top t ≡ just (found (Γ , A , c′ , s′) m κ) → Clr c′
found-clr {t = t} g ok fd with seek top t | seek-clear top t g ok
found-clr g ok refl | just _ | _ , f = f (tt , tt₁)
