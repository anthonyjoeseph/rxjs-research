{-# OPTIONS --guardedness #-}

module adequacy.Engine.Head.Race where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Properties using (length-++)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᴹ)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

open import Tree using (Obs; mergeᶠ)
open import denotation.MonotonicList.Events using (Pos; Timeline; _<ᵖ_; ix; <ᵖ-trans; ≮-trans; inside; <ᵖ-shift)
open import denotation.Unfold using (Node; Step; outˢ; skipˢ; endˢ; hushˢ; headˢ; step; restˢ; restsˢ; restᴹ; restsᶜ; restᶜ; unionˢ;
  Earliest; found; earliest; pick; Outer; doneᵒ; runᵒ; outerOf; goˢ; outerˢ; laneˢ; flatˢ;
  Source; live; ended; connectᶜ; burstingᶜ; underᶜ; subscribe; sourceˢ; bodyˢ; shutˢᵗ; burstsˢ; beforeˢ) renaming (none to noneᴱ)
open import operation.Key using (Key; at; after; _<ᴷ_)
open import operation.PureObservable using (module Machine)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; Ctx; closed; inMap; inCut;
  Out; still; shows; Cand; seek; first; retag; mapT; cutT; nx; cp; attached; attAt; raceT; outerT; laneT; lanes; inOuter; inLanes; inLn;
  CS; cs; inSrc; inBody; own; ownBest; shift; over; sourceT; bodyM; owedM) renaming (found to foundᴹ)
open import adequacy.Engine.Meaning using (gh; outerG)
open import adequacy.Engine.Shuts using (Shuts; shutAll; Toldˢ)
open import adequacy.Engine.Head using (<-≮ᴷ; <≮ᴷ; Agrees; Done; Frag; NoConn; Quiet; Upto; []; _∷_; agrees-upto; at-<ᵖ; calm; clash; done-step; shut-fixed; early; exact; ext-≮; head-hush; hush-quiet; none; none-head; quiet-first; quiet-hush; silent-first; upto-step; view; view-key; ≮<ᴷ; ≮ᴷ-trans)

------------------------------------------------------------------------
-- The earliest lane, as the stepper finds it

-- A search's winner: its head and its step.
win : ∀ {Γ B} → Earliest Γ B → Maybe (Pos × Step Γ B)
win noneᴱ               = nothing
win (found k bs l s as) = just (k , s)

-- A lane met before the winner (newer) wins only strictly first; one met
-- after (older) wins ties too.
pickW : ∀ {Γ B} → Step Γ B → Maybe Pos → Maybe (Pos × Step Γ B) → Maybe (Pos × Step Γ B)
pickW s nothing  w                = w
pickW s (just k) nothing          = just (k , s)
pickW s (just k) (just (k′ , s′)) = if k <ᵖ k′ then just (k , s) else just (k′ , s′)

minS : ∀ {Γ B} → Step Γ B → Maybe Pos → Maybe (Pos × Step Γ B) → Maybe (Pos × Step Γ B)
minS s nothing  w                = w
minS s (just k) nothing          = just (k , s)
minS s (just k) (just (k′ , s′)) = if k′ <ᵖ k then just (k′ , s′) else just (k , s)

win-pick : ∀ {Γ B} (l : Node Γ B) s ls h (E : Earliest Γ B) → win (pick l s ls h E) ≡ pickW s h (win E)
win-pick l s ls nothing  noneᴱ                 = refl
win-pick l s ls nothing  (found k bs c sc as)  = refl
win-pick l s ls (just k) noneᴱ                 = refl
win-pick l s ls (just k) (found k′ bs c sc as) with k <ᵖ k′
... | true  = refl
... | false = refl

pickW-if : ∀ {Γ B} (s : Step Γ B) h b (x y : Maybe (Pos × Step Γ B)) → pickW s h (if b then x else y) ≡ (if b then pickW s h x else pickW s h y)
pickW-if s h true  x y = refl
pickW-if s h false x y = refl

minS-if : ∀ {Γ B} (s : Step Γ B) h b (x y : Maybe (Pos × Step Γ B)) → minS s h (if b then x else y) ≡ (if b then minS s h x else minS s h y)
minS-if s h true  x y = refl
minS-if s h false x y = refl

-- Three by two comparisons, the third their consequence.
sel : ∀ {X : Set₁} (A B C : Bool) (a w m : X) → (A ≡ true → B ≡ true → C ≡ true) → (A ≡ false → B ≡ false → C ≡ false)
    → (if B then (if A then a else w) else (if C then a else m)) ≡ (if A then (if C then a else m) else (if B then w else m))
sel true  true  true  a w m t f = refl
sel true  true  false a w m t f with () ← t refl refl
sel true  false C     a w m t f = refl
sel false true  C     a w m t f = refl
sel false false true  a w m t f with () ← f refl refl
sel false false false a w m t f = refl

-- A newer lane and an older one meet the rest in either order.
swap : ∀ {Γ B} (a m : Step Γ B) ha hm w → pickW a ha (minS m hm w) ≡ minS m hm (pickW a ha w)
swap a m nothing   hm        w                = refl
swap a m (just ka) nothing   w                = refl
swap a m (just ka) (just km) nothing          = refl
swap a m (just ka) (just km) (just (kw , sw)) =
  trans (pickW-if a (just ka) (kw <ᵖ km) _ _)
    (trans (sel (ka <ᵖ kw) (kw <ᵖ km) (ka <ᵖ km) (just (ka , a)) (just (kw , sw)) (just (km , m))
                (<ᵖ-trans ka kw km) (λ x y → ≮-trans km kw ka y x))
           (sym (minS-if m (just km) (ka <ᵖ kw) _ _)))

lone : ∀ {Γ B} (s : Step Γ B) h → pickW s h nothing ≡ minS s h nothing
lone s nothing  = refl
lone s (just k) = refl

-- The oldest lane, last in the stepper's list, met last.
win-snoc : ∀ {Γ B} (LS : List (Node Γ B)) m → win (earliest (LS ++ [ m ])) ≡ minS (step m) (headˢ (step m)) (win (earliest LS))
win-snoc []       m = trans (win-pick m (step m) [] (headˢ (step m)) noneᴱ) (lone (step m) (headˢ (step m)))
win-snoc (l ∷ LS) m =
  trans (win-pick l (step l) (LS ++ [ m ]) (headˢ (step l)) (earliest (LS ++ [ m ])))
    (trans (cong (pickW (step l) (headˢ (step l))) (win-snoc LS m))
      (trans (swap (step l) (step m) (headˢ (step l)) (headˢ (step m)) (win (earliest LS)))
        (cong (minS (step m) (headˢ (step m))) (sym (win-pick l (step l) LS (headˢ (step l)) (earliest LS))))))

-- How many lanes a search saw, the winner among them.
Len : ∀ {Γ B} → Earliest Γ B → ℕ → Set
Len noneᴱ               n = ⊤
Len (found k bs l s as) n = n ≡ suc (length bs + length as)

len-pick : ∀ {Γ B} (l : Node Γ B) s ls h (E : Earliest Γ B) → Len E (length ls) → Len (pick l s ls h E) (suc (length ls))
len-pick l s ls nothing  noneᴱ                 e = tt
len-pick l s ls nothing  (found k bs c sc as)  e = cong suc e
len-pick l s ls (just k) noneᴱ                 e = refl
len-pick l s ls (just k) (found k′ bs c sc as) e with k <ᵖ k′
... | true  = refl
... | false = cong suc e

len-earliest : ∀ {Γ B} (LS : List (Node Γ B)) → Len (earliest LS) (length LS)
len-earliest []       = tt
len-earliest (l ∷ LS) = len-pick l (step l) LS (headˢ (step l)) (earliest LS) (len-earliest LS)

len-mid : ∀ {a} {X : Set a} (bs : List X) l as → length (bs ++ l ∷ as) ≡ suc (length bs + length as)
len-mid bs l as = trans (length-++ bs) (+-suc (length bs) (length as))

------------------------------------------------------------------------
-- The engine's lanes against the stepper's winner

stW : ∀ {Γ B} → Maybe (Pos × Step Γ B) → Step Γ B
stW nothing        = hushˢ
stW (just (k , s)) = s

HeadOK : ∀ {Γ B} → Maybe (Pos × Step Γ B) → Set
HeadOK nothing        = ⊤
HeadOK (just (k , s)) = headˢ s ≡ just k

WA : ∀ {Γ B} → Maybe (Key × Out B) → Maybe (Pos × Step Γ B) → Set₁
WA y w = Agrees y (stW w) × HeadOK w

quiet-wa : ∀ {R Γ B} (x y : Maybe (Cand R B)) (w : Maybe (Pos × Step Γ B)) → Quiet (mapᴹ proj₂ x) → WA (mapᴹ proj₂ y) w
         → WA (mapᴹ proj₂ (first x y)) w
quiet-wa nothing           y w q    a       = a
quiet-wa (just (F , k , o)) y w calm (a , h) = silent-first F k y (stW w) a , h

-- An older lane with its own step against the newer lanes' winner.
tf : ∀ {Γ B} {k h : Key} {o′ : Out B} (sx sw : Step Γ B) {km kw} → headˢ sx ≡ just km → headˢ sw ≡ just kw
   → Agrees (just (k , o′)) sw → k <ᴷ h ≡ true → at km <ᴷ h ≡ false → kw <ᵖ km ≡ false → Agrees (just (k , o′)) sx
tf {h = h} sx sw {km} {kw} hx hw (exact e) t ux u with view-key sw e hw
... | refl = ⊥-elim (clash (trans (sym (at-<ᵖ kw km)) (<≮ᴷ (at kw) h (at km) t ux)) u)
tf {k = k} {h} sx sw {km} hx hw (early v) t ux u = early (subst (Upto k) (sym hx) (<-≮ᴷ (at km) k h t ux))

ft : ∀ {Γ B} {k h : Key} {o : Out B} (sx sw : Step Γ B) {km kw} → headˢ sx ≡ just km → headˢ sw ≡ just kw
   → Agrees (just (h , o)) sx → k <ᴷ h ≡ false → at kw <ᴷ k ≡ false → kw <ᵖ km ≡ true → Agrees (just (h , o)) sw
ft {k = k} sx sw {km} {kw} hx hw (exact e) t uy u with view-key sx e hx
... | refl = ⊥-elim (clash (≮<ᴷ k (at kw) (at km) uy (trans (at-<ᵖ kw km) u)) t)
ft {k = k} {h} sx sw {km} {kw} hx hw (early v) t uy u = early (subst (Upto h) (sym hw) (≮ᴷ-trans (at kw) k h uy t))

min-at : ∀ {R Γ B} (x y : Maybe (Cand R B)) (sx : Step Γ B) km w → headˢ sx ≡ just km → Agrees (mapᴹ proj₂ x) sx
       → WA (mapᴹ proj₂ y) w → WA (mapᴹ proj₂ (first x y)) (minS sx (just km) w)
min-at nothing y sx km w hx ax ay = ⊥-elim (none-head sx ax hx)
min-at (just x) nothing sx km nothing hx ax ay = ax , hx
min-at (just x) nothing sx km (just (kw , sw)) hx ax (ay , hw) = ⊥-elim (none-head sw ay hw)
min-at (just (f , h , o)) (just (g , k , o′)) sx km nothing hx ax (ay , _) = calm-at (hush-quiet ay)
  where
    calm-at : Quiet (just (k , o′)) → WA (mapᴹ proj₂ (first (just (f , h , o)) (just (g , k , o′)))) (just (km , sx))
    calm-at calm with k <ᴷ h in t
    ... | true  = early (subst (Upto k) (sym hx) (<-≮ᴷ (at km) k h t (subst (Upto h) hx (agrees-upto sx ax)))) , hx
    ... | false = ax , hx
min-at (just (f , h , o)) (just (g , k , o′)) sx km (just (kw , sw)) hx ax (ay , hw) with k <ᴷ h in t | kw <ᵖ km in u
... | true  | true  = ay , hw
... | false | false = ax , hx
... | true  | false = tf {k = k} {h} sx sw hx hw ay t (subst (Upto h) hx (agrees-upto sx ax)) u , hx
... | false | true  = ft {k = k} {h} sx sw hx hw ax t (subst (Upto k) hw (agrees-upto sw ay)) u , hw

min-wa : ∀ {R Γ B} (x y : Maybe (Cand R B)) (sx : Step Γ B) w → Agrees (mapᴹ proj₂ x) sx → WA (mapᴹ proj₂ y) w
       → WA (mapᴹ proj₂ (first x y)) (minS sx (headˢ sx) w)
min-wa x y sx w ax ay with headˢ sx in hx
... | nothing = quiet-wa x y w (hush-quiet (subst (Agrees (mapᴹ proj₂ x)) (head-hush sx hx) ax)) ay
... | just km = min-at x y sx km w hx ax ay

on-true : ∀ {R A} (y : Maybe (Cand R A)) → mapᴹ proj₂ (retag (cutT true) y) ≡ mapᴹ proj₂ y
on-true nothing            = refl
on-true (just (g , h , o)) = refl

------------------------------------------------------------------------
-- The merge's race

-- The stepper's outer, done or running, as the engine's search sees it.
data Outer≈ {R Γ A} : Bool → Maybe (Cand R A) → Outer Γ A → Set₁ where
  gone : ∀ {x} → Quiet (mapᴹ proj₂ x) → Outer≈ true x doneᵒ
  runs : ∀ {x O so} → Agrees (mapᴹ proj₂ x) so → Outer≈ false x (runᵒ O so)

data Ran {Γ A} : Bool → Maybe (Node Γ A) → Set₁ where
  noOuter : Ran true nothing
  anOuter : ∀ O → Ran false (just O)

quiet-race : ∀ {R A B} d n (x : Maybe (Cand R A)) (y : Maybe (Cand R B)) → Quiet (mapᴹ proj₂ x) → Quiet (mapᴹ proj₂ y)
           → Quiet (mapᴹ proj₂ (raceT d n [] x y))
quiet-race d n nothing            nothing            qx   qy   = none
quiet-race d n nothing            (just (g , k , o)) qx   calm = calm
quiet-race d n (just (f , h , o)) nothing            calm qy   = calm
quiet-race d n (just (f , h , o)) (just (g , k , o′)) calm calm with h <ᴷ k
... | true  = calm
... | false = calm

outer-upto : ∀ {Γ A B} (g : A → Pos → Node Γ B) (O : Node Γ A) (so : Step Γ A) (L : List (Node Γ B)) P k
           → Upto k (headˢ so) → Upto k (headˢ (outerˢ (mergeᶠ nothing) g O so L [] P))
outer-upto g O (outˢ q a o′) L       P k u = ≮ᴷ-trans (at (q ++ [ ix 0 ])) (at q) k (ext-≮ q [ ix 0 ]) u
outer-upto g O (skipˢ q o′)  L       P k u = u
outer-upto g O (endˢ c)      []      P k u = u
outer-upto g O (endˢ c)      (_ ∷ _) P k u = u
outer-upto g O hushˢ         L       P k u = u

-- The outer's event, read as the merge's.
outer-agrees : ∀ {Γ A B} (g : A → Pos → Node Γ B) (O : Node Γ A) (so : Step Γ A) (L : List (Node Γ B)) P n h (o : Out A)
             → n ≡ length L → Agrees (just (h , o)) so → Agrees (just (outerT n [] h o)) (outerˢ (mergeᶠ nothing) g O so L [] P)
outer-agrees g O (outˢ q a o′) L       P n _ _ e    (exact refl) = exact refl
outer-agrees g O (skipˢ q o′)  L       P n _ _ e    (exact refl) = exact refl
outer-agrees g O (endˢ c)      []      P n _ _ refl (exact refl) = exact refl
outer-agrees g O (endˢ c)      (_ ∷ _) P n _ _ refl (exact refl) = exact refl
outer-agrees g O hushˢ         L       P n h o e    (exact ())
outer-agrees g O so            L       P n h o e    (early u)    = early (outer-upto g O so L P h u)

lane-head : ∀ {Γ A B} (g : A → Pos → Node Γ B) mo bs l (s : Step Γ B) as P
          → headˢ (laneˢ (mergeᶠ nothing) g mo bs l s as [] P) ≡ headˢ s
lane-head g mo       bs      l (outˢ k b c) as      P = refl
lane-head g mo       bs      l (skipˢ k c)  as      P = refl
lane-head g nothing  []      l (endˢ c)     []      P = refl
lane-head g nothing  []      l (endˢ c)     (_ ∷ _) P = refl
lane-head g nothing  (_ ∷ _) l (endˢ c)     as      P = refl
lane-head g (just o) bs      l (endˢ c)     as      P = refl
lane-head g mo       bs      l hushˢ        as      P = refl

-- A lane's event, read as the merge's.
lane-agrees : ∀ {Γ A B} (g : A → Pos → Node Γ B) d mo (bs : List (Node Γ B)) l (s : Step Γ B) as P n k (o : Out B)
            → Ran d mo → n ≡ suc (length bs + length as) → Agrees (just (k , o)) s
            → Agrees (just (laneT {A = A} d n [] k o)) (laneˢ (mergeᶠ nothing) g mo bs l s as [] P)
lane-agrees g d mo bs      l (outˢ k′ b c) as      P n _ _ r           e    (exact refl) = exact refl
lane-agrees g d mo bs      l (skipˢ k′ c)  as      P n _ _ r           e    (exact refl) = exact refl
lane-agrees g d mo []      l (endˢ c)      []      P n _ _ noOuter     refl (exact refl) = exact refl
lane-agrees g d mo []      l (endˢ c)      (_ ∷ _) P n _ _ noOuter     refl (exact refl) = exact refl
lane-agrees g d mo (_ ∷ _) l (endˢ c)      as      P n _ _ noOuter     refl (exact refl) = exact refl
lane-agrees g d mo bs      l (endˢ c)      as      P n _ _ (anOuter O) e    (exact refl) = exact refl
lane-agrees g d mo bs      l hushˢ         as      P n k o r           e    (exact ())
lane-agrees g d mo bs      l s             as      P n k o r           e    (early u)    =
  early (subst (Upto k) (sym (lane-head g mo bs l s as P)) u)

-- A silent mark strictly before a lane's own: no later than the merge's step.
silent-lane : ∀ {Γ A B} (g : A → Pos → Node Γ B) mo bs l (s : Step Γ B) as P {h k′ k} {o′ : Out B}
            → h <ᴷ k′ ≡ true → Agrees (just (k′ , o′)) s → headˢ s ≡ just k
            → Upto h (headˢ (laneˢ (mergeᶠ nothing) g mo bs l s as [] P))
silent-lane g mo bs l s as P {h} {k′} {k} t ay hd =
  subst (Upto h) (sym (lane-head g mo bs l s as P))
    (subst (Upto h) (sym hd) (<-≮ᴷ (at k) h k′ t (subst (Upto k′) hd (agrees-upto s ay))))

-- The engine takes the outer, the stepper the lane: only a silent outer.
out-first : ∀ {Γ A B} (g : A → Pos → Node Γ B) n O (so : Step Γ A) k₀ → headˢ so ≡ just k₀ → ∀ bs l (s : Step Γ B) as P k h (o : Out A) k′ (o′ : Out B)
          → Agrees (just (h , o)) so → Agrees (just (k′ , o′)) s → headˢ s ≡ just k → h <ᴷ k′ ≡ true → k₀ <ᵖ k ≡ false
          → Agrees (just (outerT {B = B} n [] h o)) (laneˢ (mergeᶠ nothing) g (just O) bs l s as [] P)
out-first g n O so k₀ hs bs l s as P k h o k′ o′ (exact e) ay hd t u with view-key so e hs
... | refl = ⊥-elim (clash (trans (sym (at-<ᵖ k₀ k)) (<≮ᴷ (at k₀) k′ (at k) t (subst (Upto k′) hd (agrees-upto s ay)))) u)
out-first g n O so k₀ hs bs l s as P k h o k′ o′ (early v) ay hd t u = early (silent-lane g (just O) bs l s as P t ay hd)

-- The engine takes the lane, the stepper the outer: only a silent lane.
lane-first : ∀ {Γ A B} (g : A → Pos → Node Γ B) n O (so : Step Γ A) k₀ → headˢ so ≡ just k₀ → ∀ bs l (s : Step Γ B) as P k h (o : Out A) k′ (o′ : Out B)
           → Agrees (just (h , o)) so → Agrees (just (k′ , o′)) s → headˢ s ≡ just k → h <ᴷ k′ ≡ false → k₀ <ᵖ k ≡ true
           → Agrees (just (laneT {A = A} false n [] k′ o′)) (outerˢ (mergeᶠ nothing) g O so (bs ++ l ∷ as) [] P)
lane-first g n O so k₀ hs bs l s as P k h o k′ o′ ax (exact e) hd t u with view-key s e hd
... | refl = ⊥-elim (clash (≮<ᴷ h (at k₀) (at k) (subst (Upto h) hs (agrees-upto so ax)) (trans (at-<ᵖ k₀ k) u)) t)
lane-first g n O so k₀ hs bs l s as P k h o k′ o′ ax (early v) hd t u =
  early (outer-upto g O so (bs ++ l ∷ as) P k′ (upto-step h k′ (headˢ so) (agrees-upto so ax) t))

race-run : ∀ {R Γ A B} (g : A → Pos → Node Γ B) n O (so : Step Γ A) k₀ → headˢ so ≡ just k₀ → ∀ (LS : List (Node Γ B)) P k bs l (s : Step Γ B) as
           (f : Machine.Found R) h (o : Out A) (g′ : Machine.Found R) k′ (o′ : Out B)
         → Agrees (just (h , o)) so → Agrees (just (k′ , o′)) s → headˢ s ≡ just k → n ≡ length LS → length LS ≡ suc (length bs + length as)
         → Agrees (mapᴹ proj₂ (raceT false n [] (just (f , h , o)) (just (g′ , k′ , o′))))
                  (if k₀ <ᵖ k then outerˢ (mergeᶠ nothing) g O so (bs ++ l ∷ as) [] P else laneˢ (mergeᶠ nothing) g (just O) bs l s as [] P)
race-run g n O so k₀ hs LS P k bs l s as f h o g′ k′ o′ ax ay hd e le with h <ᴷ k′ in t | k₀ <ᵖ k in u
... | true  | true  = outer-agrees g O so (bs ++ l ∷ as) P n h o (trans e (trans le (sym (len-mid bs l as)))) ax
... | false | false = lane-agrees g false (just O) bs l s as P n k′ o′ (anOuter O) (trans e le) ay
... | true  | false = out-first g n O so k₀ hs bs l s as P k h o k′ o′ ax ay hd t u
... | false | true  = lane-first g n O so k₀ hs bs l s as P k h o k′ o′ ax ay hd t u

out-or-calm : ∀ {R Γ A B} (g : A → Pos → Node Γ B) O (so : Step Γ A) LS P n (f : Machine.Found R) h (o : Out A) (g′ : Machine.Found R) k′ (o′ : Out B)
            → n ≡ length LS → Agrees (just (h , o)) so → Quiet (just (k′ , o′))
            → Agrees (mapᴹ proj₂ (raceT false n [] (just (f , h , o)) (just (g′ , k′ , o′)))) (outerˢ (mergeᶠ nothing) g O so LS [] P)
out-or-calm g O so LS P n f h o g′ k′ o′ e ax calm with h <ᴷ k′ in t
... | true  = outer-agrees g O so LS P n h o e ax
... | false = early (outer-upto g O so LS P k′ (upto-step h k′ (headˢ so) (agrees-upto so ax) t))

-- The merge's step: the outer against the earliest lane.
race : ∀ {R Γ A B} (g : A → Pos → Node Γ B) d n (OUT : Outer Γ A) (LS : List (Node Γ B)) P (E : Earliest Γ B)
         (x : Maybe (Cand R A)) (y : Maybe (Cand R B))
     → Outer≈ d x OUT → WA (mapᴹ proj₂ y) (win E) → n ≡ length LS → Len E (length LS)
     → Agrees (mapᴹ proj₂ (raceT d n [] x y)) (goˢ (mergeᶠ nothing) g OUT LS [] P E)
race g d n doneᵒ LS P noneᴱ x y (gone qx) (ay , _) e _ = quiet-hush (quiet-race d n x y qx (hush-quiet ay))
race g d n doneᵒ LS P (found k bs l s as) x nothing (gone qx) (ay , hd) e le = ⊥-elim (none-head s ay hd)
race g d n doneᵒ LS P (found k bs l s as) nothing (just (g′ , k′ , o′)) (gone qx) (ay , hd) e le =
  lane-agrees g d nothing bs l s as P n k′ o′ noOuter (trans e le) ay
race g d n doneᵒ LS P (found k bs l s as) (just (f , h , o)) (just (g′ , k′ , o′)) (gone calm) (ay , hd) e le with h <ᴷ k′ in t
... | true  = early (silent-lane g nothing bs l s as P t ay hd)
... | false = lane-agrees g d nothing bs l s as P n k′ o′ noOuter (trans e le) ay
race g d n (runᵒ O hushˢ)         LS P noneᴱ nothing y (runs _)          (ay , _) e _ = quiet-hush (quiet-race d n nothing y none (hush-quiet ay))
race g d n (runᵒ O (outˢ _ _ _))  LS P noneᴱ nothing y (runs (exact ())) _ e _
race g d n (runᵒ O (skipˢ _ _))   LS P noneᴱ nothing y (runs (exact ())) _ e _
race g d n (runᵒ O (endˢ _))      LS P noneᴱ nothing y (runs (exact ())) _ e _
race g d n (runᵒ O so) LS P noneᴱ (just (f , h , o)) nothing (runs ax) _ e _ = outer-agrees g O so LS P n h o e ax
race g d n (runᵒ O so) LS P noneᴱ (just (f , h , o)) (just (g′ , k′ , o′)) (runs ax) (ay , _) e _ =
  out-or-calm g O so LS P n f h o g′ k′ o′ e ax (hush-quiet ay)
race g d n (runᵒ O so) LS P (found k bs l s as) x nothing (runs ax) (ay , hd) e le = ⊥-elim (none-head s ay hd)
race g d n (runᵒ O hushˢ)        LS P (found k bs l s as) nothing (just (g′ , k′ , o′)) (runs _) (ay , hd) e le =
  lane-agrees g d (just O) bs l s as P n k′ o′ (anOuter O) (trans e le) ay
race g d n (runᵒ O (outˢ _ _ _)) LS P (found k bs l s as) nothing (just _) (runs (exact ())) _ e le
race g d n (runᵒ O (skipˢ _ _))  LS P (found k bs l s as) nothing (just _) (runs (exact ())) _ e le
race g d n (runᵒ O (endˢ _))     LS P (found k bs l s as) nothing (just _) (runs (exact ())) _ e le
race g d n (runᵒ O hushˢ) LS P (found k bs l s as) (just (f , h , o)) (just (g′ , k′ , o′)) (runs (exact ())) _ e le
race g d n (runᵒ O hushˢ) LS P (found k bs l s as) (just (f , h , o)) (just (g′ , k′ , o′)) (runs (early _)) (ay , hd) e le with h <ᴷ k′ in t
... | true  = early (silent-lane g (just O) bs l s as P t ay hd)
... | false = lane-agrees g d (just O) bs l s as P n k′ o′ (anOuter O) (trans e le) ay
race g d n (runᵒ O (outˢ q a o″)) LS P (found k bs l s as) (just (f , h , o)) (just (g′ , k′ , o′)) (runs ax) (ay , hd) e le =
  race-run g n O (outˢ q a o″) q refl LS P k bs l s as f h o g′ k′ o′ ax ay hd e le
race g d n (runᵒ O (skipˢ q o″)) LS P (found k bs l s as) (just (f , h , o)) (just (g′ , k′ , o′)) (runs ax) (ay , hd) e le =
  race-run g n O (skipˢ q o″) q refl LS P k bs l s as f h o g′ k′ o′ ax ay hd e le
race g d n (runᵒ O (endˢ c)) LS P (found k bs l s as) (just (f , h , o)) (just (g′ , k′ , o′)) (runs ax) (ay , hd) e le =
  race-run g n O (endˢ c) c refl LS P k bs l s as f h o g′ k′ o′ ax ay hd e le

outer-at : ∀ {R Γ A} d (o : St Γ A) (V : Shuts Γ) (x : Maybe (Cand R A)) → Frag o → Toldˢ V o → (d ≡ true → Done o × NoConn o)
         → Agrees (mapᴹ proj₂ x) (step (shutAll V (gh o))) → Outer≈ d x (outerOf (mapᴹ (shutAll V) (outerG d (gh o))))
outer-at true  o V x fo to dd a =
  gone (hush-quiet (subst (Agrees (mapᴹ proj₂ x)) (trans (cong step (shut-fixed V o to fo (proj₂ (dd refl)))) (done-step o fo (proj₁ (dd refl)))) a))
outer-at false o V x fo to dd a = runs a

------------------------------------------------------------------------
-- The connect's race

-- Just past a position not before another: not before just past it.
shift-≮ : ∀ q h → at q <ᴷ h ≡ false → at (q ++ [ ix 0 ]) <ᴷ shift h ≡ false
shift-≮ q (at p)    u = trans (at-<ᵖ (q ++ [ ix 0 ]) (p ++ [ ix 0 ])) (<ᵖ-shift q p (trans (sym (at-<ᵖ q p)) u))
shift-≮ q (after p) u = ≮ᴷ-trans (at (q ++ [ ix 0 ])) (at q) (after p) (ext-≮ q [ ix 0 ]) u

postulate
  -- A subscription at `p` heads at `p` or past it, read through any
  -- shuts: a shut ends a joiner it makes at or past the joiner's own
  -- position, and that lies under `p`.
  sub-head   : ∀ {Γ A} (V : Shuts Γ) (o : Obs Timeline Γ A) p → Upto (at p) (headˢ (step (shutAll V (subscribe o p))))
  -- Run as its burst under `p`, what a subscription at `p` leaves running
  -- heads at `p` or past it.
  sub-bursts : ∀ {Γ A B} (V : Shuts Γ) (o : Obs Timeline Γ A) p
             → Upto (at p) (headˢ (burstsˢ {B = B} p (shutAll V (subscribe o p)) (step (shutAll V (subscribe o p)))))

-- No later than a head, before something strictly later: no later.
upto-lt : ∀ m {h k} → Upto h m → k <ᴷ h ≡ true → Upto k m
upto-lt nothing  u t = tt
upto-lt (just p) {h} {k} u t = <-≮ᴷ (at p) k h t u

none-hush : ∀ {Γ A} (st : Step Γ A) → Agrees nothing st → headˢ st ≡ nothing
none-hush hushˢ        _ = refl
none-hush (outˢ _ _ _) (exact ())
none-hush (skipˢ _ _)  (exact ())
none-hush (endˢ _)     (exact ())

-- A quiet mark before an agreeing one, or after: still agreeing.
calm-first : ∀ {R Γ A} (x y : Maybe (Cand R A)) (st : Step Γ A) → Quiet (mapᴹ proj₂ x) → Agrees (mapᴹ proj₂ y) st
           → Agrees (mapᴹ proj₂ (first x y)) st
calm-first nothing           y st q    a = a
calm-first (just (F , k , o)) y st calm a = silent-first F k y st a

first-l : ∀ {R Γ A} (x y : Maybe (Cand R A)) (st : Step Γ A) → Quiet (mapᴹ proj₂ y) → Agrees (mapᴹ proj₂ x) st
        → Agrees (mapᴹ proj₂ (first x y)) st
first-l nothing y st q (exact e) with st | e
... | hushˢ | refl = quiet-hush q
first-l (just x) nothing st q a = a
first-l (just (f , h , o)) (just (g , k , o′)) st calm a with k <ᴷ h in t
... | true  = early (upto-lt (headˢ st) (agrees-upto st a) t)
... | false = a

-- A connect's own marks are silent.
own-calm : ∀ {R Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) ms → Quiet (mapᴹ proj₂ (ownBest c (connS k o b) ms))
own-calm c k o b []             = none
own-calm c k o b ((m , h) ∷ ms) =
  quiet-first (just (foundᴹ (_ , _ , c , connS k o b) m h , h , still)) (ownBest c (connS k o b) ms) calm (own-calm c k o b ms)

own-first : ∀ {R Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) m h ms (st : Step Γ B) → Upto h (headˢ st)
          → Agrees (mapᴹ proj₂ (ownBest c (connS k o b) ((m , h) ∷ ms))) st
own-first c k o b m h ms st u =
  first-l (just (foundᴹ (_ , _ , c , connS k o b) m h , h , still)) (ownBest c (connS k o b) ms) st (own-calm c k o b ms) (early u)

-- The source's mark is silent.
src-quiet : ∀ {R A B} v (x : Maybe (Cand R A)) (y : Maybe (Cand R B)) → Quiet (mapᴹ proj₂ y) → Quiet (mapᴹ proj₂ (sourceT v x y))
src-quiet v nothing            y                    q    = q
src-quiet v (just (f , h , o)) nothing              q    = calm
src-quiet v (just (f , h , o)) (just (g , k , o′))  calm with (if v then h else shift h) <ᴷ k
... | true  = calm
... | false = calm

-- The source's silent mark against the body's step: no later.
src-calm : ∀ {R Γ A B} v (x : Maybe (Cand R A)) (y : Maybe (Cand R B)) (st : Step Γ B) → Agrees (mapᴹ proj₂ y) st
         → Agrees (mapᴹ proj₂ (sourceT v x y)) st
src-calm v nothing            y st a = a
src-calm v (just (f , h , o)) nothing st (exact e) with st | e
... | hushˢ | refl = early tt
src-calm v (just (f , h , o)) (just (g , k , o′)) st a with (if v then h else shift h) <ᴷ k in t
... | true  = early (upto-lt (headˢ st) (agrees-upto st a) t)
... | false = a

-- Steps that show and head alike agree alike.
agrees-via : ∀ {Γ Δ A} {x : Maybe (Key × Out A)} (st : Step Γ A) (st′ : Step Δ A) → view st′ ≡ view st → headˢ st′ ≡ headˢ st
           → Agrees x st → Agrees x st′
agrees-via st st′ v h (exact e) = exact (trans e (sym v))
agrees-via st st′ v h (early u) = early (subst (Upto _) (sym h) u)

body-v : ∀ {Γ X B} r (s : Source Γ X) (sb : Step (X ∷ Γ) B) → view (bodyˢ r s sb) ≡ view sb
body-v r s (outˢ k a b) = refl
body-v r s (skipˢ k b)  = refl
body-v r s (endˢ c)     = refl
body-v r s hushˢ        = refl

body-h : ∀ {Γ X B} r (s : Source Γ X) (sb : Step (X ∷ Γ) B) → headˢ (bodyˢ r s sb) ≡ headˢ sb
body-h r s (outˢ k a b) = refl
body-h r s (skipˢ k b)  = refl
body-h r s (endˢ c)     = refl
body-h r s hushˢ        = refl

shut-via : ∀ {Γ X B} r e (t : Node Γ X) (sb : Step (X ∷ Γ) B) {x} → Agrees x sb → Agrees x (shutˢᵗ r e t sb)
shut-via r e t (outˢ k a b) a′ = agrees-via _ _ refl refl a′
shut-via r e t (skipˢ k b)  a′ = agrees-via _ _ refl refl a′
shut-via r e t (endˢ c)     a′ = agrees-via _ _ refl refl a′
shut-via r e t hushˢ        a′ = agrees-via _ _ refl refl a′

-- A live connect's step: its body's, or its source's skip strictly first.
data SrcStep {Γ X B} (sb : Step (X ∷ Γ) B) (st : Step Γ B) (ss : Step Γ X) : Set where
  viaBody : view st ≡ view sb → headˢ st ≡ headˢ sb → SrcStep sb st ss
  viaSrc  : ∀ q → headˢ ss ≡ just q → headˢ st ≡ just (q ++ [ ix 0 ]) → beforeˢ (q ++ [ ix 0 ]) sb ≡ true → SrcStep sb st ss

src-step : ∀ {Γ X B} r (b : Node (X ∷ Γ) B) (sb : Step (X ∷ Γ) B) (s : Node Γ X) (ss : Step Γ X) → SrcStep sb (sourceˢ r b sb s ss) ss
src-step r b sb s (outˢ q a s′) with beforeˢ (q ++ [ ix 0 ]) sb in e
... | true  = viaSrc q refl refl e
... | false = viaBody (body-v r (live s) sb) (body-h r (live s) sb)
src-step r b sb s (skipˢ q s′) with beforeˢ (q ++ [ ix 0 ]) sb in e
... | true  = viaSrc q refl refl e
... | false = viaBody (body-v r (live s) sb) (body-h r (live s) sb)
src-step r b sb s (endˢ q) with beforeˢ (q ++ [ ix 0 ]) sb in e
... | true  = viaSrc q refl refl e
... | false = viaBody (body-v r (live s) sb) (body-h r (live s) sb)
src-step r b sb s hushˢ = viaBody (body-v r (live s) sb) (body-h r (live s) sb)

-- The body's mark against a source skip strictly before its step: only a
-- silent one, no later than the skip.
body-skip : ∀ {Γ X B} (sb : Step (X ∷ Γ) B) (st : Step Γ B) {q′ k} {o′ : Out B} → headˢ st ≡ just q′ → beforeˢ q′ sb ≡ true
          → at q′ <ᴷ k ≡ false → Agrees (just (k , o′)) sb → Agrees (just (k , o′)) st
body-skip (outˢ k′ a n) st {q′} h bt nk (exact refl) = ⊥-elim (clash (trans (at-<ᵖ q′ k′) bt) nk)
body-skip (skipˢ k′ n)  st {q′} h bt nk (exact refl) = ⊥-elim (clash (trans (at-<ᵖ q′ k′) bt) nk)
body-skip (endˢ k′)     st {q′} h bt nk (exact refl) = ⊥-elim (clash (trans (at-<ᵖ q′ k′) bt) nk)
body-skip hushˢ         st h bt nk (exact ())
body-skip sb st {q′} {k} h bt nk (early u) = early (subst (Upto k) (sym h) nk)

-- A source not yet subscribed: the body's silent mark at its
-- subscription, against the fresh subscription's first skip.
p1-src : ∀ {R Γ X B} (F : Machine.Found R) p (y : Maybe (Cand R B)) (sb : Step (X ∷ Γ) B) (st : Step Γ B) q′
       → at q′ <ᴷ at p ≡ false → headˢ st ≡ just q′ → beforeˢ q′ sb ≡ true → Agrees (mapᴹ proj₂ y) sb
       → Agrees (mapᴹ proj₂ (first (just (F , at p , still)) y)) st
p1-src F p nothing sb st q′ a0 hd bt a = early (subst (Upto (at p)) (sym hd) a0)
p1-src F p (just (g , k , o′)) sb st q′ a0 hd bt a with k <ᴷ at p in t
... | true  = body-skip sb st hd bt (<-≮ᴷ (at q′) k (at p) t a0) a
... | false = early (subst (Upto (at p)) (sym hd) a0)

p1-live : ∀ {R Γ X B} (F : Machine.Found R) p (y : Maybe (Cand R B)) r (b : Node (X ∷ Γ) B) (sb : Step (X ∷ Γ) B) (s : Node Γ X) (ss : Step Γ X)
        → Upto (at p) (headˢ ss) → Agrees (mapᴹ proj₂ y) sb
        → Agrees (mapᴹ proj₂ (first (just (F , at p , still)) y)) (sourceˢ r b sb s ss)
p1-live F p y r b sb s ss u a with src-step r b sb s ss
... | viaBody v h = silent-first F (at p) y _ (agrees-via sb _ v h a)
... | viaSrc q hs hd bt =
  p1-src F p y sb _ (q ++ [ ix 0 ]) (≮ᴷ-trans (at (q ++ [ ix 0 ])) (at q) (at p) (ext-≮ q [ ix 0 ]) (subst (Upto (at p)) hs u)) hd bt a

-- A live source: its skip just past its event, against the body's mark.
p3-src : ∀ {R Γ X B} (x : Maybe (Cand R X)) (y : Maybe (Cand R B)) (so : Step Γ X) (sb : Step (X ∷ Γ) B) (st : Step Γ B) q
       → headˢ so ≡ just q → headˢ st ≡ just (q ++ [ ix 0 ]) → beforeˢ (q ++ [ ix 0 ]) sb ≡ true
       → Agrees (mapᴹ proj₂ x) so → Agrees (mapᴹ proj₂ y) sb → Agrees (mapᴹ proj₂ (sourceT false x y)) st
p3-src nothing y so sb st q hs hd bt ax ay = ⊥-elim (none-head so ax hs)
p3-src (just (f , h , o)) nothing so sb st q hs hd bt ax ay =
  early (subst (Upto (shift h)) (sym hd) (shift-≮ q h (subst (Upto h) hs (agrees-upto so ax))))
p3-src (just (f , h , o)) (just (g , k , o′)) so sb st q hs hd bt ax ay with shift h <ᴷ k in t
... | true  = early (subst (Upto (shift h)) (sym hd) (shift-≮ q h (subst (Upto h) hs (agrees-upto so ax))))
... | false = body-skip sb st hd bt (≮ᴷ-trans (at (q ++ [ ix 0 ])) (shift h) k (shift-≮ q h (subst (Upto h) hs (agrees-upto so ax))) t) ay

p3-live : ∀ {R Γ X B} (x : Maybe (Cand R X)) (y : Maybe (Cand R B)) r (b : Node (X ∷ Γ) B) (sb : Step (X ∷ Γ) B) (s : Node Γ X) (ss : Step Γ X)
        → Agrees (mapᴹ proj₂ x) ss → Agrees (mapᴹ proj₂ y) sb → Agrees (mapᴹ proj₂ (sourceT false x y)) (sourceˢ r b sb s ss)
p3-live x y r b sb s ss ax ay with src-step r b sb s ss
... | viaBody v h = agrees-via sb _ v h (src-calm false x y sb ay)
... | viaSrc q hs hd bt = p3-src x y ss sb _ q hs hd bt ax ay

-- An over connect's rest, its body's run out: its source's skip under its
-- subscription, else nothing.
data OverStep {Γ X B} (ss : Step Γ X) (st : Step Γ B) : Set₁ where
  hushed : st ≡ hushˢ → OverStep ss st
  burst  : headˢ st ≡ headˢ ss → OverStep ss st

over-step : ∀ {Γ X B} r (x y : Node Γ B) (t : Node Γ X) (ss : Step Γ X) → restˢ {B = B} t ≡ hushˢ
          → OverStep ss (unionˢ x (burstsˢ r t ss) y hushˢ)
over-step r x y t (outˢ k a t′) rt with inside r k
... | true  = burst refl
... | false rewrite rt = hushed refl
over-step r x y t (skipˢ k t′) rt with inside r k
... | true  = burst refl
... | false rewrite rt = hushed refl
over-step r x y t (endˢ k) rt rewrite rt = hushed refl
over-step r x y t hushˢ    rt rewrite rt = hushed refl

-- The over connect's source, its event unmoved and silent: no later.
over-src : ∀ {R Γ X B} (x : Maybe (Cand R X)) (y : Maybe (Cand R B)) (ss : Step Γ X) (st : Step Γ B)
         → Agrees (mapᴹ proj₂ x) ss → Quiet (mapᴹ proj₂ y) → OverStep ss st → Agrees (mapᴹ proj₂ (sourceT true x y)) st
over-src x y ss st ax qy (hushed refl) = quiet-hush (src-quiet true x y qy)
over-src nothing y ss st ax qy (burst e) =
  subst (Agrees (mapᴹ proj₂ y)) (sym (head-hush st (trans e (none-hush ss ax)))) (quiet-hush qy)
over-src (just (f , h , o)) nothing ss st ax qy (burst e) = early (subst (Upto h) (sym e) (agrees-upto ss ax))
over-src (just (f , h , o)) (just (g , k , o′)) ss st ax calm (burst e) with h <ᴷ k in t
... | true  = early (subst (Upto h) (sym e) (agrees-upto ss ax))
... | false = early (upto-step h k (headˢ st) (subst (Upto h) (sym e) (agrees-upto ss ax)) t)

-- A rest under a body run out: the source's burst alone.
under-hush : ∀ {Γ X B} r (S : Node Γ X) (n : Node (X ∷ Γ) B) → restˢ {B = B} n ≡ hushˢ
           → restˢ {B = B} (connectᶜ r n (live S)) ≡ unionˢ (burstingᶜ r S) (burstsˢ r S (step S)) (underᶜ (live S) n) hushˢ
under-hush r S n e rewrite e = refl

union-upto : ∀ {Γ B} k (x y : Node Γ B) (sx : Step Γ B) → Upto k (headˢ sx) → Upto k (headˢ (unionˢ x sx y hushˢ))
union-upto k x y (skipˢ k′ x′) u = u
union-upto k x y (outˢ _ _ _)  u = tt
union-upto k x y (endˢ _)      u = tt
union-upto k x y hushˢ         u = tt

-- An ended source resting on nothing: the body's step, shut.
ended-shut : ∀ {Γ X B} r e (t : Node Γ X) (n : Node (X ∷ Γ) B) → restˢ {B = X} t ≡ hushˢ
           → step (connectᶜ r n (ended e (restᶜ t))) ≡ shutˢᵗ r e (restᶜ t) (step n)
ended-shut r e t n h rewrite h = refl

-- Over, ended, and resting on nothing: nothing.
over-ended : ∀ {Γ X B} r e (t : Node Γ X) (n : Node (X ∷ Γ) B) → restˢ {B = B} t ≡ hushˢ → restˢ {B = X} t ≡ hushˢ
           → restˢ {B = B} n ≡ hushˢ → restˢ {B = B} (connectᶜ r n (ended e (restᶜ t))) ≡ hushˢ
over-ended r e t n t1 t2 hn rewrite t2 | t1 | hn = refl
