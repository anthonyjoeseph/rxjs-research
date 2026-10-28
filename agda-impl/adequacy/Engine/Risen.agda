{-# OPTIONS --guardedness #-}

-- THE STILL'S SUBTREE, RISEN (`rise-causal`): a rise keeps the tree
-- causal.  Most rises move only the hole, so the tree is the one already
-- causal, or its frame's bookkeeping alone moves (a scan's seed, a flatMap
-- marked done), which owns nothing.  The leaves are the rises that key
-- something new: a takeWhile's failing value its completion, an outer's
-- value its lane, a lane's end the next queued, a source's event its
-- joiners, a body's end its owed close.
module adequacy.Engine.Risen where

open import Data.Bool using (true; false)
open import Data.List using ([]; _ʳ++_; _∷_; [_]; _++_; reverse)
open import Data.List.Properties using (ʳ++-defn; reverse-involutive)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (pred; suc; _<ᵇ_; _≡ᵇ_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Timeline; ix; last)
open import operation.PureObservable using (module Machine; module Driver)
open import operation.Key using (Key; at; after)
open import adequacy.Engine.Causal using (Causal; CausalW; LanesW; Keys⁺; LaneKeys⁺; Aloft⁺; Farᴷ; walk-at; keys-map; causal-run; _≼_; w≼; nodeW; node-same;
  scan≼; flat≼; ln≼; cut≼; cut-same; _∷≼_; ≼-refl; lanes-refl; lanes-≼; killAll-≼; far-tr)
  renaming (lanes-ʳ++ to lanes-ʳ≼)
open import adequacy.Engine.Room using (plant; swap-causal; aloft-hole; aloft-room; Shy; clear-of; keys-all; lanes-all; lanes-ʳ++; lanes-rev)
open import adequacy.Engine.Fresh using (Risen; room-mono; owed-to; start-fresh; outer-risen; lanes-risen; keys-ended)
open import adequacy.Engine.Sown using (Plant; sown⁺-here)
open import adequacy.Engine.Fold using (Base)
open import adequacy.Engine.Pick using (Order; module Order; whole)

open Machine using (St; pend; coldS; ofS; doneS; joinS; mapS; scanS; cutS; lnS; flatS; takeS; connS; attached; attAt; Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug;
  free; cpAt; cutAt; overAt; nx; cp; _⊕_; ⟨_,_,_,_⟩; rising; rise; admit; dequeue; ended; alive; start; closed; killAll)

module _ {R : Set} where
  open Driver R using (Step; silent; value; complete; drained; took)

  NextCaused : Step → Set
  NextCaused (silent t k)    = Causal (whole k)
  NextCaused (value t p a k) = Causal (whole k)
  NextCaused (complete p)    = ⊤
  NextCaused drained         = ⊤

  postulate
    feed-causal : ∀ {Γ X B} (c : Ctx R Γ B) k (b : St (X ∷ Γ) B) (s : St Γ X) e p
                → Base ⟨ inSrc k b c , s , rising e , p ⟩ → Order ⟨ inSrc k b c , s , rising e , p ⟩
                → NextCaused (took (rise (inSrc k b c) s e p))

  -- A takeWhile's failing value: its completion planted.
  take-fail-causal : ∀ {Γ A} (c : Ctx R Γ A) i q (s : St Γ A) a p
                   → Base ⟨ inTake i q free c , s , rising (nx a) , p ⟩ → Order ⟨ inTake i q free c , s , rising (nx a) , p ⟩
                   → Causal (plug c (takeS i q (cpAt p) s))
  take-fail-causal c i q s a p b o =
    let (_ , ks , a′) = Order.fresh o in
    plant {N = _≡ at (p ⊕ [ last ])} c {t = takeS i q free s} {t′ = takeS i q (cpAt p) s} (Order.causal o)
      ((λ { (_ , here refl) → aloft-hole c {takeS i q free s} {takeS i q (cpAt p) s} (a′ (inj₁ (sown⁺-here p last))) ; (_ , there ()) }) ,
       swap-causal {Q = Shy p} (λ {k} {t₁} {t₂} _ al → aloft-hole c {takeS i q free t₁} {takeS i q (cpAt p) t₂} al) s ks
         (proj₂ (walk-at c (takeS i q free s) (Order.causal o))))
      (λ { (e , k) m → (λ { (_ , here refl) → m refl ; (_ , there ()) }) , k })
      (room-mono c (λ { refl → inj₁ (sown⁺-here p last) }) (aloft-room p c (takeS i q free s) a′))

  -- A body's end: its close owed, past where it rose.
  owed-causal : ∀ {Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (s : St (X ∷ Γ) B) p
              → Base ⟨ inBody k o c , s , rising cp , p ⟩ → Order ⟨ inBody k o c , s , rising cp , p ⟩
              → Causal (plug c (connS (record k { owedAt = just p }) o s))
  owed-causal c k o s p b v =
    plant {N = _≡ after p} c {t = connS k o s} {t′ = connS k′ o s} (Order.causal v)
      (owed-to {P = λ h → Aloft⁺ h c (connS k′ o s)} k {o} {o} {s} {s} p (aloft-hole c {connS k o s} {connS k′ o s} (proj₂ (proj₂ (proj₂ (a′ {after p} (inj₂ refl))))))
         (λ f → aloft-hole c {connS k o s} {connS k′ o s} (proj₁ old f)) ,
       swap-causal {Q = λ h → Farᴷ h (after p)}
         (λ { {h} {t₁} {t₂} qh (x , e , al) → x , (λ {h′} z → owed-to {P = Farᴷ h} k {t₁} {t₂} {s} {s} p qh e {h′} z) , aloft-hole c {connS k t₁ s} {connS k′ t₂ s} al })
         o (keys-map {P = Shy p} (λ {h} sh → clear-of p {h} sh {after p} (inj₂ refl)) o (keys-all {N = Plant p} {Q = Farᴷ} o (λ {h} w → proj₁ (a′ {h} w))))
         (proj₁ (proj₂ old)) ,
       swap-causal {Q = λ h → Farᴷ h (after p)}
         (λ { {h} {t₁} {t₂} qh (x , y , e , al) → x , y , (λ {h′} z → owed-to {P = Farᴷ h} k {o} {o} {t₁} {t₂} p qh e {h′} z) , aloft-hole c {connS k o t₁} {connS k′ o t₂} al })
         s (keys-map {P = Shy p} (λ {h} sh → clear-of p {h} sh {after p} (inj₂ refl)) s ks)
         (proj₂ (proj₂ old)))
      (λ { {P} (e , ko , kb) m → (λ {h′} z → owed-to {P = P} k {o} {o} {s} {s} p (m refl) e {h′} z) , ko , kb })
      (room-mono c (λ { refl → inj₂ refl }) (aloft-room p c (connS k o s) (λ {h} w → proj₂ (proj₂ (proj₂ (a′ {h} w))))))
    where
      k′ = record k { owedAt = just p }
      old : CausalW c (connS k o s)
      old = walk-at c (connS k o s) (Order.causal v)
      ks : Keys⁺ (Shy p) s
      ks = proj₁ (proj₂ (Order.fresh v))
      a′ : ∀ {h} → Plant p h → Aloft⁺ h (inBody k o c) s
      a′ = proj₂ (proj₂ (Order.fresh v))

  -- A lane's end: nothing it owned is gone.
  ended-≼ : ∀ {Γ A} (s : St Γ A) → ended s ≼ s
  ended-≼ (lnS b (cutS l attached s))  = w≼ (nodeW (λ { (_ , ()) })) (ln≼ (w≼ (node-same (λ f → f)) (cut≼ cut-same (≼-refl s))))
  ended-≼ (lnS b (cutS l (attAt p) s)) = w≼ (nodeW (λ { (_ , ()) })) (ln≼ (w≼ (node-same (λ f → f)) (cut≼ cut-same (≼-refl s))))
  ended-≼ (lnS b (pend o))             = ≼-refl _
  ended-≼ (lnS b (coldS x l))          = ≼-refl _
  ended-≼ (lnS b (ofS i p xs))         = ≼-refl _
  ended-≼ (lnS b doneS)                = ≼-refl _
  ended-≼ (lnS b (joinS j g x ib))     = ≼-refl _
  ended-≼ (lnS b (mapS f s))           = ≼-refl _
  ended-≼ (lnS b (scanS f z s))        = ≼-refl _
  ended-≼ (lnS b (lnS x s))            = ≼-refl _
  ended-≼ (lnS b (takeS i q w s))      = ≼-refl _
  ended-≼ (lnS b (flatS op f d n q o ls)) = ≼-refl _
  ended-≼ (lnS b (connS k o x))        = ≼-refl _
  ended-≼ (pend o)                     = ≼-refl _
  ended-≼ (coldS x l)                  = ≼-refl _
  ended-≼ (ofS i p xs)                 = ≼-refl _
  ended-≼ doneS                        = ≼-refl _
  ended-≼ (joinS j g x ib)             = ≼-refl _
  ended-≼ (mapS f s)                   = ≼-refl _
  ended-≼ (scanS f z s)                = ≼-refl _
  ended-≼ (cutS l a s)                 = ≼-refl _
  ended-≼ (takeS i q w s)              = ≼-refl _
  ended-≼ (flatS op f d n q o ls)      = ≼-refl _
  ended-≼ (connS k o x)                = ≼-refl _

  -- A flatMap's bookkeeping moved: the same keys.
  flat-causal : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q d′ n′ q′ (o : St Γ A) ls
              → Causal (plug c (flatS op f d n q o ls)) → Causal (plug c (flatS op f d′ n′ q′ o ls))
  flat-causal c op f d n q d′ n′ q′ o ls =
    causal-run c {flatS op f d′ n′ q′ o ls} {flatS op f d n q o ls} (w≼ (nodeW (λ { (_ , ()) })) (flat≼ (≼-refl o) (lanes-refl ls)))

  -- A lane ended in place.
  ended-causal : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B) {p e}
               → Order ⟨ inLanes op f d n q o pre post c , s , rising e , p ⟩ → Causal (plug c (flatS op f d (pred n) q o (pre ʳ++ ended s ∷ post)))
  ended-causal c op f d n q o pre post s v =
    causal-run c {flatS op f d (pred n) q o (pre ʳ++ ended s ∷ post)} {flatS op f d n q o (pre ʳ++ s ∷ post)}
      (w≼ (nodeW (λ { (_ , ()) })) (flat≼ (≼-refl o) (lanes-ʳ≼ pre (ended-≼ s ∷≼ lanes-refl post)))) (Order.causal v)

  -- A lane begun: planted beside the lanes it joins, past where it subscribes.
  start-causal : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p {d₀ n₀ q₀}
               → Causal (plug c (flatS op f d₀ n₀ q₀ o ls)) → Risen c (flatS op f d₀ n₀ q₀ o ls) p
               → Causal (whole (start c op f d n q o ls a p))
  start-causal c op f d n q o ls a p {d₀} {n₀} {q₀} ca r with closed c | start-fresh c op f d n q o ls a p r
  ... | true  | _        = flat-causal c op f d₀ n₀ q₀ d n q o ls ca
  ... | false | (_ , fa) =
    plant {N = _≡ after x} c {t = flatS op f d₀ n₀ q₀ o ls} {t′ = flatS op f d (suc n) q o (reverse ls ʳ++ s₀ ∷ [])} ca
      ((λ { (_ , ()) }) ,
       swap-causal {Q = Shy p}
         (λ { {k} {t₁} {t₂} sh (l , al) →
           lanes-ʳ++ {P = Farᴷ k} (reverse ls) (lanes-rev {P = Farᴷ k} ls l) (lane₀ {Farᴷ k} (far₀ {k} sh) , tt) ,
           aloft-hole c {flatS op f d₀ n₀ q₀ t₁ ls} {flatS op f d (suc n) q t₂ (reverse ls ʳ++ s₀ ∷ [])} al })
         o ko (proj₁ (proj₂ old)) ,
       subst (LanesW c op f d (suc n) q o []) (sym eq) (snoc-causal [] ls kl (proj₂ (proj₂ old)) w₀))
      (λ { {P} (e , kᵒ , kˡ) m → (λ { (_ , ()) }) , kᵒ , lanes-ʳ++ {P = P} (reverse ls) (lanes-rev {P = P} ls kˡ) (lane₀ {P} (m refl) , tt) })
      (room-mono c (λ { refl → inj₁ (sown⁺-here p (ix 1)) }) (aloft-room p c (flatS op f d₀ n₀ q₀ o ls) g))
    where
      x = p ⊕ [ ix 1 ]
      s₀ : St _ _
      s₀ = lnS true (cutS true (attAt x) (pend (f a)))
      ko : Keys⁺ (Shy p) o
      ko = proj₁ (proj₂ (proj₁ (proj₂ r)))
      kl : LaneKeys⁺ (Shy p) ls
      kl = proj₂ (proj₂ (proj₁ (proj₂ r)))
      g : ∀ {h} → Plant p h → Aloft⁺ h c (flatS op f d₀ n₀ q₀ o ls)
      g = proj₂ (proj₂ r)
      old : CausalW c (flatS op f d₀ n₀ q₀ o ls)
      old = walk-at c (flatS op f d₀ n₀ q₀ o ls) ca
      far₀ : ∀ {k} → Shy p k → Farᴷ k (after x)
      far₀ {k} sh = clear-of p {k} sh {after x} (inj₁ (sown⁺-here p (ix 1)))
      lane₀ : ∀ {P : Key → Set} → P (after x) → Keys⁺ P s₀
      lane₀ pk = (λ { (_ , ()) }) , (λ { (_ , here refl) → pk ; (_ , there ()) }) , (λ { (_ , ()) }) , tt
      w₀ : CausalW (inLanes op f d (suc n) q o (reverse ls) [] c) s₀
      w₀ = (λ { (_ , ()) }) , (λ { (_ , here refl) → proj₂ (fa {after x} (inj₂ refl)) ; (_ , there ()) }) , (λ { (_ , ()) }) , tt
      snoc-keys : ∀ {P : Key → Set} ys → LaneKeys⁺ P ys → Keys⁺ P s₀ → LaneKeys⁺ P (ys ++ [ s₀ ])
      snoc-keys []       _          k = k , tt
      snoc-keys (y ∷ ys) (ky , kys) k = ky , snoc-keys ys kys k
      snoc-causal : ∀ pre ys → LaneKeys⁺ (Shy p) ys → LanesW c op f d₀ n₀ q₀ o pre ys
                  → CausalW (inLanes op f d (suc n) q o (ys ʳ++ pre) [] c) s₀ → LanesW c op f d (suc n) q o pre (ys ++ [ s₀ ])
      snoc-causal pre []       _          _       w = w , tt
      snoc-causal pre (y ∷ ys) (ky , kys) (wy , l) w =
        swap-causal {Q = Shy p}
          (λ { {k} {t₁} {t₂} sh (u , v , z , al) →
            u , v , snoc-keys {Farᴷ k} ys z (lane₀ {Farᴷ k} (far₀ {k} sh)) ,
            aloft-hole c {flatS op f d₀ n₀ q₀ o (pre ʳ++ t₁ ∷ ys)} {flatS op f d (suc n) q o (pre ʳ++ t₂ ∷ ys ++ [ s₀ ])} al })
          y ky wy ,
        snoc-causal (y ∷ pre) ys kys l w
      eq : reverse ls ʳ++ s₀ ∷ [] ≡ ls ++ [ s₀ ]
      eq = trans (ʳ++-defn (reverse ls)) (cong (_++ [ s₀ ]) (reverse-involutive ls))

  -- An outer's value: its lane begun, or it waits, or it is dropped.
  admit-causal : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p
               → Base ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩ → Order ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
               → NextCaused (took (admit c op f d n q o ls a p))
  admit-causal c (mergeᶠ nothing)  f d n q o ls a p b v =
    start-causal c (mergeᶠ nothing) f d n q o ls a p (Order.causal v) (outer-risen c (mergeᶠ nothing) f d n q ls d (Order.fresh v))
  admit-causal c (mergeᶠ (just m)) f d n q o ls a p b v with n <ᵇ m
  ... | true  = start-causal c (mergeᶠ (just m)) f d n q o ls a p (Order.causal v) (outer-risen c (mergeᶠ (just m)) f d n q ls d (Order.fresh v))
  ... | false = flat-causal c (mergeᶠ (just m)) f d n q d n (q ++ [ a ]) o ls (Order.causal v)
  admit-causal c switchᶠ           f d n q o ls a p b v with killAll ls | killAll-≼ ls
  ... | ls′ , t | kw =
    let (pr , ks , g) = Order.fresh v in
    start-causal c switchᶠ f d 0 q o ls′ a p {d} {n} {q}
      (causal-run c {flatS switchᶠ f d n q o ls′} {flatS switchᶠ f d n q o ls} (w≼ (nodeW (λ { (_ , ()) })) (flat≼ (≼-refl o) kw)) (Order.causal v))
      (pr , ((λ { (_ , ()) }) , ks , lanes-≼ (λ le sh {h} w → far-tr h le (sh w)) kw (lanes-all ls (λ w → proj₁ (g w)))) , λ w → aloft-hole c (proj₂ (g w)))
  admit-causal c exhaustᶠ          f d n q o ls a p b v with n ≡ᵇ 0
  ... | true  = start-causal c exhaustᶠ f d n q o ls a p (Order.causal v) (outer-risen c exhaustᶠ f d n q ls d (Order.fresh v))
  ... | false = Order.causal v

  -- A lane's end: its slot freed, the next queued begun.
  dequeue-causal : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B) p
                 → Base ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩ → Order ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩
                 → Causal (whole (dequeue c op f d (pred n) q o (pre ʳ++ ended s ∷ post) p))
  dequeue-causal c op f d n []      o pre post s p b v = ended-causal c op f d n [] o pre post s v
  dequeue-causal c op f d n (a ∷ q) o pre post s p b v =
    start-causal c op f d (pred n) q o (pre ʳ++ ended s ∷ post) a p (ended-causal c op f d n (a ∷ q) o pre post s v)
      (lanes-risen c op f d n (a ∷ q) o pre post (pred n) (ended s) (keys-ended s (proj₁ (proj₂ (Order.fresh v)))) (Order.fresh v))

  rise-causal : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) e p → Base ⟨ c , s , rising e , p ⟩ → Order ⟨ c , s , rising e , p ⟩
              → NextCaused (took (rise c s e p))
  rise-causal top                               s (nx a) p b o = Order.causal o
  rise-causal top                               s cp     p b o = tt
  rise-causal (inMap f c)                       s e      p b o = Order.causal o
  rise-causal (inScan f z c)                    s (nx a) p b o =
    causal-run c {scanS f (f z a) s} {scanS f z s} (w≼ (nodeW (λ { (_ , ()) })) (scan≼ (≼-refl s))) (Order.causal o)
    where open Machine using (scanS)
  rise-causal (inScan f z c)                    s cp     p b o = Order.causal o
  rise-causal (inCut l a c)                     s e      p b o = Order.causal o
  rise-causal (inLn d c)                        s e      p b o = Order.causal o
  rise-causal (inTake i q free c)               s (nx a) p b o with q a | i
  ... | true  | _     = Order.causal o
  ... | false | true  = take-fail-causal c true q s a p b o
  ... | false | false = take-fail-causal c false q s a p b o
  rise-causal (inTake i q free c)               s cp     p b o = Order.causal o
  rise-causal (inTake i q (cpAt r) c)           s e      p b o = Order.causal o
  rise-causal (inTake i q (cutAt r) c)          s e      p b o = Order.causal o
  rise-causal (inTake i q (overAt r) c)         s e      p b o = Order.causal o
  rise-causal (inOuter op f d n q ls c)         s (nx a) p b o = admit-causal c op f d n q s ls a p b o
  rise-causal (inOuter op f d n q ls c)         s cp     p b o =
    causal-run c {flatS op f true n q s ls} {flatS op f d n q s ls} (w≼ (nodeW (λ { (_ , ()) })) (flat≼ (≼-refl s) (lanes-refl ls))) (Order.causal o)
  rise-causal (inLanes op f d n q o pre post c) s (nx a) p b v with alive s
  ... | true  = Order.causal v
  ... | false = Order.causal v
  rise-causal (inLanes op f d n q o pre post c) s cp     p b v with alive s
  ... | true  = dequeue-causal c op f d n q o pre post s p b v
  ... | false = Order.causal v
  rise-causal (inSrc k d c)                     s e      p b o = feed-causal c k d s e p b o
  rise-causal (inBody k d c)                    s (nx a) p b o = Order.causal o
  rise-causal (inBody k d c)                    s cp     p b o = owed-causal c k d s p b o
