-- Bug cache: type-level unit tests (see CLAUDE.md "Bug cache").
--
-- Each entry pins impl-batchSimultaneous against spec-batchSimultaneous on ONE
-- fixed canonical program, checked by refl at compile time. A regression fails
-- the typechecker instantly instead of hiding in a random QuickCheck seed.
--
-- These are a PERFORMANCE CACHE of discovered work, not real proofs. Keep them
-- dead simple. Delete this module once Formal-Verification is discharged.
--
-- Typecheck with:  agda src/Implementation/Unit-Test.agda
-- The GREEN section must always typecheck. The OPEN section holds bugs I'm
-- actively fixing; it may be red until the fix lands, then it graduates to GREEN.
module Implementation.Unit-Test where

open import Prelude
open import Shared-Types
open import Implementation.Batch-Simultaneous
open import Spec.Batch-Simultaneous
open import Implementation.Naive-Rx

-- driver: subjects present over n sources, firing the given (source,value) list
drv : {n : ℕ} → List (Fin n × Val) → Emissions n
drv xs = emissions (pureV []) xs

emp : {n : ℕ} → Emissions n
emp = drv []

s0 : {n : ℕ} → Fin (suc n)
s0 = fzero
s1 : {n : ℕ} → Fin (suc (suc n))
s1 = fsuc fzero
s2 : {n : ℕ} → Fin (suc (suc (suc n)))
s2 = fsuc (fsuc fzero)

ofv : {n : ℕ} → Val → Exp n
ofv v = ofE (v ∷ [])

-- Assert impl agrees with spec on `prog` under driver `em`.
Agree : {n : ℕ} → Emissions n → Exp n → Set
Agree em prog = impl-batchSimultaneous em prog ≡ spec-batchSimultaneous em prog

------------------------------------------------------------------------
-- GREEN: fixed bugs / passing regressions. Must always typecheck.
------------------------------------------------------------------------

-- concat leg ordering (empty driver)
_ : Agree (emp {1}) (concatAllE (ofS (srcE s0 ∷ ofE (3 ∷ []) ∷ [])))
_ = refl
_ : Agree (emp {1}) (concatAllE (ofS (ofE (3 ∷ []) ∷ srcE s0 ∷ [])))
_ = refl
_ : Agree (emp {1}) (mergeAllE (ofS (srcE s0 ∷ ofE (3 ∷ []) ∷ [])))
_ = refl

-- diamond + concatMap(of) — the common over-coalescing fix (weight), driver 5,6
_ : Agree (drv {1} ((s0 , 5) ∷ (s0 , 6) ∷ []))
          (concatAllE (mapS ofv (mergeAllE (ofS (srcE s0 ∷ mapE (λ n → (n * 10)) (srcE s0) ∷ [])))))
_ = refl

-- seed 35: merge(switchMap(of,src1), mergeMap(of,src1)) — trigger-count weight
_ : Agree (drv {2} ((s1 , 5) ∷ (s1 , 6) ∷ []))
          (mergeAllE (ofS ( switchAllE (mapS ofv (srcE s1))
                          ∷ mergeAllE (mapS ofv (srcE s1)) ∷ [])))
_ = refl

-- seed 25: merge(concatMap(of,src1), src1) — take-cut owed discount (max)
_ : Agree (drv {2} ((s1 , 5) ∷ (s1 , 6) ∷ []))
          (mergeAllE (ofS ( concatAllE (mapS ofv (srcE s1)) ∷ srcE s1 ∷ [])))
_ = refl

-- seed 48 essence: exhaust(of[v,1], switch(merge(src2,src2))) — provenance inherit
_ : Agree (drv {3} ((s2 , 6) ∷ []))
          (exhaustAllE (mapS (λ v → ofE (v ∷ 1 ∷ []))
            (switchAllE (mapS ofv (mergeAllE (ofS (srcE s2 ∷ srcE s2 ∷ [])))))))
_ = refl

------------------------------------------------------------------------
-- OPEN: bugs under active repair. Expected RED until the fix lands.
-- (serialItems trigger/flush ordering — switch/exhaust cut/drop misfires
--  because all a step's triggers precede all its flushes.)
--
-- Faithful to the QuickCheck counterexamples EXCEPT hidden mapE/scanE value
-- functions are replaced by identity: they relabel values, never move batch
-- boundaries, so the batch-STRUCTURE discrepancy (what differs) is preserved.
------------------------------------------------------------------------

idv : Val → Val
idv v = v
scz : Val → Val → Val
scz a v = v

-- seed 139: switchAll(mapS(λv→src1, mergeAll(ofS[src0,src0])))   impl [[2,0]] / spec [[2],[0]]
_ : Agree (drv {3} ((s0 , 1) ∷ (s1 , 2) ∷ (s1 , 0) ∷ (s2 , 3) ∷ []))
          (switchAllE (mapS (λ _ → srcE s1) (mergeAllE (ofS (srcE s0 ∷ srcE s0 ∷ [])))))
_ = refl

-- seed 95: map(switchAll(mapS(λv→src2, mergeAll(mapS(λv→src1, take3(of[5,9,0]))))))
_ : Agree (drv {3} ((s1 , 2) ∷ (s2 , 1) ∷ (s0 , 4) ∷ (s2 , 1) ∷ []))
          (mapE idv (switchAllE (mapS (λ _ → srcE s2)
            (mergeAllE (mapS (λ _ → srcE s1) (takeE 3 (ofE (5 ∷ 9 ∷ 0 ∷ []))))))))
_ = refl

-- seed 133: concatAll(ofS[ scan(switchAll(mapS(λv→src1, merge(mapS(λv→src2, of[6,6]))))),
--                          map(of[]), take2(scan(exhaust(ofS[empty,src0,of[7,7,0]]))) ])
_ : Agree (drv {3} ((s2 , 4) ∷ (s2 , 4) ∷ (s0 , 2) ∷ (s1 , 2) ∷ (s0 , 6) ∷ []))
          (concatAllE (ofS
            ( scanE scz 0 (switchAllE (mapS (λ _ → srcE s1)
                (mergeAllE (mapS (λ _ → srcE s2) (ofE (6 ∷ 6 ∷ []))))))
            ∷ mapE idv (ofE [])
            ∷ takeE 2 (scanE scz 0 (exhaustAllE (ofS
                (emptyE ∷ srcE s0 ∷ ofE (7 ∷ 7 ∷ 0 ∷ []) ∷ []))))
            ∷ [])))
_ = refl

-- seed 82: exhaustAll(ofS[ exhaustAll(mapS(λv→of[v], switchAll(mapS(λv→of[v,2,9],
--            merge(ofS[src2,empty,src2]))))), scan(of[0,1,9]) ])
_ : Agree (drv {3} ((s2 , 8) ∷ (s0 , 4) ∷ (s0 , 3) ∷ (s2 , 5) ∷ []))
          (exhaustAllE (ofS
            ( exhaustAllE (mapS (λ v → ofE (v ∷ []))
                (switchAllE (mapS (λ v → ofE (v ∷ 2 ∷ 9 ∷ []))
                  (mergeAllE (ofS (srcE s2 ∷ emptyE ∷ srcE s2 ∷ []))))))
            ∷ scanE scz 0 (ofE (0 ∷ 1 ∷ 9 ∷ []))
            ∷ [])))
_ = refl

-- seed 140: exhaustAll(mapS(λv→map(of[v]), merge(ofS[ of[6,5,7],
--            map(concatAll(mapS(λv→of[v,5], src1))), switchAll(ofS[src2,src1]) ])))
_ : Agree (drv {3} ((s1 , 6) ∷ []))
          (exhaustAllE (mapS (λ v → mapE idv (ofE (v ∷ [])))
            (mergeAllE (ofS
              ( ofE (6 ∷ 5 ∷ 7 ∷ [])
              ∷ mapE idv (concatAllE (mapS (λ v → ofE (v ∷ 5 ∷ [])) (srcE s1)))
              ∷ switchAllE (ofS (srcE s2 ∷ srcE s1 ∷ []))
              ∷ [])))))
_ = refl
