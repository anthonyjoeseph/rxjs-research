-- AN UNPINNED ROW OF A READING HAS FINITELY MANY ROWS BEFORE IT: a
-- reading is truncated, and an unpinned row waits on every row before it.
module simultaneous.EnterFew where

open import Data.Product using (_,_; proj₁)
open import Data.Unit using (tt)

open import denotation.EmissionSet using (EmissionSet; Den; hot; coldAt; enter; out; skip; end; Unpinned; Truncate; Few)

truncate-few : ∀ {A} {X : EmissionSet A} {q e} → Truncate X q e → Unpinned e → Few (Truncate X) q
truncate-few {e = out _} (_ , ks , c) _ = ks , λ r lt → c (proj₁ r) lt tt
truncate-few {e = skip}  (_ , ks , c) _ = ks , λ r lt → c (proj₁ r) lt tt
truncate-few {e = end}   (_ , ks , c) _ = ks , λ r lt → c (proj₁ r) lt tt

enter-few : ∀ {A} (d : Den A) p {q e} → enter d p q e → Unpinned e → Few (enter d p) q
enter-few (hot t)    p = truncate-few
enter-few (coldAt f) p = truncate-few
