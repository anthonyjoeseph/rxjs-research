-- THE OLD-DENOTATION CHECK'S FIXTURE.  Nothing here may fire.
module fixture.Clean where

-- MUST NOT: a host's engine vocabulary.
open import Host using (Run; Agree)

-- MUST NOT: a qualified host's engine vocabulary.
import Host as K

y = K.Agree
