-- THE OLD-DENOTATION CHECK'S FIXTURE.  Never typechecked: each MUST FIRE
-- line is a row `make old-denotation-selftest` names.
module fixture.Uses where

-- MUST FIRE: an old module, imported.
open import Old using (anything)

-- MUST FIRE: an operator, and a named old name, taken from a host,
-- the list running over two lines.
open import Host using (Run; mapᴰ;
                        observe)

-- MUST FIRE: a host opened wholesale.
open import Host

-- MUST FIRE: an operator through a qualified host.
import Host as H

x = H.scanᴰ
