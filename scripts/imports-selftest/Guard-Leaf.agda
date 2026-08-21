-- FIXTURE: reachable only through `Guard-Root`'s unused import.  Nothing
-- imports this except that one dead edge, which is the whole point.
module Guard-Leaf where

leaf-thing : Set
leaf-thing = Set
