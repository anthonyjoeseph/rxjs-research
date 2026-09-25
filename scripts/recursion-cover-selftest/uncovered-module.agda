-- the undeclared cycle stated inside a parameterised module, whose body
-- is indented: walk and drain call each other at a counter nothing peels.

-- PEEL: inner -> top
-- STRUCTURAL SCC: top allNode

top : Set
inner : Set
allNode : Set

top = allNode
allNode = top
inner = top

module Watched (A : Set)
               (B : Set) where

  walk : Set
  drain : Set

  walk = inner drain
  drain = walk
