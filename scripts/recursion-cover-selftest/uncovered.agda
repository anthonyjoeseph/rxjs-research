-- the same graph with one undeclared cycle added: walk and drain call
-- each other at a counter nothing peels.

-- PEEL: inner -> top
-- STRUCTURAL SCC: top allNode

top : Set
inner : Set
allNode : Set
walk : Set
drain : Set

top = allNode
allNode = top
inner = top
walk = inner drain
drain = walk
