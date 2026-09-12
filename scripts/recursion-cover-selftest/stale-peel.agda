-- a declared peel naming an edge the code no longer has.

-- PEEL: inner -> top
-- PEEL: inner -> walk
-- STRUCTURAL SCC: top allNode

top : Set
inner : Set
allNode : Set
walk : Set

top = allNode
allNode = top
inner = top
walk = inner
