-- a declared structural cycle that is no longer a cycle.

-- PEEL: inner -> top
-- STRUCTURAL SCC: top allNode
-- STRUCTURAL SCC: walk inner

top : Set
inner : Set
allNode : Set
walk : Set

top = allNode
allNode = top
inner = top
walk = inner
