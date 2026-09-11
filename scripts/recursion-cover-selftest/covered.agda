-- a call graph whose only surviving cycle is declared.

-- PEEL: inner -> top
-- STRUCTURAL SCC: top allNode

top : Set
inner : Set
allNode : Set
walk : Set

top = allNode
allNode = top
inner = top
walk = inner
