-- FIXTURE: reachable ONLY through the two unused imports in Guard-Two-A and
-- Guard-Two-B.  Neither edge is individually load-bearing; jointly they are.
module Guard-Shared where

shared-thing : Set
shared-thing = Set
