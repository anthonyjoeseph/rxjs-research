-- FIXTURE: no module declaration at all.  Agda checks it as a target and
-- crashes every IMPORTER with __IMPOSSIBLE__ out of Imports.hs.
x : Set
x = Set
