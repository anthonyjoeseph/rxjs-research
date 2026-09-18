-- fixture: the harness root, which stands ABOVE the elaboration and writes
-- plain formers of its own.  It is the sole route to `sharedSigᵉ` here, so
-- a surface that read the generator and the elaboration alone would report
-- that row's hole open.
module Implementation.Unit-Test.Prelude where

capProg : Exp Γ t → Exp Γ t
capProg e = sharedSigᵉ e
