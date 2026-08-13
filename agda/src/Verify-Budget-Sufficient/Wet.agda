-- STRATUM 2b of Verify-Budget-Sufficient: THE WET FAMILY.
--
-- TIMING RECEIPT 2026-08-11 (--profile=internal, dirty solo check): see
-- agda-performance-roadmap.md.  Measured because Subscribe-Face's cost turned
-- out to be 86% Agda's Positivity pass over ONE mutual block, and this module
-- is written in the same style; the roadmap records whether that generalises.
--
-- The half that steps the evaluator.  The Keeps ring (slot/share
-- monotonicity), the size-elim laws, the ledger arithmetic, the wet
-- lemmas for every evaluator entry point, subscribeE-walkS and
-- subscribeAll-wet, cascadeGo-walk, the width family, and the burst
-- cores (burst-wet/burst-dry/burst-bounded) and pop ring (pop-INV/
-- pop-head-bounded) that compose them.
--
-- `cascade-dry`, `drain-dry`, and `budget-sufficient` — the theorem
-- Verify-Well-Formed consumes — MOVED to `.Caps-Bridge`
-- (the 2026-08-05 upside-down ruling): a
-- module above `.Wet` can consume `.Caps-Bridge`'s `cascade-wet-via-caps`
-- in place of the cascade wet face (whose dry half is now
-- `cascadeGo-nodry`, .Burst-Walk § 8); `.Wet` itself
-- cannot, since `.Caps-Bridge` imports `.Wet`.
--
-- This module is a LAYER OVER .Caps as of 2026-08-01: the wet cores'
-- reset caps and per-instant store bound are read off `capsAt`, the caps
-- recurrence, which is the only entry-computable reach bound in the
-- machine (round3b-ledger-reset-absurd rules out the ledger).  The
-- recurrence sits in its own prerequisite module rather than in
-- .Caps-Face — the Keeps-Ring precedent, taken the same day the layering
-- landed — so this module and the caps FACE are still siblings and a
-- caps-face grind does not re-check twenty minutes of wet clauses.
module Verify-Budget-Sufficient.Wet where

-- Split 2026-08-12 into Wet/Part1..Part6 to bound per-edit recheck time.
-- The three genuine multi-member blocks are isolated one per module; no
-- mutual block was broken and no content changed.  All consumers import
-- this umbrella.

open import Verify-Budget-Sufficient.Wet.Part6 public
