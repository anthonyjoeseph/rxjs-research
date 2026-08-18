module Thy where

postulate Nat : Set

-- WIRED: applied by a real body that Main reaches.
good-lemma : Nat → Nat
good-lemma x = x

-- PASSED-ONLY: its ONLY use is as a bare argument to a postulate.
bad-lemma : Nat → Nat
bad-lemma x = x

-- NESTED VALUE COMPUTATION: `nested` is applied inside parens to build a
-- value, NOT handed over as a proof.  Must keep its reachability.
nested : Nat → Nat
nested x = x

postulate parent-core : (Nat → Nat) → Nat → Nat

-- PASSED-ONLY VIA ETA.  CLAUDE.md MANDATES `(λ {n} → f {n})` for any lemma
-- with implicits, so this is the form R2 most needs to see — and the parens
-- used to hide it, which is how `merge-cert` kept a route home for months
-- while being an ingredient of nothing (2026-08-18).  Must be REPORTED.
eta-lemma : Nat → Nat
eta-lemma x = x

-- COMPUTED INSIDE A LAMBDA: the arrow's right-hand side is an APPLICATION,
-- not a bare head, so the lambda builds a value rather than passing a proof.
-- Must keep its reachability.
computed : Nat → Nat
computed x = x

postulate eta-parent : (Nat → Nat) → (Nat → Nat) → Nat → Nat

other : Nat → Nat
other y = good-lemma y

top-line : Nat → Nat
top-line z = other (parent-core bad-lemma
                     (nested (both-mods
                       (eta-parent (λ w → eta-lemma w)
                                   (λ w → computed (nested w)) z))))

-- MODULE APPLICATIONS.  `module M = F args` is a BINDING, not a scope: the
-- names on its right are real uses, and a scanner that skips the line hands
-- them no consumer.  Both loops must see it — `via-top` exercises the
-- file-level scan, `via-mod` the nested one, which is the case that bit
-- (2026-08-18: `module V = Walk … burstH` was `burstH`'s only consumer, and
-- skipping it reported a 39-name LIVE cluster as dead).
module Box (f : Nat → Nat) where
  run : Nat → Nat
  run x = f x

via-top : Nat → Nat
via-top x = x

module TopInst = Box via-top

module Scope where
  via-mod : Nat → Nat
  via-mod x = x

  module Inst = Box via-mod

both-mods : Nat → Nat
both-mods w = TopInst.run (Scope.Inst.run w)
