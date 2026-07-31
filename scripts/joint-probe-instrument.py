#!/usr/bin/env python3
"""Instrument a COPY of Rx/Evaluator.agda so every subscribeE ENTRY is logged.

What is logged is exactly the pair subscribeE-caps demands a bound on:

    (pathLen κ , sizeᵉ b)      at every subscribeE fuel b κ id now sched st

`subscribeE-caps` hypothesises `pathLen κ + sizeᵉ b ≤ Caps.cSize c`, and its
JOINT form is what blocks thruWalk-caps / concatDrain-caps / innerFinish-caps
(agda/src/Verify-Budget-Sufficient/Caps-Face.agda).  The delivery side carries
`pathLen ≤ cSize` and `size ≤ cSize` separately, and separate bounds do not
add.  Before the ledger that would supply the joint form is threaded through
the tree, this measures whether the joint form is even TRUE on real runs.

The verified evaluator must stay byte-identical — Verify-Well-Formed reduces
its clauses — so scripts/joint-probe.sh copies the tree to a scratch project
and runs this on the copy.  The edits mirror burst-probe-instrument.py:

  1. EvalSt gains a `jointLog` field (write-only: never read by the evaluator,
     so behaviour is unchanged; joint-probe.sh greps the copy to enforce it).
  2. st-init seeds it empty.
  3. `probePathLen` / `logJoint` are defined next to retagEvents.
  4. Every `subscribeE` CLAUSE (and its declaration) is renamed `subscribeE′`,
     and a new `subscribeE` is defined as the logging wrapper.  Every recursive
     call — the clause bodies, subscribeInner, subscribeAll, stepFrame's
     re-entries, sharedConnect — is INDENTED, so it keeps the name `subscribeE`
     and goes through the wrapper.  That is what makes the log exhaustive: one
     entry per subscribeE the run ever performs, root, inner and slot alike.

Every edit is anchored on an exact source line; a missing anchor is a hard
error rather than a silent skip.
"""

import sys

DECL_HEAD = "subscribeE : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}"
DECL_LEN = 4  # the declaration is exactly four lines

ANCHORS = [
    (
        "  field registry        : List (RegId × Source × Chain Γ t)   -- live registration chains, subscription order",
        "        jointLog        : List (ℕ × ℕ)  -- JOINT PROBE (write-only)\n",
    ),
    (
        "retagEvents (value _   ∷ es) = retagEvents es",
        """
-- ── JOINT PROBE ──────────────────────────────────────────────────────
-- The chain LENGTH at a subscribe, and the SIZE of what is subscribed
-- under it.  Their sum is subscribeE-caps's hypothesis verbatim
probePathLen : ∀ {n} {Γ : Ctx n} {s t} → Path Γ s t → ℕ
probePathLen root           = 0
probePathLen (share-sink i) = 0
probePathLen (f ↠ p)        = suc (probePathLen p)

logJoint : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
         → Path Γ u t → Closed Γ u → EvalSt e → EvalSt e
logJoint κ b st =
  record st { jointLog = (probePathLen κ , sizeᵉ b) ∷ EvalSt.jointLog st }
-- ─────────────────────────────────────────────────────────────────────
""",
    ),
    (
        "              (installNode nid (merge-st 0 false) st)",
        """
-- ── JOINT PROBE: the logging wrapper every call site resolves to ─────
subscribeE fuel b κ id now sched st =
  let (burst , sched′ , st′) = subscribeE′ fuel b κ id now sched st
  in burst , sched′ , logJoint κ b st′
-- ─────────────────────────────────────────────────────────────────────
""",
    ),
]

REPLACEMENTS = [
    (
        "st-init e = record { registry = [] ; nextReg = 0 ; nodes = []",
        "st-init e = record { jointLog = [] ; registry = [] ; nextReg = 0 ; nodes = []",
    ),
    (
        "module Rx.Evaluator where",
        "{-# OPTIONS --no-termination-check #-}   -- JOINT PROBE: the logging\n"
        "-- wrapper is an identity hop, so the (fuel, expression) descent that\n"
        "-- carries the real evaluator no longer applies to this copy\n"
        "module Rx.Evaluator where",
    ),
]


def main(path: str) -> int:
    with open(path, encoding="utf-8") as f:
        lines = f.read().split("\n")

    missing = []

    for old, new in REPLACEMENTS:
        if old not in lines:
            missing.append(f"replacement anchor: {old!r}")
            continue
        lines[lines.index(old)] = new

    if DECL_HEAD not in lines:
        missing.append(f"declaration anchor: {DECL_HEAD!r}")
        decl = []
    else:
        i = lines.index(DECL_HEAD)
        decl = lines[i : i + DECL_LEN]

    heads = 0
    out = []
    for ln in lines:
        if ln.startswith("subscribeE "):
            heads += 1
            out.append("subscribeE′ " + ln[len("subscribeE ") :])
        else:
            out.append(ln)
    if heads < 10:
        missing.append(f"expected ≥10 subscribeE clause heads at column 0, found {heads}")

    if decl:
        j = out.index("subscribeE′ " + DECL_HEAD[len("subscribeE ") :])
        out[j + DECL_LEN : j + DECL_LEN] = [""] + decl
    lines = out

    for anchor, text in ANCHORS:
        if anchor not in lines:
            missing.append(f"insert anchor: {anchor!r}")
            continue
        k = lines.index(anchor)
        lines[k + 1 : k + 1] = text.split("\n")

    if missing:
        sys.stderr.write("joint-probe-instrument: anchors not found in %s:\n" % path)
        for m in missing:
            sys.stderr.write("  - %s\n" % m)
        return 1

    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))
    sys.stderr.write(
        "joint-probe-instrument: %s instrumented (%d subscribeE heads renamed)\n"
        % (path, heads)
    )
    return 0


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.stderr.write("usage: joint-probe-instrument.py <Rx/Evaluator.agda>\n")
        raise SystemExit(2)
    raise SystemExit(main(sys.argv[1]))
