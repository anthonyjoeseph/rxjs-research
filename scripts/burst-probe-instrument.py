#!/usr/bin/env python3
"""Instrument a COPY of Rx/Evaluator.agda so every subscription burst is logged.

The verified evaluator must stay byte-identical — Verify-Well-Formed reduces its
clauses, so any edit in place would break the proofs.  So scripts/burst-probe.sh
copies the tree to a scratch project and runs this on the copy.  The edits are:

  1. EvalSt gains a `burstLog` field (write-only: the evaluator never reads it,
     so behaviour is unchanged — Burst-Probe asserts that by replaying the whole
     stream against `evaluate`).
  2. st-init seeds it empty.
  3. `probeEmit` / `logBurst` are defined next to retagEvents.
  4. Every `subscribeE` CLAUSE (and its declaration) is renamed `subscribeE′`,
     and a new `subscribeE` is defined as the logging wrapper around it.  Every
     recursive call — the clause bodies, subscribeInner, stepFrame's re-entries —
     is indented, so it keeps the name `subscribeE` and therefore goes through
     the wrapper.  That is what makes the log EXHAUSTIVE: one entry per burst
     any subscribeE ever mints, root and inner alike.

Every edit is anchored on an exact source line; a missing anchor is a hard error
rather than a silent skip.
"""

import sys

DECL_HEAD = "subscribeE : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}"
DECL_LEN = 4  # the declaration is exactly four lines

ANCHORS = [
    # (exact line, text inserted after it)
    (
        "                           μᵉ; varᵉ; deferᵉ)",
        "open import Rx.Hop-Depth using (hopD\u1d49; hopD\u1d5b)   -- HOP PROBE\n",
    ),
    (
        "  field registry        : List (RegId × Source × Chain Γ t)   -- live registration chains, subscription order",
        "        burstLog        : List (List (InstEmit ⊤))  -- BURST PROBE (write-only)\n"
        "        hopLog          : List (ℕ × List ℕ)         -- HOP PROBE (write-only)\n",
    ),
    (
        "retagEvents (value _   ∷ es) = retagEvents es",
        """
-- ── BURST PROBE ──────────────────────────────────────────────────────
-- payloads are erased but VALUE EVENTS ARE KEPT: frameFresh? and the
-- accumulator analysis read only init/close/handoff/complete and the emit's
-- kind, but a witness burst is unreadable without knowing where values sat
-- (they are what makes a take frame cut)
probeRetag : ∀ {A : Set} → List (InstEvent A) → List (InstEvent ⊤)
probeRetag []               = []
probeRetag (init s    ∷ es) = init s    ∷ probeRetag es
probeRetag (close s r ∷ es) = close s r ∷ probeRetag es
probeRetag (handoff s ∷ es) = handoff s ∷ probeRetag es
probeRetag (complete  ∷ es) = complete  ∷ probeRetag es
probeRetag (value _   ∷ es) = value tt  ∷ probeRetag es

probeEmit : ∀ {A : Set} → InstEmit A → InstEmit ⊤
probeEmit (es at i from s as k) = probeRetag es at i from s as k

logBurst : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {A : Set}
         → List (InstEmit A) → EvalSt e → EvalSt e
logBurst b st = record st { burstLog = map probeEmit b ∷ EvalSt.burstLog st }

-- ── HOP PROBE ────────────────────────────────────────────────────────
-- The burst log erases payloads, but the hop measurement needs their
-- DEPTHS, so this is a second, numeric log: for each subscribe, hopD of
-- the expression walked, against hopD of every value it handed back.
-- That pair is exactly the emitted-value invariant the hop edge
-- consumes — hopD (mergeAllᵉ c) is suc (hopD c), so `every emitted value
-- of c is ≤ hopD c` is what makes the hop strict.
hopValsE : ∀ {n} {Γ : Ctx n} {u} (V : ℕ) → List (InstEvent (Val Γ u)) → List ℕ
hopValsE V []                     = []
hopValsE V (init _    ∷ es)       = hopValsE V es
hopValsE V (close _ _ ∷ es)       = hopValsE V es
hopValsE V (handoff _ ∷ es)       = hopValsE V es
hopValsE V (complete  ∷ es)       = hopValsE V es
hopValsE {u = u} V (value v ∷ es) = hopDᵛ V u v ∷ hopValsE V es

hopValsB : ∀ {n} {Γ : Ctx n} {u} (V : ℕ) → List (InstEmit (Val Γ u)) → List ℕ
hopValsB V []         = []
hopValsB V (em ∷ ems) = hopValsE V (InstEmit.events em) ++ hopValsB V ems

logHop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
       → Closed Γ u → Slots Γ → List (InstEmit (Val Γ u)) → EvalSt e → EvalSt e
logHop {e = e} b sl burst st =
  let V = sizeᵉ e + slotsSize sl
  in record st { hopLog = (hopDᵉ V b , hopValsB V burst) ∷ EvalSt.hopLog st }
-- ─────────────────────────────────────────────────────────────────────
""",
    ),
    (
        "              (installNode nid (merge-st 0 false) st)",
        """
-- ── BURST PROBE: the logging wrapper every call site resolves to ─────
subscribeE fuel b κ id now sched st =
  let (burst , sched′ , st′) = subscribeE′ fuel b κ id now sched st
  in burst , sched′ , logHop b (Sched.slots sched) burst (logBurst burst st′)
-- ─────────────────────────────────────────────────────────────────────
""",
    ),
]

REPLACEMENTS = [
    (
        "st-init e = record { registry = [] ; nextReg = 0 ; nodes = []",
        "st-init e = record { burstLog = [] ; hopLog = [] ; registry = [] ; nextReg = 0 ; nodes = []",
    ),
    (
        "module Rx.Evaluator where",
        "{-# OPTIONS --no-termination-check #-}   -- BURST PROBE: the logging\n"
        "-- wrapper is an identity hop, so the (fuel, expression) descent that\n"
        "-- carries the real evaluator no longer applies to this copy\n"
        "module Rx.Evaluator where",
    ),
]


def main(path: str) -> int:
    with open(path, encoding="utf-8") as f:
        lines = f.read().split("\n")

    missing = []

    # 1. whole-line replacements
    for old, new in REPLACEMENTS:
        if old not in lines:
            missing.append(f"replacement anchor: {old!r}")
            continue
        lines[lines.index(old)] = new

    # 2. rename every subscribeE declaration/clause head (column 0 only) and
    #    re-declare subscribeE for the wrapper
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

    # re-insert the original declaration (for the wrapper) after the renamed one
    if decl:
        j = out.index("subscribeE′ " + DECL_HEAD[len("subscribeE ") :])
        out[j + DECL_LEN : j + DECL_LEN] = [""] + decl
    lines = out

    # 3. insert-after anchors
    for anchor, text in ANCHORS:
        if anchor not in lines:
            missing.append(f"insert anchor: {anchor!r}")
            continue
        k = lines.index(anchor)
        lines[k + 1 : k + 1] = text.split("\n")

    if missing:
        sys.stderr.write("burst-probe-instrument: anchors not found in %s:\n" % path)
        for m in missing:
            sys.stderr.write("  - %s\n" % m)
        return 1

    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))
    sys.stderr.write(
        "burst-probe-instrument: %s instrumented (%d subscribeE heads renamed)\n"
        % (path, heads)
    )
    return 0


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.stderr.write("usage: burst-probe-instrument.py <Rx/Evaluator.agda>\n")
        raise SystemExit(2)
    raise SystemExit(main(sys.argv[1]))
