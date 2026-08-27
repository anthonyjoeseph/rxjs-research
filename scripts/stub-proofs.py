#!/usr/bin/env python3
"""Emit a mirror of the comment-stripped `src` with every PROOF postulated.

WHY THIS EXISTS.  The evidence trees import `src` and typecheck against it, so
a probe about one predicate pays for every theorem in the module that predicate
lives in.  The probes need DEFINITIONS to reduce -- a probe is `refl` at
concrete inputs and a postulate does not compute -- but they never unfold a
PROOF term: a refutation derives `⊥` from a statement, and a receipt pins a
numeral.  So the bodies of propositions can go, and only those.

WHAT COUNTS AS A PROOF, and the rule is deliberately narrow: the declaration's
RESULT type -- the text after its last top-level arrow -- mentions a
propositional operator (`≡`, `≤`, `<`, `⊥`).  A family ending in `Set`, a
decision procedure ending in `Bool` and an arithmetic definition ending in `ℕ`
all keep their bodies, which is what the probes compute with.

WHAT IS LEFT ALONE, conservatively: anything inside a `private`, `abstract`,
`mutual`, `instance`, `data` or `record` block.  An `abstract` body is already
opaque to the checker, so stubbing it would buy nothing anyway.

LINE NUMBERS ARE PRESERVED.  A stub emits `postulate` plus the signature
indented by two, which is one line more than the signature was, and the clause
lines it replaces are blanked -- so every later line in the file keeps its
number and `unmap-positions.py` goes on working.
"""
from __future__ import annotations

import argparse
import importlib.util as _ilu
import os
import re
import sys

# Reuse the declaration parser rather than writing a second one: two parsers
# for one language is how they drift.  The module must be registered before it
# is executed -- `@dataclass` resolves annotations through `sys.modules`.
_spec = _ilu.spec_from_file_location(
    "agda_dev", os.path.join(os.path.dirname(os.path.abspath(__file__)), "agda-dev.py"))
agda_dev = _ilu.module_from_spec(_spec)
sys.modules["agda_dev"] = agda_dev
_spec.loader.exec_module(agda_dev)

PROP = re.compile(r"[≡≤<⊥]")


def result_type(sig_text: str) -> str:
    """The text after the last TOP-LEVEL arrow of a signature's type."""
    ty = sig_text.split(":", 1)[1] if ":" in sig_text else sig_text
    depth = 0
    cut = 0
    i = 0
    while i < len(ty):
        c = ty[i]
        if c in "({":
            depth += 1
        elif c in ")}":
            depth -= 1
        elif depth == 0 and ty.startswith("→", i):
            cut = i + 1
        i += 1
    return ty[cut:]


def is_proof(sig_text: str) -> bool:
    return bool(PROP.search(result_type(sig_text)))


def stub_file(path: str) -> tuple[str, int]:
    """Return the stubbed text and how many declarations were stubbed.

    Rebuilt line by line rather than patched in place, because the exchange is
    not one-for-one: a stub is the signature plus a `postulate` header, and the
    line that header costs is taken back from the clause block it replaces.
    """
    p = agda_dev.parse(path)
    by_name: dict[str, list] = {}
    for it in p.items:
        if it.kind in ("sig", "clauses") and it.name:
            by_name.setdefault(it.name, []).append(it)

    # line index -> what to do with it
    header: dict[int, int] = {}   # sig.start -> sig.end
    blank: set[int] = set()
    drop: set[int] = set()
    n = 0
    for name, its in by_name.items():
        sig = next((i for i in its if i.kind == "sig"), None)
        cls = [i for i in its if i.kind == "clauses"]
        if sig is None or not cls:
            continue
        sig_text = " ".join(l.strip() for l in p.lines[sig.start:sig.end])
        if not is_proof(sig_text):
            continue
        body = [k for i in cls for k in range(i.start, i.end)]
        if not body:
            continue
        header[sig.start] = sig.end
        blank.update(body[:-1])
        drop.add(body[-1])       # pays for the `postulate` header line
        n += 1

    out: list[str] = []
    k = 0
    while k < len(p.lines):
        if k in header:
            out.append("postulate")
            for j in range(k, header[k]):
                l = p.lines[j]
                out.append("  " + l if l.strip() else l)
            k = header[k]
            continue
        if k in drop:
            k += 1
            continue
        out.append("" if k in blank else p.lines[k])
        k += 1
    return "\n".join(out), n


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", required=True, help="mirror src root to read")
    ap.add_argument("--dest", required=True, help="stubbed root to write")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    total = files = 0
    for root, _, names in os.walk(a.src):
        for nm in names:
            if not nm.endswith(".agda"):
                continue
            s = os.path.join(root, nm)
            d = os.path.join(a.dest, os.path.relpath(s, a.src))
            os.makedirs(os.path.dirname(d), exist_ok=True)
            text, k = stub_file(s)
            with open(d, "w", encoding="utf-8") as fh:
                fh.write(text)
            total += k
            files += 1
    print(f"stub-proofs: {total} proof(s) postulated across {files} file(s)")
    return 0


def selftest() -> int:
    fail = 0
    cases = [
        ("f : ℕ → ℕ", False, "arithmetic definition keeps its body"),
        ("okB : Caps → Bool", False, "decision procedure keeps its body"),
        ("Stream : ∀ {n} → Ctx n → Ty → Set", False, "type family keeps its body"),
        ("k≤3^k : ∀ k → k ≤ 3 ^ k", True, "an inequality is a proof"),
        ("∧-true : ∀ (a b : Bool) → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)",
         True, "an equation under an arrow is a proof"),
        ("absurd : Foo → ⊥", True, "a refutation is a proof"),
        ("g : (x ≡ y) → ℕ", False,
         "a PROPOSITION IN AN ARGUMENT is not a proof — only the result counts"),
    ]
    for sig, want, why in cases:
        got = is_proof(sig)
        if got != want:
            print(f"SELFTEST FAIL: {sig!r} -> {got}, wanted {want} ({why})")
            fail = 1
    if not fail:
        print("stub-proofs-selftest: PASS (a result type mentioning ≡/≤/</⊥ is a "
              "proof; Bool, ℕ and Set results are definitions and keep their "
              "bodies; a proposition appearing only in an ARGUMENT does not make "
              "the declaration a proof, which is what keeps the decision "
              "procedures the probes compute with)")
    return fail


if __name__ == "__main__":
    raise SystemExit(main())
