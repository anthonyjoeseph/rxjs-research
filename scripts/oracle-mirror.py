#!/usr/bin/env python3
"""The oracle's own Agda tree: the import CONE of its two runners, copied out
of the comment-stripped mirror with termination checking switched off and the
erasure markers made real.

WHY A SEPARATE TREE.  The oracle checks the evaluator's VALUES against rxjs,
not the proof, so it has no use for the termination check -- the tower pays
that, in the gate.  But an option is part of what an interface records, so
building the runners with it off inside the gate's mirror would leave that
mirror's cache alternating between two builds.  A tree of its own, under its
own `.agda-lib`, has its own `_build` and touches nothing the gate reads.

WHY A PRAGMA PER FILE AND NOT A COMMAND-LINE FLAG.  A flag reaches every module
the run loads, the standard library included, and the stdlib's interfaces are
shared with every other build on the machine.  A pragma is scoped to the file
it heads, so only this tree's modules are affected.

WHY THE MARKERS ARE COMMENTS IN `src`.  `{-@0-}` sits exactly where an `@0`
would go -- `({-@0-}le : lo ≤ ℓ)`, `→ {-@0-}Acc _<_ m →` -- and the proof never
sees it: to the gate it is a comment, so `src` stays under the options it has
and the tower checks what it always checked.  Here it becomes `@0 `, under
`--erasure`, so the compiled runners stop building and carrying the proof
terms a marked binder holds.  A marker the oracle's check rejects is one
placed on a binder the evaluator's VALUES read: the build says so by name.

WHY ONLY THE CONE.  What the key hashes and what the tree holds are the same
set, so a module outside the runners' cone can never invalidate the oracle's
cache -- an edit to the proof leaves the binaries standing.  The files hashed
are the STRIPPED ones, so a comment edit invalidates nothing either.

  oracle-mirror.py --sync   write the tree (only files whose content changed)
  oracle-mirror.py --key    print the cache key: a hash of the cone as synced
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import os
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MIRROR = os.path.join(REPO, "agda", "_stripped-comments", "src")
DEST = os.path.join(REPO, "agda", "_oracle")
ROOTS = ["CLI.Main", "Implementation.Unit-Test.Bug-Cache"]
PRAGMA = "{-# OPTIONS --erasure --no-termination-check #-}\n"
MARK, ERASED = "{-@0-}", "@0 "
LIB = ("name: rxjs-research-oracle\n"
       "include: src\n"
       "depend: standard-library-2.3\n"
       "flags: --guardedness\n")


def _check_imports():
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "check-imports.py")
    spec = importlib.util.spec_from_file_location("_check_imports", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def cone() -> dict[str, str]:
    """Module-relative path -> stripped content, for every module the roots reach."""
    ci = _check_imports()
    out, stack = {}, list(ROOTS)
    while stack:
        mod = stack.pop()
        rel = mod.replace(".", os.sep) + ".agda"
        path = os.path.join(MIRROR, rel)
        if rel in out or not os.path.isfile(path):
            continue  # already seen, or not ours (the stdlib)
        text = open(path, encoding="utf-8").read()
        out[rel] = text
        stack += [d.mod for d in ci.parse(ci.strip_comments_checked(text))]
    missing = [r for r in ROOTS if r.replace(".", os.sep) + ".agda" not in out]
    if missing:
        sys.exit(f"oracle-mirror: no mirror file for {missing} -- run `make stripped` first")
    return out


def oracle_text(text: str) -> str:
    """One cone module as the oracle compiles it."""
    return PRAGMA + text.replace(MARK, ERASED)


def sync(files: dict[str, str]) -> None:
    src = os.path.join(DEST, "src")
    want = {os.path.join(src, rel): oracle_text(text)
            for rel, text in files.items()}
    for path, text in want.items():
        if os.path.isfile(path) and open(path, encoding="utf-8").read() == text:
            continue
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            f.write(text)
    for root, _, fs in os.walk(src):
        for f in fs:
            p = os.path.join(root, f)
            if f.endswith(".agda") and p not in want:
                os.remove(p)
    lib = os.path.join(DEST, "rxjs-research-oracle.agda-lib")
    if not os.path.isfile(lib) or open(lib).read() != LIB:
        with open(lib, "w") as f:
            f.write(LIB)


def key(files: dict[str, str]) -> str:
    h = hashlib.sha256()
    for extra in ("scripts/oracle-mirror.py", "scripts/install-agda.sh"):
        h.update(open(os.path.join(REPO, extra), "rb").read())
    for rel in sorted(files):
        h.update(rel.encode() + b"\0" + files[rel].encode() + b"\0")
    return h.hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser()
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--sync", action="store_true")
    g.add_argument("--key", action="store_true")
    a = ap.parse_args()
    files = cone()
    if a.sync:
        sync(files)
        marks = sum(t.count(MARK) for t in files.values())
        print(f"oracle-mirror: {len(files)} modules in the runners' cone, "
              f"{marks} erasure markers")
    else:
        print(key(files))
    return 0


if __name__ == "__main__":
    sys.exit(main())
