#!/usr/bin/env python3
"""Rewrite Agda output about the stripped mirror back onto the real sources.

`scripts/strip-comments.py` DELETES full-line comments, so a position in
`agda/_stripped-comments/src/Foo.agda` names a different line than the same
position in `agda/src/Foo.agda`.  This filter maps them back, using the
sidecar `.linemap.json` the stripper writes: mirror line n is source line
`kept[n-1]`.  Exact, never a guess.

COLUMNS ARE UNTOUCHED, and that is not luck: the stripper only ever deletes
WHOLE lines, so no surviving line's contents shift.

THE LINE/COLUMN SEPARATOR IS EITHER A DOT OR A COMMA, and matching only one of
them is the worst failure this filter has: the path half still rewrites, so the
MIRROR's line number arrives attached to the SOURCE's path and reads as a
perfectly ordinary position.  That is a live wrong line rather than a stale
one -- it resolves, points at unrelated code, and is believed.  `--selftest`
pins both spellings for exactly that reason.

A STREAMING FILTER, deliberately.  Agda's progress (`Checking …`) has to reach
the log as it happens — `make bg-check` reports progress by tailing it, and a
buffered filter would leave a live build looking hung.  It also never swallows
an exit code: it is a filter, and the caller keeps agda's status out of band
(see the `agda` recipe, which stashes `$?` in a temp file before the pipe).
"""

import json
import os
import re
import sys

MIRROR = "_stripped-comments"

# path[:L,C[-L,C | -C]]  — Agda's Range printer, all three shapes
POS = re.compile(
    r"(?P<path>[^\s:()\[\]]*" + re.escape(MIRROR) + r"/[^\s:()\[\]]*\.agda)"
    r"(?::(?P<l1>\d+)(?P<s1>[.,])(?P<c1>\d+)"
    r"(?:-(?:(?P<l2>\d+)(?P<s2>[.,]))?(?P<c2>\d+))?)?"
)


def load_map(root):
    path = os.path.join(root, ".linemap.json")
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return {}


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    root = os.path.abspath(os.path.join(here, "..", "agda", MIRROR))
    fix = _fixer(load_map(root))

    for line in sys.stdin:
        sys.stdout.write(POS.sub(fix, line))
        sys.stdout.flush()


def selftest() -> int:
    """Does the filter still MOVE a position?  A pass-through reads as success
    everywhere else, so this asserts the mapped line DIFFERS from the mirror's
    -- the property that was silently false while the path half kept working."""
    root = os.path.abspath(os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "..", "agda", MIRROR))
    linemap = load_map(root)
    if not linemap:
        print("SELFTEST FAIL: no .linemap.json — run `make stripped` first")
        return 1

    # a file the stripper actually shortened, so mirror line != source line
    victim = next((rel for rel, kept in linemap.items()
                   if len(kept) > 3 and kept[3] != 4), None)
    if victim is None:
        print("SELFTEST FAIL: no stripped file to test against")
        return 1
    want = linemap[victim][3]

    fail = 0
    for sep in (".", ","):
        for tail, desc in ((f"4{sep}6-13", "one-line range"),
                           (f"4{sep}6-4{sep}9", "two-line range"),
                           (f"4{sep}6", "bare position")):
            line = f"/x/agda/{MIRROR}/{victim}:{tail}: error: [T]\n"
            got = POS.sub(_fixer(linemap), line)
            if MIRROR in got:
                print(f"SELFTEST FAIL: mirror path survived ({sep!r}, {desc})")
                fail = 1
            if f":{want}{sep}6" not in got:
                print(f"SELFTEST FAIL: line not mapped to {want} "
                      f"({sep!r}, {desc}) — got {got.strip()}")
                fail = 1
    if not fail:
        print("unmap-selftest: OK — both separators map, path and line")
    return fail


def _fixer(linemap):
    """`main`'s substitution, reusable by the selftest."""
    def src_line(rel, n):
        kept = linemap.get(rel)
        if not kept or n < 1 or n > len(kept):
            return n
        return kept[n - 1]

    def fix(m):
        path = m.group("path")
        i = path.find(MIRROR + "/")
        rel = path[i + len(MIRROR) + 1:]
        out = path[:i] + rel
        if m.group("l1") is None:
            return out
        out += f":{src_line(rel, int(m.group('l1')))}{m.group('s1')}{m.group('c1')}"
        if m.group("c2") is not None:
            if m.group("l2") is not None:
                out += (f"-{src_line(rel, int(m.group('l2')))}"
                        f"{m.group('s2')}{m.group('c2')}")
            else:
                out += f"-{m.group('c2')}"
        return out
    return fix


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        sys.exit(selftest())
    main()
