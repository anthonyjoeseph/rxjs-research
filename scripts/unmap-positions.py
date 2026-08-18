#!/usr/bin/env python3
"""Rewrite Agda output about the stripped mirror back onto the real sources.

`scripts/strip-comments.py` DELETES full-line comments, so a position in
`agda/_stripped-comments/src/Foo.agda` names a different line than the same
position in `agda/src/Foo.agda`.  This filter maps them back, using the
sidecar `.linemap.json` the stripper writes: mirror line n is source line
`kept[n-1]`.  Exact, never a guess.

COLUMNS ARE UNTOUCHED, and that is not luck: the stripper only ever deletes
WHOLE lines, so no surviving line's contents shift.

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
    r"(?::(?P<l1>\d+),(?P<c1>\d+)"
    r"(?:-(?:(?P<l2>\d+),)?(?P<c2>\d+))?)?"
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
    linemap = load_map(root)

    def src_line(rel, n):
        kept = linemap.get(rel)
        if not kept or n < 1 or n > len(kept):
            return n          # verbatim file, or a position we cannot place
        return kept[n - 1]

    def fix(m):
        path = m.group("path")
        i = path.find(MIRROR + "/")
        rel = path[i + len(MIRROR) + 1:]           # e.g. src/Rx/Prim.agda
        out = path[:i] + rel
        if m.group("l1") is None:
            return out
        l1 = src_line(rel, int(m.group("l1")))
        out += f":{l1},{m.group('c1')}"
        if m.group("c2") is not None:
            if m.group("l2") is not None:
                out += f"-{src_line(rel, int(m.group('l2')))},{m.group('c2')}"
            else:
                out += f"-{m.group('c2')}"
        return out

    for line in sys.stdin:
        sys.stdout.write(POS.sub(fix, line))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
