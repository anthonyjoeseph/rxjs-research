#!/usr/bin/env python3
"""SEARCH FIRST, made cheap and impossible to scope wrong.

`make find Q='...'` searches the DECLARED TYPE of every definition and
postulate in the tree and prints the statements that match.

WHY THIS EXISTS RATHER THAN grep.  The repo's number-one recurring cost
is re-deriving a fact that is already proven, and `make dup-check`
catches that only AFTER both copies exist.  This is the same law applied
before the writing rather than after.  The two ways a grep has actually
failed here:

  * SCOPED WRONG.  On 2026-08-19 three lemmas were rewritten from
    scratch because the search was run against two named files instead
    of the tree.  This walks the whole of agda/src, always; there is no
    argument that narrows it.
  * SEARCHED FOR A NAME.  Names here are idiosyncratic
    (`frameStep-chain-suc` is a path-length lemma), so guessing one
    reliably misses.  This matches the TYPE — the conclusion's shape,
    which is the thing you actually know before you know the name.

Terms are ANDed and matched against the type text, so
`make find Q='slotSize sum'` finds the statements mentioning both.  A
term is also matched against the NAME, so a name you do half-remember
still works.

Output is the STATEMENT, not the matching line: what you need in order
to answer "does this already exist?" is the type, and reading a
signature is what the SEARCH FIRST rule asks for anyway.
"""
import os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from importlib import import_module
_dup = import_module("check-duplicates".replace("-", "_")) \
    if os.path.exists(os.path.join(HERE, "check_duplicates.py")) else None

if _dup is None:                                    # module name has a dash
    import importlib.util
    _spec = importlib.util.spec_from_file_location(
        "dupcheck", os.path.join(HERE, "check-duplicates.py"))
    _dup = importlib.util.module_from_spec(_spec)
    _spec.loader.exec_module(_dup)

SRC = _dup.SRC


def wrap(text, width, lead):
    out, line = [], ""
    for word in text.split(" "):
        if line and len(line) + 1 + len(word) > width:
            out.append(line)
            line = word
        else:
            line = (line + " " + word).strip()
    if line:
        out.append(line)
    return ("\n" + lead).join(out)


def main():
    terms = [a for a in sys.argv[1:] if a.strip()]
    if not terms:
        print("usage: make find Q='<term> [<term> ...]'")
        print("  searches the DECLARED TYPE of every definition in agda/src")
        return 2

    hits = []
    for dirpath, _, files in os.walk(SRC):
        for f in sorted(files):
            if not f.endswith(".agda"):
                continue
            path = os.path.join(dirpath, f)
            rel = os.path.relpath(path, SRC)
            for name, line, ty in _dup.declarations(path):
                flat = re.sub(r"\s+", " ", ty)
                hay = flat + " \x00" + name
                if all(t in hay for t in terms):
                    hits.append((rel, line, name, flat))

    hits.sort(key=lambda h: (h[0], h[1]))
    for rel, line, name, ty in hits:
        print("%s  %s:%d" % (name, rel, line))
        print("    %s" % wrap(ty, 92, "    "))
        print()
    print("find: %d statement(s) matching %s"
          % (len(hits), " AND ".join(repr(t) for t in terms)))
    if not hits:
        print("find: nothing — but try a SHORTER term, or the operator "
              "rather than the name.")
        print("      A miss here is weak evidence; a miss on two "
              "different phrasings is strong.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except BrokenPipeError:          # piped into `head`, which is normal
        os._exit(0)
