#!/usr/bin/env python3
"""Search the repo's PROSE by content and print the whole enclosing block.

`make find` searches declared TYPES and cannot see a finding.  A finding --
a dead route, a coverage boundary, a ruling, a measured trap -- lives in a
comment block or a markdown paragraph, and plain grep returns one line out
of a forty-line header, which is a hit and not an answer.  This returns the
BLOCK, which is the unit a finding is written in.

Searched: every comment block in `agda/src` and `agda/evidence`, and every
paragraph of the load-bearing documents.  An agda hit also prints the
declaration the block sits above, since that is what the finding is about.
"""
import importlib.util
import pathlib
import re
import sys


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# the comment-block parser is `check-comments.py`'s, not a copy of it: one
# definition of what a block IS, so the searcher and the checker cannot drift
blocks = _load("check_comments",
               pathlib.Path(__file__).resolve().parent / "check-comments.py").blocks

ROOT = pathlib.Path(__file__).resolve().parent.parent
AGDA_TREES = ["agda/src", "agda/evidence"]
DOCS = ["CLAUDE.md", "PROOF-STATE.md", "EVIDENCE.md",
        "typecheck-performance-numbers.md"]


def doc_blocks(path):
    """-> [(first_line_no, [line, ...])] — paragraphs, bullets and headings.

    Blank lines are not the only boundary: PROOF-STATE is one unbroken run of
    bullets per tier, so splitting on blanks alone returns a whole tier for a
    hit on one row.  A top-level `- ` or a `#` heading starts a new block.
    """
    out, cur, start = [], [], 0

    def flush():
        nonlocal cur
        if cur:
            out.append((start, cur))
        cur = []

    for n, line in enumerate(path.read_text().splitlines() + [""], 1):
        if not line.strip():
            flush()
            continue
        if cur and re.match(r"^(?:[-*+] |#{1,6} )", line):
            flush()
        if not cur:
            start = n
        cur.append(line)
    flush()
    return out


def declaration_after(lines, idx):
    """The first non-comment, non-blank line after a comment block."""
    for line in lines[idx:]:
        s = line.strip()
        if s and not s.startswith("--"):
            return s
    return None


def main():
    if len(sys.argv) < 2 or not sys.argv[1].strip():
        sys.exit("usage: make find-prose Q='<regex>'")
    try:
        pat = re.compile(sys.argv[1], re.IGNORECASE)
    except re.error as e:
        sys.exit(f"bad regex: {e}")

    hits = 0
    files = [p for d in AGDA_TREES for p in sorted((ROOT / d).rglob("*.agda"))]
    files += [ROOT / d for d in DOCS]
    files += sorted((ROOT / "docs").glob("*.md"))

    for path in files:
        if not path.exists():
            continue
        rel = path.relative_to(ROOT)
        agda = path.suffix == ".agda"
        lines = path.read_text().splitlines()
        for start, body in (blocks(path) if agda else doc_blocks(path)):
            if not any(pat.search(line) for line in body):
                continue
            hits += 1
            head = f"── {rel}:{start} "
            print(head + "─" * max(0, 78 - len(head)))
            if agda:
                decl = declaration_after(lines, start - 1 + len(body))
                if decl:
                    print(f"   ▸ {decl}")
            for line in body:
                print(f"   {line}" if agda else f"   {line.rstrip()}")
            print()

    # a zero-hit search is an ANSWER, not a failure -- the rule this serves
    # says a miss is weak evidence and two misses on different phrasings are
    # strong, so both are results and neither is an error
    print(f"find-prose: {hits} block(s) matching {sys.argv[1]!r} "
          f"in {len(files)} file(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
