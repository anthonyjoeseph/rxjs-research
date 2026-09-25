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

WHY THE LETS ARE REWRITTEN.  Agda SUBSTITUTES a `let`: `let (r , d) = E in b`
is `b` with `proj₁ E` and `proj₁ (proj₂ E)` in place of `r` and `d`, so E runs
once per component used -- and where E is the evaluator's own recursive call,
that is a factor at every level of nesting.  Here each such block becomes
`(E) ▷ₛ λ shareᵒ → let (r , d) = shareᵒ in b`: E is an ARGUMENT, evaluated
once, and the `let` only projects a variable.  The two are definitionally
equal (`▷ₛ` unfolds and beta-reduces to the original), and the proof never
sees the rewrite.  Only the RUNTIME modules are rewritten (SHARE_ROOTS): a
proof is never run, so rewriting one could only cost it its typing.

WHY ONLY THE CONE.  What the key hashes and what the tree holds are the same
set, so a module outside the runners' cone can never invalidate the oracle's
cache -- an edit to the proof leaves the binaries standing.  The files hashed
are the STRIPPED ones, so a comment edit invalidates nothing either.

  oracle-mirror.py --sync   write the tree (only files whose content changed)
  oracle-mirror.py --key    print the cache key: a hash of the cone as synced
  oracle-mirror.py --selftest   the let rewrite, against fixed cases
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MIRROR = os.path.join(REPO, "agda", "_stripped-comments", "src")
DEST = os.path.join(REPO, "agda", "_oracle")
ROOTS = ["CLI.Main", "Implementation.Unit-Test.Bug-Cache"]
PRAGMA = "{-# OPTIONS --erasure --no-termination-check #-}\n"
MARK, ERASED = "{-@0-}", "@0 "
SHARE_ROOTS = ("Rx" + os.sep, "Implementation")
SHARE_MODULE = "Oracle-Share"
SHARE_SRC = ("module Oracle-Share where\n\n"
             "open import Agda.Primitive using (Level)\n\n"
             "infixl 0 _▷ₛ_\n"
             "_▷ₛ_ : {a b : Level} {A : Set a} {B : Set b} → A → (A → B) → B\n"
             "x ▷ₛ f = f x\n")

LIB = ("name: rxjs-research-oracle\n"
       "include: src\n"
       "depend: standard-library-2.3\n"
       "flags: --guardedness\n")


LET = re.compile(r"(?:(?<=[\s(])|^)let(?=\s)")
IN = re.compile(r"(?:(?<=\s)|^)in(?=\s|$)")
VAR = "shareᵒ"
OP = "▷ₛ"


def _code(line):
    """The line with any trailing `--` comment blanked (length kept)."""
    m = re.search(r"(?:(?<=\s)|^)--(?:\s|$)", line)
    return line if not m else line[: m.start()] + " " * (len(line) - m.start())


def _indent(line):
    return len(line) - len(line.lstrip(" "))


def _pattern_end(text, i):
    depth = 0
    for j in range(i, len(text)):
        if text[j] == "(":
            depth += 1
        elif text[j] == ")":
            depth -= 1
            if depth == 0:
                return j + 1
    return None


def _block(code, i, kw):
    """The let block whose keyword is at (i, kw), or None if unsure:
    {c: binding column, spans: [(first, last) line of each binding],
     in: (line, col), in_alone: whether `in` opens its own line}."""
    c = kw + 3
    while c < len(code[i]) and code[i][c] == " ":
        c += 1
    if c >= len(code[i].rstrip()):
        return None
    starts, inpos, j = [i], None, i
    while j < len(code):
        l = code[j]
        if j > i:
            if l.strip() == "":
                j += 1
                continue
            ind = _indent(l)
            if ind < c:
                if IN.match(l, ind):
                    inpos = (j, ind)
                break
            if ind == c:
                starts.append(j)
        k = IN.search(l, c + 1 if j == i else c)
        if k:
            inpos = (j, k.start())
            break
        j += 1
    if inpos is None:
        return None
    ii, ic = inpos
    alone = ii != i and ic == _indent(code[ii])
    last = ii - 1 if alone else ii
    if alone and starts[-1] == ii:
        starts.pop()
    while last > starts[-1] and code[last].strip() == "":
        last -= 1
    spans = [(s, starts[t + 1] - 1 if t + 1 < len(starts) else last)
             for t, s in enumerate(starts)]
    for s, e in spans:
        for r in range(s, e + 1):
            seg = code[r]
            if r == ii:
                seg = seg[:ic]
            if r == i:
                seg = seg[c:]
            if LET.search(seg):
                return None  # a let inside a binding: left alone
    return {"c": c, "spans": spans, "in": inpos, "alone": alone}


def _rewrite(get, kw_at, b):
    """{line: new text} for one block, or None to leave it alone."""
    new = {}
    g = lambda r: new.get(r, get(r))
    c, spans = b["c"], b["spans"]
    ii, ic = b["in"]
    ki, kw = kw_at
    if c - 4 < kw:
        return None
    if not any(g(s)[c:].startswith("(") for s, _ in spans):
        return None
    l = g(ki)
    new[ki] = l[:kw] + "   " + l[kw + 3:]
    for s, e in spans:
        l = g(s)
        on_in = (not b["alone"]) and e == ii
        if l[c:].startswith("("):
            pe = _pattern_end(l, c)
            eq = pe and re.match(r"[ ]*=(?= |$)", l[pe:])
            if not eq:
                return None
            pat, rhs = l[c:pe], pe + eq.end()
            if l[rhs:].strip() == "":
                if s == e:
                    return None
                l2 = g(s + 1)
                col = _indent(l2)
                if col - 1 < c:
                    return None
                new[s] = l[:c] + " " * (len(l) - c)
                new[s + 1] = l2[: col - 1] + "(" + l2[col:]
            else:
                rhs += 1  # past the space after `=`
                if l[rhs - 1] != " ":
                    return None
                new[s] = l[:c] + " " * (rhs - 1 - c) + "(" + l[rhs:]
            tail = f") {OP} λ {VAR} → let {pat} = {VAR} in"
            le = g(e)
            new[e] = (le[:ic].rstrip() + " " + tail + le[ic + 2:]) if on_in \
                else (le.rstrip() + " " + tail)
        else:
            if l[c - 4:c].strip() != "":
                return None
            new[s] = l[: c - 4] + "let " + l[c:]
            if not on_in:
                new[e] = g(e).rstrip() + " in"
    if b["alone"]:
        l = g(ii)
        new[ii] = l[:ic] + "  " + l[ic + 2:]
    return new


def share_lets(text):
    """(text, n): each `let` block binding a tuple PATTERN, rewritten so every
    pattern's right-hand side is evaluated ONCE.

        let x = A                    let x = A in
            (r , d) = E      ==>              (E
                        more                    more) ▷ₛ λ shareᵒ → let (r , d) = shareᵒ in
        in body                         body

    An edit either blanks characters or appends at a line's end, except where
    a one-line `in` is replaced -- so every column a binding's right-hand side
    lays out against is kept, and blocks rewrite independently.  A block the
    parser is unsure of is left alone: there `let` is only slower."""
    lines = text.split("\n")
    code = [_code(l) for l in lines]
    edits, n = {}, 0
    for i, cl in enumerate(code):
        for m in LET.finditer(cl):
            b = _block(code, i, m.start())
            if b is None:
                continue
            new = _rewrite(lambda r: edits.get(r, lines[r]), (i, m.start()), b)
            if new is None:
                continue
            edits.update(new)
            n += 1
    return "\n".join(edits.get(i, l) for i, l in enumerate(lines)), n


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


def oracle_text(rel: str, text: str) -> str:
    """One cone module as the oracle compiles it."""
    text = text.replace(MARK, ERASED)
    if rel.startswith(SHARE_ROOTS):
        text, n = share_lets(text)
        if n:
            text = re.sub(r"^(module\s[^\n]*\bwhere[ \t]*)$",
                          rf"\1\nopen import {SHARE_MODULE} using (_{OP}_)",
                          text, count=1, flags=re.MULTILINE)
    return PRAGMA + text


def sync(files: dict[str, str]) -> None:
    src = os.path.join(DEST, "src")
    want = {os.path.join(src, rel): oracle_text(rel, text)
            for rel, text in files.items()}
    want[os.path.join(src, SHARE_MODULE + ".agda")] = PRAGMA + SHARE_SRC
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


SHARE_CASES = [
    # a block of two patterns, the second reading the first
    ("f x =\n"
     "  let (a , b) = g x\n"
     "      (c , d) = h a\n"
     "                  b\n"
     "  in a , c",
     "f x =\n"
     "               (g x ) ▷ₛ λ shareᵒ → let (a , b) = shareᵒ in\n"
     "               (h a\n"
     "                  b ) ▷ₛ λ shareᵒ → let (c , d) = shareᵒ in\n"
     "     a , c"),
    # a plain binding stays a `let`, and keeps its column
    ("f x =\n"
     "  let y = k x\n"
     "      (a , b) = g y\n"
     "  in a",
     "f x =\n"
     "  let y = k x in\n"
     "               (g y ) ▷ₛ λ shareᵒ → let (a , b) = shareᵒ in\n"
     "     a"),
    # the one-line form
    ("f x = let (a , b) = g x in a + b",
     "f x =              (g x ) ▷ₛ λ shareᵒ → let (a , b) = shareᵒ in a + b"),
    # nothing to share: left exactly alone
    ("f x = let y = k x in y", "f x = let y = k x in y"),
    # a `let` inside a binding: the parser declines rather than guesses
    ("f x =\n  let (a , b) = let y = k x in g y\n  in a",
     "f x =\n  let (a , b) = let y = k x in g y\n  in a"),
]


def selftest() -> int:
    bad = [f"  {src!r}\n    got  {share_lets(src)[0]!r}\n    want {want!r}"
           for src, want in SHARE_CASES if share_lets(src)[0] != want]
    if bad:
        print("oracle-mirror selftest: FAIL\n" + "\n".join(bad))
        return 1
    print(f"oracle-mirror selftest: PASS ({len(SHARE_CASES)} let-sharing cases)")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--sync", action="store_true")
    g.add_argument("--key", action="store_true")
    g.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    files = cone()
    if a.sync:
        sync(files)
        marks = sum(t.count(MARK) for t in files.values())
        lets = sum(share_lets(t)[1] for r, t in files.items()
                   if r.startswith(SHARE_ROOTS))
        print(f"oracle-mirror: {len(files)} modules in the runners' cone, "
              f"{marks} erasure markers, {lets} let blocks shared")
    else:
        print(key(files))
    return 0


if __name__ == "__main__":
    sys.exit(main())
