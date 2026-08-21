#!/usr/bin/env python3
"""Mirror agda/src + agda/evidence into agda/_stripped-comments/ with every
FULL-LINE `--` comment blanked, so that a comment-only edit does not change
what Agda checks and therefore does not invalidate a single interface.

WHY A MIRROR AND NOT AN IN-PLACE STRIP.  A long build here is detached and
sometimes killed.  An in-place strip that is interrupted leaves the real tree
comment-free, recoverable only from git.  The mirror has no such window, and
it needs no restore step at all.

WHY THIS IS SAFE, which is the whole question, since a wrong strip typechecks
a DIFFERENT program and reports green:

  * ONLY FULL-LINE COMMENTS.  The line's first non-whitespace run must be the
    dashes.  So the `--` is unambiguously at a token start — `x--y` is one
    identifier and can never match.  Inline trailing comments are left alone.
  * THE DASH RULE IS AGDA'S, NOT A GUESS.  A line comment is two-or-more
    dashes followed by end-of-line or a NON-symbol character; `-->` and `--|`
    are operators, not comments.  SYMBOLS below is a deliberate SUPERSET of
    Agda's symbol set: over-listing a character means declining to strip, so
    every error in that table errs toward doing nothing.
  * FILES WITH A BLOCK COMMENT ARE COPIED VERBATIM.  A `{- … -}` (as opposed
    to a `{-# … #-}` pragma) makes "is this line inside a comment already?"
    and "is this inside a string literal?" real questions.  Rather than answer
    them, skip the file.  Measured 2026-08-18: FOUR non-pragma `{-` in the
    whole tree, three of them `{- WF -}` markers inside generated program
    text, against 16,510 full-line comments.  The exclusion costs nothing.
  * AGDA HAS NO MULTI-LINE STRING LITERAL, so a line that starts with `--`
    cannot be inside one.  That is what makes the line-local rule sound.

WHY THE LINES ARE DELETED AND NOT BLANKED.  Blanking preserves line numbers
for free, and buys almost nothing: ADDING or REMOVING a comment line still
changes the mirror by one empty line, so the cone still rebuilds — and adding
a `-- PROBED` or `-- DEAD ROUTE` line is the edit this exists to make free.
Deleting makes the mirror invariant under EVERY comment-only edit.

WHY THE LINE MAP IS A SIDECAR.  It has to be, and this is the design's one
real constraint: anything recorded INSIDE the mirror is part of what Agda
hashes, so a `-- source line 4711` marker would change whenever a comment is
added above it — making the mirror maximally sensitive to exactly the edits it
exists to absorb.  `.linemap.json` sits beside the tree, is never compiled,
and is free to churn.  `scripts/unmap-positions.py` spends it.

THE INVARIANT, asserted on every file on every run: output line i is
byte-identical to source line kept[i].  A bug can then only DROP a line, and a
dropped code line is a parse or scope error — loud, not silent.
"""

import argparse
import json
import os
import re
import sys
import tempfile

# A SUPERSET of Agda's symbol characters.  Erring long is erring safe: a
# character listed here that Agda does not treat as a symbol only means a
# comment goes unstripped.
SYMBOLS = set("-!#$%&*+./<=>?@\\^|~:;,'\"`")

LINE_COMMENT = re.compile(r"^[ \t]*(-{2,})(.?)")

# a `{-` that does NOT open a pragma
BLOCK_OPEN = re.compile(r"\{-(?!#)")


def strippable(line):
    """Is this whole line a `--` comment, by Agda's lexical rule?"""
    m = LINE_COMMENT.match(line)
    if not m:
        return False
    nxt = m.group(2)
    return nxt == "" or nxt not in SYMBOLS


def strip_text(text):
    """(stripped, kept, skip_reason).

    `kept` maps 1-based OUTPUT line -> 1-based SOURCE line, as a list.  It is
    None when the file was copied verbatim (the identity map).
    """
    if BLOCK_OPEN.search(text):
        return text, None, "block comment"
    lines = text.split("\n")
    out, kept = [], []
    for i, ln in enumerate(lines, start=1):
        if strippable(ln):
            continue
        out.append(ln)
        kept.append(i)

    # THE INVARIANT.  Never silently trust the rule above.
    assert len(out) == len(kept)
    for j, src_i in enumerate(kept):
        assert out[j] == lines[src_i - 1], (
            f"output line {j + 1} is not source line {src_i}")
    return "\n".join(out), kept, None


def agda_files(root):
    for dirpath, _dirs, names in os.walk(root):
        for n in sorted(names):
            if n.endswith(".agda"):
                yield os.path.join(dirpath, n)


def sync(agda_dir, roots, dest, verbose=False):
    written = skipped = unchanged = 0
    wanted, linemap = set(), {}
    for root in roots:
        src_root = os.path.join(agda_dir, root)
        for path in agda_files(src_root):
            rel = os.path.relpath(path, agda_dir)
            out_path = os.path.join(dest, rel)
            wanted.add(os.path.abspath(out_path))
            with open(path, encoding="utf-8") as fh:
                text = fh.read()
            stripped, kept, reason = strip_text(text)
            if reason:
                skipped += 1
                if verbose:
                    print(f"  verbatim ({reason}): {rel}")
            else:
                linemap[rel] = kept
            # Write only on a real change: an identical write is churn, and
            # churn is the one thing this tool exists to avoid.
            old = None
            if os.path.exists(out_path):
                with open(out_path, encoding="utf-8") as fh:
                    old = fh.read()
            if old == stripped:
                unchanged += 1
                continue
            os.makedirs(os.path.dirname(out_path), exist_ok=True)
            with open(out_path, "w", encoding="utf-8") as fh:
                fh.write(stripped)
            written += 1

    # A source file that is gone must not linger in the mirror, or `make agda`
    # keeps compiling a module the tree no longer has.
    # Walk only the mirrored ROOTS, never `dest` wholesale: the mirror also
    # hosts `_dev` (agda-dev's generated modules) and `_build`, and neither is
    # in `wanted`.  A wholesale walk deletes the dev loop's modules on every
    # strip -- which is every run.
    removed = 0
    for root in roots:
        for dirpath, _dirs, names in os.walk(os.path.join(dest, root)):
          for n in names:
              if not n.endswith(".agda"):
                  continue
              p = os.path.abspath(os.path.join(dirpath, n))
              if p not in wanted:
                  os.remove(p)
                  removed += 1

    # AND ITS INTERFACE, WHICH DOES NOT LIVE BESIDE IT.  Agda 2.8 keeps
    # interfaces in `_build/<ver>/agda/<rel>.agdai`, so the obvious
    # `foo.agda -> foo.agdai` sibling -- which is what this used to delete --
    # names a path no interface has ever occupied: the prune above removed the
    # source and left the interface, on every deletion this repo has ever made.
    # An interface whose source is gone is not merely stale, it CRASHES the
    # build: agda reports `__IMPOSSIBLE__` out of Imports.hs rather than any
    # diagnosis, so the orphan is invisible right up to the point where it
    # costs a full gate.  Hence a SWEEP of the whole cache and not a
    # this-run delta: the accumulated orphans were dropped by earlier runs,
    # and no run that removes nothing would ever revisit them.
    # `_dev` is exempt -- agda-dev generates and discards modules by design,
    # and its interfaces are the cache that makes the loop fast.
    # The interface root is `_build/<ver>/agda`, and it is found by WALKING to
    # it rather than by splitting the path on "agda": every checkout has an
    # `agda/` directory further left, so a leftmost split resolves `rel`
    # against the wrong root and reports every interface as an orphan.  The
    # selftest below pins this; it caught exactly that, having first cost a
    # wiped 47M cache.
    build = os.path.join(dest, "_build")
    for ver in sorted(os.listdir(build) if os.path.isdir(build) else []):
        iface = os.path.join(build, ver, "agda")
        if not os.path.isdir(iface):
            continue
        for dirpath, dirs, names in os.walk(iface):
            dirs[:] = [d for d in dirs if d != "_dev"]
            for n in names:
                if not n.endswith(".agdai"):
                    continue
                q = os.path.join(dirpath, n)
                rel = os.path.relpath(q, iface)[: -len(".agdai")]
                if not os.path.exists(os.path.join(dest, rel + ".agda")):
                    os.remove(q)
                    removed += 1

    # THE SIDECAR.  Never inside the mirror — see the module docstring.
    with open(os.path.join(dest, ".linemap.json"), "w", encoding="utf-8") as fh:
        json.dump(linemap, fh)

    # THE LIBRARY FILES, MIRRORED RATHER THAN GENERATED.  Their include paths
    # ARE the src/evidence boundary (EVIDENCE.md, E1): `rxjs-research.agda-lib`
    # says `include: src` and nothing else, so from src's side the names
    # `Refuted.*` and `Probed.*` do not exist.  Generating the mirror's lib
    # from `roots` -- which is what this used to do -- would hand the MIRROR one
    # library spanning both trees, and the mirror is what Agda actually checks:
    # the boundary would then hold everywhere except where it counts.  Mirroring
    # the real files keeps it stated in exactly one place, and a third tree with
    # its own lib is covered the moment it lands.
    for dirpath, dirs, names in os.walk(agda_dir):
        dirs[:] = [d for d in dirs if not d.startswith("_")]
        for n in sorted(names):
            if not n.endswith(".agda-lib"):
                continue
            rel = os.path.relpath(os.path.join(dirpath, n), agda_dir)
            out_path = os.path.join(
                dest, os.path.dirname(rel),
                n[: -len(".agda-lib")] + "-stripped.agda-lib")
            with open(os.path.join(dirpath, n), encoding="utf-8") as fh:
                text = fh.read()
            text = re.sub(r"^(name:\s*)(\S+)", r"\1\2-stripped", text,
                          flags=re.MULTILINE)
            if not text.endswith("\n"):
                text += "\n"
            old = None
            if os.path.exists(out_path):
                with open(out_path, encoding="utf-8") as fh:
                    old = fh.read()
            if old != text:
                os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
                with open(out_path, "w", encoding="utf-8") as fh:
                    fh.write(text)
    return written, unchanged, skipped, removed


CASES = [
    # (input line, should_be_stripped)
    ("-- a comment", True),
    ("  -- indented comment", True),
    ("----------------", True),
    ("--", True),
    ("-- | doc-ish comment", True),
    ("a --> b", False),          # not full-line
    ("--> arrow at line start", False),   # `>` is a symbol: an operator
    ("--| bar", False),          # `|` is a symbol
    ("x--y = 3", False),         # dashes not at line start
    ("foo = bar -- trailing", False),     # inline: left alone by design
    ("{-# OPTIONS --safe #-}", False),
    ("", False),
    ("  ", False),
]


def selftest():
    bad = []
    for line, want in CASES:
        got = strippable(line)
        if got != want:
            bad.append(f"  {line!r}: expected stripped={want}, got {got}")

    # a file with a block comment is copied verbatim, dashes and all
    blocky = "{- a block -}\n-- a comment\ncode = 1\n"
    out, _kept, reason = strip_text(blocky)
    if reason is None or out != blocky:
        bad.append("  a file with a non-pragma `{-` must be copied verbatim")

    # a pragma does NOT count as a block comment
    prag = "{-# OPTIONS --guardedness #-}\n-- gone\ncode = 1\n"
    out, kept, reason = strip_text(prag)
    if reason is not None:
        bad.append("  `{-#` is a pragma, not a block comment")
    elif out != "{-# OPTIONS --guardedness #-}\ncode = 1\n":
        bad.append(f"  pragma file stripped wrong: {out!r}")
    elif kept != [1, 3, 4]:
        bad.append(f"  line map wrong for the pragma case: {kept}")

    # THE POINT OF THE WHOLE TOOL: inserting a comment line must not change
    # the stripped output at all.
    a = "a = 1\n-- x\nb = 2\n"
    b = "a = 1\n-- x\n-- BRAND NEW COMMENT\nb = 2\n"
    if strip_text(a)[0] != strip_text(b)[0]:
        bad.append("  adding a comment line changed the stripped output")
    if strip_text(a)[1] != [1, 3, 4] or strip_text(b)[1] != [1, 4, 5]:
        bad.append("  the line map did not follow the inserted comment")

    # THE ORPHAN SWEEP.  A deleted module's interface does NOT sit beside it,
    # and an orphan is a build CRASH rather than a stale read, so this case
    # pins the cache layout and not merely the intent.  `_dev` must survive:
    # agda-dev's modules are generated and discarded, and pruning their
    # interfaces would silently un-cache the fast loop.
    with tempfile.TemporaryDirectory() as tmp:
        agda_dir = os.path.join(tmp, "agda")
        dest = os.path.join(agda_dir, "_stripped-comments")
        os.makedirs(os.path.join(agda_dir, "src"))
        with open(os.path.join(agda_dir, "src", "Live.agda"), "w") as fh:
            fh.write("module Live where\n-- gone\nx = 1\n")
        with open(os.path.join(agda_dir, "rxjs.agda-lib"), "w") as fh:
            fh.write("name: t\ninclude: src\n")

        iface = os.path.join(dest, "_build", "2.8.0", "agda")
        for rel in ("src/Live", "src/Dead", "_dev/Scratch"):
            os.makedirs(os.path.join(iface, os.path.dirname(rel)), exist_ok=True)
            with open(os.path.join(iface, rel + ".agdai"), "w") as fh:
                fh.write("i")
        # a mirror source with no counterpart upstream: pruned, and its
        # interface with it -- the delta case
        os.makedirs(os.path.join(dest, "src"))
        with open(os.path.join(dest, "src", "Dead.agda"), "w") as fh:
            fh.write("module Dead where\n")
        # a _dev module the loop still owns
        os.makedirs(os.path.join(dest, "_dev"))
        with open(os.path.join(dest, "_dev", "Scratch.agda"), "w") as fh:
            fh.write("module Scratch where\n")

        sync(agda_dir, ["src"], dest)

        def there(*parts):
            return os.path.exists(os.path.join(iface, *parts))

        if there("src", "Dead.agdai"):
            bad.append("  a deleted module's interface survived the prune")
        if not there("src", "Live.agdai"):
            bad.append("  a live module's interface was pruned")
        if not there("_dev", "Scratch.agdai"):
            bad.append("  a _dev interface was pruned -- that un-caches agda-dev")
        if os.path.exists(os.path.join(dest, "src", "Dead.agda")):
            bad.append("  a deleted module survived in the mirror")
        if not os.path.exists(os.path.join(dest, "_dev", "Scratch.agda")):
            bad.append("  the dev loop's own module was deleted from the mirror")

    if bad:
        print("strip-comments selftest: FAIL")
        print("\n".join(bad))
        return 1
    print(f"strip-comments selftest: PASS ({len(CASES)} lexical cases, "
          "block-comment exclusion, pragma, line map, insert-invariance; and "
          "the interface orphan sweep reaches _build rather than the .agda's "
          "sibling, spares a live module and spares _dev)")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--agda-dir", default=None)
    ap.add_argument("--dest", default=None)
    ap.add_argument("--roots", nargs="*", default=["src", "evidence"])
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()

    if args.selftest:
        sys.exit(selftest())

    here = os.path.dirname(os.path.abspath(__file__))
    agda_dir = args.agda_dir or os.path.join(here, "..", "agda")
    agda_dir = os.path.abspath(agda_dir)
    dest = args.dest or os.path.join(agda_dir, "_stripped-comments")

    w, u, s, r = sync(agda_dir, args.roots, dest, args.verbose)
    print(f"strip-comments: {w} written, {u} unchanged, {s} verbatim "
          f"(block comment), {r} removed  ->  {os.path.relpath(dest, os.getcwd())}")


if __name__ == "__main__":
    main()
