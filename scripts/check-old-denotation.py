#!/usr/bin/env python3
"""THE OLD DENOTATION, COUNTED (Anthony): Tier 0 is done when nothing
outside the old denotation reaches it.  The emission set (`denotation/EmissionSet`) is
the meaning; the stream denotation is what Tier 0 ports away from.

The old denotation is

  * every name of the modules given by `--module`: the denotation and
    nothing else, so any import of one is a use;
  * in the modules given by `--host`, the operator library: every name
    ending in `ᴰ`, and the names given by `--name`.  The rest of a host
    (the runs the engine shows, their agreement) is the engine's
    vocabulary, not the denotation's.

A use is an import of an old module, a host import naming an old name, a
host imported with no `using` (which takes the old names wholesale), or a
qualified `X.name` through a host imported `as X`.  The old modules and
the hosts themselves are not scanned: they are the old denotation.

Textual, like the other checkers.  Exits 1 while any use remains, so the
count is the remaining work, by file.

Usage:
    scripts/check-old-denotation.py [--src DIR] --module M ... --host M ... [--name N ...]
"""

import argparse
import os
import re
import sys
from collections import defaultdict

IMPORT_RE = re.compile(r"^\s*(?:open\s+)?import\s+([^\s;()]+)(.*)$")


def statements(lines):
    """Each import statement with the line it starts on, a `using` list
    that runs over several lines joined into one."""
    i = 0
    while i < len(lines):
        m = IMPORT_RE.match(lines[i])
        if not m:
            i += 1
            continue
        start, text = i, lines[i]
        while text.count("(") > text.count(")") and i + 1 < len(lines):
            i += 1
            text += " " + lines[i].strip()
        yield start + 1, IMPORT_RE.match(text)
        i += 1


def old_name(n, names):
    return n.endswith("ᴰ") or n in names


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", default="agda-impl")
    ap.add_argument("--module", nargs="+", required=True, help="modules that are wholly the old denotation")
    ap.add_argument("--host", nargs="*", default=[], help="modules whose ᴰ operators (and --name) are")
    ap.add_argument("--name", nargs="*", default=[], help="further old names in a host")
    a = ap.parse_args()
    modules, hosts, names = set(a.module), set(a.host), set(a.name)
    skip = {m.replace(".", "/") + ".agda" for m in modules | hosts}

    found = defaultdict(list)
    for root, _, fs in os.walk(a.src):
        for f in sorted(fs):
            if not f.endswith(".agda"):
                continue
            rel = os.path.relpath(os.path.join(root, f), a.src)
            if rel in skip:
                continue
            with open(os.path.join(root, f), encoding="utf-8") as fh:
                lines = fh.read().split("\n")
            aliases = set()
            for line, m in statements(lines):
                mod, rest = m.group(1), m.group(2)
                if mod in modules:
                    found[rel].append(f"{rel}:{line}: imports `{mod}`")
                    continue
                if mod not in hosts:
                    continue
                alias = re.search(r"\bas\s+(\S+)", rest)
                using = re.search(r"\busing\s*\(([^)]*)\)", rest)
                if alias:
                    aliases.add(alias.group(1))
                if using:
                    for n in (x.strip() for x in using.group(1).split(";")):
                        if old_name(n, names):
                            found[rel].append(f"{rel}:{line}: takes `{n}` from `{mod}`")
                elif not alias:
                    found[rel].append(f"{rel}:{line}: opens `{mod}` with no `using`")
            for x in aliases:
                for i, l in enumerate(lines):
                    for n in re.findall(re.escape(x) + r"\.([^\s()]+)", l):
                        if old_name(n, names):
                            found[rel].append(f"{rel}:{i + 1}: uses `{x}.{n}`")

    total = sum(len(v) for v in found.values())
    for rel in sorted(found):
        for line in found[rel]:
            print(line)
    if total:
        print(f"old-denotation: {total} use(s) across {len(found)} file(s); Tier 0 is done at none")
        sys.exit(1)
    print("old-denotation: clean — nothing outside the old denotation reaches it")


if __name__ == "__main__":
    main()
