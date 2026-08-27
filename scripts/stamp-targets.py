#!/usr/bin/env python3
"""Write the statement fingerprint onto every unstamped `-- TARGET:`.

ADOPTION ONLY, and it is deliberately not a `make` target.  A stamp is a
CLAIM that the rows below were taken against the statement as it now reads,
and a tool that writes claims on your behalf is exactly the reflex E5 exists
to forbid.  It is here so the fifty-odd targets that predate the check can be
brought under it in one pass, after the ones known to be stale have been
dealt with by hand.  Everything afterwards is stamped by whoever writes the
probe, who is the only party who knows whether the claim is true.
"""

import importlib.util
import io
import os
import sys

here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location(
    "ev", os.path.join(here, "check-evidence.py"))
ev = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ev)


def main():
    stmts = ev.statements("agda/src")
    roots = [os.path.join("agda/evidence", d) for d in ev.NAMESPACES]
    roots.append("agda/src/Harness")
    skip = set(sys.argv[1:])
    wrote = 0
    for root in roots:
        if not os.path.isdir(root):
            continue
        for path in ev.agda_files(root):
            if os.path.basename(path) in skip:
                continue
            lines = io.open(path, encoding="utf-8").read().split("\n")
            hit = False
            for i, line in enumerate(lines):
                m = ev.TARGET.match(line)
                if not m or ev.STAMP.match(m.group(1)):
                    continue
                name = m.group(1).split()[0]
                fp = stmts.get(name)
                if fp is None:
                    continue
                lines[i] = line.replace(m.group(1), f"{name} @{fp}")
                hit = True
            if hit:
                io.open(path, "w", encoding="utf-8").write("\n".join(lines))
                wrote += 1
    print(f"stamp-targets: stamped targets in {wrote} file(s)")


if __name__ == "__main__":
    main()
