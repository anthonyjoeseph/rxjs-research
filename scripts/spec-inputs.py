#!/usr/bin/env python3
"""The files `make spec-check` reads: quickcheck/Spec-Check.agda's import
closure inside agda-impl, plus the Makefile and the toolchain script.

  scripts/spec-inputs.py           list them
  scripts/spec-inputs.py --hash    one sha256 over their paths and contents

CI keys a "spec-check was green" marker on the hash, so the run is skipped
when nothing it compiles has changed. Over-inclusion is safe (a commented
import only costs a run); under-inclusion is not, so any `import` token
naming a file of the tree counts.
"""
import hashlib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "agda-impl"
ENTRY = SRC / "quickcheck" / "Spec-Check.agda"
EXTRA = [ROOT / "Makefile", ROOT / "scripts" / "install-agda.sh"]

IMPORT = re.compile(r"\bimport\s+([^\s;(){}]+)")


def closure():
    seen, todo = set(), [ENTRY]
    while todo:
        f = todo.pop()
        if f in seen:
            continue
        seen.add(f)
        for m in IMPORT.finditer(f.read_text(encoding="utf-8")):
            g = SRC.joinpath(*m.group(1).split(".")).with_suffix(".agda")
            if g.is_file():
                todo.append(g)
    return sorted(seen) + EXTRA


def main():
    files = closure()
    if "--hash" in sys.argv[1:]:
        h = hashlib.sha256()
        for f in files:
            h.update(str(f.relative_to(ROOT)).encode() + b"\0")
            h.update(f.read_bytes() + b"\0")
        print(h.hexdigest())
    else:
        for f in files:
            print(f.relative_to(ROOT))


if __name__ == "__main__":
    main()
