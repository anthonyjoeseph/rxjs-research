#!/usr/bin/env python3
"""Hold the two trees' former sets to one written-down correspondence.

The Agda tree and the TypeScript tree carry the same object language, and
what tied them together was a tag string the decoder matched and the
generator happened to emit.  Nothing failed when they diverged: a former
only one tree had was simply never generated, so the oracle and the
all-Agda sweep both reported green over shapes neither was ever handed.

`scripts/formers.tsv` is the one declaration of the pairing, and this
checks four surfaces against it, in both directions where both directions
are decidable:

  A  the Agda datatypes   agda/src/Rx/Exp.agda      `data Exp` / `Tm` / `PrimOp`
  B  the Agda decoder     agda/src/CLI/Decode.agda  `tag is "..."` / `op is "..."`
  C  the TypeScript types typescript/src/exp.ts     `export type Exp` / `Tm` / `PrimOp`
  D  the TS generator     typescript/src/generator.ts   `type: "..."`, the op lanes

A and C are checked BOTH ways -- they are closed declarations, so a former
present there and absent from the map is a finding, which is what catches a
former added to one tree alone.  B and D are checked one way only: the
decoder's file also carries the tags of types, inputs and primitive
operators, and the generator's file writes every one of those too, so
"a tag here that is not in the map" is the normal state of both and
asserting otherwise would report the whole type grammar.

D's direction is the one that costs something and the one the convention
never had: a former the generator cannot reach is covered by no sweep and
no oracle run whatever either reports, so the map's `gen` column is where
that hole is declared and counted, with its reason beside it.

The map's `role` column is the DIVIDING TEST's verdict, and the vocabulary
is closed below.  It is what stops a former's status from being a matter
of memory: the test decides which formers the one pure-function former
absorbs, and before this it was answerable only by whoever had last
thought about it, so a former added later owed no answer at all.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

PATHS = {
    "agda": "agda/src/Rx/Exp.agda",
    "decode": "agda/src/CLI/Decode.agda",
    "ts": "typescript/src/exp.ts",
    "gen": "typescript/src/generator.ts",
}


# THE DIVIDING TEST'S ANSWERS, and the vocabulary is closed on purpose: a
# former whose status is none of these has not been measured against the
# test, and inventing a word for it here is how that goes unnoticed.
ROLES = {
    "source": "produces without reading anything, and subscribes nothing",
    "lift": "a pure function of an emit's values, with carried state",
    "protocol": "reads or writes the protocol's own bookkeeping",
    "flatten": "subscribes a payload that is literal syntax and must be RUN",
    "binder": "not an operator at all -- μ-binding structure",
}


class Row:
    __slots__ = ("kind", "agda", "tag", "gen", "role", "why")

    def __init__(self, kind: str, agda: str, tag: str, gen: bool, role: str, why: str) -> None:
        self.kind, self.agda, self.tag, self.gen = kind, agda, tag, gen
        self.role, self.why = role, why


def read_map(path: Path) -> list[Row]:
    rows: list[Row] = []
    seen_agda: dict[str, int] = {}
    seen_tag: dict[str, int] = {}
    for n, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 5:
            sys.exit(f"check-formers: {path}:{n}: want 5+ tab-separated fields, got {len(parts)}")
        kind, agda, tag, gen, role = (p.strip() for p in parts[:5])
        why = parts[5].strip() if len(parts) > 5 else ""
        if kind not in ("exp", "tm", "prim"):
            sys.exit(f"check-formers: {path}:{n}: kind must be exp, tm or prim, got {kind!r}")
        if gen not in ("yes", "no"):
            sys.exit(f"check-formers: {path}:{n}: gen must be yes or no, got {gen!r}")
        if kind == "exp" and role not in ROLES:
            sys.exit(
                f"check-formers: {path}:{n}: `{agda}` has no verdict under the dividing test -- "
                f"role must be one of {', '.join(sorted(ROLES))}, got {role!r}"
            )
        if kind != "exp" and role != "-":
            sys.exit(
                f"check-formers: {path}:{n}: `{agda}` is not a stream former, so the dividing "
                f"test does not apply to it -- its role must be `-`, got {role!r}"
            )
        if gen == "no" and not why:
            sys.exit(
                f"check-formers: {path}:{n}: gen=no needs a reason in the sixth field -- "
                "an unreachable former is a hole to state, not a box to tick"
            )
        for tbl, key in ((seen_agda, agda), (seen_tag, tag)):
            if key in tbl:
                sys.exit(f"check-formers: {path}:{n}: {key!r} already declared on line {tbl[key]}")
            tbl[key] = n
        rows.append(Row(kind, agda, tag, gen == "yes", role, why))
    return rows


# ---------------------------------------------------------------- surfaces


def agda_ctors(text: str, name: str) -> set[str]:
    """Constructors of `data <name> ... where`, by indentation.

    The block ends at the first line indented no further than the `data`
    itself, which is what keeps the siblings a `mutual` block puts beside it
    (`Fn`, `Val`) out of the set.
    """
    lines = text.splitlines()
    head = re.compile(r"^(\s*)data\s+" + re.escape(name) + r"\b.*\bwhere\s*$")
    for i, line in enumerate(lines):
        m = head.match(line)
        if not m:
            continue
        depth = len(m.group(1))
        out: set[str] = set()
        for rest in lines[i + 1 :]:
            if not rest.strip():
                continue
            indent = len(rest) - len(rest.lstrip())
            if indent <= depth:
                break
            body = rest.strip()
            if body.startswith("--"):
                continue
            # several constructors may SHARE one signature (`a b : T`), which
            # is how two of the flatteners are declared -- taking the first
            # name only reported the others as deleted
            c = re.match(r"((?:[^\s:(){}]+\s+)*[^\s:(){}]+)\s*:(?!=)", body)
            if c:
                out.update(c.group(1).split())
        return out
    sys.exit(f"check-formers: no `data {name} ... where` found -- the datatype moved or was renamed")


def ts_union(text: str, name: str) -> set[str]:
    # to the first blank line, and NOT anchored to the union starting on the
    # line below its own `=`: both layouts are ordinary TypeScript, and a
    # checker that reads only the repo's current one is a checker the
    # formatter can silence
    m = re.search(r"^export type " + re.escape(name) + r"\s*=(.*?)(?:\n[ \t]*\n|\Z)", text, re.M | re.S)
    if not m:
        sys.exit(f"check-formers: no `export type {name} =` block found -- the union moved or was renamed")
    return set(re.findall(r'type:\s*"([A-Za-z]+)"', m.group(1)))


def ts_string_union(text: str, name: str) -> set[str]:
    """`export type PrimOp = "add" | "sub" | …;` -- a union of BARE STRINGS.

    The primitive operators are spelled that way rather than as tagged
    objects, so the object-union reader above finds nothing in them and
    would report the whole family missing.
    """
    m = re.search(r"^export type " + re.escape(name) + r"\s*=(.*?);", text, re.M | re.S)
    if not m:
        sys.exit(f"check-formers: no `export type {name} =` found -- the union moved or was renamed")
    return set(re.findall(r'"([A-Za-z]+)"', m.group(1)))


def gen_prim_lanes(text: str) -> set[str]:
    """Which primitive operators the generator can actually write.

    Two shapes, because an operator whose argument is not a nat pair is
    picked on its own rather than out of a list: the members of a
    `[…] as PrimOp[]` array, and any `op: "…"` written directly.  A bare
    scan for the quoted word would pass on the operator's name appearing
    anywhere in the file, which for `not` is every other line.
    """
    out: set[str] = set()
    for arr in re.findall(r"\[([^\]]*)\]\s*as PrimOp\[\]", text):
        out.update(re.findall(r'"([A-Za-z]+)"', arr))
    out.update(re.findall(r'op:\s*"([A-Za-z]+)"', text))
    return out


def quoted(text: str, pat: str) -> set[str]:
    return set(re.findall(pat, text))


# ---------------------------------------------------------------- the check


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=str(REPO), help="tree to check (the selftest points this at a fixture)")
    ap.add_argument("--map", default=None, help="the correspondence file (default: scripts/formers.tsv under --root)")
    args = ap.parse_args()

    root = Path(args.root)
    mp = Path(args.map) if args.map else root / "scripts" / "formers.tsv"
    if not mp.is_file():
        sys.exit(f"check-formers: no correspondence file at {mp}")
    rows = read_map(mp)

    src = {}
    for key, rel in PATHS.items():
        p = root / rel
        if not p.is_file():
            sys.exit(f"check-formers: missing {p}")
        src[key] = p.read_text(encoding="utf-8")

    findings: list[str] = []

    for kind, dname, uname in (("exp", "Exp", "Exp"), ("tm", "Tm", "Tm"), ("prim", "PrimOp", "PrimOp")):
        declared = {r.agda for r in rows if r.kind == kind}
        tags = {r.tag for r in rows if r.kind == kind}

        found = agda_ctors(src["agda"], dname)
        for extra in sorted(found - declared):
            findings.append(
                f"{PATHS['agda']}: `{extra}` is a constructor of {dname} and is in no row of the "
                f"map -- the TypeScript side cannot name it, so nothing generates or decodes it"
            )
        for missing in sorted(declared - found):
            findings.append(
                f"{PATHS['agda']}: the map pairs `{missing}` with a tag, but {dname} has no such "
                f"constructor -- it was renamed or deleted and the map still claims it"
            )

        found = ts_string_union(src["ts"], uname) if kind == "prim" else ts_union(src["ts"], uname)
        for extra in sorted(found - tags):
            findings.append(
                f"{PATHS['ts']}: the {uname} union carries \"{extra}\", which is in no row "
                f"of the map -- the Agda side has no former to decode it into"
            )
        for missing in sorted(tags - found):
            findings.append(
                f"{PATHS['ts']}: the map pairs a former with the tag \"{missing}\", and the {uname} "
                f"union does not carry it"
            )

    dec = quoted(src["decode"], r'tag is "([A-Za-z]+)"')
    ops = quoted(src["decode"], r'op is "([A-Za-z]+)"')
    for r in rows:
        if r.tag not in (ops if r.kind == "prim" else dec):
            findings.append(
                f"{PATHS['decode']}: nothing decodes the tag \"{r.tag}\" -- `{r.agda}` is reachable "
                f"from neither the oracle nor any program the TypeScript tree writes"
            )

    gen = quoted(src["gen"], r'type:\s*"([A-Za-z]+)"')
    gops = gen_prim_lanes(src["gen"])
    for r in rows:
        here = gops if r.kind == "prim" else gen
        if r.gen and r.tag not in here:
            findings.append(
                f"{PATHS['gen']}: nothing generates the tag \"{r.tag}\", which the map declares "
                f"reachable -- either write the lane, or declare the hole with gen=no and say why"
            )
        if not r.gen and r.tag in here:
            findings.append(
                f"{PATHS['gen']}: the tag \"{r.tag}\" IS generated, and the map declares it "
                f"unreachable -- the hole closed and the row was not"
            )

    if findings:
        print("check-formers: the two trees' former sets have diverged:")
        for f in findings:
            print(f"  {f}")
        return 1

    palette: dict[str, list[str]] = {}
    for r in rows:
        if r.kind == "exp":
            palette.setdefault(r.role, []).append(r.agda)
    print("check-formers: the palette under the dividing test:")
    for role in sorted(palette):
        print(f"  {role:9} {' '.join(sorted(palette[role]))}  -- {ROLES[role]}")

    holes = [r for r in rows if not r.gen]
    print(
        f"check-formers: {len(rows)} former(s) paired across four surfaces -- every Agda "
        f"constructor and every TypeScript union member is in the map, every tag decodes, "
        f"and {len(rows) - len(holes)} are generated"
    )
    for r in holes:
        print(f"  UNREACHABLE BY THE GENERATOR: {r.agda} / \"{r.tag}\" -- {r.why}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
