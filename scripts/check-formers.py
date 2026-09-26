#!/usr/bin/env python3
"""Hold the two trees' former sets to one written-down correspondence.

The Agda tree and the TypeScript tree carry the same object language, and
what tied them together was a tag string the decoder matched and the
generator happened to emit.  Nothing failed when they diverged: a former
only one tree had was simply never generated, so the oracle and the
all-Agda sweep both reported green over shapes neither was ever handed.

`scripts/formers.tsv` is the one declaration of the pairing, and this
checks six surfaces against it, in both directions where both directions
are decidable:

  A  the Agda datatypes   agda/src/Rx/Exp.agda      `data Exp` / `Tm` / `PrimOp`
  B  the Agda decoder     agda/src/CLI/Decode.agda  `tag is "..."` / `op is "..."`
  C  the TypeScript types typescript/src/exp.ts     `export type Exp` / `Tm` / `PrimOp`
  D  the TS generator     typescript/src/generator.ts   `type: "..."`, the op lanes
  E  the sweep's census   agda/src/QuickCheck.agda  `formerTag` / `allFormers`
  F  the Agda sweep's reach  the `gen*` definitions, composed with
                             `Rx/Elaborate.agda` and the harness root

A, C and E are checked BOTH ways -- they are closed declarations, so a former
present there and absent from the map is a finding, which is what catches a
former added to one tree alone.  B and D are checked one way only: the
decoder's file also carries the tags of types, inputs and primitive
operators, and the generator's file writes every one of those too, so
"a tag here that is not in the map" is the normal state of both and
asserting otherwise would report the whole type grammar.

D's and F's direction is the one that costs something and the one the
convention never had: a former neither generator can reach is covered by
no sweep and no oracle run whatever either reports, so the map's `gen`
and `agen` columns are where that hole is declared and counted, with its
reason beside it.

F EXISTS BECAUSE A `gen=no` REASON USED TO APPEAL TO AN UNCHECKED
SURFACE.  The two generators cover different holes on purpose -- a former
whose type IS the protocol's own structure cannot be mirrored by plain
rxjs, so the TS lane declines it and the all-Agda sweep is what covers
it -- and that division was written in the map's reason column and read
by nothing.  A reason naming a surface no check holds is a claim that
cannot go red, which is how `batchSyncᵉ` came to be declared covered by
the all-Agda sweep while the Agda generator had no arm for it at all.

E is the one that says whether the other four were ever EXERCISED.  They
decide that a former is generable; none of them can say whether a run ever
produced one, and a former nothing produces is covered by no sweep and no
oracle run whatever all four report.  So the census's own enumeration is
held to the map, and `allFormers` -- the roll the tally walks -- separately,
since a former missing from it counts zero forever while the file still
typechecks and still prints a census.

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
    "census": "agda/src/QuickCheck.agda",
    "elab": "agda/src/Rx/Elaborate.agda",
    "harness": "agda/src/Implementation/Unit-Test/Prelude.agda",
}


# THE DIVIDING TEST'S ANSWERS, and the vocabulary is closed on purpose: a
# former whose status is none of these has not been measured against the
# test, and inventing a word for it here is how that goes unnoticed.
ROLES = {
    "source": "produces without reading anything, and subscribes nothing",
    "pure": "a pure function of ONE value, with or without carried state",
    "protocol": "reads or writes the protocol's own bookkeeping",
    "flatten": "subscribes a payload that is literal syntax and must be RUN",
    "binder": "not an operator at all -- μ-binding structure",
}


class Row:
    __slots__ = ("kind", "agda", "tag", "gen", "agen", "role", "why")

    def __init__(
        self, kind: str, agda: str, tag: str, gen: bool, agen: bool, role: str, why: str
    ) -> None:
        self.kind, self.agda, self.tag, self.gen, self.agen = kind, agda, tag, gen, agen
        self.role, self.why = role, why


def read_map(path: Path) -> list[Row]:
    rows: list[Row] = []
    seen_agda: dict[str, int] = {}
    seen_tag: dict[str, int] = {}
    for n, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 6:
            sys.exit(f"check-formers: {path}:{n}: want 6+ tab-separated fields, got {len(parts)}")
        kind, agda, tag, gen, agen, role = (p.strip() for p in parts[:6])
        why = parts[6].strip() if len(parts) > 6 else ""
        if kind not in ("exp", "tm", "prim"):
            sys.exit(f"check-formers: {path}:{n}: kind must be exp, tm or prim, got {kind!r}")
        for col, val in (("gen", gen), ("agen", agen)):
            if val not in ("yes", "no"):
                sys.exit(f"check-formers: {path}:{n}: {col} must be yes or no, got {val!r}")
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
        if "no" in (gen, agen) and not why:
            sys.exit(
                f"check-formers: {path}:{n}: gen=no or agen=no needs a reason in the last field -- "
                "an unreachable former is a hole to state, not a box to tick"
            )
        if gen == "no" and agen == "no":
            sys.exit(
                f"check-formers: {path}:{n}: `{agda}` is reachable by NEITHER generator, so no "
                "sweep and no oracle run has ever been handed it -- that is not a hole to declare, "
                "it is a former nothing covers"
            )
        for tbl, key in ((seen_agda, agda), (seen_tag, tag)):
            if key in tbl:
                sys.exit(f"check-formers: {path}:{n}: {key!r} already declared on line {tbl[key]}")
            tbl[key] = n
        rows.append(Row(kind, agda, tag, gen == "yes", agen == "yes", role, why))
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


def census_enum(text: str) -> tuple[dict[str, str], set[str]]:
    """The sweep's per-former census: constructor -> tag, and the roll walked.

    THE FIFTH SURFACE, AND THE ONE THAT SAYS WHETHER THE OTHER FOUR WERE EVER
    EXERCISED.  The four above decide that a former is GENERABLE -- every tree
    spells it, the decoder takes it, the generator has a lane.  None of them
    can say whether a run ever produced one, and a former nothing produces is
    covered by no sweep and no oracle run whatever all four report: the same
    silence, one layer in.  The census answers that, so its enumeration is
    held to the map exactly as the closed declarations are.

    Two readings, because the enumeration can fail in two ways.  `formerTag`
    pairs a constructor with the tag it reports under, and a tag drifting from
    the map makes the count unattributable.  `allFormers` is the roll the
    tally actually walks, and a constructor missing from it is worse than a
    missing tag: the former is declared, the file typechecks, and its count is
    zero forever -- a coverage hole that reads as a coverage report.
    """
    tags = dict(re.findall(r"^formerTag\s+(\S+)\s*=\s*\"([A-Za-z]+)\"", text, re.M))
    if not tags:
        sys.exit("check-formers: no `formerTag` clauses found -- the census was renamed or removed")
    m = re.search(r"^allFormers\s*=(.*?)\[\]", text, re.M | re.S)
    if not m:
        sys.exit("check-formers: no `allFormers =` list found -- the census roll moved or was renamed")
    return tags, set(re.findall(r"\bf[A-Z]\w*", m.group(1)))


def mentions(text: str) -> set[str]:
    """Every name a stretch of Agda MENTIONS, comment lines excluded.

    A name counts only when it stands as a token.  Agda puts almost nothing
    out of bounds in an identifier, so the delimiter set is the punctuation
    the language actually separates applications with -- without it `input`
    matches `genInput` and `ObservableInput`, and a surface reports a lane
    its file does not have.
    """
    body = "\n".join(l for l in text.splitlines() if not l.lstrip().startswith("--"))
    return set(re.findall(r"(?:^|[\s(){}\[\],;])([^\s(){}\[\],;]+)", body))


def bodies(text: str) -> str:
    """A file with its `postulate` blocks removed.

    A postulate has NO BODY, so nothing is reached THROUGH one: a former
    named only inside a postulated statement's type is a former the
    elaboration cannot actually emit, and counting it would report coverage
    the sweep does not have.  That distinction is the whole reason this
    composition is worth computing rather than approximating by file.
    """
    out: list[str] = []
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        m = re.match(r"^(\s*)postulate\b(.*)$", lines[i])
        if m is None:
            out.append(lines[i])
            i += 1
            continue
        if m.group(2).strip():          # a one-line `postulate x : T`
            i += 1
            continue
        indent = len(m.group(1))
        i += 1
        while i < len(lines):
            nxt = lines[i]
            if nxt.strip() and len(nxt) - len(nxt.lstrip()) <= indent:
                break
            i += 1
    return "\n".join(out)


# the author's palette wears its ornament, so which names are the AUTHOR's is
# read off the name itself and no list of them has to be kept here to go stale
PALETTE = re.compile("ˢ")


def top_level(text: str) -> dict[str, set[str]]:
    """Each definition at column zero, paired with every name it mentions.

    A `where` block is indented under the definition it belongs to, so
    slicing at column zero folds one into the other -- which is what is
    wanted, since a helper's local scaffolding is reached exactly when the
    helper is.
    """
    lines = text.splitlines()
    head = re.compile(r"^([^\s(){}\[\],;:]+)\s*(:|=)")
    starts = [(i, m.group(1)) for i, l in enumerate(lines) if (m := head.match(l))]
    out: dict[str, set[str]] = {}
    for n, (i, nm) in enumerate(starts):
        j = starts[n + 1][0] if n + 1 < len(starts) else len(lines)
        out.setdefault(nm, set()).update(mentions("\n".join(lines[i:j])))
    return out


def elab_arms(elab: str) -> tuple[list[tuple[set[str], set[str]]], str]:
    """The elaboration, arm by arm: what each clause CONSUMES and what it WRITES.

    `toEnvelope` is defined one clause per author former, so the pairing is
    already in the source and needs only to be read off: the left of the
    first top-level `=` names the author's constructor, the right names the
    plain formers that constructor turns into.  Keeping them paired is what
    makes the surface a COMPOSITION rather than a union -- a union would
    credit the sweep with every former the elaboration could ever emit,
    including the ones no generator arm can reach, which is a coverage claim
    that cannot go red.

    An author-side name is recognised by its ORNAMENT: every `SExp` and
    `STm` constructor carries the palette's superscript, so no list of them
    has to be kept here to go stale.  A clause consuming none of them --
    a catch-all, a helper's recursion -- constrains nothing and is read as
    always reachable, which is the safe direction for a clause that does not
    branch on a former.
    """
    lines = bodies(elab).splitlines()
    # THE BLOCK'S INDENTATION IS READ OFF ITS FIRST CLAUSE, NOT ASSUMED.  These
    # clauses sit inside a `mutual` block, so their depth is a formatting
    # choice; pinning it at two spaces made a re-indentation of the
    # elaboration read as the elaboration having been DELETED, which is the
    # one failure a coverage check must not have -- it fires loudly while
    # saying nothing about coverage.
    anchor = re.compile(r"^(\s+)toEnvelope(Tm|Tms)?\b")
    indent = next((m.group(1) for m in map(anchor.match, lines) if m), None)
    if indent is None:
        sys.exit("check-formers: no `toEnvelope` clauses found -- the elaboration moved or was renamed")
    head = re.compile(r"^" + re.escape(indent) + r"toEnvelope(Tm|Tms)?\b")
    starts = [i for i, l in enumerate(lines) if head.match(l)]
    covered: set[int] = set()
    arms: list[tuple[set[str], set[str]]] = []
    for n, i in enumerate(starts):
        if n + 1 < len(starts):
            j = starts[n + 1]
        else:                       # the last clause ends where its block does
            j = next((k for k in range(i + 1, len(lines))
                      if lines[k].strip() and not lines[k].startswith(" ")), len(lines))
        covered |= set(range(i, j))
        text = "\n".join(l for l in lines[i:j] if not l.lstrip().startswith("--"))
        depth, cut = 0, None
        for k, ch in enumerate(text):
            if ch in "({[":
                depth += 1
            elif ch in ")}]":
                depth -= 1
            elif ch == "=" and depth == 0 and text[k + 1 : k + 2] != "=":
                cut = k
                break
        if cut is None:
            continue
        arms.append((mentions(text[:cut]), mentions(text[cut + 1 :])))
    if not arms:
        sys.exit("check-formers: no `toEnvelope` clauses found -- the elaboration moved or was renamed")
    rest = "\n".join(l for k, l in enumerate(lines) if k not in covered)
    return arms, rest


def agda_gen_reach(census: str, elab: str, harness: str) -> set[str]:
    """THE SIXTH SURFACE: which plain formers the Agda sweep can actually write.

    The sweep no longer builds plain programs.  It draws from the AUTHOR's
    palette and the harness root elaborates what it drew, so what reaches the
    plain tree is a COMPOSITION of three stretches and not one of them alone:
    the generator, the elaboration's definitions, and the harness root that
    mints and caps.  Reading any single one of them would answer a different
    question -- the generator names no plain former at all, and the
    elaboration names every one it could ever emit whether or not a program
    reaching it can be drawn.

    The generator is the run of definitions from `genB` down to the census.
    The region is bounded at both ends rather than scanned whole because the
    census below it names every former by construction, and a scan that ran
    past it would report the whole palette reachable.

    THE ELABORATION IS TAKEN AT ITS DEFINITIONS AND NOT AT ITS STATEMENTS,
    which is where this surface earns its keep: four of its arms are still
    POSTULATES, so the plain formers their conclusions are stated in are
    formers no run can produce, however freely the generator draws the
    author's operator.  `bodies` is what holds that line.
    """
    lines = census.splitlines()
    start = next((i for i, l in enumerate(lines) if re.match(r"^genB\b.*:", l)), None)
    if start is None:
        sys.exit("check-formers: no `genB :` found -- the Agda generator moved or was renamed")
    end = next((i for i, l in enumerate(lines[start:], start) if re.match(r"^marks", l)), None)
    if end is None:
        sys.exit("check-formers: no `marks…` after the generator -- the census moved or was renamed")
    drawn = mentions("\n".join(lines[start:end]))

    # the arms the generator can actually reach, and what each of them writes
    arms, rest = elab_arms(elab)
    reach = set(drawn)
    for lhs, rhs in arms:
        if {t for t in lhs if PALETTE.search(t)} <= drawn:
            reach |= rhs

    # and then the helpers those arms call, to a fixpoint: an arm reaching
    # `mapᵖ` reaches whatever `mapᵖ`'s body writes, and an arm nothing reaches
    # takes its helper down with it
    reach |= mentions(bodies(harness))
    helpers = top_level(rest)
    while True:
        grown = reach | {t for nm, body in helpers.items() if nm in reach for t in body}
        if grown == reach:
            return reach
        reach = grown


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

    agen = agda_gen_reach(src["census"], src["elab"], src["harness"])
    for r in rows:
        if r.agen and r.agda not in agen:
            findings.append(
                f"{PATHS['census']}: no arm of the Agda generator writes `{r.agda}`, which the map "
                f"declares reachable -- either write the arm, or declare the hole with agen=no"
            )
        if not r.agen and r.agda in agen:
            findings.append(
                f"{PATHS['census']}: the Agda generator DOES write `{r.agda}`, and the map declares "
                f"it unreachable -- the hole closed and the row was not"
            )

    ctag, roll = census_enum(src["census"])
    exp_tags = {r.tag for r in rows if r.kind == "exp"}
    for extra in sorted(set(ctag.values()) - exp_tags):
        findings.append(
            f"{PATHS['census']}: the census reports under the tag \"{extra}\", which is in no "
            f"`exp` row of the map -- its count cannot be attributed to a former"
        )
    for missing in sorted(exp_tags - set(ctag.values())):
        findings.append(
            f"{PATHS['census']}: the census counts nothing under the tag \"{missing}\" -- the "
            f"sweep cannot report whether a program carrying that former was ever generated"
        )
    for ctor in sorted(set(ctag) - roll):
        findings.append(
            f"{PATHS['census']}: `{ctor}` is declared and is not in `allFormers`, so the tally "
            f"never walks it and its count is zero on every run, whatever the generator produced"
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

    holes = [r for r in rows if not (r.gen and r.agen)]
    print(
        f"check-formers: {len(rows)} former(s) paired across six surfaces -- every Agda "
        f"constructor and every TypeScript union member is in the map, every tag decodes, "
        f"and {len(rows) - len(holes)} are reachable by BOTH generators"
    )
    for r in holes:
        which = "the TypeScript generator" if r.agen else "the Agda generator"
        print(f"  UNREACHABLE BY {which}: {r.agda} / \"{r.tag}\" -- {r.why}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
