# `make imports-check` — an import nothing uses is an edge nothing pays for

Agda has no unused-import warning, so a `using (…)` clause is the one place in
this tree where a dependency can be **asserted and never spent**. `-W error`
cannot help: there is no warning to promote.

That is not a tidiness matter. An import is an **edge in the module graph**, and
an edge decides two things that govern every build:

- what a full `make gate-heavy` must check **before** this file, and
- what an edit to the imported module **invalidates**.

A name nobody reads still moves both. The numbers behind that claim, and the
twelve-edge instance that paid for this checker, are in
`typecheck-performance-numbers.md` — the short version is that all thirteen
`Verify-Well-Formed/Part*` imported one name from the top of the
budget-sufficient tower and exactly **one** of them used it, which is what made
the critical path 41 levels deep instead of 29 and put twelve extra modules into
the rebuild cone of every edit in the caps/walk grind lane.

## The three commands

```
make imports-check        report; exit 1 if anything is dead   ← in the gate
make imports-fix          delete them in place
make imports-selftest     the checker still fires, both ways   ← in the gate
```

Directly, for a narrower scope:

```
scripts/check-imports.py --src agda/src/Verify-Well-Formed --stats
scripts/check-imports.py --src <one file> --fix
scripts/check-imports.py --keep-names        # module edges only, no name-level
```

## What the gate checks

**Two findings are about USE, and the gate fails on both.** A dead DECLARATION
— an `open import M using (…)` where *none* of the imported names is used,
which is the set that moves the module graph. And a dead NAME inside a clause
that still has a live one, which does not. The sections below carry the rest:
a PHANTOM name, a missing or mismatched module header, a BLANKET import, a
`public` re-export, and the orphan guard's WIRING findings.

The name-level half used to be an opt-in `--names` flag, on the argument that a
clause with one live name holds the edge open so the other thirty cost nothing a
build can measure. That argument was about BUILD TIME and the check is not about
build time — it is the same legibility argument `using` lists rest on in the
first place. A list that names thirty things a file does not touch is not a
record of what the file depends on, and the reader cannot tell which claim is
real without doing the search themselves. Anthony: *"no unused imports,
either."* Cost of the switchover: **5710 names across 67 files**, and the tree
holds at zero.

`--keep-names` suppresses the name-level half. It is for isolating a
module-EDGE question from a name one while reading a report, not for the gate.

Four cases are **skipped for the USE check**, and `--stats` counts them so the
blind spot has a size. Each still answers to the other checks — skipped here is
not exempt:

| skipped | why |
| --- | --- |
| `open import M public` | a re-export is FOR its consumers, so locally unused is normal — it gets a `RE-EXPORT` finding instead |
| `open import M` with no `using` | it imports every name `M` has, so "unused" is not decidable from this file — it gets a `BLANKET` finding instead |
| a clause with `renaming` and no `using` | same reason — the un-renamed rest is still imported |
| the tree's **claim root** | its imports ARE the claim; unused is the design |

## A PHANTOM NAME — imported from a module that does not have it

The one finding here that Agda would eventually catch on its own:

```
Phantom.agda:12: PHANTOM NAME  gone  — Phantom-Src does not mention `gone`
anywhere, so it cannot be exporting it.
```

Agda's own report is a `ModuleDoesntExport` **warning**, which `-W error` turns
into exit 42 — so the build does fail, many minutes down the tower, naming the
importer and saying nothing about where the name went. One instance per run,
too: the module aborts at the first error, so a migration that broke four
consumers costs four full builds to find. This check decides all of them in
milliseconds, before the tower starts.

**The shape it catches is a definition MOVING.** The old module stops exporting
the name; one consumer's `using` clause still asks for it while its siblings
have already been repaired. The instance that motivated it: a name migrated to
a small shared module, and one file kept the old edge — while ALSO carrying a
correct import of the same name from the new home, so the file read as fine and
`grep` for the name found it twice, both times looking right. The name-level
check cannot see it, because the file genuinely *uses* the name.

**What makes it sound is the `public` ban.** Without re-exports a module can
only export what its own text mentions, so "the name appears nowhere in M" is a
proof that M does not export it. Two consequences worth knowing:

- **It reads a module's text with its import DECLARATIONS excised.** A name M
  merely imports is not a name M exports, so a whole-file read would call it
  exported and miss the row.
- **It only asks modules it can read.** A stdlib module is not a file in this
  tree and re-exports freely, so every such import is skipped. The check
  under-reports by construction and never invents: the finding it does make is
  certain, which is why it is a gate failure rather than a report.

**It is not auto-fixable, and `--fix` leaves it alone.** The repair is the RIGHT
module, which only a human knows; deleting the item would trade a scope-check
warning for an unbound name.

**The one side to get wrong is the renaming.** `x to y` binds `y` locally but
the module must export `x` — the opposite of what every other question in this
file wants, and `split_list` returns the bound name for exactly that reason.
Reading the bound side reports a phantom on the item that is CORRECT and stays
silent on the one that is not: it fires and misses in the same breath. The
fixture pins both directions.

## THE FILE'S OWN NAME IS CHECKED FIRST

**A missing `module … where` header is not a syntax error.** Agda infers the
name from the path and checks the file happily as a TARGET. It crashes only
when something IMPORTS it, and then with

```
An internal error has occurred. Please report this as a bug.
Location of the error: __IMPOSSIBLE__, called at src/full/Agda/Interaction/Imports.hs
```

naming neither the file nor the import — the log's last line is the module
Agda was checking when it tried to load the headerless one, which is a
different, healthy file.

**And `make agda-dev` cannot see it**, which is what makes this expensive:
agda-dev checks a GENERATED copy under its own `Dev-…` module name, so the
missing header is supplied by the generator and the module reports GREEN. A
red gate plus a green dev check on the same file reads as a tooling problem,
and this is the one shape where it is not.

Bisecting it is fast once you suspect the import graph rather than the file:
a two-line module that does nothing but `import M` reproduces in seconds, and
the same probe over each of a crashing file's imports finds the culprit
directly. `grep -L '^module ' ` over the tree finds it faster still, which is
why the check lives here — one pass, milliseconds, before any finding about a
file's imports.

A declaration that disagrees with its path is the same finding: reported, and
a gate failure.

**A MIXFIX IS SPENT AS A SECTION AT LEAST AS OFTEN AS FULLY APPLIED, AND `_`
DOES NOT SEPARATE TOKENS.** `(x ⊔_) *_` is two tokens, `⊔_` and `*_` — not
`⊔` and `*` — so an atom-equality test over raw tokens calls `_*_` unused
while the file multiplies three times. That is the checker's worst failure
mode by a distance: a false positive DELETES a live import, and the build then
dies far from the edit with

```
error: [NoParseForApplication]
Could not parse the application (pmᵗ V 0 f ⊔ 1) *_
Operators used in the grammar:
  None
```

which names the USE and never the deleted import. It cost 507 live names in
one `--fix` run.

The repair is to split the TOKENS on `_` exactly as the NAMES are split, so
both sides sit in one alphabet — which also covers a multi-hole section
(`hop_via_onto_`), where stripping the underscores out instead does not.
`-` is NOT a separator, so `setNode-fnCap` is one token and does not count as
a use of `setNode`; that is correct, and it is most of what an over-loose
substring audit turns up.

A `using` entry may name a MODULE (`using (module M)`); the name it binds is `M`,
and the keyword comes off before the search. See the false-positive note below —
this is the one case that has ever deleted a live import.

These are skips for the USE analysis only. A `public` declaration is not let
through — it is illegal outright (see below), and `--fix` still never rewrites
one, because deleting a re-export means giving its consumers real imports, which
is a human's job.

## The blanket rule: an import must name what it takes (Anthony)

**An import with no `using` list is a finding in every file, claim roots
included.** It takes every name the module has, so what the file actually
depends on is written down nowhere — not at the top, not at the use sites, not
anywhere a reader or a `grep` can find it. **27 sites** in the tree today.

Stated positively, and this is the form that decides the two carve-outs below:
**no import may put names in THIS file's scope without naming them.**

This is a **policy** check and not a use analysis, which is why it is a separate
rule rather than a smarter version of the one below. The use check compares a
`using` list against the body; with no list there is nothing to compare, and the
checker has no export list to synthesise one from. So the two verdicts are
independent, and a blanket import is reported `BLANKET` and never `DEAD`.

**It buys legibility, not build time, and the distinction matters.** An import
creates the module-graph edge whatever its clause: the module is typechecked
first, its whole interface is loaded, and an edit to it invalidates this file
either way. `using` filters what enters SCOPE, not what enters the BUILD — there
is no tree-shaking. So a blanket import that is genuinely used costs exactly what
a `using` import that is used costs, and naming it buys no seconds. The dead-import
rule below is the one that moves build time, because deleting an unused import
removes the edge. (Whether a larger in-scope name set slows scope resolution is
unmeasured here, and nowhere near edge-level either way.)

**It is not auto-fixable, and `--fix` deliberately leaves it alone.** Naming the
imports means knowing which of the module's exports this file uses, which needs
the module's export list — only Agda has that. `--fix` also still exits non-zero
while a blanket finding stands, so it cannot be used to reach green.

Three shapes fire, and two near-misses must not:

| shape | verdict | why |
| --- | --- | --- |
| `open import M` | BLANKET | takes everything |
| `open import M public` | BLANKET **and** RE-EXPORT | two findings: names nothing, and re-exports |
| `open import M renaming (x to y)` | BLANKET | takes everything, respells some |
| `open import M using () renaming (x to y)` | fine | the **most precise form there is** — takes nothing, names exactly what it respells |
| `import M as Q` | fine | puts nothing in unqualified scope; every use is `Q.name`, so the dependency is written at each use site |

## No `public` re-exports (Anthony)

**A `public` re-export is illegal, named or bare.** It makes names reachable from
a module that did not define them, so every consumer downstream depends on a fact
written down nowhere in its own file: `grep` cannot find where a name came from,
`make find` reports the wrong home, and this checker's use analysis has to skip
the declaration entirely, because "locally unused" is the normal case for a
re-export. Import from the **defining** module instead and every edge is explicit.

**What it costs, measured.** 66 `public` markers to delete (62 bare, 4 named), and
**3231 names across 91 modules** become explicit imports — median 14 per module,
worst 219. Against **14564** names already imported explicitly today, so about a
22% increase in import text.

**What it does NOT buy is a shorter critical path**, and that is worth stating
plainly because it is the intuitive expectation. The ladder's dependencies are
GENUINE at the name level — `Part_n` really uses names defined in `Part_{n-1}` for
every n in 2…13 except Part3 — so removing `public` removes no edge and shortens
no chain. The transitive dependency set is unchanged.

**What it plausibly does buy is smaller interface files**, which matters because
deserialization is this build's floor and is memory-bandwidth bound. Suggestive
but CONFOUNDED evidence, and it is recorded as suggestive on purpose: across 52
interfaces totalling 31.9 MB, modules carrying a `public` re-export averaged 79.9
KB per own-declaration against 44.0 for those without. The confound is that the
re-exporting modules are also the ladder's largest, so KB-per-declaration is not
a clean measure. Deciding it needs a direct experiment — drop one re-export,
recheck the module, compare the `.agdai` — not this correlation.

**The rejected alternative, for the record**, since it looks cheaper and is not:
keeping the re-exports and merely NAMING them. That costs up to **18313
name-mentions**, 60 of the 62 sites needing more than ten and the worst 677 — and
each list must be exhaustive or the build breaks, must be revisited whenever any
consumer changes, with nothing mechanically checking completeness. On the
`Verify-Well-Formed` ladder alone that is ~2193 mentions across 12 lists, each
invalidated when any level below it gains a definition: O(n²) hand-maintained
text. Deleting the re-exports is both cheaper and stricter.

**And this half of the check buys no build time**, which is worth keeping straight
because the dead-import half does. Deleting a dead import removes a module-graph
edge; naming a blanket one does not. The two rules live in one tool and pay in
different currencies.

**The claim roots are NOT exempt from this one**, and that is the one place the
two rules collide: a claim root is skipped wholesale by the use check and still
reported here. `src/Main.agda`'s own header has demanded `using` lists in prose
since long before anything checked — "NO BARE `open import`. Individual
definitions only." Main already complies; all six of its imports carry lists.

## The claim root, and it is the only exception (Anthony)

**One file per include root is skipped wholesale: the claim root.** `agda/src`
roots at `Main.agda`, `agda/evidence/refuted` at `Refuted/Main.agda`, and both files exist
to NAME definitions rather than apply them — "individual definitions only, so
that `imported` means `claimed`". So every import in one is locally unused *by
design*, and `make wiring` reads precisely those `using` clauses to seed
reachability. Pointing a use-based checker at a claim root makes it report the
claim graph as dead weight: caught in simulation before the first `--fix` ever
ran, and deleting what it reported orphaned **84 of 86 modules**.

**It is one rule and not a list of blessed filenames**, which is the part worth
keeping. The claim root is DERIVED from the include root being scanned
(`CLAIM_ROOT`, keyed by tree, the same fact `check-wiring.py` carries as
`ROOT_REL`), so the exception cannot grow without someone adding a whole tree,
and no ordinary module can ever drift into it. Every other file in either tree
earns its imports by spending them.

The refuted tree gets the law by being a tree, not by being named twice: its root
says of itself that a refutation not listed is not checked, "exactly as in
src/Main.agda".

## The orphan guard: a sole-route edge is a WIRING finding, not dead weight

An unused import can still be the **only surviving route** to a module. Deleting
that one does not tidy the graph — it hides a subtree from `make gate-heavy` and trips
`wiring-gate` one step later. So the checker computes reachability first and
**refuses to report such an edge as dead**: it prints a `WIRING` line instead, and
`--fix` leaves the line alone and still exits non-zero, so the fixer cannot be
used to launder a wiring finding into green.

**It asks the question the FIXER asks, which is not the per-edge one.** The first
cut tested each edge alone — "would deleting *this* one orphan anything?" — and
that is strictly weaker than what `--fix` does, because the fixer deletes the
whole set at once. Two dead edges into the same module are each individually
redundant, since removing either leaves the other reaching it, and jointly they
are its only routes: a per-edge guard waves both through and the module
disappears. So the candidate set is trimmed **jointly** and grown back to a
fixpoint, holding whatever is still needed to keep every module reachable.

The same mistake has a second home, and it is the one to watch for: **the
reporting path must not re-ask the per-edge question either.** Computing "what
would be lost if this edge went" at print time silently undoes the joint
decision, because each of a sole-route pair still looks redundant against the
other. A held edge reports the at-risk modules it helps hold, computed once with
every candidate removed.

It refuses rather than picking because the repair is a human call, and it is the
one CLAUDE.md already spells out: either the module is dead (delete it on its
merits) or a real consumer is missing (wire it).

Its seeds are the claim roots **plus `check-wiring.py`'s own `MODULE_ROOTS`,
imported rather than retyped** — a compiled binary or a type-level probe is
reachable only as a root, so a guard that did not know about them would happily
orphan their subtrees. Importing the list is also what keeps the two tools from
drifting apart as roots are added.

This guard subsumes the claim-root rule above and does not depend on having
enumerated the roots correctly, which is why both exist.

On the tree as it stands the guard holds back **nothing**: all 410 dead edges can
go at once and the reachable set is unchanged at 98 modules. That was confirmed
against a separately written parser rather than by trusting the guard, which had
had the per-edge bug in it an hour earlier.

## Why you can trust it, and the one direction it errs in

Every uncertainty resolves to **used**. A false negative costs a build second; a
false positive deletes a name the proof needs, and a fixer that has done that
once is a fixer nobody runs again.

Concretely: comments are stripped before anything is read (the motivating case
had the name in a comment and nowhere else, so a checker that skips this step
finds nothing); a name is matched as a whole **token**, so `T` is not satisfied by
`True`; a mixfix name is matched by **any** of its parts, so `_∷_` counts as used
the moment `∷` appears anywhere, infix or not; and a qualified use `M.name`
counts, because `.` is a token separator.

**THE ONE FALSE POSITIVE IT HAS ACTUALLY HAD, and its shape is worth carrying.**
A module is imported by naming it `using (module M)`, and the name that binds is
`M` — the keyword is syntax. The splitter kept the whole string, and no token can
ever equal `module M`, so **every** such import read as dead. Worse, the use that
pays for it is `open M using (…)` — a module *application*, not an import
declaration — so the checker never looked at the line that would have saved it.
`make imports-fix` deleted 18 of them and the build failed at the first one with
`NoSuchModule`.

Two lessons, and the second is the general one. The proximate bug was a missing
`re.sub` in `split_list`. The structural one is that **this checker's "use" search
is over tokens in the body, so any name whose only use is a piece of SYNTAX the
tokeniser does not reach is invisible to it** — and a `module` entry was the one
such name in this repo. The direction of the error is the point: every other
uncertainty in this file resolves to *used*, and this one resolved to *dead*,
which is why it was the class that cost a build rather than a build second. When
adding a case, ask which way it fails before asking whether it fires.

**`--fix` rewrites the raw file from offsets found in the comment-stripped copy**,
which is why `strip_comments` blanks characters instead of removing them and an
assertion pins the length. The first version truncated, and spliced a using-clause
into the middle of a file's opening comment. The selftest now checks the fixer,
not only the finder: that it is idempotent, that it spares the live names, and
that it leaves the must-not-touch fixture byte-identical.

## The fixture

`scripts/imports-selftest/` is a fixture TREE, and the selftest asserts **both**
directions — a checker that fires on everything and a checker that fires on
nothing both go green against a fixture that only tests one of them.

`Fires.agda` must report four declarations and one name: a plain unused import, one
whose name appears **only in a comment**, one whose `using` list spans two lines, a
token near-miss (`T` imported, `T-rue` in the body), and a dead name sitting beside
a live one, plus two blanket imports and two `public` re-exports — the named
re-export fires too, because naming what you re-export still does not tell a
consumer where the name came from. `Quiet.agda` must report nothing: a mixfix
operator used infix, a `renaming`, a `using () renaming (…)`, a qualified
`import … as`, and a `using (module M)` whose only use is an `open M` — the last
of these is the false positive that broke the build, so it is pinned where a
regression turns three rows red at once.

**The tree owns a claim root and a sole-route edge, because the real trees cannot
test either.** `Main.agda` is the fixture's claim root and must be reported on not
at all — pointing the checker at `src/Main.agda` instead proves only that it is
silent, never that it is silent for the right reason. `Guard-Root.agda` holds an
unused import of `Guard-Leaf` that is the only route to it, and must come out as
`WIRING`, never `DEAD`, with the line byte-identical after `--fix`. This is why
the claim root is derived from the tree rather than hardcoded: a fixture cannot
exercise a rule keyed to two real filenames.

`Fires.agda` also carries the three blanket shapes and `Main.agda` a fourth, so
the collision between the blanket rule and the claim-root skip is pinned; the
`using ()` idiom and a qualified import sit in `Quiet.agda` as the near-misses.
A bare `open import` used to live in `Quiet.agda` as a must-not-fire row for the
use check — which still skips it — and moved when the blanket rule arrived,
because "the use check skips it" stopped meaning "nothing reports it".

Every one of these rows was **mutation-tested**: removing the claim-root skip,
defeating the guard, letting `--fix` ignore the hold-back, disabling the blanket
rule, exempting the claim root from it, treating `using ()` as blanket, allowing a
`public` re-export, reverting the guard to per-edge, and keeping the `module`
keyword on a using-list entry each turn the selftest red.
