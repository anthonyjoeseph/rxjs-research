# Fixture — dated narrative

The date check scans the WHOLE file, not just rows: the worst offender is
prose about the file's own rules, which is not a row and would dodge a
row-scoped check.  This line is the negative control for that: `2026` and
`08-20` alone are not dates, and a version like `1.2.3` is not one either.

## Tier 0

### Big picture tier roadmap

- **the anchor group** — the worst-class row and the two statements that share
  its currency; one unit of work because a restatement of any of them moves the
  other two.
- **the mechanical shelf** — every row whose shape is already known, ground in
  one pass off a single loaded context.
- **the parked remainder** — what is left once the two legs above land, kept
  here so the tier's plan is complete rather than open-ended.

### The ledger

- **`plain-row`** — GRINDABLE: names no date, so it must not be reported.
- **`attributed-row`** — GRINDABLE: carries a ruling's attribution
  (Anthony, 2026-08-20), which is the shape the check exists to catch.
- **`measured-row`** — GRINDABLE: measured 2026-07-31, a receipt that belongs
  in the postulate's own header where its age is the point.
- **`spelled-row`** — GRINDABLE: restated Aug 18 2026, spelled out rather
  than ISO, which is the obvious way to dodge a `\d{4}-\d{2}-\d{2}` scan.
