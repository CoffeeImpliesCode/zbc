# Finding-regression harness (issue #19)

zbc's dominant ongoing cost is false-positive tuning, and until now there
was **no measurement** — every suppression commit was validated by hand.
This harness gives a regression signal: run zbc over a stable corpus,
canonicalize the findings, and diff against a committed baseline.

```
tools/metrics/regress.py            # diff current findings vs baseline
tools/metrics/regress.py --update   # (re)write the baseline
tools/metrics/baseline.json         # committed finding set
```

A finding is keyed by `(rule_id, file, line, col)`, so the diff is
order-independent. Every run in the document is read, every URI is decoded,
and an absolute `file:` URI is made relative to the checkout's *resolved*
root — the spelling zbc resolves its own source roots to — so neither the
checkout's location (reached through a symlink included) nor URI escaping
changes source identity. A file outside the checkout keeps a `../..`-led
path, which still names exactly one file. Output:

```
+ NEW finding   — a new fire: a genuine catch, OR a false-positive regression
- REMOVED finding — a lost fire: a fixed false positive, OR a recall regression
```

Exit code is `0` when findings match and `1` when they differ. Exit `2`
means the sweep or the baseline could not be accounted for: the analyzer
failed, reported incomplete analysis, or supplied SARIF with no run to read
or a finding with no position; or the baseline is unreadable or disagrees
with its own counts. `--update` refuses to write a baseline that records no
findings at all, since that would delete the only coverage record. The
harness reads SARIF from stdout and keeps stderr separate.

The harness limits analysis to two workers to bound concurrent analysis memory
and avoid oversubscription on hosts with many CPUs. A relative `--corpus`
resolves against the checkout, not the calling directory.

## Workflow

After any rule or engine change, run `regress.py`. If the diff is empty,
the change is finding-neutral. If it isn't, **inspect each delta** and
decide whether it's the intended effect (e.g. the value_range min-length
work should *remove* `ptr-slice-without-bounds-check` findings that are
now provably safe). If intended, `--update` to re-baseline; commit the
new `baseline.json` alongside the change so the diff stays meaningful.

A finding whose line moved because its fixture was edited appears as one
added and one removed finding, with no per-rule delta. That is a stale
baseline, not a lost fire: confirm the move against the fixture before
re-baselining.

The analyzer reports coverage for selected root files, not every file on disk.
`selected=N` includes admitted files and explicitly refused files.
The counts must satisfy `selected = analyzed + partial + failed`.
A `partial` file reported the findings of every function and rule that finished; stderr lists the others as `zbc: incomplete`.
Before accepting a mass removal, compare the corpus with the selected root files.
Neither empty findings (`[]`) nor nonzero counts prove complete coverage.
Exit `2` means incomplete analysis because selection, parsing, or analysis failed, or a file was only partly analyzed because it exceeded a budget.
JSON and SARIF go to stdout. Operational diagnostics and the coverage summary go to stderr.

Run the path-identity regressions with:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tools/metrics
```


## Corpus

Default corpus is **`test/fixtures/`** — the per-rule designed fire-cases
mined from real bun/ghostty/tigerbeetle bugs. Point it elsewhere with
`--corpus DIR` (e.g. a checkout of a real project) for a richer signal.

The fixtures include bug cases and safe controls. Review each changed location
before updating the baseline.

The guarded memset fixtures prove a strict length decrease and retain both bug
findings. The baseline also records the dangling slice restored by
`growBuggy` in `defer_and_errdefer_free_overlap.zig`, and the caller-visible
partial retag in `partial_union_write.zig`. It excludes that fixture's
unobservable retags: the pure-local write, the in-place heap construction
whose only failing-path cleanup is a raw `free`, and the frame-private local
built before that same raw release. The last two exist so the private-scope
suppression has a negative of its own — a suppression with no negative case
cannot regress silently.

A rule missing from `per_rule` has no coverage at all: the diff has no
baseline entry to lose, so a recall regression in it prints nothing.

## Scope / limitation — this is regression detection, not precision/recall

The harness measures *change* against a baseline; it does not measure
absolute precision/recall, because the corpus is **unlabeled** — a
finding isn't tagged true- vs false-positive. The labeled-corpus piece
(annotating real-code findings as TP/FP so we can report precision and
recall, ideally in SARIF where TP = `result` and FP = a `suppression`
with `state:"accepted"` — see issue #19) is the remaining follow-up.
With labels, the same diff machinery yields precision/recall as a
set-diff of results vs suppressions between the run and the labeled
baseline.
