#!/usr/bin/env python3
"""Finding-regression harness for zbc (issue #19).

Runs `zbc --format=sarif` over a corpus, canonicalizes the findings, and
diffs them against a committed baseline so any rule/engine change shows
its delta:

    added findings   -> a new fire (a genuine catch, OR a false-positive
                        regression — inspect)
    removed findings -> a lost fire (a fixed false positive, OR a recall
                        regression — inspect)

Scope: this is REGRESSION detection on a stable corpus, not labeled
precision/recall. The default corpus is `test/fixtures/` (designed
fire-cases). True precision/recall needs a *labeled* corpus of real code
(the bun/ghostty PRs the fixtures are mined from) — a follow-up; see
the README.

Usage:
    regress.py [--corpus DIR] [--zbc PATH] [--baseline FILE]
    regress.py --update           # (re)write the baseline from the corpus

Exit code: 0 if findings match the baseline, 1 if they differ (CI gate),
2 on a harness error.  A sweep only counts as analyzed when every run in
the document carries an invocation with `executionSuccessful: true`; a
missing, empty, or negative completion record is exit 2, never a clean or
a changed finding set.  So are a document with no run to read, a finding
with no source position, a baseline that disagrees with itself, and an
`--update` that would record no findings: each is a sweep the harness
cannot account for, and reading any of them as zero findings would report
lost recall as a clean run.
"""
import argparse
import json
import os
import subprocess
import sys
from collections import Counter
from urllib.parse import unquote, urlsplit

HERE = os.path.dirname(os.path.abspath(__file__))
# The analyzer reports paths under the roots it resolved itself
# (`SourceSelection.canonical` runs `realPathFile`), so a sweep started
# from a symlinked spelling of this checkout still carries real,
# symlink-free absolute paths.  Measuring those against an unresolved root
# would spell every one of them `../../..`-deep, and no committed baseline
# can hold that: the whole baseline would read as added and removed at
# once.  Resolve the root once, here, and use that one spelling for the
# comparison, the analyzer's working directory, and `--zbc`.
REPO = os.path.realpath(os.path.join(HERE, "..", ".."))

def fail(message):
    print(f"regress: {message}", file=sys.stderr)
    raise SystemExit(2)


def runs_of(sarif):
    """The runs of one SARIF document, or a harness error.

    A document with no run is not an empty sweep; it is a sweep with
    nothing to account for.  Handing it on would let `findings` read zero
    results out of it and the diff report the whole baseline as removed
    — or, with an empty baseline, as no change at all.
    """
    try:
        runs = sarif["runs"]
    except (KeyError, TypeError) as e:
        fail(f"SARIF document has no readable runs member: {e}")
    if not isinstance(runs, list) or not runs:
        fail("SARIF document carries no run to read, so it is not a sweep")
    return runs


def run_zbc(zbc, corpus):
    """Return SARIF from a complete analyzer invocation."""
    try:
        r = subprocess.run([zbc, "--jobs=2", "--format=sarif", corpus],
                           capture_output=True, text=True, cwd=REPO)
    except OSError as e:
        fail(f"could not run {zbc}: {e}")
    if r.returncode not in (0, 1):
        fail(f"zbc failed with exit {r.returncode}:\n{r.stderr.strip()}")
    try:
        sarif = json.loads(r.stdout)
        # Absent evidence that the sweep finished is not evidence that it
        # did.  Requiring the record means an analyzer that stopped
        # writing it — or a differently shaped invocation — can no longer
        # let a partial corpus diff as a clean run.
        for index, run in enumerate(runs_of(sarif)):
            invocations = run.get("invocations") or []
            if not isinstance(invocations, list) or not invocations:
                fail(f"zbc recorded no invocation for run {index}, so analysis"
                     f" completeness is unknown\n{r.stderr.strip()}")
            if any(invocation.get("executionSuccessful") is not True
                   for invocation in invocations):
                fail(f"zbc reported incomplete analysis in run {index}:"
                     f"\n{r.stderr.strip()}")
    except (ValueError, KeyError, IndexError, TypeError, AttributeError) as e:
        fail(f"unusable SARIF on stdout: {e}\n{r.stderr.strip()}")
    return sarif


def source_identity(uri):
    """One spelling of one source file, whatever URI shape it arrives in.

    An absolute `file:` URI is the only form that has to be rewritten
    against *this* checkout; anything else is already checkout-independent
    and only needs the same percent-decoding, so one file cannot be counted
    twice under two spellings of one escape.  The root is the resolved
    `REPO` — the spelling the analyzer itself resolves its source roots to
    — so one checkout reads the same through a symlink as through its real
    path, and a file outside it keeps a `../..`-led spelling of its own.
    """
    parsed = urlsplit(uri)
    if parsed.scheme == "file" and parsed.netloc in ("", "localhost"):
        return os.path.relpath(unquote(parsed.path), REPO).replace(os.sep, "/")
    return unquote(uri)


def coordinate(region, field):
    """The one region coordinate a finding is keyed by.

    Defaulting a missing coordinate to 0 would key every result that
    cannot name a position to the same bucket, so a lost position would
    hide a finding instead of surfacing it.
    """
    value = region.get(field)
    if not isinstance(value, int) or isinstance(value, bool):
        fail(f"unusable SARIF finding: its region carries no integer {field}")
    return str(value)


def findings(sarif):
    """Canonical, order-independent finding set + per-rule counts."""
    keys = set()
    try:
        # Every run counts.  Reading only the first would drop the rest of
        # the document and diff the remainder as a clean sweep.
        for run in runs_of(sarif):
            for res in run["results"]:
                loc = res["locations"][0]["physicalLocation"]
                region = loc["region"]
                keys.add("\t".join([
                    res["ruleId"],
                    source_identity(loc["artifactLocation"]["uri"]),
                    coordinate(region, "startLine"),
                    coordinate(region, "startColumn"),
                ]))
    except (ValueError, KeyError, IndexError, TypeError, AttributeError) as e:
        fail(f"unusable SARIF findings: {e}")
    counts = Counter(k.split("\t", 1)[0] for k in keys)
    return keys, counts


def fmt_key(k):
    rule, uri, line, col = k.split("\t")
    return f"{uri}:{line}:{col}  {rule}"


def load_baseline_keys(path):
    """The baseline's own finding set, once it agrees with its own counts.

    A baseline that disagrees with itself is not a smaller sweep, it is a
    damaged record: its `total` and `per_rule` would then report counts
    its `findings` do not contain, and every delta printed against it
    would be measured from those counts.
    """
    try:
        with open(path) as f:
            base = json.load(f)
    except (ValueError, OSError) as e:
        fail(f"unusable baseline at {path}: {e}")
    try:
        recorded, total, per_rule = base["findings"], base["total"], base["per_rule"]
    except (KeyError, TypeError) as e:
        fail(f"unusable baseline at {path}: {e}")
    if not isinstance(recorded, list) or not isinstance(per_rule, dict):
        fail(f"unusable baseline at {path}: findings must be a list and"
             " per_rule an object of rule id to count")
    for key in recorded:
        if not isinstance(key, str) or len(key.split("\t")) != 4:
            fail(f"unusable baseline at {path}: {key!r} is not a"
                 " rule/file/line/column finding key")
    counted = dict(Counter(key.split("\t", 1)[0] for key in recorded))
    if total != len(recorded) or counted != per_rule:
        fail(f"baseline at {path} does not describe its own findings:"
             f" total says {total!r} and per_rule says {per_rule!r}, but"
             f" the file records {len(recorded)} finding(s) counting as"
             f" {counted!r}")
    return set(recorded)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", default="test/fixtures",
                    help="directory to scan; a relative path resolves against"
                         " the checkout, not the calling directory")
    ap.add_argument("--zbc", default=os.path.join(REPO, "zig-out", "bin", "zbc"))
    ap.add_argument("--baseline", default=os.path.join(HERE, "baseline.json"))
    ap.add_argument("--update", action="store_true", help="write the baseline")
    args = ap.parse_args()

    if not os.path.exists(args.zbc):
        fail(f"zbc not built at {args.zbc} (run `zig build`)")

    keys, counts = findings(run_zbc(args.zbc, args.corpus))

    if args.update:
        if not keys:
            fail(f"--update would record an empty baseline: nothing fired over"
                 f" {args.corpus}, so the analyzer or the corpus is broken, and"
                 " writing it would delete the only coverage record")
        with open(args.baseline, "w") as f:
            json.dump({
                "corpus": args.corpus,
                "total": len(keys),
                "per_rule": dict(sorted(counts.items())),
                "findings": sorted(keys),
            }, f, indent=2)
            f.write("\n")
        print(f"baseline written: {len(keys)} findings across "
              f"{len(counts)} rules over {args.corpus}")
        return

    if not os.path.exists(args.baseline):
        fail("no baseline (run --update first)")
    base_keys = load_baseline_keys(args.baseline)

    added = sorted(keys - base_keys)
    removed = sorted(base_keys - keys)

    print(f"corpus {args.corpus}: {len(keys)} findings "
          f"(baseline {len(base_keys)})")
    if not added and not removed:
        print("✓ no change vs baseline")
        return

    if added:
        print(f"\n+ {len(added)} NEW finding(s) — new catch OR false-positive regression:")
        for k in added:
            print(f"    + {fmt_key(k)}")
    if removed:
        print(f"\n- {len(removed)} REMOVED finding(s) — fixed FP OR recall regression:")
        for k in removed:
            print(f"    - {fmt_key(k)}")

    # per-rule count deltas
    base_counts = Counter(key.split("\t", 1)[0] for key in base_keys)
    deltas = {r: counts.get(r, 0) - base_counts.get(r, 0)
              for r in set(counts) | set(base_counts)}
    deltas = {r: d for r, d in deltas.items() if d}
    if deltas:
        print("\nper-rule deltas:")
        for r, d in sorted(deltas.items()):
            print(f"    {d:+d}  {r}")
    sys.exit(1)


if __name__ == "__main__":
    main()
