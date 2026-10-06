import contextlib
import io
import json
import os
import pathlib
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

import regress


# A stand-in for the analyzer binary: it writes one SARIF document to
# stdout, one operational line to stderr, and exits with `status`.  The
# harness runs it exactly as it runs zbc, so the tests below observe the
# exit codes a CI consumer sees rather than the harness's internals.
FAKE_ZBC = """#!{python}
import sys

sys.stderr.write({stderr!r})
sys.stdout.write({payload!r})
sys.exit({status})
"""


def fake_analyzer(directory, payload, *, status=0):
    """Write the stand-in analyzer binary that emits `payload`; return it."""
    path = pathlib.Path(directory) / "zbc"
    path.write_text(FAKE_ZBC.format(
        python=sys.executable,
        stderr="zbc: selected=1 analyzed=1 failed=0 findings=1\n",
        payload=payload,
        status=status,
    ))
    path.chmod(0o755)
    return str(path)


def result(rule="heap-double-free", relative="test/fixtures/owner.zig",
           line=7, column=3, *, uri=None, region=None):
    """One SARIF result, shaped like the ones zbc writes."""
    location = {"artifactLocation": {"uri": (
        uri if uri is not None
        else (pathlib.Path(regress.REPO) / relative).as_uri())}}
    if region is not None:
        location["region"] = region
    else:
        location["region"] = {"startLine": line, "startColumn": column}
    return {"ruleId": rule, "locations": [{"physicalLocation": location}]}


def document(*results):
    """A SARIF document carrying exactly these results, in one run."""
    return {"runs": [{"results": list(results)}]}


def run(*results, invocations=...):
    """One run of a SARIF document carrying exactly these results."""
    member = {"results": list(results)}
    if invocations is not ...:
        member["invocations"] = invocations
    return member


def sarif(invocations, *, rule="heap-double-free", relative="test/fixtures/owner.zig"):
    """One SARIF document shaped like the one zbc emits.

    `invocations` is spliced in verbatim, so a test can supply the
    records zbc does write, drop them, or omit the member entirely.
    """
    return json.dumps({"runs": [run(result(rule, relative),
                                   invocations=invocations)]})


COMPLETED = [{"executionSuccessful": True}]


class HarnessFixture(unittest.TestCase):
    """Scratch space plus the two ways the harness is driven."""

    def setUp(self):
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        self.scratch = scratch.name
        self.baseline = pathlib.Path(self.scratch) / "baseline.json"

    def analyzer(self, payload, *, status=0):
        return fake_analyzer(self.scratch, payload, status=status)

    def scan(self, payload, **kwargs):
        """Hand `payload` to the harness and require the exit-2 verdict."""
        with contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as failure:
                regress.run_zbc(self.analyzer(payload, **kwargs), "test/fixtures")
        self.assertEqual(failure.exception.code, 2)

    def gate(self, payload, *extra, **kwargs):
        """Run `regress.main`; return (exit code or None, stdout)."""
        argv = [
            "regress.py",
            "--zbc", self.analyzer(payload, **kwargs),
            "--baseline", str(self.baseline),
            "--corpus", "test/fixtures",
            *extra,
        ]
        out = io.StringIO()
        with mock.patch.object(sys, "argv", argv), \
                contextlib.redirect_stdout(out), \
                contextlib.redirect_stderr(io.StringIO()):
            try:
                regress.main()
            except SystemExit as stop:
                return stop.code, out.getvalue()
        return None, out.getvalue()

    def rebase(self):
        """Record the standard sweep as the baseline the gate compares to."""
        code, _ = self.gate(sarif(COMPLETED), "--update")
        self.assertIsNone(code)


class AnalyzerStreamTests(HarnessFixture):
    """A stream the harness cannot trust must not read as a clean sweep."""

    def test_no_invocation_metadata_is_not_evidence_of_a_complete_sweep(self):
        self.scan(sarif(None))

    def test_an_invocation_without_a_completion_record_is_not_evidence_of_a_complete_sweep(self):
        self.scan(sarif([{}]))

    def test_an_empty_invocation_list_is_not_evidence_of_a_complete_sweep(self):
        self.scan(sarif([]))

    def test_an_explicitly_failed_invocation_is_not_evidence_of_a_complete_sweep(self):
        self.scan(sarif([{"executionSuccessful": False}]))

    def test_a_truthy_non_boolean_completion_flag_is_still_not_a_completion_record(self):
        self.scan(sarif([{"executionSuccessful": "true"}]))

    def test_a_run_that_carries_no_results_member_is_a_harness_error(self):
        # A genuinely empty result set is a finding delta; a run with no
        # `results` member at all is not a shape this harness can read.
        code, _ = self.gate(json.dumps({"runs": [{"invocations": COMPLETED}]}))
        self.assertEqual(code, 2)

    def test_unparsable_stdout_is_a_harness_error(self):
        self.scan('{"runs": [{"results": [')

    def test_an_analyzer_failure_outranks_a_parsable_document(self):
        self.scan(sarif(COMPLETED), status=2)


class CompletionRecordTests(HarnessFixture):
    """Every run of the document, not just the first, must be accounted for."""

    def scan_document(self, payload, **kwargs):
        return self.gate(json.dumps(payload), **kwargs)[0]

    def test_a_document_with_no_run_is_a_harness_error(self):
        self.assertEqual(self.scan_document({"runs": []}), 2)

    def test_a_second_run_without_a_completion_record_is_a_harness_error(self):
        self.assertEqual(self.scan_document({
            "runs": [run(result(), invocations=COMPLETED),
                     run(result("arena-use-after-kill"), invocations=None)]}),
            2)

    def test_a_second_run_that_reports_no_completion_is_a_harness_error(self):
        self.assertEqual(self.scan_document({
            "runs": [run(result(), invocations=COMPLETED),
                     run(result("arena-use-after-kill"),
                         invocations=[{"executionSuccessful": False}])]}),
            2)

    def test_every_run_is_diffed_not_just_the_first(self):
        # A run the harness cannot see is a finding it cannot lose: were
        # only the first run read, this second one would not appear.
        self.rebase()
        code, out = self.gate(json.dumps({"runs": [
            run(result(), invocations=COMPLETED),
            run(result("arena-use-after-kill"), invocations=COMPLETED)]}))
        self.assertEqual(code, 1)
        self.assertIn("arena-use-after-kill", out)


class FindingGateTests(HarnessFixture):
    """The exit code is the gate CI reads; 2 must never masquerade as 1."""

    def test_a_matching_sweep_exits_zero(self):
        self.rebase()
        code, _ = self.gate(sarif(COMPLETED))
        self.assertIsNone(code)

    def test_a_real_finding_change_exits_one(self):
        self.rebase()
        code, out = self.gate(sarif(COMPLETED, rule="arena-use-after-kill"))
        self.assertEqual(code, 1)
        self.assertIn("arena-use-after-kill", out)

    def test_an_incomplete_sweep_never_reports_a_finding_delta(self):
        # The changed finding would be a legitimate exit 1 — if the sweep
        # that produced it could be trusted as complete.
        self.rebase()
        code, _ = self.gate(sarif(None, rule="arena-use-after-kill"))
        self.assertEqual(code, 2)

    def test_a_complete_sweep_with_no_results_is_a_finding_delta(self):
        # Nothing firing is a real answer about the corpus, so it is the
        # removed findings that the gate must report — never a clean run.
        self.rebase()
        code, out = self.gate(json.dumps({"runs": [run(invocations=COMPLETED)]}))
        self.assertEqual(code, 1)
        self.assertIn("heap-double-free", out)

    def test_a_baseline_whose_total_disagrees_with_its_findings_is_a_harness_error(self):
        self.rebase()
        recorded = json.loads(self.baseline.read_text())
        recorded["total"] += 1
        self.baseline.write_text(json.dumps(recorded))
        code, _ = self.gate(sarif(COMPLETED))
        self.assertEqual(code, 2)

    def test_a_baseline_whose_per_rule_counts_disagree_is_a_harness_error(self):
        self.rebase()
        recorded = json.loads(self.baseline.read_text())
        recorded["per_rule"]["heap-double-free"] += 1
        self.baseline.write_text(json.dumps(recorded))
        code, _ = self.gate(sarif(COMPLETED))
        self.assertEqual(code, 2)

    def test_a_malformed_finding_key_in_the_baseline_is_a_harness_error(self):
        self.rebase()
        recorded = json.loads(self.baseline.read_text())
        recorded["findings"] = ["heap-double-free test/fixtures/owner.zig"]
        recorded["total"] = 1
        recorded["per_rule"] = {"heap-double-free": 1}
        self.baseline.write_text(json.dumps(recorded))
        code, _ = self.gate(sarif(COMPLETED))
        self.assertEqual(code, 2)

    def test_an_unparsable_baseline_is_a_harness_error(self):
        self.rebase()
        self.baseline.write_text('{"findings": [')
        code, _ = self.gate(sarif(COMPLETED))
        self.assertEqual(code, 2)

    def test_an_update_that_would_record_no_findings_leaves_the_baseline_alone(self):
        self.rebase()
        before = self.baseline.read_text()
        code, _ = self.gate(json.dumps(document(run(invocations=COMPLETED))), "--update")
        self.assertEqual(code, 2)
        self.assertEqual(self.baseline.read_text(), before)

    def test_an_unusable_sweep_never_reports_a_finding_delta(self):
        self.rebase()
        code, _ = self.gate('{"runs": [{"results": [')
        self.assertEqual(code, 2)

    def test_an_unusable_sweep_never_rebaselines_the_corpus(self):
        self.rebase()
        code, _ = self.gate('{"runs": [{"results": [', "--update")
        self.assertEqual(code, 2)
        recorded = json.loads(self.baseline.read_text())
        self.assertEqual(recorded["per_rule"], {"heap-double-free": 1})


class SymlinkedCheckoutTests(unittest.TestCase):
    """Where the checkout lives must not change what a finding is.

    zbc resolves every source root before reporting a path, so a sweep
    started from a symlinked spelling of the checkout still reports the
    real paths underneath it.  Reading those against the unresolved
    spelling spells each one `../..`-deep, which no committed baseline
    holds: every finding reads as one added and one removed at once.
    """

    def setUp(self):
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        self.scratch = pathlib.Path(scratch.name)
        self.baseline = self.scratch / "baseline.json"
        # A second spelling of this tree.  Cleanup unlinks it rather than
        # walking through it, so the checkout it points at is never what
        # gets removed.
        self.checkout = self.scratch / "checkout"
        self.checkout.symlink_to(regress.REPO, target_is_directory=True)
        self.addCleanup(self.checkout.unlink, missing_ok=True)
        self.zbc = fake_analyzer(self.scratch, json.dumps(
            document(run(result(), invocations=COMPLETED))))

    def harness(self, checkout, *extra):
        """Run the harness script as CI does; return (exit code, output)."""
        argv = [
            sys.executable,
            str(checkout / "tools/metrics/regress.py"),
            "--zbc", self.zbc,
            "--baseline", str(self.baseline),
            "--corpus", "test/fixtures",
            *extra,
        ]
        done = subprocess.run(argv, capture_output=True, text=True,
                              env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
        return done.returncode, done.stdout + done.stderr

    def test_a_sweep_through_a_symlinked_checkout_reads_as_the_same_findings(self):
        code, out = self.harness(pathlib.Path(regress.REPO), "--update")
        self.assertEqual(code, 0, out)
        self.assertIn("test/fixtures/owner.zig", self.baseline.read_text())
        code, out = self.harness(self.checkout)
        self.assertEqual(code, 0, out)
        self.assertIn("no change vs baseline", out)


class FindingsTests(unittest.TestCase):
    def test_file_uri_uses_checkout_relative_source_identity(self):
        source = pathlib.Path(regress.REPO) / "test/fixtures/owner.zig"
        keys, counts = regress.findings(document(result(uri=source.as_uri())))
        self.assertEqual(keys, {"heap-double-free\ttest/fixtures/owner.zig\t7\t3"})
        self.assertEqual(counts, {"heap-double-free": 1})

    def test_a_file_outside_the_checkout_is_not_the_finding_of_one_inside_it(self):
        inside = (pathlib.Path(regress.REPO) / "test/fixtures/owner.zig").as_uri()
        outside = (pathlib.Path(regress.REPO).parent / "elsewhere/owner.zig").as_uri()
        keys, counts = regress.findings(document(result(uri=inside),
                                                  result(uri=outside)))
        self.assertEqual(keys, {
            "heap-double-free\ttest/fixtures/owner.zig\t7\t3",
            "heap-double-free\t../elsewhere/owner.zig\t7\t3",
        })
        self.assertEqual(counts, {"heap-double-free": 2})

    def test_a_relative_uri_is_decoded_to_the_same_identity(self):
        keys, _ = regress.findings(document(result(uri="test/fixtures/owner%20%231.zig")))
        self.assertEqual(keys, {"heap-double-free\ttest/fixtures/owner #1.zig\t7\t3"})

    def test_a_remote_file_uri_is_decoded_and_keeps_its_host(self):
        keys, _ = regress.findings(document(result(uri="file://ci/owner%20%231.zig")))
        self.assertEqual(keys, {"heap-double-free\tfile://ci/owner #1.zig\t7\t3"})

    def test_a_finding_without_a_line_is_a_harness_error_not_a_shared_bucket(self):
        with contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as failure:
                regress.findings(document(result(region={"startColumn": 3})))
        self.assertEqual(failure.exception.code, 2)

    def test_a_finding_without_a_column_is_a_harness_error_not_a_shared_bucket(self):
        with contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as failure:
                regress.findings(document(result(region={"startLine": 7})))
        self.assertEqual(failure.exception.code, 2)

    def test_escaped_path_characters_preserve_source_identity(self):
        source = pathlib.Path(regress.REPO) / "test/fixtures/owner #1.zig"
        keys, _ = regress.findings(document(result(uri=source.as_uri())))
        self.assertEqual(keys, {"heap-double-free\ttest/fixtures/owner #1.zig\t7\t3"})

    def test_a_document_with_no_run_is_not_an_empty_sweep(self):
        with contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as failure:
                regress.findings({"runs": []})
        self.assertEqual(failure.exception.code, 2)


if __name__ == "__main__":
    unittest.main()
