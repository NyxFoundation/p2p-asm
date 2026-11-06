"""Source ownership manifests are worktree-local, never implicit /tmp inputs."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import audit


class BaselineTests(unittest.TestCase):
    def test_should_not_read_external_state_when_baseline_is_unspecified(self):
        with patch.object(Path, "read_text", side_effect=AssertionError("unexpected read")):
            self.assertIsNone(audit.frozen_audit(None))

    def test_should_validate_exact_source_when_baseline_is_explicit(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/"source.lean").write_text("def example := 1\n")
            digest = hashlib.sha256((root/"source.lean").read_bytes()).hexdigest()
            baseline = root/"baseline.json"
            baseline.write_text(json.dumps({"source.lean": digest}))
            with patch.object(audit, "ROOT", root):
                self.assertEqual(audit.frozen_audit(baseline), 1)
                (root/"source.lean").write_text("def example := 2\n")
                with self.assertRaises(AssertionError):
                    audit.frozen_audit(baseline)

    def test_should_fail_when_explicit_baseline_is_missing(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(FileNotFoundError):
                audit.frozen_audit(Path(directory)/"missing.json")

    def test_should_reject_paths_outside_worktree_when_manifest_is_untrusted(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            baseline = root/"baseline.json"
            baseline.write_text(json.dumps({"../outside": "0"*64}))
            with patch.object(audit, "ROOT", root), self.assertRaises(ValueError):
                audit.frozen_audit(baseline)


if __name__ == "__main__":
    unittest.main()
