"""Regression tests for the CI proof-integrity gate (stdlib only)."""

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from audit_lean import project_sources, violations


class SourceAuditTests(unittest.TestCase):
    def test_rejects_proof_placeholders_and_axioms(self):
        source = "theorem t : True := by sorry\nexample : True := by admit\nprivate axiom x : False\n"
        self.assertEqual(list(violations(source)), [(1, "sorry"), (2, "admit"), (3, "axiom")])

    def test_comments_literals_and_identifiers_are_not_code(self):
        source = '''-- sorry
/-! axiom /- nested admit -/ more sorry -/
/-- admit -/ def sorryAx := "sorry \\" admit /- axiom"
def x := r##"sorry " admit axiom"##
def sorry' := '"'
def αsorry := 'a'
def «axiom» := Namespace.sorry
'''
        self.assertEqual(list(violations(source)), [])

    def test_adjacent_comments_preserve_tokens_and_line_numbers(self):
        self.assertEqual(list(violations("/- sorry -/\nexample := by /- admit -/sorry")), [(2, "sorry")])

    def test_interpolated_proof_is_not_hidden(self):
        self.assertEqual(list(violations('def x := s!"{(by sorry : Nat)}"')), [(1, "sorry")])
        self.assertEqual(list(violations('def x := s!"value: {42}"')), [])

    def test_unterminated_input_fails_closed(self):
        for source in ['/- sorry', '"sorry', 'r#"admit', '«axiom']:
            with self.subTest(source=source), self.assertRaises(ValueError):
                list(violations(source))

    def test_git_scope_includes_untracked_sources_but_excludes_dependencies(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            subprocess.run(["git", "init", "-q", folder], check=True)
            (root / ".gitignore").write_text(".lake/\n")
            (root / "Tracked.lean").write_text("example : True := by trivial\n")
            (root / "New.lean").write_text("example : True := by sorry\n")
            (root / ".lake").mkdir()
            (root / ".lake" / "Dependency.lean").write_text("axiom dependency : False\n")
            subprocess.run(["git", "add", "Tracked.lean"], cwd=root, check=True)
            self.assertEqual(project_sources(root), [Path("New.lean"), Path("Tracked.lean")])
            command = [sys.executable, "-B", str(Path(__file__).with_name("audit_lean.py").resolve())]
            failed = subprocess.run(command, cwd=root, capture_output=True, text=True)
            self.assertNotEqual(failed.returncode, 0)
            self.assertIn("New.lean:1: forbidden Lean token 'sorry'", failed.stderr)
            (root / "New.lean").write_text("/- sorry /- admit -/ axiom -/\n")
            passed = subprocess.run(command, cwd=root, capture_output=True, text=True)
            self.assertEqual(passed.returncode, 0, passed.stderr)
            self.assertIn("2 files", passed.stdout)
            subprocess.run(["git", "add", "-f", ".lake/Dependency.lean"], cwd=root, check=True)
            self.assertEqual(project_sources(root), [Path("New.lean"), Path("Tracked.lean")])


if __name__ == "__main__":
    unittest.main()
