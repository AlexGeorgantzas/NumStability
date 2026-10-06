import importlib.util
import unittest
from pathlib import Path


MODULE_PATH = Path(__file__).with_name("analyze.py")
SPEC = importlib.util.spec_from_file_location("library_usage_analyze", MODULE_PATH)
assert SPEC and SPEC.loader
analyze = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(analyze)


class LexicalScanTests(unittest.TestCase):
    def test_imports_comments_strings_and_live_names(self):
        source = '''import NumStability.Analysis.Rounding
/- NumStability.fake /- NumStability.nested -/ -/
-- NumStability.comment
def text : String := "NumStability.string"
theorem sample : True := by
  have _ := NumStability.gamma_nonneg
  have _ := NumStability.gamma_nonneg
  trivial
'''
        metrics = analyze.lexical_counts(source, {"NumStability.gamma_nonneg"})
        self.assertEqual(metrics["imports"], 1)
        self.assertEqual(metrics["qualified_occurrences"], 2)
        self.assertEqual(metrics["qualified_distinct"], 1)
        self.assertEqual(metrics["qualified_live_distinct"], 1)

    def test_scoring_boundaries(self):
        self.assertEqual(analyze.score(0, 0), 0)
        self.assertEqual(analyze.score(2, 0), 1)
        self.assertEqual(analyze.score(2, 1), 2)
        self.assertEqual(analyze.score(2, 2), 3)


if __name__ == "__main__":
    unittest.main()
