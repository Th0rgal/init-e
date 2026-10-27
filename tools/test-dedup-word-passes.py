#!/usr/bin/env python3
"""Regression checks for cross-pass structural sharing and literal token handling."""
import importlib.util
import tempfile
import subprocess
import sys
import unittest
from pathlib import Path

spec = importlib.util.spec_from_file_location('dedup', Path(__file__).with_name('dedup-word-passes.py'))
dedup = importlib.util.module_from_spec(spec)
spec.loader.exec_module(dedup)


class SharingTests(unittest.TestCase):
    def test_cross_pass_sharing_and_idempotence(self):
        with tempfile.TemporaryDirectory() as directory:
            previous = dedup.ROOT
            dedup.ROOT = Path(directory)
            try:
                root = dedup.ROOT / 'submission/InitECandidate/Proofs/WordStages'
                root.mkdir(parents=True)
                for i in range(11):
                    body = ('Flapjack.WordLangProgHOL.skip' if i < 2 else
                            f'.seq word1_0_0 word1_1_0')
                    (root / f'Pass1_{i}.lean').write_text(
                        f'def word1_{i}_0 : WordLangProgHOL (BitVec 64) :=\n{body}\n\n'
                        f'def pass1_{i} : WordLangProgHOL (BitVec 64) :=\nword1_{i}_0\n'
                        f'theorem pass1_{i}_eq : pass1_{i} = pass1_{i} := rfl\nend Test\n')
                metrics = dedup.dedup(1, True)
                self.assertEqual(metrics['removed_nodes'], 9)
                self.assertIn('.seq word1_0_0 word1_0_0', (root / 'Pass1_2.lean').read_text())
                self.assertIn(':=\nword1_2_0', (root / 'Pass1_10.lean').read_text())
                self.assertEqual(dedup.dedup(1, True)['removed_nodes'], 0)
            finally:
                dedup.ROOT = previous

    def test_sparse_keeps_nodes_referenced_only_by_later_passes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tools = root / 'tools'
            tools.mkdir()
            script = tools / 'compact-word-data.py'
            script.write_text(Path(__file__).with_name(script.name).read_text())
            base = root / 'submission/InitECandidate/Proofs/WordStages/Parallel1'
            base.mkdir(parents=True)
            for i in range(11):
                body = ('def word1_0_0 : WordLangProgHOL (BitVec 64) :=\n.skip\n\n'
                        if i == 0 else '')
                root_body = 'word1_0_0' if i == 1 else '.skip'
                (base / f'Data{i}.lean').write_text(
                    'namespace Test\n' + body +
                    f'def pass1_{i} : WordLangProgHOL (BitVec 64) := {root_body}\nend Test\n')
                (base / f'Proof{i}.lean').write_text('')
            subprocess.run([sys.executable, str(script), '1'], check=True, capture_output=True)
            sparse = base.with_name('Sparse1')
            self.assertIn('def word1_0_0', (sparse / 'Data0.lean').read_text())
            self.assertIn(':= word1_0_0', (sparse / 'Data1.lean').read_text())

    def test_ffi_strings_and_identifier_boundaries(self):
        text = 'word1_0_0 "word1_0_0" "space  inside" prefix_word1_0_0'
        self.assertEqual(dedup.rename_nodes(text, {'word1_0_0': 'word1_2_0'}),
                         'word1_2_0 "word1_0_0" "space  inside" prefix_word1_0_0')
        self.assertNotEqual(tuple(dedup.TOKEN.findall('"a  b"')),
                            tuple(dedup.TOKEN.findall('"a b"')))


if __name__ == '__main__':
    unittest.main()
