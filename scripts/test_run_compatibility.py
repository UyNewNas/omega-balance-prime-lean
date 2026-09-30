#!/usr/bin/env python3
"""Fail-closed and idempotence tests, independent of downloading or running Lean."""
from pathlib import Path
import tempfile
import json
from unittest.mock import patch
import unittest
import prepare_run_dependencies as compat


class PatchTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name) / 'Proof.lean'
        self.before = b'example := old_api\n'
        self.after = b'example := new_api\n'
        self.entry = {
            'original_sha256': compat.digest(b'original upstream state\n'),
            'before_sha256': compat.digest(self.before),
            'after_sha256': compat.digest(self.after),
            'replacements': [{'old': 'old_api', 'new': 'new_api', 'count': 1}],
        }

    def test_forward_then_idempotent(self):
        self.path.write_bytes(self.before)
        compat.write_plan([compat.planned_edit(self.path, self.entry)])
        self.assertEqual(self.path.read_bytes(), self.after)
        self.assertIsNone(compat.planned_edit(self.path, self.entry))

    def test_restore_then_idempotent(self):
        self.path.write_bytes(self.after)
        compat.write_plan([compat.planned_edit(self.path, self.entry, restore=True)])
        self.assertEqual(self.path.read_bytes(), self.before)
        self.assertIsNone(compat.planned_edit(self.path, self.entry, restore=True))

    def test_original_state_allowed_only_for_restore(self):
        self.path.write_bytes(b'original upstream state\n')
        self.assertIsNone(compat.planned_edit(self.path, self.entry, restore=True))
        with self.assertRaises(compat.CompatibilityError):
            compat.planned_edit(self.path, self.entry)

    def test_source_drift_fails_without_write(self):
        data = self.before + b'-- unrelated edit\n'
        self.path.write_bytes(data)
        for restore in [False, True]:
            with self.assertRaises(compat.CompatibilityError):
                compat.planned_edit(self.path, self.entry, restore=restore)
        self.assertEqual(self.path.read_bytes(), data)

    def test_wrong_hunk_multiplicity_fails(self):
        for text in ['', 'old_api old_api']:
            with self.assertRaises(compat.CompatibilityError):
                compat.replacement_result(text, self.entry['replacements'])

    def test_wrong_target_hash_fails(self):
        self.path.write_bytes(self.before)
        entry = dict(self.entry, after_sha256='0' * 64)
        with self.assertRaises(compat.CompatibilityError):
            compat.planned_edit(self.path, entry)
        self.assertEqual(self.path.read_bytes(), self.before)

    def test_wrong_reverse_hash_fails(self):
        self.path.write_bytes(self.after)
        entry = dict(self.entry, before_sha256='0' * 64)
        with self.assertRaises(compat.CompatibilityError):
            compat.planned_edit(self.path, entry, restore=True)

    def test_preexisting_temporary_file_fails(self):
        self.path.write_bytes(self.before)
        temporary = self.path.with_name(self.path.name + '.f3-compat-tmp')
        temporary.write_text('do not overwrite')
        with self.assertRaises(compat.CompatibilityError):
            compat.write_plan([compat.planned_edit(self.path, self.entry)])
        self.assertEqual(self.path.read_bytes(), self.before)
        self.assertEqual(temporary.read_text(), 'do not overwrite')

    def test_actual_pins_and_checkout_are_required(self):
        root = Path(self.directory.name)
        spec = {'toolchain': 'leanprover/lean4:v4.34.0', 'upstream_patches': [], 'packages': {
            'mathlib': {'direct': True, 'rev': 'abc', 'url': 'https://example.org/mathlib',
                        'directory': 'mathlib', 'manifest_name': 'mathlib'}}}
        (root / 'lean-toolchain').write_text(spec['toolchain'] + '\n')
        (root / 'lakefile.toml').write_text(
            '[[require]]\nname="mathlib"\nrev="abc"\ngit="https://example.org/mathlib"\n')
        (root / '.lake/packages/mathlib').mkdir(parents=True)
        entry = {'name': 'mathlib', 'type': 'git', 'rev': 'abc',
                 'url': 'https://example.org/mathlib', 'subDir': None}
        spec['resolved_manifest_sha256'] = compat.digest(
            json.dumps({'packages': [entry]}).encode())
        with patch.object(compat, 'ROOT', root), patch.object(compat, 'git_head', return_value='abc'):
            (root / 'lake-manifest.json').write_text(json.dumps({'packages': [entry]}))
            compat.validate_pins(spec, resolved=True)
            for field, wrong in [('rev', 'wrong'), ('url', 'wrong'), ('subDir', 'wrong')]:
                altered = dict(entry, **{field: wrong})
                (root / 'lake-manifest.json').write_text(json.dumps({'packages': [altered]}))
                with self.assertRaises(compat.CompatibilityError):
                    compat.validate_pins(spec, resolved=True)
            (root / 'lake-manifest.json').write_text(json.dumps({'packages': []}))
            with self.assertRaises(compat.CompatibilityError):
                compat.validate_pins(spec, resolved=True)
            (root / 'lake-manifest.json').write_text(json.dumps({'packages': [entry]}))
            with patch.object(compat, 'git_head', return_value='wrong'):
                with self.assertRaises(compat.CompatibilityError):
                    compat.validate_pins(spec, resolved=True)


class GiantPowerPatchTests(unittest.TestCase):
    def test_symbolic_extraction_bound_keeps_exact_statement(self):
        spec = json.loads(compat.SPEC_PATH.read_text())
        module = 'ErdosProblems.Erdos6.BFTExtraction'
        closure = spec['closure'][module]
        entries = [entry for entry in spec['edits']
                   if entry['package'] == closure['package']
                   and entry['path'] == closure['path']]
        self.assertEqual(len(entries), 1)
        entry = entries[0]
        self.assertEqual(entry['kind'], 'proof')
        self.assertEqual(entry['original_sha256'], entry['before_sha256'])
        self.assertEqual(entry['after_sha256'], closure['prepared_sha256'])
        self.assertEqual(entry['replacements'], [{
            'old': '  have hzmax : z ≤ n + 2 ^ largeK := by omega\n',
            'new': '  have hzmax : z ≤ n + 2 ^ largeK :=\n'
                   '    Nat.le_trans (Nat.le_of_lt hzhi) (Nat.add_le_add_left hbmax n)\n',
            'count': 1,
        }])
        hunk = entry['replacements'][0]
        self.assertEqual(hunk['old'].split(':=')[0], hunk['new'].split(':=')[0])
        self.assertIsNone(compat.FORBIDDEN.search(hunk['new']))


class ActualManifestTests(unittest.TestCase):
    def setUp(self):
        self.spec = json.loads(compat.SPEC_PATH.read_text())
        self.raw = (compat.ROOT / 'lake-manifest.json').read_bytes()
        self.manifest = json.loads(self.raw)

    def test_observed_resolution_and_exact_bytes(self):
        self.assertEqual(compat.digest(self.raw), self.spec['resolved_manifest_sha256'])
        compat.validate_manifest_entries(self.spec, self.manifest)
        self.assertIn('«lean-proofs-latest»',
                      [entry['name'] for entry in self.manifest['packages']])
        self.assertEqual(self.spec['packages']['lean-proofs-latest']['manifest_name'],
                         '«lean-proofs-latest»')

    def test_every_source_pin_field_is_required(self):
        for name, pin in self.spec['packages'].items():
            for field in ['rev', 'url', 'subDir', 'type']:
                with self.subTest(package=name, field=field):
                    changed = json.loads(self.raw)
                    entry = next(e for e in changed['packages']
                                 if e['name'] == pin['manifest_name'])
                    entry[field] = 'unapproved'
                    with self.assertRaises(compat.CompatibilityError):
                        compat.validate_manifest_entries(self.spec, changed)

    def test_unquoted_or_differently_quoted_name_is_not_an_alias(self):
        for name in ['lean-proofs-latest', '««lean-proofs-latest»»',
                     '"lean-proofs-latest"']:
            changed = json.loads(self.raw)
            entry = next(e for e in changed['packages']
                         if e['name'] == '«lean-proofs-latest»')
            entry['name'] = name
            with self.assertRaises(compat.CompatibilityError):
                compat.validate_manifest_entries(self.spec, changed)

    def test_missing_or_duplicate_package_is_rejected(self):
        changed = json.loads(self.raw)
        changed['packages'] = [e for e in changed['packages']
                               if e['name'] != '«lean-proofs-latest»']
        with self.assertRaises(compat.CompatibilityError):
            compat.validate_manifest_entries(self.spec, changed)
        changed = json.loads(self.raw)
        changed['packages'].append(dict(changed['packages'][0]))
        with self.assertRaises(compat.CompatibilityError):
            compat.validate_manifest_entries(self.spec, changed)


if __name__ == '__main__':
    unittest.main()
