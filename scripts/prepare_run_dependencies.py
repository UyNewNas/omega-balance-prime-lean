#!/usr/bin/env python3
"""Fail-closed, reproducible compatibility preparation for the pinned RUN producer.

Use `update` instead of a bare `lake update`: restore this adapter's proof edits,
run every original upstream post_update check, then apply the reviewed 4.34 edits.
The next Lake process reloads the narrowed library ownership. No proof is vendored.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tomllib

from check_sources import FORBIDDEN, erase_comments_and_strings

ROOT = Path(__file__).resolve().parents[1]
SPEC_PATH = ROOT / 'lake-compat/run-compatibility.json'
REPORT_PATH = ROOT / 'reports/f3_run_dependency_resolution.json'


class CompatibilityError(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise CompatibilityError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def package_dir(spec, name):
    return ROOT / '.lake/packages' / spec['packages'][name]['directory']


def git_head(directory):
    return subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'],
                                   text=True).strip()


def validate_manifest_entries(spec, manifest):
    names = [item['name'] for item in manifest['packages']]
    require(len(names) == len(set(names)), 'Duplicate resolved package names')
    entries = {item['name']: item for item in manifest['packages']}
    for name, pin in spec['packages'].items():
        # Lake pretty-prints this exact quoted Name with guillemets. Do not
        # normalize/strip arbitrary package names or accept aliases.
        entry = entries.get(pin['manifest_name'], {})
        require(entry.get('type') == 'git' and entry.get('rev') == pin['rev']
                and entry.get('url') == pin['url']
                and entry.get('subDir') == pin.get('subDir'),
                f'Actual Lake manifest does not resolve the required {name} source')


def validate_pins(spec, resolved):
    require((ROOT / 'lean-toolchain').read_text().strip() == spec['toolchain'],
            'Root Lean toolchain changed; refusing compatibility patches')
    config = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    declared = {item['name']: item for item in config.get('require', [])}
    for name, pin in spec['packages'].items():
        if pin['direct']:
            require(name in declared and declared[name].get('rev') == pin['rev']
                    and declared[name].get('git') == pin['url'],
                    f'Root declaration does not preserve immutable {name} pin')
    if not resolved:
        return
    raw_manifest = (ROOT / 'lake-manifest.json').read_bytes()
    manifest = json.loads(raw_manifest)
    validate_manifest_entries(spec, manifest)
    require(digest(raw_manifest) == spec['resolved_manifest_sha256'],
            'Resolved Lake manifest differs from the recorded actual pinned resolution')
    for name, pin in spec['packages'].items():
        directory = package_dir(spec, name)
        require(directory.is_dir() and git_head(directory) == pin['rev'],
                f'Actual {name} checkout does not match its source SHA')
    for item in spec['upstream_patches']:
        path = package_dir(spec, 'lean-proofs-latest') / item['path']
        require(digest(path.read_bytes()) == item['sha256'],
                f'Original upstream compatibility patch changed: {path}')
    return manifest


def replacement_result(text, replacements):
    """Every hunk has an exact multiplicity; never perform a fuzzy replacement."""
    for hunk in replacements:
        require(text.count(hunk['old']) == hunk['count'],
                f'Exact compatibility hunk mismatch: {hunk["old"][:100]!r}')
        text = text.replace(hunk['old'], hunk['new'])
    return text


def planned_edit(path, entry, restore=False):
    current = path.read_bytes()
    current_hash = digest(current)
    before, after = entry['before_sha256'], entry['after_sha256']
    if restore:
        if current_hash in {before, entry['original_sha256']}:
            return None
        require(current_hash == after, f'Unrecognized modified source: {path}')
        inverse = [{'old': h['new'], 'new': h['old'], 'count': h['count']}
                   for h in reversed(entry['replacements'])]
        target = replacement_result(current.decode('utf-8'), inverse).encode('utf-8')
        require(digest(target) == before, f'Reverse hunk digest mismatch: {path}')
    else:
        if current_hash == after:
            return None
        require(current_hash == before, f'Expected checked upstream patch state: {path}')
        target = replacement_result(current.decode('utf-8'), entry['replacements']).encode('utf-8')
        require(digest(target) == after, f'Forward hunk digest mismatch: {path}')
    return path, target


def write_plan(plan):
    # Validate the entire plan before modifying any source; replacement is per-file atomic.
    for path, data in plan:
        temporary = path.with_name(path.name + '.f3-compat-tmp')
        require(not temporary.exists(), f'Unexpected temporary file: {temporary}')
    for path, data in plan:
        temporary = path.with_name(path.name + '.f3-compat-tmp')
        temporary.write_bytes(data)
        temporary.replace(path)


def restore(spec):
    plan = []
    for name, pin in spec['packages'].items():
        directory = package_dir(spec, name)
        if directory.exists():
            require(git_head(directory) == pin['rev'], f'Unexpected existing {name} checkout SHA')
    producer = package_dir(spec, 'lean-proofs-latest')
    if producer.exists():
        subprocess.run(['git', '-C', str(producer), 'diff', '--exit-code', 'HEAD',
                        '--', 'src/latest/patches'], check=True)
    for entry in spec['edits']:
        if entry['kind'] != 'proof':
            path = package_dir(spec, entry['package']) / entry['path']
            if path.exists():
                require(digest(path.read_bytes()) in
                        {entry['before_sha256'], entry['after_sha256']},
                        f'Unrecognized dependency configuration: {path}')
            continue
        path = package_dir(spec, entry['package']) / entry['path']
        if path.exists():
            change = planned_edit(path, entry, restore=True)
            if change:
                plan.append(change)
    write_plan(plan)


def prepare(spec):
    validate_pins(spec, resolved=True)
    plan = []
    for entry in spec['edits']:
        path = package_dir(spec, entry['package']) / entry['path']
        change = planned_edit(path, entry)
        if change:
            plan.append(change)
    write_plan(plan)


def check(spec):
    manifest = validate_pins(spec, resolved=True)
    for entry in spec['edits']:
        path = package_dir(spec, entry['package']) / entry['path']
        require(digest(path.read_bytes()) == entry['after_sha256'],
                f'Compatibility edit not prepared: {path}')
    producer_artifacts = (package_dir(spec, 'lean-proofs-latest') /
                          'src/latest/.lake/build/lib/lean')
    for name in ['PrimeNumberTheoremAnd', 'PrimeNumberTheoremAnd.olean']:
        stale = producer_artifacts / name
        require(not stale.exists(),
                f'Stale duplicate PNT build artifacts: {stale}. '
                'Remove only the generated lean-proofs .lake/build cache and rerun update.')
    counts = {}
    for module, entry in spec['closure'].items():
        path = package_dir(spec, entry['package']) / entry['path']
        data = path.read_bytes()
        require(digest(data) == entry['prepared_sha256'], f'Closure source drift: {path}')
        clean = erase_comments_and_strings(data.decode('utf-8'))
        require(not FORBIDDEN.search(clean), f'Forbidden proof escape in {path}')
        counts[entry['package']] = counts.get(entry['package'], 0) + 1
    # The exact modified producer lakefile owns only the explicit 77-module globs.
    # ANT remains the sole owner of PrimeNumberTheoremAnd; neither our library nor
    # its audited closure contains that namespace.
    report = {
        'toolchain': spec['toolchain'],
        'packages': manifest['packages'],
        'compatibility_spec_sha256': digest(SPEC_PATH.read_bytes()),
        'closure_files_checked': counts,
        'kernel_verification': 'NOT RUN by this source/pin preparation check',
    }
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(f'RUN dependency source/pin check PASS: {sum(counts.values())} modules; '
          'kernel build and executed axiom audit still required.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['update', 'prepare', 'check'])
    args = parser.parse_args()
    try:
        spec = json.loads(SPEC_PATH.read_text())
        validate_pins(spec, resolved=False)
        if args.mode == 'update':
            restore(spec)
            subprocess.run(['lake', 'update'], cwd=ROOT, check=True)
        if args.mode in {'update', 'prepare'}:
            prepare(spec)
        check(spec)
    except (CompatibilityError, OSError, subprocess.CalledProcessError, ValueError, KeyError) as error:
        print(f'RUN dependency preparation FAILED: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
