#!/usr/bin/env python3
"""Fresh kernel checks of all project modules, with an explicitly pinned cache."""
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
MODULES = ['Moments', 'Arbor', 'Count', 'ComplexFTA', 'RootObstruction', 'Main', 'Audit', 'Solution']
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def code_only(text):
    # These project sources have no string literals. Handle nested Lean comments.
    result, depth, i = [], 0, 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1
            i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text[i:i+2] == '--':
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        else:
            result.append(text[i])
            i += 1
    assert depth == 0, 'Unclosed source comment'
    return ''.join(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package-root', type=Path, default=ROOT/'.lake/packages')
    parser.add_argument('--lean', default='lean', help='elan Lean launcher')
    args = parser.parse_args()
    packages = args.package_root.resolve()
    stamp = dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    run = ROOT/'verification'/('clean-'+stamp)
    run.mkdir(parents=True, exist_ok=False)
    pins = json.loads((ROOT/'lake-manifest.json').read_text())['packages']
    expected_sources = json.loads((ROOT/'SOURCES.json').read_text())
    result = {'status': 'RUNNING', 'started_at_utc': stamp, 'records': [],
              'dependencies': [], 'source_hashes': expected_sources,
              'trust_boundary': 'All own modules freshly compiled; pinned dependency oleans reused. This run does not rebuild mathlib or the Lean compiler.',
              'verification_script_sha256': digest(Path(__file__)),
              'package_root': str(packages)}

    def save():
        (run/'result.json').write_text(json.dumps(result, indent=2)+'\n')

    try:
        for name, sha in expected_sources.items():
            assert digest(ROOT/name) == sha, 'Source/configuration hash mismatch: '+name
        for module in MODULES:
            code = code_only((ROOT/(module+'.lean')).read_text())
            assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|run_elab)\b', code), module
            for imported in re.findall(r'^(?:public )?import\s+(\S+)', code, flags=re.M):
                assert imported in MODULES or imported.startswith('Mathlib.'), imported
            shutil.copy2(ROOT/(module+'.lean'), run/(module+'.lean'))
        paths = [str(run)]
        for pin in pins:
            directory = packages/pin['name']
            head = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
            dirty = subprocess.check_output(['git', '-C', str(directory), 'status', '--porcelain', '--untracked-files=no'], text=True).strip()
            record = {'name': pin['name'], 'expected_rev': pin['rev'], 'actual_rev': head, 'tracked_changes': dirty}
            result['dependencies'].append(record)
            assert head == pin['rev'] and not dirty, 'Dependency source mismatch: '+pin['name']
            lib = directory/'.lake/build/lib/lean'
            if lib.is_dir():
                paths.append(str(lib))
        environment = os.environ.copy()
        environment['LEAN_PATH'] = os.pathsep.join(paths)
        toolchain = (ROOT/'lean-toolchain').read_text().strip()
        base = [args.lean, '+'+toolchain]
        version = subprocess.check_output(base+['--version'], text=True)
        (run/'lean-version.txt').write_text(version)
        result['lean_version'] = version.strip()
        assert 'version 4.35.0-rc3' in version, version
        base += ['-M4096', '-j1', '-DmaxRecDepth=8192', '-DmaxHeartbeats=2000000']
        for module in MODULES:
            source = run/(module+'.lean')
            output = run/(module+'.olean')
            command = base+['-o', str(output), str(source)]
            start = time.monotonic()
            with (run/(module+'.log')).open('w') as log:
                proc = subprocess.run(command, cwd=run, env=environment,
                                      stdout=log, stderr=subprocess.STDOUT)
            text = (run/(module+'.log')).read_text()
            audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
            for theorem, axioms in audits:
                assert set(x.strip() for x in axioms.split(',') if x.strip()) <= AXIOMS, theorem
            accepted = proc.returncode == 0 and output.exists() and 'sorryAx' not in text
            row = {'module': module, 'command': command, 'exit_code': proc.returncode,
                   'elapsed_seconds': time.monotonic()-start, 'accepted': accepted,
                   'source_sha256': digest(source), 'olean_sha256': digest(output) if output.exists() else None,
                   'log_sha256': digest(run/(module+'.log')), 'axiom_audits': audits}
            result['records'].append(row)
            save()
            print(json.dumps({'module': module, 'accepted': accepted, 'seconds': row['elapsed_seconds']}), flush=True)
            assert accepted, 'Compilation failed: '+module
        audited = {name for row in result['records'] for name, _ in row['axiom_audits']}
        assert {'ArborCounterexample.E_counts_all_dilations',
                'ArborCounterexample.ehrhart_unique',
                'ArborCounterexample.complete_counterexample',
                'ArborCounterexample.E_ne_zero',
                'ArborCounterexample.not_all_arbor_ehrhart_roots_real'} <= audited
        for name, sha in expected_sources.items():
            assert digest(ROOT/name) == sha, 'Source/configuration changed during check: '+name
        result['status'] = 'PASS'
    except Exception as exc:
        result['status'] = 'FAILED'
        result['error'] = repr(exc)
    result['finished_at_utc'] = dt.datetime.now(dt.timezone.utc).isoformat()
    save()
    print(json.dumps({'status': result['status'], 'run': str(run), 'error': result.get('error')}), flush=True)
    return 0 if result['status'] == 'PASS' else 1


if __name__ == '__main__':
    sys.exit(main())
