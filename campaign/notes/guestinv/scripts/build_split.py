#!/usr/bin/env python3
"""Compile the generated R10 modules sequentially with stock Lean.

Run after split_spec.py, with the pinned toolchain on PATH and the dependency
cone extracted into .lake. Logs and the machine-readable result stay in the
chosen cache directory. Successful, unchanged outputs can be reused.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
PREFIX = 'InitECandidate.Solver.Wave8GuestInv.'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log-dir', type=Path, required=True)
    parser.add_argument('--max-memory', type=int, default=24576)
    args = parser.parse_args()
    args.log_dir.mkdir(parents=True, exist_ok=True)
    source_dir = ROOT / 'submission/InitECandidate/Solver/Wave8GuestInv'
    output_dir = ROOT / '.lake/build/lib/lean'
    files = {PREFIX + '.'.join(p.relative_to(source_dir).with_suffix('').parts): p
             for p in source_dir.rglob('*.lean')}
    assert files, 'run r10_inputs/split_spec.py first'
    dependencies = {m: [line[7:] for line in p.read_text().splitlines()
                        if line.startswith('import ') and line[7:] in files]
                    for m, p in files.items()}
    seen, active, ordered = set(), set(), []

    def visit(module):
        if module in seen:
            return
        assert module not in active, f'cyclic import: {module}'
        active.add(module)
        for dependency in dependencies[module]:
            visit(dependency)
        active.remove(module)
        seen.add(module)
        ordered.append(module)

    for module in sorted(files):
        visit(module)
    environment = os.environ.copy()
    if not environment.get('LEAN_PATH'):
        paths = sorted((ROOT / '.lake/packages').glob('*/.lake/build/lib/lean'))
        environment['LEAN_PATH'] = os.pathsep.join(map(str, [*paths, output_dir]))
    results = []

    def artifact(module):
        return output_dir / Path(module.replace('.', '/') + '.olean')

    for module in ordered:
        source = files[module]
        output = artifact(module)
        output.parent.mkdir(parents=True, exist_ok=True)
        stamp = output.with_suffix('.r10-sha256')
        digest = hashlib.sha256(source.read_bytes()).hexdigest()
        fresh = (stamp.exists() and stamp.read_text() == digest and output.exists()
                 and all(artifact(dep).stat().st_mtime_ns < output.stat().st_mtime_ns
                         for dep in dependencies[module]))
        if fresh:
            print('CACHED', module, flush=True)
            results.append({'module': module, 'source_sha256': digest,
                            'status': 'cached', 'exit': 0})
            continue
        log = args.log_dir / (module[len(PREFIX):].replace('.', '_') + '.log')
        command = ['lean', f'-M{args.max_memory}', '-R', 'submission', '-o',
                   str(output), str(source.relative_to(ROOT))]
        print('BUILD', module, flush=True)
        start = time.monotonic()
        with log.open('w') as stream:
            result = subprocess.run(command, cwd=ROOT, env=environment,
                                    stdout=stream, stderr=subprocess.STDOUT)
        elapsed = round(time.monotonic() - start, 2)
        results.append({'module': module, 'source_sha256': digest, 'status': 'built',
                        'exit': result.returncode, 'seconds': elapsed, 'command': command})
        print('EXIT', result.returncode, module, f'{elapsed}s', flush=True)
        (args.log_dir / 'split-results.json').write_text(json.dumps(results, indent=2) + '\n')
        if result.returncode:
            print(log.read_text()[-26000:], flush=True)
            raise SystemExit(result.returncode)
        stamp.write_text(digest)
    (args.log_dir / 'split-results.json').write_text(json.dumps(results, indent=2) + '\n')
    print('ALL SPLIT MODULES PASSED:', len(ordered), flush=True)


if __name__ == '__main__':
    main()
