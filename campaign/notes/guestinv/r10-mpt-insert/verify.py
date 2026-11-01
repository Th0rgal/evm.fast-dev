#!/usr/bin/env python3
"""Replay the R10 insertion proof using stock Lean and a preseeded import cone.

Run from any directory with the pinned Lean toolchain on PATH. Every module in
Wave8GuestInv's target import closure and every newly supplied generic helper is
rebuilt; other imports must already have compiled artifacts from the pinned cone.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess

import tempfile

ROOT = Path(__file__).resolve().parents[4]
PREFIX = 'InitECandidate.Solver.Wave8GuestInv.'
TARGET = PREFIX + 'ContractParts.C10'
SYMBOL = PREFIX + 'gbody__mpt_insert_node'
BASE = '664524baaf0aff6938ff399c2017a85b8ccc0c59'
GENERIC = {'InitECandidate.Solver.PanTerminatingNoRepeat'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log-dir', type=Path, required=True)
    args = parser.parse_args()
    args.log_dir = args.log_dir.resolve()
    args.log_dir.mkdir(parents=True, exist_ok=True)
    lib = ROOT / '.lake/build/lib/lean'
    source = ROOT / 'submission'
    seen, ordered = set(), []

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        if not module.startswith(PREFIX) and module not in GENERIC:
            return
        path = source / Path(module.replace('.', '/') + '.lean')
        for line in path.read_text().splitlines():
            if line.startswith('import '):
                for dep in line[7:].split('--')[0].split():
                    visit(dep)
        ordered.append((module, path))

    visit(TARGET)
    c10 = source / Path(PREFIX.replace('.', '/')) / 'ContractParts/C10.lean'
    baseline = subprocess.check_output(['git', 'show', BASE + ':' + str(c10.relative_to(ROOT))],
                                       cwd=ROOT, text=True)
    signature = r'def GBody\.«_mpt_insert_node» : Prop :=.*?\n\n'
    assert re.search(signature, baseline, re.S).group() == re.search(
        signature, c10.read_text(), re.S).group(), 'GBody signature changed'
    receipts = []
    for module, path in ordered:
        new = '.R10Shards.' in module or module in GENERIC
        if new:
            assert not re.search(r'\b(sorry|sorryAx|native_decide|axiom)\b', path.read_text()), path
        output = lib / Path(module.replace('.', '/') + '.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        log = args.log_dir / (module + '.log')
        command = ['lake', 'env', 'lean', '-j4', '-M', '12288', '-R', 'submission',
                   '-o', str(output), str(path.relative_to(ROOT))]
        print('BUILD', module, flush=True)
        with log.open('w') as stream:
            result = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
        text = log.read_text()
        if result.returncode or (new and ('sorryAx' in text or 'declaration uses `sorry`' in text)):
            print(text, end='', flush=True)
            raise SystemExit(result.returncode or 1)
        receipts.append({'module': module, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                         'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest(),
                         'command': command, 'exit': result.returncode})
    with tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False) as probe:
        probe.write(f'import {TARGET}\n#print axioms {SYMBOL}\n')
        probe_path = Path(probe.name)
    try:
        audit_log = args.log_dir / 'audit.log'
        audit_cmd = ['lake', 'env', 'lean', '-j4', '-M', '12288', str(probe_path)]
        with audit_log.open('w') as stream:
            audit_res = subprocess.run(audit_cmd, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
        audit = audit_log.read_text()
        if audit_res.returncode:
            print(audit, end='', flush=True)
            raise SystemExit(audit_res.returncode)
    finally:
        probe_path.unlink(missing_ok=True)
    match = re.search(re.escape("'" + SYMBOL + "' depends on axioms:") + r'\s*\[([^\]]*)\]', audit)
    assert match, audit
    axioms = sorted(x.strip() for x in match.group(1).split(','))
    assert axioms == sorted(['propext', 'Classical.choice', 'Quot.sound']), axioms
    receipt = {'base': BASE, 'symbol': SYMBOL, 'axioms': axioms,
               'signature_unchanged': True, 'checks': receipts,
               'lean_version': subprocess.check_output(['lake', 'env', 'lean', '--version'],
                                                       cwd=ROOT, text=True).strip()}
    (args.log_dir / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(audit, end='', flush=True)
    print('PASS:', len(receipts), 'modules; unchanged signature; exactly the standard axioms')


if __name__ == '__main__':
    main()
