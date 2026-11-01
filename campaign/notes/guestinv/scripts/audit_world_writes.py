#!/usr/bin/env python3
"""Audit every generated wk contract against the pinned AST's full call closure.

Local aliases include declarations and assignments; written formal parameters are
propagated through calls by written_params. Contract boundaries never stop the
scan. Typed ws/bs/ts/bo records use world ownership and RecordsKept, not output R.
"""
import argparse
import json
import re
import sys
from pathlib import Path
import coverage as c

ROOT = Path(__file__).resolve().parents[4]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--cache', type=Path, required=True)
    ap.add_argument('--report', type=Path, required=True)
    args = ap.parse_args()
    path = str(ROOT/'Guest/SoftwareAst.lean')
    fns, lines, graph, reach, _, _, _ = c.analyse(path, str(args.cache))
    wp, stores, calls, params = c.written_params(path, fns, lines, graph)
    parts = (ROOT/'campaign/notes/guestinv/scripts/parts/p4.lean').read_text()
    buffers = dict((k, int(n)) for k, n in re.findall(r'\("([^"]+)", ([0-9]+)\)',
        parts.split('def globalBuffers :')[1].split('def blockOutObjects')[0]))
    # sk_make is the only writer and copies 20 + 32 bytes; the tail is padding.
    buffers['sk_buf'] = 52
    records = {'ws', 'bs', 'ts', 'bo'}
    direct = {}
    for fn in sorted(reach):
        aliases = {}
        def alias(t, _):
            if c.is_app(t, 'Prog.dec'):
                aliases.setdefault(c.strval(t[2][0]), []).append(t[2][2])
            elif c.is_app(t, 'Prog.assign') and c.panast.show(t[2][0]) == 'local':
                aliases.setdefault(t[2][1][1], []).append(t[2][2])
        c.panast.walk(fns[fn], alias)
        targets = list(stores(fns[fn]))
        for callee, actuals in calls(fns[fn]):
            for i, formal in enumerate(params.get(callee, [])):
                if formal in wp.get(callee, ()) and i < len(actuals):
                    targets.append(actuals[i])
        found, seen = set(), set()
        while targets:
            for kind, name in c.free_vars(targets.pop()):
                if kind == 'global' and name in buffers and name not in records:
                    found.add(name)
                elif kind == 'local' and name not in seen:
                    seen.add(name)
                    targets.extend(aliases.get(name, []))
        direct[fn] = found
    spec = (ROOT/'campaign/specs-proposed/GuestInv.lean').read_text()
    report = []
    for name, statement in re.findall(r'theorem «(wk_[^»]+)» :\n(.*?) := by sorry', spec, re.S):
        fn = name[3:]
        closure, pending = set(), [fn]
        while pending:
            x = pending.pop()
            if x not in closure and x in fns:
                closure.add(x)
                pending.extend(graph[x])
        globals_ = set().union(*(c.global_writes(fns[x]) for x in closure))
        bw = set().union(*(direct[x] for x in closure))
        gline = re.search(r'^    (\[(?:"[^"]+"(?:, )?)*\])$', statement, re.M)
        assert gline, ('cannot parse G', name)
        declared_g = set(json.loads(gline[1]))
        declared_r = {b: int(n) for b, n in re.findall(r'\(globN s "([^"]+)", ([0-9]+)\)', statement)}
        for b, same, n in re.findall(r'\(globN s "([^"]+)", if globN s "([^"]+)" = 0 then 0 else ([0-9]+)\)', statement):
            assert b == same, (name, 'mismatched buffer normalization', b, same)
            declared_r[b] = int(n)
        assert not globals_ - declared_g, (name, 'missing globals', sorted(globals_ - declared_g))
        missing = [b for b in bw if declared_r.get(b, 0) < buffers[b]]
        assert not missing, (name, 'missing global-buffer R intervals', missing)
        report.append({'contract': name, 'transitive_functions': len(closure),
                       'writes_globals': sorted(globals_), 'G': sorted(declared_g),
                       'writes_buffers': sorted(bw), 'R_global_buffers': declared_r})
    assert len(report) >= 84, len(report)
    get_code = next(x for x in report if x['contract'] == 'wk_get_code')
    assert get_code['R_global_buffers'].get('sk_buf', 0) >= 52
    assert '"ws+16"' in parts
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps({'contracts': report, 'count': len(report),
        'missing_globals': 0, 'missing_buffers': 0}, indent=2, sort_keys=True)+'\n')
    print(f'AUDITED {len(report)} wk contracts: no missing globals or global-buffer R intervals')


if __name__ == '__main__':
    c.panast.run_big(main)
