"""Check the R10 interface transition and census every sorry in the generated spec.

Run from the repository root: python3 -I .../audit_revision.py [baseline-revision]
This is a source audit; the Lean run and #print axioms remain separate checks.
"""
import hashlib
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

SPEC = 'campaign/specs-proposed/GuestInv.lean'
base = sys.argv[1] if len(sys.argv) > 1 else '16aa6f4b0'
old = subprocess.check_output(['git', 'show', f'{base}:{SPEC}'])
new = Path(SPEC).read_bytes()


def frozen(data):
    leaves = dict(re.findall(rb'^theorem \xc2\xab(fb_[^\n]+?)\xc2\xbb([^\n]+)', data, re.M))
    return leaves

old_leaves, new_leaves = frozen(old), frozen(new)
reclassified = {b'fb_' + x.encode() for x in ('_node_rlp_fill', 'node_rlp', 'node_hash', 'mpt_root')}
assert old_leaves.keys() - new_leaves.keys() == reclassified
assert not new_leaves.keys() - old_leaves.keys()
for name in new_leaves:
    assert old_leaves[name] == new_leaves[name], name
print(f'UNCHANGED {len(new_leaves)} retained fb declarations; {len(reclassified)} moved to NodeHeap guards')
pattern = rb'^def GuestInv :.*?(?=\n\n)'
assert re.search(pattern, old, re.M | re.S)[0] == re.search(pattern, new, re.M | re.S)[0]
assert b'theorem K_target_budget :' in new and b'118223496 * K_pan + 119233963' in new
print('UNCHANGED GuestInv; R10 target-budget theorem present')

# Erase nested Lean block comments and line comments, keeping newlines for declaration starts.
text = new.decode()
out, pos, depth = [], 0, 0
while pos < len(text):
    if text.startswith('/-', pos):
        depth += 1
        pos += 2
    elif depth and text.startswith('-/', pos):
        depth -= 1
        pos += 2
    elif not depth and text.startswith('--', pos):
        end = text.find('\n', pos)
        pos = len(text) if end < 0 else end
    else:
        out.append(text[pos] if not depth or text[pos] == '\n' else ' ')
        pos += 1
assert depth == 0
clean = ''.join(out)
assert not re.search(r'\b(?:axiom|native_decide)\b', clean), 'forbidden declaration/tactic'
blocks = re.split(r'\n(?=(?:theorem|def|abbrev|structure|instance|example) )', clean)
census = Counter()
for block in blocks:
    count = len(re.findall(r'\bsorry\b', block))
    if not count:
        continue
    decl = re.match(r'theorem (\S+)', block)
    assert decl, 'sorry outside a theorem body'
    name = decl[1].strip('«»')
    category = name.split('_', 1)[0]
    if category not in {'fb', 'gbody', 'wk', 'ak', 'ek', 'mk', 'ro', 'ww', 'fk', 'nf', 'nk',
                        'rt', 'rv', 'zv', 'nz', 'dm', 'sp', 'iz'}:
        assert name in {
            'htab_set_spec', 'htab_del_spec', 'htab_del_progress_spec', 'htab_truncate_spec',
            'htab_union_into_spec', 'htab_new_spec', 'htab_new_scratch_spec',
            'mpt_insert_node_spec', 'mpt_delete_node_body_spec', 'mem_init_world',
            'op_dispatch_spec', 'frame_exception_spec', 'frame_epilogue_spec', 'finish_child_spec'
        }, f'sorry outside an allowed leaf: {name}'
        category = 'handwritten contracts'
    assert ':=' in block and 'sorry' not in block.split(':=', 1)[0]
    census[category] += count
print('SORRY CENSUS:', ', '.join(f'{k}={v}' for k, v in sorted(census.items())))
print('TOTAL:', sum(census.values()), '(all in leaf theorem bodies)')
