import re, sys
def sigs(path):
    txt = open(path).read()
    txt = re.sub(r'/-.*?-/', '', txt, flags=re.S)
    txt = re.sub(r'--[^\n]*', '', txt)
    out = {}
    blocks = re.split(r'\n(?=(?:theorem|def|abbrev|structure|example|noncomputable def|instance) )', txt)
    for b in blocks:
        m = re.match(r'(theorem|def|abbrev|structure|example|instance)\s+(\S+)', b)
        if not m: continue
        kind, name = m.group(1), m.group(2)
        if kind == 'example': continue
        if kind == 'theorem':
            sig = b.split(':=', 1)[0] if ':= by' in b or ':=' in b else b
            # theorem statements end at ':=' at top level; good enough
        else:
            sig = b  # definitions: whole body is the meaning
        out[name] = ' '.join(sig.split())
    return out
a, b = sigs(sys.argv[1]), sigs(sys.argv[2])
chg = sorted(n for n in a if n in b and a[n] != b[n])
new = sorted(n for n in b if n not in a)
gone = sorted(n for n in a if n not in b)
fb = [n for n in chg if n.startswith('«fb_')]
print('changed', len(chg), 'fb changed', len(fb)); print('CHANGED', ' '.join(chg))
print('REMOVED', ' '.join(gone))
print('NEW', len(new), ' '.join(n for n in new if not re.match(r'«(gbody_|wk_|ek_|ak_|ro_|ww_)', n) and not n.startswith('GBody.')))
print('NEW generated', len([n for n in new if re.match(r'«(gbody_|wk_|ek_|ak_|ro_|ww_)', n) or n.startswith('GBody.')]))
