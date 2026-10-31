"""Minimal parser for the generated Pancake AST in Guest/SoftwareAst.lean.

Parses every `Decl.function { name := ... body := ... }` into a nested term tree:
  ('app', head, [args])   e.g. ('app', 'Prog.seq', [t1, t2])
  ('tup', [items]) / ('list', [items]) / ('str', s) / ('num', n) / ('id', name)
Used by coverage.py; standard library only.
"""
import re

TOK = re.compile(r'\s*(?:(?P<str>"(?:[^"\\]|\\.)*")|(?P<num>\d+)|(?P<id>[A-Za-z_][A-Za-z0-9_.!?\']*)|(?P<p>:=|[()\[\],{}]))')


def tokenize(s):
    pos, out = 0, []
    while pos < len(s):
        m = TOK.match(s, pos)
        if not m:
            if s[pos:].strip() == '':
                break
            raise ValueError('bad token at %r' % s[pos:pos + 40])
        pos = m.end()
        if m.group('str') is not None:
            out.append(('str', m.group('str')[1:-1]))
        elif m.group('num') is not None:
            out.append(('num', int(m.group('num'))))
        elif m.group('id') is not None:
            out.append(('id', m.group('id')))
        else:
            out.append(('p', m.group('p')))
    return out


class Parser:
    def __init__(self, toks):
        self.t, self.i = toks, 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else ('eof', None)

    def next(self):
        tok = self.peek()
        self.i += 1
        return tok

    def atom(self):
        kind, v = self.next()
        if kind == 'p' and v == '(':
            items = [self.app()]
            while self.peek() == ('p', ','):
                self.next()
                items.append(self.app())
            assert self.next() == ('p', ')')
            return items[0] if len(items) == 1 else ('tup', items)
        if kind == 'p' and v == '[':
            items = []
            if self.peek() != ('p', ']'):
                items.append(self.app())
                while self.peek() == ('p', ','):
                    self.next()
                    items.append(self.app())
            assert self.next() == ('p', ']')
            return ('list', items)
        if kind in ('str', 'num', 'id'):
            return (kind, v)
        raise ValueError('unexpected %r' % ((kind, v),))

    def app(self):
        head = self.atom()
        args = []
        while True:
            kind, v = self.peek()
            if kind == 'eof' or (kind == 'p' and v in (')', ']', ',', '}')):
                break
            args.append(self.atom())
        if not args:
            return head
        h = head[1] if head[0] == 'id' else head
        return ('app', h, args)


def parse_functions(path):
    """Split the generated file line by line (each function is a fixed-format record)."""
    lines = open(path).read().split('\n')
    fns, line_of = {}, {}
    i = 0
    while i < len(lines):
        if lines[i].startswith('def guestFn_') and lines[i + 1].strip() == 'Decl.function':
            m = re.match(r'\s*\{ name := "([^"]+)"', lines[i + 2])
            name = m.group(1)
            j = i + 3
            while lines[j] != '      body :=':
                j += 1
            k = j + 1
            while not lines[k].startswith('      returnShape := '):
                k += 1
            body = '\n'.join(lines[j + 1:k])
            p = Parser(tokenize(body))
            term = p.app()
            assert p.peek()[0] == 'eof', name
            fns[name] = term
            line_of[name] = i + 1
            i = k
        i += 1
    return fns, line_of


def walk(t, f, ctx=()):
    """Pre-order walk calling f(term, ctx); ctx is the tuple of enclosing app heads."""
    f(t, ctx)
    if isinstance(t, tuple):
        if t[0] == 'app':
            for a in t[2]:
                walk(a, f, ctx + (t[1],))
        elif t[0] in ('tup', 'list'):
            for a in t[1]:
                walk(a, f, ctx)


def show(t):
    """Compact rendering of an expression term."""
    if not isinstance(t, tuple):
        return str(t)
    k = t[0]
    if k == 'num':
        return str(t[1])
    if k == 'str':
        return '"%s"' % t[1]
    if k == 'id':
        return t[1].split('.')[-1]
    if k == 'tup':
        return '(' + ', '.join(show(x) for x in t[1]) + ')'
    if k == 'list':
        return '[' + ', '.join(show(x) for x in t[1]) + ']'
    h, a = t[1], t[2]
    if h == 'Exp.var':
        return ('L:' if show(a[0]) == 'local' else 'G:') + a[1][1]
    if h == 'Exp.const':
        return show(a[0])
    if h == 'BitVec.ofNat':
        return show(a[1])
    if h == 'Exp.op':
        return show(a[0]) + show(a[1])
    if h == 'Exp.cmp':
        return '%s(%s, %s)' % (show(a[0]), show(a[1]), show(a[2]))
    if h == 'Exp.load':
        return 'ld(%s)' % show(a[1])
    if h == 'Exp.loadByte':
        return 'ldb(%s)' % show(a[0])
    return show(h if isinstance(h, tuple) else ('id', h)) + ' ' + ' '.join(show(x) for x in a)


def run_big(fn):
    """Run fn() in a thread with a large stack (the AST nests `seq` thousands deep)."""
    import sys
    import threading
    sys.setrecursionlimit(1000000)
    threading.stack_size(1 << 29)
    out = {}

    def target():
        out['v'] = fn()
    th = threading.Thread(target=target)
    th.start()
    th.join()
    return out.get('v')
