"""Coverage table and mechanical tick bounds for the GuestInv spec (track guestinv-opus55).

Usage:  python3 -I coverage.py Guest/SoftwareAst.lean OUTDIR

Reads the generated Pancake AST, computes the call graph from `main`, classifies every `while`
loop of every reachable function, and derives a tick bound per function:

  cost(seq a b)            = cost a + cost b
  cost(ite c a b)          = max(cost a, cost b)
  cost(dec x s e p)        = cost p
  cost(call g / handler h) = K(g) + 1 + cost h
  cost(decCall x s g a p)  = K(g) + 1 + cost p
  cost(while c b)          = (N + 1) * (cost b + 1)        -- N = iteration bound of the loop
  cost(anything else)      = 0                             -- only calls and loop iterations tick

Loop classes (N):
  CTR    a local counter i compared with a loop-invariant bound, updated only by i := i +/- c:
         N = 2^64 (or the constant bound c when the bound is a literal <= 2^16).
  GCTR   the same with a global counter (only `state_restore`: journal_n decremented).
  RO(k)  read-only body (no store, no global write, only pure callees): no-repeat on the k
         loop-carried locals, N = 2^(64k)  (refined keys in OVERRIDES).
  MAN    measure supplied by hand in OVERRIDES (class, N, justification).
Writes OUTDIR/coverage.md (tables) and OUTDIR/kgen.lean (Lean `def`s with literal values and the
symbolic formula as a comment).
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import panast  # noqa: E402

TWO64 = 2 ** 64

# Hand-supplied loop measures: (function, loop index) -> (class, N, justification).
# Filled in after inspecting every loop the heuristics leave as MAN.
OVERRIDES = {}

# Functions whose bound is not GuestInv-only (guard and potential in DESIGN.md section 6).
EVM_POTENTIAL = {('run_frames', 0)}


def is_app(t, head=None):
    return isinstance(t, tuple) and t[0] == 'app' and (head is None or t[1] == head)


def strval(t):
    return t[1] if isinstance(t, tuple) and t[0] == 'str' else None


def call_parts(t):
    """For Prog.call / Prog.decCall return (callee, handler_prog_or_None, continuation_or_None)."""
    if is_app(t, 'Prog.call'):
        a = t[2]
        opt = a[0]
        callee = strval(a[1])
        handler = None
        if is_app(opt, 'some'):
            tup = opt[2][0]
            if isinstance(tup, tuple) and tup[0] == 'tup' and len(tup[1]) == 2:
                h = tup[1][1]
                if is_app(h, 'some'):
                    inner = h[2][0]
                    if isinstance(inner, tuple) and inner[0] == 'tup' and len(inner[1]) == 3:
                        handler = inner[1][2]
        return callee, handler, None
    if is_app(t, 'Prog.decCall'):
        a = t[2]
        return strval(a[2]), None, a[4]
    return None


def callees(t, out):
    def f(x, _ctx):
        cp = call_parts(x)
        if cp and cp[0]:
            out.add(cp[0])
    panast.walk(t, f)
    return out


def var_name(e):
    if is_app(e, 'Exp.var'):
        return (panast.show(e[2][0]), e[2][1][1])
    return None


def assigns(t):
    """Set of (kind, name) assigned by Prog.assign anywhere in t, plus call destinations."""
    out = set()

    def f(x, _ctx):
        if is_app(x, 'Prog.assign'):
            out.add((panast.show(x[2][0]), x[2][1][1]))
        if is_app(x, 'Prog.call'):
            opt = x[2][0]
            if is_app(opt, 'some'):
                tup = opt[2][0]
                d = tup[1][0]
                if is_app(d, 'some'):
                    dd = d[2][0]
                    out.add((panast.show(dd[1][0]), dd[1][1][1]))
        if is_app(x, 'Prog.primitive'):
            out.add(('local', strval(x[2][0])))
    panast.walk(t, f)
    return out


def assign_exprs(t, kind, name):
    res = []

    def f(x, _ctx):
        if is_app(x, 'Prog.assign') and panast.show(x[2][0]) == kind and x[2][1][1] == name:
            res.append(x[2][2])
    panast.walk(t, f)
    return res


def has_store(t):
    found = [False]

    def f(x, _ctx):
        if is_app(x) and x[1] in ('Prog.store', 'Prog.storeByte', 'Prog.shMemStore', 'Prog.extCall'):
            found[0] = True
    panast.walk(t, f)
    return found[0]


def global_writes(t):
    return {n for (k, n) in assigns(t) if k == 'global'}


def free_vars(e):
    out = set()

    def f(x, _ctx):
        v = var_name(x)
        if v:
            out.add(v)
    panast.walk(e, f)
    return out


def has_load(e):
    found = [False]

    def f(x, _ctx):
        if is_app(x) and x[1] in ('Exp.load', 'Exp.loadByte', 'Exp.shMemLoad'):
            found[0] = True
    panast.walk(e, f)
    return found[0]


def step_of(expr, kind, name):
    """i := i + c  -> +c ; i := i - c -> -c ; else None."""
    if is_app(expr, 'Exp.op'):
        op = panast.show(expr[2][0])
        args = expr[2][1][1]
        if len(args) == 2 and var_name(args[0]) == (kind, name) and is_app(args[1], 'Exp.const'):
            c = args[1][2][0]
            c = c[2][1][1] if is_app(c, 'BitVec.ofNat') else None
            if c is None:
                return None
            if op == 'add':
                return c
            if op == 'sub':
                return -c
    return None


def top_level_items(t):
    """Statements executed unconditionally on every path that reaches the end of `t`:
    flatten the top-level seq chain and descend into dec / decCall continuations."""
    out = []
    stack = [t]
    while stack:
        x = stack.pop()
        if is_app(x, 'Prog.seq'):
            stack.append(x[2][1])
            stack.append(x[2][0])
        elif is_app(x, 'Prog.dec'):
            stack.append(x[2][3])
        elif is_app(x, 'Prog.decCall'):
            stack.append(x[2][4])
        else:
            out.append(x)
    return out


def unconditional_update(body, kind, name):
    for x in top_level_items(body):
        if is_app(x, 'Prog.assign') and panast.show(x[2][0]) == kind and x[2][1][1] == name:
            return True
    return False


def loop_decls(body):
    """Locals declared inside the loop body (dec / decCall / primitive): not loop-carried."""
    out = set()

    def f(x, _ctx):
        if is_app(x, 'Prog.dec') or is_app(x, 'Prog.decCall'):
            out.add(('local', strval(x[2][0])))
    panast.walk(body, f)
    return out


def classify(fname, idx, cond, body, pure, callee_gwrites=frozenset()):
    if (fname, idx) in OVERRIDES:
        return OVERRIDES[(fname, idx)]
    if (fname, idx) in EVM_POTENTIAL:
        return ('POT', None, 'EVM frame potential (EvmInv), section 6')
    asg = assigns(body)
    inner = loop_decls(body)
    carried = {v for v in asg if v not in inner}
    # counter loops: a local (or global) i updated by exactly one unconditional i := i + 1 (resp.
    # i := i - 1) and an exit test "i < X" (resp. "i != 0" / "i > X") with X loop-invariant.  Then
    # X - i (resp. i) is a strictly decreasing natural number below 2^64 that never wraps, so the
    # loop runs at most 2^64 iterations whatever the body does to memory (errors included).
    if is_app(cond, 'Exp.cmp'):
        cmpop = panast.show(cond[2][0])
        lhs, rhs = cond[2][1], cond[2][2]
        cands = []
        if cmpop in ('lower', 'less'):
            cands = [(lhs, rhs, +1), (rhs, lhs, -1)]      # i < X (up) ; X < i (down)
        elif cmpop in ('higher', 'greater'):
            cands = [(rhs, lhs, +1), (lhs, rhs, -1)]      # X > i (up) ; i > X (down)
        elif cmpop == 'notEqual':
            cands = [(lhs, rhs, -1), (rhs, lhs, -1)]      # i != 0 (down)
        for side, other, want in cands:
            v = var_name(side)
            if v is None or v not in carried:
                continue
            if cmpop == 'notEqual' and not (is_app(other, 'Exp.const') and panast.show(other) == '0'):
                continue
            exprs = assign_exprs(body, v[0], v[1])
            steps = [step_of(e, v[0], v[1]) for e in exprs]
            if len(steps) != 1 or steps[0] != want:
                continue
            if not unconditional_update(body, v[0], v[1]):
                continue
            if v[0] == 'global' and v[1] in callee_gwrites:
                continue
            if free_vars(other) & carried:
                continue
            if has_load(other) and (has_store(body) or not pure):
                continue
            cls = 'GCTR' if v[0] == 'global' else 'CTR'
            n = TWO64
            if want > 0 and is_app(other, 'Exp.const'):
                c = int(panast.show(other))
                if c <= 65536:
                    n = c
            return (cls, n, '%s %s %s, step %+d' % (v[1], cmpop, panast.show(other), want))
    # read-only loops: no-repeat on the carried locals
    if not has_store(body) and not global_writes(body) and pure:
        k = len([v for v in carried if v[0] == 'local'])
        return ('RO(%d)' % k, TWO64 ** max(k, 1),
                'no-repeat, key = carried locals %s' % sorted(n for _, n in carried))
    return ('MAN', None, 'carried=%s store=%s cond=%s' % (
        sorted(n for _, n in carried), has_store(body), panast.show(cond)))


def analyse(path):
    fns, line_of = panast.parse_functions(path)
    graph = {f: callees(t, set()) for f, t in fns.items()}
    # reachable from main
    reach, stack = set(), ['main']
    while stack:
        f = stack.pop()
        if f in reach or f not in fns:
            continue
        reach.add(f)
        stack.extend(graph[f])
    # purity: no store, no global write, no extCall, transitively
    impure = {f for f, t in fns.items() if has_store(t) or global_writes(t)}
    changed = True
    while changed:
        changed = False
        for f in fns:
            if f not in impure and graph[f] & impure:
                impure.add(f)
                changed = True
    gw = {f: set(global_writes(t)) for f, t in fns.items()}
    changed = True
    while changed:
        changed = False
        for f in fns:
            for g in graph[f]:
                if g in gw and not gw[g] <= gw[f]:
                    gw[f] |= gw[g]
                    changed = True
    # SCCs (Tarjan, iterative enough for this graph size)
    index, low, onst, st, sccs = {}, {}, set(), [], []
    counter = [0]

    def strong(v):
        index[v] = low[v] = counter[0]
        counter[0] += 1
        st.append(v)
        onst.add(v)
        for w in sorted(graph[v]):
            if w not in fns:
                continue
            if w not in index:
                strong(w)
                low[v] = min(low[v], low[w])
            elif w in onst:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = st.pop()
                onst.discard(w)
                comp.append(w)
                if w == v:
                    break
            sccs.append(comp)
    for v in sorted(reach):
        if v not in index:
            strong(v)
    recursive = set()
    for c in sccs:
        if len(c) > 1 or c[0] in graph[c[0]]:
            recursive.update(c)
    # loops
    loops = {}
    for f in sorted(reach):
        lst = []

        def g(x, ctx, lst=lst, f=f):
            if is_app(x, 'Prog.while'):
                cond, body = x[2][0], x[2][1]
                depth = sum(1 for h in ctx if h == 'Prog.while')
                lst.append((cond, body, depth))
        panast.walk(fns[f], g)
        loops[f] = [(i, c, b, d, classify(
            f, i, c, b, not (callees(b, set()) & impure),
            frozenset().union(*[gw.get(g, set()) for g in callees(b, set())])))
            for i, (c, b, d) in enumerate(lst)]
    return fns, line_of, graph, reach, impure, recursive, loops


def costs(fns, graph, reach, recursive, loops):
    K, formula = {}, {}
    order = []
    seen = set()

    def visit(f):
        if f in seen or f not in fns:
            return
        seen.add(f)
        for g in sorted(graph[f]):
            if g not in recursive or f not in recursive:
                visit(g)
        order.append(f)
    for f in sorted(reach):
        visit(f)
    loop_iter = {f: iter(loops[f]) for f in reach}

    def cost(t, f):
        if not isinstance(t, tuple) or t[0] != 'app':
            return 0, '0'
        h, a = t[1], t[2]
        if h == 'Prog.seq':
            x, fx = cost(a[0], f)
            y, fy = cost(a[1], f)
            return x + y, '%s + %s' % (fx, fy)
        if h == 'Prog.ite':
            x, fx = cost(a[1], f)
            y, fy = cost(a[2], f)
            return max(x, y), 'max (%s) (%s)' % (fx, fy)
        if h == 'Prog.dec':
            return cost(a[3], f)
        if h in ('Prog.call', 'Prog.decCall'):
            g, handler, cont = call_parts(t)
            kg = K.get(g)
            if kg is None:
                kg, fg = 0, 'K_%s(?)' % g
            else:
                fg = 'K_%s' % g
            hx, hf = cost(handler, f) if handler is not None else (0, '0')
            cx, cf = cost(cont, f) if cont is not None else (0, '0')
            return kg + 1 + hx + cx, '(%s + 1 + %s + %s)' % (fg, hf, cf)
        if h == 'Prog.while':
            i, _c, _b, _d, cls = next(loop_iter[f])
            bx, bf = cost(a[1], f)
            n = cls[1]
            if n is None:
                return 0, 'UNBOUNDED[%s#%d]' % (f, i)
            return (n + 1) * (bx + 1), '(N%d + 1) * (%s + 1)' % (i, bf)
        return 0, '0'
    for f in order:
        if f not in reach:
            continue
        loop_iter[f] = iter(loops[f])
        K[f], formula[f] = cost(fns[f], f)
    return K, formula, order


def main():
    path, outdir = sys.argv[1], sys.argv[2]
    fns, line_of, graph, reach, impure, recursive, loops = analyse(path)
    K, formula, order = costs(fns, graph, reach, recursive, loops)
    os.makedirs(outdir, exist_ok=True)
    nloops = sum(len(v) for f, v in loops.items())
    with open(os.path.join(outdir, 'coverage.md'), 'w') as o:
        o.write('functions: %d, reachable from main: %d, loops in reachable: %d, recursive: %s\n\n'
                % (len(fns), len(reach), nloops, sorted(recursive)))
        o.write('| function | AST line | loops | class / N | log2 K |\n|---|---|---|---|---|\n')
        for f in order:
            ls = loops[f]
            desc = '; '.join('#%d d%d %s N=%s: %s' % (
                i, d, cls[0], ('2^%d' % (cls[1].bit_length() - 1)) if cls[1] and cls[1] >= 2 ** 16
                else cls[1], cls[2]) for (i, _c, _b, d, cls) in ls) or '-'
            o.write('| `%s` | %d | %d | %s | %s |\n' % (
                f, line_of[f], len(ls), desc.replace('|', '\\|'),
                K[f].bit_length() if K[f] else 0))
        unreach = sorted(set(fns) - reach)
        o.write('\nunreachable from main (%d): %s\n' % (len(unreach), ', '.join(unreach)))
    with open(os.path.join(outdir, 'kgen.lean'), 'w') as o:
        for f in order:
            o.write('/-- %s -/\ndef K_%s : Nat := %d\n\n' % (formula[f][:3000], f, K[f]))
    print('reach', len(reach), 'loops', nloops, 'main log2', K.get('main', 0).bit_length())
    man = [(f, i, cls[2]) for f in sorted(reach) for (i, _c, _b, _d, cls) in loops[f]
           if cls[0] == 'MAN']
    print('MAN', len(man))
    with open(os.path.join(outdir, 'manual.txt'), 'w') as o:
        for f, i, why in man:
            o.write('%s#%d line %d: %s\n' % (f, i, line_of[f], why))


if __name__ == '__main__':
    panast.run_big(main)
