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
Writes OUTDIR/coverage.md (tables) and OUTDIR/kgen.lean (one symbolic Lean `def K.«f»` per function), OUTDIR/leaves.lean and
OUTDIR/tiers.txt (guarded tier, buffers).
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import panast  # noqa: E402

TWO64 = 2 ** 64

# Hand-supplied loop measures: (function, loop index) -> (class, N, justification).
# Filled in after inspecting every loop the heuristics leave as MAN.
W = 31104957928          # domainBytes = heapEnd - sourceBase
OVERRIDES = {
    ('merkleize', 0): ('MONO', 64,
        'cur := cur >> 1 while 1 < cur (signed): cur halves, at most 64 iterations'),
    ('merkleize_progressive', 0): ('WALK', W + 64,
        'size := size << 2 is 0 after <= 32 iterations; while size != 0 off strictly grows; '
        'afterwards each iteration writes roots + 32k (k += 1): fresh address, <= W'),
    ('rlp_list_count', 0): ('MONO', 2 ** 128,
        'off < len (unsigned); total = hl + pl from rlp_item_header, which returns '
        '1 <= hl + pl <= len - off or raises (rlp_fail); the body writes scratch '
        '(_rlp_validate_items_body), so the measure is len - off < 2^64 on the locals, '
        'not no-repeat (round 2)'),
    ('sort_elems', 0): ('MONO', 65,
        'width doubles 1,2,..,2^63,0; width = 2^63 exits after one inner pass, width = 0 makes the '
        'inner loop time out (WhileTimesOut, while_rank_stationary); at most 65 iterations'),
    ('sort_elems', 1): ('MONO', 2 ** 64,
        'for 1 <= width < n (signed) mid/right are capped at n with unsigned compares and do not '
        'wrap, so left strictly increases to n (mu = n - left); width = 0 gives mid = right = '
        'left, the merge loops do not run, left := right: the loop head repeats exactly '
        '(SameHead, while_rank_stationary)'),
    ('sort_elems', 2): ('MONO', 2 ** 65,
        'each iteration increments exactly one of i < mid, j < right (signed, no overflow): '
        'measure (mid - i) + (right - j)'),
    ('taylor_exponential', 0): ('MONO', 2 ** 64 + 1,
        'i := i + 1 each iteration from 1; i < 2^64 for the first 2^64 - 1 iterations; when i '
        'wraps to 0, di = 0 and u256_div(p, 0) = 0 makes acc = 0, so the loop exits'),
    ('compute_jumpdests', 0): ('WALK', W,
        'pc strictly increases by adv in [1, 33] and every iteration loads code + pc: fresh '
        'address in the contiguous ordinaryDomain'),
    ('fq12_inv', 0): ('MONO', 14,
        'Euclid on degree <= 12 polynomials: deg r1 strictly decreases, or the inner loop #1 '
        'times out (zero leading inverse), so this iteration times out (WhileTimesOut, '
        'while_rank_stationary)'),
    ('fq12_inv', 1): ('MONO', 14,
        'mu = 2 (d0 + 1) + [not yet stationary]: d0 = deg r0 in [-1, 12] strictly decreases when '
        'fq_poly_submul cancels the leading coefficient (needs: fq arithmetic cancels on '
        'non-canonical inputs, DESIGN 8); with linv = fq_inv(lead) = 0, cf = 0 and the writes '
        'to q and r0 are idempotent from the second iteration on, which repeats exactly '
        '(SameHead, while_rank_stationary)'),
    ('_rlp_validate_items_body', 0): ('STACK', (2 ** 61 + 1) * 2 ** 192,
        'each push calls scratch_alloc(24), which strictly lowers scratch_ptr and cannot wrap '
        '(<= 2^61 pushes, arbitrary globals); between pushes the body is read-only, no-repeat '
        'key (pos, end, top)'),
    ('_node_rlp_fill', 0): ('ALLOC', 2 ** 62,
        'every iteration either pushes (scratch_alloc(48): scratch_ptr strictly lower) or runs '
        '_node_rlp_finish, which allocates its encoding (alloc(n >= 1): heap_ptr strictly '
        'higher); callees release only to marks they took themselves; <= 2^64/48 + 2^64/8'),
    ('_decode_witness_node_body', 0): ('GUARD', 2 ** 68,
        'GUARDED (ArenaReady): pushes are scratch_alloc records (<= arena/88), every written '
        'object (records, branch nodes, node_new_* results) is a fresh allocation, so the slot '
        'counter top+32 < 16 is only written by this loop: <= (pushes + 1) * 64 iterations'),
    ('_mpt_insert_node', 0): ('GUARD', 2 ** 130,
        'GUARDED (MptReady): level strictly increases except on empty extension segments '
        '(pl = sl = 0); on such a segment node := +48 child; on the self-loop (child = node) '
        'node_invalidate and store(slot, node) are idempotent from the second iteration on, '
        'which repeats exactly (SameHead, while_rank_stationary with mu = 2 * rank + '
        '[not yet stationary]); <= (klen + 1) * 2^65'),
    ('_mpt_delete_node_body', 0): ('GUARD', 2 ** 130,
        'GUARDED (MptReady): descent as in _mpt_insert_node, pushing fresh scratch frames'),
    ('_mpt_delete_node_body', 1): ('GUARD', 2 ** 64,
        'GUARDED (MptReady): unwinds the scratch frames pushed by loop #0; frame links are '
        'fresh scratch objects disjoint from typed nodes, so each pop strictly shortens the chain'),
    ('memcpy', 0): ('WALK', W + 1,
        'fresh-address walk: the counter strictly increases by a positive constant and every '
        'iteration accesses base + counter (or base + 32*counter) in the contiguous domain'),
    ('memcpy', 1): ('WALK', W + 1,
        'fresh-address walk: the counter strictly increases by a positive constant and every '
        'iteration accesses base + counter (or base + 32*counter) in the contiguous domain'),
    ('memcpy', 2): ('WALK', W + 1,
        'fresh-address walk: the counter strictly increases by a positive constant and every '
        'iteration accesses base + counter (or base + 32*counter) in the contiguous domain'),
    ('memzero', 0): ('WALK', W + 1,
        'fresh-address walk: the counter strictly increases by a positive constant and every '
        'iteration accesses base + counter (or base + 32*counter) in the contiguous domain'),
    ('memzero', 1): ('WALK', W + 1,
        'fresh-address walk: the counter strictly increases by a positive constant and every '
        'iteration accesses base + counter (or base + 32*counter) in the contiguous domain'),
    ('memzero', 2): ('WALK', W + 1,
        'fresh-address walk: the counter strictly increases by a positive constant and every '
        'iteration accesses base + counter (or base + 32*counter) in the contiguous domain'),
    ('keccak256', 0): ('WALK', W + 1,
        'fresh-address walk: the counter strictly increases by a positive constant and every '
        'iteration accesses base + counter (or base + 32*counter) in the contiguous domain'),
    ('sha256', 0): ('WALK', W + 1,
        'fresh-address walk: the counter strictly increases by a positive constant and every '
        'iteration accesses base + counter (or base + 32*counter) in the contiguous domain'),
    ('ripemd160', 0): ('WALK', W + 1,
        'fresh-address walk: the counter strictly increases by a positive constant and every '
        'iteration accesses base + counter (or base + 32*counter) in the contiguous domain'),
    ('key_to_nibbles', 0): ('WALK', W + 1,
        'fresh-address walk: the counter strictly increases by a positive constant and every '
        'iteration accesses base + counter (or base + 32*counter) in the contiguous domain'),
    ('fq_poly_submul', 0): ('WALK', W + 1,
        'fresh-address walk: the counter strictly increases by a positive constant and every '
        'iteration accesses base + counter (or base + 32*counter) in the contiguous domain'),
    ('input_blob', 0): ('WALK', W + 1,
        'fresh-address walk: the counter strictly increases by a positive constant and every '
        'iteration accesses base + counter (or base + 32*counter) in the contiguous domain'),
    ('nibble_list_to_compact', 0): ('WALK', W + 1,
        'fresh-address walk: the counter strictly increases by a positive constant and every '
        'iteration accesses base + counter (or base + 32*counter) in the contiguous domain'),
    ('htab_truncate', 0): ('WF', 2 ** 64,
        'GUARDED (HtabArgWF), while_rank_stationary with mu = count t+24 < 2^64: each iteration '
        'calls htab_del on the key of the last leaf; it either deletes a leaf (count drops by '
        'one: htab_del_progress_spec; HtabArgWF kept: htab_del_spec) or returns 0 having written '
        'nothing (find_leaf may reach another leaf and memeq reject it: HtabWF does not '
        'constrain key bytes), and then the loop head repeats exactly (SameHead)'),
    # round 2: RO(k) counted locals, not words; these loops carry 4-, 5- or 6-word locals.
    # Their real measures are tiny; N is kept (it is an upper bound) so K is unchanged.
    ('modinv_bin', 0): ('MONO', 2 ** 256,
        'binary gcd: mu = bitlen(odd part of u) + bitlen(odd part of v) <= 512 drops by >= 1 '
        'per iteration (u, v odd after the halving loops, so u - v (resp. v - u) is even and '
        'its odd part is < u (resp. v)); u - v = 0 makes the next halving loop time out '
        '(WhileTimesOut, while_rank_stationary)'),
    ('modinv_bin', 1): ('MONO', 2 ** 128,
        'u != 0: mu = trailing zeros of u <= 255 drops by one; u = 0: u stays 0 and the body '
        '(shifts, mod_half = straight-line u256 arithmetic, always returns) cannot leave the '
        'loop, so the loop times out (WhileTimesOut, while_rank_stationary)'),
    ('modinv_bin', 2): ('MONO', 2 ** 128,
        'as #1 with v, x2'),
    ('bls_fp_inv_raw', 0): ('MONO', 2 ** 256,
        'as modinv_bin #0 on 384-bit values: mu <= 768'),
    ('bls_fp_inv_raw', 1): ('MONO', 2 ** 128,
        'as modinv_bin #1 on 384-bit values: trailing zeros <= 383, or u = 0 and the loop '
        'times out (bls_fp_shr1, bls_fp_half_can are straight-line arithmetic)'),
    ('bls_fp_inv_raw', 2): ('MONO', 2 ** 128,
        'as #1 with v, x2'),
    ('fq12_mul', 1): ('CTR', 2 ** 128,
        'iend >= i (unsigned notLower), i := i + 1 unconditional, iend <= 11 loop-invariant '
        '(capped before the loop): mu = iend + 1 - i <= 12'),
    ('fq12_sqr', 1): ('CTR', 2 ** 128,
        'i < k - i (unsigned), i := i + 1 unconditional, k <= 22 loop-invariant: '
        'mu = k - 2 i <= 22'),
    ('p256_fp_mul', 0): ('MONO', 2 ** 128,
        'c < 0 (signed), r := r + P, c := c + carry: P > 2^255, so of two consecutive '
        'iterations at least one carries; mu = 2 (-c) + [r < 2^256 - P] <= 2^65'),
    ('p256_fp_mul', 1): ('MONO', 2 ** 128,
        '0 < c (signed), c := c - [r < P], r := r - P: r >= P is followed by r - P < P; '
        'mu = 2 c + [r >= P] <= 2^64'),
    ('p256_fp_sqr', 0): ('MONO', 2 ** 128, 'as p256_fp_mul #0'),
    ('p256_fp_sqr', 1): ('MONO', 2 ** 128, 'as p256_fp_mul #1'),
}

# Functions whose bound is not GuestInv-only (guard and potential in DESIGN.md section 6).
EVM_POTENTIAL = {('run_frames', 0)}
MAX_CHAIN = 16384                       # frames: implied by disjoint 1408-byte scratch objects
POT_BS = MAX_CHAIN * TWO64              # bound of S = sum of state gas words
POT_BF = 2 * MAX_CHAIN + 2              # bound of F = 2 * depth + running bit
N_POT = (2 * MAX_CHAIN * TWO64 + 1) * POT_BF * POT_BS   # evmPot < N_POT


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


def classify(fname, idx, cond, body, pure, callee_gwrites=frozenset(), words=None):
    if (fname, idx) in OVERRIDES:
        return OVERRIDES[(fname, idx)]
    if (fname, idx) in EVM_POTENTIAL:
        return ('POT', N_POT, 'EVM frame potential evmPot < N_POT under EvmInv (section 6)')
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
            small_const = (is_app(other, 'Exp.const') and want > 0
                           and int(panast.show(other)) <= 2 ** 62)
            # step c >= 1 is also sound against a literal bound X <= 2^62: i < X implies
            # i + c < 2^63, so X - i still strictly decreases without wrapping
            if len(steps) != 1 or steps[0] is None or not (
                    steps[0] == want or (small_const and steps[0] > 0)):
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
            if want > 0 and is_app(other, 'Exp.const') and cmpop == 'lower':
                c = int(panast.show(other))
                if c <= 65536:
                    n = c          # unsigned i >= 0: at most X iterations
            return (cls, n, ('%s < %s' if want > 0 else '%s > %s (or != 0)') % ((v[1], panast.show(other)) if want > 0 else (v[1], panast.show(other))) + ', step %+d, unconditional' % steps[0])
    # read-only loops: no-repeat on the carried locals
    if not has_store(body) and not global_writes(body) and pure:
        # the no-repeat key is every WORD of every carried local (a 4-word struct local
        # contributes 2^256 values, round-2 non-blocking item)
        k = sum((words or {}).get(n, 1) for (kind, n) in carried if kind == 'local')
        return ('RO(%d)' % k, TWO64 ** max(k, 1),
                'no-repeat, key = carried locals %s (%d word%s)' % (
                    sorted(n for _, n in carried), k, '' if k == 1 else 's'))
    return ('MAN', None, 'carried=%s store=%s cond=%s' % (
        sorted(n for _, n in carried), has_store(body), panast.show(cond)))


def shape_words(t):
    """Number of 64-bit words of a Pancake shape (`Shape.one` = 1, `Shape.comb l` = sum)."""
    if is_app(t, 'Shape.comb'):
        lst = t[2][0]
        return sum(shape_words(x) for x in lst[1])
    return 1


def local_words(path, fns):
    """Per function: words of every parameter and every dec/decCall-declared local."""
    import re
    lines = open(path).read().split('\n')
    out = {}
    for i, ln in enumerate(lines):
        m = re.match(r'\s*\{ name := "([^"]+)"', ln)
        if m and i + 4 < len(lines) and lines[i + 3].strip().startswith('params := '):
            ws = {}
            for pm in re.finditer(r'\("([^"]+)", (\(Shape\.comb \[[^]]*\]\)|Shape\.one)\)',
                                  lines[i + 3]):
                ws[pm.group(1)] = pm.group(2).count('Shape.one')
            out[m.group(1)] = ws
    for f, t in fns.items():
        ws = out.setdefault(f, {})

        def g(x, _ctx, ws=ws):
            if is_app(x, 'Prog.dec') or is_app(x, 'Prog.decCall'):
                ws[strval(x[2][0])] = max(ws.get(strval(x[2][0]), 1), shape_words(x[2][1]))
        panast.walk(t, g)
    return out


def analyse(path, outdir):
    import time
    t0 = time.time()
    import pickle
    os.makedirs(outdir, exist_ok=True)
    cache = os.path.join(outdir, 'parsed.pickle')
    if os.path.exists(cache) and os.path.getmtime(cache) > os.path.getmtime(path):
        with open(cache, 'rb') as fh:
            fns, line_of = pickle.load(fh)
    else:
        fns, line_of = panast.parse_functions(path)
        with open(cache, 'wb') as fh:
            pickle.dump((fns, line_of), fh)
    print('parsed', time.time() - t0, flush=True)
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
    # trap_with stores to the shared trap area and then always raises TrapErr: it never
    # continues a loop iteration, so it does not break the read-only (no-repeat) argument.
    impure = {f for f, t in fns.items()
              if (has_store(t) or global_writes(t)) and f != 'trap_with'}
    changed = True
    while changed:
        changed = False
        for f in fns:
            if f not in impure and graph[f] & impure:
                impure.add(f)
                changed = True
    gw = {}

    def gwf(f):
        if f not in gw:
            r = set(global_writes(fns[f]))
            for g in graph[f]:
                if g in fns:
                    r |= gwf(g)
            gw[f] = r
        return gw[f]
    for f in fns:
        gwf(f)
    print('gw done', time.time() - t0, flush=True)
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
    print('scc done', time.time() - t0, flush=True)
    # loops
    words = local_words(path, fns)
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
            frozenset().union(*[gw.get(g, set()) for g in callees(b, set())]), words.get(f)))
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

    def nlit(n):
        """Loop bound as a readable Lean term."""
        for e in range(8, 1100):
            if n == 2 ** e:
                return '2 ^ %d' % e
        if n == W + 1:
            return '(domainBytes + 1)'
        if n == W + 64:
            return '(domainBytes + 64)'
        if n == N_POT:
            return 'evmPotMax'
        if n == 2 ** 64 + 1:
            return '(2 ^ 64 + 1)'
        if n == (2 ** 61 + 1) * 2 ** 192:
            return '((2 ^ 61 + 1) * 2 ^ 192)'
        return str(n)

    def add(x, y):
        if x == '0':
            return y
        if y == '0':
            return x
        return '%s + %s' % (x, y)

    def cost(t, f):
        if not isinstance(t, tuple) or t[0] != 'app':
            return 0, '0'
        h, a = t[1], t[2]
        if h == 'Prog.seq':
            x, fx = cost(a[0], f)
            y, fy = cost(a[1], f)
            return x + y, add(fx, fy)
        if h == 'Prog.ite':
            x, fx = cost(a[1], f)
            y, fy = cost(a[2], f)
            if fx == '0' and fy == '0':
                return 0, '0'
            if fx == fy:
                return x, fx
            return max(x, y), 'Nat.max (%s) (%s)' % (fx, fy)
        if h == 'Prog.dec':
            return cost(a[3], f)
        if h in ('Prog.call', 'Prog.decCall'):
            g, handler, cont = call_parts(t)
            kg = K[g]
            hx, hf = cost(handler, f) if handler is not None else (0, '0')
            cx, cf = cost(cont, f) if cont is not None else (0, '0')
            return kg + 1 + hx + cx, add(add('(«%s» + 1)' % g, hf), cf)
        if h == 'Prog.while':
            i, _c, _b, _d, cls = next(loop_iter[f])
            bx, bf = cost(a[1], f)
            n = cls[1]
            return (n + 1) * (bx + 1), '(%s + 1) * (%s + 1)' % (nlit(n), '0' if bf == '0' else bf)
        return 0, '0'
    for f in order:
        if f not in reach:
            continue
        loop_iter[f] = iter(loops[f])
        K[f], formula[f] = cost(fns[f], f)
    return K, formula, order


# ---------------------------------------------------------------------------------------------
# Guarded compositions (revision 4, round-3 item 5 and the assembly ruling)

GUARD_W = {'WorldOK': 'WorldOK', 'MainEntry': 'WorldOK', 'TxReady': 'WorldOK',
           'ReqsFresh': 'WorldOK', 'EvmInv': 'EvmInv', 'FinishReady': 'EvmInv',
           'ArenaReady': 'ArenaReady', 'MptReady': 'ArenaReady', 'MptObjReady': 'ArenaReady',
           'HtabArgWF': 'ArenaReady', 'RollbackReady': 'ArenaReady'}
W_PREFIX = {'WorldOK': 'wk', 'EvmInv': 'ek', 'ArenaReady': 'ak'}
# callees with a hand-written contract leaf (§7): those leaves are the hypotheses
SPEC_OF = {
    'htab_set': ['htab_set_spec'], 'htab_del': ['htab_del_spec', 'htab_del_progress_spec'],
    'htab_truncate': ['htab_truncate_spec'], 'htab_union_into': ['htab_union_into_spec'],
    'htab_new': ['htab_new_spec'], 'htab_new_scratch': ['htab_new_scratch_spec'],
    '_mpt_insert_node': ['mpt_insert_node_spec'],
    '_mpt_delete_node_body': ['mpt_delete_node_body_spec'], 'mem_init': ['mem_init_world'],
    'op_dispatch': ['op_dispatch_spec'], 'frame_exception': ['frame_exception_spec'],
    'frame_epilogue': ['frame_epilogue_spec'], 'finish_child': ['finish_child_spec']}
# write regions of the pointer-parameter writers (hand-checked on the AST, DESIGN.md §6)
REGION = {
    'memcpy': [('dst', 'locN s "n"')], 'memzero': [('dst', 'locN s "n"')],
    'st_le64': [('p', '8')], 'u256_to_be32': [('out', '32')], 'u256_to_be_min': [('out', '32')],
    'keccak256': [('out', '32')], 'header_hash': [('out', '32')],
    'rlp_encode_word': [('dst', '33')], 'rlp_encode_bytes': [('dst', 'locN s "n" + 9')],
    'encode_account': [('out', '110')], 'logs_bloom': [('out', '256')],
    'compute_contract_address': [('out', '20')], 'recover_sender_with_chain_id': [('out20', '20')],
    'extract_deposit_data': [('out', '192')], 'htr_new_payload_request': [('out', '32')],
    'node_invalidate': [('nd', '32')], '_delete_ext_finish': [('node', '176')],
    '_insert_into_leaf': [('node', '176')],
    'lst_push': None,   # header and current backing array, below
}
REGION_RAW = {'lst_push': '(locN s "l", 24), (memW s (locN s "l"), locN s "esz" * memW s (locN s "l" + 16))'}
# KeepsOn preconditions other than the caller's world guard
KEEP_PRE = {
    'requests_append': 'ReqRoom',
    'mpt_root': 'fun s => WorldAvoids (fun s => [(locN s "out", 32)]) s ∧ MptObjReady s',
    'compute_state_root': 'WorldAvoids (fun s => [(locN s "out", 32)])',
    'build_mpt_indexed': 'WorldAvoids (fun s => [(locN s "out", 32)])',
    'mpt_set': 'fun s => WorldOK s ∧ MptObjReady s',
}


def needed_calls(fns, f, guarded, root_loop):
    """Callees of f with a call site after which a guarded call or a guarded loop head is
    reachable inside f (return/raise end the path; a tail call flows only into its callee)."""
    def has_event(t):
        found = [False]

        def g(x, _c):
            if is_app(x, 'Prog.while') and root_loop:
                found[0] = True
            cp = call_parts(x)
            if cp and cp[0] in guarded:
                found[0] = True
        panast.walk(t, g)
        return found[0]
    out = []

    def walk(t, after):
        if not (isinstance(t, tuple) and t[0] == 'app'):
            return after
        h, a = t[1], t[2]
        if h == 'Prog.seq':
            return walk(a[0], walk(a[1], after))
        if h == 'Prog.ite':
            x = walk(a[1], after)
            y = walk(a[2], after)
            return x or y
        if h == 'Prog.while':
            r = has_event(a[1]) or root_loop or after
            walk(a[1], r)
            return r
        if h == 'Prog.dec':
            return walk(a[3], after)
        if h in ('Prog.return', 'Prog.raise'):
            return False
        cp = call_parts(t)
        if cp:
            g, handler, cont = cp
            if is_app(t, 'Prog.call') and is_app(a[0], 'none'):
                return g in guarded
            k = walk(cont, after) if cont is not None else after
            hh = walk(handler, after) if handler is not None else False
            out.append((g, k or hh))
            return (g in guarded) or k or hh
        return after
    walk(fns[f], False)
    return sorted({g for g, n in out if n})


def written_params(path, fns, line_of, graph):
    """Parameters each function writes through (directly, or by passing them to a written
    parameter of a callee)."""
    src = open(path).read().split('\n')
    par = {}
    for f, ln in line_of.items():
        for j in range(ln, ln + 8):
            if src[j].strip().startswith('params :='):
                par[f] = re.findall(r'\("([A-Za-z0-9_]+)", ', src[j])
                break

    def fv(e):
        return {n for (k, n) in free_vars(e) if k == 'local'}

    def stores(t):
        res = []

        def g(x, _c):
            if is_app(x) and x[1] in ('Prog.store', 'Prog.storeByte'):
                res.append(x[2][0])
        panast.walk(t, g)
        return res

    def calls(t):
        res = []

        def g(x, _c):
            if is_app(x, 'Prog.call') or is_app(x, 'Prog.decCall'):
                args = x[2][2] if is_app(x, 'Prog.call') else x[2][3]
                res.append((call_parts(x)[0], args[1] if isinstance(args, tuple) and args[0] == 'list' else []))
        panast.walk(t, g)
        return res
    wp = {f: {p for p in par.get(f, []) if any(p in fv(a) for a in stores(fns[f]))} for f in fns}
    changed = True
    while changed:
        changed = False
        for f in fns:
            for g, args in calls(fns[f]):
                if not wp.get(g):
                    continue
                for i, pn in enumerate(par.get(g, [])):
                    if pn in wp[g] and i < len(args):
                        new = (fv(args[i]) & set(par.get(f, []))) - wp[f]
                        if new:
                            wp[f] |= new
                            changed = True
    return wp, stores, calls, par


def compose(path, outdir, fns, line_of, graph, reach, impure, guarded, guard_of, order, loops, bufs):
    roots = {'run_frames', 'htab_truncate', '_decode_witness_node_body', '_mpt_insert_node',
             '_mpt_delete_node_body'}
    wp, stores, calls_of, par = written_params(path, fns, line_of, graph)
    gw = {}

    def gwf(f):
        if f not in gw:
            gw[f] = set()
            r = set(global_writes(fns[f]))
            for g in graph[f]:
                if g in fns:
                    r |= gwf(g)
            gw[f] = r
        return gw[f]
    bufsize = {g: sorted(v)[0][1] for g, v in bufs.items()}

    def closure(g):
        seen, st = set(), [g]
        while st:
            x = st.pop()
            if x in seen or x not in fns or (x in SPEC_OF and x != g):
                continue
            seen.add(x)
            st.extend(graph[x])
        return seen

    def buffers_written(g):
        res = set()
        for x in closure(g):
            decs = {}

            def d(y, _c):
                if is_app(y, 'Prog.dec'):
                    decs[strval(y[2][0])] = y[2][2]
            panast.walk(fns[x], d)
            targets = list(stores(fns[x]))
            for cg, args in calls_of(fns[x]):
                for i, pn in enumerate(par.get(cg, [])):
                    if pn in wp.get(cg, ()) and i < len(args):
                        targets.append(args[i])
            for a in targets:
                exprs = [a] + [decs[n] for (k, n) in free_vars(a) if k == 'local' and n in decs]
                for e in exprs:
                    for (k, n) in free_vars(e):
                        if k == 'global' and n in bufsize:
                            res.add(n)
        return sorted(res)
    G = lambda f: guard_of.get(f, 'WorldOK')
    need = {f: needed_calls(fns, f, guarded, f in roots) for f in guarded}
    contracts = {}   # name -> (statement, comment)
    hyps = {}        # f -> list of (type, primitive-or-local name)
    for f in order:
        if f not in guarded:
            continue
        W = GUARD_W[G(f)]
        hs = []
        for g in sorted(graph[f]):
            if g not in reach:
                continue
            if g in guarded:
                hs.append(('TerminatingFunBoundedOn %s (ofString "%s") K.«%s»' % (G(g), g, g), 'gb_' + g))
            else:
                hs.append(('TerminatingFunBoundedOn GuestInv (ofString "%s") K.«%s»' % (g, g), 'fb_' + g))
        for g in need[f]:
            if g in SPEC_OF:
                for sp in SPEC_OF[g]:
                    hs.append(('type_of% @' + sp, sp))
                continue
            if g not in impure:
                name = 'ro_' + g
                contracts[name] = ('ReadOnlyFn (ofString "%s")' % g, 'read-only')
            elif g in REGION and not (g in guarded):
                name = 'ww_' + g
                parts = REGION_RAW[g] if REGION[g] is None else ', '.join(
                    '(locN s "%s", %s)' % (pn, ln) for pn, ln in REGION[g])
                bw = buffers_written(g)
                if bw:
                    parts += ', ' + ', '.join('(globN s "%s", %d)' % (b, bufsize[b]) for b in bw)
                gws = sorted(gwf(g))
                contracts[name] = ('WritesWithin (fun s => [%s])\n    [%s] (ofString "%s")' % (
                    parts, ', '.join('"%s"' % x for x in gws), g),
                    'writes its parameter extents' + (' and the buffers ' + ', '.join(bw) if bw else ''))
            else:
                name = '%s_%s' % (W_PREFIX[W], g)
                if g in KEEP_PRE and W == 'WorldOK':
                    pre = KEEP_PRE[g]
                elif g in guarded and GUARD_W[G(g)] == W and G(g) != W:
                    pre = G(g)
                elif g in guarded and G(g) != W:
                    pre = 'fun s => %s s ∧ %s s' % (W, G(g))
                else:
                    pre = W
                pre_s = pre if pre.isidentifier() else '(%s)' % pre
                contracts[name] = ('KeepsOn %s %s (ofString "%s")' % (pre_s, W, g),
                                   'keeps `%s`' % W)
            hs.append((contracts[name][0], name))
        hyps[f] = hs
    with open(os.path.join(outdir, 'gleaves.lean'), 'w') as o:
        o.write('/-! #### Callee contracts (generated; one leaf per callee and world guard) -/\n\n')
        for name in sorted(contracts):
            st, why = contracts[name]
            g = name.split('_', 1)[1]
            o.write('/-- `%s` (AST line %d): %s. -/\ntheorem «%s» :\n    %s := by sorry\n'
                    % (g, line_of[g], why, name, st))
        o.write('\n/-! #### Composition obligations of the guarded bodies (generated)\n\n'
                '`GBody.«f»`: from the bounds of `f`\'s direct callees and the contracts of the callees at\n'
                'its guard-carrying call sites, `f`\'s body is bounded under its guard. `gbody_f` is the\n'
                'primitive; `gb_f` is PROVED from it. -/\n\n')
        for f in order:
            if f not in guarded:
                continue
            g0 = G(f)
            ls = loops[f]
            note = '; '.join('#%d %s' % (i, cls[0]) for (i, _c, _b, _d, cls) in ls) or 'loop-free'
            o.write('/-- `%s` (AST line %d, guard `%s`): %s; %d callees, %d guard-carrying. -/\n'
                    'def GBody.«%s» : Prop :=\n' % (f, line_of[f], g0, note, len(graph[f] & reach),
                                                   len(need[f]), f))
            for t, _n in hyps[f]:
                o.write('  (%s) →\n' % t)
            o.write('  TerminatingFunBoundedOn %s (ofString "%s") K.«%s»\n\n' % (g0, f, f))
            o.write('theorem «gbody_%s» : GBody.«%s» := by sorry\n\n' % (f, f))
            o.write('theorem «gb_%s» : TerminatingFunBoundedOn %s (ofString "%s") K.«%s» :=\n  «gbody_%s»'
                    % (f, g0, f, f, f))
            for _t, n in hyps[f]:
                o.write(' «%s»' % n)
            o.write('\n\n')
        # the primitive obligations used by the guarded compositions, and the assembly
        prims = []
        seen = set()
        for f in order:
            if f not in guarded:
                continue
            for t, n in hyps[f]:
                if n.startswith('gb_') or n in seen:
                    continue
                seen.add(n)
                prims.append((n, t))
            prims.append(('gbody_' + f, 'GBody.«%s»' % f))
        o.write('/-! #### Assembly (PROVED): the primitive obligations imply `main`\'s guarded bound -/\n\n'
                '/-- Every primitive obligation the guarded compositions use: the `fb_*` bounds of the\n'
                'unguarded callees of guarded functions, the §7 contract leaves, the generated callee\n'
                'contracts and the `gbody_*` composition obligations. -/\n'
                'structure Primitives : Prop where\n')
        for n, t in prims:
            o.write('  «%s» : %s\n' % (n, t.replace('\n', ' ')))
        o.write('\ntheorem assembly_main (P : Primitives) :\n'
                '    TerminatingFunBoundedOn MainEntry (ofString "main") K.«main» := by\n')
        for f in order:
            if f not in guarded:
                continue
            o.write('  have «g_%s» := P.«gbody_%s»' % (f, f))
            for _t, n in hyps[f]:
                o.write(' «g_%s»' % n[3:] if n.startswith('gb_') else ' P.«%s»' % n)
            o.write('\n')
        o.write('  exact «g_main»\n\n')
        o.write('/-- The leaves discharge the primitives (each field is its `sorry` leaf). -/\n'
                'theorem primitives : Primitives where\n')
        for n, _t in prims:
            o.write('  «%s» := «%s»\n' % (n, n))
        o.write('\n')
    with open(os.path.join(outdir, 'contracts.txt'), 'w') as o:
        for f in sorted(guarded):
            o.write('%s [%s]: %s\n' % (f, G(f), ' '.join(need[f])))
    print('contracts', len(contracts), 'primitives', len(prims))


def main():
    path, outdir = sys.argv[1], sys.argv[2]
    fns, line_of, graph, reach, impure, recursive, loops = analyse(path, outdir)
    K, formula, order = costs(fns, graph, reach, recursive, loops)
    os.makedirs(outdir, exist_ok=True)
    # guarded tier: functions whose bound needs a memory contract, and all their callers
    roots = {'run_frames', 'htab_truncate', '_decode_witness_node_body', '_mpt_insert_node',
             '_mpt_delete_node_body'}
    guarded = set(roots)
    changed = True
    while changed:
        changed = False
        for f in reach:
            if f not in guarded and graph[f] & guarded:
                guarded.add(f)
                changed = True
    guard_of = {
        'htab_truncate': 'HtabArgWF', 'rollback_child_access': 'RollbackReady',
        'finish_child': 'FinishReady', 'run_frames': 'EvmInv',
        '_decode_witness_node_body': 'ArenaReady', '_mpt_insert_node': 'MptReady',
        '_mpt_delete_node_body': 'MptReady', '_mpt_delete_node': 'MptReady',
        'mpt_set': 'MptObjReady', 'main': 'MainEntry',
        'process_transaction': 'TxReady', 'process_general_purpose_requests': 'ReqsFresh'}
    nloops = sum(len(v) for f, v in loops.items())
    with open(os.path.join(outdir, 'coverage.md'), 'w') as o:
        o.write('functions: %d, reachable from main: %d, loops in reachable: %d, recursive: %s\n\n'
                % (len(fns), len(reach), nloops, sorted(recursive)))
        o.write('| function | AST line | leaf (guard) | loops: #index depth class N: justification | log2 K |\n'
                '|---|---|---|---|---|\n')
        for f in order:
            ls = loops[f]
            desc = '; '.join('#%d d%d %s N=%s: %s' % (
                i, d, cls[0], ('2^%d' % (cls[1].bit_length() - 1)) if cls[1] and cls[1] >= 2 ** 16
                else cls[1], cls[2]) for (i, _c, _b, d, cls) in ls) or '-'
            leaf = ('`gb_%s` (%s)' % (f, guard_of.get(f, 'WorldOK'))) if f in guarded \
                else '`fb_%s` (GuestInv)' % f
            o.write('| `%s` | %d | %s | %s | %s |\n' % (
                f, line_of[f], leaf, desc.replace('|', '\\|'),
                K[f].bit_length() if K[f] else 0))
        unreach = sorted(set(fns) - reach)
        o.write('\nunreachable from main (%d): %s\n' % (len(unreach), ', '.join(unreach)))
    with open(os.path.join(outdir, 'kgen.lean'), 'w') as o:
        for f in order:
            o.write('/-- `%s` (AST line %d), log2 ≈ %d. -/\ndef «%s» : Nat := %s\n\n' % (f, line_of[f], K[f].bit_length(), f, formula[f]))
    print('reach', len(reach), 'loops', nloops, 'main log2', K.get('main', 0).bit_length())
    # dominant chain: from main, repeatedly descend into the call with the largest
    # (loop multiplicity) * K(callee) contribution
    def best_call(f):
        best = (0, None, 1)
        it = iter(loops[f])

        def walk(t, mult):
            nonlocal best
            if not isinstance(t, tuple) or t[0] != 'app':
                return
            h, a = t[1], t[2]
            if h == 'Prog.while':
                i, _c, _b, _d, cls = next(it)
                walk(a[1], mult * (cls[1] + 1))
                return
            cp = call_parts(t)
            if cp and cp[0] in K:
                v = mult * (K[cp[0]] + 1)
                if v > best[0]:
                    best = (v, cp[0], mult)
            for x in a:
                if isinstance(x, tuple):
                    if x[0] == 'app':
                        walk(x, mult)
                    elif x[0] in ('tup', 'list'):
                        for y in x[1]:
                            walk(y, mult)
        walk(fns[f], 1)
        return best
    with open(os.path.join(outdir, 'chain.txt'), 'w') as o:
        f = 'main'
        while f:
            v, g, mult = best_call(f)
            o.write('%s  log2K=%d  -> %s  (loop multiplicity log2 %d)\n' % (
                f, K[f].bit_length(), g, mult.bit_length() - 1))
            f = g
    man = [(f, i, cls[2]) for f in sorted(reach) for (i, _c, _b, _d, cls) in loops[f]
           if cls[0] == 'MAN']
    print('MAN', len(man))
    between = sorted({g for f in guarded for g in graph[f] if g in reach and g not in guarded})
    # global buffers allocated with a literal size
    bufs = {}

    def scan(x, _ctx):
        if is_app(x, 'Prog.call'):
            opt, callee = x[2][0], strval(x[2][1])
            args = x[2][2][1]
            if callee in ('alloc', 'scratch_alloc') and is_app(opt, 'some'):
                d = opt[2][0][1][0]
                if is_app(d, 'some') and panast.show(d[2][0][1][0]) == 'global' and args \
                        and is_app(args[0], 'Exp.const'):
                    bufs.setdefault(d[2][0][1][1][1], set()).add((callee, int(panast.show(args[0]))))
    for f in sorted(reach):
        panast.walk(fns[f], scan)
    with open(os.path.join(outdir, 'tiers.txt'), 'w') as o:
        o.write('GUARDED %d: %s\n' % (len(guarded), ' '.join(sorted(guarded))))
        o.write('BETWEEN %d: %s\n' % (len(between), ' '.join(between)))
        for g, v in sorted(bufs.items()):
            o.write('BUF %s %s\n' % (g, sorted(v)))
    with open(os.path.join(outdir, 'leaves.lean'), 'w') as o:
        for f in order:
            if f in guarded:
                continue
            ls = loops[f]
            note = '; '.join('#%d %s' % (i, cls[0]) for (i, _c, _b, _d, cls) in ls) or 'loop-free'
            o.write('/-- `%s` (AST line %d): %s. -/\ntheorem «fb_%s» : TerminatingFunBoundedOn '
                    'GuestInv (ofString "%s") K.«%s» := by sorry\n' % (f, line_of[f], note, f, f, f))
    compose(path, outdir, fns, line_of, graph, reach, impure, guarded, guard_of, order, loops, bufs)
    print('guarded', len(guarded), 'between', len(between), 'bufs', len(bufs))
    with open(os.path.join(outdir, 'manual.txt'), 'w') as o:
        for f, i, why in man:
            o.write('%s#%d line %d: %s\n' % (f, i, line_of[f], why))


if __name__ == '__main__':
    panast.run_big(main)
