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
    # revision 8 (coordinator note, Gemini round 5): explicit rank, N and K unchanged
    ('fq12_inv', 1): ('MONO', 14,
        'while_rank_stationary with mu = (if linv = 0 then 0 else d0 - d1) + phase at the active '
        'inner head (d0 = deg r0, d1 = deg r1 >= 1 inside the outer loop, so d0 - d1 <= 11); '
        'phase = 2 if r0[d0] < p or r0[d0] mod p != 0, 1 if r0[d0] >= p, r0[d0] mod p = 0 and '
        'q[d0 - d1] != 0, 0 otherwise. fq_mul always returns < p and fq_mul(k p, linv) = 0 for '
        '1 <= k <= 5, so every continuing iteration strictly lowers mu or is an exact repeat '
        '(SameHead: noncanonical lead r + p, period-1 state, ISSUES.md on wave8/leaves-arith-astra), '
        'and an inner SameHead makes the outer iteration WhileTimesOut; mu <= 11 + 2 = 13 <= 14'),
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


def const_value(e):
    """Value of a literal or a `*`/`+` of literals (e.g. `alloc(256 * 8)`), else None (round-3
    Gemini non-blocking: `bls_discount`, `bn_gamma`, `bn_expw`, `precompile_addrs`,
    `zero_hashes` are allocated with constant products)."""
    if is_app(e, 'Exp.const'):
        return int(panast.show(e))
    if is_app(e, 'Exp.panOp') or is_app(e, 'Exp.op'):
        op = panast.show(e[2][0])
        vals = [const_value(x) for x in e[2][1][1]]
        if any(v is None for v in vals):
            return None
        if op.endswith('mul'):
            r = 1
            for v in vals:
                r *= v
            return r
        if op.endswith('add'):
            return sum(vals)
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
           'ReqsFresh': 'WorldOK', 'MsgReady': 'WorldOK', 'BlockReady': 'WorldOK',
           'InputReady': 'WorldOK',
           'EvmInv': 'EvmInv', 'FinishReady': 'EvmInv', 'EvmRun': 'EvmInv',
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
    'rlp_encode_word': [('dst', '9')], 'rlp_encode_bytes': [('dst', 'locN s "n" + 9')],
    'encode_account': [('out', '110')], 'logs_bloom': [('out', '256')],
    'compute_contract_address': [('out', '20')], 'recover_sender_with_chain_id': [('out20', '20')],
    'extract_deposit_data': [('out', '192')], 'htr_new_payload_request': [('out', '32')],
    # revision 7: rlp_encode_word(dst, w) writes 1 + rlp_be_len(w) <= 9 bytes (AST 4795); the
    # revision-6 extent 33 overran the 16-byte `mpt_key_scratch` of `build_mpt_indexed`
    'node_invalidate': [('nd', '32')], '_delete_ext_finish': [('node', '176')],
    '_insert_into_leaf': [('node', '176')],
    'lst_push': None,   # header and current backing array, below
}
REGION_RAW = {'lst_push': '(locN s "l", 24), (memW s (locN s "l"), locN s "esz" * memW s (locN s "l" + 16))'}
# call sites whose guard-carrying frame is not the caller's guard: `process_message` builds the
# outermost frame with `frame_open(msg, 0)`, after which it runs under `EvmInv`; revision 5: the
# message record stays owned (`EvmMsgReady`) until `depth0_prepare`, which writes through it
CALL_STMT = {('process_message', 'frame_open'):
             ('fk_frame_open', 'KeepsOn FrameOpenReady EvmMsgReady (ofString "frame_open")')}
CALL_W = {('process_message', g): 'EvmInv' for g in ('depth0_prepare', 'state_snapshot', 'frame_start')}
# KeepsOn preconditions at one call site (revision 5)
CALL_PRE = {('process_message', 'depth0_prepare'): 'EvmMsgReady'}
# node-returning callees of the MPT tier (guards MptReady/MptObjReady) and their node parameters
NODE_FN = {'_insert_into_leaf': ['node'], '_split_extension': ['node'], '_collapse_branch': ['node'],
           '_delete_ext_finish': ['node', 'nc'], 'node_new_ext': ['child'], 'node_new_leaf': [],
           'node_invalidate': ['nd']}
# revision 6 (round-4 Astra items 5 and 6): each node function's own requirement `req s Nd`, read
# off its body (DESIGN.md §6 "NodeFn requirements"): the kinds of the nodes it reads/writes at fixed
# offsets, the nibble arrays it indexes a branch by or copies into a new node's path, and the
# bounds that keep those indices inside the arrays
NODE_REQ = {
    'node_new_leaf': 'KeyIn s Nd (locN s "nib") (locN s "nlen")',
    'node_new_ext': 'KeyIn s Nd (locN s "nib") (locN s "nlen")',
    'node_invalidate': 'True',
    '_insert_into_leaf': 'NodeKind s Nd "node" 1 ∧ KeyIn s Nd (locN s "rk") (locN s "rl")',
    '_split_extension': ('NodeKind s Nd "node" 2 ∧ KeyIn s Nd (locN s "rk") (locN s "rl") ∧\n'
                         '      locN s "pl" < memW s (locN s "node" + 40) ∧ locN s "pl" ≤ locN s "rl"'),
    '_collapse_branch': 'NodeKind s Nd "node" 3',
    '_delete_ext_finish': 'NodeKind s Nd "node" 2 ∧ KeyIn s Nd (locN s "seg") (locN s "sl")',
}
# revision 6: value contracts the MPT compositions need besides the uniform shapes (one extra
# leaf per callee, at the listed call sites)
EXTRA = {
    'common_prefix_length': ('rv_common_prefix_length',
                             'RetLe (fun s => min (locN s "al") (locN s "bl")) (ofString "common_prefix_length")',
                             'returns at most `min(al, bl)` (value contract)',
                             ('_mpt_insert_node', '_mpt_delete_node_body')),
    'mpt_nibble_key': ('nk_mpt_nibble_key', 'RetNibbles (ofString "mpt_nibble_key")',
                       'returns a fresh heap nibble array (value contract)', ('mpt_set',)),
    # revision 8 (round-5 Astra item 7, Gemini suggestion): the exact effect of node_invalidate
    # (the stationary argument of the self-looping empty extension), and the fresh scratch record
    # _decode_step pushes (the scratch-stack rank of _decode_witness_node_body)
    'node_invalidate': ('iz_node_invalidate', 'InvalidatesCache (ofString "node_invalidate")',
                        'zeroes the cache words `nd+8/+16/+24` and nothing else (exact effect)',
                        ('_mpt_insert_node', '_mpt_delete_node_body')),
    '_decode_step': ('sp__decode_step', 'PushesFrame (ofString "_decode_step")',
                     'a pushed record is a fresh 88-byte scratch block tagged 1 or 2 (value contract)',
                     ('_decode_witness_node_body',)),
    '_resolve_step': ('sp__resolve_step', 'ResolvesNode (ofString "_resolve_step")',
                     'a completed result is null or a fresh heap node, separated from live scratch',
                     ('_decode_witness_node_body',)),
}
# revision 8 (round-5 Astra item 7): `_decode_step` writes only memory free at entry (its stores go
# to `node_new_leaf`'s fresh node and its own `scratch_alloc` record, which `fresh_only` does not
# trace through the callee result); it gets the write frame instead of `KeepsOn ArenaReady ArenaReady`
FORCE_WW = {'_decode_step'}
# revision 8 (round-5 Fable item 3, Astra item 5): `execute_block` runs `memzero(bo, 88)` right
# after `bo := alloc(88)`, where `WorldOK` does not hold (the fresh record holds arbitrary words), so
# that site also gets the `ArenaReady`-tier write frame of `memzero` (revision 6's `ww_memzero`)
CALL_WW = {('execute_block', 'memzero')}
UNFOLD_LEMMAS0 = ('sourceFunctionEntry, Guest.Software.guestFn_{F}, '
                 'InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, '
                 'InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, '
                 'InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, '
                 'InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, '
                 'InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, '
                 'InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, '
                 'Option.map_none, Option.map_some, List.map_cons, List.map_nil')


UNFOLD_LEMMAS = UNFOLD_LEMMAS0

# guarded bodies proved by concrete composition (revision 4: shrinking the primitive list); the
# placeholders {LOOKUP} and {UNFOLD} are filled per function
WOK = 'LocalsOnly.of_localsFree localsFree_worldOK'
CALLWOK = 'callEntryOn_of_localsFree localsFree_worldOK _ _'
HANDLER_SHM = ('(TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) '
               '(fun s => clock_raise s _ _)))')
RET0 = '(TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))'


# revision 7: the attempt chain runs under `InputReady` (`si`-dependent); a call passing `L:"si"` to
# a callee whose only parameter is `si` keeps it (`callEntryOn_inputReady`, proved)
IWOK = 'localsOnly_inputReady'
ICALL = ('callEntryOn_inputReady «lookup_{C}»\n            (by simp only [%s,\n'
         '              InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural])' %
         UNFOLD_LEMMAS0.replace('{F}', '{C}'))


def attempt_proof(f, callee):
    return """  intro h1
  refine ⟨_, _, _, {LOOKUP}, ?_⟩
  simp only [{UNFOLD}]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (%s) _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 inputReady_guestInv _ _ _ %s _
          (%s))
        inputReady_guestInv %s)) ?_
  unfold K.«%s»; omega
""" % (IWOK, HANDLER_SHM, ICALL.replace('{C}', callee), RET0, f)


GBODY_PROOF = {'attempt_l%d' % k: attempt_proof('attempt_l%d' % k,
                                                'run_attempt' if k == 1 else 'attempt_l%d' % (k - 1))
               for k in range(1, 8)}
GBODY_PROOF['verify_stateless_new_payload'] = """  intro h1
  refine ⟨_, _, _, {LOOKUP}, ?_⟩
  simp only [{UNFOLD}]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (%s) _ (by decide) _ _
      (TerminatingProgBoundedOn.dec_onLocals (%s) _ (by decide) _ _
        (TerminatingProgBoundedOn.seq_guestInv_after
          (TerminatingProgBoundedOn.callHandle_on h1 inputReady_guestInv _ _ _
            (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_assign s _ _ _)
              (fun s => clock_assign s _ _ _))) _
            (%s))
          inputReady_guestInv %s))) ?_
  unfold K.«verify_stateless_new_payload»; omega
""" % (IWOK, IWOK, ICALL.replace('{C}', 'attempt_l7'), RET0)
# functions whose `lookup_` theorem is needed besides the proved ones (callees of proved bodies)
LOOKUP_EXTRA = {'run_attempt'}
GBODY_PROOF['incorporate_tx_into_block'] = """  intro hm hu
  refine ⟨_, _, _, {LOOKUP}, ?_⟩
  simp only [{UNFOLD}]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.seq_guestInv_after
      (TerminatingProgBoundedOn.call_on hu _ _ (%s)) worldOK_guestInv
      (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hm _ _) %s)) ?_
  unfold K.«incorporate_tx_into_block»; omega
""" % (CALLWOK, RET0)
ARENA = ('decode_witness_to_mpt', '_decode_witness_node', '_decode_witness_node_mpt', 'mpt_from_witness')
GBODY_PROOF['mpt_from_witness'] = """  intro hd hn
  refine ⟨_, _, _, {LOOKUP}, ?_⟩
  simp only [{UNFOLD}]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.decCall_on hd _ _ _ (%s)
      (decCallResumeOn_guestInv worldOK_guestInv _ _ _)
      (TerminatingProgBoundedOn.tailCall_guestInv hn _)) ?_
  unfold K.«mpt_from_witness»; omega
""" % CALLWOK
HANDLER_REL = ('(TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hsr _ _) '
               '(TerminatingProgBoundedOn.of_clock (fun s => clock_raise s _ _)))')
GBODY_PROOF['_decode_witness_node_mpt'] = """  intro hb hsr
  refine ⟨_, _, _, {LOOKUP}, ?_⟩
  simp only [{UNFOLD}]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (%s) _ (by simp) _ _
      (TerminatingProgBoundedOn.dec_onLocals (%s) _ (by simp) _ _
        (TerminatingProgBoundedOn.seq_guestInv_after
          (TerminatingProgBoundedOn.callHandle_on hb worldOK_guestInv _ _ _ %s _
            (callEntryOn_of_imp localsFree_arenaReady (fun s h => h.1) _ _))
          worldOK_guestInv %s))) ?_
  unfold K.«_decode_witness_node_mpt»; omega
""" % (WOK, WOK, HANDLER_REL, RET0)
GBODY_PROOF['_decode_witness_node'] = """  intro hmpt hmk hsr hro
  refine ⟨_, _, _, {LOOKUP}, ?_⟩
  simp only [{UNFOLD}]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.decCall_on hmk _ _ _
      (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _)
      (ReadOnlyFn.resumeOn (%s) worldOK_guestInv hro _ (by simp) _)
      (TerminatingProgBoundedOn.dec_onLocals (%s) _ (by simp) _ _
        (TerminatingProgBoundedOn.dec_onLocals (%s) _ (by simp) _ _
          (TerminatingProgBoundedOn.seq_guestInv_after
            (TerminatingProgBoundedOn.callHandle_on hmpt worldOK_guestInv _ _ _ %s _ (%s))
            worldOK_guestInv
            (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hsr _ _)
              %s))))) ?_
  unfold K.«_decode_witness_node»; omega
""" % (WOK, WOK, WOK, HANDLER_REL, CALLWOK, RET0)

# revision 6 (round-4 Astra item 8): guard clauses and `KeepsOn`/read-only calls carried by the
# proved Hoare rules (`seq_hoare`, `Hoare.ite_return_skip`, `Hoare.call_keeps`, `Hoare.ite_call_keeps`)
FBE = 'callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _'
ROR = '(ReadOnlyFn.resumeOn (%s) worldOK_guestInv {H} _ (by simp) _)' % WOK
ITE_RET = ('(TerminatingProgBoundedOn.ite_on (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))\n'
           '        (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))')
SKIP0 = '(TerminatingProgBoundedOn.of_clock (fun s => clock_skip s))'
GBODY_PROOF['get_pre_tx_storage'] = """  intro hrec hsl hws hk hro
  refine ⟨_, _, _, {LOOKUP}, ?_⟩
  simp only [{UNFOLD}]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.decCall_on hsl _ _ _ (%s) %s
      (TerminatingProgBoundedOn.seq_hoare %s (Hoare.ite_return_skip _ _)
        (TerminatingProgBoundedOn.seq_hoare (TerminatingProgBoundedOn.call_on hrec _ _ (%s))
          (Hoare.call_keeps localsFree_worldOK (WorldKeeps.keepsOn hk) _)
          (TerminatingProgBoundedOn.decCall_on hws _ _ _ (%s)
            (decCallResumeOn_guestInv worldOK_guestInv _ _ _) %s)))) ?_
  unfold K.«get_pre_tx_storage»; omega
""" % (FBE, ROR.replace('{H}', 'hro'), ITE_RET, FBE, CALLWOK, RET0)
GBODY_PROOF['get_storage_original'] = """  intro hhas hrec hsl hws hrh hk hrs
  refine ⟨_, _, _, {LOOKUP}, ?_⟩
  simp only [{UNFOLD}]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.decCall_on hhas _ _ _ (%s) %s
      (TerminatingProgBoundedOn.seq_hoare %s (Hoare.ite_return_skip _ _)
        (TerminatingProgBoundedOn.decCall_on hsl _ _ _ (%s) %s
          (TerminatingProgBoundedOn.seq_hoare %s (Hoare.ite_return_skip _ _)
            (TerminatingProgBoundedOn.seq_hoare (TerminatingProgBoundedOn.call_on hrec _ _ (%s))
              (Hoare.call_keeps localsFree_worldOK (WorldKeeps.keepsOn hk) _)
              (TerminatingProgBoundedOn.decCall_on hws _ _ _ (%s)
                (decCallResumeOn_guestInv worldOK_guestInv _ _ _) %s)))))) ?_
  unfold K.«get_storage_original»; omega
""" % (FBE, ROR.replace('{H}', 'hrh'), ITE_RET, FBE, ROR.replace('{H}', 'hrs'), ITE_RET, FBE, CALLWOK, RET0)
GBODY_PROOF['ws_storage_trie'] = """  intro hdw hget hset hro
  refine ⟨_, _, _, {LOOKUP}, ?_⟩
  simp only [{UNFOLD}]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (%s) _ (by simp) _ _
      (TerminatingProgBoundedOn.decCall_on hget _ _ _ (%s) %s
        (TerminatingProgBoundedOn.seq_hoare %s (Hoare.ite_return_skip _ _)
          (TerminatingProgBoundedOn.decCall_on hdw _ _ _ (%s)
            (decCallResumeOn_guestInv worldOK_guestInv _ _ _)
            (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hset _ _)
              %s))))) ?_
  unfold K.«ws_storage_trie»; omega
""" % (WOK, FBE, ROR.replace('{H}', 'hro'), ITE_RET,
       'callEntryOn_of_imp localsFree_arenaReady (fun s h => h.1) _ _', RET0)
GBODY_PROOF['decode_witness_to_mpt'] = """  intro hdw hal hmc hme hmf hnl hrme hrmf hrnl
  refine ⟨_, _, _, {LOOKUP}, ?_⟩
  simp only [{UNFOLD}]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.decCall_on hme _ _ _ (%s) %s
      (TerminatingProgBoundedOn.seq_hoare %s (Hoare.ite_return_skip _ _)
        (TerminatingProgBoundedOn.decCall_on hnl _ _ _ (%s) %s
          (TerminatingProgBoundedOn.seq_hoare
            (TerminatingProgBoundedOn.ite_on (TerminatingProgBoundedOn.call_on hmf _ _ (%s)) %s)
            (Hoare.ite_call_keeps localsFree_worldOK
              (ReadOnlyFn.keepsOn localsFree_worldOK worldOK_guestInv hrmf) _ _)
            (TerminatingProgBoundedOn.decCall_on hdw _ _ _ (%s)
              (decCallResumeOn_guestInv worldOK_guestInv _ _ _)
              (TerminatingProgBoundedOn.seq_guestInv
                (TerminatingProgBoundedOn.ite_on
                  (TerminatingProgBoundedOn.decCall_guestInv hal _ _ _
                    (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hmc _ _)
                      (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _)))) %s)
                %s)))))) ?_
  unfold K.«decode_witness_to_mpt»
  simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl]
  omega
""" % (FBE, ROR.replace('{H}', 'hrme'), ITE_RET, FBE, ROR.replace('{H}', 'hrnl'), FBE, SKIP0, CALLWOK, SKIP0, RET0)

# revision 7: a world-step callee carries `WorldOK` (`WorldKeeps.keepsOn`), also through a
# `decCall` (`KeepsOn.resumeOn`); guard clauses `if c then raise …` (`Hoare.ite_raise_skip`)
ITE_RAISE = ('(TerminatingProgBoundedOn.ite_on (TerminatingProgBoundedOn.of_clock (fun s => clock_raise s _ _))\n'
             '        (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))')
WRES = '(KeepsOn.resumeOn localsFree_worldOK (WorldKeeps.keepsOn %s) _ _)'
GBODY_PROOF['process_checked_system_transaction'] = """  intro hal hext hpu hsf wal wext wsf
  refine ⟨_, _, _, {LOOKUP}, ?_⟩
  simp only [{UNFOLD}]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.seq_hoare (TerminatingProgBoundedOn.call_on hsf _ _ (%s))
      (Hoare.call_keeps localsFree_worldOK (WorldKeeps.keepsOn wsf) _)
      (TerminatingProgBoundedOn.decCall_on hext _ _ _ (%s) %s
        (TerminatingProgBoundedOn.seq_hoare %s (Hoare.ite_raise_skip _ _ _)
          (TerminatingProgBoundedOn.decCall_on hal _ _ _ (%s) %s
            (TerminatingProgBoundedOn.decCall_on hpu _ _ _ (%s)
              (decCallResumeOn_guestInv worldOK_guestInv _ _ _)
              (TerminatingProgBoundedOn.seq_guestInv %s %s)))))) ?_
  unfold K.«process_checked_system_transaction»
  try simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl]
  omega
""" % (FBE, FBE, WRES % 'wext', ITE_RAISE, FBE, WRES % 'wal', CALLWOK,
       ITE_RAISE, RET0)

GI_ITE_RET = ('(TerminatingProgBoundedOn.ite_on (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))\n'
              '        (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))')
GBODY_PROOF['ws_get_storage'] = """  intro hal hhm hhr hkc hme hrd htl hub hsr hst hro wsr
  refine ⟨_, _, _, {LOOKUP}, ?_⟩
  simp only [{UNFOLD}]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.decCall_on hsr _ _ _ (%s) %s
      (TerminatingProgBoundedOn.decCall_on hme _ _ _ (%s) %s
        (TerminatingProgBoundedOn.seq_hoare %s (Hoare.ite_return_skip _ _)
          (TerminatingProgBoundedOn.decCall_on hst _ _ _ (%s)
            (decCallResumeOn_guestInv worldOK_guestInv _ _ _)
            (TerminatingProgBoundedOn.decCall_guestInv hhm _ _ _
              (TerminatingProgBoundedOn.decCall_guestInv hal _ _ _
                (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hkc _ _)
                  (TerminatingProgBoundedOn.decCall_guestInv htl _ _ _
                    (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hhr _ _)
                      (TerminatingProgBoundedOn.seq_guestInv %s
                        (TerminatingProgBoundedOn.decCall_guestInv hrd _ _ _
                          (TerminatingProgBoundedOn.seq_guestInv %s
                            (TerminatingProgBoundedOn.seq_guestInv %s
                              (TerminatingProgBoundedOn.decCall_guestInv hub _ _ _ %s)))))))))))))) ?_
  unfold K.«ws_get_storage»
  try simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl]
  omega
""" % (FBE, WRES % 'wsr', FBE, ROR.replace('{H}', 'hro'), ITE_RET, CALLWOK, GI_ITE_RET, GI_ITE_RET,
       ITE_RAISE, RET0)

# revision 8: `_mpt_delete_node` (scratch mark, the guarded body under a handler that releases and
# rethrows, release, return); the body's four parameters are the caller's same-named locals
# (`callEntryOn_mptReady`, proved)
MRG = '(fun s h => h.1.1)'
GBODY_PROOF['_mpt_delete_node'] = """  intro hb hmk hsr hro
  refine ⟨_, _, _, {LOOKUP}, ?_⟩
  simp only [{UNFOLD}]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.decCall_on hmk _ _ _
      (callEntryOn_of_imp localsFree_guestInv %(g)s _ _)
      (ReadOnlyFn.resumeOn localsOnly_mptReady %(g)s hro _ (by decide) _)
      (TerminatingProgBoundedOn.dec_onLocals localsOnly_mptReady _ (by decide) _ _
        (TerminatingProgBoundedOn.dec_onLocals localsOnly_mptReady _ (by decide) _ _
          (TerminatingProgBoundedOn.seq_guestInv_after
            (TerminatingProgBoundedOn.callHandle_on hb %(g)s _ _ _ %(h)s _
              (callEntryOn_mptReady «lookup__mpt_delete_node_body»
                (by simp only [%(u)s,
                  InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural])))
            %(g)s
            (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hsr _ _)
              %(r)s))))) ?_
  unfold K.«_mpt_delete_node»; omega
""" % {'g': MRG, 'h': HANDLER_REL, 'r': RET0,
       'u': UNFOLD_LEMMAS0.replace('{F}', '_mpt_delete_node_body')}
LOOKUP_EXTRA.add('_mpt_delete_node_body')

# revision 7: the witness decoders are guarded by `ArenaReady` (`state_init` calls them before the
# world is typed); their revision-6 proofs carry over with the `ArenaReady` instances
for _f in ARENA:
    GBODY_PROOF[_f] = GBODY_PROOF[_f].replace('(fun s h => h.1)', '(fun s h => h)').replace(
        'localsFree_worldOK', 'localsFree_arenaReady').replace('worldOK_guestInv', 'arenaReady_guestInv')


def ast_index(path, fname):
    lines = open(path).read().split('\n')
    start = next(i for i, l in enumerate(lines) if l.startswith('def guestAst :'))
    for k, l in enumerate(lines[start + 1:]):
        if l.strip().rstrip(',').rstrip(']').strip() == 'guestFn_' + fname:
            return k
    raise KeyError(fname)


# Preconditions of the relational contracts other than the caller's world guard (revision 7: the
# output buffers of `compute_state_root`/`build_mpt_indexed`/`mpt_root` are the region `R` of the
# step, whose avoidance is a hypothesis of `WorldStep`, so their revision-6 `WorldAvoids` pre went)
KEEP_PRE = {
    'requests_append': 'ReqRoom',
    'lst_push': 'BoListArg',
    # revision 8 (round-5 Astra item 2): the three list selectors only
    'bal_remove_change': 'BalChangeArg',
}
# revision 8 (round-5 Fable item 1): callees whose world step quantifies only over the typings
# containing the guard's tables (`WorldKeepsIn`)
KEEP_IN = {'MsgReady': 'fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)]'}
# revision 7: output regions of world-tier callees that write a caller object outside the world
# (besides the `REGION` parameter extents): the message record, the output buffers
RREG = {
    'process_message_call': [('msg', '176')],
    'compute_state_root': [('out', '32')], 'build_mpt_indexed': [('out', '32')],
    'mpt_root': [('out', '32')],
}
# world-tier callees whose written list is a world object (`lst_push(bo+40|bo+72, 8)`): no region
NO_REGION = {'lst_push'}
# trie-object callees (`MptKeeps`: the object `m` and its nodes are carried)
MPT_KEEPS = {'mpt_set', 'mpt_root'}
# callee-specific extras of `WorldStep` (stated for the exit typing `S'`)
WQ = {'requests_append': 'ReqCountInc', 'mpt_from_witness': 'RetMptObj',
      'decode_host_input': 'RetInput',
      # revision 8 (round-5 Astra item 4): the constructors' results avoid the EXIT world
      'alloc': '(RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)]))',
      'msg_new': '(RetAvoids (fun _ _ w => [(w, 176)]))',
      'te_new': '(RetAvoids (fun _ _ w => [(w, 200)]))',
      'mpt_new': '(RetAvoids (fun _ _ w => [(w, 16)]))',
      'lst_new': ('(RetAvoidsIf (fun s => locN s "esz" * locN s "cap" < 2 ^ 64)\n'
                  '      (fun s post w => [(w, 24), (memW post w, locN s "esz" * locN s "cap")]))'),
      'htab_copy': ('(RetAvoidsIf (fun s => HtabWF s (locN s "t") ∧\n'
                    '        ∀ i ∈ htabFootprint s (locN s "t"), Allocated s i)\n'
                    '      (fun _ post w => htabFootprint post w))'),
      # revision 8 (round-5 Astra item 6): the returned element slot
      'lst_push': 'RetListSlot'}
# revision 7 (round-4 Gemini item 1(c)): return typing of the constructors whose results feed
# guards, and value contracts the walks need; one leaf per callee, at every needed call site
RT = {
    'node_new_ext': ('Returns ArenaReady (fun s post p => FreshBlock s post p 56)',
                     'returns a fresh 56-byte heap node, separated from the decoder scratch stack'),
    'alloc': ('Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n"))',
              'returns a fresh aligned heap block of `n` bytes'),
    'msg_new': ('Returns ArenaReady (fun s post m => FreshBlock s post m 176 ∧\n'
                '      ∀ k, k < 22 → memW post (m + 8 * k) = 0)',
                'returns a fresh zeroed 176-byte message record (`alloc(176)`, `memzero`)'),
    'te_new': ('Returns ArenaReady (fun s post m => FreshBlock s post m 200 ∧\n'
               '      ∀ k, k < 25 → memW post (m + 8 * k) = 0)',
               'returns a fresh zeroed 200-byte transaction environment'),
    'lst_new': ('Returns ArenaReady (fun s post l =>\n'
                '      locN s "esz" * locN s "cap" < 2 ^ 64 → 1 ≤ locN s "cap" →\n'
                '        FreshBlock s post l 24 ∧ FreshBlock s post (memW post l) (locN s "esz" * locN s "cap") ∧\n'
                '        Disj (l, 24) (memW post l, locN s "esz" * locN s "cap") ∧\n'
                '        memW post (l + 8) = 0 ∧ memW post (l + 16) = locN s "cap")',
                'returns a fresh empty list (`LstOK`): header and backing array fresh and disjoint'),
    'mpt_new': ('Returns ArenaReady (fun s post m => FreshBlock s post m 16 ∧\n'
                '      memW post m = locN s "root_node" ∧ memW post (m + 8) = locN s "secured")',
                'returns a fresh 16-byte trie object with root `root_node`'),
    # revision 8 (round-5 Astra item 3): only a copy of an ALLOCATED table is well formed
    # (`htab_copy` allocates the destination at `heap_ptr`, over a source lying in free heap)
    'htab_copy': ('Returns ArenaReady (fun s post n => locN s "t" ≠ 0 ∧\n'
                  '      (HtabWF s (locN s "t") → (∀ i ∈ htabFootprint s (locN s "t"), Allocated s i) →\n'
                  '        HtabWF post n ∧ hdr post n 3 = hdr s (locN s "t") 3 ∧\n'
                  '        ∀ i ∈ htabFootprint post n, Inside i (globN s "heap_ptr") (globN post "heap_ptr")))',
                  'a normal return copied a nonzero table (`load(t + 80)` errors at `0`); a copy of a '
                  'well-formed allocated table is a fresh well-formed table'),
    # revision 8 (round-5 Astra item 7, Gemini suggestion): the returned block is fresh scratch and
    # `scratch_ptr` drops to it (`_mpt_delete_node_body` writes its frame fields through it)
    'scratch_alloc': ('Returns ArenaReady (fun s post p => FreshScratch s post p (locN s "n") ∧\n'
                      '      globN post "scratch_ptr" = p)',
                      'returns a fresh aligned scratch block of `n` bytes and lowers `scratch_ptr` to it'),
}
XV = {
    'memzero': ('zv_memzero', 'ZeroFills (ofString "memzero")',
                'zero-fills `[dst, dst + n)` (value contract)'),
    'validate_transaction': ('rv_validate_transaction', 'RetIntrinsic (ofString "validate_transaction")',
                             'returns an intrinsic cost with regular part at most `2^24` (value contract, '
                             'checks 12667)'),
    'min': ('rv_min', 'RetLe (fun s => locN s "a") (ofString "min")', 'returns at most `a` (value contract)'),
}
XV['htab_set'] = ('nz_htab_set', 'ArgNonNull "t" (ofString "htab_set")',
                  'resumes only on a nonzero table (`load(t + 0)` errors at `0`, AST 5156)')
XV['u256_to_be_min'] = ('rv_u256_to_be_min', 'RetLe (fun _ => 32) (ofString "u256_to_be_min")',
                        'returns its byte count, at most 32 (value contract)')
XV['rlp_encode_bytes'] = ('rv_rlp_encode_bytes', 'RetLe (fun s => locN s "n" + 9) (ofString "rlp_encode_bytes")',
                          'returns at most `n + 9` (header and payload; value contract)')
XV['encode_withdrawal_rlp'] = ('dm_encode_withdrawal_rlp',
                               'ResumesInDomain (fun s => (locN s "wd", 1)) (ofString "encode_withdrawal_rlp")',
                               'resumes only on an in-domain record (`loadByte(wd)`, AST 32123)')
XV['memcpy'] = ('dm_memcpy', 'ResumesInDomain (fun s => (locN s "dst", locN s "n")) (ofString "memcpy")',
                'resumes only if its destination is in the memory domain (it stores every byte)')
XV_AT = {'memzero': None, 'validate_transaction': ('process_transaction',), 'min': ('process_transaction',),
         'htab_set': ('get_storage',), 'u256_to_be_min': ('compute_state_root',),
         'rlp_encode_bytes': ('compute_state_root',), 'encode_withdrawal_rlp': ('payload_header',),
         'memcpy': ('process_transaction',)}


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
    def fresh_only(g):
        """Every store in g's closure (contracted callees excluded) lands in a block g's closure
        allocated itself (`alloc`/`scratch_alloc` result, plus offsets) or in a global buffer,
        and no written parameter of a callee receives anything else."""
        for x in closure(g):
            if x in ('alloc', 'scratch_alloc', 'trap_with'):
                continue
            src = {}

            def d(y, _c):
                if is_app(y, 'Prog.dec'):
                    src[strval(y[2][0])] = ('exp', y[2][2])
                elif is_app(y, 'Prog.decCall'):
                    src[strval(y[2][0])] = ('call', strval(y[2][2]))
                elif is_app(y, 'Prog.call'):
                    opt = y[2][0]
                    if is_app(opt, 'some'):
                        dd = opt[2][0][1][0]
                        if is_app(dd, 'some') and panast.show(dd[2][0][1][0]) == 'local':
                            src.setdefault(dd[2][0][1][1][1], ('call', strval(y[2][1])))
                elif is_app(y, 'Prog.assign') and panast.show(y[2][0]) == 'local':
                    src[y[2][1][1]] = ('bad', None)
            panast.walk(fns[x], d)

            def classify_var(n, depth):
                """'root' (fresh block, inner parameter), 'bad' (built from a load) or 'off'."""
                if x != g and n in par.get(x, []):
                    return 'root'     # checked at the call site (written-parameter arguments)
                how = src.get(n, ('off', None))
                if how[0] == 'call' and how[1] in ('alloc', 'scratch_alloc'):
                    return 'root'
                if how[0] == 'exp':
                    r = ok(how[1], depth + 1)
                    return 'root' if r == 'root' else ('bad' if r == 'bad' else 'off')
                return 'off'

            def ok(e, depth=0):
                """An address is accepted iff it has no loaded component and at least one root
                (fresh block, global buffer, inner parameter); other locals are offsets."""
                if depth > 6 or has_load(e):
                    return 'bad'
                kinds = set()
                for (k, n) in free_vars(e):
                    if k == 'global':
                        kinds.add('root' if n in bufsize else 'bad')
                    else:
                        kinds.add(classify_var(n, depth))
                if 'bad' in kinds:
                    return 'bad'
                return 'root' if 'root' in kinds else 'off'
            targets = list(stores(fns[x]))
            for cg, args in calls_of(fns[x]):
                for i, pn in enumerate(par.get(cg, [])):
                    if pn in wp.get(cg, ()) and i < len(args):
                        targets.append(args[i])
            if not all(ok(a) == 'root' for a in targets):
                return False
        return True
    G = lambda f: guard_of.get(f, 'WorldOK')
    need = {f: needed_calls(fns, f, guarded, f in roots) for f in guarded}
    contracts = {}   # name -> (statement, comment)
    hyps = {}        # f -> list of (type, primitive-or-local name)
    seen_st = {}
    full = {}

    def full_closure(g):
        """Every function reachable from `g` (contracted callees included)."""
        if g not in full:
            seen, st = set(), [g]
            while st:
                x = st.pop()
                if x in seen or x not in fns:
                    continue
                seen.add(x)
                st.extend(graph[x])
            full[g] = seen
        return full[g]
    rec_size = {'ws': 40, 'bs': 80, 'ts': 72, 'bo': 88}

    def rec_offsets(e, decs, depth=0):
        """{record: set of offsets or 'ALL'} for an address expression, ignoring loaded parts."""
        out = {}
        if depth > 8 or not isinstance(e, tuple):
            return out
        if is_app(e) and e[1] in ('Exp.load', 'Exp.loadByte', 'Exp.shMemLoad'):
            return out
        v = var_name(e)
        if v and v[0] == 'global' and v[1] in rec_size:
            return {v[1]: {0}}
        if v and v[0] == 'local' and v[1] in decs:
            r = {}
            for d in decs[v[1]]:
                for k, o in rec_offsets(d, decs, depth + 1).items():
                    r[k] = 'ALL' if (r.get(k) == 'ALL' or o == 'ALL' or (k in r and r[k] != o)) else o
            return r
        if is_app(e, 'Exp.op') and panast.show(e[2][0]) == 'add':
            terms = e[2][1][1]
            subs = [rec_offsets(x, decs, depth + 1) for x in terms]
            consts = [const_value(x) for x in terms]
            for i, sub in enumerate(subs):
                for k, o in sub.items():
                    others = [c for j, c in enumerate(consts) if j != i]
                    if o == 'ALL' or any(c is None for c in others):
                        out[k] = 'ALL'
                    else:
                        out[k] = 'ALL' if out.get(k) == 'ALL' else (out.get(k, set()) | {x + sum(others) for x in o})
            return out
        for x in (e[2] if is_app(e) else e[1] if e[0] in ('tup', 'list') else []):
            for k, o in rec_offsets(x, decs, depth + 1).items():
                out[k] = 'ALL'
        return out

    def rec_written(g):
        """Offsets of the typed records `ws`, `bs`, `ts`, `bo` that `g`'s closure may store to."""
        res = {}
        for x in full_closure(g):
            decs = {}

            def d(y, _c):
                if is_app(y, 'Prog.dec'):
                    decs.setdefault(strval(y[2][0]), []).append(y[2][2])
                elif is_app(y, 'Prog.assign') and panast.show(y[2][0]) == 'local':
                    decs.setdefault(y[2][1][1], []).append(y[2][2])
            panast.walk(fns[x], d)
            hits = []
            for a in stores(fns[x]):
                hits.append((a, False))
            for cg, args in calls_of(fns[x]):
                for i, pn in enumerate(par.get(cg, [])):
                    if pn in wp.get(cg, ()) and i < len(args):
                        hits.append((args[i], True))
            for a, whole in hits:
                for k, o in rec_offsets(a, decs).items():
                    if whole or o == 'ALL' or res.get(k) == 'ALL':
                        res[k] = 'ALL'
                    else:
                        res[k] = res.get(k, set()) | o
        return res

    def record_aliases():
        """Revision 8 (round-5 Fable non-blocking): `rec_written` follows LOCAL aliases of the four
        typed records only. Check that their pointers reach memory only through the two known
        record links (`ts+0 := bs`, `state_fresh_tx`; `bs+0 := ws`, `state_init`), and that no
        store address or written-parameter argument anywhere on the call graph is computed from a
        load of such a link (or of any word holding a record pointer). Then no store reaches a
        typed record through a memory alias, and `rec_written` is complete."""
        links = set()
        for x in reach:
            if x not in fns:
                continue
            decs = {}

            def d(y, _c):
                if is_app(y, 'Prog.dec'):
                    decs.setdefault(strval(y[2][0]), []).append(y[2][2])
                elif is_app(y, 'Prog.assign') and panast.show(y[2][0]) == 'local':
                    decs.setdefault(y[2][1][1], []).append(y[2][2])
            panast.walk(fns[x], d)

            def st(y, _c):
                # a stored VALUE that is (an offset of) a record pointer; loaded parts are words
                # read from memory, not record pointers (`rec_offsets` ignores them)
                if is_app(y) and y[1] in ('Prog.store', 'Prog.storeByte'):
                    if rec_offsets(y[2][1], decs):
                        for k, o in rec_offsets(y[2][0], decs).items():
                            links.add((x, k, 'ALL' if o == 'ALL' else tuple(sorted(o))))
            panast.walk(fns[x], st)
        assert links == {('state_init', 'bs', (0,)), ('state_fresh_tx', 'ts', (0,))}, links
        for x in reach:
            if x not in fns:
                continue
            decs = {}

            def d2(y, _c):
                if is_app(y, 'Prog.dec'):
                    decs.setdefault(strval(y[2][0]), []).append(y[2][2])
                elif is_app(y, 'Prog.assign') and panast.show(y[2][0]) == 'local':
                    decs.setdefault(y[2][1][1], []).append(y[2][2])
            panast.walk(fns[x], d2)

            def loads_link(e, depth=0):
                """Does `e` contain a load of `ts+0` or `bs+0` (directly or through locals)?"""
                if depth > 8 or not isinstance(e, tuple):
                    return False
                if is_app(e) and e[1] == 'Exp.load':
                    ro = rec_offsets(e[2][-1], decs)
                    if any(k in ('ts', 'bs') and (o == 'ALL' or 0 in o) for k, o in ro.items()):
                        return True
                v = var_name(e)
                if v and v[0] == 'local' and v[1] in decs:
                    return any(loads_link(dv, depth + 1) for dv in decs[v[1]])
                kids = e[2] if is_app(e) else (e[1] if e[0] in ('tup', 'list') else [])
                return any(loads_link(c, depth + 1) for c in kids if isinstance(c, tuple))
            targets = list(stores(fns[x]))
            for cg, args in calls_of(fns[x]):
                for i, pn in enumerate(par.get(cg, [])):
                    if pn in wp.get(cg, ()) and i < len(args):
                        targets.append(args[i])
            for a in targets:
                assert not loads_link(a), ('store through a record link', x)
        return sorted(links)
    alias_links = record_aliases()

    def keep_lean(g):
        w = rec_written(g)
        items = []
        for r in ('ws', 'bs', 'ts', 'bo'):
            if w.get(r) == 'ALL':
                continue
            ks = [k for k in range(0, rec_size[r], 8) if k not in w.get(r, set())]
            items.append('("%s", [%s])' % (r, ', '.join(str(k) for k in ks)))
        return '[%s]' % ', '.join(items)
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
                if g in XV and (XV_AT[g] is None or f in XV_AT[g]) and f not in GBODY_PROOF:
                    xn, xst, xwhy = XV[g]
                    contracts[xn] = (xst, xwhy)
                    hs.append((xst, xn))
                continue
            if g not in impure:
                name = 'ro_' + g
                contracts[name] = ('ReadOnlyFn (ofString "%s")' % g, 'read-only')
            elif G(f) in ('MptReady', 'MptObjReady') and g in NODE_FN:
                name = 'nf_' + g
                req = NODE_REQ[g]
                req_s = 'fun _ _ => True' if req == 'True' else 'fun s Nd =>\n      ' + req
                contracts[name] = ('NodeFn [%s]\n    (%s)\n    (ofString "%s")' % (
                    ', '.join('"%s"' % n for n in NODE_FN[g]), req_s, g),
                    'typed nodes in, typed nodes out (MPT tier); requirement: %s' % (
                        'none' if req == 'True' else '`' + ' '.join(req.split()) + '`'))
            elif (f, g) in CALL_STMT:
                name, st = CALL_STMT[(f, g)]
                contracts[name] = (st, 'carries the frame built by `frame_open` (hand-written)')
            elif W == 'ArenaReady' and (g in REGION or g in FORCE_WW or fresh_only(g)) and not (g in guarded):
                name = 'ww_' + g
                if g not in REGION:
                    parts = ''
                else:
                    parts = REGION_RAW[g] if REGION[g] is None else ', '.join(
                        '(locN s "%s", %s)' % (pn, ln) for pn, ln in REGION[g])
                bw = buffers_written(g)
                if bw:
                    parts += (', ' if parts else '') + ', '.join('(globN s "%s", %d)' % (b, bufsize[b]) for b in bw)
                gws = sorted(gwf(g))
                contracts[name] = ('WritesWithin (fun s => [%s])\n    [%s] (ofString "%s")' % (
                    parts, ', '.join('"%s"' % x for x in gws), g),
                    ('writes its parameter extents' if g in REGION else 'writes only memory it allocates')
                    + (' and the buffers ' + ', '.join(bw) if bw else ''))
            elif W == 'ArenaReady':
                name = 'ak_' + g
                contracts[name] = ('KeepsOn ArenaReady ArenaReady (ofString "%s")' % g, 'keeps `ArenaReady`')
            else:
                # revision 7 (round-4 Gemini item 1): relational contracts in the world and EVM tiers
                Wc = CALL_W.get((f, g), W)
                gws = '[%s]' % ', '.join('"%s"' % x for x in sorted(gwf(g)))
                regs = [] if g in NO_REGION else (
                    [('locN s "%s"' % pn, ln) for pn, ln in (REGION.get(g) or [])] +
                    [('locN s "%s"' % pn, ln) for pn, ln in RREG.get(g, [])])
                R = 'fun s => [%s]' % ', '.join('(%s, %s)' % r for r in regs) if regs else 'fun _ => []'
                if Wc == 'EvmInv':
                    name = 'ek_' + g
                    if (f, g) in CALL_PRE:
                        pre = CALL_PRE[(f, g)]
                    elif regs:
                        pre = 'EvmAvoids (%s)' % R
                    else:
                        pre = 'EvmInv'
                    pre_s = pre if pre.isidentifier() else '(%s)' % pre
                    contracts[name] = ('EvmKeeps %s\n    %s (ofString "%s")' % (pre_s, gws, g),
                                       'EVM step: `EvmInv`, `ev`/`cur_cont` (unless written) and the '
                                       'frame chain kept')
                elif g in MPT_KEEPS:
                    name = 'mk_' + g
                    contracts[name] = ('MptKeeps (%s) %s\n    %s (ofString "%s")' % (
                        R, gws, keep_lean(g), g),
                        'trie-object step: the object `m` stays typed in the grown world')
                else:
                    name = 'wk_' + g
                    if (f, g) in CALL_PRE:
                        pre = CALL_PRE[(f, g)]
                    elif g in KEEP_PRE:
                        pre = KEEP_PRE[g]
                    elif g in guarded and GUARD_W[G(g)] == 'WorldOK':
                        pre = G(g)
                    else:
                        pre = 'WorldOK'
                    pre_s = pre if pre.isidentifier() else '(%s)' % pre
                    if pre in KEEP_IN:
                        pre_s = '%s (%s)' % (pre_s, KEEP_IN[pre])
                    contracts[name] = ('WorldKeeps%s %s (%s)\n    %s\n    %s\n    %s (ofString "%s")' % (
                        'In' if pre in KEEP_IN else '', pre_s, R, gws, keep_lean(g), WQ.get(g, 'NoExtra'), g),
                        'relational world step' + (
                            ' with output region' if regs else '') + (
                            ' and extra `%s`' % WQ[g] if g in WQ else ''))
            if name in seen_st:
                assert seen_st[name] == contracts[name][0], name
            seen_st[name] = contracts[name][0]
            hs.append((contracts[name][0], name))
            if (f, g) in CALL_WW:
                wst = 'WritesWithin (fun s => [(locN s "dst", locN s "n")])\n    [%s] (ofString "%s")' % (
                    ', '.join('"%s"' % x for x in sorted(gwf(g))), g)
                contracts['ww_' + g] = (wst, 'writes its parameter extent (`ArenaReady` tier, at `%s`)' % f)
                hs.append((wst, 'ww_' + g))
            if g in EXTRA and f in EXTRA[g][3]:
                xn, xst, xwhy, _fs = EXTRA[g]
                contracts[xn] = (xst, xwhy)
                hs.append((xst, xn))
            if g in RT and f not in GBODY_PROOF:
                rst = '%s\n    (ofString "%s")' % (RT[g][0], g)
                contracts['rt_' + g] = (rst, RT[g][1])
                hs.append((rst, 'rt_' + g))
            if g in XV and (XV_AT[g] is None or f in XV_AT[g]) and f not in GBODY_PROOF:
                xn, xst, xwhy = XV[g]
                contracts[xn] = (xst, xwhy)
                hs.append((xst, xn))
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
        table = []
        for f in order:
            if f not in guarded:
                continue
            g0 = G(f)
            ls = loops[f]
            note = '; '.join('#%d %s' % (i, cls[0]) for (i, _c, _b, _d, cls) in ls) or 'loop-free'
            direct = sorted(graph[f] & reach)
            # revision 6 (round-4 Astra item 8): every hypothesis names a direct callee of f, and
            # every direct callee has its bound among the hypotheses
            named = [re.findall(r'ofString "([^"]+)"', t) for t, _n in hyps[f]]
            spec_callee = {sp: g for g, sps in SPEC_OF.items() for sp in sps}
            for (t, n), ns in zip(hyps[f], named):
                if n in spec_callee:
                    ns = [spec_callee[n]]
                assert len(set(ns)) == 1 and ns[0] in direct, (f, n, ns)
            bounds = [n for _t, n in hyps[f] if n.startswith(('fb_', 'gb_'))]
            assert sorted(b[3:] for b in bounds) == direct, f
            cons = [(n, t) for t, n in hyps[f] if not n.startswith(('fb_', 'gb_'))]
            table.append((f, line_of[f], g0, note, direct, bounds, [n for n, _t in cons],
                          f in GBODY_PROOF))
            o.write('/-- The body of `%s` alone (AST line %d, guard `%s`, %s). Its direct callees are\n'
                    'exactly %s (`«callees_%s»`, checked against the AST). Hypotheses: the bound\n'
                    'of each of these %d callees, then the contract of each callee at a guard-carrying\n'
                    'call site (%d: %s). Nothing else is assumed. -/\n'
                    'def GBody.«%s» : Prop :=\n' % (
                        f, line_of[f], g0, note,
                        ', '.join('`%s`' % g for g in direct) if direct else 'none', f,
                        len(direct), len(cons),
                        ', '.join('`%s`' % n for n, _t in cons) if cons else 'none', f))
            for t, _n in hyps[f]:
                o.write('  (%s) →\n' % t)
            o.write('  TerminatingFunBoundedOn %s (ofString "%s") K.«%s»\n\n' % (g0, f, f))
            o.write('/-- The direct callees of `%s`, read off its AST body (revision 6). -/\n'
                    'theorem «callees_%s» : sameNames (progCallees (fnBody Guest.Software.guestFn_%s))\n'
                    '    [%s] = true := by decide\n\n' % (
                        f, f, f, ', '.join('"%s"' % g for g in direct)))
            if f in GBODY_PROOF or f in LOOKUP_EXTRA:
                idx = ast_index(path, f)
                o.write('theorem «lookup_%s» : originalRuntimeCode.lookup (ofString "%s") =\n'
                        '    some ((sourceFunctionEntry Guest.Software.guestFn_%s).2) :=\n'
                        '  originalRuntimeCode_lookup_of_guestAst_getElem %d (by rw [guestAst_len]; decide)\n'
                        '    (extractFn Guest.Software.guestFn_%s) rfl\n\n' % (f, f, f, idx, f))
            if f in GBODY_PROOF:
                o.write('/-- PROVED by concrete-body composition (no longer a primitive). -/\n'
                        'theorem «gbody_%s» : GBody.«%s» := by\n' % (f, f))
                o.write(GBODY_PROOF[f].replace('{LOOKUP}', '«lookup_%s»' % f).replace(
                    '{UNFOLD}', UNFOLD_LEMMAS.replace('{F}', f)))
                o.write('\n')
            else:
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
            if f not in GBODY_PROOF:
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
            o.write('  have «g_%s» := %s«gbody_%s»' % (f, '' if f in GBODY_PROOF else 'P.', f))
            for _t, n in hyps[f]:
                o.write(' «g_%s»' % n[3:] if n.startswith('gb_') else ' P.«%s»' % n)
            o.write('\n')
        o.write('  exact «g_main»\n\n')
        o.write('/-- The leaves discharge the primitives (each field is its `sorry` leaf). -/\n'
                'theorem primitives : Primitives where\n')
        for n, _t in prims:
            o.write('  «%s» := «%s»\n' % (n, n))
        o.write('\n')
    with open(os.path.join(outdir, 'gbody.md'), 'w') as o:
        o.write('| `gbody_*` (function) | guard | loops | direct callees = bound hypotheses | '
                'contract hypotheses | status |\n|---|---|---|---|---|---|\n')
        for f, ln, g0, note, direct, bounds, cons, proved in table:
            o.write('| `%s` (AST %d) | `%s` | %s | %d: %s | %d: %s | %s |\n' % (
                f, ln, g0, note, len(direct), ', '.join(direct) if direct else '—',
                len(cons), ', '.join('`%s`' % c for c in cons) if cons else '—',
                '**proved**' if proved else 'primitive'))
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
        'process_transaction': 'TxReady', 'process_general_purpose_requests': 'ReqsFresh',
        'process_message': 'MsgReady', 'process_message_call': 'MsgReady',
        'process_create_message': 'MsgReady',
        # revision 5 (round-4 Fable item 1 and non-blocking item)
        'op_dispatch': 'EvmRun', 'op_sload': 'EvmRun', 'op_sstore': 'EvmRun',
        'execute_block': 'BlockReady',
        # revision 7: the witness decoders run inside `state_init` after `ws := alloc(40)` and
        # before `ws+24`/`ws+32` are stored, where `WorldOK` does not hold; their bodies only
        # need separated arenas (the revision-6 proofs used `WorldOK` only to reach `ArenaReady`)
        'decode_witness_to_mpt': 'ArenaReady', '_decode_witness_node': 'ArenaReady',
        '_decode_witness_node_mpt': 'ArenaReady', 'mpt_from_witness': 'ArenaReady',
        # revision 7: the input cells `run_attempt` reads `ntx` through are outside the world
        'verify_stateless_new_payload': 'InputReady', 'run_attempt': 'InputReady'}
    guard_of.update({'attempt_l%d' % k: 'InputReady' for k in range(1, 8)})
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
                        and const_value(args[0]) is not None:
                    bufs.setdefault(d[2][0][1][1][1], set()).add((callee, const_value(args[0])))
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
