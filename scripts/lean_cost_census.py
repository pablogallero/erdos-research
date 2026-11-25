# Session 87 (notes/erdos-470.md): KERNEL-COST census of the Lean pipeline (IntervalGap + pair layer + bounded pairs) on
# real deficient 3-prime prefixes. Per sampled prefix: (c, g) from multi_plan, the pair layer (pair_cert_gen.py RANGES=1,
# with QHI from the q-tails and, for p with n p^f eventually abundant, from not_weird_tail on n p^f for f < F) and the
# bounded pairs (quad_probe.py). Cost model: 0.3 s per pairOK, 0.04 s per bounded cell, 0.1 s per abundant p / range
# (session 82-83 measurements). Read-only on the checkpoint copy (prefix SHAPE only); decides nothing; no owf.
# Usage: python3 -I scripts/lean_cost_census.py CKFILE E SAMPLE SEED LIMB
import ast, os, random, subprocess, sys, time, re, io, contextlib
from math import gcd
R = os.path.dirname(os.path.abspath(__file__))
ck, E, NS, SEED, LIMB = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
sys.argv = ['x', str(LIMB), '0']
g_ = {'__file__': R + '/raise_late_plan.py', '__name__': 'lib'}
with contextlib.redirect_stdout(io.StringIO()):
    exec(open(R + '/raise_late_plan.py').read(), g_)
multi_plan, sigma = g_['multi_plan'], g_['sigma']
sys.path.insert(0, R)
sys.dont_write_bytecode = True
import pair_cert_gen as PG
def isp(x):
    return PG.isprime(x)
def warn_bound(n, S, c, g, plo, Q3):
    # p with q-tail None (n p^f eventually abundant): F = least f with n p^F pseudoperfect (stepAbOK);
    # for f < F, q >= Q_f is covered by not_weird_tail on n p^f. Returns (needed QHI, gaps)
    QH, gaps = 0, []
    for p in range(plo, Q3):
        if not (isp(p) and n % p) or PG.q_tail(n, S, p) is not None or PG.stepAbOK(n, S, c, g, [(p, 1)]): continue
        F = None
        for f in range(1, 60):
            if PG.stepAbOK(n, S, c, g, [(p, f)]): F = f; break
            m, T = PG.stepsEnd(n, S, [(p, f)])
            if T >= m: gaps.append((p, f, 'abundant not certified')); break
            A, B = 2 * m, T + m          # sigma(m)(Q+1) <= 2m(Q-1)
            QH = max(QH, PG.ceil_div(A + B, A - B))
        if F is None and not gaps: gaps.append((p, 'no F'))
    return QH, gaps
def sig(p, e): return (p ** (e + 1) - 1) // (p - 1)
keys = set()
for line in open(ck):
    line = line.strip()
    if not line.endswith(')'): continue
    try: f, un, ud, j, q0 = ast.literal_eval(line)
    except Exception: continue
    if j != 3 or len(f) != 3 or f[0] != (3, E): continue
    n = s = 1
    for p, e in f: n *= p ** e; s *= sig(p, e)
    gg = gcd(s, n)
    if (un, ud) != (s // gg, n // gg) or 2 * n <= s: continue
    keys.add(tuple(f))
keys = sorted(keys); random.seed(SEED); samp = random.sample(keys, min(NS, len(keys)))
print('root 3^%d: %d exact deficient prefixes, sample %d' % (E, len(keys), len(samp)), flush=True)
for f in samp:
    t = time.time(); n = 1
    for p, e in f: n *= p ** e
    S = sigma(n) - n
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            pl = multi_plan(dict(f))
    except Exception as ex: pl = None
    if not pl: print(f, 'NOPLAN', flush=True); continue
    c, g = pl[3], pl[4]
    plo = max(p for p, _ in f) + 1
    Q3 = 2
    while not (S + n) * Q3 * (Q3 + 1) <= 2 * n * (Q3 - 1) * (Q3 - 1): Q3 += 1
    QH, gaps = warn_bound(n, S, c, g, plo, Q3)
    a0 = [str(x) for x in (n, S, c, g, plo, 10 ** 7, 10 ** 6)]
    o0 = subprocess.run([sys.executable, '-I', R + '/pair_cert_gen.py'] + a0 + ['0'], capture_output=True, text=True, timeout=300, env=dict(os.environ, RANGES='1')).stderr
    lq = re.search(r'largest Q (\d+)', o0)
    qhi = max(QH, int(lq.group(1)) if lq else 0) + 1
    a = [str(x) for x in (n, S, c, g, plo, 10 ** 7, qhi)]
    try:
        o1 = subprocess.run([sys.executable, '-I', R + '/pair_cert_gen.py'] + a, capture_output=True, text=True, timeout=300, env=dict(os.environ, RANGES='1')).stderr
        o2 = subprocess.run([sys.executable, '-I', R + '/quad_probe.py'] + a, capture_output=True, text=True, timeout=300).stderr
    except subprocess.TimeoutExpired:
        print(f, 'c=%d g=%d TIMEOUT' % (c, g), flush=True); continue
    m = re.search(r'pairs certified (\d+), failed (\d+) (\{.*\})', o1)
    ab = re.search(r'abundant \(all q\) \[(.*?)\]; ranges (\d+)', o1)
    q = re.search(r'below the q-tails (\d+): certified (\d+) \(total cells (\d+)\)', o2)
    warn = o1.count('WARNING')
    if not (m and q and ab): print(f, 'PARSE', o1[-300:], o2[-300:], flush=True); continue
    nab = len([x for x in ab.group(1).split(',') if x.strip()])
    other = {k: v for k, v in ast.literal_eval(m.group(3)).items() if not k.startswith('bounded pair')}
    kern = 0.3 * int(m.group(1)) + 0.04 * int(q.group(3)) + 0.1 * (nab + int(ab.group(2)))
    print(f, 'c=%d g=%d abp=%d ranges=%s pairOK=%s bounded=%s/%s cells=%s other=%s warn=%d QH=%d gaps=%s kernel~%.0fs (%.1fs py)' % (
        c, g, nab, ab.group(2), m.group(1), q.group(2), q.group(1), q.group(3), other, warn, QH, gaps, kern, time.time() - t), flush=True)
