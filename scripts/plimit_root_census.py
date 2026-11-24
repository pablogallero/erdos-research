# Session 75 (notes/erdos-470.md): how many REAL 3-prime prefixes of the omega=6 search does the staircase decider
# (plimit_probe.py, FASTSTRIP=1 BOUNDED=1) close? Samples exact depth-3 keys (f, un, ud, 3, q0) of root 3^E from a checkpoint
# file (only the prefix SHAPE is used: un/ud == sigma(f)/f marks an exact prefix; region keys are skipped), and runs the
# decider on each with a per-prefix timeout. Stars (r^h, h >= 2) are still excluded, as in plimit_probe.
# Read-only on the checkpoint; decides nothing about #470 (indicative). Never point it at a file a worker is writing unless
# read-only access is guaranteed (it only opens it for reading).
# Usage: python3 -I scripts/plimit_root_census.py CKFILE E SAMPLE SEED TIMEOUT [LIMB]
import ast, os, random, subprocess, sys, time
from math import gcd
ck, E, NS, SEED, TO = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
LIMB = sys.argv[6] if len(sys.argv) > 6 else '100000'
HERE = os.path.dirname(os.path.abspath(__file__))
def sig(p, e): return (p ** (e + 1) - 1) // (p - 1)
keys = []
with open(ck) as fh:
    for line in fh:
        line = line.strip()
        if not line.endswith(')'): continue                          # half-written last line
        try: f, un, ud, j, q0 = ast.literal_eval(line)
        except Exception: continue
        if j != 3 or len(f) != 3 or f[0] != (3, E): continue
        n = s = 1
        for p, e in f: n *= p ** e; s *= sig(p, e)
        g = gcd(s, n)
        if (un, ud) != (s // g, n // g): continue                    # region key, not an exact prefix
        if 2 * n <= s: continue                                     # abundant prefix: outside plimit_probe
        keys.append(f)
keys = sorted(set(tuple(k) for k in keys))
random.seed(SEED); samp = random.sample(keys, min(NS, len(keys)))
print('root 3^%d: %d exact deficient 3-prime prefixes, sample %d' % (E, len(keys), len(samp)), flush=True)
env = dict(os.environ, FASTSTRIP='1', BOUNDED='1')
tally = {}
for f in samp:
    plan = '*'.join('%d^%d' % pe for pe in f)
    t = time.time()
    try:
        out = subprocess.run([sys.executable, '-I', os.path.join(HERE, 'plimit_probe.py'), '--plan', plan, LIMB, '0'],
                             capture_output=True, text=True, timeout=TO, env=env).stdout
        tot = [l for l in out.splitlines() if l.startswith('TOTAL')]
        if not tot: res = 'noplan' if 'plan ' not in out else 'error'
        else: res = 'closed' if tot[0].split()[5] == '0' else 'fails:' + tot[0].split()[5]
    except subprocess.TimeoutExpired:
        res = 'timeout'
    tally[res.split(':')[0]] = tally.get(res.split(':')[0], 0) + 1
    print('%-28s %-10s %6.1fs' % (plan, res, time.time() - t), flush=True)
print('TALLY', tally, flush=True)
