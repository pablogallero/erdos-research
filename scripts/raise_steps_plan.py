# Session 56 (notes/erdos-470.md): find a plan (raise one prime from a small bitset base, then old prime-power steps)
# for random deficient 5-prime prefixes, such that EVERY last prime q is covered (not_weird_mul_prime_of_intervalGap).
# Usage: python3 scripts/raise_steps_plan.py LIMB. Python only; not the omega=6 search.
import os
import itertools, random, sys
__file__=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'raise_step_probe.py')
exec(open(__file__).read().split("if os.environ.get('SOUND'")[0])
LIMB=int(sys.argv[1])
def plan(f):
    """prefix f (dict). returns (p,m,e0,c,g,gB,order) with raise of p then old steps, interval on D(n), or None."""
    ps=sorted(f); n=1
    for p,e in f.items(): n*=p**e
    best=None
    for p in ps:
        others=[q for q in ps if q!=p]
        for k in range(0,len(others)):
            for R in itertools.combinations(others,k):
                m=1
                for q in R: m*=q**f[q]
                if m>LIMB: continue
                sB,gB=gap0(m)
                for e0 in range(1,f[p]):
                    b=m*p**e0
                    if b>LIMB: break
                    s,bits,c,g=info(b)
                    if c is None: continue
                    if not all(raise_ok(m,p,e,c,g) for e in range(e0,f[p])): continue
                    rest=[q for q in others if q not in R]
                    for order in (sorted(rest),sorted(rest,reverse=True)):
                        k2=m*p**f[p]; sg2=sigma(m)*sigpp(p,f[p]); S=sg2-k2; good=True
                        for q in order:
                            if not (q*g+2*c<=S+1 and k2+2*c<=(q+1)*S+1): good=False;break
                            sg2*=sigpp(q,f[q]); k2*=q**f[q]; S=sg2-k2
                        if good: return (p,m,e0,c,g,gB,order,s)
    return None
def allq(n,c,g,sg):
    S=sg-n; bad=[]
    for q in range(2, sg//max(1,2*n-sg)+3):
        if not isprime(q) or n%q==0: continue
        if n*q < S+(n+q*S):
            if not (q*g+2*c<=S+1 and n+2*c<=(q+1)*S+1 and c<=n*q and n*q+c<=S+(n+q*S)): bad.append(q)
    return bad
random.seed(2)
primes=[p for p in range(3,60) if isprime(p)]
found=0
for t in range(3000):
    P=sorted(random.sample(primes[:8],5))
    f={p:random.choice([1,1,2,2,3,4,6,8,10]) for p in P}
    n=1
    for p,e in f.items(): n*=p**e
    sgn=1
    for p,e in f.items(): sgn*=sigpp(p,e)
    if sgn>=2*n: continue
    if max(f.values())<6: continue
    r=plan(f)
    if not r or not r[6]: continue
    if allq(n,r[3],r[4],sgn): continue
    print(f, r); found+=1
    if found>=6: break
