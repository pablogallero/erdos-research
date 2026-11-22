# Session 55 (notes/erdos-470.md): probe of a *chain* certificate (not in Lean yet; not the omega=6 search).
# Base b = sub-product of N with bitset (b <= LIMB) giving (c, g); remaining prime powers added one by one
# (interval_properDivisors_mul_prime_pow keeps c, g). Random omega=6 candidates N = prefix * q, Nq abundant.
# Usage: python3 scripts/chain_cert_probe.py [LIMB]
import os
import itertools, random, sys
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'prime_step_check.py')).read().split("N=int")[0])
def sigpp(p,e): return (p**(e+1)-1)//(p-1)
def certify(f):
    """f: dict prime->exp for N. Try base = sub-product (< LIMB), chain the rest. Return how or None."""
    N=1
    for p,e in f.items(): N*=p**e
    ps=sorted(f)
    for k in range(1,len(ps)+1):
        for B in itertools.combinations(ps,k):
            b=1
            for p in B: b*=p**f[p]
            if b>LIMB: continue
            s,bits,c,g=info(b)
            if c is None: continue
            rest=[p for p in ps if p not in B]
            for order in (sorted(rest),sorted(rest,reverse=True)):
                n=b; sg=s+b; ok=True
                for p in order:
                    S=sg-n
                    if not (p*g+2*c<=S+1 and n+2*c<=(p+1)*S+1): ok=False;break
                    n*=p**f[p]; sg*=sigpp(p,f[p])
                if not ok: continue
                S=sg-N
                if c<=N and N+c<=S: return ("int",b,c,g)
                ex=S-N
                if 0<=ex<c and bits[ex]=='1': return ("excess",b,c,g)
    return None
LIMB=int(sys.argv[1]) if len(sys.argv)>1 else 20000
random.seed(1)
primes=[p for p in range(3,400) if isprime(p)]
tot=cert=0; fails=[]
for trial in range(400):
    k=6
    P=sorted(random.sample(primes[:12],k-1))
    f={p:random.choice([1,1,2,2,3,4,6,10,15,20]) for p in P}
    n=1; sg=1
    for p,e in f.items(): n*=p**e; sg*=sigpp(p,e)
    if sg>=2*n: continue   # prefix already abundant: skip
    # last primes q > max(P) making n q abundant
    Q=sg//(2*n-sg)
    qs=[q for q in primes if q>max(P) and q<=Q]
    for q in qs[:5]:
        g2=dict(f); g2[q]=1
        tot+=1
        r=certify(g2)
        if r: cert+=1
        else: fails.append(g2)
print("LIMB",LIMB,"tested",tot,"certified",cert)
for x in fails[:8]: print("fail",x)
