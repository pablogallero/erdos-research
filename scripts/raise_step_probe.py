# Session 56 (notes/erdos-470.md): exponent-raising split D(m p^(e+1)) = D(m p^e) ∪ {m p^e} ∪ p^(e+1)·D(m), p ∤ m.
# (1) soundness check by bitsets on small cases; (2) coverage on the chain-probe candidates (base -> raise -> old steps).
# Usage: python3 scripts/raise_step_probe.py [LIMB]. Python only; not the omega=6 search.
import os, itertools, random, sys
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'prime_step_check.py')).read().split("N=int")[0])
def sigpp(p,e): return (p**(e+1)-1)//(p-1)
def gap0(m):
    """max gap of SS(D(m)) on [0, sum D(m)] (1 if D(m) = {}: vacuous)."""
    if m==1: return 0,1
    D=divisors(m)[:-1]; s=sum(D); b=1
    for d in D: b|=b<<d
    bits=bin(b)[2:][::-1]
    return s,max(len(r) for r in bits[:s+1].split('1'))+1
def raise_ok(m,p,e,c,g):
    """conditions of interval_union_insert_image for A=D(m p^e), n=m p^e, multiplier p^(e+1), B=D(m)."""
    sB,gB=gap0(m)
    sA=sigma(m)*sigpp(p,e)-m*p**e
    return p**(e+1)*gB+2*c<=sA+1 and m*p**e+2*c<=p**(e+1)*sB+sA+1
def sigma(m):
    r=1
    for q,k in fac(m).items(): r*=sigpp(q,k)
    return r
# (1) soundness: odd m, p prime not dividing m, small; if base D(m p^e) has (c,g) and raise_ok, check D(m p^(e+1)).
if os.environ.get('SOUND','1')=='1':
    chk=ok=bad=0
    for m in range(1,400,2):
        for p in (3,5,7,11,13):
            if m%p==0: continue
            for e in range(1,4):
                n=m*p**e
                if n>60000: continue
                s,bits,c,g=info(n)
                if c is None: continue
                chk+=1
                if not raise_ok(m,p,e,c,g): continue
                ok+=1
                s2,b2,_,_=info(n*p)
                gt=max(len(r) for r in b2[:s2+1].split('1'))+1
                if '0' in b2[c:s2-c+1] or gt>g: bad+=1
    print("soundness: bases",chk,"raise-cond true",ok,"unsound",bad)
LIMB=int(sys.argv[1]) if len(sys.argv)>1 else 20000
def chain(n,f,rest,c,g):
    """old split: add remaining primes (full exponents) one by one, both orders; final test. Returns kind or None."""
    N=1
    for q,e in f.items(): N*=q**e
    for order in (sorted(rest),sorted(rest,reverse=True)):
        k=n; sg=sigma(n); good=True
        for q in order:
            S=sg-k
            if not (q*g+2*c<=S+1 and k+2*c<=(q+1)*S+1): good=False;break
            k*=q**f[q]; sg*=sigpp(q,f[q])
        if not good: continue
        S=sg-N
        if c<=N and N+c<=S: return "int"
        bits=info_bits.get(n)
        if bits and 0<=S-N<c and bits[S-N]=='1': return "excess"
    return None
info_bits={}
def certify(f,raise_=True):
    ps=sorted(f)
    for k in range(1,len(ps)+1):
        for B in itertools.combinations(ps,k):
            b=1
            for p in B: b*=p**f[p]
            if b>LIMB: continue
            s,bits,c,g=info(b); info_bits[b]=bits
            if c is None: continue
            r=chain(b,f,[p for p in ps if p not in B],c,g)
            if r: return ("base",r)
    if not raise_: return None
    for p in ps:
        others=[q for q in ps if q!=p]
        for k in range(0,len(others)+1):
            for R in itertools.combinations(others,k):
                m=1
                for q in R: m*=q**f[q]
                for e0 in range(1,f[p]):
                    b=m*p**e0
                    if b>LIMB: break
                    s,bits,c,g=info(b); info_bits[b]=bits
                    if c is None: continue
                    good=True
                    for e in range(e0,f[p]):
                        if not raise_ok(m,p,e,c,g): good=False;break
                    if not good: continue
                    n=m*p**f[p]
                    r=chain(n,f,[q for q in others if q not in R],c,g)
                    if r: return ("raise",r)
    return None
random.seed(1)
primes=[p for p in range(3,400) if isprime(p)]
tot=c0=c1=0; fails=[]
for trial in range(400):
    P=sorted(random.sample(primes[:12],5))
    f={p:random.choice([1,1,2,2,3,4,6,10,15,20]) for p in P}
    n=1; sg=1
    for p,e in f.items(): n*=p**e; sg*=sigpp(p,e)
    if sg>=2*n: continue
    Q=sg//(2*n-sg)
    qs=[q for q in primes if q>max(P) and q<=Q]
    for q in qs[:5]:
        g2=dict(f); g2[q]=1
        tot+=1
        r0=certify(g2,False); r1=r0 or certify(g2,True)
        c0+=bool(r0); c1+=bool(r1)
        if not r1: fails.append(g2)
print("LIMB",LIMB,"tested",tot,"old chain",c0,"with raise",c1)
for x in fails[:8]: print("fail",x)
