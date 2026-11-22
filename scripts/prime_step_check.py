# Session 54 (notes/erdos-470.md): numerical check of the Lean prime step (SubsetSumPrimeStep.lean).
# Usage: python3 scripts/prime_step_check.py N P  (odd deficient M < N, primes 3 <= p < P). Not the omega=6 search.
import sys
def fac(n):
    f={};d=2
    while d*d<=n:
        while n%d==0: f[d]=f.get(d,0)+1; n//=d
        d+=1
    if n>1: f[n]=f.get(n,0)+1
    return f
def divisors(n):
    ds=[1]
    for p,e in fac(n).items(): ds=[d*p**i for d in ds for i in range(e+1)]
    return sorted(ds)
def isprime(n): return n>1 and all(n%k for k in range(2,int(n**.5)+1))
def info(M):
    D=divisors(M)[:-1]; s=sum(D); b=1
    for d in D: b|=b<<d
    bits=bin(b)[2:][::-1]   # bits[x]=='1' iff x in SS
    # smallest c with [c,s-c] full: last missing x <= s/2, c=x+1 (symmetry)
    half=s//2
    miss=bits.rfind('0',0,half+1)
    c=miss+1
    if 2*c>s+1: return s,bits,None,None
    # max gap: largest run of zeros +1
    g=max(len(r) for r in bits[:s+1].split('1'))+1
    return s,bits,c,g
N=int(sys.argv[1]); P=int(sys.argv[2])
defi=cent=ok=bad=missed=0
primes=[p for p in range(3,P) if isprime(p)]
for M in range(3,N,2):
    s,bits,c,g=info(M)
    if s>=M: continue
    defi+=1
    if c is None: continue
    cent+=1
    for p in primes:
        if M%p==0: continue
        cond = p*g+2*c<=s+1 and M+2*c<=(p+1)*s+1
        s2,b2,_,_=info(M*p)
        truth='0' not in b2[c:s2-c+1]
        if cond: ok+=1; bad+=(not truth)
        elif truth: missed+=1
print("N",N,"deficient",defi,"centred",cent,"cond-true",ok,"unsound",bad,"missed",missed)
