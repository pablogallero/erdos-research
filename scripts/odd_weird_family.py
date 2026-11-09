#!/usr/bin/env python3
"""Erdős #470: check that no odd weird number has exactly K distinct prime factors.

Usage: python3 scripts/odd_weird_family.py K      (K = 5: ~2-4 min; prints "K True {...}")

Same search as `chk` in ErdosResearch/OddWeirdFourCore.lean (sorted odd primes p_1 < ... < p_K,
exponents either exact or a region "x >= e"; prune when the stride-2 bound shows every completion
deficient), but the last prime is not enumerated. A node with one prime left is a *family*
{M' q^e : q >= q0 prime}, decided all at once:
  * Mq abundant (q D <= sigma(M), D = 2M - sigma(M)): Mq is pseudoperfect iff there are a in P and
    k = D + a with kq in P or kq - M in P, where P = subset sums of the proper divisors of M.
    P is described exactly: its elements below C (bitset), the interval [c, sigma(M)-M-c] it
    contains (checked by the chain condition over the sorted divisors), and its symmetry
    x <-> sigma(M)-M-x. Only primes q with Dq near a boundary of P or P+M need an individual test.
  * Mq not abundant but U q/(q-1) >= 2: go through the exponents of q; when M q^e is abundant,
    test it via the base-q digit representation of sigma(N) - 2N.
  * otherwise every completion is deficient.
A non-deficient prefix (fewer than K primes) is covered by the result for smaller omega
(multiple of a pseudoperfect number). Any test that cannot decide returns False, so the parent
splits the exponent further; True at the top is a proof (modulo bugs) for omega = K, given the
result for omega < K. isprime is Miller-Rabin; a composite wrongly accepted only adds work.
""" 
import sys, time
from math import gcd
sys.setrecursionlimit(100000)
def isprime(n):
    if n<2: return False
    for p in (3,5,7,11,13,17,19,23,29,31,37):
        if n%p==0: return n==p
    d=n-1;s=0
    while d%2==0: d//=2;s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in(1,n-1): continue
        for _ in range(s-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def sig(p,e): return (p**(e+1)-1)//(p-1)
C=1<<15
WIN=10**4
st={"n":0,"fam":0,"qchk":0,"star":0,"fail":[]}
def divisors(f):
    ds=[1]
    for p,e in f:
        ds=[d*p**i for d in ds for i in range(e+1)]
    ds.sort(); return ds
PC={}
def Pstruct(f,M,sigma):
    key=tuple(f)
    if key in PC: return PC[key]
    r=Pstruct0(f,M,sigma)
    if len(PC)>200000: PC.clear()
    PC[key]=r
    return r
def Pstruct0(f,M,sigma):
    """P = subset sums of proper divisors of M. Returns (B, c, sp): B = exact bits of P below C;
    if c is None then sp < 2C (P known exactly via symmetry); else P ⊇ [c, sp-c] with c <= C."""
    ds=divisors(f)[:-1]; sp=sigma-M
    B=1; mask=(1<<C)-1; T=0; c=None
    for d in ds:
        if c is None and T+d>=2*C:
            # SS so far exact: bits below C, symmetric about T/2 with T<2C
            m=(1<<(T//2+1))-1
            holes=(~B)&m
            c=holes.bit_length(); lo,hi=c,T-c
            if hi-lo<0: return None
        if c is not None:
            if d>hi-lo+1: return None
            hi+=d
        if d<C: B|=(B<<d)&mask
        T+=d
    assert T==sp
    if c is not None and c>C: return None
    return (B,c,sp)
def inP(x,ps):
    B,c,sp=ps
    if x<0 or x>sp: return False
    if c is None:
        y=x if x<C else sp-x
        return (B>>y)&1==1
    if x<C: return (B>>x)&1==1
    if x>sp-C: return (B>>(sp-x))&1==1
    assert c<=x<=sp-c
    return True
def pp_Mq(q,M,D,ps):
    """Mq pseudoperfect? exists a in P, k=D+a, kq in P or kq-M in P."""
    B,c,sp=ps; sigma=sp+M
    if c is not None:
        # a in [c, sp-c] (always in P); x=(D+a)q in [c, sp-c] or [M+c, sigma-c]
        for lo,hi in ((c,sp-c),(M+c,sigma-c)):
            alo=max(c,-(-lo//q)-D); ahi=min(sp-c,hi//q-D)
            if alo<=ahi: return True
    a=0
    while (D+a)*q<=sigma and a<=sp:
        if inP(a,ps):
            x=(D+a)*q
            if inP(x,ps) or inP(x-M,ps): return True
        a+=1
        if a>20000: break
    return False
def inQ(x,M,ps): return inP(x,ps) or inP(x-M,ps)
def pp_Mqe(q,e,M,ps,f=None):
    """N = M q^e pseudoperfect iff r = sigma(N)-2N = sum_{i<=e} q^i s_i with s_i in SS(div M) for
    i<e and s_e in P(M). Exact DFS from the lowest digit (branching capped: incomplete => False)."""
    sigma=ps[2]+M; N=M*q**e; r=sigma*sig(q,e)-2*N
    budget=[5000]
    def go(x,i):
        if budget[0]<=0: return False
        budget[0]-=1
        if i==e: return inP(x,ps)
        s0=x%q
        while s0<=min(x,sigma):
            if inQ(s0,M,ps) and go((x-s0)//q,i+1): return True
            s0+=q
            if budget[0]<=0: return False
        return False
    return go(r,0)
def primes_in(lo,hi):
    q=lo|1
    while q<=hi:
        if isprime(q): yield q
        q+=2
def family(f,M,sigma,un,ud,q0):
    st["fam"]+=1
    D=2*M-sigma
    if un>=2*ud: return False
    ps=Pstruct(f,M,sigma)
    if ps is None: st["fail"].append(("nostruct",f)); return False
    B,c,sp=ps
    qtop=sigma//D  # Mq abundant iff q*D <= sigma ... strictly: sigma(q+1) >= 2Mq  <=> q D <= sigma
    if q0<=qtop:
        if c is None: wins=[(q0,qtop)]
        else:
            L=C  # beyond bits we know membership exactly anyway; bad x only within C of boundaries
            # Dq in P-region safe if C<=Dq<=sp-C ; Dq-M safe if C<=Dq-M<=sp-C
            wins=[(q0,min(qtop,L//D+1)),((sp-L)//D,(M+L)//D+1),((sigma-L)//D,qtop)]
        seen=set()
        for lo,hi in wins:
            for q in primes_in(max(lo,q0),min(hi,qtop)):
                if q in seen: continue
                seen.add(q); st["qchk"]+=1
                if not pp_Mq(q,M,D,ps):
                    st["fail"].append(("Mq",f,q)); return False
    # primes q>qtop (Mq not abundant) with U q/(q-1) >= 2: go through the exponents of q
    if un>=2*ud: return False
    q=max(q0,qtop+1)
    while True:
        if un*q<2*ud*(q-1): return True
        if q>qtop+WIN: return False
        if isprime(q):
            st["star"]+=1
            e=1
            while True:
                s_,pe=sig(q,e),q**e
                if sigma*s_>=2*M*pe:
                    if not pp_Mqe(q,e,M,ps,f):
                        st["fail"].append(("star",f,q,e)); return False
                    break
                if un*s_>=2*ud*pe or e>200: return False
                e+=1
        q+=2

def search(f,M,sigma,un,ud,j,q0):
    st["n"]+=1
    if st["n"]%200000==0: print("progress", st["n"], st["fam"], round(time.time()-t), f, file=sys.stderr, flush=True)
    if sigma>=2*M: return True
    if j==0: return un<2*ud
    if j==1: return family(f,M,sigma,un,ud,q0)
    q=q0
    while True:
        a,b=un,ud
        for i in range(j): a*=q+2*i; b*=q+2*i-1
        if a<2*b: return True
        if isprime(q):
            e=1
            while True:
                s=sig(q,e); pe=q**e
                an,ad=un*q,ud*(q-1); g=gcd(an,ad)
                if search(f+[(q,e)],M*pe,sigma*s,an//g,ad//g,j-1,q+2): break
                bn,bd=un*s,ud*pe; g=gcd(bn,bd)
                if not search(f+[(q,e)],M*pe,sigma*s,bn//g,bd//g,j-1,q+2):
                    return False
                e+=1
        q+=2
t=time.time()
k=int(sys.argv[1]); t=time.time()
ok=search([],1,1,1,1,k,3)
print(k,ok,{x:y for x,y in st.items() if x!="fail"},round(time.time()-t,1))
for x in st["fail"][:20]: print(x)
