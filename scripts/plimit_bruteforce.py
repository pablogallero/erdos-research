# Session 74 (notes/erdos-470.md): brute-force cross-check of plimit_probe.py's coverage on 3^17*5^2*43^2 (p <= 61,
# q < 400, f, e <= FE, r < 4000): every abundant n p^f q^e r must have its own interval certificate, or its r-free prefix
# n p^f q^e certified (abOK, or deficient + lastOK). Session 74: FE = 8, 12.4M points, 3710 abundant, 0 uncovered (~5 min).
# Usage: python3 -I scripts/plimit_bruteforce.py [FE]. Python only; decides nothing about #470.
import os, sys
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
FE = int(sys.argv[1]) if len(sys.argv) > 1 else 8
sys.argv = ['x']
import plimit_probe as PL, subok_cost_probe as SP
n,S,c,g = 5969504034675, 5397994213977, 37, 2
C = PL.Ctx(n,S,c,g)
isp = PL.isprime
def ab(parts):
    N,T,ok = PL.chain(C, parts); return ok and c<=N and N+c<=T
def covered_prefix(parts):  # r free: abOK or deficient+lastOK
    N,T,ok = PL.chain(C, parts)
    if ok and c<=N and N+c<=T: return True
    if T < N and ok:
        return SP.lastOK(N,T,c,g,(N+T)//(N-T)+1)[0]
    return False
abund=bad=tot=0; cache={}
for p in [47,53,59,61]:
  for q in range(p+2, 400, 2):
    if not isp(q): continue
    for f in range(1,FE+1):
      for e in range(1,FE+1):
        key=(p,f,q,e); pc=covered_prefix([(p,f),(q,e)])
        N0,T0,_=PL.chain(C,[(p,f),(q,e)])
        for r in range(q+2, 4000, 2):
          if not isp(r): continue
          tot+=1
          N=N0*r; Tn=(T0+N0)*(r+1)-N  # sum of proper divisors
          if Tn <= N: continue
          abund+=1
          if pc or ab([(p,f),(q,e),(r,1)]): continue
          bad+=1
          if bad<10: print('UNCOVERED abundant', p,f,q,e,r)
print('points',tot,'abundant',abund,'uncovered',bad)
