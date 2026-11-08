"""Node count of the `fchk` search (ErdosResearch/UnitaryPerfectSixOdd.lean), in Python.

Usage: python3 -I scripts/upn_search_hybrid.py K [A0]

Searches UPNs n = 2^a * q1 * ... * qK (odd, sorted, pairwise coprime q's) as `fchk` does:
"free" state (2^a not placed yet, 2^a >= max(L, 2^A0), A0 = K-1 by default from the 2-adic
bound), "placed" state (exact target, stride 2 on odd values; in Lean this is `upnCheck`), and
the last odd variable with 2^a still free solved by a loop over the powers of two.
Prints K, {nodes, loop iterations, max depth, solutions (sorted factor lists)}, seconds.
Measured: K=4: 33 nodes, finds [3,5,7,13,64] (87360); K=5: 137 nodes; K=6: 5447 nodes + 7779
loop steps, none; K=7: 12.9M nodes (8.6M in "placed" with two odd variables left), none.
With A0 = 1 (no 2-adic bound): K=6 needs 11.9M nodes.
"""
import sys,time
from math import gcd
def asc2(L,r):
    p=1
    for j in range(r): p*=L+2*j
    return p
def ispow2(x): return x>0 and x&(x-1)==0
k=int(sys.argv[1]); A0=int(sys.argv[2]) if len(sys.argv)>2 else k-1
st={'n':0,'it':0,'d':0,'sol':[]}
def placed(P,Q,L,pre,r,d,path):
    while True:
        st['n']+=1; st['d']=max(st['d'],d)
        if 2*P<=Q: return
        if r==1:
            dd=2*P-Q
            if Q%dd==0:
                y=Q//dd
                if y>=L and all(gcd(y,p)==1 for p in pre): st['sol'].append(path+[y])
            return
        if Q*asc2(L+1,r) < 2*P*asc2(L,r): return
        if all(gcd(L,p)==1 for p in pre):
            placed(P*L,Q*(1+L),L+2,pre+[L],r-1,d+1,path+[L])
        L+=2; d+=1
def free(P,Q,L,pre,r,d,path):
    while True:
        st['n']+=1; st['d']=max(st['d'],d)
        if 2*P<=Q: return
        if r==0:
            dd=2*P-Q
            if Q%dd==0:
                y=Q//dd
                if y>=L and ispow2(y): st['sol'].append(path+[y])
            return
        if r==1:
            B=3*Q//(2*P-Q)
            E=1
            while E<=Q*(1+B):
                st['it']+=1
                den=2*P*E-Q*(1+E)
                if den>0 and (Q*(1+E))%den==0:
                    y=Q*(1+E)//den
                    if y>=L and E>=L and all(gcd(y,p)==1 for p in pre):
                        st['sol'].append(path+sorted([y,E]))
                E*=2
            return
        Lo=L|1
        E=max(L,2**A0)
        if Q*asc2(Lo+1,r)*(E+1) < 2*P*asc2(Lo,r)*E: return
        if L%2==1:
            if all(gcd(L,p)==1 for p in pre):
                free(P*L,Q*(1+L),L+1,pre+[L],r-1,d+1,path+[L])
        elif ispow2(L) and L>=2**A0:
            placed(P*L,Q*(L+1),L+1,pre,r,d+1,path+[L])
        L+=1; d+=1
sys.setrecursionlimit(10**6)
T=time.time()
free(1,1,2,[2],k,0,[])
print(k,st,time.time()-T,flush=True)
