"""Generate the Lean case tree for Erdős #1052 (unitary perfect numbers).

Usage: python3 -I scripts/upn_case_tree.py M TARGET SPLIT > out.lean

Proves: if 1 < y1 < ... < yM are pairwise coprime and prod(1 + yi) = 2 prod(yi), then
prod(yi) = TARGET (TARGET = 0 if there is no coprime solution). Nodes at depth SPLIT become
separate lemmas (heartbeat limit). Output is the body of the "Generated" section in
ErdosResearch/UnitaryPerfectFourOdd.lean (M = 5, TARGET = 87360, SPLIT = 2).

Each node: if the remaining product cannot reach the target ratio, `linarith`/`omega`;
for the last variable the equation is linear, so `omega`; otherwise find the least B for which
shifting all remaining variables to B, B+1, ... gives a polynomial 2*prod(y) - prod(1+y) with
nonnegative coefficients and positive constant (closed by `linarith` with monomial hints), and
enumerate the values below B, pruning those sharing a factor with an earlier variable.
"""
import sys, itertools
from math import prod, gcd
def ok(A,C,bs):
    n=len(bs)
    for r in range(n+1):
        for S in itertools.combinations(range(n),r):
            rest=[bs[j] for j in range(n) if j not in S]
            c=A*prod(rest)-C*prod(1+b for b in rest)
            if c<0 or (r==0 and c<=0): return False
    return True
def findB(A,C,m,L):
    # lower bounds for remaining m vars: L, L+1, ... (mixed parity: conservative step 1)
    f=lambda b: ok(A,C,[b+j for j in range(m)])
    if f(L): return L
    lo,hi=L,L+1
    while not f(hi): lo,hi=hi,L+2*(hi-L)
    while hi-lo>1:
        mid=(lo+hi)//2
        if f(mid): hi=mid
        else: lo=mid
    return hi

def wrap(l, W=100):
    if len(l)<=W: return [l]
    ind=len(l)-len(l.lstrip())
    toks=l.strip().split(' ')
    out=[]; cur=' '*ind
    first=True
    for t in toks:
        if len(cur)+1+len(t)>W and cur.strip():
            out.append(cur.rstrip()); cur=' '*(ind+4)
        cur+=('' if cur.strip()=='' else ' ')+t
    out.append(cur)
    return out

m=int(sys.argv[1]); TARGET=int(sys.argv[2]); SPLIT=int(sys.argv[3]); subs=[]
Y=[f'y{i+1}' for i in range(m)]
Z=[f'z{i+1}' for i in range(m)]
def hints(names):
    hs=[f'Nat.zero_le ({" * ".join(S)})' for r in range(2,len(names)+1) for S in itertools.combinations(names,r)]
    return ' ['+', '.join(hs)+']' if hs else ''
def bound(ind, lvl, B):
    out=[]
    for j in range(lvl,m):
        b=B+(j-lvl)
        out.append(ind+f'obtain ⟨{Z[j]}, rfl⟩ : ∃ z, {Y[j]} = z + {b} := ⟨{Y[j]} - {b}, by omega⟩')
    out.append(ind+'linarith'+hints(Z[lvl:]))
    return out
def bullet(lines, ind):
    lines[0]=ind+'· '+lines[0][len(ind)+2:]
    return lines
stat={'n':0}
def rec(A,C,lvl,L,path,ind, top=False):
    stat['n']+=1
    if lvl==SPLIT and not top:
        name=f'arith_sorted_{m}_'+'_'.join(map(str,path))
        subs.append((name,path,rec(A,C,lvl,L,path,'  ',top=True)))
        return [ind+f'exact {name} '+' '.join(ALLH)+' '+' '.join(['rfl']*len(path))]
    rem=m-lvl
    if A<=C:
        if rem==1: return [ind+'omega']
        return [ind+'linarith'+hints(Y[lvl:])]
    if rem==1:
        if C%(A-C)==0 and C//(A-C)>=L:
            y=C//(A-C); bad=[j for j,z in enumerate(path) if gcd(y,z)>1]
            out=[ind+f'obtain rfl : {Y[lvl]} = {y} := by omega']
            if bad: out.append(ind+f'norm_num at c{bad[0]+1}_{lvl+1}')
            else:
                assert prod(path)*y==TARGET, path+[y]
                out.append(ind+'exact hne (by norm_num)')
            return out
        return [ind+'omega']
    B=findB(A,C,rem,L)
    vals=list(range(L,B))
    out=[]
    if vals:
        alts=' ∨ '.join([f'{Y[lvl]} = {v}' for v in vals]+[f'{B} ≤ {Y[lvl]}'])
        out.append(ind+f'rcases (show {alts} by omega) with '+' | '.join(['rfl']*len(vals)+['hb']))
        for v in vals:
            bad=[j for j,z in enumerate(path) if gcd(v,z)>1]
            if bad: out.append(ind+f'· norm_num at c{bad[0]+1}_{lvl+1}')
            else: out+=bullet(rec(A*v,C*(1+v),lvl+1,v+1,path+[v],ind+'  '),ind)
        out+=bullet(bound(ind+'  ',lvl,B),ind)
    else:
        out+=bound(ind,lvl,B)
    return out
hyps=[f'(hlt{i+1} : {Y[i]} < {Y[i+1]})' for i in range(m-1)]
cops=[f'(c{i+1}_{j+1} : Nat.Coprime {Y[i]} {Y[j]})' for i in range(m) for j in range(i+1,m)]
ALLH=['h1']+[x.split(' ')[0][1:] for x in hyps+cops]+['h','hne']
body=rec(2,1,0,2,[],'  ')
args=' '.join(Y)
def header(name, extra, concl):
    print(f'lemma {name} {{{args} : ℕ}} (h1 : 1 < y1)')
    cur='   '
    for hy in hyps+cops:
        if len(cur)+len(hy)+1>98: print(cur); cur='   '
        cur+=' '+hy
    print(cur)
    print(f'    (h : {" * ".join(f"(1 + {y})" for y in Y)} =')
    for l in wrap(f'      2 * {" * ".join(Y)})'+extra+' :'): print(l)
    print(f'    {concl} := by')
for name,path,b in subs:
    ex=f' (hne : ¬{" * ".join(Y)} = {TARGET})'+''.join(f' (e{i+1} : {Y[i]} = {v})' for i,v in enumerate(path))
    header(name, ex, 'False')
    print('  '+' '.join(['subst']+[f'e{i+1}' for i in range(len(path))]))
    print('\n'.join(l2 for l in b for l2 in wrap(l))); print()
hyps=[f'(hlt{i+1} : {Y[i]} < {Y[i+1]})' for i in range(m-1)]
cops=[f'(c{i+1}_{j+1} : Nat.Coprime {Y[i]} {Y[j]})' for i in range(m) for j in range(i+1,m)]
print(f'lemma arith_sorted_{m} {{{args} : ℕ}} (h1 : 1 < y1)')
cur='   '
for hy in hyps+cops:
    if len(cur)+len(hy)+1>98: print(cur); cur='   '
    cur+=' '+hy
print(cur)
print(f'    (h : {" * ".join(f"(1 + {y})" for y in Y)} =')
print(f'      2 * {" * ".join(Y)}) :')
print(f'    {" * ".join(Y)} = {TARGET} := by')
print('  by_contra hne')
print('\n'.join(l2 for l in body for l2 in wrap(l)))
print('-- nodes',stat['n'],file=sys.stderr)
