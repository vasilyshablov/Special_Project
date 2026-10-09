import sys, subprocess, math, networkx as nx
from fractions import Fraction as F
from functools import lru_cache
from math import ceil, floor, isqrt

def invariants(G):
    n=G.number_of_nodes(); V=list(range(n))
    adj=[0]*n
    for u,v in G.edges(): adj[u]|=1<<v; adj[v]|=1<<u
    pc=lambda m: bin(m).count('1')
    def indep(mask):
        best=0; sub=mask
        # enumerate subsets of mask
        s=mask
        while True:
            ok=True; t=s
            while t:
                i=(t&-t).bit_length()-1; t&=t-1
                if adj[i]&s: ok=False;break
            if ok: best=max(best,pc(s))
            if s==0: break
            s=(s-1)&mask
        return best
    full=(1<<n)-1
    alpha=indep(full)
    L=[indep(adj[v]) for v in V]
    def edges_in(s): return sum(pc(adj[i]&s) for i in V if s>>i&1)//2
    def connected(s):
        if s==0: return True
        start=s&-s; seen=start; fr=start
        while fr:
            i=(fr&-fr).bit_length()-1; fr&=fr-1
            nb=adj[i]&s&~seen; seen|=nb; fr|=nb
        return seen==s
    def bipartite(s):
        col={}
        for st in V:
            if not s>>st&1 or st in col: continue
            col[st]=0; stack=[st]
            while stack:
                i=stack.pop()
                for j in V:
                    if s>>j&1 and adj[i]>>j&1:
                        if j not in col: col[j]=1-col[i]; stack.append(j)
                        elif col[j]==col[i]: return False
        return True
    def forest(s):
        # acyclic iff edges = vertices - components
        comps=0; seen=0
        for st in V:
            if s>>st&1 and not seen>>st&1:
                comps+=1; c=1<<st; fr=c
                while fr:
                    i=(fr&-fr).bit_length()-1; fr&=fr-1
                    nb=adj[i]&s&~c; c|=nb; fr|=nb
                seen|=c
        return edges_in(s)==pc(s)-comps
    b=f=pth=0
    for s in range(1<<n):
        k=pc(s)
        if k>b and bipartite(s): b=k
        if k>f and forest(s): f=k
        if k>pth and connected(s) and edges_in(s)==k-1 and all(pc(adj[i]&s)<=2 for i in V if s>>i&1): pth=k
    # hamiltonian path in G[s] DP
    ham=[[False]*n for _ in range(1<<n)]
    for i in V: ham[1<<i][i]=True
    for s in range(1,1<<n):
        for i in V:
            if ham[s][i]:
                nb=adj[i]&~s
                while nb:
                    j=(nb&-nb).bit_length()-1; nb&=nb-1
                    ham[s|1<<j][j]=True
    hp=[any(ham[s]) for s in range(1<<n)]
    # path cover number: min partition into sets with hp
    INF=99; pcn=[INF]*(1<<n); pcn[0]=0
    for s in range(1,1<<n):
        low=s&-s; rest=s^low; t=rest
        while True:
            part=t|low
            if hp[part] and pcn[s^part]+1<pcn[s]: pcn[s]=pcn[s^part]+1
            if t==0: break
            t=(t-1)&rest
    D=dict(nx.all_pairs_shortest_path_length(G))
    ecc=[max(D[v].values()) for v in V]
    deg=[pc(adj[v]) for v in V]
    # residue
    seq=sorted(deg,reverse=True)
    while seq and seq[0]>0:
        d=seq.pop(0)
        seq=[x-1 if i<d else x for i,x in enumerate(seq)]
        seq.sort(reverse=True)
    res=len(seq)
    c4=any(1 for _ in [0]) and has_c4(adj,n)
    return dict(n=n,alpha=alpha,L=L,b=b,f=f,path=pth,hampath=hp[full],pcn=pcn[full],ecc=ecc,
                rad=min(ecc),diam=max(ecc),deg=deg,res=res,c4=c4)
def has_c4(adj,n):
    for a in range(n):
        for c in range(a+1,n):
            if bin(adj[a]&adj[c]).count('1')>=2: return True
    return False

def check(G):
    I=invariants(G); n=I['n']; out=[]
    maxL=max(I['L']); lavg=F(sum(I['L']),n); eccavg=F(sum(I['ecc']),n)
    # 100: alpha <= ceil((maxL + 0.5*sqrt(S))/2), S = sum of complement degree squares
    S=sum((n-1-d)**2 for d in I['deg'])
    rhs=ceil((maxL+0.5*math.sqrt(S))/2-1e-12)
    if I['alpha']>rhs: out.append(('100',I['alpha'],rhs))
    # 133: rad + lavg^cC4 <= path
    lhs=I['rad']+(1 if I['c4'] else lavg)
    if lhs>I['path']: out.append(('133',lhs,I['path']))
    # 19: floor(eccavg + maxL) <= b
    if floor(eccavg+maxL)>I['b']: out.append(('19',floor(eccavg+maxL),I['b']))
    # 198a
    if I['b']<=2+eccavg and not I['hampath']: out.append(('198a',I['b'],eccavg))
    # 40
    if n>1 and ceil(F(I['pcn']+I['b']+1,2))>I['f']: out.append(('40',I['pcn'],I['b'],I['f']))
    # 61
    if I['res']+ceil(F(I['diam'],3))>I['f']: out.append(('61',I['res'],I['diam'],I['f']))
    return out

if __name__=='__main__':
    n=int(sys.argv[1])
    p=subprocess.Popen(['nauty-geng','-cq',str(n)],stdout=subprocess.PIPE,text=True)
    cnt=0; found={}
    for line in p.stdout:
        G=nx.from_graph6_bytes(line.strip().encode()); cnt+=1
        for r in check(G):
            if r[0] not in found:
                found[r[0]]=(line.strip(),r); print("COUNTEREXAMPLE",r,line.strip(),flush=True)
    print(n,"graphs:",cnt,"violated:",sorted(found))
