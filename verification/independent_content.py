from fractions import Fraction as F
from pathlib import Path
import math,json

def mul(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for i,u in enumerate(a):
        for j,v in enumerate(b):out[i+j]+=u*v
    return out

def quo_xk(k,D):
    rem=[F(0)]*k+[F(1)]; K=len(D)-1
    if k<K:return []
    out=[F(0)]*(k-K+1)
    for n in range(k,K-1,-1):
        c=rem[n]/D[-1];out[n-K]=c
        for j,v in enumerate(D):rem[n-K+j]-=c*v
    return out

def det(A):
    A=[r[:] for r in A]; out=F(1); n=len(A)
    for i in range(n):
      z=next((j for j in range(i,n) if A[j][i]),None)
      if z is None:return F(0)
      if z!=i:A[i],A[z]=A[z],A[i];out=-out
      v=A[i][i];out*=v
      for j in range(i+1,n):
        c=A[j][i]/v
        for k in range(i+1,n):A[j][k]-=c*A[i][k]
        A[j][i]=F(0)
    return out

def interpolate(vals):
    n=len(vals); diff=vals[:]; coeff=[]
    for i in range(n):
        coeff.append(diff[0]);diff=[b-a for a,b in zip(diff,diff[1:])]
    result=[F(0)]*n; basis=[F(1)]
    for k,c in enumerate(coeff):
        for j,v in enumerate(basis):result[j]+=c*v
        basis=[v/F(k+1) for v in mul(basis,[F(-k),F(1)])]
    return result

def chi(n):return 0 if n%2==0 else 1 if n%4==1 else -1

def moments(p,K):
    nodes=[p**(2*a) for a in range(1,K+1)]
    D=[F(1)]
    for y in nodes:D=mul(D,[F(1),-F(1,y)])
    S=[];v=F(0)
    for b in range(1,2*K+1):
        v+=chi(b)*F(p**b,(p**b-1)**2)
        if b%2==0:S.append(v)
    ans=[]
    for k in range(2*K-1):
        quo=quo_xk(k,D)
        constant=sum((c*F(j*p**j,p**(2*j)+1) for j,c in enumerate(quo) if j),F(0));linear=F(0)
        for i,y in enumerate(nodes):
            der=-F(1,y)
            for j,t in enumerate(nodes):
                if i!=j:der*=1-F(y,t)
            pole=-F(y**k,y)/der
            signed=(-1)**(i+1)*pole
            linear+=signed;constant-=signed*S[i]
        ans.append((linear,constant))
    return ans

def vp(x,p):
    if x==0:return math.inf
    x=abs(x);ans=0
    while x%p==0:ans+=1;x//=p
    return ans

def primes(n):
    return [p for p in range(2,n+1) if n%p==0 and all(p%d for d in range(2,math.isqrt(p)+1))]

rows=[]
for p in (2,3,4,6):
    for K in range(1,11):
        M=moments(p,K)
        vals=[det([[M[i+j][0]*u+M[i+j][1] for j in range(K)] for i in range(K)]) for u in range(K+1)]
        poly=interpolate(vals)
        E=K*K*(K+1)-sum(max(K-2*i,0)*(max(K-2*i,0)+1) for i in range(K))
        assert E==(10*K**3+3*K*K-10*K-3*(K%2))//12
        assert poly[-1]==(-1)**K*p**(K*(K*K-1))
        local=[]
        for ell in primes(p):
            r=vp(p,ell)
            v=min(vp(c.numerator,ell)-vp(c.denominator,ell) for c in poly)
            assert v>=r*E,(p,K,ell,v,E)
            local.append({'prime':ell,'actual_min_coefficient_valuation':v,'proved_lower_bound':r*E})
        rows.append({'p':p,'K':K,'E_K':E,'leading_coefficient_matches':True,'local':local})
result={'status':'all passed','scope':'Independent finite exact consistency evidence for the all-index proof.','cases':len(rows),'rows':rows}
(Path(__file__).resolve().parents[1]/'certificates/content-replay.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'all passed','cases':len(rows)}))
