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

def moments(p,K,A,B):
    nodes=[p**(2*a) for a in range(1,K+1)]
    D=[F(1)]
    for y in nodes:D=mul(D,[F(1),-F(1,y)])
    S=[];v=F(0)
    for b in range(1,2*K+1):
        v+=chi(b)*(A*F(1,p**b-1)+B*F(p**b,(p**b-1)**2))
        if b%2==0:S.append(v)
    ans=[]
    for k in range(2*K-1):
        quo=quo_xk(k,D)
        constant=sum((c*F((A+B*j)*p**j,p**(2*j)+1) for j,c in enumerate(quo) if j),F(0));linear=F(0)
        for i,y in enumerate(nodes):
            der=-F(1,y)
            for j,t in enumerate(nodes):
                if i!=j:der*=1-F(y,t)
            pole=-F(y**k,y)/der
            signed=(-1)**(i+1)*pole
            linear+=signed;constant-=signed*S[i]
        ans.append((linear,constant))
    return ans

def cost(K,d):
    if d%2:
        if d<=K:
            r,t=divmod(K,d)
            f=lambda m:((m+2)**2)//4 if m else 0
            return t*f(r+1)+(d-t)*f(r)
        if d<=2*K:return 2*(K-(d-1)//2)
        return 0
    if d%4==2:
        h=d//2
        return sum(max(K-a*h,0) for a in range(1,K//h+1,2))
    u=d//4
    return min(K,max(K-2*u,0)+max(K-u-1,0))

rows=[]
for p in (2,3,4,6):
    phi={}
    for d in range(1,25):phi[d]=(p**d-1)//math.prod(phi[j] for j in range(1,d) if d%j==0)
    for A,B in ((2,1),(2,-1),(2,0),(0,1),(4,3)):
        for K in range(1,7):
            M=moments(p,K,A,B)
            vals=[det([[M[i+j][0]*u+M[i+j][1] for j in range(K)] for i in range(K)]) for u in range(K+1)]
            poly=interpolate(vals)
            E=(10*K**3+3*K*K-10*K-3*(K%2))//12
            C=math.prod(phi[d]**cost(K,d) for d in range(1,4*K+1))
            assert poly[-1]==(-1)**K*p**(K*(K*K-1))
            assert all((c*C/p**E).denominator==1 for c in poly),(p,A,B,K)
            rows.append({'p':p,'A':A,'B':B,'K':K,'normalized_coefficients_integral':True,'leading_coefficient_matches':True})
result={'status':'all passed','scope':'Independent exact arithmetic corroboration; all-index proof in MIXTURE_EXTENSION.md.','cases':len(rows),'rows':rows}
Path(__file__).with_name('checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'all passed','cases':len(rows)}))
