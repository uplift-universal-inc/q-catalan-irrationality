"""Direct analytic-functional checks for the renormalized mixed target."""
from pathlib import Path
import sys,json,math
sys.path.insert(0,str(Path(__file__).resolve().parent/'source'))
from mixed_exact import moments
from flint import arb,ctx

def frac_arb(x):return arb(x.numerator)/x.denominator

def target(p,A,B,prec):
    ctx.prec=prec;q=arb(1)/p
    N=math.ceil((prec+128)*math.log(2)/math.log(p))+64
    x=q;total=arb(0)
    for n in range(1,N+1):
        total+=(A+B*n)*x/(1+x*x);x*=q
    rho=q*arb(N+2)/arb(N+1)
    tail=abs(A)*x/(1-q)+abs(B)*(N+1)*x/(1-rho)
    return total+arb(0,tail),N

def direct(p,K,A,B,prec):
    ctx.prec=prec;q=arb(1)/p
    N=math.ceil((prec+128)*math.log(2)/math.log(p))+64
    x=q;out=[arb(0) for _ in range(2*K-1)]
    for m in range(1,N+1):
        if m%2:
            W=arb(1);alpha=arb(0)
            for a in range(1,K+1):
                y=x*q**(2*a);W/=1-y;alpha+=y/(1-y)
            power=arb(1);sign=1 if m%4==1 else -1
            for k in range(2*K-1):
                f=power*W
                out[k]+=sign*(A*(f-(1 if k==0 else 0))+B*f*(k+alpha))
                power*=x
        x*=q
    for k in range(len(out)):
        out[k]+=arb(0,2*(abs(A)+abs(B))*(k+1)*x/(1-q))
    return out

rows=[];total=0
for p in [2,3]:
    for A,B in [(2,0),(2,-2),(2,3),(-2,1)]:
        for K in range(1,5):
            formal=moments(p,K,A,B)
            z,N=target(p,A,B,768)
            actual=direct(p,K,A,B,768)
            for k,(linear,constant) in enumerate(formal):
                pred=frac_arb(linear)*z+frac_arb(constant)
                assert pred.overlaps(actual[k]),(p,A,B,K,k)
                total+=1
            rows.append(dict(p=p,A=A,B=B,K=K,entry_count=2*K-1,passed=True))
result=dict(status='passed',entry_checks=total,cases=rows,scope='independent direct evaluation of renormalized functional and mixed positive/negative series target; finite consistency checks only')
Path(__file__).with_name('mixed_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status='passed',entry_checks=total,cases=len(rows))))
