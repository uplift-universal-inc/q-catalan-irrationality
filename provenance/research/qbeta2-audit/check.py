"""Independent sign/functional and numerical-tail checks for step-2 q-beta(2).
The exact entry construction is copied from the proposer; the direct functional,
positive-series target enclosure, leading-sign test, and determinant comparisons
below are separate checks, not an all-size proof.
"""
from pathlib import Path
import sys,json,math,time
sys.path.insert(0,str(Path(__file__).resolve().parent/'source'))
from step2 import entries
from flint import fmpq_mat,fmpz_poly,fmpq,arb,ctx

def target(p,prec):
    ctx.prec=prec
    N=math.ceil((prec+64)*math.log(2)/math.log(p))+64
    q=arb(1)/p; x=q; val=arb(0)
    for n in range(1,N+1):
        val+=n*x/(1+x*x)
        x*=q
    rho=q*arb(N+2)/arb(N+1)
    assert rho<1
    tail=(N+1)*x/(1-rho)
    return val+arb(0,tail),N,tail

def direct_entries(p,K,prec=768):
    ctx.prec=prec
    q=arb(1)/p
    N=math.ceil((prec+128)*math.log(2)/math.log(p))+64
    vals=[arb(0) for k in range(2*K-1)]
    x=q
    for m in range(1,N+1):
        if m%2:
            W=arb(1);alpha=arb(0)
            for a in range(1,K+1):
                y=x*q**(2*a)
                W/=1-y;alpha+=y/(1-y)
            power=arb(1)
            sign=1 if m%4==1 else -1
            for k in range(2*K-1):
                vals[k]+=sign*power*W*(k+alpha)
                power*=x
        x*=q
    # W<=2 and theta(log W)<=x for p>=2 on [0,q].
    # Hence abs theta(x^k W)<=2(k+1)q^m, including k=0.
    for k in range(len(vals)):
        vals[k]+=arb(0,2*(k+1)*x/(1-q))
    return vals

def audit_poly(p,K):
    t=time.time();aa,bb=entries(p,K,2)
    A=fmpq_mat(K,K,[aa[i+j] for i in range(K) for j in range(K)])
    B=fmpq_mat(K,K,[bb[i+j] for i in range(K) for j in range(K)])
    pol=(-(B.inv()*A)).charpoly()*B.det()
    assert pol[K]==(-1)**K*fmpq(p)**(K*(K*K-1))
    for X in [fmpq(0),fmpq(1),fmpq(2,3)]:
        assert (A+B*X).det()==pol(X)
    den=math.lcm(*(int(c.q) for c in pol));ints=[int(c.p)*(den//int(c.q)) for c in pol]
    con=math.gcd(*ints);P=fmpz_poly([c//con for c in ints])
    assert math.gcd(*(int(c) for c in P))==1
    bits=max(abs(int(c)).bit_length() for c in P)
    prec=bits+16*K*K+512
    z,N,tail=target(p,prec)
    val=arb(0)
    for c in reversed(list(P)):val=val*z+int(c)
    assert not val.contains(0),(p,K)
    row=dict(p=p,K=K,leading_sign_correct=True,primitive=True,nonzero_certified=True,
       precision=prec,target_terms=N,tail_bound=tail.str(20),value=val.str(30),logabs=float(abs(val).log()),seconds=time.time()-t)
    return row

def main():
    functional_count=0
    for p in [2,3,4,6]:
        for K in range(1,7):
            aa,bb=entries(p,K,2)
            z,_,_=target(p,768)
            direct=direct_entries(p,K,768)
            for k,actual in enumerate(direct):
                formal=arb(aa[k])+arb(bb[k])*z
                assert formal.overlaps(actual),(p,K,k)
                functional_count+=1
    rows=[]
    for p,K in [(2,2),(2,4),(2,8),(2,12),(2,16),(3,4),(3,8),(3,12),(4,4),(4,8),(6,4),(6,8)]:
        row=audit_poly(p,K);rows.append(row);print(json.dumps(row),flush=True)
    result={'status':'passed','independent_direct_functional_entry_checks':functional_count,'target_method':'positive series sum n p^n/(p^(2n)+1), with explicit geometric-ratio tail','primitive_cases':rows}
    Path(__file__).with_name('checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print('passed',functional_count,'functional entries and',len(rows),'primitive cases')
if __name__=='__main__':main()
