from flint import fmpq,fmpq_poly,fmpq_mat,fmpz_poly,arb,ctx
import math,json,time,sys
from costs import denominator_check
from pathlib import Path

def chi(n):return 0 if n%2==0 else 1 if n%4==1 else -1

def entries(p,K):
 q=fmpq(1,p); S={}; acc=fmpq(0)
 for n in range(1,4*K+1):
  y=q**n
  acc+=chi(n)*y/(1-y)**2
  if n%4==0:S[n//4]=acc
 poles=[fmpq(p)**(4*a) for a in range(1,K+1)]
 D=fmpq_poly([1])
 for r in poles:D*=fmpq_poly([1,-1/r])
 base=[]
 for a,r in enumerate(poles):
  den=fmpq(1)
  for b,t in enumerate(poles):
   if a!=b:den*=1-r/t
  base.append(1/den)
 aa=[];bb=[]
 for k in range(2*K-1):
  Q=fmpq_poly([0]*k+[1])//D
  A=sum((Q[j]*j*fmpq(p)**j/(fmpq(p)**(2*j)+1) for j in range(1,Q.degree()+1)),fmpq(0))
  B=fmpq(0)
  for a,r in enumerate(poles):
   c=base[a]*r**k
   A-=c*S[a+1];B+=c
  aa.append(A);bb.append(B)
 return aa,bb

def enclosure(p,prec):
 ctx.prec=prec
 N=math.ceil((prec+64)*math.log(2)/math.log(p))+128
 sig=[0]*(N+1)
 for d in range(1,N+1):
  for n in range(d,N+1,d):sig[n]+=d*chi(n//d)
 total=0
 for n in range(1,N+1):total=p*total+sig[n]
 value=arb(total)/arb(p)**N
 rho=(arb(N+2)/arb(N+1))**2/p
 tail=arb(N+1)**2*arb(p)**(-N-1)/(1-rho)
 return value+arb(0,tail),N,tail

def audit(p,K):
 t=time.time();aa,bb=entries(p,K)
 A=fmpq_mat(K,K,[aa[i+j] for i in range(K) for j in range(K)])
 B=fmpq_mat(K,K,[bb[i+j] for i in range(K) for j in range(K)])
 D=(-(B.inv()*A)).charpoly()*B.det()
 den=math.lcm(*(int(c.q) for c in D)); integer=[int(c.p)*(den//int(c.q)) for c in D];con=math.gcd(*integer)
 assert denominator_check(p,K,den),(p,K,"improved denominator failed")
 P=fmpz_poly([c//con for c in integer]); bits=max(abs(int(c)).bit_length() for c in P)
 assert D[K]==(-1)**(K*(K-1)//2)*fmpq(p)**(2*K*(K*K-1))
 prec=bits+16*K*K+256
 z,N,tail=enclosure(p,prec)
 val=arb(0)
 for c in reversed(list(P)):val=val*z+int(c)
 assert not val.contains(0)
 return dict(p=p,K=K,degree=P.degree(),nonzero_certified=True,precision_bits=prec,terms=N,tail_bound=tail.str(18),target=z.str(24),value=val.str(24),logabs=float(abs(val).log()),logabs_K3=float(abs(val).log())/K**3,logden_K3=math.log(den)/K**3,logcontent_K3=math.log(con)/K**3,seconds=time.time()-t)
if __name__=='__main__':
 with Path(__file__).with_name('scan.jsonl').open('w') as h:
  for K in [2,4,8,12,16,24,32]:
   r=audit(2,K);h.write(json.dumps(r)+'\n');h.flush();print(json.dumps(r),flush=True)
