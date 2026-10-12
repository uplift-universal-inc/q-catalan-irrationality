from step2 import entries
from scan import enclosure
from flint import fmpq_mat,fmpz_poly,arb
from pathlib import Path
import math,time,json

def audit(p,K):
 t=time.time();aa,bb=entries(p,K,2)
 A=fmpq_mat(K,K,[aa[i+j] for i in range(K) for j in range(K)])
 B=fmpq_mat(K,K,[bb[i+j] for i in range(K) for j in range(K)])
 D=(-(B.inv()*A)).charpoly()*B.det()
 den=math.lcm(*(int(c.q) for c in D));cs=[int(c.p)*(den//int(c.q)) for c in D];con=math.gcd(*cs)
 P=fmpz_poly([c//con for c in cs]); bits=max(abs(int(c)).bit_length() for c in P);prec=bits+16*K*K+256
 z,N,tail=enclosure(p,prec);val=arb(0)
 for c in reversed(list(P)):val=val*z+int(c)
 assert not val.contains(0)
 return dict(p=p,K=K,degree=P.degree(),nonzero_certified=True,precision_bits=prec,terms=N,tail=tail.str(18),value=val.str(24),logabs=float(abs(val).log()),logabs_K3=float(abs(val).log())/K**3,v2content=(con&-con).bit_length()-1,logden_K3=math.log(den)/K**3,logcontent_K3=math.log(con)/K**3,seconds=time.time()-t)
if __name__=='__main__':
 with Path(__file__).with_name('step2_scan.jsonl').open('w') as f:
  for K in [2,4,8,12,16,24,32,48]:
   r=audit(2,K);f.write(json.dumps(r)+'\n');f.flush();print(json.dumps(r),flush=True)
