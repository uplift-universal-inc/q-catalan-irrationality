from pathlib import Path
import sys,math,json
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'qbeta2'))
from step2 import entries,fmpq_mat

def E(K,d):
 if d%2:
  r,t=divmod(K,d)
  f=lambda m: (m+2)**2//4 if m else 0
  A=min(K,(d-1)//2)
  return t*f(r+1)+(d-t)*f(r)-min(A,t)*max(0,2-r)-max(0,A-t)*max(0,3-r)
 if d%4==2:
  h=d//2
  return sum(max(0,K-a*h) for a in range(1,K//h+1,2))
 u=d//4
 return min(K,max(0,K-4*u)+max(0,K-u-1))

def phis(p,K):
 vals={}
 for d in range(1,K+1):
  v=p**d-1
  for a in range(1,d):
   if d%a==0:
    assert v%vals[a]==0
    v//=vals[a]
  vals[d]=v
 return vals

def determinant(K,a,b):
 A=fmpq_mat(K,K,[a[i+j] for i in range(K) for j in range(K)])
 B=fmpq_mat(K,K,[b[i+j] for i in range(K) for j in range(K)])
 return (-(B.inv()*A)).charpoly()*B.det()

if __name__=='__main__':
 rows=[]
 for p in [2,3,4,5,6]:
  cyc=phis(p,4*20)
  for K in range(1,21):
   aa,bb=entries(p,K,2)
   pol=determinant(K,aa,bb)
   es={d:E(K,d) for d in range(1,4*K+1)}
   assert min(es.values())>=0
   C=math.prod(cyc[d]**e for d,e in es.items())
   assert all((c*C).q==1 for c in pol),(p,K)
   rows.append(dict(p=p,K=K,exponents=es,integral=True))
  print('p',p,'passed',flush=True)
 Path(__file__).with_suffix('.json').write_text(json.dumps({'cases':len(rows),'passed':True,'rows':rows},indent=2))
 print('All',len(rows),'cases passed')
