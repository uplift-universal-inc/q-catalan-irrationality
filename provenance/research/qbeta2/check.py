from scan import entries
from costs import denominator_check
from flint import fmpq_mat,fmpq
import math,json
from pathlib import Path
rows=[]
for p in [2,3,4,5,6]:
 for K in range(1,17):
  aa,bb=entries(p,K)
  A=fmpq_mat(K,K,[aa[i+j] for i in range(K) for j in range(K)])
  B=fmpq_mat(K,K,[bb[i+j] for i in range(K) for j in range(K)])
  D=(-(B.inv()*A)).charpoly()*B.det()
  den=math.lcm(*(int(c.q) for c in D));cs=[int(c.p)*(den//int(c.q)) for c in D];content=math.gcd(*cs)
  assert denominator_check(p,K,den),(p,K)
  assert content==p**(2*K*(K*K-1)),(p,K,'content')
  assert D[K]==(-1)**(K*(K-1)//2)*fmpq(p)**(2*K*(K*K-1))
  rows.append(dict(p=p,K=K,degree=D.degree(),content_exact=True,improved_clearer_divides=True))
Path(__file__).with_name('checks.json').write_text(json.dumps(dict(passed=len(rows),rows=rows),indent=2)+'\n')
print('Passed',len(rows),'exact coefficient/content/divisibility tests')
