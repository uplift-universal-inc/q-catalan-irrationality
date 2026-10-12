from math import pi

def exponents(K,d):
 if d%2:
  r,t=divmod(K,d)
  f=lambda m: (m+2)**2//4 if m else 0
  E=t*f(r+1)+(d-t)*f(r)
  A=min(K,(d-1)//4)
  return E-min(A,t)*max(0,2-r)-max(0,A-t)*max(0,3-r)
 if d%4:return 0
 h=d//4
 return min(K,max(0,K-2*h)+max(0,K-h-1))

def cyclotomic_values(p,M):
 v={}
 for d in range(1,M+1):
  w=p**d-1
  for e in range(1,d):
   if d%e==0:w//=v[e]
  v[d]=w
 return v

def denominator_check(p,K,den):
 v=cyclotomic_values(p,4*K)
 c=1
 for d in range(1,4*K+1):c=(c*pow(v[d],exponents(K,d),den))%den
 return c==0

if __name__=='__main__':
 for K in [100,1000,10000]:
  phi=list(range(4*K+1))
  for l in range(2,len(phi)):
   if phi[l]==l:
    for j in range(l,len(phi),l):phi[j]-=phi[j]//l
  odd=sum(phi[d]*exponents(K,d) for d in range(1,4*K+1,2))
  even=sum(phi[d]*exponents(K,d) for d in range(4,4*K+1,4))
  print(K,odd/K**3,even/K**3,(odd+even)/K**3)
 print('Expected limit',1/12+(64/3-4759/12150+82/27)/pi**2)
