from flint import fmpq,fmpq_poly,fmpq_mat,fmpz_poly,arb,ctx
import math,json,time,sys
from costs import denominator_check
from pathlib import Path

def chi(n):return 0 if n%2==0 else 1 if n%4==1 else -1

def entries(p,K,step=4):
 q=fmpq(1,p); S={}; acc=fmpq(0)
 for n in range(1,step*K+1):
  y=q**n
  acc+=chi(n)*y/(1-y)**2
  if n%step==0:S[n//step]=acc
 poles=[fmpq(p)**(step*a) for a in range(1,K+1)]
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
   c=base[a]*r**k*((-1)**(a+1) if step==2 else 1)
   A-=c*S[a+1];B+=c
  aa.append(A);bb.append(B)
 return aa,bb

