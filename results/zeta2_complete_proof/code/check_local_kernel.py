"""Exact independent checks of local factorizations in all_shells.tex.
Finite tests accompany the uniform proof and exact arrangement certificate.
"""
import json,math,sys,time
from pathlib import Path
from fractions import Fraction as Q
from flint import fmpq,nmod_poly
from rate_certificate import phi

def binom(n,k):
 if n<0:return (-1)**k*math.comb(k-n-1,k)
 return math.comb(n,k) if n>=k else 0

def res(v,p):
 v=fmpq(v);return int(v.numerator)%p*pow(int(v.denominator)%p,-1,p)%p

def run():
 started=time.monotonic();rows=[]
 for N,p in [(3,23),(7,31),(7,23),(23,61),(13,29),(17,37),(42,47),(43,47)]:
  a,b=divmod(8*N,p);M,d=divmod(11*N,p);h=phi(Q(N,p));A=1 if p>=2*N else 2
  x=nmod_poly([0,1],p);f=nmod_poly([1],p)
  for u in (9,10,11):
   fu=nmod_poly([1],p)
   for j in range(b):fu*=x+(u*N-j)%p
   fu*=pow(math.factorial(b)%p,-1,p);f*=fu
  g=nmod_poly([1],p)
  for j in range(d+1):g*=x-j
  z=x**p-x
  if h==0:q,rem=divmod(f*z,g)
  else:q,rem=divmod(f,(z**(h-1))*g)
  assert not rem
  support=[k for k in range(p) if int(q(k))]
  k=support[0];e=int(k>d);lam=[(k+u*N)//p for u in(9,10,11)];deltas=[int((k+u*N)%p<b) for u in(9,10,11)]
  P=nmod_poly([1],p)
  for lu,dd in zip(lam,deltas):
   v=nmod_poly([1],p)
   for t in range(a+dd):v*=x+lu-t
   v*=pow(math.factorial(a+dd)%p,-1,p)*pow(a+1,dd,p);P*=v
  D=nmod_poly([1],p)
  for l in range(M-e+1):D*=x-l
  B,_=divmod(P,D)
  residues=[int(P(l))*pow(int(D.derivative()(l)),-1,p)%p for l in range(M-e+1)]
  kap=((1 if (d-M+h-1)%2==0 else -1)*math.factorial(M)*math.factorial(d))%p
  def F(s):return math.prod(binom(s+u*N,8*N) for u in (9,10,11))
  fj=[F(j) for j in range(11*N+1)];weights=[(-1)**j*math.comb(11*N,j) for j in range(11*N+1)]
  cs=[weights[j]*fj[j] for j in range(11*N+1)]
  for k in range(p):
   for l in range((11*N-k)//p+1):
    expected=kap*int(q(k))*(residues[l] if l<len(residues) else 0)%p
    assert res(fmpq(cs[k+l*p],p**h),p)==expected,(N,p,'coefficient',k,l)
  harmonic=[fmpq(0)]
  for t in range(1,22*N+1):harmonic.append(harmonic[-1]+fmpq(1,t))
  deriv=[fj[j]*sum((harmonic[j+u*N]-harmonic[j+(u-8)*N] for u in (9,10,11)),fmpq(0)) for j in range(11*N+1)]
  def S(s,r):
   fs=F(s);frs=s**r*fs;out=fmpq(0)
   for j in range(11*N+1):
    if s==j:
     derivative=s**r*deriv[j]+(r*s**(r-1)*fs if r else 0)
     out+=weights[j]*derivative
    else:out+=fmpq(weights[j]*(frs-j**r*fj[j]),s-j)
   return out
  count=0
  for r in range(3):
   if not 13*N+r<(3*a-M+h)*p:continue
   assert q.degree()+r<p-1
   assert sum(pow(k,r,p)*int(q(k)) for k in range(p))%p==0
   for k in range(p):
    for nu in [-A,0,M+1]:
     val=S(k+nu*p,r)*fmpq(p if h==0 else 1, p**(h-1) if h>1 else 1)
     expected=kap*pow(k,r,p)*int(q(k))*int(B(nu))%p
     assert res(val,p)==expected,(N,p,'S',r,k,nu,res(val,p),expected)
     count+=1
  rows.append({'N':N,'p':p,'a':a,'M':M,'h':h,'e':e,'support':len(support),'Q_degree':q.degree(),'S_checks':count})
  print(rows[-1],flush=True)
 out={'all_assertions_passed':True,'cases':rows,'S_checks':sum(r['S_checks'] for r in rows),'runtime_seconds':time.monotonic()-started}
 Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out,indent=2))
if __name__=='__main__':run()
