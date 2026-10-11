#!/usr/bin/env python3
"""Exact rational certificates for the limiting spectrum and logarithmic rates.

Standard library only. This verifies finite arithmetic used in the analytic
argument; the contour and recurrence arguments are written in the accompanying manuscript.
No floating-point result is used in an assertion.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import sys
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)


def mat(a): return [[F(x) for x in row] for row in a]
I=mat([[1,0,0],[0,1,0],[0,0,1]])
def mul(a,b): return [[sum((a[i][k]*b[k][j] for k in range(3)),F(0)) for j in range(3)] for i in range(3)]
def add(a,b): return [[a[i][j]+b[i][j] for j in range(3)] for i in range(3)]
def scale(a,k): return [[x*k for x in row] for row in a]
def inverse(a):
    t=[a[i][:]+I[i][:] for i in range(3)]
    for k in range(3):
        q=next(j for j in range(k,3) if t[j][k]);t[q],t[k]=t[k],t[q]
        d=t[k][k];t[k]=[v/d for v in t[k]]
        for j in range(3):
            if j!=k:
                c=t[j][k];t[j]=[v-c*w for v,w in zip(t[j],t[k])]
    return [r[3:] for r in t]
def power(a,n):
    if n<0:return power(inverse(a),-n)
    out=I
    for _ in range(n):out=mul(out,a)
    return out

def det(a):
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
            -a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
            +a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))

def log_unit_bounds(x,K=32):
    assert 1<=x<=2
    y=(x-1)/(x+1)
    low=2*sum((y**(2*k+1)/F(2*k+1) for k in range(K)),F(0))
    tail=2*y**(2*K+1)/(F(2*K+1)*(1-y*y))
    return low,low+tail

def log_bounds(x,K=32):
    x=F(x);assert x>0;k=0
    while x<1:x*=2;k-=1
    while x>=2:x/=2;k+=1
    lo,hi=log_unit_bounds(x,K);l2,h2=log_unit_bounds(F(2),K)
    return (lo+k*l2,hi+k*h2) if k>=0 else (lo+k*h2,hi+k*l2)

def linear_logs(terms):
    lo=hi=F(0)
    for coeff,x in terms:
        a,b=log_bounds(x)
        if coeff>=0:lo+=coeff*a;hi+=coeff*b
        else:lo+=coeff*b;hi+=coeff*a
    return lo,hi


def main():
    T=mat([[0,0,F(10890,13)],[1,0,F(2305,13)],[0,1,F(42,13)]])
    A=I
    for u in (10,9,11):A=mul(A,power(add(I,scale(T,F(1,u))),u))
    A=mul(A,power(add(I,scale(T,F(-1,11))),-11))
    for v in (2,1,3):A=mul(A,power(add(I,scale(T,F(1,v))),-v))
    c2=-sum(A[i][i] for i in range(3))
    c1=sum(A[i][i]*A[j][j]-A[i][j]*A[j][i] for i in range(3) for j in range(i+1,3))
    c0=-det(A)
    assert c0==F(1855425871872,895833302668638834554683750087890625)
    assert c1==F(6119917581009155345396562793851904,32000061404626447809127858236889541015625)
    assert c2==F(266957778538934989798238376160038092809,15342324857928574809549553125)
    disc=c2*c2*c1*c1-4*c1**3-4*c2**3*c0-27*c0*c0+18*c2*c1*c0
    assert disc<0
    L=17400086428;U=17400086429
    poly=lambda x:x**3-c2*x*x+c1*x-c0
    assert poly(L)<0<poly(U)
    assert 0<c0/F(L)<1
    A2=mul(A,A)
    obs=[[I[i][0],A[i][0],A2[i][0]] for i in range(3)]
    od=det(obs)
    assert od==F(72143259339220303025804927524593090645506084475442025307751136603648,28469599455181793682074031322586982029718987334183867584429931640625)
    assert od!=0
    cb=linear_logs([(10,10),(9,9),(11,11),(-2,2),(-1,1),(-3,3),(-24,8)])
    ab=linear_logs([(1,U),(10,10),(9,9),(11,11),(-2,2),(-1,1),(-3,3),(-24,8)])
    bb=linear_logs([(F(1,2),c0),(F(-1,2),L),(10,10),(9,9),(11,11),(-2,2),(-1,1),(-3,3),(-24,8)])
    hb=linear_logs([(12,2),(6,6),(11,11),(-17,17),(6,3),(8,4),(10,5),(-24,8)])
    gap=linear_logs([(F(3,2),L),(F(-1,2),c0)])
    assert ab[1]<F('38.168733')
    assert bb[1]<F('-24.467842')
    assert hb[1]<-18
    assert gap[0]>F('62.636575')
    sigma=F('38.168733')+F('10.929906')
    tau=F('24.467842')-F('10.929906')
    assert tau>0 and 1+sigma/tau<F('4.62675')
    def bounds_json(b):return {'lower':str(b[0]),'upper':str(b[1]),'lower_decimal':float(b[0]),'upper_decimal':float(b[1])}
    out={'status':'NUMERICAL_CANDIDATE','arithmetic':'exact Fractions; 32 positive atanh-series terms with a geometric remainder',
         'limiting_theta':[[str(v) for v in row] for row in T],
         'limiting_matrix':[[str(v) for v in row] for row in A],
         'characteristic_ascending':list(map(str,[c0,c1,c2,F(1)])),
         'cubic_discriminant_negative':True,'dominant_modulus_interval':[L,U],
         'small_modulus_squared_upper':str(c0/F(L)),
         'observability_determinant':str(od),
         'C_exponent':bounds_json(cb),'scaled_coefficient_exponent_upper_enclosure':bounds_json(ab),
         'scaled_error_exponent_upper_enclosure':bounds_json(bb),
         'coarse_contour_exponent':bounds_json(hb),'spectral_gap_lower_enclosure':bounds_json(gap),
         'sigma_upper':str(sigma),'tau_lower':str(tau),'mu_upper':str(1+sigma/tau),
         'proof_dependencies':'Uniform integer normalization, contour estimates, recurrence analysis, and separation are established in the accompanying manuscript; the finite certificate verifies their constants.'}
    path=Path(__file__).with_name('analytic_certificates.json')
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in {'limiting_matrix','C_exponent','scaled_coefficient_exponent_upper_enclosure','scaled_error_exponent_upper_enclosure','coarse_contour_exponent','spectral_gap_lower_enclosure'}},indent=2))
    print('rate displays:',float(ab[1]),float(bb[1]),float(hb[1]),float(gap[0]))
    print(path)

if __name__=='__main__':main()
