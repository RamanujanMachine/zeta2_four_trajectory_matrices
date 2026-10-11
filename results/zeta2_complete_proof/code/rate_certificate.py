"""Exact rational carry-profile integral enclosure; Python standard library.

The partition argument is explained in the manuscript. This program evaluates
its finite cells and gives directed rational arithmetic for the rate estimate.
The uniform shell divisibility, analytic bounds, and separation argument
are proved in the accompanying manuscript; this verifies their rate arithmetic.
"""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json

OUT=Path(__file__).with_name('rate_certificate.json')
SLOPES=(11,-10,-9,-11,-2,-1,-3)
K=2000;SCALE=10**15
def floor(x):return x.numerator//x.denominator
def frac(x):return x-floor(x)
def rho(x,y):
    return floor(11*x)-floor(y)-floor(11*x-y)+sum(floor(u*x+y)-floor(8*x)-floor(v*x+y) for u,v in ((10,2),(9,1),(11,3)))
def phi(x):
    ys=sorted({F(0),F(1)}|{frac(s*x) for s in SLOPES})
    return min(rho(x,y) for y in ys[:-1]+[(a+b)/2 for a,b in zip(ys,ys[1:])])
def main():
    coefs=sorted(set(map(abs,SLOPES))|{abs(a-b) for a,b in combinations(SLOPES,2)}|{8})
    coefs=[c for c in coefs if c]
    cuts=sorted({F(k,c) for c in coefs for k in range(c+1)})
    rows=[];total=0;count=0;mean=F(0)
    for a,b in zip(cuts,cuts[1:]):
        values=[phi((3*a+b)/4),phi((a+b)/2),phi((a+3*b)/4)]
        assert values[0]==values[1]==values[2];h=values[0]
        rows.append((a,b,h));mean+=h*(b-a)
        if not h:continue
        assert a>0
        num=h*(b.numerator*a.denominator-a.numerator*b.denominator)
        for k in range(K):
            den=(k*a.denominator+a.numerator)*(k*b.denominator+b.numerator)
            total+=SCALE*num//den;count+=1
    assert all(h==0 for a,b,h in rows if a<F(1,13))
    lower=F(total,SCALE)+mean/F(K+1)
    upper=F(total+count,SCALE)+mean/F(K-1)
    shell_rate=F(233,120)
    c_upper=25-lower-shell_rate
    assert c_upper<F('10.929906')
    a_upper=F('38.168733');E_lower=F('62.636575')
    sigma=a_upper+F('10.929906');tau=E_lower-sigma
    mu=1+sigma/tau
    assert tau>0 and mu<F('4.62675')
    result=dict(status='NUMERICAL_CANDIDATE',coefficients=coefs,cells=len(rows),
                periods=K,rounding_scale=SCALE,rounded_sum=total,positive_cell_terms=count,
                profile_mean=str(mean),gamma_lower=str(lower),gamma_upper=str(upper),
                gamma_lower_decimal=float(lower),gamma_upper_decimal=float(upper),
                arithmetic_c_upper=str(c_upper),sigma_upper=str(sigma),tau_lower=str(tau),
                mu_upper=str(mu),mu_decimal=float(mu),
                rate_target='4.62675',
                proof_dependencies='The accompanying manuscript establishes uniform extra-shell divisibility, analytic rates, and nonvanishing; this script certifies their numerical consequence.',
                profile=[[str(a),str(b),h] for a,b,h in rows])
    OUT.write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items() if k!='profile'},indent=2))
if __name__=='__main__':main()
