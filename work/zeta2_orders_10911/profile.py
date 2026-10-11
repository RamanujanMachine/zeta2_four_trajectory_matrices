"""Numerical carry profiles, not an all-depth arithmetic result."""
from fractions import Fraction as F
from itertools import combinations,permutations
import json,math
from pathlib import Path
import mpmath as mp
from core import *

OUT=Path(__file__).resolve().parents[2]/'results/zeta2_orders_10911'
def floor(x): return x.numerator//x.denominator
def frac(x): return x-floor(x)
U=(10,9,11); V=(2,1,3); M=11
SLOPES=(11,-10,-9,-11,-2,-1,-3)
def rho(x,y,perm=(0,1,2)):
    return floor(M*x)-floor(y)-floor(M*x-y)+sum(floor(u*x+y)-floor((u-V[j])*x)-floor(V[j]*x+y) for u,j in zip(U,perm))
def phi(x,perm=(0,1,2)):
    cuts=sorted({F(0),F(1)}|{frac(s*x) for s in SLOPES})
    return min(rho(x,y,perm) for y in cuts[:-1]+[(a+b)/2 for a,b in zip(cuts,cuts[1:])])
def profile(perm):
    widths=[u-V[j] for u,j in zip(U,perm)]
    coefs=set(map(abs,SLOPES))|{abs(a-b) for a,b in combinations(SLOPES,2)}|set(widths)
    cuts=sorted({F(k,c) for c in coefs if c for k in range(c+1)})
    return [(a,b,phi((a+b)/2,perm)) for a,b in zip(cuts,cuts[1:])]
def integral(rows,cutoff):
    def m(x): return mp.mpf(x.numerator)/x.denominator
    ans=mp.mpf(0)
    for a,b,h in rows:
        if not h: continue
        assert a>0
        ans+=h*(mp.digamma(m(b))-mp.digamma(m(a)))
        if a<cutoff: ans-=h*(1/m(a)-1/m(min(b,cutoff)))
    return float(ans)
def main():
    mp.mp.dps=50; results=[]
    for perm in permutations(range(3)):
        rows=profile(perm); widths=[u-V[j] for u,j in zip(U,perm)]
        results.append(dict(permutation=perm,widths=widths,gamma_cutoff_B=integral(rows,F(1,max(widths))),
                            gamma_cutoff_13=integral(rows,F(1,13)),
                            chambers=[[str(a),str(b),h] for a,b,h in rows]))
    (OUT/'carry_profiles.json').write_text(json.dumps(results,indent=2))
    for r in results: print({k:v for k,v in r.items() if k!='chambers'})
if __name__=='__main__': main()
