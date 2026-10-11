"""Exact finite checks of the the manuscript's largest-shell congruences.
These checks accompany, and do not replace, the quantified argument.
"""
import json, math, sys
from pathlib import Path
def sieve(n):
    """Primes up to n; self-contained Eratosthenes sieve."""
    if n < 2:
        return []
    flags = bytearray(b"\x01") * (n + 1)
    flags[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(n) + 1):
        if flags[p]:
            flags[p*p:n+1:p] = b"\x00" * ((n - p*p)//p + 1)
    return [p for p in range(2, n+1) if flags[p]]

from core import fmpq, comb
from flint import fmpq_poly

def residue(q,p):
    return (int(q.numerator)%p)*pow(int(q.denominator)%p,-1,p)%p

def run(limit=120):
    cases=0; polynomial_checks=0
    for N in range(1,limit+1):
        for p in sieve(8*N):
            if p*p<=50*N or not 13*N<2*p<16*N: continue
            b=8*N-p; d=11*N-p
            sums=[0,0,0]
            for k in range(d+1):
                f=math.prod(comb(k+u*N-p,b)%p for u in (9,10,11))%p
                lam=[(k+u*N)//p for u in (9,10,11)]
                assert f==0 or lam==[1,1,1],(N,p,k)
                beta=(-1)**k*comb(d,k)
                for r in range(3): sums[r]=(sums[r]+beta*pow(k,r,p)*f)%p
            for r in range(3):
                if 13*N+r<2*p: assert sums[r]==0,(N,p,r)
            cases+=1
            if N<=12:
                F=fmpq_poly([1])
                for u in (9,10,11):
                    for z in range((u-8)*N+1,u*N+1):F*=fmpq_poly([z,1])
                    F/=math.factorial(8*N)
                for k in range(d+1):
                    f=math.prod(comb(k+u*N-p,b)%p for u in (9,10,11))%p
                    assert residue(F(k),p)==f
                    assert residue(F(k+p),p)==8*f%p
                    assert residue(p*F.derivative()(k),p)==3*f%p
                for r in range(3):
                    if not 13*N+r<2*p:continue
                    Fr=F*fmpq_poly([0]*r+[1]);S=fmpq_poly([])
                    for j in range(11*N+1):
                        quotient,rem=divmod(Fr-Fr(j),fmpq_poly([-j,1]));assert not rem
                        S+=((-1)**j*comb(11*N,j))*quotient
                    for s in range(-2*N,p-2*N):
                        k=s%p
                        expected=0
                        if k<=d:
                            f=math.prod(comb(k+u*N-p,b)%p for u in (9,10,11))%p
                            expected=-4*((-1)**k)*comb(d,k)*pow(k,r,p)*f%p
                        assert residue(p*S(s),p)==expected,(N,p,r,s)
                    polynomial_checks+=1
    result={'N_range':[1,limit], 'eligible_prime_cases':cases,
            'direct_rational_polynomial_checks':polynomial_checks,
            'all_assertions_passed':True}
    print(json.dumps(result,indent=2))
    Path(__file__).with_name('main_shell_checks.json').write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__': run()
