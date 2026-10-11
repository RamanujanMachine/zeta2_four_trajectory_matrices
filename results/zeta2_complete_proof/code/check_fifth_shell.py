"""Independent exact finite checks of the denominator-five shell identities."""
import json,math,sys
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

from flint import fmpq,fmpq_poly

def residue(q,p):return int(q.numerator)%p*pow(int(q.denominator)%p,-1,p)%p

def run(limit=300):
    cases=0;polynomial_checks=0
    X=fmpq_poly([0,1]);P=fmpq_poly([1])
    for shift in [3,3,4]:
        for j in range(3):P*=X+shift-j
        P/=6
    for N in range(1,limit+1):
        for p in sieve((8*N+2)//3):
            if p*p<=50*N or not 13*N<5*p or not 3*p<8*N:continue
            b=8*N-3*p;d=11*N-4*p
            for k in range(d+1):
                f=math.prod(math.comb(k+u*N-3*p,b)%p for u in (9,10,11))%p
                assert f==0 or [(k+u*N)//p for u in (9,10,11)]==[3,3,4],(N,p,k)
            for r in range(3):
                if not 13*N+r<5*p:continue
                value=sum((-1)**k*math.comb(d,k)*k**r*math.prod(math.comb(k+u*N-3*p,b)%p for u in (9,10,11)) for k in range(d+1))%p
                assert value==0,(N,p,r)
            cases+=1
            if N<=40:
                F=fmpq_poly([1])
                for u in (9,10,11):
                    for z in range((u-8)*N+1,u*N+1):F*=X+z
                    F/=math.factorial(8*N)
                for k in range(d+1):
                    f=math.prod(math.comb(k+u*N-3*p,b)%p for u in (9,10,11))%p
                    for nu in range(-1,5):
                        assert residue(F(k+nu*p),p)==residue(P(nu),p)*f%p
                        assert residue(p*F.derivative()(k+nu*p),p)==residue(P.derivative()(nu),p)*f%p
                for r in range(3):
                    if not 13*N+r<5*p:continue
                    Fr=F*X**r;S=fmpq_poly([])
                    for j in range(11*N+1):
                        q,rem=divmod(Fr-Fr(j),X-j);assert not rem
                        S+=(-1)**j*math.comb(11*N,j)*q
                    for h in range(1,(13*N+r)//p+1):
                        val=sum((-1)**(h*p-1-t)*math.comb(h*p-1,t)*residue(p*S(-p+t),p) for t in range(h*p))%p
                        assert val==0,(N,p,r,h)
                    polynomial_checks+=1
    out={'N_range':[1,limit],'eligible_prime_cases':cases,'direct_rational_polynomial_checks':polynomial_checks,'all_assertions_passed':True}
    print(json.dumps(out,indent=2));Path(__file__).with_name('fifth_shell_checks.json').write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__':run()
