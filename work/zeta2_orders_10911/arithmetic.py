"""Finite exact tests of candidate lcm and prime-carry normalizations."""
import argparse,json,math,sys,time
from fractions import Fraction
from pathlib import Path
from core import *
from profile import phi
sys.set_int_max_str_digits(0)
OUT=Path(__file__).resolve().parents[2]/'results/zeta2_orders_10911'

def sieve(n):
    a=bytearray(b'\1')*(n+1);a[:2]=b'\0\0'
    for p in range(2,math.isqrt(n)+1):
        if a[p]: a[p*p::p]=b'\0'*((n-p*p)//p+1)
    return [p for p in range(2,n+1) if a[p]]
def val(v,p):
    z=0
    for sign,t in ((1,abs(v.numerator)),(-1,v.denominator)):
        while t%p==0:t//=p;z+=sign
    return z
def logabs(q):return math.log(abs(int(q.numerator)))-math.log(int(q.denominator))
def run(N):
    started=time.perf_counter();W=segment(START,endpoint(N));Y=R*W;CY=Y*C(endpoint(N))
    D=lcm(*range(1,12*N+1))*lcm(*range(1,13*N+3))
    primes=sieve(13*N+2);G=1;profile=[];common=content(CY)
    for p in primes:
        if p*p<=50*N or p>13*N:continue
        h=phi(Fraction(N,p));G*=p**h
        lower=h-(p<=12*N)-(p<=13*N+2);actual=val(common,p)
        profile.append(dict(prime=p,ratio_p_over_N=p/N,carry=h,bound=lower,actual=actual,extra=actual-lower))
    normalized=CY*fmpq(D,G)
    assert all(normalized[i,j].denominator==1 for i in range(2) for j in range(3)),N
    # D/G is a normalization of CY, never the reduced denominator q itself.
    q=(Y[0,0]/Y[1,0]).denominator
    result=dict(N=N,status='NUMERICAL_CANDIDATE',D=str(D),G=str(G),C=str(C(endpoint(N))),
                all_six_entries_integral=True,arithmetic_rate=(math.log(D)-math.log(G))/N,
                log_q_bound=logabs(CY[1,0])+math.log(D)-math.log(G),actual_reduced_log_q=math.log(int(q)),
                extra_large_prime_rate=sum(row['extra']*math.log(row['prime']) for row in profile)/N,
                prime_profile=profile,runtime_seconds=time.perf_counter()-started)
    (OUT/f'arithmetic_{N}.json').write_text(json.dumps(result,indent=2))
    print(json.dumps({k:v for k,v in result.items() if k not in ('D','G','C','prime_profile')}),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--depths',nargs='+',type=int,default=[20,40,80,160,320,640])
    for N in p.parse_args().depths:
        if not (OUT/f'arithmetic_{N}.json').exists():run(N)
