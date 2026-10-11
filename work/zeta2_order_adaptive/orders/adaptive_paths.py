"""Structured genuine two-block paths, exact row/prime-adaptive certificates.

Each prefix and suffix contains whole coordinate blocks. Exact termwise
contents discard cancellation only at the one interface. All endpoints are
verified as full 3x3 matrices. No residue of the endpoint sum enters bounds.
"""
import argparse, json, math, sys, time
from fractions import Fraction
from itertools import product
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2]/'zeta2_orders_10911'))
from core import START, R, endpoint, segment, C, fmpq, fmpq_mat, encode
from arithmetic import sieve
from profile import phi

sys.set_int_max_str_digits(0)
OUT=Path(__file__).resolve().parent
SHELLS=[(Fraction(13,2),Fraction(8)),(Fraction(13,3),Fraction(9,2)),
        (Fraction(13,4),Fraction(10,3)),(Fraction(13,5),Fraction(8,3)),
        (Fraction(13,6),Fraction(9,4)),(Fraction(13,12),Fraction(9,8))]
INF=10**8


def qgcd(a,b):
    return fmpq(math.gcd(int(a.numerator),int(b.numerator)),
                math.lcm(int(a.denominator),int(b.denominator)))


def qlcm(a,b):
    if not a:return abs(b)
    if not b:return abs(a)
    return fmpq(math.lcm(int(a.numerator),int(b.numerator)),
                math.gcd(int(a.denominator),int(b.denominator)))


def content(values):
    out=fmpq(0)
    for v in values:out=qgcd(out,v)
    return out


def vp(q,p):
    if not q:return INF
    out=0
    for sign,n in ((1,abs(int(q.numerator))),(-1,int(q.denominator))):
        while n%p==0:n//=p;out+=sign
    return out


def logabs(q):
    return math.log(abs(int(q.numerator)))-math.log(int(q.denominator))


def grid(N):
    uppers=[(t,t,t)for t in(3,4,6,8,9)]+[(10,9,11)]
    lowers=[(0,0,0),(1,0,1),(1,1,2),(2,1,3)]
    for upper,lower,m in product(uppers,lowers,(0,3,6,9)):
        if m>sum(upper)-sum(lower):continue
        ds=(*upper,-m,*lower)
        name='u'+'_'.join(map(str,upper))+'_l'+'_'.join(map(str,lower))+f'_m{m}'
        yield name,ds,tuple(s+N*d for s,d in zip(START,ds))


def baseline(N):
    D=math.lcm(*range(1,12*N+1))*math.lcm(*range(1,13*N+1))
    G=H=1
    for p in sieve(13*N):
        if p*p<=50*N:continue
        G*=p**phi(Fraction(N,p))
        if any(lo*N<p<hi*N for lo,hi in SHELLS):H*=p
    return fmpq(G*H,D*C(endpoint(N)))


def run(N):
    began=time.perf_counter();W=segment(START,endpoint(N));Y=R*W
    base=baseline(N);actual=content([Y[0,0],Y[1,0]])
    assert (actual/base).denominator==1
    checkpoint=OUT/f'paths_{N}.jsonl'
    done={z['name']:z for z in map(json.loads,checkpoint.read_text().splitlines())}if checkpoint.exists()else{}
    rows=[];row_envelope=[base,base];order_envelope=base
    for name,ds,w in grid(N):
        if name in done:z=done[name]
        else:
            try:
                A=segment(START,w);B=segment(w,endpoint(N))
            except (ZeroDivisionError,ValueError) as exc:
                z=dict(N=N,name=name,direction_to_cut=ds,status='COMPUTATION_FAILED',error=str(exc))
            else:
                assert A*B==W,name
                prefix=R*A;suffix=[B[i,0]for i in range(3)]
                contents=[content([prefix[r,i]*suffix[i]for i in range(3)])for r in range(2)]
                assert all((Y[r,0]/contents[r]).denominator==1 for r in range(2))
                z=dict(N=N,name=name,direction_to_cut=ds,cut_vertex=w,status='NUMERICAL_CANDIDATE',
                       prefix_rows=encode(prefix),suffix_column=list(map(str,suffix)),
                       row_contents=list(map(str,contents)),endpoint_all_nine_entries_equal=True,
                       negative_suffix_steps=11*N+w[3],orientation='forward',selected_column=0,
                       coordinate_order=[0,1,2,4,5,6,3],matrix_dimension=3,gauge='native_unscaled')
            with checkpoint.open('a')as f:f.write(json.dumps(z)+'\n')
        if z['status']=='COMPUTATION_FAILED':continue
        cs=list(map(fmpq,z['row_contents']))
        row_envelope=[qlcm(a,b)for a,b in zip(row_envelope,cs)]
        order_envelope=qlcm(order_envelope,qgcd(*cs))
        rows.append(z)
    combined=qgcd(*row_envelope)
    assert (actual/combined).denominator==1
    primes=sieve(50*N+50);witnesses=[]
    cached_contents=[list(map(fmpq,z['row_contents']))for z in rows]
    for p in primes:
        bv=vp(base,p);valuations=[[vp(c[r],p)for r in range(2)]for c in cached_contents]
        rv=[max(v[r]for v in valuations)for r in range(2)]
        best_names=[[z['name']for z,v in zip(rows,valuations)if v[r]==rv[r]]for r in range(2)]
        cv=vp(combined,p);ov=vp(order_envelope,p)
        if cv>bv or min(rv)>ov:
            witnesses.append(dict(prime=p,baseline_valuation=bv,combined_valuation=cv,
                                  same_path_prime_envelope=ov,best_row_valuations=rv,
                                  best_row_paths=best_names,actual_valuation=vp(actual,p)))
    summary=dict(N=N,status='NUMERICAL_CANDIDATE',path_count=len(rows),
                 baseline_content=str(base),row_adaptive_content=str(combined),
                 same_path_prime_envelope_content=str(order_envelope),actual_content=str(actual),
                 gain_factor_over_six_shells=str(combined/base),
                 gain_factor_from_row_choice=str(combined/order_envelope),
                 baseline_log_q_bound=logabs(Y[1,0])-logabs(base),
                 improved_log_q_bound=logabs(Y[1,0])-logabs(combined),
                 actual_reduced_log_q=logabs(Y[1,0])-logabs(actual),
                 gain_rate=(logabs(combined)-logabs(base))/N,
                 witnesses=witnesses,runtime_seconds=time.perf_counter()-began)
    (OUT/f'summary_{N}.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({k:v for k,v in summary.items()if k not in('baseline_content','row_adaptive_content','same_path_prime_envelope_content','actual_content','witnesses')},indent=2),flush=True)


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('depths',nargs='*',type=int,default=[20,40,80,160])
    for N in ap.parse_args().depths:run(N)
