"""Long-block lookahead: exact incoming rows, exact entire remaining block.

For each cut, gcd_i(Y_cut[r,i]*B[i,0]) is a safe rational content bound.
Rational lcm across cuts chooses the best valuation independently at each prime.
The suffix always contains >=6*N negative-upper moves; no endpoint cut allowed.
"""
import argparse,json,math,sys,time
from itertools import product
from pathlib import Path
from core import *
sys.set_int_max_str_digits(0)
OUT=Path(__file__).resolve().parents[2]/'results/zeta2_orders_10911'
EXPANDED=False
def logabs(q): return math.log(abs(int(q.numerator)))-math.log(int(q.denominator))
def qlcm(a,b):
    if a==0: return b
    return fmpq(lcm(int(a.numerator),int(b.numerator)),gcd(int(a.denominator),int(b.denominator)))
def qgcd(a,b): return fmpq(gcd(int(a.numerator),int(b.numerator)),lcm(int(a.denominator),int(b.denominator)))

def cuts():
    for t in range(0,10):
        for lower in (False,True):
            if lower and t<3: continue
            for m in range(0,6):
                ds=(t,t,t,-m,2 if lower else 0,1 if lower else 0,3 if lower else 0)
                if sum(ds[:4])-sum(ds[4:])<=0 and any(ds): continue
                yield f'plateau_{t}_lowers_{int(lower)}_m_{m}',ds
    for lower in (False,True):
        for m in range(0,6):
            yield f'full_uppers_lowers_{int(lower)}_m_{m}',(10,9,11,-m,2 if lower else 0,1 if lower else 0,3 if lower else 0)
    if EXPANDED:
        for a,b,c in product((3,6,9),repeat=3):
            if a==b==c: continue
            for lower in (False,True):
                for m in (0,2,5):
                    ds=(a,b,c,-m,2 if lower else 0,1 if lower else 0,3 if lower else 0)
                    if sum(ds[:4])-sum(ds[4:])<=0: continue
                    yield f'staggered_{a}_{b}_{c}_lowers_{int(lower)}_m_{m}',ds

def run(N):
    began=time.perf_counter(); W=segment(START,endpoint(N)); Y=R*W
    bestrow=[fmpq(0),fmpq(0)]; rows=[]
    tag='_expanded' if EXPANDED else ''
    cache=OUT/f'cuts{tag}_checkpoint_{N}.jsonl'
    done={r['name']:r for r in map(json.loads,cache.read_text().splitlines())} if cache.exists() else {}
    for name,ds in cuts():
        if name in done: rec=done[name]
        else:
            w=tuple(s+N*d for s,d in zip(START,ds))
            A=segment(START,w); B=segment(w,endpoint(N)); assert A*B==W
            Z=R*A
            contents=[]
            for r in range(2):
                terms=fmpq_mat([[Z[r,i]*B[i,0] for i in range(3)]])
                contents.append(content(terms))
            c=qgcd(*contents)
            rec=dict(name=name,direction_to_cut=ds,row_contents=list(map(str,contents)),
                     common_content=str(c),log_q_bound=logabs(Y[1,0])-logabs(c))
            with cache.open('a') as f: f.write(json.dumps(rec)+'\n')
        for r in range(2): bestrow[r]=qlcm(bestrow[r],fmpq(rec['row_contents'][r]))
        rows.append(rec)
    c=qgcd(*bestrow); exact=qgcd(Y[0,0],Y[1,0])
    assert (exact/c).denominator==1
    rows.sort(key=lambda r:r['log_q_bound'])
    result=dict(N=N,status='NUMERICAL_CANDIDATE',cuts=len(rows),
                best_single_cut=rows[0],prime_adapted_row_contents=list(map(str,bestrow)),
                prime_adapted_content=str(c),prime_adapted_log_q_bound=logabs(Y[1,0])-logabs(c),
                exact_reduced_log_q=logabs(Y[1,0])-logabs(exact),remaining_integer_gap=str(exact/c),
                runtime_seconds=time.perf_counter()-began,all_cuts=rows)
    (OUT/f'cuts{tag}_{N}.json').write_text(json.dumps(result,indent=2))
    print(json.dumps(dict(N=N,cuts=len(rows),best_single_cut=rows[0]['name'],
          best_single_log_q_bound=rows[0]['log_q_bound'],prime_adapted_log_q_bound=result['prime_adapted_log_q_bound'],
          exact_reduced_log_q=result['exact_reduced_log_q'],runtime_seconds=result['runtime_seconds'])),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--depths',nargs='+',type=int,default=[2,5,10,20,40,80]);p.add_argument('--expanded',action='store_true')
    args=p.parse_args();EXPANDED=args.expanded;tag='_expanded' if EXPANDED else ''
    for N in args.depths:
        if not (OUT/f'cuts{tag}_{N}.json').exists(): run(N)
